/*
 * Copyright 2018-2019 Alyssa Rosenzweig
 *
 * Permission is hereby granted, free of charge, to any person obtaining a
 * copy of this software and associated documentation files (the "Software"),
 * to deal in the Software without restriction, including without limitation
 * the rights to use, copy, modify, merge, publish, distribute, sublicense,
 * and/or sell copies of the Software, and to permit persons to whom the
 * Software is furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice (including the next
 * paragraph) shall be included in all copies or substantial portions of the
 * Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.  IN NO EVENT SHALL
 * THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 *
 */

#include "pan_context.h"
#include "pan_util.h"
#include "pan_format.h"

#include "util/u_format.h"

static void
panfrost_invert_swizzle(const unsigned char *in, unsigned char *out)
{
        /* First, default to all zeroes to prevent uninitialized junk */

        for (unsigned c = 0; c < 4; ++c)
                out[c] = PIPE_SWIZZLE_0;

        /* Now "do" what the swizzle says */

        for (unsigned c = 0; c < 4; ++c) {
                unsigned char i = in[c];

                /* Who cares? */
                if (i < PIPE_SWIZZLE_X || i > PIPE_SWIZZLE_W)
                        continue;

                /* Invert */
                unsigned idx = i - PIPE_SWIZZLE_X;
                out[idx] = PIPE_SWIZZLE_X + c;
        }
}

static struct mali_rt_format
panfrost_mfbd_format(struct pipe_surface *surf)
{
        /* Explode details on the format */

        const struct util_format_description *desc =
                util_format_description(surf->format);

        /* The swizzle for rendering is inverted from texturing */

        unsigned char swizzle[4];
        panfrost_invert_swizzle(desc->swizzle, swizzle);

        /* Fill in accordingly, defaulting to 8-bit UNORM */

        struct mali_rt_format fmt = {
                .unk1 = 0x4000000,
                .unk2 = 0x1,
                .nr_channels = MALI_POSITIVE(desc->nr_channels),
                .unk3 = 0x4,
                .flags = 0x8,
                .swizzle = panfrost_translate_swizzle_4(swizzle),
                .unk4 = 0x8
        };

        if (desc->colorspace == UTIL_FORMAT_COLORSPACE_SRGB)
                fmt.flags |= MALI_MFBD_FORMAT_SRGB;

        /* Set flags for alternative formats */

        if (surf->format == PIPE_FORMAT_B5G6R5_UNORM) {
                fmt.unk1 = 0x14000000;
                fmt.nr_channels = MALI_POSITIVE(2);
                fmt.unk3 |= 0x1;
        } else if (surf->format == PIPE_FORMAT_R11G11B10_FLOAT) {
                fmt.unk1 = 0x88000000;
                fmt.unk3 = 0x0;
                fmt.nr_channels = MALI_POSITIVE(4);
        }

        return fmt;
}


static void
panfrost_mfbd_clear(
                struct panfrost_job *job,
                struct bifrost_framebuffer *fb,
                struct bifrost_fb_extra *fbx,
                struct bifrost_render_target *rt)
{
        if (job->clear & PIPE_CLEAR_COLOR) {
                rt->clear_color_1 = job->clear_color;
                rt->clear_color_2 = job->clear_color;
                rt->clear_color_3 = job->clear_color;
                rt->clear_color_4 = job->clear_color;
        }

        if (job->clear & PIPE_CLEAR_DEPTH) {
                fb->clear_depth = job->clear_depth;
        }

        if (job->clear & PIPE_CLEAR_STENCIL) {
                fb->clear_stencil = job->clear_stencil;
        }
}

static void
panfrost_mfbd_set_cbuf(
                struct bifrost_render_target *rt,
                struct pipe_surface *surf)
{
        struct panfrost_resource *rsrc = pan_resource(surf->texture);

        unsigned level = surf->u.tex.level;
        unsigned first_layer = surf->u.tex.first_layer;
        assert(surf->u.tex.last_layer == first_layer);
        int stride = rsrc->bo->slices[level].stride;

        mali_ptr base = panfrost_get_texture_address(rsrc, level, first_layer);

        rt->format = panfrost_mfbd_format(surf);

        /* Now, we set the layout specific pieces */

        if (rsrc->bo->layout == PAN_LINEAR) {
                rt->format.block = MALI_MFBD_BLOCK_LINEAR;
                rt->framebuffer = base;
                rt->framebuffer_stride = stride / 16;
        } else if (rsrc->bo->layout == PAN_TILED) {
                rt->format.block = MALI_MFBD_BLOCK_TILED;
                rt->framebuffer = base;
                rt->framebuffer_stride = stride;
        } else if (rsrc->bo->layout == PAN_AFBC) {
                rt->format.block = MALI_MFBD_BLOCK_AFBC;

                unsigned header_size = rsrc->bo->slices[level].header_size;

                rt->framebuffer = base + header_size;
                rt->afbc.metadata = base;
                rt->afbc.stride = 0;
                rt->afbc.unk = 0x30009;

                /* TODO: Investigate shift */
                rt->framebuffer_stride = stride << 1;
        } else {
                fprintf(stderr, "Invalid render layout (cbuf)");
                assert(0);
        }
}

static void
panfrost_mfbd_set_zsbuf(
                struct bifrost_framebuffer *fb,
                struct bifrost_fb_extra *fbx,
                struct pipe_surface *surf)
{
        struct panfrost_resource *rsrc = pan_resource(surf->texture);

        unsigned level = surf->u.tex.level;
        assert(surf->u.tex.first_layer == 0);

        unsigned offset = rsrc->bo->slices[level].offset;

        if (rsrc->bo->layout == PAN_AFBC) {
                mali_ptr base = rsrc->bo->gpu + offset;
                unsigned header_size = rsrc->bo->slices[level].header_size;

                fb->mfbd_flags |= MALI_MFBD_EXTRA;

                fbx->flags =
                        MALI_EXTRA_PRESENT |
                        MALI_EXTRA_AFBC |
                        MALI_EXTRA_AFBC_ZS |
                        MALI_EXTRA_ZS |
                        0x1; /* unknown */

                fbx->ds_afbc.depth_stencil = base + header_size;
                fbx->ds_afbc.depth_stencil_afbc_metadata = base;
                fbx->ds_afbc.depth_stencil_afbc_stride = 0;

                fbx->ds_afbc.zero1 = 0x10009;
                fbx->ds_afbc.padding = 0x1000;
        } else if (rsrc->bo->layout == PAN_LINEAR) {
                int stride = rsrc->bo->slices[level].stride;
                fb->mfbd_flags |= MALI_MFBD_EXTRA;

                fbx->flags |= MALI_EXTRA_PRESENT | MALI_EXTRA_ZS | 0x1;

                fbx->ds_linear.depth = rsrc->bo->gpu + offset;
                fbx->ds_linear.depth_stride = stride;
        } else {
                assert(0);
        }
}

/* Helper for sequential uploads used for MFBD */

#define UPLOAD(dest, offset, src, max) { \
        size_t sz = sizeof(*src); \
        memcpy(dest.cpu + offset, src, sz); \
        assert((offset + sz) <= max); \
        offset += sz; \
}

static mali_ptr
panfrost_mfbd_upload(
                struct panfrost_context *ctx,
                struct bifrost_framebuffer *fb,
                struct bifrost_fb_extra *fbx,
                struct bifrost_render_target *rts,
                unsigned cbufs)
{
        off_t offset = 0;

        /* There may be extra data stuck in the middle */
        bool has_extra = fb->mfbd_flags & MALI_MFBD_EXTRA;

        /* Compute total size for transfer */

        size_t total_sz =
                sizeof(struct bifrost_framebuffer) +
                (has_extra ? sizeof(struct bifrost_fb_extra) : 0) +
                sizeof(struct bifrost_render_target) * cbufs;

        struct panfrost_transfer m_f_trans =
                panfrost_allocate_transient(ctx, total_sz);

        /* Do the transfer */

        UPLOAD(m_f_trans, offset, fb, total_sz);

        if (has_extra)
                UPLOAD(m_f_trans, offset, fbx, total_sz);

        for (unsigned c = 0; c < cbufs; ++c) {
                UPLOAD(m_f_trans, offset, &rts[c], total_sz);
        }

        /* Return pointer suitable for the fragment section */
        return m_f_trans.gpu | MALI_MFBD | (has_extra ? 2 : 0);
}

#undef UPLOAD

/* Creates an MFBD for the FRAGMENT section of the bound framebuffer */

mali_ptr
panfrost_mfbd_fragment(struct panfrost_context *ctx, bool has_draws)
{
        struct panfrost_job *job = panfrost_get_job_for_fbo(ctx);

        struct bifrost_framebuffer fb = panfrost_emit_mfbd(ctx, has_draws);
        struct bifrost_fb_extra fbx = {};
        struct bifrost_render_target rts[4] = {};

        /* XXX: MRT case */
        fb.rt_count_2 = 1;
        fb.mfbd_flags = 0x100;

        /* TODO: MRT clear */
        panfrost_mfbd_clear(job, &fb, &fbx, &rts[0]);

        for (int cb = 0; cb < ctx->pipe_framebuffer.nr_cbufs; ++cb) {
                struct pipe_surface *surf = ctx->pipe_framebuffer.cbufs[cb];
                panfrost_mfbd_set_cbuf(&rts[cb], surf);
        }

        if (ctx->pipe_framebuffer.zsbuf) {
                panfrost_mfbd_set_zsbuf(&fb, &fbx, ctx->pipe_framebuffer.zsbuf);
        }

        /* For the special case of a depth-only FBO, we need to attach a dummy render target */

        if (ctx->pipe_framebuffer.nr_cbufs == 0) {
                struct mali_rt_format null_rt = {
                        .unk1 = 0x4000000,
                        .unk4 = 0x8
                };

                rts[0].format = null_rt;
                rts[0].framebuffer = 0;
                rts[0].framebuffer_stride = 0;
        }

        /* When scanning out, the depth buffer is immediately invalidated, so
         * we don't need to waste bandwidth writing it out. This can improve
         * performance substantially (Z32_UNORM 1080p @ 60fps is 475 MB/s of
         * memory bandwidth!).
         *
         * The exception is ReadPixels, but this is not supported on GLES so we
         * can safely ignore it. */

        if (panfrost_is_scanout(ctx)) {
                job->requirements &= ~PAN_REQ_DEPTH_WRITE;
        }

        /* Actualize the requirements */

        if (job->requirements & PAN_REQ_MSAA) {
                rts[0].format.flags |= MALI_MFBD_FORMAT_MSAA;

                /* XXX */
                fb.unk1 |= (1 << 4) | (1 << 1);
                fb.rt_count_2 = 4;
        }

        if (job->requirements & PAN_REQ_DEPTH_WRITE)
                fb.mfbd_flags |= MALI_MFBD_DEPTH_WRITE;

        /* Checksumming only works with a single render target */

        if (ctx->pipe_framebuffer.nr_cbufs == 1) {
                struct pipe_surface *surf = ctx->pipe_framebuffer.cbufs[0];
                struct panfrost_resource *rsrc = pan_resource(surf->texture);
                struct panfrost_bo *bo = rsrc->bo;

                if (bo->checksummed) {
                        unsigned level = surf->u.tex.level;
                        struct panfrost_slice *slice = &bo->slices[level];

                        fb.mfbd_flags |= MALI_MFBD_EXTRA;
                        fbx.flags |= MALI_EXTRA_PRESENT;
                        fbx.checksum_stride = slice->checksum_stride;
                        fbx.checksum = bo->gpu + slice->checksum_offset;
                }
        }

        /* We always upload at least one (dummy) cbuf */
        unsigned cbufs = MAX2(ctx->pipe_framebuffer.nr_cbufs, 1);

        return panfrost_mfbd_upload(ctx, &fb, &fbx, rts, cbufs);
}
