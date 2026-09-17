---
title: "deep sky object"
date: 2020-05-20
tags: [procedural generation, graphics]
---

A couple months ago I set [@tiny_dso](https://twitter.com/tiny_dso) running. It's a twitter art bot, which I guess is less of an exciting thing nowadays, but it's an idea I've wanted to do for at least a few years now: turn [@tiny_star_field](https://twitter.com/tiny_star_field)\'s tweets into computer generated imitations of astrophotography.

tiny_star_field is getting a bit intermittent nowadays, so I set the bot to work it's way backwards through tiny_star_field\'s old tweets. I wanted to make it something you could follow for a long time and still be surprised by, rather than something you'd scroll down once and see everything it's capable of. We'll see if I succeeded there; I'm not sure. It's hard to tweak the parameters for that kind of thing, especially since when I'm working on it I generate hundreds of images, which skews my perception of what's happening too much or not enough.

It's been running for a while, so I can let it speak for itself:

{{< img-multi
    "EXeYst0XkAITLkB.png"
    "ERjccJlXYAEwypn.png"
    "ESHpGWuW4AEAUlJ.png"
    "ETJqBfgWoAIiTNk.png"
    "EShIIcjXQAEHntm.png" 
    "EW0CH6_WkAQaKBw.png"
>}}

I don't have it in me to write more about it with a coherent structure so I'm just going to dump some notes on the implementation here. I wrote most of the code a couple years ago, returned to it a couple times, and really just decided to get it running on twitter recently. There's probably some stuff I intended to do that I've completely forgotten about, so this is mostly technical details I can read out of the code.

---

The bot part that talks to twitter is just javascript that lives on [glitch](https://tiny-dso.glitch.me/). The [image generator](https://github.com/graemephi/starfield) is an executable that spits pngs out of standard out.

---

It's written in ion, the language Per Vognsen created for [bitwise](https://github.com/pervognsen/bitwise). It's basically C99, except you can omit type names sometimes, you use `.` instead of `->`, and there is some notion of modules. Oh, and it has out of order declarations. I think when I started writing this the language was fully 2 weeks old. It looked pretty cool and I didn't want to use any libraries in this project[^1], so it fit my needs fine. As new and unfinished compilers go, it was pretty reliable. But it didn't receive a whole lot of development past that. Coming back to the code to get the images onto twitter I found it had some bugs to work around, mostly to do with getting it to generate code that would compile on linux[^2].

I found tweaking the image generation intolerable if it took more than half a second or so, so I spent some time optimising it. That means multi-threading, vector instructions, and a lot of profiling. This wasn't a problem with ion, because it can generate C code, and will take your word for it if you tell it some function or type exists. Also, it uses the C preprocessor to get line information to debuggers (and profilers). All in all, very nice. Good language.

---

I learned early on that the easiest way to render a passable looking star was to place a single white pixel on an otherwise blank texture and just use [mipmaps]({{< ref "calculating-LOD" >}}) to filter it for rendering. Rotating a shrunken, very bright, pixel gets you endless variation on how the stars look.

Pixel values fall in the range $[0, 1]$ and, if you think on it, stars really ought to be much brighter than that. So this method works best if you just let your values overflow then adaptively crunch the image back down with post-processing. Most astrophotography has gone through reams of processing, anyway.

---

All the "pixel shader"-like work is done using a pair of functions, `pixel_iter_begin` and `pixel_iter_next`. Rather than explaining what they do, here's the code for drawing a texture:

```c
func draw_tex(dest: Image*, target: Rect, tex: Tex*) {
    lod := compute_lod_level(dest.size, target.size, tex.size);
    for (it := pixel_iter_begin(dest, target); pixel_iter_next(&it)) {
        rgba := tex_lookup_lod(tex, it.npos, lod);
        *it.pixel = color_blend(*it.pixel, rgba);
    }
}
```

This would work in C, but it'd look like `for (PixelIter it = ...; pixel_iter_next(&it);) {} `. Note that trailing semicolon--`next` gets called before, not after, every iteration. Now, this way of iterating over pixels is very general and so pretty slow. It just makes doing pixel-by-pixel stuff extremely low friction to write code for. I think most programmers would reach for function pointers or generics to separate the pixel shading code from the iteration, but it's not necessary, and a pain to actually use. It turns out that the iterator code was not performance critical at all, so the overhead didn't matter much, and the implementation is also very naive.

The pixel iterator also takes care of multi-threading. Here's the definition of the `Image` struct:

```c
struct Image {
    pixels: Color*;
    size: int2;
    wr: WritableRegion;
    stride: int;
    offset: int;
}
```

The `WritableRegion` allows the pixel iterator to clip the pixels being iterated over to the block the thread is responsible for rendering. The code that actually uses the pixel iterator doesn't have to think about blocks or threads at all. It's nice!  

The drawback is that if you want to draw into a side buffer before compositing into a destination buffer, then you end up allocating the full `size` and only use a block in the middle somewhere. Avoiding that is what `stride` and `offset` are for. Usually, you'd sample an individual pixel like this:
```
sample := img.pixels[pos.x + pos.y*img.x];
```
Instead, I do this:
```
sample := img.pixels[pos.x + pos.y*img.stride - img.offset];
```
This way, you can sample an image by talking about coordinates in $[0, 1]^2$ while the image only has storage allocated for $[\frac{3}{8}, \frac{4}{8}]^2$ (for example), and all it takes is an extra subtraction.[^3] 

---

All the star colours are chosen by linearly interpolating between RGB values obtained by colour-picking from [wikipedia](https://en.wikipedia.org/wiki/Stellar_classification#/media/File:TernaryColorTmap.PNG). They're pretty close so I never had to do anything fancy involving splines or colour space transformations.

---

Most of the look comes from blurring the entire image and layering the blurred and unblurred parts together in arbitrary ways. Think blend modes in image editors. It turns out it's pretty easy to write a [fast](https://fgiesen.wordpress.com/2012/07/30/fast-blurs-1/) [blur](https://fgiesen.wordpress.com/2012/08/01/fast-blurs-2/), and you don't even have to think about how to vectorise it because everything is in 4 independent colour components already.

The diffraction spikes are blurs, too. I think a lot of people jump to the fourier transform to do diffraction spikes but I couldn't be bothered with that--just take a box filter with a hole cut out of the middle and repeat it a few times. Same principle as using iterated box filters to approximate a gaussian blur, as in the links above, but non-separable this time, so you need to do vertical and horizontal passes both on the original image (i.e., not in series). 

If you look at actual diffraction spikes you can see different colours get diffracted more or less. I think this is probably the same principle as [ground waves](https://en.wikipedia.org/wiki/Surface_wave#Ground_wave), where lower frequency radio waves diffract around the surface of the Earth more than higher frequency waves. So, I use different sizes of filter on each colour component; larger for larger wavelengths, I think, but you can only do so much in RGB.

Honestly, though, the diffraction code is kind of terrible. Every time I think about it I think of a better way to implement it. For example, I haven't vectorised it, because the memory accesses are different for each colour component. But to get diffractions at an angle I do a song and dance where I rotate a copy of the entire image to another buffer--this would be a good time to rearrange the data into colour planes to make it vectorisable: multiple rows of a plane at once. I could even reuse the other blur code at that point, and implement the convolution `(A - B)x` as `Ax - Bx`. But I don't! And I never will, now.

---

The nebulas are a hot mess of noise functions, mostly [cellular noise](https://thebookofshaders.com/12/) with a healthy dose of [domain warping](https://iquilezles.org/www/articles/warp/warp.htm). It all happens on a 2D plane; I didn't want to think about 3D volumetric anything for this project.

I do the cellular noise in fixed-point arithmetic. This was out of curiosity more anything else; the implementation comes pretty naturally from wanting to use a [certain SSE2 instruction](https://software.intel.com/sites/landingpage/IntrinsicsGuide/#text=madd&techs=SSE2&expand=3505). I'd like to write more about it, but not in this post.

---

By the way, [glitch](https://glitch.com/) is pretty cool. It spins up an instance of who-knows-what for you and clang is just sitting there, waiting to compile whatever you want. A very old version of clang. That doesn't have the intrinsics I use. Well, it has gcc, too.

If you've scrolled all the way down here and only now have decided you want the bot's twitter, [here you go](https://twitter.com/tiny_dso).

[^1]: Except [stb_image_write.h](https://github.com/nothings/stb) for the pngs. On Windows, I don't write pngs, but render to a buffer managed by SDL. So they both have one dependency, but it's a different dependency, I guess.

[^2]: I think most, if not all, of those bugs have been fixed in [this fork](https://github.com/uucidl/bitwise).

[^3]: You could also shunt the `pixels` pointer off into no-mans-land and pray  you get all the new weird boundary conditions right.
