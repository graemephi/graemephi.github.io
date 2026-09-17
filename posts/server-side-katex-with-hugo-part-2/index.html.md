---
title: "Server-side KaTeX With Hugo: Part 2"
date: 2020-01-19
more: false
---

So, despite saying I didn't want to do this in my [last post](/posts/static-katex-with-hugo/) on this, [I went and forked Hugo](https://github.com/graemephi/kahugo). Now rendering with KaTeX is way faster, and basically free when using `hugo server`. 
<!--more-->

This was more driven by curiosity than a desire to make things fast. At some point a couple weeks ago I was reminded of [QuickJS](https://bellard.org/quickjs/), and from there it was a short series of small steps to my downfall. QuickJS really enabled this. It was easy to replace the javascript from my previous post with an executable that ran the qjs interpreter on KateX bytecode, and easy to then link it to a Haskell program that drove Pandoc as a library rather than using the command line. Having done _that_, getting Goldmark, Hugo's markdown processor, to render TeX using KaTeX was also a small amount of work.  

Rather than this post just being, "hey, I'm doing this now instead," I guess I'll talk a bit more about it.

Goldmark is fairly extensible so shoe-horning in TeX-awareness just means telling Goldmark's parser to call our code when it hits a `$`: I put maths between `$` and `$$`, so `$x$` gets rendered as $x$. But taking responsibility for parsing any markdown yourself means you have to think about weird edge cases[^1]. 

Take links. Links in markdown have the following syntax: `[foo](bar.tld)`. So, how should `[$foo](bar.tld$)` be parsed? In my opinion, there is a correct answer here: that's a link. I've found people citing some old RFC that prohibits $ in urls, but [they're valid](https://en.wikipedia.org/wiki/$). Anyone who writes `[$](en.wikipedia.org/wiki/$)` wants that to be a link, and I can't think of any exceptions. 

By the way, that $ in the previous paragraph also needs to be parsed as a $, and not the opening dollar of maths.

So, those are links. What about `[$[0, 1]$](url)`? There's something satisfying about being able to link maths: [$[0,1]$](https://en.wikipedia.org/wiki/Unit_interval). So, that first example we want to not parse as TeX, and the second we do, and in order to support both we have to know if we are inside a link or not. Parsing! 

Thankfully, we have a working TeX-aware markdown processor already: Pandoc. After fixing up some minor differences between how Goldmark and Pandoc renders the HTML, Pandoc, with the old filter from last time, can [generate a bunch of test cases](https://github.com/graemephi/goldmark-qjs-katex/blob/master/gen.go). I don't follow Pandoc's example in one place; Pandoc's rule for allowing `$[]$` inside links seems to be that the brackets must be balanced. I opted for requiring `[` to appear before `]` (which would otherwise close the link).

Next, some threading stuff. Hugo uses goroutines, and the QuickJS runtime can only be used single-threaded. We don't want to make each goroutine queue to access QuickJS, and we also want to keep our changes to Hugo to a minimum. From a C perspective, there's a really obvious solution: give each thread its own QuickJS runtime using thread-local storage. But goroutines aren't threads, and the Go scheduler wants to schedule goroutines to any thread it likes. This means that between two calls into QuickJS the goroutine can move thread, and whatever way we have of communicating with the QuickJS runtime from Go needs to be okay with this happening.

What I decided to do was to just never allocate anything that would be passed back to Go, and have the Go code pass in memory instead. This makes the C code pure as far as Go is concerned, so we can use thread-local and not worry about the Go scheduler. It also means we don't have to call free, which is always good.

Last time, I reported that a single page with TeX took half a second to render. Now, my entire site takes 240ms. Without KaTeX, it's around 150ms. I still find this a bit slower than it really ought to be, but I suppose for how little work it was, it's pretty good.

[^1]: The [Commonmark spec](https://spec.commonmark.org/) is a great resource for all the markdown parsing gotchas you've never thought about before.
