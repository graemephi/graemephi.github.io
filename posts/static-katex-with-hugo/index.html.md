---
title: "Server-side KaTeX With Hugo"
date: 2019-12-15T18:01:49Z
more: false
---
__Update__ (2020-01-19): [I lasted some 3 weeks before gettng rid of this](/posts/server-side-katex-with-hugo-part-2). Also, I've changed the title from 'static' to 'server-side' which is more accurate.

---

[Hugo](https://gohugo.io/) is a static website generator written in Go. [Katex](https://katex.org/) is a math typesetting library written in Javascript. This site uses them both.

<!--more-->

I keep javascript turned off on websites unless white-listed. I notice when websites fail to load without javascript and I notice when websites don't require it at all. I'd like mine to be one of the latter, but also, I want to have proper maths typesetting. Now, usually the way you get maths onto the internet is you dump some LaTeX surrounded by \$\$ into a document, embed some random javascript file, and everything happens automatically. I don't like that.

What I want instead is for Hugo to typeset my maths. But I still want `hugo server` to render everything properly, and I don't want a complicated multi-stage build process, and I _really_ don't want to maintain my own build of Hugo. Basically, I want to be able to dump the Hugo executable somewhere and have everything work when I type

```terminal
cd blog
hugo
```

Unfortunately, Hugo doesn't really support Katex per se. It uses Markdown parsers that know to leave text surrounded by \$\$ alone, and Katex searches for them at page-load. These parsers are compiled into Hugo, and at no point can you intercept them to do further processing of your own.

But Hugo supports [Pandoc](https://pandoc.org/), and Pandoc is happy to pass you a copy of the AST to fiddle with before it actually renders anything. What's more, Pandoc knows that \$ means inline maths and \$\$ means display maths, so we can just read that information off of the AST and have Katex format it as inline or display appropriately.

So, the outlines of a solution are starting to appear. We need to write a [Pandoc filter](https://pandoc.org/filters.html) that replaces LaTeX maths with Katex's HTML typesetting.

But there is a problem. There are two problems.

1. Hugo's support of Pandoc is fairly limited. The command-line parameters it uses are hard-coded into Hugo, and they seem to just be whatever the guy who committed the PR adding Pandoc support needed (thanks to that guy, by the way. We couldn't get even this far without him). We need to pass our own arguments to get Pandoc to filter anything.

2. Pandoc doesn't support passing arguments to filters. We can tell Pandoc to execute `node`, but we can't tell Pandoc to execute `node katex.js`. This seems to be a weird artifact of how Pandoc shells out to filters, at least on Windows. 

There is a simple, elegant, and generally terrible solution to both of these problems.

The reason Hugo can call out to Pandoc, and the reason Pandoc can call out to Node, at all, is because they're both in `PATH`. So, we just have to arrange `PATH` to our liking before running Hugo. I always run Hugo from VSCode, so I can do this on a per-project basis, and not contaminate the rest of my system with this, ah, workaround.

I didn't investigate the best way to do this; I suspect on Linux it would be a bit easier. But, on Windows, I didn't want to think too hard about it, so I just compiled a couple C programs. Now I have the following folder structure:

```terminal
blog/
├── content/
├── ...
└── pandoc/
     ├── node_modules/
     ├── katex.exe
     ├── katex.js
     └── pandoc.exe
```

The first directory in `PATH` whenever I run Hugo is `path/to/blog/pandoc`. `node_modules` contains only Katex, required by `katex.js`, the pandoc filter. `katex.exe` opens a pipe to `node pandoc/katex.js` and `pandoc.exe` opens a pipe to `pandoc --katex --filter=katex`. Full paths to these are hard-coded into the executables, because I never learn.

Then, in the front matter for a post that needs Katex, we use the Pandoc renderer:

```terminal
---
title: "Static Katex With Hugo"
date: 2019-12-16T02:01:49Z
markup: pandoc
---
```

The code for the executables and Pandoc filter are pretty rote. [Here's a gist, if you're interested.](https://gist.github.com/graemephi/7c60093f342b6dabf00d976492b6c91f) 

There's one big problem with this. It's slow. For every post with maths to typeset, we have to shell out to pandoc and then it has to shell out to Node. This takes around 500ms per page for me, as opposed to 40ms for other pages. Pandoc without a filter, by the way, takes about 80ms. I can live with this for single posts as I'm writing, but I suspect before long I won't be able to stand how long a full build takes.

That 500ms is mostly spent starting up Node and initialising Katex. So, one solution is to keep Node running and pass all the posts to a single instance. That doesn't sound too hard to do myself, but my hope is Hugo will have made some progress on that themselves before I feel the need to--there are now so many preprocessors written in javascript they're already thinking about it, as far as I know. But what you really want is a LaTeX to HTML renderer written in Go.

$$ e^{i\pi} + 1 = 0 $$
