---
title: Hiding code blocks in literate programming blogs
keywords: [blogging, html]
description: Hide your extension and imports in Literate Haskell.
---

Writing a blogpost in Literate Haskell makes it easier for readers to
put the ideas of the blogpost into practice, by providing a code sample that is
commented, compilable and error-free.

However, one annoyance is that such blogposts start with some setup code like
this:

```haskell
{-# LANGUAGE Kitchen, TwoBedrooms, BigLivingRoom, Bathroom #-}
module House where
import Furniture (Bed, Sofa, KitchenSink)
```

This setup can get quite long, and my guess is that it does little for people
familiar with Haskell, and it pushes away others who are unfamiliar with the
language.

So if this is such noise, we can comment it out. Hopefully, we
can freely mix HTML and Markdown (except on reddit).

<!-- This is all an HTML comment.
\begin{code}
{-# LANGUAGE Kitchen, TwoBedrooms, BigLivingRoom, Bathroom #-}
module House where
import Furniture (Bed, Sofa, KitchenSink)
\end{code}
-->

There is some invisible code above this paragraph, but it's in the
Markdown source, in plain sight to a Haskell compiler, looking like this:

```html
<!-- This is all an HTML comment.
\begin{code}
{-# LANGUAGE Kitchen, TwoBedrooms, BigLivingRoom, Bathroom #-}
module House where
import Furniture (Bed, Sofa, KitchenSink)
\end{code}
-->
```

In my opinion, it is occasionally useful to see that bit of code, so rather
than definitely hiding it in a comment, I choose to put it in a collapsed
section:

<details class="code-details">
<summary>Extensions and imports for this Literate Haskell file</summary>
\begin{code}
{-# LANGUAGE Kitchen, TwoBedrooms, BigLivingRoom, Bathroom #-}
module House where
import Furniture (Bed, Sofa, KitchenSink)
\end{code}
</details>

The source looks as follows. This is a plain HTML feature, no CSS or JavaScript
nonsense: [the `<details>` element](https://developer.mozilla.org/en-US/docs/Web/HTML/Element/details).

```html
<details class="code-details">
<summary>Extensions and imports for this Literate Haskell file</summary>
\begin{code}
{-# LANGUAGE Kitchen, TwoBedrooms, BigLivingRoom, Bathroom #-}
module House where
import Furniture (Bed, Sofa, KitchenSink)
\end{code}
</details>
```

There seems to be a common misconception that "moving stuff" on the web can
only be implemented in JavaScript or with arcane CSS tricks.
I certainly thought so for a while, so I'm writing this piece partly to dispel
that notion, and make `<details>` a bit more well-known.
