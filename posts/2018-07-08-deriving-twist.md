---
title: Deriving instances with a twist
keywords: [haskell, haskell-tricks]
---

When defining new data types, instance derivation can generate basic
functionality for free. However, that mechanism cannot handle all types.
For example, deriving `Eq` or `Show` (using the `stock` strategy)
assumes that all constructor fields are instances of `Eq` and `Show`.

But if that condition is only broken by one field among many others,
it would be a waste if the work done by deriving could not be reused.

<details class="code-details">
  <summary>Extensions and imports for this Literate Haskell file</summary>
\begin{code}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}

import Data.Coerce (coerce)
\end{code}
</details>

Problem example
===============

Here is a `Thing` with four fields, one of which is a function. Let's try to
derive `Show` for it.

\begin{code}
data Thing = Thing Int String Bool (Int -> Int)
  deriving Show
\end{code}

The compiler generates the following code to recursively show each field
and put the results together, inserting parentheses where necessary.

```haskell
instance Show Thing where
  showsPrec a_a1ar (Thing b1_a1as b2_a1at b3_a1au b4_a1av)
    = showParen
        (a_a1ar >= 11)
        ((.)
           (showString "Thing ")
           ((.)
              (showsPrec 11 b1_a1as)
              ((.)
                 showSpace
                 ((.)
                    (showsPrec 11 b2_a1at)
                    ((.)
                       showSpace
                       ((.)
                          (showsPrec 11 b3_a1au)
                          ((.) showSpace (showsPrec 11 b4_a1av))))))))
```

That code is then typechecked, and that fails because `b4_a1av` is a function,
of type `Int -> Int`, and there is no `Show` instance for that type.

A `Show` instance for functions
===============================

An obvious workaround is to add a dummy instance for functions, that
produces some placeholder.

\begin{code}
instance Show (a -> b) where
  show _ = "_"
\end{code}

In fact, there is such an instance defined in `base` for this purpose, in
[`Text.Show.Functions`](https://hackage.haskell.org/package/base-4.11.1.0/docs/Text-Show-Functions.html),
so we could just import it.
We can use the empty import list to indicate that nothing apart from the
instance comes from this module.

```haskell
import Text.Show.Functions ()
```

Adding such an instance makes more `Show` instances derivable. However, dummy
instances for functions can make some common mistakes harder to detect at
compile time, such as forgetting to apply a function to an argument.

Furthermore, instances are always reexported, so if we're writing a library,
this also pollutes the environment of users with that controversial instance.

Parameterizing types
====================

A better solution is to hide the problematic field from the deriving mechanism.
We start by replacing the field type with a new parameter. (`Thing0` is a new
name for `Thing` to avoid conflicts in this Literate Haskell file.)

\begin{code}
data Thing0_ x = Thing0 Int String Bool x

type Thing0 = Thing0_ (Int -> Int)
\end{code}

The goal is to be able to apply `show` to `Thing0`, without manually
implementing `Show` for it (which is especially desirable if `Thing0` is a big
type).

First, we can standalone-derive a `Show` instance  for a specialization of
`Thing0_` at a type with a `Show` instance. We will then use that
as the basis for the actual instance.

The `INCOHERENT` pragma makes it so that this instance can be ignored by the
compiler later, avoiding instance overlap errors. It is fine to use this pragma
here because the final instance will behave identically anyway. The only
purpose of this first instance is to get code derived by the compiler
somewhere accessible.

\begin{code}
deriving instance {-# INCOHERENT #-} Show (Thing0_ (Opaque x))
\end{code}

where `Opaque` is the following `newtype` with a dummy instance that ignores
its contents:

\begin{code}
newtype Opaque a = Opaque a

instance Show (Opaque a) where
  show _ = "_"
\end{code}

Now we can write the actual `Show` instance by "coercing" the derived one above.
Specializing `showsPrec` to `Thing0_ (Opaque x)` cause the above instance to be
chosen rather than the one we're defining `Thing0_ x` (even though instance
resolution can be recursive like that, e.g., `Eq` for `[]`) because the above
one is the *most specific* one that matches `Thing (Opaque x)`.

\begin{code}
instance Show (Thing0_ x) where
  showsPrec = coerce (showsPrec :: Int -> Thing0_ (Opaque x) -> ShowS)
\end{code}

Here we go.

\begin{code}
main :: IO ()
main = print (Thing0 1 "two" True (+ 4) :: Thing0)

-- Output:    Thing0 1 "two" True _
\end{code}

Ew?
===

`INCOHERENT` instances are always dirty hacks, because instance resolution can
easily become unpredicable when they are abused.[^aeson] We used this pragma to
"hide" an instance created using `deriving`, usually the `stock` instances
for a few standard type classes. This trick also works for `anyclass` deriving
of instances having default implementations that are otherwise not exported.

But once we have a "default implementation" of some form, we can modify it to
work with an altered representation of a newly defined type using more common
methods (`coerce` being the cheapest one).
For this reason, libraries should export default implementations of type class
methods as separate functions, even if they use `DefaultSignatures`.

For example, we can use the same technique to derive a tweaked `Show` instance
from a `GHC.Generics` implementation (from my package
[*generic-data*](https://hackage.haskell.org/package/generic-data-0.1.1.0/docs/Generic-Data.html#v:gshowsPrec)[^1],
which also defines the `Opaque` wrapper):

```haskell
{-# LANGUAGE DeriveGeneric, ScopedTypeVariables #-}
import Data.Coerce (coerce)
import GHC.Generics (Generic)
import Generic.Data (Opaque(..), gshowsPrec)  -- generic-data

data Thing_ x = Thing Int String Bool x
  deriving Generic

type Thing = Thing_ (Int -> Int)

instance Show (Thing_ x) where
  showsPrec = coerce (gshowsPrec :: Int -> Thing_ (Opaque x) -> ShowS)

main = print (Thing 1 "2" True (+ 4) :: Thing)
```

[^aeson]: [*aeson* uses `INCOHERENT`
  instances](https://github.com/bos/aeson/blob/550b03d62021c93da58d40014280486d1c82726e/Data/Aeson/Types/ToJSON.hs#L1020)
  to implement the `omitNothingFields` option. One possibly surprising consequence
  is that, for a parameterized `Record` type, having derived an instance
  `forall a. ToJSON a => ToJSON (Record a)` with `omitNothingFields=True`,
  using that instance with `a = Maybe ()` will *not* allow fields originally of
  type `a` to be omitted.
[^1]: See also my previous post [An old and new library for generic deriving](../posts/2018-03-28-generic-data.html).
