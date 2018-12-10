---
title: Naming abstraction
description: Abstract naming
keywords: Haskell, names, quiz
---

\begin{code}
{-# LANGUAGE GADTs, NoImplicitPrelude #-}
module Naming.Abstraction where
\end{code}

Naming things is hard, so I made a little game to practice thinking
about things without names, or recognize things under unfamilar names.

Here are some things with obfuscated names. Can you tell what they do?
How would you name them? Do they have well-known names?

[Link to gist (annotated version).](https://gist.github.com/Lysxia/fe1ffd54ecb1daef0998c6c46c8851d7)

Fruits
------

\begin{code}
-- flip id, flip ($), (Data.Function.&)
apple :: banana -> (banana -> cherry) -> cherry
apple date fig = fig date

-- \f g -> fix (f . g)
-- f (g (f (g (f (g ...)))))
grapes :: (kiwi -> kiwi) -> (kiwi -> kiwi) -> kiwi
grapes lemon mango = lemon (grapes mango lemon)

-- const
nutmeg :: plum -> olive -> plum
nutmeg raspberry strawberry = raspberry
\end{code}

Animals
-------

\begin{code}
-- map for Snoc lists
albatross :: (beluga -> beluga) -> Cat beluga -> Cat beluga
albatross dolphin Elephant = Elephant
albatross dolphin (Frog giraffe hedgehog) =
  albatross dolphin giraffe `Frog` dolphin hedgehog

-- Snoc lists (lists with flipped Cons/(:))
data Cat iguana = Elephant | Frog (Cat iguana) iguana

-- undefined, but it's funny that it type checks
jaguar :: kangaroo -> kangaroo
jaguar = jaguar jaguar

-- Rose trees
data Lion nyala = Mackerel nyala (Cat (Lion nyala))

-- foldr for Snoc lists
opossum :: penguin -> (penguin -> quail -> penguin) -> Cat quail -> penguin
opossum rooster snail Elephant = rooster
opossum rooster snail (Frog tiger unicorn) =
  opossum rooster snail tiger `snail` unicorn

-- Functor
class Vulture wallaby where
  -- fmap
  fox :: (yeti -> zebra) -> wallaby yeti -> wallaby zebra
\end{code}

Animals: déjà vu
----------------

\begin{code}
-- const []
alpaca :: (beluga -> beluga) -> Cat beluga -> Cat beluga
alpaca dolphin Elephant = Elephant
alpaca dolphin (Frog giraffe hedgehog) =
  alpaca dolphin giraffe

-- Monad without return.
class Vultures wallaby where
  -- (=<<)
  lynx :: (yeti -> wallaby zebra) -> wallaby yeti -> wallaby zebra
\end{code}

Vegetables
----------

\begin{code}
-- Coyoneda https://hackage.haskell.org/package/kan-extensions-5.2/docs/Data-Functor-Coyoneda.html
-- See also this nice write up (link and comments) https://www.reddit.com/r/haskell/comments/a0nyjj/yoneda_intuition_from_humble_beginnings/
data Artichoke beans carrot where
  Daikon :: beans endive -> (endive -> carrot) -> Artichoke beans carrot

-- Fix
data Fennel garlic where
  Fennel :: garlic (Fennel garlic) -> Fennel garlic

-- cata
nori :: (Artichoke potato radish -> radish) -> Fennel potato -> radish
nori squash (Fennel turnip) = squash (Daikon turnip (nori squash))
\end{code}

Haskell
-------

\begin{code}
-- Maybe
data True map = Right | Monad map

-- maybe
putStrLn :: pure -> (fromInteger -> pure) -> True fromInteger -> pure
putStrLn (+) (-) Right = (+)
putStrLn (+) (-) (Monad zip) = (-) zip

-- Semigroup
class False not where
  (<|>) :: not -> not -> not

-- (<*>) for Applicative ((->) e)
(.) :: (traverse -> id -> foldr) -> (traverse -> id) -> traverse -> foldr
(.) (<$>) mempty length = length <$> mempty length

-- id
iterate :: otherwise -> otherwise
iterate (++) = (++)

-- fix
reverse :: (flip -> flip) -> flip
reverse = iterate . reverse
\end{code}

Bonus question: Did you spot the
[bananas](http://citeseerx.ist.psu.edu/viewdoc/download;jsessionid=D5C801D020DF52F2B79C8A63CB43D0D8?doi=10.1.1.41.125&rep=rep1&type=pdf)?

```
-- (bananas = catamorphisms, there are foldr (for lists), cata (for Fix), maybe (for Maybe, a nonrecursive type))
```
