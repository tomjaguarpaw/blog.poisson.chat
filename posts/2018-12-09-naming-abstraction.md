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

([Here's a gist](https://gist.github.com/Lysxia/b9863a7334d4b05bf4427caca5b85f20)
of the Literal Haskell source of this post.)

Fruits
------

\begin{code}
apple :: banana -> (banana -> cherry) -> cherry
apple date fig = fig date

grapes :: (kiwi -> kiwi) -> (kiwi -> kiwi) -> kiwi
grapes lemon mango = lemon (grapes mango lemon)

nutmeg :: plum -> olive -> plum
nutmeg raspberry strawberry = raspberry
\end{code}

Animals
-------

\begin{code}
albatross :: (beluga -> beluga) -> Cat beluga -> Cat beluga
albatross dolphin Elephant = Elephant
albatross dolphin (Frog giraffe hedgehog) =
  albatross dolphin giraffe `Frog` dolphin hedgehog

data Cat iguana = Elephant | Frog (Cat iguana) iguana

jaguar :: kangaroo -> kangaroo
jaguar = jaguar jaguar

data Lion nyala = Mackerel nyala (Cat (Lion nyala))

opossum :: penguin -> (penguin -> quail -> penguin) -> Cat quail -> penguin
opossum rooster snail Elephant = rooster
opossum rooster snail (Frog tiger unicorn) =
  opossum rooster snail tiger `snail` unicorn

class Vulture wallaby where
  fox :: (yeti -> zebra) -> wallaby yeti -> wallaby zebra
\end{code}

Animals: déjà vu
----------------

\begin{code}
alpaca :: (beluga -> beluga) -> Cat beluga -> Cat beluga
alpaca dolphin Elephant = Elephant
alpaca dolphin (Frog giraffe hedgehog) =
  alpaca dolphin giraffe

class Vultures wallaby where
  lynx :: (yeti -> wallaby zebra) -> wallaby yeti -> wallaby zebra
\end{code}

Vegetables
----------

\begin{code}
data Artichoke beans carrot where
  Daikon :: beans endive -> (endive -> carrot) -> Artichoke beans carrot

data Fennel garlic where
  Fennel :: garlic (Fennel garlic) -> Fennel garlic

nori :: (Artichoke potato radish -> radish) -> Fennel potato -> radish
nori squash (Fennel turnip) = squash (Daikon turnip (nori squash))
\end{code}

Haskell
-------

\begin{code}
data True map = Right | Monad map

putStrLn :: pure -> (fromInteger -> pure) -> True fromInteger -> pure
putStrLn (+) (-) Right = (+)
putStrLn (+) (-) (Monad zip) = (-) zip

class False not where
  (<|>) :: not -> not -> not

(.) :: (traverse -> id -> foldr) -> (traverse -> id) -> traverse -> foldr
(.) (<$>) mempty length = length <$> mempty length

iterate :: otherwise -> otherwise
iterate (++) = (++)

reverse :: (flip -> flip) -> flip
reverse = iterate . reverse
\end{code}

Bonus question: Did you spot the
[bananas](http://citeseerx.ist.psu.edu/viewdoc/download;jsessionid=D5C801D020DF52F2B79C8A63CB43D0D8?doi=10.1.1.41.125&rep=rep1&type=pdf)?
