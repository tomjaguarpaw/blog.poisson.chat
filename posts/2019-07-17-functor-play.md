---
title: Functor, Applicative, Monad, a play
keywords: [haskell, art]
---

A dialogue between context and focus, container and containee,
computation and value.

```haskell
context? focus!   ?!
context? _        ?
       _ focus!    !
```

= Functor

`Functor`'s `fmap` alters the focus, the context is unchanged.

```haskell
fmap alter (context focus) = context (alter focus)   ?!
fmap alter (context _    ) = context _               ?
fmap alter (      _ focus) =       _ (alter focus)    !
```

*The context asks.*

```haskell
fmap alter (context focus) = context (alter focus)   ?!
fmap alter (context _    ) = context _               ?
            context        = context                 ?
```

*The focus answers.*

```haskell
fmap alter (context focus) = context (alter focus)   ?!
fmap alter (      _ focus) =       _ (alter focus)    !
     alter          focus  =          alter focus     !
```

= Applicative

`Applicative`'s `(<*>)` combines foci and contexts simultaneously.

```haskell
context1 focus1 <*> context2 focus2 = (context1 <> context2) (focus1 focus2)   ?!
       _ focus1 <*>        _ focus2 =                      _ (focus1 focus2)    !
context1 _      <*> context2 _      = (context1 <> context2) _                 ?
```

The `(<>)` of semigroups and monoids is a metaphor.
Only a metaphor?

*Foci tell.*

```haskell
context1 focus1 <*> context2 focus2 = (context1 <> context2) (focus1 focus2)   ?!
       _ focus1 <*>        _ focus2 =                      _ (focus1 focus2)    !
         focus1              focus2 =                         focus1 focus2     !
```

*Contexts explain.*

```haskell
context1 focus1 <*> context2 focus2 = (context1 <> context2) (focus1 focus2)   ?!
context1 _      <*> context2 _      = (context1 <> context2) _                 ?
context1        < > context2        =  context1 <> context2                    ?
```

= Monad

`Monad`'s `join` nests contexts:

```haskell
join (context1 (context2 focus)) = (context1 . context2) focus   ?!
join (       _ (       _ focus)) =                     _ focus    !
join (context1 (context2 _    )) = (context1 . context2) _       ?
```

The `(.)` of functions is a metaphor.

[`(.)` makes a fine
`(<>)`](https://hackage.haskell.org/package/base-4.12.0.0/docs/Data-Semigroup.html#t:Endo):
every `Monad` is an `Applicative`.
Is `(.)` the only `(<>)`?

*A focused mind.*

```haskell
join (context1 (context2 focus)) = (context1 . context2) focus   ?!
join (       _ (       _ focus)) =                     _ focus    !
                         focus   =                       focus    !
```

*A contemplative context.*

```haskell
join (context1 (context2 focus)) = (context1 . context2) focus   ?!
join (context1 (context2 _    )) = (context1 . context2) _       ?
      context1 (context2 _    )  = (context1 . context2) _       ?
```

= Divide and conquer

```haskell
data Writer w a = Write w a

div <$> Write "no" 42 <*> Write "thing" 6 = Write "nothing" 9   ?!
div                42                   6 =                 9    !
              "no"    < >       "thing"   =       "nothing"     ?
```

= Order and chaos

```haskell
data Maybe b = Nothing | Just b

(>) <$> Just True <*> Just False = Just True   ?!
  _ <$> Just _    <*> Just _     = Just _      ?
        Just          Just       = Just        ?
        Just          Nothing    = Nothing     ?
  join (Just          Nothing)   = Nothing     ?!
```

= Everything and nothing

```haskell
(^) <$> (\x -> 0) <*> (\x -> x) = (\x -> 0 ^ x)   ?!
(^)            0             x  =        0 ^ x     !
        (\x ->  )     (\x ->  ) = (\x ->      )   ?
```
