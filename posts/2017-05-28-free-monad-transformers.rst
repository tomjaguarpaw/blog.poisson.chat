---
title: Free monad transformers
---

This post explains categorically the free construction of *free monad
transformers* which can be found in the ``free`` `library on Hackage`__.

__ https://hackage.haskell.org/package/free

> {-# LANGUAGE DeriveFunctor #-}
> {-# LANGUAGE RankNTypes #-}
> {-# LANGUAGE ScopedTypeVariables #-}
> {-# LANGUAGE TypeApplications #-}
> {-# LANGUAGE TypeOperators #-}
>
> module Free.Monad.Trans where
>
> import Control.Monad

Monad transformers are represented by the following type class.
``lift`` is a monad morphism between ``m`` and ``t m``. ``monadTrans``
witnesses the fact that a monad transformer transforms monads into monads; it
is not as general as it could be, but we will not need any more power here.

> class MonadTrans t where
>   lift :: Monad m => m a -> t m a
>   monadTrans :: Monad m => (Monad (t m) => t m a) -> t m a

``FreeT`` is a functor
======================

> newtype FreeT f m a = FreeT { runFreeT :: m (FreeF f a (FreeT f m a)) }
>
> data FreeF f a b = Pure a | Free (f b)
>   deriving Functor

Instances are left in the appendix.

The ``FreeT`` type maps a functor ``f :: * -> *`` to a monad transformer
``FreeT f :: (* -> *) -> (* -> *)``, and that mapping should be functorial.
To define that functor, we must first spell out the categories defining the
domain and codomain.

This will make ``FreeT`` a functor between categories of functors, which
is the kind of remark that makes category theory notoriously confusing.

Domain and codomain
-------------------

The domain is the category of functors ``f :: * -> *`` and natural
transformations; the codomain is a category of monad transformers, but it may
seem unclear what its morphisms should be. We will try to describe the
categorical structures of the domain and codomain in parallel.

----

A functor ``f :: * -> *`` maps a type ``a :: *`` to a type ``f a :: *``.

A monad transformer ``t :: (* -> *) -> (* -> *)`` maps a monad
``m :: * -> *`` to a monad ``t m :: * -> *``.

----

Types form a category, where morphisms are functions.

Monads form a category, where morphisms are monad morphisms.

----

A natural transformation ``h :: f ~> g`` (a "functor morphism")
between two functors ``f, g :: * -> *`` maps a type ``a :: *``
to a function ``h @a :: f a -> g a``.

> type f ~> g = forall a. f a -> g a

A monad transformer morphism ``k :: t ~~> u`` between monad transformers
``t, u :: (* -> *) -> (* -> *)`` maps a monad ``m``,
to a monad morphism ``k @m :: forall a. t m a -> u m a``.

> type t ~~> u = forall m a. Monad m => t m a -> u m a

----

A natural transformation ``h`` commutes with the functorial mapping ``fmap``.

.. code::

  h @b . fmap @f = fmap @g . h @a

A monad transformer morphism ``k`` "commutes" with ``lift``.

.. code::

  k @m . lift @t = lift @u

----

Mapping morphisms
-----------------

To be a functor, ``FreeT`` should map natural transformations ``f ~> g``
to monad transformer morphisms ``FreeT f ~~> FreeT g``. This mapping is called
``transFreeT`` in the ``free`` library.

> -- Only one of (Functor f) or (Functor g) is actually necessary for the
> -- implementation.
> transFreeT :: forall f g. Functor g => (f ~> g) -> (FreeT f ~~> FreeT g)
> transFreeT h = FreeT . trans . runFreeT
>   where
>     trans :: forall m a. Monad m
>       => m (FreeF f a (FreeT f m a))
>       -> m (FreeF g a (FreeT g m a))
>     trans = fmap @m (fmap @(FreeF g a) (transFreeT h) . transFreeF h)
>
> transFreeF :: (f ~> g) -> (FreeF f a ~> FreeF g a)
> transFreeF _ (Pure a) = Pure a
> transFreeF h (Free f) = Free (h f)

And that mapping should preserve composition.

.. code::

  transFreeT id = id
  transFreeT (h . i) = transFreeT h . transFreeT i

Semi-proof
++++++++++

For example, the left hand side of the first equation reduces to:

.. code::

  transFreeT id = FreeT . fmap (transFreeT id) . runFreeT

And there's probably an argument (by induction?) to conclude from there.

``FreeT`` is a left adjoint
===========================

A `free functor`__ is a left adjoint to a forgetful functor.

__ https://ncatlab.org/nlab/show/free+functor

Here, ``FreeT`` maps a functor ``f`` to a monad transformer ``FreeT f``. A
corresponding "forgetful functor" should somehow map a monad transformer ``t``
to a functor ``Forget t``. Let us find a good functor.

If we use ``t`` to transform a well-chosen monad, then we get another monad,
which is also a functor, exactly what we're looking for. We shall choose the
identity monad, as it is the most "neutral" of them in some sense. This may be
abstractly motivated by the fact that it is the initial object in the category
of monads and monad morphisms. It is most straightforwardly represented as a
newtype:

> newtype Identity' a = Identity' a

But it will be a bit more convenient to use the following equivalent
representation:

> type Identity a = forall m. Monad m => m a

Then, the forgetful functor is obtained as:

> type Forget t a = forall m. Monad m => t m a

We shall use the definition of adjoint functors by Hom isomorphism: there
is a natural isomorphism between ``f ~> Forget t`` and ``FreeT f ~~> t``.
In particular, it consists of a bijection given by the following functions.

Imagine ``f`` as specifying *elements of syntax*. The first direction means
that if we can interpret these elements individually, then we can interpret an
AST as a whole. This is ``foldFreeT``.

> foldFreeT
>   :: (Functor f, MonadTrans t) => (f ~> Forget t) -> (FreeT f ~~> t)
> foldFreeT h = k
>   where
>     k (FreeT m) = monadTrans $ lift m >>= \v -> case v of
>       Pure a -> return a
>       Free f -> h f >>= k

The other direction seems less useful; it says that every monad transformer
morphism out of a free monad transformer can be decomposed as a ``foldTreeT``
of some natural transformation, which is equivalent to a straightforward
restriction of that morphism.

> restrict :: Functor f => (FreeT f ~~> t) -> (f ~> Forget t)
> restrict k = k . FreeT . return . Free . fmap return

The bijection we just gave is *natural*, making this diagram commute for all
``k :: FreeT f ~~> t``, ``i :: g ~> f`` and ``l :: t ~~> u``,


.. code::

  .                           restrict
              (FreeT f ~~> t)    ->    (f ~> Forget t)
                     |                        |
  dimap i (forget l) |                        | dimap (transFreeT i) l
                     v        restrict        v
              (FreeT g ~~> u)    ->    (g ~> Forget u)

  -- or as an equation --

  forget l . restrict k . i = restrict (l . k . transFreeT i)


where ``forget`` is the forgetful functorial mapping:

> forget :: (t ~~> u) -> (Forget t ~> Forget u)
> forget k = k

and ``dimap`` is a bifunctorial mapping:

> dimap :: (a -> b) -> (c -> d) -> (b -> c) -> (a -> d)
> dimap i l k = l . k . i

This was a fun exercise in category theory. After figuring it out, I was
surprised to see that ``foldFreeT`` was not in ``free``, but `now it is`__.

__ https://github.com/ekmett/free/pull/151

----

Appendix
========

> instance (Functor f, Monad m) => Functor (FreeT f m) where
>   fmap = liftM

> instance (Functor f, Monad m) => Applicative (FreeT f m) where
>   pure = return
>   (<*>) = ap

> instance (Functor f, Monad m) => Monad (FreeT f m) where
>   return = FreeT . return . Pure
>   FreeT m >>= f = FreeT $ m >>= \v -> case v of
>     Pure a -> runFreeT (f a)
>     Free w -> return (Free (fmap (>>= f) w))

> instance Functor f => MonadTrans (FreeT f) where
>   lift = FreeT . fmap Pure
>   monadTrans t = t
