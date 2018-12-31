---
title: Surgery for data types
---

In this post I will show an example of *data type surgery*. Surgeries are
operations to change a data type by bits and pieces: modify its fields and
constructors, you get another type.

A couple of simple surgeries using `GHC.Generics` can be found in my freshly
released Haskell library:
[generic-data-surgery](https://hackage.haskell.org/package/generic-data-surgery).
Suggestions for more surgeries are welcome on [the issue
tracker](https://github.com/Lysxia/generic-data-surgery/issues).

The general motivation is to improve the applicability of various
generic[^generic] definitions, such as aeson's generic instances for `ToJSON`
and `FromJSON`.
Such a library often offers several options to customize the generic
implementations, but it can still happen that none of them quite fit your
external requirements and you have to resort to manual implementations, even
with only small mismatches with the generic implementations.
Surgeries are a new way to adapt generic implementations to such conditions
outside of your control.

[^generic]: by "generic" I mean both `GHC.Generics`, which is what the rest of the
  post will be using, and the more general idea of "data-type generic
  programming" for which `GHC.Generics` is one approach among many, alongside
  "Scrap your boilerplate" and Template Haskell (in some respects).

A toy example
=============

Consider the task of deserializing a simple record from JSON:

```haskell
data Rec = Rec
  { iden    :: Int
  , header1 :: Int
  , header2 :: Int
  , payload :: String
  } deriving (Eq, Generic, Show)
```

The JSON we want to parse will follow the same structure (an object with keys
`"iden"`, `"header1"`, `"header2"`, `"payload"`), but the `"payload"` key may
also be missing from the JSON object, and that should be interpreted as an
empty payload (`payload = ""`). Two examples of well-formed objects:

```
{"iden":1,"header1":2,"header2":3}
{"iden":1,"header1":2,"header2":3,"payload":"Hello"}
```

The aeson library's generic implementation of `parseJSON` is close to doing the
right thing, except for that extra requirement about the missing `"payload"`
key. Is this an all-or-nothing situation, where you would give up entirely the
existing automation for the smallest of issues?

Solution 1: a parameterized type
================================

There is a simple solution that doesn't require anything as fancy as surgeries.

aeson can handle missing keys in one specific case[^aeson-maybe]: with the
option `omitNothingFields=True`, missing keys corresponding to fields of type
`Maybe Something` will be parsed as `Nothing`. So if we change the
type of the field `payload` from `String` to `Maybe String`...

[^aeson-maybe]: Arguably *too* specific.

```haskell
data Rec' = Rec'
  { iden    :: Int
  , header1 :: Int
  , header2 :: Int
  , payload :: Maybe String
  } deriving (Eq, Generic, Show)
```

... then aeson's generic parser can accept a missing `payload`.

```haskell
instance FromJSON Rec' where
  parseJSON = genericParseJSON defaultOptions{omitNothingFields=True}
```

But of course that breaks any existing function that uses `payload` as a plain
`String`. To avoid that, we can generalize over the difference between `Rec` and
`Rec'` with a parameterized type:

```haskell
data Rec_ string = Rec
  { iden    :: Int
  , header1 :: Int
  , header2 :: Int
  , payload :: string
  } deriving (Eq, Functor, Generic, Show)

type Rec  = Rec_ String
type Rec' = Rec_ (Maybe String)
```

We get a `Functor` instance for free (thanks to the `DeriveFunctor` extension)
to transform the payload.

Now we can use `genericParseJSON` to first parse a `Rec_ (Maybe String)`, and
use `fmap` to massage it into a proper `Rec`.

```haskell
instance FromJSON Rec where
  parseJSON :: Value -> Parser Rec
  parseJSON = (fmap . fmap) defString
            . genericParseJSON defaultOptions{omitNothingFields=True}

-- Helper function to turn a missing string into the empty string.
defString :: Maybe String -> String
defString Nothing  = ""
defString (Just s) = s
```

Here is a little diagram detailing the intermediate types in the definition of
`parseJSON`:

```
--                            Value
-- genericParseJSON opts      ->
--                            Parser (Rec_ (Maybe String)))
-- (fmap . fmap) defString    ->
--                            Parser (Rec_ String)
--                          = Parser Rec
```

This is a nice solution, but still less than ideal. Mangling our type may make
compilation errors in unrelated places harder to understand, and it may even
introduce new ambiguity errors.
These global costs might not be worth a benefit as local as automating the
implementation of a serializer.

Thus, we would like both:

- to keep the original simple `Rec` type, where `payload` has type `String`;
- to use `genericParseJSON` with a different record type like `Rec'` where
  `payload` has type `Maybe String`.

And let's keep it [DRY](https://en.wikipedia.org/wiki/Don't_repeat_yourself):
that second record type must somehow be derived from `Rec`, rather than
redeclared explicitly.

Solution 2: type surgery
========================

Conceptually, we're looking for a very simple operation: change the type of the
`payload` field. So the code should look just as simple on the surface
(or at least, not much more complicated than the previous solution):

```haskell
instance FromJSON Rec where
  parseJSON :: Value -> Parser Rec
  parseJSON
    = fmap (fromOR . modifyRField @"payload" defString . toOR')
    . genericParseJSON defaultOptions{omitNothingFields=True}

-- Defined previously
defString :: Maybe String -> String
```

The *surgery* `modifyRField @"payload" defString` is a function that takes some
record with a field `payload` of type `Maybe String` and applies `defString` to
that field, producing a new record where `payload` has type `String` instead.
Actually, surgeries don't operate directly on records; these need to be
converted to a generic representation via `fromOR` and `toOR'`.

Here is another little diagram of what the types look like in the argument of
`fmap` above. The record types are "expanded" to illustrate what is going on
informally.
The runtime data flows top-down, but the "surgery" on types might be more
easily read bottom-up:

```
                    { ..., payload :: Maybe String }  (a synthetic type)
toOR'            ->
                 OR { ..., payload :: Maybe String }
modifyRField     ->
                 OR { ..., payload :: String }
fromOR           ->
                    { ..., payload :: String }     (Rec, a natural type)
```

On the bottom end, we know a `Rec` must be getting out (from the expected type
of `parseJSON`).
Moving up in the diagram, `fromOR` puts the record type in an "operating room"
(`OR`) (that's the metaphor; concretely this is a mapping between a type and a
generic representation like `GHC.Generics.Rep`).
Inside the operating room, we can apply the surgery `modifyRField` to change
the type of the `payload` field.
At the top of the diagram, going into `toOR'` is a *synthetic* record type,
call it `SRec`, created by the surgery, and for which there is no `data`
declaration,[^well] as opposed to a *natural* type like `Rec`.

[^well]: Of course, you'll find some "naturally declared" types if you look at
  the definition of the synthetic type, but those are really implementation
  details. Make abstraction of them, and look at that synthetic type as a type
  with a similar structure to `Rec`.

If that may seem magical, all you need to know is that this synthetic type
`SRec` has the same generic representation as the previous altered `Rec'` type
where `payload` is given type `Maybe String` (`Rep SRec = Rep Rec'`), and that
is also all `genericParseJSON` needs to see to do its thing.
No type annotations are necessary: the *synthetic generic type* that comes out
of `genericParseJSON` and goes into `toOR'` can be inferred from the fact that
the original `Rec` type is expected on the other end of the operating room.

Closing notes
=============

- generic-data-surgery is still very much in the proof-of-concept stage, but
  any issue encountered while trying to use it would help move the project
  forward.
  I haven't looked at performance; compile times are expected to be abysmal,
  but at run time there should be no overhead with proper inlining.
  Error messages are another aspect to improve: a typical error currently prints
  an unfolded `Rep` spanning a hundred lines with stuck type families.
  If you are interested in these matters, whatever your level of expertise,
  please get in touch (e.g., via GitHub or via e-mail)! I would be happy to
  help you navigate in the code.

- I can hear mumbles about row polymorphism, extensible types, etc. Indeed,
  generic-data-surgery contains pretty much yet another record library, but
  only means to use it as an intermediate representation with which to
  instantiate various generic implementations such as `genericParseJSON` above.
  In particular, it carefully preserves the type metadata found in the `M1`
  constructor of `GHC.Generics`. A better story for row polymorphism in Haskell
  may very well overtake this library.

- Modifying the contents of fields is also a good fit for lenses, and in fact
  the `modifyRField` surgery presented here can be implemented as a
  "type-changing lens" from generic-lens (to be released with
  generic-lens-1.1.0.0) plus a unification constraint on the type metadata
  carried by `GHC.Generics.M1`.[^glens]
  Other surgeries that add or remove fields and constructors seem less easy to
  express that way though.

- I got [the idea of
  first-class-families](http://blog.poisson.chat/posts/2018-08-06-one-type-family.html)
  while doing type-level acrobatics in generic-data-surgery.

- A compilable version of this example can be found [in the library
  repository](https://github.com/Lysxia/generic-data-surgery/blob/master/examples/example-aeson.hs).

[^glens]: *EDIT* 2018-12-31: generic-data now has [a bit of
  documentation](https://hackage.haskell.org/package/generic-data-0.4.0.0/docs/Generic-Data-Microsurgery.html#g:1)
  about using generic-lens for surgeries.
