Lysxia's blog
=============

https://blog.poisson.chat

---

# External dependencies

The blog uses the Python package pygments to highlight Coq code.

```
pip install --user pygments
```

# Build

```
stack build
stack exec lysxia -- build
# Find your HTML in _site/
```

# Load a Literate Haskell post

```
# Use -x to override the extension.
stack exec ghci -- -x lhs posts/2018-12-09-naming-abstraction.md
```

---

# License information

This repository includes a modified version of `haskell.xml` from KDE's
*syntax-highlighting*, licensed under LGPL 2.1 (see `haskell.xml.COPYING.LIB`).
Modifications of general interest will be upstreamed.
