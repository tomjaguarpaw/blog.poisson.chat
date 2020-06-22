#!/usr/bin/env python3

"""
Pandoc filter to pygmentize Coq code.
"""

import sys
from pandocfilters import toJSONFilter, RawBlock
from pygments import highlight
from pygments.lexers import (get_lexer_by_name, guess_lexer, TextLexer)
from pygments.formatters import get_formatter_by_name

def pygmentize(key, value, format, meta):
  if key == 'CodeBlock':
    [[ident, classes, keyvals], code] = value
    lexer = get_lexer_by_name('coq')
    if 'coq' in classes:
      return [RawBlock(format, highlight(code, lexer, get_formatter_by_name(format)))]

if __name__ == "__main__":
  toJSONFilter(pygmentize)
