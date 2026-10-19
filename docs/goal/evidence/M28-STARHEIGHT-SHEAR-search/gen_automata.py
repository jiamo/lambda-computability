#!/usr/bin/env python3
"""Print transitive automata on n points (letters identity or one cycle through 0, a canonical) as
"n a b c" lines for imtest_gen.c; star-free returns are checked afterwards on the hits only.
Usage: python3 gen_automata.py NMIN NMAX"""
import sys
from automata_search import automata
lo, hi = int(sys.argv[1]), int(sys.argv[2])
for n, lets in automata(hi):
    if n >= lo:
        print(n, *(''.join(map(str, l)) for l in lets))
