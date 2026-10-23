#!/usr/bin/env python3
"""Exact evaluation of the majorant E(r) of Section 5 of the paper "A lower bound for the Bohr radius of the bidisc".

usage: python3 -I check_majorant.py R ALPHA BETA GAMMA [n=s_n ...]     (exact rationals, e.g. 301633/1000000)

E(r) = 2 r + r^2 B(r) + 2 sum_{n=4}^{40} s_n r^n + 2 r^41 (41 - 40 r)/(1 - r)^2, where
B(r) = 4 alpha + 176 beta + 2 gamma + 1/(4 alpha) + 1/(4 (alpha + gamma/2)) + (r - gamma)^2/(140 beta) + r^2/(112 beta)
is the function of Lemma 3.6. The numbers s_n are upper bounds for the Sidon constants S({0, ..., n}): s_4 = 2, s_n as
given on the command line for the listed n, and s_n = ceil(10^8 sqrt n)/10^8 otherwise (q^2 >= 10^16 n is checked). The
last term equals 2 sum_{n>40} n r^n, which bounds the tail because S({0, ..., n}) <= sqrt n <= n. Everything is computed
with Python fractions. The program prints B(r) and E(r) truncated to 20 decimals, an upper bound for E(r) with 8
decimals, and PASS if and only if E(r) < 1. It refuses to run under python -O."""
import sys, math
from fractions import Fraction as F
if sys.flags.optimize:
    sys.exit('refusing to run with python -O')
r, a, b, g = (F(x) for x in sys.argv[1:5])
over = {int(t.split('=')[0]): F(t.split('=')[1]) for t in sys.argv[5:]}
if not (a > 0 and b > 0 and g > 0 and 0 < r < 1):
    sys.exit('bad parameters')
B = 4 * a + 176 * b + 2 * g + 1 / (4 * a) + 1 / (4 * (a + g / 2)) + (r - g) ** 2 / (140 * b) + r ** 2 / (112 * b)
tail = F(0)
for n in range(4, 41):
    if n in over:
        s = over[n]
    elif n == 4:
        s = F(2)
    else:
        q = math.isqrt(10 ** 16 * n)
        if q * q < 10 ** 16 * n:
            q += 1
        if not (q * q >= 10 ** 16 * n):
            sys.exit('sqrt bound failed')
        s = F(q, 10 ** 8)
    tail += 2 * s * r ** n
tail += 2 * r ** 41 * (41 - 40 * r) / (1 - r) ** 2
E = 2 * r + r * r * B + tail
def trunc(x, nd):            # decimal string of x truncated (towards zero) to nd places, exact
    sgn = '-' if x < 0 else ''
    x = abs(x); q = (x.numerator * 10 ** nd) // x.denominator
    return f"{sgn}{q // 10 ** nd}.{str(q % 10 ** nd).zfill(nd)}"
def ceil_dec(x, nd):         # smallest nd-decimal number >= x (x > 0), exact
    q = -((-x.numerator * 10 ** nd) // x.denominator)
    return f"{q // 10 ** nd}.{str(q % 10 ** nd).zfill(nd)}"
print(f'r* = {r} = {float(r):.10f}')
print(f'B(r*) = {trunc(B, 20)}... (truncated)')
print(f'E(r*) = {trunc(E, 20)}... (truncated to 20 decimals);  E(r*) <= {ceil_dec(E, 8)} (rounded up)')
print('PASS: E(r*) < 1, hence K_2 >= r*' if E < 1 else 'FAIL: E(r*) >= 1')
