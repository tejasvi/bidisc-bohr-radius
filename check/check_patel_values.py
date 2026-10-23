#!/usr/bin/env python3
"""Exact check of the numbers displayed in S. Patel's lower-bound computation (MathDB problem 392062, solution
"Improved lower and upper bounds for the bidisc Bohr radius", section "The exact numerical inequality").

With r = 15079379/50000000, alpha = 264631/800000, beta = 249627/10^8, gamma = 10197021/10^8, the program checks in
exact rational arithmetic that
  1. B(r) equals the displayed fraction, where
     B(r) = 4 alpha + 176 beta + 2 gamma + 1/(4 alpha) + 1/(4 (alpha + gamma/2)) + (r - gamma)^2/(140 beta) + r^2/(112 beta);
  2. the displayed integers q_n (4 <= n <= 20) are the ceilings of 10^8 sqrt(n);
  3. 2r + r^2 B(r) is below the first displayed bound;
  4. (2/10^8) sum_{n=4}^{20} q_n r^n + 2 r^21 (21 - 20 r)/(1 - r)^2 is below the second displayed bound;
  5. the sum of the two displayed bounds is the displayed total, and the total is below 1 - 1/50000000.
It prints the exact value of the majorant to 20 digits.  usage: python3 -I check_patel_values.py"""
import math
import sys
from fractions import Fraction as F

if sys.flags.optimize:
    sys.exit("refusing to run with python -O")

r = F(15079379, 50000000)
alpha, beta, gamma = F(264631, 800000), F(249627, 10**8), F(10197021, 10**8)
B_POSTED = F(44915682119816917151345293949, 11769153837063865963000000000)
Q_POSTED = {4: 200000000, 5: 223606798, 6: 244948975, 7: 264575132, 8: 282842713, 9: 300000000, 10: 316227767,
            11: 331662480, 12: 346410162, 13: 360555128, 14: 374165739, 15: 387298335, 16: 400000000,
            17: 412310563, 18: 424264069, 19: 435889895, 20: 447213596}
BOUND1, BOUND2, TOTAL = F(950295182089920172, 10**18), F(49704796478844948, 10**18), F(999999978568765120, 10**18)

ok = True


def check(name, cond):
    global ok
    print(("OK    " if cond else "FAIL  ") + name)
    ok = ok and bool(cond)


B = (4 * alpha + 176 * beta + 2 * gamma + 1 / (4 * alpha) + 1 / (4 * (alpha + gamma / 2))
     + (r - gamma) ** 2 / (140 * beta) + r ** 2 / (112 * beta))
check("1. B(r) equals the displayed fraction", B == B_POSTED)
ceil = {n: math.isqrt(10**16 * n) + (math.isqrt(10**16 * n) ** 2 < 10**16 * n) for n in range(4, 21)}
check("2. q_n = ceil(10^8 sqrt n) for 4 <= n <= 20", all(Q_POSTED[n] == ceil[n] for n in range(4, 21)))
part1 = 2 * r + r * r * B
part2 = F(2, 10**8) * sum(Q_POSTED[n] * r ** n for n in range(4, 21)) + 2 * r ** 21 * (21 - 20 * r) / (1 - r) ** 2
check("3. 2r + r^2 B(r) < first displayed bound", part1 < BOUND1)
check("4. remaining sum + tail < second displayed bound", part2 < BOUND2)
check("5. bound1 + bound2 = displayed total < 1 - 1/50000000", BOUND1 + BOUND2 == TOTAL and TOTAL < 1 - F(1, 50000000))
E = part1 + part2
digits = E.numerator * 10**20 // E.denominator          # E < 1, so these are the first 20 decimals
print("majorant at r: 0." + str(digits).rjust(20, "0") + "... (truncated)")
print("ALL CHECKS OK" if ok else "SOME CHECK FAILED")
sys.exit(0 if ok else 1)
