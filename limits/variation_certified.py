# Written by Kristian Muri Knausgård <kristianmk@ieee.org>.
# AI assistance: this file was drafted with Claude (Anthropic), an AI system, under the direction
# of the author, who is responsible for its content.
"""Certified upper bounds for V(f) = f(1/2)^2 + int_0^1 |R''(u)| du, R = f*f (ball arithmetic).

For f(t) = sum_k c_k cos(w_k t) on [-1/2, 1/2] and 0 <= u <= 1,
  R(u)   = int_{u-1/2}^{1/2} f(t) f(u - t) dt,
  R''(u) = -f'(u - 1/2) f(1/2) - f(u - 1/2) f'(1/2) + int_{u-1/2}^{1/2} f(t) f''(u - t) dt,
and the last integral is elementary.  [0, 1] is cut into n cells; on each cell R'' is evaluated on
the ball covering the cell, and |R''| is bounded by the upper end of the result.
"""
import sys
from flint import arb, ctx
from ceiling_certified import window
ctx.prec = 100

def make(name):
    w, c = window(name)
    half = arb(1) / 2
    f = lambda t: sum((ck * (wk * t).cos() for wk, ck in zip(w, c)), arb(0))
    f1 = lambda t: sum((-ck * wk * (wk * t).sin() for wk, ck in zip(w, c)), arb(0))
    def sinc_int(Om, ph, lo, hi, zero):
        """int_lo^hi cos(Om t + ph) dt, valid for balls lo, hi, ph; `zero` says that Om = 0"""
        if zero:
            return (hi - lo) * ph.cos()
        return ((Om * hi + ph).sin() - (Om * lo + ph).sin()) / Om
    def R2(u):
        lo = u - half; hi = half
        tot = -f1(lo) * f(half) - f(lo) * f1(half)
        for k, (wk, ck) in enumerate(zip(w, c)):
            for l, (wl, cl) in enumerate(zip(w, c)):
                # f(t) f''(u-t) contains  -c_k c_l w_l^2 cos(w_k t) cos(w_l (u - t))
                coef = -ck * cl * wl * wl / 2
                tot += coef * sinc_int(wk - wl, wl * u, lo, hi, k == l)
                tot += coef * sinc_int(wk + wl, -wl * u, lo, hi, bool(wk == 0) and bool(wl == 0))
        return tot
    return f, R2

def bound(name, n=20000):
    f, R2 = make(name)
    tot = arb(0)
    for i in range(n):
        u = (arb(i) / n).union(arb(i + 1) / n)
        v = R2(u)
        tot += v.abs_upper() / n
    e2 = f(arb(1) / 2) ** 2
    return e2, tot

from ceiling_certified import Win
from fractions import Fraction
print("flat    V(f) = 1, B(f) = 1/3, V/B = 3   (f = 1: R(u) = 1 - u on [0, 1])")
for name in ('mt', 'paper1', 'new', 'line'):
    e2, tv = bound(name)
    V = e2 + tv
    w = Win(name)
    B = w.C - w.R(Fraction(0))          # B(f) = C(f) - int f^2
    print(f"{name:7s} f(1/2)^2 = {e2.str(10)}   int|R''| <= {tv.str(10)}   V(f) <= {float(V.upper()):.6f}"
          f"   B(f) = {B.str(10)}   V/B <= {float((V / B).upper()):.4f}")
