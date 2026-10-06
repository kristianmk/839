# Written by Kristian Muri Knausgård <kristianmk@ieee.org>.
# AI assistance: this file was drafted with Claude (Anthropic), an AI system, under the direction
# of the author, who is responsible for its content.
"""Certified ceilings for the labelled Gram method (ball arithmetic, python-flint).

For a window f on [-1/2, 1/2] the method uses only  tr A = N  and  tr A^2 <= (C(f) + o(1)) N.
A labelled configuration on the line (labels 1, 2) with N units of multiplicity in length N and
energy  sum_{i,j} d_i d_j K(y_i - y_j)^2 <= C(f) N  is consistent with both, so the method cannot
prove more than its proportion of distinct points.  This script takes periodic trial states
(labels, rational gaps), computes their period energies rigorously by Poisson summation
(K^2 is the Fourier transform of R = f*f, supported in [-1, 1]), and certifies a mixture:

    states k with  N_k = n1 + 2 n2,  D_k = n1 + n2,  P_k = period,  E_k = n1 + 4 n2 + pair energy,
    rational weights w_k >= 0 with   sum w_k P_k <= sum w_k N_k   and   sum w_k E_k <= C sum w_k N_k
    =>  Q*(f) <= sum w_k D_k / sum w_k N_k .

Interfaces between the phases of a mixture cost O(1) each and vanish in the limit.

With a range s > 0 (third argument) the energies count only pairs at index distance at most s.
This tests certificates that, like a local inequality for s + 1 consecutive points, use only those
pairs: such a certificate is a valid triple for the range-s energy, and the same mixture argument
applies with the range-s energy in place of the full one (C(f) is unchanged).

usage: ceiling_certified.py window binding.json [range]
"""
import sys, json
from fractions import Fraction
import numpy as np
from scipy.optimize import linprog
from flint import arb, acb, fmpq, ctx

ctx.prec = 300
PI = arb.pi()


def to_arb(q):
    q = Fraction(q)
    return arb(fmpq(q.numerator, q.denominator))


def window(name):
    """frequencies and coefficients (arb) of v(u) = sum c_k cos(w_k u); f = v / int v"""
    a_new = [Fraction(v, 10**6) for v in (193305, -23105, 29166, 13952, -21009, 41052)]
    kap = [Fraction(v, 10**9) for v in (3322500, -7609135, 1190194, -731476, -1680572, 1141360)]
    harm = [2 * PI * j for j in range(1, 7)]
    a_line = [Fraction(v, 10**6) for v in (122290, -45012, 16241, 1887, 2711, 3731, -5307, 2982, -5153, 5358)]
    if name == 'new':
        w = [arb(0)] + harm; c = [arb(1)] + [to_arb(x) for x in a_new]
    elif name == 'line':
        w = [arb(0)] + [2 * PI * j for j in range(1, len(a_line) + 1)]; c = [arb(1)] + [to_arb(x) for x in a_line]
    elif name == 'mt':
        w = [arb(2).sqrt()]; c = [arb(1)]
    elif name == 'paper1':
        w = [arb(2).sqrt()] + harm; c = [arb(1)] + [to_arb(x) for x in kap]
    else:
        raise SystemExit('unknown window')
    integ = arb(0)
    for wk, ck in zip(w, c):
        integ += ck if wk == 0 else ck * 2 * (wk / 2).sin() / wk
    return w, [ck / integ for ck in c]


class Win:
    def __init__(self, name):
        self.w, self.c = window(name)
        n = len(self.w)
        # C(f) = int f^2 + 2 int F (1 - F),  F the primitive of f; rigorous integration
        def f(x):
            return sum((acb(ck) * (acb(wk) * x).cos() for wk, ck in zip(self.w, self.c)), acb(0))
        def F(x):
            tot = acb(0)
            for wk, ck in zip(self.w, self.c):
                if wk == 0:
                    tot += acb(ck) * (x + acb(1) / 2)
                else:
                    tot += acb(ck) * ((acb(wk) * x).sin() + (acb(wk) / 2).sin()) / acb(wk)
            return tot
        half = acb(1) / 2
        I1 = acb.integral(lambda x, _: f(x) * f(x), -half, half)
        I2 = acb.integral(lambda x, _: F(x) * (1 - F(x)), -half, half)
        self.C = (I1 + 2 * I2).real

    def R(self, u):
        """(f*f)(u), u rational in [0, 1]"""
        u = Fraction(u)
        if u >= 1:
            return arb(0)
        ua = to_arb(u); lo = ua - arb(1) / 2; hi = arb(1) / 2
        tot = arb(0)
        for k, (wk, ck) in enumerate(zip(self.w, self.c)):
            for l, (wl, cl) in enumerate(zip(self.w, self.c)):
                # cos(wk t) cos(wl (u - t)) = (cos((wk - wl) t + wl u) + cos((wk + wl) t - wl u)) / 2
                for Om, ph, zero in ((wk - wl, wl * ua, k == l), (wk + wl, -wl * ua, wk == 0 and wl == 0)):
                    if zero:
                        val = (hi - lo) * ph.cos()
                    else:
                        val = ((Om * hi + ph).sin() - (Om * lo + ph).sin()) / Om
                    tot += ck * cl * val / 2
        return tot

    def K(self, t):
        """K(t) = f^(t) for rational t: sum_k c_k (sinc-type terms), sinc(x) = sin(x)/x"""
        ta = to_arb(t)
        tot = arb(0)
        for wk, ck in zip(self.w, self.c):
            for sgn in (1, -1):
                z = (wk + sgn * 2 * PI * ta) / 2
                val = z.sinc()            # sin(z)/z, valid also for balls containing 0
                tot += ck * val / 2
        return tot

    def period_energy_range(self, labs, gaps, s):
        """n1 + 4 n2 + pair energy per period, pairs at index distance <= s only"""
        p = len(labs); tot = arb(sum(d * d for d in labs))
        for i in range(p):
            dist = Fraction(0)
            for r in range(1, s + 1):
                dist += gaps[(i + r - 1) % p]
                tot += 2 * labs[i] * labs[(i + r) % p] * self.K(dist) ** 2
        return tot

    def period_energy(self, labs, gaps):
        """n1 + 4 n2 + pair energy per period; gaps rational with integer sum P"""
        P = sum(gaps); assert P.denominator == 1; P = int(P)
        pos = [sum(gaps[:i], Fraction(0)) for i in range(len(gaps))]
        tot = self.R(0) * arb(sum(labs)) ** 2
        for m in range(1, P + 1):
            re = sum((arb(d) * (2 * PI * m * to_arb(y) / P).cos() for y, d in zip(pos, labs)), arb(0))
            im = sum((arb(d) * (2 * PI * m * to_arb(y) / P).sin() for y, d in zip(pos, labs)), arb(0))
            tot += 2 * self.R(Fraction(m, P)) * (re * re + im * im)
        return tot / P


def main():
    name = sys.argv[1]; data = json.load(open(sys.argv[2]))
    rng = int(sys.argv[3]) if len(sys.argv) > 3 else 0
    win = Win(name)
    print('window', name, ' C(f) =', win.C.str(20))
    states = []
    seen = set()
    for st in data['binding']:
        labs = st['labels']; g = st['gaps']
        if rng == 0:
            P = round(sum(g))
            gq = [Fraction(round(v * 10**5), 10**5) for v in g[:-1]]
            gq.append(Fraction(P) - sum(gq))        # the Poisson formula needs an integer period
        else:
            gq = [Fraction(round(v * 10**5), 10**5) for v in g]
            P = sum(gq)
        key = (tuple(labs), tuple(gq))
        if key in seen or min(gq) <= 0:
            continue
        seen.add(key)
        if rng and min(gq) < Fraction(17, 20):
            continue                      # range-s certificates are only required on separated sets
        E = win.period_energy(labs, gq) if rng == 0 else win.period_energy_range(labs, gq, rng)
        n1 = sum(1 for a in labs if a == 1); n2 = len(labs) - n1
        states.append(dict(labs=labs, gaps=gq, N=n1 + 2 * n2, D=n1 + n2, P=P, E=E))
        print('  state', labs, [str(x) for x in gq], ' N', n1 + 2 * n2, 'P', P, ' E =', E.str(15))
    # float LP for the weights: minimise sum w D  s.t. sum w N = 1, sum w P <= 1, sum w E <= C - margin
    Cf = float(win.C.mid()); margin = 1e-9
    res = linprog(c=[s['D'] for s in states],
                  A_ub=[[float(s['P']) for s in states], [float(s['E'].mid()) for s in states]],
                  b_ub=[1 - margin, Cf - margin], A_eq=[[s['N'] for s in states]], b_eq=[1.0],
                  bounds=[(0, None)] * len(states), method='highs')
    assert res.status == 0
    w = [Fraction(max(v, 0.0)).limit_denominator(10**9) for v in res.x]
    P_of = lambda s: Fraction(s['P'])
    Nt = sum(wk * s['N'] for wk, s in zip(w, states))
    Pt = sum(wk * s['P'] for wk, s in zip(w, states))
    Dt = sum(wk * s['D'] for wk, s in zip(w, states))
    Et = sum((to_arb(wk) * s['E'] for wk, s in zip(w, states)), arb(0))
    ok_span = Pt <= Nt
    ok_energy = bool(Et < win.C * to_arb(Nt))
    Q = Dt / Nt
    print('weights', [str(x) for x in w])
    print('span <= N:', ok_span, '  energy <= C N (certified):', ok_energy)
    print('energy per unit of multiplicity:', (Et / to_arb(Nt)).str(15))
    tag = name if rng == 0 else f'{name} range {rng}'
    print(f'CERTIFIED CEILING {tag}: Q <= {Q} = {float(Q):.9f}' if ok_span and ok_energy else 'NOT CERTIFIED')


if __name__ == '__main__':
    main()
