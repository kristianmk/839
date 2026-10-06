# Written by Kristian Muri Knausgård <kristianmk@ieee.org>.
# AI assistance: this file was drafted with Claude (Anthropic), an AI system, under the direction
# of the author, who is responsible for its content.
"""Data for the figure of the article: the windows and their kernels K^2 (floating point).

Writes the two data files next to the article source: the first window (new), the
Montgomery-Taylor window (mt) and the second window (line, of the section on the critical line).
"""
import sys
import numpy as np
sys.argv = ['x']
from ground_state import Win
new, mt = Win('new'), Win('mt')
A_LINE = np.array([122290, -45012, 16241, 1887, 2711, 3731, -5307, 2982, -5153, 5358]) / 1e6
J = np.arange(1, len(A_LINE) + 1)


def f_line(x):
    return 1 + float(np.sum(A_LINE * np.cos(2 * np.pi * J * x)))


def K_line(t):
    return float(np.sinc(t) + np.sum(0.5 * A_LINE * (np.sinc(t - J) + np.sinc(t + J))))


OUT = '../../ams/'
u = np.linspace(-0.5, 0.5, 201)
with open(OUT + 'knausgard839win.dat', 'w') as fh:
    fh.write('u fnew fmt fline\n')
    for x in u:
        fh.write(f'{x:.4f} {new.f(x):.6f} {mt.f(x):.6f} {f_line(x):.6f}\n')
t = np.linspace(0, 7.5, 601)
with open(OUT + 'knausgard839ker.dat', 'w') as fh:
    fh.write('t knew kmt kline\n')
    for x in t:
        fh.write(f'{x:.4f} {float(new.K(x))**2:.6e} {float(mt.K(x))**2:.6e} {K_line(x)**2:.6e}\n')
print('lattice energies', 2 * sum(float(new.K(n))**2 for n in range(1, 40)), 2 * sum(float(mt.K(n))**2 for n in range(1, 40)),
      2 * sum(K_line(n)**2 for n in range(1, 40)))
