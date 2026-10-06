#!/usr/bin/env python3
# Written by Kristian Muri Knausgård <kristianmk@ieee.org>.
# AI assistance: this file was drafted with Claude (Anthropic), an AI system, under the direction
# of the author, who is responsible for its content.
"""Writes the parameter file of verify.cpp from the frozen data of a certificate.

    python3 make_parameters.py ../certificate/inputs.json first_window.txt

The integers are copied from inputs.json without change. Three numbers are not stored there and
are fixed by the form of the certificates of the paper: the smallest gap is the separation theta
in grid steps, rounded down (a larger set of frames is then verified), and the functions B_r have
fourteen knots at 0.75, 0.875, ..., 2.375, that is from 3/4 of a unit in steps of 1/8 of a unit.
The number of points of a frame is the entry "points" of inputs.json (seven if there is none);
the parameter file is for the verifier built for that number (verify for seven points, verify8
for eight). The conditions on the data are checked by verify.cpp, not here."""
import json
import sys
from fractions import Fraction

TYPE_COUNT, KNOT_COUNT = 3, 14


def point_count(data):
    """the number of points of a frame: seven, unless the data say otherwise"""
    points = data.get('points', 7)
    if isinstance(points, bool) or not isinstance(points, int) or not 3 <= points <= 10:
        raise ValueError('points: expected an integer from 3 to 10')
    return points


def parameter_text(data):
    grid = int(data['grid'])
    if grid % 8 != 0:
        raise ValueError('the grid must be divisible by 8 (knots at multiples of 1/8)')
    points = point_count(data)
    pair_count, gap_count = points * (points - 1) // 2, points - 1
    weights, rewards, knots = data['weights'], data['h'], data['cob_knots']
    if [len(row) for row in weights] != [pair_count] * TYPE_COUNT:
        raise ValueError(f'weights: expected 3 rows of {pair_count} integers')
    if [len(row) for row in rewards] != [points] * 2:
        raise ValueError(f'rewards: expected 2 rows of {points} integers')
    if [[len(row) for row in gap] for gap in knots] != [[KNOT_COUNT] * TYPE_COUNT] * gap_count:
        raise ValueError(f'knot values: expected {gap_count} x 3 rows of 14 integers')
    numbers = [x for row in weights + rewards for x in row] + [x for gap in knots for row in gap for x in row]
    if not all(isinstance(x, int) and not isinstance(x, bool) for x in numbers):
        raise ValueError('all weights, rewards and knot values must be integers')
    minimum_gap = (Fraction(data['separation']) * grid).__floor__()
    lines = ['certificate-parameters 1',
             f"gridLength {int(data['R'])}",
             f'gridPerUnit {grid}',
             f"scale {int(data['scale'])}",
             f"alpha {int(data['alpha'])}",
             f'minimumGap {minimum_gap}',
             f'firstKnot {3 * grid // 4}',
             f'knotStep {grid // 8}',
             'weights']
    lines += [' '.join(str(x) for x in row) for row in weights]
    lines += ['rewards'] + [' '.join(str(x) for x in row) for row in rewards]
    lines += ['potentials'] + [' '.join(str(x) for x in row) for gap in knots for row in gap]
    lines += ['end']
    return '\n'.join(lines) + '\n'


def main(arguments):
    if len(arguments) != 3:
        print('usage: make_parameters.py inputs.json parameters.txt', file=sys.stderr)
        return 2
    with open(arguments[1], encoding='utf-8') as source:
        data = json.load(source)
    with open(arguments[2], 'w', encoding='utf-8') as target:
        target.write(parameter_text(data))
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv))
