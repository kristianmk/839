#!/usr/bin/env python3
"""Tests of verify and verify8, the C++ reference verifier of the local inequality for frames of
seven and of eight points.

Written by Kristian Muri Knausgård <kristianmk@ieee.org>.
AI assistance: this file was drafted with Claude (Anthropic), an AI system, under the direction
of the author, who is responsible for its content.

1. Malformed input, input outside the limits and data that violate a condition on local data are
   rejected with exit code 3, with the message for that reason and without a result line; wrong
   usage gives exit code 2. Data for frames of eight points are rejected by the program for
   seven, and data for seven points by the program for eight.
2. False certificates are not accepted: with the weights of a certificate reduced, or with its
   functions B_r removed, the program must end with exit code 1 and the status UNRESOLVED.
3. Certificates that are easier than the published ones (a larger rate alpha) are accepted, with
   the counts of boxes recorded here.
4. All of the above also with the build under AddressSanitizer and UndefinedBehaviorSanitizer,
   which stops at any out-of-bounds access and any signed overflow.
5. With --full: the three certificates of the paper give the counts of boxes stated there. With
   --full-sanitizer: the same three runs with the sanitizer build (several times slower).

usage: verify_test.py [--certificates DIR] [--full] [--full-sanitizer]
       DIR holds the folders certificate/, certificate_line/ and certificate_third/ (default:
       the parent folder).
       Needs build/verify, build/verify8, build_san/verify and build_san/verify8, see
       CMakeLists.txt. The second certificate has frames of eight points and is run with verify8.
"""
import argparse
import copy
import json
import os
import subprocess
import sys
import tempfile

from make_parameters import parameter_text, point_count

HERE = os.path.dirname(os.path.abspath(__file__))
RELEASE = os.environ.get('VERIFY_RELEASE', os.path.join(HERE, 'build', 'verify'))
SANITIZE = os.environ.get('VERIFY_SANITIZE', os.path.join(HERE, 'build_san', 'verify'))
SAN_ENV = dict(ASAN_OPTIONS='detect_leaks=1:abort_on_error=0', UBSAN_OPTIONS='halt_on_error=1:print_stacktrace=1')

# counts of boxes of the three certificates, as stated in the paper and in lean/README.md
PUBLISHED = {
    'certificate': dict(nodes=60467309, leaves=30233655, basic=21157274, affine=9076381, max_stack=49),
    'certificate_line': dict(nodes=535332163, leaves=267666082, basic=202511130, affine=65154952, max_stack=63),
    'certificate_third': dict(nodes=572959453, leaves=286479727, basic=256891820, affine=29587907, max_stack=68),
}


def run(binary, parameters, table, env=None):
    """runs the verifier; returns (exit code, result line as a dictionary or None, standard error)"""
    full_env = dict(os.environ)
    full_env.update(env or {})
    result = subprocess.run([binary, parameters, table], capture_output=True, text=True, env=full_env)
    line = result.stdout.strip()
    return result.returncode, (json.loads(line) if line else None), result.stderr


def program(binary, certificate_data):
    """the program for the number of points of a certificate: verify for seven, verify8 for eight"""
    points = point_count(certificate_data)
    return binary if points == 7 else binary + str(points)


def replace_number(text, keyword, value):
    """the parameter text with the number after a keyword replaced"""
    words = text.split('\n')
    for index, line in enumerate(words):
        if line.startswith(keyword + ' '):
            words[index] = f'{keyword} {value}'
            return '\n'.join(words)
    raise KeyError(keyword)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--certificates', default=os.path.join(HERE, '..'))
    parser.add_argument('--full', action='store_true')
    parser.add_argument('--full-sanitizer', action='store_true')
    options = parser.parse_args()
    failures = 0

    def check(name, ok, detail=''):
        nonlocal failures
        print(('ok    ' if ok else 'FAIL  ') + name + ('' if ok else '   ' + detail), flush=True)
        failures += 0 if ok else 1

    data = {}
    tables = {}
    for name in PUBLISHED:
        folder = os.path.join(options.certificates, name)
        with open(os.path.join(folder, 'inputs.json'), encoding='utf-8') as source:
            data[name] = json.load(source)
        tables[name] = os.path.join(folder, 'kernel_lower.bin')
    first = data['certificate']
    good_text = parameter_text(first)
    with open(tables['certificate'], 'rb') as source:
        good_table = source.read()
    builds = (('release', RELEASE, None), ('sanitizer', SANITIZE, SAN_ENV))

    def changed(change, base=first):
        modified = copy.deepcopy(base)
        change(modified)
        return parameter_text(modified)

    def set_item(key, row, column, value):
        def change(modified):
            modified[key][row][column] = value
        return change

    def scale_weights(numerator, denominator):
        def change(modified):
            modified['weights'] = [[x * numerator // denominator for x in row] for row in modified['weights']]
        return change

    def no_potentials(modified):
        modified['cob_knots'] = [[[0] * 14 for _ in range(3)] for _ in modified['cob_knots']]

    def knot_shift(modified):
        modified['cob_knots'][0][0][5] += 1

    def end_knot(modified):
        modified['cob_knots'][0][0][13] += 1
        modified['cob_knots'][1][0][13] -= 1

    def scale_alpha(factor):
        def change(modified):
            modified['alpha'] = modified['alpha'] * factor
        return change

    weights_text = '\n'.join(' '.join(str(x) for x in row) for row in first['weights'])
    short_weights = good_text.replace(weights_text, weights_text.rsplit(' ', 1)[0])

    # 1. rejected parameter files, in four groups by the reason the program must give
    reasons = ('the parameter file is malformed', 'a parameter is outside the limits of this program',
               'the parameters violate a condition on local data', 'the bound for the 64-bit intermediates does not hold')
    group_starts = {'empty parameter file': 0, 'grid length 0': 1, 'scale not divisible by the grid': 2,
                    'bound for the 64-bit intermediates exceeded': 3}
    rejected = {
        'empty parameter file': '',
        'wrong first keyword': good_text.replace('certificate-parameters', 'parameters'),
        'unknown format version': good_text.replace('certificate-parameters 1', 'certificate-parameters 2'),
        'keyword misspelt': good_text.replace('rewards', 'reward'),
        'keywords in another order': good_text.replace('gridLength', 'x').replace('gridPerUnit', 'gridLength').replace('x ', 'gridPerUnit '),
        'a number that is not an integer': replace_number(good_text, 'alpha', '6219.5'),
        'a word in place of a number': replace_number(good_text, 'scale', 'large'),
        'one weight missing': short_weights,
        'one number too many': good_text.replace('\npotentials\n', ' 0\npotentials\n'),
        'text after the end': good_text + '0\n',
        'the end is missing': good_text.replace('end\n', ''),
        'a number beyond 64 bits': replace_number(good_text, 'alpha', '99999999999999999999'),
        'grid length 0': replace_number(good_text, 'gridLength', 0),
        'grid length above the limit': replace_number(good_text, 'gridLength', 2 ** 21 + 1),
        'grid steps per unit 0': replace_number(good_text, 'gridPerUnit', 0),
        'scale 0': replace_number(good_text, 'scale', 0),
        'scale above the limit': replace_number(good_text, 'scale', 2 ** 31),
        'negative alpha': replace_number(good_text, 'alpha', -1),
        'smallest gap 0': replace_number(good_text, 'minimumGap', 0),
        'smallest gap beyond the grid': replace_number(good_text, 'minimumGap', first['R'] + 1),
        'negative first knot': replace_number(good_text, 'firstKnot', -1),
        'knot step 0': replace_number(good_text, 'knotStep', 0),
        'knots beyond the limit': replace_number(good_text, 'knotStep', 2 ** 26),
        'a weight above the limit of magnitude': changed(set_item('weights', 2, 0, 2 * 10 ** 9)),
        'scale not divisible by the grid': replace_number(good_text, 'scale', 2 ** 28 + 1),
        'scale not divisible by the knot step': replace_number(good_text, 'knotStep', 2047),
        'a negative weight': changed(set_item('weights', 0, 0, -1)),
        'weights above the cap': changed(scale_weights(3, 1)),
        'a weight that decreases with the label': changed(set_item('weights', 1, 3, first['weights'][0][3] - 1)),
        'a negative reward': changed(set_item('h', 0, 2, -1)),
        'reward of a double point below that of a simple point': changed(set_item('h', 1, 2, first['h'][0][2] - 1)),
        'functions B_r that do not sum to zero': changed(knot_shift),
        'a function B_r that does not vanish at its last knot': changed(end_knot),
        'alpha too small for the length of the grid': replace_number(good_text, 'alpha', first['alpha'] - 1),
        'rewards too large for the length of the grid': changed(set_item('h', 1, 3, first['h'][1][3] + 1)),
        'bound for the 64-bit intermediates exceeded': replace_number(good_text, 'alpha', 10 ** 9),
    }
    expected_reason = {}
    group = 0
    for name in rejected:
        group = group_starts.get(name, group)
        expected_reason[name] = reasons[group]
    wrong_size = 'the table has the wrong size or cannot be read'
    bad_tables = {
        'empty table': (b'', wrong_size),
        'table one byte short': (good_table[:-1], wrong_size),
        'table one byte long': (good_table + b'\0', wrong_size),
        'table one entry short': (good_table[:-4], wrong_size),
        'table entry above the scale': (good_table[:400] + (first['scale'] + 1).to_bytes(4, 'little') + good_table[404:],
                                        'an entry of the table exceeds the scale'),
    }
    with tempfile.TemporaryDirectory() as folder:
        parameter_path = os.path.join(folder, 'parameters.txt')
        table_path = os.path.join(folder, 'table.bin')

        def outcome(binary, env, text, table=None):
            with open(parameter_path, 'w', encoding='utf-8') as target:
                target.write(text)
            if table is None:
                return run(binary, parameter_path, tables['certificate'], env)
            with open(table_path, 'wb') as target:
                target.write(table)
            return run(binary, parameter_path, table_path, env)

        for label, binary, env in builds:
            for name, text in rejected.items():
                code, line, err = outcome(binary, env, text)
                ok = code == 3 and line is None and err.strip() == 'verify: ' + expected_reason[name]
                check(f'{label}: {name} -> exit code 3', ok, f'got {code}: {err[:200]}')
            for name, (table, reason) in bad_tables.items():
                code, line, err = outcome(binary, env, good_text, table)
                ok = code == 3 and line is None and err.strip() == 'verify: ' + reason
                check(f'{label}: {name} -> exit code 3', ok, f'got {code}: {err[:200]}')
            result = subprocess.run([binary], capture_output=True, text=True)
            check(f'{label}: no arguments -> exit code 2', result.returncode == 2 and result.stdout == '')
            code, line, err = run(binary, '/nonexistent/parameters.txt', tables['certificate'], env)
            check(f'{label}: missing parameter file -> exit code 3', code == 3 and line is None)
            with open(parameter_path, 'w', encoding='utf-8') as target:
                target.write(good_text)
            code, line, err = run(binary, parameter_path, '/nonexistent/table.bin', env)
            check(f'{label}: missing table -> exit code 3', code == 3 and line is None)
            # data for another number of points
            malformed = 'verify: ' + reasons[0]
            second = data['certificate_line']
            with open(parameter_path, 'w', encoding='utf-8') as target:
                target.write(parameter_text(second))
            code, line, err = run(binary, parameter_path, tables['certificate_line'], env)
            ok = code == 3 and line is None and err.strip() == malformed
            check(f'{label}: data for eight points, program for seven -> exit code 3', ok, f'got {code}: {err[:200]}')
            with open(parameter_path, 'w', encoding='utf-8') as target:
                target.write(good_text)
            code, line, err = run(program(binary, second), parameter_path, tables['certificate'], env)
            ok = code == 3 and line is None and err.strip() == malformed
            check(f'{label}: data for seven points, program for eight -> exit code 3', ok, f'got {code}: {err[:200]}')

            # 2. false certificates
            false_cases = {
                'weights reduced by one tenth': (changed(scale_weights(9, 10)), 16379, 'certificate'),
                'weights halved': (changed(scale_weights(1, 2)), 493, 'certificate'),
                'functions B_r removed': (changed(no_potentials), 588146, 'certificate'),
                'second certificate, weights reduced by one tenth':
                    (changed(scale_weights(9, 10), data['certificate_line']), 4743953, 'certificate_line'),
                'third certificate, weights halved':
                    (changed(scale_weights(1, 2), data['certificate_third']), None, 'certificate_third'),
            }
            for name, (text, nodes, certificate) in false_cases.items():
                if certificate != 'certificate':
                    with open(parameter_path, 'w', encoding='utf-8') as target:
                        target.write(text)
                    code, line, err = run(program(binary, data[certificate]), parameter_path, tables[certificate], env)
                else:
                    code, line, err = outcome(binary, env, text)
                clean = 'ERROR' not in err and 'runtime error' not in err
                ok = code == 1 and line is not None and line['status'] == 'UNRESOLVED' and clean
                ok = ok and (nodes is None or line['nodes'] == nodes) and 'gaps of the box' in err
                check(f'{label}: {name} -> exit code 1, not accepted', ok, f'got {code}: {line} {err[:200]}')

            # 3. easier certificates
            easy_cases = {
                'alpha doubled': (changed(scale_alpha(2)), dict(nodes=559, leaves=280, basic=280, affine=0, max_stack=33)),
                'alpha times four': (changed(scale_alpha(4)), dict(nodes=1, leaves=1, basic=1, affine=0, max_stack=1)),
            }
            for name, (text, expected) in easy_cases.items():
                code, line, err = outcome(binary, env, text)
                clean = 'ERROR' not in err and 'runtime error' not in err
                ok = code == 0 and line is not None and line['status'] == 'PASS_COB_CONTINUUM' and clean
                ok = ok and all(line[key] == value for key, value in expected.items())
                check(f'{label}: {name} -> accepted with {expected["nodes"]} boxes', ok, f'got {code}: {line} {err[:200]}')

        # 5. the certificates of the paper
        full_builds = ([builds[0]] if options.full else []) + ([builds[1]] if options.full_sanitizer else [])
        for label, binary, env in full_builds:
            for name, expected in PUBLISHED.items():
                with open(parameter_path, 'w', encoding='utf-8') as target:
                    target.write(parameter_text(data[name]))
                code, line, err = run(program(binary, data[name]), parameter_path, tables[name], env)
                clean = 'ERROR' not in err and 'runtime error' not in err
                ok = code == 0 and line is not None and line['status'] == 'PASS_COB_CONTINUUM' and clean
                ok = ok and all(line[key] == value for key, value in expected.items())
                ok = ok and line['nodes'] == 2 * line['leaves'] - 1 and line['leaves'] == line['basic'] + line['affine']
                check(f'{label}: {name} -> accepted, {expected["nodes"]} boxes, {expected["leaves"]} accepted', ok,
                      f'got {code}: {line} {err[:200]}')
                if ok:
                    print('      ' + json.dumps(line), flush=True)

    print(f'\n{"ALL TESTS PASSED" if failures == 0 else str(failures) + " TESTS FAILED"}')
    sys.exit(0 if failures == 0 else 1)


if __name__ == '__main__':
    main()
