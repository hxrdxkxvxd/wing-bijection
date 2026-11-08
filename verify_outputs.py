#!/usr/bin/env python3
"""Check executable outputs directly against the paper's two finite conditions."""
import ast
from pathlib import Path
import random
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
BINARY = ROOT / '.lake/build/bin/wingDemo'


def check(n, points, wings):
    result = subprocess.run([str(BINARY), str(n), ','.join(map(str, points)),
                             ','.join(map(str, wings))],
                            capture_output=True, text=True, timeout=30)
    if result.returncode:
        raise AssertionError((n, points, wings, result.returncode, result.stdout, result.stderr))
    lines = result.stdout.splitlines()
    pairs = ast.literal_eval(next(s.split(': ', 1)[1] for s in lines
                                  if s.startswith('(point, tau(point)): ')))
    reported_keep = ast.literal_eval(next(s.split(': ', 1)[1] for s in lines
                                         if s.startswith('agreements: ')))
    reported_boundary = ast.literal_eval(next(s.split(':', 1)[1] for s in lines
                                             if s.startswith('boundary: ')))
    mapping = dict(pairs)
    assert len(pairs) == len(points) == len(mapping)
    assert set(mapping) == set(mapping.values()) == set(points)
    wing_by_point = dict(zip(points, wings))
    assert all((x ^ y) & wing_by_point[x] == wing_by_point[x] for x, y in pairs)
    keep = [sum(((x ^ y) >> j) & 1 == 0 for x, y in pairs) for j in range(n)]
    boundary = [sum(x ^ (1 << j) not in mapping for x in points) for j in range(n)]
    assert keep == reported_keep and boundary == reported_boundary
    assert all(a <= b for a, b in zip(keep, boundary))
    assert lines[-1] == 'output checks: true'
    return {'n': n, 'points': points, 'wings': wings,
            'mapping': pairs, 'agreements': keep, 'boundary': boundary}


def valid_masks(n, points, x):
    points = set(points)
    choices = []
    for wing in range(1 << n):
        sub = wing
        while x ^ sub in points:
            if sub == 0:
                choices.append(wing)
                break
            sub = (sub - 1) & wing
    return choices


def main():
    cases = [
        (0, [], []), (0, [0], [0]), (2, [0], [0]),
        (2, [0, 1, 2, 3], [3, 3, 3, 3]),
        (4, [0, 1, 4, 5, 7, 12, 13, 14, 15], [5, 5, 5, 9, 10, 3, 10, 3, 3]),
        (3, [0, 1, 2, 5, 6, 7], [2, 0, 2, 2, 4, 2]),
        (3, [0, 1, 2, 4, 6, 7], [0, 1, 6, 6, 2, 0]),
    ]
    rng = random.Random(20261107)
    for n in [1, 2, 3]:
        for _ in range(12):
            points = [x for x in range(1 << n) if rng.random() < 0.7]
            wings = [rng.choice(valid_masks(n, points, x)) for x in points]
            cases.append((n, points, wings))
    results = [check(*case) for case in cases]
    rejected = []
    for args, expected in [(['2', '0', '1'], 1),
                           (['2', '0,0', '0,0'], 2),
                           (['2', '4', '0'], 2),
                           (['2', '0', '4'], 2),
                           (['2', '0,1', '0'], 2)]:
        p = subprocess.run([str(BINARY), *args], capture_output=True, text=True, timeout=30)
        assert p.returncode == expected, (args, p.returncode, p.stdout, p.stderr)
        rejected.append({'args': args, 'exit_status': p.returncode})
    print(f"valid cases passed: {len(results)}; invalid inputs rejected: {len(rejected)}")


if __name__ == '__main__':
    main()
