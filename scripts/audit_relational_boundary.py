"""Exact finite audit from the literal seed/center coefficient definitions.

This is a reproducible integer experiment, not an all-cutoff Lean proof.
Material positions start at 1; B is the periodic profile truncated at slope*M.
"""


def slope(b):
    return 4 if b == 2 else b


def radii(b):
    return [1] if b == 2 else range(1, b // 2 + 1)


def profile(b, n):
    if b == 2:
        return 1 - int(n % 2 == 0) - 2 * int(n % 4 == 0)
    if b % 2:
        return 1 - b * int(n % b == 0)
    return 1 + int(n % (b // 2) == 0) - (b + 2) * int(n % b == 0)


def literal_row(b, M, window):
    row = [0] * window
    for r in radii(b):
        row[r - 1] += 1
    for k in range(M):
        center = slope(b) * (k + 1)
        for r in radii(b):
            row[center - r - 1] += 1
            row[center - 1] -= 2
            row[center + r - 1] += 1
    return row


for M in range(1, 101):
    window = max(slope(b) * M + len(radii(b)) for b in range(2, 8))
    squared_norm = 0
    for b in range(2, 8):
        C = literal_row(b, M, window)
        B = [profile(b, n) if n <= slope(b) * M else 0 for n in range(1, window + 1)]
        E = [c - q for c, q in zip(C, B)]
        expected = [int(slope(b) * M < n <= slope(b) * M + len(radii(b)))
                    for n in range(1, window + 1)]
        assert E == expected, (b, M)
        squared_norm += sum(x * x for x in E)
    assert squared_norm == 12, M
print('PASS_EXACT_FINITE: cutoffs 1..100; literal C=B+E; antipodal endpoints retained; ||E||_F^2=12')
