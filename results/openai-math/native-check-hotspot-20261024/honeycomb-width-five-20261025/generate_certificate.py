"""Exact diagnostic and witness generation; Python is not a proof checker."""

from fractions import Fraction
from hashlib import sha256
import json
from pathlib import Path

stage = Path(__file__).resolve().parent
p, q = 1847, 1000


def neighbors(v):
    side, i, j = v
    if side == 0:
        choices = [(1, i, j - 1), (1, i, j), (1, i - 1, j)]
    else:
        choices = [(0, i, j + 1), (0, i, j), (0, i + 1, j)]
    return tuple(w for w in choices if 0 <= w[2] < 5)


def normalize(w):
    t = w[-1][1]
    return tuple((side, i - t, j) for side, i, j in w)


def slide(w, c):
    return normalize((w if len(w) < 6 else w[1:]) + (c,))


levels = {1: {((side, 0, j),) for side in range(2) for j in range(5)}}
for n in range(2, 7):
    levels[n] = {
        normalize(w + (c,))
        for w in levels[n - 1]
        for c in neighbors(w[-1])
        if c not in w
    }
all_counts = {str(k): len(v) for k, v in levels.items()}
short_levels = {1: {((0, 0, 0),)}}
for n in range(2, 6):
    short_levels[n] = {
        normalize(w + (c,))
        for w in short_levels[n - 1]
        for c in neighbors(w[-1])
        if c not in w
    }
levels = {**short_levels, 6: levels[6]}
states = sorted(set.union(*levels.values()), key=lambda w: (len(w), w))
successors = {
    w: tuple(slide(w, c) for c in neighbors(w[-1]) if c not in w)
    for w in states
}
assert all(v in successors for vs in successors.values() for v in vs)
full = sorted(levels[6])
counts = [{w: 1 for w in full}]
for _ in range(10):
    counts.append({w: sum(counts[-1][v] for v in successors[w]) for w in full})
assert len(full) == 336
assert max(counts[10].values()) == 450
assert 450 * q**10 < p**10
assert Fraction(p, q)**2 < 2 + Fraction(1414, 1000)
assert Fraction(1414, 1000)**2 < 2

potential = {
    w: sum(p ** (9 - k) * q**k * counts[k][w] for k in range(10))
    for w in full
}
for n in range(5, 0, -1):
    for w in levels[n]:
        numerator = q * sum(potential[v] for v in successors[w])
        potential[w] = max(1, (numerator + p - 1) // p)

assert all(potential[w] > 0 for w in states)
assert all(q * sum(potential[v] for v in successors[w]) <= p * potential[w]
           for w in states)


def vertex(v):
    side, i, j = v
    return f'.{"up" if side == 0 else "down"} ({i}) {j}'


def window(w):
    return '[' + ', '.join(vertex(v) for v in w) + ']'


# A simple list-based definition is intentional. Lean recomputes every local
# candidate, normalization, lookup and integer inequality using ordinary decide.
blocks = [states[k:k+12] for k in range(0, len(states), 12)]
table = ''
for k, block in enumerate(blocks):
    table += f'def table{k} : List (List Vertex × ℕ) := [\n'
    table += ',\n'.join(f'  ({window(w)}, {potential[w]})' for w in block)
    table += '\n]\n\n'
table += 'def table : List (List Vertex × ℕ) :=\n  '
table += ' ++ '.join(f'table{k}' for k in range(len(blocks))) + '\n'
(stage / 'PotentialTable.lean.inc').write_text(table)

checks = ''
for k, _ in enumerate(blocks):
    checks += f'lemma checked{k} : ∀ w ∈ table{k}.map Prod.fst, rowOK w := by decide\n'
checks += '\nlemma table_checked : ∀ w ∈ states, rowOK w := by\n'
checks += '  simp only [states, table, List.map_append, List.forall_mem_append]\n'
# Construct the left-associated conjunction matching Lean's ++ syntax.
conjunction = 'checked0'
for k in range(1, len(blocks)):
    conjunction = f'⟨{conjunction}, checked{k}⟩'
checks += '  exact ' + conjunction + '\n\n'
checks += 'lemma source_checked : normalize [Vertex.up 0 0] ∈ states := by decide\n'
(stage / 'CertificateChecks.lean.inc').write_text(checks)

records = [
    {'window': w, 'potential': potential[w],
     'successors': [states.index(v) for v in successors[w]]}
    for w in states
]
diagnostic = {
    'height': 5, 'windowSize': 6, 'betaNumerator': p, 'betaDenominator': q,
    'allStateCountsByLength': all_counts,
    'certificateStateCountsByLength': {str(k): len(v) for k, v in levels.items()},
    'stateCount': len(states), 'fullStateCount': len(full),
    'maximumFullStateTenStepCount': max(counts[10].values()),
    'blockComparison': {'left': 450 * q**10, 'right': p**10},
    'initialPotential': potential[((0, 0, 0),)],
    'localCertificatesAllTrueInPython': True,
    'leanProofEstablished': False,
    'tableSHA256': sha256(table.encode()).hexdigest(),
    'states': records,
}
(stage / 'certificate-diagnostic.json').write_text(json.dumps(diagnostic, indent=2) + '\n')
print(json.dumps({k: v for k, v in diagnostic.items() if k != 'states'}))
