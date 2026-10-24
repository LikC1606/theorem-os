"""Exact finite graph counts for a proposed proof route; not Lean acceptance."""
from datetime import datetime, timezone
from pathlib import Path
import hashlib
import json


def neighbors(vertex, height):
    polarity, horizontal, vertical = vertex
    if polarity == 'up':
        candidates = [('down', horizontal, vertical - 1),
                      ('down', horizontal, vertical),
                      ('down', horizontal - 1, vertical)]
    else:
        candidates = [('up', horizontal, vertical + 1),
                      ('up', horizontal, vertical),
                      ('up', horizontal + 1, vertical)]
    return [candidate for candidate in candidates if 0 <= candidate[2] < height]


def normalized_edge(previous, current):
    return ((previous[0], previous[1] - current[1], previous[2]),
            (current[0], 0, current[2]))


def block(height, steps):
    states = [(previous, (polarity, 0, vertical))
              for polarity in ('up', 'down') for vertical in range(height)
              for previous in neighbors((polarity, 0, vertical), height)]
    index = {state: number for number, state in enumerate(states)}
    transitions = [[index[normalized_edge(current, successor)]
                    for successor in neighbors(current, height) if successor != previous]
                   for previous, current in states]
    counts = [1] * len(states)
    for _ in range(steps):
        counts = [sum(counts[successor] for successor in row) for row in transitions]
    maximum = max(counts)
    # mu = sqrt(2 + sqrt(2)); mu^(2*steps) = A + B*sqrt(2).
    rational, radical = 1, 0
    for _ in range(steps):
        rational, radical = 2 * rational + 2 * radical, rational + 2 * radical
    difference = maximum ** 2 - rational
    below = difference < 0 or difference ** 2 < 2 * radical ** 2
    assert below
    return {'height': height, 'stepsAfterIncomingEdge': steps,
            'stateCount': len(states), 'normalizedDirectedEdges': states,
            'transitionIndices': transitions, 'continuationsPerState': counts,
            'maximumContinuations': maximum,
            'exactComparison': {'mu': 'sqrt(2 + sqrt(2))',
                                'muPowerTwiceSteps': {'A': rational, 'B': radical},
                                'maximumSquaredMinusA': difference,
                                'differenceSquared': difference ** 2,
                                'twiceBSquared': 2 * radical ** 2,
                                'maximumStrictlyBelowMuPowerSteps': below}}


if __name__ == '__main__':
    stage = Path(__file__).resolve().parent
    official = stage.parent / 'honeycomb-confined-finiteness-20261024/CanonicalDefinitions.lean.inc'
    results = [block(height, steps) for height, steps in [(1, 1), (2, 2), (3, 5), (4, 14)]]
    expected = [1, 3, 20, 5376]
    assert [result['maximumContinuations'] for result in results] == expected
    report = {'schema': 'theorem-os.nonbacktracking-block-diagnostic.v1',
              'observedAt': datetime.now(timezone.utc).isoformat(),
              'canonicalDefinitionReference': str(official),
              'canonicalDefinitionSHA256': hashlib.sha256(official.read_bytes()).hexdigest(),
              'arithmetic': 'Python arbitrary-precision integers; no floating-point comparisons',
              'scope': 'Finite diagnostic from translationally normalized incoming edges; requires formal connection to canonical paths and kernel proof.',
              'leanInvocations': 0, 'nativeTaskProof': False, 'originalGoalSolved': False,
              'sourceSHA256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              'blocks': results}
    with (stage / 'block-counts.json').open('x') as output:
        json.dump(report, output, ensure_ascii=False, indent=2)
        output.write('\n')
    print(json.dumps([{'height': item['height'], 'steps': item['stepsAfterIncomingEdge'],
                       'maxContinuations': item['maximumContinuations']} for item in results]))
