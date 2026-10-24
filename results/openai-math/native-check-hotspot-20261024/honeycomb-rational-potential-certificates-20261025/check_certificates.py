"""Check finite incoming-edge potentials exactly; this is not a Lean proof."""
from datetime import datetime, timezone
from fractions import Fraction
from hashlib import sha256
import json
from pathlib import Path


def neighbors(vertex, height):
    polarity, horizontal, vertical = vertex
    if polarity == "up":
        candidates = [("down", horizontal, vertical - 1),
                      ("down", horizontal, vertical),
                      ("down", horizontal - 1, vertical)]
    else:
        candidates = [("up", horizontal, vertical + 1),
                      ("up", horizontal, vertical),
                      ("up", horizontal + 1, vertical)]
    return [v for v in candidates if 0 <= v[2] < height]


def normalize(previous, current):
    return ((previous[0], previous[1] - current[1], previous[2]),
            (current[0], 0, current[2]))


def certificate(height, numerator, denominator, weights, prior):
    states = [(previous, (polarity, 0, vertical))
              for polarity in ("up", "down") for vertical in range(height)
              for previous in neighbors((polarity, 0, vertical), height)]
    index = {state: i for i, state in enumerate(states)}
    transitions = [[index[normalize(current, following)]
                    for following in neighbors(current, height)
                    if following != previous]
                   for previous, current in states]
    assert json.loads(json.dumps(states)) == prior["normalizedDirectedEdges"]
    assert transitions == prior["transitionIndices"]
    assert len(states) == len(weights) and min(weights) > 0
    beta = Fraction(numerator, denominator)
    # For positive beta, these exact inequalities imply beta < sqrt(2+sqrt(2)).
    delta = beta * beta - 2
    assert beta > 0 and delta > 0 and delta * delta < 2
    rows = []
    for i, state in enumerate(states):
        following_weight = sum(weights[j] for j in transitions[i])
        slack = numerator * weights[i] - denominator * following_weight
        assert slack >= 0
        rows.append({"index": i, "normalizedIncomingEdge": state,
                     "weight": weights[i], "successors": transitions[i],
                     "successorWeightSum": following_weight,
                     "scaledSlack": slack})
    return {"height": height, "stateCount": len(states),
            "beta": {"numerator": numerator, "denominator": denominator},
            "weights": weights, "minWeight": min(weights),
            "maxWeight": max(weights), "rows": rows,
            "allExactTransitionInequalitiesPassed": True,
            "muComparison": {"betaSquaredMinusTwo": str(delta),
                             "squareOfBetaSquaredMinusTwo": str(delta * delta),
                             "strictlyLessThanTwo": True},
            "intendedInduction": "N(n,a,b) <= w(a,b)/min(w) * beta^n",
            "leanConnectionProved": False}


if __name__ == "__main__":
    stage = Path(__file__).resolve().parent
    prior_path = stage.parent / "honeycomb-nonbacktracking-block-diagnostic-20261025/block-counts.json"
    prior_bytes = prior_path.read_bytes()
    prior = {b["height"]: b for b in json.loads(prior_bytes)["blocks"]}
    definitions = stage.parent / "honeycomb-confined-finiteness-20261024/CanonicalDefinitions.lean.inc"
    result = {"schema": "theorem-os.rational-potential-diagnostic.v1",
              "observedAt": datetime.now(timezone.utc).isoformat(),
              "arithmetic": "arbitrary-precision integers and exact fractions; no floating point",
              "definitionReference": str(definitions),
              "definitionSHA256": sha256(definitions.read_bytes()).hexdigest(),
              "priorDiagnosticSHA256": sha256(prior_bytes).hexdigest(),
              "scriptSHA256": sha256(Path(__file__).read_bytes()).hexdigest(),
              "leanInvocations": 0, "nativeTaskAcceptance": False,
              "originalGoalSolved": False,
              "certificates": [
                  certificate(3, 11, 6,
                      [6, 6, 11, 9, 9, 7, 10, 10, 7, 10, 10, 11, 9, 9, 6, 6], prior[3]),
                  certificate(4, 1847, 1000,
                      [29, 29, 64, 50, 50, 56, 58, 58, 33, 52, 52,
                       33, 52, 52, 56, 58, 58, 64, 50, 50, 29, 29], prior[4])],
              "evidenceBoundary": "Finite rational transition checks only. The canonical path connection, induction and summability still require Lean kernel verification."}
    with (stage / "certificates.json").open("x") as out:
        json.dump(result, out, ensure_ascii=False, indent=2)
        out.write("\n")
    print(json.dumps([{"height": c["height"], "states": c["stateCount"],
                       "maxWeight": c["maxWeight"],
                       "minimumScaledSlack": min(r["scaledSlack"] for r in c["rows"])}
                      for c in result["certificates"]]))
