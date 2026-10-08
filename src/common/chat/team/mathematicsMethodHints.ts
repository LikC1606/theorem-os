/** Small optional method cards. Lexical cues select reading material, never decide mathematical truth. */
const METHOD_CARDS = [
  {
    cue: /counterexample|refut|missing premise|反例|缺失.*条件/iu,
    text: 'Counterexample repair: check every original hypothesis against the witness. If it violates an omitted original condition, derive a usable property from that condition and retry the revised claim. If it satisfies the original assumptions but refutes the helper, change the conclusion or connection; no consequence of those assumptions can exclude it. Unknown legality stays unknown. Only a legal witness violating the original goal refutes that goal; finite examples cannot certify truth.',
  },
  {
    cue: /induct|recurs|descen|minimal|maximal|well.found|归纳|递归|下降|最小|最大/iu,
    text: 'Induction or extremality: expand a general recursive step; compare its call with the current hypothesis. Form the actual generalized proposition by universal quantification over changed parameters or a needed invariant; retry the same step, base case and specialization back to the original goal. For a least feasible natural b above a, derive infeasibility for a < m < b. Descent needs preserved constraints, a still-bad object and strict well-founded decrease; real sets need not have minima.',
  },
  {
    cue: /represent|invariant|symmetr|analogy|state transition|表示|不变量|对称|类比/iu,
    text: 'Representation: align objects, operations, assumptions and return to goal; preservation need not reflect back. Reuse applicable theorems or rebuild only justified mechanisms; never invent structure. Legal same-state objects with different continuations refute state sufficiency, not the target; repair from hypotheses. Check finite states, deterministic continuation, eventual periodicity versus periodicity from the start; full history may destroy finiteness. No counterexample is not proof.',
  },
  {
    cue: /construct|witness|candidate|special case|boundary|degenerat|small case|example|构造|见证|候选|特例|边界|退化|例子/iu,
    text: 'Specialization and construction: name the unknown object and required relations. Unfold definitions or a revealing boundary case to justify a candidate form; substitute it and refine unmet conditions using original hypotheses. Check quantifiers, types and degenerate cases. Sufficient construction choices need not be necessary. Failure of one candidate or restricted family does not refute the target; finite samples do not prove it. Transfer relations, not an unrelated example answer.',
  },
  {
    cue: /sufficient|necessary|backward|bridge|connect|hypothes|assumption|充分|必要|反向|连接|假设/iu,
    text: 'Bridge synthesis: test a concrete call with explicit premises privately; keep before/after, context and diagnostics. Residual goals belong to this connection, not necessarily the theorem. Trace added premises; seek a checked local connection or revised claim. Query intended transformations; read full local types and instantiate. Reuse library support, preserving witness obligations. Counterexamples refute exact claims; critique is no replacement. Conditional work proves neither end; no axiom/sorry/admit.',
  },
] as const;

/** Call with the current bounded task, not the full conversation. No match needs no method ceremony. */
export function selectMathematicsMethodHints(task: string): string {
  const selected = METHOD_CARDS.filter((card) => card.cue.test(task)).slice(0, 2);
  return selected.length
    ? [
        'Optional mathematical methods for this question; choose only what helps and recheck applicability:',
        ...selected.map((card) => card.text),
      ].join('\n')
    : '';
}
