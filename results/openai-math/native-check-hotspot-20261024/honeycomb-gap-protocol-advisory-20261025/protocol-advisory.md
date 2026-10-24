Protocol clarification for mathematical gap reports (2026-10-25).

The frozen parser's mathematicalGap.consumer object has exactly two keys: taskId and taskDigest. The phrase visible kind:"goal" describes the task referred to by those two keys; kind is not a key in the consumer object. For the current unchanged original goal the correct consumer reference is:

```json
{"taskId":"initial_goal_1","taskDigest":"ab8c91c92c1d5d985ed03edfaee27bbef6df38455b84a82711d07d8d13e77890"}
```

Use the current COOPERATION.json contract if that goal is subsequently revised. Keep all six required mathematicalGap fields: consumer, previousGap, reduced, remaining, evidenceScope and reconsiderWhen. The five descriptive fields must contain your actual mathematical findings; the example above only specifies the consumer reference. previousDeliveryId is optional and must refer to a visible mathematicalGaps entry for that goal, not an ordinary research delivery.

A historical width_two_summability_diagnostic report was rejected because its consumer included kind. This was intake feedback, not a Lean proof failure. A correction must use the same active assignment binding and its visible delivery receipt. If a matching needs-correction receipt is present in your current assignment, submit a complete corrected event and set replacesReceipt to that receipt's id. If a later correction is itself rejected, replace that latest receipt. Do not reuse an old assignment's delivery binding or claim to resolve its receipt from a different assignment.

For a completed assigned proof, save the exact requested declaration and use the ordinary typed proof delivery. A mathematicalGap report is not a substitute for delivering the two ready summability proofs. This clarification supplies no theorem, premise, proof acceptance or new assignment. Continue the existing mathematical work.
