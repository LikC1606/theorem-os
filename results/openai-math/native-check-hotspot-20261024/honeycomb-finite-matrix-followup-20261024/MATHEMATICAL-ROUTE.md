# Finite nonnegative Green series: direct first-moment reduction

The proposed finite-matrix implication is mathematically valid. A shorter proof uses the Cauchy product and does not build a trimmed matrix or prove a uniform spectral contraction. The candidate Lean file is checked separately; its precise verification status is recorded in README and the actual validation receipts, not inferred from this argument.

For a finite state set I, suppose L_a(i), R_b(i) are nonnegative and c_(a+b) = sum_i L_a(i) R_b(i). Assume sum_n c_n converges. Each product L_a(i) R_b(i) is bounded by c_(a+b). If L_.(i) or R_.(i) is identically zero, that state contributes zero. Otherwise choose positive witnesses L_a(i)>0 and R_b(i)>0. The estimates L_n(i)R_b(i) <= c_(n+b) and L_a(i)R_n(i) <= c_(a+n) prove both scalar half-series summable. Their nonnegative Cauchy product is summable. Summing over the finite state set yields

    sum_i sum_(a+b=n) L_a(i)R_b(i) = (n+1)c_n.

Subtracting the original summable c_n gives summability of n*c_n. For A entrywise nonnegative and u,v nonnegative, take L_a = u^T A^a and R_b = A^b v. The factorization follows from A^(a+b)=A^a A^b. This handles an empty state set and invisible states directly.

The stronger untrimmed inference “a single scalar Green series converges, hence every matrix-entry Green series converges” is false. For A=diag(1/2,2), u=v=(1,0), c_n=(1/2)^n has sum 2, while (A^n)_(2,2)=2^n has divergent sum. The direct theorem above never needs that false inference. A trimming proof would need both reachability from u and coaccessibility to v, followed by an exact path-preservation result for the restricted matrix.

# Exact connection still needed for HoneycombBridgeFiniteness

The canonical source defines firstLengthWeight p = (p.vertices.length : Real)*weight p. Its accepted bridgeFiniteBridgeSums_of_firstLengthWeight already reduces the six original clauses to this first-length summability for every h>=1. The four previously checked finite-box lemmas provide only Summable weight, conditional on a bound K_h uniform in box radius; this follow-up does not duplicate those lemmas or establish K_h.

For each fixed h, an exact finite transfer model should produce nonnegative A,u,v and a span function k(p), with c_k=u^T A^k v equal to the sum of the weights of exactly the original anchored BridgePath h paths with span k. The origin mark, unique terminal mark, cut connectivity, absence of cycles and empty padding, and exact vertex weighting all remain essential. A fixed finite shift in the indexing can be handled, but it must be stated. An unbounded encoding multiplicity or arbitrary extra accepted walks cannot be ignored: it can break the inference from actual bridge mass to summability of c_k.

If that exact model and the finite-box mass input are supplied, zeroth-mass summability gives summable c_k. The finite-matrix theorem gives summable k*c_k. A checked inequality vertices.length <= 2*h*k(p), obtained from an exact scan of the k occupied two-column slabs and Nodup, then bounds every finite bridge-family first-length sum by 2*h*sum_k k*c_k. Applying summable_of_sum_le closes firstLengthWeight summability. The endpoint vector normalization must match weight=alpha^(vertices.length); no K_h=1 claim is needed.

Thus the genuinely missing original mathematics remains: (1) a uniform finite-box bound for each fixed h, and (2) an exact finite transfer encoding together with its span/length bound. This follow-up aims to discharge the reusable finite-matrix analysis once those inputs are available. It does not prove an unconditional bridge theorem or the strict strip-growth interface.

# Evidence status

E: canonical source 96e89fbc7f26408eaaab99235481d1dd64ffcc1c, saved as canonical-Submission.lean, defines the weighted first moment and contains bridgeFiniteBridgeSums_of_firstLengthWeight.
E: pinned Mathlib Data/Matrix/Mul.lean contains pow_apply_nonneg, dotProduct_mulVec and mulVec_mulVec.
E: pinned Mathlib Topology/Algebra/InfiniteSum/Ring.lean:221 provides summable_sum_mul_antidiagonal_of_summable_mul.
E: pinned Mathlib Analysis/Normed/Ring/InfiniteSum.lean:34 provides Summable.mul_of_nonneg.
I: the Cauchy-product argument and diagonal counterexample are deductions from these definitions and elementary algebra, independently elaborated in the candidate Lean proof where stated.
?: the uniform finite-box bound, exact honeycomb transfer encoding and span/length bound have not been established here.

Research mode: Light, local_only. The canonical source, public RESEARCH.md and pinned library theorem bodies were read. The older public research notes carry stale assignment/source claims, so current canonical source and host checkpoint identities take precedence. No publisher solution, ProducedSolution, hidden model reasoning, online search or new dependencies were used.
