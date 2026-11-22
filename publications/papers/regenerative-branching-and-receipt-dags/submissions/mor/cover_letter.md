# Cover Letter — Submission to *Mathematics of Operations Research*

Dear Editor-in-Chief and Area Editors of *Mathematics of Operations Research*,

Please consider the enclosed manuscript, **"Prepayment Thresholds, Informative Zero Receipts, and Certified Polynomial Decision Diagrams in Partially Observed Regenerative Maintenance,"** for publication as an original research article in *Mathematics of Operations Research*.

Sequential maintenance and standby dispatch in regenerative stochastic systems sit at the junction of several classic themes in *Mathematics of Operations Research*—including controlled branching processes (Rothblum and Whittle, *MOR* 1982), the computational complexity of partially observed Markov decision processes (Papadimitriou and Tsitsiklis, *MOR* 1987), constrained dynamic programming (Feinberg, *MOR* 2000), and optimal maintenance under partial observation (Makis and Jiang, *MOR* 2003). In physical escrow, autonomous systems, and biological maintenance, however, three realistic constraints interact simultaneously: (i) operating reliability $r_\theta$ is drawn once from a prior $\pi_0$ and persists across the entire horizon; (ii) active repair spawns a healthy standby unit (`child1`) but requires *hard sample-path prepayment* $B_t \ge c$ prior to observing uncertain fault outcomes; and (iii) the controller observes *only* coarse two-bit post-transaction receipts $o_t = (\mathrm{birth}_t, \mathrm{paid}_t) \in \{0,1\}^2$ hiding the growing underlying genealogical population.

Combining self-contained stochastic dynamic programming proofs (Appendix A.1–A.6) with a pure-kernel Lean 4 formalization (`0` incomplete proofs, `0` compiler-trust evaluation axioms), this article establishes six main results:
1. **Native-to-compressed commutation and full-history Bayes optimality (Theorem 1):** Exact step-by-step commutation between the unbounded native genealogical store and a belief–wallet dynamic program achieving pathwise prepayment safety and exact Bayes optimality over all real-randomized history strategies.
2. **Closed-form high-price continuation and sharp thresholds (Theorem 2):** Explicit two-body zero-write continuation polynomials $U_1, U_2$ and the closed-form Bayes value $V_{H+1}^* = \max\{0, \mathbb{E}[r_\theta(1 - p + d\,U_2(r_\theta, d, H))]\}$ whenever $B_0 = c$ and $p \ge S_H(d)$, with necessary-and-sufficient positivity threshold $p < 1 + d M_H / \mu_1$.
3. **Asymmetric value of persistence, body feedback, and parameter revelation (Theorem 3):** Exact persistence variance premium $d\,\mathrm{Var}(r_\theta)$, strict post-fault retry threshold contraction ($21/16 \to 5/4$), strictly positive four-step receipt-feedback gain $d^3\mathbb{E}[r_\theta^3(1 - r_\theta)]$, yet *exact zero* post-repair expected value of perfect information on $\theta$ ($\mathrm{EVPI}_{\mathrm{post}} = 0$).
4. **Informative zero-receipt filtering and universal counting posteriors (Theorem 4):** Separation of informative fault zero receipts from deterministic damaged-idle / absent-slot zero receipts, proving exact cancellation of policy randomization factors across *all* real-randomized policies.
5. **Five-coordinate joint sufficiency and sharpness separations (Theorem 5):** Proof that $\sigma = (t, q, s, f, k)$ preserves all-action single-step joint laws and Bellman values, paired with reachable witnesses proving physical-Markov insufficiency ($5/8 \neq 1/2$), genealogy-erasing history mergers, and menu-relativity at slot $2$.
6. **All-action certifying decision diagrams and $24(H+1)^4$ node ceiling (Theorem 6):** Soundness of an executable rational certificate checker rejecting omitted unselected-action branches and compressing $28^8 \approx 3.78 \times 10^{11}$ eight-step branches into $1,661$ certified nodes ($151$ execution nodes) with exact value $884450457 / 1342177280$.

In strict compliance with INFORMS *Mathematics of Operations Research* double-anonymous guidelines, `mor_blinded_manuscript.pdf` contains zero author identifiers in text, headers, declarations, or PDF metadata, features a single-paragraph 182-word equation-free and citation-free abstract, 5 keywords, and explicit MSC 2020 and OR/MS subject classifications, accompanied by `mor_title_page.pdf`.

This work is original, independent, and not under consideration elsewhere. Thank you for your consideration.

Sincerely,

Degui Qian  
Independent Researcher
