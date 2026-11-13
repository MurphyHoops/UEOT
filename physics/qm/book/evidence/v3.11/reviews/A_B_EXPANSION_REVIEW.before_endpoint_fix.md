# A: narrow review of B's self-contained Chapter 70 expansion

Review date: 2026-11-14 (Asia/Shanghai). Reviewer: native agent A.

## Scope and verdict

Reviewed `CH70_B_expanded.zh.md` and `CH70_B_expanded.en.md` in
`work_publication_review/`, concentrating on the new Choi-to-all-input
proof, the term-by-term physical-repair cost, and the finite Duhamel
orientation. Compared those arguments to the already reviewed
`work_b/B_DYNAMICS_PROOF.md` and its operational scope. The final read-back
also inspected the corresponding integrated sections 70.5 and 70.6 of
both actual book sources.

**Final verdict: PASS_NARROW_MATHEMATICAL_AND_TEXTUAL_READBACK.** The expansion provides the missing
self-contained explanatory steps without strengthening the original
theorems beyond their premises. The two TeX escape defects identified by
the master are corrected in the expanded fragments, and the recommended
Hermitianization explanation is present in both integrated book sources.
No new test was run for this review and neither book was modified by A.

## 1. Choi errors control arbitrary untouched references

The new proof treats a unit rank-one operator `|u><v|` on the qubit and any
finite reference, rather than only a positive Bell state. Write

\[
|u\rangle=(I\otimes A)|\Omega_2\rangle,\qquad
|v\rangle=(I\otimes B)|\Omega_2\rangle,
\]

where `A,B:C^2 -> R` may be rectangular. If u and v are unit vectors,
their Hilbert–Schmidt norms are sqrt(2), so their operator norms are at
most sqrt(2). The norm of each output block therefore grows by at most
two relative to its normalized Choi block. Singular-value decomposition
and the triangle inequality extend this to every trace-class input,
with a factor equal to its input trace norm. The factor is independent
of reference dimension. Consequently

\[
\tfrac12\|\mathcal Q-\Phi\|_\diamond
\le(d_{\rm in}/2)\sum_h\|Q_h-J_h\|_1
=\sum_h\|Q_h-J_h\|_1
\]

for input dimension two. This is a proof of the all-input bound, not
numerical extrapolation from one Bell input. It remains valid even if
the raw represented map is not CP, since the estimate is linear and
uses arbitrary trace-class inputs.

The displayed Frobenius-to-trace bound has the correct factor two for
4-by-4 blocks. The stored numerical convention remains normalized
output-S tensor input/reference, consistent with B's exact rational
repair and A's earlier explicit SWAP-and-scale interface check.

One recommended explanatory sentence was sent to B: because the true
J is Hermitian, Hermitianization is an orthogonal projection for the
Frobenius norm and cannot enlarge the error relative to J. This makes
the raw-entry interval enclosure to the exact Hermitian rational Q
step explicit. It does not require another numerical certificate or
change the represented result. The sentence has now been read back in
both integrated book sources.

## 2. Physical repair cost is correct term by term

The expansion retains the actual hypotheses `e=sum_h||Q_h-J_h||_1`,
`e<10^-12`, `delta=10^-10`, and `a=(1+20delta)^-1`. Adding delta I4
to four blocks adds 8 delta I2 to their summed output partial trace.
The marginal defect is bounded by e, so the residual R is positive.
Adding `|0><0|_out tensor R` to the existing failure block establishes
exact TP, while preserving the label set.

With `s=sum_h tr(Q_h-J_h)` and `|s|<=e`, the derivation reads

\[
\begin{aligned}
\sum_h\|J_h^{rep}-J_h\|_1
&\le ae+(1-a)+16a\delta+\operatorname{tr}R,\\
\operatorname{tr}R&=1-a(1+s+16\delta),\\
\sum_h\|J_h^{rep}-J_h\|_1
&\le ae+2(1-a)-as\\
&\le2ae+40a\delta.
\end{aligned}
\]

Each equality and inequality is justified: positivity turns the
identity/repair terms into their traces, all true normalized Choi
blocks have total trace one, and `2(1-a)=40a delta`. The 16 a delta
terms cancel when the residual trace is substituted. The qubit
half-diamond lift contributes no additional factor. The resulting
`a(40delta+2e)<10^-8` is consistent with the original source proof.

The text correctly says this is a fixed-policy **terminal** instrument,
not a map proved implementable at the original early stopping times and
not a repaired process tensor for arbitrary interventions. It also
charges any later floating contraction separately. The conservative
additional d20 allowance is explicitly distinguished from truncation
already included in the pointwise interval certificate.

## 3. Duhamel orientation and finite support agree with the source proof

The interaction-picture formula

\[
W(T,0)=I-i\lambda\int_0^T W(T,s)\widetilde V(s)\,ds
\]

has the correct orientation: differentiation in the lower endpoint
gives `partial_s W(T,s)=i lambda W(T,s)V(s)`. Repeatedly expanding
the left suffix leaves the true unitary at the left of the finite
remainder. The field factors to its right act successively on a
vacuum-originating finite-support vector. The field's number-changing
bound is unchanged by the free picture and dilated system/record
operations, since those preserve bath number.

The first K terms therefore agree with the product-cutoff source, and
the two order-K+1 remainders are bounded separately by c_(K+1). Their
sum is 2 c_(K+1). The proof requires no infinite Dyson-series
convergence and does not apply a field to an uncontrolled true tail.
Purification and full record retention preserve arbitrary SR input;
discarding the bath and unused dilation registers contracts trace
distance. This is the same argument as the original B proof, now
written out with its decisive direction visible.

The boundary-prefix expression correctly includes the square root of
the actual prefix mass. It is kept separate from the uniform d_K
certificate. The parameter Duhamel argument separately uses the true
infinite-source energy bound before adding finite approximation
errors. These directions are not interchanged.

## 4. Editorial issues and final read-back

The master had already identified two malformed TeX fragments in the
expanded residual display: `Tr !left` and a corrupted live-history sum
subscript. They are text-escaping defects, not mathematical changes.
Both corrected expressions were read back as `\\operatorname{Tr}\\!\\left[`
and `\\sum_{h\\,\\mathrm{live}}`. The corrected fragment SHA256 identities are:

* Chinese: `6b562d7a52bf473f43738615380855c9f9ed813dc047731bb92b43e366c80e62`
* English: `576d5d82af1d45d7daa56cb89eafacf1bd162f4aba2e7bab8170cad93f0927bc`

The integrated sources additionally contain the exact-Hermitianization
sentence and equivalent gathered line breaks in the all-input bound.
Their final whole-file and section identities are recorded in
`A_CH70_FINAL_TEXT_CHECK.json`. The Duhamel direction, Choi norm factor,
repair cost and fixed-policy terminal scope remain unchanged. This review
does not claim to have rendered PDF page images.
