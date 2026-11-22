# Independent A review of the dynamic source calculation

The new inference result has been checked independently by B and C. A has
also reviewed B's tail construction and C's validated mode propagation,
and supplied a separate executable audit in `review_bc.py`.
The audit passes and its exact receipt is `review_bc.json`.

The substantive numerical conclusion is stronger than a small perturbation
diagnostic: in the explicitly specified Anderson--Eaker, mu=1 prescription
without an additional finite curvature term, the archived dynamic reference
has initial quantum density

\[
 \rho_{\mathrm q}(0)>0.65831423060
 \quad\text{using validated modes through }k=64,
\]
\[
 \rho_{\mathrm q}(0)>1.51016335437
 \quad\text{using the additional validated modes through }k=256.
\]

Both bounds include all larger modes. They are not cutoff estimates.
They exceed the density 1/2 required by the original intrinsic initial
geometry. This rejects that fixed background/reference/prescription
combination as an unaltered self-consistent initial data set. It does not
reject every finite curvature coupling or supply a replacement geometry.

## 1. What was inspected and executed

A read the full current `propagation/background.py`,
`propagation/finite_modes.py`, `propagation/extra_eta0.py`,
`stress/tail.py`, and `stress/assemble.py`, as well as the previous source
contract. The executable audit covers:

- A constant-background analytic oscillator step for k=2,17,64, with the
  full interval Taylor error retained. Every exact analytic result lies
  inside C's reported energy ball. Removing the Taylor remainder makes all
  three tests fail against the analytic error lower bound.
- Symbolic differentiation of the W2 construction, including the defect
  formula and the phase integration-by-parts coefficient.
- The finite unresolved mode-sum identity with complete k-squared
  degeneracy.
- An independent eta=0 assembly and infinite-tail bound. This implementation
  does **not** call B's `assemble`, `cut_stress`, `local_tail`, or
  `analytic` functions.

The current B assembly receipt also passed an actual read-only
`stress/assemble.py --check` replay after the tail receipts were refreshed.

The last audit uses C's exact rational mode enclosures and B's exact rational
preparation-integral bounds. Their hashes, and the relevant source hashes,
are recorded. This is an independent audit of the stated finite and tail
certificates, not a second independent construction of the quantum state.

Run:

```sh
/Users/murphyhoops/Documents/ueot-physics-closure-20261111/.physics-venv/bin/python \
  /Users/murphyhoops/Documents/ueot-physics-continuation-20261119/physics/qm/null_source/timelike/evolution/inference/review_bc.py --check
```

No full high-mode propagation is repeated by this audit. Its static exact
test and symbolic calculations address distinct risks in the certificate.

## 2. C: smooth preparation and validated finite modes

### Endpoint preparation caps

For the smooth switch, set
\(z=\exp[-1/x+1/(1-x)]\), \(S=z/(1+z)\).
Each order-n Bell monomial in the derivatives of z has an x-pole of order
at most 2n. On a cap with \(2n\varepsilon\le1\),
\(x^{-m}e^{-1/x}\) increases for every \(m\le2n\), and the remaining
\((1-x)^{-j}\) factors increase as well. Evaluating positive majorants at
the cap endpoint therefore bounds the entire cap, not just a sample.
The inverse-series recurrence uses \(1+z\ge1\); the right-cap formula
uses the reflection identity for S. The conversion from x derivatives to
eta derivatives correctly contributes the factor 16 to each order.

The script enforces the monotonicity condition. A directly tested invalid
case, order 33 at epsilon=1/64, is rejected. This condition cannot be dropped
when extending the Taylor order.

### Energy norm and the local remainder

For \(\omega=\sqrt{k^2-1}\), C propagates

\[
 u'=p/a^2,\qquad p'=-\omega^2a^2u,
 \qquad
 N^2=\omega a^2|u|^2+\frac{|p|^2}{\omega a^2}.
\]

Direct differentiation yields \(|(\log N)'|\le|a'/a|\).
The same bound applies to an initial uncertainty ball because the equations
are linear. The interval bound on a and its derivatives supplies derivative
bounds throughout a cell. C's scaled recurrence generates the thirteenth
Taylor coefficient for the degree-12 approximation; its norm supplies the
Taylor remainder.

The update correctly adds three contributions: propagated incoming
uncertainty, the local Taylor remainder multiplied by the actual center's
initial norm, and the directed interval recentering error. The center is
only a nominal number. The proof does not depend on it being exact.

The energy quadratic form has operator norm omega in this norm. The pressure
quadratic form has signed eigenvalues omega and -omega/3, so its absolute
operator norm is also at most omega. Consequently the common bound

\[
 |\Delta e|,|\Delta s|\le
 \omega(2N\mathcal E+\mathcal E^2)
\]

is valid for an error radius \(\mathcal E\). C's mode-to-stress conversion
uses this bound and retains the full degeneracy.

The additional eta=0 computation for k=65..256 uses the same certified
propagator, changes only its declared endpoint list in the process, and
checks a summed stress error. The assembly checks that combining both
finite receipts gives every k=2..256 exactly once.

## 3. B: W2 defect and the infinite tail

Write \(\delta=k^{-2}\), \(A=1+q\delta\), and

\[
 T=-\frac{q''}{4A}
   +\frac{5\delta(q')^2}{16A^2},\qquad
 B=A+\delta^2T,\qquad W_2=k\sqrt B.
\]

A independently differentiated T twice and verified B's T1 and T2
expressions. Substituting the normalized WKB mode into its exact mode
equation gives \(R=\delta^2R_n\), matching B's normalized defect
identically as a rational function.

After removal of the diagonal mixing term, the phase derivative is
\(\varphi'=W_2+R/(2W_2)\). With \(c_b=R/(2W_2)\),

\[
 \frac{c_b}{2\varphi'}
 =k^{-6}\frac{R_n}{4B+2\delta^3R_n}.
\]

This is the coefficient used in B's integration-by-parts improvement.
The initial boundary term vanishes because the same W2 mode is exactly
matched to the original static vacuum. Positivity of the phase denominator
must hold across preparation for the improved estimate; B retains the
non-improved bound otherwise.

The absolute mixing estimate has k^-5 decay, and the phase estimate has
k^-6 decay. Multiplying by k-squared degeneracy gives the stated summation
powers. The density cross term has an additional cancellation of its
leading k term; pressure does not have this cancellation. The resulting
pressure bound can therefore be much wider without invalidating the
density lower bound.

For a density lower bound, the diagonal contribution
\(2|\beta|^2e_{W2}\) is nonnegative and may be dropped. The negative
cross term and the local W2 subtraction remainder must still be retained.
They are retained in the audit.

### The intermediate band is not discarded

At eta=0 the subtraction coefficients are \(E_1=-1/2,E_3=3/8\).
The canonical Wronskian gives

\[
 e_k=|v'_k-hv_k|^2+(k^2-1)|v_k|^2\ge\sqrt{k^2-1}.
\]

This follows from AM--GM and
\(|\operatorname{Im}(v_k^*(v'_k-hv_k))|=1/2\), independently of the
prepared state's excitation.

With

\[
 r_{\mathrm{static}}(k)
 =k^2\sqrt{k^2-1}-k^3+k/2+1/(8k),
\]

the full degeneracy-weighted lower summand is
\(r_{\mathrm{static}}(k)-1/(2k)\).
The binomial tail begins with \(-1/(16k^3)\); subsequent positive
coefficient ratios are \((j-1/2)/(j+1)<1\). Thus

\[
 \sum_{k=K+1}^{J}k^2(e_k-d_k)
 \ge
 -\frac{1}{32K^2[1-(K+1)^{-2}]}
 -\frac12\log(J/K).
\]

The whole band K<k<=J is included. For k>J the independently certified W2
tail is used. The preparation constants certified for k>=257 remain valid
when J>=256 because the inverse-frequency domain is only restricted.

### The regular zero mode and local addition

The k=1 mode is the declared Gaussian, not an oscillator vacuum.
Its raw energy and raw pressure are both \(1/(2c)\) in the mode-sum
normalization. At eta=0 its energy summand after the single k=1 subtraction
is -3/8. The assembly subtracts that k=1 term exactly once, then adds the
same Anderson--Eaker local correction.

The independent eta=0 audit uses

\[
 L=\log(3/4)+2\gamma,\qquad
 \rho_{\mathrm{an}}(0)=\frac{58+45L}{8640\pi^2}.
\]

It specializes the tail directly to
\(A=1+\delta\),
\(B=A-2\delta^2/A\), and
\(R_n=(16-2\delta)/(A^2B)\), rather than calling B's generic routine.
This reproduces the complete lower bounds.

| Validated finite cutoff K | Finite rho lower | Band to J=3072 lower | Tail beyond J lower | Full rho lower |
|---:|---:|---:|---:|---:|
| 64 | 0.6639334337489057 | -0.005447725207600 | -0.000171477940006 | 0.6583142306013002 |
| 256 | 1.5138316903699174 | -0.003496858050363 | -0.000171477940006 | 1.5101633543795492 |

Table values are rounded diagnostics; the rational endpoints in
`review_bc.json` are the authoritative inequalities. Both strict decimal
bounds at the top of this review have been rounded downward.

## 4. Physical interpretation and remaining obligations

The original intrinsic initial geometry has a=sqrt(3), Kij=0. Its
Hamiltonian constraint requires total density 1/2 in the project's units.
The fixed-prescription quantum reference alone exceeds that value.
Keeping the original nonnegative classical scalar contribution cannot
repair this constraint. Consequently this particular prepared state cannot
be inserted into the unchanged original initial geometry with all the
declared finite couplings fixed as above.

This conclusion is tied to the prescription and the finite gravity
couplings. At eta=0, \((H_1)_\rho=6\), so a freely changed stress-side
alpha changes the density constraint by 6 alpha. A single density value
cannot rule out that freedom. Choosing an alpha to cancel one constraint
does not construct a self-consistent nonlinear geometry or prove that the
first-order expansion is accurate.

Also \((H_1)_E=-18\) at eta=0. The combination E+3 rho cancels this
curvature term, but nine-mode and stiff contributions are still proportional
there. Moreover Rnn contains acceleration; it is not an additional datum
fixed by the intrinsic pair (a,Kij). The original classical acceleration
must not be imposed as a second initial constraint without new data.

This explains the purpose of A's complete-window relation. With the original
total coherent-source second moment M2=27 and regular zero-mode covariance
retained, u is calibrated: two density readings in the original nominal
supports suffice, with certified epsilon error gain below 9.352409.
If the combined stiff calibration is unknown, three independent geometry
contractions fit epsilon,u,alpha and a fourth supplies a held-out check.
A bounded u uncertainty can also be propagated in the two-reading design.

The coherent-source energy uses M2=E[P^2], not E[P]^2. For the old
Y=s/2+X mixture with E[X^2]=3/4, M2=27 even though the squared mean is 27/4.
A new mean-field readout determines only E[P]; it cannot determine the
zero-mode covariance from u when the displacement variance is unknown.

Both inference contracts remain conditional on additional geometry
measurements and an adequate dynamic reference across the complete windows.
They neither fix the coupling by decree nor treat the existing
field-characteristic readouts as geometry data.

The current point enclosures do not give the required full-window reference
integrals. Wide pressure enclosures, actual geometry apparatus error,
apparatus stress, and finite-coupling evolution remain open. The new
calculation establishes an initial-data incompatibility in a declared
prescription and a useful observable relation for a future corrected
calculation; it does not provide a completed semiclassical spacetime.
