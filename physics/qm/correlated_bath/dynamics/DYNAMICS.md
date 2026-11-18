# Correlated two-mode dynamics for the frozen three-slot source

## Event API for inference (C)

From this directory, or with it on `PYTHONPATH`, use

```python
from correlated_cq import event_probabilities, exact_blocks, events_from_blocks

p = event_probabilities(lam=.3, n=.5, c=.25, eta=.96, name="XY",
                        timing="changed_intervals")
blocks = exact_blocks(.3, .5, .25, timing="deployment")
all_settings = {name: events_from_blocks(blocks, .96, name)
                for name in ("XX", "XY", "YZ", "ZZ")}
```

Each vector is ordered `f-, f+, pf-, pf+, ppf-, ppf+, ppp-, ppp+`. Each cell is a joint probability per shot, including early failures. S is the first qubit. The default SR input is the normalized Bell state. `rho_sr=` accepts an arbitrary finite reference in the block API. The named Pauli tester uses a qubit reference. The optional timing argument takes `deployment` or `changed_intervals`; the latter swaps only durations 1 and 2. The fixed readout uses effects (I ± η O)/2 and observes the record exactly. The float API evaluates the infinite-source formula. In the (u,v,w) coordinates, w=λ², u=w(2n+1), v=wc. The covariance is specified at shot time zero.

## Result and quantifiers

Let S be a qubit, R any finite reference and E the two persistent oscillators. Start each shot in ρ_SR ⊗ σ_E. For either timing and every allowed λ,n,c, the normalized total-number Galerkin source with K=16 differs from the infinite source by at most **0.011677620430** in half the sum of the terminal SR trace norms. At K=13 the bound is **0.038466572543**. Each bound compares two channels evaluated at the same parameters. It includes the entire failure state in each record.

A separate integer implementation gives a physically valid rational CQ channel for specified rational parameters. At K=16 its worst-case error, including arithmetic and trace-preserving completion, is **0.027602916940** over the whole parameter box and both timings. At K=13 it is **0.049430334750**. The representation and bounds below also define the mathematical construction at real parameter values given exact arithmetic/comparisons. The runnable integer interface accepts rationals, including decimal or fractional strings. At (λ,n,c)=(0.3,0.5,0.25) its K=16 bounds tighten to **0.017009045852** for deployment and **0.017008956708** for the swap. These are deterministic bounds before readout. Applying the same detector is a channel contraction for every frozen η. An event computed from the rational map and rational η uses exact fractions.

## Initial state, clock and instrument

Units are ℏ=1. With Z=diag(1,−1), frequencies ω=(1,3/2) and relative couplings g=(1,3/5),
\[
 H=I\otimes H_E+\lambda Z\otimes\sum_k g_k(a_k+a_k^\dagger),\qquad
 H_E=\sum_k\omega_k a_k^\dagger a_k .
\]
The bath has zero mean, zero anomalous moments and shot-time-zero normal covariance \(N_{ij}=\langle a_i^\dagger a_j\rangle\), with diagonal n and off-diagonal c real. In normalized quadratures \(q=(a+a^\dagger)/\sqrt2,\ p=(a-a^\dagger)/(i\sqrt2)\), \([q,p]=i\), the symmetrized covariance in order (q₁,p₁,q₂,p₂) is
\[
 V=\begin{pmatrix}(n+1/2)I_2 & c I_2\\ c I_2 &(n+1/2)I_2\end{pmatrix}.
\]
The passive modes \((a_1\pm a_2)/\sqrt2\) carry independent normalized thermal states of mean \(n\pm c\). This includes a vacuum normal mode at either rank-one edge and the joint vacuum at n=0. Fix \(0\le n\le3/5,\ |c|\le n,\ 1/5\le\lambda\le2/5,\ 9/10\le\eta\le1\). Preparation phase is locked to the start of each shot. The different frequencies subsequently rotate the off-diagonal covariance.

After each joint slot, apply F=diag(√(1/8),1/2) on failure, or \(R_j P\) on pass, where P=diag(√(7/8),√(3/4)). The ordered rotations are \(R_y(\pi/2),R_x(\pi/3),I\), with \(R_a(t)=\exp(-it\sigma_a/2)\). Failure stops immediately. The two time orders are (2/3,3/4,1/2) and (3/4,2/3,1/2). The Kraus effects sum to identity, and the branch SR traces are the true prefix probabilities. In particular \(27/64\le p_{ppp}\le343/512\) by multiplying the conditional pass bounds. The computed deployment probabilities on the two Z inputs at the example point are 0.574747436923 and 0.492640660220.

## Infinite-bath formula

Use \(D(b)=\exp(\sum b_k a_k^\dagger-\bar b_k a_k)\). For a fixed sign z in a slot of length t, completing the oscillator square gives
\[
 U_z(t)=e^{i\phi_0(t)}D(z\xi(t))e^{-iH_Et},\quad
 \xi_k(t)=\lambda g_k(e^{-i\omega_kt}-1)/\omega_k,\quad
 \phi_0=\sum_k(\lambda g_k/\omega_k)^2(\omega_kt-\sin\omega_kt).
\]
The history is the chronological product with the last slot on the left. Start β=0 and φ=0. For each new slot set \(b_0=e^{-i\omega t}\beta,\ b_1=z\xi(t)\), then
\[
 \phi\gets\phi+\phi_0(t)+\operatorname{Im}\langle b_0,b_1\rangle,\qquad
 \beta\gets b_0+b_1,\qquad \langle b,c\rangle=\sum\bar b_k c_k .
\]
A pair of histories ending at the same prefix cancels the common \(\sum\phi_0\). Cyclicity in \(\mathrm{Tr}(U_h\sigma U_{h'}^\dagger)\) puts \(D(-\beta')D(\beta)\) in that order. With \(T\) the duration of the actual prefix,
\[
 d_k=e^{+i\omega_kT}(\beta_k-\beta'_k),\quad
 L_{hh'}=\exp\!\left(i[\phi-\phi'+\operatorname{Im}\langle\beta',\beta\rangle]
 -(n+\tfrac12)\|d\|^2-2c\,\operatorname{Re}(\bar d_1 d_2)\right).
\]
The positive rotation follows from conjugation by \(e^{+iH_ET}\) inside the initial-state trace. Equivalently a slot beginning at clock A contributes \(\lambda z(g_k/\omega_k)e^{i\omega_kA}(1-e^{i\omega_kt})\) in the interaction picture. Both representations retain the Weyl exchange phase. Using a final-frame displacement directly with the initial N changes the cross term for nonzero c. In the natural coordinates \(u=\lambda^2(2n+1), v=\lambda^2c, w=\lambda^2\), the unit-λ displacement supplies coefficients \(-u\|d^{\rm unit}\|_2^2/2-2v\,\mathrm{Re}(\bar d^{\rm unit}_{1}d^{\rm unit}_{2})+iw\Phi^{\rm unit}\), where the first squared norm sums both modes.

For a record y, let \(K_j\) be F or the designated pass Kraus operator. For sign history h form \(A_h=K_\ell\Pi_{h_\ell}\cdots K_1\Pi_{h_1}\). The terminal block is
\[
 B_y=\sum_{h,h'} L_{hh'}(A_h\otimes I_R)\rho_{SR}(A_{h'}^\dagger\otimes I_R).
\]
This follows by expanding only the conditional unitaries in their Z projectors and tracing E after stopping. It uses the Gaussian characteristic function once on the initial state. The finite history sum applies even when branch bath states after control have become non-Gaussian. For an effect \(O=\sigma_a\otimes\sigma_b\) the complete binary tester returns \((\mathrm{Tr} B_y\pm\eta\mathrm{Tr}(O B_y))/2\) with minus first.

## Total-number cutoff and propagated boundary

Let \(\Pi_s\) project on total occupation s and \(P_K=\sum_{s=0}^K\Pi_s\). Use \(H_K=P_K H P_K\), the same controls and the normalized state \(P_K\sigma P_K/\mathrm{Tr}(P_K\sigma)\). The embedding J identifies the triangular basis \(|i,s-i\rangle,\ 0\le i\le s\le K\) with its physical subspace. Bath dimension is \((K+1)(K+2)/2\). Free frequencies and forcing always act in the laboratory modes. The finite model requires a mathematical change of initial state only.

Write \(a=(n+c)/(1+n+c), b=(n-c)/(1+n-c)\). Probability in shell s is
\[
 p_s=(1-a)(1-b)\sum_{h=0}^s a^h b^{s-h}.
\]
The exact tail is \(a^{K+1}+(1-a)\sum_{i=0}^K a^i b^{K+1-i}\), valid also at \(a=b\) and at zero. The initial state commutes with total number. Splitting by s is therefore an actual convex decomposition, including the coherence within each shell. Sorting the two mean occupancies bounds the larger by 6/5 and the smaller by 3/5. Independent geometric variables with ratios \(a_*=6/11,\ b_*=3/8\) stochastically dominate the sum, by coupling each sorted mode to the same uniform random number as its dominator.

Purify SR and each normalized shell state. Store pass/fail coherently in orthogonal records, using fresh flags and an isometric extension of each instrument. After stopping allow free bath rotation to the common horizon with zero coupling. Tracing the final bath, purification and unused flags, and dephasing the record gives exactly the original CQ output. The finite and infinite controls intertwine J and preserve total occupation. In the free interaction picture the live control coefficient has norm at most one. The driving field maps shell j to j+1 with norm at most \(\lambda\|g\|_2\sqrt{j+1}\), and to j−1 with norm at most \(\lambda\|g\|_2\sqrt j\). This follows by a passive mode rotation for the instantaneous complex coupling vector; its norm stays fixed.

The only term in \(HJ-JH_K\) is creation out of the live top shell. Duhamel's formula gives an upper bound on the norm error for a unit vector initially on shell s of
\[
 \int_0^T\lambda\|g\|_2\sqrt{K+1}\;
       \|\Pi_K\,{\bf1}_{\rm live}\psi_K(t)\|\,dt .
\]
Squaring the norm in this integrand sums the **subnormalized** live prefix weights times their conditional top-shell probabilities. Branches do not acquire an independent unit weight. For a uniform upper bound we may drop the live projector. One can apply Duhamel separately between the finite number of interventions and telescope, since every flag isometry is a contraction. The embedded finite path is finite-support and in the domain of the exact forced oscillator; the unitary Duhamel integral is well-defined.

To bound the propagated shell norm, put \(x=\lambda\|g\|_2 T\le9/10\), using \(T=23/12\) and \(\|g\|_2^2=34/25\). Let \(A_{j+1,j}=A_{j,j+1}=\sqrt{j+1}\), all other entries zero. At time \(u=\lambda\|g\|_2t\), expand the finite interaction propagator in its convergent Dyson series. At each order, the norm of each path of intermediate shell indices is bounded by the product of the corresponding A entries; the simplex volume is \(u^h/h!\). Flag isometries introduce no bath steps. Thus the shell norm is bounded by \((e^{u A_K})_{K,s}\), where \(A_K\) is the finite restriction. All entries in each nonnegative power are at most the corresponding full-oscillator path sum. Normal ordering \(e^{u(a+a^\dagger)}=e^{u^2/2}e^{ua^\dagger}e^{ua}\) evaluates the latter coefficient for s≤K as
\[
 e^{u^2/2}\sqrt{K!/s!}
 \sum_{l=0}^s {s\choose l}\frac{u^{K-s+2l}}{(K-s+l)!}.
\]
For rigor the identity can first be read coefficientwise as a formal power series on number vectors. The displayed function is entire in u, so its absolutely convergent real series bounds every finite-cutoff power.

Integrate the boundary inequality, set \(d=K-s,\ x=9/10\), and use \(e^{x^2/2}\le1/(1-x^2/2)\). The shell-specific contribution to half trace distance is bounded by
\[
 f_s=\min\left(1,\frac{x^{d+1}\sqrt{(K+1)!/s!}}{1-x^2/2}
 \sum_{l=0}^s {s\choose l}\frac{x^{2l}}{(d+l)!(d+2l+1)}\right).
\]
For two unit purifications their trace distance is at most their vector distance, and the output channel contracts trace distance. The cap 1 follows for normalized states. Coupling the common shell masses of the true and normalized finite models costs at most \(\sum_{s\le K}p_s f_s+\Pr(s>K)\): the finite law contains each mass \(p_s\) and its remaining mass can be paired arbitrarily with the exact tail. Set \(h_s=\max_{j\le s} f_j\) through K and \(h_s=1\) above K. The total stochastic bound is
\[
 B_K=1-\sum_{s=0}^K (1-a_*)(1-b_*)\Big[\sum_{i=0}^s a_*^i b_*^{s-i}\Big](1-h_s).
\]
The function uniform_bound evaluates this using exact fractions and rounds each square root *upward* by integer square root at 12 decimal places. No finite solver comparison is used in obtaining \(B_K\). Examples of its outward values are 0.055985832631 at K=12, 0.025259114053 at K=14, 0.002098904698 at K=20 and 0.000357107093 at K=24. At K=20 the example deployment's direct CQ discrepancy exceeds its initial thermal tail, illustrating why the boundary integral is needed.

## Independent finite computations and arithmetic

The SciPy backend prepares the physical shell by diagonalizing \(a_1^\dagger a_2+a_2^\dagger a_1=N_+-N_-\). Its ordered eigenvalues are \(2h-s\). The square-root factors use exactly the thermal weights above, normalized over the retained shells. Sparse exponentials of the two physical \(H_\pm\) act on S-selected amplitudes, followed by the real instrument and rotations. Each failed vector is reduced on SR immediately. Mixed SR inputs use a spectral ensemble. The implementation of this computation in **fock.py** calls no Weyl-history code.

The bounded integer computation in **bounded_fock.py** implements the same Galerkin source on a normalized Bell input. It uses a dyadic lattice of mesh \(\delta=2^{-27}\), integer matrix products, and exact fractions. A returned normalized Choi specifies a channel on every SR input. The following bounds account for the entire numerical calculation.

1. For total shell s and plus occupation h expand \((a_1^\dagger+a_2^\dagger)^h(a_1^\dagger-a_2^\dagger)^{s-h}\). Let C be the coefficient of monomial \(x^iy^{s-i}\) in \((x+y)^h(x-y)^{s-h}\). The purification amplitude on \((i,s-i;h,s-h)\), per nonzero Bell component, is \(C\sqrt{w\,i!(s-i)!/[2^{s+1}h!(s-h)!]}\), with w its conditioned thermal weight. Signed integer square root rounds magnitudes down with error <δ. If D is the bath dimension, the initial vector error is at most \(2D\delta\).
2. For a slot choose the smallest nonnegative b with \(t(3K/2+K+1)/2^b\le1/4\). Indeed \(\|H_\pm\|\le3K/2+2\lambda\|g\|\sqrt K\). Form the real symmetric grid approximation X to \(tH_+/2^b\). At most five entries per row and column differ by at most δ, giving operator error \(5\delta\) and \(\|X\|<1/2\). Hermitian interpolation/Duhamel bounds the corresponding exponential error by \(5\delta\). Evaluate the degree-12 Taylor polynomial of \(-iX\) by Horner recurrence. The Taylor remainder for the anti-Hermitian exponential is at most \(2^{-13}/13!\), by its integral remainder. Each rounded matrix has Frobenius error at most \(2D\delta\) per product; contraction by \(\|X\|/j\) makes their sum at most \(4D\delta\). This gives the initial operator error e. Each squaring replaces e by \(2e+e^2+2D\delta\). Number parity gives the minus propagator by exact conjugation. Each update rounds its bound upward where needed.
3. Keep a common purified vector including all stopped flags. If E bounds its current error, an approximate slot of error e followed by grid rounding costs \(E\gets E+e(1+E)+3D\delta\). There are at most \(4D^2\) complex active amplitudes. The combined fail/pass isometry has at most six nonzero rounded entries of error <δ. Its two output vectors add at most \(4D\delta\) in Euclidean error. Hence update \(E\gets E+3\delta(1+E)+4D\delta\). Prefix norms already include their probabilities. Real/imaginary integer products check a conservative signed-64-bit bound before multiplication. Final Gram products use arbitrary-size integers. At K≤16 intermediate propagators stay within \(1+e\) of unit norm, and each purified prefix within \(1+E\); the implemented guard has ample range at the stated cutoffs.
4. Exactly divide the positive Gram blocks by their combined trace. The trace distance of the normalized whole vector to the true unit vector is the distance of the true vector to its projection on the computed line, at most E. Partial trace and record dephasing preserve the bound on Bell output. Let M be its exact reference marginal. It is trace one; hence \(\|M-I/2\|_\infty=D(M,I/2)\le E\). Take τ the smaller of E and a rational row-norm upper bound, and \(s=1/(1+2\tau)\). Multiply each Choi block by s, then add \(|0\rangle\langle0|\otimes(I/2-sM)\) to f. The residual is positive and the repaired marginal equals I/2. This specifies a completely positive trace-preserving map, with Bell repair error at most \(1-s\). Failure is retained in its entirety and this explicitly budgeted mass adjustment is purely numerical.
5. For an arbitrary pure SR input write \(|\psi\rangle=(I\otimes A)|\Phi_2\rangle\), with \(\|A\|_\infty\le\sqrt2\), and use convexity for mixtures. This bounds the worst-case complete distance of the computed map to the true finite map by \(2(E+1-s)\). Adding \(B_K\) gives the infinite-source bound. In particular \(s\ge1/(1+2E)\) yields the uniform numbers at the start of this note. At K=16, \(E\le0.002663625827\). The rational matrices and the tighter point-specific repair costs for both timings are saved in **observed.json**. Entry pairs are [real,imaginary] in S-output, input-reference order. For general input the contraction is \(B_{ar,bs}=2\sum_{ij}J_{ai,bj}\rho_{ir,js}\) for each record.

## Reproduction, costs and interpretation

For Linux or macOS, set **UEOT_UPSTREAM_REPO** to a Git checkout or bare repository containing the pinned commit below. Use Python 3.10+ with NumPy, SciPy and mpmath. From this directory run

~~~sh
export UEOT_UPSTREAM_REPO=/path/to/upstream/repository
python -B verify_dynamics.py --receipt dynamics-replay.json
python -B review_inference.py --receipt inference-review-replay.json
~~~

Each explicit receipt path must be new. Omitting the option runs all checks and prints the result. In a fresh staging directory it also creates the conventional receipt when that file is absent. The original macOS receipt **observed.json** has SHA-256 **82d4b1db3b1046f8c723a008fb5f6045f07f839c16474d8355e29f3f1b84fc30**. The original **review_observed.json** has SHA-256 **90056e31f6fcb72012b9d8216d36e447ef7d6523a5606b172a0b79a991a1df02**. Runtime and resource fields identify their own execution.

To obtain the finite event prediction directly, use

~~~python
from bounded_fock import certified_choi, rational_events

blocks, budget = certified_choi("3/10", "1/2", "1/4", 16, "changed_intervals")
p = rational_events(blocks, "24/25", "YZ")
assert sum(p) == 1
~~~

Forty Bell comparisons covered both orders, cutoffs 4,8,13,16,20, positive correlation, zero correlation and both singular thermal edges. The greatest observed \(D_{\rm CQ}\) among the eight timing/parameter combinations at each cutoff was respectively 0.026574, 0.003079, 0.000169, 0.00002773 and 0.000002416 (rounded upward). For deployment at (0.3,0.5,0.25), K=16 gave contributions \(9.559\times10^{-8},1.263\times10^{-7},1.125\times10^{-7},5.123\times10^{-7}\) from f,pf,ppf,ppp. A mixed qubit–qutrit input at K=13 gave \(1.128\times10^{-6}\). On the separate negative-frame check at (0.4,0.6,−0.45), the K=20 Fock discrepancy was \(4.37\times10^{-7}\) on deployment and \(4.35\times10^{-7}\) on the swap; omitting the preparation-frame rotation raised these to 0.011121 and 0.012128. The pinned Gaussian expression with the correct covariance agreed with the event API's full matrices to \(1.8\times10^{-16}\). These cross-checks used floating arithmetic. The proof and the integer certificates give the enclosures.

At K=16, D=153. SciPy stores at most order \(2\,\dim R\,D^2\) complex amplitudes per purified vector; the integer solver stores dense \(D\times D\) propagators and Bell purifications. The 40 comparisons and auxiliary checks completed in 4.73 s with peak process RSS 103,481,344 bytes on the recorded macOS run. Per-run times, package versions and unrounded diagnostic distances are in **observed.json**. Recording a Bell Choi channel eliminates any bath evolution at application time.

The stated channel errors cover thermal truncation, boundary propagation and, for the stored rational map, arithmetic/repair. They assume the Hamiltonian, bath preparation, clock, controls, detector law and specified parameters. Estimating these parameters from data, or bounding drift, loss and gate/model errors requires its own budget. A detector error \(|\Delta\eta|\) contributes at most \(|\Delta\eta|/2\) for a fixed binary tester. The direct-sum error is per input shot. For conditioned ppp, the triangle inequality and trace balance across other records give \(D_{\rm cond}\le D_{\rm CQ}/p_{ppp}\) whenever both probabilities are positive. No hardware trials enter this computation.

Historical definitions and vacuum comparison were read from Git object 44b6cd200cd01eccf15d4dc817311388d317a1af under physics/qm/persistent_bath, in SHARED_MODEL.json, model_contract.json, CALIBRATION_CONTRACT.json and dynamics.py. The last blob's SHA-256 is 3eb805d8ec9f8010583023f8a57812c759fba4fcc48c27c36a9079367f664001. The November 18 plan supplies the correlated initial state and parameter range. All new computations and receipts in this directory are separate from the historical data.
