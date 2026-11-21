# Independent review of the infinite-field energy lower bound

This review checks the mathematical assembly in [tail.py](../stress/tail.py) and [assemble.py](../stress/assemble.py). It does not replace their directed UV integration receipts. The finite-mode input is independently supplied by this directory.

## 1. Wronskian, degeneracy, zero mode, and analytic addition

At \(\eta=0\), \(a=\sqrt3\), \(h=0\), \(q=1\), \(q'=0\), and \(q''=8\). The exact nonzero-mode normalization is

\[
 v_kv_k^{*\prime}-v_k^*v_k'=i.
\]

It implies \(|v_k||v_k'|\geq1/2\), so

\[
 e_k=|v_k'|^2+(k^2-1)|v_k|^2\geq\sqrt{k^2-1}=\omega_k.
\]

This holds for the exact evolved reference mode, with no adiabatic approximation. The spectral multiplicity is \(k^2\), and the energy-density prefactor at this point is \(1/(36\pi^2)\).

The inverse-frequency subtraction has

\[
 d_k=k-\frac1{2k}+\frac3{8k^3}.
\]

For the regular homogeneous Gaussian, the raw coefficient is \(e_0=1/2\). Its raw density is \(1/(72\pi^2)=3/(8\pi^2a^6)\). The \(k=1\) subtraction is still \(d_1=7/8\) and must occur exactly once.

Independently substituting \(a'=0\), \(a''=-2\sqrt3\) into Anderson–Eaker gives \({}^{(1)}H^0{}_0=6\), \({}^{(3)}H^0{}_0=1/3\). Their equation 12a therefore reduces to

\[
 \rho_{\rm an}(0)=\frac{58+45L}{8640\pi^2},
 \qquad L=\log(3/4)+2\gamma.
\]

Combining the raw zero mode, its one subtraction, and this analytic addition yields

\[
 \rho_{\rm zero-sub+an}(0)=
 \frac{-32+45L}{8640\pi^2}.
\]

The assembly uses these values. In particular, its positive finite-mode result does not arise from omitting the homogeneous subtraction or from treating the analytic addition alone as the complete stress tensor.

## 2. A controlled middle-frequency interval

For \(K<k\leq J\), the Wronskian bound gives

\[
 k^2(e_k-d_k)\geq r_{\rm stat}(k)-\frac1{2k},
 \quad
 r_{\rm stat}(k)=k^2\sqrt{k^2-1}-k^3+\frac k2+\frac1{8k}.
\]

For \(0<x<1\),

\[
 \sqrt{1-x}=1-\frac x2-\frac{x^2}{8}
             -\sum_{n\geq3}c_nx^n,\qquad
 c_3=\frac1{16},\quad
 \frac{c_{n+1}}{c_n}=\frac{2n-1}{2n+2}<1.
\]

Consequently,

\[
 r_{\rm stat}(k)\geq-\frac1{16k^3(1-k^{-2})}.
\]

Using decreasing-function integral bounds,

\[
 \sum_{k=K+1}^J\frac1k\leq\log(J/K),\qquad
 \sum_{k=K+1}^J\frac1{k^3}\leq\frac1{2K^2},
\]

gives the exact middle-band lower bound used by the code:

\[
 \rho_{K<k\leq J}\geq
 -\frac1{36\pi^2}
 \left[
 \frac12\log(J/K)+
 \frac1{32K^2[1-(K+1)^{-2}]}
 \right].
\]

No intermediate frequency is silently discarded.

## 3. The far-tail factors

The reviewed approximate mode is \(w=(2W)^{-1/2}e^{-i\int W}\), with

\[
 s=k^2+q,\quad
 t=-\frac{q''}{4s}+\frac{5q'^2}{16s^2},\quad
 W^2=s+t.
\]

Its residual \(w''+(k^2+q)w=Rw\) is

\[
 R=\frac{q''t}{4s(s+t)}-\frac{t''}{4(s+t)}
 +\frac5{16}\left[
 \frac{2q't'+t'^2}{(s+t)^2}
 -\frac{q'^2t(2s+t)}{s^2(s+t)^2}
 \right].
\]

The implementation's normalized formulas for \(T,T',T''\) reproduce this identity. At the static starting endpoint, all derivatives of q vanish and \(W=\omega_k\), so this reference matches the exact mode and its derivative.

Writing the exact mode as \(v=\alpha w+\beta w^*\), with the variation-of-constants condition, gives \(|\alpha|^2-|\beta|^2=1\). After the diagonal phase is removed, the off-diagonal magnitude is \(|R/(2W)|\), and the oscillatory phase satisfies

\[
 \phi'=W+\frac{R}{2W}.
\]

With \(\delta=k^{-2}\), \(W^2=k^2B\), \(R=k^{-4}R_n\),

\[
 \frac{R/(2W)}{2\phi'}=
 k^{-6}\frac{R_n}{4B+2\delta^3R_n}.
\]

This is the H function used for integration by parts. Its endpoint, derivative-integral, and remaining nonlinear terms have the powers used in beta6 and N11. The integration-by-parts candidate is used only after the phase denominator has been enclosed away from zero on the whole path; otherwise the nonoscillatory estimate remains available.

The energy difference decomposes as

\[
 e(v)-e(w)=2|\beta|^2e(w)
       +2\operatorname{Re}\{\alpha\beta^* C\},
 \qquad
 C=(w'-hw)^2+(k^2-1)w^2.
\]

The first term is nonnegative and can be omitted for a lower bound. If \(g=h+W'/(2W)\), then

\[
 2|C|\leq2|g|+
 \frac{g^2+|q+1|+|t|}{W}.
\]

The factor two from the cross term is thus already included in the implementation's Rconst/Rinv bounds. After multiplication by \(k^2\), an \(|\alpha\beta|\leq A/k^r\) bound sums to the denominators \((r-3)J^{r-3}\) and \((r-2)J^{r-2}\) appearing in rho_negative. At the time-symmetric point \(g=0\), the constant part vanishes, strengthening this energy lower bound.

The local WKB-minus-subtraction remainder is separately enclosed by the third Taylor coefficient in \(\delta\); multiplying by the degeneracy leaves a \(k^{-3}\) sum bounded by \(1/(2J^2)\). It is retained in the negative tail bound.

A UV anchor computed uniformly for all \(k>K_{\rm anchor}\) can be reused at a larger splice \(J\geq K_{\rm anchor}\): its inverse-frequency domain contains the smaller domain for all \(k>J\). The selected lower bound therefore covers the entire infinite field.

## 4. Meaning of the resulting constraint test

The verdict concerns the archived reference state, the stated regular zero mode, the given initial geometry and curvature, \(\hbar=1\), the Anderson–Eaker prescription with \(\mu=1\), and no added finite curvature counterterms.

If this full quantum density alone exceeds \(1/2\), it already exceeds the total density allowed by the original time-symmetric initial Hamiltonian constraint. Adding a classical minimally coupled homogeneous scalar with nonnegative kinetic energy cannot restore that same constraint. This rejects the unchanged initial geometry and matter assignment in this fixed prescription.

It does not prove a scheme-independent obstruction, solve the modified semiclassical initial-value problem, or certify a new geometry. It also does not turn the coarse pressure enclosures into precise finite-window baseline data.

## Primary reference

[Anderson and Eaker, gr-qc/9906055](https://arxiv.org/pdf/gr-qc/9906055), equations 5–12, for the mode normalization, spectral measure, inverse-frequency subtraction, and analytic addition. The positivity, middle-band estimate, and residual/Bogoliubov algebra above are rederived here for the declared model.
