# AO. Smooth outgoing preparation and the still-active finite-slice obstruction

## AO1. Same local candidate, explicitly free comparison

Use three conformal free fields on unit ESU, their common Fock vacuum
\(\Omega\), and the normal-ordered free total energy \(H_0\).
For each actual constituent cutoff \(K\), Wick order with respect to that
same vacuum. Consider the first-Dyson vector
\[
 \Phi_{1,K}(T)=-i\int_{-\infty}^T f(t)
 \left[g\int\chi_K\phi_K\psi_K\,dV+
       \frac{\lambda}{4}\int:
       (\chi_K^2+\phi_K^2+\psi_K^2)^2:\,dV\right](t)\Omega\,dt .       \tag{AO.1}
\]
The overall expansion parameter would multiply this entire interaction.
The two fixed couplings in the example remain \(g=\lambda=1/10\).

This is the free first-order comparison of the AL/AM polynomial candidate.
It is not the AB--AF global apparatus, and its record calibration does not
transfer. No complete time-dependent interacting Hamiltonian limit or
higher-Dyson remainder is asserted. For a stable switching comparison the
example below has \(f\ge0\) and an overall nonnegative expansion parameter;
arbitrary negative quartic switches do not inherit AM's semiboundedness.

## AO2. Exact three- and four-particle spectral weights

Let \(C(q,z)=q/(1-2qz+q^2)=\sum_{k\ge1}q^kU_{k-1}(z)\).
Character multiplication and normalized \(S^3\)/SU(2) Haar orthogonality give
\[
 \langle C^3\rangle=\frac{q^3}{(1-q^2)^3},\qquad
 \langle C^4\rangle=\frac{q^4(1+q^2)}{(1-q^2)^5}.             \tag{AO.2}
\]
For the second identity, expand
\(C^2=\sum_{\ell\ge0}(\ell+1)q^{\ell+2}U_\ell/(1-q^2)\)
and sum the squared coefficients. Thus the cubic odd-\(n\) coefficient
is \((n^2-1)/8\); the quartic even-\(n\) coefficient is
\(n^2(n^2-4)/192\).

For \(d\) independent components,
\(\langle:(\sum_A\varphi_A^2)^2:(x):
          (\sum_A\varphi_A^2)^2:(y)\rangle
 =8d(d+2)W_0(x,y)^4\).
At \(d=3\) this factor is \(120\). Including the two spatial volumes,
the propagator normalization \(W_0=C/(2V_0)\), and \((\lambda/4)^2\),
one obtains, with \(F_T(n)=\int_{-\infty}^T f(t)e^{int}dt\),
\[
 \boxed{
 \|\Phi_1(T)\|^2
 =\frac{g^2}{64V_0}\sum_{\substack{n\ge3\\ n\ {\rm odd}}}
            (n^2-1)|F_T(n)|^2
 +\frac{5\lambda^2}{2048V_0^2}
       \sum_{\substack{n\ge4\\ n\ {\rm even}}}
            n^2(n^2-4)|F_T(n)|^2 .}                         \tag{AO.3}
\]
This equality defines a Hilbert vector only when the sums converge.
The three- and four-particle sectors are orthogonal, so there is no
cross term that could cancel the quartic tail.

## AO3. Complete smooth switch: actual graph convergence and a normal comparison state

For a complete \(f\in C_c^\infty(\mathbb R)\) switch, ending after its
support, \(F_T=\widehat f\). All sums remain finite after inserting
\(n^{2p}\), for every \(p\ge0\). The cutoff vector is exactly the projection
of the full three/four-particle vector onto configurations whose every
constituent frequency is at most \(K\).

Every cubic total frequency \(n\le K+2\), and every quartic \(n\le K+3\),
is fully included. For instance, if four positive constituent frequencies
sum to \(n\le K+3\), each is at most \(n-3\le K\).
These projections commute with \(H_0\). It follows that
\[
 \Phi_{1,K}\longrightarrow\Phi_1
       \quad\text{in every }D((1+H_0)^p)\text{ graph norm}.   \tag{AO.4}
\]
This concerns the free \(H_0\), not an interacting Hamiltonian.

There is a quantitative actual-cutoff tail. Put
\(L_N=\|f^{(N)}\|_1\), \(N>p+5/2\), and
\(C_4=5\lambda^2/(2048V_0^2)\).
Bounding the omitted sectors by all frequencies above the fully included
range, the squared \(H_0^p\) error is at most
\[
 \frac{g^2L_N^2}{64V_0}
       \frac{(K+2)^{2p+3-2N}}{2N-2p-3}
 +C_4L_N^2
       \frac{(K+3)^{2p+5-2N}}{2N-2p-5}.                    \tag{AO.5}
\]
This is a first-vector cutoff error, not an interacting approximation error.

Because \(\Phi_1\) is orthogonal to the vacuum, the comparison state
\[
 \Xi_\epsilon=
 \frac{\Omega+\epsilon\Phi_1}
      {\sqrt{1+\epsilon^2\|\Phi_1\|^2}}                     \tag{AO.6}
\]
is an exactly normalized positive normal free-field state.
Its normalized actual cutoffs converge in the same free graph norms, and
\[
 \langle H_0^j\rangle_{\Xi_\epsilon}
 =\frac{\epsilon^2\langle\Phi_1,H_0^j\Phi_1\rangle}
        {1+\epsilon^2\|\Phi_1\|^2}<\infty\quad(j>0).
\]
Its half trace distance from the vacuum is exactly
\[
 D_{\rm half}(\Xi_\epsilon,\Omega)
 =\frac{|\epsilon|\|\Phi_1\|}
         {\sqrt{1+\epsilon^2\|\Phi_1\|^2}}.
\]
The fixed finite particle numbers and all free energy graph moments give
smooth particle wavefunctions on the compact slices; free
Klein--Gordon propagation preserves this smoothness. Their two-point
difference from the vacuum is smooth, so (AO.6) is Hadamard for the free
fields. This is a constructed comparison state. Normalizing the vector
does not prove it is the output of the claimed interacting preparation,
or prove any \(O(\epsilon^2)\) approximation remainder.

## AO4. A still-active endpoint has a different answer

Suppose the switching function is smooth with all past endpoint jets zero,
but the selected finite slice has \(f(T)\ne0\).
Two integrations by parts give
\[
 F_T(n)=\frac{f(T)e^{inT}}{in}+R_n,\qquad
 |R_n|\le\frac{A_T}{n^2},\quad
 A_T=|f'(T)|+\|f''\|_{L^1(-\infty,T]} .
\]
For \(n\ge2A_T/|f(T)|\),
\(|F_T(n)|\ge|f(T)|/(2n)\).
If
\[
 K\ge\max\{8,4A_T/|f(T)|\},
\]
the even frequencies \(n\in[K/2,K]\) contain at least \(K/8\) terms,
are all present in the actual four-constituent cutoff, and satisfy
\(n^2-4\ge K^2/8\). Therefore
\[
 \boxed{\|\Phi_{1,K}(T)\|^2
 \ge\frac{5\lambda^2|f(T)|^2}{2^{19}V_0^2}K^3.}            \tag{AO.7}
\]
This is a squared-norm bound; the norm grows at least as \(K^{3/2}\).
A scalar or quadratic counterterm cannot cancel this orthogonal
four-particle component on the free vacuum.

More generally, if the first nonzero endpoint jet has order \(m\),
with enough past integrability for \(m+2\) integrations by parts,
\[
 F_T(n)=
  \frac{(-1)^m f^{(m)}(T)e^{inT}}{(in)^{m+1}}
       +O(n^{-m-2}).
\]
For nonzero \(\lambda\), the quartic tail gives the sharp criterion
\[
 \boxed{\Phi_1(T)\in D(H_0^p)
       \ \Longleftrightarrow\ m>p+\tfrac32,\qquad p\ge0.}   \tag{AO.8}
\]
At equality the divergence is logarithmic. Thus \(m=2\) supplies a
Hilbert vector but not finite free mean energy; finite free mean and second
energy moments both require at least \(m=3\).
For pure cubic interaction the corresponding criterion is \(m>p+1/2\).
The cases \(m\ge1\) already have the coupling off at the endpoint, and
cannot replace a still-active preparation.

## AO5. One fixed compact switch, two explicit endpoints

Keep the AI positive bump,
\[
 \tau=\tfrac1{10},\quad
 f(t)=\exp[1-1/(1-(t/\tau)^2)]\ (|t|<\tau),\qquad f=0
 \text{ otherwise}.
\]
For the complete switch ending at \(T\ge\tau\),
\(\widehat f(n)\ge\tau e^{-1/3}\cos(n\tau)>0\) for \(n=3,4\).
The lowest sectors in (AO.3) therefore give the explicit positive
squared-norm lower bound
\[
 \tau^2e^{-2/3}\left[
  \frac{g^2}{8V_0}\cos^2(3\tau)
  +\frac{15\lambda^2}{32V_0^2}\cos^2(4\tau)\right].          \tag{AO.9}
\]

Instead end at its center \(T=0\): \(f(0)=1,f'(0)=0\).
The derivative magnitude has a unique positive maximum at
\(y=1/(1-(t/\tau)^2)=(3+\sqrt3)/2\), and
\[
 \|f'\|_\infty
 =\tau^{-1}\sqrt{36+21\sqrt3}\,
             e^{-(1+\sqrt3)/2}<22 .
\]
Thus \(A_0=\|f''\|_{L^1(-\infty,0]}=2\|f'\|_\infty<44\).
For \(g=\lambda=1/10\) and every \(K\ge176\), (AO.7) becomes
\[
 \boxed{\|\Phi_{1,K}(0)\|^2
        \ge K^3/(10485760V_0^2).}                         \tag{AO.10}
\]
The same smooth switch has a good complete outgoing first vector and
a divergent still-active first vector. The endpoint, not just smoothness
of the past switch, is part of the preparation contract.

## AO6. Exact scope of the rejection

No Hilbert vector has the non-square-summable occupation coefficients
in (AO.7). Therefore a construction that requires those actual
cutoff coefficients to be the strong free-Fock coupling derivative
cannot be accepted.

There is also no uniform normalized-state remainder of the form
\[
 \|\Psi_{\epsilon,K}-\Omega-\epsilon\Phi_{1,K}\|
       \le C\epsilon^2
\]
at the active endpoint with \(C\) and a nonzero allowed \(\epsilon\)
independent of \(K\): normalization would imply
\(|\epsilon|\|\Phi_{1,K}\|\le2+C\epsilon^2\), contradicting (AO.7).
This applies to a one-sided positive coupling parameter as well.

Normalizing the active finite-cutoff first vector by the recipe (AO.6)
does not repair it. Every fixed finite-occupation coefficient of
\(\Phi_{1,K}\) stabilizes while its norm diverges, so the normalized
vectors converge weakly to zero and cannot converge strongly to a unit
vector. Their pure densities likewise have no trace-norm normal-state
limit.

Divergence of cutoff derivatives alone does not rule out a possible
cutoff-limit family with a noncommuting derivative limit, a nonanalytic
coupling dependence, a different representation, or a different dressed
preparation. The complete-switch graph result does not prove a full Dyson
series or interacting continuum unitary. The next required object remains
a positive correlated preparation valid while the local interaction is
active, together with the same counterterms, smooth source histories and
stress/constraint domains. Physical unification remains open.
