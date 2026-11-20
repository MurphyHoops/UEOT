# Positive-dust finite-stress obstruction

## 1. Precise model and claim

This starts with the **new**, explicitly chosen two homogeneous zero-mode
model in [GRAVITY_CONTRACT.md](GRAVITY_CONTRACT.md). It does not change the
frozen AE theory. Put
\[
 c={3\over8V_0},\quad g_P={|P|^2\over2c}={4V_0|P|^2\over3},\quad
 H_P=c\,\partial_x^2+{cg_P\over x^2}+W(x),\qquad
 W(x)=V_0U_0x^2-\tfrac32V_0x^{2/3}.
\]
Here \(x=a^{3/2}>0\), the measure is \(dx\,d^2P\), and the fixed separated
limit-circle/limit-point self-adjoint realization is the one already
declared. The positive integrated zero-mode matter energy is the
quadratic form
\[
 K_{0,P}={|P|^2\over2x^2}.
\]
It must not be replaced by the signed total Hamiltonian.

**Fiber theorem.** If \(g_P\ge1/4\),
\[
 \psi\in D(H_P),\qquad
 \psi=\mathbf1_{(-\infty,0]}(H_P)\psi,
\]
and \(\langle e^{-itH_P}\psi,K_{0,P}e^{-itH_P}\psi\rangle\) is finite at
every time in a nonempty open interval, then \(\psi=0\).

**Normal-state theorem.** Let
\(H_\theta=\int^\oplus H_{P,\theta}\,d^2P\), and let a density operator
\(\rho\) satisfy
\[
 \rho=\Pi_-\rho\Pi_-,\quad \Pi_-=\mathbf1_{(-\infty,0]}(H_\theta),
 \qquad {\rm Tr}(\rho H_\theta^2)<\infty .
\]
If \({\rm Tr}(\rho_tK_0)<\infty\) throughout a nonempty open time interval,
then its momentum law is entirely supported in
\[
             D=\{|P|^2<3/(16V_0)\}.                         \tag{1}
\]
This is a necessary finite-positive-energy condition, not a sufficient
certificate of all local stress moments. Compact spectral support is not
required.

## 2. The positive matter form detects the endpoint amplitude

For \(g_P>1/4\), put \(\nu=\sqrt{g_P-1/4}\). The one remaining allowed
boundary amplitude of a vector in the fixed self-adjoint domain is
\[
 \psi(x)=\gamma_P(\psi)b_\theta(x)+q_\psi(x),\qquad
 b_\theta(x)=\sqrt{x}\,[A_\theta\cos(\nu\log(x/\ell))
                        +B_\theta\sin(\nu\log(x/\ell))],
\]
with a nonzero real coefficient pair. The remainder is \(o(x^{3/2})\).
At \(g_P=1/4\), replace this by
\[
 b_\theta(x)=\sqrt{x}\,[A_\theta+B_\theta\log(x/\ell)],
 \qquad q_\psi=o(x^{3/2}|\log x|).
\]
The local boundedness of \(W\) leaves these inverse-square maximal/minimal
domain expansions unchanged. Thus \(q_\psi/x\in L^2(0,\epsilon)\), while
\(b_\theta/x\notin L^2(0,\epsilon)\). The latter is respectively an
infinite logarithmic-coordinate integral of a nonzero periodic square or
a nonzero polynomial square. Hence
\[
              \langle K_{0,P}\rangle_\psi<\infty
                     \ \Longrightarrow\ \gamma_P(\psi)=0.             \tag{2}
\]

For graph continuity, choose a complementary real endpoint solution
\(d_\theta\) with \(W(b_\theta,d_\theta)=1\), multiplied by a smooth
near-zero cutoff. Both \(d_\theta,H_{\max}d_\theta\) are in \(L^2\).
Green's identity gives
\[
 |\gamma_P(\psi)|\le c^{-1}
   (\|d_\theta\|\,\|H_P\psi\|+\|H_{\max}d_\theta\|\,\|\psi\|).
\]
No uniformity of this bound in \(P\) is needed below.

The endpoint expansions are standard inverse-square domain results:
Derezinski--Richard, [arXiv:1604.03340](https://arxiv.org/abs/1604.03340),
Sections 2.2--2.3. Their use here is distinct from the following
time-window argument.

## 3. A graph-continuous trace with no hidden spectral channel

The scalar half-line LC/LP Sturm--Liouville transform permits a real
entire left-normalized solution \(\phi_E\) with \(\gamma_P(\phi_E)=1\).
It gives a unitary transform to \(L^2(\mathbb R,d\mu_P)\), with \(H_P\)
acting as multiplication by \(E\). For compact spectral support,
\[
                 \gamma_P(\psi)=\int \widehat\psi(E)\,d\mu_P(E).
\]
Graph continuity implies
\[
                  \int{d\mu_P(E)\over1+E^2}<\infty.                    \tag{3}
\]
For example, insert
\(f_n=\mathbf1_{[-n,n]}/(1+E^2)\) into the graph bound:
\(I_n\le C_P\sqrt{I_n}\), where
\(I_n=\int_{[-n,n]}(1+E^2)^{-1}d\mu_P\).

For every \(\psi\in D(H_P)\), Cauchy--Schwarz and (3) give
\[
 \int|\widehat\psi|d\mu_P
 \le\left[\int(1+E^2)|\widehat\psi|^2d\mu_P\right]^{1/2}
     \left[\int{d\mu_P\over1+E^2}\right]^{1/2}<\infty .
\]
The trace formula therefore extends to the full operator domain. In the
inner-product convention conjugate-linear in the first slot it is also
\[
 \gamma_P(\psi)=\langle\eta_P,(H_P-i)\psi\rangle,\qquad
 \widehat\eta_P(E)=(E+i)^{-1}.
\]
Its spectral amplitude is nowhere zero. Scalar multiplicity and this
normalization are essential: graph continuity alone would not prove
cyclicity or rule out an invisible spectral channel.

Primary support: Eckhardt--Gesztesy--Nichols--Teschl,
[arXiv:1208.4677](https://arxiv.org/abs/1208.4677), Theorem 8.4, Lemma 9.2,
Theorem 9.3, Lemma 9.7 and Corollary 9.8. These provide the LC normalization,
scalar unitary spectral transform and Weyl-vector integrability. One may
apply the standard negative-leading-derivative convention to \(-H_P/c\)
and then change the spectral parameter. No semiboundedness of \(H_P\)
is asserted.

## 4. Positive dust gives one-sided Fourier uniqueness

Positive dust means that the physical generator is in the sector \(E\le0\).
For \(\psi\) as in the fiber theorem, \(d\nu=\widehat\psi\,d\mu_P\) is a
finite complex measure supported there. Define
\[
 A(z)=\int_{(-\infty,0]}e^{-iEz}\,d\nu(E).
\]
It is bounded analytic for \({\rm Im}\,z>0\) and continuous to the real
axis, because \(|e^{-iEz}|=e^{E\,{\rm Im}z}\le1\). Its boundary value is
\(\gamma_P(e^{-itH_P}\psi)\). By (2), a finite positive matter form
throughout an open interval gives \(A(t)=0\) on that interval.
Schwarz reflection across that zero real boundary, followed by the
identity theorem, gives \(A=0\) on the upper half-plane. Continuity and
Fourier uniqueness for finite complex measures give \(\nu=0\), hence
\(\psi=0\).

The sign of the half-plane, finite total variation of \(\nu\), and
nonvanishing spectral trace amplitude are all part of the proof. A finite
mean total energy alone would not establish these domain hypotheses.
The proof does not say that positive matter energy is infinite at every
individual time: isolated zero endpoint amplitudes are not excluded.

## 5. Direct integrals, correlations and normal mixed states

Write \(\rho=\sum_n\lambda_n|\psi_n\rangle\langle\psi_n|\), with positive
weights. Finite \({\rm Tr}(\rho H_\theta^2)\) puts every such vector in
\(D(H_\theta)\), and its fibers almost everywhere in \(D(H_{P,\theta})\)
with the nonpositive spectral support.

Choose a countable dense set of times in the proposed open interval.
Positivity and Tonelli, applied to each \(n\) and each such time, leave
one common null set of \(P\) outside which all those positive fiber
energies are finite. The boundary amplitudes vanish there by (2).
Time evolution is continuous in the graph norm, so their vanishing
extends from the dense time set to the whole interval. The fiber theorem
then kills every \(g_P\ge1/4\) component and proves (1).
Source--geometry entanglement and off-diagonal momentum correlations
cannot cancel this positive form.

## 6. Quantitative rejection of the actual input momentum law

Every component of the actual two-dimensional Gaussian mixture has
momentum covariance \(vI\), \(v=x_0/4\). Irrespective of its mean,
\[
 p_{\rm old}(P)\le {1\over2\pi v},\qquad
 {\mathbb P}_{\rm old}(D)\le {3\over32V_0v}<2.85\,10^{-12}.             \tag{4}
\]
The interval certificate evaluates (4) using the frozen exact input
intervals. A separate rational bound uses \(v>1.669\,10^9\) and
\(V_0>19.73\), giving \(3/1053739840000<2.85\,10^{-12}\).

Any source marginal from an accepted normal dust history has probability
one in \(D\). Applying this binary momentum projection shows, with
\(D_{\rm tr}=\tfrac12\|\rho-\sigma\|_1\),
\[
 D_{\rm tr}(\rho_{\rm original,S},\rho_{\rm admissible,S})
       \ge1-{\mathbb P}_{\rm old}(D)>1-2.85\,10^{-12}.                  \tag{5}
\]
This rejects almost the entire original momentum law, not a small bad
tail. It also rejects its momentum-preserving stress-equivalent family
and a direct splice of the positive-clock code in this cohort.

## 7. Laplace--Beltrami and constant-weight orderings do not repair it

### The full three-dimensional minisuperspace Laplace--Beltrami choice

The same homogeneous kinetic action, before Fourier transforming matter,
is
\[
 L_{\rm kin}={1\over2N}
   [-{4V_0\over3}\dot x^2+x^2(\dot Q_1^2+\dot Q_2^2)] .
\]
Thus its configuration-space metric is
\[
 {\cal G}_{AB}=\operatorname{diag}(-4V_0/3,x^2,x^2),\qquad
 |\det{\cal G}|^{1/2}=\sqrt{4V_0/3}\,x^2.
\]
Choose the standard Laplace--Beltrami kinetic ordering
\(-\Delta_{\cal G}/2\), without an added configuration-space curvature
term. In matter momentum representation it gives
\[
 H_{\rm LB}=c(\partial_x^2+2x^{-1}\partial_x)
             +{|P|^2\over2x^2}+W(x)
\]
on \(L^2(x^2dx\,d^2P)\); the constant measure factor is immaterial.
The geometric unitary \(U\psi=x\psi\) gives
\[
           U H_{\rm LB}U^{-1}=H_{\rm flat}.
\]
There is no extra inverse-square potential. This is an operator/domain
equivalence when \(D(H_{\rm LB})=U^{-1}D(H_{\rm flat})\), not just an
identity of formal expressions. In particular
\(W(xu,xv)=x^2W(u,v)\) transports the weighted boundary form correctly.
All the separated extensions are carried to their corresponding flat
extensions.

The unitary acts only on geometry and commutes with the source algebra,
the P spectral projections and the positive K0 multiplication form.
Negative spectral support, total H second moments, the source marginal,
and finite or infinite K0 expectation at every time are therefore
preserved. The same quantitative exclusion (4)--(5) applies to this
full minisuperspace Laplace--Beltrami choice. It is not a unique
quantization derived from Core. The standard ordering and possible
curvature-ordering alternatives are discussed by Ryan--Turbiner,
[quant-ph/0406167](https://arxiv.org/abs/quant-ph/0406167); the metric and
unitary identities here are derived directly from this action.

### A wider fixed constant-weight family

For any fixed finite real beta, declare
\[
 {\cal H}_\beta=L^2(x^\beta dx\,d^2P),\qquad
 H_\beta=c\,x^{-\beta}\partial_x x^\beta\partial_x
                         +{|P|^2\over2x^2}+W(x).
\]
This is an additional family of ordering choices, not the
Laplace--Beltrami operator of the same metric for every beta.
Under \(U_\beta\psi=x^{\beta/2}\psi\),
\[
 U_\beta H_\beta U_\beta^{-1}
 =c\partial_x^2+{c g_{\beta,P}\over x^2}+W(x),\qquad
 g_{\beta,P}={|P|^2\over2c}+{\beta(2-\beta)\over4}.                    \tag{6}
\]
For a fixed measurable decomposable self-adjoint realization, the earlier
proof applies to each fiber with \(P\ne0\) and \(g_{\beta,P}\ge1/4\).
Consequently finite total H second moment plus an open finite-K0 window
forces a normal state into
\[
       D_\beta=\{|P|^2<R_\beta^2\},\qquad
       R_\beta^2={3(\beta-1)^2\over16V_0}.                            \tag{7}
\]
At beta=1, P=0 has K0=0 and cannot be excluded by the fiber argument.
It is a null set for \(d^2P\), so it carries no normal direct-integral
state. There is no nonzero normal state satisfying the stated gate in
that case. For other beta the low-P endpoint can change classification;
no claim that all fibers remain limit-circle is needed.

The input Gaussian mixture has strictly positive momentum density
everywhere, so every finite \(R_\beta\) leaves positive excluded weight.
An explicit bound is available. For an isotropic Gaussian of covariance
\(vI\), a centered disk has its greatest probability when the Gaussian
mean is zero: rotate its mean to the first axis and condition on the
second coordinate; the first-coordinate centered-interval probability
decreases with the magnitude of its mean. Integrating, and then mixing,
gives
\[
 {\mathbb P}_{\rm old}(D_\beta^c)
 \ge \exp[-R_\beta^2/(2v)]
 =\exp[-(\beta-1)^2 B_0]>0,\qquad B_0={3\over32V_0v}.                 \tag{8}
\]
Thus **every finite fixed beta fails exact preservation of the original
P law** under the same physical regularity gate. If an admissible source
marginal exists, its trace distance from the old source is at least the
right-hand side of (8). The elementary area bound also gives
\({\mathbb P}_{\rm old}(D_\beta)\le\min(1,(\beta-1)^2B_0)\).
For beta=0 and beta=2 the original quantitative certificate is identical;
for \(0\le\beta\le2\) its coarse \(2.85\,10^{-12}\) upper bound still
holds. There is no beta-independent near-one trace-distance bound for
arbitrarily large \(|\beta|\).

This corollary fixes the proper-dust-time constraint; multiplying the
constraint by an x-dependent lapse function before quantizing is a new
choice, not covered by the displayed equivalence. Momentum-mixing
boundary conditions, new physical inner products, different endpoint
dynamics and general quantum-gravity completions are also outside this
ordering family.

## 8. Revised acceptance decision

The self-adjoint operator construction, physical inner product and
nonempty positive-dust sector remain mathematically valid. They do
**not** pass the original-state, finite-positive-stress time-window gate.
The present model cannot be registered as an accepted carrier for that
common physical history.

The initial theorem is conditional on this flat ordering, half-line geometry,
fixed decomposable separated extension, positive dust branch and finite
total spectral second moment. Section 7 extends it to the stated
Laplace--Beltrami and fixed constant-weight family. It does not exclude
general other quantizations,
clock models, general physical Hilbert spaces, the frozen mean-SCE, or
full quantum gravity. Adding a hard wall, regularizing inverse volume or
changing the ordering would be a new physical assumption requiring its
own justification and a fresh source/domain/limit check.

The next gate is an independently justified geometric constraint whose
physical domain preserves the actual positive matter form on an open
time window. Only after that gate can the nonzero field modes, full AE
limit and local total-source apparatus be connected. The analytical
theorem is written and natively reviewed; the Python certificate checks
its coefficients, endpoint identities, signs and quantitative consequence,
not a formalized proof of spectral theory.
