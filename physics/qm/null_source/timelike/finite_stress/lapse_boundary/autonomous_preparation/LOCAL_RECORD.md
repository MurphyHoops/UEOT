# AR — A causal record between separated caps, with the actual AQ preparation

## AR.1 Replace global encoding and readout by explicit local operations

Use exactly the AQ state prepared with \(\tau=100\), then keep \(r=1/5\)
constant. Reset the elapsed-time coordinate to zero at the completed ramp.
The common reference state \(\rho_\tau\) is zero-mean, spatially homogeneous,
parity-even and Hadamard for the final coupled \(P_r\). It is not replaced
by the AP ground in any covariance or energy calculation.

Let two cap centers on unit \(S^3\) have distance \(3/2\), and both cap
radii be \(\varepsilon=1/2\). The source and receiver caps are disjoint.
For geodesic distance \(d\) from a cap center put
\[
 b_\varepsilon(d)=
 \begin{cases}\exp[1-1/(1-d^2/\varepsilon^2)]&d<\varepsilon\\0&d\ge\varepsilon,\end{cases}
 \quad V_\varepsilon=2\pi(\varepsilon-\tfrac12\sin2\varepsilon).
\]
Take \(f=b_\varepsilon/\sqrt{V_\varepsilon}\) on the source cap and
\(g=b_\varepsilon/\sqrt{V_\varepsilon}\) on the receiver cap.
These are nonnegative \(C^\infty\) real functions,
\(\|f\|_2,\|g\|_2\le1\); the volume denominator is not a claim of exact
unit \(L^2\) norm. Their integrals obey
\[
 \int f,\int g\ge e^{-1/3}V_{\varepsilon/2}/\sqrt{V_\varepsilon}.
\]

Encode the two signs with the local source Weyl operators
\(D_\pm=\exp[\pm i\phi_s(f)]\). They shift the source momentum by
\(\pm f\), with zero initial field means. Both use the same \(\rho_\tau\).
The entire initial probe marginal, and all local observables outside
the source cap, remain identical. At time \(T=3\) read
\(Q=\phi_p(g)\) in the receiver cap using a Gaussian instrument of
resolution \(\sigma=1/10\). These are abstract local algebra operations;
a local autonomous encoder/pointer and their stress are not constructed.
The read time labels the field slice, not a completed physical deadline
for collecting the cap-wide readout into a classical device.

## AR.2 Exact retarded transfer, before the first wrap

Let \(\gamma\) be geodesic separation. For a radial field, \(u=\sin\gamma\,\phi\)
turns \((\partial_t^2-\Delta_{S^3}+1\pm r)\phi=0\) into
\((\partial_t^2-\partial_\gamma^2\pm r)u=0\).
The positive initial-velocity one-dimensional kernels are
\[
 J_\pm(t,\gamma)=\tfrac12\Theta(t-\gamma)
 \{J_0,I_0\}(\sqrt r\sqrt{t^2-\gamma^2}),\quad
 S_\pm(t,\gamma)=-{1\over2\pi\sin\gamma}\partial_\gamma J_\pm .
\]
For \(0<\gamma,t<\pi\), all other \(2\pi\)-periodic images lie outside
the cone. The spatially constant auxiliary circle mode drops out of
\(\partial_\gamma\); it is not a negative-energy \(S^3\) mode.

The two \(S_\pm\) have the same front
\(\delta(t-\gamma)/(4\pi\sin\gamma)\). It cancels in the off-diagonal
source-to-probe kernel \(G_{ps}=(S_+-S_-)/2\). Inside the cone,
\[
 G_{ps}(t,\gamma)=
 -{\sqrt r\,\gamma\over8\pi\sin\gamma\sqrt{t^2-\gamma^2}}\,
 [J_1(z)+I_1(z)],\qquad z=\sqrt r\sqrt{t^2-\gamma^2}.
\]
The defining Bessel series give
\[
 J_1(z)+I_1(z)=
 \sum_{m\ge0}{z^{4m+1}\over2^{4m}(2m)!(2m+1)!}\ge z
 \quad(z\ge0).
\]
Therefore \(G_{ps}\le-r\gamma/(8\pi\sin\gamma)\le-r/(8\pi)\).
This is a causal real-data/commutator propagator, not the
positive-frequency Wightman function. Initial spacelike correlations
in that function are not a signal.

For the two caps all pairwise distances lie between \(1/2\) and \(5/2\).
For every \(0<t<1/2\), the local source Weyl commutes with the receiver
observable and its bounded spectral functions. All receiver-cap observables and its raw/binary record marginal
are then identical for the two codes, not only the mean. The complete
retained source-plus-probe output need not agree, and probe observables
near the source cap can already differ. At \(T=3\), all cap pairs are strictly timelike and \(3<\pi\),
so their means have magnitude
\[
 \mu=-\iint g(y)G_{ps}(3,d(y,x))f(x)\,dx\,dy
 \ge \mu_{\rm lo}:=
 {r e^{-2/3}V_{\varepsilon/2}^2\over8\pi V_\varepsilon}>0.
\]
The actual constituent-cutoff transfer converges to this expression:
\(f,g\) have rapidly decreasing spectral coefficients.
Finite spectral cutoffs themselves need not be exactly causal.
The same positive bound holds for the whole window \(5/2<T<\pi\).
During this interval the fixed local \(H_r\), without further switching,
has generated distinguishable normal states of the receiver algebra.
This is a finite-time local quantum record, not a permanent classical one.


There is also a concrete cutoff error without evolving a mode numerically.
For \(K\ge1\), the spectral projections commute with the transfer
operator. The gradient bounds below give
\[
 |\mu-\mu_K|\le {G^2\over(K+1)^2-1}
 \left[{3\over8(K+1)^2}+{\sqrt5\over16(K+1)^3}\right],
 \quad G=22/5 .
\]
Indeed the norm of the transfer on a \(k\)-shell is at most the bracket,
by a divided difference of \(\sin(3\sqrt\lambda)/\sqrt\lambda\);
both \(f\) and \(g\) tails have squared norm at most
\(G^2/[(K+1)^2-1]\).
At \(K=64\) the error is below \(4.1\times10^{-7}\), less than the
positive continuum signal bound. The same variance envelope certifies
a positive complete binary record at that cutoff too. Its small
acausal spectral tails are still cutoff artifacts, not a continuum signal.

## AR.3 Complete local instrument and explicit positive contrast

At the receiver use
\[
 M_z(Q)=(2\pi\sigma^2)^{-1/4}
      \exp[-(z-Q)^2/(4\sigma^2)],\qquad
 \int M_z^\dagger M_z\,dz=I.
\]
All real outcomes are retained. For a binary complete record use
\(z\ge0\) versus \(z<0\); this is a coarse grain, not postselection.

The exact AQ squeezing bounds imply, at any final constant-coupling
waiting time, for \(k\ge1\),
\[
 \operatorname{Var}q_{k+}\le1/(2k),\quad
 \operatorname{Var}q_{k-}\le{k\over2(k^2-r)},\quad
 \operatorname{Var}p_{k+}\le{k^2+r\over2k},\quad
 \operatorname{Var}p_{k-}\le k/2.
\]
Independence of the two normal fields gives
\[
 \nu:=\operatorname{Var}_{\rho_\tau}\phi_p(g,T)
 \le {9\over16}\|g\|^2\le9/16.
\]
Source coherent encoding changes the mean but not this covariance.
The raw record is Gaussian with means \(\pm\mu\) and variance
\(\nu+\sigma^2\). Its binary probability contrast is exactly
\[
 d_{\rm cap}=\operatorname{erf}
 \left({\mu\over\sqrt{2(\nu+\sigma^2)}}\right)
 \ge {2x_{\rm lo}\over\sqrt\pi}e^{-x_{\rm lo}^2}>0,\quad
 x_{\rm lo}=\mu_{\rm lo}\sqrt{200/229}.
\]
This bound follows from integrating \(e^{-s^2}\) on \([0,x_{\rm lo}]\);
no Gaussian approximation or numerical mode ODE is used. The bounded
binary effect also bounds the operational distance of the two states
restricted to the receiver algebra from below; no spatial tensor-factor
density matrix is assumed.

\(Q(g)\) is a self-adjoint Segal field. Its bounded spectral functions
belong to the cap's time-slice local von Neumann algebra. Consequently
the nonselective dual instrument is the identity on its spacelike
commutant. Conditional correlations do not violate this statement.
The sharply timed observable here is **linear and spatially smooth**;
it is not the sharp composite pressure that failed AP's variance gate.

## AR.4 Actual all-mode instrument and its state domains

In a common canonical representation let \(Q_K=Q(P_Kg)\).
All \(Q_K\) commute with \(Q\), and \(Q_K\to Q\) in strong resolvent sense.
For the full Gaussian Stinespring isometry
\((V_K\psi)(z)=M_z(Q_K)\psi\), Gaussian integration gives exactly
\[
 \int M_z(Q_K)M_z(Q)\,dz
 =\exp[-(Q_K-Q)^2/(8\sigma^2)].
\]
Thus
\[
 \|(V_K-V)\psi\|^2
 =2\|\psi\|^2-2\langle\psi,
   e^{-(Q_K-Q)^2/(8\sigma^2)}\psi\rangle\longrightarrow0.
\]
Together with the actual AQ preparation, smooth source Weyl limit and
constant-coupling propagators, this proves convergence of the complete
all-outcome instruments on the actual prepared input. Trace-class
outputs and their binary coarse grains converge; a success branch is
never substituted for the whole instrument.

For completeness, let \(V\) now denote the Gaussian state covariance,
\(c\) the real phase-space vector of \(Q\), \(J\) the canonical
symplectic matrix, \(d=Jc\), \(\nu=c^TVc\), and \(v=1/(4\sigma^2)\).
The normalized conditional covariance is
\[
 V_z=V+vdd^T-{(Vc)(Vc)^T\over\nu+\sigma^2},
\quad
 m_z=m+{Vc\,(z-c^Tm)\over\nu+\sigma^2}.
\]
The signs of \(d\) do not affect its quadratic term.
The AQ endpoint is Hadamard for \(P_r\), and \(g\) is smooth; hence
\(Vc\) and \(d\), transported as Cauchy data, are smooth solutions.
These finite-rank covariance changes preserve the \(P_r\)-Hadamard
property. Integrating over all \(z\), or either binary outcome, preserves
the smooth two-point difference.

Smooth \(f,g\) lie in every one-particle energy graph. The Fourier
Gaussian representation of \(M_z(Q)\) as an integral of Weyl operators,
together with their polynomial energy-graph bounds, preserves all final
coupled-energy moments on these AQ states. Gaussian outcome moments
control the nonselective integral. Cutoff energy convergence means
common diagonal graph convergence and varying-\(H_{r,K}\) recovery;
it does not impose a fixed physical \(H_r\) graph on bare-tail vectors.

## AR.5 Retained full Hamiltonian energy, including the interaction

Let \(D=\sqrt{-\Delta_{S^3}+1}\). The same squeezing envelope gives
\[
 \operatorname{Var}\Pi_p(g)
 \le {11\over20}\langle g,Dg\rangle
 \le {11\over20}\sqrt{1+\|\nabla b_\varepsilon\|_\infty^2}
 <P_*,
\]
with the identical bound for \(\operatorname{Var}\Pi_s(f)\), using
\(f\) in the inner product.
Writing \(u=(3+\sqrt3)/2\), the bump derivative maximum is
\[
 \|\nabla b_\varepsilon\|_\infty
 ={2\over\varepsilon}u^{3/2}\sqrt{u-1}\,e^{1-u}<22/5 .
\]
Volume normalization therefore gives
\(\|\nabla f\|^2,\|\nabla g\|^2<(22/5)^2\).
For the numerical budget use the safe upper
\(P_*=(11/20)\sqrt{1+(22/5)^2}\).

The source kick changes the full coupled \(H_r\) by
\(\pm\Pi_s(f)+\|f\|^2/2\).
Parity of \(\rho_\tau\) makes its covariance with the odd linear term
zero. Thus the source mean increase is at most \(1/2\), and its variance
increase is at most \(P_*\).
The subsequent classical coherent solution has conserved positive
energy \(\|f\|^2/2\le1/2\). This bounds the squared mean
\(|\langle\Pi_p(g)\rangle|^2\le1\).

The nonselective Gaussian \(Q(g)\) measurement is random
\(\pi_p\)-translation by \(\xi g\), with \(\operatorname{Var}\xi=v=25\).
In this same Hamiltonian, including \(r\phi\psi\),
\[
 \Delta\langle H_r\rangle={v\over2}\|g\|^2\le12.5,\quad
 \Delta\operatorname{Var}H_r
 =v\langle\Pi_p(g)^2\rangle+{v^2\over2}\|g\|^4 .
\]
AQ's \(E_{\rm exc},V_E\) therefore give the complete retained-system bounds
\[
 \langle H_r\rangle_{\rm out}\le e+E_{\rm exc}+13,\quad
 \operatorname{Var}_{\rm out}H_r
 \le V_E+26P_*+25+625/2<403.
\]
The mean is an **upper bound**, since the cap functions were not
renormalized to exact unit norm. The external ramp work, encoding cost
and all reader outcomes remain in the ledger. These are retained-field
costs; no physical pointer's own stress has been supplied.

## AR.6 Exact gravitational rejection on this local encoding slice

For the code-minus-reference smooth classical solution, the encoding
slice has fields zero and momenta \((\pm f,0)\).
The complete improved tensor from AP gives pointwise
\[
 \delta\rho(y)=f(y)^2/2,\qquad
 \delta p(y)=f(y)^2/6,\qquad
 \delta T_{0i}(y)=0.
\]
Thereafter the increment is the full improved \(T_{\mu\nu}[h]\), retaining
the mixing term. The common AQ reference stress is spatially homogeneous.
The fixed ESU Einstein tensor and fixed local curvature counterterms are
also homogeneous, but \(f^2\) is compactly supported and nonconstant.
These two-field encoded states therefore fail the pointwise static
Einstein constraint already on the encoding slice. This conclusion
does not assume that the AQ reference is stationary, and does not
exclude a backreacted geometry or another actual source.

Both signs remain related by joint parity, so their complete energy
and parity-even stress statistics agree. The local record distinguishes
the encoded sign; it does not measure a gravitational constraint charge.
Any tensor noise calculation must use the actual AQ covariance and the
new inhomogeneous smooth mean, not the AP stationary covariance.


The reader also has an exact retained-field stress increment. At its
terminal slice, averaging the random probe momentum kick gives
\[
 \Delta_{\rm read}\rho(y)=v g(y)^2/2,\quad
 \Delta_{\rm read}p(y)=v g(y)^2/6,\quad
 \Delta_{\rm read}T_{0i}=0 .
\]
At later times the increment is \(vT_{\mu\nu}[h_g]\), where \(h_g\)
is the coupled smooth classical solution with initial probe momentum
\(g\) and zero fields. Cross terms vanish on averaging the zero-mean
kick. Its energy integrates to \(v\|g\|^2/2\), and its nonzero value
proves that the complete retained matter state really changes.
The reader's nonselective action is on the probe species, so the
source-species marginal at that endpoint is unchanged.
An external apparatus must supply this stress/energy impulse; the
retained fields alone are not conserved across the operation.


## AR.7 Full tensor noise added by this same nonselective reader

Let \(F,G\) be real smooth compact spacetime tensor tests supported
after the reader's terminal slice. Write \(A_F=T(F)\), and retain the
complete improved tensor, its mixing term and one fixed renormalization
datum. For the random Weyl kick \(W_\xi=e^{i\xi Q_p(g)}\),
\[
 W_\xi^\dagger A_F W_\xi
 =A_F+\xi B_F+\xi^2 C_F,\qquad
 B_F=2\mathcal B_F(h_g,\Phi),\quad C_F=T_F[h_g].
\]
Here \(\mathcal B\) is the symmetric bilinear polarization of the
classical quadratic tensor. \(B_F\) is a legitimate real linear field
smear and \(C_F\) is a real scalar. Fixed c-number renormalization terms
cancel in the Weyl difference. All terms have finite second moments on
the actual AQ/AR states by the smooth common domain already proved.

Averaging \(\xi\sim N(0,v)\) and centering each state separately yields
the exact same-channel identities
\[
 \Delta\langle A_F\rangle=vC_F,
\]
\[
 N_{\rm out}(F,G)-N_{\rm before}(F,G)
 =v\,\operatorname{Re}\langle B_FB_G\rangle_{\rm before}
                   +2v^2 C_F C_G .
\]
In particular,
\[
 \operatorname{Var}_{\rm out}T(F)
 -\operatorname{Var}_{\rm before}T(F)
 =v\langle B_F^2\rangle_{\rm before}+2v^2 C_F^2\ge0 .
\]
The linear-field second moment here is **not centered**; it retains the
coherent encoding mean. The increment is a positive semidefinite real
Gram kernel plus a rank-one term. It preserves all cross components of
the tensor. It is not a subtraction of divergent sharp-time variances.

For the conserved integrated energy, treated on its separately
established energy domain, \(B_H=\Pi_p(g)\) and
\(C_H=\|g\|^2/2\); this reproduces exactly AR.5's complete energy cost
and variance formula. This algebraic consistency does not replace the
smooth-test proof by a sharp pressure assertion.

Thus this full Gaussian reader never decreases an unconditioned
smooth quadratic stress variance of the retained fields. Conditional
inference may still be informative. Apparatus correlations and its own
stress are not included by this identity, and it is not a no-go theorem
for the complete gravity--matter--apparatus source. The post-readout
support restriction prevents interpreting an updated state's backward
extension as a modification of the actual preparation past.

## AR.8 Closure and primary identities

This comparison closes actual finite-past preparation plus local
encoding, causal propagation, a complete normal local mathematical
instrument, explicit positive contrast and retained energy/domain
control on one local linear action. It simultaneously rejects the
retained fields as a static Einstein solution. The source actuator,
pointer, total apparatus stress, self-consistent geometry and physical
unification remain open.

The circle/radial reduction and cap estimates are derived here.
The additional frozen-source constraint obstruction and the next full
same-state acceptance gate are in [NEXT_GATE.md](NEXT_GATE.md).
For the underlying 1+1 kernel, see Finster–Paganini,
https://doi.org/10.1007/s00023-022-01215-8 , Section 2.2 Eq. (2.8).
Their Green operator has the opposite sign convention \(PS=-\delta\);
the positive initial-velocity kernel here has \(+\frac12\Theta J_0\).
The Bessel series used above are NIST DLMF
https://dlmf.nist.gov/10.2.E2 and https://dlmf.nist.gov/10.25.E2.
These references do not claim this \(S^3\) apparatus or its gravitational
completion. This is also not a claim of a compact positive-frequency
one-particle state.
