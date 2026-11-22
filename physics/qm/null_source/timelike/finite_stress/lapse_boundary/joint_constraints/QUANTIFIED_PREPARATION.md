# JC10 — A certified nonzero target ball for the eight-control preparation

The local inverse in JOINT_PREPARATION.md can be quantified without
solving old mode or geometry ODEs. All norms here are Euclidean control
norms or the explicitly stated coupled one-particle/Fock norms.
These deliberately coarse constants establish a nonzero domain, not
an optimized or experimentally accessible operating range.

## 1. Explicit profile derivative budget

Let \(B_j=\|b^{(j)}\|_1\). With the same bump, \(\delta=1/10\),
\(I\geq e^{-1/3}>5/7\), and \(M<11/5\),
\[
 \|a'\|_1=\frac2{\delta I}<28,\qquad
 \|a''\|_1=\frac{4M}{\delta^2I}<1232 .
\]
The second equality follows because \(w'\) has exactly one extremum
on each half of its support. Convolution gives the safe bounds
\[
 (B_0,B_1,B_2,B_3,B_4)
 <(1,28,784,35000,1517824),                                      \tag{1}
\]
where \(B_0=1\) is equality; each other upper bound is strict.
In particular the largest of
\(\sqrt{B_j^2+B_{j+1}^2}\), \(0\leq j\leq3\), is below
\[
 s_0=1600000 .
\]
For \(u=(\boldsymbol\epsilon,\boldsymbol\zeta)\) put \(x=s_0|u|\).
The actual compact-source Dyson proof then yields coefficient bounds
\[
 \|\alpha_n\|\leq x^n/n!,\qquad
 \|D\beta_n\|_{\rm HS}\leq2n^3x^n/n! .                           \tag{2}
\]
Indeed the row estimate for the third integrated commutator uses
\({\rm Tr}D^{-4}\leq\zeta(2)<4\), with the plus-field gap \(D>1\).
The same bounds apply to multilinear parameter derivatives and every
actual constituent cutoff.

## 2. Observable bounds and the actual nonlinear remainder

For each of the four plus-field density moments \(A_A\) and each
longitudinal moment \(P_A\), write
\[
 O=d\Gamma(a_O)+\tfrac12(a^\dagger b_Oa^\dagger+\mathrm{h.c.}).
\]
Only adjacent shells occur. For the density number block, after
multiplication by \(D^{-1/2}\) on both sides, its edge coefficient is
\[
 \frac{k(k+1)+\mu+\omega_k\omega_{k+1}}
      {2\omega_k\omega_{k+1}}<1 .
\]
Separating the raising and lowering blocks bounds its norm by two.
For \(P_A=-i[H_r,A_A]\), the number block acquires only
\(|\omega_{k+1}-\omega_k|<1\). The pair norms follow from
\(2\sum d_k^2W_k\) and \(2\sum\Omega_k^2d_k^2W_k\).
Thus the common safe bounds
\[
 \|D^{-1/2}a_OD^{-1/2}\|\leq4,\qquad \|b_O\|_{\rm HS}\leq1          \tag{3}
\]
hold for all eight observables.

Let \(F(u)=(\langle\mathbf A\rangle,\langle\mathbf P\rangle)\)
be the actual endpoint mean map. Equations (2)–(3) give each component
the coefficient majorant
\[
 g(x)=e^{2x}(16P(x)^2+2P(x)),\qquad P(x)=x+3x^2+x^3 .
\]
The number part contributes the first term and the anomalous pair part
the second. The antipodal symmetry makes \(F\) odd, so its quadratic
coefficient is zero. Differentiating the multilinear Dyson bounds gives,
for \(x\leq1\),
\[
 \|DF(u)-J\|
 \leq\sqrt8\,s_0x^2g'(1)
 <10^5s_0^3|u|^2,\qquad J=DF(0).                                \tag{4}
\]
Here \(g'(1)=2440e^2\), and \(\sqrt8\,2440e^2<10^5\).
This is a bound on the actual map, not solely its formal Taylor series.

## 3. An inverse bound and an explicit contraction

For \(j=0,1,2\), use
\(|\widehat b(\Omega)|\leq B_2/\Omega^2\),
\(2|d_k|W_k\leq\mu/[32k(k+1)]\), and \(\Omega_k\geq3\). Then
\[
 |a_1^{(j)}(\pi)|\leq\frac{\mu B_2}{32\,3^{\,2-j}} .
\]
The two-by-two block \(J_2\) has Frobenius norm below six.
The first-shell lower bound \(a_1<-9\times10^{-4}\) and
\(a_1''>9|a_1|\) give
\[
 \det J_2>(9\times10^{-4})^2\,9=7.29\times10^{-6},\qquad
 \|J^{-1}\|=\|J_2^{-1}\|<10^6=:M_0 .                              \tag{5}
\]
The full eight-by-eight Frobenius norm is not being identified with
the two-by-two norm; the equality here is for the operator norm of
the repeated blocks.

Take
\[
 r_0=10^{-16},\qquad y_0=r_0/(2M_0)=5\times10^{-23}.
\]
On the closed control ball \(|u|\leq r_0\),
\[
 L=M_0\,10^5s_0^3r_0^2=0.004096<1/2 .
\]
For every \(|y|\leq y_0\), the map
\[
 {\cal T}_y(u)=J^{-1}\{y-[F(u)-Ju]\}
\]
maps this closed ball into itself and has Lipschitz constant at most
\(L\). The integral of (4) along a segment gives both assertions.
Banach's theorem therefore supplies a unique fixed point **in that
ball**, with a convergent iterative definition starting from zero.
No uniqueness outside that ball is claimed.

The instantaneous source bound is
\(\|s(t,\cdot)\|_\infty<310r_0<1/5\), so the positive-gap condition
used by the full-field state construction holds throughout.

## 4. A concrete encoding range

For any real cap profile with \(\|f\|_2\leq1\),
\[
 \left|\int\mathbf Z f^2/2\right|\leq1/2 .
\]
Hence the target \((-\eta^2\mathbf d,\mathbf0)\) lies in the certified
ball whenever
\[
 \boxed{0<\eta\leq10^{-11}.}                                     \tag{6}
\]
The unique common preparation for the two signs then realizes the
eight projected means in JOINT_PREPARATION.md, on the actual normal
endpoint state. The controls are defined by the proven contraction;
a numerical optimal control vector is not claimed in this certificate.

Only these eight mean projections are solved. The positive homogeneous
code energy, higher modes, full quantum constraints, autonomous
actuation and calibrated readout remain separate obligations.
