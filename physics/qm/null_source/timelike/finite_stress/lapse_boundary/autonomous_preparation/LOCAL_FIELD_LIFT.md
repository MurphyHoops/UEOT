# AJ. What lifting the global coordinate to a local field actually requires

## AJ1. The global-coordinate classical model is not a local truncation

The frozen Z global coordinate is a useful autonomous quantum model, but its
classical equations already show the limit of interpreting it as a local
controller:
\[
 \ddot\phi+L\phi+r(x)\psi=0,\qquad
 \ddot\psi+L\psi+r(x)\phi=0,\qquad
 M\ddot x=-r'(x)\int\phi\psi\,dV-e'(x),
 \quad L=-\Delta_{S^3}+1 .
\]
Choose smooth \(f_A,f_B\) with separated supports, at distance \(d>0\),
and a smooth background \(\psi_0\) for which both overlaps are nonzero.
Assume \(r'(x_0)\ne0\). Perturb only the initial \(\phi\) by \(f_B\);
all velocity, \(\psi\), \(x\), and \(\dot x\) variations vanish initially.
Then
\[
 \delta\ddot x(0)=-\frac{r'(x_0)}M\langle f_B,\psi_0\rangle ,
\]
\[
 \delta\phi^{(4)}(0)
 =L^2f_B+r(x_0)^2f_B+
     \frac{r'(x_0)^2}M\psi_0\langle f_B,\psi_0\rangle .
\]
Local derivative terms have zero overlap with \(f_A\). The first
cross-region response is
\[
 \langle f_A,\delta\phi(t)\rangle
 =\frac{t^4r'(x_0)^2}{24M}
       \langle f_A,\psi_0\rangle\langle f_B,\psi_0\rangle+o(t^4).
                                                               \tag{AJ.1}
\]
It is nonzero at arbitrarily small positive \(t<d\).
Any \(x\)-only scalar counterterm has no effect on this first cross term.

This is a smooth classical domain-of-dependence diagnostic. No quantum
commutator Taylor series on an unproved common domain is used.
It excludes treating this global controller as an arbitrary local causal
truncation. It does not exclude constructing a different local controller.

## AJ2. A bounded classical local coupling is stable and has global energy solutions

Replace \(x\) by a real scalar \(\chi(t,y)\), with positive effective mass on
fixed ESU, and use the local potential
\[
 V=\tfrac12m_\chi^2\chi^2+
       \tfrac12(\phi^2+\psi^2)+r(\chi)\phi\psi .
\]
Since \(|r|\le1/5\),
\[
 V\ge\tfrac12m_\chi^2\chi^2+
              \tfrac12(1-\tfrac15)(\phi^2+\psi^2)\ge0 .
\]
The standard energy controls all three \(H^1\) norms and velocity \(L^2\)
norms. With bounded \(r,r',r''\), the nonlinear force map is locally
Lipschitz from \(H^1(S^3)^3\) to \(L^2(S^3)^3\):
the hardest difference is \(r''(\cdot)\delta\chi\,\phi\psi\),
bounded using \(H^1\subset L^6\). The other quadratic products use the
finite volume and the same Sobolev embedding. Wave Duhamel estimates give
local energy-space existence with lifetime controlled by these norms.
Energy conservation and coercivity continue it globally. Smooth data
retain local finite propagation. This is a classical statement.

The quantum replacement \(r(\chi(y))\phi(y)\psi(y)\) is not thereby defined.
The following two precise bare proposals show why a separate UV
construction is needed.

## AJ3. A fixed bounded bump of the bare point field vanishes strongly

Let \(\chi_K(y)\) be the free conformal controller with its actual full-shell
canonical cutoff. Its vacuum variance is
\[
 \sigma_K^2=\frac{K(K+1)}{4V_0}.
\]
For fixed bounded compactly supported \(r\),
\[
 \|r(\chi_K(y))\Omega\|^2
 \le \frac{\|r\|_{L^2(\mathbb R)}^2}{\sqrt{2\pi}\,\sigma_K}
 \longrightarrow0.                                         \tag{AJ.2}
\]
For a fixed finite-mode vector tensored with the tail vacuum, the low-field
spectral law convolves with a broad Gaussian tail. The same Gaussian
density supremum bound holds uniformly in the low spectral shift and in
\(y\). Such vectors are dense, and \(\|r(\chi_K(y))\|\le\|r\|_\infty\).
Therefore \(r(\chi_K(y))\to0\) strongly, and for each \(f\in L^1(S^3)\)
also \(\int f(y)r(\chi_K(y))dV_y\to0\) strongly.

This is not operator-norm convergence. It does not permit multiplying the
strong limit by the unbounded cutoff product \(\phi_K\psi_K\), by divergent
counterterms, or by cutoff-dependent vectors. No free limit of the full
interaction Hamiltonian follows from (AJ.2).

## AJ4. Variance rescaling fails at a point and loses fluctuating local content under smearing

Another possible bare proposal is \(X_K(y)=\chi_K(y)/\sigma_K\).
For nested cutoffs \(K,2K\), the two commuting point variables have unit
Gaussian variances and correlation
\[
 \rho_K=\frac{\sigma_K}{\sigma_{2K}}
       =\sqrt{\frac{K+1}{2(2K+1)}}\le\frac1{\sqrt3}
       \longrightarrow\frac12 .
\]
If real \(r\) is nonconstant in Gaussian \(L^2\), expand its centered part in
normalized Hermite polynomials, with coefficients \(c_n\). Then
\[
 \operatorname{Cov}(r(X_K),r(X_{2K}))
      =\sum_{n\ge1}c_n^2\rho_K^n
      \le\rho_K\operatorname{Var}_\gamma(r).
\]
Consequently
\[
 \|[r(X_K(y))-r(X_{2K}(y))]\Omega\|^2
 \ge2(1-1/\sqrt3)\operatorname{Var}_\gamma(r)>0.               \tag{AJ.3}
\]
The point operators are not strongly Cauchy, even after subtracting their
Gaussian mean.

For spatial smearing the outcome is different. At noncoincident,
nonantipodal \(y,z\), the equal-time cutoff covariance is
\[
 C_K(y,z)=\frac1{2V_0\sin\gamma}
                  \sum_{k\le K}\sin(k\gamma),
\]
so \(C_K/\sigma_K^2\to0\) off a measure-zero set.
The Hermite expansion bounds the absolute covariance of the centered
\(r(X_K)\) by \(\operatorname{Var}_\gamma(r)|C_K/\sigma_K^2|\).
Dominated convergence in the double \(L^1\) integral yields
\[
 \int f(y)r(X_K(y))\,dV_y
   \ \longrightarrow\ \mu_\gamma(r)\int f\,dV\ I
                                                               \tag{AJ.4}
\]
strongly. For the dense extension beyond the vacuum, use finite-mode,
finite-particle vectors: their low-field action divided by \(\sigma_K\)
vanishes in norm. Bounded Lipschitz \(r\), commuting low/high fields,
and the bounded operator norm give the same limit, then density extends it
to all vectors. This argument uses that core, not an unproved field-domain
assertion for arbitrary finite-mode vectors.

For this entry's bump one can quantify the strictly positive variance.
The disjoint Gaussian events \(G\le0\) and \(1/4\le G\le3/4\) have
\(r=0\) and \(r\ge e^{-4/3}/5\), respectively. Using
\(\mathbb P(G\le0)=1/2\) and
\(\mathbb P(1/4\le G\le3/4)\ge\frac12(2\pi)^{-1/2}e^{-9/32}\),
\[
 \operatorname{Var}_\gamma(r)\ge
     \frac{e^{-283/96}}{100\sqrt{2\pi}}>0.0002 .              \tag{AJ.5}
\]
This lower bound uses the two opposite event orderings in the independent
pair formula for variance.

Neither (AJ.3) nor (AJ.4) controls the product with \(\phi_K\psi_K\).
They reject two precise bare shortcuts. A renormalized local action must
be defined and tested on its own terms.

## AJ5. Relation to existing construction results

These conclusions do not assert that all bounded-interaction constructions
fail. Dybalski's [arXiv:2502.07546](https://arxiv.org/abs/2502.07546) treats
bounded total single-field potentials and obtains exact Schwinger-function
limits in specified rescalings. Our \(r(\chi)\phi\psi\) is unbounded in
\(\phi,\psi\), so that theorem does not cover it. Section 4 also identifies
a divergent two-point function in the nontrivial field-rescaled case as an
obstruction to Osterwalder-Schrader reconstruction; that result is not a
normal interacting Hamiltonian construction for this ESU apparatus.

Accepted: the global-model locality diagnostic, classical local stability,
and the two explicit bare quantum cutoff results.
Open: a positive normal continuum local theory with the required stress,
joint preparation and calibrated instrument. AK next computes which
source-containing counterterms and lapse columns such a theory requires
already at one loop.
