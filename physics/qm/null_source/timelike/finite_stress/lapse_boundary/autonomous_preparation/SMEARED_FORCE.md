# AH. Self-adjoint time-smeared force, actual cutoffs and finite energy cost

## AH1. Definition on the retained full-field Hamiltonian

Use the same accepted \(H=H_M\), including the controller kinetic energy,
all field modes, scalar counterterm, and interactions. Put \(p=p_x\),
\(U(t)=e^{-itH}\), \(N=H+2\ge1\), and let \(g\) be real \(C_c^\infty(\mathbb R)\).
The frozen lower bound gives
\(p^2/(2M)\le H-\inf e\le N\) as forms. Define
\[
 F(g)\psi=-\int g'(t)U(t)^\dagger pU(t)\psi\,dt,\qquad\psi\in Q(H).
                                                               \tag{AH.1}
\]
This is a Bochner integral, and
\[
 \|F(g)\psi\|\le\sqrt{2M}\|g'\|_1\|N^{1/2}\psi\|.                \tag{AH.2}
\]
For real \(g\) it is symmetric. At finite canonical cutoff, integration by
parts on a weak smooth core identifies it with the time-smearing of
\(-\partial_xH_{{\rm field},K}\). That identity is extended as a form/closure;
it does not assert that a sharp force strongly acts on every vector of
\(Q(H)\). AG explains why such an assertion would be unjustified.

Time translation gives
\[
 U(s)^\dagger F(g)U(s)=F(g(\,\cdot-s)),\qquad
 i[H,F(g)]=-F(g'),\quad i[F(g),N]=F(g').                         \tag{AH.3}
\]
The derivative identity is first a form identity on \(D(N^{3/2})\);
spectral truncation of \(N\) extends it to \(D(N)\). With
\(\omega=\sqrt{2M}\|g''\|_1\), the commutator form is bounded by
\[
 |\langle\psi,i[F(g),N]\psi\rangle|
 \le\omega\|\psi\|\|N^{1/2}\psi\|
 \le\omega\langle\psi,N\psi\rangle .
\]
Together with (AH.2), Nelson's commutator theorem on the operator core
\(D(N)\) proves essential self-adjointness of \(F(g)|_{D(N)}\).
Its closure, written \(A_g\), contains \(Q(H)\): approximate any form-domain
vector by spectral truncations and use (AH.2). No claim that the moving
finite-particle form core is an operator core is needed.

A directly applicable statement of the theorem is Corollary B.2,
Eq. (B.3), in van Luijk, *Energy-Limited Quantum Dynamics*,
[CMP 406, 120 (2025)](https://doi.org/10.1007/s00220-025-05282-w).
The hypotheses here have been checked above; compact resolvent is not assumed.

## AH2. Actual physical cutoff convergence

This is the actual Z canonical \(H_K\), not compression of an already
constructed limit force. Define \(F_K(g)\) by (AH.1) with \(H_K\).
Hereafter \(F_K(g)\) denotes its self-adjoint closure.
The preceding argument works uniformly in \(K\), including the embedded
free high tail. Let \(\Pi_K\) project to its vacuum tail. It commutes with
\(H_K,p,F_K(g)\) and tends strongly to one.

For \(\psi\in D(H)\), set \(\phi=(H+i)\psi\) and
\[
 \psi_K=\Pi_K(H_K+i)^{-1}\phi .
\]
Strong resolvent convergence gives both \(\psi_K\to\psi\) and
\(H_K\psi_K\to H\psi\). At each \(t\), \(U_K(t)\psi_K\to U(t)\psi\);
the conserved total form energies also converge. The Z moving-frame proof
has two nonnegative terms: physical controller kinetic energy and
diagonal fiber energy. Each has a lower-semicontinuity bound at its limit,
and the bounded scalar \(e_K\to e\) uniformly. Convergence of the sum then
forces convergence of each norm. In particular,
\[
 pU_K(t)\psi_K\longrightarrow pU(t)\psi .
\]
Weak convergence of this derivative follows by testing against its smooth
core; equality of limiting norms upgrades it to strong convergence.
The uniform energy bound and \(g'\in L^1\) imply
\(F_K(g)\psi_K\to A_g\psi\).

Since \(D(H)\) is a core for \(A_g\), for
\(\eta=(A_g+i)\psi\) the resolvent identity gives
\[
 \|(F_K(g)+i)^{-1}\eta-\psi\|
 \le\|\eta-(F_K(g)+i)\psi_K\|+\|\psi_K-\psi\|\to0.
\]
Its dense range and the uniform resolvent bound establish
\(F_K(g)\to A_g\) in strong resolvent sense. The projections \(\Pi_K\)
reduce these operators; this includes the physical finite-mode instruments.

## AH3. Normal all-outcome instrument

For \(\sigma>0\), spectral calculus defines
\[
 M_z=(2\pi\sigma^2)^{-1/4}
       \exp[-(z-A_g)^2/(4\sigma^2)],\qquad
 {\cal I}(dz)(\rho)=M_z\rho M_z\,dz.                           \tag{AH.4}
\]
This is a normal instrument with all outcomes retained. Its readout law
convolves the spectral law of \(A_g\) with a centered Gaussian of variance
\(\sigma^2\). Every \(Q(H)\) input therefore has a finite second readout
moment by (AH.2).

For actual cutoffs, each fixed-\(z\) multiplier is a \(C_0\) function.
Strong resolvent convergence implies strong convergence of \(M_{z,K}\).
The isometries \(V_K\psi:z\mapsto M_{z,K}\psi\) converge weakly by testing
compact-\(z\) simple functions, and their norms all equal \(\|\psi\|\).
Hence they converge strongly. The integral trace-norm difference of the
outcome-valued density is at most
\(2\|\psi\|\|V_K\psi-V\psi\|\). Finite-rank approximation extends this
to every normal input, including a passive reference system. The classical
output is an \(L^1\) trace-class field, not an asserted trace-class
matrix built from Dirac delta kets.

## AH4. Energy and second-moment cost of this instrument

The nonselective channel in (AH.4) is the Gaussian average of
\(e^{-i\lambda A_g}\rho e^{i\lambda A_g}\), with
\(v=\operatorname{Var}\lambda=1/(4\sigma^2)\).
This section bounds the retained Z energy cost. It does not provide the
own energy or local construction of a separate physical reader.

Let \(B=i[A_g,N]=F(g')\) as the extended form, so
\(\|B\psi\|\le\omega\|N^{1/2}\psi\|\). The following regularization also
avoids assuming undefined \(pH\) or \(Hp\) actions. Put
\(R_\epsilon=(1+\epsilon N)^{-1}\), \(N_\epsilon=NR_\epsilon\).
The weak resolvent identity gives the bounded commutator
\[
 i[A_g,N_\epsilon]=R_\epsilon B R_\epsilon=:B_\epsilon .
\]
It holds on \(D(A_g)\); \(A_gR_\epsilon\) is bounded by (AH.2), and the
resolvent identity extends the form to all vectors. For normalized
\(\psi_\lambda=e^{-i\lambda A_g}\psi\),
\[
 \left|\frac{d}{d\lambda}
       \langle N_\epsilon\rangle_\lambda\right|
 \le\omega\sqrt{\langle N_\epsilon\rangle_\lambda},
\]
using \(NR_\epsilon^2\le NR_\epsilon\).
After integration and monotone \(\epsilon\downarrow0\),
\[
 \sqrt{\langle N\rangle_\lambda}
 \le\sqrt{\langle N\rangle_0}+\frac{\omega|\lambda|}{2}.
\]
Thus, writing \(\mu_1=\sqrt{2v/\pi}\),
\[
 \boxed{\langle N\rangle_{\rm out}
 \le E_1+\omega\sqrt{E_1}\mu_1+\omega^2v/4.}                   \tag{AH.5}
\]

For the second spectral moment,
\(i[A_g,N_\epsilon^2]=B_\epsilon N_\epsilon+N_\epsilon B_\epsilon\).
Its expectation is bounded in absolute value by
\(2\omega\sqrt{\langle N_\epsilon^2\rangle}
            \sqrt{\langle N_\epsilon\rangle}\).
Integration followed by monotone convergence proves \(D(N)\) invariance
and
\[
 \sqrt{\langle N^2\rangle_\lambda}
 \le a+b|\lambda|+c\lambda^2,\quad
 a=\sqrt{E_2},\ b=\omega\sqrt{E_1},\ c=\omega^2/4 .
\]
Averaging its square, with
\(\mathbb E|\lambda|^3=2v\mu_1\) and
\(\mathbb E\lambda^4=3v^2\), gives
\[
 \boxed{\langle N^2\rangle_{\rm out}
 \le a^2+2ab\mu_1+(b^2+2ac)v+4bcv\mu_1+3c^2v^2.}            \tag{AH.6}
\]
These estimates extend by convexity to finite-moment mixed inputs, or by
applying the argument to a purification.

## AH5. Concrete compact test and limits

Take the original \(M=1\) outside H2 preparation Z2, with
\(\langle H\rangle=56\), \(\langle H^2\rangle=4426\), and
\[
 g(t)=r(-3/2+5t),\qquad {\rm supp}\,g\subset[0.3,0.5].
\]
Here \(g\) is only the smearing test. It never replaces the quantum
controller in \(H\). The AB/AC analytic derivative bounds imply
\[
 \|g'\|_1=0.4,\quad
 \|g''\|_1=20\max|r'|<17,\quad \omega\le17\sqrt2 .
\]
For \(\sigma=1\), \(E_1=58,E_2=4654,v=1/4\). The certificate evaluates
(AH.5)–(AH.6) outward and also
\[
 \langle A_g^2\rangle
 \le 2(0.4)^2(56+\|e\|_\infty)<17.921.
\]
The readout second moment is consequently below \(18.921\).
This \(\sigma=1\) is the force reader, not the earlier \(P\) reader with
\(\sigma=0.1\).

Joint low-field parity commutes with \(H\) and \(p\). The two AB sign codes
related by that parity therefore have identical \(A_g\) spectral laws.
This force instrument is not a calibrated sign discriminator.
Accepted: a self-adjoint smeared global force, actual cutoff instrument
limit, and finite first/second retained-energy costs.
Open: a local autonomous reader, the full local stress/Hadamard problem,
spatial Einstein constraints and physical unification.
