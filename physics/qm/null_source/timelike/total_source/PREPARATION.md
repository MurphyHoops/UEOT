# An explicit energy-preserving dilation and its actual resources

## 1. Entropy cannot be removed by a target-only thermal rotation

The two eigenvalues w,w change to w+c,w-c. A shell-only unitary cannot do
this; in particular a unitary commuting with the free Hamiltonian preserves
its thermal function. Put x=c/w. The shell entropy reduction is
\[
 \Delta S=w[(1+x)\log(1+x)+(1-x)\log(1-x)]\ge c^2/w.
\]
At x=1, Delta S=2w log2. The inequality follows by differentiating the
bracket minus x^2 twice. For any initially independent finite-entropy
apparatus and joint unitary,
Delta S_apparatus=Delta S+I_final>=Delta S.
An unchanged finite-entropy catalyst cannot supply this reduction. A common
temperature Gibbs apparatus with an energy-conserving unitary cannot create
the nonthermal state from a joint Gibbs input.

## 2. A complete, unpostselected pure-memory dilation

Take a two-dimensional degenerate memory, H_a=0, initially |0>.
Let A+/-=(A1+/-A2)/sqrt2, and use the ordered block
(|A+,0>,|A-,0>,|A+,1>,|A-,1>). The following unitary acts as identity outside W:
\[
 U_x=\begin{pmatrix}
 1&0&0&0\\0&\sqrt{1-x}&-\sqrt x&0\\
 0&\sqrt x&\sqrt{1-x}&0\\0&0&0&1
 \end{pmatrix}.
\]
Every shell vector in this block has the same total energy. Thus U_x
commutes with the free shell+memory Hamiltonian. Its output on this block is
w|+0><+0|+w|Psi_x><Psi_x|, where
Psi_x=sqrt(1-x)|-0>+sqrt(x)|+1>.
Tracing the actual memory gives rho_+. A shell species phase interchanges
A+ and A- and produces rho_-; the unaffected thermal complement stays fixed.

There is no discarded outcome. With rho_perp=rho_th-w(P_++P_-), the
unnormalized memory blocks are
sigma0=rho_perp+wP_++(w-c)P_- and sigma1=cP_+.
The actual memory marginal is diag(1-c,c), with entropy h2(c). The final
mutual information is h2(c)-Delta S. The off-diagonal memory coherence in
the full output must be retained; dephasing it changes joint entropy by
w h2(x). A readable flag is not an excuse to discard its environment.

## 3. Energy preservation does not close the gate's total source

A generator is
J=i(|+1><-0|-|-0><+1|), U_x=exp(-i theta J), sin^2(theta)=x.
Initially, and under this gate, <J>=0 and Var(J)=w.
For an externally controlled H_int=lambda(t)J,
Var(H_int)=lambda^2 w and Var(partial_t H_int)=lambda'^2 w.
The free energy and mean gate work can be unchanged while transient
interaction/drive fluctuations are nonzero. For a closed lambda pulse the
integrated work statement also depends on the complete control model;
these instantaneous variances are not a dissipated-work lower bound.

H_a=0 is an internal energy convention, not proof of zero local stress.
A physical carrier, controller, timing/program and localized coupling remain
necessary. TOTAL_FUTURE.md proves exactly what the actual endpoint output
implies, and CARRIER.md gives a separate invariant carrier model. Neither
constructs the local gate action. No result is silently combined with the
distinct classical autonomous benchmark.
