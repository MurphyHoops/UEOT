# UV continuation: combine the source and counterterms before judging the limit

## U1. What the bare coefficient proves, and what it does not

At fixed A,u and the same AE subtraction convention,
\[
 g_K=C/120-H_K/4\longrightarrow-\infty.
\]
Thus the positive-g common-form construction cannot by itself give a
sequence with K unbounded on this fixed clock patch. Rechoosing u with K
changes the background and is not the prescribed continuum limit.

This statement is **not** a no-continuum theorem. g_K is the Hessian of
the local subtraction block in the finite-K action. The source response
also has divergent local pieces. Their sum, including its state and
boundary terms, is the object to renormalize. A sign test on one bare
summand is insufficient; nor does 1/g_K -> 0 prove convergence of the
complete quantum generator.

## U2. A same-convention static high-frequency cancellation with C2 tails

Here is a useful exact consistency test, explicitly distinct from the
actual nonstatic incoming state. Freeze a scalar potential V in the high
oscillator frequencies, with k²>1+V. For the two fields the shell vacuum
energy is E_k(V)=k² sqrt(k²-1-V). Its local vacuum Lagrangian contribution
is -E_k. The increment of L1's counterterm at this shell is exactly
\[
 L_{\mathrm{ct},k}
 =k^3-\frac{(1+V)k}{2}-\frac{(1+V)^2}{8k}.
\]
Writing z=(1+V)/k², their **combined** contribution is
\[
 R_k(V)=k^3 F(z),\qquad
 F(z)=-\sqrt{1-z}+1-z/2-z^2/8.                              \tag{U1}
\]
F(0)=F'(0)=F''(0)=0. For |z|<=1/2,
|F^{(3)}(z)|<=3/sqrt(2)<3.
If M>=max(1,sup|1+V|) and k²>=2M, Taylor's integral remainder gives
\[
 |R_k|\le M^3/k^3,\quad
 |\partial_VR_k|\le2M^2/k^3,\quad
 |\partial_V^2R_k|\le3M/k^3.                               \tag{U2}
\]
Their tails above K are bounded respectively by
M³/(2K²), M²/K² and 3M/(2K²).
Thus this local high-frequency comparison converges in C2 on compact V
sets. In particular,
\[
 \partial_V^2(-E_k)=\frac1{4k}+O(k^{-3}),\qquad
 \partial_V^2L_{\mathrm{ct},k}=-\frac1{4k}.                 \tag{U3}
\]
The logarithmic Hessian divergence cancels. The k=1 reference, the finite
analytic term and finitely many low modes remain separate and unchanged.

U1--U3 are newly checked algebra and a rigorous tail estimate for this
c-number frozen-V comparison. They do not calculate the actual incoming
nonstatic determinant, retarded polarization, CTP boundary contacts or
the coupled quantum-geometric propagator. The Anderson--Eaker primary
paper explains why local subtraction and the source must be combined;
it does not establish the quantum model constructed here.

## U3. What is genuinely rejected in the fixed-Fock representation

The predecessor QUANTUM_ENDPOINT already rejects an isolated active
full-field shear as a normal fixed-Fock limit. We reuse that result here,
without counting it as a new theorem. Its finite-K mechanism is visible:
on actual high-mode vacua with position variance 1/(2 Omega_k),
Omega_k~k, the centered Q_K has
\[
 \operatorname{Var}(:Q_K:)=\sum_{k=3}^K\frac{k^2}{4\Omega_k^2}
                         \sim K/4 .
\]
Removing a scalar expectation does not make this sharp-slice operator
converge in the source L2 norm. The shear overlap per shell has modulus
\[
 |\langle e^{i\kappa Q_k}\rangle|
 =\left(1+\frac{\kappa^2}{4\Omega_k^2}\right)^{-k^2/2}.
\]
For fixed nonzero kappa, tail products fail the Cauchy test; a scalar phase
does not alter the modulus. The uniform source dilation R likewise is
not individually an infinite-mode Fock unitary.

Those facts reject a **factor-by-factor** passage to fixed-Fock limits in
W R U_tilde R† W†. They do not reject a joint limit of the complete
product, where cancellations may occur, or another locally covariant
representation with properly transported states. They also do not make
a sharp-slice Q² legal merely by calling it Wick ordered.

## U4. The next continuum object and its required checks

A meaningful continuation must specify the combined finite-K CTP or
propagator object, embeddings of states and observables, and one common
renormalization prescription. It must then establish:

1. Uniform estimates on the complete object, including matter polarization
   and the geometric subtraction, rather than on isolated W or g.
2. Convergence on the declared time/space smoothed domain; contacts and
   initial density transport must accompany the bulk expressions.
3. The same Ward identities, constraint rows, positive normal joint state
   and causal composition after the limit.
4. Recovery or a controlled replacement of the actual mean history and
   finite calibrated readings with the full preparation/controller source.

The finite-K existence results in this directory are useful starting data,
not these uniform estimates. Local covariant Wick-product theorems on a
classical background constrain allowable renormalization but do not
supply a quantum geometry Hilbert space or this missing full-field limit.
