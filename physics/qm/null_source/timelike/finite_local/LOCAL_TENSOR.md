# A local tensor calculation that the averaged certificate cannot replace

The short cap probe breaks spatial \(SO(4)\). This is not merely a possible caveat: the actual nonselective out state has a strictly nonzero anisotropic mean source.

Let \(u=Ef\) be the real smooth classical displacement solution for the fixed short test. The out nonselective target channel is exactly a mixture of Weyl displacements with independent Gaussian \(\xi_i\) for the two fields, \(E\xi_i=0\), \(E\xi_i^2=s=1/(4v_m)\). Therefore
\[
\Delta\langle T_{\mu\nu}\rangle=2s\,T_{\mu\nu}[u].
\]
This formula uses the full displacement, not just its high projection. Its zero-mode constant part carries no stress, but is useful in proving nonconstancy of the full solution.

At the slice immediately after the pulse, finite propagation bounds \(\operatorname{supp}u\) by a proper cap of radius \(7\pi/12\). We may use the looser \(5\pi/8\) cap, whose volume is
\[
V_{\rm cap}=5\pi^2/4+\pi/\sqrt2<3V/4,\qquad V=2\pi^2.
\]
The nonzero source gain implies \(\int_{S^3}u\,d\Omega=\pm A^{-2}\). Thus \(u\) cannot be constant on this slice.

Cauchy–Schwarz and the first nonzero scalar eigenvalue 3 of the unit \(S^3\) give
\[
\int|Du|^2\ge3\left[{(\int u)^2\over V_{\rm cap}}
                    -{(\int u)^2\over V}\right]
 >{1\over2\pi^2A^4},\qquad
\int|Du|^4>{1\over8\pi^6A^8}.
\]
The physical orthonormal anisotropic pressure is
\[
\Delta\pi=2sA^{-2}
 \left(Du\otimes Du-\tfrac13\gamma |Du|^2\right).
\]
The squared tensor norm of the bracket is \(2|Du|^4/3\). Including the physical volume factor \(A^3\),
\[
W:=\int|\Delta\pi|^2\,dV_{\rm phys}
 >{s^2\over3\pi^6A^9}
 ={1\over12\pi^2A\,w_{\rm ptr}^2}>0.
\]
Every factor is independently checked in the script. This lower bound is tiny; it proves nonzero exact anisotropy, not practical detectability or failure of a controlled approximation.

The smooth binary instrument is complete, so \(\sum_bp_b\pi_b=\Delta\pi\), since the old state is homogeneous. Jensen in the tensor \(L^2\) space gives
\(\sum_bp_b\|\pi_b\|_2^2\ge W\). At least one actual complete flag has nonzero anisotropic target stress. With no compensating anisotropic device source, two homogeneous FLRW branches cannot both solve the pointwise field equations at this common out slice. This does not exclude nonhomogeneous metrics or explicit device compensation, and it does not assert nonzero anisotropy at every later instant.

## The exact new local stress-noise kernel

Define the polarized linear operator
\[
L_{\mu\nu}^{(i)}[\Phi_i,u]
 =\nabla_\mu\Phi_i\nabla_\nu u+\nabla_\mu u\nabla_\nu\Phi_i
   -g_{\mu\nu}\nabla_\alpha\Phi_i\nabla^\alpha u,\qquad t=T[u].
\]
The displaced stress is
\(T_{\rm tot}+\sum_i\xi_iL^{(i)}+\sum_i\xi_i^2t\).
Subtract its mean before squaring. Independence of the pointer variables, their vanishing odd moments, and \(\operatorname{Var}(\xi_i^2)=2s^2\) give the exact added symmetrized connected noise
\[
\Delta N(x,x')
 =s\sum_{i=1}^2
    \left\langle\tfrac12\{L^{(i)}(x),L^{(i)}(x')\}\right\rangle_{\rm original}
  +4s^2t(x)t(x').
\]
The linear moment is **raw**, so actual means are retained. This derivation requires no Gaussian assumption for the target CQ mixture. Its original cross-species noise remains in \(N_{\rm original}\); it is not deleted by applying Wick's rule to the mixture.

These are out-region conserved tensor kernels. The noise is a bidistribution and requires smooth spacetime smearing for finite observable variances. Conditional flag noise is obtained from
\(N_\Phi=\sum_bp_bN_b+\operatorname{Cov}_b(\langle T\rangle_b,\langle T'\rangle_b)\); it is not simply equal to the nonselective expression above.

The actual source and its extra noise are thus explicit. The next task is the causal response of nonhomogeneous metric modes, with the same device/controller total source, rather than projecting this tensor back to a homogeneous ansatz.


## Positive added noise for every smooth local stress test

For a real symmetric smooth compact spacetime test \(H^{ab}\) in the free-out region, integration by parts gives
\[
L_i(H)=\Phi_i(F_H[u]),\quad
F_H[u]=-\nabla_a(2H^{ab}\nabla_bu-\operatorname{tr}(H)\nabla^au).
\]
Thus the exact nonselective variance increment is
\[
\Delta\operatorname{Var}(T_{\rm tot}(H))
 =s\sum_i\langle\Phi_i(F_H)^2\rangle
   +4s^2T[u](H)^2
 \ge(\Delta\langle T_{\rm tot}(H)\rangle)^2\ge0.
\]
The added noise kernel is positive semidefinite on such tests. Better conditional source precision therefore does not mean a reduction of the complete nonselective local stress noise. This does not assert monotonicity of every conditional flag's noise.

The out injected target energy also bounds the integrated momentum by \(\int|\Delta j|dV\le\Delta E<1.88\,10^{-11}\), and integrated anisotropic stress by \(\int|\Delta\pi|dV\le2\sqrt{2/3}\Delta E\). These upper bounds coexist with the tiny strict anisotropy lower bound; an exact obstruction is not an estimate of a large observable effect.


The support argument also gives an energy lower bound. More generally, if the out support fraction is \(f<1\), source gain is \(\beta_{\rm signal}\), and \(w_{\rm ptr}=v_m/\beta_{\rm signal}^2\), then
\[
\Delta E\ge{3A\over4w_{\rm ptr}}(1/f-1).
\]
Our \(f<3/4\) yields \(\Delta E>A/(4w_{\rm ptr})>8.31\,10^{-14}\). This is a resource bound for this specified static two-pointer local random-displacement channel, not a universal apparatus cost for all instruments with the same POVM. A long exact filter can have \(f=1\) and constant out \(u\), consistently giving zero out energy.

In a physical orthonormal frame the Euclidean Frobenius norm of a massless classical stress tensor is exactly \(2\rho[u]\). Consequently the complete nonselective mean tensor obeys \(\int\|\Delta T\|_F dV=2\Delta E<3.76\,10^{-11}\). It controls all components in an integrated mean norm, but is not a pointwise, conditional-flag or full-history total-source bound.
