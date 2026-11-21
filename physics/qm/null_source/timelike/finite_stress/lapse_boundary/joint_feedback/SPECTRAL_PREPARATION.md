# From an available Dirac input to a target law: exact success and error bounds

## S1. Existence and preparation are different gates

Fix one physically selected original self-adjoint realization \(R\) and its already constructed physical Hilbert space. The radial \(R\) is a Dirac observable there. Let \(\rho_0\) be an **actually available** normal trace-one physical input, with spectral law
\(\nu_0(B)=\operatorname{Tr}\rho_0E_R(B)\).
The existence gate \(\mu\ll\nu_R\) in BOUNDARY_INTERFACE does not imply that this input can prepare \(\mu\).

This page treats spectral nondemolition operations
\(K_j=f_j(R)\). It computes their exact law and conditional-state tradeoffs, retaining both success and failure in a trace-preserving instrument. It does not claim every target full source density is determined by its radial law, or that such an operation has been derived from a local autonomous apparatus.

## S2. Exact target law and maximum success probability

Suppose \(\mu=r\nu_0\) is a probability. A success operation with several spectral Kraus functions has
\(q(R)=\sum_j|f_j(R)|^2\le I\).
Its conditional radial law is \(q\nu_0/s\), with success probability \(s=\int q\,d\nu_0\).
Exact equality to \(\mu\) therefore requires \(q=sr\) almost everywhere, giving
\[
\boxed{s_{\max}=1/\operatorname*{ess\,sup}_{\nu_0}r,}                \tag{S1}
\]
with value zero if the essential supremum is infinite.
For any \(0<s\le s_{\max}\),
\[
K_s=\sqrt{s\,r(R)},\qquad K_f=\sqrt{I-K_s^\dagger K_s}
\]
attain it. On a \(\nu_0\)-null set with nonzero \(R\)-spectral projection, choose the multiplier to be zero; a measure-class equality for the input alone must not accidentally define an unbounded global Kraus operator.

The combined instrument is completely positive and trace preserving. Its nonselective radial law remains exactly \(\nu_0\); the successful law is not an unconditional narrowing. The full input coherence can change.

If the target has a \(\nu_0\)-singular mass \(q_\perp>0\), exact nonzero-probability QND preparation is impossible; every conditional law has total-variation error at least \(q_\perp\). This is a theorem about the stated spectral QND class, not all possible physical interactions.

## S3. Optimal radial error at a prescribed success rate

Fix \(s\in(0,1]\), \(M=1/s\), and decompose
\(\mu=r\nu_0+\mu_\perp\), \(\mu_\perp(\mathbb R)=q_\perp\).
Every output density at that success rate must satisfy
\(0\le f\le M\), \(\int f\,d\nu_0=1\).
Let
\[
\delta_M=\int(r-M)_+\,d\nu_0,\qquad
c_M=\int(M-r)_+\,d\nu_0=M-1+q_\perp+\delta_M.
\]
The exact optimum is
\[
\boxed{\min D_{\rm TV}(f\nu_0,\mu)=q_\perp+\delta_M.}                \tag{S2}
\]
The lower bound follows from the singular support and the set \(\{r>M\}\). If \(c_M>0\), the bounded density
\[
f_M=\min(r,M)+\frac{q_\perp+\delta_M}{c_M}(M-r)_+
\]
is normalized and lies below \(M\), because \(M\ge1\).
It is below \(r\) on \(\{r>M\}\) and above \(r\) elsewhere, so it reaches S2.
The zero-denominator case is \(M=1,q_\perp=\delta_M=0,r=1\), with \(f_M=1\).
The two Kraus operators
\(\sqrt{s f_M(R)}\), \(\sqrt{1-sf_M(R)}\)
realize precisely the specified success probability.

For \(q_\perp=0\), one can also control a specific full normal target state. Define the Hilbert–Schmidt operator
\(X=\sqrt{r(R)}\rho_0^{1/2}\) by bounded truncation; its squared norm is one. Let \(\rho_*=XX^\dagger\), and \(Y=\sqrt{f_M(R)}\rho_0^{1/2}\). The canonical purifications have overlap
\(\operatorname{Tr}X^\dagger Y=\int\sqrt{rf_M}\,d\nu_0\ge1-\delta_M\).
Therefore
\[
D_{\rm tr}(\rho_*,YY^\dagger)\le\sqrt{2\delta_M-\delta_M^2}.          \tag{S3}
\]
Only the **radial TV** optimum is claimed. S3 is an upper bound for this specified filtered target, not a quantum trace-distance optimum, not an arbitrary old bare-state target, and not a construction of its singular component.

## S4. A second controlled approximation with a different success rate

For \(q_\perp=0\), set \(r_M=\min(r,M)\), \(\delta_M=\int(r-M)_+\), \(a_M=1-\delta_M\). The simpler filter
\[
K_{s,M}=\sqrt{r_M(R)/M}
\]
has success probability \(s_M=a_M/M>0\), with the corresponding complete failure Kraus operator. Its conditional law is \(\mu_M=r_M\nu_0/a_M\), and
\[
D_{\rm TV}(\mu_M,\mu)\le\delta_M\to0.
\]
For \(Y_M=\sqrt{r_M(R)}\rho_0^{1/2}/\sqrt{a_M}\),
the purification overlap is at least \(\sqrt{a_M}\), giving
\[
D_{\rm tr}(XX^\dagger,Y_MY_M^\dagger)\le\sqrt{\delta_M}.             \tag{S4}
\]
These are Hilbert–Schmidt limits, not undefined traces of unbounded operator products. The success tends to zero when an unbounded density ratio is approximated this way. S2 and S4 have different success contracts and should not be conflated.

## S5. A genuine smooth lift through the original constraint

An arbitrary physical Borel multiplier \(f(R)\) cannot automatically be represented by the kinematic multiplier \(f(P_1^2+P_2^2)\). Their null sets can differ: the kinematic radial momentum has Lebesgue spectral type, while \(R\) can have singular spectrum. This is a real limitation of an unqualified Borel lift.

There is a constructive smooth bridge. For the truncated filter of S4, set
\(\vartheta(\lambda)=\arcsin\sqrt{r_M(\lambda)/M}\in[0,\pi/2]\).
Regularity of the finite Borel measure \(\nu_0\), Lusin approximation and smoothing give smooth functions \(\vartheta_n\in[0,\pi/2]\) with
\[
\|\vartheta_n-\vartheta\|_{L^2(\nu_0)}\le\epsilon_n\to0.
\]
The kinematic operators
\[
\sin\vartheta_n(P_1^2+P_2^2),\qquad
\cos\vartheta_n(P_1^2+P_2^2)
\]
are a complete bounded Kraus pair, strongly commute with the original \(a,C_R\), preserve the original smooth annular test space, and intertwine its rigging exactly with
\(\sin\vartheta_n(R),\cos\vartheta_n(R)\).
This follows directly by multiplication in the predecessor's polar rigging formula; no arbitrary Borel equivalence class is substituted.

For a purification of the specified input, the squared difference between the two-record Stinespring vectors is
\[
2\int[1-\cos(\vartheta_n-\vartheta)]\,d\nu_0\le\epsilon_n^2.
\]
Hence their complete success/failure classical–quantum outputs, even with the reference retained, have trace distance at most \(\epsilon_n\). The success probability differs from \(s_M\) by at most \(\epsilon_n\). If \(\epsilon_n<s_M\), the normalized successful state is within
\[
\epsilon_n/s_M
\]
of the ideal S4 state: the trace norm of the failure block bounds the success probability difference, giving the required normalization estimate. Together with S4,
\[
D_{\rm tr}(\rho_{\rm success,n},\rho_*)
 \le\sqrt{\delta_M}+\epsilon_n/s_M,\qquad
p_{\rm success,n}\ge s_M-\epsilon_n>0.                              \tag{S5}
\]
The same smooth-angle method applies to the bounded fixed-rate filter in S3, with its own ideal success rate and error.

This is a constraint-compatible smooth CP preparation approximation for the specified input. Its constants require the actual \(\nu_0\), which has not been computed for the unselected domain. It is not uniform over all inputs, not a free reference state, and not a local, covariant, autonomous implementation. All success and failure records remain in the same nonselective operation.

## S6. Remaining concrete task

Select the physical boundary relation of the original constraint from an actual preparation/action input, determine its radial spectral type on the two old bands with controlled error, and supply a reference state that can actually be prepared. Only then do S1–S5 produce numerical success/accuracy claims. The present closure supplies exact acceptance tests and attainable conditional constructions; it does not silently assert those missing inputs.
