# JC7 — Joint preparation of eight density and momentum moments

The four-control pulse in LOCAL_PREPARATION.md produces a nonzero
longitudinal momentum. Treating that momentum as zero would leave a
false closure. A second, explicitly specified time profile remedies
this particular defect.

## 1. Same local source, two profiles per coordinate

Keep the same ground, operators and compact smooth \(b\). Set
\[
 s(t,x)=\sum_{A=1}^4[\epsilon_A b(t)+\zeta_A b'(t)]Z_A(x).           \tag{1}
\]
The uniform Dyson/commutator proof applies to this finite linear span
with the corresponding \(L^1\) derivative bounds. It constructs the
actual normal analytic endpoint density and all its final coupled
energy moments. It still leaves the absolute scalar CTP phase separate.

Let \(u_0=(3+\sqrt3)/2\) and
\(M=2u_0^{3/2}\sqrt{u_0-1}e^{1-u_0}<2.2\).
Differentiating the defining bump gives
\[
 \|b\|_\infty\leq C_0=10e^{1/3},\qquad
 \|b'\|_\infty\leq C_1=100Me^{1/3}.
\]
The open condition
\(C_0|\boldsymbol\epsilon|+C_1|\boldsymbol\zeta|<1/5\)
keeps the plus spatial gap above one and the minus gap at \(0.8\).
The local inverse neighborhood below is intersected with this domain.
The gap bound alone is not a numerical inverse-function radius.

## 2. Actual eight-dimensional Jacobian

Define terminal moment vectors
\[
 A_A=\int Z_AT_{00},\qquad
 P_A=\int\nabla^i Z_A\,T_{0i}.
\]
Write \(a=a_1(\pi)\), \(a'=a_1'(\pi)\), \(a''=a_1''(\pi)\).
Integration by parts in the source time shows that a \(b'\) input
has density response \(a_1'\). Thus at the actual endpoint
\[
 \begin{pmatrix}\mathbf A\\\mathbf P\end{pmatrix}
 =
 \left[\begin{pmatrix}a&a'\\-a'&-a''\end{pmatrix}\otimes I_4\right]
 \begin{pmatrix}\boldsymbol\epsilon\\\boldsymbol\zeta\end{pmatrix}
 +O(|u|^3),\qquad u=(\boldsymbol\epsilon,\boldsymbol\zeta).         \tag{2}
\]
The cubic remainder follows from analyticity and the antipodal
symmetry \(u\mapsto-u\).
All shell contributions give \(a<0,\ a'<0,\ a''>0\). Therefore
\[
 \boxed{\det J_2=(a')^2-aa''>0,\qquad \det J_8=(\det J_2)^4>0.}     \tag{3}
\]
The first-shell bounds in LOCAL_PREPARATION.md already give a strict
positive lower bound; no uncertain cancellation in a truncated sum is
used.

The finite-dimensional inverse function theorem, applied to the
**actual endpoint density map**, now proves: every sufficiently small
eight-vector of these density and longitudinal-momentum moments has a
unique sufficiently small control \(u\) in this family.
The target neighborhood is existential here; a numerical radius is
not claimed.

## 3. Common two-code preparation and remaining energy

The prepared state is centered and even under simultaneous field parity.
At the coding slice apply either of the inherited physical-source
momentum displacements \(\pm\eta f\). Its exact additional classical
tensor is
\[
 \delta\rho_{\rm code}=\eta^2f^2/2,\quad
 \delta T_{0i,\rm code}=0,\quad
 \delta T_{ij,\rm code}=\eta^2f^2\gamma_{ij}/6 .                   \tag{4}
\]
All cross terms linear in the field vanish in the common centered
preparation. With \(d_A=\int Z_Af^2/2\), choose the target
\((\mathbf A,\mathbf P)=(-\eta^2\mathbf d,\mathbf0)\).
Equations (2)–(3) give
\[
 u(\eta)=-\eta^2J_8^{-1}(\mathbf d,\mathbf0)+O(\eta^6).             \tag{5}
\]
The two code states then meet these same eight projected **mean**
conditions. This does not impose an operator constraint or match their
full noise tensor.

For the transform convention \(\widehat h(\Omega)=\int h(t)e^{i\Omega t}dt\),
\[
 \widehat h_A(\Omega)
   =(\epsilon_A-i\Omega\zeta_A)\widehat b(\Omega).
\]
The phase difference removes the quadratic cross term, while \(SO(4)\)
removes cross terms between distinct coordinates. Hence
\[
 E_{\rm exc}=E_b|\boldsymbol\epsilon|^2+
             E_d|\boldsymbol\zeta|^2+O(|u|^4),\quad
 E_d=\sum_k\Omega_k^3W_k|\widehat b(\Omega_k)|^2>0,
\]
\[
 {\rm Var}H_r=V_b|\boldsymbol\epsilon|^2+
             V_d|\boldsymbol\zeta|^2+O(|u|^4),\quad
 V_d=\sum_k\Omega_k^4W_k|\widehat b(\Omega_k)|^2>0.                 \tag{6}
\]
Here \(E_b,V_b\) are defined in LOCAL_PREPARATION.md. All four
coefficients are finite. The preparation energy for (5) is
\(O(\eta^4)\), while each code still adds
\(\eta^2\|f\|^2/2\). Thus the positive homogeneous order-\(\eta^2\)
condition in STATIC_RESPONSE.md survives.

## 4. Full first-order tensor and exact scope

Let
\[
 \boldsymbol\alpha(T)=a_1(T)\boldsymbol\epsilon+
                      a_1'(T)\boldsymbol\zeta,\qquad
 \boldsymbol\chi(T)=o_1(T)\boldsymbol\epsilon+
                    o_1'(T)\boldsymbol\zeta .
\]
Then
\[
 \delta\rho=4\boldsymbol\alpha\cdot\mathbf Z/V_0,\quad
 \delta T_{0i}=-4\partial_i(\boldsymbol\alpha'\cdot\mathbf Z)/(3V_0),
\]
\[
 \delta T_{ij}=
 \frac4{3V_0}(\boldsymbol\alpha-2\mu\boldsymbol\chi)\cdot\mathbf Z
                  \,\gamma_{ij}.
\]
This explicitly retains the pressure and momentum columns. The
post-pulse Ward identity follows from \(a_1''+a_1=2\mu o_1\).

The result controls eight projections and the common normal
preparation which realizes them. Higher harmonics, rotational momentum,
the homogeneous energy condition, full quantum fluctuations,
self-consistent geometric evolution, and the actuator's total source
remain open. An externally prescribed local source is not an
autonomous gravitational apparatus.
