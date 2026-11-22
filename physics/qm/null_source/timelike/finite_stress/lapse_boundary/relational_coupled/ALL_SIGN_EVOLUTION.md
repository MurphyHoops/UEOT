# Complete finite-mode dynamics for either sign of g

This extends the positive-g construction to every fixed finite K>=2 on a
compact clock interval J on which g_K has one nonzero sign, and to every
fixed eta>=-1/4 with the declared Friedrichs principal realization.
The occupation cutoff used in the proof is removed; the spatial mode
cutoff K is not. All scalar terms include the corrected frozen nonzero U0.

## A1. Remove only the zero-mode dilation

Write H0=P0²/2+Hosc, where P0² is the sum over the two zero modes and
Hosc=sum_j omega_j(n_j+1/2), j=1..d, d=2 sum_{k=2}^K k².
In the W-frame use R0=exp[-i(u-ui)D0]. It cancels only D0.
The nonzero-mode dilation Dosc=(i/2)sum(a_j†²-a_j²) remains.
The resulting Hamiltonian is
\[
 H=\alpha A_\eta+\beta x^2+
 \kappa_x^{-1}[H_{\rm osc}+e^{-2(u-u_i)}P_0^2/2+d_0]
 +d_1\kappa_x+D_{\rm osc},
\quad \alpha=1/(2g),\quad\beta=9d_3/4.                       \tag{A1}
\]
In particular we have not replaced an indefinite infinite-dimensional
source operator by finitely many occupation levels.

## A2. The real lens also works when alpha is negative

Use exactly LENS_EVOLUTION's construction with ds/du=2alpha.
For alpha<0 this is a reverse monotone real coordinate, not a complex
scale. The fundamental pair r1,r2 still has Wronskian 1. Thus
b=sqrt(r1²+r2²)>0, theta=b'/(2alpha b), and the real unitary lens L
satisfies the same Pinney identity. It is identity at ui.
The complete transformed generator is Hhat=Hdiag+Dosc, with
\[
 H_{\rm diag}=\frac{\alpha}{b^2}(A_\eta+y^2)
 +b^{-2/3}\kappa_y^{-1}[H_{\rm osc}+e^{-2(u-u_i)}P_0^2/2+d_0]
 +b^{2/3}d_1\kappa_y,\quad \kappa_y=(3y/2)^{2/3}.            \tag{A2}
\]
Let epsilon=sign(g). The coefficient of A_eta+y² in epsilon Hdiag
is c(u)=|alpha|/b², with c0=min_J c>0.

## A3. A positive comparison operator, not an added physical source

Define lambda0=1+Hosc+P0²/2, S=lambda0³, and
\[
 {\cal Q}_\sharp=D(q_{\eta,F})\cap D(y)\cap D(S^{1/2}),\qquad
 T[\psi]=q_\eta[\psi]+\|y\psi\|^2+\langle S\rangle.           \tag{A3}
\]
For each source spectral fiber lambda>=1, ORDERING_DOMAIN gives
I<=sqrt(m q_eta)/r_eta, r_eta=1+sqrt(1+4eta)/2.
Set B=sup_J b^(-2/3)[max(1,e^(-2(u-ui)))+|d0|] and
V=sup_J|b^(2/3)d1|. Two scalar Young bounds imply
\[
 B\lambda I\le\frac{c_0}4 q_\eta+\frac{c_0}4\langle y^2\rangle+
 C_B\lambda^3,\quad C_B=\frac{2B^3}{\sqrt3 c_0^2 r_\eta^3},
\]
\[
 Vm\le\frac{c_0}4\langle y^2\rangle+C_V,\quad
 C_V=\frac{2V^{3/2}}{\sqrt{3c_0}}.                          \tag{A4}
\]
For example, first absorb the square root into c0 q/4, then maximize
a lambda² kappa-(c0/9)kappa³; y²=4kappa³/9.
These estimates are valid for source-valued vectors by the source spectral
resolution and include the critical eta=-1/4 form.

Take Lambda=C_B+C_V+1. The comparison form
\[
 F(u)=\epsilon H_{\rm diag}(u)+\Lambda S
 \ge(3c_0/4)q_\eta+(c_0/2)y^2+S\ge1                       \tag{A5}
\]
is closed, positive, has common domain Qsharp, and is uniformly equivalent
to T on J. The same A4 applied to coefficient derivatives proves C2 form
regularity and |F'|<=C_J F. Fixed U0 contributes its full a⁴ derivatives.

S and the total nonzero occupation N strongly commute with F and Hdiag:
their spectral projections preserve the forms and remove cross terms.
Hence Hdiag=epsilon(F-Lambda S) has a definite self-adjoint direct-integral
realization. Its diagonal evolution can equivalently be obtained from
the positive F evolution by removing the commuting phase.
Lambda S is a comparison device only. It is not a change to the action.

## A4. Retain Dosc and control its commutator

On finite occupation vectors,
i[Dosc,Hosc]=sum(omega²q²-p²), whose absolute form is bounded by 2Hosc.
After multiplication by kappa_y^-1 it is bounded by C_J T using A4.

The commutator with S has a useful finite explicit constant.
In the occupation basis, lambda_n=1+|p0|²/2+sum omega_j(n_j+1/2).
Nonzero Dosc matrix elements join m=n+/-2e_j. With
delta=|lambda_m-lambda_n|=2omega_j,
\[
 \delta|D_{mn}|\le\lambda_{\max},\quad
 1\le\lambda_{\max}/\lambda_{\min}\le5 .
\]
Therefore
\[
 \frac{|[D,S]_{mn}|}{\lambda_m^{3/2}\lambda_n^{3/2}}
 \le3(\lambda_{\max}/\lambda_{\min})^{3/2}<36 .
\]
There are at most 2d neighbors per row and column, so the Schur bound is
\[
 \|S^{-1/2}i[D_{\rm osc},S]S^{-1/2}\|\le72d.                \tag{A6}
\]
Consequently the actual complete generator obeys the comparison-form
commutator bound |i[Hhat,F]|=|i[Dosc,F]|<=C_J F.
The finite constant depends on K; it is not a continuum estimate.

## A5. Domain of the commutator and the exact abstract theorem

We use Ammari--Breteaux, Appendix C, Corollary C.4, with its S(t)=F(u),
H+1=Qsharp, A(t)=Hhat(u). Root and two agents read the stated hypotheses:
a norm-continuous symmetric Qsharp->Qsharp* generator, a common positive
comparison form, a form bound on F', and a commutator bound on D(F^(3/2)).
The generator itself need not be semibounded.

That last domain is not replaced by a formal core calculation.
N,F,S strongly commute, N+1<=lambda0 and F>=S. Occupation band bounds give
||Dosc psi||_Qsharp<=C_d||(N+1)psi||_Qsharp.
For psi in D(F^(3/2)), the latter is finite by the joint spectral calculus.
The diagonal F/S terms in the required commutator cancel exactly.
Cut off N and the zero-mode momentum; these projections commute with F,S
and converge in the necessary F^(3/2) and NQsharp norms. At finite N the
geometric forms commute with Dosc, leaving only the two source
commutators in A4/A6. Passing in the controlled form norms proves the
bound on the actual required domain. No claim that compact-kappa
Schwartz functions are an operator core for every snapshot is used.

Corollary C.4 now supplies the unique full unitary Uhat, with
Uhat Qsharp=Qsharp and trajectories C(Qsharp) intersect C1(Qsharp*).
This is a standard abstract theorem applied to the present complete
operator with all its hypotheses checked, not a new general theorem.

A constructive check also distinguishes the two cutoffs.
Let D_M=P_{N<=M}Dosc P_{N<=M}. For the bounded-source-occupation
perturbation, the same energy bound is uniform in M.
With J_R=(1+F/R)^-1 and F_R=FJ_R,
F_R'=J_R F' J_R and i[D_M,F_R]=J_R i[D_M,F]J_R.
The diagonal generator commutes with F_R.
This yields the uniform energy estimate before R->infinity.
The band width two gives, for L>=M sufficiently large,
\[
 \|(D_M-D_L)\psi\|\le C_d M^{-1/2}\|S^{1/2}\psi\|.          \tag{A7}
\]
Duhamel and the uniform energy estimate give both forward and reverse
strong Cauchy limits, hence a unitary limit. This removes M, not K.

## A6. Original variables, snapshots and the remaining limits

R0 preserves Qsharp since its zero-momentum scaling makes lambda0 and its
cube uniformly equivalent. L preserves Qsharp by its homogeneous
dilation and the ground-state phase estimate
q_eta[e^(i theta y²/2)psi]<=2q_eta[psi]+2theta²||ypsi||².
Thus the original energy class is the fixed W_K Qsharp, and
\[
 U_{\rm bulk}=W R_0(u)L(u)\widehat U(u,v)
                    L(v)^\dagger R_0(v)^\dagger W^\dagger. \tag{A8}
\]
The common-test weak equation transports back exactly. Reversing the
frames and using form density gives uniqueness in this continuous
energy class; unitarity extends the family to the whole Hilbert space.

For a frozen original u*, repeat the construction on any compact auxiliary
time interval. The original equation is autonomous, and uniqueness gives
a group. Stone yields an original-snapshot self-adjoint realization.
For phi in the compact/Schwartz test space, the weak dual identity
V(t)†phi-phi=i integral_0^t V(s)†Hformal phi ds
is an H-valued Bochner identity. It proves that the generator agrees
with the formal expression on these tests. It does not prove they are
an operator core or that actual-u snapshot domains are strongly transported.

K=131072 is an actual negative-g example now covered.
The earlier high-frequency negative-energy test still correctly proves
lack of semiboundedness, but no longer blocks finite-K unitary evolution.
No passage through g=0, full K limit, unique physical ordering, general
spatial constraints, or apparatus has been supplied.
