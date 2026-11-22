# A fixed controlled gate: all normal pointer states and the recovery frontier

The predecessor's incoming-energy preparation is a genuine normal toy
instrument. Its delta=1e-6 source marginal preserves the stated stress
algebra restriction. This page tests what happens if that **same gate**
is asked to pay the physical mean-recovery resource of MEAN_RECOVERY.
It allows any independent normal pointer state, not just Gaussians.

## P1. Exact pullback and source-intrinsic fluctuation

Fix the original source rho_S,K, B=A delta H_in,K, h=h_i>0 and
U_B=exp[-i Q_g B/h]. The test observable is still
\(\mathcal A=hP_g+H_{i,K}\), not the original P_u constraint.
Under t=Q_g/h the exact pulled-back self-adjoint realization is
\[
 \widehat{\mathcal A}=-i\partial_t+R(t),\quad
 R(t)=e^{itB}H_{i,K}e^{-itB}-B
     =R_0(t)+tR_1+t^2R_2,                                  \tag{P1}
\]
\[
 R_1=-h'\mathsf D+(h/A^2-h'I_i)\mathsf P,\qquad
 R_2=-h'\mathsf P/(2A^2).
\]
R0 contains the finite nonzero-mode pair terms with their actual phases.
They are not deleted; its source GNS norm is uniformly bounded in t.

Purify the independent normal input as f(t) tensor v, with
v=rho_S^(1/2) (equivalently its finite rank-two purification); f may be
vector valued to purify an arbitrary mixed pointer. Project onto the
source subspace perpendicular to v. For any real mean shift a, on compact
time tests the distribution identity is
\[
 P_\perp(\widehat{\mathcal A}-a)(f\otimes v)
                  = f(t)\otimes\delta R(t)v.                \tag{P2}
\]
All pointer derivatives, phases and scalar mean shifts lie in the v
direction and disappear under this bounded projection.

This argument does not assume f belongs separately to H1. Start with the
concrete self-adjoint pullback U_B† A U_B. If its second moment is finite,
the left side of P2 is L2; the local distribution identity is valid since
B preserves the finite-mode Schwartz source on compact t intervals.
Thus no cancellation between an unbounded derivative and a source term
can evade
\[
 \operatorname{Var}_{out}\mathcal A
       \ge \int\|\delta R(t)v\|^2\,d\mu(t).                 \tag{P3}
\]
This holds for arbitrary pointer mixtures and phases, but requires the
initial source-pointer independence just specified.

## P2. Actual, nonzero quadratic coefficient

Let s2=||delta R2||_2, s1=||delta R1||_2,
s0=sup_t||delta R0(t)||_2. From the current two-branch thin energy law,
with epsilon_2=sqrt(3)/A,
\[
 s_2^2=A^2 h'^2
       [\sigma_{\rm thin}^2\mu_2+4p(1-p)\epsilon_2^2].
\]
The original total energy branch law is narrow, but the zero energy alone
also carries its shell correlation; the extra positive term is retained.

A direct bound on the normalized bump gives
mu2>=exp(-2/3)/64>1/128: bound its denominator by 2 exp(-2), and integrate
x² exp[-2/(1-x²)] over |x| in [1/4,1/2].
SOURCE_BUDGETS then yields
\[
 s_2>100h,\qquad s_1<e^{-1122},\qquad s_0<e^{-1098}.          \tag{P4}
\]
For s1 use the explicit R1 coefficients and W7. For s0 use the already
source-bound Hi-B estimate; the pair phases preserve its number-grade
norm. Finite K truncation does not increase that norm.

Since s2>0 and R0 is uniformly bounded, for all sufficiently large |t|
one has ||delta R(t)v||>s2 t²/2. Hence finite output residual second moment
itself forces E t⁴<infinity. This is a consequence, not an extra tail
assumption imposed on the pointer. Put x=(E t⁴)^(1/4); reverse triangle gives
\[
 \operatorname{RMS}_{out}\mathcal A
 \ge s_2x^2-s_1x-s_0.                                     \tag{P5}
\]
Here RMS is the centered standard deviation. Any noncentered RMS is at least
as large; arbitrary mean calibration does not remove P5.

## P3. Mean recovery and pointer residual cannot both pass for this gate

SOURCE_BUDGETS gives q2,out<1e19+2e15 x+1e12 x². On the positive-confining
K=65536 branch, recovery of m=h and the old P_u mean budget requires
q2,out>=1/(100h²). If x<=1/(1e8 h), then
\[
 h^2q_{2,out}<10^{19}h^2+2\,10^7h+10^{-4}<10^{-2},
\]
a contradiction. Therefore x>1/(1e8 h).
On that interval the quadratic in P5 is increasing and P4 implies
\[
 \boxed{\operatorname{RMS}_{out}\mathcal A
        >5\,10^{-15}/h>\exp(19940).}                       \tag{P6}
\]
Thus the same original source, arbitrary independent normal pointer, and
this fixed U_B cannot simultaneously provide the necessary source resource
for original-geometry mean recovery and a small actual toy residual.
In particular, changing a Gaussian into a specially phased or mixed
pointer does not repair this preparation family.

P6 is not an identification P_g=P_u and not a proof about all interactions.
The source marginal after this gate may be embedded in some other joint
geometry state only if that state passes its own action/domain/constraint
checks. This page states a necessary marginal-resource test, not such an
embedding. The source, controller and apparatus stress of a local autonomous
implementation are still missing.

## P4. Gaussian comparison and a reusable finite-resource inequality

For the old real Gaussian, v_t=1/(4delta²). The exact conditional source mean is
r1 t+r2 t², where r1=2A Ez(h-A²h'I_i), r2=-A h'Ez.
The symmetric pointer-derivative cross vanishes, so
\[
 \operatorname{Var}_{out}\mathcal A
 \ge\delta^2+\frac{r_1^2}{4\delta^2}
              +\frac{(Ah'E_z)^2}{8\delta^4}.               \tag{P7}
\]
The minimum of only the first and last terms is
3|Ah'Ez|^(2/3)/2^(5/3), at delta=(|Ah'Ez|/2)^(1/3).
This optimizes a lower bound, not the entire variance or a general device.
It explains why the old accurate finite-delta toy result cannot be
extrapolated to a free zero-residual limit.

More generally, if a necessary source budget Qreq exceeds Q0, S5 forces
\[
 x\ge x_{\min}=\frac{2(Q_{\rm req}-Q_0)}
 {J_0+\sqrt{J_0^2+4L_0(Q_{\rm req}-Q_0)}}.
\]
When the right side of P5 is increasing on x>=x_min, it gives a direct
preparation-resource/residual frontier. This is a gate-specific necessary
bound with actual source data, not a universal optimum.
