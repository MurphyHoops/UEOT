# Y. A locally subtracted actual two-branch phase for the homogeneous field probe

## Y1. Scope and actual mode problem

This closes the scalar-phase gate for X's spatially constant
smooth mixing potential on the FIXED unit Einstein cylinder.
It does not close U's inhomogeneous lapse phase, a changing
metric determinant or any joint Einstein constraint.

Take r in C_c^infinity((0,T)), real; the concrete X pulse has
T=.2, |r|<=.2. After the fixed source/probe rotation, each
S3 mode k, multiplicity k^2, obeys

 y_V''+(k^2+V(t))y_V=0, V=+r or -r,
 y_V(0)=1, y_V'(0)=-ik.
 For t>=T, y_V=a_V,k e^(-ikt)+b_V,k e^(ikt).             (Y1)

These are the actual mode solutions of the local action.
Their Wronskian gives |a|^2-|b|^2=1.
The finite-K quadratic Hamiltonians exist, but we do not
assume their unsmeared infinite-mode expression is a common
old-vacuum-domain self-adjoint generator.

## Y2. A controlled WKB comparison, not a formal series

Use a coupling homotopy V=+s r or -s r, 0<=s<=1.
Let M_j be finite upper bounds for ||r^(j)||infinity, j=0,...,4.
Define homotopy-uniform triangle bounds

 F_j=M_j/2 (j=0,1,2),
 G0=(M0^2+M2)/8,
 G1=(2M0M1+M3)/8,
 G2=(2M1^2+2M0M2+M4)/8.                                (Y2)

For the actual V put f=V/2, g=-(V^2+V'')/8 and
W_k=k+f/k+g/k^3.
Choose k0>=1 so F0/k0^2+G0/k0^4<=1/2.
Then W_k>=k/2 for k>=k0 and

 y_app(t)=(k/W_k(t))^(1/2) exp[-i integral_0^t W_k].
 y_app''+(k^2+V)y_app=-R_k y_app,
 R_k=W_k^2-k^2-V+W_k''/(2W_k)-3(W_k')^2/(4W_k^2).

The order-k^-2 terms cancel because
f^2+2g+f''/2=0. Directly bounding the remaining exact rational
expression, using W_k>=k/2, gives

 ||R_k||infinity <= C_R/k^4,
 C_R=2F0G0+G0^2+F2(F0+G0)+G2+3(F1+G1)^2.               (Y3)

No cancellation in a norm evaluated only at s=1 is assumed;
(Y2) applies uniformly to both signs and the whole homotopy.

All pulse jets vanish near the endpoints, so y_app has exactly
the initial data in (Y1) and W_k(T)=k, W_k'(T)=0.
Let e=y_V-y_app. In the normalized pair (e,e'/k), free
oscillation is a norm-preserving rotation. The remaining
linear coefficient is bounded by M0/k and the forcing by
sqrt(2) C_R/k^5. Volterra's formula and Gronwall give

 sup_(0<=t<=T) ||(e,e'/k)||
       <= C_A/k^5,
 C_A=sqrt(2) T C_R exp(T M0/k0).                        (Y4)

The exact endpoint extraction
a=e^(ikT)(y+i y'/k)/2, b=e^(-ikT)(y-i y'/k)/2
therefore yields

 a_V,k=exp[-i integral V/(2k)+i I2/(8k^3)]+O(C_A/k^5),
 |b_V,k|<=C_A/k^5, I2=integral r^2,                     (Y5)

uniformly over the two signs and s, with I2 replaced by s^2I2
on the homotopy. The integral of V'' vanishes exactly.

## Y3. Continuous metaplectic phase and a summable field limit

In interaction picture relative to the free ESU evolution,
one oscillator's actual vacuum amplitude is
(conjugate(a_V,k))^(-1/2), with the continuous metaplectic lift.
Let G_k be the product for V=+r and V=-r.

Choose k1>=k0 with C_A/k1^5<=1/2. For these high modes the
relative a/a_app lies within a half-unit disk around one
for the ENTIRE coupling homotopy. Hence the continuous log
equals the small-disk log and |Log(1+delta)|<=2|delta|.
The actual quadratic unitary is continuous on the (s,t)
rectangle and starts at the free unitary; this identifies the
homotopy branch with its time metaplectic lift. Low modes keep
their actual continuous branches. No endpoint principal square
root is substituted without controlling winding.

The two O(1/k) phases cancel between +r and -r, leaving

 log G_k = i I2/(8k^3)+epsilon_k,
 |epsilon_k| <= 2C_A/k^5, k>=k1.                        (Y6)

This is an error bound for the ACTUAL ODE, not an asymptotic
series used without a remainder. With the actual k^2 degeneracy,

 sum_(k>K) |k^2 epsilon_k| <= C_A/K^2, K>=k1.            (Y7)

All finite lower modes are ordinary normal oscillators.
The explicit finite derivative certificate may give a very
conservative k1 and tail constant; it proves convergence
without claiming that that many modes have been computed.

## Y4. One local counterterm prescription and actual CTP convergence

Let H_K=sum_(k=1)^K 1/k and V0=2pi^2.
The free-phase-removed cutoff vacuum amplitude is
G_K=product_(k<=K) G_k^(k^2). Its logarithm has the actual
divergence +i I2 H_K/8.

Choose one real finite coefficient c_r and the Lorentzian
local action term

 S_ct,K=[-H_K/(16pi^2)+c_r] integral sqrt(-g) r^2
       =-H_K I2/8+c_r V0 I2.                           (Y8)

Then

 exp(i S_ct,K) G_K -> G_ren
 =exp[i c_r V0 I2+
               sum_(k>=1) k^2(log G_k-iI2/(8k^3))] != 0. (Y9)

The high-mode sum is absolutely convergent with (Y7).
Using log K instead of H_K is another finite prescription;
the Euler-constant shift must be carried in c_r.
The certificate's illustrative prescription is c_r=0 in
the H_K scheme. It is a declared finite input, not an
experimentally measured or uniquely required value.

X already proved convergence of the actual finite-K
positive-vacuum-overlap implementers W_K and their adjoints.
The actual interaction-picture unitary differs by its
vacuum amplitude's phase:
U_K^I=(G_K/|G_K|)W_K.
Since (Y9) is nonzero,

 exp(i S_ct,K) U_K^I -> U_ren, and adjoints, strongly.    (Y10)

Therefore for any fixed normal source-probe/reference density,
or a trace-norm-convergent cutoff preparation, the actual
two-branch kernels
U_ren,K(r_+) rho_K U_ren,K(r_-)^dagger
converge in trace norm.
They give normalized, conjugate-symmetric positive Gram
influences and complete bounded instrument limits.
For arbitrary normal inputs the influence trace may vanish;
nonzero vacuum Gaussian overlaps are a separate statement.
This is actual finite-amplitude normal CTP convergence within
the fixed-background, spatially constant pulse family.

The O(k^-5) estimate in this entry proves the required HS and
phase-tail facts. The ALL energy-moment statement in X comes
from Hadamard smoothness and W, not from expanding this one
finite-order estimate beyond its stated strength.

## Y5. Counterterm contacts, controller work and what remains open

The subtraction in (Y8) matches the independently computed
paired heat coefficient delta a4=r^2/(16pi^2) in X.
It is a local mixing-potential vacuum counterterm; common
free geometric phases have already been removed.
This agreement is established on the specified ESU histories.

Retaining the lapse, S_ct=int N sqrt(h)c_K r^2 gives

 Gamma_N,ct=sqrt(h)c_K r^2,
 Gamma_r,ct=2N sqrt(h)c_K r,
 Gamma_Nr,ct=2sqrt(h)c_K r,
 Gamma_rr,ct=2N sqrt(h)c_K,
 T_ct,mu nu=c_K r^2 g_mu nu.                            (Y11)

The mixed composite, work Ward identity and stress must use
the same subtraction and the same finite c_r.
Different c_r values leave the single-history measurement
channel unchanged but change cross-history phases, response,
controller work bookkeeping and the gravitational source.
The measurement does not by itself determine c_r.

This result is not a proof for general spatial r(t,x), does
not complete the gravitational lapse/Weyl phase in U/T,
and supplies neither a dynamical controller producing r
nor a solution of the metric constraints. It does close
one genuine nonlinear-in-amplitude source-probe phase gate
that channel normality alone left open.

The proof uses elementary oscillator comparison and the
finite-mode metaplectic convention already independently
checked in T. The local heat coefficient is cross-checked
against Vassilevich's Eq. 4.28, as recorded in X.
