# AB. An outside product preparation and an actual autonomous full-field record

## AB1. One declared Hamiltonian family; a new parameter is not the old example

Use Z's actual semibounded H_M and canonical H_M,K on the fixed unit ESU,
with c_r=0 and
r(x)=(1/5) exp[4-1/(x(1-x))] on (0,1), zero outside.
Its controller kinetic term is p_x^2/(2M); its full field, interaction,
r^2 harmonic counterterm and finite vacuum potential e(x) are retained.

M>0 is chosen once before preparation. This is the SAME Z Hamiltonian
family and subtraction, but M different from 1 is a different operator.
No result below claims that Z5's previously fixed M=1,p=10 example has
passed. The coarse existence example in this entry uses M=10^16.
AC sharpens the proof and fixes the final working example at M=10^12.

Let u(z)=sqrt(630) z^2(1-z)^2 for 0<z<1, zero otherwise, and
b_delta(x)=delta^(-1/2) u((x-X0)/delta+1/2) exp(i M v x),
X0=-3/2, v=5, 0<delta<=1.
Prepare the source k=1 coherent state with q mean +1 or -1 and p mean 0.
The probe and all other source modes are in the free ESU vacuum.
This is a genuine outside-coupling PRODUCT preparation: r=0 throughout
the controller support. Both codes share the same controller/probe
environment. The two coherent source states are not orthogonal.

The envelope has zero value and first derivative at its endpoints, so
b_delta is H2 and the full input belongs to D(H_M). It need not be in
D(H_M^2). Exact envelope integrals are
int u^2=1, int (u')^2=12, int (u'')^2=504,
int (z-1/2)^2 u^2=1/44.
Consequently the mean and variance of the TOTAL H_M spectral energy are
E=M v^2/2+6/(M delta^2)+1/2,
Var(H_M)=12 v^2/delta^2+90/(M^2 delta^4)+1/2.             (AB1)
The variance is a second spectral moment on D(H_M).
Joint parity of the two low source/probe modes relates the two codes
and commutes with H_M, so their entire total-H spectral laws coincide.
Their sign record is not a total-energy or geometry-charge measurement.

## AB2. Actual finite-cutoff trial and its number-moment control

Everything in the comparison is first derived at the ACTUAL finite K.
Write W_K(x) for Z's squeeze, A_K=W_K^dagger W_K',
D_K(x)=dGamma(omega_K(x)) and e_K for the same renormalized scalar potential.
The higher free spectator modes stay vacuum. Put X(t)=X0+vt and
b_t=exp[-it p_x^2/(2M)]b_delta.

Let U_cl,K be the ordinary finite-field evolution for r(X(t)), INCLUDING
e_K and the same counterterm phase; it is used only as a comparison.
Define Phi_K(t)=W_K(X(t))^dagger U_cl,K(t) psi_code and
Psi_trial,K(t,x)=b_t(x) W_K(x) Phi_K(t).
Then
i Phi_K'=[D_K(X)+e_K(X)-i v A_K(X)] Phi_K.               (AB2)
This does not prescribe the actual controller path. The actual evolution
remains exp(-it H_M,K); its distance from this trial is bounded below.

Let h=Nop+2 and c(x)=||theta'(x)||_l2, including both signs and k^2
multiplicity. For the pair operators, the ordinary Fock estimates give
||A psi||<=c ||h psi||,
||A' psi||<=c2 ||h psi||,
||A^2 psi||<=2 c^2 ||h^2 psi||.                         (AB3)
The number shifts by two imply
||[h,A]psi||<=2c||h psi||,
||[h^2,A]psi||<=6c||h^2 psi||.
Since D commutes with h, Gronwall applied to (AB2) gives
q1=||h Phi_K||<=exp(2L) sqrt(27)/2<5,
q2=||h^2 Phi_K||<=exp(6L) sqrt(1025)/4<40,
L=int_0^T |v| c(X(t))dt<=pi/(8 sqrt(3)), T=1/2.        (AB4)
The initial total number is Poisson with mean 1/2. The constants 27/4
and 1025/16 are its exact h^2 and h^4 moments.

The bound on L follows from
c(x)<=|r'(x)| pi/[4 sqrt(3)(1-r_*)],
int_0^1 |r'| dx=2r_*, r_*=1/5.
These are moments of the REFERENCE Phi_K, not a claim that the actual
interacting field remains Gaussian or has these same number moments.

For completeness, the elementary pair estimates used in (AB3) agree with
Bruneau--Derezinski, "Bogoliubov Hamiltonians and one-parameter groups of
Bogoliubov transformations", J. Math. Phys. 48, 022101 (2007), Section II.B,
Proposition 2.2. The number-shift and model-specific bounds here are derived
directly; that paper does not prove this controller model.
https://www.esi.ac.at/preprints/esi1832.pdf

## AB3. All-mode residual, including the connection and vacuum force

Let xi_t=(partial_x-iMv)b_t. Direct differentiation, with the squeeze
sign convention in Z, gives the exact finite-K residual
(i partial_t-H_M,K)Psi_trial,K
=W_K { b_t[D_K(X)-D_K(x)+e_K(X)-e_K(x)
                 +i v(A_K(x)-A_K(X))]Phi_K
        +xi_t A_K(x)Phi_K/M
        +b_t[A_K'(x)+A_K(x)^2]Phi_K/(2M) }.            (AB5)
In particular the A', A^2 and e_K terms are present.

The exact free packet variance and centered derivative norm are
Delta_t^2=||(x-X(t))b_t||^2
         =delta^2/44+12t^2/(M^2 delta^2),
||xi_t||=sqrt(12)/delta.                               (AB6)
Using the weaker Delta_t<=delta+2/(M delta) on [0,1/2] suffices for
a first existence estimate. Uniform coarse coefficient bounds are
||r'||<=3.2, ||r''||<=147.2,
sup||theta'||_l2<2, sup||theta''||_l2<100,
sup_k |omega_k'|<2 and sup|e_K'|<1.
The r'' bound follows by writing y=1/[x(1-x)]>=4 and bounding
(1/5)e^(4-y)(y^4-6y^3+6y^2) term by term.
The derivative of e_K is uniformly summable as k^-5, not the derivative
of an unsubtracted divergent vacuum sum.

Equations (AB3)--(AB6) then give
||residual|| <=2600 Delta_t+40/(M delta)+500/M.
Integration for T=1/2 yields
epsilon_dyn<=1300delta+2620/(M delta)+250/M.
Although X(T)=1 and W_K(1)=I, b_T is not supported at one point.
The endpoint frame MUST be removed:
||(W_K(x)-I)Phi_K(T)||<=10 |x-1|,
epsilon_frame<=10delta+20/(M delta).
Thus the total vector error is bounded by
epsilon_coarse=1310delta+2640/(M delta)+250/M.           (AB7)

At every finite K, b_t is H2 and the finite-mode Gaussian vector has
all number moments. The trial is in the actual operator domain, so
Duhamel is legitimate there. We do NOT assume that its infinite-mode
version is differentiable in a bare free-energy domain, or that A Phi
has finite field energy. Apply the estimates at finite K and then use
Z's actual strong propagator limit on the fixed outside input.

After tracing to the two low modes, the reference is K-independent.
The half trace distance between the actual low output and this reference
is therefore <=epsilon_coarse. This conclusion does not require an
unproved interchange of an infinite derivative and a field limit.
Y also supplies the reference's full renormalized endpoint phase limit,
but the low-mode record bound already follows from the finite-K estimates.
The common scalar phase was retained when deriving every residual.

## AB4. A strictly positive complete record in a positive time

The reference low-mode equations are y'=(A0+r(X(t))B)y,
y=(q_s,p_s,q_p,p_p), with free orthogonal rotations and ||B||=1.
Let I=int_0^T r(X(t))dt<=1/25.
For source mean (1,0,0,0), the first-order physical probe P=p_p mean is
m1=-int_0^T r(X(t)) cos(t) cos(T-t)dt.
On x in [1/4,3/4], r>=exp(-4/3)/5; dt=dx/5, so
|m1|>=exp(-4/3) cos(1/2)^2/50.
The remainder of the actual finite-dimensional Dyson solution obeys
|m-m1|<=exp(1/25)-1-1/25.
Define
m_*=exp(-4/3) cos(1/2)^2/50-[exp(1/25)-1-1/25]>0.       (AB8)
Also |m|<=exp(1/25)-1<.05 and Var(P)<=exp(2/25)/2.
This is a controlled bound on the actual reference ODE, not a truncated
series asserted without its remainder. No ODE integration is executed.

The complete Gaussian P instrument has
M_z=(2 pi sigma^2)^(-1/4) exp[-(z-P)^2/(4sigma^2)].
Keep every z outcome and optionally apply the stochastic binary score
w(z)=[1+sin z]/2. At sigma=1/10 the binary effect is
E=[I+exp(-1/200)sin P]/2.
The two reference Gaussian means are opposite. Thus their probability
contrast satisfies
d_cl>=exp[-1/200-exp(2/25)/4] sin(m_*)>0.0024.            (AB9)
No free-phase demodulation was hidden: this is physical P at T=1/2.

Each actual code's bounded-effect probability differs from the reference
by at most epsilon_coarse. Therefore
d_actual>=d_cl-2epsilon_coarse.
For M=10^16 and delta=10^-7, epsilon_coarse=0.000133640000025
and d_actual>0.0021. All are ESU model units, not seconds or SI resources.

The exact normal CP instrument is defined by the fixed product environment,
the actual U_M and M_z for arbitrary normal FULL-source/reference inputs.
The numerical approximation bound is only proved for the specified two
coherent codes (and may be extended under separately stated moment bounds).
It is not an unconstrained diamond-norm approximation.

## AB5. Source change and the remaining physical gate

For the low reference, compare its interaction to free evolution on the
same input. On the free input, ||q_s q_p psi_free||<=sqrt(3)/2.
Duhamel hence bounds the k=1 source half trace distance from its free coherent
state by sqrt(3) I/2<=sqrt(3)/50. The actual k=1 source marginal differs by at
most an additional epsilon_coarse (or AC's improved error).
A nonselective probe-only reader leaves the entire source marginal unchanged.
This is a bounded-state-distance budget, not a bound on unbounded energy
observables and not preservation of the original complete bare state.

This entry closes outside preparation -> actual all-field autonomous
evolution -> complete sign record for one new fixed parameter instance.
It leaves the original M=1 example, an efficient local four-dimensional
controller, physical terminal readout, operator-valued Hadamard/stress
propagation and quantum Einstein constraints OPEN.
