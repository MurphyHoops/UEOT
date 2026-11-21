# A fixed bounded record of the actual initial layer

## W1. Fixed finite-prefix projection

Fix the C5 geometry profile g and low input convention, with
supp g in [a,b], J^2>1+b^2, and the common Xi phase anchor in this
interval. For a fixed M>=J define the isometry FROM THE LOW HILBERT
SPACE

    V_M zeta=g(kappa)e^{i Xi_M(kappa)}
             W_low(kappa)zeta tensor phi_{kappa,[J,M]}.

Its input is not an arbitrary geometry amplitude. The operator

    P_M=(V_M V_M*) tensor I_{>M}

is one bounded joint projection in the fixed bulk Hilbert space for
every K>=M. It contains geometry coherence and only a finite source
prefix. For F_s=exp[is/(2kappa)],

    V_M* F_s V_M=chi(s) I_low,
    chi(s)=integral |g(kappa)|^2 exp[is/(2kappa)]d kappa.

Thus the ideal initial P_M probability is one and its phase-evolved
value is |chi(s)|^2, for every common low density and shared reference.

## W2. Controlled prefix error

Let r_0=(1+b^2)/J^2<1. Uniformly K>=M>=J, the actual C5 isometries obey

    ||V_K-iota_KM V_M|| <= e_M,
    e_M=b^2/[4(1-r_0)sqrt M]
         +3(b-a)(1+b^2)^2/[32(1-r_0)^(5/2) M^2].

The first term follows from the real squeeze
|r_k|<=b^2/[4(1-r_0)k^2], the exact product vacuum overlap, and

    2[1-product cosh(r_k)^(-k^2)] <= sum k^2 r_k^2,
    sum_{k>M} k^-2 <= 1/M.

For the scalar phase tail, Taylor's remainder for (1-x)^(-1/2)
bounds each Xi' remainder by
3(1+b^2)^2/[16(1-r_0)^(5/2)k^3]. Integrate from the common anchor
and use sum_{k>M}k^-3<=1/(2M^2). If the phase anchor lies outside
[a,b], enlarge the interval in the bound.

The initial probability is at least 1-e_M^2 because the comparison
vector lies in the projection range. A normalized pure-state
expectation changes by at most its vector-norm error; purification
gives the same bound for any fixed low mixture. If e_K(s) denotes
the actual complete propagation error from INITIAL_LAYER, then

    Tr rho_0,K P_M - Tr U_K rho_0,K U_K* P_M
       >= Delta(s)-e_M^2-e_M-e_K(s),
    Delta(s)=1-|chi(s)|^2.

## W3. A strictly positive gap with a fixed projection

Choose ordered intervals I_-=[a_1,b_1], I_+=[a_2,b_2] with b_1<a_2
and positive profile masses w_-,w_+. Choose s>0 satisfying

    (s/2)(1/a-1/b)<=pi.

The exact double-integral expression for Delta gives

    Delta(s)>=Delta_0
      =4 w_- w_+ sin^2[(s/4)(1/b_1-1/a_2)]>0.

Choose M once with e_M+e_M^2<=Delta_0/4. Then choose K sufficiently
large that e_K(s)<=Delta_0/4. The actual C5 record decreases by at
least Delta_0/2. The actual C9 record changes at each endpoint by
at most delta_K from RARE_PREPARATION; for delta_K<=Delta_0/8
the same fixed projection has a probability drop at least Delta_0/4.

A numerical bound in the paired certificate uses two identical smooth
normalized bumps with disjoint supports [11/10,13/10] and
[17/10,19/10], each with probability 1/2. Set J=3, s=4 and M=10^6.
No bump quadrature is needed: translation symmetry fixes both masses.
The outward inequalities certify e_M+e_M^2<Delta_0/4. This illustrates
a finite prefix and an eventual positive gap; the propagation constant
is not numerically certified, so it is not a usable numerical K
threshold or an apparatus design.

## W4. Observable and physical scope

P_M is bounded on the physical slice completion identified in
LOCAL_CONSTRAINT. No uniform energy-domain preservation is assumed,
and no derivative of P_M is taken. The raw expression is obtained
by the actual finite-K W_K co-transport and may depend on K, including
high-mode factors. It is not a constructed cutoff-independent local
raw detector.

Geometry multiplication B(kappa) and fiberwise source records commute
with F_s and cannot see this particular phase layer. The coherent
projection detects a density change, not a global scalar phase.
This rejects the declared uniform original-u initial-window gate.
It does not settle fixed positive-u limits or the old fixed interior
time smear. Autonomous preparation, controller stress, local coupling,
calibration and the full Einstein--CTP problem remain open.

## W5. A geometry-only bounded effect exists for every normal limit

Let rho_G be the geometry marginal of any normal joint limit.
It is trace-class of trace one. Since F_s has no point spectrum,
rho_G cannot commute with F_s: a positive eigenvalue of rho_G
would supply a finite-dimensional invariant eigenspace and then an
eigenvector of F_s. Thus D=rho_G-F_s rho_G F_s* is nonzero,
self-adjoint trace class with trace zero. It has a positive eigenpair
(lambda,x). Choose normalized y in C_c^infinity(0,infinity) with
||y-x||<lambda/(4||D||). Then <y,Dy>>=lambda/2.

The one fixed effect |y><y| tensor I_source therefore detects the
actual layer in the complete evolution by trace convergence.
This is an existence result; W1-W3 retain the explicit computable
joint-prefix gap. Geometry-only refers to the fixed bulk partition.
No energy-domain preservation is claimed: the transported source
zero modes can obstruct such a stronger claim. Its raw pullback can
depend on K and source coordinates. It is not a built local probe.
