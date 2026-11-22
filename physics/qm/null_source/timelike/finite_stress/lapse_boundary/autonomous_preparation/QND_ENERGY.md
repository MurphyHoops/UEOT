# AF. An exact autonomous record of the Z system's conserved energy

## AF1. Target, two preparations and the declared coarse calibration

Here use the original Z Hamiltonian instance H=H_(M=1), c_r=0, with its
outside packet b_2(x)=u(x+2)exp(i10x) on [-2,-1].
This entry is a DIFFERENT apparatus and target from AD.
Its variable code is the source k=1 vacuum (code 0) or one quantum (code 1).
The probe and all high modes are vacuum in both codes.

Both full Z vectors are in D(H). Because r=0 throughout the initial support,
the exact first two spectral moments give
mu_0=56, mu_1=57, Var_0(H)=Var_1(H)=1290.
For B_c=H-113/2,
<B_c>_0=-1/2, <B_c>_1=+1/2,
<B_c^2>_0=<B_c^2>_1=m2=5161/4.                       (AF1)
This uses only moments; it does NOT assert that the complete energy laws
are translates of each other.

Select R=m2=5161/4 once, and let
C_R(b)=clip(b,-R,R),
w_R(E)=[1+C_R(E-113/2)/R]/2,
theta(E)=arcsin sqrt(w_R(E)).                          (AF2)
Theta is continuous and bounded in [0,pi/2], not asserted smooth.
This is an explicitly calibrated BINARY record of the entire Z generator
H (controller + source + probe), in Z's fixed ESU/subtraction convention.
It is not a measurement of a source-only Hamiltonian or of the later
combined apparatus H_Q.

The scalar inequality
|b-C_R(b)|<=b^2/(4R)
follows from (|b|/R-2)^2>=0 outside the clipping interval.
It implies the complete record probabilities will have
p_1-p_0 >=1/(2R)-m2/(4R^2)=1/5161>0.                 (AF3)
A bit converted to E_est=113/2+R(2j-1) has, conditional on energy E,
mean 113/2+C_R(E-113/2) and variance R^2-C_R(E-113/2)^2.
This is a coarse bounded energy response, not a high-precision estimate
or a sharp repeatable energy measurement.

## AF2. Same exact clock, new source-containing autonomous Hamiltonian

Use AD's clock chi(y)=u(y+2), h_R=p_y^2/2+(2pi)^2(y+1/2)^2/2,
F=0 on y<=-1 and F=1 on y>=0, with the same C3 transition.
There is no LO in this apparatus.
Define
G_Q=theta(H) tensor sigma_y,
U_Qrecord=exp(-iG_Q),
W_Q(y)=exp[-iF(y)G_Q],
H_Q=W_Q[H+h_R]W_Q^dagger.                             (AF4)
The entire Z generator H strongly commutes with G_Q and H_Q.
The clock kinetic energy is the FULL (p_y+F'G_Q)^2/2.
The global spectral coupling is source-containing; it is not an
independent additive carrier. Its boundedness provides a legitimate
normal operator construction, not a local covariant action.

The preparation is the original Z code tensor chi tensor |0>_R.
W_Q=I on its clock support, so it is a normal product state in D(H_Q).
At T=1/2 the clock is reflected to [0,1] exactly. The actual endpoint is
chi_T tensor exp[-i theta(H) tensor sigma_y]
                  [exp(-iTH)psi_code tensor |0>].     (AF5)
No externally switched interaction or successful-arrival condition is
substituted for the autonomous H_Q evolution.

Define the ACTUAL cutoff family with
G_Q,K=theta(H_K) tensor sigma_y,
W_Q,K=exp[-iF G_Q,K],
H_Q,K=W_Q,K[H_K+h_R]W_Q,K^dagger.                     (AF6)
The continuous bounded functional calculus of Z's strong-resolvent limit
gives theta(H_K)->theta(H) strongly; W_Q,K and their adjoints converge
strongly by dominated y integration. Their actual propagators and normal
bounded instruments therefore converge. This is not the false identity
theta(P_K H P_K)=P_K theta(H)P_K.

## AF3. Complete instrument and exact nonselective energy accounting

Project the physical bare register on j=0,1 at T=1/2, keeping both outcomes.
The exact instrument on the WHOLE Z system is
I_0(rho)=cos(theta(H)) exp(-iTH)rho exp(iTH) cos(theta(H)),
I_1(rho)=sin(theta(H)) exp(-iTH)rho exp(iTH) sin(theta(H)). (AF7)
It is normal, completely positive and complete. If the variable input
is only the source, first tensor the fixed controller/probe environment
and then trace it; do not rewrite these as functions of H_source.

Both Kraus functions commute with H. Hence the entire Z energy law is
unchanged by the nonselective output. Individual conditioned laws are
Bayesian reweightings, with every outcome retained in the unselected map.

There is also an exact statement about the COMPLETE apparatus energy H_Q.
On the endpoint clock support, W_Q^dagger P_j W_Q equals the y-independent
A_j^out=U_Qrecord^dagger P_j U_Qrecord.
These projections commute with H+h_R and sum to I. Thus for every bounded
Borel f, the nonselective endpoint projection preserves <f(H_Q)> exactly.
This proves preservation of its entire spectral law for the DECLARED
clock preparation. It does not assert [P_j,H_Q]=0 on the full Hilbert space,
and the calibrated effect w_R(H) is not generally w_R(H_Q).

The clock mean and variance are AE's exact values
E_R=6+45pi^2/22,
Var_R=90-6pi^2/11+577pi^4/1573.
The two complete initial H_Q means are respectively
62+45pi^2/22 and 63+45pi^2/22,
and both variances are
1380-6pi^2/11+577pi^4/1573.                             (AF8)
They remain exactly the same through both autonomous evolution and the
complete nonselective endpoint instrument. No apparatus energy is dropped.
The initial clock is H2; these are second spectral moments, not a claim
of D(h_R^2) or arbitrarily high moments.

## AF4. The complete Z state changes, with a quantitative upper bound

The nonselective map preserves energy probabilities but can remove energy
coherences. For these code inputs one can bound the actual change relative
to the UNREAD state rho_T=exp(-iTH)rho exp(iTH).
The identity
theta(E)=pi/4+(1/2)arcsin clip((E-113/2)/R,-1,1)
gives |theta(E)-pi/4|<=pi|E-113/2|/(4R).
Compare the actual memory isometry with a fixed pi/4 register rotation.
For either code, including a purifying reference if desired,
D_half(I_0(rho)+I_1(rho),rho_T)
 <=pi sqrt(m2)/(4R)=pi/(2sqrt(5161))<.022.              (AF9)

For each of the two PURE code inputs the change is strictly positive.
Z's lower bound is above the lower plateau threshold -4935/4.
The means 56 and 57 exclude support wholly on the upper plateau
[5387/4,infinity). If theta's spectral law were constant at an interior
value, strict monotonicity would force Var(H)=0, contradicting 1290.
Thus theta's law is nonconstant, and
Fidelity_with_unread_pure_state
 =<cos theta>^2+<sin theta>^2=|<exp(i theta)>|^2<1.
The unread rank-one projection therefore gives a strictly positive
half-trace-distance lower bound 1-|<exp(i theta)>|^2.
No numerical positive lower bound is computed here.

This is strict change of the entire Z state, not necessarily of its
source-only marginal. General mixed energy-diagonal states can remain
unchanged, so the pure-state argument must not be extended to them.

The actual joint target-energy/bit law is
mu(dE)[w_R(E)delta_1+(1-w_R(E))delta_0].
Monotonicity and the nonconstant w_R law imply
Cov(H,J)=(1/2)int int (E-E')(w_R(E)-w_R(E'))dmu(E)dmu(E')>0.
Let p=<J>. The lower spectral bound makes w_R bounded below by a positive
constant, while the means exclude the upper plateau, so 0<p<1.
The J=1 posterior law is equivalent to the nondegenerate original energy
law. The optimal affine energy predictor therefore has
0<1290-Cov(H,J)^2/[p(1-p)]<1290.
This is a strictly improved INFERENCE mean-square residual. The actual
nonselective physical variance of H is still 1290. J is a memory bit,
not a geometric charge. No numerical covariance or residual is computed.

The full apparatus energy can also be included without dropping the clock.
In the POST-INSTRUMENT classical--quantum output, let epsilon denote a
clock-energy value with law nu_R. For every bounded f,
Tr[f(H_Q) P_j rho_endpoint P_j]
 =int int f(E+epsilon) w_j(E) dmu(E) dnu_R(epsilon).
Consequently the post-record covariance of complete energy and J equals
Cov(H,J)>0, while Var(H_Q)=1290+Var_R is unchanged. The best binary
prediction mean-square residual for complete energy is
Var_R+[1290-Cov(H,J)^2/(p(1-p))],
strictly between Var_R and Var_R+1290.
The independent clock fluctuation is an explicit positive floor in THIS
declared preparation and record. This is a post-instrument sequential
statistic, not a joint spectral law of pre-projection bare P_j and H_Q,
and it does not provide a universal response w_R(H_Q).

## AF5. Closure and the gravitational/locality boundary

This comparison closes normal outside preparation, autonomous finite-time
writing, complete calibrated Z-energy record, actual cutoff limit, and
exact nonselective COMPLETE energy conservation in one declared global
apparatus model. Its gap is >=1/5161, in model units.

It does not prove the old M=1 physical-P probe-collision gain; it uses a
different global theta(H) apparatus and different code states. Without
the T=1/2 projection, the full-period unitary at T=1 returns the clock
to F=0 and uncomputes the register. A permanent classical record is not
supplied by this closed unitary alone.

The final Born projection has a normal, energy-balanced instrument here;
its local macroscopic mechanism has not been constructed.
H is the fixed ESU, free-vacuum-zero, c_r=0 generator. No identification
with a geometric constraint charge is made.

For a varying metric/lapse, delta theta(H) cannot in general be replaced
by theta'(H)delta H. The variations need operator-functional derivative
and domain control; clipped theta is not even scalar smooth at the ends.
Consequently one cannot add the old stress to a bare clock stress and
claim the new complete gravitational source. The local covariant action,
total renormalized stress and joint Einstein constraints remain OPEN.
