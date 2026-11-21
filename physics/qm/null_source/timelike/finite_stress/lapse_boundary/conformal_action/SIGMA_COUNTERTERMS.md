# Q. The complete flat four-gradient heat tensor and retained-lapse contacts

## Q1. From a nonzero witness to the actual tensor

Use physical target fields and the same metric as SIGMA_UV_GATE.
In the orthonormal coframe

 e1=dchi, e2=sqrt(1+k_c)dphi_+, e3=sqrt(1-k_c)dphi_-,
 phi_+=(phi+psi)/sqrt(2), phi_-=(phi-psi)/sqrt(2),

the sectional curvatures are
A=K12=-k_c''/[2(1+k_c)]+k_c'²/[4(1+k_c)²],
B=K13= k_c''/[2(1-k_c)]+k_c'²/[4(1-k_c)²],
C=K23=k_c'²/[4(1-k_c²)].
These are coframe components, not a claim of global orthonormal
coordinate functions.

Put v_mu^a=e^a_A partial_mu X^A and S_ab=v_mu^a v^{mu b}.
For D=-(nabla²+E) the target-curvature endomorphism is

 E11=A S22+B S33, E22=A S11+C S33, E33=B S11+C S22,
 E12=-A S12, E13=-B S13, E23=-C S23.                   (Q1)

The pullback curvature obeys

 tr Omega_mu nu Omega^mu nu
  =-4[A²(S11S22-S12²)+B²(S11S33-S13²)+C²(S22S33-S23²)].

Thus, apart from total derivatives, the COMPLETE flat four-gradient
heat density is

 a4_four=(4pi)^-2 {
  (1/2)tr E²
  -(1/3)[A² det S12+B² det S13+C² det S23] }.           (Q2)

The fixed-sign statement applies only to rank-one homogeneous
gradients, where all wedge terms vanish and tr E² is a sum of
squares. No arbitrary-background positivity assertion is made.

On curved spacetime the same a4 formula also gives
(R_g/6)tr E, with tr E=Ric_target(partial X,partial X),
plus three copies of the scalar pure-curvature part
[5R_g²-2Ric_g²+2Riem_g²]/360, and total derivatives
Box(tr E)/6+3 Box R_g/30.
The latter cannot be discarded on finite initial/final hypersurfaces
without their boundary/state treatment. This lists necessary bulk
data; it does not supply a full finite-boundary renormalization theorem.

The finite coefficients of all allowed operators require stated
renormalization conditions. The divergent tensor does not determine
their finite values, and no symmetry/UV fixed point is assumed for
the current compact bump metric.

## Q2. Exact homogeneous lapse row of any quartic gradient term

Let F4(X,v) be any homogeneous quartic polynomial in physical
velocities v=DX, with the appropriate target tensor coefficients.
The covariant homogeneous density is N V F4(X,v), independent of a
before Legendre transformation. Euler's identity gives

 Pi_A=V F4_vA,
 E4=v.Pi-VF4=3VF4,
 Gamma_N=-3VF4, Gamma_u=0,
 Theta4=Pi_A delta X^A.                                (Q3)

At fixed coordinate velocities X', the primitive lapse/velocity
contacts are

 S_NN=12V F4/N,
 S_N,X'_A=-3V F4_vA/N,
 S_X'_A,X'_B=V F4_vAvB/N.                              (Q4)

Field-coordinate derivatives of F4 supply the other mixed contacts.
On each CTP branch they arise from that branch's single action;
there is no primitive mixed-plus/minus action contact.

Standalone quartic stress is rho4=3F4/a⁴, p4=F4/a⁴ at fixed
velocities. This is not the pressure of a quartic canonical
Hamiltonian correction at fixed total momenta.
For L2=Va² G(v,v)/2 and a first-order added VF4,
fixed-momentum stationarity gives

 delta T=-VF4(v0), delta rho=-F4(v0)/a⁴,
 delta p=-3F4(v0)/a⁴.                                 (Q5)

Indeed the velocity correction changes the quadratic stress by
-4F4/a⁴; adding the direct quartic pieces gives (Q5).
This derivation avoids assigning a fluid exponent to an isolated
Hamiltonian term while omitting the corrected quadratic stress.
It is a first-order comparison, not a globally positive exact
truncated Hamiltonian.

## Q3. What has now been closed

The full flat-space divergent four-gradient tensor and its complete
homogeneous primitive lapse/velocity contact structure are explicit.
The required curvature--matter term is derived in MIXED_ACTION and
cannot be absorbed into a source-independent geometry noise.

Still open: finite coefficient values, all curved-space/boundary
renormalization, common quantum domains and normal initial states
for the completed action, and a controlled approximation of the
previous bare homogeneous apparatus by that completed theory.

Primary derivations inspected: Vassilevich hep-th/0306138, (4.28);
Codello--Percacci 0810.0715, arbitrary-dimensional sigma Hessian (3);
Percacci--Zanusso 0910.0851, general two-/four-derivative action (5).
Their special symmetric-target fixed-point results are not imported.
