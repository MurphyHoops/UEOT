# V. A normal old vacuum can fail the new lapse's Hadamard condition

## V1. The new static ground state is Hadamard, with explicit hypotheses

Use precisely U's positive static conformal Klein-Gordon operator,
0<|epsilon|<sqrt(V)/11 and N=1+epsilon Y3. On
M=R x S3 with g_N=-N^2 dt^2+h, smooth N is bounded above and
away from zero. The compact spatial slice is Cauchy: the cones
are uniformly comparable with those of the Einstein cylinder.
The vector partial_t is complete, future timelike and Killing.
The real scalar conformal KG operator is normally hyperbolic
and invariant under this time translation.

The positive elliptic gap established in U supplies the genuine
quasifree stationary ground state with spatial-kernel two-point function

 W_N(t,t')=(1/2)N^(1/2)Omega^(-1)
                   exp[-iOmega(t-t')]N^(1/2).              (V1)

It is a KG bisolution; its positivity follows from the positive
spectral measure. Its full canonical CCR reproduce the causal
propagator, so its commutator vanishes at spacelike separation.
The vacuum is a positive-energy ground state and hence passive.
These are the stationary, bisolution and locality hypotheses of
Sahlmann--Verch, Theorem 5.1, checked individually here.
For the canonically quantized scalar they imply that this selected
ground state's two-point function is Hadamard.

This conclusion uses a theorem about the actual KG field.
It does not follow merely from the Hilbert--Schmidt normality
estimate, and does not apply to arbitrary normal densities,
a fluctuating metric, or the homogeneous device truncation.

## V2. A non-smoothing covariance difference for the OLD initial state

Use the old ESU vacuum's SAME canonical Cauchy covariance on the
new static spacetime, as in T and U. This defines a positive
normal state after the symplectic Cauchy identification, but its
Hadamard property must be checked on the new KG spacetime.

On L2(dV_h), or equivalently half-densities, adopt the principal
symbol convention
sigma([A,B])=(1/i){sigma(A),sigma(B)},
{a,b}=partial_xi a partial_x b-partial_x a partial_xi b.
For D=sqrt(-Delta+1), d=|xi|_h and v_xi=xi_sharp/|xi|.
The Hamilton flow of d follows unit-speed geodesics, so

 sigma_0([D,[D,f]])=-Hess_h f(v_xi,v_xi).
 B=[D,[D,f]]/2+Delta f/6,
 sigma_0(B)=-(1/2)Hess^TF_h f(v_xi,v_xi).                 (V2)

Positive elliptic square-root calculus gives Omega,Y in Psi^1
with the SAME principal symbol N|xi|. Their difference X first
belongs to Psi^0. The Sylvester identity
Omega X+X Y=epsilon N^(1/2) B N^(1/2)
has right-hand side of order zero; comparison of the order-one
symbols forces sigma_0(X)=0. Thus X belongs to Psi^(-1), with

 sigma_(-1)(Omega-Y)
       =-epsilon Hess^TF_h f(v_xi,v_xi)/(4|xi|).           (V3)

This leading symbol is exact for each allowed epsilon; it is
not just an uncontrolled perturbative claim in epsilon.

The new static ground has
C_pp,N=(1/2)N^(-1/2)Omega N^(-1/2).
The old initial canonical vacuum has C_pp,old=D/2. Therefore

 C_pp,N-C_pp,old=(1/2)N^(-1/2)(Omega-Y)N^(-1/2),
 sigma_(-1)(C_pp,N-C_pp,old)
       =-epsilon Hess^TF_h f(v_xi,v_xi)/(8N|xi|).          (V4)

Here p=N^(-1)partial_t q is the unit-normal derivative, so this
is the relevant normal-derivative Cauchy covariance. If both
states were Hadamard on the SAME new spacetime, the difference
of their two-point functions would be smooth. Its Cauchy data,
including these normal derivatives, would then be smooth too.
The nonzero order-minus-one symbol in (V4) contradicts that.

For f=(4cos^2 chi-1)/sqrt(V), the orthonormal Hessian's trace-free
eigenvalues are

 (16,-8,-8)sin^2 chi/(3sqrt(V)).
 integral_S3 |Hess^TF f|^2 dV=80/3.                      (V5)

At chi=pi/2 in the radial cotangent direction, (V4) is
-2epsilon/(3sqrt(V)N|xi|), nonzero for every permitted epsilon!=0.
Hence the old ESU canonical vacuum on this new static branch
is normal but NOT Hadamard.

## V3. Consequence for the same-initial-state CTP problem

The finite-mode influence of T and full-field spectral-zero
normal kernel of U remain valid in their stated domains.
The old input's failure of the Hadamard condition blocks any
automatic upgrade to locally covariant renormalized stress on
these nonzero lapse branches. A c-number vacuum-energy or local
counterterm phase does not change a two-point function and
therefore cannot repair this state defect.

Conversely the new static ground is a legitimate Hadamard
comparison but changes the initial state. Substituting a
branch-dependent ground state into T would change the stated
preparation. It is not a same-density solution.

For this test the constant-lapse branch is smoothly extended
for all time to examine its specified Cauchy state. No abrupt
switch is called a smooth spacetime. A genuinely smooth common
past with N=1, followed by distinct smooth positive lapses, is
a different and viable preparation problem. The Hadamard
property then propagates with the true KG evolution; actually
constructing its complete two-branch phase and device feedback
remains a subsequent gate.

This is a concrete rejection of one preparation, alongside a
legal static-state control. It is not an exclusion of every
normal state, every preparation or every interacting theory.

## V4. Checked primary mathematics and certificate scope

Sahlmann--Verch, "Passivity and Microlocal Spectrum Condition",
https://arxiv.org/pdf/math-ph/0002021 , Theorem 5.1,
PDF pages 19--20 for the hypotheses and statement.
The scalar CCR implication to Hadamard form is stated in the
introduction and used here with the exact scalar bisolution.

Ammann--Lauter--Nistor--Vasy, "Complex Powers and Non-Compact
Manifolds", https://arxiv.org/pdf/math/0211305 ,
Example 2 (compact manifolds, PDF page 7) and Theorem 7.9
(PDF page 23). These justify the classical pseudodifferential
square roots and principal symbols used in V2.

The automated certificate independently checks the explicit
spherical eigenfunction, normalized measure, Hessian tensor,
its positive norm and the symbol algebra. The application of
the microlocal theorem and smooth-difference argument is the
written analytic proof above, not a machine-formal proof.

## V5. The old state is also outside the new positive energy form domain

The physical beta in U has order-minus-two principal symbol
-epsilon HessTF f(v_xi,v_xi)/(8N|xi|^2).
Therefore A=Omega^(1/2)beta has order -3/2 and principal symbol

 -epsilon HessTF f(v_xi,v_xi)/(8sqrt(N)|xi|^(3/2)).         (V6)

It is nonzero on an open spatial/cotangent cone. Localize there.
For a compactly supported coordinate symbol the HS norm squared
is (2pi)^(-3) integral |a(x,xi)|^2 dx dxi, by the Fourier
Plancherel identity for the integral kernel. The leading symbol
in (V6) contributes a positive multiple of integral_R^infinity
r^2 r^(-3)dr, which diverges. The next-order symbol is
O(r^(-5/2)); it cannot cancel the leading lower bound for
sufficiently large r on a smaller open cone.
Thus Omega^(1/2)beta is NOT Hilbert--Schmidt.

For the actual nonnegative Hamiltonian H_N^(0) in U,

 <0_D|H_N^(0)|0_D>=n_s ||Omega^(1/2)beta||_HS^2=infinity. (V7)

This is the extended positive quadratic-form expectation.
The old vacuum is not in D((H_N^(0))^(1/2)), while it remains
a normal vector with a well-defined strongly continuous unitary
orbit. Finite probabilities for bounded observations do not
supply an unbounded energy/stress moment.

There is also an actual canonical finite-section conclusion,
without postulating a logarithmic rate. U proved uniform strong
convergence of U_K^(0)(t), and hence strong-resolvent convergence
of their nonnegative generators. For each M, min(H_K^(0),M)
converges strongly to min(H_N^(0),M). Positivity and (V7) then give

 liminf_K <0_D|H_K^(0)|0_D>=infinity.                     (V8)

The free-tail extension has zero vacuum energy and agrees with
the actual cutoff expectation. The full shell identity in T
gives <0_D|H_epsilon,K|0_D>=E_gs,0,K exactly. Hence
E_gs,epsilon,K-E_gs,0,K tends to minus infinity for each fixed
allowed nonzero epsilon. Neither this result nor a principal
symbol residue is identified with the renormalized finite part
of the canonical-cutoff gravitational phase.

For a checked primary presentation of the localized HS argument,
see Sussman, "The microlocal irregularity of Gaussian noise",
https://ethanwsussman.github.io/WF.pdf , Proposition 4.1 and its
local-symbol proof (PDF pages 32--33). The explicit nonzero
symbol, dimension and energy-domain application are given above.
