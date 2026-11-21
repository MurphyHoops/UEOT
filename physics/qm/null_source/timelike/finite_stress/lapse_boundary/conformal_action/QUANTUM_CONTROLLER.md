# Z. A stable autonomous quantum-controller comparison on the full field Fock space

## Z1. Precisely what changes from the prescribed probe pulse

X/Y treat r(t) as an externally prescribed smooth function.
Here replace it by r(x), where x is ONE quantum-mechanical
controller coordinate, r in C_c^infinity(R), and |r|<=r_*<1.
The fixed background is still the unit ESU and its time.
The Hilbert space is L2(R_x) tensor Fock(L2(S3) plus L2(S3)).

This is a spatially homogeneous global controller model.
It is not a full four-dimensional local controller field,
nor a proved consistent truncation of such a field: local
controller modes could be excited by inhomogeneous phi psi.
The pointwise field interaction r(x)phi(y)psi(y) uses the
same global x over S3. A causal local realization of that
global control and a dynamical metric remain open.

For each actual finite field cutoff, use the SAME counterterm
and finite c_r convention as Y:

 H_K=p_x^2/(2M)+H_pair,K(r(x))-E_free,K
                      +r(x)^2 Hharm_K/8-c_r V0 r(x)^2.   (Z1)

Hharm_K=sum_(k<=K)1/k, V0=2pi^2. E_free,K=sum_(k<=K)k^3
is the two-field free vacuum energy. On a full-space extension,
higher modes are free spectators. On vacuum tails this is
exactly the actual finite-cutoff model.
M>0 and c_r are selected once; the example is M=1,c_r=0.
This is a free-vacuum-zero energy convention on the fixed ESU.
The absolute Casimir/geometric source must be restored with
its declared convention before coupling gravity.

No source/probe energy, interaction energy or controller
kinetic energy is removed in (Z1). It is not obtained by
imposing r(t) after evolving the controller.

## Z2. Exact fiber diagonalization and the bounded finite vacuum potential

The two field combinations have frequencies

 omega_k,plus/minus(x)=sqrt(k^2 plus/minus r(x)),
 theta_k,plus/minus(x)=(1/4)log(1 plus/minus r(x)/k^2).    (Z2)

Let W(x) be the real squeezing implementer with positive
vacuum overlap. Its coefficient sequences, with k^2
multiplicity for each sign, satisfy

 |theta_k,plus/minus| <= r_*/[4(1-r_*)k^2],
 |partial_x theta_k,plus/minus|
             <= ||r'||infinity/[4(1-r_*)k^2].            (Z3)

Thus both sequences are uniformly square summable, and their
actual canonical truncations converge in l2, also after an
x derivative. W_K(x) and W(x) have genuine C1 action on the
finite-particle core; no common old-vacuum energy domain is
inferred from their norm convergence.

Define the positive fiber Hamiltonian

 h_+(x)=W(x)dGamma(omega(x))W(x)^dagger.

The finite ground-energy remainder is the uniformly
convergent real function

 e(x)=sum_(k>=1) k^2[
       (sqrt(k^2+r)+sqrt(k^2-r)-2k)/2+r^2/(8k^3)]
                                      -c_r V0 r^2.     (Z4)

To see the uniform convergence, put
h(z)=[sqrt(1+z)+sqrt(1-z)-2]/2+z^2/8.
It has its first four Taylor coefficients below order four
zero, h(z)<=0, and Taylor's theorem gives

 |h(z)| <= 5|z|^4/[128(1-r_*)^(7/2)], |z|<=r_*.
 |sum_(k>K) k^3 h(r/k^2)|
       <= 5r_*^4/[512(1-r_*)^(7/2)K^4].                (Z5)

The sign follows either the even binomial expansion or
h''(z)<=0 for z>=0, with h'(0)=h(0)=0.
The same uniformly convergent differentiated series shows e
is smooth. In particular, e is bounded above and below.
The finite vacuum potential has not been set to zero separately
at each x; doing so would change the autonomous controller force.

## Z3. Closed form and actual self-adjoint autonomous evolution

On L2(R_x;Fock) define

 q[Psi]=(1/(2M))integral ||partial_x Psi||^2 dx
       +integral ||h_+(x)^(1/2)Psi(x)||^2 dx
       +integral e(x)||Psi(x)||^2 dx.                    (Z6)

The domain is the intersection of the controller H1 space
and the positive direct-integral field form domain.
Each positive term is closed; after adding a common constant
to make e nonnegative, their sum is closed.
The domain is dense because it contains
Psi(x)=W(x)Phi(x), with Phi compactly supported smooth in x
and taking values in finite-mode, finite-particle vectors.
The closed semibounded form determines a self-adjoint H.
It gives the actual autonomous unitary exp(-itH).

In the adapted frame Phi=W^dagger Psi the kinetic term is
||partial_x Phi+A(x)Phi||^2/(2M),
A=W^dagger W'=(1/2)sum theta'_j(a_j^2-a_j^dagger^2).
Here b=W a W^dagger=cosh(theta)a+sinh(theta)a^dagger,
which fixes the squeeze-sign convention.
This entire connection is retained; its vacuum/particle
kinetic contributions have not been dropped as an
adiabatic approximation. A is controlled on finite-particle
vectors by the l2 theta' bound and Nop+1.

The construction proves a lower bound, not the existence
of a normalizable ground vector. It is distinct from the
unstable noncritical u-clock generator in E.

## Z4. Moving cores and the actual finite-cutoff limit

A subtle domain point matters: W(x)|0> generally has infinite
FREE high-tail energy, so it need not belong to any finite-K
free-tail field form domain. A fixed common-domain shortcut
is invalid. Use moving cores instead.

First the adapted vectors in Z3 are a form core of (Z6).
In the adapted frame, smooth number cutoffs j(Nop/R) commute
with dGamma(omega). The commutator
[A,j(Nop/R)] is uniformly bounded and strongly tends to zero:
pair creation changes number by two, its norm grows at most
as Nop+1, and the cutoff difference is O(1/R) supported
where Nop is of order R. For complete domain justification, use the physical-frame bounded
multiplier B_R(x)=W(x)j(Nop/R)W(x)^dagger. It is strongly C1,
with B_R prime=W[A,j(Nop/R)]W^dagger uniformly bounded and
strongly tending to zero. The H1 multiplier product rule therefore
applies directly to every physical-frame Psi in H1. No separate
assumption that A Phi is in L2 is made. Since B_R commutes with
the fiber field form, this proves convergence in the sum form norm.
At bounded particle number, finite mode projections have
commutator with A bounded by a constant times the l2 tail
of theta', uniformly in x. That tail tends to zero by (Z3).
The field forms commute with those mode projections.
Finally ordinary compact-x cutoff and mollification complete
the core approximation. This proves density in the SUM
form norm, not just density in Hilbert space.

For a core vector Psi=W Phi choose Psi_K=W_K Phi.
The controller derivative converges by the C1 squeeze bound.
For K above Phi's finite mode support,
dGamma(omega_K)^(1/2)Phi=dGamma(omega)^(1/2)Phi exactly.
Hence both positive form terms and the uniformly convergent
e_K term converge. Diagonal approximation gives the form
recovery sequence for any Psi in the full form domain.

For the lower bound, suppose Psi_K converges weakly and
the commonly shifted q_K is bounded. Its derivatives and
B_K Psi_K, B_K=h_+,K^(1/2), are bounded. Test the latter
against moving graph-core vectors W_K Phi:
B_K W_K Phi -> B W Phi strongly, as just shown.
The adapted compact-x, finite-mode/particle test vectors also
form an operator graph core for the direct-integral B itself:
fiber spectral truncation followed by x approximation proves this.
Self-adjointness of the direct-integral B identifies every
weak limit as B Psi; closedness also identifies the weak
controller derivative. The shifted multiplication potentials
converge in operator norm and are nonnegative.
Weak lower semicontinuity of these three squared norms gives
the form lower bound.

Thus the actual q_K converge in the weak-lower-bound/strong-
recovery (Mosco) sense. Their self-adjoint H_K converge to H
in strong resolvent sense, and exp(-itH_K) and adjoints
converge strongly, uniformly on compact time intervals.
Fixed normal inputs/references and complete bounded
instruments consequently have actual trace-norm cutoff limits.
The free-tail extension agrees with the finite-cutoff
Hamiltonian on its physical vacuum-tail subspace.

## Z5. One normal finite-energy preparation, and what is not inherited

For the concrete r(x)=.2 exp[4-1/(x(1-x))] on 0<x<1
and zero otherwise, take the normalized controller packet

 b(x)=sqrt(2)sin[pi(x+2)]exp(i10x), -2<x<-1,
 b(x)=0 otherwise,

and the full source/probe ESU vacuum.
This b is in H1 with zero boundary traces; it is a legitimate
form-domain preparation, not asserted to lie in D(H).
Since r vanishes on its support, the field and counterterm
contributions vanish initially. At M=1,

 q[b tensor vacuum]=50+pi^2/2.                           (Z7)

For this finite-energy input the total H spectral energy
distribution and mean are conserved under the autonomous
unitary. Controller, field and interaction contributions
exchange within the same total Hamiltonian. Its positive
controller kinetic and dressed field-form energies remain
bounded by the total energy plus the finite lower bound
for e. The usual free-field energy at arbitrary intermediate
controller positions is not asserted finite.

A second, stronger preparation has a finite second total-energy
spectral moment. Put y=x+2 and take

 b_2(x)=sqrt(630)y^2(1-y)^2 exp(i10x), 0<y<1,
 b_2(x)=0 otherwise.

The envelope and its first derivative vanish at both endpoints,
so b_2 is H2 and b_2 tensor vacuum is in the actual D(H).
All interaction/counterterm terms vanish on its support.
Exact integration gives int u^2=1, int (u')^2=12 and
int (u'')^2=504. At M=1,

 <H>=56, <H^2>=||H Psi||^2=4426, Var(H)=1290.             (Z8)

Here <H^2> means the second spectral moment/quadratic expression
on D(H); membership in D(H^2) is not asserted. The mean and this
finite variance are conserved by the same full autonomous unitary.
This does not prove finite local stress variance or all moments.

The joint evolving state need not remain Gaussian.
X's prescribed-pulse transfer coefficient, Gaussian
convolution and timing calibration are NOT inherited.
A complete final probe measurement is still a normal CP
instrument using exp(-itH) and retaining or tracing the
controller explicitly, but its actual discrimination and
pulse-tracking errors must be computed anew.
The terminal reader has not become autonomous.

## Z6. Actual total-energy backaction of a complete terminal reader

Choose Q=q_probe,k=1 and the complete normal instrument

 M_z=(2pi sigma^2)^(-1/4)exp[-(z-Q)^2/(4sigma^2)].

It acts on the SAME autonomous system for any normal input;
controller/source can subsequently be retained or traced.
The measured Q and record z have a joint spectral/Gaussian law,
so the record mean-square noise relative to Q is exactly sigma^2.
It is not a source-coordinate or geometric reconstruction error.

For U_l=exp(-i l Q), U_l^dagger p_probe,1 U_l=p_probe,1-l.
The coordinate interaction r(x)q_source q_probe, controller kinetic
term and every counterterm are unchanged. At k=1,

 H_low=(p_s^2+p_p^2+q_s^2+q_p^2+2r q_s q_p)/2,
 E_ground,low=(sqrt(1+r)+sqrt(1-r))/2 <= 1.

Since |r|<1, p_p^2/2 <= h_+(x)+1 and
q_p^2 <= 2(h_+(x)+1)/(1-r_*).
Thus the finite-mode Weyl unitary preserves the whole closed form
domain, and its actual form identity is

 q_H[U_l Psi]=q_H[Psi]-l<Psi,p_p Psi>
                                      +l^2||Psi||^2/2.  (Z9)

The nonselective instrument equals the Gaussian Weyl average with
mean l=0 and v_l=1/(4sigma^2). By the positive shifted form,
spectral decomposition and integration of (Z9), every finite-total-
form-energy normal input has

 Delta<H>=v_l/2=1/(8sigma^2).                            (Z10)

No Gaussian joint state, free high-tail energy or product marginals
are assumed.

The bound on p_p makes it infinitesimally H-bounded.
Consequently the form identity represents the self-adjoint operator
H-l p_p+l^2/2 on D(H), and U_l preserves D(H).
For finite second H spectral moment, expand the squared norm
||(H-l p_p+l^2/2)Psi||^2 and average the Gaussian.
No Hp or pH domain assumption is needed: odd cross terms vanish.
Spectral decomposition or the Hilbert--Schmidt norm of H sqrt(rho)
extends this to normal mixed states with finite second moment:

 <H^2>_out=<H^2>_in+v_l(<p_p^2>_in+<H>_in)+3v_l^2/4,
 Var_out(H)=Var_in(H)+v_l<p_p^2>_in+v_l^2/2.              (Z11)

For preparation (Z8) at ANY finite autonomous readout time,
<H>_in=56 and Var_in(H)=1290. With sigma=.1, the reader output has

 <H>_out=68.5,
 1602.5 <= Var_out(H) < 4452.507076.

The upper bound uses <p_p^2> <= 2[56-inf(e)+1].
All are model-unit total-energy quantities. Source-to-probe
discrimination remains unknown for this preparation.
The reader's own physical energy supply has not been constructed;
(Z10)-(Z11) are its exact backaction on the retained Z total system,
not closure of the still-external terminal reader.

Completed: a full-field normal, semibounded autonomous
quantum-controller/source/probe Hamiltonian, its actual
canonical-cutoff limit and a normal finite-energy input.
Open: accurate finite-time record/calibration, a local
four-dimensional control field and terminal readout,
Hadamard/local-stress properties for the operator-valued
control problem, and all quantum-geometric constraints.
No full four-dimensional physical-unification claim is made.

Primary mathematical convergence reference checked:
Chen--Song, Continuity of eigenvalues of subordinate processes in
domains, Math. Z. 252 (2006), Proposition 2.1 and the Mosco
definition immediately preceding it,
https://rsong.web.illinois.edu/pages/evcont.pdf .
Only the general closed-form/resolvent equivalence is used;
their stochastic-process application is not imported into this model.
The moving-core and weak-limit hypotheses are proved above.
