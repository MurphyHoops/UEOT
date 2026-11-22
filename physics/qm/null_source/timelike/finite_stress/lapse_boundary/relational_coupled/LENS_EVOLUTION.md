# Complete finite-mode evolution on every compact positive-g window

## L1. Why the inverted scalar term is not a propagation obstruction

COUPLED_FORMS first used g>0 and d3>0. At small K, g>0 but d3<0,
so its semibounded static form is unavailable. This page supplies a
time-dependent unitary transform for the **complete** finite-mode operator.
The result holds for every fixed ordering eta>=-1/4 with its specified
Friedrichs form. It does not cover g<0 or crossing g=0.

After the source dilation R(u), write in the Liouville coordinate
\[
 \widetilde H=\mathfrak a(u) A_\eta+\beta(u)x^2+
 c x^{-2/3}[H_s(u)+d_0(u)]+c_\kappa d_1(u)x^{2/3},
\]
where \(\mathfrak a=1/(2g)>0\), \(\beta=9d_3/4\),
\(c=(2/3)^{2/3}\), \(c_\kappa=(3/2)^{2/3}\).
All coefficients are smooth on a compact positive-g interval.

## L2. A globally positive auxiliary scale on this compact interval

Set ds/du=2 mathfrak a. Let r1,r2 solve
\[
 r_{ss}+(\beta/\mathfrak a)r=0,\quad
 (r_1,r_{1,s})(s_0)=(1,0),\quad(r_2,r_{2,s})(s_0)=(0,1).
\]
Their Wronskian is 1. Hence b=(r1^2+r2^2)^(1/2)>0 everywhere, and
b, b^-1 and the needed derivatives are bounded on the compact interval.
Direct differentiation gives
\[
 b''-\frac{\mathfrak a'}{\mathfrak a}b'
       +4\mathfrak a\beta b=\frac{4\mathfrak a^2}{b^3}.        \tag{L1}
\]
This is an analytic construction from a regular linear auxiliary ODE;
no old mode/geometry ODE and no numerical auxiliary ODE is run.
The Ermakov--Pinney identity is standard (REFERENCES); its actual use and
positivity here are justified by the nonzero Wronskian.

For the current g'=1/4 and d3=59/720-g/2, the same fundamental equation is
\[
 r''+\frac1{4g}r'+\left(\frac{59}{160g}-\frac94\right)r=0,
\]
or \(r_{gg}+r_g/g+(59/(10g)-36)r=0\).
No explicit special-function formula is needed.

## L3. The transformed Hamiltonian, with all terms retained

Define \(\theta=b'/(2\mathfrak a b)\) and
\[
 (L(u)\phi)(x)=b^{-1/2}e^{i\theta x^2/2}\phi(x/b),\qquad y=x/b.
\]
Then
\[
 L^\dagger\widetilde H L-iL^\dagger L'
 =\frac{\mathfrak a}{b^2}(A_\eta+y^2)
 +c b^{-2/3}y^{-2/3}H_s
 +c d_0b^{-2/3}y^{-2/3}
 +c_\kappa d_1b^{2/3}y^{2/3}.                              \tag{L2}
\]
The dilation coefficient is \(2\mathfrak a\theta-b'/b=0\).
The quadratic coefficient becomes mathfrak a/b^2 by L1.
The source term remains positive, with the same squeezed finite-mode H_s.
This is a time-dependent change of representation, not deletion of the
negative cubic potential in the original Hamiltonian.

The common form space is
\[
 D(q_\eta)\cap D(y)\cap D(y^{-1/3}H_0^{1/2}).
\]
Both scalar lower powers are infinitesimal form perturbations relative to
q_eta+||y phi||^2; ORDERING_DOMAIN proves the inverse-power bound even at
the critical endpoint. Dilation preserves the homogeneous q_eta domain.
For the quadratic phase, the ground-state expression gives
q_eta[e^(i theta y²/2)phi] <= 2 q_eta[phi]+2 theta²||y phi||²,
so it also preserves this form space, including eta=-1/4.
R is bounded and strongly continuous on it by source energy equivalence.
The form coefficients are C2, positive after a finite scalar shift.
The same common-form theorem therefore gives a complete unitary propagator.

Undo L, R and W. This defines the original complete weak evolution,
unique in the transported continuous energy class, with all source terms.
For each frozen u*, repeat with the auxiliary source dilation and this lens
on every finite auxiliary-time interval; the reverse transformation proves
weak uniqueness. The same autonomous group argument as SNAPSHOT_DOMAIN
then supplies a self-adjoint realization of the original frozen operator.
No essential self-adjointness or actual-u strong snapshot-domain transport
is inferred.

## L4. Current model and the remaining continuum question

K=2 has g approximately 2.58 and d3<0 on the same clock patch. It is now
included, as are all finite K with a compact g>0 patch.
There is no claim that K=2 approximates the full-field source.

At fixed background, g_K decreases without bound with K, so this
positive-g method cannot itself give an unbounded cutoff sequence.
Changing u with K to maintain g changes the background.
The bare coefficient by itself does **not** exclude a properly
renormalized combined continuum theory; CUTOFF_GATE examines this
distinction. Physical source/geometry mean recovery remains a separate
gate, analyzed in MEAN_RECOVERY.
