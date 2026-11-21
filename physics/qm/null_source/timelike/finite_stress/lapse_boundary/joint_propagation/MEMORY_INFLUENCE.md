# Exact conditional memory influence and its initial mixed blocks

## I1. Same action, same prepared state, two independent histories

Use the genuine conformal-lapse harmonic memory from MEMORY_ACTION,
H_M=Pi^2/(2M)+M Omega^2 Lambda^2/2, M,Omega>0, and the real Gaussian
chi_sigma with v=sigma^2. For prescribed positive histories kappa_+,
kappa_- in the monotone u chart, keep

    tau_+=integral du/kappa_+(u), tau_-=integral du/kappa_-(u),
    t=tau_+-tau_-,
    a=1/(2kappa_i,+), b=1/(2kappa_i,-).

Before reducing the lapse, tau_+-tau_-=integral(N_+-N_-)d eta.
The branch endpoints/lapses remain independent until variation.

The ACTIVE initial gate has plus ket e^{ia Lambda}chi_sigma and
minus bra chi_sigma*e^{-ib Lambda}. The exact conditional influence is

    F(t,a,b)=<chi_sigma|e^{-ib Lambda}e^{-iH_M t}
                              e^{ia Lambda}|chi_sigma>.              (I.1)

The final memory trace is included. On a pure canonical rewrite the
transported endpoint density/readouts must instead be co-transformed;
I.1 is not a new interaction supplied by a passive boundary phase.
Off-diagonal final endpoints would also require their final transport.

This is an exact memory calculation for prescribed geometry histories.
It does not define or solve a quantum-geometric path measure, a global
constraint kernel, or the full tensor Einstein--CTP equations.

## I2. Closed Gaussian formula and its branch

Set m=M Omega, theta=Omega t and

    A=m v+1/(4m v)>=1, beta=1/(2m v),
    d(t)=cos(theta)+i A sin(theta).

Then

    F(t,a,b)=d(t)^(-1/2)
       exp{-v[(cos(theta)+i beta sin(theta))(a^2+b^2)-2ab]/[2d(t)]}.
                                                                    (I.2)

The inverse square root is CONTINUOUSLY continued from t=0, F(0,0,0)=1.
It is not reset to the principal square root at each time.
Since |d|^2=cos^2(theta)+A^2 sin^2(theta)>=1, no real-time zero occurs.

A stable global branch formula is d^(-1/2)=exp(-i theta/2)/sqrt(q_theta),
where q_theta=cos^2(theta)+A sin^2(theta)
+i(A-1)sin(theta)cos(theta). Its real part is at least one, so only
this last square root uses the ordinary principal branch.

For a direct derivation, insert the harmonic Mehler kernel and integrate
over initial/final Lambda. The two-variable Gaussian matrix has

    Q_diag=1/(2v)-i m cot(theta), Q_off=i m csc(theta),
    det Q=-i m d/(v sin(theta)),
    Q_diag/det Q=v[cos(theta)+i beta sin(theta)]/d,
    Q_off/det Q=-v/d.

The Gaussian integral gives I.2 away from sin(theta)=0; strong
continuity gives the remaining times with the stated branch.
In particular,

    F(0,a,b)=exp[-v(a-b)^2/2],
    F(pi/Omega,a,b)=-i exp[-v(a+b)^2/2],
    F(2pi/Omega,a,b)=-exp[-v(a-b)^2/2].                (I.3)

The last minus sign is the oscillator zero-point phase. Dropping it
would change a two-time influence even though some equal-time
probabilities could remain unchanged.

## I3. Positivity, normalization and causal composition

For a history h define the normalized memory vector

    eta[h]=exp[-iH_M tau[h]]exp[i a[h_i]Lambda]chi_sigma.

Then F[h_+,h_-]=<eta[h_-],eta[h_+]> is a positive Gram kernel,
Hermitian under branch exchange, has |F|<=1 and F[h,h]=1.
This proves positivity without treating the calculated noise and
response blocks as independently chosen random variables.

For the unshifted Gaussian, let
r=(1/2)log(2M Omega v). Its normal energy law is

    Prob(E=Omega(2j+1/2))
       =(2j)!/[2^(2j)(j!)^2] tanh(r)^(2j)/cosh(r), j>=0.

Its characteristic function is equivalently
e^{-i theta/2}/[cosh(r)sqrt(1-tanh(r)^2 e^{-2i theta})].
This supplies an independent branch/normality check.

Successive time segments add tau before the final memory trace.
In general F(t_1+t_2,a,b) is not F(t_1,a,b)F(t_2,a,b): multiplying
two traced factors would reset the memory. The energy noise is
correlated across the whole history and is not white noise.

The exact CP preparation/evolution map starts from the PRE-GATE source
input rho_S, applies the fixed normal isometry
U(rho_S tensor |chi><chi|)U*, then the actual joint evolution and trace.
Once source and memory are correlated, the future influence need not
define a CP dynamical map on an arbitrary reduced input E_sigma(rho_S)
alone. Keep the pre-gate state and both endpoint factors.

## I4. Mean, noise and the full initial ordered block

Let L=log F be the continuous local logarithm near the physical
history t=0,a=b=q. Define

    h_0=1/(8Mv)+M Omega^2 v/2,
    V_0=1/(32M^2v^2)+M^2 Omega^4 v^2/2-Omega^2/4,
    E_q=h_0+q^2/(2M), V_q=V_0+q^2/(4M^2v).

Differentiating I.2 gives exactly

    L_t=-i E_q, L_tt=-V_q,
    L_a=L_b=0,
    L_aa=L_bb=-v, L_ab=v,
    L_ta=L_tb=-i q/(2M).                              (I.4)

The last terms are imaginary ordered response/contact data, not
nonzero real symmetric noise assigned by hand.

In the actual initial memory state e^{iq Lambda}chi_sigma, the
ordered centered covariance of (H_M,Lambda) is

    N_ordered=[[V_q,-i q/(2M)],[i q/(2M),v]].

Its determinant is v V_0>=0. Indeed
V_0=[M Omega^2 v-1/(4Mv)]^2/2.
The symmetric energy-Lambda covariance is zero, while their ordered
mixed expectation is -i q/(2M). Removing this imaginary block would
destroy the response information.

Averaging q=X/2 over the actual source law reproduces MEMORY_ACTION's
bare and weighted means. The variance also includes the dispersion of
the conditional mean E_q; averaging conditional variances alone
would miss (I_4-I_2^2)/(64M^2).

## I5. Explicit endpoint and history contact terms

At the common initial kappa, da/dkappa_i,+ = db/dkappa_i,-
=-1/(2kappa_i^2). Since the first endpoint derivatives of L vanish,
its cross endpoint Hessian is

    L_{kappa_i,+ kappa_i,-}=v/(4kappa_i^4).            (I.5)

It agrees with the actual Gaussian boundary momentum covariance.
The mixed time/endpoint rows follow by the same chain rule from I.4.

For interior kappa variations with endpoints held fixed,

    delta t/delta kappa_+(u)=-kappa(u)^-2,
    delta t/delta kappa_-(u)=+kappa(u)^-2.

Thus on the common history,

    L_+(u)=+i E_q/kappa(u)^2,
    L_-(u)=-i E_q/kappa(u)^2,
    L_{+-}(u,v)=+V_q/[kappa(u)^2 kappa(v)^2],
    L_{++}(u,v)=-V_q/[kappa(u)^2 kappa(v)^2]
                      -2i E_q kappa(u)^-3 delta(u-v),
    L_{--}(u,v)=-V_q/[kappa(u)^2 kappa(v)^2]
                      +2i E_q kappa(u)^-3 delta(u-v). (I.6)

In I.6 the two subscripts label second functional derivatives. The delta contacts arise from
varying kappa^-1 and must accompany the energy covariance.
For the retained lapse itself, the interior derivative of t is +1
on the plus branch and -1 on the minus branch; its second derivative
is zero. The original action contacts in MEMORY_ACTION and the
endpoint lapse terms remain distinct contributions.

With F=exp(i S_IF), S_IF=-i log F. Its physical plus lapse derivative
is -E_q, with the opposite minus-branch sign. These are conditional
memory rows, not the full original Einstein tensor source.

## I6. Free-pointer boundary check and verification scope

For Omega->0 at fixed M,v,t,

    d_0=1+i t/(4Mv),
    F_free=exp[-v(a-b)^2/2] d_0^(-1/2)
              exp[-i t(a+b)^2/(8M d_0)].              (I.7)

This is also the direct Gaussian momentum integral, providing a check
independent of the oscillator Mehler representation. It does not
extend the discrete direct-sum dynamical theorem to every free-memory
domain, or erase the source-form and normality costs.

The paired check verifies exact cumulants, endpoint rows, matrix
positivity/determinant identities, the Gaussian integral coefficients,
and finite Gram matrices with the correct continued branch.
These checks accompany the analytic derivation; they are not a
machine-formal proof or a solved coupled gravitational path integral.
The real controller implementing the ACTIVE initial gate, full tensor
response and experimental calibration remain OPEN.
