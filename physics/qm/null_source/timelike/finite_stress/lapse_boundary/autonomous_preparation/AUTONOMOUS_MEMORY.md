# AD. An exact autonomous clock writes the source-sign record into memory

## AD1. This is a new global apparatus Hamiltonian

Keep AC's FIXED H_M with M=10^12 and its two outside product inputs.
Add one oscillator b (the local oscillator, LO), with H_LO=N_b and initial
coherent amplitude beta0=i B exp(iT), B=10^4, T=1/2; at T its amplitude is iB.
Add a degenerate two-state register R with zero Hamiltonian and initial |0>.
This LO is a finite quantum system, not an infinite classical reference.

Let a be the physical k=1 probe annihilator, P=(a-a^dagger)/(i sqrt(2)),
D=a^dagger b+b^dagger a, Ntot=N_a+N_b.
Choose the balanced beam splitter U_BS so that
U_BS^dagger(N_a-N_b)U_BS=D.
For instance its one-particle rotation sends
a ->(a+b)/sqrt(2), b ->(b-a)/sqrt(2).
Set kappa=exp(-1/200), and define
w_d=[1+kappa sin(d/(sqrt(2) B))]/2,
Theta(d)=arcsin sqrt(w_d),
U_mem=exp[-i Theta(N_a-N_b) tensor sigma_y],
U=U_mem U_BS.                                         (AD1)
There is NO intermediate photon-count projection. The count dependence
is a coherent controlled rotation. U commutes strongly with Ntot.

By the bounded spectral functional calculus choose a self-adjoint G with
||G||<=pi and exp(-iG)=U (for example G=-Arg(U)).
G strongly commutes with Ntot. Its boundedness does not make it local
in spacetime: this is a global selected-mode apparatus.

## AD2. Exact finite-time clock transport and the complete active interaction

The new clock coordinate is y. Use m_R=1, Omega=2pi and
h_R=p_y^2/2+Omega^2(y+1/2)^2/2.
The clock initially has chi(y)=u(y+2), supported on [-2,-1], where u is AB's
normalized H2 polynomial envelope. Its energy includes the oscillator
zero-point energy; no new zero subtraction is imposed.

Let F(y)=0 for y<=-1, F(y)=1 for y>=0. In the transition set z=y+1 and
F=35z^4-84z^5+70z^6-20z^7.
This C3 function has vanishing first three endpoint derivatives.
Define the multiplication unitary W_R(y)=exp[-iF(y)G] and
H_ext=W_R[H_M+N_b+h_R]W_R^dagger.                       (AD2)
This definition gives its exact self-adjoint domain and closed form.
It is semibounded, and is at least Omega/2 plus Z's lower bound.

The physical initial state is the SAME outside H_M input, tensor the
independent LO, register and clock states, since W_R=I on clock support.
We hold the final physical register projection P_j=|j><j| FIXED.
Equation (AD2) is a new ACTIVE interaction Hamiltonian, not a passive
change of both dynamics and observables.

The clock kinetic energy becomes (p_y+F'G)^2/2.
The whole square is retained. H_M+N_b must also be conjugated.
Because W_R commutes with Ntot, the only changed H_M field term is the
selected low-mode interaction r(x)q_s W_R q_p W_R^dagger.
All high-mode terms, controller kinetic energy, and the same x-dependent
counterterms remain. In particular, at F=1 the Hamiltonian does NOT
automatically become the old H_M: the surviving low interaction is
conjugated by U. Leaving this term out defines a different apparatus.

For the actual field cutoff set
H_ext,K=W_R[H_M,K+N_b+h_R]W_R^dagger.                    (AD3)
The SAME W_R is used for every K. Tensor extension and conjugation of
Z's actual strong propagator limit give the actual full-field limit
of these Hamiltonians and all bounded complete instruments.
No common bare high-mode domain is assumed.

A harmonic oscillator half-period is a spatial reflection:
exp(-iT h_R)chi(y)=exp(-i pi/2)chi(-1-y), T=pi/Omega=1/2.
The final clock has exact support [0,1], where F=1. Therefore the actual
endpoint state, before a register projection, is exactly the reflected
clock tensor
U [ exp(-iT H_M)psi_code tensor |iB>_LO tensor |0>_R ]. (AD4)
There is no arrival postselection or discarded clock tail.

## AD3. Finite LO error and a positive actual complete memory record

On a coherent LO write b=iB+c, with c in vacuum. Then
D/(sqrt(2)B)=P+(a^dagger c+c^dagger a)/(sqrt(2)B).
Duhamel, applied on finite-energy probe vectors and then by purification,
gives for any fixed s
|<exp[isD/(sqrt(2)B)]>-<exp(isP)>|
 <= |s|sqrt(<N_a>)/(sqrt(2)B)+s^2/(4B).                (AD5)
The proof uses ||a exp(itP)psi||<=sqrt(<N_a>)+|t|/sqrt(2);
no large-LO limit is substituted for the finite state.

On AB's REFERENCE Gaussian probe, odd source-to-probe Dyson orders give
||S_probe,source||<=sinh(I), I<=1/25.
Its covariance contribution is bounded by exp(2I).
Hence
<N_a>_ref <=[exp(2/25)-1+sinh(1/25)^2]/2<.043.
For s=1, (AD5) is bounded by
delta_LO=[sqrt(.043)/sqrt(2)+1/4]/B<4*10^-5.

The exact register probabilities from (AD1) are a complete two-outcome
normal instrument. Relative to the Gaussian P reader's BINARY EFFECT,
the ideal reference probability error is <=kappa delta_LO/2 per code.
This approximates the effect only. The actual post-state is the explicit
beam-splitter/LO/register channel, not the Gaussian Lueders instrument.

AC's actual low-probe state error contracts through this fixed channel.
Thus the actual endpoint register contrast satisfies
d_memory >= d_cl-2 epsilon-kappa delta_LO>0.00229.       (AD6)
The certificate gives a tighter outward interval.
All records are retained; there is no normalization on successful arrivals
or a preferred binary outcome. The exact CP instrument exists for arbitrary
normal source/reference inputs, while the numerical error bound remains
limited to the two specified codes.

## AD4. What this closure supplies and what remains open

We have an autonomous, semibounded, actual full-field-cutoff Hamiltonian,
a product preparation, a finite-energy LO and clock, exact finite-time
record writing and a complete bounded register instrument.
AE includes the entire resource and terminal-projection accounting.

The final bare register PVM is still a mathematical readout operation.
The Hamiltonian is a global constructed apparatus, not a local covariant
four-dimensional action. The reader is not guaranteed to store a permanent
record. In the unitary continuation without the T=1/2 projection, at
T=1 the harmonic clock returns to its initial support and the register
uncomputes to |0>. A physical stable classical record is not constructed.

The extended two code preparations have identical entire H_ext spectral
laws: conjugate the old joint low-mode parity by W_R; it commutes with
H_ext and acts as the old parity on the initial F=0 support.
Thus this source-sign record is still NOT total-energy or geometric-charge
discrimination. No quantum Einstein constraint is solved here.
