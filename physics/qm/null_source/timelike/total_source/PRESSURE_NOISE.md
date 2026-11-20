# Complete local stress-noise difference

Use the states of COHERENCE.md, not an incoherent replacement of their quartic
moments. Define t_ab,m(x) as the coefficient of a_m^2 in one species' stress
tensor, and Tcal_ab(x)=sum_m t_ab,m(x). Then
\[
 \langle0|T^{(i)}_{ab}(x)|A_i\rangle
                  =\sqrt{2/d}\,{\cal T}_{ab}(x).
\]
All other modes, zero-mode cross terms, subtraction terms and mean products
cancel in the state difference: four selected shell operators are required
to connect A1 and A2. This proves for the full local connected symmetrized
noise, including all spacetime components,
\[
 \boxed{\Delta N_{abcd}(x,x')={16c\over d}
        \operatorname{Re}[{\cal T}_{ab}(x){\cal T}_{cd}(x')^*]}.
\]
This is a finite smooth difference. It does not require the individual
singular coincident noise kernels to be assigned an unregulated point value.

On the common static S3 background, in a local orthonormal frame,
\[
 \sum Y_m^2=d/V_0,\quad
 \sum\nabla_iY_m\nabla_jY_m=d\omega^2\gamma_{ij}/(3V_0),\quad V_0=2\pi^2.
\]
The kinetic and gradient a^2 terms cancel exactly in the density:
\[
 {\cal T}_{00}={\cal T}_{0i}=0,\qquad
 {\cal T}_{ij}=-{d\omega\over3V_0A^4}
                  e^{-2i\omega\eta}\delta_{ij}.
\]
Consequently the complete difference is a spatially uniform pure-pressure
kernel,
\[
 \Delta N_{pp}(\eta,\eta')=D_p\cos[\Omega(\eta-\eta')],
 \quad D_p=16cd\left({\omega\over3V_0A^4}\right)^2,\quad\Omega=2\sqrt3 .
\]
Its real smeared quadratic form is nonnegative and rank at most two:
D_p[(int f cos Omega eta)^2+(int f sin Omega eta)^2].
It is conserved on the static background. All density/momentum slots of
this SECOND-MOMENT difference vanish. This does not prove equality of every
higher local density record, nor the absolute Hamiltonian constraint for
each state.

The commutator of two free quadratic stresses is quadratic plus a scalar.
Equal W2 therefore gives equal retarded stress response; common local
renormalization/contact terms also cancel. The new noise and the common
linear response are compatible pieces of one state pair. Beyond the static
background the common free evolution still preserves W2 equality, but the
pure-pressure form itself must be recomputed.

The main numerical certificate sets c=w. All lengths, times and stresses
are in the inherited model units; no conversion to instrument sensitivity
is asserted.
