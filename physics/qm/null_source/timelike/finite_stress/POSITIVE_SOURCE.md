# Finite positive constituent energies and total-source variance

Use the actual normal state in CRITICAL_STATE.md and the volume domains
proved in VOLUME_MOMENTS.md. The physical Hilbert space in this construction
is the strictly negative sector Pi=1_(-infinity,0)(H), with E=-H>=0.
There is a uniform negative gap for the constructed state. We do not
assume that a possible zero-energy kernel has all the domains below.

## 1. Dense closed forms and their second moments

On Pi H define positive vacuum, zero-mode and dust energies by their
compressed positive forms. Their total is the closed form
\[
 j[\psi]=q\|v^{1/2}\psi\|^2+
          \|K_0^{1/2}\psi\|^2+\|E^{1/2}\psi\|^2,\quad
 K_0=P^2/(2v),\ q=V_0U_0.
\tag{23}
\]
The domain is dense: the span of f(H)u, for compact smooth f supported
strictly below zero and u in C_c^infinity(P) tensor c00(n), is dense in
Pi H by the spectral theorem. The moment proof places these vectors
in D(v), D(P^2) and D(H). Each restricted positive form is closed,
and their sum is closed. It defines a positive self-adjoint J.

If a physical psi is in D(v) intersect D(P^2) intersect D(H), the
representation theorem gives
\[
 J\psi=\Pi(qv+K_0)\psi+E\psi,
\]
and hence
\[
 \|J\psi\|^2\le
 3[q^2\|v\psi\|^2+\|K_0\psi\|^2+\|H\psi\|^2].
\tag{24}
\]
Since v>=delta and P commutes with v,
\[
 \operatorname{Tr}\Omega_t J^2
 \le3[q^2\langle v^2\rangle_t+
             {\langle P^4\rangle_{\rm old}\over4\delta^2}
             +\langle H^2\rangle_0]<\infty.
\tag{25}
\]
All positive constituent means are finite as well. The original negative
gravitational kinetic form is bounded in absolute value by 4gamma<v>,
and the curvature form by (3V0/2)<v^(1/3)>.
No cancellation between divergent positive and negative terms defines H.

Equation (25) is a second-moment statement about this explicitly defined
positive form sum. It does not infer every high moment of a noncommuting
sum from separate high moments.

## 2. Original momentum moments are retained exactly

For each original Gaussian component the two centered momentum
coordinates have variance v_seed=x0/4, and the center radius squared is
K2*R with R equally likely 1 and 1+sqrt(3)/2. Angular details do not
affect these radial moments. With L=1+sqrt(3)/4,
\[
 \langle P^2\rangle=2v_{\rm seed}+K_2L,
\]
\[
 \langle P^4\rangle=8v_{\rm seed}^2+8v_{\rm seed}K_2L
              +K_2^2(11/8+\sqrt3/2).
\tag{26}
\]
These are full mixture moments; v_seed must not be substituted for
the full mixture variance. All moments are finite, and P is conserved.

## 3. A positive reduced dust density with controlled variance

The density is an additional ordering prescription. Put M=v^-1/2 and
B=Pi M Pi on the physical space. From the Jacobi coefficients,
\[
 [H,M]_{n,n+1}=\gamma\sqrt\delta(\sqrt n-\sqrt{n+1}).
\]
The row sum is maximized at n=2:
\[
 \|[H,M]\|\le\gamma\sqrt\delta(\sqrt3-1).
\tag{27}
\]
For n>=2 the sum telescopes to sqrt(n+1)-sqrt(n-1), a decreasing
function; the first row is smaller. This bound is independent of P.
It also proves M preserves D(H), first on the core and then by graph
closure. Pi commutes strongly with H, so B preserves D(E).

Define the closed positive form
\[
 R_D={1\over V_0}(E^{1/2}B)^*(E^{1/2}B).
\tag{28}
\]
Its domain contains the dense D(E). On D(E),
R_D psi=B E B psi/V0, and
\[
 \|R_D\psi\|\le
 {\,\delta^{-1}\|E\psi\|+
                    \gamma(\sqrt3-1)\|\psi\|\,\over V_0}.
\]
Therefore
\[
 \operatorname{Tr}\Omega_t R_D^2
 \le {2\langle H^2\rangle_0\over V_0^2\delta^2}
       +{2\gamma^2(\sqrt3-1)^2\over V_0^2}<\infty .
\tag{29}
\]
The homogeneous zero-mode density has
rho0=P^2/(2V0v^2), and rho0^2<=P^4/(4V0^2delta^4);
vacuum density is U0. Their compressed positive forms have corresponding
finite second moments on the constructed state.

Uncompressed M(-H)M need not be positive on Pi, because M need not
preserve the negative sector. B^2 is not Pi v^-1 Pi. The density in
(28) is not asserted to obey an exact volume integral identity with E,
nor a covariant local Ward identity. Those are further physical gates.

## 4. What has closed

One normal initial geometry-source state, one fixed dust-time evolution,
finite positive constituent energies, finite total positive-energy
variance, and a finite positive reduced dust-density variance have now
been established in the declared model. Finite stress does not establish
small stress fluctuations, a semiclassical approximation or local RSET
for the original field theory.
