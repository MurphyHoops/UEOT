# Same-source finite-slice budgets, including the incoming preparation

This page fixes the source from BOUNDARY_STATE, its actual quiet history with
c=exp(-20000), and the finite-slice canonical transport. No old scientific
entry is executed. The bounds below are in model units and are deliberately
conservative. They are not apparatus energies.

## S1. Actual inputs and the two zero modes

The frozen fields give
8e4<A<1e5, 8e5<Ez<1e6, 2e-7<sigma<2.2e-7, and 0<p<1.
The finite-slice primitive obeys |A² I_i|<=3 epsilon, epsilon<exp(-1158),
hence |I_i|<1e-14. The W7 support-vector estimates of READOUT_WITNESS are
rechecked from the explicit bump derivatives, rather than inferred from
an uncomputed source matrix:
\[
 \|\mathsf Q\psi_N\|<10^8,\quad
 \|\mathsf D\psi_N\|<10^{15},\quad
 \|\mathsf P\psi_N\|<10^{22}.
\]
Here mathsf Q=sum Q_j², mathsf D=sum{Q_j,P_j}/2, mathsf P=sum P_j²,
in the incoming zero-mode variables. The smooth normalized bump has
||varpi'||_infty<10, ||varpi''||_infty<200; its compact radial support has
energy <1e6. The source branches may be correlated with the k=2 shell.

At the actual slice, q_j=A(Q_j+I_i P_j), p_j=h_i q_j+P_j/A. Therefore
\[
 Q_z=\frac{A^2}2(\mathsf Q+2I_i\mathsf D+I_i^2\mathsf P),\quad
 {\cal D}_z=2h_iQ_z+\mathsf D+I_i\mathsf P ,
\]
and ||Q_z||_2<1e18, ||D_z||_2<2e15. Norms are GNS/vector norms, not
their squares. These formulas retain the original incoming correlations.

## S2. The complete nonzero-mode Q second moment

For the two fields and k² real modes per field, put
\[
 Q_k=|v_k|^2(N_k+k^2)+\tfrac12(v_k^2 A_k+\bar v_k^2A_k^\dagger),
 \quad A_k=\sum_{r=1}^{2k^2}a_r^2,\quad
 [A_k,A_k^\dagger]=4N_k+4k^2.
\]
For k>=3 the actual incoming vacuum, transported by the same Jost modes,
gives mean k²|v|² and variance k²|v|⁴. Distinct high k vacuum factors are
independent. ACTUAL_INVERSE gives |F_k|<=2, so |v_k|²<=2/omega_k and
omega_k>=sqrt(3) k/2. Hence, for every K<=100000,
\[
 M=\sum_{k=3}^K k^2|v_k|^2<3\sum_{k=1}^K k<1.6\,10^{10},\quad
 V=\sum_{k=3}^K k^2|v_k|^4\le16K/3<5.4\,10^5.
\]
The high contribution has norm sqrt(M²+V), not sqrt(V) alone.

For k=2 the full non-Gaussian shell must be retained. In its two excited
NOON branches, A_2 has squared norm 16 or 0, and N_2=2. The exact Q_2²
coefficients are respectively 50|v_2|⁴ and 42|v_2|⁴; vacuum gives
20|v_2|⁴. The current mixtures therefore give
[20+(26+/-4)p]|v_2|⁴ and ||Q_2||_2<10.
Consequently ||Q_osc||_2<2e10, and by the same-source GNS triangle,
\[
 Q_0:=\|Q_K\|_{2,\rho}<10^{19}<e^{50}.                       \tag{S1}
\]
We do not assume zero/shell independence when adding these norms.

The analogous first dilation moment uses |v v'^*|<3 (the same Jost
bounds with the past L1 potential <0.1). Thus
|<D_osc>|<=6 sum_{k=2}^K(k²+2 delta_{k2})<3e15,
and |<D_K>|<5e15<e40.

## S3. Canonical target inherited from the actual mean history

The full original bulk momentum target, including the matter endpoint, is
\[
 P_{u,\mathrm{ref}}
 =-3V_0A^2h_i+P_{u,\mathrm{ct}}+2h_i\langle Q_K\rangle
                              -\langle{\cal D}_K\rangle.    \tag{S2}
\]
P_u,ct is L5 of ACTION_LIFT, with
DP_kappa,ct=-H_K V'/4+(30h h'+C h'')/120.
On the frozen quiet history all needed derivatives through order four are
bounded by epsilon. For K<1e5, H_K<13, |B_K|<1e10, C<400, V<2epsilon,
|V'|<3epsilon. Direct triangle estimates give
|P_u,ct|<3e10 epsilon, and
\[
 |P_{u,\mathrm{ref}}|<e^{60}.                                \tag{S3}
\]
This is the old classical canonical budget, not a proof that a finite-K
quantum state follows the old mean solution. The old mean-SCE remains
a different, explicitly full-field expectation statement.

At the initial point,
h=-s c+sigma_F b+Theta v and
h'=-s²c+sigma_F²b+Theta²v.
The frozen E4 remainder bound gives |Theta^j v|<e202 c²<c for j<=4.
With .9c<b<1.1c, s<3 and 936000<sigma_F<937000,
\[
 0<h<e^{-19980},\qquad h'/h>5\,10^5.                         \tag{S4}
\]
The script checks the coefficient inequalities in the log domain; it does
not turn underflow into zero or run a geometry ODE.

## S4. The same incoming-energy controlled gate, all pointer laws

Let B=A delta H_in,K, t=Q_g/h and U_B=exp(-it B).
For this particular input, oscillator density blocks commute with their
total oscillator energy, including the NOON coherences. Thus the
nonselective source output is equivalent to the zero-mode energy flow
on this input. This is not an operator identity for arbitrary inputs and
not an identity of the joint gate.

In incoming variables Q_j -> Q_j+t P_j/A², giving exactly
\[
 Q_K(t)=Q_K+tJ+t^2 L,\quad
 J=\mathsf D+I_i\mathsf P,\quad L=\mathsf P/(2A^2),
\]
for the source marginal expectation calculation just described.
The finite constants obey ||J||_2<2e15 and ||L||_2<1e12.
For any independent normal pointer law with
x=(E t^4)^(1/4)<infinity, Minkowski on the direct-integral GNS space gives
\[
 q_{2,\mathrm{out}}:=\sqrt{\operatorname{Tr}\sigma Q_K^2}
 \le Q_0+\|J\|_2 x+\|L\|_2x^2
 <10^{19}+2\,10^{15}x+10^{12}x^2.                           \tag{S5}
\]
There is one common t for the modes; no modewise independent noise is used.
For the real Gaussian of INCOMING_PREPARATION, E t²=1/(4delta²),
E t⁴=3/(16delta⁴), so the sharper bound is
Q0+||J||/(2delta)+sqrt(3)||L||/(4delta²).
At delta=1e-6 this is <e60. The exact even Gaussian fourth-moment formula is
\[
 \operatorname{Tr}\sigma Q_K^2
 =\operatorname{Tr}\rho[Q_K^2+v(J^2+\{Q_K,L\})+3v^2L^2],
 \quad v=1/(4\delta^2).
\]
The full bare state changes; the unchanged stress-algebra restriction from
the predecessor is not an unchanged canonical coordinate distribution.
