# P. A calibrated homogeneous geometry class and its state-change cost

## P1. The same action maps the complete energy class to geometry

Use the ENERGY example of LOCAL_AUTONOMOUS, including its incoming
normal preparation, complete total K and actual reduced propagation.
No independent geometry tensor factor is added. At the fixed final
slice u_f=.56, f_f=exp(-.02), let

 K_low,max=50126122.5, K_high,min=50379072.5,
 Delta K_gap=252950,
 K_theta=50252597.5.

K_theta is the midpoint of the GAP. It is not the different midpoint
K_*=50253597.25 used once in the propagation comparison.

For each single chosen pair (A,U_0) in the certified parameter box,
the selected lower root satisfies

 partial_K kappa_f(K)=f_f/[2 kappa_f(K)sqrt(Delta_f(K))]>0.   (P1)

Define the threshold ONCE as kappa_theta=kappa_f(K_theta).
Thus the spectral identities on the admitted total band are

 1_(kappa_f>kappa_theta)=1_(K>K_theta),
 1_(H_f>H_theta)=1_(K>K_theta),
 H_f=kappa_f/a_f, H_theta=kappa_theta/a_f.               (P2)

H_f is the proper-time homogeneous expansion rate (dt=aN deta);
its units are inverse MODEL proper time, not calibrated inverse seconds.

A common derivative bound gives, for the SAME fixed parameters,

 gap_kappa >= f_f Delta K_gap/
                         [2 kappa_max sqrt(Delta)_max],
 gap_H >= f_f Delta K_gap/
                         [2 a_max kappa_max sqrt(Delta)_max].       (P3)

The half-gap gives each class's margin from its threshold. The
certificate computes these positive bounds at u_f. Separately
enclosing absolute kappa values over uncertain A,U_0 may yield
overlapping intervals. We do NOT infer a universal absolute numerical
threshold across different parameter realizations from (P1).

## P2. Calibrated effect on the actual prepared range

Let V_pre=U(u_f,u_i)W_in. Spectral intertwining and the complete
actual evolution give

 1_(K>K_theta)V_pre=V_pre P_high.

Consequently the local instrument effect obeys

 ||V_pre* [F_high-1_(kappa_f>kappa_theta)] V_pre||
 =||E_high-P_high|| <= epsilon.                        (P4)

The same holds for H_f. It is uniform for all normal source-code
states, including arbitrary normal reference systems.
This is calibration on the specified PREPARED RANGE, not a
norm approximation of these effects on the entire physical Hilbert
space. It concerns pre-read geometry classes, not preservation of
postmeasurement K or geometry. It gives no continuous-kappa accuracy,
no local four-dimensional metric measurement and no Einstein
constraint-residual measurement (that residual is identically zero
in this selected homogeneous model).

## P3. The complete homogeneous stress classes follow as well

The full three-field apparatus stress is
rho_app=p_app=f_f K/(V a_f⁴). Its code is the same, and
gap_rho_app=gap_p_app=f_f Delta K_gap/(V a_f⁴).
It includes the controller, probe and interaction.

For the present conformal-vacuum input, put Y=1+kappa², z=fK,
q=3Va²/2, r=VU_0a⁴, d=sqrt(Delta)=q-2a_cY>0.
The critical relation and its actual pressure evolution give

 a_cY²-qY+r+z=0, Y_z=1/d, chi=Y-3z/d,
 rho_total=3Y/(2a²),
 p_total=-rho_total+3z/(a²d).                           (P5)

These are the complete homogeneous Ward projections in the declared
critical renormalization, including the fixed vacuum/geometric terms.
Their derivatives at fixed u are

 rho_total,K=3f/(2a²d)>0,
 p_total,K=f[3/(2a²d)+6a_c z/(a²d³)]>0.                (P6)

Therefore thresholds obtained from K_theta give the same binary
projectors. Both total-stress class gaps are at least
3 f_f Delta K_gap/(2 a_max² d_max). Pressure may be negative;
this is a pressure-level class, not a positive/negative-pressure test.
Changing the source input, EFT action, branch or post-read state
requires checking these identifications again.

## P4. Information has a nonzero bare-source-state cost

This instrument has an actual QND property for the source code:
preparation, propagation, admitted-band projections and both sqrt(F)
commute with the source momentum code projections. This property
is essential; generic measurements with a re-preparation step do
not obey the following conclusion for a specified input.

Take any normalized pure vectors |l>,|h> in the two source code
bands and the ideal balanced coherent seed |+>=(|l>+|h>)/sqrt(2).
Include preparation, evolution and the COMPLETE two-record reader
in one Stinespring isometry. Let p_j(l),p_j(h) be its record laws.
QND implies that its source off-diagonal output block has trace norm

 ||rho_out,lh||1 <= B_classical/2,
 B_classical=sum_j sqrt[p_j(l)p_j(h)].

This follows by tracing each record block and Cauchy-Schwarz; no
final product state or reader energy conservation is assumed.
Any known block-diagonal source unitary calibration preserves that
off-diagonal trace norm. The bounded coherence witness then yields

 D_tr(rho_source,out,|+><+|)
       >=(1-B_classical)/2
       >=1/2-sqrt[epsilon(1-epsilon)].                 (P7)

The last step uses p_high(l)<=epsilon and
p_high(h)>=1-epsilon, epsilon<1/2.
The actual incoming bare-source marginal differs from the coherent
seed by at most e_in, so the triangle inequality gives

 D_tr(rho_source,out,rho_source,in)
    >=1/2-sqrt[epsilon(1-epsilon)]-e_in >0.             (P8)

The same statement holds after any explicitly chosen code-preserving
output calibration. All comparisons are in the reduced physical
Hilbert-space embedding and its source marginal, not an unweighted
raw-kernel trace norm.

The certificate evaluates (P7)-(P8) from the already verified local
record error, without fitting a more favorable input or discarding
a failed record. This directly demonstrates that useful records
here do not preserve the full bare source state.

## P5. Closure and its remaining boundary

This completes the action-based identification and uniform calibration
of a specified homogeneous geometry/stress CLASS, together with a
strict state-change cost, in the selected reduced model.
It advances beyond an uncalibrated auxiliary pointer. Autonomous
preparation, terminal reader stress, full interacting QFT and
inhomogeneous Einstein-CTP dynamics remain open.
