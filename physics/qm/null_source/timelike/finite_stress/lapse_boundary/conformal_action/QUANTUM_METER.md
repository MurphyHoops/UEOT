# G. A finite-time proper-rest qubit meter in the SAME critical constraint

## G1. Positive apparatus, one initial state and one parameter choice

Use the common-u lower branch of CRITICAL_BRANCH. Let E=H_c,
c(E)=[1-cos(pi(E-E_c))]/2, so 0<=c<=1, c(E_c)=0 and c(E_c+1)=1.
This is a declared SPECTRAL functional calculus prescription.
It is not asserted to be the Weyl quantization of the naive classical
cosine energy, nor a four-dimensional local polynomial coupling.

Set u_*=0.55, a_*=Aexp(u_*), and choose ONCE

    H_rest=[30+25c(E)sigma_z]/a_*,
    A_meter=30+25c(E)sigma_z,
    f(u)=a/a_*=exp(u-u_*),
    T(u)=E+f(u)A_meter.                                 (G1)

H_rest is strictly positive, including its interaction. E and A_meter
commute and are individually conserved; T'(u)=f A_meter, so total
conformal energy is NOT called constant. The proper-rest coupling is
N a H_rest, not the radiationlike N H_app of an f=1 comparison.

The initial matter state is any normal state on the vacuum/one k=1
particle source span, tensor the memory |+x>. The first source
excitation is spatially homogeneous. The four total-energy branches
lie inside E_c+[0,100] for all u in J, including both memory levels.

The actual selected critical evolution is exactly

    U(u_f,u_i)=exp[-i integral h(u,T(u))du].              (G2)

Every apparatus energy and interaction is included before solving
kappa(u,T). No fixed-kappa pulse, large-energy subtraction, external
u-programmed gate or mean-only geometry replacement is used.

## G2. The finite-time complete instrument

For source energy E_j write
Phi_j,+/-=integral_J h(u,E_j+f(u)[30+/-25c(E_j)])du,
Delta_j=Phi_j,+-Phi_j,-.
The final memory sigma_y readout gives the diagonal source Kraus maps

    K_+/-y(E_j)=[exp(-iPhi_j,+) -/+ i exp(-iPhi_j,-)]/2,
    p_+y(E_j)=[1+sin(Delta_j)]/2.                       (G3)

Both outcomes are retained; sum K* K=I. The corresponding full
source-memory Lüders instrument is normal and preserves the admitted
four-dimensional sector. Shared reference systems are allowed.
The quantum coupling/evolution is the actual one in (G2); the final
reader is an abstract calibrated observable, not a derived autonomous
local apparatus.

Delta_0=0. For the one-particle source,

 Delta_1=integral_J du integral_(E_c+1+5f)^(E_c+1+55f)
                             dT/kappa(u,T).             (G4)

This positive double-integral formula avoids subtracting enormous
geometry phases. If the common chart bounds are kappa_min,max,

    50[2sinh(0.01)]/kappa_max <= Delta_1
        <=50[2sinh(0.01)]/kappa_min.                    (G5)

The outward certificate verifies 0<Delta_1<pi/2 and a strictly
positive readout gap from the vacuum value 1/2.
These are model probabilities and time units, not a laboratory
calibration or SI performance claim.

## G3. State change is retained, not hidden

Let Phi_bar_j=(Phi_j,++Phi_j,-)/2. The nonselective source coherence is

 rho_jl -> exp[-i(Phi_bar_j-Phi_bar_l)]
              cos[(Delta_j-Delta_l)/2] rho_jl.          (G6)

The source energy distribution is unchanged, while the full bare
state generally changes. After the stated diagonal phase calibration,
the coherent pure input (|vac>+exp(i theta)|1>)/sqrt(2) changes in
trace distance by [1-cos(Delta_1/2)]/2. A diagonal balanced mixture
need not change at all. This phase-compensated distance is a lower
bound on the uncompensated distance for that coherent pure example;
the mathematical phase comparison does not implement an extra device. The optimal conditional-memory distinguishability
is sin(Delta_1/2); the actual sigma_y record gap is sin(Delta_1)/2.
This does not evade the earlier fixed-bare-marginal extension exclusion.

Before readout, for any source state with balanced populations,

 <T>=E_c+1/2+30f,  Var(T)=1/4+(625/2)f².

All branches are retained. For this PARTICULAR |+x> input family,
nonselective sigma_y readout preserves the E/sigma_z spectral law,
hence the complete homogeneous energy law. It does not commute with
A_meter for general inputs. No autonomous energy-conserving terminal
reader has been derived from this family-specific fact.

## G4. Same lapse action, contacts and conditional influence

An exact quantum-sector variational representative is
integral[i Psi* Psi'-N Psi*(E+fA_meter)Psi]deta, with the explicitly
chosen spectral Hamiltonian. Spin coherent overlaps retain their Berry
endpoint phases; patch changes transport the state and gluing.
One may also use time-sliced operator CTP directly. A naive classical
c(E_classical) is not substituted for this quantum prescription.

On each branch,
Gamma_N=-(E+fA_meter), Gamma_u=-N f' A_meter.
The primitive phase-space contacts are
S_NN=0, S_Nu=-f'A_meter delta, S_uu=-N f''A_meter delta.
For f=exp(u-u_*), f'=f''=f.

For prescribed classical lapse/scale paths define
tau_0=integral N deta, tau_f=integral Nf deta on each branch.
The exact influence is

 F=Tr rho exp[-iE Delta tau_0-iA_meter Delta tau_f]
  =exp[-i30 Delta tau_f] sum_j rho_jj exp[-iE_j Delta tau_0]
                            cos[25c(E_j)Delta tau_f].   (G7)

It is a positive Gram kernel with unit physical diagonal. Its
same-branch log Hessian is minus the full covariance and minus i times
the primitive contact mean; cross-branch covariance has the corresponding
positive sign and no primitive mixed-branch contact. Differentiate
(G7) once: do not add its action contacts a second time.

The matter-plus-meter stress projections are

 rho(u)=[E+f_u A_meter]/(V_3a_u⁴), p(u)=E/(3V_3a_u⁴).

They obey rho_u+3(rho+p)=0 as an operator identity. If
V_E=Var E,V_A=Var A_meter,C=Cov(E,A_meter), the full projected noises are

 N_rhorho=[V_E+(f_u+f_v)C+f_uf_v V_A]/(V_3²a_u⁴a_v⁴),
 N_rhop=[V_E+f_u C]/(3V_3²a_u⁴a_v⁴),
 N_prho=[V_E+f_v C]/(3V_3²a_u⁴a_v⁴),
 N_pp=V_E/(9V_3²a_u⁴a_v⁴).

E and A_meter commute, so this block is positive. On the stated input
C=0 and V_A=625<c(E)²>, but their spectral laws are not independent.
The critical anomaly/geometry is separately retained in the SAME
operator constraint and pressure row. This projected block is not
the full spatial tensor noise.

## G5. Completed and open gates

This completes a normal, finite-time, source-sensitive homogeneous
meter construction with positive proper-rest apparatus energy and
exact reduced geometry feedback. It changes the matter action,
renormalization and physical representation from the predecessor.
Global c(H_c), the finite spectral sector, the selected reduced
ordering, and the abstract terminal reader are explicit restrictions.
Local four-dimensional coupling, complete field CCR/spatial constraints,
an autonomous full reader/preparer, and physical unification remain open.
