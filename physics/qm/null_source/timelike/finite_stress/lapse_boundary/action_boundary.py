"""Check lapse-preserved action, canonical endpoint and physical constraint normalization."""
import sympy as s
from common import finish
t, eps = s.symbols("t eps", real=True)
q, h, N = [s.Function(x)(t) for x in ("q", "h", "N")]
w2 = s.symbols("omega_squared", real=True)
kappa = h/N
X = s.diff(q,t)-h*q
Lraw = X**2/(2*N)-N*w2*q**2/2
Lbulk = s.diff(q,t)**2/(2*N)-N*(w2-s.diff(kappa,t)/N-kappa**2)*q**2/2
B = kappa*q**2/2
assert s.simplify(Lraw-Lbulk+s.diff(B,t)) == 0
nn, hh, qq, vel, pp, kap, kd = s.symbols("N h q velocity p kappa kappaprime", nonzero=True, real=True)
lr = (vel-hh*qq)**2/(2*nn)-nn*w2*qq**2/2
assert s.simplify(s.diff(lr,nn)+(vel-hh*qq)**2/(2*nn**2)+w2*qq**2/2) == 0
assert s.simplify(s.diff(lr,nn,2)-(vel-hh*qq)**2/nn**3) == 0
assert s.simplify(s.diff(lr,nn,hh)-(vel-hh*qq)*qq/nn**2) == 0
# Weyl-symbol Hamiltonian shear, with i W' W^dagger included.
Hbulk = nn*(pp**2+w2*qq**2)/2-(kd+nn*kap**2)*qq**2/2
Htransformed = s.expand(Hbulk.subs(pp,pp+kap*qq)+kd*qq**2/2)
Hraw = nn*(pp**2+w2*qq**2)/2+nn*kap*qq*pp
assert s.simplify(Htransformed-Hraw) == 0
# Off-shell finite interval: deliberate omission has an observable nonzero error.
Bt = B.subs({q:1+t,h:1+t*t,N:1+eps*(2+t)})
endpoint = Bt.subs(t,1)-Bt.subs(t,0)
coefs = [s.simplify(s.diff(endpoint,eps,i).subs(eps,0)/s.factorial(i)) for i in range(3)]
assert coefs == [s.Rational(7,2),-11,34]
# g00 chain-rule contact.
a = s.symbols("a", positive=True)
j = s.symbols("j", negative=True)
Nj = s.sqrt(-j)/a
assert s.simplify(s.diff(Nj,j)+1/(2*a*a*Nj)) == 0
assert s.simplify(s.diff(Nj,j,2)+1/(4*a**4*Nj**3)) == 0
# Derive action rows directly in physical phi variables, not a guessed Einstein row.
aa, av, acc, nv, V0, phiv, wphi, U0 = s.symbols(
    "a aprime asecond Nprime V0 phiprime omega_phi_squared U0", nonzero=True, real=True)
L = 3*V0*(-av**2/nn+nn*aa**2)/2 + aa**2*phiv**2/(2*nn)-nn*aa**2*wphi/2-V0*nn*aa**4*U0
rho = phiv**2/(2*nn**2*aa**2*V0)+wphi/(2*aa**2*V0)+U0
press = phiv**2/(2*nn**2*aa**2*V0)-wphi/(6*aa**2*V0)-U0
E = 1+av**2/(aa**2*nn**2)-s.Rational(2,3)*aa**2*rho
S = (acc/aa-av**2/aa**2)/nn**2-av*nv/(aa*nn**3)+(1+av**2/(aa**2*nn**2))/2+aa**2*press
GammaN = s.diff(L,nn)
assert s.simplify(GammaN-3*V0*aa**2*E/2) == 0
dLdav=s.diff(L,av)
dt_dLdav=s.diff(dLdav,aa)*av+s.diff(dLdav,av)*acc+s.diff(dLdav,nn)*nv
Gammau=aa*(s.diff(L,aa)-dt_dLdav)
assert s.simplify(Gammau-3*V0*nn*aa**2*(S+E/2)) == 0
assert s.simplify(Gammau-nn*GammaN-3*V0*nn*aa**2*S) == 0
# General noncommuting CTP matrix factors: cancellation by explicit unitary inverses,
# including final gluing. Pauli rotations give a nontrivial exact finite example.
I=s.eye(2); sx=s.Matrix([[0,1],[1,0]]); sz=s.diag(1,-1)
Wp=(I-s.I*sx)/s.sqrt(2); Wm=(I-s.I*sz)/s.sqrt(2)
Wfp=(I+s.I*sx)/s.sqrt(2); Wfm=(I+s.I*sz)/s.sqrt(2)
Up=sz; Um=sx; rho0=s.Matrix([[s.Rational(2,3),s.Rational(1,6)],[s.Rational(1,6),s.Rational(1,3)]])
Urp=Wfp*Up*Wp.H; Urm=Wfm*Um*Wm.H
rr=Wp*rho0*Wm.H
raw=s.trace(Urp*rr*Urm.H)
bulk=s.trace((Wfm.H*Wfp)*Up*rho0*Um.H)
assert s.simplify(raw-bulk)==0
wrong=s.trace(Up*rho0*Um.H)
assert s.simplify(raw-wrong)!=0
finish("action_boundary.py", {
    "lapse_preserved_off_shell_action_identity":True,
    "canonical_Hamiltonian_identity_with_time_derivative":True,
    "configuration_lapse_and_mixed_contacts_checked":True,
    "physical_EH_plus_free_lapse_and_pressure_rows_derived":True,
    "bulk_rows_do_not_replace_initial_distribution_terms":True,
    "CTP_initial_and_final_transport_exact_matrix_comparator":True,
    "omitted_endpoint_raw_minus_bulk_first_derivative":11,
    "omitted_endpoint_raw_minus_bulk_second_derivative":-68,
    "g00_chain_rule_contact_checked":True,
    "pure_canonical_dressing_supplies_new_physical_charge":False,
    "all_mode_cutoff_spatial_diffeomorphism_algebra_claimed":False,
    "full_renormalized_tensor_Hessian_constructed":False,
}, ["finite_stress/FINITE_SLICE_UV.md","finite_stress/DYNAMIC_CHARGE.md",
    "nonlinear_history/KERNELS.md"])
