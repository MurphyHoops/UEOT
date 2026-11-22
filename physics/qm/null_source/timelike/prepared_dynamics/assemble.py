"""Assemble an all-mode, all-initial-root normal-derivative obstruction."""
from fractions import Fraction as Q
from pathlib import Path
from math import ceil,floor
import argparse,hashlib,json,sys
from mpmath import iv,mp
import phase_bounds as pb
bg,old,initial=pb.bg,pb.old,pb.initial
I,box=bg.I,bg.box
HERE=Path(__file__).resolve().parent
PROP=HERE.parent/"evolution"/"propagation"
sys.path.insert(0,str(PROP))
import finite_modes as fm
iv.dps=70;mp.dps=80
N=512;LAM=32768
RADIUS=Q(15933,67108864)

def read(path):
    return json.loads(path.read_text())
def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def top(x):return initial.top(x)
def absI(x):return initial.absolute(x)
def sym(x):return box(-bg.upper(x),bg.upper(x))
def interval(x):return old.read_pair(x)

def inputs():
    data={}
    for n in ['phase_bounds_uniform.json','phase_quadrature_zero.json','phase_extension_zero.json','phase_sensitivity.json']:
        data[n]=read(HERE/n);assert data[n]['status']=='PASS'
        assert data[n]['N']==N
    assert data['phase_bounds_uniform.json']['J']==8
    assert data['phase_extension_zero.json']['J']==8
    assert data['phase_sensitivity.json']['J']==8
    for n in ['phase_bounds_uniform.json','phase_sensitivity.json']:
        assert Q(data[n]['radius'])==RADIUS
    for n in ['phase_quadrature_zero.json','phase_extension_zero.json']:
        assert Q(data[n]['radius'])==0
    modes=[]
    for path in [PROP/'result.json',PROP/'extra_eta0_256.json',HERE/'modes_257_512.json']:
        receipt=read(path);modes+=receipt['targets']['0']['modes']
        if path.parent==PROP:
            for rel,digest in receipt['source_sha256'].items():assert sha(PROP/rel)==digest
        else:
            for rel,digest in receipt['new_source_sha256'].items():assert sha(HERE.parent/rel)==digest
    assert [r['k'] for r in modes]==list(range(2,N+1))
    previous=read(HERE.parent/'prepared_initial'/'result.json')
    assert previous['initial_existence']['root_exists']
    assert Q(previous['initial_existence']['root_absolute_bound'])==RADIUS
    assert previous['physical_prescription']['lambda']==LAM
    return modes,data,previous

def finite_values(modes):
    rho=-I(Q(3,8));pressure=I(Q(13,24))
    derivative=I(0);derivative_error=I(0)
    a=iv.sqrt(3)
    for row in modes:
        k=row['k'];omega=iv.sqrt(k*k-1)
        rho+=k*k*(interval(row['e'])-k+I(Q(1,2*k))-I(Q(3,8*k**3)))
        pressure+=k*k*(interval(row['s'])-I(Q(k,3))-I(Q(1,2*k))+I(Q(7,8*k**3)))
        u=iv.mpc(I(Q(row['u_center'][0])),I(Q(row['u_center'][1])))
        p=iv.mpc(I(Q(row['p_center'][0])),I(Q(row['p_center'][1])))
        E=I(Q(row['norm_error_radius']));norm=fm.norm(u,p,a,omega)
        cross=u.real*p.real+u.imag*p.imag
        radius=norm*E+E*E/2
        weight=I(k*k*(k*k-1))*2/(27*iv.pi**2)
        derivative-=weight*cross
        derivative_error+=weight*radius
    return rho/(36*iv.pi**2),pressure/(36*iv.pi**2),derivative+sym(derivative_error),top(derivative_error)

def nonlinear_remainders(bound,previous):
    d=box(0,Q(1,(N+1)**2));theta=box(-RADIUS,RADIUS)
    qv=initial.family_q_box(Q(0),Q(0),theta,4)
    dj=bg.Jet.const(d,0);q=[bg.Jet.const(v,0) for v in qv]
    A,B,T,T1,Rn=old.normalized_defect(q,dj)
    b=B.c[0];tt=T.c[0];root=iv.sqrt(b)
    E=absI((b+1-d)/(2*root));S=absI((b-(1-d)/3)/(2*root))
    P=absI((b+(1-d)/3)/root);R=absI((qv[0]+1+d*tt)/root)
    D=top(interval(bound['D5']));rapidity=D/(N+1)**5
    cosh=old.cosh(rapidity);cosh2=old.cosh(2*rapidity)
    cubic_d=top(2/(27*iv.pi**2)*I(Q(2,3))*D**3*cosh2/(10*N**10))
    diag_p=S*D**2*cosh**2/(3*N**6)
    cubic_p=I(Q(2,3))*P*D**3*cosh2/(11*N**11)
    diag_r=E*D**2*cosh**2/(3*N**6)
    cubic_r=I(Q(2,3))*R*D**3*cosh2/(13*N**13)
    local=previous['new_uniform_uv']
    # Previous delta and parameter boxes contain the present ones. Taylor tail
    # sum scales as N^-2, with exactly the same initial a and subtraction.
    local_r=top(interval(local['rho_local_subtraction_tail']))/4
    local_p=top(interval(local['pressure_local_subtraction_tail']))/4
    error_r=top((diag_r+cubic_r)/(36*iv.pi**2)+local_r+interval(bound['taylor_remainder_density']))
    error_p=top((diag_p+cubic_p)/(36*iv.pi**2)+local_p+interval(bound['taylor_remainder_pressure']))
    error_d=top(cubic_d+interval(bound['taylor_remainder_derivative']))
    return [error_r,error_p,error_d],{
      'density_diagonal':old.pair(diag_r/(36*iv.pi**2)),'pressure_diagonal':old.pair(diag_p/(36*iv.pi**2)),
      'density_cubic':old.pair(cubic_r/(36*iv.pi**2)),'pressure_cubic':old.pair(cubic_p/(36*iv.pi**2)),
      'pressure_derivative_cubic':old.pair(cubic_d),'density_local':old.pair(local_r),'pressure_local':old.pair(local_p),
      'total_uniform_density_remainder':old.pair(error_r),'total_uniform_pressure_remainder':old.pair(error_p),
      'total_uniform_pressure_derivative_remainder':old.pair(error_d)}

def mean_lipschitz(previous,sensitivity):
    H=top(interval(previous['finite_modes']['original_log_energy_bound']))
    g=top(iv.exp(2*H)*(iv.exp(I(RADIUS)/32)-1)/I(RADIUS))
    sum_cubes=I(Q((N*(N+1)//2)**2-1))
    harmonic=I(sum((Q(1,k) for k in range(1,N+1)),Q(0)))
    sum_k=I(N*(N+1)//2)
    theta=box(-RADIUS,RADIUS)
    Lrho_num=g*sum_cubes+absI((theta-2)/4)*harmonic
    Lp_num=g*sum_cubes+sum_k/3+absI(theta/12-I(Q(1,3)))*harmonic
    C=19+15*(iv.log(I(3)*LAM**2/4)+2*iv.euler)
    Lrho_an=absI(C*(2*theta-4)/(8640*iv.pi**2))
    Lp_an=absI((C*(2*theta-8)+180*theta-244)/(25920*iv.pi**2))
    b=sensitivity['born_polynomial_lipschitz']
    Lrho=top(Lrho_num/(36*iv.pi**2)+Lrho_an+interval(b['density']))
    Lp=top(Lp_num/(36*iv.pi**2)+Lp_an+interval(b['pressure']))
    return Lrho,Lp

def derivative_parameter_change(root_bound,previous,bound,sensitivity):
    H=top(interval(previous['finite_modes']['original_log_energy_bound']))
    g=top(iv.exp(2*H)*(iv.exp(I(RADIUS)/32)-1)/I(RADIUS))
    K=256
    moment=I(Q(K*(K+1)*(2*K+1)*(K-1)*(K+2),10))
    low_L=top(g*moment/(27*iv.pi**2))
    Dold=top(interval(previous['new_uniform_uv']['D5']))
    Dr=top(interval(bound['Dr_above_256']));Lphi=top(interval(bound['Lphi_above_256']))
    harmonic1=I(sum((Q(1,k)-Q(1,k**3) for k in range(K+1,N+1)),Q(0)))
    harmonic2=I(sum((Q(1,k**2)-Q(1,k**4) for k in range(K+1,N+1)),Q(0)))
    block_L=top(2/(27*iv.pi**2)*iv.exp(3*Dold/(K+1)**5)*(Dr*harmonic1+2*Dold*Lphi*harmonic2))
    born_L=top(interval(sensitivity['born_polynomial_lipschitz']['pressure_derivative']))
    return top(root_bound*(low_L+block_L+born_L)),{
      'low_modes_2_256_L':old.pair(low_L),'new_modes_257_512_L':old.pair(block_L),
      'infinite_Born_polynomial_L':old.pair(born_L),'D5_above_256_from_prior_uniform_certificate':old.pair(Dold)}

def compute():
    modes,data,previous=inputs()
    rho0,p0,dp0,finite_dp_error=finite_values(modes)
    qa=data['phase_quadrature_zero.json']['born_polynomial_integrals']
    qb=data['phase_extension_zero.json']['born_polynomial_integrals']
    born={key:interval(qa[key])+interval(qb[key]) for key in qa}
    analytic=initial.analytic_initial(I(0))
    proxies=[rho0+analytic[0]+born['density'],p0+analytic[1]+born['pressure'],dp0+born['pressure_derivative']]
    remainders,remainder_receipt=nonlinear_remainders(data['phase_bounds_uniform.json'],previous)
    Lrho,Lp=mean_lipschitz(previous,data['phase_sensitivity.json'])
    D0=top(absI(proxies[0]-proxies[1])+remainders[0]+remainders[1])
    L=top(Lrho+Lp)
    denominator=I(LAM**2)-3*L
    assert bg.lower(denominator)>0
    root_bound=top(3*D0/denominator)
    assert bg.upper(root_bound)<bg.lower(I(RADIUS))
    change,change_receipt=derivative_parameter_change(root_bound,previous,data['phase_bounds_uniform.json'],data['phase_sensitivity.json'])
    derivative=proxies[2]+sym(remainders[2]+change)
    sign_excluded=bg.upper(derivative)<0
    paths=[HERE/n for n in ['assemble.py','phase_bounds.py','phase_quadrature.py','phase_extension.py','phase_sensitivity.py','generate_modes.py']]+[HERE/n for n in data]+[HERE/'modes_257_512.json',
          PROP/'result.json',PROP/'extra_eta0_256.json',HERE.parent/'prepared_initial'/'result.json']
    result={'schema':'ueot-prepared-normal-obstruction/1','status':'PASS' if sign_excluded else 'UNRESOLVED',
      'lambda':LAM,'root_radius_before':str(RADIUS),'N':N,'J':8,
      'source_sha256':{str(p.relative_to(HERE.parent)):sha(p) for p in sorted(paths)},
      'same_static_seed_and_actual_geometry_family':True,'mean_source_fixed_in_physical_time':True,
      'finite_pressure_derivative':old.pair(dp0),'finite_pressure_derivative_error':old.pair(finite_dp_error),
      'born_tail_polynomial':{k:old.pair(v) for k,v in born.items()},
      'zero_parameter_proxies':{k:old.pair(v) for k,v in zip(['Qrho','Qp','Qpprime'],proxies)},
      'uniform_remainders':remainder_receipt,
      'root_tightening':{'D0':old.pair(D0),'Lrho':old.pair(Lrho),'Lp':old.pair(Lp),'positive_denominator':old.pair(denominator),
         'all_prior_roots_absolute_bound':old.pair(root_bound),'existence_reused_not_reproved':True},
      'root_parameter_derivative_change':{'absolute_bound':old.pair(change),**change_receipt},
      'Qpprime_all_roots':old.pair(derivative),
      'lambda5_normal_spatial_Einstein_residual':old.pair(-2*derivative/iv.sqrt(3)),
      'required_a_third_over_a':old.pair(-3*derivative/LAM**2),
      'existing_a_third_over_a':'0',
      'constraint_cubic_coefficient_C_over_a0_squared':old.pair(2*(-2+sym(root_bound))*derivative/LAM**2),
      'no_smooth_SCE_extension_preserving_this_prepared_past':sign_excluded,
      'positive_window_statement':'If all mean equations held on any [0,epsilon) in a smooth same-state fixed-source extension, their initial normal derivatives would vanish; the certified spatial derivative does not.',
      'scope':{'initial_slice_existence_preserved':True,'this_prepared_history_excluded':sign_excluded,
        'SCE_as_a_theory_excluded':False,'new_compatible_past_constructed':False,'full_unified_physics':False}}
    return result

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--write',action='store_true');ap.add_argument('--check',action='store_true')
    args=ap.parse_args();result=compute()
    for key in ['finite_pressure_derivative','Qpprime_all_roots','lambda5_normal_spatial_Einstein_residual']:
        print(key,[float(x) for x in map(Q,result[key])],flush=True)
    print('all-root radius',float(Q(result['root_tightening']['all_prior_roots_absolute_bound'][1])),flush=True)
    print('parameter derivative change',float(Q(result['root_parameter_derivative_change']['absolute_bound'][1])),flush=True)
    rendered=json.dumps(result,indent=2,sort_keys=True)+'\n';path=HERE/'result.json'
    if args.write:path.write_text(rendered)
    if args.check:
        assert result['status']=='PASS', 'Normal-derivative sign unresolved'
        assert path.read_text()==rendered
    print(result['status']+': all-mode normal derivative and smooth-extension obstruction',flush=True)
if __name__=='__main__':main()
