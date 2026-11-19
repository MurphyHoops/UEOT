"""True quantum-mixture readout bounds and mean-gravity/branch negative controls."""
from fractions import Fraction as F
from pathlib import Path
import argparse,hashlib,json
import sympy as sp
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[4]
PREFIX=Path('physics/qm/null_source/timelike')

def frozen_json(relative,blob_sha):
    raw=(ROOT/PREFIX/relative).read_bytes()
    assert hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()==blob_sha
    return json.loads(raw)

def compute():
    review=frozen_json('stress_kernel/review.json','97aecfc23a19ef8564312855fe9d9fe3d57eb2cc')
    prepared=frozen_json('prepared_initial/result.json','3e683f672b448adb244247b1fe4c8bb51c78eb9e')
    assert review['status']==prepared['status']=='PASS'
    s=review['same_scale'];p=prepared['physical_prescription']
    assert s['lambda']==p['lambda']==32768
    assert p['mu']==1 and p['alpha_AE']==0 and p['extra_finite_terms']==0
    Q,L=sp.symbols('Q L',commutative=False)
    Y,S,V0,V1=sp.symbols('Y S V0 V1',real=True)
    def letters(op):
        if op==1:return ()
        if op==Q or op==L:return (str(op),)
        if op.is_Pow:
            assert op.exp.is_Integer and op.exp>=0
            return letters(op.base)*int(op.exp)
        assert op.is_Mul
        return sum((letters(x) for x in op.args),())
    def even_reference(expr):
        result=0
        for term in sp.Add.make_args(sp.expand(expr)):
            coefficient,op=term.as_independent(Q,L,as_Add=False)
            word=letters(op)
            if word.count('L')%2 or word==('Q',):continue
            name=''.join(word)
            value=1 if not word else {'QQ':V0,'LL':V1}.get(name,sp.Symbol('E_'+name))
            result+=coefficient*value
        return sp.expand(result)
    X=Q+Y*L+(Y**2-1)*S
    differences={}
    for n in (2,3):
        expr=even_reference(X**n)
        expected=sp.Rational(3,4)*S*S if n==2 else sp.Rational(9,4)*S*V1
        for sign in (-1,1):
            old=sum(expr.subs(Y,(sign+b*sp.sqrt(3))/2) for b in (-1,1))/2
            new=sp.Rational(2+sign,4)*expr.subs(Y,1)+sp.Rational(2-sign,4)*expr.subs(Y,-1)
            assert sp.simplify(old-new-expected)==0
            if n==2:assert sp.simplify(new-V0-V1)==0
        differences[str(n)]=str(expected)
    # A preparation-label-correlated compensator cancels the rank-one covariance,
    # while preserving a true higher-moment distinction of the original mixture.
    D=-(Y**2-1)*S
    compensated={}
    for n in (2,3,4):
        expr=even_reference((X+D)**n)
        expected=0 if n<4 else sp.Rational(3,4)*sp.Symbol('E_LLLL')
        for sign in (-1,1):
            old=sum(expr.subs(Y,(sign+b*sp.sqrt(3))/2) for b in (-1,1))/2
            new=sp.Rational(2+sign,4)*expr.subs(Y,1)+sp.Rational(2-sign,4)*expr.subs(Y,-1)
            assert sp.simplify(old-new-expected)==0
        compensated[str(n)]=str(expected)
    for expr,expected in [(even_reference(D**2),sp.Rational(3,4)*S*S),
                          (even_reference((X*D+D*X)/2),-sp.Rational(3,4)*S*S)]:
        for sign in (-1,1):
            old=sum(expr.subs(Y,(sign+b*sp.sqrt(3))/2) for b in (-1,1))/2
            new=sp.Rational(2+sign,4)*expr.subs(Y,1)+sp.Rational(2-sign,4)*expr.subs(Y,-1)
            assert sp.simplify(old-new-expected)==0
    matrix=sp.Rational(3,4)*S*S*sp.Matrix([[1,-1],[-1,1]])
    assert matrix.eigenvals()=={0:1,sp.Rational(3,2)*S*S:1}
    assert (sp.ones(1,2)*matrix*sp.ones(2,1))[0]==0
    eps=sp.symbols('epsilon',positive=True);a=sp.zeros(5)
    for k in range(1,5):a[k-1,k]=sp.sqrt(k)
    adag=a.T;Qosc=adag*a+eps*(a*a+adag*adag);vac=sp.eye(5)[:,0]
    v1,v2=Qosc*vac,Qosc**2*vac
    mu2,mu4=sp.expand(v1.dot(v1)),sp.expand(v2.dot(v2))
    assert mu2==2*eps**2 and mu4==8*eps**2+28*eps**4
    assert sp.simplify(mu4/mu2**2-(2/eps**2+7))==0
    lam2=s['lambda']**2;R=prepared['absolute_stress']['Qrho_absolute_integer_bound']
    assert R==508 and lam2==1073741824
    source_epsilon=F(2*R,lam2)
    assert source_epsilon==F(127,134217728)
    assert 1-source_epsilon==F(prepared['initial_existence']['M2_over_27lambda4_lower'])
    qstar,qt,z=sp.symbols('qstar qt z',real=True)
    mstar=1-2*qstar/lam2;residual=1-mstar*z-2*qt/lam2
    assert sp.factor(residual.subs(qt,qstar)-mstar*(1-z))==0
    d_lower=F(4330127,5000000)
    assert d_lower**2<F(3,4)
    branch_lower=d_lower-F(6*R,lam2)
    assert branch_lower>F(86602,100000)
    keys=['full_c0_over_D2_upper','all_mode_c1_over_D2_upper','d_squared',
          'relative_total_stress_variance_upper','old_mixture_relative_variance_lower']
    c0=F(s[keys[0]][1]);c1=F(s[keys[1]][1]);d2=F(s['d_squared'][0])
    assert c0>=0 and c1>=0 and d2>0
    variance=c0/(d2*d2*lam2*lam2)+c1/(d2*lam2)
    risk=F(16,3)*variance
    assert variance<F(4503,1000000) and risk<F(1501,62500)
    ratio=4*F(s['relative_total_stress_variance_upper'][1])/F(s['old_mixture_relative_variance_lower'][0])
    assert ratio<F(24017733110,10**12)
    return {'schema':'ueot-actual-source-readout/1','status':'PASS','moment_differences':differences,
      'noncommuting_words_kept_distinct':True,
      'correlated_compensation':{'device':'D=-(Y^2-1)*S',
          'field_device_covariance_increment':'(3/4)*S^2*[[1,-1],[-1,1]]',
          'joint_increment_positive_semidefinite':True,
          'total_centered_moment_differences':compensated,
          'quasifree_linear_L_fourth_moment_difference':'9*V1^2/4',
          'physical_device_implementation_proved':False,'equal_full_record_laws_claimed':False},
      'oscillator_second_moment':str(mu2),'oscillator_fourth_moment':str(mu4),
      'source_relative_bound':str(source_epsilon),'same_initial_branch_residual_lower':str(branch_lower),
      'archived_inputs':{key:s[key] for key in keys},
      'ideal_stress_risk_exact_upper':str(risk),'ideal_stress_risk_outward_gate':'1501/62500',
      'independent_risk_upper':str(ratio),
      'mean_only_geometry_record_theorem':{'common_mean_functional':True,
          'common_initial_and_boundary_data':True,'common_solution_selection_kernel_required':True,
          'geometry_only_common_instrument_kernel_required':True,'record_total_variation':0,
          'equal_prior_optimal_error':'1/2','direct_matter_readout_excluded_from_hypotheses':True},
      'scope':{'archived_fixed_background_only_for_numerical_risk':True,
               'Gaussian_completion_assumed':False,'fourth_moment_bound_assumed':False,
               'new_background_noise_certified':False,'gravity_POVM_or_device_built':False,
               'branchwise_geometry_is_inferred':False},
      'source_identity':{Path(__file__).name:hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}}

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--write',action='store_true');ap.add_argument('--check',action='store_true')
    args=ap.parse_args();result=compute();rendered=json.dumps(result,indent=2,sort_keys=True)+'\n';path=HERE/'source_readout.json'
    if args.write:path.write_text(rendered)
    if args.check:assert path.read_text()==rendered
    print('PASS: actual non-Gaussian source readout; distinct gravity closure required')
if __name__=='__main__':main()
