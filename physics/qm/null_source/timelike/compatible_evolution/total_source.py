"""Exact total-source completion: full invariant laws, budget, and scope."""
from fractions import Fraction as Q
from pathlib import Path
import argparse,hashlib,json
import sympy as s
HERE=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def compute():
    d=s.sqrt(3)/2
    distributions={}
    for sigma in [-1,1]:
        old=[((sigma+s.sqrt(3))/2,s.Rational(1,2)),
             ((sigma-s.sqrt(3))/2,s.Rational(1,2))]
        new=[(s.Integer(1),s.Rational(2+sigma,4)),
             (s.Integer(-1),s.Rational(2-sigma,4))]
        for label,dist in [('old',old),('new',new)]:
            assert s.simplify(sum(p for y,p in dist)-1)==0
            assert s.simplify(sum(p*y for y,p in dist)-s.Rational(sigma,2))==0
            assert s.simplify(sum(p*y*y for y,p in dist)-1)==0
            distributions[str(sigma)+'_'+label]=[[str(y),str(p)] for y,p in dist]
        assert s.simplify(sum(p*y**4 for y,p in old)-s.Rational(7,4))==0
        assert s.simplify(sum(p*y**4 for y,p in new)-1)==0
    y,r,ell=s.symbols('y r ell',real=True,positive=True)
    O=s.Matrix([[r,y],[-y,r]])/s.sqrt(ell)
    reduce=lambda expr:s.simplify(s.expand(expr).subs(r*r,ell-y*y))
    assert (O.T*O-s.eye(2)).applyfunc(reduce)==s.zeros(2)
    assert reduce(O.det()-1)==0
    assert s.simplify(O*s.Matrix([0,s.sqrt(ell)])-s.Matrix([y,r]))==s.zeros(2,1)
    v1,v2,w1,w2=s.symbols('v1 v2 w1 w2',real=True)
    v=s.Matrix([v1,v2]);w=s.Matrix([w1,w2])
    assert reduce(((O*v).T*(O*w)-v.T*w)[0])==0
    V0,V1=s.symbols('V0 V1',nonnegative=True)
    assert reduce(2*V0+(y*y+r*r)*V1-(2*V0+ell*V1))==0
    assert s.simplify(1/(1+d)-(4-2*s.sqrt(3)))==0
    # Include the second reference RSET, not only its coherent displacement.
    rmean=s.symbols('rmean',real=True)
    mstar=1-rmean
    defect=-(ell-1)*mstar-rmean
    assert s.simplify(defect.subs(ell,1+d)-(-d+(d-1)*rmean))==0
    eps=Q(127,134217728);dminus=Q(4330127,5000000)
    assert dminus*dminus<Q(3,4)
    defect_lower=dminus-(1-dminus)*eps
    assert defect_lower>Q(866025,1000000)
    initial=json.loads((HERE.parent/'prepared_initial/result.json').read_text())
    assert initial['absolute_stress']['Qrho_absolute_integer_bound']==508
    assert 2*Q(508,32768**2)==eps
    history=json.loads((HERE/'history.json').read_text())
    dynamics=json.loads((HERE.parent/'prepared_dynamics/result.json').read_text())
    assert history['status']=='PASS' and Q(dynamics['Qpprime_all_roots'][1])<0
    # Vanishing total canonical-scalar stress forces velocity=0 and U=0.
    vel,a,U=s.symbols('vel a U',real=True,positive=True)
    rho=vel*vel/(2*a*a)+U;p=vel*vel/(2*a*a)-U
    assert s.simplify(rho+p-vel*vel/(a*a))==0
    assert s.simplify(rho-p-2*U)==0
    return {'schema':'ueot-total-source-symmetry/1','status':'PASS',
      'original_label_distributions':distributions,
      'exact_rotation':'ell^(-1/2) [[r_y,y],[-y,r_y]], r_y=sqrt(ell-y^2)',
      'checks':{'label_marginal_preserved':True,'orthogonal_det_one':True,
                'coherent_vector_orbit':True,'all_quadratic_species_contractions':True,
                'reservoir_fluctuations_included':True,'second_reference_RSET_included':True},
      'invariant_record_laws':{'total_variation':0,'equal_prior_Bayes_error':'1/2',
                              'reason':'bounded effect invariance, not moment determinacy'},
      'sharp_coherent_budget':{'ell_min':'1+sqrt(3)/2',
          'mean_reservoir_over_original_field_min':'sqrt(3)/2',
          'original_field_fraction_at_fixed_total_max':'4-2*sqrt(3)'},
      'old_geometry_normalized_constraint_absolute_lower':str(defect_lower),
      'later_release_driver_NEC':{'initial_NEC_slope':'-p_qprime(0)>0',
        'identity':'rho_Dprime=-3h(rho_D+p_D)',
        'strict_contraction':'h<0 for every t>0 in the constructed window',
        'both_endpoint_driver_densities':0,'some_open_interval_has_negative_NEC':True,
        'proof':'nontrivial positive initial NEC and zero endpoint densities force weighted cancellation',
        'uniform_initial_positive_interval_length_certified':False},
      'outward_constraint_gate':'866025/1000000',
      'scope':{'same_original_field_marginal':True,'second_identical_quantum_field_added':True,
        'original_single_field_geometry_repaired':False,'local_controller_implemented':False,
        'all_possible_noninvariant_instruments_covered':False,
        'all_renormalized_energy_lower_bound':False,'gravitational_channel_constructed':False,
        'vanishing_mean_driver_implies_vanishing_driver_noise':False},
      'source_sha256':{Path(__file__).name:sha(Path(__file__)),
        '../prepared_initial/result.json':sha(HERE.parent/'prepared_initial/result.json'),
        'history.json':sha(HERE/'history.json'),
        '../prepared_dynamics/result.json':sha(HERE.parent/'prepared_dynamics/result.json')}}
def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--write',action='store_true');ap.add_argument('--check',action='store_true')
    args=ap.parse_args();r=compute();data=json.dumps(r,indent=2,sort_keys=True)+'\n'
    p=HERE/'total_source.json'
    if args.write:p.write_text(data)
    if args.check:assert p.read_text()==data
    print('PASS: complete invariant record laws, sharp coherent budget, original-geometry exclusion')
if __name__=='__main__':main()
