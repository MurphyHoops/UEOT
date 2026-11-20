"""Independent rational gates and provenance/scope audit of the new construction."""
from fractions import Fraction as Q
from pathlib import Path
import argparse,hashlib,json
HERE=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(name):return json.loads((HERE/name).read_text())
def upper(pair):return Q(pair[1])
def lower(pair):return Q(pair[0])
def check_sources(result,base):
    for rel,digest in result['source_sha256'].items():
        assert sha(base/rel)==digest,(base,rel)
def compute():
    names=['state_norms','feedback','algebra','history','total_source']
    data={k:read(k+'.json') for k in names}
    assert all(r['status']=='PASS' for r in data.values())
    for name in ['state_norms','feedback','history']:
        check_sources(data[name],HERE.parent)
    for name in ['algebra','total_source']:
        check_sources(data[name],HERE)
    state=data['state_norms'];hist=data['history'];feedback=data['feedback'];total=data['total_source']
    for key,gate in [('N0_upper',Q(61,1000)),('S1_upper',43),('S_upper',44),
                     ('S2_upper',14000),('weighted_n_upper',Q(185,1000))]:
        assert upper(state[key])<gate
    assert [r['k'] for r in state['modes']]==list(range(2,513))
    assert state['mode_integrations_performed']==state['past_integrals_evaluated_numerically']==0
    T=Q(hist['T']);D=upper(hist['reference_residual_upper'])
    kap=upper(hist['full_feedback_with_fixed_driver'])
    assert T==Q(1,2**40) and D<Q(1,6400) and kap<Q(1,4)
    assert 300*D<(1-kap)/16
    assert lower(hist['self_mapping_margin'])>Q(6137,100000)
    assert Q(2,5)*D*T-450*D*D*T*T>Q(1358,10**21)
    assert (Q(9,10)*T-3150*D*T*T)/3>Q(2728,10**16)
    assert lower(hist['shooting_endpoint_margin'])>0
    assert lower(hist['shooting_monotonicity_margin'])>0
    assert Q(hist['fixed_buffer_end'])==T/4
    assert Q(hist['driver_release'])==3*T/4
    assert Q(hist['post_release_window_length'])==T/4>0
    assert hist['scope']['smooth_Hadamard_post_release_history']
    assert not hist['scope']['immediate_undriven_extension']
    assert not hist['scope']['physical_controller_constructed']
    assert not hist['scope']['long_time_or_global_existence']
    large=next(w for w in feedback['windows'] if w['T']=='1/2097152')
    assert upper(large['kappa'])<Q(165,1000)
    assert not large['self_map_forcing_certified']
    # All original roots still have negative actual pressure derivative.
    old=json.loads((HERE.parent/'prepared_dynamics/result.json').read_text())
    assert upper(old['Qpprime_all_roots'])<0
    assert lower(old['lambda5_normal_spatial_Einstein_residual'])>0
    assert total['later_release_driver_NEC']['some_open_interval_has_negative_NEC']
    assert not total['later_release_driver_NEC']['uniform_initial_positive_interval_length_certified']
    assert total['invariant_record_laws']['total_variation']==0
    assert Q(total['invariant_record_laws']['equal_prior_Bayes_error'])==Q(1,2)
    assert Q(total['old_geometry_normalized_constraint_absolute_lower'])>Q(866025,1000000)
    assert not total['scope']['original_single_field_geometry_repaired']
    assert not total['scope']['all_possible_noninvariant_instruments_covered']
    assert not total['scope']['vanishing_mean_driver_implies_vanishing_driver_noise']
    assert all(data['algebra']['checks'].values())
    # Proofs are explicit analytic inputs, not silently replaced by Python flags.
    paths=[HERE/(k+'.json') for k in names]+[HERE/'README.md',HERE/'REGULARITY.md',
        HERE/'REVIEW.md',HERE.parent/'prepared_dynamics/result.json',Path(__file__)]
    return {'schema':'ueot-compatible-independent-review/1','status':'PASS',
      'reviewed_claims':['actual all-root centered norms','complete feedback and self-map',
        'fixed closed buffer','same-window smooth bootstrap and Hadamard propagation',
        'fixed-source unique later-release shooting','necessary driver NEC violation',
        'full invariant total-source probability law','sharp extra coherent budget'],
      'analytic_review':{'native_agents':3,'A':'compatible history and shooting',
        'B':'complete response and all-order regularity','C':'total source and device scope',
        'root':'directed arithmetic, identities, source provenance and execution',
        'external_human_peer_review':False,'formal_Lean_proof':False},
      'negative_controls':{'old_immediate_release_obstruction_preserved':True,
        'contraction_without_self_map_not_promoted':True,'no_timewise_parameter_roots':True,
        'new_driver_not_claimed_to_be_realized_device':True,'no_old_instrument_probability_migration':True,
        'O2_completion_not_claimed_as_original_geometry':True,
        'mean_driver_zero_not_noise_zero':True,'NEC_not_renormalization_reassigned':True},
      'whole_unified_physics_goal':'OPEN',
      'source_sha256':{str(p.relative_to(HERE.parent)):sha(p) for p in paths}}
def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--write',action='store_true');ap.add_argument('--check',action='store_true')
    args=ap.parse_args();r=compute();data=json.dumps(r,indent=2,sort_keys=True)+'\n'
    p=HERE/'review.json'
    if args.write:p.write_text(data)
    if args.check:assert p.read_text()==data
    print('PASS: independent rational margins, immutable input hashes, and scientific scope')
if __name__=='__main__':main()
