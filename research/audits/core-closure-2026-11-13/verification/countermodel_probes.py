"""Exact finite countermodels for an audit; no claim about current UEOT yet.

These witnesses test stronger interpretations that must be compared with the
current frozen contracts. Fractions make every displayed equality exact.
"""
from fractions import Fraction as F
import json


def frac(x):
    return str(x)


def run():
    out = {}

    # CM1: legal killed kernel does not entail persistence or implementation
    # of the law conditioned on survival.
    p = F(1, 2)
    k = [[p]]
    conditioned = [[F(1)]]
    assert all(sum(row) <= 1 for row in k)
    assert conditioned not in [k]
    out["killed_kernel_and_conditioning"] = {
        "kernel": [[frac(v) for v in r] for r in k],
        "survival_n_10": frac(p**10),
        "conditioned_row": ["1"],
        "conditioned_action_admissible": False,
        "limit_survival": "0 (since 0 < p < 1)",
    }

    # CM2: two microstates share an observation, but different next-block laws
    # obstruct a state-independent Markov quotient.
    states = ("a", "b", "c")
    obs = {"a": 0, "b": 0, "c": 1}
    nxt = {"a": "a", "b": "c", "c": "c"}
    assert obs["a"] == obs["b"]
    assert obs[nxt["a"]] != obs[nxt["b"]]
    out["non_lumpable_observation"] = {
        "observations": obs,
        "transition": nxt,
        "next_observation_from_a": obs[nxt["a"]],
        "next_observation_from_b": obs[nxt["b"]],
        "exact_markov_quotient_exists_for_all_initial_states": False,
    }

    # CM3: local feasibility need not survive composition with a shared budget.
    budget, cost_left, cost_right = 1, 1, 1
    assert cost_left <= budget and cost_right <= budget
    assert cost_left + cost_right > budget
    out["shared_resource_composition"] = {
        "budget": budget,
        "component_costs": [cost_left, cost_right],
        "each_locally_feasible": True,
        "joint_feasible": False,
    }

    # CM4: Price's identity does not make a selected trait increase.
    q = [F(1, 2), F(1, 2)]
    z, w = [F(0), F(1)], [F(2), F(1)]
    mean_w = sum(qi*wi for qi, wi in zip(q, w))
    before = sum(qi*zi for qi, zi in zip(q, z))
    after = sum(qi*wi*zi for qi, wi, zi in zip(q, w, z)) / mean_w
    cov = sum(qi*wi*zi for qi, wi, zi in zip(q, w, z)) - mean_w*before
    assert after - before == cov / mean_w == F(-1, 6)
    out["negative_price_selection"] = {
        "trait": list(map(frac, z)),
        "fitness": list(map(frac, w)),
        "initial_weights": list(map(frac, q)),
        "trait_before": frac(before),
        "trait_after": frac(after),
        "covariance_over_mean_fitness": frac(cov/mean_w),
    }

    # CM5: indistinguishable hidden modes require incompatible safe actions.
    # A randomized observation policy selects L with probability r; success
    # probabilities are r and 1-r, hence robust success <= 1/2.
    for n in range(101):
        r = F(n, 100)
        assert min(r, 1-r) <= F(1, 2)
    out["hidden_mode_control"] = {
        "modes": ["L", "R"],
        "observation_in_both_modes": "same",
        "safe_action_in_L": "L",
        "safe_action_in_R": "R",
        "full_information_success": "1",
        "best_robust_observation_success": "1/2",
        "proof": "min(r,1-r) <= (r+(1-r))/2 = 1/2; equality at r=1/2",
    }

    # CM6: an identity transition supplies dynamics without change/development.
    identity = [[F(1), F(0)], [F(0), F(1)]]
    assert all(sum(row) == 1 for row in identity)
    out["static_legal_dynamics"] = {
        "kernel": [[frac(v) for v in r] for r in identity],
        "legal_markov_dynamics": True,
        "forced_development": False,
    }

    # CM7: current books' nonconstant readout with an intervention-irrelevant
    # coordinate. This rebuts universal nonempty failure structure, not the
    # conditional minimal-cut reconstruction theorem.
    xs = [(x, u) for x in (0, 1) for u in (0, 1)]
    readout = lambda state: state[0]
    cut = lambda state: (state[0], 1-state[1])
    assert len({readout(x) for x in xs}) == 2
    assert all(readout(cut(x)) == readout(x) for x in xs)
    out["nonconstant_object_empty_failure_family"] = {
        "state_space": xs,
        "readout": "q(x,u)=x",
        "allowed_cut": "(x,u)->(x,1-u)",
        "nonconstant_readout": True,
        "any_allowed_cut_destroys_readout": False,
    }

    # CM8: exact independent calculations in the present census source.
    s, delta, b, gamma, damage = F(3, 4), F(1, 8), F(3, 8), F(1, 4), F(1, 3)
    kc, kb = s+b, s-delta+b+gamma
    rates = [kc, (1-damage)*kb+damage*kc]

    def two_bernoulli_counts(survival, birth):
        return [(1-survival)*(1-birth),
                survival*(1-birth)+(1-survival)*birth, survival*birth]

    low = two_bernoulli_counts(s, b)
    high = two_bernoulli_counts(s-delta, b+gamma)
    extinct_both = low[0]*high[0]
    high_extinct_low_nonzero = high[0]*(1-low[0])
    zero_extended_share = sum(low[i]*high[j]*F(j, i+j)
                              for i in range(3) for j in range(3) if i+j)
    conditional_share = zero_extended_share/(1-extinct_both)
    ratio_of_means = kb/(kc+kb)
    assert high[0] == F(9, 64)
    assert high_extinct_low_nonzero == F(243, 2048)
    assert extinct_both == F(45, 2048)
    assert zero_extended_share == F(2095, 4096)
    assert conditional_share == F(2095, 4006)
    assert ratio_of_means == F(10, 19)
    assert len({zero_extended_share, conditional_share, ratio_of_means}) == 3
    out["current_source_selection_boundaries"] = {
        "p_s_delta_b_gamma_q": list(map(frac, (s, delta, b, gamma, damage))),
        "program_growth_rates": list(map(frac, rates)),
        "best_program_first_tick_extinction": frac(high[0]),
        "best_extinct_other_nonzero": frac(high_extinct_low_nonzero),
        "both_extinct": frac(extinct_both),
        "expected_zero_extended_best_share": frac(zero_extended_share),
        "conditional_nonzero_best_share": frac(conditional_share),
        "ratio_expected_counts": frac(ratio_of_means),
        "source_locations": ["CoreRegenerativeSource.lean:215-238,352-402", "CSX-23:2395"],
    }

    # CM9: the current critical-parameter example. A direct 2x2 matrix
    # recurrence independently checks finite populations; no source checker is
    # imported. The all-time equality follows because the post-first-tick row
    # is proportional to nu and nu M = nu.
    s, delta, b, gamma, damage = F(2, 3), F(1, 8), F(1, 4), F(1, 4), F(1, 3)
    kc, kb = s+b, s-delta+b+gamma
    nu = [1-damage, damage]
    mat = [[kb*v for v in nu], [kc*v for v in nu]]
    vector = [F(0), F(1)]
    expectations = []
    assert sum(nu[i]*[kb, kc][i] for i in range(2)) == 1
    for n in range(1, 13):
        vector = [sum(vector[i]*mat[i][j] for i in range(2)) for j in range(2)]
        expectations.append(sum(vector))
    assert expectations == [F(11, 12)]*12
    out["current_source_exponent_not_horizon_optimality"] = {
        "p_s_delta_b_gamma_q": list(map(frac, (s, delta, b, gamma, damage))),
        "program_growth_factor": "1",
        "damaged_program_expected_population_n_1_to_12": list(map(frac, expectations)),
        "damaged_refusal_expected_population_every_n": "1",
        "all_time_proof": "first row = (11/12)*nu and nu*M=nu",
    }

    # CM10: rank three at a legal source point. The determinant is b.
    b, damage = F(3, 8), F(1, 3)
    jacobian = [[F(1), F(0), F(0)], [F(0), F(1), F(0)], [F(0), damage, b]]
    determinant = jacobian[0][0]*jacobian[1][1]*jacobian[2][2]
    assert determinant == F(3, 8) > 0
    out["current_source_no_smooth_common_two_dimensional_factor"] = {
        "response": "F(s,b,q)=(s,b,bq)",
        "jacobian_at_point": [[frac(v) for v in row] for row in jacobian],
        "determinant": frac(determinant),
        "proof": "rank D(g o h) <= 2 for C1 h:R3->R2, g:R2->R3; rank DF=3",
        "restriction": "C1 common encoding of all three responses on an open parameter neighborhood",
    }
    return out


if __name__ == "__main__":
    print(json.dumps(run(), ensure_ascii=False, indent=2))
