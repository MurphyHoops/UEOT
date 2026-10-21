"""Independent finite arithmetic for a written contract; no Lean execution."""

from fractions import Fraction as F
import json
from pathlib import Path


def row(v, matrix):
    return [sum((v[i] * matrix[i][j] for i in range(len(v))), F(0))
            for j in range(len(matrix))]


def col(matrix, v):
    return [sum((r[j] * v[j] for j in range(len(v))), F(0)) for r in matrix]


def masses(v, matrix, horizon):
    out = [sum(v, F(0))]
    for _ in range(horizon):
        v = row(v, matrix)
        out.append(sum(v, F(0)))
    return out


def mul(a, b):
    return [[sum((a[i][k] * b[k][j] for k in range(len(b))), F(0))
             for j in range(len(b))] for i in range(len(a))]


def absorbing_completion(q):
    n = len(q)
    assert all(x >= 0 for r in q for x in r)
    assert all(sum(r, F(0)) <= 1 for r in q)
    p = [r + [1 - sum(r, F(0))] for r in q]
    p += [[F(0)] * n + [F(1)]]
    assert all(sum(r, F(0)) == 1 for r in p)
    return p


def finite_conditioned_kernel(q, remaining):
    assert remaining > 0
    g_previous = [F(1)] * len(q)
    for _ in range(remaining - 1):
        g_previous = col(q, g_previous)
    g = col(q, g_previous)
    assert all(value > 0 for value in g)
    return [[q[i][j] * g_previous[j] / g[i] for j in range(len(q))]
            for i in range(len(q))]


def rational_json(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {k: rational_json(v) for k, v in value.items()}
    if isinstance(value, list):
        return [rational_json(v) for v in value]
    return value


results = {}

q = [[F(0), F(1)], [F(0), F(0)]]
assert mul(q, q) == [[F(0), F(0)], [F(0), F(0)]]
assert masses([F(1), F(0)], q, 2) == [F(1), F(1), F(0)]
results['8.1_nilpotent'] = {
    'actual_stochastic_completion': absorbing_completion(q),
    'survival_n_0_1_2': masses([F(1), F(0)], q, 2),
    'positive_QSD_impossibility': 'Written coordinate proof, not inferred from numerical search.'
}

q = [[F(0), F(0)], [F(1, 2), F(1, 2)]]
r, rho = [F(1, 2), F(1, 2)], F(1, 2)
assert row(r, q) == [rho * x for x in r]
assert masses([F(1), F(0)], q, 2) == [F(1), F(0), F(0)]
results['8.2_full_support_QSD_dead_initial_state'] = {
    'actual_stochastic_completion': absorbing_completion(q),
    'left_QSD': r,
    'rho': rho,
    'left_product': row(r, q),
    'delta_a_survival_n_0_1_2': masses([F(1), F(0)], q, 2),
    'QSD_initial_survival_n_0_1_2': masses(r, q, 2),
}

p_return = [[F(0), F(1)], [F(1), F(0)]]
p_absorb = [[F(0), F(1)], [F(0), F(1)]]
delta_a = [F(1), F(0)]
assert row(row(delta_a, p_return), p_return)[0] == 1
assert row(row(delta_a, p_absorb), p_absorb)[0] == 0
assert masses([F(1)], [[F(0)]], 2) == [F(1), F(0), F(0)]
results['8.3_return_requires_nonabsorbing_outside_state'] = {
    'actual_return_matrix': p_return,
    'terminal_safe_probability_at_2': row(row(delta_a, p_return), p_return)[0],
    'survival_n_0_1_2': masses([F(1)], [[F(0)]], 2),
    'absorbing_alternative_terminal_safe_at_2': row(row(delta_a, p_absorb), p_absorb)[0],
}

q = [[F(1, 4), F(1, 8)], [F(1, 2), F(1, 4)]]
h, r, rho = [F(1), F(2)], [F(2, 3), F(1, 3)], F(1, 2)
assert col(q, h) == [rho * x for x in h]
assert row(r, q) == [rho * x for x in r]
doob = [[q[i][j] * h[j] / (rho * h[i]) for j in range(2)] for i in range(2)]
one_step = finite_conditioned_kernel(q, 1)
two_steps = finite_conditioned_kernel(q, 2)
assert doob == [[F(1, 2), F(1, 2)]] * 2
assert one_step == [[F(2, 3), F(1, 3)]] * 2
assert two_steps == doob
g1 = col(q, [F(1), F(1)])
survival_1 = sum((r[i] * g1[i] for i in range(2)), F(0))
conditional_initial = [r[i] * g1[i] / survival_1 for i in range(2)]
conditional_terminal = [x / survival_1 for x in row(r, q)]
assert conditional_initial == [F(1, 2), F(1, 2)]
assert conditional_terminal == r
pairing = sum((r[i] * h[i] for i in range(2)), F(0))
doob_initial = [r[i] * h[i] / pairing for i in range(2)]
conditioned_paths = [[r[i] * q[i][j] / survival_1 for j in range(2)] for i in range(2)]
doob_paths = [[doob_initial[i] * doob[i][j] for j in range(2)] for i in range(2)]
path_tv = sum((abs(conditioned_paths[i][j] - doob_paths[i][j])
               for i in range(2) for j in range(2)), F(0)) / 2
assert path_tv == F(1, 6)
results['8.4_Doob_vs_finite_window'] = {
    'actual_stochastic_completion': absorbing_completion(q),
    'rho': rho, 'positive_h': h, 'left_QSD': r,
    'Q_h': col(q, h), 'r_Q': row(r, q),
    'Doob_kernel': doob,
    'one_remaining_step_conditional_kernel': one_step,
    'two_remaining_steps_conditional_kernel': two_steps,
    'QSD_initial_survival_at_1': survival_1,
    'initial_law_given_survival_at_1': conditional_initial,
    'terminal_law_given_survival_at_1': conditional_terminal,
    'Doob_h_tilted_initial': doob_initial,
    'one_step_conditional_full_path_masses': conditioned_paths,
    'one_step_Doob_full_path_masses': doob_paths,
    'one_step_path_TV': path_tv,
}

q = [[F(1, 2), F(0)], [F(0), F(1, 2)]]
different_qsds = [[F(1), F(0)], [F(0), F(1)], [F(1, 3), F(2, 3)]]
for r in different_qsds:
    assert row(r, q) == [x / 2 for x in r]
results['8.5_nonunique_QSD'] = {
    'actual_stochastic_completion': absorbing_completion(q),
    'distinct_QSD_examples': different_qsds,
    'rho': F(1, 2),
}

q = [[F(1, 2)]]
eta0 = [F(1, 3)]
assert masses(eta0, q, 2) == [F(1, 3), F(1, 6), F(1, 12)]
results['arbitrary_initial_mass_including_failure_at_zero'] = {
    'actual_initial_on_safe_then_cemetery': [F(1, 3), F(2, 3)],
    'actual_stochastic_completion': absorbing_completion(q),
    'survival_n_0_1_2': masses(eta0, q, 2),
    'ever_failure_at_zero': F(2, 3),
    'conditional_safe_initial_given_S0': [F(1)],
}

assert masses([], [], 2) == [F(0), F(0), F(0)]
results['empty_safe_type'] = {
    'survival_n_0_1_2': masses([], [], 2),
    'ever_failure_at_zero': F(1),
    'conditional_PMF_constructed': False,
}

record = {
    'status': 'EXACT_RATIONAL_ARITHMETIC_CHECKED_NOT_LEAN',
    'scope': 'Concrete finite examples only; no universal theorem or Lean/API check claimed.',
    'uses_floating_point': False,
    'compiled_Lean': False,
    'production_modified': False,
    'checks': results,
}
output = Path(__file__).with_name('RATIONAL_CHECKS.json')
output.write_text(json.dumps(rational_json(record), ensure_ascii=False, indent=2) + '\n')
print(json.dumps({'status': record['status'], 'example_count': len(results), 'output': str(output)}))
