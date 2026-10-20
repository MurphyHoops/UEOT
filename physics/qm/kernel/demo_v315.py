"""Exact witnesses for finite mixture and persistence interfaces (no empirical data)."""

from fractions import Fraction as F
import json

from ueot_qm import Matrix, diagonal, identity, Instrument, KrausTerm, real_trace
from ueot_qm.finite_dynamics import (
    ProbabilityWeights, MixtureWeightBudget, channel_operator,
    cesaro_average, substochastic_instrument,
)


def main():
    stay = Instrument({"ok": [KrausTerm(identity(2))]})
    flip = Instrument({"ok": [KrausTerm(Matrix([[0, 1], [1, 0]]))]})
    rho = diagonal([1, 0])
    budget = MixtureWeightBudget((stay, flip), ProbabilityWeights([F(3, 4), F(1, 4)]),
                                ProbabilityWeights([F(1, 4), F(3, 4)]))
    observed = abs(real_trace(rho @ (channel_operator(budget.left, rho)
                                     - channel_operator(budget.right, rho))))
    if observed != budget.upper_bound:
        raise ArithmeticError("the sharp mixture witness failed")
    cycle = []
    for n in (1, 2, 3, 4, 5, 7):
        average = cesaro_average(flip, rho, n)
        observed_residual = abs(real_trace(rho @ (channel_operator(flip, average) - average)))
        if observed_residual != F(n % 2, n):
            raise ArithmeticError("the alternating Cesaro witness failed")
        cycle.append({"N": n, "P0_average": real_trace(rho @ average),
                      "P0_invariance_residual": observed_residual, "all_effect_budget": F(1, n)})
    Q = ((F(1, 4), F(1, 2)), (F(1, 8), F(1, 4)))
    q, h, r = (F(1, 3), F(2, 3)), (F(3, 2), F(3, 4)), F(1, 2)
    qsd = diagonal(q)
    killed = substochastic_instrument(Q)
    state, survival = qsd, []
    for n in range(1, 7):
        state = killed.branch(state, "survive")
        mass = real_trace(state)
        if state != qsd * r ** n or mass != r ** n:
            raise ArithmeticError("the exact QSD survival witness failed")
        survival.append({"n": n, "mass": mass, "posterior_equals_qsd": state / mass == qsd})
    doob = tuple(tuple(Q[i][j] * h[j] / (r * h[i]) for j in range(2)) for i in range(2))
    pi = tuple(q[i] * h[i] for i in range(2))
    conditioned = substochastic_instrument(doob)
    if pi == q or channel_operator(conditioned, diagonal(pi)) != diagonal(pi):
        raise ArithmeticError("the QSD/Doob distinction witness failed")
    output = {
        "schema": "ueot_qm.finite_dynamics_demo.v31.5",
        "mixture": {"library": "identity, Pauli X", "component_fingerprint": budget.component_fingerprint,
                    "left_weights": budget.left_weights.values, "right_weights": budget.right_weights.values,
                    "computed_TV_upper_budget": budget.upper_bound, "attaining_P0_difference": observed},
        "cesaro_alternating_orbit": cycle,
        "survival": {"row_substochastic_Q": Q, "q": q, "r": r, "h": h, "word_witnesses": survival,
                     "Doob_Q": doob, "Doob_stationary_pi": pi, "pi_differs_from_q": pi != q,
                     "uniform_initial_survival": killed.probability(identity(2) / 2, "survive"),
                     "transposed_Q_survival": substochastic_instrument(tuple(zip(*Q))).probability(qsd, "survive")},
        "scope": [
            "Exact rational runtime witnesses, not empirical observations or a proof of Python execution",
            "Mixture budget requires one fixed component library; it is not a diamond-norm certificate",
            "Cesaro stationary existence does not assert unique stationarity or convergence of the raw orbit",
            "Diagonal survival transfers Core QSD premises; it does not reconstruct noncommutative Perron theory",
        ],
    }
    print(json.dumps(output, ensure_ascii=False, indent=2,
                     default=lambda value: str(value) if isinstance(value, F) else value))


if __name__ == "__main__":
    main()
