"""Declared fixtures; real outcomes and hidden Kraus multiplicities stay separate."""
import json
from fractions import Fraction
from pathlib import Path
import numpy as np
from finite_conditioning import Instrument, Leaf, Node, repeated_success_tree


def load_registered_model(path):
    path = Path(path)
    plan = json.loads(path.read_text())
    if plan["schema"] != "ueot-qm.finite-conditioning-reference/1":
        raise ValueError("unsupported registered-plan schema")
    protocol = plan["protocol"]
    if protocol["kind"] != "repeated_success_with_early_failure" or not protocol["stop_on_failure"]:
        raise ValueError("registered protocol semantics changed")

    def matrix(rows):
        return np.array([[float(Fraction(x)) for x in row] for row in rows], complex)

    inst = Instrument({o: tuple(matrix(k) for k in ks)
                       for o, ks in plan["source_instrument"].items()})
    rho = matrix(plan["initial_density"]["real"]) + 1j * matrix(plan["initial_density"]["imag"])
    tree = repeated_success_tree(inst, set(protocol["success_labels"]), protocol["horizon"])
    return inst, tree, rho


def t3(plan_path=None):
    return load_registered_model(plan_path or Path(__file__).with_name("frozen_plan.json"))


def positive_chain():
    path = Path(__file__).with_name("positive_chain_plan.json")
    inst, tree, rho = load_registered_model(path)
    plan = json.loads(path.read_text())
    def matrix(rows):
        return np.array([[float(Fraction(x)) for x in row] for row in rows], complex)
    library = {a: Instrument({o: tuple(matrix(k) for k in ks) for o, ks in branches.items()})
               for a, branches in plan["allowed_library"].items()}
    return inst, tree, rho, library


def projective_record(swapped=False):
    p0, p1 = np.diag([1, 0]), np.diag([0, 1])
    return Instrument({"0": (p1 if swapped else p0,), "1": (p0 if swapped else p1,)})


def singular_one_step():
    inst = projective_record()
    return Node(inst, {"0": Leaf(True), "1": Leaf(False)}), np.eye(2) / 2


def early_stop():
    first = projective_record()
    coin = Instrument({"pass": (np.eye(2) / np.sqrt(2),),
                       "fail": (np.eye(2) / np.sqrt(2),)})
    child = Node(coin, {"pass": Leaf(True), "fail": Leaf(False)})
    return Node(first, {"0": Leaf(True), "1": child}), np.eye(2) / 2


def diagonal_classical():
    # Hidden j,i Kraus implement actual classical transition kernels and erase
    # off-diagonal inputs. Visible labels a,b remain genuine source outcomes.
    q = {"a": np.array([[1 / 4, 0], [1 / 8, 1 / 4]]),
         "b": np.array([[0, 1 / 8], [1 / 4, 0]])}
    total = sum(q.values())
    q["failure"] = np.diag(1 - total.sum(axis=0))
    branches = {}
    for o, matrix in q.items():
        ks = []
        for j in range(2):
            for i in range(2):
                k = np.zeros((2, 2), complex)
                k[j, i] = np.sqrt(matrix[j, i])
                ks.append(k)
        branches[o] = tuple(ks)
    instrument = Instrument(branches)
    return instrument, repeated_success_tree(instrument, {"a", "b"}, 2), np.diag([2 / 3, 1 / 3]), q


def deterministic_label(label):
    return Instrument({"0": (np.array([[1 if label == "0" else 0]], complex),),
                       "1": (np.array([[1 if label == "1" else 0]], complex),)})


def out_of_library():
    p0, p1 = np.diag([1, 0]), np.diag([0, 1])
    x = np.array([[0, 1], [1, 0]], complex)
    dephasing = Instrument({"out": (p0, p1)})
    flipped = Instrument({"out": (x @ p0, x @ p1)})
    identity = Instrument({"out": (np.eye(2),)})
    return identity, dephasing, flipped
