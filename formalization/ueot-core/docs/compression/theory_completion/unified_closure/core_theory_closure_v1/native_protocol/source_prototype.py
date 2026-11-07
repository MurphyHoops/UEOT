#!/usr/bin/env python3
"""Exact local source prototype for the core theory closure.

This is a specification probe, not a Lean certificate.  It reads literal code,
executes paid repair before the same program's action, and emits actual retained
and newborn records.  No expected population matrix is an input.
"""
from __future__ import annotations

from collections import defaultdict
from dataclasses import asdict, dataclass, replace
from fractions import Fraction as F
from itertools import product
import json
from pathlib import Path


@dataclass(frozen=True)
class Parameters:
    survival: F
    care_only_survival: F
    common_birth: F
    bloom_only_birth: F
    damage: F
    supply: int = 5
    reserve: int = 1

    def validate(self):
        s, d, b, g, q = (self.survival, self.care_only_survival,
                          self.common_birth, self.bloom_only_birth, self.damage)
        assert 0 < d < s < 1 and 0 < b and b + g < 1
        assert d < g and 0 < q < 1
        assert s + b > 1  # open-environment supercritical positive branch
        assert self.supply == 5 and self.reserve == 1


@dataclass(frozen=True)
class Body:
    code: tuple[tuple[bool, bool, bool], tuple[bool, bool, bool]]
    gate: bool
    bootstrap: bool = True
    # A silent physical tag is deliberately not controller-readable.  It is the
    # first nontrivial quotient coordinate, not an individual identity.
    tag: bool = False


@dataclass(frozen=True)
class Organism:
    identity: tuple[tuple[int, int], ...]
    parent: tuple[tuple[int, int], ...] | None
    born_at: int
    age: int
    body: Body
    wallet: int = 1


def majority(row):
    a, b, c = row
    return (a and b) or (a and c) or (b and c)


def decode(body):
    return tuple(majority(row) for row in body.code)


def encode(rows, *, tag=False):
    return Body(tuple((x, x, x) for x in rows), True, True, tag)


def damage(body, damaged):
    if not damaged:
        return body
    return replace(body, code=tuple((not a, b, c) for a, b, c in body.code), gate=False)


def visible(body):
    # All six code cells and the real main gate are an explicitly allowed
    # diagnostic sensor.  Identity, true program label, tag and noise are absent.
    return body.code, body.gate, body.bootstrap


def damaged(body):
    return (not body.gate) or any(a != b or b != c for a, b, c in body.code)


def repair(body):
    """A finite trusted majority/read/write primitive, with no desired θ input."""
    target = tuple((majority(row),) * 3 for row in body.code)
    changed_cells = sum(x != y for old, new in zip(body.code, target)
                        for x, y in zip(old, new))
    fee = changed_cells + int(not body.gate)
    if fee and not body.bootstrap:
        return body, 0, False
    return replace(body, code=target, gate=True), fee, True


def raw_execute(body, original_diagnostic):
    if not body.gate:
        return None
    bit = body.code[int(original_diagnostic)][0]
    return "bloom" if bit else "care"


def operation_fee(action):
    return {"care": 1, "bloom": 2, "stop": 0}[action]


def program_request(body):
    # Bootstrap decodes the row only to prepay its request.  After restoration,
    # execution below reads the actual repaired active cell again.
    return "bloom" if decode(body)[int(damaged(body))] else "care"


def atoms(p):
    s, d, b, g, q = (p.survival, p.care_only_survival,
                     p.common_birth, p.bloom_only_birth, p.damage)
    sw = (1-s, d, s-d)          # neither, care-only, both modes retain parent
    bw = (1-b-g, g, b)          # neither, bloom-only, both modes create child
    dw = (1-q, q)
    for u, v, dp, dc in product(range(3), range(3), (False, True), (False, True)):
        yield (u, v, dp, dc), sw[u] * bw[v] * dw[dp] * dw[dc]


def tick(p, old, t, noise, *, request=None, supplied=None):
    """One old census member is processed once.  Children are returned, not run."""
    flow = p.supply if supplied is None else supplied
    available = old.wallet + flow
    before_damaged = damaged(old.body)
    asked = program_request(old.body) if request is None else request
    if asked == "stop":
        return dict(status="stopped", request=asked, before=old, repaired=old.body,
                    repair_fee=0, operation_fee=0, actual_fee=0,
                    available=available, source_inflow=flow, request_cap=0,
                    returned_to_environment=available, outputs=[], noise_used=False)

    restored, repair_fee, boot_ok = repair(old.body)
    # Request cap reserves both possible live records.  Actual payment later
    # depends on the unobserved outcome, but it cannot validate the cap retroactively.
    cap = repair_fee + operation_fee(asked) + 2*p.reserve
    if cap > available or not boot_ok:
        # Rejection is an actual non-executed transaction.  It leaves the old
        # organism and old balance unchanged, refunds the unconsumed flow, and
        # does not read this tick's unobserved random atom.
        return dict(status="rejected", reason="bootstrap" if not boot_ok else "funds",
                    request=asked, before=old, repaired=old.body,
                    repair_fee=0, operation_fee=0, actual_fee=0,
                    available=available, source_inflow=flow, request_cap=cap,
                    returned_to_environment=flow, outputs=[old], noise_used=False)

    if request is None:
        actual = raw_execute(restored, before_damaged)
        assert actual == asked
    else:
        # An explicit allowed request port is used only for the comparison class.
        # It has the same body, bootstrap, cap and event operation as the internal program.
        actual = asked if restored.gate else None
    assert actual in ("care", "bloom")
    u, v, dp, dc = noise
    retain = (u == 2) or (u == 1 and actual == "care")
    born = (v == 2) or (v == 1 and actual == "bloom")
    outputs = []
    if retain:
        outputs.append(replace(old, age=old.age+1, body=damage(restored, dp), wallet=p.reserve))
    if born:
        child_id = old.identity + ((t+1, 0),)
        outputs.append(Organism(child_id, old.identity, t+1, 0,
                                damage(restored, dc), p.reserve))
    op_fee = operation_fee(actual)
    actual_fee = repair_fee + op_fee
    refund = available - actual_fee - p.reserve*len(outputs)
    assert refund >= 0
    assert available == actual_fee + sum(x.wallet for x in outputs) + refund
    return dict(status="executed", request=asked, actual_action=actual,
                before=old, repaired=restored, repair_fee=repair_fee,
                operation_fee=op_fee, actual_fee=actual_fee,
                available=available, source_inflow=flow, request_cap=cap,
                returned_to_environment=refund, outputs=outputs, noise_used=True,
                retained=retain, newborn=born, noise=noise)


def founder(theta, d, n=0, tag=False):
    # θ=false compiles care/care; θ=true compiles bloom/care.
    return Organism(((0, n),), None, 0, 0, damage(encode((theta, False), tag=tag), d))


def census_round(p, population, t, noises):
    assert len(population) == len(noises)
    receipts = [tick(p, old, t, w) for old, w in zip(population, noises)]
    assert all(r["status"] == "executed" for r in receipts)
    out = [x for r in receipts for x in r["outputs"]]
    assert len(out) <= 2*len(population)
    assert len({x.identity for x in out}) == len(out)
    assert sum(r["source_inflow"] for r in receipts) == 5*len(population)
    return out, receipts


def serializable(value):
    if isinstance(value, F): return str(value)
    if hasattr(value, "__dataclass_fields__"): return serializable(asdict(value))
    if isinstance(value, dict): return {str(k): serializable(v) for k, v in value.items()}
    if isinstance(value, (list, tuple)): return [serializable(v) for v in value]
    return value


def main():
    p = Parameters(F(3,4), F(1,8), F(3,8), F(1,4), F(1,3))
    p.validate()
    assert sum(w for _, w in atoms(p)) == 1
    rows, outcomes = {}, []
    for theta, d in product((False, True), repeat=2):
        old = founder(theta, d)
        L, B = [F(0), F(0)], [F(0), F(0)]
        for w, mass in atoms(p):
            r = tick(p, old, 0, w)
            assert r["status"] == "executed"
            assert decode(r["repaired"]) == (theta, False) and r["repaired"].gate
            assert r["repair_fee"] == (3 if d else 0)
            for out in r["outputs"]:
                assert decode(out.body) == (theta, False)
                if out.identity == old.identity:
                    L[int(damaged(out.body))] += mass
                    assert out.parent == old.parent and out.age == old.age+1
                else:
                    B[int(damaged(out.body))] += mass
                    assert out.parent == old.identity and out.born_at == 1 and out.age == 0
            outcomes.append(dict(program=int(theta), body=int(d), mass=mass, receipt=r))
        rows[f"theta{int(theta)}_body{int(d)}"] = dict(L=L, B=B, M=[x+y for x,y in zip(L,B)])

    k0, k1 = p.survival+p.common_birth, p.survival-p.care_only_survival+p.common_birth+p.bloom_only_birth
    nu = [1-p.damage, p.damage]
    for theta, d in product((False, True), repeat=2):
        k = k1 if theta and not d else k0
        assert rows[f"theta{int(theta)}_body{int(d)}"]["M"] == [k*x for x in nu]
    lambdas = [k0, (1-p.damage)*k1+p.damage*k0]
    assert lambdas[1] > lambdas[0] > 1

    # Causal controls use identical body/program/funds, varying only the named cut.
    healthy = founder(True, False)
    gate_cut = replace(healthy.body, gate=False)
    wrong_code = replace(healthy.body, code=((False,True,True),healthy.body.code[1]))
    assert raw_execute(healthy.body,False)=="bloom"
    assert raw_execute(gate_cut,False) is None
    assert raw_execute(wrong_code,False)=="care"
    boot_cut = replace(founder(True,True),body=replace(founder(True,True).body,bootstrap=False))
    assert tick(p,boot_cut,0,(2,2,False,False))["status"]=="rejected"
    assert tick(p,founder(True,True),0,(2,2,False,False),supplied=4)["status"]=="rejected"
    assert tick(p,founder(True,True),0,(0,0,False,False),request="bloom")["status"]=="rejected"

    # Complete erasure gives the same visible physical state for both origins.
    erased = Body(((False,False,False),(False,False,False)),False,True)
    recovered, _, _ = repair(erased)
    assert decode(recovered)==(False,False)
    assert decode(recovered)!=(True,False)
    # There is no θ argument by which repair could distinguish the two histories.

    # A two-parent shared purse would break row-rectangular implementation.
    caps = [tick(p,founder(False,True),0,(0,0,False,False))["request_cap"]]*2
    assert caps==[6,6] and all(c<=6 for c in caps) and sum(caps)>6

    # Best-program extinction precedes a surviving inferior program with positive mass.
    best_extinct = sum(m for w,m in atoms(p) if not tick(p,founder(True,False),0,w)["outputs"])
    low_nonzero = sum(m for w,m in atoms(p) if tick(p,founder(False,False),0,w)["outputs"])
    assert best_extinct > 0 and low_nonzero > 0

    # Rejection is a real identity transition.  In a subcritical source it can
    # dominate forced continuation; this refutes an unconditional growth claim.
    sub = Parameters(F(1,4), F(1,8), F(1,8), F(3,16), F(1,3))
    sub_stall = sum(m*len(tick(sub,founder(True,True),0,w,request="bloom")["outputs"]) for w,m in atoms(sub))
    sub_continue = sum(m*len(tick(sub,founder(True,True),0,w)["outputs"]) for w,m in atoms(sub))
    assert sub_stall == 1 and sub_continue == F(3,8) and sub_stall > sub_continue
    assert all(x > 0 for r in rows.values() for x in r["M"])
    stop = tick(p,founder(True,True),0,(2,2,False,False),request="stop")
    assert not stop["outputs"] and stop["returned_to_environment"] == 6

    # All born records are delayed until next census, with actual parent pointers.
    pop = [founder(True,True,0),founder(False,False,1)]
    pop1, trace1 = census_round(p,pop,0,[(2,2,False,True),(2,2,True,False)])
    pop2, trace2 = census_round(p,pop1,1,[(2,2,False,False)]*len(pop1))
    assert len(pop1)==4 and len(trace1)==2 and len(trace2)==4 and len(pop2)==8

    # A genuine quotient forgets only a non-readable, event-irrelevant tag.
    for theta,d in product((False,True),repeat=2):
        for w,_ in atoms(p):
            a=tick(p,founder(theta,d,tag=False),0,w)
            b=tick(p,founder(theta,d,tag=True),0,w)
            for key in ["status","request","repair_fee","actual_fee","request_cap","returned_to_environment"]:
                assert a[key]==b[key]
            assert [(x.identity,x.parent,x.age,x.wallet,visible(x.body)) for x in a["outputs"]] == [(x.identity,x.parent,x.age,x.wallet,visible(x.body)) for x in b["outputs"]]

    report = dict(schema="UEOT/CORE_REGENERATIVE_EXACT_PROTOTYPE/V1", status="PASS_SOURCE_PROBE_NOT_LEAN",
                  parameters=p, event_count=len(outcomes), primitive_atoms=36,
                  input_is_only_local_event_parameters=True, expected_matrices_derived_from_records=rows,
                  derived_growth=lambdas, damage_distribution=nu,
                  cap_by_body_action={"H_care":3,"H_bloom":4,"D_care":6,"D_bloom":7},
                  best_extinct_probability=best_extinct,
                  best_extinct_and_low_nonzero_probability=best_extinct*low_nonzero,
                  open_positive_class="0<delta<s<1;0<b;b+gamma<1;delta<gamma;0<q<1;s+b>1",
                  subcritical_rejection_counterexample={"parameters":sub,"one_step_reject_mean":sub_stall,"one_step_continue_mean":sub_continue},
                  continue_body_blocks_primitive_power=1, faithful_program_blocks="Global multi-program matrix is block diagonal; no global primitivity claim",
                  negative_checks={"gate_cut_blocks_execution":True,"wrong_active_code_changes_action":True,
                                   "bootstrap_cut_blocks_recovery":True,"underfunded_repair_rejected":True,
                                   "D_bloom_rejected_even_when_outcome_free":True,
                                   "erased_code_cannot_identify_original_program":True,
                                   "shared_purse_breaks_row_independence":True,
                                   "stop_zero_row_not_primitive":True,
                                   "subcritical_rejection_dominates_continuation":True},
                  quotient_checks=144, source_clock="Each pre-census member once; newborn acts only next tick",
                  no_free_newborn_funding="Every output wallet is a literal debit of the parent's 1+5 balance",
                  closed_wallet_limit="Per-tick inflow 5 per old member is an explicit environment input; supply up to T is <=5*n*(2**T-1)",
                  sample_two_round_execution=[trace1,trace2], all_one_step_records=outcomes,
                  scope="S0 exact source probe; no claim of Lean closure, whole-core completion, or empirical support")
    out=Path(__file__).with_suffix('.json');out.write_text(json.dumps(serializable(report),ensure_ascii=False,indent=2)+'\n')
    print(json.dumps(serializable({k:v for k,v in report.items() if k not in ['all_one_step_records','sample_two_round_execution']}),ensure_ascii=False,indent=2))


if __name__ == '__main__': main()
