#!/usr/bin/env python3
"""Validate candidate UEOT trust-policy structure using Python stdlib only.

Authorization never comes from candidate HEAD. Consumers load the policy from the
PR base SHA / integrated main. This validator checks shape and fail-closed defaults.
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

POLICY = Path('.ai/TRUST_POLICY.json')


def _strings(value: object) -> bool:
    return isinstance(value, list) and bool(value) and all(isinstance(x, str) and x for x in value)


def main() -> int:
    try:
        p = json.loads(POLICY.read_text(encoding='utf-8'))
    except Exception as exc:  # noqa: BLE001
        print(f'invalid trust policy JSON: {exc}', file=sys.stderr)
        return 1

    errors: list[str] = []
    if p.get('schema_version') != 2:
        errors.append('schema_version must be 2')
    if p.get('repository') != 'MurphyHoops/UEOT':
        errors.append('repository must be MurphyHoops/UEOT')
    if p.get('policy_source') != 'pr-base':
        errors.append('policy_source must be pr-base')

    bootstrap = p.get('bootstrap')
    if not isinstance(bootstrap, dict):
        errors.append('bootstrap must be an object')
    else:
        if bootstrap.get('when_base_policy_missing') != 'owner-authorization':
            errors.append('bootstrap.when_base_policy_missing must be owner-authorization')
        if bootstrap.get('owner_authorization_marker') != '[UEOT-OWNER-AUTHORIZATION]':
            errors.append('bootstrap.owner_authorization_marker must be [UEOT-OWNER-AUTHORIZATION]')

    authority = p.get('authority')
    expected_authority = {
        'merge_mode': 'ai-autonomous',
        'normal_integration_path': 'pull-request-reviewed',
        'builder_may_self_approve': False,
        'direct_main_write': 'allowed-for-recovery-or-explicitly-justified-maintenance',
    }
    if authority != expected_authority:
        errors.append('authority must encode AI-autonomous merge, reviewed-PR normal integration, no Builder self-approval, and explicit direct-main exception authority')

    review = p.get('review')
    authors = review.get('trusted_review_artifact_authors') if isinstance(review, dict) else None
    if not _strings(authors):
        errors.append('review.trusted_review_artifact_authors must be a non-empty string array')
    if not isinstance(review, dict) or review.get('independent_review_required') is not True:
        errors.append('review.independent_review_required must be true')

    ci = p.get('ci')
    if not isinstance(ci, dict):
        errors.append('ci must be an object')
    else:
        if ci.get('unmatched_changed_paths') != 'elevated-review':
            errors.append('ci.unmatched_changed_paths must be elevated-review')
        elevated = ci.get('elevated_review_paths')
        if not _strings(elevated):
            errors.append('ci.elevated_review_paths must be a non-empty string array')
        elif len(elevated) != len(set(elevated)):
            errors.append('ci.elevated_review_paths must be unique')

        gates = ci.get('gates')
        if not isinstance(gates, dict) or not gates:
            errors.append('ci.gates must be a non-empty object')
            gates = {}
        for gate_id, gate in gates.items():
            if not isinstance(gate_id, str) or not gate_id:
                errors.append('gate ids must be non-empty strings')
                continue
            if not isinstance(gate, dict):
                errors.append(f'gate {gate_id} must be an object')
                continue
            workflow = gate.get('workflow_path')
            if not isinstance(workflow, str) or not workflow.startswith('.github/workflows/'):
                errors.append(f'gate {gate_id} workflow_path must be under .github/workflows/')
            if not isinstance(gate.get('job_name'), str) or not gate['job_name']:
                errors.append(f'gate {gate_id} job_name must be non-empty')
            if gate.get('allowed_conclusions') != ['success']:
                errors.append(f'gate {gate_id} allowed_conclusions must be [success]')
            if gate.get('require_workflow_unchanged_from_base') is not True:
                errors.append(f'gate {gate_id} must require workflow unchanged from base')
            inputs = gate.get('protected_inputs')
            if not isinstance(inputs, list) or any(not isinstance(x, str) or not x for x in inputs):
                errors.append(f'gate {gate_id} protected_inputs must be a string array')
            elif len(inputs) != len(set(inputs)):
                errors.append(f'gate {gate_id} protected_inputs must be unique')

        rules = ci.get('path_rules')
        if not isinstance(rules, list) or not rules:
            errors.append('ci.path_rules must be a non-empty array')
        else:
            for i, rule in enumerate(rules):
                if not isinstance(rule, dict):
                    errors.append(f'path rule {i} must be an object')
                    continue
                patterns = rule.get('patterns')
                req = rule.get('require_gates')
                if not _strings(patterns):
                    errors.append(f'path rule {i} patterns must be non-empty strings')
                if not isinstance(req, list) or not req or any(x not in gates for x in req):
                    errors.append(f'path rule {i} require_gates must reference defined gates')

    if errors:
        print('Trust policy validation FAILED:', file=sys.stderr)
        for error in errors:
            print(f'- {error}', file=sys.stderr)
        return 1
    print('Trust policy validation passed.')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
