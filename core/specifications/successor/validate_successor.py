#!/usr/bin/env python3
"""Static integrity checks for the additive Core successor specification.

This script does not invoke Lean, lake, a compiler, a book builder, or a remote
service.  Existing proof receipts are reused only at matching source bytes.
Run from any directory; --root may name another checkout of the same cut.
"""

from __future__ import annotations

import argparse
from collections import Counter, deque
from datetime import datetime, timezone
import hashlib
import html
import json
from pathlib import Path
import re
import subprocess
import sys
import unicodedata
from urllib.parse import unquote, urlsplit


BASE_COMMIT = "16a89154183c22030d4526413167d095d94e6890"
BASE_TREE = "839321b98ddcf368d0673484f7239733b53a5180"
FROZEN_PATH = "mathematics/source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md"
FROZEN_SHA = "ed00dd102157cdafe3a79c45506e86dc574d6cba65feb2df8686e63ce2726303"
FROZEN_BYTES = 183440
IDS_SHA = "854822354c9e54b376bbbccf5ac61a9501efcd99f323e996da9420d268c2d0d2"
PACKAGE = "core/specifications/successor"
LEAN_ROOT = "formalization/ueot-core"
DOCS = LEAN_ROOT + "/docs/compression/theory_completion/unified_closure/"
FIELDS = ["id", "name", "definition", "domain", "assumptions", "quantifiers",
          "conclusion", "proof", "status", "failure", "consumer", "nonclaims"]
PID_ANCHOR = re.compile(r'<a\s+id=["\'](p-[a-z]+-\d+)["\']\s*>\s*</a>')
CARD_ANCHOR = re.compile(r'<a\s+id=["\'](csx-\d+)["\']\s*>\s*</a>')
FIELD_MARKER = re.compile(r'<!--\s*contract-field:\s*([a-z_]+)\s*-->')
FORMULA_MARKER = re.compile(r'<!--\s*contract-formula:\s*(CSX-\d+)\s*-->')
FULL_NAME = re.compile(r'^UEOT\.[A-Za-z0-9_\u0080-\uffff.\']+$')


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def strip_lean_comments(source: str) -> str:
    """Keep line numbers, handle nested comments and literal strings."""
    out: list[str] = []
    i, depth = 0, 0
    in_string = False
    while i < len(source):
        pair = source[i:i + 2]
        c = source[i]
        if depth:
            if pair == "/-":
                depth += 1
                out.extend("  ")
                i += 2
            elif pair == "-/":
                depth -= 1
                out.extend("  ")
                i += 2
            else:
                out.append("\n" if c == "\n" else " ")
                i += 1
        elif in_string:
            # Keep string content out of the command scanner as well.
            out.append("\n" if c == "\n" else " ")
            if c == "\\" and i + 1 < len(source):
                i += 1
                out.append("\n" if source[i] == "\n" else " ")
            elif c == '"':
                in_string = False
            i += 1
        elif pair == "/-":
            depth = 1
            out.extend("  ")
            i += 2
        elif pair == "--":
            end = source.find("\n", i)
            if end < 0:
                end = len(source)
            out.extend(" " * (end - i))
            i = end
        elif c == '"':
            in_string = True
            out.append(" ")
            i += 1
        else:
            out.append(c)
            i += 1
    return "".join(out)


def without_code_fences(text: str) -> str:
    lines, fence = [], None
    for line in text.splitlines():
        marker = re.match(r'^\s{0,3}(`{3,}|~{3,})', line)
        if marker:
            token = marker.group(1)
            if fence is None:
                fence = (token[0], len(token))
            elif token[0] == fence[0] and len(token) >= fence[1]:
                fence = None
            lines.append("")
        else:
            lines.append(line if fence is None else "")
    return "\n".join(lines)


def markdown_anchors(text: str) -> set[str]:
    anchors = set(re.findall(r'<a\b[^>]*(?:id|name)=["\']([^"\']+)["\']', text))
    seen: Counter[str] = Counter()
    for line in without_code_fences(text).splitlines():
        match = re.match(r'^\s{0,3}#{1,6}\s+(.+?)(?:\s+#+\s*)?$', line)
        if not match:
            continue
        heading = re.sub(r'\[([^]]+)\]\([^)]*\)', r'\1', match.group(1))
        heading = re.sub(r'<[^>]+>', '', html.unescape(heading)).lower()
        heading = heading.replace('`', '').replace('*', '')
        heading = re.sub(r'(?<!\w)_{1,2}(.+?)_{1,2}(?!\w)', r'\1', heading)
        slug = ''.join(c for c in heading if not (
            unicodedata.category(c)[0] in {'P', 'S'} and c not in {'-', '_'}))
        slug = re.sub(r'\s', '-', slug.strip())
        count = seen[slug]
        anchors.add(slug if count == 0 else f'{slug}-{count}')
        seen[slug] += 1
    return anchors


class Audit:
    def __init__(self, root: Path):
        self.root = root.resolve()
        self.checks: list[dict] = []
        self.hashes: dict[str, str] = {}
        self.modules: dict[str, list[str]] = {}
        self.declarations: dict[tuple[str, str], dict] = {}
        self.route_cache: dict[tuple[str, str], list[str] | None] = {}
        self.frozen_ids: list[str] = []
        self.mapping: dict = {}
        self.claim_index: dict | list = {}
        self.claims: list[dict] = []

    def path(self, relative: str) -> Path:
        p = (self.root / relative).resolve()
        if not p.is_relative_to(self.root):
            raise ValueError(f'Path escapes repository: {relative}')
        return p

    def sha(self, relative: str) -> str:
        if relative not in self.hashes:
            self.hashes[relative] = digest(self.path(relative).read_bytes())
        return self.hashes[relative]

    def read_json(self, relative: str):
        self.sha(relative)
        return json.loads(self.path(relative).read_text(encoding='utf-8'))

    def git(self, *args: str) -> str:
        result = subprocess.run(['git', '-C', str(self.root), *args],
                                capture_output=True, text=True, check=False)
        if result.returncode:
            raise ValueError(f'git {args[0]} failed: {result.stderr.strip()}')
        return result.stdout

    def record(self, name: str, errors: list, **details):
        self.checks.append({'name': name, 'passed': not errors,
                            'errors': errors, **details})

    def run_group(self, name: str, method):
        try:
            method()
        except (OSError, ValueError, KeyError, TypeError, AttributeError, IndexError, AssertionError) as exc:
            self.record(name, [{'error': type(exc).__name__, 'message': str(exc)}])

    def baseline_and_protected_files(self):
        tree = self.git('rev-parse', BASE_COMMIT + '^{tree}').strip()
        errors = [] if tree == BASE_TREE else [{'baseline_tree': tree, 'expected': BASE_TREE}]
        tracked = set(self.git('ls-tree', '-r', '--name-only', '-z', BASE_COMMIT).split('\0')) - {''}
        changed = set(self.git('diff', '--name-only', '--no-renames', '-z', BASE_COMMIT, '--').split('\0')) - {''}
        untracked = set(self.git('ls-files', '--others', '--exclude-standard', '-z').split('\0')) - {''}

        def protected(path: str) -> bool:
            return (path.endswith('.lean')
                    or path.startswith(('mathematics/', 'philosophy/', 'physics/'))
                    or path in {'core/specifications/manifest.yaml',
                                LEAN_ROOT + '/lean-toolchain',
                                LEAN_ROOT + '/lake-manifest.json'})

        violations = sorted(p for p in changed | untracked if protected(p))
        errors.extend({'protected_path_changed': p} for p in violations)
        changed_paths = sorted(changed | untracked)
        unsupported_paths = [p for p in changed_paths
                             if p != 'core/specifications/README.md'
                             and not p.startswith(PACKAGE + '/')]
        errors.extend({'outside_authorized_document_scope': p} for p in unsupported_paths)
        self.record('baseline_and_protected_files', errors, baseline_commit=BASE_COMMIT,
                    baseline_tree=tree, protected_baseline_files=sum(protected(p) for p in tracked),
                    changed_protected_files=violations,
                    changed_paths=changed_paths, unsupported_paths=unsupported_paths,
                    meaning='Worktree bytes/modes relative to the fixed base, including untracked additions; no Lean execution.')

    def frozen_contract(self):
        data = self.path(FROZEN_PATH).read_bytes()
        source = data.decode('utf-8')
        ids = [p.upper() for p in PID_ANCHOR.findall(source)]
        self.frozen_ids = ids
        actual = {'sha256': self.sha(FROZEN_PATH), 'bytes': len(data),
                  'anchor_count': len(ids), 'unique_anchor_count': len(set(ids)),
                  'ordered_ids_sha256': digest(('\n'.join(ids) + '\n').encode())}
        expected = {'sha256': FROZEN_SHA, 'bytes': FROZEN_BYTES,
                    'anchor_count': 106, 'unique_anchor_count': 106, 'ordered_ids_sha256': IDS_SHA}
        errors = [{k: actual[k], 'expected': v} for k, v in expected.items() if actual[k] != v]
        self.record('frozen_contract', errors, path=FROZEN_PATH, **actual)

    def scan_public_lean_sources(self):
        base = self.path(LEAN_ROOT)
        files = sorted(set(base.glob('*.lean')) | set((base / 'UEOT').rglob('*.lean')))
        declaration_pattern = re.compile(
            r'(?:@\[[^\]]*\]\s*)*'
            r'(?P<mods>(?:(?:noncomputable|nonrec|protected|private|unsafe|partial)\s+)*)'
            r'(?:theorem|lemma|def|abbrev|structure|class|inductive|axiom|opaque|constant)\s+'
            r'(?P<name>[^\s(:{]+)')
        for file in files:
            module = '.'.join(file.relative_to(base).with_suffix('').parts)
            source = strip_lean_comments(file.read_text(encoding='utf-8'))
            imports = []
            scopes: list[tuple[str, str | None]] = []
            names: list[str] = []
            for line_number, line in enumerate(source.splitlines(), 1):
                text = line.strip()
                im = re.match(r'^(?:public\s+)?import\s+(.+)$', text)
                if im:
                    imports.extend(im.group(1).split())
                namespace = re.match(r'^namespace\s+(\S+)$', text)
                section = re.match(r'^(?:noncomputable\s+)?section(?:\s+(\S+))?$', text)
                end = re.match(r'^end(?:\s+(\S+))?$', text)
                if namespace:
                    part = namespace.group(1)
                    scopes.append(('namespace', part))
                    names.append(part)
                elif section:
                    scopes.append(('section', section.group(1)))
                elif end and scopes:
                    kind, _ = scopes.pop()
                    if kind == 'namespace':
                        names.pop()
                declaration = declaration_pattern.match(text)
                if declaration:
                    name = declaration.group('name')
                    full_name = name[7:] if name.startswith('_root_.') else '.'.join(names + [name])
                    self.declarations[(module, full_name)] = {
                        'line': line_number,
                        'private': 'private' in declaration.group('mods').split(),
                    }
            self.modules[module] = imports
        self.record('public_source_inventory', [], source_modules=len(self.modules),
                    textual_named_declarations=len(self.declarations),
                    limitation='Textual declaration/import inventory; does not elaborate types or inspect compiled proof terms.')

    def route(self, start: str, target: str):
        key = (start, target)
        if key in self.route_cache:
            return self.route_cache[key]
        queue, seen = deque([(start, [start])]), set()
        while queue:
            module, route = queue.popleft()
            if module == target:
                self.route_cache[key] = route
                return route
            if module in seen:
                continue
            seen.add(module)
            queue.extend((m, route + [m]) for m in self.modules.get(module, []) if m in self.modules)
        self.route_cache[key] = None
        return None

    def resolve_endpoint(self, name: str, source_path: str | None = None) -> dict:
        """Resolve a real declaration, requiring a unique public source match.

        A fully qualified name is matched exactly. A short/suffix name is
        looked up in the scanned declarations; its namespace is never invented.
        Ambiguity, absence and private-only matches raise ValueError.
        """
        candidates = []
        for (module, declaration), record in self.declarations.items():
            matched = declaration == name if name.startswith('UEOT.') else (
                declaration == name or declaration.endswith('.' + name))
            path = LEAN_ROOT + '/' + module.replace('.', '/') + '.lean'
            if (matched and not record['private'] and (source_path is None or path == source_path)
                    and self.route('UEOT', module) is not None):
                candidates.append((module, declaration, path, record))
        if len(candidates) != 1:
            raise ValueError(f'Expected one public defining declaration for {name!r}; '
                             f'found {[(m, d) for m, d, _, _ in candidates]}')
        module, declaration, path, record = candidates[0]
        return {'declaration': declaration, 'source_path': path, 'module': module,
                'source_sha256': self.sha(path), 'public_import': 'UEOT',
                'import_route': self.route('UEOT', module), 'declaration_line': record['line']}

    def check_endpoint(self, endpoint: dict) -> list[dict]:
        errors = []
        try:
            for field in ['declaration', 'source_path', 'public_import', 'source_sha256', 'import_route']:
                if not endpoint.get(field):
                    errors.append({'missing_endpoint_field': field, 'endpoint': endpoint.get('declaration')})
            if errors:
                return errors
            path, name = endpoint['source_path'], endpoint['declaration']
            relative = Path(path).relative_to(LEAN_ROOT)
            if relative.suffix != '.lean':
                raise ValueError(f'Endpoint source is not Lean: {path}')
            module = '.'.join(relative.with_suffix('').parts)
            if endpoint.get('module', module) != module:
                errors.append({'module_path_mismatch': name, 'expected_module': module})
            declaration = self.declarations.get((module, name))
            if declaration is None:
                errors.append({'declaration_not_found_in_defining_file': name, 'path': path})
            elif declaration['private']:
                errors.append({'private_declaration_claimed_public': name, 'path': path})
            elif endpoint.get('declaration_line', declaration['line']) != declaration['line']:
                errors.append({'declaration_line_mismatch': name, 'actual': declaration['line']})
            if self.sha(path) != endpoint['source_sha256']:
                errors.append({'source_hash_mismatch': path, 'endpoint': name})
            public_import = endpoint['public_import']
            if public_import != 'UEOT':
                errors.append({'unexpected_public_import': public_import, 'endpoint': name})
            route = endpoint['import_route']
            if not isinstance(route, list) or not route or route[0] != public_import or route[-1] != module:
                errors.append({'invalid_import_route_endpoints': name, 'route': route})
            elif any(b not in self.modules.get(a, []) for a, b in zip(route, route[1:])):
                errors.append({'import_route_contains_nonexistent_edge': name, 'route': route})
            if self.route(public_import, module) is None:
                errors.append({'not_publicly_reachable': name, 'module': module})
        except (OSError, ValueError, KeyError, TypeError) as exc:
            errors.append({'invalid_endpoint': endpoint.get('declaration'), 'message': str(exc)})
        return errors

    def interface_map(self):
        self.mapping = self.read_json(PACKAGE + '/V3_PROPOSITION_INTERFACE_MAP.json')
        mapping, errors = self.mapping, []
        entries = mapping['entries']
        ids = [r['pid'] for r in entries]
        if ids != self.frozen_ids:
            errors.append({'map_pid_order_or_set_mismatch': ids})
        if mapping.get('baseline_commit') != BASE_COMMIT or mapping.get('baseline_tree') != BASE_TREE:
            errors.append({'map_baseline_mismatch': True})
        frozen = mapping['frozen_source']
        for key, expected in [('path', FROZEN_PATH), ('sha256', FROZEN_SHA), ('bytes', FROZEN_BYTES),
                              ('proposition_count', 106), ('ordered_ids_sha256', IDS_SHA)]:
            if frozen.get(key) != expected:
                errors.append({'map_frozen_metadata_mismatch': key, 'actual': frozen.get(key), 'expected': expected})
        declarations = {d['declaration'] for r in entries for d in r['declarations']}
        if len(entries) != 106 or len(declarations) != 163:
            errors.append({'map_counts': {'pids': len(entries), 'unique_declarations': len(declarations)}})
        catalog = mapping['successor_extension_catalog']
        for row in entries:
            if row['source'].get('anchor') != row['pid'].lower() or row['source'].get('path') != FROZEN_PATH:
                errors.append({'frozen_anchor_binding_mismatch': row['pid']})
            for endpoint in row['declarations']:
                errors.extend(self.check_endpoint(endpoint))
            relations = row.get('successor_extensions', [])
            for relation in relations:
                group = catalog.get(relation.get('catalog_id'))
                if not group or row['pid'] not in group['related_pids']:
                    errors.append({'bad_successor_relation': row['pid'], 'relation': relation})
            expected_status = 'linked_with_explicit_scope' if relations else 'no_direct_extension_registered'
            if row.get('successor_relation_status') != expected_status:
                errors.append({'bad_empty_relation_semantics': row['pid']})
            for consumer in row.get('consumers', []):
                target = self.path(consumer['path'])
                if not target.is_file():
                    errors.append({'missing_consumer': consumer})
                elif consumer.get('anchor') and consumer['anchor'] not in markdown_anchors(target.read_text(encoding='utf-8')):
                    errors.append({'missing_consumer_anchor': consumer})
        for key, group in catalog.items():
            if not group.get('declarations') or not group.get('scope') or not group.get('relation_type'):
                errors.append({'incomplete_catalog_contract': key})
            for pid in group['related_pids']:
                if pid not in self.frozen_ids:
                    errors.append({'unknown_related_pid': key, 'pid': pid})
                elif not any(r.get('catalog_id') == key for row in entries if row['pid'] == pid
                             for r in row.get('successor_extensions', [])):
                    errors.append({'one_way_catalog_relation': key, 'pid': pid})
            for endpoint in group['declarations']:
                errors.extend(self.check_endpoint(endpoint))
        for provenance in mapping['source_mapping_provenance']:
            if self.sha(provenance['path']) != provenance['sha256']:
                errors.append({'mapping_provenance_hash_mismatch': provenance['path']})
        self.record('v3_interface_map', errors, pids=len(entries), unique_legacy_declarations=len(declarations),
                    successor_groups=len(catalog), successor_endpoints=sum(len(g['declarations']) for g in catalog.values()),
                    pids_without_direct_extension=sum(not r.get('successor_extensions') for r in entries))

    def reused_receipts(self):
        expected = []
        path = DOCS + 'core_growth_classification_v1/LEAN_VALIDATION.json'
        for row in self.read_json(path)['checked_modules']:
            expected.append((path, row['source'], row['source_sha256'], 'reused_successful_lean_receipt'))
        path = DOCS + 'core_growth_classification_v1/SOURCE_BINDING.json'
        for source, sha in self.read_json(path)['old_execution_sources_byte_identical'].items():
            expected.append((path, source, sha, 'reused_source_identity_receipt'))
        path = DOCS + 'general_perron_compact_spectral_source_v1/SOURCE_VALIDATION.json'
        for row in self.read_json(path)['proof_bytes_verified']:
            expected.append((path, row['path'], row['sha256'], 'reused_public_source_validation'))
        bindings = self.mapping['reused_source_receipt_bindings']
        actual = [(b['receipt_path'], b['source_path'], b['source_sha256'], b['evidence_kind']) for b in bindings]
        errors = []
        if Counter(actual) != Counter(expected) or len(expected) != 26:
            errors.append({'receipt_binding_inventory_mismatch': True, 'expected_count': len(expected), 'actual_count': len(actual)})
        for binding in bindings:
            if self.sha(binding['source_path']) != binding['source_sha256']:
                errors.append({'receipt_source_hash_mismatch': binding['source_path']})
            if self.sha(binding['receipt_path']) != binding['receipt_sha256']:
                errors.append({'receipt_document_hash_mismatch': binding['receipt_path']})
            if binding.get('compiled_in_this_document_upgrade') is not False:
                errors.append({'false_new_compilation_claim': binding['source_path']})
            if binding.get('current_source_hash_matches') is not True:
                errors.append({'source_match_flag_missing': binding['source_path']})
        self.record('reused_source_receipts', errors, total=len(bindings),
                    kinds=dict(Counter(b['evidence_kind'] for b in bindings)),
                    lean_rebuild_performed=False)

    def claim_index_integrity(self):
        self.claim_index = self.read_json(PACKAGE + '/CLAIM_INDEX.json')
        if isinstance(self.claim_index, list):
            self.claims = self.claim_index
        else:
            self.claims = self.claim_index.get('entries', self.claim_index.get('claims', []))
        errors = []
        if not self.claims:
            errors.append({'empty_claim_index': True})
        ids = [c['id'] for c in self.claims]
        if len(ids) != len(set(ids)) or any(not re.fullmatch(r'CSX-\d+', i) for i in ids):
            errors.append({'invalid_or_duplicate_claim_ids': ids})
        metadata = self.claim_index if isinstance(self.claim_index, dict) else {}
        normative_documents = metadata.get('normative_documents', {})
        expected_documents = {
            'zh': PACKAGE + '/UEOT_Core_Successor_Specification.md',
            'en': PACKAGE + '/UEOT_Core_Successor_Specification.en.md',
        }
        if set(normative_documents) != set(expected_documents):
            errors.append({'normative_document_languages_mismatch': sorted(normative_documents),
                           'expected': sorted(expected_documents)})
        for language, expected_path in expected_documents.items():
            document = normative_documents.get(language, {})
            if document.get('path') != expected_path:
                errors.append({'normative_document_path_mismatch': language,
                               'actual': document.get('path'), 'expected': expected_path})
            if document.get('sha256') != self.sha(expected_path):
                errors.append({'normative_document_hash_mismatch': language, 'path': expected_path})
        catalog_to_contracts = metadata.get('catalog_to_contracts', {})
        expected_catalog = set(self.mapping.get('successor_extension_catalog', {}))
        if set(catalog_to_contracts) != expected_catalog:
            errors.append({'catalog_contract_inventory_mismatch': True,
                           'missing_catalogs': sorted(expected_catalog - set(catalog_to_contracts)),
                           'unexpected_catalogs': sorted(set(catalog_to_contracts) - expected_catalog)})
        for catalog, contracts in catalog_to_contracts.items():
            if not isinstance(contracts, list) or not contracts:
                errors.append({'catalog_contract_list_missing_or_invalid': catalog})
            elif any(not isinstance(cid, str) or cid not in ids for cid in contracts):
                errors.append({'catalog_contract_ids_invalid': catalog, 'actual': contracts})
            elif len(contracts) != len(set(contracts)):
                errors.append({'catalog_contract_ids_duplicated': catalog, 'actual': contracts})
        for claim in self.claims:
            if claim.get('contract_fields') != FIELDS:
                errors.append({'contract_fields_mismatch': claim['id'], 'actual': claim.get('contract_fields')})
            if not claim.get('title') or not claim.get('proof_levels'):
                errors.append({'missing_claim_title_or_proof_levels': claim['id']})
            if set(claim.get('legacy_pids', [])) - set(self.frozen_ids):
                errors.append({'unknown_claim_legacy_pids': claim['id']})
            for source in claim.get('sources', []):
                if self.sha(source['path']) != source['sha256']:
                    errors.append({'claim_source_hash_mismatch': claim['id'], 'path': source['path']})
                for endpoint in source.get('declarations', []):
                    errors.extend(self.check_endpoint(endpoint))
                    if endpoint['source_path'] != source['path']:
                        errors.append({'claim_source_endpoint_binding_mismatch': claim['id'], 'endpoint': endpoint['declaration']})
            for evidence in claim.get('evidence', []):
                if self.sha(evidence['path']) != evidence['sha256']:
                    errors.append({'claim_evidence_hash_mismatch': claim['id'], 'path': evidence['path']})
        self.record('claim_index_integrity', errors, claims=len(self.claims), fields_per_claim=len(FIELDS),
                    normative_documents=normative_documents,
                    catalog_to_contracts_count=len(catalog_to_contracts),
                    endpoint_references=sum(len(s.get('declarations', [])) for c in self.claims for s in c.get('sources', [])))

    def bilingual_contracts(self):
        errors, documents, cards = [], {}, {}
        filenames = {'zh': 'UEOT_Core_Successor_Specification.md',
                     'en': 'UEOT_Core_Successor_Specification.en.md'}
        expected_ids = [c['id'] for c in self.claims]
        for language, filename in filenames.items():
            path = PACKAGE + '/' + filename
            self.sha(path)
            documents[language] = self.path(path).read_text(encoding='utf-8')
            matches = list(CARD_ANCHOR.finditer(documents[language]))
            ids = [m.group(1).upper() for m in matches]
            if ids != expected_ids:
                errors.append({'language': language, 'card_ids_order_or_set_mismatch': ids, 'expected': expected_ids})
            cards[language] = {}
            for i, match in enumerate(matches):
                end = matches[i + 1].start() if i + 1 < len(matches) else len(documents[language])
                cards[language][match.group(1).upper()] = documents[language][match.end():end]
        for claim in self.claims:
            cid = claim['id']
            expected_names = {d['declaration'] for source in claim.get('sources', []) for d in source.get('declarations', [])}
            observed = {}
            for language in filenames:
                card = cards[language].get(cid)
                if card is None:
                    continue
                markers = FIELD_MARKER.findall(card)
                if markers != FIELDS:
                    errors.append({'language': language, 'claim': cid, 'field_markers_mismatch': markers})
                formula_matches = list(FORMULA_MARKER.finditer(card))
                expected_formula = claim.get('formula')
                formula = None
                if expected_formula is not None and expected_formula != '':
                    if len(formula_matches) != 1 or formula_matches[0].group(1) != cid:
                        errors.append({'language': language, 'claim': cid, 'formula_marker_mismatch': [m.group(1) for m in formula_matches]})
                    else:
                        after = card[formula_matches[0].end():]
                        match = re.match(r'\s*\n\s*\$\$(.*?)\$\$', after, re.S)
                        if match is None:
                            errors.append({'language': language, 'claim': cid, 'missing_formula_after_marker': True})
                        else:
                            formula = match.group(1).strip()
                            if formula != expected_formula.strip():
                                errors.append({'language': language, 'claim': cid, 'formula_differs_from_index': formula})
                elif formula_matches:
                    errors.append({'language': language, 'claim': cid, 'unexpected_formula_marker': True})
                names = []
                for token in re.findall(r'`([^`\n]+)`', without_code_fences(card)):
                    if FULL_NAME.fullmatch(token) and token not in self.modules and token not in names:
                        names.append(token)
                if set(names) != expected_names:
                    errors.append({'language': language, 'claim': cid,
                                   'missing_code_endpoints': sorted(expected_names - set(names)),
                                   'unexpected_code_endpoints': sorted(set(names) - expected_names)})
                observed[language] = {'formula': formula, 'endpoints': names, 'fields': markers}
            if observed.get('zh') != observed.get('en'):
                errors.append({'claim': cid, 'bilingual_structural_mismatch': observed})
        self.record('bilingual_contract_sync', errors, expected_cards=len(expected_ids),
                    languages=list(filenames), exact_fields=FIELDS,
                    meaning='IDs, marker order, raw mathematical formula strings and full declaration code lists; natural-language equivalence requires human review.')

    def new_markdown_links(self):
        changed = set(self.git('diff', '--name-only', '--no-renames', '-z', BASE_COMMIT, '--').split('\0')) - {''}
        untracked = set(self.git('ls-files', '--others', '--exclude-standard', '-z').split('\0')) - {''}
        files = sorted(p for p in changed | untracked if p.endswith('.md') and self.path(p).is_file())
        errors, link_count = [], 0
        anchor_cache: dict[str, set[str]] = {}

        def check_target(origin: str, target: str):
            nonlocal link_count
            target = target.strip()
            if target.startswith('<') and target.endswith('>'):
                target = target[1:-1]
            else:
                target = re.split(r'\s+["\']', target, maxsplit=1)[0]
            parsed = urlsplit(target)
            if parsed.scheme or parsed.netloc or target.startswith('//'):
                return
            link_count += 1
            target_path = unquote(parsed.path)
            resolved = (self.path(origin).parent / target_path).resolve() if target_path else self.path(origin)
            if not resolved.is_relative_to(self.root):
                errors.append({'file': origin, 'link_escapes_repository': target})
                return
            if not resolved.exists():
                errors.append({'file': origin, 'missing_local_link': target})
                return
            if parsed.fragment and resolved.is_file() and resolved.suffix.lower() == '.md':
                key = resolved.relative_to(self.root).as_posix()
                if key not in anchor_cache:
                    anchor_cache[key] = markdown_anchors(resolved.read_text(encoding='utf-8'))
                anchor = unquote(parsed.fragment)
                if anchor not in anchor_cache[key]:
                    errors.append({'file': origin, 'missing_local_anchor': target})

        for relative in files:
            body = without_code_fences(self.path(relative).read_text(encoding='utf-8'))
            body = re.sub(r'(`+)([^\n]*?)\1', lambda m: ' ' * len(m.group(0)), body)
            for match in re.finditer(r'!?\[[^\]\n]*\]\((<[^>\n]+>|[^)\n]+)\)', body):
                check_target(relative, match.group(1))
            definitions = {}
            for match in re.finditer(r'^\s{0,3}\[([^]\n]+)\]:\s*(.+)$', body, re.M):
                definitions[match.group(1).strip().casefold()] = match.group(2)
                check_target(relative, match.group(2))
            # CommonMark renders an unresolved [S1][S2] sequence as literal
            # text, not as a link.  Defined reference targets were checked
            # above; do not misclassify adjacent scholarly source labels.
        self.record('new_markdown_local_links', errors, changed_markdown_files=len(files),
                    audited_markdown_paths=files, checked_local_links=link_count,
                    meaning='All changed and untracked Markdown: relative file targets and Markdown anchors; remote URLs are not fetched.')

    def run(self):
        for name, method in [
            ('baseline_and_protected_files', self.baseline_and_protected_files),
            ('frozen_contract', self.frozen_contract),
            ('public_source_inventory', self.scan_public_lean_sources),
            ('v3_interface_map', self.interface_map),
            ('reused_source_receipts', self.reused_receipts),
            ('claim_index_integrity', self.claim_index_integrity),
            ('bilingual_contract_sync', self.bilingual_contracts),
            ('new_markdown_local_links', self.new_markdown_links),
        ]:
            self.run_group(name, method)
        return {
            'schema_version': 1,
            'status': 'PASS' if all(c['passed'] for c in self.checks) else 'FAIL',
            'generated_at_utc': datetime.now(timezone.utc).isoformat(),
            'baseline_commit': BASE_COMMIT,
            'baseline_tree': BASE_TREE,
            'verification_kind': 'static_document_and_source_integrity',
            'lean_rebuild_performed': False,
            'proof_receipts': 'Reused at matching recorded source bytes; no new proof execution is claimed.',
            'validator_sha256': digest(Path(__file__).read_bytes()),
            'checks': self.checks,
            'input_file_sha256': dict(sorted(self.hashes.items())),
        }


def markdown_receipt(result: dict) -> str:
    lines = ['# Core successor static validation', '', f"Status: **{result['status']}**.", '',
             f"Baseline: `{BASE_COMMIT}`; tree: `{BASE_TREE}`.", '',
             f"Validator SHA-256: `{result['validator_sha256']}`.", '',
             'This receipt reports static document/source integrity. No Lean compilation, full build,',
             'book build, remote publication or empirical validation was performed by this script.',
             'Historical proof receipts are reused only at matching source bytes.', '',
             '| Check | Result | Errors |', '|---|---|---:|']
    for check in result['checks']:
        lines.append(f"| {check['name']} | {'PASS' if check['passed'] else 'FAIL'} | {len(check['errors'])} |")
    for check in result['checks']:
        if check['errors']:
            lines += ['', f"## {check['name']}", '', '```json',
                      json.dumps(check['errors'], ensure_ascii=False, indent=2), '```']
    lines += ['', 'Human semantic review remains responsible for matching mathematical hypotheses,',
              'quantifiers, source classes, trust levels and nonclaims. This static PASS is not a',
              'new kernel proof, nor a claim of empirical confirmation.', '']
    return '\n'.join(lines)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=Path(__file__).resolve().parents[3])
    parser.add_argument('--json-output', '--json', type=Path,
                        default=Path(PACKAGE + '/validation/STATIC_VALIDATION.json'))
    parser.add_argument('--markdown-output', '--markdown', type=Path,
                        default=Path(PACKAGE + '/validation/STATIC_VALIDATION.md'))
    parser.add_argument('--no-write', action='store_true', help='Print the summary without writing receipts.')
    args = parser.parse_args()
    audit = Audit(args.root)
    result = audit.run()
    if not args.no_write:
        for path, contents in [(args.json_output, json.dumps(result, ensure_ascii=False, indent=2) + '\n'),
                               (args.markdown_output, markdown_receipt(result))]:
            target = path if path.is_absolute() else audit.root / path
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_text(contents, encoding='utf-8')
    print(json.dumps({'status': result['status'], 'lean_rebuild_performed': False,
                      'checks': [{'name': c['name'], 'passed': c['passed'], 'errors': len(c['errors'])}
                                 for c in result['checks']]}, ensure_ascii=False, indent=2))
    return 0 if result['status'] == 'PASS' else 1


if __name__ == '__main__':
    sys.exit(main())
