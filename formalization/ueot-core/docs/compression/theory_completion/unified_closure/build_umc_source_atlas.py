#!/usr/bin/env python3
"""Cross-check all 106 frozen P-IDs against actual Lean declaration locations.

Three levels are kept distinct:
  DIRECT_LEXICAL: exact pid-shaped theorem name seen in Lean source;
  CANONICAL_DOC_MATCH: a literal theorem named in historical governance/docs,
    lexically confirmed inside the Lean repository;
  NEEDS_SOURCE_SEMANTIC_MAPPING: never assert a successful mapping from guess.

This is a source declaration index, not a Lean elaborator / proof dependency
graph and not a re-audit of frozen source semantics. The frozen main count
remains governed elsewhere.
"""
import csv, json, re
from pathlib import Path
from collections import defaultdict

ROOT = Path(__file__).resolve().parents[6]
DOCS = ROOT / 'formalization/ueot-core/docs'
LEAN = ROOT / 'formalization/ueot-core/UEOT'
OUT = Path(__file__).parent / 'UMC_00_SOURCE_ATLAS_V1.json'
CANONICAL = DOCS / 'PID_STATUS.yaml'
HIERARCHY = DOCS / 'compression/hierarchy/H0_HIERARCHY_INVENTORY.md'
INDEX = DOCS / 'CORE_COMPRESSION_THEOREM_INDEX.csv'

def build_atlas():
    decls = defaultdict(list)
    for path in sorted(LEAN.rglob('*.lean')):
        rel = str(path.relative_to(ROOT))
        for ln, line in enumerate(path.read_text().splitlines(), 1):
            m = re.match(r"\s*(?:private\s+|protected\s+|noncomputable\s+)*"
                         r"(?:theorem|lemma)\s+([A-Za-z_][A-Za-z_0-9']*)\b", line)
            if m:
                decls[m.group(1)].append({'path': rel, 'line': ln})
    historical = CANONICAL.read_text()
    ledger = json.loads((DOCS/'compression/COMPRESSION_LEDGER.yaml').read_text())
    counted_routes = ledger['final_dispositions']
    canonical_by_pid = {}
    for m in re.finditer(r'^  (P-[A-Z]+-\d+):\n', historical, re.M):
        end = historical.find('\n  P-', m.end())
        block = historical[m.end():end if end >= 0 else len(historical)]
        h = re.search(r'^    canonical_theorem:\s*([^\n]+)', block, re.M)
        if h:
            canonical_by_pid[m.group(1)] = h.group(1).strip().strip('"')
    h0 = HIERARCHY.read_text()
    snippets = {}
    pat = re.compile(r'^- (P-[A-Z]+-\d+)\s+[—–-]\s+(.+?)(?=^\s*- P-[A-Z]+-\d+\s+[—–-]|^### |^## |\Z)',re.M|re.S)
    for m in pat.finditer(h0):
        snippets.setdefault(m.group(1), []).append(m.group(2))
    ids = list(csv.DictReader(INDEX.open()))
    # Direct source inspection for legacy P-IDs whose official theorem does
    # NOT use the bare p_abc_01 name. Each entry is a verified literal Lean
    # declaration at the named module, but semantic matching remains NOT
    # independently rechecked merely by this automated source atlas.
    extra_symbols = {
      'P-MET-01': ('TVKernel.lean','tvDist_comp_le'),
      'P-MET-02': ('TVSpan.lean','abs_integral_sub_le_span'),
      'P-PROC-01': ('ConcreteHistoryMarkovization.lean','p_proc_01_history_markovization'),
      'P-INFO-01': ('InformationMemoryBound.lean','p_info_01_discrete_entropy'),
      'P-INFO-02': ('InformationPInfo02.lean','p_info_02_ennreal'),
      'P-INFO-03': ('InformationPredictiveRateZero.lean','predictiveObjectRateZero_eq_sourceEntropy'),
      'P-INFO-05': ('InformationEntropy.lean','p_info_05_uniform_entropy'),
      'P-REC-01': ('RecoveryProbability.lean','p_rec_01_mean_bound'),
      'P-STAT-01': ('FiniteAlphabetPStat01.lean','p_stat_01_tail'),
      'P-CTL-03': ('DiffusionHJBVerification.lean','p_ctl_03'),
    }
    res=[]
    for row in ids:
        pid=row['pid']
        natural = pid.lower().replace('-','_')
        direct=decls[natural]
        hints=[]
        for evidence in counted_routes[pid].get('audit_evidence', []):
            if evidence.startswith('theorem:'):
                hints.append(('CANONICAL_COUNTED_LEDGER',evidence.removeprefix('theorem:')))
        if pid in canonical_by_pid:
            hints.append(('PID_STATUS_HISTORICAL',canonical_by_pid[pid]))
        for text in snippets.get(pid,[]):
            for token in re.findall(r'`([^\x60]+)`',text):
                if token.startswith('UEOT.'):
                    hints.append(('H0_HIERARCHY_SOURCE',token.strip('.,;')))
        confirmed=[]
        for kind,qual in hints:
            symbol=qual.split('.')[-1]
            hits=decls.get(symbol,[])
            for hit in hits:
                # Only disambiguate location by known qualified package-prefix.
                # Namespaced constant lookup still needs Lean elaboration.
                module=hit['path'].replace('formalization/ueot-core/','').removesuffix('.lean').replace('/','.')
                if qual.rsplit('.',1)[0] == module or len(hits)==1:
                    entry={'symbol':qual,'reference_kind':kind,**hit}
                    if entry not in confirmed:confirmed.append(entry)
        if len(direct)==1 and not confirmed:
            confirmed=[{'symbol':natural,'reference_kind':'DIRECT_PID_LEXICAL',**direct[0]}]
        if pid in extra_symbols and not confirmed:
            filename, symbol = extra_symbols[pid]
            hits = [h for h in decls[symbol] if h['path'].endswith('/'+filename)]
            assert hits, (pid, filename, symbol)
            confirmed=[{'symbol':symbol,
                        'reference_kind':'ADDITIONAL_MANUAL_LEXICAL_LOCATION',**h}
                       for h in hits]
        # Explicit ambiguity: never quietly choose first among duplicate names.
        state=('DOC_REFERENCED_LOCATION_FOUND' if confirmed and
                 any(x['reference_kind'] in {'CANONICAL_COUNTED_LEDGER',
                   'PID_STATUS_HISTORICAL', 'H0_HIERARCHY_SOURCE'}
                   for x in confirmed)
              else 'MANUAL_LEXICAL_LOCATION_FOUND' if confirmed and
                 any(x['reference_kind']=='ADDITIONAL_MANUAL_LEXICAL_LOCATION'
                     for x in confirmed)
              else 'EXACT_PID_LEXICAL_LOCATION_FOUND' if len(direct)==1
              else 'NEEDS_SOURCE_SEMANTIC_MAPPING')
        res.append({'pid':pid,'source_chapter':row['source_chapter'],
                    'source_line':int(row['source_line']),
                    'final_disposition': counted_routes[pid]['status'],
                    'live_ledger_theorem_evidence':
                      [e for e in counted_routes[pid].get('audit_evidence',[])
                       if e.startswith('theorem:')],
                    'mapping_status':state,
                    'historical_canonical':canonical_by_pid.get(pid),
                    'direct_name_locations':direct,
                    'document_referenced_locations':confirmed,
                    'semantic_match_reverified_in_this_pass':False})
    from collections import Counter
    counts=Counter(x['mapping_status'] for x in res)
    return {'schema':1,'status':'SOURCE_DECLARATION_ATLAS_NOT_SEMANTIC_PROOF',
            'fixed_pid_count':106,'records':res,'summary':dict(counts),
            'source_semantics_warning': 'A lexical theorem name or quoted documentation reference is not a renewed formal semantic certification. Duplicate/unmapped declarations remain explicit.'}

if __name__=='__main__':
    result=build_atlas()
    OUT.write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
    print('UMC00_ATLAS',json.dumps(result['summary'],sort_keys=True),'records',len(result['records']))
    print('UNMAPPED',[x['pid'] for x in result['records'] if x['mapping_status']=='NEEDS_SOURCE_SEMANTIC_MAPPING'])
