#!/usr/bin/env python3
"""Read EVERY first-party UEOT Lean file and generate auditable import/declaration DAG.

Import edges are literal text and source tokens, NOT elaborated kernel proof
dependencies. The output intentionally never asserts semantic theorem equivalence
from words, filename matches or graph reachability.
"""
from pathlib import Path
from hashlib import sha256
from collections import Counter, defaultdict
import re, json

ROOT = Path(__file__).resolve().parents[6]
CORE = ROOT / 'formalization/ueot-core'
BASE = CORE / 'UEOT'
OUT = Path(__file__).parent / 'UMC_GLOBAL_MODULE_DAG_V4.json'

def category(path: Path):
    rel = path.relative_to(CORE).as_posix()
    if '/TheoryCompletion/UnifiedClosure/' in rel: return 'UMC_New_Bridges'
    if '/TheoryCompletion/ScientificClosure/' in rel: return 'C1_C7_SISC'
    if '/TheoryCompletion/' in rel: return 'P0_P12_TheoryCompletion'
    if '/Compression/Hierarchy/' in rel: return 'Hierarchy'
    if '/Compression/Objecthood/' in rel: return 'Objecthood'
    if '/Compression/CrossTrack/' in rel: return 'CrossTrack'
    if '/Compression/' in rel: return 'Compression_Frozen_Bridges'
    return 'Core_v3_and_Substrate'

def manifest():
    paths = sorted(BASE.rglob('*.lean'))
    paths = [CORE / 'UEOT.lean', CORE / 'UEOT/V3.lean'] + paths
    paths = sorted(set(p for p in paths if p.is_file()))
    modules={}
    source_digest=sha256()
    for p in sorted(paths, key=lambda path: path.relative_to(CORE).with_suffix('').as_posix().replace('/', '.')):
        name = p.relative_to(CORE).with_suffix('').as_posix().replace('/','.')
        data=p.read_bytes()
        source_digest.update(name.encode('utf-8'))
        source_digest.update(b'\x00')
        source_digest.update(data)
        source_digest.update(b'\x00')
        text=data.decode('utf-8')
        imports=re.findall(r'^\s*import\s+(\S+)',text,re.M)
        # Lexical declarations only; namespaces and elaborated theorem
        # dependencies are explicitly out of scope.
        defs=re.findall(r'^\s*(?:(?:private|protected|noncomputable|unsafe)\s+)*(theorem|lemma|structure|class|def|abbrev|inductive)\s+([A-Za-z_][A-Za-z_0-9\']*)',text,re.M)
        heads=re.findall(r'/-!\s*#\s+([^\n]+)',text)
        modules[name]={'source':p.relative_to(ROOT).as_posix(),
                       'bytes':p.stat().st_size,
                       'lines':len(text.splitlines()),
                       'category':category(p),
                       'title':heads[0][:160] if heads else None,
                       'imports':imports,
                       'theorem_lemma_count':sum(k in ['theorem','lemma'] for k,_ in defs),
                       'decl_count':len(defs)}
    direct={m:[e for e in entry['imports'] if e in modules] for m,entry in modules.items()}
    missing={m:[e for e in entry['imports'] if e.startswith('UEOT.') and e not in modules]
             for m,entry in modules.items() if
             any(e.startswith('UEOT.') and e not in modules for e in entry['imports'])}
    visit=set(); in_stack=set(); cycles=[]
    def dfs(n):
        if n in in_stack:cycles.append(n);return
        if n in visit:return
        in_stack.add(n);visit.add(n)
        for e in direct[n]:dfs(e)
        in_stack.remove(n)
    if 'UEOT' in modules: dfs('UEOT')
    for k in modules:dfs(k)
    # DFS above visited all; root reachability separately.
    reach=set()
    def walk(n):
        if n in reach:return
        reach.add(n)
        for j in direct[n]:walk(j)
    if 'UEOT' in modules:walk('UEOT')
    indeg=Counter(y for v in direct.values() for y in v)
    cross=Counter()
    for m, deps in direct.items():
        for d in deps:
            if modules[m]['category'] != modules[d]['category']:
                cross[(modules[m]['category'],modules[d]['category'])]+=1
    result={'schema_version':3,
       'source_tree_sha256': source_digest.hexdigest(),
       'scope':'literal first-party UEOT Lean source files and their direct imports',
       'source_semantics':'metadata audit, NOT independent theorem-source semantic certification',
       'total_Lean_modules':len(modules),
       'total_source_lines':sum(v['lines'] for v in modules.values()),
       'total_theorem_lemma_tokens':sum(v['theorem_lemma_count'] for v in modules.values()),
       'category_counts':dict(Counter(v['category'] for v in modules.values())),
       'reachable_from_UEOT_root':len(reach),
       'not_reachable_from_UEOT_root':sorted(set(modules)-reach),
       'cycles_detected':cycles,
       'missing_internal_imports':missing,
       'most_imported_first_party':[{'module':m,'direct_dependents':indeg[m]}
            for m in sorted(modules,key=lambda m:(-indeg[m],m))[:45]],
       'cross_category_direct_edges':[{'from':a,'to':b,'edges':n}
              for (a,b),n in sorted(cross.items())],
       'entries':modules}
    OUT.write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
    return result

if __name__=='__main__':
    d=manifest()
    print('UMC_GLOBAL_MODULE_SURVEY', json.dumps(
       {k:d[k] for k in
        ['source_tree_sha256','total_Lean_modules','total_source_lines','total_theorem_lemma_tokens',
         'category_counts','reachable_from_UEOT_root','not_reachable_from_UEOT_root',
         'cycles_detected','missing_internal_imports']},ensure_ascii=False))
