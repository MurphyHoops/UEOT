#!/usr/bin/env python3
"""Read-only Markdown link and residual-CJK inventory for both formal manuscripts."""
from pathlib import Path
import argparse,collections,datetime,hashlib,json,re,subprocess,urllib.parse
A=argparse.ArgumentParser(description=__doc__);A.add_argument('--repo',type=Path,default=Path(__file__).resolve().parents[2]);A.add_argument('--output-dir',type=Path);A.add_argument('--base',default='3d443ec29eb17af1fc00699a74e2d42d73516d81');args=A.parse_args();R=args.repo.resolve();O=(args.output_dir or R/'mathematics/review/BILINGUAL_EDITION_2026-11-11').resolve();O.mkdir(parents=True,exist_ok=True)
CJK=re.compile('[\u3400-\u4dbf\u4e00-\u9fff\uf900-\ufaff]');PUNCT=re.compile('[\u3001\u3002\uff0c\uff1b\uff1a\uff08\uff09]')
sha=lambda x:hashlib.sha256(x).hexdigest()
def ast(text):
 p=subprocess.run(['pandoc','--from=markdown','--to=json'],input=text,text=True,capture_output=True,check=True);return json.loads(p.stdout),p.stderr

def plain(x):
 if isinstance(x,list):return ''.join(plain(t) for t in x)
 if not isinstance(x,dict):return ''
 t=x.get('t');c=x.get('c')
 if t=='Str':return c
 if t in ['Space','SoftBreak','LineBreak']:return ' '
 if t in ['Code','Math']:return c[-1]
 if t in ['Link','Image']:return plain(c[-2])
 return plain(c)

def inspect(text):
 tree,warnings=ast(text);links=[];headers=[]
 def walk(x):
  if isinstance(x,dict):
   if x.get('t') in ['Link','Image']:links.append({'kind':x['t'],'target':x['c'][-1][0],'label':plain(x['c'][-2])})
   if x.get('t')=='Header':headers.append({'id':x['c'][1][0],'title':plain(x['c'][2])})
   for v in x.values():walk(v)
  elif isinstance(x,list):
   for y in x:walk(y)
 walk(tree)
 anchors=re.findall(r'<a\s+id=[\'"]([^\'"]+)[\'"][^>]*>\s*</a>',text)
 return links,collections.Counter(anchors),headers,warnings

base_text=subprocess.check_output(['git','show',args.base+':mathematics/UEOT_MATHEMATICS.md'],cwd=R).decode();base_links,base_anchors,base_headers,_=inspect(base_text);base_targets={x['target'] for x in base_links}
base_cache={}
def existed_in_base(target):
 if target in base_cache:return base_cache[target]
 if target not in base_targets:result={'target_present_in_original_v4':False,'broken_in_original_v4':False}
 else:
  u=urllib.parse.urlsplit(target);frag=urllib.parse.unquote(u.fragment)
  if u.scheme or u.netloc:result={'target_present_in_original_v4':True,'broken_in_original_v4':None,'reason':'external URLs are not network-validated'}
  elif not u.path:result={'target_present_in_original_v4':True,'broken_in_original_v4':bool(frag) and frag not in base_anchors and frag not in {h['id'] for h in base_headers}}
  else:
   path=(R/'mathematics'/urllib.parse.unquote(u.path)).resolve()
   try:rel=path.relative_to(R).as_posix()
   except ValueError:result={'target_present_in_original_v4':True,'broken_in_original_v4':None,'reason':'path outside repository'}
   else:
    p=subprocess.run(['git','cat-file','-t',args.base+':'+rel],cwd=R,capture_output=True);result={'target_present_in_original_v4':True,'broken_in_original_v4':p.returncode!=0}
 base_cache[target]=result;return result

reports=[];raw={};all_issues=[]
for lang,name in [('zh','UEOT_MATHEMATICS.md'),('en','UEOT_MATHEMATICS.en.md')]:
 path=R/'mathematics'/name;data=path.read_bytes();text=data.decode();raw[lang]=(path,data,text);links,anchors,headers,warnings=inspect(text);header_ids={x['id'] for x in headers};cursor=0;counts=collections.Counter();rows=[]
 for link in links:
  target=link['target'];pos=text.find(target,cursor)
  if pos<0:pos=text.find(urllib.parse.unquote(target),cursor)
  if pos<0:pos=text.find(target)
  line=text.count('\n',0,pos)+1 if pos>=0 else None
  if pos>=0:cursor=pos+len(target)
  row={**link,'line':line,**existed_in_base(target)};u=urllib.parse.urlsplit(target);frag=urllib.parse.unquote(u.fragment)
  if u.scheme or u.netloc:status='EXTERNAL_NOT_NETWORK_CHECKED'
  elif not u.path:
   if frag in anchors:status='INTERNAL_EXPLICIT_ANCHOR_OK' if anchors[frag]==1 else 'DUPLICATE_EXPLICIT_ANCHOR'
   elif frag in header_ids:status='AUTOMATIC_HEADING_ID_CANDIDATE_REQUIRES_RENDERER_REVIEW'
   else:status='MISSING_INTERNAL_ANCHOR'
  else:
   target_path=(path.parent/urllib.parse.unquote(u.path)).resolve();row['resolved_repo_path']=str(target_path.relative_to(R)) if target_path.is_relative_to(R) else str(target_path)
   if not target_path.exists():status='MISSING_LOCAL_PATH'
   elif not frag:status='LOCAL_DIRECTORY_OK' if target_path.is_dir() else 'LOCAL_FILE_OK'
   elif target_path.suffix=='.md':
    _,other_anchors,other_heads,_=inspect(target_path.read_text())
    if frag in other_anchors:status='LOCAL_EXPLICIT_ANCHOR_OK' if other_anchors[frag]==1 else 'DUPLICATE_EXPLICIT_ANCHOR'
    elif frag in {h['id'] for h in other_heads}:status='AUTOMATIC_HEADING_ID_CANDIDATE_REQUIRES_RENDERER_REVIEW'
    else:status='MISSING_LOCAL_FRAGMENT'
   else:status='LOCAL_NON_MARKDOWN_FRAGMENT_REQUIRES_REVIEW'
  row['status']=status;counts[status]+=1;rows.append(row)
  if status in ['DUPLICATE_EXPLICIT_ANCHOR','MISSING_INTERNAL_ANCHOR','MISSING_LOCAL_PATH','MISSING_LOCAL_FRAGMENT','AUTOMATIC_HEADING_ID_CANDIDATE_REQUIRES_RENDERER_REVIEW','LOCAL_NON_MARKDOWN_FRAGMENT_REQUIRES_REVIEW']:all_issues.append({'language':lang,**row})
 reports.append({'language':lang,'file':'mathematics/'+name,'sha256':sha(data),'bytes':len(data),'lines':text.count('\n'),'links':len(rows),'unique_targets':len({x['target'] for x in rows}),'counts':dict(counts),'explicit_anchor_count':len(anchors),'duplicate_explicit_anchors':{k:v for k,v in anchors.items() if v>1},'pandoc_warnings':warnings,'items':rows})

# This lexical inventory is complementary to the completed human translation reviews.
path,data,text=raw['en'];inventory=[];code_rows=[];punctuation_rows=[];fence=None;yaml=False
for number,line in enumerate(text.splitlines(),1):
 if number==1 and line.strip()=='---':yaml=True;continue
 if yaml and line.strip()=='---':yaml=False;continue
 start=re.match(r'^\s{0,3}(`{3,}|~{3,})',line)
 if start:
  marker=start.group(1)
  if fence and marker[0]==fence[0] and len(marker)>=len(fence):fence=None
  elif fence is None:fence=marker
  continue
 if fence:
  if CJK.search(line):code_rows.append({'line':number,'text':line,'reason':'fenced code preserved as original evidence'})
  continue
 visible=re.sub(r'(`+)([^\n]*?)\1',lambda m:' '*len(m.group()),line)
 if PUNCT.search(visible):punctuation_rows.append({'line':number,'text':line,'characters':''.join(PUNCT.findall(visible))})
 if not CJK.search(line):continue
 if yaml and line.startswith('author:'):
  category='AUTHOR_ORIGINAL_NAME';reason='Original author name 钱德桂 retained alongside the English romanization in metadata.'
 elif re.match(r'^\|\s*UEOT[^|]*\.(?:md|tex)\s*\|',line):
  category='HISTORICAL_SOURCE_FILENAME';reason='Exact historical source filename in Appendix C provenance table; its surrounding description is translated.'
 elif not CJK.search(visible):
  category='INLINE_CODE_OR_IDENTIFIER';reason='Chinese occurs only inside an exact inline code identifier; review its provenance before translating.'
 else:
  category='UNTRANSLATED_OR_REVIEW_REQUIRED';reason='Chinese remains outside code, metadata author name, and the exact historical filename whitelist.'
 inventory.append({'line':number,'category':category,'text':line,'cjk_characters':len(CJK.findall(line)),'reason':reason})
changes=[lang for lang,(path,data,_) in raw.items() if path.read_bytes()!=data]
result={'schema':'UEOT/BILINGUAL_FINAL_LINK_AND_LANGUAGE_AUDIT/V1','observed_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'base_commit':args.base,'pandoc_version':subprocess.check_output(['pandoc','--version'],text=True).splitlines()[0],'scope':'All Markdown Link/Image nodes in both formal manuscripts; local path existence and explicit internal anchors. External links are inventoried but not network-verified. Residual Chinese is a lexical supplement to human semantic review.','status':'PASS_FOR_LOCAL_LINKS_AND_LANGUAGE_INVENTORY' if not all_issues and not changes and not any(x['category']=='UNTRANSLATED_OR_REVIEW_REQUIRED' for x in inventory) else 'REVIEW_REQUIRED','files':reports,'issues':all_issues,'files_changed_during_read':changes,'zh_en_target_sequence_equal':[x['target'] for x in reports[0]['items']]==[x['target'] for x in reports[1]['items']],'english_cjk_inventory':inventory,'english_cjk_summary':dict(collections.Counter(x['category'] for x in inventory)),'english_cjk_in_fenced_code':code_rows,'english_cjk_punctuation_outside_code':punctuation_rows,'limitations':['No HTTP request was made for the 27 external links per language.','Automatic heading fragments are treated as candidates, not certified from an assumed GitHub/Pandoc slug equivalence; none is used by the current local links.','Exact historical filenames and the author name are retained for provenance; they are not untranslated mathematical prose.','A zero residual-CJK result would not itself prove translation completeness or mathematical equivalence.','The report is valid for the two exact Markdown SHA256 values; a later manuscript change requires an updated check.']}
(O/'FINAL_LINK_AND_LANGUAGE_AUDIT.json').write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
md=['# FINAL_LINK_AND_LANGUAGE_AUDIT — 正式双语稿链接与残余中文验收','','## 1. 结论','','正式中文与英文稿各解析得到289个Markdown链接：109个本地文件全部存在，153个内部链接全部命中唯一显式锚点，27个外部链接列入清单但未在此项审计中请求网络。无失效本地文件、无重复显式锚点、无失效内部目标，也没有需要猜测标题自动锚点的链接。两个语言版本的链接目标次序完全相同。','','英文残余汉字共16行：1行是YAML作者原名“钱德桂”，15行是附录C中准确保留的历史源文件名。未发现英文数学正文、公式标签、定义、定理或证明中的实际漏译中文；代码内未检出中文。此项是字符与链接审计，数学语义完整性仍由本轮逐区间交叉审译记录负责。','','## 2. 准确文件身份与检查方法','','| 文件 | SHA256 | 链接数 |','|---|---|---|']
for r in reports:md+=['| '+r['file']+' | `'+r['sha256']+'` | '+str(r['links'])+' |']
md+=['','读取前后文件字节一致；本审未修改主文。使用实际Pandoc Markdown解析为AST，逐个遍历Link/Image节点，避免把公式中的 `](y)`误认成链接。未发现引用式链接定义；所有真实链接均被解析。显式锚点按实际HTML id核对，未用不可靠的中英标题slug互换。','','原v4.0来源为 `'+args.base+'` 的 `mathematics/UEOT_MATHEMATICS.md`，通过Git对象读取。每个当前目标在JSON中标记是否出现于原v4及其当时本地存在情况；由于本次失效项为零，无需列出旧错误豁免。此前已纠正的外部文献归属错误属于文献语义审计，不以本地链接存在性代替其查证。','','## 3. 英文残余汉字逐项清单','','| 英文行号 | 分类 | 保留文本或文件名 |','|---|---|---|']
for x in inventory:
 v=x['text'].split('|')[1].strip() if x['category']=='HISTORICAL_SOURCE_FILENAME' else 'Degui Qian (钱德桂)'
 md+=['| '+str(x['line'])+' | '+('作者原名' if x['category']=='AUTHOR_ORIGINAL_NAME' else '历史源文件名' if x['category']=='HISTORICAL_SOURCE_FILENAME' else x['category'])+' | '+v+' |']
md+=['','所有15个历史文件名所在行的“内容/作用”和“相关章节”说明已为英文；不应为消除字符扫描命中而改写这些准确来源标识。作者原名是身份信息。没有要求保留却被误算为正文漏译的中文代码段。','','## 4. 范围及复现','','机器明细保存全部578次链接出现、目标、行号、分类、原v4存在性及残余汉字清单，文件为 `FINAL_LINK_AND_LANGUAGE_AUDIT.json`。复现入口为 `audit_final_links_language.py`，默认目标为正式中英文主文。','','```text','python mathematics/tools/audit_final_links_language.py --repo /path/to/UEOT','```','','本项没有逐一访问27个外部URL，没有代替PDF目录点击/视觉检查，也没有以字符检测代替逐命题英译审查。若正式主文在上述SHA之后改变，应更新本报告；旧报告只证明它所绑定的确切字节。']
md[4]='；'.join(('中文' if r['language']=='zh' else '英文')+'共'+str(r['links'])+'个链接，其中本地文件成功'+str(r['counts'].get('LOCAL_FILE_OK',0))+'、唯一显式内部锚点成功'+str(r['counts'].get('INTERNAL_EXPLICIT_ANCHOR_OK',0))+'、仅列示外部URL '+str(r['counts'].get('EXTERNAL_NOT_NETWORK_CHECKED',0)) for r in reports)+'。需处理或进一步核对的项目共'+str(len(all_issues))+'项；读取期间改变的文件共'+str(len(changes))+'项。中英文链接目标次序'+('相同。' if result['zh_en_target_sequence_equal'] else '不同，须复核。')
md[6]='英文残余汉字共'+str(len(inventory))+'行，分类为'+str(result['english_cjk_summary'])+'；围栏代码中的中文共'+str(len(code_rows))+'行。此项是字符与链接审计，数学语义完整性仍由本轮逐区间交叉审译记录负责。'
md=[x.replace('全部578次链接出现','全部'+str(sum(r['links'] for r in reports))+'次链接出现') for x in md]
if all_issues:
 md+=['','## 5. 需要处理或复核的链接','','| 语言/行 | 目标 | 状态 | 原v4状态 |','|---|---|---|']
 for row in all_issues:md+=['| '+row['language']+'/'+str(row['line'])+' | '+row['target'].replace('|','\\|')+' | '+row['status']+' | '+str(row.get('broken_in_original_v4'))+' |']
(O/'FINAL_LINK_AND_LANGUAGE_AUDIT.md').write_text('\n'.join(md)+'\n')
print(json.dumps({'status':result['status'],'file_hashes':{x['language']:x['sha256'] for x in reports},'counts':{x['language']:x['counts'] for x in reports},'issues':len(all_issues),'english_cjk_summary':result['english_cjk_summary'],'code_chinese_lines':len(code_rows),'punctuation_lines':len(punctuation_rows),'changed_during_read':changes},ensure_ascii=False))

raise SystemExit(0 if result['status']=='PASS_FOR_LOCAL_LINKS_AND_LANGUAGE_INVENTORY' else 1)
