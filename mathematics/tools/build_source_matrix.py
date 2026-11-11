"""Build an auditable publication index from a fixed manuscript and static source evidence."""
import argparse,hashlib,json,re,subprocess
from pathlib import Path
BASE='3d443ec29eb17af1fc00699a74e2d42d73516d81'
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--repo',type=Path,default=Path(__file__).resolve().parents[2])
parser.add_argument('--base',default=BASE,help='Immutable Git manuscript snapshot')
parser.add_argument('--output-dir',type=Path)
parser.add_argument('--matrix-output',type=Path)
args=parser.parse_args();ROOT=args.repo.resolve()
WORK=(args.output_dir or ROOT/'mathematics/review/BILINGUAL_EDITION_2026-11-11').resolve()
MATRIX=(args.matrix_output or ROOT/'mathematics/THEOREM_SOURCE_MATRIX.md').resolve()
WORK.mkdir(parents=True,exist_ok=True);MATRIX.parent.mkdir(parents=True,exist_ok=True)
base_bytes=subprocess.check_output(['git','show',args.base+':mathematics/UEOT_MATHEMATICS.md'],cwd=ROOT)
lines=base_bytes.decode('utf-8').splitlines();book='\n'.join(lines)
ledger=json.loads((ROOT/'formalization/ueot-core/docs/compression/COMPRESSION_LEDGER.yaml').read_text())
records=json.loads((WORK/'LEAN_DECLARATION_EVIDENCE.json').read_text())
notes=dict(l.split('\t',1) for l in (WORK/'pid-review-notes.tsv').read_text().splitlines())
assert set(notes)==set(ledger['audit_records']), (set(notes)-set(ledger['audit_records']),set(ledger['audit_records'])-set(notes))
where={};heading='';location_evidence=[]
for i,l in enumerate(lines[:6933],1):
 if re.match(r'^#{1,3} ',l):heading=l.lstrip('# ')
 # Only an explicit statement label at the beginning of the line can define
 # the canonical location. Later bold references must never overwrite it.
 label=re.match(r'^\*\*((?:P|K)-[A-Z]+-\d+[^*]*)\*\*',l)
 if not label:continue
 for pid in re.findall(r'\bP-[A-Z]+-\d+\b',label.group(1)):
  assert pid not in where, (pid,where.get(pid),i)
  where[pid]=(i,heading)
  location_evidence.append({'pid':pid,'line':i,'section':heading,'statement_line':l,'method':'unique line-initial explicit bold statement label'})
assert set(where)==set(ledger['audit_records']), (set(where)-set(ledger['audit_records']),set(ledger['audit_records'])-set(where))
(WORK/'P_ID_STATEMENT_LOCATIONS.json').write_text(json.dumps({'source_commit':args.base,'source_sha256':hashlib.sha256(base_bytes).hexdigest(),'count':len(where),'statements':location_evidence},ensure_ascii=False,indent=2)+'\n')
def link(path):return '../'+path if path.startswith('formalization/') else path
md=['# THEOREM_SOURCE_MATRIX — 双语数学定本来源矩阵','','## 1. 固定身份、读法与审查层次','',f'审查源：`{args.base}`中的 `mathematics/UEOT_MATHEMATICS.md` 原 v4.0 Git快照（脚本通过 `git show` 读取，不另复制正文）。表中行号只用于本轮定位；稳定编号、源文件路径和完整声明名才是长期标识。正式4.1新增导读会改变主文行号。','','本矩阵保留 D/P/K/H/E/N/O 原规则。P 表示有数学证明，不表示结论无条件、原创或已有现实验证。下表全部106个 P-ID 的书面陈述、证明骨架及来源声明经本轮数学子审逐编号核对；163个源端点全部静态定位到实际定义文件。没有重新执行 Lean elaboration、全库证明编译或逐行重证全部依赖。结构枚举、静态声明读审、数学语义审查和历史构建回执是四种不同证据。','','原Core文件183440字节，SHA-256 `ed00dd102157cdafe3a79c45506e86dc574d6cba65feb2df8686e63ce2726303`。原106个P-ID不改写、不新增、不重编号。11个generated、89个retained_adapter、6个retained_boundary是原压缩账本的处分，不是106个定理都由四条公理产生。完整源声明由 `mathematics/tools/extract_declarations.py` 从本快照的登记文件及未变Lean源码生成；审计目录中的 `LEAN_DECLARATION_EVIDENCE.json` 保存实际 header，必须连同 Lean 的 namespace/section 参数和 structure 字段阅读。','','## 2. 冻结106个P-ID：逐编号陈述、实际端点与前提','','| P-ID / 主文位置 | 冻结源位置与处分 | 实际Lean声明与定义文件 | 数学前提、证明作用和边界（本轮逐项读审） |','|---|---|---|---|']
for pid in sorted(where,key=lambda x:where[x][0]):
 rec=ledger['audit_records'][pid];loc=where[pid];links=[]
 for r in records:
  if r['pid']!=pid:continue
  c=r['candidates'][0];links.append('`'+r['name']+'` — ['+Path(c['path']).name+']('+link(c['path'])+'):'+str(c['line']))
 d=ledger['final_dispositions'][pid]['status']
 md.append('| '+pid+' — '+loc[1]+'；原主文L'+str(loc[0])+' | Core v3.0 L'+str(rec['source_line'])+'；`'+d+'` | '+'<br>'.join(links)+' | '+notes[pid].replace('|','\\|')+' |')
md+=['','9个原来源超链接指向重导出入口而非声明定义处：本表已进一步定位实际定义文件；没有把入口文件中搜索不到声明报告成 Lean 缺失。此修正仅改善查阅路径。','','## 3. 42个M编号后继命题：保留来源与独立范围','','M编号属于书籍后继连接，不加入106个P-ID。M-21族与§35.4/35.7的形式来源已由后继真实源包补齐；不能再沿用早期“只有书面”的历史状态。下表的端点沿用本书附录F的既有映射，完整命名空间展开规则同F.1；这不是新的Lean覆盖计数。','','| 编号 / 原主文行 | 原状态与内容 | 精确源映射（附录F） |','|---|---|---|']
mmap={}
for l in lines[7683:7759]:
 cells=[x.strip() for x in l.split('|')]
 if len(cells)>=4 and cells[1].startswith('M-'):
  key=cells[1]
  ids=re.findall(r'M-\d+\.\d+',key)
  if '–' in key and len(ids)==2:
   a,b=ids;pre=a.rsplit('.',1)[0];ids=[pre+'.'+str(n) for n in range(int(a.rsplit('.',1)[1]),int(b.rsplit('.',1)[1])+1)]
  for id in ids:mmap[id]=' | '.join(cells[2:-1])
for i,l in enumerate(lines[:5464],1):
 m=re.match(r'^\*\*(M-\d+\.\d+)[^*]*\*\*(.*)',l)
 if not m:continue
 id=m.group(1);state='P/N' if id in ['M-33.1','M-34.1','M-34.3','M-37.6'] else 'P'
 title=l.replace('**','').replace('|','\\|')
 md.append('| '+id+' / L'+str(i)+' | '+state+'；'+title+' | '+mmap.get(id,'参见附录F.3.1及对应章的实际来源说明').replace('|','；')+' |')
md+=['','## 4. D、K、H、N的显式编号与来源义务','','这些条目没有被升格为新的P-ID。无独立编号的反例继续按章节定位；没有发现正文把合成模型作为E类现实证据。','','| 状态/编号 | 原主文位置 | 内容及证据层次 |','|---|---|---|']
seen=set();heading=''
for i,l in enumerate(lines[:6933],1):
 if re.match(r'^#{1,3} ',l):heading=l.lstrip('# ')
 for id in re.findall(r'\b(?:D|K|H|N)-[A-Z][A-Z0-9]*(?:-[A-Z0-9]+)*',l):
  if id in seen or not re.search(r'\*\*[^*]*'+id,l):continue
  seen.add(id);text=l.replace('**','').replace('|','\\|')
  md.append('| '+id+' | '+heading+'；L'+str(i)+' | '+text+' |')
md+=['','K条目依赖标准结果的正确假设。P-QSD/P-EVO后继工厂实际供应原接口并不抹去有限本原性、紧自伴resolvent、生成关系或正谱条件。H-INT、H-CAR-FRAME、H-DDH是机制/领域前提；目前不因形式证明而改记E。开放范围见§31.2、§34.7以及每一后继源的明确未覆盖域；历史OPEN字样与现行未覆盖域须分开。','','## 5. 第39章95节的命题族与来源包','','本节逐节给出完整覆盖位置，避免以旧目录推断范围。每节常包含多个同源辅助等式、正例和反例，故95行是来源组织单元，**不是95条独立定理的计数**。本轮逐节阅读全部自然语言主张与推导边界；未重新审查这些源包的每一行Lean证明。精确主端点和消费者见附录F.5及各包THEOREM_INDEX/SOURCE_VALIDATION，书中包链接保留。','','| 节 / 原主文位置 | 直接来源包或模块 | 主张类型与审查边界 |','|---|---|---|']
ranges=[(1,6,'register_fault_resources_v1 / actual_infinite_sources_v1','P/H/N；真实执行、付费、后代及程序来源；保护代码、原源和评价条件保留'),(7,8,'predictive_genealogy_source_v1','P/N；可数动作、标准Borel/可数生成条件、固定先验共同版本；时戳元数据权限明确'),(9,9,'canonical_brownian_source_v1','P/H；有限Gaussian一致族到全时间源，不将存在字段当实际源'),(10,11,'continuous_history_source_v1','P/N；固定时刻修改与样本连续分别证明；完整历史控制不可压成最后事件'),(12,13,'adaptive_stochastic_sources_v1','P/H；fresh adaptive协议和整个自然过去条件增量，非不可数任意协议'),(14,14,'history_integral_source_v1','P；同输入类和原有限输出身份'),(15,16,'predictable_finite_purpose_v1','P/H；原可预测L²稠密性；有限训练Good和实际返回策略'),(17,18,'continuous_resource_source_v1','P/N/H；连续积分版本与外部供给，非封闭能源'),(19,21,'compensator_population_source_v1','P/N；补偿鞅不等于一般分割QV；子代经验Price需正出生数'),(22,22,'full_qv_vector_training_source_v1','P/H；确定分割L¹/概率极限，不冒称所有分割a.s.'),(23,25,'vector_weighted_population_source_v1','P/H/N；联合过去、资金训练和完整人口/读数源，None/无出生保留'),(26,29,'ito_vector_calibration_source_v1','P/H/N；真实同输入Itô/OU/常控制与校准，导数界、条件数及风险类型保留'),(30,30,'past_feedback_scale_source_v1','P/H；原过去有限反馈表，最终Q能量，非EP替换'),(31,33,'table_continuous_funding_source_v1','P/H/N；向量连续版本、逐计划资金充要、分离条件有用接受'),(34,38,'bounded_control_carrier_source_v1 / q_integral_vector_qv_program_source_v1','P/H/N；有界部署、同输入Q积分、固定输入QV、实际AST与有限输出障碍'),(39,41,'fixed_q_run_stateweighted_source_v1','P/H；固定QA、真实ItoRun/无限奖励及状态权重、可数程序记录'),(42,44,'state_ito_q_martingale_recovery_source_v1','P/H/N；有限维Itô有导数界，Q过程逐时a.e.，恢复检查非最优'),(45,48,'drift_ou_instruction_qfull_source_v1','P/H/N；可测漂移点采样反例、物理OU、指定程序GOD/GOA、完整Q域'),(49,51,'rotating_body_dynamic_price_source_v1','P/H/N；轮末身体/真实子对象、全价格参数分类，时钟与作用域明确'),(52,54,'resource_block_dynamic_data_source_v1','P/H/N；同源有限钱包健康占据障碍、块运输、数据选择后联合风险'),(55,57,'funded_countable_block_source_v1','P/H/N；先供给支付、可数块、实际轮末首命中；非微步骤命中'),(58,60,'native_lifecycle_rank_source_v1','P/H/N；同对象/同记录律与有限线性秩充分性，非全局非线性ΠΦ'),(61,64,'p9_lineage_organization_source_v1','P/H/N；同一P9六性质、实际有限世代Price、同tick组织；历史状态须标明'),(65,67,'owner_discovery_resource_source_v1','P/H/N；owner/clock登记、父标记风险和有限全账本；读权限成本明确'),(68,69,'finite_predictive_source_v1','P/H/N；同钱包/首出生父、规范预测与实际控制；旧尾部缺口为历史阶段'),(70,71,'finite_predictive_source_v1 / conflict_family_book_source_v1','P/H/N；实际末亲本续行与旧具名结果真实消费，不把有限钱包变无限资金'),(72,74,'general_perron_compact_spectral_source_v1','P/K/H；一般本原矩阵工厂、实际resolvent谱展开及非零余项实例'),(75,81,'joint_decision_closure_v1','P/H/N；有限期限、持久未知率、同菜单单钱包Bayes最优；非无限或全知最优'),(82,88,'decision_representation_closure_v1','P/H/N；可执行统计/全动作证书/同返回图，接受器正确而非通用生成器完备'),(89,95,'mechanism_decision_closure_v1','P/H/N；固定S/G机制、独立私随机、全策略TV与minimax regret；native_decide公理依赖须保留')]
for i,l in enumerate(lines,1):
 m=re.match(r'^## (39\.(\d+)) (.*)',l)
 if not m:continue
 n=int(m.group(2));r=next(x for x in ranges if x[0]<=n<=x[1]);packages=[]
 for pkg in r[2].split(' / '):
  path='../formalization/ueot-core/docs/compression/theory_completion/unified_closure/'+pkg+'/'
  packages.append('['+pkg+']('+path+')')
 md.append('| '+m.group(1)+' '+m.group(3)+'；L'+str(i)+' | '+'；'.join(packages)+' | '+r[3]+' |')
md+=['','## 6. 核心总论、全部章与附录的覆盖','','核心总论的7部分以 `core_theory_closure_v1/THEOREM_INDEX.md`、同源增长/选择反馈的实际源及本书正文为来源。总论中的增长率比较类、程序真实实现、机制参数正域、付费与身份条件均按各段检查；有限期望指数界、正公共底数的最小性、书面n次根推论和a.s.人口增长不混型。','','| 范围 | 本轮实际检查 | 未由该检查推出的结论 |','|---|---|---|','| 核心总论 I–VII | 同源parts/wallet/census，付费再生，ρ=max(1,kc,(1−q)kb+qkc)，两程序参数区间，有限期望族及固定代数先后极限 | 不表示物理自治、未知参数学习、a.s.人口增长或所有环境的优化 |','| 0–17 | 全部陈述/证明骨架、106对应项、重要反例及条件接口 | 不把被动预测等同干预、访问擦除等同物理死亡 |','| 18–31 | 全部陈述/证明骨架，评价/控制/GOA/路径KL/ΠΦ/复制及装配 | 不从结构产生唯一规范目标；不把不同最优类混合 |','| 32–35 | 全部M命题与证明，八类层级、四机制、校准、P0–P12及同源安全 | 不把四机制计数替代全部适配器；不把P12条件终端写成普遍自创生 |','| 36–38 | 全部M命题、真实后验和占据，正逃逸、支持可行双向，真实训练—选择—部署 | 不把训练分布替代部署、不丢未见质量、不用不同Good拼接 |','| 39.1–95 | 每节自然语言数学主张及来源/机制/概率/比较类边界 | 不是本轮重编译或逐行重证全部后继Lean库 |','| A | 符号及数学类型；Q_n局部复用另加澄清 | 同字符不保证跨章同类型 |','| B | 106个稳定P编号与正文出现一一对照 | 编号不表示原创、无条件性或自然支持 |','| C | 标准依赖分类及真实引用错误影响；外部文献由主代理核验 | 文献链接存在不等于所述主题正确 |','| D | 完整代码/历史输出作为被冻结证据；本轮结构检查保留代码 | 未把2371断言冒称全理论证明或本轮执行 |','| E | 升级门槛、复现与历史版本边界 | 不以旧3.1交付状态替代当前4.1验收 |','| F | 命名空间、全部后继M映射、源码及回执层次，历史OPEN域 | 历史回执不是本轮CI；局部CLOSED不等于自然验证 |','','## 7. 可复现性和剩余风险','','自动检查应独立核对106个P、42个M、所有显式D/K/H/N、95个第39章节、全部公式块/代码/证明结束符/链接和中英结构。它只能发现结构漏项及符号漂移，不能证明翻译量词与所有隐含前提正确。出版后的逐命题英译复核另记 TRANSLATION_EQUIVALENCE_AUDIT，不能由本矩阵的中文审阅状态自动继承。']
MATRIX.write_text('\n'.join(md)+'\n')
print({'pids':len(where),'M':sum(1 for l in lines if re.match(r'^\*\*M-\d+\.\d+',l)),'explicit_nonP_ids':len(seen),'chapter39_sections':sum(1 for l in lines if re.match(r'^## 39\.\d+ ',l)),'matrix_bytes':MATRIX.stat().st_size})
