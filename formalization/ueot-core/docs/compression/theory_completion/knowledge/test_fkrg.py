#!/usr/bin/env python3
"""Offline, adversarial regression for FKRG discovery, freshness, reuse and scope."""
from pathlib import Path
from hashlib import sha256
import json
import sqlite3
import subprocess
import tempfile
import unittest
from unittest import mock
from contextlib import redirect_stdout
import io
import sys

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE))
import fkrg

class FkrgTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.tmp=tempfile.TemporaryDirectory(prefix="fkrg-test-")
        cls.db=Path(cls.tmp.name)/"index.sqlite3"
        fkrg.build(cls.db)
    @classmethod
    def tearDownClass(cls):cls.tmp.cleanup()

    def test_full_current_modules_discovered(self):
        c,meta=fkrg.fresh(self.db)
        self.assertEqual(int(meta["module_count"]),len(fkrg.sources()))
        self.assertGreaterEqual(int(meta["declaration_count"]),3500)
        self.assertEqual(meta["scope"] if "scope" in meta else
                         meta["type_authority"],
                         "LEXICAL_CANDIDATES_REQUIRE_KERNEL_VERIFICATION")
        self.assertTrue(c.execute("SELECT 1 FROM declarations WHERE kind='theorem' LIMIT 1").fetchone())
        c.close()

    def test_frozen_core_source_and_stochastic_bridge_found(self):
        c,_=fkrg.fresh(self.db)
        for sym in ("UEOT.V3.ViabilitySource.p_per_03",
                    "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.stochastic_future_complete_probes_card_le",
                    "UEOT.V3.Compression.Objecthood.RepairLawSelfReconstruction.jointRepairKernel_restored"):
            self.assertIsNotNone(c.execute("SELECT id FROM declarations WHERE candidate=?",(sym,)).fetchone())
        c.close()

    def test_inline_attribute_declaration_indexed(self):
        c,_=fkrg.fresh(self.db)
        row=c.execute("SELECT kind FROM declarations WHERE candidate=?",(
            "UEOT.V3.FiniteDiscountedControl.Model.coe_discountNN",)).fetchone()
        self.assertIsNotNone(row, "Codex #306: @[simp] theorem missing")
        self.assertEqual(row["kind"],"theorem")
        c.close()

    def test_qualified_declaration_not_truncated(self):
        c,_=fkrg.fresh(self.db)
        row=c.execute("SELECT candidate FROM declarations WHERE candidate=?",(
            "UEOT.V3.ProcessInterface.Interface.comp",)).fetchone()
        self.assertIsNotNone(row,"Codex #306: def Interface.comp truncated")
        wrong=c.execute("""SELECT candidate FROM declarations
           WHERE path LIKE ? AND line=36 AND candidate=?""",(
           "%/ProcessInterface.lean","UEOT.V3.ProcessInterface.Interface")).fetchone()
        self.assertIsNone(wrong)
        c.close()

    def test_offline_status_without_origin_main(self):
        self.assertIsNone(fkrg.optional_ref("refs/remotes/nonexistent-remote/main"))
        with mock.patch.object(fkrg,"optional_ref",return_value=None):
            sink=io.StringIO()
            with redirect_stdout(sink):
                fkrg.status(self.db)
            result=json.loads(sink.getvalue())
            self.assertIsNone(result["cached_origin_main"])
            self.assertEqual(result["index_state"],"FRESH")
            self.assertEqual(result["remote_ci"],"NOT_CHECKED_OFFLINE")

    def test_umc_scope_mirrors_immutable_base_l2_exact_path_authorizations(self):
        import audit_umc_local as umc
        branch="compression/theory-completion-fkrg-review-fixes"
        prefix="formalization/ueot-core/docs/compression/theory_completion/knowledge/"
        approved=prefix+"fkrg.py"
        # Immutable-base policy FIXTURE: after temporary L2 authorization is
        # revoked from main, this unit test must retain its original semantics.
        policy={"tracks":{"TC":{"mutable_existing_exact_paths":[]}},
                "l2_existing_path_exceptions":[{
                    "track":"TC","temporary":True,
                    "branch_patterns":["^compression/theory-completion-fkrg-review-fixes$"],
                    "paths":[approved]}]}
        seen=[]
        def fixed_baseline(command,**kwargs):
            seen.append(command)
            if "ls-tree" in command:
                return "\n".join((approved,prefix+"README.md",
                                    prefix+"FKRG_TASKS.json"))+"\n"
            if "show" in command:
                return json.dumps(policy)
            raise AssertionError(("unexpected immutable-base query",command))
        with mock.patch.object(umc,"run",side_effect=fixed_baseline):
            umc.validate_tc_local_scope("IMMUTABLE_BASE",branch,[approved])
            for unauthorized in (prefix+"README.md",prefix+"FKRG_TASKS.json"):
                with self.subTest(path=unauthorized):
                    with self.assertRaisesRegex(RuntimeError,"out-of-scope"):
                        umc.validate_tc_local_scope("IMMUTABLE_BASE",branch,
                                                    [unauthorized])
            with self.assertRaisesRegex(RuntimeError,"out-of-scope"):
                umc.validate_tc_local_scope("IMMUTABLE_BASE",None,[approved])
            umc.validate_tc_local_scope("IMMUTABLE_BASE",branch,
                                        [prefix+"FKRG_NEW_RESEARCH_NOTE.md"])
        self.assertTrue(any("show" in command for command in seen))
        self.assertTrue(any("ls-tree" in command for command in seen))

    def test_fast_audit_cannot_overwrite_full_receipt(self):
        import audit_umc_local
        with tempfile.TemporaryDirectory(prefix="fkrg-nonfull-") as tmp:
            target=Path(tmp)/"receipt.json"
            immutable='{"UMC_axioms":"145/145_LEAN_STANDARD_AXIOMS","full_Lean":"PASS"}\n'
            target.write_text(immutable)
            result={"UMC_axioms":"NOT_RUN","full_Lean":"NOT_RUN"}
            audit_umc_local.write_audit_receipt(result,full=False,output=target)
            self.assertEqual(target.read_text(),immutable)

    def test_fast_audit_does_not_create_receipt(self):
        import audit_umc_local
        with tempfile.TemporaryDirectory(prefix="fkrg-no-receipt-") as tmp:
            target=Path(tmp)/"receipt.json"
            audit_umc_local.write_audit_receipt(
                {"full_Lean":"NOT_RUN"},full=False,output=target)
            self.assertFalse(target.exists())

    def test_full_audit_receipt_writer(self):
        import audit_umc_local
        with tempfile.TemporaryDirectory(prefix="fkrg-full-receipt-") as tmp:
            target=Path(tmp)/"receipt.json"
            result={"full_Lean":"PASS","fixture":"serialization only"}
            audit_umc_local.write_audit_receipt(result,full=True,output=target)
            self.assertEqual(json.loads(target.read_text()),result)
            self.assertTrue(target.read_bytes().endswith(b"\n"))

    def test_full_audit_preserves_historical_receipt(self):
        import audit_umc_local
        with tempfile.TemporaryDirectory(prefix="fkrg-historical-receipt-") as tmp:
            historical=Path(tmp)/"UMC_LOCAL_EXACT_HEAD_AUDIT_V4.json"
            previous=Path(tmp)/"UMC_LOCAL_EXACT_HEAD_AUDIT_V3.json"
            original=b'{"full_Lean":"PASS","historical":true}\n'
            historical.write_bytes(original)
            previous.write_bytes(original)
            with mock.patch.object(audit_umc_local,"OUT",historical), \
                 mock.patch.object(audit_umc_local,"HERE",Path(tmp)):
                audit_umc_local.write_audit_receipt({"full_Lean":"PASS"},full=True)
                self.assertEqual(historical.read_bytes(),original)
                for old in (historical,previous):
                    with self.subTest(receipt=old.name):
                        with self.assertRaisesRegex(RuntimeError,"HISTORICAL_UMC_RECEIPT"):
                            audit_umc_local.write_audit_receipt(
                                {"full_Lean":"PASS"},full=True,output=old)
            self.assertEqual(historical.read_bytes(),original)
            self.assertEqual(previous.read_bytes(),original)

    def test_inventory_detached_no_private_branch(self):
        import audit_local_branch_inventory as inventory
        def fake_git(*args,**kwargs):
            if args[0]=="symbolic-ref":return None
            if args[0]=="for-each-ref":return "feature"
            if args[0]=="worktree":return ""
            if args[0]=="rev-parse" and args[-1] in ("HEAD","deadbeef"):
                return "deadbeef"
            if args[0]=="rev-parse" and args[-1]=="feature":return "featureSHA"
            if args[0]=="rev-parse":return None
            raise AssertionError(("unexpected git call",args))
        with tempfile.TemporaryDirectory(prefix="fkrg-inventory-") as tmp:
            with mock.patch.object(inventory,"ROOT",Path(tmp)):
                with mock.patch.object(inventory,"git",side_effect=fake_git):
                    data=inventory.build()
            self.assertIsNone(data["active_branch"])
            self.assertEqual(data["active_local_head"],"deadbeef")
            self.assertEqual(data["baseline_ref"],"deadbeef")
            self.assertEqual(data["branch_count"],1)
            self.assertIsNone(data["main"])
            self.assertFalse(data["main_comparison_available"])
            self.assertEqual(data["baseline_meaning"],
                             "HEAD_ONLY_NOT_MAIN_DO_NOT_CLASSIFY_MERGED")
            self.assertEqual(data["branches"][0]["status"],"MAIN_BASELINE_UNAVAILABLE")
            self.assertIsNone(data["branches"][0]["is_main_ancestor"])
            self.assertIsNone(data["branches"][0]["unique_commits_vs_main"])
            self.assertNotIn("ALREADY",data["branches"][0]["recommendation"])
            with mock.patch.object(inventory,"build",return_value=data):
                report=Path(tmp)/"offline.md"
                inventory.run(report=report)
                self.assertIn("UNAVAILABLE",report.read_text())
                self.assertIn("不可判为已合并",report.read_text())
                self.assertIn("历史合并结论未验证",report.read_text())
                self.assertNotIn("formal/p*",report.read_text())
                self.assertNotIn("主线主动收窄",report.read_text())
                with self.assertRaisesRegex(ValueError,"historical"):
                    inventory.run(output=inventory.OUT)

    def test_cross_module_import_lookup(self):
        c,_=fkrg.fresh(self.db)
        sym="UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.reconstructed_program_joint_and_source_safety"
        self.assertIsNotNone(c.execute("SELECT id FROM declarations WHERE candidate=?",(sym,)).fetchone())
        c.close()

    def test_every_open_task_has_real_reuse_candidates(self):
        c,meta=fkrg.fresh(self.db)
        tasks=json.loads(fkrg.TASKS.read_text())["tasks"]
        for name,t in tasks.items():
            self.assertEqual(t["status"],"OPEN")
            self.assertTrue(t["new_obligations"] and t["known_boundaries"])
            self.assertTrue(t["reuse_symbols"])
            for sym in t["reuse_symbols"]:
                self.assertIsNotNone(
                    c.execute("SELECT 1 FROM declarations WHERE candidate=?",(sym,)).fetchone(),
                    (name,sym))
        c.close()

    def test_stale_index_rejected(self):
        c=sqlite3.connect(self.db)
        old=c.execute("SELECT value FROM meta WHERE key='source_tree_sha256'").fetchone()[0]
        c.execute("UPDATE meta SET value='DELIBERATE_DRIFT' WHERE key='source_tree_sha256'")
        c.commit();c.close()
        with self.assertRaisesRegex(RuntimeError,"STALE_INDEX"):
            fkrg.fresh(self.db)
        c=sqlite3.connect(self.db)
        c.execute("UPDATE meta SET value=? WHERE key='source_tree_sha256'",(old,))
        c.commit();c.close()
        good,_=fkrg.fresh(self.db);good.close()

    def test_cache_from_old_extractor_is_stale_even_if_lean_unchanged(self):
        c=sqlite3.connect(self.db)
        recorded=dict(c.execute("SELECT key,value FROM meta").fetchall())
        try:
            self.assertEqual(recorded["schema"],"FKRG_V2")
            self.assertEqual(len(recorded["extractor_sha256"]),64)
            for key,value in (("schema","FKRG_V1"),
                              ("extractor_sha256","OLD_PARSER_DIGEST")):
                c.execute("UPDATE meta SET value=? WHERE key=?",(value,key))
                c.commit()
                with self.assertRaisesRegex(RuntimeError,"STALE_INDEX"):
                    fkrg.fresh(self.db)
                c.execute("UPDATE meta SET value=? WHERE key=?",
                          (recorded[key],key))
                c.commit()
            good,_=fkrg.fresh(self.db)
            good.close()
        finally:
            c.close()

    def test_imported_comment_parser_changes_invalidate_cached_index(self):
        with tempfile.TemporaryDirectory(prefix="fkrg-parser-drift-") as temp:
            alternative=Path(temp)/"changed_comment_parser.py"
            original=fkrg.COMMENT_PARSER_PATH.read_bytes()
            alternative.write_bytes(original + b"\\n# test-only parser change\\n")
            observed=fkrg.extractor_fingerprint()
            with mock.patch.object(fkrg,"COMMENT_PARSER_PATH",alternative):
                self.assertNotEqual(fkrg.extractor_fingerprint(),observed)
                with self.assertRaisesRegex(RuntimeError,"STALE_INDEX"):
                    fkrg.fresh(self.db)
            con,meta=fkrg.fresh(self.db)
            self.assertEqual(meta["extractor_sha256"],observed)
            con.close()

    def test_private_helpers_not_alias_public_lean_theorems(self):
        c,_=fkrg.fresh(self.db)
        rows=c.execute("""SELECT candidate FROM declarations
            WHERE simple='survivalProb_zero_eq_one_of_not_mem'""").fetchall()
        self.assertGreaterEqual(len(rows),2)
        self.assertEqual(len(rows),len({r[0] for r in rows}))
        for (candidate,) in rows:
            self.assertTrue(candidate.startswith("private@"),candidate)
            with self.assertRaisesRegex(RuntimeError,"PRIVATE_LEAN"):
                fkrg.lean_check(c,candidate)
        c.close()

    def test_unknown_symbol_refuses_kernel_verification(self):
        c,_=fkrg.fresh(self.db)
        with self.assertRaisesRegex(RuntimeError,"NO_LEXICAL_FULL_NAME"):
            fkrg.lean_check(c,"UEOT.V3.DoesNotExist.nonexistent")
        c.close()

    def test_frozen_counts_not_promoted(self):
        self.assertEqual(len(json.loads((HERE.parent/"unified_closure"/
                         "UMC_CORE_106_SEMANTIC_REVIEW_V1.json").read_text())["rows"]),106)
        self.assertNotIn("FULL_MATHEMATICAL_CLOSURE",fkrg.TASKS.read_text())
        self.assertFalse((HERE/"FKRG_COUNTED_LEDGER.json").exists())


class UMCBaselineGitTests(unittest.TestCase):
    """Exercise fetched-main selection against real commits and ancestry."""

    def setUp(self):
        import audit_umc_local
        self.umc=audit_umc_local
        tmp=tempfile.TemporaryDirectory(prefix="umc-main-ancestry-")
        self.addCleanup(tmp.cleanup)
        self.repo=Path(tmp.name)
        self.git("init","--quiet","--initial-branch=main")
        (self.repo/"baseline.txt").write_text("frozen baseline\n")
        self.git("add","baseline.txt")
        self.git("commit","--quiet","-m","baseline")
        self.base=self.git("rev-parse","HEAD")
        base_tree=self.git("rev-parse",f"{self.base}^{{tree}}")

        # This path is already present on newer main. Using the older fetched
        # ref could wrongly classify its later modification as an L1 addition.
        self.existing_path=("formalization/ueot-core/docs/compression/"
                            "theory_completion/knowledge/AlreadyOnMain.md")
        existing=self.repo/self.existing_path
        existing.parent.mkdir(parents=True)
        existing.write_text("existing on the newer main commit\n")
        self.git("add",self.existing_path)
        self.git("commit","--quiet","-m","main adds governed file")
        self.ahead=self.git("rev-parse","HEAD")
        ahead_tree=self.git("rev-parse",f"{self.ahead}^{{tree}}")
        self.fork=self.git("commit-tree",base_tree,"-p",self.base,"-m","other main")
        self.unrelated=self.git("commit-tree",base_tree,"-m","unrelated root")
        self.research=self.git("commit-tree",ahead_tree,"-p",self.ahead,
                               "-m","research tip consumes fetched main")
        self.merge=self.git("commit-tree",ahead_tree,"-p",self.ahead,
                            "-p",self.fork,"-m","candidate contains both histories")
        self.git("checkout","--detach","--quiet",self.research)

    def git(self,*args):
        return subprocess.run(
            ["git","-c","user.name=UEOT regression fixture",
             "-c","user.email=ueot-fixture@example.invalid",
             "-c","commit.gpgSign=false","-c","core.hooksPath=/dev/null",*args],
            cwd=self.repo,text=True,capture_output=True,check=True).stdout.strip()

    def test_only_consistent_fetched_main_is_a_pinned_baseline(self):
        self.assertNotIn(self.existing_path,
                         self.git("ls-tree","-r","--name-only",self.base).splitlines())
        self.assertIn(self.existing_path,
                      self.git("ls-tree","-r","--name-only",self.ahead).splitlines())
        cases=[
            ("equal refs",self.base,self.base,self.research,True),
            ("fetched main advanced",self.ahead,self.base,self.research,True),
            ("no local main",self.ahead,None,self.research,True),
            ("missing fetched main",None,self.ahead,self.research,False),
            ("fetched ref behind local governed file",self.base,self.ahead,self.research,False),
            ("diverged main refs",self.fork,self.ahead,self.merge,False),
            ("unrelated main histories",self.unrelated,self.ahead,self.unrelated,False),
            ("HEAD behind fetched main",self.ahead,self.base,self.base,False),
            ("HEAD diverged from fetched main",self.ahead,self.base,self.fork,False),
        ]
        # Only the fixture directory is substituted. Git resolution, ancestry,
        # and the production baseline selector all execute without mocks.
        with mock.patch.object(self.umc,"ROOT",self.repo):
            for label,origin,local,head,accepted in cases:
                with self.subTest(case=label):
                    self.git("checkout","--detach","--quiet",head)
                    for ref,value in (("refs/remotes/origin/main",origin),
                                      ("refs/heads/main",local)):
                        if value is None:
                            self.git("update-ref","-d",ref)
                        else:
                            self.git("update-ref",ref,value)
                    if accepted:
                        self.assertEqual(self.umc.baseline_main_ref(),origin)
                    else:
                        with self.assertRaises(RuntimeError):
                            self.umc.baseline_main_ref()


class UMCFastAuditIntegrationTests(unittest.TestCase):
    """Run the entire fast audit, separately from receipt writer unit tests."""

    def test_real_fast_audit_preserves_all_historical_receipts(self):
        import audit_umc_local as umc

        def historical_bytes():
            return {path.name:path.read_bytes() for path in
                    sorted(umc.HERE.glob("UMC_LOCAL_EXACT_HEAD_AUDIT_V*.json"))}

        before=historical_bytes()
        self.assertIn(umc.OUT.name,before)
        try:
            # No atlas, import, scope, stage, DAG, baseline, or writer mock:
            # a broken fast-audit contract must fail this integration test.
            result=umc.audit(False)
        finally:
            # Assert both path-set and byte preservation even if audit raises.
            self.assertEqual(historical_bytes(),before)

        self.assertEqual(result["source_PIDs_located"],106)
        self.assertEqual(result["research_modules"],result["public_root_imports"])
        self.assertEqual(result["global_bundled_Lean_modules"],len(fkrg.sources()))
        self.assertTrue(result["full_import_dag_acyclic_reachable_complete"])
        self.assertEqual(result["full_Lean"],"NOT_RUN")
        self.assertEqual(result["UMC_axioms"],"NOT_RUN")
        self.assertIsNone(result["UMC_native_census"])
        self.assertEqual(result["global_strong_unified_closure"],"NOT_ESTABLISHED")
        self.assertEqual(result["scientific_external_evidence"],"UNVERIFIED")


class UMCSourceFreshnessTests(unittest.TestCase):
    """Mandatory current-source integration gate plus bounded negative fixtures."""

    def setUp(self):
        import audit_umc_local
        self.umc=audit_umc_local
        tmp=tempfile.TemporaryDirectory(prefix="umc-source-dag-")
        self.addCleanup(tmp.cleanup)
        self.core=Path(tmp.name)/"core"
        self.bridge=self.core/"UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/Fixture.lean"
        self.bridge.parent.mkdir(parents=True)
        self.root=self.core/"UEOT.lean"
        self.root.write_text("import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.Fixture\n")
        self.bridge.write_text("-- a source-hash fixture, not a compiled proof\n")
        modules={
            path.relative_to(self.core).with_suffix('').as_posix().replace('/', '.'):path
            for path in (self.root,self.bridge)}
        digest=sha256()
        for name,path in sorted(modules.items()):
            digest.update(name.encode('utf-8')+b'\0'+path.read_bytes()+b'\0')
        self.dag={
            "entries":{name:{} for name in modules},
            "source_tree_sha256":digest.hexdigest(),
            "total_Lean_modules":2,"reachable_from_UEOT_root":2,
            "not_reachable_from_UEOT_root":[],"cycles_detected":[],
            "missing_internal_imports":{},"category_counts":{"UMC_New_Bridges":1}}
        self.dag_path=Path(tmp.name)/"dag.json"
        self.write_dag()

    def write_dag(self,changes=None):
        value=dict(self.dag)
        value.update(changes or {})
        self.dag_path.write_text(json.dumps(value))

    def validate_fixture(self):
        return self.umc.validate_global_source_dag(self.core,self.dag_path)

    def test_current_source_dag_is_fresh(self):
        # Real checked-out source and stored DAG; no UMC atlas, stage,
        # receipt, or branch-authorization mock can suppress this gate.
        current=self.umc.validate_global_source_dag()
        self.assertEqual(current["total_Lean_modules"],len(fkrg.sources()))

    def test_minimal_source_fixture_is_valid(self):
        self.assertEqual(self.validate_fixture()["total_Lean_modules"],2)

    def test_added_source_module_is_rejected(self):
        (self.core/"UEOT/Extra.lean").write_text("-- new source module\n")
        with self.assertRaisesRegex(RuntimeError,"module paths disagree"):
            self.validate_fixture()

    def test_deleted_source_module_is_rejected(self):
        self.bridge.unlink()
        with self.assertRaisesRegex(RuntimeError,"module paths disagree"):
            self.validate_fixture()

    def test_source_byte_drift_is_rejected(self):
        self.bridge.write_text(self.bridge.read_text()+"-- changed source bytes\n")
        with self.assertRaisesRegex(RuntimeError,"source fingerprint mismatch"):
            self.validate_fixture()

    def test_stale_counts_hash_or_open_graph_are_rejected(self):
        cases=[
            ("total",{"total_Lean_modules":3,"reachable_from_UEOT_root":3},"incorrect total modules"),
            ("umc",{"category_counts":{"UMC_New_Bridges":2}},"UMC module count mismatch"),
            ("hash",{"source_tree_sha256":"0"*64},"source fingerprint mismatch"),
            ("cycle",{"cycles_detected":["UEOT"]},"import graph not closed"),
            ("missing",{"missing_internal_imports":{"UEOT":["UEOT.Absent"]}},"import graph not closed"),
            ("unreachable",{"not_reachable_from_UEOT_root":["UEOT.Fixture"]},"import graph not closed"),
            ("reach_count",{"reachable_from_UEOT_root":1},"import graph not closed"),
        ]
        for label,changes,message in cases:
            with self.subTest(case=label):
                self.write_dag(changes)
                with self.assertRaisesRegex(RuntimeError,message):
                    self.validate_fixture()

class UMCNativeEvidenceTests(unittest.TestCase):
    def test_discovery_keeps_nested_and_attributed_public_names(self):
        import audit_umc_local as umc
        with tempfile.TemporaryDirectory(prefix="umc-nested-discovery-") as tmp:
            root=Path(tmp)
            source=root/"UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/Fixture.lean"
            source.parent.mkdir(parents=True)
            source.write_text("""namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
namespace Nested
@[simp] theorem visible : True := trivial
private theorem hidden : True := trivial
end Nested
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
namespace DifferentLogicalNamespace
theorem still_owned_by_source_module : True := trivial
end DifferentLogicalNamespace
""")
            with mock.patch.object(umc,"CORE",root), mock.patch.object(fkrg,"REPO",root):
                names=umc.discover_umc_theorem_candidates([source])
            self.assertEqual(names,[
                "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.Nested.visible",
                "DifferentLogicalNamespace.still_owned_by_source_module",
            ])

    def native_report(self):
        module="UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.Fixture"
        def row(name,private=False):
            return {"name":name,"source_module":module,"is_private":private,
                    "axioms":["propext","Classical.choice","Quot.sound"]}
        return {"schema":"UMC_NATIVE_AXIOM_CENSUS_V1","source_modules":[module],
                "theorems":[row("Nested.public"),row("DifferentLogicalNamespace.public"),
                            row("_private.Fixture.0.hidden",True),row("Nested.generated.eq_1")]}

    def parse_report(self,report):
        import audit_umc_local as umc
        return umc.parse_native_umc_audit(
            "UMC_NATIVE_AUDIT_JSON "+json.dumps(report)+"\n",
            ["UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.Fixture"],
            ["Nested.public","DifferentLogicalNamespace.public"],["Nested.public"])

    def test_native_scope_keeps_private_generated_and_other_logical_namespace(self):
        result=self.parse_report(self.native_report())
        self.assertEqual(result["theorem_constants"],4)
        self.assertEqual(result["private_theorem_constants"],1)
        self.assertEqual(result["confirmed_public_source_candidates"],2)
        self.assertEqual(result["other_native_public_constants"],1)
        # A lexical candidate cannot override native private classification or
        # be counted in both categories if candidate discovery was imprecise.
        report=self.native_report()
        report["theorems"][1]["is_private"]=True
        result=self.parse_report(report)
        self.assertEqual(result["private_theorem_constants"],2)
        self.assertEqual(result["confirmed_public_source_candidates"],1)
        self.assertEqual(result["other_native_public_constants"],1)

    def test_malformed_or_untrusted_native_evidence_is_rejected(self):
        mutations=[
            ("scope",lambda d:d.update(source_modules=[]),"compiled module scope mismatch"),
            ("duplicate",lambda d:d["theorems"].append(dict(d["theorems"][0])),"duplicate native"),
            ("outside",lambda d:d["theorems"][1].update(source_module="Outside.Module"),"outside compiled"),
            ("axiom",lambda d:d["theorems"][2].update(axioms=["Private.escape"]),"nonstandard axiom"),
            ("classification",lambda d:d["theorems"][2].update(is_private="true"),"private-name classification"),
            ("stage",lambda d:d["theorems"].pop(0),"stage cites missing compiled"),
        ]
        for label,mutate,message in mutations:
            with self.subTest(case=label):
                report=self.native_report()
                mutate(report)
                with self.assertRaisesRegex(RuntimeError,message):
                    self.parse_report(report)


if __name__=="__main__":
    unittest.main(verbosity=2)
