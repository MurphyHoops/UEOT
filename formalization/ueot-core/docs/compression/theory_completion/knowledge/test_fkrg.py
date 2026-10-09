#!/usr/bin/env python3
"""Offline, adversarial regression for FKRG discovery, freshness, reuse and scope."""
from pathlib import Path
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

    def test_ci_detached_main_baseline_falls_back_to_origin_main(self):
        import audit_umc_local
        from types import SimpleNamespace
        seen=[]
        def fake_run(argv,**kwargs):
            seen.append(argv[-1])
            return SimpleNamespace(returncode=1 if
                argv[-1]=="refs/heads/main" else 0)
        with mock.patch.object(audit_umc_local.subprocess,"run",side_effect=fake_run):
            self.assertEqual(audit_umc_local.baseline_main_ref(),
                             "refs/remotes/origin/main")
        self.assertEqual(seen,["refs/heads/main","refs/remotes/origin/main"])
        with mock.patch.object(audit_umc_local.subprocess,"run",
                              return_value=SimpleNamespace(returncode=1)):
            with self.assertRaisesRegex(RuntimeError,"main baseline unavailable"):
                audit_umc_local.baseline_main_ref()

    def test_fast_audit_cannot_overwrite_full_receipt(self):
        import audit_umc_local
        with tempfile.TemporaryDirectory(prefix="fkrg-nonfull-") as tmp:
            target=Path(tmp)/"receipt.json"
            immutable='{"UMC_axioms":"145/145_LEAN_STANDARD_AXIOMS","full_Lean":"PASS"}\n'
            target.write_text(immutable)
            with mock.patch.object(audit_umc_local,"OUT",target):
                result=audit_umc_local.audit(False)
            self.assertEqual(target.read_text(),immutable)
            self.assertEqual(result["full_Lean"],"NOT_RUN")

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

if __name__=="__main__":
    unittest.main(verbosity=2)
