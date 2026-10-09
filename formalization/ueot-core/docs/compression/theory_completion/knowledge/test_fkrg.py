#!/usr/bin/env python3
"""Offline, adversarial regression for FKRG discovery, freshness, reuse and scope."""
from pathlib import Path
import json
import sqlite3
import subprocess
import tempfile
import unittest
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
