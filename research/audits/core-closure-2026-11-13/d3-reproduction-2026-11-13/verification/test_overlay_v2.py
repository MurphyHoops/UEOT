"""Narrow filesystem regression check for the observed D3 cache-root failure.
No Lean execution; only temporary fake cache files are created.
"""
import importlib.util
import json
import os
from pathlib import Path
import tempfile

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("d3_v2", HERE / "run_d3_reproduction_v2.py")
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)
plan = json.loads((HERE / "D3_PLAN.json").read_text())
stems = {x["module"].replace(".", "/") for x in plan["fresh_modules"]} | {"D3Probe"}
extensions = [".olean", ".ilean", ".olean.private", ".olean.server", ".trace", ".server", ".olean.trace"]

with tempfile.TemporaryDirectory(prefix="ueot-d3-v2-") as td:
    root = Path(td).resolve()
    cache, overlay, probe = root / "cache", root / "overlay", root / "probe"
    cache.mkdir()
    probe.mkdir()
    for stem in stems:
        for ext in extensions:
            path = cache / (stem + ext)
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(("old immutable " + stem + ext).encode())
    old_dependency = cache / "UEOT/V3/PredictionAE.olean"
    old_dependency.write_bytes(b"reused PredictionAE")
    old_dependency.with_suffix(".trace").write_bytes(b"old Lake trace")
    external = root / "linked-namespace-source"
    external.mkdir()
    (external / "Helper.olean").write_bytes(b"linked-directory child")
    (cache / "UEOT/LinkedNamespace").symlink_to(external, target_is_directory=True)

    before = runner.snapshot_cached_targets(cache, stems)
    assert not overlay.exists(), "old snapshot must precede overlay creation"
    assert len(before) == len(stems) * len(extensions)
    overlay.mkdir()
    mirrored = runner.mirror_project_cache(cache, overlay, stems)
    assert mirrored["linked_directory_count"] == 0
    assert mirrored["linked_file_count"] == 3
    assert (overlay / "UEOT").is_dir() and not (overlay / "UEOT").is_symlink()
    assert (overlay / "UEOT/LinkedNamespace").is_dir()
    assert not (overlay / "UEOT/LinkedNamespace").is_symlink()
    assert (overlay / "UEOT/LinkedNamespace/Helper.olean").is_symlink()
    for stem in stems:
        for ext in extensions:
            assert not os.path.lexists(overlay / (stem + ext)), (stem, ext)

    reported_old = overlay / "UEOT/V3/PredictionAE.olean"
    absolute_old = runner.classify_dependency(str(reported_old), probe, overlay)
    relative_old = runner.classify_dependency(os.path.relpath(reported_old, probe), probe, overlay)
    assert absolute_old["resolved_path"] == relative_old["resolved_path"] == str(old_dependency)
    assert not absolute_old["fresh_overlay"] and not relative_old["fresh_overlay"]
    assert absolute_old["reported_path_is_symlink"]

    for stem in stems:
        new = overlay / (stem + ".olean")
        runner.require_fresh_slot(new, overlay)
        new.write_bytes(("new independent " + stem).encode())
        runner.require_regular_fresh_file(new, overlay)
        for reported in (str(new), os.path.relpath(new, probe)):
            item = runner.classify_dependency(reported, probe, overlay)
            assert item["fresh_overlay"] and item["resolved_path"] == str(new)
            assert not item["reported_path_is_symlink"]

    victim = overlay / "D3Probe.olean"
    victim.unlink()
    victim.symlink_to(old_dependency)
    try:
        runner.require_regular_fresh_file(victim, overlay)
        raise AssertionError("symlink must not count as fresh regular output")
    except RuntimeError:
        pass
    victim.unlink()
    victim.symlink_to(root / "missing-cache-file")
    try:
        runner.require_fresh_slot(victim, overlay)
        raise AssertionError("dangling symlink must not be a fresh slot")
    except RuntimeError:
        pass
    victim.unlink()
    victim.write_bytes(b"fresh probe restored")

    after = runner.snapshot_cached_targets(cache, stems)
    unchanged = runner.compare_cached_targets(before, after)
    assert unchanged["status"] == "UNCHANGED"
    tamper = cache / "UEOT.olean.private"
    original = tamper.read_bytes()
    tamper.write_bytes(b"simulated accidental overwrite in fake cache")
    detected = runner.compare_cached_targets(before, runner.snapshot_cached_targets(cache, stems))
    assert detected["status"] == "CHANGED"
    assert [x["relative_path"] for x in detected["changes"]] == ["UEOT.olean.private"]
    tamper.write_bytes(original)
    assert runner.compare_cached_targets(before, runner.snapshot_cached_targets(cache, stems))["status"] == "UNCHANGED"

result = {"status": "PASS_FILESYSTEM_REGRESSION_ONLY", "fresh_lean_execution": False,
          "production_files_touched": False, "selected_targets": 15, "reserved_probe": True,
          "protected_old_artifacts_tested": len(stems) * len(extensions),
          "reused_file_links": mirrored["linked_file_count"], "directory_links_created": 0,
          "absolute_and_relative_old_links_classified_reused": True,
          "all_target_extensions_excluded": True, "fresh_outputs_regular": True,
          "symlink_and_dangling_link_rejected": True, "old_target_bytes_unchanged": True,
          "simulated_old_target_overwrite_detected": True}
(HERE / "OVERLAY_V2_LOCAL_VALIDATION.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result, indent=2))
