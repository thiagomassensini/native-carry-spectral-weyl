#!/usr/bin/env python3
"""Cross-check local Lean theorems, the public registry, audit, and claims."""

from __future__ import annotations

import json
import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
MODULES = [
    (ROOT / "NativeCarrySpectralWeyl/Camera/PeriodicProfiles.lean",
     "NativeCarrySpectralWeyl.Camera."),
    (ROOT / "NativeCarrySpectralWeyl/Camera/Geometry.lean",
     "NativeCarrySpectralWeyl.Camera."),
    (ROOT / "NativeCarrySpectralWeyl/Camera/Factors.lean",
     "NativeCarrySpectralWeyl.Camera."),
    (ROOT / "NativeCarrySpectralWeyl/Camera/NativeLineFloor.lean",
     "NativeCarrySpectralWeyl.Camera."),
    (ROOT / "NativeCarrySpectralWeyl/Camera/FiniteCoefficientBridge.lean",
     "NativeCarrySpectralWeyl.Camera.FiniteBridge."),
    (ROOT / "NativeCarrySpectralWeyl/Camera/C2InteriorProfile.lean",
     "NativeCarrySpectralWeyl.Camera.FiniteBridge."),
    (ROOT / "NativeCarrySpectralWeyl/Camera/NaturalInteriorProfile.lean",
     "NativeCarrySpectralWeyl.Camera.FiniteBridge."),
    (ROOT / "NativeCarrySpectralWeyl/Camera/ProfileDirichlet.lean",
     "NativeCarrySpectralWeyl.Camera."),
    (ROOT / "NativeCarrySpectralWeyl/Camera/BracketSeries.lean",
     "NativeCarrySpectralWeyl.Camera."),
    (ROOT / "NativeCarrySpectralWeyl/Camera/NormalConvergence.lean",
     "NativeCarrySpectralWeyl.Camera."),
    (ROOT / "NativeCarrySpectralWeyl/Camera/BracketProfileBridge.lean",
     "NativeCarrySpectralWeyl.Camera.FiniteBridge."),
    (ROOT / "NativeCarrySpectralWeyl/Camera/BracketProfileFactorization.lean",
     "NativeCarrySpectralWeyl.Camera."),
    (ROOT / "NativeCarrySpectralWeyl/Camera/CrossFactorization.lean",
     "NativeCarrySpectralWeyl.Camera."),
    (ROOT / "NativeCarrySpectralWeyl/Camera/CommonZeroSet.lean",
     "NativeCarrySpectralWeyl.Camera."),
    (ROOT / "NativeCarrySpectralWeyl/Camera/QuantitativeTail.lean",
     "NativeCarrySpectralWeyl.Camera."),
    (ROOT / "NativeCarrySpectralWeyl/Camera/DerivativeTail.lean",
     "NativeCarrySpectralWeyl.Camera."),
    (ROOT / "NativeCarrySpectralWeyl/Camera/HigherDerivativeTail.lean",
     "NativeCarrySpectralWeyl.Camera."),
    (ROOT / "NativeCarrySpectralWeyl/Camera/ZeroMultiplicity.lean",
     "NativeCarrySpectralWeyl.Camera."),
    (ROOT / "NativeCarrySpectralWeyl/Camera/ModalEnergy.lean",
     "NativeCarrySpectralWeyl.Camera."),
    (ROOT / "NativeCarrySpectralWeyl/Finite/Gram.lean",
     "NativeCarrySpectralWeyl.Finite."),
    (ROOT / "NativeCarrySpectralWeyl/Finite/Moments.lean",
     "NativeCarrySpectralWeyl.Finite."),
    (ROOT / "NativeCarrySpectralWeyl/Finite/Whitening.lean",
     "NativeCarrySpectralWeyl.Finite."),
    (ROOT / "NativeCarrySpectralWeyl/Finite/StepDensity.lean",
     "NativeCarrySpectralWeyl.Finite."),
    (ROOT / "NativeCarrySpectralWeyl/Finite/StepPOVM.lean",
     "NativeCarrySpectralWeyl.Finite."),
    (ROOT / "NativeCarrySpectralWeyl/Limits/PeriodicMean.lean",
     "NativeCarrySpectralWeyl.Limits."),
    (ROOT / "NativeCarrySpectralWeyl/Limits/CameraCovariance.lean",
     "NativeCarrySpectralWeyl.Limits."),
    (ROOT / "NativeCarrySpectralWeyl/Limits/ResolventWeight.lean",
     "NativeCarrySpectralWeyl.Limits."),
]


def fail(message: str) -> None:
    raise SystemExit(f"registry check failed: {message}")


registry = json.loads((ROOT / "audit/theorem-registry.json").read_text())
entries = registry["theorems"]
if registry["count"] != len(entries):
    fail("declared theorem count differs from registry length")

expected_ids = [f"NCSW-{index:03d}" for index in range(1, len(entries) + 1)]
ids = [entry["id"] for entry in entries]
qualified = [entry["qualified"] for entry in entries]
if ids != expected_ids:
    fail("theorem IDs are not contiguous and ordered")
if len(set(qualified)) != len(qualified):
    fail("qualified theorem names are not unique")

source_names: list[str] = []
for module, prefix in MODULES:
    text = module.read_text()
    names = re.findall(
        r"^(?:@\[[^\n]*\]\s*)?theorem\s+([A-Za-z0-9_']+)",
        text,
        re.MULTILINE,
    )
    source_names.extend(prefix + name for name in names)
if source_names != qualified:
    fail("registry order or content differs from local theorem declarations")

audit_text = (ROOT / "NativeCarrySpectralWeyl/Audit.lean").read_text()
audit_names = re.findall(r"^#print axioms\s+(\S+)\s*$", audit_text, re.MULTILINE)
if audit_names != qualified:
    fail("Audit.lean order or content differs from theorem registry")

ledger = json.loads((ROOT / "audit/claim-ledger.json").read_text())
if ledger["registry_count"] != len(entries):
    fail("claim ledger registry_count is stale")
claims = ledger["claims"]
if ledger["count"] != len(claims):
    fail("declared claim count differs from ledger length")
known_ids = set(ids)
used_ids: set[str] = set()
for claim in claims:
    theorem_ids = claim.get("theorem_ids", [])
    unknown = set(theorem_ids) - known_ids
    if unknown:
        fail(f"claim {claim['id']} cites unknown IDs: {sorted(unknown)}")
    used_ids.update(theorem_ids)
if used_ids != known_ids:
    fail(f"claim ledger coverage differs from registry: {sorted(known_ids ^ used_ids)}")

print(f"registry check passed: {len(entries)} theorems, {len(claims)} claims")
