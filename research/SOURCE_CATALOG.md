# Research source catalog

This catalog records the initial local audit.  Files have not yet been copied
into this repository; the paths below identify the workspace inputs used to
design the plan.

## Canonical core documents

| Source under `carry-lab/Wayl` | SHA-256 | Intended role |
|---|---|---|
| `native_carry_defect_probe_research_log.md` | `8be81ba74d53aa9b77807c050c74b0f8df2ba2476b56bfe237134aa1b8914f5f` | Consolidated dependency map |
| `ALL_BASES_NATIVE_CAMERA_COMMON_ZERO_SET_THEOREM.md` | `074d27a121c602af6b96e8fb2ccb7d5ef5b9b1c680ca82000000c2db258fe031` | Camera profiles, factors and analytic bridge |
| `ALL_BASES_INFINITE_CAMERA_SPECTRAL_ATLAS_THEOREM.md` | `25b291bac6d7cf6c07e7a91d1cba25ead4d46b17514c947e3536ad9294beb0a6` | Countable Gram completion and Weyl inverse |
| `LIMITE_FRAME_DEFECT_PROBES_SEM_COLAPSO.md` | `c5fcffebf1f1acfb770a26eff34b176187b2c0a57a6aa02b97b83492bff8800e` | Noncollapse target |
| `UNICIDADE_LIMITE_COVARIANCIA_DEFECT_PROBES.md` | `5a5e7024f3093aacc6aa6d37a8c22cf7f5f5c05a069bfbb0a4fa34b06d5947fc` | Return-metric covariance limit |
| `OPERADOR_ESPECTRAL_CAMERAS_DEFECT_WEYL.md` | `07a8ec4ac6446f0cb422734e2f4a8a4354825f9752847c47490e08e5451f0783` | Finite spectral pair |
| `CONVERGENCIA_FUNCIONAL_DEFECT_PROBES_POVM.md` | `c439ab475e6fcfcd67295114277193d793384dae01572c8582aa318bc8453545` | Functional moment limit |
| `TRANSFORMADA_CAUCHY_STIELTJES_POVM_E_WEYL_CAMERAS.md` | `23b468dec2322bcfbb8d2dbb96a9528bc3a5b2aa18d86b5dc3a7cd8cecaf679f` | Finite Cauchy/Weyl construction |
| `native_carry_camera_second_centered_moment_lab.py` | `d13feb6c04ff58d8660f85a5547d901c33ed091c8d6d31d879278382c95c2f9c` | Recovered second-moment and finite POVM laboratory |

## Exact duplicate families

- four copies of `MODO_MISTO_3_4_6_COUPLED_PV_SISTEMA_DISCRETO.md`;
- three copies of `WEYL_RETURN_DEFECT_CANONICAL_STATE.md`;
- two copies of `native_carry_mixed_mode_two_jump_coupled_pv_lab.py`;
- two copies of `mixed_mode_two_jump_coupled_pv_audit.json`;
- two copies of `weyl_global_nonuniversal_defect_audit.py`.

Only one canonical member of each family should enter a preserved source
bundle.

## Source defects and missing dependencies

- `three_color_creation_operator_audit.json` ends with `}t`; it must be
  preserved as an invalid original blob or repaired into a separately named
  derived artifact, never silently overwritten.
- The Python laboratories depend on historical modules including
  `native_carry_collective_operator_lab.py`,
  `native_carry_primitive_real_operator_all_bases_fixed.py` and
  `native_carry_pythagorean_node_weyl_colligation_lab.py`.  These exist in the
  tracked `carry-lab` Git history and should be materialized from an exact
  commit, not from its dirty worktree.
- `native_carry_camera_second_centered_moment_lab.py` was supplied through
  `/tmp`, parsed successfully by Python's AST parser and copied byte-for-byte to
  `carry-lab/Wayl` on 2026-08-09.

## Lean dependencies

| Repository | Exact commit | Release context |
|---|---|---|
| `green-frame-theorem` | `cd2d838bee67ad23f869a02f8ed9f0a0feb926fa` | `v2.1.0`, 511 audited public theorems |
| `finite-native-carry-operator` | `00e9d6beb17226545abf5ddf90bbfede6c7146b0` | `v0.1.0`, finite camera/operator layer |

Both use Lean and Mathlib `4.32.0`.
