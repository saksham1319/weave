# Weave — Lean formalisation

Machine-checkable statements behind [`proofs.md`](../proofs.md). Read that file for the narrative; this folder is the reference for agents who need exact statements.

## Status: written offline, **not yet machine-checked**
These files were written without a Lean toolchain, so nothing here has been compiled.

What to expect:
- **Statements** are intended to be final.
- **Proofs** use conservative tactics (`omega`, `simp`, `decide`, `norm_num`, `ring`, `abel`, `nlinarith`). They may need small repairs, typically lemma renames between Mathlib versions.

When fixing a broken proof:
- **Keep the statement.** If a statement turns out to be false, record that in `proofs.md` before changing it.
- **Don't paper over it.** Never replace a proof with `sorry` without noting it here.

### To check (needs network once)
```bash
cd lean
lake exe cache get   # prebuilt Mathlib
lake build
```
`lean-toolchain` and `lakefile.toml` pin Lean/Mathlib `v4.22.0`. If that tag is unavailable, set `rev = "master"` and the matching toolchain, then run `lake update`.

## Map
| File | proofs.md | Main declarations |
|---|---|---|
| `Weave/Pitfalls.lean` | H1, H2 | `sum_hides_cardinality`, `sum_hides_double_spend`, `w`, `percolation_residue`, `percolation_not_multiset` |
| `Weave/Merge.lean` | I1, I2 | `no_merge_closed_verifier`, `signed_conserved`, `spendable_grows`, `spendable_not_additive` |
| `Weave/Digest.lean` | I3 | `compressing_digest_collides`, `every_digest_has_every_size` |
| `Weave/Slots.lean` | T1, T2, T3, T9 | `count_update`, `excl_spend`, `excl_create`, `excl_relocate`, `no_double_spend`, `count_run`, `excl_run`, `count_relocate`, `count_pair`, `adopt_conserves` |
| `Weave/Lattice.lean` | T4, T5, T6, H3, C3 | `cone_inter`, `cone_union`, `children_in_cone_meet_in_cone`, `wrap_needs_half_lap`, `same_winding_below_half_lap`, `digest_recurrence` |
| `Weave/Shards.lean` | T8 | `layersEquivShards`, `card_shards`, `meets_once`, `next_meeting`, `meeting_is_antipode`, `shards_after_expand`, `shards_after_contract` |

## Not formalised (and why)
| Item | Why it isn't here |
|---|---|
| I3 (Gentry–Wichs), I4 (Tamassia–Triandopoulos), I5 (Fiat–Shamir in-circuit, AROM), I6 (quantum) | Cited results about computational models. They are stated in `proofs.md`. |
| T7 (cone consistency), as a whole | Its geometric steps are T5/T6 above. The induction over hash-linked histories and the crossing-register step are argued in `proofs.md`. A natural next target: model a history as a function from positions to sets of block versions, the checks as equalities, and prove "no position has two versions". |
| Main soundness theorem | Rests on cryptographic assumptions A1–A4 (knowledge soundness, collision resistance, unforgeability). These are modelled informally. |

## Conventions
- **Coordinates:** planar `(x, t)` with `x + t` even; layers grow downward; the cylinder has `W = 2P` half-block units, where `P` is blocks per ring.
- **Tables:** slot tables are `ι → Option Coin`. Merkle commitments are idealised: binding is an assumption, so proofs reason about the table directly.
- **Docstrings:** every theorem's docstring names its `proofs.md` tag.
