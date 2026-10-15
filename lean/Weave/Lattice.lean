import Mathlib

/-!
# The lattice: cones, quads, and the wrap (proofs.md T4–T6, H3)

Planar coordinates: a block is `(x, t)` with `x + t` even; layers grow downward.
Parents are `(x - 1, t - 1)` and `(x + 1, t - 1)`; their shared parent (the *meet*,
apex of the quad face) is `(x, t - 2)`. The cylinder is the plane modulo lateral shifts
by `W = 2P` half-block units.

* `cone_inter`, `cone_union` (+ finite versions) — **T4**, the quad lemma.
* `children_in_cone_meet_in_cone` — **T5**, Case A of cone consistency.
* `wrap_needs_half_lap`, `same_winding_below_half_lap` — **T6**, Case B needs half a lap.
* `digest_recurrence` — **H3**, exact inclusion–exclusion for summed digests.
-/

namespace Weave.Lattice

/-- `u` lies in the closed past cone of `v` (on the plane). -/
abbrev InCone (v u : ℤ × ℤ) : Prop := u.2 ≤ v.2 ∧ |u.1 - v.1| ≤ v.2 - u.2

/-- Lattice points: `x + t` even. -/
abbrev OnLattice (u : ℤ × ℤ) : Prop := (u.1 + u.2) % 2 = 0

/-- Upper-left parent. -/
def pL (v : ℤ × ℤ) : ℤ × ℤ := (v.1 - 1, v.2 - 1)

/-- Upper-right parent. -/
def pR (v : ℤ × ℤ) : ℤ × ℤ := (v.1 + 1, v.2 - 1)

/-- The parents' shared parent: apex of `v`'s quad face. -/
def meet (v : ℤ × ℤ) : ℤ × ℤ := (v.1, v.2 - 2)

/-! ## T4: the quad lemma -/

/-- The two parents' cones overlap in exactly the meet's cone. -/
theorem cone_inter (v u : ℤ × ℤ) :
    (InCone (pL v) u ∧ InCone (pR v) u) ↔ InCone (meet v) u := by
  obtain ⟨x, t⟩ := v
  obtain ⟨y, s⟩ := u
  simp only [InCone, pL, pR, meet, abs_le]
  constructor <;> intro h <;> omega

/-- A block's cone is itself plus its parents' cones. -/
theorem cone_union (v u : ℤ × ℤ) (hv : OnLattice v) (hu : OnLattice u) :
    InCone v u ↔ (u = v ∨ InCone (pL v) u ∨ InCone (pR v) u) := by
  obtain ⟨x, t⟩ := v
  obtain ⟨y, s⟩ := u
  simp only [InCone, OnLattice, pL, pR, abs_le, Prod.mk.injEq] at *
  constructor <;> intro h <;> omega

/-! ## T5: Case A -/

/-- If both children of `u` lie in `v`'s cone, so does their common child — whose adjacency
check compares the two children's references to `u`. -/
theorem children_in_cone_meet_in_cone (v u : ℤ × ℤ)
    (h1 : InCone v (u.1 - 1, u.2 + 1)) (h2 : InCone v (u.1 + 1, u.2 + 1)) :
    InCone v (u.1, u.2 + 2) := by
  obtain ⟨x, t⟩ := v
  obtain ⟨y, s⟩ := u
  simp only [InCone, abs_le] at *
  omega

/-! ## T6: Case B -/

/-- Lift the cylinder of circumference `W` to the plane. Suppose the two children of
`u = (y, ·)`, at depth `t - s` below `v = (x, t)`, are reached through windings `a ≠ b`,
i.e. their lifts `(y - 1 + a W, s)` and `(y + 1 + b W, s)` both lie in `v`'s planar cone.
Then the cone is at least half a lap deep: `W ≤ 2 (t - s) + 2`. -/
theorem wrap_needs_half_lap (W x y t s a b : ℤ) (hW : 0 < W) (hab : a ≠ b)
    (h1 : |(y - 1 + a * W) - x| ≤ t - s) (h2 : |(y + 1 + b * W) - x| ≤ t - s) :
    W ≤ 2 * (t - s) + 2 := by
  rw [abs_le] at h1 h2
  rcases lt_or_gt_of_ne hab with h | h
  · have hk : W ≤ b * W - a * W := by nlinarith
    generalize a * W = A at h1 hk
    generalize b * W = B at h2 hk
    omega
  · have hk : W ≤ a * W - b * W := by nlinarith
    generalize a * W = A at h1 hk
    generalize b * W = B at h2 hk
    omega

/-- **C3.** With `W = 2P`, any history less than `P - 1` layers deep reaches both children
through the same winding, so the adjacency check alone (Case A) gives consistency. -/
theorem same_winding_below_half_lap (P x y t s a b : ℤ) (hP : 0 < P)
    (h1 : |(y - 1 + a * (2 * P)) - x| ≤ t - s) (h2 : |(y + 1 + b * (2 * P)) - x| ≤ t - s)
    (hshallow : t - s < P - 1) : a = b := by
  by_contra hab
  have := wrap_needs_half_lap (2 * P) x y t s a b (by omega) hab h1 h2
  omega

/-! ## Finite cones and the exact digest recurrence (H3) -/

/-- The cone of `v` down to genesis (layer `0`), as a finite set of lattice points. -/
def cone (v : ℤ × ℤ) : Finset (ℤ × ℤ) :=
  ((Finset.Icc (v.1 - v.2) (v.1 + v.2)) ×ˢ (Finset.Icc 0 v.2)).filter
    (fun u => InCone v u ∧ OnLattice u)

theorem mem_cone (v u : ℤ × ℤ) : u ∈ cone v ↔ 0 ≤ u.2 ∧ InCone v u ∧ OnLattice u := by
  obtain ⟨x, t⟩ := v
  obtain ⟨y, s⟩ := u
  simp only [cone, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, InCone, OnLattice,
    abs_le]
  constructor <;> intro h <;> omega

theorem cone_inter_finset (v : ℤ × ℤ) : cone (pL v) ∩ cone (pR v) = cone (meet v) := by
  ext u
  rw [Finset.mem_inter, mem_cone, mem_cone, mem_cone]
  obtain ⟨x, t⟩ := v
  obtain ⟨y, s⟩ := u
  simp only [InCone, OnLattice, pL, pR, meet, abs_le]
  constructor <;> intro h <;> omega

theorem cone_eq_insert (v : ℤ × ℤ) (hv : OnLattice v) (ht : 1 ≤ v.2) :
    cone v = insert v (cone (pL v) ∪ cone (pR v)) := by
  ext u
  rw [Finset.mem_insert, Finset.mem_union, mem_cone, mem_cone, mem_cone]
  obtain ⟨x, t⟩ := v
  obtain ⟨y, s⟩ := u
  simp only [InCone, OnLattice, pL, pR, abs_le, Prod.mk.injEq] at *
  constructor <;> intro h <;> omega

theorem self_not_mem_parents (v : ℤ × ℤ) : v ∉ cone (pL v) ∪ cone (pR v) := by
  rw [Finset.mem_union, mem_cone, mem_cone]
  obtain ⟨x, t⟩ := v
  simp only [InCone, OnLattice, pL, pR, abs_le]
  omega

/-- **H3.** Inclusion–exclusion over the quad face: for any summed digest
`D(S) = ∑_{u ∈ S} Δ u` in an abelian group (e.g. ECMH),
`D(cone v) + D(cone meet) = Δ v + D(cone p_L) + D(cone p_R)`. On the plane; on the cylinder
this needs the cone to be less than half a lap deep (T6). It certifies nothing about
exclusivity (I1). -/
theorem digest_recurrence {A : Type*} [AddCommGroup A] (Δ : ℤ × ℤ → A) (v : ℤ × ℤ)
    (hv : OnLattice v) (ht : 1 ≤ v.2) :
    ∑ u ∈ cone v, Δ u + ∑ u ∈ cone (meet v), Δ u
      = Δ v + ∑ u ∈ cone (pL v), Δ u + ∑ u ∈ cone (pR v), Δ u := by
  calc ∑ u ∈ cone v, Δ u + ∑ u ∈ cone (meet v), Δ u
      = Δ v + (∑ u ∈ cone (pL v) ∪ cone (pR v), Δ u
          + ∑ u ∈ cone (pL v) ∩ cone (pR v), Δ u) := by
        rw [cone_eq_insert v hv ht, Finset.sum_insert (self_not_mem_parents v),
          ← cone_inter_finset v, add_assoc]
    _ = Δ v + ∑ u ∈ cone (pL v), Δ u + ∑ u ∈ cone (pR v), Δ u := by
        rw [Finset.sum_union_inter, add_assoc]

/-- The same recurrence, solved for the block's digest. -/
theorem digest_recurrence' {A : Type*} [AddCommGroup A] (Δ : ℤ × ℤ → A) (v : ℤ × ℤ)
    (hv : OnLattice v) (ht : 1 ≤ v.2) :
    ∑ u ∈ cone v, Δ u
      = Δ v + ∑ u ∈ cone (pL v), Δ u + ∑ u ∈ cone (pR v), Δ u - ∑ u ∈ cone (meet v), Δ u :=
  eq_sub_of_add_eq (digest_recurrence Δ v hv ht)

end Weave.Lattice
