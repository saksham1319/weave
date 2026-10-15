import Mathlib

/-!
# Shards, meetings and antipodes (proofs.md T8)

Light-cone coordinates: with planar `(x, t)`, put `a = (x + t)/2`, `b = (x - t)/2`, so
`t = a - b` and `x = a + b`. On a ring of `P` blocks, `a mod P` names a block's left strand
and `b mod P` its right strand; a block is the crossing of the two.

* `layersEquivShards`, `card_shards`, `meets_once` — exactly `P²` shards; each strand pair
  meets exactly once per `P` layers.
* `next_meeting`, `meeting_is_antipode` — consecutive meetings are exactly `P` layers apart,
  `P` half-block units sideways: half way round a ring of `W = 2P` units.
* `shards_after_expand`, `shards_after_contract` — elastic defects move the count to `(P ± 1)²`.
-/

namespace Weave.Shards

section Integer

/-- Two meetings of the same strand pair (`a ≡ a'`, `b ≡ b'` mod `P`) are a multiple of `P`
layers apart, so the next one is at least `P` layers later. -/
theorem next_meeting (P a b a' b' : ℤ) (ha : P ∣ a' - a) (hb : P ∣ b' - b)
    (hlater : a - b < a' - b') : a - b + P ≤ a' - b' := by
  have hd : P ∣ (a' - b') - (a - b) := by
    have h := dvd_sub ha hb
    have e : a' - a - (b' - b) = (a' - b') - (a - b) := by ring
    rwa [e] at h
  have := Int.le_of_dvd (by omega) hd
  omega

/-- The next meeting `(a + P, b)` is exactly `P` layers later and `P` units sideways. -/
theorem meeting_is_antipode (P a b : ℤ) :
    ((a + P) - b) - (a - b) = P ∧ ((a + P) + b) - (a + b) = P := by
  constructor <;> ring

end Integer

section Ring

variable (P : ℕ) [NeZero P]

/-- The block in layer `t` on left strand `α` sits on right strand `α - t`. -/
def shardOf (p : ZMod P × ZMod P) : ZMod P × ZMod P := (p.2, p.2 - p.1)

/-- Over any `P` consecutive layers, blocks `(t, α)` and strand pairs are in bijection. -/
def layersEquivShards : ZMod P × ZMod P ≃ ZMod P × ZMod P where
  toFun := shardOf P
  invFun s := (s.1 - s.2, s.1)
  left_inv p := by simp [shardOf]
  right_inv s := by simp [shardOf]

/-- There are exactly `P²` shards. -/
theorem card_shards : Fintype.card (ZMod P × ZMod P) = P ^ 2 := by
  simp [Fintype.card_prod, ZMod.card, sq]

/-- Strands `α` (left) and `β` (right) meet in layer `t` iff `t ≡ α - β (mod P)`:
exactly once per `P` layers. -/
theorem meets_once (α β t : ZMod P) : (∃ a, shardOf P (t, a) = (α, β)) ↔ t = α - β := by
  constructor
  · rintro ⟨a, h⟩
    simp only [shardOf, Prod.mk.injEq] at h
    obtain ⟨rfl, h⟩ := h
    rw [← h]
    ring
  · rintro rfl
    exact ⟨α, by simp [shardOf]⟩

end Ring

/-- An expansion adds one strand pair. -/
theorem shards_after_expand (P : ℕ) : (P + 1) ^ 2 = P ^ 2 + 2 * P + 1 := by ring

/-- A contraction removes one strand pair. -/
theorem shards_after_contract (P : ℕ) (hP : 1 ≤ P) : (P - 1) ^ 2 + 2 * P = P ^ 2 + 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, P = k + 1 := ⟨P - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  ring

end Weave.Shards
