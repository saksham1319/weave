import Mathlib

/-!
# Merging cannot preserve exclusivity on its own (proofs.md I1, I2)

States are multiplicity vectors over three coins `x, y, z`, written `(m_x, m_y, m_z)`.
A shared ancestor `q` holds `x`. One branch spends `x` into `y`, the other spends `x` into `z`.
Each branch is exclusive and each transaction conserves the count, yet the merge
`a + b - q = q + txXY + txXZ` holds `x` at multiplicity `-1`.
-/

namespace Weave.Merge

/-- Multiplicities of coins `x, y, z`. -/
abbrev M := ℤ × ℤ × ℤ

/-- Exclusive: every coin appears 0 or 1 times. -/
abbrev Exclusive (m : M) : Prop :=
  (m.1 = 0 ∨ m.1 = 1) ∧ (m.2.1 = 0 ∨ m.2.1 = 1) ∧ (m.2.2 = 0 ∨ m.2.2 = 1)

/-- Signed count (what a homomorphic cardinality certificate tracks). -/
def signed (m : M) : ℤ := m.1 + m.2.1 + m.2.2

/-- Spendable supply: coins with positive multiplicity. -/
def spendable (m : M) : ℤ := max m.1 0 + max m.2.1 0 + max m.2.2 0

/-- The shared ancestor holds coin `x`. -/
def q : M := (1, 0, 0)

/-- Spend `x`, create `y`. -/
def txXY : M := (-1, 1, 0)

/-- Spend `x`, create `z`. -/
def txXZ : M := (-1, 0, 1)

theorem q_excl : Exclusive q := by decide
theorem left_excl : Exclusive (q + txXY) := by decide
theorem right_excl : Exclusive (q + txXZ) := by decide
theorem txs_conserve : signed txXY = 0 ∧ signed txXZ = 0 := by decide

/-- Merging two branches over their shared ancestor is `a + b - q`. -/
theorem merge_eq : (q + txXY) + (q + txXZ) - q = q + txXY + txXZ := by abel

/-- The merge double-spends `x`. -/
theorem merged_not_excl : ¬ Exclusive (q + txXY + txXZ) := by decide

/-- **I1.** No verifier is sound (accepts only exclusive states), complete (accepts every
exclusive state) and closed under merging branches whose transactions conserve count. -/
theorem no_merge_closed_verifier :
    ¬ ∃ V : M → Prop,
      (∀ m, V m → Exclusive m) ∧ (∀ m, Exclusive m → V m) ∧
        (∀ s t₁ t₂, V s → V (s + t₁) → V (s + t₂) → signed t₁ = 0 → signed t₂ = 0 →
          V (s + t₁ + t₂)) := by
  rintro ⟨V, sound, complete, closed⟩
  exact merged_not_excl
    (sound _ (closed q txXY txXZ (complete _ q_excl) (complete _ left_excl)
      (complete _ right_excl) txs_conserve.1 txs_conserve.2))

/-- **I2.** The signed count is unchanged by the double spend… -/
theorem signed_conserved : signed (q + txXY + txXZ) = signed q := by decide

/-- …while spendable supply grew by one. -/
theorem spendable_grows : spendable (q + txXY + txXZ) = spendable q + 1 := by decide

/-- Spendable supply is not additive, so no homomorphic digest can track it. -/
theorem spendable_not_additive : ∃ a b : M, spendable (a + b) ≠ spendable a + spendable b :=
  ⟨(1, 0, 0), (-1, 0, 0), by decide⟩

end Weave.Merge
