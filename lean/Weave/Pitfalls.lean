import Mathlib

/-!
# Historical pitfalls (proofs.md §1)

* **H1** — summing coin points `r • G` over one generator hides cardinality and double spends.
* **H2** — the `n⁻¹` percolation rule weights ancestors by binomial fractions, not by 1,
  so certificates stop being multiset digests and cut-through fails.
-/

namespace Weave.Pitfalls

/-! ## H1: one generator -/

/-- Two coins `a • G, b • G` and the single coin `(a + b) • G` have the same sum,
but different sizes: a sum cannot see cardinality (coin splitting / inflation). -/
theorem sum_hides_cardinality {A : Type*} [AddCommGroup A] (G : A) (a b : ℤ) :
    ({a • G, b • G} : Multiset A).sum = ({(a + b) • G} : Multiset A).sum ∧
      Multiset.card ({a • G, b • G} : Multiset A) ≠ Multiset.card ({(a + b) • G} : Multiset A) := by
  constructor
  · simp [add_zsmul]
  · simp

/-- Spending `C_A` twice looks exactly like spending two coins whose sum is `2 C_A`. -/
theorem sum_hides_double_spend {A : Type*} [AddCommGroup A] (CA CX CY : A)
    (h : CX + CY = CA + CA) :
    ({CA, CA} : Multiset A).sum = ({CX, CY} : Multiset A).sum := by
  simp [h]

/-! ## H2: `n⁻¹` percolation

`w k j` is the weight the rule `D(v) = ½ D(p_L) + ½ D(p_R) + Δ(v)` gives to an ancestor
`k` layers up at lateral offset `j` (half-block units). An honest multiset digest would need
weight `1` for every ancestor. -/

/-- Weight of an ancestor `k` layers up at lateral offset `j` under the `n⁻¹` rule. -/
def w : ℕ → ℤ → ℚ
  | 0, j => if j = 0 then 1 else 0
  | k + 1, j => (w k (j - 1) + w k (j + 1)) / 2

/-- The meet (two layers up, straight above) gets weight `½`. -/
theorem w_meet : w 2 0 = 1 / 2 := by norm_num [w]

/-- The ancestor three layers up, one unit left, gets weight `3/8`. -/
theorem w_far : w 3 (-1) = 3 / 8 := by norm_num [w]

/-- A coin created at `(x-1, t-3)` and spent at the meet `(x, t-2)` should vanish from `v`'s
certificate; under the `n⁻¹` rule it leaves residue `-1/8`. -/
theorem percolation_residue : w 3 (-1) - w 2 0 = -1 / 8 := by
  rw [w_far, w_meet]; norm_num

/-- Ancestors are not counted once: the certificate is not a multiset digest. -/
theorem percolation_not_multiset : w 2 0 ≠ 1 := by
  rw [w_meet]; norm_num

end Weave.Pitfalls
