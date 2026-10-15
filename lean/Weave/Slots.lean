import Mathlib

/-!
# Slot tables: the contents of a strand certificate (proofs.md T1–T3, T9)

A strand's certificate commits (by a Merkle root) to a table of slots, each empty or holding
one coin. Merkle binding is a computational assumption (proofs.md A2), so it is idealised away
here: we reason about the table itself.

* `count_update` — **T1**, the edit equation.
* `excl_spend`, `excl_create`, `excl_relocate`, `excl_run`, `no_double_spend` — **T2**.
* `count_run`, `count_relocate`, `count_pair` — **T3**, scarcity.
* `adopt_conserves` — **T9**, adoption carries counts over unchanged.
-/

namespace Weave.Slots

open Finset

variable {ι Coin : Type*} [Fintype ι] [DecidableEq ι]

/-- A strand's slot table. -/
abbrev Table (ι Coin : Type*) := ι → Option Coin

/-- 1 if the slot is occupied. -/
def occ : Option Coin → ℕ
  | none => 0
  | some _ => 1

/-- Number of occupied slots. -/
def count (t : Table ι Coin) : ℕ := ∑ i, occ (t i)

/-- No coin sits in two slots. -/
def Excl (t : Table ι Coin) : Prop := ∀ i j c, t i = some c → t j = some c → i = j

/-! ## T1: the edit equation -/

/-- Rewriting one slot changes the count by exactly (what was written) − (what was there). -/
theorem count_update (t : Table ι Coin) (i : ι) (v : Option Coin) :
    count (Function.update t i v) + occ (t i) = count t + occ v := by
  have key : ∀ f : ι → ℕ, ∑ x, f x = f i + ∑ x ∈ univ.erase i, f x :=
    fun f => (add_sum_erase _ _ (mem_univ i)).symm
  unfold count
  rw [key (fun x => occ (Function.update t i v x)), key (fun x => occ (t x))]
  have hrest : ∑ x ∈ univ.erase i, occ (Function.update t i v x)
      = ∑ x ∈ univ.erase i, occ (t x) :=
    sum_congr rfl fun x hx => by rw [Function.update_apply, if_neg (ne_of_mem_erase hx)]
  rw [hrest, Function.update_apply, if_pos rfl]
  ring

/-! ## T2: exclusivity -/

theorem excl_spend {t : Table ι Coin} (h : Excl t) (i : ι) :
    Excl (Function.update t i none) := by
  intro a b c ha hb
  have ha' : t a = some c := by
    by_cases hai : a = i
    · rw [hai, Function.update_apply, if_pos rfl] at ha
      cases ha
    · rwa [Function.update_apply, if_neg hai] at ha
  have hb' : t b = some c := by
    by_cases hbi : b = i
    · rw [hbi, Function.update_apply, if_pos rfl] at hb
      cases hb
    · rwa [Function.update_apply, if_neg hbi] at hb
  exact h a b c ha' hb'

theorem excl_create {t : Table ι Coin} (h : Excl t) (i : ι) (c : Coin)
    (fresh : ∀ j, t j ≠ some c) : Excl (Function.update t i (some c)) := by
  intro a b d ha hb
  by_cases hai : a = i <;> by_cases hbi : b = i
  · rw [hai, hbi]
  · rw [hai, Function.update_apply, if_pos rfl] at ha
    rw [Function.update_apply, if_neg hbi] at hb
    cases ha
    exact absurd hb (fresh b)
  · rw [hbi, Function.update_apply, if_pos rfl] at hb
    rw [Function.update_apply, if_neg hai] at ha
    cases hb
    exact absurd ha (fresh a)
  · rw [Function.update_apply, if_neg hai] at ha
    rw [Function.update_apply, if_neg hbi] at hb
    exact h a b d ha hb

/-- After a coin is spent, no slot holds it: a second spend has nothing to open. -/
theorem no_double_spend {t : Table ι Coin} (h : Excl t) {i : ι} {c : Coin}
    (hi : t i = some c) : ∀ j, Function.update t i none j ≠ some c := by
  intro j hj
  by_cases hji : j = i
  · rw [hji, Function.update_apply, if_pos rfl] at hj
    cases hj
  · rw [Function.update_apply, if_neg hji] at hj
    exact hji (h j i c hj hi)

/-- Relocation (spend, then re-create the same coin elsewhere) keeps the table exclusive. -/
theorem excl_relocate {t : Table ι Coin} (h : Excl t) {i : ι} {c : Coin}
    (hi : t i = some c) (j : ι) :
    Excl (Function.update (Function.update t i none) j (some c)) :=
  excl_create (excl_spend h i) j c (no_double_spend h hi)

/-- Relocation leaves the count unchanged. -/
theorem count_relocate {t : Table ι Coin} {i j : ι} {c : Coin}
    (hi : t i = some c) (hj : t j = none) (hji : j ≠ i) :
    count (Function.update (Function.update t i none) j (some c)) = count t := by
  have h1 := count_update t i none
  have h2 := count_update (Function.update t i none) j (some c)
  rw [hi] at h1
  rw [Function.update_apply, if_neg hji, hj] at h2
  simp only [occ] at h1 h2
  omega

/-! ## Edits and runs -/

/-- One edit to a table. -/
inductive Op (κ C : Type*)
  | spend (i : κ)
  | create (i : κ) (c : C)

namespace Op

/-- The table after the edit. -/
def apply (t : Table ι Coin) : Op ι Coin → Table ι Coin
  | spend i => Function.update t i none
  | create i c => Function.update t i (some c)

/-- When an edit is allowed: spend an occupied slot; create a fresh coin in an empty slot. -/
def Allowed (t : Table ι Coin) : Op ι Coin → Prop
  | spend i => t i ≠ none
  | create i c => t i = none ∧ ∀ j, t j ≠ some c

/-- Signed change in the count: `-1` per spend, `+1` per create. -/
def delta : Op ι Coin → ℤ
  | spend _ => -1
  | create _ _ => 1

end Op

theorem count_apply {t : Table ι Coin} {o : Op ι Coin} (h : o.Allowed t) :
    (count (o.apply t) : ℤ) = count t + o.delta := by
  cases o with
  | spend i =>
    simp only [Op.Allowed] at h
    have hu := count_update t i none
    simp only [Op.apply, Op.delta]
    cases ht : t i with
    | none => exact absurd ht h
    | some c =>
      rw [ht] at hu
      simp only [occ] at hu
      omega
  | create i c =>
    simp only [Op.Allowed] at h
    have hu := count_update t i (some c)
    rw [h.1] at hu
    simp only [Op.apply, Op.delta]
    simp only [occ] at hu
    omega

theorem excl_apply {t : Table ι Coin} {o : Op ι Coin} (hx : Excl t) (h : o.Allowed t) :
    Excl (o.apply t) := by
  cases o with
  | spend i => exact excl_spend hx i
  | create i c =>
    simp only [Op.Allowed] at h
    exact excl_create hx i c h.2

/-- A sequence of edits, each allowed at the moment it is applied. -/
def Run : Table ι Coin → List (Op ι Coin) → Prop
  | _, [] => True
  | t, o :: os => o.Allowed t ∧ Run (o.apply t) os

/-- Apply a sequence of edits. -/
def applyAll : Table ι Coin → List (Op ι Coin) → Table ι Coin
  | t, [] => t
  | t, o :: os => applyAll (o.apply t) os

/-- **T3.** Over a valid run the count moves by the sum of the deltas. A balanced transaction
(`|I| = |O|`, i.e. deltas summing to zero) leaves it unchanged. -/
theorem count_run : ∀ (t : Table ι Coin) (os : List (Op ι Coin)), Run t os →
    (count (applyAll t os) : ℤ) = count t + (os.map Op.delta).sum
  | t, [], _ => by simp [applyAll]
  | t, o :: os, hrun => by
    obtain ⟨h, hr⟩ := hrun
    rw [applyAll, count_run _ os hr, count_apply h, List.map_cons, List.sum_cons]
    ring

/-- **T2.** Exclusivity survives any valid run. -/
theorem excl_run : ∀ (t : Table ι Coin) (os : List (Op ι Coin)), Excl t → Run t os →
    Excl (applyAll t os)
  | t, [], hx, _ => hx
  | t, o :: os, hx, hrun => by
    obtain ⟨h, hr⟩ := hrun
    exact excl_run _ os (excl_apply hx h) hr

/-- A block's two strands form one table indexed by `ι ⊕ ι`; its count is the sum of the two
strands' counts, so per-block conservation is T3 applied to that table. -/
theorem count_pair (t : Table (ι ⊕ ι) Coin) :
    count t = count (fun i => t (Sum.inl i)) + count (fun i => t (Sum.inr i)) := by
  simp only [count, Fintype.sum_sum_type]

/-! ## T9: adoption -/

/-- A strand's total is its main count plus its adopted trees' counts. Adopting a retiring
tree adds exactly that tree's count: nothing is created or lost. -/
theorem adopt_conserves (main retiring : ℕ) (adopted : List ℕ) :
    main + (retiring :: adopted).sum = (main + adopted.sum) + retiring := by
  rw [List.sum_cons]; ring

end Weave.Slots
