import Mathlib

/-!
# Binding is not well-formedness (proofs.md I3)

* Any digest that compresses must collide, so binding can only ever be computational.
* In a group, every value is the sum of a multiset of every size, so the statement
  "some multiset of size `n` has digest `d`" is vacuous. Well-formedness must instead mean
  "a valid history producing this certificate is known" — a proof-of-knowledge statement,
  which is why the scheme carries a folding proof.
-/

namespace Weave.Digest

/-- Pigeonhole: a compressing digest has collisions. -/
theorem compressing_digest_collides {X G : Type*} [Fintype X] [Fintype G] (D : X → G)
    (h : Fintype.card G < Fintype.card X) : ∃ x y, x ≠ y ∧ D x = D y :=
  Fintype.exists_ne_map_eq_of_card_lt D h

/-- Every group element is the sum of `n + 1` elements, for every `n`. -/
theorem every_digest_has_every_size {G : Type*} [AddCommGroup G] (d : G) (n : ℕ) :
    ∃ f : Fin (n + 1) → G, ∑ i, f i = d :=
  ⟨fun i => if i = 0 then d else 0, by simp⟩

end Weave.Digest
