/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.FrozenCoordinateOrdering
/-! # Frozen-first ordering is literally identity on an initial segment

The increasing frozen and complementary enumerations coincide with the
ordinary first and last coordinate blocks. No permutation of the spatial
source is needed for a deterministic prefix-freezing trace.
-/
@[expose] public section
namespace LeanCanny.Geometry.FrozenCoordinateOrdering
open scoped Classical
variable {N : ℕ}

theorem permutation_eq_refl (s : Finset (Fin N))
    (hs : ∀i,i∈s↔i.val<s.card) : permutation s=Equiv.refl (Fin N):=by
  have HN : s.card≤N:=by simpa only [Fintype.card_fin] using s.card_le_univ
  let left : Fin s.card→Fin N:=fun i=>⟨i.val,lt_of_lt_of_le i.isLt HN⟩
  have HL : left=(s.orderEmbOfFin rfl : Fin s.card→Fin N):=
    Finset.orderEmbOfFin_unique rfl (fun i=>(hs (left i)).mpr i.isLt) (fun _ _ h=>h)
  have HC : sᶜ.card=N-s.card:=by rw [Finset.card_compl,Fintype.card_fin]
  let right : Fin (N-s.card)→Fin N:=fun i=>⟨s.card+i.val,by have H:=i.isLt; omega⟩
  have HR : right=(sᶜ.orderEmbOfFin HC : Fin (N-s.card)→Fin N):=by
    apply Finset.orderEmbOfFin_unique HC
    · intro i
      apply Finset.mem_compl.mpr
      intro hi
      have HH:=(hs (right i)).mp hi
      change s.card+i.val<s.card at HH
      omega
    · intro i j hij
      change s.card+i.val<s.card+j.val
      exact Nat.add_lt_add_left hij s.card
  apply Equiv.ext
  intro i
  obtain ⟨a,rfl⟩:=(flatten s).surjective i
  change permutation s (flatten s a)=flatten s a
  rw [permutation_flatten]
  cases a with
  | inl j=>
    change s.orderEmbOfFin rfl j=flatten s (.inl j)
    exact (congrFun HL j).symm.trans (Fin.ext rfl)
  | inr j=>
    change sᶜ.orderEmbOfFin HC j=flatten s (.inr j)
    exact (congrFun HR j).symm.trans (Fin.ext rfl)

end LeanCanny.Geometry.FrozenCoordinateOrdering
