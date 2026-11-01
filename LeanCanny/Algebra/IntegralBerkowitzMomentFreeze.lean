/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralBerkowitzBlockMoment
/-! # Freeze one coefficient algebra before evaluating its trailing moment -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralBerkowitzMomentFreezeBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open IntegralBerkowitzBlockBits
set_option backward.isDefEq.respectTransparency false

noncomputable def freeze (S : Source) (c : List Bool) : Source where
  dimension _ := S.dimension c
  rank _ := S.rank c
  carrier _ := S.carrier c
  ring _ := S.ring c
  nontrivial _ := S.nontrivial c
  basis _ := S.basis c
  matrix _ := S.matrix c
  modulus _ := S.modulus c
  modulus_ne_zero _ := S.modulus_ne_zero c
  coefficient _ := 0
  basisRow _ := ⟨0, S.rank_pos c⟩
  basisCol _ := ⟨0, S.rank_pos c⟩

noncomputable def atMoment (S : Source) (r t s u : ℕ) : List Bool := by
  let := S.ring []
  let v := s / (S.dimension [] + 1)
  let d := S.dimension [] - v - 1
  let row := fun j : Fin d => S.matrix [] ⟨v, by have := j.isLt; dsimp only [d] at this; omega⟩
    ⟨v + 1 + j.val, by have := j.isLt; dsimp only [d] at this; omega⟩
  let col := fun i : Fin d => S.matrix [] ⟨v + 1 + i.val, by have := i.isLt; dsimp only [d] at this; omega⟩
    ⟨v, by have := i.isLt; dsimp only [d] at this; omega⟩
  let mat := fun i j : Fin d => S.matrix []
    ⟨v + 1 + i.val, by have := i.isLt; dsimp only [d] at this; omega⟩
    ⟨v + 1 + j.val, by have := j.isLt; dsimp only [d] at this; omega⟩
  exact residueBits ((Algebra.leftMulMatrix (S.basis [])
    (borderMoment row col mat (u % (S.dimension [] + 1) - (s % (S.dimension [] + 1) + 1)))
    ⟨r % S.rank [], Nat.mod_lt _ (S.rank_pos [])⟩
    ⟨t % S.rank [], Nat.mod_lt _ (S.rank_pos [])⟩ : ℤ) : ZMod (S.modulus []))

theorem value_freeze_point (S : Source) (p : List Bool) :
    (momentFamily S).value p = (momentFamily (freeze S (original p))).value p := rfl

theorem value_freeze (S : Source) (p : List Bool) :
    (momentFamily S).value p = atMoment (freeze S (original p))
      (Nat.fromBitsLE (basisRowCode p)) (Nat.fromBitsLE (basisColCode p))
      (Nat.fromBitsLE (MatrixMoment.EntryBits.rowIndex p)) (Nat.fromBitsLE (MatrixMoment.EntryBits.colIndex p)) := rfl

end LeanCanny.Algebra.IntegralBerkowitzMomentFreezeBits
