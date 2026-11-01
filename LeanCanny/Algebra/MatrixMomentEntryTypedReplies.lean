/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.MatrixMomentEntryControllerLocal
/-! # Local moment replies follow from finite block replies -/
@[expose] public section
namespace LeanCanny.Algebra.MatrixMoment.EntryBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
set_option backward.isDefEq.respectTransparency false

theorem repliesAt_of_typed (a : Access) (input rowTask columnTask matrixTask answer : List Bool → List Bool)
    (q c : List Bool) (d : ℕ) (i j : Fin (d + 2))
    (hd : a.dimension c = BinaryNatCode.encode d)
    (hi : input q = pair c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))
    (hr : ∀ v : Fin d, answer (rowTask (pair c (BinaryNatCode.encode v.val))) = a.row (pair c (BinaryNatCode.encode v.val)))
    (hc : ∀ v : Fin d, answer (columnTask (pair c (BinaryNatCode.encode v.val))) = a.column (pair c (BinaryNatCode.encode v.val)))
    (he : ∀ v w : Fin d, answer (matrixTask (pair c (pair (BinaryNatCode.encode v.val) (BinaryNatCode.encode w.val)))) =
      a.entry (pair c (pair (BinaryNatCode.encode v.val) (BinaryNatCode.encode w.val)))) :
    RepliesAt a input rowTask columnTask matrixTask answer q := by
  have HU (x : Unit) : x = () := Subsingleton.elim _ _
  have HL (v : Fin d) : BinaryNatCode.encode (v.val + 1) ≠ BinaryNatCode.encode (d + 1) := by
    intro h
    have H := BinaryNatCode.encode_injective h
    have HV := v.isLt
    omega
  obtain ⟨p, rfl⟩ := (vertexEquiv d).surjective i
  obtain ⟨z, rfl⟩ := (vertexEquiv d).surjective j
  rcases p with ⟨⟩ | (v | ⟨⟩) <;> rcases z with ⟨⟩ | (w | ⟨⟩)
  all_goals simp [RepliesAt, hi, rowIndex, colIndex, sinkIndex, hd, HU, HL, Controller.pred_code, hr, hc, he]

end LeanCanny.Algebra.MatrixMoment.EntryBits
