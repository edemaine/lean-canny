/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.BerkowitzPolynomialSpace

/-! # Conditional polynomial determinant families

The selected family supplies its dimension, modulus, coefficient degree, and
matrix together. Entry requests select by their original matrix context.
This supports square-free leaf matrices and internal resultant matrices in
one recursive determinant task family.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace LeanCanny.Algebra.BerkowitzPolynomial
open LeanCanny.Encoding LeanCanny.Computation

namespace ModularFamily

noncomputable def branchMatrix (L R : ModularFamily) (c : List Bool) (choice : Bool) :
    Matrix (Fin (if choice then L.dimension c else R.dimension c))
      (Fin (if choice then L.dimension c else R.dimension c))
      (Polynomial (ZMod (if choice then L.modulus c else R.modulus c))) :=
  Bool.rec (motive := fun b =>
    Matrix (Fin (if b then L.dimension c else R.dimension c))
      (Fin (if b then L.dimension c else R.dimension c))
      (Polynomial (ZMod (if b then L.modulus c else R.modulus c)))) (R.matrix c) (L.matrix c) choice

noncomputable def branch (select : List Bool → Bool) (L R : ModularFamily) : ModularFamily where
  dimension c := if select c then L.dimension c else R.dimension c
  modulus c := if select c then L.modulus c else R.modulus c
  degree c := if select c then L.degree c else R.degree c
  matrix c := branchMatrix L R c (select c)
  modulus_ne_zero c := by
    split_ifs
    · exact L.modulus_ne_zero c
    · exact R.modulus_ne_zero c

private theorem branchMatrix_value (L R : ModularFamily) (c : List Bool) (choice : Bool) :
    MatrixPower.residueBits (m := if choice then L.modulus c else R.modulus c)
      ((branchMatrix L R c choice).det.coeff (if choice then L.degree c else R.degree c)) =
      if choice then L.value c else R.value c := by
  cases choice <;> rfl

theorem branch_value (select : List Bool → Bool) (L R : ModularFamily) (c : List Bool) :
    (branch select L R).value c = if select c then L.value c else R.value c :=
  branchMatrix_value L R c (select c)

end ModularFamily

namespace ModularAccess

private theorem branchMatrix_entry {L R : ModularFamily} (a : ModularAccess L) (b : ModularAccess R)
    (c : List Bool) (d : ℕ) (choice : Bool)
    (i j : Fin (if choice then L.dimension c else R.dimension c)) :
    (if choice then a.entry (pair c (pair (BinaryNatCode.encode i.val) (pair (BinaryNatCode.encode j.val) (BinaryNatCode.encode d))))
      else b.entry (pair c (pair (BinaryNatCode.encode i.val) (pair (BinaryNatCode.encode j.val) (BinaryNatCode.encode d))))) =
      MatrixPower.residueBits (m := if choice then L.modulus c else R.modulus c)
        (((ModularFamily.branchMatrix L R c choice) i j).coeff d) := by
  cases choice with
  | false => exact b.entry_eq c i j d
  | true => exact a.entry_eq c i j d

noncomputable def branch {L R : ModularFamily} (select : List Bool → Bool)
    (a : ModularAccess L) (b : ModularAccess R) : ModularAccess (ModularFamily.branch select L R) where
  dimension c := if select c then a.dimension c else b.dimension c
  modulus c := if select c then a.modulus c else b.modulus c
  degree c := if select c then a.degree c else b.degree c
  entry p := if select (pairFst p) then a.entry p else b.entry p
  dimension_eq c := by
    cases hs : select c <;> simp only [ModularFamily.branch, hs, Bool.false_eq_true, ite_false, ite_true,
      a.dimension_eq, b.dimension_eq]
  modulus_eq c := by
    cases hs : select c <;> simp only [ModularFamily.branch, hs, Bool.false_eq_true, ite_false, ite_true,
      a.modulus_eq, b.modulus_eq]
  degree_eq c := by
    cases hs : select c <;> simp only [ModularFamily.branch, hs, Bool.false_eq_true, ite_false, ite_true,
      a.degree_eq, b.degree_eq]
  entry_eq := by
    intro c i j d
    simp only [pairFst_pair]
    exact branchMatrix_entry a b c d (select c) i j

theorem branch_controls {L R : ModularFamily} (select : List Bool → Bool)
    (a : ModularAccess L) (b : ModularAccess R) (hs : (fun c => [select c]) ∈ FP)
    (ha : a.ControlsPolyTime) (hb : b.ControlsPolyTime) : (branch select a b).ControlsPolyTime :=
  ⟨(flag_computable hs).ite' ha.dimension hb.dimension,
    (flag_computable hs).ite' ha.modulus hb.modulus, (flag_computable hs).ite' ha.degree hb.degree⟩

end ModularAccess
end LeanCanny.Algebra.BerkowitzPolynomial
