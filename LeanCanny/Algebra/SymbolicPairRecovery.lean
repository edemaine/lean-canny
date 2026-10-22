/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.SymbolicFixedTableEntrySpace
public import LeanCanny.Algebra.SubresultantAccessFP
public import LeanCanny.Algebra.CoefficientMinorSpace

/-! # Supplied-order symbolic pair recovery

Linear inputs use their actual coefficients. Other inputs use the first
subresultant, with explicit supplied orders and zero outside its interior range.
-/

@[expose] public section
namespace LeanCanny.Algebra.SymbolicPairRecovery
open Polynomial SymbolicScaledSquarefree
open scoped Classical

noncomputable def subresultantCoefficient (p q : Polynomial Coefficient) (c m n r : ℕ) :
    Polynomial Coefficient :=
  (Subresultant.polynomial (shiftFamily p c) (q.map C) m n 1).coeff r

noncomputable def coordinateCoefficient (p q : Polynomial Coefficient) (c m n r : ℕ) :
    Polynomial Coefficient :=
  if n = 1 then C (q.coeff r) else if m = 1 then (shiftFamily p c).coeff r
    else subresultantCoefficient p q c m n r

lemma coordinateCoefficient_eq (p q : Polynomial Coefficient) (c r : ℕ) :
    coordinateCoefficient p q c p.natDegree q.natDegree r =
      LeanCanny.Algebra.coordinateCoefficient p q c r := rfl

lemma subresultantCoefficient_eq_minor (p q : Polynomial Coefficient) (c m n r : ℕ)
    (hm : 1 < m) (hn : 1 < n) (hr : r ≤ 1) :
    subresultantCoefficient p q c m n r =
      (Subresultant.minor (shiftFamily p c) (q.map C) m n 1 r).det := by
  rw [subresultantCoefficient, Subresultant.coeff, ite_eq_left ⟨hm, hn, hr⟩]

lemma subresultantCoefficient_zero (p q : Polynomial Coefficient) (c m n r : ℕ)
    (h : ¬ (1 < m ∧ 1 < n ∧ r ≤ 1)) : subresultantCoefficient p q c m n r = 0 := by
  rw [subresultantCoefficient, Subresultant.coeff, ite_eq_right h]

end LeanCanny.Algebra.SymbolicPairRecovery
