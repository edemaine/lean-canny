/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.OriginalFormulaRows
/-! # A native row family in the original or any larger spatial coordinate block -/
@[expose] public section
namespace LeanCanny.Encoding.OriginalFormulaRows
open ETR LeanCanny.Computation LeanCanny.Connectivity LeanCanny.Algebra
open scoped Classical
attribute [local irreducible] pair LeanCanny.Connectivity.Input.field
  ClosedFormulaGateMetadata.dimension ClosedFormulaGateMetadata.count dimension count degree mass term

structure Family where
  arity : List Bool → ℕ
  count : List Bool → ℕ
  degree : List Bool → ℕ
  mass : List Bool → ℕ
  term : List Bool → Term
  term_scope : ∀ q, (term q).arity≤arity (pairFst q)
  degree_bound : ∀ c i,
    ((term (pair c (List.replicate i true))).finitePolynomial (arity c)).totalDegree≤degree c
  mass_bound : ∀ c i,
    MvMass.mass ((term (pair c (List.replicate i true))).finitePolynomial (arity c))≤2^mass c

noncomputable def Family.polynomial (F : Family) (c : List Bool) (i : ℕ) : MvPolynomial (Fin (F.arity c)) ℤ :=
  (F.term (pair c (List.replicate i true))).finitePolynomial (F.arity c)

structure Family.Access (F : Family) : Prop where
  arity : UnaryFn F.arity
  count : UnaryFn F.count
  degree : UnaryFn F.degree
  mass : UnaryFn F.mass
  term : (fun q => (F.term q).toData.toBits) ∈ FP

noncomputable def family (ambient : List Bool → ℕ) (hfit : ∀ c, dimension c≤ambient c) : Family where
  arity := ambient
  count := count
  degree := degree
  mass := mass
  term := term
  term_scope q := (term_scope q).trans (hfit (pairFst q))
  degree_bound c i := polynomial_degree (ambient c) c i
  mass_bound c i := polynomial_mass (ambient c) c i

theorem access (ambient : List Bool → ℕ) (hfit : ∀ c, dimension c≤ambient c)
    (hambient : UnaryFn ambient) : (family ambient hfit).Access := by
  unfold family
  exact ⟨hambient,count_unary,degree_unary,mass_unary,term_FP⟩

noncomputable def original : Family := family dimension (fun _ => le_refl _)
theorem original_access : original.Access := access dimension (fun _ => le_refl _) dimension_unary

theorem padded_polynomial (ambient : List Bool → ℕ) (hfit : ∀ c, dimension c≤ambient c)
    (c : List Bool) (i : ℕ) : (family ambient hfit).polynomial c i=polynomial (ambient c) c i := by
  simp only [Family.polynomial,family,polynomial]

theorem padded_coefficient_bound (ambient : List Bool → ℕ) (hfit : ∀ c, dimension c≤ambient c)
    (c : List Bool) (i : ℕ) (a : Fin (ambient c) →₀ ℕ) :
    (((family ambient hfit).polynomial c i).coeff a).natAbs≤2^mass c := by
  rw [padded_polynomial]
  exact coefficient_bound (ambient c) c i a

theorem eval_retained (ambient : List Bool → ℕ) (hfit : ∀ c, dimension c≤ambient c)
    (c : List Bool) (i : ℕ) (x : Fin (ambient c) → ℝ) (old : Fin (dimension c) → ℝ)
    (hx : ∀ j : Fin (dimension c), x ⟨j.val,j.isLt.trans_le (hfit c)⟩=old j) :
    ((family ambient hfit).polynomial c i).eval₂ (Int.castRingHom ℝ) x=
      (original.polynomial c i).eval₂ (Int.castRingHom ℝ) old := by
  rw [padded_polynomial,eval_polynomial]
  change (term (pair c (List.replicate i true))).eval (Formula.extend x)=
    (polynomial (dimension c) c i).eval₂ (Int.castRingHom ℝ) old
  rw [eval_polynomial]
  apply Term.eval_congr
  intro j hj
  have HJ : j < dimension c := hj.trans_le (by simpa only [pairFst_pair] using term_scope (pair c (List.replicate i true)))
  have HN : j < ambient c := HJ.trans_le (hfit c)
  simp only [Formula.extend,dite_eq_left HJ,dite_eq_left HN]
  exact hx ⟨j,HJ⟩

theorem polynomial_invalid (ambient : List Bool → ℕ) (hfit : ∀ c, dimension c≤ambient c)
    (c : List Bool) (i : ℕ) (hi : count c ≤ i) : (family ambient hfit).polynomial c i=0 := by
  simp only [Family.polynomial,family,term_invalid c i hi,Term.finitePolynomial,MvPolynomial.C_0]
  rfl

end LeanCanny.Encoding.OriginalFormulaRows
