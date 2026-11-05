/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialEliminantCoefficientModel
/-! # A coefficient query retains every source parameter exponent -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialEliminantCoefficientQuery
open LeanCanny.Algebra LeanCanny.Connectivity MvPolynomial
open FormulaSignSlotCenteredRadialGraph
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def spatial (c : List Bool) (x : Fin (FormulaSignSlotRadialFormalInput.dimension c) →₀ ℕ) :
    Fin (FormulaSignSlotRadialFormalInput.spatial c) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => x (FormulaSignSlotRadialFormalInput.spatialIndex c i))
noncomputable def center (c : List Bool) (x : Fin (FormulaSignSlotRadialFormalInput.dimension c) →₀ ℕ) :
    Fin (d c) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => x (FormulaSignSlotRadialFormalInput.formalCenterIndex c i))
noncomputable def radius (c : List Bool) (x : Fin (FormulaSignSlotRadialFormalInput.dimension c) →₀ ℕ) :=
  x (FormulaSignSlotRadialFormalInput.formalRadiusIndex c)
noncomputable def homogeneous (c : List Bool) (x : Fin (FormulaSignSlotRadialFormalInput.dimension c) →₀ ℕ) (h : ℕ) :
    Option (Fin (FormulaSignSlotRadialFormalInput.spatial c)) →₀ ℕ := (spatial c x).optionElim h

private theorem join_left {σ τ : Type*} (e : σ →₀ ℕ) (f : τ →₀ ℕ) :
    PartialCoefficient.leftExponent (NestedPolynomial.joinExponent e f) = e :=
  congrArg Prod.fst (Finsupp.sumFinsuppAddEquivProdFinsupp.apply_symm_apply (e, f))
private theorem join_right {σ τ : Type*} (e : σ →₀ ℕ) (f : τ →₀ ℕ) :
    PartialCoefficient.rightExponent (NestedPolynomial.joinExponent e f) = f :=
  congrArg Prod.snd (Finsupp.sumFinsuppAddEquivProdFinsupp.apply_symm_apply (e, f))

theorem reconstruct (c : List Bool) (x : Fin (FormulaSignSlotRadialFormalInput.dimension c) →₀ ℕ) :
    FormulaSignSlotRadialEliminantSource.exponent c (spatial c x) (radius c x) (center c x) = x := by
  ext i
  obtain ⟨a, rfl⟩ := (FormulaSignSlotRadialEliminantSource.layout c).surjective i
  rw [FormulaSignSlotRadialEliminantSource.exponent, Finsupp.mapDomain_equiv_apply,
    Equiv.symm_apply_apply]
  cases a with
  | inl a =>
    rw [← PartialCoefficient.leftExponent_apply, join_left]
    refine Fin.cases ?_ (fun j => ?_) a
    · rw [IntegerParameterFlatten.joinExponent_zero]
      rfl
    · rw [IntegerParameterFlatten.joinExponent_succ]
      rfl
  | inr a =>
    rw [← PartialCoefficient.rightExponent_apply, join_right]
    rfl

theorem dense (c : List Bool) (j : Fin (FormulaSignSlotRadialFormalInput.spatial c))
    (x : Fin (FormulaSignSlotRadialFormalInput.dimension c) →₀ ℕ) :
    FormulaSignSlotRadialEliminantCoefficientModel.dense c j (spatial c x) (radius c x) (center c x) =
      (pderiv (FormulaSignSlotRadialFormalInput.spatialIndex c j)
        ((FormulaSignSlotRadialFormalInput.polynomial c) ^ 2)).coeff x := by
  rw [FormulaSignSlotRadialEliminantCoefficientModel.dense, reconstruct]

private theorem parameters_zero_generic {m a : ℕ} (x : Fin (m + (a + 1)) →₀ ℕ) :
    x (Fin.natAdd m (Fin.last a)) = 0 ∧
        (Finsupp.equivFunOnFinite.symm (fun i : Fin a => x (Fin.natAdd m (Fin.castAdd 1 i))) : Fin a →₀ ℕ) = 0 ↔
      ∀ i, m ≤ i.val → x i = 0 := by
  constructor
  · rintro ⟨hr, hv⟩ i hi
    obtain ⟨u, rfl⟩ := (finSumFinEquiv : Sum (Fin m) (Fin (a + 1)) ≃ Fin (m + (a + 1))).surjective i
    cases u with
    | inl j => have H := j.isLt; change m ≤ j.val at hi; omega
    | inr j =>
      refine Fin.lastCases ?_ (fun v => ?_) j
      · exact hr
      · exact congrArg (fun f : Fin a →₀ ℕ => f v) hv
  · intro H
    constructor
    · exact H _ (by change m ≤ m + a; omega)
    · ext i
      exact H _ (by change m ≤ m + i.val; omega)

theorem parameters_zero (c : List Bool) (x : Fin (FormulaSignSlotRadialFormalInput.dimension c) →₀ ℕ) :
    radius c x = 0 ∧ center c x = 0 ↔
      ∀ i, FormulaSignSlotRadialFormalInput.spatial c ≤ i.val → x i = 0 :=
  parameters_zero_generic x

end LeanCanny.Encoding.FormulaSignSlotRadialEliminantCoefficientQuery
