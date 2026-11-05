/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialFormalInput
public import LeanCanny.Algebra.IntegerParameterCoefficient
public import LeanCanny.Algebra.NestedPolynomialCoefficient
/-! # The actual formal radial source supplies its spatial derivative coefficients

Radius and center coefficients are extracted without specializing either block.
The integer source remains the original native term and its original layout.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialEliminantSource
open ETR LeanCanny.Algebra LeanCanny.Connectivity MvPolynomial
open FormulaSignSlotCenteredRadialGraph
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def variableLayout (m a : ℕ) :
    Sum (Fin (m + 1)) (Fin a) ≃ Sum (Fin m) (Sum (Fin a) Unit) where
  toFun := Sum.elim (fun i => Fin.cases (.inr (.inr ())) Sum.inl i) (fun i => .inr (.inl i))
  invFun := Sum.elim (fun i => .inl i.succ) (Sum.elim Sum.inr (fun _ => .inl 0))
  left_inv i := by
    cases i with
    | inl i => exact Fin.cases rfl (fun _ => rfl) i
    | inr i => rfl
  right_inv i := by
    rcases i with i | (i | i)
    · rfl
    · rfl
    · cases i; rfl

private theorem flatten_diagram {m a : ℕ}
    (p : MvPolynomial (Fin m) (Polynomial (MvPolynomial (Fin a) ℤ))) :
    rename (variableLayout m a) (NestedPolynomial.flatten (IntegerParameterFlatten.flatten p)) =
      eval₂Hom (Polynomial.eval₂RingHom
        (rename (R := ℤ) (fun i : Fin a => (Sum.inr (Sum.inl i) : Sum (Fin m) (Sum (Fin a) Unit)))).toRingHom
        (X (.inr (.inr ())))) (fun i => X (.inl i)) p := by
  have H : (rename (variableLayout m a)).toRingHom.comp
      (NestedPolynomial.flatten.comp IntegerParameterFlatten.flatten) =
      eval₂Hom (Polynomial.eval₂RingHom
        (rename (R := ℤ) (fun i : Fin a => (Sum.inr (Sum.inl i) : Sum (Fin m) (Sum (Fin a) Unit)))).toRingHom
        (X (.inr (.inr ())))) (fun i => X (.inl i)) := by
    apply MvPolynomial.ringHom_ext'
    · apply Polynomial.ringHom_ext'
      · apply MvPolynomial.ringHom_ext'
        · exact Subsingleton.elim _ _
        · intro i
          simp [IntegerParameterFlatten.flatten, IntegerParameterFlatten.coefficientMap,
            variableLayout]
      · simp [IntegerParameterFlatten.flatten, IntegerParameterFlatten.coefficientMap,
          variableLayout]
    · intro i
      simp [IntegerParameterFlatten.flatten, variableLayout]
  exact congrArg (fun f => f p) H

noncomputable def layout (c : List Bool) :=
  (variableLayout (FormulaSignSlotRadialFormalInput.spatial c) (d c)).trans (FormulaSignSlotRadialFormalInput.layout c)

noncomputable def flatten (c : List Bool) :
    MvPolynomial (Fin (FormulaSignSlotRadialFormalInput.spatial c)) (FormulaSignSlotRadialFormalCenter.Radius c) →+*
      MvPolynomial (Fin (FormulaSignSlotRadialFormalInput.dimension c)) ℤ :=
  (rename (layout c)).toRingHom.comp (NestedPolynomial.flatten.comp IntegerParameterFlatten.flatten)

theorem flatten_eq (c : List Bool) (p : MvPolynomial (Fin (FormulaSignSlotRadialFormalInput.spatial c)) (FormulaSignSlotRadialFormalCenter.Radius c)) :
    flatten c p = rename (FormulaSignSlotRadialFormalInput.layout c) (FormulaSignSlotRadialFormalBounds.flatten c p) := by
  dsimp only [FormulaSignSlotRadialFormalInput.spatial] at p ⊢
  change rename (FormulaSignSlotRadialFormalInput.layout c ∘
    variableLayout (N c + d c + 1) (d c))
    (NestedPolynomial.flatten (IntegerParameterFlatten.flatten p)) = _
  rw [← rename_rename, flatten_diagram]
  rfl

noncomputable def exponent (c : List Bool) (e : Fin (FormulaSignSlotRadialFormalInput.spatial c) →₀ ℕ)
    (r : ℕ) (v : Fin (d c) →₀ ℕ) : Fin (FormulaSignSlotRadialFormalInput.dimension c) →₀ ℕ :=
  (NestedPolynomial.joinExponent (IntegerParameterFlatten.joinExponent r e) v).mapDomain (layout c)

theorem coefficient (c : List Bool) (p : MvPolynomial (Fin (FormulaSignSlotRadialFormalInput.spatial c)) (FormulaSignSlotRadialFormalCenter.Radius c))
    (e : Fin (FormulaSignSlotRadialFormalInput.spatial c) →₀ ℕ) (r : ℕ) (v : Fin (d c) →₀ ℕ) :
    (flatten c p).coeff (exponent c e r v) = ((p.coeff e).coeff r).coeff v := by
  change (rename (layout c) (NestedPolynomial.flatten (IntegerParameterFlatten.flatten p))).coeff
    ((NestedPolynomial.joinExponent (IntegerParameterFlatten.joinExponent r e) v).mapDomain (layout c)) = _
  rw [coeff_rename_mapDomain _ (layout c).injective,
    NestedPolynomial.coefficient, IntegerParameterFlatten.coeff_flatten]
  have HT : IntegerParameterFlatten.tailExponent (IntegerParameterFlatten.joinExponent r e) = e := by
    ext i
    exact IntegerParameterFlatten.joinExponent_succ r e i
  rw [HT, IntegerParameterFlatten.joinExponent_zero]

theorem derivative (c : List Bool) (p : MvPolynomial (Fin (FormulaSignSlotRadialFormalInput.spatial c)) (FormulaSignSlotRadialFormalCenter.Radius c))
    (j : Fin (FormulaSignSlotRadialFormalInput.spatial c)) :
    flatten c (pderiv j p) = pderiv (FormulaSignSlotRadialFormalInput.spatialIndex c j) (flatten c p) := by
  change rename (layout c) (NestedPolynomial.flatten (IntegerParameterFlatten.flatten (pderiv j p))) = _
  change rename (layout c) (NestedPolynomial.flatten (IntegerParameterFlatten.flatten (pderiv j p))) =
    pderiv (layout c (.inl j.succ)) (rename (layout c) (NestedPolynomial.flatten (IntegerParameterFlatten.flatten p)))
  rw [IntegerParameterFlatten.flatten_pderiv, NestedPolynomial.flatten_pderiv,
    pderiv_rename (layout c).injective]

theorem source_derivative_coefficient (c : List Bool) (j : Fin (FormulaSignSlotRadialFormalInput.spatial c))
    (e : Fin (FormulaSignSlotRadialFormalInput.spatial c) →₀ ℕ) (r : ℕ) (v : Fin (d c) →₀ ℕ) :
    (pderiv (FormulaSignSlotRadialFormalInput.spatialIndex c j) ((FormulaSignSlotRadialFormalInput.polynomial c) ^ 2)).coeff (exponent c e r v) =
      (((pderiv j ((FormulaSignSlotRadialFormalCenter.polynomial c) ^ 2)).coeff e).coeff r).coeff v := by
  have HF : flatten c (FormulaSignSlotRadialFormalCenter.polynomial c) = FormulaSignSlotRadialFormalInput.polynomial c := flatten_eq c _
  rw [← HF, ← map_pow, ← derivative, coefficient]

end LeanCanny.Encoding.FormulaSignSlotRadialEliminantSource
