/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialJointSelectionStratum
public import LeanCanny.Encoding.FormulaSignSlotRadialCenterTrailingSelection
/-! # The actual margin trailing choice persists on the coefficient stratum -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialJointSelectionStratum
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Connectivity LeanCanny.Computation Set
open FormulaSignSlotRadialJointCoefficientCatalogue
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem trailing_guards_iff_of_signs (c : List Bool) (j : ℕ)
    (hj : j<FormulaSignSlotRadialJointLayout.spatialCount c) (x y : Point c) (HS : Signs c x y)
    (tau D ell : ℕ) :
    FormulaSignSlotRadialCenterTrailingSelection.Guards (coordinateContext c j) (center c j x) tau D ell ↔
      FormulaSignSlotRadialCenterTrailingSelection.Guards (coordinateContext c j) (center c j y) tau D ell := by
  have HB : FormulaSignSlotRadialCenterSelection.bound (coordinateContext c j)=degree c := by
    apply FormulaSignSlotRadialEliminantRootProfiles.degree_eq
    simp only [coordinateContext,FormulaSignSlotRadialCoordinatePacket.root,base,pairFst_pair]
  have zeroes (u v : Point c) (HV : Signs c u v) (s : ℕ) (hs : s<limit c) (t : ℕ) (ht : t<limit c)
      (r : ℕ) (hr : r<limit c) :
      FormulaSignSlotRadialCenterSelection.Zero (coordinateContext c j) (center c j u) s t r ↔
        FormulaSignSlotRadialCenterSelection.Zero (coordinateContext c j) (center c j v) s t r :=
    coefficient_zero_iff c u v HV j s t r hj hs ht hr
  have transfer (u v : Point c) (HV : Signs c u v) :
      FormulaSignSlotRadialCenterTrailingSelection.Guards (coordinateContext c j) (center c j u) tau D ell →
        FormulaSignSlotRadialCenterTrailingSelection.Guards (coordinateContext c j) (center c j v) tau D ell := by
    rintro ⟨HG,HL,HB0,HN⟩
    have Htau := HG.1
    have HD := HG.2.1
    have HT0 : tau<limit c := by unfold limit; omega
    have HE0 : ell<limit c := by unfold limit; omega
    refine ⟨(guards_iff_of_signs c j hj u v HV tau D).mp HG,HL,?_,?_⟩
    · intro t ht r hr
      apply (zeroes u v HV tau HT0 t (by unfold limit; omega) r (by unfold limit; omega)).mp
      exact HB0 t ht r hr
    · intro HZ
      apply HN
      intro r hr
      exact (zeroes u v HV tau HT0 ell HE0 r (by unfold limit; omega)).mpr (HZ r hr)
  exact ⟨transfer x y HS,transfer y x (fun i => (HS i).symm)⟩

private theorem continuous_integer_eval {ι : Type*} (p : MvPolynomial ι ℤ) :
    Continuous (fun x : ι → ℝ => p.eval₂ (Int.castRingHom ℝ) x) := by
  simpa only [MvPolynomial.eval₂_eq_eval_map] using (p.map (Int.castRingHom ℝ)).continuous_eval

theorem trailing_guards_iff_on_equation_stratum (c : List Bool) (j : ℕ)
    (hj : j<FormulaSignSlotRadialJointLayout.spatialCount c) (K : ℕ)
    {s : Set (Point c)} (HS : IsPreconnected s)
    (HEq : ∀ z∈s, ∃ w : ℝ, SquareFeatureProduct.equation
      (List.ofFn (fun i : Fin (count c) => featureValue c i.val z)) K w=0)
    {x y : Point c} (HX : x∈s) (HY : y∈s) (tau D ell : ℕ) :
    FormulaSignSlotRadialCenterTrailingSelection.Guards (coordinateContext c j) (center c j x) tau D ell ↔
      FormulaSignSlotRadialCenterTrailingSelection.Guards (coordinateContext c j) (center c j y) tau D ell := by
  apply trailing_guards_iff_of_signs c j hj x y ?_ tau D ell
  intro i
  exact SquareFeatureSignStratum.sign_eq_on_equation_stratum (count c)
    (fun i z => featureValue c i.val z) (fun i => continuous_integer_eval (family.feature c i.val)) K HS HEq HX HY i

end LeanCanny.Encoding.FormulaSignSlotRadialJointSelectionStratum
