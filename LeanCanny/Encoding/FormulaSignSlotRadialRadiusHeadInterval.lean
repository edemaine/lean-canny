/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialRadiusHeadEvaluation
public import LeanCanny.Algebra.SingleRootSignCount
/-! # Exact open-radius interval tests for actual selected radial heads

The two ordinary Tarski queries use Y*(b-Y) and its square. Endpoints are
excluded automatically, including repeated roots. No infinitesimal is used.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialRadiusHeadInterval
open LeanCanny.Algebra LeanCanny.Connectivity Polynomial Set
open FormulaSignSlotCenteredRadialGraph
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def window (b : ℝ) : ℝ[X] := X*(C b-X)
private theorem window_positive (b r : ℝ) (hb : 0<b) :
    SignType.sign ((window b).eval r)=SignType.pos ↔ r∈Ioo 0 b := by
  rw [show SignType.pos=(1 : SignType) from rfl,sign_eq_one_iff]
  simp only [window,Polynomial.eval_mul,Polynomial.eval_X,Polynomial.eval_sub,Polynomial.eval_C,mem_Ioo]
  constructor
  · intro H
    rcases mul_pos_iff.mp H with H|H
    · exact ⟨H.1,by linarith [H.2]⟩
    · exfalso
      linarith [H.1,H.2]
  · rintro ⟨H0,H1⟩
    exact mul_pos H0 (sub_pos.mpr H1)

private theorem empty_iff (p : ℝ[X]) (hp : p≠0) (b : ℝ) (hb : 0<b) :
    (∀ r,p.eval r=0 → r∉Ioo 0 b) ↔
      RootSignQueries.tarskiQuery p ((window b)^2)+RootSignQueries.tarskiQuery p (window b)=0 := by
  have HZ : RootSignQueries.singleSignCount p (window b) SignType.pos=0 ↔
      ∀r∈p.roots.toFinset,r∉Ioo 0 b := by
    rw [RootSignQueries.singleSignCount,Finset.card_eq_zero,Finset.filter_eq_empty_iff]
    simp only [window_positive b _ hb]
  have HRoots : (∀r∈p.roots.toFinset,r∉Ioo 0 b) ↔ ∀r,p.eval r=0 → r∉Ioo 0 b := by
    simp only [Multiset.mem_toFinset,Polynomial.mem_roots hp,Polynomial.IsRoot]
  have HC := RootSignQueries.singleSignCount_positive p (window b)
  rw [←HRoots,←HZ]
  omega

noncomputable def specialized (c : List Bool) (a : Fin (d (pairFst c)) → ℝ) (tau eta : ℕ) :=
  (FormulaSignSlotRadialRadiusHeadEvaluation.radiusPolynomial c tau eta).map
    (MvPolynomial.eval₂Hom (Int.castRingHom ℝ) a)

theorem leading_empty_iff (c : List Bool) (a : Fin (d (pairFst c)) → ℝ) (tau D : ℕ)
    (H : FormulaSignSlotRadialCenterSelection.Guards c a tau D) (b : ℝ) (hb : 0<b) :
    (∀r,(FormulaSignSlotRadialCenterSquarefreeSelection.coordinate c a).leadingCoeff.eval r=0 → r∉Ioo 0 b) ↔
      RootSignQueries.tarskiQuery (specialized c a tau D) ((window b)^2)+
        RootSignQueries.tarskiQuery (specialized c a tau D) (window b)=0 := by
  have HE : specialized c a tau D=(FormulaSignSlotRadialCenterSquarefreeSelection.coordinate c a).leadingCoeff :=
    FormulaSignSlotRadialRadiusHeadEvaluation.leading c a tau D H
  rw [HE]
  apply empty_iff
  · exact Polynomial.leadingCoeff_ne_zero.mpr (FormulaSignSlotRadialParameterEliminant.coordinate_ne_zero _ _ _)
  · exact hb

theorem trailing_empty_iff (c : List Bool) (a : Fin (d (pairFst c)) → ℝ) (tau D ell : ℕ)
    (H : FormulaSignSlotRadialCenterTrailingSelection.Guards c a tau D ell) (b : ℝ) (hb : 0<b) :
    (∀r,(FormulaSignSlotRadialCenterSquarefreeSelection.coordinate c a).trailingCoeff.eval r=0 → r∉Ioo 0 b) ↔
      RootSignQueries.tarskiQuery (specialized c a tau ell) ((window b)^2)+
        RootSignQueries.tarskiQuery (specialized c a tau ell) (window b)=0 := by
  have HE : specialized c a tau ell=(FormulaSignSlotRadialCenterSquarefreeSelection.coordinate c a).trailingCoeff :=
    FormulaSignSlotRadialRadiusHeadEvaluation.trailing c a tau D ell H
  rw [HE]
  apply empty_iff
  · exact Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr
      (FormulaSignSlotRadialParameterEliminant.coordinate_ne_zero _ _ _)
  · exact hb

end LeanCanny.Encoding.FormulaSignSlotRadialRadiusHeadInterval
