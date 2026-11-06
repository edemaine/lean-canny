/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialRadiusWindowSigns
public import LeanCanny.Encoding.FormulaSignSlotRadialRadiusHeadInterval
/-! # Actual coordinate leading and margin trailing radius intervals from installed signs -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialRadiusWindowInterval
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.Connectivity Polynomial MvPolynomial Set
open scoped Classical
set_option backward.isDefEq.respectTransparency false
private theorem cast_heq {n m : ℕ} (h : n=m) (v : Fin m → ℝ) : HEq (IntegralPolynomialWindowTarski.intervalCastValues h v) v := by cases h; rfl
private theorem map_heq {n m : ℕ} (h : n=m) (p : Polynomial (MvPolynomial (Fin n) ℤ))
    (q : Polynomial (MvPolynomial (Fin m) ℤ)) (hp : HEq p q) (v : Fin n → ℝ) (w : Fin m → ℝ) (hv : HEq v w) :
    p.map (MvPolynomial.eval₂Hom (Int.castRingHom ℝ) v) = q.map (MvPolynomial.eval₂Hom (Int.castRingHom ℝ) w) := by
  cases h
  cases eq_of_heq hp
  cases eq_of_heq hv
  rfl
private theorem radius_context_heq (c d : List Bool) (hc : c=d) (t u e f : ℕ) (ht : t=u) (he : e=f) :
    HEq (FormulaSignSlotRadialRadiusHeadEvaluation.radiusPolynomial c t e)
      (FormulaSignSlotRadialRadiusHeadEvaluation.radiusPolynomial d u f) := by cases hc; cases ht; cases he; rfl
private theorem reader_context (c : List Bool) (t e : ℕ) :
    HEq (FormulaSignSlotRadialRadiusHeadReader.polynomial (FormulaSignSlotRadialRadiusTarskiCatalogue.headContext c t e))
      (FormulaSignSlotRadialRadiusHeadEvaluation.radiusPolynomial c t e) := by
  unfold FormulaSignSlotRadialRadiusHeadReader.polynomial
  exact radius_context_heq _ _ (by simp only [FormulaSignSlotRadialRadiusHeadReader.original,FormulaSignSlotRadialRadiusTarskiCatalogue.headContext,pairFst_pair]) _ _ _ _
    (by simp only [FormulaSignSlotRadialRadiusHeadReader.tau,FormulaSignSlotRadialRadiusTarskiCatalogue.headContext,pairSnd_pair,pairFst_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits])
    (by simp only [FormulaSignSlotRadialRadiusHeadReader.eta,FormulaSignSlotRadialRadiusTarskiCatalogue.headContext,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits])

theorem base_head_eq (c : List Bool) (t e : ℕ) (a : Fin (FormulaSignSlotRadialRadiusWindowSigns.centerCount c) → ℝ) :
    IntegralPolynomialWindowTarski.baseHead FormulaSignSlotRadialRadiusWindowBridge.source FormulaSignSlotRadialRadiusWindowBridge.centers FormulaSignSlotRadialRadiusWindowBridge.dimension (FormulaSignSlotRadialRadiusTarskiCatalogue.headContext c t e) (FormulaSignSlotRadialRadiusWindowSigns.center c t e a) =
      FormulaSignSlotRadialRadiusHeadInterval.specialized c a t e := by
  unfold IntegralPolynomialWindowTarski.baseHead
  rw [FormulaSignSlotRadialRadiusWindowBridge.radius_polynomial]
  exact map_heq (FormulaSignSlotRadialRadiusWindowSigns.centers_eq c t e) _ _ (reader_context c t e) _ _ (cast_heq _ _)

theorem interval_iff (c : List Bool) (b : ℝ) (a : Fin (FormulaSignSlotRadialRadiusWindowSigns.centerCount c) → ℝ)
    (b' : ℝ) (a' : Fin (FormulaSignSlotRadialRadiusWindowSigns.centerCount c) → ℝ) (H : FormulaSignSlotRadialRadiusWindowSigns.Signs c b a b' a')
    (t e : ℕ) (ht : t < FormulaSignSlotRadialRadiusTarskiCatalogue.limit c) (he : e < FormulaSignSlotRadialRadiusTarskiCatalogue.limit c) (hb : 0 < b) (hb' : 0 < b') :
    (∀r,(FormulaSignSlotRadialRadiusHeadInterval.specialized c a t e).eval r=0 → r ∉ Ioo 0 b) ↔
      ∀r,(FormulaSignSlotRadialRadiusHeadInterval.specialized c a' t e).eval r=0 → r ∉ Ioo 0 b' := by
  have HE := IntegralPolynomialWindowTarski.interval_iff_of_signs FormulaSignSlotRadialRadiusWindowBridge.source FormulaSignSlotRadialRadiusWindowBridge.centers FormulaSignSlotRadialRadiusWindowBridge.dimension (FormulaSignSlotRadialRadiusTarskiCatalogue.headContext c t e)
    b (FormulaSignSlotRadialRadiusWindowSigns.center c t e a) b' (FormulaSignSlotRadialRadiusWindowSigns.center c t e a') (FormulaSignSlotRadialRadiusWindowSigns.catalogue_signs c b a b' a' H t e ht he) hb hb'
  rw [base_head_eq,base_head_eq] at HE
  exact HE

theorem zero_iff (c : List Bool) (b : ℝ) (a : Fin (FormulaSignSlotRadialRadiusWindowSigns.centerCount c) → ℝ)
    (b' : ℝ) (a' : Fin (FormulaSignSlotRadialRadiusWindowSigns.centerCount c) → ℝ) (H : FormulaSignSlotRadialRadiusWindowSigns.Signs c b a b' a')
    (t e : ℕ) (ht : t < FormulaSignSlotRadialRadiusTarskiCatalogue.limit c) (he : e < FormulaSignSlotRadialRadiusTarskiCatalogue.limit c) :
    FormulaSignSlotRadialRadiusHeadInterval.specialized c a t e=0 ↔
      FormulaSignSlotRadialRadiusHeadInterval.specialized c a' t e=0 := by
  have HE := IntegralPolynomialWindowTarski.zero_iff_of_signs FormulaSignSlotRadialRadiusWindowBridge.source FormulaSignSlotRadialRadiusWindowBridge.centers FormulaSignSlotRadialRadiusWindowBridge.dimension (FormulaSignSlotRadialRadiusTarskiCatalogue.headContext c t e)
    b (FormulaSignSlotRadialRadiusWindowSigns.center c t e a) b' (FormulaSignSlotRadialRadiusWindowSigns.center c t e a') (FormulaSignSlotRadialRadiusWindowSigns.catalogue_signs c b a b' a' H t e ht he)
  rw [IntegralPolynomialWindowTarski.zero_iff,IntegralPolynomialWindowTarski.zero_iff,base_head_eq,base_head_eq] at HE
  exact HE

theorem coefficient_zero_iff (c : List Bool) (b : ℝ) (a : Fin (FormulaSignSlotRadialRadiusWindowSigns.centerCount c) → ℝ)
    (b' : ℝ) (a' : Fin (FormulaSignSlotRadialRadiusWindowSigns.centerCount c) → ℝ) (H : FormulaSignSlotRadialRadiusWindowSigns.Signs c b a b' a')
    (t e r : ℕ) (ht : t ≤ FormulaSignSlotRadialCenterSelection.bound c)
    (he : e ≤ FormulaSignSlotRadialCenterSelection.bound c) (hr : r ≤ FormulaSignSlotRadialCenterSelection.bound c) :
    FormulaSignSlotRadialCenterSelection.Zero c a t e r ↔ FormulaSignSlotRadialCenterSelection.Zero c a' t e r := by
  change t ≤ FormulaSignSlotRadialEliminantPacked.resultDegree c at ht
  change e ≤ FormulaSignSlotRadialEliminantPacked.resultDegree c at he
  change r ≤ FormulaSignSlotRadialEliminantPacked.resultDegree c at hr
  have ht' : t < FormulaSignSlotRadialRadiusTarskiCatalogue.limit c := by unfold FormulaSignSlotRadialRadiusTarskiCatalogue.limit FormulaSignSlotRadialRadiusTarskiCatalogue.inputDegree; omega
  have he' : e < FormulaSignSlotRadialRadiusTarskiCatalogue.limit c := by unfold FormulaSignSlotRadialRadiusTarskiCatalogue.limit FormulaSignSlotRadialRadiusTarskiCatalogue.inputDegree; omega
  have hr' : r ≤ FormulaSignSlotRadialRadiusWindowBridge.source.degree (FormulaSignSlotRadialRadiusTarskiCatalogue.headContext c t e) := by
    change r ≤ FormulaSignSlotRadialEliminantPacked.resultDegree (pairFst (FormulaSignSlotRadialRadiusTarskiCatalogue.headContext c t e))
    rw [FormulaSignSlotRadialRadiusTarskiCatalogue.headContext,pairFst_pair]
    exact hr
  have HE := IntegralPolynomialWindowTarski.base_coefficient_zero_iff FormulaSignSlotRadialRadiusWindowBridge.source FormulaSignSlotRadialRadiusWindowBridge.centers FormulaSignSlotRadialRadiusWindowBridge.dimension (FormulaSignSlotRadialRadiusTarskiCatalogue.headContext c t e)
    b (FormulaSignSlotRadialRadiusWindowSigns.center c t e a) b' (FormulaSignSlotRadialRadiusWindowSigns.center c t e a') (FormulaSignSlotRadialRadiusWindowSigns.catalogue_signs c b a b' a' H t e ht' he') r hr'
  rw [base_head_eq,base_head_eq] at HE
  simpa only [FormulaSignSlotRadialRadiusHeadInterval.specialized,Polynomial.coeff_map,
    FormulaSignSlotRadialRadiusHeadEvaluation.coefficient,FormulaSignSlotRadialCenterSelection.Zero,MvPolynomial.coe_eval₂Hom] using HE

private theorem guards_transfer (c : List Bool) (b : ℝ) (a : Fin (FormulaSignSlotRadialRadiusWindowSigns.centerCount c) → ℝ)
    (b' : ℝ) (a' : Fin (FormulaSignSlotRadialRadiusWindowSigns.centerCount c) → ℝ) (H : FormulaSignSlotRadialRadiusWindowSigns.Signs c b a b' a') (t D : ℕ)
    (HG : FormulaSignSlotRadialCenterSelection.Guards c a t D) : FormulaSignSlotRadialCenterSelection.Guards c a' t D := by
  rcases HG with ⟨ht,hD,HL,⟨r,hr,HN⟩,HH⟩
  refine ⟨ht,hD,?_,⟨r,hr,?_⟩,?_⟩
  · intro k hk e he r hr
    exact (coefficient_zero_iff c b a b' a' H k e r (by omega) (by omega) (by omega)).mp (HL k hk e he r hr)
  · exact (coefficient_zero_iff c b a b' a' H t D r ht hD (by omega)).not.mp HN
  · intro e he hDe r hr
    exact (coefficient_zero_iff c b a b' a' H t e r ht (by omega) (by omega)).mp (HH e he hDe r hr)

theorem guards_iff (c : List Bool) (b : ℝ) (a : Fin (FormulaSignSlotRadialRadiusWindowSigns.centerCount c) → ℝ)
    (b' : ℝ) (a' : Fin (FormulaSignSlotRadialRadiusWindowSigns.centerCount c) → ℝ) (H : FormulaSignSlotRadialRadiusWindowSigns.Signs c b a b' a') (t D : ℕ) :
    FormulaSignSlotRadialCenterSelection.Guards c a t D ↔ FormulaSignSlotRadialCenterSelection.Guards c a' t D :=
  ⟨guards_transfer c b a b' a' H t D, guards_transfer c b' a' b a (fun i => (H i).symm) t D⟩

private theorem trailing_transfer (c : List Bool) (b : ℝ) (a : Fin (FormulaSignSlotRadialRadiusWindowSigns.centerCount c) → ℝ)
    (b' : ℝ) (a' : Fin (FormulaSignSlotRadialRadiusWindowSigns.centerCount c) → ℝ) (H : FormulaSignSlotRadialRadiusWindowSigns.Signs c b a b' a') (t D ell : ℕ)
    (HG : FormulaSignSlotRadialCenterTrailingSelection.Guards c a t D ell) :
    FormulaSignSlotRadialCenterTrailingSelection.Guards c a' t D ell := by
  rcases HG with ⟨HS,hell,HL,HN⟩
  have ht := HS.1
  have hD := HS.2.1
  refine ⟨guards_transfer c b a b' a' H t D HS,hell,?_,?_⟩
  · intro j hj r hr
    exact (coefficient_zero_iff c b a b' a' H t j r ht (by omega) (by omega)).mp (HL j hj r hr)
  · intro HAll
    apply HN
    intro r hr
    exact (coefficient_zero_iff c b a b' a' H t ell r ht (by omega) (by omega)).mpr (HAll r hr)

theorem trailing_guards_iff (c : List Bool) (b : ℝ) (a : Fin (FormulaSignSlotRadialRadiusWindowSigns.centerCount c) → ℝ)
    (b' : ℝ) (a' : Fin (FormulaSignSlotRadialRadiusWindowSigns.centerCount c) → ℝ) (H : FormulaSignSlotRadialRadiusWindowSigns.Signs c b a b' a') (t D ell : ℕ) :
    FormulaSignSlotRadialCenterTrailingSelection.Guards c a t D ell ↔
      FormulaSignSlotRadialCenterTrailingSelection.Guards c a' t D ell :=
  ⟨trailing_transfer c b a b' a' H t D ell, trailing_transfer c b' a' b a (fun i => (H i).symm) t D ell⟩

theorem zero_or_interval_iff (c : List Bool) (b : ℝ) (a : Fin (FormulaSignSlotRadialRadiusWindowSigns.centerCount c) → ℝ)
    (b' : ℝ) (a' : Fin (FormulaSignSlotRadialRadiusWindowSigns.centerCount c) → ℝ) (H : FormulaSignSlotRadialRadiusWindowSigns.Signs c b a b' a')
    (t e : ℕ) (ht : t < FormulaSignSlotRadialRadiusTarskiCatalogue.limit c) (he : e < FormulaSignSlotRadialRadiusTarskiCatalogue.limit c) (hb : 0 < b) (hb' : 0 < b') :
    (FormulaSignSlotRadialRadiusHeadInterval.specialized c a t e=0 ∨
      ∀r,(FormulaSignSlotRadialRadiusHeadInterval.specialized c a t e).eval r=0 → r ∉ Ioo 0 b) ↔
    (FormulaSignSlotRadialRadiusHeadInterval.specialized c a' t e=0 ∨
      ∀r,(FormulaSignSlotRadialRadiusHeadInterval.specialized c a' t e).eval r=0 → r ∉ Ioo 0 b') :=
  or_congr (zero_iff c b a b' a' H t e ht he) (interval_iff c b a b' a' H t e ht he hb hb')

private theorem lt_limit_of_bound (c : List Bool) (t : ℕ) (ht : t ≤ FormulaSignSlotRadialCenterSelection.bound c) :
    t < FormulaSignSlotRadialRadiusTarskiCatalogue.limit c := by
  change t ≤ FormulaSignSlotRadialEliminantPacked.resultDegree c at ht
  unfold FormulaSignSlotRadialRadiusTarskiCatalogue.limit FormulaSignSlotRadialRadiusTarskiCatalogue.inputDegree
  omega

/-- Both actual leading heads are selected internally from the installed coefficient signs. -/
theorem leading_interval_iff (c : List Bool) (b : ℝ) (a : Fin (FormulaSignSlotRadialRadiusWindowSigns.centerCount c) → ℝ)
    (b' : ℝ) (a' : Fin (FormulaSignSlotRadialRadiusWindowSigns.centerCount c) → ℝ) (H : FormulaSignSlotRadialRadiusWindowSigns.Signs c b a b' a') (hb : 0 < b) (hb' : 0 < b') :
    (∀r,(FormulaSignSlotRadialCenterSquarefreeSelection.coordinate c a).leadingCoeff.eval r=0 → r ∉ Ioo 0 b) ↔
      ∀r,(FormulaSignSlotRadialCenterSquarefreeSelection.coordinate c a').leadingCoeff.eval r=0 → r ∉ Ioo 0 b' := by
  obtain ⟨t,ht,D,hD,HL⟩ := FormulaSignSlotRadialCenterSelection.exists_guards c a
  have HR := (guards_iff c b a b' a' H t D).mp HL
  have HE := interval_iff c b a b' a' H t D (lt_limit_of_bound c t ht) (lt_limit_of_bound c D hD) hb hb'
  have EL : FormulaSignSlotRadialRadiusHeadInterval.specialized c a t D =
      (FormulaSignSlotRadialCenterSquarefreeSelection.coordinate c a).leadingCoeff :=
    FormulaSignSlotRadialRadiusHeadEvaluation.leading c a t D HL
  have ER : FormulaSignSlotRadialRadiusHeadInterval.specialized c a' t D =
      (FormulaSignSlotRadialCenterSquarefreeSelection.coordinate c a').leadingCoeff :=
    FormulaSignSlotRadialRadiusHeadEvaluation.leading c a' t D HR
  rw [EL,ER] at HE
  exact HE

/-- The margin trailing index is selected and transported through its finite actual zero guards. -/
theorem trailing_interval_iff (c : List Bool) (b : ℝ) (a : Fin (FormulaSignSlotRadialRadiusWindowSigns.centerCount c) → ℝ)
    (b' : ℝ) (a' : Fin (FormulaSignSlotRadialRadiusWindowSigns.centerCount c) → ℝ) (H : FormulaSignSlotRadialRadiusWindowSigns.Signs c b a b' a') (hb : 0 < b) (hb' : 0 < b') :
    (∀r,(FormulaSignSlotRadialCenterSquarefreeSelection.coordinate c a).trailingCoeff.eval r=0 → r ∉ Ioo 0 b) ↔
      ∀r,(FormulaSignSlotRadialCenterSquarefreeSelection.coordinate c a').trailingCoeff.eval r=0 → r ∉ Ioo 0 b' := by
  obtain ⟨t,ht,D,hD,ell,hell,HL⟩ := FormulaSignSlotRadialCenterTrailingSelection.exists_guards c a
  have HR := (trailing_guards_iff c b a b' a' H t D ell).mp HL
  have HE := interval_iff c b a b' a' H t ell (lt_limit_of_bound c t ht)
    (lt_limit_of_bound c ell (hell.trans hD)) hb hb'
  have EL : FormulaSignSlotRadialRadiusHeadInterval.specialized c a t ell =
      (FormulaSignSlotRadialCenterSquarefreeSelection.coordinate c a).trailingCoeff :=
    FormulaSignSlotRadialRadiusHeadEvaluation.trailing c a t D ell HL
  have ER : FormulaSignSlotRadialRadiusHeadInterval.specialized c a' t ell =
      (FormulaSignSlotRadialCenterSquarefreeSelection.coordinate c a').trailingCoeff :=
    FormulaSignSlotRadialRadiusHeadEvaluation.trailing c a' t D ell HR
  rw [EL,ER] at HE
  exact HE

end LeanCanny.Encoding.FormulaSignSlotRadialRadiusWindowInterval
