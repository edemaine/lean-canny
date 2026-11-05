/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.PolynomialRadiusSublevelMap
public import LeanCanny.Geometry.PolynomialComponentPaths
/-! # Component paths inside a residual-and-radius window

Two real slack coordinates turn the inequalities into a polynomial zero set.
Its component paths project into the original window. This works at singular
levels and uses no regularity or supplied semialgebraic path theorem.
-/
@[expose] public section
namespace LeanCanny.Geometry.PolynomialRadiusWindowPaths
open MvPolynomial Set PolynomialRadiusSublevelMap CoerciveComponentSampling
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

def Window (q : MvPolynomial (Fin n) ℤ) (e r : ℝ) : Set (Fin n → ℝ) :=
  {x | normValue x ≤ r ∧ residual q x ≤ e}

def embed (i : Fin n) : Fin (n+2) := i.castSucc.castSucc
def old (z : Fin (n+2) → ℝ) : Fin n → ℝ := fun i => z (embed i)
def firstSlack : Fin (n+2) := (Fin.last n).castSucc
def secondSlack : Fin (n+2) := Fin.last (n+1)

noncomputable def polynomial (q : MvPolynomial (Fin n) ℤ) (e r : ℝ) : MvPolynomial (Fin (n+2)) ℝ :=
  (rename embed ((q^2).map (Int.castRingHom ℝ)) + X firstSlack ^ 2 - C e)^2 +
    (rename embed ((normPolynomial n).map (Int.castRingHom ℝ)) + X secondSlack ^ 2 - C r)^2

theorem zero_iff (q : MvPolynomial (Fin n) ℤ) (e r : ℝ) (z : Fin (n+2) → ℝ) :
    (polynomial q e r).eval z = 0 ↔
      residual q (old z) + z firstSlack ^ 2 = e ∧ normValue (old z) + z secondSlack ^ 2 = r := by
  simp only [polynomial,eval_add,eval_pow,eval_sub,eval_rename,eval_map,eval_X,eval_C]
  rw [add_eq_zero_iff_of_nonneg (sq_nonneg _) (sq_nonneg _)]
  simp only [sq_eq_zero_iff,sub_eq_zero]
  rfl

theorem old_mem (q : MvPolynomial (Fin n) ℤ) (e r : ℝ) (z : Fin (n+2) → ℝ)
    (hz : (polynomial q e r).eval z = 0) : old z ∈ Window q e r := by
  obtain ⟨HE,HR⟩ := (zero_iff q e r z).mp hz
  constructor
  · linarith [sq_nonneg (z secondSlack)]
  · linarith [sq_nonneg (z firstSlack)]

noncomputable def sectionPoint (q : MvPolynomial (Fin n) ℤ) (e r : ℝ) (x : Fin n → ℝ) : Fin (n+2) → ℝ :=
  Fin.snoc (Fin.snoc x (Real.sqrt (e - residual q x))) (Real.sqrt (r - normValue x))

theorem old_section (q : MvPolynomial (Fin n) ℤ) (e r : ℝ) (x : Fin n → ℝ) :
    old (sectionPoint q e r x) = x := by
  funext i
  simp only [old,embed,sectionPoint,Fin.snoc_castSucc]

theorem first_section (q : MvPolynomial (Fin n) ℤ) (e r : ℝ) (x : Fin n → ℝ) :
    sectionPoint q e r x firstSlack = Real.sqrt (e - residual q x) := by
  simp only [sectionPoint,firstSlack,Fin.snoc_castSucc,Fin.snoc_last]
theorem second_section (q : MvPolynomial (Fin n) ℤ) (e r : ℝ) (x : Fin n → ℝ) :
    sectionPoint q e r x secondSlack = Real.sqrt (r - normValue x) := by
  simp only [sectionPoint,secondSlack,Fin.snoc_last]

theorem section_zero (q : MvPolynomial (Fin n) ℤ) (e r : ℝ) (x : Fin n → ℝ) (hx : x ∈ Window q e r) :
    (polynomial q e r).eval (sectionPoint q e r x) = 0 := by
  rw [zero_iff,old_section,first_section,second_section]
  rw [Real.sq_sqrt (sub_nonneg.mpr hx.2),Real.sq_sqrt (sub_nonneg.mpr hx.1)]
  constructor <;> ring

theorem continuous_section (q : MvPolynomial (Fin n) ℤ) (e r : ℝ) : Continuous (sectionPoint q e r) := by
  have HI : Continuous (fun x : Fin n → ℝ => x) := continuous_id
  have HE : Continuous (fun x : Fin n → ℝ => Real.sqrt (e - residual q x)) :=
    Real.continuous_sqrt.comp (continuous_const.sub
      (ProjectionCritical.contDiff_eval (Int.castRingHom ℝ) (q^2)).continuous)
  have HR : Continuous (fun x : Fin n → ℝ => Real.sqrt (r - normValue x)) :=
    Real.continuous_sqrt.comp (continuous_const.sub
      (ProjectionCritical.contDiff_eval (Int.castRingHom ℝ) (normPolynomial n)).continuous)
  have H1 := HI.finSnoc (A := fun _ : Fin (n+1) => ℝ) HE
  exact H1.finSnoc (A := fun _ : Fin (n+2) => ℝ)
    HR

noncomputable def sectionMap (q : MvPolynomial (Fin n) ℤ) (e r : ℝ) (x : Window q e r) :
    Zeros (polynomial q e r) := ⟨sectionPoint q e r x.val,section_zero q e r x.val x.property⟩

theorem continuous_sectionMap (q : MvPolynomial (Fin n) ℤ) (e r : ℝ) : Continuous (sectionMap q e r) :=
  ((continuous_section q e r).comp continuous_subtype_val).subtype_mk _

theorem continuous_old : Continuous (old (n := n)) := continuous_pi (fun i => continuous_apply (embed i))

theorem joined_of_component (q : MvPolynomial (Fin n) ℤ) (e r : ℝ)
    (x y : Fin n → ℝ) (hx : x ∈ Window q e r) (hy : y ∈ connectedComponentIn (Window q e r) x) :
    JoinedIn (Window q e r) x y := by
  rw [connectedComponentIn_eq_image hx] at hy
  obtain ⟨z,hz,rfl⟩ := hy
  have HC := (continuous_sectionMap q e r).mapsTo_connectedComponent ⟨x,hx⟩ hz
  have H := PolynomialComponentPaths.subtype_joined (polynomial q e r)
    (sectionMap q e r ⟨x,hx⟩) (sectionMap q e r z) HC
  have HP := H.map continuous_old.continuousOn
  change JoinedIn (old '' Zeros (polynomial q e r))
    (old (sectionPoint q e r x)) (old (sectionPoint q e r z.val)) at HP
  rw [old_section,old_section] at HP
  apply HP.mono
  rintro a ⟨b,hb,rfl⟩
  exact old_mem q e r b hb

theorem component_iff_joined (q : MvPolynomial (Fin n) ℤ) (e r : ℝ)
    (x y : Fin n → ℝ) (hx : x ∈ Window q e r) (hy : y ∈ Window q e r) :
    y ∈ connectedComponentIn (Window q e r) x ↔ JoinedIn (Window q e r) x y := by
  constructor
  · exact joined_of_component q e r x y hx
  · intro H
    rw [connectedComponentIn_eq_image hx]
    exact ⟨⟨y,hy⟩,pathComponent_subset_component _ ((joinedIn_iff_joined hx hy).mp H),rfl⟩

end LeanCanny.Geometry.PolynomialRadiusWindowPaths
