/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialJointCoefficientMeaning
public import LeanCanny.Geometry.SquareFeatureSignStratum
public import LeanCanny.Encoding.FormulaSignSlotRadialCenterSelection
public import Mathlib.Topology.Algebra.MvPolynomial
/-! # Actual radial perturbation/degree guards persist on their feature stratum

This uses the concrete bounded coefficient catalogue. No polynomial sign,
selected index, or sampler point is supplied by a component oracle.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialJointSelectionStratum
open LeanCanny.Algebra LeanCanny.Connectivity LeanCanny.Geometry LeanCanny.Computation MvPolynomial Set
open FormulaSignSlotRadialJointCoefficientCatalogue
open scoped Classical
set_option backward.isDefEq.respectTransparency false

abbrev Point (c : List Bool) := Fin (family.arity c) → ℝ
noncomputable def extend {n : ℕ} (x : Fin n → ℝ) (i : ℕ) : ℝ := if hi : i<n then x ⟨i,hi⟩ else 0
theorem extend_val {n : ℕ} (x : Fin n → ℝ) (i : Fin n) : extend x i.val=x i := by
  simp only [extend,dite_eq_left i.isLt]
noncomputable def featureValue (c : List Bool) (i : ℕ) (x : Point c) :=
  (family.feature c i).eval₂ (Int.castRingHom ℝ) x
def Signs (c : List Bool) (x y : Point c) : Prop :=
  ∀ i : Fin (count c), SignType.sign (featureValue c i.val x)=SignType.sign (featureValue c i.val y)

theorem coefficient_zero_iff (c : List Bool) (x y : Point c) (HS : Signs c x y)
    (j s t r : ℕ) (hj : j<FormulaSignSlotRadialJointLayout.spatialCount c)
    (hs : s<limit c) (ht : t<limit c) (hr : r<limit c) :
    coefficientValue c j s t r (extend x)=0 ↔ coefficientValue c j s t r (extend y)=0 := by
  let k := encode c j s t r
  have HK : k<count c := encode_lt c j s t r hj hs ht hr
  have HE (z : Point c) : (fun i : Fin (family.arity c) => extend z i.val)=z := funext (extend_val z)
  have HX := feature_coefficient c j s t r hs ht hr (extend x)
  have HY := feature_coefficient c j s t r hs ht hr (extend y)
  rw [HE x] at HX
  rw [HE y] at HY
  have HSign := HS ⟨k,HK⟩
  change SignType.sign ((family.feature c k).eval₂ (Int.castRingHom ℝ) x)=
    SignType.sign ((family.feature c k).eval₂ (Int.castRingHom ℝ) y) at HSign
  rw [HX,HY] at HSign
  have H0 := Iff.of_eq (congrArg (fun a : SignType => a=0) HSign)
  simpa only [sign_eq_zero_iff] using H0

noncomputable def coordinateContext (c : List Bool) (j : ℕ) :=
  FormulaSignSlotRadialCoordinatePacket.packet (FormulaSignSlotRadialJointLayout.source true c) j
noncomputable def center (c : List Bool) (j : ℕ) (x : Point c)
    (i : Fin (FormulaSignSlotCenteredRadialGraph.d (pairFst (coordinateContext c j)))) := extend x (4*i.val)

theorem guards_iff_of_signs (c : List Bool) (j : ℕ) (hj : j<FormulaSignSlotRadialJointLayout.spatialCount c)
    (x y : Point c) (HS : Signs c x y) (tau D : ℕ) :
    FormulaSignSlotRadialCenterSelection.Guards (coordinateContext c j) (center c j x) tau D ↔
      FormulaSignSlotRadialCenterSelection.Guards (coordinateContext c j) (center c j y) tau D := by
  have HB : FormulaSignSlotRadialCenterSelection.bound (coordinateContext c j)=degree c := by
    apply FormulaSignSlotRadialEliminantRootProfiles.degree_eq
    simp only [coordinateContext,FormulaSignSlotRadialCoordinatePacket.root,base,pairFst_pair]
  have zeroes (u v : Point c) (HV : Signs c u v) (s : ℕ) (hs : s<limit c) (t : ℕ) (ht : t<limit c)
      (r : ℕ) (hr : r<limit c) :
      FormulaSignSlotRadialCenterSelection.Zero (coordinateContext c j) (center c j u) s t r ↔
        FormulaSignSlotRadialCenterSelection.Zero (coordinateContext c j) (center c j v) s t r :=
    coefficient_zero_iff c u v HV j s t r hj hs ht hr
  have transfer (u v : Point c) (HV : Signs c u v) :
      FormulaSignSlotRadialCenterSelection.Guards (coordinateContext c j) (center c j u) tau D →
        FormulaSignSlotRadialCenterSelection.Guards (coordinateContext c j) (center c j v) tau D := by
    rintro ⟨HT,HD,HL,⟨r,hr,HN⟩,HH⟩
    have HT0 : tau<limit c := by unfold limit; omega
    have HD0 : D<limit c := by unfold limit; omega
    have HR0 : r<limit c := by unfold limit; omega
    refine ⟨HT,HD,?_,⟨r,hr,(zeroes u v HV tau HT0 D HD0 r HR0).not.mp HN⟩,?_⟩
    · intro s hs t ht r hr
      apply (zeroes u v HV s (by unfold limit; omega) t (by unfold limit; omega) r (by unfold limit; omega)).mp
      exact HL s hs t ht r hr
    · intro t ht hdt r hr
      apply (zeroes u v HV tau HT0 t (by unfold limit; omega) r (by unfold limit; omega)).mp
      exact HH t ht hdt r hr
  exact ⟨transfer x y HS,transfer y x (fun i => (HS i).symm)⟩

private theorem continuous_integer_eval {ι : Type*} (p : MvPolynomial ι ℤ) :
    Continuous (fun x : ι → ℝ => p.eval₂ (Int.castRingHom ℝ) x) := by
  simpa only [MvPolynomial.eval₂_eq_eval_map] using (p.map (Int.castRingHom ℝ)).continuous_eval

theorem guards_iff_on_equation_stratum (c : List Bool) (j : ℕ)
    (hj : j<FormulaSignSlotRadialJointLayout.spatialCount c) (K : ℕ)
    {s : Set (Point c)} (HS : IsPreconnected s)
    (HEq : ∀ z∈s, ∃ w : ℝ, SquareFeatureProduct.equation
      (List.ofFn (fun i : Fin (count c) => featureValue c i.val z)) K w=0)
    {x y : Point c} (HX : x∈s) (HY : y∈s) (tau D : ℕ) :
    FormulaSignSlotRadialCenterSelection.Guards (coordinateContext c j) (center c j x) tau D ↔
      FormulaSignSlotRadialCenterSelection.Guards (coordinateContext c j) (center c j y) tau D := by
  apply guards_iff_of_signs c j hj x y ?_ tau D
  intro i
  exact SquareFeatureSignStratum.sign_eq_on_equation_stratum (count c)
    (fun i z => featureValue c i.val z) (fun i => continuous_integer_eval (family.feature c i.val)) K HS HEq HX HY i

end LeanCanny.Encoding.FormulaSignSlotRadialJointSelectionStratum
