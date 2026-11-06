/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialJointStratumLabels
public import LeanCanny.Geometry.SquareFeatureSignStratum
public import Mathlib.Topology.Algebra.MvPolynomial
/-! # Every actual catalogue feature retains its sign along a stratum path -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialJointFeatureRetention
open LeanCanny.Algebra LeanCanny.Geometry Set
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "F" => FormulaSignSlotRadialJointCoefficientCatalogue.family
local notation "S" => FormulaSignSlotRadialJointStratum.source
local notation "Space" => FormulaSignSlotRadialJointStratumLabels.Space

noncomputable def feature (c : List Bool) (i : ℕ) (x : Space c) : ℝ :=
  ((F).feature (FormulaSignSlotRadialJointStratum.header c) i).eval₂ (Int.castRingHom ℝ)
    (FormulaSignSlotRadialJointStratum.oldPoint c x.val)

private theorem continuous_integer_eval {ι : Type*} (p : MvPolynomial ι ℤ) :
    Continuous (fun x : ι → ℝ => p.eval₂ (Int.castRingHom ℝ) x) := by
  simpa only [MvPolynomial.eval₂_eq_eval_map] using (p.map (Int.castRingHom ℝ)).continuous_eval

theorem continuous_feature (c : List Bool) (i : ℕ) : Continuous (feature c i) := by
  have HC : Continuous (fun x : Space c => FormulaSignSlotRadialJointStratum.oldPoint c x.val) := by
    apply continuous_pi
    intro j
    exact (continuous_apply j.castSucc).comp continuous_subtype_val
  exact (continuous_integer_eval ((F).feature (FormulaSignSlotRadialJointStratum.header c) i)).comp HC

theorem equation (c : List Bool) (x : Space c) :
    ∃ w : ℝ, SquareFeatureProduct.equation
      (List.ofFn (fun i : Fin ((F).count (FormulaSignSlotRadialJointStratum.header c)) => feature c i.val x))
      (FormulaSignSlotRadialJointStratum.selected c) w = 0 := by
  have HX := (FormulaSignSlotRadialJointStratum.zero_iff c x.val).mp
    (FormulaSignSlotRadialJointStratumLabels.source_zero c x) |>.2
  exact ⟨x.val (Fin.last (FormulaSignSlotRadialJointStratum.oldArity c)),
    (SquareFeatureProduct.equation_zero_iff _ _ _).mpr HX⟩

theorem sign_eq_of_joined (c : List Bool) (x y : Space c)
    (h : JoinedIn (CoerciveComponentSampling.Zeros (((S).polynomial c).map (Int.castRingHom ℝ))) x.val y.val)
    (i : Fin ((F).count (FormulaSignSlotRadialJointStratum.header c))) :
    SignType.sign (feature c i.val x) = SignType.sign (feature c i.val y) := by
  obtain ⟨p⟩ := (joinedIn_iff_joined x.property y.property).mp h
  apply SquareFeatureSignStratum.sign_eq_on_equation_stratum
    ((F).count (FormulaSignSlotRadialJointStratum.header c)) (fun j z => feature c j.val z)
    (fun j => continuous_feature c j.val) (FormulaSignSlotRadialJointStratum.selected c)
    (s := Set.range p) ?_ (fun z _ => equation c z) p.source_mem_range p.target_mem_range i
  simpa only [Set.image_univ] using isPreconnected_univ.image p p.continuous.continuousOn

end LeanCanny.Encoding.FormulaSignSlotRadialJointFeatureRetention
