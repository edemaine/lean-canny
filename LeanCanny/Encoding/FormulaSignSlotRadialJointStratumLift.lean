/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialJointStratumLabels
/-! # Every literal core root lifts to its bounded feature-count stratum -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialJointStratumLift
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.ETR LeanCanny.Connectivity LeanCanny.Computation
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "F" => FormulaSignSlotRadialJointCoefficientCatalogue.family
local notation "X" u => AuxiliaryCandidateComponentCover.Space FormulaSignSlotRadialJointLayout.dimension
  FormulaSignSlotRadialJointCore.equation u

attribute [local irreducible] FormulaSignSlotRadialJointCore.equation FormulaSignSlotRadialJointLayout.dimension

private theorem last_cases_last {n : ℕ} (p : Fin n → ℝ) (v : ℝ) :
    Fin.lastCases v p (Fin.last n) = v := by simp only [Fin.lastCases_last]

private theorem last_cases_old {n : ℕ} (p : Fin n → ℝ) (v : ℝ) :
    (fun i : Fin n => Fin.lastCases v p i.castSucc) = p := by
  funext i
  exact Fin.lastCases_castSucc i

private theorem cast_heq {n m : ℕ} (h : n = m) (p : Fin m → ℝ) :
    HEq (fun i : Fin n => p (Fin.cast h i)) p := by
  cases h
  rfl

private theorem core_cast_zero (c u : List Bool)
    (h : FormulaSignSlotRadialJointStratum.header c = u) (x : X u) :
    (FormulaSignSlotRadialJointCore.equation (FormulaSignSlotRadialJointStratum.header c)).eval
      (Formula.extend (fun i => x.val (Fin.cast (congrArg FormulaSignSlotRadialJointLayout.dimension h) i))) = 0 := by
  subst u
  simpa only [Fin.cast_refl, id_eq] using FormulaSignSlotRadialJointComponentTransport.core_root _ x

noncomputable def append (c : List Bool)
    (p : Fin (FormulaSignSlotRadialJointStratum.oldArity c) → ℝ) (v : ℝ) :
    Fin (FormulaSignSlotRadialJointStratum.arity c) → ℝ := Fin.lastCases v p

theorem oldPoint_append (c : List Bool)
    (p : Fin (FormulaSignSlotRadialJointStratum.oldArity c) → ℝ) (v : ℝ) :
    FormulaSignSlotRadialJointStratum.oldPoint c (append c p v) = p := by
  exact @last_cases_old (FormulaSignSlotRadialJointStratum.oldArity c) p v

theorem values_cast (c u : List Bool) (h : FormulaSignSlotRadialJointStratum.header c = u)
    (p : Fin (FormulaSignSlotRadialJointLayout.dimension u) → ℝ) (v : ℝ) :
    FormulaSignSlotRadialJointStratum.values c
      (append c (fun i => p (Fin.cast (congrArg FormulaSignSlotRadialJointLayout.dimension h) i)) v) =
        SquareFeatureProductEvaluation.values F u p := by
  subst u
  simp only [FormulaSignSlotRadialJointStratum.values, oldPoint_append, Fin.cast_refl, id_eq]

private theorem append_last (c : List Bool)
    (p : Fin (FormulaSignSlotRadialJointStratum.oldArity c) → ℝ) (v : ℝ) :
    append c p v (Fin.last (FormulaSignSlotRadialJointStratum.oldArity c)) = v :=
  @last_cases_last (FormulaSignSlotRadialJointStratum.oldArity c) p v

attribute [local irreducible] FormulaSignSlotRadialJointStratum.polynomial

theorem corePoint_heq (c u : List Bool) (h : FormulaSignSlotRadialJointStratum.header c = u)
    (y : FormulaSignSlotRadialJointStratumLabels.Space c) (x : X u)
    (hy : HEq (FormulaSignSlotRadialJointStratum.oldPoint c y.val) x.val) :
    HEq (FormulaSignSlotRadialJointStratumLabels.corePoint c y) x := by
  subst u
  apply heq_of_eq
  apply Subtype.ext
  exact eq_of_heq hy

theorem project_heq (side : Bool) (c u : List Bool)
    (h : FormulaSignSlotRadialJointStratum.header c = u)
    (y : FormulaSignSlotRadialJointStratumLabels.Space c) (x : X u)
    (hy : HEq (FormulaSignSlotRadialJointStratum.oldPoint c y.val) x.val) :
    HEq (FormulaSignSlotRadialJointStratumLabels.project side c y)
      (FormulaSignSlotRadialJointComponentTransport.project side u x) := by
  subst u
  have HE := eq_of_heq (corePoint_heq c _ rfl y x hy)
  unfold FormulaSignSlotRadialJointStratumLabels.project
  rw [HE]

theorem exists_lift (u : List Bool) (x : X u) :
    ∃ k ≤ (F).count u, ∃ y : FormulaSignSlotRadialJointStratumLabels.Space
      (FormulaSignSlotRadialJointStratum.packet u k),
      HEq (FormulaSignSlotRadialJointStratum.oldPoint
        (FormulaSignSlotRadialJointStratum.packet u k) y.val) x.val := by
  let a := SquareFeatureProductEvaluation.values F u x.val
  let k := SquareFeatureProduct.zeroCount a
  have HK : k ≤ (F).count u := by
    have H := SquareFeatureProduct.zeroCount_le a
    simpa only [k, a, SquareFeatureProductEvaluation.values, List.length_ofFn] using H
  obtain ⟨v,HV⟩ := (SquareFeatureProduct.exists_certificate_iff a k).mpr rfl
  let c := FormulaSignSlotRadialJointStratum.packet u k
  have HC : FormulaSignSlotRadialJointStratum.header c = u := pairFst_pair _ _
  let p : Fin (FormulaSignSlotRadialJointStratum.oldArity c) → ℝ :=
    fun i => x.val (Fin.cast (congrArg FormulaSignSlotRadialJointLayout.dimension HC) i)
  let y := append c p v
  have HY : (FormulaSignSlotRadialJointStratum.polynomial c).eval₂ (Int.castRingHom ℝ) y = 0 := by
    apply (FormulaSignSlotRadialJointStratum.zero_iff c y).mpr
    constructor
    · rw [oldPoint_append]
      exact core_cast_zero c u HC x
    · have HVal := values_cast c u HC x.val v
      change FormulaSignSlotRadialJointStratum.values c y = a at HVal
      rw [HVal]
      have HSelected : FormulaSignSlotRadialJointStratum.selected c = k := by
        simp only [c, FormulaSignSlotRadialJointStratum.packet, FormulaSignSlotRadialJointStratum.selected,
          pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
      rw [HSelected]
      rw [show y (Fin.last (FormulaSignSlotRadialJointStratum.oldArity c)) = v from append_last c p v]
      exact HV
  have HYM : MvPolynomial.eval y ((FormulaSignSlotRadialJointStratum.polynomial c).map (Int.castRingHom ℝ)) = 0 := by
    simpa only [MvPolynomial.eval_map] using HY
  refine ⟨k,HK,⟨y,HYM⟩,?_⟩
  rw [oldPoint_append]
  exact cast_heq (congrArg FormulaSignSlotRadialJointLayout.dimension HC) x.val

end LeanCanny.Encoding.FormulaSignSlotRadialJointStratumLift
