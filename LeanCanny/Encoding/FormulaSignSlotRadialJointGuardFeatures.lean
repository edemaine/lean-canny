/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialJointGridCompleteCatalogue
public import LeanCanny.Encoding.FormulaSignSlotRadialJointRadiusTarskiCatalogue
public import LeanCanny.Encoding.FormulaSignSlotRadialJointPrincipalWindowCatalogue
public import LeanCanny.Encoding.FormulaSignSlotRadialJointValueWindowCatalogue
public import LeanCanny.Algebra.SquareFeatureProductAppend
/-! # Actual grid, coordinate-head, principal and value interval features -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialJointGuardFeatures
open LeanCanny.Algebra LeanCanny.Computation
open scoped Classical
local notation "G" => FormulaSignSlotRadialJointGridCompleteCatalogue.family
local notation "T" => FormulaSignSlotRadialJointRadiusTarskiCatalogue.family
local notation "P" => FormulaSignSlotRadialJointPrincipalWindowCatalogue.family
local notation "V" => FormulaSignSlotRadialJointValueWindowCatalogue.family

private theorem cast_heq {n m : ℕ} (h : n = m) (p : MvPolynomial (Fin n) ℤ) :
    HEq (MvPolynomial.rename (Fin.cast h) p) p := by
  cases h
  simpa only [Fin.cast_refl, MvPolynomial.rename_id, AlgHom.id_apply] using (HEq.rfl : HEq p p)

private theorem evaluate_cast {n m : ℕ} (h : n = m) (p : MvPolynomial (Fin n) ℤ)
    (v : ℕ → ℝ) :
    (MvPolynomial.rename (Fin.cast h) p).eval₂ (Int.castRingHom ℝ) (fun i => v i.val) =
      p.eval₂ (Int.castRingHom ℝ) (fun i => v i.val) := by
  subst m
  simp only [Fin.cast_refl, MvPolynomial.rename_id, AlgHom.id_apply]

noncomputable def baseFamily := SquareFeatureProductAppend.family G T (fun _ => rfl)
noncomputable def principalFamily := SquareFeatureProductAppend.family baseFamily P (fun _ => rfl)
noncomputable def family := SquareFeatureProductAppend.family principalFamily V (fun _ => rfl)
noncomputable def base_access : SquareFeatureProductFamily.Access baseFamily :=
  SquareFeatureProductAppend.access G T (fun _ => rfl)
    FormulaSignSlotRadialJointGridCompleteCatalogue.access
    FormulaSignSlotRadialJointRadiusTarskiCatalogue.access
noncomputable def principal_access : SquareFeatureProductFamily.Access principalFamily :=
  SquareFeatureProductAppend.access baseFamily P (fun _ => rfl) base_access
    FormulaSignSlotRadialJointPrincipalWindowCatalogue.access
noncomputable def access : SquareFeatureProductFamily.Access family :=
  SquareFeatureProductAppend.access principalFamily V (fun _ => rfl) principal_access
    FormulaSignSlotRadialJointValueWindowCatalogue.access

noncomputable def principalIndex (c : List Bool) (i : ℕ) := baseFamily.count c + i
noncomputable def valueIndex (c : List Bool) (i : ℕ) := principalFamily.count c + i

theorem base_count_le (c : List Bool) : baseFamily.count c ≤ family.count c :=
  (Nat.le_add_right _ _).trans (Nat.le_add_right _ _)

theorem grid_count_le (c : List Bool) : (G).count c ≤ family.count c :=
  (Nat.le_add_right _ _).trans (base_count_le c)

theorem base_feature (c : List Bool) (i : ℕ) (hi : i < baseFamily.count c) :
    family.feature c i = baseFamily.feature c i :=
  (SquareFeatureProductAppend.feature_left principalFamily V (fun _ => rfl) c i
    (hi.trans_le (Nat.le_add_right _ _))).trans
      (SquareFeatureProductAppend.feature_left baseFamily P (fun _ => rfl) c i hi)

theorem grid_feature (c : List Bool) (i : ℕ) (hi : i < (G).count c) :
    family.feature c i = (G).feature c i :=
  (base_feature c i (hi.trans_le (Nat.le_add_right _ _))).trans
    (SquareFeatureProductAppend.feature_left G T (fun _ => rfl) c i hi)

theorem tarski_feature (c : List Bool) (i : ℕ) (hi : i < (T).count c) :
    HEq (family.feature c ((G).count c + i)) ((T).feature c i) := by
  have H : (G).count c + i < baseFamily.count c := Nat.add_lt_add_left hi _
  exact (heq_of_eq (base_feature c _ H)).trans
    ((heq_of_eq (SquareFeatureProductAppend.feature_right G T (fun _ => rfl) c i hi)).trans
      (cast_heq rfl ((T).feature c i)))

theorem principal_index_lt (c : List Bool) (i : ℕ) (hi : i < (P).count c) :
    principalIndex c i < family.count c :=
  (Nat.add_lt_add_left hi _).trans_le (Nat.le_add_right _ _)

theorem value_index_lt (c : List Bool) (i : ℕ) (hi : i < (V).count c) :
    valueIndex c i < family.count c := Nat.add_lt_add_left hi _

theorem principal_feature_eval (c : List Bool) (i : ℕ) (hi : i < (P).count c) (v : ℕ → ℝ) :
    (family.feature c (principalIndex c i)).eval₂ (Int.castRingHom ℝ) (fun j => v j.val) =
      ((P).feature c i).eval₂ (Int.castRingHom ℝ) (fun j => v j.val) := by
  have H0 := SquareFeatureProductAppend.feature_left principalFamily V (fun _ => rfl) c
    (principalIndex c i) (Nat.add_lt_add_left hi _)
  have H1 := SquareFeatureProductAppend.feature_right baseFamily P (fun _ => rfl) c i hi
  exact (congrArg (fun p => p.eval₂ (Int.castRingHom ℝ) (fun j => v j.val)) H0).trans
    ((congrArg (fun p => p.eval₂ (Int.castRingHom ℝ) (fun j => v j.val)) H1).trans
      (evaluate_cast rfl _ v))

theorem value_feature_eval (c : List Bool) (i : ℕ) (hi : i < (V).count c) (v : ℕ → ℝ) :
    (family.feature c (valueIndex c i)).eval₂ (Int.castRingHom ℝ) (fun j => v j.val) =
      ((V).feature c i).eval₂ (Int.castRingHom ℝ) (fun j => v j.val) := by
  have H := SquareFeatureProductAppend.feature_right principalFamily V (fun _ => rfl) c i hi
  exact (congrArg (fun p => p.eval₂ (Int.castRingHom ℝ) (fun j => v j.val)) H).trans
    (evaluate_cast rfl _ v)

end LeanCanny.Encoding.FormulaSignSlotRadialJointGuardFeatures
