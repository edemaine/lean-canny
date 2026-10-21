/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.SubresultantEntrySpace
public import LeanCanny.Algebra.BerkowitzPolynomialSpace

/-!
# Certified modular coefficients of symbolic subresultants

A guarded polynomial determinant evaluator computes a selected coefficient of
a selected subresultant coefficient polynomial. FP metadata and space-bounded
input coefficient routines suffice. Invalid orders/coefficient indices return
zero on all input strings, including the empty-minor boundary.
-/

@[expose] public section

namespace LeanCanny.Algebra.SubresultantPolynomial

open LeanCanny.Encoding
open LeanCanny.Encoding.Brackets
open LeanCanny.Computation
open MatrixPower

structure ModularFamily where
  modulus : List Bool → ℕ
  left : (c : List Bool) → Polynomial (Polynomial (ZMod (modulus c)))
  right : (c : List Bool) → Polynomial (Polynomial (ZMod (modulus c)))
  leftDegree : List Bool → ℕ
  rightDegree : List Bool → ℕ
  order : List Bool → ℕ
  coefficient : List Bool → ℕ
  degree : List Bool → ℕ
  modulus_ne_zero : ∀ c, modulus c ≠ 0

def ModularFamily.valid (F : ModularFamily) (c : List Bool) : Prop :=
  F.order c < F.leftDegree c ∧ F.order c < F.rightDegree c ∧ F.coefficient c ≤ F.order c
instance (F : ModularFamily) (c : List Bool) : Decidable (F.valid c) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

noncomputable def ModularFamily.value (F : ModularFamily) (c : List Bool) : List Bool :=
  residueBits (((Subresultant.polynomial (F.left c) (F.right c) (F.leftDegree c) (F.rightDegree c) (F.order c)).coeff
    (F.coefficient c)).coeff (F.degree c))

def ModularFamily.zeroLanguage (F : ModularFamily) : Language :=
  {c | ((Subresultant.polynomial (F.left c) (F.right c) (F.leftDegree c) (F.rightDegree c) (F.order c)).coeff
    (F.coefficient c)).coeff (F.degree c) = 0}

noncomputable def ModularFamily.determinant (F : ModularFamily) : BerkowitzPolynomial.ModularFamily where
  dimension c := (F.leftDegree c - F.order c) + (F.rightDegree c - F.order c)
  modulus := F.modulus
  degree := F.degree
  matrix c := if F.valid c then Subresultant.minor (F.left c) (F.right c) (F.leftDegree c) (F.rightDegree c)
    (F.order c) (F.coefficient c) else 0
  modulus_ne_zero := F.modulus_ne_zero

theorem ModularFamily.value_eq (F : ModularFamily) (c : List Bool) : F.value c =
    if F.valid c then residueBits ((Subresultant.minor (F.left c) (F.right c) (F.leftDegree c) (F.rightDegree c)
      (F.order c) (F.coefficient c)).det.coeff (F.degree c)) else [] := by
  unfold value
  rw [Subresultant.coeff]
  by_cases hv : F.valid c
  · have hv' : F.order c < F.leftDegree c ∧ F.order c < F.rightDegree c ∧ F.coefficient c ≤ F.order c := hv
    rw [ite_eq_left hv', ite_eq_left hv]
  · have hv' : ¬ (F.order c < F.leftDegree c ∧ F.order c < F.rightDegree c ∧ F.coefficient c ≤ F.order c) := hv
    rw [ite_eq_right hv', ite_eq_right hv]
    simp [residueBits, BinaryNatCode.encode]

structure ModularAccess (F : ModularFamily) where
  bits : SubresultantBits.Access
  leftDegree_eq : ∀ c, bits.base.leftDegree c = BinaryNatCode.encode (F.leftDegree c)
  rightDegree_eq : ∀ c, bits.base.rightDegree c = BinaryNatCode.encode (F.rightDegree c)
  modulus_eq : ∀ c, bits.base.modulus c = BinaryNatCode.encode (F.modulus c)
  degree_eq : ∀ c, bits.base.degree c = BinaryNatCode.encode (F.degree c)
  order_eq : ∀ c, bits.order c = BinaryNatCode.encode (F.order c)
  coefficient_eq : ∀ c, bits.coefficient c = BinaryNatCode.encode (F.coefficient c)
  leftCoefficient_eq : ∀ c i d, bits.base.leftCoefficient (pair c (pair (BinaryNatCode.encode i) (BinaryNatCode.encode d))) =
    residueBits (((F.left c).coeff i).coeff d)
  rightCoefficient_eq : ∀ c i d, bits.base.rightCoefficient (pair c (pair (BinaryNatCode.encode i) (BinaryNatCode.encode d))) =
    residueBits (((F.right c).coeff i).coeff d)

namespace ModularAccess

theorem enabled_valid {F : ModularFamily} (a : ModularAccess F) (c : List Bool) : a.bits.enabled c ↔ F.valid c :=
  a.bits.enabled_eq c _ _ _ _ (a.leftDegree_eq c) (a.rightDegree_eq c) (a.order_eq c) (a.coefficient_eq c)

set_option backward.isDefEq.respectTransparency false in
noncomputable def determinant {F : ModularFamily} (a : ModularAccess F) :
    BerkowitzPolynomial.ModularAccess F.determinant where
  dimension := a.bits.dimension
  modulus := a.bits.base.modulus
  degree := a.bits.base.degree
  entry := a.bits.entry
  dimension_eq c := a.bits.dimension_code c _ _ _ (a.leftDegree_eq c) (a.rightDegree_eq c) (a.order_eq c)
  modulus_eq := a.modulus_eq
  degree_eq := a.degree_eq
  entry_eq := by
    intro c i j d
    change a.bits.entry (pair c (pair (BinaryNatCode.encode i.val) (pair (BinaryNatCode.encode j.val) (BinaryNatCode.encode d)))) =
      residueBits (((if F.valid c then Subresultant.minor (F.left c) (F.right c) (F.leftDegree c) (F.rightDegree c)
        (F.order c) (F.coefficient c) else 0) i j).coeff d)
    by_cases hv : F.valid c
    · have h := a.bits.entry_correct c (F.left c) (F.right c) _ _ _ _ d residueBits
        (a.leftDegree_eq c) (a.rightDegree_eq c) (a.order_eq c) (a.coefficient_eq c)
        (fun t => a.leftCoefficient_eq c t d) (fun t => a.rightCoefficient_eq c t d)
        (by simp [residueBits, BinaryNatCode.encode]) hv i j
      simpa only [ite_eq_left hv] using h
    · have hen : ¬ a.bits.enabled c := fun h => hv ((a.enabled_valid c).mp h)
      simp [SubresultantBits.Access.entry, hen, hv, residueBits, BinaryNatCode.encode]

theorem determinant_controls {F : ModularFamily} (a : ModularAccess F) (ha : a.bits.ControlsPolyTime) :
    a.determinant.ControlsPolyTime := by
  have hd := a.bits.dimension_mem_FP ha
  constructor
  · simpa only [determinant] using hd
  · simpa only [determinant] using ha.base.modulus
  · simpa only [determinant] using ha.base.degree

set_option backward.isDefEq.respectTransparency false in
theorem evaluator {F : ModularFamily} (a : ModularAccess F) (ha : a.bits.ControlsPolyTime)
    (L : SpaceFunction a.bits.base.leftCoefficient) (R : SpaceFunction a.bits.base.rightCoefficient) :
    SpaceFunction F.value := by
  have Eentry := a.bits.entryEvaluator ha L R
  have ED := BerkowitzPolynomial.ModularAccess.evaluator a.determinant (determinant_controls a ha) Eentry
  let E := SpaceFunction.branch (fun c => decide (a.bits.enabled c)) (a.bits.enabled_fppred ha).flag_mem_FP
    ED (SpaceFunction.ofFP (fun _ => []) (constFn_mem_FP []))
  refine E.congr (funext fun c => ?_)
  rw [F.value_eq]
  by_cases hv : F.valid c
  · have hen := (a.enabled_valid c).mpr hv
    simp only [hen, decide_true, ↓reduceIte, BerkowitzPolynomial.ModularFamily.value, ModularFamily.determinant, ite_eq_left hv]
  · have hen : ¬ a.bits.enabled c := fun h => hv ((a.enabled_valid c).mp h)
    simp only [hen, decide_false, Bool.false_eq_true, ↓reduceIte, ite_eq_right hv]

theorem decider {F : ModularFamily} (a : ModularAccess F) (ha : a.bits.ControlsPolyTime)
    (L : SpaceFunction a.bits.base.leftCoefficient) (R : SpaceFunction a.bits.base.rightCoefficient) :
    SpaceDecider F.zeroLanguage := by
  have hflag : (fun w : List Bool => [decide (w = [])]) ∈ FP :=
    (stringEq_fppred id_mem_FP (constFn_mem_FP [])).flag_mem_FP
  apply (evaluator a ha L R).decider (fun w => decide (w = [])) hflag
  intro c
  let : NeZero (F.modulus c) := ⟨F.modulus_ne_zero c⟩
  have hz : residueBits (0 : ZMod (F.modulus c)) = [] := by simp [residueBits, BinaryNatCode.encode]
  change _ = 0 ↔ decide (residueBits _ = []) = true
  rw [decide_eq_true_eq, ← hz, (residueBits_injective (F.modulus c)).eq_iff]

theorem zeroLanguage_mem_PSPACE {F : ModularFamily} (a : ModularAccess F) (ha : a.bits.ControlsPolyTime)
    (L : SpaceFunction a.bits.base.leftCoefficient) (R : SpaceFunction a.bits.base.rightCoefficient) :
    F.zeroLanguage ∈ PSPACE := (decider a ha L R).mem_PSPACE

end ModularAccess
end LeanCanny.Algebra.SubresultantPolynomial
