/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.CannyCoefficientSpace

/-! # Total supplied-degree metadata for Canny coefficient sources

Raw degree-code writers select Sylvester orders by binary decoding. They need
not equal actual polynomial degrees. Normalization supplies the exact encoded
order fields expected by the native determinant routines. Original polynomial
coefficient access, direction, and output-degree selection are retained.
-/

@[expose] public section

namespace LeanCanny.Algebra.CannyResultantBits.Access
open LeanCanny.Encoding LeanCanny.Computation

def withDegreeCodes {F : Family} {leftOrder rightOrder : List Bool → ℕ}
    (a : Access F leftOrder rightOrder) (leftCode rightCode : List Bool → List Bool) :
    Access F (fun c => Nat.fromBitsLE (leftCode c)) (fun c => Nat.fromBitsLE (rightCode c)) where
  leftDegree := BinaryNat.normalize ∘ leftCode
  rightDegree := BinaryNat.normalize ∘ rightCode
  direction := a.direction
  degree := a.degree
  leftCoefficient := a.leftCoefficient
  rightCoefficient := a.rightCoefficient
  leftDegree_eq c := BinaryNat.normalize_eq_bits (leftCode c)
  rightDegree_eq c := BinaryNat.normalize_eq_bits (rightCode c)
  direction_eq := a.direction_eq
  degree_eq := a.degree_eq
  leftCoefficient_eq := a.leftCoefficient_eq
  rightCoefficient_eq := a.rightCoefficient_eq

/-- No certificate for the discarded old degree writers or the coefficient
answers is needed. In particular the supplied codes need no degree-validation
hypothesis. Their decoded orders define the specified-degree determinant. -/
theorem withDegreeCodes_controls {F : Family} {leftOrder rightOrder : List Bool → ℕ}
    (a : Access F leftOrder rightOrder) (leftCode rightCode : List Bool → List Bool)
    (hl : leftCode ∈ FP) (hr : rightCode ∈ FP) (hd : a.direction ∈ FP) (hk : a.degree ∈ FP) :
    (a.withDegreeCodes leftCode rightCode).ControlsPolyTime := by
  have hl' := mem_FP_comp hl BinaryNat.normalize_mem_FP
  have hr' := mem_FP_comp hr BinaryNat.normalize_mem_FP
  exact ⟨hl', hr', hd, hk⟩

theorem withDegreeCodes_value_eq {F : Family} (leftCode rightCode : List Bool → List Bool) (q : List Bool)
    (hl : leftCode (pairFst q) = BinaryNatCode.encode (F.left (pairFst q)).natDegree)
    (hr : rightCode (pairFst q) = BinaryNatCode.encode (F.right (pairFst q)).natDegree) :
    F.specifiedValue (fun c => Nat.fromBitsLE (leftCode c)) (fun c => Nat.fromBitsLE (rightCode c)) q = F.value q := by
  apply F.specifiedValue_eq
  · simp only [hl, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  · simp only [hr, BinaryNatCode.encode, Nat.fromBitsLE_bits]

end LeanCanny.Algebra.CannyResultantBits.Access
