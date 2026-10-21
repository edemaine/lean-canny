/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.CannyCoordinateSign
public import LeanCanny.Algebra.IntegerDigitSpace

/-!
# Magnitude bits of Canny's actual integer coefficients

The resultant and all-branch coordinate interfaces supply the residue evaluator
and FP magnitude budget. The complete CRT digit algorithm computes any selected
coefficient-magnitude bit without materializing the coefficient. Queries pair
the original source context with a binary bit index.
-/

@[expose] public section

namespace LeanCanny.Algebra
open Complexity
open LeanCanny.Encoding
open LeanCanny.Computation

namespace CannyResultantBits.IntegerAccess

theorem magnitudeBitEvaluator {F : BoundedFamily} (a : IntegerAccess F) (ha : a.PolyTime) :
    SpaceFunction (ArithmeticBits.bitValue (fun c => (F.source.coefficient c).natAbs)) := by
  refine IntegerDigitBits.evaluator (Access.evaluator a.residue ha.residue) a.budget (budget_mem_FP a ha)
    F.source.coefficient ?_ F.source.value_packet
  intro c
  rw [budget_code, show Nat.fromBitsLE (BinaryNatCode.encode (F.budget c)) = F.budget c from Nat.fromBitsLE_bits _]
  exact F.coefficient_bits c

end CannyResultantBits.IntegerAccess

namespace CannyCoordinateBits
open CannySubresultantBits (BoundedFamily IntegerAccess)

theorem magnitudeBitEvaluator {F : BoundedFamily} (a : IntegerAccess F) (ha : a.PolyTime) :
    SpaceFunction (ArithmeticBits.bitValue (fun c => (integerCoefficient F.family c).natAbs)) := by
  refine IntegerDigitBits.evaluator (evaluator a.residue (a.residue_polyTime ha)) (budgetWord a)
    (budgetWord_mem_FP a ha) (integerCoefficient F.family) ?_ (value_packet F.family)
  intro c
  rw [budgetWord_code, show Nat.fromBitsLE (BinaryNatCode.encode (budget F c)) = budget F c from Nat.fromBitsLE_bits _]
  exact coefficient_bits F c

end CannyCoordinateBits
end LeanCanny.Algebra
