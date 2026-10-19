/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.CannyCoordinateSign
public import LeanCanny.Algebra.IntegerRankSpace

/-!
# CRT correction-rank bits for Canny's actual coefficients

The concrete resultant and all-branch coordinate coefficient interfaces supply
the uniform residue routine and FP magnitude budget needed for rank bit access.
Full coefficient digit access still needs streamed large-product arithmetic.
-/

@[expose] public section

namespace LeanCanny.Algebra
open Complexity
open LeanCanny.Encoding
open LeanCanny.Computation

namespace CannyResultantBits.IntegerAccess

noncomputable def rankBitEvaluator {F : BoundedFamily} (a : IntegerAccess F) (ha : a.PolyTime)
    (index : List Bool → List Bool) (hi : index ∈ FP) :
    SpaceFunction (fun c => if (IntegerRankBits.rank a.budget F.source.coefficient c).testBit
      (Nat.fromBitsLE (index c)) then [true] else []) :=
  IntegerRankBits.evaluator (Access.evaluator a.residue ha.residue) a.budget index (budget_mem_FP a ha) hi
    F.source.coefficient F.source.value_packet

end CannyResultantBits.IntegerAccess

namespace CannyCoordinateBits
open CannySubresultantBits (BoundedFamily IntegerAccess)

noncomputable def rankBitEvaluator {F : BoundedFamily} (a : IntegerAccess F) (ha : a.PolyTime)
    (index : List Bool → List Bool) (hi : index ∈ FP) :
    SpaceFunction (fun c => if (IntegerRankBits.rank (budgetWord a) (integerCoefficient F.family) c).testBit
      (Nat.fromBitsLE (index c)) then [true] else []) :=
  IntegerRankBits.evaluator (evaluator a.residue (a.residue_polyTime ha)) (budgetWord a) index
    (budgetWord_mem_FP a ha) hi (integerCoefficient F.family) (value_packet F.family)

end CannyCoordinateBits
end LeanCanny.Algebra
