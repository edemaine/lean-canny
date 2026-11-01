/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedValueMacaulayMatrix

/-! # The one shifted reply is an actual mapped-system coefficient -/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedValueMacaulayChildren
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedVirtualQueryBits IntegralMixedVirtualCaps IntegralMixedValueMacaulayTasks
open scoped Classical
attribute [local irreducible] IntegralMixedValueDoubleNilpotent.basis

noncomputable def coefficientReference (P : Parameters) (F : Family) (q : List Bool)
    (r t : Fin (IntegralMixedValueMacaulayMatrix.rank (IntegralMixedVirtualTaskBits.family P F) q)) : List Bool → List Bool :=
  MacaulayIntegralLocalCorrect.coefficient (layout P F) q
    (IntegralMixedValueDoubleSystem.mappedSystem (IntegralMixedVirtualTaskBits.family P F) q
      ((IntegralMixedVirtualTaskBits.indices P F).coordinate q))
    (fun z => residueBits ((Algebra.leftMulMatrix
      (IntegralMixedValueDoubleNilpotent.basis ((IntegralMixedVirtualTaskBits.family P F).state q)) z r t : ℤ) : ZMod (modulus P q)))

theorem coefficient_packet (P : Parameters) (F : Family) (q : List Bool)
    (r t : Fin (IntegralMixedValueMacaulayMatrix.rank (IntegralMixedVirtualTaskBits.family P F) q))
    (j : Fin ((layout P F).arity q)) (k : ℕ) :
    coefficientReference P F q r t (MacaulayFullBoxBits.entryPacket q j.val k r.val t.val) = residueBits
      ((Algebra.leftMulMatrix (IntegralMixedValueDoubleNilpotent.basis ((IntegralMixedVirtualTaskBits.family P F).state q))
        ((IntegralMixedValueDoubleSystem.mappedSystem (IntegralMixedVirtualTaskBits.family P F) q
          ((IntegralMixedVirtualTaskBits.indices P F).coordinate q) j).coeff
            (RationalSubstitution.Indexed.exponentVector ((layout P F).arity q) (entry ((layout P F).width q) k))) r t : ℤ) :
              ZMod (modulus P q)) :=
  MacaulayIntegralLocalCorrect.coefficient_packet _ _ _ _ j k r.val t.val

theorem coefficient_reply (P : Parameters) (F : Family) (g : RootGeometry P F) (q : List Bool)
    (r t : Fin (IntegralMixedValueMacaulayMatrix.rank (IntegralMixedVirtualTaskBits.family P F) q))
    (hr : get P .row q = r.val) (ht : get P .col q = t.val)
    (hq : MacaulayIntegralEntryRequest.request (layout P F) (packet P q)) :
    IntegralMixedValueReciprocalMatrix.value P F (query P F q) =
      coefficientReference P F q r t (queryPacket P F q) := by
  let j : Fin ((layout P F).arity q) := ⟨sourceRow P F q, sourceRow_lt P F q hq⟩
  let k : Fin (count ((layout P F).arity q) ((layout P F).width q)) := ⟨difference P F q, difference_lt P F q⟩
  have HP : queryPacket P F q = MacaulayFullBoxBits.entryPacket q j.val k.val r.val t.val := by
    rw [queryPacket_eq, hr, ht]
  rw [HP, coefficient_packet]
  have HS := IntegralMixedValueReciprocalSnapshot.macaulay_child P F g q
  rw [hr, ht] at HS
  have HE := HS.trans (congrArg (fun z : ℤ => residueBits (z : ZMod (modulus P q)))
    (IntegralMixedValueReciprocalSnapshot.parent_entry P F q j k r t))
  unfold IntegralMixedValueReciprocalMatrix.entry at HE
  rw [nativeExponent_refl] at HE
  exact HE

end LeanCanny.Algebra.IntegralMixedValueMacaulayChildren
