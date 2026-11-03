/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalHeightPackets
/-! # Weighted affine height coefficients from the actual current model

The old matrix packets use exactly the caller modulus already budgeted in the
source task. Powers remain implicit; no weighted row polynomial is serialized.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedPhysicalHeightBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask FixedWidthPolynomial
open IntegralMixedFramedHistoryFamilyBits (Plan)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

 def modulusWord (P : Parameters) (q : List Bool) := BinaryNatCode.encode (modulus P q-1)
theorem modulusWord_FP (P : Parameters) (a : Access P) : modulusWord P∈FP :=
  ((modulus_binary P a).sub (BinaryFn.const 1)).bits_mem_FP

theorem modulusWord_value (P : Parameters) (q : List Bool) : Nat.fromBitsLE (modulusWord P q)+1=modulus P q := by
  simp only [modulusWord,BinaryNatCode.encode,Nat.fromBitsLE_bits]
  have H:=modulus_ne_zero P q
  omega

theorem powered_evaluator (P : Parameters) (a : Access P) (D : Plan P)
    (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (c : IntegralMixedFramedCurrentQNativeBits.Controls P D J)
    (hb : IntegralMixedFramedCurrentQNativeBits.Bounds P D J c)
    (V : List Bool→ℕ) (hV : UnaryFn V) (target : List Bool→List Bool) (ht : target∈FP) :
    SpaceFunction (FixedWidthRowBits.value (family P D J).arity V
      ((family P D J).poweredPolynomial (fun q=>P.cap (RankedHistoryTask.root q)+1)) target (modulusWord P)) := by
  apply IntegralCoordinateCoefficientBits.powered_evaluator_local (family P D J)
    (fun q=>P.cap (RankedHistoryTask.root q)+1) V target (modulusWord P) (entry P a D J c)
    ((a.cap.comp RankedHistoryTask.root_FP).add (UnaryFn.const 1)) (arity_unary P a D J) (width_unary P a D J)
    hV ht (modulusWord_FP P a) (entry_space P a D J c hb)
  intro q r t
  have HE:=entry_packet P a D J c q (modulusWord P q) r t
  exact HE.trans (congrArg₂ (fun (z : ℤ) (m : ℕ)=>residueBits (z : ZMod m)) rfl (modulusWord_value P q).symm)

end LeanCanny.Algebra.IntegralMixedFramedPhysicalHeightBits
