/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedIntegerProducerNative
public import LeanCanny.Algebra.IntegralIntegerCompanionSpace
/-! # Actual integer producer arithmetic charges original degree and coefficients

The original integer polynomial is read from the creating command. Neither
its exact degree nor its coefficient residues are assumed polynomial time.
The old coefficient algebra contributes only its canonical scalar identity
matrices, so this construction assumes no old-history matrix evaluator.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedIntegerProducerSpaceBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open scoped Classical

noncomputable def polynomial (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool) : Polynomial ℤ :=
  IntegralMixedIntegerProducerBits.polynomial P D (IntegralMixedVirtualTaskBits.saved P q)
noncomputable def degreeWord (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool) : List Bool :=
  BinaryNatCode.encode (polynomial P D q).natDegree

structure Original (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) : Prop where
  degree : SpaceFunction (degreeWord P D)
  coefficient : SpaceFunction (PrimitivePairBits.coefficient (polynomial P D))

theorem controls (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) :
    IntegralIntegerCompanionBits.Controls (IntegralMixedIntegerProducerBits.family P D) where
  width := IntegralMixedIntegerProducerBits.width_unary P a D
  modulus := modulus_binary P a
  row := (get_binary P a .row).mod (IntegralMixedIntegerProducerBits.newRank_binary P a D)
  col := (get_binary P a .col).mod (IntegralMixedIntegerProducerBits.newRank_binary P a D)

theorem companion_evaluator (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Original P D) :
    SpaceFunction (IntegralMixedIntegerProducerBits.companionValue P D) :=
  IntegralIntegerCompanionBits.evaluator (IntegralMixedIntegerProducerBits.family P D) (polynomial P D)
    (fun _ => rfl) (fun _ => rfl) (controls P a D) (degreeWord P D) h.degree (fun _ => rfl) h.coefficient

theorem leading_evaluator (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Original P D) :
    SpaceFunction (IntegralMixedIntegerProducerBits.leadingValue P D) := by
  have E := IntegralIntegerCompanionBits.leading_evaluator (IntegralMixedIntegerProducerBits.family P D) (polynomial P D)
    (controls P a D) (degreeWord P D) h.degree h.coefficient
  refine E.congr (funext fun q => ?_)
  exact IntegralIntegerCompanionBits.leadingReader_eq (IntegralMixedIntegerProducerBits.family P D) (polynomial P D)
    (fun _ => rfl) (degreeWord P D) (fun _ => rfl) q

def coefficientPacket (P : Parameters) (q : List Bool) : List Bool :=
  pair (pair q (BinaryNatCode.encode (get P .coefficient q))) (BinaryNatCode.encode (modulus P q - 1))
theorem coefficientPacket_FP (P : Parameters) (a : Access P) : coefficientPacket P ∈ FP :=
  mem_FP_pair (mem_FP_pair id_mem_FP (get_binary P a .coefficient).bits_mem_FP)
    ((modulus_binary P a).sub (BinaryFn.const 1)).bits_mem_FP

theorem raw_evaluator (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Original P D) :
    SpaceFunction (IntegralMixedIntegerProducerBits.rawScalar P D) := by
  refine (h.coefficient.precompose (coefficientPacket P) (coefficientPacket_FP P a)).congr (funext fun q => ?_)
  exact IntegerPolynomialRootQueriesBits.coefficient_packet (polynomial P D) q (get P .coefficient q)
    (modulus P q) (Nat.pos_of_ne_zero (modulus_ne_zero P q))

theorem coefficient_evaluator (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Original P D) :
    SpaceFunction (IntegralMixedIntegerProducerBits.coefficientValue P D) := by
  have H := ((get_binary P a .row).mod (IntegralMixedIntegerProducerBits.oldRank_binary P a D)).eq
    ((get_binary P a .col).mod (IntegralMixedIntegerProducerBits.oldRank_binary P a D))
  exact (SpaceFunction.branch _ H.flag_mem_FP (raw_evaluator P a D h) (SpaceFunction.ofFP _ (constFn_mem_FP []))).congr
    (funext fun q => by simp only [IntegralMixedIntegerProducerBits.coefficientValue, decide_eq_true_eq])

end LeanCanny.Algebra.IntegralMixedIntegerProducerSpaceBits
