/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedCriticalGuardQueries
public import LeanCanny.Algebra.FixedWidthMonomialSpace
/-! # Native coefficients of the actual critical scalar/physical guard

The two powers stay binary. The only charged scalar is the literal retained
integer denominator, supplied by the verified original current-Q backend.
Negative or nonunit leading residues require no inverse operation.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedCriticalGuardBits
open LeanCanny LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask MatrixPower
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open IntegralMixedHeaderTablesBits (Tables)
open IntegralMixedFramedCompanionUniformBits (lifted liftedPlan)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family

noncomputable def atKey (G : IntegralMixedCutSource.Family) (key : List Bool) (i : ℕ) : ℤ :=
  if hi : i<G.birth key then (G.state key).bank.denominator ⟨i,hi⟩ else 0

private theorem integerAt_base (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (q : List Bool) (i : ℕ) : IntegralMixedFramedBankDenominatorBits.integerAt P D H q i=
      atKey (family P D H) (PaddedIntegralGeneratorSource.base q) i := rfl

noncomputable def denominator (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool→List Bool) (stage : List Bool→ℕ) (q : List Bool) : ℤ :=
  atKey (family P D H) (key q) (age P key stage q)

attribute [local irreducible] atKey

theorem denominator_packet (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool→List Bool) (stage : List Bool→ℕ) (modulus : List Bool→List Bool) (q : List Bool) :
    IntegralMixedFramedBankDenominatorBits.value P D H (denominatorPacket P key stage modulus q)=
      residueBits (denominator P D H key stage q : ZMod (Nat.fromBitsLE (modulus q)+1)) := by
  have HM : IntegralMixedFramedCompanionQueryBits.callerModulus (denominatorPacket P key stage modulus q)=
      Nat.fromBitsLE (modulus q)+1 := by
    simp only [IntegralMixedFramedCompanionQueryBits.callerModulus,denominatorPacket,
      PaddedIntegralGeneratorSource.modulus,pairFst_pair,pairSnd_pair]
  unfold IntegralMixedFramedBankDenominatorBits.value
  rw [HM,integerAt_base]
  simp only [denominator,denominatorPacket,IntegralMixedFramedBankDenominatorBits.index,
    PaddedIntegralGeneratorSource.row,PaddedIntegralGeneratorSource.base,pairFst_pair,pairSnd_pair,
    BinaryNatCode.encode,Nat.fromBitsLE_bits]

noncomputable def rawPolynomial (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (T : Tables) (key : List Bool→List Bool) (stage : List Bool→ℕ) (q : List Bool) : MvPolynomial (Fin (count P T key q)) ℤ :=
  FixedWidthMonomialBits.polynomial (count P T key) (scalar P T key stage) (scalarPower P key stage) (fun _=>1) q -
    FixedWidthMonomialBits.polynomial (count P T key) (physical P T key stage) (physicalPower P key stage)
      (denominator P D H key stage) q
noncomputable def polynomial (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (T : Tables) (key : List Bool→List Bool) (stage : List Bool→ℕ) (q : List Bool) : MvPolynomial (Fin (count P T key q)) ℤ :=
  if Active P T key stage q then rawPolynomial P D H T key stage q else 0

private theorem one_evaluator (modulus : List Bool→List Bool) (hm : modulus∈FP) :
    SpaceFunction (fun q=>residueBits (1 : ZMod (Nat.fromBitsLE (modulus q)+1))) := by
  have HM:BinaryFn (fun q=>Nat.fromBitsLE (modulus q)+1) := (BinaryFn.fromBits hm).add (BinaryFn.const 1)
  exact (SpaceFunction.ofFP _ (mem_FP_comp HM.bits_mem_FP ArithmeticBits.one_mem_FP)).congr
    (funext fun q=>ArithmeticBits.one_residueBits _)

theorem coefficient_evaluator (P : Parameters) (a : Access P) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (Hnew : IntegralMixedFramedHistoryFamilyBits.Data (lifted P) (liftedPlan P D))
    (c : IntegralMixedFramedCurrentQNativeBits.Controls (lifted P) (liftedPlan P D) Hnew)
    (hb : IntegralMixedFramedCurrentQNativeBits.Bounds (lifted P) (liftedPlan P D) Hnew c)
    (T : Tables) (hT : IntegralMixedHeaderTablesBits.Access T)
    (key : List Bool→List Bool) (stage W : List Bool→ℕ) (target modulus : List Bool→List Bool)
    (hk : key∈FP) (hj : UnaryFn stage) (hW : UnaryFn W) (ht : target∈FP) (hm : modulus∈FP) :
    SpaceFunction (FixedWidthRowBits.value (count P T key) W (polynomial P D H T key stage) target modulus) := by
  have HA:=count_unary P a T hT key hk
  have ES:=FixedWidthMonomialBits.coefficient_evaluator (count P T key) W
    (scalar P T key stage) (scalarPower P key stage) target (fun _=>1) modulus
    (fun q=>residueBits (1 : ZMod (Nat.fromBitsLE (modulus q)+1))) (one_evaluator modulus hm)
    (fun _=>rfl) HA hW (BinaryFn.ofUnary (scalar_unary P a T hT key stage hk hj))
    (scalarPower_binary P a key stage hk hj) ht
  have ED:=((IntegralMixedFramedCurrentQBankProductBits.denominator_evaluator P a D H Hnew c hb).precompose
    (denominatorPacket P key stage modulus) (denominatorPacket_FP P a key stage modulus hk hj hm)).congr
    (funext fun q=>denominator_packet P D H key stage modulus q)
  have EP:=FixedWidthMonomialBits.coefficient_evaluator (count P T key) W
    (physical P T key stage) (physicalPower P key stage) target (denominator P D H key stage) modulus
    (fun q=>residueBits (denominator P D H key stage q : ZMod (Nat.fromBitsLE (modulus q)+1))) ED
    (fun _=>rfl) HA hW (physical_binary P a T hT key stage hk hj)
    (physicalPower_binary P a key stage hk hj) ht
  have ER:=FixedWidthRowBits.sub_evaluator _ W _ _ target modulus hm ES EP
  exact FixedWidthRowBits.guarded_evaluator _ W (rawPolynomial P D H T key stage) target modulus
    (FixedWidthRowBits.value _ W (rawPolynomial P D H T key stage) target modulus)
    (Active P T key stage) (active_FP P a T hT key stage hk hj) ER (fun _ _=>rfl)
end LeanCanny.Algebra.IntegralMixedFramedCriticalGuardBits
