/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderCriticalBankEquality
public import LeanCanny.Algebra.IntegralMixedFramedCoordinateCharacteristicActual
public import LeanCanny.Algebra.ThomEncoding
public import LeanCanny.Encoding.IntegralFramedPhysicalBankPolynomial
/-! # The streamed derivative scan is exactly equality of every old quotient -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderCriticalBankEquality
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open FormulaSignSlotRadialProviderCriticalPrefixes (birth key key_birth positive input)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "NB" => FormulaSignSlotRadialProviderRecordPlan.bank
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.bank IntegralMixedFramedHistoryFamilyBits.family

theorem coordinate_val (child : Bool) (q : List Bool) (i k : ℕ) (hi : i<birth false q) :
    (coordinate child q (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k))).val=
      i+(if child then 1 else 0) := by
  simp only [coordinate,selected,pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits,
    min_eq_left (by omega : i≤birth false q-1)]

noncomputable def point (child : Bool) (q w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (input child) q w) (i : ℕ) : ℝ :=
  IntegralFramedPhysicalSquare.point (NB).parameters (NB).plan
    (NB).data (NB).nodes (NB).factor
    (NB).seed (NB).bounds (key child)
    (positive child) q w hv
    (coordinate child q (pair (BinaryNatCode.encode i) (BinaryNatCode.encode 0)))

theorem derivative_polynomial (q : List Bool) (i k : ℕ) :
    (derivatives).polynomial (pair q (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k)))=
      Polynomial.derivative^[k] ((source).polynomial (pair q (BinaryNatCode.encode i))) := by
  simp only [derivatives,IntegerPolynomialSourceChoice.reindex,Function.comp_apply,regroup,
    pairFst_pair,pairSnd_pair]
  exact IntegerPolynomialIteratedDerivativeBits.packet (source) _ k

attribute [local irreducible] originalSource source derivatives coordinate point

private noncomputable def naturalPolynomial (B : IntegralFramedBankQuery.Bank) (k : List Bool) (i : ℕ) : Polynomial ℤ :=
  if hi : i<(IntegralMixedFramedHistoryFamilyBits.family B.parameters B.plan B.data).birth k then
    IntegralMixedBankCoordinatePolynomial.polynomial
      ((IntegralMixedFramedHistoryFamilyBits.family B.parameters B.plan B.data).state k) ⟨i,hi⟩ else 0

theorem value_packet (child : Bool) (q w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (input child) q w) (i k : ℕ) :
    value child (pair (pair q w) (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k)))=
      InfinitesimalSign.encode (ThomEncoding.sign
        (((source).polynomial (pair q (BinaryNatCode.encode i))).map (Int.castRingHom ℝ))
        (point child q w hv i) k) :=by
  have HC : coordinate child q (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k))=
      coordinate child q (pair (BinaryNatCode.encode i) (BinaryNatCode.encode 0)) :=by
    apply Fin.ext
    simp only [coordinate,selected,pairFst_pair,pairSnd_pair]
  have HP:=IntegralFramedPhysicalUnivariateTest.packet
    (NB).parameters (NB).plan (NB).data
    (NB).nodes (NB).factor (NB).seed
    (NB).bounds (key child) (positive child)
    (coordinate child) (derivatives) q w
    (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k)) hv
  rw [derivative_polynomial,HC] at HP
  simpa only [value,point,ThomEncoding.sign,Polynomial.iterate_derivative_map,Polynomial.eval_map] using HP

theorem source_nonzero (q : List Bool) (i : ℕ) :
    (source).polynomial (pair q (BinaryNatCode.encode i))≠0 :=by
  simpa only [source,originalSource,FormulaSignSlotRadialProviderFieldEquality.originalSource,IntegerPolynomialSourceChoice.reindex,Function.comp_apply,
    IntegralMixedFramedCoordinateCharacteristicBits.rootSource] using
    IntegralMixedFramedCoordinateCharacteristicBits.nonzero (NB).parameters
      (NB).plan (NB).data (saved (pair q (BinaryNatCode.encode i)))

theorem parent_root (q w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (input false) q w)
    (i : ℕ) (hi : i<birth false q) :
    ((source).polynomial (pair q (BinaryNatCode.encode i))).eval₂ (Int.castRingHom ℝ)
      (point false q w hv i)=0 :=by
  let B:=NB
  let ctx:=pair (key false q) (BinaryNatCode.encode i)
  have HK : IntegralMixedFramedCoordinateCharacteristicBits.key ctx=key false q :=by
    simp only [IntegralMixedFramedCoordinateCharacteristicBits.key,ctx,pairFst_pair]
  have HC : IntegralMixedFramedCoordinateCharacteristicBits.count B.parameters B.plan B.data ctx=
      birth false q :=by
    unfold IntegralMixedFramedCoordinateCharacteristicBits.count
    rw [HK]
    exact key_birth false q
  have HI : IntegralMixedFramedCoordinateCharacteristicBits.index ctx<
      IntegralMixedFramedCoordinateCharacteristicBits.count B.parameters B.plan B.data ctx :=by
    rw [HC]
    simpa only [IntegralMixedFramedCoordinateCharacteristicBits.index,ctx,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits] using hi
  have HA : IntegralMixedFramedCoordinateCharacteristicBits.Active B.parameters ctx :=by
    unfold IntegralMixedFramedCoordinateCharacteristicBits.Active
    rw [HK]
    have HB := (IntegralMixedFramedHistoryFamilyBits.family_birth B.parameters B.plan B.data
      (key false q)).symm.trans (key_birth false q)
    rw [HB]
    simp only [key,IntegralMixedFramedHistoryFamilyBits.keyAt,pairFst_pair]
    exact FormulaSignSlotRadialProviderCriticalPrefixes.below_cap false q
  have HI' : i<(IntegralMixedFramedHistoryFamilyBits.family B.parameters B.plan B.data).birth (key false q) :=by
    rw [key_birth]
    exact hi
  have HE : (⟨i,HI'⟩ :
      Fin ((IntegralMixedFramedHistoryFamilyBits.family B.parameters B.plan B.data).birth (key false q)))=
      coordinate false q (pair (BinaryNatCode.encode i) (BinaryNatCode.encode 0)) :=by
    apply Fin.ext
    rw [coordinate_val false q i 0 hi]
    simp only [Bool.false_eq_true,ite_false,Nat.add_zero]
  have HN : IntegralMixedFramedCoordinateCharacteristicBits.polynomial B.parameters B.plan B.data ctx=
      naturalPolynomial B (IntegralMixedFramedCoordinateCharacteristicBits.key ctx)
        (IntegralMixedFramedCoordinateCharacteristicBits.index ctx) :=by
    have HI0 : IntegralMixedFramedCoordinateCharacteristicBits.index ctx <
        (IntegralMixedFramedHistoryFamilyBits.family B.parameters B.plan B.data).birth
          (IntegralMixedFramedCoordinateCharacteristicBits.key ctx) := HI
    rw [naturalPolynomial,dite_eq_left HI0]
    exact IntegralMixedFramedCoordinateCharacteristicBits.polynomial_actual B.parameters B.plan B.data ctx HA HI
  have HIndex : IntegralMixedFramedCoordinateCharacteristicBits.index ctx=i :=by
    simp only [IntegralMixedFramedCoordinateCharacteristicBits.index,ctx,pairSnd_pair,
      BinaryNatCode.encode,Nat.fromBitsLE_bits]
  have HP : (source).polynomial (pair q (BinaryNatCode.encode i))=
      naturalPolynomial B (key false q) i :=by
    have HD : (source).polynomial (pair q (BinaryNatCode.encode i))=
        IntegralMixedFramedCoordinateCharacteristicBits.polynomial B.parameters B.plan B.data ctx :=by
      simp only [source,originalSource,FormulaSignSlotRadialProviderFieldEquality.originalSource,IntegerPolynomialSourceChoice.reindex,Function.comp_apply,
        IntegralMixedFramedCoordinateCharacteristicBits.rootSource,saved,pairFst_pair,pairSnd_pair,ctx,B]
    exact HD.trans (HN.trans (congrArg₂ (naturalPolynomial B) HK HIndex))
  rw [HP,naturalPolynomial,dite_eq_left HI']
  have HR:=IntegralFramedPhysicalSquare.bank_polynomial_root B.parameters B.plan B.data
    B.nodes B.factor B.seed B.bounds (key false) (positive false) q w hv ⟨i,HI'⟩
  simpa only [point,←HE] using HR

theorem coordinate_iff (q v : List Bool)
    (hp : SquareSampleCompleteVertices.Valid (input false) q
      (IntegralMixedPhysicalCriticalQuery.parentWord q))
    (hv : SquareSampleCompleteVertices.Valid (input true) q v)
    (i : ℕ) (hi : i<birth false q) :
    (∀k<degree (pair (pair q v) (List.replicate i true))+1,
      value false (probe false (pair (pair (pair q v) (List.replicate i true)) (BinaryNatCode.encode k)))=
        value true (probe true (pair (pair (pair q v) (List.replicate i true)) (BinaryNatCode.encode k)))) ↔
      point false q (IntegralMixedPhysicalCriticalQuery.parentWord q) hp i=
        point true q v hv i :=by
  simp only [probe,pairFst_pair,pairSnd_pair,List.length_replicate,Bool.false_eq_true,ite_true,ite_false]
  simp_rw [value_packet false q _ hp,value_packet true q v hv,
    SquareSampleTestSign.encode_eq_iff]
  let p:=((source).polynomial (pair q (BinaryNatCode.encode i))).map (Int.castRingHom ℝ)
  let a:=point false q (IntegralMixedPhysicalCriticalQuery.parentWord q) hp i
  let b:=point true q v hv i
  have HA:p.eval a=0:=by rw [Polynomial.eval_map];exact parent_root q _ hp i hi
  have HD:p.natDegree≤degree (pair (pair q v) (List.replicate i true)) :=by
    apply Polynomial.natDegree_map_le.trans
    simpa only [degree,pairFst_pair,pairSnd_pair,List.length_replicate] using
      (source).degree_bound (pair q (BinaryNatCode.encode i))
  constructor
  · intro hs
    have HB:SignType.sign (p.eval b)=0:=by
      have H0:=hs 0 (by omega)
      change ThomEncoding.sign p a 0=ThomEncoding.sign p b 0 at H0
      simpa only [ThomEncoding.sign,Function.iterate_zero_apply,HA,sign_zero] using H0.symm
    exact ThomEncoding.root_eq p ((Polynomial.map_ne_zero_iff Int.cast_injective).mpr
      (source_nonzero q i)) _ HD a b HA (sign_eq_zero_iff.mp HB) (fun k hk=>hs k (by omega))
  · intro he k _
    rw [he]

theorem agrees_iff (q v : List Bool)
    (hp : SquareSampleCompleteVertices.Valid (input false) q (IntegralMixedPhysicalCriticalQuery.parentWord q))
    (hv : SquareSampleCompleteVertices.Valid (input true) q v) :
    agrees (pair q v) ↔
      ∀i<birth false q,
        point false q (IntegralMixedPhysicalCriticalQuery.parentWord q) hp i=
          point true q v hv i :=by
  simp only [agrees,pairFst_pair]
  constructor
  · intro H i hi
    exact (coordinate_iff q v hp hv i hi).mp (H i hi)
  · intro H i hi
    exact (coordinate_iff q v hp hv i hi).mpr (H i hi)

end LeanCanny.Encoding.FormulaSignSlotRadialProviderCriticalBankEquality
