/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderFieldEquality
public import LeanCanny.Algebra.IntegralMixedFramedCoordinateCharacteristicActual
public import LeanCanny.Algebra.ThomEncoding
public import LeanCanny.Encoding.IntegralFramedPhysicalBankPolynomial
public import LeanCanny.Encoding.IntegralFramedPhysicalBankChronologicalPoint
/-! # The left characteristic polynomial identifies values across two contexts -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderFieldEquality
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (family)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "B" => FormulaSignSlotRadialProviderRecordPlan.bank
local notation "P" => IntegralFramedBankQuery.Bank.parameters B
local notation "D" => IntegralFramedBankQuery.Bank.plan B
local notation "H" => IntegralFramedBankQuery.Bank.data B
local notation "G" => family P D H
local notation "S" => FormulaSignSlotRadialProviderAtomic.input

private theorem snapshot_count (Q : Parameters) (E : IntegralMixedFramedHistoryFamilyBits.Plan Q)
    (J : IntegralMixedFramedHistoryFamilyBits.Data Q E) (k : List Bool) :
    (IntegralMixedFramedBankSnapshotBits.atKey Q E J k).count=(family Q E J).birth k := rfl

theorem count_eq (c : List Bool) : count c=FormulaSignSlotRadialProviderRecordPlan.fullCount (pairFst c) := by
  unfold count
  rw [←snapshot_count]
  simpa only [FormulaSignSlotRadialProviderRecordPlan.bank] using
    FormulaSignSlotRadialProviderRecordPlan.bank_count c

theorem key_root (c : List Bool) : pairFst ((B).key c)=pairFst c := by
  change pairFst (FormulaSignSlotRadialProviderRecordPlan.bankKey c)=_
  simp only [FormulaSignSlotRadialProviderRecordPlan.bankKey,IntegralMixedFramedHistoryFamilyBits.keyAt,pairFst_pair]

theorem below_cap (c : List Bool) : IntegralMixedFramedHistoryFamilyBits.prefixLength P ((B).key c)<
    (P).cap (pairFst ((B).key c)) := by
  rw [←IntegralMixedFramedHistoryFamilyBits.family_birth P D H,key_root c]
  change count c<_
  rw [count_eq]
  change FormulaSignSlotRadialProviderRecordPlan.fullCount (pairFst c)<
    FormulaSignSlotRadialProviderRecordPlan.fullCount (pairFst c)+2
  omega

attribute [local irreducible] family originalSource derivatives coordinate value
  IntegralFramedPhysicalUnivariateTest.value IntegralMixedBankCoordinatePolynomial.polynomial
  IntegralFramedPhysicalSquare.point

private theorem decode_encode (k : ℕ) : Nat.fromBitsLE (BinaryNatCode.encode k)=k:=Nat.fromBitsLE_bits k

noncomputable def pointNewest (c w : List Bool) (hv : SquareSampleCompleteVertices.Valid S c w) (i : ℕ) : ℝ :=
  IntegralFramedPhysicalSquare.point P D H (B).nodes (B).factor (B).seed (B).bounds (B).key (B).positive c w hv
    ⟨min i (count c-1),by
      change min i (count c-1)<count c
      have HP:=count_pos c
      omega⟩
noncomputable def point (c w : List Bool) (hv : SquareSampleCompleteVertices.Valid S c w) (chronological : ℕ) :=
  pointNewest c w hv (newest (count c) chronological)
attribute [local irreducible] pointNewest

theorem point_env (c w : List Bool) (hv : SquareSampleCompleteVertices.Valid S c w)
    (i : ℕ) (hi : i<count c) : point c w hv i=
      IntegralFramedPhysicalBankTerm.env B FormulaSignSlotRadialProviderRecordPlan.tables
        FormulaSignSlotRadialProviderAtomic.bank_represents c w hv i := by
  rw [IntegralFramedPhysicalBankTerm.env_chronological B FormulaSignSlotRadialProviderRecordPlan.tables
    FormulaSignSlotRadialProviderAtomic.bank_represents c w hv i hi]
  unfold point pointNewest
  apply congrArg (IntegralFramedPhysicalSquare.point P D H (B).nodes (B).factor (B).seed (B).bounds
    (B).key (B).positive c w hv)
  apply Fin.ext
  change min (newest (count c) i) (count c-1)=count c-1-i
  unfold newest
  omega

theorem derivative_polynomial (c arg : List Bool) (i k : ℕ) :
    (derivatives).polynomial (pair c (pair arg (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k))))=
      Polynomial.derivative^[k] ((originalSource).polynomial arg) :=by
  simp only [derivatives,IntegerPolynomialSourceChoice.reindex,Function.comp_apply,derivativePacket,
    pairFst_pair,pairSnd_pair]
  exact IntegerPolynomialIteratedDerivativeBits.packet (originalSource) arg k

theorem value_packet (c w arg : List Bool) (hv : SquareSampleCompleteVertices.Valid S c w) (i k : ℕ) :
    value (pair (pair c w) (pair arg (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k))))=
      InfinitesimalSign.encode (ThomEncoding.sign (((originalSource).polynomial arg).map (Int.castRingHom ℝ))
        (pointNewest c w hv i) k) :=by
  unfold value
  have HP:=IntegralFramedPhysicalUnivariateTest.packet P D H (B).nodes (B).factor (B).seed (B).bounds
    (B).key (B).positive (coordinate) (derivatives) c w
    (pair arg (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k))) hv
  have HC : IntegralFramedPhysicalSquare.point P D H (B).nodes (B).factor (B).seed (B).bounds (B).key (B).positive
      c w hv (coordinate c (pair arg (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k))))=
        pointNewest c w hv i :=by
    unfold pointNewest
    apply congrArg (IntegralFramedPhysicalSquare.point P D H (B).nodes (B).factor (B).seed (B).bounds (B).key (B).positive c w hv)
    apply Fin.ext
    simp only [coordinate,pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits]
  have HE:=congrArg₂ (fun (p : Polynomial ℤ) (v : ℝ)=>p.eval₂ (Int.castRingHom ℝ) v)
    (derivative_polynomial c arg i k) HC
  exact (HP.trans (congrArg (fun v : ℝ=>InfinitesimalSign.encode (SignType.sign v)) HE)).trans
    (by simp only [ThomEncoding.sign,Polynomial.iterate_derivative_map,Polynomial.eval_map])

private noncomputable def naturalPolynomial (bankData : IntegralFramedBankQuery.Bank) (key : List Bool) (i : ℕ) : Polynomial ℤ :=
  if hi : i<(family bankData.parameters bankData.plan bankData.data).birth key then
    IntegralMixedBankCoordinatePolynomial.polynomial ((family bankData.parameters bankData.plan bankData.data).state key) ⟨i,hi⟩ else 0

theorem source_nonzero (arg : List Bool) : (originalSource).polynomial arg≠0 :=by
  simpa only [originalSource,
    IntegralMixedFramedCoordinateCharacteristicBits.rootSource] using
      IntegralMixedFramedCoordinateCharacteristicBits.nonzero P D H arg

private theorem source_polynomial (c : List Bool) (i : ℕ) (hi : i<count c) :
    (originalSource).polynomial (pair ((B).key c) (BinaryNatCode.encode i))=
      naturalPolynomial B ((B).key c) i :=by
  let arg:=pair ((B).key c) (BinaryNatCode.encode i)
  have HA : IntegralMixedFramedCoordinateCharacteristicBits.Active P arg :=by
    simp only [IntegralMixedFramedCoordinateCharacteristicBits.Active,IntegralMixedFramedCoordinateCharacteristicBits.key,arg,pairFst_pair]
    exact below_cap c
  have HI : IntegralMixedFramedCoordinateCharacteristicBits.index arg<IntegralMixedFramedCoordinateCharacteristicBits.count P D H arg :=by
    simpa only [IntegralMixedFramedCoordinateCharacteristicBits.index,IntegralMixedFramedCoordinateCharacteristicBits.count,
      IntegralMixedFramedCoordinateCharacteristicBits.key,IntegralMixedFramedCoordinateCharacteristicBits.family,
      count,arg,pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits] using hi
  have HN : IntegralMixedFramedCoordinateCharacteristicBits.polynomial P D H arg=
      naturalPolynomial B (IntegralMixedFramedCoordinateCharacteristicBits.key arg) (IntegralMixedFramedCoordinateCharacteristicBits.index arg) :=by
    have HI0 : IntegralMixedFramedCoordinateCharacteristicBits.index arg<(G).birth
        (IntegralMixedFramedCoordinateCharacteristicBits.key arg) :=HI
    rw [naturalPolynomial,dite_eq_left HI0]
    exact IntegralMixedFramedCoordinateCharacteristicBits.polynomial_actual P D H arg HA HI
  have HE : (originalSource).polynomial arg=IntegralMixedFramedCoordinateCharacteristicBits.polynomial P D H arg :=by
    simp only [originalSource,
      IntegralMixedFramedCoordinateCharacteristicBits.rootSource]
  exact HE.trans (HN.trans (congrArg₂ (naturalPolynomial B)
    (by simp only [IntegralMixedFramedCoordinateCharacteristicBits.key,arg,pairFst_pair])
    (by simp only [IntegralMixedFramedCoordinateCharacteristicBits.index,arg,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits])))

private theorem bank_root (c w : List Bool) (hv : SquareSampleCompleteVertices.Valid S c w) (i : ℕ)
    (hi : i<count c) :
    (IntegralMixedBankCoordinatePolynomial.polynomial ((G).state ((B).key c)) ⟨i,hi⟩).eval₂
      (Int.castRingHom ℝ) (pointNewest c w hv i)=0 :=by
  have hi' : i<(G).birth ((B).key c):=hi
  have HC : pointNewest c w hv i=IntegralFramedPhysicalSquare.point P D H
      (B).nodes (B).factor (B).seed (B).bounds (B).key (B).positive c w hv ⟨i,hi'⟩ :=by
    unfold pointNewest
    apply congrArg (IntegralFramedPhysicalSquare.point P D H (B).nodes (B).factor (B).seed (B).bounds
      (B).key (B).positive c w hv)
    apply Fin.ext
    exact min_eq_left (by omega)
  exact (congrArg (fun v : ℝ=>(IntegralMixedBankCoordinatePolynomial.polynomial ((G).state ((B).key c)) ⟨i,hi'⟩).eval₂
    (Int.castRingHom ℝ) v) HC).trans (IntegralFramedPhysicalSquare.bank_polynomial_root P D H
      (B).nodes (B).factor (B).seed (B).bounds (B).key (B).positive c w hv ⟨i,hi'⟩)

theorem left_root (c w : List Bool) (hv : SquareSampleCompleteVertices.Valid S c w) (i : ℕ)
    (hi : i<count c) :
    ((originalSource).polynomial (pair ((B).key c) (BinaryNatCode.encode i))).eval₂
      (Int.castRingHom ℝ) (pointNewest c w hv i)=0 :=by
  have HP:=source_polynomial c i hi
  have HE : (originalSource).polynomial (pair ((B).key c) (BinaryNatCode.encode i))=
      IntegralMixedBankCoordinatePolynomial.polynomial ((G).state ((B).key c)) ⟨i,hi⟩ :=
    HP.trans (dite_eq_left hi)
  exact (congrArg (fun p : Polynomial ℤ=>p.eval₂ (Int.castRingHom ℝ) (pointNewest c w hv i)) HE).trans
    (bank_root c w hv i hi)

theorem oldArgument_packet (cL wL cR wR : List Bool) (a b : ℕ) :
    oldArgument (packet cL wL cR wR a b)=
      pair ((B).key cL) (BinaryNatCode.encode (newest (count cL) a)) :=by
  simp only [oldArgument,selected,context,sample,label,labelWord,packet,
    Bool.false_eq_true,ite_false,pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits]

theorem agrees_iff (cL wL cR wR : List Bool)
    (hL : SquareSampleCompleteVertices.Valid S cL wL) (hR' : SquareSampleCompleteVertices.Valid S cR wR) (a b : ℕ) :
    agrees (packet cL wL cR wR a b) ↔ point cL wL hL a=point cR wR hR' b :=by
  let arg:=pair ((B).key cL) (BinaryNatCode.encode (newest (count cL) a))
  have HN : agrees (packet cL wL cR wR a b) ↔
      ∀k<(originalSource).degree arg+1,
        ThomEncoding.sign (((originalSource).polynomial arg).map (Int.castRingHom ℝ)) (point cL wL hL a) k=
        ThomEncoding.sign (((originalSource).polynomial arg).map (Int.castRingHom ℝ)) (point cR wR hR' b) k :=by
    simp only [agrees,degree,probe,oldArgument,selected,context,sample,label,labelWord,packet,
      Bool.false_eq_true,ite_false,ite_true,pairFst_pair,pairSnd_pair,decode_encode]
    dsimp only [arg]
    simp_rw [value_packet cL wL (pair ((B).key cL) (BinaryNatCode.encode (newest (count cL) a))) hL,
      value_packet cR wR (pair ((B).key cL) (BinaryNatCode.encode (newest (count cL) a))) hR',
      SquareSampleTestSign.encode_eq_iff]
    rfl
  rw [HN]
  let p:=((originalSource).polynomial arg).map (Int.castRingHom ℝ)
  have HA : p.eval (point cL wL hL a)=0 :=by
    rw [Polynomial.eval_map]
    exact left_root cL wL hL _ (newest_lt _ _ (count_pos cL))
  have HD : p.natDegree≤(originalSource).degree arg :=
    Polynomial.natDegree_map_le.trans ((originalSource).degree_bound arg)
  constructor
  · intro hs
    have HB : SignType.sign (p.eval (point cR wR hR' b))=0 :=by
      have H0:=hs 0 (by omega)
      change ThomEncoding.sign p _ 0=ThomEncoding.sign p _ 0 at H0
      simpa only [ThomEncoding.sign,Function.iterate_zero_apply,HA,sign_zero] using H0.symm
    exact ThomEncoding.root_eq p ((Polynomial.map_ne_zero_iff Int.cast_injective).mpr (source_nonzero arg)) _ HD
      _ _ HA (sign_eq_zero_iff.mp HB) (fun k hk=>hs k (by omega))
  · intro he k _
    rw [he]

theorem language_packet_iff (cL wL cR wR : List Bool)
    (hL : SquareSampleCompleteVertices.Valid S cL wL) (hR' : SquareSampleCompleteVertices.Valid S cR wR) (a b : ℕ)
    (ha' : a<count cL) (hb : b<count cR) :
    packet cL wL cR wR a b∈language ↔point cL wL hL a=point cR wR hR' b :=by
  have HW : Wellformed (packet cL wL cR wR a b) :=by
    simp only [Wellformed,canonical,context,word,sample,label,labelWord,packet,
      Bool.false_eq_true,ite_false,ite_true,pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits]
  have HB : Labels (packet cL wL cR wR a b) :=by
    simpa only [Labels,context,sample,label,labelWord,packet,Bool.false_eq_true,ite_false,ite_true,
      pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits] using And.intro ha' hb
  have HM : packet cL wL cR wR a b∈language ↔agrees (packet cL wL cR wR a b) :=by
    constructor
    · exact fun h=>h.2.2.2.2
    · intro h
      refine ⟨HW,?_,?_,HB,h⟩
      · simpa only [context,word,sample,packet,Bool.false_eq_true,ite_false,pairFst_pair,pairSnd_pair] using hL
      · simpa only [context,word,sample,packet,ite_true,pairFst_pair,pairSnd_pair] using hR'
  exact HM.trans (agrees_iff cL wL cR wR hL hR' a b)

theorem reject_left (z : List Bool)
    (hbad : count (context false z)≤label false z) : z∉language :=
  fun h=>(Nat.not_lt_of_ge hbad) h.2.2.2.1.1
theorem reject_right (z : List Bool)
    (hbad : count (context true z)≤label true z) : z∉language :=
  fun h=>(Nat.not_lt_of_ge hbad) h.2.2.2.1.2

end LeanCanny.Encoding.FormulaSignSlotRadialProviderFieldEquality
