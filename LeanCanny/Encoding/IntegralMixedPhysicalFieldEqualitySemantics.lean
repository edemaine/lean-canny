/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedPhysicalFieldEquality
public import LeanCanny.Algebra.IntegralMixedFramedCoordinateCharacteristicActual
public import LeanCanny.Algebra.ThomEncoding
public import LeanCanny.Encoding.IntegralFramedPhysicalBankPolynomial
/-! # The left characteristic polynomial identifies values across two contexts -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedPhysicalFieldEquality
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedPhysicalMarkedPlan (bank)
open IntegralMixedFramedHistoryFamilyBits (family)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term}
  (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R : List Bool→ℕ} (hR : BinaryFn R)
local notation "B" => bank hn ht ha hR false
local notation "P" => IntegralFramedBankQuery.Bank.parameters B
local notation "D" => IntegralFramedBankQuery.Bank.plan B
local notation "H" => IntegralFramedBankQuery.Bank.data B
local notation "G" => family P D H
local notation "S" => IntegralMixedPhysicalMarkedTest.input hn ht ha hR false

theorem count_eq (c : List Bool) : count hn ht ha hR c=IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n (pairFst c) :=by
  simp only [count,bank,Bool.false_eq_true,ite_false,IntegralMixedAuxiliaryMarkedRecordPlan.bank,
    IntegralMixedFramedHistoryFamilyBits.family_birth,IntegralMixedAuxiliaryMarkedRecordPlan.bankKey]
  exact IntegralMixedFramedHistoryFamilyBits.keyAt_prefix _ _ _ _
    (by change IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n (pairFst c)≤
      IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n (pairFst c)+2+1;omega)
theorem key_root (c : List Bool) : pairFst ((B).key c)=pairFst c :=by
  change pairFst (IntegralMixedAuxiliaryMarkedRecordPlan.bankKey n c)=_
  simp only [IntegralMixedAuxiliaryMarkedRecordPlan.bankKey,IntegralMixedFramedHistoryFamilyBits.keyAt,pairFst_pair]
theorem below_cap (c : List Bool) : IntegralMixedFramedHistoryFamilyBits.prefixLength P ((B).key c)<(P).cap (pairFst ((B).key c)) :=by
  rw [←IntegralMixedFramedHistoryFamilyBits.family_birth P D H,key_root hn ht ha hR c]
  change count hn ht ha hR c<_
  rw [count_eq hn ht ha hR c]
  change IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n (pairFst c)<
    IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n (pairFst c)+2
  omega

attribute [local irreducible] bank family originalSource derivatives coordinate value
  IntegralFramedPhysicalUnivariateTest.value IntegralMixedBankCoordinatePolynomial.polynomial
  IntegralFramedPhysicalSquare.point

private theorem decode_encode (k : ℕ) : Nat.fromBitsLE (BinaryNatCode.encode k)=k:=Nat.fromBitsLE_bits k

noncomputable def pointNewest (c w : List Bool) (hv : SquareSampleCompleteVertices.Valid S c w) (i : ℕ) : ℝ :=
  IntegralFramedPhysicalSquare.point P D H (B).nodes (B).factor (B).seed (B).bounds (B).key (B).positive c w hv
    ⟨min i (count hn ht ha hR c-1),by
      change min i (count hn ht ha hR c-1)<count hn ht ha hR c
      have HP:=count_pos hn ht ha hR c
      omega⟩
noncomputable def point (c w : List Bool) (hv : SquareSampleCompleteVertices.Valid S c w) (chronological : ℕ) :=
  pointNewest hn ht ha hR c w hv (newest (count hn ht ha hR c) chronological)
attribute [local irreducible] pointNewest

theorem derivative_polynomial (c arg : List Bool) (i k : ℕ) :
    (derivatives hn ht ha hR).polynomial (pair c (pair arg (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k))))=
      Polynomial.derivative^[k] ((originalSource hn ht ha hR).polynomial arg) :=by
  simp only [derivatives,IntegerPolynomialSourceChoice.reindex,Function.comp_apply,derivativePacket,
    pairFst_pair,pairSnd_pair]
  exact IntegerPolynomialIteratedDerivativeBits.packet (originalSource hn ht ha hR) arg k

theorem value_packet (c w arg : List Bool) (hv : SquareSampleCompleteVertices.Valid S c w) (i k : ℕ) :
    value hn ht ha hR (pair (pair c w) (pair arg (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k))))=
      InfinitesimalSign.encode (ThomEncoding.sign (((originalSource hn ht ha hR).polynomial arg).map (Int.castRingHom ℝ))
        (pointNewest hn ht ha hR c w hv i) k) :=by
  unfold value
  have HP:=IntegralFramedPhysicalUnivariateTest.packet P D H (B).nodes (B).factor (B).seed (B).bounds
    (B).key (B).positive (coordinate hn ht ha hR) (derivatives hn ht ha hR) c w
    (pair arg (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k))) hv
  have HC : IntegralFramedPhysicalSquare.point P D H (B).nodes (B).factor (B).seed (B).bounds (B).key (B).positive
      c w hv (coordinate hn ht ha hR c (pair arg (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k))))=
        pointNewest hn ht ha hR c w hv i :=by
    unfold pointNewest
    apply congrArg (IntegralFramedPhysicalSquare.point P D H (B).nodes (B).factor (B).seed (B).bounds (B).key (B).positive c w hv)
    apply Fin.ext
    simp only [coordinate,pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits]
  have HE:=congrArg₂ (fun (p : Polynomial ℤ) (v : ℝ)=>p.eval₂ (Int.castRingHom ℝ) v)
    (derivative_polynomial hn ht ha hR c arg i k) HC
  exact (HP.trans (congrArg (fun v : ℝ=>InfinitesimalSign.encode (SignType.sign v)) HE)).trans
    (by simp only [ThomEncoding.sign,Polynomial.iterate_derivative_map,Polynomial.eval_map])

private noncomputable def naturalPolynomial (bankData : IntegralFramedBankQuery.Bank) (key : List Bool) (i : ℕ) : Polynomial ℤ :=
  if hi : i<(family bankData.parameters bankData.plan bankData.data).birth key then
    IntegralMixedBankCoordinatePolynomial.polynomial ((family bankData.parameters bankData.plan bankData.data).state key) ⟨i,hi⟩ else 0

theorem source_nonzero (arg : List Bool) : (originalSource hn ht ha hR).polynomial arg≠0 :=by
  simpa only [originalSource,IntegralMixedPhysicalCriticalBankEquality.originalSource,
    IntegralMixedFramedCoordinateCharacteristicBits.rootSource] using
      IntegralMixedFramedCoordinateCharacteristicBits.nonzero P D H arg

private theorem source_polynomial (c : List Bool) (i : ℕ) (hi : i<count hn ht ha hR c) :
    (originalSource hn ht ha hR).polynomial (pair ((B).key c) (BinaryNatCode.encode i))=
      naturalPolynomial B ((B).key c) i :=by
  let arg:=pair ((B).key c) (BinaryNatCode.encode i)
  have HA : IntegralMixedFramedCoordinateCharacteristicBits.Active P arg :=by
    simp only [IntegralMixedFramedCoordinateCharacteristicBits.Active,IntegralMixedFramedCoordinateCharacteristicBits.key,arg,pairFst_pair]
    exact below_cap hn ht ha hR c
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
  have HE : (originalSource hn ht ha hR).polynomial arg=IntegralMixedFramedCoordinateCharacteristicBits.polynomial P D H arg :=by
    simp only [originalSource,IntegralMixedPhysicalCriticalBankEquality.originalSource,
      IntegralMixedFramedCoordinateCharacteristicBits.rootSource]
  exact HE.trans (HN.trans (congrArg₂ (naturalPolynomial B)
    (by simp only [IntegralMixedFramedCoordinateCharacteristicBits.key,arg,pairFst_pair])
    (by simp only [IntegralMixedFramedCoordinateCharacteristicBits.index,arg,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits])))

private theorem bank_root (c w : List Bool) (hv : SquareSampleCompleteVertices.Valid S c w) (i : ℕ)
    (hi : i<count hn ht ha hR c) :
    (IntegralMixedBankCoordinatePolynomial.polynomial ((G).state ((B).key c)) ⟨i,hi⟩).eval₂
      (Int.castRingHom ℝ) (pointNewest hn ht ha hR c w hv i)=0 :=by
  have hi' : i<(G).birth ((B).key c):=hi
  have HC : pointNewest hn ht ha hR c w hv i=IntegralFramedPhysicalSquare.point P D H
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
    (hi : i<count hn ht ha hR c) :
    ((originalSource hn ht ha hR).polynomial (pair ((B).key c) (BinaryNatCode.encode i))).eval₂
      (Int.castRingHom ℝ) (pointNewest hn ht ha hR c w hv i)=0 :=by
  have HP:=source_polynomial hn ht ha hR c i hi
  have HE : (originalSource hn ht ha hR).polynomial (pair ((B).key c) (BinaryNatCode.encode i))=
      IntegralMixedBankCoordinatePolynomial.polynomial ((G).state ((B).key c)) ⟨i,hi⟩ :=
    HP.trans (dite_eq_left hi)
  exact (congrArg (fun p : Polynomial ℤ=>p.eval₂ (Int.castRingHom ℝ) (pointNewest hn ht ha hR c w hv i)) HE).trans
    (bank_root hn ht ha hR c w hv i hi)

theorem oldArgument_packet (cL wL cR wR : List Bool) (a b : ℕ) :
    oldArgument hn ht ha hR (packet cL wL cR wR a b)=
      pair ((B).key cL) (BinaryNatCode.encode (newest (count hn ht ha hR cL) a)) :=by
  simp only [oldArgument,selected,context,sample,label,labelWord,packet,
    Bool.false_eq_true,ite_false,pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits]

theorem agrees_iff (cL wL cR wR : List Bool)
    (hL : SquareSampleCompleteVertices.Valid S cL wL) (hR' : SquareSampleCompleteVertices.Valid S cR wR) (a b : ℕ) :
    agrees hn ht ha hR (packet cL wL cR wR a b) ↔ point hn ht ha hR cL wL hL a=point hn ht ha hR cR wR hR' b :=by
  let arg:=pair ((B).key cL) (BinaryNatCode.encode (newest (count hn ht ha hR cL) a))
  have HN : agrees hn ht ha hR (packet cL wL cR wR a b) ↔
      ∀k<(originalSource hn ht ha hR).degree arg+1,
        ThomEncoding.sign (((originalSource hn ht ha hR).polynomial arg).map (Int.castRingHom ℝ)) (point hn ht ha hR cL wL hL a) k=
        ThomEncoding.sign (((originalSource hn ht ha hR).polynomial arg).map (Int.castRingHom ℝ)) (point hn ht ha hR cR wR hR' b) k :=by
    simp only [agrees,degree,probe,oldArgument,selected,context,sample,label,labelWord,packet,
      Bool.false_eq_true,ite_false,ite_true,pairFst_pair,pairSnd_pair,decode_encode]
    dsimp only [arg]
    simp_rw [value_packet hn ht ha hR cL wL (pair ((B).key cL) (BinaryNatCode.encode (newest (count hn ht ha hR cL) a))) hL,
      value_packet hn ht ha hR cR wR (pair ((B).key cL) (BinaryNatCode.encode (newest (count hn ht ha hR cL) a))) hR',
      SquareSampleTestSign.encode_eq_iff]
    rfl
  rw [HN]
  let p:=((originalSource hn ht ha hR).polynomial arg).map (Int.castRingHom ℝ)
  have HA : p.eval (point hn ht ha hR cL wL hL a)=0 :=by
    rw [Polynomial.eval_map]
    exact left_root hn ht ha hR cL wL hL _ (newest_lt _ _ (count_pos hn ht ha hR cL))
  have HD : p.natDegree≤(originalSource hn ht ha hR).degree arg :=
    Polynomial.natDegree_map_le.trans ((originalSource hn ht ha hR).degree_bound arg)
  constructor
  · intro hs
    have HB : SignType.sign (p.eval (point hn ht ha hR cR wR hR' b))=0 :=by
      have H0:=hs 0 (by omega)
      change ThomEncoding.sign p _ 0=ThomEncoding.sign p _ 0 at H0
      simpa only [ThomEncoding.sign,Function.iterate_zero_apply,HA,sign_zero] using H0.symm
    exact ThomEncoding.root_eq p ((Polynomial.map_ne_zero_iff Int.cast_injective).mpr (source_nonzero hn ht ha hR arg)) _ HD
      _ _ HA (sign_eq_zero_iff.mp HB) (fun k hk=>hs k (by omega))
  · intro he k _
    rw [he]

theorem language_packet_iff (cL wL cR wR : List Bool)
    (hL : SquareSampleCompleteVertices.Valid S cL wL) (hR' : SquareSampleCompleteVertices.Valid S cR wR) (a b : ℕ)
    (ha' : a<count hn ht ha hR cL) (hb : b<count hn ht ha hR cR) :
    packet cL wL cR wR a b∈language hn ht ha hR ↔point hn ht ha hR cL wL hL a=point hn ht ha hR cR wR hR' b :=by
  have HW : Wellformed (packet cL wL cR wR a b) :=by
    simp only [Wellformed,canonical,context,word,sample,label,labelWord,packet,
      Bool.false_eq_true,ite_false,ite_true,pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits]
  have HB : Labels hn ht ha hR (packet cL wL cR wR a b) :=by
    simpa only [Labels,context,sample,label,labelWord,packet,Bool.false_eq_true,ite_false,ite_true,
      pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits] using And.intro ha' hb
  have HM : packet cL wL cR wR a b∈language hn ht ha hR ↔agrees hn ht ha hR (packet cL wL cR wR a b) :=by
    constructor
    · exact fun h=>h.2.2.2.2
    · intro h
      refine ⟨HW,?_,?_,HB,h⟩
      · simpa only [context,word,sample,packet,Bool.false_eq_true,ite_false,pairFst_pair,pairSnd_pair] using hL
      · simpa only [context,word,sample,packet,ite_true,pairFst_pair,pairSnd_pair] using hR'
  exact HM.trans (agrees_iff hn ht ha hR cL wL cR wR hL hR' a b)

theorem reject_left (z : List Bool)
    (hbad : count hn ht ha hR (context false z)≤label false z) : z∉language hn ht ha hR :=
  fun h=>(Nat.not_lt_of_ge hbad) h.2.2.2.1.1
theorem reject_right (z : List Bool)
    (hbad : count hn ht ha hR (context true z)≤label true z) : z∉language hn ht ha hR :=
  fun h=>(Nat.not_lt_of_ge hbad) h.2.2.2.1.2

end LeanCanny.Encoding.IntegralMixedPhysicalFieldEquality
