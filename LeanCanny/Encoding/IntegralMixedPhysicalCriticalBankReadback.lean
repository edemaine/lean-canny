/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedPhysicalCriticalBankEquality
public import LeanCanny.Algebra.IntegralMixedFramedCoordinateCharacteristicActual
public import LeanCanny.Algebra.ThomEncoding
/-! # The streamed derivative scan is exactly equality of every old quotient -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedPhysicalCriticalBankEquality
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedPhysicalMarkedPlan (bank)
open IntegralMixedPhysicalCriticalPrefixes (birth key key_birth positive input)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term}
  (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R : List Bool→ℕ} (hR : BinaryFn R) (outer : Bool)

theorem coordinate_val (child : Bool) (q : List Bool) (i k : ℕ) (hi : i<birth n outer false q) :
    (coordinate hn ht ha hR outer child q (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k))).val=
      i+(if child then 1 else 0) := by
  simp only [coordinate,selected,pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits,
    min_eq_left (by omega : i≤birth n outer false q-1)]

noncomputable def point (child : Bool) (q w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (input hn ht ha hR outer child) q w) (i : ℕ) : ℝ :=
  IntegralFramedPhysicalSquare.point (bank hn ht ha hR outer).parameters (bank hn ht ha hR outer).plan
    (bank hn ht ha hR outer).data (bank hn ht ha hR outer).nodes (bank hn ht ha hR outer).factor
    (bank hn ht ha hR outer).seed (bank hn ht ha hR outer).bounds (key n outer child)
    (positive hn ht ha hR outer child) q w hv
    (coordinate hn ht ha hR outer child q (pair (BinaryNatCode.encode i) (BinaryNatCode.encode 0)))

theorem derivative_polynomial (q : List Bool) (i k : ℕ) :
    (derivatives hn ht ha hR outer).polynomial (pair q (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k)))=
      Polynomial.derivative^[k] ((source hn ht ha hR outer).polynomial (pair q (BinaryNatCode.encode i))) := by
  simp only [derivatives,IntegerPolynomialSourceChoice.reindex,Function.comp_apply,regroup,
    pairFst_pair,pairSnd_pair]
  exact IntegerPolynomialIteratedDerivativeBits.packet (source hn ht ha hR outer) _ k

attribute [local irreducible] bank originalSource source derivatives coordinate

private noncomputable def naturalPolynomial (B : IntegralFramedBankQuery.Bank) (k : List Bool) (i : ℕ) : Polynomial ℤ :=
  if hi : i<(IntegralMixedFramedHistoryFamilyBits.family B.parameters B.plan B.data).birth k then
    IntegralMixedBankCoordinatePolynomial.polynomial
      ((IntegralMixedFramedHistoryFamilyBits.family B.parameters B.plan B.data).state k) ⟨i,hi⟩ else 0

theorem value_packet (child : Bool) (q w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (input hn ht ha hR outer child) q w) (i k : ℕ) :
    value hn ht ha hR outer child (pair (pair q w) (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k)))=
      InfinitesimalSign.encode (ThomEncoding.sign
        (((source hn ht ha hR outer).polynomial (pair q (BinaryNatCode.encode i))).map (Int.castRingHom ℝ))
        (point hn ht ha hR outer child q w hv i) k) :=by
  have HC : coordinate hn ht ha hR outer child q (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k))=
      coordinate hn ht ha hR outer child q (pair (BinaryNatCode.encode i) (BinaryNatCode.encode 0)) :=by
    apply Fin.ext
    simp only [coordinate,selected,pairFst_pair,pairSnd_pair]
  have HP:=IntegralFramedPhysicalUnivariateTest.packet
    (bank hn ht ha hR outer).parameters (bank hn ht ha hR outer).plan (bank hn ht ha hR outer).data
    (bank hn ht ha hR outer).nodes (bank hn ht ha hR outer).factor (bank hn ht ha hR outer).seed
    (bank hn ht ha hR outer).bounds (key n outer child) (positive hn ht ha hR outer child)
    (coordinate hn ht ha hR outer child) (derivatives hn ht ha hR outer) q w
    (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k)) hv
  rw [derivative_polynomial,HC] at HP
  simpa only [value,point,ThomEncoding.sign,Polynomial.iterate_derivative_map,Polynomial.eval_map] using HP

theorem source_nonzero (q : List Bool) (i : ℕ) :
    (source hn ht ha hR outer).polynomial (pair q (BinaryNatCode.encode i))≠0 :=by
  simpa only [source,originalSource,IntegerPolynomialSourceChoice.reindex,Function.comp_apply,
    IntegralMixedFramedCoordinateCharacteristicBits.rootSource] using
    IntegralMixedFramedCoordinateCharacteristicBits.nonzero (bank hn ht ha hR outer).parameters
      (bank hn ht ha hR outer).plan (bank hn ht ha hR outer).data (saved n outer (pair q (BinaryNatCode.encode i)))

theorem parent_root (q w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (input hn ht ha hR outer false) q w)
    (i : ℕ) (hi : i<birth n outer false q) :
    ((source hn ht ha hR outer).polynomial (pair q (BinaryNatCode.encode i))).eval₂ (Int.castRingHom ℝ)
      (point hn ht ha hR outer false q w hv i)=0 :=by
  let B:=bank hn ht ha hR outer
  let ctx:=pair (key n outer false q) (BinaryNatCode.encode i)
  have HK : IntegralMixedFramedCoordinateCharacteristicBits.key ctx=key n outer false q :=by
    simp only [IntegralMixedFramedCoordinateCharacteristicBits.key,ctx,pairFst_pair]
  have HC : IntegralMixedFramedCoordinateCharacteristicBits.count B.parameters B.plan B.data ctx=
      birth n outer false q :=by
    unfold IntegralMixedFramedCoordinateCharacteristicBits.count
    rw [HK]
    exact key_birth hn ht ha hR outer false q
  have HI : IntegralMixedFramedCoordinateCharacteristicBits.index ctx<
      IntegralMixedFramedCoordinateCharacteristicBits.count B.parameters B.plan B.data ctx :=by
    rw [HC]
    simpa only [IntegralMixedFramedCoordinateCharacteristicBits.index,ctx,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits] using hi
  have HA : IntegralMixedFramedCoordinateCharacteristicBits.Active B.parameters ctx :=by
    unfold IntegralMixedFramedCoordinateCharacteristicBits.Active
    rw [HK]
    have HB := (IntegralMixedFramedHistoryFamilyBits.family_birth B.parameters B.plan B.data
      (key n outer false q)).symm.trans (key_birth hn ht ha hR outer false q)
    rw [HB]
    simp only [key,IntegralMixedFramedHistoryFamilyBits.keyAt,pairFst_pair]
    exact IntegralMixedPhysicalCriticalPrefixes.below_cap hn ht ha hR outer false q
  obtain ⟨φ,_,Hφ⟩:=IntegralFramedPhysicalSquare.exists_interpretation B.parameters B.plan B.data
    B.nodes B.factor B.seed B.bounds (key n outer false) (positive hn ht ha hR outer false) q w hv
  have HI' : i<(IntegralMixedFramedHistoryFamilyBits.family B.parameters B.plan B.data).birth (key n outer false q) :=by
    rw [key_birth hn ht ha hR outer]
    exact hi
  have HE : (⟨i,HI'⟩ :
      Fin ((IntegralMixedFramedHistoryFamilyBits.family B.parameters B.plan B.data).birth (key n outer false q)))=
      coordinate hn ht ha hR outer false q (pair (BinaryNatCode.encode i) (BinaryNatCode.encode 0)) :=by
    apply Fin.ext
    rw [coordinate_val hn ht ha hR outer false q i 0 hi]
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
  have HP : (source hn ht ha hR outer).polynomial (pair q (BinaryNatCode.encode i))=
      naturalPolynomial B (key n outer false q) i :=by
    have HD : (source hn ht ha hR outer).polynomial (pair q (BinaryNatCode.encode i))=
        IntegralMixedFramedCoordinateCharacteristicBits.polynomial B.parameters B.plan B.data ctx :=by
      simp only [source,originalSource,IntegerPolynomialSourceChoice.reindex,Function.comp_apply,
        IntegralMixedFramedCoordinateCharacteristicBits.rootSource,saved,pairFst_pair,pairSnd_pair,ctx,B]
    exact HD.trans (HN.trans (congrArg₂ (naturalPolynomial B) HK HIndex))
  rw [HP,naturalPolynomial,dite_eq_left HI']
  have HR:=IntegralMixedBankCoordinatePolynomial.quotient_root
    ((IntegralMixedFramedHistoryFamilyBits.family B.parameters B.plan B.data).state (key n outer false q)) φ ⟨i,HI'⟩
  rw [Hφ] at HR
  simpa only [point,←HE] using HR

theorem coordinate_iff (q v : List Bool)
    (hp : SquareSampleCompleteVertices.Valid (input hn ht ha hR outer false) q
      (IntegralMixedPhysicalCriticalQuery.parentWord q))
    (hv : SquareSampleCompleteVertices.Valid (input hn ht ha hR outer true) q v)
    (i : ℕ) (hi : i<birth n outer false q) :
    (∀k<degree hn ht ha hR outer (pair (pair q v) (List.replicate i true))+1,
      value hn ht ha hR outer false (probe false (pair (pair (pair q v) (List.replicate i true)) (BinaryNatCode.encode k)))=
        value hn ht ha hR outer true (probe true (pair (pair (pair q v) (List.replicate i true)) (BinaryNatCode.encode k)))) ↔
      point hn ht ha hR outer false q (IntegralMixedPhysicalCriticalQuery.parentWord q) hp i=
        point hn ht ha hR outer true q v hv i :=by
  simp only [probe,pairFst_pair,pairSnd_pair,List.length_replicate,Bool.false_eq_true,ite_true,ite_false]
  simp_rw [value_packet hn ht ha hR outer false q _ hp,value_packet hn ht ha hR outer true q v hv,
    SquareSampleTestSign.encode_eq_iff]
  let p:=((source hn ht ha hR outer).polynomial (pair q (BinaryNatCode.encode i))).map (Int.castRingHom ℝ)
  let a:=point hn ht ha hR outer false q (IntegralMixedPhysicalCriticalQuery.parentWord q) hp i
  let b:=point hn ht ha hR outer true q v hv i
  have HA:p.eval a=0:=by rw [Polynomial.eval_map];exact parent_root hn ht ha hR outer q _ hp i hi
  have HD:p.natDegree≤degree hn ht ha hR outer (pair (pair q v) (List.replicate i true)) :=by
    apply Polynomial.natDegree_map_le.trans
    simpa only [degree,pairFst_pair,pairSnd_pair,List.length_replicate] using
      (source hn ht ha hR outer).degree_bound (pair q (BinaryNatCode.encode i))
  constructor
  · intro hs
    have HB:SignType.sign (p.eval b)=0:=by
      have H0:=hs 0 (by omega)
      change ThomEncoding.sign p a 0=ThomEncoding.sign p b 0 at H0
      simpa only [ThomEncoding.sign,Function.iterate_zero_apply,HA,sign_zero] using H0.symm
    exact ThomEncoding.root_eq p ((Polynomial.map_ne_zero_iff Int.cast_injective).mpr
      (source_nonzero hn ht ha hR outer q i)) _ HD a b HA (sign_eq_zero_iff.mp HB) (fun k hk=>hs k (by omega))
  · intro he k _
    rw [he]

theorem agrees_iff (q v : List Bool)
    (hp : SquareSampleCompleteVertices.Valid (input hn ht ha hR outer false) q (IntegralMixedPhysicalCriticalQuery.parentWord q))
    (hv : SquareSampleCompleteVertices.Valid (input hn ht ha hR outer true) q v) :
    agrees hn ht ha hR outer (pair q v) ↔
      ∀i<birth n outer false q,
        point hn ht ha hR outer false q (IntegralMixedPhysicalCriticalQuery.parentWord q) hp i=
          point hn ht ha hR outer true q v hv i :=by
  simp only [agrees,pairFst_pair]
  constructor
  · intro H i hi
    exact (coordinate_iff hn ht ha hR outer q v hp hv i hi).mp (H i hi)
  · intro H i hi
    exact (coordinate_iff hn ht ha hR outer q v hp hv i hi).mpr (H i hi)

end LeanCanny.Encoding.IntegralMixedPhysicalCriticalBankEquality
