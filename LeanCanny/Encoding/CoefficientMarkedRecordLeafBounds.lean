/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordLeafQuery
public import LeanCanny.Algebra.IntegralMixedFramedBankTermBounds
public import LeanCanny.Algebra.DiagonalUnivariateSystem
/-! # Original coefficient bounds for every mandatory native leaf query -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordLeafQuery
open LeanCanny.Algebra LeanCanny.Computation Polynomial IntegralMixedHistory
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

private theorem leaf_mass (A:CoefficientBankTermQuery.Arguments ℤ) (p:ℤ[X]) (D i M L:ℕ)
    (hp:p.natDegree≤D) (hMass:coefficientMass p≤2^M)
    (hCommon:A.common.natAbs≤2^L) (hCofactor:∀j,(A.cofactor j).natAbs≤2^L):
    MvMass.mass (CoefficientBankLeafQuery.polynomial A p D i)≤2^(M+D*L):=by
  unfold CoefficientBankLeafQuery.polynomial
  split_ifs with hi
  · unfold CoefficientBankUnivariateQuery.physical CoefficientBankUnivariateQuery.polynomial
    apply (DiagonalUnivariateSystem.mass_le _ _).trans
    apply (IntegerPolynomialExpandSource.mass_le _ _).trans
    have HN:coefficientMass (C (A.cofactor (A.birth-1-i))*X)≤2^L:=by
      rw [show (X:ℤ[X])=X^1 from (pow_one _).symm,Polynomial.C_mul_X_pow_eq_monomial,coefficientMass_monomial]
      exact hCofactor _
    have HD:coefficientMass (C A.common)≤2^L:=by
      simpa only [coefficientMass_C] using hCommon
    calc
      _≤coefficientMass p*(2^L)^D:=UnivariateRational.clear_mass _ _ _ _ hp (2^L) HN HD
      _≤2^M*(2^L)^D:=Nat.mul_le_mul_right _ hMass
      _=2^(M+D*L):=by rw [←pow_mul,←pow_add];congr 1;ring
  · simpa only [MvMass.zero] using Nat.zero_le (2^(M+D*L))

private theorem snapshot_abs (P:IntegralCriticalHistoryTask.Parameters)
    (D:IntegralMixedFramedHistoryFamilyBits.Plan P) (H:IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key:List Bool) (G:ℕ)
    (h:∀j,((IntegralMixedFramedBankSnapshotBits.atKey P D H key).denominator j).natAbs≤2^G):
    let A:=CoefficientBankTermQuery.ofSnapshot P D H key (IntegralFramedPhysicalSquare.count P D key)
      (IntegralFramedPhysicalSquare.sampler P D H key).scalar
    A.common.natAbs≤2^((IntegralMixedFramedBankSnapshotBits.atKey P D H key).count*G) ∧
      ∀i,(A.cofactor i).natAbs≤2^((IntegralMixedFramedBankSnapshotBits.atKey P D H key).count*G):=
  ⟨IntegralMixedFramedBankTermBits.snapshot_common_bound _ _ h,
    IntegralMixedFramedBankTermBits.snapshot_cofactor_bound _ _ h⟩

variable {n:List Bool→ℕ} {t:List Bool→LeanCanny.ETR.Term}
  (hn:UnaryFn n) (ht:(fun q=>(t q).toData.toBits)∈FP) (ha:∀q,(t q).arity≤n q)

noncomputable def degreeCap (ctx:List Bool):ℕ:=
  ∑i∈Finset.range (IntegralMixedAuxiliaryMarkedIntegerSource.number n ctx+8),degree hn ht ha ctx i

theorem degree_le_cap (ctx:List Bool) (i:ℕ) (hi:i<IntegralMixedAuxiliaryMarkedIntegerSource.number n ctx+8):
    degree hn ht ha ctx i≤degreeCap hn ht ha ctx:=
  Finset.single_le_sum (fun j _=>Nat.zero_le (degree hn ht ha ctx j)) (Finset.mem_range.mpr hi)

theorem degreeCap_binary:BinaryFn (degreeCap hn ht ha):=by
  have HI:BinaryFn (fun z=>degree hn ht ha (pairFst z) (pairSnd z).length):=
    (IntegralMixedAuxiliaryMarkedIntegerSource.access hn ht ha (BinaryFn.const 0)).degree.comp
      (mem_FP_pair pairFst_mem_FP (BinaryFn.ofUnary (UnaryFn.length pairSnd_mem_FP)).bits_mem_FP)
  have HS:=BinaryFn.sum ((IntegralMixedAuxiliaryMarkedIntegerSource.number_unary hn).add (UnaryFn.const 8)) HI
  exact HS.of_eq (fun ctx=>by
    simp only [pairFst_pair,pairSnd_pair,List.length_replicate,degreeCap])

noncomputable def slope (ctx:List Bool):ℕ:=
  IntegralMixedAuxiliaryMarkedRecordRadiusHeight.seedSlope hn ht ha ctx+
    2*degreeCap hn ht ha ctx*CoefficientMarkedRecordActual.horizon hn ht ha ctx*
      IntegralMixedAuxiliaryMarkedRecordRadiusHeight.bankSlope hn ht ha ctx

noncomputable def offset (ctx:List Bool):ℕ:=
  IntegralMixedAuxiliaryMarkedRecordRadiusHeight.seedOffset hn ht ha ctx+
    2*degreeCap hn ht ha ctx*CoefficientMarkedRecordActual.horizon hn ht ha ctx*
      IntegralMixedAuxiliaryMarkedRecordRadiusHeight.bankOffset hn ht ha ctx

noncomputable def coefficientBudget (ctx:List Bool):ℕ:=
  IntegerPolynomialDyadic.massBudget (CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha ctx)
    (slope hn ht ha ctx) (offset hn ht ha ctx)

private theorem horizon_binary:BinaryFn (CoefficientMarkedRecordActual.horizon hn ht ha):=
  BinaryFn.ofUnary ((IntegralMixedAuxiliaryMarkedRecordPlan.access hn ht ha).cap.add (UnaryFn.const 1))

theorem slope_binary:BinaryFn (slope hn ht ha):=
  (IntegralMixedAuxiliaryMarkedRecordRadiusHeight.seedSlope_binary hn ht ha).add
    ((((BinaryFn.const 2).mul (degreeCap_binary hn ht ha)).mul (horizon_binary hn ht ha)).mul
      (IntegralMixedAuxiliaryMarkedRecordRadiusHeight.bankSlope_binary hn ht ha))

theorem offset_binary:BinaryFn (offset hn ht ha):=
  (IntegralMixedAuxiliaryMarkedRecordRadiusHeight.seedOffset_binary hn ht ha).add
    ((((BinaryFn.const 2).mul (degreeCap_binary hn ht ha)).mul (horizon_binary hn ht ha)).mul
      (IntegralMixedAuxiliaryMarkedRecordRadiusHeight.bankOffset_binary hn ht ha))

theorem coefficientBudget_binary:BinaryFn (coefficientBudget hn ht ha):=
  IntegerPolynomialDyadic.massBudget_binary (CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff_binary hn ht ha)
    (slope_binary hn ht ha) (offset_binary hn ht ha)

attribute [local irreducible] IntegralMixedSourceIntegerRecordAppend.plan
  IntegralMixedAuxiliaryMarkedIntegerSource.candidate IntegralMixedAuxiliaryCandidate.sourceInput
  IntegralMixedAuxiliaryCandidate.source IntegralMixedAuxiliaryMarkedIntegerSource.oldKey

private theorem native_mass (ctx:List Bool) (R:List Bool→ℕ) (k:ℕ) (aux:List Bool) (i:ℕ)
    (hi:i<IntegralMixedAuxiliaryMarkedIntegerSource.number n ctx+8):
    MvMass.mass (nativePolynomial hn ht ha ctx R k aux i)≤2^(slope hn ht ha ctx*R ctx+offset hn ht ha ctx):=by
  let P:=IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha
  let D:=IntegralMixedAuxiliaryMarkedRecordPlan.plan hn ht ha R
  let H:=IntegralMixedAuxiliaryMarkedRecordPlan.data hn ht ha R
  let key:=CoefficientMarkedRecordRowLayout.key (n:=n) ctx k aux
  let G:=IntegralMixedAuxiliaryMarkedRecordRadiusHeight.bankSlope hn ht ha ctx*R ctx+
    IntegralMixedAuxiliaryMarkedRecordRadiusHeight.bankOffset hn ht ha ctx
  let A:=nativeArguments hn ht ha ctx R k aux
  let source:=IntegralMixedAuxiliaryMarkedIntegerSource.source hn ht ha R
  let q:=sourceKey ctx i
  have HC:(IntegralMixedFramedBankSnapshotBits.atKey P D H key).count≤
      CoefficientMarkedRecordActual.horizon hn ht ha ctx:=by
    change (IntegralMixedFramedHistoryFamilyBits.family P D H).birth key≤_
    rw [IntegralMixedFramedHistoryFamilyBits.family_birth]
    have HM:=min_le_right (Nat.fromBitsLE (pairFst (pairSnd key))) (P.cap (pairFst key)+1)
    change IntegralMixedFullHistoryFamilyBits.prefixLength P key≤_ at HM
    change IntegralMixedFullHistoryFamilyBits.prefixLength P key≤P.cap ctx+1
    simpa only [key,CoefficientMarkedRecordRowLayout.key_root] using HM
  have HB:=IntegralMixedAuxiliaryMarkedRecordRadiusHeight.bank_bounds hn ht ha R key
  have HDen:∀j,((IntegralMixedFramedBankSnapshotBits.atKey P D H key).denominator j).natAbs≤2^G:=by
    intro j
    have HJ:=HB.denominator j
    simp only [key,CoefficientMarkedRecordRowLayout.key_root] at HJ
    change (((IntegralMixedFramedHistoryFamilyBits.family P D H).state key).bank.denominator j).natAbs≤2^G
    exact HJ
  have HP:=snapshot_abs P D H key G HDen
  have HM:2^((IntegralMixedFramedBankSnapshotBits.atKey P D H key).count*G)≤
      2^(CoefficientMarkedRecordActual.horizon hn ht ha ctx*G):=
    Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right G HC)
  have HCommon:A.common.natAbs≤2^(CoefficientMarkedRecordActual.horizon hn ht ha ctx*G):=HP.1.trans HM
  have HCof:∀j,(A.cofactor j).natAbs≤2^(CoefficientMarkedRecordActual.horizon hn ht ha ctx*G):=
    fun j=>(HP.2 j).trans HM
  have Hdegree:2*source.degree q≤2*degreeCap hn ht ha ctx:=by
    rw [←degree_native hn ht ha ctx R i]
    exact Nat.mul_le_mul_left _ (degree_le_cap hn ht ha ctx i hi)
  have HSource:source.mass q≤IntegralMixedAuxiliaryMarkedRecordRadiusHeight.seedSlope hn ht ha ctx*R ctx+
      IntegralMixedAuxiliaryMarkedRecordRadiusHeight.seedOffset hn ht ha ctx:=
    IntegralMixedAuxiliaryMarkedRecordRadiusHeight.integer_mass_le hn ht ha R ctx i hi
  have HL:=leaf_mass A (source.polynomial q) (2*source.degree q) i (source.mass q)
    (CoefficientMarkedRecordActual.horizon hn ht ha ctx*G)
    ((source.degree_bound q).trans (by omega)) (source.mass_bound q) HCommon HCof
  have HE:source.mass q+2*source.degree q*(CoefficientMarkedRecordActual.horizon hn ht ha ctx*G)≤
      slope hn ht ha ctx*R ctx+offset hn ht ha ctx:=by
    refine (Nat.add_le_add HSource (Nat.mul_le_mul_right _ Hdegree)).trans_eq ?_
    unfold slope offset G
    ring
  exact HL.trans (Nat.pow_le_pow_right (by decide) HE)

private theorem mapped_bound (r:ℤ) (A:CoefficientBankTermQuery.Arguments ℤ[X])
    (B:CoefficientBankTermQuery.Arguments ℤ) (hA:A.map (evalRingHom r)=B)
    (p:(ℤ[X])[X]) (q:ℤ[X]) (hp:p.map (evalRingHom r)=q) (D E i M:ℕ) (hD:D=E)
    (h:MvMass.mass (CoefficientBankLeafQuery.polynomial B q E i)≤M):
    MvMass.mass (MvPolynomial.map (evalRingHom r) (CoefficientBankLeafQuery.polynomial A p D i))≤M:=by
  cases hA
  cases hp
  cases hD
  rw [CoefficientBankLeafQuery.polynomial_map]
  exact h

attribute [local irreducible] polynomial nativePolynomial nativeArguments
  CoefficientMarkedRecordTermQuery.arguments CoefficientBankLeafQuery.polynomial
  CoefficientBankTermQuery.ofSnapshot IntegralMixedFramedHistoryFamilyBits.family
  CoefficientMarkedRecordRowLayout.key IntegralMixedCausalRecordPlanBits.count
  IntegralMixedCausalRecordPlanBits.records

theorem mapped_mass (ctx:List Bool) (R:List Bool→ℕ) (k:ℕ)
    (hk:k≤IntegralMixedCausalRecordPlanBits.count ctx) (aux:List Bool) (i:ℕ)
    (hi:i<IntegralMixedAuxiliaryMarkedIntegerSource.number n ctx+8)
    (hlarge:CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha ctx≤R ctx):
    MvMass.mass (MvPolynomial.map (evalRingHom ((2:ℤ)^R ctx)) (polynomial hn ht ha ctx k hk i))≤
      2^(slope hn ht ha ctx*R ctx+offset hn ht ha ctx):=by
  have HA:=CoefficientMarkedRecordTermQuery.arguments_specialize hn ht ha ctx R k hk aux hlarge
  have HP:=IntegralMixedAuxiliaryMarkedRadiusModel.polynomial_map_eval hn ht ha R (sourceKey ctx i)
  simp only [sourceKey,pairFst_pair] at HP
  have HD:=congrArg (2*·) (degree_native hn ht ha ctx R i)
  have HM:=native_mass hn ht ha ctx R k aux i hi
  unfold polynomial
  unfold nativePolynomial nativeArguments at HM
  exact mapped_bound _ _ _ HA _ _ HP _ _ i _ HD HM

theorem coefficient_degree_mass (ctx:List Bool) (k:ℕ) (hk:k≤IntegralMixedCausalRecordPlanBits.count ctx)
    (i:ℕ) (hi:i<IntegralMixedAuxiliaryMarkedIntegerSource.number n ctx+8)
    (e:Fin (CoefficientMarkedRecordTermQuery.arguments hn ht ha ctx k hk).dimension→₀ ℕ):
    ((polynomial hn ht ha ctx k hk i).coeff e).natDegree≤slope hn ht ha ctx ∧
      coefficientMass ((polynomial hn ht ha ctx k hk i).coeff e)≤2^coefficientBudget hn ht ha ctx:=by
  apply IntegerPolynomialDyadic.degree_mass_of_growth
  intro r hr
  have HM:=(MvMass.coeff_le _ e).trans (mapped_mass hn ht ha ctx (fun _=>r) k hk [] i hi hr)
  simpa only [MvPolynomial.coeff_map,Polynomial.coe_evalRingHom] using HM

end LeanCanny.Encoding.CoefficientMarkedRecordLeafQuery
