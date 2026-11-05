/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordTermQuery
public import LeanCanny.Algebra.IntegralMixedFramedBankTermBounds
/-! # Original parameter coefficient bounds for the actual term queries -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordTermQuery
open LeanCanny.Algebra LeanCanny.Computation Polynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def termSize (word:List Bool→List Bool) (ctx:List Bool):ℕ:=
  (termSyntax word ctx).toData.size
noncomputable def countSize (word:List Bool→List Bool) (ctx:List Bool):ℕ:=
  (termSyntax word ctx).monomialCount.size

theorem termSize_unary (word:List Bool→List Bool) (hw:word∈FP):UnaryFn (termSize word):=
  (UnaryFn.length (mem_FP_comp hw LeanCanny.ETR.TermView.normalize_mem_FP)).of_eq
    (fun ctx=>by simp only [Function.comp_apply,LeanCanny.ETR.TermView.normalize_eq_term,Data.length_toBits];rfl)

theorem countSize_unary (word:List Bool→List Bool) (hw:word∈FP):UnaryFn (countSize word):=
  ((IntegralMixedFramedBankTermBits.monomialSize_unary word hw).comp
    (mem_FP_pair id_mem_FP (constFn_mem_FP []))).of_eq (fun ctx=>by
      simp only [IntegralMixedFramedBankTermBits.monomialSize,
        IntegralMixedFramedBankTermBits.source,LeanCanny.ETR.RationalSubstitutionBits.Source.syntax,
        LeanCanny.ETR.RationalSubstitutionBits.Source.ofTerm,IntegralMixedFramedBankTermBits.wordAt,pairFst_pair]
      rfl)

variable {n:List Bool→ℕ} {t:List Bool→LeanCanny.ETR.Term}
  (hn:UnaryFn n) (ht:(fun q=>(t q).toData.toBits)∈FP) (ha:∀q,(t q).arity≤n q)

noncomputable def slope (word:List Bool→List Bool) (ctx:List Bool):ℕ:=
  termSize word ctx*(2*termSize word ctx)*CoefficientMarkedRecordActual.horizon hn ht ha ctx*
    IntegralMixedAuxiliaryMarkedRecordRadiusHeight.bankSlope hn ht ha ctx

noncomputable def offset (word:List Bool→List Bool) (ctx:List Bool):ℕ:=
  countSize word ctx+termSize word ctx+
    termSize word ctx*(2*termSize word ctx)*CoefficientMarkedRecordActual.horizon hn ht ha ctx*
      IntegralMixedAuxiliaryMarkedRecordRadiusHeight.bankOffset hn ht ha ctx

noncomputable def coefficientBudget (word:List Bool→List Bool) (ctx:List Bool):ℕ:=
  IntegerPolynomialDyadic.massBudget (CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha ctx)
    (slope hn ht ha word ctx) (offset hn ht ha word ctx)

private theorem horizon_binary:BinaryFn (CoefficientMarkedRecordActual.horizon hn ht ha):=
  BinaryFn.ofUnary ((IntegralMixedAuxiliaryMarkedRecordPlan.access hn ht ha).cap.add (UnaryFn.const 1))

theorem slope_binary (word:List Bool→List Bool) (hw:word∈FP):BinaryFn (slope hn ht ha word):=
  (((BinaryFn.ofUnary (termSize_unary word hw)).mul
    ((BinaryFn.const 2).mul (BinaryFn.ofUnary (termSize_unary word hw)))).mul
      (horizon_binary hn ht ha)).mul (IntegralMixedAuxiliaryMarkedRecordRadiusHeight.bankSlope_binary hn ht ha)

theorem offset_binary (word:List Bool→List Bool) (hw:word∈FP):BinaryFn (offset hn ht ha word):=
  ((BinaryFn.ofUnary (countSize_unary word hw)).add (BinaryFn.ofUnary (termSize_unary word hw))).add
    ((((BinaryFn.ofUnary (termSize_unary word hw)).mul
      ((BinaryFn.const 2).mul (BinaryFn.ofUnary (termSize_unary word hw)))).mul
        (horizon_binary hn ht ha)).mul (IntegralMixedAuxiliaryMarkedRecordRadiusHeight.bankOffset_binary hn ht ha))

theorem coefficientBudget_binary (word:List Bool→List Bool) (hw:word∈FP):BinaryFn (coefficientBudget hn ht ha word):=
  IntegerPolynomialDyadic.massBudget_binary (CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff_binary hn ht ha)
    (slope_binary hn ht ha word hw) (offset_binary hn ht ha word hw)

attribute [local irreducible] IntegralMixedSourceIntegerRecordAppend.plan
  IntegralMixedAuxiliaryMarkedIntegerSource.candidate IntegralMixedAuxiliaryCandidate.sourceInput
  IntegralMixedAuxiliaryCandidate.source IntegralMixedAuxiliaryMarkedIntegerSource.oldKey

private theorem native_mass (word:List Bool→List Bool) (ctx:List Bool) (R:List Bool→ℕ) (k:ℕ) (aux:List Bool):
    MvMass.mass (MvPolynomial.rename
      (IntegralFramedPhysicalSquare.sampler (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha)
        (IntegralMixedAuxiliaryMarkedRecordPlan.plan hn ht ha R) (IntegralMixedAuxiliaryMarkedRecordPlan.data hn ht ha R)
        (CoefficientMarkedRecordRowLayout.key (n:=n) ctx k aux)).scalar
      (IntegralMixedFramedBankTermBits.polynomial (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha)
        (IntegralMixedAuxiliaryMarkedRecordPlan.plan hn ht ha R) (IntegralMixedAuxiliaryMarkedRecordPlan.data hn ht ha R)
        word (CoefficientMarkedRecordRowLayout.key (n:=n) ctx k aux)))≤
      2^(slope hn ht ha word ctx*R ctx+offset hn ht ha word ctx):=by
  let P:=IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha
  let D:=IntegralMixedAuxiliaryMarkedRecordPlan.plan hn ht ha R
  let H:=IntegralMixedAuxiliaryMarkedRecordPlan.data hn ht ha R
  let key:=CoefficientMarkedRecordRowLayout.key (n:=n) ctx k aux
  have HC:(IntegralMixedFramedBankSnapshotBits.atKey P D H key).count≤
      CoefficientMarkedRecordActual.horizon hn ht ha ctx:=by
    change (IntegralMixedFramedHistoryFamilyBits.family P D H).birth key≤_
    rw [IntegralMixedFramedHistoryFamilyBits.family_birth]
    have HM:=min_le_right (Nat.fromBitsLE (pairFst (pairSnd key))) (P.cap (pairFst key)+1)
    change IntegralMixedFullHistoryFamilyBits.prefixLength P key≤_ at HM
    change IntegralMixedFullHistoryFamilyBits.prefixLength P key≤P.cap ctx+1
    simpa only [key,CoefficientMarkedRecordRowLayout.key_root] using HM
  have HF:=IntegralMixedAuxiliaryMarkedRecordRadiusHeight.familyHeight_le hn ht ha R key
  simp only [key,CoefficientMarkedRecordRowLayout.key_root] at HF
  have HCoord:=Nat.mul_le_mul HC HF
  have HS:IntegralMixedFramedBankTermBits.size word key=termSize word ctx:=by
    change (LeanCanny.ETR.TermView.term (word (pairFst key))).toData.size=_
    rw [CoefficientMarkedRecordRowLayout.key_root]
    rfl
  have HM:IntegralMixedFramedBankTermBits.monomialSize word key=countSize word ctx:=by
    change (LeanCanny.ETR.TermView.term (word (pairFst key))).monomialCount.size=_
    rw [CoefficientMarkedRecordRowLayout.key_root]
    rfl
  have HE:IntegralMixedFramedBankTermBits.mass P D H word (fun _=>3)
      (IntegralMixedAuxiliaryMarkedRecordPlan.factor hn ht ha)
      (IntegralMixedAuxiliaryMarkedRecordRadiusHeight.seed hn ht ha R) key≤
      slope hn ht ha word ctx*R ctx+offset hn ht ha word ctx:=by
    unfold IntegralMixedFramedBankTermBits.mass IntegralMixedFramedBankTermBits.coordinateMass
    rw [HS,HM]
    refine (Nat.add_le_add_left (Nat.mul_le_mul_left _ HCoord) _).trans_eq ?_
    unfold slope offset
    ring
  exact (MvMass.rename_le _ _).trans
    ((IntegralMixedFramedBankTermBits.polynomial_mass P D H word (fun _=>3)
      (IntegralMixedAuxiliaryMarkedRecordPlan.factor hn ht ha)
      (IntegralMixedAuxiliaryMarkedRecordRadiusHeight.seed hn ht ha R)
      (IntegralMixedAuxiliaryMarkedRecordRadiusHeight.familyInputs hn ht ha R) key).trans
        (Nat.pow_le_pow_right (by decide) HE))

private def Bounded (A:CoefficientBankTermQuery.Arguments ℤ) (p:LeanCanny.ETR.Term) (M:ℕ):Prop:=
  MvMass.mass (CoefficientBankTermQuery.polynomial A p)≤M

private theorem bounded_snapshot (P:IntegralCriticalHistoryTask.Parameters)
    (D:IntegralMixedFramedHistoryFamilyBits.Plan P) (H:IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key:List Bool) (word:List Bool→List Bool) (M:ℕ)
    (h:MvMass.mass (MvPolynomial.rename (IntegralFramedPhysicalSquare.sampler P D H key).scalar
      (IntegralMixedFramedBankTermBits.polynomial P D H word key))≤M):
    Bounded (CoefficientBankTermQuery.ofSnapshot P D H key (IntegralFramedPhysicalSquare.count P D key)
      (IntegralFramedPhysicalSquare.sampler P D H key).scalar)
      ((IntegralMixedFramedBankTermBits.source word).syntax key) M:=by
  unfold Bounded
  rw [CoefficientBankTermQuery.polynomial_native]
  exact h

private theorem bounded_map (A:CoefficientBankTermQuery.Arguments ℤ[X]) (r:ℤ)
    (p:LeanCanny.ETR.Term) (M:ℕ)
    (h:Bounded (A.map (evalRingHom r)) p M):
    MvMass.mass (MvPolynomial.map (evalRingHom r) (CoefficientBankTermQuery.polynomial A p))≤M:=by
  rw [CoefficientBankTermQuery.polynomial_map]
  exact h

private theorem bounded_congr (A B:CoefficientBankTermQuery.Arguments ℤ) (he:A=B)
    (p:LeanCanny.ETR.Term) (M:ℕ) (h:Bounded B p M):Bounded A p M:=by
  cases he
  exact h

attribute [local irreducible] arguments polynomial CoefficientBankTermQuery.polynomial
  CoefficientBankTermQuery.ofSnapshot IntegralMixedFramedHistoryFamilyBits.family Bounded
  CoefficientMarkedRecordRowLayout.key IntegralMixedCausalRecordPlanBits.count
  IntegralMixedCausalRecordPlanBits.records

theorem mapped_mass (word:List Bool→List Bool) (ctx:List Bool) (R:List Bool→ℕ) (k:ℕ)
    (hk:k≤IntegralMixedCausalRecordPlanBits.count ctx) (aux:List Bool)
    (hlarge:CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha ctx≤R ctx):
    MvMass.mass (MvPolynomial.map (evalRingHom ((2:ℤ)^R ctx)) (polynomial hn ht ha word ctx k hk))≤
      2^(slope hn ht ha word ctx*R ctx+offset hn ht ha word ctx):=by
  let P:=IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha
  let D:=IntegralMixedAuxiliaryMarkedRecordPlan.plan hn ht ha R
  let H:=IntegralMixedAuxiliaryMarkedRecordPlan.data hn ht ha R
  let key:=CoefficientMarkedRecordRowLayout.key (n:=n) ctx k aux
  let A:=CoefficientBankTermQuery.ofSnapshot P D H key (IntegralFramedPhysicalSquare.count P D key)
    (IntegralFramedPhysicalSquare.sampler P D H key).scalar
  have HS:(IntegralMixedFramedBankTermBits.source word).syntax key=termSyntax word ctx:=by
    change LeanCanny.ETR.TermView.term (word (pairFst key))=_
    rw [CoefficientMarkedRecordRowLayout.key_root]
    rfl
  have HB0:=bounded_snapshot P D H key word _ (native_mass hn ht ha word ctx R k aux)
  have HB:Bounded A (termSyntax word ctx) (2^(slope hn ht ha word ctx*R ctx+offset hn ht ha word ctx)):=HS ▸ HB0
  have HE:=arguments_specialize hn ht ha ctx R k hk aux hlarge
  have HH:Bounded ((arguments hn ht ha ctx k hk).map (evalRingHom ((2:ℤ)^R ctx)))
      (termSyntax word ctx) (2^(slope hn ht ha word ctx*R ctx+offset hn ht ha word ctx)):=
    bounded_congr _ _ HE _ _ HB
  unfold polynomial
  exact bounded_map _ _ _ _ HH

theorem coefficient_degree_mass (word:List Bool→List Bool) (ctx:List Bool) (k:ℕ)
    (hk:k≤IntegralMixedCausalRecordPlanBits.count ctx)
    (e:Fin (arguments hn ht ha ctx k hk).dimension→₀ ℕ):
    ((polynomial hn ht ha word ctx k hk).coeff e).natDegree≤slope hn ht ha word ctx ∧
      coefficientMass ((polynomial hn ht ha word ctx k hk).coeff e)≤2^coefficientBudget hn ht ha word ctx:=by
  apply IntegerPolynomialDyadic.degree_mass_of_growth
  intro r hr
  have HM:=(MvMass.coeff_le _ e).trans (mapped_mass hn ht ha word ctx (fun _=>r) k hk [] hr)
  simpa only [MvPolynomial.coeff_map,Polynomial.coe_evalRingHom] using HM

end LeanCanny.Encoding.CoefficientMarkedRecordTermQuery
