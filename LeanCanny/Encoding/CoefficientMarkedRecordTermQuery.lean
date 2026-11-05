/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.CoefficientBankTermQuery
public import LeanCanny.Encoding.CoefficientMarkedRecordBankProducts
public import LeanCanny.Encoding.CoefficientMarkedRecordRowBounds
/-! # Constructed term queries at the actual full physical columns -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordTermQuery
open LeanCanny.Algebra LeanCanny.Computation IntegralMixedHistory Polynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def pack {R:Type*} [CommRing R] (S W:ℕ)
    (D:CoefficientMarkedRecordRows.Data R) (q:R) (c:ℕ→R):CoefficientBankTermQuery.Arguments R:=
  ⟨S,W,D.birth,D.count,q,c,D.scalar⟩

private theorem pack_map {R S:Type*} [CommRing R] [CommRing S] (φ:R→+*S)
    (h w:ℕ) (D:CoefficientMarkedRecordRows.Data R) (q:R) (c:ℕ→R):
    (pack h w D q c).map φ=
      pack h w (CoefficientMarkedRecordRows.map φ D) (φ q) (fun i=>φ (c i)):=rfl

private theorem pack_snapshot (P:IntegralCriticalHistoryTask.Parameters)
    (D:IntegralMixedFramedHistoryFamilyBits.Plan P) (H:IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key:List Bool):
    pack (P.cap (pairFst key)+1) (P.width (pairFst key))
      (CoefficientMarkedRecordRowBounds.samplerData P D H key)
      (IntegralMixedFramedBankSnapshotBits.atKey P D H key).common
      (IntegralMixedFramedBankSnapshotBits.atKey P D H key).cofactor=
    CoefficientBankTermQuery.ofSnapshot P D H key (IntegralFramedPhysicalSquare.count P D key)
      (IntegralFramedPhysicalSquare.sampler P D H key).scalar:=rfl

private theorem native_polynomial_heq (P:IntegralCriticalHistoryTask.Parameters)
    (D:IntegralMixedFramedHistoryFamilyBits.Plan P) (H:IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key:List Bool) (word:List Bool→List Bool):
    HEq (CoefficientBankTermQuery.polynomial
      (CoefficientBankTermQuery.ofSnapshot P D H key (IntegralFramedPhysicalSquare.count P D key)
        (IntegralFramedPhysicalSquare.sampler P D H key).scalar)
      ((IntegralMixedFramedBankTermBits.source word).syntax key))
      (MvPolynomial.rename (IntegralFramedPhysicalSquare.sampler P D H key).scalar
        (IntegralMixedFramedBankTermBits.polynomial P D H word key)):=
  heq_of_eq (CoefficientBankTermQuery.polynomial_native P D H key (IntegralFramedPhysicalSquare.count P D key)
    (IntegralFramedPhysicalSquare.sampler P D H key).scalar word)

private theorem family_resources (P:IntegralCriticalHistoryTask.Parameters)
    (D:IntegralMixedFramedHistoryFamilyBits.Plan P) (H:IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key:List Bool):
    ((IntegralMixedFramedHistoryFamilyBits.family P D H).cap key,
      (IntegralMixedFramedHistoryFamilyBits.family P D H).width key)=
      (P.cap (pairFst key)+1,P.width (pairFst key)):=rfl

variable {n:List Bool→ℕ} {t:List Bool→LeanCanny.ETR.Term}
  (hn:UnaryFn n) (ht:(fun q=>(t q).toData.toBits)∈FP) (ha:∀q,(t q).arity≤n q)

noncomputable def arguments (ctx:List Bool) (k:ℕ) (hk:k≤IntegralMixedCausalRecordPlanBits.count ctx):
    CoefficientBankTermQuery.Arguments ℤ[X]:=
  pack (CoefficientMarkedRecordActual.horizon hn ht ha ctx) (CoefficientMarkedIntegerBirth.width hn ht ha ctx)
    (CoefficientMarkedRecordRows.symbolic hn ht ha ctx k hk)
    (CoefficientMarkedRecordBankProducts.common hn ht ha ctx k)
    (CoefficientMarkedRecordBankProducts.cofactor hn ht ha ctx k)

noncomputable def termSyntax (word:List Bool→List Bool) (ctx:List Bool):LeanCanny.ETR.Term:=
  LeanCanny.ETR.TermView.term (word ctx)

noncomputable def polynomial (word:List Bool→List Bool) (ctx:List Bool) (k:ℕ)
    (hk:k≤IntegralMixedCausalRecordPlanBits.count ctx):
    MvPolynomial (Fin (arguments hn ht ha ctx k hk).dimension) ℤ[X]:=
  CoefficientBankTermQuery.polynomial (arguments hn ht ha ctx k hk) (termSyntax word ctx)

attribute [local irreducible] CoefficientMarkedRecordNative.run CoefficientMarkedRecordPrefix.build
  IntegralMixedSourceIntegerRecordAppend.plan CoefficientMarkedRecordRowBounds.samplerData
  arguments pack CoefficientBankTermQuery.polynomial CoefficientBankTermQuery.ofSnapshot
  IntegralMixedFramedHistoryFamilyBits.family
  IntegralMixedAuxiliaryMarkedIntegerSource.candidate IntegralMixedAuxiliaryCandidate.sourceInput
  IntegralMixedAuxiliaryCandidate.source IntegralMixedAuxiliaryMarkedIntegerSource.oldKey

private theorem resource_pair (ctx:List Bool) (k:ℕ) (aux:List Bool):
    (CoefficientMarkedRecordActual.horizon hn ht ha ctx,CoefficientMarkedIntegerBirth.width hn ht ha ctx)=
      ((IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha).cap
        (pairFst (CoefficientMarkedRecordRowLayout.key (n:=n) ctx k aux))+1,
       (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha).width
        (pairFst (CoefficientMarkedRecordRowLayout.key (n:=n) ctx k aux))):=by
  let P:=IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha
  let key:=CoefficientMarkedRecordRowLayout.key (n:=n) ctx k aux
  have HC:CoefficientMarkedRecordActual.horizon hn ht ha ctx=P.cap ctx+1:=rfl
  have HW:CoefficientMarkedIntegerBirth.width hn ht ha ctx=P.width ctx:=rfl
  have HK:pairFst key=ctx:=CoefficientMarkedRecordRowLayout.key_root (n:=n) ctx k aux
  have H0:(CoefficientMarkedRecordActual.horizon hn ht ha ctx,CoefficientMarkedIntegerBirth.width hn ht ha ctx)=
      (P.cap ctx+1,P.width ctx):=
    congrArg₂ (fun a b:ℕ=>(a,b)) HC HW
  have H1:(P.cap ctx+1,P.width ctx)=(P.cap (pairFst key)+1,P.width (pairFst key)):=
    congrArg (fun root:List Bool=>(P.cap root+1,P.width root)) HK.symm
  exact H0.trans H1

theorem arguments_specialize (ctx:List Bool) (R:List Bool→ℕ) (k:ℕ)
    (hk:k≤IntegralMixedCausalRecordPlanBits.count ctx) (aux:List Bool)
    (hlarge:CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha ctx≤R ctx):
    (arguments hn ht ha ctx k hk).map (evalRingHom ((2:ℤ)^R ctx))=
      CoefficientBankTermQuery.ofSnapshot (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha)
        (IntegralMixedAuxiliaryMarkedRecordPlan.plan hn ht ha R) (IntegralMixedAuxiliaryMarkedRecordPlan.data hn ht ha R)
        (CoefficientMarkedRecordRowLayout.key (n:=n) ctx k aux)
        (IntegralFramedPhysicalSquare.count (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha)
          (IntegralMixedAuxiliaryMarkedRecordPlan.plan hn ht ha R) (CoefficientMarkedRecordRowLayout.key (n:=n) ctx k aux))
        (IntegralFramedPhysicalSquare.sampler (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha)
          (IntegralMixedAuxiliaryMarkedRecordPlan.plan hn ht ha R) (IntegralMixedAuxiliaryMarkedRecordPlan.data hn ht ha R)
          (CoefficientMarkedRecordRowLayout.key (n:=n) ctx k aux)).scalar:=by
  let P:=IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha
  let D:=IntegralMixedAuxiliaryMarkedRecordPlan.plan hn ht ha R
  let H:=IntegralMixedAuxiliaryMarkedRecordPlan.data hn ht ha R
  let key:=CoefficientMarkedRecordRowLayout.key (n:=n) ctx k aux
  have HE:=CoefficientMarkedRecordRows.map_indexed hn ht ha ctx R k hk aux hlarge
  have HP:=CoefficientMarkedRecordBankProducts.products_specialize hn ht ha ctx R k hk aux hlarge
  have HR:=resource_pair hn ht ha ctx k aux
  unfold arguments
  refine (pack_map (evalRingHom ((2:ℤ)^R ctx)) _ _ _ _ _).trans ?_
  have HData:=congrArg (fun data=>pack
    (CoefficientMarkedRecordActual.horizon hn ht ha ctx) (CoefficientMarkedIntegerBirth.width hn ht ha ctx)
    data ((CoefficientMarkedRecordBankProducts.common hn ht ha ctx k).eval ((2:ℤ)^R ctx))
    (fun i=>(CoefficientMarkedRecordBankProducts.cofactor hn ht ha ctx k i).eval ((2:ℤ)^R ctx))) HE
  refine HData.trans ?_
  have HProducts:=congrArg (fun p:ℤ×(ℕ→ℤ)=>pack
    (CoefficientMarkedRecordActual.horizon hn ht ha ctx) (CoefficientMarkedIntegerBirth.width hn ht ha ctx)
    (CoefficientMarkedRecordRows.indexed hn ht ha ctx R k aux) p.1 p.2) HP
  change pack _ _ _ _ _= _ at HProducts
  refine HProducts.trans ?_
  have HResource:=congrArg (fun p:ℕ×ℕ=>pack p.1 p.2
    (CoefficientMarkedRecordRows.indexed hn ht ha ctx R k aux)
    (IntegralMixedFramedBankSnapshotBits.atKey P D H key).common
    (IntegralMixedFramedBankSnapshotBits.atKey P D H key).cofactor) HR
  have HI:CoefficientMarkedRecordRows.indexed hn ht ha ctx R k aux=
      CoefficientMarkedRecordRowBounds.samplerData P D H key:=by
    unfold CoefficientMarkedRecordRows.indexed CoefficientMarkedRecordRowBounds.samplerData
    rfl
  have HF:=congrArg (fun data=>pack (P.cap (pairFst key)+1) (P.width (pairFst key)) data
    (IntegralMixedFramedBankSnapshotBits.atKey P D H key).common
    (IntegralMixedFramedBankSnapshotBits.atKey P D H key).cofactor) HI
  have HLast:=pack_snapshot P D H key
  have HLast2:=HF.trans HLast
  exact HResource.trans HLast2

theorem polynomial_specialize (word:List Bool→List Bool) (ctx:List Bool) (R:List Bool→ℕ) (k:ℕ)
    (hk:k≤IntegralMixedCausalRecordPlanBits.count ctx) (aux:List Bool)
    (hlarge:CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha ctx≤R ctx):
    HEq (MvPolynomial.map (evalRingHom ((2:ℤ)^R ctx)) (polynomial hn ht ha word ctx k hk))
      (MvPolynomial.rename
        (IntegralFramedPhysicalSquare.sampler (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha)
          (IntegralMixedAuxiliaryMarkedRecordPlan.plan hn ht ha R) (IntegralMixedAuxiliaryMarkedRecordPlan.data hn ht ha R)
          (CoefficientMarkedRecordRowLayout.key (n:=n) ctx k aux)).scalar
        (IntegralMixedFramedBankTermBits.polynomial (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha)
          (IntegralMixedAuxiliaryMarkedRecordPlan.plan hn ht ha R) (IntegralMixedAuxiliaryMarkedRecordPlan.data hn ht ha R)
          word (CoefficientMarkedRecordRowLayout.key (n:=n) ctx k aux))):=by
  let P:=IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha
  let D:=IntegralMixedAuxiliaryMarkedRecordPlan.plan hn ht ha R
  let H:=IntegralMixedAuxiliaryMarkedRecordPlan.data hn ht ha R
  let key:=CoefficientMarkedRecordRowLayout.key (n:=n) ctx k aux
  let A:=CoefficientBankTermQuery.ofSnapshot P D H key (IntegralFramedPhysicalSquare.count P D key)
    (IntegralFramedPhysicalSquare.sampler P D H key).scalar
  have HE:=CoefficientBankTermQuery.polynomial_heq_of_eq _ A
    (arguments_specialize hn ht ha ctx R k hk aux hlarge) (termSyntax word ctx)
  have HS:(IntegralMixedFramedBankTermBits.source word).syntax key=termSyntax word ctx:=by
    change LeanCanny.ETR.TermView.term (word (pairFst key))=termSyntax word ctx
    rw [CoefficientMarkedRecordRowLayout.key_root]
    rfl
  have HN:=native_polynomial_heq P D H key word
  have HT:=congrArg (CoefficientBankTermQuery.polynomial A) HS
  have HM:=CoefficientBankTermQuery.polynomial_map (evalRingHom ((2:ℤ)^R ctx))
    (arguments hn ht ha ctx k hk) (termSyntax word ctx)
  exact (heq_of_eq HM).trans (HE.trans ((heq_of_eq HT.symm).trans HN))

end LeanCanny.Encoding.CoefficientMarkedRecordTermQuery
