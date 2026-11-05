/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordRowLayout
/-! # Computed integer-parameter rows and scalar columns of the actual sampler -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordRows
open LeanCanny.Algebra LeanCanny.Computation IntegralMixedHistory Polynomial
open IntegralMixedFramedPhysicalLayoutCongruence
open scoped Classical
set_option backward.isDefEq.respectTransparency false

structure Data (R:Type*) [CommRing R] where
  count:ℕ
  birth:ℕ
  rows:Fin count→MvPolynomial (Fin count) R
  scalar:Fin birth→Fin count

noncomputable def map {R S:Type*} [CommRing R] [CommRing S] (f:R→+*S) (D:Data R):Data S:=
  ⟨D.count,D.birth,fun i=>MvPolynomial.map f (D.rows i),D.scalar⟩

noncomputable def stateData {a S B m:ℕ} {P:SpatialSource a} (L:Layout)
    (x:State P S B m L.index):Data ℤ:=
  ⟨L.count,m,PolynomialSystemReindex.system L.enumeration x.sampler.rows,L.enumeration∘x.sampler.scalar⟩

noncomputable def prefixData {S B m:ℕ} (L:Layout)
    (F:CoefficientHistoryPrefix.Prefix ℤ[X] S B m L.index):Data ℤ[X]:=
  ⟨L.count,m,PolynomialSystemReindex.system L.enumeration F.rows,L.enumeration∘F.scalar⟩

private theorem prefixData_map {a S B m radius:ℕ} {P:SpatialSource a} (L M:Layout)
    (F:CoefficientHistoryPrefix.Prefix ℤ[X] S B m L.index) (x:State P S B m M.index)
    (he:L=M) (h:CoefficientHistoryPrefix.Specializes radius F x):
    map (evalRingHom ((2:ℤ)^radius)) (prefixData L F)=stateData M x:=by
  cases he
  obtain ⟨_,_,_,hr,hs⟩:=h.pointwise
  have HR:(fun i=>MvPolynomial.map (evalRingHom ((2:ℤ)^radius))
      (PolynomialSystemReindex.system L.enumeration F.rows i))=
      PolynomialSystemReindex.system L.enumeration x.sampler.rows:=by
    funext i
    simp only [PolynomialSystemReindex.system,MvPolynomial.map_rename]
    exact congrArg (MvPolynomial.rename L.enumeration) (hr (L.enumeration.symm i))
  have HS:L.enumeration∘F.scalar=L.enumeration∘x.sampler.scalar:=
    congrArg (fun f=>L.enumeration∘f) hs
  exact congrArg₂ (fun r s=>(⟨L.count,m,r,s⟩:Data ℤ)) HR HS

private theorem stateData_transport {a b S T B C m k:ℕ} {P:SpatialSource a} {Q:SpatialSource b}
    (L M:Layout) (x:State P S B m L.index) (y:State Q T C k M.index)
    (en:a=b) (eS:S=T) (eB:B=C) (em:m=k) (eP:HEq P Q) (eL:L=M) (he:HEq x y):
    stateData L x=stateData M y:=by
  cases en
  cases eS
  cases eB
  cases em
  cases eL
  cases eq_of_heq eP
  cases eq_of_heq he
  rfl

private theorem source_at_root (N:List Bool→ℕ) (P:∀root,SpatialSource (N root))
    (root root':List Bool) (h:root'=root):HEq (P root) (P root'):=by
  cases h
  rfl

variable {n:List Bool→ℕ} {t:List Bool→LeanCanny.ETR.Term}
  (hn:UnaryFn n) (ht:(fun q=>(t q).toData.toBits)∈FP) (ha:∀q,(t q).arity≤n q)

noncomputable def symbolic (ctx:List Bool) (k:ℕ) (hk:k≤IntegralMixedCausalRecordPlanBits.count ctx):Data ℤ[X]:=
  prefixData (CoefficientMarkedRecordRowLayout.fixed hn ht ha ctx k hk)
    (CoefficientMarkedRecordPrefix.build hn ht ha ctx (CoefficientMarkedRecordActual.horizon hn ht ha ctx)
      (CoefficientMarkedRecordActual.codes ctx k))

noncomputable def native (ctx:List Bool) (R:List Bool→ℕ) (k:ℕ)
    (hk:k≤IntegralMixedCausalRecordPlanBits.count ctx):Data ℤ:=
  stateData (CoefficientMarkedRecordRowLayout.fixed hn ht ha ctx k hk)
    (CoefficientMarkedRecordNative.run hn ht ha ctx R (CoefficientMarkedRecordActual.horizon hn ht ha ctx)
      (CoefficientMarkedRecordActual.codes ctx k) (CoefficientMarkedRecordActual.prefix_room hn ht ha ctx k hk))

noncomputable def indexed (ctx:List Bool) (R:List Bool→ℕ) (k:ℕ) (aux:List Bool):Data ℤ:=
  let P:=IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha
  let D:=IntegralMixedAuxiliaryMarkedRecordPlan.plan hn ht ha R
  let H:=IntegralMixedAuxiliaryMarkedRecordPlan.data hn ht ha R
  let key:=CoefficientMarkedRecordRowLayout.key (n:=n) ctx k aux
  let sampler:=IntegralFramedPhysicalSquare.sampler P D H key
  ⟨IntegralFramedPhysicalSquare.count P D key,(IntegralMixedFramedHistoryFamilyBits.family P D H).birth key,
    sampler.rows,sampler.scalar⟩

attribute [local irreducible] CoefficientMarkedRecordNative.run CoefficientMarkedRecordPrefix.build
  IntegralMixedSourceIntegerRecordAppend.plan CoefficientMarkedRecordRowLayout.commands

private theorem family_width_at (P:IntegralCriticalHistoryTask.Parameters)
    (D:IntegralMixedFramedHistoryFamilyBits.Plan P) (H:IntegralMixedFramedHistoryFamilyBits.Data P D) (key:List Bool):
    (IntegralMixedFramedHistoryFamilyBits.family P D H).width key=P.width (pairFst key):=rfl

private theorem family_cap_at (P:IntegralCriticalHistoryTask.Parameters)
    (D:IntegralMixedFramedHistoryFamilyBits.Plan P) (H:IntegralMixedFramedHistoryFamilyBits.Data P D) (key:List Bool):
    (IntegralMixedFramedHistoryFamilyBits.family P D H).cap key=P.cap (pairFst key)+1:=rfl

private theorem family_ambient_at (P:IntegralCriticalHistoryTask.Parameters)
    (D:IntegralMixedFramedHistoryFamilyBits.Plan P) (H:IntegralMixedFramedHistoryFamilyBits.Data P D) (key:List Bool):
    (IntegralMixedFramedHistoryFamilyBits.family P D H).ambient key=P.ambient (pairFst key):=rfl

theorem family_width (ctx:List Bool) (R:List Bool→ℕ) (k:ℕ) (aux:List Bool):
    CoefficientMarkedIntegerBirth.width hn ht ha ctx=
      (IntegralMixedAuxiliaryMarkedRecordRadiusHeight.actualFamily hn ht ha R).width
        (CoefficientMarkedRecordRowLayout.key (n:=n) ctx k aux):=by
  let P:=IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha
  have HB:P.width ctx=CoefficientMarkedIntegerBirth.width hn ht ha ctx:=rfl
  exact (HB.symm.trans (congrArg P.width (CoefficientMarkedRecordRowLayout.key_root (n:=n) ctx k aux)).symm).trans
    (family_width_at P (IntegralMixedAuxiliaryMarkedRecordPlan.plan hn ht ha R)
      (IntegralMixedAuxiliaryMarkedRecordPlan.data hn ht ha R) _).symm

theorem family_cap (ctx:List Bool) (R:List Bool→ℕ) (k:ℕ) (aux:List Bool):
    CoefficientMarkedRecordActual.horizon hn ht ha ctx=
      (IntegralMixedAuxiliaryMarkedRecordRadiusHeight.actualFamily hn ht ha R).cap
        (CoefficientMarkedRecordRowLayout.key (n:=n) ctx k aux):=by
  let P:=IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha
  exact (congrArg (fun root=>P.cap root+1) (CoefficientMarkedRecordRowLayout.key_root (n:=n) ctx k aux)).symm.trans
    (family_cap_at P (IntegralMixedAuxiliaryMarkedRecordPlan.plan hn ht ha R)
      (IntegralMixedAuxiliaryMarkedRecordPlan.data hn ht ha R) _).symm

theorem family_ambient (ctx:List Bool) (R:List Bool→ℕ) (k:ℕ) (aux:List Bool):
    IntegralMixedAuxiliaryMarkedIntegerSource.number n ctx+3=
      (IntegralMixedAuxiliaryMarkedRecordRadiusHeight.actualFamily hn ht ha R).ambient
        (CoefficientMarkedRecordRowLayout.key (n:=n) ctx k aux):=by
  let P:=IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha
  exact (congrArg P.ambient (CoefficientMarkedRecordRowLayout.key_root (n:=n) ctx k aux)).symm.trans
    (family_ambient_at P (IntegralMixedAuxiliaryMarkedRecordPlan.plan hn ht ha R)
      (IntegralMixedAuxiliaryMarkedRecordPlan.data hn ht ha R) _).symm

theorem family_birth (ctx:List Bool) (R:List Bool→ℕ) (k:ℕ)
    (hk:k≤IntegralMixedCausalRecordPlanBits.count ctx) (aux:List Bool):
    (CoefficientMarkedPreludeActual.indices n ctx).length+(CoefficientMarkedRecordActual.codes ctx k).length=
      (IntegralMixedAuxiliaryMarkedRecordRadiusHeight.actualFamily hn ht ha R).birth
        (CoefficientMarkedRecordRowLayout.key (n:=n) ctx k aux):=by
  have H: (IntegralMixedAuxiliaryMarkedRecordRadiusHeight.actualFamily hn ht ha R).birth
      (CoefficientMarkedRecordRowLayout.key (n:=n) ctx k aux)=
      (CoefficientMarkedPreludeActual.indices n ctx).length+k:=
    (IntegralMixedFramedHistoryFamilyBits.family_birth (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha)
      (IntegralMixedAuxiliaryMarkedRecordPlan.plan hn ht ha R) (IntegralMixedAuxiliaryMarkedRecordPlan.data hn ht ha R) _).trans
      (IntegralMixedFramedHistoryFamilyBits.keyAt_prefix _ ctx _ aux
        (CoefficientMarkedRecordActual.birth_room hn ht ha ctx k hk))
  exact (congrArg (Nat.add (CoefficientMarkedPreludeActual.indices n ctx).length)
    (CoefficientMarkedRecordActual.codes_length ctx k)).trans H.symm

theorem family_source (ctx:List Bool) (R:List Bool→ℕ) (k:ℕ) (aux:List Bool):
    HEq (CoefficientMarkedRecordNative.source (n:=n) (t:=t) ctx R)
      ((IntegralMixedAuxiliaryMarkedRecordRadiusHeight.actualFamily hn ht ha R).spatial
        (CoefficientMarkedRecordRowLayout.key (n:=n) ctx k aux)):=by
  let key:=CoefficientMarkedRecordRowLayout.key (n:=n) ctx k aux
  have HS: (IntegralMixedAuxiliaryMarkedRecordRadiusHeight.actualFamily hn ht ha R).spatial key=
      IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t R (pairFst key):=
    (IntegralMixedFramedHistoryFamilyBits.family_spatial (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha)
      (IntegralMixedAuxiliaryMarkedRecordPlan.plan hn ht ha R) (IntegralMixedAuxiliaryMarkedRecordPlan.data hn ht ha R) key).trans
      (IntegralMixedAuxiliaryMarkedRecordPlan.instruction_source hn ht ha R key)
  exact (source_at_root (fun root=>IntegralMixedAuxiliaryMarkedIntegerSource.number n root+3)
    (IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t R) ctx (pairFst key)
    (CoefficientMarkedRecordRowLayout.key_root (n:=n) ctx k aux)).trans (heq_of_eq HS).symm

/-- The literal oldest-first ordering includes every physical and multiplier row. -/
theorem native_eq_indexed (ctx:List Bool) (R:List Bool→ℕ) (k:ℕ)
    (hk:k≤IntegralMixedCausalRecordPlanBits.count ctx) (aux:List Bool):
    native hn ht ha ctx R k hk=indexed hn ht ha ctx R k aux:=by
  let P:=IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha
  let D:=IntegralMixedAuxiliaryMarkedRecordPlan.plan hn ht ha R
  let H:=IntegralMixedAuxiliaryMarkedRecordPlan.data hn ht ha R
  let G:=IntegralMixedFramedHistoryFamilyBits.family P D H
  let key:=CoefficientMarkedRecordRowLayout.key (n:=n) ctx k aux
  let L:=CoefficientMarkedRecordRowLayout.fixed hn ht ha ctx k hk
  let M:=layout (IntegralMixedFramedHistoryFamilyBits.commands P D key)
  let x:=CoefficientMarkedRecordNative.run hn ht ha ctx R (CoefficientMarkedRecordActual.horizon hn ht ha ctx)
    (CoefficientMarkedRecordActual.codes ctx k) (CoefficientMarkedRecordActual.prefix_room hn ht ha ctx k hk)
  let y:=G.state key
  have HL:L=M:=(CoefficientMarkedRecordRowLayout.family_layout hn ht ha ctx R k hk aux).symm
  have HX:=CoefficientMarkedRecordActual.native_family hn ht ha ctx R k hk aux
  change stateData L x=stateData M y
  exact stateData_transport L M x y (family_ambient hn ht ha ctx R k aux)
    (family_cap hn ht ha ctx R k aux) (family_width hn ht ha ctx R k aux)
    (family_birth hn ht ha ctx R k hk aux) (family_source hn ht ha ctx R k aux) HL HX

/-- Equations and scalar columns specialize to the actual indexed sampler. -/
theorem map_indexed (ctx:List Bool) (R:List Bool→ℕ) (k:ℕ)
    (hk:k≤IntegralMixedCausalRecordPlanBits.count ctx) (aux:List Bool)
    (hR:CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha ctx≤R ctx):
    map (evalRingHom ((2:ℤ)^R ctx)) (symbolic hn ht ha ctx k hk)=indexed hn ht ha ctx R k aux:=
  (prefixData_map _ _ _ _ rfl
    (CoefficientMarkedRecordEffectiveCutoff.specializes_above_effective hn ht ha ctx R k hk hR)).trans
    (native_eq_indexed hn ht ha ctx R k hk aux)

private theorem rows_of_eq {R:Type*} [CommRing R] (A B:Data R) (he:A=B):HEq A.rows B.rows:=by
  cases he
  rfl

private theorem scalar_of_eq {R:Type*} [CommRing R] (A B:Data R) (he:A=B):HEq A.scalar B.scalar:=by
  cases he
  rfl

theorem rows_map_heq (ctx:List Bool) (R:List Bool→ℕ) (k:ℕ)
    (hk:k≤IntegralMixedCausalRecordPlanBits.count ctx) (aux:List Bool)
    (hR:CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha ctx≤R ctx):
    HEq (fun i=>MvPolynomial.map (evalRingHom ((2:ℤ)^R ctx)) ((symbolic hn ht ha ctx k hk).rows i))
      (indexed hn ht ha ctx R k aux).rows:=
  rows_of_eq _ _ (map_indexed hn ht ha ctx R k hk aux hR)

theorem scalar_column_heq (ctx:List Bool) (R:List Bool→ℕ) (k:ℕ)
    (hk:k≤IntegralMixedCausalRecordPlanBits.count ctx) (aux:List Bool)
    (hR:CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha ctx≤R ctx):
    HEq (symbolic hn ht ha ctx k hk).scalar (indexed hn ht ha ctx R k aux).scalar:=
  scalar_of_eq _ _ (map_indexed hn ht ha ctx R k hk aux hR)

end LeanCanny.Encoding.CoefficientMarkedRecordRows
