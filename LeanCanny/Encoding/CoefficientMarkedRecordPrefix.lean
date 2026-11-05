/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedPreludeActual
public import LeanCanny.Algebra.CoefficientMixedCutSourceDegree
public import LeanCanny.Algebra.CoefficientMixedCutAtInfinity
public import LeanCanny.Encoding.BoundedRegularRadiusLowModel
/-! # Constructed symbolic prefixes of the original marked raw records

Original bytes fix the tag, rule, degree and stored indices. Current Q and
normalization index are computed in the recursively constructed algebra.
The data has no requested radius or specialization/mass premise.
-/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordPrefix
open LeanCanny.Algebra LeanCanny.Computation IntegralMixedHistory Polynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n:List Bool→ℕ} {t:List Bool→LeanCanny.ETR.Term}
  (hn:UnaryFn n) (ht:(fun q=>(t q).toData.toBits)∈FP) (ha:∀q,(t q).arity≤n q)

noncomputable def source (ctx:List Bool) (radius:ℕ):=
  IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t (fun _=>radius) ctx

noncomputable def low (ctx:List Bool):
    MvPolynomial (Fin (IntegralMixedAuxiliaryMarkedIntegerSource.number n ctx+4)) ℤ[X]:=
  BoundedRegularRadiusLowModel.low
    ((t (IntegralMixedAuxiliaryMarkedIntegerSource.original ctx)).finitePolynomial
      (IntegralMixedAuxiliaryMarkedIntegerSource.number n ctx))
    (t (IntegralMixedAuxiliaryMarkedIntegerSource.original ctx)).toData.size
    (t (IntegralMixedAuxiliaryMarkedIntegerSource.original ctx)).toData.size

noncomputable def leading (ctx:List Bool):ℤ[X]:=
  BoundedRegularRadiusLowModel.leading (IntegralMixedAuxiliaryMarkedIntegerSource.number n ctx)
    (t (IntegralMixedAuxiliaryMarkedIntegerSource.original ctx)).toData.size
    (t (IntegralMixedAuxiliaryMarkedIntegerSource.original ctx)).toData.size

theorem source_fields (ctx:List Bool) (radius:ℕ):
    (low (n:=n) (t:=t) ctx).map (Polynomial.evalRingHom ((2:ℤ)^radius))=(source (n:=n) (t:=t) ctx radius).low ∧
    (leading (n:=n) (t:=t) ctx).eval ((2:ℤ)^radius)=(source (n:=n) (t:=t) ctx radius).leading:=by
  exact BoundedRegularRadiusLowModel.source_fields (IntegralMixedAuxiliaryMarkedIntegerSource.number n)
    (t∘IntegralMixedAuxiliaryMarkedIntegerSource.original) (fun _=>radius) ctx

theorem source_degree (ctx:List Bool) (radius:ℕ):
    (source (n:=n) (t:=t) ctx 0).degree=(source (n:=n) (t:=t) ctx radius).degree:=by
  unfold source
  rw [IntegralMixedAuxiliaryMarkedIntegerPlan.spatial_degree,
    IntegralMixedAuxiliaryMarkedIntegerPlan.spatial_degree]

theorem source_cap (ctx:List Bool):
    IntegralMixedExceptionalBounds.auxiliaryCap
      (IntegralMixedAuxiliaryMarkedIntegerSource.number n ctx+3+1) (source (n:=n) (t:=t) ctx 0).degree≤
      2^CoefficientMarkedIntegerBirth.width hn ht ha ctx:=by
  unfold source
  rw [IntegralMixedAuxiliaryMarkedIntegerPlan.spatial_degree]
  exact IntegralMixedAuxiliaryMarkedRecordPlan.spatial_cap hn ht ha ctx

noncomputable def cut (ctx:List Bool) (birth:ℕ) (code:List Bool):
    IntegralMixedCausalRecordBits.Cut (source (n:=n) (t:=t) ctx 0)
      (CoefficientMarkedIntegerBirth.width hn ht ha ctx):=
  IntegralMixedCausalUnitRecordBits.cut _ (by change 0<IntegralMixedAuxiliaryMarkedIntegerSource.number n ctx+3;omega)
    birth code (source_cap hn ht ha ctx)

def Index (ambient:ℕ) (base:Type):List (List Bool)→Type
  | []=>base
  | code::cs=>if IntegralMixedUnitRecordCode.critical code then
      (Index ambient base cs⊕FlatAffineCriticalStage.Variables (ambient+1))⊕Unit
    else Index ambient base cs⊕Unit

noncomputable def cutIndex {A:Type} [CommRing A] [Algebra ℤ[X] A] {m:ℕ}
    (ctx:List Bool) (bank:CoefficientHeightBank ℤ[X] A m)
    (b:CoefficientCoordinateBasis ℤ[X] A m (2^CoefficientMarkedIntegerBirth.width hn ht ha ctx))
    (birth:ℕ) (code:List Bool):ℕ:=
  let c:=cut hn ht ha ctx birth code
  CoefficientMixedCutAtInfinity.formalIndex b bank (low (n:=n) (t:=t) ctx) (leading (n:=n) (t:=t) ctx)
    (c.rule 1 one_ne_zero) c.current (c.kind 1 one_ne_zero) c.degree

noncomputable def build (ctx:List Bool) (S:ℕ):(cs:List (List Bool))→
    CoefficientHistoryPrefix.Prefix ℤ[X] S (CoefficientMarkedIntegerBirth.width hn ht ha ctx)
      ((CoefficientMarkedPreludeActual.indices n ctx).length+cs.length)
      (Index (IntegralMixedAuxiliaryMarkedIntegerSource.number n ctx+3)
        (CoefficientMarkedPreludePrefix.Index (CoefficientMarkedPreludeActual.indices n ctx)) cs)
  | []=>CoefficientMarkedPreludePrefix.build hn ht ha ctx S (CoefficientMarkedPreludeActual.indices n ctx)
  | code::cs=>by
    let F:=build ctx S cs
    let birth:=(CoefficientMarkedPreludeActual.indices n ctx).length+cs.length
    cases hc:IntegralMixedUnitRecordCode.critical code
    · let c:=cut hn ht ha ctx birth code
      let τ:=cutIndex hn ht ha ctx F.bank F.basis birth code
      simp only [Index,hc,Bool.false_eq_true,ite_false]
      exact CoefficientHistoryPrefix.scalarStep F
        (CoefficientMixedCutSpecialization.polynomial F.basis F.bank
          (low (n:=n) (t:=t) ctx) (leading (n:=n) (t:=t) ctx)
          (c.rule 1 one_ne_zero) c.current (c.kind 1 one_ne_zero) c.degree τ) c.degree
        (CoefficientMixedCutSpecialization.leading F.basis F.bank
          (low (n:=n) (t:=t) ctx) (leading (n:=n) (t:=t) ctx)
          (c.rule 1 one_ne_zero) c.current (c.kind 1 one_ne_zero) c.degree τ)
    · simp only [Index,hc,ite_true]
      exact CoefficientHistoryPrefix.criticalStep F (low (n:=n) (t:=t) ctx) (leading (n:=n) (t:=t) ctx)
        (source (n:=n) (t:=t) ctx 0).degree
        (IntegralMixedCausalUnitRecordBits.physical (IntegralMixedAuxiliaryMarkedIntegerSource.number n ctx+3) birth code)

end LeanCanny.Encoding.CoefficientMarkedRecordPrefix
