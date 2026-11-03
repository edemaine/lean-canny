/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedCausalRecordDegree
public import LeanCanny.Algebra.IntegralMixedRelativeCutSpecialized
/-! # Exact decoded command for a chosen specialized cut degree

A valid selected factor with a real root determines the specialized degree.
Rewriting that field preserves its actual source, rule, kind and current Q;
there is no assertion that an arbitrary causal record has a real solution.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedCausalRecordDegree
open LeanCanny.Algebra LeanCanny.Computation IntegralMixedHistory
open IntegralMixedCausalRecordBits
open IntegralMixedUnitRecordCode (field)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem cut {n B : ℕ} (S : SpatialSource n) (hn : 0<n) (birth : ℕ)
    (code : List Bool) (d : ℕ) (hd : d≤IntegralMixedExceptionalBounds.auxiliaryCap (n+1) S.degree)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) S.degree≤2^B) :
    IntegralMixedCausalUnitRecordBits.cut S hn birth (withDegree code d) hcap=
      { IntegralMixedCausalUnitRecordBits.cut S hn birth code hcap with
        degree:=d,source_cap:=hd,degree_cap:=hd.trans hcap }:=by
  simp only [IntegralMixedCausalUnitRecordBits.cut,virtual,writtenDegree S code d hd,
    IntegralMixedCausalUnitRecordBits.tag,IntegralMixedCausalUnitRecordBits.current,
    field_4,field_8,field_10,field_11]

theorem command {n B : ℕ} (S : SpatialSource n) (hn : 0<n) (birth : ℕ)
    (code : List Bool) (hcut : IntegralMixedUnitRecordCode.critical code=false)
    (d : ℕ) (hd : d≤IntegralMixedExceptionalBounds.auxiliaryCap (n+1) S.degree)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) S.degree≤2^B)
    (Q : ℤ) (hQ : Q≠0) :
    (IntegralMixedCausalUnitRecordBits.record S hn birth (withDegree code d) hcap).template.command Q hQ=
      .cut ((IntegralMixedCausalUnitRecordBits.cut S hn birth code hcap).rule Q hQ)
        ((IntegralMixedCausalUnitRecordBits.cut S hn birth code hcap).kind Q hQ) d hd (hd.trans hcap):=by
  simp only [IntegralMixedCausalUnitRecordBits.record,IntegralMixedUnitRecordCode.critical,
    field_0] at *
  simp only [hcut,Bool.false_eq_true,ite_false,Template.command,cut S hn birth code d hd hcap]
  rfl

theorem selectedDegree_readback {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
    (x : State P S B m ι) (hm : m≤S) (hn : 0<n) (code : List Bool)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) :
    let q:=commonDenominator x
    let hq:=commonDenominator_ne_zero x
    let cut:=IntegralMixedCausalUnitRecordBits.cut P hn m code hcap
    let d:=IntegralMixedRelativeCuts.selectedDegree x hm (cut.rule q hq) φ (cut.kind q hq)
    IntegralMixedCanonicalUnitRuleBits.writtenDegree P (withDegree code d)=d:=by
  dsimp only
  exact writtenDegree _ _ _ (IntegralMixedRelativeCuts.selectedDegree_bound _ _ _ _ _)

end LeanCanny.Encoding.IntegralMixedCausalRecordDegree
