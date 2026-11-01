/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.PositiveMarginSourceBounds
/-! # Native endpoint extension retains every old candidate, including a zero-margin point -/
@[expose] public section
namespace LeanCanny.Encoding.PositiveMarginSource
open LeanCanny.Computation ETR LeanCanny.Connectivity
open MonotoneGateSource

def endpointRule (F : Family) (c : List Bool) : Formula :=
  .or (.and (.eqZero (root F c)) (.eqZero (.var (F.dimension c+F.count c)))) (.eqZero (reciprocal F c))

def endpoint (F : Family) (s : Formula) (c : List Bool) : Formula :=
  .and s (.and (FormulaConjunctionWriter.rangeConjunction (condition F) F.count c) (endpointRule F c))

theorem endpointRule_FP (F : Family) (hF : Access F) : (fun c => (endpointRule F c).encode) ∈ FP := by
  have HV := mem_FP_of_eq (Term.variableBits_mem_FP (hF.dimension.add hF.count)) (fun c => Term.variableBits_eq (F.dimension c+F.count c))
  have H:=Codec.taggedTwo_mem_FP 5 (Codec.taggedTwo_mem_FP 4 (Codec.taggedOne_mem_FP 1 (root_FP F hF))
    (Codec.taggedOne_mem_FP 1 HV)) (Codec.taggedOne_mem_FP 1 (reciprocal_FP F hF))
  apply mem_FP_of_eq H
  intro c
  simp only [endpointRule,Formula.encode,Formula.toData,Codec.taggedTwo_toBits,Codec.taggedOne_toBits]

theorem endpoint_FP (F : Family) (hF : Access F) {s : List Bool → Formula}
    (hs : (fun c => (s c).encode) ∈ FP) : (fun c => (endpoint F (s c) c).encode) ∈ FP := by
  have H:=Codec.taggedTwo_mem_FP 4 hs (Codec.taggedTwo_mem_FP 4
    (FormulaConjunctionWriter.range_FP (condition_FP F hF) hF.count) (endpointRule_FP F hF))
  apply mem_FP_of_eq H
  intro c
  simp only [endpoint,Formula.encode,Formula.toData,Codec.taggedTwo_toBits]

theorem endpointRule_arity (F : Family) (c : List Bool) : (endpointRule F c).arity≤total F c := by
  have HR:=root_arity F c
  have HC:=reciprocal_arity F c
  simp only [endpointRule,Formula.arity,Term.arity,total] at *
  omega

theorem conditions_arity (F : Family) (c : List Bool)
    (ha : ∀ i < F.count c, (F.atom (pair c (List.replicate i true))).arity≤F.dimension c) :
    (FormulaConjunctionWriter.rangeConjunction (condition F) F.count c).arity≤total F c := by
  have H:=source_arity F c ha
  change max (reciprocal F c).arity (FormulaConjunctionWriter.rangeConjunction (condition F) F.count c).arity≤total F c at H
  exact (Nat.le_max_right _ _).trans H

theorem endpoint_arity (F : Family) (s : Formula) (c : List Bool) (hs : s.arity≤F.dimension c)
    (ha : ∀ i < F.count c, (F.atom (pair c (List.replicate i true))).arity≤F.dimension c) :
    (endpoint F s c).arity≤total F c :=
  max_le (hs.trans (by unfold total; omega)) (max_le (conditions_arity F c ha) (endpointRule_arity F c))

end LeanCanny.Encoding.PositiveMarginSource
