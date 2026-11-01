/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaConjunctionWriter
public import LeanCanny.Encoding.WeakCircleCanonicalWriter
public import LeanCanny.Connectivity.MonotoneGateGraph
/-! # A native endpoint formula fixes every circle and every arithmetic gate uniquely -/
@[expose] public section
namespace LeanCanny.Encoding.MonotoneGateEndpoint
open LeanCanny.Computation LeanCanny.Connectivity ETR MonotoneGateSource LeanCanny.Geometry
open scoped Classical

def condition (F : Family) (q : List Bool) : Formula :=
  .and (WeakCircleCanonicalFormula.formula (F.atom q) (witnessIndex F q false) (witnessIndex F q true))
    (.eqZero (constraint F q))

def endpoint (F : Family) (s : Formula) (c : List Bool) : Formula :=
  .and s (FormulaConjunctionWriter.rangeConjunction (condition F) F.count c)

theorem condition_FP (F : Family) (hF : Access F) :
    (fun q => (condition F q).encode) ∈ FP := by
  have H0 : UnaryFn (fun q => witnessIndex F q false) := by
    simpa only [witnessIndex,Bool.toNat_false,Nat.add_zero] using
      (dimension_unary F hF).add ((UnaryFn.const 2).mul index_unary)
  have H1 : UnaryFn (fun q => witnessIndex F q true) :=
    ((dimension_unary F hF).add ((UnaryFn.const 2).mul index_unary)).add (UnaryFn.const 1)
  have HC := WeakCircleCanonicalWriter.formula_FP hF.atom H0 H1
  have HG := Codec.taggedOne_mem_FP 1 (constraint_FP F hF)
  apply mem_FP_of_eq (Codec.taggedTwo_mem_FP 4 HC HG)
  intro q
  simp only [condition,Formula.encode,Formula.toData,Codec.taggedTwo_toBits,Codec.taggedOne_toBits]

theorem endpoint_FP (F : Family) (hF : Access F) {s : List Bool → Formula}
    (hs : (fun c => (s c).encode) ∈ FP) :
    (fun c => (endpoint F (s c) c).encode) ∈ FP := by
  have HR := FormulaConjunctionWriter.range_FP (condition_FP F hF) hF.count
  apply mem_FP_of_eq (Codec.taggedTwo_mem_FP 4 hs HR)
  intro c
  simp only [endpoint,Formula.encode,Formula.toData,Codec.taggedTwo_toBits]

theorem endpoint_holds (F : Family) (s : Formula) (c : List Bool) (env : ℕ → ℝ) :
    (endpoint F s c).Holds env ↔ s.Holds env ∧ ∀ i < F.count c,
      (condition F (pair c (List.replicate i true))).Holds env := by
  simp only [endpoint,Formula.Holds,FormulaConjunctionWriter.rangeConjunction,
    FormulaConjunctionWriter.holds,List.forall_mem_map,List.mem_range]

theorem condition_arity (F : Family) (c : List Bool) (i : ℕ) (hi : i < F.count c)
    (ha : (F.atom (pair c (List.replicate i true))).arity≤F.dimension c) :
    (condition F (pair c (List.replicate i true))).arity≤MonotoneGateGraph.total F c := by
  have HG := constraint_arity F (pair c (List.replicate i true))
    (by simpa only [index,count,pairFst_pair,pairSnd_pair,List.length_replicate] using hi)
    (by simpa only [dimension,pairFst_pair] using ha)
  simp only [condition,Formula.arity,WeakCircleCanonicalFormula.arity]
  simp only [valueIndex,witnessIndex,dimension,count,index,pairFst_pair,pairSnd_pair,List.length_replicate,
    Bool.toNat_false,Bool.toNat_true,Nat.add_zero] at HG ⊢
  dsimp [MonotoneGateGraph.total,MonotoneGateGraph.base]
  omega

theorem endpoint_arity (F : Family) (s : Formula) (c : List Bool) (hs : s.arity≤F.dimension c)
    (ha : ∀ i < F.count c, (F.atom (pair c (List.replicate i true))).arity≤F.dimension c) :
    (endpoint F s c).arity≤MonotoneGateGraph.total F c := by
  apply max_le (hs.trans (by dsimp [MonotoneGateGraph.total,MonotoneGateGraph.base]; omega))
  apply FormulaConjunctionWriter.arity
  simp only [List.forall_mem_map,List.mem_range]
  exact fun i hi => condition_arity F c i hi (ha i hi)

end LeanCanny.Encoding.MonotoneGateEndpoint
