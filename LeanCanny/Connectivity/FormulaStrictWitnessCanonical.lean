/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.FormulaStrictWitnessEndpoints
public import LeanCanny.Connectivity.InputFP
/-! # Native canonical connectivity records for the strict-conjunct reduction

This is a component-preserving reduction for a strict conjunct inside an
arbitrary old Boolean context. It does not commute with disjunction and
is not a reduction of arbitrary Boolean formulas to equations.
-/
@[expose] public section
namespace LeanCanny.Connectivity.FormulaStrictWitness
open ETR LeanCanny.Encoding LeanCanny.Computation
open scoped Classical

theorem lifted_formula_FP {n : List Bool → ℕ} {p : List Bool → Formula} {t : List Bool → Term}
    (hn : UnaryFn n) (hp : (fun q => (p q).encode) ∈ FP) (ht : (fun q => (t q).toData.toBits) ∈ FP) :
    (fun q => (lifted (n q) (p q) (t q)).formula.encode) ∈ FP := by
  have H := Codec.taggedTwo_mem_FP 4 hp (Codec.taggedOne_mem_FP 1 (term_bits_FP hn ht))
  apply mem_FP_of_eq H
  intro q
  simp only [lifted,Formula.encode,Formula.toData,Codec.taggedOne_toBits,Codec.taggedTwo_toBits]

theorem endpoint_FP {n : List Bool → ℕ} {s : List Bool → Formula} {t : List Bool → Term}
    (hn : UnaryFn n) (hs : (fun q => (s q).encode) ∈ FP) (ht : (fun q => (t q).toData.toBits) ∈ FP) :
    (fun q => (endpoint (n q) (s q) (t q)).encode) ∈ FP := by
  have H0 := Term.variableBits_mem_FP hn
  have H1 := Term.variableBits_mem_FP (hn.add (UnaryFn.const 1))
  have H := Codec.taggedTwo_mem_FP 4 hs (Codec.taggedTwo_mem_FP 4
    (Codec.taggedOne_mem_FP 1 (term_bits_FP hn ht))
    (Codec.taggedTwo_mem_FP 4 (Codec.taggedOne_mem_FP 1 H1)
      (Codec.taggedOne_mem_FP 2 (Codec.taggedTwo_mem_FP 3 (constFn_mem_FP (Term.const (-1)).toData.toBits) H0))))
  apply mem_FP_of_eq H
  intro q
  simp only [endpoint,Formula.encode,Formula.toData,Term.variableBits_eq,
    Codec.taggedOne_toBits,Codec.taggedTwo_toBits,Term.toData]

theorem whole_record_FP {n : List Bool → ℕ} {p : List Bool → Formula} {t : List Bool → Term}
    (hn : UnaryFn n) (hp : (fun q => (p q).encode) ∈ FP) (ht : (fun q => (t q).toData.toBits) ∈ FP) :
    (fun q => (Input.whole (lifted (n q) (p q) (t q))).encode) ∈ FP := by
  have H := Codec.taggedTwo_mem_FP 1 (Codec.unary_toBits_mem_FP (hn.add (UnaryFn.const 2)))
    (lifted_formula_FP hn hp ht)
  apply mem_FP_of_eq H
  intro q
  exact Codec.taggedTwo_toBits 1 _ _

theorem point_record_FP {n : List Bool → ℕ} {p s d : List Bool → Formula} {t : List Bool → Term}
    (hn : UnaryFn n) (hp : (fun q => (p q).encode) ∈ FP) (hs : (fun q => (s q).encode) ∈ FP)
    (hd : (fun q => (d q).encode) ∈ FP) (ht : (fun q => (t q).toData.toBits) ∈ FP) :
    (fun q => (Input.point (PointQuery.mk (lifted (n q) (p q) (t q))
      (endpoint (n q) (s q) (t q)) (endpoint (n q) (d q) (t q)))).encode) ∈ FP := by
  have H := mem_FP_comp (appendFn_mem_FP (appendFn_mem_FP (appendFn_mem_FP
    (appendFn_mem_FP (constFn_mem_FP (Codec.unary 0).toBits)
      (Codec.unary_toBits_mem_FP (hn.add (UnaryFn.const 2))))
      (lifted_formula_FP hn hp ht)) (endpoint_FP hn hs ht)) (endpoint_FP hn hd ht)) Brackets.wrap_mem_FP
  apply mem_FP_of_eq H
  intro q
  simp only [Function.comp_apply,Input.encode,Input.toData,Data.toBits_l,Brackets.wrap,
    List.map_cons,List.map_nil,List.flatten_cons,List.flatten_nil,List.append_nil,List.append_assoc,
    lifted,Formula.encode]

theorem whole_language_iff (n : ℕ) (p : Formula) (t : Term) (hp : p.arity ≤ n) (ht : t.arity ≤ n) :
    (Input.whole (lifted n p t)).encode ∈ connectedLanguage ↔
      (Input.whole (original n p t)).encode ∈ connectedLanguage := by
  simpa only [whole_encode_mem_iff] using connected_iff n p t hp ht

theorem point_language_iff (n : ℕ) (p s d : Formula) (t : Term) (hp : p.arity ≤ n) (ht : t.arity ≤ n)
    (x y : (original n p t).realization) (hs : Denotes n s x.val) (hd : Denotes n d y.val) :
    (Input.point (PointQuery.mk (lifted n p t) (endpoint n s t) (endpoint n d t))).encode ∈ pointLanguage ↔
      (Input.point (PointQuery.mk (original n p t) s d)).encode ∈ pointLanguage := by
  simpa only [point_encode_mem_iff] using reachable_iff n p s d t hp ht x y hs hd

end LeanCanny.Connectivity.FormulaStrictWitness
