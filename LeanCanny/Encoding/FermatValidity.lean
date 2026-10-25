/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FermatAffineQuery
public import LeanCanny.Computation.SpaceFunctionQuantifiers

/-! # Native validation of the sampled sweep certificate

The checker scans the actual affine and infinity chart circuits. It agrees
with the existing Valid predicate for the constructed dyadic source; neither
the certificate predicate nor a semantic query oracle is supplied as input.
-/

@[expose] public section
namespace LeanCanny.Encoding.FermatValidity
open LeanCanny.ETR LeanCanny.ETR.ComplexCircuit LeanCanny.Computation
open FermatSweepCertificate MvPolynomial
open scoped Classical

private theorem flagTrue {p : Prop} {d : Decidable p} : [@decide p d] = [true] ↔ p := by
  simp only [List.cons.injEq, and_true]
  exact Iff.of_eq (@decide_eq_true_eq p d)

noncomputable def affine (source record : List Bool → List Bool) (dim degree exponent : List Bool → ℕ)
    (a : List Bool → ℤ) : List Bool → List Bool :=
  FermatAffineQuery.empty (source ∘ pairFst) (record ∘ pairFst) (dim ∘ pairFst) (degree ∘ pairFst)
    (exponent ∘ pairFst) (fun p => (pairSnd p).length) (a ∘ pairFst)

noncomputable def infinity (record : List Bool → List Bool) (dim degree : List Bool → ℕ) : List Bool → List Bool :=
  FermatInfinityQuery.empty (dim ∘ pairFst) (degree ∘ pairFst) (fun p => (pairSnd p).length) (record ∘ pairFst)

noncomputable def charts (source record : List Bool → List Bool) (dim degree exponent : List Bool → ℕ)
    (a : List Bool → ℤ) (p : List Bool) : List Bool :=
  [decide (affine source record dim degree exponent a p = [true] ∧ infinity record dim degree p = [true])]

noncomputable def check (source record : List Bool → List Bool) (dim degree exponent : List Bool → ℕ)
    (a : List Bool → ℤ) (c : List Bool) : List Bool :=
  [decide (∀ k < dim c + 1, charts source record dim degree exponent a (pair c (List.replicate k true)) = [true])]

theorem charts_evaluator {source record : List Bool → List Bool} {dim degree exponent : List Bool → ℕ}
    {a : List Bool → ℤ} (ht : source ∈ FP) (hr : record ∈ FP) (hd : UnaryFn dim)
    (hN : BinaryFn degree) (hE : BinaryFn exponent) (ha : (fun c => (Term.const (a c)).toData.toBits) ∈ FP) :
    SpaceFunction (charts source record dim degree exponent a) := by
  have ht' := mem_FP_comp pairFst_mem_FP ht
  have hr' := mem_FP_comp pairFst_mem_FP hr
  have hd' := UnaryFn.comp hd pairFst_mem_FP
  have hN' := hN.comp (FP.computable pairFst_mem_FP)
  have hE' := hE.comp (FP.computable pairFst_mem_FP)
  have ha' := mem_FP_comp pairFst_mem_FP ha
  exact (FermatAffineQuery.empty_evaluator ht' hr' hd' hN' hE' (UnaryFn.length pairSnd_mem_FP) ha').andFlags
    (FermatInfinityQuery.empty_evaluator hd' hN' (UnaryFn.length pairSnd_mem_FP) hr')

theorem evaluator {source record : List Bool → List Bool} {dim degree exponent : List Bool → ℕ}
    {a : List Bool → ℤ} (ht : source ∈ FP) (hr : record ∈ FP) (hd : UnaryFn dim)
    (hN : BinaryFn degree) (hE : BinaryFn exponent) (ha : (fun c => (Term.const (a c)).toData.toBits) ∈ FP) :
    SpaceFunction (check source record dim degree exponent a) :=
  (charts_evaluator ht hr hd hN hE ha).forall_unary (hd.add (UnaryFn.const 1))

theorem charts_correct (source record : List Bool → List Bool) (dim degree exponent : List Bool → ℕ)
    (a : List Bool → ℤ) (c : List Bool) (low : MvPolynomial (Fin (dim c + 2)) ℤ)
    (ht : (TermView.term (source c)).toPolynomial = rename Fin.val low) (ha : a c ≠ 0)
    (hN : 0 < degree c) (k : ℕ) (hk : k < dim c + 1) :
    charts source record dim degree exponent a (pair c (List.replicate k true)) = [true] ↔
      ¬ AffineBad (dyadicLow low (exponent c)) (dyadicLeading (a c) (exponent c)) (degree c) (record c) ⟨k, hk⟩ ∧
      ¬ InfinityBad (dyadicLeading (a c) (exponent c)) (degree c) (record c) ⟨k, hk⟩ := by
  have hp : charts source record dim degree exponent a (pair c (List.replicate k true)) = [true] ↔
      FermatAffineQuery.empty source record dim degree exponent (fun _ => k) a c = [true] ∧
      FermatInfinityQuery.empty dim degree (fun _ => k) record c = [true] := by
    simp only [charts, flagTrue]
    simp only [affine, infinity, FermatAffineQuery.empty, FermatInfinityQuery.empty]
    simp only [flagTrue]
    simp only [FermatAffineQuery.query_eq_data, FermatInfinityQuery.query_eq_data,
      Function.comp_apply, pairFst_pair, pairSnd_pair, List.length_replicate]
  rw [hp, FermatAffineQuery.empty_correct source record dim degree exponent (fun _ => k) a c low ht hN hk,
    FermatInfinityQuery.empty_correct dim degree (fun _ => k) record c
      (dyadicLeading (a c) (exponent c)) (dyadicLeading_ne_zero (a c) ha (exponent c)) hN hk]
  simp only [flagTrue]

theorem check_packet (source : List Bool → List Bool) (dim degree exponent : List Bool → ℕ)
    (a : List Bool → ℤ) (c r : List Bool) :
    check (source ∘ pairFst) pairSnd (dim ∘ pairFst) (degree ∘ pairFst)
      (exponent ∘ pairFst) (a ∘ pairFst) (pair c r) =
      check source (fun _ => r) dim degree exponent a c := by
  unfold check
  congr 1
  apply decide_eq_decide.mpr
  simp only [charts, flagTrue]
  simp only [affine, infinity, FermatAffineQuery.empty, FermatInfinityQuery.empty]
  simp only [flagTrue]
  simp only [FermatAffineQuery.query_eq_data, FermatInfinityQuery.query_eq_data,
    Function.comp_apply, pairFst_pair, pairSnd_pair, List.length_replicate]

theorem correct (source record : List Bool → List Bool) (dim degree exponent : List Bool → ℕ)
    (a : List Bool → ℤ) (c : List Bool) (low : MvPolynomial (Fin (dim c + 2)) ℤ)
    (ht : (TermView.term (source c)).toPolynomial = rename Fin.val low) (ha : a c ≠ 0)
    (hlow : low.totalDegree < degree c) (hN : 1 < degree c) :
    check source record dim degree exponent a c =
      [decide (Valid (dyadicLow low (exponent c)) (dyadicLeading (a c) (exponent c)) (degree c) (record c))] := by
  have hv := valid_iff_no_bad_charts (dyadicLow low (exponent c)) (dyadicLeading (a c) (exponent c))
    (degree c) (dyadicLow_degree low (exponent c) (degree c) hlow) hN (record c)
  have hiff : (∀ k < dim c + 1, charts source record dim degree exponent a (pair c (List.replicate k true)) = [true]) ↔
      Valid (dyadicLow low (exponent c)) (dyadicLeading (a c) (exponent c)) (degree c) (record c) := by
    rw [hv]
    constructor
    · intro h
      refine ⟨fun i => ?_, fun i => ?_⟩
      · exact ((charts_correct source record dim degree exponent a c low ht ha (by omega) i.val i.isLt).mp (h i.val i.isLt)).1
      · exact ((charts_correct source record dim degree exponent a c low ht ha (by omega) i.val i.isLt).mp (h i.val i.isLt)).2
    · rintro ⟨hA, hI⟩ k hk
      exact (charts_correct source record dim degree exponent a c low ht ha (by omega) k hk).mpr ⟨hA ⟨k, hk⟩, hI ⟨k, hk⟩⟩
  unfold check
  congr 1
  exact decide_eq_decide.mpr hiff

end LeanCanny.Encoding.FermatValidity
