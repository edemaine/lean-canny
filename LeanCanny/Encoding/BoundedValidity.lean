/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedAffineQuery

/-! # Native validation of the bounded source's actual sweep record

All affine charts use the shared source constructed from the original term.
Infinity charts use its pure-power leading form. The resulting checker
agrees with the existing finite `Valid` predicate for this same source.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedValidity
open LeanCanny.ETR LeanCanny.Computation LeanCanny.Geometry LeanCanny.Algebra MvPolynomial
open BoundedSourceWriter FermatSweepCertificate
open scoped Classical

private theorem flagTrue {p : Prop} {d : Decidable p} : [@decide p d] = [true] ↔ p := by
  simp only [List.cons.injEq, and_true]
  exact Iff.of_eq (@decide_eq_true_eq p d)

noncomputable def affine (P : Readers) : List Bool → List Bool :=
  BoundedAffineQuery.empty (P.precomp pairFst) (fun p => (pairSnd p).length)
noncomputable def infinity (P : Readers) : List Bool → List Bool :=
  FermatInfinityQuery.empty (fun p => P.dim (pairFst p) + 2) (degree P ∘ pairFst)
    (fun p => (pairSnd p).length) (P.record ∘ pairFst)
noncomputable def charts (P : Readers) (p : List Bool) : List Bool :=
  [decide (affine P p = [true] ∧ infinity P p = [true])]
noncomputable def check (P : Readers) (c : List Bool) : List Bool :=
  [decide (∀ k < P.dim c + 3, charts P (pair c (List.replicate k true)) = [true])]

theorem charts_evaluator {P : Readers} (h : P.PolyTime) : SpaceFunction (charts P) := by
  have ha := BoundedAffineQuery.empty_evaluator (h.precomp pairFst_mem_FP) (UnaryFn.length pairSnd_mem_FP)
  have hi := FermatInfinityQuery.empty_evaluator
    ((UnaryFn.comp h.dim pairFst_mem_FP).add (UnaryFn.const 2))
    ((degree_binary h).comp (FP.computable pairFst_mem_FP)) (UnaryFn.length pairSnd_mem_FP)
    (mem_FP_comp pairFst_mem_FP h.record)
  exact ha.andFlags hi

theorem evaluator {P : Readers} (h : P.PolyTime) : SpaceFunction (check P) :=
  (charts_evaluator h).forall_unary (h.dim.add (UnaryFn.const 3))

theorem leading_ne_zero (P : Readers) (c : List Bool) : (leading P c : ℚ) ≠ 0 := by
  exact_mod_cast (IntegerRegularSource.leading_ne_zero 1 (degree P c)
    (BoundedRegularSource.sourceMassExponent (P.dim c) (size P c) (size P c) (P.radius c)) (by decide))

theorem lower_degree (P : Readers) (c : List Bool) : ((lower P c).map (Int.castRingHom ℚ)).totalDegree < degree P c :=
  (PolynomialMapDegree.degree_le _ _).trans_lt
    (IntegerRegularSource.lower_degree _ _ _ (BoundedRegularSource.lower_degree _ _ _ _ (original_degree P c)))

theorem infinity_at (P : Readers) (c : List Bool) (k : ℕ) :
    infinity P (pair c (List.replicate k true)) =
      FermatInfinityQuery.empty (fun c => P.dim c + 2) (degree P) (fun _ => k) P.record c := by
  simp only [infinity, FermatInfinityQuery.empty]
  congr 1
  apply decide_eq_decide.mpr
  simp only [FermatInfinityQuery.query_eq_data, Function.comp_apply, pairFst_pair, pairSnd_pair, List.length_replicate]

theorem charts_correct (P : Readers) (c : List Bool) (ht : (TermView.term (P.source c)).arity ≤ P.dim c)
    (k : ℕ) (hk : k < P.dim c + 3) :
    charts P (pair c (List.replicate k true)) = [true] ↔
      ¬ AffineBad ((lower P c).map (Int.castRingHom ℚ)) (leading P c : ℚ) (degree P c) (P.record c) ⟨k, hk⟩ ∧
      ¬ InfinityBad (leading P c : ℚ) (degree P c) (P.record c) ⟨k, hk⟩ := by
  have hN : 0 < degree P c := (BoundedRegularSource.powerDegree_gt_one (size P c)).trans' (by decide)
  simp only [charts, flagTrue, affine, BoundedAffineQuery.empty_precomp,
    pairFst_pair, pairSnd_pair, List.length_replicate, infinity_at]
  rw [BoundedAffineQuery.empty_correct P (fun _ => k) c ht hk,
    FermatInfinityQuery.empty_correct (fun c => P.dim c + 2) (degree P) (fun _ => k) P.record c
      (leading P c : ℚ) (leading_ne_zero P c) hN hk]
  simp only [flagTrue]

theorem correct (P : Readers) (c : List Bool) (ht : (TermView.term (P.source c)).arity ≤ P.dim c) :
    check P c = [decide (Valid ((lower P c).map (Int.castRingHom ℚ)) (leading P c : ℚ) (degree P c) (P.record c))] := by
  have hv := valid_iff_no_bad_charts ((lower P c).map (Int.castRingHom ℚ)) (leading P c : ℚ)
    (degree P c) (lower_degree P c) (BoundedRegularSource.powerDegree_gt_one (size P c)) (P.record c)
  have hi : (∀ k < P.dim c + 3, charts P (pair c (List.replicate k true)) = [true]) ↔
      Valid ((lower P c).map (Int.castRingHom ℚ)) (leading P c : ℚ) (degree P c) (P.record c) := by
    rw [hv]
    constructor
    · intro h
      exact ⟨fun i => ((charts_correct P c ht i.val i.isLt).mp (h i.val i.isLt)).1,
        fun i => ((charts_correct P c ht i.val i.isLt).mp (h i.val i.isLt)).2⟩
    · rintro ⟨ha, hinf⟩ k hk
      exact (charts_correct P c ht k hk).mpr ⟨ha ⟨k, hk⟩, hinf ⟨k, hk⟩⟩
  unfold check
  congr 1
  exact decide_eq_decide.mpr hi

end LeanCanny.Encoding.BoundedValidity
