/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Connectivity.BoundedEndpointQuery
public import LeanCanny.Computation.ImplicitGraphPSPACE

/-! # Native search for a piece meeting an original endpoint fiber

The search enumerates fixed-width piece labels and uses actual marked-source
queries. Its space bound needs only the source and formula writers. Coverage
and endpoint validity prove that the selected label has a marked point over
the endpoint; they are not assumptions on a decision routine.
-/

@[expose] public section
namespace LeanCanny.Connectivity.BoundedEndpointLocator
open ETR Geometry Computation Encoding Encoding.BoundedFullWriter
open Encoding.BoundedOriginalQuery BoundedEndpointQuery Turing.MultiTapeTM
open scoped Classical

noncomputable def test (P : Readers) (endpoint piece : List Bool → Formula) (c u : List Bool) : Bool :=
  decide (∃ x : ℕ → ℝ, MarkedPoint P c (fun i => x i.val) ∧
    (Formula.and (endpoint c) (piece (LeanCanny.pair c u))).Holds x)

noncomputable def locate (P : Readers) (endpoint piece : List Bool → Formula) (width : List Bool → ℕ) :
    List Bool → List Bool :=
  ImplicitGraph.findWord (fun p => test P endpoint piece p.1 p.2) width

theorem test_correct (P : Readers) (endpoint piece : List Bool → Formula) (c u : List Bool)
    (a : Fin (P.dim c) → ℝ) (hp : Denotes (P.dim c) (endpoint c) a) :
    test P endpoint piece c u = true ↔
      ∃ z : BoundedRegularSource.Marked (original P c) (size P c) (size P c) (P.radius c),
        (BoundedRegularSource.markedProjection (original P c) (size P c) (size P c) (P.radius c) z).val = a ∧
          witnessPiece (piece (LeanCanny.pair c u)) z.val.val := by
  rw [test, decide_eq_true_eq]
  exact marked_endpoint_correct P c _ _ a hp

attribute [local irreducible] test Encoding.BoundedOriginalQuery.MarkedPoint

theorem test_computable {P : Readers} {endpoint piece : List Bool → Formula} (h : P.PolyTime)
    (ht : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c)
    (hp : (fun c => (endpoint c).encode) ∈ FP) (hq : (fun c => (piece c).encode) ∈ FP) :
    ComputableInPolySpace (fun p : List Bool × List Bool => test P endpoint piece p.1 p.2)
      (encPair encBits encBits) encBool := by
  have he := Encoding.BoundedOriginalQuery.marked_evaluator (P := P.comp LeanCanny.pairFst)
    (p := fun c => Formula.and (endpoint (LeanCanny.pairFst c)) (piece c)) (h.comp pairFst_mem_FP)
    (fun c => ht (LeanCanny.pairFst c)) (and_encode_mem_FP (mem_FP_comp pairFst_mem_FP hp) hq)
  have hpair := pair_computable (ComputableTidilyInPolyTime.fst encBits encBits)
    (ComputableTidilyInPolyTime.snd encBits encBits)
  obtain ⟨S, hS, hraw⟩ := (he.computable.comp (.of_tidyPolyTime hpair)).exists_inSpace
  refine ComputableInPolySpace.of_inSpace hS (hraw.of_enc_eq ?_)
  intro p
  simp only [encBits_apply, encBool_apply, LeanCanny.pairFst_pair, test]
  change [decide (∃ x, MarkedAssignment P p.1 x ∧
      (Formula.and (endpoint p.1) (piece (LeanCanny.pair p.1 p.2))).Holds x)] =
    [decide (∃ x, MarkedAssignment (P.comp LeanCanny.pairFst) (LeanCanny.pair p.1 p.2) x ∧
      (Formula.and (endpoint p.1) (piece (LeanCanny.pair p.1 p.2))).Holds x)]
  simp only [markedAssignment_comp, LeanCanny.pairFst_pair]

@[simp] theorem locate_length (P : Readers) (endpoint piece : List Bool → Formula) (width : List Bool → ℕ) (c : List Bool) :
    (locate P endpoint piece width c).length = width c := ImplicitGraph.findWord_length _ _ _

theorem locate_evaluator {P : Readers} {endpoint piece : List Bool → Formula} {width : List Bool → ℕ} (h : P.PolyTime)
    (ht : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c)
    (hp : (fun c => (endpoint c).encode) ∈ FP) (hq : (fun c => (piece c).encode) ∈ FP) (hw : UnaryFn width) :
    SpaceFunction (locate P endpoint piece width) :=
  ⟨ImplicitGraph.findWord_computable (test_computable h ht hp hq) hw⟩

theorem locate_correct (P : Readers) (endpoint piece : List Bool → Formula) (width : List Bool → ℕ) (c : List Bool)
    (a : Fin (P.dim c) → ℝ) (hp : Denotes (P.dim c) (endpoint c) a)
    (ha : a ∈ BoundedZeroSource.Bounded (original P c) (P.radius c))
    (hcover : ∀ z : BoundedRegularSource.Marked (original P c) (size P c) (size P c) (P.radius c),
      ∃ u, u.length = width c ∧ witnessPiece (piece (LeanCanny.pair c u)) z.val.val) :
    ∃ z : BoundedRegularSource.Marked (original P c) (size P c) (size P c) (P.radius c),
      (BoundedRegularSource.markedProjection (original P c) (size P c) (size P c) (P.radius c) z).val = a ∧
        witnessPiece (piece (LeanCanny.pair c (locate P endpoint piece width c))) z.val.val := by
  apply (test_correct P endpoint piece c _ a hp).mp
  apply ImplicitGraph.findWord_correct
    (test := fun p : List Bool × List Bool => test P endpoint piece p.1 p.2) (width := width) (c := c)
  let z := BoundedRegularSource.markedLift (original P c) (size P c) (size P c) (P.radius c) ⟨a, ha⟩
  obtain ⟨u, hu, hz⟩ := hcover z
  refine ⟨u, hu, (test_correct P endpoint piece c u a hp).mpr ⟨z, ?_, hz⟩⟩
  exact congrArg Subtype.val (BoundedRegularSource.markedProjection_lift _ _ _ _ ⟨a, ha⟩)

end LeanCanny.Connectivity.BoundedEndpointLocator
