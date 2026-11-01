/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineExceptionalEndpointFrame
public import LeanCanny.Encoding.FlatAffineHeightCells

/-! # Independent exceptional-scalar and original-parent frames

The record contains an original source and independent complete labels for
its frozen parent and exceptional scalar. No point, interior sample, joint
marker, or nonempty fiber is required. The native assembler checks that
the two input packets have the same original source.

The represented slice uses one extra frozen parameter. It does not append
an ordinary critical block, or supply a critical sampler over this extended
parameter history.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineExceptionalSliceFrame
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.Geometry
open FlatAffineFullSourceTower (Inputs arity)
open FlatAffineCompleteRootStages (next)
open FlatAffineLastHeightRow (row parentCone)
open scoped Classical
attribute [local irreducible] SquareSampleCompleteVertices.candidate

def source (q : List Bool) : List Bool := pairFst (pairFst q)
def parentWord (q : List Bool) : List Bool := pairSnd (pairFst q)
def scalarWord (q : List Bool) : List Bool := pairSnd q
def record (u v a : List Bool) : List Bool := pair (pair u v) a

theorem source_FP : source ∈ FP := by polytime [source]
theorem source_record (u v a : List Bool) : source (record u v a) = u := by
  simp only [source, record, pairFst_pair]
theorem parentWord_record (u v a : List Bool) : parentWord (record u v a) = v := by
  simp only [parentWord, record, pairFst_pair, pairSnd_pair]
theorem scalarWord_record (u v a : List Bool) : scalarWord (record u v a) = a := by
  simp only [scalarWord, record, pairSnd_pair]

noncomputable def scalarSource (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) := FlatAffineHeightCells.source (next F) C (row F h)

theorem scalarAccess {F : Inputs} (hF : F.Access)
    (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (hh : UnaryFn (fun u => (h u).val)) :
    IntegerPolynomialRootQueriesBits.Access (scalarSource F C h) :=
  FlatAffineHeightCells.access (FlatAffineCompleteRootStages.access hF (hF.depth.add (UnaryFn.const 1)))
    C (row F h) (FlatAffineLastHeightRow.row_unary hF h hh)

noncomputable def language (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) : Language :=
  {q | FlatAffineCompleteVertices.Valid F (parentCone F C) (source q) (parentWord q) ∧
    SquareSampleCompleteVertices.Valid (IntegerPolynomialSampleInput.input (scalarSource F C h)) (source q) (scalarWord q)}

def scalarPacket (q : List Bool) : List Bool := pair (source q) (scalarWord q)
theorem scalarPacket_FP : scalarPacket ∈ FP := by polytime [scalarPacket, source, scalarWord]

theorem decider {F : Inputs} (hF : F.Access)
    (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (hh : UnaryFn (fun u => (h u).val)) :
    SpaceDecider (language F C h) := by
  have P := ((SquareSampleCompleteVertices.decider (FlatAffinePowerSampleInput.access hF (parentCone F C))).precompose
    pairFst pairFst_mem_FP).flagEvaluator
  have S := ((SquareSampleCompleteVertices.decider (IntegerPolynomialSampleInput.access (scalarAccess hF C h hh))).precompose
    scalarPacket scalarPacket_FP).flagEvaluator
  apply (P.andFlags S).decider (fun z => decide (z = [true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro q
  simp only [language, SquareSampleCompleteVertices.language, Set.mem_ofPred_eq,
    Set.mem_preimage, scalarPacket, pairFst_pair, pairSnd_pair, List.cons.injEq, and_true, decide_eq_true_eq]
  rfl

theorem record_valid (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (u v a : List Bool) :
    record u v a ∈ language F C h ↔
      FlatAffineCompleteVertices.Valid F (parentCone F C) u v ∧
        SquareSampleCompleteVertices.Valid (IntegerPolynomialSampleInput.input (scalarSource F C h)) u a := by
  simp only [language, Set.mem_ofPred_eq, source_record, parentWord_record, scalarWord_record]

/-- Native assembly from independently supplied `(source,parent)` and
`(source,scalar)` packets. -/
def build (q : List Bool) : List Bool :=
  record (pairFst (pairFst q)) (pairSnd (pairFst q)) (pairSnd (pairSnd q))
theorem build_FP : build ∈ FP := by polytime [build, record]
theorem evaluator : SpaceFunction build := SpaceFunction.ofFP build build_FP

theorem build_fields (q : List Bool) :
    source (build q) = pairFst (pairFst q) ∧
      parentWord (build q) = pairSnd (pairFst q) ∧
        scalarWord (build q) = pairSnd (pairSnd q) := by
  simp only [build, source_record, parentWord_record, scalarWord_record, and_self]

noncomputable def ready (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) : Language :=
  {q | pairFst (pairFst q) = pairFst (pairSnd q) ∧ build q ∈ language F C h}

theorem ready_decider {F : Inputs} (hF : F.Access)
    (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (hh : UnaryFn (fun u => (h u).val)) :
    SpaceDecider (ready F C h) := by
  have E := SpaceFunction.ofFP _ (Brackets.stringEq_fppred
    (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP)).flag_mem_FP
  have V := ((decider hF C h hh).precompose build build_FP).flagEvaluator
  apply (E.andFlags V).decider (fun z => decide (z = [true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro q
  simp only [ready, Set.mem_ofPred_eq, Set.mem_preimage, List.cons.injEq, and_true, decide_eq_true_eq, Function.comp_apply]

theorem build_valid (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (q : List Bool) (hq : q ∈ ready F C h) :
    build q ∈ language F C h := hq.2

theorem ready_packets (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (u v a : List Bool) :
    pair (pair u v) (pair u a) ∈ ready F C h ↔
      FlatAffineCompleteVertices.Valid F (parentCone F C) u v ∧
        SquareSampleCompleteVertices.Valid (IntegerPolynomialSampleInput.input (scalarSource F C h)) u a := by
  simp only [ready, Set.mem_ofPred_eq, build, pairFst_pair, pairSnd_pair, true_and, record_valid]

noncomputable def parent (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (u v : List Bool) (hv : FlatAffineCompleteVertices.Valid F (parentCone F C) u v) :
    FlatAffinePowerSampleInput.OriginalRoots F u := FlatAffineCompleteVertices.vertexEquiv F (parentCone F C) u ⟨v, hv⟩

noncomputable def scalar (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (u a : List Bool) : ℝ :=
  IntegerPolynomialSampleSlice.point (scalarSource F C h) (pair (pair u a) [])

theorem scalar_packet (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (u a : List Bool)
    (ha : SquareSampleCompleteVertices.Valid (IntegerPolynomialSampleInput.input (scalarSource F C h)) u a) :
    scalar F C h u a = (SquareSampleCompleteVertices.candidate (IntegerPolynomialSampleInput.input (scalarSource F C h)) u a ha).val (0 : Fin 1) :=
  IntegerPolynomialSampleSlice.point_packet _ _ _ [] ha

noncomputable def slice (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (u v a : List Bool)
    (hv : FlatAffineCompleteVertices.Valid F (parentCone F C) u v) : Set (Fin (arity F u) → ℝ) :=
  FlatAffineExceptionalEndpointFrame.presentation F h u (parent F C u v hv) (scalar F C h u a)

theorem slice_eq (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (u v a : List Bool)
    (hv : FlatAffineCompleteVertices.Valid F (parentCone F C) u v) :
    slice F C h u v a hv = FlatAffineShiftedSlice.slice F u (parent F C u v hv) (h u) (scalar F C h u a) :=
  FlatAffineExceptionalEndpointFrame.presentation_eq_slice F h u _ _

/-- Complete labels exist for every parent and exceptional scalar,
irrespective of whether their common slice contains a point. -/
theorem exists_record (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (u : List Bool)
    (x : FlatAffinePowerSampleInput.OriginalRoots F u) (t : ℝ)
    (ht : SymbolicScaledSquarefree.scalarEvaluation t
      (FlatAffineHeightSlabExceptional.polynomial (next F) (row F h) u) = 0) :
    ∃ v a, ∃ hv : FlatAffineCompleteVertices.Valid F (parentCone F C) u v,
      record u v a ∈ language F C h ∧ parent F C u v hv = x ∧ scalar F C h u a = t ∧
        slice F C h u v a hv = FlatAffineShiftedSlice.slice F u x (h u) t := by
  obtain ⟨⟨v, hv⟩, hx⟩ := (FlatAffineCompleteVertices.vertexEquiv F (parentCone F C) u).surjective x
  obtain ⟨a, ha, he⟩ := IntegerPolynomialSampleInput.root_complete (scalarSource F C h) u
    (FlatAffineHeightSlabExceptional.ne_zero (next F) C (row F h) u) t ht
  have hs : scalar F C h u a = t := (scalar_packet F C h u a ha).trans he
  refine ⟨v, a, hv, (record_valid F C h u v a).mpr ⟨hv, ha⟩, hx, hs, ?_⟩
  exact (slice_eq F C h u v a hv).trans (congrArg₂ (fun p s => FlatAffineShiftedSlice.slice F u p (h u) s) hx hs)

def rank (F : Inputs) (h : (u : List Bool) → Fin (arity F u)) (q : List Bool) : ℕ :=
  F.source.dim (source q) + 3 - ((h (source q)).val + 1)

theorem rank_unary {F : Inputs} (hF : F.Access) (h : (u : List Bool) → Fin (arity F u))
    (hh : UnaryFn (fun u => (h u).val)) : UnaryFn (rank F h) :=
  ((hF.source.dim.add (UnaryFn.const 3)).sub (hh.add (UnaryFn.const 1))).comp source_FP

theorem build_rank (F : Inputs) (h : (u : List Bool) → Fin (arity F u)) (q : List Bool)
    (hn : (h (pairFst (pairFst q))).val < F.source.dim (pairFst (pairFst q)) + 3) :
    source (build q) = pairFst (pairFst q) ∧
      rank F h (build q) < F.source.dim (pairFst (pairFst q)) + 3 - (h (pairFst (pairFst q))).val := by
  have hs : source (build q) = pairFst (pairFst q) := source_record _ _ _
  refine ⟨hs, ?_⟩
  have hv : (h (source (build q))).val = (h (pairFst (pairFst q))).val := congrArg (fun u => (h u).val) hs
  unfold rank
  rw [congrArg F.source.dim hs, hv]
  omega

noncomputable def envelope (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (u : List Bool) : List Bool :=
  record u (List.replicate (FlatAffineCompleteVertices.width F (parentCone F C) u) false)
    (List.replicate (SquareSampleCompleteVertices.width (IntegerPolynomialSampleInput.input (scalarSource F C h)) u) false)

theorem envelope_FP {F : Inputs} (hF : F.Access)
    (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (hh : UnaryFn (fun u => (h u).val)) : envelope F C h ∈ FP :=
  mem_FP_pair (mem_FP_pair id_mem_FP
    ((SquareSampleCompleteVertices.width_unary (FlatAffinePowerSampleInput.access hF (parentCone F C))).replicate_mem_FP false))
    ((IntegerPolynomialSampleInput.width_unary (scalarAccess hF C h hh)).replicate_mem_FP false)

theorem record_length (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (u v a : List Bool)
    (hv : FlatAffineCompleteVertices.Valid F (parentCone F C) u v)
    (ha : SquareSampleCompleteVertices.Valid (IntegerPolynomialSampleInput.input (scalarSource F C h)) u a) :
    (record u v a).length = (envelope F C h u).length := by
  have HP := FlatAffineCompleteVertices.word_length F (parentCone F C) u v hv
  have HS := (Classical.choose ha).1
  simp only [record, envelope, pair_length, List.length_replicate, HP, HS]
  rfl

theorem build_polynomial {F : Inputs} (hF : F.Access)
    (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (hh : UnaryFn (fun u => (h u).val)) :
    ∃ p : Polynomial ℕ, ∀ q, q ∈ ready F C h → (build q).length ≤ p.eval (pairFst (pairFst q)).length := by
  obtain ⟨p, hp⟩ := output_length_poly_of_mem_FP (envelope_FP hF C h hh)
  refine ⟨p, ?_⟩
  intro q hq
  have H := (record_valid F C h _ _ _).mp hq.2
  exact (record_length F C h _ _ _ H.1 H.2).le.trans (hp _)

end LeanCanny.Encoding.FlatAffineExceptionalSliceFrame
