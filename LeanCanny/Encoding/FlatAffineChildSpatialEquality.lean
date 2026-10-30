/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineCompleteChildGeometry
public import LeanCanny.Encoding.SquareSampleCompleteCoordinateEquality

/-! # Native equality of the newest spatial blocks of complete children -/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineChildSpatialEquality
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation
open FlatAffineFullSourceTower (Inputs arity stageWidth)
open FlatAffineCompleteRootStages (next newest)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

def selected (F : Inputs) (u d : List Bool) : Fin (arity F u) :=
  ⟨min (Nat.fromBitsLE d) (arity F u - 1), by
    have : 0 < arity F u := by unfold arity; omega
    omega⟩
lemma selected_encode (F : Inputs) (u : List Bool) (i : Fin (arity F u)) : selected F u (BinaryNatCode.encode i.val) = i := by
  apply Fin.ext
  simp only [selected, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  exact Nat.min_eq_left (by have := i.isLt; omega)

noncomputable def slot (F : Inputs) (u : List Bool) (i : Fin (arity F u)) : Fin (FlatAffineFullSourcePositive.count (next F) u) :=
  (FlatAffinePowerTower.current ⟨F.depth u, Nat.lt_succ_self _⟩ i).castSucc
noncomputable def slotWord (F : Inputs) (u d : List Bool) : List Bool := BinaryNatCode.encode (slot F u (selected F u d)).val
theorem slotWord_FP {F : Inputs} (h : F.Access) : (fun q => slotWord F (pairFst q) (pairSnd q)) ∈ FP := by
  have HI := UnaryFn.fromBitsLE_min pairSnd_mem_FP (((FlatAffineFullSourceTower.arity_unary h).comp pairFst_mem_FP).sub (UnaryFn.const 1))
  have H : UnaryFn (fun q => (slot F (pairFst q) (selected F (pairFst q) (pairSnd q))).val) :=
    (((FlatAffineFullSourceTower.stageWidth_unary h).mul h.depth).comp pairFst_mem_FP |>.add HI).of_eq (fun q => by
      change stageWidth F (pairFst q) * F.depth (pairFst q) + min (Nat.fromBitsLE (pairSnd q)) (arity F (pairFst q) - 1) =
        min (Nat.fromBitsLE (pairSnd q)) (arity F (pairFst q) - 1) + stageWidth F (pairFst q) * F.depth (pairFst q)
      omega)
  exact (BinaryFn.ofUnary H).bits_mem_FP

def context (r : List Bool) : List Bool := pair (pairFst (pairFst r)) (pairSnd r)
theorem context_FP : context ∈ FP := by polytime [context]
noncomputable def query (F : Inputs) (r : List Bool) : List Bool :=
  pair (pairFst r) (slotWord F (pairFst (pairFst r)) (pairSnd r))
theorem query_FP {F : Inputs} (h : F.Access) : query F ∈ FP := by
  have H := mem_FP_comp context_FP (slotWord_FP h)
  exact mem_FP_pair pairFst_mem_FP (mem_FP_of_eq H (fun r => by simp only [context, Function.comp_apply, pairFst_pair, pairSnd_pair]))
theorem query_packet (F : Inputs) (u w v : List Bool) (i : Fin (arity F u)) :
    query F (pair (pair u (pair w v)) (BinaryNatCode.encode i.val)) =
      pair (pair u (pair w v)) (BinaryNatCode.encode (slot F u i).val) := by
  simp only [query, pairFst_pair, pairSnd_pair]
  rw [slotWord, selected_encode]

theorem point_coordinate (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate (next F)) (u w : List Bool)
    (hw : FlatAffineCompleteVertices.Valid (next F) cone u w) (i : Fin (arity F u)) :
    newest F u (FlatAffineCompleteVertices.vertexEquiv (next F) cone u ⟨w, hw⟩).val (Sum.inl i) =
      (SquareSampleCompleteVertices.candidate (FlatAffinePowerSampleInput.input (next F) cone) u w hw).val (slot F u i) := by
  have HI : TriangularPolynomialRows.block (stageWidth F u) (F.depth u) (F.depth u + 1) (Nat.lt_succ_self _)
      (FlatAffineCriticalTower.blockEquiv (arity F u) (Sum.inl i)) =
      FlatAffinePowerTower.current ⟨F.depth u, Nat.lt_succ_self _⟩ i :=
    (FlatAffinePowerTower.row_index_eq ⟨F.depth u, Nat.lt_succ_self _⟩ (Sum.inl i)).symm
  exact (congrArg (FlatAffineCompleteVertices.vertexEquiv (next F) cone u ⟨w, hw⟩).val HI).trans
    (FlatAffineCompleteVertices.ambient_coordinate (next F) cone u w hw ⟨F.depth u, Nat.lt_succ_self _⟩ i)

noncomputable def language (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate (next F)) : Language :=
  {q | ∀ i < arity F (pairFst q), query F (pair q (BinaryNatCode.encode i)) ∈
    SquareSampleCompleteCoordinateEquality.language (FlatAffinePowerSampleInput.input (next F) cone)}

theorem evaluator {F : Inputs} (h : F.Access) (cone : FlatAffinePowerPositive.ConeCertificate (next F)) :
    SpaceFunction (fun q => [decide (q ∈ language F cone)]) := by
  have D := SquareSampleCompleteCoordinateEquality.decider (FlatAffinePowerSampleInput.access (FlatAffineCompleteChildLabels.nextAccess h) cone)
  have E := (D.precompose (query F) (query_FP h)).flagEvaluator
  have N := BinaryFn.ofUnary ((FlatAffineFullSourceTower.arity_unary h).comp pairFst_mem_FP)
  exact (E.forall_binary N).congr (funext fun q => by
    apply congrArg List.singleton
    apply Bool.eq_iff_iff.mpr
    simp only [language, Set.mem_ofPred_eq, Set.mem_preimage, List.cons.injEq, and_true, decide_eq_true_eq])

theorem decider {F : Inputs} (h : F.Access) (cone : FlatAffinePowerPositive.ConeCertificate (next F)) : SpaceDecider (language F cone) := by
  apply (evaluator h cone).decider (fun z => decide (z = [true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro q
  simp only [List.cons.injEq, and_true, decide_eq_true_eq]

theorem packet (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate (next F)) (u w v : List Bool)
    (hw : FlatAffineCompleteVertices.Valid (next F) cone u w) (hv : FlatAffineCompleteVertices.Valid (next F) cone u v) :
    pair u (pair w v) ∈ language F cone ↔
      newest F u (FlatAffineCompleteVertices.vertexEquiv (next F) cone u ⟨w, hw⟩).val ∘ Sum.inl =
      newest F u (FlatAffineCompleteVertices.vertexEquiv (next F) cone u ⟨v, hv⟩).val ∘ Sum.inl := by
  have H (i : Fin (arity F u)) := SquareSampleCompleteCoordinateEquality.packet
    (FlatAffinePowerSampleInput.input (next F) cone) (FlatAffinePowerSampleInput.complete (next F) cone) u w v hw hv (slot F u i)
  constructor
  · intro ha
    funext i
    have HE := (H i).mp (by
      rw [← query_packet F u w v i]
      exact ha i.val (by simpa only [pairFst_pair] using i.isLt))
    exact (point_coordinate F cone u w hw i).trans (HE.trans (point_coordinate F cone u v hv i).symm)
  · intro HE i hi
    have HI : i < arity F u := by simpa only [pairFst_pair] using hi
    rw [query_packet F u w v ⟨i, HI⟩]
    apply (H ⟨i, HI⟩).mpr
    exact (point_coordinate F cone u w hw ⟨i, HI⟩).symm.trans
      ((congrFun HE ⟨i, HI⟩).trans (point_coordinate F cone u v hv ⟨i, HI⟩))

end LeanCanny.Encoding.FlatAffineChildSpatialEquality
