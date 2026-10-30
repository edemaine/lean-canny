/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineEndpointFiniteRankImage
public import LeanCanny.Encoding.FixedWidthNatVectorSpace

/-! # Native short descriptors of actual spatial fiber points

The base packet contains the frame and anchor label. Each indexed query
retains both and selects one original spatial coordinate. Its distinct-value
rank fits in one more bit than a complete joint label. A streamed writer
constructs the full coordinate-rank descriptor in polynomial space.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineEndpointRankWord
open LeanCanny.Algebra LeanCanny.Computation
open FlatAffineFullSourceTower (Inputs)
open FlatAffineFullSourcePositive (count)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
attribute [local irreducible] FiniteWordProjectionRank.rank FlatAffineEndpointFiniteRanks.data

def index (F : Inputs) (c : List Bool) : Fin (FlatAffineEndpointFiniteSide.originalCount F (FlatAffineEndpointFiniteRanks.frame c)) :=
  FlatAffineEndpointFiniteSide.coordinate F (FlatAffineEndpointFiniteRanks.frame c) (pairSnd (pairSnd c))

theorem index_unary {F : Inputs} (h : F.Access) : UnaryFn (fun c => (index F c).val) :=
  UnaryFn.fromBitsLE_min (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP)
    (((FlatAffineEndpointFiniteSide.originalCount_unary h).comp FlatAffineEndpointFiniteRanks.frame_FP).sub (UnaryFn.const 1))

def rankContext (r : List Bool) : List Bool :=
  pair (pairFst (pairFst r)) (pair (pairSnd (pairFst r)) (pairSnd r))
def rankQuery (r : List Bool) : List Bool := pair (rankContext r) (pairSnd (pairFst r))
theorem rankContext_FP : rankContext ∈ FP := by polytime [rankContext]
theorem rankQuery_FP : rankQuery ∈ FP := by polytime [rankQuery, rankContext]

noncomputable def ordinal (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (b : List Bool) (i : ℕ) : ℕ :=
  FiniteWordProjectionRank.rank (FlatAffineEndpointFiniteRanks.data F cone height (index F))
    (rankQuery (pair b (BinaryNatCode.encode i)))

noncomputable def read (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (r : List Bool) : List Bool :=
  BinaryNatCode.encode (FiniteWordProjectionRank.rank (FlatAffineEndpointFiniteRanks.data F cone height (index F)) (rankQuery r))

theorem readEvaluator {F : Inputs} (h : F.Access) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) : SpaceFunction (read F cone height) :=
  (FlatAffineEndpointFiniteRanks.evaluator h cone height hh (index F) (index_unary h)).precompose rankQuery rankQuery_FP

def arity (F : Inputs) (b : List Bool) : ℕ := FlatAffineEndpointFiniteSide.originalCount F (pairFst b)
theorem arity_unary {F : Inputs} (h : F.Access) : UnaryFn (arity F) :=
  (FlatAffineEndpointFiniteSide.originalCount_unary h).comp pairFst_mem_FP

noncomputable def width (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (b : List Bool) : ℕ :=
  SquareSampleCompleteVertices.width (FlatAffineEndpointFiniteSample.input F cone height) (pairFst b) + 1

theorem width_unary {F : Inputs} (h : F.Access) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) : UnaryFn (width F cone height) :=
  ((FlatAffineEndpointFiniteSample.width_unary h cone height hh).comp pairFst_mem_FP).add (UnaryFn.const 1)

theorem ordinal_bits (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (b : List Bool) (i : ℕ) :
    (ordinal F cone height b i).size ≤ width F cone height b := by
  have H := FiniteWordProjectionRank.rank_bits (FlatAffineEndpointFiniteRanks.data F cone height (index F))
    (rankQuery (pair b (BinaryNatCode.encode i)))
  simpa only [ordinal, width, rankQuery, rankContext, FlatAffineEndpointFiniteRanks.data,
    SquareSampleCompleteProjectionRank.data, FlatAffineEndpointFiniteRanks.frame, pairFst_pair, pairSnd_pair] using H

noncomputable def word (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (b : List Bool) : List Bool :=
  FixedWidthNatVector.encode (arity F b) (width F cone height b) (ordinal F cone height b)

theorem evaluator {F : Inputs} (h : F.Access) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) : SpaceFunction (word F cone height) :=
  FixedWidthNatVector.encodeEvaluator (arity F) (width F cone height) (ordinal F cone height)
    (arity_unary h) (width_unary h cone height hh) (read F cone height) (readEvaluator h cone height hh) (fun _ _ => rfl)

theorem word_length (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (b : List Bool) :
    (word F cone height b).length = arity F b * width F cone height b := FixedWidthNatVector.length_encode _ _ _

theorem length_unary {F : Inputs} (h : F.Access) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) :
    UnaryFn (fun b => arity F b * width F cone height b) := (arity_unary h).mul (width_unary h cone height hh)

theorem decode_word (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (b : List Bool) (i : ℕ) (hi : i < arity F b) :
    Nat.fromBitsLE (((word F cone height b).drop (i * width F cone height b)).take (width F cone height b)) =
      ordinal F cone height b i :=
  FixedWidthNatVector.decode_block _ _ _ i hi (Nat.size_le.mp (ordinal_bits F cone height b i))

end LeanCanny.Encoding.FlatAffineEndpointRankWord
