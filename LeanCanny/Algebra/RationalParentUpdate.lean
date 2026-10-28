/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.RationalCoordinateFamily
public import LeanCanny.Encoding.BoundedCriticalSampleBlockSource

/-! # Retaining ambient coordinates through a child parameter

Child coordinate zero retains the parent's parameter. Successor coordinates
replace a contiguous free block. Every other ambient coordinate is composed
through that retained parameter. The native readers and binary bounds include
both families and the rational composition, including empty blocks.
-/

@[expose] public section
namespace LeanCanny.Algebra.RationalParentUpdate
open LeanCanny.Encoding LeanCanny.Computation UnivariateRational RationalCoordinateFamily
open BoundedCriticalSampleBlockSource (InBlock)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def oldQuery (q : List Bool) : List Bool := pair (pairFst (pairFst q)) (pairSnd q)
def retainedQuery (q : List Bool) : List Bool := pair (pairFst q) []
def spatialQuery (offset : List Bool → ℕ) (q : List Bool) : List Bool :=
  pair (pairFst q) (BinaryNatCode.encode (Nat.fromBitsLE (pairSnd q) - offset (pairFst q) + 1))

theorem oldQuery_FP : oldQuery ∈ FP :=
  mem_FP_pair (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairSnd_mem_FP
theorem retainedQuery_FP : retainedQuery ∈ FP := mem_FP_pair pairFst_mem_FP (constFn_mem_FP [])
theorem spatialQuery_FP {offset : List Bool → ℕ} (ho : BinaryFn offset) : spatialQuery offset ∈ FP :=
  mem_FP_pair pairFst_mem_FP
    (((BinaryFn.fromBits pairSnd_mem_FP).sub (ho.comp pairFst_mem_FP)).add (BinaryFn.const 1)).bits_mem_FP

def old (F : Family) : Family :=
  reindex F pairFst oldQuery (fun _ => pairFst_pair _ _)
def retained (G : Family) : Family :=
  reindex G id retainedQuery (fun _ => pairFst_pair _ _)
def spatial (G : Family) (offset : List Bool → ℕ) : Family :=
  reindex G id (spatialQuery offset) (fun _ => pairFst_pair _ _)

noncomputable def update (F G : Family) (offset dim : List Bool → ℕ) : Family :=
  choose (fun q => InBlock (offset (pairFst q)) (dim (pairFst q)) (Nat.fromBitsLE (pairSnd q)))
    (spatial G offset) (compose (old F) (retained G))

theorem access {F G : Family} (A : Access F) (B : Access G)
    {offset dim : List Bool → ℕ} (ho : BinaryFn offset) (hk : BinaryFn dim) : Access (update F G offset dim) := by
  have O := reindex_access A pairFst oldQuery (fun _ => pairFst_pair _ _) pairFst_mem_FP oldQuery_FP
  have R := reindex_access B id retainedQuery (fun _ => pairFst_pair _ _) id_mem_FP retainedQuery_FP
  have S := reindex_access B id (spatialQuery offset) (fun _ => pairFst_pair _ _) id_mem_FP (spatialQuery_FP ho)
  have hi := BinaryFn.fromBits pairSnd_mem_FP
  have hO : BinaryFn (fun q => offset (pairFst q)) := ho.comp pairFst_mem_FP
  have hK : BinaryFn (fun q => dim (pairFst q)) := hk.comp pairFst_mem_FP
  exact choose_access ((hO.le hi).and (hi.lt (hO.add hK))) S (compose_access O R)

theorem coordinate (F G : Family) (offset dim : List Bool → ℕ) (u : List Bool) (i : ℕ) :
    (update F G offset dim).coordinate (pair u (BinaryNatCode.encode i)) =
      if InBlock (offset u) (dim u) i then G.coordinate (pair u (BinaryNatCode.encode (i - offset u + 1)))
      else (F.coordinate (pair (pairFst u) (BinaryNatCode.encode i))).compWith (F.degree (pairFst u))
        (G.coordinate (pair u (BinaryNatCode.encode 0))) := by
  simp only [update, choose, spatial, old, retained, reindex, compose, oldQuery, retainedQuery,
    spatialQuery, Function.comp_apply, id_eq, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits, Nat.zero_bits]

theorem point_update (F G : Family) (offset dim : List Bool → ℕ) (u : List Bool) (theta : ℝ)
    (hG : Defined G u theta) (i : ℕ) :
    point (update F G offset dim) u theta i =
      if InBlock (offset u) (dim u) i then point G u theta (i - offset u + 1)
      else point F (pairFst u) (point G u theta 0) i := by
  unfold point
  rw [coordinate]
  split_ifs
  · rfl
  · exact Coordinate.eval_compWith _ _ _ (by simpa only [pairFst_pair] using F.degree_le (pair (pairFst u) (BinaryNatCode.encode i))) theta (hG 0)

theorem defined_update (F G : Family) (offset dim : List Bool → ℕ) (u : List Bool) (theta : ℝ)
    (hG : Defined G u theta) (hF : Defined F (pairFst u) (point G u theta 0)) :
    Defined (update F G offset dim) u theta := by
  intro i
  rw [coordinate]
  split_ifs
  · exact hG _
  · exact Coordinate.compWith_denominator_ne_zero _ _ _
      (by simpa only [pairFst_pair] using F.degree_le (pair (pairFst u) (BinaryNatCode.encode i)))
      theta (hG 0) (hF i)

end LeanCanny.Algebra.RationalParentUpdate
