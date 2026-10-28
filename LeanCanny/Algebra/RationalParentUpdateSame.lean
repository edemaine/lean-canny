/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.RationalParentUpdate

/-! # Updating a rational parent within the same source context -/

@[expose] public section
namespace LeanCanny.Algebra.RationalParentUpdate
open LeanCanny.Encoding LeanCanny.Computation UnivariateRational RationalCoordinateFamily
open BoundedCriticalSampleBlockSource (InBlock)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def same (F G : Family) (offset dim : List Bool → ℕ) : Family :=
  choose (fun q => InBlock (offset (pairFst q)) (dim (pairFst q)) (Nat.fromBitsLE (pairSnd q)))
    (spatial G offset) (compose F (retained G))

theorem same_access {F G : Family} (A : Access F) (B : Access G)
    {offset dim : List Bool → ℕ} (ho : BinaryFn offset) (hk : BinaryFn dim) : Access (same F G offset dim) := by
  have R := reindex_access B id retainedQuery (fun _ => pairFst_pair _ _) id_mem_FP retainedQuery_FP
  have S := reindex_access B id (spatialQuery offset) (fun _ => pairFst_pair _ _) id_mem_FP (spatialQuery_FP ho)
  have hi := BinaryFn.fromBits pairSnd_mem_FP
  have hO : BinaryFn (fun q => offset (pairFst q)) := ho.comp pairFst_mem_FP
  have hK : BinaryFn (fun q => dim (pairFst q)) := hk.comp pairFst_mem_FP
  exact choose_access ((hO.le hi).and (hi.lt (hO.add hK))) S (compose_access A R)

theorem same_coordinate (F G : Family) (offset dim : List Bool → ℕ) (u : List Bool) (i : ℕ) :
    (same F G offset dim).coordinate (pair u (BinaryNatCode.encode i)) =
      if InBlock (offset u) (dim u) i then G.coordinate (pair u (BinaryNatCode.encode (i - offset u + 1)))
      else (F.coordinate (pair u (BinaryNatCode.encode i))).compWith (F.degree u)
        (G.coordinate (pair u (BinaryNatCode.encode 0))) := by
  simp only [same, choose, spatial, retained, reindex, compose, retainedQuery, spatialQuery,
    Function.comp_apply, id_eq, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits, Nat.zero_bits]

theorem same_point (F G : Family) (offset dim : List Bool → ℕ) (u : List Bool) (theta : ℝ)
    (hG : Defined G u theta) (i : ℕ) :
    point (same F G offset dim) u theta i =
      if InBlock (offset u) (dim u) i then point G u theta (i - offset u + 1)
      else point F u (point G u theta 0) i := by
  unfold point
  rw [same_coordinate]
  split_ifs
  · rfl
  · exact Coordinate.eval_compWith _ _ _
      (by simpa only [pairFst_pair] using F.degree_le (pair u (BinaryNatCode.encode i))) theta (hG 0)

theorem same_defined (F G : Family) (offset dim : List Bool → ℕ) (u : List Bool) (theta : ℝ)
    (hG : Defined G u theta) (hF : Defined F u (point G u theta 0)) :
    Defined (same F G offset dim) u theta := by
  intro i
  rw [same_coordinate]
  split_ifs
  · exact hG _
  · exact Coordinate.compWith_denominator_ne_zero _ _ _
      (by simpa only [pairFst_pair] using F.degree_le (pair u (BinaryNatCode.encode i)))
      theta (hG 0) (hF i)

end LeanCanny.Algebra.RationalParentUpdate
