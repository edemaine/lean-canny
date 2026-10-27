/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedAlgebraicSliceSeed

/-! # Specializing a computed seed at the original algebraic parameter

Attaching actual-degree metadata preserves the root ordinal and its real
value. The original head and the streamed symbolic seed therefore specialize
to the head and fixed pseudo-remainder seed in the same real slice.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedAlgebraicSlice.Tarski
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter Polynomial
open scoped Classical
attribute [local irreducible] BoundedProjectionRootCount.count BoundedProjectionOrderedRoot.root
  point specialized degree

def liftQuery (v : List Bool) : List Bool := pair v (BinaryNat.normalize (pairSnd (pairFst v)))
theorem liftQuery_FP : liftQuery ∈ FP := by polytime [liftQuery]

theorem lift_valid (P : Readers) (v : List Bool) (hv : pairFst v ∈ valid P) :
    liftQuery v ∈ valid (P.comp origin) := by
  simpa only [valid, Set.mem_ofPred_eq, liftQuery, pairFst_pair, pairSnd_pair,
    BoundedProjectionRootCount.count_comp, BinaryNat.normalize_eq_bits, Nat.fromBitsLE_bits, origin] using hv

theorem lift_point (P : Readers) (v : List Bool) (hv : pairFst v ∈ valid P) :
    point (P.comp origin) (liftQuery v) = point P (pairFst v) := by
  let r : Fin (BoundedProjectionRootCount.count P (origin v)) := ⟨Nat.fromBitsLE (pairSnd (pairFst v)), hv⟩
  let s : Fin (BoundedProjectionRootCount.count (P.comp origin) v) :=
    ⟨r.val, by simpa only [BoundedProjectionRootCount.count_comp] using r.isLt⟩
  have hq : liftQuery v = pair v (BinaryNatCode.encode s.val) := by
    simp only [liftQuery, s, r, BinaryNat.normalize_eq_bits, BinaryNatCode.encode]
  rw [hq, point_packet, BoundedProjectionOrderedRoot.root_value_comp P origin v s r rfl]
  rw [point, dite_eq_left hv]
  rfl

theorem head_lift (P : Readers) (F : Family) (v : List Bool) (hv : pairFst v ∈ valid P) :
    specialized (P.comp origin) (headFamily F) (liftQuery v) = specialized P F (pairFst v) := by
  rw [specialized, ite_eq_left (lift_valid P v hv), specialized, ite_eq_left hv]
  rw [lift_point P v hv]
  simp only [liftQuery, pairFst_pair, Family.slice, headFamily, origin]

theorem seed_lift (P : Readers) (F G : Family) (v : List Bool) (hv : pairFst v ∈ valid P) :
    specialized (P.comp origin) (seedFamily F G) (liftQuery v) =
      PseudoRemainder.seed (specialized P F (pairFst v)) (specialized P G (pairFst v))
        (declared F G v) (bound F G v) := by
  rw [specialized, ite_eq_left (lift_valid P v hv), specialized, ite_eq_left hv, specialized, ite_eq_left hv]
  rw [lift_point P v hv]
  simp only [liftQuery, pairFst_pair, Family.slice, seedFamily, source, BivariateTarskiSeedBits.Family.seed, origin]
  rw [PseudoRemainder.seed_map]

theorem declared_prepare (P : Readers) (F G : Family) (u : List Bool) (hu : 0 < degree P F u) :
    declared F G (prepare P F u) = degree P F u := by
  have hd : degree P F u ≤ F.degree (pairFst u) := by simpa only [degree] using specialized_degree P F u
  simp only [declared, prepare, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits, bound, origin, pairFst_pair]
  omega

theorem degree_valid (P : Readers) (F : Family) (u : List Bool) (hu : 0 < degree P F u) : u ∈ valid P := by
  by_contra hv
  have hd : degree P F u = 0 := by rw [degree, specialized, ite_eq_right hv, Polynomial.natDegree_zero]
  omega

theorem input_degree (P : Readers) (F G : Family) (u : List Bool) :
    (specialized P G u * (specialized P F u).derivative).natDegree ≤ bound F G (prepare P F u) := by
  have hp := (Polynomial.natDegree_derivative_le (specialized P F u)).trans (Nat.sub_le _ _)
  have hF := specialized_degree P F u
  have hG := specialized_degree P G u
  apply Polynomial.natDegree_mul_le.trans
  simp only [bound, origin, prepare, pairFst_pair]
  omega

end LeanCanny.Encoding.BoundedAlgebraicSlice.Tarski
