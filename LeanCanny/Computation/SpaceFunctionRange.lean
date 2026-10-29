/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.BoundedFoldSpace
public import LeanCanny.Computation.SpaceFunctionChain
public import LeanCanny.Computation.PolyTimeArithmetic

/-! # Polynomial-space traversal of unary ranges

The child may take arbitrary polynomial space. Its native output-length
bound gives a common unary envelope, so concatenating a polynomial number of
child words retains only polynomial space.
-/

@[expose] public section
namespace LeanCanny.Computation.SpaceFunction
open Turing.MultiTapeTM

private def collectQuery (count : List Bool → ℕ) (p : List Bool) : List Bool :=
  pair (pairFst p) (List.replicate (min (Nat.fromBitsLE (BoundedFold.counter p)) (count (pairFst p))) true)
private def collectFinish (p : List Bool) : List Bool := BoundedFold.accumulator (pairFst p) ++ pairSnd p
private def collectStep (count : List Bool → ℕ) (f : List Bool → List Bool) (p : List Bool) : List Bool :=
  collectFinish (pair p (f (collectQuery count p)))

private theorem collectStep_evaluator {count : List Bool → ℕ} {f : List Bool → List Bool}
    (hn : UnaryFn count) (E : SpaceFunction f) : SpaceFunction (collectStep count f) := by
  have hi := UnaryFn.fromBitsLE_min BoundedFold.counter_mem_FP (hn.comp pairFst_mem_FP)
  have hq : collectQuery count ∈ FP := mem_FP_pair pairFst_mem_FP hi.mem_FP
  have hf : collectFinish ∈ FP := appendFn_mem_FP (mem_FP_comp (f := pairFst) (g := BoundedFold.accumulator) pairFst_mem_FP BoundedFold.accumulator_mem_FP) pairSnd_mem_FP
  exact E.call _ _ hq hf

private theorem collect_fold (count : List Bool → ℕ) (f : List Bool → List Bool) (c : List Bool) (k : ℕ) (hk : k ≤ count c) :
    BoundedFold.fold (collectStep count f) (fun _ => []) c k =
      (List.range k).flatMap (fun i => f (pair c (List.replicate i true))) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [BoundedFold.fold, ih (by omega)]
    simp only [collectStep, collectFinish, collectQuery, pairFst_pair, pairSnd_pair,
      BoundedFold.context_packet, BoundedFold.counter_packet, BoundedFold.accumulator_packet,
      show Nat.fromBitsLE (BinaryNatCode.encode k) = k from Nat.fromBitsLE_bits k,
      Nat.min_eq_left (show k ≤ count c by omega), List.range_succ, List.flatMap_append,
      List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-- A finite family of space-reader outputs has a common unary length bound. -/
theorem finiteLengthEnvelope {f : List Bool → List Bool} {count : List Bool → ℕ}
    (E : SpaceFunction f) (hn : UnaryFn count) :
    ∃ bound : List Bool → ℕ, UnaryFn bound ∧ ∀ c i, i < count c →
      (f (pair c (List.replicate i true))).length ≤ bound c := by
  obtain ⟨a, d, ha⟩ := E.computable.polyBounded_length.exists_le
  let bound : List Bool → ℕ := fun c => a * (2 * c.length + count c + 3) ^ d
  have hb : UnaryFn bound := (UnaryFn.const a).mul
    (((((UnaryFn.const 2).mul (UnaryFn.length id_mem_FP)).add hn).add (UnaryFn.const 3)).pow_const d)
  refine ⟨bound, hb, fun c i hi => ?_⟩
  have H : (f (pair c (List.replicate i true))).length ≤ a * ((pair c (List.replicate i true)).length + 1) ^ d := by
    simpa only [encBits_apply] using ha (pair c (List.replicate i true))
  apply H.trans
  apply Nat.mul_le_mul_left a (Nat.pow_le_pow_left ?_ d)
  rw [pair_length, List.length_replicate]
  omega

theorem flatMap_unary {f : List Bool → List Bool} {count : List Bool → ℕ}
    (E : SpaceFunction f) (hn : UnaryFn count) :
    SpaceFunction (fun c => (List.range (count c)).flatMap (fun i => f (pair c (List.replicate i true)))) := by
  obtain ⟨bound, hb, hsize⟩ := finiteLengthEnvelope E hn
  have hlen (c : List Bool) (k : ℕ) (hk : k ≤ count c) :
      ((List.range k).flatMap (fun i => f (pair c (List.replicate i true)))).length ≤ k * bound c := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [List.range_succ, List.flatMap_append]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_append]
      have H := Nat.add_le_add (ih (by omega)) (hsize c k (by omega))
      simpa only [Nat.succ_mul] using H
  obtain ⟨p, hp⟩ := output_length_poly_of_mem_FP (hn.mul hb).mem_FP
  have hpoly (c : List Bool) : count c * bound c ≤ p.eval c.length := by
    simpa only [List.length_replicate] using hp c
  have R := BoundedFold.evaluator (collectStep_evaluator hn E) (fun c => BinaryNatCode.encode (count c))
    (fun _ => []) (bits_mem_FP hn) (constFn_mem_FP []) p (fun c k hk => by
      simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits] at hk
      rw [collect_fold count f c k hk]
      exact (hlen c k hk).trans ((Nat.mul_le_mul_right (bound c) hk).trans (hpoly c)))
  exact R.congr (funext fun c => by
    simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits, collect_fold count f c _ le_rfl])

end LeanCanny.Computation.SpaceFunction
