/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.ThomEncodingOrder
public import LeanCanny.Algebra.InfinitesimalSignSpace

/-! # A native one-bit scan for Thom-sign comparisons

The child returns two sign tags for the requested derivative index. The scan
also reads the next index and retains a single comparison bit. Its space
certificate is total even for malformed child tags.
-/

@[expose] public section
namespace LeanCanny.Algebra.ThomOrderBits
open LeanCanny.Encoding LeanCanny.Computation Brackets

def below (a b : List Bool) : Prop :=
  (a = [true] ∧ b ≠ [true]) ∨ (a = [] ∧ b = [false, true])
instance (a b : List Bool) : Decidable (below a b) := inferInstanceAs (Decidable (_ ∨ _))

theorem below_pred {f g : List Bool → List Bool} (hf : f ∈ FP) (hg : g ∈ FP) :
    FPPred (fun z => below (f z) (g z)) :=
  ((stringEq_fppred hf (constFn_mem_FP [true])).and
      (stringEq_fppred hg (constFn_mem_FP [true])).not).or
    ((stringEq_fppred hf (constFn_mem_FP [])).and (stringEq_fppred hg (constFn_mem_FP [false, true])))

theorem below_packet (a b : SignType) : below (InfinitesimalSign.encode a) (InfinitesimalSign.encode b) ↔ a < b := by
  cases a <;> cases b <;> decide

def orient (z : List Bool) : Bool := decide
  ((pairSnd z = [false, true] ∧ below (pairFst (pairFst z)) (pairSnd (pairFst z))) ∨
    (pairSnd z = [true] ∧ below (pairSnd (pairFst z)) (pairFst (pairFst z))))

theorem orient_FP : (fun z => [orient z]) ∈ FP := by
  have hA := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
  have hB := mem_FP_comp pairFst_mem_FP pairSnd_mem_FP
  exact (((stringEq_fppred pairSnd_mem_FP (constFn_mem_FP [false, true])).and (below_pred hA hB)).or
    ((stringEq_fppred pairSnd_mem_FP (constFn_mem_FP [true])).and (below_pred hB hA))).flag_mem_FP

theorem orient_packet (a b next : SignType) :
    orient (pair (pair (InfinitesimalSign.encode a) (InfinitesimalSign.encode b)) (InfinitesimalSign.encode next)) =
      ThomEncoding.direction a b next := by
  cases a <;> cases b <;> cases next <;> decide

def nextQuery (p : List Bool) : List Bool := pair (pairFst p) (BinaryNat.succ (BoundedFold.counter p))
theorem nextQuery_FP : nextQuery ∈ FP := by
  have hs := mem_FP_comp BoundedFold.counter_mem_FP BinaryNat.succ_mem_FP
  exact mem_FP_pair pairFst_mem_FP hs

def leftTag (z : List Bool) : List Bool := pairFst (pairFst (pairSnd z))
def rightTag (z : List Bool) : List Bool := pairSnd (pairFst (pairSnd z))
def orientQuery (z : List Bool) : List Bool := pair (pairFst (pairSnd z)) (pairFst (pairSnd (pairSnd z)))
theorem leftTag_FP : leftTag ∈ FP := mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP) pairFst_mem_FP
theorem rightTag_FP : rightTag ∈ FP := mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP) pairSnd_mem_FP
theorem orientQuery_FP : orientQuery ∈ FP := mem_FP_pair (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP)
  (mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) pairFst_mem_FP)

def finish (z : List Bool) : List Bool :=
  if leftTag z = rightTag z then BoundedFold.accumulator (pairFst z) else [orient (orientQuery z)]
theorem finish_FP : finish ∈ FP := by
  have ha := mem_FP_comp pairFst_mem_FP BoundedFold.accumulator_mem_FP
  have ho := mem_FP_comp orientQuery_FP orient_FP
  exact (stringEq_fppred leftTag_FP rightTag_FP).ite_mem_FP ha ho

def update (f : List Bool → List Bool) (p : List Bool) : List Bool :=
  finish (pair p (pair (f (BoundedFold.query p)) (f (nextQuery p))))

theorem update_evaluator {f : List Bool → List Bool} (E : SpaceFunction f) : SpaceFunction (update f) := by
  have L := E.precompose BoundedFold.query BoundedFold.query_mem_FP
  have R := E.precompose nextQuery nextQuery_FP
  exact ((L.pairOutputs R).withInput.postcompose finish finish_FP).congr (funext fun _ => rfl)

theorem fold_length (f : List Bool → List Bool) (q : List Bool) (n : ℕ) :
    (BoundedFold.fold (update f) (fun _ => [false]) q n).length = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [BoundedFold.fold, update, finish]
    split_ifs
    · simpa only [pairFst_pair, BoundedFold.accumulator_packet] using ih
    · rfl

def value (f bound : List Bool → List Bool) (q : List Bool) : List Bool :=
  BoundedFold.fold (update f) (fun _ => [false]) q (Nat.fromBitsLE (bound q))

theorem evaluator {f bound : List Bool → List Bool} (E : SpaceFunction f) (hb : bound ∈ FP) :
    SpaceFunction (value f bound) :=
  BoundedFold.evaluator (update_evaluator E) bound (fun _ => [false]) hb (constFn_mem_FP _) 1
    (fun q n _ => by simpa only [fold_length, Polynomial.eval_one] using Nat.le_refl 1)

theorem fold_packet (f : List Bool → List Bool) (q : List Bool) (a b : ℕ → SignType)
    (hf : ∀ k, f (pair q (BinaryNatCode.encode k)) = pair (InfinitesimalSign.encode (a k)) (InfinitesimalSign.encode (b k)))
    (n : ℕ) : BoundedFold.fold (update f) (fun _ => [false]) q n = [ThomEncoding.orderScan a b n] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hsucc : BinaryNat.succ (BinaryNatCode.encode n) = BinaryNatCode.encode (n + 1) := by
      simp only [BinaryNat.succ_eq_bits, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    rw [BoundedFold.fold, ih]
    simp only [update, BoundedFold.query, nextQuery, BoundedFold.context_packet, BoundedFold.counter_packet,
      hsucc, hf, finish, leftTag, rightTag, orientQuery,
      pairFst_pair, pairSnd_pair, BoundedFold.accumulator_packet, orient_packet, ThomEncoding.orderScan]
    have he : InfinitesimalSign.encode (a n) = InfinitesimalSign.encode (b n) ↔ a n = b n := by
      cases a n <;> cases b n <;> decide
    by_cases hn : a n = b n <;> simp only [he, hn, ↓reduceIte]

end LeanCanny.Algebra.ThomOrderBits
