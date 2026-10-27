/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.BoundedFoldSpace
public import LeanCanny.Encoding.BinaryBitFP
public import LeanCanny.Computation.PolyTimeBinaryNat

/-! # Native Boolean circuits with polynomial-space atom decisions

Each gate appends one bit to a polynomial-size table. Binary references
outside the computed prefix read false, giving total behavior on all gate
descriptions. Constants, atoms, negation, conjunction, and disjunction are
supported. The atom computation may use polynomial space and arbitrary time.
-/

@[expose] public section
namespace LeanCanny.Computation.BooleanCircuitSpace
open LeanCanny.Encoding
open Turing.MultiTapeTM

structure Family where
  count : List Bool → ℕ
  tag : List Bool → ℕ
  left : List Bool → ℕ
  right : List Bool → ℕ

structure Access (F : Family) : Prop where
  count : UnaryFn F.count
  tag : BinaryFn F.tag
  left : BinaryFn F.left
  right : BinaryFn F.right

def operation (tag : ℕ) (atom left right : Bool) : Bool := decide
  (tag = 1 ∨ (tag = 2 ∧ atom = true) ∨ (tag = 3 ∧ left = false) ∨
    (tag = 4 ∧ left = true ∧ right = true) ∨ (tag = 5 ∧ (left = true ∨ right = true)))

def values (F : Family) (atom : List Bool → Bool) (c : List Bool) : ℕ → List Bool
  | 0 => []
  | k + 1 =>
      let q := pair c (BinaryNatCode.encode k)
      let v := values F atom c k
      v ++ [operation (F.tag q) (atom q) (v[F.left q]?.getD false) (v[F.right q]?.getD false)]

theorem values_length (F : Family) (atom : List Bool → Bool) (c : List Bool) (k : ℕ) :
    (values F atom c k).length = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [values, List.length_append, List.length_singleton, ih]

def value (F : Family) (atom : List Bool → Bool) (c : List Bool) : Bool :=
  (values F atom c (F.count c))[F.count c - 1]?.getD false

def childQuery (z : List Bool) : List Bool := BoundedFold.query (pairFst z)
def prior (z : List Bool) : List Bool := BoundedFold.accumulator (pairFst z)

def finish (F : Family) (z : List Bool) : List Bool := prior z ++
  [operation (F.tag (childQuery z)) ((pairSnd z)[0]?.getD false)
    ((prior z)[F.left (childQuery z)]?.getD false) ((prior z)[F.right (childQuery z)]?.getD false)]

private theorem binaryBit {word : List Bool → List Bool} {index : List Bool → ℕ}
    (hw : word ∈ FP) (hi : BinaryFn index) : FPPred (fun z => (word z)[index z]?.getD false = true) := by
  have hn := UnaryFn.fromBitsLE_min hi.bits_mem_FP (UnaryFn.length hw)
  have H := FPPred.getBit hw hn
  exact H.of_iff (fun z => by simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits, BinaryNat.getD_min_length])

theorem finish_FP (F : Family) (A : Access F) : finish F ∈ FP := by
  have hq : childQuery ∈ FP := mem_FP_comp pairFst_mem_FP BoundedFold.query_mem_FP
  have hp : prior ∈ FP := mem_FP_comp pairFst_mem_FP BoundedFold.accumulator_mem_FP
  have ht : BinaryFn (fun z => F.tag (childQuery z)) := A.tag.comp hq
  have hl : BinaryFn (fun z => F.left (childQuery z)) := A.left.comp hq
  have hr : BinaryFn (fun z => F.right (childQuery z)) := A.right.comp hq
  have hb := FPPred.getBit pairSnd_mem_FP (UnaryFn.const 0)
  have hL := binaryBit hp hl
  have hR := binaryBit hp hr
  have hnot : FPPred (fun z => (prior z)[F.left (childQuery z)]?.getD false = false) :=
    hL.not.of_iff (fun z => by cases (prior z)[F.left (childQuery z)]?.getD false <;> decide)
  have hg := (ht.eq (BinaryFn.const 1)).or (((ht.eq (BinaryFn.const 2)).and hb).or
    (((ht.eq (BinaryFn.const 3)).and hnot).or (((ht.eq (BinaryFn.const 4)).and (hL.and hR)).or
      ((ht.eq (BinaryFn.const 5)).and (hL.or hR)))))
  exact appendFn_mem_FP hp hg.flag_mem_FP

def step (F : Family) (atom : List Bool → Bool) : List Bool → List Bool :=
  BoundedFold.update (finish F) (fun q => [atom q])

theorem step_packet (F : Family) (atom : List Bool → Bool) (c : List Bool) (k : ℕ) :
    step F atom (BoundedFold.packet c k (values F atom c k)) = values F atom c (k + 1) := by
  simp only [step, BoundedFold.update, finish, childQuery, prior, BoundedFold.query,
    pairFst_pair, pairSnd_pair, BoundedFold.context_packet, BoundedFold.counter_packet,
    BoundedFold.accumulator_packet, List.getElem?_cons_zero, Option.getD_some, values]

theorem values_evaluator (F : Family) (A : Access F) (atom : List Bool → Bool)
    (R : SpaceFunction (fun q => [atom q])) : SpaceFunction (fun c => values F atom c (F.count c)) := by
  have E := BoundedFold.updateEvaluator R (finish F) (finish_FP F A)
  obtain ⟨p, hp⟩ := output_length_poly_of_mem_FP A.count.mem_FP
  have hbound (c : List Bool) : F.count c ≤ p.eval c.length := by
    simpa only [List.length_replicate] using hp c
  have H := BoundedFold.evaluator_spec E (fun c => BinaryNatCode.encode (F.count c)) (fun _ => [])
    (bits_mem_FP A.count) (constFn_mem_FP []) (values F atom) (fun _ => rfl)
    (fun c k _ => step_packet F atom c k)
    (PolyBounded.of_polynomiallyBounded _ (.polynomial_eval p))
    (fun c k hk => by rw [values_length]; rw [BinaryNatCode.encode, Nat.fromBitsLE_bits] at hk; exact hk.trans (hbound c))
  exact H.congr (funext fun c => by rw [BinaryNatCode.encode, Nat.fromBitsLE_bits])

theorem evaluator (F : Family) (A : Access F) (atom : List Bool → Bool)
    (R : SpaceFunction (fun q => [atom q])) : SpaceFunction (fun c => [value F atom c]) := by
  have hout := getBit_mem_FP id_mem_FP ((UnaryFn.length id_mem_FP).sub (UnaryFn.const 1))
  have E := (values_evaluator F A atom R).postcompose
    (fun v => [v[v.length - 1]?.getD false]) hout
  exact E.congr (funext fun c => by simp only [Function.comp_apply, values_length, value])

def language (F : Family) (atom : List Bool → Bool) : Language := {c | value F atom c = true}

theorem decider (F : Family) (A : Access F) (atom : List Bool → Bool)
    (R : SpaceFunction (fun q => [atom q])) : SpaceDecider (language F atom) := by
  apply (evaluator F A atom R).decider (fun z => decide (z = [true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro c
  simp only [language, Set.mem_ofPred_eq, decide_eq_true_eq, List.cons.injEq, and_true]

def Family.comp (F : Family) (f : List Bool → List Bool) : Family where
  count c := F.count (f c)
  tag q := F.tag (pair (f (pairFst q)) (pairSnd q))
  left q := F.left (pair (f (pairFst q)) (pairSnd q))
  right q := F.right (pair (f (pairFst q)) (pairSnd q))

theorem Access.comp {F : Family} (A : Access F) (f : List Bool → List Bool) (hf : f ∈ FP) : Access (F.comp f) := by
  have hq := mem_FP_pair (mem_FP_comp pairFst_mem_FP hf) pairSnd_mem_FP
  exact ⟨A.count.comp hf, A.tag.comp hq, A.left.comp hq, A.right.comp hq⟩

theorem values_comp (F : Family) (f : List Bool → List Bool) (atom sourceAtom : List Bool → Bool)
    (c : List Bool) (n : ℕ) (h : ∀ k < n, atom (pair c (BinaryNatCode.encode k)) = sourceAtom (pair (f c) (BinaryNatCode.encode k))) :
    values (F.comp f) atom c n = values F sourceAtom (f c) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [values]
    rw [ih (fun k hk => h k (by omega)), h n (by omega)]
    simp only [Family.comp, pairFst_pair, pairSnd_pair]

theorem value_comp (F : Family) (f : List Bool → List Bool) (atom sourceAtom : List Bool → Bool)
    (c : List Bool) (h : ∀ k < F.count (f c), atom (pair c (BinaryNatCode.encode k)) = sourceAtom (pair (f c) (BinaryNatCode.encode k))) :
    value (F.comp f) atom c = value F sourceAtom (f c) := by
  unfold value
  change (values (F.comp f) atom c (F.count (f c)))[F.count (f c) - 1]?.getD false = _
  rw [values_comp F f atom sourceAtom c _ h]

end LeanCanny.Computation.BooleanCircuitSpace
