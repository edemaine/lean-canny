/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.SignStatistic
public import LeanCanny.Algebra.InfinitesimalSignSpace
public import LeanCanny.Encoding.BinaryModFP
public import LeanCanny.Encoding.BinaryMulFP
import Mathlib.Algebra.Ring.Parity

/-! # Polynomial-space streaming of signed principal-coefficient statistics

Binary counters retain zero gaps and positive/negative contributions. Sign
evaluation is a space-bounded child of the bounded scan; its workspace is
included in the resulting machine certificate.
-/

@[expose] public section

namespace LeanCanny.Algebra.SignStatisticBits
open Complexity
open LeanCanny.Encoding
open LeanCanny.Encoding.Brackets
open LeanCanny.Computation
open SignStatistic PrincipalSubresultant

def evenWord (w : List Bool) : Prop := BinaryNat.mod (pair w [false, true]) = []
instance (w : List Bool) : Decidable (evenWord w) := inferInstanceAs
  (Decidable (BinaryNat.mod (pair w [false, true]) = []))
def chooseTwo (w : List Bool) : List Bool :=
  BinaryNat.half (BinaryNat.mul (pair w (BinaryNat.pred w)))

theorem evenWord_iff (w : List Bool) : evenWord w ↔ Even (Nat.fromBitsLE w) := by
  simp only [evenWord, BinaryNat.mod_pair, BinaryNat.bits_eq_nil_iff]
  change Nat.fromBitsLE w % 2 = 0 ↔ Even (Nat.fromBitsLE w)
  exact Nat.even_iff.symm

theorem evenWord_fppred : FPPred evenWord :=
  stringEq_fppred (mem_FP_comp (mem_FP_pair id_mem_FP (constFn_mem_FP [false, true]))
    BinaryNat.mod_mem_FP) (constFn_mem_FP [])

theorem chooseTwo_mem_FP : chooseTwo ∈ FP :=
  mem_FP_comp (mem_FP_comp (mem_FP_pair id_mem_FP BinaryNat.pred_mem_FP)
    BinaryNat.mul_mem_FP) BinaryNat.half_mem_FP

theorem chooseTwo_code (n : ℕ) :
    chooseTwo n.bits = (n.choose 2).bits := by
  simp only [chooseTwo, BinaryNat.pred_eq_bits, BinaryNat.mul_pair, BinaryNat.half_eq_bits,
    Nat.fromBitsLE_bits, Nat.choose_two_right]

def pack (a g p n : List Bool) : List Bool := pair a (pair g (pair p n))
def encode (s : State) : List Bool := pack (InfinitesimalSign.encode s.previous)
  (BinaryNatCode.encode s.gap) (BinaryNatCode.encode s.positive) (BinaryNatCode.encode s.negative)

def previous (w : List Bool) : List Bool := pairFst (pairFst w)
def gap (w : List Bool) : List Bool := pairFst (pairSnd (pairFst w))
def positive (w : List Bool) : List Bool := pairFst (pairSnd (pairSnd (pairFst w)))
def negative (w : List Bool) : List Bool := pairSnd (pairSnd (pairSnd (pairFst w)))
def current (w : List Bool) : List Bool := pairSnd w

theorem previous_mem_FP : previous ∈ FP := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
theorem gap_mem_FP : gap ∈ FP :=
  mem_FP_comp (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) pairFst_mem_FP
theorem positive_mem_FP : positive ∈ FP :=
  mem_FP_comp (mem_FP_comp (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) pairSnd_mem_FP) pairFst_mem_FP
theorem negative_mem_FP : negative ∈ FP :=
  mem_FP_comp (mem_FP_comp (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) pairSnd_mem_FP) pairSnd_mem_FP
theorem current_mem_FP : current ∈ FP := pairSnd_mem_FP

def active (w : List Bool) : Prop := previous w ≠ [] ∧ current w ≠ [] ∧ evenWord (gap w)
def agrees (w : List Bool) : Prop := previous w = current w
def plusWeight (w : List Bool) : Prop := evenWord (chooseTwo (gap w))
def positiveStep (w : List Bool) : Prop := active w ∧
  ((plusWeight w ∧ agrees w) ∨ (¬plusWeight w ∧ ¬agrees w))
def negativeStep (w : List Bool) : Prop := active w ∧
  ((plusWeight w ∧ ¬agrees w) ∨ (¬plusWeight w ∧ agrees w))

instance (w : List Bool) : Decidable (active w) := inferInstanceAs
  (Decidable (previous w ≠ [] ∧ current w ≠ [] ∧ evenWord (gap w)))
instance (w : List Bool) : Decidable (agrees w) := inferInstanceAs (Decidable (previous w = current w))
instance (w : List Bool) : Decidable (plusWeight w) := inferInstanceAs
  (Decidable (evenWord (chooseTwo (gap w))))
instance (w : List Bool) : Decidable (positiveStep w) := inferInstanceAs
  (Decidable (active w ∧ ((plusWeight w ∧ agrees w) ∨ (¬plusWeight w ∧ ¬agrees w))))
instance (w : List Bool) : Decidable (negativeStep w) := inferInstanceAs
  (Decidable (active w ∧ ((plusWeight w ∧ ¬agrees w) ∨ (¬plusWeight w ∧ agrees w))))

theorem active_fppred : FPPred active :=
  ((stringEq_fppred previous_mem_FP (constFn_mem_FP [])).not).and
    (((stringEq_fppred current_mem_FP (constFn_mem_FP [])).not).and
      (evenWord_fppred.comp gap_mem_FP))
theorem agrees_fppred : FPPred agrees := stringEq_fppred previous_mem_FP current_mem_FP
theorem plusWeight_fppred : FPPred plusWeight :=
  evenWord_fppred.comp (show (chooseTwo ∘ gap) ∈ FP from
    mem_FP_comp gap_mem_FP chooseTwo_mem_FP)
theorem positiveStep_fppred : FPPred positiveStep :=
  active_fppred.and ((plusWeight_fppred.and agrees_fppred).or
    (plusWeight_fppred.not.and agrees_fppred.not))
theorem negativeStep_fppred : FPPred negativeStep :=
  active_fppred.and ((plusWeight_fppred.and agrees_fppred.not).or
    (plusWeight_fppred.not.and agrees_fppred))

def move (w : List Bool) : List Bool :=
  if current w = [] then pack (previous w) (BinaryNat.succ (gap w)) (positive w) (negative w)
  else pack (current w) []
    (if positiveStep w then BinaryNat.succ (positive w) else positive w)
    (if negativeStep w then BinaryNat.succ (negative w) else negative w)

theorem pack_mem_FP {a g p n : List Bool → List Bool}
    (ha : a ∈ FP) (hg : g ∈ FP) (hp : p ∈ FP) (hn : n ∈ FP) :
    (fun w => pack (a w) (g w) (p w) (n w)) ∈ FP :=
  mem_FP_pair ha (mem_FP_pair hg (mem_FP_pair hp hn))

theorem move_mem_FP : move ∈ FP := by
  have hp := positiveStep_fppred.ite_mem_FP
    (mem_FP_comp positive_mem_FP BinaryNat.succ_mem_FP) positive_mem_FP
  have hn := negativeStep_fppred.ite_mem_FP
    (mem_FP_comp negative_mem_FP BinaryNat.succ_mem_FP) negative_mem_FP
  have hz := pack_mem_FP previous_mem_FP (mem_FP_comp gap_mem_FP BinaryNat.succ_mem_FP)
    positive_mem_FP negative_mem_FP
  have hs := pack_mem_FP current_mem_FP (constFn_mem_FP []) hp hn
  have h := (stringEq_fppred current_mem_FP (constFn_mem_FP [])).ite_mem_FP hz hs
  refine mem_FP_of_eq (g := move) h ?_
  intro w
  simp only [move, Function.comp_apply]

theorem step_predicates (s : State) (a : SignType) :
    (positiveStep (pair (encode s) (InfinitesimalSign.encode a)) ↔ contribution s a = 1) ∧
    (negativeStep (pair (encode s) (InfinitesimalSign.encode a)) ↔ contribution s a = -1) := by
  rcases s with ⟨b, k, p, n⟩
  simp only [positiveStep, negativeStep, active, agrees, plusWeight, previous, gap, current,
    encode, pack, pairFst_pair, pairSnd_pair]
  simp only [evenWord_iff, BinaryNatCode.encode, chooseTwo_code, Nat.fromBitsLE_bits,
    contribution, zeroGapWeight_def]
  by_cases hk : Even k <;> by_cases hc : Even (k.choose 2) <;>
    cases b <;> cases a <;> simp [hk, hc, neg_one_pow_eq_ite, InfinitesimalSign.encode]

theorem move_encode (s : State) (a : SignType) :
    move (pair (encode s) (InfinitesimalSign.encode a)) = encode (step s a) := by
  have hp := (step_predicates s a).1
  have hn := (step_predicates s a).2
  unfold move
  simp only [hp, hn]
  simp only [current, previous, gap, positive, negative, encode, pack,
    pairFst_pair, pairSnd_pair]
  by_cases ha : a = 0
  · subst a
    simp only [InfinitesimalSign.encode, ↓reduceIte, SignStatistic.step, BinaryNat.succ_eq_bits,
      BinaryNatCode.encode, Nat.fromBitsLE_bits]
  · have ht : InfinitesimalSign.encode a ≠ [] := by cases a <;> simp_all [InfinitesimalSign.encode]
    simp only [ht, ↓reduceIte, SignStatistic.step, ha]
    split_ifs <;> simp [BinaryNat.succ_eq_bits, BinaryNatCode.encode, Nat.fromBitsLE_bits]

def query (p : List Bool) : List Bool := pair (pairFst p) (BoundedFold.counter p)
def finish (z : List Bool) : List Bool :=
  move (pair (BoundedFold.accumulator (pairFst z)) (pairSnd z))
def update (f : List Bool → List Bool) (p : List Bool) : List Bool :=
  finish (pair p (f (query p)))

theorem query_mem_FP : query ∈ FP := mem_FP_pair pairFst_mem_FP BoundedFold.counter_mem_FP
theorem finish_mem_FP : finish ∈ FP := by
  have h := mem_FP_comp (mem_FP_pair
    (mem_FP_comp pairFst_mem_FP BoundedFold.accumulator_mem_FP) pairSnd_mem_FP) move_mem_FP
  exact mem_FP_of_eq (g := finish) h (fun _ => rfl)

theorem updateEvaluator {f : List Bool → List Bool} (E : SpaceFunction f) :
    SpaceFunction (update f) := by
  let Q := ((E.precompose query query_mem_FP).withInput).postcompose finish finish_mem_FP
  refine Q.congr (funext fun p => ?_)
  simp only [update, Function.comp_apply]

theorem fold_eq_scan (f : List Bool → List Bool) (c : List Bool) (a : ℕ → SignType)
    (hf : ∀ i, f (pair c (BinaryNatCode.encode i)) = InfinitesimalSign.encode (a i)) (k : ℕ) :
    BoundedFold.fold (update f) (fun _ => encode initial) c k = encode (scan a k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [BoundedFold.fold, ih]
    simp only [update, finish, query, pairFst_pair, pairSnd_pair, BoundedFold.context_packet,
      BoundedFold.counter_packet, BoundedFold.accumulator_packet, hf, move_encode, scan]

theorem encode_length_bound (a : ℕ → SignType) (k : ℕ) :
    (encode (scan a k)).length ≤ 5 * k.size + 10 := by
  have hs : (InfinitesimalSign.encode (scan a k).previous).length ≤ 2 := by
    cases (scan a k).previous <;> decide
  obtain ⟨hg, hp, hn⟩ := scan_bounds a k
  have hg' := Nat.size_le_size hg
  have hp' := Nat.size_le_size hp
  have hn' := Nat.size_le_size hn
  simp only [encode, pack, pair_length, BinaryNatCode.length_encode]
  omega

/-- The two unsigned parts give a canonical signed integer encoding. -/
def integerCode (z : ℤ) : List Bool :=
  pair (BinaryNatCode.encode z.toNat) (BinaryNatCode.encode (-z).toNat)

def answer (v : List Bool) : List Bool :=
  pair (BinaryNat.sub (pair (pairFst (pairSnd (pairSnd v))) (pairSnd (pairSnd (pairSnd v)))))
    (BinaryNat.sub (pair (pairSnd (pairSnd (pairSnd v))) (pairFst (pairSnd (pairSnd v)))))

theorem answer_mem_FP : answer ∈ FP := by
  have hv := mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP
  have hp := mem_FP_comp hv pairFst_mem_FP
  have hn := mem_FP_comp hv pairSnd_mem_FP
  have hpn := mem_FP_comp (mem_FP_pair hp hn) BinaryNat.sub_mem_FP
  have hnp := mem_FP_comp (mem_FP_pair hn hp) BinaryNat.sub_mem_FP
  have h := mem_FP_pair hpn hnp
  refine mem_FP_of_eq (g := answer) h ?_
  intro v
  simp only [answer, Function.comp_apply]

theorem answer_encode (s : State) : answer (encode s) = integerCode s.value := by
  simp only [answer, encode, pack, pairFst_pair, pairSnd_pair, BinaryNat.sub_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits, integerCode, State.value]
  congr 2 <;> omega

/-- The sign source may itself use polynomial space. The binary count is FP;
neither the sign list nor its exponentially many coefficients is stored. -/
theorem evaluator {f : List Bool → List Bool} (E : SpaceFunction f)
    (count : List Bool → List Bool) (hc : count ∈ FP) (a : List Bool → ℕ → SignType)
    (hsign : ∀ c i, f (pair c (BinaryNatCode.encode i)) = InfinitesimalSign.encode (a c i)) :
    SpaceFunction (fun c => integerCode (permanencesMinusVariations
      ((List.range (Nat.fromBitsLE (count c))).map (a c)))) := by
  let p := Classical.choose (Cobham.output_length_poly_of_mem_FP hc)
  have hp : ∀ c, (count c).length ≤ p.eval c.length :=
    Classical.choose_spec (Cobham.output_length_poly_of_mem_FP hc)
  let Q := BoundedFold.evaluator (updateEvaluator E) count (fun _ => encode initial)
    hc (constFn_mem_FP _) (5 * p + 10) (by
      intro c k hk
      rw [fold_eq_scan f c (a c) (hsign c)]
      have hsize : k.size ≤ p.eval c.length := (Nat.size_le_size hk).trans
        ((Nat.size_le.mpr (Nat.fromBitsLE_lt_pow_length (count c))).trans (hp c))
      have hl := encode_length_bound (a c) k
      simpa only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat] using
        hl.trans (by omega))
  let R := Q.postcompose answer answer_mem_FP
  refine R.congr (funext fun c => ?_)
  simp only [Function.comp_apply]
  rw [fold_eq_scan f c (a c) (hsign c), answer_encode, scan_value]

end LeanCanny.Algebra.SignStatisticBits
