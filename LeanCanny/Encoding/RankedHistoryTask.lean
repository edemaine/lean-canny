/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.PolyTimePairing
public import LeanCanny.Computation.PolyTimeBinaryNat

/-! # Flat ranked task words for retained-history readers

Every request stores the original input and history bank once, followed by
its birth, local phase, and query fields. Retargeting replaces these fields
while preserving that same root word. A fixed phase count and unary birth
cap give a polynomial rank bound for mixed recursive readers.
-/

@[expose] public section
namespace LeanCanny.Encoding.RankedHistoryTask
set_option backward.isDefEq.respectTransparency false

def root (q : List Bool) : List Bool := pairFst q
def birthWord (q : List Bool) : List Bool := pairFst (pairSnd q)
def phaseWord (q : List Bool) : List Bool := pairFst (pairSnd (pairSnd q))
def fields (q : List Bool) : List Bool := pairSnd (pairSnd (pairSnd q))
def pack (r : List Bool) (b p : ℕ) (f : List Bool) : List Bool :=
  pair r (pair (BinaryNatCode.encode b) (pair (BinaryNatCode.encode p) f))
def birth (cap : List Bool → ℕ) (q : List Bool) : ℕ := min (Nat.fromBitsLE (birthWord q)) (cap (root q))
def phase (P : ℕ) (q : List Bool) : ℕ := min (Nat.fromBitsLE (phaseWord q)) (P - 1)
def rank (cap : List Bool → ℕ) (P : ℕ) (q : List Bool) : ℕ := P * birth cap q + phase P q

theorem root_FP : root ∈ FP := pairFst_mem_FP
theorem birthWord_FP : birthWord ∈ FP := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
theorem phaseWord_FP : phaseWord ∈ FP := mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) pairFst_mem_FP
theorem fields_FP : fields ∈ FP := mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) pairSnd_mem_FP

@[simp] theorem root_pack (r : List Bool) (b p : ℕ) (f : List Bool) : root (pack r b p f) = r := by
  simp only [root, pack, pairFst_pair]
@[simp] theorem fields_pack (r : List Bool) (b p : ℕ) (f : List Bool) : fields (pack r b p f) = f := by
  simp only [fields, pack, pairSnd_pair]

theorem birth_pack (cap : List Bool → ℕ) (r : List Bool) (b p : ℕ) (f : List Bool) (hb : b ≤ cap r) :
    birth cap (pack r b p f) = b := by
  simp only [birth, birthWord, root, pack, pairSnd_pair, pairFst_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits, min_eq_left hb]

theorem phase_pack (P : ℕ) (r : List Bool) (b p : ℕ) (f : List Bool) (hp : p < P) :
    phase P (pack r b p f) = p := by
  have HP : p ≤ P - 1 := by omega
  simp only [phase, phaseWord, pack, pairSnd_pair, pairFst_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits, min_eq_left HP]

theorem pack_length (r : List Bool) (b p : ℕ) (f : List Bool) :
    (pack r b p f).length = 2 * r.length + 2 * b.size + 2 * p.size + f.length + 6 := by
  simp only [pack, pair_length, BinaryNatCode.length_encode]
  omega

def retarget (b p : List Bool → ℕ) (f : List Bool → List Bool) (q : List Bool) : List Bool :=
  pack (root q) (b q) (p q) (f q)

theorem retarget_FP {b p : List Bool → ℕ} {f : List Bool → List Bool}
    (hb : BinaryFn b) (hp : BinaryFn p) (hf : f ∈ FP) : retarget b p f ∈ FP :=
  mem_FP_pair root_FP (mem_FP_pair hb.bits_mem_FP (mem_FP_pair hp.bits_mem_FP hf))

theorem retarget_root (b p : List Bool → ℕ) (f : List Bool → List Bool) (q : List Bool) :
    root (retarget b p f q) = root q := root_pack _ _ _ _

theorem birth_unary (cap : List Bool → ℕ) (hc : UnaryFn cap) : UnaryFn (birth cap) :=
  UnaryFn.fromBitsLE_min birthWord_FP (hc.comp root_FP)
theorem phase_unary (P : ℕ) : UnaryFn (phase P) :=
  UnaryFn.fromBitsLE_min phaseWord_FP (UnaryFn.const (P - 1))
theorem rank_unary (cap : List Bool → ℕ) (hc : UnaryFn cap) (P : ℕ) : UnaryFn (rank cap P) :=
  ((UnaryFn.const P).mul (birth_unary cap hc)).add (phase_unary P)

theorem rank_bound (cap : List Bool → ℕ) (P : ℕ) (hP : 0 < P) (q : List Bool) :
    rank cap P q < P * (cap (root q) + 1) := by
  have HB : birth cap q ≤ cap (root q) := min_le_right _ _
  have HP : phase P q < P := (min_le_right _ _).trans_lt (by omega : P - 1 < P)
  unfold rank
  nlinarith

theorem lower_birth (cap : List Bool → ℕ) (P : ℕ) (q : List Bool) (b p : ℕ) (f : List Bool)
    (hb : b < birth cap q) (hp : p < P) : rank cap P (pack (root q) b p f) < rank cap P q := by
  have HB : b ≤ cap (root q) := hb.le.trans (min_le_right _ _)
  rw [rank, birth_pack cap _ _ _ _ HB, phase_pack _ _ _ _ _ hp]
  unfold rank
  nlinarith

theorem lower_phase (cap : List Bool → ℕ) (P : ℕ) (q : List Bool) (p : ℕ) (f : List Bool)
    (hp : p < phase P q) : rank cap P (pack (root q) (birth cap q) p f) < rank cap P q := by
  have HP : p < P := hp.trans_le ((min_le_right _ _).trans (Nat.sub_le P 1))
  have HB : birth cap q ≤ cap (root q) := min_le_right _ _
  rw [rank, birth_pack cap (root q) (birth cap q) p f HB, phase_pack _ _ _ _ _ HP]
  exact Nat.add_lt_add_left hp _

def wordBudget (cap : List Bool → ℕ) (P : ℕ) (bound : List Bool → ℕ) (q : List Bool) : ℕ :=
  2 * (root q).length + 2 * (cap (root q)).size + 2 * P.size + bound (root q) + 6

theorem pack_length_le (cap : List Bool → ℕ) (P : ℕ) (bound : List Bool → ℕ)
    (q : List Bool) (b p : ℕ) (f : List Bool) (hb : b ≤ cap (root q)) (hp : p ≤ P)
    (hf : f.length ≤ bound (root q)) : (pack (root q) b p f).length ≤ wordBudget cap P bound q := by
  rw [pack_length]
  have HB := Nat.size_le_size hb
  have HP := Nat.size_le_size hp
  unfold wordBudget
  omega

theorem retarget_iterate_root (b p : List Bool → ℕ) (f : List Bool → List Bool) (q : List Bool) (n : ℕ) :
    root ((retarget b p f)^[n] q) = root q := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', retarget_root, ih]

theorem retarget_iterate_length (cap : List Bool → ℕ) (P : ℕ) (bound b p : List Bool → ℕ)
    (f : List Bool → List Bool)
    (hb : ∀ q, b q ≤ cap (root q)) (hp : ∀ q, p q ≤ P)
    (hf : ∀ q, (f q).length ≤ bound (root q)) (q : List Bool) (n : ℕ) :
    ((retarget b p f)^[n] q).length ≤ q.length + wordBudget cap P bound q := by
  cases n with
  | zero => exact Nat.le_add_right _ _
  | succ n =>
    rw [Function.iterate_succ_apply']
    let x := (retarget b p f)^[n] q
    have H := pack_length_le cap P bound x (b x) (p x) (f x) (hb x) (hp x) (hf x)
    have HE : wordBudget cap P bound x = wordBudget cap P bound q := by
      dsimp only [x]
      simp only [wordBudget, retarget_iterate_root]
    rw [HE] at H
    exact H.trans (Nat.le_add_left _ _)

theorem wordBudget_unary (cap : List Bool → ℕ) (P : ℕ) (bound : List Bool → ℕ)
    (hc : UnaryFn cap) (hb : UnaryFn bound) : UnaryFn (wordBudget cap P bound) := by
  have HR := UnaryFn.length root_FP
  have HC : UnaryFn (fun q => (cap (root q)).size) :=
    (UnaryFn.length (BinaryFn.ofUnary (hc.comp root_FP)).bits_mem_FP).of_eq
      (fun q => BinaryNatCode.length_encode _)
  exact (((((UnaryFn.const 2).mul HR).add ((UnaryFn.const 2).mul HC)).add
    (UnaryFn.const (2 * P.size))).add (hb.comp root_FP)).add (UnaryFn.const 6)

end LeanCanny.Encoding.RankedHistoryTask
