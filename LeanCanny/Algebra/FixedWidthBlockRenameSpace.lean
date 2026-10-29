/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.BlockRenameCoefficient
public import LeanCanny.Algebra.MatrixPowerArithmeticFP
public import LeanCanny.Computation.SpaceFunctionBranch
public import LeanCanny.Computation.PolyTimeBinaryNat
public import LeanCanny.Encoding.BinaryAddFP

/-! # Native coefficient access after embedding in a variable block

An FP guard rejects exponents outside the selected block. FP repacking sends
the remaining exponents to the original source reader. Moduli and source
context are retained, and noncanonical exponent words are normalized.
-/

@[expose] public section
namespace LeanCanny.Algebra.FixedWidthBlockRenameBits
open LeanCanny.Encoding LeanCanny.Computation FixedWidthPolynomial MatrixPower
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable (A N O W : List Bool → ℕ) (target : List Bool → List Bool)

def indexQuery (q : List Bool) : List Bool := pair (pairFst q)
  (BinaryNat.add (pair (BinaryNatCode.encode (O (pairFst q))) (pairSnd q)))

theorem indexQuery_FP (hO : UnaryFn O) : indexQuery O ∈ FP := by
  have hp : (fun q => pair (BinaryNatCode.encode (O (pairFst q))) (pairSnd q)) ∈ FP :=
    mem_FP_pair (BinaryFn.ofUnary hO.lift).bits_mem_FP pairSnd_mem_FP
  have ha : (fun q => BinaryNat.add (pair (BinaryNatCode.encode (O (pairFst q))) (pairSnd q))) ∈ FP :=
    mem_FP_comp (g := BinaryNat.add) hp BinaryNat.add_mem_FP
  exact mem_FP_pair pairFst_mem_FP ha

def read (q : List Bool) : List Bool := FixedWidthQuery.read N W target (indexQuery O q)

theorem read_FP (hN : UnaryFn N) (hO : UnaryFn O) (hW : UnaryFn W) (ht : target ∈ FP) :
    read N O W target ∈ FP := mem_FP_comp (indexQuery_FP O hO) (FixedWidthQuery.read_mem_FP hN hW ht)

theorem read_packet (c : List Bool) (i : ℕ) :
    read N O W target (pair c (BinaryNatCode.encode i)) =
      BinaryNatCode.encode (FixedWidthQuery.entry N W target c (O c + i)) := by
  simp only [read, indexQuery, pairFst_pair, pairSnd_pair, BinaryNat.add_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits]
  exact FixedWidthQuery.read_packet N W target c (O c + i)

def word (c : List Bool) : List Bool :=
  FixedWidthNatVector.encode (A c) (W c) (fun i => FixedWidthQuery.entry N W target c (O c + i))

theorem word_FP (hA : UnaryFn A) (hN : UnaryFn N) (hO : UnaryFn O) (hW : UnaryFn W) (ht : target ∈ FP) :
    word A N O W target ∈ FP :=
  FixedWidthNatVector.encode_mem_FP A W _ hA hW (read N O W target)
    (read_FP N O W target hN hO hW ht) (read_packet N O W target)

theorem word_coordinate (c : List Bool) (i : ℕ) (hi : i < A c) :
    FixedWidthQuery.coordinate W (word A N O W target) c i = FixedWidthQuery.entry N W target c (O c + i) := by
  apply FixedWidthNatVector.decode_block _ _ _ i hi
  unfold FixedWidthQuery.entry FixedWidthQuery.coordinate
  split_ifs
  · exact (Nat.fromBitsLE_lt_pow_length _).trans_le
      (Nat.pow_le_pow_right (by decide) (List.length_take_le _ _))
  · exact Nat.two_pow_pos _

def Supported (c : List Bool) : Prop := ∀ i < N c,
  (O c ≤ i ∧ i < O c + A c) ∨ FixedWidthQuery.coordinate W target c i = 0

theorem supported_FP (hA : UnaryFn A) (hN : UnaryFn N) (hO : UnaryFn O) (hW : UnaryFn W)
    (ht : target ∈ FP) : FPPred (Supported A N O W target) := by
  have hi := BinaryFn.ofUnary UnaryFn.index
  have hlo := (BinaryFn.ofUnary hO.lift).le hi
  have hhi := hi.lt (BinaryFn.ofUnary (hO.add hA).lift)
  have hc := take_mem_FP (drop_mem_FP (mem_FP_comp pairFst_mem_FP ht) (UnaryFn.index.mul hW.lift)) hW.lift
  have hz := (BinaryFn.fromBits hc).eq (BinaryFn.const 0)
  apply (FPPred.forall_lt hN ((hlo.and hhi).or hz)).of_iff
  intro c
  simp only [Supported, Function.comp_apply, pairFst_pair, pairSnd_pair, List.length_replicate,
    FixedWidthQuery.coordinate]

def sourceQuery (c : List Bool) : List Bool := pair c (BinaryNat.normalize (word A N O W target c))

theorem sourceQuery_FP (hA : UnaryFn A) (hN : UnaryFn N) (hO : UnaryFn O) (hW : UnaryFn W) (ht : target ∈ FP) :
    sourceQuery A N O W target ∈ FP :=
  mem_FP_pair id_mem_FP (mem_FP_comp (word_FP A N O W target hA hN hO hW ht) BinaryNat.normalize_mem_FP)

noncomputable def value (reader : List Bool → List Bool) (c : List Bool) : List Bool :=
  if Supported A N O W target c then reader (sourceQuery A N O W target c) else []

theorem evaluator {reader : List Bool → List Bool} (E : SpaceFunction reader)
    (hA : UnaryFn A) (hN : UnaryFn N) (hO : UnaryFn O) (hW : UnaryFn W) (ht : target ∈ FP) :
    SpaceFunction (value A N O W target reader) := by
  have H := SpaceFunction.branch (fun c => decide (Supported A N O W target c))
    (supported_FP A N O W target hA hN hO hW ht).flag_mem_FP
    (E.precompose _ (sourceQuery_FP A N O W target hA hN hO hW ht))
    (SpaceFunction.ofFP _ (constFn_mem_FP []))
  exact H.congr (funext fun _ => by simp only [value, Function.comp_apply, decide_eq_true_eq])

theorem entry_bits (w : ℕ) (bits : List Bool) (i : ℕ) :
    entry w (Nat.fromBitsLE bits) i = Nat.fromBitsLE ((bits.drop (i * w)).take w) := by
  rw [entry_eq_digit, BinaryNat.value_take, drop_value]

theorem exponent_word (c : List Bool) (hfit : O c + A c ≤ N c) :
    nativeExponent (Equiv.refl (Fin (A c))) (W c) (Nat.fromBitsLE (word A N O W target c)) =
      BlockRenameCoefficient.restrict (A c) (N c) (O c) hfit
        (nativeExponent (Equiv.refl (Fin (N c))) (W c) (Nat.fromBitsLE (target c))) := by
  ext i
  simp only [nativeExponent, BlockRenameCoefficient.restrict, Finsupp.coe_equivFunOnFinite_symm,
    Equiv.refl_apply, BlockRenameCoefficient.shift, entry_bits]
  have hi : O c + i.val < N c := by have := i.isLt; omega
  simpa only [FixedWidthQuery.entry, ite_eq_left hi, FixedWidthQuery.coordinate] using
    word_coordinate A N O W target c i.val i.isLt

theorem supported_iff (c : List Bool) :
    BlockRenameCoefficient.Supported (A c) (N c) (O c)
      (nativeExponent (Equiv.refl (Fin (N c))) (W c) (Nat.fromBitsLE (target c))) ↔
        Supported A N O W target c := by
  simp only [BlockRenameCoefficient.Supported, nativeExponent, Finsupp.coe_equivFunOnFinite_symm,
    Equiv.refl_apply, entry_bits, Supported, FixedWidthQuery.coordinate, Fin.forall_iff]

theorem packet {a n o : ℕ} (p : MvPolynomial (Fin a) ℤ) (hfit : o + a ≤ n)
    (reader : List Bool → List Bool) (c : List Bool) (m : ℕ)
    (ha : A c = a) (hn : N c = n) (ho : O c = o)
    (hr : ∀ r, reader (pair c (BinaryNatCode.encode r)) = residueBits
      ((p.coeff (nativeExponent (Equiv.refl (Fin a)) (W c) r) : ℤ) : ZMod m)) :
    value A N O W target reader c = residueBits
      (((MvPolynomial.rename (BlockRenameCoefficient.shift a n o hfit) p).coeff
        (nativeExponent (Equiv.refl (Fin n)) (W c) (Nat.fromBitsLE (target c))) : ℤ) : ZMod m) := by
  subst a
  subst n
  subst o
  rw [value, BlockRenameCoefficient.coefficient]
  by_cases hs : Supported A N O W target c
  · rw [ite_eq_left hs, ite_eq_left ((supported_iff A N O W target c).mpr hs), sourceQuery,
      BinaryNat.normalize_eq_bits]
    change reader (pair c (BinaryNatCode.encode (Nat.fromBitsLE (word A N O W target c)))) = _
    rw [hr, exponent_word A N O W target c hfit]
  · rw [ite_eq_right hs, ite_eq_right (fun h => hs ((supported_iff A N O W target c).mp h))]
    simp only [Int.cast_zero, residueBits, ZMod.val_zero, BinaryNatCode.encode]
    rfl

end LeanCanny.Algebra.FixedWidthBlockRenameBits
