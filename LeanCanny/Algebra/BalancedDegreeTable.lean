/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.BalancedCanonicalDegrees
public import LeanCanny.Algebra.BalancedMetadataAddress
public import LeanCanny.Encoding.FixedWidthNatVectorSpace

/-! # Preparing canonical degree entries of the balanced metadata table

All degrees of the padded finite-annihilator tree are computed from the
original leaf reader and serialized in polynomial space. The frame uses the
existing metadata layout. Direction cells start at zero; selecting consistent
separating directions and connecting padded source readers remain separate.
-/

@[expose] public section

namespace LeanCanny.Algebra.BalancedDegreeTable
open Polynomial
open LeanCanny.Encoding LeanCanny.Computation
open SeparableBits (Family Readers)
open BalancedParameterContext (packet original)
open scoped Classical

noncomputable def value (B : Family) (count : List Bool → ℕ) (c : List Bool) (r : ℕ) : ℕ :=
  if (BinaryNatCode.encode r)[0]?.getD false then 0
  else BalancedCanonicalDegrees.degree B count (BalancedMetadataAddress.query (pair c (BinaryNatCode.encode r)))

noncomputable def read (B : Family) (count : List Bool → ℕ) (p : List Bool) : List Bool :=
  if (pairSnd p)[0]?.getD false then []
  else BinaryNatCode.encode (BalancedCanonicalDegrees.degree B count (BalancedMetadataAddress.query p))

theorem read_packet (B : Family) (count : List Bool → ℕ) (c : List Bool) (r : ℕ) :
    read B count (pair c (BinaryNatCode.encode r)) = BinaryNatCode.encode (value B count c r) := by
  simp only [read, value, pairSnd_pair]
  split_ifs <;> rfl

theorem readEvaluator (B : Family) (A : Readers B) (hne : ∀ c, B.polynomial c ≠ 0)
    (count D : List Bool → ℕ) (hn : UnaryFn count) (hD : BinaryFn D)
    (hdegree : ∀ c i, i < count c → (B.polynomial (pair c (BinaryNatCode.encode i))).natDegree ≤ D c) :
    SpaceFunction (read B count) := by
  have E := (BalancedCanonicalDegrees.evaluator B A hne count D hn hD hdegree).precompose
    BalancedMetadataAddress.query BalancedMetadataAddress.query_FP
  have R := SpaceFunction.branch (fun p => (pairSnd p)[0]?.getD false)
    (getBit_mem_FP pairSnd_mem_FP (UnaryFn.const 0)) (SpaceFunction.ofFP _ (constFn_mem_FP [])) E
  exact R.congr (funext fun p => by simp only [read, Function.comp_apply])

def budget (count D : List Bool → ℕ) (c : List Bool) : ℕ := (D c + 1) ^ BalancedCanonicalDegrees.maxLeaves count c
def width (count D : List Bool → ℕ) (c : List Bool) : ℕ := 2 * (budget count D c).size + 1

theorem budget_binary {count D : List Bool → ℕ} (hn : UnaryFn count) (hD : BinaryFn D) : BinaryFn (budget count D) :=
  (hD.add (BinaryFn.const 1)).powUnary (BalancedCanonicalDegrees.maxLeaves_unary hn)

theorem width_unary {count D : List Bool → ℕ} (hn : UnaryFn count) (hD : BinaryFn D) : UnaryFn (width count D) := by
  have h : UnaryFn (fun c => (budget count D c).size) :=
    (UnaryFn.length (budget_binary hn hD).bits_mem_FP).of_eq (fun c => Nat.size_eq_bits_len _)
  exact ((UnaryFn.const 2).mul h).add (UnaryFn.const 1)

theorem width_pos (count D : List Bool → ℕ) (c : List Bool) : 0 < width count D c := by unfold width; omega

theorem value_bound (B : Family) (count D : List Bool → ℕ) (hne : ∀ c, B.polynomial c ≠ 0)
    (hdegree : ∀ c i, i < count c → (B.polynomial (pair c (BinaryNatCode.encode i))).natDegree ≤ D c)
    (c : List Bool) (r : ℕ) : value B count c r ≤ budget count D c := by
  unfold value
  split_ifs
  · exact Nat.zero_le _
  · have hb := BalancedCanonicalDegrees.product_bound B count D hne hdegree
      (original (BalancedMetadataAddress.query (pair c (BinaryNatCode.encode r))))
      (BalancedCanonicalDegrees.width count (BalancedMetadataAddress.query (pair c (BinaryNatCode.encode r))) *
        BalancedParameterContext.index (BalancedMetadataAddress.query (pair c (BinaryNatCode.encode r))))
      (BalancedCanonicalDegrees.width count (BalancedMetadataAddress.query (pair c (BinaryNatCode.encode r))))
    have hw := BalancedCanonicalDegrees.width_le count (BalancedMetadataAddress.query (pair c (BinaryNatCode.encode r)))
    have h := hb.trans (Nat.pow_le_pow_right (by omega) hw)
    simpa only [BalancedCanonicalDegrees.degree, BalancedMetadataAddress.query, original, pairFst_pair, budget] using h

theorem value_fits (B : Family) (count D : List Bool → ℕ) (hne : ∀ c, B.polynomial c ≠ 0)
    (hdegree : ∀ c i, i < count c → (B.polynomial (pair c (BinaryNatCode.encode i))).natDegree ≤ D c)
    (c : List Bool) (r : ℕ) : value B count c r < 2 ^ width count D c :=
  (value_bound B count D hne hdegree c r).trans_lt
    ((Nat.lt_size_self _).trans_le (Nat.pow_le_pow_right (by decide) (by unfold width; omega)))

noncomputable def prepare (B : Family) (count D : List Bool → ℕ) (c : List Bool) : List Bool :=
  BalancedMetadataTable.frame c (BalancedMetadataTable.capacity (count c)) (width count D c) (value B count c)

theorem prepare_length (B : Family) (count D : List Bool → ℕ) (c : List Bool) :
    (prepare B count D c).length = 2 * c.length + 2 * width count D c +
      BalancedMetadataTable.capacity (count c) * width count D c + 4 :=
  BalancedMetadataTable.frame_length _ _ _ _

theorem prepareEvaluator (B : Family) (A : Readers B) (hne : ∀ c, B.polynomial c ≠ 0)
    (count D : List Bool → ℕ) (hn : UnaryFn count) (hD : BinaryFn D)
    (hdegree : ∀ c i, i < count c → (B.polynomial (pair c (BinaryNatCode.encode i))).natDegree ≤ D c) :
    SpaceFunction (prepare B count D) := by
  have hw := width_unary hn hD
  have E := FixedWidthNatVector.encodeEvaluator
    (fun c => BalancedMetadataTable.capacity (count c)) (width count D) (value B count)
    (BalancedMetadataTable.capacity_unary hn) hw (read B count) (readEvaluator B A hne count D hn hD hdegree) (read_packet B count)
  have hf := mem_FP_pair pairFst_mem_FP (mem_FP_pair (hw.lift.replicate_mem_FP true) pairSnd_mem_FP)
  have R := E.withInput.postcompose
    (fun p => pair (pairFst p) (pair (List.replicate (width count D (pairFst p)) true) (pairSnd p))) hf
  exact R.congr (funext fun c => by simp only [prepare, BalancedMetadataTable.frame, Function.comp_apply, pairFst_pair, pairSnd_pair])

theorem value_cell (B : Family) (count : List Bool → ℕ) (hne : ∀ c, B.polynomial c ≠ 0)
    (which : Bool) (c : List Bool) (h i : ℕ) (hh : h ≤ (count c).size) :
    value B count c (2 * BalancedMetadataTable.key h i + if which then 1 else 0) =
      if which then 0 else (BalancedPrimitiveTree.node (BalancedCanonicalDegrees.leaves B count hne c) h i).polynomial.natDegree := by
  unfold value
  rw [BalancedMetadataAddress.query_cell]
  simp only [BinaryNatCode.encode, BalancedMetadataAddress.cell_bits, List.getElem?_cons_zero, Option.getD_some]
  cases which with
  | true => rfl
  | false => exact BalancedCanonicalDegrees.degree_packet B count hne c h i hh

theorem prepared_fields (B : Family) (count D : List Bool → ℕ) (hne : ∀ c, B.polynomial c ≠ 0)
    (hdegree : ∀ c i, i < count c → (B.polynomial (pair c (BinaryNatCode.encode i))).natDegree ≤ D c)
    (which : Bool) (c : List Bool) (h i : ℕ) (hh : h ≤ (count c).size) (hi : i < 2 ^ ((count c).size - h)) :
    Nat.fromBitsLE (BalancedMetadataTable.read which (packet (prepare B count D c) h i)) =
      if which then 0 else (BalancedPrimitiveTree.node (BalancedCanonicalDegrees.leaves B count hne c) h i).polynomial.natDegree := by
  unfold prepare
  rw [BalancedMetadataTable.read_frame which c _ _ h i _ (width_pos count D c)
    (BalancedMetadataTable.cell_lt_capacity which (count c) h i hh hi)
    (value_fits B count D hne hdegree c _)]
  simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]
  exact value_cell B count hne which c h i hh

theorem prepared_order (B : Family) (count D : List Bool → ℕ) (hne : ∀ c, B.polynomial c ≠ 0)
    (hdegree : ∀ c i, i < count c → (B.polynomial (pair c (BinaryNatCode.encode i))).natDegree ≤ D c)
    (c : List Bool) (h i : ℕ) (hh : h ≤ (count c).size) (hi : i < 2 ^ ((count c).size - h)) :
    BalancedMetadataTable.order (packet (prepare B count D c) h i) =
      (BalancedPrimitiveTree.node (BalancedCanonicalDegrees.leaves B count hne c) h i).polynomial.natDegree :=
  prepared_fields B count D hne hdegree false c h i hh hi

theorem prepared_direction (B : Family) (count D : List Bool → ℕ) (hne : ∀ c, B.polynomial c ≠ 0)
    (hdegree : ∀ c i, i < count c → (B.polynomial (pair c (BinaryNatCode.encode i))).natDegree ≤ D c)
    (c : List Bool) (h i : ℕ) (hh : h ≤ (count c).size) (hi : i < 2 ^ ((count c).size - h)) :
    BalancedMetadataTable.direction (packet (prepare B count D c) h i) = 0 :=
  prepared_fields B count D hne hdegree true c h i hh hi

/-- The same width can hold the separating directions filled in later. -/
theorem direction_fits (B : Family) (count D : List Bool → ℕ) (hne : ∀ c, B.polynomial c ≠ 0)
    (hdegree : ∀ c i, i < count c → (B.polynomial (pair c (BinaryNatCode.encode i))).natDegree ≤ D c)
    (c : List Bool) (h i : ℕ) (hh : h + 1 ≤ (count c).size) :
    PrimitivePair.select
      (BalancedPrimitiveTree.node (BalancedCanonicalDegrees.leaves B count hne c) h (2 * i)).polynomial
      (BalancedPrimitiveTree.node (BalancedCanonicalDegrees.leaves B count hne c) h (2 * i + 1)).polynomial < 2 ^ width count D c := by
  let L := BalancedPrimitiveTree.node (BalancedCanonicalDegrees.leaves B count hne c) h (2 * i)
  let R := BalancedPrimitiveTree.node (BalancedCanonicalDegrees.leaves B count hne c) h (2 * i + 1)
  have hd : (BalancedPrimitiveTree.node (BalancedCanonicalDegrees.leaves B count hne c) (h + 1) i).polynomial.natDegree ≤
      budget count D c := by
    have he : value B count c (2 * BalancedMetadataTable.key (h + 1) i) =
        (BalancedPrimitiveTree.node (BalancedCanonicalDegrees.leaves B count hne c) (h + 1) i).polynomial.natDegree := by
      simpa only [Bool.false_eq_true, ite_false, Nat.add_zero] using value_cell B count hne false c (h + 1) i hh
    rw [← he]
    exact value_bound B count D hne hdegree c _
  rw [BalancedPrimitiveTree.node, SeparableIntegerPolynomial.combine_degree] at hd
  have hs := (PrimitivePair.select_spec L.polynomial R.polynomial
    (L.separable_in_field (L := AlgebraicClosure ℚ)) (R.separable_in_field (L := AlgebraicClosure ℚ))
    (IsAlgClosed.splits _) (IsAlgClosed.splits _)).1
  have hb : PrimitivePair.select L.polynomial R.polynomial ≤ (budget count D c) ^ 2 :=
    hs.trans (Nat.pow_le_pow_left hd 2)
  have ht : (budget count D c) ^ 2 < 2 ^ (2 * (budget count D c).size) := by
    simpa only [← pow_mul, Nat.mul_comm] using Nat.pow_lt_pow_left (Nat.lt_size_self (budget count D c)) (by decide : 2 ≠ 0)
  exact hb.trans_lt (ht.trans_le (Nat.pow_le_pow_right (by decide) (by unfold width; omega)))

theorem prepared_source (B : Family) (count D : List Bool → ℕ) (c : List Bool) :
    BalancedMetadataTable.source (prepare B count D c) = c := BalancedMetadataTable.source_frame _ _ _ _

end LeanCanny.Algebra.BalancedDegreeTable
