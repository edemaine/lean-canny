/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatFullSourceSampleRecordSpan
public import LeanCanny.Algebra.SymmetricRankTrailing
public import LeanCanny.Algebra.SignedIntegerResidue
public import LeanCanny.Algebra.CharacteristicIntegerBounds
public import LeanCanny.Algebra.IntegerMatrixTrailingSpace

/-! # Native ranks of regular flat sign row prefixes

The prefix is a binary input field. Masking unused rows preserves a fixed
exponential matrix dimension with native entry access. Characteristic scans
compute its nullity and hence the rank of the actual row prefix.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatFullSourceSamplePrefixRank
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter
open Brackets MatrixPower Berkowitz
open FlatFullSourceTower (Inputs)
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] FlatFullSourceSampleRecords.length FlatFullSourceSampleThom.labelWidth
  FlatFullSourceSampleCoordinates.parameterDegree FlatFullSourceSampleCoordinates.baseHeight
  FlatFullSourceSampleQueries.roots FlatFullSourceSampleRegularCount.count

noncomputable abbrev dimension (P : Inputs) (q : List Bool) : ℕ := 2 ^ FlatFullSourceSampleRecords.length P (pairFst q)
noncomputable def bits (P : Inputs) (q : List Bool) : ℕ := FlatFullSourceSampleThom.labelWidth P (pairFst q)
noncomputable def budget (P : Inputs) (q : List Bool) : ℕ := CharacteristicIntegerBounds.budget (dimension P q) (bits P q)

theorem dimension_binary {P : Inputs} (h : P.Access) : BinaryFn (dimension P) :=
  (FlatFullSourceSampleRecordSpan.dimension_binary h).comp pairFst_mem_FP
theorem bits_binary {P : Inputs} (h : P.Access) : BinaryFn (bits P) :=
  BinaryFn.ofUnary ((FlatFullSourceSampleThom.labelWidth_unary h).comp pairFst_mem_FP)
theorem budget_binary {P : Inputs} (h : P.Access) : BinaryFn (budget P) :=
  CharacteristicIntegerBounds.budget_binary (dimension_binary h) (bits_binary h)

def query (t : List Bool) : List Bool := pair (pairFst (pairFst t)) (pairSnd t)
theorem query_FP : query ∈ FP := mem_FP_pair (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairSnd_mem_FP
def valid (t : List Bool) : Prop :=
  Nat.fromBitsLE (pairFst (pairSnd t)) < Nat.fromBitsLE (pairSnd (pairFst t)) ∧
    Nat.fromBitsLE (pairSnd (pairSnd t)) < Nat.fromBitsLE (pairSnd (pairFst t))
theorem valid_FP : FPPred valid := by
  have hi := BinaryFn.fromBits (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP)
  have hj := BinaryFn.fromBits (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP)
  have hk := BinaryFn.fromBits (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP)
  exact (hi.lt hk).and (hj.lt hk)

noncomputable def entry (P : Inputs) (t : List Bool) : ℤ :=
  if valid t then FlatFullSourceSampleRecordSpan.entry P (query t) else 0

theorem entry_evaluator {P : Inputs} (h : P.Access) :
    SpaceFunction (fun t => SignStatisticBits.integerCode (entry P t)) := by
  have E := (FlatFullSourceSampleRecordSpan.entry_evaluator h).precompose query query_FP
  have R := SpaceFunction.branch _ valid_FP.flag_mem_FP E (SpaceFunction.ofFP _ (constFn_mem_FP (SignStatisticBits.integerCode 0)))
  exact R.congr (funext fun t => by by_cases hv : valid t <;> simp [entry, hv])

theorem entry_bound (P : Inputs) (t : List Bool) : (entry P t).natAbs ≤ 2 ^ bits P (pairFst t) := by
  have hb := FlatFullSourceSampleRecordSpan.entry_bounds P (query t)
  rw [query, pairFst_pair] at hb
  have hm : (FlatFullSourceSampleRecordSpan.entry P (query t)).natAbs ≤
      2 ^ FlatFullSourceSampleThom.labelWidth P (pairFst (pairFst t)) := by
    have hc : ((FlatFullSourceSampleRecordSpan.entry P (query t)).natAbs : ℤ) ≤
        ((2 ^ FlatFullSourceSampleThom.labelWidth P (pairFst (pairFst t)) : ℕ) : ℤ) := by
      rw [Int.natCast_natAbs]
      exact abs_le.mpr hb
    exact_mod_cast hc
  unfold entry
  split_ifs
  · exact hm
  · exact Nat.zero_le _

noncomputable def matrix (P : Inputs) (q : List Bool) : Matrix (Fin (dimension P q)) (Fin (dimension P q)) ℤ :=
  Matrix.of (fun i j => entry P (pair q (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))))

theorem matrix_bound (P : Inputs) (q : List Bool) (i j : Fin (dimension P q)) :
    (matrix P q i j).natAbs ≤ 2 ^ bits P q := by
  have h := entry_bound P (pair q (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))
  rw [pairFst_pair] at h
  exact h

noncomputable def family (P : Inputs) : IntegerFamily where
  dimension := dimension P
  matrix := matrix P
  budget := budget P
  determinant_bits q := by
    have h := IntegerModular.det_natAbs_size_le_uniform (matrix P q) (bits P q) (matrix_bound P q)
    apply h.trans
    unfold budget CharacteristicIntegerBounds.budget
    rw [Nat.mul_add, Nat.mul_one]
    omega

noncomputable def rows (P : Inputs) (q : List Bool) :
    Matrix (Fin (dimension P q)) (FlatFullSourceSampleRecordSpan.Root P (pairFst q)) ℚ :=
  Matrix.of (fun i x => if i.val < Nat.fromBitsLE (pairSnd q) then FlatFullSourceSampleRecordSpan.matrix P (pairFst q) i x else 0)
noncomputable def gram (P : Inputs) (q : List Bool) := rows P q * (rows P q).transpose

theorem cast_matrix (P : Inputs) (q : List Bool) : (matrix P q).map (Int.castRingHom ℚ) = gram P q := by
  ext i j
  by_cases hi : i.val < Nat.fromBitsLE (pairSnd q) <;> by_cases hj : j.val < Nat.fromBitsLE (pairSnd q)
  · have he := FlatFullSourceSampleRecordSpan.entry_packet P (pairFst q) i j
    rw [FlatFullSourceSampleRecordSpan.gram, Matrix.mul_apply] at he
    simpa only [matrix, Matrix.of_apply, entry, valid, query, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits,
      hi, hj, and_self, ite_true, Matrix.map_apply, gram, Matrix.mul_apply, Matrix.transpose_apply, rows,
      Int.coe_castRingHom] using he
  all_goals simp only [matrix, Matrix.of_apply, entry, valid, query, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits,
    hi, hj, false_and, and_false, ite_false, Matrix.map_apply, Int.coe_castRingHom, Int.cast_zero,
    gram, Matrix.mul_apply, Matrix.transpose_apply, rows, zero_mul, mul_zero, Finset.sum_const_zero]

theorem gram_symmetric (P : Inputs) (q : List Bool) : (gram P q).IsSymm := by
  simp only [gram, Matrix.IsSymm, Matrix.transpose_mul, Matrix.transpose_transpose]

theorem trailing_cast (p : Polynomial ℤ) : (p.map (Int.castRingHom ℚ)).natTrailingDegree = p.natTrailingDegree := by
  by_cases hp : p = 0
  · simp [hp]
  · have hm : p.map (Int.castRingHom ℚ) ≠ 0 := (Polynomial.map_ne_zero_iff Int.cast_injective).mpr hp
    rw [Polynomial.natTrailingDegree_eq_support_min' hm, Polynomial.natTrailingDegree_eq_support_min' hp]
    simp only [Polynomial.support_map_of_injective p (f := Int.castRingHom ℚ) Int.cast_injective]

theorem rank_eq (P : Inputs) (q : List Bool) :
    (gram P q).rank = dimension P q - (matrix P q).charpoly.natTrailingDegree := by
  rw [SymmetricRankTrailing.rank_eq_sub_trailing _ (gram_symmetric P q), Fintype.card_fin,
    ← cast_matrix, Matrix.charpoly_map, trailing_cast]

def residueQuery (p : List Bool) : List Bool := pair (pair (pairFst (pairFst p)) (pairSnd p)) (pairSnd (pairFst p))
theorem residueQuery_FP : residueQuery ∈ FP :=
  mem_FP_pair (mem_FP_pair (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairSnd_mem_FP)
    (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP)

noncomputable def residueValue (P : Inputs) (q : List Bool) : List Bool :=
  residueBits (entry P (pairFst q) : ZMod (Nat.fromBitsLE (pairSnd q) + 1))
theorem residueValue_packet (P : Inputs) (c m : List Bool) :
    residueValue P (pair c m) = residueBits (entry P c : ZMod (Nat.fromBitsLE m + 1)) := by
  generalize hq : pair c m = q
  have hc : pairFst q = c := by rw [← hq, pairFst_pair]
  have hm : pairSnd q = m := by rw [← hq, pairSnd_pair]
  subst c
  subst m
  rfl

noncomputable def coefficient (P : Inputs) : List Bool → List Bool := residueValue P ∘ residueQuery
attribute [local irreducible] residueValue coefficient

theorem coefficient_evaluator {P : Inputs} (h : P.Access) : SpaceFunction (coefficient P) := by
  have E := (entry_evaluator h).precompose pairFst pairFst_mem_FP
  have R := SignedIntegerResidue.evaluator (z := fun q => entry P (pairFst q)) E pairSnd_mem_FP
  unfold coefficient residueValue
  exact R.precompose residueQuery residueQuery_FP

theorem coefficient_packet (P : Inputs) (q : List Bool) (i j : Fin (dimension P (pairFst q))) :
    coefficient P (pair q (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) =
      residueBits ((matrix P (pairFst q) i j : ℤ) : ZMod (Nat.fromBitsLE (pairSnd q) + 1)) := by
  have hq : residueQuery (pair q (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) =
      pair (pair (pairFst q) (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) (pairSnd q) := by
    simp only [residueQuery, pairFst_pair, pairSnd_pair]
  rw [coefficient, Function.comp_apply, hq, residueValue_packet]
  rfl

noncomputable def access (P : Inputs) : IntegerAccess (family P) where
  dimension q := BinaryNatCode.encode (dimension P q)
  budget q := BinaryNatCode.encode (budget P q)
  entry := coefficient P
  dimension_eq _ := rfl
  budget_eq _ := rfl
  entry_eq := coefficient_packet P

attribute [local irreducible] matrix budget bits

theorem controls {P : Inputs} (h : P.Access) : (access P).ControlsPolyTime := by
  have hN := BinaryFn.bits_mem_FP (dimension_binary h)
  have hB := BinaryFn.bits_mem_FP (budget_binary h)
  constructor
  · change (fun q => BinaryNatCode.encode (dimension P q)) ∈ FP
    exact hN
  · change (fun q => BinaryNatCode.encode (budget P q)) ∈ FP
    exact hB

noncomputable def trailing (P : Inputs) (q : List Bool) : List Bool :=
  BinaryNatCode.encode (matrix P q).charpoly.natTrailingDegree

theorem trailing_evaluator {P : Inputs} (h : P.Access) : SpaceFunction (trailing P) := by
  have hC : ∀ q k, (((family P).matrix q).charpoly.coeff k).natAbs.size ≤ budget P q := by
    intro q k
    change ((matrix P q).charpoly.coeff k).natAbs.size ≤ budget P q
    unfold budget
    exact CharacteristicIntegerBounds.coefficient_bits (matrix P q) (bits P q) (matrix_bound P q) k
  have E := IntegerMatrixTrailingBits.evaluator (access P) (controls h) (coefficient_evaluator h)
    (budget_binary h) hC
  exact E

noncomputable def rank (P : Inputs) (q : List Bool) : ℕ := (gram P q).rank

noncomputable def finish (P : Inputs) (z : List Bool) : List Bool :=
  BinaryNat.sub (pair (BinaryNatCode.encode (dimension P (pairFst z))) (pairSnd z))
theorem finish_FP {P : Inputs} (h : P.Access) : finish P ∈ FP := by
  have hN := BinaryFn.bits_mem_FP ((dimension_binary h).comp pairFst_mem_FP)
  have H := mem_FP_comp (mem_FP_pair hN pairSnd_mem_FP) BinaryNat.sub_mem_FP
  exact mem_FP_of_eq H (fun _ => by simp only [finish, Function.comp_apply])

attribute [local irreducible] rank trailing finish

theorem evaluator {P : Inputs} (h : P.Access) :
    SpaceFunction (fun q => BinaryNatCode.encode (rank P q)) := by
  have E := (trailing_evaluator h).withInput
  have R := E.postcompose (finish P) (finish_FP h)
  apply R.congr
  funext q
  simp only [Function.comp_apply, finish, pairFst_pair, pairSnd_pair, trailing, BinaryNat.sub_pair, BinaryNatCode.encode,
    Nat.fromBitsLE_bits, rank, rank_eq]

noncomputable def prefixRows (P : Inputs) (c : List Bool) (k : ℕ) :
    Matrix (FlatFullSourceSampleRecordSpan.Index P c) (FlatFullSourceSampleRecordSpan.Root P c) ℚ :=
  Matrix.of (fun i x => if i.val < k then FlatFullSourceSampleRecordSpan.matrix P c i x else 0)
noncomputable def prefixRank (P : Inputs) (c : List Bool) (k : ℕ) : ℕ :=
  (prefixRows P c k * (prefixRows P c k).transpose).rank

theorem rank_as_prefix (P : Inputs) (q : List Bool) :
    rank P q = prefixRank P (pairFst q) (Nat.fromBitsLE (pairSnd q)) := by
  unfold rank gram rows prefixRank prefixRows
  rfl
theorem rank_packet (P : Inputs) (c : List Bool) (k : ℕ) :
    rank P (pair c (BinaryNatCode.encode k)) = prefixRank P c k := by
  rw [rank_as_prefix, pairFst_pair, pairSnd_pair]
  exact congrArg (prefixRank P c) (Nat.fromBitsLE_bits k)

theorem prefixRank_zero (P : Inputs) (c : List Bool) : prefixRank P c 0 = 0 := by
  have he : prefixRows P c 0 = 0 := by ext i x; simp [prefixRows]
  simp only [prefixRank, he, Matrix.zero_mul, Matrix.rank_zero]

theorem prefixRank_full (P : Inputs) (c : List Bool) (k : ℕ)
    (hk : 2 ^ FlatFullSourceSampleRecords.length P c ≤ k) :
    prefixRank P c k = FlatFullSourceSampleRegularCount.count P c := by
  have he : prefixRows P c k = FlatFullSourceSampleRecordSpan.matrix P c := by
    ext i x
    exact ite_eq_left (i.isLt.trans_le hk)
  rw [prefixRank, he]
  exact FlatFullSourceSampleRecordSpan.rank_gram P c

theorem prefixRank_mono (P : Inputs) (c : List Bool) : Monotone (prefixRank P c) := by
  intro k l hkl
  unfold prefixRank
  rw [Matrix.rank_self_mul_transpose, Matrix.rank_self_mul_transpose,
    Matrix.rank_eq_finrank_span_row, Matrix.rank_eq_finrank_span_row]
  apply Submodule.finrank_mono
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  by_cases hi : i.val < k
  · have hl : i.val < l := hi.trans_le hkl
    have he : (prefixRows P c k).row i = (prefixRows P c l).row i := by
      ext x
      simp only [Matrix.row, prefixRows, Matrix.of_apply, hi, hl, ite_true]
    rw [he]
    exact Submodule.subset_span ⟨i, rfl⟩
  · have he : (prefixRows P c k).row i = 0 := by ext x; simp only [Matrix.row, prefixRows, Matrix.of_apply, hi, ite_false, Pi.zero_apply]
    rw [he]
    exact Submodule.zero_mem _

theorem prefixRank_le_count (P : Inputs) (c : List Bool) (k : ℕ) :
    prefixRank P c k ≤ FlatFullSourceSampleRegularCount.count P c := by
  have H := prefixRank_mono P c (Nat.le_add_right k (2 ^ FlatFullSourceSampleRecords.length P c))
  rw [prefixRank_full P c (k + 2 ^ FlatFullSourceSampleRecords.length P c) (by omega)] at H
  exact H

def successor (q : List Bool) : List Bool := pair (pairFst q) (BinaryNat.succ (pairSnd q))
theorem successor_FP : successor ∈ FP := by
  have H := mem_FP_pair pairFst_mem_FP (mem_FP_comp pairSnd_mem_FP BinaryNat.succ_mem_FP)
  exact mem_FP_of_eq H (fun _ => by simp only [successor, Function.comp_apply])

noncomputable def gainLanguage (P : Inputs) : Language := {q |
  prefixRank P (pairFst q) (Nat.fromBitsLE (pairSnd q)) <
    prefixRank P (pairFst q) (Nat.fromBitsLE (pairSnd q) + 1)}

theorem gainDecider {P : Inputs} (h : P.Access) : SpaceDecider (gainLanguage P) := by
  have E := evaluator h
  have R := E.pairOutputs (E.precompose successor successor_FP)
  have hc := ((BinaryFn.fromBits pairFst_mem_FP).lt (BinaryFn.fromBits pairSnd_mem_FP)).flag_mem_FP
  apply R.decider (fun z => decide (Nat.fromBitsLE (pairFst z) < Nat.fromBitsLE (pairSnd z))) hc
  intro q
  simp only [gainLanguage, Set.mem_ofPred_eq, pairFst_pair, pairSnd_pair, Function.comp_apply,
    BinaryNatCode.encode, Nat.fromBitsLE_bits, decide_eq_true_eq, rank_as_prefix, successor,
    BinaryNat.succ_eq_bits]

end LeanCanny.Encoding.FlatFullSourceSamplePrefixRank
