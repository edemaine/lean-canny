/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedAlgebraicFiberRecordGram
public import LeanCanny.Algebra.SymmetricRankTrailing
public import LeanCanny.Algebra.SignedIntegerResidue
public import LeanCanny.Algebra.CharacteristicIntegerBounds
public import LeanCanny.Algebra.IntegerMatrixTrailingSpace

/-! # Native ranks of fiber-record row prefixes

Masking unused rows retains a fixed matrix dimension. Native characteristic
coefficient scans compute its nullity and hence the prefix rank. Every Gram
entry is recomputed from the original bivariate reader.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedAlgebraicFiberPrefixRank
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter BoundedAlgebraicSlice
open Brackets MatrixPower Berkowitz
open scoped Classical BigOperators

noncomputable abbrev dimension (F : Family) (q : List Bool) : ℕ := 2 ^ BoundedAlgebraicFiberRecords.length F (pairFst (pairFst q))
noncomputable def bits (F : Family) (q : List Bool) : ℕ := (F.degree (pairFst (pairFst q))).size
noncomputable def budget (F : Family) (q : List Bool) : ℕ := CharacteristicIntegerBounds.budget (dimension F q) (bits F q)
theorem dimension_binary {F : Family} (A : F.Access) : BinaryFn (dimension F) :=
  (BoundedAlgebraicFiberRecordSpan.dimension_binary A).comp pairFst_mem_FP
theorem bits_binary {F : Family} (A : F.Access) : BinaryFn (bits F) := by
  have hd : BinaryFn (fun q => F.degree (pairFst (pairFst q))) :=
    A.degree_binary.comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)
  exact hd.size
theorem budget_binary {F : Family} (A : F.Access) : BinaryFn (budget F) :=
  CharacteristicIntegerBounds.budget_binary (dimension_binary A) (bits_binary A)

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

noncomputable def entry (P : Readers) (F : Family) (t : List Bool) : ℤ :=
  if valid t then BoundedAlgebraicFiberRecordGram.entry P F (query t) else 0
theorem entry_evaluator {P : Readers} (h : P.PolyTime) {F : Family} (A : F.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (fun t => SignStatisticBits.integerCode (entry P F t)) := by
  have E := (BoundedAlgebraicFiberRecordGram.evaluator h A ha).precompose query query_FP
  have R := SpaceFunction.branch _ valid_FP.flag_mem_FP E (SpaceFunction.ofFP _ (constFn_mem_FP (SignStatisticBits.integerCode 0)))
  exact R.congr (funext fun t => by by_cases hv : valid t <;> simp [entry, hv])

theorem entry_bound (P : Readers) (F : Family) (t : List Bool) : (entry P F t).natAbs ≤ 2 ^ bits F (pairFst t) := by
  have H := BoundedAlgebraicFiberRecordGram.entry_bound P F (query t)
  simp only [query, pairFst_pair] at H
  have hd : (BoundedAlgebraicFiberRecordGram.entry P F (query t)).natAbs ≤ 2 ^ bits F (pairFst t) := by
    simpa only [query, bits] using H.trans (Nat.lt_size_self (F.degree (pairFst (pairFst (pairFst t))))).le
  unfold entry
  split_ifs
  · exact hd
  · exact Nat.zero_le _

noncomputable def matrix (P : Readers) (F : Family) (q : List Bool) : Matrix (Fin (dimension F q)) (Fin (dimension F q)) ℤ :=
  fun i j => entry P F (pair q (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))
theorem matrix_bound (P : Readers) (F : Family) (q : List Bool) (i j : Fin (dimension F q)) :
    (matrix P F q i j).natAbs ≤ 2 ^ bits F q := by
  have H := entry_bound P F (pair q (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))
  rw [pairFst_pair] at H
  exact H

noncomputable def family (P : Readers) (F : Family) : IntegerFamily where
  dimension := dimension F
  matrix := matrix P F
  budget := budget F
  determinant_bits q := by
    have H := IntegerModular.det_natAbs_size_le_uniform (matrix P F q) (bits F q) (matrix_bound P F q)
    apply H.trans
    unfold budget CharacteristicIntegerBounds.budget
    rw [Nat.mul_add, Nat.mul_one]
    omega

noncomputable def rows (P : Readers) (F : Family) (q : List Bool) :
    Matrix (Fin (dimension F q)) (BoundedAlgebraicFiberRecordSpan.Root P F (pairFst q)) ℚ :=
  fun i x => if i.val < Nat.fromBitsLE (pairSnd q) then BoundedAlgebraicFiberRecordSpan.matrix P F (pairFst q) i x else 0
noncomputable def gram (P : Readers) (F : Family) (q : List Bool) := rows P F q * (rows P F q).transpose

theorem cast_matrix (P : Readers) (F : Family) (q : List Bool) : (matrix P F q).map (Int.castRingHom ℚ) = gram P F q := by
  ext i j
  by_cases hi : i.val < Nat.fromBitsLE (pairSnd q) <;> by_cases hj : j.val < Nat.fromBitsLE (pairSnd q)
  · have he := BoundedAlgebraicFiberRecordGram.entry_packet P F (pairFst q) i j
    rw [BoundedAlgebraicFiberRecordSpan.gram, Matrix.mul_apply] at he
    simpa only [matrix, entry, valid, query, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits,
      hi, hj, and_self, ite_true, Matrix.map_apply, gram, Matrix.mul_apply, Matrix.transpose_apply, rows,
      Int.coe_castRingHom] using he
  all_goals simp only [matrix, entry, valid, query, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits,
    hi, hj, false_and, and_false, ite_false, Matrix.map_apply, Int.coe_castRingHom, Int.cast_zero,
    gram, Matrix.mul_apply, Matrix.transpose_apply, rows, zero_mul, mul_zero, Finset.sum_const_zero]

theorem gram_symmetric (P : Readers) (F : Family) (q : List Bool) : (gram P F q).IsSymm := by
  simp only [gram, Matrix.IsSymm, Matrix.transpose_mul, Matrix.transpose_transpose]
theorem rank_eq (P : Readers) (F : Family) (q : List Bool) :
    (gram P F q).rank = dimension F q - (matrix P F q).charpoly.natTrailingDegree := by
  rw [SymmetricRankTrailing.rank_eq_sub_trailing _ (gram_symmetric P F q), Fintype.card_fin,
    ← cast_matrix, Matrix.charpoly_map, BoundedProjectionPrefixRank.trailing_cast]

def residueQuery (p : List Bool) : List Bool := pair (pair (pairFst (pairFst p)) (pairSnd p)) (pairSnd (pairFst p))
theorem residueQuery_FP : residueQuery ∈ FP :=
  mem_FP_pair (mem_FP_pair (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairSnd_mem_FP)
    (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP)
noncomputable def residueValue (P : Readers) (F : Family) (q : List Bool) : List Bool :=
  residueBits (entry P F (pairFst q) : ZMod (Nat.fromBitsLE (pairSnd q) + 1))
theorem residueValue_packet (P : Readers) (F : Family) (c m : List Bool) :
    residueValue P F (pair c m) = residueBits (entry P F c : ZMod (Nat.fromBitsLE m + 1)) := by
  generalize hq : pair c m = q
  have hc : pairFst q = c := by rw [← hq, pairFst_pair]
  have hm : pairSnd q = m := by rw [← hq, pairSnd_pair]
  subst c
  subst m
  rfl

noncomputable def coefficient (P : Readers) (F : Family) : List Bool → List Bool := residueValue P F ∘ residueQuery
attribute [local irreducible] residueValue coefficient
theorem coefficient_evaluator {P : Readers} (h : P.PolyTime) {F : Family} (A : F.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (coefficient P F) := by
  have E := (entry_evaluator h A ha).precompose pairFst pairFst_mem_FP
  have R := SignedIntegerResidue.evaluator (z := fun q => entry P F (pairFst q)) E pairSnd_mem_FP
  unfold coefficient residueValue
  exact R.precompose residueQuery residueQuery_FP
theorem coefficient_packet (P : Readers) (F : Family) (q : List Bool) (i j : Fin (dimension F (pairFst q))) :
    coefficient P F (pair q (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) =
      residueBits ((matrix P F (pairFst q) i j : ℤ) : ZMod (Nat.fromBitsLE (pairSnd q) + 1)) := by
  have hq : residueQuery (pair q (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) =
      pair (pair (pairFst q) (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) (pairSnd q) := by
    simp only [residueQuery, pairFst_pair, pairSnd_pair]
  rw [coefficient, Function.comp_apply, hq, residueValue_packet]
  rfl

noncomputable def access (P : Readers) (F : Family) : IntegerAccess (family P F) where
  dimension q := BinaryNatCode.encode (dimension F q)
  budget q := BinaryNatCode.encode (budget F q)
  entry := coefficient P F
  dimension_eq _ := rfl
  budget_eq _ := rfl
  entry_eq := coefficient_packet P F
attribute [local irreducible] matrix budget bits

theorem controls (P : Readers) {F : Family} (A : F.Access) : (access P F).ControlsPolyTime := by
  have hN := (dimension_binary A).bits_mem_FP
  have hB := (budget_binary A).bits_mem_FP
  exact ⟨hN, hB⟩

noncomputable def trailing (P : Readers) (F : Family) (q : List Bool) : List Bool := BinaryNatCode.encode (matrix P F q).charpoly.natTrailingDegree
theorem trailing_evaluator {P : Readers} (h : P.PolyTime) {F : Family} (A : F.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (trailing P F) := by
  have hC : ∀ q k, (((family P F).matrix q).charpoly.coeff k).natAbs.size ≤ budget F q := by
    intro q k
    change ((matrix P F q).charpoly.coeff k).natAbs.size ≤ budget F q
    unfold budget
    exact CharacteristicIntegerBounds.coefficient_bits (matrix P F q) (bits F q) (matrix_bound P F q) k
  have E := IntegerMatrixTrailingBits.evaluator (access P F) (controls P A) (coefficient_evaluator h A ha) (budget_binary A) hC
  exact E

noncomputable def rank (P : Readers) (F : Family) (q : List Bool) : ℕ := (gram P F q).rank
noncomputable def finish (F : Family) (z : List Bool) : List Bool :=
  BinaryNat.sub (pair (BinaryNatCode.encode (dimension F (pairFst z))) (pairSnd z))
theorem finish_FP {F : Family} (A : F.Access) : finish F ∈ FP := by
  have hN := BinaryFn.bits_mem_FP ((dimension_binary A).comp pairFst_mem_FP)
  have H := mem_FP_comp (mem_FP_pair hN pairSnd_mem_FP) BinaryNat.sub_mem_FP
  exact mem_FP_of_eq H (fun _ => by simp only [finish, Function.comp_apply])
attribute [local irreducible] rank trailing finish

theorem evaluator {P : Readers} (h : P.PolyTime) {F : Family} (A : F.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (fun q => BinaryNatCode.encode (rank P F q)) := by
  have E := (trailing_evaluator h A ha).withInput.postcompose (finish F) (finish_FP A)
  apply E.congr
  funext q
  simp only [Function.comp_apply, finish, pairFst_pair, pairSnd_pair, trailing, BinaryNat.sub_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits, rank, rank_eq]

noncomputable def prefixRows (P : Readers) (F : Family) (u : List Bool) (k : ℕ) :
    Matrix (BoundedAlgebraicFiberRecordSpan.Index F u) (BoundedAlgebraicFiberRecordSpan.Root P F u) ℚ :=
  fun i x => if i.val < k then BoundedAlgebraicFiberRecordSpan.matrix P F u i x else 0
noncomputable def prefixRank (P : Readers) (F : Family) (u : List Bool) (k : ℕ) : ℕ :=
  (prefixRows P F u k * (prefixRows P F u k).transpose).rank
theorem rank_as_prefix (P : Readers) (F : Family) (q : List Bool) :
    rank P F q = prefixRank P F (pairFst q) (Nat.fromBitsLE (pairSnd q)) := by
  unfold rank gram rows prefixRank prefixRows
  rfl
theorem rank_packet (P : Readers) (F : Family) (u : List Bool) (k : ℕ) :
    rank P F (pair u (BinaryNatCode.encode k)) = prefixRank P F u k := by
  rw [rank_as_prefix, pairFst_pair, pairSnd_pair]
  exact congrArg (prefixRank P F u) (Nat.fromBitsLE_bits k)
theorem prefixRank_zero (P : Readers) (F : Family) (u : List Bool) : prefixRank P F u 0 = 0 := by
  have he : prefixRows P F u 0 = 0 := by ext i x; simp [prefixRows]
  simp only [prefixRank, he, Matrix.zero_mul, Matrix.rank_zero]
theorem prefixRank_full (P : Readers) (F : Family) (u : List Bool) (k : ℕ)
    (hk : 2 ^ BoundedAlgebraicFiberRecords.length F (pairFst u) ≤ k) : prefixRank P F u k = RootCount.count P F u := by
  have he : prefixRows P F u k = BoundedAlgebraicFiberRecordSpan.matrix P F u := by
    ext i x
    exact ite_eq_left (i.isLt.trans_le hk)
  rw [prefixRank, he]
  exact BoundedAlgebraicFiberRecordSpan.rank_gram P F u
theorem prefixRank_mono (P : Readers) (F : Family) (u : List Bool) : Monotone (prefixRank P F u) := by
  intro k l hkl
  unfold prefixRank
  rw [Matrix.rank_self_mul_transpose, Matrix.rank_self_mul_transpose, Matrix.rank_eq_finrank_span_row, Matrix.rank_eq_finrank_span_row]
  apply Submodule.finrank_mono
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  by_cases hi : i.val < k
  · have he : (prefixRows P F u k).row i = (prefixRows P F u l).row i := by
      ext x
      simp only [Matrix.row, prefixRows, hi, hi.trans_le hkl, ite_true]
    rw [he]
    exact Submodule.subset_span ⟨i, rfl⟩
  · have he : (prefixRows P F u k).row i = 0 := by ext x; simp only [Matrix.row, prefixRows, hi, ite_false, Pi.zero_apply]
    rw [he]
    exact Submodule.zero_mem _

theorem prefixRank_le_count (P : Readers) (F : Family) (u : List Bool) (k : ℕ) :
    prefixRank P F u k ≤ RootCount.count P F u := by
  have H := prefixRank_mono P F u (le_max_left k (2 ^ BoundedAlgebraicFiberRecords.length F (pairFst u)))
  rw [prefixRank_full P F u _ (le_max_right k _)] at H
  exact H

def successor (q : List Bool) : List Bool := pair (pairFst q) (BinaryNat.succ (pairSnd q))
theorem successor_FP : successor ∈ FP := by
  have H := mem_FP_pair pairFst_mem_FP (mem_FP_comp pairSnd_mem_FP BinaryNat.succ_mem_FP)
  exact mem_FP_of_eq H (fun _ => by simp only [successor, Function.comp_apply])
noncomputable def gainLanguage (P : Readers) (F : Family) : Language := {q |
  prefixRank P F (pairFst q) (Nat.fromBitsLE (pairSnd q)) < prefixRank P F (pairFst q) (Nat.fromBitsLE (pairSnd q) + 1)}
theorem gainDecider {P : Readers} (h : P.PolyTime) {F : Family} (A : F.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceDecider (gainLanguage P F) := by
  have E := evaluator h A ha
  have R := E.pairOutputs (E.precompose successor successor_FP)
  have hc := ((BinaryFn.fromBits pairFst_mem_FP).lt (BinaryFn.fromBits pairSnd_mem_FP)).flag_mem_FP
  apply R.decider (fun z => decide (Nat.fromBitsLE (pairFst z) < Nat.fromBitsLE (pairSnd z))) hc
  intro q
  simp only [gainLanguage, Set.mem_ofPred_eq, pairFst_pair, pairSnd_pair, Function.comp_apply,
    BinaryNatCode.encode, Nat.fromBitsLE_bits, decide_eq_true_eq, rank_as_prefix, successor, BinaryNat.succ_eq_bits]

end LeanCanny.Encoding.BoundedAlgebraicFiberPrefixRank
