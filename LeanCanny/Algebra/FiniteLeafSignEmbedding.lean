/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FiniteLeafSignSource

/-! # Rotating and extending streamed finite-variable constraints

Source variable zero moves to the last of the original positions, and each
positive source variable moves down one position. Further native positions
have exponent zero. The source coefficient, count, and budget readers remain
unchanged; the exponent reader computes the inverse index in binary.
-/

@[expose] public section
namespace LeanCanny.Algebra.FiniteLeafSignBits
open LeanCanny.Encoding LeanCanny.Computation
open RationalSubstitution
open scoped Classical BigOperators

/-- Inverse of the cyclic shift, used only at positions below `A`. -/
def inverseIndex (A i : ℕ) : ℕ := if i + 1 < A then i + 1 else 0

theorem inverseIndex_lt (A i : ℕ) (hi : i < A) : inverseIndex A i < A := by
  unfold inverseIndex
  split_ifs <;> omega

/-- Rotate the first `A` positions and include them among `N` positions. -/
def rotationEmbedding (A N : ℕ) (hAN : A ≤ N) : Fin A ↪ Fin N where
  toFun k := ⟨if k.val = 0 then A - 1 else k.val - 1, by
    have hk := k.isLt
    split_ifs <;> omega⟩
  inj' := by
    intro k l h
    apply Fin.ext
    have H := congrArg Fin.val h
    dsimp only at H
    split_ifs at H <;> omega

@[simp] theorem rotationEmbedding_val (A N : ℕ) (hAN : A ≤ N) (k : Fin A) :
    (rotationEmbedding A N hAN k).val = if k.val = 0 then A - 1 else k.val - 1 := rfl

theorem rotationEmbedding_lt (A N : ℕ) (hAN : A ≤ N) (k : Fin A) :
    (rotationEmbedding A N hAN k).val < A := by
  have hk := k.isLt
  change (if k.val = 0 then A - 1 else k.val - 1) < A
  split_ifs <;> omega

theorem inverseIndex_rotation (A N : ℕ) (hAN : A ≤ N) (k : Fin A) :
    inverseIndex A (rotationEmbedding A N hAN k).val = k.val := by
  have hk := k.isLt
  change inverseIndex A (if k.val = 0 then A - 1 else k.val - 1) = k.val
  unfold inverseIndex
  split_ifs <;> omega

theorem rotationEmbedding_inverse (A N : ℕ) (hAN : A ≤ N) (i : Fin N) (hi : i.val < A) :
    rotationEmbedding A N hAN ⟨inverseIndex A i.val, inverseIndex_lt A i.val hi⟩ = i := by
  apply Fin.ext
  change (if inverseIndex A i.val = 0 then A - 1 else inverseIndex A i.val - 1) = i.val
  by_cases h : i.val + 1 < A
  · have hx : inverseIndex A i.val = i.val + 1 := ite_eq_left h
    rw [hx, ite_eq_right (by omega : i.val + 1 ≠ 0)]
    omega
  · have hx : inverseIndex A i.val = 0 := ite_eq_right h
    rw [hx, ite_eq_left rfl]
    omega

noncomputable def Source.embed {arity : List Bool → ℕ} (S : Source arity)
    (N : List Bool → ℕ) : Source N where
  count := S.count
  terms := S.terms
  degree := S.degree
  height := S.height
  coefficient := S.coefficient
  exponent c j r i := if i < arity c then S.exponent c j r (inverseIndex (arity c) i) else 0
  pattern := S.pattern
  exponent_le c j r hr i _ := by
    split_ifs with hi
    · exact S.exponent_le c j r hr _ (inverseIndex_lt _ _ hi)
    · exact Nat.zero_le _
  coefficient_le := S.coefficient_le

private theorem exponentVector_embed (A N : ℕ) (hAN : A ≤ N) (e : ℕ → ℕ) :
    Indexed.exponentVector N (fun i => if i < A then e (inverseIndex A i) else 0) =
      (Indexed.exponentVector A e).mapDomain (rotationEmbedding A N hAN) := by
  rw [← Finsupp.embDomain_eq_mapDomain]
  ext i
  by_cases hi : i.val < A
  · let k : Fin A := ⟨inverseIndex A i.val, inverseIndex_lt A i.val hi⟩
    have he : rotationEmbedding A N hAN k = i := rotationEmbedding_inverse A N hAN i hi
    rw [← he, Finsupp.embDomain_apply_self]
    simp only [Indexed.exponentVector, Finsupp.coe_equivFunOnFinite_symm,
      rotationEmbedding_lt, ite_true, inverseIndex_rotation]
  · have hn : i ∉ Set.range (rotationEmbedding A N hAN) := by
      rintro ⟨k, rfl⟩
      exact hi (rotationEmbedding_lt A N hAN k)
    rw [Finsupp.embDomain_of_notMem_range _ _ _ hn]
    simp only [Indexed.exponentVector, Finsupp.coe_equivFunOnFinite_symm, hi, ite_false]

theorem Source.embed_polynomial {arity : List Bool → ℕ} (S : Source arity) (N : List Bool → ℕ)
    (c : List Bool) (j : ℕ) (hAN : arity c ≤ N c) :
    (S.embed N).polynomial c j = MvPolynomial.rename (rotationEmbedding (arity c) (N c) hAN) (S.polynomial c j) := by
  simp only [Source.polynomial, Indexed.source, Source.embed, map_sum, MvPolynomial.rename_monomial]
  apply Finset.sum_congr rfl
  intro r _
  rw [exponentVector_embed]

theorem Source.embed_eval {arity : List Bool → ℕ} (S : Source arity) (N : List Bool → ℕ)
    (c : List Bool) (j : ℕ) (hAN : arity c ≤ N c)
    {K : Type*} [CommSemiring K] (φ : ℤ →+* K) (z : Fin (N c) → K) :
    ((S.embed N).polynomial c j).eval₂ φ z =
      (S.polynomial c j).eval₂ φ (z ∘ rotationEmbedding (arity c) (N c) hAN) := by
  rw [Source.embed_polynomial S N c j hAN, MvPolynomial.eval₂_rename]

def variableWord (p : List Bool) : List Bool := pairSnd (pairSnd p)
def exponentContext (p : List Bool) : List Bool := pairFst (pairFst p)

theorem variableWord_FP : variableWord ∈ FP := mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP
theorem exponentContext_FP : exponentContext ∈ FP := mem_FP_comp pairFst_mem_FP pairFst_mem_FP

def validVariable (arity : List Bool → ℕ) (p : List Bool) : Prop :=
  Nat.fromBitsLE (variableWord p) < arity (exponentContext p)

theorem validVariable_pred {arity : List Bool → ℕ} (hA : UnaryFn arity) : FPPred (validVariable arity) :=
  (BinaryNat.lt_fppred variableWord_FP (mem_FP_comp exponentContext_FP (bits_mem_FP hA))).of_iff
    (fun p => by simp only [validVariable, Function.comp_apply, Nat.fromBitsLE_bits])

def inverseCode (arity : List Bool → ℕ) (p : List Bool) : List Bool :=
  if Nat.fromBitsLE (variableWord p) + 1 < arity (exponentContext p) then
    BinaryNat.succ (variableWord p) else []

theorem inverseCode_FP {arity : List Bool → ℕ} (hA : UnaryFn arity) : inverseCode arity ∈ FP := by
  have hs := mem_FP_comp variableWord_FP BinaryNat.succ_mem_FP
  have hp : FPPred (fun p => Nat.fromBitsLE (variableWord p) + 1 < arity (exponentContext p)) :=
    (BinaryNat.lt_fppred hs (mem_FP_comp exponentContext_FP (bits_mem_FP hA))).of_iff
    (fun p => by simp only [Function.comp_apply, BinaryNat.succ_eq_bits, Nat.fromBitsLE_bits])
  exact hp.ite_mem_FP hs (constFn_mem_FP [])

def exponentEmbeddingQuery (arity : List Bool → ℕ) (p : List Bool) : List Bool :=
  pair (pairFst p) (pair (pairFst (pairSnd p)) (inverseCode arity p))

theorem exponentEmbeddingQuery_FP {arity : List Bool → ℕ} (hA : UnaryFn arity) : exponentEmbeddingQuery arity ∈ FP :=
  mem_FP_pair pairFst_mem_FP (mem_FP_pair (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP) (inverseCode_FP hA))

theorem inverseCode_packet (arity : List Bool → ℕ) (q : List Bool) (r i : ℕ) :
    inverseCode arity (pair q (pair (BinaryNatCode.encode r) (BinaryNatCode.encode i))) =
      BinaryNatCode.encode (inverseIndex (arity (pairFst q)) i) := by
  simp only [inverseCode, variableWord, exponentContext, pairFst_pair, pairSnd_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits, BinaryNat.succ_eq_bits, inverseIndex]
  split_ifs <;> rfl

noncomputable def embeddedExponent {arity : List Bool → ℕ} {S : Source arity} (R : S.Access)
    (p : List Bool) : List Bool :=
  if validVariable arity p then R.exponent (exponentEmbeddingQuery arity p) else []

theorem embeddedExponent_FP {arity : List Bool → ℕ} {S : Source arity} (R : S.Access) (hA : UnaryFn arity) :
    embeddedExponent R ∈ FP :=
  (validVariable_pred hA).ite_mem_FP (mem_FP_comp (exponentEmbeddingQuery_FP hA) R.exponent_FP) (constFn_mem_FP [])

noncomputable def Source.Access.embed {arity : List Bool → ℕ} {S : Source arity} (R : S.Access)
    (N : List Bool → ℕ) (hA : UnaryFn arity) : (S.embed N).Access where
  coefficient := R.coefficient
  exponent := embeddedExponent R
  pattern := R.pattern
  count_unary := R.count_unary
  terms_binary := R.terms_binary
  degree_binary := R.degree_binary
  height_binary := R.height_binary
  coefficientEvaluator := R.coefficientEvaluator
  exponent_FP := embeddedExponent_FP R hA
  pattern_FP := R.pattern_FP
  coefficient_eq := R.coefficient_eq
  exponent_eq q r hr i _ := by
    simp only [embeddedExponent, validVariable, variableWord, exponentContext, pairFst_pair,
      pairSnd_pair, show Nat.fromBitsLE (BinaryNatCode.encode i) = i from Nat.fromBitsLE_bits i]
    by_cases hi : i < arity (pairFst q)
    · simp only [Source.embed, hi, ite_true, exponentEmbeddingQuery, inverseCode_packet, pairFst_pair, pairSnd_pair]
      exact R.exponent_eq q r hr _ (inverseIndex_lt _ _ hi)
    · simp only [Source.embed, hi, ite_false]
      rfl
  pattern_eq := R.pattern_eq

/-- Native forward index writer, on `pair context sourceIndex`. -/
def rotationCode (arity : List Bool → ℕ) (p : List Bool) : List Bool :=
  if Nat.fromBitsLE (pairSnd p) = 0 then
    BinaryNat.sub (pair (BinaryNatCode.encode (arity (pairFst p))) [true])
  else BinaryNat.sub (pair (pairSnd p) [true])

attribute [local irreducible] BinaryNat.sub

theorem rotationCode_FP {arity : List Bool → ℕ} (hA : UnaryFn arity) : rotationCode arity ∈ FP := by
  have hz : FPPred (fun p => Nat.fromBitsLE (pairSnd p) = 0) :=
    (BinaryNat.le_fppred pairSnd_mem_FP (constFn_mem_FP [])).of_iff (fun p => by
      change Nat.fromBitsLE (pairSnd p) ≤ 0 ↔ Nat.fromBitsLE (pairSnd p) = 0
      omega)
  have hl := mem_FP_comp (mem_FP_pair (mem_FP_comp pairFst_mem_FP (bits_mem_FP hA))
    (constFn_mem_FP [true])) BinaryNat.sub_mem_FP
  have hr := mem_FP_comp (mem_FP_pair pairSnd_mem_FP (constFn_mem_FP [true])) BinaryNat.sub_mem_FP
  exact hz.ite_mem_FP hl hr

theorem rotationCode_packet (arity N : List Bool → ℕ) (c : List Bool) (hAN : arity c ≤ N c) (k : Fin (arity c)) :
    rotationCode arity (pair c (BinaryNatCode.encode k.val)) =
      BinaryNatCode.encode (rotationEmbedding (arity c) (N c) hAN k).val := by
  simp only [rotationCode, pairFst_pair, pairSnd_pair, BinaryNat.sub_pair, BinaryNatCode.encode,
    Nat.fromBitsLE_bits, rotationEmbedding_val]
  change (if k.val = 0 then (arity c - 1).bits else (k.val - 1).bits) =
    (if k.val = 0 then arity c - 1 else k.val - 1).bits
  split_ifs <;> rfl

end LeanCanny.Algebra.FiniteLeafSignBits
