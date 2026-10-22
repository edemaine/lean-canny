/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.SymbolicCoordinatePathSource
public import LeanCanny.Algebra.SymbolicKroneckerSpace
public import LeanCanny.Algebra.SymbolicCoefficientContext
public import LeanCanny.Algebra.ClearingMatrixSpace
public import LeanCanny.Algebra.SymbolicBalancedBounds

/-! # Native coefficients of an entire symbolic rational coordinate path

A single polynomial matrix product accounts for every clearing stage. Only
coordinate factors are encoded; the original root index remains the power
of the numerator in every matrix entry.
-/

@[expose] public section
namespace LeanCanny.Algebra.SymbolicCoordinatePathBits
open Polynomial SymbolicBalancedCoordinate
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open scoped Classical
attribute [local irreducible] BinaryNat.normalize

noncomputable def indexedNumerator (F : Source) (c : List Bool) : Polynomial (Polynomial ℤ) :=
  (F.inner (pairFst c) (Nat.fromBitsLE (pairSnd c))).numerator
noncomputable def indexedDenominator (F : Source) (c : List Bool) : Polynomial (Polynomial ℤ) :=
  (F.inner (pairFst c) (Nat.fromBitsLE (pairSnd c))).denominator

def indexedExponent (F : Source) (c : List Bool) : ℕ :=
  F.exponent (pairFst c) (Nat.fromBitsLE (pairSnd c))

def origin (p : List Bool) : List Bool := original (pairFst p)
def stageWord (p : List Bool) : List Bool := pairFst (pairSnd p)
def rowWord (p : List Bool) : List Bool := pairFst (pairSnd (pairSnd p))
def colWord (p : List Bool) : List Bool := pairFst (pairSnd (pairSnd (pairSnd p)))
def entryAlpha (p : List Bool) : List Bool := pairSnd (pairSnd (pairSnd (pairSnd p)))
def stageContext (p : List Bool) : List Bool := pair (origin p) (stageWord p)
def modulusWord (p : List Bool) : List Bool := pairSnd (pairFst (pairFst p))

def radix (F : Source) (p : List Bool) : ℕ :=
  (F.cap (origin p) + 1) * (F.innerBound (origin p) + 1) + Nat.fromBitsLE (entryAlpha p) + 2

def entryExponent (F : Source) (p : List Bool) : ℕ := indexedExponent F (stageContext p)
def entryDegree (F : Source) (p : List Bool) : ℕ :=
  Nat.fromBitsLE (entryAlpha p) + radix F p * Nat.fromBitsLE (colWord p)

noncomputable def kernelNumerator (F : Source) (p : List Bool) : ℤ[X] :=
  PolynomialKronecker.encode (radix F p) (indexedNumerator F (stageContext p))
noncomputable def kernelDenominator (F : Source) (p : List Bool) : ℤ[X] :=
  PolynomialKronecker.encode (radix F p) (indexedDenominator F (stageContext p))

noncomputable def entry (F : Source) : List Bool → List Bool :=
  ClearingMatrixBits.value (kernelNumerator F) (kernelDenominator F) (entryExponent F)
    (fun p => Nat.fromBitsLE (rowWord p)) (entryDegree F) modulusWord

theorem origin_FP : origin ∈ FP := mem_FP_comp pairFst_mem_FP original_FP
theorem stageWord_FP : stageWord ∈ FP := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
theorem rowWord_FP : rowWord ∈ FP := mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) pairFst_mem_FP
theorem colWord_FP : colWord ∈ FP := mem_FP_comp
  (mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) pairSnd_mem_FP) pairFst_mem_FP
theorem entryAlpha_FP : entryAlpha ∈ FP := mem_FP_comp
  (mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) pairSnd_mem_FP) pairSnd_mem_FP
theorem stageContext_FP : stageContext ∈ FP := mem_FP_pair origin_FP stageWord_FP
theorem modulusWord_FP : modulusWord ∈ FP := mem_FP_comp
  (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairSnd_mem_FP

theorem radix_binary (F : Source) (hc : BinaryFn F.cap) (hb : BinaryFn F.innerBound) : BinaryFn (radix F) := by
  have h1 : BinaryFn (fun p => F.cap (origin p)) := hc.comp origin_FP
  have h2 : BinaryFn (fun p => F.innerBound (origin p)) := hb.comp origin_FP
  exact ((((h1.add (BinaryFn.const 1)).mul (h2.add (BinaryFn.const 1))).add
    (BinaryFn.fromBits entryAlpha_FP)).add (BinaryFn.const 2))

lemma radix_pos (F : Source) (p : List Bool) : 0 < radix F p := by unfold radix; omega
lemma alpha_lt_radix (F : Source) (p : List Bool) : Nat.fromBitsLE (entryAlpha p) < radix F p := by unfold radix; omega
lemma bound_lt_radix (F : Source) (p : List Bool) : F.innerBound (origin p) < radix F p := by
  unfold radix
  have := Nat.le_mul_of_pos_left (F.innerBound (origin p) + 1) (Nat.zero_lt_succ (F.cap (origin p)))
  simp only [Nat.succ_eq_add_one] at this
  omega
lemma product_lt_radix (F : Source) (p : List Bool) :
    F.cap (origin p) * F.innerBound (origin p) < radix F p := by unfold radix; nlinarith

theorem entryEvaluator (F : Source) (hc : BinaryFn F.cap) (hb : BinaryFn F.innerBound)
    (he : BinaryFn (indexedExponent F))
    (N : SpaceFunction (SymbolicFixedTableEntryBits.coefficient (indexedNumerator F)))
    (D : SpaceFunction (SymbolicFixedTableEntryBits.coefficient (indexedDenominator F))) : SpaceFunction (entry F) := by
  have EN := SymbolicFixedTableEntryBits.withContextEvaluator _ stageContext stageContext_FP N
  have ED := SymbolicFixedTableEntryBits.withContextEvaluator _ stageContext stageContext_FP D
  have KN := SymbolicKroneckerBits.evaluator (indexedNumerator F ∘ stageContext) (radix F)
    (radix_binary F hc hb) (radix_pos F)
    (fun p k => by
      simp only [Function.comp_apply, indexedNumerator, stageContext, pairFst_pair, pairSnd_pair]
      exact (F.numeratorInner _ _ k).trans_lt (bound_lt_radix F p)) EN
  have KD := SymbolicKroneckerBits.evaluator (indexedDenominator F ∘ stageContext) (radix F)
    (radix_binary F hc hb) (radix_pos F)
    (fun p k => by
      simp only [Function.comp_apply, indexedDenominator, stageContext, pairFst_pair, pairSnd_pair]
      exact (F.denominatorInner _ _ k).trans_lt (bound_lt_radix F p)) ED
  have hE : BinaryFn (entryExponent F) := he.comp stageContext_FP
  have hJ : BinaryFn (entryDegree F) :=
    (BinaryFn.fromBits entryAlpha_FP).add ((radix_binary F hc hb).mul (BinaryFn.fromBits colWord_FP))
  exact ClearingMatrixBits.evaluator _ _ _ _ _ _ hE (BinaryFn.fromBits rowWord_FP) hJ modulusWord_FP KN KD

lemma power_product_inner (n d : Polynomial (Polynomial ℤ)) (H e r : ℕ)
    (hn : ∀ k, (n.coeff k).natDegree ≤ H) (hd : ∀ k, (d.coeff k).natDegree ≤ H)
    (hr : r ≤ e) (k : ℕ) : ((n ^ r * d ^ (e - r)).coeff k).natDegree ≤ e * H := by
  apply (PolynomialKronecker.inner_degree_iff_swap _ _).mpr ?_ k
  rw [map_mul, map_pow, map_pow]
  calc
    _ ≤ r * H + (e - r) * H := natDegree_mul_le.trans
      (Nat.add_le_add (natDegree_pow_le.trans (Nat.mul_le_mul_left _
        ((PolynomialKronecker.inner_degree_iff_swap n H).mp hn)))
        (natDegree_pow_le.trans (Nat.mul_le_mul_left _
          ((PolynomialKronecker.inner_degree_iff_swap d H).mp hd))))
    _ = _ := by rw [← Nat.add_mul, Nat.add_sub_of_le hr]

lemma entry_packet (F : Source) (q : List Bool) (s : ℕ) (i j : Fin (width F q)) (u : ℕ) :
    entry F (pair q (pair (BinaryNatCode.encode s) (pair (BinaryNatCode.encode i.val)
      (pair (BinaryNatCode.encode j.val) (BinaryNatCode.encode u))))) =
        residueBits (((factor F q s i j).coeff u : ℤ) :
          ZMod (Nat.fromBitsLE (pairSnd (pairFst q)) + 1)) := by
  let p := pair q (pair (BinaryNatCode.encode s) (pair (BinaryNatCode.encode i.val)
    (pair (BinaryNatCode.encode j.val) (BinaryNatCode.encode u))))
  have ho : origin p = original q := by simp only [p, origin, pairFst_pair]
  have ha : Nat.fromBitsLE (entryAlpha p) = u := by simp only [p, entryAlpha, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  have hri : i.val ≤ F.exponent (original q) s → ∀ k,
      (((F.inner (original q) s).numerator ^ i.val *
        (F.inner (original q) s).denominator ^ (F.exponent (original q) s - i.val)).coeff k).natDegree < radix F p := by
    intro hi k
    exact (power_product_inner _ _ (F.innerBound (original q)) _ _
      (F.numeratorInner _ _) (F.denominatorInner _ _) hi k).trans_lt
      ((Nat.mul_le_mul_right _ (F.exponent_le _ _)).trans_lt (by simpa only [ho] using product_lt_radix F p))
  change entry F p = _
  simp only [entry, ClearingMatrixBits.value, kernelNumerator, kernelDenominator,
    entryExponent, indexedExponent, indexedNumerator, indexedDenominator
    , stageContext, stageWord, rowWord, colWord, entryDegree, modulusWord, p, origin, entryAlpha,
    pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  rw [UnivariateRational.clear_X_pow]
  by_cases hi : i.val ≤ F.exponent (original q) s
  · rw [ite_eq_left hi]
    have hh := PolynomialKronecker.coefficient (radix F p)
      ((F.inner (original q) s).numerator ^ i.val *
        (F.inner (original q) s).denominator ^ (F.exponent (original q) s - i.val))
      (hri hi) u j.val (by simpa only [ha] using alpha_lt_radix F p)
    rw [map_mul, map_pow, map_pow] at hh
    change RationalSubstitution.IntegerBits.coefficientResidue _ _ = _
    have heq := congrArg (fun z : ℤ => RationalSubstitution.IntegerBits.coefficientResidue z
      (Nat.fromBitsLE (pairSnd (pairFst q)) + 1)) hh
    simpa only [p, BinaryNatCode.encode, factor, SymbolicClearingMatrix.clearingMatrix, hi, ite_true,
      RationalSubstitution.IntegerBits.coefficientResidue] using heq
  · simp only [coeff_zero, factor, SymbolicClearingMatrix.clearingMatrix,
      hi, ite_false, RationalSubstitution.IntegerBits.coefficientResidue, Int.cast_zero]

noncomputable def access (F : Source) (numerator : Bool) (hc : BinaryFn F.cap)
    (hk : BinaryFn F.depth) : PolynomialMatrixProductBits.Access (productFamily F numerator) where
  width := width_binary F hc
  count := hk.comp original_FP
  modulus := ((BinaryFn.fromBits (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP)).add (BinaryFn.const 1))
  row := BinaryFn.const (if numerator then 1 else 0)
  col := BinaryFn.fromBits rootWord_FP
  degree := BinaryFn.fromBits alphaWord_FP
  entry := entry F
  entry_eq := by
    intro q s i j u
    change entry F _ = residueBits (((factor F q s i j).map
      (Int.castRingHom (ZMod (Nat.fromBitsLE (pairSnd (pairFst q)) + 1)))).coeff u)
    rw [coeff_map]
    simpa only [Int.coe_castRingHom] using entry_packet F q s i j u

theorem coefficientEvaluator (F : Source) (numerator : Bool) (hc : BinaryFn F.cap)
    (hk : BinaryFn F.depth) (hb : BinaryFn F.innerBound) (he : BinaryFn (indexedExponent F))
    (N : SpaceFunction (SymbolicFixedTableEntryBits.coefficient (indexedNumerator F)))
    (D : SpaceFunction (SymbolicFixedTableEntryBits.coefficient (indexedDenominator F))) :
    SpaceFunction (SymbolicFixedTableEntryBits.coefficient (F.component numerator)) :=
  (PolynomialMatrixProductBits.evaluator (productFamily F numerator) (access F numerator hc hk)
    (entryEvaluator F hc hb he N D)).congr (value_eq F numerator)

end LeanCanny.Algebra.SymbolicCoordinatePathBits
