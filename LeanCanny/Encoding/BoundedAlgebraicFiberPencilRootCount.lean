/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedAlgebraicFiberPencilSource
public import LeanCanny.Algebra.SignPatternCountSpace

/-! # Native distinct-real-root counting for the weighted Gram pencil

The determinant's coefficients come from the actual streamed moment reader.
Binary degree and mass controls permit the exponential dimension and integer
coefficient bounds. Comparing the resulting root count with the supplied
dimension is a native separation test on the total context language.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedAlgebraicFiberPencilRootCount
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter Polynomial
open BoundedAlgebraicFiberPencilEntries
open scoped Classical

def degree (b : List Bool) : ℕ := dimension b + 1
theorem degree_binary : BinaryFn degree := dimension_binary.add (BinaryFn.const 1)

noncomputable def massExponent (F : BoundedAlgebraicSlice.Family) (b : List Bool) : ℕ :=
  BoundedAlgebraicFiberPencilBounds.budget F b + (degree b + 1).size
theorem massExponent_binary {F : BoundedAlgebraicSlice.Family} (A : F.Access) : BinaryFn (massExponent F) :=
  (BoundedAlgebraicFiberPencilBounds.budget_binary A).add ((degree_binary.add (BinaryFn.const 1)).size)

theorem mass_bound (P : Readers) (F : BoundedAlgebraicSlice.Family) (b : List Bool) : coefficientMass (matrix P F b).det ≤ 2 ^ massExponent F b := by
  apply coefficientMass_le_pow_of_degree_coeff _ (degree b) (BoundedAlgebraicFiberPencilBounds.budget F b)
  · exact (BoundedAlgebraicFiberPencilBounds.determinant_degree P F b).trans (Nat.le_succ _)
  · intro k
    exact (Nat.lt_size_self _).le.trans (Nat.pow_le_pow_right (by decide)
      (BoundedAlgebraicFiberPencilBounds.determinant_bits P F b k))

noncomputable def family (P : Readers) (F : BoundedAlgebraicSlice.Family) : SignPatternBits.Family where
  root b := (matrix P F b).det
  polynomial _ _ := 1
  pattern _ _ := 0
  count _ := []
  rootDegree b := BinaryNatCode.encode (degree b)
  degree _ := []
  rootMass b := BinaryNatCode.encode (massExponent F b)
  mass _ := []
  rootDegree_pos b := by simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits, degree]; omega
  root_degree b := by
    simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]
    exact (BoundedAlgebraicFiberPencilBounds.determinant_degree P F b).trans (Nat.le_succ _)
  root_mass b := by simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]; exact mass_bound P F b
  polynomial_degree _ i hi := by change i < 0 at hi; omega
  polynomial_mass _ i hi := by change i < 0 at hi; omega

theorem controls (P : Readers) {F : BoundedAlgebraicSlice.Family} (A : F.Access) : SignPatternBits.ControlsPolyTime (family P F) :=
  ⟨constFn_mem_FP [], UnaryFn.const 0, degree_binary.bits_mem_FP, constFn_mem_FP [],
    (massExponent_binary A).bits_mem_FP, constFn_mem_FP []⟩

noncomputable def access (P : Readers) (F : BoundedAlgebraicSlice.Family) : SignPatternBits.Access (family P F) where
  rootCoefficient := BoundedAlgebraicFiberPencilCoefficient.value P F
  polynomialCoefficient _ := []
  pattern _ := []
  root_eq b k m hm := by
    generalize hw : BinaryNatCode.encode (m - 1) = w
    have he : Nat.fromBitsLE w + 1 = m := by
      rw [← hw]
      simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]
      omega
    subst m
    exact BoundedAlgebraicFiberPencilCoefficient.value_packet P F b k w
  polynomial_eq _ i hi := by change i < 0 at hi; omega
  pattern_eq _ _ := rfl

noncomputable def count (P : Readers) (F : BoundedAlgebraicSlice.Family) (b : List Bool) : ℕ :=
  (((matrix P F b).det.map (Int.castRingHom ℝ)).roots.toFinset).card

theorem family_count (P : Readers) (F : BoundedAlgebraicSlice.Family) (b : List Bool) : SignPatternBits.rootCount (family P F) b = count P F b := by
  simp [SignPatternBits.rootCount, family, RootSignQueries.signCount, count, algebraMap_int_eq,
    show Nat.fromBitsLE ([] : List Bool) = 0 from rfl]

theorem evaluator {P : Readers} (h : P.PolyTime) {F : BoundedAlgebraicSlice.Family} (A : F.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (fun b => BinaryNatCode.encode (count P F b)) := by
  have E := SignPatternBits.rootCountEvaluator (access P F) (controls P A) (constFn_mem_FP [])
    (BoundedAlgebraicFiberPencilCoefficient.evaluator h A ha) (SpaceFunction.ofFP _ (constFn_mem_FP []))
  exact E.congr (funext fun b => congrArg BinaryNatCode.encode (family_count P F b))

noncomputable def language (P : Readers) (F : BoundedAlgebraicSlice.Family) : Language := {b | count P F b = dimension b}

theorem decider {P : Readers} (h : P.PolyTime) {F : BoundedAlgebraicSlice.Family} (A : F.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceDecider (language P F) := by
  have E := (evaluator h A ha).withInput
  have hR := BinaryFn.fromBits (mem_FP_comp pairFst_mem_FP BoundedAlgebraicFiberWeightedMoments.count_FP)
  have hc := ((BinaryFn.fromBits pairSnd_mem_FP).eq hR).flag_mem_FP
  apply E.decider (fun z => decide (Nat.fromBitsLE (pairSnd z) =
    Nat.fromBitsLE (BoundedAlgebraicFiberWeightedMoments.count (pairFst z)))) hc
  intro b
  simp only [language, Set.mem_ofPred_eq, pairFst_pair, pairSnd_pair, BinaryNatCode.encode,
    Nat.fromBitsLE_bits, decide_eq_true_eq]

theorem language_packet (P : Readers) (F : BoundedAlgebraicSlice.Family) (c m : List Bool) (t : ℕ) :
    BoundedAlgebraicFiberWeightedMoments.context c (BoundedAlgebraicSlice.RootCount.count P F c) m t ∈ language P F ↔
      Function.Injective (BoundedAlgebraicFiberRootHash.integerValue P F c (Nat.fromBitsLE m + 1) t) := by
  change count P F (BoundedAlgebraicFiberWeightedMoments.context c (BoundedAlgebraicSlice.RootCount.count P F c) m t) =
    dimension (BoundedAlgebraicFiberWeightedMoments.context c (BoundedAlgebraicSlice.RootCount.count P F c) m t) ↔ _
  rw [BoundedAlgebraicFiberPencilSource.dimension_context]
  exact BoundedAlgebraicFiberPencilSource.real_rootCount_eq_count_iff P F c m t

end LeanCanny.Encoding.BoundedAlgebraicFiberPencilRootCount
