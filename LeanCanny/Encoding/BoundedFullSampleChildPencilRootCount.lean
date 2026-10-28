/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedFullSampleChildPencilSource
public import LeanCanny.Algebra.SignPatternCountSpace

/-! # Native distinct-real-root counting for the weighted Gram pencil

The determinant's coefficients come from the actual streamed moment reader.
Binary degree and mass controls permit the exponential dimension and integer
coefficient bounds. Comparing the resulting root count with the supplied
dimension is a native separation test on the total context language.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedFullSampleChildPencilRootCount
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter Polynomial
open BoundedFullSampleChildPencilEntries
open BoundedFullSampleChildSource (Inputs)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BoundedFullSampleChildRecords.length BoundedFullSampleChildThom.labelWidth
  BoundedFullSampleChildCoordinates.parameterDegree BoundedFullSampleChildCoordinates.baseHeight
  BoundedFullSampleChildQueries.roots BoundedFullSampleChildRegularCount.count

def degree (b : List Bool) : ℕ := dimension b + 1
theorem degree_binary : BinaryFn degree := dimension_binary.add (BinaryFn.const 1)

noncomputable def massExponent (P : Inputs) (b : List Bool) : ℕ :=
  BoundedFullSampleChildPencilBounds.budget P b + (degree b + 1).size
theorem massExponent_binary {P : Inputs} (h : P.PolyTime) : BinaryFn (massExponent P) :=
  (BoundedFullSampleChildPencilBounds.budget_binary h).add ((degree_binary.add (BinaryFn.const 1)).size)

theorem mass_bound (P : Inputs) (b : List Bool) : coefficientMass (matrix P b).det ≤ 2 ^ massExponent P b := by
  apply coefficientMass_le_pow_of_degree_coeff _ (degree b) (BoundedFullSampleChildPencilBounds.budget P b)
  · exact (BoundedFullSampleChildPencilBounds.determinant_degree P b).trans (Nat.le_succ _)
  · intro k
    exact (Nat.lt_size_self _).le.trans (Nat.pow_le_pow_right (by decide)
      (BoundedFullSampleChildPencilBounds.determinant_bits P b k))

noncomputable def family (P : Inputs) : SignPatternBits.Family where
  root b := (matrix P b).det
  polynomial _ _ := 1
  pattern _ _ := 0
  count _ := []
  rootDegree b := BinaryNatCode.encode (degree b)
  degree _ := []
  rootMass b := BinaryNatCode.encode (massExponent P b)
  mass _ := []
  rootDegree_pos b := by simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits, degree]; omega
  root_degree b := by
    simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]
    exact (BoundedFullSampleChildPencilBounds.determinant_degree P b).trans (Nat.le_succ _)
  root_mass b := by simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]; exact mass_bound P b
  polynomial_degree _ i hi := by change i < 0 at hi; omega
  polynomial_mass _ i hi := by change i < 0 at hi; omega

theorem controls {P : Inputs} (h : P.PolyTime) : SignPatternBits.ControlsPolyTime (family P) :=
  ⟨constFn_mem_FP [], UnaryFn.const 0, degree_binary.bits_mem_FP, constFn_mem_FP [],
    (massExponent_binary h).bits_mem_FP, constFn_mem_FP []⟩

noncomputable def access (P : Inputs) : SignPatternBits.Access (family P) where
  rootCoefficient := BoundedFullSampleChildPencilCoefficient.value P
  polynomialCoefficient _ := []
  pattern _ := []
  root_eq b k m hm := by
    generalize hw : BinaryNatCode.encode (m - 1) = w
    have he : Nat.fromBitsLE w + 1 = m := by
      rw [← hw]
      simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]
      omega
    subst m
    exact BoundedFullSampleChildPencilCoefficient.value_packet P b k w
  polynomial_eq _ i hi := by change i < 0 at hi; omega
  pattern_eq _ _ := rfl

noncomputable def count (P : Inputs) (b : List Bool) : ℕ :=
  (((matrix P b).det.map (Int.castRingHom ℝ)).roots.toFinset).card

theorem family_count (P : Inputs) (b : List Bool) : SignPatternBits.rootCount (family P) b = count P b := by
  simp [SignPatternBits.rootCount, family, RootSignQueries.signCount, count, algebraMap_int_eq,
    show Nat.fromBitsLE ([] : List Bool) = 0 from rfl]

theorem evaluator {P : Inputs} (h : P.PolyTime) :
    SpaceFunction (fun b => BinaryNatCode.encode (count P b)) := by
  have E := SignPatternBits.rootCountEvaluator (access P) (controls h) (constFn_mem_FP [])
    (BoundedFullSampleChildPencilCoefficient.evaluator h) (SpaceFunction.ofFP _ (constFn_mem_FP []))
  exact E.congr (funext fun b => congrArg BinaryNatCode.encode (family_count P b))

noncomputable def language (P : Inputs) : Language := {b | count P b = dimension b}

theorem decider {P : Inputs} (h : P.PolyTime) : SpaceDecider (language P) := by
  have E := (evaluator h).withInput
  have hR := BinaryFn.fromBits (mem_FP_comp pairFst_mem_FP BoundedFullSampleChildWeightedMoments.count_FP)
  have hc := ((BinaryFn.fromBits pairSnd_mem_FP).eq hR).flag_mem_FP
  apply E.decider (fun z => decide (Nat.fromBitsLE (pairSnd z) =
    Nat.fromBitsLE (BoundedFullSampleChildWeightedMoments.count (pairFst z)))) hc
  intro b
  simp only [language, Set.mem_ofPred_eq, pairFst_pair, pairSnd_pair, BinaryNatCode.encode,
    Nat.fromBitsLE_bits, decide_eq_true_eq]

theorem language_packet (P : Inputs) (c m : List Bool) (t : ℕ) :
    BoundedFullSampleChildWeightedMoments.context c (BoundedFullSampleChildRegularCount.count P c) m t ∈ language P ↔
      Function.Injective (BoundedFullSampleChildRootHash.integerValue P c (Nat.fromBitsLE m + 1) t) := by
  change count P (BoundedFullSampleChildWeightedMoments.context c (BoundedFullSampleChildRegularCount.count P c) m t) =
    dimension (BoundedFullSampleChildWeightedMoments.context c (BoundedFullSampleChildRegularCount.count P c) m t) ↔ _
  rw [BoundedFullSampleChildPencilSource.dimension_context]
  exact BoundedFullSampleChildPencilSource.real_rootCount_eq_count_iff P c m t

end LeanCanny.Encoding.BoundedFullSampleChildPencilRootCount
