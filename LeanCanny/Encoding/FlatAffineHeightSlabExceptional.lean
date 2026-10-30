/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineHeightExceptional
public import LeanCanny.Encoding.FlatAffineHeightTrailing
public import LeanCanny.Encoding.FlatAffineHeightCoordinateTrailing
public import LeanCanny.Connectivity.FlatAffineHeightArcs

/-! # A native complete exceptional polynomial for actual affine-height slabs

The first block of factors regularizes every coordinate. The second retains
every equation-value trailing factor. The third controls coordinate zeros,
including critical multiplier zeros. The polynomial and all its budgets
come from the original source programs.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineHeightSlabExceptional
open LeanCanny.Algebra LeanCanny.Computation MatrixPower
open FlatAffineFullSourceTower (Inputs)
open FlatAffineFullSourcePositive (count)
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000

noncomputable def row (F : Inputs) (z : List Bool) : Fin (count F (pairFst z)) :=
  FlatAffineHeightGram.rawRow F (pairFst z) (Nat.fromBitsLE (pairSnd z))

theorem row_unary {F : Inputs} (h : F.Access) : UnaryFn (fun z => (row F z).val) :=
  UnaryFn.fromBitsLE_min pairSnd_mem_FP
    (((FlatAffineFullSourcePositive.count_unary h).comp pairFst_mem_FP).sub (UnaryFn.const 1))

noncomputable def certificate (F : Inputs) (height : (u : List Bool) → Fin (count F u)) :
    List Bool → Polynomial (Polynomial ℤ) :=
  FlatAffineHeightTrailing.polynomial (FlatAffineFullSourceContext.comp F pairFst)
    (fun z => height (pairFst z)) (row F)

lemma certificate_eq (F : Inputs) (height : (u : List Bool) → Fin (count F u)) (z : List Bool) :
    certificate F height z =
      (FlatAffineHeightValues.family F height
        (fun u => FlatAffineHeightGram.rawRow F u (Nat.fromBitsLE (pairSnd z)))).affine.homogeneous.annihilator (pairFst z) := by
  change (FlatAffineHeightValues.family (FlatAffineFullSourceContext.comp F pairFst)
    (fun z => height (pairFst z)) (row F)).affine.homogeneous.annihilator z = _
  calc
    _ = (FlatAffineHeightValues.family (FlatAffineFullSourceContext.comp F pairFst)
        (fun z => height (pairFst z))
        (fun r => FlatAffineHeightGram.rawRow F (pairFst r) (Nat.fromBitsLE (pairSnd z)))).affine.homogeneous.annihilator z :=
      FlatAffineHeightValues.annihilator_row_congr _ _ _ _ z rfl
    _ = _ := FlatAffineHeightValues.annihilator_comp F height
      (fun u => FlatAffineHeightGram.rawRow F u (Nat.fromBitsLE (pairSnd z))) pairFst z

lemma certificate_packet (F : Inputs) (height : (u : List Bool) → Fin (count F u))
    (u : List Bool) (i : Fin (count F u)) :
    certificate F height (pair u (BinaryNatCode.encode i.val)) =
      Connectivity.FlatAffineHeightArcs.certificate F height u i := by
  rw [certificate_eq]
  simp only [pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  rfl

noncomputable def trailing (F : Inputs) (height : (u : List Bool) → Fin (count F u)) (z : List Bool) : Polynomial ℤ :=
  (certificate F height z).trailingCoeff

theorem trailingEvaluator {F : Inputs} (h : F.Access) (height : (u : List Bool) → Fin (count F u))
    (hh : UnaryFn (fun u => (height u).val)) : SpaceFunction (PrimitivePairBits.coefficient (trailing F height)) :=
  FlatAffineHeightTrailing.coefficientEvaluator (FlatAffineFullSourceContext.access h pairFst_mem_FP)
    (fun z => height (pairFst z)) (row F) (hh.comp pairFst_mem_FP) (row_unary h)

theorem trailing_ne_zero (F : Inputs) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (z : List Bool) : trailing F height z ≠ 0 := by
  apply Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr
  rw [certificate_eq]
  exact FlatAffineHeightValues.ne_zero F hcone height _ _

noncomputable def trailingDegreeBound (F : Inputs) : List Bool → ℕ :=
  FlatAffineHeightTrailing.innerBound (FlatAffineFullSourceContext.comp F pairFst) (row F)

noncomputable def trailingMassBound (F : Inputs) (z : List Bool) : ℕ :=
  FlatAffineHeightValueBounds.heightBound (FlatAffineFullSourceContext.comp F pairFst) (row F) z +
    (trailingDegreeBound F z + 1).size

theorem trailingDegreeBound_binary {F : Inputs} (h : F.Access)
    (height : (u : List Bool) → Fin (count F u)) : BinaryFn (trailingDegreeBound F) :=
  FlatAffineHeightTrailing.innerBound_binary (FlatAffineFullSourceContext.access h pairFst_mem_FP)
    (fun z => height (pairFst z)) (row F) (row_unary h)

theorem trailingMassBound_binary {F : Inputs} (h : F.Access)
    (height : (u : List Bool) → Fin (count F u)) : BinaryFn (trailingMassBound F) :=
  (FlatAffineHeightValueBounds.heightBound_binary (FlatAffineFullSourceContext.access h pairFst_mem_FP)
    (fun z => height (pairFst z)) (row F) (row_unary h)).add
      ((trailingDegreeBound_binary h height).add (BinaryFn.const 1)).size

theorem trailing_degree_bound (F : Inputs) (height : (u : List Bool) → Fin (count F u)) (z : List Bool) :
    (trailing F height z).natDegree ≤ trailingDegreeBound F z :=
  FlatAffineHeightTrailing.trailing_degree_le _ _ _ z

theorem trailing_mass_bound (F : Inputs) (height : (u : List Bool) → Fin (count F u)) (z : List Bool) :
    coefficientMass (trailing F height z) ≤ 2 ^ trailingMassBound F z := by
  apply coefficientMass_le_pow_of_degree_coeff _ _ _ (trailing_degree_bound F height z)
  intro k
  exact (Nat.lt_size_self _).le.trans (Nat.pow_le_pow_right (by decide)
    (FlatAffineHeightValueBounds.height_le (FlatAffineFullSourceContext.comp F pairFst)
      (fun z => height (pairFst z)) (row F) z (certificate F height z).natTrailingDegree k))

def second (F : Inputs) (z : List Bool) : List Bool :=
  pair (pairFst z) (BinaryNatCode.encode (Nat.fromBitsLE (pairSnd z) - count F (pairFst z)))

theorem second_FP {F : Inputs} (h : F.Access) : second F ∈ FP :=
  mem_FP_pair pairFst_mem_FP (BinaryFn.bits_mem_FP ((BinaryFn.fromBits pairSnd_mem_FP).sub
    ((BinaryFn.ofUnary (FlatAffineFullSourcePositive.count_unary h)).comp pairFst_mem_FP)))

def first (F : Inputs) (z : List Bool) : Prop := Nat.fromBitsLE (pairSnd z) < count F (pairFst z)
instance (F : Inputs) : DecidablePred (first F) := fun _ => inferInstanceAs (Decidable (_ < _))

theorem first_fppred {F : Inputs} (h : F.Access) : FPPred (first F) :=
  (BinaryFn.fromBits pairSnd_mem_FP).lt ((BinaryFn.ofUnary (FlatAffineFullSourcePositive.count_unary h)).comp pairFst_mem_FP)

noncomputable def factor (F : Inputs) (height : (u : List Bool) → Fin (count F u)) (z : List Bool) : Polynomial ℤ :=
  if first F z then FlatAffineHeightExceptional.indexed F height z else
    if first F (second F z) then trailing F height (second F z) else
      FlatAffineHeightCoordinateTrailing.indexed F height (second F (second F z))

theorem factorEvaluator {F : Inputs} (h : F.Access) (height : (u : List Bool) → Fin (count F u))
    (hh : UnaryFn (fun u => (height u).val)) : SpaceFunction (PrimitivePairBits.coefficient (factor F height)) := by
  have T := PolynomialFamilyProductBits.reindexEvaluator (trailingEvaluator h height hh) (second F) (second_FP h)
  have C := PolynomialFamilyProductBits.reindexEvaluator (FlatAffineHeightCoordinateTrailing.indexedEvaluator h height hh)
    (second F ∘ second F) (mem_FP_comp (second_FP h) (second_FP h))
  have TC := SpaceFunction.branch (fun q => decide (first F (second F (RationalSubstitution.IntegerBits.context q))))
    ((first_fppred h).comp (mem_FP_comp RationalSubstitution.IntegerBits.context_mem_FP (second_FP h))).flag_mem_FP T C
  have H := SpaceFunction.branch (fun q => decide (first F (RationalSubstitution.IntegerBits.context q)))
    ((first_fppred h).comp RationalSubstitution.IntegerBits.context_mem_FP).flag_mem_FP
    (FlatAffineHeightExceptional.indexedEvaluator h height hh) TC
  refine H.congr (funext fun q => ?_)
  simp only [decide_eq_true_eq, Function.comp_apply, PrimitivePairBits.coefficient, factor]
  split_ifs <;> rfl

noncomputable def polynomial (F : Inputs) (height : (u : List Bool) → Fin (count F u)) : List Bool → Polynomial ℤ :=
  PolynomialFamilyProductBits.polynomial (factor F height) (fun u => 3 * count F u)

theorem evaluator {F : Inputs} (h : F.Access) (height : (u : List Bool) → Fin (count F u))
    (hh : UnaryFn (fun u => (height u).val)) : SpaceFunction (PrimitivePairBits.coefficient (polynomial F height)) :=
  PolynomialFamilyProductBits.evaluator _ _ ((BinaryFn.const 3).mul (BinaryFn.ofUnary (FlatAffineFullSourcePositive.count_unary h)))
    (factorEvaluator h height hh)

theorem ne_zero (F : Inputs) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (u : List Bool) : polynomial F height u ≠ 0 := by
  apply PolynomialFamilyProductBits.ne_zero _ _ ?_ u
  intro z
  dsimp only [factor]
  split_ifs
  · exact FlatAffineHeightExceptional.indexed_ne_zero F hcone height z
  · exact trailing_ne_zero F hcone height _
  · exact FlatAffineHeightCoordinateTrailing.indexed_ne_zero F hcone height _

theorem avoids {K : Type*} [Field K] (phi : Polynomial ℤ →+* K)
    (F : Inputs) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (u : List Bool)
    (ht : phi (polynomial F height u) ≠ 0) :
    phi (Connectivity.FlatAffineHeightArcs.exceptional F height u) ≠ 0 := by
  have H : ∀ j < 3 * count F u, phi (factor F height (pair u (BinaryNatCode.encode j))) ≠ 0 := by
    simpa only [polynomial, PolynomialFamilyProductBits.polynomial, map_prod,
      Finset.prod_ne_zero_iff, Finset.mem_range] using ht
  rw [Connectivity.FlatAffineHeightArcs.exceptional, map_mul, mul_ne_zero_iff]
  constructor
  · rw [map_prod]
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    apply FlatAffineHeightExceptional.indexed_avoids phi F hcone height u i
    have Hi := H i.val (by have := i.isLt; omega)
    simpa only [factor, first, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits,
      i.isLt, ite_true] using Hi
  · rw [map_prod]
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    have Hi := H (count F u + i.val) (by have := i.isLt; omega)
    have hn : ¬ count F u + i.val < count F u := by omega
    simp only [factor, first, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits, hn, ite_false,
      second, Nat.add_sub_cancel_left, i.isLt, ite_true, trailing] at Hi
    change phi (certificate F height (pair u (BinaryNatCode.encode i.val))).trailingCoeff ≠ 0 at Hi
    rwa [certificate_packet F height u i] at Hi

theorem coordinate_trailing_avoids {K : Type*} [Field K] (phi : Polynomial ℤ →+* K)
    (F : Inputs) (height : (u : List Bool) → Fin (count F u)) (u : List Bool)
    (ht : phi (polynomial F height u) ≠ 0) :
    phi (FlatAffineHeightCoordinateTrailing.polynomial F height u) ≠ 0 := by
  have H : ∀ j < 3 * count F u, phi (factor F height (pair u (BinaryNatCode.encode j))) ≠ 0 := by
    simpa only [polynomial, PolynomialFamilyProductBits.polynomial, map_prod,
      Finset.prod_ne_zero_iff, Finset.mem_range] using ht
  simp only [FlatAffineHeightCoordinateTrailing.polynomial, PolynomialFamilyProductBits.polynomial,
    map_prod, Finset.prod_ne_zero_iff, Finset.mem_range]
  intro i hi
  have HI := H (2 * count F u + i) (by omega)
  have H0 : ¬2 * count F u + i < count F u := by omega
  have H1 : 2 * count F u + i - count F u = count F u + i := by omega
  have H2 : ¬count F u + i < count F u := by omega
  have H3 : count F u + i - count F u = i := by omega
  simpa only [factor, first, second, pairFst_pair, pairSnd_pair, BinaryNatCode.encode,
    Nat.fromBitsLE_bits, H0, ite_false, H1, H2, H3] using HI

noncomputable def factorDegreeBound (F : Inputs) (z : List Bool) : ℕ :=
  if first F z then FlatAffineHeightExceptional.indexedDegreeBound F z else
    if first F (second F z) then trailingDegreeBound F (second F z) else
      FlatAffineHeightExceptional.degree F (second F (second F z))

noncomputable def factorMassBound (F : Inputs) (z : List Bool) : ℕ :=
  if first F z then FlatAffineHeightExceptional.indexedMassBound F z else
    if first F (second F z) then trailingMassBound F (second F z) else
      FlatAffineHeightExceptional.exponent F (second F (second F z))

theorem factorDegreeBound_binary {F : Inputs} (h : F.Access)
    (height : (u : List Bool) → Fin (count F u)) : BinaryFn (factorDegreeBound F) :=
  BinaryFn.ite (first_fppred h) (FlatAffineHeightExceptional.indexedDegreeBound_binary h)
    (BinaryFn.ite ((first_fppred h).comp (second_FP h)) ((trailingDegreeBound_binary h height).comp (second_FP h))
      ((FlatAffineHeightExceptional.degree_binary h).comp (mem_FP_comp (second_FP h) (second_FP h))))

theorem factorMassBound_binary {F : Inputs} (h : F.Access)
    (height : (u : List Bool) → Fin (count F u)) : BinaryFn (factorMassBound F) :=
  BinaryFn.ite (first_fppred h) (FlatAffineHeightExceptional.indexedMassBound_binary h)
    (BinaryFn.ite ((first_fppred h).comp (second_FP h)) ((trailingMassBound_binary h height).comp (second_FP h))
      ((FlatAffineHeightExceptional.exponent_binary h).comp (mem_FP_comp (second_FP h) (second_FP h))))

theorem factor_degree_bound (F : Inputs) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (z : List Bool) :
    (factor F height z).natDegree ≤ factorDegreeBound F z := by
  dsimp only [factor, factorDegreeBound]
  split_ifs
  · exact FlatAffineHeightExceptional.indexed_degree_bound F hcone height z
  · exact trailing_degree_bound F height _
  · exact FlatAffineHeightCoordinateTrailing.indexed_degree_bound F height _

theorem factor_mass_bound (F : Inputs) (height : (u : List Bool) → Fin (count F u)) (z : List Bool) :
    coefficientMass (factor F height z) ≤ 2 ^ factorMassBound F z := by
  dsimp only [factor, factorMassBound]
  split_ifs
  · exact FlatAffineHeightExceptional.indexed_mass_bound F height z
  · exact trailing_mass_bound F height _
  · exact FlatAffineHeightCoordinateTrailing.indexed_mass_bound F height _

noncomputable def degreeBound (F : Inputs) : List Bool → ℕ :=
  PolynomialFamilyProductBits.budget (fun u => 3 * count F u) (factorDegreeBound F)

noncomputable def massBound (F : Inputs) : List Bool → ℕ :=
  PolynomialFamilyProductBits.budget (fun u => 3 * count F u) (factorMassBound F)

theorem degreeBound_binary {F : Inputs} (h : F.Access)
    (height : (u : List Bool) → Fin (count F u)) : BinaryFn (degreeBound F) :=
  PolynomialFamilyProductBits.budget_binary ((UnaryFn.const 3).mul (FlatAffineFullSourcePositive.count_unary h))
    (factorDegreeBound_binary h height)

theorem massBound_binary {F : Inputs} (h : F.Access)
    (height : (u : List Bool) → Fin (count F u)) : BinaryFn (massBound F) :=
  PolynomialFamilyProductBits.budget_binary ((UnaryFn.const 3).mul (FlatAffineFullSourcePositive.count_unary h))
    (factorMassBound_binary h height)

theorem degree_bound (F : Inputs) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (u : List Bool) :
    (polynomial F height u).natDegree ≤ degreeBound F u :=
  PolynomialFamilyProductBits.degree_le_budget _ _ _ (factor_degree_bound F hcone height) u

theorem mass_bound (F : Inputs) (height : (u : List Bool) → Fin (count F u)) (u : List Bool) :
    coefficientMass (polynomial F height u) ≤ 2 ^ massBound F u :=
  PolynomialFamilyProductBits.mass_le_budget _ _ _ (factor_mass_bound F height) u

end LeanCanny.Encoding.FlatAffineHeightSlabExceptional
