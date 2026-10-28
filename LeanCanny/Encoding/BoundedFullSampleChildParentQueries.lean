/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedFullSampleChildParentThom

/-! # Native selected parent-sign patterns and moments on child candidates

Only the selected derivative orders are listed. Their count is polynomial;
each order remains binary. Native sign-pattern counts and signed products
run on exactly the regular joint candidates, preserving the parent source.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedFullSampleChildParentQueries
open LeanCanny.Algebra LeanCanny.Computation
open BoundedFullSampleChildSource (Inputs)
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BoundedFullSampleChildParentThom.polynomial PrimitivePairBits.coefficient
  BoundedFullSampleChildParentThom.degree BoundedFullSampleChildParentThom.mass
  BoundedFullSampleChildCoordinates.parameterDegree BoundedFullSampleChildCoordinates.baseHeight

def orderContext (orders : List Bool → List Bool) (w : List Bool) : List Bool :=
  pair (pairFst w) (BinaryNat.normalize (orders w))
theorem orderContext_FP {orders : List Bool → List Bool} (ho : orders ∈ FP) : orderContext orders ∈ FP :=
  mem_FP_pair pairFst_mem_FP (mem_FP_comp ho BinaryNat.normalize_mem_FP)

noncomputable def family (F : Inputs) (features : List Bool → ℕ) (orders : List Bool → List Bool)
    (sigma : List Bool → SignType) : SignPatternBits.Family :=
  { BoundedFullSampleChildEquationCount.family F with
    polynomial := fun u i => BoundedFullSampleChildParentThom.polynomial F
      (orderContext orders (pair u (BinaryNatCode.encode i)))
    pattern := fun u i => sigma (pair u (BinaryNatCode.encode i))
    count := fun u => BinaryNatCode.encode (features u)
    degree := fun u => BinaryNatCode.encode (BoundedFullSampleChildParentThom.degree F (pair u []))
    mass := fun u => BinaryNatCode.encode (BoundedFullSampleChildParentThom.mass F (pair u []))
    polynomial_degree := fun u i _ => by
      simpa only [BinaryNatCode.encode, Nat.fromBitsLE_bits, BoundedFullSampleChildParentThom.degree,
        BoundedFullSampleChildParentThom.exponent, BoundedFullSampleChildParentThom.parent,
        BoundedFullSampleChildParentThom.child, orderContext, pairFst_pair] using
        BoundedFullSampleChildParentThom.polynomial_degree F (orderContext orders (pair u (BinaryNatCode.encode i)))
    polynomial_mass := fun u i _ => by
      simpa only [BinaryNatCode.encode, Nat.fromBitsLE_bits, BoundedFullSampleChildParentThom.mass,
        BoundedFullSampleChildParentThom.exponent, BoundedFullSampleChildParentThom.parent,
        BoundedFullSampleChildParentThom.child, orderContext, pairFst_pair] using
        BoundedFullSampleChildParentThom.polynomial_mass F (orderContext orders (pair u (BinaryNatCode.encode i))) }

theorem controls {F : Inputs} (h : F.PolyTime) {features : List Bool → ℕ} (hc : UnaryFn features)
    (orders : List Bool → List Bool) (sigma : List Bool → SignType) :
    SignPatternBits.ControlsPolyTime (family F features orders sigma) := by
  have hp : (fun u : List Bool => pair u []) ∈ FP := mem_FP_pair id_mem_FP (constFn_mem_FP [])
  have hd : BinaryFn (fun u => BoundedFullSampleChildParentThom.degree F (pair u [])) :=
    (BoundedFullSampleChildParentThom.degree_binary h).comp hp
  have hm : BinaryFn (fun u => BoundedFullSampleChildParentThom.mass F (pair u [])) :=
    (BoundedFullSampleChildParentThom.mass_binary h).comp hp
  constructor
  · exact bits_mem_FP hc
  · simpa only [family, BinaryNatCode.encode, Nat.fromBitsLE_bits] using hc
  · exact (BoundedFullSampleChildEquationCount.controls h).rootDegree
  · exact hd.bits_mem_FP
  · exact (BoundedFullSampleChildEquationCount.controls h).rootMass
  · exact hm.bits_mem_FP

noncomputable def access (F : Inputs) (features : List Bool → ℕ) (orders : List Bool → List Bool)
    (sigma : List Bool → SignType) : SignPatternBits.Access (family F features orders sigma) where
  rootCoefficient := (BoundedFullSampleChildEquationCount.access F).rootCoefficient
  polynomialCoefficient := PrimitivePairBits.coefficient
    (BoundedFullSampleChildParentThom.polynomial F ∘ orderContext orders) ∘ BoundedFullSampleChildReaders.query
  pattern w := InfinitesimalSign.encode (sigma w)
  root_eq := (BoundedFullSampleChildEquationCount.access F).root_eq
  polynomial_eq u i _ k m hm := by
    simp only [Function.comp_apply, PrimitivePairBits.coefficient,
      RationalSubstitution.IntegerBits.coefficientResidue, IntegerTarskiSeedBits.integerResidue]
    exact congrArg₂ (fun (z : ℤ) (m : ℕ) => MatrixPower.residueBits (z : ZMod m))
      (by simp only [BoundedFullSampleChildReaders.query, RationalSubstitution.IntegerBits.context,
        RationalSubstitution.IntegerBits.selectedDegree, pairFst_pair, pairSnd_pair,
        BinaryNatCode.encode, Nat.fromBitsLE_bits]; rfl)
      (by simp only [BoundedFullSampleChildReaders.query, RationalSubstitution.IntegerBits.mValue,
        pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]; omega)
  pattern_eq _ _ := rfl

theorem coefficient_evaluator {F : Inputs} (h : F.PolyTime) (features : List Bool → ℕ)
    {orders : List Bool → List Bool} (ho : orders ∈ FP) (sigma : List Bool → SignType) :
    SpaceFunction (access F features orders sigma).polynomialCoefficient :=
  (PrimitivePairBits.withContextEvaluator _ (orderContext orders)
    (SpaceFunction.ofFP _ (orderContext_FP ho)) (BoundedFullSampleChildParentThom.evaluator h)).precompose
      BoundedFullSampleChildReaders.query BoundedFullSampleChildReaders.query_FP

theorem patternCount_evaluator {F : Inputs} (h : F.PolyTime) {features : List Bool → ℕ} (hc : UnaryFn features)
    {orders : List Bool → List Bool} (ho : orders ∈ FP) {sigma : List Bool → SignType}
    (hs : (fun w => InfinitesimalSign.encode (sigma w)) ∈ FP) :
    SpaceFunction (fun u => BinaryNatCode.encode
      (BoundedFullSampleChildQueries.patternCount F (family F features orders sigma) u)) :=
  BoundedFullSampleChildQueries.patternCount_evaluator h (access F features orders sigma)
    (controls h hc orders sigma) hs (coefficient_evaluator h features ho sigma)

noncomputable def moment (F : Inputs) (features : List Bool → ℕ) (orders : List Bool → List Bool) : List Bool → ℤ :=
  BoundedFullSampleChildQueries.moment F (family F features orders (fun _ => 0))

theorem moment_evaluator {F : Inputs} (h : F.PolyTime) {features : List Bool → ℕ} (hc : UnaryFn features)
    {orders : List Bool → List Bool} (ho : orders ∈ FP) :
    SpaceFunction (fun u => SignStatisticBits.integerCode (moment F features orders u)) :=
  BoundedFullSampleChildQueries.moment_evaluator h (access F features orders (fun _ => 0))
    (controls h hc orders (fun _ => 0)) (coefficient_evaluator h features ho (fun _ => 0))

theorem moment_eq_sum (F : Inputs) (features : List Bool → ℕ) (orders : List Bool → List Bool) (u : List Bool) :
    moment F features orders u = ∑ theta ∈ BoundedFullSampleChildQueries.roots F u,
      ∏ i ∈ Finset.range (features u),
        (SignType.sign ((BoundedCriticalSampleThom.polynomial F.block.parent (pairFst u)
          (Nat.fromBitsLE (orders (pair u (BinaryNatCode.encode i))))).eval₂ (Int.castRingHom ℝ)
            (BoundedFullSampleChildParameters.decode F u theta (BoundedFullSampleChildParentThom.first F u))) : ℤ) := by
  simp only [moment, BoundedFullSampleChildQueries.moment, BoundedFullSampleChildQueries.product,
    family, BinaryNatCode.encode, Nat.fromBitsLE_bits, Polynomial.eval_map, algebraMap_int_eq]
  apply Finset.sum_congr rfl
  intro theta ht
  apply Finset.prod_congr rfl
  intro i _
  have he : orderContext orders (pair u i.bits) = pair u
      (BinaryNatCode.encode (Nat.fromBitsLE (orders (pair u i.bits)))) := by
    simp only [orderContext, pairFst_pair, BinaryNat.normalize_eq_bits, BinaryNatCode.encode]
  rw [he, BoundedFullSampleChildParentThom.sign F u _ theta
    ((BoundedFullSampleChildQueries.mem_roots F u theta).mp ht).1]

end LeanCanny.Encoding.BoundedFullSampleChildParentQueries
