/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalSampleChildParentThom

/-! # Native selected parent-sign patterns and moments on child candidates

Only the selected derivative orders are listed. Their count is polynomial;
each order remains binary. Native sign-pattern counts and signed products
run on exactly the regular joint candidates, preserving the parent source.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalSampleChildParentQueries
open LeanCanny.Algebra LeanCanny.Computation
open BoundedCriticalSampleChildSource (Inputs)
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BoundedCriticalSampleChildParentThom.polynomial PrimitivePairBits.coefficient
  BoundedCriticalSampleChildParentThom.degree BoundedCriticalSampleChildParentThom.mass
  BoundedCriticalSampleChildCoordinates.parameterDegree BoundedCriticalSampleChildCoordinates.baseHeight

def orderContext (orders : List Bool → List Bool) (w : List Bool) : List Bool :=
  pair (pairFst w) (BinaryNat.normalize (orders w))
theorem orderContext_FP {orders : List Bool → List Bool} (ho : orders ∈ FP) : orderContext orders ∈ FP :=
  mem_FP_pair pairFst_mem_FP (mem_FP_comp ho BinaryNat.normalize_mem_FP)

noncomputable def family (F : Inputs) (features : List Bool → ℕ) (orders : List Bool → List Bool)
    (sigma : List Bool → SignType) : SignPatternBits.Family :=
  { BoundedCriticalSampleChildEquationCount.family F with
    polynomial := fun u i => BoundedCriticalSampleChildParentThom.polynomial F
      (orderContext orders (pair u (BinaryNatCode.encode i)))
    pattern := fun u i => sigma (pair u (BinaryNatCode.encode i))
    count := fun u => BinaryNatCode.encode (features u)
    degree := fun u => BinaryNatCode.encode (BoundedCriticalSampleChildParentThom.degree F (pair u []))
    mass := fun u => BinaryNatCode.encode (BoundedCriticalSampleChildParentThom.mass F (pair u []))
    polynomial_degree := fun u i _ => by
      simpa only [BinaryNatCode.encode, Nat.fromBitsLE_bits, BoundedCriticalSampleChildParentThom.degree,
        BoundedCriticalSampleChildParentThom.exponent, BoundedCriticalSampleChildParentThom.parent,
        BoundedCriticalSampleChildParentThom.child, orderContext, pairFst_pair] using
        BoundedCriticalSampleChildParentThom.polynomial_degree F (orderContext orders (pair u (BinaryNatCode.encode i)))
    polynomial_mass := fun u i _ => by
      simpa only [BinaryNatCode.encode, Nat.fromBitsLE_bits, BoundedCriticalSampleChildParentThom.mass,
        BoundedCriticalSampleChildParentThom.exponent, BoundedCriticalSampleChildParentThom.parent,
        BoundedCriticalSampleChildParentThom.child, orderContext, pairFst_pair] using
        BoundedCriticalSampleChildParentThom.polynomial_mass F (orderContext orders (pair u (BinaryNatCode.encode i))) }

theorem controls {F : Inputs} (h : F.PolyTime) {features : List Bool → ℕ} (hc : UnaryFn features)
    (orders : List Bool → List Bool) (sigma : List Bool → SignType) :
    SignPatternBits.ControlsPolyTime (family F features orders sigma) := by
  have hp : (fun u : List Bool => pair u []) ∈ FP := mem_FP_pair id_mem_FP (constFn_mem_FP [])
  have hd : BinaryFn (fun u => BoundedCriticalSampleChildParentThom.degree F (pair u [])) :=
    (BoundedCriticalSampleChildParentThom.degree_binary h).comp hp
  have hm : BinaryFn (fun u => BoundedCriticalSampleChildParentThom.mass F (pair u [])) :=
    (BoundedCriticalSampleChildParentThom.mass_binary h).comp hp
  constructor
  · exact bits_mem_FP hc
  · simpa only [family, BinaryNatCode.encode, Nat.fromBitsLE_bits] using hc
  · exact (BoundedCriticalSampleChildEquationCount.controls h).rootDegree
  · exact hd.bits_mem_FP
  · exact (BoundedCriticalSampleChildEquationCount.controls h).rootMass
  · exact hm.bits_mem_FP

noncomputable def access (F : Inputs) (features : List Bool → ℕ) (orders : List Bool → List Bool)
    (sigma : List Bool → SignType) : SignPatternBits.Access (family F features orders sigma) where
  rootCoefficient := (BoundedCriticalSampleChildEquationCount.access F).rootCoefficient
  polynomialCoefficient := PrimitivePairBits.coefficient
    (BoundedCriticalSampleChildParentThom.polynomial F ∘ orderContext orders) ∘ BoundedCriticalSampleChildReaders.query
  pattern w := InfinitesimalSign.encode (sigma w)
  root_eq := (BoundedCriticalSampleChildEquationCount.access F).root_eq
  polynomial_eq u i _ k m hm := by
    simp only [Function.comp_apply, PrimitivePairBits.coefficient,
      RationalSubstitution.IntegerBits.coefficientResidue, IntegerTarskiSeedBits.integerResidue]
    exact congrArg₂ (fun (z : ℤ) (m : ℕ) => MatrixPower.residueBits (z : ZMod m))
      (by simp only [BoundedCriticalSampleChildReaders.query, RationalSubstitution.IntegerBits.context,
        RationalSubstitution.IntegerBits.selectedDegree, pairFst_pair, pairSnd_pair,
        BinaryNatCode.encode, Nat.fromBitsLE_bits]; rfl)
      (by simp only [BoundedCriticalSampleChildReaders.query, RationalSubstitution.IntegerBits.mValue,
        pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]; omega)
  pattern_eq _ _ := rfl

theorem coefficient_evaluator {F : Inputs} (h : F.PolyTime) (features : List Bool → ℕ)
    {orders : List Bool → List Bool} (ho : orders ∈ FP) (sigma : List Bool → SignType) :
    SpaceFunction (access F features orders sigma).polynomialCoefficient :=
  (PrimitivePairBits.withContextEvaluator _ (orderContext orders)
    (SpaceFunction.ofFP _ (orderContext_FP ho)) (BoundedCriticalSampleChildParentThom.evaluator h)).precompose
      BoundedCriticalSampleChildReaders.query BoundedCriticalSampleChildReaders.query_FP

theorem patternCount_evaluator {F : Inputs} (h : F.PolyTime) {features : List Bool → ℕ} (hc : UnaryFn features)
    {orders : List Bool → List Bool} (ho : orders ∈ FP) {sigma : List Bool → SignType}
    (hs : (fun w => InfinitesimalSign.encode (sigma w)) ∈ FP) :
    SpaceFunction (fun u => BinaryNatCode.encode
      (BoundedCriticalSampleChildQueries.patternCount F (family F features orders sigma) u)) :=
  BoundedCriticalSampleChildQueries.patternCount_evaluator h (access F features orders sigma)
    (controls h hc orders sigma) hs (coefficient_evaluator h features ho sigma)

noncomputable def moment (F : Inputs) (features : List Bool → ℕ) (orders : List Bool → List Bool) : List Bool → ℤ :=
  BoundedCriticalSampleChildQueries.moment F (family F features orders (fun _ => 0))

theorem moment_evaluator {F : Inputs} (h : F.PolyTime) {features : List Bool → ℕ} (hc : UnaryFn features)
    {orders : List Bool → List Bool} (ho : orders ∈ FP) :
    SpaceFunction (fun u => SignStatisticBits.integerCode (moment F features orders u)) :=
  BoundedCriticalSampleChildQueries.moment_evaluator h (access F features orders (fun _ => 0))
    (controls h hc orders (fun _ => 0)) (coefficient_evaluator h features ho (fun _ => 0))

theorem moment_eq_sum (F : Inputs) (features : List Bool → ℕ) (orders : List Bool → List Bool) (u : List Bool) :
    moment F features orders u = ∑ theta ∈ BoundedCriticalSampleChildQueries.roots F u,
      ∏ i ∈ Finset.range (features u),
        (SignType.sign ((BoundedCriticalSampleThom.polynomial F.parent (pairFst u)
          (Nat.fromBitsLE (orders (pair u (BinaryNatCode.encode i))))).eval₂ (Int.castRingHom ℝ)
            (BoundedCriticalSampleChildParameters.decode F u theta (BoundedCriticalSampleChildParentThom.first F u))) : ℤ) := by
  simp only [moment, BoundedCriticalSampleChildQueries.moment, BoundedCriticalSampleChildQueries.product,
    family, BinaryNatCode.encode, Nat.fromBitsLE_bits, Polynomial.eval_map, algebraMap_int_eq]
  apply Finset.sum_congr rfl
  intro theta ht
  apply Finset.prod_congr rfl
  intro i _
  have he : orderContext orders (pair u i.bits) = pair u
      (BinaryNatCode.encode (Nat.fromBitsLE (orders (pair u i.bits)))) := by
    simp only [orderContext, pairFst_pair, BinaryNat.normalize_eq_bits, BinaryNatCode.encode]
  rw [he, BoundedCriticalSampleChildParentThom.sign F u _ theta
    ((BoundedCriticalSampleChildQueries.mem_roots F u theta).mp ht).1]

end LeanCanny.Encoding.BoundedCriticalSampleChildParentQueries
