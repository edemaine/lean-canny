/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.SignQueryProductSpace
public import LeanCanny.Algebra.SignQueryBudget
public import LeanCanny.Algebra.TarskiQueryPSPACE

/-! # Original polynomial families for product Tarski queries -/

@[expose] public section

namespace LeanCanny.Algebra.SignQueryBits
open Complexity Polynomial
open LeanCanny.Encoding
open LeanCanny.Computation
open scoped BigOperators

structure Family where
  root : List Bool → ℤ[X]
  polynomial : List Bool → ℕ → ℤ[X]
  exponent : List Bool → ℕ → Fin 3
  count : List Bool → List Bool
  rootDegree : List Bool → List Bool
  degree : List Bool → List Bool
  rootMass : List Bool → List Bool
  mass : List Bool → List Bool
  rootDegree_pos : ∀ c, 0 < Nat.fromBitsLE (rootDegree c)
  root_degree : ∀ c, (root c).natDegree ≤ Nat.fromBitsLE (rootDegree c)
  root_mass : ∀ c, coefficientMass (root c) ≤ 2 ^ Nat.fromBitsLE (rootMass c)
  polynomial_degree : ∀ c i, i < Nat.fromBitsLE (count c) → (polynomial c i).natDegree ≤ Nat.fromBitsLE (degree c)
  polynomial_mass : ∀ c i, i < Nat.fromBitsLE (count c) → coefficientMass (polynomial c i) ≤ 2 ^ Nat.fromBitsLE (mass c)

structure ControlsPolyTime (F : Family) : Prop where
  count : F.count ∈ FP
  rootDegree : F.rootDegree ∈ FP
  degree : F.degree ∈ FP
  rootMass : F.rootMass ∈ FP
  mass : F.mass ∈ FP

noncomputable def Family.product (F : Family) (c : List Bool) : ℤ[X] :=
  ∏ i ∈ Finset.range (Nat.fromBitsLE (F.count c)), F.polynomial c i ^ (F.exponent c i).val

theorem Family.product_degree (F : Family) (c : List Bool) :
    (F.product c).natDegree ≤ Nat.fromBitsLE (RootSignQueries.queryDegreeCode (F.count c) (F.degree c)) := by
  have h := RootSignQueries.natDegree_queryPolynomial_le
    (fun i : Fin (Nat.fromBitsLE (F.count c)) => F.polynomial c i.val)
    (fun i => F.exponent c i.val) _ (fun i => F.polynomial_degree c i.val i.isLt)
  change (∏ i : Fin (Nat.fromBitsLE (F.count c)), F.polynomial c i.val ^ (F.exponent c i.val).val).natDegree ≤ _ at h
  rw [Fin.prod_univ_eq_prod_range (fun i => F.polynomial c i ^ (F.exponent c i).val)] at h
  simpa only [Family.product,
    Fintype.card_fin, RootSignQueries.queryDegreeCode_eq, BinaryNatCode.encode, Nat.fromBitsLE_bits] using h

theorem Family.product_mass (F : Family) (c : List Bool) :
    coefficientMass (F.product c) ≤ 2 ^ Nat.fromBitsLE (RootSignQueries.queryDegreeCode (F.count c) (F.mass c)) := by
  have h := RootSignQueries.coefficientMass_queryPolynomial_le
    (fun i : Fin (Nat.fromBitsLE (F.count c)) => F.polynomial c i.val)
    (fun i => F.exponent c i.val) _ (fun i => F.polynomial_mass c i.val i.isLt)
  change coefficientMass (∏ i : Fin (Nat.fromBitsLE (F.count c)), F.polynomial c i.val ^ (F.exponent c i.val).val) ≤ _ at h
  rw [Fin.prod_univ_eq_prod_range (fun i => F.polynomial c i ^ (F.exponent c i).val)] at h
  simpa only [Family.product,
    Fintype.card_fin, RootSignQueries.queryDegreeCode_eq, BinaryNatCode.encode, Nat.fromBitsLE_bits] using h

noncomputable def Family.tarski (F : Family) : IntegerTarskiSeedBits.Family where
  head := F.root
  query := F.product
  degree := F.rootDegree
  queryBound c := RootSignQueries.queryDegreeCode (F.count c) (F.degree c)
  headMass := F.rootMass
  queryMass c := RootSignQueries.queryDegreeCode (F.count c) (F.mass c)
  degree_pos := F.rootDegree_pos
  head_degree := F.root_degree
  query_degree := F.product_degree
  head_mass := F.root_mass
  query_mass := F.product_mass

theorem tarski_controls (F : Family) (hF : ControlsPolyTime F) : IntegerTarskiSeedBits.ControlsPolyTime F.tarski := by
  have hd := RootSignQueries.queryDegreeCode_mem_FP hF.count hF.degree
  have hb := RootSignQueries.queryDegreeCode_mem_FP hF.count hF.mass
  constructor
  · simpa only [Family.tarski] using hF.rootDegree
  · simpa only [Family.tarski] using hd
  · simpa only [Family.tarski] using hF.rootMass
  · simpa only [Family.tarski] using hb

structure Access (F : Family) where
  rootCoefficient : List Bool → List Bool
  polynomialCoefficient : List Bool → List Bool
  exponent : List Bool → List Bool
  root_eq : ∀ c k m, 0 < m → rootCoefficient
    (pair (pair c (BinaryNatCode.encode k)) (BinaryNatCode.encode (m - 1))) =
      IntegerTarskiSeedBits.integerResidue ((F.root c).coeff k) m
  polynomial_eq : ∀ c i, i < Nat.fromBitsLE (F.count c) → ∀ k m, 0 < m → polynomialCoefficient
    (pair (pair c (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k))) (BinaryNatCode.encode (m - 1))) =
      IntegerTarskiSeedBits.integerResidue ((F.polynomial c i).coeff k) m
  exponent_eq : ∀ c i, i < Nat.fromBitsLE (F.count c) →
    Nat.fromBitsLE (exponent (pair c (BinaryNatCode.encode i))) = (F.exponent c i).val

end LeanCanny.Algebra.SignQueryBits
