/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.SignQueryTarskiSpace
public import LeanCanny.Encoding.TernaryFP

/-! # Indexed sources and ternary queries for finite sign patterns -/

@[expose] public section

namespace LeanCanny.Algebra.SignPatternBits
open Complexity Polynomial
open LeanCanny.Encoding
open LeanCanny.Computation
open scoped BigOperators

structure Family where
  root : List Bool → ℤ[X]
  polynomial : List Bool → ℕ → ℤ[X]
  pattern : List Bool → ℕ → SignType
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
  countUnary : UnaryFn (fun c => Nat.fromBitsLE (F.count c))
  rootDegree : F.rootDegree ∈ FP
  degree : F.degree ∈ FP
  rootMass : F.rootMass ∈ FP
  mass : F.mass ∈ FP

noncomputable def queryFamily (F : Family) : SignQueryBits.Family where
  root := F.root ∘ pairFst
  polynomial q := F.polynomial (pairFst q)
  exponent q i := Ternary.exponent (Nat.fromBitsLE (F.count (pairFst q))) (Nat.fromBitsLE (pairSnd q)) i
  count := F.count ∘ pairFst
  rootDegree := F.rootDegree ∘ pairFst
  degree := F.degree ∘ pairFst
  rootMass := F.rootMass ∘ pairFst
  mass := F.mass ∘ pairFst
  rootDegree_pos q := F.rootDegree_pos (pairFst q)
  root_degree q := F.root_degree (pairFst q)
  root_mass q := F.root_mass (pairFst q)
  polynomial_degree q := F.polynomial_degree (pairFst q)
  polynomial_mass q := F.polynomial_mass (pairFst q)

theorem query_controls (F : Family) (hF : ControlsPolyTime F) : SignQueryBits.ControlsPolyTime (queryFamily F) := by
  have hc := mem_FP_comp pairFst_mem_FP hF.count
  have hr := mem_FP_comp pairFst_mem_FP hF.rootDegree
  have hd := mem_FP_comp pairFst_mem_FP hF.degree
  have hb := mem_FP_comp pairFst_mem_FP hF.rootMass
  have hm := mem_FP_comp pairFst_mem_FP hF.mass
  exact ⟨hc, hr, hd, hb, hm⟩

structure Access (F : Family) where
  rootCoefficient : List Bool → List Bool
  polynomialCoefficient : List Bool → List Bool
  pattern : List Bool → List Bool
  root_eq : ∀ c k m, 0 < m → rootCoefficient
    (pair (pair c (BinaryNatCode.encode k)) (BinaryNatCode.encode (m - 1))) =
      IntegerTarskiSeedBits.integerResidue ((F.root c).coeff k) m
  polynomial_eq : ∀ c i, i < Nat.fromBitsLE (F.count c) → ∀ k m, 0 < m → polynomialCoefficient
    (pair (pair c (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k))) (BinaryNatCode.encode (m - 1))) =
      IntegerTarskiSeedBits.integerResidue ((F.polynomial c i).coeff k) m
  pattern_eq : ∀ c i, pattern (pair c (BinaryNatCode.encode i)) = InfinitesimalSign.encode (F.pattern c i)

def sourceQuery (p : List Bool) : List Bool :=
  pair (pair (pairFst (pairFst (pairFst p))) (pairSnd (pairFst p))) (pairSnd p)
def original (p : List Bool) : List Bool := pairFst (pairFst p)
def queryIndex (p : List Bool) : List Bool := pairSnd (pairFst p)

theorem sourceQuery_mem_FP : sourceQuery ∈ FP :=
  mem_FP_pair (mem_FP_pair (mem_FP_comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairFst_mem_FP)
    (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP)) pairSnd_mem_FP
theorem original_mem_FP : original ∈ FP := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
theorem queryIndex_mem_FP : queryIndex ∈ FP := mem_FP_comp pairFst_mem_FP pairSnd_mem_FP

def queryAccess {F : Family} (a : Access F) : SignQueryBits.Access (queryFamily F) where
  rootCoefficient := a.rootCoefficient ∘ sourceQuery
  polynomialCoefficient := a.polynomialCoefficient ∘ sourceQuery
  exponent p := Ternary.digit (F.count (original p)) (queryIndex p) (pairSnd p)
  root_eq := by
    intro q k m hm
    simpa only [Function.comp_apply, sourceQuery, pairFst_pair, pairSnd_pair, queryFamily] using a.root_eq (pairFst q) k m hm
  polynomial_eq := by
    intro q i hi k m hm
    simpa only [Function.comp_apply, sourceQuery, pairFst_pair, pairSnd_pair, queryFamily] using
      a.polynomial_eq (pairFst q) i hi k m hm
  exponent_eq := by
    intro q i _
    simp only [original, queryIndex, pairFst_pair, pairSnd_pair, Ternary.digit_exponent, BinaryNatCode.encode,
      Nat.fromBitsLE_bits, queryFamily]

theorem queryExponent_mem_FP {F : Family} (a : Access F) (hF : ControlsPolyTime F) : (queryAccess a).exponent ∈ FP := by
  have hk := mem_FP_comp original_mem_FP hF.count
  have hu := hF.countUnary.comp original_mem_FP
  have h := Ternary.digit_mem_FP hk queryIndex_mem_FP pairSnd_mem_FP hu
  refine mem_FP_of_eq (g := (queryAccess a).exponent) h ?_
  intro p
  simp only [queryAccess, Function.comp_apply]

noncomputable def queryEvaluator {F : Family} (a : Access F) (hF : ControlsPolyTime F)
    (H : SpaceFunction a.rootCoefficient) (P : SpaceFunction a.polynomialCoefficient) :
    SpaceFunction (fun q => SignStatisticBits.integerCode ((queryFamily F).value q)) :=
  SignQueryBits.evaluator (queryAccess a) (query_controls F hF) (queryExponent_mem_FP a hF)
    (H.precompose sourceQuery sourceQuery_mem_FP) (P.precompose sourceQuery sourceQuery_mem_FP)

noncomputable def weight (F : Family) (q : List Bool) : ℤ :=
  ∏ i ∈ Finset.range (Nat.fromBitsLE (F.count (pairFst q))),
    RootSignQueries.weight (F.pattern (pairFst q) i)
      (Ternary.exponent (Nat.fromBitsLE (F.count (pairFst q))) (Nat.fromBitsLE (pairSnd q)) i)

noncomputable def scaledCount (F : Family) (c : List Bool) : ℤ := RootSignQueries.scaledRootCount
  ((F.root c).map (algebraMap ℤ ℝ))
  (fun i : Fin (Nat.fromBitsLE (F.count c)) => (F.polynomial c i.val).map (algebraMap ℤ ℝ))
  (fun i => F.pattern c i.val)

end LeanCanny.Algebra.SignPatternBits
