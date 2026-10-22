/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.DyadicPolynomialSpace
public import LeanCanny.Algebra.SignPatternCountSpace

/-! # Uniform sources for root-sign patterns at a dyadic parameter

The root polynomial and indexed query polynomials have polynomial coefficients
in beta. A common dyadic exponent and uniform query bounds give the original
integer sign-pattern interface after positive denominator clearing.
-/

@[expose] public section

namespace LeanCanny.Algebra.DyadicSignPatternBits
open Polynomial
open LeanCanny.Encoding
open LeanCanny.Computation

structure Family where
  root : DyadicPolynomialBits.Family
  polynomial : List Bool → ℕ → (ℤ[X])[X]
  pattern : List Bool → ℕ → SignType
  count : List Bool → List Bool
  degree : List Bool → List Bool
  parameterDegree : List Bool → List Bool
  mass : List Bool → List Bool
  polynomial_degree : ∀ c i, (polynomial c i).natDegree ≤ Nat.fromBitsLE (degree c)
  coefficient_degree : ∀ c i j, ((polynomial c i).coeff j).natDegree ≤ Nat.fromBitsLE (parameterDegree c)
  coefficient_mass : ∀ c i j, coefficientMass ((polynomial c i).coeff j) ≤ 2 ^ Nat.fromBitsLE (mass c)

structure ControlsPolyTime (F : Family) : Prop where
  root : DyadicPolynomialBits.ControlsPolyTime F.root
  count : F.count ∈ FP
  countUnary : UnaryFn (fun c => Nat.fromBitsLE (F.count c))
  degree : F.degree ∈ FP
  parameterDegree : F.parameterDegree ∈ FP
  mass : F.mass ∈ FP

def queryFamily (F : Family) : DyadicPolynomialBits.Family where
  polynomial r := F.polynomial (pairFst r) (Nat.fromBitsLE (pairSnd r))
  degree := F.degree ∘ pairFst
  parameterDegree := F.parameterDegree ∘ pairFst
  exponent := F.root.exponent ∘ pairFst
  mass := F.mass ∘ pairFst
  polynomial_degree r := F.polynomial_degree (pairFst r) _
  coefficient_degree r := F.coefficient_degree (pairFst r) _
  coefficient_mass r := F.coefficient_mass (pairFst r) _

theorem query_controls (F : Family) (hF : ControlsPolyTime F) :
    DyadicPolynomialBits.ControlsPolyTime (queryFamily F) := by
  have hd := mem_FP_comp pairFst_mem_FP hF.degree
  have hp := mem_FP_comp pairFst_mem_FP hF.parameterDegree
  have hs := mem_FP_comp pairFst_mem_FP hF.root.exponent
  have hm := mem_FP_comp pairFst_mem_FP hF.mass
  exact ⟨hd, hp, hs, hm⟩

def queryMassCode (F : Family) (c : List Bool) : List Bool :=
  DyadicPolynomialBits.massCode (queryFamily F) (pair c [])

theorem queryMassCode_mem_FP (F : Family) (hF : ControlsPolyTime F) : queryMassCode F ∈ FP := by
  have h := mem_FP_comp (mem_FP_pair id_mem_FP (constFn_mem_FP []))
    (DyadicPolynomialBits.massCode_mem_FP (queryFamily F) (query_controls F hF))
  refine mem_FP_of_eq (g := queryMassCode F) h ?_
  intro c
  simp only [queryMassCode, Function.comp_apply, id_eq]

theorem query_massCode (F : Family) (c i : List Bool) :
    DyadicPolynomialBits.massCode (queryFamily F) (pair c i) = queryMassCode F c := by
  simp only [DyadicPolynomialBits.massCode, queryFamily, queryMassCode, Function.comp_apply, pairFst_pair]

noncomputable def family (F : Family) : SignPatternBits.Family where
  root := F.root.specialized
  polynomial c i := (queryFamily F).specialized (pair c (BinaryNatCode.encode i))
  pattern := F.pattern
  count := F.count
  rootDegree := BinaryNat.succ ∘ F.root.degree
  degree := F.degree
  rootMass := DyadicPolynomialBits.massCode F.root
  mass := queryMassCode F
  rootDegree_pos c := by simp only [Function.comp_apply, BinaryNat.succ_eq_bits, Nat.fromBitsLE_bits]; omega
  root_degree c := by
    simp only [Function.comp_apply, BinaryNat.succ_eq_bits, Nat.fromBitsLE_bits]
    exact (DyadicPolynomialBits.specialized_degree F.root c).trans (Nat.le_succ _)
  root_mass := DyadicPolynomialBits.specialized_mass F.root
  polynomial_degree c i _ := by
    simpa only [queryFamily, Function.comp_apply, pairFst_pair] using
      DyadicPolynomialBits.specialized_degree (queryFamily F) (pair c (BinaryNatCode.encode i))
  polynomial_mass c i _ := by
    simpa only [query_massCode] using
      DyadicPolynomialBits.specialized_mass (queryFamily F) (pair c (BinaryNatCode.encode i))

theorem controls (F : Family) (hF : ControlsPolyTime F) : SignPatternBits.ControlsPolyTime (family F) := by
  have hd := mem_FP_comp hF.root.degree BinaryNat.succ_mem_FP
  exact ⟨hF.count, hF.countUnary, hd, hF.degree,
    DyadicPolynomialBits.massCode_mem_FP F.root hF.root, queryMassCode_mem_FP F hF⟩

structure Access (F : Family) where
  root : DyadicPolynomialBits.Access F.root
  coefficient : List Bool → List Bool
  pattern : List Bool → List Bool
  coefficient_eq : ∀ c i j k m, 0 < m → coefficient
    (pair (pair c (pair (BinaryNatCode.encode i) (pair (BinaryNatCode.encode j) (BinaryNatCode.encode k))))
      (BinaryNatCode.encode (m - 1))) =
      DyadicBits.integerResidue (((F.polynomial c i).coeff j).coeff k) m
  pattern_eq : ∀ c i, pattern (pair c (BinaryNatCode.encode i)) = InfinitesimalSign.encode (F.pattern c i)

def sourceQuery (p : List Bool) : List Bool :=
  pair (pair (pairFst (pairFst (pairFst p)))
    (pair (BinaryNat.normalize (pairSnd (pairFst (pairFst p)))) (pairSnd (pairFst p)))) (pairSnd p)

theorem sourceQuery_mem_FP : sourceQuery ∈ FP := by
  have hc := mem_FP_comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairFst_mem_FP
  have hi := mem_FP_comp (mem_FP_comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairSnd_mem_FP)
    BinaryNat.normalize_mem_FP
  have hj := mem_FP_comp pairFst_mem_FP pairSnd_mem_FP
  have h := mem_FP_pair (mem_FP_pair hc (mem_FP_pair hi hj)) pairSnd_mem_FP
  refine mem_FP_of_eq (g := sourceQuery) h ?_
  intro p
  simp only [sourceQuery, Function.comp_apply]

def queryAccess {F : Family} (a : Access F) : DyadicPolynomialBits.Access (queryFamily F) where
  coefficient := a.coefficient ∘ sourceQuery
  coefficient_eq := by
    intro r j k m hm
    simp only [Function.comp_apply, sourceQuery, pairFst_pair, pairSnd_pair, BinaryNat.normalize_eq_bits]
    simpa only [queryFamily, BinaryNatCode.encode] using
      a.coefficient_eq (pairFst r) (Nat.fromBitsLE (pairSnd r)) j k m hm

def specializedQuery (p : List Bool) : List Bool :=
  pair (pair (pair (pairFst (pairFst p)) (pairFst (pairSnd (pairFst p))))
    (pairSnd (pairSnd (pairFst p)))) (pairSnd p)

theorem specializedQuery_mem_FP : specializedQuery ∈ FP := by
  have hc := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
  have hi := mem_FP_comp (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) pairFst_mem_FP
  have hj := mem_FP_comp (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) pairSnd_mem_FP
  have h := mem_FP_pair (mem_FP_pair (mem_FP_pair hc hi) hj) pairSnd_mem_FP
  refine mem_FP_of_eq (g := specializedQuery) h ?_
  intro p
  simp only [specializedQuery, Function.comp_apply]

noncomputable def access {F : Family} (a : Access F) : SignPatternBits.Access (family F) where
  rootCoefficient := F.root.residue
  polynomialCoefficient := (queryFamily F).residue ∘ specializedQuery
  pattern := a.pattern
  root_eq c j m hm := DyadicPolynomialBits.residue_packet F.root c j m hm
  polynomial_eq c i _ j m hm := by
    simp only [Function.comp_apply, specializedQuery, pairFst_pair, pairSnd_pair]
    exact DyadicPolynomialBits.residue_packet (queryFamily F) (pair c (BinaryNatCode.encode i)) j m hm
  pattern_eq := a.pattern_eq

theorem queryEvaluator {F : Family} (a : Access F) (hF : ControlsPolyTime F)
    (P : SpaceFunction a.coefficient) : SpaceFunction (access a).polynomialCoefficient :=
  (DyadicPolynomialBits.residueEvaluator (queryAccess a) (query_controls F hF)
    (P.precompose sourceQuery sourceQuery_mem_FP)).precompose specializedQuery specializedQuery_mem_FP

end LeanCanny.Algebra.DyadicSignPatternBits
