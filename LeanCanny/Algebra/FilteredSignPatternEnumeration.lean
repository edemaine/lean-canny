/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.SignPatternComposition
public import LeanCanny.Algebra.WeightedSignQueries

/-! # Native enumeration of filtered feature sign patterns

The second context field selects a ternary sign pattern. Appending these
constraints to a filter counts the accepted roots with exactly that pattern.
-/

@[expose] public section
namespace LeanCanny.Algebra.SignPatternBits
open Polynomial LeanCanny.Encoding LeanCanny.Computation
open LeanCanny.Encoding.Brackets
open scoped Classical BigOperators

def enumeratedSign (k r i : ℕ) : SignType :=
  SignType.fin3Equiv.symm (Ternary.exponent k r i)

def patternEquiv (k : ℕ) : Fin (3 ^ k) ≃ (Fin k → SignType) :=
  (finFunctionFinEquiv (m := 3) (n := k)).symm.trans
    (Equiv.piCongrRight fun _ => SignType.fin3Equiv.symm.toEquiv)

theorem patternEquiv_apply (k : ℕ) (r : Fin (3 ^ k)) (i : Fin k) :
    patternEquiv k r i = enumeratedSign k r.val i.val := by
  simp only [patternEquiv, Equiv.trans_apply, Equiv.piCongrRight_apply,
    ← Ternary.vector_eq_symm, enumeratedSign, Ternary.exponent_fin]
  rfl

def signCode (t : List Bool) : List Bool :=
  if t = [] then [] else if t = [true] then [false, true] else [true]

theorem signCode_trit (t : Fin 3) :
    signCode (BinaryNatCode.encode t.val) = InfinitesimalSign.encode (SignType.fin3Equiv.symm t) := by
  fin_cases t <;> rfl

theorem signCode_FP : signCode ∈ FP :=
  (stringEq_fppred id_mem_FP (constFn_mem_FP [])).ite_mem_FP (constFn_mem_FP [])
    ((stringEq_fppred id_mem_FP (constFn_mem_FP [true])).ite_mem_FP
      (constFn_mem_FP [false, true]) (constFn_mem_FP [true]))

def Family.enumerate (G : Family) : Family :=
  { G.comp pairFst with
    pattern := fun c i => enumeratedSign (Nat.fromBitsLE (G.count (pairFst c)))
      (Nat.fromBitsLE (pairSnd c)) i }

theorem enumerate_controls {G : Family} (hG : ControlsPolyTime G) : ControlsPolyTime G.enumerate := by
  have h := comp_controls hG pairFst_mem_FP
  exact ⟨h.count, h.countUnary, h.rootDegree, h.degree, h.rootMass, h.mass⟩

def enumeratedPattern (G : Family) (q : List Bool) : List Bool :=
  signCode (Ternary.digit (G.count (original q)) (queryIndex q) (pairSnd q))

theorem enumeratedPattern_FP {G : Family} (hG : ControlsPolyTime G) : enumeratedPattern G ∈ FP :=
  mem_FP_comp (Ternary.digit_mem_FP (mem_FP_comp original_mem_FP hG.count)
    queryIndex_mem_FP pairSnd_mem_FP (hG.countUnary.comp original_mem_FP)) signCode_FP

def Access.enumerate {G : Family} (A : Access G) : Access G.enumerate where
  rootCoefficient := (A.comp pairFst).rootCoefficient
  polynomialCoefficient := (A.comp pairFst).polynomialCoefficient
  pattern := enumeratedPattern G
  root_eq := (A.comp pairFst).root_eq
  polynomial_eq := (A.comp pairFst).polynomial_eq
  pattern_eq c i := by
    simp only [enumeratedPattern, original, queryIndex, pairFst_pair, pairSnd_pair,
      Ternary.digit_exponent, BinaryNatCode.encode, Nat.fromBitsLE_bits, Family.enumerate,
      enumeratedSign]
    exact signCode_trit _

noncomputable def acceptedRoots (F : Family) (c : List Bool) : Finset ℝ :=
  (((F.root c).map (algebraMap ℤ ℝ)).roots.toFinset).filter fun x =>
    ∀ i, i < Nat.fromBitsLE (F.count c) →
      SignType.sign (((F.polynomial c i).map (algebraMap ℤ ℝ)).eval x) = F.pattern c i

theorem rootCount_eq_card (F : Family) (c : List Bool) :
    rootCount F c = (acceptedRoots F c).card := by
  unfold rootCount RootSignQueries.signCount acceptedRoots
  congr 1
  ext x
  simp only [Finset.mem_filter, Fin.forall_iff]

theorem enumeratedCount_eq (F G : Family) (c : List Bool) (r : ℕ) :
    rootCount ((F.comp pairFst).append G.enumerate) (pair c (BinaryNatCode.encode r)) =
      RootSignQueries.signCount (acceptedRoots F c)
        (fun i : Fin (Nat.fromBitsLE (G.count c)) => (G.polynomial c i.val).map (algebraMap ℤ ℝ))
        (fun i => enumeratedSign (Nat.fromBitsLE (G.count c)) r i.val) := by
  rw [rootCount_eq_card]
  unfold RootSignQueries.signCount
  congr 1
  ext x
  simp only [acceptedRoots, Finset.mem_filter, Fin.forall_iff]
  rw [append_signs]
  simp only [Family.comp, Family.enumerate, Function.comp_apply, pairFst_pair, pairSnd_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits, Family.append]
  tauto

end LeanCanny.Algebra.SignPatternBits
