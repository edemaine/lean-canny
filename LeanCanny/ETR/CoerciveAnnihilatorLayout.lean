/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.CoerciveHomogeneousRowReader
public import LeanCanny.Algebra.CoerciveHomogeneousLayout
public import LeanCanny.Algebra.MacaulayFullBoxDeterminantSpace
public import LeanCanny.ETR.CoerciveAnnihilatorControls

/-! # Native metadata and rows for the actual canonical coordinate eliminants -/

@[expose] public section
namespace LeanCanny.ETR.CoerciveAnnihilatorLayout
open LeanCanny.Encoding LeanCanny.Computation LeanCanny.Algebra
open CoerciveSourceSampling CoerciveCriticalHomogenization
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] RationalSubstitutionBits.compiledTerm

noncomputable def layout (input : List Bool → List Bool) : MacaulayFullBoxBits.Layout where
  arity c := dimension (input c) + 1
  width c := CoerciveHomogeneousRepack.width (input c)
  level c := dimension (input c) * (2 * degreeAllowance (input c)) + 1
  degree c i := if i = 0 then 1 else 2 * degreeAllowance (input c) + 1

lemma controls {input : List Bool → List Bool} (hi : input ∈ FP) : (layout input).Controls := by
  have hn := dimension_unary.comp hi
  have hd := degreeAllowance_unary.comp hi
  have heq : FPPred (fun q => Nat.fromBitsLE (pairSnd q) = 0) :=
    (BinaryNat.le_fppred pairSnd_mem_FP (constFn_mem_FP [])).of_iff (fun _ => by change _ ≤ 0 ↔ _; omega)
  refine ⟨hn.add (UnaryFn.const 1), CoerciveHomogeneousRepack.width_unary.comp hi,
    (hn.mul ((UnaryFn.const 2).mul hd)).add (UnaryFn.const 1), ?_⟩
  apply BinaryFn.of_bits
  exact bits_mem_FP (UnaryFn.ite heq (UnaryFn.const 1)
    ((((UnaryFn.const 2).mul hd).add (UnaryFn.const 1)).comp pairFst_mem_FP))

lemma degrees (input : List Bool → List Bool) (c : List Bool) :
    (fun i : Fin ((layout input).arity c) => (layout input).degree c i.val) =
      finDegree (n := dimension (input c)) (degreeAllowance (input c)) := by
  funext i
  exact (CoerciveHomogeneousLayout.finDegree_eq _ i).symm

lemma level_eq (input : List Bool → List Bool) (c : List Bool) :
    (layout input).level c = Macaulay.level (fun i : Fin ((layout input).arity c) => (layout input).degree c i.val) := by
  rw [degrees]
  exact (CoerciveSourceControls.level_eq (dimension (input c)) (degreeAllowance (input c))).symm

noncomputable def family (input : List Bool → List Bool) (coordinate : List Bool → ℕ) (c : List Bool) :
    Fin ((layout input).arity c) → MvPolynomial (Fin ((layout input).arity c)) CoerciveCriticalHomogenization.Coefficient :=
  if hc : coordinate c < dimension (input c) then
    finSystem (polynomial (input c)) (degreeAllowance (input c)) ⟨coordinate c,hc⟩ else fun _ => 0

lemma family_inner_degree (input : List Bool → List Bool) (coordinate : List Bool → ℕ)
    (c : List Bool) (i : Fin ((layout input).arity c)) (e : Fin ((layout input).arity c) →₀ ℕ) (k : ℕ) :
    (((family input coordinate c i).coeff e).coeff k).natDegree ≤ 1 := by
  unfold family
  split_ifs with hc
  · exact (CoerciveCriticalBounds.finSystem_entryBounds _ _ (polynomial_degree (input c)) ⟨coordinate c,hc⟩ i e).innerDegree k
  · simp

lemma determinant_eq (input : List Bool → List Bool) (coordinate : List Bool → ℕ)
    (c : List Bool) (hc : coordinate c < dimension (input c)) :
    ProjectiveBoxGramEliminant.polynomial (family input coordinate c)
      (fun i => (layout input).degree c i.val) ((layout input).width c) =
      CoerciveBoxGramEliminant.polynomial (polynomial (input c)) (degreeAllowance (input c)) ⟨coordinate c,hc⟩ := by
  rw [family, dite_eq_left hc, degrees]
  rfl

end LeanCanny.ETR.CoerciveAnnihilatorLayout
