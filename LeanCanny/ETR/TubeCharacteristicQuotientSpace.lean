/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeCharacteristicQuotient
public import LeanCanny.Algebra.IntegerSumSpace
public import LeanCanny.Computation.SpaceFunctionPair

/-! # Polynomial-space access to the true characteristic quotient's lowest data

Both complete index computations supply the signed order difference. Removing
inactive padding also preserves the certified lowest numerator scalar signs.
These are rational-quotient data; polynomiality is not assumed or proved here.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeCharacteristicQuotient
open Complexity LeanCanny.Encoding LeanCanny.Computation LeanCanny.Algebra

attribute [local irreducible] RationalSubstitutionBits.compiledTerm numeratorScalar order

noncomputable def orderCode (source active : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ) (c : List Bool) : List Bool :=
  SignStatisticBits.integerCode (order source active n d ell c)

noncomputable def orderEvaluator {source active modulus inner middle : List Bool → List Bool}
    {n d : List Bool → ℕ → Polynomial ℤ} {ell : List Bool → ℕ → ℤ}
    (D : TubeBivariate.Data source active modulus inner middle n d ell) :
    SpaceFunction (orderCode source active n d ell) := by
  have E := (TubeDeformation.lowestIndexEvaluator D).pairOutputs (TubeExtraneous.lowestIndexEvaluator D)
  have F := E.postcompose IntegerSumBits.difference IntegerSumBits.difference_mem_FP
  refine F.congr (funext fun c => ?_)
  change IntegerSumBits.difference (pair (TubeDeformation.lowestIndex source active n d ell c)
    (TubeExtraneous.lowestIndex source active n d ell c)) = _
  simp only [TubeDeformation.lowestIndex, TubeExtraneous.lowestIndex, IntegerSumBits.difference_parts,
    orderCode, order_eq, MacaulayBits.fromBits_encode]

theorem negativeOrder_mem_PSPACE {source active modulus inner middle : List Bool → List Bool}
    {n d : List Bool → ℕ → Polynomial ℤ} {ell : List Bool → ℕ → ℤ}
    (D : TubeBivariate.Data source active modulus inner middle n d ell) :
    {c | order source active n d ell c < 0} ∈ PSPACE := by
  have hf := (BinaryNat.lt_fppred pairFst_mem_FP pairSnd_mem_FP).flag_mem_FP
  apply SpaceDecider.mem_PSPACE
  refine (orderEvaluator D).decider
    (fun w => decide (Nat.fromBitsLE (pairFst w) < Nat.fromBitsLE (pairSnd w))) hf ?_
  intro c
  simp only [Set.mem_ofPred_eq, orderCode, SignStatisticBits.integerCode, pairFst_pair, pairSnd_pair,
    MacaulayBits.fromBits_encode, decide_eq_true_eq]
  omega

noncomputable def numeratorSign (source active inner middle : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ) (c : List Bool) : List Bool :=
  InfinitesimalSign.tag (numeratorScalar source active inner middle n d ell c)

noncomputable def numeratorSignEvaluator {source active modulus inner middle : List Bool → List Bool}
    {n d : List Bool → ℕ → Polynomial ℤ} {ell : List Bool → ℕ → ℤ}
    (D : TubeBivariate.Data source active modulus inner middle n d ell) :
    SpaceFunction (numeratorSign source active inner middle n d ell) := by
  have E := TubeDeformation.characteristicSignEvaluator D
  exact E.congr (funext fun c => by rw [TubeDeformation.characteristicSign, numeratorSign, numeratorScalar_eq])

end LeanCanny.ETR.TubeCharacteristicQuotient
