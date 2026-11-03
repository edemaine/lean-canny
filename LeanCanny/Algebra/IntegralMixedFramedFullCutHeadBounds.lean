/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedFullCutHeadSpace
/-! # Original degree, mass and arity controls for full relative cut heads -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedFullCutHead
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (parent : List Bool→List Bool)

theorem saved_FP (a : Access P) (hp : parent∈FP) : saved P parent∈FP:=
  mem_FP_comp hp (IntegralMixedVirtualTaskBits.saved_FP P a)

theorem arity_unary (a : Access P) (hp : parent∈FP) : UnaryFn (arity P D H parent) :=
  ((IntegralMixedFullHistoryFamilyBits.prefix_unary P a).comp (saved_FP P parent a hp)).of_eq
    (fun c=>(IntegralMixedFramedHistoryFamilyBits.family_birth P D H (saved P parent c)).symm)

noncomputable def headDegree (c : List Bool) :=coefficientDegree P D H (saved P parent c)
noncomputable def headMass (L F C : List Bool→ℕ) (c : List Bool) :=coefficientMass P D H L F C (saved P parent c)

theorem headDegree_binary (a : Access P) (hp : parent∈FP) : BinaryFn (headDegree P D H parent) :=by
  have HD : BinaryFn (fun c=>IntegralMixedFramedCutCoefficientBits.degree P D H (pair (saved P parent c) (BinaryNatCode.encode 0))) :=
    (IntegralMixedFramedCutCoefficientBits.degree_binary P a D H).comp
    (mem_FP_pair (saved_FP P parent a hp) (constFn_mem_FP (BinaryNatCode.encode 0)))
  exact HD.of_eq (fun c=>by
    simp only [IntegralMixedFramedCutCoefficientBits.degree,IntegralMixedFramedCutCoefficientBits.source,
      IntegralMixedFramedCutCoefficientBits.horizon,IntegralMixedFramedCutCoefficientBits.key,pairFst_pair,
      headDegree,coefficientDegree])

theorem headMass_binary (a : Access P) (L F C : List Bool→ℕ)
    (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C) (hp : parent∈FP) : BinaryFn (headMass P D H parent L F C) :=by
  have HM : BinaryFn (fun c=>IntegralMixedFramedCutCoefficientBits.massBound P D H L F C (pair (saved P parent c) (BinaryNatCode.encode 0))) :=
    (IntegralMixedFramedCutCoefficientBits.massBound_binary P a D H L F C hL hF hC).comp
    (mem_FP_pair (saved_FP P parent a hp) (constFn_mem_FP (BinaryNatCode.encode 0)))
  exact HM.of_eq (fun c=>by
    simp only [IntegralMixedFramedCutCoefficientBits.massBound,IntegralMixedFramedCutCoefficientBits.source,
      IntegralMixedFramedCutCoefficientBits.key,pairFst_pair,headMass,coefficientMass])

theorem head_coefficient_degree (d : List Bool→ℕ) (c : List Bool) (k : ℕ) :
    ((head P D H parent d c).coeff k).totalDegree≤headDegree P D H parent c :=by
  rw [head_coefficient]
  split_ifs
  · exact coefficient_degree P D H (saved P parent c) k
  · simp only [MvPolynomial.totalDegree_zero]
    exact Nat.zero_le _

theorem head_coefficient_mass (d : List Bool→ℕ) (L F C : List Bool→ℕ)
    (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
    (hF : ∀root,1≤F root) (hf : ∀old,IntegralMixedFramedOriginalBounds.FallbackBounds P D H L C old)
    (c : List Bool) (k : ℕ) : MvMass.mass ((head P D H parent d c).coeff k)≤2^headMass P D H parent L F C c :=by
  rw [head_coefficient]
  split_ifs
  · exact coefficient_mass P D H L F C hs hF hf (saved P parent c) k
  · simp only [MvMass.zero]
    exact Nat.zero_le _

end LeanCanny.Algebra.IntegralMixedFramedFullCutHead
