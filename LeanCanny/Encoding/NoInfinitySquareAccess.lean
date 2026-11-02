/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.NoInfinitySquareGram

/-! # Complete native square sampling from original row access

All coefficient evaluation charges the supplied original row SpaceFunction.
No annihilator reader, Jacobian certificate or row-validity oracle is assumed.
-/
@[expose] public section
namespace LeanCanny.Encoding.NoInfinitySquareSample
open LeanCanny.Algebra LeanCanny.Computation MatrixPower
open scoped Classical

noncomputable def row (F : Family) (q : List Bool) : Fin (F.count (SquareSampleInput.source q)) :=
  SquareSampleInput.selected (input F) (SquareSampleInput.source q) (SquareSampleInput.indexWord q)

theorem row_unary {F : Family} (h : Access F) : UnaryFn (fun q=>(row F q).val) :=
  UnaryFn.fromBitsLE_min SquareSampleInput.indexWord_FP
    ((h.count.comp SquareSampleInput.source_FP).sub (UnaryFn.const 1))

private theorem coefficient_pair (p : List Bool→Polynomial ℤ) (c r m : List Bool) :
    PrimitivePairBits.coefficient p (pair (pair c r) m)=
      residueBits ((p c).coeff (Nat.fromBitsLE r) : ZMod (Nat.fromBitsLE m+1)) := by
  simp only [PrimitivePairBits.coefficient,RationalSubstitution.IntegerBits.context,
    RationalSubstitution.IntegerBits.selectedDegree,RationalSubstitution.IntegerBits.mValue,
    pairFst_pair,pairSnd_pair]
  rfl

theorem ann_evaluator {F : Family} (h : Access F) :
    SpaceFunction (SquareSampleInput.annCoefficient (input F)) := by
  have E := NoInfinitySquareGram.annihilator_evaluator (access_comp h SquareSampleInput.source_FP)
    (row F) (row_unary h)
  let prepare (q : List Bool) := pair (pair q (SquareSampleInput.rankWord q)) (SquareSampleInput.modulusWord q)
  have hp : prepare∈FP := mem_FP_pair (mem_FP_pair id_mem_FP SquareSampleInput.rankWord_FP) SquareSampleInput.modulusWord_FP
  refine (E.precompose prepare hp).congr (funext fun q=>?_)
  simp only [Function.comp_apply,prepare,coefficient_pair,NoInfinitySquareGram.annihilator_eq]
  rfl

theorem access {F : Family} (h : Access F) : (input F).Access :=
  ⟨h.count,h.degree,h.mass,annDegree_binary h,annHeight_binary h,h.row,ann_evaluator h⟩

theorem count_evaluator {F : Family} (h : Access F) :
    SpaceFunction (fun u=>BinaryNatCode.encode (SquareSampleComplete.count (input F) u)) :=
  SquareSampleComplete.count_evaluator (access h) (complete F)

theorem language_mem_PSPACE {F : Family} (h : Access F) :
    {u | ∃ z : Fin (F.count u)→ℝ,∀ i,(F.rows u i).eval₂ (Int.castRingHom ℝ) z=0}∈PSPACE :=
  SquareSampleComplete.language_mem_PSPACE (access h) (complete F)

end LeanCanny.Encoding.NoInfinitySquareSample
