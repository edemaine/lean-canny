/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.NoInfinitySquareSample
public import LeanCanny.Algebra.MacaulayFullBoxDeterminantSpace

/-! # Original numeric controls derive the complete reciprocal Gram layout -/
@[expose] public section
namespace LeanCanny.Encoding.NoInfinitySquareSample
open LeanCanny.Algebra LeanCanny.Computation
open scoped Classical BigOperators

abbrev layout (F : Family) : MacaulayFullBoxBits.Layout where
  arity u := F.count u+1
  width := width F
  level u := Macaulay.level (AffineBoxGramEliminant.degrees (fun i : Fin (F.count u)=>F.rowDegree u i.val))
  degree u i := if i=0 then 1 else F.rowDegree u (i-1)

theorem degrees_eq (F : Family) (u : List Bool) :
    (fun i : Fin ((layout F).arity u)=>(layout F).degree u i.val)=
      AffineBoxGramEliminant.degrees (fun i : Fin (F.count u)=>F.rowDegree u i.val) := by
  funext i
  refine Fin.cases ?_ (fun j=>?_) i <;> simp [layout,AffineBoxGramEliminant.degrees]

theorem level_eq (F : Family) (u : List Bool) :
    (layout F).level u=Macaulay.level (fun i : Fin ((layout F).arity u)=>(layout F).degree u i.val) := by
  rw [degrees_eq]

theorem level_binary {F : Family} (h : Access F) : BinaryFn (layout F).level := by
  have hi := bits_mem_FP UnaryFn.index
  have hr : BinaryFn (fun q=>F.rowDegree (pairFst q) (pairSnd q).length) :=
    BinaryFn.of_eq (h.rowDegree.comp (mem_FP_pair pairFst_mem_FP hi)) (fun q=>by
      simp only [Function.comp_apply,pairFst_pair,pairSnd_pair,Nat.fromBitsLE_bits])
  have HS := (BinaryFn.sum h.count (hr.sub (BinaryFn.const 1))).add (BinaryFn.const 1)
  apply BinaryFn.of_eq HS
  intro u
  simp only [Macaulay.level,AffineBoxGramEliminant.degrees,Fin.sum_univ_succ,
    Fin.cases_zero,Fin.cases_succ,Nat.sub_self,zero_add,pairFst_pair,pairSnd_pair,List.length_replicate]
  exact congrArg (fun z=>z+1) (Fin.sum_univ_eq_sum_range (fun i=>F.rowDegree u i-1) (F.count u)).symm

theorem width_unary {F : Family} (h : Access F) : UnaryFn (width F) :=
  UnaryFn.of_eq (UnaryFn.length (level_binary h).bits_mem_FP) (fun _=>BinaryNatCode.length_encode _)

theorem controls {F : Family} (h : Access F) : (layout F).Controls := by
  refine ⟨h.count.add (UnaryFn.const 1),width_unary h,level_binary h,?_⟩
  have hn := (BinaryFn.fromBits pairSnd_mem_FP).sub (BinaryFn.const 1)
  have HT := h.rowDegree.comp (mem_FP_pair pairFst_mem_FP hn.bits_mem_FP)
  have HE : BinaryFn (fun q=>F.rowDegree (pairFst q) (Nat.fromBitsLE (pairSnd q)-1)) :=
    BinaryFn.of_eq HT (fun q=>by simp only [Function.comp_apply,pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits])
  exact BinaryFn.of_eq (BinaryFn.ite ((BinaryFn.fromBits pairSnd_mem_FP).eq (BinaryFn.const 0))
    (BinaryFn.const 1) HE) (fun _=>rfl)

theorem dimension_binary {F : Family} (h : Access F) : BinaryFn (dimension F) := by
  have HE := (h.count.add (UnaryFn.const 1)).mul (width_unary h)
  have HD := (BinaryFn.ofUnary (h.count.add (UnaryFn.const 3))).mul ((BinaryFn.const 2).powUnary HE)
  exact BinaryFn.of_eq HD (fun u=>by
    unfold dimension AffineFiniteCoordinates.dimension AffineBoxGramEliminant.dimension FixedWidthPolynomial.count
    rw [←pow_mul]
    change (F.count u+3)*2^((F.count u+1)*width F u)=
      (F.count u+3)*2^(width F u*(F.count u+1))
    rw [Nat.mul_comm (width F u) (F.count u+1)])

theorem annDegree_binary {F : Family} (h : Access F) : BinaryFn (annDegree F) :=
  (dimension_binary h).add (BinaryFn.const 1)

theorem annHeight_binary {F : Family} (h : Access F) : BinaryFn (annHeight F) :=
  (((dimension_binary h).size.mul (dimension_binary h)).add
    ((dimension_binary h).mul (h.mass.add (BinaryFn.const 1)))).add (BinaryFn.const 1)

end LeanCanny.Encoding.NoInfinitySquareSample
