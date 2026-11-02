/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.NoInfinitySquareControls
public import LeanCanny.Algebra.ReciprocalCoordinateSpace
public import LeanCanny.Algebra.AffineCoordinateRowsSpace

/-! # Native reciprocal homogeneous rows from the original square-row reader -/
@[expose] public section
namespace LeanCanny.Encoding.NoInfinitySquareSample
open LeanCanny.Algebra LeanCanny.Computation MvPolynomial MatrixPower
open scoped Classical

theorem selected_degree_binary {F : Family} (h : Access F)
    (row : (u : List Bool)→Fin (F.count u)) (hr : UnaryFn (fun u=>(row u).val)) :
    BinaryFn (fun u=>F.rowDegree u (row u).val) :=
  BinaryFn.of_eq (h.rowDegree.comp (mem_FP_pair id_mem_FP (BinaryFn.ofUnary hr).bits_mem_FP))
    (fun u=>by simp only [Function.comp_apply,pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits,id_eq])

theorem integer_evaluator {F : Family} (h : Access F) {W : List Bool→ℕ} (hW : UnaryFn W)
    (row : (u : List Bool)→Fin (F.count u)) (hr : UnaryFn (fun u=>(row u).val))
    {modulus : List Bool→List Bool} (hm : modulus∈FP) :
    SpaceFunction (HomogenizationPolynomialBits.integerValue F.count W (fun u=>F.rows u (row u)) modulus) := by
  have E := h.row.precompose
    (fun q=>SquareSampleInput.query (pairFst q) (BinaryNatCode.encode (row (pairFst q)).val)
      (List.replicate (W (pairFst q)) false) (pairSnd q) (modulus (pairFst q)))
    (SquareSampleInput.query_FP pairFst_mem_FP ((BinaryFn.ofUnary hr).bits_mem_FP.comp pairFst_mem_FP)
      ((hW.comp pairFst_mem_FP).replicate_mem_FP false) pairSnd_mem_FP (mem_FP_comp pairFst_mem_FP hm))
  exact E.congr (funext fun q=>by
    rw [Function.comp_apply,SquareSampleInput.row_packet (input F) _ (row (pairFst q)),List.length_replicate]
    rfl)

theorem homogeneous_evaluator {F : Family} (h : Access F) {W : List Bool→ℕ} (hW : UnaryFn W)
    (row : (u : List Bool)→Fin (F.count u)) (hr : UnaryFn (fun u=>(row u).val))
    {parameter modulus : List Bool→List Bool} (hk : parameter∈FP) (hm : modulus∈FP) :
    SpaceFunction (HomogenizationPolynomialBits.value F.count W (fun u=>F.rowDegree u (row u).val)
      (fun u=>F.rows u (row u)) parameter modulus) :=
  HomogenizationPolynomialBits.evaluator h.count hW (selected_degree_binary h row hr)
    _ parameter modulus hk (integer_evaluator h hW row hr hm)

noncomputable def coordinateSystem (F : Family) (coordinate : (u : List Bool)→Fin (F.count u)) (u : List Bool) :
    Fin (F.count u+1)→MvPolynomial (Fin (F.count u+1)) (Polynomial ℤ) :=
  AffineBoxGramEliminant.system
    (AffineFiniteCoordinates.homogeneousRows (F.rows u) (fun i=>F.rowDegree u i.val)) (coordinate u).succ

noncomputable def coordinateValue (F : Family) (W : List Bool→ℕ)
    (coordinate : (u : List Bool)→Fin (F.count u)) (row : (u : List Bool)→Fin (F.count u+1))
    (parameter modulus : List Bool→List Bool) (q : List Bool) : List Bool :=
  residueBits (((coordinateSystem F coordinate (pairFst q) (row (pairFst q))).coeff
    (FixedWidthPolynomial.nativeExponent (Equiv.refl _) (W (pairFst q)) (Nat.fromBitsLE (pairSnd q)))).coeff
      (Nat.fromBitsLE (parameter (pairFst q))) : ZMod (Nat.fromBitsLE (modulus (pairFst q))+1))

theorem coordinateValue_pair (F : Family) (W : List Bool→ℕ)
    (coordinate : (u : List Bool)→Fin (F.count u)) (row : (u : List Bool)→Fin (F.count u+1))
    (parameter modulus : List Bool→List Bool) (c r : List Bool) :
    coordinateValue F W coordinate row parameter modulus (pair c r)=
      residueBits (((coordinateSystem F coordinate c (row c)).coeff
        (FixedWidthPolynomial.nativeExponent (Equiv.refl _) (W c) (Nat.fromBitsLE r))).coeff
          (Nat.fromBitsLE (parameter c)) : ZMod (Nat.fromBitsLE (modulus c)+1)) := by
  let read (u bits : List Bool) := residueBits (((coordinateSystem F coordinate u (row u)).coeff
    (FixedWidthPolynomial.nativeExponent (Equiv.refl _) (W u) (Nat.fromBitsLE bits))).coeff
      (Nat.fromBitsLE (parameter u)) : ZMod (Nat.fromBitsLE (modulus u)+1))
  change read (pairFst (pair c r)) (pairSnd (pair c r))=read c r
  rw [pairFst_pair,pairSnd_pair]

theorem coordinateSystem_comp (F : Family) (f : List Bool→List Bool)
    (coordinate : (u : List Bool)→Fin (F.count u)) (u : List Bool) :
    coordinateSystem (comp F f) (fun q=>coordinate (f q)) u=coordinateSystem F coordinate (f u) := rfl

theorem coordinate_evaluator {F : Family} (h : Access F) {W : List Bool→ℕ} (hW : UnaryFn W)
    (coordinate : (u : List Bool)→Fin (F.count u)) (hc : UnaryFn (fun u=>(coordinate u).val))
    (row : (u : List Bool)→Fin (F.count u+1)) (hr : UnaryFn (fun u=>(row u).val))
    {parameter modulus : List Bool→List Bool} (hk : parameter∈FP) (hm : modulus∈FP) :
    SpaceFunction (coordinateValue F W coordinate row parameter modulus) := by
  let tail := AffineCoordinateRowsBits.tailRow F.count F.count_pos row
  have ht := AffineCoordinateRowsBits.tailRow_unary h.count F.count_pos row hr
  have EL := ReciprocalCoordinateBits.evaluator h.count hW coordinate hc hk hm
  have ER := homogeneous_evaluator h hW tail ht hk hm
  have hz := FPPred.eq (hr.comp pairFst_mem_FP) (UnaryFn.const 0)
  refine (SpaceFunction.branch _ hz.flag_mem_FP EL ER).congr (funext fun q=>?_)
  simp only [decide_eq_true_eq]
  by_cases hi0 : (row (pairFst q)).val=0
  · rw [ite_eq_left hi0]
    have hrow : row (pairFst q)=0 := Fin.ext hi0
    unfold coordinateValue
    rw [hrow]
    rfl
  · rw [ite_eq_right hi0]
    unfold coordinateValue
    rw [←AffineCoordinateRowsBits.tailRow_succ F.count F.count_pos row (pairFst q) hi0]
    simp only [coordinateSystem,AffineBoxGramEliminant.system,Fin.cases_succ,
      AffineFiniteCoordinates.homogeneousRows,map_rename,WeightedHomogenization.map_homogenize]
    rfl

end LeanCanny.Encoding.NoInfinitySquareSample
