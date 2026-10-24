/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeRegularJacobianBudget
public import LeanCanny.ETR.TubeRegularFiniteSigns
public import LeanCanny.Algebra.FixedWidthDerivativeSpace
public import LeanCanny.Algebra.FixedWidthDeterminantSpace

/-! # Native coefficient access for the actual regular tube Jacobian

Regular row codes provide a finite square matrix layout. A native derivative
reader uses one original regular-equation coefficient call; fixed-width
Kronecker substitution and Berkowitz compute its determinant coefficients.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeRegularJacobianBits
open LeanCanny.Encoding LeanCanny.Computation LeanCanny.Algebra MatrixPower
open Geometry TubeEncoding TubeProjectionEncoding
open scoped Classical
attribute [local irreducible] RationalSubstitutionBits.compiledTerm TubeRegularSource.polynomial
set_option backward.isDefEq.respectTransparency false

noncomputable def order (bits : List Bool) : ℕ := pointCount (TubeIndexed.arity bits) + 1
noncomputable def arity (bits : List Bool) : ℕ := TubeIndexed.projectionDimension bits + 1

def bound (bits : List Bool) : ℕ := max (TubeRegularJacobianBudget.degreeBudget bits) (TubeIndexed.degreeBound bits)
def width (bits : List Bool) : ℕ := (bound bits).size

theorem order_unary : UnaryFn order :=
  (TubeProjectionQuery.pointCount_unary TubeIndexed.arity_unary).add (UnaryFn.const 1)
theorem arity_unary : UnaryFn arity := TubeIndexed.projectionDimension_unary.add (UnaryFn.const 1)
theorem bound_unary : UnaryFn bound := TubeRegularJacobianBudget.degreeBudget_unary.max TubeIndexed.degreeBound_unary
theorem width_unary : UnaryFn width := bound_unary.size

theorem bound_lt (bits : List Bool) : bound bits < 2 ^ width bits := Nat.lt_size_self _

noncomputable def rowCode (bits : List Bool) (i : TubeRegularSource.Index bits) : ℕ :=
  TubeRegularFiniteSigns.rowCode id bits i

theorem rowCode_lt (bits : List Bool) (i : TubeRegularSource.Index bits) : rowCode bits i < order bits :=
  TubeRegularFiniteSigns.rowCode_lt id (fun _ => []) bits i

theorem rowCode_injective (bits : List Bool) : Function.Injective (rowCode bits) := by
  intro i j h
  have hi := TubeRegularFiniteSigns.row_rowCode id bits i
  have hj := TubeRegularFiniteSigns.row_rowCode id bits j
  rw [show TubeRegularFiniteSigns.rowCode id bits i = TubeRegularFiniteSigns.rowCode id bits j from h] at hi
  exact hi.symm.trans hj

noncomputable def rowEquiv (bits : List Bool) : TubeRegularSource.Index bits ≃ Fin (order bits) :=
  Equiv.ofBijective (fun i => ⟨rowCode bits i, rowCode_lt bits i⟩)
    ((Fintype.bijective_iff_injective_and_card _).mpr ⟨fun _ _ h => rowCode_injective bits (congrArg Fin.val h), by
      rw [Fintype.card_fin, Fintype.card_option, TubePolynomial.projection_count]
      unfold order TubeIndexed.arity pointCount constraintCount
      simp only [Fintype.card_fin]
      omega⟩)

theorem rowEquiv_value (bits : List Bool) (i : TubeRegularSource.Index bits) :
    (rowEquiv bits i).val = rowCode bits i := rfl

def column (n k : ℕ) : ℕ := if k = 0 then 0 else if k = 1 then n + 1 else TubeProjectionRow.selected n (k - 1) + 1

private theorem output_none (bits : List Bool) : (TubeHomogenization.outputEquiv bits none).val = 0 := by
  unfold TubeHomogenization.outputEquiv
  exact HomogenizationLayout.variableEquiv_none _

private theorem output_point (bits : List Bool) (i : Point (TubeIndexed.arity bits)) :
    (TubeHomogenization.outputEquiv bits (some (.inl (.inl i)))).val =
      (pointEquiv (TubeIndexed.arity bits) i).val + 1 := by
  change (HomogenizationLayout.variableEquiv (variableEquiv (TubeIndexed.arity bits))
    (some (.inl (.inl i)))).val = _
  rw [HomogenizationLayout.variableEquiv_some, TubeProjectionEncoding.index_point]

theorem column_code (bits : List Bool) (j : TubeRegularSource.Index bits) :
    column (TubeIndexed.arity bits) (rowCode bits j) =
      (TubeHomogenization.outputEquiv bits (TubeRegularJacobianBudget.coordinate bits j)).val := by
  cases j with
  | none => change column _ 0 = (TubeHomogenization.outputEquiv bits none).val; rw [output_none]; simp [column]
  | some j =>
    cases j with
    | none =>
      change column (TubeIndexed.arity bits) 1 =
        (TubeHomogenization.outputEquiv bits (some (.inl (.inl (TubePolynomial.base _))))).val
      rw [output_point bits (TubePolynomial.base (Fin (CompactSource.term bits).arity))]
      dsimp only [TubeIndexed.arity]
      rw [TubeProjectionRow.base_index]
      simp [column]
    | some j =>
      change column (TubeIndexed.arity bits) (TubeProjectionRow.code (TubeIndexed.arity bits) (some j) + 1) =
        (TubeHomogenization.outputEquiv bits (some (.inl (.inl j.val)))).val
      rw [output_point bits j.val]
      have hpos := (TubeProjectionRow.code_valid (TubeIndexed.arity bits) j).1
      unfold column
      rw [ite_eq_right (by omega), ite_eq_right (by omega), Nat.add_sub_cancel, TubeProjectionRow.selected_code]

noncomputable def nativeMatrix (bits : List Bool) (s : Finset (PerturbedSource.Index bits)) :
    Matrix (Fin (order bits)) (Fin (order bits)) (MvPolynomial (Fin (arity bits)) ℤ) :=
  fun i j => MvPolynomial.rename (TubeHomogenization.outputEquiv bits)
    (TubeRegularJacobianBudget.matrix bits s ((rowEquiv bits).symm i) ((rowEquiv bits).symm j))

theorem nativeMatrix_det (bits : List Bool) (s : Finset (PerturbedSource.Index bits)) :
    (nativeMatrix bits s).det = MvPolynomial.rename (TubeHomogenization.outputEquiv bits)
      (TubeRegularJacobianBudget.polynomial bits s) := by
  change ((MvPolynomial.rename (TubeHomogenization.outputEquiv bits)).toRingHom.mapMatrix
    (Matrix.reindex (rowEquiv bits) (rowEquiv bits) (TubeRegularJacobianBudget.matrix bits s))).det = _
  rw [← RingHom.map_det, Matrix.det_reindex_self]
  rfl

variable (source active modulus : List Bool → List Bool)

def rowWord (q : List Bool) : List Bool := pairFst (pairSnd q)
def colWord (q : List Bool) : List Bool := pairFst (pairSnd (pairSnd q))
def rankWord (q : List Bool) : List Bool := pairSnd (pairSnd (pairSnd q))

theorem rowWord_mem_FP : rowWord ∈ FP := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
theorem colWord_mem_FP : colWord ∈ FP := mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) pairFst_mem_FP
theorem rankWord_mem_FP : rankWord ∈ FP := mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) pairSnd_mem_FP

noncomputable def selected (q : List Bool) : ℕ :=
  column (TubeIndexed.arity (source (pairFst q)))
    (min (Nat.fromBitsLE (colWord q)) (order (source (pairFst q))))

theorem selected_unary (hs : source ∈ FP) : UnaryFn (selected source) := by
  have hn := TubeIndexed.arity_unary.comp (mem_FP_comp pairFst_mem_FP hs)
  have hk := UnaryFn.fromBitsLE_min colWord_mem_FP (order_unary.comp (mem_FP_comp pairFst_mem_FP hs))
  exact UnaryFn.ite (FPPred.eq hk (UnaryFn.const 0)) (UnaryFn.const 0)
    (UnaryFn.ite (FPPred.eq hk (UnaryFn.const 1)) (hn.add (UnaryFn.const 1))
      ((TubeProjectionRow.selected_unary hn (hk.sub (UnaryFn.const 1))).add (UnaryFn.const 1)))

noncomputable def entry : List Bool → List Bool :=
  FixedWidthDerivativeBits.value (arity ∘ source ∘ pairFst) (TubeIndexed.blockWidth ∘ source ∘ pairFst)
    (width ∘ source ∘ pairFst) (TubeIndexed.degreeBound ∘ source ∘ pairFst) (selected source) rankWord
    (BinaryNat.succ ∘ modulus ∘ pairFst)
    (TubeRegularBits.value (source ∘ pairFst) (active ∘ pairFst) rowWord (modulus ∘ pairFst))

theorem entry_evaluator (hs : source ∈ FP) (ha : active ∈ FP) (hm : modulus ∈ FP) :
    SpaceFunction (entry source active modulus) := by
  have hsource := mem_FP_comp pairFst_mem_FP hs
  exact FixedWidthDerivativeBits.evaluator _ _ _ _ _ _ _
    (TubeRegularBits.evaluator _ _ _ _ hsource (mem_FP_comp pairFst_mem_FP ha) rowWord_mem_FP (mem_FP_comp pairFst_mem_FP hm))
    (arity_unary.comp hsource) (TubeIndexed.blockWidth_unary.comp hsource) (width_unary.comp hsource)
    (TubeIndexed.degreeBound_unary.comp hsource) (selected_unary source hs) rankWord_mem_FP
    (mem_FP_comp (mem_FP_comp pairFst_mem_FP hm) BinaryNat.succ_mem_FP)

theorem entry_packet (c : List Bool) (i j : Fin (order (source c))) (r : ℕ) :
    entry source active modulus
      (pair c (pair (BinaryNatCode.encode i.val) (pair (BinaryNatCode.encode j.val) (BinaryNatCode.encode r)))) =
      residueBits (((nativeMatrix (source c) (activeSet (TubeIndexed.arity (source c)) (active c)) i j).coeff
        (RationalSubstitution.Indexed.exponentVector (arity (source c)) (FixedWidthPolynomial.entry (width (source c)) r)) : ℤ) :
          ZMod (Nat.fromBitsLE (modulus c) + 1)) := by
  let q := pair c (pair (BinaryNatCode.encode i.val) (pair (BinaryNatCode.encode j.val) (BinaryNatCode.encode r)))
  let ri := (rowEquiv (source c)).symm i
  let rj := (rowEquiv (source c)).symm j
  let p := TubeRegularSource.polynomial (source c) (activeSet (TubeIndexed.arity (source c)) (active c)) ri
  let f := TubeHomogenization.outputEquiv (source c)
  have hj := congrArg Fin.val ((rowEquiv (source c)).apply_symm_apply j)
  change rowCode (source c) rj = j.val at hj
  have hsel : selected source q = (f (TubeRegularJacobianBudget.coordinate (source c) rj)).val := by
    unfold selected
    simp only [q, colWord, pairFst_pair, pairSnd_pair,
      show Nat.fromBitsLE (BinaryNatCode.encode j.val) = j.val from Nat.fromBitsLE_bits j.val,
      min_eq_left j.isLt.le]
    rw [← hj]
    exact column_code (source c) rj
  have hcoeff (k : ℕ) :
      TubeRegularBits.value (source ∘ pairFst) (active ∘ pairFst) rowWord (modulus ∘ pairFst)
        (pair q (BinaryNatCode.encode k)) =
      residueBits ((p.coeff (FixedWidthPolynomial.nativeExponent f (TubeIndexed.blockWidth (source c)) k) : ℤ) :
        ZMod (Nat.fromBitsLE (modulus c) + 1)) := by
    have hi := congrArg Fin.val ((rowEquiv (source c)).apply_symm_apply i)
    change rowCode (source c) ri = i.val at hi
    have hrow : TubeRegularBits.decodedIndex (fun _ => source c)
        (fun _ => BinaryNatCode.encode i.val) [] = ri := by
      change TubeRegularFiniteSigns.row id (source c) i.val = ri
      rw [← hi]
      exact TubeRegularFiniteSigns.row_rowCode id (source c) ri
    let residue (bits act word modword : List Bool) : List Bool :=
      residueBits (((TubeRegularSource.polynomial bits (activeSet (TubeIndexed.arity bits) act)
        (TubeRegularBits.decodedIndex (fun _ => bits) (fun _ => word) [])).coeff
          (FixedWidthPolynomial.nativeExponent (TubeHomogenization.outputEquiv bits)
            (TubeIndexed.blockWidth bits) k) : ℤ) : ZMod (Nat.fromBitsLE modword + 1))
    have h := TubeRegularBits.value_packet (source ∘ pairFst) (active ∘ pairFst) rowWord (modulus ∘ pairFst) q k
    change TubeRegularBits.value (source ∘ pairFst) (active ∘ pairFst) rowWord (modulus ∘ pairFst)
      (pair q (BinaryNatCode.encode k)) =
        residue ((source ∘ pairFst) q) ((active ∘ pairFst) q) (rowWord q) ((modulus ∘ pairFst) q) at h
    simp only [Function.comp_apply, q, rowWord, pairFst_pair, pairSnd_pair] at h
    dsimp only [residue] at h
    rw [hrow] at h
    exact h

  have hexp : FixedWidthDerivativeBits.exponent (width ∘ source ∘ pairFst) rankWord f q =
      FixedWidthPolynomial.nativeExponent f (width (source c)) r := by
    ext z
    simp only [FixedWidthDerivativeBits.exponent, FixedWidthPolynomial.nativeExponent,
      Finsupp.coe_equivFunOnFinite_symm, FixedWidthQuery.coordinate, rankWord, q, pairFst_pair, pairSnd_pair,
      Function.comp_apply, BinaryNatCode.encode, FixedWidthPolynomial.entry]
  have H := FixedWidthDerivativeBits.packet (arity ∘ source ∘ pairFst) (TubeIndexed.blockWidth ∘ source ∘ pairFst)
    (width ∘ source ∘ pairFst) (TubeIndexed.degreeBound ∘ source ∘ pairFst) (selected source) rankWord
    (BinaryNat.succ ∘ modulus ∘ pairFst) f
    (TubeRegularBits.value (source ∘ pairFst) (active ∘ pairFst) rowWord (modulus ∘ pairFst)) q p
    (TubeRegularJacobianBudget.coordinate (source c) rj) (Nat.fromBitsLE (modulus c) + 1)
    (by simp only [Function.comp_apply, q, pairFst_pair]; rfl) hsel
    (by simp only [Function.comp_apply, q, pairFst_pair]; unfold TubeIndexed.degreeBound; omega)
    (by simpa only [Function.comp_apply, q, pairFst_pair] using TubeRegularSource.degree_le (source c) _ ri)
    (by simpa only [Function.comp_apply, q, pairFst_pair] using TubeIndexed.degreeBound_lt (source c))
    (by simp only [Function.comp_apply, q, pairFst_pair]; exact BinaryNat.succ_eq_bits _)
    (by simpa only [Function.comp_apply, q, pairFst_pair] using hcoeff)
  rw [hexp] at H
  change entry source active modulus q = _
  change entry source active modulus q = residueBits (m := Nat.fromBitsLE (modulus c) + 1)
    (((MvPolynomial.rename f (MvPolynomial.pderiv (TubeRegularJacobianBudget.coordinate (source c) rj) p)).coeff
      (RationalSubstitution.Indexed.exponentVector (TubeIndexed.projectionDimension (source c) + 1)
        (FixedWidthPolynomial.entry (width (source c)) r)) : ℤ) : ZMod (Nat.fromBitsLE (modulus c) + 1))
  rw [FixedWidthPolynomial.coeff_rename_rank f _ (width (source c)) r]
  exact H

theorem nativeMatrix_entry_degree (bits : List Bool) (s : Finset (PerturbedSource.Index bits))
    (i j : Fin (order bits)) : (nativeMatrix bits s i j).totalDegree ≤ bound bits := by
  apply (MvPolynomial.totalDegree_rename_le _ _).trans
  exact (TubeRegularJacobianBudget.entry_degree_le bits s _ _).trans
    ((Nat.sub_le _ _).trans (le_max_right _ _))

theorem nativeMatrix_det_degree (bits : List Bool) (s : Finset (PerturbedSource.Index bits)) :
    (nativeMatrix bits s).det.totalDegree ≤ bound bits := by
  rw [nativeMatrix_det]
  exact (MvPolynomial.totalDegree_rename_le _ _).trans
    ((TubeRegularJacobianBudget.degree_le bits s).trans (le_max_left _ _))

variable (degree : List Bool → List Bool)

/-- Native modular coefficient computation for the actual regular Jacobian. -/
noncomputable def value : List Bool → List Bool :=
  (FixedWidthDeterminantBits.family (arity ∘ source) (order ∘ source) (width ∘ source) modulus degree
    (fun c => nativeMatrix (source c) (activeSet (TubeIndexed.arity (source c)) (active c)))).value

theorem evaluator (hs : source ∈ FP) (ha : active ∈ FP) (hm : modulus ∈ FP) (hd : degree ∈ FP) :
    SpaceFunction (value source active modulus degree) := by
  exact FixedWidthDeterminantBits.evaluator (arity ∘ source) (order ∘ source) (width ∘ source) modulus degree
    (fun c => nativeMatrix (source c) (activeSet (TubeIndexed.arity (source c)) (active c)))
    (entry source active modulus) (bound ∘ source)
    (fun c i j => nativeMatrix_entry_degree (source c) _ i j) (fun c => bound_lt (source c))
    (entry_packet source active modulus) (entry_evaluator source active modulus hs ha hm)
    (arity_unary.comp hs) (order_unary.comp hs) (width_unary.comp hs) hm hd

theorem value_packet (c : List Bool) (r : ℕ) (hd : degree c = BinaryNatCode.encode r)
    (hr : r < FixedWidthPolynomial.count (arity (source c)) (width (source c))) :
    value source active modulus degree c =
      residueBits (((TubeRegularJacobianBudget.polynomial (source c)
        (activeSet (TubeIndexed.arity (source c)) (active c))).coeff
          (FixedWidthPolynomial.nativeExponent (TubeHomogenization.outputEquiv (source c)) (width (source c)) r) : ℤ) :
            ZMod (Nat.fromBitsLE (modulus c) + 1)) := by
  have hdegree : Nat.fromBitsLE (degree c) = r := by rw [hd]; exact Nat.fromBitsLE_bits r
  have H := FixedWidthDeterminantBits.value_eq (arity ∘ source) (order ∘ source) (width ∘ source) modulus degree
    (fun c => nativeMatrix (source c) (activeSet (TubeIndexed.arity (source c)) (active c)))
    c (bound (source c)) (nativeMatrix_det_degree (source c) _) (bound_lt (source c))
    (by simpa only [Function.comp_apply, hdegree] using hr)
  dsimp +instances only [TubeIndexed.arity, arity] at H ⊢
  rw [nativeMatrix_det, hdegree] at H
  dsimp +instances only [Function.comp_apply, arity] at H
  rw [FixedWidthPolynomial.coeff_rename_rank] at H
  exact H

end LeanCanny.ETR.TubeRegularJacobianBits
