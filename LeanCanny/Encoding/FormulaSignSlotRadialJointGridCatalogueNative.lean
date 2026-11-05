/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialJointGridCatalogue
public import LeanCanny.Algebra.FixedWidthRowReboxSpace
/-! # Closed native access to every actual grid feature in one catalogue -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialJointGridCatalogue
open LeanCanny.Algebra LeanCanny.Computation MatrixPower FixedWidthPolynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def datumQuery (q : List Bool) := datum (pairFst q) (Nat.fromBitsLE (pairSnd q))
theorem datumQuery_FP : datumQuery ∈ FP := by
  have HC : (fun q => choice (pairFst q) (Nat.fromBitsLE (pairSnd q))) ∈ FP := by
    apply mem_FP_of_eq (mem_FP_comp (mem_FP_pair (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP)
      pairSnd_mem_FP) WordList.reader_FP)
    intro q
    simp only [Function.comp_apply,WordList.reader,pairFst_pair,pairSnd_pair,choice]
  have HI := (BinaryFn.fromBits pairSnd_mem_FP).bits_mem_FP
  exact mem_FP_pair (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) (mem_FP_pair HI HC)

def context := RationalSubstitution.IntegerBits.context
def target := RationalSubstitution.IntegerBits.selectedDegree
def original (q : List Bool) := pairFst (context q)
def index (q : List Bool) := Nat.fromBitsLE (pairSnd (context q))
theorem context_FP : context ∈ FP := RationalSubstitution.IntegerBits.context_mem_FP
theorem target_FP : target ∈ FP := RationalSubstitution.IntegerBits.selectedDegree_mem_FP
theorem original_FP : original ∈ FP := mem_FP_comp context_FP pairFst_mem_FP
noncomputable def rowArity (q : List Bool) := arity (original q)
noncomputable def rowWidth (q : List Bool) := SquareFeatureProductFamily.inputWidth family (original q)
noncomputable def oldWidth (q : List Bool) := FormulaSignSlotRadialJointGridSource.source.width (datumQuery (context q))
noncomputable def rowPolynomial (q : List Bool) : MvPolynomial (Fin (rowArity q)) ℤ := feature (original q) (index q)
theorem rowArity_unary : UnaryFn rowArity := arity_unary.comp original_FP
private theorem width_control (F : SquareFeatureProductFamily.Family) (H : BinaryFn F.degree) :
    UnaryFn (SquareFeatureProductFamily.inputWidth F) :=
  (UnaryFn.length (H.add (BinaryFn.const 1)).bits_mem_FP).of_eq
    (fun _ => BinaryNatCode.length_encode _)
theorem rowWidth_unary : UnaryFn rowWidth := (width_control family degree_binary).comp original_FP
theorem oldWidth_unary : UnaryFn oldWidth := FormulaSignSlotRadialJointGridSource.access.width.comp
  (mem_FP_comp context_FP datumQuery_FP)

private theorem cast_coefficient {a b : ℕ} (h : a=b) (p : MvPolynomial (Fin a) ℤ) (W r : ℕ) :
    (MvPolynomial.rename (Fin.cast h) p).coeff (nativeExponent (Equiv.refl (Fin b)) W r)=
      p.coeff (nativeExponent (Equiv.refl (Fin a)) W r) := by
  subst b
  simp only [Fin.cast_refl,MvPolynomial.rename_id,AlgHom.id_apply]

theorem row_fit (q : List Bool) : (rowPolynomial q).totalDegree<2^oldWidth q := by
  exact ((MvPolynomial.totalDegree_rename_le _ _).trans
    (FormulaSignSlotRadialJointGridSource.source.polynomial_degree _)).trans_lt
      (FormulaSignSlotRadialJointGridSource.degree_fit (datumQuery (context q)))

noncomputable def coefficient : List Bool → List Bool := FixedWidthRowBits.value rowArity rowWidth rowPolynomial target pairSnd
theorem coefficient_evaluator : SpaceFunction coefficient := by
  let bits := FixedWidthQuery.repack rowArity rowWidth rowArity oldWidth target
  have HB : bits ∈ FP := FixedWidthQuery.repack_mem_FP rowArity_unary rowWidth_unary
    rowArity_unary oldWidth_unary target_FP
  let read := datumQuery ∘ context
  have HR : read ∈ FP := mem_FP_comp context_FP datumQuery_FP
  let query := fun q => pair (pair (read q) (bits q)) (pairSnd q)
  have HQ : query ∈ FP := mem_FP_pair (mem_FP_pair HR HB) pairSnd_mem_FP
  have E := FormulaSignSlotRadialJointGridSource.access.evaluator.precompose query HQ
  have EP : SpaceFunction (FixedWidthRowBits.value rowArity oldWidth rowPolynomial bits pairSnd) := by
    apply E.congr
    funext q
    change FormulaSignSlotRadialJointGridSource.access.coefficient (query q)=_
    rw [show FormulaSignSlotRadialJointGridSource.access.coefficient (query q)=
      FormulaSignSlotRadialJointGridSource.access.coefficient (pair (pair (read q) (bits q)) (pairSnd q)) from rfl,
      FormulaSignSlotRadialJointGridSource.access.packet]
    exact congrArg (fun a : ℤ => residueBits (a : ZMod (Nat.fromBitsLE (pairSnd q)+1)))
      (cast_coefficient (arity_eq (original q) (index q))
        (FormulaSignSlotRadialJointGridSource.source.polynomial (read q)) (oldWidth q)
        (Nat.fromBitsLE (bits q))).symm
  exact FixedWidthRowReboxBits.evaluator rowArity oldWidth rowWidth target rowPolynomial pairSnd
    rowArity_unary oldWidth_unary rowWidth_unary target_FP row_fit EP

noncomputable def access : SquareFeatureProductFamily.Access family where
  arity := arity_unary
  count := BinaryFn.ofUnary count_unary
  degree := degree_binary
  mass := mass_binary
  coefficient := coefficient
  evaluator := coefficient_evaluator
  packet c i _ bits modulus := by
    let H (c : List Bool) (i r m : ℕ) := residueBits (((feature c i).coeff
      (nativeExponent (Equiv.refl _) (SquareFeatureProductFamily.inputWidth family c) r) : ℤ) : ZMod (m+1))
    change H (original (pair (pair (pair c (BinaryNatCode.encode i)) bits) modulus))
      (index (pair (pair (pair c (BinaryNatCode.encode i)) bits) modulus))
      (Nat.fromBitsLE (target (pair (pair (pair c (BinaryNatCode.encode i)) bits) modulus)))
      (Nat.fromBitsLE (pairSnd (pair (pair (pair c (BinaryNatCode.encode i)) bits) modulus))) =
      H c i (Nat.fromBitsLE bits) (Nat.fromBitsLE modulus)
    congr 1 <;> simp only [original,index,context,target,RationalSubstitution.IntegerBits.context,
      RationalSubstitution.IntegerBits.selectedDegree,pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits]

end LeanCanny.Encoding.FormulaSignSlotRadialJointGridCatalogue
