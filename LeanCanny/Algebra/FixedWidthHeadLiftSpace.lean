/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegerParameterCoefficientSpace
public import LeanCanny.Algebra.FixedWidthRowArithmetic
public import LeanCanny.Algebra.EmbeddedCoefficient
/-! # Native coefficient access after adjoining one unused head variable

A nonzero head exponent gives zero. Otherwise one query drops that fixed
width block and reads the original polynomial. The new head may be the
actual successor scalar while the old tail retains the same joint tuple.
-/
@[expose] public section
namespace LeanCanny.Algebra.FixedWidthHeadLiftBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial MvPolynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem zero_not_range (n : ℕ) : (0 : Fin (n+1))∉Set.range (Fin.succ : Fin n→Fin (n+1)) := by
  rintro ⟨i,hi⟩
  exact Fin.succ_ne_zero i hi

theorem rename_coefficient {n : ℕ} (p : MvPolynomial (Fin n) ℤ) (e : Fin (n+1)→₀ℕ) :
    (rename Fin.succ p).coeff e=if e 0=0 then p.coeff (IntegerParameterFlatten.tailExponent e) else 0 := by
  by_cases hz : e 0=0
  · have HE : (IntegerParameterFlatten.tailExponent e).mapDomain Fin.succ=e := by
      ext j
      refine Fin.cases ?_ (fun i=>?_) j
      · rw [Finsupp.mapDomain_of_notMem_range _ _ (zero_not_range n)]
        exact hz.symm
      · rw [Finsupp.mapDomain_apply_of_injective (Fin.succ_injective n)]
        rfl
    rw [ite_eq_left hz]
    conv_lhs => rw [←HE]
    exact coeff_rename_mapDomain _ (Fin.succ_injective n) p _
  · rw [ite_eq_right hz]
    apply coeff_rename_eq_zero
    intro d hd
    have H:=congrArg (fun u : Fin (n+1)→₀ℕ=>u 0) hd
    rw [Finsupp.mapDomain_of_notMem_range _ _ (zero_not_range n)] at H
    exact (hz H.symm).elim

theorem evaluator (A W : List Bool→ℕ) (p : (c : List Bool)→MvPolynomial (Fin (A c)) ℤ)
    (target modulus : List Bool→List Bool) (hW : UnaryFn W) (ht : target∈FP)
    (E : SpaceFunction (FixedWidthRowBits.value A W p (IntegerParameterCoefficientBits.spatial W target) modulus)) :
    SpaceFunction (FixedWidthRowBits.value (fun c=>A c+1) W (fun c=>rename Fin.succ (p c)) target modulus) := by
  have HG : FPPred (fun c=>Nat.fromBitsLE (IntegerParameterCoefficientBits.parameter W target c)=0) :=
    (BinaryFn.fromBits (IntegerParameterCoefficientBits.parameter_mem_FP W target hW ht)).eq (BinaryFn.const 0)
  have H := SpaceFunction.branch (fun c=>decide (Nat.fromBitsLE (IntegerParameterCoefficientBits.parameter W target c)=0))
    HG.flag_mem_FP E (SpaceFunction.ofFP _ (constFn_mem_FP []))
  apply H.congr
  funext c
  unfold FixedWidthRowBits.value
  rw [rename_coefficient,IntegerParameterCoefficientBits.parameter_nativeExponent W target (A c) c,
    IntegerParameterCoefficientBits.tail_nativeExponent W target (A c) c]
  by_cases hz : Nat.fromBitsLE (IntegerParameterCoefficientBits.parameter W target c)=0
  · simp only [hz,decide_true,ite_true]
  · simp only [hz,decide_false,Bool.false_eq_true,ite_false,Int.cast_zero,residueBits,ZMod.val_zero,BinaryNatCode.encode,Nat.zero_bits]

end LeanCanny.Algebra.FixedWidthHeadLiftBits
