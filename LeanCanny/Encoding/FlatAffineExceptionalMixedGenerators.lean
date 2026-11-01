/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineExceptionalMixedHistory

/-! # Native retained generators of the concrete initial bank

The actual creating companion is transported through every later initial
integer birth. Quotient ranks and discarded digits are computed from the
exact newest-first birth index, without a full-norm degree FP assumption.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineExceptionalMixedHistory
open LeanCanny.Algebra LeanCanny.Computation MatrixPower
open FlatAffineFullSourceTower (Inputs arity)
open FlatAffineCompleteRootStages (next)
open FlatAffineExceptionalBankSource (births width)
open scoped Classical

noncomputable def generatorValue (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (S : List Bool → ℕ)
    (hm : ∀ q, births F (pairFst q) ≤ S q + 1) (i : ∀ q, Fin (births F (pairFst q)))
    (modulus : List Bool → ℕ)
    (row col : ∀ q, Fin (FixedWidthPolynomial.count (births F (pairFst q)) (width F (pairFst q))))
    (q : List Bool) : List Bool :=
  residueBits ((Algebra.leftMulMatrix (initial F C h (S q) (pairFst q) (hm q)).sampler.scalarPrefix.basis.finBasis
    ((initial F C h (S q) (pairFst q) (hm q)).sampler.scalarPrefix.basis.generator (i q)) (row q) (col q) : ℤ) : ZMod (modulus q))

theorem generator_evaluator {F : Inputs} (hF : F.Access)
    (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (hh : UnaryFn (fun u => (h u).val))
    (S : List Bool → ℕ) (hm : ∀ q, births F (pairFst q) ≤ S q + 1)
    (i : ∀ q, Fin (births F (pairFst q))) (hi : BinaryFn (fun q => (i q).val))
    (modulus : List Bool → ℕ) (hmod : ∀ q, modulus q ≠ 0) (hM : BinaryFn modulus)
    (row col : ∀ q, Fin (FixedWidthPolynomial.count (births F (pairFst q)) (width F (pairFst q))))
    (hR : BinaryFn (fun q => (row q).val)) (hC : BinaryFn (fun q => (col q).val)) :
    SpaceFunction (generatorValue F C h S hm i modulus row col) := by
  let o := fun q => initialOrigin F C h (S q) (pairFst q) (hm q) (i q)
  have HU : UnaryFn (fun q => (i q).val) :=
    (UnaryFn.fromBitsLE_of_le hi.bits_mem_FP ((FlatAffineExceptionalBankSource.births_unary hF).comp pairFst_mem_FP)
      (fun q => by simpa only [BinaryNatCode.encode, Nat.fromBitsLE_bits] using (i q).isLt.le)).of_eq
      (fun _ => Nat.fromBitsLE_bits _)
  have HW := (FlatAffineExceptionalBankSource.width_unary hF h).comp pairFst_mem_FP
  have HB : BinaryFn (fun q => (o q).chain.radix) :=
    (((BinaryFn.const 2).powUnary HW).powUnary HU).of_eq (fun q => (o q).toGeneratorOrigin.radix_eq.symm)
  let oldRow := fun q => (o q).chain.oldIndex (row q)
  let oldCol := fun q => (o q).chain.oldIndex (col q)
  have HR : BinaryFn (fun q => (oldRow q).val) := hR.div HB
  have HC : BinaryFn (fun q => (oldCol q).val) := hC.div HB
  have E := creating_evaluator hF C h hh S hm i hi modulus hmod hM oldRow oldCol HR HC
  have HG := (hR.mod HB).eq (hC.mod HB)
  have EZ : SpaceFunction (fun q => residueBits (0 : ZMod (modulus q))) :=
    (SpaceFunction.ofFP _ (constFn_mem_FP [])).congr (funext fun q => ArithmeticBits.zero_residueBits (modulus q))
  refine (SpaceFunction.branch _ HG.flag_mem_FP E EZ).congr (funext fun q => ?_)
  have HE := (o q).toGeneratorOrigin.matrix (row q) (col q)
  change (if decide ((row q).val % (o q).chain.radix = (col q).val % (o q).chain.radix) = true then _ else _) = _
  have HV : generatorValue F C h S hm i modulus row col q =
      residueBits (((if (row q).val % (o q).chain.radix = (col q).val % (o q).chain.radix then
        Algebra.leftMulMatrix
          (UniformIntegralPrefix.step (o q).oldPrefix (o q).birth_bound (Nat.two_pow_pos (width F (pairFst q)))
            (o q).polynomial (o q).degree).basis.finBasis (AdjoinRoot.root _)
          ((o q).chain.oldIndex (row q)) ((o q).chain.oldIndex (col q)) else 0) : ℤ) : ZMod (modulus q)) := by
    convert congrArg (fun z : ℤ => residueBits (z : ZMod (modulus q))) HE using 1; rfl
  rw [HV]
  by_cases H : (row q).val % (o q).chain.radix = (col q).val % (o q).chain.radix
  · simp only [H, decide_true, ite_true]
    rfl
  · simp only [H, decide_false, Bool.false_eq_true, ite_false, Int.cast_zero]

end LeanCanny.Encoding.FlatAffineExceptionalMixedHistory
