/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineRowAccess
public import LeanCanny.Encoding.FlatAffineRowPolynomials
public import LeanCanny.Encoding.FlatAffineHeightCoefficient
public import LeanCanny.Algebra.FixedWidthRowArithmetic

/-! # Native linear components of completed affine rows -/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineRowLinearReaders
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR MvPolynomial
open FlatAffineFullSourceTower (Inputs arity)
open FlatAffineRowLayout FlatAffineRowAccess
open scoped BigOperators Classical
set_option backward.isDefEq.respectTransparency false

variable (F : Inputs) (row : (u : List Bool) → Fin (FlatAffineFullSourcePositive.count F u))
  (W : List Bool → ℕ) (target modulus : List Bool → List Bool)

noncomputable def read (p : (u : List Bool) → MvPolynomial (Fin (FlatAffineFullSourcePositive.count F u)) ℤ) :=
  FixedWidthRowBits.value (FlatAffineFullSourcePositive.count F) W p target modulus

noncomputable def muPolynomial (u : List Bool) : MvPolynomial (Fin (FlatAffineFullSourcePositive.count F u)) ℤ :=
  ∑ j, C (FlatAffineFullSourceTower.direction F u (stage F row u) j (spatial F row u)) * X (multiplier F row u j)

def muEntry (q : List Bool) : ℕ :=
  counter (fun u => arity F u + 1) q * arity F (pairFst q) + (spatial F row (pairFst q)).val

def heightEntry (q : List Bool) : ℕ :=
  ((height F row (pairFst q)).val + 1) * arity F (pairFst q) + counter (arity F) q

variable {F row W target modulus}

theorem mu_evaluator (h : F.Access) (hr : UnaryFn (fun u => (row u).val))
    (hW : UnaryFn W) (ht : target ∈ FP) (hm : modulus ∈ FP) :
    SpaceFunction (read F W target modulus (muPolynomial F row)) := by
  have hn := FlatAffineFullSourceTower.arity_unary h
  have he : UnaryFn (muEntry F row) := ((counter_unary (hn.add (UnaryFn.const 1))).mul
    (hn.comp pairFst_mem_FP)).add ((spatial_unary h hr).comp pairFst_mem_FP)
  have H := FlatAffineHeightCoefficient.evaluator (FlatAffineFullSourcePositive.count F)
    (fun u => arity F u + 1) W F.width (muEntry F row) (directionRecord F row) target modulus
    (FlatAffineFullSourcePositive.count_unary h) (hn.add (UnaryFn.const 1)) hW h.width he
    (BinaryFn.ofUnary (multiplierSelected_unary h hr)) (direction_evaluator h hr) ht hm (multiplier F row) (by
      intro u i
      simp only [multiplierSelected, counter, pairFst_pair, pairSnd_pair, MacaulayBits.fromBits_encode,
        Nat.min_eq_left i.isLt.le]
      change min (offset F row u + arity F u + i.val) _ = min (offset F row u + (arity F u + i.val)) _
      rw [Nat.add_assoc])
  refine H.congr (funext fun u => ?_)
  rw [FlatAffineHeightCoefficient.packet]
  change MatrixPower.residueBits _ = MatrixPower.residueBits _
  congr 2
  apply congrArg (fun p : MvPolynomial (Fin (FlatAffineFullSourcePositive.count F u)) ℤ => p.coeff _)
  unfold FlatAffineHeightCoefficient.polynomial FixedWidthHeightBits.polynomial muPolynomial
  apply Finset.sum_congr rfl
  intro i _
  simp only [FlatAffineHeightCoefficient.scalar, muEntry, counter, pairFst_pair, pairSnd_pair,
    MacaulayBits.fromBits_encode, Nat.min_eq_left i.isLt.le]
  rw [show (spatial F row (pairFst (pair u (BinaryNatCode.encode i.val)))).val = (spatial F row u).val from
    congrArg (fun v => (spatial F row v).val) (pairFst_pair u (BinaryNatCode.encode i.val))]
  rfl

theorem currentHeight_evaluator (h : F.Access) (hr : UnaryFn (fun u => (row u).val))
    (hW : UnaryFn W) (ht : target ∈ FP) (hm : modulus ∈ FP) :
    SpaceFunction (read F W target modulus (FlatAffineRowPolynomials.currentHeight F row)) := by
  have hn := FlatAffineFullSourceTower.arity_unary h
  have he : UnaryFn (heightEntry F row) :=
    ((((height_unary h hr).add (UnaryFn.const 1)).mul hn).comp pairFst_mem_FP).add (counter_unary hn)
  have H := FlatAffineHeightCoefficient.evaluator (FlatAffineFullSourcePositive.count F) (arity F) W F.width
    (heightEntry F row) (directionRecord F row) target modulus (FlatAffineFullSourcePositive.count_unary h)
    hn hW h.width he (BinaryFn.ofUnary (currentSelected_unary h hr)) (direction_evaluator h hr) ht hm (current F row) (by
      intro u i
      simp only [currentSelected, counter, pairFst_pair, pairSnd_pair, MacaulayBits.fromBits_encode, Nat.min_eq_left i.isLt.le]
      rfl)
  refine H.congr (funext fun u => ?_)
  rw [FlatAffineHeightCoefficient.packet]
  change MatrixPower.residueBits _ = MatrixPower.residueBits _
  congr 2
  apply congrArg (fun p : MvPolynomial (Fin (FlatAffineFullSourcePositive.count F u)) ℤ => p.coeff _)
  unfold FlatAffineHeightCoefficient.polynomial FixedWidthHeightBits.polynomial FlatAffineRowPolynomials.currentHeight
    AffineHeightPolynomial.polynomial
  apply Finset.sum_congr rfl
  intro i _
  simp only [FlatAffineHeightCoefficient.scalar, heightEntry, counter, pairFst_pair, pairSnd_pair,
    MacaulayBits.fromBits_encode, Nat.min_eq_left i.isLt.le]
  rw [show (height F row (pairFst (pair u (BinaryNatCode.encode i.val)))).val = (height F row u).val from
    congrArg (fun v => (height F row v).val) (pairFst_pair u (BinaryNatCode.encode i.val))]
  rfl

noncomputable def oldPolynomial (F : Inputs) (row : (u : List Bool) → Fin (FlatAffineFullSourcePositive.count F u))
    (field : List Bool → List Bool) (u : List Bool) : MvPolynomial (Fin (FlatAffineFullSourcePositive.count F u)) ℤ :=
  AffineHeightPolynomial.polynomial
    (fun i : Fin (arity F u) => FlatAffineFullSourceTower.integer (F.width u)
      (FlatAffineFullSourceTower.normal (levelRecord F row u)) i.val)
    (fun i => coordinate F u (min (Nat.fromBitsLE (field (levelRecord F row u))) (stage F row u - 1)) i.val)

theorem oldHeight_evaluator (h : F.Access) (hr : UnaryFn (fun u => (row u).val))
    (hW : UnaryFn W) (ht : target ∈ FP) (hm : modulus ∈ FP)
    (field : List Bool → List Bool) (hf : field ∈ FP) :
    SpaceFunction (read F W target modulus (oldPolynomial F row field)) := by
  have hn := FlatAffineFullSourceTower.arity_unary h
  let f := fun u (i : Fin (arity F u)) => coordinate F u
    (min (Nat.fromBitsLE (field (levelRecord F row u))) (stage F row u - 1)) i.val
  have H := FlatAffineHeightCoefficient.evaluator_space (FlatAffineFullSourcePositive.count F) (arity F) W F.width
    (counter (arity F)) (FlatAffineFullSourceTower.normal ∘ levelRecord F row) target modulus
    (FlatAffineFullSourcePositive.count_unary h) hn hW h.width (counter_unary hn)
    (oldSelected_evaluator h hr field hf) ((level_evaluator h hr).postcompose _ normal_FP) ht hm f (by
      intro u i
      simp only [oldSelected, counter, pairFst_pair, pairSnd_pair, MacaulayBits.fromBits_encode, Nat.min_eq_left i.isLt.le]
      rfl)
  refine H.congr (funext fun u => ?_)
  rw [FlatAffineHeightCoefficient.packet]
  change MatrixPower.residueBits _ = MatrixPower.residueBits _
  congr 2
  apply congrArg (fun p : MvPolynomial (Fin (FlatAffineFullSourcePositive.count F u)) ℤ => p.coeff _)
  unfold FlatAffineHeightCoefficient.polynomial FixedWidthHeightBits.polynomial oldPolynomial AffineHeightPolynomial.polynomial
  apply Finset.sum_congr rfl
  intro i _
  simp only [FlatAffineHeightCoefficient.scalar, counter, pairFst_pair, pairSnd_pair, MacaulayBits.fromBits_encode,
    Nat.min_eq_left i.isLt.le, Function.comp_apply]
  rfl

theorem constant_evaluator (h : F.Access) (hr : UnaryFn (fun u => (row u).val))
    (hW : UnaryFn W) (ht : target ∈ FP) (hm : modulus ∈ FP) :
    SpaceFunction (read F W target modulus (FlatAffineRowPolynomials.constantLevel F row)) := by
  have H := FlatAffineIntegerSpace.evaluator F.width (fun _ => 0)
    (FlatAffineFullSourceTower.constant ∘ levelRecord F row) modulus h.width (UnaryFn.const 0)
    ((level_evaluator h hr).postcompose _ constant_FP) hm
  exact FixedWidthConstantBits.evaluator (FlatAffineFullSourcePositive.count_unary h) hW ht H
    (fun u => FlatAffineFullSourceTower.integer (F.width u) (FlatAffineFullSourceTower.constant (levelRecord F row u)) 0)
    (fun _ => rfl)

end LeanCanny.Encoding.FlatAffineRowLinearReaders
