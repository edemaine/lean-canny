/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFullCriticalDispatcher
public import LeanCanny.ETR.SizedCollectedCoefficient
/-! # Original spatial coefficient leaves from a literal term writer

The original low polynomial is supplied by a polynomial-time term word writer.
Collected coefficients are computed in polynomial space, including repeated
monomials. The term scope and polynomial identity refer only to the original
root, independently of all interpreted mixed-prefix matrices.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedOriginalSpatialTermBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open scoped Classical

def root (p : List Bool) := RankedHistoryTask.root (pairFst p)

theorem root_FP : root ∈ FP := mem_FP_comp pairFst_mem_FP RankedHistoryTask.root_FP

def dimension (P : Parameters) (p : List Bool) := P.ambient (root p) + 1

def width (P : Parameters) (p : List Bool) := (P.degree (root p)).size

def source (word : List Bool → List Bool) (p : List Bool) := word (root p)

def target (p : List Bool) := BinaryNat.normalize (pairSnd p)

def modulusWord (P : Parameters) (p : List Bool) := BinaryNatCode.encode (modulus P (pairFst p) - 1)

theorem dimension_unary (P : Parameters) (a : Access P) : UnaryFn (dimension P) :=
  (a.ambient.comp root_FP).add (UnaryFn.const 1)

theorem width_unary (P : Parameters) (a : Access P) : UnaryFn (width P) := by
  have HD : BinaryFn (fun p => P.degree (root p)) := a.degree.comp root_FP
  exact (UnaryFn.length HD.bits_mem_FP).of_eq (fun p => Nat.size_eq_bits_len _)

theorem source_FP (word : List Bool → List Bool) (hword : word ∈ FP) : source word ∈ FP :=
  mem_FP_comp root_FP hword

theorem target_FP : target ∈ FP := mem_FP_comp pairSnd_mem_FP BinaryNat.normalize_mem_FP

theorem modulusWord_FP (P : Parameters) (a : Access P) : modulusWord P ∈ FP := by
  have HM : BinaryFn (fun p => modulus P (pairFst p)) := (modulus_binary P a).comp pairFst_mem_FP
  exact (HM.sub (BinaryFn.const 1)).bits_mem_FP

noncomputable def scalar (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (p : List Bool) : List Bool :=
  residueBits (((D.spatial (root p)).low.coeff
    (RationalSubstitution.Indexed.exponentVector (dimension P p)
      (FixedWidthPolynomial.entry (width P p) (Nat.fromBitsLE (pairSnd p))))) :
    ZMod (modulus P (pairFst p)))

theorem collected_eq (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (word : List Bool → List Bool)
    (hp : ∀ r, (ETR.TermView.term (word r)).finitePolynomial (P.ambient r + 1) = (D.spatial r).low)
    (p : List Bool) :
    ETR.SizedCollectedCoefficient.value (dimension P) (width P) (source word) target (modulusWord P) p = scalar P D p := by
  have HM : Nat.fromBitsLE (modulusWord P p) + 1 = modulus P (pairFst p) := by
    simp only [modulusWord, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    have H := modulus_ne_zero P (pairFst p)
    omega
  unfold ETR.SizedCollectedCoefficient.value
  rw [HM]
  have HC : FixedWidthQuery.coordinate (width P) target p =
      FixedWidthPolynomial.entry (width P p) (Nat.fromBitsLE (pairSnd p)) := by
    funext i
    simp only [FixedWidthQuery.coordinate, target, BinaryNat.normalize_eq_bits, FixedWidthPolynomial.entry]
  rw [HC]
  change residueBits (((ETR.TermView.term (word (root p))).finitePolynomial (P.ambient (root p) + 1)).coeff _ :
    ZMod (modulus P (pairFst p))) = _
  rw [hp]
  rfl

theorem evaluator (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (word : List Bool → List Bool) (hword : word ∈ FP)
    (hs : ∀ r, (ETR.TermView.term (word r)).arity ≤ P.ambient r + 1)
    (hp : ∀ r, (ETR.TermView.term (word r)).finitePolynomial (P.ambient r + 1) = (D.spatial r).low) :
    SpaceFunction (scalar P D) := by
  have E := ETR.SizedCollectedCoefficient.evaluator (dimension_unary P a) (width_unary P a)
    (source_FP word hword) target_FP (modulusWord_FP P a) (fun p => hs (root p))
  exact E.congr (funext (collected_eq P D word hp))

end LeanCanny.Algebra.IntegralMixedOriginalSpatialTermBits
