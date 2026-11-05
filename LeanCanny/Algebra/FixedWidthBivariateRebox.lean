/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.FixedWidthRowReboxSpace
/-! # Changing the coefficient box of an actual bivariate reader

Every exponent is checked against the original box before repacking. The
outer coefficient and caller modulus are unchanged.
-/
@[expose] public section
namespace LeanCanny.Algebra.FixedWidthBivariateRebox
open Polynomial LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial
open scoped Classical
variable (A U V D : List Bool → ℕ)
variable (p : (c : List Bool) → Polynomial (MvPolynomial (Fin (A c)) ℤ))

def origin (z : List Bool) := pairFst (pairFst z)
def outer (z : List Bool) := Nat.fromBitsLE (pairSnd (pairSnd z))
def target (z : List Bool) := pairFst (pairSnd z)
def modulus (z : List Bool) := pairSnd (pairFst z)
theorem origin_FP : origin ∈ FP := by polytime [origin]
theorem outer_binary : BinaryFn outer := BinaryFn.fromBits (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP)
theorem target_FP : target ∈ FP := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
theorem modulus_FP : modulus ∈ FP := mem_FP_comp pairFst_mem_FP pairSnd_mem_FP

noncomputable def value := FixedWidthRowBits.value (A ∘ origin) (V ∘ origin)
  (fun z => (p (origin z)).coeff (outer z)) target modulus

theorem evaluator (R : CertifiedPolynomial.BivariateReader (FixedWidthBivariateReader.polynomial A U p))
    (hA : UnaryFn A) (hU : UnaryFn U) (hV : UnaryFn V)
    (hP : ∀ c j, ((p c).coeff j).totalDegree ≤ D c) (hfit : ∀ c, D c < 2 ^ U c) :
    SpaceFunction (value A V p) := by
  have E := FixedWidthBivariateRowBits.evaluator A U p R hA hU
    (fun c j => (hP c j).trans_lt (hfit c)) origin origin_FP outer outer_binary
    (FixedWidthQuery.repack (A ∘ origin) (V ∘ origin) (A ∘ origin) (U ∘ origin) target) modulus
    (FixedWidthQuery.repack_mem_FP (hA.comp origin_FP) (hV.comp origin_FP)
      (hA.comp origin_FP) (hU.comp origin_FP) target_FP) modulus_FP
  exact FixedWidthRowReboxBits.evaluator (A ∘ origin) (U ∘ origin) (V ∘ origin) target
    (fun z => (p (origin z)).coeff (outer z)) modulus (hA.comp origin_FP)
    (hU.comp origin_FP) (hV.comp origin_FP) target_FP
    (fun z => (hP _ _).trans_lt (hfit _)) E

private noncomputable def entry (c : List Bool) (j W : ℕ) (bits m : List Bool) :=
  residueBits (((((p c).coeff j).coeff
    (nativeExponent (Equiv.refl (Fin (A c))) W (Nat.fromBitsLE bits))) : ℤ) :
      ZMod (Nat.fromBitsLE m + 1))
private theorem value_entry (z : List Bool) : value A V p z =
    entry A p (origin z) (outer z) (V (origin z)) (target z) (modulus z) := rfl
attribute [local irreducible] entry

theorem packet (q : List Bool) (u v : ℕ) :
    value A V p (pair q (pair (BinaryNatCode.encode u) (BinaryNatCode.encode v))) =
      residueBits (((((p (pairFst q)).coeff v).coeff
        (nativeExponent (Equiv.refl _) (V (pairFst q)) u)) : ℤ) :
          ZMod (Nat.fromBitsLE (pairSnd q) + 1)) := by
  rw [value_entry]
  simp only [origin, outer, target, modulus, pairFst_pair, pairSnd_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits]
  unfold entry
  rw [Nat.fromBitsLE_bits]

noncomputable def reader
    (R : CertifiedPolynomial.BivariateReader (FixedWidthBivariateReader.polynomial A U p))
    (hA : UnaryFn A) (hU : UnaryFn U) (hV : UnaryFn V)
    (hP : ∀ c j, ((p c).coeff j).totalDegree ≤ D c)
    (hfitU : ∀ c, D c < 2 ^ U c) (hfitV : ∀ c, D c < 2 ^ V c) :
    CertifiedPolynomial.BivariateReader (FixedWidthBivariateReader.polynomial A V p) :=
  FixedWidthBivariateReader.reader A V p (value A V p)
    (evaluator A U V D p R hA hU hV hP hfitU) hA hV D hP hfitV (packet A V p)

end LeanCanny.Algebra.FixedWidthBivariateRebox
