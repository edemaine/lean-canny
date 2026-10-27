/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PrincipalMinorSpace
public import LeanCanny.Algebra.BerkowitzPolynomialSpace
public import LeanCanny.Algebra.CertifiedPolynomial

/-! # Parameter coefficients of principal minors in native space

Each matrix entry asks an original bivariate reader for one parameter
coefficient modulo the requested modulus. The outer degree parameters are
explicit and need not equal the symbolic degrees.
-/

@[expose] public section
namespace LeanCanny.Algebra.PolynomialPrincipalMinorBits
open Polynomial LeanCanny.Encoding LeanCanny.Computation MatrixPower

structure Family where
  left : List Bool → (ℤ[X])[X]
  right : List Bool → (ℤ[X])[X]
  leftDegree : List Bool → ℕ
  rightDegree : List Bool → ℕ
  order : List Bool → ℕ
  order_left : ∀ c, order c ≤ leftDegree c
  order_right : ∀ c, order c ≤ rightDegree c

structure Access (F : Family) where
  left : CertifiedPolynomial.BivariateReader F.left
  right : CertifiedPolynomial.BivariateReader F.right
  leftDegree : BinaryFn F.leftDegree
  rightDegree : BinaryFn F.rightDegree
  order : BinaryFn F.order

def origin (z : List Bool) : List Bool := pairFst (pairFst z)
def modulus (z : List Bool) : ℕ := Nat.fromBitsLE (pairSnd z) + 1
theorem origin_FP : origin ∈ FP := mem_FP_comp pairFst_mem_FP pairFst_mem_FP

noncomputable def determinant (F : Family) (c : List Bool) : ℤ[X] :=
  (Subresultant.minor (F.left c) (F.right c) (F.leftDegree c) (F.rightDegree c) (F.order c) (F.order c)).det

noncomputable def modular (F : Family) : BerkowitzPolynomial.ModularFamily where
  dimension z := (F.leftDegree (origin z) - F.order (origin z)) + (F.rightDegree (origin z) - F.order (origin z))
  modulus := modulus
  degree z := Nat.fromBitsLE (pairSnd (pairFst z))
  matrix z := (Subresultant.minor (F.left (origin z)) (F.right (origin z))
    (F.leftDegree (origin z)) (F.rightDegree (origin z)) (F.order (origin z)) (F.order (origin z))).map
      (Polynomial.mapRingHom (Int.castRingHom (ZMod (modulus z))))
  modulus_ne_zero z := by simp [modulus]

/-- The Sylvester coefficient context is a modular determinant context paired
with the selected parameter degree. -/
def sourceQuery (t : List Bool) : List Bool :=
  pair (pair (origin (pairFst (pairFst t))) (pairSnd (pairFst (pairFst t))))
    (pair (pairSnd (pairFst t)) (pairSnd t))
theorem sourceQuery_FP : sourceQuery ∈ FP := by polytime [sourceQuery, origin]

def bits {F : Family} (A : Access F) : PrincipalMinorBits.Bits where
  base := {
    leftDegree z := BinaryNatCode.encode (F.leftDegree (origin z))
    rightDegree z := BinaryNatCode.encode (F.rightDegree (origin z))
    coefficientBits _ := []
    leftCoefficient := A.left.coefficient ∘ sourceQuery
    rightCoefficient := A.right.coefficient ∘ sourceQuery }
  order z := BinaryNatCode.encode (F.order (origin z))

theorem controls {F : Family} (A : Access F) : (bits A).ControlsPolyTime :=
  ⟨⟨BinaryFn.bits_mem_FP (A.leftDegree.comp origin_FP), BinaryFn.bits_mem_FP (A.rightDegree.comp origin_FP),
    constFn_mem_FP []⟩, BinaryFn.bits_mem_FP (A.order.comp origin_FP)⟩

def entryQuery (e : List Bool) : List Bool :=
  pair (pair (pairFst e) (pairSnd (pairSnd (pairSnd e))))
    (pair (pairFst (pairSnd e)) (pairFst (pairSnd (pairSnd e))))
theorem entryQuery_FP : entryQuery ∈ FP := by polytime [entryQuery]

theorem entry_correct {F : Family} (A : Access F) (z : List Bool)
    (i j : Fin ((modular F).dimension z)) (d : ℕ) :
    ((bits A).entry ∘ entryQuery) (pair z (pair (BinaryNatCode.encode i.val)
      (pair (BinaryNatCode.encode j.val) (BinaryNatCode.encode d)))) =
      residueBits (((modular F).matrix z i j).coeff d) := by
    simp only [Function.comp_apply, entryQuery, pairFst_pair, pairSnd_pair]
    have H := (bits A).entry_correct (pair z (BinaryNatCode.encode d))
      (F.left (origin z)) (F.right (origin z)) (F.leftDegree (origin z)) (F.rightDegree (origin z))
      (F.order (origin z)) (F.order_left _) (F.order_right _)
      (fun p : ℤ[X] => residueBits ((p.map (Int.castRingHom (ZMod (modulus z)))).coeff d))
      (show SylvesterBits.CorrectAt (bits A).base (pair z (BinaryNatCode.encode d))
        (F.left (origin z)) (F.right (origin z)) (F.leftDegree (origin z)) (F.rightDegree (origin z))
        (fun p : ℤ[X] => residueBits ((p.map (Int.castRingHom (ZMod (modulus z)))).coeff d)) from by
        constructor
        · simp only [bits, pairFst_pair]
        · simp only [bits, pairFst_pair]
        · intro v
          simp only [bits, Function.comp_apply, sourceQuery, pairFst_pair, pairSnd_pair]
          rw [Polynomial.coeff_map]
          change A.left.coefficient (pair (pair (origin z) (pairSnd z))
            (pair (BinaryNatCode.encode d) (BinaryNatCode.encode v))) =
            residueBits ((((F.left (origin z)).coeff v).coeff d : ℤ) : ZMod (Nat.fromBitsLE (pairSnd z) + 1))
          have H := A.left.coefficient_eq (pair (origin z) (pairSnd z)) d v
          simp only [pairFst_pair] at H
          refine H.trans ?_
          exact congrArg₂ (fun (a : ℤ) (m : ℕ) => residueBits (a : ZMod m)) rfl
            (by rw [pairSnd_pair])
        · intro v
          simp only [bits, Function.comp_apply, sourceQuery, pairFst_pair, pairSnd_pair]
          rw [Polynomial.coeff_map]
          change A.right.coefficient (pair (pair (origin z) (pairSnd z))
            (pair (BinaryNatCode.encode d) (BinaryNatCode.encode v))) =
            residueBits ((((F.right (origin z)).coeff v).coeff d : ℤ) : ZMod (Nat.fromBitsLE (pairSnd z) + 1))
          have H := A.right.coefficient_eq (pair (origin z) (pairSnd z)) d v
          simp only [pairFst_pair] at H
          refine H.trans ?_
          exact congrArg₂ (fun (a : ℤ) (m : ℕ) => residueBits (a : ZMod m)) rfl
            (by rw [pairSnd_pair])
        · simp [residueBits, BinaryNatCode.encode])
      (by simp only [bits, pairFst_pair]) i j
    exact H

noncomputable def modularAccess {F : Family} (A : Access F) : BerkowitzPolynomial.ModularAccess (modular F) where
  dimension z := BinaryNatCode.encode ((F.leftDegree (origin z) - F.order (origin z)) +
    (F.rightDegree (origin z) - F.order (origin z)))
  modulus z := BinaryNat.succ (pairSnd z)
  degree z := BinaryNat.normalize (pairSnd (pairFst z))
  entry := (bits A).entry ∘ entryQuery
  dimension_eq _ := rfl
  modulus_eq _ := BinaryNat.succ_eq_bits _
  degree_eq _ := BinaryNat.normalize_eq_bits _
  entry_eq := entry_correct A

theorem modular_controls {F : Family} (A : Access F) :
    BerkowitzPolynomial.ModularAccess.ControlsPolyTime (F := modular F) (modularAccess A) := by
  have hm : BinaryFn (fun z => F.leftDegree (origin z)) := A.leftDegree.comp origin_FP
  have hn : BinaryFn (fun z => F.rightDegree (origin z)) := A.rightDegree.comp origin_FP
  have hk : BinaryFn (fun z => F.order (origin z)) := A.order.comp origin_FP
  have hD := BinaryFn.bits_mem_FP ((hm.sub hk).add (hn.sub hk))
  have hM := mem_FP_comp pairSnd_mem_FP BinaryNat.succ_mem_FP
  have hK := mem_FP_comp (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) BinaryNat.normalize_mem_FP
  exact ⟨hD, hM, hK⟩

theorem evaluator {F : Family} (A : Access F) : SpaceFunction (modular F).value :=
  BerkowitzPolynomial.ModularAccess.evaluator (modularAccess A) (modular_controls A)
    (((bits A).entryEvaluator (controls A)
      (A.left.evaluator.precompose sourceQuery sourceQuery_FP)
      (A.right.evaluator.precompose sourceQuery sourceQuery_FP)).precompose entryQuery entryQuery_FP)

theorem value_eq (F : Family) (z : List Bool) :
    (modular F).value z = residueBits (((determinant F (origin z)).coeff
      (Nat.fromBitsLE (pairSnd (pairFst z))) : ℤ) : ZMod (modulus z)) := by
  let M := Subresultant.minor (F.left (origin z)) (F.right (origin z))
    (F.leftDegree (origin z)) (F.rightDegree (origin z)) (F.order (origin z)) (F.order (origin z))
  have H : (M.map (Polynomial.mapRingHom (Int.castRingHom (ZMod (modulus z))))).det =
      M.det.map (Int.castRingHom (ZMod (modulus z))) :=
    ((Polynomial.mapRingHom (Int.castRingHom (ZMod (modulus z)))).map_det M).symm
  change residueBits ((M.map (Polynomial.mapRingHom (Int.castRingHom (ZMod (modulus z))))).det.coeff
    (Nat.fromBitsLE (pairSnd (pairFst z)))) = _
  rw [H, Polynomial.coeff_map]
  rfl

end LeanCanny.Algebra.PolynomialPrincipalMinorBits
