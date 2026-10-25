/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegerParameterCoefficientSpace
public import LeanCanny.Algebra.FixedWidthCriticalSpace
public import LeanCanny.Algebra.ProjectionCriticalFamily

/-! # Native coefficients for the actual parameter-ring critical equations

Integer parameter substitution commutes with the spatial critical equations.
The source reader splits the parameter block, and the derivative program
changes only spatial coordinates. The resulting native program evaluates
actual coefficients of the same equations used in the geometric sweep.
-/

@[expose] public section
namespace LeanCanny.Algebra.ParameterizedCriticalCoefficientBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial
open IntegerParameterFlatten MvPolynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem flatten_spatialEquation {n : ℕ} (q : MvPolynomial (Fin n) (Polynomial ℤ))
    (base i : Fin n) (v : Fin n → ℕ) :
    flatten (ProjectionCriticalFamily.spatialEquation q base (fun j => (v j : Polynomial ℤ)) i) =
      if i = base then flatten q else pderiv i.succ (flatten q) - C (v i : ℤ) * pderiv base.succ (flatten q) := by
  unfold ProjectionCriticalFamily.spatialEquation
  split_ifs
  · rfl
  · simp only [map_sub, map_mul, flatten_pderiv, flatten_C]
    congr 2
    simp [coefficientMap]

variable (A W D base selected : List Bool → ℕ) (target modulus direction : List Bool → List Bool)

noncomputable def value (reader : List Bool → List Bool) : List Bool → List Bool :=
  FixedWidthCriticalBits.value A W D base selected target modulus direction
    (IntegerParameterCoefficientBits.liftReader W reader)

theorem evaluator {reader : List Bool → List Bool} (E : SpaceFunction reader)
    (hA : UnaryFn A) (hW : UnaryFn W) (hD : BinaryFn D) (hb : UnaryFn base) (hs : UnaryFn selected)
    (ht : target ∈ FP) (hm : modulus ∈ FP) (hv : direction ∈ FP) :
    SpaceFunction (value A W D base selected target modulus direction reader) :=
  FixedWidthCriticalBits.evaluator A W D base selected target modulus direction
    (IntegerParameterCoefficientBits.liftReader_evaluator W E hW) hA hW hD hb hs ht hm hv

theorem packet {n : ℕ} (q : MvPolynomial (Fin n) (Polynomial ℤ)) (b i : Fin n) (v : Fin n → ℕ)
    (reader : List Bool → List Bool) (c : List Bool) (m : ℕ)
    (hA : A c = n + 1) (hb : base c = b.succ.val) (hi : selected c = i.succ.val)
    (hpos : 0 < D c) (hD : (flatten q).totalDegree ≤ D c) (hW : D c < 2 ^ W c)
    (hm : modulus c = BinaryNatCode.encode (m + 1)) (hv : direction c = BinaryNatCode.encode (v i))
    (hreader : ∀ k r, reader (pair c (pair (BinaryNatCode.encode k) (BinaryNatCode.encode r))) =
      residueBits (((q.coeff (nativeExponent (Equiv.refl (Fin n)) (W c) r)).coeff k : ℤ) : ZMod (m + 1))) :
    value A W D base selected target modulus direction reader c =
      residueBits (((flatten (ProjectionCriticalFamily.spatialEquation q b (fun j => (v j : Polynomial ℤ)) i)).coeff
        (nativeExponent (Equiv.refl (Fin (n + 1))) (W c) (Nat.fromBitsLE (target c))) : ℤ) : ZMod (m + 1)) := by
  have h := FixedWidthCriticalBits.packet A W D base selected target modulus direction
    (Equiv.refl (Fin (n + 1))) (flatten q) b.succ i.succ (v i) m
    (IntegerParameterCoefficientBits.liftReader W reader) c hA hb hi hpos hD hW hm hv
    (fun r => IntegerParameterCoefficientBits.liftReader_packet W q reader c m r hreader)
  simpa only [value, flatten_spatialEquation, Fin.succ_inj] using h

end LeanCanny.Algebra.ParameterizedCriticalCoefficientBits
