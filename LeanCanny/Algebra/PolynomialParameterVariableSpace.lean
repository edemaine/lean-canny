/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FixedWidthRowArithmetic

/-! # Native variable coefficients over an integer parameter ring

Spatial variables have constant parameter coefficients. A binary zero-index
guard lets the existing integer variable reader supply their canonical
parameter coefficient, including raw ranks and modulus one.
-/

@[expose] public section
namespace LeanCanny.Algebra.PolynomialParameterVariableBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower MvPolynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false

lemma coefficient {ι : Type*} (i : ι) (u : ι →₀ ℕ) (k : ℕ) :
    (((X i : MvPolynomial ι (Polynomial ℤ)).coeff u).coeff k) =
      if k = 0 then ((X i : MvPolynomial ι ℤ).coeff u) else 0 := by
  simp only [coeff_X]
  split_ifs <;> simp_all [Polynomial.coeff_one]

noncomputable def value (N W : List Bool → ℕ) (coordinate : (c : List Bool) → Fin (N c))
    (target parameter modulus : List Bool → List Bool) (q : List Bool) : List Bool :=
  residueBits (((((X (coordinate q) : MvPolynomial (Fin (N q)) (Polynomial ℤ)).coeff
    (FixedWidthPolynomial.nativeExponent (Equiv.refl _) (W q) (Nat.fromBitsLE (target q)))).coeff
      (Nat.fromBitsLE (parameter q))) : ℤ) : ZMod (Nat.fromBitsLE (modulus q) + 1))

theorem evaluator {N W : List Bool → ℕ} (hN : UnaryFn N) (hW : UnaryFn W)
    (coordinate : (c : List Bool) → Fin (N c)) (hc : UnaryFn (fun c => (coordinate c).val))
    (target parameter modulus : List Bool → List Bool)
    (ht : target ∈ FP) (hk : parameter ∈ FP) (hm : modulus ∈ FP) :
    SpaceFunction (value N W coordinate target parameter modulus) := by
  have EV := FixedWidthRowBits.variable_evaluator N W coordinate target modulus hN hW hc ht hm
  have hz := (BinaryFn.fromBits hk).eq (BinaryFn.const 0)
  have R := SpaceFunction.branch (fun q => decide (Nat.fromBitsLE (parameter q) = 0)) hz.flag_mem_FP
    EV (SpaceFunction.ofFP _ (constFn_mem_FP []))
  refine R.congr (funext fun q => ?_)
  simp only [value, coefficient, decide_eq_true_eq]
  split_ifs
  · rfl
  · simp [residueBits, BinaryNatCode.encode]

end LeanCanny.Algebra.PolynomialParameterVariableBits
