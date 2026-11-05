/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.SquareSamplePolynomialTest
public import LeanCanny.Encoding.IntegralFramedBankPolynomialModel
public import LeanCanny.Algebra.FixedWidthBoxRepackSpace

/-! # Charged implicit sources as square-sample polynomial tests

Only the number of source coordinates is identified with the square sampler.
The coefficient reader checks the original source box before repacking into
it, and retains the caller's modulus.
-/

@[expose] public section
namespace LeanCanny.Encoding.SquareSampleSourceTest
open LeanCanny.Algebra LeanCanny.Computation MatrixPower FixedWidthPolynomial
open IntegralFramedBankPolynomialModel (Source)
open SquareSampleInput (Inputs)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def castPolynomial {n m : ℕ} (h : n = m)
    (p : MvPolynomial (Fin n) ℤ) : MvPolynomial (Fin m) ℤ := h ▸ p

theorem cast_degree {n m : ℕ} (h : n = m) (p : MvPolynomial (Fin n) ℤ) :
    (castPolynomial h p).totalDegree = p.totalDegree := by cases h; rfl

theorem cast_mass {n m : ℕ} (h : n = m) (p : MvPolynomial (Fin n) ℤ) :
    MvMass.mass (castPolynomial h p) = MvMass.mass p := by cases h; rfl

theorem cast_coefficient {n m : ℕ} (h : n = m) (p : MvPolynomial (Fin n) ℤ) (W r : ℕ) :
    (castPolynomial h p).coeff (nativeExponent (Equiv.refl _) W r) =
      p.coeff (nativeExponent (Equiv.refl _) W r) := by cases h; rfl

theorem cast_eval {n m : ℕ} (h : n = m) (p : MvPolynomial (Fin n) ℤ)
    (z : Fin m → ℝ) :
    (castPolynomial h p).eval₂ (Int.castRingHom ℝ) z =
      p.eval₂ (Int.castRingHom ℝ) (fun i => z (Fin.cast h i)) := by cases h; rfl

noncomputable def test (F : Inputs) (S : Source)
    (h : ∀ u, S.arity u = SquareSampleSource.count F u) : SquareSamplePolynomialTest.Test F where
  polynomial u := castPolynomial (h u) (S.polynomial u)
  degree := S.degree
  mass := S.mass
  polynomial_degree u := (cast_degree (h u) _).le.trans (S.polynomial_degree u)
  polynomial_mass u := (cast_mass (h u) _).le.trans (S.polynomial_mass u)

theorem test_eval (F : Inputs) (S : Source)
    (h : ∀ u, S.arity u = SquareSampleSource.count F u) (u : List Bool)
    (z : Fin (SquareSampleSource.count F u) → ℝ) :
    ((test F S h).polynomial u).eval₂ (Int.castRingHom ℝ) z =
      (S.polynomial u).eval₂ (Int.castRingHom ℝ) (fun i => z (Fin.cast (h u) i)) :=
  cast_eval (h u) (S.polynomial u) z

def context := RationalSubstitution.IntegerBits.context
def target := RationalSubstitution.IntegerBits.selectedDegree

noncomputable def sourceValue (S : Source) (V : List Bool → ℕ) : List Bool → List Bool :=
  FixedWidthRowBits.value (S.arity ∘ context) (V ∘ context)
    (fun q => S.polynomial (context q)) target pairSnd

theorem source_evaluator (S : Source) (A : IntegralFramedBankPolynomialModel.Access S)
    (V : List Bool → ℕ) (hV : UnaryFn V) : SpaceFunction (sourceValue S V) := by
  have HC : context ∈ FP := RationalSubstitution.IntegerBits.context_mem_FP
  have HT : target ∈ FP := RationalSubstitution.IntegerBits.selectedDegree_mem_FP
  let bits := FixedWidthQuery.repack (S.arity ∘ context) (V ∘ context)
    (S.arity ∘ context) (S.width ∘ context) target
  have HB : bits ∈ FP := FixedWidthQuery.repack_mem_FP
    (A.arity.comp HC) (hV.comp HC) (A.arity.comp HC) (A.width.comp HC) HT
  have HQ : (fun q => pair (pair (context q) (bits q)) (pairSnd q)) ∈ FP :=
    mem_FP_pair (mem_FP_pair HC HB) pairSnd_mem_FP
  have E := A.evaluator.precompose _ HQ
  have EP : SpaceFunction (FixedWidthRowBits.value (S.arity ∘ context) (S.width ∘ context)
      (fun q => S.polynomial (context q)) bits pairSnd) := by
    exact E.congr (funext fun q => A.packet _ _ _)
  exact FixedWidthBoxRepackBits.evaluator (S.arity ∘ context) (S.width ∘ context)
    (V ∘ context) (fun q => S.polynomial (context q))
    (fun q e he i => (MvPolynomial.monomial_le_degreeOf i he).trans_lt (S.fit _ i))
    target pairSnd (A.arity.comp HC) (A.width.comp HC) (hV.comp HC) HT EP

theorem access (F : Inputs) (S : Source)
    (h : ∀ u, S.arity u = SquareSampleSource.count F u)
    (A : IntegralFramedBankPolynomialModel.Access S) : (test F S h).Access := by
  have HV : UnaryFn (fun u => (S.degree u).size) :=
    (UnaryFn.length A.degree.bits_mem_FP).of_eq (fun u => BinaryNatCode.length_encode (S.degree u))
  refine ⟨A.degree, A.mass, (source_evaluator S A _ HV).congr (funext fun q => ?_)⟩
  unfold sourceValue FixedWidthRowBits.value SquareSamplePolynomialTest.coefficient
    FixedWidthRationalSubstitutionBits.Family.coefficient
  change residueBits (((S.polynomial (context q)).coeff
      (nativeExponent (Equiv.refl _) ((S.degree (context q)).size) (Nat.fromBitsLE (target q))) :
        ZMod (Nat.fromBitsLE (pairSnd q) + 1))) = _
  rw [nativeExponent_refl]
  exact congrArg (fun z : ℤ => residueBits (z : ZMod (Nat.fromBitsLE (pairSnd q) + 1)))
    (cast_coefficient (h (context q)) (S.polynomial (context q))
      ((S.degree (context q)).size) (Nat.fromBitsLE (target q))).symm

noncomputable def substitution_access {F : Inputs} (hF : F.Access) (S : Source)
    (h : ∀ u, S.arity u = SquareSampleSource.count F u)
    (A : IntegralFramedBankPolynomialModel.Access S) :
    FixedWidthRationalSubstitutionBits.Access (SquareSamplePolynomialTest.family (test F S h)) :=
  SquareSamplePolynomialTest.access hF (access F S h A)

noncomputable def cleared_access {F : Inputs} (hF : F.Access) (S : Source)
    (h : ∀ u, S.arity u = SquareSampleSource.count F u)
    (A : IntegralFramedBankPolynomialModel.Access S) :
    (SquareSamplePolynomialTest.test (test F S h)).Access :=
  SquareSamplePolynomialTest.test_access hF (access F S h A)

end LeanCanny.Encoding.SquareSampleSourceTest
