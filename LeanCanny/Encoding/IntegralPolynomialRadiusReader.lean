/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedBankPolynomialModel
public import LeanCanny.Algebra.FixedWidthBivariateReader
public import LeanCanny.Algebra.FixedWidthParameterCons
public import LeanCanny.Algebra.MvTwoParameterCoefficient
/-! # A native radius reader from an actual multivariate coefficient source

Variable zero becomes the radius; all remaining variable indices retain
order. An explicit bound check prevents large radius powers from wrapping.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralPolynomialRadiusReader
open LeanCanny.Algebra LeanCanny.Computation MatrixPower FixedWidthPolynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false
open IntegralFramedBankPolynomialModel (Source Access)

variable (S : Source) (N : List Bool → ℕ) (hd : ∀ c, S.arity c = N c + 1)

noncomputable def castPolynomial (c : List Bool) :=
  MvPolynomial.rename (Fin.cast (hd c)) (S.polynomial c)
noncomputable def polynomial (c : List Bool) :=
  MvPolynomial.finSuccEquiv ℤ (N c) (castPolynomial S N hd c)

theorem coefficient_degree (c : List Bool) (v : ℕ) :
    ((polynomial S N hd c).coeff v).totalDegree ≤ S.degree c :=
  ((MvTwoParameterCoefficient.one_degree (castPolynomial S N hd c) v).trans
    (MvPolynomial.totalDegree_rename_le _ _)).trans (S.polynomial_degree c)

theorem coefficient_mass (c : List Bool) (v : ℕ) :
    MvMass.mass ((polynomial S N hd c).coeff v) ≤ 2 ^ S.mass c :=
  ((MvTwoParameterCoefficient.one_mass (castPolynomial S N hd c) v).trans
    (MvMass.rename_le _ _)).trans (S.polynomial_mass c)

theorem polynomial_degree (c : List Bool) : (polynomial S N hd c).natDegree ≤ S.degree c := by
  rw [polynomial, MvPolynomial.natDegree_finSuccEquiv]
  exact ((MvPolynomial.degreeOf_le_totalDegree _ _).trans
    (MvPolynomial.totalDegree_rename_le _ _)).trans (S.polynomial_degree c)

private theorem evaluate_radius {n : ℕ} (p : MvPolynomial (Fin (n + 1)) ℤ)
    (z : Fin n → ℝ) (r : ℝ) :
    ((MvPolynomial.finSuccEquiv ℤ n p).map (MvPolynomial.eval₂Hom (Int.castRingHom ℝ) z)).eval r =
      p.eval₂ (Int.castRingHom ℝ) (Fin.cons r z) := by
  have H : (Polynomial.evalRingHom r).comp
      ((Polynomial.mapRingHom (MvPolynomial.eval₂Hom (Int.castRingHom ℝ) z)).comp
        (MvPolynomial.finSuccEquiv ℤ n).toRingHom) =
      MvPolynomial.eval₂Hom (Int.castRingHom ℝ) (Fin.cons r z) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [MvPolynomial.finSuccEquiv_X_zero]
      · simp [MvPolynomial.finSuccEquiv_X_succ]
  exact congrArg (fun f : MvPolynomial (Fin (n + 1)) ℤ →+* ℝ => f p) H

theorem specialization (c : List Bool) (z : Fin (N c) → ℝ) (r : ℝ) :
    ((polynomial S N hd c).map (MvPolynomial.eval₂Hom (Int.castRingHom ℝ) z)).eval r =
      (S.polynomial c).eval₂ (Int.castRingHom ℝ) (fun i => (Fin.cons r z : Fin (N c + 1) → ℝ) (Fin.cast (hd c) i)) := by
  rw [polynomial, evaluate_radius, castPolynomial, MvPolynomial.eval₂_rename]
  rfl

private theorem cast_coefficient {a b : ℕ} (h : a = b)
    (p : MvPolynomial (Fin a) ℤ) (w r : ℕ) :
    (MvPolynomial.rename (Fin.cast h) p).coeff (nativeExponent (Equiv.refl _) w r) =
      p.coeff (nativeExponent (Equiv.refl _) w r) := by
  subst b
  simp only [Fin.cast_refl, MvPolynomial.rename_id, AlgHom.id_apply]

def inner (z : List Bool) := pairFst (pairSnd z)
def outer (z : List Bool) := Nat.fromBitsLE (pairSnd (pairSnd z))
def modulus (z : List Bool) := pairSnd (pairFst z)
def origin := FixedWidthBivariateReader.origin

def query (z : List Bool) := pair (pair (origin z)
  (FixedWidthParameterConsBits.prepend (S.width ∘ origin) outer inner z)) (modulus z)

def Valid (z : List Bool) : Prop := outer z < 2 ^ S.width (origin z)

variable (A : Access S)

theorem query_FP (A : Access S) : query S ∈ FP := by
  have HO := FixedWidthBivariateReader.origin_FP
  have HW := A.width.comp HO
  have HI : inner ∈ FP := by polytime [inner]
  have HM : modulus ∈ FP := by polytime [modulus]
  have HY : BinaryFn outer := BinaryFn.fromBits (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP)
  exact mem_FP_pair (mem_FP_pair HO
    (FixedWidthParameterConsBits.prepend_FP _ _ _ HW HY HI)) HM

theorem valid_FP (A : Access S) : FPPred (Valid S) := by
  have HY : BinaryFn outer := BinaryFn.fromBits (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP)
  exact HY.lt ((BinaryFn.const 2).powUnary (A.width.comp FixedWidthBivariateReader.origin_FP))

noncomputable def value (z : List Bool) : List Bool :=
  if Valid S z then A.coefficient (query S z) else []

theorem evaluator : SpaceFunction (value S A) := by
  have E := A.evaluator.precompose (query S) (query_FP S A)
  have H := SpaceFunction.branch (fun z => decide (Valid S z)) (valid_FP S A).flag_mem_FP E
    (SpaceFunction.ofFP _ (constFn_mem_FP []))
  exact H.congr (funext fun z => by simp only [value, decide_eq_true_eq, Function.comp_apply])

theorem packet (hfit : ∀ c, S.degree c < 2 ^ S.width c) (q : List Bool) (u v : ℕ) :
    value S A (pair q (pair (BinaryNatCode.encode u) (BinaryNatCode.encode v))) =
      residueBits (((((polynomial S N hd (pairFst q)).coeff v).coeff
        (nativeExponent (Equiv.refl _) (S.width (pairFst q)) u)) : ℤ) :
          ZMod (Nat.fromBitsLE (pairSnd q) + 1)) := by
  let z := pair q (pair (BinaryNatCode.encode u) (BinaryNatCode.encode v))
  have HO : origin z = pairFst q := by simp only [origin, FixedWidthBivariateReader.origin, z, pairFst_pair]
  have HI : inner z = BinaryNatCode.encode u := by simp only [z, inner, pairSnd_pair, pairFst_pair]
  have HY : outer z = v := by simp only [z, outer, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  have HM : modulus z = pairSnd q := by simp only [z, modulus, pairFst_pair]
  change value S A z = _
  unfold value
  by_cases HV : v < 2 ^ S.width (pairFst q)
  · rw [ite_eq_left (by simpa only [Valid, HO, HY] using HV)]
    unfold query
    rw [A.packet, HO, HM]
    simp only [FixedWidthParameterConsBits.prepend, Function.comp_apply, HO, HI, HY]
    have HE := FixedWidthParameterConsBits.nativeExponent_prepend (N (pairFst q))
      (S.width (pairFst q)) v (BinaryNatCode.encode u) HV
    rw [show Nat.fromBitsLE (BinaryNatCode.encode u) = u from by
      simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]] at HE
    rw [← cast_coefficient (hd (pairFst q))]
    rw [HE]
    rw [polynomial, MvPolynomial.finSuccEquiv_coeff_coeff]
    rfl
  · rw [ite_eq_right (by simpa only [Valid, HO, HY] using HV)]
    have HD : (polynomial S N hd (pairFst q)).natDegree < v :=
      (polynomial_degree S N hd _).trans_lt ((hfit _).trans_le (Nat.le_of_not_gt HV))
    simp only [Polynomial.coeff_eq_zero_of_natDegree_lt HD, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply, Int.cast_zero]
    rfl

noncomputable def reader (hN : UnaryFn N) (hfit : ∀ c, S.degree c < 2 ^ S.width c) :
    CertifiedPolynomial.BivariateReader
      (FixedWidthBivariateReader.polynomial N S.width (polynomial S N hd)) :=
  FixedWidthBivariateReader.reader N S.width (polynomial S N hd) (value S A) (evaluator S A)
    hN A.width S.degree (coefficient_degree S N hd) hfit (packet S N hd A hfit)

end LeanCanny.Encoding.IntegralPolynomialRadiusReader
