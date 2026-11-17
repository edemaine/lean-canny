/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.CoordinatePolynomialEvaluation
public import LeanCanny.CountingHierarchy.CoordinateCandidateBounds
public import LeanCanny.CountingHierarchy.CoefficientEvaluation
public import LeanCanny.CountingHierarchy.IntegerBivariate
public import LeanCanny.CountingHierarchy.NativeRelativeBounds

/-! # Uniform addressed coordinate candidates from the original source -/

@[expose] public section

namespace LeanCanny.CountingHierarchy

open Cslib Cslib.Complexity Turing.MultiTapeTM MvPolynomial Polynomial

noncomputable def coordinateCandidateValue (p n d i j t : ℕ) (value : List ℕ → ℕ) : ℕ :=
  coefficientResidue p j (fun u => coordinatePolynomialValue p n d u i t value)

@[fun_prop] theorem coordinateParameterDegreeBound_polyTime {α : Type} {enc : α ↪ List Bool}
    {n d : α → ℕ} (hn : ComputableInPolyTime n enc encUnary) (hd : ComputableInPolyTime d enc encNat) :
    ComputableInPolyTime (fun w => coordinateParameterDegreeBound (n w) (d w)) enc encNat := by
  have hb := ComputableInPolyTime.unary_to_binary.comp hn
  have hdim := ComputableInPolyTime.binary_pow' (ComputableInPolyTime.binary_add' hd (.const 1)) hn
  exact ComputableInPolyTime.binary_mul' hdim (ComputableInPolyTime.binary_add' hb
    (ComputableInPolyTime.binary_mul' hb (ComputableInPolyTime.binary_add' hdim
      (ComputableInPolyTime.binary_mul' hb hd))))

theorem coordinateCandidateValue_mem {α : Type} {enc : α ↪ List Bool} {a : ℕ}
    (E : Decoder enc) {p n d i j t : α → ℕ} {value : α × List ℕ → ℕ}
    (hp : ComputableInPolyTime p enc encNat) (hn : ComputableInPolyTime n enc encUnary)
    (hd : ComputableInPolyTime d enc encNat) (hi : ComputableInPolyTime i enc encNat)
    (hj : ComputableInPolyTime j enc encNat) (ht : ComputableInPolyTime t enc encNat)
    (hv : value ∈ CountingFunction a (encPair enc (encList encNat)) encNat) :
    (fun w => coordinateCandidateValue (p w) (n w) (d w) (i w) (j w) (t w)
      (fun y => value (w, y))) ∈ CountingFunction (a + 11) enc encNat := by
  have hf := ComputableInPolyTime.fst enc encNat
  have hv' := CountingFunction.preprocess (input := encPair (encPair enc encNat) (encList encNat)) hv
    (g := fun q : (α × ℕ) × List ℕ => (q.1.1, q.2)) (by fun_prop)
  have hvalues := coordinatePolynomialValue_mem (Decoder.pair E Decoder.nat) (hp.comp hf) (hn.comp hf)
    (hd.comp hf) (ComputableInPolyTime.snd _ _) (hi.comp hf) (ht.comp hf) hv'
  have h := coefficientResidue_mem E hp hj hvalues
  simpa only [coordinateCandidateValue, Function.comp_apply, Nat.add_assoc] using h

theorem coordinateCandidateValue_cast {p n : ℕ} [Fact p.Prime] (d : ℕ) (hd : 1 ≤ d)
    (F : MvPolynomial (Fin n) ℤ) (hF : F.totalDegree ≤ d + 1) (i : Fin n) (j t : ℕ)
    (hcut : criticalCoefficientPrimeCutoff n d < p)
    (hH : coordinateParameterDegreeBound n d < p - 1) (hj : j < p - 1)
    (value : List ℕ → ℕ)
    (hv : ∀ y, (value y : ZMod p) = MvPolynomial.eval₂ (Int.castRingHom (ZMod p))
      (fun k : Fin n => (y[k.val]?.getD 0 : ZMod p)) F) :
    (coordinateCandidateValue p n d i.val j t value : ZMod p) =
      ((Bivariate.swap (parametricCoordinatePolynomial d F hF i)).coeff j).eval₂
        (Int.castRingHom (ZMod p)) (t : ZMod p) := by
  let phi := Polynomial.eval₂RingHom (Int.castRingHom (ZMod p)) (t : ZMod p)
  let Q := (Bivariate.swap (parametricCoordinatePolynomial d F hF i)).map phi
  have hQ : Q.natDegree < p - 1 :=
    Polynomial.natDegree_map_le.trans_lt ((coordinateCandidate_index_bound d hd F hF i).trans_lt hH)
  have hval (u : ℕ) (_hu : u < p) :
      (coordinatePolynomialValue p n d u i.val t value : ZMod p) = Q.eval (u : ZMod p) := by
    rw [coordinatePolynomialValue_cast d hd F hF u t i hcut value hv]
    dsimp only [Q]
    rw [Polynomial.eval_map, integer_bivariate_swap_eval]
    rfl
  rw [coordinateCandidateValue, coefficientResidue_eq_val Q j _ hQ hj hval,
    ZMod.natCast_zmod_val, Polynomial.coeff_map]
  rfl

end LeanCanny.CountingHierarchy
