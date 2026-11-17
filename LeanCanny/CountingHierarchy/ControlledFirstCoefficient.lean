/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.FirstVariableCoefficients
public import LeanCanny.CountingHierarchy.CoefficientEvaluation
public import LeanCanny.CountingHierarchy.PointBlocks

/-! # Uniform first-variable coefficients at one additional counting level -/

@[expose] public section

namespace LeanCanny.CountingHierarchy.Controlled

open Cslib Cslib.Complexity Turing.MultiTapeTM MvPolynomial

variable {α : Type} {n : α → ℕ} {enc : α ↪ List Bool} {a : ℕ}
  {P : (w : α) → MvPolynomial (Fin (n w + 1)) ℤ}

noncomputable def firstCoefficient (C : Controlled P enc a) (E : Decoder enc)
    (hn : ComputableInPolyTime n enc encUnary) (k : α → ℕ)
    (hk : ComputableInPolyTime k enc encNat) :
    Controlled (fun w => firstVariableCoefficient (P w) (k w)) enc (a + 1) where
  arity_computable := hn
  degreeBound := C.degreeBound
  degree_computable := C.degree_computable
  degree_le w := (firstVariableCoefficient_degree_le _ _).trans (C.degree_le w)
  massExponent := C.massExponent
  mass_computable := C.mass_computable
  mass_le w := (firstVariableCoefficient_mass_le _ _).trans (C.mass_le w)
  cutoff w := max (C.cutoff w) (max (C.degreeBound w) (k w)) + 1
  cutoff_computable := ComputableInPolyTime.binary_add'
    (ComputableInPolyTime.binary_max' C.cutoff_computable
      (ComputableInPolyTime.binary_max' C.degree_computable hk)) (.const 1)
  evaluate q := coefficientResidue q.2.1 (k q.1) (fun t => C.evaluate (q.1, q.2.1, t :: q.2.2))
  evaluate_mem := by
    have hf := ComputableInPolyTime.fst enc (encPair encNat (encList encNat))
    have hp : ComputableInPolyTime (fun q : α × (ℕ × List ℕ) => q.2.1) (encEvaluation enc) encNat := by fun_prop
    have hw : ComputableInPolyTime (fun q : (α × (ℕ × List ℕ)) × ℕ => q.1.1)
        (encPair (encEvaluation enc) encNat) enc := by fun_prop
    have hp' : ComputableInPolyTime (fun q : (α × (ℕ × List ℕ)) × ℕ => q.1.2.1)
        (encPair (encEvaluation enc) encNat) encNat := by fun_prop
    have hz : ComputableInPolyTime (fun q : (α × (ℕ × List ℕ)) × ℕ => q.1.2.2)
        (encPair (encEvaluation enc) encNat) (encList encNat) := by fun_prop
    have ht := ComputableInPolyTime.snd (encEvaluation enc) encNat
    have hpoint := (ComputableTidilyInPolyTime.cons' ht.tidy hz.tidy).computableInPolyTime
    have hv := CountingFunction.preprocess C.evaluate_mem (hw.prod (hp'.prod hpoint))
    exact coefficientResidue_mem (Decoder.pair E (Decoder.pair Decoder.nat (Decoder.list Decoder.nat)))
      hp (hk.comp hf) hv
  evaluate_eq w p z hp hcut := by
    let : Fact p.Prime := ⟨hp⟩
    let phi : MvPolynomial (Fin (n w)) ℤ →+* ZMod p :=
      MvPolynomial.eval₂Hom (Int.castRingHom (ZMod p)) (fun i => (z[i.val]?.getD 0 : ZMod p))
    let Q := (MvPolynomial.finSuccEquiv ℤ (n w) (P w)).map phi
    have hQ : Q.natDegree < p - 1 := by
      have hdeg : Q.natDegree ≤ (P w).totalDegree :=
        Polynomial.natDegree_map_le.trans ((MvPolynomial.natDegree_finSuccEquiv _).le.trans
          (MvPolynomial.degreeOf_le_totalDegree _ _))
      have := C.degree_le w
      omega
    have hk' : k w < p - 1 := by omega
    have hval (t : ℕ) (_ht : t < p) :
        (C.evaluate (w, p, t :: z) : ZMod p) = Q.eval (t : ZMod p) := by
      rw [C.evaluate_eq w p _ hp (by omega)]
      simp only [evaluation, ZMod.natCast_zmod_val, Q, Polynomial.eval_map]
      rw [eval_finSuccEquiv]
      congr 2
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp
    rw [coefficientResidue_eq_val Q (k w) _ hQ hk' hval]
    simp only [Q, Polynomial.coeff_map, phi, MvPolynomial.coe_eval₂Hom,
      firstVariableCoefficient, evaluation]

end LeanCanny.CountingHierarchy.Controlled
