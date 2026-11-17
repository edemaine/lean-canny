/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MvCoefficientMass
public import CslibFrontier.Computability.Complexity.Classes.CountingHierarchy.Arithmetic
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.BinaryDiv
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryOrder

/-!
# Controlled integer polynomial families

A polynomial is a mathematical specification, not machine input. A controlled
family supplies polynomial-time binary degree, logarithmic coefficient-mass
and prime-cutoff bounds, a polynomial-time unary arity, and one total modular
evaluator at a fixed counting level. Bounds depend only on the primary instance.
Evaluation points are lists of binary naturals; missing coordinates are zero.

This is the access contract of Section 2 of OpenAI's October 4, 2026 preprint
*Existential--universal real sentences in the counting hierarchy*. It permits
exponential degrees and exponentially long coefficients without assuming their
expanded encodings are available. The closure proofs construct the actual
evaluators and their resource certificates.
-/

public section

namespace LeanCanny.CountingHierarchy

open Cslib Cslib.Complexity Turing.MultiTapeTM MvPolynomial

/-- An instance, a binary modulus and a list of binary coordinates. The instance
and modulus are framed; the coordinate list uses the native list encoding. -/
abbrev encEvaluation {α : Type} (enc : α ↪ List Bool) :
    (α × (ℕ × List ℕ)) ↪ List Bool :=
  encPair enc (encPair encNat (encList encNat))

/-- Polynomial evaluation at the supplied coordinates, padded by zeros. -/
@[expose] noncomputable def evaluation {n : ℕ} (P : MvPolynomial (Fin n) ℤ)
    (p : ℕ) (z : List ℕ) : ℕ :=
  (eval₂ (Int.castRingHom (ZMod p)) (fun i => ((z[i.val]?.getD 0 : ℕ) : ZMod p)) P).val

/-- Uniform finite-field access with bounds independent of the evaluation prime.
The polynomial family is never passed to the realizing machine. -/
structure Controlled {α : Type} {n : α → ℕ}
    (P : (w : α) → MvPolynomial (Fin (n w)) ℤ)
    (enc : α ↪ List Bool) (a : ℕ) where
  /-- Arity is polynomially bounded, witnessed by its unary computation. -/
  arity_computable : ComputableInPolyTime n enc encUnary
  /-- Binary total-degree bound. -/
  degreeBound : α → ℕ
  degree_computable : ComputableInPolyTime degreeBound enc encNat
  degree_le : ∀ w, (P w).totalDegree ≤ degreeBound w
  /-- Binary exponent bounding the sum of absolute coefficients. -/
  massExponent : α → ℕ
  mass_computable : ComputableInPolyTime massExponent enc encNat
  mass_le : ∀ w, Algebra.MvMass.mass (P w) ≤ 2 ^ massExponent w
  /-- Binary lower bound on the evaluation prime. -/
  cutoff : α → ℕ
  cutoff_computable : ComputableInPolyTime cutoff enc encNat
  /-- One total evaluator, also defined for small or composite moduli. -/
  evaluate : α × (ℕ × List ℕ) → ℕ
  evaluate_mem : evaluate ∈ CountingFunction a (encEvaluation enc) encNat
  evaluate_eq : ∀ w p z, p.Prime → cutoff w < p →
    evaluate (w, p, z) = evaluation (P w) p z

namespace Controlled

variable {α : Type} {n : α → ℕ} {enc : α ↪ List Bool} {a b : ℕ}
  {P Q : (w : α) → MvPolynomial (Fin (n w)) ℤ}

/-- Increasing the fixed counting level retains the same bounds and evaluator. -/
@[expose] def mono (C : Controlled P enc a) (hab : a ≤ b) : Controlled P enc b :=
  { C with evaluate_mem := CountingFunction.mono hab C.evaluate_mem }

/-- A polynomial-time integer family gives a controlled constant polynomial. -/
@[expose] noncomputable def constant (hn : ComputableInPolyTime n enc encUnary)
    (c : α → ℤ) (hc : ComputableInPolyTime c enc encIntBin) :
    Controlled (fun w => C (c w) : (w : α) → MvPolynomial (Fin (n w)) ℤ) enc a where
  arity_computable := hn
  degreeBound := fun _ => 0
  degree_computable := .const 0
  degree_le w := by simp only [totalDegree_C, le_refl]
  massExponent := fun w => (c w).natAbs.size
  mass_computable := ComputableInPolyTime.unary_to_binary.comp
    (ComputableInPolyTime.binary_size.comp (ComputableInPolyTime.intBin_natAbs.comp hc))
  mass_le w := by
    rw [Algebra.MvMass.C]
    exact (Nat.lt_size_self _).le
  cutoff := fun _ => 0
  cutoff_computable := .const 0
  evaluate := fun q => (c q.1 % (q.2.1 : ℤ)).toNat
  evaluate_mem := CountingFunction.of_polyTime
    (ComputableInPolyTime.intBin_emodNat'
      (hc.comp (ComputableInPolyTime.fst _ _)) (by fun_prop))
  evaluate_eq w p z hp _ := by
    let : NeZero p := ⟨hp.ne_zero⟩
    simpa only [evaluation, eval₂_C, Int.coe_castRingHom, Int.toNat_natCast] using
      (congrArg Int.toNat (ZMod.val_intCast (n := p) (c w))).symm

/-- A selected coordinate is controlled. The index is unary because it is
bounded by the polynomially many variables, whereas coordinate values are binary. -/
@[expose] noncomputable def coordinate (hn : ComputableInPolyTime n enc encUnary)
    (i : (w : α) → Fin (n w))
    (hi : ComputableInPolyTime (fun w => (i w).val) enc encUnary) :
    Controlled (fun w => X (i w) : (w : α) → MvPolynomial (Fin (n w)) ℤ) enc a where
  arity_computable := hn
  degreeBound := fun _ => 1
  degree_computable := .const 1
  degree_le w := by simp only [totalDegree_X, le_refl]
  massExponent := fun _ => 0
  mass_computable := .const 0
  mass_le w := by simp only [Algebra.MvMass.X, pow_zero, le_refl]
  cutoff := fun _ => 0
  cutoff_computable := .const 0
  evaluate := fun q => q.2.2[(i q.1).val]?.getD 0 % q.2.1
  evaluate_mem := by
    apply CountingFunction.of_polyTime
    have hindex : ComputableInPolyTime
        (fun q : α × (ℕ × List ℕ) => (i q.1).val) (encEvaluation enc) encUnary :=
      hi.comp (ComputableInPolyTime.fst _ _)
    fun_prop
  evaluate_eq w p z hp _ := by
    let : NeZero p := ⟨hp.ne_zero⟩
    simp only [evaluation, eval₂_X, ZMod.val_natCast]

/-- Adding controlled polynomials preserves the common counting level. -/
@[expose] noncomputable def add (CP : Controlled P enc a) (CQ : Controlled Q enc a) :
    Controlled (fun w => P w + Q w) enc a where
  arity_computable := CP.arity_computable
  degreeBound := fun w => max (CP.degreeBound w) (CQ.degreeBound w)
  degree_computable := ComputableInPolyTime.binary_max' CP.degree_computable CQ.degree_computable
  degree_le w := (totalDegree_add _ _).trans (max_le_max (CP.degree_le w) (CQ.degree_le w))
  massExponent := fun w => CP.massExponent w + CQ.massExponent w + 1
  mass_computable := by
    exact ComputableInPolyTime.binary_add'
      (ComputableInPolyTime.binary_add' CP.mass_computable CQ.mass_computable) (.const 1)
  mass_le w := by
    apply (Algebra.MvMass.add_le _ _).trans
    apply (Nat.add_le_add (CP.mass_le w) (CQ.mass_le w)).trans
    have hp : 2 ^ CP.massExponent w ≤ 2 ^ (CP.massExponent w + CQ.massExponent w) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    have hq : 2 ^ CQ.massExponent w ≤ 2 ^ (CP.massExponent w + CQ.massExponent w) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    rw [pow_succ]
    omega
  cutoff := fun w => max (CP.cutoff w) (CQ.cutoff w)
  cutoff_computable := ComputableInPolyTime.binary_max' CP.cutoff_computable CQ.cutoff_computable
  evaluate := fun q => (CP.evaluate q + CQ.evaluate q) % q.2.1
  evaluate_mem := CountingFunction.nat_mod
    (CountingFunction.map (CountingFunction.prod CP.evaluate_mem CQ.evaluate_mem)
      ComputableInPolyTime.binary_add)
    (CountingFunction.of_polyTime (by fun_prop))
  evaluate_eq w p z hp hcut := by
    let : NeZero p := ⟨hp.ne_zero⟩
    rw [CP.evaluate_eq w p z hp (lt_of_le_of_lt (le_max_left _ _) hcut),
      CQ.evaluate_eq w p z hp (lt_of_le_of_lt (le_max_right _ _) hcut)]
    simp only [evaluation, eval₂_add, ZMod.val_add]

/-- Multiplication uses only the two modular values and ordinary modular arithmetic. -/
@[expose] noncomputable def mul (CP : Controlled P enc a) (CQ : Controlled Q enc a) :
    Controlled (fun w => P w * Q w) enc a where
  arity_computable := CP.arity_computable
  degreeBound := fun w => CP.degreeBound w + CQ.degreeBound w
  degree_computable := ComputableInPolyTime.binary_add' CP.degree_computable CQ.degree_computable
  degree_le w := (totalDegree_mul _ _).trans (Nat.add_le_add (CP.degree_le w) (CQ.degree_le w))
  massExponent := fun w => CP.massExponent w + CQ.massExponent w
  mass_computable := ComputableInPolyTime.binary_add' CP.mass_computable CQ.mass_computable
  mass_le w := by
    apply (Algebra.MvMass.mul_le _ _).trans
    simpa only [pow_add] using Nat.mul_le_mul (CP.mass_le w) (CQ.mass_le w)
  cutoff := fun w => max (CP.cutoff w) (CQ.cutoff w)
  cutoff_computable := ComputableInPolyTime.binary_max' CP.cutoff_computable CQ.cutoff_computable
  evaluate := fun q => CP.evaluate q * CQ.evaluate q % q.2.1
  evaluate_mem := CountingFunction.nat_mod
    (CountingFunction.nat_mul CP.evaluate_mem CQ.evaluate_mem)
    (CountingFunction.of_polyTime (by fun_prop))
  evaluate_eq w p z hp hcut := by
    rw [CP.evaluate_eq w p z hp (lt_of_le_of_lt (le_max_left _ _) hcut),
      CQ.evaluate_eq w p z hp (lt_of_le_of_lt (le_max_right _ _) hcut)]
    simp only [evaluation, eval₂_mul, ZMod.val_mul]

/-- Binary exponents may have exponential value. Modular powering preserves the
level, while degree and logarithmic mass bounds require only binary multiplication. -/
@[expose] noncomputable def pow (CP : Controlled P enc a) (e : α → ℕ)
    (he : ComputableInPolyTime e enc encNat) : Controlled (fun w => P w ^ e w) enc a where
  arity_computable := CP.arity_computable
  degreeBound := fun w => CP.degreeBound w * e w
  degree_computable := ComputableInPolyTime.binary_mul' CP.degree_computable he
  degree_le w := by
    simpa only [Nat.mul_comm] using
      (totalDegree_pow (P w) (e w)).trans (Nat.mul_le_mul_left (e w) (CP.degree_le w))
  massExponent := fun w => CP.massExponent w * e w
  mass_computable := ComputableInPolyTime.binary_mul' CP.mass_computable he
  mass_le w := by
    apply (Algebra.MvMass.pow_le _ _).trans
    simpa only [pow_mul] using Nat.pow_le_pow_left (CP.mass_le w) (e w)
  cutoff := CP.cutoff
  cutoff_computable := CP.cutoff_computable
  evaluate := fun q => powMod q.2.1 (CP.evaluate q) (e q.1)
  evaluate_mem := CountingFunction.powMod
    (CountingFunction.of_polyTime (by fun_prop)) CP.evaluate_mem
    (CountingFunction.of_polyTime (he.comp (ComputableInPolyTime.fst _ _)))
  evaluate_eq w p z hp hcut := by
    let : NeZero p := ⟨hp.ne_zero⟩
    rw [CP.evaluate_eq w p z hp hcut, powMod_of_ne_zero hp.ne_zero]
    rw [← ZMod.val_natCast, Nat.cast_pow]
    simp only [evaluation, ZMod.natCast_zmod_val, eval₂_pow]

end Controlled
end LeanCanny.CountingHierarchy
