/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineExceptionalBankCriticalData

/-! # Explicit polynomial specialization guards for independent companions

Independent integer companions can choose unrelated roots. For every bank
entry this module tests its powered scalar slot against the original integer
leading coefficient times the retained physical coordinate. An extra physical
coordinate carries the independently labeled exceptional scalar. Its equality
with that label, and the original parent label, are explicit frame conditions.

These guards imply the exact recovery premises used by CriticalData_slice.
Their integer coefficients and degree budgets come from the initial source.
A native polynomial-test decision still needs the mixed sampler's Access;
no such Access or connectivity oracle is assumed here.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineExceptionalBankCorrelation
open LeanCanny.Algebra LeanCanny.Computation MvPolynomial
open FlatAffineFullSourceTower (Inputs arity)
open FlatAffineCompleteRootStages (next)
open FlatAffineLastHeightRow (parentCone)
open FlatAffineExceptionalBankSource (births width finitePolynomial)
open FlatAffineExceptionalParentBank (bank values)
open IntegralIntegerRootBank (Index)
open scoped Classical

private theorem numerator_generators {S B : ℕ} {ι : Type} [Fintype ι]
    (F : IntegralHistorySampler.Sampler S (2 ^ B) 0 ι) (m : ℕ)
    (p : Fin m → Polynomial ℤ) (hp : ∀ i, p i ≠ 0) (hm : m ≤ S + 1) (i : Fin m) :
    (IntegralIntegerRootBank.run F m p hp hm).bank.numerator i =
      (IntegralIntegerRootBank.run F m p hp hm).sampler.scalarPrefix.basis.generator i := by
  induction m with
  | zero => exact Fin.elim0 i
  | succ m ih =>
    refine Fin.cases rfl (fun j => ?_) i
    exact congrArg (AdjoinRoot.of _) (ih (fun i => p i.succ) (fun i => hp i.succ) (by omega) j)

abbrev HistoryIndex (F : Inputs) (u : List Bool) :=
  Index (Fin (FlatAffineFullSourcePositive.count F u)) (births F u)
abbrev JointIndex (F : Inputs) (u : List Bool) := HistoryIndex F u ⊕ Unit

def target (F : Inputs) (u : List Bool) (i : Fin (births F u)) : JointIndex F u :=
  Fin.cases (Sum.inr ()) (fun j => Sum.inl (IntegralIntegerRootBank.old (births F u) j)) i

noncomputable def guard (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (S : ℕ) (u : List Bool) (hm : births F u ≤ S + 1)
    (i : Fin (births F u)) : MvPolynomial (JointIndex F u) ℤ :=
  X (Sum.inl ((bank F C h S u hm).sampler.scalar i)) ^
      UniformIntegralPowerSchedule.weights S (2 ^ width F u) (births F u) i -
    MvPolynomial.C (finitePolynomial F C h u i).leadingCoeff * X (target F u i)

theorem guard_eval (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (S : ℕ) (u : List Bool) (hm : births F u ≤ S + 1)
    (i : Fin (births F u)) (z : JointIndex F u → ℝ) :
    (guard F C h S u hm i).eval₂ (Int.castRingHom ℝ) z =
      z (Sum.inl ((bank F C h S u hm).sampler.scalar i)) ^
        UniformIntegralPowerSchedule.weights S (2 ^ width F u) (births F u) i -
      ((finitePolynomial F C h u i).leadingCoeff : ℝ) * z (target F u i) := by
  simp only [guard, eval₂_sub, eval₂_pow, eval₂_X, eval₂_mul, eval₂_C, Int.coe_castRingHom]

def Correlated (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (S : ℕ) (u : List Bool) (hm : births F u ≤ S + 1)
    (z : JointIndex F u → ℝ) : Prop :=
  ∀ i, (guard F C h S u hm i).eval₂ (Int.castRingHom ℝ) z = 0

structure MatchesFrame (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (u v a : List Bool)
    (hv : FlatAffineCompleteVertices.Valid F (parentCone F C) u v) (z : JointIndex F u → ℝ) : Prop where
  parent : ∀ i, z (Sum.inl (IntegralIntegerRootBank.old (births F u) i)) =
    (SquareSampleCompleteVertices.candidate (FlatAffinePowerSampleInput.input F (parentCone F C)) u v hv).val i
  scalar : z (Sum.inr ()) = FlatAffineExceptionalSliceFrame.scalar F C h u a

theorem target_values (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (u v a : List Bool)
    (hv : FlatAffineCompleteVertices.Valid F (parentCone F C) u v) (z : JointIndex F u → ℝ)
    (H : MatchesFrame F C h u v a hv z) (i : Fin (births F u)) :
    z (target F u i) = values F C h u v a hv i := by
  refine Fin.cases H.scalar (fun j => H.parent j) i

theorem recovery_of_correlated (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (S : ℕ) (u v a : List Bool) (hm : births F u ≤ S + 1)
    (hv : FlatAffineCompleteVertices.Valid F (parentCone F C) u v)
    (z : JointIndex F u → ℝ) (Hframe : MatchesFrame F C h u v a hv z)
    (Hguard : Correlated F C h S u hm z)
    (φ : (bank F C h S u hm).sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ)
    (Hφ : ∀ i, φ ((bank F C h S u hm).sampler.scalarPrefix.basis.generator i) =
      z (Sum.inl ((bank F C h S u hm).sampler.scalar i)) ^
        UniformIntegralPowerSchedule.weights S (2 ^ width F u) (births F u) i)
    (i : Fin (births F u)) :
    φ ((bank F C h S u hm).bank.numerator i) / ((bank F C h S u hm).bank.denominator i : ℝ) =
      values F C h u v a hv i := by
  have HN : (bank F C h S u hm).bank.numerator i = (bank F C h S u hm).sampler.scalarPrefix.basis.generator i :=
    numerator_generators _ _ _ _ _ i
  have HG := Hguard i
  rw [guard_eval, sub_eq_zero] at HG
  have HD := FlatAffineExceptionalParentBank.denominator_eq F C h S u hm i
  have HZ : ((finitePolynomial F C h u i).leadingCoeff : ℝ) ≠ 0 :=
    Int.cast_ne_zero.mpr (Polynomial.leadingCoeff_ne_zero.mpr (FlatAffineExceptionalBankSource.finite_nonzero F C h u i))
  rw [HN, Hφ, HG, HD, mul_div_cancel_left₀ _ HZ]
  exact target_values F C h u v a hv z Hframe i

theorem exists_correlated_realization (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (S : ℕ) (u v a : List Bool) (hm : births F u ≤ S + 1)
    (hv : FlatAffineCompleteVertices.Valid F (parentCone F C) u v)
    (ha : SquareSampleCompleteVertices.Valid (IntegerPolynomialSampleInput.input (FlatAffineExceptionalSliceFrame.scalarSource F C h)) u a) :
    ∃ z : JointIndex F u → ℝ,
      ∃ φ : (bank F C h S u hm).sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ,
        (∀ j, ((bank F C h S u hm).sampler.rows j).eval₂ (Int.castRingHom ℝ) (z ∘ Sum.inl) = 0) ∧
        MatchesFrame F C h u v a hv z ∧ Correlated F C h S u hm z ∧
        ∀ i, φ ((bank F C h S u hm).sampler.scalarPrefix.basis.generator i) =
          z (Sum.inl ((bank F C h S u hm).sampler.scalar i)) ^
            UniformIntegralPowerSchedule.weights S (2 ^ width F u) (births F u) i := by
  obtain ⟨y, φ, hy, hold, Hφ, Hvalues⟩ := FlatAffineExceptionalParentBank.exists_realization F C h S u v a hm hv ha
  let z : JointIndex F u → ℝ := Sum.elim y (fun _ => FlatAffineExceptionalSliceFrame.scalar F C h u a)
  have Hframe : MatchesFrame F C h u v a hv z := ⟨hold, rfl⟩
  refine ⟨z, φ, hy, Hframe, ?_, Hφ⟩
  intro i
  have HN : (bank F C h S u hm).bank.numerator i = (bank F C h S u hm).sampler.scalarPrefix.basis.generator i :=
    numerator_generators _ _ _ _ _ i
  have HD := FlatAffineExceptionalParentBank.denominator_eq F C h S u hm i
  have HZ : ((bank F C h S u hm).bank.denominator i : ℝ) ≠ 0 :=
    Int.cast_ne_zero.mpr ((bank F C h S u hm).denominator_ne_zero i)
  have HE := (div_eq_iff HZ).mp (Hvalues i)
  rw [HN, Hφ i, HD] at HE
  rw [guard_eval, target_values F C h u v a hv z Hframe i]
  exact sub_eq_zero.mpr (HE.trans (mul_comm _ _))

theorem guard_degree (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (S : ℕ) (u : List Bool) (hm : births F u ≤ S + 1)
    (i : Fin (births F u)) : (guard F C h S u hm i).totalDegree ≤
      UniformIntegralPowerSchedule.birth S (2 ^ width F u) S := by
  let W := UniformIntegralPowerSchedule.weights S (2 ^ width F u) (births F u) i
  have HW : W ≤ UniformIntegralPowerSchedule.birth S (2 ^ width F u) S :=
    UniformIntegralPowerSchedule.birth_le S _ _ (by omega)
  have HP : (X (Sum.inl ((bank F C h S u hm).sampler.scalar i)) ^ W : MvPolynomial (JointIndex F u) ℤ).totalDegree ≤ W := by
    simpa only [one_mul] using ((isHomogeneous_X (R := ℤ) (Sum.inl ((bank F C h S u hm).sampler.scalar i))).pow W).totalDegree_le
  apply (totalDegree_sub _ _).trans
  apply max_le (HP.trans HW)
  exact (totalDegree_mul _ _).trans (by
    simp only [totalDegree_C, totalDegree_X, Nat.zero_add]
    exact UniformIntegralPowerSchedule.birth_pos S _ S)

theorem guard_mass (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (S : ℕ) (u : List Bool) (hm : births F u ≤ S + 1)
    (i : Fin (births F u)) : MvMass.mass (guard F C h S u hm i) ≤
      2 ^ (FlatAffineExceptionalBankSource.massBound F C h u + 1) := by
  have HP : MvMass.mass (X (Sum.inl ((bank F C h S u hm).sampler.scalar i)) ^
      UniformIntegralPowerSchedule.weights S (2 ^ width F u) (births F u) i : MvPolynomial (JointIndex F u) ℤ) ≤ 1 := by
    simpa only [MvMass.X, one_pow] using MvMass.pow_le (X (Sum.inl ((bank F C h S u hm).sampler.scalar i))) _
  have HL : (finitePolynomial F C h u i).leadingCoeff.natAbs ≤ 2 ^ FlatAffineExceptionalBankSource.massBound F C h u := by
    have H := FlatAffineExceptionalBankSource.mass_le F C h (pair u (BinaryNatCode.encode i.val))
    rw [pairFst_pair] at H
    exact (coeff_natAbs_le_coefficientMass _ _).trans H
  have HM := (MvMass.mul_le (MvPolynomial.C (finitePolynomial F C h u i).leadingCoeff) (X (target F u i))).trans
    (by simpa only [MvMass.C, MvMass.X, Nat.mul_one] using HL)
  have H := (MvMass.sub_le _ _).trans (Nat.add_le_add HP HM)
  rw [pow_succ]
  exact H.trans (by have HH : 1 ≤ 2 ^ FlatAffineExceptionalBankSource.massBound F C h u := Nat.one_le_two_pow; omega)

noncomputable def degreeBudget (F : Inputs) (s : List Bool → ℕ) (u : List Bool) : ℕ :=
  UniformIntegralPowerSchedule.birth (s u) (2 ^ width F u) (s u)

theorem degreeBudget_binary {F : Inputs} (hF : F.Access) (h : (u : List Bool) → Fin (arity F u))
    {s : List Bool → ℕ} (hs : UnaryFn s) : BinaryFn (degreeBudget F s) :=
  UniformIntegralPowerSchedule.birth_binary hs
    ((BinaryFn.const 2).powUnary (FlatAffineExceptionalBankSource.width_unary hF h)) hs

theorem massBudget_binary {F : Inputs} (hF : F.Access)
    (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (hh : UnaryFn (fun u => (h u).val)) :
    BinaryFn (fun u => FlatAffineExceptionalBankSource.massBound F C h u + 1) :=
  (FlatAffineExceptionalBankSource.massBound_binary hF C h hh).add (BinaryFn.const 1)

def rowRecord (u : List Bool) (i : ℕ) : List Bool := pair u (BinaryNatCode.encode i)

theorem rowRecord_polynomial {F : Inputs} (hF : F.Access) :
    ∃ p : Polynomial ℕ, ∀ u (i : Fin (births F u)), (rowRecord u i.val).length ≤ p.eval u.length := by
  have E : (fun u => pair u (List.replicate (births F u).size false)) ∈ FP :=
    mem_FP_pair id_mem_FP ((FlatAffineExceptionalBankSource.births_unary hF).size.replicate_mem_FP false)
  obtain ⟨p, hp⟩ := output_length_poly_of_mem_FP E
  refine ⟨p, ?_⟩
  intro u i
  have H : (BinaryNatCode.encode i.val).length ≤ (births F u).size := by
    rw [BinaryNatCode.length_encode]
    exact Nat.size_le_size i.isLt.le
  have HL : (rowRecord u i.val).length ≤ (pair u (List.replicate (births F u).size false)).length := by
    simpa only [rowRecord, pair_length, List.length_replicate] using Nat.add_le_add_left H (2 * u.length + 2)
  exact HL.trans (hp u)

end LeanCanny.Encoding.FlatAffineExceptionalBankCorrelation
