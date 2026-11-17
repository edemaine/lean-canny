/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.CriticalEvaluationAccess
public import LeanCanny.CountingHierarchy.QuotientCharacteristicSpecialization

/-! # Source-specialized evaluation of the critical relations and Jacobian -/

public section

namespace LeanCanny.CountingHierarchy

open Cslib Cslib.Complexity Turing.MultiTapeTM MvPolynomial PurePowerResidue

@[expose] def criticalTraceDegreeBound (n d : ℕ) : ℕ := (d + 1) ^ n * (d + 2) + n * d

@[expose] def criticalCoefficientPrimeCutoff (n d : ℕ) : ℕ :=
  (d + 1) * (criticalTraceDegreeBound n d + 1) + 1 +
    (d + 1) ^ n + (d + 1) ^ n * (d + 1) ^ n + d + 6

theorem criticalCoefficientPrimeCutoff_polyTime {α : Type} {enc : α ↪ List Bool}
    {n d : α → ℕ} (hn : ComputableInPolyTime n enc encUnary)
    (hd : ComputableInPolyTime d enc encNat) :
    ComputableInPolyTime (fun w => criticalCoefficientPrimeCutoff (n w) (d w)) enc encNat := by
  have hnb := ComputableInPolyTime.unary_to_binary.comp hn
  have he := ComputableInPolyTime.binary_add' hd (.const 1)
  have hD := ComputableInPolyTime.binary_pow' he hn
  have hB := ComputableInPolyTime.binary_add'
    (ComputableInPolyTime.binary_mul' hD (ComputableInPolyTime.binary_add' hd (.const 2)))
    (ComputableInPolyTime.binary_mul' hnb hd)
  have hgrid := ComputableInPolyTime.binary_add'
    (ComputableInPolyTime.binary_mul' he (ComputableInPolyTime.binary_add' hB (.const 1))) (.const 1)
  exact ComputableInPolyTime.binary_add' (ComputableInPolyTime.binary_add'
    (ComputableInPolyTime.binary_add' (ComputableInPolyTime.binary_add' hgrid hD)
      (ComputableInPolyTime.binary_mul' hD hD)) hd) (.const 6)

theorem criticalParameterResidue_cast {p : ℕ} [Fact p.Prime] (n d b : ℕ) :
    (criticalParameterResidue p n d b : ZMod p) = (criticalIntegerParameter n d b : ZMod p) := by
  rw [criticalParameterResidue, powMod_of_ne_zero (Fact.out : p.Prime).ne_zero,
    ZMod.natCast_mod, Nat.cast_pow, criticalIntegerParameter, Int.cast_pow, Int.cast_ofNat, Nat.cast_ofNat]

theorem criticalCutoffResidue_cast {p : ℕ} [Fact p.Prime] (n d b : ℕ) :
    (criticalCutoffResidue p n d b : ZMod p) = (criticalIntegerCutoff n d b : ZMod p) := by
  rw [criticalCutoffResidue, powMod_of_ne_zero (Fact.out : p.Prime).ne_zero,
    ZMod.natCast_mod, Nat.cast_pow, criticalIntegerCutoff, Int.cast_pow, Int.cast_ofNat, Nat.cast_ofNat]

theorem finiteCriticalRelations_map_field {p n : ℕ} [Fact p.Prime] (d b : ℕ)
    (F : MvPolynomial (Fin n) ℤ) (i : Fin n) :
    (finiteCriticalRelations d b F i).map (Int.castRingHom (ZMod p)) =
      criticalLower (d + 1) (fun j => ((separatedCenters (d + 1) j : ℕ) : ZMod p))
        (criticalParameterResidue p n d b : ZMod p) (F.map (Int.castRingHom (ZMod p))) i := by
  rw [finiteCriticalRelations, criticalLower_map]
  simp only [Int.coe_castRingHom, Int.cast_natCast]
  rw [criticalParameterResidue_cast]

theorem finiteCriticalObjective_map_field {p n : ℕ} [Fact p.Prime] (d b : ℕ)
    (F : MvPolynomial (Fin n) ℤ) :
    (finiteCriticalObjective d b F).map (Int.castRingHom (ZMod p)) =
      deformedPolynomial (d + 1) (fun j => ((separatedCenters (d + 1) j : ℕ) : ZMod p))
        (criticalParameterResidue p n d b : ZMod p) (F.map (Int.castRingHom (ZMod p))) := by
  rw [finiteCriticalObjective, deformedPolynomial_map]
  simp only [Int.coe_castRingHom, Int.cast_natCast]
  rw [criticalParameterResidue_cast]

/-- The constructed evaluation programs equal evaluation of the actual
source integer objective, relations and Jacobian after coefficient reduction. -/
theorem sourceCriticalEvaluation_cast {p n : ℕ} [Fact p.Prime] (d b : ℕ)
    (F : MvPolynomial (Fin n) ℤ) (hF : F.totalDegree ≤ d + 1)
    (hcut : criticalCoefficientPrimeCutoff n d < p) (z : List ℕ) (value : List ℕ → ℕ)
    (hv : ∀ y, (value y : ZMod p) = eval
      (fun i : Fin n => ((y[i.val]?.getD 0 : ℕ) : ZMod p)) (F.map (Int.castRingHom (ZMod p)))) :
    ((criticalObjectiveValue p n (d + 1) (criticalParameterResidue p n d b) z value : ZMod p) =
      eval (fun i : Fin n => ((z[i.val]?.getD 0 : ℕ) : ZMod p))
        ((finiteCriticalObjective d b F).map (Int.castRingHom (ZMod p)))) ∧
    ((criticalJacobianValue p n (d + 1) (criticalParameterResidue p n d b) z value : ZMod p) =
      eval (fun i : Fin n => ((z[i.val]?.getD 0 : ℕ) : ZMod p))
        ((jacobian (d + 1) (finiteCriticalRelations d b F)).map (Int.castRingHom (ZMod p)))) ∧
    (∀ i : Fin n,
      (criticalLowerValue p n (d + 1) (criticalParameterResidue p n d b) i.val z value : ZMod p) =
        eval (fun j : Fin n => ((z[j.val]?.getD 0 : ℕ) : ZMod p))
          ((finiteCriticalRelations d b F i).map (Int.castRingHom (ZMod p)))) := by
  have hp : 3 < p := by unfold criticalCoefficientPrimeCutoff at hcut; omega
  have hdeg : (F.map (Int.castRingHom (ZMod p))).totalDegree < p - 1 := by
    apply (map_degree_le _ F).trans_lt
    unfold criticalCoefficientPrimeCutoff at hcut
    omega
  refine ⟨?_, ?_, ?_⟩
  · rw [finiteCriticalObjective_map_field]
    exact criticalObjectiveValue_cast _ _ _ z value hv
  · rw [jacobian_map]
    have hr : (fun i => (finiteCriticalRelations d b F i).map (Int.castRingHom (ZMod p))) =
        criticalLower (d + 1) (fun j => ((separatedCenters (d + 1) j : ℕ) : ZMod p))
          (criticalParameterResidue p n d b : ZMod p) (F.map (Int.castRingHom (ZMod p))) := by
      funext i
      exact finiteCriticalRelations_map_field d b F i
    rw [hr]
    exact criticalJacobianValue_cast _ _ _ z value hdeg hp hv
  · intro i
    rw [finiteCriticalRelations_map_field]
    exact criticalLowerValue_cast _ _ _ i z value hdeg hp hv

end LeanCanny.CountingHierarchy
