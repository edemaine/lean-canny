/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedCutProbeBounds
public import LeanCanny.Algebra.IntegralRelativeTruncation
/-! # Actual selected relative cut heads over integer raw variables

Only coefficients are represented canonically. Evaluating the resulting
integer polynomial at one raw tuple recovers the relative factor under
that tuple's SAME old hom, without taking an absolute norm.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedFullCutHead
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask Polynomial
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)

noncomputable def coefficientAt (old : List Bool) (k : ℕ) : MvPolynomial (Fin ((family P D H).birth old)) ℤ :=
  CoordinatePowerSubstitution.substitute
    (UniformIntegralPowerSchedule.weights (P.cap (pairFst old)+1) (2^(family P D H).width old) ((family P D H).birth old))
    (((family P D H).state old).sampler.scalarPrefix.basis.representative
      ((IntegralMixedRelativeCuts.factor ((family P D H).state old) ((family P D H).birth_bound old)
        ((family P D H).rule old) ((family P D H).kind old)).coeff k))

theorem coefficient_evaluation (old : List Bool) (k : ℕ)
    (z : Fin ((family P D H).birth old)→ℝ)
    (φ : ((family P D H).state old).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hφ : ∀i,φ (((family P D H).state old).sampler.scalarPrefix.basis.generator i)=
      z i^UniformIntegralPowerSchedule.weights (P.cap (pairFst old)+1) (2^(family P D H).width old) ((family P D H).birth old) i) :
    (coefficientAt P D H old k).eval₂ (Int.castRingHom ℝ) z=
      φ ((IntegralMixedRelativeCuts.factor ((family P D H).state old) ((family P D H).birth_bound old)
        ((family P D H).rule old) ((family P D H).kind old)).coeff k) :=by
  have HS:=CoordinatePowerSubstitution.eval_substitute (Int.castRingHom ℝ)
    (UniformIntegralPowerSchedule.weights (P.cap (pairFst old)+1) (2^(family P D H).width old) ((family P D H).birth old))
    (((family P D H).state old).sampler.scalarPrefix.basis.representative
      ((IntegralMixedRelativeCuts.factor ((family P D H).state old) ((family P D H).birth_bound old)
        ((family P D H).rule old) ((family P D H).kind old)).coeff k)) z
  have HE:=((family P D H).state old).sampler.scalarPrefix.basis.representative_eval_algHom
    ((IntegralMixedRelativeCuts.factor ((family P D H).state old) ((family P D H).birth_bound old)
      ((family P D H).rule old) ((family P D H).kind old)).coeff k) φ
  change (((family P D H).state old).sampler.scalarPrefix.basis.representative
    ((IntegralMixedRelativeCuts.factor ((family P D H).state old) ((family P D H).birth_bound old)
      ((family P D H).rule old) ((family P D H).kind old)).coeff k)).eval₂ (Int.castRingHom ℝ)
    (fun i=>φ (((family P D H).state old).sampler.scalarPrefix.basis.generator i))=_ at HE
  exact HS.trans (by simpa only [hφ] using HE)

noncomputable def coefficientDegree (old : List Bool) :=
  UniformIntegralPowerSchedule.birth (P.cap (pairFst old)+1) (2^(family P D H).width old) ((family P D H).birth old-1)*
    ((family P D H).birth old*(2^(family P D H).width old-1))

theorem coefficient_degree (old : List Bool) (k : ℕ) :
    (coefficientAt P D H old k).totalDegree≤coefficientDegree P D H old :=by
  apply (CoordinatePowerSubstitution.degree_le _ _ _ (UniformIntegralPowerSchedule.weights_le _ _ _)).trans
  exact Nat.mul_le_mul_left _ (((family P D H).state old).sampler.scalarPrefix.basis.representative_degree _)

noncomputable def coefficientMass (L F C : List Bool→ℕ) (old : List Bool) :=
  (family P D H).birth old*(family P D H).width old+IntegralMixedFramedRawHeight.rootCeiling P L F C (pairFst old)

theorem coefficient_mass (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
    (hF : ∀root,1≤F root) (hf : ∀old,IntegralMixedFramedOriginalBounds.FallbackBounds P D H L C old)
    (old : List Bool) (k : ℕ) : MvMass.mass (coefficientAt P D H old k)≤2^coefficientMass P D H L F C old :=by
  have HR : MvMass.mass (((family P D H).state old).sampler.scalarPrefix.basis.representative
      ((IntegralMixedRelativeCuts.factor ((family P D H).state old) ((family P D H).birth_bound old)
        ((family P D H).rule old) ((family P D H).kind old)).coeff k))≤
      FixedWidthPolynomial.count ((family P D H).birth old) ((family P D H).width old)*
        2^IntegralMixedFramedRawHeight.rootCeiling P L F C (pairFst old) :=by
    apply PaddedIntegralParameterExtension.representative_mass
    intro r
    exact IntegralMixedFramedRawHeight.coefficient_root_height P D H L F C hs hF hf old k r _
  apply (CoordinatePowerSubstitution.mass_le _ _).trans (HR.trans_eq ?_)
  unfold coefficientMass FixedWidthPolynomial.count
  rw [←pow_mul,←pow_add]
  congr 1
  ring

variable (parent : List Bool→List Bool) (d : List Bool→ℕ)
def saved (c : List Bool) :=IntegralMixedVirtualTaskBits.saved P (parent c)
def degree (c : List Bool) :=min (d c) (numericCap P (RankedHistoryTask.root (parent c)))
noncomputable def arity (c : List Bool) :=(family P D H).birth (saved P parent c)
noncomputable def head (c : List Bool) : Polynomial (MvPolynomial (Fin (arity P D H parent c)) ℤ) :=
  if IntegralMixedFramedFullCutProbeBits.Active P (parent c) then
    ∑k∈Finset.range (degree P parent d c+1),Polynomial.monomial k (coefficientAt P D H (saved P parent c) k) else 0

theorem head_coefficient (c : List Bool) (k : ℕ) : (head P D H parent d c).coeff k=
    if IntegralMixedFramedFullCutProbeBits.Active P (parent c) ∧ k≤degree P parent d c then
      coefficientAt P D H (saved P parent c) k else 0 :=by
  by_cases ha : IntegralMixedFramedFullCutProbeBits.Active P (parent c)
  · simp [head,ha,Polynomial.coeff_monomial,eq_comm]
  · simp [head,ha]

theorem head_degree (c : List Bool) : (head P D H parent d c).natDegree≤degree P parent d c :=by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  rw [head_coefficient,ite_eq_right (by omega)]

theorem head_evaluation (c : List Bool) (ha : IntegralMixedFramedFullCutProbeBits.Active P (parent c))
    (z : Fin (arity P D H parent c)→ℝ)
    (φ : ((family P D H).state (saved P parent c)).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hφ : ∀i,φ (((family P D H).state (saved P parent c)).sampler.scalarPrefix.basis.generator i)=
      z i^UniformIntegralPowerSchedule.weights (P.cap (pairFst (saved P parent c))+1)
        (2^(family P D H).width (saved P parent c)) ((family P D H).birth (saved P parent c)) i) :
    (head P D H parent d c).map (MvPolynomial.eval₂Hom (Int.castRingHom ℝ) z)=
      (IntegralRelativeTruncation.truncate
        (IntegralMixedRelativeCuts.factor ((family P D H).state (saved P parent c)) ((family P D H).birth_bound _)
          ((family P D H).rule _) ((family P D H).kind _)) (degree P parent d c)).map φ.toRingHom :=by
  ext k
  rw [Polynomial.coeff_map,head_coefficient,Polynomial.coeff_map,IntegralRelativeTruncation.coefficient]
  by_cases hk : k≤degree P parent d c
  · rw [ite_eq_left ⟨ha,hk⟩,ite_eq_left hk]
    exact coefficient_evaluation P D H (saved P parent c) k z φ hφ
  · rw [ite_eq_right (fun H=>hk H.2),ite_eq_right hk,map_zero,map_zero]

end LeanCanny.Algebra.IntegralMixedFramedFullCutHead
