/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedTraceCutExact
/-! # The terminal suffix determines one selected parent embedding

Full cut compatibility does not merely assert existence in some conjugate
component. The complete joint tuple fixes every old basis generator, hence
fixes the entire algebra homomorphism. This is the selected-parent interface
needed before applying geometric frame continuation. A frame and its actual
record-to-frame syntax agreement remain separate geometric requirements.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedTraceCutSelectedParent
open LeanCanny.Algebra IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open IntegralFramedTraceCutMetadata (terminal terminal_positive)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family
variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
  (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
  (r u w : List Bool)
  (hv : SquareSampleCompleteVertices.Valid (IntegralFramedTraceCutSource.input P D H L F C hs) r w)
local notation "c" => IntegralFramedTraceCutTask.task P (pair r (pair u []))
local notation "G" => family P D H
local notation "parent" => IntegralMixedVirtualTaskBits.saved P c
local notation "old" => IntegralMixedCutSource.Family.state G parent
local notation "degree" => IntegralMixedCutSource.Family.degree G parent
local notation "rule" => IntegralMixedCutSource.Family.rule G parent
local notation "kind" => IntegralMixedCutSource.Family.kind G parent
local notation "bound" => IntegralMixedCutSource.Family.birth_bound G parent
local notation "factor" => IntegralMixedRelativeCuts.factor old bound rule kind
local notation "M" => IntegralMixedCutSource.Family.birth G (terminal P D r)
local notation "z" => IntegralFramedCompleteSuffix.joint P D H L F C hs (terminal P D) (terminal_positive P D H) r w hv
local notation "bankPoint" => IntegralMixedFramedBankObservation.Data.point
  (IntegralMixedFramedBankObservation.ofState (IntegralMixedCutSource.Family.state G (terminal P D r))) z (M-birth P c-1)

noncomputable def At (φ : (old).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) : Prop :=
  (∀ i,φ ((old).sampler.scalarPrefix.basis.generator i)=z (i.val+(M-(G).birth parent))^
    UniformIntegralPowerSchedule.weights (IntegralMixedFramedChoiceProbeSourceBits.horizon P c)
      (2^(G).width parent) ((G).birth parent) i) ∧
  IntegralMixedRelativeCuts.Valid old bound rule φ kind ∧ ((factor).map φ.toRingHom).natDegree=degree ∧
  (factor).eval₂ φ.toRingHom bankPoint=0

theorem unique {φ ψ : (old).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ}
    (hφ : At P D H L F C hs r u w hv φ) (hψ : At P D H L F C hs r u w hv ψ) : φ=ψ := by
  apply (old).sampler.scalarPrefix.basis.algHom_ext
  intro i
  exact (hφ.1 i).trans (hψ.1 i).symm

theorem compatible_iff_existsUnique : IntegralFramedTraceCutExact.Compatible P D H L F C hs r u w hv ↔
    ∃! φ,At P D H L F C hs r u w hv φ := by
  constructor
  · rintro ⟨φ,hφ⟩
    refine ⟨φ,hφ,fun ψ hψ=>?_⟩
    exact unique P D H L F C hs r u w hv hψ hφ
  · rintro ⟨φ,hφ,_⟩
    exact ⟨φ,hφ⟩

/-- Any geometric construction using this literal old tuple receives the
same validity, degree and root facts; there is no independent embedding. -/
theorem compatible_at (hc : IntegralFramedTraceCutExact.Compatible P D H L F C hs r u w hv)
    (φ : (old).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hφ : ∀ i,φ ((old).sampler.scalarPrefix.basis.generator i)=z (i.val+(M-(G).birth parent))^
      UniformIntegralPowerSchedule.weights (IntegralMixedFramedChoiceProbeSourceBits.horizon P c)
        (2^(G).width parent) ((G).birth parent) i) :
    IntegralMixedRelativeCuts.Valid old bound rule φ kind ∧ ((factor).map φ.toRingHom).natDegree=degree ∧
      (factor).eval₂ φ.toRingHom bankPoint=0 := by
  obtain ⟨ψ,hψ,hfacts⟩:=hc
  have HE : ψ=φ := by
    apply (old).sampler.scalarPrefix.basis.algHom_ext
    intro i
    exact (hψ i).trans (hφ i).symm
  exact HE ▸ hfacts
end LeanCanny.Encoding.IntegralFramedTraceCutSelectedParent
