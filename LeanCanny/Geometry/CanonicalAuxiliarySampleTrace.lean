/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.CanonicalAuxiliaryCutWitness

/-! # Finite traces of actual correlated limit-coordinate births

Every edge records the literal tagged command, selected factor, actual scalar
root and restriction to the preceding hom. The terminal source may be a pure
reframe; no equality with a family's padding/default source is asserted.
-/
@[expose] public section
namespace LeanCanny.Geometry.CanonicalAuxiliaryTrajectory
open LeanCanny.Algebra LeanCanny.ETR IntegralMixedHistory
open AuxiliaryTiltedTerm FrozenAuxiliaryComponentSampling SampleFrame
open scoped Classical
variable {n S B D : ℕ} {t : Term} {ht : (term n t).degreeBound≤D}

inductive SampleTrace (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+3) (FixedLeadingTiltedSource.degree D)≤2^B) :
    SampleFrame n S B D t ht → ℕ → SampleFrame n S B D t ht → Prop
  | nil (F) : SampleTrace hcap F 0 F
  | cut {F L r} (hk : F.frozen<n) (b : slice (polynomial n t) F.frozen F.parameters)
      (W : CutWitness F hk b) (tail : SampleTrace hcap (W.frame hcap) r L) :
      SampleTrace hcap F (r+1) L

namespace SampleTrace
variable {hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+3) (FixedLeadingTiltedSource.degree D)≤2^B}
    {F L : SampleFrame n S B D t ht} {r : ℕ}

theorem frozen_count (H : SampleTrace hcap F r L) : L.frozen=F.frozen+r := by
  induction H with
  | nil F => omega
  | @cut F L r hk b W tail ih =>
    change _=(F.frozen+1)+_ at ih
    omega

theorem birth_count (H : SampleTrace hcap F r L) : L.birth=F.birth+r := by
  induction H with
  | nil F => omega
  | @cut F L r hk b W tail ih =>
    change _=(F.birth+1)+_ at ih
    omega

theorem length_le (H : SampleTrace hcap F r L) : r≤n-F.frozen := by
  have HC := frozen_count H
  have HL := L.frozen_le
  omega

theorem old_hom (H : SampleTrace hcap F r L) :
    ∃ ρ : F.state.sampler.scalarPrefix.carrier →ₐ[ℤ] L.state.sampler.scalarPrefix.carrier,
      L.hom.comp ρ=F.hom := by
  induction H with
  | nil F => exact ⟨AlgHom.id ℤ _,rfl⟩
  | @cut F L r hk b W tail ih =>
    obtain ⟨ρ,hρ⟩ := ih
    let α : F.state.sampler.scalarPrefix.carrier →ₐ[ℤ] (W.frame hcap).state.sampler.scalarPrefix.carrier :=
      AdjoinRoot.ofAlgHom ℤ _
    refine ⟨ρ.comp α,?_⟩
    apply AlgHom.ext
    intro a
    have H1 := congrArg (fun χ => χ (α a)) hρ
    have H2 := congrArg (fun χ => χ a) W.restricts
    exact H1.trans H2

theorem old_tuple (H : SampleTrace hcap F r L) :
    ∃ keep : F.carrier → L.carrier, Function.Injective keep ∧ ∀ i, L.root (keep i)=F.root i := by
  induction H with
  | nil F => exact ⟨id,Function.injective_id,fun _ => rfl⟩
  | @cut F L r hk b W tail ih =>
    obtain ⟨keep,hkeep,hroot⟩ := ih
    refine ⟨fun i => keep (Sum.inl i),hkeep.comp Sum.inl_injective,fun i => ?_⟩
    exact (hroot (Sum.inl i)).trans (W.keeps i)

end SampleTrace
end LeanCanny.Geometry.CanonicalAuxiliaryTrajectory
