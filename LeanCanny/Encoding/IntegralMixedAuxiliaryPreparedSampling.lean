/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedAuxiliaryRecipeRealization
public import LeanCanny.Geometry.CanonicalAuxiliarySeededSampling
/-! # Every original clopen piece has an actual packed empty-plan sample

Only n bounded original cut-label pairs are serialized. The source schedule
uses the same n-record horizon and the original seed plus one throughout.
The terminal readback belongs to the actual saved family at prefix n.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedAuxiliaryRecipeRoot
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript
open IntegralMixedAuxiliaryParameters IntegralMixedAuxiliarySchedule
open LeanCanny.Geometry.CanonicalAuxiliaryTrajectory AuxiliaryTiltedTerm
open LeanCanny.Geometry.CoerciveComponentSampling
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] terminalState scalarWidth scalarCeiling spatialDegree planAt

theorem exists_prepared_sample_uniform {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q)
    (original : List Bool)
    (C : Set (Zeros (polynomial (n original) (t original)))) (hC : IsClopen C)
    (x0 : Zeros (polynomial (n original) (t original))) (hx0 : x0∈C) :
    ∃ labels : Fin (n original) → ℕ × ℕ,
      (∀ i,(labels i).1≤scalarCeiling n t original ∧ (labels i).2≤scalarCeiling n t original) ∧
      ∃ p : Zeros (polynomial (n original) (t original)), p∈C ∧
        ∀ advice context, OriginalRealization (terminalState hn ht ha original labels advice context) p.val := by
  have Hword : wordBudget (n original) (degreeCharge n t original) (t original)≤seed n t original+1 := by
    simp only [seed,originalSeed,Nat.zero_add]
    omega
  obtain ⟨L,_,hbirth,Htrace,p,hp,hread⟩ := exists_closed_seeded_sample
    (D:=degreeCharge n t original) (S:=n original+3) (B:=scalarWidth n t original)
    (t original) (augmented n t original).degreeBound_le_dataSize (ha original) (by omega)
    (recipeCap n t original) (seed n t original+1) (by omega) Hword C hC x0 hx0
  obtain ⟨labels,hcs,hBounds,hIndex,hState⟩ := Htrace.exists_label_run (by omega)
    (recipeCap n t original) (seed n t original+1) (by omega) Hword
  have HL : OriginalRealization L.state p.val := ⟨L.root,L.root_eq,L.hom,L.interprets,hread⟩
  have HB : ∀ i,(labels i).1≤scalarCeiling n t original ∧ (labels i).2≤scalarCeiling n t original := by
    simpa only [scalarCeiling,spatialDegree] using hBounds
  refine ⟨labels,HB,p,hp,?_⟩
  intro advice context
  exact terminal_realization_of_replay hn ht ha original labels advice context L hbirth hcs hIndex hState p.val HL
theorem exists_prepared_sample {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q)
    (original advice context : List Bool)
    (C : Set (Zeros (polynomial (n original) (t original)))) (hC : IsClopen C)
    (x0 : Zeros (polynomial (n original) (t original))) (hx0 : x0∈C) :
    ∃ labels : Fin (n original) → ℕ × ℕ,
      (∀ i,(labels i).1≤scalarCeiling n t original ∧ (labels i).2≤scalarCeiling n t original) ∧
      ∃ p : Zeros (polynomial (n original) (t original)), p∈C ∧
        OriginalRealization (terminalState hn ht ha original labels advice context) p.val := by
  obtain ⟨labels,hb,p,hp,hr⟩:=exists_prepared_sample_uniform hn ht ha original C hC x0 hx0
  exact ⟨labels,hb,p,hp,hr advice context⟩
end LeanCanny.Encoding.IntegralMixedAuxiliaryRecipeRoot
