/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedCompanionKeyTransport
/-! # Honest original-root pullback of changing-source histories

An augmented root can carry an additional caller modulus while every source,
instruction and retained prefix is read from the complete projected original
root. Only the task modulus budget is enlarged. No old root is decoded as a
new instruction table and no caller modulus is clipped.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedRootPullback
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan prefixLength)
open scoped Classical

def parameters (P : Parameters) (project : List Bool → List Bool) (extra : List Bool → ℕ) : Parameters where
  cap := P.cap ∘ project
  width := P.width ∘ project
  ambient := P.ambient ∘ project
  sourceWidth := P.sourceWidth ∘ project
  degree := P.degree ∘ project
  height := P.height ∘ project
  modulusBound root := max (P.modulusBound (project root)) (extra root)

theorem access (P : Parameters) (a : Access P) (project : List Bool → List Bool)
    (hp : project∈FP) (extra : List Bool → ℕ) (he : BinaryFn extra) : Access (parameters P project extra) where
  cap := a.cap.comp hp
  width := a.width.comp hp
  ambient := a.ambient.comp hp
  sourceWidth := a.sourceWidth.comp hp
  degree := a.degree.comp hp
  height := a.height.comp hp
  modulusBound := by
    have HB : BinaryFn (fun root => P.modulusBound (project root)) := a.modulusBound.comp hp
    exact (BinaryFn.ite (HB.le he) he HB).of_eq (fun root => by
      change (if P.modulusBound (project root)≤extra root then extra root else P.modulusBound (project root))=max (P.modulusBound (project root)) (extra root)
      by_cases h : P.modulusBound (project root)≤extra root
      · rw [ite_eq_left h,max_eq_right h]
      · rw [ite_eq_right h,max_eq_left (by omega)])

noncomputable def plan (P : Parameters) (D : Plan P) (project : List Bool → List Bool) (extra : List Bool → ℕ) :
    Plan (parameters P project extra) where
  initialSource root := D.initialSource (project root)
  initial_degree root := D.initial_degree (project root)
  scalar_cap root := D.scalar_cap (project root)
  rules root := D.rules (project root)
  room root := D.room (project root)

def key (project : List Bool → List Bool) (q : List Bool) : List Bool :=
  pair (project (pairFst q)) (pairSnd q)

theorem key_FP (project : List Bool → List Bool) (hp : project∈FP) : key project∈FP :=
  mem_FP_pair (mem_FP_comp pairFst_mem_FP hp) pairSnd_mem_FP

theorem key_root (project : List Bool → List Bool) (q : List Bool) : pairFst (key project q)=project (pairFst q) :=
  pairFst_pair _ _

theorem key_prefix (P : Parameters) (project : List Bool → List Bool) (extra : List Bool → ℕ) (q : List Bool) :
    prefixLength P (key project q)=prefixLength (parameters P project extra) q := by
  simp only [prefixLength,IntegralMixedFullHistoryFamilyBits.prefixLength,key,pairFst_pair,pairSnd_pair,parameters,Function.comp_apply]

def profile (P : Parameters) (project : List Bool → List Bool) (extra : List Bool → ℕ)
    (k : IntegralMixedFramedCompanionBits.PrefixKey (parameters P project extra)) :
    IntegralMixedFramedCompanionBits.PrefixKey P :=
  ⟨project k.root,k.birth,k.bounded⟩

theorem source_atPrefix (P : Parameters) (D : Plan P) (project : List Bool → List Bool) (extra : List Bool → ℕ)
    (k : IntegralMixedFramedCompanionBits.PrefixKey (parameters P project extra)) :
    IntegralMixedFramedCompanionBits.atPrefix (parameters P project extra) (plan P D project extra) k=
      IntegralMixedFramedCompanionBits.atPrefix P D (profile P project extra k) := by
  rfl

theorem modulus_budget (P : Parameters) (project : List Bool → List Bool) (extra : List Bool → ℕ) (root : List Bool) :
    extra root≤numericCap (parameters P project extra) root :=
  (le_max_right _ _).trans (IntegralCriticalQueryBounds.metadata_le _ _ _ _ _ _ _ _).2.2.2.2.2.2.2

end LeanCanny.Algebra.IntegralMixedFramedRootPullback
