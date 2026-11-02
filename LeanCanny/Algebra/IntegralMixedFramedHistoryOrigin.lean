/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedHistoryScript
public import LeanCanny.Algebra.IntegralScalarGeneratorOrigin
/-! # Source-local producer origins in a changing-source history

The creator state is the actual older prefix reframed at the creator's source.
Its companion embeds into the final prefix, and its original integer leading
remains the retained denominator. No earlier command is replayed at a later
source, and producer birth indices still decrease inside the original root.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedHistoryScript
open LeanCanny.Encoding LeanCanny.Computation UniformIntegralPrefix IntegralMixedHistory
open scoped Classical
variable {n S B : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]

def older (cs : List (Instruction n B)) (i : Fin cs.length) := cs.drop (i.val+1)
def chosen (cs : List (Instruction n B)) (i : Fin cs.length) := cs[i.val]

theorem older_length (cs : List (Instruction n B)) (i : Fin cs.length) :
    (older cs i).length=cs.length-1-i.val := by
  simp only [older, List.length_drop]
  omega

theorem older_bound (cs : List (Instruction n B)) (h : cs.length≤S+1) (i : Fin cs.length) :
    (older cs i).length≤S := by
  have H := i.isLt
  rw [older_length]
  omega

noncomputable def birthState (initial : State P S B 0 ι) (cs : List (Instruction n B))
    (h : cs.length≤S+1) (i : Fin cs.length) :=
  reframe (run initial (older cs i) ((older_bound cs h i).trans (Nat.le_add_right S 1)))
    (chosen cs i).source (chosen cs i).source_cap

noncomputable def birthPrefix (initial : State P S B 0 ι) (cs : List (Instruction n B))
    (h : cs.length≤S+1) (i : Fin cs.length) :=
  UniformIntegralPrefix.step (birthState initial cs h i).sampler.scalarPrefix (older_bound cs h i)
    (Nat.two_pow_pos B)
    (IntegralMixedFullHistoryScript.polynomial (birthState initial cs h i) (older_bound cs h i) (chosen cs i).command)
    (IntegralMixedFullHistoryScript.degree (birthState initial cs h i) (older_bound cs h i) (chosen cs i).command)

structure Origin (initial : State P S B 0 ι) (cs : List (Instruction n B))
    (h : cs.length≤S+1) (i : Fin cs.length) where
  chain : Chain S B (birthPrefix initial cs h i) (run initial cs h).sampler.scalarPrefix
  generator_eq : chain.embed (AdjoinRoot.root _)=(run initial cs h).sampler.scalarPrefix.basis.generator i
  denominator_eq : (run initial cs h).bank.denominator i=
    IntegralMixedFullHistoryScript.leading (birthState initial cs h i) (older_bound cs h i) (chosen cs i).command

noncomputable def origin (initial : State P S B 0 ι) (cs : List (Instruction n B)) :
    ∀ (h : cs.length≤S+1) (i : Fin cs.length), Origin initial cs h i := by
  induction cs with
  | nil => intro h i; exact Fin.elim0 i
  | cons c cs ih =>
    intro h i
    have HT : cs.length≤S+1 := by simp only [List.length_cons] at h; omega
    have HS : cs.length≤S := by simp only [List.length_cons] at h; omega
    refine Fin.cases ?_ (fun j => ?_) i
    · cases c with
      | mk source hcap command => cases command <;> exact ⟨.refl _, rfl, rfl⟩
    · let o := ih HT j
      cases c with
      | mk source hcap command =>
        cases command with
        | integer p hp hd =>
          refine {
            chain := o.chain.step HS (p.map (Int.castRingHom (run initial cs HT).sampler.scalarPrefix.carrier)) p.natDegree
            generator_eq := ?_
            denominator_eq := o.denominator_eq }
          change AdjoinRoot.of _ (o.chain.embed (AdjoinRoot.root _))=
            AdjoinRoot.of _ ((run initial cs HT).sampler.scalarPrefix.basis.generator j)
          rw [o.generator_eq]
        | critical r =>
          refine {
            chain := o.chain.step HS
              (criticalPolynomial (reframe (run initial cs HT) source hcap) HS r)
              (criticalDegree (reframe (run initial cs HT) source hcap) HS r)
            generator_eq := ?_
            denominator_eq := o.denominator_eq }
          change AdjoinRoot.of _ (o.chain.embed (AdjoinRoot.root _))=
            AdjoinRoot.of _ ((run initial cs HT).sampler.scalarPrefix.basis.generator j)
          rw [o.generator_eq]
        | cut r k d ha hd =>
          refine {
            chain := o.chain.step HS
              (normalizedScalarPolynomial (reframe (run initial cs HT) source hcap)
                (IntegralMixedCutMatrix.raw (reframe (run initial cs HT) source hcap) HS r k d) d) d
            generator_eq := ?_
            denominator_eq := o.denominator_eq }
          change AdjoinRoot.of _ (o.chain.embed (AdjoinRoot.root _))=
            AdjoinRoot.of _ ((run initial cs HT).sampler.scalarPrefix.basis.generator j)
          rw [o.generator_eq]

noncomputable def Origin.toGeneratorOrigin {initial : State P S B 0 ι} {cs : List (Instruction n B)}
    {h : cs.length≤S+1} {i : Fin cs.length} (o : Origin initial cs h i) :
    IntegralScalarRootHistoryBounds.GeneratorOrigin (run initial cs h).sampler.scalarPrefix
      (run initial cs h).bank i where
  birth := (older cs i).length
  order := by have H := i.isLt; rw [older_length]; omega
  oldPrefix := (birthState initial cs h i).sampler.scalarPrefix
  birth_bound := older_bound cs h i
  polynomial := IntegralMixedFullHistoryScript.polynomial (birthState initial cs h i) (older_bound cs h i) (chosen cs i).command
  degree := IntegralMixedFullHistoryScript.degree (birthState initial cs h i) (older_bound cs h i) (chosen cs i).command
  degree_bound := IntegralMixedFullHistoryScript.degree_cap (birthState initial cs h i) (older_bound cs h i) (chosen cs i).command
  leading := IntegralMixedFullHistoryScript.leading (birthState initial cs h i) (older_bound cs h i) (chosen cs i).command
  leading_eq := IntegralMixedFullHistoryScript.leading_coefficient (birthState initial cs h i) (older_bound cs h i) (chosen cs i).command
  leading_ne_zero := IntegralMixedFullHistoryScript.leading_ne_zero (birthState initial cs h i) (older_bound cs h i) (chosen cs i).command
  chain := o.chain
  generator_eq := o.generator_eq
  denominator_eq := o.denominator_eq

theorem Origin.matrix {initial : State P S B 0 ι} {cs : List (Instruction n B)}
    {h : cs.length≤S+1} {i : Fin cs.length} (o : Origin initial cs h i)
    (r t : Fin (FixedWidthPolynomial.count cs.length B)) :
    Algebra.leftMulMatrix (run initial cs h).sampler.scalarPrefix.basis.finBasis
      ((run initial cs h).sampler.scalarPrefix.basis.generator i) r t=
      if r.val%o.chain.radix=t.val%o.chain.radix then
        Algebra.leftMulMatrix (birthPrefix initial cs h i).basis.finBasis
          (AdjoinRoot.root _) (o.chain.oldIndex r) (o.chain.oldIndex t) else 0 := by
  rw [← o.generator_eq]
  exact o.chain.matrix _ r t

theorem Origin.length_eq {initial : State P S B 0 ι} {cs : List (Instruction n B)}
    {h : cs.length≤S+1} {i : Fin cs.length} (o : Origin initial cs h i) : o.chain.length=i.val :=
  o.toGeneratorOrigin.length_eq

end LeanCanny.Algebra.IntegralMixedFramedHistoryScript
