/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedHistoryScript
public import LeanCanny.Algebra.IntegralScalarGeneratorOrigin

/-! # Actual creating commands in mixed scalar histories

A retained scalar selects a tagged command and its actual older state.
The resulting prefix chain embeds that command's companion generator into
the final prefix, preserves its original integer leading denominator, and
fixes the exact number of intervening scalar births.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedHistoryScript
open LeanCanny.Encoding LeanCanny.Computation UniformIntegralPrefix IntegralMixedHistory
open scoped Classical
variable {n S B : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]

def older (cs : List (Command n B)) (i : Fin cs.length) := cs.drop (i.val + 1)
def chosen (cs : List (Command n B)) (i : Fin cs.length) := cs[i.val]

theorem older_length (cs : List (Command n B)) (i : Fin cs.length) :
    (older cs i).length = cs.length - 1 - i.val := by
  simp only [older, List.length_drop]
  omega

theorem older_bound (cs : List (Command n B)) (h : cs.length ≤ S + 1) (i : Fin cs.length) :
    (older cs i).length ≤ S := by
  have H := i.isLt
  rw [older_length]
  omega

noncomputable def birthState (initial : State P S B 0 ι) (cs : List (Command n B))
    (h : cs.length ≤ S + 1) (i : Fin cs.length) :=
  run initial (older cs i) ((older_bound cs h i).trans (Nat.le_add_right S 1))

noncomputable def birthPrefix (initial : State P S B 0 ι) (cs : List (Command n B))
    (h : cs.length ≤ S + 1) (i : Fin cs.length) :=
  UniformIntegralPrefix.step (birthState initial cs h i).sampler.scalarPrefix (older_bound cs h i)
    (Nat.two_pow_pos B) (polynomial (birthState initial cs h i) (older_bound cs h i) (chosen cs i))
    (degree (birthState initial cs h i) (older_bound cs h i) (chosen cs i))

structure Origin (initial : State P S B 0 ι) (cs : List (Command n B))
    (h : cs.length ≤ S + 1) (i : Fin cs.length) where
  chain : Chain S B (birthPrefix initial cs h i) (run initial cs h).sampler.scalarPrefix
  generator_eq : chain.embed (AdjoinRoot.root _) = (run initial cs h).sampler.scalarPrefix.basis.generator i
  denominator_eq : (run initial cs h).bank.denominator i =
    leading (birthState initial cs h i) (older_bound cs h i) (chosen cs i)

noncomputable def origin (initial : State P S B 0 ι) (cs : List (Command n B)) :
    ∀ (h : cs.length ≤ S + 1) (i : Fin cs.length), Origin initial cs h i := by
  induction cs with
  | nil => intro h i; exact Fin.elim0 i
  | cons c cs ih =>
    intro h i
    have HT : cs.length ≤ S + 1 := by simp only [List.length_cons] at h; omega
    have HS : cs.length ≤ S := by simp only [List.length_cons] at h; omega
    refine Fin.cases ?_ (fun j => ?_) i
    · cases c <;> exact ⟨.refl _, rfl, rfl⟩
    · let o := ih HT j
      cases c with
      | integer p hp hcap =>
        refine {
          chain := o.chain.step HS (p.map (Int.castRingHom (run initial cs HT).sampler.scalarPrefix.carrier)) p.natDegree
          generator_eq := ?_
          denominator_eq := o.denominator_eq }
        change AdjoinRoot.of _ (o.chain.embed (AdjoinRoot.root _)) =
          AdjoinRoot.of _ ((run initial cs HT).sampler.scalarPrefix.basis.generator j)
        rw [o.generator_eq]
      | critical r =>
        refine {
          chain := o.chain.step HS (criticalPolynomial (run initial cs HT) HS r) (criticalDegree (run initial cs HT) HS r)
          generator_eq := ?_
          denominator_eq := o.denominator_eq }
        change AdjoinRoot.of _ (o.chain.embed (AdjoinRoot.root _)) =
          AdjoinRoot.of _ ((run initial cs HT).sampler.scalarPrefix.basis.generator j)
        rw [o.generator_eq]

noncomputable def Origin.toGeneratorOrigin {initial : State P S B 0 ι} {cs : List (Command n B)}
    {h : cs.length ≤ S + 1} {i : Fin cs.length} (o : Origin initial cs h i) :
    IntegralScalarRootHistoryBounds.GeneratorOrigin (run initial cs h).sampler.scalarPrefix
      (run initial cs h).bank i where
  birth := (older cs i).length
  order := by have H := i.isLt; rw [older_length]; omega
  oldPrefix := (birthState initial cs h i).sampler.scalarPrefix
  birth_bound := older_bound cs h i
  polynomial := polynomial (birthState initial cs h i) (older_bound cs h i) (chosen cs i)
  degree := degree (birthState initial cs h i) (older_bound cs h i) (chosen cs i)
  degree_bound := degree_cap (birthState initial cs h i) (older_bound cs h i) (chosen cs i)
  leading := leading (birthState initial cs h i) (older_bound cs h i) (chosen cs i)
  leading_eq := leading_coefficient (birthState initial cs h i) (older_bound cs h i) (chosen cs i)
  leading_ne_zero := leading_ne_zero (birthState initial cs h i) (older_bound cs h i) (chosen cs i)
  chain := o.chain
  generator_eq := o.generator_eq
  denominator_eq := o.denominator_eq

theorem Origin.matrix {initial : State P S B 0 ι} {cs : List (Command n B)}
    {h : cs.length ≤ S + 1} {i : Fin cs.length} (o : Origin initial cs h i)
    (r t : Fin (FixedWidthPolynomial.count cs.length B)) :
    Algebra.leftMulMatrix (run initial cs h).sampler.scalarPrefix.basis.finBasis
      ((run initial cs h).sampler.scalarPrefix.basis.generator i) r t =
      if r.val % o.chain.radix = t.val % o.chain.radix then
        Algebra.leftMulMatrix (birthPrefix initial cs h i).basis.finBasis
          (AdjoinRoot.root _) (o.chain.oldIndex r) (o.chain.oldIndex t) else 0 := by
  rw [← o.generator_eq]
  exact o.chain.matrix _ r t

theorem Origin.length_eq {initial : State P S B 0 ι} {cs : List (Command n B)}
    {h : cs.length ≤ S + 1} {i : Fin cs.length} (o : Origin initial cs h i) : o.chain.length = i.val :=
  o.toGeneratorOrigin.length_eq

end LeanCanny.Algebra.IntegralMixedHistoryScript
