/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedSweepRetarget
public import LeanCanny.Algebra.IntegralMixedCausalRecord
/-! # The selected cut realizes the record's shared coordinate field

The actual decoder stores the chosen Kind coordinate in critical.coordinate
as well. This retargets that field, transfers the selected-component guards
and actual factor root, then constructs the exact retargeted scalar command.
No equality of the syntactically different sweep rules is asserted.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedSweepRetarget
open IntegralMixedHistory IntegralMixedCriticalSweep IntegralMixedRelativeCuts
open UniformIntegralPowerSchedule IntegralHistorySampler
open scoped Classical
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type}

def coordinateIndex (r : Rule n) : Kind P r→ℕ
  | .coordinate j _=>j.val
  | .squarefree j _=>j.val
  | .value j _=>j.val
  | .limitCoordinate j _=>j.val

def choiceIndex (r : Rule n) : Kind P r→ℕ
  | .coordinate _ c=>c.val
  | .squarefree _ c=>c.val
  | .value _ c=>c.val
  | .limitCoordinate _ c=>c.val

def tag (r : Rule n) : Kind P r→IntegralMixedCausalRecordBits.Tag
  | .coordinate _ _=>.coordinate
  | .squarefree _ _=>.squarefree
  | .value _ _=>.value
  | .limitCoordinate _ _=>.limitCoordinate

theorem coordinateIndex_eq (r : Rule n) (k : ℕ) (c : Kind P r) :
    coordinateIndex (rule r k) (kind r k c)=coordinateIndex r c:=by cases c <;> rfl

theorem choiceIndex_eq (r : Rule n) (k : ℕ) (c : Kind P r) :
    choiceIndex (rule r k) (kind r k c)=choiceIndex r c:=by cases c <;> rfl

theorem tag_eq (r : Rule n) (k : ℕ) (c : Kind P r) :
    tag (rule r k) (kind r k c)=tag r c:=by cases c <;> rfl

variable [Fintype ι]

theorem real_extend_shared_coordinate (x : State P S B m ι) (hm : m≤S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (c : Kind P r) (hc : Valid x hm r φ c)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B)
    (z : ι→ℝ) (hz : ∀i,(x.sampler.rows i).eval₂ (Int.castRingHom ℝ) z=0)
    (hφ : ∀i,φ (x.sampler.scalarPrefix.basis.generator i)=z (x.sampler.scalar i)^weights S (2^B) m i)
    (values : Fin m→ℝ) (H : ∀i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (a : ℝ) (ha : (factor x hm r c).eval₂ φ.toRingHom a=0) :
    let j:=coordinateIndex r c
    let decodedRule:=rule r j
    let decodedKind:=kind r j c
    let d:=selectedDegree x hm decodedRule φ decodedKind
    let hd:=selectedDegree_bound x hm decodedRule φ decodedKind
    let command : IntegralMixedFullHistoryScript.Command P B:=.cut decodedRule decodedKind d hd (hd.trans hcap)
    let born:=IntegralMixedFullHistoryScript.step x hm command
    d=selectedDegree x hm r φ c ∧
    ∃y : (ι⊕Unit)→ℝ,∃ψ : born.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
      (∀i,(born.sampler.rows i).eval₂ (Int.castRingHom ℝ) y=0) ∧
      (∀i,y (Sum.inl i)=z i) ∧ ψ.comp (AdjoinRoot.ofAlgHom ℤ _)=φ ∧
      (∀i,ψ (born.sampler.scalarPrefix.basis.generator i)=y (born.sampler.scalar i)^weights S (2^B) (m+1) i) ∧
      ∀i,ψ (born.bank.numerator i)/(born.bank.denominator i:ℝ)=(Fin.cons a values : Fin (m+1)→ℝ) i:=by
  refine ⟨selectedDegree_eq x hm r (coordinateIndex r c) φ c,?_⟩
  apply real_extend_selectedDegree x hm (rule r (coordinateIndex r c)) φ (kind r (coordinateIndex r c) c)
    ((valid_iff x hm r _ φ c).mpr hc) hcap z hz hφ values H a
  rw [factor_eq]
  exact ha

end LeanCanny.Algebra.IntegralMixedSweepRetarget
