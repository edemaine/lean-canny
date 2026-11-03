/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapLevelLedger
public import LeanCanny.Encoding.IntegralMixedRoadmapRecordBudget
/-! # Checked local levels fit one original chain budget

Only subtype bounds change. Every chronological record byte and retained
producer value stays literal. Creating-prefix validity remains the checked
level's own condition; widening its outer finite type does not replace it.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapRecordChain
open LeanCanny.Algebra LeanCanny.Geometry
open scoped Classical

def Word.weaken {a b : ℕ} (h : a≤b) (w : Word a) : Word b:=⟨w.val,w.property.trans h⟩

def Endpoint.weaken {a b c d : ℕ} (ht : a≤b) (hc : c≤d) : Endpoint a c→Endpoint b d
  | .retained label=>.retained (Fin.castLE hc label)
  | .fresh word=>.fresh (Word.weaken ht word)

theorem Endpoint.codes_weaken {a b c d : ℕ} (ht : a≤b) (hc : c≤d) (e : Endpoint a c) :
    ((e.weaken ht hc).codes.map Subtype.val)=e.codes.map Subtype.val :=by
  cases e <;> rfl

def Level.weaken {n k a b c d : ℕ} (ht : a≤b) (hc : c≤d) (L : Level n k a c) : Level n k b d where
  left:=L.left.weaken ht hc
  right:=L.right.weaken ht hc
  anchor:=Word.weaken ht L.anchor
  midpoint i:=Word.weaken ht (L.midpoint i)
  endpoint:=Word.weaken ht L.endpoint
  companions i:=Word.weaken ht (L.companions i)

theorem Level.codes_weaken {n k a b c d : ℕ} (ht : a≤b) (hc : c≤d) (L : Level n k a c) :
    ((L.weaken ht hc).codes.map Subtype.val)=L.codes.map Subtype.val :=by
  simp only [Level.codes,List.map_append,List.map_cons,List.map_nil,List.map_ofFn,
    Level.weaken,Endpoint.codes_weaken]
  rfl

theorem codeBudget_mono_width (n birth B C : ℕ) (h : B≤C) :
    IntegralMixedCutRecordConstructor.codeBudget n birth B≤IntegralMixedCutRecordConstructor.codeBudget n birth C :=by
  unfold IntegralMixedCutRecordConstructor.codeBudget IntegralMixedCutRecordConstructor.fieldBudget
  omega

theorem local_budget_le {n B sourceCap birth initial C : ℕ} {q : List Bool}
    (_h : IntegralMixedRoadmapLevel.Checked n B sourceCap birth q)
    (hm : IntegralMixedRoadmapLevel.endBirth n birth q≤maxBirth n initial) (hB : B≤C) :
    IntegralMixedRoadmapLevel.budget n B birth q≤codeBound n initial C :=
  (IntegralMixedOptionalEndpoints.codeBudget_mono n B _ _ hm).trans
    (codeBudget_mono_width n (maxBirth n initial) B C hB)

noncomputable def originalLevel {n B sourceCap birth initial C : ℕ} {q : List Bool}
    (h : IntegralMixedRoadmapLevel.Checked n B sourceCap birth q)
    (hm : IntegralMixedRoadmapLevel.endBirth n birth q≤maxBirth n initial) (hB : B≤C) :
    Level n (IntegralMixedRoadmapLevel.k q) (codeBound n initial C) (maxBirth n initial) :=
  (IntegralMixedRoadmapLevel.ledger h).weaken (local_budget_le h hm hB) hm

theorem originalLevel_codes {n B sourceCap birth initial C : ℕ} {q : List Bool}
    (h : IntegralMixedRoadmapLevel.Checked n B sourceCap birth q)
    (hm : IntegralMixedRoadmapLevel.endBirth n birth q≤maxBirth n initial) (hB : B≤C) :
    (originalLevel h hm hB).codes.map Subtype.val=IntegralMixedRoadmapLevel.codes n q :=by
  rw [originalLevel,Level.codes_weaken,IntegralMixedRoadmapLevel.ledger_codes]

theorem originalLevel_word {n B sourceCap birth initial C : ℕ} {q : List Bool}
    (h : IntegralMixedRoadmapLevel.Checked n B sourceCap birth q)
    (hm : IntegralMixedRoadmapLevel.endBirth n birth q≤maxBirth n initial) (hB : B≤C) :
    WordList.encode ((originalLevel h hm hB).codes.map Subtype.val)=IntegralMixedRoadmapLevel.slice q :=by
  rw [originalLevel_codes]
  exact h.2.symm

end LeanCanny.Encoding.IntegralMixedRoadmapRecordChain
