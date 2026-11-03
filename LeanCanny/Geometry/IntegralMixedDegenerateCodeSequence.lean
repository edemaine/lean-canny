/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedDegenerateEndpointCaptures
public import LeanCanny.Geometry.IntegralMixedPointCompanionBounds
/-! # Explicit newest-first code sequence and local degenerate-level budget

Each component list is the literal code list of the corresponding actual
program. The chronological byte word is its reverse. Local decoder receipts
are carried by MidpointCaptures / ChildCaptures and the optional PairResult.
-/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedOptionalEndpoints
open LeanCanny.Algebra LeanCanny.Encoding IntegralMixedHistory
open LeanCanny.Geometry.IntegralMixedFrozenFrame
open IntegralMixedFullHistoryScript IntegralMixedCausalRowConstructor
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
variable {x : State P S B m ι} {F : Frame n} {z : ι→ℝ}
    {φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ} {values : Fin m→ℝ}
    {c : ℝ} {hn : 0<n}
    {hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B}

noncomputable def PairResult.midpointCaptureCodes (R : PairResult x F z φ values c c hn hcap)
    (h g : Fin (n+1)) (hg : g∉(line F h).frozen)
    (js : List (IntegralMixedPointCompanion.Free (insert h R.frame.frozen))):=
  IntegralMixedPointCompanion.codes (insert h R.frame.frozen) (midpointDouble h)
    (IntegralMixedPointCompanion.shiftRows (referencedMidpointRows R.atomic h R.left R.right) 1)
    ⟨g,R.free_after_pair h g hg⟩ js

noncomputable def PairResult.childCaptureCodes (R : PairResult x F z φ values c c hn hcap)
    (h g : Fin (n+1)) (hg : g∉(line F h).frozen)
    (js : List (IntegralMixedPointCompanion.Free (insert h R.frame.frozen))) (right : Bool):=
  IntegralMixedPointCompanion.codes (insert h R.frame.frozen) (fun _=>false)
    (IntegralMixedPointCompanion.shiftRows
      (referencedEndpointRows (R.capturedFrame_atomic js.length) h (R.endpointIndex js.length right)) 1)
    ⟨g,R.free_after_pair h g hg⟩ js

noncomputable def PairResult.degenerateCodes (R : PairResult x F z φ values c c hn hcap)
    (h g j : Fin (n+1)) (hg : g∉(line F h).frozen) (hj : j∉(line F h).frozen)
    (js : List (IntegralMixedPointCompanion.Free (insert h R.frame.frozen))) (right : Bool):=
  R.childCaptureCodes h g hg js right ++[(R.endpointData h g hg js.length right).code] ++
    R.midpointCaptureCodes h g hg js ++
    [(referencedMidpointData R.atomic h R.left R.right g j
      (R.free_after_pair h g hg) (R.free_after_pair h j hj)).code] ++R.codes

noncomputable def PairResult.degenerateCommands (R : PairResult x F z φ values c c hn hcap)
    (h g j : Fin (n+1)) (hg : g∉(line F h).frozen) (hj : j∉(line F h).frozen)
    (js : List (IntegralMixedPointCompanion.Free (insert h R.frame.frozen))) (right : Bool) :
    List (Command P B):=
  IntegralMixedPointCompanion.commands (insert h R.frame.frozen) (fun _=>false)
    (IntegralMixedPointCompanion.shiftRows
      (referencedEndpointRows (R.capturedFrame_atomic js.length) h (R.endpointIndex js.length right)) 1)
    ⟨g,R.free_after_pair h g hg⟩ js ++[.critical (R.endpointData h g hg js.length right).rule] ++
    IntegralMixedPointCompanion.commands (insert h R.frame.frozen) (midpointDouble h)
      (IntegralMixedPointCompanion.shiftRows (referencedMidpointRows R.atomic h R.left R.right) 1)
      ⟨g,R.free_after_pair h g hg⟩ js ++
    [.critical (referencedMidpointData R.atomic h R.left R.right g j
      (R.free_after_pair h g hg) (R.free_after_pair h j hj)).rule] ++R.commands

theorem PairResult.degenerateCodes_length (R : PairResult x F z φ values c c hn hcap)
    (h g j : Fin (n+1)) (hg : g∉(line F h).frozen) (hj : j∉(line F h).frozen)
    (js : List (IntegralMixedPointCompanion.Free (insert h R.frame.frozen))) (right : Bool) :
    (R.degenerateCodes h g j hg hj js right).length=R.commands.length+2+2*js.length:=by
  simp only [PairResult.degenerateCodes,List.length_append,List.length_singleton,
    PairResult.childCaptureCodes,PairResult.midpointCaptureCodes,IntegralMixedPointCompanion.codes_length,R.code_count]
  omega

theorem PairResult.degenerateCommands_length (R : PairResult x F z φ values c c hn hcap)
    (h g j : Fin (n+1)) (hg : g∉(line F h).frozen) (hj : j∉(line F h).frozen)
    (js : List (IntegralMixedPointCompanion.Free (insert h R.frame.frozen))) (right : Bool) :
    (R.degenerateCommands h g j hg hj js right).length=R.commands.length+2+2*js.length:=by
  simp only [PairResult.degenerateCommands,List.length_append,List.length_singleton,
    IntegralMixedPointCompanion.commands_length]
  omega

theorem PairResult.degenerateCodes_command_count (R : PairResult x F z φ values c c hn hcap)
    (h g j : Fin (n+1)) (hg : g∉(line F h).frozen) (hj : j∉(line F h).frozen)
    (js : List (IntegralMixedPointCompanion.Free (insert h R.frame.frozen))) (right : Bool) :
    (R.degenerateCodes h g j hg hj js right).length=(R.degenerateCommands h g j hg hj js right).length:=by
  rw [R.degenerateCodes_length,R.degenerateCommands_length]

theorem PairResult.degenerateCodes_fresh_count (R : PairResult x F z φ values c c hn hcap)
    (h g j : Fin (n+1)) (hg : g∉(line F h).frozen) (hj : j∉(line F h).frozen)
    (js : List (IntegralMixedPointCompanion.Free (insert h R.frame.frozen)))
    (freshLeft freshRight : ℕ) (hc : R.commands.length=freshLeft+freshRight) (right : Bool) :
    (R.degenerateCodes h g j hg hj js right).length=freshLeft+freshRight+2+2*js.length:=by
  rw [R.degenerateCodes_length,hc]

theorem PairResult.degenerateCodes_count_le (R : PairResult x F z φ values c c hn hcap)
    (h g j : Fin (n+1)) (hg : g∉(line F h).frozen) (hj : j∉(line F h).frozen)
    (js : List (IntegralMixedPointCompanion.Free (insert h R.frame.frozen))) (right : Bool) :
    (R.degenerateCodes h g j hg hj js right).length≤4+2*js.length:=by
  rw [R.degenerateCodes_length]
  have HR:=R.count
  omega

theorem PairResult.degenerateCodes_level_budget (R : PairResult x F z φ values c c hn hcap)
    (h g j : Fin (n+1)) (hg : g∉(line F h).frozen) (hj : j∉(line F h).frozen)
    (js : List (IntegralMixedPointCompanion.Free (insert h R.frame.frozen)))
    (hq : js.length=n+1-(F.frozen.card+1)) (right : Bool) :
    (R.degenerateCodes h g j hg hj js right).length≤4+2*(n+1-(F.frozen.card+1)):=by
  simpa only [hq] using R.degenerateCodes_count_le h g j hg hj js right

theorem allFree_length_eq (frozen : Finset (Fin (n+1))) :
    (IntegralMixedPointCompanion.allFree frozen).length=n+1-frozen.card:=by
  simp only [IntegralMixedPointCompanion.allFree,Finset.length_toList,Finset.card_univ]
  change Fintype.card {i : Fin (n+1) // ¬i∈frozen}=n+1-frozen.card
  rw [Fintype.card_subtype_compl,Fintype.card_fin,Fintype.card_coe]

theorem PairResult.degenerateCodes_allFree_level_budget (R : PairResult x F z φ values c c hn hcap)
    (h g j : Fin (n+1)) (hh : h∉F.frozen)
    (hg : g∉(line F h).frozen) (hj : j∉(line F h).frozen) (right : Bool) :
    (R.degenerateCodes h g j hg hj
      (IntegralMixedPointCompanion.allFree (insert h R.frame.frozen)) right).length≤
      4+2*(n+1-(F.frozen.card+1)):=by
  apply R.degenerateCodes_level_budget h g j hg hj _ _ right
  rw [allFree_length_eq,R.frozen,Finset.card_insert_of_notMem hh]

def PairResult.degenerateBudget (R : PairResult x F z φ values c c hn hcap) (q : ℕ):=
  IntegralMixedCutRecordConstructor.codeBudget n (m+R.commands.length+2+2*q) B

theorem PairResult.degenerateCodes_size (R : PairResult x F z φ values c c hn hcap)
    (h g j : Fin (n+1)) (hg : g∉(line F h).frozen) (hj : j∉(line F h).frozen)
    (js : List (IntegralMixedPointCompanion.Free (insert h R.frame.frozen))) (right : Bool) :
    ∀code∈R.degenerateCodes h g j hg hj js right,code.length≤R.degenerateBudget js.length:=by
  have Hchild : ∀code∈R.childCaptureCodes h g hg js right,code.length≤R.degenerateBudget js.length:=by
    intro code hc
    exact (IntegralMixedPointCompanion.code_size _ _ _ _ js code hc).trans
      (codeBudget_mono n B _ _ (by omega))
  have Hend : (R.endpointData h g hg js.length right).code.length≤R.degenerateBudget js.length:=
    (R.endpointData h g hg js.length right).code_length.trans
      ((IntegralMixedCutRecordConstructor.critical_codeBudget_le n _ B).trans
        (codeBudget_mono n B _ _ (by omega)))
  have Hmid : ∀code∈R.midpointCaptureCodes h g hg js,code.length≤R.degenerateBudget js.length:=by
    intro code hc
    exact (IntegralMixedPointCompanion.code_size _ _ _ _ js code hc).trans
      (codeBudget_mono n B _ _ (by omega))
  have Hanchor : (referencedMidpointData R.atomic h R.left R.right g j
      (R.free_after_pair h g hg) (R.free_after_pair h j hj)).code.length≤R.degenerateBudget js.length:=
    (referencedMidpointData R.atomic h R.left R.right g j
      (R.free_after_pair h g hg) (R.free_after_pair h j hj)).code_length.trans
      ((IntegralMixedCutRecordConstructor.critical_codeBudget_le n _ B).trans
        (codeBudget_mono n B _ _ (by omega)))
  have Hold : ∀code∈R.codes,code.length≤R.degenerateBudget js.length:=by
    intro code hc
    exact (R.code_size code hc).trans (codeBudget_mono n B _ _ (by omega))
  intro code hc
  simp only [PairResult.degenerateCodes,List.mem_append,List.mem_singleton] at hc
  aesop

theorem PairResult.degenerate_word_size (R : PairResult x F z φ values c c hn hcap)
    (h g j : Fin (n+1)) (hg : g∉(line F h).frozen) (hj : j∉(line F h).frozen)
    (js : List (IntegralMixedPointCompanion.Free (insert h R.frame.frozen))) (right : Bool) :
    (WordList.encode (R.degenerateCodes h g j hg hj js right).reverse).length≤
      (2*R.degenerateBudget js.length+2)*(R.commands.length+2+2*js.length):=by
  have H:=WordList.length_le (R.degenerateCodes h g j hg hj js right).reverse
    (R.degenerateBudget js.length) (fun code hc=>R.degenerateCodes_size h g j hg hj js right code
      (List.mem_reverse.mp hc))
  simpa only [List.length_reverse,R.degenerateCodes_length] using H

end LeanCanny.Geometry.IntegralMixedOptionalEndpoints
