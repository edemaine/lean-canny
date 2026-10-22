/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.RecursiveStackBounds

/-! # Native space certificates for one recursive stack transition -/

@[expose] public section

namespace LeanCanny.Computation.RecursiveStack
open Turing.MultiTapeTM

private def install {F : Type} (p : (State F × Action F) × F) : State F :=
  let s := p.1.1
  let a := p.1.2
  if s.1 then s else
  if a.1 then
    if s.2.2.2.isEmpty then (true, a.2.2.1, s.2.2.1, [])
    else (false, [], p.2, s.2.2.2.tail)
  else if a.2.1 then (false, [], a.2.2.2, s.2.2.1 :: s.2.2.2)
  else (false, [], a.2.2.2, s.2.2.2)

private theorem install_computable {F : Type} (encF : F ↪ List Bool) :
    ComputableTidilyInPolyTime (install (F := F))
      (encPair (encPair (encState encF) (encAction encF)) encF) (encState encF) := by
  unfold install
  fun_prop

theorem step_computable {F : Type} [Inhabited F] (encF : F ↪ List Bool)
    {localStep : F → Action F} {receive : F × List Bool → F}
    (hl : ComputableTidilyInPolySpace localStep encF (encAction encF))
    (hr : ComputableTidilyInPolySpace receive (encPair encF encBits) encF) :
    ComputableTidilyInPolySpace (step localStep receive) (encState encF) (encState encF) := by
  have hcurrent : ComputableTidilyInPolyTime (fun s : State F => s.2.2.1) (encState encF) encF := by
    fun_prop
  have hp : ComputableTidilyInPolySpace (fun s : State F => (s, localStep s.2.2.1))
      (encState encF) (encPair (encState encF) (encAction encF)) :=
    ComputableTidilyInPolySpace.id'.prod (hl.comp (.of_polyTime hcurrent))
  have hquery : ComputableTidilyInPolyTime
      (fun p : State F × Action F => (p.1.2.2.2.headD default, p.2.2.2.1))
      (encPair (encState encF) (encAction encF)) (encPair encF encBits) := by
    fun_prop
  have hreply := hr.comp (ComputableTidilyInPolySpace.of_polyTime hquery)
  have h := (ComputableTidilyInPolySpace.of_polyTime (install_computable encF)).comp
    ((ComputableTidilyInPolySpace.id'.prod hreply).comp hp)
  refine h.congr fun s => ?_
  rcases s with ⟨halted, output, current, stack⟩
  cases halted <;> cases hd : (localStep current).1 <;> cases hc : (localStep current).2.1 <;>
    cases stack <;> simp only [install, step, hd, hc, Bool.false_eq_true,
      ite_true, ite_false, List.isEmpty_nil, List.isEmpty_cons, List.headD_cons, List.tail_cons]

theorem initial_computable {α F : Type} {encIn : α ↪ List Bool} {encF : F ↪ List Bool}
    {start : α → F} (hs : ComputableTidilyInPolySpace start encIn encF) :
    ComputableTidilyInPolySpace (fun x => initial (start x)) encIn (encState encF) :=
  (ComputableTidilyInPolySpace.of_polyTime (ComputableTidilyInPolyTime.const false)).prod
    ((ComputableTidilyInPolySpace.of_polyTime (ComputableTidilyInPolyTime.const [])).prod
      (hs.prod (ComputableTidilyInPolySpace.of_polyTime (ComputableTidilyInPolyTime.const []))))

end LeanCanny.Computation.RecursiveStack
