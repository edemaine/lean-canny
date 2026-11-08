/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Computation.ControllerRequests
public import LeanCanny.Computation.PolyTimeBinaryNat
/-! # Native output postprocessing preserves a recursive controller's requests -/
@[expose] public section
namespace LeanCanny.Computation.RecursiveController.Controller
open Turing.MultiTapeTM
variable {Q S : Type}

def postprocess (C : Controller Q S) (f : List Bool → List Bool) : Controller Q S :=
  { C with output := f ∘ C.output }

theorem postprocess_reference (C : Controller Q S) (f : List Bool → List Bool) (answer : Q → List Bool) :
    (C.postprocess f).reference answer = C.reference answer := rfl

theorem postprocess_requests (C : Controller Q S) (f : List Bool → List Bool)
    (answer : Q → List Bool) (budget : Q → ℕ) (q c : Q) :
    (C.postprocess f).Requests answer budget q c ↔ C.Requests answer budget q c := Iff.rfl

theorem postprocess_certificates (C : Controller Q S) {encQ : Q ↪ List Bool} {encS : S ↪ List Bool}
    (hC : C.Certificates (encQ := encQ) (encS := encS)) (f : List Bool → List Bool) (hf : f ∈ FP) :
    (C.postprocess f).Certificates (encQ := encQ) (encS := encS) where
  initial := hC.initial
  halted := hC.halted
  output := (ComputableInPolySpace.of_tidyPolyTime (FP.computable hf)).comp hC.output
  needs := hC.needs
  query := hC.query
  advance := hC.advance
  resume := hC.resume

end LeanCanny.Computation.RecursiveController.Controller
