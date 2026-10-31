/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MatrixPowerRecursiveController
public import LeanCanny.Computation.ControllerRequests
public import LeanCanny.Computation.PolyTimeBinaryNat

/-! # Uniform resumable modular matrix-power stages

Native metadata constructs the controller, its binary stopping allowance,
and its unary state bound. Replies need only satisfy the matrix-entry
semantics. No entry evaluator is used by the native certificate.
-/

@[expose] public section
namespace LeanCanny.Algebra.MatrixPower.ModularRecursiveStage
open LeanCanny.Encoding LeanCanny.Computation Controller
open Turing.MultiTapeTM
set_option backward.isDefEq.respectTransparency false
variable {F : ModularFamily}

def initial (a : ModularAccess F) : List Bool → List Bool := initialPacket a.exponent a.row a.col

def ops (a : ModularAccess F) : Callbacks := modularCallbacks a.dimension a.modulus (fun _ => [])

def stage (a : ModularAccess F) (task : List Bool → List Bool) :
    RecursiveController.Controller (List Bool) (List Bool) := RecursiveStage.controller (ops a) (initial a) task

theorem initial_FP (a : ModularAccess F) (ha : a.ControlsPolyTime) : initial a ∈ FP :=
  initialPacket_mem_FP ha.exponent ha.row ha.col

theorem certificates (a : ModularAccess F) (ha : a.ControlsPolyTime) (task : List Bool → List Bool) (ht : task ∈ FP) :
    (stage a task).Certificates (encQ := encBits) (encS := encBits) := by
  have H := modularCallbacks_polyTime ha.dimension ha.modulus (constFn_mem_FP [])
  exact RecursiveStage.certificates (ops a) ⟨H.dimension, H.zero, H.one, H.combine⟩
    (initial a) task (SpaceFunction.ofFP _ (initial_FP a ha)) ht

theorem initial_eq (a : ModularAccess F) (c : List Bool) :
    initial a c = pair c (stateBits (residueBits (m := F.modulus c))
      (.eval ⟨(F.exponent c).size, F.exponent c, F.row c, F.col c⟩ [])) :=
  initialPacket_encode a.exponent a.row a.col c _ _ _ _ (a.exponent_eq c) (a.row_eq c) (a.col_eq c)

theorem correctAt (a : ModularAccess F) (task answer : List Bool → List Bool)
    (he : ∀ c (i j : Fin (F.dimension c)), answer (task (pair c
      (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))) = residueBits (F.matrix c i j))
    (c : List Bool) : CorrectAt (RecursiveStage.oracleCallbacks (ops a) task answer) c (F.matrix c) residueBits := by
  let : NeZero (F.modulus c) := ⟨F.modulus_ne_zero c⟩
  exact modularCallbacks_correctAt a.dimension a.modulus (answer ∘ task) c (F.modulus c)
    (F.matrix c) (a.dimension_eq c) (a.modulus_eq c) (he c)

def clockWidth (F : ModularFamily) (c : List Bool) : ℕ := ((F.dimension c).size + 2) * (F.exponent c).size + 1
def clock (F : ModularFamily) (c : List Bool) : ℕ := 2 ^ clockWidth F c

def stateBound (F : ModularFamily) (c : List Bool) : ℕ :=
  2 * c.length + 2 + 64 * ((F.dimension c).size + (F.exponent c).size + (F.modulus c).size + 1) ^ 2

theorem size_unary {f : List Bool → ℕ} (word : List Bool → List Bool) (hw : word ∈ FP)
    (he : ∀ c, word c = BinaryNatCode.encode (f c)) : UnaryFn (fun c => (f c).size) :=
  (UnaryFn.length hw).of_eq (fun c => by rw [he c, BinaryNatCode.length_encode])

theorem clockWidth_unary (a : ModularAccess F) (ha : a.ControlsPolyTime) : UnaryFn (clockWidth F) :=
  (((size_unary a.dimension ha.dimension a.dimension_eq).add (UnaryFn.const 2)).mul
    (size_unary a.exponent ha.exponent a.exponent_eq)).add (UnaryFn.const 1)

theorem clock_binary (a : ModularAccess F) (ha : a.ControlsPolyTime) : BinaryFn (clock F) :=
  (BinaryFn.const 2).powUnary (clockWidth_unary a ha)

theorem stateBound_unary (a : ModularAccess F) (ha : a.ControlsPolyTime) : UnaryFn (stateBound F) := by
  have H := (((size_unary a.dimension ha.dimension a.dimension_eq).add
    (size_unary a.exponent ha.exponent a.exponent_eq)).add
    (size_unary a.modulus ha.modulus a.modulus_eq)).add (UnaryFn.const 1)
  exact ((((UnaryFn.const 2).mul (UnaryFn.length id_mem_FP)).add (UnaryFn.const 2)).add
    ((UnaryFn.const 64).mul (H.mul H))).of_eq (fun c => by simp only [stateBound, pow_two, id_eq])

theorem work_le_clock (c : List Bool) : work (F.dimension c) (F.exponent c).size (F.exponent c) + 1 ≤ clock F c :=
  work_add_one_le_two_pow _ _ _

theorem halted_after (a : ModularAccess F) (task answer : List Bool → List Bool)
    (he : ∀ c (i j : Fin (F.dimension c)), answer (task (pair c
      (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))) = residueBits (F.matrix c i j))
    (c : List Bool) : (stage a task).halted
      (((stage a task).reference answer)^[clock F c] ((stage a task).initial c)) = true := by
  have HS := RecursiveStage.halted_after (ops a) (initial a) task answer c (F.matrix c) residueBits
    (correctAt a task answer he c) (F.exponent c) (F.row c) (F.col c) (initial_eq a c)
  let n := work (F.dimension c) (F.exponent c).size (F.exponent c) + 1
  have HL : n ≤ clock F c := work_le_clock c
  change (stage a task).halted (((stage a task).reference answer)^[n] (initial a c)) = true at HS
  have HF : (stage a task).reference answer (((stage a task).reference answer)^[n] (initial a c)) =
      ((stage a task).reference answer)^[n] (initial a c) := by
    simp only [RecursiveController.Controller.reference, HS, ite_true]
  change (stage a task).halted (((stage a task).reference answer)^[clock F c] (initial a c)) = true
  rw [← Nat.sub_add_cancel HL, Function.iterate_add_apply, Function.iterate_fixed HF]
  exact HS

theorem output_when_halted (a : ModularAccess F) (task answer : List Bool → List Bool)
    (he : ∀ c (i j : Fin (F.dimension c)), answer (task (pair c
      (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))) = residueBits (F.matrix c i j))
    (c : List Bool) (t : ℕ)
    (hh : (stage a task).halted (((stage a task).reference answer)^[t] ((stage a task).initial c)) = true) :
    (stage a task).output (((stage a task).reference answer)^[t] ((stage a task).initial c)) = F.value c :=
  RecursiveStage.output_when_halted (ops a) (initial a) task answer c (F.matrix c) residueBits
    (correctAt a task answer he c) (F.exponent c) t (F.row c) (F.col c) (initial_eq a c) hh

theorem state_length (a : ModularAccess F) (task answer : List Bool → List Bool)
    (he : ∀ c (i j : Fin (F.dimension c)), answer (task (pair c
      (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))) = residueBits (F.matrix c i j))
    (c : List Bool) (t : ℕ) :
    (((stage a task).reference answer)^[t] ((stage a task).initial c)).length ≤ stateBound F c := by
  let : NeZero (F.modulus c) := ⟨F.modulus_ne_zero c⟩
  exact RecursiveStage.modular_state_length a.dimension a.modulus (initial a) task answer c
    (F.modulus c) (F.matrix c) (correctAt a task answer he c) (F.exponent c) t (F.row c) (F.col c) (initial_eq a c)

theorem requests_in_bounds (a : ModularAccess F) (task answer : List Bool → List Bool)
    (he : ∀ c (i j : Fin (F.dimension c)), answer (task (pair c
      (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))) = residueBits (F.matrix c i j))
    (budget : List Bool → ℕ) (c child : List Bool)
    (hreq : (stage a task).Requests answer budget c child) :
    ∃ i j : Fin (F.dimension c), child = task (pair c
      (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) := by
  obtain ⟨t, _ht, _hh, hn, hchild⟩ := hreq
  let s : State (ZMod (F.modulus c)) (F.dimension c) :=
    (MatrixPower.step (F.matrix c))^[t]
      (.eval ⟨(F.exponent c).size, F.exponent c, F.row c, F.col c⟩ [])
  have HO : ((stage a task).reference answer)^[t] ((stage a task).initial c) = pair c (stateBits residueBits s) := by
    change ((RecursiveStage.controller (ops a) (initial a) task).reference answer)^[t] (initial a c) = _
    rw [initial_eq]
    exact RecursiveStage.reference_iterate (ops a) (initial a) task answer c (F.matrix c) residueBits
      (correctAt a task answer he c) t _
  change needsEntry (((stage a task).reference answer)^[t] ((stage a task).initial c)) = true at hn
  change child = task (entryInput (((stage a task).reference answer)^[t] ((stage a task).initial c))) at hchild
  rw [HO] at hn hchild
  obtain ⟨i, j, hq⟩ := RecursiveStage.entry_query_indices c residueBits s hn
  exact ⟨i, j, hchild.trans (congrArg task hq)⟩

theorem context_iterate (a : ModularAccess F) (task answer : List Bool → List Bool)
    (he : ∀ c (i j : Fin (F.dimension c)), answer (task (pair c
      (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))) = residueBits (F.matrix c i j))
    (c : List Bool) (t : ℕ) :
    pairFst (((stage a task).reference answer)^[t] ((stage a task).initial c)) = c := by
  change pairFst (((RecursiveStage.controller (ops a) (initial a) task).reference answer)^[t] (initial a c)) = c
  rw [initial_eq, RecursiveStage.reference_iterate (ops a) (initial a) task answer c (F.matrix c) residueBits
    (correctAt a task answer he c), pairFst_pair]

end LeanCanny.Algebra.MatrixPower.ModularRecursiveStage
