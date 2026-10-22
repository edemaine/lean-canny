/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PolynomialPowerSpace
public import LeanCanny.Algebra.MatrixPowerRecursiveController

/-! # Resumable polynomial matrix-power coefficient queries

The flattened coefficient matrix uses the existing scalar controller. Its
entry requests are delegated to tasks, without assuming their computability.
-/

@[expose] public section

namespace LeanCanny.Algebra.PolynomialPower.RecursiveStage
open LeanCanny.Encoding LeanCanny.Computation
open MatrixPower MatrixPower.Controller
open Turing.MultiTapeTM

variable {F : ModularFamily} (a : ModularAccess F)

def ops : Callbacks :=
  modularCallbacks (Access.liftedDimension a.bits) a.bits.modulus (fun _ => [])

def initial : List Bool → List Bool :=
  initialPacket a.bits.exponent (Access.liftedRow a.bits) (Access.liftedCol a.bits)

def controller (entryTask : List Bool → List Bool) : RecursiveController.Controller (List Bool) (List Bool) :=
  MatrixPower.RecursiveStage.controller (ops a) (initial a) entryTask

theorem certificates (ha : a.bits.ControlsPolyTime) (entryTask : List Bool → List Bool) (ht : entryTask ∈ FP) :
    (controller a entryTask).Certificates (encQ := encBits) (encS := encBits) := by
  have h := a.power_controls ha
  have ho := modularCallbacks_polyTime h.dimension h.modulus (constFn_mem_FP [])
  exact MatrixPower.RecursiveStage.certificates (ops a) ⟨ho.dimension, ho.zero, ho.one, ho.combine⟩
    (initial a) entryTask (.ofFP _ (initialPacket_mem_FP h.exponent h.row h.col)) ht

theorem initial_encode (c : List Bool) :
    initial a c = pair c (stateBits (residueBits (m := F.modulus c))
      (.eval ⟨(F.exponent c).size, F.exponent c, F.power.row c, F.power.col c⟩ [])) :=
  initialPacket_encode _ _ _ c _ _ _ _ (a.power.exponent_eq c) (a.power.row_eq c) (a.power.col_eq c)

theorem correctAt (entryTask answer : List Bool → List Bool)
    (he : ∀ p, answer (entryTask p) = a.power.entry p) (c : List Bool) :
    CorrectAt (MatrixPower.RecursiveStage.oracleCallbacks (ops a) entryTask answer) c (F.power.matrix c) residueBits := by
  let : NeZero (F.modulus c) := ⟨F.modulus_ne_zero c⟩
  let : NeZero (F.power.modulus c) := ⟨F.modulus_ne_zero c⟩
  exact modularCallbacks_correctAt _ _ _ c _ _ (a.power.dimension_eq c) (a.power.modulus_eq c)
    (fun i j => (he _).trans (a.power.entry_eq c i j))

theorem halted_after (entryTask answer : List Bool → List Bool)
    (he : ∀ p, answer (entryTask p) = a.power.entry p) (c : List Bool) :
    (controller a entryTask).halted (((controller a entryTask).reference answer)^[
      work (F.dimension c * (F.degree c + 1)) (F.exponent c).size (F.exponent c) + 1] (initial a c)) = true :=
  MatrixPower.RecursiveStage.halted_after (ops a) (initial a) entryTask answer c (F.power.matrix c)
    residueBits (correctAt a entryTask answer he c) (F.exponent c) (F.power.row c) (F.power.col c) (initial_encode a c)

theorem context_iterate (entryTask answer : List Bool → List Bool)
    (c : List Bool) (t : ℕ) :
    pairFst (((controller a entryTask).reference answer)^[t] (initial a c)) = c := by
  have hpacket (k : ℕ) : ∃ s, ((controller a entryTask).reference answer)^[k] (initial a c) = pair c s := by
    induction k with
    | zero => exact ⟨_, initial_encode a c⟩
    | succ k ih =>
      obtain ⟨s, hs⟩ := ih
      rw [Function.iterate_succ_apply', hs]
      change ∃ s', (MatrixPower.RecursiveStage.controller (ops a) (initial a) entryTask).reference answer (pair c s) = pair c s'
      rw [MatrixPower.RecursiveStage.reference_packet]
      exact ⟨MatrixPower.Controller.nextState
        (MatrixPower.RecursiveStage.oracleCallbacks (ops a) entryTask answer) (pair c s),
        by simp only [MatrixPower.Controller.step, pairFst_pair]⟩
  obtain ⟨s, hs⟩ := hpacket t
  rw [hs, pairFst_pair]

theorem output_when_halted (entryTask answer : List Bool → List Bool)
    (he : ∀ p, answer (entryTask p) = a.power.entry p) (c : List Bool) (t : ℕ)
    (hh : (controller a entryTask).halted (((controller a entryTask).reference answer)^[t] (initial a c)) = true) :
    (controller a entryTask).output (((controller a entryTask).reference answer)^[t] (initial a c)) = F.value c := by
  have h := MatrixPower.RecursiveStage.output_when_halted (ops a) (initial a) entryTask answer c
    (F.power.matrix c) residueBits (correctAt a entryTask answer he c) (F.exponent c) t
    (F.power.row c) (F.power.col c) (initial_encode a c) hh
  refine h.trans ?_
  change residueBits ((PolynomialCoefficientMatrix.finHom (F.dimension c) (F.degree c) (F.matrix c) ^
    F.exponent c) (finProdFinEquiv (F.row c, Fin.last (F.degree c))) (finProdFinEquiv (F.col c, 0))) = _
  rw [PolynomialCoefficientMatrix.finHom_pow_last_zero]
  rfl

theorem state_length (entryTask answer : List Bool → List Bool)
    (he : ∀ p, answer (entryTask p) = a.power.entry p) (c : List Bool) (t : ℕ) :
    (((controller a entryTask).reference answer)^[t] (initial a c)).length ≤ 2 * c.length + 2 +
      64 * ((F.dimension c * (F.degree c + 1)).size + (F.exponent c).size + (F.modulus c).size + 1) ^ 2 := by
  let : NeZero (F.modulus c) := ⟨F.modulus_ne_zero c⟩
  exact MatrixPower.RecursiveStage.modular_state_length _ _ (initial a) entryTask answer c (F.modulus c)
    (F.power.matrix c) (correctAt a entryTask answer he c) (F.exponent c) t
    (F.power.row c) (F.power.col c) (initial_encode a c)

/-- Lower-triangular coefficient access is routed to one coefficient task or
one fixed zero task. The guard and query writer use only FP metadata. -/
def liftedTask (entryTask : List Bool → List Bool) (zeroTask : List Bool) (p : List Bool) : List Bool :=
  if Access.lower a.bits p then entryTask (Access.coefficientInput a.bits p) else zeroTask

theorem liftedTask_FP (ha : a.bits.ControlsPolyTime) (entryTask : List Bool → List Bool)
    (ht : entryTask ∈ FP) (zeroTask : List Bool) : liftedTask a entryTask zeroTask ∈ FP := by
  have hquery := mem_FP_comp (Access.coefficientInput_mem_FP a.bits ha) ht
  exact (flag_computable (Access.lower_mem_FP a.bits ha)).ite' hquery (constFn_mem_FP zeroTask)

theorem liftedTask_eq (entryTask answer : List Bool → List Bool) (zeroTask : List Bool)
    (he : ∀ p, answer (entryTask p) = a.bits.coefficient p) (hz : answer zeroTask = []) (p : List Bool) :
    answer (liftedTask a entryTask zeroTask p) = a.power.entry p := by
  change answer (if Access.lower a.bits p then entryTask (Access.coefficientInput a.bits p) else zeroTask) =
    (if Access.lower a.bits p then a.bits.coefficient (Access.coefficientInput a.bits p) else [])
  split_ifs <;> first | exact he _ | exact hz

end LeanCanny.Algebra.PolynomialPower.RecursiveStage
