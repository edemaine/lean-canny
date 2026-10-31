/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralDenominatorPassCorrect
public import LeanCanny.Algebra.IntegralScalarRootHistoryBounds

/-! # Actual critical histories have denominator-only scripts

Each instruction retains integer leading metadata and indices of earlier
denominators. Executing the chronological script recovers exactly the
newest-first denominator bank of the actual scalar-root history.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalDenominatorScript
open LeanCanny.Encoding LeanCanny.Computation IntegralDenominatorPass
open UniformIntegralPrefix MatrixPower
open scoped BigOperators Classical
set_option backward.isDefEq.respectTransparency false

structure Instruction where
  leading : ℤ
  degree : ℕ
  exponent : ℕ
  indices : List ℕ

def Instruction.next (s : Instruction) (v : List ℤ) : ℤ :=
  (s.leading * (s.indices.map (scale v)).prod ^ s.degree * (s.degree : ℤ)) ^ s.exponent

def execute (s : List Instruction) : List ℤ := s.foldl (fun v t => t.next v :: v) []

theorem execute_append (s : List Instruction) (t : Instruction) :
    execute (s ++ [t]) = t.next (execute s) :: execute s := by
  simp only [execute, List.foldl_append, List.foldl_cons, List.foldl_nil]

def selectorIndex {m : ℕ} (i : Option (Fin m)) : ℕ :=
  match i with
  | none => m
  | some j => j.val

theorem scale_ofFn {m : ℕ} (v : Fin m → ℤ) (i : Option (Fin m)) :
    scale (List.ofFn v) (selectorIndex i) =
      (match i with | none => 1 | some j => v j) := by
  cases i with
  | none => simp [scale, selectorIndex]
  | some j => simp [scale, selectorIndex]

noncomputable def instruction (F : IntegralHistoryCriticalBits.Family) (c : List Bool)
    (select : Fin (F.ambient c + 1) → Option (Fin (F.birth c))) : Instruction where
  leading := (F.data c).leading
  degree := (F.data c).degree
  exponent := IntegralClearedCriticalLeadingBits.exponent (IntegralHistoryCriticalBits.source F) c
  indices := List.ofFn (fun i => selectorIndex (select i))

theorem instruction_next (F : IntegralHistoryCriticalBits.Family) (c : List Bool)
    (bank : HeightBank (F.scalarPrefix c))
    (select : Fin (F.ambient c + 1) → Option (Fin (F.birth c)))
    (scales : ∀ i, (F.data c).scales i = bank.selectedDenominator (select i)) :
    (instruction F c select).next (List.ofFn bank.denominator) =
      IntegralClearedCriticalLeadingBits.integer (IntegralHistoryCriticalBits.source F) c := by
  have H (i : Fin (F.ambient c + 1)) :
      scale (List.ofFn bank.denominator) (selectorIndex (select i)) = (F.data c).scales i := by
    rw [scales i, scale_ofFn]
    cases select i <;> rfl
  unfold Instruction.next instruction
  rw [List.map_ofFn, List.prod_ofFn]
  simp only [Function.comp_apply, H]
  rfl

theorem history_script {n W D C S B m : ℕ} {P : Prefix S (2 ^ B) m} {bank : HeightBank P}
    (h : IntegralScalarRootHistoryBounds.History n W D C P bank) :
    ∃ s : List Instruction, s.length = m ∧ execute s = List.ofFn bank.denominator := by
  induction h with
  | base S B => exact ⟨[], rfl, by simp [execute]⟩
  | step F c bank previous select heights scales hC hP hn hW hD hdegree ih =>
    obtain ⟨s, hs, he⟩ := ih
    refine ⟨s ++ [instruction F c select], by simp only [List.length_append, List.length_singleton, hs], ?_⟩
    rw [execute_append, he, instruction_next F c bank select scales]
    change _ = List.ofFn (Fin.cons _ bank.denominator)
    rw [List.ofFn_succ]
    rfl

def instructionAt (s : List Instruction) (i : ℕ) : Instruction :=
  (s[i]?).getD ⟨0, 0, 0, []⟩

def program (s : List Bool → List Instruction) (modulus : List Bool → ℕ)
    (hm : ∀ c, modulus c ≠ 0) : IntegralDenominatorPass.Family where
  count c := (s c).length
  modulus := modulus
  modulus_ne_zero := hm
  arity c i := (instructionAt (s c) i).indices.length
  leading c i := (instructionAt (s c) i).leading
  degree c i := (instructionAt (s c) i).degree
  exponent c i := (instructionAt (s c) i).exponent
  index c i j := ((instructionAt (s c) i).indices[j]?).getD i

theorem program_next (s : List Bool → List Instruction) (modulus : List Bool → ℕ)
    (hm : ∀ c, modulus c ≠ 0) (c : List Bool) (i : ℕ) (v : List ℤ) :
    integerNext (program s modulus hm) c i v = (instructionAt (s c) i).next v := by
  let t := instructionAt (s c) i
  have H : (∏ j ∈ Finset.range t.indices.length, scale v ((t.indices[j]?).getD i)) =
      (t.indices.map (scale v)).prod := by
    rw [Finset.prod_range]
    rw [← Fin.prod_univ_fun_getElem t.indices (scale v)]
    apply Finset.prod_congr rfl
    intro j _hj
    rw [List.getElem?_eq_getElem j.isLt, Option.getD_some]
  change (t.leading * (∏ j ∈ Finset.range t.indices.length, scale v ((t.indices[j]?).getD i)) ^ t.degree *
    (t.degree : ℤ)) ^ t.exponent = t.next v
  rw [H]
  rfl

theorem program_integers (s : List Bool → List Instruction) (modulus : List Bool → ℕ)
    (hm : ∀ c, modulus c ≠ 0) (c : List Bool) (i : ℕ) (hi : i ≤ (s c).length) :
    integers (program s modulus hm) c i = execute ((s c).take i) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have HI : i < (s c).length := by omega
    rw [integers, ih (by omega), program_next, List.take_add_one,
      List.getElem?_eq_getElem HI, Option.toList_some, execute_append]
    simp only [instructionAt, List.getElem?_eq_getElem HI, Option.getD_some]

theorem program_final (s : List Bool → List Instruction) (modulus : List Bool → ℕ)
    (hm : ∀ c, modulus c ≠ 0) (c : List Bool) :
    integers (program s modulus hm) c ((s c).length) = execute (s c) := by
  rw [program_integers s modulus hm c _ le_rfl, List.take_length]

theorem script_reader_FP (s : List Bool → List Instruction) (modulus : List Bool → ℕ)
    (hm : ∀ c, modulus c ≠ 0) (a : IntegralDenominatorPass.Access (program s modulus hm))
    (j : List Bool → ℕ) (hj : BinaryFn j) :
    (fun c => residueBits (((execute (s c))[j c]?).getD 0 : ZMod (modulus c))) ∈ FP := by
  have H := integer_reader_FP (program s modulus hm) a j hj
  refine mem_FP_of_eq H (fun c => ?_)
  change residueBits (((integers (program s modulus hm) c ((s c).length))[j c]?).getD 0 : ZMod (modulus c)) = _
  rw [program_final]

end LeanCanny.Algebra.IntegralCriticalDenominatorScript
