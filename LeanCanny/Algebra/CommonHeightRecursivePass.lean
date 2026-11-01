/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.CommonHeightResidueFP
public import LeanCanny.Algebra.ModularFoldRecursiveController

/-! # Resumable cofactor products of earlier retained leadings

Only count, modulus and omitted-index metadata are native FP. Each scalar
residue is a recursive producer-leading request at birth `count-1-i`.
The finish masks the omitted factor locally, so there is no extra term
phase and no FP or space-evaluator premise for the retained leadings.
The accumulator remains one residue word, including for empty banks and
modulus one.
-/

@[expose] public section
namespace LeanCanny.Algebra.CommonHeightRecursivePass
open LeanCanny.Encoding LeanCanny.Computation MatrixPower Turing.MultiTapeTM
open CommonHeightBits
open scoped Classical BigOperators

structure Controls (F : Scalars) : Prop where
  count : UnaryFn F.count
  modulus : BinaryFn F.modulus
  selected : BinaryFn F.selected

def descriptor (F : Scalars) (p : List Bool) : List Bool :=
  pair (pairFst p) (pair
    (BinaryNatCode.encode (F.count (pairFst p) - 1 - Nat.fromBitsLE (pairSnd p))) (pairSnd p))

theorem descriptor_FP (F : Scalars) (a : Controls F) : descriptor F ∈ FP := by
  have HC : BinaryFn (fun p => F.count (pairFst p)) := (BinaryFn.ofUnary a.count).comp pairFst_mem_FP
  exact mem_FP_pair pairFst_mem_FP (mem_FP_pair
    ((HC.sub (BinaryFn.const 1)).sub (BinaryFn.fromBits pairSnd_mem_FP)).bits_mem_FP pairSnd_mem_FP)

theorem descriptor_packet (F : Scalars) (q : List Bool) (i : ℕ) :
    descriptor F (pair q (BinaryNatCode.encode i)) =
      pair q (pair (BinaryNatCode.encode (F.count q - 1 - i)) (BinaryNatCode.encode i)) := by
  simp only [descriptor, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]

theorem producer_birth_lt (F : Scalars) (q : List Bool) (i : ℕ) (hi : i < F.count q) :
    F.count q - 1 - i < F.count q := by omega

def modulus (F : Scalars) (q : List Bool) := BinaryNatCode.encode (F.modulus q)

def finish (F : Scalars) (z : List Bool) : List Bool :=
  ModularProduct.finish (modulus F) (pair (pairFst z)
    (if Nat.fromBitsLE (BoundedFold.counter (pairFst z)) = F.selected (pairFst (pairFst z)) then
      ArithmeticBits.one (modulus F (pairFst (pairFst z))) else pairSnd z))

theorem finish_FP (F : Scalars) (a : Controls F) : finish F ∈ FP := by
  have HC := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
  have HI := mem_FP_comp pairFst_mem_FP BoundedFold.counter_mem_FP
  have HP := (BinaryFn.fromBits HI).eq (a.selected.comp HC)
  have HM := mem_FP_comp HC a.modulus.bits_mem_FP
  exact mem_FP_comp (mem_FP_pair pairFst_mem_FP
    (HP.ite_mem_FP (mem_FP_comp (g := ArithmeticBits.one) HM ArithmeticBits.one_mem_FP) pairSnd_mem_FP))
      (ModularProduct.finish_mem_FP a.modulus.bits_mem_FP)

def program (F : Scalars) (task : List Bool → List Bool) : RecursiveFold.Program where
  count := F.count
  seed := ModularProduct.seed (modulus F)
  entryTask := task ∘ descriptor F
  finish := finish F

theorem certificates (F : Scalars) (a : Controls F) (task : List Bool → List Bool) (ht : task ∈ FP) :
    (program F task).controller.Certificates (encQ := encBits) (encS := RecursiveFold.encState) :=
  RecursiveFold.Program.certificates _ (BinaryFn.ofUnary a.count)
    (ModularProduct.seed_mem_FP a.modulus.bits_mem_FP)
    (mem_FP_comp (f := descriptor F) (g := task) (descriptor_FP F a) ht) (finish_FP F a)

noncomputable def masked (F : Scalars) (task answer : List Bool → List Bool) (p : List Bool) : List Bool :=
  if Nat.fromBitsLE (pairSnd p) = F.selected (pairFst p) then ArithmeticBits.one (modulus F (pairFst p))
  else answer (task (descriptor F p))

theorem update_eq (F : Scalars) (task answer : List Bool → List Bool) :
    (program F task).update answer = ModularProduct.update (modulus F) (masked F task answer) := by
  funext p
  simp only [RecursiveFold.Program.update, program, ModularProduct.update, BoundedFold.update, finish, masked,
    Function.comp_apply, pairFst_pair, pairSnd_pair, BoundedFold.query,
    BoundedFold.counter]

theorem partialValue (F : Scalars) (task answer : List Bool → List Bool) (q : List Bool)
    (ha : ∀ i < F.count q, answer (task (pair q
      (pair (BinaryNatCode.encode (F.count q - 1 - i)) (BinaryNatCode.encode i)))) =
        residueBits (F.scale q i : ZMod (F.modulus q))) (k : ℕ) (hk : k ≤ F.count q) :
    (program F task).partialValue answer q k =
      residueBits ((∏ i ∈ Finset.range k, if i = F.selected q then 1 else F.scale q i : ℤ) : ZMod (F.modulus q)) := by
  unfold RecursiveFold.Program.partialValue
  rw [update_eq]
  change BoundedFold.fold (ModularProduct.update (modulus F) (masked F task answer))
    (ModularProduct.seed (modulus F)) q k = _
  have HM : Nat.fromBitsLE (modulus F q) = F.modulus q := Nat.fromBitsLE_bits _
  have HC : ∀ i < F.count q, masked F task answer (pair q (BinaryNatCode.encode i)) =
      residueBits ((if i = F.selected q then 1 else F.scale q i : ℤ) : ZMod (F.modulus q)) := by
    intro i hi
    simp only [masked, pairFst_pair, pairSnd_pair]
    rw [show Nat.fromBitsLE (BinaryNatCode.encode i) = i from Nat.fromBitsLE_bits i]
    by_cases H : i = F.selected q
    · rw [ite_eq_left H, ite_eq_left H]
      simpa only [modulus, Int.cast_one] using ArithmeticBits.one_residueBits (F.modulus q)
    · rw [ite_eq_right H, ite_eq_right H, descriptor_packet]
      exact ha i hi
  have HF := ModularProduct.fold_eq_product (modulus F) (masked F task answer) q (F.count q)
    (fun i => ((if i = F.selected q then 1 else F.scale q i : ℤ) : ZMod (Nat.fromBitsLE (modulus F q))))
    (by rw [HM]; exact Nat.pos_of_ne_zero (F.modulus_ne_zero q))
    (fun i hi => (HC i hi).trans (congrArg (fun M : ℕ => residueBits
      ((if i = F.selected q then 1 else F.scale q i : ℤ) : ZMod M)) HM.symm)) k hk
  have HE : BoundedFold.fold (ModularProduct.update (modulus F) (masked F task answer))
      (ModularProduct.seed (modulus F)) q k = residueBits
        ((∏ i ∈ Finset.range k, if i = F.selected q then 1 else F.scale q i : ℤ) : ZMod (Nat.fromBitsLE (modulus F q))) := by
    simpa only [← Int.cast_prod] using HF
  exact HE.trans (congrArg (fun M : ℕ => residueBits
    ((∏ i ∈ Finset.range k, if i = F.selected q then 1 else F.scale q i : ℤ) : ZMod M)) HM)

theorem value_eq (F : Scalars) (task answer : List Bool → List Bool) (q : List Bool)
    (ha : ∀ i < F.count q, answer (task (pair q
      (pair (BinaryNatCode.encode (F.count q - 1 - i)) (BinaryNatCode.encode i)))) =
        residueBits (F.scale q i : ZMod (F.modulus q))) :
    (program F task).value answer q = residueBits (F.cofactor q : ZMod (F.modulus q)) :=
  partialValue F task answer q ha _ le_rfl

theorem requests_iff (F : Scalars) (task answer : List Bool → List Bool) (q child : List Bool) :
    (program F task).controller.Requests answer (program F task).count q child ↔
      ∃ i < F.count q, child = task (pair q
        (pair (BinaryNatCode.encode (F.count q - 1 - i)) (BinaryNatCode.encode i))) := by
  rw [RecursiveFold.Program.requests_iff]
  simp only [RecursiveFold.Program.child, program, Function.comp_apply, descriptor_packet]

theorem orbit_length (F : Scalars) (task answer : List Bool → List Bool) (q : List Bool)
    (ha : ∀ i < F.count q, answer (task (pair q
      (pair (BinaryNatCode.encode (F.count q - 1 - i)) (BinaryNatCode.encode i)))) =
        residueBits (F.scale q i : ZMod (F.modulus q))) (t : ℕ) :
    (RecursiveFold.encState (((program F task).controller.reference answer)^[t]
      ((program F task).initial q))).length ≤
        2 * q.length + 2 * (encNat (F.count q)).length + (modulus F q).length + 2 := by
  apply RecursiveFold.Program.orbit_length
  intro k hk
  rw [partialValue F task answer q ha k hk]
  let : NeZero (F.modulus q) := ⟨F.modulus_ne_zero q⟩
  let z : ℤ := ∏ i ∈ Finset.range k, if i = F.selected q then 1 else F.scale q i
  have HM : Nat.fromBitsLE (modulus F q) = F.modulus q := Nat.fromBitsLE_bits _
  have HT : (z : ZMod (F.modulus q)).val < Nat.fromBitsLE (modulus F q) := HM.symm ▸ ZMod.val_lt _
  exact ModularFold.bits_length_le (modulus F) q (z : ZMod (F.modulus q)).val HT


end LeanCanny.Algebra.CommonHeightRecursivePass
