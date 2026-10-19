/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.TreeFold
public import LeanCanny.Encoding.FiniteLookup

/-!
# Machine-level polynomial time for finite-frame tree folds

A fixed-width injective frame code and a fixed finite list covering every frame
turn the stack fold into a bitstring machine. Each input bit pushes or pops one
frame. The finite control is implemented by a certified finite lookup table.
The proof includes all intermediate stack sizes and applies uniformly to every
tree depth and to malformed inputs.
-/

@[expose] public section

namespace LeanCanny.Encoding.TreeFold
open Complexity
open Brackets

variable {σ : Type*}

def stackBits (code : σ → List Bool) (stack : List σ) : List Bool := (stack.map code).flatten

@[simp] theorem stackBits_nil (code : σ → List Bool) : stackBits code [] = [] := rfl

@[simp] theorem stackBits_cons (code : σ → List Bool) (s : σ) (rest : List σ) :
    stackBits code (s :: rest) = code s ++ stackBits code rest := rfl

def encode (code : σ → List Bool) : Option (List σ) → List Bool
  | none => [false]
  | some stack => true :: stackBits code stack

theorem encode_length (code : σ → List Bool) (width : ℕ)
    (hlen : ∀ s, (code s).length = width) (state : Option (List σ)) :
    (encode code state).length = 1 + width * frameCount state := by
  have hs : ∀ stack : List σ, (stackBits code stack).length = width * stack.length := by
    intro stack
    induction stack with
    | nil => simp
    | cons s rest ih =>
        simp only [stackBits_cons, List.length_append, hlen, List.length_cons, ih, Nat.mul_add,
          Nat.mul_one]
        omega
  cases state <;> simp [encode, frameCount, hs, Nat.add_comm]

def pairPattern (code : σ → List Bool) (p : σ × σ) : List Bool := code p.1 ++ code p.2

theorem pairPattern_injective (code : σ → List Bool) (width : ℕ)
    (hlen : ∀ s, (code s).length = width) (hinj : Function.Injective code) :
    Function.Injective (pairPattern code) := by
  intro a b h
  have he := List.append_inj h ((hlen a.1).trans (hlen b.1).symm)
  exact Prod.ext (hinj he.1) (hinj he.2)

def popKey (width : ℕ) (xs : List Bool) : List Bool := (xs.drop 1).take (2 * width)

def popTail (width : ℕ) (xs : List Bool) : List Bool := (xs.drop 1).drop (2 * width)

def popEncoded (code : σ → List Bool) (width : ℕ) (keys : List σ)
    (combine : σ → σ → σ) : List Bool → List Bool :=
  FiniteLookup.rewrite (keys.product keys) (pairPattern code)
    (fun p => true :: code (combine p.1 p.2)) (popKey width) (popTail width) [false]

def encodedStep (empty : σ) (combine : σ → σ → σ) (code : σ → List Bool)
    (width : ℕ) (keys : List σ) (b : Bool) (xs : List Bool) : List Bool :=
  if xs[0]?.getD false = true then
    if b then true :: (code empty ++ xs.drop 1)
    else popEncoded code width keys combine xs
  else [false]

theorem popKey_two (code : σ → List Bool) (width : ℕ)
    (hlen : ∀ s, (code s).length = width) (child parent : σ) (rest : List σ) :
    popKey width (encode code (some (child :: parent :: rest))) = pairPattern code (child, parent) := by
  change (code child ++ (code parent ++ stackBits code rest)).take (2 * width) = _
  have hp : (code child ++ code parent).length = 2 * width := by simp [hlen]; omega
  rw [← List.append_assoc, ← hp, List.take_left]
  rfl

theorem popTail_two (code : σ → List Bool) (width : ℕ)
    (hlen : ∀ s, (code s).length = width) (child parent : σ) (rest : List σ) :
    popTail width (encode code (some (child :: parent :: rest))) = stackBits code rest := by
  change (code child ++ (code parent ++ stackBits code rest)).drop (2 * width) = _
  have hp : (code child ++ code parent).length = 2 * width := by simp [hlen]; omega
  rw [← List.append_assoc, ← hp, List.drop_left]

/-- The finite lookup implementation agrees with the abstract stack step. -/
theorem encodedStep_encode (empty : σ) (combine : σ → σ → σ) (code : σ → List Bool)
    (width : ℕ) (hwidth : 0 < width) (hlen : ∀ s, (code s).length = width)
    (hinj : Function.Injective code) (keys : List σ) (hkeys : ∀ s, s ∈ keys)
    (b : Bool) (state : Option (List σ)) :
    encodedStep empty combine code width keys b (encode code state) =
      encode code (step empty combine b state) := by
  cases state with
  | none => simp [encodedStep, encode, step]
  | some stack =>
      cases b with
      | true => simp [encodedStep, encode, step]
      | false =>
          simp only [encodedStep, encode, List.getElem?_cons_zero, Option.getD_some,
            ite_true, Bool.false_eq_true, ite_false]
          cases stack with
          | nil =>
              apply FiniteLookup.rewrite_miss
              intro p _ h
              have hh := congrArg List.length h
              simp [popKey, pairPattern, hlen] at hh
              omega
          | cons child tail =>
              cases tail with
              | nil =>
                  apply FiniteLookup.rewrite_miss
                  intro p _ h
                  have hh := congrArg List.length h
                  simp [popKey, pairPattern, stackBits, hlen] at hh
                  omega
              | cons parent rest =>
                  change popEncoded code width keys combine
                    (encode code (some (child :: parent :: rest))) =
                    encode code (some (combine child parent :: rest))
                  unfold popEncoded
                  rw [FiniteLookup.rewrite_match (keys.product keys) (pairPattern code)
                    (fun p => true :: code (combine p.1 p.2)) (popKey width) (popTail width)
                    [false] _ (pairPattern_injective code width hlen hinj) (child, parent)
                    (List.mem_product.mpr ⟨hkeys child, hkeys parent⟩)
                    (popKey_two code width hlen child parent rest)]
                  rw [popTail_two code width hlen]
                  rfl

theorem encodedStep_mem_FP (empty : σ) (combine : σ → σ → σ) (code : σ → List Bool)
    (width : ℕ) (keys : List σ) (b : Bool) : encodedStep empty combine code width keys b ∈ FP := by
  have hdrop := drop_mem_FP id_mem_FP (UnaryFn.const 1)
  have hkey : popKey width ∈ FP := take_mem_FP hdrop (UnaryFn.const (2 * width))
  have htail : popTail width ∈ FP := drop_mem_FP hdrop (UnaryFn.const (2 * width))
  have hpop : popEncoded code width keys combine ∈ FP :=
    FiniteLookup.rewrite_mem_FP _ _ _ hkey htail _
  have hpush : (fun xs => true :: (code empty ++ xs.drop 1)) ∈ FP :=
    Cobham.appendFn_mem_FP (constFn_mem_FP (true :: code empty)) hdrop
  cases b
  · exact (FPPred.getBit id_mem_FP (UnaryFn.const 0)).ite_mem_FP hpop (constFn_mem_FP [false])
  · exact (FPPred.getBit id_mem_FP (UnaryFn.const 0)).ite_mem_FP hpush (constFn_mem_FP [false])

/-- A finite-frame bottom-up tree fold is in Complexitylib's multitape `FP`.
The code and exhaustive list of frames are fixed parameters, not input-dependent oracles. -/
theorem runEncoded_mem_FP (empty : σ) (combine : σ → σ → σ) (code : σ → List Bool)
    (width : ℕ) (hwidth : 0 < width) (hlen : ∀ s, (code s).length = width)
    (hinj : Function.Injective code) (keys : List σ) (hkeys : ∀ s, s ∈ keys) :
    (fun bits => encode code (run empty combine bits)) ∈ FP := by
  have hacc : (fun w : List Bool => pairSnd (pairFst w)) ∈ FP :=
    mem_FP_comp pairFst_mem_FP pairSnd_mem_FP
  refine recFold_mem_FP_of_bound (g := fun _ bits => encode code (run empty combine bits))
    (mem_FP_comp hacc (encodedStep_mem_FP empty combine code width keys false))
    (mem_FP_comp hacc (encodedStep_mem_FP empty combine code width keys true))
    (constFn_mem_FP (encode code (some [empty]))) (constFn_mem_FP []) id_mem_FP
    ?_ ?_ ?_ ((PolyBound.const 1).add
      ((PolyBound.const width).mul (PolyBound.id.add (PolyBound.const 1)))) ?_
  · intro z
    rfl
  · intro z bits
    simpa only [Function.comp_apply, pairFst_pair, pairSnd_pair, run_cons] using
      (encodedStep_encode empty combine code width hwidth hlen hinj keys hkeys false
        (run empty combine bits)).symm
  · intro z bits
    simpa only [Function.comp_apply, pairFst_pair, pairSnd_pair, run_cons] using
      (encodedStep_encode empty combine code width hwidth hlen hinj keys hkeys true
        (run empty combine bits)).symm
  · intro z bits hbits
    rw [encode_length code width hlen]
    have hh := (run_frameCount_le empty combine bits).trans (Nat.add_le_add_right hbits.length_le 1)
    exact Nat.add_le_add_left (Nat.mul_le_mul_left width hh) 1

end LeanCanny.Encoding.TreeFold
