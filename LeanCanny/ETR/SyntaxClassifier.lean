/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.NumericPayloadFP
public import LeanCanny.Encoding.TreeFoldFP
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Basic

/-!
# Finite summaries for the ETR tree grammar

Node categories may overlap. Child counts are capped at six, enough to distinguish
all constructor tags. A frame retains the first three child summaries and the
aggregate flags needed to recognize arbitrary-length unary and binary payloads.
-/

@[expose] public section

namespace LeanCanny.ETR.SyntaxClassifier
open Complexity

def cap (n : ℕ) : Fin 7 := ⟨min 6 n, by omega⟩

@[simp] theorem cap_val (n : ℕ) : (cap n).val = min 6 n := rfl

@[simp] theorem cap_succ (n : ℕ) : cap ((cap n).val + 1) = cap (n + 1) := by
  apply Fin.ext
  simp only [cap_val]
  omega

@[ext] structure Info where
  count : Fin 7
  empty : Bool
  unary : Bool
  trueBit : Bool
  natural : Bool
  integer : Bool
  term : Bool
  formula : Bool
  deriving DecidableEq, Repr

def infoEquiv : Info ≃ (Fin 7 × Bool × Bool × Bool × Bool × Bool × Bool × Bool) where
  toFun i := ⟨i.count, i.empty, i.unary, i.trueBit, i.natural, i.integer, i.term, i.formula⟩
  invFun := fun ⟨c, e, u, b, n, z, t, p⟩ => ⟨c, e, u, b, n, z, t, p⟩
  left_inv := by intro i; cases i; rfl
  right_inv := by rintro ⟨c, e, u, b, n, z, t, p⟩; rfl

instance : Fintype Info := Fintype.ofEquiv _ infoEquiv.symm

def noInfo : Info := ⟨0, false, false, false, false, false, false, false⟩

def Info.tag (i : Info) (n : ℕ) : Bool := i.unary && decide (i.count.val = n)

def Info.isBit (i : Info) : Bool := i.empty || i.trueBit

@[ext] structure Frame where
  count : Fin 7
  allEmpty : Bool
  allBits : Bool
  lastTrue : Bool
  first : Info
  second : Info
  third : Info
  deriving DecidableEq, Repr

def frameEquiv : Frame ≃ (Fin 7 × Bool × Bool × Bool × Info × Info × Info) where
  toFun f := ⟨f.count, f.allEmpty, f.allBits, f.lastTrue, f.first, f.second, f.third⟩
  invFun := fun ⟨c, e, b, l, x, y, z⟩ => ⟨c, e, b, l, x, y, z⟩
  left_inv := by intro f; cases f; rfl
  right_inv := by rintro ⟨c, e, b, l, x, y, z⟩; rfl

instance : Fintype Frame := Fintype.ofEquiv _ frameEquiv.symm

/-- Direct summary of a list, used as the specification of the frame update. -/
def summary (xs : List Info) : Frame where
  count := cap xs.length
  allEmpty := xs.all Info.empty
  allBits := xs.all Info.isBit
  lastTrue := (xs.getLast?.getD noInfo).trueBit
  first := xs[0]?.getD noInfo
  second := xs[1]?.getD noInfo
  third := xs[2]?.getD noInfo

def emptyFrame : Frame := summary []

def prepend (i : Info) (f : Frame) : Frame where
  count := cap (f.count.val + 1)
  allEmpty := i.empty && f.allEmpty
  allBits := i.isBit && f.allBits
  lastTrue := if f.count.val = 0 then i.trueBit else f.lastTrue
  first := i
  second := f.first
  third := f.second

theorem summary_cons (i : Info) (xs : List Info) :
    summary (i :: xs) = prepend i (summary xs) := by
  cases xs with
  | nil => rfl
  | cons j xs =>
      apply Frame.ext <;>
        simp [summary, prepend, List.getLast?_cons_of_ne_nil]
      apply Fin.ext
      simp only [cap_val]
      omega

/-- Complete a node after its children have been summarized. -/
def finish (f : Frame) : Info where
  count := f.count
  empty := decide (f.count.val = 0)
  unary := f.allEmpty
  trueBit := decide (f.count.val = 1) && f.first.empty
  natural := f.allBits && (decide (f.count.val = 0) || f.lastTrue)
  integer := decide (f.count.val = 2) &&
    (f.first.tag 0 || f.first.tag 1) && f.second.natural
  term :=
    (decide (f.count.val = 2) &&
      ((f.first.tag 0 && f.second.integer) || (f.first.tag 1 && f.second.unary))) ||
    (decide (f.count.val = 3) && (f.first.tag 2 || f.first.tag 3) &&
      f.second.term && f.third.term)
  formula :=
    (decide (f.count.val = 1) && f.first.tag 0) ||
    (decide (f.count.val = 2) &&
      (((f.first.tag 1 || f.first.tag 2) && f.second.term) ||
        (f.first.tag 3 && f.second.formula))) ||
    (decide (f.count.val = 3) && (f.first.tag 4 || f.first.tag 5) &&
      f.second.formula && f.third.formula)

def combine (child parent : Frame) : Frame := prepend (finish child) parent

@[simp] theorem min_six_eq_iff (n k : ℕ) (hk : k < 6) : min 6 n = k ↔ n = k := by omega

/-- The list-level specification of node classification, before frame compression. -/
def direct (xs : List Info) : Info where
  count := cap xs.length
  empty := xs.isEmpty
  unary := xs.all Info.empty
  trueBit := match xs with | [a] => a.empty | _ => false
  natural := xs.all Info.isBit && (xs.isEmpty || (xs.getLast?.getD noInfo).trueBit)
  integer := match xs with
    | [a, b] => (a.tag 0 || a.tag 1) && b.natural
    | _ => false
  term := match xs with
    | [a, b] => (a.tag 0 && b.integer) || (a.tag 1 && b.unary)
    | [a, b, c] => (a.tag 2 || a.tag 3) && b.term && c.term
    | _ => false
  formula := match xs with
    | [a] => a.tag 0
    | [a, b] => ((a.tag 1 || a.tag 2) && b.term) || (a.tag 3 && b.formula)
    | [a, b, c] => (a.tag 4 || a.tag 5) && b.formula && c.formula
    | _ => false

theorem finish_summary (xs : List Info) : finish (summary xs) = direct xs := by
  rcases xs with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, rest⟩⟩⟩⟩ <;>
    apply Info.ext <;> simp [finish, summary, direct, cap, noInfo]

def classify : Data → Info
  | .l xs => finish (summary (xs.map classify))

/-- The concrete classifier is exactly the node value computed by the generic stack fold. -/
theorem classify_eq_fold (d : Data) :
    classify d = finish (LeanCanny.Encoding.TreeFold.foldData emptyFrame combine d) := by
  have key : ∀ (n : ℕ) (d : Data), d.size ≤ n →
      classify d = finish (LeanCanny.Encoding.TreeFold.foldData emptyFrame combine d) := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
        rintro ⟨xs⟩ hn
        rw [classify, LeanCanny.Encoding.TreeFold.foldData]
        congr 1
        have hchildren : ∀ c ∈ xs,
            classify c = finish (LeanCanny.Encoding.TreeFold.foldData emptyFrame combine c) := by
          intro c hc
          exact ih c.size ((Data.size_lt_of_mem hc).trans_le hn) c le_rfl
        induction xs with
        | nil => rfl
        | cons c cs ihcs =>
            rw [List.map_cons, List.map_cons, List.foldr_cons, summary_cons,
              hchildren c (List.mem_cons_self ..), combine]
            congr 1
            have htail : (Data.l cs).size ≤ n := by rw [Data.cons_size] at hn; omega
            exact ihcs htail (fun c' hc' => hchildren c' (List.mem_cons_of_mem c hc'))
  exact key d.size d le_rfl

/-- Intended meanings of all finite flags. Count is retained independently of unary validity. -/
structure Correct (d : Data) (i : Info) : Prop where
  count : i.count.val = min 6 d.asList.length
  empty : i.empty = true ↔ d = Data.empty
  unary : i.unary = true ↔ ∃ n : ℕ, d = Codec.unary n
  trueBit : i.trueBit = true ↔ d = Codec.bit true
  natural : i.natural = true ↔ ∃ n : ℕ, d = Codec.natural n
  integer : i.integer = true ↔ ∃ z : ℤ, d = Codec.integer z
  term : i.term = true ↔ ∃ t : Term, d = t.toData
  formula : i.formula = true ↔ ∃ p : Formula, d = p.toData

theorem Correct.tag_iff {d : Data} {i : Info} (h : Correct d i) (n : ℕ) (hn : n < 6) :
    i.tag n = true ↔ d = Codec.unary n := by
  simp only [Info.tag, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨hu, hc⟩
    obtain ⟨m, rfl⟩ := h.unary.mp hu
    have hm := h.count
    simp only [Codec.unary, Data.l_asList, List.length_replicate] at hm
    have he : m = n := by omega
    subst m
    rfl
  · intro hd
    refine ⟨h.unary.mpr ⟨n, hd⟩, ?_⟩
    have hc := h.count
    rw [hd] at hc
    simp only [Codec.unary, Data.l_asList, List.length_replicate] at hc
    omega

theorem Correct.isBit_iff {d : Data} {i : Info} (h : Correct d i) :
    i.isBit = true ↔ ∃ b : Bool, d = Codec.bit b := by
  rw [Info.isBit, Bool.or_eq_true, h.empty, h.trueBit]
  constructor
  · rintro (he | ht)
    · exact ⟨false, he⟩
    · exact ⟨true, ht⟩
  · rintro ⟨b, hb⟩
    cases b
    · exact Or.inl hb
    · exact Or.inr hb

end LeanCanny.ETR.SyntaxClassifier
