/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.SyntaxClassifier

/-! # Correctness of the finite ETR syntax classifier -/

@[expose] public section

namespace LeanCanny.ETR.SyntaxClassifier


theorem classify_count (d : Data) : (classify d).count.val = min 6 d.asList.length := by
  cases d with
  | l xs => rw [classify, finish_summary]; simp [direct]

theorem classify_empty_iff (d : Data) : (classify d).empty = true ↔ d = Data.empty := by
  cases d with
  | l xs => rw [classify, finish_summary]; simp [direct]

theorem unary_image_l (xs : List Data) :
    (∃ n : ℕ, Data.l xs = Codec.unary n) ↔ ∀ c ∈ xs, c = Data.empty := by
  constructor
  · rintro ⟨n, he⟩
    change Data.l xs = Data.l (List.replicate n Data.empty) at he
    rw [Data.l.inj he]
    simp
  · intro h
    exact ⟨xs.length, congrArg Data.l (List.eq_replicate_of_mem h)⟩

theorem classify_unary_iff (d : Data) :
    (classify d).unary = true ↔ ∃ n : ℕ, d = Codec.unary n := by
  cases d with
  | l xs =>
      rw [classify, finish_summary]
      change (xs.map classify).all Info.empty = true ↔ _
      rw [unary_image_l]
      simp only [List.all_eq_true, List.forall_mem_map, classify_empty_iff]

theorem classify_tag_iff (d : Data) (n : ℕ) (hn : n < 6) :
    (classify d).tag n = true ↔ d = Codec.unary n := by
  simp only [Info.tag, Bool.and_eq_true, decide_eq_true_eq, classify_unary_iff, classify_count]
  constructor
  · rintro ⟨⟨m, rfl⟩, hm⟩
    simp only [Codec.unary, Data.l_asList, List.length_replicate] at hm
    have he : m = n := by omega
    subst m
    rfl
  · intro hd
    refine ⟨⟨n, hd⟩, ?_⟩
    rw [hd]
    simp only [Codec.unary, Data.l_asList, List.length_replicate]
    omega

theorem classify_trueBit_iff (d : Data) : (classify d).trueBit = true ↔ d = Codec.bit true := by
  cases d with
  | l xs =>
      rw [classify, finish_summary]
      rcases xs with _ | ⟨a, _ | ⟨b, rest⟩⟩ <;>
        simp [direct, Codec.bit, classify_empty_iff]

theorem classify_isBit_iff (d : Data) :
    (classify d).isBit = true ↔ ∃ b : Bool, d = Codec.bit b := by
  rw [Info.isBit, Bool.or_eq_true, classify_empty_iff, classify_trueBit_iff]
  constructor
  · rintro (he | ht)
    · exact ⟨false, he⟩
    · exact ⟨true, ht⟩
  · rintro ⟨b, hb⟩
    cases b
    · exact Or.inl hb
    · exact Or.inr hb

theorem all_bits_image (xs : List Data) :
    (∀ d ∈ xs, ∃ b : Bool, d = Codec.bit b) ↔ ∃ digits : List Bool, xs = digits.map Codec.bit := by
  constructor
  · intro h
    induction xs with
    | nil => exact ⟨[], rfl⟩
    | cons d ds ih =>
        obtain ⟨b, hb⟩ := h d (List.mem_cons_self ..)
        obtain ⟨bs, hbs⟩ := ih (fun c hc => h c (List.mem_cons_of_mem d hc))
        exact ⟨b :: bs, by rw [hb, hbs]; rfl⟩
  · rintro ⟨digits, rfl⟩
    intro d hd
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp hd
    exact ⟨b, rfl⟩

theorem allBits_summary_iff (xs : List Data) :
    (xs.map classify).all Info.isBit = true ↔ ∃ digits : List Bool, xs = digits.map Codec.bit := by
  rw [← all_bits_image]
  simp only [List.all_eq_true, List.forall_mem_map, classify_isBit_iff]

theorem lastTrue_summary_iff (xs : List Data) :
    ((xs.map classify).getLast?.getD noInfo).trueBit = true ↔
      xs.getLast? = some (Codec.bit true) := by
  rw [List.getLast?_map]
  cases hl : xs.getLast? with
  | none => simp [noInfo]
  | some d => simp [classify_trueBit_iff]

theorem canonical_bit_nodes_iff (digits : List Bool) :
    (digits.map Codec.bit = [] ∨ (digits.map Codec.bit).getLast? = some (Codec.bit true)) ↔
      Codec.CanonicalDigits digits := by
  rw [List.getLast?_map]
  cases hl : digits.getLast? with
  | none => simp [Codec.CanonicalDigits, hl]
  | some b => cases b <;> simp [Codec.CanonicalDigits, hl, Codec.bit]

theorem natural_image_l (xs : List Data) :
    (∃ n : ℕ, Data.l xs = Codec.natural n) ↔
      ∃ digits : List Bool, xs = digits.map Codec.bit ∧ Codec.CanonicalDigits digits := by
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n.bits, Data.l.inj hn, Codec.canonicalDigits_bits n⟩
  · rintro ⟨digits, hd, hc⟩
    obtain ⟨n, rfl⟩ := (Codec.canonicalDigits_iff digits).mp hc
    exact ⟨n, congrArg Data.l hd⟩

theorem classify_natural_iff (d : Data) :
    (classify d).natural = true ↔ ∃ n : ℕ, d = Codec.natural n := by
  cases d with
  | l xs =>
      rw [classify, finish_summary]
      change ((xs.map classify).all Info.isBit &&
        ((xs.map classify).isEmpty || ((xs.map classify).getLast?.getD noInfo).trueBit)) = true ↔ _
      rw [Bool.and_eq_true, Bool.or_eq_true, allBits_summary_iff,
        List.isEmpty_iff, List.map_eq_nil_iff, lastTrue_summary_iff, natural_image_l]
      constructor
      · rintro ⟨⟨digits, hd⟩, hc⟩
        exact ⟨digits, hd, (canonical_bit_nodes_iff digits).mp (hd ▸ hc)⟩
      · rintro ⟨digits, hd, hc⟩
        exact ⟨⟨digits, hd⟩, hd ▸ (canonical_bit_nodes_iff digits).mpr hc⟩

theorem integer_image_l (xs : List Data) :
    (∃ z : ℤ, Data.l xs = Codec.integer z) ↔
      (∃ n : ℕ, xs = [Codec.unary 0, Codec.natural n]) ∨
      (∃ n : ℕ, xs = [Codec.unary 1, Codec.natural n]) := by
  constructor
  · rintro ⟨z, hz⟩
    cases z with
    | ofNat n => exact Or.inl ⟨n, Data.l.inj hz⟩
    | negSucc n => exact Or.inr ⟨n, Data.l.inj hz⟩
  · rintro (⟨n, rfl⟩ | ⟨n, rfl⟩)
    · exact ⟨.ofNat n, rfl⟩
    · exact ⟨.negSucc n, rfl⟩

theorem classify_integer_iff (d : Data) :
    (classify d).integer = true ↔ ∃ z : ℤ, d = Codec.integer z := by
  cases d with
  | l xs =>
      rw [classify, finish_summary, integer_image_l]
      rcases xs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩ <;>
        simp only [List.map_cons, List.map_nil, direct, Bool.and_eq_true, Bool.or_eq_true,
          classify_tag_iff _ 0 (by decide), classify_tag_iff _ 1 (by decide),
          classify_natural_iff, List.cons.injEq]
      all_goals aesop

theorem term_image_l (xs : List Data) :
    (∃ t : Term, Data.l xs = t.toData) ↔
      (∃ z : ℤ, xs = [Codec.unary 0, Codec.integer z]) ∨
      (∃ i : ℕ, xs = [Codec.unary 1, Codec.unary i]) ∨
      (∃ t u : Term, xs = [Codec.unary 2, t.toData, u.toData]) ∨
      (∃ t u : Term, xs = [Codec.unary 3, t.toData, u.toData]) := by
  constructor
  · rintro ⟨t, ht⟩
    cases t with
    | const z => exact Or.inl ⟨z, Data.l.inj ht⟩
    | var i => exact Or.inr (Or.inl ⟨i, Data.l.inj ht⟩)
    | add t u => exact Or.inr (Or.inr (Or.inl ⟨t, u, Data.l.inj ht⟩))
    | mul t u => exact Or.inr (Or.inr (Or.inr ⟨t, u, Data.l.inj ht⟩))
  · rintro (⟨z, rfl⟩ | ⟨i, rfl⟩ | ⟨t, u, rfl⟩ | ⟨t, u, rfl⟩)
    · exact ⟨.const z, rfl⟩
    · exact ⟨.var i, rfl⟩
    · exact ⟨.add t u, rfl⟩
    · exact ⟨.mul t u, rfl⟩

theorem formula_image_l (xs : List Data) :
    (∃ p : Formula, Data.l xs = p.toData) ↔
      xs = [Codec.unary 0] ∨
      (∃ t : Term, xs = [Codec.unary 1, t.toData]) ∨
      (∃ t : Term, xs = [Codec.unary 2, t.toData]) ∨
      (∃ p : Formula, xs = [Codec.unary 3, p.toData]) ∨
      (∃ p q : Formula, xs = [Codec.unary 4, p.toData, q.toData]) ∨
      (∃ p q : Formula, xs = [Codec.unary 5, p.toData, q.toData]) := by
  constructor
  · rintro ⟨p, hp⟩
    cases p with
    | falsum => exact Or.inl (Data.l.inj hp)
    | eqZero t => exact Or.inr (Or.inl ⟨t, Data.l.inj hp⟩)
    | ltZero t => exact Or.inr (Or.inr (Or.inl ⟨t, Data.l.inj hp⟩))
    | not p => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨p, Data.l.inj hp⟩)))
    | and p q => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, q, Data.l.inj hp⟩))))
    | or p q => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨p, q, Data.l.inj hp⟩))))
  · rintro (rfl | ⟨t, rfl⟩ | ⟨t, rfl⟩ | ⟨p, rfl⟩ | ⟨p, q, rfl⟩ | ⟨p, q, rfl⟩)
    · exact ⟨.falsum, rfl⟩
    · exact ⟨.eqZero t, rfl⟩
    · exact ⟨.ltZero t, rfl⟩
    · exact ⟨.not p, rfl⟩
    · exact ⟨.and p q, rfl⟩
    · exact ⟨.or p q, rfl⟩

theorem classify_syntax_iff (d : Data) :
    ((classify d).term = true ↔ ∃ t : Term, d = t.toData) ∧
      ((classify d).formula = true ↔ ∃ p : Formula, d = p.toData) := by
  have key : ∀ (n : ℕ) (d : Data), d.size ≤ n →
      ((classify d).term = true ↔ ∃ t : Term, d = t.toData) ∧
        ((classify d).formula = true ↔ ∃ p : Formula, d = p.toData) := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
        rintro ⟨xs⟩ hn
        have ht : ∀ c ∈ xs, (classify c).term = true ↔ ∃ t : Term, c = t.toData := by
          intro c hc
          exact (ih c.size ((Data.size_lt_of_mem hc).trans_le hn) c le_rfl).1
        have hp : ∀ c ∈ xs, (classify c).formula = true ↔ ∃ p : Formula, c = p.toData := by
          intro c hc
          exact (ih c.size ((Data.size_lt_of_mem hc).trans_le hn) c le_rfl).2
        constructor
        · rw [classify, finish_summary, term_image_l]
          rcases xs with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨e, rest⟩⟩⟩⟩ <;>
            simp [direct, classify_tag_iff, classify_integer_iff, classify_unary_iff, ht]
          all_goals aesop
        · rw [classify, finish_summary, formula_image_l]
          rcases xs with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨e, rest⟩⟩⟩⟩ <;>
            simp [direct, classify_tag_iff, ht, hp]
          all_goals aesop
  exact key d.size d le_rfl

theorem classify_correct (d : Data) : Correct d (classify d) where
  count := classify_count d
  empty := classify_empty_iff d
  unary := classify_unary_iff d
  trueBit := classify_trueBit_iff d
  natural := classify_natural_iff d
  integer := classify_integer_iff d
  term := (classify_syntax_iff d).1
  formula := (classify_syntax_iff d).2

end LeanCanny.ETR.SyntaxClassifier
