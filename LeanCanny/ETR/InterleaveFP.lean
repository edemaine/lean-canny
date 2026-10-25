/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.NNFFP
public import LeanCanny.ETR.EquationSize

/-! # Polynomial-time disjoint copies of real formulas

Even and odd variable names give independent copies of an assignment. Raw
integer payloads are retained at constants; their internal trees must never
be interpreted as variable occurrences. Separate term and formula transforms
also distinguish their overlapping constructor tags.
-/

@[expose] public section

namespace LeanCanny.ETR.Interleave
open LeanCanny.Encoding LeanCanny.Encoding.Brackets

@[local simp] theorem unary_eq_iff (i j : ℕ) : Codec.unary i = Codec.unary j ↔ i = j := by
  constructor
  · intro h
    have := congrArg Codec.readUnary h
    simpa using this
  · rintro rfl; rfl

def index (b : Bool) (i : ℕ) : ℕ := 2 * i + b.toNat

def termData (b : Bool) : Data → Data
  | .l [tag, a] =>
    if tag = Codec.unary 0 then .l [tag, a]
    else if tag = Codec.unary 1 then
      NNF.one 1 (Codec.unary (index b (Codec.unaryValue a.toBits)))
    else (Term.const 0).toData
  | .l [tag, a, c] =>
    if tag = Codec.unary 2 then NNF.two 2 (termData b a) (termData b c)
    else if tag = Codec.unary 3 then NNF.two 3 (termData b a) (termData b c)
    else (Term.const 0).toData
  | _ => (Term.const 0).toData

def formulaData (b : Bool) : Data → Data
  | .l [tag, a] =>
    if tag = Codec.unary 1 then NNF.one 1 (termData b a)
    else if tag = Codec.unary 2 then NNF.one 2 (termData b a)
    else if tag = Codec.unary 3 then NNF.one 3 (formulaData b a)
    else NNF.falseData
  | .l [tag, a, c] =>
    if tag = Codec.unary 4 then NNF.two 4 (formulaData b a) (formulaData b c)
    else if tag = Codec.unary 5 then NNF.two 5 (formulaData b a) (formulaData b c)
    else NNF.falseData
  | _ => NNF.falseData

theorem termData_term (b : Bool) (t : Term) :
    termData b t.toData = (t.rename (index b)).toData := by
  induction t <;> simp_all [termData, Term.toData, Term.rename, NNF.one, NNF.two]

theorem formulaData_formula (b : Bool) (p : Formula) :
    formulaData b p.toData = (p.rename (index b)).toData := by
  induction p <;> simp_all [formulaData, Formula.toData, Formula.rename,
    termData_term, NNF.one, NNF.two, NNF.falseData]

theorem termData_size (b : Bool) (d : Data) : (termData b d).size ≤ 10 * d.size := by
  induction d using Data.inductionChildren with
  | node xs ih =>
    have hpos := @Data.size_pos (.l xs)
    rcases xs with _ | ⟨tag, _ | ⟨a, _ | ⟨c, _ | ⟨e, rest⟩⟩⟩⟩
    · simp [termData, Term.dataSize_const_zero]
    · simp only [termData, Term.dataSize_const_zero]; omega
    · have hv : Codec.unaryValue a.toBits ≤ a.size := by
        simp only [Codec.unaryValue, Data.length_toBits]
        exact (Nat.div_le_self _ _).trans (Nat.sub_le _ _)
      have hb : b.toNat ≤ 1 := by cases b <;> decide
      simp only [termData]
      split
      · simp only [Data.cons_size, Data.size_empty]; omega
      · split
        · simp only [NNF.one_size, Codec.unary_size, index, Data.cons_size, Data.size_empty]
          omega
        · simp only [Term.dataSize_const_zero]; omega
    · have ha := ih a (by simp)
      have hc := ih c (by simp)
      have ht := @Data.size_pos tag
      simp only [termData]
      split
      · simp only [NNF.two_size, Data.cons_size, Data.size_empty] at *; omega
      · split
        · simp only [NNF.two_size, Data.cons_size, Data.size_empty] at *; omega
        · simp only [Term.dataSize_const_zero]; omega
    · simp only [termData, Term.dataSize_const_zero]; omega

theorem formulaData_size (b : Bool) (d : Data) : (formulaData b d).size ≤ 20 * d.size := by
  induction d using Data.inductionChildren with
  | node xs ih =>
    have hpos := @Data.size_pos (.l xs)
    rcases xs with _ | ⟨tag, _ | ⟨a, _ | ⟨c, _ | ⟨e, rest⟩⟩⟩⟩
    · simp [formulaData]
    · simp only [formulaData, NNF.falseData_size]; omega
    · have ha := ih a (by simp)
      have ht := termData_size b a
      simp only [formulaData]
      split
      · simp only [NNF.one_size, Data.cons_size, Data.size_empty] at *; omega
      · split
        · simp only [NNF.one_size, Data.cons_size, Data.size_empty] at *; omega
        · split
          · simp only [NNF.one_size, Data.cons_size, Data.size_empty] at *; omega
          · simp only [NNF.falseData_size]; omega
    · have ha := ih a (by simp)
      have hc := ih c (by simp)
      have ht := @Data.size_pos tag
      simp only [formulaData]
      split
      · simp only [NNF.two_size, Data.cons_size, Data.size_empty] at *; omega
      · split
        · simp only [NNF.two_size, Data.cons_size, Data.size_empty] at *; omega
        · simp only [NNF.falseData_size]; omega
    · simp only [formulaData, NNF.falseData_size]; omega

def code (b : Bool) (xs : List Data) : List Bool :=
  pair (Data.l xs).toBits
    (pair (Data.l (xs.map (termData b))).toBits (Data.l (xs.map (formulaData b))).toBits)

def raw (frame : List Bool) : List Bool := pairFst frame
def terms (frame : List Bool) : List Bool := pairFst (pairSnd frame)
def formulas (frame : List Bool) : List Bool := pairSnd (pairSnd frame)

theorem raw_mem_FP : raw ∈ FP := pairFst_mem_FP
theorem terms_mem_FP : terms ∈ FP := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
theorem formulas_mem_FP : formulas ∈ FP := mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP

attribute [local irreducible] NNF.second NNF.third raw terms formulas

def finishTerm (b : Bool) (frame : List Bool) : List Bool :=
  if NNF.HasOne 0 (raw frame) then raw frame
  else if NNF.HasOne 1 (raw frame) then
    Term.variableBits (index b (Codec.unaryValue (NNF.second (raw frame))))
  else if NNF.HasTwo 2 (raw frame) then
    Codec.taggedTwo 2 (NNF.second (terms frame)) (NNF.third (terms frame))
  else if NNF.HasTwo 3 (raw frame) then
    Codec.taggedTwo 3 (NNF.second (terms frame)) (NNF.third (terms frame))
  else (Term.const 0).toData.toBits

def finishFormula (frame : List Bool) : List Bool :=
  if NNF.HasOne 1 (raw frame) then Codec.taggedOne 1 (NNF.second (terms frame))
  else if NNF.HasOne 2 (raw frame) then Codec.taggedOne 2 (NNF.second (terms frame))
  else if NNF.HasOne 3 (raw frame) then Codec.taggedOne 3 (NNF.second (formulas frame))
  else if NNF.HasTwo 4 (raw frame) then
    Codec.taggedTwo 4 (NNF.second (formulas frame)) (NNF.third (formulas frame))
  else if NNF.HasTwo 5 (raw frame) then
    Codec.taggedTwo 5 (NNF.second (formulas frame)) (NNF.third (formulas frame))
  else Formula.falsum.encode

theorem finishTerm_mem_FP (b : Bool) : finishTerm b ∈ FP := by
  have hu : UnaryFn (fun f => Codec.unaryValue (NNF.second (raw f))) := Codec.unaryValue_unary.comp (mem_FP_comp raw_mem_FP NNF.second_mem_FP)
  have hv : (fun f => Term.variableBits (index b (Codec.unaryValue (NNF.second (raw f))))) ∈ FP := Term.variableBits_mem_FP (((UnaryFn.const 2).mul hu).add (UnaryFn.const b.toNat))
  have hs : (fun f => NNF.second (terms f)) ∈ FP := mem_FP_comp terms_mem_FP NNF.second_mem_FP
  have ht : (fun f => NNF.third (terms f)) ∈ FP := mem_FP_comp terms_mem_FP NNF.third_mem_FP
  have h := ((NNF.hasOne_fppred 0).comp raw_mem_FP).ite_mem_FP raw_mem_FP
    (((NNF.hasOne_fppred 1).comp raw_mem_FP).ite_mem_FP hv
      (((NNF.hasTwo_fppred 2).comp raw_mem_FP).ite_mem_FP (Codec.taggedTwo_mem_FP 2 hs ht)
        (((NNF.hasTwo_fppred 3).comp raw_mem_FP).ite_mem_FP (Codec.taggedTwo_mem_FP 3 hs ht)
          (constFn_mem_FP (Term.const 0).toData.toBits))))
  exact mem_FP_of_eq h (fun frame => by simp only [finishTerm, index])

theorem finishFormula_mem_FP : finishFormula ∈ FP := by
  have ht : (fun f => NNF.second (terms f)) ∈ FP := mem_FP_comp terms_mem_FP NNF.second_mem_FP
  have hp : (fun f => NNF.second (formulas f)) ∈ FP := mem_FP_comp formulas_mem_FP NNF.second_mem_FP
  have hq : (fun f => NNF.third (formulas f)) ∈ FP := mem_FP_comp formulas_mem_FP NNF.third_mem_FP
  have h := ((NNF.hasOne_fppred 1).comp raw_mem_FP).ite_mem_FP (Codec.taggedOne_mem_FP 1 ht)
    (((NNF.hasOne_fppred 2).comp raw_mem_FP).ite_mem_FP (Codec.taggedOne_mem_FP 2 ht)
      (((NNF.hasOne_fppred 3).comp raw_mem_FP).ite_mem_FP (Codec.taggedOne_mem_FP 3 hp)
        (((NNF.hasTwo_fppred 4).comp raw_mem_FP).ite_mem_FP (Codec.taggedTwo_mem_FP 4 hp hq)
          (((NNF.hasTwo_fppred 5).comp raw_mem_FP).ite_mem_FP (Codec.taggedTwo_mem_FP 5 hp hq)
            (constFn_mem_FP Formula.falsum.encode)))))
  exact mem_FP_of_eq h (fun frame => by simp only [finishFormula])

theorem finishTerm_code (b : Bool) (xs : List Data) :
    finishTerm b (code b xs) = (termData b (.l xs)).toBits := by
  rcases xs with _ | ⟨tag, _ | ⟨a, _ | ⟨c, _ | ⟨e, rest⟩⟩⟩⟩ <;>
    simp [finishTerm, code, raw, terms, NNF.hasOne_toBits, NNF.hasTwo_toBits,
      NNF.one, NNF.two, NNF.second, NNF.third, firstChild_toBits, remainingChildren_toBits,
      termData, Term.variableBits, Codec.taggedOne_toBits, Codec.taggedTwo_toBits]
  all_goals split_ifs <;> rfl

theorem finishFormula_code (b : Bool) (xs : List Data) :
    finishFormula (code b xs) = (formulaData b (.l xs)).toBits := by
  rcases xs with _ | ⟨tag, _ | ⟨a, _ | ⟨c, _ | ⟨e, rest⟩⟩⟩⟩ <;>
    simp [finishFormula, code, raw, terms, formulas, NNF.hasOne_toBits, NNF.hasTwo_toBits,
      NNF.one, NNF.two, NNF.second, NNF.third, firstChild_toBits, remainingChildren_toBits,
      formulaData, Formula.encode, NNF.falseData, Codec.taggedOne_toBits, Codec.taggedTwo_toBits]
  all_goals split_ifs <;> rfl

def combineBits (b : Bool) (packet : List Bool) : List Bool :=
  let child := pairFst (pairSnd packet)
  let parent := pairSnd (pairSnd packet)
  pair (consNode (raw child) (raw parent))
    (pair (consNode (finishTerm b child) (terms parent))
      (consNode (finishFormula child) (formulas parent)))

theorem combineBits_mem_FP (b : Bool) : combineBits b ∈ FP := by
  have hc : (fun z => pairFst (pairSnd z)) ∈ FP := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
  have hp : (fun z => pairSnd (pairSnd z)) ∈ FP := mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP
  have hrc := mem_FP_comp hc raw_mem_FP
  have hrp := mem_FP_comp hp raw_mem_FP
  have htc := mem_FP_comp hc (finishTerm_mem_FP b)
  have htp := mem_FP_comp hp terms_mem_FP
  have hfc := mem_FP_comp hc finishFormula_mem_FP
  have hfp := mem_FP_comp hp formulas_mem_FP
  unfold combineBits
  exact mem_FP_pair (consNode_mem_FP hrc hrp)
    (mem_FP_pair (consNode_mem_FP htc htp) (consNode_mem_FP hfc hfp))

theorem combineBits_code (b : Bool) (z : List Bool) (child parent : List Data) :
    combineBits b (pair z (pair (code b child) (code b parent))) =
      code b (NNF.combine child parent) := by
  simp only [combineBits, pairFst_pair, pairSnd_pair, finishTerm_code, finishFormula_code]
  simp only [code, raw, terms, formulas, NNF.combine, pairFst_pair, pairSnd_pair,
    List.map_cons, consNode_toBits]

theorem code_length_le (b : Bool) (xs : List Data) : (code b xs).length ≤ 100 * (Data.l xs).size := by
  have ht : (Data.l (xs.map (termData b))).size ≤ 10 * (Data.l xs).size := by
    induction xs with
    | nil => simp [Data.size_empty]
    | cons d ds ih =>
      have := termData_size b d
      simp only [List.map_cons, Data.cons_size] at *; omega
  have hf : (Data.l (xs.map (formulaData b))).size ≤ 20 * (Data.l xs).size := by
    clear ht
    induction xs with
    | nil => simp [Data.size_empty]
    | cons d ds ih =>
      have := formulaData_size b d
      simp only [List.map_cons, Data.cons_size] at *; omega
  have hp := @Data.size_pos (.l xs)
  simp only [code, pair_length, Data.length_toBits]
  omega

theorem run_code_mem_FP (b : Bool) :
    (fun bits => DynamicTreeFold.encode (code b) (TreeFold.run [] NNF.combine bits)) ∈ FP := by
  have hg : ∀ child parent : List Data, (NNF.reference (NNF.combine child parent)).length ≤
      (NNF.reference child).length + (NNF.reference parent).length + 0 := by
    intro child parent
    simp [NNF.reference, NNF.combine, Data.cons_size]
  refine DynamicTreeFold.runEncoded_mem_FP (fun _ => []) (fun _ => NNF.combine) (code b)
    (fun _ => code b []) (combineBits b) (constFn_mem_FP _) (combineBits_mem_FP b)
    (fun _ => rfl) (combineBits_code b)
    ((PolyBound.const 1000).add ((PolyBound.const 1000).mul PolyBound.id)) ?_
  intro z t ht
  have hc := DynamicTreeFold.encode_length_le_mul (code b) NNF.reference 100 (by decide)
    (fun xs => by simpa only [NNF.reference, List.length_replicate] using code_length_le b xs)
    (TreeFold.run [] NNF.combine t)
  have hr := DynamicTreeFold.run_encode_length_le ([] : List Data) NNF.combine NNF.reference 0 hg t
  simp only [NNF.reference, List.length_replicate, Data.size_empty] at hr
  have hh := hc.trans (Nat.mul_le_mul_left 100 hr)
  have hl := ht.length_le
  omega

def transform (b : Bool) (bits : List Bool) : List Bool :=
  firstChild (formulas (pairFst
    ((DynamicTreeFold.encode (code b) (TreeFold.run [] NNF.combine bits)).drop 1)))

theorem transform_mem_FP (b : Bool) : transform b ∈ FP := by
  have hd := drop_mem_FP (run_code_mem_FP b) (UnaryFn.const 1)
  have hf : (fun bits => pairFst ((DynamicTreeFold.encode (code b)
      (TreeFold.run [] NNF.combine bits)).drop 1)) ∈ FP := mem_FP_comp hd pairFst_mem_FP
  have hp : (fun bits => formulas (pairFst ((DynamicTreeFold.encode (code b)
      (TreeFold.run [] NNF.combine bits)).drop 1))) ∈ FP := mem_FP_comp hf formulas_mem_FP
  exact mem_FP_comp hp firstChild_mem_FP

theorem transform_toBits (b : Bool) (d : Data) : transform b d.toBits = (formulaData b d).toBits := by
  simp [transform, TreeFold.run_toBits, NNF.foldData_identity, NNF.combine,
    DynamicTreeFold.encode, DynamicTreeFold.stackBits, code, formulas]

/-- Malformed words become falsum; on a formula this writes its disjoint copy. -/
def renameBits (b : Bool) (bits : List Bool) : List Bool :=
  if Grammar.recognizeFormula bits then transform b bits else Formula.falsum.encode

theorem renameBits_mem_FP (b : Bool) : renameBits b ∈ FP :=
  (FPPred.of_flag Grammar.recognizeFormula_mem_FP).ite_mem_FP
    (transform_mem_FP b) (constFn_mem_FP _)

theorem renameBits_encode (b : Bool) (p : Formula) :
    renameBits b p.encode = (p.rename (index b)).encode := by
  rw [renameBits, Grammar.recognizeFormula_encode, ite_eq_left rfl]
  exact (transform_toBits b p.toData).trans (congrArg Data.toBits (formulaData_formula b p))

end LeanCanny.ETR.Interleave
