/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.CoefficientMarkedRecordBirthSpecialization
public import LeanCanny.Algebra.CoefficientHistoryPrefixSpecialization

/-! # The actual dependent record step preserves prefix specialization

The local quotient maps carry full rows and slots through the literal native
step. Explicit index equalities account for the interpreter's Boolean casts.
-/

@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordSpecialization
universe u
open LeanCanny.Algebra LeanCanny.Computation IntegralMixedHistory Polynomial
open CoefficientMarkedRecordBirthSpecialization
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)
  (ctx : List Bool) (radius : List Bool → ℕ) {S m : ℕ} {ι : Type} [Fintype ι]
  (F : CoefficientHistoryPrefix.Prefix ℤ[X] S (CoefficientMarkedIntegerBirth.width hn ht ha ctx) m ι)
  (x : State (CoefficientMarkedRecordNative.source (n := n) (t := t) ctx radius)
    S (CoefficientMarkedIntegerBirth.width hn ht ha ctx) m ι) (hm : m ≤ S)

theorem critical_next
    (h : CoefficientHistoryPrefix.Specializes (radius ctx) F x) (code : List Bool)
    (hc : IntegralMixedUnitRecordCode.critical code = true) :
    CoefficientHistoryPrefix.Specializes (radius ctx) (criticalPrefix hn ht ha ctx F code)
      (CoefficientMarkedRecordNative.next hn ht ha ctx radius x hm code) := by
  obtain ⟨ψ, hb, hg, hr, hs⟩ := h.pointwise
  obtain ⟨φ, hb', hg', hr', hs'⟩ := critical_specializes hn ht ha ctx radius F x hm ψ hg hb hr hs code
  have hh := CoefficientHistoryPrefix.specializes_of_pointwise (radius ctx)
    (criticalPrefix hn ht ha ctx F code)
    (criticalStep x hm (IntegralMixedCausalUnitRecordBits.physical
      (IntegralMixedAuxiliaryMarkedIntegerSource.number n ctx + 3) m code)) φ hb' hg' hr' hs'
  apply hh.state_transport _ (critical_next_heq hn ht ha ctx radius x hm code hc)
  exact (ite_eq_left hc).symm

theorem cut_next
    (h : CoefficientHistoryPrefix.Specializes (radius ctx) F x) (code : List Bool)
    (hc : IntegralMixedUnitRecordCode.critical code ≠ true) (entryBits : ℕ)
    (HE : let c := CoefficientMarkedRecordPrefix.cut hn ht ha ctx m code
      ∀ i j, coefficientMass (Algebra.leftMulMatrix F.basis.basis
        ((CoefficientMixedCutSpecialization.raw F.bank
          (CoefficientMarkedRecordPrefix.low (n := n) (t := t) ctx)
          (CoefficientMarkedRecordPrefix.leading (n := n) (t := t) ctx)
          (c.rule 1 one_ne_zero) c.current (c.kind 1 one_ne_zero) c.degree).coeff c.degree) i j) ≤ 2 ^ entryBits)
    (HR : ParameterMatrixMassBounds.characteristicBudget
      ((2 ^ CoefficientMarkedIntegerBirth.width hn ht ha ctx) ^ m) entryBits + 1 ≤ radius ctx) :
    CoefficientHistoryPrefix.Specializes (radius ctx) (cutPrefix hn ht ha ctx F code)
      (CoefficientMarkedRecordNative.next hn ht ha ctx radius x hm code) := by
  obtain ⟨ψ, hb, hg, hr, hs⟩ := h.pointwise
  obtain ⟨φ, hb', hg', hr', hs'⟩ := cut_specializes hn ht ha ctx radius F x hm ψ hg hb hr hs code entryBits HE HR
  have hh := CoefficientHistoryPrefix.specializes_of_pointwise (radius ctx)
    (cutPrefix hn ht ha ctx F code) (nativeCut hn ht ha ctx radius x hm code) φ hb' hg' hr' hs'
  apply hh.state_transport _ (cut_next_heq hn ht ha ctx radius x hm code hc)
  exact (ite_eq_right hc).symm

private theorem boolRec_true {A : Sort u} (b : Bool) (f : b = false → A) (g : b = true → A)
    (h : b = true) : Bool.rec (motive := fun v => b = v → A) f g b rfl = g h := by
  cases h
  rfl

private theorem boolRec_false {A : Sort u} (b : Bool) (f : b = false → A) (g : b = true → A)
    (h : b = false) : Bool.rec (motive := fun v => b = v → A) f g b rfl = f h := by
  cases h
  rfl

private theorem recEqApp {A : Sort u} {b c : Bool} (h : b = c) (f : b = c → A) :
    Eq.rec (motive := fun x _ => b = x → A) f h.symm rfl = f h := by
  cases h
  rfl

private theorem mpr_heq {A B : Sort u} (h : A = B) (x : B) : HEq (h.mpr x) x := by
  cases h
  rfl

theorem critical_build_heq (S : ℕ) (cs : List (List Bool)) (code : List Bool)
    (hc : IntegralMixedUnitRecordCode.critical code = true) :
    HEq (criticalPrefix hn ht ha ctx (CoefficientMarkedRecordPrefix.build hn ht ha ctx S cs) code)
      (CoefficientMarkedRecordPrefix.build hn ht ha ctx S (code :: cs)) := by
  simp only [criticalPrefix, CoefficientMarkedRecordPrefix.build]
  rw [boolRec_true _ _ _ hc]
  rw [recEqApp hc]
  exact (mpr_heq _ _).symm

theorem cut_build_heq (S : ℕ) (cs : List (List Bool)) (code : List Bool)
    (hc : IntegralMixedUnitRecordCode.critical code = false) :
    HEq (cutPrefix hn ht ha ctx (CoefficientMarkedRecordPrefix.build hn ht ha ctx S cs) code)
      (CoefficientMarkedRecordPrefix.build hn ht ha ctx S (code :: cs)) := by
  simp only [cutPrefix, CoefficientMarkedRecordPrefix.build]
  rw [boolRec_false _ _ _ hc]
  rw [recEqApp hc]
  exact (mpr_heq _ _).symm

noncomputable def topMatrix (code : List Bool) :=
  let c := CoefficientMarkedRecordPrefix.cut hn ht ha ctx m code
  Algebra.leftMulMatrix F.basis.basis
    ((CoefficientMixedCutSpecialization.raw F.bank
      (CoefficientMarkedRecordPrefix.low (n := n) (t := t) ctx)
      (CoefficientMarkedRecordPrefix.leading (n := n) (t := t) ctx)
      (c.rule 1 one_ne_zero) c.current (c.kind 1 one_ne_zero) c.degree).coeff c.degree)

def topEntryBound (code : List Bool) (bits : ℕ) : Prop :=
  ∀ i j, coefficientMass (topMatrix hn ht ha ctx F code i j) ≤ 2 ^ bits

theorem critical_cons (S : ℕ) (cs : List (List Bool)) (code : List Bool)
    (hroom : (CoefficientMarkedPreludeActual.indices n ctx).length + (code :: cs).length ≤ S + 1)
    (hprev : CoefficientHistoryPrefix.Specializes (radius ctx)
      (CoefficientMarkedRecordPrefix.build hn ht ha ctx S cs)
      (CoefficientMarkedRecordNative.run hn ht ha ctx radius S cs ((Nat.le_succ _).trans hroom)))
    (hc : IntegralMixedUnitRecordCode.critical code = true) :
    CoefficientHistoryPrefix.Specializes (radius ctx)
      (CoefficientMarkedRecordPrefix.build hn ht ha ctx S (code :: cs))
      (CoefficientMarkedRecordNative.run hn ht ha ctx radius S (code :: cs) hroom) := by
  have ht0 : (CoefficientMarkedPreludeActual.indices n ctx).length + cs.length ≤ S + 1 :=
    (Nat.le_succ _).trans hroom
  have hm : (CoefficientMarkedPreludeActual.indices n ctx).length + cs.length ≤ S :=
    Nat.succ_le_succ_iff.mp hroom
  let F := CoefficientMarkedRecordPrefix.build hn ht ha ctx S cs
  let x := CoefficientMarkedRecordNative.run hn ht ha ctx radius S cs ht0
  have hh := critical_next hn ht ha ctx radius F x hm hprev code hc
  apply hh.prefix_transport _ (critical_build_heq hn ht ha ctx S cs code hc)
  exact (ite_eq_left hc).symm

theorem cut_cons (S : ℕ) (cs : List (List Bool)) (code : List Bool)
    (hroom : (CoefficientMarkedPreludeActual.indices n ctx).length + (code :: cs).length ≤ S + 1)
    (hprev : CoefficientHistoryPrefix.Specializes (radius ctx)
      (CoefficientMarkedRecordPrefix.build hn ht ha ctx S cs)
      (CoefficientMarkedRecordNative.run hn ht ha ctx radius S cs ((Nat.le_succ _).trans hroom)))
    (hc : IntegralMixedUnitRecordCode.critical code = false) (bits : ℕ)
    (HE : topEntryBound hn ht ha ctx (CoefficientMarkedRecordPrefix.build hn ht ha ctx S cs) code bits)
    (HR : ParameterMatrixMassBounds.characteristicBudget
      ((2 ^ CoefficientMarkedIntegerBirth.width hn ht ha ctx) ^
        ((CoefficientMarkedPreludeActual.indices n ctx).length + cs.length)) bits + 1 ≤ radius ctx) :
    CoefficientHistoryPrefix.Specializes (radius ctx)
      (CoefficientMarkedRecordPrefix.build hn ht ha ctx S (code :: cs))
      (CoefficientMarkedRecordNative.run hn ht ha ctx radius S (code :: cs) hroom) := by
  have ht0 : (CoefficientMarkedPreludeActual.indices n ctx).length + cs.length ≤ S + 1 :=
    (Nat.le_succ _).trans hroom
  have hm : (CoefficientMarkedPreludeActual.indices n ctx).length + cs.length ≤ S :=
    Nat.succ_le_succ_iff.mp hroom
  let F := CoefficientMarkedRecordPrefix.build hn ht ha ctx S cs
  let x := CoefficientMarkedRecordNative.run hn ht ha ctx radius S cs ht0
  have hc' : IntegralMixedUnitRecordCode.critical code ≠ true := by rw [hc]; decide
  have hh := cut_next hn ht ha ctx radius F x hm hprev code hc' bits HE HR
  apply hh.prefix_transport _ (cut_build_heq hn ht ha ctx S cs code hc)
  exact (ite_eq_right hc').symm

noncomputable def matrixMass {δ : Type*} [Fintype δ] (M : Matrix δ δ ℤ[X]) : ℕ :=
  Finset.univ.sup (fun ij : δ × δ => coefficientMass (M ij.1 ij.2))

private theorem matrix_entry_bound {δ : Type*} [Fintype δ] (M : Matrix δ δ ℤ[X]) (i j : δ) :
    coefficientMass (M i j) ≤ 2 ^ (matrixMass M).size :=
  (Finset.le_sup (f := fun ij : δ × δ => coefficientMass (M ij.1 ij.2)) (Finset.mem_univ (i, j))).trans
    (Nat.lt_size_self _).le

private theorem matrix_mass_le {δ : Type*} [Fintype δ] (M : Matrix δ δ ℤ[X]) (B : ℕ)
    (h : ∀ i j, coefficientMass (M i j) ≤ 2 ^ B) : matrixMass M ≤ 2 ^ B := by
  apply Finset.sup_le
  intro ij _
  exact h ij.1 ij.2

noncomputable def entryMass (code : List Bool) : ℕ := matrixMass (topMatrix hn ht ha ctx F code)

noncomputable def entryBits (code : List Bool) : ℕ := (entryMass hn ht ha ctx F code).size

omit [Fintype ι] in
theorem topEntryBound_entryBits (code : List Bool) :
    topEntryBound hn ht ha ctx F code (entryBits hn ht ha ctx F code) := by
  intro i j
  exact matrix_entry_bound (topMatrix hn ht ha ctx F code) i j

omit [Fintype ι] in
theorem entryBits_le (code : List Bool) (B : ℕ) (h : topEntryBound hn ht ha ctx F code B) :
    entryBits hn ht ha ctx F code ≤ B + 1 := by
  have hm : entryMass hn ht ha ctx F code ≤ 2 ^ B := by
    exact matrix_mass_le (topMatrix hn ht ha ctx F code) B h
  exact (Nat.size_le_size hm).trans_eq Nat.size_pow

noncomputable def cutoff (ctx : List Bool) (S : ℕ) : List (List Bool) → ℕ
  | [] => 0
  | code :: cs => if IntegralMixedUnitRecordCode.critical code then cutoff ctx S cs else
      max (cutoff ctx S cs) (ParameterMatrixMassBounds.characteristicBudget
        ((2 ^ CoefficientMarkedIntegerBirth.width hn ht ha ctx) ^
          ((CoefficientMarkedPreludeActual.indices n ctx).length + cs.length))
        (entryBits hn ht ha ctx (CoefficientMarkedRecordPrefix.build hn ht ha ctx S cs) code) + 1)

/-- The complete constructed record prefix specializes above a radius-independent
cutoff. Original-only complexity bounds for this cutoff are a separate theorem. -/
theorem specializes (S : ℕ) (cs : List (List Bool)) :
    ∀ hroom : (CoefficientMarkedPreludeActual.indices n ctx).length + cs.length ≤ S + 1,
    cutoff hn ht ha ctx S cs ≤ radius ctx →
    CoefficientHistoryPrefix.Specializes (radius ctx)
      (CoefficientMarkedRecordPrefix.build hn ht ha ctx S cs)
      (CoefficientMarkedRecordNative.run hn ht ha ctx radius S cs hroom) := by
  induction cs with
  | nil =>
    intro hroom _
    have ht0 : (CoefficientMarkedPreludeActual.indices n ctx).length ≤ S + 1 := by
      simpa only [List.length_nil, Nat.add_zero] using hroom
    obtain ⟨ψ, hb, hg, hr, hs⟩ := CoefficientMarkedPreludePrefix.specializes hn ht ha ctx radius S
      (CoefficientMarkedPreludeActual.indices n ctx) ht0
    exact CoefficientHistoryPrefix.specializes_of_pointwise (radius ctx) _ _ ψ hb hg hr hs
  | cons code cs ih =>
    intro hroom hR
    have ht0 : (CoefficientMarkedPreludeActual.indices n ctx).length + cs.length ≤ S + 1 := by
      simp only [List.length_cons] at hroom; omega
    by_cases hc : IntegralMixedUnitRecordCode.critical code = true
    · have htail : cutoff hn ht ha ctx S cs ≤ radius ctx := by
        simpa only [cutoff, hc, ite_true] using hR
      exact critical_cons hn ht ha ctx radius S cs code hroom (ih ht0 htail) hc
    · have hf := Bool.eq_false_of_not_eq_true hc
      have hmax : max (cutoff hn ht ha ctx S cs) (ParameterMatrixMassBounds.characteristicBudget
          ((2 ^ CoefficientMarkedIntegerBirth.width hn ht ha ctx) ^
            ((CoefficientMarkedPreludeActual.indices n ctx).length + cs.length))
          (entryBits hn ht ha ctx (CoefficientMarkedRecordPrefix.build hn ht ha ctx S cs) code) + 1) ≤ radius ctx := by
        simpa only [cutoff, hf, Bool.false_eq_true, ite_false] using hR
      exact cut_cons hn ht ha ctx radius S cs code hroom (ih ht0 ((le_max_left _ _).trans hmax)) hf _
        (topEntryBound_entryBits hn ht ha ctx _ code) ((le_max_right _ _).trans hmax)

end LeanCanny.Encoding.CoefficientMarkedRecordSpecialization
