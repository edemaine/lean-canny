/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FlatAffineExceptionalFramedIntegerPrelude
public import LeanCanny.Algebra.IntegralMixedFramedPrefixHeight
/-! # The actual finite integer bank satisfies the original height schedule

One original source/default bound and the established bank polynomial mass
bound imply every initial instruction bound. Later instructions are charged
at their actual births after the initial bank. The family construction does
not assume a bound for the complete interpreted bank or its coefficients.
-/
@[expose] public section
namespace LeanCanny.Encoding.FlatAffineExceptionalFramedPreludeBounds
open LeanCanny.Algebra LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript IntegralMixedFramedStepHeight
open IntegralMixedFramedHistoryFamilyBits (Plan)
open FlatAffineFullSourceTower (Inputs arity)
open FlatAffineCompleteRootStages (next)
open FlatAffineExceptionalBankSource (births width finitePolynomial massBound)
open FlatAffineExceptionalFramedIntegerPrelude (command commands plan)
open scoped Classical

noncomputable def seed (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (input : List Bool → List Bool)
    (original : List Bool → ℕ) (root : List Bool) : ℕ := original root+massBound F C h (input root)

theorem seed_binary {F : Inputs} (hF : F.Access) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (hh : UnaryFn (fun u => (h u).val))
    (input : List Bool → List Bool) (hi : input∈FP) (original : List Bool → ℕ) (ho : BinaryFn original) :
    BinaryFn (seed F C h input original) := ho.add ((FlatAffineExceptionalBankSource.massBound_binary hF C h hh).comp hi)

theorem mass_le_seed (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (input : List Bool → List Bool)
    (original : List Bool → ℕ) (root : List Bool) :
    massBound F C h (input root)≤seed F C h input original root := Nat.le_add_left _ _

theorem finite_coefficient (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (u : List Bool) (i : Fin (births F u)) (k : ℕ) :
    ((finitePolynomial F C h u i).coeff k).natAbs≤2^massBound F C h u := by
  have HM : coefficientMass (finitePolynomial F C h u i)≤2^massBound F C h u := by
    simpa only [finitePolynomial,pairFst_pair] using
      FlatAffineExceptionalBankSource.mass_le F C h (pair u (BinaryNatCode.encode i.val))
  exact (coeff_natAbs_le_coefficientMass _ k).trans HM

theorem instruction_bounds {n B G f W D L : ℕ} (Q : SpatialSource n)
    (hcap : PurePowerReductionBounds.dimension (n+1) Q.degree≤2^B)
    (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (u : List Bool) (hB : width F u≤B)
    (i : Fin (births F u))
    (hd : InstructionBounds G f W D L (⟨Q,hcap,IntegralMixedFullHistoryScript.defaultCommand⟩ : Instruction n B))
    (hm : massBound F C h u≤f*G+1) :
    InstructionBounds G f W D L (command Q B hcap F C h u hB i) where
  low := hd.low
  leading := hd.leading
  width := hd.width
  degree := hd.degree
  auxiliary := hd.auxiliary
  command := by
    intro k
    exact (finite_coefficient F C h u i k).trans (Nat.pow_le_pow_right (by decide) hm)

private theorem uniform_script {n S B W D L f C : ℕ} (cs : List (Instruction n B))
    (hc : ∀ c∈cs, InstructionBounds (C+1) f W D L c) : ScriptBounds S W D L f C cs := by
  induction cs with
  | nil => trivial
  | cons c cs ih =>
    refine ⟨ih (fun d hd => hc d (List.mem_cons_of_mem c hd)),?_⟩
    exact instruction_bounds_mono (source_le_height n S B W D L f C _) (hc c List.mem_cons_self)

theorem commands_bounds {n S B W D L f C₀ : ℕ} (Q : SpatialSource n)
    (hcap : PurePowerReductionBounds.dimension (n+1) Q.degree≤2^B)
    (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (u : List Bool) (hB : width F u≤B)
    (hd : InstructionBounds (C₀+1) f W D L (⟨Q,hcap,IntegralMixedFullHistoryScript.defaultCommand⟩ : Instruction n B))
    (hm : massBound F C h u≤f*(C₀+1)+1) :
    ScriptBounds S W D L f C₀ (commands Q B hcap F C h u hB) := by
  apply uniform_script
  intro c hc
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hc
  exact instruction_bounds Q hcap F C h u hB i hd hm

/-- Later bounds use the actual absolute birth after an already-created prefix. -/
def LaterBounds {n B : ℕ} (S W D L f C shift : ℕ) : List (Instruction n B) → Prop
  | [] => True
  | c::cs => LaterBounds S W D L f C shift cs ∧
      InstructionBounds (height n S B W D L f C (shift+cs.length)) f W D L c

theorem append_bounds {n S B W D L f C : ℕ} (later initial : List (Instruction n B))
    (hi : ScriptBounds S W D L f C initial)
    (hl : LaterBounds S W D L f C initial.length later) :
    ScriptBounds S W D L f C (later++initial) := by
  induction later with
  | nil => exact hi
  | cons c cs ih =>
    refine ⟨ih hl.1,?_⟩
    change InstructionBounds (height n S B W D L f C ((cs++initial).length)) f W D L c
    rw [List.length_append]
    simpa only [Nat.add_comm initial.length cs.length] using hl.2

theorem familyInputs (P : Parameters) (base : Plan P) (F : Inputs)
    (C : FlatAffinePowerPositive.ConeCertificate (next F)) (h : (u : List Bool) → Fin (arity F u))
    (input : List Bool → List Bool)
    (later : (root : List Bool) → List (Instruction (P.ambient root) (P.width root)))
    (hW : ∀ root, width F (input root)≤P.width root)
    (hroom : ∀ root, (later root).length+births F (input root)+2≤P.cap root+1)
    (L f C₀ : List Bool → ℕ)
    (hd : ∀ root, InstructionBounds (C₀ root+1) (f root) (P.sourceWidth root) (P.degree root) (L root)
      (IntegralMixedFramedHistoryFamilyBits.defaultInstruction P base root))
    (hm : ∀ root, massBound F C h (input root)≤f root*(C₀ root+1)+1)
    (hl : ∀ root, LaterBounds (P.cap root+1) (P.sourceWidth root) (P.degree root) (L root) (f root) (C₀ root)
      (births F (input root)) (later root)) :
    FamilyInputs P (plan P base F C h input later hW hroom) L f C₀ where
  default := hd
  script root := by
    apply append_bounds
    · exact commands_bounds _ _ F C h (input root) (hW root) (hd root) (hm root)
    · simpa only [FlatAffineExceptionalFramedIntegerPrelude.length_commands] using hl root

theorem familyInputs_seed (P : Parameters) (base : Plan P) (F : Inputs)
    (C : FlatAffinePowerPositive.ConeCertificate (next F)) (h : (u : List Bool) → Fin (arity F u))
    (input : List Bool → List Bool)
    (later : (root : List Bool) → List (Instruction (P.ambient root) (P.width root)))
    (hW : ∀ root, width F (input root)≤P.width root)
    (hroom : ∀ root, (later root).length+births F (input root)+2≤P.cap root+1)
    (L f original : List Bool → ℕ) (hf : ∀ root, 1≤f root)
    (hd : ∀ root, InstructionBounds (seed F C h input original root+1) (f root)
      (P.sourceWidth root) (P.degree root) (L root)
      (IntegralMixedFramedHistoryFamilyBits.defaultInstruction P base root))
    (hl : ∀ root, LaterBounds (P.cap root+1) (P.sourceWidth root) (P.degree root) (L root) (f root)
      (seed F C h input original root) (births F (input root)) (later root)) :
    FamilyInputs P (plan P base F C h input later hW hroom) L f (seed F C h input original) := by
  apply familyInputs P base F C h input later hW hroom L f _ hd _ hl
  intro root
  have HM := mass_le_seed F C h input original root
  have HF := hf root
  nlinarith

end LeanCanny.Encoding.FlatAffineExceptionalFramedPreludeBounds
