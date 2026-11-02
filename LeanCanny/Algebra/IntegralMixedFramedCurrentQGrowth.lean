/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedPrefixHeight
public import LeanCanny.Algebra.IntegralMixedExpressionBounds
/-! # Current-denominator slopes fit an original-only causal height schedule

The denominator has at most birth times old-bank height bits. A fixed original
factor above the horizon absorbs this cost. Actual suffix bank bounds are proved
inductively, rather than supplied as per-prefix input assumptions.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedCurrentQGrowth
open LeanCanny.Encoding LeanCanny.Computation IntegralMixedHistory IntegralMixedFramedHistoryScript
open IntegralMixedFramedStepHeight
open scoped Classical

variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type}

theorem denominator_size (x : State P S B m ι) (G : ℕ) (HG : x.bank.Bounds G) :
    (commonDenominator x).natAbs.size≤m*G+1 := by
  simpa only [Nat.size_pow] using Nat.size_le_size (commonDenominator_height x G HG)

theorem denominator_budget (x : State P S B m ι) (G F : ℕ) (HG : x.bank.Bounds G) (hm : m≤F) :
    (commonDenominator x).natAbs.size≤F*G+1 :=
  (denominator_size x G HG).trans (Nat.add_le_add_right (Nat.mul_le_mul_right G hm) 1)

def CommandCore {n B : ℕ} {P : SpatialSource n} (C L : ℕ) : IntegralMixedFullHistoryScript.Command P B → Prop
  | .integer p _ _ => ∀ k,(p.coeff k).natAbs≤2^C
  | .critical r => (∀ i,(r.heights i).nodes≤L) ∧ (∀ i,(r.heights i).CoefficientsBound C) ∧
      (∀ i,(r.scales i).natAbs.size≤C)
  | .cut r _ _ _ _ => (∀ i,(r.critical.heights i).nodes≤L) ∧ (∀ i,(r.critical.heights i).CoefficientsBound C) ∧
      (∀ i,(r.critical.scales i).natAbs.size≤C)

structure OriginalInstruction {n B : ℕ} (G F W D L : ℕ) (c : Instruction n B) : Prop where
  low : ∀ e,(c.source.low.coeff e).natAbs≤2^(F*G+1)
  leading : c.source.leading.natAbs.size≤F*G+1
  width : c.source.degree.size≤W
  degree : c.source.degree≤D
  auxiliary : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) c.source.degree≤2^B
  command : CommandCore (F*G+1) L c.command

def SlopePolicy (x : State P S B m ι) (G F : ℕ) (c : Instruction n B) : Prop :=
  match c.command with
  | .cut r _ _ _ _ => r.slope=commonDenominator x ∨ r.slope.natAbs.size≤F*G+1
  | _ => True

theorem instruction_bounds (x : State P S B m ι) (G F W D L : ℕ) (c : Instruction n B)
    (HG : x.bank.Bounds G) (hm : m≤F) (hc : OriginalInstruction G F W D L c) (hs : SlopePolicy x G F c) :
    InstructionBounds G F W D L c := by
  refine ⟨hc.low,hc.leading,hc.width,hc.degree,hc.auxiliary,?_⟩
  have HB := hc.command
  cases he : c.command with
  | integer p hp hd => simpa only [he,CommandCore,IntegralMixedFullScriptHeight.CommandBounds] using HB
  | critical r => simpa only [he,CommandCore,IntegralMixedFullScriptHeight.CommandBounds] using HB
  | cut r k d ha hd =>
    simp only [SlopePolicy,he] at hs
    simp only [he,CommandCore] at HB
    refine ⟨HB.1,HB.2.1,HB.2.2,?_⟩
    rcases hs with hs | hs
    · rw [hs]
      exact denominator_budget x G F HG hm
    · exact hs

/-- A syntax specification mentions actual earlier Q only as a literal slope
identity. Its coefficient/degree bounds exclude that slope. -/
def CausalBounds {n S B : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
    (initial : State P S B 0 ι) (W D L F C : ℕ) :
    (cs : List (Instruction n B)) → cs.length≤S+1 → Prop
  | [],_ => True
  | c::cs,h => CausalBounds initial W D L F C cs (by simp only [List.length_cons] at h; omega) ∧
      OriginalInstruction (height n S B W D L F C cs.length) F W D L c ∧
      SlopePolicy (run initial cs (by simp only [List.length_cons] at h; omega))
        (height n S B W D L F C cs.length) F c

theorem script_bounds {n S B : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
    (initial : State P S B 0 ι) (W D L F C : ℕ) (hF : S≤F)
    (cs : List (Instruction n B)) (hcs : cs.length≤S+1) (hc : CausalBounds initial W D L F C cs hcs) :
    ScriptBounds S W D L F C cs := by
  induction cs with
  | nil => trivial
  | cons c cs ih =>
    have ht : cs.length≤S+1 := by simp only [List.length_cons] at hcs; omega
    have hm : cs.length≤F := by simp only [List.length_cons] at hcs; omega
    have HB := ih ht hc.1
    refine ⟨HB,?_⟩
    exact instruction_bounds (run initial cs ht) (height n S B W D L F C cs.length) F W D L c
      (run_bounds initial cs ht W D L F C HB) hm hc.2.1 hc.2.2

open IntegralCriticalHistoryTask in
theorem rules_bound (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (root : List Bool) :
    (D.rules root).length≤(P.cap root+1)+1 := by
  have H := D.room root
  omega

open IntegralCriticalHistoryTask in
theorem family_inputs (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (L F C : List Bool → ℕ)
    (hF : ∀ root,P.cap root+1≤F root)
    (hc : ∀ root,CausalBounds (IntegralMixedFramedHistoryFamilyBits.initial P D root)
      (P.sourceWidth root) (P.degree root) (L root) (F root) (C root) (D.rules root) (rules_bound P D root))
    (hd : ∀ root,InstructionBounds (C root+1) (F root) (P.sourceWidth root) (P.degree root) (L root)
      (IntegralMixedFramedHistoryFamilyBits.defaultInstruction P D root)) : FamilyInputs P D L F C where
  script root := script_bounds (IntegralMixedFramedHistoryFamilyBits.initial P D root)
    (P.sourceWidth root) (P.degree root) (L root) (F root) (C root) (hF root) (D.rules root) (rules_bound P D root) (hc root)
  default := hd

def factor (S F : ℕ) := F+S+1
def envelope (n S B W D L F C j : ℕ) := height n S B W D L (factor S F) C j

theorem factor_horizon (S F : ℕ) : S≤factor S F := by unfold factor; omega

theorem envelope_binary {n S B W D L F C j : List Bool → ℕ}
    (hn : UnaryFn n) (hS : UnaryFn S) (hB : UnaryFn B) (hW : UnaryFn W)
    (hD : BinaryFn D) (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C) (hj : UnaryFn j) :
    BinaryFn (fun q => envelope (n q) (S q) (B q) (W q) (D q) (L q) (F q) (C q) (j q)) :=
  height_binary hn hS hB hW hD hL ((hF.add (BinaryFn.ofUnary hS)).add (BinaryFn.const 1)) hC hj

theorem envelope_bits (n S B W D L F C j : ℕ) :
    (envelope n S B W D L F C j).size≤(growth n S B W D L (factor S F)).size*j+(C+1).size+1 :=
  height_bits n S B W D L (factor S F) C j

end LeanCanny.Algebra.IntegralMixedFramedCurrentQGrowth
