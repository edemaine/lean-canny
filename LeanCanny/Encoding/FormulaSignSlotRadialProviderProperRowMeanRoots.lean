/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperRowMeanRule
public import LeanCanny.Geometry.IntegralMixedBankValueInterpretation
public import LeanCanny.Algebra.IntegralMixedNumericalSweepSpecialization
/-! # Actual provider mean-zero roots are ordinary midpoint roots -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderProperRow
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Connectivity LeanCanny.Computation LeanCanny.ETR
open IntegralMixedHistory IntegralMixedCriticalSweep IntegralMixedNumericalSweep Polynomial IntegralCriticalHistoryTask
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem mean_roots (A B : IntegralMixedPrefixSnapshot.Data) (he : A=B)
    (hm : A.birth≤A.horizon) (hl : B.birth≤B.horizon)
    (r : Rule A.ambient) (s : Rule B.ambient) (a b : Fin A.birth)
    (hs : HEq s (IntegralMixedMeanCenteredSweep.rule r a b))
    (hr : r.slope=commonDenominator A.state)
    (hc : Canonical A.state)
    (φ : A.state.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (ψ : B.state.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (H : ∀(i : Fin A.birth) (j : Fin B.birth),i.val=j.val→φ (A.state.bank.numerator i)/(A.state.bank.denominator i:ℝ)=
      ψ (B.state.bank.numerator j)/(B.state.bank.denominator j:ℝ))
    (hz : r.critical.heights r.height=.constant 0)
    (h1 : r.critical.scales r.height=1)
    (j : Fin (A.ambient-r.critical.offset.val+1))
    (k : Fin (B.ambient-s.critical.offset.val+1)) (hj : j.val=k.val) :
    ((selected B.state hl s k ψ).map (evalRingHom 0)).roots=
      ((selected A.state hm r j φ).map (evalRingHom
        ((φ (A.state.bank.numerator a)/(A.state.bank.denominator a:ℝ)+
          φ (A.state.bank.numerator b)/(A.state.bank.denominator b:ℝ))/2))).roots :=by
  cases he
  have HS : s=IntegralMixedMeanCenteredSweep.rule r a b:=eq_of_heq hs
  subst s
  have HP : φ=ψ:=IntegralMixedBankValueInterpretation.hom_ext A.state hc φ ψ
    (fun i=>H i i rfl)
  subst ψ
  have HJ : j=k:=Fin.ext hj
  subst k
  let values : Fin A.birth→ℝ:=fun i=>φ (A.state.bank.numerator i)/(A.state.bank.denominator i:ℝ)
  have HZ : (r.critical.heights r.height).evaluate values=0:=by rw [hz];simp only [AffineExpr.evaluate,Int.cast_zero]
  rw [selected_specialize A.state hl (IntegralMixedMeanCenteredSweep.rule r a b) hr φ values (fun _=>rfl),
    selected_specialize A.state hm r hr φ values (fun _=>rfl)]
  rw [Polynomial.roots_C_mul _ (coordinateScale_ne_zero A.state hl _),
    Polynomial.roots_C_mul _ (coordinateScale_ne_zero A.state hm r),
    ←IntegralMixedMeanCenteredSweep.coordinateAt_mean A.source r a b values HZ h1 j]

private theorem raw_ordinary_normal_form {a b : ℕ} (w : List Bool) (g j : ℕ)
    (hg : IntegralMixedChronologicalCutCode.Good a b w g j) (Q : ℤ) (hQ : Q≠0)
    : let r:=(IntegralMixedChronologicalCutCode.rawData a b w g j hg).rule Q hQ
    r.critical.heights r.height=.constant 0 ∧r.critical.scales r.height=1 :=by
  dsimp only
  let d:=IntegralMixedChronologicalFrameCode.descriptor a b w hg.1
  let hk:=IntegralMixedChronologicalCutCode.raw_fit a b w g j hg
  constructor
  · change (d.atom (FrozenCoordinateOrdering.permutation
      (IntegralMixedChronologicalSweepFrame.frame d hk).frozen
      (IntegralMixedChronologicalSweepFrame.next d hk))).value=.constant 0
    rw [(IntegralMixedChronologicalSweepFrame.prefix_frozen d hk).permutation]
    simp only [Equiv.refl_apply,IntegralMixedChronologicalFrame.Descriptor.atom,
      IntegralMixedChronologicalSweepFrame.next,Fin.val_mk,Nat.lt_irrefl,dite_false,
      IntegralMixedCausalRowConstructor.Atom.value]
  · rfl

local notation "BK"=>FormulaSignSlotRadialProviderRecordPlan.bank
local notation "P"=>IntegralFramedBankQuery.Bank.parameters BK
local notation "G"=>IntegralMixedFramedHistoryFamilyBits.family P
  (IntegralFramedBankQuery.Bank.plan BK) (IntegralFramedBankQuery.Bank.data BK)
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.bank
  parent terminal creating parentBirth root

private theorem ordinary_normal_form (z : List Bool)
    (hv : FormulaSignSlotRadialProviderAtomic.Valid (atomic z))
    (hg : FormulaSignSlotRadialProviderProperRowWitness.RowGood z) :
    let r:=(G).rule (parentKey false z)
    r.critical.heights r.height=.constant 0 ∧r.critical.scales r.height=1 :=by
  dsimp only
  rw [rule_at_parent false z (row_count_positive z hv) hg]
  simp only [parentData,Bool.false_eq_true,ite_false]
  exact raw_ordinary_normal_form _ _ _ _ _ _

private theorem actual_birth (mode : Bool) (z : List Bool)
    (hv : FormulaSignSlotRadialProviderAtomic.Valid (atomic z)) :
    (G).birth (parentKey mode z)=parentBirth mode z :=by
  have HC:=row_count_positive z hv
  exact (IntegralMixedFramedHistoryFamilyBits.family_birth P
    (IntegralFramedBankQuery.Bank.plan BK) (IntegralFramedBankQuery.Bank.data BK) _).trans
      ((parentKey_prefix mode z HC).trans (parentBirth_eq mode z HC).symm)

noncomputable def actualMeanReference (side : Bool) (z : List Bool)
    (hv : FormulaSignSlotRadialProviderAtomic.Valid (atomic z))
    (hg : FormulaSignSlotRadialProviderProperRowWitness.RowGood z) :
    Fin ((G).birth (parentKey false z)):=
  ⟨(meanReference side z hv hg).val,by
    rw [actual_birth false z hv]
    exact (meanReference side z hv hg).isLt⟩

def MeanRootsAgree (F : IntegralMixedCutSource.Family) (o e : List Bool)
    (a b : Fin (F.birth o)) : Prop:=
  ∀φ : (F.state o).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
  ∀ψ : (F.state e).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
  (∀(i : Fin (F.birth o)) (j : Fin (F.birth e)),i.val=j.val→φ ((F.state o).bank.numerator i)/((F.state o).bank.denominator i:ℝ)=
    ψ ((F.state e).bank.numerator j)/((F.state e).bank.denominator j:ℝ))→
  ∀j : Fin (F.ambient o-(F.rule o).critical.offset.val+1),
  ∀k : Fin (F.ambient e-(F.rule e).critical.offset.val+1),j.val=k.val→
    ((selected (F.state e) (F.birth_bound e) (F.rule e) k ψ).map (evalRingHom 0)).roots=
    ((selected (F.state o) (F.birth_bound o) (F.rule o) j φ).map (evalRingHom
      ((φ ((F.state o).bank.numerator a)/((F.state o).bank.denominator a:ℝ)+
        φ ((F.state o).bank.numerator b)/((F.state o).bank.denominator b:ℝ))/2))).roots

theorem actual_mean_roots (z : List Bool)
    (hv : FormulaSignSlotRadialProviderAtomic.Valid (atomic z))
    (hg : FormulaSignSlotRadialProviderProperRowWitness.RowGood z) :
    MeanRootsAgree G (parentKey false z) (parentKey true z)
      (actualMeanReference false z hv hg) (actualMeanReference true z hv hg) :=by
  intro φ ψ H j k hj
  have HC:=row_count_positive z hv
  have HN:=ordinary_normal_form z hv hg
  exact mean_roots (IntegralMixedPrefixSnapshot.ofState ((G).state (parentKey false z)))
    (IntegralMixedPrefixSnapshot.ofState ((G).state (parentKey true z)))
    (parent_state_snapshot_eq z (row_count_positive z hv)) _ _ _ _
    (actualMeanReference false z hv hg) (actualMeanReference true z hv hg)
    (actual_mean_rule z hv hg) (rule_current false z HC hg)
    (parent_canonical false z HC) φ ψ H
    HN.1 HN.2 j k hj

end LeanCanny.Encoding.FormulaSignSlotRadialProviderProperRow
