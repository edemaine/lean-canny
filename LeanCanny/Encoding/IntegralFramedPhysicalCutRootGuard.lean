/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedPhysicalCutRows
public import LeanCanny.Encoding.IntegralFramedPhysicalTraceCutParent
public import LeanCanny.Algebra.IntegralMixedCutHeadRootGuard
public import LeanCanny.Encoding.IntegralFramedTerminalCutBankPoint
/-! # A full vertex's actual cut suffix has exactly the native head root guard -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedPhysicalTraceCutSource
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralFramedBankQuery (Bank)
open IntegralFramedPhysicalBankTerm (input)
open IntegralFramedPhysicalSuffixTest (rawTuple)
open IntegralMixedFramedHistoryFamilyBits (family)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] family rawTuple parent
variable (B : Bank) (hkey : ∀c,B.key c=B.key (pair (pairFst c) []))
  (c w : List Bool) (hv : SquareSampleCompleteVertices.Valid (input B) c w) (u : List Bool)
local notation "p" => parent B c u
local notation "G" => family B.parameters B.plan B.data
local notation "old" => IntegralMixedVirtualTaskBits.saved B.parameters p
local notation "x" => IntegralMixedCutSource.Family.state G old
local notation "bound" => IntegralMixedCutSource.Family.birth_bound G old
local notation "rule" => IntegralMixedCutSource.Family.rule G old
local notation "kind" => IntegralMixedCutSource.Family.kind G old
local notation "degree" => IntegralMixedCutSource.Family.degree G old
local notation "offset" => IntegralFramedTerminalCutTest.count B.parameters B.plan B.data (taskKey B) p-
  IntegralMixedCutSource.Family.birth G old
noncomputable def cutTuple (i : Fin ((G).birth old+1)) : ℝ :=rawTuple B c w hv
  (i.val+((G).birth (B.key c)-(birth B.parameters p+1)))
local notation "z" => cutTuple B c w hv u

include hkey in
theorem factor_root_guard (ha : IntegralMixedFramedFullCutProbeBits.Active B.parameters p)
    (hcut : IntegralFramedCreatingCut.ParentCut B.parameters B.plan p)
    (hroot : pairFst (B.key c)=RankedHistoryTask.root p)
    (hfit : birth B.parameters p<(G).birth (B.key c))
    (φ : (x).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hφ : ∀i,φ ((x).sampler.scalarPrefix.basis.generator i)=rawTuple B c w hv (i.val+offset)^
      UniformIntegralPowerSchedule.weights (IntegralMixedFramedChoiceProbeSourceBits.horizon B.parameters p)
        (2^(G).width old) ((G).birth old) i)
    (hc : IntegralMixedRelativeCuts.CoefficientGuards x bound rule φ kind degree) :
    (IntegralMixedRelativeCuts.factor x bound rule kind).eval₂ φ.toRingHom
      (IntegralRelativeTruncation.jointQuotient (x).sampler.scalarPrefix
        (IntegralMixedRelativeCuts.factor x bound rule kind) degree z)=0 ↔
      z 0≠0 ∨ φ ((IntegralMixedRelativeCuts.factor x bound rule kind).coeff 0)=0 :=by
  have HM : (G).birth old=birth B.parameters p :=
    (IntegralMixedFramedHistoryFamilyBits.geometry B.parameters B.plan B.data).birth p
  have HP (i : Fin ((G).birth old)) : φ ((x).sampler.scalarPrefix.basis.generator i)=
      z i.succ^UniformIntegralPowerSchedule.weights ((G).cap old) (2^(G).width old) ((G).birth old) i :=by
    have HI : i.val+offset=i.succ.val+((G).birth (B.key c)-(birth B.parameters p+1)) :=by
      rw [count_parent B hkey c u]
      simp only [Fin.val_succ]
      omega
    have HW:=congrArg (fun S : ℕ=>UniformIntegralPowerSchedule.weights S
      (2^(G).width old) ((G).birth old) i) (parent_horizon B c u).symm
    exact (hφ i).trans (congrArg₂ (fun (a : ℝ) (e : ℕ)=>a^e) (congrArg (rawTuple B c w hv) HI) HW)
  exact IntegralMixedRelativeCuts.head_root_guard x bound rule kind degree (((G).degree_bound old).trans ((G).scalar_cap old)) φ z HP hc
    (normalized_rows B c w hv p ha hcut hroot hfit)

end LeanCanny.Encoding.IntegralFramedPhysicalTraceCutSource
