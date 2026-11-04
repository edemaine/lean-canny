/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedPhysicalTraceCutParent
public import LeanCanny.Encoding.IntegralFramedPhysicalScalarObservation
/-! # A cut's selected old interpretation reads its actual prefix observation -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedPhysicalTraceCutSource
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralFramedBankQuery (Bank)
open IntegralMixedFramedHistoryFamilyBits (family prefixLength keyAt)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable (B :Bank) (hkey :∀c,B.key c=B.key (pair (pairFst c) []))
  (c w :List Bool) (hv :SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalBankTerm.input B) c w)
  (u old :List Bool) (hparent :old=IntegralMixedVirtualTaskBits.saved B.parameters (parent B c u))
  (m :ℕ) (hm :m≤prefixLength B.parameters (B.key c)) (aux :List Bool)
  (he :old=keyAt (pairFst (B.key c)) m aux)
  (hf :(family B.parameters B.plan B.data).birth old≤(family B.parameters B.plan B.data).birth (B.key c))
local notation "G"=>family B.parameters B.plan B.data
local notation "p"=>parent B c u

include hkey hparent hm he hf in
theorem quotient_observation
    (φ :((G).state old).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hφ :∀i,φ (((G).state old).sampler.scalarPrefix.basis.generator i)=
      IntegralFramedPhysicalSuffixTest.rawTuple B c w hv
        (i.val+(IntegralFramedTerminalCutTest.count B.parameters B.plan B.data (taskKey B) p-(G).birth old))^
        UniformIntegralPowerSchedule.weights (IntegralMixedFramedChoiceProbeSourceBits.horizon B.parameters p)
          (2^(G).width old) ((G).birth old) i) :
    ∀i :Fin ((G).birth old),φ (((G).state old).bank.numerator i)/(((G).state old).bank.denominator i:ℝ)=
      (IntegralFramedPhysicalScalarObservation.atKeyObservation B.parameters B.plan old).point
        (IntegralFramedPhysicalSquare.naturalPoint B.parameters B.plan B.data B.nodes B.factor B.seed B.bounds
          B.key B.positive c w hv) i.val:=by
  have HG :∀i,φ (((G).state old).sampler.scalarPrefix.basis.generator i)=
      IntegralFramedPhysicalSquare.scalarTuple B.parameters B.plan B.data B.nodes B.factor B.seed B.bounds
        B.key B.positive c w hv (UniformIntegralPowerSchedule.embed hf i)^
          UniformIntegralPowerSchedule.weights ((G).cap old) (2^(G).width old) ((G).birth old) i:=by
    intro i
    have HRaw :IntegralFramedPhysicalSuffixTest.rawTuple B c w hv
        (i.val+(IntegralFramedTerminalCutTest.count B.parameters B.plan B.data (taskKey B) p-(G).birth old))=
        IntegralFramedPhysicalSquare.scalarTuple B.parameters B.plan B.data B.nodes B.factor B.seed B.bounds
          B.key B.positive c w hv (UniformIntegralPowerSchedule.embed hf i):=by
      rw [count_parent B hkey c u]
      unfold IntegralFramedPhysicalSuffixTest.rawTuple IntegralMixedFramedBankObservation.extend
      rw [dite_eq_left (show i.val+((G).birth (B.key c)-(G).birth old)<(G).birth (B.key c) by
        have HI:=i.isLt;omega)]
      apply congrArg (IntegralFramedPhysicalSquare.scalarTuple B.parameters B.plan B.data B.nodes B.factor B.seed B.bounds
        B.key B.positive c w hv)
      apply Fin.ext
      exact Nat.add_comm _ _
    have HP :(G).cap old=IntegralMixedFramedChoiceProbeSourceBits.horizon B.parameters p:=
      (congrArg (G).cap hparent).trans (parent_horizon B c u)
    have HI:=hφ i
    rw [←HP,HRaw] at HI
    exact HI
  exact IntegralFramedPhysicalScalarObservation.quotient_prefix_at B.parameters B.plan B.data
    B.nodes B.factor B.seed B.bounds B.key B.positive c w hv old m hm aux he hf φ HG

end LeanCanny.Encoding.IntegralFramedPhysicalTraceCutSource
