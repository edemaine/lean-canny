/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedPhysicalTraceCutSemantics
public import LeanCanny.Encoding.IntegralFramedPhysicalScalarRoots
public import LeanCanny.Encoding.IntegralFramedTerminalCutRows

/-! # Actual cut rows at a suffix of the same full physical vertex -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedPhysicalTraceCutSource
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask UniformIntegralPrefix
open IntegralFramedBankQuery (Bank)
open IntegralFramedPhysicalBankTerm (input)
open IntegralFramedPhysicalSuffixTest (rawTuple)
open IntegralMixedFramedHistoryFamilyBits (family)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] family rawTuple IntegralMixedHistory.normalizedScalarPolynomial IntegralMixedCutMatrix.raw
variable (B : Bank) (c w : List Bool)
  (hv : SquareSampleCompleteVertices.Valid (input B) c w) (q : List Bool)
  (ha : IntegralMixedFramedFullCutProbeBits.Active B.parameters q)
local notation "G" => family B.parameters B.plan B.data
local notation "old" => IntegralMixedVirtualTaskBits.saved B.parameters q
local notation "x" => IntegralMixedCutSource.Family.state G old
local notation "degree" => IntegralMixedCutSource.Family.degree G old
local notation "rule" => IntegralMixedCutSource.Family.rule G old
local notation "kind" => IntegralMixedCutSource.Family.kind G old
local notation "bound" => IntegralMixedCutSource.Family.birth_bound G old
local notation "row" => IntegralMixedHistory.normalizedScalarPolynomial x
  (IntegralMixedCutMatrix.raw x bound rule kind degree) degree
local notation "z" => rawTuple B c w hv

include ha in
theorem normalized_rows (hcut : IntegralFramedCreatingCut.ParentCut B.parameters B.plan q)
    (hroot : pairFst (B.key c)=RankedHistoryTask.root q) (hfit : birth B.parameters q<(G).birth (B.key c)) :
    ∀i,(UniformIntegralPrefixRows.rows ((G).cap old) (x).sampler.scalarPrefix.rows (x).sampler.scalarPrefix.basis row degree i).eval₂
      (Int.castRingHom ℝ) (fun j=>z (j.val+((G).birth (B.key c)-(birth B.parameters q+1))))=0 :=by
  let sigma : ℕ→ℝ:=fun j=>z (j+((G).birth (B.key c)-(birth B.parameters q+1)))
  have HZ : RootsAt ((G).state (B.key c)).sampler.scalarPrefix z :=by
    unfold rawTuple
    exact IntegralFramedPhysicalSquare.scalar_roots_at B.parameters B.plan B.data B.nodes B.factor B.seed B.bounds
      B.key B.positive c w hv
  have HR : RootsAt ((G).state (IntegralFramedCutSuccessor.key B.parameters q)).sampler.scalarPrefix sigma :=
    IntegralFramedTerminalCutRows.prefix_roots B.parameters B.plan B.data (B.key c) (RankedHistoryTask.root q)
      (BinaryNatCode.encode (get B.parameters .slot15 q)) (birth B.parameters q+1) hroot (by omega) z HZ
  exact IntegralFramedCutRootRows.normalized_rows B.parameters B.plan B.data q ha sigma HR hcut

end LeanCanny.Encoding.IntegralFramedPhysicalTraceCutSource
