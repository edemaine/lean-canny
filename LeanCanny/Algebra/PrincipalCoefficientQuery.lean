/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PrincipalCoefficientSpace
public import LeanCanny.Algebra.SignStatisticQuery

/-! # Streamed principal queries from certified polynomial coefficient readers

This closes the principal-sign-reader assumption in the sign-statistic scan.
The degree and coefficient-budget writers are FP; original coefficient routines
may use polynomial space. Retaining computed actual degrees on an extended
context is the remaining interface to the integer Tarski-seed evaluator.
-/

@[expose] public section

namespace LeanCanny.Algebra.PrincipalCoefficientBits
open Complexity Polynomial
open LeanCanny.Encoding
open LeanCanny.Computation
open PrincipalSubresultant

noncomputable def queryEvaluator {F : Resultant.Family} (a : Resultant.Access F)
    (ha : a.bits.ControlsPolyTime) (P : SpaceFunction a.bits.leftCoefficient)
    (Q : SpaceFunction a.bits.rightCoefficient) : SpaceFunction (fun c => SignStatisticBits.integerCode
      (permanencesMinusVariations ((List.range (F.leftDegree c + 1)).reverse.map
        (signedPsc (F.left c) (F.right c) (F.leftDegree c) (F.rightDegree c))))) := by
  let E := SignStatisticBits.descendingEvaluator (signEvaluator a ha P Q) a.bits.leftDegree ha.leftDegree
    (fun c i => signedPsc (F.left c) (F.right c) (F.leftDegree c) (F.rightDegree c) i)
    (by
      intro c i
      simp only [coefficient, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits])
  refine E.congr (funext fun c => ?_)
  rw [a.leftDegree, show Nat.fromBitsLE (BinaryNatCode.encode (F.leftDegree c)) = F.leftDegree c from
    Nat.fromBitsLE_bits _]

/-- With actual degree metadata, the principal pipeline evaluates a Tarski
query from coefficient readers for the head and its integer pseudo-seed. -/
noncomputable def tarskiEvaluator {F : Resultant.Family} (a : Resultant.Access F)
    (ha : a.bits.ControlsPolyTime) (P : SpaceFunction a.bits.leftCoefficient)
    (Q : SpaceFunction a.bits.rightCoefficient) (f : List Bool → ℤ[X]) (D : List Bool → ℕ)
    (hm : ∀ c, (F.left c).natDegree = F.leftDegree c) (hp : ∀ c, 0 < F.leftDegree c)
    (hn : ∀ c, F.rightDegree c = (F.right c).natDegree)
    (hs : ∀ c, F.right c = PseudoRemainder.seed (F.left c) (f c) (F.leftDegree c) (D c))
    (hD : ∀ c, (f c * (F.left c).derivative).natDegree ≤ D c) :
    SpaceFunction (fun c => SignStatisticBits.integerCode (RootSignQueries.tarskiQuery
      ((F.left c).map (algebraMap ℤ ℝ)) ((f c).map (algebraMap ℤ ℝ)))) := by
  refine (queryEvaluator a ha P Q).congr (funext fun c => ?_)
  rw [RootSignQueries.tarskiQuery_pseudo_int (F.left c) (f c) _ (D c) (hm c) (hp c) (hD c)]
  simp only [PseudoRemainder.principalQuery, ← hs c, hn c]

end LeanCanny.Algebra.PrincipalCoefficientBits
