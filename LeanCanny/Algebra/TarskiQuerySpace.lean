/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.TarskiPrincipalContext

/-! # Polynomial-space Tarski queries from the original two coefficient readers

The actual head and seed degrees are computed and retained, rather than assumed
to be FP functions of the original input. Total capped contexts support the
intermediate evaluators on every word. The constant-head branch returns zero,
including the zero-polynomial convention for the finite root query.
-/

@[expose] public section

namespace LeanCanny.Algebra.TarskiQueryBits
open Complexity Polynomial
open LeanCanny.Encoding
open LeanCanny.Computation
open IntegerTarskiSeedBits

noncomputable def value (F : Family) (c : List Bool) : ℤ := RootSignQueries.tarskiQuery
  ((F.head c).map (algebraMap ℤ ℝ)) ((F.query c).map (algebraMap ℤ ℝ))

theorem value_of_degree_zero (F : Family) (c : List Bool) (hp : (F.head c).natDegree = 0) :
    value F c = 0 := by
  unfold value
  rw [eq_C_of_natDegree_eq_zero hp, Polynomial.map_C]
  rw [RootSignQueries.tarskiQuery, Polynomial.roots_C]
  simp [RootSignQueries.signSum]

theorem prepared_principal_eq (F : Family) (c : List Bool) (hp : 0 < (F.head c).natDegree) :
    PseudoRemainder.principalQuery
      ((TarskiDegreeContext.family F).head (TarskiDegreeContext.prepared F c))
      ((TarskiDegreeContext.family F).query (TarskiDegreeContext.prepared F c))
      (Nat.fromBitsLE ((TarskiDegreeContext.family F).degree (TarskiDegreeContext.prepared F c)))
      (Nat.fromBitsLE ((TarskiDegreeContext.family F).degree (TarskiDegreeContext.prepared F c)) +
        Nat.fromBitsLE ((TarskiDegreeContext.family F).queryBound (TarskiDegreeContext.prepared F c))) = value F c := by
  let G := TarskiDegreeContext.family F
  let x := TarskiDegreeContext.prepared F c
  have hh : G.head x = F.head c := TarskiDegreeContext.prepared_head F c
  have hd : Nat.fromBitsLE (G.degree x) = (F.head c).natDegree := TarskiDegreeContext.prepared_degree F c hp
  have hq : G.query x = F.query c := by
    simp only [G, x, TarskiDegreeContext.family, TarskiDegreeContext.prepared, Function.comp_apply, pairFst_pair]
  have hD := G.input_degree x
  rw [hh, hq, hd] at hD
  change PseudoRemainder.principalQuery (G.head x) (G.query x) (Nat.fromBitsLE (G.degree x))
    (Nat.fromBitsLE (G.degree x) + Nat.fromBitsLE (G.queryBound x)) = _
  rw [hh, hq, hd]
  exact (RootSignQueries.tarskiQuery_pseudo_int (F.head c) (F.query c) _ _ rfl hp hD).symm

/-- The only arithmetic subroutines supplied externally read original head and
query coefficients modulo arbitrary positive moduli. Metadata fields are bounds. -/
noncomputable def evaluator {F : Family} (a : Access F) (hF : ControlsPolyTime F)
    (P : SpaceFunction a.headCoefficient) (Q : SpaceFunction a.queryCoefficient) :
    SpaceFunction (fun c => SignStatisticBits.integerCode (value F c)) := by
  let b := TarskiDegreeContext.access a
  have hb := TarskiDegreeContext.controls F hF
  have PH : SpaceFunction b.headCoefficient := by
    simpa only [b, TarskiDegreeContext.access] using TarskiDegreeContext.headEvaluator P
  have QH : SpaceFunction b.queryCoefficient := by
    simpa only [b, TarskiDegreeContext.access] using
      Q.precompose TarskiDegreeContext.sourceQuery TarskiDegreeContext.sourceQuery_mem_FP
  let V := TarskiPrincipalContext.principalEvaluator b hb PH QH
  have hz : FPPred (fun x => Nat.fromBitsLE (pairSnd x) = 0) :=
    (BinaryNat.lt_fppred pairSnd_mem_FP (constFn_mem_FP [true])).of_iff (fun x => by
      change Nat.fromBitsLE (pairSnd x) < 1 ↔ Nat.fromBitsLE (pairSnd x) = 0
      omega)
  let B := SpaceFunction.branch (fun x => decide (Nat.fromBitsLE (pairSnd x) = 0)) hz.flag_mem_FP
    (SpaceFunction.ofFP (fun _ => SignStatisticBits.integerCode 0) (constFn_mem_FP _)) V
  have H : SpaceFunction (TarskiDegreeContext.prepared F) := by
    refine (a.headDegreeEvaluator hF P).withInput.congr (funext fun c => ?_)
    simp only [TarskiDegreeContext.prepared]
  let E := H.chain B
  refine E.congr (funext fun c => ?_)
  simp only [Function.comp_apply, decide_eq_true_eq]
  have hc : Nat.fromBitsLE (pairSnd (TarskiDegreeContext.prepared F c)) = (F.head c).natDegree := by
    simp only [TarskiDegreeContext.prepared, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  rw [hc]
  by_cases hp : (F.head c).natDegree = 0
  · rw [ite_eq_left hp, value_of_degree_zero F c hp]
  · rw [ite_eq_right hp]
    exact congrArg SignStatisticBits.integerCode (prepared_principal_eq F c (by omega))

end LeanCanny.Algebra.TarskiQueryBits
