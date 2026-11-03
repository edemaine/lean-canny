/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedFramedCriticalReadback
public import LeanCanny.Encoding.IntegralFramedPhysicalScalarRoots
/-! # The same complete full vertex anchors an actual creating critical block

The command decomposition identifies the literal retained creator. Every
root and the older interpreting hom are obtained from the one full vertex.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedPhysicalCriticalReadback
open LeanCanny.Algebra LeanCanny.Geometry IntegralCriticalHistoryTask IntegralMixedHistory
open IntegralMixedFramedHistoryScript
open IntegralMixedFramedHistoryFamilyBits (Plan family initial commands)
open IntegralMixedFramedPhysicalIndex (enumerate)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
  (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
  (key : List Bool→List Bool) (hpos : ∀q,0<(family P D H).birth (key q))
  (q w : List Bool) (hv : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalSquare.input P D H L F C hs key hpos) q w)

noncomputable def tuple : ℕ→ℝ:=IntegralMixedFramedBankObservation.extend
  (IntegralFramedPhysicalSquare.joint P D H L F C hs key hpos q w hv)

theorem tuple_roots : IntegralMixedFramedCriticalReadback.Roots (initial P D (pairFst (key q)))
    (commands P D (key q)) (((family P D H).birth_bound (key q)).trans (Nat.le_succ _))
    (tuple P D H L F C hs key hpos q w hv) :=by
  have HE : (fun j=>tuple P D H L F C hs key hpos q w hv
      (enumerate (commands P D (key q)) j).val)=IntegralFramedPhysicalSquare.rawPoint P D H L F C hs key hpos q w hv :=by
    funext j
    unfold tuple IntegralMixedFramedBankObservation.extend
    exact dite_eq_left (enumerate (commands P D (key q)) j).isLt
  intro i
  change (((family P D H).state (key q)).sampler.rows i).eval₂ (Int.castRingHom ℝ)
    (fun j=>tuple P D H L F C hs key hpos q w hv (enumerate (commands P D (key q)) j).val)=0
  rw [HE]
  exact IntegralFramedPhysicalSquare.raw_roots P D H L F C hs key hpos q w hv i

variable (Q : SpatialSource (P.ambient (pairFst (key q))))
  (hQ : PurePowerReductionBounds.dimension (P.ambient (pairFst (key q))+1) Q.degree≤2^P.width (pairFst (key q)))
  (r : CriticalRule (P.ambient (pairFst (key q))))
  (newer older : List (Instruction (P.ambient (pairFst (key q))) (P.width (pairFst (key q)))))
  (hcs : commands P D (key q)=newer++⟨Q,hQ,.critical r⟩::older)

include D H Q hQ r newer hcs in
theorem older_room : older.length≤P.cap (pairFst (key q))+1 :=by
  have HB:=(family P D H).birth_bound (key q)
  change (commands P D (key q)).length≤P.cap (pairFst (key q))+1 at HB
  rw [hcs,List.length_append,List.length_cons] at HB
  omega

noncomputable def oldState : State Q (P.cap (pairFst (key q))+1) (P.width (pairFst (key q))) older.length (Index (Fin 0) older) :=
  reframe (run (initial P D (pairFst (key q))) older
    ((older_room P D H key q Q hQ r newer older hcs).trans (Nat.le_succ _))) Q hQ

theorem exists_critical_point :
    let x:=oldState P D H key q Q hQ r newer older hcs
    ∃φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
      (∀i,φ (x.sampler.scalarPrefix.basis.generator i)=
        tuple P D H L F C hs key hpos q w hv (enumerate older (x.sampler.scalar i)).val^
          UniformIntegralPowerSchedule.weights (P.cap (pairFst (key q))+1) (2^P.width (pairFst (key q))) older.length i) ∧
      IntegralMixedCriticalReadback.CriticalPoint x (older_room P D H key q Q hQ r newer older hcs) r φ
        (IntegralMixedFramedCriticalReadback.point (S:=P.cap (pairFst (key q))+1) older
          (tuple P D H L F C hs key hpos q w hv)) :=by
  have HC : (commands P D (key q)).length≤P.cap (pairFst (key q))+1+1:=
    ((family P D H).birth_bound (key q)).trans (Nat.le_succ _)
  have HT : (newer++⟨Q,hQ,.critical r⟩::older).length≤P.cap (pairFst (key q))+1+1:=hcs ▸ HC
  have HZ:=(IntegralMixedFramedCriticalReadback.roots_congr (initial P D (pairFst (key q))) _ _ HC HT hcs
    (tuple P D H L F C hs key hpos q w hv)).mp (tuple_roots P D H L F C hs key hpos q w hv)
  exact IntegralMixedFramedCriticalReadback.run_critical (initial P D (pairFst (key q))) Q hQ r newer older HT
    ((older_room P D H key q Q hQ r newer older hcs).trans (Nat.le_succ _))
    (older_room P D H key q Q hQ r newer older hcs) (tuple P D H L F C hs key hpos q w hv) HZ

end LeanCanny.Encoding.IntegralFramedPhysicalCriticalReadback
