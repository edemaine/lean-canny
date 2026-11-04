/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedCanonicalPaddingObservation
public import LeanCanny.Algebra.IntegralMixedFramedCompanionObservationFrom
/-! # Canonical padding retains every powered physical block as well as scalars -/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedCanonicalPadding
open LeanCanny.Algebra LeanCanny.Encoding IntegralMixedHistory
open IntegralMixedFramedHistoryScript IntegralMixedFramedPhysicalIndex IntegralMixedFramedFixedContinuation
open IntegralMixedCausalRowConstructor IntegralMixedPointCompanion IntegralMixedFrozenFrame
open IntegralMixedFramedRunObservation
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def zeroFree (n : ℕ) : Free (∅ : Finset (Fin (n+1))):=⟨0,Finset.notMem_empty _⟩
def paddingSelections (n k : ℕ):=List.replicate k (zeroFree n)

theorem paddingSelections_length (n k : ℕ) : (paddingSelections n k).length=k:=List.length_replicate

private theorem shift_empty_rows (n m k : ℕ) :
    shiftRows (fun _ : Fin (n+1)=>Row.single (none : Atom m)) k=
      (fun _ : Fin (n+1)=>Row.single (none : Atom (m+k))):=by
  induction k with
  | zero=>rfl
  | succ k ih=>rw [shiftRows,ih];rfl

private theorem empty_command {n B m : ℕ} {P : SpatialSource n} (k : ℕ) :
    command (P:=P) (B:=B) (∅ : Finset (Fin (n+1))) (fun _=>false)
      (fun _=>Row.single (none : Atom m)) (zeroFree n) k (zeroFree n)=
      .critical (IntegralMixedCanonicalPaddingSeed.rule n):=by
  unfold command pointData
  rw [shift_empty_rows]
  simpa only [zeroFree] using congrArg
    (fun r=>IntegralMixedFullHistoryScript.Command.critical (P:=P) (B:=B) r) (original_rule n (m+k))

theorem padding_commands {n B : ℕ} (P : SpatialSource n)
    (hP : PurePowerReductionBounds.dimension (n+1) P.degree≤2^B) (m k : ℕ) :
    (commands (P:=P) (B:=B) (∅ : Finset (Fin (n+1))) (fun _=>false)
      (fun _=>Row.single (none : Atom m)) (zeroFree n) (paddingSelections n k)).map (wrap P hP)=
      List.replicate k (IntegralMixedCanonicalPaddingSeed.instruction P hP):=by
  induction k with
  | zero=>rfl
  | succ k ih=>
    simp only [paddingSelections] at ih
    simp only [paddingSelections,List.replicate_succ,commands,List.map_cons,List.length_replicate]
    rw [empty_command,ih]
    rfl

theorem run_physical_observation {n S B : ℕ} {Q : SpatialSource n}
    (initial : State Q S B 0 (Fin 0)) (cs : List (Instruction n B)) (ho : cs.length≤S+1)
    (P : SpatialSource n) (hP : PurePowerReductionBounds.dimension (n+1) P.degree≤2^B)
    (hn : 0<n) (charge : ℕ) (hdegree : P.degree=BoundedZeroSource.powerDegree charge)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B)
    (z : ℕ→ℝ) (hz : (ofCommands initial cs ho).Roots z)
    (p : Fin (n+1)→ℝ)
    (hp : (FermatCriticalHomogenization.polynomial P.low P.leading P.degree).eval₂ (Int.castRingHom ℝ) p=0)
    (hg : ∀i,i≠0→(MvPolynomial.pderiv i
      (FermatCriticalHomogenization.polynomial P.low P.leading P.degree)).eval₂ (Int.castRingHom ℝ) p=0)
    (k : ℕ) (room : (List.replicate k (IntegralMixedCanonicalPaddingSeed.instruction P hP)++cs).length≤S+1) :
    ∃u : ℕ→ℝ,
      (ofCommands initial (List.replicate k (IntegralMixedCanonicalPaddingSeed.instruction P hP)++cs) room).Roots u ∧
      (∀i,i<arity cs→u i=z i) ∧
      (∀j : Fin (paddingSelections n k).length,∀i,
        u (arity cs+(2*n+4)*((paddingSelections n k).length-1-j.val)+i.val)^
          UniformIntegralPowerSchedule.physical S (2^B) (cs.length+((paddingSelections n k).length-1-j.val))=p i) ∧
      ∀i : Fin (cs.length+(paddingSelections n k).length),
        (ofCommands initial (List.replicate k (IntegralMixedCanonicalPaddingSeed.instruction P hP)++cs) room).point u i.val=
          IntegralMixedPointCompanion.values p (fun j=> (ofCommands initial cs ho).point z j.val) (paddingSelections n k) i:=by
  let x:=reframe (IntegralMixedFramedHistoryScript.run initial cs ho) P hP
  let raw : Index (Fin 0) cs→ℝ:=fun i=>z (enumerate cs i).val
  have HR : ∀i,(x.sampler.rows i).eval₂ (Int.castRingHom ℝ) raw=0:=
    (roots_actual initial cs ho z).mp hz
  obtain ⟨φ,Hφ,HV⟩:=before_interprets initial P hP cs ho raw HR
  let old : Fin cs.length→ℝ:=fun i=>(ofCommands initial cs ho).point z i.val
  have HOld : ∀i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=old i:=by
    intro i
    exact (HV i).trans (point_actual initial cs ho z i).symm
  let rows : Fin (n+1)→Row cs.length:=fun _=>.single none
  let g:=zeroFree n
  let js:=paddingSelections n k
  have HRoom : cs.length+js.length≤S+1:=by
    have H:=room
    simp only [List.length_append,List.length_replicate] at H
    simp only [js,paddingSelections_length]
    omega
  have HP : p∈slice P (originalFrame (∅ : Finset (Fin (n+1))) (fun _=>false) rows) old:=
    ⟨hp,fun i hi=>False.elim (Finset.notMem_empty i hi)⟩
  have HF : PrefixFrozen (originalFrame (∅ : Finset (Fin (n+1))) (fun _=>false) rows):=
    PrefixFrozen.of_empty _ rfl
  have HE:=IntegralMixedPointCompanion.exists_realized x _ _ rows g hn charge hdegree hcap HF
    raw HR φ Hφ old HOld p HP (fun i _ hi=>hg i hi) js HRoom
  let R:=Classical.choice HE.1
  obtain ⟨u,HU,HO,HB,HV⟩:=companion_observation_from initial hP cs ho x rfl rfl HEq.rfl
    (enumerate cs) rfl HEq.rfl _ _ rows g raw φ old p js HRoom R
  have HC : (commands (P:=P) (B:=B) (∅ : Finset (Fin (n+1))) (fun _=>false) rows g js).map (wrap P hP)++cs=
      List.replicate k (IntegralMixedCanonicalPaddingSeed.instruction P hP)++cs:=
    congrArg (fun newer=>newer++cs) (padding_commands P hP cs.length k)
  refine ⟨u,?_,?_,HB,?_⟩
  · simpa only [HC] using HU
  · intro i hi
    have H:=HO ((enumerate cs).symm ⟨i,hi⟩)
    simpa only [raw,Equiv.apply_symm_apply,Fin.val_mk] using H
  · simpa only [HC,old] using HV

end LeanCanny.Geometry.IntegralMixedCanonicalPadding
