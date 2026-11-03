/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedPaddedZeroRealExtension
public import LeanCanny.Encoding.IntegralFramedPhysicalRealizedVertex
/-! # A reserved last cut probe has one honest full complete word

The parent realization is given before the reserved probe. The actual
script ends in that chosen cut; no solvability of arbitrary later records
is assumed. The fresh word retains every old bank quotient together.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedPaddedCutVertex
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedIntegerRealization IntegralMixedFramedHistoryScript
open IntegralMixedFramedHistoryFamilyBits (Plan family commands initial)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def values (v : ℕ→ℝ) (i : ℕ):=if i=0 then 0 else v (i-1)

theorem step_realizes {n S B m : ℕ} {Q : SpatialSource n} {ι : Type} [Fintype ι]
    (x : State Q S B m ι) (hm : m≤S) (r : IntegralMixedCriticalSweep.Rule n)
    (c : IntegralMixedRelativeCuts.Kind Q r) (d : ℕ) (hd : d<2^B)
    (v : ℕ→ℝ) (hv : Realizes x v) : Realizes (IntegralMixedRelativeCuts.step x hm r c d) (values v):=by
 obtain ⟨z,φ,hz,hφ,hv⟩:=hv
 obtain ⟨y,ψ,hy,_,_,_,hψ,hhead,htail⟩:=normalizedScalar_padding_zero_extend x hm
   (IntegralRelativeTruncation.truncate (IntegralMixedRelativeCuts.factor x hm r c) d) d hd z hz φ hφ
 refine ⟨y,ψ,hy,hψ,?_⟩
 intro i
 refine Fin.cases ?_ (fun j=>?_) i
 · exact hhead
 · simpa only [IntegralMixedRelativeCuts.step,values,Fin.val_succ,Nat.succ_ne_zero,ite_false,Nat.add_sub_cancel] using (htail j).trans (hv j)

theorem run_realizes {n S B : ℕ} {Q : SpatialSource n} {ι : Type} [Fintype ι]
    (x : State Q S B 0 ι) (cs : List (Instruction n B)) (R : SpatialSource n)
    (hR : PurePowerReductionBounds.dimension (n+1) R.degree≤2^B)
    (r : IntegralMixedCriticalSweep.Rule n) (c : IntegralMixedRelativeCuts.Kind R r)
    (d : ℕ) (hs : d≤IntegralMixedExceptionalBounds.auxiliaryCap (n+1) R.degree) (hd : d<2^B)
    (room : (⟨R,hR,.cut r c d hs hd.le⟩::cs).length≤S+1)
    (v : ℕ→ℝ) (hv : Realizes (run x cs (by simp only [List.length_cons] at room;omega)) v) :
    Realizes (run x (⟨R,hR,.cut r c d hs hd.le⟩::cs) room) (values v):=
 step_realizes (reframe (run x cs (by simp only [List.length_cons] at room;omega)) R hR)
   (by simp only [List.length_cons] at room;omega) r c d hd v hv

private theorem run_realizes_eq {n S B : ℕ} {Q : SpatialSource n} {ι : Type} [Fintype ι]
    (x : State Q S B 0 ι) (cs ds : List (Instruction n B)) (he : cs=ds)
    (hc : cs.length≤S+1) (hd : ds.length≤S+1) (v : ℕ→ℝ) (hv : Realizes (run x ds hd) v) :
    Realizes (run x cs hc) v:=by cases he;exact hv

private theorem run_realizes_root (P : Parameters) (D : Plan P) (r s : List Bool) (he : r=s)
    (hr : (D.rules r).length≤P.cap r+1+1) (hs : (D.rules s).length≤P.cap s+1+1)
    (v : ℕ→ℝ) (hv : Realizes (run (initial P D r) (D.rules r) hr) v) :
    Realizes (run (initial P D s) (D.rules s) hs) v:=by cases he;exact hv

variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
 (L F C : List Bool→ℕ) (hsyntax : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
 (root : List Bool) (cs : List (Instruction (P.ambient root) (P.width root)))
 (R : SpatialSource (P.ambient root))
 (hR : PurePowerReductionBounds.dimension (P.ambient root+1) R.degree≤2^P.width root)
 (r : IntegralMixedCriticalSweep.Rule (P.ambient root)) (c : IntegralMixedRelativeCuts.Kind R r)
 (d : ℕ) (hs : d≤IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient root+1) R.degree)
 (hd : d<2^P.width root)
 (hscript : D.rules root=⟨R,hR,.cut r c d hs hd.le⟩::cs)

include hscript in
theorem full_positive : 0<(family P D H).birth
    (IntegralMixedFramedHistoryFamilyBits.keyAt root (D.rules root).length []):=by
 rw [IntegralMixedFramedHistoryFamilyBits.family_birth,IntegralMixedFramedHistoryFamilyBits.keyAt_prefix
   P root _ [] (by have HB:=D.room root;omega),hscript,List.length_cons]
 exact Nat.succ_pos _

theorem exists_vertex (v : ℕ→ℝ)
    (hv : Realizes (run (initial P D root) cs (by have HB:=D.room root;rw [hscript] at HB;simp only [List.length_cons] at HB;omega)) v) :
    let key:=fun _ : List Bool=>IntegralMixedFramedHistoryFamilyBits.keyAt root (D.rules root).length []
    let hp:=fun _ : List Bool=>full_positive P D H root cs R hR r c d hs hd hscript
    ∃w,∃hw : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalSquare.input P D H L F C hsyntax key hp) [] w,
      w.length=SquareSampleCompleteVertices.width (IntegralFramedPhysicalSquare.input P D H L F C hsyntax key hp) [] ∧
      ∀i : Fin ((family P D H).birth (key [])),
        IntegralFramedPhysicalSquare.point P D H L F C hsyntax key hp [] w hw i=values v i.val:=by
 dsimp only
 let key:=IntegralMixedFramedHistoryFamilyBits.keyAt root (D.rules root).length []
 have HC : (D.rules root).length≤P.cap root+1+1:=by have HB:=D.room root;omega
 have HZ:=run_realizes (initial P D root) cs R hR r c d hs hd
   (by rw [←hscript];exact HC) v hv
 have HK : pairFst key=root:=by simp only [key,IntegralMixedFramedHistoryFamilyBits.keyAt,pairFst_pair]
 have HE : commands P D key=D.rules (pairFst key):=by
   unfold commands
   have HL : (D.rules (pairFst key)).length=IntegralMixedFramedHistoryFamilyBits.prefixLength P key:=by
     rw [HK]
     exact (IntegralMixedFramedHistoryFamilyBits.keyAt_prefix P root _ [] (by have HB:=D.room root;omega)).symm
   rw [←HL]
   exact paddedPast_full _ _
 have HFull:=run_realizes_eq (initial P D root) _ _ hscript HC _ _ HZ
 have HC' : (D.rules (pairFst key)).length≤P.cap (pairFst key)+1+1:=by rw [HK];exact HC
 have HFull':=run_realizes_root P D root (pairFst key) HK.symm HC HC' (values v) HFull
 have HR:=run_realizes_eq (initial P D (pairFst key)) (commands P D key) (D.rules (pairFst key)) HE
   (by rw [HE];exact HC') HC' (values v) HFull'
 have HState : Realizes ((family P D H).state key) (values v):=HR
 exact IntegralFramedPhysicalSquare.exists_realized P D H L F C hsyntax (fun _=>key)
   (fun _=>full_positive P D H root cs R hR r c d hs hd hscript) [] (values v) HState

end LeanCanny.Encoding.IntegralFramedPaddedCutVertex
