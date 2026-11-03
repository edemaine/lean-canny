/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalDrop
public import LeanCanny.Encoding.IntegralFramedPhysicalSquarePoint
public import LeanCanny.Encoding.IntegralMixedSourceIntegerPaddingRealization
/-! # An actual full vertex realizes each earlier same-root physical prefix

Every old raw column and bank value is read from the SAME full joint tuple.
No prefix sampler word, scalar-only system or old realization is supplied.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedPhysicalPrefixRealization
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript
open IntegralMixedFramedHistoryFamilyBits (Plan family initial commands defaultInstruction prefixLength keyAt)
open IntegralMixedFramedPhysicalIndex (enumerate arity)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem roots_list_transport {n S B : ℕ} {Q : SpatialSource n}
    (initial : State Q S B 0 (Fin 0)) (cs ds : List (Instruction n B))
    (hc : (cs).length≤S+1) (hd : ds.length≤S+1) (he : cs=ds) (z : Index (Fin 0) cs→ℝ)
    (hz : ∀i,((run initial cs hc).sampler.rows i).eval₂ (Int.castRingHom ℝ) z=0) :
    ∀i,((run initial ds hd).sampler.rows i).eval₂ (Int.castRingHom ℝ)
      (z∘cast (congrArg (Index (Fin 0)) he).symm)=0 :=by
  cases he
  exact hz

private theorem column_cast {n B : ℕ} (cs ds : List (Instruction n B)) (he : cs=ds)
    (i : Index (Fin 0) ds) :
    (enumerate cs (cast (congrArg (Index (Fin 0)) he).symm i)).val=(enumerate ds i).val :=by
  cases he
  rfl

variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
 (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
 (key : List Bool→List Bool) (hpos : ∀c,0<(family P D H).birth (key c))
 (c w : List Bool) (hv : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalSquare.input P D H L F C hs key hpos) c w)
local notation "root"=>pairFst (key c)
local notation "cs"=>commands P D (key c)

noncomputable abbrev past (m : ℕ) :=paddedPast (defaultInstruction P D root) (D.rules root) m

theorem drop_eq (m : ℕ) (hm : m≤prefixLength P (key c)) :
    (commands P D (key c)).drop (prefixLength P (key c)-m)=past P D key c m :=
  paddedPast_drop _ _ _ _ hm

noncomputable def embedding (m : ℕ) (hm : m≤prefixLength P (key c)) :
    Index (Fin 0) (past P D key c m)→Index (Fin 0) (commands P D (key c)) :=
  IntegralMixedFramedPhysicalDrop.embedding cs (prefixLength P (key c)-m)∘
    cast (congrArg (Index (Fin 0)) (drop_eq P D key c m hm)).symm

theorem column (m : ℕ) (hm : m≤prefixLength P (key c)) (i : Index (Fin 0) (past P D key c m)) :
    (enumerate cs (embedding P D key c m hm i)).val=(enumerate (past P D key c m) i).val :=by
  have HE:=IntegralMixedFramedPhysicalDrop.enumerate_embedding cs (prefixLength P (key c)-m)
    (cast (congrArg (Index (Fin 0)) (drop_eq P D key c m hm)).symm i)
  refine HE.trans ?_
  exact column_cast _ _ (drop_eq P D key c m hm) i

noncomputable def raw (m : ℕ) (hm : m≤prefixLength P (key c)) : Index (Fin 0) (past P D key c m)→ℝ :=
 IntegralFramedPhysicalSquare.rawPoint P D H L F C hs key hpos c w hv∘embedding P D key c m hm

theorem raw_column (m : ℕ) (hm : m≤prefixLength P (key c))
    (i : Index (Fin 0) (past P D key c m)) :
    raw P D H L F C hs key hpos c w hv m hm i=
      IntegralFramedPhysicalSquare.joint P D H L F C hs key hpos c w hv
        ⟨(enumerate (past P D key c m) i).val,by
          rw [←column P D key c m hm i]
          exact (enumerate cs (embedding P D key c m hm i)).isLt⟩ :=by
  apply congrArg (IntegralFramedPhysicalSquare.joint P D H L F C hs key hpos c w hv)
  apply Fin.ext
  exact column P D key c m hm i

noncomputable def state (m : ℕ) (hm : m≤prefixLength P (key c)) :=
 IntegralMixedFramedFamilyRunView.runAt P D root m (hm.trans (min_le_right _ _))

theorem raw_roots (m : ℕ) (hm : m≤prefixLength P (key c)) :
    ∀i,((state P D key c m hm).sampler.rows i).eval₂ (Int.castRingHom ℝ) (raw P D H L F C hs key hpos c w hv m hm)=0 :=by
  have HC : (cs).length≤(P.cap root+1)+1 :=by
    rw [commands,paddedPast_length]
    exact (min_le_right _ _).trans (Nat.le_succ _)
  have HD : ((cs).drop (prefixLength P (key c)-m)).length≤(P.cap root+1)+1 :=by
    rw [List.length_drop]
    exact (Nat.sub_le _ _).trans HC
  have HP : (past P D key c m).length≤(P.cap root+1)+1 :=by
    rw [past,paddedPast_length]
    exact (hm.trans (min_le_right _ _)).trans (Nat.le_succ _)
  have HF : ∀i,((run (initial P D root) cs HC).sampler.rows i).eval₂ (Int.castRingHom ℝ)
      (IntegralFramedPhysicalSquare.rawPoint P D H L F C hs key hpos c w hv)=0 :=
    IntegralFramedPhysicalSquare.raw_roots P D H L F C hs key hpos c w hv
  have HZ:=IntegralMixedFramedPhysicalDrop.roots (initial P D root) cs HC
    (prefixLength P (key c)-m) HD
    (IntegralFramedPhysicalSquare.rawPoint P D H L F C hs key hpos c w hv) HF
  exact roots_list_transport (initial P D root) ((cs).drop (prefixLength P (key c)-m))
    (past P D key c m) HD HP (drop_eq P D key c m hm)
    (IntegralFramedPhysicalSquare.rawPoint P D H L F C hs key hpos c w hv∘
      IntegralMixedFramedPhysicalDrop.embedding cs (prefixLength P (key c)-m)) HZ

noncomputable def values (m : ℕ) (hm : m≤prefixLength P (key c)) : ℕ→ℝ :=
 IntegralMixedFramedBankObservation.extend
   (IntegralMixedFullBankPoint.point (state P D key c m hm) (raw P D H L F C hs key hpos c w hv m hm))

theorem values_at (m : ℕ) (hm : m≤prefixLength P (key c)) (i : Fin (past P D key c m).length) :
    values P D H L F C hs key hpos c w hv m hm i.val=
      raw P D H L F C hs key hpos c w hv m hm ((state P D key c m hm).sampler.scalar i)^
        UniformIntegralPowerSchedule.weights (P.cap root+1) (2^P.width root) (past P D key c m).length i /
        ((state P D key c m hm).bank.denominator i:ℝ) :=by
  unfold values IntegralMixedFramedBankObservation.extend
  rw [dite_eq_left i.isLt]
  rfl

theorem exists_interpretation (m : ℕ) (hm : m≤prefixLength P (key c)) :
    ∃φ : (state P D key c m hm).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
      (∀i,φ ((state P D key c m hm).sampler.scalarPrefix.basis.generator i)=
        raw P D H L F C hs key hpos c w hv m hm ((state P D key c m hm).sampler.scalar i)^
          UniformIntegralPowerSchedule.weights (P.cap root+1) (2^P.width root) (past P D key c m).length i) ∧
      ∀i,φ ((state P D key c m hm).bank.numerator i)/((state P D key c m hm).bank.denominator i:ℝ)=
        values P D H L F C hs key hpos c w hv m hm i.val :=by
  have HC : Canonical (state P D key c m hm):=by
    apply run_canonical
    intro i
    exact Fin.elim0 i
  obtain ⟨φ,hφ,hvalues⟩:=IntegralMixedFullBankPoint.interprets (state P D key c m hm) HC
    (raw P D H L F C hs key hpos c w hv m hm) (raw_roots P D H L F C hs key hpos c w hv m hm)
  refine ⟨φ,hφ,?_⟩
  intro i
  have HE : values P D H L F C hs key hpos c w hv m hm i.val=
      IntegralMixedFullBankPoint.point (state P D key c m hm) (raw P D H L F C hs key hpos c w hv m hm) i:=
    dite_eq_left i.isLt
  exact (hvalues i).trans HE.symm

theorem realizes (m : ℕ) (hm : m≤prefixLength P (key c)) :
    IntegralMixedIntegerRealization.Realizes (state P D key c m hm)
      (values P D H L F C hs key hpos c w hv m hm) :=by
  obtain ⟨φ,hφ,hvalues⟩:=exists_interpretation P D H L F C hs key hpos c w hv m hm
  exact ⟨raw P D H L F C hs key hpos c w hv m hm,φ,
    raw_roots P D H L F C hs key hpos c w hv m hm,hφ,hvalues⟩

theorem canonical_realizes (m : ℕ) (hm : m≤prefixLength P (key c)) (aux : List Bool) :
    IntegralMixedIntegerRealization.Realizes
      (IntegralMixedFramedFamilyRunView.stateView P D H (keyAt root m aux))
      (values P D H L F C hs key hpos c w hv m hm) :=
  (IntegralMixedSourceIntegerPaddingRealization.realizes_at_key_iff P D H root aux m
    (hm.trans (min_le_right _ _)) _).mpr (realizes P D H L F C hs key hpos c w hv m hm)

end LeanCanny.Encoding.IntegralFramedPhysicalPrefixRealization
