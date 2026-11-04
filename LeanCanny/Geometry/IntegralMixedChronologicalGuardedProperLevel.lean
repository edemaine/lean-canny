/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedChronologicalGuardedPair
public import LeanCanny.Geometry.IntegralMixedChronologicalProperLevel
public import LeanCanny.Geometry.IntegralMixedGuardedProgramBirths
public import LeanCanny.Algebra.IntegralMixedFramedCompanionObservationFrom
/-! # One actual natural tuple retains the guarded endpoints and both proper-level blocks -/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedChronologicalEndpoint
open LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Connectivity
open IntegralMixedHistory IntegralMixedFrozenFrame IntegralMixedChronologicalFrame
open IntegralMixedOptionalEndpoints IntegralMixedPointCompanion IntegralMixedFullHistoryScript
open IntegralMixedFramedFixedContinuation IntegralHistorySampler UniformIntegralPowerSchedule FlatAffineCriticalStage
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem enumeration_from {α β :Type} {a :ℕ} (h :α=β) (e :α≃Fin a)
    (u :ℕ→ℝ) (y :α→ℝ) (z :β→ℝ) (hy :HEq y z) (hu :∀i,u (e i).val=y i):
    ∃f :β≃Fin a,HEq e f ∧∀i,u (f i).val=z i:=by
  subst β
  cases eq_of_heq hy
  exact ⟨e,HEq.rfl,hu⟩

private theorem full_continue_canonical {n S B m :ℕ} {P :SpatialSource n} {ι :Type} [Fintype ι]
    (x :State P S B m ι) (hx :Canonical x) (cs :List (Command P B)) (room :m+cs.length≤S+1):
    Canonical (continueRun x cs room):=by
  induction cs with
  | nil=>exact hx
  | cons c cs ih=>exact step_canonical _ (ih (by simp only [List.length_cons] at room;omega)) _ c

private theorem point_heq {n S B a b :ℕ} {Q :SpatialSource n} {ι κ :Type}
    (x :State Q S B a ι) (y :State Q S B b κ) (hab :a=b) (hi :ι=κ) (hx :HEq x y)
    (z :ι→ℝ) (w :κ→ℝ) (hz :HEq z w) (i :Fin a) (j :Fin b) (hij :i.val=j.val):
    IntegralMixedFullBankPoint.point x z i=IntegralMixedFullBankPoint.point y w j:=by
  subst b
  subst κ
  cases eq_of_heq hx
  cases eq_of_heq hz
  exact congrArg (IntegralMixedFullBankPoint.point x z) (Fin.ext hij)

private theorem old_column_heq {n B :ℕ} {Q :SpatialSource n} {α β :Type}
    (h :α=β) (i :α) (j :β) (hij :HEq i j) (c :Command Q B):
    HEq (IntegralMixedChosenLocalRealization.oldColumn c i) (IntegralMixedChosenLocalRealization.oldColumn c j):=by
  subst β
  cases eq_of_heq hij
  rfl

private theorem old_columns_heq {n B :ℕ} {Q :SpatialSource n} {α β :Type}
    (h :α=β) (i :α) (j :β) (hij :HEq i j) (cs :List (Command Q B)):
    HEq (oldColumns cs i) (oldColumns cs j):=by
  subst β
  cases eq_of_heq hij
  rfl

private theorem old_columns_append {n B :ℕ} {Q :SpatialSource n} {ι :Type}
    (cs ds :List (Command Q B)) (i :ι):
    HEq (oldColumns (cs++ds) i) (oldColumns cs (oldColumns ds i)):=by
  induction cs with
  | nil=>rfl
  | cons c cs ih=>exact old_column_heq (IntegralMixedOptionalEndpoints.index_append ι cs ds) _ _ ih c

private theorem wrapped_old_heq {n B :ℕ} {Q :SpatialSource n}
    (hQ :PurePowerReductionBounds.dimension (n+1) Q.degree≤2^B)
    (cs :List (Command Q B)) (older :List (IntegralMixedFramedHistoryScript.Instruction n B))
    (i :IntegralMixedFramedHistoryScript.Index (Fin 0) older):
    HEq (IntegralMixedFramedPhysicalPersistence.embed (cs.map (wrap Q hQ)) older i) (oldColumns cs i):=by
  induction cs with
  | nil=>rfl
  | cons c cs ih=>
    have H:=old_column_heq (IntegralMixedFramedFixedContinuation.index_append Q hQ cs older) _ _ ih c
    cases c <;> exact H

private theorem equivalence_value_heq {α β :Type} {a :ℕ} (h :α=β) (e :α≃Fin a) (f :β≃Fin a)
    (he :HEq e f) (i :α) (j :β) (hij :HEq i j):(e i).val=(f j).val:=by
  subst β
  cases eq_of_heq he
  cases eq_of_heq hij
  rfl

private theorem old_number {n B :ℕ} {Q :SpatialSource n} {κ :Type}
    (hQ :PurePowerReductionBounds.dimension (n+1) Q.degree≤2^B)
    (cs :List (Command Q B)) (older :List (IntegralMixedFramedHistoryScript.Instruction n B))
    (hi :Index (IntegralMixedFramedHistoryScript.Index (Fin 0) older) cs=κ)
    (w :IntegralMixedFramedHistoryScript.Index (Fin 0) older→κ)
    (hw :∀i,HEq (oldColumns cs i) (w i))
    (e :κ≃Fin (IntegralMixedFramedPhysicalIndex.arity (cs.map (wrap Q hQ)++older)))
    (he :HEq (IntegralMixedFramedPhysicalIndex.enumerate (cs.map (wrap Q hQ)++older)) e)
    (i :IntegralMixedFramedHistoryScript.Index (Fin 0) older):
    (e (w i)).val=(IntegralMixedFramedPhysicalIndex.enumerate older i).val:=by
  have HV:=equivalence_value_heq ((IntegralMixedFramedFixedContinuation.index_append Q hQ cs older).trans hi)
    (IntegralMixedFramedPhysicalIndex.enumerate (cs.map (wrap Q hQ)++older)) e he
    (IntegralMixedFramedPhysicalPersistence.embed (cs.map (wrap Q hQ)) older i) (w i)
    ((wrapped_old_heq hQ cs older i).trans (hw i))
  exact HV.symm.trans (IntegralMixedFramedPhysicalPersistence.enumerate_embed (cs.map (wrap Q hQ)) older i)

theorem observe_constructed_tuple {n S B b :ℕ} {P Q :SpatialSource n} {κ :Type}
    (initial :State P S B 0 (Fin 0))
    (hQ :PurePowerReductionBounds.dimension (n+1) Q.degree≤2^B)
    (older :List (IntegralMixedFramedHistoryScript.Instruction n B)) (ho :older.length≤S+1)
    (cs :List (Command Q B)) (room :older.length+cs.length≤S+1)
    (x :State Q S B b κ) (hb :older.length+cs.length=b)
    (hi :Index (IntegralMixedFramedHistoryScript.Index (Fin 0) older) cs=κ)
    (hx :HEq (continueRun (reframe (IntegralMixedFramedHistoryScript.run initial older ho) Q hQ) cs room) x)
    (z :κ→ℝ) (hz :∀i,(x.sampler.rows i).eval₂ (Int.castRingHom ℝ) z=0):
    Canonical x ∧∃u :ℕ→ℝ,∃e :κ≃Fin (IntegralMixedFramedPhysicalIndex.arity (cs.map (wrap Q hQ)++older)),
      (IntegralMixedFramedRunObservation.ofCommands initial (cs.map (wrap Q hQ)++older)
        (by simp only [List.length_append,List.length_map];omega)).Roots u ∧
      HEq (IntegralMixedFramedPhysicalIndex.enumerate (cs.map (wrap Q hQ)++older)) e ∧
      (∀i,u (e i).val=z i) ∧
      ∀i :Fin b,(IntegralMixedFramedRunObservation.ofCommands initial (cs.map (wrap Q hQ)++older)
        (by simp only [List.length_append,List.length_map];omega)).point u i.val=
          IntegralMixedFullBankPoint.point x z i:=by
  subst κ
  subst b
  cases eq_of_heq hx
  have HC:=full_continue_canonical (reframe (IntegralMixedFramedHistoryScript.run initial older ho) Q hQ)
    (IntegralMixedFramedHistoryScript.reframe_canonical _
      (IntegralMixedFramedHistoryScript.run_canonical initial (fun i=>Fin.elim0 i) older ho) Q hQ) cs room
  obtain ⟨u,y,hy,hu,hcol⟩:=tuple_append_observation initial Q hQ older ho cs room z hz
  obtain ⟨e,he,hecol⟩:=enumeration_from (IntegralMixedFramedFixedContinuation.index_append Q hQ cs older)
    (IntegralMixedFramedPhysicalIndex.enumerate (cs.map (wrap Q hQ)++older)) u y z hy hcol
  refine ⟨HC,u,e,hu,he,hecol,?_⟩
  intro i
  have HM :(cs.map (wrap Q hQ)++older).length=older.length+cs.length:=by
    simp only [List.length_append,List.length_map]
    omega
  let j :Fin (cs.map (wrap Q hQ)++older).length:=⟨i.val,by rw [HM];exact i.isLt⟩
  have HP:=IntegralMixedFramedRunObservation.point_actual initial (cs.map (wrap Q hQ)++older)
    (by simp only [List.length_append,List.length_map];omega) u j
  change _=IntegralMixedFullBankPoint.point _
    (fun k=>u (IntegralMixedFramedPhysicalIndex.enumerate (cs.map (wrap Q hQ)++older) k).val) j at HP
  rw [show (fun k=>u (IntegralMixedFramedPhysicalIndex.enumerate (cs.map (wrap Q hQ)++older) k).val)=y
    from funext hcol] at HP
  exact HP.trans (point_heq _ _ HM (IntegralMixedFramedFixedContinuation.index_append Q hQ cs older)
    (run_append initial Q hQ older ho cs room) y z hy j i rfl)

section Captures
variable {n S B m :ℕ} {P :SpatialSource n} {ι :Type} [Fintype ι]
variable {x :State P S B m ι} {d :Descriptor n m} {z :ι→ℝ}
  {φ :x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ} {values :Fin m→ℝ} {left right :Endpoint m}
  {hn :0<n} {hcap :IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B}
variable (R :NativePair x d z φ values left right hn hcap) (hk :d.labels.length<n+1)
  (g :Fin (n+1)) (hg :g∉(line d.frame (IntegralMixedChronologicalSweepFrame.next d hk)).frozen)

noncomputable def NativePair.levelIndex (side :Bool):Type:=
  Index ((Index ((Index ι R.result.commands⊕Variables (n+1))⊕Unit)
    (R.levelMidpointCommands hk g hg)⊕Variables (n+1))⊕Unit) (R.levelChildCommands hk g hg side)

theorem NativePair.level_index (side :Bool):
    Index ι (R.levelCommands hk g hg side)=
      Index ((Index ((Index ι R.result.commands⊕Variables (n+1))⊕Unit)
        (R.levelMidpointCommands hk g hg)⊕Variables (n+1))⊕Unit) (R.levelChildCommands hk g hg side):=by
  simp only [NativePair.levelCommands,List.append_assoc,List.singleton_append,IntegralMixedOptionalEndpoints.index_append,Index,NextIndex]

noncomputable def NativePair.levelPairColumn (side :Bool) (i :Index ι R.result.commands):
    R.levelIndex hk g hg side:=
  oldColumns (R.levelChildCommands hk g hg side)
    (Sum.inl (Sum.inl (oldColumns (R.levelMidpointCommands hk g hg) (Sum.inl (Sum.inl i)))))

theorem NativePair.level_old_heq (side :Bool) (i :ι):
    HEq (oldColumns (R.levelCommands hk g hg side) i)
      (R.levelPairColumn hk g hg side (oldColumns R.result.commands i)):=by
  let cM :Command P B:=.critical (R.levelMidpointData hk g hg).rule
  let cE :Command P B:=.critical (R.levelEndpointData hk g hg side).rule
  let mc:=R.levelMidpointCommands hk g hg
  let cc:=R.levelChildCommands hk g hg side
  let cs1:=cM::R.result.commands
  let cs2:=mc++cs1
  let cs3:=cE::cs2
  have HM:=old_columns_append mc cs1 i
  have HI:=IntegralMixedOptionalEndpoints.index_append ι mc cs1
  have HB:=old_column_heq HI _ _ HM cE
  have HC:=old_columns_heq (congrArg (fun κ :Type=>NextIndex κ cE) HI) _ _ HB cc
  have HT:=(old_columns_append cc cs3 i).trans HC
  have HCodes :R.levelCommands hk g hg side=cc++cs3:=by
    simp only [NativePair.levelCommands,cM,cE,mc,cc,cs1,cs2,cs3,List.append_assoc,List.cons_append,List.nil_append]
  rw [HCodes]
  convert HT using 1; rfl

noncomputable def NativePair.levelMidAnchorColumn (side :Bool) (i :Fin (n+1)):
    R.levelIndex hk g hg side:=
  oldColumns (R.levelChildCommands hk g hg side)
    (Sum.inl (Sum.inl (oldColumns (R.levelMidpointCommands hk g hg) (Sum.inl (ambient i)))))

noncomputable def NativePair.levelMidColumn (side :Bool) (k :Fin (R.orderedFree hk).length) (i :Fin (n+1)):
    R.levelIndex hk g hg side:=
  oldColumns (R.levelChildCommands hk g hg side)
    (Sum.inl (Sum.inl (blockColumn (insert (IntegralMixedChronologicalSweepFrame.next d hk) R.result.frame.frozen)
      (midpointDouble (IntegralMixedChronologicalSweepFrame.next d hk))
      (shiftRows (R.levelMidpointRows hk) 1) ⟨g,R.result.free_after_pair _ g hg⟩ (R.orderedFree hk) k i)))

noncomputable def NativePair.levelChildAnchorColumn (side :Bool) (i :Fin (n+1)):
    R.levelIndex hk g hg side:=
  oldColumns (R.levelChildCommands hk g hg side) (Sum.inl (ambient i))

noncomputable def NativePair.levelChildColumn (side :Bool) (k :Fin (R.orderedFree hk).length) (i :Fin (n+1)):
    R.levelIndex hk g hg side:=
  blockColumn (insert (IntegralMixedChronologicalSweepFrame.next d hk) R.result.frame.frozen)
    (fun _=>false) (shiftRows (R.levelEndpointRows hk side) 1)
    ⟨g,R.result.free_after_pair _ g hg⟩ (R.orderedFree hk) k i

variable (hp :m+R.result.commands.length≤S)
  (room :m+R.result.commands.length+1+(R.orderedFree hk).length≤S+1)
  (hroom :m+R.result.commands.length+1+(R.orderedFree hk).length≤S)
  (side :Bool)
  (childRoom :m+R.result.commands.length+1+(R.orderedFree hk).length+1+(R.orderedFree hk).length≤S+1)
  (pMID pChild :Fin (n+1)→ℝ)
  (A :R.result.MidpointCaptures hp (IntegralMixedChronologicalSweepFrame.next d hk) g g hg hg
    pMID (R.orderedFree hk) room)
  (E :R.LevelChildCaptures hk g hg hp pMID room A hroom side pChild childRoom)

theorem NativePair.captures_pair_raw (i :Index ι R.result.commands):
    E.captures.tuple (R.levelPairColumn hk g hg side i)=R.result.tuple i:=by
  exact (E.captures.old_raw _).trans ((E.anchor.old_raw _).trans
    ((A.captures.old_raw _).trans (A.anchor.old_raw i)))

theorem NativePair.captures_old_raw (i :ι):
    E.captures.tuple (R.levelPairColumn hk g hg side (oldColumns R.result.commands i))=z i:=
  (R.captures_pair_raw hk g hg hp room hroom side childRoom pMID pChild A E _).trans (R.result.old_raw i)

theorem NativePair.captures_mid_anchor (i :Fin (n+1)):
    E.captures.tuple (R.levelMidAnchorColumn hk g hg side i)^
      physical S (2^B) (m+R.result.commands.length)=pMID i:=by
  have H:=(E.captures.old_raw _).trans ((E.anchor.old_raw _).trans (A.captures.old_raw (Sum.inl (ambient i))))
  change E.captures.tuple (R.levelMidAnchorColumn hk g hg side i)=A.anchor.tuple (Sum.inl (ambient i)) at H
  rw [H]
  exact A.anchor.physical i

theorem NativePair.captures_mid_block (k :Fin (R.orderedFree hk).length) (i :Fin (n+1)):
    E.captures.tuple (R.levelMidColumn hk g hg side k i)^
      physical S (2^B) (m+R.result.commands.length+1+((R.orderedFree hk).length-1-k.val))=pMID i:=by
  let col :Index ((Index ι R.result.commands⊕Variables (n+1))⊕Unit) (R.levelMidpointCommands hk g hg):=blockColumn (insert (IntegralMixedChronologicalSweepFrame.next d hk) R.result.frame.frozen)
    (midpointDouble (IntegralMixedChronologicalSweepFrame.next d hk)) (shiftRows (R.levelMidpointRows hk) 1)
    ⟨g,R.result.free_after_pair _ g hg⟩ (R.orderedFree hk) k i
  have H:=(E.captures.old_raw (Sum.inl (Sum.inl col))).trans (E.anchor.old_raw col)
  change E.captures.tuple (R.levelMidColumn hk g hg side k i)=
    A.captures.tuple (blockColumn _ _ _ _ (R.orderedFree hk) k i) at H
  rw [H]
  exact A.captures.blocks k i

theorem NativePair.captures_child_anchor (i :Fin (n+1)):
    E.captures.tuple (R.levelChildAnchorColumn hk g hg side i)^
      physical S (2^B) (m+R.result.commands.length+1+(R.orderedFree hk).length)=pChild i:=by
  rw [show E.captures.tuple (R.levelChildAnchorColumn hk g hg side i)=E.anchor.tuple (Sum.inl (ambient i))
    from E.captures.old_raw _]
  exact E.anchor.physical i

theorem NativePair.captures_child_block (k :Fin (R.orderedFree hk).length) (i :Fin (n+1)):
    E.captures.tuple (R.levelChildColumn hk g hg side k i)^
      physical S (2^B) (m+R.result.commands.length+1+(R.orderedFree hk).length+1+
        ((R.orderedFree hk).length-1-k.val))=pChild i:=E.captures.blocks k i

structure NativePair.NaturalReadback {L :ℕ} (u :ℕ→ℝ)
    (e :R.levelIndex hk g hg side≃Fin L) (bank :ℕ→ℝ):Prop where
  endpoint_trace :GuardedProgram x hn hcap z φ values R.result.commands R.result.room R.result.codes
    R.result.tuple R.result.hom R.result.nextValues
  columns :∀i,u (e i).val=E.captures.tuple i
  bank_values :∀i :Fin (m+R.result.commands.length+1+(R.orderedFree hk).length+1+(R.orderedFree hk).length),
    bank i.val=IntegralMixedPointCompanion.values pChild
      (Fin.cons (pChild g) (IntegralMixedPointCompanion.values pMID (Fin.cons (pMID g) R.result.nextValues)
        (R.orderedFree hk))) (R.orderedFree hk) i

variable {L :ℕ} {u :ℕ→ℝ} {e :R.levelIndex hk g hg side≃Fin L} {bank :ℕ→ℝ}
  (N :R.NaturalReadback hk g hg hp room hroom side childRoom pMID pChild A E u e bank)

include N in
theorem NativePair.NaturalReadback.pair_raw (i :Index ι R.result.commands):
    u (e (R.levelPairColumn hk g hg side i)).val=R.result.tuple i:=
  (N.columns _).trans (R.captures_pair_raw hk g hg hp room hroom side childRoom pMID pChild A E i)

include N in
theorem NativePair.NaturalReadback.old_raw (i :ι):
    u (e (R.levelPairColumn hk g hg side (oldColumns R.result.commands i))).val=z i:=
  (N.columns _).trans (R.captures_old_raw hk g hg hp room hroom side childRoom pMID pChild A E i)

include N in
theorem NativePair.NaturalReadback.mid_anchor (i :Fin (n+1)):
    u (e (R.levelMidAnchorColumn hk g hg side i)).val^
      physical S (2^B) (m+R.result.commands.length)=pMID i:=by
  rw [N.columns]
  exact R.captures_mid_anchor hk g hg hp room hroom side childRoom pMID pChild A E i

include N in
theorem NativePair.NaturalReadback.mid_block (k :Fin (R.orderedFree hk).length) (i :Fin (n+1)):
    u (e (R.levelMidColumn hk g hg side k i)).val^
      physical S (2^B) (m+R.result.commands.length+1+((R.orderedFree hk).length-1-k.val))=pMID i:=by
  rw [N.columns]
  exact R.captures_mid_block hk g hg hp room hroom side childRoom pMID pChild A E k i

include N in
theorem NativePair.NaturalReadback.child_anchor (i :Fin (n+1)):
    u (e (R.levelChildAnchorColumn hk g hg side i)).val^
      physical S (2^B) (m+R.result.commands.length+1+(R.orderedFree hk).length)=pChild i:=by
  rw [N.columns]
  exact R.captures_child_anchor hk g hg hp room hroom side childRoom pMID pChild A E i

include N in
theorem NativePair.NaturalReadback.child_block (k :Fin (R.orderedFree hk).length) (i :Fin (n+1)):
    u (e (R.levelChildColumn hk g hg side k i)).val^
      physical S (2^B) (m+R.result.commands.length+1+(R.orderedFree hk).length+1+
        ((R.orderedFree hk).length-1-k.val))=pChild i:=by
  rw [N.columns]
  exact R.captures_child_block hk g hg hp room hroom side childRoom pMID pChild A E k i

end Captures

section Actual
variable {n S B :ℕ} {P Q :SpatialSource n} (initial :State P S B 0 (Fin 0))
  (hQ :PurePowerReductionBounds.dimension (n+1) Q.degree≤2^B)
  (older :List (IntegralMixedFramedHistoryScript.Instruction n B)) (ho :older.length≤S+1)
local notation "parent"=>reframe (IntegralMixedFramedHistoryScript.run initial older ho) Q hQ

theorem exists_guarded_proper_level (d :Descriptor n older.length) (hk :d.labels.length<n+1)
    (g :Fin (n+1)) (hg :g∉(line d.frame (IntegralMixedChronologicalSweepFrame.next d hk)).frozen)
    (HG :g.val=d.labels.length+1) (positive :0<n) (charge :ℕ)
    (hdegree :Q.degree=BoundedZeroSource.powerDegree charge)
    (hcapQ :IntegralMixedExceptionalBounds.auxiliaryCap (n+1) Q.degree≤2^B)
    (z :IntegralMixedFramedHistoryScript.Index (Fin 0) older→ℝ)
    (hz :∀i,((parent).sampler.rows i).eval₂ (Int.castRingHom ℝ) z=0)
    (φ :(parent).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hφ :∀i,φ ((parent).sampler.scalarPrefix.basis.generator i)=z ((parent).sampler.scalar i)^weights S (2^B) older.length i)
    (values :Fin older.length→ℝ) (H :∀i,φ ((parent).bank.numerator i)/((parent).bank.denominator i:ℝ)=values i)
    (horizon :older.length+2+2+2*(n-d.labels.length)≤S+1)
    (choices :IntegralMixedRelativeCuts.Choices parent (by omega)
      (cutRule parent d.frame (IntegralMixedChronologicalSweepFrame.next d hk) g hg) φ)
    (left right :Endpoint older.length)
    (HL :left.Allowed (jointEndpointSet parent (by omega) φ d.frame
      (IntegralMixedChronologicalSweepFrame.next d hk) g hg values choices))
    (HR :right.Allowed (jointEndpointSet parent (by omega) φ d.frame
      (IntegralMixedChronologicalSweepFrame.next d hk) g hg values choices))
    (hab :left.value values<right.value values)
    (M :MatchedSlabInterior parent (by omega) φ (line d.frame (IntegralMixedChronologicalSweepFrame.next d hk))
      (IntegralMixedChronologicalSweepFrame.next d hk) (Finset.mem_insert_self _ _) g hg values
      (left.value values) (right.value values) ⟨(left.value values+right.value values)/2,by constructor <;> linarith⟩)
    (i :IntegralMixedSelectedPhysicalFiber.physical (cutSource parent d.frame (IntegralMixedChronologicalSweepFrame.next d hk))
      (by omega) (cutRule parent d.frame (IntegralMixedChronologicalSweepFrame.next d hk) g hg) φ
        ((left.value values+right.value values)/2)):
    let rho:=FrozenCoordinateOrdering.permutation (line d.frame (IntegralMixedChronologicalSweepFrame.next d hk)).frozen
    let pMID:=M.curve i ((left.value values+right.value values)/2)∘rho.symm
    ∃R :NativePair parent d z φ values left right positive hcapQ,
      let hr :older.length+R.result.commands.length+2+2*(R.orderedFree hk).length≤S+1:=by
        have HC:=R.result.count
        have HQ:=R.orderedFree_length hk
        omega
      let hp :older.length+R.result.commands.length≤S:=by omega
      let room :older.length+R.result.commands.length+1+(R.orderedFree hk).length≤S+1:=by omega
      let hroom :older.length+R.result.commands.length+1+(R.orderedFree hk).length≤S:=by omega
      let childRoom :older.length+R.result.commands.length+1+(R.orderedFree hk).length+1+(R.orderedFree hk).length≤S+1:=by omega
      ∃A :R.result.MidpointCaptures hp (IntegralMixedChronologicalSweepFrame.next d hk) g g hg hg
        pMID (R.orderedFree hk) room,∀side,
        let pChild:=M.curve i (if side then right.value values else left.value values)∘rho.symm
        ∃E :R.LevelChildCaptures hk g hg hp pMID room A hroom side pChild childRoom,
        ∃u :ℕ→ℝ,∃e :R.levelIndex hk g hg side≃Fin (IntegralMixedFramedPhysicalIndex.arity
            ((R.levelCommands hk g hg side).map (wrap Q hQ)++older)),
          (IntegralMixedFramedRunObservation.ofCommands initial
            ((R.levelCommands hk g hg side).map (wrap Q hQ)++older)
            (by have HH:=R.level_room hk g hg side childRoom;simp only [List.length_append,List.length_map];omega)).Roots u ∧
          HEq (IntegralMixedFramedPhysicalIndex.enumerate ((R.levelCommands hk g hg side).map (wrap Q hQ)++older)) e ∧
          (∀j :IntegralMixedFramedHistoryScript.Index (Fin 0) older,
            u (IntegralMixedFramedPhysicalIndex.enumerate older j).val=z j) ∧
          R.NaturalReadback hk g hg hp room hroom side childRoom pMID pChild A E u e
            (fun j=>(IntegralMixedFramedRunObservation.ofCommands initial
              ((R.levelCommands hk g hg side).map (wrap Q hQ)++older)
              (by have HH:=R.level_room hk g hg side childRoom;simp only [List.length_append,List.length_map];omega)).point u j):=by
  dsimp only
  obtain ⟨R,G⟩:=optional_pair_guarded parent (by omega) (by omega) positive charge hdegree hcapQ d hk g hg HG
    z hz φ hφ values H choices left right HL HR
  refine ⟨R,?_⟩
  have HCpair:=R.result.count
  have HQ:=R.orderedFree_length hk
  have hpR :older.length+R.result.commands.length≤S:=by omega
  have roomR :older.length+R.result.commands.length+1+(R.orderedFree hk).length≤S+1:=by omega
  have hroomR :older.length+R.result.commands.length+1+(R.orderedFree hk).length≤S:=by omega
  have childRoomR :older.length+R.result.commands.length+1+(R.orderedFree hk).length+1+
      (R.orderedFree hk).length≤S+1:=by omega
  obtain ⟨A,HE⟩:=R.exists_matched_level_captures hk g hg (by omega) charge hdegree H hab M i
    hpR roomR hroomR childRoomR
  refine ⟨A,?_⟩
  intro side
  obtain ⟨E⟩:=HE side
  have HM :older.length+(R.levelCommands hk g hg side).length=
      older.length+R.result.commands.length+1+(R.orderedFree hk).length+1+(R.orderedFree hk).length:=by
    rw [R.levelCommands_length]
    omega
  have HS:=R.level_run_heq hk g hg hpR roomR hroomR side childRoomR
  have HO:=observe_constructed_tuple initial hQ older ho (R.levelCommands hk g hg side)
    (R.level_room hk g hg side childRoomR) (R.levelFinalState hk g hg hpR roomR hroomR side childRoomR) HM
    (R.level_index hk g hg side) HS E.captures.tuple E.captures.roots
  obtain ⟨HC,u,e,hu,hen,hcol,hpoint⟩:=HO
  refine ⟨E,u,e,hu,hen,?_,⟨G,hcol,?_⟩⟩
  · intro j
    have HN:=old_number hQ (R.levelCommands hk g hg side) older (R.level_index hk g hg side)
      (fun j=>R.levelPairColumn hk g hg side (oldColumns R.result.commands j)) (R.level_old_heq hk g hg side) e hen j
    have HR:=(hcol (R.levelPairColumn hk g hg side (oldColumns R.result.commands j))).trans
      (R.captures_old_raw hk g hg hpR roomR hroomR side childRoomR _ _ A E j)
    exact (congrArg u HN.symm).trans HR
  · intro j
    have HV:=IntegralMixedCanonicalBankPoint.quotient_eq (R.levelFinalState hk g hg hpR roomR hroomR side childRoomR) HC
      _ E.captures.hom E.captures.generators j
    exact (hpoint j).trans (HV.symm.trans (E.captures.quotients j))

end Actual
end LeanCanny.Geometry.IntegralMixedChronologicalEndpoint
