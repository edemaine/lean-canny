/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedPhysicalCriticalAnchor
public import LeanCanny.Encoding.IntegralFramedPhysicalCriticalGuardTest
public import LeanCanny.Geometry.IntegralMixedFramedCriticalQuotients
/-! # The creating hom reads the same retained quotients as the full word -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedPhysicalCriticalReadback
open LeanCanny.Algebra LeanCanny.Geometry IntegralCriticalHistoryTask IntegralMixedHistory
open IntegralMixedFramedHistoryScript
open IntegralMixedFramedHistoryFamilyBits (Plan family initial commands)
open IntegralMixedFramedPhysicalIndex (enumerate)
open IntegralMixedFramedRunObservation (ofCommands)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem indexedPoint_key_cast (G :IntegralMixedCutSource.Family)
    (a :List Bool→ℕ) (e :∀k,G.physical k≃Fin (a k))
    (k l :List Bool) (hk :k=l) (b :ℕ) (h :b=a k) (h' :b=a l) (z :Fin (a l)→ℝ)
    (i :Fin (G.birth k)) (j :Fin (G.birth l)) (hij :i.val=j.val) :
    IntegralMixedFullBankPoint.indexedPoint (G.state k) ((e k).trans (finCongr h.symm))
      (fun t=>z (Fin.cast h' t)) i=IntegralMixedFullBankPoint.indexedPoint (G.state l) (e l) z j :=by
  cases hk
  have HI :i=j:=Fin.ext hij
  cases HI
  cases h
  rfl

theorem header_packet (P :Parameters) (D :Plan P) (H :IntegralMixedFramedHistoryFamilyBits.Data P D)
    (T :IntegralMixedHeaderTablesBits.Tables) (hr :IntegralMixedFramedHeaderBits.Represents P D H T)
    (key :List Bool→List Bool) (stage :List Bool→ℕ) (c d :List Bool) (b :ℕ)
    (hb :stage (pair c d)=b) :
    IntegralMixedFramedCriticalGuardBits.header T (IntegralFramedPhysicalCriticalGuardTest.keyDatum key) stage (pair c d)=
      IntegralMixedCommandHeaderBits.command (IntegralMixedFramedRootPullback.instructionAt P D (pairFst (key c)) b).command:=by
  have HK :IntegralFramedPhysicalCriticalGuardTest.keyDatum key (pair c d)=key c:=congrArg key (pairFst_pair c d)
  have HI:=IntegralMixedFramedRootPullback.instructionAt_congr P D _ _ _ _ (congrArg pairFst HK) hb
  have HE:=IntegralMixedFramedRootPullback.instruction_read (fun _ _ I=>IntegralMixedCommandHeaderBits.command I.command) _ _
    (congrArg P.ambient (congrArg pairFst HK)) (congrArg P.width (congrArg pairFst HK)) HI
  exact (IntegralMixedFramedCriticalGuardBits.header_actual P D H T hr _ _ _).trans HE

theorem actualPoint_indexed (P :Parameters) (D :Plan P) (H :IntegralMixedFramedHistoryFamilyBits.Data P D)
    (T :IntegralMixedHeaderTablesBits.Tables) (hr :IntegralMixedFramedHeaderBits.Represents P D H T)
    (key :List Bool→List Bool) (stage :List Bool→ℕ) (q :List Bool)
    (ha :IntegralMixedFramedCriticalGuardBits.Active P T key stage q)
    (z :Fin (IntegralMixedFramedPhysicalIndex.arity (commands P D (key q)))→ℝ) :
    IntegralMixedFramedCriticalGuard.actualPoint P D H T hr key stage q ha
      (z∘Fin.cast (IntegralMixedFramedCriticalGuardBits.count_actual P D H T hr key q))=
    IntegralMixedFullBankPoint.indexedPoint ((family P D H).state (key q))
      (enumerate (commands P D (key q))) z
      ⟨IntegralMixedFramedCriticalGuardBits.age P key stage q,
        IntegralMixedFramedCriticalGuardBits.age_lt P D H T key stage q ha⟩ :=by
  unfold IntegralMixedFramedCriticalGuard.actualPoint IntegralMixedFramedCriticalGuard.fullEquiv
    IntegralMixedFullBankPoint.indexedPoint IntegralMixedFullBankPoint.point IntegralMixedCanonicalBankPoint.point
  congr 2

private theorem point_congr {n S B :ℕ} {Q :SpatialSource n}
    (x :State Q S B 0 (Fin 0)) (cs ds :List (Instruction n B))
    (hc :cs.length≤S+1) (hd :ds.length≤S+1) (he :cs=ds) (z :ℕ→ℝ) (i :ℕ) :
    (ofCommands x cs hc).point z i=(ofCommands x ds hd).point z i:=by cases he;rfl

variable (P :Parameters) (D :Plan P) (H :IntegralMixedFramedHistoryFamilyBits.Data P D)
  (L F C :List Bool→ℕ) (hs :IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
  (key :List Bool→List Bool) (hpos :∀q,0<(family P D H).birth (key q))
  (q w :List Bool) (hv :SquareSampleCompleteVertices.Valid
    (IntegralFramedPhysicalSquare.input P D H L F C hs key hpos) q w)
  (Q :SpatialSource (P.ambient (pairFst (key q))))
  (hQ :PurePowerReductionBounds.dimension (P.ambient (pairFst (key q))+1) Q.degree≤2^P.width (pairFst (key q)))
  (r :CriticalRule (P.ambient (pairFst (key q))))
  (newer older :List (Instruction (P.ambient (pairFst (key q))) (P.width (pairFst (key q)))))
  (hcs :commands P D (key q)=newer++⟨Q,hQ,.critical r⟩::older)
local notation "x"=>oldState P D H key q Q hQ r newer older hcs

theorem quotient_full
    (φ :(x).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hφ :∀i,φ ((x).sampler.scalarPrefix.basis.generator i)=
      tuple P D H L F C hs key hpos q w hv (enumerate older ((x).sampler.scalar i)).val^
        UniformIntegralPowerSchedule.weights (P.cap (pairFst (key q))+1) (2^P.width (pairFst (key q))) older.length i)
    (i :Fin older.length) :
    φ ((x).bank.numerator i)/((x).bank.denominator i:ℝ)=
      IntegralFramedPhysicalSquare.point P D H L F C hs key hpos q w hv
        ⟨newer.length+1+i.val,by
          change newer.length+1+i.val<(commands P D (key q)).length
          rw [hcs,List.length_append,List.length_cons]
          omega⟩ :=by
  let z:=tuple P D H L F C hs key hpos q w hv
  have HO :=(older_room P D H key q Q hQ r newer older hcs).trans (Nat.le_succ _)
  have HC :(commands P D (key q)).length≤P.cap (pairFst (key q))+1+1:=
    ((family P D H).birth_bound (key q)).trans (Nat.le_succ _)
  have HE :commands P D (key q)=(newer++[⟨Q,hQ,.critical r⟩])++older:=by
    simpa only [List.append_assoc,List.singleton_append] using hcs
  have HT :((newer++[Instruction.mk Q hQ (.critical r)])++older).length≤P.cap (pairFst (key q))+1+1:=HE ▸ HC
  have HR:=IntegralMixedFramedCriticalReadback.quotient_of_generators
    (initial P D (pairFst (key q))) hQ older HO z φ hφ i
  have HP:=IntegralMixedFramedCriticalReadback.point_append
    (initial P D (pairFst (key q))) (newer++[Instruction.mk Q hQ (.critical r)]) older HT HO z i
  have HN :(newer++[Instruction.mk Q hQ (.critical r)]).length+i.val=newer.length+1+i.val:=by
    simp only [List.length_append,List.length_singleton]
  rw [HN] at HP
  have HH:=point_congr (initial P D (pairFst (key q))) (commands P D (key q)) _ HC HT HE z
    (newer.length+1+i.val)
  refine HR.trans (HP.symm.trans (HH.symm.trans ?_))
  have HZ :z=IntegralFramedPhysicalSquare.naturalPoint P D H L F C hs key hpos q w hv:=by
    funext k
    rfl
  rw [HZ]
  exact IntegralFramedPhysicalPrefixPoint.full_point P D H L F C hs key hpos q w hv
    ⟨newer.length+1+i.val,by rw [hcs,List.length_append,List.length_cons];omega⟩

end LeanCanny.Encoding.IntegralFramedPhysicalCriticalReadback
