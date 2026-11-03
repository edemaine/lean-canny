/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedOptionalSlabEndpoints
public import LeanCanny.Geometry.IntegralMixedReferencedMidpointRealization
public import LeanCanny.Encoding.IntegralMixedJointRecordBudgetNative
/-! # Optional retained endpoints and one physical anchor use at most three births -/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedOptionalEndpoints
open LeanCanny.Algebra LeanCanny.Encoding IntegralMixedHistory IntegralMixedCriticalSweep
open IntegralMixedFullHistoryScript IntegralMixedChosenLocalRealization
open LeanCanny.Geometry.IntegralMixedFrozenFrame
open IntegralHistorySampler UniformIntegralPowerSchedule FlatAffineCriticalStage
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]

def byteBudget (n m B : ℕ):=(2*budget n m B+2)*3

theorem realize_slab (x : State P S B m ι) (hm : m≤S) (hroom : m+2≤S) (hn : 0<n)
    (charge : ℕ) (hdegree : P.degree=BoundedZeroSource.powerDegree charge)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B)
    (F : Frame n) (HF : FreeNormal F) (HA : AtomicRows F m) (HP : PrefixFrozen F)
    (h g j : Fin (n+1)) (hfirst : h.val=F.frozen.card) (hh : h∉F.frozen)
    (hg : g∉insert h F.frozen) (hj : j∉insert h F.frozen)
    (z : ι→ℝ) (hz : ∀ i,(x.sampler.rows i).eval₂ (Int.castRingHom ℝ) z=0)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hφ : ∀ i,φ (x.sampler.scalarPrefix.basis.generator i)=z (x.sampler.scalar i)^weights S (2^B) m i)
    (values : Fin m→ℝ) (H : ∀ i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (old : IntegralMixedRelativeCuts.Choices x hm (cutRule x F h g hg) φ)
    (left right : Endpoint m)
    (HL : left.Allowed (jointEndpointSet x hm φ F h g hg values old))
    (HR : right.Allowed (jointEndpointSet x hm φ F h g hg values old))
    (point : Fin (n+1)→ℝ) (hp : point∈slice P F values)
    (hmid : point h=(left.value values+right.value values)/2)
    (hgrad : ∀ i,i∉insert h F.frozen→i≠g→
      (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial P.low P.leading P.degree)).eval₂
        (Int.castRingHom ℝ) point=0) :
    ∃ R : PairResult x F z φ values (left.value values) (right.value values) hn hcap,
      R.commands.length=left.freshCount+right.freshCount ∧
      ∃ hg' : g∉insert h R.frame.frozen,∃ hj' : j∉insert h R.frame.frozen,
      let d:=referencedMidpointData R.atomic h R.left R.right g j hg' hj'
      let cs:=(.critical d.rule : Command P B)::R.commands
      ∃ room : m+cs.length≤S+1,
        cs.length=left.freshCount+right.freshCount+1 ∧
        cs.length≤3 ∧ (d.code::R.codes).length=cs.length ∧ Decodes x hn hcap cs room (d.code::R.codes) ∧
        (WordList.encode (d.code::R.codes).reverse).length≤byteBudget n m B ∧
        let born:=continueRun x cs room
        ∃ y : Index ι cs→ℝ,∃ ψ : born.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
          (∀ i,(born.sampler.rows i).eval₂ (Int.castRingHom ℝ) y=0) ∧
          (∀ i,y (oldColumns cs i)=z i) ∧
          (∀ i,y (Sum.inl (ambient i))^physical S (2^B) (m+R.commands.length)=point i) ∧
          ψ.comp (oldLift x cs room)=φ ∧
          (∀ i,ψ (born.sampler.scalarPrefix.basis.generator i)=y (born.sampler.scalar i)^weights S (2^B) (m+cs.length) i) ∧
          (∀ i,ψ (born.bank.numerator i)/(born.bank.denominator i:ℝ)=
            (Fin.cons (point j) R.nextValues : Fin (m+cs.length)→ℝ) i) ∧
          ψ (born.bank.numerator R.left.succ)/(born.bank.denominator R.left.succ:ℝ)=left.value values ∧
          ψ (born.bank.numerator R.right.succ)/(born.bank.denominator R.right.succ:ℝ)=right.value values :=by
  obtain ⟨R,Hbirthcount⟩:=realize_pair x hm (by omega) hn charge hdegree hcap F HF HA HP h hh g hg
    z hz φ hφ values H old left right HL HR
  have hg' : g∉insert h R.frame.frozen:=by rw [R.frozen]; exact hg
  have hj' : j∉insert h R.frame.frozen:=by rw [R.frozen]; exact hj
  have hh' : h∉R.frame.frozen:=by rw [R.frozen]; exact hh
  have hfirst' : h.val=R.frame.frozen.card:=by rw [R.frozen]; exact hfirst
  have hp' : point∈slice P R.frame R.nextValues:=by rw [R.slice_eq]; exact hp
  have hmid' : point h=(R.nextValues R.left+R.nextValues R.right)/2:=by
    rw [R.left_value,R.right_value]
    exact hmid
  have hgrad' : ∀ i,i∉insert h R.frame.frozen→i≠g→
      (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial P.low P.leading P.degree)).eval₂
        (Int.castRingHom ℝ) point=0:=by rw [R.frozen]; exact hgrad
  have hbirth : m+R.commands.length≤S:=by have HC:=R.count; omega
  obtain ⟨hsize,hcode,y,ψ,hy,hold,hphysical,hrestrict,hψ,Hvalues⟩:=
    referenced_midpoint_realize (continueRun x R.commands R.room) hbirth hn charge hdegree hcap
      R.atomic R.prefixFrozen h hfirst' hh' R.left R.right g j hg' hj'
      R.tuple R.roots R.hom R.generators R.nextValues R.quotients point hp' hmid' hgrad'
  let d:=referencedMidpointData R.atomic h R.left R.right g j hg' hj'
  let cs:=(.critical d.rule : Command P B)::R.commands
  have hcs : m+cs.length≤S+1:=by dsimp only [cs]; simp only [List.length_cons]; omega
  have Hsize : d.code.length≤budget n m B:=hsize.trans (codeBudget_mono n B _ (m+2) (by have HC:=R.count; omega))
  have Hcount : (d.code::R.codes).reverse.length≤3:=by
    simp only [List.length_reverse,List.length_cons,R.code_count]
    have HC:=R.count
    omega
  have Hwords : ∀ code∈(d.code::R.codes).reverse,code.length≤budget n m B:=by
    intro code hc
    simp only [List.mem_reverse,List.mem_cons] at hc
    rcases hc with rfl|hc
    · exact Hsize
    · exact R.code_size code hc
  have Hbytes : (WordList.encode (d.code::R.codes).reverse).length≤byteBudget n m B:=
    (WordList.length_le _ _ Hwords).trans (Nat.mul_le_mul_left _ Hcount)
  refine ⟨R,Hbirthcount,hg',hj',hcs,?_,?_,?_,⟨R.decode,hcode⟩,Hbytes,y,ψ,hy,?_,hphysical,?_,hψ,Hvalues,?_,?_⟩
  · simp only [List.length_cons,Hbirthcount]
  · simp only [List.length_cons]
    have HC:=R.count
    omega
  · simp only [List.length_cons,R.code_count]
  · intro i
    exact (hold (oldColumns R.commands i)).trans (R.old_raw i)
  · change (ψ.comp (scalarLift (continueRun x R.commands R.room) hbirth (.critical d.rule))).comp
      (oldLift x R.commands R.room)=φ
    exact (congrArg (fun χ=>χ.comp (oldLift x R.commands R.room)) hrestrict).trans R.old_hom
  · exact (Hvalues R.left.succ).trans R.left_value
  · exact (Hvalues R.right.succ).trans R.right_value

theorem physical_columns_le (cs : List (Command P B)) (hc : cs.length≤3) :
    Fintype.card (Index ι cs)≤Fintype.card ι+3*(2*n+4) :=by
  rw [physical_arity]
  have HK : criticalCount cs≤cs.length:=List.countP_le_length
  calc
    _≤Fintype.card ι+3+(2*n+3)*3:=by
      exact Nat.add_le_add (Nat.add_le_add_left hc _) (Nat.mul_le_mul_left _ (HK.trans hc))
    _=Fintype.card ι+3*(2*n+4):=by ring

omit [Fintype ι] in
theorem byteBudget_unary {n birth B : List Bool→ℕ} (hn : UnaryFn n) (hm : BinaryFn birth) (hB : UnaryFn B) :
    UnaryFn (fun q=>byteBudget (n q) (birth q) (B q)) :=by
  have H:=IntegralMixedCutRecordConstructor.codeBudget_unary hn (hm.add (BinaryFn.const 2)) hB
  exact (((UnaryFn.const 2).mul H).add (UnaryFn.const 2)).mul (UnaryFn.const 3)

end LeanCanny.Geometry.IntegralMixedOptionalEndpoints
