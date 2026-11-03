/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedJointGeneralSlabBounds
public import LeanCanny.Geometry.IntegralMixedReferencedMidpointFrame
/-! # Exact finite prefix bookkeeping for optional endpoint births

Commands and their parallel code list are newest first, as continueRun.
The chronological byte word is the reverse code list. No new interpreter
or sampling context is introduced.
-/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedOptionalEndpoints
open LeanCanny.Algebra LeanCanny.Encoding IntegralMixedHistory IntegralMixedCriticalSweep
open IntegralMixedFullHistoryScript IntegralMixedChosenLocalRealization
open LeanCanny.Geometry.IntegralMixedFrozenFrame
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]

def oldColumns : (cs : List (Command P B))→ι→Index ι cs
  | [],i=>i
  | c::cs,i=>oldColumn c (oldColumns cs i)

noncomputable def oldLift (x : State P S B m ι) : (cs : List (Command P B))→
    (room : m+cs.length≤S+1)→
    x.sampler.scalarPrefix.carrier→ₐ[ℤ](continueRun x cs room).sampler.scalarPrefix.carrier
  | [],_=>AlgHom.id ℤ _
  | c::cs,room=>(scalarLift (continueRun x cs (by simp only [List.length_cons] at room; omega))
      (by simp only [List.length_cons] at room; omega) c).comp
        (oldLift x cs (by simp only [List.length_cons] at room; omega))

noncomputable def Decodes (x : State P S B m ι) (hn : 0<n)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B) :
    (cs : List (Command P B))→(room : m+cs.length≤S+1)→List (List Bool)→Prop
  | [],_,codes=>codes=[]
  | _::_,_,[]=>False
  | c::cs,room,code::codes=>
      Decodes x hn hcap cs (by simp only [List.length_cons] at room; omega) codes ∧
      (IntegralMixedCausalUnitRecordBits.record P hn (m+cs.length) code hcap).template.command
        (commonDenominator (continueRun x cs (by simp only [List.length_cons] at room; omega)))
        (commonDenominator_ne_zero _)=c

def budget (n m B : ℕ):=IntegralMixedCutRecordConstructor.codeBudget n (m+2) B

theorem codeBudget_mono (n B u v : ℕ) (huv : u≤v) :
    IntegralMixedCutRecordConstructor.codeBudget n u B≤IntegralMixedCutRecordConstructor.codeBudget n v B :=by
  have HS:=Nat.size_le_size huv
  have HR : IntegralMixedCriticalRecordConstructor.rowBudget u≤IntegralMixedCriticalRecordConstructor.rowBudget v:=by
    unfold IntegralMixedCriticalRecordConstructor.rowBudget
    omega
  have HT:=Nat.mul_le_mul_right (n+1) (Nat.add_le_add_right (Nat.mul_le_mul_left 2 HR) 2)
  change IntegralMixedCriticalRecordConstructor.tableBudget n u≤IntegralMixedCriticalRecordConstructor.tableBudget n v at HT
  unfold IntegralMixedCutRecordConstructor.codeBudget IntegralMixedCutRecordConstructor.fieldBudget
  exact Nat.mul_le_mul_right 16 (by omega)

structure PairResult (x : State P S B m ι) (F : Frame n)
    (z : ι→ℝ) (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (values : Fin m→ℝ)
    (a b : ℝ) (hn : 0<n) (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B) where
  commands : List (Command P B)
  count : commands.length≤2
  room : m+commands.length≤S+1
  codes : List (List Bool)
  code_count : codes.length=commands.length
  code_size : ∀ code∈codes,code.length≤budget n m B
  decode : Decodes x hn hcap commands room codes
  tuple : Index ι commands→ℝ
  hom : (continueRun x commands room).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ
  roots : ∀ i,((continueRun x commands room).sampler.rows i).eval₂ (Int.castRingHom ℝ) tuple=0
  old_raw : ∀ i,tuple (oldColumns commands i)=z i
  old_hom : hom.comp (oldLift x commands room)=φ
  generators : ∀ i,hom ((continueRun x commands room).sampler.scalarPrefix.basis.generator i)=
    tuple ((continueRun x commands room).sampler.scalar i)^UniformIntegralPowerSchedule.weights S (2^B) (m+commands.length) i
  nextValues : Fin (m+commands.length)→ℝ
  quotients : ∀ i,hom ((continueRun x commands room).bank.numerator i)/
    ((continueRun x commands room).bank.denominator i:ℝ)=nextValues i
  frame : Frame n
  atomic : AtomicRows frame (m+commands.length)
  prefixFrozen : PrefixFrozen frame
  freeNormal : FreeNormal frame
  frozen : frame.frozen=F.frozen
  slice_eq : slice P frame nextValues=slice P F values
  left : Fin (m+commands.length)
  right : Fin (m+commands.length)
  left_value : nextValues left=a
  right_value : nextValues right=b

end LeanCanny.Geometry.IntegralMixedOptionalEndpoints
