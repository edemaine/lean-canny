/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.CoefficientHistoryPrefix
public import LeanCanny.Encoding.CoefficientMarkedIntegerBirth
public import LeanCanny.Algebra.IntegralMixedFramedStateTransport
/-! # Recursive symbolic prefixes of the actual marked integer leaves

The input list contains original leaf indices, newest first. Its formal
carrier, basis, bank and physical rows are constructed independently of the
radius. Every radius has a derived map to the actual native integer run.
-/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedPreludePrefix
open LeanCanny.Algebra LeanCanny.Computation IntegralMixedHistory Polynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n:List Bool→ℕ} {t:List Bool→LeanCanny.ETR.Term}
  (hn:UnaryFn n) (ht:(fun q=>(t q).toData.toBits)∈FP) (ha:∀q,(t q).arity≤n q)

def Index :List ℕ→Type
  | []=>Fin 0
  | _::is=>Index is⊕Unit

instance indexFintype:(is:List ℕ)→Fintype (Index is)
  | []=>inferInstanceAs (Fintype (Fin 0))
  | _::is=>by
    change Fintype (Index is⊕Unit)
    letI:=indexFintype is
    infer_instance

noncomputable def build (ctx:List Bool) (S:ℕ):(is:List ℕ)→
    CoefficientHistoryPrefix.Prefix ℤ[X] S (CoefficientMarkedIntegerBirth.width hn ht ha ctx) is.length (Index is)
  | []=>CoefficientHistoryPrefix.base (R:=ℤ[X]) S (CoefficientMarkedIntegerBirth.width hn ht ha ctx)
  | i::is=>
    let F:=build ctx S is
    CoefficientHistoryPrefix.scalarStep F
      ((CoefficientMarkedIntegerBirth.leaf hn ht ha ctx i).map (algebraMap ℤ[X] F.carrier))
      (CoefficientMarkedIntegerBirth.leaf hn ht ha ctx i).natDegree
      (CoefficientMarkedIntegerBirth.leaf hn ht ha ctx i).leadingCoeff

noncomputable def initial (ctx:List Bool) (radius:List Bool→ℕ) (S:ℕ):
    State (IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t radius ctx) S
      (CoefficientMarkedIntegerBirth.width hn ht ha ctx) 0 (Fin 0):=
  IntegralMixedHistory.base (IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t radius ctx)
    (IntegralHistorySampler.base S (2^CoefficientMarkedIntegerBirth.width hn ht ha ctx))
    (IntegralMixedFramedHistoryFamilyBits.initial
      (IntegralMixedAuxiliaryMarkedIntegerPlan.parameters hn ht ha)
      (IntegralMixedAuxiliaryMarkedIntegerPlan.plan hn ht ha radius) ctx).critical_cap

noncomputable def nativeRun (ctx:List Bool) (radius:List Bool→ℕ) (S:ℕ):
    (is:List ℕ)→is.length≤S+1→
    State (IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t radius ctx) S
      (CoefficientMarkedIntegerBirth.width hn ht ha ctx) is.length (Index is)
  | [],_=>initial hn ht ha ctx radius S
  | i::is,h=>CoefficientMarkedIntegerBirth.nativeStep hn ht ha ctx i radius
      (nativeRun ctx radius S is (by simp only [List.length_cons] at h;omega))
      (by simp only [List.length_cons] at h;omega)

theorem specializes (ctx:List Bool) (radius:List Bool→ℕ) (S:ℕ)
    (is:List ℕ) (h:is.length≤S+1):
    ∃ψ:(build hn ht ha ctx S is).carrier→+*(nativeRun hn ht ha ctx radius S is h).sampler.scalarPrefix.carrier,
      CoefficientCoordinateBasis.Specializes (Polynomial.evalRingHom ((2:ℤ)^radius ctx)) ψ
        (build hn ht ha ctx S is).basis
        (CoefficientCoordinateBasis.ofIntegral (nativeRun hn ht ha ctx radius S is h).sampler.scalarPrefix.basis) ∧
      CoefficientHeightBank.Specializes (Polynomial.evalRingHom ((2:ℤ)^radius ctx)) ψ
        (build hn ht ha ctx S is).bank (CoefficientHeightBank.ofState (nativeRun hn ht ha ctx radius S is h)) ∧
      (∀j,MvPolynomial.map (Polynomial.evalRingHom ((2:ℤ)^radius ctx))
        ((build hn ht ha ctx S is).rows j)=(nativeRun hn ht ha ctx radius S is h).sampler.rows j) ∧
      (build hn ht ha ctx S is).scalar=(nativeRun hn ht ha ctx radius S is h).sampler.scalar:=by
  induction is with
  | nil=>
    refine ⟨Polynomial.evalRingHom ((2:ℤ)^radius ctx),?_,?_,?_,?_⟩
    · exact CoefficientCoordinateBasis.base_specializes _ _
    · constructor
      · intro z
        rfl
      · intro j
        exact Fin.elim0 j
      · intro j
        exact Fin.elim0 j
    · intro j
      exact Fin.elim0 j
    · funext j
      exact Fin.elim0 j
  | cons i is ih=>
    have ht0:is.length≤S+1:=by simp only [List.length_cons] at h;omega
    have hm:is.length≤S:=by simp only [List.length_cons] at h;omega
    obtain ⟨ψ,HBasis,HBank,HRows,HSlots⟩:=ih ht0
    let F:=build hn ht ha ctx S is
    let x:=nativeRun hn ht ha ctx radius S is ht0
    refine ⟨CoefficientMarkedIntegerBirth.specialize hn ht ha ctx i radius F.bank x hm ψ HBank,?_,?_,?_,?_⟩
    · exact CoefficientMarkedIntegerBirth.basis_specializes hn ht ha ctx i radius F.bank F.basis x hm ψ HBank HBasis
    · exact CoefficientMarkedIntegerBirth.bank_specializes hn ht ha ctx i radius F.bank x hm ψ HBank
    · have HR:=CoefficientMarkedIntegerBirth.rows_map_native hn ht ha ctx i radius F.bank F.basis x hm ψ HBank HBasis F.rows HRows
      change (∀j,MvPolynomial.map (Polynomial.evalRingHom ((2:ℤ)^radius ctx))
        (CoefficientCanonicalScalarAppend.rows S F.rows F.scalar F.basis
          (CoefficientMarkedIntegerBirth.polynomial hn ht ha ctx i (A:=F.carrier))
          (CoefficientMarkedIntegerBirth.leaf hn ht ha ctx i).natDegree j)=_)
      change F.scalar=x.sampler.scalar at HSlots
      rw [HSlots]
      exact congrFun HR
    · change (Fin.cons (Sum.inr ()) (fun j=>Sum.inl (F.scalar j)) :
          Fin (is.length+1)→Index is⊕Unit)=
        (Fin.cons (Sum.inr ()) (fun j=>Sum.inl (x.sampler.scalar j)) :
          Fin (is.length+1)→Index is⊕Unit)
      change F.scalar=x.sampler.scalar at HSlots
      rw [HSlots]

noncomputable def instruction (ctx:List Bool) (radius:List Bool→ℕ) (i:ℕ):
    IntegralMixedFramedHistoryScript.Instruction
      (IntegralMixedAuxiliaryMarkedIntegerSource.number n ctx+3)
      (CoefficientMarkedIntegerBirth.width hn ht ha ctx) where
  source:=IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t radius ctx
  source_cap:=(initial hn ht ha ctx radius 0).critical_cap
  command:=.integer ((IntegralMixedAuxiliaryMarkedIntegerSource.source hn ht ha radius).polynomial
    (pair ctx (BinaryNatCode.encode i)))
    (IntegralMixedAuxiliaryMarkedIntegerSource.nonzero hn ht ha radius _)
    (((IntegralMixedAuxiliaryMarkedIntegerSource.source hn ht ha radius).degree_bound _).trans
      (IntegralMixedAuxiliaryMarkedIntegerPlan.source_degree_cap hn ht ha radius ctx i))

noncomputable def commands (ctx:List Bool) (radius:List Bool→ℕ) (is:List ℕ):=
  is.map (instruction hn ht ha ctx radius)

theorem commands_length (ctx:List Bool) (radius:List Bool→ℕ) (is:List ℕ):
    (commands hn ht ha ctx radius is).length=is.length:=List.length_map _

theorem index_eq (ctx:List Bool) (radius:List Bool→ℕ) (is:List ℕ):
    Index is=IntegralMixedFramedHistoryScript.Index (Fin 0) (commands hn ht ha ctx radius is):=by
  induction is with
  | nil=>rfl
  | cons i is ih=>
    simpa only [Index,commands,List.map_cons,IntegralMixedFramedHistoryScript.Index,instruction,
      IntegralMixedFullHistoryScript.NextIndex] using congrArg (fun I:Type=>I⊕Unit) ih

/-- The target recursion is the literal framed interpreter on the same leaves. -/
theorem nativeRun_framed (ctx:List Bool) (radius:List Bool→ℕ) (S:ℕ)
    (is:List ℕ) (h:is.length≤S+1):
    HEq (nativeRun hn ht ha ctx radius S is h)
      (reframe (IntegralMixedFramedHistoryScript.run (initial hn ht ha ctx radius S)
        (commands hn ht ha ctx radius is) (by rw [commands_length];exact h))
        (IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t radius ctx)
        (initial hn ht ha ctx radius S).critical_cap):=by
  induction is with
  | nil=>rfl
  | cons i is ih=>
    have ht0:is.length≤S+1:=by simp only [List.length_cons] at h;omega
    have hm:is.length≤S:=by simp only [List.length_cons] at h;omega
    let x:=nativeRun hn ht ha ctx radius S is ht0
    let y:=reframe (IntegralMixedFramedHistoryScript.run (initial hn ht ha ctx radius S)
      (commands hn ht ha ctx radius is) (by rw [commands_length];exact ht0))
      (IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t radius ctx) (initial hn ht ha ctx radius S).critical_cap
    have H:=IntegralMixedFramedStateTransport.step_reframe_heq x y
      (commands_length hn ht ha ctx radius is).symm (index_eq hn ht ha ctx radius is) (ih ht0)
      hm (by rw [commands_length];exact hm) (instruction hn ht ha ctx radius i).command
      (IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t radius ctx) (initial hn ht ha ctx radius S).critical_cap
    change HEq (IntegralMixedFullHistoryScript.step x hm (instruction hn ht ha ctx radius i).command)
      (reframe (IntegralMixedFullHistoryScript.step y (by rw [commands_length];exact hm)
        (instruction hn ht ha ctx radius i).command)
        (IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t radius ctx) (initial hn ht ha ctx radius S).critical_cap)
    have HE : reframe (IntegralMixedFullHistoryScript.step x hm (instruction hn ht ha ctx radius i).command)
        (IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t radius ctx) (initial hn ht ha ctx radius S).critical_cap=
        IntegralMixedFullHistoryScript.step x hm (instruction hn ht ha ctx radius i).command:=reframe_same _
    exact (heq_of_eq HE).symm.trans H

end LeanCanny.Encoding.CoefficientMarkedPreludePrefix
