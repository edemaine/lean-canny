/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralPolynomialWindowTarskiSelection
public import LeanCanny.Encoding.IntegralPolynomialWindowTarskiCatalogue
public import LeanCanny.Algebra.SingleRootSignCount
/-! # Exact finite interval predicates at one actual source/center/endpoint

Canonical control writers retain the same raw source and the same real tuple.
The zero head is rejected; a nonzero constant head is handled explicitly.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralPolynomialWindowTarski
open LeanCanny.Algebra LeanCanny.Computation Polynomial MvPolynomial PrincipalSubresultant Set
open IntegralFramedBankPolynomialModel (Source)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem lifted_head_map {n:ℕ} (p:Polynomial (MvPolynomial (Fin n) ℤ)) (v:Fin (n+1) → ℝ):
    (p.map (MvPolynomial.rename Fin.succ).toRingHom).map (MvPolynomial.eval₂Hom (Int.castRingHom ℝ) v)=
      p.map (MvPolynomial.eval₂Hom (Int.castRingHom ℝ) (fun i=>v i.succ)):=by
  ext i
  simp only [Polynomial.coeff_map]
  change MvPolynomial.eval₂ (Int.castRingHom ℝ) v (MvPolynomial.rename Fin.succ (p.coeff i)) =
    MvPolynomial.eval₂ (Int.castRingHom ℝ) (fun i=>v i.succ) (p.coeff i)
  rw [MvPolynomial.eval₂_rename]
  rfl
def intervalCastValues {n m:ℕ} (h:n=m) (v:Fin m → ℝ):Fin n → ℝ:=fun i=>v (Fin.cast h i)
private theorem intervalCastValues_heq {n m:ℕ} (h:n=m) (v:Fin m → ℝ):HEq (intervalCastValues h v) v:=by cases h;rfl

variable (S:Source) (N:List Bool → ℕ) (hd:∀c,S.arity c=N c+1)
local instance windowIntervalArityNeZero (q:List Bool):NeZero (arity N q):=⟨by unfold arity;omega⟩

noncomputable def baseHead (c:List Bool) (a:Fin (N c) → ℝ):ℝ[X]:=
  (IntegralPolynomialRadiusReader.polynomial S N hd c).map (MvPolynomial.eval₂Hom (Int.castRingHom ℝ) a)
noncomputable def realWindow (b:ℝ):ℝ[X]:=Polynomial.X*(Polynomial.C b-Polynomial.X)

theorem head_radius_map (q:List Bool) (v:Fin (arity N q) → ℝ):realHead S N hd q v=
    (IntegralPolynomialRadiusReader.polynomial S N hd (original q)).map
      (MvPolynomial.eval₂Hom (Int.castRingHom ℝ) (fun i=>v i.succ)):=by
  unfold realHead head
  exact lifted_head_map _ v

theorem head_radius_eval (q:List Bool) (v:Fin (arity N q) → ℝ) (r:ℝ):
    (realHead S N hd q v).eval r=(S.polynomial (original q)).eval₂ (Int.castRingHom ℝ)
      (fun i=>(Fin.cons r (fun j=>v j.succ):Fin (N (original q)+1) → ℝ) (Fin.cast (hd (original q)) i)):=by
  rw [head_radius_map]
  exact IntegralPolynomialRadiusReader.specialization S N hd _ _ r

theorem query_radius_map (q:List Bool) (v:Fin (arity N q) → ℝ):
    realQuery N q v=(realWindow (v 0))^(moment q):=by
  unfold realQuery query window realWindow
  simp only [Polynomial.map_pow,Polynomial.map_mul,Polynomial.map_sub,Polynomial.map_X,Polynomial.map_C,
    MvPolynomial.coe_eval₂Hom,MvPolynomial.eval₂_X]

theorem real_seed_eq (q:List Bool) (v:Fin (arity N q) → ℝ):realSeed S N hd q v=
    PseudoRemainder.seed (realHead S N hd q v) (realQuery N q v) (degree S q) (bound S q):=by
  unfold realSeed realHead realQuery seed
  exact (PseudoRemainder.seed_map _ _ _ _ _).symm

noncomputable abbrev intervalControl:=IntegralPolynomialWindowTarskiCatalogue.control

theorem interval_control_original (c:List Bool) (d s:ℕ) (m:Bool):original (intervalControl c d s m)=c:=by
  simp only [original,FormulaSignSlotRadialRadiusTarskiFamily.original,intervalControl,
    IntegralPolynomialWindowTarskiCatalogue.control,pairFst_pair]
theorem interval_control_dimension (c:List Bool) (d s:ℕ) (m:Bool):arity N (intervalControl c d s m)=N c+1:=by
  unfold arity
  rw [interval_control_original]
noncomputable def values (c:List Bool) (d s:ℕ) (m:Bool) (b:ℝ) (a:Fin (N c) → ℝ):
    Fin (arity N (intervalControl c d s m)) → ℝ:=
  intervalCastValues (interval_control_dimension N c d s m) (Fin.cons b a)

private theorem head_at_context (q c:List Bool) (HO:original q=c) (b:ℝ) (a:Fin (N c) → ℝ)
    (v:Fin (arity N q) → ℝ) (HV:HEq v (Fin.cons b a : Fin (N c+1) → ℝ)):realHead S N hd q v=baseHead S N hd c a:=by
  cases HO
  have HE:v=(Fin.cons b a : Fin (N (original q)+1) → ℝ):=eq_of_heq HV
  subst v
  rw [head_radius_map]
  rfl

theorem canonical_head (c:List Bool) (d s:ℕ) (m:Bool) (b:ℝ) (a:Fin (N c) → ℝ):
    realHead S N hd (intervalControl c d s m) (values N c d s m b a)=baseHead S N hd c a:=
  head_at_context S N hd _ c (interval_control_original c d s m) b a _ (intervalCastValues_heq _ _)

theorem interval_control_moment (c:List Bool) (d s:ℕ) (m:Bool):moment (intervalControl c d s m)=(if m then 2 else 1):=by
  cases m <;> simp [moment,FormulaSignSlotRadialRadiusTarskiFamily.moment,
    FormulaSignSlotRadialRadiusTarskiFamily.momentWord,intervalControl,
    IntegralPolynomialWindowTarskiCatalogue.control]

theorem canonical_query (c:List Bool) (d s:ℕ) (m:Bool) (b:ℝ) (a:Fin (N c) → ℝ):
    realQuery N (intervalControl c d s m) (values N c d s m b a)=(realWindow b)^(if m then 2 else 1):=by
  rw [query_radius_map,interval_control_moment]
  have HB:values N c d s m b a 0=b:=by
    unfold values intervalCastValues
    have H0:Fin.cast (interval_control_dimension N c d s m) (0:Fin (arity N (intervalControl c d s m)))=0:=Fin.ext rfl
    rw [H0,Fin.cons_zero]
  rw [HB]

theorem interval_control_degree (c:List Bool) (d s:ℕ) (m:Bool):
    degree S (intervalControl c d s m)=min d (S.degree c)+1:=by
  simp only [degree,inputBound,degreeWord,FormulaSignSlotRadialRadiusTarskiFamily.degreeWord,
    original,FormulaSignSlotRadialRadiusTarskiFamily.original,intervalControl,
    IntegralPolynomialWindowTarskiCatalogue.control,pairFst_pair,pairSnd_pair,
    BinaryNatCode.encode,Nat.fromBitsLE_bits]
theorem interval_control_seed (c:List Bool) (d s:ℕ) (m:Bool):
    seedDegree S (intervalControl c d s m)=min s (S.degree c):=by
  simp only [seedDegree,inputBound,seedWord,FormulaSignSlotRadialRadiusTarskiFamily.seedWord,
    original,FormulaSignSlotRadialRadiusTarskiFamily.original,intervalControl,
    IntegralPolynomialWindowTarskiCatalogue.control,pairFst_pair,pairSnd_pair,
    BinaryNatCode.encode,Nat.fromBitsLE_bits]
theorem interval_control_bound (c:List Bool) (d s:ℕ) (m:Bool):bound S (intervalControl c d s m)=S.degree c+5:=by
  unfold bound inputBound
  rw [interval_control_original]

theorem canonical_seed (c:List Bool) (d s:ℕ) (m:Bool) (b:ℝ) (a:Fin (N c) → ℝ):
    realSeed S N hd (intervalControl c d s m) (values N c d s m b a)=
      PseudoRemainder.seed (baseHead S N hd c a) ((realWindow b)^(if m then 2 else 1))
        (min d (S.degree c)+1) (S.degree c+5):=by
  rw [real_seed_eq,canonical_head,canonical_query,interval_control_degree,interval_control_bound]

theorem baseHead_degree (c:List Bool) (a:Fin (N c) → ℝ):(baseHead S N hd c a).natDegree  ≤  S.degree c:=
  Polynomial.natDegree_map_le.trans (IntegralPolynomialRadiusReader.polynomial_degree S N hd c)

theorem exists_selected (c:List Bool) (b:ℝ) (a:Fin (N c) → ℝ) (m:Bool)
    (HP:0 < (baseHead S N hd c a).natDegree):
    ∃d, d < IntegralPolynomialWindowTarskiCatalogue.limit S c ∧∃s,
      s < IntegralPolynomialWindowTarskiCatalogue.limit S c ∧
      Selected S N hd (intervalControl c d s m) (values N c d s m b a):=by
  let p:=baseHead S N hd c a
  let d:=p.natDegree
  let dm:=d-1
  let z:=PseudoRemainder.seed p ((realWindow b)^(if m then 2 else 1)) d (S.degree c+5)
  let s:=z.natDegree
  have HB:d  ≤  S.degree c:=baseHead_degree S N hd c a
  have Hpos:0 < d:=HP
  have HM:min dm (S.degree c)+1=d:=by
    rw [Nat.min_eq_left (by dsimp only [dm];omega)]
    dsimp only [dm]
    omega
  have HS:s < d:=by
    have H:=real_seed_degree S N hd (intervalControl c dm 0 m) (values N c dm 0 m b a)
    rw [canonical_seed,interval_control_degree,HM] at H
    exact H
  refine ⟨dm,by unfold IntegralPolynomialWindowTarskiCatalogue.limit;dsimp only [dm];omega,s,?_,?_⟩
  · unfold IntegralPolynomialWindowTarskiCatalogue.limit
    omega
  · apply (selected_iff S N hd _ _).mpr
    constructor
    · rw [canonical_head,interval_control_degree,HM]
    · rw [canonical_seed,interval_control_seed,HM,Nat.min_eq_left (by omega:s  ≤  S.degree c)]

def ConstantSelected (c:List Bool) (a:Fin (N c) → ℝ):Prop:=
  (baseHead S N hd c a).coeff 0 ≠ 0 ∧∀i,0 < i → i  ≤  S.degree c → (baseHead S N hd c a).coeff i=0

private theorem window_positive (b r:ℝ) (HB:0 < b):
    SignType.sign ((realWindow b).eval r)=SignType.pos ↔ r∈Ioo 0 b:=by
  rw [show SignType.pos=(1:SignType) from rfl,sign_eq_one_iff]
  simp only [realWindow,Polynomial.eval_mul,Polynomial.eval_X,Polynomial.eval_sub,Polynomial.eval_C,mem_Ioo]
  constructor
  · intro H
    rcases mul_pos_iff.mp H with H|H
    · exact ⟨H.1,by linarith [H.2]⟩
    · exfalso
      linarith [H.1,H.2]
  · rintro ⟨H0,H1⟩
    exact mul_pos H0 (sub_pos.mpr H1)

private theorem empty_iff_moments (p:ℝ[X]) (HP:p ≠ 0) (b:ℝ) (HB:0 < b):
    (∀r,p.eval r=0 → r ∉ Ioo 0 b) ↔
      RootSignQueries.tarskiQuery p ((realWindow b)^2)+RootSignQueries.tarskiQuery p (realWindow b)=0:=by
  have HZ:RootSignQueries.singleSignCount p (realWindow b) SignType.pos=0 ↔
      ∀r∈p.roots.toFinset,r ∉ Ioo 0 b:=by
    rw [RootSignQueries.singleSignCount,Finset.card_eq_zero,Finset.filter_eq_empty_iff]
    simp only [window_positive b _ HB]
  have HR:(∀r∈p.roots.toFinset,r ∉ Ioo 0 b) ↔∀r,p.eval r=0 → r ∉ Ioo 0 b:=by
    simp only [Multiset.mem_toFinset,Polynomial.mem_roots HP,Polynomial.IsRoot]
  have HC:=RootSignQueries.singleSignCount_positive p (realWindow b)
  rw [←HR,←HZ]
  omega

theorem interval_iff_statistics (c:List Bool) (d1 s1 d2 s2:ℕ) (b:ℝ) (a:Fin (N c) → ℝ) (HB:0 < b)
    (H1:Selected S N hd (intervalControl c d1 s1 false) (values N c d1 s1 false b a))
    (H2:Selected S N hd (intervalControl c d2 s2 true) (values N c d2 s2 true b a)):
    (∀r,(baseHead S N hd c a).eval r=0 → r ∉ Ioo 0 b) ↔
      statistic S N hd (intervalControl c d2 s2 true) (values N c d2 s2 true b a)+
        statistic S N hd (intervalControl c d1 s1 false) (values N c d1 s1 false b a)=0:=by
  have HP:baseHead S N hd c a ≠ 0:=by
    intro HZ
    have HNZ:(realHead S N hd (intervalControl c d1 s1 false) (values N c d1 s1 false b a)).coeff
        (degree S (intervalControl c d1 s1 false)) ≠ 0:=H1.1.1
    rw [canonical_head,HZ,Polynomial.coeff_zero] at HNZ
    exact HNZ rfl
  have HT1:=tarski_eq_statistic S N hd _ _ H1
  have HT2:=tarski_eq_statistic S N hd _ _ H2
  rw [canonical_head,canonical_query] at HT1 HT2
  simp only [Bool.false_eq_true,ite_false,ite_true,pow_one] at HT1 HT2
  rw [←HT1,←HT2]
  exact empty_iff_moments _ HP b HB

noncomputable def Empty (c:List Bool) (b:ℝ) (a:Fin (N c) → ℝ):Prop:=
  ConstantSelected S N hd c a ∨∃d1,d1 < IntegralPolynomialWindowTarskiCatalogue.limit S c ∧∃s1,
    s1 < IntegralPolynomialWindowTarskiCatalogue.limit S c ∧∃d2,d2 < IntegralPolynomialWindowTarskiCatalogue.limit S c ∧∃s2,
    s2 < IntegralPolynomialWindowTarskiCatalogue.limit S c ∧
    Selected S N hd (intervalControl c d1 s1 false) (values N c d1 s1 false b a) ∧
    Selected S N hd (intervalControl c d2 s2 true) (values N c d2 s2 true b a) ∧
    statistic S N hd (intervalControl c d2 s2 true) (values N c d2 s2 true b a)+
      statistic S N hd (intervalControl c d1 s1 false) (values N c d1 s1 false b a)=0

private theorem constant_degree (c:List Bool) (a:Fin (N c) → ℝ) (H:ConstantSelected S N hd c a):
    (baseHead S N hd c a).natDegree=0:=by
  apply Nat.eq_zero_of_le_zero
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro i hi
  by_cases hD:i  ≤  S.degree c
  · exact H.2 i hi hD
  · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by have HB:=baseHead_degree S N hd c a;omega)

theorem empty_iff (c:List Bool) (b:ℝ) (a:Fin (N c) → ℝ) (HB:0 < b):
    Empty S N hd c b a ↔∀r,(baseHead S N hd c a).eval r=0 → r ∉ Ioo 0 b:=by
  constructor
  · rintro (HC|⟨d1,_,s1,_,d2,_,s2,_,H1,H2,HS⟩)
    · have HD:=constant_degree S N hd c a HC
      intro r HR
      rw [Polynomial.eq_C_of_natDegree_eq_zero HD,Polynomial.eval_C] at HR
      exact (HC.1 HR).elim
    · exact (interval_iff_statistics S N hd c d1 s1 d2 s2 b a HB H1 H2).mpr HS
  · intro HE
    have HNZ:baseHead S N hd c a ≠ 0:=by
      intro H0
      have HR:=HE (b/2) (by rw [H0,Polynomial.eval_zero])
      exact HR ⟨by linarith,by linarith⟩
    by_cases HD:(baseHead S N hd c a).natDegree=0
    · left
      constructor
      · rw [←HD,Polynomial.coeff_natDegree]
        exact Polynomial.leadingCoeff_ne_zero.mpr HNZ
      · intro i hi _
        exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    · obtain ⟨d1,HD1,s1,HS1,H1⟩:=exists_selected S N hd c b a false (by omega)
      obtain ⟨d2,HD2,s2,HS2,H2⟩:=exists_selected S N hd c b a true (by omega)
      exact Or.inr ⟨d1,HD1,s1,HS1,d2,HD2,s2,HS2,H1,H2,
        (interval_iff_statistics S N hd c d1 s1 d2 s2 b a HB H1 H2).mp HE⟩

noncomputable def Zero (c:List Bool) (a:Fin (N c) → ℝ):Prop:=
  ∀i,i  ≤  S.degree c → (baseHead S N hd c a).coeff i=0

theorem zero_iff (c:List Bool) (a:Fin (N c) → ℝ):Zero S N hd c a ↔baseHead S N hd c a=0:=by
  constructor
  · intro H
    ext i
    rw [Polynomial.coeff_zero]
    by_cases HI:i  ≤  S.degree c
    · exact H i HI
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by have HB:=baseHead_degree S N hd c a;omega)
  · intro H i _
    rw [H,Polynomial.coeff_zero]

theorem zero_or_empty_iff (c:List Bool) (b:ℝ) (a:Fin (N c) → ℝ) (HB:0 < b):
    (Zero S N hd c a ∨Empty S N hd c b a) ↔
      baseHead S N hd c a=0 ∨∀r,(baseHead S N hd c a).eval r=0 → r ∉ Ioo 0 b:=
  or_congr (zero_iff S N hd c a) (empty_iff S N hd c b a HB)

end LeanCanny.Encoding.IntegralPolynomialWindowTarski
