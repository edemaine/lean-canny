/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedOptionalEndpointTrace

/-! # Actual continuation states and decoder receipts compose in chronological order -/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedOptionalEndpoints
open LeanCanny.Algebra LeanCanny.Encoding IntegralMixedHistory IntegralMixedFullHistoryScript
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B m : ℕ} {P : SpatialSource n}

theorem index_append (ι : Type) (cs ds : List (Command P B)) :
    Index ι (cs++ds)=Index (Index ι ds) cs :=by
  induction cs with
  | nil=>rfl
  | cons c cs ih=>exact congrArg (fun t : Type=>NextIndex t c) ih

theorem step_heq {m₁ m₂ : ℕ} {ι₁ ι₂ : Type} [I₁ : Fintype ι₁] [I₂ : Fintype ι₂]
    (x : State P S B m₁ ι₁) (y : State P S B m₂ ι₂) (hx : m₁≤S) (hy : m₂≤S)
    (hm : m₁=m₂) (hi : ι₁=ι₂) (HE : HEq x y) (c : Command P B) :
    HEq (step x hx c) (step y hy c) :=by
  subst m₂
  subst ι₂
  have Hxy : x=y:=eq_of_heq HE
  subst y
  have HI : I₁=I₂:=Subsingleton.elim _ _
  cases HI
  rfl

theorem commonDenominator_heq {m₁ m₂ : ℕ} {ι₁ ι₂ : Type}
    (x : State P S B m₁ ι₁) (y : State P S B m₂ ι₂)
    (hm : m₁=m₂) (hi : ι₁=ι₂) (HE : HEq x y) :
    commonDenominator x=commonDenominator y :=by
  subst m₂
  subst ι₂
  have Hxy : x=y:=eq_of_heq HE
  exact congrArg commonDenominator Hxy

theorem continueRun_append {ι : Type} [Fintype ι] (x : State P S B m ι)
    (ds : List (Command P B)) (hd : m+ds.length≤S+1)
    (cs : List (Command P B)) (h : m+(cs++ds).length≤S+1)
    (hc : m+ds.length+cs.length≤S+1) :
    HEq (continueRun x (cs++ds) h) (continueRun (continueRun x ds hd) cs hc) :=by
  induction cs with
  | nil=>rfl
  | cons c cs ih=>
    have HT : m+(cs++ds).length=m+ds.length+cs.length:=by rw [List.length_append];omega
    exact step_heq _ _ _ _ HT (index_append ι cs ds)
      (ih (by simp only [List.cons_append,List.length_cons] at h;omega)
        (by simp only [List.length_cons] at hc;omega)) c

theorem decoded_command_congr (hn : 0<n) (birth other : ℕ) (code : List Bool)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B)
    (Q R : ℤ) (hQ : Q≠0) (hR : R≠0) (hb : birth=other) (hQR : Q=R) :
    (IntegralMixedCausalUnitRecordBits.record P hn birth code hcap).template.command Q hQ=
      (IntegralMixedCausalUnitRecordBits.record P hn other code hcap).template.command R hR :=by
  subst other
  subst R
  rfl

theorem Decodes.prepend_critical {ι : Type} [Fintype ι] (x : State P S B m ι) (hn : 0<n)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B)
    (cs : List (Command P B)) (hc : m+cs.length≤S+1) (codes : List (List Bool))
    (HD : Decodes x hn hcap cs hc codes) {birth : ℕ}
    (data : IntegralMixedCriticalRecordConstructor.Data n birth) (hb : birth=m+cs.length)
    (h : m+(.critical data.rule::cs).length≤S+1) :
    Decodes x hn hcap (.critical data.rule::cs) h (data.code::codes) :=by
  refine ⟨HD,?_⟩
  exact (decoded_command_congr hn _ birth data.code hcap _ _ _ _ hb.symm rfl).trans
    (IntegralMixedCriticalRecordConstructor.command_decode P hn data hcap
      (commonDenominator (continueRun x cs hc)) (commonDenominator_ne_zero _))

theorem Decodes.append {ι : Type} [Fintype ι] (x : State P S B m ι) (hn : 0<n)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B)
    (ds : List (Command P B)) (hd : m+ds.length≤S+1) (oldCodes : List (List Bool))
    (HD : Decodes x hn hcap ds hd oldCodes)
    (cs : List (Command P B)) (hc : m+ds.length+cs.length≤S+1) (codes : List (List Bool))
    (HC : Decodes (continueRun x ds hd) hn hcap cs hc codes)
    (h : m+(cs++ds).length≤S+1) :
    Decodes x hn hcap (cs++ds) h (codes++oldCodes) :=by
  induction cs generalizing codes with
  | nil=>
    have HE : codes=[]:=HC
    subst codes
    exact HD
  | cons c cs ih=>
    cases codes with
    | nil=>exact HC.elim
    | cons code codes=>
      refine ⟨ih (by simp only [List.length_cons] at hc;omega) codes HC.1
        (by simp only [List.cons_append,List.length_cons] at h;omega),?_⟩
      have HT : m+(cs++ds).length=m+ds.length+cs.length:=by rw [List.length_append];omega
      have HS:=continueRun_append x ds hd cs
        (by simp only [List.cons_append,List.length_cons] at h;omega)
        (by simp only [List.length_cons] at hc;omega)
      have HQ:=commonDenominator_heq _ _ HT (index_append ι cs ds) HS
      exact (decoded_command_congr hn _ _ code hcap _ _ _ _ HT HQ).trans HC.2

theorem Decodes.congr_start {m₁ m₂ : ℕ} {ι₁ ι₂ : Type} [I₁ : Fintype ι₁] [I₂ : Fintype ι₂]
    (x : State P S B m₁ ι₁) (y : State P S B m₂ ι₂) (hm : m₁=m₂) (hi : ι₁=ι₂) (HE : HEq x y)
    (hn : 0<n) (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B)
    (cs : List (Command P B)) (hx : m₁+cs.length≤S+1) (hy : m₂+cs.length≤S+1)
    (codes : List (List Bool)) : Decodes x hn hcap cs hx codes↔Decodes y hn hcap cs hy codes :=by
  subst m₂
  subst ι₂
  have Hxy : x=y:=eq_of_heq HE
  subst y
  have HI : I₁=I₂:=Subsingleton.elim _ _
  cases HI
  rfl

theorem continueRun_heq {m₁ m₂ : ℕ} {ι₁ ι₂ : Type} [I₁ : Fintype ι₁] [I₂ : Fintype ι₂]
    (x : State P S B m₁ ι₁) (y : State P S B m₂ ι₂) (hm : m₁=m₂) (hi : ι₁=ι₂) (HE : HEq x y)
    (cs : List (Command P B)) (hx : m₁+cs.length≤S+1) (hy : m₂+cs.length≤S+1) :
    HEq (continueRun x cs hx) (continueRun y cs hy) :=by
  induction cs with
  | nil=>exact HE
  | cons c cs ih=>
    exact step_heq _ _ _ _ (congrArg (·+cs.length) hm) (congrArg (fun t : Type=>Index t cs) hi)
      (ih (by simp only [List.length_cons] at hx;omega) (by simp only [List.length_cons] at hy;omega)) c

theorem continueRun_list_heq {ι : Type} [Fintype ι] (x : State P S B m ι)
    (cs ds : List (Command P B)) (hc : m+cs.length≤S+1) (hd : m+ds.length≤S+1) (HE : cs=ds) :
    HEq (continueRun x cs hc) (continueRun x ds hd) :=by
  subst ds
  rfl

end LeanCanny.Geometry.IntegralMixedOptionalEndpoints
