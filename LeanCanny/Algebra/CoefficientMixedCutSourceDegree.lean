/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.CoefficientMixedCutSpecialization
public import LeanCanny.Algebra.IntegralMixedCausalUnitRecord
/-! # Original cut shapes depend on the source degree alone

Changing radius changes source coefficients. This transports the literal
kind/indices and causal record while leaving the computed formal recipe fixed.
-/
@[expose] public section
namespace LeanCanny.Algebra.CoefficientMixedCutSourceDegree
open IntegralMixedHistory IntegralMixedRelativeCuts IntegralMixedCausalRecordBits
open scoped Classical
variable {n width:ℕ} {P Q:SpatialSource n}

def kind (h:P.degree=Q.degree) (r:IntegralMixedCriticalSweep.Rule n):Kind P r→Kind Q r:=by
  cases P with
  | mk p a D hD hp ha=>
    cases Q with
    | mk q b E hE hq hb=>
      dsimp only at h
      cases h
      intro c
      cases c with
      | coordinate j k=>exact .coordinate j k
      | squarefree j k=>exact .squarefree j k
      | value j k=>exact .value j k
      | limitCoordinate j k=>exact .limitCoordinate j k

variable {R A:Type*} [CommRing R] [CommRing A] [Algebra R A] {m N:ℕ}

theorem factor_eq (h:P.degree=Q.degree) (bank:CoefficientHeightBank R A m)
    (low:MvPolynomial (Fin (n+1)) R) (a:R) (r:IntegralMixedCriticalSweep.Rule n)
    (s:R) (c:Kind P r):
    CoefficientMixedCutDispatcher.factor bank low a r s (kind h r c)=
      CoefficientMixedCutDispatcher.factor bank low a r s c:=by
  cases P
  cases Q
  dsimp only at h
  cases h
  cases c <;> rfl

theorem raw_eq (h:P.degree=Q.degree) (bank:CoefficientHeightBank R A m)
    (low:MvPolynomial (Fin (n+1)) R) (a:R) (r:IntegralMixedCriticalSweep.Rule n)
    (current:Bool) (c:Kind P r) (d:ℕ):
    CoefficientMixedCutSpecialization.raw bank low a r current (kind h r c) d=
      CoefficientMixedCutSpecialization.raw bank low a r current c d:=by
  unfold CoefficientMixedCutSpecialization.raw CoefficientMixedCutDispatcher.raw
  rw [factor_eq]

theorem polynomial_eq (h:P.degree=Q.degree) (b:CoefficientCoordinateBasis R A m N)
    (bank:CoefficientHeightBank R A m) (low:MvPolynomial (Fin (n+1)) R) (a:R)
    (r:IntegralMixedCriticalSweep.Rule n) (current:Bool) (c:Kind P r) (d τ:ℕ):
    CoefficientMixedCutSpecialization.polynomial b bank low a r current (kind h r c) d τ=
      CoefficientMixedCutSpecialization.polynomial b bank low a r current c d τ:=by
  unfold CoefficientMixedCutSpecialization.polynomial
  rw [raw_eq]

theorem leading_eq (h:P.degree=Q.degree) (b:CoefficientCoordinateBasis R A m N)
    (bank:CoefficientHeightBank R A m) (low:MvPolynomial (Fin (n+1)) R) (a:R)
    (r:IntegralMixedCriticalSweep.Rule n) (current:Bool) (c:Kind P r) (d τ:ℕ):
    CoefficientMixedCutSpecialization.leading b bank low a r current (kind h r c) d τ=
      CoefficientMixedCutSpecialization.leading b bank low a r current c d τ:=by
  unfold CoefficientMixedCutSpecialization.leading
  rw [raw_eq]

def cut (h:P.degree=Q.degree) (c:Cut P width):Cut Q width where
  critical:=c.critical
  height:=c.height
  frozen:=c.frozen
  tag:=c.tag
  coordinate:=c.coordinate
  choice:=c.choice
  degree:=c.degree
  source_cap:=by rw [←h];exact c.source_cap
  degree_cap:=c.degree_cap
  current:=c.current

theorem cut_kind (h:P.degree=Q.degree) (c:Cut P width) (q:ℤ) (hq:q≠0):
    kind h (c.rule q hq) (c.kind q hq)=(cut h c).kind q hq:=by
  cases P
  cases Q
  dsimp only at h
  cases h
  rcases c with ⟨cr,h,hf,tag,j,k,d,hs,hd,cur⟩
  cases tag <;> rfl

theorem cut_of_code (h:P.degree=Q.degree) (hn:0<n) (birth:ℕ) (code:List Bool)
    (hP:IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^width)
    (hQ:IntegralMixedExceptionalBounds.auxiliaryCap (n+1) Q.degree≤2^width):
    cut h (IntegralMixedCausalUnitRecordBits.cut P hn birth code hP)=
      IntegralMixedCausalUnitRecordBits.cut Q hn birth code hQ:=by
  cases P
  cases Q
  dsimp only at h
  cases h
  rfl

/-- The current-Q mode is the exact original causal command, not a new rule. -/
theorem native_command {S m:ℕ} {ι:Type} (x:State P S width m ι) (c:Cut P width):
    IntegralMixedFullHistoryScript.Command.cut
      (CoefficientMixedCutSpecialization.nativeRule x (c.rule 1 one_ne_zero) c.current)
      (CoefficientMixedCutSpecialization.nativeKind x (c.rule 1 one_ne_zero) c.current
        (c.kind 1 one_ne_zero)) c.degree c.source_cap c.degree_cap=
      (Template.cut c).command (commonDenominator x) (commonDenominator_ne_zero x):=by
  rcases c with ⟨cr,h,hf,tag,j,k,d,hs,hd,cur⟩
  cases cur <;> cases tag <;> rfl

end LeanCanny.Algebra.CoefficientMixedCutSourceDegree
