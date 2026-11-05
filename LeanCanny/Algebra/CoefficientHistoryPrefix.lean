/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.CoefficientMixedCriticalBirth
/-! # Constructed coefficient-prefix data for the framed recursion

This stores algebraic data, not specialization hypotheses. A source reframe
changes the inputs of the next birth without changing any existing field.
-/
@[expose] public section
namespace LeanCanny.Algebra.CoefficientHistoryPrefix
open scoped Classical

structure Prefix (R:Type) [CommRing R] (S width m:ℕ) (ι:Type) where
  carrier:Type
  ring:CommRing carrier
  algebra:@Algebra R carrier _ ring.toSemiring
  nontrivial:Nontrivial carrier
  basis:@CoefficientCoordinateBasis R carrier _ ring algebra m (2^width)
  bank:@CoefficientHeightBank R carrier _ ring m
  rows:ι→MvPolynomial ι R
  scalar:Fin m→ι

attribute [instance] Prefix.ring Prefix.algebra Prefix.nontrivial

variable {R:Type} [CommRing R] {S width m:ℕ} {ι:Type}

noncomputable def base [Nontrivial R] (S width:ℕ):Prefix R S width 0 (Fin 0) where
  carrier:=R
  ring:=inferInstance
  algebra:=inferInstance
  nontrivial:=inferInstance
  basis:=CoefficientCoordinateBasis.base R (2^width)
  bank:={numerator:=Fin.elim0,denominator:=Fin.elim0}
  rows:=Fin.elim0
  scalar:=Fin.elim0

noncomputable def scalarStep (F:Prefix R S width m ι) (p:Polynomial F.carrier)
    (d:ℕ) (leading:R):Prefix R S width (m+1) (ι⊕Unit) where
  carrier:=PaddedIntegralParameterExtension.Extension p d (2^width)
  ring:=inferInstance
  algebra:=inferInstance
  nontrivial:=PaddedIntegralParameterExtension.nontrivial p d (2^width) (Nat.two_pow_pos _)
  basis:=F.basis.paddedStep p d
  bank:=F.bank.rootStep p d (2^width) leading
  rows:=CoefficientCanonicalScalarAppend.rows S F.rows F.scalar F.basis p d
  scalar:=Fin.cons (Sum.inr ()) (fun i=>Sum.inl (F.scalar i))

noncomputable def criticalBlock {n:ℕ} (F:Prefix R S width m ι)
    (low:MvPolynomial (Fin (n+1)) R) (a:R) (D:ℕ) (r:IntegralMixedHistory.CriticalRule n):
    Prefix R S width m (ι⊕FlatAffineCriticalStage.Variables (n+1)) where
  carrier:=F.carrier
  ring:=F.ring
  algebra:=F.algebra
  nontrivial:=F.nontrivial
  basis:=F.basis
  bank:=F.bank
  rows:=CoefficientMixedCriticalBirth.physicalRows (cap:=S) F.bank F.basis low a r F.rows F.scalar D
  scalar:=fun i=>Sum.inl (F.scalar i)

noncomputable def criticalStep {n:ℕ} (F:Prefix R S width m ι)
    (low:MvPolynomial (Fin (n+1)) R) (a:R) (D:ℕ) (r:IntegralMixedHistory.CriticalRule n):
    Prefix R S width (m+1) ((ι⊕FlatAffineCriticalStage.Variables (n+1))⊕Unit):=
  scalarStep (criticalBlock F low a D r)
    (CoefficientMixedCriticalPolynomial.polynomial F.bank low a D r)
    (PurePowerReductionBounds.dimension (n-r.offset.val+1) D)
    (CoefficientMixedCriticalPolynomial.leadingValue F.bank a D r)

end LeanCanny.Algebra.CoefficientHistoryPrefix
