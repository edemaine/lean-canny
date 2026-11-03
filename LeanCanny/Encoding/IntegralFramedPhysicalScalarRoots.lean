/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedPhysicalSquarePoint
public import LeanCanny.Algebra.IntegralMixedFramedScalarEmbedding
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalScalarRows
public import LeanCanny.Algebra.UniformIntegralPrefixJointRoots
public import LeanCanny.Algebra.IntegralMixedFramedBankObservation
/-! # A full vertex supplies its literal raw scalar-prefix joint root

This is only projection through the actual scalar injection. The full
sampler context and vertex word remain fixed; no scalar vertex is chosen.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedPhysicalSquare
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask UniformIntegralPrefix
open IntegralMixedFramedHistoryFamilyBits (Plan family commands)
open IntegralMixedFramedPhysicalIndex (enumerate)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
  (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
  (key : List Bool→List Bool) (hpos : ∀c,0<(family P D H).birth (key c))
  (c w : List Bool) (hv : SquareSampleCompleteVertices.Valid (input P D H L F C hs key hpos) c w)

noncomputable def scalarTuple : Fin ((family P D H).birth (key c))→ℝ :=
  fun i=>rawPoint P D H L F C hs key hpos c w hv (((family P D H).state (key c)).sampler.scalar i)

theorem scalarTuple_map (i : Fin ((family P D H).birth (key c))) :
    scalarTuple P D H L F C hs key hpos c w hv i=
      joint P D H L F C hs key hpos c w hv (IntegralMixedFramedScalarEmbedding.scalarMap P D H (key c) i) :=rfl

theorem scalar_roots : ∀i,(((family P D H).state (key c)).sampler.scalarPrefix.rows i).eval₂
    (Int.castRingHom ℝ) (scalarTuple P D H L F C hs key hpos c w hv)=0 :=by
  intro i
  have HI:=raw_roots P D H L F C hs key hpos c w hv (((family P D H).state (key c)).sampler.scalar i)
  have HR:=IntegralMixedFramedPhysicalIndex.family_scalarRows P D H (key c) i
  have HE:=congrArg (fun p : MvPolynomial ((family P D H).physical (key c)) ℤ=>
    p.eval₂ (Int.castRingHom ℝ) (rawPoint P D H L F C hs key hpos c w hv)) HR
  have HX : (MvPolynomial.rename (((family P D H).state (key c)).sampler.scalar)
      (((family P D H).state (key c)).sampler.scalarPrefix.rows i)).eval₂ (Int.castRingHom ℝ)
        (rawPoint P D H L F C hs key hpos c w hv)=
      (((family P D H).state (key c)).sampler.scalarPrefix.rows i).eval₂ (Int.castRingHom ℝ)
        (scalarTuple P D H L F C hs key hpos c w hv) :=by
    rw [MvPolynomial.eval₂_rename]
    rfl
  exact HX.symm.trans (HE.symm.trans HI)

theorem scalar_roots_at : RootsAt ((family P D H).state (key c)).sampler.scalarPrefix
    (IntegralMixedFramedBankObservation.extend (scalarTuple P D H L F C hs key hpos c w hv)) :=by
  change ∀i,(((family P D H).state (key c)).sampler.scalarPrefix.rows i).eval₂ (Int.castRingHom ℝ)
    (fun j=>IntegralMixedFramedBankObservation.extend (scalarTuple P D H L F C hs key hpos c w hv) j.val)=0
  have HE : (fun j : Fin ((family P D H).birth (key c))=>
      IntegralMixedFramedBankObservation.extend (scalarTuple P D H L F C hs key hpos c w hv) j.val)=
      scalarTuple P D H L F C hs key hpos c w hv :=by
    funext j
    exact dite_eq_left j.isLt
  rw [HE]
  exact scalar_roots P D H L F C hs key hpos c w hv
end LeanCanny.Encoding.IntegralFramedPhysicalSquare
