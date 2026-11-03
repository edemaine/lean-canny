/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedPhysicalSquarePoint
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalRowTransport
/-! # Complete vertices and natural-column roots of the actual full sampler

Only columns below the actual full arity are read. Zero extension lets the
literal natural-variable row identities be used without dependent Fin casts.
Completeness includes every real full root, including singular ones.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedPhysicalSquare
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask MvPolynomial
open IntegralMixedFramedHistoryFamilyBits (Plan family commands)
open IntegralMixedFramedPhysicalRowTransport
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem natural_roots_iff (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool) (z : ℕ→ℝ) :
    (∀i,(keyRow P D key i).eval₂ (Int.castRingHom ℝ) z=0) ↔
      ∀i,((sampler P D H key).rows i).eval₂ (Int.castRingHom ℝ) (fun j=>z j.val)=0 :=by
  constructor
  · intro HZ i
    have HE:=HZ i.val
    rw [keyRow_family P D H key i.val i.isLt,MvPolynomial.eval₂_rename] at HE
    exact HE
  · intro HZ i
    by_cases hi : i<count P D key
    · rw [keyRow_family P D H key i hi,MvPolynomial.eval₂_rename]
      exact HZ ⟨i,hi⟩
    · change (natRows (IntegralMixedFramedHistoryFamilyBits.initial P D (pairFst key))
        (commands P D key) _ i).eval₂ (Int.castRingHom ℝ) z=0
      have HN : ¬i<IntegralMixedFramedPhysicalIndex.arity (commands P D key):=hi
      have HE : natRows (IntegralMixedFramedHistoryFamilyBits.initial P D (pairFst key))
          (commands P D key) (((family P D H).birth_bound key).trans (Nat.le_succ _)) i=0:=
        dite_eq_right HN
      exact (congrArg (fun p : MvPolynomial ℕ ℤ=>p.eval₂ (Int.castRingHom ℝ) z) HE).trans
        (MvPolynomial.eval₂_zero _ _)

variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
  (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
  (key : List Bool→List Bool) (hpos : ∀c,0<(family P D H).birth (key c))
  (c w : List Bool) (hv : SquareSampleCompleteVertices.Valid (input P D H L F C hs key hpos) c w)

noncomputable def naturalPoint (i : ℕ) : ℝ :=
  if hi : i<count P D (key c) then joint P D H L F C hs key hpos c w hv ⟨i,hi⟩ else 0

theorem naturalPoint_at (i : Fin (count P D (key c))) :
    naturalPoint P D H L F C hs key hpos c w hv i.val=joint P D H L F C hs key hpos c w hv i :=by
  rw [naturalPoint,dite_eq_left i.isLt]

theorem naturalPoint_roots :
    ∀i,(keyRow P D (key c) i).eval₂ (Int.castRingHom ℝ)
      (naturalPoint P D H L F C hs key hpos c w hv)=0 :=by
  apply (natural_roots_iff P D H (key c) _).mpr
  have HE : (fun j : Fin (count P D (key c))=>naturalPoint P D H L F C hs key hpos c w hv j.val)=
      joint P D H L F C hs key hpos c w hv:=funext (naturalPoint_at P D H L F C hs key hpos c w hv)
  rw [HE]
  exact joint_roots P D H L F C hs key hpos c w hv

omit w hv in
theorem exists_joint_natural (z : ℕ→ℝ)
    (hz : ∀i,(keyRow P D (key c) i).eval₂ (Int.castRingHom ℝ) z=0) :
    ∃w,∃hv : SquareSampleCompleteVertices.Valid (input P D H L F C hs key hpos) c w,
      ∀i : Fin (count P D (key c)),joint P D H L F C hs key hpos c w hv i=z i.val :=by
  obtain ⟨w,hv,HE⟩:=exists_joint P D H L F C hs key hpos c (fun i=>z i.val)
    ((natural_roots_iff P D H (key c) z).mp hz)
  exact ⟨w,hv,fun i=>congrFun HE i⟩

end LeanCanny.Encoding.IntegralFramedPhysicalSquare
