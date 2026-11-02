/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FlatAffineExceptionalIntegerProducer
public import LeanCanny.Encoding.FlatAffineExceptionalInitialValueBound
public import LeanCanny.Algebra.IntegralMixedIntegerRealization
public import LeanCanny.Algebra.IntegralMixedHistorySemantics
/-! # Correlated original roots in the actual bank-only initial prefix

This constructs a fresh target hom by re-adjoining the prescribed original
integer roots. It does not identify the legacy parent's physical sampler with
the bank-only target, and permits a larger scalar width and history cap.
-/
@[expose] public section
namespace LeanCanny.Encoding.FlatAffineExceptionalInitialRealization
open LeanCanny.Algebra IntegralMixedHistory IntegralMixedFullHistoryScript
open IntegralMixedIntegerRealization
open FlatAffineFullSourceTower (Inputs arity)
open FlatAffineCompleteRootStages (next)
open FlatAffineLastHeightRow (parentCone)
open FlatAffineExceptionalBankSource (births width finitePolynomial)
open scoped Classical

noncomputable def values (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (u v a : List Bool)
    (hv : FlatAffineCompleteVertices.Valid F (parentCone F C) u v) (i : ℕ) : ℝ :=
  if hi : i < births F u then FlatAffineExceptionalParentBank.values F C h u v a hv ⟨i,hi⟩ else 0

theorem values_fin (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (u v a : List Bool)
    (hv : FlatAffineCompleteVertices.Valid F (parentCone F C) u v) (i : Fin (births F u)) :
    values F C h u v a hv i.val = FlatAffineExceptionalParentBank.values F C h u v a hv i := by
  simp only [values,i.isLt,dite_true]

theorem commands_roots {n B : ℕ} (P : SpatialSource n) (F : Inputs)
    (C : FlatAffinePowerPositive.ConeCertificate (next F)) (h : (u : List Bool) → Fin (arity F u))
    (u v a : List Bool) (hB : width F u ≤ B)
    (hv : FlatAffineCompleteVertices.Valid F (parentCone F C) u v)
    (ha : SquareSampleCompleteVertices.Valid
      (IntegerPolynomialSampleInput.input (FlatAffineExceptionalSliceFrame.scalarSource F C h)) u a)
    (i : Fin (FlatAffineExceptionalIntegerCommands.commands P B F C h u hB).length) :
    Root (FlatAffineExceptionalIntegerCommands.commands P B F C h u hB)[i] (values F C h u v a hv i.val) := by
  have hi : i.val < births F u := by simpa only [FlatAffineExceptionalIntegerCommands.length_commands] using i.isLt
  let j : Fin (List.ofFn (FlatAffineExceptionalIntegerCommands.command P B F C h u hB)).length :=
    ⟨i.val,by simpa only [List.length_ofFn] using hi⟩
  change Root ((List.ofFn (FlatAffineExceptionalIntegerCommands.command P B F C h u hB)).get j) _
  rw [List.get_ofFn]
  change (finitePolynomial F C h u ⟨i.val,hi⟩).eval₂ (Int.castRingHom ℝ) (values F C h u v a hv i.val)=0
  rw [values_fin F C h u v a hv ⟨i.val,hi⟩]
  exact FlatAffineExceptionalParentBank.values_root F C h u v a hv ha _

theorem commands_realizes {n S B : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
    (initial : State P S B 0 ι) (z : ι → ℝ)
    (hz : ∀ i, (initial.sampler.rows i).eval₂ (Int.castRingHom ℝ) z=0)
    (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F)) (h : (u : List Bool) → Fin (arity F u))
    (u v a : List Bool) (hB : width F u ≤ B)
    (hm : (FlatAffineExceptionalIntegerCommands.commands P B F C h u hB).length ≤ S+1)
    (hv : FlatAffineCompleteVertices.Valid F (parentCone F C) u v)
    (ha : SquareSampleCompleteVertices.Valid
      (IntegerPolynomialSampleInput.input (FlatAffineExceptionalSliceFrame.scalarSource F C h)) u a) :
    Realizes (run initial (FlatAffineExceptionalIntegerCommands.commands P B F C h u hB) hm)
      (values F C h u v a hv) :=
  realizes initial z hz _ hm _ (commands_roots P F C h u v a hB hv ha)

theorem paddedPast_append {n B : ℕ} {P : SpatialSource n} (later initial : List (Command P B)) :
    paddedPast (later++initial) initial.length=initial := by
  rw [paddedPast_valid _ _ (by simp only [List.length_append]; omega)]
  simp only [past,List.reverse_append]
  have HL : initial.length=initial.reverse.length := List.length_reverse.symm
  rw [HL,List.take_left,List.reverse_reverse]

theorem family_commands (P : IntegralCriticalHistoryTask.Parameters)
    (base : IntegralMixedFullHistoryFamilyBits.Data P)
    (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F)) (h : (u : List Bool) → Fin (arity F u))
    (input : List Bool → List Bool)
    (later : (root : List Bool) → List (Command (base.spatial root) (P.width root)))
    (hW : ∀ root, width F (input root) ≤ P.width root)
    (hroom : ∀ root, (later root).length+births F (input root)+2 ≤ P.cap root+1)
    (key : List Bool) (hb : IntegralMixedFullHistoryFamilyBits.prefixLength P key = births F (input (pairFst key))) :
    IntegralMixedFullHistoryFamilyBits.commands P
      (FlatAffineExceptionalIntegerProducer.data P base F C h input later hW hroom) key =
      FlatAffineExceptionalIntegerCommands.commands (base.spatial (pairFst key)) (P.width (pairFst key))
        F C h (input (pairFst key)) (hW (pairFst key)) := by
  unfold IntegralMixedFullHistoryFamilyBits.commands
  rw [hb]
  change paddedPast (later _ ++ FlatAffineExceptionalIntegerCommands.commands _ _ F C h _ _) _ = _
  rw [← FlatAffineExceptionalIntegerCommands.length_commands (base.spatial (pairFst key)) (P.width (pairFst key))
    F C h (input (pairFst key)) (hW (pairFst key))]
  exact paddedPast_append _ _

theorem family_realizes (P : IntegralCriticalHistoryTask.Parameters)
    (base : IntegralMixedFullHistoryFamilyBits.Data P)
    (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F)) (h : (u : List Bool) → Fin (arity F u))
    (input : List Bool → List Bool)
    (later : (root : List Bool) → List (Command (base.spatial root) (P.width root)))
    (hW : ∀ root, width F (input root) ≤ P.width root)
    (hroom : ∀ root, (later root).length+births F (input root)+2 ≤ P.cap root+1)
    (key v a : List Bool)
    (hb : IntegralMixedFullHistoryFamilyBits.prefixLength P key = births F (input (pairFst key)))
    (hv : FlatAffineCompleteVertices.Valid F (parentCone F C) (input (pairFst key)) v)
    (ha : SquareSampleCompleteVertices.Valid
      (IntegerPolynomialSampleInput.input (FlatAffineExceptionalSliceFrame.scalarSource F C h)) (input (pairFst key)) a) :
    Realizes ((IntegralMixedFullHistoryFamilyBits.family P
      (FlatAffineExceptionalIntegerProducer.data P base F C h input later hW hroom)).state key)
      (values F C h (input (pairFst key)) v a hv) := by
  have hm : (FlatAffineExceptionalIntegerCommands.commands (base.spatial (pairFst key)) (P.width (pairFst key))
      F C h (input (pairFst key)) (hW (pairFst key))).length ≤ P.cap (pairFst key)+1+1 := by
    rw [FlatAffineExceptionalIntegerCommands.length_commands]
    have H := hroom (pairFst key)
    omega
  exact realizes_run_eq (IntegralMixedFullHistoryFamilyBits.initial P
      (FlatAffineExceptionalIntegerProducer.data P base F C h input later hW hroom) (pairFst key))
    _ _ _ hm (family_commands P base F C h input later hW hroom key hb) _
    (commands_realizes _ Fin.elim0 (fun i => Fin.elim0 i) F C h _ v a (hW _) hm hv ha)

end LeanCanny.Encoding.FlatAffineExceptionalInitialRealization
