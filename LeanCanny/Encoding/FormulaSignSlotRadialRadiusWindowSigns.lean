/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialRadiusWindowBridge
/-! # Installed coordinate-head feature signs preserve actual-source window queries -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialRadiusWindowSigns
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.Connectivity Polynomial MvPolynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false
private theorem cast_heq {n m : ℕ} (h : n=m) (v : Fin m → ℝ) : HEq (IntegralPolynomialWindowTarski.intervalCastValues h v) v := by cases h; rfl
private theorem cons_cast_heq {n m : ℕ} (h : n=m) (b : ℝ) (v : Fin m → ℝ) :
    HEq (Fin.cons b (IntegralPolynomialWindowTarski.intervalCastValues h v) : Fin (n+1) → ℝ) (Fin.cons b v : Fin (m+1) → ℝ) := by cases h; rfl
private theorem feature_eval (C : ChargedPolynomialCatalogue.Input) (c : List Bool) (i : ℕ)
    (z : List Bool) (hz : C.row (pair c (BinaryNatCode.encode i))=z)
    (v : Fin (C.arity c) → ℝ) (w : Fin (C.source.arity z) → ℝ)
    (hw : HEq w (fun j => v (Fin.cast (C.dimension c i) j))) :
    (ChargedPolynomialCatalogue.feature C c i).eval₂ (Int.castRingHom ℝ) v =
      (C.source.polynomial z).eval₂ (Int.castRingHom ℝ) w := by
  cases hz
  have HE : w=(fun j => v (Fin.cast (C.dimension c i) j)) := eq_of_heq hw
  subst w
  exact MvPolynomial.eval₂_rename _ _ _ _
private theorem eval_heq {n m : ℕ} (h : n=m) (p : MvPolynomial (Fin n) ℤ)
    (q : MvPolynomial (Fin m) ℤ) (hp : HEq p q) (v : Fin n → ℝ) (w : Fin m → ℝ) (hv : HEq v w) :
    p.eval₂ (Int.castRingHom ℝ) v = q.eval₂ (Int.castRingHom ℝ) w := by
  cases h
  cases eq_of_heq hp
  cases eq_of_heq hv
  rfl

noncomputable abbrev centerCount (c : List Bool) := FormulaSignSlotCenteredRadialGraph.d (pairFst c)
noncomputable def tuple (c : List Bool) (b : ℝ) (a : Fin (centerCount c) → ℝ) : Fin (FormulaSignSlotRadialRadiusTarskiCatalogue.arity c) → ℝ := Fin.cons b a
theorem centers_eq (c : List Bool) (t e : ℕ) : FormulaSignSlotRadialRadiusWindowBridge.centers (FormulaSignSlotRadialRadiusTarskiCatalogue.headContext c t e)=centerCount c := by
  simp only [FormulaSignSlotRadialRadiusWindowBridge.centers, FormulaSignSlotRadialRadiusHeadReader.arity, FormulaSignSlotRadialRadiusHeadReader.original,
    FormulaSignSlotRadialRadiusTarskiCatalogue.headContext, pairFst_pair, centerCount]
noncomputable def center (c : List Bool) (t e : ℕ) (a : Fin (centerCount c) → ℝ) : Fin (FormulaSignSlotRadialRadiusWindowBridge.centers (FormulaSignSlotRadialRadiusTarskiCatalogue.headContext c t e)) → ℝ :=
  IntegralPolynomialWindowTarski.intervalCastValues (centers_eq c t e) a
noncomputable def Signs (c : List Bool) (b : ℝ) (a : Fin (centerCount c) → ℝ) (b' : ℝ) (a' : Fin (centerCount c) → ℝ) : Prop :=
  ∀ i : Fin (FormulaSignSlotRadialRadiusTarskiCatalogue.count c), SignType.sign (((FormulaSignSlotRadialRadiusTarskiCatalogue.family).feature c i.val).eval₂ (Int.castRingHom ℝ) (tuple c b a)) =
    SignType.sign (((FormulaSignSlotRadialRadiusTarskiCatalogue.family).feature c i.val).eval₂ (Int.castRingHom ℝ) (tuple c b' a'))

theorem encoded_feature_eval (c : List Bool) (r m j s d e t : ℕ) (hr : r < 3) (hm : m < 2)
    (hj : j < FormulaSignSlotRadialRadiusTarskiCatalogue.limit c) (hs : s < FormulaSignSlotRadialRadiusTarskiCatalogue.limit c) (hd : d < FormulaSignSlotRadialRadiusTarskiCatalogue.limit c) (he : e < FormulaSignSlotRadialRadiusTarskiCatalogue.limit c) (ht : t < FormulaSignSlotRadialRadiusTarskiCatalogue.limit c)
    (b : ℝ) (a : Fin (centerCount c) → ℝ) :
    ((FormulaSignSlotRadialRadiusTarskiCatalogue.family).feature c (FormulaSignSlotRadialRadiusTarskiCatalogue.encode c r m j s d e t)).eval₂ (Int.castRingHom ℝ) (tuple c b a) =
      (IntegralPolynomialWindowTarski.entryPolynomial FormulaSignSlotRadialRadiusWindowBridge.source FormulaSignSlotRadialRadiusWindowBridge.centers FormulaSignSlotRadialRadiusWindowBridge.dimension
        (IntegralPolynomialWindowTarski.intervalControl (FormulaSignSlotRadialRadiusTarskiCatalogue.headContext c t e) d s (decide (m=1))) r j).eval₂ (Int.castRingHom ℝ)
          (IntegralPolynomialWindowTarski.values FormulaSignSlotRadialRadiusWindowBridge.centers (FormulaSignSlotRadialRadiusTarskiCatalogue.headContext c t e) d s (decide (m=1)) b (center c t e a)) := by
  let q := IntegralPolynomialWindowTarski.intervalControl (FormulaSignSlotRadialRadiusTarskiCatalogue.headContext c t e) d s (decide (m=1))
  let z := pair (FormulaSignSlotRadialRadiusWindowBridge.roleWord r) (pair q (BinaryNatCode.encode j))
  let v := IntegralPolynomialWindowTarski.values FormulaSignSlotRadialRadiusWindowBridge.centers (FormulaSignSlotRadialRadiusTarskiCatalogue.headContext c t e) d s (decide (m=1)) b (center c t e a)
  let w := IntegralPolynomialWindowTarski.intervalCastValues (FormulaSignSlotRadialRadiusWindowBridge.kernel_arity q r j) v
  calc
    _ = (FormulaSignSlotRadialRadiusTarskiKernelSource.polynomial z).eval₂ (Int.castRingHom ℝ) w := by
      apply feature_eval FormulaSignSlotRadialRadiusTarskiCatalogue.input c (FormulaSignSlotRadialRadiusTarskiCatalogue.encode c r m j s d e t) z (FormulaSignSlotRadialRadiusTarskiCatalogue.row_encode c r m j s d e t hr hm hj hs hd he ht)
      have HV : HEq v (Fin.cons b (center c t e a) : Fin (FormulaSignSlotRadialRadiusWindowBridge.centers (FormulaSignSlotRadialRadiusTarskiCatalogue.headContext c t e)+1) → ℝ) := cast_heq _ _
      have HT : HEq (Fin.cons b (center c t e a) : Fin (FormulaSignSlotRadialRadiusWindowBridge.centers (FormulaSignSlotRadialRadiusTarskiCatalogue.headContext c t e)+1) → ℝ) (tuple c b a) :=
        cons_cast_heq (centers_eq c t e) b a
      have HW : HEq w (tuple c b a) := (cast_heq (FormulaSignSlotRadialRadiusWindowBridge.kernel_arity q r j) v).trans (HV.trans HT)
      exact HW.trans (cast_heq (FormulaSignSlotRadialRadiusTarskiCatalogue.input.dimension c (FormulaSignSlotRadialRadiusTarskiCatalogue.encode c r m j s d e t)) (tuple c b a)).symm
    _ = _ := eval_heq (FormulaSignSlotRadialRadiusWindowBridge.kernel_arity q r j) _ _ (FormulaSignSlotRadialRadiusWindowBridge.kernel_packet q r j) _ _ (cast_heq _ _)

theorem entry_sign (c : List Bool) (b : ℝ) (a : Fin (centerCount c) → ℝ)
    (b' : ℝ) (a' : Fin (centerCount c) → ℝ) (H : Signs c b a b' a')
    (r m j s d e t : ℕ) (hr : r < 3) (hm : m < 2)
    (hj : j < FormulaSignSlotRadialRadiusTarskiCatalogue.limit c) (hs : s < FormulaSignSlotRadialRadiusTarskiCatalogue.limit c) (hd : d < FormulaSignSlotRadialRadiusTarskiCatalogue.limit c) (he : e < FormulaSignSlotRadialRadiusTarskiCatalogue.limit c) (ht : t < FormulaSignSlotRadialRadiusTarskiCatalogue.limit c) :
    SignType.sign ((IntegralPolynomialWindowTarski.entryPolynomial FormulaSignSlotRadialRadiusWindowBridge.source FormulaSignSlotRadialRadiusWindowBridge.centers FormulaSignSlotRadialRadiusWindowBridge.dimension
      (IntegralPolynomialWindowTarski.intervalControl (FormulaSignSlotRadialRadiusTarskiCatalogue.headContext c t e) d s (decide (m=1))) r j).eval₂ (Int.castRingHom ℝ)
        (IntegralPolynomialWindowTarski.values FormulaSignSlotRadialRadiusWindowBridge.centers (FormulaSignSlotRadialRadiusTarskiCatalogue.headContext c t e) d s (decide (m=1)) b (center c t e a))) =
    SignType.sign ((IntegralPolynomialWindowTarski.entryPolynomial FormulaSignSlotRadialRadiusWindowBridge.source FormulaSignSlotRadialRadiusWindowBridge.centers FormulaSignSlotRadialRadiusWindowBridge.dimension
      (IntegralPolynomialWindowTarski.intervalControl (FormulaSignSlotRadialRadiusTarskiCatalogue.headContext c t e) d s (decide (m=1))) r j).eval₂ (Int.castRingHom ℝ)
        (IntegralPolynomialWindowTarski.values FormulaSignSlotRadialRadiusWindowBridge.centers (FormulaSignSlotRadialRadiusTarskiCatalogue.headContext c t e) d s (decide (m=1)) b' (center c t e a'))) := by
  have HH := H ⟨FormulaSignSlotRadialRadiusTarskiCatalogue.encode c r m j s d e t,FormulaSignSlotRadialRadiusTarskiCatalogue.encode_lt c r m j s d e t hr hm hj hs hd he ht⟩
  change SignType.sign (((FormulaSignSlotRadialRadiusTarskiCatalogue.family).feature c (FormulaSignSlotRadialRadiusTarskiCatalogue.encode c r m j s d e t)).eval₂ _ _) = _ at HH
  rw [encoded_feature_eval c r m j s d e t hr hm hj hs hd he ht,
    encoded_feature_eval c r m j s d e t hr hm hj hs hd he ht] at HH
  exact HH

theorem limit_head (c : List Bool) (t e : ℕ) : IntegralPolynomialWindowTarskiCatalogue.limit FormulaSignSlotRadialRadiusWindowBridge.source (FormulaSignSlotRadialRadiusTarskiCatalogue.headContext c t e)=FormulaSignSlotRadialRadiusTarskiCatalogue.limit c := by
  unfold IntegralPolynomialWindowTarskiCatalogue.limit FormulaSignSlotRadialRadiusTarskiCatalogue.limit FormulaSignSlotRadialRadiusTarskiCatalogue.inputDegree
  change FormulaSignSlotRadialEliminantPacked.resultDegree (pairFst (FormulaSignSlotRadialRadiusTarskiCatalogue.headContext c t e))+2 =
    FormulaSignSlotRadialEliminantPacked.resultDegree c+2
  rw [FormulaSignSlotRadialRadiusTarskiCatalogue.headContext,pairFst_pair]

private theorem encode_digits (L k : ℕ) (hL : 0 < L) (hk : k < 6*(L*(L*L))) :
    k%3+3*((k/3)%2+2*((k/6)%L+L*((k/6/L)%L+L*((k/6/L/L)%L))))=k := by
  have H0 : k/6 < L*(L*L) := (Nat.div_lt_iff_lt_mul (by decide : 0 < 6)).mpr (by simpa only [Nat.mul_comm] using hk)
  have H1 : k/6/L < L*L := (Nat.div_lt_iff_lt_mul hL).mpr (by simpa only [Nat.mul_assoc] using H0)
  have H2 : k/6/L/L < L := (Nat.div_lt_iff_lt_mul hL).mpr H1
  have E0 := Nat.mod_add_div k 3
  have E1 := Nat.mod_add_div (k/3) 2
  have E2 := Nat.mod_add_div (k/6) L
  have E3 := Nat.mod_add_div (k/6/L) L
  have ED : k/3/2=k/6 := by rw [Nat.div_div_eq_div_mul]
  rw [Nat.mod_eq_of_lt H2,E3,E2,←ED,E1,E0]

theorem catalogue_signs (c : List Bool) (b : ℝ) (a : Fin (centerCount c) → ℝ)
    (b' : ℝ) (a' : Fin (centerCount c) → ℝ) (H : Signs c b a b' a')
    (t e : ℕ) (ht : t < FormulaSignSlotRadialRadiusTarskiCatalogue.limit c) (he : e < FormulaSignSlotRadialRadiusTarskiCatalogue.limit c) :
    IntegralPolynomialWindowTarski.CatalogueSigns FormulaSignSlotRadialRadiusWindowBridge.source FormulaSignSlotRadialRadiusWindowBridge.centers FormulaSignSlotRadialRadiusWindowBridge.dimension (FormulaSignSlotRadialRadiusTarskiCatalogue.headContext c t e) b (center c t e a) b' (center c t e a') := by
  intro k
  let q := FormulaSignSlotRadialRadiusTarskiCatalogue.headContext c t e
  let L := IntegralPolynomialWindowTarskiCatalogue.limit FormulaSignSlotRadialRadiusWindowBridge.source q
  have hL : 0 < L := by unfold L IntegralPolynomialWindowTarskiCatalogue.limit; omega
  let r := k.val%3
  let m := (k.val/3)%2
  let j := (k.val/6)%L
  let s := (k.val/6/L)%L
  let d := (k.val/6/L/L)%L
  have hr : r < 3 := Nat.mod_lt _ (by decide)
  have hm : m < 2 := Nat.mod_lt _ (by decide)
  have hj : j < IntegralPolynomialWindowTarskiCatalogue.limit FormulaSignSlotRadialRadiusWindowBridge.source q := Nat.mod_lt _ hL
  have hs : s < IntegralPolynomialWindowTarskiCatalogue.limit FormulaSignSlotRadialRadiusWindowBridge.source q := Nat.mod_lt _ hL
  have hd : d < IntegralPolynomialWindowTarskiCatalogue.limit FormulaSignSlotRadialRadiusWindowBridge.source q := Nat.mod_lt _ hL
  have HE : IntegralPolynomialWindowTarskiCatalogue.encode FormulaSignSlotRadialRadiusWindowBridge.source q r m j s d=k.val := encode_digits L k.val hL k.isLt
  change SignType.sign (((IntegralPolynomialWindowTarskiCatalogue.family FormulaSignSlotRadialRadiusWindowBridge.source FormulaSignSlotRadialRadiusWindowBridge.centers FormulaSignSlotRadialRadiusWindowBridge.dimension).feature q k.val).eval₂ _ _) = _
  rw [←HE,IntegralPolynomialWindowTarski.encoded_feature_eval FormulaSignSlotRadialRadiusWindowBridge.source FormulaSignSlotRadialRadiusWindowBridge.centers FormulaSignSlotRadialRadiusWindowBridge.dimension q r m j s d hr hm hj hs hd,
    IntegralPolynomialWindowTarski.encoded_feature_eval FormulaSignSlotRadialRadiusWindowBridge.source FormulaSignSlotRadialRadiusWindowBridge.centers FormulaSignSlotRadialRadiusWindowBridge.dimension q r m j s d hr hm hj hs hd]
  exact entry_sign c b a b' a' H r m j s d e t hr hm
    (by simpa only [q,limit_head] using hj) (by simpa only [q,limit_head] using hs)
    (by simpa only [q,limit_head] using hd) he ht

end LeanCanny.Encoding.FormulaSignSlotRadialRadiusWindowSigns
