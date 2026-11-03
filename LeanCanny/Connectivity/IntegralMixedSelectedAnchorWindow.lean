/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.IntegralMixedSelectedWindowQueries
public import LeanCanny.Connectivity.IntegralMixedSelectedRootRank
public import LeanCanny.Algebra.IntegralMixedSelectedCoordinateOrderedQueries
public import LeanCanny.Algebra.DyadicTarskiSpace
/-! # An epsilon window identifies an anchor without a remainder-degree oracle

Only the head parameter is fixed. Keeping epsilon in the query preserves
the existing exact seed-degree theorem, even when its value at epsilon zero
would have smaller degree.
-/
@[expose] public section
namespace LeanCanny.Connectivity.IntegralMixedSelectedAnchorWindow
open LeanCanny.Algebra LeanCanny.Geometry Polynomial
open IntegralMixedSelectedCoordinateWindow
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem rank_injective (s : Finset ℝ) (u v : ℝ) (hu : u∈s) (hv : v∈s) :
    OrderedRealRootWindow.rank s u=OrderedRealRootWindow.rank s v→u=v :=by
  have H:=FiniteImageRank.rank_eq_iff s id u v hu hv
  simpa only [FiniteImageRank.rank_eq,Finset.image_id,id_eq,OrderedRealRootWindow.rank] using H.mp

theorem all_windows_iff (p : ℝ[X]) (code : ℕ) (y : ℝ) :
    (∀ε : ℝ,0<ε→Window p code y ε)↔
      y∈p.roots.toFinset ∧ OrderedRealRootWindow.rank p.roots.toFinset y=code :=by
  constructor
  · intro H
    obtain ⟨z,hz,hk,hd⟩:=(window_iff p code y 1).mp (H 1 zero_lt_one)
    have HE : z=y:=by
      by_contra hne
      have HP : 0<dist z y:=dist_pos.mpr hne
      obtain ⟨w,hw,hwk,hwd⟩:=(window_iff p code y (dist z y/2)).mp
        (H (dist z y/2) (by linarith))
      have HW : w=z:=rank_injective _ _ _ hw hz (hwk.trans hk.symm)
      rw [HW] at hwd
      linarith
    subst z
    exact ⟨hz,hk⟩
  · rintro ⟨hy,hk⟩ ε hε
    exact (window_iff p code y ε).mpr ⟨y,hy,hk,by simpa only [dist_self] using hε⟩

theorem constant_window_iff_of_stable (p : ℝ[X]) (code : ℕ) (y : ℝ) (B : Prop)
    (H : ∃η : ℝ,0<η ∧ ∀ε : ℝ,0<ε→ε<η→∃ζ : ℝ,0<ζ ∧
      ∀δ : ℝ,0<δ→δ<ζ→(Window p code y ε↔B)) :
    B↔y∈p.roots.toFinset ∧ OrderedRealRootWindow.rank p.roots.toFinset y=code :=by
  rw [←all_windows_iff]
  obtain ⟨η,hη,HE⟩:=H
  constructor
  · intro hB ε hε
    let ε₀:=min ε (η/2)
    have hε₀ : 0<ε₀:=lt_min hε (by linarith)
    have hεη : ε₀<η:=(min_le_right _ _).trans_lt (by linarith)
    obtain ⟨ζ,hζ,Hζ⟩:=HE ε₀ hε₀ hεη
    have HW:=(Hζ (ζ/2) (by linarith) (by linarith)).mpr hB
    obtain ⟨z,hz,hk,hd⟩:=(window_iff p code y ε₀).mp HW
    exact (window_iff p code y ε).mpr ⟨z,hz,hk,hd.trans_le (min_le_left _ _)⟩
  · intro HW
    obtain ⟨ζ,hζ,Hζ⟩:=HE (η/2) (by linarith) (by linarith)
    exact (Hζ (ζ/2) (by linarith) (by linarith)).mp (HW (η/2) (by linarith))

noncomputable def value (p : ℝ[X]) (d : ℕ) (y scale : ℝ) (negative : Bool) (e : Fin 3) :=
  IntegralMixedSelectedCoordinateOrderedQueries.value (p.map Polynomial.C) d y scale negative e

noncomputable def Test (p : ℝ[X]) (d : ℕ) (y scale : ℝ) (code : ℕ) : Prop :=
  2*value p d y scale false 0≤2*(code:ℤ)+value p d y scale false 2+value p d y scale false 1 ∧
    2*(code:ℤ)<value p d y scale true 2-value p d y scale true 1

theorem window_stable (p : ℝ[X]) (d : ℕ) (hd : 0<d) (hp : p.natDegree=d)
    (y scale : ℝ) (hs : 0<scale) (code : ℕ) :
    ∃η : ℝ,0<η ∧ ∀ε : ℝ,0<ε→ε<η→∃ζ : ℝ,0<ζ ∧
      ∀δ : ℝ,0<δ→δ<ζ→(Window p code y ε↔Test p d y scale code) :=by
  have HP : (p.map Polynomial.C).natDegree=d:=
    (Polynomial.natDegree_map_eq_of_injective Polynomial.C_injective p).trans hp
  obtain ⟨η,hη,HE⟩:=IntegralMixedSelectedCoordinateOrderedQueries.eventually_queries
    (p.map Polynomial.C) d hd HP y scale hs.ne'
  refine ⟨η,hη,fun ε hε hεη=>?_⟩
  obtain ⟨ζ,hζ,Hζ⟩:=HE ε hε hεη
  refine ⟨ζ,hζ,fun δ hδ hδζ=>?_⟩
  have HQ (negative : Bool) (e : Fin 3) :
      RootSignQueries.tarskiQuery p ((X-C (y+if negative then ε else -ε))^e.val)=
        value p d y scale negative e :=by
    have H:=Hζ negative e δ hδ hδζ
    rw [IntegralMixedSelectedCoordinateOrderedQueries.evaluated_head,
      IntegralMixedSelectedCoordinateOrderedQueries.evaluated_query] at H
    have HH : (p.map Polynomial.C).map (evalRingHom δ)=p:=by
      rw [Polynomial.map_map]
      have HC : (evalRingHom δ).comp Polynomial.C=RingHom.id ℝ:=by ext a;simp
      rw [HC,Polynomial.map_id]
    rw [HH] at H
    have HC : X-C y+C (if negative then -ε else ε)=
        (X-C (y+if negative then ε else -ε) : ℝ[X]):=by
      cases negative <;> simp only [Bool.false_eq_true,ite_false,ite_true,map_add,map_neg] <;> ring
    rw [HC,mul_pow,←map_pow] at H
    have HT:=RootSignQueries.tarskiQuery_C_mul p ((X-C (y+if negative then ε else -ε))^e.val)
      1 (scale^e.val) one_ne_zero (pow_pos hs _)
    simp only [map_one,one_mul] at HT
    exact HT.symm.trans H
  have H0:=HQ false 0
  have HL1:=HQ false 1
  have HL2:=HQ false 2
  have HU1:=HQ true 1
  have HU2:=HQ true 2
  simp only [Bool.false_eq_true,ite_false,ite_true,show (0 : Fin 3).val=0 from rfl,
    show (1 : Fin 3).val=1 from rfl,show (2 : Fin 3).val=2 from rfl,pow_zero,pow_one,
    ←sub_eq_add_neg] at H0 HL1 HL2 HU1 HU2
  rw [IntegralMixedSelectedWindowQueries.window_iff,H0,HL1,HL2,HU1,HU2]
  rfl

theorem test_iff (p : ℝ[X]) (d : ℕ) (hd : 0<d) (hp : p.natDegree=d)
    (y scale : ℝ) (hs : 0<scale) (code : ℕ) :
    Test p d y scale code↔y∈p.roots.toFinset ∧ OrderedRealRootWindow.rank p.roots.toFinset y=code :=
  constant_window_iff_of_stable p code y _ (window_stable p d hd hp y scale hs code)

theorem captured_ordinal_iff {n S B m : ℕ} {P : IntegralMixedHistory.SpatialSource n} {ι : Type}
    (x : IntegralMixedHistory.State P S B m ι) (hm : m≤S) (r : IntegralMixedCriticalSweep.Rule n)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (t : ℝ) (j : IntegralMixedSelectedGeometry.Free r)
    (a : IntegralMixedSelectedPhysicalFiber.physical x hm r φ t) (scale : ℝ) (hs : 0<scale) (code : ℕ) :
    Test (IntegralMixedFrozenFrameSectionCode.polynomial x hm r φ t j)
      (PurePowerReductionBounds.dimension (n-r.critical.offset.val+1) P.degree)
      (a.val (ClearedCoordinateCritical.freeIndex r.critical.offset.val (IntegralMixedCriticalSweep.fit r).le j))
      scale code ↔code=(IntegralMixedFrozenFrameSectionCode.ordinal x hm r φ t a j).val :=by
  have HP : (IntegralMixedFrozenFrameSectionCode.polynomial x hm r φ t j).natDegree=
      PurePowerReductionBounds.dimension (n-r.critical.offset.val+1) P.degree:=
    IntegralMixedCriticalSweep.specialized_degree x hm r j φ t
  have HD : 0<PurePowerReductionBounds.dimension (n-r.critical.offset.val+1) P.degree:=
    pow_pos (Nat.two_pow_pos _) _
  apply (test_iff (IntegralMixedFrozenFrameSectionCode.polynomial x hm r φ t j)
    (PurePowerReductionBounds.dimension (n-r.critical.offset.val+1) P.degree) HD HP _ scale hs code).trans
  have HM:=IntegralMixedFrozenFrameSectionCode.coordinate_mem x hm r φ t a j
  have HO:=IntegralMixedSelectedRootRank.ordinal_rank x hm r φ t a j
  change (IntegralMixedFrozenFrameSectionCode.ordinal x hm r φ t a j).val=
    OrderedRealRootWindow.rank (IntegralMixedFrozenFrameSectionCode.polynomial x hm r φ t j).roots.toFinset _ at HO
  rw [←HO]
  exact and_iff_right HM |>.trans eq_comm

end LeanCanny.Connectivity.IntegralMixedSelectedAnchorWindow
