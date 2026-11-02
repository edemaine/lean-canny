/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedFrozenFrameSectionCard
public import LeanCanny.Encoding.FixedWidthNatVector

/-! # Explicit words for actual selected critical sections

Each digit is the ordered real-root index of an actual selected coordinate
polynomial over the same old hom. Frozen-coordinate reconstruction proves
injectivity. This semantic encoder does not assert that a real-root rank
is an FP input reader or that independently chosen roots form a section.
-/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedFrozenFrameSectionCode
open LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Connectivity IntegralMixedHistory IntegralMixedCriticalSweep Set Polynomial
open IntegralMixedSelectedGeometry IntegralMixedSelectedPhysicalFiber IntegralMixedFrozenFrame
open scoped Classical
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type}

noncomputable def polynomial (x : State P S B m ι) (hm : m≤S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (t : ℝ) (j : Free r) : Polynomial ℝ :=
  (selected x hm r j φ).map (Polynomial.evalRingHom t)

noncomputable def roots (x : State P S B m ι) (hm : m≤S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (t : ℝ) (j : Free r) : Finset ℝ :=
  (polynomial x hm r φ t j).roots.toFinset

theorem roots_card (x : State P S B m ι) (hm : m≤S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (t : ℝ) (j : Free r) :
    (roots x hm r φ t j).card≤2^B := by
  apply (Multiset.toFinset_card_le _).trans ((Polynomial.card_roots' _).trans ?_)
  change (polynomial x hm r φ t j).natDegree≤_
  rw [polynomial,specialized_degree]
  exact criticalDegree_cap x hm r.critical

theorem coordinate_mem (x : State P S B m ι) (hm : m≤S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (t : ℝ) (a : physical x hm r φ t) (j : Free r) :
    a.val (ClearedCoordinateCritical.freeIndex r.critical.offset.val (fit r).le j)∈roots x hm r φ t j := by
  have Hdegree:=specialized_degree x hm r j φ t
  have HP : polynomial x hm r φ t j≠0 := by
    intro Hzero
    have Hpos : 0<PurePowerReductionBounds.dimension (n-r.critical.offset.val+1) P.degree:=
      pow_pos (Nat.two_pow_pos _) _
    change (polynomial x hm r φ t j).natDegree=_ at Hdegree
    rw [Hzero,Polynomial.natDegree_zero] at Hdegree
    omega
  exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots HP).mpr (physical_coordinate_root x hm r φ t a j))

noncomputable def ordinal (x : State P S B m ι) (hm : m≤S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (t : ℝ) (a : physical x hm r φ t) (j : Free r) :
    Fin (roots x hm r φ t j).card :=
  ((roots x hm r φ t j).orderIsoOfFin rfl).symm
    ⟨a.val (ClearedCoordinateCritical.freeIndex r.critical.offset.val (fit r).le j),coordinate_mem x hm r φ t a j⟩

theorem root_ordinal (x : State P S B m ι) (hm : m≤S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (t : ℝ) (a : physical x hm r φ t) (j : Free r) :
    OrderedRealCells.root (roots x hm r φ t j) (ordinal x hm r φ t a j)=
      a.val (ClearedCoordinateCritical.freeIndex r.critical.offset.val (fit r).le j) :=
  congrArg Subtype.val (((roots x hm r φ t j).orderIsoOfFin rfl).apply_symm_apply _)

theorem ordinal_lt (x : State P S B m ι) (hm : m≤S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (t : ℝ) (a : physical x hm r φ t) (j : Free r) :
    (ordinal x hm r φ t a j).val<2^B := (ordinal x hm r φ t a j).isLt.trans_le (roots_card x hm r φ t j)

noncomputable def word (x : State P S B m ι) (hm : m≤S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (t : ℝ) (a : physical x hm r φ t) : List Bool :=
  FixedWidthNatVector.encode (n+1) B
    (fun j=>if hj : j<n-r.critical.offset.val+1 then (ordinal x hm r φ t a ⟨j,hj⟩).val else 0)

theorem word_length (x : State P S B m ι) (hm : m≤S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (t : ℝ) (a : physical x hm r φ t) :
    (word x hm r φ t a).length=(n+1)*B := FixedWidthNatVector.length_encode _ _ _

theorem word_digit (x : State P S B m ι) (hm : m≤S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (t : ℝ) (a : physical x hm r φ t) (j : Free r) :
    Nat.fromBitsLE (((word x hm r φ t a).drop (j.val*B)).take B)=(ordinal x hm r φ t a j).val := by
  have HJ : j.val<n+1:=by have H:=j.isLt; omega
  have HD:=FixedWidthNatVector.decode_block (n+1) B
    (fun k=>if hk : k<n-r.critical.offset.val+1 then (ordinal x hm r φ t a ⟨k,hk⟩).val else 0)
    j.val HJ (by simpa only [dite_eq_left j.isLt] using ordinal_lt x hm r φ t a j)
  simpa only [word,dite_eq_left j.isLt] using HD

theorem word_injective (x : State P S B m ι) (hm : m≤S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (t : ℝ) : Function.Injective (word x hm r φ t) := by
  intro a b Hword
  have HO (j : Free r) : ordinal x hm r φ t a j=ordinal x hm r φ t b j := by
    apply Fin.ext
    rw [←word_digit x hm r φ t a j,←word_digit x hm r φ t b j,Hword]
  have Hfree : freeCoordinates r a.val=freeCoordinates r b.val := by
    funext j
    have HE:=congrArg (fun k=>(roots x hm r φ t j).orderIsoOfFin rfl k) (HO j)
    simp only [ordinal,OrderIso.apply_symm_apply] at HE
    exact congrArg Subtype.val HE
  apply Subtype.ext
  calc
    _=IntegralMixedSweepRows.point x hm r φ t (freeCoordinates r a.val):=(reconstruct x hm r φ t a.val a.property.1).symm
    _=IntegralMixedSweepRows.point x hm r φ t (freeCoordinates r b.val):=congrArg (IntegralMixedSweepRows.point x hm r φ t) Hfree
    _=b.val:=reconstruct x hm r φ t b.val b.property.1

def width (n B : ℕ) : ℕ := (n+1)*B

theorem width_unary {n B : List Bool→ℕ} (hn : UnaryFn n) (hB : UnaryFn B) :
    UnaryFn (fun q=>width (n q) (B q)) := (hn.add (UnaryFn.const 1)).mul hB

theorem width_polynomial {n B : List Bool→ℕ} (hn : UnaryFn n) (hB : UnaryFn B) :
    ∃ p : Polynomial ℕ,∀ q,width (n q) (B q)≤p.eval q.length := by
  obtain ⟨p,HP⟩:=output_length_poly_of_mem_FP (width_unary hn hB).mem_FP
  exact ⟨p,fun q=>by simpa only [List.length_replicate] using HP q⟩

end LeanCanny.Geometry.IntegralMixedFrozenFrameSectionCode
