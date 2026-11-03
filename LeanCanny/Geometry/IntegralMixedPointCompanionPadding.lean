/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedPointCompanionCodeStable
/-! # Physical padding repeats a previously realized point in its old frame

The repeated code has fixed chronological producer labels. Actual rules
shift their references and their creating common denominator can change.
The anchored specialization starts from an already realized full block;
its seed is not chosen from a prospective query or probe.
-/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedPointCompanion
open LeanCanny.Algebra LeanCanny.Encoding IntegralMixedHistory IntegralMixedFullHistoryScript
open IntegralMixedCausalRowConstructor IntegralMixedFrozenFrame IntegralMixedChosenLocalRealization
open IntegralHistorySampler UniformIntegralPowerSchedule
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
variable (x : State P S B m ι) (frozen : Finset (Fin (n+1))) (double : Fin (n+1)→Bool)
    (rows : Fin (n+1)→Row m) (g : Free frozen)

theorem commands_replicate_length (k : ℕ) :
    (commands (P:=P) (B:=B) frozen double rows g (List.replicate k g)).length=k :=by
  simp only [commands_length,List.length_replicate]

omit [Fintype ι] in
theorem command_replicate_get (k : ℕ) (i : Fin k) :
    (commands (P:=P) (B:=B) frozen double rows g (List.replicate k g)).get
      ⟨i.val,by simpa only [commands_length,List.length_replicate] using i.isLt⟩=
      command frozen double rows g (k-1-i.val) g :=by
  induction k with
  | zero=>exact Fin.elim0 i
  | succ k ih=>
    refine Fin.cases ?_ (fun i=>?_) i
    · change command frozen double rows g (List.replicate k g).length g=_
      simp only [List.length_replicate,Fin.val_zero,Nat.add_sub_cancel_right,Nat.sub_zero]
    · change (commands (P:=P) (B:=B) frozen double rows g (List.replicate k g)).get _=_
      rw [ih i]
      congr 1
      simp only [Fin.val_succ]
      omega

omit [Fintype ι] in
theorem values_replicate (p : Fin (n+1)→ℝ) (old : Fin m→ℝ) (k : ℕ) (i : Fin k) :
    values p old (List.replicate k g) ⟨i.val,by simp only [List.length_replicate];have :=i.isLt;omega⟩=p g.val :=by
  simpa only [List.get_eq_getElem,List.getElem_replicate] using
    values_get p old (List.replicate k g) ⟨i.val,by simpa only [List.length_replicate] using i.isLt⟩

theorem repeat_commonDenominator (k : ℕ) (room : m+(g::List.replicate k g).length≤S+1) :
    commonDenominator (run x frozen double rows g (g::List.replicate k g) room)=
      leading (run x frozen double rows g (List.replicate k g)
        (by simp only [List.length_cons] at room;omega))
        (by simp only [List.length_cons] at room;omega)
        (command frozen double rows g (List.replicate k g).length g)*
      commonDenominator (run x frozen double rows g (List.replicate k g)
        (by simp only [List.length_cons] at room;omega)) :=
  command_commonDenominator _ _ _

theorem exists_repeat (hn : 0<n) (charge : ℕ) (hdegree : P.degree=BoundedZeroSource.powerDegree charge)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B)
    (HP : PrefixFrozen (originalFrame frozen double rows))
    (z : ι→ℝ) (hz : ∀i,(x.sampler.rows i).eval₂ (Int.castRingHom ℝ) z=0)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hφ : ∀i,φ (x.sampler.scalarPrefix.basis.generator i)=z (x.sampler.scalar i)^weights S (2^B) m i)
    (old : Fin m→ℝ) (H : ∀i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=old i)
    (p : Fin (n+1)→ℝ) (hp : p∈slice P (originalFrame frozen double rows) old)
    (hg : ∀i,i∉frozen→i≠g.val→
      (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial P.low P.leading P.degree)).eval₂
        (Int.castRingHom ℝ) p=0)
    (k : ℕ) (room : m+(List.replicate k g).length≤S+1) :
    Nonempty (Realized x frozen double rows g z φ old p (List.replicate k g) room) ∧
      Decoded x frozen double rows g hn hcap (List.replicate k g) room :=
  exists_realized x frozen double rows g hn charge hdegree hcap HP z hz φ hφ old H p hp hg _ room

 theorem repeat_from_realized (hn : 0<n) (charge : ℕ) (hdegree : P.degree=BoundedZeroSource.powerDegree charge)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B)
    (HP : PrefixFrozen (originalFrame frozen double rows))
    (z : ι→ℝ) (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (old : Fin m→ℝ)
    (p : Fin (n+1)→ℝ) (hp : p∈slice P (originalFrame frozen double rows) old)
    (hg : ∀i,i∉frozen→i≠g.val→
      (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial P.low P.leading P.degree)).eval₂
        (Int.castRingHom ℝ) p=0)
    (js : List (Free frozen)) (room : m+js.length≤S+1)
    (R : Realized x frozen double rows g z φ old p js room) (anchor : Fin js.length)
    (k : ℕ) (hroom : m+js.length+(List.replicate k g).length≤S+1) :
    let seed:=run x frozen double rows g js room
    let seedRows:=shiftRows rows js.length
    ∃U : Realized seed frozen double seedRows g R.tuple R.hom (values p old js) p (List.replicate k g) hroom,
      Decoded seed frozen double seedRows g hn hcap (List.replicate k g) hroom ∧
      ∀i,U.tuple (IntegralMixedOptionalEndpoints.oldColumns
        (commands frozen double seedRows g (List.replicate k g)) (blockColumn frozen double rows g js anchor i))^
          physical S (2^B) (m+(js.length-1-anchor.val))=p i :=by
  have HS : p∈slice P (originalFrame frozen double (shiftRows rows js.length)) (values p old js):=by
    rw [show originalFrame frozen double (shiftRows rows js.length)=frame frozen double rows js.length from rfl,
      slice_values frozen double rows p old js]
    exact hp
  obtain ⟨⟨U⟩,HD⟩:=exists_repeat (run x frozen double rows g js room) frozen double (shiftRows rows js.length) g
    hn charge hdegree hcap HP R.tuple R.roots R.hom R.generators (values p old js) R.quotients p HS hg k hroom
  refine ⟨U,HD,fun i=>?_⟩
  rw [U.old_raw]
  exact R.blocks anchor i

end LeanCanny.Geometry.IntegralMixedPointCompanion
