/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.SquareSampleHashNaturality
/-! # The same ordinal names the same parameter after an exact rebase -/
@[expose] public section
namespace LeanCanny.Encoding.SquareSampleOrdinalNaturality
open LeanCanny.Algebra LeanCanny.Computation SquareSampleInput SquareSampleRankNaturality
open SquareSampleHashNaturality
open scoped Classical

theorem value_congr (P Q : Inputs) (c d : List Bool)
    (hD : SquareSampleCoordinates.parameterDegree P c=SquareSampleCoordinates.parameterDegree Q d)
    (hp : SquareSampleCoordinates.parameter P c=SquareSampleCoordinates.parameter Q d)
    (hR : SquareSampleQueries.roots P c=SquareSampleQueries.roots Q d)
    (r : ℕ) (hr : r<SquareSampleRegularCount.count P c) :
    SquareSampleHashEnumeration.value P (pair c (BinaryNatCode.encode r))=
      SquareSampleHashEnumeration.value Q (pair d (BinaryNatCode.encode r)) :=by
  have HC:=count_congr P Q c d hR
  have HV:=values_congr P Q c d hD hp hR
  obtain ⟨hP,hPr⟩:=SquareSampleHashEnumeration.value_spec P c r hr
  obtain ⟨hQ,hQr⟩:=SquareSampleHashEnumeration.value_spec Q d r (HC ▸ hr)
  apply SquareSampleHashRoots.rank_unique Q d (HV ▸ hP) hQ
  have HE : SquareSampleHashRoots.rank Q d
      (SquareSampleHashEnumeration.value P (pair c (BinaryNatCode.encode r)))=r:=by
    simpa only [SquareSampleHashRoots.rank,HV] using hPr
  exact HE.trans hQr.symm

theorem root_val_congr (P Q : Inputs) (c d : List Bool)
    (hD : SquareSampleCoordinates.parameterDegree P c=SquareSampleCoordinates.parameterDegree Q d)
    (hp : SquareSampleCoordinates.parameter P c=SquareSampleCoordinates.parameter Q d)
    (hR : SquareSampleQueries.roots P c=SquareSampleQueries.roots Q d)
    (r : Fin (SquareSampleRegularCount.count P c)) (s : Fin (SquareSampleRegularCount.count Q d))
    (hrs : r.val=s.val) :
    (SquareSampleHashEnumeration.root P c r).val=(SquareSampleHashEnumeration.root Q d s).val :=by
  let x:=SquareSampleHashEnumeration.root P c r
  let y:=SquareSampleHashEnumeration.root Q d s
  let e:=rootEquiv P Q c d hR
  have HX : SquareSampleHashChoice.hash Q d (e x)=SquareSampleHashChoice.hash Q d y:=by
    calc
      _=SquareSampleHashChoice.hash P c x:=(hash_congr P Q c d hD hp hR x (e x) rfl).symm
      _=SquareSampleHashEnumeration.value P (pair c (BinaryNatCode.encode r.val)):=
        SquareSampleHashEnumeration.hash_root P c r
      _=SquareSampleHashEnumeration.value Q (pair d (BinaryNatCode.encode r.val)):=
        value_congr P Q c d hD hp hR r.val r.isLt
      _=SquareSampleHashEnumeration.value Q (pair d (BinaryNatCode.encode s.val)):=by rw [hrs]
      _=SquareSampleHashChoice.hash Q d y:=(SquareSampleHashEnumeration.hash_root Q d s).symm
  exact congrArg Subtype.val (SquareSampleHashChoice.hash_injective Q d HX)

theorem root_val_comp (F : Inputs) (f : List Bool→List Bool) (u : List Bool)
    (r : Fin (SquareSampleRegularCount.count (comp F f) u))
    (s : Fin (SquareSampleRegularCount.count F (f u))) (hrs : r.val=s.val) :
    (SquareSampleHashEnumeration.root (comp F f) u r).val=
      (SquareSampleHashEnumeration.root F (f u) s).val :=
  root_val_congr (comp F f) F u (f u) rfl
    (SquareSampleParameterNaturality.parameter_comp F f u)
    (SquareSampleParameterNaturality.roots_comp F f u) r s hrs

end LeanCanny.Encoding.SquareSampleOrdinalNaturality
