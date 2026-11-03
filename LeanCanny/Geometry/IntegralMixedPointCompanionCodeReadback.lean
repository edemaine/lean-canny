/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedPointCompanionCodeStable

/-! # Actual row bytes and ordered coordinates determine entire capture words -/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedPointCompanion
open LeanCanny.Algebra LeanCanny.Encoding IntegralMixedHistory IntegralMixedFrozenFrame IntegralMixedCausalRowConstructor
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n m u : ℕ}

theorem original_code_of_rows (frozen : Finset (Fin (n+1))) (double : Fin (n+1)→Bool)
    (rows : Fin (n+1)→Row m) (other : Fin (n+1)→Row u) (g j : Free frozen)
    (HB : ∀ i,(rows i).base=(other i).base) (HM : ∀ i,(rows i).midpoint=(other i).midpoint) :
    (originalPointData frozen double rows g.val j.val g.property j.property).code=
      (originalPointData frozen double other g.val j.val g.property j.property).code :=by
  simp only [originalPointData,IntegralMixedCriticalRecordConstructor.Data.code,HB,HM]
  rfl

theorem codes_map_zero (frozen : Finset (Fin (n+1))) (double : Fin (n+1)→Bool)
    (rows : Fin (n+1)→Row m) (g : Free frozen) (js : List (Free frozen)) :
    codes frozen double rows g js=js.map (fun j=>(pointData frozen double rows g 0 j).code) :=by
  induction js with
  | nil=>rfl
  | cons j js ih=>rw [codes,List.map_cons,pointData_code_stable,ih]

theorem codes_shift (frozen : Finset (Fin (n+1))) (double : Fin (n+1)→Bool)
    (rows : Fin (n+1)→Row m) (g : Free frozen) (js : List (Free frozen)) (q : ℕ) :
    codes frozen double (shiftRows rows q) g js=codes frozen double rows g js :=by
  rw [codes_map_zero,codes_map_zero]
  apply List.map_congr_left
  intro j _
  exact original_code_of_rows frozen double (shiftRows rows q) rows g j
    (shiftRows_base rows q) (shiftRows_midpoint rows q)

theorem ordered_codes (frozen : Finset (Fin (n+1))) (double : Fin (n+1)→Bool)
    (rows : Fin (n+1)→Row m) (g : Free frozen) (js : List (Free frozen)) (k : ℕ)
    (HL : js.length=n+1-(k+1)) (HG : ∀i : Fin js.length,(js.get i).val.val=k+1+i.val)
    (emit : ℕ→List Bool) (HD : ∀j : Free frozen,(pointData frozen double rows g 0 j).code=emit j.val.val) :
    (codes frozen double rows g js).reverse=(List.range (n+1-(k+1))).map (fun i=>emit (n-i)) :=by
  rw [codes_map_zero,←List.map_reverse]
  apply List.ext_getElem
  · simp only [List.length_map,List.length_reverse,List.length_range,HL]
  · intro i hi hj
    simp only [List.length_map,List.length_reverse] at hi
    simp only [List.getElem_map,List.getElem_reverse,HD,List.getElem_range]
    apply congrArg emit
    have HE:=HG ⟨js.length-1-i,by omega⟩
    simp only [List.get_eq_getElem] at HE
    rw [HE,HL]
    omega

end LeanCanny.Geometry.IntegralMixedPointCompanion
