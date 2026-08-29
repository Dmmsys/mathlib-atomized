/-
Copyright (c) 2022 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
module

public import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-!
# Laurent expansions of rational functions

## Main declarations

* `RatFunc.laurent`: the Laurent expansion of the rational function `f` at `r`, as an `AlgHom`.
* `RatFunc.laurent_injective`: the Laurent expansion at `r` is unique

## Implementation details

Implemented as the quotient of two Taylor expansions, over domains.
An auxiliary definition is provided first to make the construction of the `AlgHom` easier,
  which works on `CommRing` which are not necessarily domains.
-/

@[expose] public section


universe u

namespace RatFunc

noncomputable section

open Polynomial

open scoped nonZeroDivisors

variable {R : Type u} [CommRing R] (r s : R) (p q : R[X]) (f : R⟮X⟯)

/--
theorem `taylor_mem_nonZeroDivisors` / 定理 `taylor_mem_nonZeroDivisors`

English:
theorem taylor_mem_nonZeroDivisors
  given: (hp : p in R[X]⁰)
  statement: taylor r p in R[X]⁰
  proof: by
  rw [mem_nonZeroDivisors_iff_right]
  intro x hx
  have : x = taylor (r - r) x := by simp
  rwa [this, sub_eq_add_neg, ← taylor_taylor, ← taylor_mul,
    LinearMap.map_eq_zero_iff _ (taylor_injective _), mul_right_mem_nonZeroDivisors_eq_zero_iff hp,
    LinearMap.map_eq_zero_iff _ (taylor_inject

中文:
定理 taylor_mem_nonZeroDivisors
  条件: (hp : p in R[X]⁰)
  结论: taylor r p in R[X]⁰
  证明: by
  rw [mem_nonZeroDivisors_iff_right]
  intro x hx
  have : x = taylor (r - r) x := by simp
  rwa [this, sub_eq_add_neg, ← taylor_taylor, ← taylor_mul,
    LinearMap.map_eq_zero_iff _ (taylor_injective _), mul_right_mem_nonZeroDivisors_eq_zero_iff hp,
    LinearMap.map_eq_zero_iff _ (taylor_inject

Depends on / 依赖: LinearMap, LinearMap.map_eq_zero_iff, map_eq_zero_iff, mem_nonZeroDivisors_iff_right, mul_right_mem_nonZeroDivisors_eq_zero_iff, sub_eq_add_neg, taylor, taylor_injective, taylor_mul, taylor_taylor
-/
theorem taylor_mem_nonZeroDivisors (hp : p in R[X]⁰) : taylor r p in R[X]⁰ := by
  rw [mem_nonZeroDivisors_iff_right]
  intro x hx
  have : x = taylor (r - r) x := by simp
  rwa [this, sub_eq_add_neg, ← taylor_taylor, ← taylor_mul,
    LinearMap.map_eq_zero_iff _ (taylor_injective _), mul_right_mem_nonZeroDivisors_eq_zero_iff hp,
    LinearMap.map_eq_zero_iff _ (taylor_injective _)] at hx

/--
Definition of `laurentAux` / `laurentAux` 的定义

English:
definition laurentAux
  signature: : R⟮X⟯ ->+* R⟮X⟯
  body: RatFunc.mapRingHom
    ( { toFun := taylor r
        map_add' := map_add (taylor r)
        map_mul' := taylor_mul _
        map_zero' := map_zero (taylor r)
        map_one' := taylor_one r } : R[X] ->+* R[X])
    (taylor_mem_nonZeroDivisors _)

中文:
定义 laurentAux
  签名: : R⟮X⟯ ->+* R⟮X⟯
  定义体: RatFunc.mapRingHom
    ( { toFun := taylor r
        map_add' := map_add (taylor r)
        map_mul' := taylor_mul _
        map_zero' := map_zero (taylor r)
        map_one' := taylor_one r } : R[X] ->+* R[X])
    (taylor_mem_nonZeroDivisors _)

Depends on / 依赖: RatFunc, RatFunc.mapRingHom, mapRingHom, map_add, map_mul, map_one, map_zero, taylor, taylor_mem_nonZeroDivisors, taylor_mul, taylor_one
-/
def laurentAux : R⟮X⟯ ->+* R⟮X⟯ :=
  RatFunc.mapRingHom
    ( { toFun := taylor r
        map_add' := map_add (taylor r)
        map_mul' := taylor_mul _
        map_zero' := map_zero (taylor r)
        map_one' := taylor_one r } : R[X] ->+* R[X])
    (taylor_mem_nonZeroDivisors _)

/--
theorem `laurentAux_ofFractionRing_mk` / 定理 `laurentAux_ofFractionRing_mk`

English:
theorem laurentAux_ofFractionRing_mk
  given: (q : R[X]⁰)
  proof: map_apply_ofFractionRing_mk _ _ _ _

中文:
定理 laurentAux_ofFractionRing_mk
  条件: (q : R[X]⁰)
  证明: map_apply_ofFractionRing_mk _ _ _ _

Depends on / 依赖: map_apply_ofFractionRing_mk
-/
theorem laurentAux_ofFractionRing_mk (q : R[X]⁰) :
    laurentAux r (ofFractionRing (Localization.mk p q)) =
      ofFractionRing (.mk (taylor r p) ⟨taylor r q, taylor_mem_nonZeroDivisors r q q.prop⟩) :=
  map_apply_ofFractionRing_mk _ _ _ _

variable [IsDomain R]

/--
theorem `laurentAux_div` / 定理 `laurentAux_div`

English:
theorem laurentAux_div
  proof: -- Porting note: added `by exact taylor_mem_nonZeroDivisors r`
  map_apply_div _ (by exact taylor_mem_nonZeroDivisors r) _ _

@[simp]

中文:
定理 laurentAux_div
  证明: -- Porting note: added `by exact taylor_mem_nonZeroDivisors r`
  map_apply_div _ (by exact taylor_mem_nonZeroDivisors r) _ _

@[simp]
-/
theorem laurentAux_div :
    laurentAux r (algebraMap _ _ p / algebraMap _ _ q) =
      algebraMap _ _ (taylor r p) / algebraMap _ _ (taylor r q) :=
  -- Porting note: added `by exact taylor_mem_nonZeroDivisors r`
  map_apply_div _ (by exact taylor_mem_nonZeroDivisors r) _ _

@[simp]
/--
theorem `laurentAux_algebraMap` / 定理 `laurentAux_algebraMap`

English:
theorem laurentAux_algebraMap
  statement: laurentAux r (algebraMap _ _ p) = algebraMap _ _ (taylor r p)
  proof: by
  rw [← mk_one]; rw [← mk_one]; rw [mk_eq_div]; rw [laurentAux_div]; rw [mk_eq_div]; rw [taylor_one]; rw [map_one]; rw [map_one]

中文:
定理 laurentAux_algebraMap
  结论: laurentAux r (algebraMap _ _ p) = algebraMap _ _ (taylor r p)
  证明: by
  rw [← mk_one]; rw [← mk_one]; rw [mk_eq_div]; rw [laurentAux_div]; rw [mk_eq_div]; rw [taylor_one]; rw [map_one]; rw [map_one]

Depends on / 依赖: laurentAux_div, map_one, mk_eq_div, mk_one, taylor_one
-/
theorem laurentAux_algebraMap : laurentAux r (algebraMap _ _ p) = algebraMap _ _ (taylor r p) := by
  rw [← mk_one]; rw [← mk_one]; rw [mk_eq_div]; rw [laurentAux_div]; rw [mk_eq_div]; rw [taylor_one]; rw [map_one]; rw [map_one]

/--
Definition of `laurent` / `laurent` 的定义

English:
definition laurent
  signature: : R⟮X⟯ ->ₐ[R] R⟮X⟯
  body: RatFunc.mapAlgHom (.ofLinearMap (taylor r) (taylor_one _) (taylor_mul _))
    (taylor_mem_nonZeroDivisors _)

中文:
定义 laurent
  签名: : R⟮X⟯ ->ₐ[R] R⟮X⟯
  定义体: RatFunc.mapAlgHom (.ofLinearMap (taylor r) (taylor_one _) (taylor_mul _))
    (taylor_mem_nonZeroDivisors _)

Depends on / 依赖: RatFunc, RatFunc.mapAlgHom, mapAlgHom, ofLinearMap, taylor, taylor_mem_nonZeroDivisors, taylor_mul, taylor_one
-/
def laurent : R⟮X⟯ ->ₐ[R] R⟮X⟯ :=
  RatFunc.mapAlgHom (.ofLinearMap (taylor r) (taylor_one _) (taylor_mul _))
    (taylor_mem_nonZeroDivisors _)

/--
theorem `laurent_div` / 定理 `laurent_div`

English:
theorem laurent_div
  proof: laurentAux_div r p q

@[simp]

中文:
定理 laurent_div
  证明: laurentAux_div r p q

@[simp]

Depends on / 依赖: laurentAux_div
-/
theorem laurent_div :
    laurent r (algebraMap _ _ p / algebraMap _ _ q) =
      algebraMap _ _ (taylor r p) / algebraMap _ _ (taylor r q) :=
  laurentAux_div r p q

@[simp]
/--
theorem `laurent_algebraMap` / 定理 `laurent_algebraMap`

English:
theorem laurent_algebraMap
  statement: laurent r (algebraMap _ _ p) = algebraMap _ _ (taylor r p)
  proof: laurentAux_algebraMap _ _

@[simp]

中文:
定理 laurent_algebraMap
  结论: laurent r (algebraMap _ _ p) = algebraMap _ _ (taylor r p)
  证明: laurentAux_algebraMap _ _

@[simp]

Depends on / 依赖: laurentAux_algebraMap
-/
theorem laurent_algebraMap : laurent r (algebraMap _ _ p) = algebraMap _ _ (taylor r p) :=
  laurentAux_algebraMap _ _

@[simp]
/--
theorem `laurent_X` / 定理 `laurent_X`

English:
theorem laurent_X
  statement: laurent r X = X + C r
  proof: by
  rw [← algebraMap_X]; rw [laurent_algebraMap]; rw [taylor_X]; rw [map_add]; rw [algebraMap_C]

@[simp]

中文:
定理 laurent_X
  结论: laurent r X = X + C r
  证明: by
  rw [← algebraMap_X]; rw [laurent_algebraMap]; rw [taylor_X]; rw [map_add]; rw [algebraMap_C]

@[simp]

Depends on / 依赖: algebraMap_C, algebraMap_X, laurent_algebraMap, map_add, taylor_X
-/
theorem laurent_X : laurent r X = X + C r := by
  rw [← algebraMap_X]; rw [laurent_algebraMap]; rw [taylor_X]; rw [map_add]; rw [algebraMap_C]

@[simp]
/--
theorem `laurent_C` / 定理 `laurent_C`

English:
theorem laurent_C
  given: (x : R)
  statement: laurent r (C x) = C x
  proof: by
  rw [← algebraMap_C]; rw [laurent_algebraMap]; rw [taylor_C]

@[simp]

中文:
定理 laurent_C
  条件: (x : R)
  结论: laurent r (C x) = C x
  证明: by
  rw [← algebraMap_C]; rw [laurent_algebraMap]; rw [taylor_C]

@[simp]

Depends on / 依赖: algebraMap_C, laurent_algebraMap, taylor_C
-/
theorem laurent_C (x : R) : laurent r (C x) = C x := by
  rw [← algebraMap_C]; rw [laurent_algebraMap]; rw [taylor_C]

@[simp]
/--
theorem `laurent_at_zero` / 定理 `laurent_at_zero`

English:
theorem laurent_at_zero
  statement: laurent 0 f = f
  proof: by induction f using RatFunc.induction_on; simp

中文:
定理 laurent_at_zero
  结论: laurent 0 f = f
  证明: by induction f using RatFunc.induction_on; simp

Depends on / 依赖: RatFunc, RatFunc.induction_on, induction_on
-/
theorem laurent_at_zero : laurent 0 f = f := by induction f using RatFunc.induction_on; simp

/--
theorem `laurent_laurent` / 定理 `laurent_laurent`

English:
theorem laurent_laurent
  statement: laurent r (laurent s f) = laurent (r + s) f
  proof: by
  induction f using RatFunc.induction_on
  simp_rw [laurent_div, taylor_taylor]

中文:
定理 laurent_laurent
  结论: laurent r (laurent s f) = laurent (r + s) f
  证明: by
  induction f using RatFunc.induction_on
  simp_rw [laurent_div, taylor_taylor]

Depends on / 依赖: RatFunc, RatFunc.induction_on, induction_on, laurent_div, simp_rw, taylor_taylor
-/
theorem laurent_laurent : laurent r (laurent s f) = laurent (r + s) f := by
  induction f using RatFunc.induction_on
  simp_rw [laurent_div, taylor_taylor]

/--
theorem `laurent_injective` / 定理 `laurent_injective`

English:
theorem laurent_injective
  statement: Function.Injective (laurent r)
  proof: fun _ _ h => by
  simpa [laurent_laurent] using congr_arg (laurent (-r)) h

中文:
定理 laurent_injective
  结论: Function.Injective (laurent r)
  证明: fun _ _ h => by
  simpa [laurent_laurent] using congr_arg (laurent (-r)) h

Depends on / 依赖: congr_arg, laurent, laurent_laurent
-/
theorem laurent_injective : Function.Injective (laurent r) := fun _ _ h => by
  simpa [laurent_laurent] using congr_arg (laurent (-r)) h

end

end RatFunc
