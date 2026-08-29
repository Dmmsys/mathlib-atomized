/-
Copyright (c) 2024 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
module

public import Mathlib.Algebra.Ring.CentroidHom
public import Mathlib.Algebra.Star.StarRingHom
public import Mathlib.Algebra.Star.Subsemiring
public import Mathlib.Algebra.Star.Basic

/-!
# Centroid homomorphisms on Star Rings

When a (nonunital, non-associative) semiring is equipped with an involutive automorphism the
center of the centroid becomes a star ring in a natural way and the natural mapping of the centre of
the semiring into the centre of the centroid becomes a \*-homomorphism.

## Tags

centroid
-/

@[expose] public section

variable {α : Type*}

namespace CentroidHom

section NonUnitalNonAssocStarSemiring

variable [NonUnitalNonAssocSemiring α] [StarRing α]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Star (CentroidHom α)
  body: { toFun := fun a => star (f (star a))
    map_zero' := by
      simp only [star_zero, map_zero]
    map_add' := fun a b => by simp only [star_add, map_add]
    map_mul_left' := fun a b => by simp only [star_mul, map_mul_right, star_star]
    map_mul_right' := fun a b => by simp only [star_mul, map_mul_left, star_star] }

中文:
实例 :
  签名: 对合 (Centroid态射 α)
  定义体: { toFun := fun a => star (f (star a))
    map_zero' := by
      simp only [star_zero, map_zero]
    map_add' := fun a b => by simp only [star_add, map_add]
    map_mul_left' := fun a b => by simp only [star_mul, map_mul_right, star_star]
    map_mul_right' := fun a b => by simp only [star_mul, map_mul_left, star_star] }

Depends on / 依赖: map_add, map_mul_left, map_mul_right, map_zero, star_add, star_mul, star_star, star_zero
-/
instance : Star (CentroidHom α) where
  star f :=
  { toFun := fun a => star (f (star a))
    map_zero' := by
      simp only [star_zero, map_zero]
    map_add' := fun a b => by simp only [star_add, map_add]
    map_mul_left' := fun a b => by simp only [star_mul, map_mul_right, star_star]
    map_mul_right' := fun a b => by simp only [star_mul, map_mul_left, star_star] }

/--
lemma `star_apply` / 引理 `star_apply`

English:
lemma star_apply
  given: (f : CentroidHom α) (a : α)
  statement: (star f) a = star (f (star a))
  proof: rfl

中文:
引理 star_apply
  条件: (f : Centroid态射 α) (a : α)
  结论: (star f) a = star (f (star a))
  证明: rfl
-/
@[simp] lemma star_apply (f : CentroidHom α) (a : α) : (star f) a = star (f (star a)) := rfl

/--
Instance `instStarAddMonoid` / 实例 `instStarAddMonoid`

English:
instance instStarAddMonoid
  signature: : StarAddMonoid (CentroidHom α) where
  body: ext (fun _ => by
    rw [star_apply]; rw [star_apply]; rw [star_star]; rw [star_star])
  star_add _ _ := ext fun _ => star_add _ _

中文:
实例 instStarAddMonoid
  签名: : StarAdd幺半群 (Centroid态射 α) where
  定义体: ext (fun _ => by
    rw [star_apply]; rw [star_apply]; rw [star_star]; rw [star_star])
  star_add _ _ := ext fun _ => star_add _ _

Depends on / 依赖: star_add, star_apply, star_star
-/
instance instStarAddMonoid : StarAddMonoid (CentroidHom α) where
  star_involutive f := ext (fun _ => by
    rw [star_apply]; rw [star_apply]; rw [star_star]; rw [star_star])
  star_add _ _ := ext fun _ => star_add _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Star (Subsemiring.center (CentroidHom α))
  body: ⟨star (f : CentroidHom α), Subsemiring.mem_center_iff.mpr (fun g => ext (fun a =>
    calc
      g (star (f (star a))) = star (star g (f (star a))) := by rw [star_apply, star_star]
      _ = star ((star g * f) (star a)) := rfl
      _ = star ((f * star g) (star a)) := by rw [f.property.comm]
      _ = star (f (star g (star a))) := rfl
      _ = star (f (star (g a))) := by rw [star_apply, star_star]))⟩

中文:
实例 :
  签名: 对合 (子半环.center (Centroid态射 α))
  定义体: ⟨star (f : CentroidHom α), Subsemiring.mem_center_iff.mpr (fun g => ext (fun a =>
    calc
      g (star (f (star a))) = star (star g (f (star a))) := by rw [star_apply, star_star]
      _ = star ((star g * f) (star a)) := rfl
      _ = star ((f * star g) (star a)) := by rw [f.property.comm]
      _ = star (f (star g (star a))) := rfl
      _ = star (f (star (g a))) := by rw [star_apply, star_star]))⟩

Depends on / 依赖: CentroidHom, Subsemiring, Subsemiring.mem_center_iff.mpr, mem_center_iff
-/
instance : Star (Subsemiring.center (CentroidHom α)) where
  star f := ⟨star (f : CentroidHom α), Subsemiring.mem_center_iff.mpr (fun g => ext (fun a =>
    calc
      g (star (f (star a))) = star (star g (f (star a))) := by rw [star_apply, star_star]
      _ = star ((star g * f) (star a)) := rfl
      _ = star ((f * star g) (star a)) := by rw [f.property.comm]
      _ = star (f (star g (star a))) := rfl
      _ = star (f (star (g a))) := by rw [star_apply, star_star]))⟩

/--
Instance `instStarAddMonoidCenter` / 实例 `instStarAddMonoidCenter`

English:
instance instStarAddMonoidCenter
  signature: : StarAddMonoid (Subsemiring.center (CentroidHom α)) where
  body: SetCoe.ext (star_involutive f.val)
  star_add f g := SetCoe.ext (star_add f.val g.val)

中文:
实例 instStarAddMonoidCenter
  签名: : StarAdd幺半群 (子半环.center (Centroid态射 α)) where
  定义体: SetCoe.ext (star_involutive f.val)
  star_add f g := SetCoe.ext (star_add f.val g.val)

Depends on / 依赖: SetCoe, SetCoe.ext, f.val, star_involutive
-/
instance instStarAddMonoidCenter : StarAddMonoid (Subsemiring.center (CentroidHom α)) where
  star_involutive f := SetCoe.ext (star_involutive f.val)
  star_add f g := SetCoe.ext (star_add f.val g.val)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: StarRing (Subsemiring.center (CentroidHom α))
  body: instStarAddMonoidCenter
  star_mul f g := by
    ext a
    calc
      star (f * g) a = star (g * f) a := by rw [CommMonoid.mul_comm f g]
      _ = star (g (f (star a))) := rfl
      _ = star (g (star (star (f (star a))))) := by simp only [star_star]
      _ = (star g * star f) a := rfl

中文:
实例 :
  签名: 对合环 (子半环.center (Centroid态射 α))
  定义体: instStarAddMonoidCenter
  star_mul f g := by
    ext a
    calc
      star (f * g) a = star (g * f) a := by rw [CommMonoid.mul_comm f g]
      _ = star (g (f (star a))) := rfl
      _ = star (g (star (star (f (star a))))) := by simp only [star_star]
      _ = (star g * star f) a := rfl

Depends on / 依赖: instStarAddMonoidCenter
-/
instance : StarRing (Subsemiring.center (CentroidHom α)) where
  __ := instStarAddMonoidCenter
  star_mul f g := by
    ext a
    calc
      star (f * g) a = star (g * f) a := by rw [CommMonoid.mul_comm f g]
      _ = star (g (f (star a))) := rfl
      _ = star (g (star (star (f (star a))))) := by simp only [star_star]
      _ = (star g * star f) a := rfl

/--
Definition of `centerStarEmbedding` / `centerStarEmbedding` 的定义

English:
definition centerStarEmbedding
  signature: : Subsemiring.center (CentroidHom α) ->⋆ₙ+* CentroidHom α where
  body: (SubsemiringClass.subtype (Subsemiring.center (CentroidHom α))).toNonUnitalRingHom
  map_star' _ := rfl

中文:
定义 centerStarEmbedding
  签名: : 子半环.center (Centroid态射 α) ->⋆ₙ+* Centroid态射 α where
  定义体: (SubsemiringClass.subtype (Subsemiring.center (CentroidHom α))).toNonUnitalRingHom
  map_star' _ := rfl

Depends on / 依赖: CentroidHom, Subsemiring, Subsemiring.center, SubsemiringClass, SubsemiringClass.subtype, center, map_star, subtype, toNonUnitalRingHom
-/
def centerStarEmbedding : Subsemiring.center (CentroidHom α) ->⋆ₙ+* CentroidHom α where
  toNonUnitalRingHom :=
    (SubsemiringClass.subtype (Subsemiring.center (CentroidHom α))).toNonUnitalRingHom
  map_star' _ := rfl

/--
theorem `star_centerToCentroidCenter` / 定理 `star_centerToCentroidCenter`

English:
theorem star_centerToCentroidCenter
  given: (z : NonUnitalStarSubsemiring.center α)
  proof: by
  ext a
  calc
      (star (centerToCentroidCenter z)) a = star (z * star a) := rfl
      _ = star (star a) * star z := by simp only [star_mul, star_star, StarMemClass.coe_star]
      _ = a * star z := by rw [star_star]
      _ = (star z) * a := by rw [(star z).property.comm]
      _ = (centerToCentroidCenter ((star z) : NonUnitalStarSubsemiring.center α)) a := rfl

中文:
定理 star_centerToCentroidCenter
  条件: (z : 非幺对合子半环.center α)
  证明: by
  ext a
  calc
      (star (centerToCentroidCenter z)) a = star (z * star a) := rfl
      _ = star (star a) * star z := by simp only [star_mul, star_star, StarMemClass.coe_star]
      _ = a * star z := by rw [star_star]
      _ = (star z) * a := by rw [(star z).property.comm]
      _ = (centerToCentroidCenter ((star z) : NonUnitalStarSubsemiring.center α)) a := rfl

Depends on / 依赖: NonUnitalStarSubsemiring, NonUnitalStarSubsemiring.center, StarMemClass, StarMemClass.coe_star, center, centerToCentroidCenter, coe_star, property, property.comm, star_mul, star_star
-/
theorem star_centerToCentroidCenter (z : NonUnitalStarSubsemiring.center α) :
    star (centerToCentroidCenter z) =
      (centerToCentroidCenter (star z : NonUnitalStarSubsemiring.center α)) := by
  ext a
  calc
      (star (centerToCentroidCenter z)) a = star (z * star a) := rfl
      _ = star (star a) * star z := by simp only [star_mul, star_star, StarMemClass.coe_star]
      _ = a * star z := by rw [star_star]
      _ = (star z) * a := by rw [(star z).property.comm]
      _ = (centerToCentroidCenter ((star z) : NonUnitalStarSubsemiring.center α)) a := rfl

/--
Definition of `starCenterToCentroidCenter` / `starCenterToCentroidCenter` 的定义

English:
definition starCenterToCentroidCenter
  signature: :
  body: centerToCentroidCenter
  map_star' _ := (star_centerToCentroidCenter _).symm

中文:
定义 starCenterToCentroidCenter
  签名: :
  定义体: centerToCentroidCenter
  map_star' _ := (star_centerToCentroidCenter _).symm

Depends on / 依赖: centerToCentroidCenter
-/
def starCenterToCentroidCenter :
    NonUnitalStarSubsemiring.center α ->⋆ₙ+* Subsemiring.center (CentroidHom α) where
  toNonUnitalRingHom := centerToCentroidCenter
  map_star' _ := (star_centerToCentroidCenter _).symm

/--
Definition of `starCenterToCentroid` / `starCenterToCentroid` 的定义

English:
definition starCenterToCentroid
  signature: : NonUnitalStarSubsemiring.center α ->⋆ₙ+* CentroidHom α
  body: NonUnitalStarRingHom.comp (centerStarEmbedding) (starCenterToCentroidCenter)

中文:
定义 starCenterToCentroid
  签名: : 非幺对合子半环.center α ->⋆ₙ+* Centroid态射 α
  定义体: NonUnitalStarRingHom.comp (centerStarEmbedding) (starCenterToCentroidCenter)

Depends on / 依赖: NonUnitalStarRingHom, NonUnitalStarRingHom.comp, centerStarEmbedding, starCenterToCentroidCenter
-/
def starCenterToCentroid : NonUnitalStarSubsemiring.center α ->⋆ₙ+* CentroidHom α :=
  NonUnitalStarRingHom.comp (centerStarEmbedding) (starCenterToCentroidCenter)

/--
lemma `starCenterToCentroid_apply` / 引理 `starCenterToCentroid_apply`

English:
lemma starCenterToCentroid_apply
  given: (z : NonUnitalStarSubsemiring.center α) (a : α)
  proof: rfl

中文:
引理 starCenterToCentroid_apply
  条件: (z : 非幺对合子半环.center α) (a : α)
  证明: rfl
-/
lemma starCenterToCentroid_apply (z : NonUnitalStarSubsemiring.center α) (a : α) :
    (starCenterToCentroid z) a = z * a := rfl

/--
Let `α` be a star ring with commutative centroid. Then the centroid is a star ring.
-/
@[reducible]
/--
Definition of `starRingOfCommCentroidHom` / `starRingOfCommCentroidHom` 的定义

English:
definition starRingOfCommCentroidHom
  signature: (mul_comm : IsMulCommutative (CentroidHom α))
  body: instStarAddMonoid
  star_mul _ _ := ext fun _ => by simp [mul_comm']

中文:
定义 starRingOfCommCentroidHom
  签名: (mul_comm : 是MulCommutative (Centroid态射 α))
  定义体: instStarAddMonoid
  star_mul _ _ := ext fun _ => by simp [mul_comm']

Depends on / 依赖: instStarAddMonoid
-/
def starRingOfCommCentroidHom (mul_comm : IsMulCommutative (CentroidHom α)) :
    StarRing (CentroidHom α) where
  __ := instStarAddMonoid
  star_mul _ _ := ext fun _ => by simp [mul_comm']

end NonUnitalNonAssocStarSemiring

section NonAssocStarSemiring

variable [NonAssocSemiring α] [StarRing α]

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `starCenterIsoCentroid` / `starCenterIsoCentroid` 的定义

English:
definition starCenterIsoCentroid
  signature: : StarSubsemiring.center α ≃⋆+* CentroidHom α where
  body: starCenterToCentroid
  invFun T :=
    ⟨T 1, by constructor <;> simp [commute_iff_eq, ← map_mul_left, ← map_mul_right]⟩
left_inv z := Subtype.ext by simp only [MulHom.toFun_eq_coe,
    NonUnitalRingHom.coe_toMulHom, NonUnitalStarRingHom.coe_toNonUnitalRingHom,
    starCenterToCentroid_apply, mul_one]
right_inv T := CentroidHom.ext fun _ => by
    simp [starCenterToCentroid_apply, ← map_mul_right]

@[simp]

中文:
定义 starCenterIsoCentroid
  签名: : 对合子半环.center α ≃⋆+* Centroid态射 α where
  定义体: starCenterToCentroid
  invFun T :=
    ⟨T 1, by constructor <;> simp [commute_iff_eq, ← map_mul_left, ← map_mul_right]⟩
left_inv z := Subtype.ext by simp only [MulHom.toFun_eq_coe,
    NonUnitalRingHom.coe_toMulHom, NonUnitalStarRingHom.coe_toNonUnitalRingHom,
    starCenterToCentroid_apply, mul_one]
right_inv T := CentroidHom.ext fun _ => by
    simp [starCenterToCentroid_apply, ← map_mul_right]

@[simp]

Depends on / 依赖: starCenterToCentroid
-/
def starCenterIsoCentroid : StarSubsemiring.center α ≃⋆+* CentroidHom α where
  __ := starCenterToCentroid
  invFun T :=
    ⟨T 1, by constructor <;> simp [commute_iff_eq, ← map_mul_left, ← map_mul_right]⟩
left_inv z := Subtype.ext by simp only [MulHom.toFun_eq_coe,
    NonUnitalRingHom.coe_toMulHom, NonUnitalStarRingHom.coe_toNonUnitalRingHom,
    starCenterToCentroid_apply, mul_one]
right_inv T := CentroidHom.ext fun _ => by
    simp [starCenterToCentroid_apply, ← map_mul_right]

@[simp]
/--
lemma `starCenterIsoCentroid_apply` / 引理 `starCenterIsoCentroid_apply`

English:
lemma starCenterIsoCentroid_apply
  given: (a : ↥(NonUnitalStarSubsemiring.center α))
  proof: rfl

@[simp]

中文:
引理 starCenterIsoCentroid_apply
  条件: (a : ↥(非幺对合子半环.center α))
  证明: rfl

@[simp]
-/
lemma starCenterIsoCentroid_apply (a : ↥(NonUnitalStarSubsemiring.center α)) :
    CentroidHom.starCenterIsoCentroid a = CentroidHom.starCenterToCentroid a := rfl

@[simp]
/--
lemma `starCenterIsoCentroid_symm_apply_coe` / 引理 `starCenterIsoCentroid_symm_apply_coe`

English:
lemma starCenterIsoCentroid_symm_apply_coe
  given: (T : CentroidHom α)
  proof: rfl

中文:
引理 starCenterIsoCentroid_symm_apply_coe
  条件: (T : Centroid态射 α)
  证明: rfl
-/
lemma starCenterIsoCentroid_symm_apply_coe (T : CentroidHom α) :
    ↑(CentroidHom.starCenterIsoCentroid.symm T) = T 1 := rfl

end NonAssocStarSemiring

end CentroidHom
