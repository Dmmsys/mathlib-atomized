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

/-
**CentroidHom.** 是 Mathlib 中的一个实例，位于命名空间 `CentroidHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Star (CentroidHom α) where
  star f :=
  { toFun := fun a => star (f (star a))
    map_zero' := by
      simp only [star_zero, map_zero]
    map_add' := fun a b => by simp only [star_add, map_add]
    map_mul_left' := fun a b => by simp only [star_mul, map_mul_right, star_star]
    map_mul_right' := fun a b => by simp only [star_mul, map_mul_left, star_star] }
/-
**CentroidHom.star_apply** 是 Mathlib 中的一个定理，位于命名空间 `CentroidHom`。
形式化陈述：∀ {α : Type u_1} [inst : NonUnitalNonAssocSemiring α] [inst_1 : StarRing α
] (f : CentroidHom α) (a : α),   (star f) a = star (f (star a))
参数：f : CentroidHom α；a : α；star f；f (star a)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma star_apply (f : CentroidHom α) (a : α) : (star f) a = star (f (star a)) := rfl
/-
**CentroidHom.instStarAddMonoid** 是 Mathlib 中的一个实例，位于命名空间 `CentroidHom`。
形式化陈述：instStarAddMonoid : StarAddMonoid (CentroidHom α) where star_involutive f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instStarAddMonoid : StarAddMonoid (CentroidHom α) where
  star_involutive f := ext (fun _ => by
    rw [star_apply, star_apply, star_star, star_star])
  star_add _ _ := ext fun _ => star_add _ _
/-
**CentroidHom.** 是 Mathlib 中的一个实例，位于命名空间 `CentroidHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Star (Subsemiring.center (CentroidHom α)) where
  star f := ⟨star (f : CentroidHom α), Subsemiring.mem_center_iff.mpr (fun g => ext (fun a =>
    calc
      g (star (f (star a))) = star (star g (f (star a))) := by rw [star_apply, star_star]
      _ = star ((star g * f) (star a)) := rfl
      _ = star ((f * star g) (star a)) := by rw [f.property.comm]
      _ = star (f (star g (star a))) := rfl
      _ = star (f (star (g a))) := by rw [star_apply, star_star]))⟩
/-
**CentroidHom.instStarAddMonoidCenter** 是 Mathlib 中的一个实例，位于命名空间 `CentroidHom`。
形式化陈述：instStarAddMonoidCenter : StarAddMonoid (Subsemiring.center (CentroidHom α
)) where star_involutive f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instStarAddMonoidCenter : StarAddMonoid (Subsemiring.center (CentroidHom α)) where
  star_involutive f := SetCoe.ext (star_involutive f.val)
  star_add f g := SetCoe.ext (star_add f.val g.val)
/-
**CentroidHom.** 是 Mathlib 中的一个实例，位于命名空间 `CentroidHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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

/-- The canonical \*-homomorphism embedding the center of `CentroidHom α` into `CentroidHom α`. -/
/-
**CentroidHom.centerStarEmbedding** 是 Mathlib 中的一个定义，位于命名空间 `CentroidHom`。
形式化陈述：centerStarEmbedding : Subsemiring.center (CentroidHom α) ->⋆ₙ+* CentroidHo
m α where toNonUnitalRingHom
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical \*-homomorphism embedding the center of `CentroidHom α` into `Cent
roidHom α`.
-/
def centerStarEmbedding : Subsemiring.center (CentroidHom α) →⋆ₙ+* CentroidHom α where
  toNonUnitalRingHom :=
    (SubsemiringClass.subtype (Subsemiring.center (CentroidHom α))).toNonUnitalRingHom
  map_star' _ := rfl
/-
**CentroidHom.star_centerToCentroidCenter** 是 Mathlib 中的一个定理，位于命名空间 `CentroidHom
`。
形式化陈述：star_centerToCentroidCenter (z : NonUnitalStarSubsemiring.center α) : star
 (centerToCentroidCenter z) = (centerToCentroidCenter (star z : NonUnitalStarSub
semiring.center α))
参数：z : NonUnitalStarSubsemiring.center α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `CentroidHom.ext`：ext {f g : CentroidHom α} (h : forall a, f a = g a) : f
 = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `StarMul.star_mul`：∀ {R : Type u} {inst : Mul R} [self : StarMul R] (r s 
: R), star (r * s) = star s * star r
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `star_star`：star_star [InvolutiveStar R] (r : R) : star (star r) = r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IsMulCentral.comm`：∀ {M : Type u_1} [inst : Mul M] {z : M}, IsMulCentral
 z → ∀ (a : M), Commute z a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
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

/-- The canonical \*-homomorphism from the center of a non-unital, non-associative \*-semiring
into the center of its centroid. -/
/-
**CentroidHom.starCenterToCentroidCenter** 是 Mathlib 中的一个定义，位于命名空间 `CentroidHom`
。
形式化陈述：starCenterToCentroidCenter : NonUnitalStarSubsemiring.center α ->⋆ₙ+* Subs
emiring.center (CentroidHom α) where toNonUnitalRingHom
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical \*-homomorphism from the center of a non-unital, non-associative \
*-semiring
into the center of its centroid.
-/
def starCenterToCentroidCenter :
    NonUnitalStarSubsemiring.center α →⋆ₙ+* Subsemiring.center (CentroidHom α) where
  toNonUnitalRingHom := centerToCentroidCenter
  map_star' _ := (star_centerToCentroidCenter _).symm

/-- The canonical homomorphism from the center into the centroid -/
/-
**CentroidHom.starCenterToCentroid** 是 Mathlib 中的一个定义，位于命名空间 `CentroidHom`。
形式化陈述：starCenterToCentroid : NonUnitalStarSubsemiring.center α ->⋆ₙ+* CentroidHo
m α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical homomorphism from the center into the centroid
-/
def starCenterToCentroid : NonUnitalStarSubsemiring.center α →⋆ₙ+* CentroidHom α :=
  NonUnitalStarRingHom.comp (centerStarEmbedding) (starCenterToCentroidCenter)
/-
**CentroidHom.starCenterToCentroid_apply** 是 Mathlib 中的一个引理，位于命名空间 `CentroidHom`
。
形式化陈述：starCenterToCentroid_apply (z : NonUnitalStarSubsemiring.center α) (a : α)
 : (starCenterToCentroid z) a = z * a
参数：z : NonUnitalStarSubsemiring.center α；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma starCenterToCentroid_apply (z : NonUnitalStarSubsemiring.center α) (a : α) :
    (starCenterToCentroid z) a = z * a := rfl

/--
Let `α` be a star ring with commutative centroid. Then the centroid is a star ring.
-/
@[reducible]
/-
**CentroidHom.starRingOfCommCentroidHom** 是 Mathlib 中的一个定义，位于命名空间 `CentroidHom`。
形式化陈述：starRingOfCommCentroidHom (mul_comm : IsMulCommutative (CentroidHom α)) : 
StarRing (CentroidHom α) where __
参数：mul_comm : IsMulCommutative (CentroidHom α)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `α` be a star ring with commutative centroid. Then the centroid is a star ri
ng.
-/
def starRingOfCommCentroidHom (mul_comm : IsMulCommutative (CentroidHom α)) :
    StarRing (CentroidHom α) where
  __ := instStarAddMonoid
  star_mul _ _ := ext fun _ ↦ by simp [mul_comm']

end NonUnitalNonAssocStarSemiring

section NonAssocStarSemiring

variable [NonAssocSemiring α] [StarRing α]

set_option backward.isDefEq.respectTransparency false in
/-- The canonical isomorphism from the center of a (non-associative) semiring onto its centroid. -/
/-
**CentroidHom.starCenterIsoCentroid** 是 Mathlib 中的一个定义，位于命名空间 `CentroidHom`。
形式化陈述：starCenterIsoCentroid : StarSubsemiring.center α ≃⋆+* CentroidHom α where 
__
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical isomorphism from the center of a (non-associative) semiring onto i
ts centroid.
-/
def starCenterIsoCentroid : StarSubsemiring.center α ≃⋆+* CentroidHom α where
  __ := starCenterToCentroid
  invFun T :=
    ⟨T 1, by constructor <;> simp [commute_iff_eq, ← map_mul_left, ← map_mul_right]⟩
  left_inv z := Subtype.ext <| by simp only [MulHom.toFun_eq_coe,
    NonUnitalRingHom.coe_toMulHom, NonUnitalStarRingHom.coe_toNonUnitalRingHom,
    starCenterToCentroid_apply, mul_one]
  right_inv T := CentroidHom.ext <| fun _ => by
    simp [starCenterToCentroid_apply, ← map_mul_right]

@[simp]
/-
**CentroidHom.starCenterIsoCentroid_apply** 是 Mathlib 中的一个引理，位于命名空间 `CentroidHom
`。
形式化陈述：starCenterIsoCentroid_apply (a : ↥(NonUnitalStarSubsemiring.center α)) : C
entroidHom.starCenterIsoCentroid a = CentroidHom.starCenterToCentroid a
参数：a : ↥(NonUnitalStarSubsemiring.center α)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma starCenterIsoCentroid_apply (a : ↥(NonUnitalStarSubsemiring.center α)) :
    CentroidHom.starCenterIsoCentroid a = CentroidHom.starCenterToCentroid a := rfl

@[simp]
/-
**CentroidHom.starCenterIsoCentroid_symm_apply_coe** 是 Mathlib 中的一个引理，位于命名空间 `Ce
ntroidHom`。
形式化陈述：starCenterIsoCentroid_symm_apply_coe (T : CentroidHom α) : ↑(CentroidHom.s
tarCenterIsoCentroid.symm T) = T 1
参数：T : CentroidHom α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma starCenterIsoCentroid_symm_apply_coe (T : CentroidHom α) :
    ↑(CentroidHom.starCenterIsoCentroid.symm T) = T 1 := rfl

end NonAssocStarSemiring

end CentroidHom

