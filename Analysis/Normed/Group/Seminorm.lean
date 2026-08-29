/-
Copyright (c) 2022 María Inés de Frutos-Fernández, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Yaël Dillies
-/
module

public import Mathlib.Data.NNReal.Defs
public import Mathlib.Order.ConditionallyCompleteLattice.Group
public import Mathlib.Data.FunLike.Module

/-!
# Group seminorms

This file defines norms and seminorms in a group. A group seminorm is a function to the reals which
is positive-semidefinite and subadditive. A norm further only maps zero to zero.

## Main declarations

* `AddGroupSeminorm`: A function `f` from an additive group `G` to the reals that preserves zero,
  takes nonnegative values, is subadditive and such that `f (-x) = f x` for all `x`.
* `NonarchAddGroupSeminorm`: A function `f` from an additive group `G` to the reals that
  preserves zero, takes nonnegative values, is nonarchimedean and such that `f (-x) = f x`
  for all `x`.
* `GroupSeminorm`: A function `f` from a group `G` to the reals that sends one to zero, takes
  nonnegative values, is submultiplicative and such that `f x⁻¹ = f x` for all `x`.
* `AddGroupNorm`: A seminorm `f` such that `f x = 0 → x = 0` for all `x`.
* `NonarchAddGroupNorm`: A nonarchimedean seminorm `f` such that `f x = 0 → x = 0` for all `x`.
* `GroupNorm`: A seminorm `f` such that `f x = 0 → x = 1` for all `x`.

## Notes

The corresponding hom classes are defined in `Analysis.Order.Hom.Basic` to be used by absolute
values.

We do not define `NonarchAddGroupSeminorm` as an extension of `AddGroupSeminorm` to avoid
having a superfluous `add_le'` field in the resulting structure. The same applies to
`NonarchAddGroupNorm`.

## References

* [H. H. Schaefer, *Topological Vector Spaces*][schaefer1966]

## Tags

norm, seminorm
-/

@[expose] public section

assert_not_exists Finset

open Set

open NNReal

variable {R R' E F G : Type*}

/--
Definition of `AddGroupSeminorm` / `AddGroupSeminorm` 的定义

English:
structure AddGroupSeminorm
  parameters: (G : Type*) [AddGroup G]
  axioms and operations (4):
    - toFun : G -> Real
    - map_zero' : toFun 0 = 0
    - add_le' : forall r s, toFun (r + s) <= toFun r + toFun s
    - neg' : forall r, toFun (-r) = toFun r

中文:
结构 加法群半范数
  参数: (G : 类型) [加法群 G]
  公理与运算 (4 个):
    - toFun : G -> 实数
    - map_zero' : toFun 0 = 0
    - add_le' : 对任意 r s, toFun (r + s) <= toFun r + toFun s
    - neg' : 对任意 r, toFun (-r) = toFun r
-/
structure AddGroupSeminorm (G : Type*) [AddGroup G] where
  -- Porting note: can't extend `ZeroHom G ℝ` because otherwise `to_additive` won't work since
  -- we aren't using old structures
  /-- The bare function of an `AddGroupSeminorm`. -/
  protected toFun : G -> Real
  /-- The image of zero is zero. -/
  protected map_zero' : toFun 0 = 0
  /-- The seminorm is subadditive. -/
  protected add_le' : forall r s, toFun (r + s) <= toFun r + toFun s
  /-- The seminorm is invariant under negation. -/
  protected neg' : forall r, toFun (-r) = toFun r

/-- A seminorm on a group `G` is a function `f : G → ℝ` that sends one to zero, is submultiplicative
and such that `f x⁻¹ = f x` for all `x`. -/
@[to_additive]
/--
Definition of `GroupSeminorm` / `GroupSeminorm` 的定义

English:
structure GroupSeminorm
  parameters: (G : Type*) [Group G]
  axioms and operations (4):
    - toFun : G -> Real
    - map_one' : toFun 1 = 0
    - mul_le' : forall x y, toFun (x * y) <= toFun x + toFun y
    - inv' : forall x, toFun x⁻¹ = toFun x

中文:
结构 群半范数
  参数: (G : 类型) [群 G]
  公理与运算 (4 个):
    - toFun : G -> 实数
    - map_one' : toFun 1 = 0
    - mul_le' : 对任意 x y, toFun (x * y) <= toFun x + toFun y
    - inv' : 对任意 x, toFun x⁻¹ = toFun x
-/
structure GroupSeminorm (G : Type*) [Group G] where
  /-- The bare function of a `GroupSeminorm`. -/
  protected toFun : G -> Real
  /-- The image of one is zero. -/
  protected map_one' : toFun 1 = 0
  /-- The seminorm applied to a product is dominated by the sum of the seminorm applied to the
  factors. -/
  protected mul_le' : forall x y, toFun (x * y) <= toFun x + toFun y
  /-- The seminorm is invariant under inversion. -/
  protected inv' : forall x, toFun x⁻¹ = toFun x

/--
Definition of `NonarchAddGroupSeminorm` / `NonarchAddGroupSeminorm` 的定义

English:
structure NonarchAddGroupSeminorm
  parameters: (G : Type*) [AddGroup G]
  extends: ZeroHom G Real
  axioms and operations (2):
    - add_le_max' : forall r s, toFun (r + s) <= max (toFun r) (toFun s)
    - neg' : forall r, toFun (-r) = toFun r

中文:
结构 NonarchAdd群半范数
  参数: (G : 类型) [加法群 G]
  继承: 保零态射 G 实数
  公理与运算 (2 个):
    - add_le_max' : 对任意 r s, toFun (r + s) <= 最大值 (toFun r) (toFun s)
    - neg' : 对任意 r, toFun (-r) = toFun r
-/
structure NonarchAddGroupSeminorm (G : Type*) [AddGroup G] extends ZeroHom G Real where
  /-- The seminorm applied to a sum is dominated by the maximum of the function applied to the
  addends. -/
  protected add_le_max' : forall r s, toFun (r + s) <= max (toFun r) (toFun s)
  /-- The seminorm is invariant under negation. -/
  protected neg' : forall r, toFun (-r) = toFun r

/-! NOTE: We do not define `NonarchAddGroupSeminorm` as an extension of `AddGroupSeminorm`
  to avoid having a superfluous `add_le'` field in the resulting structure. The same applies to
  `NonarchAddGroupNorm` below. -/


/--
Definition of `AddGroupNorm` / `AddGroupNorm` 的定义

English:
structure AddGroupNorm
  parameters: (G : Type*) [AddGroup G]
  extends: AddGroupSeminorm G
  axioms and operations (1):
    - eq_zero_of_map_eq_zero' : forall x, toFun x = 0 -> x = 0

中文:
结构 加法群范数
  参数: (G : 类型) [加法群 G]
  继承: 加法群半范数 G
  公理与运算 (1 个):
    - eq_zero_of_map_eq_zero' : 对任意 x, toFun x = 0 -> x = 0
-/
structure AddGroupNorm (G : Type*) [AddGroup G] extends AddGroupSeminorm G where
  /-- If the image under the seminorm is zero, then the argument is zero. -/
  protected eq_zero_of_map_eq_zero' : forall x, toFun x = 0 -> x = 0

/-- A seminorm on a group `G` is a function `f : G → ℝ` that sends one to zero, is submultiplicative
and such that `f x⁻¹ = f x` and `f x = 0 → x = 1` for all `x`. -/
@[to_additive]
/--
Definition of `GroupNorm` / `GroupNorm` 的定义

English:
structure GroupNorm
  parameters: (G : Type*) [Group G]
  extends: GroupSeminorm G
  axioms and operations (1):
    - eq_one_of_map_eq_zero' : forall x, toFun x = 0 -> x = 1

中文:
结构 群范数
  参数: (G : 类型) [群 G]
  继承: 群半范数 G
  公理与运算 (1 个):
    - eq_one_of_map_eq_zero' : 对任意 x, toFun x = 0 -> x = 1
-/
structure GroupNorm (G : Type*) [Group G] extends GroupSeminorm G where
  /-- If the image under the norm is zero, then the argument is one. -/
  protected eq_one_of_map_eq_zero' : forall x, toFun x = 0 -> x = 1

/--
Definition of `NonarchAddGroupNorm` / `NonarchAddGroupNorm` 的定义

English:
structure NonarchAddGroupNorm
  parameters: (G : Type*) [AddGroup G]
  extends: NonarchAddGroupSeminorm G
  axioms and operations (1):
    - eq_zero_of_map_eq_zero' : forall x, toFun x = 0 -> x = 0

中文:
结构 NonarchAdd群范数
  参数: (G : 类型) [加法群 G]
  继承: NonarchAdd群半范数 G
  公理与运算 (1 个):
    - eq_zero_of_map_eq_zero' : 对任意 x, toFun x = 0 -> x = 0
-/
structure NonarchAddGroupNorm (G : Type*) [AddGroup G] extends NonarchAddGroupSeminorm G where
  /-- If the image under the norm is zero, then the argument is zero. -/
  protected eq_zero_of_map_eq_zero' : forall x, toFun x = 0 -> x = 0

/--
Definition of `NonarchAddGroupSeminormClass` / `NonarchAddGroupSeminormClass` 的定义

English:
class NonarchAddGroupSeminormClass
  parameters: (F : Type*) (α : outParam Type*)
  extends: NonarchimedeanHomClass F α Real
  axioms and operations (2):
    - map_zero((f : F)) : f 0 = 0
    - map_neg_eq_map'((f : F) (a : α)) : f (-a) = f a

中文:
类 NonarchAdd群半范数类
  参数: (F : 类型) (α : outParam 类型)
  继承: Nonarchimedean态射类 F α 实数
  公理与运算 (2 个):
    - map_zero((f : F)) : f 0 = 0
    - map_neg_eq_map'((f : F) (a : α)) : f (-a) = f a
-/
class NonarchAddGroupSeminormClass (F : Type*) (α : outParam Type*)
    [AddGroup α] [FunLike F α Real] : Prop
    extends NonarchimedeanHomClass F α Real where
  /-- The image of zero is zero. -/
  protected map_zero (f : F) : f 0 = 0
  /-- The seminorm is invariant under negation. -/
  protected map_neg_eq_map' (f : F) (a : α) : f (-a) = f a

/--
Definition of `NonarchAddGroupNormClass` / `NonarchAddGroupNormClass` 的定义

English:
class NonarchAddGroupNormClass
  parameters: (F : Type*) (α : outParam Type*) [AddGroup α] [FunLike F α Real]
  extends: NonarchAddGroupSeminormClass F α
  axioms and operations (1):
    - eq_zero_of_map_eq_zero((f : F) {a : α}) : f a = 0 -> a = 0

中文:
类 NonarchAdd群范数类
  参数: (F : 类型) (α : outParam 类型) [加法群 α] [函数状 F α 实数]
  继承: NonarchAdd群半范数类 F α
  公理与运算 (1 个):
    - eq_zero_of_map_eq_zero((f : F) {a : α}) : f a = 0 -> a = 0
-/
class NonarchAddGroupNormClass (F : Type*) (α : outParam Type*) [AddGroup α] [FunLike F α Real] : Prop
    extends NonarchAddGroupSeminormClass F α where
  /-- If the image under the norm is zero, then the argument is zero. -/
  protected eq_zero_of_map_eq_zero (f : F) {a : α} : f a = 0 -> a = 0

section NonarchAddGroupSeminormClass

variable [AddGroup E] [FunLike F E Real] [NonarchAddGroupSeminormClass F E] (f : F) (x y : E)

/--
theorem `map_sub_le_max` / 定理 `map_sub_le_max`

English:
theorem map_sub_le_max
  statement: f (x - y) <= max (f x) (f y)
  proof: by
  rw [sub_eq_add_neg]; rw [← NonarchAddGroupSeminormClass.map_neg_eq_map' f y]
  exact map_add_le_max _ _ _

中文:
定理 map_sub_le_max
  结论: f (x - y) <= 最大值 (f x) (f y)
  证明: by
  rw [sub_eq_add_neg]; rw [← NonarchAddGroupSeminormClass.map_neg_eq_map' f y]
  exact map_add_le_max _ _ _

Depends on / 依赖: NonarchAddGroupSeminormClass, NonarchAddGroupSeminormClass.map_neg_eq_map, map_add_le_max, map_neg_eq_map, sub_eq_add_neg
-/
theorem map_sub_le_max : f (x - y) <= max (f x) (f y) := by
  rw [sub_eq_add_neg]; rw [← NonarchAddGroupSeminormClass.map_neg_eq_map' f y]
  exact map_add_le_max _ _ _

end NonarchAddGroupSeminormClass

-- See note [lower instance priority]
instance (priority := 100) NonarchAddGroupSeminormClass.toAddGroupSeminormClass
    [FunLike F E Real] [AddGroup E] [NonarchAddGroupSeminormClass F E] : AddGroupSeminormClass F E Real :=
  { ‹NonarchAddGroupSeminormClass F E› with
    map_add_le_add := fun f _ _ =>
      haveI h_nonneg : forall a, 0 <= f a := by
        intro a
        rw [← NonarchAddGroupSeminormClass.map_zero f]; rw [← sub_self a]
        exact le_trans (map_sub_le_max _ _ _) (by rw [max_self (f a)])
      le_trans (map_add_le_max _ _ _)
        (max_le (le_add_of_nonneg_right (h_nonneg _)) (le_add_of_nonneg_left (h_nonneg _)))
    map_neg_eq_map := NonarchAddGroupSeminormClass.map_neg_eq_map' }

-- See note [lower instance priority]
instance (priority := 100) NonarchAddGroupNormClass.toAddGroupNormClass
    [FunLike F E Real] [AddGroup E] [NonarchAddGroupNormClass F E] : AddGroupNormClass F E Real :=
  { ‹NonarchAddGroupNormClass F E› with
    map_add_le_add := map_add_le_add
    map_neg_eq_map := NonarchAddGroupSeminormClass.map_neg_eq_map' }

/-! ### Seminorms -/


namespace GroupSeminorm

section Group

variable [Group E] [Group F] [Group G] {p q : GroupSeminorm E}

@[to_additive]
/--
Instance `funLike` / 实例 `funLike`

English:
instance funLike
  signature: : FunLike (GroupSeminorm E) E Real where
  body: f.toFun
  coe_injective f g h := by cases f; cases g; congr

@[to_additive]

中文:
实例 funLike
  签名: : 函数状 (群半范数 E) E 实数 where
  定义体: f.toFun
  coe_injective f g h := by cases f; cases g; congr

@[to_additive]

Depends on / 依赖: f.toFun
-/
instance funLike : FunLike (GroupSeminorm E) E Real where
  coe f := f.toFun
  coe_injective f g h := by cases f; cases g; congr

@[to_additive]
/--
Instance `groupSeminormClass` / 实例 `groupSeminormClass`

English:
instance groupSeminormClass
  signature: : GroupSeminormClass (GroupSeminorm E) E Real where
  body: f.map_one'
  map_mul_le_add f := f.mul_le'
  map_inv_eq_map f := f.inv'

@[to_additive (attr := simp)]

中文:
实例 groupSeminormClass
  签名: : 群半范数类 (群半范数 E) E 实数 where
  定义体: f.map_one'
  map_mul_le_add f := f.mul_le'
  map_inv_eq_map f := f.inv'

@[to_additive (attr := simp)]

Depends on / 依赖: f.map_one, map_one
-/
instance groupSeminormClass : GroupSeminormClass (GroupSeminorm E) E Real where
  map_one_eq_zero f := f.map_one'
  map_mul_le_add f := f.mul_le'
  map_inv_eq_map f := f.inv'

@[to_additive (attr := simp)]
/--
theorem `toFun_eq_coe` / 定理 `toFun_eq_coe`

English:
theorem toFun_eq_coe
  statement: p.toFun = p
  proof: rfl

@[to_additive (attr := ext)]

中文:
定理 toFun_eq_coe
  结论: p.toFun = p
  证明: rfl

@[to_additive (attr := ext)]
-/
theorem toFun_eq_coe : p.toFun = p :=
  rfl

@[to_additive (attr := ext)]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  statement: (forall x, p x = q x) -> p = q
  proof: DFunLike.ext p q

@[to_additive]

中文:
定理 ext
  结论: (对任意 x, p x = q x) -> p = q
  证明: DFunLike.ext p q

@[to_additive]

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem ext : (forall x, p x = q x) -> p = q :=
  DFunLike.ext p q

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (GroupSeminorm E)
  body: PartialOrder.lift _ DFunLike.coe_injective

@[to_additive]

中文:
实例 :
  签名: 偏序 (群半范数 E)
  定义体: PartialOrder.lift _ DFunLike.coe_injective

@[to_additive]

Depends on / 依赖: DFunLike, DFunLike.coe_injective, PartialOrder, PartialOrder.lift, coe_injective
-/
instance : PartialOrder (GroupSeminorm E) :=
  PartialOrder.lift _ DFunLike.coe_injective

@[to_additive]
/--
theorem `le_def` / 定理 `le_def`

English:
theorem le_def
  statement: p <= q ↔ (p : E -> Real) <= q
  proof: Iff.rfl

@[to_additive]

中文:
定理 le_def
  结论: p <= q ↔ (p : E -> 实数) <= q
  证明: Iff.rfl

@[to_additive]

Depends on / 依赖: Iff.rfl
-/
theorem le_def : p <= q ↔ (p : E -> Real) <= q :=
  Iff.rfl

@[to_additive]
/--
theorem `lt_def` / 定理 `lt_def`

English:
theorem lt_def
  statement: p < q ↔ (p : E -> Real) < q
  proof: Iff.rfl

@[to_additive (attr := simp, norm_cast)]

中文:
定理 lt_def
  结论: p < q ↔ (p : E -> 实数) < q
  证明: Iff.rfl

@[to_additive (attr := simp, norm_cast)]

Depends on / 依赖: Iff.rfl
-/
theorem lt_def : p < q ↔ (p : E -> Real) < q :=
  Iff.rfl

@[to_additive (attr := simp, norm_cast)]
/--
theorem `coe_le_coe` / 定理 `coe_le_coe`

English:
theorem coe_le_coe
  statement: (p : E -> Real) <= q ↔ p <= q
  proof: Iff.rfl

@[to_additive (attr := simp, norm_cast)]

中文:
定理 coe_le_coe
  结论: (p : E -> 实数) <= q ↔ p <= q
  证明: Iff.rfl

@[to_additive (attr := simp, norm_cast)]

Depends on / 依赖: Iff.rfl
-/
theorem coe_le_coe : (p : E -> Real) <= q ↔ p <= q :=
  Iff.rfl

@[to_additive (attr := simp, norm_cast)]
/--
theorem `coe_lt_coe` / 定理 `coe_lt_coe`

English:
theorem coe_lt_coe
  statement: (p : E -> Real) < q ↔ p < q
  proof: Iff.rfl

中文:
定理 coe_lt_coe
  结论: (p : E -> 实数) < q ↔ p < q
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem coe_lt_coe : (p : E -> Real) < q ↔ p < q :=
  Iff.rfl

variable (p q) (f : F ->* E)

@[to_additive]
/--
Instance `instZeroGroupSeminorm` / 实例 `instZeroGroupSeminorm`

English:
instance instZeroGroupSeminorm
  signature: : Zero (GroupSeminorm E)
  body: ⟨{ toFun := 0
      map_one' := Pi.zero_apply _
      mul_le' := fun _ _ => (zero_add _).ge
      inv' := fun _ => rfl }⟩

@[to_additive]

中文:
实例 instZeroGroupSeminorm
  签名: : 零 (群半范数 E)
  定义体: ⟨{ toFun := 0
      map_one' := Pi.zero_apply _
      mul_le' := fun _ _ => (zero_add _).ge
      inv' := fun _ => rfl }⟩

@[to_additive]

Depends on / 依赖: Pi.zero_apply, map_one, mul_le, zero_add, zero_apply
-/
instance instZeroGroupSeminorm : Zero (GroupSeminorm E) :=
  ⟨{ toFun := 0
      map_one' := Pi.zero_apply _
      mul_le' := fun _ _ => (zero_add _).ge
      inv' := fun _ => rfl }⟩

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsZeroApply (GroupSeminorm E) E Real
  body: rfl

@[deprecated (since := "2026-07-10")] alias _root_.GroupSeminorm.coe_zero := FunLike.coe_zero
@[deprecated (since := "2026-07-10")] alias _root_.AddGroupSeminorm.coe_zero := FunLike.coe_zero

@[deprecated (since := "2026-07-10")] protected alias _root_.GroupSeminorm.zero_apply :=
  zero_apply
@

中文:
实例 :
  签名: 是ZeroApply (群半范数 E) E 实数
  定义体: rfl

@[deprecated (since := "2026-07-10")] alias _root_.GroupSeminorm.coe_zero := FunLike.coe_zero
@[deprecated (since := "2026-07-10")] alias _root_.AddGroupSeminorm.coe_zero := FunLike.coe_zero

@[deprecated (since := "2026-07-10")] protected alias _root_.GroupSeminorm.zero_apply :=
  zero_apply
@
-/
instance : IsZeroApply (GroupSeminorm E) E Real where
  zero_apply _ := rfl

@[deprecated (since := "2026-07-10")] alias _root_.GroupSeminorm.coe_zero := FunLike.coe_zero
@[deprecated (since := "2026-07-10")] alias _root_.AddGroupSeminorm.coe_zero := FunLike.coe_zero

@[deprecated (since := "2026-07-10")] protected alias _root_.GroupSeminorm.zero_apply :=
  zero_apply
@[deprecated (since := "2026-07-10")] protected alias _root_.AddGroupSeminorm.zero_apply :=
  zero_apply

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (GroupSeminorm E)
  body: ⟨0⟩

@[to_additive]

中文:
实例 :
  签名: 可居 (群半范数 E)
  定义体: ⟨0⟩

@[to_additive]
-/
instance : Inhabited (GroupSeminorm E) :=
  ⟨0⟩

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Add (GroupSeminorm E)
  body: ⟨fun p q =>
    { toFun := fun x => p x + q x
      map_one' := by simp_rw [map_one_eq_zero p, map_one_eq_zero q, zero_add]
      mul_le' := fun _ _ =>
(add_le_add (map_mul_le_add p _ _) <| map_mul_le_add q _ _).trans_eq
          add_add_add_comm _ _ _ _
      inv' := fun x => by simp_rw [map_inv_e

中文:
实例 :
  签名: 加法 (群半范数 E)
  定义体: ⟨fun p q =>
    { toFun := fun x => p x + q x
      map_one' := by simp_rw [map_one_eq_zero p, map_one_eq_zero q, zero_add]
      mul_le' := fun _ _ =>
(add_le_add (map_mul_le_add p _ _) <| map_mul_le_add q _ _).trans_eq
          add_add_add_comm _ _ _ _
      inv' := fun x => by simp_rw [map_inv_e

Depends on / 依赖: add_add_add_comm, add_le_add, map_inv_eq_map, map_mul_le_add, map_one, map_one_eq_zero, mul_le, simp_rw, trans_eq, zero_add
-/
instance : Add (GroupSeminorm E) :=
  ⟨fun p q =>
    { toFun := fun x => p x + q x
      map_one' := by simp_rw [map_one_eq_zero p, map_one_eq_zero q, zero_add]
      mul_le' := fun _ _ =>
(add_le_add (map_mul_le_add p _ _) <| map_mul_le_add q _ _).trans_eq
          add_add_add_comm _ _ _ _
      inv' := fun x => by simp_rw [map_inv_eq_map p, map_inv_eq_map q] }⟩

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsAddApply (GroupSeminorm E) E Real
  body: rfl

@[deprecated (since := "2026-07-10")] alias _root_.GroupSeminorm.coe_add := FunLike.coe_add
@[deprecated (since := "2026-07-10")] alias _root_.AddGroupSeminorm.coe_add := FunLike.coe_add

@[deprecated (since := "2026-07-10")] protected alias _root_.GroupSeminorm.add_apply :=
  add_apply
@[depre

中文:
实例 :
  签名: 是加法Apply (群半范数 E) E 实数
  定义体: rfl

@[deprecated (since := "2026-07-10")] alias _root_.GroupSeminorm.coe_add := FunLike.coe_add
@[deprecated (since := "2026-07-10")] alias _root_.AddGroupSeminorm.coe_add := FunLike.coe_add

@[deprecated (since := "2026-07-10")] protected alias _root_.GroupSeminorm.add_apply :=
  add_apply
@[depre
-/
instance : IsAddApply (GroupSeminorm E) E Real where
  add_apply _ _ _ := rfl

@[deprecated (since := "2026-07-10")] alias _root_.GroupSeminorm.coe_add := FunLike.coe_add
@[deprecated (since := "2026-07-10")] alias _root_.AddGroupSeminorm.coe_add := FunLike.coe_add

@[deprecated (since := "2026-07-10")] protected alias _root_.GroupSeminorm.add_apply :=
  add_apply
@[deprecated (since := "2026-07-10")] protected alias _root_.AddGroupSeminorm.add_apply :=
  add_apply

open scoped Classical in
@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SupSet (GroupSeminorm E)
  body: if h : BddAbove s then
      { toFun x := ⨆ p : s, p.1 x
        map_one' := by simp
        mul_le' x y := by
          obtain (rfl | hs) := eq_empty_or_nonempty s
          · simp
          · have : Nonempty s := hs.to_subtype
            refine ciSup_le fun p => (map_mul_le_add p.1 x y).trans ?_


中文:
实例 :
  签名: 上确界集 (群半范数 E)
  定义体: if h : BddAbove s then
      { toFun x := ⨆ p : s, p.1 x
        map_one' := by simp
        mul_le' x y := by
          obtain (rfl | hs) := eq_empty_or_nonempty s
          · simp
          · have : Nonempty s := hs.to_subtype
            refine ciSup_le fun p => (map_mul_le_add p.1 x y).trans ?_


Depends on / 依赖: BddAbove, DFunLike, DFunLike.coe, Monotone, Monotone.map_bddAbove, Nonempty, Set.range_comp, Subtype, Subtype.val, all_goals, ciSup_le, eq_empty_or_nonempty, hs.to_subtype, le_ciSup, map_bddAbove, map_mul_le_add, map_one, mul_le, range_comp, to_subtype
-/
noncomputable instance : SupSet (GroupSeminorm E) where
  sSup s :=
    if h : BddAbove s then
      { toFun x := ⨆ p : s, p.1 x
        map_one' := by simp
        mul_le' x y := by
          obtain (rfl | hs) := eq_empty_or_nonempty s
          · simp
          · have : Nonempty s := hs.to_subtype
            refine ciSup_le fun p => (map_mul_le_add p.1 x y).trans ?_
            gcongr
            all_goals
              apply le_ciSup (f := (DFunLike.coe · _) ∘ Subtype.val) ?_ p
              simpa [Set.range_comp] using Monotone.map_bddAbove (fun _ _ h' => by exact h' _) h
        inv' x := by simp }
    else 0

@[to_additive]
/--
lemma `sSup_of_not_bddAbove` / 引理 `sSup_of_not_bddAbove`

English:
lemma sSup_of_not_bddAbove
  given: {s : Set (GroupSeminorm E)} (hs : ¬BddAbove s)
  proof: by
  simp [SupSet.sSup, hs]

@[to_additive]

中文:
引理 sSup_of_not_bddAbove
  条件: {s : 集合 (群半范数 E)} (hs : ¬BddAbove s)
  证明: by
  simp [SupSet.sSup, hs]

@[to_additive]

Depends on / 依赖: SupSet, SupSet.sSup
-/
lemma sSup_of_not_bddAbove {s : Set (GroupSeminorm E)} (hs : ¬BddAbove s) :
    sSup s = 0 := by
  simp [SupSet.sSup, hs]

@[to_additive]
/--
lemma `coe_sSup_apply` / 引理 `coe_sSup_apply`

English:
lemma coe_sSup_apply
  given: {s : Set (GroupSeminorm E)} (hs : BddAbove s) {x : E}
  proof: by
  simp [SupSet.sSup, hs]
  rfl

@[to_additive]

中文:
引理 coe_sSup_apply
  条件: {s : 集合 (群半范数 E)} (hs : BddAbove s) {x : E}
  证明: by
  simp [SupSet.sSup, hs]
  rfl

@[to_additive]

Depends on / 依赖: SupSet, SupSet.sSup
-/
lemma coe_sSup_apply {s : Set (GroupSeminorm E)} (hs : BddAbove s) {x : E} :
    ⇑(sSup s) x = ⨆ p : s, (p : GroupSeminorm E) x := by
  simp [SupSet.sSup, hs]
  rfl

@[to_additive]
/--
lemma `coe_sSup_apply'` / 引理 `coe_sSup_apply'`

English:
lemma coe_sSup_apply'
  given: {s : Set (GroupSeminorm E)} (hs : BddAbove s) {x : E}
  proof: by
  rw [coe_sSup_apply hs]; rw [← sSup_range]
  congr
  ext
  simp

@[to_additive]

中文:
引理 coe_sSup_apply'
  条件: {s : 集合 (群半范数 E)} (hs : BddAbove s) {x : E}
  证明: by
  rw [coe_sSup_apply hs]; rw [← sSup_range]
  congr
  ext
  simp

@[to_additive]

Depends on / 依赖: coe_sSup_apply, sSup_range
-/
lemma coe_sSup_apply' {s : Set (GroupSeminorm E)} (hs : BddAbove s) {x : E} :
    ⇑(sSup s) x = sSup ((· x) '' s) := by
  rw [coe_sSup_apply hs]; rw [← sSup_range]
  congr
  ext
  simp

@[to_additive]
/--
lemma `coe_iSup_apply` / 引理 `coe_iSup_apply`

English:
lemma coe_iSup_apply
  given: {ι : Type*} (f : ι -> GroupSeminorm E) (h : BddAbove (range f)) {x : E}
  proof: by
  rw [← sSup_range]; rw [coe_sSup_apply h]
.symm exact (Set.rangeFactorization_surjective.iSup_congr _ (by simp))

@[to_additive]

中文:
引理 coe_iSup_apply
  条件: {ι : 类型} (f : ι -> 群半范数 E) (h : BddAbove (range f)) {x : E}
  证明: by
  rw [← sSup_range]; rw [coe_sSup_apply h]
.symm exact (Set.rangeFactorization_surjective.iSup_congr _ (by simp))

@[to_additive]

Depends on / 依赖: Set.rangeFactorization_surjective.iSup_congr, coe_sSup_apply, iSup_congr, rangeFactorization_surjective, sSup_range
-/
lemma coe_iSup_apply {ι : Type*} (f : ι -> GroupSeminorm E) (h : BddAbove (range f)) {x : E} :
    ⇑(⨆ i, f i) x = ⨆ i, (f i : GroupSeminorm E) x := by
  rw [← sSup_range]; rw [coe_sSup_apply h]
.symm exact (Set.rangeFactorization_surjective.iSup_congr _ (by simp))

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Max (GroupSeminorm E)
  body: ⟨fun p q =>
    { toFun := p ⊔ q
      map_one' := by
        rw [Pi.sup_apply]; rw [← map_one_eq_zero p]; rw [sup_eq_left]; rw [map_one_eq_zero p]; rw [map_one_eq_zero q]
      mul_le' := fun x y =>
        sup_le ((map_mul_le_add p x y).trans <| add_le_add le_sup_left le_sup_left)
          ((map_

中文:
实例 :
  签名: 最大值 (群半范数 E)
  定义体: ⟨fun p q =>
    { toFun := p ⊔ q
      map_one' := by
        rw [Pi.sup_apply]; rw [← map_one_eq_zero p]; rw [sup_eq_left]; rw [map_one_eq_zero p]; rw [map_one_eq_zero q]
      mul_le' := fun x y =>
        sup_le ((map_mul_le_add p x y).trans <| add_le_add le_sup_left le_sup_left)
          ((map_

Depends on / 依赖: Pi.sup_apply, add_le_add, le_sup_left, le_sup_right, map_inv_eq_map, map_mul_le_add, map_one, map_one_eq_zero, mul_le, sup_apply, sup_eq_left, sup_le
-/
instance : Max (GroupSeminorm E) :=
  ⟨fun p q =>
    { toFun := p ⊔ q
      map_one' := by
        rw [Pi.sup_apply]; rw [← map_one_eq_zero p]; rw [sup_eq_left]; rw [map_one_eq_zero p]; rw [map_one_eq_zero q]
      mul_le' := fun x y =>
        sup_le ((map_mul_le_add p x y).trans <| add_le_add le_sup_left le_sup_left)
          ((map_mul_le_add q x y).trans <| add_le_add le_sup_right le_sup_right)
      inv' := fun x => by rw [Pi.sup_apply, Pi.sup_apply, map_inv_eq_map p, map_inv_eq_map q] }⟩

@[to_additive (attr := simp, norm_cast)]
/--
theorem `coe_sup` / 定理 `coe_sup`

English:
theorem coe_sup
  statement: ⇑(p ⊔ q) = ⇑p ⊔ ⇑q
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 coe_sup
  结论: ⇑(p ⊔ q) = ⇑p ⊔ ⇑q
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem coe_sup : ⇑(p ⊔ q) = ⇑p ⊔ ⇑q :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `sup_apply` / 定理 `sup_apply`

English:
theorem sup_apply
  given: (x : E)
  statement: (p ⊔ q) x = p x ⊔ q x
  proof: rfl

@[to_additive]

中文:
定理 sup_apply
  条件: (x : E)
  结论: (p ⊔ q) x = p x ⊔ q x
  证明: rfl

@[to_additive]
-/
theorem sup_apply (x : E) : (p ⊔ q) x = p x ⊔ q x :=
  rfl

@[to_additive]
/--
Instance `semilatticeSup` / 实例 `semilatticeSup`

English:
instance semilatticeSup
  signature: : SemilatticeSup (GroupSeminorm E)
  body: DFunLike.coe_injective.semilatticeSup _ .rfl .rfl coe_sup

中文:
实例 semilatticeSup
  签名: : SemilatticeSup (群半范数 E)
  定义体: DFunLike.coe_injective.semilatticeSup _ .rfl .rfl coe_sup

Depends on / 依赖: DFunLike, DFunLike.coe_injective.semilatticeSup, coe_injective, coe_sup, semilatticeSup
-/
instance semilatticeSup : SemilatticeSup (GroupSeminorm E) :=
  DFunLike.coe_injective.semilatticeSup _ .rfl .rfl coe_sup

/-- Composition of a group seminorm with a monoid homomorphism as a group seminorm. -/
@[to_additive /-- Composition of an additive group seminorm with an additive monoid homomorphism as
an additive group seminorm. -/]
/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: (p : GroupSeminorm E) (f : F ->* E)
  body: p (f x)
  map_one' := by simp_rw [f.map_one, map_one_eq_zero p]
mul_le' _ _ := (congr_arg p <| f.map_mul _ _).trans_le map_mul_le_add p _ _
  inv' x := by simp_rw [map_inv, map_inv_eq_map p]

@[to_additive (attr := simp)]

中文:
定义 comp
  签名: (p : 群半范数 E) (f : F ->* E)
  定义体: p (f x)
  map_one' := by simp_rw [f.map_one, map_one_eq_zero p]
mul_le' _ _ := (congr_arg p <| f.map_mul _ _).trans_le map_mul_le_add p _ _
  inv' x := by simp_rw [map_inv, map_inv_eq_map p]

@[to_additive (attr := simp)]
-/
def comp (p : GroupSeminorm E) (f : F ->* E) : GroupSeminorm F where
  toFun x := p (f x)
  map_one' := by simp_rw [f.map_one, map_one_eq_zero p]
mul_le' _ _ := (congr_arg p <| f.map_mul _ _).trans_le map_mul_le_add p _ _
  inv' x := by simp_rw [map_inv, map_inv_eq_map p]

@[to_additive (attr := simp)]
/--
theorem `coe_comp` / 定理 `coe_comp`

English:
theorem coe_comp
  statement: ⇑(p.comp f) = p ∘ f
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 coe_comp
  结论: ⇑(p.comp f) = p ∘ f
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem coe_comp : ⇑(p.comp f) = p ∘ f :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `comp_apply` / 定理 `comp_apply`

English:
theorem comp_apply
  given: (x : F)
  statement: (p.comp f) x = p (f x)
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 comp_apply
  条件: (x : F)
  结论: (p.comp f) x = p (f x)
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem comp_apply (x : F) : (p.comp f) x = p (f x) :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `comp_id` / 定理 `comp_id`

English:
theorem comp_id
  statement: p.comp (MonoidHom.id _) = p
  proof: ext fun _ => rfl

@[to_additive (attr := simp)]

中文:
定理 comp_id
  结论: p.comp (幺半群态射.id _) = p
  证明: ext fun _ => rfl

@[to_additive (attr := simp)]
-/
theorem comp_id : p.comp (MonoidHom.id _) = p :=
  ext fun _ => rfl

@[to_additive (attr := simp)]
/--
theorem `comp_zero` / 定理 `comp_zero`

English:
theorem comp_zero
  statement: p.comp (1 : F ->* E) = 0
  proof: ext fun _ => map_one_eq_zero p

@[to_additive (attr := simp)]

中文:
定理 comp_zero
  结论: p.comp (1 : F ->* E) = 0
  证明: ext fun _ => map_one_eq_zero p

@[to_additive (attr := simp)]

Depends on / 依赖: map_one_eq_zero
-/
theorem comp_zero : p.comp (1 : F ->* E) = 0 :=
  ext fun _ => map_one_eq_zero p

@[to_additive (attr := simp)]
/--
theorem `zero_comp` / 定理 `zero_comp`

English:
theorem zero_comp
  statement: (0 : GroupSeminorm E).comp f = 0
  proof: ext fun _ => rfl

@[to_additive]

中文:
定理 zero_comp
  结论: (0 : 群半范数 E).comp f = 0
  证明: ext fun _ => rfl

@[to_additive]
-/
theorem zero_comp : (0 : GroupSeminorm E).comp f = 0 :=
  ext fun _ => rfl

@[to_additive]
/--
theorem `comp_assoc` / 定理 `comp_assoc`

English:
theorem comp_assoc
  given: (g : F ->* E) (f : G ->* F)
  statement: p.comp (g.comp f) = (p.comp g).comp f
  proof: ext fun _ => rfl

@[to_additive]

中文:
定理 comp_assoc
  条件: (g : F ->* E) (f : G ->* F)
  结论: p.comp (g.comp f) = (p.comp g).comp f
  证明: ext fun _ => rfl

@[to_additive]
-/
theorem comp_assoc (g : F ->* E) (f : G ->* F) : p.comp (g.comp f) = (p.comp g).comp f :=
  ext fun _ => rfl

@[to_additive]
/--
theorem `add_comp` / 定理 `add_comp`

English:
theorem add_comp
  given: (f : F ->* E)
  statement: (p + q).comp f = p.comp f + q.comp f
  proof: ext fun _ => rfl

中文:
定理 add_comp
  条件: (f : F ->* E)
  结论: (p + q).comp f = p.comp f + q.comp f
  证明: ext fun _ => rfl
-/
theorem add_comp (f : F ->* E) : (p + q).comp f = p.comp f + q.comp f :=
  ext fun _ => rfl

variable {p q}

@[to_additive]
/--
theorem `comp_mono` / 定理 `comp_mono`

English:
theorem comp_mono
  given: (hp : p <= q)
  statement: p.comp f <= q.comp f
  proof: fun _ => hp _

中文:
定理 comp_mono
  条件: (hp : p <= q)
  结论: p.comp f <= q.comp f
  证明: fun _ => hp _
-/
theorem comp_mono (hp : p <= q) : p.comp f <= q.comp f := fun _ => hp _

end Group

section CommGroup

variable [CommGroup E] [CommGroup F] (p q : GroupSeminorm E) (x : E)

@[to_additive]
/--
theorem `comp_mul_le` / 定理 `comp_mul_le`

English:
theorem comp_mul_le
  given: (f g : F ->* E)
  statement: p.comp (f * g) <= p.comp f + p.comp g
  proof: fun _ =>
  map_mul_le_add p _ _

@[to_additive]

中文:
定理 comp_mul_le
  条件: (f g : F ->* E)
  结论: p.comp (f * g) <= p.comp f + p.comp g
  证明: fun _ =>
  map_mul_le_add p _ _

@[to_additive]
-/
theorem comp_mul_le (f g : F ->* E) : p.comp (f * g) <= p.comp f + p.comp g := fun _ =>
  map_mul_le_add p _ _

@[to_additive]
/--
theorem `mul_bddBelow_range_add` / 定理 `mul_bddBelow_range_add`

English:
theorem mul_bddBelow_range_add
  given: {p q : GroupSeminorm E} {x : E}
  proof: ⟨0, by
    rintro _ ⟨x, rfl⟩
    dsimp
    positivity⟩

@[to_additive]

中文:
定理 mul_bddBelow_range_add
  条件: {p q : 群半范数 E} {x : E}
  证明: ⟨0, by
    rintro _ ⟨x, rfl⟩
    dsimp
    positivity⟩

@[to_additive]
-/
theorem mul_bddBelow_range_add {p q : GroupSeminorm E} {x : E} :
    BddBelow (range fun y => p y + q (x / y)) :=
  ⟨0, by
    rintro _ ⟨x, rfl⟩
    dsimp
    positivity⟩

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Min (GroupSeminorm E)
  body: ⟨fun p q =>
    { toFun := fun x => ⨅ y, p y + q (x / y)
      map_one' :=
        ciInf_eq_of_forall_ge_of_forall_gt_exists_lt
          (fun _ => by positivity) fun r hr =>
          ⟨1, by rwa [div_one, map_one_eq_zero p, map_one_eq_zero q, add_zero]⟩
      mul_le' := fun x y =>
        le_ciInf_

中文:
实例 :
  签名: 最小值 (群半范数 E)
  定义体: ⟨fun p q =>
    { toFun := fun x => ⨅ y, p y + q (x / y)
      map_one' :=
        ciInf_eq_of_forall_ge_of_forall_gt_exists_lt
          (fun _ => by positivity) fun r hr =>
          ⟨1, by rwa [div_one, map_one_eq_zero p, map_one_eq_zero q, add_zero]⟩
      mul_le' := fun x y =>
        le_ciInf_

Depends on / 依赖: add_add_add_comm, add_le_add, add_zero, ciInf_eq_of_forall_ge_of_forall_gt_exists_lt, ciInf_le_of_le, div_one, iInf_comp, inv_surjective, inv_surjective.iInf_comp, le_ciInf_add_ciInf, map_mul_le_add, map_one, map_one_eq_zero, mul_bddBelow_range_add, mul_div_mul_comm, mul_le, symm.trans
-/
noncomputable instance : Min (GroupSeminorm E) :=
  ⟨fun p q =>
    { toFun := fun x => ⨅ y, p y + q (x / y)
      map_one' :=
        ciInf_eq_of_forall_ge_of_forall_gt_exists_lt
          (fun _ => by positivity) fun r hr =>
          ⟨1, by rwa [div_one, map_one_eq_zero p, map_one_eq_zero q, add_zero]⟩
      mul_le' := fun x y =>
        le_ciInf_add_ciInf fun u v => by
          refine ciInf_le_of_le mul_bddBelow_range_add (u * v) ?_
          rw [mul_div_mul_comm]; rw [add_add_add_comm]
          exact add_le_add (map_mul_le_add p _ _) (map_mul_le_add q _ _)
      inv' := fun x =>
(inv_surjective.iInf_comp _).symm.trans by
          simp_rw [map_inv_eq_map p, ← inv_div', map_inv_eq_map q] }⟩

@[to_additive (attr := simp)]
/--
theorem `inf_apply` / 定理 `inf_apply`

English:
theorem inf_apply
  statement: (p ⊓ q) x = ⨅ y, p y + q (x / y)
  proof: rfl

@[to_additive]

中文:
定理 inf_apply
  结论: (p ⊓ q) x = ⨅ y, p y + q (x / y)
  证明: rfl

@[to_additive]
-/
theorem inf_apply : (p ⊓ q) x = ⨅ y, p y + q (x / y) :=
  rfl

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Lattice (GroupSeminorm E)
  body: { GroupSeminorm.semilatticeSup with
    inf := (· ⊓ ·)
    inf_le_left := fun p q x =>
ciInf_le_of_le mul_bddBelow_range_add x by rw [div_self', map_one_eq_zero q, add_zero]
    inf_le_right := fun p q x =>
ciInf_le_of_le mul_bddBelow_range_add (1 : E) by
        simpa only [div_one x, map_one_eq_ze

中文:
实例 :
  签名: 格 (群半范数 E)
  定义体: { GroupSeminorm.semilatticeSup with
    inf := (· ⊓ ·)
    inf_le_left := fun p q x =>
ciInf_le_of_le mul_bddBelow_range_add x by rw [div_self', map_one_eq_zero q, add_zero]
    inf_le_right := fun p q x =>
ciInf_le_of_le mul_bddBelow_range_add (1 : E) by
        simpa only [div_one x, map_one_eq_ze

Depends on / 依赖: GroupSeminorm, GroupSeminorm.semilatticeSup, add_le_add, add_zero, ciInf_le_of_le, div_one, div_self, inf_le_left, inf_le_right, le_ciInf, le_inf, le_map_add_map_div, le_rfl, map_one_eq_zero, mul_bddBelow_range_add, semilatticeSup, zero_add
-/
noncomputable instance : Lattice (GroupSeminorm E) :=
  { GroupSeminorm.semilatticeSup with
    inf := (· ⊓ ·)
    inf_le_left := fun p q x =>
ciInf_le_of_le mul_bddBelow_range_add x by rw [div_self', map_one_eq_zero q, add_zero]
    inf_le_right := fun p q x =>
ciInf_le_of_le mul_bddBelow_range_add (1 : E) by
        simpa only [div_one x, map_one_eq_zero p, zero_add (q x)] using le_rfl
    le_inf := fun a _ _ hb hc _ =>
le_ciInf fun _ => (le_map_add_map_div a _ _).trans add_le_add (hb _) (hc _) }

end CommGroup

end GroupSeminorm

/- TODO: All the following ought to be automated using `to_additive`. The problem is that it doesn't
see that `SMul R ℝ` should be fixed because `ℝ` is fixed. -/
namespace AddGroupSeminorm

variable [AddGroup E] [SMul R Real] [SMul R Real>=0] [IsScalarTower R Real>=0 Real]

/--
Instance `toOne` / 实例 `toOne`

English:
instance toOne
  signature: [DecidableEq E]
  body: ⟨{ toFun := fun x => if x = 0 then 0 else 1
      map_zero' := if_pos rfl
      add_le' := fun x y => by
        by_cases hx : x = 0
        · rw [if_pos hx, hx, zero_add, zero_add]
        · rw [if_neg hx]
          refine le_add_of_le_of_nonneg ?_ ?_ <;> split_ifs <;> norm_num
      neg' := fun x 

中文:
实例 toOne
  签名: [DecidableEq E]
  定义体: ⟨{ toFun := fun x => if x = 0 then 0 else 1
      map_zero' := if_pos rfl
      add_le' := fun x y => by
        by_cases hx : x = 0
        · rw [if_pos hx, hx, zero_add, zero_add]
        · rw [if_neg hx]
          refine le_add_of_le_of_nonneg ?_ ?_ <;> split_ifs <;> norm_num
      neg' := fun x 

Depends on / 依赖: add_le, if_neg, if_pos, le_add_of_le_of_nonneg, map_zero, neg_eq_zero, simp_rw, split_ifs, zero_add
-/
instance toOne [DecidableEq E] : One (AddGroupSeminorm E) :=
  ⟨{ toFun := fun x => if x = 0 then 0 else 1
      map_zero' := if_pos rfl
      add_le' := fun x y => by
        by_cases hx : x = 0
        · rw [if_pos hx, hx, zero_add, zero_add]
        · rw [if_neg hx]
          refine le_add_of_le_of_nonneg ?_ ?_ <;> split_ifs <;> norm_num
      neg' := fun x => by simp_rw [neg_eq_zero] }⟩

@[simp]
/--
theorem `apply_one` / 定理 `apply_one`

English:
theorem apply_one
  given: [DecidableEq E] (x : E)
  statement: (1 : AddGroupSeminorm E) x = if x = 0 then 0 else 1
  proof: rfl

中文:
定理 apply_one
  条件: [DecidableEq E] (x : E)
  结论: (1 : 加法群半范数 E) x = if x = 0 then 0 else 1
  证明: rfl
-/
theorem apply_one [DecidableEq E] (x : E) : (1 : AddGroupSeminorm E) x = if x = 0 then 0 else 1 :=
  rfl

/--
Instance `toSMul` / 实例 `toSMul`

English:
instance toSMul
  signature: : SMul R (AddGroupSeminorm E)
  body: ⟨fun r p =>
    { toFun := fun x => r • p x
      map_zero' := by
        simp only [← smul_one_smul Real>=0 r (_ : Real), NNReal.smul_def, smul_eq_mul, map_zero, mul_zero]
      add_le' := fun _ _ => by
        simp only [← smul_one_smul Real>=0 r (_ : Real), NNReal.smul_def, smul_eq_mul, ← mul_add

中文:
实例 toSMul
  签名: : 标量乘法 R (加法群半范数 E)
  定义体: ⟨fun r p =>
    { toFun := fun x => r • p x
      map_zero' := by
        simp only [← smul_one_smul Real>=0 r (_ : Real), NNReal.smul_def, smul_eq_mul, map_zero, mul_zero]
      add_le' := fun _ _ => by
        simp only [← smul_one_smul Real>=0 r (_ : Real), NNReal.smul_def, smul_eq_mul, ← mul_add

Depends on / 依赖: NNReal, NNReal.smul_def, add_le, map_add_le_add, map_neg_eq_map, map_zero, mul_add, mul_zero, simp_rw, smul_def, smul_eq_mul, smul_one_smul
-/
instance toSMul : SMul R (AddGroupSeminorm E) :=
  ⟨fun r p =>
    { toFun := fun x => r • p x
      map_zero' := by
        simp only [← smul_one_smul Real>=0 r (_ : Real), NNReal.smul_def, smul_eq_mul, map_zero, mul_zero]
      add_le' := fun _ _ => by
        simp only [← smul_one_smul Real>=0 r (_ : Real), NNReal.smul_def, smul_eq_mul, ← mul_add]
        gcongr
        apply map_add_le_add
      neg' := fun x => by simp_rw [map_neg_eq_map] }⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsSMulApply R (AddGroupSeminorm E) E Real
  body: rfl

@[deprecated (since := "2026-07-10")] alias coe_smul := FunLike.coe_smul

@[deprecated (since := "2026-07-10")] protected alias smul_apply := smul_apply

中文:
实例 :
  签名: 是SMulApply R (加法群半范数 E) E 实数
  定义体: rfl

@[deprecated (since := "2026-07-10")] alias coe_smul := FunLike.coe_smul

@[deprecated (since := "2026-07-10")] protected alias smul_apply := smul_apply
-/
instance : IsSMulApply R (AddGroupSeminorm E) E Real where
  smul_apply _ _ _ := rfl

@[deprecated (since := "2026-07-10")] alias coe_smul := FunLike.coe_smul

@[deprecated (since := "2026-07-10")] protected alias smul_apply := smul_apply

/--
Instance `isScalarTower` / 实例 `isScalarTower`

English:
instance isScalarTower
  signature: [SMul R' Real] [SMul R' Real>=0] [IsScalarTower R' Real>=0 Real] [SMul R R']
  body: FunLike.isScalarTower

中文:
实例 isScalarTower
  签名: [标量乘法 R' 实数] [标量乘法 R' 实数>=0] [标量塔 R' 实数>=0 实数] [标量乘法 R R']
  定义体: FunLike.isScalarTower

Depends on / 依赖: FunLike, FunLike.isScalarTower, isScalarTower
-/
instance isScalarTower [SMul R' Real] [SMul R' Real>=0] [IsScalarTower R' Real>=0 Real] [SMul R R']
    [IsScalarTower R R' Real] : IsScalarTower R R' (AddGroupSeminorm E) :=
  FunLike.isScalarTower

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddCommMonoid (AddGroupSeminorm E)
  body: fast_instance% FunLike.addCommMonoid

中文:
实例 :
  签名: 加法交换幺半群 (加法群半范数 E)
  定义体: fast_instance% FunLike.addCommMonoid

Depends on / 依赖: FunLike, FunLike.addCommMonoid, addCommMonoid, fast_instance
-/
instance : AddCommMonoid (AddGroupSeminorm E) := fast_instance% FunLike.addCommMonoid

/--
theorem `smul_sup` / 定理 `smul_sup`

English:
theorem smul_sup
  given: (r : R) (p q : AddGroupSeminorm E)
  statement: r • (p ⊔ q) = r • p ⊔ r • q
  proof: have Real.smul_max : forall x y : Real, r • max x y = max (r • x) (r • y) := fun x y => by
    simpa only [← smul_eq_mul, ← NNReal.smul_def, smul_one_smul Real>=0 r (_ : Real)] using
      mul_max_of_nonneg x y (r • (1 : Real>=0) : Real>=0).coe_nonneg
  ext fun _ => Real.smul_max _ _

中文:
定理 smul_sup
  条件: (r : R) (p q : 加法群半范数 E)
  结论: r • (p ⊔ q) = r • p ⊔ r • q
  证明: have Real.smul_max : forall x y : Real, r • max x y = max (r • x) (r • y) := fun x y => by
    simpa only [← smul_eq_mul, ← NNReal.smul_def, smul_one_smul Real>=0 r (_ : Real)] using
      mul_max_of_nonneg x y (r • (1 : Real>=0) : Real>=0).coe_nonneg
  ext fun _ => Real.smul_max _ _

Depends on / 依赖: NNReal, NNReal.smul_def, Real.smul_max, coe_nonneg, mul_max_of_nonneg, smul_def, smul_eq_mul, smul_max, smul_one_smul
-/
theorem smul_sup (r : R) (p q : AddGroupSeminorm E) : r • (p ⊔ q) = r • p ⊔ r • q :=
  have Real.smul_max : forall x y : Real, r • max x y = max (r • x) (r • y) := fun x y => by
    simpa only [← smul_eq_mul, ← NNReal.smul_def, smul_one_smul Real>=0 r (_ : Real)] using
      mul_max_of_nonneg x y (r • (1 : Real>=0) : Real>=0).coe_nonneg
  ext fun _ => Real.smul_max _ _

end AddGroupSeminorm

namespace NonarchAddGroupSeminorm

section AddGroup

variable [AddGroup E] {p q : NonarchAddGroupSeminorm E}

/--
Instance `funLike` / 实例 `funLike`

English:
instance funLike
  signature: : FunLike (NonarchAddGroupSeminorm E) E Real where
  body: f.toFun
  coe_injective f g h := by obtain ⟨⟨_, _⟩, _, _⟩ := f; cases g; congr

中文:
实例 funLike
  签名: : 函数状 (NonarchAdd群半范数 E) E 实数 where
  定义体: f.toFun
  coe_injective f g h := by obtain ⟨⟨_, _⟩, _, _⟩ := f; cases g; congr

Depends on / 依赖: f.toFun
-/
instance funLike : FunLike (NonarchAddGroupSeminorm E) E Real where
  coe f := f.toFun
  coe_injective f g h := by obtain ⟨⟨_, _⟩, _, _⟩ := f; cases g; congr

/--
Instance `nonarchAddGroupSeminormClass` / 实例 `nonarchAddGroupSeminormClass`

English:
instance nonarchAddGroupSeminormClass
  signature: :
  body: f.add_le_max'
  map_zero f := f.map_zero'
  map_neg_eq_map' f := f.neg'

@[simp]

中文:
实例 nonarchAddGroupSeminormClass
  签名: :
  定义体: f.add_le_max'
  map_zero f := f.map_zero'
  map_neg_eq_map' f := f.neg'

@[simp]

Depends on / 依赖: add_le_max, f.add_le_max
-/
instance nonarchAddGroupSeminormClass :
    NonarchAddGroupSeminormClass (NonarchAddGroupSeminorm E) E where
  map_add_le_max f := f.add_le_max'
  map_zero f := f.map_zero'
  map_neg_eq_map' f := f.neg'

@[simp]
/--
theorem `toZeroHom_eq_coe` / 定理 `toZeroHom_eq_coe`

English:
theorem toZeroHom_eq_coe
  statement: ⇑p.toZeroHom = p
  proof: by
  rfl

@[ext]

中文:
定理 toZeroHom_eq_coe
  结论: ⇑p.toZeroHom = p
  证明: by
  rfl

@[ext]
-/
theorem toZeroHom_eq_coe : ⇑p.toZeroHom = p := by
  rfl

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  statement: (forall x, p x = q x) -> p = q
  proof: DFunLike.ext p q

中文:
定理 ext
  结论: (对任意 x, p x = q x) -> p = q
  证明: DFunLike.ext p q

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem ext : (forall x, p x = q x) -> p = q :=
  DFunLike.ext p q

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (NonarchAddGroupSeminorm E)
  body: PartialOrder.lift _ DFunLike.coe_injective

中文:
实例 :
  签名: 偏序 (NonarchAdd群半范数 E)
  定义体: PartialOrder.lift _ DFunLike.coe_injective

Depends on / 依赖: DFunLike, DFunLike.coe_injective, PartialOrder, PartialOrder.lift, coe_injective
-/
noncomputable instance : PartialOrder (NonarchAddGroupSeminorm E) :=
  PartialOrder.lift _ DFunLike.coe_injective

/--
theorem `le_def` / 定理 `le_def`

English:
theorem le_def
  statement: p <= q ↔ (p : E -> Real) <= q
  proof: Iff.rfl

中文:
定理 le_def
  结论: p <= q ↔ (p : E -> 实数) <= q
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem le_def : p <= q ↔ (p : E -> Real) <= q :=
  Iff.rfl

/--
theorem `lt_def` / 定理 `lt_def`

English:
theorem lt_def
  statement: p < q ↔ (p : E -> Real) < q
  proof: Iff.rfl

@[simp, norm_cast]

中文:
定理 lt_def
  结论: p < q ↔ (p : E -> 实数) < q
  证明: Iff.rfl

@[simp, norm_cast]

Depends on / 依赖: Iff.rfl
-/
theorem lt_def : p < q ↔ (p : E -> Real) < q :=
  Iff.rfl

@[simp, norm_cast]
/--
theorem `coe_le_coe` / 定理 `coe_le_coe`

English:
theorem coe_le_coe
  statement: (p : E -> Real) <= q ↔ p <= q
  proof: Iff.rfl

@[simp, norm_cast]

中文:
定理 coe_le_coe
  结论: (p : E -> 实数) <= q ↔ p <= q
  证明: Iff.rfl

@[simp, norm_cast]

Depends on / 依赖: Iff.rfl
-/
theorem coe_le_coe : (p : E -> Real) <= q ↔ p <= q :=
  Iff.rfl

@[simp, norm_cast]
/--
theorem `coe_lt_coe` / 定理 `coe_lt_coe`

English:
theorem coe_lt_coe
  statement: (p : E -> Real) < q ↔ p < q
  proof: Iff.rfl

中文:
定理 coe_lt_coe
  结论: (p : E -> 实数) < q ↔ p < q
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem coe_lt_coe : (p : E -> Real) < q ↔ p < q :=
  Iff.rfl

variable (p q)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Zero (NonarchAddGroupSeminorm E)
  body: ⟨{ toFun := 0
      map_zero' := Pi.zero_apply _
      add_le_max' := fun r s => by simp only [Pi.zero_apply]; rw [max_eq_right]; rfl
      neg' := fun _ => rfl }⟩

中文:
实例 :
  签名: 零 (NonarchAdd群半范数 E)
  定义体: ⟨{ toFun := 0
      map_zero' := Pi.zero_apply _
      add_le_max' := fun r s => by simp only [Pi.zero_apply]; rw [max_eq_right]; rfl
      neg' := fun _ => rfl }⟩

Depends on / 依赖: Pi.zero_apply, add_le_max, map_zero, max_eq_right, zero_apply
-/
instance : Zero (NonarchAddGroupSeminorm E) :=
  ⟨{ toFun := 0
      map_zero' := Pi.zero_apply _
      add_le_max' := fun r s => by simp only [Pi.zero_apply]; rw [max_eq_right]; rfl
      neg' := fun _ => rfl }⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsZeroApply (NonarchAddGroupSeminorm E) E Real
  body: rfl

@[deprecated (since := "2026-07-10")] alias coe_zero := FunLike.coe_zero

@[deprecated (since := "2026-07-10")] protected alias zero_apply := zero_apply

中文:
实例 :
  签名: 是ZeroApply (NonarchAdd群半范数 E) E 实数
  定义体: rfl

@[deprecated (since := "2026-07-10")] alias coe_zero := FunLike.coe_zero

@[deprecated (since := "2026-07-10")] protected alias zero_apply := zero_apply
-/
instance : IsZeroApply (NonarchAddGroupSeminorm E) E Real where
  zero_apply _ := rfl

@[deprecated (since := "2026-07-10")] alias coe_zero := FunLike.coe_zero

@[deprecated (since := "2026-07-10")] protected alias zero_apply := zero_apply

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (NonarchAddGroupSeminorm E)
  body: ⟨0⟩

中文:
实例 :
  签名: 可居 (NonarchAdd群半范数 E)
  定义体: ⟨0⟩
-/
instance : Inhabited (NonarchAddGroupSeminorm E) :=
  ⟨0⟩

open scoped Classical in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SupSet (NonarchAddGroupSeminorm E)
  body: if h : BddAbove s then
      { toFun x := ⨆ p : s, p.1 x
        map_zero' := by simp
        add_le_max' x y := by
          obtain (rfl | hs) := eq_empty_or_nonempty s
          · simp
          · have : Nonempty s := hs.to_subtype
            refine ciSup_le fun p => (map_add_le_max p.1 x y).tran

中文:
实例 :
  签名: 上确界集 (NonarchAdd群半范数 E)
  定义体: if h : BddAbove s then
      { toFun x := ⨆ p : s, p.1 x
        map_zero' := by simp
        add_le_max' x y := by
          obtain (rfl | hs) := eq_empty_or_nonempty s
          · simp
          · have : Nonempty s := hs.to_subtype
            refine ciSup_le fun p => (map_add_le_max p.1 x y).tran

Depends on / 依赖: BddAbove, DFunLike, DFunLike.coe, Monotone, Monotone.map_bddAbove, Nonempty, Set.range_comp, Subtype, Subtype.val, add_le_max, all_goals, ciSup_le, eq_empty_or_nonempty, hs.to_subtype, le_ciSup, map_add_le_max, map_bddAbove, map_zero, range_comp, to_subtype
-/
noncomputable instance : SupSet (NonarchAddGroupSeminorm E) where
  sSup s :=
    if h : BddAbove s then
      { toFun x := ⨆ p : s, p.1 x
        map_zero' := by simp
        add_le_max' x y := by
          obtain (rfl | hs) := eq_empty_or_nonempty s
          · simp
          · have : Nonempty s := hs.to_subtype
            refine ciSup_le fun p => (map_add_le_max p.1 x y).trans ?_
            gcongr
            all_goals
              apply le_ciSup (f := (DFunLike.coe · _) ∘ Subtype.val) ?_ p
              simpa [Set.range_comp] using Monotone.map_bddAbove (fun _ _ h' => by exact h' _) h
        neg' := by simp }
    else 0

/--
lemma `sSup_of_not_bddAbove` / 引理 `sSup_of_not_bddAbove`

English:
lemma sSup_of_not_bddAbove
  given: {s : Set (NonarchAddGroupSeminorm E)} (hs : ¬BddAbove s)
  proof: by
  simp [SupSet.sSup, hs]

中文:
引理 sSup_of_not_bddAbove
  条件: {s : 集合 (NonarchAdd群半范数 E)} (hs : ¬BddAbove s)
  证明: by
  simp [SupSet.sSup, hs]

Depends on / 依赖: SupSet, SupSet.sSup
-/
lemma sSup_of_not_bddAbove {s : Set (NonarchAddGroupSeminorm E)} (hs : ¬BddAbove s) :
    sSup s = 0 := by
  simp [SupSet.sSup, hs]

/--
lemma `coe_sSup_apply` / 引理 `coe_sSup_apply`

English:
lemma coe_sSup_apply
  given: {s : Set (NonarchAddGroupSeminorm E)} (hs : BddAbove s) {x : E}
  proof: by
  simp [SupSet.sSup, hs]
  rfl

中文:
引理 coe_sSup_apply
  条件: {s : 集合 (NonarchAdd群半范数 E)} (hs : BddAbove s) {x : E}
  证明: by
  simp [SupSet.sSup, hs]
  rfl

Depends on / 依赖: SupSet, SupSet.sSup
-/
lemma coe_sSup_apply {s : Set (NonarchAddGroupSeminorm E)} (hs : BddAbove s) {x : E} :
    ⇑(sSup s) x = ⨆ p : s, (p : NonarchAddGroupSeminorm E) x := by
  simp [SupSet.sSup, hs]
  rfl

/--
lemma `coe_sSup_apply'` / 引理 `coe_sSup_apply'`

English:
lemma coe_sSup_apply'
  given: {s : Set (NonarchAddGroupSeminorm E)} (hs : BddAbove s) {x : E}
  proof: by
  rw [coe_sSup_apply hs]; rw [← sSup_range]
  congr
  ext
  simp

中文:
引理 coe_sSup_apply'
  条件: {s : 集合 (NonarchAdd群半范数 E)} (hs : BddAbove s) {x : E}
  证明: by
  rw [coe_sSup_apply hs]; rw [← sSup_range]
  congr
  ext
  simp

Depends on / 依赖: coe_sSup_apply, sSup_range
-/
lemma coe_sSup_apply' {s : Set (NonarchAddGroupSeminorm E)} (hs : BddAbove s) {x : E} :
    ⇑(sSup s) x = sSup ((· x) '' s) := by
  rw [coe_sSup_apply hs]; rw [← sSup_range]
  congr
  ext
  simp

/--
lemma `coe_iSup_apply` / 引理 `coe_iSup_apply`

English:
lemma coe_iSup_apply
  statement: {ι : Type*} (f : ι -> NonarchAddGroupSeminorm E) (h : BddAbove (range f))
  proof: by
  rw [← sSup_range]; rw [coe_sSup_apply h]
.symm exact (Set.rangeFactorization_surjective.iSup_congr _ (by simp))

中文:
引理 coe_iSup_apply
  结论: {ι : 类型} (f : ι -> NonarchAdd群半范数 E) (h : BddAbove (range f))
  证明: by
  rw [← sSup_range]; rw [coe_sSup_apply h]
.symm exact (Set.rangeFactorization_surjective.iSup_congr _ (by simp))

Depends on / 依赖: Set.rangeFactorization_surjective.iSup_congr, coe_sSup_apply, iSup_congr, rangeFactorization_surjective, sSup_range
-/
lemma coe_iSup_apply {ι : Type*} (f : ι -> NonarchAddGroupSeminorm E) (h : BddAbove (range f))
    {x : E} : ⇑(⨆ i, f i) x = ⨆ i, (f i : NonarchAddGroupSeminorm E) x := by
  rw [← sSup_range]; rw [coe_sSup_apply h]
.symm exact (Set.rangeFactorization_surjective.iSup_congr _ (by simp))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Max (NonarchAddGroupSeminorm E)
  body: ⟨fun p q =>
    { toFun := p ⊔ q
      map_zero' := by rw [Pi.sup_apply, ← map_zero p, sup_eq_left, map_zero p, map_zero q]
      add_le_max' := fun x y =>
        sup_le ((map_add_le_max p x y).trans <| max_le_max le_sup_left le_sup_left)
          ((map_add_le_max q x y).trans <| max_le_max le_sup

中文:
实例 :
  签名: 最大值 (NonarchAdd群半范数 E)
  定义体: ⟨fun p q =>
    { toFun := p ⊔ q
      map_zero' := by rw [Pi.sup_apply, ← map_zero p, sup_eq_left, map_zero p, map_zero q]
      add_le_max' := fun x y =>
        sup_le ((map_add_le_max p x y).trans <| max_le_max le_sup_left le_sup_left)
          ((map_add_le_max q x y).trans <| max_le_max le_sup

Depends on / 依赖: Pi.sup_apply, add_le_max, le_sup_left, le_sup_right, map_add_le_max, map_neg_eq_map, map_zero, max_le_max, simp_rw, sup_apply, sup_eq_left, sup_le
-/
instance : Max (NonarchAddGroupSeminorm E) :=
  ⟨fun p q =>
    { toFun := p ⊔ q
      map_zero' := by rw [Pi.sup_apply, ← map_zero p, sup_eq_left, map_zero p, map_zero q]
      add_le_max' := fun x y =>
        sup_le ((map_add_le_max p x y).trans <| max_le_max le_sup_left le_sup_left)
          ((map_add_le_max q x y).trans <| max_le_max le_sup_right le_sup_right)
      neg' := fun x => by simp_rw [Pi.sup_apply, map_neg_eq_map p, map_neg_eq_map q]}⟩

@[simp, norm_cast]
/--
theorem `coe_sup` / 定理 `coe_sup`

English:
theorem coe_sup
  statement: ⇑(p ⊔ q) = ⇑p ⊔ ⇑q
  proof: rfl

@[simp]

中文:
定理 coe_sup
  结论: ⇑(p ⊔ q) = ⇑p ⊔ ⇑q
  证明: rfl

@[simp]
-/
theorem coe_sup : ⇑(p ⊔ q) = ⇑p ⊔ ⇑q :=
  rfl

@[simp]
/--
theorem `sup_apply` / 定理 `sup_apply`

English:
theorem sup_apply
  given: (x : E)
  statement: (p ⊔ q) x = p x ⊔ q x
  proof: rfl

中文:
定理 sup_apply
  条件: (x : E)
  结论: (p ⊔ q) x = p x ⊔ q x
  证明: rfl
-/
theorem sup_apply (x : E) : (p ⊔ q) x = p x ⊔ q x :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SemilatticeSup (NonarchAddGroupSeminorm E)
  body: DFunLike.coe_injective.semilatticeSup _ .rfl .rfl coe_sup

中文:
实例 :
  签名: SemilatticeSup (NonarchAdd群半范数 E)
  定义体: DFunLike.coe_injective.semilatticeSup _ .rfl .rfl coe_sup

Depends on / 依赖: DFunLike, DFunLike.coe_injective.semilatticeSup, coe_injective, coe_sup, semilatticeSup
-/
noncomputable instance : SemilatticeSup (NonarchAddGroupSeminorm E) :=
  DFunLike.coe_injective.semilatticeSup _ .rfl .rfl coe_sup

end AddGroup

section AddCommGroup

variable [AddCommGroup E]

/--
theorem `add_bddBelow_range_add` / 定理 `add_bddBelow_range_add`

English:
theorem add_bddBelow_range_add
  given: {p q : NonarchAddGroupSeminorm E} {x : E}
  proof: ⟨0, by
    rintro _ ⟨x, rfl⟩
    dsimp
    positivity⟩

中文:
定理 add_bddBelow_range_add
  条件: {p q : NonarchAdd群半范数 E} {x : E}
  证明: ⟨0, by
    rintro _ ⟨x, rfl⟩
    dsimp
    positivity⟩
-/
theorem add_bddBelow_range_add {p q : NonarchAddGroupSeminorm E} {x : E} :
    BddBelow (range fun y => p y + q (x - y)) :=
  ⟨0, by
    rintro _ ⟨x, rfl⟩
    dsimp
    positivity⟩

end AddCommGroup

end NonarchAddGroupSeminorm

namespace GroupSeminorm

variable [Group E] [SMul R Real] [SMul R Real>=0] [IsScalarTower R Real>=0 Real]

/--
Instance `toOne` / 实例 `toOne`

English:
instance toOne
  signature: [DecidableEq E]
  body: ⟨{ toFun := fun x => if x = 1 then 0 else 1
      map_one' := if_pos rfl
      mul_le' := fun x y => by
        by_cases hx : x = 1
        · rw [if_pos hx, hx, one_mul, zero_add]
        · rw [if_neg hx]
          refine le_add_of_le_of_nonneg ?_ ?_ <;> split_ifs <;> norm_num
      inv' := fun x =>

中文:
实例 toOne
  签名: [DecidableEq E]
  定义体: ⟨{ toFun := fun x => if x = 1 then 0 else 1
      map_one' := if_pos rfl
      mul_le' := fun x y => by
        by_cases hx : x = 1
        · rw [if_pos hx, hx, one_mul, zero_add]
        · rw [if_neg hx]
          refine le_add_of_le_of_nonneg ?_ ?_ <;> split_ifs <;> norm_num
      inv' := fun x =>

Depends on / 依赖: if_neg, if_pos, inv_eq_one, le_add_of_le_of_nonneg, map_one, mul_le, one_mul, simp_rw, split_ifs, zero_add
-/
instance toOne [DecidableEq E] : One (GroupSeminorm E) :=
  ⟨{ toFun := fun x => if x = 1 then 0 else 1
      map_one' := if_pos rfl
      mul_le' := fun x y => by
        by_cases hx : x = 1
        · rw [if_pos hx, hx, one_mul, zero_add]
        · rw [if_neg hx]
          refine le_add_of_le_of_nonneg ?_ ?_ <;> split_ifs <;> norm_num
      inv' := fun x => by simp_rw [inv_eq_one] }⟩

@[simp]
/--
theorem `apply_one` / 定理 `apply_one`

English:
theorem apply_one
  given: [DecidableEq E] (x : E)
  statement: (1 : GroupSeminorm E) x = if x = 1 then 0 else 1
  proof: rfl

中文:
定理 apply_one
  条件: [DecidableEq E] (x : E)
  结论: (1 : 群半范数 E) x = if x = 1 then 0 else 1
  证明: rfl
-/
theorem apply_one [DecidableEq E] (x : E) : (1 : GroupSeminorm E) x = if x = 1 then 0 else 1 :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMul R (GroupSeminorm E)
  body: ⟨fun r p =>
    { toFun := fun x => r • p x
      map_one' := by
        simp only [← smul_one_smul Real>=0 r (_ : Real), NNReal.smul_def, smul_eq_mul, map_one_eq_zero p,
          mul_zero]
      mul_le' := fun _ _ => by
        simp only [← smul_one_smul Real>=0 r (_ : Real), NNReal.smul_def, smul

中文:
实例 :
  签名: 标量乘法 R (群半范数 E)
  定义体: ⟨fun r p =>
    { toFun := fun x => r • p x
      map_one' := by
        simp only [← smul_one_smul Real>=0 r (_ : Real), NNReal.smul_def, smul_eq_mul, map_one_eq_zero p,
          mul_zero]
      mul_le' := fun _ _ => by
        simp only [← smul_one_smul Real>=0 r (_ : Real), NNReal.smul_def, smul

Depends on / 依赖: NNReal, NNReal.smul_def, map_inv_eq_map, map_mul_le_add, map_one, map_one_eq_zero, mul_add, mul_le, mul_zero, simp_rw, smul_def, smul_eq_mul, smul_one_smul
-/
instance : SMul R (GroupSeminorm E) :=
  ⟨fun r p =>
    { toFun := fun x => r • p x
      map_one' := by
        simp only [← smul_one_smul Real>=0 r (_ : Real), NNReal.smul_def, smul_eq_mul, map_one_eq_zero p,
          mul_zero]
      mul_le' := fun _ _ => by
        simp only [← smul_one_smul Real>=0 r (_ : Real), NNReal.smul_def, smul_eq_mul, ← mul_add]
        gcongr
        apply map_mul_le_add
      inv' := fun x => by simp_rw [map_inv_eq_map p] }⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsSMulApply R (GroupSeminorm E) E Real
  body: rfl

@[deprecated (since := "2026-07-10")] alias coe_smul := FunLike.coe_smul

@[deprecated (since := "2026-07-10")] protected alias smul_apply := smul_apply

中文:
实例 :
  签名: 是SMulApply R (群半范数 E) E 实数
  定义体: rfl

@[deprecated (since := "2026-07-10")] alias coe_smul := FunLike.coe_smul

@[deprecated (since := "2026-07-10")] protected alias smul_apply := smul_apply
-/
instance : IsSMulApply R (GroupSeminorm E) E Real where
  smul_apply _ _ _ := rfl

@[deprecated (since := "2026-07-10")] alias coe_smul := FunLike.coe_smul

@[deprecated (since := "2026-07-10")] protected alias smul_apply := smul_apply

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: R' Real] [SMul R' Real>=0] [IsScalarTower R' Real>=0 Real] [SMul R R'] [IsScalarTower R R' Real] :
  body: FunLike.isScalarTower

中文:
实例 [标量乘法
  签名: R' 实数] [标量乘法 R' 实数>=0] [标量塔 R' 实数>=0 实数] [标量乘法 R R'] [标量塔 R R' 实数] :
  定义体: FunLike.isScalarTower

Depends on / 依赖: FunLike, FunLike.isScalarTower, isScalarTower
-/
instance [SMul R' Real] [SMul R' Real>=0] [IsScalarTower R' Real>=0 Real] [SMul R R'] [IsScalarTower R R' Real] :
    IsScalarTower R R' (GroupSeminorm E) :=
  FunLike.isScalarTower

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddCommMonoid (GroupSeminorm E)
  body: fast_instance% FunLike.addCommMonoid

中文:
实例 :
  签名: 加法交换幺半群 (群半范数 E)
  定义体: fast_instance% FunLike.addCommMonoid

Depends on / 依赖: FunLike, FunLike.addCommMonoid, addCommMonoid, fast_instance
-/
instance : AddCommMonoid (GroupSeminorm E) := fast_instance% FunLike.addCommMonoid

/--
theorem `smul_sup` / 定理 `smul_sup`

English:
theorem smul_sup
  given: (r : R) (p q : GroupSeminorm E)
  statement: r • (p ⊔ q) = r • p ⊔ r • q
  proof: have Real.smul_max : forall x y : Real, r • max x y = max (r • x) (r • y) := fun x y => by
    simpa only [← smul_eq_mul, ← NNReal.smul_def, smul_one_smul Real>=0 r (_ : Real)] using
      mul_max_of_nonneg x y (r • (1 : Real>=0) : Real>=0).coe_nonneg
  ext fun _ => Real.smul_max _ _

中文:
定理 smul_sup
  条件: (r : R) (p q : 群半范数 E)
  结论: r • (p ⊔ q) = r • p ⊔ r • q
  证明: have Real.smul_max : forall x y : Real, r • max x y = max (r • x) (r • y) := fun x y => by
    simpa only [← smul_eq_mul, ← NNReal.smul_def, smul_one_smul Real>=0 r (_ : Real)] using
      mul_max_of_nonneg x y (r • (1 : Real>=0) : Real>=0).coe_nonneg
  ext fun _ => Real.smul_max _ _

Depends on / 依赖: NNReal, NNReal.smul_def, Real.smul_max, coe_nonneg, mul_max_of_nonneg, smul_def, smul_eq_mul, smul_max, smul_one_smul
-/
theorem smul_sup (r : R) (p q : GroupSeminorm E) : r • (p ⊔ q) = r • p ⊔ r • q :=
  have Real.smul_max : forall x y : Real, r • max x y = max (r • x) (r • y) := fun x y => by
    simpa only [← smul_eq_mul, ← NNReal.smul_def, smul_one_smul Real>=0 r (_ : Real)] using
      mul_max_of_nonneg x y (r • (1 : Real>=0) : Real>=0).coe_nonneg
  ext fun _ => Real.smul_max _ _

end GroupSeminorm

namespace NonarchAddGroupSeminorm

variable [AddGroup E] [SMul R Real] [SMul R Real>=0] [IsScalarTower R Real>=0 Real]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DecidableEq
  signature: E] : One (NonarchAddGroupSeminorm E)
  body: ⟨{ toFun := fun x => if x = 0 then 0 else 1
      map_zero' := if_pos rfl
      add_le_max' := fun x y => by
        by_cases hx : x = 0
        · simp_rw [if_pos hx, hx, zero_add]
          exact le_max_of_le_right (le_refl _)
        · simp_rw [if_neg hx]
          split_ifs <;> simp
      neg' :=

中文:
实例 [DecidableEq
  签名: E] : 幺 (NonarchAdd群半范数 E)
  定义体: ⟨{ toFun := fun x => if x = 0 then 0 else 1
      map_zero' := if_pos rfl
      add_le_max' := fun x y => by
        by_cases hx : x = 0
        · simp_rw [if_pos hx, hx, zero_add]
          exact le_max_of_le_right (le_refl _)
        · simp_rw [if_neg hx]
          split_ifs <;> simp
      neg' :=

Depends on / 依赖: add_le_max, if_neg, if_pos, le_max_of_le_right, le_refl, map_zero, neg_eq_zero, simp_rw, split_ifs, zero_add
-/
instance [DecidableEq E] : One (NonarchAddGroupSeminorm E) :=
  ⟨{ toFun := fun x => if x = 0 then 0 else 1
      map_zero' := if_pos rfl
      add_le_max' := fun x y => by
        by_cases hx : x = 0
        · simp_rw [if_pos hx, hx, zero_add]
          exact le_max_of_le_right (le_refl _)
        · simp_rw [if_neg hx]
          split_ifs <;> simp
      neg' := fun x => by simp_rw [neg_eq_zero] }⟩

@[simp]
/--
theorem `apply_one` / 定理 `apply_one`

English:
theorem apply_one
  given: [DecidableEq E] (x : E)
  proof: rfl

中文:
定理 apply_one
  条件: [DecidableEq E] (x : E)
  证明: rfl
-/
theorem apply_one [DecidableEq E] (x : E) :
    (1 : NonarchAddGroupSeminorm E) x = if x = 0 then 0 else 1 :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMul R (NonarchAddGroupSeminorm E)
  body: ⟨fun r p =>
    { toFun := fun x => r • p x
      map_zero' := by
        simp only [← smul_one_smul Real>=0 r (_ : Real), NNReal.smul_def, smul_eq_mul, map_zero p,
          mul_zero]
      add_le_max' := fun x y => by
        simp only [← smul_one_smul Real>=0 r (_ : Real), NNReal.smul_def, smul_e

中文:
实例 :
  签名: 标量乘法 R (NonarchAdd群半范数 E)
  定义体: ⟨fun r p =>
    { toFun := fun x => r • p x
      map_zero' := by
        simp only [← smul_one_smul Real>=0 r (_ : Real), NNReal.smul_def, smul_eq_mul, map_zero p,
          mul_zero]
      add_le_max' := fun x y => by
        simp only [← smul_one_smul Real>=0 r (_ : Real), NNReal.smul_def, smul_e

Depends on / 依赖: NNReal, NNReal.smul_def, NNReal.zero_le_coe, add_le_max, map_add_le_max, map_neg_eq_map, map_zero, mul_max_of_nonneg, mul_zero, simp_rw, smul_def, smul_eq_mul, smul_one_smul, zero_le_coe
-/
instance : SMul R (NonarchAddGroupSeminorm E) :=
  ⟨fun r p =>
    { toFun := fun x => r • p x
      map_zero' := by
        simp only [← smul_one_smul Real>=0 r (_ : Real), NNReal.smul_def, smul_eq_mul, map_zero p,
          mul_zero]
      add_le_max' := fun x y => by
        simp only [← smul_one_smul Real>=0 r (_ : Real), NNReal.smul_def, smul_eq_mul, ←
          mul_max_of_nonneg _ _ NNReal.zero_le_coe]
        gcongr
        apply map_add_le_max
      neg' := fun x => by simp_rw [map_neg_eq_map p] }⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsSMulApply R (NonarchAddGroupSeminorm E) E Real
  body: rfl

@[deprecated (since := "2026-07-10")] alias coe_smul := FunLike.coe_smul

@[deprecated (since := "2026-07-10")] protected alias smul_apply := smul_apply

中文:
实例 :
  签名: 是SMulApply R (NonarchAdd群半范数 E) E 实数
  定义体: rfl

@[deprecated (since := "2026-07-10")] alias coe_smul := FunLike.coe_smul

@[deprecated (since := "2026-07-10")] protected alias smul_apply := smul_apply
-/
instance : IsSMulApply R (NonarchAddGroupSeminorm E) E Real where
  smul_apply _ _ _ := rfl

@[deprecated (since := "2026-07-10")] alias coe_smul := FunLike.coe_smul

@[deprecated (since := "2026-07-10")] protected alias smul_apply := smul_apply

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: R' Real] [SMul R' Real>=0] [IsScalarTower R' Real>=0 Real] [SMul R R'] [IsScalarTower R R' Real] :
  body: FunLike.isScalarTower

中文:
实例 [标量乘法
  签名: R' 实数] [标量乘法 R' 实数>=0] [标量塔 R' 实数>=0 实数] [标量乘法 R R'] [标量塔 R R' 实数] :
  定义体: FunLike.isScalarTower

Depends on / 依赖: FunLike, FunLike.isScalarTower, isScalarTower
-/
instance [SMul R' Real] [SMul R' Real>=0] [IsScalarTower R' Real>=0 Real] [SMul R R'] [IsScalarTower R R' Real] :
    IsScalarTower R R' (NonarchAddGroupSeminorm E) := FunLike.isScalarTower

/--
theorem `smul_sup` / 定理 `smul_sup`

English:
theorem smul_sup
  given: (r : R) (p q : NonarchAddGroupSeminorm E)
  statement: r • (p ⊔ q) = r • p ⊔ r • q
  proof: have Real.smul_max : forall x y : Real, r • max x y = max (r • x) (r • y) := fun x y => by
    simpa only [← smul_eq_mul, ← NNReal.smul_def, smul_one_smul Real>=0 r (_ : Real)] using
      mul_max_of_nonneg x y (r • (1 : Real>=0) : Real>=0).coe_nonneg
  ext fun _ => Real.smul_max _ _

中文:
定理 smul_sup
  条件: (r : R) (p q : NonarchAdd群半范数 E)
  结论: r • (p ⊔ q) = r • p ⊔ r • q
  证明: have Real.smul_max : forall x y : Real, r • max x y = max (r • x) (r • y) := fun x y => by
    simpa only [← smul_eq_mul, ← NNReal.smul_def, smul_one_smul Real>=0 r (_ : Real)] using
      mul_max_of_nonneg x y (r • (1 : Real>=0) : Real>=0).coe_nonneg
  ext fun _ => Real.smul_max _ _

Depends on / 依赖: NNReal, NNReal.smul_def, Real.smul_max, coe_nonneg, mul_max_of_nonneg, smul_def, smul_eq_mul, smul_max, smul_one_smul
-/
theorem smul_sup (r : R) (p q : NonarchAddGroupSeminorm E) : r • (p ⊔ q) = r • p ⊔ r • q :=
  have Real.smul_max : forall x y : Real, r • max x y = max (r • x) (r • y) := fun x y => by
    simpa only [← smul_eq_mul, ← NNReal.smul_def, smul_one_smul Real>=0 r (_ : Real)] using
      mul_max_of_nonneg x y (r • (1 : Real>=0) : Real>=0).coe_nonneg
  ext fun _ => Real.smul_max _ _

end NonarchAddGroupSeminorm

/-! ### Norms -/


namespace GroupNorm

section Group

variable [Group E] {p q : GroupNorm E}

@[to_additive]
/--
Instance `funLike` / 实例 `funLike`

English:
instance funLike
  signature: : FunLike (GroupNorm E) E Real where
  body: f.toFun
  coe_injective f g h := by obtain ⟨⟨_, _, _, _⟩, _⟩ := f; cases g; congr

@[to_additive]

中文:
实例 funLike
  签名: : 函数状 (群范数 E) E 实数 where
  定义体: f.toFun
  coe_injective f g h := by obtain ⟨⟨_, _, _, _⟩, _⟩ := f; cases g; congr

@[to_additive]

Depends on / 依赖: f.toFun
-/
instance funLike : FunLike (GroupNorm E) E Real where
  coe f := f.toFun
  coe_injective f g h := by obtain ⟨⟨_, _, _, _⟩, _⟩ := f; cases g; congr

@[to_additive]
/--
Instance `groupNormClass` / 实例 `groupNormClass`

English:
instance groupNormClass
  signature: : GroupNormClass (GroupNorm E) E Real where
  body: f.map_one'
  map_mul_le_add f := f.mul_le'
  map_inv_eq_map f := f.inv'
  eq_one_of_map_eq_zero f := f.eq_one_of_map_eq_zero' _

@[to_additive (attr := simp)]

中文:
实例 groupNormClass
  签名: : 群范数类 (群范数 E) E 实数 where
  定义体: f.map_one'
  map_mul_le_add f := f.mul_le'
  map_inv_eq_map f := f.inv'
  eq_one_of_map_eq_zero f := f.eq_one_of_map_eq_zero' _

@[to_additive (attr := simp)]

Depends on / 依赖: f.map_one, map_one
-/
instance groupNormClass : GroupNormClass (GroupNorm E) E Real where
  map_one_eq_zero f := f.map_one'
  map_mul_le_add f := f.mul_le'
  map_inv_eq_map f := f.inv'
  eq_one_of_map_eq_zero f := f.eq_one_of_map_eq_zero' _

@[to_additive (attr := simp)]
/--
theorem `toGroupSeminorm_eq_coe` / 定理 `toGroupSeminorm_eq_coe`

English:
theorem toGroupSeminorm_eq_coe
  statement: ⇑p.toGroupSeminorm = p
  proof: rfl

@[to_additive (attr := ext)]

中文:
定理 toGroupSeminorm_eq_coe
  结论: ⇑p.toGroupSeminorm = p
  证明: rfl

@[to_additive (attr := ext)]
-/
theorem toGroupSeminorm_eq_coe : ⇑p.toGroupSeminorm = p :=
  rfl

@[to_additive (attr := ext)]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  statement: (forall x, p x = q x) -> p = q
  proof: DFunLike.ext p q

@[to_additive]

中文:
定理 ext
  结论: (对任意 x, p x = q x) -> p = q
  证明: DFunLike.ext p q

@[to_additive]

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem ext : (forall x, p x = q x) -> p = q :=
  DFunLike.ext p q

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (GroupNorm E)
  body: PartialOrder.lift _ DFunLike.coe_injective

@[to_additive]

中文:
实例 :
  签名: 偏序 (群范数 E)
  定义体: PartialOrder.lift _ DFunLike.coe_injective

@[to_additive]

Depends on / 依赖: DFunLike, DFunLike.coe_injective, PartialOrder, PartialOrder.lift, coe_injective
-/
instance : PartialOrder (GroupNorm E) :=
  PartialOrder.lift _ DFunLike.coe_injective

@[to_additive]
/--
theorem `le_def` / 定理 `le_def`

English:
theorem le_def
  statement: p <= q ↔ (p : E -> Real) <= q
  proof: Iff.rfl

@[to_additive]

中文:
定理 le_def
  结论: p <= q ↔ (p : E -> 实数) <= q
  证明: Iff.rfl

@[to_additive]

Depends on / 依赖: Iff.rfl
-/
theorem le_def : p <= q ↔ (p : E -> Real) <= q :=
  Iff.rfl

@[to_additive]
/--
theorem `lt_def` / 定理 `lt_def`

English:
theorem lt_def
  statement: p < q ↔ (p : E -> Real) < q
  proof: Iff.rfl

@[to_additive (attr := simp, norm_cast)]

中文:
定理 lt_def
  结论: p < q ↔ (p : E -> 实数) < q
  证明: Iff.rfl

@[to_additive (attr := simp, norm_cast)]

Depends on / 依赖: Iff.rfl
-/
theorem lt_def : p < q ↔ (p : E -> Real) < q :=
  Iff.rfl

@[to_additive (attr := simp, norm_cast)]
/--
theorem `coe_le_coe` / 定理 `coe_le_coe`

English:
theorem coe_le_coe
  statement: (p : E -> Real) <= q ↔ p <= q
  proof: Iff.rfl

@[to_additive (attr := simp, norm_cast)]

中文:
定理 coe_le_coe
  结论: (p : E -> 实数) <= q ↔ p <= q
  证明: Iff.rfl

@[to_additive (attr := simp, norm_cast)]

Depends on / 依赖: Iff.rfl
-/
theorem coe_le_coe : (p : E -> Real) <= q ↔ p <= q :=
  Iff.rfl

@[to_additive (attr := simp, norm_cast)]
/--
theorem `coe_lt_coe` / 定理 `coe_lt_coe`

English:
theorem coe_lt_coe
  statement: (p : E -> Real) < q ↔ p < q
  proof: Iff.rfl

中文:
定理 coe_lt_coe
  结论: (p : E -> 实数) < q ↔ p < q
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem coe_lt_coe : (p : E -> Real) < q ↔ p < q :=
  Iff.rfl

variable (p q)

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Add (GroupNorm E)
  body: ⟨fun p q =>
    { p.toGroupSeminorm + q.toGroupSeminorm with
      eq_one_of_map_eq_zero' := fun _x hx =>
of_not_not fun h => hx.not_gt add_pos (map_pos_of_ne_one p h) (map_pos_of_ne_one q h) }⟩

@[to_additive]

中文:
实例 :
  签名: 加法 (群范数 E)
  定义体: ⟨fun p q =>
    { p.toGroupSeminorm + q.toGroupSeminorm with
      eq_one_of_map_eq_zero' := fun _x hx =>
of_not_not fun h => hx.not_gt add_pos (map_pos_of_ne_one p h) (map_pos_of_ne_one q h) }⟩

@[to_additive]

Depends on / 依赖: add_pos, eq_one_of_map_eq_zero, hx.not_gt, map_pos_of_ne_one, not_gt, of_not_not, p.toGroupSeminorm, q.toGroupSeminorm, toGroupSeminorm
-/
instance : Add (GroupNorm E) :=
  ⟨fun p q =>
    { p.toGroupSeminorm + q.toGroupSeminorm with
      eq_one_of_map_eq_zero' := fun _x hx =>
of_not_not fun h => hx.not_gt add_pos (map_pos_of_ne_one p h) (map_pos_of_ne_one q h) }⟩

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsAddApply (GroupNorm E) E Real
  body: rfl

@[deprecated (since := "2026-07-10")] alias _root_.GroupNorm.coe_add := FunLike.coe_add
@[deprecated (since := "2026-07-10")] alias _root_.AddGroupNorm.coe_add := FunLike.coe_add

@[deprecated (since := "2026-07-10")] protected alias _root_.GroupNorm.add_apply := add_apply
@[deprecated (since :

中文:
实例 :
  签名: 是加法Apply (群范数 E) E 实数
  定义体: rfl

@[deprecated (since := "2026-07-10")] alias _root_.GroupNorm.coe_add := FunLike.coe_add
@[deprecated (since := "2026-07-10")] alias _root_.AddGroupNorm.coe_add := FunLike.coe_add

@[deprecated (since := "2026-07-10")] protected alias _root_.GroupNorm.add_apply := add_apply
@[deprecated (since :
-/
instance : IsAddApply (GroupNorm E) E Real where
  add_apply _ _ _ := rfl

@[deprecated (since := "2026-07-10")] alias _root_.GroupNorm.coe_add := FunLike.coe_add
@[deprecated (since := "2026-07-10")] alias _root_.AddGroupNorm.coe_add := FunLike.coe_add

@[deprecated (since := "2026-07-10")] protected alias _root_.GroupNorm.add_apply := add_apply
@[deprecated (since := "2026-07-10")] protected alias _root_.AddGroupNorm.add_apply := add_apply

-- Note: To define an instance SupSet (GroupNorm E) requires a canonical "bottom" norm for sSup ∅.
-- The zero function fails definiteness; the discrete norm needs complex proofs.
-- See https://github.com/leanprover-community/mathlib/pull/11329 for context.
@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Max (GroupNorm E)
  body: ⟨fun p q =>
    { p.toGroupSeminorm ⊔ q.toGroupSeminorm with
      eq_one_of_map_eq_zero' := fun _x hx =>
of_not_not fun h => hx.not_gt lt_sup_iff.2 Or.inl map_pos_of_ne_one p h }⟩

@[to_additive (attr := simp, norm_cast)]

中文:
实例 :
  签名: 最大值 (群范数 E)
  定义体: ⟨fun p q =>
    { p.toGroupSeminorm ⊔ q.toGroupSeminorm with
      eq_one_of_map_eq_zero' := fun _x hx =>
of_not_not fun h => hx.not_gt lt_sup_iff.2 Or.inl map_pos_of_ne_one p h }⟩

@[to_additive (attr := simp, norm_cast)]

Depends on / 依赖: Or.inl, eq_one_of_map_eq_zero, hx.not_gt, lt_sup_iff, map_pos_of_ne_one, not_gt, of_not_not, p.toGroupSeminorm, q.toGroupSeminorm, toGroupSeminorm
-/
instance : Max (GroupNorm E) :=
  ⟨fun p q =>
    { p.toGroupSeminorm ⊔ q.toGroupSeminorm with
      eq_one_of_map_eq_zero' := fun _x hx =>
of_not_not fun h => hx.not_gt lt_sup_iff.2 Or.inl map_pos_of_ne_one p h }⟩

@[to_additive (attr := simp, norm_cast)]
/--
theorem `coe_sup` / 定理 `coe_sup`

English:
theorem coe_sup
  statement: ⇑(p ⊔ q) = ⇑p ⊔ ⇑q
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 coe_sup
  结论: ⇑(p ⊔ q) = ⇑p ⊔ ⇑q
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem coe_sup : ⇑(p ⊔ q) = ⇑p ⊔ ⇑q :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `sup_apply` / 定理 `sup_apply`

English:
theorem sup_apply
  given: (x : E)
  statement: (p ⊔ q) x = p x ⊔ q x
  proof: rfl

@[to_additive]

中文:
定理 sup_apply
  条件: (x : E)
  结论: (p ⊔ q) x = p x ⊔ q x
  证明: rfl

@[to_additive]
-/
theorem sup_apply (x : E) : (p ⊔ q) x = p x ⊔ q x :=
  rfl

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SemilatticeSup (GroupNorm E)
  body: DFunLike.coe_injective.semilatticeSup _ .rfl .rfl coe_sup

中文:
实例 :
  签名: SemilatticeSup (群范数 E)
  定义体: DFunLike.coe_injective.semilatticeSup _ .rfl .rfl coe_sup

Depends on / 依赖: DFunLike, DFunLike.coe_injective.semilatticeSup, coe_injective, coe_sup, semilatticeSup
-/
instance : SemilatticeSup (GroupNorm E) :=
  DFunLike.coe_injective.semilatticeSup _ .rfl .rfl coe_sup

end Group

end GroupNorm

namespace AddGroupNorm

variable [AddGroup E] [DecidableEq E]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: One (AddGroupNorm E)
  body: ⟨{ (1 : AddGroupSeminorm E) with
      eq_zero_of_map_eq_zero' := fun _x => zero_ne_one.ite_eq_left_iff.1 }⟩

@[simp]

中文:
实例 :
  签名: 幺 (加法群范数 E)
  定义体: ⟨{ (1 : AddGroupSeminorm E) with
      eq_zero_of_map_eq_zero' := fun _x => zero_ne_one.ite_eq_left_iff.1 }⟩

@[simp]

Depends on / 依赖: AddGroupSeminorm, eq_zero_of_map_eq_zero, ite_eq_left_iff, zero_ne_one, zero_ne_one.ite_eq_left_iff
-/
instance : One (AddGroupNorm E) :=
  ⟨{ (1 : AddGroupSeminorm E) with
      eq_zero_of_map_eq_zero' := fun _x => zero_ne_one.ite_eq_left_iff.1 }⟩

@[simp]
/--
theorem `apply_one` / 定理 `apply_one`

English:
theorem apply_one
  given: (x : E)
  statement: (1 : AddGroupNorm E) x = if x = 0 then 0 else 1
  proof: rfl

中文:
定理 apply_one
  条件: (x : E)
  结论: (1 : 加法群范数 E) x = if x = 0 then 0 else 1
  证明: rfl
-/
theorem apply_one (x : E) : (1 : AddGroupNorm E) x = if x = 0 then 0 else 1 :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (AddGroupNorm E)
  body: ⟨1⟩

中文:
实例 :
  签名: 可居 (加法群范数 E)
  定义体: ⟨1⟩
-/
instance : Inhabited (AddGroupNorm E) :=
  ⟨1⟩

end AddGroupNorm

namespace GroupNorm

/--
Instance `_root_.AddGroupNorm.toOne` / 实例 `_root_.AddGroupNorm.toOne`

English:
instance _root_.AddGroupNorm.toOne
  signature: [AddGroup E] [DecidableEq E]
  body: ⟨{ (1 : AddGroupSeminorm E) with
    eq_zero_of_map_eq_zero' := fun _ => zero_ne_one.ite_eq_left_iff.1 }⟩

中文:
实例 _root_.加法群范数.toOne
  签名: [加法群 E] [DecidableEq E]
  定义体: ⟨{ (1 : AddGroupSeminorm E) with
    eq_zero_of_map_eq_zero' := fun _ => zero_ne_one.ite_eq_left_iff.1 }⟩

Depends on / 依赖: AddGroupSeminorm, eq_zero_of_map_eq_zero, ite_eq_left_iff, zero_ne_one, zero_ne_one.ite_eq_left_iff
-/
instance _root_.AddGroupNorm.toOne [AddGroup E] [DecidableEq E] : One (AddGroupNorm E) :=
  ⟨{ (1 : AddGroupSeminorm E) with
    eq_zero_of_map_eq_zero' := fun _ => zero_ne_one.ite_eq_left_iff.1 }⟩

variable [Group E] [DecidableEq E]

/--
Instance `toOne` / 实例 `toOne`

English:
instance toOne
  signature: : One (GroupNorm E)
  body: ⟨{ (1 : GroupSeminorm E) with eq_one_of_map_eq_zero' := fun _ => zero_ne_one.ite_eq_left_iff.1 }⟩

@[simp]

中文:
实例 toOne
  签名: : 幺 (群范数 E)
  定义体: ⟨{ (1 : GroupSeminorm E) with eq_one_of_map_eq_zero' := fun _ => zero_ne_one.ite_eq_left_iff.1 }⟩

@[simp]

Depends on / 依赖: GroupSeminorm, eq_one_of_map_eq_zero, ite_eq_left_iff, zero_ne_one, zero_ne_one.ite_eq_left_iff
-/
instance toOne : One (GroupNorm E) :=
  ⟨{ (1 : GroupSeminorm E) with eq_one_of_map_eq_zero' := fun _ => zero_ne_one.ite_eq_left_iff.1 }⟩

@[simp]
/--
theorem `apply_one` / 定理 `apply_one`

English:
theorem apply_one
  given: (x : E)
  statement: (1 : GroupNorm E) x = if x = 1 then 0 else 1
  proof: rfl

@[to_additive existing]

中文:
定理 apply_one
  条件: (x : E)
  结论: (1 : 群范数 E) x = if x = 1 then 0 else 1
  证明: rfl

@[to_additive existing]
-/
theorem apply_one (x : E) : (1 : GroupNorm E) x = if x = 1 then 0 else 1 :=
  rfl

@[to_additive existing]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (GroupNorm E)
  body: ⟨1⟩

中文:
实例 :
  签名: 可居 (群范数 E)
  定义体: ⟨1⟩
-/
instance : Inhabited (GroupNorm E) :=
  ⟨1⟩

end GroupNorm

namespace NonarchAddGroupNorm

section AddGroup

variable [AddGroup E] {p q : NonarchAddGroupNorm E}

/--
Instance `funLike` / 实例 `funLike`

English:
instance funLike
  signature: : FunLike (NonarchAddGroupNorm E) E Real where
  body: f.toFun
  coe_injective f g h := by obtain ⟨⟨⟨_, _⟩, _, _⟩, _⟩ := f; cases g; congr

中文:
实例 funLike
  签名: : 函数状 (NonarchAdd群范数 E) E 实数 where
  定义体: f.toFun
  coe_injective f g h := by obtain ⟨⟨⟨_, _⟩, _, _⟩, _⟩ := f; cases g; congr

Depends on / 依赖: f.toFun
-/
instance funLike : FunLike (NonarchAddGroupNorm E) E Real where
  coe f := f.toFun
  coe_injective f g h := by obtain ⟨⟨⟨_, _⟩, _, _⟩, _⟩ := f; cases g; congr

/--
Instance `nonarchAddGroupNormClass` / 实例 `nonarchAddGroupNormClass`

English:
instance nonarchAddGroupNormClass
  signature: : NonarchAddGroupNormClass (NonarchAddGroupNorm E) E where
  body: f.add_le_max'
  map_zero f := f.map_zero'
  map_neg_eq_map' f := f.neg'
  eq_zero_of_map_eq_zero f := f.eq_zero_of_map_eq_zero' _

@[simp]

中文:
实例 nonarchAddGroupNormClass
  签名: : NonarchAdd群范数类 (NonarchAdd群范数 E) E where
  定义体: f.add_le_max'
  map_zero f := f.map_zero'
  map_neg_eq_map' f := f.neg'
  eq_zero_of_map_eq_zero f := f.eq_zero_of_map_eq_zero' _

@[simp]

Depends on / 依赖: add_le_max, f.add_le_max
-/
instance nonarchAddGroupNormClass : NonarchAddGroupNormClass (NonarchAddGroupNorm E) E where
  map_add_le_max f := f.add_le_max'
  map_zero f := f.map_zero'
  map_neg_eq_map' f := f.neg'
  eq_zero_of_map_eq_zero f := f.eq_zero_of_map_eq_zero' _

@[simp]
/--
theorem `toNonarchAddGroupSeminorm_eq_coe` / 定理 `toNonarchAddGroupSeminorm_eq_coe`

English:
theorem toNonarchAddGroupSeminorm_eq_coe
  statement: ⇑p.toNonarchAddGroupSeminorm = p
  proof: rfl

@[ext]

中文:
定理 toNonarchAddGroupSeminorm_eq_coe
  结论: ⇑p.toNonarchAddGroupSeminorm = p
  证明: rfl

@[ext]
-/
theorem toNonarchAddGroupSeminorm_eq_coe : ⇑p.toNonarchAddGroupSeminorm = p :=
  rfl

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  statement: (forall x, p x = q x) -> p = q
  proof: DFunLike.ext p q

中文:
定理 ext
  结论: (对任意 x, p x = q x) -> p = q
  证明: DFunLike.ext p q

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem ext : (forall x, p x = q x) -> p = q :=
  DFunLike.ext p q

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (NonarchAddGroupNorm E)
  body: PartialOrder.lift _ DFunLike.coe_injective

中文:
实例 :
  签名: 偏序 (NonarchAdd群范数 E)
  定义体: PartialOrder.lift _ DFunLike.coe_injective

Depends on / 依赖: DFunLike, DFunLike.coe_injective, PartialOrder, PartialOrder.lift, coe_injective
-/
noncomputable instance : PartialOrder (NonarchAddGroupNorm E) :=
  PartialOrder.lift _ DFunLike.coe_injective

/--
theorem `le_def` / 定理 `le_def`

English:
theorem le_def
  statement: p <= q ↔ (p : E -> Real) <= q
  proof: Iff.rfl

中文:
定理 le_def
  结论: p <= q ↔ (p : E -> 实数) <= q
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem le_def : p <= q ↔ (p : E -> Real) <= q :=
  Iff.rfl

/--
theorem `lt_def` / 定理 `lt_def`

English:
theorem lt_def
  statement: p < q ↔ (p : E -> Real) < q
  proof: Iff.rfl

@[simp, norm_cast]

中文:
定理 lt_def
  结论: p < q ↔ (p : E -> 实数) < q
  证明: Iff.rfl

@[simp, norm_cast]

Depends on / 依赖: Iff.rfl
-/
theorem lt_def : p < q ↔ (p : E -> Real) < q :=
  Iff.rfl

@[simp, norm_cast]
/--
theorem `coe_le_coe` / 定理 `coe_le_coe`

English:
theorem coe_le_coe
  statement: (p : E -> Real) <= q ↔ p <= q
  proof: Iff.rfl

@[simp, norm_cast]

中文:
定理 coe_le_coe
  结论: (p : E -> 实数) <= q ↔ p <= q
  证明: Iff.rfl

@[simp, norm_cast]

Depends on / 依赖: Iff.rfl
-/
theorem coe_le_coe : (p : E -> Real) <= q ↔ p <= q :=
  Iff.rfl

@[simp, norm_cast]
/--
theorem `coe_lt_coe` / 定理 `coe_lt_coe`

English:
theorem coe_lt_coe
  statement: (p : E -> Real) < q ↔ p < q
  proof: Iff.rfl

中文:
定理 coe_lt_coe
  结论: (p : E -> 实数) < q ↔ p < q
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem coe_lt_coe : (p : E -> Real) < q ↔ p < q :=
  Iff.rfl

variable (p q)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Max (NonarchAddGroupNorm E)
  body: ⟨fun p q =>
    { p.toNonarchAddGroupSeminorm ⊔ q.toNonarchAddGroupSeminorm with
      eq_zero_of_map_eq_zero' := fun _x hx =>
of_not_not fun h => hx.not_gt lt_sup_iff.2 Or.inl map_pos_of_ne_zero p h }⟩

@[simp, norm_cast]

中文:
实例 :
  签名: 最大值 (NonarchAdd群范数 E)
  定义体: ⟨fun p q =>
    { p.toNonarchAddGroupSeminorm ⊔ q.toNonarchAddGroupSeminorm with
      eq_zero_of_map_eq_zero' := fun _x hx =>
of_not_not fun h => hx.not_gt lt_sup_iff.2 Or.inl map_pos_of_ne_zero p h }⟩

@[simp, norm_cast]

Depends on / 依赖: Or.inl, eq_zero_of_map_eq_zero, hx.not_gt, lt_sup_iff, map_pos_of_ne_zero, not_gt, of_not_not, p.toNonarchAddGroupSeminorm, q.toNonarchAddGroupSeminorm, toNonarchAddGroupSeminorm
-/
instance : Max (NonarchAddGroupNorm E) :=
  ⟨fun p q =>
    { p.toNonarchAddGroupSeminorm ⊔ q.toNonarchAddGroupSeminorm with
      eq_zero_of_map_eq_zero' := fun _x hx =>
of_not_not fun h => hx.not_gt lt_sup_iff.2 Or.inl map_pos_of_ne_zero p h }⟩

@[simp, norm_cast]
/--
theorem `coe_sup` / 定理 `coe_sup`

English:
theorem coe_sup
  statement: ⇑(p ⊔ q) = ⇑p ⊔ ⇑q
  proof: rfl

@[simp]

中文:
定理 coe_sup
  结论: ⇑(p ⊔ q) = ⇑p ⊔ ⇑q
  证明: rfl

@[simp]
-/
theorem coe_sup : ⇑(p ⊔ q) = ⇑p ⊔ ⇑q :=
  rfl

@[simp]
/--
theorem `sup_apply` / 定理 `sup_apply`

English:
theorem sup_apply
  given: (x : E)
  statement: (p ⊔ q) x = p x ⊔ q x
  proof: rfl

中文:
定理 sup_apply
  条件: (x : E)
  结论: (p ⊔ q) x = p x ⊔ q x
  证明: rfl
-/
theorem sup_apply (x : E) : (p ⊔ q) x = p x ⊔ q x :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SemilatticeSup (NonarchAddGroupNorm E)
  body: DFunLike.coe_injective.semilatticeSup _ .rfl .rfl coe_sup

中文:
实例 :
  签名: SemilatticeSup (NonarchAdd群范数 E)
  定义体: DFunLike.coe_injective.semilatticeSup _ .rfl .rfl coe_sup

Depends on / 依赖: DFunLike, DFunLike.coe_injective.semilatticeSup, coe_injective, coe_sup, semilatticeSup
-/
noncomputable instance : SemilatticeSup (NonarchAddGroupNorm E) :=
  DFunLike.coe_injective.semilatticeSup _ .rfl .rfl coe_sup

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DecidableEq
  signature: E] : One (NonarchAddGroupNorm E)
  body: ⟨{ (1 : NonarchAddGroupSeminorm E) with
      eq_zero_of_map_eq_zero' := fun _ => zero_ne_one.ite_eq_left_iff.1 }⟩

@[simp]

中文:
实例 [DecidableEq
  签名: E] : 幺 (NonarchAdd群范数 E)
  定义体: ⟨{ (1 : NonarchAddGroupSeminorm E) with
      eq_zero_of_map_eq_zero' := fun _ => zero_ne_one.ite_eq_left_iff.1 }⟩

@[simp]

Depends on / 依赖: NonarchAddGroupSeminorm, eq_zero_of_map_eq_zero, ite_eq_left_iff, zero_ne_one, zero_ne_one.ite_eq_left_iff
-/
instance [DecidableEq E] : One (NonarchAddGroupNorm E) :=
  ⟨{ (1 : NonarchAddGroupSeminorm E) with
      eq_zero_of_map_eq_zero' := fun _ => zero_ne_one.ite_eq_left_iff.1 }⟩

@[simp]
/--
theorem `apply_one` / 定理 `apply_one`

English:
theorem apply_one
  given: [DecidableEq E] (x : E)
  proof: rfl

中文:
定理 apply_one
  条件: [DecidableEq E] (x : E)
  证明: rfl
-/
theorem apply_one [DecidableEq E] (x : E) :
    (1 : NonarchAddGroupNorm E) x = if x = 0 then 0 else 1 :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DecidableEq
  signature: E] : Inhabited (NonarchAddGroupNorm E)
  body: ⟨1⟩

中文:
实例 [DecidableEq
  签名: E] : 可居 (NonarchAdd群范数 E)
  定义体: ⟨1⟩
-/
instance [DecidableEq E] : Inhabited (NonarchAddGroupNorm E) :=
  ⟨1⟩

end AddGroup

end NonarchAddGroupNorm
