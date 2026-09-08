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

/-- A seminorm on an additive group `G` is a function `f : G → ℝ` that preserves zero, is
subadditive and such that `f (-x) = f x` for all `x`. -/
/-
**AddGroupSeminorm** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(G : Type u_6) → [AddGroup G] → Type u_6
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A seminorm on an additive group `G` is a function `f : G → ℝ` that preserves zer
o, is
subadditive and such that `f (-x) = f x` for all `x`.
-/
structure AddGroupSeminorm (G : Type*) [AddGroup G] where
  -- Porting note: can't extend `ZeroHom G ℝ` because otherwise `to_additive` won't work since
  -- we aren't using old structures
  /-- The bare function of an `AddGroupSeminorm`. -/
  protected toFun : G → ℝ
  /-- The image of zero is zero. -/
  protected map_zero' : toFun 0 = 0
  /-- The seminorm is subadditive. -/
  protected add_le' : ∀ r s, toFun (r + s) ≤ toFun r + toFun s
  /-- The seminorm is invariant under negation. -/
  protected neg' : ∀ r, toFun (-r) = toFun r

/-- A seminorm on a group `G` is a function `f : G → ℝ` that sends one to zero, is submultiplicative
and such that `f x⁻¹ = f x` for all `x`. -/
@[to_additive]
/-
**GroupSeminorm** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(G : Type u_6) → [Group G] → Type u_6
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A seminorm on a group `G` is a function `f : G → ℝ` that sends one to zero, is s
ubmultiplicative
and such that `f x⁻¹ = f x` for all `x`.
-/
structure GroupSeminorm (G : Type*) [Group G] where
  /-- The bare function of a `GroupSeminorm`. -/
  protected toFun : G → ℝ
  /-- The image of one is zero. -/
  protected map_one' : toFun 1 = 0
  /-- The seminorm applied to a product is dominated by the sum of the seminorm applied to the
  factors. -/
  protected mul_le' : ∀ x y, toFun (x * y) ≤ toFun x + toFun y
  /-- The seminorm is invariant under inversion. -/
  protected inv' : ∀ x, toFun x⁻¹ = toFun x

/-- A nonarchimedean seminorm on an additive group `G` is a function `f : G → ℝ` that preserves
zero, is nonarchimedean and such that `f (-x) = f x` for all `x`. -/
/-
**NonarchAddGroupSeminorm** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(G : Type u_6) → [AddGroup G] → Type u_6
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A nonarchimedean seminorm on an additive group `G` is a function `f : G → ℝ` tha
t preserves
zero, is nonarchimedean and such that `f (-x) = f x` for all `x`.
-/
structure NonarchAddGroupSeminorm (G : Type*) [AddGroup G] extends ZeroHom G ℝ where
  /-- The seminorm applied to a sum is dominated by the maximum of the function applied to the
  addends. -/
  protected add_le_max' : ∀ r s, toFun (r + s) ≤ max (toFun r) (toFun s)
  /-- The seminorm is invariant under negation. -/
  protected neg' : ∀ r, toFun (-r) = toFun r

/-! NOTE: We do not define `NonarchAddGroupSeminorm` as an extension of `AddGroupSeminorm`
  to avoid having a superfluous `add_le'` field in the resulting structure. The same applies to
  `NonarchAddGroupNorm` below. -/


/-- A norm on an additive group `G` is a function `f : G → ℝ` that preserves zero, is subadditive
and such that `f (-x) = f x` and `f x = 0 → x = 0` for all `x`. -/
/-
**AddGroupNorm** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(G : Type u_6) → [AddGroup G] → Type u_6
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A norm on an additive group `G` is a function `f : G → ℝ` that preserves zero, i
s subadditive
and such that `f (-x) = f x` and `f x = 0 → x = 0` for all `x`.
-/
structure AddGroupNorm (G : Type*) [AddGroup G] extends AddGroupSeminorm G where
  /-- If the image under the seminorm is zero, then the argument is zero. -/
  protected eq_zero_of_map_eq_zero' : ∀ x, toFun x = 0 → x = 0

/-- A seminorm on a group `G` is a function `f : G → ℝ` that sends one to zero, is submultiplicative
and such that `f x⁻¹ = f x` and `f x = 0 → x = 1` for all `x`. -/
@[to_additive]
/-
**GroupNorm** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(G : Type u_6) → [Group G] → Type u_6
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A seminorm on a group `G` is a function `f : G → ℝ` that sends one to zero, is s
ubmultiplicative
and such that `f x⁻¹ = f x` and `f x = 0 → x = 1` for all `x`.
-/
structure GroupNorm (G : Type*) [Group G] extends GroupSeminorm G where
  /-- If the image under the norm is zero, then the argument is one. -/
  protected eq_one_of_map_eq_zero' : ∀ x, toFun x = 0 → x = 1

/-- A nonarchimedean norm on an additive group `G` is a function `f : G → ℝ` that preserves zero, is
nonarchimedean and such that `f (-x) = f x` and `f x = 0 → x = 0` for all `x`. -/
/-
**NonarchAddGroupNorm** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(G : Type u_6) → [AddGroup G] → Type u_6
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A nonarchimedean norm on an additive group `G` is a function `f : G → ℝ` that pr
eserves zero, is
nonarchimedean and such that `f (-x) = f x` and `f x = 0 → x = 0` for all `x`.
-/
structure NonarchAddGroupNorm (G : Type*) [AddGroup G] extends NonarchAddGroupSeminorm G where
  /-- If the image under the norm is zero, then the argument is zero. -/
  protected eq_zero_of_map_eq_zero' : ∀ x, toFun x = 0 → x = 0

/-- `NonarchAddGroupSeminormClass F α` states that `F` is a type of nonarchimedean seminorms on
the additive group `α`.

You should extend this class when you extend `NonarchAddGroupSeminorm`. -/
/-
**NonarchAddGroupSeminormClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(F : Type u_6) → (α : outParam (Type u_7)) → [AddGroup α] → [FunLike F α ℝ
] → Prop
参数：Type u_7。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`NonarchAddGroupSeminormClass F α` states that `F` is a type of nonarchimedean s
eminorms on
the additive group `α`.

You should extend this class when you extend `NonarchAddGroupSeminorm`.
-/
class NonarchAddGroupSeminormClass (F : Type*) (α : outParam Type*)
    [AddGroup α] [FunLike F α ℝ] : Prop
    extends NonarchimedeanHomClass F α ℝ where
  /-- The image of zero is zero. -/
  protected map_zero (f : F) : f 0 = 0
  /-- The seminorm is invariant under negation. -/
  protected map_neg_eq_map' (f : F) (a : α) : f (-a) = f a

/-- `NonarchAddGroupNormClass F α` states that `F` is a type of nonarchimedean norms on the
additive group `α`.

You should extend this class when you extend `NonarchAddGroupNorm`. -/
/-
**NonarchAddGroupNormClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(F : Type u_6) → (α : outParam (Type u_7)) → [AddGroup α] → [FunLike F α ℝ
] → Prop
参数：Type u_7。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`NonarchAddGroupNormClass F α` states that `F` is a type of nonarchimedean norms
 on the
additive group `α`.

You should extend this class when you extend `NonarchAddGroupNorm`.
-/
class NonarchAddGroupNormClass (F : Type*) (α : outParam Type*) [AddGroup α] [FunLike F α ℝ] : Prop
    extends NonarchAddGroupSeminormClass F α where
  /-- If the image under the norm is zero, then the argument is zero. -/
  protected eq_zero_of_map_eq_zero (f : F) {a : α} : f a = 0 → a = 0

section NonarchAddGroupSeminormClass

variable [AddGroup E] [FunLike F E ℝ] [NonarchAddGroupSeminormClass F E] (f : F) (x y : E)

/-
**map_sub_le_max** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_sub_le_max : f (x - y) <= max (f x) (f y)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NonarchAddGroupSeminormClass.map_neg_eq_map'`：∀ {F : Type u_6} {α : outP
aram (Type u_7)} {inst : AddGroup α} {inst_1 : FunLike F α ℝ}   [self : NonarchA
ddGroupSeminormClass F α] (f : F) …
· 使用定理 `NonarchimedeanHomClass.map_add_le_max`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : Add α} {inst_1 : LinearOrder β}   {i
nst_2 : FunLike F α β} [sel…
· 使用定理 `NonarchAddGroupSeminormClass.toNonarchimedeanHomClass`：∀ {F : Type u_6} 
{α : outParam (Type u_7)} {inst : AddGroup α} {inst_1 : FunLike F α ℝ}   [self :
 NonarchAddGroupSeminormClass F α], Nonarch…
-/
theorem map_sub_le_max : f (x - y) ≤ max (f x) (f y) := by
  rw [sub_eq_add_neg, ← NonarchAddGroupSeminormClass.map_neg_eq_map' f y]
  exact map_add_le_max _ _ _

end NonarchAddGroupSeminormClass

-- See note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) NonarchAddGroupSeminormClass.toAddGroupSeminormClass
    [FunLike F E ℝ] [AddGroup E] [NonarchAddGroupSeminormClass F E] : AddGroupSeminormClass F E ℝ :=
  { ‹NonarchAddGroupSeminormClass F E› with
    map_add_le_add := fun f _ _ =>
      haveI h_nonneg : ∀ a, 0 ≤ f a := by
        intro a
        rw [← NonarchAddGroupSeminormClass.map_zero f, ← sub_self a]
        exact le_trans (map_sub_le_max _ _ _) (by rw [max_self (f a)])
      le_trans (map_add_le_max _ _ _)
        (max_le (le_add_of_nonneg_right (h_nonneg _)) (le_add_of_nonneg_left (h_nonneg _)))
    map_neg_eq_map := NonarchAddGroupSeminormClass.map_neg_eq_map' }

-- See note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) NonarchAddGroupNormClass.toAddGroupNormClass
    [FunLike F E ℝ] [AddGroup E] [NonarchAddGroupNormClass F E] : AddGroupNormClass F E ℝ :=
  { ‹NonarchAddGroupNormClass F E› with
    map_add_le_add := map_add_le_add
    map_neg_eq_map := NonarchAddGroupSeminormClass.map_neg_eq_map' }

/-! ### Seminorms -/


namespace GroupSeminorm

section Group

variable [Group E] [Group F] [Group G] {p q : GroupSeminorm E}

@[to_additive]
/-
**GroupSeminorm.funLike** 是 Mathlib 中的一个实例，位于命名空间 `GroupSeminorm`。
形式化陈述：funLike : FunLike (GroupSeminorm E) E Real where coe f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance funLike : FunLike (GroupSeminorm E) E ℝ where
  coe f := f.toFun
  coe_injective f g h := by cases f; cases g; congr

@[to_additive]
/-
**GroupSeminorm.groupSeminormClass** 是 Mathlib 中的一个实例，位于命名空间 `GroupSeminorm`。
形式化陈述：groupSeminormClass : GroupSeminormClass (GroupSeminorm E) E Real where map
_one_eq_zero f
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `GroupSeminorm.mul_le'`：∀ {G : Type u_6} [inst : Group G] (self : GroupSe
minorm G) (x y : G), self.toFun (x * y) ≤ self.toFun x + self.toFun y
· 使用定理 `GroupSeminorm.map_one'`：∀ {G : Type u_6} [inst : Group G] (self : GroupS
eminorm G), self.toFun 1 = 0
· 使用定理 `GroupSeminorm.inv'`：∀ {G : Type u_6} [inst : Group G] (self : GroupSemin
orm G) (x : G), self.toFun x⁻¹ = self.toFun x
-/
instance groupSeminormClass : GroupSeminormClass (GroupSeminorm E) E ℝ where
  map_one_eq_zero f := f.map_one'
  map_mul_le_add f := f.mul_le'
  map_inv_eq_map f := f.inv'

@[to_additive (attr := simp)]
/-
**GroupSeminorm.toFun_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `GroupSeminorm`。
形式化陈述：toFun_eq_coe : p.toFun = p
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toFun_eq_coe : p.toFun = p :=
  rfl

@[to_additive (attr := ext)]
/-
**GroupSeminorm.ext** 是 Mathlib 中的一个定理，位于命名空间 `GroupSeminorm`。
形式化陈述：ext : (forall x, p x = q x) -> p = q
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem ext : (∀ x, p x = q x) → p = q :=
  DFunLike.ext p q

@[to_additive]
/-
**GroupSeminorm.** 是 Mathlib 中的一个实例，位于命名空间 `GroupSeminorm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PartialOrder (GroupSeminorm E) :=
  PartialOrder.lift _ DFunLike.coe_injective

@[to_additive]
/-
**GroupSeminorm.le_def** 是 Mathlib 中的一个定理，位于命名空间 `GroupSeminorm`。
形式化陈述：le_def : p <= q ↔ (p : E -> Real) <= q
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem le_def : p ≤ q ↔ (p : E → ℝ) ≤ q :=
  Iff.rfl

@[to_additive]
/-
**GroupSeminorm.lt_def** 是 Mathlib 中的一个定理，位于命名空间 `GroupSeminorm`。
形式化陈述：lt_def : p < q ↔ (p : E -> Real) < q
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem lt_def : p < q ↔ (p : E → ℝ) < q :=
  Iff.rfl

@[to_additive (attr := simp, norm_cast)]
/-
**GroupSeminorm.coe_le_coe** 是 Mathlib 中的一个定理，位于命名空间 `GroupSeminorm`。
形式化陈述：coe_le_coe : (p : E -> Real) <= q ↔ p <= q
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem coe_le_coe : (p : E → ℝ) ≤ q ↔ p ≤ q :=
  Iff.rfl

@[to_additive (attr := simp, norm_cast)]
/-
**GroupSeminorm.coe_lt_coe** 是 Mathlib 中的一个定理，位于命名空间 `GroupSeminorm`。
形式化陈述：coe_lt_coe : (p : E -> Real) < q ↔ p < q
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem coe_lt_coe : (p : E → ℝ) < q ↔ p < q :=
  Iff.rfl

variable (p q) (f : F →* E)

@[to_additive]
/-
**GroupSeminorm.instZeroGroupSeminorm** 是 Mathlib 中的一个实例，位于命名空间 `GroupSeminorm`。
形式化陈述：instZeroGroupSeminorm : Zero (GroupSeminorm E)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instZeroGroupSeminorm : Zero (GroupSeminorm E) :=
  ⟨{  toFun := 0
      map_one' := Pi.zero_apply _
      mul_le' := fun _ _ => (zero_add _).ge
      inv' := fun _ => rfl }⟩

@[to_additive]
/-
**GroupSeminorm.** 是 Mathlib 中的一个实例，位于命名空间 `GroupSeminorm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsZeroApply (GroupSeminorm E) E ℝ where
  zero_apply _ := rfl

@[deprecated (since := "2026-07-10")] alias _root_.GroupSeminorm.coe_zero := FunLike.coe_zero
@[deprecated (since := "2026-07-10")] alias _root_.AddGroupSeminorm.coe_zero := FunLike.coe_zero

@[deprecated (since := "2026-07-10")] protected alias _root_.GroupSeminorm.zero_apply :=
  zero_apply
@[deprecated (since := "2026-07-10")] protected alias _root_.AddGroupSeminorm.zero_apply :=
  zero_apply

@[to_additive]
/-
**GroupSeminorm.** 是 Mathlib 中的一个实例，位于命名空间 `GroupSeminorm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (GroupSeminorm E) :=
  ⟨0⟩

@[to_additive]
/-
**GroupSeminorm.** 是 Mathlib 中的一个实例，位于命名空间 `GroupSeminorm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Add (GroupSeminorm E) :=
  ⟨fun p q =>
    { toFun := fun x => p x + q x
      map_one' := by simp_rw [map_one_eq_zero p, map_one_eq_zero q, zero_add]
      mul_le' := fun _ _ =>
        (add_le_add (map_mul_le_add p _ _) <| map_mul_le_add q _ _).trans_eq <|
          add_add_add_comm _ _ _ _
      inv' := fun x => by simp_rw [map_inv_eq_map p, map_inv_eq_map q] }⟩

@[to_additive]
/-
**GroupSeminorm.** 是 Mathlib 中的一个实例，位于命名空间 `GroupSeminorm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsAddApply (GroupSeminorm E) E ℝ where
  add_apply _ _ _ := rfl

@[deprecated (since := "2026-07-10")] alias _root_.GroupSeminorm.coe_add := FunLike.coe_add
@[deprecated (since := "2026-07-10")] alias _root_.AddGroupSeminorm.coe_add := FunLike.coe_add

@[deprecated (since := "2026-07-10")] protected alias _root_.GroupSeminorm.add_apply :=
  add_apply
@[deprecated (since := "2026-07-10")] protected alias _root_.AddGroupSeminorm.add_apply :=
  add_apply

open scoped Classical in
@[to_additive]
/-
**GroupSeminorm.** 是 Mathlib 中的一个实例，位于命名空间 `GroupSeminorm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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
            refine ciSup_le fun p ↦ (map_mul_le_add p.1 x y).trans ?_
            gcongr
            all_goals
              apply le_ciSup (f := (DFunLike.coe · _) ∘ Subtype.val) ?_ p
              simpa [Set.range_comp] using Monotone.map_bddAbove (fun _ _ h' ↦ by exact h' _) h
        inv' x := by simp }
    else 0

@[to_additive]
/-
**GroupSeminorm.sSup_of_not_bddAbove** 是 Mathlib 中的一个引理，位于命名空间 `GroupSeminorm`。
形式化陈述：sSup_of_not_bddAbove {s : Set (GroupSeminorm E)} (hs : ¬BddAbove s) : sSup
 s = 0
参数：GroupSeminorm E；hs : ¬BddAbove s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma sSup_of_not_bddAbove {s : Set (GroupSeminorm E)} (hs : ¬BddAbove s) :
    sSup s = 0 := by
  simp [SupSet.sSup, hs]

@[to_additive]
/-
**GroupSeminorm.coe_sSup_apply** 是 Mathlib 中的一个引理，位于命名空间 `GroupSeminorm`。
形式化陈述：coe_sSup_apply {s : Set (GroupSeminorm E)} (hs : BddAbove s) {x : E} : ⇑(s
Sup s) x = ⨆ p : s, (p : GroupSeminorm E) x
参数：GroupSeminorm E；hs : BddAbove s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
-/
lemma coe_sSup_apply {s : Set (GroupSeminorm E)} (hs : BddAbove s) {x : E} :
    ⇑(sSup s) x = ⨆ p : s, (p : GroupSeminorm E) x := by
  simp [SupSet.sSup, hs]
  rfl

@[to_additive]
/-
**GroupSeminorm.coe_sSup_apply'** 是 Mathlib 中的一个引理，位于命名空间 `GroupSeminorm`。
形式化陈述：coe_sSup_apply' {s : Set (GroupSeminorm E)} (hs : BddAbove s) {x : E} : ⇑(
sSup s) x = sSup ((· x) '' s)
参数：GroupSeminorm E；hs : BddAbove s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `GroupSeminorm.coe_sSup_apply`：coe_sSup_apply {s : Set (GroupSeminorm E)}
 (hs : BddAbove s) {x : E} : ⇑(sSup s) x = ⨆ p : s, (p : GroupSeminorm E) x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sSup_range`：sSup_range : sSup (range f) = iSup f
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma coe_sSup_apply' {s : Set (GroupSeminorm E)} (hs : BddAbove s) {x : E} :
    ⇑(sSup s) x = sSup ((· x) '' s) := by
  rw [coe_sSup_apply hs, ← sSup_range]
  congr
  ext
  simp

@[to_additive]
/-
**GroupSeminorm.coe_iSup_apply** 是 Mathlib 中的一个引理，位于命名空间 `GroupSeminorm`。
形式化陈述：coe_iSup_apply {ι : Type*} (f : ι -> GroupSeminorm E) (h : BddAbove (range
 f)) {x : E} : ⇑(⨆ i, f i) x = ⨆ i, (f i : GroupSeminorm E) x
参数：f : ι -> GroupSeminorm E；h : BddAbove (range f)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sSup_range`：sSup_range : sSup (range f) = iSup f
· 使用引理 `GroupSeminorm.coe_sSup_apply`：coe_sSup_apply {s : Set (GroupSeminorm E)}
 (hs : BddAbove s) {x : E} : ⇑(sSup s) x = ⨆ p : s, (p : GroupSeminorm E) x
· 使用定理 `Function.Surjective.iSup_congr`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : So
rt u_5} [inst : SupSet α] {f : ι → α} {g : ι' → α} (h : ι → ι'),   Function.Surj
ective h → (∀ (x : ι…
· 使用定理 `Set.rangeFactorization_surjective`：∀ {α : Type u} {ι : Sort u_1} {f : ι 
→ α}, Function.Surjective (Set.rangeFactorization f)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma coe_iSup_apply {ι : Type*} (f : ι → GroupSeminorm E) (h : BddAbove (range f)) {x : E} :
    ⇑(⨆ i, f i) x = ⨆ i, (f i : GroupSeminorm E) x := by
  rw [← sSup_range, coe_sSup_apply h]
  exact (Set.rangeFactorization_surjective.iSup_congr _ (by simp)) |>.symm

@[to_additive]
/-
**GroupSeminorm.** 是 Mathlib 中的一个实例，位于命名空间 `GroupSeminorm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Max (GroupSeminorm E) :=
  ⟨fun p q =>
    { toFun := p ⊔ q
      map_one' := by
        rw [Pi.sup_apply, ← map_one_eq_zero p, sup_eq_left, map_one_eq_zero p, map_one_eq_zero q]
      mul_le' := fun x y =>
        sup_le ((map_mul_le_add p x y).trans <| add_le_add le_sup_left le_sup_left)
          ((map_mul_le_add q x y).trans <| add_le_add le_sup_right le_sup_right)
      inv' := fun x => by rw [Pi.sup_apply, Pi.sup_apply, map_inv_eq_map p, map_inv_eq_map q] }⟩

@[to_additive (attr := simp, norm_cast)]
/-
**GroupSeminorm.coe_sup** 是 Mathlib 中的一个定理，位于命名空间 `GroupSeminorm`。
形式化陈述：coe_sup : ⇑(p ⊔ q) = ⇑p ⊔ ⇑q
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_sup : ⇑(p ⊔ q) = ⇑p ⊔ ⇑q :=
  rfl

@[to_additive (attr := simp)]
/-
**GroupSeminorm.sup_apply** 是 Mathlib 中的一个定理，位于命名空间 `GroupSeminorm`。
形式化陈述：sup_apply (x : E) : (p ⊔ q) x = p x ⊔ q x
参数：x : E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sup_apply (x : E) : (p ⊔ q) x = p x ⊔ q x :=
  rfl

@[to_additive]
/-
**GroupSeminorm.semilatticeSup** 是 Mathlib 中的一个实例，位于命名空间 `GroupSeminorm`。
形式化陈述：semilatticeSup : SemilatticeSup (GroupSeminorm E)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `GroupSeminorm.coe_sup`：coe_sup : ⇑(p ⊔ q) = ⇑p ⊔ ⇑q
-/
instance semilatticeSup : SemilatticeSup (GroupSeminorm E) :=
  DFunLike.coe_injective.semilatticeSup _ .rfl .rfl coe_sup

/-- Composition of a group seminorm with a monoid homomorphism as a group seminorm. -/
@[to_additive /-- Composition of an additive group seminorm with an additive monoid homomorphism as
an additive group seminorm. -/]
/-
**GroupSeminorm.comp** 是 Mathlib 中的一个定义，位于命名空间 `GroupSeminorm`。
形式化陈述：comp (p : GroupSeminorm E) (f : F ->* E) : GroupSeminorm F where toFun x
参数：p : GroupSeminorm E；f : F ->* E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def comp (p : GroupSeminorm E) (f : F →* E) : GroupSeminorm F where
  toFun x := p (f x)
  map_one' := by simp_rw [f.map_one, map_one_eq_zero p]
  mul_le' _ _ := (congr_arg p <| f.map_mul _ _).trans_le <| map_mul_le_add p _ _
  inv' x := by simp_rw [map_inv, map_inv_eq_map p]

@[to_additive (attr := simp)]
/-
**GroupSeminorm.coe_comp** 是 Mathlib 中的一个定理，位于命名空间 `GroupSeminorm`。
形式化陈述：coe_comp : ⇑(p.comp f) = p ∘ f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_comp : ⇑(p.comp f) = p ∘ f :=
  rfl

@[to_additive (attr := simp)]
/-
**GroupSeminorm.comp_apply** 是 Mathlib 中的一个定理，位于命名空间 `GroupSeminorm`。
形式化陈述：comp_apply (x : F) : (p.comp f) x = p (f x)
参数：x : F。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_apply (x : F) : (p.comp f) x = p (f x) :=
  rfl

@[to_additive (attr := simp)]
/-
**GroupSeminorm.comp_id** 是 Mathlib 中的一个定理，位于命名空间 `GroupSeminorm`。
形式化陈述：comp_id : p.comp (MonoidHom.id _) = p
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GroupSeminorm.ext`：ext : (forall x, p x = q x) -> p = q
-/
theorem comp_id : p.comp (MonoidHom.id _) = p :=
  ext fun _ => rfl

@[to_additive (attr := simp)]
/-
**GroupSeminorm.comp_zero** 是 Mathlib 中的一个定理，位于命名空间 `GroupSeminorm`。
形式化陈述：comp_zero : p.comp (1 : F ->* E) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GroupSeminorm.ext`：ext : (forall x, p x = q x) -> p = q
· 使用定理 `GroupSeminormClass.map_one_eq_zero`：∀ {F : Type u_7} {α : outParam (Type
 u_8)} {β : outParam (Type u_9)} {inst : Group α} {inst_1 : AddCommMonoid β}   {
inst_2 : PartialOrder β}…
-/
theorem comp_zero : p.comp (1 : F →* E) = 0 :=
  ext fun _ => map_one_eq_zero p

@[to_additive (attr := simp)]
/-
**GroupSeminorm.zero_comp** 是 Mathlib 中的一个定理，位于命名空间 `GroupSeminorm`。
形式化陈述：zero_comp : (0 : GroupSeminorm E).comp f = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GroupSeminorm.ext`：ext : (forall x, p x = q x) -> p = q
-/
theorem zero_comp : (0 : GroupSeminorm E).comp f = 0 :=
  ext fun _ => rfl

@[to_additive]
/-
**GroupSeminorm.comp_assoc** 是 Mathlib 中的一个定理，位于命名空间 `GroupSeminorm`。
形式化陈述：comp_assoc (g : F ->* E) (f : G ->* F) : p.comp (g.comp f) = (p.comp g).co
mp f
参数：g : F ->* E；f : G ->* F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GroupSeminorm.ext`：ext : (forall x, p x = q x) -> p = q
-/
theorem comp_assoc (g : F →* E) (f : G →* F) : p.comp (g.comp f) = (p.comp g).comp f :=
  ext fun _ => rfl

@[to_additive]
/-
**GroupSeminorm.add_comp** 是 Mathlib 中的一个定理，位于命名空间 `GroupSeminorm`。
形式化陈述：add_comp (f : F ->* E) : (p + q).comp f = p.comp f + q.comp f
参数：f : F ->* E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GroupSeminorm.ext`：ext : (forall x, p x = q x) -> p = q
-/
theorem add_comp (f : F →* E) : (p + q).comp f = p.comp f + q.comp f :=
  ext fun _ => rfl

variable {p q}

@[to_additive]
/-
**GroupSeminorm.comp_mono** 是 Mathlib 中的一个定理，位于命名空间 `GroupSeminorm`。
形式化陈述：comp_mono (hp : p <= q) : p.comp f <= q.comp f
参数：hp : p <= q。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_mono (hp : p ≤ q) : p.comp f ≤ q.comp f := fun _ => hp _

end Group

section CommGroup

variable [CommGroup E] [CommGroup F] (p q : GroupSeminorm E) (x : E)

@[to_additive]
/-
**GroupSeminorm.comp_mul_le** 是 Mathlib 中的一个定理，位于命名空间 `GroupSeminorm`。
形式化陈述：comp_mul_le (f g : F ->* E) : p.comp (f * g) <= p.comp f + p.comp g
参数：f g : F ->* E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulLEAddHomClass.map_mul_le_add`：∀ {F : Type u_7} {α : outParam (Type u_
8)} {β : outParam (Type u_9)} {inst : Mul α} {inst_1 : Add β} {inst_2 : LE β}   
{inst_3 : FunLike F α…
· 使用定理 `GroupSeminormClass.toMulLEAddHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : Group α} {inst_1 : AddCommMonoid β} 
  {inst_2 : PartialOrder β}…
-/
theorem comp_mul_le (f g : F →* E) : p.comp (f * g) ≤ p.comp f + p.comp g := fun _ =>
  map_mul_le_add p _ _

@[to_additive]
/-
**GroupSeminorm.mul_bddBelow_range_add** 是 Mathlib 中的一个定理，位于命名空间 `GroupSeminorm`
。
形式化陈述：mul_bddBelow_range_add {p q : GroupSeminorm E} {x : E} : BddBelow (range f
un y => p y + q (x / y))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `add_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preorder 
α] [AddLeftMono α] {a b : α}, 0 ≤ a → 0 ≤ b → 0 ≤ a + b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `NonnegHomClass.apply_nonneg`：∀ {F : Type u_7} {α : outParam (Type u_8)} 
{β : outParam (Type u_9)} {inst : Zero β} {inst_1 : LE β}   {inst_2 : FunLike F 
α β} [self : Nonn…
· 使用定理 `GroupSeminormClass.toNonnegHomClass`：∀ {F : Type u_2} {α : Type u_3} {β 
: Type u_4} [inst : FunLike F α β] [inst_1 : Group α] [inst_2 : AddCommMonoid β]
   [inst_3 : LinearOrder …
-/
theorem mul_bddBelow_range_add {p q : GroupSeminorm E} {x : E} :
    BddBelow (range fun y => p y + q (x / y)) :=
  ⟨0, by
    rintro _ ⟨x, rfl⟩
    dsimp
    positivity⟩

@[to_additive]
/-
**GroupSeminorm.** 是 Mathlib 中的一个实例，位于命名空间 `GroupSeminorm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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
          rw [mul_div_mul_comm, add_add_add_comm]
          exact add_le_add (map_mul_le_add p _ _) (map_mul_le_add q _ _)
      inv' := fun x =>
        (inv_surjective.iInf_comp _).symm.trans <| by
          simp_rw [map_inv_eq_map p, ← inv_div', map_inv_eq_map q] }⟩

@[to_additive (attr := simp)]
/-
**GroupSeminorm.inf_apply** 是 Mathlib 中的一个定理，位于命名空间 `GroupSeminorm`。
形式化陈述：inf_apply : (p ⊓ q) x = ⨅ y, p y + q (x / y)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inf_apply : (p ⊓ q) x = ⨅ y, p y + q (x / y) :=
  rfl

@[to_additive]
/-
**GroupSeminorm.** 是 Mathlib 中的一个实例，位于命名空间 `GroupSeminorm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : Lattice (GroupSeminorm E) :=
  { GroupSeminorm.semilatticeSup with
    inf := (· ⊓ ·)
    inf_le_left := fun p q x =>
      ciInf_le_of_le mul_bddBelow_range_add x <| by rw [div_self', map_one_eq_zero q, add_zero]
    inf_le_right := fun p q x =>
      ciInf_le_of_le mul_bddBelow_range_add (1 : E) <| by
        simpa only [div_one x, map_one_eq_zero p, zero_add (q x)] using le_rfl
    le_inf := fun a _ _ hb hc _ =>
      le_ciInf fun _ => (le_map_add_map_div a _ _).trans <| add_le_add (hb _) (hc _) }

end CommGroup

end GroupSeminorm

/- TODO: All the following ought to be automated using `to_additive`. The problem is that it doesn't
see that `SMul R ℝ` should be fixed because `ℝ` is fixed. -/
namespace AddGroupSeminorm

variable [AddGroup E] [SMul R ℝ] [SMul R ℝ≥0] [IsScalarTower R ℝ≥0 ℝ]

/-
**AddGroupSeminorm.toOne** 是 Mathlib 中的一个实例，位于命名空间 `AddGroupSeminorm`。
形式化陈述：toOne [DecidableEq E] : One (AddGroupSeminorm E)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance toOne [DecidableEq E] : One (AddGroupSeminorm E) :=
  ⟨{  toFun := fun x => if x = 0 then 0 else 1
      map_zero' := if_pos rfl
      add_le' := fun x y => by
        by_cases hx : x = 0
        · rw [if_pos hx, hx, zero_add, zero_add]
        · rw [if_neg hx]
          refine le_add_of_le_of_nonneg ?_ ?_ <;> split_ifs <;> norm_num
      neg' := fun x => by simp_rw [neg_eq_zero] }⟩

@[simp]
/-
**AddGroupSeminorm.apply_one** 是 Mathlib 中的一个定理，位于命名空间 `AddGroupSeminorm`。
形式化陈述：apply_one [DecidableEq E] (x : E) : (1 : AddGroupSeminorm E) x = if x = 0 
then 0 else 1
参数：x : E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem apply_one [DecidableEq E] (x : E) : (1 : AddGroupSeminorm E) x = if x = 0 then 0 else 1 :=
  rfl

/-- Any action on `ℝ` which factors through `ℝ≥0` applies to an `AddGroupSeminorm`. -/
/-
**AddGroupSeminorm.toSMul** 是 Mathlib 中的一个实例，位于命名空间 `AddGroupSeminorm`。
形式化陈述：toSMul : SMul R (AddGroupSeminorm E)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any action on `ℝ` which factors through `ℝ≥0` applies to an `AddGroupSeminorm`.
-/
instance toSMul : SMul R (AddGroupSeminorm E) :=
  ⟨fun r p =>
    { toFun := fun x => r • p x
      map_zero' := by
        simp only [← smul_one_smul ℝ≥0 r (_ : ℝ), NNReal.smul_def, smul_eq_mul, map_zero, mul_zero]
      add_le' := fun _ _ => by
        simp only [← smul_one_smul ℝ≥0 r (_ : ℝ), NNReal.smul_def, smul_eq_mul, ← mul_add]
        gcongr
        apply map_add_le_add
      neg' := fun x => by simp_rw [map_neg_eq_map] }⟩
/-
**AddGroupSeminorm.** 是 Mathlib 中的一个实例，位于命名空间 `AddGroupSeminorm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsSMulApply R (AddGroupSeminorm E) E ℝ where
  smul_apply _ _ _ := rfl

@[deprecated (since := "2026-07-10")] alias coe_smul := FunLike.coe_smul

@[deprecated (since := "2026-07-10")] protected alias smul_apply := smul_apply
/-
**AddGroupSeminorm.isScalarTower** 是 Mathlib 中的一个实例，位于命名空间 `AddGroupSeminorm`。
形式化陈述：isScalarTower [SMul R' Real] [SMul R' Real>=0] [IsScalarTower R' Real>=0 R
eal] [SMul R R'] [IsScalarTower R R' Real] : IsScalarTower R R' (AddGroupSeminor
m E)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `FunLike.isScalarTower`：∀ {M : Type u_1} {M' : Type u_2} {F : Type u_3} {
α : Type u_4} {β : Type u_5} [i : FunLike F α β] [inst : SMul M β]   [inst_1 : S
Mul M' β] […
· 使用定理 `AddGroupSeminorm.instIsSMulApplyReal`：∀ {R : Type u_1} {E : Type u_3} [i
nst : AddGroup E] [inst_1 : SMul R ℝ] [inst_2 : SMul R NNReal]   [inst_3 : IsSca
larTower R NNReal ℝ], IsSM…
-/
instance isScalarTower [SMul R' ℝ] [SMul R' ℝ≥0] [IsScalarTower R' ℝ≥0 ℝ] [SMul R R']
    [IsScalarTower R R' ℝ] : IsScalarTower R R' (AddGroupSeminorm E) :=
  FunLike.isScalarTower
/-
**AddGroupSeminorm.** 是 Mathlib 中的一个实例，位于命名空间 `AddGroupSeminorm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddCommMonoid (AddGroupSeminorm E) := fast_instance% FunLike.addCommMonoid
/-
**AddGroupSeminorm.smul_sup** 是 Mathlib 中的一个定理，位于命名空间 `AddGroupSeminorm`。
形式化陈述：smul_sup (r : R) (p q : AddGroupSeminorm E) : r • (p ⊔ q) = r • p ⊔ r • q
参数：r : R；p q : AddGroupSeminorm E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `smul_one_smul`：smul_one_smul {M} (N) [Monoid N] [SMul M N] [MulAction N 
α] [SMul M α] [IsScalarTower M N α] (x : M) (y : α) : (x • (1 : N)) • y = x • y
· 使用定理 `mul_max_of_nonneg`：mul_max_of_nonneg [PosMulMono R] (b c : R) (ha : 0 <=
 a) : a * max b c = max (a * b) (a * c)
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `NNReal.coe_nonneg`：∀ (r : NNReal), 0 ≤ ↑r
· 使用定理 `AddGroupSeminorm.ext`：∀ {E : Type u_3} [inst : AddGroup E] {p q : AddGro
upSeminorm E}, (∀ (x : E), p x = q x) → p = q
-/
theorem smul_sup (r : R) (p q : AddGroupSeminorm E) : r • (p ⊔ q) = r • p ⊔ r • q :=
  have Real.smul_max : ∀ x y : ℝ, r • max x y = max (r • x) (r • y) := fun x y => by
    simpa only [← smul_eq_mul, ← NNReal.smul_def, smul_one_smul ℝ≥0 r (_ : ℝ)] using
      mul_max_of_nonneg x y (r • (1 : ℝ≥0) : ℝ≥0).coe_nonneg
  ext fun _ => Real.smul_max _ _

end AddGroupSeminorm

namespace NonarchAddGroupSeminorm

section AddGroup

variable [AddGroup E] {p q : NonarchAddGroupSeminorm E}

/-
**NonarchAddGroupSeminorm.funLike** 是 Mathlib 中的一个实例，位于命名空间 `NonarchAddGroupSemi
norm`。
形式化陈述：funLike : FunLike (NonarchAddGroupSeminorm E) E Real where coe f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance funLike : FunLike (NonarchAddGroupSeminorm E) E ℝ where
  coe f := f.toFun
  coe_injective f g h := by obtain ⟨⟨_, _⟩, _, _⟩ := f; cases g; congr
/-
**NonarchAddGroupSeminorm.nonarchAddGroupSeminormClass** 是 Mathlib 中的一个实例，位于命名空间
 `NonarchAddGroupSeminorm`。
形式化陈述：nonarchAddGroupSeminormClass : NonarchAddGroupSeminormClass (NonarchAddGro
upSeminorm E) E where map_add_le_max f
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `NonarchAddGroupSeminorm.add_le_max'`：∀ {G : Type u_6} [inst : AddGroup G
] (self : NonarchAddGroupSeminorm G) (r s : G),   self.toFun (r + s) ≤ max (self
.toFun r) (self.toFun s)
· 使用定理 `ZeroHom.map_zero'`：∀ {M : Type u_10} {N : Type u_11} [inst : Zero M] [in
st_1 : Zero N] (self : ZeroHom M N), self.toFun 0 = 0
· 使用定理 `NonarchAddGroupSeminorm.neg'`：∀ {G : Type u_6} [inst : AddGroup G] (self
 : NonarchAddGroupSeminorm G) (r : G), self.toFun (-r) = self.toFun r
-/
instance nonarchAddGroupSeminormClass :
    NonarchAddGroupSeminormClass (NonarchAddGroupSeminorm E) E where
  map_add_le_max f := f.add_le_max'
  map_zero f := f.map_zero'
  map_neg_eq_map' f := f.neg'

@[simp]
/-
**NonarchAddGroupSeminorm.toZeroHom_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `NonarchAdd
GroupSeminorm`。
形式化陈述：toZeroHom_eq_coe : ⇑p.toZeroHom = p
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toZeroHom_eq_coe : ⇑p.toZeroHom = p := by
  rfl

@[ext]
/-
**NonarchAddGroupSeminorm.ext** 是 Mathlib 中的一个定理，位于命名空间 `NonarchAddGroupSeminorm
`。
形式化陈述：ext : (forall x, p x = q x) -> p = q
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem ext : (∀ x, p x = q x) → p = q :=
  DFunLike.ext p q
/-
**NonarchAddGroupSeminorm.** 是 Mathlib 中的一个实例，位于命名空间 `NonarchAddGroupSeminorm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : PartialOrder (NonarchAddGroupSeminorm E) :=
  PartialOrder.lift _ DFunLike.coe_injective
/-
**NonarchAddGroupSeminorm.le_def** 是 Mathlib 中的一个定理，位于命名空间 `NonarchAddGroupSemin
orm`。
形式化陈述：le_def : p <= q ↔ (p : E -> Real) <= q
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem le_def : p ≤ q ↔ (p : E → ℝ) ≤ q :=
  Iff.rfl
/-
**NonarchAddGroupSeminorm.lt_def** 是 Mathlib 中的一个定理，位于命名空间 `NonarchAddGroupSemin
orm`。
形式化陈述：lt_def : p < q ↔ (p : E -> Real) < q
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem lt_def : p < q ↔ (p : E → ℝ) < q :=
  Iff.rfl

@[simp, norm_cast]
/-
**NonarchAddGroupSeminorm.coe_le_coe** 是 Mathlib 中的一个定理，位于命名空间 `NonarchAddGroupS
eminorm`。
形式化陈述：coe_le_coe : (p : E -> Real) <= q ↔ p <= q
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem coe_le_coe : (p : E → ℝ) ≤ q ↔ p ≤ q :=
  Iff.rfl

@[simp, norm_cast]
/-
**NonarchAddGroupSeminorm.coe_lt_coe** 是 Mathlib 中的一个定理，位于命名空间 `NonarchAddGroupS
eminorm`。
形式化陈述：coe_lt_coe : (p : E -> Real) < q ↔ p < q
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem coe_lt_coe : (p : E → ℝ) < q ↔ p < q :=
  Iff.rfl

variable (p q)
/-
**NonarchAddGroupSeminorm.** 是 Mathlib 中的一个实例，位于命名空间 `NonarchAddGroupSeminorm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Zero (NonarchAddGroupSeminorm E) :=
  ⟨{  toFun := 0
      map_zero' := Pi.zero_apply _
      add_le_max' := fun r s => by simp only [Pi.zero_apply]; rw [max_eq_right]; rfl
      neg' := fun _ => rfl }⟩
/-
**NonarchAddGroupSeminorm.** 是 Mathlib 中的一个实例，位于命名空间 `NonarchAddGroupSeminorm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsZeroApply (NonarchAddGroupSeminorm E) E ℝ where
  zero_apply _ := rfl

@[deprecated (since := "2026-07-10")] alias coe_zero := FunLike.coe_zero

@[deprecated (since := "2026-07-10")] protected alias zero_apply := zero_apply
/-
**NonarchAddGroupSeminorm.** 是 Mathlib 中的一个实例，位于命名空间 `NonarchAddGroupSeminorm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (NonarchAddGroupSeminorm E) :=
  ⟨0⟩

open scoped Classical in
/-
**NonarchAddGroupSeminorm.** 是 Mathlib 中的一个实例，位于命名空间 `NonarchAddGroupSeminorm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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
            refine ciSup_le fun p ↦ (map_add_le_max p.1 x y).trans ?_
            gcongr
            all_goals
              apply le_ciSup (f := (DFunLike.coe · _) ∘ Subtype.val) ?_ p
              simpa [Set.range_comp] using Monotone.map_bddAbove (fun _ _ h' ↦ by exact h' _) h
        neg' := by simp }
    else 0
/-
**NonarchAddGroupSeminorm.sSup_of_not_bddAbove** 是 Mathlib 中的一个引理，位于命名空间 `Nonarc
hAddGroupSeminorm`。
形式化陈述：sSup_of_not_bddAbove {s : Set (NonarchAddGroupSeminorm E)} (hs : ¬BddAbove
 s) : sSup s = 0
参数：NonarchAddGroupSeminorm E；hs : ¬BddAbove s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma sSup_of_not_bddAbove {s : Set (NonarchAddGroupSeminorm E)} (hs : ¬BddAbove s) :
    sSup s = 0 := by
  simp [SupSet.sSup, hs]
/-
**NonarchAddGroupSeminorm.coe_sSup_apply** 是 Mathlib 中的一个引理，位于命名空间 `NonarchAddGr
oupSeminorm`。
形式化陈述：coe_sSup_apply {s : Set (NonarchAddGroupSeminorm E)} (hs : BddAbove s) {x 
: E} : ⇑(sSup s) x = ⨆ p : s, (p : NonarchAddGroupSeminorm E) x
参数：NonarchAddGroupSeminorm E；hs : BddAbove s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
-/
lemma coe_sSup_apply {s : Set (NonarchAddGroupSeminorm E)} (hs : BddAbove s) {x : E} :
    ⇑(sSup s) x = ⨆ p : s, (p : NonarchAddGroupSeminorm E) x := by
  simp [SupSet.sSup, hs]
  rfl
/-
**NonarchAddGroupSeminorm.coe_sSup_apply'** 是 Mathlib 中的一个引理，位于命名空间 `NonarchAddG
roupSeminorm`。
形式化陈述：coe_sSup_apply' {s : Set (NonarchAddGroupSeminorm E)} (hs : BddAbove s) {x
 : E} : ⇑(sSup s) x = sSup ((· x) '' s)
参数：NonarchAddGroupSeminorm E；hs : BddAbove s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `NonarchAddGroupSeminorm.coe_sSup_apply`：coe_sSup_apply {s : Set (Nonarch
AddGroupSeminorm E)} (hs : BddAbove s) {x : E} : ⇑(sSup s) x = ⨆ p : s, (p : Non
archAddGroupSeminorm E) x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sSup_range`：sSup_range : sSup (range f) = iSup f
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma coe_sSup_apply' {s : Set (NonarchAddGroupSeminorm E)} (hs : BddAbove s) {x : E} :
    ⇑(sSup s) x = sSup ((· x) '' s) := by
  rw [coe_sSup_apply hs, ← sSup_range]
  congr
  ext
  simp
/-
**NonarchAddGroupSeminorm.coe_iSup_apply** 是 Mathlib 中的一个引理，位于命名空间 `NonarchAddGr
oupSeminorm`。
形式化陈述：coe_iSup_apply {ι : Type*} (f : ι -> NonarchAddGroupSeminorm E) (h : BddAb
ove (range f)) {x : E} : ⇑(⨆ i, f i) x = ⨆ i, (f i : NonarchAddGroupSeminorm E) 
x
参数：f : ι -> NonarchAddGroupSeminorm E；h : BddAbove (range f)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sSup_range`：sSup_range : sSup (range f) = iSup f
· 使用引理 `NonarchAddGroupSeminorm.coe_sSup_apply`：coe_sSup_apply {s : Set (Nonarch
AddGroupSeminorm E)} (hs : BddAbove s) {x : E} : ⇑(sSup s) x = ⨆ p : s, (p : Non
archAddGroupSeminorm E) x
· 使用定理 `Function.Surjective.iSup_congr`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : So
rt u_5} [inst : SupSet α] {f : ι → α} {g : ι' → α} (h : ι → ι'),   Function.Surj
ective h → (∀ (x : ι…
· 使用定理 `Set.rangeFactorization_surjective`：∀ {α : Type u} {ι : Sort u_1} {f : ι 
→ α}, Function.Surjective (Set.rangeFactorization f)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma coe_iSup_apply {ι : Type*} (f : ι → NonarchAddGroupSeminorm E) (h : BddAbove (range f))
    {x : E} : ⇑(⨆ i, f i) x = ⨆ i, (f i : NonarchAddGroupSeminorm E) x := by
  rw [← sSup_range, coe_sSup_apply h]
  exact (Set.rangeFactorization_surjective.iSup_congr _ (by simp)) |>.symm
/-
**NonarchAddGroupSeminorm.** 是 Mathlib 中的一个实例，位于命名空间 `NonarchAddGroupSeminorm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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
/-
**NonarchAddGroupSeminorm.coe_sup** 是 Mathlib 中的一个定理，位于命名空间 `NonarchAddGroupSemi
norm`。
形式化陈述：coe_sup : ⇑(p ⊔ q) = ⇑p ⊔ ⇑q
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_sup : ⇑(p ⊔ q) = ⇑p ⊔ ⇑q :=
  rfl

@[simp]
/-
**NonarchAddGroupSeminorm.sup_apply** 是 Mathlib 中的一个定理，位于命名空间 `NonarchAddGroupSe
minorm`。
形式化陈述：sup_apply (x : E) : (p ⊔ q) x = p x ⊔ q x
参数：x : E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sup_apply (x : E) : (p ⊔ q) x = p x ⊔ q x :=
  rfl
/-
**NonarchAddGroupSeminorm.** 是 Mathlib 中的一个实例，位于命名空间 `NonarchAddGroupSeminorm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : SemilatticeSup (NonarchAddGroupSeminorm E) :=
  DFunLike.coe_injective.semilatticeSup _ .rfl .rfl coe_sup

end AddGroup

section AddCommGroup

variable [AddCommGroup E]

/-
**NonarchAddGroupSeminorm.add_bddBelow_range_add** 是 Mathlib 中的一个定理，位于命名空间 `Nona
rchAddGroupSeminorm`。
形式化陈述：add_bddBelow_range_add {p q : NonarchAddGroupSeminorm E} {x : E} : BddBelo
w (range fun y => p y + q (x - y))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `add_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preorder 
α] [AddLeftMono α] {a b : α}, 0 ≤ a → 0 ≤ b → 0 ≤ a + b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `NonnegHomClass.apply_nonneg`：∀ {F : Type u_7} {α : outParam (Type u_8)} 
{β : outParam (Type u_9)} {inst : Zero β} {inst_1 : LE β}   {inst_2 : FunLike F 
α β} [self : Nonn…
· 使用定理 `AddGroupSeminormClass.toNonnegHomClass`：∀ {F : Type u_2} {α : Type u_3} 
{β : Type u_4} [inst : FunLike F α β] [inst_1 : AddGroup α] [inst_2 : AddCommMon
oid β]   [inst_3 : LinearOrd…
· 使用定理 `NonarchAddGroupSeminormClass.toAddGroupSeminormClass`：∀ {E : Type u_3} {
F : Type u_4} [inst : FunLike F E ℝ] [inst_1 : AddGroup E] [NonarchAddGroupSemin
ormClass F E],   AddGroupSeminormClass F E…
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

variable [Group E] [SMul R ℝ] [SMul R ℝ≥0] [IsScalarTower R ℝ≥0 ℝ]

/-
**GroupSeminorm.toOne** 是 Mathlib 中的一个实例，位于命名空间 `GroupSeminorm`。
形式化陈述：toOne [DecidableEq E] : One (GroupSeminorm E)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance toOne [DecidableEq E] : One (GroupSeminorm E) :=
  ⟨{  toFun := fun x => if x = 1 then 0 else 1
      map_one' := if_pos rfl
      mul_le' := fun x y => by
        by_cases hx : x = 1
        · rw [if_pos hx, hx, one_mul, zero_add]
        · rw [if_neg hx]
          refine le_add_of_le_of_nonneg ?_ ?_ <;> split_ifs <;> norm_num
      inv' := fun x => by simp_rw [inv_eq_one] }⟩

@[simp]
/-
**GroupSeminorm.apply_one** 是 Mathlib 中的一个定理，位于命名空间 `GroupSeminorm`。
形式化陈述：apply_one [DecidableEq E] (x : E) : (1 : GroupSeminorm E) x = if x = 1 the
n 0 else 1
参数：x : E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem apply_one [DecidableEq E] (x : E) : (1 : GroupSeminorm E) x = if x = 1 then 0 else 1 :=
  rfl

/-- Any action on `ℝ` which factors through `ℝ≥0` applies to an `AddGroupSeminorm`. -/
/-
**GroupSeminorm.** 是 Mathlib 中的一个实例，位于命名空间 `GroupSeminorm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any action on `ℝ` which factors through `ℝ≥0` applies to an `AddGroupSeminorm`.
-/
instance : SMul R (GroupSeminorm E) :=
  ⟨fun r p =>
    { toFun := fun x => r • p x
      map_one' := by
        simp only [← smul_one_smul ℝ≥0 r (_ : ℝ), NNReal.smul_def, smul_eq_mul, map_one_eq_zero p,
          mul_zero]
      mul_le' := fun _ _ => by
        simp only [← smul_one_smul ℝ≥0 r (_ : ℝ), NNReal.smul_def, smul_eq_mul, ← mul_add]
        gcongr
        apply map_mul_le_add
      inv' := fun x => by simp_rw [map_inv_eq_map p] }⟩
/-
**GroupSeminorm.** 是 Mathlib 中的一个实例，位于命名空间 `GroupSeminorm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsSMulApply R (GroupSeminorm E) E ℝ where
  smul_apply _ _ _ := rfl

@[deprecated (since := "2026-07-10")] alias coe_smul := FunLike.coe_smul

@[deprecated (since := "2026-07-10")] protected alias smul_apply := smul_apply
/-
**GroupSeminorm.** 是 Mathlib 中的一个实例，位于命名空间 `GroupSeminorm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMul R' ℝ] [SMul R' ℝ≥0] [IsScalarTower R' ℝ≥0 ℝ] [SMul R R'] [IsScalarTower R R' ℝ] :
    IsScalarTower R R' (GroupSeminorm E) :=
  FunLike.isScalarTower
/-
**GroupSeminorm.** 是 Mathlib 中的一个实例，位于命名空间 `GroupSeminorm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddCommMonoid (GroupSeminorm E) := fast_instance% FunLike.addCommMonoid
/-
**GroupSeminorm.smul_sup** 是 Mathlib 中的一个定理，位于命名空间 `GroupSeminorm`。
形式化陈述：smul_sup (r : R) (p q : GroupSeminorm E) : r • (p ⊔ q) = r • p ⊔ r • q
参数：r : R；p q : GroupSeminorm E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `smul_one_smul`：smul_one_smul {M} (N) [Monoid N] [SMul M N] [MulAction N 
α] [SMul M α] [IsScalarTower M N α] (x : M) (y : α) : (x • (1 : N)) • y = x • y
· 使用定理 `mul_max_of_nonneg`：mul_max_of_nonneg [PosMulMono R] (b c : R) (ha : 0 <=
 a) : a * max b c = max (a * b) (a * c)
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `NNReal.coe_nonneg`：∀ (r : NNReal), 0 ≤ ↑r
· 使用定理 `GroupSeminorm.ext`：ext : (forall x, p x = q x) -> p = q
-/
theorem smul_sup (r : R) (p q : GroupSeminorm E) : r • (p ⊔ q) = r • p ⊔ r • q :=
  have Real.smul_max : ∀ x y : ℝ, r • max x y = max (r • x) (r • y) := fun x y => by
    simpa only [← smul_eq_mul, ← NNReal.smul_def, smul_one_smul ℝ≥0 r (_ : ℝ)] using
      mul_max_of_nonneg x y (r • (1 : ℝ≥0) : ℝ≥0).coe_nonneg
  ext fun _ => Real.smul_max _ _

end GroupSeminorm

namespace NonarchAddGroupSeminorm

variable [AddGroup E] [SMul R ℝ] [SMul R ℝ≥0] [IsScalarTower R ℝ≥0 ℝ]

/-
**NonarchAddGroupSeminorm.** 是 Mathlib 中的一个实例，位于命名空间 `NonarchAddGroupSeminorm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DecidableEq E] : One (NonarchAddGroupSeminorm E) :=
  ⟨{  toFun := fun x => if x = 0 then 0 else 1
      map_zero' := if_pos rfl
      add_le_max' := fun x y => by
        by_cases hx : x = 0
        · simp_rw [if_pos hx, hx, zero_add]
          exact le_max_of_le_right (le_refl _)
        · simp_rw [if_neg hx]
          split_ifs <;> simp
      neg' := fun x => by simp_rw [neg_eq_zero] }⟩

@[simp]
/-
**NonarchAddGroupSeminorm.apply_one** 是 Mathlib 中的一个定理，位于命名空间 `NonarchAddGroupSe
minorm`。
形式化陈述：apply_one [DecidableEq E] (x : E) : (1 : NonarchAddGroupSeminorm E) x = if
 x = 0 then 0 else 1
参数：x : E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem apply_one [DecidableEq E] (x : E) :
    (1 : NonarchAddGroupSeminorm E) x = if x = 0 then 0 else 1 :=
  rfl

/-- Any action on `ℝ` which factors through `ℝ≥0` applies to a `NonarchAddGroupSeminorm`. -/
/-
**NonarchAddGroupSeminorm.** 是 Mathlib 中的一个实例，位于命名空间 `NonarchAddGroupSeminorm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any action on `ℝ` which factors through `ℝ≥0` applies to a `NonarchAddGroupSemin
orm`.
-/
instance : SMul R (NonarchAddGroupSeminorm E) :=
  ⟨fun r p =>
    { toFun := fun x => r • p x
      map_zero' := by
        simp only [← smul_one_smul ℝ≥0 r (_ : ℝ), NNReal.smul_def, smul_eq_mul, map_zero p,
          mul_zero]
      add_le_max' := fun x y => by
        simp only [← smul_one_smul ℝ≥0 r (_ : ℝ), NNReal.smul_def, smul_eq_mul, ←
          mul_max_of_nonneg _ _ NNReal.zero_le_coe]
        gcongr
        apply map_add_le_max
      neg' := fun x => by simp_rw [map_neg_eq_map p] }⟩
/-
**NonarchAddGroupSeminorm.** 是 Mathlib 中的一个实例，位于命名空间 `NonarchAddGroupSeminorm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsSMulApply R (NonarchAddGroupSeminorm E) E ℝ where
  smul_apply _ _ _ := rfl

@[deprecated (since := "2026-07-10")] alias coe_smul := FunLike.coe_smul

@[deprecated (since := "2026-07-10")] protected alias smul_apply := smul_apply
/-
**NonarchAddGroupSeminorm.** 是 Mathlib 中的一个实例，位于命名空间 `NonarchAddGroupSeminorm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMul R' ℝ] [SMul R' ℝ≥0] [IsScalarTower R' ℝ≥0 ℝ] [SMul R R'] [IsScalarTower R R' ℝ] :
    IsScalarTower R R' (NonarchAddGroupSeminorm E) := FunLike.isScalarTower
/-
**NonarchAddGroupSeminorm.smul_sup** 是 Mathlib 中的一个定理，位于命名空间 `NonarchAddGroupSem
inorm`。
形式化陈述：smul_sup (r : R) (p q : NonarchAddGroupSeminorm E) : r • (p ⊔ q) = r • p ⊔
 r • q
参数：r : R；p q : NonarchAddGroupSeminorm E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `smul_one_smul`：smul_one_smul {M} (N) [Monoid N] [SMul M N] [MulAction N 
α] [SMul M α] [IsScalarTower M N α] (x : M) (y : α) : (x • (1 : N)) • y = x • y
· 使用定理 `mul_max_of_nonneg`：mul_max_of_nonneg [PosMulMono R] (b c : R) (ha : 0 <=
 a) : a * max b c = max (a * b) (a * c)
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `NNReal.coe_nonneg`：∀ (r : NNReal), 0 ≤ ↑r
· 使用定理 `NonarchAddGroupSeminorm.ext`：ext : (forall x, p x = q x) -> p = q
-/
theorem smul_sup (r : R) (p q : NonarchAddGroupSeminorm E) : r • (p ⊔ q) = r • p ⊔ r • q :=
  have Real.smul_max : ∀ x y : ℝ, r • max x y = max (r • x) (r • y) := fun x y => by
    simpa only [← smul_eq_mul, ← NNReal.smul_def, smul_one_smul ℝ≥0 r (_ : ℝ)] using
      mul_max_of_nonneg x y (r • (1 : ℝ≥0) : ℝ≥0).coe_nonneg
  ext fun _ => Real.smul_max _ _

end NonarchAddGroupSeminorm

/-! ### Norms -/


namespace GroupNorm

section Group

variable [Group E] {p q : GroupNorm E}

@[to_additive]
/-
**GroupNorm.funLike** 是 Mathlib 中的一个实例，位于命名空间 `GroupNorm`。
形式化陈述：funLike : FunLike (GroupNorm E) E Real where coe f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance funLike : FunLike (GroupNorm E) E ℝ where
  coe f := f.toFun
  coe_injective f g h := by obtain ⟨⟨_, _, _, _⟩, _⟩ := f; cases g; congr

@[to_additive]
/-
**GroupNorm.groupNormClass** 是 Mathlib 中的一个实例，位于命名空间 `GroupNorm`。
形式化陈述：groupNormClass : GroupNormClass (GroupNorm E) E Real where map_one_eq_zero
 f
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `GroupSeminorm.mul_le'`：∀ {G : Type u_6} [inst : Group G] (self : GroupSe
minorm G) (x y : G), self.toFun (x * y) ≤ self.toFun x + self.toFun y
· 使用定理 `GroupSeminorm.map_one'`：∀ {G : Type u_6} [inst : Group G] (self : GroupS
eminorm G), self.toFun 1 = 0
· 使用定理 `GroupSeminorm.inv'`：∀ {G : Type u_6} [inst : Group G] (self : GroupSemin
orm G) (x : G), self.toFun x⁻¹ = self.toFun x
· 使用定理 `GroupNorm.eq_one_of_map_eq_zero'`：∀ {G : Type u_6} [inst : Group G] (sel
f : GroupNorm G) (x : G), self.toFun x = 0 → x = 1
-/
instance groupNormClass : GroupNormClass (GroupNorm E) E ℝ where
  map_one_eq_zero f := f.map_one'
  map_mul_le_add f := f.mul_le'
  map_inv_eq_map f := f.inv'
  eq_one_of_map_eq_zero f := f.eq_one_of_map_eq_zero' _

@[to_additive (attr := simp)]
/-
**GroupNorm.toGroupSeminorm_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `GroupNorm`。
形式化陈述：toGroupSeminorm_eq_coe : ⇑p.toGroupSeminorm = p
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toGroupSeminorm_eq_coe : ⇑p.toGroupSeminorm = p :=
  rfl

@[to_additive (attr := ext)]
/-
**GroupNorm.ext** 是 Mathlib 中的一个定理，位于命名空间 `GroupNorm`。
形式化陈述：ext : (forall x, p x = q x) -> p = q
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem ext : (∀ x, p x = q x) → p = q :=
  DFunLike.ext p q

@[to_additive]
/-
**GroupNorm.** 是 Mathlib 中的一个实例，位于命名空间 `GroupNorm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PartialOrder (GroupNorm E) :=
  PartialOrder.lift _ DFunLike.coe_injective

@[to_additive]
/-
**GroupNorm.le_def** 是 Mathlib 中的一个定理，位于命名空间 `GroupNorm`。
形式化陈述：le_def : p <= q ↔ (p : E -> Real) <= q
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem le_def : p ≤ q ↔ (p : E → ℝ) ≤ q :=
  Iff.rfl

@[to_additive]
/-
**GroupNorm.lt_def** 是 Mathlib 中的一个定理，位于命名空间 `GroupNorm`。
形式化陈述：lt_def : p < q ↔ (p : E -> Real) < q
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem lt_def : p < q ↔ (p : E → ℝ) < q :=
  Iff.rfl

@[to_additive (attr := simp, norm_cast)]
/-
**GroupNorm.coe_le_coe** 是 Mathlib 中的一个定理，位于命名空间 `GroupNorm`。
形式化陈述：coe_le_coe : (p : E -> Real) <= q ↔ p <= q
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem coe_le_coe : (p : E → ℝ) ≤ q ↔ p ≤ q :=
  Iff.rfl

@[to_additive (attr := simp, norm_cast)]
/-
**GroupNorm.coe_lt_coe** 是 Mathlib 中的一个定理，位于命名空间 `GroupNorm`。
形式化陈述：coe_lt_coe : (p : E -> Real) < q ↔ p < q
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem coe_lt_coe : (p : E → ℝ) < q ↔ p < q :=
  Iff.rfl

variable (p q)

@[to_additive]
/-
**GroupNorm.** 是 Mathlib 中的一个实例，位于命名空间 `GroupNorm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Add (GroupNorm E) :=
  ⟨fun p q =>
    { p.toGroupSeminorm + q.toGroupSeminorm with
      eq_one_of_map_eq_zero' := fun _x hx =>
        of_not_not fun h => hx.not_gt <| add_pos (map_pos_of_ne_one p h) (map_pos_of_ne_one q h) }⟩

@[to_additive]
/-
**GroupNorm.** 是 Mathlib 中的一个实例，位于命名空间 `GroupNorm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsAddApply (GroupNorm E) E ℝ where
  add_apply _ _ _ := rfl

@[deprecated (since := "2026-07-10")] alias _root_.GroupNorm.coe_add := FunLike.coe_add
@[deprecated (since := "2026-07-10")] alias _root_.AddGroupNorm.coe_add := FunLike.coe_add

@[deprecated (since := "2026-07-10")] protected alias _root_.GroupNorm.add_apply := add_apply
@[deprecated (since := "2026-07-10")] protected alias _root_.AddGroupNorm.add_apply := add_apply

-- Note: To define an instance SupSet (GroupNorm E) requires a canonical "bottom" norm for sSup ∅.
-- The zero function fails definiteness; the discrete norm needs complex proofs.
-- See https://github.com/leanprover-community/mathlib/pull/11329 for context.
@[to_additive]
/-
**GroupNorm.** 是 Mathlib 中的一个实例，位于命名空间 `GroupNorm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Max (GroupNorm E) :=
  ⟨fun p q =>
    { p.toGroupSeminorm ⊔ q.toGroupSeminorm with
      eq_one_of_map_eq_zero' := fun _x hx =>
        of_not_not fun h => hx.not_gt <| lt_sup_iff.2 <| Or.inl <| map_pos_of_ne_one p h }⟩

@[to_additive (attr := simp, norm_cast)]
/-
**GroupNorm.coe_sup** 是 Mathlib 中的一个定理，位于命名空间 `GroupNorm`。
形式化陈述：coe_sup : ⇑(p ⊔ q) = ⇑p ⊔ ⇑q
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_sup : ⇑(p ⊔ q) = ⇑p ⊔ ⇑q :=
  rfl

@[to_additive (attr := simp)]
/-
**GroupNorm.sup_apply** 是 Mathlib 中的一个定理，位于命名空间 `GroupNorm`。
形式化陈述：sup_apply (x : E) : (p ⊔ q) x = p x ⊔ q x
参数：x : E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sup_apply (x : E) : (p ⊔ q) x = p x ⊔ q x :=
  rfl

@[to_additive]
/-
**GroupNorm.** 是 Mathlib 中的一个实例，位于命名空间 `GroupNorm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SemilatticeSup (GroupNorm E) :=
  DFunLike.coe_injective.semilatticeSup _ .rfl .rfl coe_sup

end Group

end GroupNorm

namespace AddGroupNorm

variable [AddGroup E] [DecidableEq E]

/-
**AddGroupNorm.** 是 Mathlib 中的一个实例，位于命名空间 `AddGroupNorm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : One (AddGroupNorm E) :=
  ⟨{ (1 : AddGroupSeminorm E) with
      eq_zero_of_map_eq_zero' := fun _x => zero_ne_one.ite_eq_left_iff.1 }⟩

@[simp]
/-
**AddGroupNorm.apply_one** 是 Mathlib 中的一个定理，位于命名空间 `AddGroupNorm`。
形式化陈述：apply_one (x : E) : (1 : AddGroupNorm E) x = if x = 0 then 0 else 1
参数：x : E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem apply_one (x : E) : (1 : AddGroupNorm E) x = if x = 0 then 0 else 1 :=
  rfl
/-
**AddGroupNorm.** 是 Mathlib 中的一个实例，位于命名空间 `AddGroupNorm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (AddGroupNorm E) :=
  ⟨1⟩

end AddGroupNorm

namespace GroupNorm

/-
**GroupNorm._root_.AddGroupNorm.toOne** 是 Mathlib 中的一个实例，位于命名空间 `GroupNorm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance _root_.AddGroupNorm.toOne [AddGroup E] [DecidableEq E] : One (AddGroupNorm E) :=
  ⟨{ (1 : AddGroupSeminorm E) with
    eq_zero_of_map_eq_zero' := fun _ => zero_ne_one.ite_eq_left_iff.1 }⟩

variable [Group E] [DecidableEq E]
/-
**GroupNorm.toOne** 是 Mathlib 中的一个实例，位于命名空间 `GroupNorm`。
形式化陈述：toOne : One (GroupNorm E)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance toOne : One (GroupNorm E) :=
  ⟨{ (1 : GroupSeminorm E) with eq_one_of_map_eq_zero' := fun _ => zero_ne_one.ite_eq_left_iff.1 }⟩

@[simp]
/-
**GroupNorm.apply_one** 是 Mathlib 中的一个定理，位于命名空间 `GroupNorm`。
形式化陈述：apply_one (x : E) : (1 : GroupNorm E) x = if x = 1 then 0 else 1
参数：x : E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem apply_one (x : E) : (1 : GroupNorm E) x = if x = 1 then 0 else 1 :=
  rfl

@[to_additive existing]
/-
**GroupNorm.** 是 Mathlib 中的一个实例，位于命名空间 `GroupNorm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (GroupNorm E) :=
  ⟨1⟩

end GroupNorm

namespace NonarchAddGroupNorm

section AddGroup

variable [AddGroup E] {p q : NonarchAddGroupNorm E}

/-
**NonarchAddGroupNorm.funLike** 是 Mathlib 中的一个实例，位于命名空间 `NonarchAddGroupNorm`。
形式化陈述：funLike : FunLike (NonarchAddGroupNorm E) E Real where coe f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance funLike : FunLike (NonarchAddGroupNorm E) E ℝ where
  coe f := f.toFun
  coe_injective f g h := by obtain ⟨⟨⟨_, _⟩, _, _⟩, _⟩ := f; cases g; congr
/-
**NonarchAddGroupNorm.nonarchAddGroupNormClass** 是 Mathlib 中的一个实例，位于命名空间 `Nonarc
hAddGroupNorm`。
形式化陈述：nonarchAddGroupNormClass : NonarchAddGroupNormClass (NonarchAddGroupNorm E
) E where map_add_le_max f
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `NonarchAddGroupSeminorm.add_le_max'`：∀ {G : Type u_6} [inst : AddGroup G
] (self : NonarchAddGroupSeminorm G) (r s : G),   self.toFun (r + s) ≤ max (self
.toFun r) (self.toFun s)
· 使用定理 `ZeroHom.map_zero'`：∀ {M : Type u_10} {N : Type u_11} [inst : Zero M] [in
st_1 : Zero N] (self : ZeroHom M N), self.toFun 0 = 0
· 使用定理 `NonarchAddGroupSeminorm.neg'`：∀ {G : Type u_6} [inst : AddGroup G] (self
 : NonarchAddGroupSeminorm G) (r : G), self.toFun (-r) = self.toFun r
· 使用定理 `NonarchAddGroupNorm.eq_zero_of_map_eq_zero'`：∀ {G : Type u_6} [inst : Ad
dGroup G] (self : NonarchAddGroupNorm G) (x : G), self.toFun x = 0 → x = 0
-/
instance nonarchAddGroupNormClass : NonarchAddGroupNormClass (NonarchAddGroupNorm E) E where
  map_add_le_max f := f.add_le_max'
  map_zero f := f.map_zero'
  map_neg_eq_map' f := f.neg'
  eq_zero_of_map_eq_zero f := f.eq_zero_of_map_eq_zero' _

@[simp]
/-
**NonarchAddGroupNorm.toNonarchAddGroupSeminorm_eq_coe** 是 Mathlib 中的一个定理，位于命名空间
 `NonarchAddGroupNorm`。
形式化陈述：toNonarchAddGroupSeminorm_eq_coe : ⇑p.toNonarchAddGroupSeminorm = p
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toNonarchAddGroupSeminorm_eq_coe : ⇑p.toNonarchAddGroupSeminorm = p :=
  rfl

@[ext]
/-
**NonarchAddGroupNorm.ext** 是 Mathlib 中的一个定理，位于命名空间 `NonarchAddGroupNorm`。
形式化陈述：ext : (forall x, p x = q x) -> p = q
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem ext : (∀ x, p x = q x) → p = q :=
  DFunLike.ext p q
/-
**NonarchAddGroupNorm.** 是 Mathlib 中的一个实例，位于命名空间 `NonarchAddGroupNorm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : PartialOrder (NonarchAddGroupNorm E) :=
  PartialOrder.lift _ DFunLike.coe_injective
/-
**NonarchAddGroupNorm.le_def** 是 Mathlib 中的一个定理，位于命名空间 `NonarchAddGroupNorm`。
形式化陈述：le_def : p <= q ↔ (p : E -> Real) <= q
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem le_def : p ≤ q ↔ (p : E → ℝ) ≤ q :=
  Iff.rfl
/-
**NonarchAddGroupNorm.lt_def** 是 Mathlib 中的一个定理，位于命名空间 `NonarchAddGroupNorm`。
形式化陈述：lt_def : p < q ↔ (p : E -> Real) < q
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem lt_def : p < q ↔ (p : E → ℝ) < q :=
  Iff.rfl

@[simp, norm_cast]
/-
**NonarchAddGroupNorm.coe_le_coe** 是 Mathlib 中的一个定理，位于命名空间 `NonarchAddGroupNorm`
。
形式化陈述：coe_le_coe : (p : E -> Real) <= q ↔ p <= q
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem coe_le_coe : (p : E → ℝ) ≤ q ↔ p ≤ q :=
  Iff.rfl

@[simp, norm_cast]
/-
**NonarchAddGroupNorm.coe_lt_coe** 是 Mathlib 中的一个定理，位于命名空间 `NonarchAddGroupNorm`
。
形式化陈述：coe_lt_coe : (p : E -> Real) < q ↔ p < q
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem coe_lt_coe : (p : E → ℝ) < q ↔ p < q :=
  Iff.rfl

variable (p q)
/-
**NonarchAddGroupNorm.** 是 Mathlib 中的一个实例，位于命名空间 `NonarchAddGroupNorm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Max (NonarchAddGroupNorm E) :=
  ⟨fun p q =>
    { p.toNonarchAddGroupSeminorm ⊔ q.toNonarchAddGroupSeminorm with
      eq_zero_of_map_eq_zero' := fun _x hx =>
        of_not_not fun h => hx.not_gt <| lt_sup_iff.2 <| Or.inl <| map_pos_of_ne_zero p h }⟩

@[simp, norm_cast]
/-
**NonarchAddGroupNorm.coe_sup** 是 Mathlib 中的一个定理，位于命名空间 `NonarchAddGroupNorm`。
形式化陈述：coe_sup : ⇑(p ⊔ q) = ⇑p ⊔ ⇑q
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_sup : ⇑(p ⊔ q) = ⇑p ⊔ ⇑q :=
  rfl

@[simp]
/-
**NonarchAddGroupNorm.sup_apply** 是 Mathlib 中的一个定理，位于命名空间 `NonarchAddGroupNorm`。
形式化陈述：sup_apply (x : E) : (p ⊔ q) x = p x ⊔ q x
参数：x : E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sup_apply (x : E) : (p ⊔ q) x = p x ⊔ q x :=
  rfl
/-
**NonarchAddGroupNorm.** 是 Mathlib 中的一个实例，位于命名空间 `NonarchAddGroupNorm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : SemilatticeSup (NonarchAddGroupNorm E) :=
  DFunLike.coe_injective.semilatticeSup _ .rfl .rfl coe_sup
/-
**NonarchAddGroupNorm.** 是 Mathlib 中的一个实例，位于命名空间 `NonarchAddGroupNorm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DecidableEq E] : One (NonarchAddGroupNorm E) :=
  ⟨{ (1 : NonarchAddGroupSeminorm E) with
      eq_zero_of_map_eq_zero' := fun _ => zero_ne_one.ite_eq_left_iff.1 }⟩

@[simp]
/-
**NonarchAddGroupNorm.apply_one** 是 Mathlib 中的一个定理，位于命名空间 `NonarchAddGroupNorm`。
形式化陈述：apply_one [DecidableEq E] (x : E) : (1 : NonarchAddGroupNorm E) x = if x =
 0 then 0 else 1
参数：x : E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem apply_one [DecidableEq E] (x : E) :
    (1 : NonarchAddGroupNorm E) x = if x = 0 then 0 else 1 :=
  rfl
/-
**NonarchAddGroupNorm.** 是 Mathlib 中的一个实例，位于命名空间 `NonarchAddGroupNorm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DecidableEq E] : Inhabited (NonarchAddGroupNorm E) :=
  ⟨1⟩

end AddGroup

end NonarchAddGroupNorm

