/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.GroupWithZero.Commute
public import Mathlib.Algebra.GroupWithZero.Hom

/-!
# Further lemmas about units in a `MonoidWithZero` or a `GroupWithZero`.

-/

@[expose] public section

assert_not_exists DenselyOrdered MulAction Ring

open scoped Ring

variable {M M₀ G₀ M₀' G₀' F F' : Type*}
variable [MonoidWithZero M₀]

section Monoid

variable [Monoid M] [GroupWithZero G₀]

/-
**isLocalHom_of_exists_map_ne_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isLocalHom_of_exists_map_ne_one [FunLike F G₀ M] [MonoidHomClass F G₀ M] {
f : F} (hf : exists x : G₀, f x != 1) : IsLocalHom f where map_nonunit a h
参数：hf : exists x : G₀, f x != 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsUnit.mul_right_cancel`：∀ {M : Type u_1} [inst : Monoid M] {a b c : M},
 IsUnit b → a * b = c * b → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
-/
lemma isLocalHom_of_exists_map_ne_one [FunLike F G₀ M] [MonoidHomClass F G₀ M] {f : F}
    (hf : ∃ x : G₀, f x ≠ 1) : IsLocalHom f where
  map_nonunit a h := by
    rcases eq_or_ne a 0 with (rfl | h)
    · obtain ⟨t, ht⟩ := hf
      refine (ht ?_).elim
      have := map_mul f t 0
      rw [← one_mul (f (t * 0)), mul_zero] at this
      exact (h.mul_right_cancel this).symm
    · exact ⟨⟨a, a⁻¹, mul_inv_cancel₀ h, inv_mul_cancel₀ h⟩, rfl⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [FunLike F G₀ M₀] [MonoidWithZeroHomClass F G₀ M₀] [Nontrivial M₀]
    (f : F) : IsLocalHom f :=
  isLocalHom_of_exists_map_ne_one ⟨0, by simp⟩

end Monoid

section GroupWithZero

namespace Commute

variable [GroupWithZero G₀] {a b c d : G₀}

/-- The `MonoidWithZero` version of `div_eq_div_iff_mul_eq_mul`. -/
/-
**Commute.div_eq_div_iff** 是 Mathlib 中的一个定理，位于命名空间 `Commute`。
形式化陈述：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a b c d : G₀},   Commute b d 
→ b ≠ 0 → d ≠ 0 → (a / b = c / d ↔ a * d = c * b)
参数：a / b = c / d ↔ a * d = c * b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Commute.div_eq_div_iff_of_isUnit`：div_eq_div_iff_of_isUnit (hbd : Commut
e b d) (hb : IsUnit b) (hd : IsUnit d) : a / b = c / d ↔ a * d = c * b
· 使用定理 `Ne.isUnit`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 →
 IsUnit a

--- 原说明 ---
The `MonoidWithZero` version of `div_eq_div_iff_mul_eq_mul`.
-/
protected lemma div_eq_div_iff (hbd : Commute b d) (hb : b ≠ 0) (hd : d ≠ 0) :
    a / b = c / d ↔ a * d = c * b :=
  hbd.div_eq_div_iff_of_isUnit hb.isUnit hd.isUnit

/-- The `MonoidWithZero` version of `mul_inv_eq_mul_inv_iff_mul_eq_mul`. -/
/-
**Commute.mul_inv_eq_mul_inv_iff** 是 Mathlib 中的一个定理，位于命名空间 `Commute`。
形式化陈述：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a b c d : G₀},   Commute b d 
→ b ≠ 0 → d ≠ 0 → (a * b⁻¹ = c * d⁻¹ ↔ a * d = c * b)
参数：a * b⁻¹ = c * d⁻¹ ↔ a * d = c * b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Commute.mul_inv_eq_mul_inv_iff_of_isUnit`：mul_inv_eq_mul_inv_iff_of_isUn
it (hbd : Commute b d) (hb : IsUnit b) (hd : IsUnit d) : a * b⁻¹ = c * d⁻¹ ↔ a *
 d = c * b
· 使用定理 `Ne.isUnit`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 →
 IsUnit a

--- 原说明 ---
The `MonoidWithZero` version of `mul_inv_eq_mul_inv_iff_mul_eq_mul`.
-/
protected lemma mul_inv_eq_mul_inv_iff (hbd : Commute b d) (hb : b ≠ 0) (hd : d ≠ 0) :
    a * b⁻¹ = c * d⁻¹ ↔ a * d = c * b :=
  hbd.mul_inv_eq_mul_inv_iff_of_isUnit hb.isUnit hd.isUnit

/-- The `MonoidWithZero` version of `inv_mul_eq_inv_mul_iff_mul_eq_mul`. -/
/-
**Commute.inv_mul_eq_inv_mul_iff** 是 Mathlib 中的一个定理，位于命名空间 `Commute`。
形式化陈述：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a b c d : G₀},   Commute b d 
→ b ≠ 0 → d ≠ 0 → (b⁻¹ * a = d⁻¹ * c ↔ d * a = b * c)
参数：b⁻¹ * a = d⁻¹ * c ↔ d * a = b * c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Commute.inv_mul_eq_inv_mul_iff_of_isUnit`：inv_mul_eq_inv_mul_iff_of_isUn
it (hbd : Commute b d) (hb : IsUnit b) (hd : IsUnit d) : b⁻¹ * a = d⁻¹ * c ↔ d *
 a = b * c
· 使用定理 `Ne.isUnit`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 →
 IsUnit a

--- 原说明 ---
The `MonoidWithZero` version of `inv_mul_eq_inv_mul_iff_mul_eq_mul`.
-/
protected lemma inv_mul_eq_inv_mul_iff (hbd : Commute b d) (hb : b ≠ 0) (hd : d ≠ 0) :
    b⁻¹ * a = d⁻¹ * c ↔ d * a = b * c :=
  hbd.inv_mul_eq_inv_mul_iff_of_isUnit hb.isUnit hd.isUnit

end Commute

section MulZeroOneClass

variable [GroupWithZero G₀] [MulZeroOneClass M₀'] [Nontrivial M₀'] [FunLike F G₀ M₀']
  [MonoidWithZeroHomClass F G₀ M₀']
  (f : F) {a : G₀}

/-
**map_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_ne_zero : f a != 0 ↔ a != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `instCanLiftUnitsValIsUnit`：∀ {M : Type u_1} [inst : Monoid M], CanLift M
 Mˣ Units.val IsUnit
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isUnit_iff_ne_zero`：isUnit_iff_ne_zero : IsUnit a ↔ a != 0
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `Units.mul_inv`：mul_inv : (a * ↑a⁻¹ : α) = 1
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
-/
theorem map_ne_zero : f a ≠ 0 ↔ a ≠ 0 := by
  refine ⟨fun hfa ha => hfa <| ha.symm ▸ map_zero f, ?_⟩
  intro hx H
  lift a to G₀ˣ using isUnit_iff_ne_zero.mpr hx
  apply one_ne_zero (α := M₀')
  rw [← map_one f, ← Units.mul_inv a, map_mul, H, zero_mul]

@[simp]
/-
**map_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_eq_zero : f a = 0 ↔ a = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `map_ne_zero`：map_ne_zero : f a != 0 ↔ a != 0
-/
theorem map_eq_zero : f a = 0 ↔ a = 0 :=
  not_iff_not.1 (map_ne_zero f)

end MulZeroOneClass

section MonoidWithZero

variable [GroupWithZero G₀] [Nontrivial M₀] [MonoidWithZero M₀'] [FunLike F G₀ M₀]
  [MonoidWithZeroHomClass F G₀ M₀] [FunLike F' G₀ M₀']
  (f : F) {a : G₀}

/-
**eq_on_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_on_inv {F G M} [Group G] [Monoid M] [FunLike F G M] [MonoidHomClass F G
 M] (f g : F) {x : G} (h : f x = g x) : f x⁻¹ = g x⁻¹
参数：f g : F；h : f x = g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUnit.eq_on_inv`：IsUnit.eq_on_inv {F G N} [DivisionMonoid G] [Monoid N]
 [FunLike F G N] [MonoidHomClass F G N] {x : G} (hx : IsUnit x) (f g : F) (h : f
 x = g…
· 使用引理 `Group.isUnit`：Group.isUnit [Group α] (a : α) : IsUnit a
-/
theorem eq_on_inv₀ [MonoidWithZeroHomClass F' G₀ M₀'] (f g : F') (h : f a = g a) :
    f a⁻¹ = g a⁻¹ := by
  rcases eq_or_ne a 0 with (rfl | ha)
  · rw [inv_zero, map_zero, map_zero]
  · exact (IsUnit.mk0 a ha).eq_on_inv f g h

end MonoidWithZero

section GroupWithZero

variable [GroupWithZero G₀] [GroupWithZero G₀'] [FunLike F G₀ G₀']
  [MonoidWithZeroHomClass F G₀ G₀'] (f : F) (a b : G₀)

/-- A monoid homomorphism between groups with zeros sending `0` to `0` sends `a⁻¹` to `(f a)⁻¹`. -/
@[simp]
/-
**map_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_inv [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f : F) (a : G
) : f a⁻¹ = (f a)⁻¹
参数：f : F；a : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_inv_of_mul_eq_one_left`：eq_inv_of_mul_eq_one_left (h : a * b = 1) : a
 = b⁻¹
· 使用定理 `map_mul_eq_one`：map_mul_eq_one [MonoidHomClass F M N] (f : F) {a b : M} 
(h : a * b = 1) : f a * f b = 1
· 使用定理 `inv_mul_cancel`：inv_mul_cancel (a : G) : a⁻¹ * a = 1

--- 原说明 ---
A monoid homomorphism between groups with zeros sending `0` to `0` sends `a⁻¹` t
o `(f a)⁻¹`.
-/
theorem map_inv₀ : f a⁻¹ = (f a)⁻¹ := by
  by_cases h : a = 0
  · simp [h, map_zero f]
  · apply eq_inv_of_mul_eq_one_left
    rw [← map_mul, inv_mul_cancel₀ h, map_one]

@[simp]
/-
**map_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_div [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f : F) : fora
ll a b, f (a / b) = f a / f b
参数：f : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_div'`：map_div' [DivInvMonoid G] [DivInvMonoid H] [MulHomClass F G H]
 (f : F) (hf : forall a, f a⁻¹ = (f a)⁻¹) (a b : G) : f (a / b) = f a / f b
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `map_inv`：map_inv [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f 
: F) (a : G) : f a⁻¹ = (f a)⁻¹
-/
theorem map_div₀ : f (a / b) = f a / f b :=
  map_div' f (map_inv₀ f) a b

end GroupWithZero

/-- We define the inverse as a `MonoidWithZeroHom` by extending the inverse map by zero
on non-units. -/
/-
**MonoidWithZero.inverse** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：MonoidWithZero.inverse {M : Type*} [CommMonoidWithZero M] : M ->*₀ M where
 toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We define the inverse as a `MonoidWithZeroHom` by extending the inverse map by z
ero
on non-units.
-/
noncomputable def MonoidWithZero.inverse {M : Type*} [CommMonoidWithZero M] :
    M →*₀ M where
  toFun := Ring.inverse
  map_zero' := Ring.inverse_zero _
  map_one' := Ring.inverse_one _
  map_mul' x y := (Ring.mul_inverse_rev x y).trans (mul_comm _ _)

@[simp]
/-
**MonoidWithZero.coe_inverse** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonoidWithZero.coe_inverse {M : Type*} [CommMonoidWithZero M] : (MonoidWit
hZero.inverse : M -> M) = Ring.inverse
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem MonoidWithZero.coe_inverse {M : Type*} [CommMonoidWithZero M] :
    (MonoidWithZero.inverse : M → M) = Ring.inverse :=
  rfl

@[simp]
/-
**MonoidWithZero.inverse_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonoidWithZero.inverse_apply {M : Type*} [CommMonoidWithZero M] (a : M) : 
MonoidWithZero.inverse a = a⁻¹ʳ
参数：a : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem MonoidWithZero.inverse_apply {M : Type*} [CommMonoidWithZero M] (a : M) :
    MonoidWithZero.inverse a = a⁻¹ʳ :=
  rfl

/-- Inversion on a commutative group with zero, considered as a monoid with zero homomorphism. -/
/-
**invMonoidWithZeroHom** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：invMonoidWithZeroHom {G₀ : Type*} [CommGroupWithZero G₀] : G₀ ->*₀ G₀
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Inversion on a commutative group with zero, considered as a monoid with zero hom
omorphism.
-/
def invMonoidWithZeroHom {G₀ : Type*} [CommGroupWithZero G₀] : G₀ →*₀ G₀ :=
  { invMonoidHom with map_zero' := inv_zero }

/-- If a monoid homomorphism `f` between two `GroupWithZero`s maps `0` to `0`, then it maps `x^n`,
`n : ℤ`, to `(f x)^n`. -/
@[simp]
/-
**map_zpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_zpow [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f : F) (g : 
G) (n : Int) : f (g ^ n) = f g ^ n
参数：f : F；g : G；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_zpow'`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLik
e F G H] [inst_1 : DivInvMonoid G]   [inst_2 : DivInvMonoid H] [MonoidHomClass …
· 使用定理 `map_inv`：map_inv [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f 
: F) (a : G) : f a⁻¹ = (f a)⁻¹

--- 原说明 ---
If a monoid homomorphism `f` between two `GroupWithZero`s maps `0` to `0`, then 
it maps `x^n`,
`n : ℤ`, to `(f x)^n`.
-/
theorem map_zpow₀ {F G₀ G₀' : Type*} [GroupWithZero G₀] [GroupWithZero G₀'] [FunLike F G₀ G₀']
    [MonoidWithZeroHomClass F G₀ G₀'] (f : F) (x : G₀) (n : ℤ) : f (x ^ n) = f x ^ n :=
  map_zpow' f (map_inv₀ f) x n

end GroupWithZero

