/-
Copyright (c) 2022 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shing Tak Lam, Frédéric Dupuis
-/
module

public import Mathlib.Algebra.Group.Submonoid.Operations
public import Mathlib.Algebra.Star.SelfAdjoint
public import Mathlib.Algebra.Algebra.Spectrum.Basic
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Algebra.Star.MonoidHom
public import Mathlib.Algebra.Star.StarProjection

/-!
# Unitary elements of a star monoid

This file defines `unitary R`, where `R` is a star monoid, as the submonoid made of the elements
that satisfy `star U * U = 1` and `U * star U = 1`, and these form a group.
This includes, for instance, unitary operators on Hilbert spaces.

See also `Matrix.UnitaryGroup` for specializations to `unitary (Matrix n n R)`.

## Tags

unitary
-/

@[expose] public section


/-- In a \*-monoid, `unitary R` is the submonoid consisting of all the elements `U` of
`R` such that `star U * U = 1` and `U * star U = 1`.
-/
/-
**unitary** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：unitary (R : Type*) [Monoid R] [StarMul R] : Submonoid R where carrier
参数：R : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In a \*-monoid, `unitary R` is the submonoid consisting of all the elements `U` 
of
`R` such that `star U * U = 1` and `U * star U = 1`.
-/
def unitary (R : Type*) [Monoid R] [StarMul R] : Submonoid R where
  carrier := { U | star U * U = 1 ∧ U * star U = 1 }
  one_mem' := by simp only [mul_one, and_self_iff, Set.mem_ofPred_eq, star_one]
  mul_mem' := @fun U B ⟨hA₁, hA₂⟩ ⟨hB₁, hB₂⟩ => by
    refine ⟨?_, ?_⟩
    · calc
        star (U * B) * (U * B) = star B * star U * U * B := by simp only [mul_assoc, star_mul]
        _ = star B * (star U * U) * B := by rw [← mul_assoc]
        _ = 1 := by rw [hA₁, mul_one, hB₁]
    · calc
        U * B * star (U * B) = U * B * (star B * star U) := by rw [star_mul]
        _ = U * (B * star B) * star U := by simp_rw [← mul_assoc]
        _ = 1 := by rw [hB₂, mul_one, hA₂]

variable {R : Type*}

namespace Unitary

section Monoid

variable [Monoid R] [StarMul R]

/-
**Unitary.mem_iff** 是 Mathlib 中的一个定理，位于命名空间 `Unitary`。
形式化陈述：mem_iff {U : R} : U in unitary R ↔ star U * U = 1 ∧ U * star U = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_iff {U : R} : U ∈ unitary R ↔ star U * U = 1 ∧ U * star U = 1 :=
  Iff.rfl

@[simp]
/-
**Unitary.star_mul_self_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Unitary`。
形式化陈述：star_mul_self_of_mem {U : R} (hU : U in unitary R) : star U * U = 1
参数：hU : U in unitary R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem star_mul_self_of_mem {U : R} (hU : U ∈ unitary R) : star U * U = 1 :=
  hU.1

@[simp]
/-
**Unitary.mul_star_self_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Unitary`。
形式化陈述：mul_star_self_of_mem {U : R} (hU : U in unitary R) : U * star U = 1
参数：hU : U in unitary R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem mul_star_self_of_mem {U : R} (hU : U ∈ unitary R) : U * star U = 1 :=
  hU.2
/-
**Unitary.star_mem** 是 Mathlib 中的一个定理，位于命名空间 `Unitary`。
形式化陈述：star_mem {U : R} (hU : U in unitary R) : star U in unitary R
参数：hU : U in unitary R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `star_star`：star_star [InvolutiveStar R] (r : R) : star (star r) = r
· 使用定理 `Unitary.mul_star_self_of_mem`：mul_star_self_of_mem {U : R} (hU : U in un
itary R) : U * star U = 1
· 使用定理 `Unitary.star_mul_self_of_mem`：star_mul_self_of_mem {U : R} (hU : U in un
itary R) : star U * U = 1
-/
theorem star_mem {U : R} (hU : U ∈ unitary R) : star U ∈ unitary R :=
  ⟨by rw [star_star, mul_star_self_of_mem hU], by rw [star_star, star_mul_self_of_mem hU]⟩

@[simp]
/-
**Unitary.star_mem_iff** 是 Mathlib 中的一个定理，位于命名空间 `Unitary`。
形式化陈述：star_mem_iff {U : R} : star U in unitary R ↔ U in unitary R
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Unitary.star_mem`：star_mem {U : R} (hU : U in unitary R) : star U in uni
tary R
· 使用定理 `star_star`：star_star [InvolutiveStar R] (r : R) : star (star r) = r
-/
theorem star_mem_iff {U : R} : star U ∈ unitary R ↔ U ∈ unitary R :=
  ⟨fun h => star_star U ▸ star_mem h, star_mem⟩
/-
**Unitary.** 是 Mathlib 中的一个实例，位于命名空间 `Unitary`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Star (unitary R) :=
  ⟨fun U => ⟨star U, star_mem U.prop⟩⟩

@[simp, norm_cast]
/-
**Unitary.coe_star** 是 Mathlib 中的一个定理，位于命名空间 `Unitary`。
形式化陈述：coe_star {U : unitary R} : ↑(star U) = (star U : R)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_star {U : unitary R} : ↑(star U) = (star U : R) :=
  rfl
/-
**Unitary.coe_star_mul_self** 是 Mathlib 中的一个定理，位于命名空间 `Unitary`。
形式化陈述：coe_star_mul_self (U : unitary R) : (star U : R) * U = 1
参数：U : unitary R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Unitary.star_mul_self_of_mem`：star_mul_self_of_mem {U : R} (hU : U in un
itary R) : star U * U = 1
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
-/
theorem coe_star_mul_self (U : unitary R) : (star U : R) * U = 1 :=
  star_mul_self_of_mem U.prop
/-
**Unitary.coe_mul_star_self** 是 Mathlib 中的一个定理，位于命名空间 `Unitary`。
形式化陈述：coe_mul_star_self (U : unitary R) : (U : R) * star U = 1
参数：U : unitary R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Unitary.mul_star_self_of_mem`：mul_star_self_of_mem {U : R} (hU : U in un
itary R) : U * star U = 1
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
-/
theorem coe_mul_star_self (U : unitary R) : (U : R) * star U = 1 :=
  mul_star_self_of_mem U.prop

@[simp]
/-
**Unitary.star_mul_self** 是 Mathlib 中的一个定理，位于命名空间 `Unitary`。
形式化陈述：star_mul_self (U : unitary R) : star U * U = 1
参数：U : unitary R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Unitary.coe_star_mul_self`：coe_star_mul_self (U : unitary R) : (star U :
 R) * U = 1
-/
theorem star_mul_self (U : unitary R) : star U * U = 1 :=
  Subtype.ext <| coe_star_mul_self U

@[simp]
/-
**Unitary.mul_star_self** 是 Mathlib 中的一个定理，位于命名空间 `Unitary`。
形式化陈述：mul_star_self (U : unitary R) : U * star U = 1
参数：U : unitary R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Unitary.coe_mul_star_self`：coe_mul_star_self (U : unitary R) : (U : R) *
 star U = 1
-/
theorem mul_star_self (U : unitary R) : U * star U = 1 :=
  Subtype.ext <| coe_mul_star_self U
/-
**Unitary.** 是 Mathlib 中的一个实例，位于命名空间 `Unitary`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Group (unitary R) :=
  { Submonoid.toMonoid _ with
    inv := star
    inv_mul_cancel := star_mul_self }
/-
**Unitary.** 是 Mathlib 中的一个实例，位于命名空间 `Unitary`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : InvolutiveStar (unitary R) :=
  ⟨by
    intro x
    ext
    rw [coe_star, coe_star, star_star]⟩
/-
**Unitary.** 是 Mathlib 中的一个实例，位于命名空间 `Unitary`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : StarMul (unitary R) :=
  ⟨by
    intro x y
    ext
    rw [coe_star, Submonoid.coe_mul, Submonoid.coe_mul, coe_star, coe_star, star_mul]⟩
/-
**Unitary.** 是 Mathlib 中的一个实例，位于命名空间 `Unitary`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (unitary R) :=
  ⟨1⟩
/-
**Unitary.star_eq_inv** 是 Mathlib 中的一个定理，位于命名空间 `Unitary`。
形式化陈述：star_eq_inv (U : unitary R) : star U = U⁻¹
参数：U : unitary R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem star_eq_inv (U : unitary R) : star U = U⁻¹ :=
  rfl
/-
**Unitary.star_eq_inv'** 是 Mathlib 中的一个定理，位于命名空间 `Unitary`。
形式化陈述：star_eq_inv' : (star : unitary R -> unitary R) = Inv.inv
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem star_eq_inv' : (star : unitary R → unitary R) = Inv.inv :=
  rfl

/-- The unitary elements embed into the units. -/
@[simps]
/-
**Unitary.toUnits** 是 Mathlib 中的一个定义，位于命名空间 `Unitary`。
形式化陈述：toUnits : unitary R ->* Rˣ where toFun x
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Unitary.coe_mul_star_self`：coe_mul_star_self (U : unitary R) : (U : R) *
 star U = 1
· 使用定理 `Unitary.coe_star_mul_self`：coe_star_mul_self (U : unitary R) : (star U :
 R) * U = 1

--- 原说明 ---
The unitary elements embed into the units.
-/
def toUnits : unitary R →* Rˣ where
  toFun x := ⟨x, ↑x⁻¹, coe_mul_star_self x, coe_star_mul_self x⟩
  map_one' := Units.ext rfl
  map_mul' _ _ := Units.ext rfl
/-
**Unitary.toUnits_injective** 是 Mathlib 中的一个定理，位于命名空间 `Unitary`。
形式化陈述：toUnits_injective : Function.Injective (toUnits : unitary R -> Rˣ)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Units.ext_iff`：∀ {α : Type u} [inst : Monoid α] {u v : αˣ}, u = v ↔ ↑u =
 ↑v
-/
theorem toUnits_injective : Function.Injective (toUnits : unitary R → Rˣ) := fun _ _ h =>
  Subtype.ext <| Units.ext_iff.mp h
/-
**Unitary._root_.IsUnit.mem_unitary_iff_star_mul_self** 是 Mathlib 中的一个定理，位于命名空间 
`Unitary`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.IsUnit.mem_unitary_iff_star_mul_self {u : R} (hu : IsUnit u) :
    u ∈ unitary R ↔ star u * u = 1 := by
  rw [mem_iff, and_iff_left_of_imp fun h_mul => ?_]
  lift u to Rˣ using hu
  exact left_inv_eq_right_inv h_mul u.mul_inv ▸ u.mul_inv
/-
**Unitary._root_.IsUnit.mem_unitary_iff_mul_star_self** 是 Mathlib 中的一个定理，位于命名空间 
`Unitary`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.IsUnit.mem_unitary_iff_mul_star_self {u : R} (hu : IsUnit u) :
    u ∈ unitary R ↔ u * star u = 1 := by
  rw [← star_mem_iff, hu.star.mem_unitary_iff_star_mul_self, star_star]

alias ⟨_, _root_.IsUnit.mem_unitary_of_star_mul_self⟩ := IsUnit.mem_unitary_iff_star_mul_self
alias ⟨_, _root_.IsUnit.mem_unitary_of_mul_star_self⟩ := IsUnit.mem_unitary_iff_mul_star_self
/-
**Unitary.isUnit_coe** 是 Mathlib 中的一个定理，位于命名空间 `Unitary`。
形式化陈述：isUnit_coe {U : unitary R} : IsUnit (U : R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Units.isUnit`：∀ {M : Type u_1} [inst : Monoid M] (u : Mˣ), IsUnit ↑u
-/
theorem isUnit_coe {U : unitary R} : IsUnit (U : R) := (Unitary.toUnits _).isUnit

/-- For unitary `U` in a star-monoid `R`, `x * U = y * U` if and only if `x = y`
for all `x` and `y` in `R`. -/
/-
**Unitary.mul_left_inj** 是 Mathlib 中的一个定理，位于命名空间 `Unitary`。
形式化陈述：∀ {R : Type u_1} [inst : Monoid R] [inst_1 : StarMul R] {x y : R} (U : ↥(u
nitary R)), x * ↑U = y * ↑U ↔ x = y
参数：U : ↥(unitary R)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Units.mul_left_inj`：mul_left_inj (a : αˣ) {b c : α} : b * a = c * a ↔ b 
= c
· 使用定理 `Unitary.val_toUnits_apply`：∀ {R : Type u_1} [inst : Monoid R] [inst_1 : 
StarMul R] (x : ↥(unitary R)), ↑(Unitary.toUnits x) = ↑x

--- 原说明 ---
For unitary `U` in a star-monoid `R`, `x * U = y * U` if and only if `x = y`
for all `x` and `y` in `R`.
-/
protected theorem mul_left_inj {x y : R} (U : unitary R) :
    x * U = y * U ↔ x = y :=
  val_toUnits_apply U ▸ Units.mul_left_inj _

/-- For unitary `U` in a star-monoid `R`, `U * x = U * y` if and only if `x = y`
for all `x` and `y` in `R`. -/
/-
**Unitary.mul_right_inj** 是 Mathlib 中的一个定理，位于命名空间 `Unitary`。
形式化陈述：∀ {R : Type u_1} [inst : Monoid R] [inst_1 : StarMul R] {x y : R} (U : ↥(u
nitary R)), ↑U * x = ↑U * y ↔ x = y
参数：U : ↥(unitary R)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Units.mul_right_inj`：mul_right_inj (a : αˣ) {b c : α} : (a : α) * b = a 
* c ↔ b = c
· 使用定理 `Unitary.val_toUnits_apply`：∀ {R : Type u_1} [inst : Monoid R] [inst_1 : 
StarMul R] (x : ↥(unitary R)), ↑(Unitary.toUnits x) = ↑x

--- 原说明 ---
For unitary `U` in a star-monoid `R`, `U * x = U * y` if and only if `x = y`
for all `x` and `y` in `R`.
-/
protected theorem mul_right_inj {x y : R} (U : unitary R) :
    U * x = U * y ↔ x = y :=
  val_toUnits_apply U ▸ Units.mul_right_inj _
/-
**Unitary.mul_inv_mem_iff** 是 Mathlib 中的一个引理，位于命名空间 `Unitary`。
形式化陈述：mul_inv_mem_iff {G : Type*} [Group G] [StarMul G] (a b : G) : a * b⁻¹ in u
nitary G ↔ star a * a = star b * b
参数：a b : G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsUnit.mem_unitary_iff_star_mul_self`：∀ {R : Type u_1} [inst : Monoid R]
 [inst_1 : StarMul R] {u : R}, IsUnit u → (u ∈ unitary R ↔ star u * u = 1)
· 使用引理 `Group.isUnit`：Group.isUnit [Group α] (a : α) : IsUnit a
· 使用定理 `StarMul.star_mul`：∀ {R : Type u} {inst : Mul R} [self : StarMul R] (r s 
: R), star (r * s) = star s * star r
· 使用定理 `star_inv`：star_inv [Group R] [StarMul R] (x : R) : star x⁻¹ = (star x)⁻¹
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `inv_mul_eq_iff_eq_mul`：inv_mul_eq_iff_eq_mul : a⁻¹ * b = c ↔ b = a * c
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_inv_eq_iff_eq_mul`：mul_inv_eq_iff_eq_mul : a * b⁻¹ = c ↔ a = c * b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mul_inv_mem_iff {G : Type*} [Group G] [StarMul G] (a b : G) :
    a * b⁻¹ ∈ unitary G ↔ star a * a = star b * b := by
  rw [(Group.isUnit _).mem_unitary_iff_star_mul_self, star_mul, star_inv, mul_assoc,
    inv_mul_eq_iff_eq_mul, mul_one, ← mul_assoc, mul_inv_eq_iff_eq_mul]
/-
**Unitary.inv_mul_mem_iff** 是 Mathlib 中的一个引理，位于命名空间 `Unitary`。
形式化陈述：inv_mul_mem_iff {G : Type*} [Group G] [StarMul G] (a b : G) : a⁻¹ * b in u
nitary G ↔ a * star a = b * star b
参数：a b : G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `star_inv`：star_inv [Group R] [StarMul R] (x : R) : star x⁻¹ = (star x)⁻¹
· 使用引理 `Unitary.mul_inv_mem_iff`：mul_inv_mem_iff {G : Type*} [Group G] [StarMul 
G] (a b : G) : a * b⁻¹ in unitary G ↔ star a * a = star b * b
-/
lemma inv_mul_mem_iff {G : Type*} [Group G] [StarMul G] (a b : G) :
    a⁻¹ * b ∈ unitary G ↔ a * star a = b * star b := by
  simpa [← mul_inv_rev] using mul_inv_mem_iff a⁻¹ b⁻¹
/-
**Unitary._root_.Units.unitary_eq** 是 Mathlib 中的一个定理，位于命名空间 `Unitary`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Units.unitary_eq : unitary Rˣ = (unitary R).comap (Units.coeHom R) := by
  ext
  simp [mem_iff, Units.ext_iff]

/-- In a star monoid, the product `a * b⁻¹` of units is unitary if `star a * a = star b * b`. -/
/-
**Unitary._root_.Units.mul_inv_mem_unitary** 是 Mathlib 中的一个引理，位于命名空间 `Unitary`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In a star monoid, the product `a * b⁻¹` of units is unitary if `star a * a = sta
r b * b`.
-/
protected lemma _root_.Units.mul_inv_mem_unitary (a b : Rˣ) :
    (a * b⁻¹ : R) ∈ unitary R ↔ star a * a = star b * b := by
  simp [← mul_inv_mem_iff, Units.unitary_eq]

/-- In a star monoid, the product `a⁻¹ * b` of units is unitary if `a * star a = b * star b`. -/
/-
**Unitary._root_.Units.inv_mul_mem_unitary** 是 Mathlib 中的一个引理，位于命名空间 `Unitary`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In a star monoid, the product `a⁻¹ * b` of units is unitary if `a * star a = b *
 star b`.
-/
protected lemma _root_.Units.inv_mul_mem_unitary (a b : Rˣ) :
    (a⁻¹ * b : R) ∈ unitary R ↔ a * star a = b * star b := by
  simp [← inv_mul_mem_iff, Units.unitary_eq]
/-
**Unitary.instIsStarNormal** 是 Mathlib 中的一个实例，位于命名空间 `Unitary`。
形式化陈述：instIsStarNormal (u : unitary R) : IsStarNormal u where .trans (mul_star_s
elf u).symm star_comm_self
参数：u : unitary R。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Unitary.star_mul_self`：star_mul_self (U : unitary R) : star U * U = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Unitary.mul_star_self`：mul_star_self (U : unitary R) : U * star U = 1
-/
instance instIsStarNormal (u : unitary R) : IsStarNormal u where
  star_comm_self := star_mul_self u |>.trans <| (mul_star_self u).symm
/-
**Unitary.coe_isStarNormal** 是 Mathlib 中的一个实例，位于命名空间 `Unitary`。
形式化陈述：coe_isStarNormal (u : unitary R) : IsStarNormal (u : R) where star_comm_se
lf
参数：u : unitary R。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `star_comm_self'`：star_comm_self' [Mul R] [Star R] (x : R) [IsStarNormal 
x] : star x * x = x * star x
-/
instance coe_isStarNormal (u : unitary R) : IsStarNormal (u : R) where
  star_comm_self := congr(Subtype.val $(star_comm_self' u))

@[aesop 10% apply (rule_sets := [CStarAlgebra])]
/-
**Unitary._root_.isStarNormal_of_mem_unitary** 是 Mathlib 中的一个引理，位于命名空间 `Unitary`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.isStarNormal_of_mem_unitary {u : R} (hu : u ∈ unitary R) : IsStarNormal u :=
  coe_isStarNormal ⟨u, hu⟩
/-
**Unitary.commute_self_star** 是 Mathlib 中的一个引理，位于命名空间 `Unitary`。
形式化陈述：commute_self_star (u : unitary R) : Commute u (star u)
参数：u : unitary R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Unitary.mul_star_self`：mul_star_self (U : unitary R) : U * star U = 1
· 使用定理 `Unitary.star_mul_self`：star_mul_self (U : unitary R) : star U * U = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma commute_self_star (u : unitary R) : Commute u (star u) := by simp [commute_iff_eq]
/-
**Unitary.commute_star_self** 是 Mathlib 中的一个引理，位于命名空间 `Unitary`。
形式化陈述：commute_star_self (u : unitary R) : Commute (star u) u
参数：u : unitary R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Unitary.star_mul_self`：star_mul_self (U : unitary R) : star U * U = 1
· 使用定理 `Unitary.mul_star_self`：mul_star_self (U : unitary R) : U * star U = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma commute_star_self (u : unitary R) : Commute (star u) u := by simp [commute_iff_eq]
/-
**Unitary._root_.commute_unitary_star_self** 是 Mathlib 中的一个引理，位于命名空间 `Unitary`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.commute_unitary_star_self {u : R} (hu : u ∈ unitary R) : Commute (star u) u :=
  isStarNormal_of_mem_unitary hu |>.star_comm_self
/-
**Unitary._root_.commute_unitary_self_star** 是 Mathlib 中的一个引理，位于命名空间 `Unitary`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.commute_unitary_self_star {u : R} (hu : u ∈ unitary R) : Commute u (star u) :=
  commute_unitary_star_self hu |>.symm
/-
**Unitary._root_.commute_unitary_iff_star_left_conjugate** 是 Mathlib 中的一个引理，位于命名
空间 `Unitary`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.commute_unitary_iff_star_left_conjugate {x u : R} (hu : u ∈ unitary R) :
    Commute u x ↔ star u * x * u = x := by
  simpa using! (Unitary.toUnits ⟨u, hu⟩).commute_iff_inv_mul_cancel
/-
**Unitary._root_.commute_unitary_iff_star_right_conjugate** 是 Mathlib 中的一个引理，位于命
名空间 `Unitary`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.commute_unitary_iff_star_right_conjugate {x u : R} (hu : u ∈ unitary R) :
    Commute u x ↔ u * x * star u = x := by
  simpa using! (Unitary.toUnits ⟨u, hu⟩).commute_iff_mul_inv_cancel

end Monoid

end Unitary

section Group

variable {G : Type*} [Group G] [StarMul G]

/-
**Unitary.inv_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Unitary.inv_mem {g : G} (hg : g in unitary G) : g⁻¹ in unitary G
参数：hg : g in unitary G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `star_inv`：star_inv [Group R] [StarMul R] (x : R) : star x⁻¹ = (star x)⁻¹
· 使用定理 `And.symm`：∀ {a b : Prop}, a ∧ b → b ∧ a
-/
theorem Unitary.inv_mem {g : G} (hg : g ∈ unitary G) : g⁻¹ ∈ unitary G := by
  simp_rw [mem_iff, star_inv, ← mul_inv_rev, inv_eq_one] at *
  exact hg.symm

variable (G) in
/-- `unitary` as a `Subgroup` of a group.

Note the group structure on this type is not defeq to the one on `unitary`.
This situation naturally arises when considering the unitary elements as a
subgroup of the group of units of a star monoid. -/
/-
**unitarySubgroup** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：unitarySubgroup : Subgroup G where toSubmonoid
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Unitary.inv_mem`：Unitary.inv_mem {g : G} (hg : g in unitary G) : g⁻¹ in 
unitary G

--- 原说明 ---
`unitary` as a `Subgroup` of a group.

Note the group structure on this type is not defeq to the one on `unitary`.
This situation naturally arises when considering the unitary elements as a
subgroup of the group of units of a star monoid.
-/
def unitarySubgroup : Subgroup G where
  toSubmonoid := unitary G
  inv_mem' := Unitary.inv_mem

@[simp]
/-
**unitarySubgroup_toSubmonoid** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：unitarySubgroup_toSubmonoid : (unitarySubgroup G).toSubmonoid = unitary G
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem unitarySubgroup_toSubmonoid : (unitarySubgroup G).toSubmonoid = unitary G := rfl

@[simp]
/-
**mem_unitarySubgroup_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_unitarySubgroup_iff {g : G} : g in unitarySubgroup G ↔ g in unitary G
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_unitarySubgroup_iff {g : G} : g ∈ unitarySubgroup G ↔ g ∈ unitary G :=
  Iff.rfl

nonrec theorem Unitary.inv_mem_iff {g : G} : g⁻¹ ∈ unitary G ↔ g ∈ unitary G :=
  inv_mem_iff (H := unitarySubgroup G)

end Group

namespace Unitary

section SMul

section

variable {A : Type*}
  [Monoid R] [Monoid A] [MulAction R A] [SMulCommClass R A A]
  [IsScalarTower R A A] [StarMul R] [StarMul A] [StarModule R A]

/-
**Unitary.smul_mem_of_mem** 是 Mathlib 中的一个引理，位于命名空间 `Unitary`。
形式化陈述：smul_mem_of_mem {r : R} {a : A} (hr : r in unitary R) (ha : a in unitary A
) : r • a in unitary A
参数：hr : r in unitary R；ha : a in unitary A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `StarModule.star_smul`：∀ {R : Type u} {A : Type v} {inst : Star R} {inst_
1 : Star A} {inst_2 : SMul R A} [self : StarModule R A] (r : R)   (a : A), star 
(r • a) = …
· 使用引理 `mul_smul_comm`：mul_smul_comm [Mul β] [SMul α β] [SMulCommClass α β β] (s
 : α) (x y : β) : x * s • y = s • (x * y)
· 使用引理 `smul_mul_assoc`：smul_mul_assoc [Mul β] [SMul α β] [IsScalarTower α β β] 
(r : α) (x y : β) : r • x * y = r • (x * y)
· 使用定理 `Unitary.star_mul_self_of_mem`：star_mul_self_of_mem {U : R} (hU : U in un
itary R) : star U * U = 1
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `Unitary.mul_star_self_of_mem`：mul_star_self_of_mem {U : R} (hU : U in un
itary R) : U * star U = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
lemma smul_mem_of_mem {r : R} {a : A} (hr : r ∈ unitary R) (ha : a ∈ unitary A) :
    r • a ∈ unitary A := by
  simp [mem_iff, smul_smul, mul_smul_comm, smul_mul_assoc, hr, ha]
/-
**Unitary.smul_mem** 是 Mathlib 中的一个引理，位于命名空间 `Unitary`。
形式化陈述：smul_mem (r : unitary R) {a : A} (ha : a in unitary A) : r • a in unitary 
A
参数：r : unitary R；ha : a in unitary A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Unitary.smul_mem_of_mem`：smul_mem_of_mem {r : R} {a : A} (hr : r in unit
ary R) (ha : a in unitary A) : r • a in unitary A
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
-/
lemma smul_mem (r : unitary R) {a : A} (ha : a ∈ unitary A) :
    r • a ∈ unitary A :=
  smul_mem_of_mem (R := R) r.prop ha
/-
**Unitary.** 是 Mathlib 中的一个实例，位于命名空间 `Unitary`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMul (unitary R) (unitary A) where
  smul r a := ⟨r • a, smul_mem r a.prop⟩

@[simp, norm_cast]
/-
**Unitary.coe_smul** 是 Mathlib 中的一个引理，位于命名空间 `Unitary`。
形式化陈述：coe_smul (r : unitary R) (a : unitary A) : ↑(r • a) = r • (a : A)
参数：r : unitary R；a : unitary A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_smul (r : unitary R) (a : unitary A) : ↑(r • a) = r • (a : A) := rfl
/-
**Unitary.** 是 Mathlib 中的一个实例，位于命名空间 `Unitary`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MulAction (unitary R) (unitary A) where
  one_smul _ := Subtype.ext <| one_smul ..
  mul_smul _ _ _ := Subtype.ext <| mul_smul ..
/-
**Unitary.** 是 Mathlib 中的一个实例，位于命名空间 `Unitary`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : StarModule (unitary R) (unitary A) where
  star_smul _ _ := Subtype.ext <| star_smul (_ : R) _

end

section

variable {S A : Type*}
  [Monoid R] [Monoid S] [Monoid A] [StarMul R] [StarMul S] [StarMul A]
  [MulAction R S] [MulAction R A] [MulAction S A]
  [StarModule R S] [StarModule R A] [StarModule S A]
  [IsScalarTower R A A] [IsScalarTower S A A]
  [SMulCommClass R A A] [SMulCommClass S A A]

/-
**Unitary.** 是 Mathlib 中的一个实例，位于命名空间 `Unitary`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMulCommClass R S A] : SMulCommClass (unitary R) (unitary S) (unitary A) where
  smul_comm _ _ _ := Subtype.ext <| smul_comm _ (_ : S) (_ : A)
/-
**Unitary.** 是 Mathlib 中的一个实例，位于命名空间 `Unitary`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsScalarTower R S S] [SMulCommClass R S S] [IsScalarTower R S A] :
    IsScalarTower (unitary R) (unitary S) (unitary A) where
  smul_assoc _ _ _ := Subtype.ext <| smul_assoc _ (_ : S) (_ : A)

end

end SMul

section Map

variable {R S T : Type*} [Monoid R] [StarMul R] [Monoid S] [StarMul S] [Monoid T] [StarMul T]

/-
**Unitary.map_mem** 是 Mathlib 中的一个引理，位于命名空间 `Unitary`。
形式化陈述：map_mem {F : Type*} [FunLike F R S] [StarHomClass F R S] [MonoidHomClass F
 R S] (f : F) {r : R} (hr : r in unitary R) : f r in unitary S
参数：f : F；hr : r in unitary R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `StarHomClass.map_star`：∀ {F : Type u_1} {R : outParam (Type u_2)} {S : o
utParam (Type u_3)} {inst : Star R} {inst_1 : Star S}   {inst_2 : FunLike F R S}
 [self : St…
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Unitary.mem_iff`：mem_iff {U : R} : U in unitary R ↔ star U * U = 1 ∧ U *
 star U = 1
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma map_mem {F : Type*} [FunLike F R S] [StarHomClass F R S] [MonoidHomClass F R S]
    (f : F) {r : R} (hr : r ∈ unitary R) : f r ∈ unitary S := by
  rw [mem_iff] at hr
  simpa [map_star, map_mul] using! And.intro congr(f $(hr.1)) congr(f $(hr.2))

/-- The star monoid homomorphism between unitary subgroups induced by a star monoid homomorphism of
the underlying star monoids. -/
@[simps]
/-
**Unitary.map** 是 Mathlib 中的一个定义，位于命名空间 `Unitary`。
形式化陈述：map (f : R ->⋆* S) : unitary R ->⋆* unitary S where toFun
参数：f : R ->⋆* S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The star monoid homomorphism between unitary subgroups induced by a star monoid 
homomorphism of
the underlying star monoids.
-/
def map (f : R →⋆* S) : unitary R →⋆* unitary S where
  toFun := Subtype.map f (fun _ ↦ map_mem f)
  map_one' := Subtype.ext <| map_one f
  map_mul' _ _ := Subtype.ext <| map_mul f _ _
  map_star' _ := Subtype.ext <| map_star f _

@[simp]
/-
**Unitary.coe_map** 是 Mathlib 中的一个引理，位于命名空间 `Unitary`。
形式化陈述：coe_map (f : R ->⋆* S) (x : unitary R) : map f x = f x
参数：f : R ->⋆* S；x : unitary R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_map (f : R →⋆* S) (x : unitary R) : map f x = f x := rfl

@[simp]
/-
**Unitary.coe_map_star** 是 Mathlib 中的一个引理，位于命名空间 `Unitary`。
形式化陈述：coe_map_star (f : R ->⋆* S) (x : unitary R) : map f (star x) = f (star x)
参数：f : R ->⋆* S；x : unitary R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_map_star (f : R →⋆* S) (x : unitary R) : map f (star x) = f (star x) := rfl

@[simp]
/-
**Unitary.map_id** 是 Mathlib 中的一个引理，位于命名空间 `Unitary`。
形式化陈述：map_id : map (.id R) = .id (unitary R)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map_id : map (.id R) = .id (unitary R) := rfl
/-
**Unitary.map_comp** 是 Mathlib 中的一个引理，位于命名空间 `Unitary`。
形式化陈述：map_comp (g : S ->⋆* T) (f : R ->⋆* S) : map (g.comp f) = (map g).comp (ma
p f)
参数：g : S ->⋆* T；f : R ->⋆* S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map_comp (g : S →⋆* T) (f : R →⋆* S) : map (g.comp f) = (map g).comp (map f) := rfl

@[simp]
/-
**Unitary.map_injective** 是 Mathlib 中的一个引理，位于命名空间 `Unitary`。
形式化陈述：map_injective {f : R ->⋆* S} (hf : Function.Injective f) : Function.Inject
ive (map f : unitary R -> unitary S)
参数：hf : Function.Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.map_injective`：map_injective {p : α -> Prop} {q : β -> Prop} {f 
: α -> β} (h : forall a, p a -> q (f a)) (hf : Injective f) : Injective (map f h
)
· 使用引理 `Unitary.map_mem`：map_mem {F : Type*} [FunLike F R S] [StarHomClass F R S
] [MonoidHomClass F R S] (f : F) {r : R} (hr : r in unitary R) : f r in unitary 
S
· 使用定理 `StarMonoidHom.instStarHomClass`：∀ {A : Type u_2} {B : Type u_3} [inst : 
Monoid A] [inst_1 : Star A] [inst_2 : Monoid B] [inst_3 : Star B],   StarHomClas
s (A →⋆* B) A B
· 使用定理 `StarMonoidHom.instMonoidHomClass`：∀ {A : Type u_2} {B : Type u_3} [inst 
: Monoid A] [inst_1 : Star A] [inst_2 : Monoid B] [inst_3 : Star B],   MonoidHom
Class (A →⋆* B) A B
-/
lemma map_injective {f : R →⋆* S} (hf : Function.Injective f) :
    Function.Injective (map f : unitary R → unitary S) :=
  Subtype.map_injective (fun _ ↦ map_mem f) hf
/-
**Unitary.toUnits_comp_map** 是 Mathlib 中的一个引理，位于命名空间 `Unitary`。
形式化陈述：toUnits_comp_map (f : R ->⋆* S) : toUnits.comp (map f).toMonoidHom = (Unit
s.map f.toMonoidHom).comp toUnits
参数：f : R ->⋆* S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.ext`：MonoidHom.ext [MulOne M] [MulOne N] ⦃f g : M ->* N⦄ (h : 
forall x, f x = g x) : f = g
· 使用定理 `Units.ext`：ext {u v : αˣ} (huv : u.val = v.val) : u = v
-/
lemma toUnits_comp_map (f : R →⋆* S) :
    toUnits.comp (map f).toMonoidHom = (Units.map f.toMonoidHom).comp toUnits := by
  ext; rfl

/-- The star monoid isomorphism between unitary subgroups induced by a star monoid isomorphism of
the underlying star monoids. -/
@[simps]
/-
**Unitary.mapEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Unitary`。
形式化陈述：mapEquiv (f : R ≃⋆* S) : unitary R ≃⋆* unitary S
参数：f : R ≃⋆* S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The star monoid isomorphism between unitary subgroups induced by a star monoid i
somorphism of
the underlying star monoids.
-/
def mapEquiv (f : R ≃⋆* S) : unitary R ≃⋆* unitary S :=
  { map f.toStarMonoidHom with
    toFun := map f.toStarMonoidHom
    invFun := map f.symm.toStarMonoidHom
    left_inv := fun _ ↦ Subtype.ext <| f.left_inv _
    right_inv := fun _ ↦ Subtype.ext <| f.right_inv _ }

@[simp]
/-
**Unitary.mapEquiv_refl** 是 Mathlib 中的一个引理，位于命名空间 `Unitary`。
形式化陈述：mapEquiv_refl : mapEquiv (.refl R) = .refl (unitary R)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mapEquiv_refl : mapEquiv (.refl R) = .refl (unitary R) := rfl

@[simp]
/-
**Unitary.mapEquiv_symm** 是 Mathlib 中的一个引理，位于命名空间 `Unitary`。
形式化陈述：mapEquiv_symm (f : R ≃⋆* S) : mapEquiv f.symm = (mapEquiv f).symm
参数：f : R ≃⋆* S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mapEquiv_symm (f : R ≃⋆* S) : mapEquiv f.symm = (mapEquiv f).symm := rfl

@[simp]
/-
**Unitary.mapEquiv_trans** 是 Mathlib 中的一个引理，位于命名空间 `Unitary`。
形式化陈述：mapEquiv_trans (f : R ≃⋆* S) (g : S ≃⋆* T) : mapEquiv (f.trans g) = (mapEq
uiv f).trans (mapEquiv g)
参数：f : R ≃⋆* S；g : S ≃⋆* T。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mapEquiv_trans (f : R ≃⋆* S) (g : S ≃⋆* T) :
    mapEquiv (f.trans g) = (mapEquiv f).trans (mapEquiv g) :=
  rfl

@[simp]
/-
**Unitary.toMonoidHom_mapEquiv** 是 Mathlib 中的一个引理，位于命名空间 `Unitary`。
形式化陈述：toMonoidHom_mapEquiv (f : R ≃⋆* S) : (mapEquiv f).toStarMonoidHom = map f.
toStarMonoidHom
参数：f : R ≃⋆* S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toMonoidHom_mapEquiv (f : R ≃⋆* S) :
    (mapEquiv f).toStarMonoidHom = map f.toStarMonoidHom :=
  rfl

/-- The unitary subgroup of the units is equivalent to the unitary elements of the monoid. -/
@[simps!]
/-
**Unitary._root_.unitarySubgroupUnitsEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Unitary`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The unitary subgroup of the units is equivalent to the unitary elements of the m
onoid.
-/
def _root_.unitarySubgroupUnitsEquiv {M : Type*} [Monoid M] [StarMul M] :
    unitarySubgroup Mˣ ≃* unitary M where
  toFun x := ⟨x.val, congr_arg Units.val x.prop.1, congr_arg Units.val x.prop.2⟩
  invFun x := ⟨⟨x, star x, x.prop.2, x.prop.1⟩, Units.ext x.prop.1, Units.ext x.prop.2⟩
  map_mul' _ _ := rfl
  left_inv _ := Subtype.ext <| Units.ext rfl
  right_inv _ := rfl

end Map

section CommMonoid

variable [CommMonoid R] [StarMul R]

/-
**Unitary.** 是 Mathlib 中的一个实例，位于命名空间 `Unitary`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CommGroup (unitary R) :=
  { (inferInstance : Group (unitary R)), Submonoid.toCommMonoid _ with }
/-
**Unitary.mem_iff_star_mul_self** 是 Mathlib 中的一个定理，位于命名空间 `Unitary`。
形式化陈述：mem_iff_star_mul_self {U : R} : U in unitary R ↔ star U * U = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Unitary.mem_iff`：mem_iff {U : R} : U in unitary R ↔ star U * U = 1 ∧ U *
 star U = 1
· 使用定理 `and_iff_left_of_imp`：∀ {a b : Prop}, (a → b) → (a ∧ b ↔ a)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem mem_iff_star_mul_self {U : R} : U ∈ unitary R ↔ star U * U = 1 :=
  mem_iff.trans <| and_iff_left_of_imp fun h => mul_comm (star U) U ▸ h
/-
**Unitary.mem_iff_self_mul_star** 是 Mathlib 中的一个定理，位于命名空间 `Unitary`。
形式化陈述：mem_iff_self_mul_star {U : R} : U in unitary R ↔ U * star U = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Unitary.mem_iff`：mem_iff {U : R} : U in unitary R ↔ star U * U = 1 ∧ U *
 star U = 1
· 使用定理 `and_iff_right_of_imp`：∀ {b a : Prop}, (b → a) → (a ∧ b ↔ b)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem mem_iff_self_mul_star {U : R} : U ∈ unitary R ↔ U * star U = 1 :=
  mem_iff.trans <| and_iff_right_of_imp fun h => mul_comm U (star U) ▸ h

end CommMonoid

section GroupWithZero

variable [GroupWithZero R] [StarMul R]

@[norm_cast]
/-
**Unitary.coe_inv** 是 Mathlib 中的一个定理，位于命名空间 `Unitary`。
形式化陈述：coe_inv (U : unitary R) : ↑U⁻¹ = (U⁻¹ : R)
参数：U : unitary R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_inv_of_mul_eq_one_right`：eq_inv_of_mul_eq_one_right (h : a * b = 1) :
 b = a⁻¹
· 使用定理 `Unitary.coe_mul_star_self`：coe_mul_star_self (U : unitary R) : (U : R) *
 star U = 1
-/
theorem coe_inv (U : unitary R) : ↑U⁻¹ = (U⁻¹ : R) :=
  eq_inv_of_mul_eq_one_right <| coe_mul_star_self _

@[norm_cast]
/-
**Unitary.coe_div** 是 Mathlib 中的一个定理，位于命名空间 `Unitary`。
形式化陈述：coe_div (U₁ U₂ : unitary R) : ↑(U₁ / U₂) = (U₁ / U₂ : R)
参数：U₁ U₂ : unitary R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Unitary.coe_inv`：coe_inv (U : unitary R) : ↑U⁻¹ = (U⁻¹ : R)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coe_div (U₁ U₂ : unitary R) : ↑(U₁ / U₂) = (U₁ / U₂ : R) := by
  simp only [div_eq_mul_inv, coe_inv, Submonoid.coe_mul]

@[norm_cast]
/-
**Unitary.coe_zpow** 是 Mathlib 中的一个定理，位于命名空间 `Unitary`。
形式化陈述：coe_zpow (U : unitary R) (z : Int) : ↑(U ^ z) = (U : R) ^ z
参数：U : unitary R；z : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zpow_negSucc`：zpow_negSucc (a : G) (n : Nat) : a ^ (Int.negSucc n) = (a 
^ (n + 1))⁻¹
· 使用定理 `Unitary.coe_inv`：coe_inv (U : unitary R) : ↑U⁻¹ = (U⁻¹ : R)
-/
theorem coe_zpow (U : unitary R) (z : ℤ) : ↑(U ^ z) = (U : R) ^ z := by
  cases z
  · simp [SubmonoidClass.coe_pow]
  · simp [coe_inv]

end GroupWithZero

section Ring

variable [Ring R] [StarRing R]

/-
**Unitary.** 是 Mathlib 中的一个实例，位于命名空间 `Unitary`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Neg (unitary R) where
  neg U :=
    ⟨-U, by simp [mem_iff, star_neg]⟩

@[norm_cast]
/-
**Unitary.coe_neg** 是 Mathlib 中的一个定理，位于命名空间 `Unitary`。
形式化陈述：coe_neg (U : unitary R) : ↑(-U) = (-U : R)
参数：U : unitary R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_neg (U : unitary R) : ↑(-U) = (-U : R) :=
  rfl
/-
**Unitary.** 是 Mathlib 中的一个实例，位于命名空间 `Unitary`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasDistribNeg (unitary R) :=
  Subtype.coe_injective.hasDistribNeg _ coe_neg (unitary R).coe_mul

end Ring

section UnitaryConjugate

universe u

variable {R A : Type*} [CommSemiring R] [Ring A] [Algebra R A] [StarMul A]

/-- Unitary conjugation preserves the spectrum, star on right. -/
@[simp]
/-
**Unitary.spectrum_star_right_conjugate** 是 Mathlib 中的一个引理，位于命名空间 `Unitary`。
形式化陈述：spectrum_star_right_conjugate {a : A} {U : unitary A} : spectrum R (U * a 
* (star U : A)) = spectrum R a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `spectrum.units_conjugate`：spectrum.units_conjugate {a : A} {u : Aˣ} : sp
ectrum R (u * a * u⁻¹) = spectrum R a

--- 原说明 ---
Unitary conjugation preserves the spectrum, star on right.
-/
lemma spectrum_star_right_conjugate {a : A} {U : unitary A} :
    spectrum R (U * a * (star U : A)) = spectrum R a :=
  spectrum.units_conjugate (u := toUnits U)

/-- Unitary conjugation preserves the spectrum, star on left. -/
@[simp]
/-
**Unitary.spectrum_star_left_conjugate** 是 Mathlib 中的一个引理，位于命名空间 `Unitary`。
形式化陈述：spectrum_star_left_conjugate {a : A} {U : unitary A} : spectrum R ((star U
 : A) * a * U) = spectrum R a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `star_star`：star_star [InvolutiveStar R] (r : R) : star (star r) = r
· 使用引理 `Unitary.spectrum_star_right_conjugate`：spectrum_star_right_conjugate {a 
: A} {U : unitary A} : spectrum R (U * a * (star U : A)) = spectrum R a

--- 原说明 ---
Unitary conjugation preserves the spectrum, star on left.
-/
lemma spectrum_star_left_conjugate {a : A} {U : unitary A} :
    spectrum R ((star U : A) * a * U) = spectrum R a := by
  simpa using spectrum_star_right_conjugate (U := star U)

end UnitaryConjugate

/-- In a ring without zero divisors and with trivial star, the only unitary elements are `1`
and `-1`. -/
/-
**Unitary.mem_iff_eq_one_or_eq_neg_one** 是 Mathlib 中的一个定理，位于命名空间 `Unitary`。
形式化陈述：mem_iff_eq_one_or_eq_neg_one [Ring R] [StarRing R] [TrivialStar R] [NoZero
Divisors R] {a : R} : a in unitary R ↔ a = 1 ∨ a = -1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `TrivialStar.star_trivial`：∀ {R : Type u} {inst : Star R} [self : Trivial
Star R] (r : R), star r = r
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
In a ring without zero divisors and with trivial star, the only unitary elements
 are `1`
and `-1`.
-/
theorem mem_iff_eq_one_or_eq_neg_one [Ring R] [StarRing R] [TrivialStar R] [NoZeroDivisors R]
    {a : R} : a ∈ unitary R ↔ a = 1 ∨ a = -1 := by
  simp [mem_iff, mul_self_eq_one_iff]

end Unitary

/-
**IsStarProjection.two_mul_sub_one_mem_unitary** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsStarProjection.two_mul_sub_one_mem_unitary {R : Type*} [Ring R] [StarRin
g R] {p : R} (hp : IsStarProjection p) : 2 * p - 1 in unitary R
参数：hp : IsStarProjection p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `star_sub`：star_sub [AddGroup R] [StarAddMonoid R] (r s : R) : star (r - 
s) = star r - star s
· 使用定理 `StarAddMonoid.star_add`：∀ {R : Type u} {inst : AddMonoid R} [self : Star
AddMonoid R] (r s : R), star (r + s) = star r + star s
· 使用定理 `IsSelfAdjoint.star_eq`：star_eq [Star R] {x : R} (hx : IsSelfAdjoint x) :
 star x = x
· 使用定理 `IsStarProjection.isSelfAdjoint`：∀ {R : Type u_1} [inst : Mul R] [inst_1 
: Star R] {p : R}, IsStarProjection p → IsSelfAdjoint p
· 使用定理 `star_one`：star_one [MulOneClass R] [StarMul R] : star (1 : R) = 1
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `sub_mul`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), (a
 - b) * c = a * c - b * c
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用引理 `IsIdempotentElem.eq`：eq (ha : IsIdempotentElem a) : a * a = a
· 使用定理 `IsStarProjection.isIdempotentElem`：∀ {R : Type u_1} [inst : Mul R] [inst
_1 : Star R] {p : R}, IsStarProjection p → IsIdempotentElem p
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `sub_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a - 
(a - b) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem IsStarProjection.two_mul_sub_one_mem_unitary {R : Type*} [Ring R] [StarRing R] {p : R}
    (hp : IsStarProjection p) : 2 * p - 1 ∈ unitary R := by
  simp only [two_mul, Unitary.mem_iff, star_sub, star_add,
    hp.isSelfAdjoint.star_eq, star_one, mul_sub, mul_add,
    sub_mul, add_mul, hp.isIdempotentElem.eq, one_mul, add_sub_cancel_right,
    mul_one, sub_sub_cancel, and_self]
