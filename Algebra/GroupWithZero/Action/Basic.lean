/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Group.Action.End
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Group.Action.Prod
public import Mathlib.Algebra.GroupWithZero.Prod

/-!
# Definitions of group actions

This file defines a hierarchy of group action type-classes on top of the previously defined
notation classes `SMul` and its additive version `VAdd`:

* `MulAction M α` and its additive version `AddAction G P` are typeclasses used for
  actions of multiplicative and additive monoids and groups; they extend notation classes
  `SMul` and `VAdd` that are defined in `Algebra.Group.Defs`;
* `DistribMulAction M A` is a typeclass for an action of a multiplicative monoid on
  an additive monoid such that `a • (b + c) = a • b + a • c` and `a • 0 = 0`.

The hierarchy is extended further by `Module`, defined elsewhere.

Also provided are typeclasses for faithful and transitive actions, and typeclasses regarding the
interaction of different group actions,

* `SMulCommClass M N α` and its additive version `VAddCommClass M N α`;
* `IsScalarTower M N α` and its additive version `VAddAssocClass M N α`;
* `IsCentralScalar M α` and its additive version `IsCentralVAdd M N α`.

## Notation

- `a • b` is used as notation for `SMul.smul a b`.
- `a +ᵥ b` is used as notation for `VAdd.vadd a b`.

## Implementation details

This file should avoid depending on other parts of `GroupTheory`, to avoid import cycles.
More sophisticated lemmas belong in `GroupTheory.GroupAction`.

## Tags

group action
-/

@[expose] public section

assert_not_exists Ring

open Function

variable {G G₀ A M M₀ N₀ R α : Type*}

section GroupWithZero
variable [GroupWithZero G₀] [MulAction G₀ α] {a : G₀}

/-
**MulAction.bijective** 是 Mathlib 中的一个定理，位于命名空间 `MulAction`。
形式化陈述：∀ {α : Type u_5} {β : Type u_6} [inst : Group α] [inst_1 : MulAction α β] 
(g : α), Function.Bijective fun x => g • x
参数：g : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.bijective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Bijec
tive ⇑e
-/
protected lemma MulAction.bijective₀ (ha : a ≠ 0) : Bijective (a • · : α → α) :=
  MulAction.bijective <| Units.mk0 a ha
/-
**MulAction.injective** 是 Mathlib 中的一个定理，位于命名空间 `MulAction`。
形式化陈述：∀ {α : Type u_5} {β : Type u_6} [inst : Group α] [inst_1 : MulAction α β] 
(g : α), Function.Injective fun x => g • x
参数：g : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Bijective.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β
}, Function.Bijective f → Function.Injective f
· 使用定理 `MulAction.bijective`：∀ {α : Type u_5} {β : Type u_6} [inst : Group α] [i
nst_1 : MulAction α β] (g : α), Function.Bijective fun x => g • x
-/
protected lemma MulAction.injective₀ (ha : a ≠ 0) : Injective (a • · : α → α) :=
  (MulAction.bijective₀ ha).injective
/-
**MulAction.surjective** 是 Mathlib 中的一个定理，位于命名空间 `MulAction`。
形式化陈述：∀ {α : Type u_5} {β : Type u_6} [inst : Group α] [inst_1 : MulAction α β] 
(g : α), Function.Surjective fun x => g • x
参数：g : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Bijective.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → 
β}, Function.Bijective f → Function.Surjective f
· 使用定理 `MulAction.bijective`：∀ {α : Type u_5} {β : Type u_6} [inst : Group α] [i
nst_1 : MulAction α β] (g : α), Function.Bijective fun x => g • x
-/
protected lemma MulAction.surjective₀ (ha : a ≠ 0) : Surjective (a • · : α → α) :=
  (MulAction.bijective₀ ha).surjective

end GroupWithZero

section DistribMulAction
variable [Group G] [Monoid M] [AddMonoid A]
variable (A)

/-- Each element of the group defines an additive monoid isomorphism.

This is a stronger version of `MulAction.toPerm`. -/
@[simps +simpRhs]
/-
**DistribMulAction.toAddEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：DistribMulAction.toAddEquiv [DistribMulAction G A] (x : G) : A ≃+ A where 
__
参数：x : G。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.left_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Function
.LeftInverse self.invFun self.toFun
· 使用定理 `Equiv.right_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Functio
n.RightInverse self.invFun self.toFun

--- 原说明 ---
Each element of the group defines an additive monoid isomorphism.

This is a stronger version of `MulAction.toPerm`.
-/
def DistribMulAction.toAddEquiv [DistribMulAction G A] (x : G) : A ≃+ A where
  __ := DistribSMul.toAddMonoidHom A x
  __ := MulAction.toPermHom G A x

variable (G)

/-- Each element of the group defines an additive monoid isomorphism.

This is a stronger version of `MulAction.toPermHom`. -/
@[simps]
/-
**DistribMulAction.toAddAut** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：DistribMulAction.toAddAut [DistribMulAction G A] : G ->* Multiplicative (A
ddAut A) where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Each element of the group defines an additive monoid isomorphism.

This is a stronger version of `MulAction.toPermHom`.
-/
def DistribMulAction.toAddAut [DistribMulAction G A] : G →* Multiplicative (AddAut A) where
  toFun := toAddEquiv _
  map_one' := AddEquiv.ext (one_smul _)
  map_mul' _ _ := AddEquiv.ext (mul_smul _ _)

end DistribMulAction

/-- Scalar multiplication as a monoid homomorphism with zero. -/
@[simps]
/-
**smulMonoidWithZeroHom** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：smulMonoidWithZeroHom [MonoidWithZero M₀] [MulZeroOneClass N₀] [MulActionW
ithZero M₀ N₀] [IsScalarTower M₀ N₀ N₀] [SMulCommClass M₀ N₀ N₀] : M₀ × N₀ ->*₀ 
N₀
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Scalar multiplication as a monoid homomorphism with zero.
-/
def smulMonoidWithZeroHom [MonoidWithZero M₀] [MulZeroOneClass N₀] [MulActionWithZero M₀ N₀]
    [IsScalarTower M₀ N₀ N₀] [SMulCommClass M₀ N₀ N₀] : M₀ × N₀ →*₀ N₀ :=
  { smulMonoidHom with map_zero' := smul_zero _ }
/-
**IsUnit.smul_sub_iff_sub_inv_smul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsUnit.smul_sub_iff_sub_inv_smul [Group G] [Monoid R] [AddGroup R] [Distri
bMulAction G R] [IsScalarTower G R R] [SMulCommClass G R R] (r : G) (a : R) : Is
Unit (r • (1 : R) - a) ↔ IsUnit (1 - r⁻¹ • a)
参数：r : G；a : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isUnit_smul_iff`：∀ {α : Type u_5} {β : Type u_6} [inst : Group α] [inst_
1 : Monoid β] [inst_2 : MulAction α β] [SMulCommClass α β β]   [IsScalarTower α 
β β] …
· 使用定理 `smul_sub`：smul_sub (r : M) (x y : A) : r • (x - y) = r • x - r • y
· 使用引理 `smul_inv_smul`：smul_inv_smul (g : G) (a : α) : g • g⁻¹ • a = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma IsUnit.smul_sub_iff_sub_inv_smul [Group G] [Monoid R] [AddGroup R] [DistribMulAction G R]
    [IsScalarTower G R R] [SMulCommClass G R R] (r : G) (a : R) :
    IsUnit (r • (1 : R) - a) ↔ IsUnit (1 - r⁻¹ • a) := by
  rw [← isUnit_smul_iff r (1 - r⁻¹ • a), smul_sub, smul_inv_smul]
/-
**div_smul_div_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：div_smul_div_comm [Group G] [GroupWithZero G₀] [MulAction G G₀] [IsScalarT
ower G G₀ G₀] [SMulCommClass G G₀ G₀] (g h : G) (a b : G₀) : (g / h) • (a / b) =
 (g • a) / (h • b)
参数：g h : G；a b : G₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ne_of_apply_ne`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) {x y : α}, f
 x ≠ f y → x ≠ y
· 使用引理 `inv_smul_smul`：inv_smul_smul (g : G) (a : α) : g⁻¹ • g • a = a
· 使用引理 `eq_div_iff_mul_eq`：eq_div_iff_mul_eq (hc : c != 0) : a = b / c ↔ a * c =
 b
· 使用引理 `smul_mul_smul_comm`：smul_mul_smul_comm [Mul α] [Mul β] [SMul α β] [IsSca
larTower α β β] [IsScalarTower α α β] [SMulCommClass α β β] (a : α) (b : β) (c :
 α) (d :…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `div_mul_cancel`：div_mul_cancel (a b : G) : a / b * b = a
· 使用定理 `IsUnit.div_mul_cancel`：∀ {α : Type u} [inst : DivisionMonoid α] {b : α},
 IsUnit b → ∀ (a : α), a / b * b = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem div_smul_div_comm [Group G] [GroupWithZero G₀] [MulAction G G₀]
    [IsScalarTower G G₀ G₀] [SMulCommClass G G₀ G₀] (g h : G) (a b : G₀) :
    (g / h) • (a / b) = (g • a) / (h • b) := by
  have (x : G) : x • (0 : G₀) = 0 := by simpa using (smul_assoc x (0 : G₀) (0 : G₀)).symm
  by_cases hb : b = 0
  · simp [hb, this]
  have : h • b ≠ 0 := by
    refine (ne_of_apply_ne (h⁻¹ • ·) ?_)
    simpa [this]
  rw [eq_div_iff_mul_eq this, smul_mul_smul_comm]
  simp [hb]
/-
**smul_zpow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：smul_zpow (g : G) (a : H) (n : Int) : (g • a) ^ n = g ^ n • a ^ n
参数：g : G；a : H；n : Int。
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
· 使用定理 `smul_pow`：∀ {M : Type u_1} {N : Type u_2} [inst : Monoid M] [inst_1 : Mo
noid N] [inst_2 : MulAction M N] [IsScalarTower M N N]   [SMulCommClass M N N]…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zpow_negSucc`：zpow_negSucc (a : G) (n : Nat) : a ^ (Int.negSucc n) = (a 
^ (n + 1))⁻¹
· 使用引理 `smul_inv`：smul_inv (g : G) (a : H) : (g • a)⁻¹ = g⁻¹ • a⁻¹
-/
@[simp] theorem smul_zpow₀' [Group G] [GroupWithZero G₀] [MulDistribMulAction G G₀]
    (g : G) (x : G₀) (n : ℤ) : g • (x ^ n) = (g • x) ^ n := by
  cases n <;> simp
