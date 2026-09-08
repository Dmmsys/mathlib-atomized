/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Patrick Massot, Eric Wieser
-/
module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Notation.Pi.Basic
public import Mathlib.Data.Sum.Basic
public import Mathlib.Logic.Unique
public import Mathlib.Tactic.Spread

/-!
# Instances and theorems on pi types

This file provides instances for the typeclass defined in `Algebra.Group.Defs`. More sophisticated
instances are defined in `Algebra.Group.Pi.Lemmas` files elsewhere.

## Porting note

This file relied on the `pi_instance` tactic, which was not available at the time of porting. The
comment `--pi_instance` is inserted before all fields which were previously derived by
`pi_instance`. See this Zulip discussion:
[https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/not.20porting.20pi_instance]
-/

@[expose] public section

-- We enforce to only import `Algebra.Group.Defs` and basic logic
assert_not_exists Set.range MonoidHom MonoidWithZero DenselyOrdered

universe u v₁ v₂ v₃

variable {I : Type u}

-- The indexing type
variable {α β γ : Type*}

-- The families of types already equipped with instances
variable {f : I → Type v₁} {g : I → Type v₂} {h : I → Type v₃}
variable (x y : ∀ i, f i) (i : I)

namespace Pi

@[to_additive]
/-
**Pi.isMulCommutative** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
形式化陈述：isMulCommutative [forall i, Mul (f i)] [forall i, IsMulCommutative (f i)] 
: IsMulCommutative (forall i, f i) where is_comm.comm _ _
参数：f i；f i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `mul_comm'`：mul_comm' {M : Type*} [Mul M] [IsMulCommutative M] (a b : M) 
: a * b = b * a
-/
instance isMulCommutative [∀ i, Mul (f i)] [∀ i, IsMulCommutative (f i)] :
    IsMulCommutative (∀ i, f i) where
  is_comm.comm _ _ := by ext; apply mul_comm'

@[to_additive]
/-
**Pi.commMagma** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
形式化陈述：commMagma [forall i, CommMagma (f i)] : CommMagma (forall i, f i) where mu
l_comm _ _
参数：f i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance commMagma [∀ i, CommMagma (f i)] : CommMagma (∀ i, f i) where
  mul_comm _ _ := by ext; apply mul_comm

@[to_additive]
/-
**Pi.semigroup** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
形式化陈述：semigroup [forall i, Semigroup (f i)] : Semigroup (forall i, f i) where mu
l_assoc
参数：f i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance semigroup [∀ i, Semigroup (f i)] : Semigroup (∀ i, f i) where
  mul_assoc := by intros; ext; exact mul_assoc _ _ _

@[to_additive]
/-
**Pi.commSemigroup** 是 Mathlib 中的一个定义，位于命名空间 `Pi`。
形式化陈述：{I : Type u} → {f : I → Type v₁} → [(i : I) → CommSemigroup (f i)] → CommS
emigroup ((i : I) → f i)
参数：i : I；f i；(i : I) → f i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance commSemigroup [∀ i, CommSemigroup (f i)] : CommSemigroup (∀ i, f i) where

@[to_additive]
/-
**Pi.mulOneClass** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
形式化陈述：mulOneClass [forall i, MulOneClass (f i)] : MulOneClass (forall i, f i) wh
ere one_mul
参数：f i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance mulOneClass [∀ i, MulOneClass (f i)] : MulOneClass (∀ i, f i) where
  one_mul := by intros; ext; exact one_mul _
  mul_one := by intros; ext; exact mul_one _

@[to_additive]
/-
**Pi.invOneClass** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
形式化陈述：invOneClass [forall i, InvOneClass (f i)] : InvOneClass (forall i, f i) wh
ere inv_one
参数：f i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance invOneClass [∀ i, InvOneClass (f i)] : InvOneClass (∀ i, f i) where
  inv_one := by ext; exact inv_one

@[to_additive]
/-
**Pi.monoid** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
形式化陈述：monoid [forall i, Monoid (f i)] : Monoid (forall i, f i) where __
参数：f i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance monoid [∀ i, Monoid (f i)] : Monoid (∀ i, f i) where
  __ := semigroup
  __ := mulOneClass
  npow := fun n x i => x i ^ n
  npow_zero := by intros; ext; exact Monoid.npow_zero _
  npow_succ := by intros; ext; exact Monoid.npow_succ _ _

@[to_additive]
/-
**Pi.commMonoid** 是 Mathlib 中的一个定义，位于命名空间 `Pi`。
形式化陈述：{I : Type u} → {f : I → Type v₁} → [(i : I) → CommMonoid (f i)] → CommMono
id ((i : I) → f i)
参数：i : I；f i；(i : I) → f i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance commMonoid [∀ i, CommMonoid (f i)] : CommMonoid (∀ i, f i) where

@[to_additive Pi.subNegMonoid]
/-
**Pi.divInvMonoid** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
形式化陈述：divInvMonoid [forall i, DivInvMonoid (f i)] : DivInvMonoid (forall i, f i)
 where zpow
参数：f i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance divInvMonoid [∀ i, DivInvMonoid (f i)] : DivInvMonoid (∀ i, f i) where
  zpow := fun z x i => x i ^ z
  div_eq_mul_inv := by intros; ext; exact div_eq_mul_inv _ _
  zpow_zero' := by intros; ext; exact DivInvMonoid.zpow_zero' _
  zpow_succ' := by intros; ext; exact DivInvMonoid.zpow_succ' _ _
  zpow_neg' := by intros; ext; exact DivInvMonoid.zpow_neg' _ _

@[to_additive]
/-
**Pi.divInvOneMonoid** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
形式化陈述：divInvOneMonoid [forall i, DivInvOneMonoid (f i)] : DivInvOneMonoid (foral
l i, f i) where inv_one
参数：f i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance divInvOneMonoid [∀ i, DivInvOneMonoid (f i)] : DivInvOneMonoid (∀ i, f i) where
  inv_one := by ext; exact inv_one

@[to_additive]
/-
**Pi.involutiveInv** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
形式化陈述：involutiveInv [forall i, InvolutiveInv (f i)] : InvolutiveInv (forall i, f
 i) where inv_inv
参数：f i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance involutiveInv [∀ i, InvolutiveInv (f i)] : InvolutiveInv (∀ i, f i) where
  inv_inv := by intros; ext; exact inv_inv _

@[to_additive]
/-
**Pi.divisionMonoid** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
形式化陈述：divisionMonoid [forall i, DivisionMonoid (f i)] : DivisionMonoid (forall i
, f i) where __
参数：f i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance divisionMonoid [∀ i, DivisionMonoid (f i)] : DivisionMonoid (∀ i, f i) where
  __ := divInvMonoid
  __ := involutiveInv
  mul_inv_rev := by intros; ext; exact mul_inv_rev _ _
  inv_eq_of_mul := by intro _ _ h; ext; exact DivisionMonoid.inv_eq_of_mul _ _ (congrFun h _)

@[to_additive instSubtractionCommMonoid]
/-
**Pi.divisionCommMonoid** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
形式化陈述：divisionCommMonoid [forall i, DivisionCommMonoid (f i)] : DivisionCommMono
id (forall i, f i)
参数：f i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance divisionCommMonoid [∀ i, DivisionCommMonoid (f i)] : DivisionCommMonoid (∀ i, f i) :=
  { divisionMonoid, commSemigroup with }

@[to_additive]
/-
**Pi.group** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
形式化陈述：group [forall i, Group (f i)] : Group (forall i, f i) where inv_mul_cancel
参数：f i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance group [∀ i, Group (f i)] : Group (∀ i, f i) where
  inv_mul_cancel := by intros; ext; exact inv_mul_cancel _

@[to_additive]
/-
**Pi.commGroup** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
形式化陈述：commGroup [forall i, CommGroup (f i)] : CommGroup (forall i, f i)
参数：f i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance commGroup [∀ i, CommGroup (f i)] : CommGroup (∀ i, f i) := { group, commMonoid with }
/-
**Pi.instIsLeftCancelMul** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：∀ {I : Type u} {f : I → Type v₁} [inst : (i : I) → Mul (f i)] [∀ (i : I), 
IsLeftCancelMul (f i)],   IsLeftCancelMul ((i : I) → f i)
参数：i : I；f i；i : I；f i；(i : I) → f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_left_cancel`：mul_left_cancel : a * b = a * c -> b = c
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
-/
@[to_additive] instance instIsLeftCancelMul [∀ i, Mul (f i)] [∀ i, IsLeftCancelMul (f i)] :
    IsLeftCancelMul (∀ i, f i) where
  mul_left_cancel _ _ _ h := funext fun _ ↦ mul_left_cancel (congr_fun h _)
/-
**Pi.instIsRightCancelMul** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：∀ {I : Type u} {f : I → Type v₁} [inst : (i : I) → Mul (f i)] [∀ (i : I), 
IsRightCancelMul (f i)],   IsRightCancelMul ((i : I) → f i)
参数：i : I；f i；i : I；f i；(i : I) → f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_right_cancel`：mul_right_cancel : a * b = c * b -> a = c
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
-/
@[to_additive] instance instIsRightCancelMul [∀ i, Mul (f i)] [∀ i, IsRightCancelMul (f i)] :
    IsRightCancelMul (∀ i, f i) where
  mul_right_cancel _ _ _ h := funext fun _ ↦ mul_right_cancel (congr_fun h _)
/-
**Pi.instIsCancelMul** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：∀ {I : Type u} {f : I → Type v₁} [inst : (i : I) → Mul (f i)] [∀ (i : I), 
IsCancelMul (f i)],   IsCancelMul ((i : I) → f i)
参数：i : I；f i；i : I；f i；(i : I) → f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Pi.instIsLeftCancelMul`：∀ {I : Type u} {f : I → Type v₁} [inst : (i : I)
 → Mul (f i)] [∀ (i : I), IsLeftCancelMul (f i)],   IsLeftCancelMul ((i : I) → f
 i)
· 使用定理 `IsCancelMul.toIsLeftCancelMul`：∀ {G : Type u} {inst : Mul G} [self : IsC
ancelMul G], IsLeftCancelMul G
· 使用定理 `Pi.instIsRightCancelMul`：∀ {I : Type u} {f : I → Type v₁} [inst : (i : I
) → Mul (f i)] [∀ (i : I), IsRightCancelMul (f i)],   IsRightCancelMul ((i : I) 
→ f i)
· 使用定理 `IsCancelMul.toIsRightCancelMul`：∀ {G : Type u} {inst : Mul G} [self : Is
CancelMul G], IsRightCancelMul G
-/
@[to_additive] instance instIsCancelMul [∀ i, Mul (f i)] [∀ i, IsCancelMul (f i)] :
    IsCancelMul (∀ i, f i) where

@[to_additive]
/-
**Pi.leftCancelSemigroup** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
形式化陈述：leftCancelSemigroup [forall i, LeftCancelSemigroup (f i)] : LeftCancelSemi
group (forall i, f i)
参数：f i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance leftCancelSemigroup [∀ i, LeftCancelSemigroup (f i)] : LeftCancelSemigroup (∀ i, f i) :=
  { semigroup with mul_left_cancel := fun _ _ _ => mul_left_cancel }

@[to_additive]
/-
**Pi.rightCancelSemigroup** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
形式化陈述：rightCancelSemigroup [forall i, RightCancelSemigroup (f i)] : RightCancelS
emigroup (forall i, f i)
参数：f i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance rightCancelSemigroup [∀ i, RightCancelSemigroup (f i)] : RightCancelSemigroup (∀ i, f i) :=
  { semigroup with mul_right_cancel := fun _ _ _ => mul_right_cancel }

@[to_additive]
/-
**Pi.leftCancelMonoid** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
形式化陈述：leftCancelMonoid [forall i, LeftCancelMonoid (f i)] : LeftCancelMonoid (fo
rall i, f i)
参数：f i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance leftCancelMonoid [∀ i, LeftCancelMonoid (f i)] : LeftCancelMonoid (∀ i, f i) :=
  { leftCancelSemigroup, monoid with }

@[to_additive]
/-
**Pi.rightCancelMonoid** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
形式化陈述：rightCancelMonoid [forall i, RightCancelMonoid (f i)] : RightCancelMonoid 
(forall i, f i)
参数：f i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance rightCancelMonoid [∀ i, RightCancelMonoid (f i)] : RightCancelMonoid (∀ i, f i) :=
  { rightCancelSemigroup, monoid with }

@[to_additive]
/-
**Pi.cancelMonoid** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
形式化陈述：cancelMonoid [forall i, CancelMonoid (f i)] : CancelMonoid (forall i, f i)
参数：f i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance cancelMonoid [∀ i, CancelMonoid (f i)] : CancelMonoid (∀ i, f i) :=
  { leftCancelMonoid, rightCancelMonoid with }

@[to_additive]
/-
**Pi.cancelCommMonoid** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
形式化陈述：cancelCommMonoid [forall i, CancelCommMonoid (f i)] : CancelCommMonoid (fo
rall i, f i)
参数：f i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance cancelCommMonoid [∀ i, CancelCommMonoid (f i)] : CancelCommMonoid (∀ i, f i) :=
  { leftCancelMonoid, commMonoid with }

end Pi

namespace Function

section Extend

@[to_additive]
/-
**Function.extend_one** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：extend_one [One γ] (f : α -> β) : Function.extend f (1 : α -> γ) (1 : β ->
 γ) = 1
参数：f : α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
-/
theorem extend_one [One γ] (f : α → β) : Function.extend f (1 : α → γ) (1 : β → γ) = 1 :=
  funext fun _ => by apply ite_self

@[to_additive]
/-
**Function.extend_mul** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：extend_mul [Mul γ] (f : α -> β) (g₁ g₂ : α -> γ) (e₁ e₂ : β -> γ) : Functi
on.extend f (g₁ * g₂) (e₁ * e₂) = Function.extend f g₁ e₁ * Function.extend f g₂
 e₂
参数：f : α -> β；g₁ g₂ : α -> γ；e₁ e₂ : β -> γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.extend_def`：extend_def (f : α -> β) (g : α -> γ) (e' : β -> γ) 
(b : β) [Decidable (exists a, f a = b)] : extend f g e' b = if h : exists a, f a
 = b then…
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `apply_dite₂`：apply_dite₂ {α β γ : Sort*} (f : α -> β -> γ) (P : Prop) [D
ecidable P] (a : P -> α) (b : ¬P -> α) (c : P -> β) (d : ¬P -> β) : f (dite P a 
b…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
-/
theorem extend_mul [Mul γ] (f : α → β) (g₁ g₂ : α → γ) (e₁ e₂ : β → γ) :
    Function.extend f (g₁ * g₂) (e₁ * e₂) = Function.extend f g₁ e₁ * Function.extend f g₂ e₂ := by
  classical
  funext x
  simp [Function.extend_def, apply_dite₂]

@[to_additive]
/-
**Function.extend_inv** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：extend_inv [Inv γ] (f : α -> β) (g : α -> γ) (e : β -> γ) : Function.exten
d f g⁻¹ e⁻¹ = (Function.extend f g e)⁻¹
参数：f : α -> β；g : α -> γ；e : β -> γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.extend_def`：extend_def (f : α -> β) (g : α -> γ) (e' : β -> γ) 
(b : β) [Decidable (exists a, f a = b)] : extend f g e' b = if h : exists a, f a
 = b then…
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `apply_dite`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [inst
 : Decidable P] (x : P → α) (y : ¬P → α),   f (dite P x y) = if h : P then f (x 
…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem extend_inv [Inv γ] (f : α → β) (g : α → γ) (e : β → γ) :
    Function.extend f g⁻¹ e⁻¹ = (Function.extend f g e)⁻¹ := by
  classical
  funext x
  simp [Function.extend_def, apply_dite Inv.inv]

@[to_additive]
/-
**Function.extend_div** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：extend_div [Div γ] (f : α -> β) (g₁ g₂ : α -> γ) (e₁ e₂ : β -> γ) : Functi
on.extend f (g₁ / g₂) (e₁ / e₂) = Function.extend f g₁ e₁ / Function.extend f g₂
 e₂
参数：f : α -> β；g₁ g₂ : α -> γ；e₁ e₂ : β -> γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.extend_def`：extend_def (f : α -> β) (g : α -> γ) (e' : β -> γ) 
(b : β) [Decidable (exists a, f a = b)] : extend f g e' b = if h : exists a, f a
 = b then…
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `apply_dite₂`：apply_dite₂ {α β γ : Sort*} (f : α -> β -> γ) (P : Prop) [D
ecidable P] (a : P -> α) (b : ¬P -> α) (c : P -> β) (d : ¬P -> β) : f (dite P a 
b…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
-/
theorem extend_div [Div γ] (f : α → β) (g₁ g₂ : α → γ) (e₁ e₂ : β → γ) :
    Function.extend f (g₁ / g₂) (e₁ / e₂) = Function.extend f g₁ e₁ / Function.extend f g₂ e₂ := by
  classical
  funext x
  simp [Function.extend_def, apply_dite₂]

end Extend

/-
**Function.comp_eq_const_iff** 是 Mathlib 中的一个引理，位于命名空间 `Function`。
形式化陈述：comp_eq_const_iff (b : β) (f : α -> β) {g : β -> γ} (hg : Injective g) : g
 ∘ f = Function.const _ (g b) ↔ f = Function.const _ b
参数：b : β；f : α -> β；hg : Injective g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Injective f → ∀ {a b : α} {c : β}, f b = c → (f a = c ↔ a = b)
· 使用定理 `Function.Injective.comp_left`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort 
u_3} {g : β → γ}, Function.Injective g → Function.Injective fun x => g ∘ x
-/
lemma comp_eq_const_iff (b : β) (f : α → β) {g : β → γ} (hg : Injective g) :
    g ∘ f = Function.const _ (g b) ↔ f = Function.const _ b :=
  hg.comp_left.eq_iff' rfl

@[to_additive]
/-
**Function.comp_eq_one_iff** 是 Mathlib 中的一个引理，位于命名空间 `Function`。
形式化陈述：comp_eq_one_iff [One β] [One γ] (f : α -> β) {g : β -> γ} (hg : Injective 
g) (hg0 : g 1 = 1) : g ∘ f = 1 ↔ f = 1
参数：f : α -> β；hg : Injective g；hg0 : g 1 = 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Function.comp_eq_const_iff`：comp_eq_const_iff (b : β) (f : α -> β) {g : 
β -> γ} (hg : Injective g) : g ∘ f = Function.const _ (g b) ↔ f = Function.const
 _ b
-/
lemma comp_eq_one_iff [One β] [One γ] (f : α → β) {g : β → γ} (hg : Injective g) (hg0 : g 1 = 1) :
    g ∘ f = 1 ↔ f = 1 := by
  simpa [hg0, const_one] using comp_eq_const_iff 1 f hg

@[to_additive]
/-
**Function.comp_ne_one_iff** 是 Mathlib 中的一个引理，位于命名空间 `Function`。
形式化陈述：comp_ne_one_iff [One β] [One γ] (f : α -> β) {g : β -> γ} (hg : Injective 
g) (hg0 : g 1 = 1) : g ∘ f != 1 ↔ f != 1
参数：f : α -> β；hg : Injective g；hg0 : g 1 = 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.ne`：∀ {α : Sort u_1} {β : Sort u_2} {a b : α} {c d : β}, (a = b ↔ c 
= d) → (a ≠ b ↔ c ≠ d)
· 使用引理 `Function.comp_eq_one_iff`：comp_eq_one_iff [One β] [One γ] (f : α -> β) {
g : β -> γ} (hg : Injective g) (hg0 : g 1 = 1) : g ∘ f = 1 ↔ f = 1
-/
lemma comp_ne_one_iff [One β] [One γ] (f : α → β) {g : β → γ} (hg : Injective g) (hg0 : g 1 = 1) :
    g ∘ f ≠ 1 ↔ f ≠ 1 :=
  (comp_eq_one_iff f hg hg0).ne

end Function

/-- If the one function is surjective, the codomain is trivial. -/
@[to_additive (attr := instance_reducible)
  /-- If the zero function is surjective, the codomain is trivial. -/]
/-
**uniqueOfSurjectiveOne** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：uniqueOfSurjectiveOne (α : Type*) {β : Type*} [One β] (h : Function.Surjec
tive (1 : α -> β)) : Unique β
参数：α : Type*；h : Function.Surjective (1 : α -> β)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def uniqueOfSurjectiveOne (α : Type*) {β : Type*} [One β] (h : Function.Surjective (1 : α → β)) :
    Unique β :=
  h.uniqueOfSurjectiveConst α (1 : β)

@[to_additive]
/-
**Subsingleton.pi_mulSingle_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subsingleton.pi_mulSingle_eq {α : Type*} [DecidableEq I] [Subsingleton I] 
[One α] (i : I) (x : α) : Pi.mulSingle i x = fun _ => x
参数：i : I；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用引理 `Pi.mulSingle_eq_same`：mulSingle_eq_same (i : ι) (x : M i) : mulSingle i 
x i = x
-/
theorem Subsingleton.pi_mulSingle_eq {α : Type*} [DecidableEq I] [Subsingleton I] [One α]
    (i : I) (x : α) : Pi.mulSingle i x = fun _ => x :=
  funext fun j => by rw [Subsingleton.elim j i, Pi.mulSingle_eq_same]

namespace Sum

variable (a a' : α → γ) (b b' : β → γ)

@[to_additive (attr := simp)]
/-
**Sum.elim_one_one** 是 Mathlib 中的一个定理，位于命名空间 `Sum`。
形式化陈述：elim_one_one [One γ] : Sum.elim (1 : α -> γ) (1 : β -> γ) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sum.elim_const_const`：∀ {γ : Sort u_1} {α : Type u_2} {β : Type u_3} (c 
: γ),   Sum.elim (Function.const α c) (Function.const β c) = Function.const (α ⊕
 β) c
-/
theorem elim_one_one [One γ] : Sum.elim (1 : α → γ) (1 : β → γ) = 1 :=
  Sum.elim_const_const 1

@[to_additive (attr := simp)]
/-
**Sum.elim_mulSingle_one** 是 Mathlib 中的一个定理，位于命名空间 `Sum`。
形式化陈述：elim_mulSingle_one [DecidableEq α] [DecidableEq β] [One γ] (i : α) (c : γ)
 : Sum.elim (Pi.mulSingle i c) (1 : β -> γ) = Pi.mulSingle (Sum.inl i) c
参数：i : α；c : γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Sum.elim_update_left`：elim_update_left {γ : Sort*} [DecidableEq α] [Deci
dableEq β] (f : α -> γ) (g : β -> γ) (a : α) (x : γ) : Sum.elim (update f a x) g
 = update …
· 使用定理 `Sum.elim_one_one`：elim_one_one [One γ] : Sum.elim (1 : α -> γ) (1 : β ->
 γ) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem elim_mulSingle_one [DecidableEq α] [DecidableEq β] [One γ] (i : α) (c : γ) :
    Sum.elim (Pi.mulSingle i c) (1 : β → γ) = Pi.mulSingle (Sum.inl i) c := by
  simp only [Pi.mulSingle, Sum.elim_update_left, elim_one_one]

@[to_additive (attr := simp)]
/-
**Sum.elim_one_mulSingle** 是 Mathlib 中的一个定理，位于命名空间 `Sum`。
形式化陈述：elim_one_mulSingle [DecidableEq α] [DecidableEq β] [One γ] (i : β) (c : γ)
 : Sum.elim (1 : α -> γ) (Pi.mulSingle i c) = Pi.mulSingle (Sum.inr i) c
参数：i : β；c : γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Sum.elim_update_right`：elim_update_right {γ : Sort*} [DecidableEq α] [De
cidableEq β] (f : α -> γ) (g : β -> γ) (b : β) (x : γ) : Sum.elim f (update g b 
x) = update…
· 使用定理 `Sum.elim_one_one`：elim_one_one [One γ] : Sum.elim (1 : α -> γ) (1 : β ->
 γ) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem elim_one_mulSingle [DecidableEq α] [DecidableEq β] [One γ] (i : β) (c : γ) :
    Sum.elim (1 : α → γ) (Pi.mulSingle i c) = Pi.mulSingle (Sum.inr i) c := by
  simp only [Pi.mulSingle, Sum.elim_update_right, elim_one_one]

@[to_additive]
/-
**Sum.elim_inv_inv** 是 Mathlib 中的一个定理，位于命名空间 `Sum`。
形式化陈述：elim_inv_inv [Inv γ] : Sum.elim a⁻¹ b⁻¹ = (Sum.elim a b)⁻¹
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Sum.comp_elim`：∀ {γ : Sort u_1} {δ : Sort u_2} {α : Type u_3} {β : Type 
u_4} (f : γ → δ) (g : α → γ) (h : β → γ),   f ∘ Sum.elim g h = Sum.elim (f ∘ g) 
(f …
-/
theorem elim_inv_inv [Inv γ] : Sum.elim a⁻¹ b⁻¹ = (Sum.elim a b)⁻¹ :=
  (Sum.comp_elim Inv.inv a b).symm

@[to_additive]
/-
**Sum.elim_mul_mul** 是 Mathlib 中的一个定理，位于命名空间 `Sum`。
形式化陈述：elim_mul_mul [Mul γ] : Sum.elim (a * a') (b * b') = Sum.elim a b * Sum.eli
m a' b'
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem elim_mul_mul [Mul γ] : Sum.elim (a * a') (b * b') = Sum.elim a b * Sum.elim a' b' := by
  ext x
  cases x <;> rfl

@[to_additive]
/-
**Sum.elim_div_div** 是 Mathlib 中的一个定理，位于命名空间 `Sum`。
形式化陈述：elim_div_div [Div γ] : Sum.elim (a / a') (b / b') = Sum.elim a b / Sum.eli
m a' b'
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem elim_div_div [Div γ] : Sum.elim (a / a') (b / b') = Sum.elim a b / Sum.elim a' b' := by
  ext x
  cases x <;> rfl

end Sum

