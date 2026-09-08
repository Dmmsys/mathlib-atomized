/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Util.Delaborators

/-! # Units in pi types -/

@[expose] public section

variable {ι : Type*} {M : ι → Type*} [∀ i, Monoid (M i)] {x : Π i, M i}

open Units in
/-- The monoid equivalence between units of a product,
and the product of the units of each monoid. -/
@[to_additive (attr := simps)
  /-- The additive-monoid equivalence between (additive) units of a product,
  and the product of the (additive) units of each monoid. -/]
/-
**MulEquiv.piUnits** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：MulEquiv.piUnits : (Π i, M i)ˣ ≃* Π i, (M i)ˣ where toFun f i
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def MulEquiv.piUnits : (Π i, M i)ˣ ≃* Π i, (M i)ˣ where
  toFun f i := ⟨f.val i, f.inv i, congr_fun f.val_inv i, congr_fun f.inv_val i⟩
  invFun f := ⟨(val <| f ·), (inv <| f ·), funext (val_inv <| f ·), funext (inv_val <| f ·)⟩
  map_mul' _ _ := rfl

@[to_additive]
/-
**Pi.isUnit_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Pi.isUnit_iff : IsUnit x ↔ forall i, IsUnit (x i)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Classical.skolem`：∀ {α : Sort u} {b : α → Sort v} {p : (x : α) → b x → P
rop}, (∀ (x : α), ∃ y, p x y) ↔ ∃ f, ∀ (x : α), p x (f x)
-/
lemma Pi.isUnit_iff :
    IsUnit x ↔ ∀ i, IsUnit (x i) := by
  simp_rw [isUnit_iff_exists, funext_iff, ← forall_and]
  exact Classical.skolem (p := fun i y ↦ x i * y = 1 ∧ y * x i = 1).symm

@[to_additive]
/-
**Pi.instSubsingletonUnits** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Pi.instSubsingletonUnits [forall i, Subsingleton (M i)ˣ] : Subsingleton (f
orall i, M i)ˣ
参数：M i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsingleton.units_of_isUnit`：∀ {M : Type u_1} [inst : Monoid M], (∀ (a 
: M), IsUnit a → a = 1) → Subsingleton Mˣ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
instance Pi.instSubsingletonUnits [∀ i, Subsingleton (M i)ˣ] : Subsingleton (∀ i, M i)ˣ :=
  .units_of_isUnit <| by simp [Pi.isUnit_iff, funext_iff]

@[to_additive]
alias ⟨IsUnit.apply, _⟩ := Pi.isUnit_iff

@[to_additive]
/-
**IsUnit.val_inv_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsUnit.val_inv_apply (hx : IsUnit x) (i : ι) : (hx.unit⁻¹).1 i = (hx.apply
 i).unit⁻¹
参数：hx : IsUnit x；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUnit.apply`：∀ {ι : Type u_1} {M : ι → Type u_2} [inst : (i : ι) → Mono
id (M i)] {x : (i : ι) → M i},   IsUnit x → ∀ (i : ι), IsUnit (x i)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Units.inv_eq_val_inv`：inv_eq_val_inv : a.inv = ((a⁻¹ : αˣ) : α)
· 使用定理 `MulEquiv.val_inv_piUnits_apply`：∀ {ι : Type u_1} {M : ι → Type u_2} [ins
t : (i : ι) → Monoid (M i)] (f : ((i : ι) → M i)ˣ) (i : ι),   ↑(MulEquiv.piUnits
 f i)⁻¹ = f.inv i
· 使用定理 `Units.ext`：ext {u v : αˣ} (huv : u.val = v.val) : u = v
-/
lemma IsUnit.val_inv_apply (hx : IsUnit x) (i : ι) : (hx.unit⁻¹).1 i = (hx.apply i).unit⁻¹ := by
  rw [← Units.inv_eq_val_inv, ← MulEquiv.val_inv_piUnits_apply]; congr; ext; rfl
