/-
Copyright (c) 2021 Benjamin Davidson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Davidson
-/
module

public import Mathlib.Algebra.Ring.NegOnePow

/-!
# Periodicity

In this file we define and then prove facts about periodic and antiperiodic functions.

## Main definitions

* `Function.Periodic`: A function `f` is *periodic* if `∀ x, f (x + c) = f x`.
  `f` is referred to as periodic with period `c` or `c`-periodic.

* `Function.Antiperiodic`: A function `f` is *antiperiodic* if `∀ x, f (x + c) = -f x`.
  `f` is referred to as antiperiodic with antiperiod `c` or `c`-antiperiodic.

Note that any `c`-antiperiodic function will necessarily also be `2 • c`-periodic.

## Tags

period, periodic, periodicity, antiperiodic
-/

@[expose] public section

assert_not_exists Field

variable {α β γ : Type*} {f g : α → β} {c c₁ c₂ x : α}

open Set

namespace Function

/-! ### Periodicity -/


/-- A function `f` is said to be `Periodic` with period `c` if for all `x`, `f (x + c) = f x`. -/
@[simp, wikidata Q184743]
/-
**Function.Periodic** 是 Mathlib 中的一个定义，位于命名空间 `Function`。
形式化陈述：Periodic [Add α] (f : α -> β) (c : α) : Prop
参数：f : α -> β；c : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function `f` is said to be `Periodic` with period `c` if for all `x`, `f (x + 
c) = f x`.
-/
def Periodic [Add α] (f : α → β) (c : α) : Prop :=
  ∀ x : α, f (x + c) = f x
/-
**Function.Periodic.funext** 是 Mathlib 中的一个定理，位于命名空间 `Function.Periodic`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c : α} [inst : Add α], Functi
on.Periodic f c → (fun x => f (x + c)) = f
参数：fun x => f (x + c)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
protected theorem Periodic.funext [Add α] (h : Periodic f c) : (fun x => f (x + c)) = f :=
  funext h
/-
**Function.Periodic.comp** 是 Mathlib 中的一个定理，位于命名空间 `Function.Periodic`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f : α → β} {c : α} [inst :
 Add α],   Function.Periodic f c → ∀ (g : β → γ), Function.Periodic (g ∘ f) c
参数：g : β → γ；g ∘ f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
protected theorem Periodic.comp [Add α] (h : Periodic f c) (g : β → γ) : Periodic (g ∘ f) c := by
  simp_all
/-
**Function.Periodic.comp_addHom** 是 Mathlib 中的一个定理，位于命名空间 `Function.Periodic`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f : α → β} {c : α} [inst :
 Add α] [inst_1 : Add γ],   Function.Periodic f c →     ∀ (g : γ →ₙ+ α) (g_inv :
 α → γ), Function.RightInverse g_inv ⇑g → Function.Periodic (f ∘ ⇑g) (g_inv c)
参数：g : γ →ₙ+ α；g_inv : α → γ；f ∘ ⇑g；g_inv c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddHom.addHomClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add M] [inst
_1 : Add N], AddHomClass (M →ₙ+ N) M N
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Periodic.comp_addHom [Add α] [Add γ] (h : Periodic f c) (g : AddHom γ α) (g_inv : α → γ)
    (hg : RightInverse g_inv g) : Periodic (f ∘ g) (g_inv c) := fun x => by
  simp only [hg c, h (g x), map_add, comp_apply]

@[to_additive]
/-
**Function.Periodic.mul** 是 Mathlib 中的一个定理，位于命名空间 `Function.Periodic`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f g : α → β} {c : α} [inst : Add α] [inst
_1 : Mul β],   Function.Periodic f c → Function.Periodic g c → Function.Periodic
 (f * g) c
参数：f * g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
protected theorem Periodic.mul [Add α] [Mul β] (hf : Periodic f c) (hg : Periodic g c) :
    Periodic (f * g) c := by simp_all

@[to_additive]
/-
**Function.Periodic.div** 是 Mathlib 中的一个定理，位于命名空间 `Function.Periodic`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f g : α → β} {c : α} [inst : Add α] [inst
_1 : Div β],   Function.Periodic f c → Function.Periodic g c → Function.Periodic
 (f / g) c
参数：f / g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
protected theorem Periodic.div [Add α] [Div β] (hf : Periodic f c) (hg : Periodic g c) :
    Periodic (f / g) c := by simp_all

@[to_additive]
/-
**Function._root_.List.periodic_prod** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.List.periodic_prod [Add α] [MulOneClass β] (l : List (α → β))
    (hl : ∀ f ∈ l, Periodic f c) : Periodic l.prod c := by
  induction l with
  | nil => simp
  | cons g l ih =>
    rw [List.forall_mem_cons] at hl
    simpa only [List.prod_cons] using hl.1.mul (ih hl.2)

@[to_additive]
/-
**Function._root_.Multiset.periodic_prod** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Multiset.periodic_prod [Add α] [CommMonoid β] (s : Multiset (α → β))
    (hs : ∀ f ∈ s, Periodic f c) : Periodic s.prod c :=
  (s.prod_toList ▸ s.toList.periodic_prod) fun f hf => hs f <| Multiset.mem_toList.mp hf

@[to_additive]
/-
**Function._root_.Finset.periodic_prod** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Finset.periodic_prod [Add α] [CommMonoid β] {ι : Type*} {f : ι → α → β}
    (s : Finset ι) (hs : ∀ i ∈ s, Periodic (f i) c) : Periodic (∏ i ∈ s, f i) c :=
  s.prod_map_toList f ▸ (s.toList.map f).periodic_prod (by simpa [-Periodic])

@[to_additive]
/-
**Function.Periodic.smul** 是 Mathlib 中的一个定理，位于命名空间 `Function.Periodic`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f : α → β} {c : α} [inst :
 Add α] [inst_1 : SMul γ β],   Function.Periodic f c → ∀ (a : γ), Function.Perio
dic (a • f) c
参数：a : γ；a • f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
protected theorem Periodic.smul [Add α] [SMul γ β] (h : Periodic f c) (a : γ) :
    Periodic (a • f) c := by simp_all
/-
**Function.Periodic.const_smul** 是 Mathlib 中的一个定理，位于命名空间 `Function.Periodic`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f : α → β} {c : α} [inst :
 AddMonoid α] [inst_1 : Group γ]   [inst_2 : DistribMulAction γ α], Function.Per
iodic f c → ∀ (a : γ), Function.Periodic (fun x => f (a • x)) (a⁻¹ • c)
参数：a : γ；fun x => f (a • x)；a⁻¹ • c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用引理 `smul_inv_smul`：smul_inv_smul (g : G) (a : α) : g • g⁻¹ • a = a
-/
protected theorem Periodic.const_smul [AddMonoid α] [Group γ] [DistribMulAction γ α]
    (h : Periodic f c) (a : γ) : Periodic (fun x => f (a • x)) (a⁻¹ • c) := fun x => by
  simpa only [smul_add, smul_inv_smul] using h (a • x)
/-
**Function.Periodic.const_inv_smul** 是 Mathlib 中的一个定理，位于命名空间 `Function.Periodic`
。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f : α → β} {c : α} [inst :
 AddMonoid α] [inst_1 : Group γ]   [inst_2 : DistribMulAction γ α], Function.Per
iodic f c → ∀ (a : γ), Function.Periodic (fun x => f (a⁻¹ • x)) (a • c)
参数：a : γ；fun x => f (a⁻¹ • x)；a • c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `Function.Periodic.const_smul`：∀ {α : Type u_1} {β : Type u_2} {γ : Type 
u_3} {f : α → β} {c : α} [inst : AddMonoid α] [inst_1 : Group γ]   [inst_2 : Dis
tribMulAction γ α]…
-/
theorem Periodic.const_inv_smul [AddMonoid α] [Group γ] [DistribMulAction γ α] (h : Periodic f c)
    (a : γ) : Periodic (fun x => f (a⁻¹ • x)) (a • c) := by
  simpa only [inv_inv] using h.const_smul a⁻¹
/-
**Function.Periodic.add_period** 是 Mathlib 中的一个定理，位于命名空间 `Function.Periodic`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c₁ c₂ : α} [inst : AddSemigro
up α],   Function.Periodic f c₁ → Function.Periodic f c₂ → Function.Periodic f (
c₁ + c₂)
参数：c₁ + c₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem Periodic.add_period [AddSemigroup α] (h1 : Periodic f c₁) (h2 : Periodic f c₂) :
    Periodic f (c₁ + c₂) := by simp_all [← add_assoc]
/-
**Function.Periodic.sub_eq** 是 Mathlib 中的一个定理，位于命名空间 `Function.Periodic`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c : α} [inst : AddGroup α],  
 Function.Periodic f c → ∀ (x : α), f (x - c) = f x
参数：x : α；x - c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem Periodic.sub_eq [AddGroup α] (h : Periodic f c) (x : α) : f (x - c) = f x := by
  simpa only [sub_add_cancel] using (h (x - c)).symm
/-
**Function.Periodic.sub_eq'** 是 Mathlib 中的一个定理，位于命名空间 `Function.Periodic`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c x : α} [inst : SubtractionC
ommMonoid α],   Function.Periodic f c → f (c - x) = f (-x)
参数：c - x；-x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_neg_add`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b :
 α), a - b = -b + a
-/
theorem Periodic.sub_eq' [SubtractionCommMonoid α] (h : Periodic f c) : f (c - x) = f (-x) := by
  simpa only [sub_eq_neg_add] using h (-x)
/-
**Function.Periodic.neg** 是 Mathlib 中的一个定理，位于命名空间 `Function.Periodic`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c : α} [inst : AddGroup α],  
 Function.Periodic f c → Function.Periodic f (-c)
参数：-c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Function.Periodic.sub_eq`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c
 : α} [inst : AddGroup α],   Function.Periodic f c → ∀ (x : α), f (x - c) = f x
-/
protected theorem Periodic.neg [AddGroup α] (h : Periodic f c) : Periodic f (-c) := by
  simpa only [sub_eq_add_neg, Periodic] using h.sub_eq
/-
**Function.Periodic.sub_period** 是 Mathlib 中的一个定理，位于命名空间 `Function.Periodic`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c₁ c₂ : α} [inst : AddGroup α
],   Function.Periodic f c₁ → Function.Periodic f c₂ → Function.Periodic f (c₁ -
 c₂)
参数：c₁ - c₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `Function.Periodic.neg`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c : 
α} [inst : AddGroup α],   Function.Periodic f c → Function.Periodic f (-c)
-/
theorem Periodic.sub_period [AddGroup α] (h1 : Periodic f c₁) (h2 : Periodic f c₂) :
    Periodic f (c₁ - c₂) := fun x => by
  rw [sub_eq_add_neg, ← add_assoc, h2.neg, h1]
/-
**Function.Periodic.const_add** 是 Mathlib 中的一个定理，位于命名空间 `Function.Periodic`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c : α} [inst : AddSemigroup α
],   Function.Periodic f c → ∀ (a : α), Function.Periodic (fun x => f (a + x)) c
参数：a : α；fun x => f (a + x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
-/
theorem Periodic.const_add [AddSemigroup α] (h : Periodic f c) (a : α) :
    Periodic (fun x => f (a + x)) c := fun x => by simpa [add_assoc] using h (a + x)
/-
**Function.Periodic.add_const** 是 Mathlib 中的一个定理，位于命名空间 `Function.Periodic`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c : α} [inst : AddCommSemigro
up α],   Function.Periodic f c → ∀ (a : α), Function.Periodic (fun x => f (x + a
)) c
参数：a : α；fun x => f (x + a)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_right_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c : G)
, a + b + c = a + c + b
-/
theorem Periodic.add_const [AddCommSemigroup α] (h : Periodic f c) (a : α) :
    Periodic (fun x => f (x + a)) c := fun x => by
  simpa only [add_right_comm] using h (x + a)
/-
**Function.Periodic.const_sub** 是 Mathlib 中的一个定理，位于命名空间 `Function.Periodic`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c : α} [inst : AddCommGroup α
],   Function.Periodic f c → ∀ (a : α), Function.Periodic (fun x => f (a - x)) c
参数：a : α；fun x => f (a - x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Periodic.sub_eq`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c
 : α} [inst : AddGroup α],   Function.Periodic f c → ∀ (x : α), f (x - c) = f x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Periodic.const_sub [AddCommGroup α] (h : Periodic f c) (a : α) :
    Periodic (fun x => f (a - x)) c := fun x => by
  simp only [← sub_sub, h.sub_eq]
/-
**Function.Periodic.sub_const** 是 Mathlib 中的一个定理，位于命名空间 `Function.Periodic`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c : α} [inst : SubtractionCom
mMonoid α],   Function.Periodic f c → ∀ (a : α), Function.Periodic (fun x => f (
x - a)) c
参数：a : α；fun x => f (x - a)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Function.Periodic.add_const`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}
 {c : α} [inst : AddCommSemigroup α],   Function.Periodic f c → ∀ (a : α), Funct
ion.Periodic (fun…
-/
theorem Periodic.sub_const [SubtractionCommMonoid α] (h : Periodic f c) (a : α) :
    Periodic (fun x => f (x - a)) c := by
  simpa only [sub_eq_add_neg] using h.add_const (-a)
/-
**Function.Periodic.nsmul** 是 Mathlib 中的一个定理，位于命名空间 `Function.Periodic`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c : α} [inst : AddMonoid α], 
  Function.Periodic f c → ∀ (n : ℕ), Function.Periodic f (n • c)
参数：n : ℕ；n • c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M), 0 • a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `add_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M) (m n : ℕ), (m +
 n) • a = m • a + n • a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
theorem Periodic.nsmul [AddMonoid α] (h : Periodic f c) (n : ℕ) : Periodic f (n • c) := by
  induction n <;> simp_all [add_nsmul, ← add_assoc]
/-
**Function.Periodic.nat_mul** 是 Mathlib 中的一个定理，位于命名空间 `Function.Periodic`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c : α} [inst : NonAssocSemiri
ng α],   Function.Periodic f c → ∀ (n : ℕ), Function.Periodic f (↑n * c)
参数：n : ℕ；↑n * c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `Function.Periodic.nsmul`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c 
: α} [inst : AddMonoid α],   Function.Periodic f c → ∀ (n : ℕ), Function.Periodi
c f (n • c)
-/
theorem Periodic.nat_mul [NonAssocSemiring α] (h : Periodic f c) (n : ℕ) : Periodic f (n * c) := by
  simpa only [nsmul_eq_mul] using h.nsmul n
/-
**Function.Periodic.neg_nsmul** 是 Mathlib 中的一个定理，位于命名空间 `Function.Periodic`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c : α} [inst : AddGroup α],  
 Function.Periodic f c → ∀ (n : ℕ), Function.Periodic f (-(n • c))
参数：n : ℕ；-(n • c)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Periodic.neg`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c : 
α} [inst : AddGroup α],   Function.Periodic f c → Function.Periodic f (-c)
· 使用定理 `Function.Periodic.nsmul`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c 
: α} [inst : AddMonoid α],   Function.Periodic f c → ∀ (n : ℕ), Function.Periodi
c f (n • c)
-/
theorem Periodic.neg_nsmul [AddGroup α] (h : Periodic f c) (n : ℕ) : Periodic f (-(n • c)) :=
  (h.nsmul n).neg
/-
**Function.Periodic.neg_nat_mul** 是 Mathlib 中的一个定理，位于命名空间 `Function.Periodic`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c : α} [inst : NonAssocRing α
],   Function.Periodic f c → ∀ (n : ℕ), Function.Periodic f (-(↑n * c))
参数：n : ℕ；-(↑n * c)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Periodic.neg`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c : 
α} [inst : AddGroup α],   Function.Periodic f c → Function.Periodic f (-c)
· 使用定理 `Function.Periodic.nat_mul`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
c : α} [inst : NonAssocSemiring α],   Function.Periodic f c → ∀ (n : ℕ), Functio
n.Periodic f (↑…
-/
theorem Periodic.neg_nat_mul [NonAssocRing α] (h : Periodic f c) (n : ℕ) : Periodic f (-(n * c)) :=
  (h.nat_mul n).neg
/-
**Function.Periodic.sub_nsmul_eq** 是 Mathlib 中的一个定理，位于命名空间 `Function.Periodic`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c x : α} [inst : AddGroup α],
   Function.Periodic f c → ∀ (n : ℕ), f (x - n • c) = f x
参数：n : ℕ；x - n • c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Function.Periodic.neg_nsmul`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}
 {c : α} [inst : AddGroup α],   Function.Periodic f c → ∀ (n : ℕ), Function.Peri
odic f (-(n • c))
-/
theorem Periodic.sub_nsmul_eq [AddGroup α] (h : Periodic f c) (n : ℕ) : f (x - n • c) = f x := by
  simpa only [sub_eq_add_neg] using h.neg_nsmul n x
/-
**Function.Periodic.sub_nat_mul_eq** 是 Mathlib 中的一个定理，位于命名空间 `Function.Periodic`
。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c x : α} [inst : NonAssocRing
 α],   Function.Periodic f c → ∀ (n : ℕ), f (x - ↑n * c) = f x
参数：n : ℕ；x - ↑n * c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `Function.Periodic.sub_nsmul_eq`：∀ {α : Type u_1} {β : Type u_2} {f : α →
 β} {c x : α} [inst : AddGroup α],   Function.Periodic f c → ∀ (n : ℕ), f (x - n
 • c) = f x
-/
theorem Periodic.sub_nat_mul_eq [NonAssocRing α] (h : Periodic f c) (n : ℕ) :
    f (x - n * c) = f x := by
  simpa only [nsmul_eq_mul] using h.sub_nsmul_eq n
/-
**Function.Periodic.nsmul_sub_eq** 是 Mathlib 中的一个定理，位于命名空间 `Function.Periodic`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c x : α} [inst : SubtractionC
ommMonoid α],   Function.Periodic f c → ∀ (n : ℕ), f (n • c - x) = f (-x)
参数：n : ℕ；n • c - x；-x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Periodic.sub_eq'`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
c x : α} [inst : SubtractionCommMonoid α],   Function.Periodic f c → f (c - x) =
 f (-x)
· 使用定理 `Function.Periodic.nsmul`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c 
: α} [inst : AddMonoid α],   Function.Periodic f c → ∀ (n : ℕ), Function.Periodi
c f (n • c)
-/
theorem Periodic.nsmul_sub_eq [SubtractionCommMonoid α] (h : Periodic f c) (n : ℕ) :
    f (n • c - x) = f (-x) :=
  (h.nsmul n).sub_eq'
/-
**Function.Periodic.nat_mul_sub_eq** 是 Mathlib 中的一个定理，位于命名空间 `Function.Periodic`
。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c x : α} [inst : NonAssocRing
 α],   Function.Periodic f c → ∀ (n : ℕ), f (↑n * c - x) = f (-x)
参数：n : ℕ；↑n * c - x；-x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_neg_add`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b :
 α), a - b = -b + a
· 使用定理 `Function.Periodic.nat_mul`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
c : α} [inst : NonAssocSemiring α],   Function.Periodic f c → ∀ (n : ℕ), Functio
n.Periodic f (↑…
-/
theorem Periodic.nat_mul_sub_eq [NonAssocRing α] (h : Periodic f c) (n : ℕ) :
    f (n * c - x) = f (-x) := by
  simpa only [sub_eq_neg_add] using h.nat_mul n (-x)
/-
**Function.Periodic.zsmul** 是 Mathlib 中的一个定理，位于命名空间 `Function.Periodic`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c : α} [inst : AddGroup α],  
 Function.Periodic f c → ∀ (n : ℤ), Function.Periodic f (n • c)
参数：n : ℤ；n • c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `natCast_zsmul`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G) (n : ℕ),
 ↑n • a = n • a
· 使用定理 `Function.Periodic.nsmul`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c 
: α} [inst : AddMonoid α],   Function.Periodic f c → ∀ (n : ℕ), Function.Periodi
c f (n • c)
· 使用定理 `negSucc_zsmul`：negSucc_zsmul {G} [SubNegMonoid G] (a : G) (n : Nat) : In
t.negSucc n • a = -((n + 1) • a)
· 使用定理 `Function.Periodic.neg`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c : 
α} [inst : AddGroup α],   Function.Periodic f c → Function.Periodic f (-c)
-/
protected theorem Periodic.zsmul [AddGroup α] (h : Periodic f c) (n : ℤ) : Periodic f (n • c) := by
  rcases n with n | n
  · simpa only [Int.ofNat_eq_natCast, natCast_zsmul] using h.nsmul n
  · simpa only [negSucc_zsmul] using (h.nsmul (n + 1)).neg
/-
**Function.Periodic.int_mul** 是 Mathlib 中的一个定理，位于命名空间 `Function.Periodic`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c : α} [inst : NonAssocRing α
],   Function.Periodic f c → ∀ (n : ℤ), Function.Periodic f (↑n * c)
参数：n : ℤ；↑n * c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zsmul_eq_mul`：∀ {α : Type u_3} [inst : NonAssocRing α] (a : α) (n : ℤ), 
n • a = ↑n * a
· 使用定理 `Function.Periodic.zsmul`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c 
: α} [inst : AddGroup α],   Function.Periodic f c → ∀ (n : ℤ), Function.Periodic
 f (n • c)
-/
protected theorem Periodic.int_mul [NonAssocRing α] (h : Periodic f c) (n : ℤ) :
    Periodic f (n * c) := by
  simpa only [zsmul_eq_mul] using h.zsmul n
/-
**Function.Periodic.sub_zsmul_eq** 是 Mathlib 中的一个定理，位于命名空间 `Function.Periodic`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c x : α} [inst : AddGroup α],
   Function.Periodic f c → ∀ (n : ℤ), f (x - n • c) = f x
参数：n : ℤ；x - n • c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Periodic.sub_eq`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c
 : α} [inst : AddGroup α],   Function.Periodic f c → ∀ (x : α), f (x - c) = f x
· 使用定理 `Function.Periodic.zsmul`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c 
: α} [inst : AddGroup α],   Function.Periodic f c → ∀ (n : ℤ), Function.Periodic
 f (n • c)
-/
theorem Periodic.sub_zsmul_eq [AddGroup α] (h : Periodic f c) (n : ℤ) : f (x - n • c) = f x :=
  (h.zsmul n).sub_eq x
/-
**Function.Periodic.sub_int_mul_eq** 是 Mathlib 中的一个定理，位于命名空间 `Function.Periodic`
。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c x : α} [inst : NonAssocRing
 α],   Function.Periodic f c → ∀ (n : ℤ), f (x - ↑n * c) = f x
参数：n : ℤ；x - ↑n * c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Periodic.sub_eq`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c
 : α} [inst : AddGroup α],   Function.Periodic f c → ∀ (x : α), f (x - c) = f x
· 使用定理 `Function.Periodic.int_mul`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
c : α} [inst : NonAssocRing α],   Function.Periodic f c → ∀ (n : ℤ), Function.Pe
riodic f (↑n * …
-/
theorem Periodic.sub_int_mul_eq [NonAssocRing α] (h : Periodic f c) (n : ℤ) : f (x - n * c) = f x :=
  (h.int_mul n).sub_eq x
/-
**Function.Periodic.zsmul_sub_eq** 是 Mathlib 中的一个定理，位于命名空间 `Function.Periodic`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c x : α} [inst : AddCommGroup
 α],   Function.Periodic f c → ∀ (n : ℤ), f (n • c - x) = f (-x)
参数：n : ℤ；n • c - x；-x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Periodic.sub_eq'`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
c x : α} [inst : SubtractionCommMonoid α],   Function.Periodic f c → f (c - x) =
 f (-x)
· 使用定理 `Function.Periodic.zsmul`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c 
: α} [inst : AddGroup α],   Function.Periodic f c → ∀ (n : ℤ), Function.Periodic
 f (n • c)
-/
theorem Periodic.zsmul_sub_eq [AddCommGroup α] (h : Periodic f c) (n : ℤ) :
    f (n • c - x) = f (-x) :=
  (h.zsmul _).sub_eq'
/-
**Function.Periodic.int_mul_sub_eq** 是 Mathlib 中的一个定理，位于命名空间 `Function.Periodic`
。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c x : α} [inst : NonAssocRing
 α],   Function.Periodic f c → ∀ (n : ℤ), f (↑n * c - x) = f (-x)
参数：n : ℤ；↑n * c - x；-x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Periodic.sub_eq'`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
c x : α} [inst : SubtractionCommMonoid α],   Function.Periodic f c → f (c - x) =
 f (-x)
· 使用定理 `Function.Periodic.int_mul`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
c : α} [inst : NonAssocRing α],   Function.Periodic f c → ∀ (n : ℤ), Function.Pe
riodic f (↑n * …
-/
theorem Periodic.int_mul_sub_eq [NonAssocRing α] (h : Periodic f c) (n : ℤ) :
    f (n * c - x) = f (-x) :=
  (h.int_mul _).sub_eq'
/-
**Function.Periodic.eq** 是 Mathlib 中的一个定理，位于命名空间 `Function.Periodic`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c : α} [inst : AddZeroClass α
], Function.Periodic f c → f c = f 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
protected theorem Periodic.eq [AddZeroClass α] (h : Periodic f c) : f c = f 0 := by
  simpa only [zero_add] using h 0
/-
**Function.Periodic.neg_eq** 是 Mathlib 中的一个定理，位于命名空间 `Function.Periodic`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c : α} [inst : AddGroup α], F
unction.Periodic f c → f (-c) = f 0
参数：-c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Periodic.eq`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c : α
} [inst : AddZeroClass α], Function.Periodic f c → f c = f 0
· 使用定理 `Function.Periodic.neg`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c : 
α} [inst : AddGroup α],   Function.Periodic f c → Function.Periodic f (-c)
-/
protected theorem Periodic.neg_eq [AddGroup α] (h : Periodic f c) : f (-c) = f 0 :=
  h.neg.eq
/-
**Function.Periodic.nsmul_eq** 是 Mathlib 中的一个定理，位于命名空间 `Function.Periodic`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c : α} [inst : AddMonoid α], 
  Function.Periodic f c → ∀ (n : ℕ), f (n • c) = f 0
参数：n : ℕ；n • c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Periodic.eq`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c : α
} [inst : AddZeroClass α], Function.Periodic f c → f c = f 0
· 使用定理 `Function.Periodic.nsmul`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c 
: α} [inst : AddMonoid α],   Function.Periodic f c → ∀ (n : ℕ), Function.Periodi
c f (n • c)
-/
protected theorem Periodic.nsmul_eq [AddMonoid α] (h : Periodic f c) (n : ℕ) : f (n • c) = f 0 :=
  (h.nsmul n).eq
/-
**Function.Periodic.nat_mul_eq** 是 Mathlib 中的一个定理，位于命名空间 `Function.Periodic`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c : α} [inst : NonAssocSemiri
ng α],   Function.Periodic f c → ∀ (n : ℕ), f (↑n * c) = f 0
参数：n : ℕ；↑n * c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Periodic.eq`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c : α
} [inst : AddZeroClass α], Function.Periodic f c → f c = f 0
· 使用定理 `Function.Periodic.nat_mul`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
c : α} [inst : NonAssocSemiring α],   Function.Periodic f c → ∀ (n : ℕ), Functio
n.Periodic f (↑…
-/
theorem Periodic.nat_mul_eq [NonAssocSemiring α] (h : Periodic f c) (n : ℕ) : f (n * c) = f 0 :=
  (h.nat_mul n).eq
/-
**Function.Periodic.zsmul_eq** 是 Mathlib 中的一个定理，位于命名空间 `Function.Periodic`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c : α} [inst : AddGroup α],  
 Function.Periodic f c → ∀ (n : ℤ), f (n • c) = f 0
参数：n : ℤ；n • c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Periodic.eq`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c : α
} [inst : AddZeroClass α], Function.Periodic f c → f c = f 0
· 使用定理 `Function.Periodic.zsmul`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c 
: α} [inst : AddGroup α],   Function.Periodic f c → ∀ (n : ℤ), Function.Periodic
 f (n • c)
-/
theorem Periodic.zsmul_eq [AddGroup α] (h : Periodic f c) (n : ℤ) : f (n • c) = f 0 :=
  (h.zsmul n).eq
/-
**Function.Periodic.int_mul_eq** 是 Mathlib 中的一个定理，位于命名空间 `Function.Periodic`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c : α} [inst : NonAssocRing α
],   Function.Periodic f c → ∀ (n : ℤ), f (↑n * c) = f 0
参数：n : ℤ；↑n * c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Periodic.eq`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c : α
} [inst : AddZeroClass α], Function.Periodic f c → f c = f 0
· 使用定理 `Function.Periodic.int_mul`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
c : α} [inst : NonAssocRing α],   Function.Periodic f c → ∀ (n : ℤ), Function.Pe
riodic f (↑n * …
-/
theorem Periodic.int_mul_eq [NonAssocRing α] (h : Periodic f c) (n : ℤ) : f (n * c) = f 0 :=
  (h.int_mul n).eq
/-
**Function.periodic_with_period_zero** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：periodic_with_period_zero [AddZeroClass α] (f : α -> β) : Periodic f 0
参数：f : α -> β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
theorem periodic_with_period_zero [AddZeroClass α] (f : α → β) : Periodic f 0 := fun x => by
  rw [add_zero]

/-- The iterates `a`, `f a`, `f^[2] a` etc form a periodic sequence with period `n`
iff `a` is a periodic point for `f`. -/
/-
**Function.periodic_iterate_iff** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：periodic_iterate_iff {f : α -> α} {n : Nat} {a : α} : Periodic (f^[·] a) n
 ↔ IsPeriodicPt f n a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Periodic.eq`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c : α
} [inst : AddZeroClass α], Function.Periodic f c → f c = f 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.iterate_add_apply`：iterate_add_apply (m n : Nat) (x : α) : f^[m
 + n] x = f^[m] (f^[n] x)
· 使用定理 `Function.IsFixedPt.eq`：∀ {α : Type u₁} {f : α → α} {x : α}, Function.IsF
ixedPt f x → f x = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The iterates `a`, `f a`, `f^[2] a` etc form a periodic sequence with period `n`
iff `a` is a periodic point for `f`.
-/
theorem periodic_iterate_iff {f : α → α} {n : ℕ} {a : α} :
    Periodic (f^[·] a) n ↔ IsPeriodicPt f n a := by
  refine ⟨fun h ↦ h.eq, fun h k ↦ ?_⟩
  simp only [Function.iterate_add_apply, h.eq]

alias ⟨Periodic.isPeriodicPt, IsPeriodicPt.periodic_iterate⟩ := periodic_iterate_iff
/-
**Function.Periodic.map_vadd_zmultiples** 是 Mathlib 中的一个定理，位于命名空间 `Function.Peri
odic`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c : α} [inst : AddCommGroup α
],   Function.Periodic f c → ∀ (a : ↥(AddSubgroup.zmultiples c)) (x : α), f (a +
ᵥ x) = f x
参数：a : ↥(AddSubgroup.zmultiples c)；x : α；a +ᵥ x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Function.Periodic.zsmul`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c 
: α} [inst : AddGroup α],   Function.Periodic f c → ∀ (n : ℤ), Function.Periodic
 f (n • c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Periodic.map_vadd_zmultiples [AddCommGroup α] (hf : Periodic f c)
    (a : AddSubgroup.zmultiples c) (x : α) : f (a +ᵥ x) = f x := by
  rcases a with ⟨_, m, rfl⟩
  simp [AddSubgroup.vadd_def, add_comm _ x, hf.zsmul m x]
/-
**Function.Periodic.map_vadd_multiples** 是 Mathlib 中的一个定理，位于命名空间 `Function.Perio
dic`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c : α} [inst : AddCommMonoid 
α],   Function.Periodic f c → ∀ (a : ↥(AddSubmonoid.multiples c)) (x : α), f (a 
+ᵥ x) = f x
参数：a : ↥(AddSubmonoid.multiples c)；x : α；a +ᵥ x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Function.Periodic.nsmul`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c 
: α} [inst : AddMonoid α],   Function.Periodic f c → ∀ (n : ℕ), Function.Periodi
c f (n • c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Periodic.map_vadd_multiples [AddCommMonoid α] (hf : Periodic f c)
    (a : AddSubmonoid.multiples c) (x : α) : f (a +ᵥ x) = f x := by
  rcases a with ⟨_, m, rfl⟩
  simp [AddSubmonoid.vadd_def, add_comm _ x, hf.nsmul m x]

/-- Lift a periodic function to a function from the quotient group. -/
/-
**Function.Periodic.lift** 是 Mathlib 中的一个定义，位于命名空间 `Function.Periodic`。
形式化陈述：{α : Type u_1} →   {β : Type u_2} →     {f : α → β} → {c : α} → [inst : Ad
dGroup α] → Function.Periodic f c → α ⧸ AddSubgroup.zmultiples c → β
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lift a periodic function to a function from the quotient group.
-/
def Periodic.lift [AddGroup α] (h : Periodic f c) (x : α ⧸ AddSubgroup.zmultiples c) : β :=
  Quotient.liftOn' x f fun a b h' => by
    rw [QuotientAddGroup.leftRel_apply] at h'
    obtain ⟨k, hk⟩ := h'
    exact (h.zsmul k _).symm.trans (congr_arg f (add_eq_of_eq_neg_add hk))

@[simp]
/-
**Function.Periodic.lift_coe** 是 Mathlib 中的一个定理，位于命名空间 `Function.Periodic`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c : α} [inst : AddGroup α] (h
 : Function.Periodic f c) (a : α),   h.lift ↑a = f a
参数：h : Function.Periodic f c；a : α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Periodic.lift_coe [AddGroup α] (h : Periodic f c) (a : α) :
    h.lift (a : α ⧸ AddSubgroup.zmultiples c) = f a :=
  rfl

/-- A periodic function `f : R → X` on a semiring (or, more generally, `AddZeroClass`)
of non-zero period is not injective. -/
/-
**Function.Periodic.not_injective** 是 Mathlib 中的一个定理，位于命名空间 `Function.Periodic`。
形式化陈述：∀ {R : Type u_4} {X : Type u_5} [inst : AddZeroClass R] {f : R → X} {c : R
},   Function.Periodic f c → c ≠ 0 → ¬Function.Injective f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Periodic.eq`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c : α
} [inst : AddZeroClass α], Function.Periodic f c → f c = f 0

--- 原说明 ---
A periodic function `f : R → X` on a semiring (or, more generally, `AddZeroClass
`)
of non-zero period is not injective.
-/
lemma Periodic.not_injective {R X : Type*} [AddZeroClass R] {f : R → X} {c : R}
    (hf : Periodic f c) (hc : c ≠ 0) : ¬ Injective f := fun h ↦ hc <| h hf.eq

/-! ### Antiperiodicity -/

/-- A function `f` is said to be `antiperiodic` with antiperiod `c` if for all `x`,
  `f (x + c) = -f x`. -/
@[simp]
/-
**Function.Antiperiodic** 是 Mathlib 中的一个定义，位于命名空间 `Function`。
形式化陈述：Antiperiodic [Add α] [Neg β] (f : α -> β) (c : α) : Prop
参数：f : α -> β；c : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function `f` is said to be `antiperiodic` with antiperiod `c` if for all `x`,
  `f (x + c) = -f x`.
-/
def Antiperiodic [Add α] [Neg β] (f : α → β) (c : α) : Prop :=
  ∀ x : α, f (x + c) = -f x
/-
**Function.Antiperiodic.funext** 是 Mathlib 中的一个定理，位于命名空间 `Function.Antiperiodic`
。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c : α} [inst : Add α] [inst_1
 : Neg β],   Function.Antiperiodic f c → (fun x => f (x + c)) = -f
参数：fun x => f (x + c)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
protected theorem Antiperiodic.funext [Add α] [Neg β] (h : Antiperiodic f c) :
    (fun x => f (x + c)) = -f :=
  funext h
/-
**Function.Antiperiodic.funext'** 是 Mathlib 中的一个定理，位于命名空间 `Function.Antiperiodic
`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c : α} [inst : Add α] [inst_1
 : InvolutiveNeg β],   Function.Antiperiodic f c → (fun x => -f (x + c)) = f
参数：fun x => -f (x + c)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_eq_iff_eq_neg`：∀ {G : Type u_3} [inst : InvolutiveNeg G] {a b : G}, 
-a = b ↔ a = -b
· 使用定理 `Function.Antiperiodic.funext`：∀ {α : Type u_1} {β : Type u_2} {f : α → β
} {c : α} [inst : Add α] [inst_1 : Neg β],   Function.Antiperiodic f c → (fun x 
=> f (x + c)) = -f
-/
protected theorem Antiperiodic.funext' [Add α] [InvolutiveNeg β] (h : Antiperiodic f c) :
    (fun x => -f (x + c)) = f :=
  neg_eq_iff_eq_neg.mpr h.funext

/-- If a function is `antiperiodic` with antiperiod `c`, then it is also `Periodic` with period
`2 • c`. -/
/-
**Function.Antiperiodic.periodic** 是 Mathlib 中的一个定理，位于命名空间 `Function.Antiperiodi
c`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c : α} [inst : AddMonoid α] [
inst_1 : InvolutiveNeg β],   Function.Antiperiodic f c → Function.Periodic f (2 
• c)
参数：2 • c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `two_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M), 2 • a = a + a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
If a function is `antiperiodic` with antiperiod `c`, then it is also `Periodic` 
with period
`2 • c`.
-/
protected theorem Antiperiodic.periodic [AddMonoid α] [InvolutiveNeg β]
    (h : Antiperiodic f c) : Periodic f (2 • c) := by simp [two_nsmul, ← add_assoc, h _]

/-- If a function is `antiperiodic` with antiperiod `c`, then it is also `Periodic` with period
  `2 * c`. -/
/-
**Function.Antiperiodic.periodic_two_mul** 是 Mathlib 中的一个定理，位于命名空间 `Function.Ant
iperiodic`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c : α} [inst : NonAssocSemiri
ng α] [inst_1 : InvolutiveNeg β],   Function.Antiperiodic f c → Function.Periodi
c f (2 * c)
参数：2 * c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Antiperiodic.periodic`：∀ {α : Type u_1} {β : Type u_2} {f : α →
 β} {c : α} [inst : AddMonoid α] [inst_1 : InvolutiveNeg β],   Function.Antiperi
odic f c → Function.…
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a

--- 原说明 ---
If a function is `antiperiodic` with antiperiod `c`, then it is also `Periodic` 
with period
  `2 * c`.
-/
protected theorem Antiperiodic.periodic_two_mul [NonAssocSemiring α] [InvolutiveNeg β]
    (h : Antiperiodic f c) : Periodic f (2 * c) := nsmul_eq_mul 2 c ▸ h.periodic
/-
**Function.Antiperiodic.eq** 是 Mathlib 中的一个定理，位于命名空间 `Function.Antiperiodic`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c : α} [inst : AddZeroClass α
] [inst_1 : Neg β],   Function.Antiperiodic f c → f c = -f 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
protected theorem Antiperiodic.eq [AddZeroClass α] [Neg β] (h : Antiperiodic f c) : f c = -f 0 := by
  simpa only [zero_add] using h 0
/-
**Function.Antiperiodic.even_nsmul_periodic** 是 Mathlib 中的一个定理，位于命名空间 `Function.
Antiperiodic`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c : α} [inst : AddMonoid α] [
inst_1 : InvolutiveNeg β],   Function.Antiperiodic f c → ∀ (n : ℕ), Function.Per
iodic f ((2 * n) • c)
参数：n : ℕ；(2 * n) • c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Periodic.nsmul`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c 
: α} [inst : AddMonoid α],   Function.Periodic f c → ∀ (n : ℕ), Function.Periodi
c f (n • c)
· 使用定理 `Function.Antiperiodic.periodic`：∀ {α : Type u_1} {β : Type u_2} {f : α →
 β} {c : α} [inst : AddMonoid α] [inst_1 : InvolutiveNeg β],   Function.Antiperi
odic f c → Function.…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M) (m n : ℕ), (m *
 n) • a = n • m • a
-/
theorem Antiperiodic.even_nsmul_periodic [AddMonoid α] [InvolutiveNeg β] (h : Antiperiodic f c)
    (n : ℕ) : Periodic f ((2 * n) • c) := mul_nsmul c 2 n ▸ h.periodic.nsmul n
/-
**Function.Antiperiodic.nat_even_mul_periodic** 是 Mathlib 中的一个定理，位于命名空间 `Functio
n.Antiperiodic`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c : α} [inst : NonAssocSemiri
ng α] [inst_1 : InvolutiveNeg β],   Function.Antiperiodic f c → ∀ (n : ℕ), Funct
ion.Periodic f (↑n * (2 * c))
参数：n : ℕ；↑n * (2 * c)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Periodic.nat_mul`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
c : α} [inst : NonAssocSemiring α],   Function.Periodic f c → ∀ (n : ℕ), Functio
n.Periodic f (↑…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Function.Antiperiodic.periodic_two_mul`：∀ {α : Type u_1} {β : Type u_2} 
{f : α → β} {c : α} [inst : NonAssocSemiring α] [inst_1 : InvolutiveNeg β],   Fu
nction.Antiperiodic f c → Fu…
-/
theorem Antiperiodic.nat_even_mul_periodic [NonAssocSemiring α] [InvolutiveNeg β]
    (h : Antiperiodic f c) (n : ℕ) : Periodic f (n * (2 * c)) :=
  h.periodic_two_mul.nat_mul n
/-
**Function.Antiperiodic.odd_nsmul_antiperiodic** 是 Mathlib 中的一个定理，位于命名空间 `Functi
on.Antiperiodic`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c : α} [inst : AddMonoid α] [
inst_1 : InvolutiveNeg β],   Function.Antiperiodic f c → ∀ (n : ℕ), Function.Ant
iperiodic f ((2 * n + 1) • c)
参数：n : ℕ；(2 * n + 1) • c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M) (m n : ℕ), (m +
 n) • a = m • a + n • a
· 使用定理 `one_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M), 1 • a = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `Function.Antiperiodic.even_nsmul_periodic`：∀ {α : Type u_1} {β : Type u_
2} {f : α → β} {c : α} [inst : AddMonoid α] [inst_1 : InvolutiveNeg β],   Functi
on.Antiperiodic f c → ∀ (n : ℕ)…
-/
theorem Antiperiodic.odd_nsmul_antiperiodic [AddMonoid α] [InvolutiveNeg β] (h : Antiperiodic f c)
    (n : ℕ) : Antiperiodic f ((2 * n + 1) • c) := fun x => by
  rw [add_nsmul, one_nsmul, ← add_assoc, h, h.even_nsmul_periodic]
/-
**Function.Antiperiodic.nat_odd_mul_antiperiodic** 是 Mathlib 中的一个定理，位于命名空间 `Func
tion.Antiperiodic`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c : α} [inst : NonAssocSemiri
ng α] [inst_1 : InvolutiveNeg β],   Function.Antiperiodic f c → ∀ (n : ℕ), Funct
ion.Antiperiodic f (↑n * (2 * c) + c)
参数：n : ℕ；↑n * (2 * c) + c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `Function.Antiperiodic.nat_even_mul_periodic`：∀ {α : Type u_1} {β : Type 
u_2} {f : α → β} {c : α} [inst : NonAssocSemiring α] [inst_1 : InvolutiveNeg β],
   Function.Antiperiodic f c → ∀ …
-/
theorem Antiperiodic.nat_odd_mul_antiperiodic [NonAssocSemiring α] [InvolutiveNeg β]
    (h : Antiperiodic f c) (n : ℕ) : Antiperiodic f (n * (2 * c) + c) := fun x => by
  rw [← add_assoc, h, h.nat_even_mul_periodic]
/-
**Function.Antiperiodic.even_zsmul_periodic** 是 Mathlib 中的一个定理，位于命名空间 `Function.
Antiperiodic`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c : α} [inst : AddGroup α] [i
nst_1 : InvolutiveNeg β],   Function.Antiperiodic f c → ∀ (n : ℤ), Function.Peri
odic f ((2 * n) • c)
参数：n : ℤ；(2 * n) • c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_zsmul`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a : α) (m n : 
ℤ), (m * n) • a = m • n • a
· 使用定理 `two_zsmul`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 2 • a = a +
 a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `two_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M), 2 • a = a + a
· 使用定理 `Function.Periodic.zsmul`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c 
: α} [inst : AddGroup α],   Function.Periodic f c → ∀ (n : ℤ), Function.Periodic
 f (n • c)
· 使用定理 `Function.Antiperiodic.periodic`：∀ {α : Type u_1} {β : Type u_2} {f : α →
 β} {c : α} [inst : AddMonoid α] [inst_1 : InvolutiveNeg β],   Function.Antiperi
odic f c → Function.…
-/
theorem Antiperiodic.even_zsmul_periodic [AddGroup α] [InvolutiveNeg β] (h : Antiperiodic f c)
    (n : ℤ) : Periodic f ((2 * n) • c) := by
  rw [mul_comm, mul_zsmul, two_zsmul, ← two_nsmul]
  exact h.periodic.zsmul n
/-
**Function.Antiperiodic.int_even_mul_periodic** 是 Mathlib 中的一个定理，位于命名空间 `Functio
n.Antiperiodic`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c : α} [inst : NonAssocRing α
] [inst_1 : InvolutiveNeg β],   Function.Antiperiodic f c → ∀ (n : ℤ), Function.
Periodic f (↑n * (2 * c))
参数：n : ℤ；↑n * (2 * c)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Periodic.int_mul`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
c : α} [inst : NonAssocRing α],   Function.Periodic f c → ∀ (n : ℤ), Function.Pe
riodic f (↑n * …
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Function.Antiperiodic.periodic_two_mul`：∀ {α : Type u_1} {β : Type u_2} 
{f : α → β} {c : α} [inst : NonAssocSemiring α] [inst_1 : InvolutiveNeg β],   Fu
nction.Antiperiodic f c → Fu…
-/
theorem Antiperiodic.int_even_mul_periodic [NonAssocRing α] [InvolutiveNeg β] (h : Antiperiodic f c)
    (n : ℤ) : Periodic f (n * (2 * c)) :=
  h.periodic_two_mul.int_mul n
/-
**Function.Antiperiodic.odd_zsmul_antiperiodic** 是 Mathlib 中的一个定理，位于命名空间 `Functi
on.Antiperiodic`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c : α} [inst : AddGroup α] [i
nst_1 : InvolutiveNeg β],   Function.Antiperiodic f c → ∀ (n : ℤ), Function.Anti
periodic f ((2 * n + 1) • c)
参数：n : ℤ；(2 * n + 1) • c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_zsmul`：∀ {G : Type u_3} [inst : AddGroup G] (a : G) (m n : ℤ), (m + 
n) • a = m • a + n • a
· 使用定理 `one_zsmul`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 1 • a = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `Function.Antiperiodic.even_zsmul_periodic`：∀ {α : Type u_1} {β : Type u_
2} {f : α → β} {c : α} [inst : AddGroup α] [inst_1 : InvolutiveNeg β],   Functio
n.Antiperiodic f c → ∀ (n : ℤ),…
-/
theorem Antiperiodic.odd_zsmul_antiperiodic [AddGroup α] [InvolutiveNeg β] (h : Antiperiodic f c)
    (n : ℤ) : Antiperiodic f ((2 * n + 1) • c) := by
  intro x
  rw [add_zsmul, one_zsmul, ← add_assoc, h, h.even_zsmul_periodic]
/-
**Function.Antiperiodic.int_odd_mul_antiperiodic** 是 Mathlib 中的一个定理，位于命名空间 `Func
tion.Antiperiodic`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c : α} [inst : NonAssocRing α
] [inst_1 : InvolutiveNeg β],   Function.Antiperiodic f c → ∀ (n : ℤ), Function.
Antiperiodic f (↑n * (2 * c) + c)
参数：n : ℤ；↑n * (2 * c) + c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `Function.Antiperiodic.int_even_mul_periodic`：∀ {α : Type u_1} {β : Type 
u_2} {f : α → β} {c : α} [inst : NonAssocRing α] [inst_1 : InvolutiveNeg β],   F
unction.Antiperiodic f c → ∀ (n :…
-/
theorem Antiperiodic.int_odd_mul_antiperiodic [NonAssocRing α] [InvolutiveNeg β]
    (h : Antiperiodic f c) (n : ℤ) : Antiperiodic f (n * (2 * c) + c) := fun x => by
  rw [← add_assoc, h, h.int_even_mul_periodic]
/-
**Function.Antiperiodic.sub_eq** 是 Mathlib 中的一个定理，位于命名空间 `Function.Antiperiodic`
。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c : α} [inst : AddGroup α] [i
nst_1 : InvolutiveNeg β],   Function.Antiperiodic f c → ∀ (x : α), f (x - c) = -
f x
参数：x : α；x - c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Antiperiodic.sub_eq [AddGroup α] [InvolutiveNeg β] (h : Antiperiodic f c) (x : α) :
    f (x - c) = -f x := by simp only [← neg_eq_iff_eq_neg, ← h (x - c), sub_add_cancel]
/-
**Function.Antiperiodic.sub_eq'** 是 Mathlib 中的一个定理，位于命名空间 `Function.Antiperiodic
`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c x : α} [inst : SubtractionC
ommMonoid α] [inst_1 : Neg β],   Function.Antiperiodic f c → f (c - x) = -f (-x)
参数：c - x；-x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_neg_add`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b :
 α), a - b = -b + a
-/
theorem Antiperiodic.sub_eq' [SubtractionCommMonoid α] [Neg β] (h : Antiperiodic f c) :
    f (c - x) = -f (-x) := by simpa only [sub_eq_neg_add] using h (-x)
/-
**Function.Antiperiodic.neg** 是 Mathlib 中的一个定理，位于命名空间 `Function.Antiperiodic`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c : α} [inst : AddGroup α] [i
nst_1 : InvolutiveNeg β],   Function.Antiperiodic f c → Function.Antiperiodic f 
(-c)
参数：-c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Function.Antiperiodic.sub_eq`：∀ {α : Type u_1} {β : Type u_2} {f : α → β
} {c : α} [inst : AddGroup α] [inst_1 : InvolutiveNeg β],   Function.Antiperiodi
c f c → ∀ (x : α),…
-/
protected theorem Antiperiodic.neg [AddGroup α] [InvolutiveNeg β] (h : Antiperiodic f c) :
    Antiperiodic f (-c) := by simpa only [sub_eq_add_neg, Antiperiodic] using h.sub_eq
/-
**Function.Antiperiodic.neg_eq** 是 Mathlib 中的一个定理，位于命名空间 `Function.Antiperiodic`
。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c : α} [inst : AddGroup α] [i
nst_1 : InvolutiveNeg β],   Function.Antiperiodic f c → f (-c) = -f 0
参数：-c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Function.Antiperiodic.neg`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
c : α} [inst : AddGroup α] [inst_1 : InvolutiveNeg β],   Function.Antiperiodic f
 c → Function.A…
-/
theorem Antiperiodic.neg_eq [AddGroup α] [InvolutiveNeg β] (h : Antiperiodic f c) :
    f (-c) = -f 0 := by
  simpa only [zero_add] using h.neg 0
/-
**Function.Antiperiodic.nat_mul_eq_of_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Functio
n.Antiperiodic`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c : α} [inst : NonAssocSemiri
ng α] [inst_1 : NegZeroClass β],   Function.Antiperiodic f c → f 0 = 0 → ∀ (n : 
ℕ), f (↑n * c) = 0
参数：n : ℕ；↑n * c。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Antiperiodic.nat_mul_eq_of_eq_zero [NonAssocSemiring α] [NegZeroClass β]
    (h : Antiperiodic f c) (hi : f 0 = 0) : ∀ n : ℕ, f (n * c) = 0
  | 0 => by rwa [Nat.cast_zero, zero_mul]
  | n + 1 => by simp [add_mul, h _, Antiperiodic.nat_mul_eq_of_eq_zero h hi n]
/-
**Function.Antiperiodic.int_mul_eq_of_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Functio
n.Antiperiodic`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c : α} [inst : NonAssocRing α
] [inst_1 : SubtractionMonoid β],   Function.Antiperiodic f c → f 0 = 0 → ∀ (n :
 ℤ), f (↑n * c) = 0
参数：n : ℤ；↑n * c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `Function.Antiperiodic.nat_mul_eq_of_eq_zero`：∀ {α : Type u_1} {β : Type 
u_2} {f : α → β} {c : α} [inst : NonAssocSemiring α] [inst_1 : NegZeroClass β], 
  Function.Antiperiodic f c → f 0…
· 使用定理 `Int.cast_negSucc`：cast_negSucc (n : Nat) : (-[n+1] : R) = -(n + 1 : Nat)
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `Function.Antiperiodic.neg`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
c : α} [inst : AddGroup α] [inst_1 : InvolutiveNeg β],   Function.Antiperiodic f
 c → Function.A…
-/
theorem Antiperiodic.int_mul_eq_of_eq_zero [NonAssocRing α] [SubtractionMonoid β]
    (h : Antiperiodic f c) (hi : f 0 = 0) : ∀ n : ℤ, f (n * c) = 0
  | (n : ℕ) => by rw [Int.cast_natCast, h.nat_mul_eq_of_eq_zero hi n]
  | .negSucc n => by rw [Int.cast_negSucc, neg_mul, ← mul_neg, h.neg.nat_mul_eq_of_eq_zero hi]
/-
**Function.Antiperiodic.add_zsmul_eq** 是 Mathlib 中的一个定理，位于命名空间 `Function.Antiper
iodic`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c x : α} [inst : AddGroup α] 
[inst_1 : SubtractionMonoid β],   Function.Antiperiodic f c → ∀ (n : ℤ), f (x + 
n • c) = ↑n.negOnePow • f x
参数：n : ℤ；x + n • c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Int.even_or_odd'`：even_or_odd' (n : Int) : exists k, n = 2 * k ∨ n = 2 *
 k + 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Antiperiodic.even_zsmul_periodic`：∀ {α : Type u_1} {β : Type u_
2} {f : α → β} {c : α} [inst : AddGroup α] [inst_1 : InvolutiveNeg β],   Functio
n.Antiperiodic f c → ∀ (n : ℤ),…
· 使用引理 `Int.negOnePow_two_mul`：negOnePow_two_mul (n : Int) : (2 * n).negOnePow =
 1
· 使用定理 `Units.val_one`：val_one : ((1 : αˣ) : α) = 1
· 使用定理 `one_zsmul`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 1 • a = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Antiperiodic.odd_zsmul_antiperiodic`：∀ {α : Type u_1} {β : Type
 u_2} {f : α → β} {c : α} [inst : AddGroup α] [inst_1 : InvolutiveNeg β],   Func
tion.Antiperiodic f c → ∀ (n : ℤ),…
· 使用引理 `Int.negOnePow_two_mul_add_one`：negOnePow_two_mul_add_one (n : Int) : (2 
* n + 1).negOnePow = -1
· 使用定理 `Units.val_neg`：∀ {α : Type u} [inst : Monoid α] [inst_1 : HasDistribNeg 
α] (u : αˣ), ↑(-u) = -↑u
· 使用定理 `neg_zsmul`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a : α) (n : ℤ)
, -n • a = -(n • a)
-/
theorem Antiperiodic.add_zsmul_eq [AddGroup α] [SubtractionMonoid β] (h : Antiperiodic f c)
    (n : ℤ) : f (x + n • c) = (n.negOnePow : ℤ) • f x := by
  rcases Int.even_or_odd' n with ⟨k, rfl | rfl⟩
  · rw [h.even_zsmul_periodic, Int.negOnePow_two_mul, Units.val_one, one_zsmul]
  · rw [h.odd_zsmul_antiperiodic, Int.negOnePow_two_mul_add_one, Units.val_neg,
      Units.val_one, neg_zsmul, one_zsmul]
/-
**Function.Antiperiodic.sub_zsmul_eq** 是 Mathlib 中的一个定理，位于命名空间 `Function.Antiper
iodic`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c x : α} [inst : AddGroup α] 
[inst_1 : SubtractionMonoid β],   Function.Antiperiodic f c → ∀ (n : ℤ), f (x - 
n • c) = ↑n.negOnePow • f x
参数：n : ℤ；x - n • c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `neg_zsmul`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a : α) (n : ℤ)
, -n • a = -(n • a)
· 使用引理 `Int.negOnePow_neg`：negOnePow_neg (n : Int) : (-n).negOnePow = n.negOnePo
w
· 使用定理 `Function.Antiperiodic.add_zsmul_eq`：∀ {α : Type u_1} {β : Type u_2} {f :
 α → β} {c x : α} [inst : AddGroup α] [inst_1 : SubtractionMonoid β],   Function
.Antiperiodic f c → ∀ (n…
-/
theorem Antiperiodic.sub_zsmul_eq [AddGroup α] [SubtractionMonoid β] (h : Antiperiodic f c)
    (n : ℤ) : f (x - n • c) = (n.negOnePow : ℤ) • f x := by
  simpa only [sub_eq_add_neg, neg_zsmul, Int.negOnePow_neg] using h.add_zsmul_eq (-n)
/-
**Function.Antiperiodic.zsmul_sub_eq** 是 Mathlib 中的一个定理，位于命名空间 `Function.Antiper
iodic`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c x : α} [inst : AddCommGroup
 α] [inst_1 : SubtractionMonoid β],   Function.Antiperiodic f c → ∀ (n : ℤ), f (
n • c - x) = ↑n.negOnePow • f (-x)
参数：n : ℤ；n • c - x；-x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Function.Antiperiodic.add_zsmul_eq`：∀ {α : Type u_1} {β : Type u_2} {f :
 α → β} {c x : α} [inst : AddGroup α] [inst_1 : SubtractionMonoid β],   Function
.Antiperiodic f c → ∀ (n…
-/
theorem Antiperiodic.zsmul_sub_eq [AddCommGroup α] [SubtractionMonoid β] (h : Antiperiodic f c)
    (n : ℤ) : f (n • c - x) = (n.negOnePow : ℤ) • f (-x) := by
  rw [sub_eq_add_neg, add_comm]
  exact h.add_zsmul_eq n
/-
**Function.Antiperiodic.add_int_mul_eq** 是 Mathlib 中的一个定理，位于命名空间 `Function.Antip
eriodic`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c x : α} [inst : NonAssocRing
 α] [inst_1 : NonAssocRing β],   Function.Antiperiodic f c → ∀ (n : ℤ), f (x + ↑
n * c) = ↑↑n.negOnePow * f x
参数：n : ℤ；x + ↑n * c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zsmul_eq_mul`：∀ {α : Type u_3} [inst : NonAssocRing α] (a : α) (n : ℤ), 
n • a = ↑n * a
· 使用定理 `Function.Antiperiodic.add_zsmul_eq`：∀ {α : Type u_1} {β : Type u_2} {f :
 α → β} {c x : α} [inst : AddGroup α] [inst_1 : SubtractionMonoid β],   Function
.Antiperiodic f c → ∀ (n…
-/
theorem Antiperiodic.add_int_mul_eq [NonAssocRing α] [NonAssocRing β] (h : Antiperiodic f c)
    (n : ℤ) : f (x + n * c) = (n.negOnePow : ℤ) * f x := by
  simpa only [zsmul_eq_mul] using h.add_zsmul_eq n
/-
**Function.Antiperiodic.sub_int_mul_eq** 是 Mathlib 中的一个定理，位于命名空间 `Function.Antip
eriodic`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c x : α} [inst : NonAssocRing
 α] [inst_1 : NonAssocRing β],   Function.Antiperiodic f c → ∀ (n : ℤ), f (x - ↑
n * c) = ↑↑n.negOnePow * f x
参数：n : ℤ；x - ↑n * c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zsmul_eq_mul`：∀ {α : Type u_3} [inst : NonAssocRing α] (a : α) (n : ℤ), 
n • a = ↑n * a
· 使用定理 `Function.Antiperiodic.sub_zsmul_eq`：∀ {α : Type u_1} {β : Type u_2} {f :
 α → β} {c x : α} [inst : AddGroup α] [inst_1 : SubtractionMonoid β],   Function
.Antiperiodic f c → ∀ (n…
-/
theorem Antiperiodic.sub_int_mul_eq [NonAssocRing α] [NonAssocRing β] (h : Antiperiodic f c)
    (n : ℤ) : f (x - n * c) = (n.negOnePow : ℤ) * f x := by
  simpa only [zsmul_eq_mul] using h.sub_zsmul_eq n
/-
**Function.Antiperiodic.int_mul_sub_eq** 是 Mathlib 中的一个定理，位于命名空间 `Function.Antip
eriodic`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c x : α} [inst : NonAssocRing
 α] [inst_1 : NonAssocRing β],   Function.Antiperiodic f c → ∀ (n : ℤ), f (↑n * 
c - x) = ↑↑n.negOnePow * f (-x)
参数：n : ℤ；↑n * c - x；-x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zsmul_eq_mul`：∀ {α : Type u_3} [inst : NonAssocRing α] (a : α) (n : ℤ), 
n • a = ↑n * a
· 使用定理 `Function.Antiperiodic.zsmul_sub_eq`：∀ {α : Type u_1} {β : Type u_2} {f :
 α → β} {c x : α} [inst : AddCommGroup α] [inst_1 : SubtractionMonoid β],   Func
tion.Antiperiodic f c → …
-/
theorem Antiperiodic.int_mul_sub_eq [NonAssocRing α] [NonAssocRing β] (h : Antiperiodic f c)
    (n : ℤ) : f (n * c - x) = (n.negOnePow : ℤ) * f (-x) := by
  simpa only [zsmul_eq_mul] using h.zsmul_sub_eq n
/-
**Function.Antiperiodic.add_nsmul_eq** 是 Mathlib 中的一个定理，位于命名空间 `Function.Antiper
iodic`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c x : α} [inst : AddMonoid α]
 [inst_1 : SubtractionMonoid β],   Function.Antiperiodic f c → ∀ (n : ℕ), f (x +
 n • c) = (-1) ^ n • f x
参数：n : ℕ；x + n • c；-1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.even_or_odd'`：even_or_odd' (n : Nat) : exists k, n = 2 * k ∨ n = 2 *
 k + 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Antiperiodic.even_nsmul_periodic`：∀ {α : Type u_1} {β : Type u_
2} {f : α → β} {c : α} [inst : AddMonoid α] [inst_1 : InvolutiveNeg β],   Functi
on.Antiperiodic f c → ∀ (n : ℕ)…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Even.neg_pow`：∀ {α : Type u_2} [inst : Monoid α] [inst_1 : HasDistribNeg
 α] {n : ℕ}, Even n → ∀ (a : α), (-a) ^ n = a ^ n
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Antiperiodic.odd_nsmul_antiperiodic`：∀ {α : Type u_1} {β : Type
 u_2} {f : α → β} {c : α} [inst : AddMonoid α] [inst_1 : InvolutiveNeg β],   Fun
ction.Antiperiodic f c → ∀ (n : ℕ)…
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `neg_zsmul`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a : α) (n : ℤ)
, -n • a = -(n • a)
-/
theorem Antiperiodic.add_nsmul_eq [AddMonoid α] [SubtractionMonoid β] (h : Antiperiodic f c)
    (n : ℕ) : f (x + n • c) = (-1) ^ n • f x := by
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · rw [h.even_nsmul_periodic]
    simp
  · rw [h.odd_nsmul_antiperiodic]
    simp [pow_add]
/-
**Function.Antiperiodic.sub_nsmul_eq** 是 Mathlib 中的一个定理，位于命名空间 `Function.Antiper
iodic`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c x : α} [inst : AddGroup α] 
[inst_1 : SubtractionMonoid β],   Function.Antiperiodic f c → ∀ (n : ℕ), f (x - 
n • c) = (-1) ^ n • f x
参数：n : ℕ；x - n • c；-1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `natCast_zsmul`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G) (n : ℕ),
 ↑n • a = n • a
· 使用定理 `Function.Antiperiodic.sub_zsmul_eq`：∀ {α : Type u_1} {β : Type u_2} {f :
 α → β} {c x : α} [inst : AddGroup α] [inst_1 : SubtractionMonoid β],   Function
.Antiperiodic f c → ∀ (n…
-/
theorem Antiperiodic.sub_nsmul_eq [AddGroup α] [SubtractionMonoid β] (h : Antiperiodic f c)
    (n : ℕ) : f (x - n • c) = (-1) ^ n • f x := by
  simpa only [Int.reduceNeg, natCast_zsmul] using! h.sub_zsmul_eq n
/-
**Function.Antiperiodic.nsmul_sub_eq** 是 Mathlib 中的一个定理，位于命名空间 `Function.Antiper
iodic`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c x : α} [inst : AddCommGroup
 α] [inst_1 : SubtractionMonoid β],   Function.Antiperiodic f c → ∀ (n : ℕ), f (
n • c - x) = (-1) ^ n • f (-x)
参数：n : ℕ；n • c - x；-1；-x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `natCast_zsmul`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G) (n : ℕ),
 ↑n • a = n • a
· 使用定理 `Function.Antiperiodic.zsmul_sub_eq`：∀ {α : Type u_1} {β : Type u_2} {f :
 α → β} {c x : α} [inst : AddCommGroup α] [inst_1 : SubtractionMonoid β],   Func
tion.Antiperiodic f c → …
-/
theorem Antiperiodic.nsmul_sub_eq [AddCommGroup α] [SubtractionMonoid β] (h : Antiperiodic f c)
    (n : ℕ) : f (n • c - x) = (-1) ^ n • f (-x) := by
  simpa only [Int.reduceNeg, natCast_zsmul] using! h.zsmul_sub_eq n
/-
**Function.Antiperiodic.const_add** 是 Mathlib 中的一个定理，位于命名空间 `Function.Antiperiod
ic`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c : α} [inst : AddSemigroup α
] [inst_1 : Neg β],   Function.Antiperiodic f c → ∀ (a : α), Function.Antiperiod
ic (fun x => f (a + x)) c
参数：a : α；fun x => f (a + x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
-/
theorem Antiperiodic.const_add [AddSemigroup α] [Neg β] (h : Antiperiodic f c) (a : α) :
    Antiperiodic (fun x => f (a + x)) c := fun x => by simpa [add_assoc] using h (a + x)
/-
**Function.Antiperiodic.add_const** 是 Mathlib 中的一个定理，位于命名空间 `Function.Antiperiod
ic`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c : α} [inst : AddCommSemigro
up α] [inst_1 : Neg β],   Function.Antiperiodic f c → ∀ (a : α), Function.Antipe
riodic (fun x => f (x + a)) c
参数：a : α；fun x => f (x + a)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_right_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c : G)
, a + b + c = a + c + b
-/
theorem Antiperiodic.add_const [AddCommSemigroup α] [Neg β] (h : Antiperiodic f c) (a : α) :
    Antiperiodic (fun x => f (x + a)) c := fun x => by
  simpa only [add_right_comm] using h (x + a)
/-
**Function.Antiperiodic.const_sub** 是 Mathlib 中的一个定理，位于命名空间 `Function.Antiperiod
ic`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c : α} [inst : AddCommGroup α
] [inst_1 : InvolutiveNeg β],   Function.Antiperiodic f c → ∀ (a : α), Function.
Antiperiodic (fun x => f (a - x)) c
参数：a : α；fun x => f (a - x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Antiperiodic.sub_eq`：∀ {α : Type u_1} {β : Type u_2} {f : α → β
} {c : α} [inst : AddGroup α] [inst_1 : InvolutiveNeg β],   Function.Antiperiodi
c f c → ∀ (x : α),…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Antiperiodic.const_sub [AddCommGroup α] [InvolutiveNeg β] (h : Antiperiodic f c) (a : α) :
    Antiperiodic (fun x => f (a - x)) c := fun x => by
  simp only [← sub_sub, h.sub_eq]
/-
**Function.Antiperiodic.sub_const** 是 Mathlib 中的一个定理，位于命名空间 `Function.Antiperiod
ic`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c : α} [inst : SubtractionCom
mMonoid α] [inst_1 : Neg β],   Function.Antiperiodic f c → ∀ (a : α), Function.A
ntiperiodic (fun x => f (x - a)) c
参数：a : α；fun x => f (x - a)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Function.Antiperiodic.add_const`：∀ {α : Type u_1} {β : Type u_2} {f : α 
→ β} {c : α} [inst : AddCommSemigroup α] [inst_1 : Neg β],   Function.Antiperiod
ic f c → ∀ (a : α), F…
-/
theorem Antiperiodic.sub_const [SubtractionCommMonoid α] [Neg β] (h : Antiperiodic f c) (a : α) :
    Antiperiodic (fun x => f (x - a)) c := by
  simpa only [sub_eq_add_neg] using h.add_const (-a)
/-
**Function.Antiperiodic.smul** 是 Mathlib 中的一个定理，位于命名空间 `Function.Antiperiodic`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f : α → β} {c : α} [inst :
 Add α] [inst_1 : Monoid γ]   [inst_2 : AddGroup β] [inst_3 : DistribMulAction γ
 β],   Function.Antiperiodic f c → ∀ (a : γ), Function.Antiperiodic (a • f) c
参数：a : γ；a • f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem Antiperiodic.smul [Add α] [Monoid γ] [AddGroup β] [DistribMulAction γ β]
    (h : Antiperiodic f c) (a : γ) : Antiperiodic (a • f) c := by simp_all
/-
**Function.Antiperiodic.const_smul** 是 Mathlib 中的一个定理，位于命名空间 `Function.Antiperio
dic`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f : α → β} {c : α} [inst :
 AddMonoid α] [inst_1 : Neg β]   [inst_2 : Group γ] [inst_3 : DistribMulAction γ
 α],   Function.Antiperiodic f c → ∀ (a : γ), Function.Antiperiodic (fun x => f 
(a • x)) (a⁻¹ • c)
参数：a : γ；fun x => f (a • x)；a⁻¹ • c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用引理 `smul_inv_smul`：smul_inv_smul (g : G) (a : α) : g • g⁻¹ • a = a
-/
theorem Antiperiodic.const_smul [AddMonoid α] [Neg β] [Group γ] [DistribMulAction γ α]
    (h : Antiperiodic f c) (a : γ) : Antiperiodic (fun x => f (a • x)) (a⁻¹ • c) := fun x => by
  simpa only [smul_add, smul_inv_smul] using h (a • x)
/-
**Function.Antiperiodic.const_inv_smul** 是 Mathlib 中的一个定理，位于命名空间 `Function.Antip
eriodic`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f : α → β} {c : α} [inst :
 AddMonoid α] [inst_1 : Neg β]   [inst_2 : Group γ] [inst_3 : DistribMulAction γ
 α],   Function.Antiperiodic f c → ∀ (a : γ), Function.Antiperiodic (fun x => f 
(a⁻¹ • x)) (a • c)
参数：a : γ；fun x => f (a⁻¹ • x)；a • c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `Function.Antiperiodic.const_smul`：∀ {α : Type u_1} {β : Type u_2} {γ : T
ype u_3} {f : α → β} {c : α} [inst : AddMonoid α] [inst_1 : Neg β]   [inst_2 : G
roup γ] [inst_3 : Dist…
-/
theorem Antiperiodic.const_inv_smul [AddMonoid α] [Neg β] [Group γ] [DistribMulAction γ α]
    (h : Antiperiodic f c) (a : γ) : Antiperiodic (fun x => f (a⁻¹ • x)) (a • c) := by
  simpa only [inv_inv] using h.const_smul a⁻¹
/-
**Function.Antiperiodic.add** 是 Mathlib 中的一个定理，位于命名空间 `Function.Antiperiodic`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c₁ c₂ : α} [inst : AddSemigro
up α] [inst_1 : InvolutiveNeg β],   Function.Antiperiodic f c₁ → Function.Antipe
riodic f c₂ → Function.Periodic f (c₁ + c₂)
参数：c₁ + c₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem Antiperiodic.add [AddSemigroup α] [InvolutiveNeg β] (h1 : Antiperiodic f c₁)
    (h2 : Antiperiodic f c₂) : Periodic f (c₁ + c₂) := by simp_all [← add_assoc]
/-
**Function.Antiperiodic.sub** 是 Mathlib 中的一个定理，位于命名空间 `Function.Antiperiodic`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c₁ c₂ : α} [inst : AddGroup α
] [inst_1 : InvolutiveNeg β],   Function.Antiperiodic f c₁ → Function.Antiperiod
ic f c₂ → Function.Periodic f (c₁ - c₂)
参数：c₁ - c₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Function.Antiperiodic.add`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
c₁ c₂ : α} [inst : AddSemigroup α] [inst_1 : InvolutiveNeg β],   Function.Antipe
riodic f c₁ → F…
· 使用定理 `Function.Antiperiodic.neg`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
c : α} [inst : AddGroup α] [inst_1 : InvolutiveNeg β],   Function.Antiperiodic f
 c → Function.A…
-/
theorem Antiperiodic.sub [AddGroup α] [InvolutiveNeg β] (h1 : Antiperiodic f c₁)
    (h2 : Antiperiodic f c₂) : Periodic f (c₁ - c₂) := by
  simpa only [sub_eq_add_neg] using h1.add h2.neg
/-
**Function.Periodic.add_antiperiod** 是 Mathlib 中的一个定理，位于命名空间 `Function.Periodic`
。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c₁ c₂ : α} [inst : AddSemigro
up α] [inst_1 : Neg β],   Function.Periodic f c₁ → Function.Antiperiodic f c₂ → 
Function.Antiperiodic f (c₁ + c₂)
参数：c₁ + c₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem Periodic.add_antiperiod [AddSemigroup α] [Neg β] (h1 : Periodic f c₁)
    (h2 : Antiperiodic f c₂) : Antiperiodic f (c₁ + c₂) := by simp_all [← add_assoc]
/-
**Function.Periodic.sub_antiperiod** 是 Mathlib 中的一个定理，位于命名空间 `Function.Periodic`
。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c₁ c₂ : α} [inst : AddGroup α
] [inst_1 : InvolutiveNeg β],   Function.Periodic f c₁ → Function.Antiperiodic f
 c₂ → Function.Antiperiodic f (c₁ - c₂)
参数：c₁ - c₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Function.Periodic.add_antiperiod`：∀ {α : Type u_1} {β : Type u_2} {f : α
 → β} {c₁ c₂ : α} [inst : AddSemigroup α] [inst_1 : Neg β],   Function.Periodic 
f c₁ → Function.Antipe…
· 使用定理 `Function.Antiperiodic.neg`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
c : α} [inst : AddGroup α] [inst_1 : InvolutiveNeg β],   Function.Antiperiodic f
 c → Function.A…
-/
theorem Periodic.sub_antiperiod [AddGroup α] [InvolutiveNeg β] (h1 : Periodic f c₁)
    (h2 : Antiperiodic f c₂) : Antiperiodic f (c₁ - c₂) := by
  simpa only [sub_eq_add_neg] using h1.add_antiperiod h2.neg
/-
**Function.Periodic.add_antiperiod_eq** 是 Mathlib 中的一个定理，位于命名空间 `Function.Period
ic`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c₁ c₂ : α} [inst : AddMonoid 
α] [inst_1 : Neg β],   Function.Periodic f c₁ → Function.Antiperiodic f c₂ → f (
c₁ + c₂) = -f 0
参数：c₁ + c₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Antiperiodic.eq`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c
 : α} [inst : AddZeroClass α] [inst_1 : Neg β],   Function.Antiperiodic f c → f 
c = -f 0
· 使用定理 `Function.Periodic.add_antiperiod`：∀ {α : Type u_1} {β : Type u_2} {f : α
 → β} {c₁ c₂ : α} [inst : AddSemigroup α] [inst_1 : Neg β],   Function.Periodic 
f c₁ → Function.Antipe…
-/
theorem Periodic.add_antiperiod_eq [AddMonoid α] [Neg β] (h1 : Periodic f c₁)
    (h2 : Antiperiodic f c₂) : f (c₁ + c₂) = -f 0 :=
  (h1.add_antiperiod h2).eq
/-
**Function.Periodic.sub_antiperiod_eq** 是 Mathlib 中的一个定理，位于命名空间 `Function.Period
ic`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c₁ c₂ : α} [inst : AddGroup α
] [inst_1 : InvolutiveNeg β],   Function.Periodic f c₁ → Function.Antiperiodic f
 c₂ → f (c₁ - c₂) = -f 0
参数：c₁ - c₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Antiperiodic.eq`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c
 : α} [inst : AddZeroClass α] [inst_1 : Neg β],   Function.Antiperiodic f c → f 
c = -f 0
· 使用定理 `Function.Periodic.sub_antiperiod`：∀ {α : Type u_1} {β : Type u_2} {f : α
 → β} {c₁ c₂ : α} [inst : AddGroup α] [inst_1 : InvolutiveNeg β],   Function.Per
iodic f c₁ → Function.…
-/
theorem Periodic.sub_antiperiod_eq [AddGroup α] [InvolutiveNeg β] (h1 : Periodic f c₁)
    (h2 : Antiperiodic f c₂) : f (c₁ - c₂) = -f 0 :=
  (h1.sub_antiperiod h2).eq
/-
**Function.Antiperiodic.mul** 是 Mathlib 中的一个定理，位于命名空间 `Function.Antiperiodic`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f g : α → β} {c : α} [inst : Add α] [inst
_1 : Mul β] [inst_2 : HasDistribNeg β],   Function.Antiperiodic f c → Function.A
ntiperiodic g c → Function.Periodic (f * g) c
参数：f * g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem Antiperiodic.mul [Add α] [Mul β] [HasDistribNeg β] (hf : Antiperiodic f c)
    (hg : Antiperiodic g c) : Periodic (f * g) c := by simp_all
/-
**Function.Antiperiodic.div** 是 Mathlib 中的一个定理，位于命名空间 `Function.Antiperiodic`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f g : α → β} {c : α} [inst : Add α] [inst
_1 : DivisionMonoid β]   [inst_2 : HasDistribNeg β], Function.Antiperiodic f c →
 Function.Antiperiodic g c → Function.Periodic (f / g) c
参数：f / g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `neg_div_neg_eq`：neg_div_neg_eq (a b : R) : -a / -b = a / b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem Antiperiodic.div [Add α] [DivisionMonoid β] [HasDistribNeg β] (hf : Antiperiodic f c)
    (hg : Antiperiodic g c) : Periodic (f / g) c := by simp_all [neg_div_neg_eq]

/-- For an antiperiodic function `f` with antiperiod `c`, summing `f` over a `Finset` shifted by
`c` (via `addRightEmbedding c`) negates the sum over the original `Finset`. -/
/-
**Function.Antiperiodic.sum_map_addRightEmbedding** 是 Mathlib 中的一个定理，位于命名空间 `Fun
ction.Antiperiodic`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {c : α} [inst : Add α] [inst_1
 : IsRightCancelAdd α]   [inst_2 : SubtractionCommMonoid β],   Function.Antiperi
odic f c → ∀ (s : Finset α), ∑ k ∈ Finset.map (addRightEmbedding c) s, f k = -∑ 
k ∈ s, f k
参数：s : Finset α；addRightEmbedding c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_map`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst : A
ddCommMonoid M] (s : Finset ι) (e : ι ↪ κ) (f : κ → M),   ∑ x ∈ Finset.map e s, 
f x …
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `addRightEmbedding_apply`：∀ {G : Type u_1} [inst : Add G] [inst_1 : IsRig
htCancelAdd G] (g h : G), (addRightEmbedding g) h = h + g
· 使用定理 `Finset.sum_neg_distrib`：∀ {ι : Type u_1} {G : Type u_5} {s : Finset ι} [
inst : SubtractionCommMonoid G] (f : ι → G),   ∑ x ∈ s, -f x = -∑ x ∈ s, f x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
For an antiperiodic function `f` with antiperiod `c`, summing `f` over a `Finset
` shifted by
`c` (via `addRightEmbedding c`) negates the sum over the original `Finset`.
-/
theorem Antiperiodic.sum_map_addRightEmbedding [Add α] [IsRightCancelAdd α]
    [SubtractionCommMonoid β] (hf : Antiperiodic f c) (s : Finset α) :
    ∑ k ∈ s.map (addRightEmbedding c), f k = -∑ k ∈ s, f k := by
  simp [hf _]

end Function

