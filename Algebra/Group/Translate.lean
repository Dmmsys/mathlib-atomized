/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.GroupTheory.GroupAction.DomAct.Basic

/-!
# Translation operator

This file defines the translation of a function from a group by an element of that group.

## Notation

`τ a f` is notation for `translate a f`.

## See also

Generally, translation is the same as acting on the domain by subtraction. This setting is
abstracted by `DomAddAct` in such a way that `τ a f = DomAddAct.mk (-a) +ᵥ f` (see
`translate_eq_domAddActMk_vadd`). Using `DomAddAct` is irritating in applications because of this
negation appearing inside `DomAddAct.mk`. Although mathematically equivalent, the pen and paper
convention is that translating is an action by subtraction, not by addition.
-/

@[expose] public section

open Function Set
open scoped Pointwise

variable {ι α β M G H : Type*} [AddCommGroup G]

/-- Translation of a function in a group by an element of that group.
`τ a f` is defined as `x ↦ f (x - a)`. -/
/-
**translate** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：translate (a : G) (f : G -> α) : G -> α
参数：a : G；f : G -> α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Translation of a function in a group by an element of that group.
`τ a f` is defined as `x ↦ f (x - a)`.
-/
def translate (a : G) (f : G → α) : G → α := fun x ↦ f (x - a)

@[inherit_doc] scoped[translate] notation "τ " => translate

open scoped translate
/-
**translate_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_2} {G : Type u_5} [inst : AddCommGroup G] (a : G) (f : G → α
) (x : G), translate a f x = f (x - a)
参数：a : G；f : G → α；x : G；x - a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma translate_apply (a : G) (f : G → α) (x : G) : τ a f x = f (x - a) := rfl
/-
**translate_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_2} {G : Type u_5} [inst : AddCommGroup G] (f : G → α), trans
late 0 f = f
参数：f : G → α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma translate_zero (f : G → α) : τ 0 f = f := by ext; simp
/-
**translate_translate** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：translate_translate (a b : G) (f : G -> α) : τ a (τ b f) = τ (a + b) f
参数：a b : G；f : G -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_sub`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b c : α), 
a - b - c = a - (b + c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma translate_translate (a b : G) (f : G → α) : τ a (τ b f) = τ (a + b) f := by
  ext; simp [sub_sub]
/-
**translate_add** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：translate_add (a b : G) (f : G -> α) : τ (a + b) f = τ a (τ b f)
参数：a b : G；f : G -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_sub`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b c : α), 
a - b - c = a - (b + c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma translate_add (a b : G) (f : G → α) : τ (a + b) f = τ a (τ b f) := by ext; simp [sub_sub]

/-- See `translate_add` -/
/-
**translate_add'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：translate_add' (a b : G) (f : G -> α) : τ (a + b) f = τ b (τ a f)
参数：a b : G；f : G -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用引理 `translate_add`：translate_add (a b : G) (f : G -> α) : τ (a + b) f = τ a 
(τ b f)

--- 原说明 ---
See `translate_add`
-/
lemma translate_add' (a b : G) (f : G → α) : τ (a + b) f = τ b (τ a f) := by
  rw [add_comm, translate_add]
/-
**translate_comm** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：translate_comm (a b : G) (f : G -> α) : τ a (τ b f) = τ b (τ a f)
参数：a b : G；f : G -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `translate_add`：translate_add (a b : G) (f : G -> α) : τ (a + b) f = τ a 
(τ b f)
· 使用引理 `translate_add'`：translate_add' (a b : G) (f : G -> α) : τ (a + b) f = τ 
b (τ a f)
-/
lemma translate_comm (a b : G) (f : G → α) : τ a (τ b f) = τ b (τ a f) := by
  rw [← translate_add, translate_add']

-- We make `simp` push the `τ` outside
/-
**comp_translate** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} {G : Type u_5} [inst : AddCommGroup G] (a 
: G) (f : G → α) (g : α → β),   g ∘ translate a f = translate a (g ∘ f)
参数：a : G；f : G → α；g : α → β；g ∘ f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma comp_translate (a : G) (f : G → α) (g : α → β) : g ∘ τ a f = τ a (g ∘ f) := rfl
/-
**translate_eq_domAddActMk_vadd** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：translate_eq_domAddActMk_vadd (a : G) (f : G -> α) : τ a f = DomAddAct.mk 
(-a) +ᵥ f
参数：a : G；f : G -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_neg_add`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b :
 α), a - b = -b + a
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma translate_eq_domAddActMk_vadd (a : G) (f : G → α) : τ a f = DomAddAct.mk (-a) +ᵥ f := by
  ext; simp [DomAddAct.vadd_apply, sub_eq_neg_add]

@[simp]
/-
**translate_smul_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：translate_smul_right [SMul H α] (a : G) (f : G -> α) (c : H) : τ a (c • f)
 = c • τ a f
参数：a : G；f : G -> α；c : H。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma translate_smul_right [SMul H α] (a : G) (f : G → α) (c : H) : τ a (c • f) = c • τ a f := rfl
/-
**translate_zero_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_2} {G : Type u_5} [inst : AddCommGroup G] [inst_1 : Zero α] 
(a : G), translate a 0 = 0
参数：a : G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma translate_zero_right [Zero α] (a : G) : τ a (0 : G → α) = 0 := rfl
/-
**translate_add_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：translate_add_right [Add α] (a : G) (f g : G -> α) : τ a (f + g) = τ a f +
 τ a g
参数：a : G；f g : G -> α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma translate_add_right [Add α] (a : G) (f g : G → α) : τ a (f + g) = τ a f + τ a g := rfl
/-
**translate_sub_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：translate_sub_right [Sub α] (a : G) (f g : G -> α) : τ a (f - g) = τ a f -
 τ a g
参数：a : G；f g : G -> α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma translate_sub_right [Sub α] (a : G) (f g : G → α) : τ a (f - g) = τ a f - τ a g := rfl
/-
**translate_neg_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：translate_neg_right [Neg α] (a : G) (f : G -> α) : τ a (-f) = -τ a f
参数：a : G；f : G -> α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma translate_neg_right [Neg α] (a : G) (f : G → α) : τ a (-f) = -τ a f := rfl

section AddCommMonoid
variable [AddCommMonoid M]

/-
**translate_sum_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：translate_sum_right (a : G) (f : ι -> G -> M) (s : Finset ι) : τ a (∑ i in
 s, f i) = ∑ i in s, τ a (f i)
参数：a : G；f : ι -> G -> M；s : Finset ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma translate_sum_right (a : G) (f : ι → G → M) (s : Finset ι) :
    τ a (∑ i ∈ s, f i) = ∑ i ∈ s, τ a (f i) := by ext; simp
/-
**sum_translate** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：sum_translate [Fintype G] (a : G) (f : G -> M) : ∑ b, τ a f b = ∑ b, f b
参数：a : G；f : G -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fintype.sum_equiv`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst 
: Fintype ι] [inst_1 : Fintype κ] [inst_2 : AddCommMonoid M]   (e : ι ≃ κ) (f : 
ι → M) …
-/
lemma sum_translate [Fintype G] (a : G) (f : G → M) : ∑ b, τ a f b = ∑ b, f b :=
  Fintype.sum_equiv (Equiv.subRight _) _ _ fun _ ↦ rfl

end AddCommMonoid

section AddCommGroup
variable [AddCommGroup H]

/-
**support_translate** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {G : Type u_5} {H : Type u_6} [inst : AddCommGroup G] [inst_1 : AddCommG
roup H] (a : G) (f : G → H),   Function.support (translate a f) = a +ᵥ Function.
support f
参数：a : G；f : G → H；translate a f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_eq_neg_add`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b :
 α), a - b = -b + a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma support_translate (a : G) (f : G → H) : support (τ a f) = a +ᵥ support f := by
  ext; simp [mem_vadd_set_iff_neg_vadd_mem, sub_eq_neg_add]

end AddCommGroup

variable [CommMonoid M]

/-
**translate_prod_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：translate_prod_right (a : G) (f : ι -> G -> M) (s : Finset ι) : τ a (∏ i i
n s, f i) = ∏ i in s, τ a (f i)
参数：a : G；f : ι -> G -> M；s : Finset ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_apply`：Finset.prod_apply {α : Type*} {M : α -> Type*} [foral
l a, CommMonoid (M a)] (a : α) (s : Finset ι) (g : ι -> forall a, M a) : (∏ c in
 s, g c…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma translate_prod_right (a : G) (f : ι → G → M) (s : Finset ι) :
    τ a (∏ i ∈ s, f i) = ∏ i ∈ s, τ a (f i) := by ext; simp
