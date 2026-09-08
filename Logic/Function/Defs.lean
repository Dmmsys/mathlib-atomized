/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Haitao Zhang
-/
module

public import Mathlib.Init

import Mathlib.Tactic.Attr.Register

/-!
# General operations on functions
-/

@[expose] public section

universe u₁ u₂ u₃ u₄ u₅

namespace Function

variable {α : Sort u₁} {β : Sort u₂} {φ : Sort u₃} {δ : Sort u₄} {ζ : Sort u₅}

/-
**Function.flip_def** 是 Mathlib 中的一个引理，位于命名空间 `Function`。
形式化陈述：flip_def {f : α -> β -> φ} : flip f = fun b a => f a b
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma flip_def {f : α → β → φ} : flip f = fun b a => f a b := rfl

attribute [mfld_simps] id_comp comp_id
/-
**Function.comp_assoc** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：comp_assoc (f : φ -> δ) (g : β -> φ) (h : α -> β) : (f ∘ g) ∘ h = f ∘ g ∘ 
h
参数：f : φ -> δ；g : β -> φ；h : α -> β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_assoc (f : φ → δ) (g : β → φ) (h : α → β) : (f ∘ g) ∘ h = f ∘ g ∘ h :=
  rfl

/- ### Dependent composition -/

/-- Composition of dependent functions: `(f ∘' g) x = f (g x)`, where type of `g x` depends on `x`
and type of `f (g x)` depends on `x` and `g x`. -/
@[inline, reducible]
/-
**Function.dcomp** 是 Mathlib 中的一个定义，位于命名空间 `Function`。
形式化陈述：dcomp {β : α -> Sort u₂} {φ : forall {x : α}, β x -> Sort u₃} (f : forall 
{x : α} (y : β x), φ y) (g : forall x, β x) : forall x, φ (g x)
参数：f : forall {x : α} (y : β x), φ y；g : forall x, β x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of dependent functions: `(f ∘' g) x = f (g x)`, where type of `g x` 
depends on `x`
and type of `f (g x)` depends on `x` and `g x`.
-/
def dcomp {β : α → Sort u₂} {φ : ∀ {x : α}, β x → Sort u₃} (f : ∀ {x : α} (y : β x), φ y)
    (g : ∀ x, β x) : ∀ x, φ (g x) := fun x => f (g x)

@[inherit_doc] infixr:80 " ∘' " => Function.dcomp

section DComp

variable {ι} {β : ι → Sort*} {φ : ∀ {i : ι}, β i → Sort*} (f : ∀ {i : ι} (y : β i), φ y)
    (g : ∀ i, β i) (i : ι)

/-
**Function.dcomp_def** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：dcomp_def : @f ∘' g = fun i => f (g i)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem dcomp_def : @f ∘' g = fun i => f (g i) := rfl
/-
**Function.dcomp_apply** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：dcomp_apply : dcomp @f g i = f (g i)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem dcomp_apply : dcomp @f g i = f (g i) := rfl
/-
**Function.dcomp_eq_comp** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：∀ {α : Sort u_3} {β : Sort u_4} {γ : Sort u_5} (f : β → γ) (g : α → β), (f
un {x} => f) ∘' g = f ∘ g
参数：f : β → γ；g : α → β；fun {x} => f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem dcomp_eq_comp {α β γ} (f : β → γ) (g : α → β) : f ∘' g = f ∘ g := rfl

end DComp

/- ### The product of functions -/

/-- Product of functions: `Function.prod f g i = (f i, g i)`, where the types of `f i` and
`g i` may depend on `i`. -/
/-
**Function.prod** 是 Mathlib 中的一个定义，位于命名空间 `Function`。
形式化陈述：{ι : Sort u_3} → {α : ι → Type u_1} → {β : ι → Type u_2} → ((i : ι) → α i)
 → ((i : ι) → β i) → (i : ι) → α i × β i
参数：(i : ι) → α i；(i : ι) → β i；i : ι。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Product of functions: `Function.prod f g i = (f i, g i)`, where the types of `f 
i` and
`g i` may depend on `i`.
-/
protected def prod {ι} {α β : ι → Type*} (f : ∀ i, α i) (g : ∀ i, β i) (i : ι) :
    α i × β i := (f i, g i)

section DProd

variable {ι} {α β : ι → Type*} (f f' : ∀ i, α i) (g g' : ∀ i, β i)

/-
**Function.prod_def** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：prod_def : Function.prod f g = fun i : ι => (f i, g i)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prod_def : Function.prod f g = fun i : ι => (f i, g i) := rfl
/-
**Function.prod_apply** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：∀ {ι : Sort u_3} {α : ι → Type u_1} {β : ι → Type u_2} (f : (i : ι) → α i)
 (g : (i : ι) → β i) (i : ι),   Function.prod f g i = (f i, g i)
参数：f : (i : ι) → α i；g : (i : ι) → β i；i : ι；f i, g i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, grind =] lemma prod_apply (i : ι) : Function.prod f g i = (f i, g i) := rfl

variable {f f' g g'} in
/-
**Function.prod_inj** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：∀ {ι : Sort u_3} {α : ι → Type u_1} {β : ι → Type u_2} {f f' : (i : ι) → α
 i} {g g' : (i : ι) → β i},   Function.prod f g = Function.prod f' g' ↔ f = f' ∧
 g = g'
参数：i : ι；i : ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] theorem prod_inj : Function.prod f g = Function.prod f' g' ↔ f = f' ∧ g = g' := by
  simp [funext_iff, Prod.ext_iff, forall_and]

end DProd

section Prod

variable {α β : Type*} {ι : Sort*} (f : ι → α) (g : ι → β)

/-
**Function.prod_ext_iff** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：prod_ext_iff {h h' : ι -> α × β} : h = h' ↔ Prod.fst ∘ h = Prod.fst ∘ h' ∧
 Prod.snd ∘ h = Prod.snd ∘ h'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.prod_inj`：∀ {ι : Sort u_3} {α : ι → Type u_1} {β : ι → Type u_2
} {f f' : (i : ι) → α i} {g g' : (i : ι) → β i},   Function.prod f g = Function.
prod f'…
-/
theorem prod_ext_iff {h h' : ι → α × β} :
    h = h' ↔ Prod.fst ∘ h = Prod.fst ∘ h' ∧ Prod.snd ∘ h = Prod.snd ∘ h' :=
  prod_inj
/-
**Function.prod_fst_snd** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2}, Function.prod Prod.fst Prod.snd = id
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma prod_fst_snd : Function.prod (Prod.fst : _ → α) (Prod.snd : _ → β) = id := rfl
/-
**Function.prod_snd_fst** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2}, Function.prod Prod.snd Prod.fst = Prod.sw
ap
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma prod_snd_fst : Function.prod (Prod.snd : _ → β) (Prod.fst : _ → α) = .swap := rfl
/-
**Function.fst_comp_prod** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_3} (f : ι → α) (g : ι → β), Pr
od.fst ∘ Function.prod f g = f
参数：f : ι → α；g : ι → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem fst_comp_prod : Prod.fst ∘ Function.prod f g = f := rfl
/-
**Function.snd_comp_prod** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_3} (f : ι → α) (g : ι → β), Pr
od.snd ∘ Function.prod f g = g
参数：f : ι → α；g : ι → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem snd_comp_prod : Prod.snd ∘ Function.prod f g = g := rfl
/-
**Function.prod_fst_comp_snd_comp** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_3} (h : ι → α × β), Function.p
rod (Prod.fst ∘ h) (Prod.snd ∘ h) = h
参数：h : ι → α × β；Prod.fst ∘ h；Prod.snd ∘ h。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem prod_fst_comp_snd_comp (h : ι → α × β) :
    Function.prod (Prod.fst ∘ h) (Prod.snd ∘ h) = h := rfl
/-
**Function.const_prod** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：const_prod (p : α × β) : const ι p = Function.prod (const ι p.1) (const ι 
p.2)
参数：p : α × β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem const_prod (p : α × β) : const ι p = Function.prod (const ι p.1) (const ι p.2) := rfl
/-
**Function.prod_const_const** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_3} (a : α) (b : β),   Function
.prod (Function.const ι a) (Function.const ι b) = Function.const ι (a, b)
参数：a : α；b : β；Function.const ι a；Function.const ι b；a, b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem prod_const_const (a : α) (b : β) :
    Function.prod (const ι a) (const ι b) = const ι (a, b) := rfl
/-
**Function.prod_comp** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：prod_comp {κ} (h : κ -> ι) : Function.prod f g ∘ h = Function.prod (f ∘ h)
 (g ∘ h)
参数：h : κ -> ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prod_comp {κ} (h : κ → ι) : Function.prod f g ∘ h = Function.prod (f ∘ h) (g ∘ h) := rfl
/-
**Function.prod_comp_fst_comp_snd** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：∀ {α₁ : Type u_4} {α₂ : Type u_5} {β₁ : Type u_6} {β₂ : Type u_7} (f : α₁ 
→ α₂) (g : β₁ → β₂),   Function.prod (f ∘ Prod.fst) (g ∘ Prod.snd) = Prod.map f 
g
参数：f : α₁ → α₂；g : β₁ → β₂；f ∘ Prod.fst；g ∘ Prod.snd。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem prod_comp_fst_comp_snd {α₁ α₂ β₁ β₂} (f : α₁ → α₂) (g : β₁ → β₂) :
    Function.prod (f ∘ Prod.fst) (g ∘ Prod.snd) = Prod.map f g := rfl
/-
**Function.map_comp_prod** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_3} (f : ι → α) (g : ι → β) {γ 
: Type u_4} {δ : Type u_5} (h : α → γ)   (k : β → δ), Prod.map h k ∘ Function.pr
od f g = Function.prod (h ∘ f) (k ∘ g)
参数：f : ι → α；g : ι → β；h : α → γ；k : β → δ；h ∘ f；k ∘ g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem map_comp_prod {γ δ} (h : α → γ) (k : β → δ) :
    Prod.map h k ∘ Function.prod f g = Function.prod (h ∘ f) (k ∘ g) := rfl
/-
**Function.prod_comp_prod** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：prod_comp_prod {γ δ} (h : α × β -> γ) (k : α × β -> δ) : Function.prod h k
 ∘ Function.prod f g = Function.prod (h ∘ Function.prod f g) (k ∘ Function.prod 
f g)
参数：h : α × β -> γ；k : α × β -> δ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prod_comp_prod {γ δ} (h : α × β → γ) (k : α × β → δ) :
    Function.prod h k ∘ Function.prod f g =
      Function.prod (h ∘ Function.prod f g) (k ∘ Function.prod f g) := rfl
/-
**Function.swap_comp_prod** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_3} (f : ι → α) (g : ι → β),   
Prod.swap ∘ Function.prod f g = Function.prod g f
参数：f : ι → α；g : ι → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem swap_comp_prod : Prod.swap ∘ Function.prod f g = Function.prod g f := rfl

end Prod

/- ### The diagonal map -/

/-- The diagonal map into `Prod`. -/
/-
**Function.diag** 是 Mathlib 中的一个定义，位于命名空间 `Function`。
形式化陈述：{α : Type u_1} → α → α × α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The diagonal map into `Prod`.
-/
@[inline] protected def diag {α} : α → α × α := fun a : α ↦ (a, a)

section Diag

variable {α β γ : Type*} (f : α → β) (g : α → γ) (a b : α)

/-
**Function.diag_def** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：diag_def : Function.diag = fun a : α => (a, a)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem diag_def : Function.diag = fun a : α ↦ (a, a) := rfl
/-
**Function.diag_apply** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：∀ {α : Type u_1} (a : α), Function.diag a = (a, a)
参数：a : α；a, a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, grind =] theorem diag_apply : Function.diag a = (a, a) := rfl
/-
**Function.diag_injective** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：diag_injective : Injective (α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem diag_injective : Injective (α := α) Function.diag := fun _ _ ↦ congrArg Prod.fst
/-
**Function.prod_id_id** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：∀ {α : Type u_1}, Function.prod id id = Function.diag
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem prod_id_id : Function.prod (@id α) id = Function.diag := rfl
/-
**Function.fst_comp_diag** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：∀ {α : Type u_1}, Prod.fst ∘ Function.diag = id
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem fst_comp_diag : Prod.fst ∘ Function.diag = @id α := rfl
/-
**Function.snd_comp_diag** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：∀ {α : Type u_1}, Prod.snd ∘ Function.diag = id
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem snd_comp_diag : Prod.snd ∘ Function.diag = @id α := rfl
/-
**Function.diag_comp** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} (f : α → β), Function.diag ∘ f = Function.
prod f f
参数：f : α → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem diag_comp : Function.diag ∘ f = Function.prod f f := rfl
/-
**Function.map_comp_diag** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} (f : α → β) (g : α → γ), Pr
od.map f g ∘ Function.diag = Function.prod f g
参数：f : α → β；g : α → γ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem map_comp_diag : Prod.map f g ∘ Function.diag = Function.prod f g := rfl
/-
**Function.swap_comp_diag** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：∀ {α : Type u_1}, Prod.swap ∘ Function.diag = Function.diag
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem swap_comp_diag : Prod.swap ∘ Function.diag = Function.diag (α := α) := rfl

end Diag

/- ### `onFun` function -/

/-- Given functions `f : β → β → φ` and `g : α → β`, produce a function `α → α → φ` that evaluates
`g` on each argument, then applies `f` to the results. Can be used, e.g., to transfer a relation
from `β` to `α`. -/
/-
**Function.onFun** 是 Mathlib 中的一个缩写定义，位于命名空间 `Function`。
形式化陈述：onFun (f : β -> β -> φ) (g : α -> β) : α -> α -> φ
参数：f : β -> β -> φ；g : α -> β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given functions `f : β → β → φ` and `g : α → β`, produce a function `α → α → φ` 
that evaluates
`g` on each argument, then applies `f` to the results. Can be used, e.g., to tra
nsfer a relation
from `β` to `α`.
-/
abbrev onFun (f : β → β → φ) (g : α → β) : α → α → φ := fun x y => f (g x) (g y)

@[inherit_doc onFun]
scoped infixl:2 " on " => onFun

/- ### The argument-reversing map -/

/-- For a two-argument function `f`, `swap f` is the same function but taking the arguments
in the reverse order. `swap f y x = f x y`. -/
/-
**Function.swap** 是 Mathlib 中的一个缩写定义，位于命名空间 `Function`。
形式化陈述：swap {φ : α -> β -> Sort u₃} (f : forall x y, φ x y) : forall y x, φ x y
参数：f : forall x y, φ x y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For a two-argument function `f`, `swap f` is the same function but taking the ar
guments
in the reverse order. `swap f y x = f x y`.
-/
abbrev swap {φ : α → β → Sort u₃} (f : ∀ x y, φ x y) : ∀ y x, φ x y := fun y x => f x y
/-
**Function.swap_def** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：swap_def {φ : α -> β -> Sort u₃} (f : forall x y, φ x y) : swap f = fun y 
x => f x y
参数：f : forall x y, φ x y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem swap_def {φ : α → β → Sort u₃} (f : ∀ x y, φ x y) : swap f = fun y x => f x y := rfl
/-
**Function.onFun_swap_comm** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：onFun_swap_comm (f : β -> β -> φ) (g : α -> β) : (swap f on g) = swap (f o
n g)
参数：f : β -> β -> φ；g : α -> β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem onFun_swap_comm (f : β → β → φ) (g : α → β) : (swap f on g) = swap (f on g) := rfl

/- ### Bijective functions -/

/-- A function is called bijective if it is both injective and surjective. -/
/-
**Function.Bijective** 是 Mathlib 中的一个定义，位于命名空间 `Function`。
形式化陈述：Bijective (f : α -> β)
参数：f : α -> β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function is called bijective if it is both injective and surjective.
-/
def Bijective (f : α → β) :=
  Injective f ∧ Surjective f
/-
**Function.Bijective.comp** 是 Mathlib 中的一个定理，位于命名空间 `Function.Bijective`。
形式化陈述：∀ {α : Sort u₁} {β : Sort u₂} {φ : Sort u₃} {g : β → φ} {f : α → β},   Fun
ction.Bijective g → Function.Bijective f → Function.Bijective (g ∘ f)
参数：g ∘ f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `Function.Surjective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3}
 {g : β → γ} {f : α → β},   Function.Surjective g → Function.Surjective f → Func
tion.Surjectiv…
-/
theorem Bijective.comp {g : β → φ} {f : α → β} : Bijective g → Bijective f → Bijective (g ∘ f)
  | ⟨h_ginj, h_gsurj⟩, ⟨h_finj, h_fsurj⟩ => ⟨h_ginj.comp h_finj, h_gsurj.comp h_fsurj⟩
/-
**Function.bijective_id** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：bijective_id : Bijective (@id α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.injective_id`：∀ {α : Sort u_1}, Function.Injective id
· 使用定理 `Function.surjective_id`：∀ {α : Sort u_1}, Function.Surjective id
-/
theorem bijective_id : Bijective (@id α) :=
  ⟨injective_id, surjective_id⟩

variable {f : α → β}
/-
**Function.Injective.beq_eq** 是 Mathlib 中的一个定理，位于命名空间 `Function.Injective`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : BEq α] [LawfulBEq α] [inst_2 : BEq
 β] [LawfulBEq β] {f : α → β},   Function.Injective f → ∀ {a b : α}, (f a == f b
) = (a == b)
参数：f a == f b；a == b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Bool.of_not_eq_true`：∀ {b : Bool}, ¬b = true → b = false
-/
theorem Injective.beq_eq {α β : Type*} [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β] {f : α → β}
    (I : Injective f) {a b : α} : (f a == f b) = (a == b) := by
  by_cases h : a == b <;> simp [h] <;> simpa [I.eq_iff] using h

/- ### Bicomposition -/

section Bicomp

variable {α β γ δ ε : Sort*}

/-- Compose a binary function `f` with a pair of unary functions `g` and `h`.
If both arguments of `f` have the same type and `g = h`, then `bicompl f g g = f on g`. -/
/-
**Function.bicompl** 是 Mathlib 中的一个定义，位于命名空间 `Function`。
形式化陈述：bicompl (f : γ -> δ -> ε) (g : α -> γ) (h : β -> δ) (a b)
参数：f : γ -> δ -> ε；g : α -> γ；h : β -> δ；a b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Compose a binary function `f` with a pair of unary functions `g` and `h`.
If both arguments of `f` have the same type and `g = h`, then `bicompl f g g = f
 on g`.
-/
def bicompl (f : γ → δ → ε) (g : α → γ) (h : β → δ) (a b) :=
  f (g a) (h b)

/-- Compose a unary function `f` with a binary function `g`. -/
/-
**Function.bicompr** 是 Mathlib 中的一个定义，位于命名空间 `Function`。
形式化陈述：bicompr (f : γ -> δ) (g : α -> β -> γ) (a b)
参数：f : γ -> δ；g : α -> β -> γ；a b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Compose a unary function `f` with a binary function `g`.
-/
def bicompr (f : γ → δ) (g : α → β → γ) (a b) :=
  f (g a b)

-- Suggested local notation:
local notation f " ∘₂ " g => bicompr f g
/-
**Function.uncurry_bicompr** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：uncurry_bicompr {α β γ δ} (f : α -> β -> γ) (g : γ -> δ) : uncurry (g ∘₂ f
) = g ∘ uncurry f
参数：f : α -> β -> γ；g : γ -> δ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem uncurry_bicompr {α β γ δ} (f : α → β → γ) (g : γ → δ) : uncurry (g ∘₂ f) = g ∘ uncurry f :=
  rfl
/-
**Function.uncurry_bicompl** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：uncurry_bicompl {α β γ δ ε} (f : γ -> δ -> ε) (g : α -> γ) (h : β -> δ) : 
uncurry (bicompl f g h) = uncurry f ∘ Prod.map g h
参数：f : γ -> δ -> ε；g : α -> γ；h : β -> δ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem uncurry_bicompl {α β γ δ ε} (f : γ → δ → ε) (g : α → γ) (h : β → δ) :
    uncurry (bicompl f g h) = uncurry f ∘ Prod.map g h :=
  rfl

end Bicomp

end Function

namespace Function

variable {α : Type u₁} {β : Type u₂}

/- ### Fixed points of functions -/

/-- A point `x` is a fixed point of `f : α → α` if `f x = x`. -/
/-
**Function.IsFixedPt** 是 Mathlib 中的一个定义，位于命名空间 `Function`。
形式化陈述：IsFixedPt (f : α -> α) (x : α)
参数：f : α -> α；x : α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A point `x` is a fixed point of `f : α → α` if `f x = x`.
-/
def IsFixedPt (f : α → α) (x : α) := f x = x

/-- If `x` is a fixed point of `f`, then `f x = x`. This is useful, e.g., for `rw` or `simp`. -/
/-
**Function.IsFixedPt.eq** 是 Mathlib 中的一个定理，位于命名空间 `Function.IsFixedPt`。
形式化陈述：∀ {α : Type u₁} {f : α → α} {x : α}, Function.IsFixedPt f x → f x = x
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `x` is a fixed point of `f`, then `f x = x`. This is useful, e.g., for `rw` o
r `simp`.
-/
protected theorem IsFixedPt.eq {f : α → α} {x : α} (hf : IsFixedPt f x) : f x = x :=
  hf
/-
**Function.IsFixedPt.decidable** 是 Mathlib 中的一个定义，位于命名空间 `Function.IsFixedPt`。
形式化陈述：{α : Type u₁} → [h : DecidableEq α] → {f : α → α} → {x : α} → Decidable (F
unction.IsFixedPt f x)
参数：Function.IsFixedPt f x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance IsFixedPt.decidable [h : DecidableEq α] {f : α → α} {x : α} : Decidable (IsFixedPt f x) :=
  h (f x) x

@[nontriviality]
/-
**Function.IsFixedPt.of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `Function.IsFixed
Pt`。
形式化陈述：∀ {α : Type u₁} [Subsingleton α] (f : α → α) (x : α), Function.IsFixedPt f
 x
参数：f : α → α；x : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
theorem IsFixedPt.of_subsingleton [Subsingleton α] (f : α → α) (x : α) : IsFixedPt f x :=
  Subsingleton.elim _ _

/-- Every point is a fixed point of `id`. -/
/-
**Function.isFixedPt_id** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：isFixedPt_id (x : α) : IsFixedPt id x
参数：x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Every point is a fixed point of `id`.
-/
theorem isFixedPt_id (x : α) : IsFixedPt id x :=
  rfl

/-- A function fixes every point iff it is the identity. -/
/-
**Function.forall_isFixedPt_iff** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：∀ {α : Type u₁} {f : α → α}, (∀ (x : α), Function.IsFixedPt f x) ↔ f = id
参数：∀ (x : α), Function.IsFixedPt f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Function.isFixedPt_id`：isFixedPt_id (x : α) : IsFixedPt id x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
A function fixes every point iff it is the identity.
-/
@[simp] theorem forall_isFixedPt_iff {f : α → α} : (∀ x, IsFixedPt f x) ↔ f = id :=
  ⟨funext, fun h ↦ h ▸ isFixedPt_id⟩

end Function

namespace Pi

variable {ι : Sort*} {α β : ι → Sort*}

/- ### `Pi.map` function -/

/-- Sends a dependent function `a : ∀ i, α i` to a dependent function `Pi.map f a : ∀ i, β i`
by applying `f i` to `i`-th component. -/
/-
**Pi.map** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：Pi.map {f g : β -> C} [HasProduct f] [HasProduct g] (p : forall b, f b ⟶ g
 b) : ∏ᶜ f ⟶ ∏ᶜ g
参数：p : forall b, f b ⟶ g b。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Sends a dependent function `a : ∀ i, α i` to a dependent function `Pi.map f a : 
∀ i, β i`
by applying `f i` to `i`-th component.
-/
protected def map (f : ∀ i, α i → β i) : (∀ i, α i) → (∀ i, β i) := fun a i ↦ f i (a i)

@[simp]
/-
**Pi.map_apply** 是 Mathlib 中的一个引理，位于命名空间 `Pi`。
形式化陈述：map_apply (f : forall i, α i -> β i) (a : forall i, α i) (i : ι) : Pi.map 
f a i = f i (a i)
参数：f : forall i, α i -> β i；a : forall i, α i；i : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map_apply (f : ∀ i, α i → β i) (a : ∀ i, α i) (i : ι) : Pi.map f a i = f i (a i) := rfl

end Pi

