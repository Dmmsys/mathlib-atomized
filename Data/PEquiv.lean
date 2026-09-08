/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.Data.Option.Basic
public import Batteries.Tactic.Congr
public import Mathlib.Data.Set.Basic
public import Mathlib.Tactic.Contrapose

/-!

# Partial Equivalences

In this file, we define partial equivalences `PEquiv`, which are a bijection between a subset of `α`
and a subset of `β`. Notationally, a `PEquiv` is denoted by "`≃.`" (note that the full stop is part
of the notation). The way we store these internally is with two functions `f : α → Option β` and
the reverse function `g : β → Option α`, with the condition that if `f a` is `some b`,
then `g b` is `some a`.

## Main results

- `PEquiv.ofSet`: creates a `PEquiv` from a set `s`,
  which sends an element to itself if it is in `s`.
- `PEquiv.single`: given two elements `a : α` and `b : β`, create a `PEquiv` that sends them to
  each other, and ignores all other elements.
- `PEquiv.injective_of_forall_ne_isSome`/`injective_of_forall_isSome`: If the domain of a `PEquiv`
  is all of `α` (except possibly one point), its `toFun` is injective.

## Canonical order

`PEquiv` is canonically ordered by inclusion; that is, if a function `f` defined on a subset `s`
is equal to `g` on that subset, but `g` is also defined on a larger set, then `f ≤ g`. We also have
a definition of `⊥`, which is the empty `PEquiv` (sends all to `none`), which in the end gives us a
`SemilatticeInf` with an `OrderBot` instance.

## Tags

pequiv, partial equivalence

-/

@[expose] public section

assert_not_exists RelIso

universe u v w x

/-- A `PEquiv` is a partial equivalence, a representation of a bijection between a subset
  of `α` and a subset of `β`. See also `PartialEquiv` for a version that requires `toFun` and
`invFun` to be globally defined functions and has `source` and `target` sets as extra fields. -/
/-
**PEquiv** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u → Type v → Type (max u v)
参数：max u v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `PEquiv` is a partial equivalence, a representation of a bijection between a s
ubset
  of `α` and a subset of `β`. See also `PartialEquiv` for a version that require
s `toFun` and
`invFun` to be globally defined functions and has `source` and `target` sets as 
extra fields.
-/
structure PEquiv (α : Type u) (β : Type v) where
  /-- The underlying partial function of a `PEquiv` -/
  toFun : α → Option β
  /-- The partial inverse of `toFun` -/
  invFun : β → Option α
  /-- `invFun` is the partial inverse of `toFun` -/
  inv : ∀ (a : α) (b : β), invFun b = some a ↔ toFun a = some b

/-- A `PEquiv` is a partial equivalence, a representation of a bijection between a subset
  of `α` and a subset of `β`. See also `PartialEquiv` for a version that requires `toFun` and
`invFun` to be globally defined functions and has `source` and `target` sets as extra fields. -/
infixr:25 " ≃. " => PEquiv

namespace PEquiv

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type x}

open Function Option

/-
**PEquiv.** 是 Mathlib 中的一个实例，位于命名空间 `PEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : FunLike (α ≃. β) α (Option β) :=
  { coe := toFun
    coe_injective := by
      rintro ⟨f₁, f₂, hf⟩ ⟨g₁, g₂, hg⟩ (rfl : f₁ = g₁)
      congr with y x
      simp only [hf, hg] }
/-
**PEquiv.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `PEquiv`。
形式化陈述：∀ {α : Type u} {β : Type v} (f₁ : α → Option β) (f₂ : β → Option α)   (h :
 ∀ (a : α) (b : β), f₂ b = some a ↔ f₁ a = some b), ⇑{ toFun := f₁, invFun := f₂
, inv := h } = f₁
参数：f₁ : α → Option β；f₂ : β → Option α；h : ∀ (a : α) (b : β), f₂ b = some a ↔ f₁
 a = some b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem coe_mk (f₁ : α → Option β) (f₂ h) : (mk f₁ f₂ h : α → Option β) = f₁ :=
  rfl
/-
**PEquiv.coe_mk_apply** 是 Mathlib 中的一个定理，位于命名空间 `PEquiv`。
形式化陈述：coe_mk_apply (f₁ : α -> Option β) (f₂ : β -> Option α) (h) (x : α) : (PEqu
iv.mk f₁ f₂ h : α -> Option β) x = f₁ x
参数：f₁ : α -> Option β；f₂ : β -> Option α；h；x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mk_apply (f₁ : α → Option β) (f₂ : β → Option α) (h) (x : α) :
    (PEquiv.mk f₁ f₂ h : α → Option β) x = f₁ x :=
  rfl
/-
**PEquiv.ext** 是 Mathlib 中的一个定理，位于命名空间 `PEquiv`。
形式化陈述：∀ {α : Type u} {β : Type v} {f g : α ≃. β}, (∀ (x : α), f x = g x) → f = g
参数：∀ (x : α), f x = g x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
@[ext] theorem ext {f g : α ≃. β} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h

/-- The identity map as a partial equivalence. -/
@[refl]
/-
**PEquiv.refl** 是 Mathlib 中的一个定义，位于命名空间 `PEquiv`。
形式化陈述：(α : Type u_1) → α ≃. α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity map as a partial equivalence.
-/
protected def refl (α : Type*) : α ≃. α where
  toFun := some
  invFun := some
  inv _ _ := eq_comm

/-- The inverse partial equivalence. -/
@[symm]
/-
**PEquiv.symm** 是 Mathlib 中的一个定义，位于命名空间 `PEquiv`。
形式化陈述：{α : Type u} → {β : Type v} → (α ≃. β) → β ≃. α
参数：α ≃. β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inverse partial equivalence.
-/
protected def symm (f : α ≃. β) : β ≃. α where
  toFun := f.2
  invFun := f.1
  inv _ _ := (f.inv _ _).symm
/-
**PEquiv.mem_iff_mem** 是 Mathlib 中的一个定理，位于命名空间 `PEquiv`。
形式化陈述：mem_iff_mem (f : α ≃. β) : forall {a : α} {b : β}, a in f.symm b ↔ b in f 
a
参数：f : α ≃. β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PEquiv.inv`：∀ {α : Type u} {β : Type v} (self : α ≃. β) (a : α) (b : β),
 self.invFun b = some a ↔ self.toFun a = some b
-/
theorem mem_iff_mem (f : α ≃. β) : ∀ {a : α} {b : β}, a ∈ f.symm b ↔ b ∈ f a :=
  f.3 _ _
/-
**PEquiv.eq_some_iff** 是 Mathlib 中的一个定理，位于命名空间 `PEquiv`。
形式化陈述：eq_some_iff (f : α ≃. β) : forall {a : α} {b : β}, f.symm b = some a ↔ f a
 = some b
参数：f : α ≃. β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PEquiv.inv`：∀ {α : Type u} {β : Type v} (self : α ≃. β) (a : α) (b : β),
 self.invFun b = some a ↔ self.toFun a = some b
-/
theorem eq_some_iff (f : α ≃. β) : ∀ {a : α} {b : β}, f.symm b = some a ↔ f a = some b :=
  f.3 _ _

/-- Composition of partial equivalences `f : α ≃. β` and `g : β ≃. γ`. -/
@[trans]
/-
**PEquiv.trans** 是 Mathlib 中的一个定义，位于命名空间 `PEquiv`。
形式化陈述：{α : Type u} → {β : Type v} → {γ : Type w} → (α ≃. β) → (β ≃. γ) → α ≃. γ
参数：α ≃. β；β ≃. γ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of partial equivalences `f : α ≃. β` and `g : β ≃. γ`.
-/
protected def trans (f : α ≃. β) (g : β ≃. γ) :
    α ≃. γ where
  toFun a := (f a).bind g
  invFun a := (g.symm a).bind f.symm
  inv a b := by simp_all [and_comm, eq_some_iff f, eq_some_iff g, bind_eq_some_iff]

@[simp]
/-
**PEquiv.refl_apply** 是 Mathlib 中的一个定理，位于命名空间 `PEquiv`。
形式化陈述：refl_apply (a : α) : PEquiv.refl α a = some a
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem refl_apply (a : α) : PEquiv.refl α a = some a :=
  rfl

@[simp]
/-
**PEquiv.symm_refl** 是 Mathlib 中的一个定理，位于命名空间 `PEquiv`。
形式化陈述：symm_refl : (PEquiv.refl α).symm = PEquiv.refl α
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm_refl : (PEquiv.refl α).symm = PEquiv.refl α :=
  rfl

@[simp]
/-
**PEquiv.symm_symm** 是 Mathlib 中的一个定理，位于命名空间 `PEquiv`。
形式化陈述：symm_symm (f : α ≃. β) : f.symm.symm = f
参数：f : α ≃. β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm_symm (f : α ≃. β) : f.symm.symm = f := rfl
/-
**PEquiv.symm_apply_eq** 是 Mathlib 中的一个定理，位于命名空间 `PEquiv`。
形式化陈述：symm_apply_eq (f : α ≃. β) {x : β} {y : α} : f.symm x = y ↔ x = f y
参数：f : α ≃. β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PEquiv.eq_some_iff`：eq_some_iff (f : α ≃. β) : forall {a : α} {b : β}, f
.symm b = some a ↔ f a = some b
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem symm_apply_eq (f : α ≃. β) {x : β} {y : α} : f.symm x = y ↔ x = f y := by
  rw [eq_some_iff, eq_comm]
/-
**PEquiv.eq_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `PEquiv`。
形式化陈述：eq_symm_apply (f : α ≃. β) {x : β} {y : α} : y = f.symm x ↔ f y = x
参数：f : α ≃. β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PEquiv.eq_some_iff`：eq_some_iff (f : α ≃. β) : forall {a : α} {b : β}, f
.symm b = some a ↔ f a = some b
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem eq_symm_apply (f : α ≃. β) {x : β} {y : α} : y = f.symm x ↔ f y = x := by
  rw [← eq_some_iff, eq_comm]
/-
**PEquiv.symm_bijective** 是 Mathlib 中的一个定理，位于命名空间 `PEquiv`。
形式化陈述：symm_bijective : Function.Bijective (PEquiv.symm : (α ≃. β) -> β ≃. α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.bijective_iff_has_inverse`：bijective_iff_has_inverse : Bijectiv
e f ↔ exists g, LeftInverse g f ∧ RightInverse g f
· 使用定理 `PEquiv.symm_symm`：symm_symm (f : α ≃. β) : f.symm.symm = f
-/
theorem symm_bijective : Function.Bijective (PEquiv.symm : (α ≃. β) → β ≃. α) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩
/-
**PEquiv.symm_injective** 是 Mathlib 中的一个定理，位于命名空间 `PEquiv`。
形式化陈述：symm_injective : Function.Injective (@PEquiv.symm α β)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Bijective.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β
}, Function.Bijective f → Function.Injective f
· 使用定理 `PEquiv.symm_bijective`：symm_bijective : Function.Bijective (PEquiv.symm 
: (α ≃. β) -> β ≃. α)
-/
theorem symm_injective : Function.Injective (@PEquiv.symm α β) :=
  symm_bijective.injective
/-
**PEquiv.trans_assoc** 是 Mathlib 中的一个定理，位于命名空间 `PEquiv`。
形式化陈述：trans_assoc (f : α ≃. β) (g : β ≃. γ) (h : γ ≃. δ) : (f.trans g).trans h =
 f.trans (g.trans h)
参数：f : α ≃. β；g : β ≃. γ；h : γ ≃. δ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PEquiv.ext`：∀ {α : Type u} {β : Type v} {f g : α ≃. β}, (∀ (x : α), f x 
= g x) → f = g
· 使用定理 `Option.bind_assoc`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} (x : O
ption α) (f : α → Option β) (g : β → Option γ),   (x.bind f).bind g = x.bind fun
 y => (…
-/
theorem trans_assoc (f : α ≃. β) (g : β ≃. γ) (h : γ ≃. δ) :
    (f.trans g).trans h = f.trans (g.trans h) :=
  ext fun _ => Option.bind_assoc _ _ _
/-
**PEquiv.mem_trans** 是 Mathlib 中的一个定理，位于命名空间 `PEquiv`。
形式化陈述：mem_trans (f : α ≃. β) (g : β ≃. γ) (a : α) (c : γ) : c in f.trans g a ↔ e
xists b, b in f a ∧ c in g b
参数：f : α ≃. β；g : β ≃. γ；a : α；c : γ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Option.bind_eq_some_iff`：∀ {α : Type u_1} {b : α} {α_1 : Type u_2} {x : 
Option α_1} {f : α_1 → Option α},   x.bind f = some b ↔ ∃ a, x = some a ∧ f a = 
some b
-/
theorem mem_trans (f : α ≃. β) (g : β ≃. γ) (a : α) (c : γ) :
    c ∈ f.trans g a ↔ ∃ b, b ∈ f a ∧ c ∈ g b :=
  Option.bind_eq_some_iff
/-
**PEquiv.trans_eq_some** 是 Mathlib 中的一个定理，位于命名空间 `PEquiv`。
形式化陈述：trans_eq_some (f : α ≃. β) (g : β ≃. γ) (a : α) (c : γ) : f.trans g a = so
me c ↔ exists b, f a = some b ∧ g b = some c
参数：f : α ≃. β；g : β ≃. γ；a : α；c : γ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Option.bind_eq_some_iff`：∀ {α : Type u_1} {b : α} {α_1 : Type u_2} {x : 
Option α_1} {f : α_1 → Option α},   x.bind f = some b ↔ ∃ a, x = some a ∧ f a = 
some b
-/
theorem trans_eq_some (f : α ≃. β) (g : β ≃. γ) (a : α) (c : γ) :
    f.trans g a = some c ↔ ∃ b, f a = some b ∧ g b = some c :=
  Option.bind_eq_some_iff
/-
**PEquiv.trans_eq_none** 是 Mathlib 中的一个定理，位于命名空间 `PEquiv`。
形式化陈述：trans_eq_none (f : α ≃. β) (g : β ≃. γ) (a : α) : f.trans g a = none ↔ for
all b c, b ∉ f a ∨ c ∉ g b
参数：f : α ≃. β；g : β ≃. γ；a : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `imp_iff_not_or`：imp_iff_not_or : a -> b ↔ ¬a ∨ b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b
-/
theorem trans_eq_none (f : α ≃. β) (g : β ≃. γ) (a : α) :
    f.trans g a = none ↔ ∀ b c, b ∉ f a ∨ c ∉ g b := by
  simp only [eq_none_iff_forall_not_mem, mem_trans, imp_iff_not_or.symm]
  push Not
  exact forall_comm

@[simp]
/-
**PEquiv.refl_trans** 是 Mathlib 中的一个定理，位于命名空间 `PEquiv`。
形式化陈述：refl_trans (f : α ≃. β) : (PEquiv.refl α).trans f = f
参数：f : α ≃. β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PEquiv.ext`：∀ {α : Type u} {β : Type v} {f g : α ≃. β}, (∀ (x : α), f x 
= g x) → f = g
· 使用定理 `Option.ext`：∀ {α : Type u_1} {o₁ o₂ : Option α}, (∀ (a : α), o₁ = some a
 ↔ o₂ = some a) → o₁ = o₂
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem refl_trans (f : α ≃. β) : (PEquiv.refl α).trans f = f := by
  ext; dsimp [PEquiv.trans]; rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**PEquiv.trans_refl** 是 Mathlib 中的一个定理，位于命名空间 `PEquiv`。
形式化陈述：trans_refl (f : α ≃. β) : f.trans (PEquiv.refl β) = f
参数：f : α ≃. β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PEquiv.ext`：∀ {α : Type u} {β : Type v} {f g : α ≃. β}, (∀ (x : α), f x 
= g x) → f = g
· 使用定理 `Option.ext`：∀ {α : Type u_1} {o₁ o₂ : Option α}, (∀ (a : α), o₁ = some a
 ↔ o₂ = some a) → o₁ = o₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Option.bind_congr'`：bind_congr' {f g : α -> Option β} {x y : Option α} (
hx : x = y) (hf : forall a in y, f a = g a) : x.bind f = y.bind g
· 使用定理 `Option.bind_fun_some`：∀ {α : Type u_1} (x : Option α), x.bind some = x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem trans_refl (f : α ≃. β) : f.trans (PEquiv.refl β) = f := by
  ext; dsimp [PEquiv.trans]; simp
/-
**PEquiv.inj** 是 Mathlib 中的一个定理，位于命名空间 `PEquiv`。
形式化陈述：∀ {α : Type u} {β : Type v} (f : α ≃. β) {a₁ a₂ : α} {b : β}, b ∈ f a₁ → b
 ∈ f a₂ → a₁ = a₂
参数：f : α ≃. β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PEquiv.mem_iff_mem`：mem_iff_mem (f : α ≃. β) : forall {a : α} {b : β}, a
 in f.symm b ↔ b in f a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Option.some.injEq`：∀ {α : Type u} (val val_1 : α), (some val = some val_
1) = (val = val_1)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem inj (f : α ≃. β) {a₁ a₂ : α} {b : β} (h₁ : b ∈ f a₁) (h₂ : b ∈ f a₂) :
    a₁ = a₂ := by rw [← mem_iff_mem] at *; cases h : f.symm b <;> simp_all

/-- If the domain of a `PEquiv` is `α` except a point, its forward direction is injective. -/
/-
**PEquiv.injective_of_forall_ne_isSome** 是 Mathlib 中的一个定理，位于命名空间 `PEquiv`。
形式化陈述：injective_of_forall_ne_isSome (f : α ≃. β) (a₂ : α) (h : forall a₁ : α, a₁
 != a₂ -> isSome (f a₁)) : Injective f
参数：f : α ≃. β；a₂ : α；h : forall a₁ : α, a₁ != a₂ -> isSome (f a₁)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.HasLeftInverse.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : 
α → β}, Function.HasLeftInverse f → Function.Injective f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_imp_comm`：not_imp_comm : ¬a -> b ↔ ¬b -> a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Bool.false_eq_true`：(false = true) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `PEquiv.eq_some_iff`：eq_some_iff (f : α ≃. β) : forall {a : α} {b : β}, f
.symm b = some a ↔ f a = some b

--- 原说明 ---
If the domain of a `PEquiv` is `α` except a point, its forward direction is inje
ctive.
-/
theorem injective_of_forall_ne_isSome (f : α ≃. β) (a₂ : α)
    (h : ∀ a₁ : α, a₁ ≠ a₂ → isSome (f a₁)) : Injective f :=
  HasLeftInverse.injective
    ⟨fun b => Option.recOn b a₂ fun b' => Option.recOn (f.symm b') a₂ id, fun x => by
      cases hfx : f x
      · have : x = a₂ := not_imp_comm.1 (h x) (hfx.symm ▸ by simp)
        simp [this]
      · dsimp only
        rw [(eq_some_iff f).2 hfx]
        rfl⟩

/-- If the domain of a `PEquiv` is all of `α`, its forward direction is injective. -/
/-
**PEquiv.injective_of_forall_isSome** 是 Mathlib 中的一个定理，位于命名空间 `PEquiv`。
形式化陈述：injective_of_forall_isSome {f : α ≃. β} (h : forall a : α, isSome (f a)) :
 Injective f
参数：h : forall a : α, isSome (f a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `PEquiv.injective_of_forall_ne_isSome`：injective_of_forall_ne_isSome (f :
 α ≃. β) (a₂ : α) (h : forall a₁ : α, a₁ != a₂ -> isSome (f a₁)) : Injective f

--- 原说明 ---
If the domain of a `PEquiv` is all of `α`, its forward direction is injective.
-/
theorem injective_of_forall_isSome {f : α ≃. β} (h : ∀ a : α, isSome (f a)) : Injective f :=
  (Classical.em (Nonempty α)).elim
    (fun hn => injective_of_forall_ne_isSome f (Classical.choice hn) fun a _ => h a) fun hn x =>
    (hn ⟨x⟩).elim

section OfSet

variable (s : Set α) [DecidablePred (· ∈ s)]

/-- Creates a `PEquiv` that is the identity on `s`, and `none` outside of it. -/
/-
**PEquiv.ofSet** 是 Mathlib 中的一个定义，位于命名空间 `PEquiv`。
形式化陈述：ofSet (s : Set α) [DecidablePred (· in s)] : α ≃. α where toFun a
参数：s : Set α；· in s。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Creates a `PEquiv` that is the identity on `s`, and `none` outside of it.
-/
def ofSet (s : Set α) [DecidablePred (· ∈ s)] :
    α ≃. α where
  toFun a := if a ∈ s then some a else none
  invFun a := if a ∈ s then some a else none
  inv a b := by
    split_ifs with hb ha ha
    · simp [eq_comm]
    · simp [ne_of_mem_of_not_mem hb ha]
    · simp [ne_of_mem_of_not_mem ha hb]
    · simp
/-
**PEquiv.mem_ofSet_self_iff** 是 Mathlib 中的一个定理，位于命名空间 `PEquiv`。
形式化陈述：mem_ofSet_self_iff {s : Set α} [DecidablePred (· in s)] {a : α} : a in ofS
et s a ↔ a in s
参数：· in s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
-/
theorem mem_ofSet_self_iff {s : Set α} [DecidablePred (· ∈ s)] {a : α} : a ∈ ofSet s a ↔ a ∈ s := by
  dsimp [ofSet]; split_ifs <;> simp [*]
/-
**PEquiv.mem_ofSet_iff** 是 Mathlib 中的一个定理，位于命名空间 `PEquiv`。
形式化陈述：mem_ofSet_iff {s : Set α} [DecidablePred (· in s)] {a b : α} : a in ofSet 
s b ↔ a = b ∧ a in s
参数：· in s。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mem_ofSet_iff {s : Set α} [DecidablePred (· ∈ s)] {a b : α} :
    a ∈ ofSet s b ↔ a = b ∧ a ∈ s := by
  dsimp [ofSet]
  grind

@[simp]
/-
**PEquiv.ofSet_eq_some_iff** 是 Mathlib 中的一个定理，位于命名空间 `PEquiv`。
形式化陈述：ofSet_eq_some_iff {s : Set α} {_ : DecidablePred (· in s)} {a b : α} : ofS
et s b = some a ↔ a = b ∧ a in s
参数：· in s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PEquiv.mem_ofSet_iff`：mem_ofSet_iff {s : Set α} [DecidablePred (· in s)]
 {a b : α} : a in ofSet s b ↔ a = b ∧ a in s
-/
theorem ofSet_eq_some_iff {s : Set α} {_ : DecidablePred (· ∈ s)} {a b : α} :
    ofSet s b = some a ↔ a = b ∧ a ∈ s :=
  mem_ofSet_iff
/-
**PEquiv.ofSet_eq_some_self_iff** 是 Mathlib 中的一个定理，位于命名空间 `PEquiv`。
形式化陈述：ofSet_eq_some_self_iff {s : Set α} {_ : DecidablePred (· in s)} {a : α} : 
ofSet s a = some a ↔ a in s
参数：· in s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PEquiv.mem_ofSet_self_iff`：mem_ofSet_self_iff {s : Set α} [DecidablePred
 (· in s)] {a : α} : a in ofSet s a ↔ a in s
-/
theorem ofSet_eq_some_self_iff {s : Set α} {_ : DecidablePred (· ∈ s)} {a : α} :
    ofSet s a = some a ↔ a ∈ s :=
  mem_ofSet_self_iff

@[simp]
/-
**PEquiv.ofSet_symm** 是 Mathlib 中的一个定理，位于命名空间 `PEquiv`。
形式化陈述：ofSet_symm : (ofSet s).symm = ofSet s
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofSet_symm : (ofSet s).symm = ofSet s :=
  rfl

@[simp]
/-
**PEquiv.ofSet_univ** 是 Mathlib 中的一个定理，位于命名空间 `PEquiv`。
形式化陈述：ofSet_univ : ofSet Set.univ = PEquiv.refl α
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofSet_univ : ofSet Set.univ = PEquiv.refl α :=
  rfl

@[simp]
/-
**PEquiv.ofSet_eq_refl** 是 Mathlib 中的一个定理，位于命名空间 `PEquiv`。
形式化陈述：ofSet_eq_refl {s : Set α} [DecidablePred (· in s)] : ofSet s = PEquiv.refl
 α ↔ s = Set.univ
参数：· in s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.eq_univ_iff_forall`：eq_univ_iff_forall {s : Set α} : s = univ ↔ fora
ll x, x in s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PEquiv.mem_ofSet_self_iff`：mem_ofSet_self_iff {s : Set α} [DecidablePred
 (· in s)] {a : α} : a in ofSet s a ↔ a in s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `PEquiv.ofSet.congr_simp`：∀ {α : Type u} (s s_1 : Set α),   s = s_1 →    
 ∀ {inst : DecidablePred fun x => x ∈ s} [inst_1 : DecidablePred fun x => x ∈ s_
1], PEquiv.of…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ofSet_eq_refl {s : Set α} [DecidablePred (· ∈ s)] :
    ofSet s = PEquiv.refl α ↔ s = Set.univ :=
  ⟨fun h => by
    rw [Set.eq_univ_iff_forall]
    intro
    rw [← mem_ofSet_self_iff, h]
    exact rfl, fun h => by simp only [← ofSet_univ, h]⟩

end OfSet

/-
**PEquiv.symm_trans_rev** 是 Mathlib 中的一个定理，位于命名空间 `PEquiv`。
形式化陈述：symm_trans_rev (f : α ≃. β) (g : β ≃. γ) : (f.trans g).symm = g.symm.trans
 f.symm
参数：f : α ≃. β；g : β ≃. γ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm_trans_rev (f : α ≃. β) (g : β ≃. γ) : (f.trans g).symm = g.symm.trans f.symm :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-
**PEquiv.self_trans_symm** 是 Mathlib 中的一个定理，位于命名空间 `PEquiv`。
形式化陈述：self_trans_symm (f : α ≃. β) : f.trans f.symm = ofSet { a | (f a).isSome }
参数：f : α ≃. β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PEquiv.ext`：∀ {α : Type u} {β : Type v} {f g : α ≃. β}, (∀ (x : α), f x 
= g x) → f = g
· 使用定理 `Option.ext`：∀ {α : Type u_1} {o₁ o₂ : Option α}, (∀ (a : α), o₁ = some a
 ↔ o₂ = some a) → o₁ = o₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `PEquiv.eq_some_iff`：eq_some_iff (f : α ≃. β) : forall {a : α} {b : β}, f
.symm b = some a ↔ f a = some b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `PEquiv.inj`：∀ {α : Type u} {β : Type v} (f : α ≃. β) {a₁ a₂ : α} {b : β}
, b ∈ f a₁ → b ∈ f a₂ → a₁ = a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem self_trans_symm (f : α ≃. β) : f.trans f.symm = ofSet { a | (f a).isSome } := by
  ext
  dsimp [PEquiv.trans]
  simp only [eq_some_iff f, Option.isSome_iff_exists, bind_eq_some_iff,
    ofSet_eq_some_iff]
  constructor
  · rintro ⟨b, hb₁, hb₂⟩
    exact ⟨PEquiv.inj _ hb₂ hb₁, b, hb₂⟩
  · simp +contextual
/-
**PEquiv.symm_trans_self** 是 Mathlib 中的一个定理，位于命名空间 `PEquiv`。
形式化陈述：symm_trans_self (f : α ≃. β) : f.symm.trans f = ofSet { b | (f.symm b).isS
ome }
参数：f : α ≃. β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PEquiv.symm_injective`：symm_injective : Function.Injective (@PEquiv.symm
 α β)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PEquiv.self_trans_symm`：self_trans_symm (f : α ≃. β) : f.trans f.symm = 
ofSet { a | (f a).isSome }
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem symm_trans_self (f : α ≃. β) : f.symm.trans f = ofSet { b | (f.symm b).isSome } :=
  symm_injective <| by simp [symm_trans_rev, self_trans_symm, -symm_symm]
/-
**PEquiv.trans_symm_eq_iff_forall_isSome** 是 Mathlib 中的一个定理，位于命名空间 `PEquiv`。
形式化陈述：trans_symm_eq_iff_forall_isSome {f : α ≃. β} : f.trans f.symm = PEquiv.ref
l α ↔ forall a, isSome (f a)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PEquiv.self_trans_symm`：self_trans_symm (f : α ≃. β) : f.trans f.symm = 
ofSet { a | (f a).isSome }
· 使用定理 `PEquiv.ofSet_eq_refl`：ofSet_eq_refl {s : Set α} [DecidablePred (· in s)]
 : ofSet s = PEquiv.refl α ↔ s = Set.univ
· 使用定理 `Set.eq_univ_iff_forall`：eq_univ_iff_forall {s : Set α} : s = univ ↔ fora
ll x, x in s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem trans_symm_eq_iff_forall_isSome {f : α ≃. β} :
    f.trans f.symm = PEquiv.refl α ↔ ∀ a, isSome (f a) := by
  rw [self_trans_symm, ofSet_eq_refl, Set.eq_univ_iff_forall]; rfl
/-
**PEquiv.instBotPEquiv** 是 Mathlib 中的一个实例，位于命名空间 `PEquiv`。
形式化陈述：instBotPEquiv : Bot (α ≃. β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instBotPEquiv : Bot (α ≃. β) :=
  ⟨{  toFun := fun _ => none
      invFun := fun _ => none
      inv := by simp }⟩
/-
**PEquiv.** 是 Mathlib 中的一个实例，位于命名空间 `PEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (α ≃. β) :=
  ⟨⊥⟩

@[simp]
/-
**PEquiv.bot_apply** 是 Mathlib 中的一个定理，位于命名空间 `PEquiv`。
形式化陈述：bot_apply (a : α) : (⊥ : α ≃. β) a = none
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bot_apply (a : α) : (⊥ : α ≃. β) a = none :=
  rfl

@[simp]
/-
**PEquiv.symm_bot** 是 Mathlib 中的一个定理，位于命名空间 `PEquiv`。
形式化陈述：symm_bot : (⊥ : α ≃. β).symm = ⊥
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm_bot : (⊥ : α ≃. β).symm = ⊥ :=
  rfl

@[simp]
/-
**PEquiv.trans_bot** 是 Mathlib 中的一个定理，位于命名空间 `PEquiv`。
形式化陈述：trans_bot (f : α ≃. β) : f.trans (⊥ : β ≃. γ) = ⊥
参数：f : α ≃. β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PEquiv.ext`：∀ {α : Type u} {β : Type v} {f g : α ≃. β}, (∀ (x : α), f x 
= g x) → f = g
· 使用定理 `Option.ext`：∀ {α : Type u_1} {o₁ o₂ : Option α}, (∀ (a : α), o₁ = some a
 ↔ o₂ = some a) → o₁ = o₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Option.bind_congr'`：bind_congr' {f g : α -> Option β} {x y : Option α} (
hx : x = y) (hf : forall a in y, f a = g a) : x.bind f = y.bind g
· 使用定理 `Option.bind_fun_none`：∀ {α : Type u_1} {β : Type u_2} (x : Option α), (x
.bind fun x => none) = none
· 使用定理 `PEquiv.mk.congr_simp`：∀ {α : Type u} {β : Type v} (toFun toFun_1 : α → O
ption β) (e_toFun : toFun = toFun_1) (invFun invFun_1 : β → Option α)   (e_invFu
n : invFun…
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem trans_bot (f : α ≃. β) : f.trans (⊥ : β ≃. γ) = ⊥ := by
  ext; dsimp [PEquiv.trans]; simp

@[simp]
/-
**PEquiv.bot_trans** 是 Mathlib 中的一个定理，位于命名空间 `PEquiv`。
形式化陈述：bot_trans (f : β ≃. γ) : (⊥ : α ≃. β).trans f = ⊥
参数：f : β ≃. γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PEquiv.ext`：∀ {α : Type u} {β : Type v} {f g : α ≃. β}, (∀ (x : α), f x 
= g x) → f = g
· 使用定理 `Option.ext`：∀ {α : Type u_1} {o₁ o₂ : Option α}, (∀ (a : α), o₁ = some a
 ↔ o₂ = some a) → o₁ = o₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Option.bind_congr'`：bind_congr' {f g : α -> Option β} {x y : Option α} (
hx : x = y) (hf : forall a in y, f a = g a) : x.bind f = y.bind g
· 使用定理 `Option.bind_fun_none`：∀ {α : Type u_1} {β : Type u_2} (x : Option α), (x
.bind fun x => none) = none
· 使用定理 `PEquiv.mk.congr_simp`：∀ {α : Type u} {β : Type v} (toFun toFun_1 : α → O
ption β) (e_toFun : toFun = toFun_1) (invFun invFun_1 : β → Option α)   (e_invFu
n : invFun…
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem bot_trans (f : β ≃. γ) : (⊥ : α ≃. β).trans f = ⊥ := by
  ext; dsimp [PEquiv.trans]; simp
/-
**PEquiv.isSome_symm_get** 是 Mathlib 中的一个定理，位于命名空间 `PEquiv`。
形式化陈述：isSome_symm_get (f : α ≃. β) {a : α} (h : isSome (f a)) : isSome (f.symm (
Option.get _ h))
参数：f : α ≃. β；h : isSome (f a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Option.isSome_iff_exists`：∀ {α : Type u_1} {x : Option α}, x.isSome = tr
ue ↔ ∃ a, x = some a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PEquiv.eq_some_iff`：eq_some_iff (f : α ≃. β) : forall {a : α} {b : β}, f
.symm b = some a ↔ f a = some b
· 使用定理 `Option.some_get`：∀ {α : Type u_1} {x : Option α} (h : x.isSome = true), 
some (x.get h) = x
-/
theorem isSome_symm_get (f : α ≃. β) {a : α} (h : isSome (f a)) :
    isSome (f.symm (Option.get _ h)) :=
  isSome_iff_exists.2 ⟨a, by rw [f.eq_some_iff, some_get]⟩

section Single

variable [DecidableEq α] [DecidableEq β] [DecidableEq γ]

/-- Create a `PEquiv` which sends `a` to `b` and `b` to `a`, but is otherwise `none`. -/
/-
**PEquiv.single** 是 Mathlib 中的一个定义，位于命名空间 `PEquiv`。
形式化陈述：single (a : α) (b : β) : α ≃. β where toFun x
参数：a : α；b : β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Create a `PEquiv` which sends `a` to `b` and `b` to `a`, but is otherwise `none`
.
-/
def single (a : α) (b : β) :
    α ≃. β where
  toFun x := if x = a then some b else none
  invFun x := if x = b then some a else none
  inv x y := by
    split_ifs with h1 h2
    · simp [*]
    · simp only [some.injEq, iff_false] at *
      exact Ne.symm h2
    · simp only [some.injEq, false_iff] at *
      exact Ne.symm h1
    · simp
/-
**PEquiv.mem_single** 是 Mathlib 中的一个定理，位于命名空间 `PEquiv`。
形式化陈述：mem_single (a : α) (b : β) : b in single a b a
参数：a : α；b : β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
theorem mem_single (a : α) (b : β) : b ∈ single a b a :=
  if_pos rfl
/-
**PEquiv.mem_single_iff** 是 Mathlib 中的一个定理，位于命名空间 `PEquiv`。
形式化陈述：mem_single_iff (a₁ a₂ : α) (b₁ b₂ : β) : b₁ in single a₂ b₂ a₁ ↔ a₁ = a₂ ∧
 b₁ = b₂
参数：a₁ a₂ : α；b₁ b₂ : β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Option.some.injEq`：∀ {α : Type u} (val val_1 : α), (some val = some val_
1) = (val = val_1)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
-/
theorem mem_single_iff (a₁ a₂ : α) (b₁ b₂ : β) : b₁ ∈ single a₂ b₂ a₁ ↔ a₁ = a₂ ∧ b₁ = b₂ := by
  dsimp [single]; split_ifs <;> simp [*, eq_comm]

@[simp]
/-
**PEquiv.symm_single** 是 Mathlib 中的一个定理，位于命名空间 `PEquiv`。
形式化陈述：symm_single (a : α) (b : β) : (single a b).symm = single b a
参数：a : α；b : β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm_single (a : α) (b : β) : (single a b).symm = single b a :=
  rfl

@[simp]
/-
**PEquiv.single_apply** 是 Mathlib 中的一个定理，位于命名空间 `PEquiv`。
形式化陈述：single_apply (a : α) (b : β) : single a b a = some b
参数：a : α；b : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
theorem single_apply (a : α) (b : β) : single a b a = some b :=
  if_pos rfl
/-
**PEquiv.single_apply_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `PEquiv`。
形式化陈述：single_apply_of_ne {a₁ a₂ : α} (h : a₁ != a₂) (b : β) : single a₁ b a₂ = n
one
参数：h : a₁ != a₂；b : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
-/
theorem single_apply_of_ne {a₁ a₂ : α} (h : a₁ ≠ a₂) (b : β) : single a₁ b a₂ = none :=
  if_neg h.symm
/-
**PEquiv.single_trans_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `PEquiv`。
形式化陈述：single_trans_of_mem (a : α) {b : β} {c : γ} {f : β ≃. γ} (h : c in f b) : 
(single a b).trans f = single a c
参数：a : α；h : c in f b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PEquiv.ext`：∀ {α : Type u} {β : Type v} {f g : α ≃. β}, (∀ (x : α), f x 
= g x) → f = g
· 使用定理 `Option.ext`：∀ {α : Type u_1} {o₁ o₂ : Option α}, (∀ (a : α), o₁ = some a
 ↔ o₂ = some a) → o₁ = o₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Option.bind_congr'`：bind_congr' {f g : α -> Option β} {x y : Option α} (
hx : x = y) (hf : forall a in y, f a = g a) : x.bind f = y.bind g
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Option.some.injEq`：∀ {α : Type u} (val val_1 : α), (some val = some val_
1) = (val = val_1)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
-/
theorem single_trans_of_mem (a : α) {b : β} {c : γ} {f : β ≃. γ} (h : c ∈ f b) :
    (single a b).trans f = single a c := by
  ext
  dsimp [single, PEquiv.trans]
  split_ifs <;> simp_all
/-
**PEquiv.trans_single_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `PEquiv`。
形式化陈述：trans_single_of_mem {a : α} {b : β} (c : γ) {f : α ≃. β} (h : b in f a) : 
f.trans (single b c) = single a c
参数：c : γ；h : b in f a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PEquiv.symm_injective`：symm_injective : Function.Injective (@PEquiv.symm
 α β)
· 使用定理 `PEquiv.single_trans_of_mem`：single_trans_of_mem (a : α) {b : β} {c : γ} 
{f : β ≃. γ} (h : c in f b) : (single a b).trans f = single a c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `PEquiv.mem_iff_mem`：mem_iff_mem (f : α ≃. β) : forall {a : α} {b : β}, a
 in f.symm b ↔ b in f a
-/
theorem trans_single_of_mem {a : α} {b : β} (c : γ) {f : α ≃. β} (h : b ∈ f a) :
    f.trans (single b c) = single a c :=
  symm_injective <| single_trans_of_mem _ ((mem_iff_mem f).2 h)

@[simp]
/-
**PEquiv.single_trans_single** 是 Mathlib 中的一个定理，位于命名空间 `PEquiv`。
形式化陈述：single_trans_single (a : α) (b : β) (c : γ) : (single a b).trans (single b
 c) = single a c
参数：a : α；b : β；c : γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PEquiv.single_trans_of_mem`：single_trans_of_mem (a : α) {b : β} {c : γ} 
{f : β ≃. γ} (h : c in f b) : (single a b).trans f = single a c
· 使用定理 `PEquiv.mem_single`：mem_single (a : α) (b : β) : b in single a b a
-/
theorem single_trans_single (a : α) (b : β) (c : γ) :
    (single a b).trans (single b c) = single a c :=
  single_trans_of_mem _ (mem_single _ _)

@[simp]
/-
**PEquiv.single_subsingleton_eq_refl** 是 Mathlib 中的一个定理，位于命名空间 `PEquiv`。
形式化陈述：single_subsingleton_eq_refl [Subsingleton α] (a b : α) : single a b = PEqu
iv.refl α
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PEquiv.ext`：∀ {α : Type u} {β : Type v} {f g : α ≃. β}, (∀ (x : α), f x 
= g x) → f = g
· 使用定理 `Option.ext`：∀ {α : Type u_1} {o₁ o₂ : Option α}, (∀ (a : α), o₁ = some a
 ↔ o₂ = some a) → o₁ = o₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem single_subsingleton_eq_refl [Subsingleton α] (a b : α) : single a b = PEquiv.refl α := by
  ext i j
  dsimp [single]
  rw [if_pos (Subsingleton.elim i a), Subsingleton.elim i j, Subsingleton.elim b j]
/-
**PEquiv.trans_single_of_eq_none** 是 Mathlib 中的一个定理，位于命名空间 `PEquiv`。
形式化陈述：trans_single_of_eq_none {b : β} (c : γ) {f : δ ≃. β} (h : f.symm b = none)
 : f.trans (single b c) = ⊥
参数：c : γ；h : f.symm b = none。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PEquiv.ext`：∀ {α : Type u} {β : Type v} {f g : α ≃. β}, (∀ (x : α), f x 
= g x) → f = g
· 使用定理 `Option.ext`：∀ {α : Type u_1} {o₁ o₂ : Option α}, (∀ (a : α), o₁ = some a
 ↔ o₂ = some a) → o₁ = o₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `PEquiv.eq_some_iff`：eq_some_iff (f : α ≃. β) : forall {a : α} {b : β}, f
.symm b = some a ↔ f a = some b
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem trans_single_of_eq_none {b : β} (c : γ) {f : δ ≃. β} (h : f.symm b = none) :
    f.trans (single b c) = ⊥ := by
  ext
  simp only [eq_none_iff_forall_not_mem, Option.mem_def, f.eq_some_iff] at h
  dsimp [PEquiv.trans, single]
  simp only [bind_eq_some_iff, iff_false, not_exists, not_and, reduceCtorEq]
  intros
  split_ifs <;> simp_all
/-
**PEquiv.single_trans_of_eq_none** 是 Mathlib 中的一个定理，位于命名空间 `PEquiv`。
形式化陈述：single_trans_of_eq_none (a : α) {b : β} {f : β ≃. δ} (h : f b = none) : (s
ingle a b).trans f = ⊥
参数：a : α；h : f b = none。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PEquiv.symm_injective`：symm_injective : Function.Injective (@PEquiv.symm
 α β)
· 使用定理 `PEquiv.trans_single_of_eq_none`：trans_single_of_eq_none {b : β} (c : γ) 
{f : δ ≃. β} (h : f.symm b = none) : f.trans (single b c) = ⊥
-/
theorem single_trans_of_eq_none (a : α) {b : β} {f : β ≃. δ} (h : f b = none) :
    (single a b).trans f = ⊥ :=
  symm_injective <| trans_single_of_eq_none _ h
/-
**PEquiv.single_trans_single_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `PEquiv`。
形式化陈述：single_trans_single_of_ne {b₁ b₂ : β} (h : b₁ != b₂) (a : α) (c : γ) : (si
ngle a b₁).trans (single b₂ c) = ⊥
参数：h : b₁ != b₂；a : α；c : γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PEquiv.single_trans_of_eq_none`：single_trans_of_eq_none (a : α) {b : β} 
{f : β ≃. δ} (h : f b = none) : (single a b).trans f = ⊥
· 使用定理 `PEquiv.single_apply_of_ne`：single_apply_of_ne {a₁ a₂ : α} (h : a₁ != a₂)
 (b : β) : single a₁ b a₂ = none
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
-/
theorem single_trans_single_of_ne {b₁ b₂ : β} (h : b₁ ≠ b₂) (a : α) (c : γ) :
    (single a b₁).trans (single b₂ c) = ⊥ :=
  single_trans_of_eq_none _ (single_apply_of_ne h.symm _)

end Single

section Order

/-
**PEquiv.instPartialOrderPEquiv** 是 Mathlib 中的一个实例，位于命名空间 `PEquiv`。
形式化陈述：instPartialOrderPEquiv : PartialOrder (α ≃. β) where le f g
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instPartialOrderPEquiv : PartialOrder (α ≃. β) where
  le f g := ∀ (a : α) (b : β), b ∈ f a → b ∈ g a
  le_refl _ _ _ := id
  le_trans _ _ _ fg gh a b := gh a b ∘ fg a b
  le_antisymm f g fg gf :=
    ext
      (by
        intro a
        rcases h : g a with _ | b
        · exact eq_none_iff_forall_not_mem.2 fun b hb => Option.not_mem_none b <| h ▸ fg a b hb
        · exact gf _ _ h)
/-
**PEquiv.le_def** 是 Mathlib 中的一个定理，位于命名空间 `PEquiv`。
形式化陈述：le_def {f g : α ≃. β} : f <= g ↔ forall (a : α) (b : β), b in f a -> b in 
g a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem le_def {f g : α ≃. β} : f ≤ g ↔ ∀ (a : α) (b : β), b ∈ f a → b ∈ g a :=
  Iff.rfl
/-
**PEquiv.** 是 Mathlib 中的一个实例，位于命名空间 `PEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : OrderBot (α ≃. β) :=
  { instBotPEquiv with bot_le := fun _ _ _ h => (not_mem_none _ h).elim }
/-
**PEquiv.** 是 Mathlib 中的一个实例，位于命名空间 `PEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DecidableEq α] [DecidableEq β] : SemilatticeInf (α ≃. β) :=
  { instPartialOrderPEquiv with
    inf := fun f g =>
      { toFun := fun a => if f a = g a then f a else none
        invFun := fun b => if f.symm b = g.symm b then f.symm b else none
        inv := fun a b => by
          have hf := @mem_iff_mem _ _ f a b
          have hg := @mem_iff_mem _ _ g a b
          simp only [Option.mem_def] at *
          grind }
    inf_le_left := fun _ _ _ _ => by simp only [coe_mk, mem_def]; split_ifs <;> simp [*]
    inf_le_right := fun _ _ _ _ => by simp only [coe_mk, mem_def]; split_ifs <;> simp [*]
    le_inf := fun f g h fg gh a b => by
      intro H
      have hf := fg a b H
      have hg := gh a b H
      simp only [Option.mem_def, PEquiv.coe_mk_apply] at *
      rw [hf, hg, if_pos rfl] }

end Order

end PEquiv

namespace Equiv

variable {α : Type*} {β : Type*} {γ : Type*}

/-- Turns an `Equiv` into a `PEquiv` of the whole type. -/
/-
**Equiv.toPEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：toPEquiv (f : α ≃ β) : α ≃. β where toFun
参数：f : α ≃ β。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Turns an `Equiv` into a `PEquiv` of the whole type.
-/
def toPEquiv (f : α ≃ β) : α ≃. β where
  toFun := some ∘ f
  invFun := some ∘ f.symm
  inv := by simp [Equiv.eq_symm_apply, eq_comm]

@[simp]
/-
**Equiv.toPEquiv_refl** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：toPEquiv_refl : (Equiv.refl α).toPEquiv = PEquiv.refl α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
-/
theorem toPEquiv_refl : (Equiv.refl α).toPEquiv = PEquiv.refl α :=
  rfl
/-
**Equiv.toPEquiv_trans** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：toPEquiv_trans (f : α ≃ β) (g : β ≃ γ) : (f.trans g).toPEquiv = f.toPEquiv
.trans g.toPEquiv
参数：f : α ≃ β；g : β ≃ γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
-/
theorem toPEquiv_trans (f : α ≃ β) (g : β ≃ γ) :
    (f.trans g).toPEquiv = f.toPEquiv.trans g.toPEquiv :=
  rfl
/-
**Equiv.toPEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：toPEquiv_symm (f : α ≃ β) : f.symm.toPEquiv = f.toPEquiv.symm
参数：f : α ≃ β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem toPEquiv_symm (f : α ≃ β) : f.symm.toPEquiv = f.toPEquiv.symm :=
  rfl

@[simp]
/-
**Equiv.toPEquiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：toPEquiv_apply (f : α ≃ β) (x : α) : f.toPEquiv x = some (f x)
参数：f : α ≃ β；x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toPEquiv_apply (f : α ≃ β) (x : α) : f.toPEquiv x = some (f x) :=
  rfl

end Equiv

