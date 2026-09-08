/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Data.Prod.Basic
public import Mathlib.Logic.Function.Basic
public import Mathlib.Logic.Nontrivial.Defs
public import Mathlib.Logic.Unique
public import Mathlib.Order.Defs.LinearOrder

import Mathlib.Tactic.Attr.Register

/-!
# Nontrivial types

Results about `Nontrivial`.
-/

@[expose] public section

variable {α : Type*} {β : Type*}

-- `x` and `y` are explicit here, as they are often needed to guide typechecking of `h`.
/-
**nontrivial_of_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nontrivial_of_lt [Preorder α] (x y : α) (h : x < y) : Nontrivial α
参数：x y : α；h : x < y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
-/
theorem nontrivial_of_lt [Preorder α] (x y : α) (h : x < y) : Nontrivial α :=
  ⟨⟨x, y, ne_of_lt h⟩⟩
/-
**exists_pair_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_pair_lt (α : Type*) [Nontrivial α] [LinearOrder α] : exists x y : α
, x < y
参数：α : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_pair_ne`：exists_pair_ne (α : Type*) [Nontrivial α] : exists x y :
 α, x != y
· 使用引理 `lt_or_gt_of_ne`：lt_or_gt_of_ne (h : a != b) : a < b ∨ b < a
-/
theorem exists_pair_lt (α : Type*) [Nontrivial α] [LinearOrder α] : ∃ x y : α, x < y := by
  rcases exists_pair_ne α with ⟨x, y, hxy⟩
  cases lt_or_gt_of_ne hxy <;> exact ⟨_, _, ‹_›⟩
/-
**nontrivial_iff_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nontrivial_iff_lt [LinearOrder α] : Nontrivial α ↔ exists x y : α, x < y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_pair_lt`：exists_pair_lt (α : Type*) [Nontrivial α] [LinearOrder α
] : exists x y : α, x < y
· 使用定理 `nontrivial_of_lt`：nontrivial_of_lt [Preorder α] (x y : α) (h : x < y) : 
Nontrivial α
-/
theorem nontrivial_iff_lt [LinearOrder α] : Nontrivial α ↔ ∃ x y : α, x < y :=
  ⟨fun h ↦ @exists_pair_lt α h _, fun ⟨x, y, h⟩ ↦ nontrivial_of_lt x y h⟩
/-
**Subtype.nontrivial_iff_exists_ne** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subtype.nontrivial_iff_exists_ne (p : α -> Prop) (x : Subtype p) : Nontriv
ial (Subtype p) ↔ exists (y : α) (_ : p y), y != x
参数：p : α -> Prop；x : Subtype p。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nontrivial_iff_exists_ne`：nontrivial_iff_exists_ne (x : α) : Nontrivial 
α ↔ exists y, y != x
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem Subtype.nontrivial_iff_exists_ne (p : α → Prop) (x : Subtype p) :
    Nontrivial (Subtype p) ↔ ∃ (y : α) (_ : p y), y ≠ x := by
  simp only [_root_.nontrivial_iff_exists_ne x, Subtype.exists, Ne, Subtype.ext_iff]

open scoped Classical in
/-- An inhabited type is either nontrivial, or has a unique element. -/
/-
**nontrivialPSumUnique** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：nontrivialPSumUnique (α : Type*) [Inhabited α] : Nontrivial α oplus' Uniqu
e α
参数：α : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An inhabited type is either nontrivial, or has a unique element.
-/
noncomputable def nontrivialPSumUnique (α : Type*) [Inhabited α] :
    Nontrivial α ⊕' Unique α :=
  if h : Nontrivial α then PSum.inl h
  else
    PSum.inr
      { default := default,
        uniq := fun x : α ↦ by
          by_contra H
          exact h ⟨_, _, H⟩ }
/-
**Option.nontrivial** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Option.nontrivial [Nonempty α] : Nontrivial (Option α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Option.nontrivial [Nonempty α] : Nontrivial (Option α) := by
  inhabit α
  exact ⟨none, some default, nofun⟩
/-
**nontrivial_prod_right** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：nontrivial_prod_right [Nonempty α] [Nontrivial β] : Nontrivial (α × β)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.nontrivial`：∀ {α : Type u_1} {β : Type u_2} [Nontriv
ial β] {f : α → β}, Function.Surjective f → Nontrivial α
· 使用定理 `Prod.snd_surjective`：snd_surjective [h : Nonempty α] : Function.Surjecti
ve (@snd α β)
-/
instance nontrivial_prod_right [Nonempty α] [Nontrivial β] : Nontrivial (α × β) :=
  Prod.snd_surjective.nontrivial
/-
**nontrivial_prod_left** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：nontrivial_prod_left [Nontrivial α] [Nonempty β] : Nontrivial (α × β)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.nontrivial`：∀ {α : Type u_1} {β : Type u_2} [Nontriv
ial β] {f : α → β}, Function.Surjective f → Nontrivial α
· 使用定理 `Prod.fst_surjective`：fst_surjective [h : Nonempty β] : Function.Surjecti
ve (@fst α β)
-/
instance nontrivial_prod_left [Nontrivial α] [Nonempty β] : Nontrivial (α × β) :=
  Prod.fst_surjective.nontrivial

namespace Pi

variable {I : Type*} {f : I → Type*}

/-- A pi type is nontrivial if it's nonempty everywhere and nontrivial somewhere. -/
/-
**Pi.nontrivial_at** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：nontrivial_at (i' : I) [inst : forall i, Nonempty (f i)] [Nontrivial (f i'
)] : Nontrivial (forall i : I, f i)
参数：i' : I；f i；f i'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.nontrivial`：∀ {α : Type u_1} {β : Type u_2} [Nontrivi
al α] {f : α → β}, Function.Injective f → Nontrivial β
· 使用定理 `Function.update_injective`：update_injective (f : forall a, β a) (a' : α)
 : Injective (update f a')

--- 原说明 ---
A pi type is nontrivial if it's nonempty everywhere and nontrivial somewhere.
-/
theorem nontrivial_at (i' : I) [inst : ∀ i, Nonempty (f i)] [Nontrivial (f i')] :
    Nontrivial (∀ i : I, f i) := by
  classical
  let := Classical.decEq (∀ i : I, f i)
  exact (Function.update_injective (fun i ↦ Classical.choice (inst i)) i').nontrivial

/-- As a convenience, provide an instance automatically if `(f default)` is nontrivial.

If a different index has the non-trivial type, then use `haveI := nontrivial_at that_index`.
-/
/-
**Pi.nontrivial** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
形式化陈述：nontrivial [Inhabited I] [forall i, Nonempty (f i)] [Nontrivial (f default
)] : Nontrivial (forall i : I, f i)
参数：f i；f default。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Pi.nontrivial_at`：nontrivial_at (i' : I) [inst : forall i, Nonempty (f i
)] [Nontrivial (f i')] : Nontrivial (forall i : I, f i)

--- 原说明 ---
As a convenience, provide an instance automatically if `(f default)` is nontrivi
al.

If a different index has the non-trivial type, then use `haveI := nontrivial_at 
that_index`.
-/
instance nontrivial [Inhabited I] [∀ i, Nonempty (f i)] [Nontrivial (f default)] :
    Nontrivial (∀ i : I, f i) :=
  nontrivial_at default

end Pi

/-
**Function.nontrivial** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Function.nontrivial [h : Nonempty α] [Nontrivial β] : Nontrivial (α -> β)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Nonempty.elim`：∀ {α : Sort u} {p : Prop}, Nonempty α → (∀ (a : α), p) → 
p
· 使用定理 `Pi.nontrivial_at`：nontrivial_at (i' : I) [inst : forall i, Nonempty (f i
)] [Nontrivial (f i')] : Nontrivial (forall i : I, f i)
· 使用定理 `Nontrivial.to_nonempty`：∀ {α : Type u_1} [Nontrivial α], Nonempty α
-/
instance Function.nontrivial [h : Nonempty α] [Nontrivial β] : Nontrivial (α → β) :=
  h.elim fun a ↦ Pi.nontrivial_at a

@[nontriviality]
/-
**Subsingleton.le** 是 Mathlib 中的一个定理，位于命名空间 `Subsingleton`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] [Subsingleton α] (x y : α), x ≤ y
参数：x y : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
protected theorem Subsingleton.le [Preorder α] [Subsingleton α] (x y : α) : x ≤ y :=
  le_of_eq (Subsingleton.elim x y)
