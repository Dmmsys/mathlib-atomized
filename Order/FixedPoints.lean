/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau, Yury Kudryashov
-/
module

public import Mathlib.Dynamics.FixedPoints.Basic
public import Mathlib.Order.Hom.Order
public import Mathlib.Order.BourbakiWitt

/-!
# Fixed point construction on complete lattices

This file sets up the basic theory of fixed points of a monotone function in a complete lattice.

## Main definitions

* `OrderHom.lfp`: The least fixed point of a bundled monotone function.
* `OrderHom.gfp`: The greatest fixed point of a bundled monotone function.
* `OrderHom.prevFixed`: The greatest fixed point of a bundled monotone function smaller than or
  equal to a given element.
* `OrderHom.nextFixed`: The least fixed point of a bundled monotone function greater than or
  equal to a given element.
* `fixedPoints.completeLattice`: The Knaster-Tarski theorem: fixed points of a monotone
  self-map of a complete lattice form themselves a complete lattice.

## Tags

fixed point, complete lattice, monotone function
-/

@[expose] public section


universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

open Function (fixedPoints IsFixedPt)

namespace OrderHom

section Basic

variable [CompleteLattice α] (f : α →o α)

/-- Least fixed point of a monotone function -/
/-
**OrderHom.lfp** 是 Mathlib 中的一个定义，位于命名空间 `OrderHom`。
形式化陈述：lfp : (α ->o α) ->o α where toFun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Least fixed point of a monotone function
-/
def lfp : (α →o α) →o α where
  toFun f := sInf { a | f a ≤ a }
  monotone' _ _ hle := sInf_le_sInf fun a ha => (hle a).trans ha

/-- Greatest fixed point of a monotone function -/
/-
**OrderHom.gfp** 是 Mathlib 中的一个定义，位于命名空间 `OrderHom`。
形式化陈述：gfp : (α ->o α) ->o α where toFun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Greatest fixed point of a monotone function
-/
def gfp : (α →o α) →o α where
  toFun f := sSup { a | a ≤ f a }
  monotone' _ _ hle := sSup_le_sSup fun a ha => le_trans ha (hle a)
/-
**OrderHom.lfp_le** 是 Mathlib 中的一个定理，位于命名空间 `OrderHom`。
形式化陈述：lfp_le {a : α} (h : f a <= a) : f.lfp <= a
参数：h : f a <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sInf_le`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, a ∈ s → sInf s ≤ a
-/
theorem lfp_le {a : α} (h : f a ≤ a) : f.lfp ≤ a :=
  sInf_le h
/-
**OrderHom.lfp_le_fixed** 是 Mathlib 中的一个定理，位于命名空间 `OrderHom`。
形式化陈述：lfp_le_fixed {a : α} (h : f a = a) : f.lfp <= a
参数：h : f a = a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderHom.lfp_le`：lfp_le {a : α} (h : f a <= a) : f.lfp <= a
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
-/
theorem lfp_le_fixed {a : α} (h : f a = a) : f.lfp ≤ a :=
  f.lfp_le h.le
/-
**OrderHom.le_lfp** 是 Mathlib 中的一个定理，位于命名空间 `OrderHom`。
形式化陈述：le_lfp {a : α} (h : forall b, f b <= b -> a <= b) : a <= f.lfp
参数：h : forall b, f b <= b -> a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_sInf`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, (∀ b ∈ s, a ≤ b) → a ≤ sInf s
-/
theorem le_lfp {a : α} (h : ∀ b, f b ≤ b → a ≤ b) : a ≤ f.lfp :=
  le_sInf h
/-
**OrderHom.map_le_lfp** 是 Mathlib 中的一个定理，位于命名空间 `OrderHom`。
形式化陈述：map_le_lfp {a : α} (ha : a <= f.lfp) : f a <= f.lfp
参数：ha : a <= f.lfp。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderHom.le_lfp`：le_lfp {a : α} (h : forall b, f b <= b -> a <= b) : a <
= f.lfp
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `OrderHom.mono`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [inst
_1 : Preorder β] (f : α →o β), Monotone ⇑f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `le_sInf_iff`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set
 α} {a : α}, a ≤ sInf s ↔ ∀ b ∈ s, a ≤ b
-/
theorem map_le_lfp {a : α} (ha : a ≤ f.lfp) : f a ≤ f.lfp :=
  f.le_lfp fun _ hb => (f.mono <| le_sInf_iff.1 ha _ hb).trans hb

@[simp]
/-
**OrderHom.map_lfp** 是 Mathlib 中的一个定理，位于命名空间 `OrderHom`。
形式化陈述：map_lfp : f f.lfp = f.lfp
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderHom.map_le_lfp`：map_le_lfp {a : α} (ha : a <= f.lfp) : f a <= f.lfp
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `OrderHom.lfp_le`：lfp_le {a : α} (h : f a <= a) : f.lfp <= a
· 使用定理 `OrderHom.mono`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [inst
_1 : Preorder β] (f : α →o β), Monotone ⇑f
-/
theorem map_lfp : f f.lfp = f.lfp :=
  have h : f f.lfp ≤ f.lfp := f.map_le_lfp le_rfl
  h.antisymm <| f.lfp_le <| f.mono h
/-
**OrderHom.isFixedPt_lfp** 是 Mathlib 中的一个定理，位于命名空间 `OrderHom`。
形式化陈述：isFixedPt_lfp : IsFixedPt f f.lfp
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderHom.map_lfp`：map_lfp : f f.lfp = f.lfp
-/
theorem isFixedPt_lfp : IsFixedPt f f.lfp :=
  f.map_lfp
/-
**OrderHom.lfp_le_map** 是 Mathlib 中的一个定理，位于命名空间 `OrderHom`。
形式化陈述：lfp_le_map {a : α} (ha : f.lfp <= a) : f.lfp <= f a
参数：ha : f.lfp <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OrderHom.map_lfp`：map_lfp : f f.lfp = f.lfp
· 使用定理 `OrderHom.mono`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [inst
_1 : Preorder β] (f : α →o β), Monotone ⇑f
-/
theorem lfp_le_map {a : α} (ha : f.lfp ≤ a) : f.lfp ≤ f a :=
  calc
    f.lfp = f f.lfp := f.map_lfp.symm
    _ ≤ f a := f.mono ha
/-
**OrderHom.isLeast_lfp_le** 是 Mathlib 中的一个定理，位于命名空间 `OrderHom`。
形式化陈述：isLeast_lfp_le : IsLeast { a | f a <= a } f.lfp
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `OrderHom.map_lfp`：map_lfp : f f.lfp = f.lfp
· 使用定理 `OrderHom.lfp_le`：lfp_le {a : α} (h : f a <= a) : f.lfp <= a
-/
theorem isLeast_lfp_le : IsLeast { a | f a ≤ a } f.lfp :=
  ⟨f.map_lfp.le, fun _ => f.lfp_le⟩
/-
**OrderHom.isLeast_lfp** 是 Mathlib 中的一个定理，位于命名空间 `OrderHom`。
形式化陈述：isLeast_lfp : IsLeast (fixedPoints f) f.lfp
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderHom.isFixedPt_lfp`：isFixedPt_lfp : IsFixedPt f f.lfp
· 使用定理 `OrderHom.lfp_le_fixed`：lfp_le_fixed {a : α} (h : f a = a) : f.lfp <= a
-/
theorem isLeast_lfp : IsLeast (fixedPoints f) f.lfp :=
  ⟨f.isFixedPt_lfp, fun _ => f.lfp_le_fixed⟩
/-
**OrderHom.lfp_induction** 是 Mathlib 中的一个定理，位于命名空间 `OrderHom`。
形式化陈述：lfp_induction {p : α -> Prop} (step : forall a, p a -> a <= f.lfp -> p (f 
a)) (hSup : forall s, (forall a in s, p a) -> p (sSup s)) : p f.lfp
参数：step : forall a, p a -> a <= f.lfp -> p (f a)；hSup : forall s, (forall a in s
, p a) -> p (sSup s)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sSup_le`：sSup_le (h : forall b in s, b <= a) : sSup s <= a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `OrderHom.map_le_lfp`：map_le_lfp {a : α} (ha : a <= f.lfp) : f a <= f.lfp
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `OrderHom.lfp_le`：lfp_le {a : α} (h : f a <= a) : f.lfp <= a
· 使用定理 `le_sSup`：le_sSup (h : a in s) : a <= sSup s
-/
theorem lfp_induction {p : α → Prop} (step : ∀ a, p a → a ≤ f.lfp → p (f a))
    (hSup : ∀ s, (∀ a ∈ s, p a) → p (sSup s)) : p f.lfp := by
  set s := { a | a ≤ f.lfp ∧ p a }
  specialize hSup s fun a => And.right
  suffices sSup s = f.lfp from this ▸ hSup
  have h : sSup s ≤ f.lfp := sSup_le fun b => And.left
  have hmem : f (sSup s) ∈ s := ⟨f.map_le_lfp h, step _ hSup h⟩
  exact h.antisymm (f.lfp_le <| le_sSup hmem)
/-
**OrderHom.le_gfp** 是 Mathlib 中的一个定理，位于命名空间 `OrderHom`。
形式化陈述：le_gfp {a : α} (h : a <= f a) : a <= f.gfp
参数：h : a <= f a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_sSup`：le_sSup (h : a in s) : a <= sSup s
-/
theorem le_gfp {a : α} (h : a ≤ f a) : a ≤ f.gfp :=
  le_sSup h
/-
**OrderHom.gfp_le** 是 Mathlib 中的一个定理，位于命名空间 `OrderHom`。
形式化陈述：gfp_le {a : α} (h : forall b, b <= f b -> b <= a) : f.gfp <= a
参数：h : forall b, b <= f b -> b <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sSup_le`：sSup_le (h : forall b in s, b <= a) : sSup s <= a
-/
theorem gfp_le {a : α} (h : ∀ b, b ≤ f b → b ≤ a) : f.gfp ≤ a :=
  sSup_le h
/-
**OrderHom.isFixedPt_gfp** 是 Mathlib 中的一个定理，位于命名空间 `OrderHom`。
形式化陈述：isFixedPt_gfp : IsFixedPt f f.gfp
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderHom.isFixedPt_lfp`：isFixedPt_lfp : IsFixedPt f f.lfp
-/
theorem isFixedPt_gfp : IsFixedPt f f.gfp :=
  f.dual.isFixedPt_lfp

@[simp]
/-
**OrderHom.map_gfp** 是 Mathlib 中的一个定理，位于命名空间 `OrderHom`。
形式化陈述：map_gfp : f f.gfp = f.gfp
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderHom.map_lfp`：map_lfp : f f.lfp = f.lfp
-/
theorem map_gfp : f f.gfp = f.gfp :=
  f.dual.map_lfp
/-
**OrderHom.map_le_gfp** 是 Mathlib 中的一个定理，位于命名空间 `OrderHom`。
形式化陈述：map_le_gfp {a : α} (ha : a <= f.gfp) : f a <= f.gfp
参数：ha : a <= f.gfp。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderHom.lfp_le_map`：lfp_le_map {a : α} (ha : f.lfp <= a) : f.lfp <= f a
-/
theorem map_le_gfp {a : α} (ha : a ≤ f.gfp) : f a ≤ f.gfp :=
  f.dual.lfp_le_map ha
/-
**OrderHom.gfp_le_map** 是 Mathlib 中的一个定理，位于命名空间 `OrderHom`。
形式化陈述：gfp_le_map {a : α} (ha : f.gfp <= a) : f.gfp <= f a
参数：ha : f.gfp <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderHom.map_le_lfp`：map_le_lfp {a : α} (ha : a <= f.lfp) : f a <= f.lfp
-/
theorem gfp_le_map {a : α} (ha : f.gfp ≤ a) : f.gfp ≤ f a :=
  f.dual.map_le_lfp ha
/-
**OrderHom.isGreatest_gfp_le** 是 Mathlib 中的一个定理，位于命名空间 `OrderHom`。
形式化陈述：isGreatest_gfp_le : IsGreatest { a | a <= f a } f.gfp
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderHom.isLeast_lfp_le`：isLeast_lfp_le : IsLeast { a | f a <= a } f.lfp
-/
theorem isGreatest_gfp_le : IsGreatest { a | a ≤ f a } f.gfp :=
  f.dual.isLeast_lfp_le
/-
**OrderHom.isGreatest_gfp** 是 Mathlib 中的一个定理，位于命名空间 `OrderHom`。
形式化陈述：isGreatest_gfp : IsGreatest (fixedPoints f) f.gfp
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderHom.isLeast_lfp`：isLeast_lfp : IsLeast (fixedPoints f) f.lfp
-/
theorem isGreatest_gfp : IsGreatest (fixedPoints f) f.gfp :=
  f.dual.isLeast_lfp
/-
**OrderHom.gfp_induction** 是 Mathlib 中的一个定理，位于命名空间 `OrderHom`。
形式化陈述：gfp_induction {p : α -> Prop} (step : forall a, p a -> f.gfp <= a -> p (f 
a)) (hInf : forall s, (forall a in s, p a) -> p (sInf s)) : p f.gfp
参数：step : forall a, p a -> f.gfp <= a -> p (f a)；hInf : forall s, (forall a in s
, p a) -> p (sInf s)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderHom.lfp_induction`：lfp_induction {p : α -> Prop} (step : forall a, 
p a -> a <= f.lfp -> p (f a)) (hSup : forall s, (forall a in s, p a) -> p (sSup 
s)) : p f.lf…
-/
theorem gfp_induction {p : α → Prop} (step : ∀ a, p a → f.gfp ≤ a → p (f a))
    (hInf : ∀ s, (∀ a ∈ s, p a) → p (sInf s)) : p f.gfp :=
  f.dual.lfp_induction step hInf
/-
**OrderHom.lfp_le_gfp** 是 Mathlib 中的一个定理，位于命名空间 `OrderHom`。
形式化陈述：lfp_le_gfp : f.lfp <= f.gfp
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderHom.lfp_le_fixed`：lfp_le_fixed {a : α} (h : f a = a) : f.lfp <= a
· 使用定理 `OrderHom.isFixedPt_gfp`：isFixedPt_gfp : IsFixedPt f f.gfp
-/
theorem lfp_le_gfp : f.lfp ≤ f.gfp :=
  f.lfp_le_fixed f.isFixedPt_gfp

end Basic

section Eqn

variable [CompleteLattice α] [CompleteLattice β] (f : β →o α) (g : α →o β)

-- Rolling rule
/-
**OrderHom.map_lfp_comp** 是 Mathlib 中的一个定理，位于命名空间 `OrderHom`。
形式化陈述：map_lfp_comp : f (g.comp f).lfp = (f.comp g).lfp
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `OrderHom.mono`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [inst
_1 : Preorder β] (f : α →o β), Monotone ⇑f
· 使用定理 `OrderHom.lfp_le_fixed`：lfp_le_fixed {a : α} (h : f a = a) : f.lfp <= a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `OrderHom.map_lfp`：map_lfp : f f.lfp = f.lfp
· 使用定理 `OrderHom.lfp_le`：lfp_le {a : α} (h : f a <= a) : f.lfp <= a
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
-/
theorem map_lfp_comp : f (g.comp f).lfp = (f.comp g).lfp :=
  le_antisymm ((f.comp g).map_lfp ▸ f.mono (lfp_le_fixed _ <| congr_arg g (f.comp g).map_lfp)) <|
    lfp_le _ (congr_arg f (g.comp f).map_lfp).le
/-
**OrderHom.map_gfp_comp** 是 Mathlib 中的一个定理，位于命名空间 `OrderHom`。
形式化陈述：map_gfp_comp : f (g.comp f).gfp = (f.comp g).gfp
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderHom.map_lfp_comp`：map_lfp_comp : f (g.comp f).lfp = (f.comp g).lfp
-/
theorem map_gfp_comp : f (g.comp f).gfp = (f.comp g).gfp :=
  f.dual.map_lfp_comp g.dual

-- Diagonal rule
/-
**OrderHom.lfp_lfp** 是 Mathlib 中的一个定理，位于命名空间 `OrderHom`。
形式化陈述：lfp_lfp (h : α ->o α ->o α) : (lfp.comp h).lfp = h.onDiag.lfp
参数：h : α ->o α ->o α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `OrderHom.lfp_le`：lfp_le {a : α} (h : f a <= a) : f.lfp <= a
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `OrderHom.map_lfp`：map_lfp : f f.lfp = f.lfp
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem lfp_lfp (h : α →o α →o α) : (lfp.comp h).lfp = h.onDiag.lfp := by
  let a := (lfp.comp h).lfp
  refine (lfp_le _ ?_).antisymm (lfp_le _ (Eq.le ?_))
  · exact lfp_le _ h.onDiag.map_lfp.le
  have ha : (lfp ∘ h) a = a := (lfp.comp h).map_lfp
  calc
    h a a = h a (h a).lfp := congr_arg (h a) ha.symm
    _ = (h a).lfp := (h a).map_lfp
    _ = a := ha
/-
**OrderHom.gfp_gfp** 是 Mathlib 中的一个定理，位于命名空间 `OrderHom`。
形式化陈述：gfp_gfp (h : α ->o α ->o α) : (gfp.comp h).gfp = h.onDiag.gfp
参数：h : α ->o α ->o α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderHom.lfp_lfp`：lfp_lfp (h : α ->o α ->o α) : (lfp.comp h).lfp = h.onD
iag.lfp
-/
theorem gfp_gfp (h : α →o α →o α) : (gfp.comp h).gfp = h.onDiag.gfp :=
  @lfp_lfp αᵒᵈ _ <| (OrderHom.dualIso αᵒᵈ αᵒᵈ).symm.toOrderEmbedding.toOrderHom.comp h.dual

end Eqn

section PrevNext

variable [CompleteLattice α] (f : α →o α)

/-
**OrderHom.gfp_const_inf_le** 是 Mathlib 中的一个定理，位于命名空间 `OrderHom`。
形式化陈述：gfp_const_inf_le (x : α) : (const α x ⊓ f).gfp <= x
参数：x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderHom.gfp_le`：gfp_le {a : α} (h : forall b, b <= f b -> b <= a) : f.g
fp <= a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
-/
theorem gfp_const_inf_le (x : α) : (const α x ⊓ f).gfp ≤ x :=
  (gfp_le _) fun _ hb => hb.trans inf_le_left

/-- Previous fixed point of a monotone map. If `f` is a monotone self-map of a complete lattice and
`x` is a point such that `f x ≤ x`, then `f.prevFixed x hx` is the greatest fixed point of `f`
that is less than or equal to `x`. -/
/-
**OrderHom.prevFixed** 是 Mathlib 中的一个定义，位于命名空间 `OrderHom`。
形式化陈述：prevFixed (x : α) (hx : f x <= x) : fixedPoints f
参数：x : α；hx : f x <= x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Previous fixed point of a monotone map. If `f` is a monotone self-map of a compl
ete lattice and
`x` is a point such that `f x ≤ x`, then `f.prevFixed x hx` is the greatest fixe
d point of `f`
that is less than or equal to `x`.
-/
def prevFixed (x : α) (hx : f x ≤ x) : fixedPoints f :=
  ⟨(const α x ⊓ f).gfp,
    calc
      f (const α x ⊓ f).gfp = x ⊓ f (const α x ⊓ f).gfp :=
        Eq.symm <| inf_of_le_right <| (f.mono <| f.gfp_const_inf_le x).trans hx
      _ = (const α x ⊓ f).gfp := (const α x ⊓ f).map_gfp
      ⟩

/-- Next fixed point of a monotone map. If `f` is a monotone self-map of a complete lattice and
`x` is a point such that `x ≤ f x`, then `f.nextFixed x hx` is the least fixed point of `f`
that is greater than or equal to `x`. -/
/-
**OrderHom.nextFixed** 是 Mathlib 中的一个定义，位于命名空间 `OrderHom`。
形式化陈述：nextFixed (x : α) (hx : x <= f x) : fixedPoints f
参数：x : α；hx : x <= f x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Next fixed point of a monotone map. If `f` is a monotone self-map of a complete 
lattice and
`x` is a point such that `x ≤ f x`, then `f.nextFixed x hx` is the least fixed p
oint of `f`
that is greater than or equal to `x`.
-/
def nextFixed (x : α) (hx : x ≤ f x) : fixedPoints f :=
  { f.dual.prevFixed x hx with val := (const α x ⊔ f).lfp }
/-
**OrderHom.prevFixed_le** 是 Mathlib 中的一个定理，位于命名空间 `OrderHom`。
形式化陈述：prevFixed_le {x : α} (hx : f x <= x) : ↑(f.prevFixed x hx) <= x
参数：hx : f x <= x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderHom.gfp_const_inf_le`：gfp_const_inf_le (x : α) : (const α x ⊓ f).gf
p <= x
-/
theorem prevFixed_le {x : α} (hx : f x ≤ x) : ↑(f.prevFixed x hx) ≤ x :=
  f.gfp_const_inf_le x
/-
**OrderHom.le_nextFixed** 是 Mathlib 中的一个定理，位于命名空间 `OrderHom`。
形式化陈述：le_nextFixed {x : α} (hx : x <= f x) : x <= f.nextFixed x hx
参数：hx : x <= f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderHom.prevFixed_le`：prevFixed_le {x : α} (hx : f x <= x) : ↑(f.prevFi
xed x hx) <= x
-/
theorem le_nextFixed {x : α} (hx : x ≤ f x) : x ≤ f.nextFixed x hx :=
  f.dual.prevFixed_le hx
/-
**OrderHom.nextFixed_le** 是 Mathlib 中的一个定理，位于命名空间 `OrderHom`。
形式化陈述：nextFixed_le {x : α} (hx : x <= f x) {y : fixedPoints f} (h : x <= y) : f.
nextFixed x hx <= y
参数：hx : x <= f x；h : x <= y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subtype.coe_le_coe`：coe_le_coe [LE α] {p : α -> Prop} {x y : Subtype p} 
: (x : α) <= y ↔ x <= y
· 使用定理 `OrderHom.lfp_le`：lfp_le {a : α} (h : f a <= a) : f.lfp <= a
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem nextFixed_le {x : α} (hx : x ≤ f x) {y : fixedPoints f} (h : x ≤ y) :
    f.nextFixed x hx ≤ y :=
  Subtype.coe_le_coe.1 <| lfp_le _ <| sup_le h y.2.le

@[simp]
/-
**OrderHom.nextFixed_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `OrderHom`。
形式化陈述：nextFixed_le_iff {x : α} (hx : x <= f x) {y : fixedPoints f} : f.nextFixed
 x hx <= y ↔ x <= y
参数：hx : x <= f x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `OrderHom.le_nextFixed`：le_nextFixed {x : α} (hx : x <= f x) : x <= f.nex
tFixed x hx
· 使用定理 `OrderHom.nextFixed_le`：nextFixed_le {x : α} (hx : x <= f x) {y : fixedPo
ints f} (h : x <= y) : f.nextFixed x hx <= y
-/
theorem nextFixed_le_iff {x : α} (hx : x ≤ f x) {y : fixedPoints f} :
    f.nextFixed x hx ≤ y ↔ x ≤ y :=
  ⟨fun h => (f.le_nextFixed hx).trans h, f.nextFixed_le hx⟩

@[simp]
/-
**OrderHom.le_prevFixed_iff** 是 Mathlib 中的一个定理，位于命名空间 `OrderHom`。
形式化陈述：le_prevFixed_iff {x : α} (hx : f x <= x) {y : fixedPoints f} : y <= f.prev
Fixed x hx ↔ ↑y <= x
参数：hx : f x <= x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderHom.nextFixed_le_iff`：nextFixed_le_iff {x : α} (hx : x <= f x) {y :
 fixedPoints f} : f.nextFixed x hx <= y ↔ x <= y
-/
theorem le_prevFixed_iff {x : α} (hx : f x ≤ x) {y : fixedPoints f} :
    y ≤ f.prevFixed x hx ↔ ↑y ≤ x :=
  f.dual.nextFixed_le_iff hx
/-
**OrderHom.le_prevFixed** 是 Mathlib 中的一个定理，位于命名空间 `OrderHom`。
形式化陈述：le_prevFixed {x : α} (hx : f x <= x) {y : fixedPoints f} (h : ↑y <= x) : y
 <= f.prevFixed x hx
参数：hx : f x <= x；h : ↑y <= x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `OrderHom.le_prevFixed_iff`：le_prevFixed_iff {x : α} (hx : f x <= x) {y :
 fixedPoints f} : y <= f.prevFixed x hx ↔ ↑y <= x
-/
theorem le_prevFixed {x : α} (hx : f x ≤ x) {y : fixedPoints f} (h : ↑y ≤ x) :
    y ≤ f.prevFixed x hx :=
  (f.le_prevFixed_iff hx).2 h
/-
**OrderHom.le_map_sup_fixedPoints** 是 Mathlib 中的一个定理，位于命名空间 `OrderHom`。
形式化陈述：le_map_sup_fixedPoints (x y : fixedPoints f) : (x ⊔ y : α) <= f (x ⊔ y)
参数：x y : fixedPoints f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Monotone.le_map_sup`：le_map_sup [SemilatticeSup α] [SemilatticeSup β] {f
 : α -> β} (h : Monotone f) (x y : α) : f x ⊔ f y <= f (x ⊔ y)
· 使用定理 `OrderHom.mono`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [inst
_1 : Preorder β] (f : α →o β), Monotone ⇑f
-/
theorem le_map_sup_fixedPoints (x y : fixedPoints f) : (x ⊔ y : α) ≤ f (x ⊔ y) :=
  calc
    (x ⊔ y : α) = f x ⊔ f y := congr_arg₂ (· ⊔ ·) x.2.symm y.2.symm
    _ ≤ f (x ⊔ y) := f.mono.le_map_sup x y

-- Porting note: `x ⊓ y` without the `.val`s fails to synthesize `Inf` instance
/-
**OrderHom.map_inf_fixedPoints_le** 是 Mathlib 中的一个定理，位于命名空间 `OrderHom`。
形式化陈述：map_inf_fixedPoints_le (x y : fixedPoints f) : f (x ⊓ y) <= x.val ⊓ y.val
参数：x y : fixedPoints f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderHom.le_map_sup_fixedPoints`：le_map_sup_fixedPoints (x y : fixedPoin
ts f) : (x ⊔ y : α) <= f (x ⊔ y)
-/
theorem map_inf_fixedPoints_le (x y : fixedPoints f) : f (x ⊓ y) ≤ x.val ⊓ y.val :=
  f.dual.le_map_sup_fixedPoints x y
/-
**OrderHom.le_map_sSup_subset_fixedPoints** 是 Mathlib 中的一个定理，位于命名空间 `OrderHom`。
形式化陈述：le_map_sSup_subset_fixedPoints (A : Set α) (hA : A subseteq fixedPoints f)
 : sSup A <= f (sSup A)
参数：A : Set α；hA : A subseteq fixedPoints f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sSup_le`：sSup_le (h : forall b in s, b <= a) : sSup s <= a
· 使用定理 `OrderHom.mono`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [inst
_1 : Preorder β] (f : α →o β), Monotone ⇑f
· 使用定理 `le_sSup`：le_sSup (h : a in s) : a <= sSup s
-/
theorem le_map_sSup_subset_fixedPoints (A : Set α) (hA : A ⊆ fixedPoints f) :
    sSup A ≤ f (sSup A) :=
  sSup_le fun _ hx => hA hx ▸ (f.mono <| le_sSup hx)
/-
**OrderHom.map_sInf_subset_fixedPoints_le** 是 Mathlib 中的一个定理，位于命名空间 `OrderHom`。
形式化陈述：map_sInf_subset_fixedPoints_le (A : Set α) (hA : A subseteq fixedPoints f)
 : f (sInf A) <= sInf A
参数：A : Set α；hA : A subseteq fixedPoints f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_sInf`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, (∀ b ∈ s, a ≤ b) → a ≤ sInf s
· 使用定理 `OrderHom.mono`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [inst
_1 : Preorder β] (f : α →o β), Monotone ⇑f
· 使用定理 `sInf_le`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, a ∈ s → sInf s ≤ a
-/
theorem map_sInf_subset_fixedPoints_le (A : Set α) (hA : A ⊆ fixedPoints f) :
    f (sInf A) ≤ sInf A :=
  le_sInf fun _ hx => hA hx ▸ (f.mono <| sInf_le hx)

end PrevNext

end OrderHom

namespace fixedPoints

open OrderHom

variable [CompleteLattice α] (f : α →o α)

/-
**fixedPoints.** 是 Mathlib 中的一个实例，位于命名空间 `fixedPoints`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : BoundedOrder (fixedPoints f) where
  top := ⟨f.gfp, f.isFixedPt_gfp⟩
  bot := ⟨f.lfp, f.isFixedPt_lfp⟩
  le_top x := f.le_gfp x.2.ge
  bot_le x := f.lfp_le x.2.le
/-
**fixedPoints.** 是 Mathlib 中的一个实例，位于命名空间 `fixedPoints`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SemilatticeSup (fixedPoints f) where
  sup x y := f.nextFixed (x ⊔ y) (f.le_map_sup_fixedPoints x y)
  le_sup_left _ _ := Subtype.coe_le_coe.1 <| le_sup_left.trans (f.le_nextFixed _)
  le_sup_right _ _ := Subtype.coe_le_coe.1 <| le_sup_right.trans (f.le_nextFixed _)
  sup_le _ _ _ hxz hyz := f.nextFixed_le _ <| sup_le hxz hyz
/-
**fixedPoints.** 是 Mathlib 中的一个实例，位于命名空间 `fixedPoints`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SemilatticeInf (fixedPoints f) where
  __ : PartialOrder (fixedPoints f) := inferInstance
  inf x y := f.prevFixed (x ⊓ y) (f.map_inf_fixedPoints_le x y)
  __ := OrderDual.instSemilatticeInf (fixedPoints f.dual)

/-- **Knaster-Tarski Theorem**: The fixed points of `f` form a complete lattice. -/
/-
**fixedPoints.completeLattice** 是 Mathlib 中的一个实例，位于命名空间 `fixedPoints`。
形式化陈述：completeLattice : CompleteLattice (fixedPoints f) where sSup s
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
**Knaster-Tarski Theorem**: The fixed points of `f` form a complete lattice.
-/
instance completeLattice : CompleteLattice (fixedPoints f) where
  sSup s :=
    f.nextFixed (sSup (Subtype.val '' s))
      (f.le_map_sSup_subset_fixedPoints (Subtype.val '' s)
        fun _ ⟨x, hx⟩ => hx.2 ▸ x.2)
  isLUB_sSup _ :=
    ⟨fun _ hx ↦ (le_sSup <| Set.mem_image_of_mem _ hx).trans (f.le_nextFixed _),
      fun _ hx ↦ f.nextFixed_le _ <| sSup_le <| Set.forall_mem_image.2 hx⟩
  sInf s :=
    f.prevFixed (sInf (Subtype.val '' s))
      (f.map_sInf_subset_fixedPoints_le (Subtype.val '' s) fun _ ⟨x, hx⟩ => hx.2 ▸ x.2)
  isGLB_sInf _ :=
    ⟨fun _ hx ↦ (f.prevFixed_le _).trans (sInf_le <| Set.mem_image_of_mem _ hx),
      fun _ hx ↦ f.le_prevFixed _ <| le_sInf <| Set.forall_mem_image.2 hx⟩

open OmegaCompletePartialOrder fixedPoints

/-- **Kleene's fixed point Theorem**: The least fixed point in a complete lattice is
the supremum of iterating a function on bottom arbitrary often. -/
/-
**fixedPoints.lfp_eq_sSup_iterate** 是 Mathlib 中的一个定理，位于命名空间 `fixedPoints`。
形式化陈述：lfp_eq_sSup_iterate (h : ωScottContinuous f) : f.lfp = ⨆ n, f^[n] ⊥
参数：h : ωScottContinuous f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `OrderHom.lfp_le_fixed`：lfp_le_fixed {a : α} (h : f a = a) : f.lfp <= a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Function.mem_fixedPoints`：mem_fixedPoints : x in fixedPoints f ↔ IsFixed
Pt f x
· 使用定理 `OmegaCompletePartialOrder.fixedPoints.ωSup_iterate_mem_fixedPoint`：ωSup_
iterate_mem_fixedPoint (h : x <= f x) : ωSup (iterateChain f x h) in fixedPoints
 f
· 使用定理 `OmegaCompletePartialOrder.ωScottContinuous.map_ωSup_of_orderHom`：∀ {α : 
Type u_2} {β : Type u_3} [inst : OmegaCompletePartialOrder α] [inst_1 : OmegaCom
pletePartialOrder β]   {f : α →o β},   OmegaCompleteP…
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `OrderHom.le_lfp`：le_lfp {a : α} (h : forall b, f b <= b -> a <= b) : a <
= f.lfp
· 使用定理 `OmegaCompletePartialOrder.fixedPoints.ωSup_iterate_le_prefixedPoint`：ωSu
p_iterate_le_prefixedPoint (h : x <= f x) {a : α} (h_a : f a <= a) (h_x_le_a : x
 <= a) : ωSup (iterateChain f x h) <= a

--- 原说明 ---
**Kleene's fixed point Theorem**: The least fixed point in a complete lattice is
the supremum of iterating a function on bottom arbitrary often.
-/
theorem lfp_eq_sSup_iterate (h : ωScottContinuous f) :
    f.lfp = ⨆ n, f^[n] ⊥ := by
  apply le_antisymm
  · apply lfp_le_fixed
    exact Function.mem_fixedPoints.mp (ωSup_iterate_mem_fixedPoint
      ⟨f, h.map_ωSup_of_orderHom⟩ ⊥ bot_le)
  · apply le_lfp
    intro a h_a
    exact ωSup_iterate_le_prefixedPoint ⟨f, h.map_ωSup_of_orderHom⟩ ⊥ bot_le h_a bot_le
/-
**fixedPoints.gfp_eq_sInf_iterate** 是 Mathlib 中的一个定理，位于命名空间 `fixedPoints`。
形式化陈述：gfp_eq_sInf_iterate (h : ωScottContinuous f.dual) : f.gfp = ⨅ n, f^[n] ⊤
参数：h : ωScottContinuous f.dual。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `fixedPoints.lfp_eq_sSup_iterate`：lfp_eq_sSup_iterate (h : ωScottContinuo
us f) : f.lfp = ⨆ n, f^[n] ⊥
-/
theorem gfp_eq_sInf_iterate (h : ωScottContinuous f.dual) :
    f.gfp = ⨅ n, f^[n] ⊤ :=
  lfp_eq_sSup_iterate f.dual h

end fixedPoints

