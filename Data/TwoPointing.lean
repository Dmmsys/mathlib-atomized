/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Logic.Nontrivial.Defs
public import Mathlib.Logic.Nonempty
public import Mathlib.Tactic.Simps.Basic
public import Batteries.Logic

/-!
# Two-pointings

This file defines `TwoPointing α`, the type of two pointings of `α`. A two-pointing is the data of
two distinct terms.

This is morally a Type-valued `Nontrivial`. Another type which is quite close in essence is `Sym2`.
Categorically speaking, `prod` is a cospan in the category of types. This forms the category of
bipointed types. Two-pointed types form a full subcategory of those.

## References

* [nLab, *Coalgebra of the real interval*]
  (https://ncatlab.org/nlab/show/coalgebra+of+the+real+interval)
-/

@[expose] public section

open Function

variable {α β : Type*}

/-- Two-pointing of a type. This is a Type-valued termed `Nontrivial`. -/
@[ext]
/-
**TwoPointing** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u_3 → Type u_3
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Two-pointing of a type. This is a Type-valued termed `Nontrivial`.
-/
structure TwoPointing (α : Type*) extends α × α where
  /-- `fst` and `snd` are distinct terms -/
  fst_ne_snd : fst ≠ snd
  deriving DecidableEq

initialize_simps_projections TwoPointing (+toProd, -fst, -snd)

namespace TwoPointing

variable (p : TwoPointing α) (q : TwoPointing β)

/-
**TwoPointing.snd_ne_fst** 是 Mathlib 中的一个定理，位于命名空间 `TwoPointing`。
形式化陈述：snd_ne_fst : p.snd != p.fst
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `TwoPointing.fst_ne_snd`：∀ {α : Type u_3} (self : TwoPointing α), self.to
Prod.1 ≠ self.toProd.2
-/
theorem snd_ne_fst : p.snd ≠ p.fst :=
  p.fst_ne_snd.symm

/-- Swaps the two pointed elements. -/
@[simps]
/-
**TwoPointing.swap** 是 Mathlib 中的一个定义，位于命名空间 `TwoPointing`。
形式化陈述：swap : TwoPointing α
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `TwoPointing.snd_ne_fst`：snd_ne_fst : p.snd != p.fst

--- 原说明 ---
Swaps the two pointed elements.
-/
def swap : TwoPointing α :=
  ⟨(p.snd, p.fst), p.snd_ne_fst⟩
/-
**TwoPointing.swap_fst** 是 Mathlib 中的一个定理，位于命名空间 `TwoPointing`。
形式化陈述：swap_fst : p.swap.fst = p.snd
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem swap_fst : p.swap.fst = p.snd := rfl
/-
**TwoPointing.swap_snd** 是 Mathlib 中的一个定理，位于命名空间 `TwoPointing`。
形式化陈述：swap_snd : p.swap.snd = p.fst
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem swap_snd : p.swap.snd = p.fst := rfl

@[simp]
/-
**TwoPointing.swap_swap** 是 Mathlib 中的一个定理，位于命名空间 `TwoPointing`。
形式化陈述：swap_swap : p.swap.swap = p
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem swap_swap : p.swap.swap = p := rfl

include p in
/-
**TwoPointing.to_nontrivial** 是 Mathlib 中的一个定理，位于命名空间 `TwoPointing`。
形式化陈述：to_nontrivial : Nontrivial α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TwoPointing.fst_ne_snd`：∀ {α : Type u_3} (self : TwoPointing α), self.to
Prod.1 ≠ self.toProd.2
-/
theorem to_nontrivial : Nontrivial α :=
  ⟨⟨p.fst, p.snd, p.fst_ne_snd⟩⟩
/-
**TwoPointing.** 是 Mathlib 中的一个实例，位于命名空间 `TwoPointing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Nontrivial α] : Nonempty (TwoPointing α) :=
  let ⟨a, b, h⟩ := exists_pair_ne α
  ⟨⟨(a, b), h⟩⟩

@[simp]
/-
**TwoPointing.nonempty_two_pointing_iff** 是 Mathlib 中的一个定理，位于命名空间 `TwoPointing`。
形式化陈述：nonempty_two_pointing_iff : Nonempty (TwoPointing α) ↔ Nontrivial α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TwoPointing.to_nontrivial`：to_nontrivial : Nontrivial α
· 使用定理 `TwoPointing.instNonemptyOfNontrivial`：∀ {α : Type u_1} [Nontrivial α], N
onempty (TwoPointing α)
-/
theorem nonempty_two_pointing_iff : Nonempty (TwoPointing α) ↔ Nontrivial α :=
  ⟨fun ⟨p⟩ ↦ p.to_nontrivial, fun _ => inferInstance⟩

section Pi

variable (α) [Nonempty α]

/-- The two-pointing of constant functions. -/
/-
**TwoPointing.pi** 是 Mathlib 中的一个定义，位于命名空间 `TwoPointing`。
形式化陈述：pi : TwoPointing (α -> β) where fst _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The two-pointing of constant functions.
-/
def pi : TwoPointing (α → β) where
  fst _ := q.fst
  snd _ := q.snd
  fst_ne_snd h := q.fst_ne_snd (congr_fun h (Classical.arbitrary α))

@[simp]
/-
**TwoPointing.pi_fst** 是 Mathlib 中的一个定理，位于命名空间 `TwoPointing`。
形式化陈述：pi_fst : (q.pi α).fst = const α q.fst
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pi_fst : (q.pi α).fst = const α q.fst :=
  rfl

@[simp]
/-
**TwoPointing.pi_snd** 是 Mathlib 中的一个定理，位于命名空间 `TwoPointing`。
形式化陈述：pi_snd : (q.pi α).snd = const α q.snd
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pi_snd : (q.pi α).snd = const α q.snd :=
  rfl

end Pi

/-- The product of two two-pointings. -/
/-
**TwoPointing.prod** 是 Mathlib 中的一个定义，位于命名空间 `TwoPointing`。
形式化陈述：prod : TwoPointing (α × β) where fst
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The product of two two-pointings.
-/
def prod : TwoPointing (α × β) where
  fst := (p.fst, q.fst)
  snd := (p.snd, q.snd)
  fst_ne_snd h := p.fst_ne_snd (congr_arg Prod.fst h)

@[simp]
/-
**TwoPointing.prod_fst** 是 Mathlib 中的一个定理，位于命名空间 `TwoPointing`。
形式化陈述：prod_fst : (p.prod q).fst = (p.fst, q.fst)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prod_fst : (p.prod q).fst = (p.fst, q.fst) :=
  rfl

@[simp]
/-
**TwoPointing.prod_snd** 是 Mathlib 中的一个定理，位于命名空间 `TwoPointing`。
形式化陈述：prod_snd : (p.prod q).snd = (p.snd, q.snd)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prod_snd : (p.prod q).snd = (p.snd, q.snd) :=
  rfl

/-- The sum of two pointings. Keeps the first point from the left and the second point from the
right. -/
/-
**TwoPointing.sum** 是 Mathlib 中的一个定义，位于命名空间 `TwoPointing`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → TwoPointing α → TwoPointing β → TwoPoint
ing (α ⊕ β)
参数：α ⊕ β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The sum of two pointings. Keeps the first point from the left and the second poi
nt from the
right.
-/
protected def sum : TwoPointing (α ⊕ β) :=
  ⟨(Sum.inl p.fst, Sum.inr q.snd), Sum.inl_ne_inr⟩

@[simp]
/-
**TwoPointing.sum_fst** 是 Mathlib 中的一个定理，位于命名空间 `TwoPointing`。
形式化陈述：sum_fst : (p.sum q).fst = Sum.inl p.fst
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sum_fst : (p.sum q).fst = Sum.inl p.fst :=
  rfl

@[simp]
/-
**TwoPointing.sum_snd** 是 Mathlib 中的一个定理，位于命名空间 `TwoPointing`。
形式化陈述：sum_snd : (p.sum q).snd = Sum.inr q.snd
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sum_snd : (p.sum q).snd = Sum.inr q.snd :=
  rfl

/-- The `false`, `true` two-pointing of `Bool`. -/
/-
**TwoPointing.bool** 是 Mathlib 中的一个定义，位于命名空间 `TwoPointing`。
形式化陈述：TwoPointing Bool
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Bool.false_ne_true`：false ≠ true

--- 原说明 ---
The `false`, `true` two-pointing of `Bool`.
-/
protected def bool : TwoPointing Bool :=
  ⟨(false, true), Bool.false_ne_true⟩

@[simp]
/-
**TwoPointing.bool_fst** 是 Mathlib 中的一个定理，位于命名空间 `TwoPointing`。
形式化陈述：bool_fst : TwoPointing.bool.fst = false
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bool_fst : TwoPointing.bool.fst = false := rfl

@[simp]
/-
**TwoPointing.bool_snd** 是 Mathlib 中的一个定理，位于命名空间 `TwoPointing`。
形式化陈述：bool_snd : TwoPointing.bool.snd = true
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bool_snd : TwoPointing.bool.snd = true := rfl
/-
**TwoPointing.** 是 Mathlib 中的一个实例，位于命名空间 `TwoPointing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (TwoPointing Bool) :=
  ⟨TwoPointing.bool⟩

/-- The `False`, `True` two-pointing of `Prop`. -/
/-
**TwoPointing.prop** 是 Mathlib 中的一个定义，位于命名空间 `TwoPointing`。
形式化陈述：TwoPointing Prop
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `false_ne_true`：False ≠ True

--- 原说明 ---
The `False`, `True` two-pointing of `Prop`.
-/
protected def prop : TwoPointing Prop :=
  ⟨(False, True), false_ne_true⟩

@[simp]
/-
**TwoPointing.prop_fst** 是 Mathlib 中的一个定理，位于命名空间 `TwoPointing`。
形式化陈述：prop_fst : TwoPointing.prop.fst = False
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prop_fst : TwoPointing.prop.fst = False :=
  rfl

@[simp]
/-
**TwoPointing.prop_snd** 是 Mathlib 中的一个定理，位于命名空间 `TwoPointing`。
形式化陈述：prop_snd : TwoPointing.prop.snd = True
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prop_snd : TwoPointing.prop.snd = True :=
  rfl

end TwoPointing

