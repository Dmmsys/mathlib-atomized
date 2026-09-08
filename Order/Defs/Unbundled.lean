/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

public import Mathlib.Data.Set.Defs
public import Batteries.Tactic.Alias
public import Mathlib.Tactic.ExtendDoc

import Mathlib.Tactic.ToDual

/-!
# Orders

Defines classes for preorders, partial orders, and linear orders
and proves some basic lemmas about them.
-/

@[expose] public section

/-! ### Unbundled classes -/

/-- `IsIrrefl X r` means the binary relation `r` on `X` is irreflexive (that is, `r x x` never
holds). -/
@[deprecated Std.Irrefl (since := "2026-01-07")]
/-
**IsIrrefl** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：IsIrrefl (α : Sort*) (r : α -> α -> Prop) : Prop
参数：α : Sort*；r : α -> α -> Prop。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`IsIrrefl X r` means the binary relation `r` on `X` is irreflexive (that is, `r 
x x` never
holds).
-/
abbrev IsIrrefl (α : Sort*) (r : α → α → Prop) : Prop := Std.Irrefl r

/-- `IsRefl X r` means the binary relation `r` on `X` is reflexive. -/
@[deprecated Std.Refl (since := "2026-01-08")]
/-
**IsRefl** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：IsRefl (α : Sort*) (r : α -> α -> Prop) : Prop
参数：α : Sort*；r : α -> α -> Prop。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`IsRefl X r` means the binary relation `r` on `X` is reflexive.
-/
abbrev IsRefl (α : Sort*) (r : α → α → Prop) : Prop := Std.Refl r

/-- `IsAsymm X r` means that the binary relation `r` on `X` is asymmetric, that is,
`r a b → ¬ r b a`. -/
@[deprecated Std.Asymm (since := "2026-01-03")]
/-
**IsAsymm** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：IsAsymm (α : Sort*) (r : α -> α -> Prop) : Prop
参数：α : Sort*；r : α -> α -> Prop。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`IsAsymm X r` means that the binary relation `r` on `X` is asymmetric, that is,
`r a b → ¬ r b a`.
-/
abbrev IsAsymm (α : Sort*) (r : α → α → Prop) : Prop := Std.Asymm r

/-- `IsAntisymm X r` means the binary relation `r` on `X` is antisymmetric. -/
@[deprecated Std.Antisymm (since := "2026-01-06")]
/-
**IsAntisymm** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：IsAntisymm (α : Sort*) (r : α -> α -> Prop) : Prop
参数：α : Sort*；r : α -> α -> Prop。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`IsAntisymm X r` means the binary relation `r` on `X` is antisymmetric.
-/
abbrev IsAntisymm (α : Sort*) (r : α → α → Prop) : Prop := Std.Antisymm r

/-- `IsTrans X r` means the binary relation `r` on `X` is transitive. -/
/-
**IsTrans** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Sort u_1) → (α → α → Prop) → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`IsTrans X r` means the binary relation `r` on `X` is transitive.
-/
class IsTrans (α : Sort*) (r : α → α → Prop) : Prop where
  trans : ∀ a b c, r a b → r b c → r a c
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {α : Sort*} {r : α → α → Prop} [IsTrans α r] : Trans r r r :=
  ⟨IsTrans.trans _ _ _⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) {α : Sort*} {r : α → α → Prop} [Trans r r r] : IsTrans α r :=
  ⟨fun _ _ _ => Trans.trans⟩

/-- `IsTotal X r` means that the binary relation `r` on `X` is total, that is, that for any
`x y : X` we have `r x y` or `r y x`. -/
@[deprecated Std.Total (since := "2026-01-09")]
/-
**IsTotal** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：IsTotal (α : Sort*) (r : α -> α -> Prop) : Prop
参数：α : Sort*；r : α -> α -> Prop。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`IsTotal X r` means that the binary relation `r` on `X` is total, that is, that 
for any
`x y : X` we have `r x y` or `r y x`.
-/
abbrev IsTotal (α : Sort*) (r : α → α → Prop) : Prop := Std.Total r

/-- `IsPreorder X r` means that the binary relation `r` on `X` is a pre-order, that is, reflexive
and transitive. -/
/-
**IsPreorder** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Sort u_1) → (α → α → Prop) → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`IsPreorder X r` means that the binary relation `r` on `X` is a pre-order, that 
is, reflexive
and transitive.
-/
class IsPreorder (α : Sort*) (r : α → α → Prop) : Prop extends Std.Refl r, IsTrans α r

/-- `IsPartialOrder X r` means that the binary relation `r` on `X` is a partial order, that is,
`IsPreorder X r` and `Std.Antisymm r`. -/
/-
**IsPartialOrder** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Sort u_1) → (α → α → Prop) → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`IsPartialOrder X r` means that the binary relation `r` on `X` is a partial orde
r, that is,
`IsPreorder X r` and `Std.Antisymm r`.
-/
class IsPartialOrder (α : Sort*) (r : α → α → Prop) : Prop extends IsPreorder α r, Std.Antisymm r

/-- `IsLinearOrder X r` means that the binary relation `r` on `X` is a linear order, that is,
`IsPartialOrder X r` and `Std.Total r`. -/
/-
**IsLinearOrder** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Sort u_1) → (α → α → Prop) → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`IsLinearOrder X r` means that the binary relation `r` on `X` is a linear order,
 that is,
`IsPartialOrder X r` and `Std.Total r`.
-/
class IsLinearOrder (α : Sort*) (r : α → α → Prop) : Prop extends IsPartialOrder α r, Std.Total r

/-- `IsEquiv X r` means that the binary relation `r` on `X` is an equivalence relation, that
is, `IsPreorder X r` and `Std.Symm r`. -/
/-
**IsEquiv** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Sort u_1) → (α → α → Prop) → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`IsEquiv X r` means that the binary relation `r` on `X` is an equivalence relati
on, that
is, `IsPreorder X r` and `Std.Symm r`.
-/
class IsEquiv (α : Sort*) (r : α → α → Prop) : Prop extends IsPreorder α r, Std.Symm r

/-- `IsStrictOrder X r` means that the binary relation `r` on `X` is a strict order, that is,
`Std.Irrefl r` and `IsTrans X r`. -/
/-
**IsStrictOrder** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Sort u_1) → (α → α → Prop) → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`IsStrictOrder X r` means that the binary relation `r` on `X` is a strict order,
 that is,
`Std.Irrefl r` and `IsTrans X r`.
-/
class IsStrictOrder (α : Sort*) (r : α → α → Prop) : Prop extends Std.Irrefl r, IsTrans α r

/-- `IsStrictWeakOrder X lt` means that the binary relation `lt` on `X` is a strict weak order,
that is, `IsStrictOrder X lt` and `¬lt a b ∧ ¬lt b a → ¬lt b c ∧ ¬lt c b → ¬lt a c ∧ ¬lt c a`. -/
/-
**IsStrictWeakOrder** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Sort u_1) → (α → α → Prop) → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`IsStrictWeakOrder X lt` means that the binary relation `lt` on `X` is a strict 
weak order,
that is, `IsStrictOrder X lt` and `¬lt a b ∧ ¬lt b a → ¬lt b c ∧ ¬lt c b → ¬lt a
 c ∧ ¬lt c a`.
-/
class IsStrictWeakOrder (α : Sort*) (lt : α → α → Prop) : Prop extends IsStrictOrder α lt where
  incomp_trans : ∀ a b c, ¬lt a b ∧ ¬lt b a → ¬lt b c ∧ ¬lt c b → ¬lt a c ∧ ¬lt c a

/-- `IsTrichotomous X lt` means that the binary relation `lt` on `X` is trichotomous, that is,
either `lt a b` or `a = b` or `lt b a` for any `a` and `b`. -/
@[deprecated Std.Trichotomous (since := "2026-01-24")]
/-
**IsTrichotomous** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：IsTrichotomous (α : Sort*) (lt : α -> α -> Prop) : Prop
参数：α : Sort*；lt : α -> α -> Prop。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`IsTrichotomous X lt` means that the binary relation `lt` on `X` is trichotomous
, that is,
either `lt a b` or `a = b` or `lt b a` for any `a` and `b`.
-/
abbrev IsTrichotomous (α : Sort*) (lt : α → α → Prop) : Prop := Std.Trichotomous lt

/-- `IsStrictTotalOrder X lt` means that the binary relation `lt` on `X` is a strict total order,
that is, `Std.Trichotomous lt` and `IsStrictOrder X lt`. -/
/-
**IsStrictTotalOrder** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Sort u_1) → (α → α → Prop) → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`IsStrictTotalOrder X lt` means that the binary relation `lt` on `X` is a strict
 total order,
that is, `Std.Trichotomous lt` and `IsStrictOrder X lt`.
-/
class IsStrictTotalOrder (α : Sort*) (lt : α → α → Prop) : Prop
    extends Std.Trichotomous lt, IsStrictOrder α lt
/-
**Equivalence.of_isEquiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Equivalence.of_isEquiv {α : Sort*} (lt : α -> α -> Prop) [IsEquiv α lt] : 
Equivalence lt where refl
参数：lt : α -> α -> Prop。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Std.Refl.refl`：∀ {α : Sort u} {r : α → α → Prop} [self : Std.Refl r] (a 
: α), r a a
· 使用定理 `IsPreorder.toRefl`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsPreorde
r α r], Std.Refl r
· 使用定理 `IsEquiv.toIsPreorder`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsEqui
v α r], IsPreorder α r
· 使用定理 `Std.Symm.symm`：∀ {α : Sort u} {r : α → α → Prop} [self : Std.Symm r] (a 
b : α), r a b → r b a
· 使用定理 `IsEquiv.toSymm`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsEquiv α r]
, Std.Symm r
· 使用定理 `IsTrans.trans`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsTrans α r] 
(a b c : α), r a b → r b c → r a c
· 使用定理 `IsPreorder.toIsTrans`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsPreo
rder α r], IsTrans α r
-/
theorem Equivalence.of_isEquiv {α : Sort*} (lt : α → α → Prop) [IsEquiv α lt] : Equivalence lt where
  refl := Std.Refl.refl; symm := Std.Symm.symm _ _; trans := IsTrans.trans _ _ _
/-
**IsEquiv.of_equivalence** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsEquiv.of_equivalence {α : Sort*} {lt : α -> α -> Prop} (h : Equivalence 
lt) : IsEquiv α lt where refl
参数：h : Equivalence lt。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equivalence.refl`：∀ {α : Sort u} {r : α → α → Prop}, Equivalence r → ∀ (
x : α), r x x
· 使用定理 `Equivalence.trans`：∀ {α : Sort u} {r : α → α → Prop}, Equivalence r → ∀ 
{x y z : α}, r x y → r y z → r x z
· 使用定理 `Equivalence.symm`：∀ {α : Sort u} {r : α → α → Prop}, Equivalence r → ∀ {
x y : α}, r x y → r y x
-/
theorem IsEquiv.of_equivalence {α : Sort*} {lt : α → α → Prop} (h : Equivalence lt) :
    IsEquiv α lt where
  refl := h.refl; symm _ _ := h.symm; trans _ _ _ := h.trans
/-
**equivalence_iff_isEquiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：equivalence_iff_isEquiv {α : Sort*} (lt : α -> α -> Prop) : Equivalence lt
 ↔ IsEquiv α lt
参数：lt : α -> α -> Prop。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsEquiv.of_equivalence`：IsEquiv.of_equivalence {α : Sort*} {lt : α -> α 
-> Prop} (h : Equivalence lt) : IsEquiv α lt where refl
· 使用定理 `Equivalence.of_isEquiv`：Equivalence.of_isEquiv {α : Sort*} (lt : α -> α 
-> Prop) [IsEquiv α lt] : Equivalence lt where refl
-/
theorem equivalence_iff_isEquiv {α : Sort*} (lt : α → α → Prop) : Equivalence lt ↔ IsEquiv α lt :=
  ⟨.of_equivalence, fun _ => .of_isEquiv lt⟩

/-- Equality is an equivalence relation. -/
/-
**eq_isEquiv** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：eq_isEquiv (α : Sort*) : IsEquiv α (· = ·) where symm
参数：α : Sort*。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
Equality is an equivalence relation.
-/
instance eq_isEquiv (α : Sort*) : IsEquiv α (· = ·) where
  symm := @Eq.symm _
  trans := @Eq.trans _
  refl := Eq.refl
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (α : Sort*) : Std.Symm (α := α) Ne where
  symm _ _ := Ne.symm

/-- `Iff` is an equivalence relation. -/
/-
**iff_isEquiv** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：iff_isEquiv : IsEquiv Prop Iff where symm
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.refl`：∀ (a : Prop), a ↔ a
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)

--- 原说明 ---
`Iff` is an equivalence relation.
-/
instance iff_isEquiv : IsEquiv Prop Iff where
  symm := @Iff.symm
  trans := @Iff.trans
  refl := @Iff.refl

section

variable {α : Sort*} {r : α → α → Prop} {a b c : α}

/-- Local notation for an arbitrary binary relation `r`. -/
local infixl:50 " ≺ " => r

/-
**irrefl** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：irrefl [Std.Irrefl r] (a : α) : ¬a ≺ a
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Std.Irrefl.irrefl`：∀ {α : Sort u} {r : α → α → Prop} [self : Std.Irrefl 
r] (a : α), ¬r a a
-/
lemma irrefl [Std.Irrefl r] (a : α) : ¬a ≺ a := Std.Irrefl.irrefl a
/-
**refl** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：refl [Std.Refl r] (a : α) : a ≺ a
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Std.Refl.refl`：∀ {α : Sort u} {r : α → α → Prop} [self : Std.Refl r] (a 
: α), r a a
-/
lemma refl [Std.Refl r] (a : α) : a ≺ a := Std.Refl.refl a
/-
**trans** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：trans [IsTrans α r] : a ≺ b -> b ≺ c -> a ≺ c
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTrans.trans`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsTrans α r] 
(a b c : α), r a b → r b c → r a c
-/
lemma trans [IsTrans α r] : a ≺ b → b ≺ c → a ≺ c := IsTrans.trans _ _ _
/-
**symm** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：symm [Std.Symm r] : a ≺ b -> b ≺ a
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Std.Symm.symm`：∀ {α : Sort u} {r : α → α → Prop} [self : Std.Symm r] (a 
b : α), r a b → r b a
-/
lemma symm [Std.Symm r] : a ≺ b → b ≺ a := Std.Symm.symm _ _
/-
**antisymm** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：antisymm [Std.Antisymm r] : a ≺ b -> b ≺ a -> a = b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Std.Antisymm.antisymm`：∀ {α : Sort u} {r : α → α → Prop} [self : Std.Ant
isymm r] (a b : α), r a b → r b a → a = b
-/
lemma antisymm [Std.Antisymm r] : a ≺ b → b ≺ a → a = b := Std.Antisymm.antisymm _ _
/-
**asymm** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：asymm [Std.Asymm r] : a ≺ b -> ¬b ≺ a
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Std.Asymm.asymm`：∀ {α : Sort u} {r : α → α → Prop} [self : Std.Asymm r] 
(a b : α), r a b → ¬r b a
-/
lemma asymm [Std.Asymm r] : a ≺ b → ¬b ≺ a := Std.Asymm.asymm _ _
/-
**trichotomous** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：trichotomous [Std.Trichotomous r] : forall a b : α, a ≺ b ∨ a = b ∨ b ≺ a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Std.Trichotomous.rel_or_eq_or_rel_swap`：∀ {α : Sort u_1} {r : α → α → Pr
op} [i : Std.Trichotomous r] {a b : α}, r a b ∨ a = b ∨ r b a
-/
lemma trichotomous [Std.Trichotomous r] : ∀ a b : α, a ≺ b ∨ a = b ∨ b ≺ a :=
  fun _ _ ↦ Std.Trichotomous.rel_or_eq_or_rel_swap
/-
**irrefl_def** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：irrefl_def : Std.Irrefl r ↔ forall ⦃a⦄, ¬r a a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Std.Irrefl.irrefl`：∀ {α : Sort u} {r : α → α → Prop} [self : Std.Irrefl 
r] (a : α), ¬r a a
-/
lemma irrefl_def : Std.Irrefl r ↔ ∀ ⦃a⦄, ¬r a a :=
  ⟨(·.irrefl), .mk⟩
/-
**refl_def** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：refl_def : Std.Refl r ↔ forall ⦃a⦄, r a a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Std.Refl.refl`：∀ {α : Sort u} {r : α → α → Prop} [self : Std.Refl r] (a 
: α), r a a
-/
lemma refl_def : Std.Refl r ↔ ∀ ⦃a⦄, r a a :=
  ⟨(·.refl), .mk⟩
/-
**isTrans_def** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isTrans_def {α : Sort*} {r : α -> α -> Prop} : IsTrans α r ↔ forall ⦃a b c
⦄, r a b -> r b c -> r a c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTrans.trans`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsTrans α r] 
(a b c : α), r a b → r b c → r a c
-/
lemma isTrans_def {α : Sort*} {r : α → α → Prop} : IsTrans α r ↔ ∀ ⦃a b c⦄, r a b → r b c → r a c :=
  ⟨(·.trans), .mk⟩
/-
**symm_def** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：symm_def : Std.Symm r ↔ forall ⦃a b⦄, r a b -> r b a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Std.Symm.symm`：∀ {α : Sort u} {r : α → α → Prop} [self : Std.Symm r] (a 
b : α), r a b → r b a
-/
lemma symm_def : Std.Symm r ↔ ∀ ⦃a b⦄, r a b → r b a :=
  ⟨(·.symm), .mk⟩
/-
**antisymm_def** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：antisymm_def : Std.Antisymm r ↔ forall ⦃a b⦄, r a b -> r b a -> a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Std.Antisymm.antisymm`：∀ {α : Sort u} {r : α → α → Prop} [self : Std.Ant
isymm r] (a b : α), r a b → r b a → a = b
-/
lemma antisymm_def : Std.Antisymm r ↔ ∀ ⦃a b⦄, r a b → r b a → a = b :=
  ⟨(·.antisymm), .mk⟩
/-
**asymm_def** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：asymm_def : Std.Asymm r ↔ forall ⦃a b⦄, r a b -> ¬r b a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Std.Asymm.asymm`：∀ {α : Sort u} {r : α → α → Prop} [self : Std.Asymm r] 
(a b : α), r a b → ¬r b a
-/
lemma asymm_def : Std.Asymm r ↔ ∀ ⦃a b⦄, r a b → ¬r b a :=
  ⟨(·.asymm), .mk⟩
/-
**total_def** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：total_def : Std.Total r ↔ forall ⦃a b⦄, r a b ∨ r b a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Std.Total.total`：∀ {α : Sort u} {r : α → α → Prop} [self : Std.Total r] 
(a b : α), r a b ∨ r b a
-/
lemma total_def : Std.Total r ↔ ∀ ⦃a b⦄, r a b ∨ r b a :=
  ⟨(·.total), .mk⟩
/-
**trichotomous_def** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：trichotomous_def : Std.Trichotomous r ↔ forall ⦃a b⦄, ¬r a b -> ¬r b a -> 
a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Std.Trichotomous.trichotomous`：∀ {α : Sort u} {r : α → α → Prop} [self :
 Std.Trichotomous r] (a b : α), ¬r a b → ¬r b a → a = b
-/
lemma trichotomous_def : Std.Trichotomous r ↔ ∀ ⦃a b⦄, ¬r a b → ¬r b a → a = b :=
  ⟨(·.trichotomous), .mk⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 90) asymm_of_isTrans_of_irrefl [IsTrans α r] [Std.Irrefl r] : Std.Asymm r :=
  ⟨fun a _b h₁ h₂ => absurd (_root_.trans h₁ h₂) (irrefl a)⟩
/-
**Std.Irrefl.decide** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Std.Irrefl.decide [DecidableRel r] [Std.Irrefl r] : Std.Irrefl (fun a b =>
 decide (r a b) = true) where irrefl
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `decide_eq_true_eq`：∀ {p : Prop} [inst : Decidable p], (decide p = true) 
= p
· 使用定理 `Std.Irrefl.irrefl`：∀ {α : Sort u} {r : α → α → Prop} [self : Std.Irrefl 
r] (a : α), ¬r a a
-/
instance Std.Irrefl.decide [DecidableRel r] [Std.Irrefl r] :
    Std.Irrefl (fun a b => decide (r a b) = true) where
  irrefl := fun a => by simpa using irrefl a
/-
**Std.Refl.decide** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Std.Refl.decide [DecidableRel r] [Std.Refl r] : Std.Refl (fun a b => decid
e (r a b) = true) where refl
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `decide_eq_true_eq`：∀ {p : Prop} [inst : Decidable p], (decide p = true) 
= p
· 使用定理 `Std.Refl.refl`：∀ {α : Sort u} {r : α → α → Prop} [self : Std.Refl r] (a 
: α), r a a
-/
instance Std.Refl.decide [DecidableRel r] [Std.Refl r] :
    Std.Refl (fun a b => decide (r a b) = true) where
  refl := fun a => by simpa using refl a
/-
**IsTrans.decide** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：IsTrans.decide [DecidableRel r] [IsTrans α r] : IsTrans α (fun a b => deci
de (r a b) = true) where trans
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `decide_eq_true_eq`：∀ {p : Prop} [inst : Decidable p], (decide p = true) 
= p
· 使用定理 `IsTrans.trans`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsTrans α r] 
(a b c : α), r a b → r b c → r a c
-/
instance IsTrans.decide [DecidableRel r] [IsTrans α r] :
    IsTrans α (fun a b => decide (r a b) = true) where
  trans := fun a b c => by simpa using trans a b c
/-
**Std.Symm.decide** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Std.Symm.decide [DecidableRel r] [Std.Symm r] : Std.Symm (fun a b => decid
e (r a b) = true) where symm
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `decide_eq_true_eq`：∀ {p : Prop} [inst : Decidable p], (decide p = true) 
= p
· 使用定理 `Std.Symm.symm`：∀ {α : Sort u} {r : α → α → Prop} [self : Std.Symm r] (a 
b : α), r a b → r b a
-/
instance Std.Symm.decide [DecidableRel r] [Std.Symm r] :
    Std.Symm (fun a b => decide (r a b) = true) where
  symm := fun a b => by simpa using symm a b
/-
**Std.Antisymm.decide** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Std.Antisymm.decide [DecidableRel r] [Std.Antisymm r] : Std.Antisymm (fun 
a b => decide (r a b) = true) where antisymm a b h₁ h₂
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Std.Antisymm.antisymm`：∀ {α : Sort u} {r : α → α → Prop} [self : Std.Ant
isymm r] (a b : α), r a b → r b a → a = b
· 使用定理 `decide_eq_true_eq`：∀ {p : Prop} [inst : Decidable p], (decide p = true) 
= p
-/
instance Std.Antisymm.decide [DecidableRel r] [Std.Antisymm r] :
    Std.Antisymm (fun a b => decide (r a b) = true) where
  antisymm a b h₁ h₂ := antisymm (r := r) _ _ (by simpa using h₁) (by simpa using h₂)
/-
**Std.Asymm.decide** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Std.Asymm.decide [DecidableRel r] [Std.Asymm r] : Std.Asymm (fun a b => de
cide (r a b) = true) where asymm
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `decide_eq_true_eq`：∀ {p : Prop} [inst : Decidable p], (decide p = true) 
= p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Std.Asymm.asymm`：∀ {α : Sort u} {r : α → α → Prop} [self : Std.Asymm r] 
(a b : α), r a b → ¬r b a
-/
instance Std.Asymm.decide [DecidableRel r] [Std.Asymm r] :
    Std.Asymm (fun a b => decide (r a b) = true) where
  asymm := fun a b => by simpa using asymm a b
/-
**Std.Total.decide** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Std.Total.decide [DecidableRel r] [Std.Total r] : Std.Total (fun a b => de
cide (r a b) = true) where total
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `decide_eq_true_eq`：∀ {p : Prop} [inst : Decidable p], (decide p = true) 
= p
· 使用定理 `Std.Total.total`：∀ {α : Sort u} {r : α → α → Prop} [self : Std.Total r] 
(a b : α), r a b ∨ r b a
-/
instance Std.Total.decide [DecidableRel r] [Std.Total r] :
    Std.Total (fun a b => decide (r a b) = true) where
  total := fun a b => by simpa using total a b
/-
**Std.Trichotomous.decide** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Std.Trichotomous.decide [DecidableRel r] [Std.Trichotomous r] : Std.Tricho
tomous (fun a b => decide (r a b) = true) where trichotomous a b
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `decide_eq_true_eq`：∀ {p : Prop} [inst : Decidable p], (decide p = true) 
= p
· 使用定理 `Std.Trichotomous.trichotomous`：∀ {α : Sort u} {r : α → α → Prop} [self :
 Std.Trichotomous r] (a b : α), ¬r a b → ¬r b a → a = b
-/
instance Std.Trichotomous.decide [DecidableRel r] [Std.Trichotomous r] :
    Std.Trichotomous (fun a b => decide (r a b) = true) where
  trichotomous a b := by simpa using trichotomous a b

variable (r)
/-
**irrefl_of** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Sort u_1} (r : α → α → Prop) [Std.Irrefl r] (a : α), ¬r a a
参数：r : α → α → Prop；a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `irrefl`：irrefl [Std.Irrefl r] (a : α) : ¬a ≺ a
-/
@[elab_without_expected_type] lemma irrefl_of [Std.Irrefl r] (a : α) : ¬a ≺ a := irrefl a
/-
**refl_of** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Sort u_1} (r : α → α → Prop) [Std.Refl r] (a : α), r a a
参数：r : α → α → Prop；a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `refl`：refl [Std.Refl r] (a : α) : a ≺ a
-/
@[elab_without_expected_type] lemma refl_of [Std.Refl r] (a : α) : a ≺ a := refl a
/-
**trans_of** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Sort u_1} (r : α → α → Prop) {a b c : α} [IsTrans α r], r a b → r b
 c → r a c
参数：r : α → α → Prop。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `trans`：trans [IsTrans α r] : a ≺ b -> b ≺ c -> a ≺ c
-/
@[elab_without_expected_type] lemma trans_of [IsTrans α r] : a ≺ b → b ≺ c → a ≺ c := _root_.trans
/-
**symm_of** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Sort u_1} (r : α → α → Prop) {a b : α} [Std.Symm r], r a b → r b a
参数：r : α → α → Prop。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `symm`：symm [Std.Symm r] : a ≺ b -> b ≺ a
-/
@[elab_without_expected_type] lemma symm_of [Std.Symm r] : a ≺ b → b ≺ a := symm
/-
**asymm_of** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Sort u_1} (r : α → α → Prop) {a b : α} [Std.Asymm r], r a b → ¬r b 
a
参数：r : α → α → Prop。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `asymm`：asymm [Std.Asymm r] : a ≺ b -> ¬b ≺ a
-/
@[elab_without_expected_type] lemma asymm_of [Std.Asymm r] : a ≺ b → ¬b ≺ a := asymm

@[elab_without_expected_type]
/-
**total_of** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：total_of [Std.Total r] (a b : α) : a ≺ b ∨ b ≺ a
参数：a b : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Std.Total.total`：∀ {α : Sort u} {r : α → α → Prop} [self : Std.Total r] 
(a b : α), r a b ∨ r b a
-/
lemma total_of [Std.Total r] (a b : α) : a ≺ b ∨ b ≺ a := Std.Total.total _ _

@[elab_without_expected_type]
/-
**trichotomous_of** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：trichotomous_of [Std.Trichotomous r] : forall a b : α, a ≺ b ∨ a = b ∨ b ≺
 a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `trichotomous`：trichotomous [Std.Trichotomous r] : forall a b : α, a ≺ b 
∨ a = b ∨ b ≺ a
-/
lemma trichotomous_of [Std.Trichotomous r] : ∀ a b : α, a ≺ b ∨ a = b ∨ b ≺ a := trichotomous

section

/-- `Std.Refl` as a definition, suitable for use in proofs. -/
@[deprecated Std.Refl (since := "2026-03-27")]
/-
**Reflexive** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Reflexive
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Std.Refl` as a definition, suitable for use in proofs.
-/
def Reflexive := ∀ x, x ≺ x

/-- `Std.Symm` as a definition, suitable for use in proofs. -/
@[deprecated Std.Symm (since := "2026-06-10")]
/-
**Symmetric** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Symmetric
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Std.Symm` as a definition, suitable for use in proofs.
-/
def Symmetric := ∀ ⦃x y⦄, x ≺ y → y ≺ x

/-- `IsTrans` as a definition, suitable for use in proofs. -/
@[deprecated IsTrans (since := "2026-02-20")]
/-
**Transitive** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Transitive
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`IsTrans` as a definition, suitable for use in proofs.
-/
def Transitive := ∀ ⦃x y z⦄, x ≺ y → y ≺ z → x ≺ z

/-- `Std.Irrefl` as a definition, suitable for use in proofs. -/
@[deprecated Std.Irrefl (since := "2026-02-12")]
/-
**Irreflexive** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Irreflexive
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Std.Irrefl` as a definition, suitable for use in proofs.
-/
def Irreflexive := ∀ x, ¬x ≺ x

/-- `Std.Antisymm` as a definition, suitable for use in proofs. -/
@[deprecated Std.Antisymm (since := "2026-02-09")]
/-
**AntiSymmetric** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：AntiSymmetric
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Std.Antisymm` as a definition, suitable for use in proofs.
-/
def AntiSymmetric := ∀ ⦃x y⦄, x ≺ y → y ≺ x → x = y

/-- `Std.Total` as a definition, suitable for use in proofs. -/
@[deprecated Std.Total (since := "2026-02-10")]
/-
**Total** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Total
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Std.Total` as a definition, suitable for use in proofs.
-/
def Total := ∀ x y, x ≺ y ∨ y ≺ x
/-
**Equivalence.stdRefl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Equivalence.stdRefl (h : Equivalence r) : Std.Refl r where refl
参数：h : Equivalence r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equivalence.refl`：∀ {α : Sort u} {r : α → α → Prop}, Equivalence r → ∀ (
x : α), r x x
-/
theorem Equivalence.stdRefl (h : Equivalence r) : Std.Refl r where
  refl := h.refl

@[deprecated (since := "2026-03-27")] alias Equivalence.reflexive := Equivalence.stdRefl
/-
**Equivalence.stdSymm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Equivalence.stdSymm (h : Equivalence r) : Std.Symm r where symm _ _
参数：h : Equivalence r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equivalence.symm`：∀ {α : Sort u} {r : α → α → Prop}, Equivalence r → ∀ {
x y : α}, r x y → r y x
-/
theorem Equivalence.stdSymm (h : Equivalence r) : Std.Symm r where
  symm _ _ := h.symm

@[deprecated (since := "2026-06-10")] alias Equivalence.symmetric := Equivalence.stdSymm
/-
**Equivalence.isTrans** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Equivalence.isTrans (h : Equivalence r) : IsTrans α r
参数：h : Equivalence r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equivalence.trans`：∀ {α : Sort u} {r : α → α → Prop}, Equivalence r → ∀ 
{x y z : α}, r x y → r y z → r x z
-/
theorem Equivalence.isTrans (h : Equivalence r) : IsTrans α r :=
  ⟨fun _ _ _ ↦ h.trans⟩

@[deprecated (since := "2026-02-20")] alias Equivalence.transitive := Equivalence.isTrans
/-
**Equivalence.isEquiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Equivalence.isEquiv (h : Equivalence r) : IsEquiv α r
参数：h : Equivalence r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equivalence.stdRefl`：Equivalence.stdRefl (h : Equivalence r) : Std.Refl 
r where refl
· 使用定理 `Equivalence.stdSymm`：Equivalence.stdSymm (h : Equivalence r) : Std.Symm 
r where symm _ _
· 使用定理 `Equivalence.isTrans`：Equivalence.isTrans (h : Equivalence r) : IsTrans α
 r
-/
theorem Equivalence.isEquiv (h : Equivalence r) : IsEquiv α r :=
  have := h.stdRefl
  have := h.stdSymm
  have := h.isTrans
  {}

variable {β : Sort*} (r : β → β → Prop) (f : α → β)
/-
**InvImage.isTrans** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：InvImage.isTrans [IsTrans β r] : IsTrans α (InvImage r f)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `trans_of`：∀ {α : Sort u_1} (r : α → α → Prop) {a b c : α} [IsTrans α r],
 r a b → r b c → r a c
-/
instance InvImage.isTrans [IsTrans β r] : IsTrans α (InvImage r f) :=
  ⟨fun _ _ _ ↦ trans_of r⟩

@[deprecated (since := "2026-02-20")] alias InvImage.trans := InvImage.isTrans
/-
**InvImage.irrefl** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：InvImage.irrefl [Std.Irrefl r] : Std.Irrefl (InvImage r f)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `irrefl_of`：∀ {α : Sort u_1} (r : α → α → Prop) [Std.Irrefl r] (a : α), ¬
r a a
-/
instance InvImage.irrefl [Std.Irrefl r] : Std.Irrefl (InvImage r f) :=
  ⟨fun (a : α) (h₁ : InvImage r f a a) ↦ irrefl_of r (f a) h₁⟩

@[deprecated (since := "2026-02-12")] alias InvImage.irreflexive := InvImage.irrefl

end

end

/-! ### Minimal and maximal -/

section LE

variable {α : Type*} [LE α] {P : α → Prop} {x y : α}

/-- `Minimal P x` means that `x` is a minimal element satisfying `P`. -/
@[to_dual /-- `Maximal P x` means that `x` is a maximal element satisfying `P`. -/]
/-
**Minimal** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Minimal (P : α -> Prop) (x : α) : Prop
参数：P : α -> Prop；x : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Minimal P x` means that `x` is a minimal element satisfying `P`.
-/
def Minimal (P : α → Prop) (x : α) : Prop := P x ∧ ∀ ⦃y⦄, P y → y ≤ x → x ≤ y

@[to_dual]
/-
**Minimal.prop** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Minimal.prop (h : Minimal P x) : P x
参数：h : Minimal P x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma Minimal.prop (h : Minimal P x) : P x :=
  h.1

@[to_dual le_of_ge] -- TODO: improve this naming
/-
**Minimal.le_of_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Minimal.le_of_le (h : Minimal P x) (hy : P y) (hle : y <= x) : x <= y
参数：h : Minimal P x；hy : P y；hle : y <= x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma Minimal.le_of_le (h : Minimal P x) (hy : P y) (hle : y ≤ x) : x ≤ y :=
  h.2 hy hle

end LE

section LE
variable {ι : Sort*} {α : Type*} [LE α] {P : ι → Prop} {f : ι → α} {i j : ι}

/-- `MinimalFor P f i` means that `f i` is minimal over all `i` satisfying `P`. -/
@[to_dual /-- `MaximalFor P f i` means that `f i` is maximal over all `i` satisfying `P`. -/]
/-
**MinimalFor** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：MinimalFor (P : ι -> Prop) (f : ι -> α) (i : ι) : Prop
参数：P : ι -> Prop；f : ι -> α；i : ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`MinimalFor P f i` means that `f i` is minimal over all `i` satisfying `P`.
-/
def MinimalFor (P : ι → Prop) (f : ι → α) (i : ι) : Prop := P i ∧ ∀ ⦃j⦄, P j → f j ≤ f i → f i ≤ f j

@[to_dual]
/-
**MinimalFor.prop** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MinimalFor.prop (h : MinimalFor P f i) : P i
参数：h : MinimalFor P f i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma MinimalFor.prop (h : MinimalFor P f i) : P i := h.1

@[to_dual]
/-
**MinimalFor.le_of_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MinimalFor.le_of_le (h : MinimalFor P f i) (hj : P j) (hji : f j <= f i) :
 f i <= f j
参数：h : MinimalFor P f i；hj : P j；hji : f j <= f i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma MinimalFor.le_of_le (h : MinimalFor P f i) (hj : P j) (hji : f j ≤ f i) : f i ≤ f j :=
  h.2 hj hji

end LE

/-! ### Upper and lower sets -/

/-- An upper set in an order `α` is a set such that any element greater than one of its members is
also a member. Also called up-set, upward-closed set. -/
@[to_dual /-- A lower set in an order `α` is a set such that any element less than one of its
members is also a member. Also called down-set, downward-closed set. -/]
/-
**IsUpperSet** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsUpperSet {α : Type*} [LE α] (s : Set α) : Prop
参数：s : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def IsUpperSet {α : Type*} [LE α] (s : Set α) : Prop :=
  ∀ ⦃a b : α⦄, a ≤ b → a ∈ s → b ∈ s

@[inherit_doc IsUpperSet]
/-
**UpperSet** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_1) → [LE α] → Type u_1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
structure UpperSet (α : Type*) [LE α] where
  /-- The carrier of an `UpperSet`. -/
  carrier : Set α
  /-- The carrier of an `UpperSet` is an upper set. -/
  upper' : IsUpperSet carrier

extend_docs UpperSet before "The type of upper sets of an order."

@[inherit_doc IsLowerSet, to_dual]
/-
**LowerSet** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_1) → [LE α] → Type u_1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
structure LowerSet (α : Type*) [LE α] where
  /-- The carrier of a `LowerSet`. -/
  carrier : Set α
  /-- The carrier of a `LowerSet` is a lower set. -/
  lower' : IsLowerSet carrier

extend_docs LowerSet before "The type of lower sets of an order."

/-- An upper set relative to a predicate `P` is a set such that all elements satisfy `P` and
any element greater than one of its members and satisfying `P` is also a member. -/
@[to_dual /-- A lower set relative to a predicate `P` is a set such that all elements satisfy `P`
and any element less than one of its members and satisfying `P` is also a member. -/]
/-
**IsRelUpperSet** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsRelUpperSet {α : Type*} [LE α] (s : Set α) (P : α -> Prop) : Prop
参数：s : Set α；P : α -> Prop。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def IsRelUpperSet {α : Type*} [LE α] (s : Set α) (P : α → Prop) : Prop :=
  ∀ ⦃a : α⦄, a ∈ s → P a ∧ ∀ ⦃b : α⦄, a ≤ b → P b → b ∈ s

@[inherit_doc IsRelUpperSet]
/-
**RelUpperSet** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{α : Type u_1} → [LE α] → (α → Prop) → Type u_1
参数：α → Prop。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
structure RelUpperSet {α : Type*} [LE α] (P : α → Prop) where
  /-- The carrier of a `RelUpperSet`. -/
  carrier : Set α
  /-- The carrier of a `RelUpperSet` is an upper set relative to `P`.

  Do NOT use directly. Please use `RelUpperSet.isRelUpperSet` instead. -/
  isRelUpperSet' : IsRelUpperSet carrier P

extend_docs RelUpperSet before "The type of upper sets of an order relative to `P`."

@[inherit_doc IsRelLowerSet, to_dual]
/-
**RelLowerSet** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{α : Type u_1} → [LE α] → (α → Prop) → Type u_1
参数：α → Prop。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
structure RelLowerSet {α : Type*} [LE α] (P : α → Prop) where
  /-- The carrier of a `RelLowerSet`. -/
  carrier : Set α
  /-- The carrier of a `RelLowerSet` is a lower set relative to `P`.

  Do NOT use directly. Please use `RelLowerSet.isRelLowerSet` instead. -/
  isRelLowerSet' : IsRelLowerSet carrier P

extend_docs RelLowerSet before "The type of lower sets of an order relative to `P`."

variable {α β : Sort*} {r : α → α → Prop} {s : β → β → Prop}
/-
**of_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：of_eq {α} {a b c : α} (_ : (a : α) = c) (_ : b = c) : a = b
参数：_ : (a : α) = c；_ : b = c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `refl`：refl [Std.Refl r] (a : α) : a ≺ a
-/
theorem of_eq [Std.Refl r] : ∀ {a b}, a = b → r a b
  | _, _, .refl _ => refl _
/-
**comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：comm [Std.Symm r] {a b : α} : r a b ↔ r b a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `symm`：symm [Std.Symm r] : a ≺ b -> b ≺ a
-/
theorem comm [Std.Symm r] {a b : α} : r a b ↔ r b a :=
  ⟨symm, symm⟩
/-
**antisymm'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：antisymm' [Std.Antisymm r] {a b : α} : r a b -> r b a -> b = a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `antisymm`：antisymm [Std.Antisymm r] : a ≺ b -> b ≺ a -> a = b
-/
theorem antisymm' [Std.Antisymm r] {a b : α} : r a b → r b a → b = a := fun h h' => antisymm h' h
/-
**antisymm_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：antisymm_iff [Std.Refl r] [Std.Antisymm r] {a b : α} : r a b ∧ r b a ↔ a =
 b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `antisymm`：antisymm [Std.Antisymm r] : a ≺ b -> b ≺ a -> a = b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `refl`：refl [Std.Refl r] (a : α) : a ≺ a
-/
theorem antisymm_iff [Std.Refl r] [Std.Antisymm r] {a b : α} : r a b ∧ r b a ↔ a = b :=
  ⟨fun h => antisymm h.1 h.2, by
    rintro rfl
    exact ⟨refl _, refl _⟩⟩

/-- A version of `antisymm` with `r` explicit.

This lemma matches the lemmas from lean core in `Init.Algebra.Classes`, but is missing there. -/
@[elab_without_expected_type]
/-
**antisymm_of** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：antisymm_of (r : α -> α -> Prop) [Std.Antisymm r] {a b : α} : r a b -> r b
 a -> a = b
参数：r : α -> α -> Prop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `antisymm`：antisymm [Std.Antisymm r] : a ≺ b -> b ≺ a -> a = b

--- 原说明 ---
A version of `antisymm` with `r` explicit.

This lemma matches the lemmas from lean core in `Init.Algebra.Classes`, but is m
issing there.
-/
theorem antisymm_of (r : α → α → Prop) [Std.Antisymm r] {a b : α} : r a b → r b a → a = b :=
  antisymm

/-- A version of `antisymm'` with `r` explicit.

This lemma matches the lemmas from lean core in `Init.Algebra.Classes`, but is missing there. -/
@[elab_without_expected_type]
/-
**antisymm_of'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：antisymm_of' (r : α -> α -> Prop) [Std.Antisymm r] {a b : α} : r a b -> r 
b a -> b = a
参数：r : α -> α -> Prop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `antisymm'`：antisymm' [Std.Antisymm r] {a b : α} : r a b -> r b a -> b = 
a

--- 原说明 ---
A version of `antisymm'` with `r` explicit.

This lemma matches the lemmas from lean core in `Init.Algebra.Classes`, but is m
issing there.
-/
theorem antisymm_of' (r : α → α → Prop) [Std.Antisymm r] {a b : α} : r a b → r b a → b = a :=
  antisymm'

/-- A version of `comm` with `r` explicit.

This lemma matches the lemmas from lean core in `Init.Algebra.Classes`, but is missing there. -/
/-
**comm_of** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：comm_of (r : α -> α -> Prop) [Std.Symm r] {a b : α} : r a b ↔ r b a
参数：r : α -> α -> Prop。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `comm`：comm [Std.Symm r] {a b : α} : r a b ↔ r b a

--- 原说明 ---
A version of `comm` with `r` explicit.

This lemma matches the lemmas from lean core in `Init.Algebra.Classes`, but is m
issing there.
-/
theorem comm_of (r : α → α → Prop) [Std.Symm r] {a b : α} : r a b ↔ r b a :=
  comm
/-
**Std.Asymm.antisymm** 是 Mathlib 中的一个定理，位于命名空间 `Std.Asymm`。
形式化陈述：∀ {α : Sort u_1} (r : α → α → Prop) [Std.Asymm r], Std.Antisymm r
参数：r : α → α → Prop。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Std.instAntisymmOfAsymm`：∀ {α : Sort u_1} (r : α → α → Prop) [Std.Asymm 
r], Std.Antisymm r
-/
protected theorem Std.Asymm.antisymm (r : α → α → Prop) [Std.Asymm r] : Std.Antisymm r :=
  inferInstance

@[deprecated (since := "2026-01-05")] protected alias IsAsymm.isAntisymm := Std.Asymm.antisymm
@[deprecated (since := "2026-01-06")] protected alias Std.Asymm.isAntisymm := Std.Asymm.antisymm
/-
**Std.Asymm.irrefl** 是 Mathlib 中的一个定理，位于命名空间 `Std.Asymm`。
形式化陈述：∀ {α : Sort u_1} {r : α → α → Prop} [Std.Asymm r], Std.Irrefl r
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Std.instIrreflOfAsymm`：∀ {α : Sort u_1} (r : α → α → Prop) [Std.Asymm r]
, Std.Irrefl r
-/
protected theorem Std.Asymm.irrefl [Std.Asymm r] : Std.Irrefl r :=
  inferInstance

@[deprecated (since := "2026-01-05")] protected alias IsAsymm.isIrrefl := Std.Asymm.irrefl
@[deprecated (since := "2026-01-07")] protected alias Std.Asymm.isIrrefl := Std.Asymm.irrefl
/-
**Std.Total.trichotomous** 是 Mathlib 中的一个定理，位于命名空间 `Std.Total`。
形式化陈述：∀ {α : Sort u_1} (r : α → α → Prop) [Std.Total r], Std.Trichotomous r
参数：r : α → α → Prop。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Std.instTrichotomousOfTotal`：∀ {α : Sort u_1} (r : α → α → Prop) [Std.To
tal r], Std.Trichotomous r
-/
protected theorem Std.Total.trichotomous (r : α → α → Prop) [Std.Total r] : Std.Trichotomous r :=
  inferInstance

@[deprecated (since := "2026-01-24")] alias Std.Total.isTrichotomous := Std.Total.trichotomous

-- see Note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) Std.Total.to_refl (r : α → α → Prop) [Std.Total r] : Std.Refl r :=
  inferInstance
/-
**ne_of_irrefl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Sort u_1} {r : α → α → Prop} [Std.Irrefl r] {x y : α}, r x y → x ≠ 
y
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `irrefl`：irrefl [Std.Irrefl r] (a : α) : ¬a ≺ a
-/
theorem ne_of_irrefl {r} [Std.Irrefl r] : ∀ {x y : α}, r x y → x ≠ y
  | _, _, h, rfl => irrefl _ h
/-
**ne_of_irrefl'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Sort u_1} {r : α → α → Prop} [Std.Irrefl r] {x y : α}, r x y → y ≠ 
x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `irrefl`：irrefl [Std.Irrefl r] (a : α) : ¬a ≺ a
-/
theorem ne_of_irrefl' {r} [Std.Irrefl r] : ∀ {x y : α}, r x y → y ≠ x
  | _, _, h, rfl => irrefl _ h
/-
**not_rel_of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_rel_of_subsingleton (r : α -> α -> Prop) [Std.Irrefl r] [Subsingleton 
α] (x y) : ¬r x y
参数：r : α -> α -> Prop；x y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `irrefl`：irrefl [Std.Irrefl r] (a : α) : ¬a ≺ a
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
theorem not_rel_of_subsingleton (r : α → α → Prop) [Std.Irrefl r] [Subsingleton α] (x y) : ¬r x y :=
  Subsingleton.elim x y ▸ irrefl x
/-
**rel_of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rel_of_subsingleton (r : α -> α -> Prop) [Std.Refl r] [Subsingleton α] (x 
y) : r x y
参数：r : α -> α -> Prop；x y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `refl`：refl [Std.Refl r] (a : α) : a ≺ a
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
theorem rel_of_subsingleton (r : α → α → Prop) [Std.Refl r] [Subsingleton α] (x y) : r x y :=
  Subsingleton.elim x y ▸ refl x

@[simp]
/-
**empty_relation_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：empty_relation_apply (a b : α) : emptyRelation a b ↔ False
参数：a b : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem empty_relation_apply (a b : α) : emptyRelation a b ↔ False :=
  Iff.rfl
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : @Std.Irrefl α emptyRelation :=
  ⟨fun _ => id⟩
/-
**rel_congr_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rel_congr_left [Std.Symm r] [IsTrans α r] {a b c : α} (h : r a b) : r a c 
↔ r b c
参数：h : r a b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `trans_of`：∀ {α : Sort u_1} (r : α → α → Prop) {a b c : α} [IsTrans α r],
 r a b → r b c → r a c
· 使用定理 `symm_of`：∀ {α : Sort u_1} (r : α → α → Prop) {a b : α} [Std.Symm r], r a
 b → r b a
-/
theorem rel_congr_left [Std.Symm r] [IsTrans α r] {a b c : α} (h : r a b) : r a c ↔ r b c :=
  ⟨trans_of r (symm_of r h), trans_of r h⟩
/-
**rel_congr_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rel_congr_right [Std.Symm r] [IsTrans α r] {a b c : α} (h : r b c) : r a b
 ↔ r a c
参数：h : r b c。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `trans_of`：∀ {α : Sort u_1} (r : α → α → Prop) {a b c : α} [IsTrans α r],
 r a b → r b c → r a c
· 使用定理 `symm_of`：∀ {α : Sort u_1} (r : α → α → Prop) {a b : α} [Std.Symm r], r a
 b → r b a
-/
theorem rel_congr_right [Std.Symm r] [IsTrans α r] {a b c : α} (h : r b c) : r a b ↔ r a c :=
  ⟨(trans_of r · h), (trans_of r · (symm_of r h))⟩
/-
**rel_congr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rel_congr [Std.Symm r] [IsTrans α r] {a b c d : α} (h₁ : r a b) (h₂ : r c 
d) : r a c ↔ r b d
参数：h₁ : r a b；h₂ : r c d。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `rel_congr_left`：rel_congr_left [Std.Symm r] [IsTrans α r] {a b c : α} (h
 : r a b) : r a c ↔ r b c
· 使用定理 `rel_congr_right`：rel_congr_right [Std.Symm r] [IsTrans α r] {a b c : α} 
(h : r b c) : r a b ↔ r a c
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem rel_congr [Std.Symm r] [IsTrans α r] {a b c d : α} (h₁ : r a b) (h₂ : r c d) :
    r a c ↔ r b d := by
  rw [rel_congr_left h₁, rel_congr_right h₂]
/-
**trans_trichotomous_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：trans_trichotomous_left [IsTrans α r] [Std.Trichotomous r] {a b c : α} (h₁
 : ¬r b a) (h₂ : r b c) : r a c
参数：h₁ : ¬r b a；h₂ : r b c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `trichotomous_of`：trichotomous_of [Std.Trichotomous r] : forall a b : α, 
a ≺ b ∨ a = b ∨ b ≺ a
· 使用引理 `trans`：trans [IsTrans α r] : a ≺ b -> b ≺ c -> a ≺ c
-/
theorem trans_trichotomous_left [IsTrans α r] [Std.Trichotomous r] {a b c : α}
    (h₁ : ¬r b a) (h₂ : r b c) : r a c := by
  rcases trichotomous_of r a b with (h₃ | rfl | h₃)
  · exact _root_.trans h₃ h₂
  · exact h₂
  · exact absurd h₃ h₁
/-
**trans_trichotomous_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：trans_trichotomous_right [IsTrans α r] [Std.Trichotomous r] {a b c : α} (h
₁ : r a b) (h₂ : ¬r c b) : r a c
参数：h₁ : r a b；h₂ : ¬r c b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `trichotomous_of`：trichotomous_of [Std.Trichotomous r] : forall a b : α, 
a ≺ b ∨ a = b ∨ b ≺ a
· 使用引理 `trans`：trans [IsTrans α r] : a ≺ b -> b ≺ c -> a ≺ c
-/
theorem trans_trichotomous_right [IsTrans α r] [Std.Trichotomous r] {a b c : α}
    (h₁ : r a b) (h₂ : ¬r c b) : r a c := by
  rcases trichotomous_of r b c with (h₃ | rfl | h₃)
  · exact _root_.trans h₁ h₃
  · exact h₁
  · exact absurd h₃ h₂

@[deprecated IsTrans.trans (since := "2026-02-20")]
/-
**transitive_of_trans** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：transitive_of_trans (r : α -> α -> Prop) [IsTrans α r] : Transitive r
参数：r : α -> α -> Prop。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTrans.trans`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsTrans α r] 
(a b c : α), r a b → r b c → r a c
-/
theorem transitive_of_trans (r : α → α → Prop) [IsTrans α r] : Transitive r := IsTrans.trans

/-- In a trichotomous irreflexive order, every element is determined by the set of predecessors. -/
/-
**extensional_of_trichotomous_of_irrefl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：extensional_of_trichotomous_of_irrefl (r : α -> α -> Prop) [Std.Trichotomo
us r] [Std.Irrefl r] {a b : α} (H : forall x, r x a ↔ r x b) : a = b
参数：r : α -> α -> Prop；H : forall x, r x a ↔ r x b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用引理 `trichotomous`：trichotomous [Std.Trichotomous r] : forall a b : α, a ≺ b 
∨ a = b ∨ b ≺ a
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `irrefl`：irrefl [Std.Irrefl r] (a : α) : ¬a ≺ a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b

--- 原说明 ---
In a trichotomous irreflexive order, every element is determined by the set of p
redecessors.
-/
theorem extensional_of_trichotomous_of_irrefl (r : α → α → Prop) [Std.Trichotomous r] [Std.Irrefl r]
    {a b : α} (H : ∀ x, r x a ↔ r x b) : a = b :=
  ((@trichotomous _ r _ a b).resolve_left <| mt (H _).2 <| irrefl a).resolve_right <| mt (H _).1
    <| irrefl b
