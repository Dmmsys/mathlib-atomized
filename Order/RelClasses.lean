/-
Copyright (c) 2020 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Mario Carneiro, Yury Kudryashov
-/
module

public import Mathlib.Logic.IsEmpty.Basic
public import Mathlib.Order.OrderDual
public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Tactic.MkIffOfInductiveProp

/-!
# Unbundled relation classes

In this file we prove some properties of `Is*` classes defined in
`Mathlib/Order/Defs/Unbundled.lean`.
The main difference between these classes and the usual order classes (`Preorder` etc) is that
usual classes extend `LE` and/or `LT` while these classes take a relation as an explicit argument.
-/

@[expose] public section

universe u v

variable {α : Type u} {β : Type v} {r : α → α → Prop} {s : β → β → Prop}

open Function

@[deprecated inferInstance (since := "2026-04-28")]
/-
**Std.Refl.swap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Std.Refl.swap (r : α -> α -> Prop) [Std.Refl r] : Std.Refl (swap r)
参数：r : α -> α -> Prop。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.instReflSwapProp`：∀ {α : Sort u_1} (r : α → α → Prop) [Std.Refl
 r], Std.Refl (Function.swap r)
-/
theorem Std.Refl.swap (r : α → α → Prop) [Std.Refl r] : Std.Refl (swap r) :=
  inferInstance

@[deprecated (since := "2026-01-09")] alias IsRefl.swap := Std.Refl.swap

@[deprecated inferInstance (since := "2026-04-28")]
/-
**Std.Irrefl.swap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Std.Irrefl.swap (r : α -> α -> Prop) [Std.Irrefl r] : Std.Irrefl (swap r)
参数：r : α -> α -> Prop。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.instIrreflSwapProp`：∀ {α : Sort u_1} (r : α → α → Prop) [Std.Ir
refl r], Std.Irrefl (Function.swap r)
-/
theorem Std.Irrefl.swap (r : α → α → Prop) [Std.Irrefl r] : Std.Irrefl (swap r) :=
  inferInstance

@[deprecated inferInstance (since := "2026-04-28")]
/-
**IsTrans.swap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsTrans.swap (r) [IsTrans α r] : IsTrans α (swap r)
参数：r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.instIsTransSwapProp`：∀ {α : Sort u_1} (r : α → α → Prop) [IsTra
ns α r], IsTrans α (Function.swap r)
-/
theorem IsTrans.swap (r) [IsTrans α r] : IsTrans α (swap r) :=
  inferInstance

@[deprecated inferInstance (since := "2026-04-28")]
/-
**Std.Antisymm.swap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Std.Antisymm.swap (r : α -> α -> Prop) [Std.Antisymm r] : Std.Antisymm (sw
ap r)
参数：r : α -> α -> Prop。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.instAntisymmSwapProp`：∀ {α : Sort u_1} (r : α → α → Prop) [Std.
Antisymm r], Std.Antisymm (Function.swap r)
-/
theorem Std.Antisymm.swap (r : α → α → Prop) [Std.Antisymm r] : Std.Antisymm (swap r) :=
  inferInstance

@[deprecated inferInstance (since := "2026-04-28")]
/-
**Std.Asymm.swap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Std.Asymm.swap (r : α -> α -> Prop) [Std.Asymm r] : Std.Asymm (swap r)
参数：r : α -> α -> Prop。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.instAsymmSwapProp`：∀ {α : Sort u_1} (r : α → α → Prop) [Std.Asy
mm r], Std.Asymm (Function.swap r)
-/
theorem Std.Asymm.swap (r : α → α → Prop) [Std.Asymm r] : Std.Asymm (swap r) :=
  inferInstance

@[deprecated (since := "2026-01-05")] alias IsAsymm.swap := Std.Asymm.swap

@[deprecated inferInstance (since := "2026-04-28")]
/-
**Std.Total.swap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Std.Total.swap (r : α -> α -> Prop) [Std.Total r] : Std.Total (swap r)
参数：r : α -> α -> Prop。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.instTotalSwapProp`：∀ {α : Sort u_1} (r : α → α → Prop) [Std.Tot
al r], Std.Total (Function.swap r)
-/
theorem Std.Total.swap (r : α → α → Prop) [Std.Total r] : Std.Total (swap r) :=
  inferInstance

@[deprecated inferInstance (since := "2026-04-28")]
/-
**Std.Trichotomous.swap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Std.Trichotomous.swap (r : α -> α -> Prop) [Std.Trichotomous r] : Std.Tric
hotomous (swap r)
参数：r : α -> α -> Prop。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.instTrichotomousSwapProp`：∀ {α : Sort u_1} (r : α → α → Prop) [
Std.Trichotomous r], Std.Trichotomous (Function.swap r)
-/
theorem Std.Trichotomous.swap (r : α → α → Prop) [Std.Trichotomous r] : Std.Trichotomous (swap r) :=
  inferInstance

@[deprecated (since := "2026-01-24")] alias IsTrichotomous.swap := Std.Trichotomous.swap

@[deprecated inferInstance (since := "2026-04-28")]
/-
**IsPreorder.swap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsPreorder.swap (r) [IsPreorder α r] : IsPreorder α (swap r)
参数：r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.instIsPreorderSwapProp`：∀ {α : Sort u_1} (r : α → α → Prop) [Is
Preorder α r], IsPreorder α (Function.swap r)
-/
theorem IsPreorder.swap (r) [IsPreorder α r] : IsPreorder α (swap r) :=
  inferInstance

@[deprecated inferInstance (since := "2026-04-28")]
/-
**IsStrictOrder.swap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsStrictOrder.swap (r) [IsStrictOrder α r] : IsStrictOrder α (swap r)
参数：r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.instIsStrictOrderSwapProp`：∀ {α : Sort u_1} (r : α → α → Prop) 
[IsStrictOrder α r], IsStrictOrder α (Function.swap r)
-/
theorem IsStrictOrder.swap (r) [IsStrictOrder α r] : IsStrictOrder α (swap r) :=
  inferInstance

@[deprecated inferInstance (since := "2026-04-28")]
/-
**IsPartialOrder.swap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsPartialOrder.swap (r) [IsPartialOrder α r] : IsPartialOrder α (swap r)
参数：r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.instIsPartialOrderSwapProp`：∀ {α : Sort u_1} (r : α → α → Prop)
 [IsPartialOrder α r], IsPartialOrder α (Function.swap r)
-/
theorem IsPartialOrder.swap (r) [IsPartialOrder α r] : IsPartialOrder α (swap r) :=
  inferInstance
/-
**eq_empty_relation** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_empty_relation (r : α -> α -> Prop) [Std.Irrefl r] [Subsingleton α] : r
 = emptyRelation
参数：r : α -> α -> Prop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext₂`：∀ {α : Sort u_1} {β : α → Sort u_2} {γ : (a : α) → β a → Sort u
_3} {f g : (a : α) → (b : β a) → γ a b},   (∀ (a : α) (b : β a), f a b = g a …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
· 使用定理 `not_rel_of_subsingleton`：not_rel_of_subsingleton (r : α -> α -> Prop) [S
td.Irrefl r] [Subsingleton α] (x y) : ¬r x y
-/
theorem eq_empty_relation (r : α → α → Prop) [Std.Irrefl r] [Subsingleton α] : r = emptyRelation :=
  funext₂ <| by simpa using not_rel_of_subsingleton r

/-- Construct a partial order from an `isStrictOrder` relation.

See note [reducible non-instances]. -/
/-
**partialOrderOfSO** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：partialOrderOfSO (r) [IsStrictOrder α r] : PartialOrder α where le x y
参数：r。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a partial order from an `isStrictOrder` relation.

See note [reducible non-instances].
-/
abbrev partialOrderOfSO (r) [IsStrictOrder α r] : PartialOrder α where
  le x y := x = y ∨ r x y
  lt := r
  le_refl _ := Or.inl rfl
  le_trans x y z h₁ h₂ :=
    match y, z, h₁, h₂ with
    | _, _, Or.inl rfl, h₂ => h₂
    | _, _, h₁, Or.inl rfl => h₁
    | _, _, Or.inr h₁, Or.inr h₂ => Or.inr (_root_.trans h₁ h₂)
  le_antisymm x y h₁ h₂ :=
    match y, h₁, h₂ with
    | _, Or.inl rfl, _ => rfl
    | _, _, Or.inl rfl => rfl
    | _, Or.inr h₁, Or.inr h₂ => (asymm h₁ h₂).elim
  lt_iff_le_not_ge x y :=
    ⟨fun h => ⟨Or.inr h, not_or_intro (fun e => by rw [e] at h; exact irrefl _ h) (asymm h)⟩,
      fun ⟨h₁, h₂⟩ => h₁.resolve_left fun e => h₂ <| e ▸ Or.inl rfl⟩

/-- Construct a linear order from an `IsStrictTotalOrder` relation.

See note [reducible non-instances]. -/
/-
**linearOrderOfSTO** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：linearOrderOfSTO (r) [IsStrictTotalOrder α r] [DecidableRel r] : LinearOrd
er α
参数：r。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictTotalOrder.toIsStrictOrder`：∀ {α : Sort u_1} {lt : α → α → Prop}
 [self : IsStrictTotalOrder α lt], IsStrictOrder α lt

--- 原说明 ---
Construct a linear order from an `IsStrictTotalOrder` relation.

See note [reducible non-instances].
-/
abbrev linearOrderOfSTO (r) [IsStrictTotalOrder α r] [DecidableRel r] : LinearOrder α :=
  let hD : DecidableRel (fun x y => x = y ∨ r x y) := fun x y => decidable_of_iff (¬r y x)
    ⟨fun h => ((trichotomous_of r y x).resolve_left h).imp Eq.symm id, fun h =>
      h.elim (fun h => h ▸ irrefl_of _ _) (asymm_of r)⟩
  { __ := partialOrderOfSO r
    le_total := fun x y =>
      match y, trichotomous_of r x y with
      | _, Or.inl h => Or.inl (Or.inr h)
      | _, Or.inr (Or.inl rfl) => Or.inl (Or.inl rfl)
      | _, Or.inr (Or.inr h) => Or.inr (Or.inr h),
    toMin := minOfLe,
    toMax := maxOfLe,
    toDecidableLE := hD }

@[deprecated inferInstance (since := "2026-04-28")]
/-
**IsStrictTotalOrder.swap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsStrictTotalOrder.swap (r) [IsStrictTotalOrder α r] : IsStrictTotalOrder 
α (swap r)
参数：r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.instIsStrictTotalOrderSwapProp`：∀ {α : Sort u_1} (r : α → α → P
rop) [IsStrictTotalOrder α r], IsStrictTotalOrder α (Function.swap r)
-/
theorem IsStrictTotalOrder.swap (r) [IsStrictTotalOrder α r] : IsStrictTotalOrder α (swap r) :=
  inferInstance

/-! ### Order connection -/

/-- A connected order is one satisfying the condition `a < c → a < b ∨ b < c`.
  This is recognizable as an intuitionistic substitute for `a ≤ b ∨ b ≤ a` on
  the constructive reals, and is also known as negative transitivity,
  since the contrapositive asserts transitivity of the relation `¬ a < b`. -/
/-
**IsOrderConnected** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u) → (α → α → Prop) → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A connected order is one satisfying the condition `a < c → a < b ∨ b < c`.
  This is recognizable as an intuitionistic substitute for `a ≤ b ∨ b ≤ a` on
  the constructive reals, and is also known as negative transitivity,
  since the contrapositive asserts transitivity of the relation `¬ a < b`.
-/
class IsOrderConnected (α : Type u) (lt : α → α → Prop) : Prop where
  /-- A connected order is one satisfying the condition `a < c → a < b ∨ b < c`. -/
  conn : ∀ a b c, lt a c → lt a b ∨ lt b c
/-
**IsOrderConnected.neg_trans** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsOrderConnected.neg_trans {r : α -> α -> Prop} [IsOrderConnected α r] {a 
b c} (h₁ : ¬r a b) (h₂ : ¬r b c) : ¬r a c
参数：h₁ : ¬r a b；h₂ : ¬r b c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `IsOrderConnected.conn`：∀ {α : Type u} {lt : α → α → Prop} [self : IsOrde
rConnected α lt] (a b c : α), lt a c → lt a b ∨ lt b c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem IsOrderConnected.neg_trans {r : α → α → Prop} [IsOrderConnected α r] {a b c}
    (h₁ : ¬r a b) (h₂ : ¬r b c) : ¬r a c :=
  mt (IsOrderConnected.conn a b c) <| by simp [h₁, h₂]
/-
**isStrictWeakOrder_of_isOrderConnected** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isStrictWeakOrder_of_isOrderConnected [Std.Asymm r] [IsOrderConnected α r]
 : IsStrictWeakOrder α r
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Std.Asymm.irrefl`：∀ {α : Sort u_1} {r : α → α → Prop} [Std.Asymm r], Std
.Irrefl r
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `IsOrderConnected.conn`：∀ {α : Type u} {lt : α → α → Prop} [self : IsOrde
rConnected α lt] (a b c : α), lt a c → lt a b ∨ lt b c
· 使用引理 `asymm`：asymm [Std.Asymm r] : a ≺ b -> ¬b ≺ a
· 使用定理 `IsOrderConnected.neg_trans`：IsOrderConnected.neg_trans {r : α -> α -> Pr
op} [IsOrderConnected α r] {a b c} (h₁ : ¬r a b) (h₂ : ¬r b c) : ¬r a c
-/
theorem isStrictWeakOrder_of_isOrderConnected [Std.Asymm r] [IsOrderConnected α r] :
    IsStrictWeakOrder α r :=
  { @Std.Asymm.irrefl α r _ with
    trans := fun _ _ c h₁ h₂ => (IsOrderConnected.conn _ c _ h₁).resolve_right (asymm h₂),
    incomp_trans := fun _ _ _ ⟨h₁, h₂⟩ ⟨h₃, h₄⟩ =>
      ⟨IsOrderConnected.neg_trans h₁ h₃, IsOrderConnected.neg_trans h₄ h₂⟩ }

-- see Note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) isStrictOrderConnected_of_isStrictTotalOrder [IsStrictTotalOrder α r] :
    IsOrderConnected α r :=
  ⟨fun _ _ _ h ↦ (trichotomous _ _).imp_right
    fun o ↦ o.elim (fun e ↦ e ▸ h) fun h' ↦ _root_.trans h' h⟩

/-! ### Inverse Image -/

/-
**InvImage.trichotomous** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：InvImage.trichotomous [Std.Trichotomous r] {f : β -> α} (h : Function.Inje
ctive f) : Std.Trichotomous (InvImage r f)
参数：h : Function.Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Std.Trichotomous.trichotomous`：∀ {α : Sort u} {r : α → α → Prop} [self :
 Std.Trichotomous r] (a b : α), ¬r a b → ¬r b a → a = b

--- 原说明 ---
### Inverse Image
-/
theorem InvImage.trichotomous [Std.Trichotomous r] {f : β → α} (h : Function.Injective f) :
    Std.Trichotomous (InvImage r f) :=
  ⟨fun {a b} hab hba ↦ h <| Std.Trichotomous.trichotomous (f a) (f b) hab hba⟩

@[deprecated (since := "2026-01-24")] alias InvImage.isTrichotomous := InvImage.trichotomous
/-
**InvImage.asymm** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：InvImage.asymm [Std.Asymm r] (f : β -> α) : Std.Asymm (InvImage r f) where
 asymm a b h h2
参数：f : β -> α。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Std.Asymm.asymm`：∀ {α : Sort u} {r : α → α → Prop} [self : Std.Asymm r] 
(a b : α), r a b → ¬r b a
-/
instance InvImage.asymm [Std.Asymm r] (f : β → α) : Std.Asymm (InvImage r f) where
  asymm a b h h2 := Std.Asymm.asymm (f a) (f b) h h2

/-! ### Well-order -/


/-- A well-founded relation. Not to be confused with `IsWellOrder`. -/
/-
**IsWellFounded** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u) → (α → α → Prop) → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A well-founded relation. Not to be confused with `IsWellOrder`.
-/
@[mk_iff] class IsWellFounded (α : Type u) (r : α → α → Prop) : Prop where
  /-- The relation is `WellFounded`, as a proposition. -/
  wf : WellFounded r
/-
**WellFoundedRelation.isWellFounded** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：WellFoundedRelation.isWellFounded [h : WellFoundedRelation α] : IsWellFoun
ded α WellFoundedRelation.rel
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `WellFoundedRelation.wf`：∀ {α : Sort u} [self : WellFoundedRelation α], W
ellFounded WellFoundedRelation.rel
-/
instance WellFoundedRelation.isWellFounded [h : WellFoundedRelation α] :
    IsWellFounded α WellFoundedRelation.rel :=
  { h with }
/-
**WellFoundedRelation.asymmetric** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：WellFoundedRelation.asymmetric {α : Sort*} [WellFoundedRelation α] {a b : 
α} : WellFoundedRelation.rel a b -> ¬ WellFoundedRelation.rel b a
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WellFoundedRelation.asymmetric._unary`：∀ {α : Sort u_1} [inst : WellFoun
dedRelation α]   (_x : (a : α) ×' (b : α) ×' (_ : WellFoundedRelation.rel a b) ×
' WellFoundedRelation.rel b…
-/
theorem WellFoundedRelation.asymmetric {α : Sort*} [WellFoundedRelation α] {a b : α} :
    WellFoundedRelation.rel a b → ¬ WellFoundedRelation.rel b a :=
  fun hab hba => WellFoundedRelation.asymmetric hba hab
termination_by a
/-
**WellFoundedRelation.asymmetric** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：WellFoundedRelation.asymmetric {α : Sort*} [WellFoundedRelation α] {a b : 
α} : WellFoundedRelation.rel a b -> ¬ WellFoundedRelation.rel b a
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WellFoundedRelation.asymmetric._unary`：∀ {α : Sort u_1} [inst : WellFoun
dedRelation α]   (_x : (a : α) ×' (b : α) ×' (_ : WellFoundedRelation.rel a b) ×
' WellFoundedRelation.rel b…
-/
theorem WellFoundedRelation.asymmetric₃ {α : Sort*} [WellFoundedRelation α] {a b c : α} :
    WellFoundedRelation.rel a b → WellFoundedRelation.rel b c → ¬ WellFoundedRelation.rel c a :=
  fun hab hbc hca => WellFoundedRelation.asymmetric₃ hca hab hbc
termination_by a
/-
**WellFounded.prod_lex** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：WellFounded.prod_lex {ra : α -> α -> Prop} {rb : β -> β -> Prop} (ha : Wel
lFounded ra) (hb : WellFounded rb) : WellFounded (Prod.Lex ra rb)
参数：ha : WellFounded ra；hb : WellFounded rb。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WellFoundedRelation.wf`：∀ {α : Sort u} [self : WellFoundedRelation α], W
ellFounded WellFoundedRelation.rel
-/
lemma WellFounded.prod_lex {ra : α → α → Prop} {rb : β → β → Prop} (ha : WellFounded ra)
    (hb : WellFounded rb) : WellFounded (Prod.Lex ra rb) :=
  (Prod.lex ⟨_, ha⟩ ⟨_, hb⟩).wf

section PSigma

open PSigma

/-- The lexicographical order of well-founded relations is well-founded. -/
/-
**WellFounded.psigma_lex** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：WellFounded.psigma_lex {α : Sort*} {β : α -> Sort*} {r : α -> α -> Prop} {
s : forall a : α, β a -> β a -> Prop} (ha : WellFounded r) (hb : forall x, WellF
ounded (s x)) : WellFounded (Lex r s)
参数：ha : WellFounded r；hb : forall x, WellFounded (s x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PSigma.lexAccessible`：∀ {α : Sort u} {β : α → Sort v} {r : α → α → Prop}
 {s : (a : α) → β a → β a → Prop} {a : α},   Acc r a → (∀ (a : α), WellFounded (
s a)) → ∀ …
· 使用定理 `WellFounded.apply`：∀ {α : Sort u} {r : α → α → Prop}, WellFounded r → ∀ 
(a : α), Acc r a

--- 原说明 ---
The lexicographical order of well-founded relations is well-founded.
-/
theorem WellFounded.psigma_lex
    {α : Sort*} {β : α → Sort*} {r : α → α → Prop} {s : ∀ a : α, β a → β a → Prop}
    (ha : WellFounded r) (hb : ∀ x, WellFounded (s x)) : WellFounded (Lex r s) :=
  WellFounded.intro fun ⟨a, b⟩ => lexAccessible (WellFounded.apply ha a) hb b
/-
**WellFounded.psigma_revLex** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：WellFounded.psigma_revLex {α : Sort*} {β : Sort*} {r : α -> α -> Prop} {s 
: β -> β -> Prop} (ha : WellFounded r) (hb : WellFounded s) : WellFounded (RevLe
x r s)
参数：ha : WellFounded r；hb : WellFounded s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PSigma.revLexAccessible`：∀ {α : Sort u} {β : Sort v} {r : α → α → Prop} 
{s : β → β → Prop} {b : β},   Acc s b → (∀ (a : α), Acc r a) → ∀ (a : α), Acc (P
Sigma.RevLex …
· 使用定理 `WellFounded.apply`：∀ {α : Sort u} {r : α → α → Prop}, WellFounded r → ∀ 
(a : α), Acc r a
-/
theorem WellFounded.psigma_revLex
    {α : Sort*} {β : Sort*} {r : α → α → Prop} {s : β → β → Prop}
    (ha : WellFounded r) (hb : WellFounded s) : WellFounded (RevLex r s) :=
  WellFounded.intro fun ⟨a, b⟩ => revLexAccessible (apply hb b) (WellFounded.apply ha) a
/-
**WellFounded.psigma_skipLeft** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：WellFounded.psigma_skipLeft (α : Type u) {β : Type v} {s : β -> β -> Prop}
 (hb : WellFounded s) : WellFounded (SkipLeft α s)
参数：α : Type u；hb : WellFounded s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WellFounded.psigma_revLex`：WellFounded.psigma_revLex {α : Sort*} {β : So
rt*} {r : α -> α -> Prop} {s : β -> β -> Prop} (ha : WellFounded r) (hb : WellFo
unded s) : Well…
· 使用定理 `WellFoundedRelation.wf`：∀ {α : Sort u} [self : WellFoundedRelation α], W
ellFounded WellFoundedRelation.rel
-/
theorem WellFounded.psigma_skipLeft (α : Type u) {β : Type v} {s : β → β → Prop}
    (hb : WellFounded s) : WellFounded (SkipLeft α s) :=
  psigma_revLex emptyWf.wf hb

end PSigma

namespace IsWellFounded

variable (r) [IsWellFounded α r]

/-- Induction on a well-founded relation. -/
/-
**IsWellFounded.induction** 是 Mathlib 中的一个定理，位于命名空间 `IsWellFounded`。
形式化陈述：induction {motive : α -> Prop} (a : α) (ind : forall x, (forall y, r y x -
> motive y) -> motive x) : motive a
参数：a : α；ind : forall x, (forall y, r y x -> motive y) -> motive x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WellFounded.induction`：∀ {α : Sort u} {r : α → α → Prop},   WellFounded 
r → ∀ {C : α → Prop} (a : α), (∀ (x : α), (∀ (y : α), r y x → C y) → C x) → C a
· 使用定理 `IsWellFounded.wf`：∀ {α : Type u} {r : α → α → Prop} [self : IsWellFounde
d α r], WellFounded r

--- 原说明 ---
Induction on a well-founded relation.
-/
theorem induction {motive : α → Prop} (a : α) (ind : ∀ x, (∀ y, r y x → motive y) → motive x) :
    motive a :=
  wf.induction _ ind

/-- All values are accessible under the well-founded relation. -/
/-
**IsWellFounded.apply** 是 Mathlib 中的一个定理，位于命名空间 `IsWellFounded`。
形式化陈述：apply : forall a, Acc r a
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WellFounded.apply`：∀ {α : Sort u} {r : α → α → Prop}, WellFounded r → ∀ 
(a : α), Acc r a
· 使用定理 `IsWellFounded.wf`：∀ {α : Type u} {r : α → α → Prop} [self : IsWellFounde
d α r], WellFounded r

--- 原说明 ---
All values are accessible under the well-founded relation.
-/
theorem apply : ∀ a, Acc r a :=
  wf.apply

/-- Creates data, given a way to generate a value from all that compare as less under a well-founded
relation. See also `IsWellFounded.fix_eq`. -/
/-
**IsWellFounded.fix** 是 Mathlib 中的一个定义，位于命名空间 `IsWellFounded`。
形式化陈述：fix {motive : α -> Sort*} : (ind : forall x : α, (forall y : α, r y x -> m
otive y) -> motive x) -> forall x : α, motive x
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsWellFounded.wf`：∀ {α : Type u} {r : α → α → Prop} [self : IsWellFounde
d α r], WellFounded r

--- 原说明 ---
Creates data, given a way to generate a value from all that compare as less unde
r a well-founded
relation. See also `IsWellFounded.fix_eq`.
-/
def fix {motive : α → Sort*} : (ind : ∀ x : α, (∀ y : α, r y x → motive y) → motive x) →
    ∀ x : α, motive x :=
  wf.fix

/-- The value from `IsWellFounded.fix` is built from the previous ones as specified. -/
/-
**IsWellFounded.fix_eq** 是 Mathlib 中的一个定理，位于命名空间 `IsWellFounded`。
形式化陈述：fix_eq {motive : α -> Sort*} (ind : forall x : α, (forall y : α, r y x -> 
motive y) -> motive x) : forall x, fix r ind x = ind x fun y _ => fix r ind y
参数：ind : forall x : α, (forall y : α, r y x -> motive y) -> motive x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WellFounded.fix_eq`：∀ {α : Sort u} {C : α → Sort v} {r : α → α → Prop} (
hwf : WellFounded r) (F : (x : α) → ((y : α) → r y x → C y) → C x)   (x : α), hw
f.fix F …
· 使用定理 `IsWellFounded.wf`：∀ {α : Type u} {r : α → α → Prop} [self : IsWellFounde
d α r], WellFounded r

--- 原说明 ---
The value from `IsWellFounded.fix` is built from the previous ones as specified.
-/
theorem fix_eq {motive : α → Sort*} (ind : ∀ x : α, (∀ y : α, r y x → motive y) → motive x) :
    ∀ x, fix r ind x = ind x fun y _ => fix r ind y :=
  wf.fix_eq ind

/-- Derive a `WellFoundedRelation` instance from an `isWellFounded` instance. -/
@[instance_reducible]
/-
**IsWellFounded.toWellFoundedRelation** 是 Mathlib 中的一个定义，位于命名空间 `IsWellFounded`。
形式化陈述：toWellFoundedRelation : WellFoundedRelation α
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsWellFounded.wf`：∀ {α : Type u} {r : α → α → Prop} [self : IsWellFounde
d α r], WellFounded r

--- 原说明 ---
Derive a `WellFoundedRelation` instance from an `isWellFounded` instance.
-/
def toWellFoundedRelation : WellFoundedRelation α :=
  ⟨r, IsWellFounded.wf⟩

end IsWellFounded

/-
**WellFounded.asymmetric** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：WellFounded.asymmetric {α : Sort*} {r : α -> α -> Prop} (h : WellFounded r
) (a b) : r a b -> ¬r b a
参数：h : WellFounded r；a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WellFoundedRelation.asymmetric`：WellFoundedRelation.asymmetric {α : Sort
*} [WellFoundedRelation α] {a b : α} : WellFoundedRelation.rel a b -> ¬ WellFoun
dedRelation.rel b a
-/
theorem WellFounded.asymmetric {α : Sort*} {r : α → α → Prop} (h : WellFounded r) (a b) :
    r a b → ¬r b a :=
  @WellFoundedRelation.asymmetric _ ⟨_, h⟩ _ _
/-
**WellFounded.asymmetric** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：WellFounded.asymmetric {α : Sort*} {r : α -> α -> Prop} (h : WellFounded r
) (a b) : r a b -> ¬r b a
参数：h : WellFounded r；a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WellFoundedRelation.asymmetric`：WellFoundedRelation.asymmetric {α : Sort
*} [WellFoundedRelation α] {a b : α} : WellFoundedRelation.rel a b -> ¬ WellFoun
dedRelation.rel b a
-/
theorem WellFounded.asymmetric₃ {α : Sort*} {r : α → α → Prop} (h : WellFounded r) (a b c) :
    r a b → r b c → ¬r c a :=
  @WellFoundedRelation.asymmetric₃ _ ⟨_, h⟩ _ _ _

-- see Note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) (r : α → α → Prop) [IsWellFounded α r] : Std.Asymm r :=
  ⟨IsWellFounded.wf.asymmetric⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (r : α → α → Prop) [i : IsWellFounded α r] : IsWellFounded α (Relation.TransGen r) :=
  ⟨i.wf.transGen⟩

/-- A class for a well-founded relation `<`. -/
@[to_dual /-- A class for a well-founded relation `>`. -/]
/-
**WellFoundedLT** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：WellFoundedLT (α : Type*) [LT α] : Prop
参数：α : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A class for a well-founded relation `<`.
-/
abbrev WellFoundedLT (α : Type*) [LT α] : Prop :=
  IsWellFounded α (· < ·)

@[to_dual wellFounded_gt]
/-
**wellFounded_lt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：wellFounded_lt [LT α] [WellFoundedLT α] : @WellFounded α (· < ·)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsWellFounded.wf`：∀ {α : Type u} {r : α → α → Prop} [self : IsWellFounde
d α r], WellFounded r
-/
lemma wellFounded_lt [LT α] [WellFoundedLT α] : @WellFounded α (· < ·) := IsWellFounded.wf

-- See note [lower instance priority]
@[to_dual]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) (α : Type*) [LT α] [h : WellFoundedLT α] : WellFoundedGT αᵒᵈ :=
  h

@[to_dual]
/-
**wellFoundedGT_dual_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：wellFoundedGT_dual_iff (α : Type*) [LT α] : WellFoundedGT αᵒᵈ ↔ WellFounde
dLT α
参数：α : Type*。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsWellFounded.wf`：∀ {α : Type u} {r : α → α → Prop} [self : IsWellFounde
d α r], WellFounded r
-/
theorem wellFoundedGT_dual_iff (α : Type*) [LT α] : WellFoundedGT αᵒᵈ ↔ WellFoundedLT α :=
  ⟨fun h => ⟨h.wf⟩, fun h => ⟨h.wf⟩⟩

/-- A well order is a well-founded linear order. -/
@[wikidata Q659746]
/-
**IsWellOrder** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u) → (α → α → Prop) → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A well order is a well-founded linear order.
-/
class IsWellOrder (α : Type u) (r : α → α → Prop) : Prop
    extends IsWellFounded α r, Std.Trichotomous r
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (r) [IsWellOrder α r] : IsTrans α r where
  trans a b c hab hbc := by
    rcases trichotomous_of r a c with (hac | rfl | hca)
    · exact hac
    · exact asymm_of r hab hbc |>.elim
    · exact IsWellFounded.wf.asymmetric₃ a b c hab hbc hca |>.elim

-- see Note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) {α} (r : α → α → Prop) [IsWellOrder α r] :
    IsStrictTotalOrder α r where

namespace WellFoundedLT

variable [LT α] [WellFoundedLT α]

/-- Inducts on a well-founded `<` relation. -/
@[to_dual /-- Inducts on a well-founded `>` relation. -/]
/-
**WellFoundedLT.induction** 是 Mathlib 中的一个定理，位于命名空间 `WellFoundedLT`。
形式化陈述：induction {motive : α -> Prop} (a : α) (ind : forall x, (forall y, y < x -
> motive y) -> motive x) : motive a
参数：a : α；ind : forall x, (forall y, y < x -> motive y) -> motive x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsWellFounded.induction`：induction {motive : α -> Prop} (a : α) (ind : f
orall x, (forall y, r y x -> motive y) -> motive x) : motive a

--- 原说明 ---
Inducts on a well-founded `<` relation.
-/
theorem induction {motive : α → Prop} (a : α)
    (ind : ∀ x, (∀ y, y < x → motive y) → motive x) : motive a :=
  IsWellFounded.induction _ _ ind

/-- All values are accessible under the well-founded `<`. -/
@[to_dual /-- All values are accessible under the well-founded `>`. -/]
/-
**WellFoundedLT.apply** 是 Mathlib 中的一个定理，位于命名空间 `WellFoundedLT`。
形式化陈述：apply : forall a : α, Acc (· < ·) a
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsWellFounded.apply`：apply : forall a, Acc r a

--- 原说明 ---
All values are accessible under the well-founded `<`.
-/
theorem apply : ∀ a : α, Acc (· < ·) a :=
  IsWellFounded.apply _

/-- Creates data, given a way to generate a value from all that compare as lesser. See also
`WellFoundedLT.fix_eq`. -/
@[to_dual /-- Creates data, given a way to generate a value from all that compare as greater.
See also `WellFoundedGT.fix_eq`. -/]
/-
**WellFoundedLT.fix** 是 Mathlib 中的一个定义，位于命名空间 `WellFoundedLT`。
形式化陈述：fix {motive : α -> Sort*} : (ind : forall x : α, (forall y : α, y < x -> m
otive y) -> motive x) -> forall x : α, motive x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def fix {motive : α → Sort*} : (ind : ∀ x : α, (∀ y : α, y < x → motive y) → motive x) →
    ∀ x : α, motive x :=
  IsWellFounded.fix (· < ·)

/-- The value from `WellFoundedLT.fix` is built from the previous ones as specified. -/
@[to_dual /-- The value from `WellFoundedGT.fix` is built from the successive ones as specified. -/]
/-
**WellFoundedLT.fix_eq** 是 Mathlib 中的一个定理，位于命名空间 `WellFoundedLT`。
形式化陈述：fix_eq {motive : α -> Sort*} (ind : forall x : α, (forall y : α, y < x -> 
motive y) -> motive x) : forall x, fix ind x = ind x fun y _ => fix ind y
参数：ind : forall x : α, (forall y : α, y < x -> motive y) -> motive x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsWellFounded.fix_eq`：fix_eq {motive : α -> Sort*} (ind : forall x : α, 
(forall y : α, r y x -> motive y) -> motive x) : forall x, fix r ind x = ind x f
un y _ => …

--- 原说明 ---
The value from `WellFoundedLT.fix` is built from the previous ones as specified.
-/
theorem fix_eq {motive : α → Sort*} (ind : ∀ x : α, (∀ y : α, y < x → motive y) → motive x) :
    ∀ x, fix ind x = ind x fun y _ => fix ind y :=
  IsWellFounded.fix_eq _ ind

/-- Derive a `WellFoundedRelation` instance from a `WellFoundedLT` instance. -/
@[to_dual (attr := instance_reducible)
  /-- Derive a `WellFoundedRelation` instance from a `WellFoundedGT` instance. -/]
/-
**WellFoundedLT.toWellFoundedRelation** 是 Mathlib 中的一个定义，位于命名空间 `WellFoundedLT`。
形式化陈述：toWellFoundedRelation : WellFoundedRelation α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def toWellFoundedRelation : WellFoundedRelation α :=
  IsWellFounded.toWellFoundedRelation (· < ·)

end WellFoundedLT

open scoped Classical in
/-- Construct a decidable linear order from a well-founded linear order. -/
@[instance_reducible]
/-
**IsWellOrder.linearOrder** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsWellOrder.linearOrder (r : α -> α -> Prop) [IsWellOrder α r] : LinearOrd
er α
参数：r : α -> α -> Prop。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instIsStrictTotalOrderOfIsWellOrder`：∀ {α : Type u_1} (r : α → α → Prop)
 [IsWellOrder α r], IsStrictTotalOrder α r

--- 原说明 ---
Construct a decidable linear order from a well-founded linear order.
-/
noncomputable def IsWellOrder.linearOrder (r : α → α → Prop) [IsWellOrder α r] : LinearOrder α :=
  linearOrderOfSTO r

/-- Derive a `WellFoundedRelation` instance from an `IsWellOrder` instance. -/
@[instance_reducible]
/-
**IsWellOrder.toHasWellFounded** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsWellOrder.toHasWellFounded [LT α] [hwo : IsWellOrder α (· < ·)] : WellFo
undedRelation α where rel
参数：· < ·。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Derive a `WellFoundedRelation` instance from an `IsWellOrder` instance.
-/
def IsWellOrder.toHasWellFounded [LT α] [hwo : IsWellOrder α (· < ·)] : WellFoundedRelation α where
  rel := (· < ·)
  wf := hwo.wf

-- This isn't made into an instance as it loops with `Std.Irrefl r`.
/-
**Subsingleton.isWellOrder** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subsingleton.isWellOrder [Subsingleton α] (r : α -> α -> Prop) [Std.Irrefl
 r] : IsWellOrder α r where .elim⟩ wf
参数：r : α -> α -> Prop。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_rel_of_subsingleton`：not_rel_of_subsingleton (r : α -> α -> Prop) [S
td.Irrefl r] [Subsingleton α] (x y) : ¬r x y
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
theorem Subsingleton.isWellOrder [Subsingleton α] (r : α → α → Prop) [Std.Irrefl r] :
    IsWellOrder α r where
  wf := .intro fun a ↦ ⟨_, fun y h ↦ not_rel_of_subsingleton r y a h |>.elim⟩
  trichotomous a b _ _ := Subsingleton.elim a b
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Subsingleton α] : IsWellOrder α emptyRelation :=
  Subsingleton.isWellOrder _
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) [IsEmpty α] (r : α → α → Prop) : IsWellOrder α r where
  wf := wellFounded_of_isEmpty r
  trichotomous := isEmptyElim
/-
**Prod.Lex.instIsWellFounded** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Prod.Lex.instIsWellFounded [IsWellFounded α r] [IsWellFounded β s] : IsWel
lFounded (α × β) (Prod.Lex r s)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `WellFounded.prod_lex`：WellFounded.prod_lex {ra : α -> α -> Prop} {rb : β
 -> β -> Prop} (ha : WellFounded ra) (hb : WellFounded rb) : WellFounded (Prod.L
ex ra rb)
· 使用定理 `IsWellFounded.wf`：∀ {α : Type u} {r : α → α → Prop} [self : IsWellFounde
d α r], WellFounded r
-/
instance Prod.Lex.instIsWellFounded [IsWellFounded α r] [IsWellFounded β s] :
    IsWellFounded (α × β) (Prod.Lex r s) :=
  ⟨IsWellFounded.wf.prod_lex IsWellFounded.wf⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsWellOrder α r] [IsWellOrder β s] : IsWellOrder (α × β) (Prod.Lex r s) where
  trichotomous := fun ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ hab hba ↦ by
    obtain rfl := Std.Trichotomous.trichotomous a₁ b₁
      (mt (Prod.Lex.left a₂ b₂) hab) (mt (Prod.Lex.left b₂ a₂) hba)
    obtain rfl := Std.Trichotomous.trichotomous a₂ b₂
      (mt (Prod.Lex.right a₁) hab) (mt (Prod.Lex.right a₁) hba)
    rfl
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (r : α → α → Prop) [IsWellFounded α r] (f : β → α) : IsWellFounded _ (InvImage r f) :=
  ⟨InvImage.wf f IsWellFounded.wf⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (f : α → ℕ) : IsWellFounded _ (InvImage (· < ·) f) :=
  ⟨(measure f).wf⟩
/-
**Subrelation.isWellFounded** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subrelation.isWellFounded (r : α -> α -> Prop) [IsWellFounded α r] {s : α 
-> α -> Prop} (h : Subrelation s r) : IsWellFounded α s
参数：r : α -> α -> Prop；h : Subrelation s r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subrelation.wf`：∀ {α : Sort u} {r q : α → α → Prop}, Subrelation q r → W
ellFounded r → WellFounded q
· 使用定理 `IsWellFounded.wf`：∀ {α : Type u} {r : α → α → Prop} [self : IsWellFounde
d α r], WellFounded r
-/
theorem Subrelation.isWellFounded (r : α → α → Prop) [IsWellFounded α r] {s : α → α → Prop}
    (h : Subrelation s r) : IsWellFounded α s :=
  ⟨h.wf IsWellFounded.wf⟩

@[to_dual]
/-
**Prod.wellFoundedLT** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Prod.wellFoundedLT [Preorder α] [WellFoundedLT α] [Preorder β] [WellFounde
dLT β] : WellFoundedLT (α × β) where wf
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `WellFoundedLT.induction`：induction {motive : α -> Prop} (a : α) (ind : f
orall x, (forall y, y < x -> motive y) -> motive x) : motive a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Prod.lt_iff`：lt_iff : x < y ↔ x.1 < y.1 ∧ x.2 <= y.2 ∨ x.1 <= y.1 ∧ x.2 
< y.2
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
instance Prod.wellFoundedLT [Preorder α] [WellFoundedLT α] [Preorder β] [WellFoundedLT β] :
    WellFoundedLT (α × β) where
  wf := by
    suffices h : ∀ a, ∀ a' ≤ a, ∀ b, Acc (· < ·) (a', b) from ⟨fun x => h x.1 x.1 le_rfl x.2⟩
    intro a a' ha b
    induction a using WellFoundedLT.induction generalizing a' b with | ind a iha
    induction b using WellFoundedLT.induction generalizing a' with | ind b ihb
    refine Acc.intro (a', b) fun x hx => ?_
    obtain ⟨ha', hb⟩ | ⟨ha', hb⟩ := Prod.lt_iff.1 hx
    · exact iha x.1 (ha'.trans_le ha) x.1 le_rfl x.2
    · exact ihb x.2 hb x.1 (ha'.trans ha)

@[deprecated (since := "2026-01-12")] alias Prod.wellFoundedLT' := Prod.wellFoundedLT
@[deprecated (since := "2026-01-12")] alias Prod.wellFoundedGT' := Prod.wellFoundedGT

namespace Set

/-- An unbounded or cofinal set. -/
/-
**Set.Unbounded** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：Unbounded (r : α -> α -> Prop) (s : Set α) : Prop
参数：r : α -> α -> Prop；s : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An unbounded or cofinal set.
-/
def Unbounded (r : α → α → Prop) (s : Set α) : Prop :=
  ∀ a, ∃ b ∈ s, ¬r b a

/-- A bounded or final set. Not to be confused with `Bornology.IsBounded`. -/
/-
**Set.Bounded** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：Bounded (r : α -> α -> Prop) (s : Set α) : Prop
参数：r : α -> α -> Prop；s : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A bounded or final set. Not to be confused with `Bornology.IsBounded`.
-/
def Bounded (r : α → α → Prop) (s : Set α) : Prop :=
  ∃ a, ∀ b ∈ s, r b a

@[simp]
/-
**Set.not_bounded_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：not_bounded_iff {r : α -> α -> Prop} (s : Set α) : ¬Bounded r s ↔ Unbounde
d r s
参数：s : Set α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem not_bounded_iff {r : α → α → Prop} (s : Set α) : ¬Bounded r s ↔ Unbounded r s := by
  simp only [Bounded, Unbounded, not_forall, not_exists, exists_prop]

@[simp]
/-
**Set.not_unbounded_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：not_unbounded_iff {r : α -> α -> Prop} (s : Set α) : ¬Unbounded r s ↔ Boun
ded r s
参数：s : Set α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_iff_comm`：not_iff_comm : (¬a ↔ b) ↔ (¬b ↔ a)
· 使用定理 `Set.not_bounded_iff`：not_bounded_iff {r : α -> α -> Prop} (s : Set α) : 
¬Bounded r s ↔ Unbounded r s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem not_unbounded_iff {r : α → α → Prop} (s : Set α) : ¬Unbounded r s ↔ Bounded r s := by
  rw [not_iff_comm, not_bounded_iff]
/-
**Set.unbounded_of_isEmpty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：unbounded_of_isEmpty [IsEmpty α] {r : α -> α -> Prop} (s : Set α) : Unboun
ded r s
参数：s : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem unbounded_of_isEmpty [IsEmpty α] {r : α → α → Prop} (s : Set α) : Unbounded r s :=
  isEmptyElim

end Set

namespace Order.Preimage

/-
**Order.Preimage.instRefl** 是 Mathlib 中的一个实例，位于命名空间 `Order.Preimage`。
形式化陈述：instRefl [Std.Refl r] {f : β -> α} : Std.Refl (f ⁻¹'o r)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `refl_of`：∀ {α : Sort u_1} (r : α → α → Prop) [Std.Refl r] (a : α), r a a
-/
instance instRefl [Std.Refl r] {f : β → α} : Std.Refl (f ⁻¹'o r) :=
  ⟨fun _ => refl_of r _⟩
/-
**Order.Preimage.instIrrefl** 是 Mathlib 中的一个实例，位于命名空间 `Order.Preimage`。
形式化陈述：instIrrefl [Std.Irrefl r] {f : β -> α} : Std.Irrefl (f ⁻¹'o r)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `irrefl_of`：∀ {α : Sort u_1} (r : α → α → Prop) [Std.Irrefl r] (a : α), ¬
r a a
-/
instance instIrrefl [Std.Irrefl r] {f : β → α} : Std.Irrefl (f ⁻¹'o r) :=
  ⟨fun _ => irrefl_of r _⟩
/-
**Order.Preimage.instIsSymm** 是 Mathlib 中的一个实例，位于命名空间 `Order.Preimage`。
形式化陈述：instIsSymm [Std.Symm r] {f : β -> α} : Std.Symm (f ⁻¹'o r)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `symm_of`：∀ {α : Sort u_1} (r : α → α → Prop) {a b : α} [Std.Symm r], r a
 b → r b a
-/
instance instIsSymm [Std.Symm r] {f : β → α} : Std.Symm (f ⁻¹'o r) :=
  ⟨fun _ _ ↦ symm_of r⟩
/-
**Order.Preimage.instAsymm** 是 Mathlib 中的一个实例，位于命名空间 `Order.Preimage`。
形式化陈述：instAsymm [Std.Asymm r] {f : β -> α} : Std.Asymm (f ⁻¹'o r)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `asymm_of`：∀ {α : Sort u_1} (r : α → α → Prop) {a b : α} [Std.Asymm r], r
 a b → ¬r b a
-/
instance instAsymm [Std.Asymm r] {f : β → α} : Std.Asymm (f ⁻¹'o r) :=
  ⟨fun _ _ ↦ asymm_of r⟩
/-
**Order.Preimage.instIsTrans** 是 Mathlib 中的一个实例，位于命名空间 `Order.Preimage`。
形式化陈述：instIsTrans [IsTrans α r] {f : β -> α} : IsTrans β (f ⁻¹'o r)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `trans_of`：∀ {α : Sort u_1} (r : α → α → Prop) {a b c : α} [IsTrans α r],
 r a b → r b c → r a c
-/
instance instIsTrans [IsTrans α r] {f : β → α} : IsTrans β (f ⁻¹'o r) :=
  ⟨fun _ _ _ => trans_of r⟩
/-
**Order.Preimage.instIsPreorder** 是 Mathlib 中的一个定理，位于命名空间 `Order.Preimage`。
形式化陈述：∀ {α : Type u} {β : Type v} {r : α → α → Prop} [IsPreorder α r] {f : β → α
}, IsPreorder β (f ⁻¹'o r)
参数：f ⁻¹'o r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPreorder.toRefl`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsPreorde
r α r], Std.Refl r
· 使用定理 `IsPreorder.toIsTrans`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsPreo
rder α r], IsTrans α r
-/
instance instIsPreorder [IsPreorder α r] {f : β → α} : IsPreorder β (f ⁻¹'o r) where
/-
**Order.Preimage.instIsStrictOrder** 是 Mathlib 中的一个定理，位于命名空间 `Order.Preimage`。
形式化陈述：∀ {α : Type u} {β : Type v} {r : α → α → Prop} [IsStrictOrder α r] {f : β 
→ α}, IsStrictOrder β (f ⁻¹'o r)
参数：f ⁻¹'o r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrder.toIrrefl`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsSt
rictOrder α r], Std.Irrefl r
· 使用定理 `IsStrictOrder.toIsTrans`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsS
trictOrder α r], IsTrans α r
-/
instance instIsStrictOrder [IsStrictOrder α r] {f : β → α} : IsStrictOrder β (f ⁻¹'o r) where
/-
**Order.Preimage.instIsStrictWeakOrder** 是 Mathlib 中的一个实例，位于命名空间 `Order.Preimage
`。
形式化陈述：instIsStrictWeakOrder [IsStrictWeakOrder α r] {f : β -> α} : IsStrictWeakO
rder β (f ⁻¹'o r) where incomp_trans _ _ _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.Preimage.instIsStrictOrder`：∀ {α : Type u} {β : Type v} {r : α → α
 → Prop} [IsStrictOrder α r] {f : β → α}, IsStrictOrder β (f ⁻¹'o r)
· 使用定理 `IsStrictWeakOrder.toIsStrictOrder`：∀ {α : Sort u_1} {lt : α → α → Prop} 
[self : IsStrictWeakOrder α lt], IsStrictOrder α lt
· 使用定理 `IsStrictWeakOrder.incomp_trans`：∀ {α : Sort u_1} {lt : α → α → Prop} [se
lf : IsStrictWeakOrder α lt] (a b c : α),   ¬lt a b ∧ ¬lt b a → ¬lt b c ∧ ¬lt c 
b → ¬lt a c ∧ ¬lt c …
-/
instance instIsStrictWeakOrder [IsStrictWeakOrder α r] {f : β → α} :
    IsStrictWeakOrder β (f ⁻¹'o r) where
  incomp_trans _ _ _ := IsStrictWeakOrder.incomp_trans (lt := r) _ _ _
/-
**Order.Preimage.instIsEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Order.Preimage`。
形式化陈述：∀ {α : Type u} {β : Type v} {r : α → α → Prop} [IsEquiv α r] {f : β → α}, 
IsEquiv β (f ⁻¹'o r)
参数：f ⁻¹'o r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.Preimage.instIsPreorder`：∀ {α : Type u} {β : Type v} {r : α → α → 
Prop} [IsPreorder α r] {f : β → α}, IsPreorder β (f ⁻¹'o r)
· 使用定理 `IsEquiv.toIsPreorder`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsEqui
v α r], IsPreorder α r
· 使用定理 `IsEquiv.toSymm`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsEquiv α r]
, Std.Symm r
-/
instance instIsEquiv [IsEquiv α r] {f : β → α} : IsEquiv β (f ⁻¹'o r) where
/-
**Order.Preimage.instTotal** 是 Mathlib 中的一个实例，位于命名空间 `Order.Preimage`。
形式化陈述：instTotal [Std.Total r] {f : β -> α} : Std.Total (f ⁻¹'o r)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `total_of`：total_of [Std.Total r] (a b : α) : a ≺ b ∨ b ≺ a
-/
instance instTotal [Std.Total r] {f : β → α} : Std.Total (f ⁻¹'o r) :=
  ⟨fun _ _ => total_of r _ _⟩
/-
**Order.Preimage.antisymm** 是 Mathlib 中的一个定理，位于命名空间 `Order.Preimage`。
形式化陈述：antisymm [Std.Antisymm r] {f : β -> α} (hf : f.Injective) : Std.Antisymm (
f ⁻¹'o r)
参数：hf : f.Injective。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `antisymm_of`：antisymm_of (r : α -> α -> Prop) [Std.Antisymm r] {a b : α}
 : r a b -> r b a -> a = b
-/
theorem antisymm [Std.Antisymm r] {f : β → α} (hf : f.Injective) : Std.Antisymm (f ⁻¹'o r) :=
  ⟨fun _ _ h₁ h₂ ↦ hf <| antisymm_of r h₁ h₂⟩

@[deprecated (since := "2026-01-06")] alias isAntisymm := antisymm

end Order.Preimage

/-! ### Strict-non strict relations -/


/-- An unbundled relation class stating that `r` is the nonstrict relation corresponding to the
strict relation `s`. Compare `lt_iff_le_not_ge`. This is mostly meant to provide dot
notation on `(⊆)` and `(⊂)`. -/
/-
**IsNonstrictStrictOrder** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_1) → semiOutParam (α → α → Prop) → (α → α → Prop) → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An unbundled relation class stating that `r` is the nonstrict relation correspon
ding to the
strict relation `s`. Compare `lt_iff_le_not_ge`. This is mostly meant to provide
 dot
notation on `(⊆)` and `(⊂)`.
-/
class IsNonstrictStrictOrder (α : Type*) (r : semiOutParam (α → α → Prop)) (s : α → α → Prop) :
    Prop where
  /-- The relation `r` is the nonstrict relation corresponding to the strict relation `s`. -/
  right_iff_left_not_left (a b : α) : s a b ↔ r a b ∧ ¬r b a
/-
**right_iff_left_not_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：right_iff_left_not_left {r s : α -> α -> Prop} [IsNonstrictStrictOrder α r
 s] {a b : α} : s a b ↔ r a b ∧ ¬r b a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsNonstrictStrictOrder.right_iff_left_not_left`：∀ {α : Type u_1} {r : se
miOutParam (α → α → Prop)} {s : α → α → Prop} [self : IsNonstrictStrictOrder α r
 s] (a b : α),   s a b ↔ r a b ∧ ¬r …
-/
theorem right_iff_left_not_left {r s : α → α → Prop} [IsNonstrictStrictOrder α r s] {a b : α} :
    s a b ↔ r a b ∧ ¬r b a :=
  IsNonstrictStrictOrder.right_iff_left_not_left _ _

/-- A version of `right_iff_left_not_left` with explicit `r` and `s`. -/
/-
**right_iff_left_not_left_of** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：right_iff_left_not_left_of (r s : α -> α -> Prop) [IsNonstrictStrictOrder 
α r s] {a b : α} : s a b ↔ r a b ∧ ¬r b a
参数：r s : α -> α -> Prop。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `right_iff_left_not_left`：right_iff_left_not_left {r s : α -> α -> Prop} 
[IsNonstrictStrictOrder α r s] {a b : α} : s a b ↔ r a b ∧ ¬r b a

--- 原说明 ---
A version of `right_iff_left_not_left` with explicit `r` and `s`.
-/
theorem right_iff_left_not_left_of (r s : α → α → Prop) [IsNonstrictStrictOrder α r s] {a b : α} :
    s a b ↔ r a b ∧ ¬r b a :=
  right_iff_left_not_left
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {s : α → α → Prop} [IsNonstrictStrictOrder α r s] : Std.Irrefl s :=
  ⟨fun _ h => ((right_iff_left_not_left_of r s).1 h).2 ((right_iff_left_not_left_of r s).1 h).1⟩

/-! #### `⊆` and `⊂` -/

section Subset

attribute [to_set_notation]
  le_of_eq_of_le le_of_le_of_eq le_refl le_rfl le_of_eq ge_of_eq ne_of_not_le ne_of_not_ge
  le_trans le_antisymm ge_antisymm Eq.trans_le Eq.le Eq.ge le_antisymm_iff ge_antisymm_iff

@[deprecated (since := "2026-05-24")] alias HasSubset.subset.trans_eq := LE.le.trans_eq

@[deprecated (since := "2026-01-24")] alias Eq.subset' := Eq.subset

@[deprecated LE.le.trans (since := "2026-05-24")]
alias HasSubset.Subset.trans := subset_trans

@[deprecated LE.le.antisymm (since := "2026-05-24")]
alias HasSubset.Subset.antisymm := subset_antisymm

@[deprecated LE.le.antisymm' (since := "2026-05-24")]
alias HasSubset.Subset.antisymm' := superset_antisymm

end Subset

section SSubset

attribute [to_set_notation]
  lt_of_eq_of_lt lt_of_lt_of_eq lt_irrefl ne_of_lt ne_of_gt lt_trans lt_asymm Eq.trans_lt

@[deprecated (since := "2026-06-11")] alias ssubset_irrfl := ssubset_irrefl

@[deprecated (since := "2026-05-24")] alias HasSSubset.SSubset.trans_eq := LT.lt.trans_eq

@[deprecated (since := "2026-05-24")] alias HasSSubset.SSubset.false := LT.lt.false

@[deprecated (since := "2026-05-24")] alias HasSSubset.SSubset.ne := LT.lt.ne

@[deprecated (since := "2026-05-24")] alias HasSSubset.SSubset.ne' := LT.lt.ne'

@[deprecated (since := "2026-05-24")] alias HasSSubset.SSubset.trans := LT.lt.trans

@[deprecated (since := "2026-05-24")] alias HasSSubset.SSubset.asymm := LT.lt.asymm

end SSubset

section SubsetSSubset

attribute [to_set_notation] lt_iff_le_not_ge le_of_lt
  not_le_of_gt not_lt_of_ge lt_of_le_not_ge
  LT.lt.le LT.lt.not_ge LE.le.not_gt LE.le.lt_of_not_ge
  lt_of_le_of_lt lt_of_lt_of_le lt_of_le_of_ne lt_of_ne_of_le eq_or_lt_of_le lt_or_eq_of_le
  eq_of_le_of_not_lt eq_of_le_of_not_lt'
  LE.le.trans_lt LT.lt.trans_le LE.le.lt_of_ne Ne.lt_of_le
  LE.le.eq_or_lt LE.le.lt_or_eq
  LE.le.eq_of_not_lt LE.le.eq_of_not_lt'
  lt_iff_le_and_ne le_iff_lt_or_eq

-- TODO: deprecate these aliases
alias ssubset_iff_subset_not_subset := ssubset_iff_subset_not_superset
alias not_subset_of_ssubset := not_subset_of_ssuperset
alias not_ssubset_of_subset := not_ssubset_of_superset
alias ssubset_of_subset_not_subset := ssubset_of_subset_not_superset
alias LT.lt.not_subset := LT.lt.not_superset
alias LE.le.not_ssubset := LE.le.not_ssuperset
alias LE.le.ssubset_of_not_subset := LE.le.ssubset_of_not_superset

@[deprecated (since := "2026-05-24")] alias HasSSubset.SSubset.subset := LT.lt.subset
@[deprecated (since := "2026-05-24")] alias HasSSubset.SSubset.not_subset := LT.lt.not_superset
@[deprecated (since := "2026-05-24")] alias HasSubset.Subset.not_ssubset := LE.le.not_ssuperset
@[deprecated (since := "2026-05-24")]
alias HasSubset.Subset.ssubset_of_not_subset := LE.le.ssubset_of_not_superset

alias eq_of_superset_of_not_ssuperset := eq_of_subset_of_not_ssubset'
alias LE.le.eq_of_not_ssuperset := LE.le.eq_of_not_ssubset'

@[deprecated (since := "2026-05-24")]
alias HasSubset.Subset.trans_ssubset := LE.le.trans_ssubset
@[deprecated (since := "2026-05-24")]
alias HasSSubset.SSubset.trans_subset := LT.lt.trans_subset
@[deprecated (since := "2026-05-24")]
alias HasSubset.Subset.ssubset_of_ne := LE.le.ssubset_of_ne
@[deprecated (since := "2026-05-24")]
alias HasSubset.Subset.eq_or_ssubset := LE.le.eq_or_ssubset
@[deprecated (since := "2026-05-24")]
alias HasSubset.Subset.ssubset_or_eq := LE.le.ssubset_or_eq
@[deprecated (since := "2026-05-24")]
alias HasSubset.Subset.eq_of_not_ssubset := LE.le.eq_of_not_ssubset
@[deprecated (since := "2026-05-24")]
alias HasSubset.Subset.eq_of_not_ssuperset := LE.le.eq_of_not_ssuperset

-- TODO: deprecate
alias ssubset_iff_subset_ne := ssubset_iff_subset_and_ne

end SubsetSSubset

/-! ### Conversion of bundled order typeclasses to unbundled relation typeclasses -/


@[to_dual instReflGe]
/-
**instReflLe** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：instReflLe [Preorder α] : @Std.Refl α (· <= ·)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a

--- 原说明 ---
### Conversion of bundled order typeclasses to unbundled relation typeclasses
-/
instance instReflLe [Preorder α] : @Std.Refl α (· ≤ ·) :=
  ⟨le_refl⟩

/-- A version of `Std.le_refl` that works with `Std.Refl (· ≥ ·)`.
This is needed for `to_dual` translations because `Std.le_refl` requires `Std.Refl (· ≤ ·)`,
but after translation `instReflLe` becomes `instReflGe : Std.Refl (· ≥ ·)`. -/
/-
**Std.ge_refl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Std.ge_refl {α : Type*} [LE α] [inst : @Std.Refl α (· >= ·)] (a : α) : a <
= a
参数：· >= ·；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Std.Refl.refl`：∀ {α : Sort u} {r : α → α → Prop} [self : Std.Refl r] (a 
: α), r a a

--- 原说明 ---
A version of `Std.le_refl` that works with `Std.Refl (· ≥ ·)`.
This is needed for `to_dual` translations because `Std.le_refl` requires `Std.Re
fl (· ≤ ·)`,
but after translation `instReflLe` becomes `instReflGe : Std.Refl (· ≥ ·)`.
-/
theorem Std.ge_refl {α : Type*} [LE α] [inst : @Std.Refl α (· ≥ ·)] (a : α) : a ≤ a :=
  @Std.Refl.refl α (· ≥ ·) inst a

attribute [to_dual existing Std.ge_refl] Std.le_refl

@[to_dual instIsTransGe]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Preorder α] : IsTrans α (· ≤ ·) :=
  ⟨@le_trans _ _⟩

@[to_dual instIsPreorderGe]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Preorder α] : IsPreorder α (· ≤ ·) where

@[to_dual instIrreflGt]
/-
**instIrreflLt** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：instIrreflLt [Preorder α] : @Std.Irrefl α (· < ·)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
-/
instance instIrreflLt [Preorder α] : @Std.Irrefl α (· < ·) :=
  ⟨lt_irrefl⟩

@[to_dual instIsTransGt]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Preorder α] : IsTrans α (· < ·) :=
  ⟨@lt_trans _ _⟩

@[to_dual instAsymmGt]
/-
**instAsymmLt** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：instAsymmLt [Preorder α] : Std.Asymm (α
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_asymm`：lt_asymm (h : a < b) : ¬b < a
-/
instance instAsymmLt [Preorder α] : Std.Asymm (α := α) (· < ·) :=
  ⟨@lt_asymm _ _⟩

@[to_dual instAntisymmGt]
/-
**instAntisymmLt** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：instAntisymmLt [Preorder α] : @Std.Antisymm α (· < ·)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Std.Asymm.antisymm`：∀ {α : Sort u_1} (r : α → α → Prop) [Std.Asymm r], S
td.Antisymm r
-/
instance instAntisymmLt [Preorder α] : @Std.Antisymm α (· < ·) :=
  Std.Asymm.antisymm _

@[to_dual instIsStrictOrderGt]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Preorder α] : IsStrictOrder α (· < ·) where

@[to_dual instIsNonstrictStrictOrderGeGt]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Preorder α] : IsNonstrictStrictOrder α (· ≤ ·) (· < ·) :=
  ⟨@lt_iff_le_not_ge _ _⟩

@[to_dual instAntisymmGe]
/-
**instAntisymmLe** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：instAntisymmLe [PartialOrder α] : @Std.Antisymm α (· <= ·)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
-/
instance instAntisymmLe [PartialOrder α] : @Std.Antisymm α (· ≤ ·) :=
  ⟨@le_antisymm _ _⟩

@[to_dual instIsPartialOrderGe]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [PartialOrder α] : IsPartialOrder α (· ≤ ·) where

@[to_dual total']
/-
**LE.total** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：LE.total [LinearOrder α] : @Std.Total α (· <= ·)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
-/
instance LE.total [LinearOrder α] : @Std.Total α (· ≤ ·) :=
  ⟨le_total⟩

@[to_dual instIsLinearOrderGe]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [LinearOrder α] : IsLinearOrder α (· ≤ ·) where

@[to_dual instTrichotomousGt]
/-
**instTrichotomousLt** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：instTrichotomousLt [LinearOrder α] : @Std.Trichotomous α (· < ·)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instTrichotomousLt [LinearOrder α] : @Std.Trichotomous α (· < ·) :=
  ⟨by grind⟩

@[to_dual instTrichotomousGe]
/-
**instTrichotomousLe** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：instTrichotomousLe [LinearOrder α] : @Std.Trichotomous α (· <= ·)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Std.instTrichotomousOfTotal`：∀ {α : Sort u_1} (r : α → α → Prop) [Std.To
tal r], Std.Trichotomous r
-/
instance instTrichotomousLe [LinearOrder α] : @Std.Trichotomous α (· ≤ ·) :=
  inferInstance

@[to_dual instIsStrictTotalOrderGt]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [LinearOrder α] : IsStrictTotalOrder α (· < ·) where

@[to_dual isTrans_ge]
/-
**isTrans_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isTrans_le [Preorder α] : IsTrans α LE.le
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTransLe`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x1 ≤ x2
-/
theorem isTrans_le [Preorder α] : IsTrans α LE.le :=
  inferInstance

@[deprecated (since := "2026-02-21")]
alias transitive_ge := isTrans_ge
@[to_dual existing transitive_ge, deprecated (since := "2026-02-21")]
alias transitive_le := isTrans_le

@[to_dual isTrans_gt]
/-
**isTrans_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isTrans_lt [Preorder α] : IsTrans α LT.lt
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTransLt`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x1 < x2
-/
theorem isTrans_lt [Preorder α] : IsTrans α LT.lt :=
  inferInstance

@[deprecated (since := "2026-02-21")]
alias transitive_gt := isTrans_gt
@[to_dual existing transitive_gt, deprecated (since := "2026-02-21")]
alias transitive_lt := isTrans_lt

@[to_dual total_ge]
/-
**OrderDual.total_le** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：OrderDual.total_le [LE α] [h : @Std.Total α (· <= ·)] : @Std.Total αᵒᵈ (· 
<= ·)
参数：· <= ·。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance OrderDual.total_le [LE α] [h : @Std.Total α (· ≤ ·)] : @Std.Total αᵒᵈ (· ≤ ·) :=
  inferInstanceAs <| @Std.Total α <| swap (· ≤ ·)
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : WellFoundedLT ℕ :=
  ⟨Nat.lt_wfRel.wf⟩

@[to_dual isWellOrder_gt]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) isWellOrder_lt [LinearOrder α] [WellFoundedLT α] :
    IsWellOrder α (· < ·) where
