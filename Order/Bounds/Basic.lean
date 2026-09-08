/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov
-/
module

public import Mathlib.Order.Antisymmetrization
public import Mathlib.Order.Bounds.Defs
public import Mathlib.Order.Directed
public import Mathlib.Order.BoundedOrder.Monotone
public import Mathlib.Order.Interval.Set.Basic

/-!
# Upper / lower bounds

In this file we prove various lemmas about upper/lower bounds of a set:
monotonicity, behaviour under `∪`, `∩`, `insert`,
and provide formulas for `∅`, `univ`, and intervals.
-/

@[expose] public section

open Function Set

open OrderDual (toDual ofDual)

variable {α β γ : Type*}

section

variable [Preorder α] {s t u : Set α} {a b : α}

@[to_dual]
/-
**mem_upperBounds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_upperBounds : a in upperBounds s ↔ forall x in s, x <= a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_upperBounds : a ∈ upperBounds s ↔ ∀ x ∈ s, x ≤ a :=
  Iff.rfl

@[to_dual]
/-
**mem_upperBounds_iff_subset_Iic** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mem_upperBounds_iff_subset_Iic : a in upperBounds s ↔ s subseteq Iic a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_upperBounds_iff_subset_Iic : a ∈ upperBounds s ↔ s ⊆ Iic a := Iff.rfl

@[to_dual]
/-
**bddAbove_def** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：bddAbove_def : BddAbove s ↔ exists x, forall y in s, y <= x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem bddAbove_def : BddAbove s ↔ ∃ x, ∀ y ∈ s, y ≤ x :=
  Iff.rfl

@[to_dual]
/-
**top_mem_upperBounds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：top_mem_upperBounds [OrderTop α] (s : Set α) : ⊤ in upperBounds s
参数：s : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_top`：le_top : a <= ⊤
-/
theorem top_mem_upperBounds [OrderTop α] (s : Set α) : ⊤ ∈ upperBounds s := fun _ _ => le_top

@[to_dual (attr := simp)]
/-
**isLeast_bot_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLeast_bot_iff [OrderBot α] : IsLeast s ⊥ ↔ ⊥ in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `and_iff_left`：∀ {b a : Prop}, b → (a ∧ b ↔ a)
· 使用定理 `bot_mem_lowerBounds`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : Orde
rBot α] (s : Set α), ⊥ ∈ lowerBounds s
-/
theorem isLeast_bot_iff [OrderBot α] : IsLeast s ⊥ ↔ ⊥ ∈ s :=
  and_iff_left <| bot_mem_lowerBounds _

/-- A set `s` is not bounded above if and only if for each `x` there exists `y ∈ s` such that `x`
is not greater than or equal to `y`. This version only assumes `Preorder` structure and uses
`¬(y ≤ x)`. A version for linear orders is called `not_bddAbove_iff`. -/
@[to_dual
/-- A set `s` is not bounded below if and only if for each `x` there exists `y ∈ s` such that `x`
is not less than or equal to `y`. This version only assumes `Preorder` structure and uses
`¬(x ≤ y)`. A version for linear orders is called `not_bddBelow_iff`. -/]
/-
**not_bddAbove_iff'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_bddAbove_iff' : ¬BddAbove s ↔ forall x, exists y in s, ¬y <= x
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
theorem not_bddAbove_iff' : ¬BddAbove s ↔ ∀ x, ∃ y ∈ s, ¬y ≤ x := by
  simp [BddAbove, upperBounds, Set.Nonempty]

/-- A set `s` is not bounded above if and only if for each `x` there exists `y ∈ s` that is greater
than `x`. A version for preorders is called `not_bddAbove_iff'`. -/
@[to_dual
/-- A set `s` is not bounded below if and only if for each `x` there exists `y ∈ s` that is less
than `x`. A version for preorders is called `not_bddBelow_iff'`. -/]
/-
**not_bddAbove_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_bddAbove_iff {α : Type*} [LinearOrder α] {s : Set α} : ¬BddAbove s ↔ f
orall x, exists y in s, x < y
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
theorem not_bddAbove_iff {α : Type*} [LinearOrder α] {s : Set α} :
    ¬BddAbove s ↔ ∀ x, ∃ y ∈ s, x < y := by
  simp only [not_bddAbove_iff', not_le]

@[to_dual (attr := simp)]
/-
**bddAbove_preimage_ofDual** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：bddAbove_preimage_ofDual {s : Set α} : BddAbove (ofDual ⁻¹' s) ↔ BddBelow 
s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma bddAbove_preimage_ofDual {s : Set α} : BddAbove (ofDual ⁻¹' s) ↔ BddBelow s := Iff.rfl

@[to_dual (attr := simp)]
/-
**bddAbove_preimage_toDual** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：bddAbove_preimage_toDual {s : Set αᵒᵈ} : BddAbove (toDual ⁻¹' s) ↔ BddBelo
w s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma bddAbove_preimage_toDual {s : Set αᵒᵈ} : BddAbove (toDual ⁻¹' s) ↔ BddBelow s := Iff.rfl

@[to_dual]
/-
**BddAbove.dual** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：BddAbove.dual (h : BddAbove s) : BddBelow (ofDual ⁻¹' s)
参数：h : BddAbove s。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem BddAbove.dual (h : BddAbove s) : BddBelow (ofDual ⁻¹' s) :=
  h

@[to_dual]
/-
**IsLeast.dual** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLeast.dual (h : IsLeast s a) : IsGreatest (ofDual ⁻¹' s) (toDual a)
参数：h : IsLeast s a。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IsLeast.dual (h : IsLeast s a) : IsGreatest (ofDual ⁻¹' s) (toDual a) :=
  h

@[to_dual]
/-
**IsLUB.dual** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLUB.dual (h : IsLUB s a) : IsGLB (ofDual ⁻¹' s) (toDual a)
参数：h : IsLUB s a。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IsLUB.dual (h : IsLUB s a) : IsGLB (ofDual ⁻¹' s) (toDual a) :=
  h

/-- If `a` is the least element of a set `s`, then subtype `s` is an order with bottom element. -/
@[to_dual
/-- If `a` is the greatest element of a set `s`, then subtype `s` is an order with top element. -/]
/-
**IsLeast.orderBot** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：IsLeast.orderBot (h : IsLeast s a) : OrderBot s where bot
参数：h : IsLeast s a。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
abbrev IsLeast.orderBot (h : IsLeast s a) :
    OrderBot s where
  bot := ⟨a, h.1⟩
  bot_le := Subtype.forall.2 h.2

@[to_dual]
/-
**isLUB_congr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLUB_congr (h : upperBounds s = upperBounds t) : IsLUB s a ↔ IsLUB t a
参数：h : upperBounds s = upperBounds t。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsLUB.eq_1`：∀ {α : Type u_1} [inst : LE α] (s : Set α), IsLUB s = IsLeas
t (upperBounds s)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isLUB_congr (h : upperBounds s = upperBounds t) : IsLUB s a ↔ IsLUB t a := by
  rw [IsLUB, IsLUB, h]

@[to_dual (attr := simp)]
/-
**IsCofinalFor.of_subset** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsCofinalFor.of_subset (hst : s subseteq t) : IsCofinalFor s t
参数：hst : s subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
lemma IsCofinalFor.of_subset (hst : s ⊆ t) : IsCofinalFor s t :=
  fun a ha ↦ ⟨a, hst ha, le_rfl⟩

@[to_dual]
alias LE.le.isCofinalFor := IsCofinalFor.of_subset

@[deprecated (since := "2026-03-23")] alias HasSubset.Subset.isCofinalFor := LE.le.isCofinalFor
@[deprecated (since := "2026-03-23")] alias HasSubset.Subset.isCoinitialFor := LE.le.isCoinitialFor

@[deprecated LE.le.isCofinalFor (since := "2026-01-08")]
alias HasSubset.Subset.iscofinalfor := IsCofinalFor.of_subset
@[deprecated LE.le.isCoinitialFor (since := "2026-01-08")]
alias HasSubset.Subset.iscoinitialfor := IsCoinitialFor.of_subset

@[to_dual (attr := refl)]
/-
**IsCofinalFor.rfl** 是 Mathlib 中的一个定理，位于命名空间 `IsCofinalFor`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {s : Set α}, IsCofinalFor s s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsCofinalFor.of_subset`：IsCofinalFor.of_subset (hst : s subseteq t) : Is
CofinalFor s t
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
-/
protected lemma IsCofinalFor.rfl : IsCofinalFor s s := .of_subset .rfl

@[to_dual]
/-
**IsCofinalFor.trans** 是 Mathlib 中的一个定理，位于命名空间 `IsCofinalFor`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {s t u : Set α}, IsCofinalFor s t → I
sCofinalFor t u → IsCofinalFor s u
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
protected lemma IsCofinalFor.trans (hst : IsCofinalFor s t) (htu : IsCofinalFor t u) :
    IsCofinalFor s u :=
  fun _a ha ↦ let ⟨_b, hb, hab⟩ := hst ha; let ⟨c, hc, hbc⟩ := htu hb; ⟨c, hc, hab.trans hbc⟩

@[to_dual]
/-
**IsCofinalFor.mono_left** 是 Mathlib 中的一个定理，位于命名空间 `IsCofinalFor`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {s t u : Set α}, s ⊆ t → IsCofinalFor
 t u → IsCofinalFor s u
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCofinalFor.trans`：∀ {α : Type u_1} [inst : Preorder α] {s t u : Set α}
, IsCofinalFor s t → IsCofinalFor t u → IsCofinalFor s u
· 使用定理 `LE.le.isCofinalFor`：∀ {α : Type u_1} [inst : Preorder α] {s t : Set α}, 
s ⊆ t → IsCofinalFor s t
-/
protected lemma IsCofinalFor.mono_left (hst : s ⊆ t) (htu : IsCofinalFor t u) :
    IsCofinalFor s u := hst.isCofinalFor.trans htu

@[to_dual]
/-
**IsCofinalFor.mono_right** 是 Mathlib 中的一个定理，位于命名空间 `IsCofinalFor`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {s t u : Set α}, t ⊆ u → IsCofinalFor
 s t → IsCofinalFor s u
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCofinalFor.trans`：∀ {α : Type u_1} [inst : Preorder α] {s t u : Set α}
, IsCofinalFor s t → IsCofinalFor t u → IsCofinalFor s u
· 使用定理 `LE.le.isCofinalFor`：∀ {α : Type u_1} [inst : Preorder α] {s t : Set α}, 
s ⊆ t → IsCofinalFor s t
-/
protected lemma IsCofinalFor.mono_right (htu : t ⊆ u) (hst : IsCofinalFor s t) :
    IsCofinalFor s u := hst.trans htu.isCofinalFor
/-
**DirectedOn.isCofinalFor_fst_image_prod_snd_image** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：DirectedOn.isCofinalFor_fst_image_prod_snd_image {β : Type*} [Preorder β] 
{s : Set (α × β)} (hs : DirectedOn (· <= ·) s) : IsCofinalFor ((Prod.fst '' s) ×
ˢ (Prod.snd '' s)) s
参数：α × β；hs : DirectedOn (· <= ·) s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma DirectedOn.isCofinalFor_fst_image_prod_snd_image {β : Type*} [Preorder β] {s : Set (α × β)}
    (hs : DirectedOn (· ≤ ·) s) : IsCofinalFor ((Prod.fst '' s) ×ˢ (Prod.snd '' s)) s := by
  rintro ⟨_, _⟩ ⟨⟨x, hx, rfl⟩, y, hy, rfl⟩
  obtain ⟨z, hz, hxz, hyz⟩ := hs _ hx _ hy
  exact ⟨z, hz, hxz.1, hyz.2⟩

@[to_dual]
/-
**IsCofinalFor.nonempty** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsCofinalFor.nonempty (h : IsCofinalFor s t) (hs : s.Nonempty) : t.Nonempt
y
参数：h : IsCofinalFor s t；hs : s.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma IsCofinalFor.nonempty (h : IsCofinalFor s t) (hs : s.Nonempty) : t.Nonempty :=
  let ⟨_, ha⟩ := hs; let ⟨b, hb, _⟩ := h ha; ⟨b, hb⟩
/-
**IsCofinalFor.union_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCofinalFor.union_left (hc : IsCofinalFor s t) : IsCofinalFor (s union t)
 t
参数：hc : IsCofinalFor s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem IsCofinalFor.union_left (hc : IsCofinalFor s t) : IsCofinalFor (s ∪ t) t := by
  rintro a (has | hat)
  · exact hc has
  · exact ⟨a, hat, le_rfl⟩
/-
**IsCofinalFor.union_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCofinalFor.union_right (hc : IsCofinalFor s t) : IsCofinalFor (t union s
) t
参数：hc : IsCofinalFor s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.union_comm`：union_comm (a b : Set α) : a union b = b union a
· 使用定理 `IsCofinalFor.union_left`：IsCofinalFor.union_left (hc : IsCofinalFor s t)
 : IsCofinalFor (s union t) t
-/
theorem IsCofinalFor.union_right (hc : IsCofinalFor s t) : IsCofinalFor (t ∪ s) t := by
  rw [union_comm]
  exact hc.union_left
/-
**DirectedOn.of_isCofinalFor** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DirectedOn.of_isCofinalFor (hd : DirectedOn (· <= ·) t) (hst : s subseteq 
t) (hc : IsCofinalFor t s) : DirectedOn (· <= ·) s
参数：hd : DirectedOn (· <= ·) t；hst : s subseteq t；hc : IsCofinalFor t s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
theorem DirectedOn.of_isCofinalFor (hd : DirectedOn (· ≤ ·) t)
    (hst : s ⊆ t) (hc : IsCofinalFor t s) : DirectedOn (· ≤ ·) s := by
  intro x hx y hy
  obtain ⟨z, hz, hxz, hyz⟩ := hd x (hst hx) y (hst hy)
  obtain ⟨w, hw, hzw⟩ := hc hz
  exact ⟨w, hw, hxz.trans hzw, hyz.trans hzw⟩
/-
**isCofinalFor_or_isCofinalFor_of_directedOn_union** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCofinalFor_or_isCofinalFor_of_directedOn_union (h : DirectedOn (· <= ·) 
(s union t)) : IsCofinalFor t s ∨ IsCofinalFor s t
参数：h : DirectedOn (· <= ·) (s union t)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
-/
theorem isCofinalFor_or_isCofinalFor_of_directedOn_union (h : DirectedOn (· ≤ ·) (s ∪ t)) :
    IsCofinalFor t s ∨ IsCofinalFor s t := by
  rw [or_iff_not_imp_left]
  intro hts x hx
  simp only [IsCofinalFor, not_forall, not_exists, not_and] at hts
  obtain ⟨y, hy, hys⟩ := hts
  obtain ⟨z, (hzs | hzt), hxz, hyz⟩ := h x (.inl hx) y (.inr hy)
  · cases hys z hzs hyz
  · exact ⟨z, hzt, hxz⟩
/-
**directedOn_union_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：directedOn_union_iff : DirectedOn (· <= ·) (s union t) ↔ DirectedOn (· <= 
·) s ∧ IsCofinalFor t s ∨ DirectedOn (· <= ·) t ∧ IsCofinalFor s t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isCofinalFor_or_isCofinalFor_of_directedOn_union`：isCofinalFor_or_isCofi
nalFor_of_directedOn_union (h : DirectedOn (· <= ·) (s union t)) : IsCofinalFor 
t s ∨ IsCofinalFor s t
· 使用定理 `DirectedOn.of_isCofinalFor`：DirectedOn.of_isCofinalFor (hd : DirectedOn 
(· <= ·) t) (hst : s subseteq t) (hc : IsCofinalFor t s) : DirectedOn (· <= ·) s
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
· 使用定理 `IsCofinalFor.union_right`：IsCofinalFor.union_right (hc : IsCofinalFor s 
t) : IsCofinalFor (t union s) t
· 使用定理 `Set.subset_union_right`：subset_union_right {s t : Set α} : t subseteq s 
union t
· 使用定理 `IsCofinalFor.union_left`：IsCofinalFor.union_left (hc : IsCofinalFor s t)
 : IsCofinalFor (s union t) t
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
theorem directedOn_union_iff :
    DirectedOn (· ≤ ·) (s ∪ t) ↔
      DirectedOn (· ≤ ·) s ∧ IsCofinalFor t s ∨ DirectedOn (· ≤ ·) t ∧ IsCofinalFor s t := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · rcases isCofinalFor_or_isCofinalFor_of_directedOn_union h with hts | hst
    · exact .inl ⟨DirectedOn.of_isCofinalFor h subset_union_left hts.union_right, hts⟩
    · exact .inr ⟨DirectedOn.of_isCofinalFor h subset_union_right hst.union_left, hst⟩
  · rintro (⟨hs, hts⟩ | ⟨ht, hst⟩) x hx y hy
    · obtain ⟨x', hx', hxx'⟩ := hts.union_right hx
      obtain ⟨y', hy', hyy'⟩ := hts.union_right hy
      obtain ⟨z, hz, hx'z, hy'z⟩ := hs x' hx' y' hy'
      exact ⟨z, .inl hz, hxx'.trans hx'z, hyy'.trans hy'z⟩
    · obtain ⟨x', hx', hxx'⟩ := hst.union_left hx
      obtain ⟨y', hy', hyy'⟩ := hst.union_left hy
      obtain ⟨z, hz, hx'z, hy'z⟩ := ht x' hx' y' hy'
      exact ⟨z, .inr hz, hxx'.trans hx'z, hyy'.trans hy'z⟩
/-
**directedOn_or_directedOn_of_union** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：directedOn_or_directedOn_of_union (h : DirectedOn (· <= ·) (s union t)) : 
DirectedOn (· <= ·) s ∨ DirectedOn (· <= ·) t
参数：h : DirectedOn (· <= ·) (s union t)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `directedOn_union_iff`：directedOn_union_iff : DirectedOn (· <= ·) (s unio
n t) ↔ DirectedOn (· <= ·) s ∧ IsCofinalFor t s ∨ DirectedOn (· <= ·) t ∧ IsCofi
nalFor s t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
-/
theorem directedOn_or_directedOn_of_union (h : DirectedOn (· ≤ ·) (s ∪ t)) :
    DirectedOn (· ≤ ·) s ∨ DirectedOn (· ≤ ·) t := by
  rw [directedOn_union_iff] at h
  tauto
/-
**directedOn_or_directedOn_of_union'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：directedOn_or_directedOn_of_union' (hn : (s union t).Nonempty) (h : Direct
edOn (· <= ·) (s union t)) : DirectedOn (· <= ·) s ∧ s.Nonempty ∨ DirectedOn (· 
<= ·) t ∧ t.Nonempty
参数：hn : (s union t).Nonempty；h : DirectedOn (· <= ·) (s union t)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `directedOn_or_directedOn_of_union`：directedOn_or_directedOn_of_union (h 
: DirectedOn (· <= ·) (s union t)) : DirectedOn (· <= ·) s ∨ DirectedOn (· <= ·)
 t
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `Set.empty_union`：empty_union (a : Set α) : ∅ union a = a
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.union_empty`：union_empty (a : Set α) : a union ∅ = a
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
-/
theorem directedOn_or_directedOn_of_union'
    (hn : (s ∪ t).Nonempty) (h : DirectedOn (· ≤ ·) (s ∪ t)) :
    DirectedOn (· ≤ ·) s ∧ s.Nonempty ∨ DirectedOn (· ≤ ·) t ∧ t.Nonempty := by
  obtain h | h := directedOn_or_directedOn_of_union h
  · obtain rfl | hs := s.eq_empty_or_nonempty
    · aesop
    · exact .inl ⟨h, hs⟩
  · obtain rfl | ht := t.eq_empty_or_nonempty
    · aesop
    · exact .inr ⟨h, ht⟩

/-!
### Monotonicity
-/


@[to_dual]
/-
**upperBounds_mono_set** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：upperBounds_mono_set ⦃s t : Set α⦄ (hst : s subseteq t) : upperBounds t su
bseteq upperBounds s
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Monotonicity
-/
theorem upperBounds_mono_set ⦃s t : Set α⦄ (hst : s ⊆ t) : upperBounds t ⊆ upperBounds s :=
  fun _ hb _ h => hb <| hst h

@[to_dual (attr := gcongr)]
/-
**upperBounds_mono_of_isCofinalFor** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：upperBounds_mono_of_isCofinalFor (hst : IsCofinalFor s t) : upperBounds t 
subseteq upperBounds s
参数：hst : IsCofinalFor s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
lemma upperBounds_mono_of_isCofinalFor (hst : IsCofinalFor s t) : upperBounds t ⊆ upperBounds s :=
  fun _a ha _b hb ↦ let ⟨_c, hc, hbc⟩ := hst hb; hbc.trans (ha hc)

@[to_dual]
/-
**upperBounds_mono_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：upperBounds_mono_mem ⦃a b⦄ (hab : a <= b) : a in upperBounds s -> b in upp
erBounds s
参数：hab : a <= b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
-/
theorem upperBounds_mono_mem ⦃a b⦄ (hab : a ≤ b) : a ∈ upperBounds s → b ∈ upperBounds s :=
  fun ha _ h => le_trans (ha h) hab

@[to_dual]
/-
**upperBounds_mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：upperBounds_mono ⦃s t : Set α⦄ (hst : s subseteq t) ⦃a b⦄ (hab : a <= b) :
 a in upperBounds t -> b in upperBounds s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `upperBounds_mono_set`：upperBounds_mono_set ⦃s t : Set α⦄ (hst : s subset
eq t) : upperBounds t subseteq upperBounds s
· 使用定理 `upperBounds_mono_mem`：upperBounds_mono_mem ⦃a b⦄ (hab : a <= b) : a in u
pperBounds s -> b in upperBounds s
-/
theorem upperBounds_mono ⦃s t : Set α⦄ (hst : s ⊆ t) ⦃a b⦄ (hab : a ≤ b) :
    a ∈ upperBounds t → b ∈ upperBounds s := fun ha =>
  upperBounds_mono_set hst <| upperBounds_mono_mem hab ha

/-- If `s ⊆ t` and `t` is bounded above, then so is `s`. -/
@[to_dual (attr := gcongr) /-- If `s ⊆ t` and `t` is bounded below, then so is `s`. -/]
/-
**BddAbove.mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：BddAbove.mono ⦃s t : Set α⦄ (h : s subseteq t) : BddAbove t -> BddAbove s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Nonempty.mono`：∀ {α : Type u} {s t : Set α}, s ⊆ t → s.Nonempty → t.
Nonempty
· 使用定理 `upperBounds_mono_set`：upperBounds_mono_set ⦃s t : Set α⦄ (hst : s subset
eq t) : upperBounds t subseteq upperBounds s

--- 原说明 ---
If `s ⊆ t` and `t` is bounded above, then so is `s`.
-/
theorem BddAbove.mono ⦃s t : Set α⦄ (h : s ⊆ t) : BddAbove t → BddAbove s :=
  Nonempty.mono <| upperBounds_mono_set h

/-- If the range of a function `g` is bounded above, then `g ∘ f` is bounded above for all functions
`f`. -/
@[to_dual /-- If the range of a function `g` is bounded below, then `g ∘ f` is bounded below for all
functions `f`. -/]
/-
**BddAbove.range_comp_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：BddAbove.range_comp_right (f : γ -> β) {g : β -> α} (hg : BddAbove (Set.ra
nge g)) : BddAbove (Set.range (g ∘ f))
参数：f : γ -> β；hg : BddAbove (Set.range g)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BddAbove.mono`：BddAbove.mono ⦃s t : Set α⦄ (h : s subseteq t) : BddAbove
 t -> BddAbove s
· 使用定理 `Set.range_comp_subset_range`：range_comp_subset_range (f : α -> β) (g : β
 -> γ) : range (g ∘ f) subseteq range g
-/
theorem BddAbove.range_comp_right (f : γ → β) {g : β → α}
    (hg : BddAbove (Set.range g)) : BddAbove (Set.range (g ∘ f)) :=
  hg.mono (range_comp_subset_range f g)

/-- If `a` is a least upper bound for sets `s` and `p`, then it is a least upper bound for any
set `t`, `s ⊆ t ⊆ p`. -/
@[to_dual /-- If `a` is a greatest lower bound for sets `s` and `p`, then it is a greater lower
bound for any set `t`, `s ⊆ t ⊆ p`. -/]
/-
**IsLUB.of_subset_of_superset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLUB.of_subset_of_superset {s t p : Set α} (hs : IsLUB s a) (hp : IsLUB p
 a) (hst : s subseteq t) (htp : t subseteq p) : IsLUB t a
参数：hs : IsLUB s a；hp : IsLUB p a；hst : s subseteq t；htp : t subseteq p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `upperBounds_mono_set`：upperBounds_mono_set ⦃s t : Set α⦄ (hst : s subset
eq t) : upperBounds t subseteq upperBounds s
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `lowerBounds_mono_set`：∀ {α : Type u_1} [inst : Preorder α] ⦃s t : Set α⦄
, s ⊆ t → lowerBounds t ⊆ lowerBounds s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem IsLUB.of_subset_of_superset {s t p : Set α} (hs : IsLUB s a) (hp : IsLUB p a) (hst : s ⊆ t)
    (htp : t ⊆ p) : IsLUB t a :=
  ⟨upperBounds_mono_set htp hp.1, lowerBounds_mono_set (upperBounds_mono_set hst) hs.2⟩

/-- The least upper bound of a set is also the least upper bound of any cofinal subset. -/
@[to_dual /-- The greatest lower bound of a set is also the greatest lower bound of any
coinitial subset. -/]
/-
**IsLUB.of_isCofinalFor** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLUB.of_isCofinalFor {s t : Set α} (hs : IsLUB s a) (hts : t subseteq s) 
(hst : IsCofinalFor s t) : IsLUB t a
参数：hs : IsLUB s a；hts : t subseteq s；hst : IsCofinalFor s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `upperBounds_mono_set`：upperBounds_mono_set ⦃s t : Set α⦄ (hst : s subset
eq t) : upperBounds t subseteq upperBounds s
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `upperBounds_mono_of_isCofinalFor`：upperBounds_mono_of_isCofinalFor (hst 
: IsCofinalFor s t) : upperBounds t subseteq upperBounds s
-/
theorem IsLUB.of_isCofinalFor {s t : Set α} (hs : IsLUB s a) (hts : t ⊆ s)
    (hst : IsCofinalFor s t) : IsLUB t a :=
  ⟨upperBounds_mono_set hts hs.1, fun _b hb ↦ hs.2 (upperBounds_mono_of_isCofinalFor hst hb)⟩

@[to_dual]
/-
**IsLeast.mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLeast.mono (ha : IsLeast s a) (hb : IsLeast t b) (hst : s subseteq t) : 
b <= a
参数：ha : IsLeast s a；hb : IsLeast t b；hst : s subseteq t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem IsLeast.mono (ha : IsLeast s a) (hb : IsLeast t b) (hst : s ⊆ t) : b ≤ a :=
  hb.2 (hst ha.1)

@[to_dual]
/-
**IsLUB.mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLUB.mono (ha : IsLUB s a) (hb : IsLUB t b) (hst : s subseteq t) : a <= b
参数：ha : IsLUB s a；hb : IsLUB t b；hst : s subseteq t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLeast.mono`：IsLeast.mono (ha : IsLeast s a) (hb : IsLeast t b) (hst : 
s subseteq t) : b <= a
· 使用定理 `upperBounds_mono_set`：upperBounds_mono_set ⦃s t : Set α⦄ (hst : s subset
eq t) : upperBounds t subseteq upperBounds s
-/
theorem IsLUB.mono (ha : IsLUB s a) (hb : IsLUB t b) (hst : s ⊆ t) : a ≤ b :=
  IsLeast.mono hb ha <| upperBounds_mono_set hst

@[to_dual]
/-
**subset_lowerBounds_upperBounds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：subset_lowerBounds_upperBounds (s : Set α) : s subseteq lowerBounds (upper
Bounds s)
参数：s : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem subset_lowerBounds_upperBounds (s : Set α) : s ⊆ lowerBounds (upperBounds s) :=
  fun _ hx _ hy => hy hx

@[to_dual]
/-
**Set.Nonempty.bddAbove_lowerBounds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.Nonempty.bddAbove_lowerBounds (hs : s.Nonempty) : BddAbove (lowerBound
s s)
参数：hs : s.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Nonempty.mono`：∀ {α : Type u} {s t : Set α}, s ⊆ t → s.Nonempty → t.
Nonempty
· 使用定理 `subset_upperBounds_lowerBounds`：∀ {α : Type u_1} [inst : Preorder α] (s 
: Set α), s ⊆ upperBounds (lowerBounds s)
-/
theorem Set.Nonempty.bddAbove_lowerBounds (hs : s.Nonempty) : BddAbove (lowerBounds s) :=
  hs.mono (subset_upperBounds_lowerBounds s)

/-!
### Conversions
-/


@[to_dual]
/-
**IsLeast.isGLB** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLeast.isGLB (h : IsLeast s a) : IsGLB s a
参数：h : IsLeast s a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a

--- 原说明 ---
### Conversions
-/
theorem IsLeast.isGLB (h : IsLeast s a) : IsGLB s a :=
  ⟨h.2, fun _ hb => hb h.1⟩

@[to_dual]
/-
**IsLUB.upperBounds_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLUB.upperBounds_eq (h : IsLUB s a) : upperBounds s = Ici a
参数：h : IsLUB s a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `upperBounds_mono_mem`：upperBounds_mono_mem ⦃a b⦄ (hab : a <= b) : a in u
pperBounds s -> b in upperBounds s
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem IsLUB.upperBounds_eq (h : IsLUB s a) : upperBounds s = Ici a :=
  Set.ext fun _ => ⟨fun hb => h.2 hb, fun hb => upperBounds_mono_mem hb h.1⟩

@[to_dual]
/-
**IsLeast.lowerBounds_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLeast.lowerBounds_eq (h : IsLeast s a) : lowerBounds s = Iic a
参数：h : IsLeast s a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsGLB.lowerBounds_eq`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α} {
a : α}, IsGLB s a → lowerBounds s = Set.Iic a
· 使用定理 `IsLeast.isGLB`：IsLeast.isGLB (h : IsLeast s a) : IsGLB s a
-/
theorem IsLeast.lowerBounds_eq (h : IsLeast s a) : lowerBounds s = Iic a :=
  h.isGLB.lowerBounds_eq

@[to_dual]
/-
**IsGreatest.lt_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsGreatest.lt_iff (h : IsGreatest s a) : a < b ↔ forall x in s, x < b
参数：h : IsGreatest s a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem IsGreatest.lt_iff (h : IsGreatest s a) : a < b ↔ ∀ x ∈ s, x < b :=
  ⟨fun hlt _x hx => (h.2 hx).trans_lt hlt, fun h' => h' _ h.1⟩

@[to_dual le_isGLB_iff]
/-
**isLUB_le_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLUB_le_iff (h : IsLUB s a) : a <= b ↔ b in upperBounds s
参数：h : IsLUB s a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsLUB.upperBounds_eq`：IsLUB.upperBounds_eq (h : IsLUB s a) : upperBounds
 s = Ici a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isLUB_le_iff (h : IsLUB s a) : a ≤ b ↔ b ∈ upperBounds s := by
  rw [h.upperBounds_eq]
  rfl

@[to_dual]
/-
**isLUB_iff_le_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLUB_iff_le_iff : IsLUB s a ↔ forall b, a <= b ↔ b in upperBounds s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isLUB_le_iff`：isLUB_le_iff (h : IsLUB s a) : a <= b ↔ b in upperBounds s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem isLUB_iff_le_iff : IsLUB s a ↔ ∀ b, a ≤ b ↔ b ∈ upperBounds s :=
  ⟨fun h _ => isLUB_le_iff h, fun H => ⟨(H _).1 le_rfl, fun b hb => (H b).2 hb⟩⟩

/-- If `s` has a least upper bound, then it is bounded above. -/
@[to_dual /-- If `s` has a greatest lower bound, then it is bounded below. -/]
/-
**IsLUB.bddAbove** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLUB.bddAbove (h : IsLUB s a) : BddAbove s
参数：h : IsLUB s a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a

--- 原说明 ---
If `s` has a least upper bound, then it is bounded above.
-/
theorem IsLUB.bddAbove (h : IsLUB s a) : BddAbove s :=
  ⟨a, h.1⟩

/-- If `s` has a greatest element, then it is bounded above. -/
@[to_dual /-- If `s` has a least element, then it is bounded below. -/]
/-
**IsGreatest.bddAbove** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsGreatest.bddAbove (h : IsGreatest s a) : BddAbove s
参数：h : IsGreatest s a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
If `s` has a greatest element, then it is bounded above.
-/
theorem IsGreatest.bddAbove (h : IsGreatest s a) : BddAbove s :=
  ⟨a, h.2⟩

@[to_dual]
/-
**IsLeast.nonempty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLeast.nonempty (h : IsLeast s a) : s.Nonempty
参数：h : IsLeast s a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem IsLeast.nonempty (h : IsLeast s a) : s.Nonempty :=
  ⟨a, h.1⟩

/-!
### Union and intersection
-/

@[to_dual (attr := simp)]
/-
**upperBounds_union** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：upperBounds_union : upperBounds (s union t) = upperBounds s inter upperBou
nds t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
### Union and intersection
-/
theorem upperBounds_union : upperBounds (s ∪ t) = upperBounds s ∩ upperBounds t :=
  Subset.antisymm (fun _ hb => ⟨fun _ hx => hb (Or.inl hx), fun _ hx => hb (Or.inr hx)⟩)
    fun _ hb _ hx => hx.elim (fun hs => hb.1 hs) fun ht => hb.2 ht

@[to_dual]
/-
**union_upperBounds_subset_upperBounds_inter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：union_upperBounds_subset_upperBounds_inter : upperBounds s union upperBoun
ds t subseteq upperBounds (s inter t)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.union_subset`：union_subset {s t r : Set α} (sr : s subseteq r) (tr :
 t subseteq r) : s union t subseteq r
· 使用定理 `upperBounds_mono_set`：upperBounds_mono_set ⦃s t : Set α⦄ (hst : s subset
eq t) : upperBounds t subseteq upperBounds s
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
-/
theorem union_upperBounds_subset_upperBounds_inter :
    upperBounds s ∪ upperBounds t ⊆ upperBounds (s ∩ t) :=
  union_subset (upperBounds_mono_set inter_subset_left)
    (upperBounds_mono_set inter_subset_right)

@[to_dual]
/-
**isLeast_union_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLeast_union_iff {a : α} {s t : Set α} : IsLeast (s union t) a ↔ IsLeast 
s a ∧ a in lowerBounds t ∨ a in lowerBounds s ∧ IsLeast t a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `lowerBounds_union`：∀ {α : Type u_1} [inst : Preorder α] {s t : Set α}, l
owerBounds (s ∪ t) = lowerBounds s ∩ lowerBounds t
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isLeast_union_iff {a : α} {s t : Set α} :
    IsLeast (s ∪ t) a ↔ IsLeast s a ∧ a ∈ lowerBounds t ∨ a ∈ lowerBounds s ∧ IsLeast t a := by
  simp [IsLeast, lowerBounds_union, or_and_right, and_comm (a := a ∈ t), and_assoc]

/-- If `s` is bounded, then so is `s ∩ t` -/
@[to_dual /-- If `s` is bounded, then so is `s ∩ t` -/]
/-
**BddAbove.inter_of_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：BddAbove.inter_of_left (h : BddAbove s) : BddAbove (s inter t)
参数：h : BddAbove s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BddAbove.mono`：BddAbove.mono ⦃s t : Set α⦄ (h : s subseteq t) : BddAbove
 t -> BddAbove s
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s

--- 原说明 ---
If `s` is bounded, then so is `s ∩ t`
-/
theorem BddAbove.inter_of_left (h : BddAbove s) : BddAbove (s ∩ t) :=
  h.mono inter_subset_left

/-- If `t` is bounded, then so is `s ∩ t` -/
@[to_dual /-- If `t` is bounded, then so is `s ∩ t` -/]
/-
**BddAbove.inter_of_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：BddAbove.inter_of_right (h : BddAbove t) : BddAbove (s inter t)
参数：h : BddAbove t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BddAbove.mono`：BddAbove.mono ⦃s t : Set α⦄ (h : s subseteq t) : BddAbove
 t -> BddAbove s
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t

--- 原说明 ---
If `t` is bounded, then so is `s ∩ t`
-/
theorem BddAbove.inter_of_right (h : BddAbove t) : BddAbove (s ∩ t) :=
  h.mono inter_subset_right

/-- In a directed order, the union of bounded above sets is bounded above. -/
@[to_dual /-- In a codirected order, the union of bounded below sets is bounded below. -/]
/-
**BddAbove.union** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：BddAbove.union [IsDirectedOrder α] {s t : Set α} : BddAbove s -> BddAbove 
t -> BddAbove (s union t)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_ge_ge`：exists_ge_ge [LE α] [IsDirectedOrder α] (a b : α) : exists
 c, a <= c ∧ b <= c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `BddAbove.eq_1`：∀ {α : Type u_1} [inst : LE α] (s : Set α), BddAbove s = 
(upperBounds s).Nonempty
· 使用定理 `upperBounds_union`：upperBounds_union : upperBounds (s union t) = upperBo
unds s inter upperBounds t
· 使用定理 `upperBounds_mono_mem`：upperBounds_mono_mem ⦃a b⦄ (hab : a <= b) : a in u
pperBounds s -> b in upperBounds s

--- 原说明 ---
In a directed order, the union of bounded above sets is bounded above.
-/
theorem BddAbove.union [IsDirectedOrder α] {s t : Set α} :
    BddAbove s → BddAbove t → BddAbove (s ∪ t) := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  obtain ⟨c, hca, hcb⟩ := exists_ge_ge a b
  rw [BddAbove, upperBounds_union]
  exact ⟨c, upperBounds_mono_mem hca ha, upperBounds_mono_mem hcb hb⟩

/-- In a directed order, the union of two sets is bounded above if and only if both sets are. -/
@[to_dual
/-- In a codirected order, the union of two sets is bounded below if and only if both sets are. -/]
/-
**bddAbove_union** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：bddAbove_union [IsDirectedOrder α] {s t : Set α} : BddAbove (s union t) ↔ 
BddAbove s ∧ BddAbove t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BddAbove.mono`：BddAbove.mono ⦃s t : Set α⦄ (h : s subseteq t) : BddAbove
 t -> BddAbove s
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
· 使用定理 `Set.subset_union_right`：subset_union_right {s t : Set α} : t subseteq s 
union t
· 使用定理 `BddAbove.union`：BddAbove.union [IsDirectedOrder α] {s t : Set α} : BddAb
ove s -> BddAbove t -> BddAbove (s union t)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem bddAbove_union [IsDirectedOrder α] {s t : Set α} :
    BddAbove (s ∪ t) ↔ BddAbove s ∧ BddAbove t :=
  ⟨fun h => ⟨h.mono subset_union_left, h.mono subset_union_right⟩, fun h =>
    h.1.union h.2⟩

@[to_dual]
/-
**bbdAbove_range_sup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：bbdAbove_range_sup {ι : Sort*} {α : Type*} [SemilatticeSup α] {f g : ι -> 
α} (hf : BddAbove <| range f) (hg : BddAbove <| range g) : BddAbove range fun x 
=> f x ⊔ g x
参数：hf : BddAbove <| range f；hg : BddAbove <| range g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_le_sup`：sup_le_sup (h₁ : a <= b) (h₂ : c <= d) : a ⊔ c <= b ⊔ d
-/
theorem bbdAbove_range_sup {ι : Sort*} {α : Type*} [SemilatticeSup α] {f g : ι → α}
    (hf : BddAbove <| range f) (hg : BddAbove <| range g) :
    BddAbove <| range fun x ↦ f x ⊔ g x := by
  have ⟨af, haf⟩ := hf
  have ⟨ag, hag⟩ := hg
  exact ⟨af ⊔ ag, fun a ⟨i, ha⟩ ↦ ha ▸ sup_le_sup (haf ⟨i, rfl⟩) (hag ⟨i, rfl⟩)⟩

@[to_dual]
/-
**bbdAbove_range_left_of_sup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：bbdAbove_range_left_of_sup {ι : Sort*} {α : Type*} [SemilatticeSup α] {f g
 : ι -> α} (h : BddAbove <| range fun x => f x ⊔ g x) : BddAbove range f
参数：h : BddAbove <| range fun x => f x ⊔ g x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
-/
theorem bbdAbove_range_left_of_sup {ι : Sort*} {α : Type*} [SemilatticeSup α] {f g : ι → α}
    (h : BddAbove <| range fun x ↦ f x ⊔ g x) : BddAbove <| range f := by
  have ⟨b, hb⟩ := h
  exact ⟨b, fun a ⟨i, ha⟩ ↦ ha ▸ le_sup_left.trans (hb ⟨i, rfl⟩)⟩

@[to_dual]
/-
**bbdAbove_range_right_of_sup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：bbdAbove_range_right_of_sup {ι : Sort*} {α : Type*} [SemilatticeSup α] {f 
g : ι -> α} (h : BddAbove <| range fun x => f x ⊔ g x) : BddAbove range g
参数：h : BddAbove <| range fun x => f x ⊔ g x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
-/
theorem bbdAbove_range_right_of_sup {ι : Sort*} {α : Type*} [SemilatticeSup α] {f g : ι → α}
    (h : BddAbove <| range fun x ↦ f x ⊔ g x) : BddAbove <| range g := by
  have ⟨b, hb⟩ := h
  exact ⟨b, fun a ⟨i, ha⟩ ↦ ha ▸ le_sup_right.trans (hb ⟨i, rfl⟩)⟩

@[to_dual]
/-
**bbdAbove_range_sup_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：bbdAbove_range_sup_iff {ι : Sort*} {α : Type*} [SemilatticeSup α] {f g : ι
 -> α} : BddAbove (range fun x => f x ⊔ g x) ↔ BddAbove (range f) ∧ BddAbove (ra
nge g) where mp h
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `bbdAbove_range_left_of_sup`：bbdAbove_range_left_of_sup {ι : Sort*} {α : 
Type*} [SemilatticeSup α] {f g : ι -> α} (h : BddAbove <| range fun x => f x ⊔ g
 x) : BddAbove r…
· 使用定理 `bbdAbove_range_right_of_sup`：bbdAbove_range_right_of_sup {ι : Sort*} {α 
: Type*} [SemilatticeSup α] {f g : ι -> α} (h : BddAbove <| range fun x => f x ⊔
 g x) : BddAbove …
· 使用定理 `bbdAbove_range_sup`：bbdAbove_range_sup {ι : Sort*} {α : Type*} [Semilatt
iceSup α] {f g : ι -> α} (hf : BddAbove <| range f) (hg : BddAbove <| range g) :
 BddAbov…
-/
theorem bbdAbove_range_sup_iff {ι : Sort*} {α : Type*} [SemilatticeSup α] {f g : ι → α} :
    BddAbove (range fun x ↦ f x ⊔ g x) ↔ BddAbove (range f) ∧ BddAbove (range g) where
  mp h := ⟨bbdAbove_range_left_of_sup h, bbdAbove_range_right_of_sup h⟩
  mpr := fun ⟨hf, hg⟩ ↦ bbdAbove_range_sup hf hg

/-- If `a` is the least upper bound of `s` and `b` is the least upper bound of `t`,
then `a ⊔ b` is the least upper bound of `s ∪ t`. -/
@[to_dual /-- If `a` is the greatest lower bound of `s` and `b` is the greatest lower bound of `t`,
then `a ⊓ b` is the greatest lower bound of `s ∪ t`. -/]
/-
**IsLUB.union** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLUB.union [SemilatticeSup γ] {a b : γ} {s t : Set γ} (hs : IsLUB s a) (h
t : IsLUB t b) : IsLUB (s union t) (a ⊔ b)
参数：hs : IsLUB s a；ht : IsLUB t b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_sup_of_le_left`：le_sup_of_le_left (h : c <= a) : c <= a ⊔ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `le_sup_of_le_right`：le_sup_of_le_right (h : c <= b) : c <= a ⊔ b
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem IsLUB.union [SemilatticeSup γ] {a b : γ} {s t : Set γ} (hs : IsLUB s a) (ht : IsLUB t b) :
    IsLUB (s ∪ t) (a ⊔ b) :=
  ⟨fun _ h =>
    h.casesOn (fun h => le_sup_of_le_left <| hs.left h) fun h => le_sup_of_le_right <| ht.left h,
    fun _ hc =>
    sup_le (hs.right fun _ hd => hc <| Or.inl hd) (ht.right fun _ hd => hc <| Or.inr hd)⟩

/-- If `a` is the least element of `s` and `b` is the least element of `t`,
then `min a b` is the least element of `s ∪ t`. -/
@[to_dual /-- If `a` is the greatest element of `s` and `b` is the greatest element of `t`,
then `max a b` is the greatest element of `s ∪ t`. -/]
/-
**IsLeast.union** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLeast.union [LinearOrder γ] {a b : γ} {s t : Set γ} (ha : IsLeast s a) (
hb : IsLeast t b) : IsLeast (s union t) (min a b)
参数：ha : IsLeast s a；hb : IsLeast t b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `inf_of_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, b ≤
 a → a ⊓ b = b
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `IsGLB.union`：∀ {γ : Type u_3} [inst : SemilatticeInf γ] {a b : γ} {s t :
 Set γ}, IsGLB s a → IsGLB t b → IsGLB (s ∪ t) (a ⊓ b)
· 使用定理 `IsLeast.isGLB`：IsLeast.isGLB (h : IsLeast s a) : IsGLB s a
-/
theorem IsLeast.union [LinearOrder γ] {a b : γ} {s t : Set γ} (ha : IsLeast s a)
    (hb : IsLeast t b) : IsLeast (s ∪ t) (min a b) :=
  ⟨by rcases le_total a b with h | h <;> simp [h, ha.1, hb.1], (ha.isGLB.union hb.isGLB).1⟩

@[to_dual]
/-
**IsLUB.inter_Ici_of_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLUB.inter_Ici_of_mem [LinearOrder γ] {s : Set γ} {a b : γ} (ha : IsLUB s
 a) (hb : b in s) : IsLUB (s inter Ici b) a
参数：ha : IsLUB s a；hb : b in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
theorem IsLUB.inter_Ici_of_mem [LinearOrder γ] {s : Set γ} {a b : γ} (ha : IsLUB s a) (hb : b ∈ s) :
    IsLUB (s ∩ Ici b) a :=
  ⟨fun _ hx => ha.1 hx.1, fun c hc =>
    have hbc : b ≤ c := hc ⟨hb, le_rfl⟩
    ha.2 fun x hx => ((le_total x b).elim fun hxb => hxb.trans hbc) fun hbx => hc ⟨hx, hbx⟩⟩
/-
**bddAbove_iff_exists_ge** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：bddAbove_iff_exists_ge [SemilatticeSup γ] {s : Set γ} (x₀ : γ) : BddAbove 
s ↔ exists x, x₀ <= x ∧ forall y in s, y <= x
参数：x₀ : γ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `bddAbove_def`：bddAbove_def : BddAbove s ↔ exists x, forall y in s, y <= 
x
· 使用定理 `exists_ge_and_iff_exists`：exists_ge_and_iff_exists [SemilatticeSup α] {P
 : α -> Prop} {x₀ : α} (hP : Monotone P) : (exists x, x₀ <= x ∧ P x) ↔ exists x,
 P x
· 使用定理 `Monotone.ball`：Monotone.ball {P : β -> α -> Prop} {s : Set β} (hP : fora
ll x in s, Monotone (P x)) : Monotone fun y => forall x in s, P x y
· 使用定理 `monotone_le`：monotone_le {x : α} : Monotone (x <= ·)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem bddAbove_iff_exists_ge [SemilatticeSup γ] {s : Set γ} (x₀ : γ) :
    BddAbove s ↔ ∃ x, x₀ ≤ x ∧ ∀ y ∈ s, y ≤ x := by
  rw [bddAbove_def, exists_ge_and_iff_exists]
  exact Monotone.ball fun x _ => monotone_le

@[to_dual existing bddAbove_iff_exists_ge]
/-
**bddBelow_iff_exists_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：bddBelow_iff_exists_le [SemilatticeInf γ] {s : Set γ} (x₀ : γ) : BddBelow 
s ↔ exists x, x <= x₀ ∧ forall y in s, x <= y
参数：x₀ : γ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `bddAbove_iff_exists_ge`：bddAbove_iff_exists_ge [SemilatticeSup γ] {s : S
et γ} (x₀ : γ) : BddAbove s ↔ exists x, x₀ <= x ∧ forall y in s, y <= x
-/
theorem bddBelow_iff_exists_le [SemilatticeInf γ] {s : Set γ} (x₀ : γ) :
    BddBelow s ↔ ∃ x, x ≤ x₀ ∧ ∀ y ∈ s, x ≤ y :=
  bddAbove_iff_exists_ge (toDual x₀)

@[to_dual exists_le]
/-
**BddAbove.exists_ge** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：BddAbove.exists_ge [SemilatticeSup γ] {s : Set γ} (hs : BddAbove s) (x₀ : 
γ) : exists x, x₀ <= x ∧ forall y in s, y <= x
参数：hs : BddAbove s；x₀ : γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `bddAbove_iff_exists_ge`：bddAbove_iff_exists_ge [SemilatticeSup γ] {s : S
et γ} (x₀ : γ) : BddAbove s ↔ exists x, x₀ <= x ∧ forall y in s, y <= x
-/
theorem BddAbove.exists_ge [SemilatticeSup γ] {s : Set γ} (hs : BddAbove s) (x₀ : γ) :
    ∃ x, x₀ ≤ x ∧ ∀ y ∈ s, y ≤ x :=
  (bddAbove_iff_exists_ge x₀).mp hs

/-!
### Specific sets

#### Unbounded intervals
-/


@[to_dual]
/-
**isLeast_Ici** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLeast_Ici : IsLeast (Ici a) a
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.self_mem_Ici`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, a ∈ Set.
Ici a

--- 原说明 ---
### Specific sets

#### Unbounded intervals
-/
theorem isLeast_Ici : IsLeast (Ici a) a :=
  ⟨self_mem_Ici, fun _ => id⟩

@[to_dual]
/-
**isLUB_Iic** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLUB_Iic : IsLUB (Iic a) a
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsGreatest.isLUB`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α} {a : 
α}, IsGreatest s a → IsLUB s a
· 使用定理 `isGreatest_Iic`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, IsGreatest
 (Set.Iic a) a
-/
theorem isLUB_Iic : IsLUB (Iic a) a :=
  isGreatest_Iic.isLUB

@[to_dual]
/-
**upperBounds_Iic** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：upperBounds_Iic : upperBounds (Iic a) = Ici a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLUB.upperBounds_eq`：IsLUB.upperBounds_eq (h : IsLUB s a) : upperBounds
 s = Ici a
· 使用定理 `isLUB_Iic`：isLUB_Iic : IsLUB (Iic a) a
-/
theorem upperBounds_Iic : upperBounds (Iic a) = Ici a :=
  isLUB_Iic.upperBounds_eq

@[to_dual]
/-
**bddAbove_Iic** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：bddAbove_Iic : BddAbove (Iic a)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLUB.bddAbove`：IsLUB.bddAbove (h : IsLUB s a) : BddAbove s
· 使用定理 `isLUB_Iic`：isLUB_Iic : IsLUB (Iic a) a
-/
theorem bddAbove_Iic : BddAbove (Iic a) :=
  isLUB_Iic.bddAbove

@[to_dual]
/-
**bddAbove_Iio** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：bddAbove_Iio : BddAbove (Iio a)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem bddAbove_Iio : BddAbove (Iio a) :=
  ⟨a, fun _ hx => le_of_lt hx⟩

@[to_dual]
/-
**le_of_isLUB_Iio** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_of_isLUB_Iio (a : α) (hb : IsLUB (Iio a) b) : b <= a
参数：a : α；hb : IsLUB (Iio a) b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isLUB_le_iff`：isLUB_le_iff (h : IsLUB s a) : a <= b ↔ b in upperBounds s
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem le_of_isLUB_Iio (a : α) (hb : IsLUB (Iio a) b) : b ≤ a :=
  (isLUB_le_iff hb).mpr fun _ hk => le_of_lt hk

@[deprecated (since := "2026-01-17")] alias lub_Iio_le := le_of_isLUB_Iio
@[deprecated (since := "2026-01-17")] alias le_glb_Ioi := le_of_isGLB_Ioi

@[to_dual]
/-
**lub_Iio_eq_self_or_Iio_eq_Iic** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lub_Iio_eq_self_or_Iio_eq_Iic [PartialOrder γ] {j : γ} (i : γ) (hj : IsLUB
 (Iio i) j) : j = i ∨ Iio i = Iic j
参数：i : γ；hj : IsLUB (Iio i) j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_lt_of_le`：eq_or_lt_of_le (h : a <= b) : a = b ∨ a < b
· 使用定理 `le_of_isLUB_Iio`：le_of_isLUB_Iio (a : α) (hb : IsLUB (Iio a) b) : b <= a
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
-/
theorem lub_Iio_eq_self_or_Iio_eq_Iic [PartialOrder γ] {j : γ} (i : γ) (hj : IsLUB (Iio i) j) :
    j = i ∨ Iio i = Iic j := by
  rcases eq_or_lt_of_le (le_of_isLUB_Iio i hj) with hj_eq_i | hj_lt_i
  · exact Or.inl hj_eq_i
  · right
    exact Set.ext fun k => ⟨fun hk_lt => hj.1 hk_lt, fun hk_le_j => lt_of_le_of_lt hk_le_j hj_lt_i⟩
section

variable [LinearOrder γ]

@[to_dual]
/-
**exists_lub_Iio** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_lub_Iio (i : γ) : exists j, IsLUB (Iio i) j
参数：i : γ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mem_lowerBounds`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α} {a : α
}, a ∈ lowerBounds s ↔ ∀ x ∈ s, a ≤ x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem exists_lub_Iio (i : γ) : ∃ j, IsLUB (Iio i) j := by
  by_cases! h_exists_lt : ∃ j, j ∈ upperBounds (Iio i) ∧ j < i
  · obtain ⟨j, hj_ub, hj_lt_i⟩ := h_exists_lt
    exact ⟨j, hj_ub, fun k hk_ub => hk_ub hj_lt_i⟩
  · refine ⟨i, fun j hj => le_of_lt hj, ?_⟩
    rw [mem_lowerBounds]
    exact h_exists_lt

variable [DenselyOrdered γ]

@[to_dual]
/-
**isLUB_Iio** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLUB_Iio {a : γ} : IsLUB (Iio a) a
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `le_of_forall_lt_imp_le_of_dense`：∀ {α : Type u_2} [inst : LinearOrder α]
 [DenselyOrdered α] {a₁ a₂ : α}, (∀ a < a₂, a ≤ a₁) → a₂ ≤ a₁
-/
theorem isLUB_Iio {a : γ} : IsLUB (Iio a) a :=
  ⟨fun _ hx => le_of_lt hx, fun _ hy => le_of_forall_lt_imp_le_of_dense hy⟩

@[to_dual]
/-
**upperBounds_Iio** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：upperBounds_Iio {a : γ} : upperBounds (Iio a) = Ici a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLUB.upperBounds_eq`：IsLUB.upperBounds_eq (h : IsLUB s a) : upperBounds
 s = Ici a
· 使用定理 `isLUB_Iio`：isLUB_Iio {a : γ} : IsLUB (Iio a) a
-/
theorem upperBounds_Iio {a : γ} : upperBounds (Iio a) = Ici a :=
  isLUB_Iio.upperBounds_eq

end

/-!
#### Singleton
-/


@[to_dual (attr := simp)]
/-
**isGreatest_singleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isGreatest_singleton : IsGreatest {a} a
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Set.eq_of_mem_singleton`：eq_of_mem_singleton {x y : α} (h : x in ({y} : 
Set α)) : x = y

--- 原说明 ---
#### Singleton
-/
theorem isGreatest_singleton : IsGreatest {a} a :=
  ⟨mem_singleton a, fun _ hx => le_of_eq <| eq_of_mem_singleton hx⟩

@[to_dual (attr := simp)]
/-
**isLUB_singleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLUB_singleton : IsLUB {a} a
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsGreatest.isLUB`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α} {a : 
α}, IsGreatest s a → IsLUB s a
· 使用定理 `isGreatest_singleton`：isGreatest_singleton : IsGreatest {a} a
-/
theorem isLUB_singleton : IsLUB {a} a :=
  isGreatest_singleton.isLUB

@[to_dual (attr := simp)]
/-
**bddAbove_singleton** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：bddAbove_singleton : BddAbove ({a} : Set α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLUB.bddAbove`：IsLUB.bddAbove (h : IsLUB s a) : BddAbove s
· 使用定理 `isLUB_singleton`：isLUB_singleton : IsLUB {a} a
-/
lemma bddAbove_singleton : BddAbove ({a} : Set α) := isLUB_singleton.bddAbove

@[to_dual (attr := simp)]
/-
**upperBounds_singleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：upperBounds_singleton : upperBounds {a} = Ici a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLUB.upperBounds_eq`：IsLUB.upperBounds_eq (h : IsLUB s a) : upperBounds
 s = Ici a
· 使用定理 `isLUB_singleton`：isLUB_singleton : IsLUB {a} a
-/
theorem upperBounds_singleton : upperBounds {a} = Ici a :=
  isLUB_singleton.upperBounds_eq

/-!
#### Bounded intervals
-/


@[to_dual (attr := simp)]
/-
**bddAbove_Icc** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：bddAbove_Icc : BddAbove (Icc a b)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
#### Bounded intervals
-/
lemma bddAbove_Icc : BddAbove (Icc a b) := ⟨b, fun _ => And.right⟩
@[to_dual (attr := simp)]
/-
**bddAbove_Ico** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：bddAbove_Ico : BddAbove (Ico a b)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BddAbove.mono`：BddAbove.mono ⦃s t : Set α⦄ (h : s subseteq t) : BddAbove
 t -> BddAbove s
· 使用定理 `Set.Ico_subset_Icc_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ico b a ⊆ Set.Icc b a
· 使用引理 `bddAbove_Icc`：bddAbove_Icc : BddAbove (Icc a b)
-/
lemma bddAbove_Ico : BddAbove (Ico a b) := bddAbove_Icc.mono Ico_subset_Icc_self
@[to_dual (attr := simp)]
/-
**bddBelow_Ico** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：bddBelow_Ico : BddBelow (Ico a b)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BddBelow.mono`：∀ {α : Type u_1} [inst : Preorder α] ⦃s t : Set α⦄, s ⊆ t
 → BddBelow t → BddBelow s
· 使用定理 `Set.Ico_subset_Icc_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ico b a ⊆ Set.Icc b a
· 使用定理 `bddBelow_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, BddBelow (
Set.Icc b a)
-/
lemma bddBelow_Ico : BddBelow (Ico a b) := bddBelow_Icc.mono Ico_subset_Icc_self
@[to_dual (attr := simp)]
/-
**bddAbove_Ioo** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：bddAbove_Ioo : BddAbove (Ioo a b)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BddAbove.mono`：BddAbove.mono ⦃s t : Set α⦄ (h : s subseteq t) : BddAbove
 t -> BddAbove s
· 使用定理 `Set.Ioo_subset_Icc_self`：Ioo_subset_Icc_self : Ioo a b subseteq Icc a b
· 使用引理 `bddAbove_Icc`：bddAbove_Icc : BddAbove (Icc a b)
-/
lemma bddAbove_Ioo : BddAbove (Ioo a b) := bddAbove_Icc.mono Ioo_subset_Icc_self

@[to_dual]
/-
**isGreatest_Icc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isGreatest_Icc (h : a <= b) : IsGreatest (Icc a b) b
参数：h : a <= b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.right_mem_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ∈ S
et.Icc b a ↔ b ≤ a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem isGreatest_Icc (h : a ≤ b) : IsGreatest (Icc a b) b :=
  ⟨right_mem_Icc.2 h, fun _ => And.right⟩

@[to_dual]
/-
**isLUB_Icc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLUB_Icc (h : a <= b) : IsLUB (Icc a b) b
参数：h : a <= b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsGreatest.isLUB`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α} {a : 
α}, IsGreatest s a → IsLUB s a
· 使用定理 `isGreatest_Icc`：isGreatest_Icc (h : a <= b) : IsGreatest (Icc a b) b
-/
theorem isLUB_Icc (h : a ≤ b) : IsLUB (Icc a b) b :=
  (isGreatest_Icc h).isLUB

@[to_dual]
/-
**upperBounds_Icc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：upperBounds_Icc (h : a <= b) : upperBounds (Icc a b) = Ici b
参数：h : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLUB.upperBounds_eq`：IsLUB.upperBounds_eq (h : IsLUB s a) : upperBounds
 s = Ici a
· 使用定理 `isLUB_Icc`：isLUB_Icc (h : a <= b) : IsLUB (Icc a b) b
-/
theorem upperBounds_Icc (h : a ≤ b) : upperBounds (Icc a b) = Ici b :=
  (isLUB_Icc h).upperBounds_eq

@[to_dual]
/-
**isGreatest_Ioc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isGreatest_Ioc (h : a < b) : IsGreatest (Ioc a b) b
参数：h : a < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.right_mem_Ioc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ∈ S
et.Ioc b a ↔ b < a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem isGreatest_Ioc (h : a < b) : IsGreatest (Ioc a b) b :=
  ⟨right_mem_Ioc.2 h, fun _ => And.right⟩

@[to_dual]
/-
**isLUB_Ioc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLUB_Ioc (h : a < b) : IsLUB (Ioc a b) b
参数：h : a < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsGreatest.isLUB`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α} {a : 
α}, IsGreatest s a → IsLUB s a
· 使用定理 `isGreatest_Ioc`：isGreatest_Ioc (h : a < b) : IsGreatest (Ioc a b) b
-/
theorem isLUB_Ioc (h : a < b) : IsLUB (Ioc a b) b :=
  (isGreatest_Ioc h).isLUB

@[to_dual]
/-
**upperBounds_Ioc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：upperBounds_Ioc (h : a < b) : upperBounds (Ioc a b) = Ici b
参数：h : a < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLUB.upperBounds_eq`：IsLUB.upperBounds_eq (h : IsLUB s a) : upperBounds
 s = Ici a
· 使用定理 `isLUB_Ioc`：isLUB_Ioc (h : a < b) : IsLUB (Ioc a b) b
-/
theorem upperBounds_Ioc (h : a < b) : upperBounds (Ioc a b) = Ici b :=
  (isLUB_Ioc h).upperBounds_eq

section

variable [SemilatticeSup γ] [DenselyOrdered γ]

@[to_dual]
/-
**isGLB_Ioo** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isGLB_Ioo {a b : γ} (h : a < b) : IsGLB (Ioo a b) a
参数：h : a < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `eq_or_lt_of_le`：eq_or_lt_of_le (h : a <= b) : a = b ∨ a < b
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `exists_between`：exists_between [LT α] [DenselyOrdered α] {a₁ a₂ : α} : a
₁ < a₂ -> exists a, a₁ < a ∧ a < a₂
· 使用定理 `not_lt_of_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
theorem isGLB_Ioo {a b : γ} (h : a < b) : IsGLB (Ioo a b) a :=
  ⟨fun _ hx => hx.1.le, fun x hx => by
    rcases eq_or_lt_of_le (le_sup_right : a ≤ x ⊔ a) with h₁ | h₂
    · exact h₁.symm ▸ le_sup_left
    obtain ⟨y, lty, ylt⟩ := exists_between h₂
    apply (not_lt_of_ge (sup_le (hx ⟨lty, ylt.trans_le (sup_le _ h.le)⟩) lty.le) ylt).elim
    obtain ⟨u, au, ub⟩ := exists_between h
    apply (hx ⟨au, ub⟩).trans ub.le⟩

@[to_dual]
/-
**lowerBounds_Ioo** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lowerBounds_Ioo {a b : γ} (hab : a < b) : lowerBounds (Ioo a b) = Iic a
参数：hab : a < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsGLB.lowerBounds_eq`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α} {
a : α}, IsGLB s a → lowerBounds s = Set.Iic a
· 使用定理 `isGLB_Ioo`：isGLB_Ioo {a b : γ} (h : a < b) : IsGLB (Ioo a b) a
-/
theorem lowerBounds_Ioo {a b : γ} (hab : a < b) : lowerBounds (Ioo a b) = Iic a :=
  (isGLB_Ioo hab).lowerBounds_eq

@[to_dual]
/-
**isGLB_Ioc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isGLB_Ioc {a b : γ} (hab : a < b) : IsGLB (Ioc a b) a
参数：hab : a < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsGLB.of_subset_of_superset`：∀ {α : Type u_1} [inst : Preorder α] {a : α
} {s t p : Set α}, IsGLB s a → IsGLB p a → s ⊆ t → t ⊆ p → IsGLB t a
· 使用定理 `isGLB_Ioo`：isGLB_Ioo {a b : γ} (h : a < b) : IsGLB (Ioo a b) a
· 使用定理 `isGLB_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b ≤ a → IsGLB
 (Set.Icc b a) b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Set.Ioo_subset_Ioc_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioo b a ⊆ Set.Ioc b a
· 使用定理 `Set.Ioc_subset_Icc_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioc a b ⊆ Set.Icc a b
-/
theorem isGLB_Ioc {a b : γ} (hab : a < b) : IsGLB (Ioc a b) a :=
  (isGLB_Ioo hab).of_subset_of_superset (isGLB_Icc hab.le) Ioo_subset_Ioc_self Ioc_subset_Icc_self

@[to_dual]
/-
**lowerBounds_Ioc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lowerBounds_Ioc {a b : γ} (hab : a < b) : lowerBounds (Ioc a b) = Iic a
参数：hab : a < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsGLB.lowerBounds_eq`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α} {
a : α}, IsGLB s a → lowerBounds s = Set.Iic a
· 使用定理 `isGLB_Ioc`：isGLB_Ioc {a b : γ} (hab : a < b) : IsGLB (Ioc a b) a
-/
theorem lowerBounds_Ioc {a b : γ} (hab : a < b) : lowerBounds (Ioc a b) = Iic a :=
  (isGLB_Ioc hab).lowerBounds_eq

end

@[to_dual]
/-
**bddBelow_iff_subset_Ici** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：bddBelow_iff_subset_Ici : BddBelow s ↔ exists a, s subseteq Ici a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem bddBelow_iff_subset_Ici : BddBelow s ↔ ∃ a, s ⊆ Ici a :=
  Iff.rfl

@[to_dual none]
/-
**bddBelow_bddAbove_iff_subset_Icc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：bddBelow_bddAbove_iff_subset_Icc : BddBelow s ∧ BddAbove s ↔ exists a b, s
 subseteq Icc a b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Ici_inter_Iic`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, Set.I
ci a ∩ Set.Iic b = Set.Icc a b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem bddBelow_bddAbove_iff_subset_Icc : BddBelow s ∧ BddAbove s ↔ ∃ a b, s ⊆ Icc a b := by
  simp [Ici_inter_Iic.symm, subset_inter_iff, bddBelow_iff_subset_Ici,
    bddAbove_iff_subset_Iic, exists_and_left, exists_and_right]

/-!
#### Univ
-/

/-
**isGreatest_univ_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {a : α}, IsGreatest Set.univ a ↔ IsTo
p a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
#### Univ
-/
@[to_dual (attr := simp)] theorem isGreatest_univ_iff : IsGreatest univ a ↔ IsTop a := by
  simp [IsGreatest, mem_upperBounds, IsTop]

@[to_dual]
/-
**isGreatest_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isGreatest_univ [OrderTop α] : IsGreatest (univ : Set α) ⊤
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isGreatest_univ_iff`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, IsGre
atest Set.univ a ↔ IsTop a
· 使用定理 `isTop_top`：isTop_top : IsTop (⊤ : α)
-/
theorem isGreatest_univ [OrderTop α] : IsGreatest (univ : Set α) ⊤ :=
  isGreatest_univ_iff.2 isTop_top

@[to_dual (attr := simp)]
/-
**OrderTop.upperBounds_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：OrderTop.upperBounds_univ [PartialOrder γ] [OrderTop γ] : upperBounds (uni
v : Set γ) = {⊤}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsGreatest.upperBounds_eq`：∀ {α : Type u_1} [inst : Preorder α] {s : Set
 α} {a : α}, IsGreatest s a → upperBounds s = Set.Ici a
· 使用定理 `isGreatest_univ`：isGreatest_univ [OrderTop α] : IsGreatest (univ : Set α
) ⊤
· 使用定理 `Set.Ici_top`：Ici_top [PartialOrder α] [OrderTop α] : Ici (⊤ : α) = {⊤}
-/
theorem OrderTop.upperBounds_univ [PartialOrder γ] [OrderTop γ] :
    upperBounds (univ : Set γ) = {⊤} := by rw [isGreatest_univ.upperBounds_eq, Ici_top]

@[to_dual]
/-
**isLUB_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLUB_univ [OrderTop α] : IsLUB (univ : Set α) ⊤
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsGreatest.isLUB`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α} {a : 
α}, IsGreatest s a → IsLUB s a
· 使用定理 `isGreatest_univ`：isGreatest_univ [OrderTop α] : IsGreatest (univ : Set α
) ⊤
-/
theorem isLUB_univ [OrderTop α] : IsLUB (univ : Set α) ⊤ :=
  isGreatest_univ.isLUB

@[to_dual (attr := simp)]
/-
**NoTopOrder.upperBounds_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：NoTopOrder.upperBounds_univ [NoTopOrder α] : upperBounds (univ : Set α) = 
∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_of_subset_empty`：eq_empty_of_subset_empty {s : Set α} : s s
ubseteq ∅ -> s = ∅
· 使用定理 `not_isTop`：∀ {α : Type u_1} [inst : LE α] [NoTopOrder α] (a : α), ¬IsTop
 a
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
-/
theorem NoTopOrder.upperBounds_univ [NoTopOrder α] : upperBounds (univ : Set α) = ∅ :=
  eq_empty_of_subset_empty fun b hb =>
    not_isTop b fun x => hb (mem_univ x)

@[to_dual (attr := simp)]
/-
**not_bddAbove_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_bddAbove_univ [NoTopOrder α] : ¬BddAbove (univ : Set α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NoTopOrder.upperBounds_univ`：NoTopOrder.upperBounds_univ [NoTopOrder α] 
: upperBounds (univ : Set α) = ∅
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem not_bddAbove_univ [NoTopOrder α] : ¬BddAbove (univ : Set α) := by simp [BddAbove]

/-!
#### Empty set
-/


@[to_dual (attr := simp)]
/-
**upperBounds_empty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：upperBounds_empty : upperBounds (∅ : Set α) = univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g

--- 原说明 ---
#### Empty set
-/
theorem upperBounds_empty : upperBounds (∅ : Set α) = univ := by
  simp only [upperBounds, eq_univ_iff_forall, mem_ofPred_eq, forall_mem_empty, forall_true_iff]

@[to_dual (attr := simp)]
/-
**bddAbove_empty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：bddAbove_empty [Nonempty α] : BddAbove (∅ : Set α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `upperBounds_empty`：upperBounds_empty : upperBounds (∅ : Set α) = univ
-/
theorem bddAbove_empty [Nonempty α] : BddAbove (∅ : Set α) := by
  simp only [BddAbove, upperBounds_empty, univ_nonempty]
/-
**isGLB_empty_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {a : α}, IsGLB ∅ a ↔ IsTop a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `lowerBounds_empty`：∀ {α : Type u_1} [inst : Preorder α], lowerBounds ∅ =
 Set.univ
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[to_dual (attr := simp)] theorem isGLB_empty_iff : IsGLB ∅ a ↔ IsTop a := by
  simp [IsGLB]

@[to_dual]
/-
**isGLB_empty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isGLB_empty [OrderTop α] : IsGLB ∅ (⊤ : α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isGLB_empty_iff`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, IsGLB ∅ a
 ↔ IsTop a
· 使用定理 `isTop_top`：isTop_top : IsTop (⊤ : α)
-/
theorem isGLB_empty [OrderTop α] : IsGLB ∅ (⊤ : α) :=
  isGLB_empty_iff.2 isTop_top

@[to_dual]
/-
**IsLUB.nonempty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLUB.nonempty [NoBotOrder α] (hs : IsLUB s a) : s.Nonempty
参数：hs : IsLUB s a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.nonempty_iff_ne_empty`：nonempty_iff_ne_empty : s.Nonempty ↔ s != ∅
· 使用定理 `not_isBot`：not_isBot [NoBotOrder α] (a : α) : ¬IsBot a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `upperBounds_empty`：upperBounds_empty : upperBounds (∅ : Set α) = univ
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
-/
theorem IsLUB.nonempty [NoBotOrder α] (hs : IsLUB s a) : s.Nonempty :=
  nonempty_iff_ne_empty.2 fun h =>
    not_isBot a fun _ => hs.right <| by rw [h, upperBounds_empty]; exact mem_univ _

@[to_dual]
/-
**nonempty_of_not_bddAbove** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nonempty_of_not_bddAbove [ha : Nonempty α] (h : ¬BddAbove s) : s.Nonempty
参数：h : ¬BddAbove s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nonempty.elim`：∀ {α : Sort u} {p : Prop}, Nonempty α → (∀ (a : α), p) → 
p
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_bddAbove_iff'`：not_bddAbove_iff' : ¬BddAbove s ↔ forall x, exists y 
in s, ¬y <= x
-/
theorem nonempty_of_not_bddAbove [ha : Nonempty α] (h : ¬BddAbove s) : s.Nonempty :=
  (Nonempty.elim ha) fun x => (not_bddAbove_iff'.1 h x).imp fun _ ha => ha.1

/-!
#### insert
-/


/-- Adding a point to a set preserves its boundedness above. -/
@[to_dual (attr := simp) /-- Adding a point to a set preserves its boundedness below. -/]
/-
**bddAbove_insert** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：bddAbove_insert [IsDirectedOrder α] {s : Set α} {a : α} : BddAbove (insert
 a s) ↔ BddAbove s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Adding a point to a set preserves its boundedness above.
-/
theorem bddAbove_insert [IsDirectedOrder α] {s : Set α} {a : α} :
    BddAbove (insert a s) ↔ BddAbove s := by
  simp only [insert_eq, bddAbove_union, bddAbove_singleton, true_and]

@[to_dual]
/-
**BddAbove.insert** 是 Mathlib 中的一个定理，位于命名空间 `BddAbove`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] [IsDirectedOrder α] {s : Set α} (a : 
α), BddAbove s → BddAbove (insert a s)
参数：a : α；insert a s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `bddAbove_insert`：bddAbove_insert [IsDirectedOrder α] {s : Set α} {a : α}
 : BddAbove (insert a s) ↔ BddAbove s
-/
protected theorem BddAbove.insert [IsDirectedOrder α] {s : Set α} (a : α) :
    BddAbove s → BddAbove (insert a s) :=
  bddAbove_insert.2

@[to_dual]
/-
**IsLUB.insert** 是 Mathlib 中的一个定理，位于命名空间 `IsLUB`。
形式化陈述：∀ {γ : Type u_3} [inst : SemilatticeSup γ] (a : γ) {b : γ} {s : Set γ}, Is
LUB s b → IsLUB (insert a s) (a ⊔ b)
参数：a : γ；insert a s；a ⊔ b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.insert_eq`：insert_eq (x : α) (s : Set α) : insert x s = ({x} : Set α
) union s
· 使用定理 `IsLUB.union`：IsLUB.union [SemilatticeSup γ] {a b : γ} {s t : Set γ} (hs 
: IsLUB s a) (ht : IsLUB t b) : IsLUB (s union t) (a ⊔ b)
· 使用定理 `isLUB_singleton`：isLUB_singleton : IsLUB {a} a
-/
protected theorem IsLUB.insert [SemilatticeSup γ] (a) {b} {s : Set γ} (hs : IsLUB s b) :
    IsLUB (insert a s) (a ⊔ b) := by
  rw [insert_eq]
  exact isLUB_singleton.union hs

@[to_dual]
/-
**IsGreatest.insert** 是 Mathlib 中的一个定理，位于命名空间 `IsGreatest`。
形式化陈述：∀ {γ : Type u_3} [inst : LinearOrder γ] (a : γ) {b : γ} {s : Set γ}, IsGre
atest s b → IsGreatest (insert a s) (max a b)
参数：a : γ；insert a s；max a b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.insert_eq`：insert_eq (x : α) (s : Set α) : insert x s = ({x} : Set α
) union s
· 使用定理 `IsGreatest.union`：∀ {γ : Type u_3} [inst : LinearOrder γ] {a b : γ} {s t
 : Set γ},   IsGreatest s a → IsGreatest t b → IsGreatest (s ∪ t) (max a b)
· 使用定理 `isGreatest_singleton`：isGreatest_singleton : IsGreatest {a} a
-/
protected theorem IsGreatest.insert [LinearOrder γ] (a) {b} {s : Set γ} (hs : IsGreatest s b) :
    IsGreatest (insert a s) (max a b) := by
  rw [insert_eq]
  exact isGreatest_singleton.union hs

@[to_dual (attr := simp)]
/-
**upperBounds_insert** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：upperBounds_insert (a : α) (s : Set α) : upperBounds (insert a s) = Ici a 
inter upperBounds s
参数：a : α；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.insert_eq`：insert_eq (x : α) (s : Set α) : insert x s = ({x} : Set α
) union s
· 使用定理 `upperBounds_union`：upperBounds_union : upperBounds (s union t) = upperBo
unds s inter upperBounds t
· 使用定理 `upperBounds_singleton`：upperBounds_singleton : upperBounds {a} = Ici a
-/
theorem upperBounds_insert (a : α) (s : Set α) :
    upperBounds (insert a s) = Ici a ∩ upperBounds s := by
  rw [insert_eq, upperBounds_union, upperBounds_singleton]

/-- When there is a global maximum, every set is bounded above. -/
@[to_dual (attr := simp) /-- When there is a global minimum, every set is bounded below. -/]
/-
**OrderTop.bddAbove** 是 Mathlib 中的一个定理，位于命名空间 `OrderTop`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] [OrderTop α] (s : Set α), BddAbove s
参数：s : Set α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderTop.le_top`：∀ {α : Type u} {inst : LE α} [self : OrderTop α] (a : α
), a ≤ ⊤

--- 原说明 ---
When there is a global maximum, every set is bounded above.
-/
protected theorem OrderTop.bddAbove [OrderTop α] (s : Set α) : BddAbove s :=
  ⟨⊤, fun a _ => OrderTop.le_top a⟩

/-- Sets are automatically bounded or cobounded in complete lattices. To use the same statements
in complete and conditionally complete lattices but let automation fill automatically the
boundedness proofs in complete lattices, we use the tactic `bddDefault` in the statements,
in the form `(hA : BddAbove A := by bddDefault)`. -/
macro "bddDefault" : tactic =>
  `(tactic| first
    | apply OrderTop.bddAbove
    | apply OrderBot.bddBelow)

/-!
#### Pair
-/


@[to_dual]
/-
**isLUB_pair** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLUB_pair [SemilatticeSup γ] {a b : γ} : IsLUB {a, b} (a ⊔ b)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLUB.insert`：∀ {γ : Type u_3} [inst : SemilatticeSup γ] (a : γ) {b : γ}
 {s : Set γ}, IsLUB s b → IsLUB (insert a s) (a ⊔ b)
· 使用定理 `isLUB_singleton`：isLUB_singleton : IsLUB {a} a

--- 原说明 ---
#### Pair
-/
theorem isLUB_pair [SemilatticeSup γ] {a b : γ} : IsLUB {a, b} (a ⊔ b) :=
  isLUB_singleton.insert _

@[to_dual]
/-
**isGreatest_pair** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isGreatest_pair [LinearOrder γ] {a b : γ} : IsGreatest {a, b} (max a b)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsGreatest.insert`：∀ {γ : Type u_3} [inst : LinearOrder γ] (a : γ) {b : 
γ} {s : Set γ}, IsGreatest s b → IsGreatest (insert a s) (max a b)
· 使用定理 `isGreatest_singleton`：isGreatest_singleton : IsGreatest {a} a
-/
theorem isGreatest_pair [LinearOrder γ] {a b : γ} : IsGreatest {a, b} (max a b) :=
  isGreatest_singleton.insert _

/-!
#### Lower/upper bounds
-/


@[to_dual (attr := simp)]
/-
**isLUB_lowerBounds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLUB_lowerBounds : IsLUB (lowerBounds s) a ↔ IsGLB s a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `subset_upperBounds_lowerBounds`：∀ {α : Type u_1} [inst : Preorder α] (s 
: Set α), s ⊆ upperBounds (lowerBounds s)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `IsGreatest.isLUB`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α} {a : 
α}, IsGreatest s a → IsLUB s a

--- 原说明 ---
#### Lower/upper bounds
-/
theorem isLUB_lowerBounds : IsLUB (lowerBounds s) a ↔ IsGLB s a :=
  ⟨fun H => ⟨fun _ hx => H.2 <| subset_upperBounds_lowerBounds s hx, H.1⟩, IsGreatest.isLUB⟩

end

section Minimal

variable [Preorder α] {s : Set α} {a b : α}

@[to_dual]
/-
**DirectedOn.le_of_minimal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DirectedOn.le_of_minimal (h : DirectedOn (fun x y => y <= x) s) (hMin : Mi
nimal (· in s) a) (hb : b in s) : a <= b
参数：h : DirectedOn (fun x y => y <= x) s；hMin : Minimal (· in s) a；hb : b in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem DirectedOn.le_of_minimal (h : DirectedOn (fun x y ↦ y ≤ x) s) (hMin : Minimal (· ∈ s) a)
    (hb : b ∈ s) : a ≤ b := by
  obtain ⟨z, hz, hza, hzb⟩ := h a hMin.1 b hb
  exact (hMin.2 hz hza).trans hzb

@[to_dual]
/-
**DirectedOn.minimal_iff_isLeast** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DirectedOn.minimal_iff_isLeast (h : DirectedOn (fun x y => y <= x) s) : Mi
nimal (· in s) a ↔ IsLeast s a
参数：h : DirectedOn (fun x y => y <= x) s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `DirectedOn.le_of_minimal`：DirectedOn.le_of_minimal (h : DirectedOn (fun 
x y => y <= x) s) (hMin : Minimal (· in s) a) (hb : b in s) : a <= b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem DirectedOn.minimal_iff_isLeast (h : DirectedOn (fun x y ↦ y ≤ x) s) :
    Minimal (· ∈ s) a ↔ IsLeast s a :=
  ⟨fun hMin ↦ ⟨hMin.1, fun _ hy ↦ h.le_of_minimal hMin hy⟩, fun h ↦ ⟨h.1, fun _ hy _ ↦ h.2 hy⟩⟩

end Minimal

@[to_dual]
/-
**minimal_iff_isLeast** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：minimal_iff_isLeast [LinearOrder α] {s : Set α} {a : α} : Minimal (· in s)
 a ↔ IsLeast s a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirectedOn.minimal_iff_isLeast`：DirectedOn.minimal_iff_isLeast (h : Dire
ctedOn (fun x y => y <= x) s) : Minimal (· in s) a ↔ IsLeast s a
· 使用定理 `Std.Total.directedOn`：Std.Total.directedOn [Std.Total r] (s : Set α) : D
irectedOn r s
· 使用定理 `LE.total'`：∀ {α : Type u} [inst : LinearOrder α], Std.Total fun x1 x2 =>
 x2 ≤ x1
-/
theorem minimal_iff_isLeast [LinearOrder α] {s : Set α} {a : α} :
    Minimal (· ∈ s) a ↔ IsLeast s a :=
  (Std.Total.directedOn s).minimal_iff_isLeast

/-!
### (In)equalities with the least upper bound and the greatest lower bound
-/


section Preorder

variable [Preorder α] [Preorder β] {s s' : Set α} {t : Set β} {a b : α}

@[to_dual self (reorder := a b, ha hb)]
/-
**lowerBounds_le_upperBounds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {s : Set α} {a b : α}, a ∈ lowerBound
s s → b ∈ upperBounds s → s.Nonempty → a ≤ b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
-/
theorem lowerBounds_le_upperBounds (ha : a ∈ lowerBounds s) (hb : b ∈ upperBounds s) :
    s.Nonempty → a ≤ b
  | ⟨_, hc⟩ => le_trans (ha hc) (hb hc)

@[to_dual none]
/-
**lowerBounds_le_upperBounds_of_nonempty_inter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lowerBounds_le_upperBounds_of_nonempty_inter (h : (s inter s').Nonempty) (
ha : a in lowerBounds s) (hb : b in upperBounds s') : a <= b
参数：h : (s inter s').Nonempty；ha : a in lowerBounds s；hb : b in upperBounds s'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
-/
theorem lowerBounds_le_upperBounds_of_nonempty_inter (h : (s ∩ s').Nonempty)
    (ha : a ∈ lowerBounds s) (hb : b ∈ upperBounds s') : a ≤ b := by
  have ⟨x, hx, hx'⟩ := h
  exact le_trans (ha hx) (hb hx')

@[to_dual self (reorder := a b, ha hb)]
/-
**isGLB_le_isLUB** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isGLB_le_isLUB (ha : IsGLB s a) (hb : IsLUB s b) (hs : s.Nonempty) : a <= 
b
参数：ha : IsGLB s a；hb : IsLUB s b；hs : s.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lowerBounds_le_upperBounds`：∀ {α : Type u_1} [inst : Preorder α] {s : Se
t α} {a b : α}, a ∈ lowerBounds s → b ∈ upperBounds s → s.Nonempty → a ≤ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem isGLB_le_isLUB (ha : IsGLB s a) (hb : IsLUB s b) (hs : s.Nonempty) : a ≤ b :=
  lowerBounds_le_upperBounds ha.1 hb.1 hs

@[to_dual none]
/-
**isGLB_le_isLUB_of_nonempty_inter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isGLB_le_isLUB_of_nonempty_inter (h : (s inter s').Nonempty) (ha : IsGLB s
 a) (hb : IsLUB s' b) : a <= b
参数：h : (s inter s').Nonempty；ha : IsGLB s a；hb : IsLUB s' b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lowerBounds_le_upperBounds_of_nonempty_inter`：lowerBounds_le_upperBounds
_of_nonempty_inter (h : (s inter s').Nonempty) (ha : a in lowerBounds s) (hb : b
 in upperBounds s') : a <= b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem isGLB_le_isLUB_of_nonempty_inter (h : (s ∩ s').Nonempty) (ha : IsGLB s a)
    (hb : IsLUB s' b) : a ≤ b :=
  lowerBounds_le_upperBounds_of_nonempty_inter h ha.left hb.left

@[to_dual lt_isGLB_iff]
/-
**isLUB_lt_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLUB_lt_iff (ha : IsLUB s a) : a < b ↔ exists c in upperBounds s, c < b
参数：ha : IsLUB s a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem isLUB_lt_iff (ha : IsLUB s a) : a < b ↔ ∃ c ∈ upperBounds s, c < b :=
  ⟨fun hb => ⟨a, ha.1, hb⟩, fun ⟨_, hcs, hcb⟩ => lt_of_le_of_lt (ha.2 hcs) hcb⟩

@[to_dual self (reorder := a b, x y, ha hb, hx hy)]
/-
**le_of_isLUB_le_isGLB** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_of_isLUB_le_isGLB {x y} (ha : IsGLB s a) (hb : IsLUB s b) (hab : b <= a
) (hx : x in s) (hy : y in s) : x <= y
参数：ha : IsGLB s a；hb : IsLUB s b；hab : b <= a；hx : x in s；hy : y in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem le_of_isLUB_le_isGLB {x y} (ha : IsGLB s a) (hb : IsLUB s b) (hab : b ≤ a) (hx : x ∈ s)
    (hy : y ∈ s) : x ≤ y :=
  calc
    x ≤ b := hb.1 hx
    _ ≤ a := hab
    _ ≤ y := ha.1 hy

@[to_dual (attr := simp)]
/-
**upperBounds_prod** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：upperBounds_prod (hs : s.Nonempty) (ht : t.Nonempty) : upperBounds (s ×ˢ t
) = upperBounds s ×ˢ upperBounds t
参数：hs : s.Nonempty；ht : t.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.nonempty_coe_sort`：nonempty_coe_sort {s : Set α} : Nonempty ↥s ↔ s.N
onempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
lemma upperBounds_prod (hs : s.Nonempty) (ht : t.Nonempty) :
    upperBounds (s ×ˢ t) = upperBounds s ×ˢ upperBounds t := by
  ext; rw [← nonempty_coe_sort] at hs ht; aesop (add simp [upperBounds, Prod.le_def, forall_and])

@[to_dual]
/-
**IsLUB.prod** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsLUB.prod {b : β} (hs : s.Nonempty) (ht : t.Nonempty) (ha : IsLUB s a) (h
b : IsLUB t b) : IsLUB (s ×ˢ t) (a, b)
参数：hs : s.Nonempty；ht : t.Nonempty；ha : IsLUB s a；hb : IsLUB t b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `upperBounds_prod`：upperBounds_prod (hs : s.Nonempty) (ht : t.Nonempty) :
 upperBounds (s ×ˢ t) = upperBounds s ×ˢ upperBounds t
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma IsLUB.prod {b : β} (hs : s.Nonempty) (ht : t.Nonempty) (ha : IsLUB s a) (hb : IsLUB t b) :
    IsLUB (s ×ˢ t) (a, b) := by simp_all +contextual [IsLUB, IsLeast, lowerBounds]
/-
**isLUB_congr_of_antisymmRel** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLUB_congr_of_antisymmRel {a b : α} (h : AntisymmRel (· <= ·) a b) : IsLU
B s a ↔ IsLUB s b
参数：h : AntisymmRel (· <= ·) a b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AntisymmRel.le_congr_left`：AntisymmRel.le_congr_left (h : AntisymmRel (·
 <= ·) a b) : a <= c ↔ b <= c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isLUB_congr_of_antisymmRel {a b : α} (h : AntisymmRel (· ≤ ·) a b) :
    IsLUB s a ↔ IsLUB s b := by
  simp [isLUB_iff_le_iff, h.le_congr_left]

-- TODO: `to_dual` doesn't work with `AntisymmRel`.
/-
**isGLB_congr_of_antisymmRel** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isGLB_congr_of_antisymmRel {a b : α} (h : AntisymmRel (· <= ·) a b) : IsGL
B s a ↔ IsGLB s b
参数：h : AntisymmRel (· <= ·) a b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AntisymmRel.le_congr_right`：AntisymmRel.le_congr_right (h : AntisymmRel 
(· <= ·) b c) : a <= b ↔ a <= c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isGLB_congr_of_antisymmRel {a b : α} (h : AntisymmRel (· ≤ ·) a b) :
    IsGLB s a ↔ IsGLB s b := by
  simp [isGLB_iff_le_iff, h.le_congr_right]

end Preorder

section PartialOrder

variable [PartialOrder α] {s : Set α} {a b : α}

@[to_dual]
/-
**IsLeast.unique** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLeast.unique (Ha : IsLeast s a) (Hb : IsLeast s b) : a = b
参数：Ha : IsLeast s a；Hb : IsLeast s b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem IsLeast.unique (Ha : IsLeast s a) (Hb : IsLeast s b) : a = b :=
  le_antisymm (Ha.right Hb.left) (Hb.right Ha.left)

@[to_dual]
/-
**IsLeast.isLeast_iff_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLeast.isLeast_iff_eq (Ha : IsLeast s a) : IsLeast s b ↔ a = b
参数：Ha : IsLeast s a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLeast.unique`：IsLeast.unique (Ha : IsLeast s a) (Hb : IsLeast s b) : a
 = b
-/
theorem IsLeast.isLeast_iff_eq (Ha : IsLeast s a) : IsLeast s b ↔ a = b :=
  Iff.intro Ha.unique fun h => h ▸ Ha

@[to_dual]
/-
**IsLUB.unique** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLUB.unique (Ha : IsLUB s a) (Hb : IsLUB s b) : a = b
参数：Ha : IsLUB s a；Hb : IsLUB s b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLeast.unique`：IsLeast.unique (Ha : IsLeast s a) (Hb : IsLeast s b) : a
 = b
-/
theorem IsLUB.unique (Ha : IsLUB s a) (Hb : IsLUB s b) : a = b :=
  IsLeast.unique Ha Hb

@[to_dual self (reorder := a b, Ha Hb)]
/-
**Set.subsingleton_of_isLUB_le_isGLB** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.subsingleton_of_isLUB_le_isGLB (Ha : IsGLB s a) (Hb : IsLUB s b) (hab 
: b <= a) : s.Subsingleton
参数：Ha : IsGLB s a；Hb : IsLUB s b；hab : b <= a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `le_of_isLUB_le_isGLB`：le_of_isLUB_le_isGLB {x y} (ha : IsGLB s a) (hb : 
IsLUB s b) (hab : b <= a) (hx : x in s) (hy : y in s) : x <= y
-/
theorem Set.subsingleton_of_isLUB_le_isGLB (Ha : IsGLB s a) (Hb : IsLUB s b) (hab : b ≤ a) :
    s.Subsingleton := fun _ hx _ hy =>
  le_antisymm (le_of_isLUB_le_isGLB Ha Hb hab hx hy) (le_of_isLUB_le_isGLB Ha Hb hab hy hx)

@[to_dual self (reorder := a b, Ha Hb)]
/-
**isGLB_lt_isLUB_of_ne** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isGLB_lt_isLUB_of_ne (Ha : IsGLB s a) (Hb : IsLUB s b) {x y} (Hx : x in s)
 (Hy : y in s) (Hxy : x != y) : a < b
参数：Ha : IsGLB s a；Hb : IsLUB s b；Hx : x in s；Hy : y in s；Hxy : x != y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `lt_iff_le_not_ge`：lt_iff_le_not_ge : a < b ↔ a <= b ∧ ¬b <= a
· 使用定理 `lowerBounds_le_upperBounds`：∀ {α : Type u_1} [inst : Preorder α] {s : Se
t α} {a b : α}, a ∈ lowerBounds s → b ∈ upperBounds s → s.Nonempty → a ≤ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Set.subsingleton_of_isLUB_le_isGLB`：Set.subsingleton_of_isLUB_le_isGLB (
Ha : IsGLB s a) (Hb : IsLUB s b) (hab : b <= a) : s.Subsingleton
-/
theorem isGLB_lt_isLUB_of_ne (Ha : IsGLB s a) (Hb : IsLUB s b) {x y} (Hx : x ∈ s) (Hy : y ∈ s)
    (Hxy : x ≠ y) : a < b :=
  lt_iff_le_not_ge.2
    ⟨lowerBounds_le_upperBounds Ha.1 Hb.1 ⟨x, Hx⟩, fun hab =>
      Hxy <| Set.subsingleton_of_isLUB_le_isGLB Ha Hb hab Hx Hy⟩

end PartialOrder

section LinearOrder

variable [LinearOrder α] {s : Set α} {a b : α}

@[to_dual isGLB_lt_iff]
/-
**lt_isLUB_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lt_isLUB_iff (h : IsLUB s a) : b < a ↔ exists c in s, b < c
参数：h : IsLUB s a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `isLUB_le_iff`：isLUB_le_iff (h : IsLUB s a) : a <= b ↔ b in upperBounds s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem lt_isLUB_iff (h : IsLUB s a) : b < a ↔ ∃ c ∈ s, b < c := by
  simp_rw [← not_le, isLUB_le_iff h, mem_upperBounds, not_forall, not_le, exists_prop]

@[to_dual none]
/-
**IsLUB.exists_between** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLUB.exists_between (h : IsLUB s a) (hb : b < a) : exists c in s, b < c ∧
 c <= a
参数：h : IsLUB s a；hb : b < a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `lt_isLUB_iff`：lt_isLUB_iff (h : IsLUB s a) : b < a ↔ exists c in s, b < 
c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem IsLUB.exists_between (h : IsLUB s a) (hb : b < a) : ∃ c ∈ s, b < c ∧ c ≤ a :=
  let ⟨c, hcs, hbc⟩ := (lt_isLUB_iff h).1 hb
  ⟨c, hcs, hbc, h.1 hcs⟩

@[to_dual none]
/-
**IsLUB.exists_between'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLUB.exists_between' (h : IsLUB s a) (h' : a ∉ s) (hb : b < a) : exists c
 in s, b < c ∧ c < a
参数：h : IsLUB s a；h' : a ∉ s；hb : b < a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLUB.exists_between`：IsLUB.exists_between (h : IsLUB s a) (hb : b < a) 
: exists c in s, b < c ∧ c <= a
· 使用定理 `LE.le.lt_of_ne`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a ≠ b → a < b
-/
theorem IsLUB.exists_between' (h : IsLUB s a) (h' : a ∉ s) (hb : b < a) : ∃ c ∈ s, b < c ∧ c < a :=
  let ⟨c, hcs, hbc, hca⟩ := h.exists_between hb
  ⟨c, hcs, hbc, hca.lt_of_ne fun hac => h' <| hac ▸ hcs⟩

@[to_dual none]
/-
**IsGLB.exists_between** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsGLB.exists_between (h : IsGLB s a) (hb : a < b) : exists c in s, a <= c 
∧ c < b
参数：h : IsGLB s a；hb : a < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isGLB_lt_iff`：∀ {α : Type u_1} [inst : LinearOrder α] {s : Set α} {a b :
 α}, IsGLB s a → (a < b ↔ ∃ c ∈ s, c < b)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem IsGLB.exists_between (h : IsGLB s a) (hb : a < b) : ∃ c ∈ s, a ≤ c ∧ c < b :=
  let ⟨c, hcs, hbc⟩ := (isGLB_lt_iff h).1 hb
  ⟨c, hcs, h.1 hcs, hbc⟩

@[to_dual none]
/-
**IsGLB.exists_between'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsGLB.exists_between' (h : IsGLB s a) (h' : a ∉ s) (hb : a < b) : exists c
 in s, a < c ∧ c < b
参数：h : IsGLB s a；h' : a ∉ s；hb : a < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsGLB.exists_between`：IsGLB.exists_between (h : IsGLB s a) (hb : a < b) 
: exists c in s, a <= c ∧ c < b
· 使用定理 `LE.le.lt_of_ne`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a ≠ b → a < b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem IsGLB.exists_between' (h : IsGLB s a) (h' : a ∉ s) (hb : a < b) : ∃ c ∈ s, a < c ∧ c < b :=
  let ⟨c, hcs, hac, hcb⟩ := h.exists_between hb
  ⟨c, hcs, hac.lt_of_ne fun hac => h' <| hac.symm ▸ hcs, hcb⟩

end LinearOrder

/-
**isGreatest_himp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isGreatest_himp [GeneralizedHeytingAlgebra α] (a b : α) : IsGreatest {w | 
w ⊓ a <= b} (a ⇨ b)
参数：a b : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `himp_inf_self`：himp_inf_self (a b : α) : (a ⇨ b) ⊓ a = b ⊓ a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem isGreatest_himp [GeneralizedHeytingAlgebra α] (a b : α) :
    IsGreatest {w | w ⊓ a ≤ b} (a ⇨ b) := by
  simp [IsGreatest, mem_upperBounds]
/-
**isLeast_sdiff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLeast_sdiff [GeneralizedCoheytingAlgebra α] (a b : α) : IsLeast {w | a <
= b ⊔ w} (a \ b)
参数：a b : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sup_sdiff_self`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] 
(a b : α), a ⊔ b \ a = a ⊔ b
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem isLeast_sdiff [GeneralizedCoheytingAlgebra α] (a b : α) :
    IsLeast {w | a ≤ b ⊔ w} (a \ b) := by
  simp [IsLeast, mem_lowerBounds]
/-
**isGreatest_compl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isGreatest_compl [HeytingAlgebra α] (a : α) : IsGreatest {w | Disjoint w a
} (aᶜ)
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `himp_bot`：himp_bot (a : α) : a ⇨ ⊥ = aᶜ
· 使用定理 `isGreatest_himp`：isGreatest_himp [GeneralizedHeytingAlgebra α] (a b : α)
 : IsGreatest {w | w ⊓ a <= b} (a ⇨ b)
-/
theorem isGreatest_compl [HeytingAlgebra α] (a : α) :
    IsGreatest {w | Disjoint w a} (aᶜ) := by
  simpa only [himp_bot, disjoint_iff_inf_le] using isGreatest_himp a ⊥
/-
**isLeast_hnot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLeast_hnot [CoheytingAlgebra α] (a : α) : IsLeast {w | Codisjoint a w} (
￢a)
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CoheytingAlgebra.top_sdiff`：∀ {α : Type u_4} [self : CoheytingAlgebra α]
 (a : α), ⊤ \ a = ￢a
· 使用定理 `isLeast_sdiff`：isLeast_sdiff [GeneralizedCoheytingAlgebra α] (a b : α) :
 IsLeast {w | a <= b ⊔ w} (a \ b)
-/
theorem isLeast_hnot [CoheytingAlgebra α] (a : α) :
    IsLeast {w | Codisjoint a w} (￢a) := by
  simpa only [CoheytingAlgebra.top_sdiff, codisjoint_iff_le_sup] using isLeast_sdiff ⊤ a
/-
**Nat.instDecidableIsLeast** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Nat.instDecidableIsLeast (p : Nat -> Prop) (n : Nat) [DecidablePred p] : D
ecidable (IsLeast { n : Nat | p n } n)
参数：p : Nat -> Prop；n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Nat.instDecidableIsLeast (p : ℕ → Prop) (n : ℕ) [DecidablePred p] :
    Decidable (IsLeast { n : ℕ | p n } n) :=
  decidable_of_iff (p n ∧ ∀ k < n, ¬p k) <| .and .rfl <| by
    simp [mem_lowerBounds, @imp_not_comm _ (p _)]

/-- An alternative constructor for `SemilatticeSup` using `IsLUB`. -/
@[to_dual (attr := instance_reducible)
/-- An alternative constructor for `SemilatticeInf` using `IsGLB`. -/]
/-
**SemilatticeSup.ofIsLUB** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：SemilatticeSup.ofIsLUB [PartialOrder α] (sup : α -> α -> α) (isLUB_pair : 
forall a b, IsLUB {a, b} (sup a b)) : SemilatticeSup α where sup
参数：sup : α -> α -> α；isLUB_pair : forall a b, IsLUB {a, b} (sup a b)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def SemilatticeSup.ofIsLUB [PartialOrder α] (sup : α → α → α)
    (isLUB_pair : ∀ a b, IsLUB {a, b} (sup a b)) :
    SemilatticeSup α where
  sup := sup
  le_sup_left a b := (isLUB_pair a b).1 (mem_insert _ _)
  le_sup_right a b := (isLUB_pair a b).1 (mem_insert_of_mem _ (mem_singleton _))
  sup_le a b _ hac hbc := (isLUB_pair a b).2 (forall_insert_of_forall (forall_eq.mpr hbc) hac)

/-- An alternative constructor for `Lattice` using `IsLUB` and `IsGLB`. -/
@[instance_reducible, to_dual self (reorder := 3 4, 5 6)]
/-
**Lattice.ofIsLUBofIsGLB** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Lattice.ofIsLUBofIsGLB [PartialOrder α] (sup inf : α -> α -> α) (isLUB_pai
r : forall a b, IsLUB {a, b} (sup a b)) (isGLB_pair : forall a b, IsGLB {a, b} (
inf a b)) : Lattice α where __
参数：sup inf : α -> α -> α；isLUB_pair : forall a b, IsLUB {a, b} (sup a b)；isGLB_p
air : forall a b, IsGLB {a, b} (inf a b)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SemilatticeInf.inf_le_left`：∀ {α : Type u} [self : SemilatticeInf α] (a 
b : α), SemilatticeInf.inf a b ≤ a
· 使用定理 `SemilatticeInf.inf_le_right`：∀ {α : Type u} [self : SemilatticeInf α] (a
 b : α), SemilatticeInf.inf a b ≤ b
· 使用定理 `SemilatticeInf.le_inf`：∀ {α : Type u} [self : SemilatticeInf α] (a b c :
 α), a ≤ b → a ≤ c → a ≤ SemilatticeInf.inf b c

--- 原说明 ---
An alternative constructor for `Lattice` using `IsLUB` and `IsGLB`.
-/
def Lattice.ofIsLUBofIsGLB [PartialOrder α] (sup inf : α → α → α)
    (isLUB_pair : ∀ a b, IsLUB {a, b} (sup a b)) (isGLB_pair : ∀ a b, IsGLB {a, b} (inf a b)) :
    Lattice α where
  __ := SemilatticeSup.ofIsLUB sup isLUB_pair
  __ := SemilatticeInf.ofIsGLB inf isGLB_pair
