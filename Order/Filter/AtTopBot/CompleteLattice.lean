/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jeremy Avigad, Yury Kudryashov, Patrick Massot
-/
module

public import Mathlib.Order.ConditionallyCompleteLattice.Indexed
public import Mathlib.Order.Filter.AtTopBot.Tendsto

/-!
# `Filter.atTop` and `Filter.atBot` in (conditionally) complete lattices
-/

public section

assert_not_exists Finset

variable {ι ι' α β γ : Type*}

open Set

namespace Filter

@[nontriviality]
/-
**Filter.Subsingleton.atTop_eq** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Subsingleton`。
形式化陈述：∀ (α : Type u_6) [Subsingleton α] [inst : Preorder α], Filter.atTop = ⊤
参数：α : Type u_6。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `top_unique`：top_unique (h : ⊤ <= a) : a = ⊤
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.mem_principal`：∀ {α : Type u_1} {s t : Set α}, s ∈ Filter.princip
al t ↔ t ⊆ s
· 使用定理 `ciInf_subsingleton`：∀ {α : Type u_1} {ι : Sort u_4} [inst : Conditionall
yCompletePartialOrderInf α] [Subsingleton ι] (i : ι) (s : ι → α),   ⨅ i, s i = s
 i
· 使用定理 `Filter.atTop.eq_1`：∀ {α : Type u_3} [inst : Preorder α], Filter.atTop = 
⨅ a, Filter.principal (Set.Ici a)
· 使用定理 `Set.self_mem_Ici`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, a ∈ Set.
Ici a
-/
theorem Subsingleton.atTop_eq (α) [Subsingleton α] [Preorder α] : (atTop : Filter α) = ⊤ := by
  refine top_unique fun s hs x => ?_
  rw [atTop, ciInf_subsingleton x, mem_principal] at hs
  exact hs self_mem_Ici

@[nontriviality]
/-
**Filter.Subsingleton.atBot_eq** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Subsingleton`。
形式化陈述：∀ (α : Type u_6) [Subsingleton α] [inst : Preorder α], Filter.atBot = ⊤
参数：α : Type u_6。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Subsingleton.atTop_eq`：∀ (α : Type u_6) [Subsingleton α] [inst : 
Preorder α], Filter.atTop = ⊤
· 使用定理 `OrderDual.instSubsingleton`：∀ (α : Type u_2) [h : Subsingleton α], Subsi
ngleton αᵒᵈ
-/
theorem Subsingleton.atBot_eq (α) [Subsingleton α] [Preorder α] : (atBot : Filter α) = ⊤ :=
  @Subsingleton.atTop_eq αᵒᵈ _ _

/-- If `f` is a monotone function with bounded range
and `g` tends to `atTop` along a nontrivial filter,
then the indexed supremum of `f ∘ g` is equal to the indexed supremum of `f`.

The assumption `BddAbove (range f)` can be omitted,
if the codomain of `f` is a conditionally complete linear order or a complete lattice, see below.
-/
/-
**Filter._root_.Monotone.ciSup_comp_tendsto_atTop** 是 Mathlib 中的一个定理，位于命名空间 `Fil
ter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f` is a monotone function with bounded range
and `g` tends to `atTop` along a nontrivial filter,
then the indexed supremum of `f ∘ g` is equal to the indexed supremum of `f`.

The assumption `BddAbove (range f)` can be omitted,
if the codomain of `f` is a conditionally complete linear order or a complete la
ttice, see below.
-/
theorem _root_.Monotone.ciSup_comp_tendsto_atTop [Preorder β] [ConditionallyCompleteLattice γ]
    {l : Filter α} [l.NeBot] {f : β → γ} (hf : Monotone f) (hb : BddAbove (range f))
    {g : α → β} (hg : Tendsto g l atTop) : ⨆ a, f (g a) = ⨆ b, f b := by
  have : Nonempty α := nonempty_of_neBot l
  have : Nonempty β := .map g ‹_›
  rw [← csInf_upperBounds_range, ← csInf_upperBounds_range,
    ← hf.upperBounds_range_comp_tendsto_atTop hg, Function.comp_def]
  exacts [hb, hb.mono <| range_comp_subset_range _ _]

/-- If `f` is a monotone function with bounded range
and `g` tends to `atBot` along a nontrivial filter,
then the indexed infimum of `f ∘ g` is equal to the indexed infimum of `f`.

The assumption `BddBelow (range f)` can be omitted,
if the codomain of `f` is a conditionally complete linear order or a complete lattice, see below.
-/
/-
**Filter._root_.Monotone.ciInf_comp_tendsto_atBot** 是 Mathlib 中的一个定理，位于命名空间 `Fil
ter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f` is a monotone function with bounded range
and `g` tends to `atBot` along a nontrivial filter,
then the indexed infimum of `f ∘ g` is equal to the indexed infimum of `f`.

The assumption `BddBelow (range f)` can be omitted,
if the codomain of `f` is a conditionally complete linear order or a complete la
ttice, see below.
-/
theorem _root_.Monotone.ciInf_comp_tendsto_atBot [Preorder β] [ConditionallyCompleteLattice γ]
    {l : Filter α} [l.NeBot] {f : β → γ} (hf : Monotone f) (hb : BddBelow (range f))
    {g : α → β} (hg : Tendsto g l atBot) : ⨅ a, f (g a) = ⨅ b, f b :=
  hf.dual.ciSup_comp_tendsto_atTop hb hg

/-- If `f` is an antitone function with bounded range
and `g` tends to `atBot` along a nontrivial filter,
then the indexed supremum of `f ∘ g` is equal to the indexed supremum of `f`.

The assumption `BddAbove (range f)` can be omitted,
if the codomain of `f` is a conditionally complete linear order or a complete lattice, see below.
-/
/-
**Filter._root_.Antitone.ciSup_comp_tendsto_atBot** 是 Mathlib 中的一个定理，位于命名空间 `Fil
ter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f` is an antitone function with bounded range
and `g` tends to `atBot` along a nontrivial filter,
then the indexed supremum of `f ∘ g` is equal to the indexed supremum of `f`.

The assumption `BddAbove (range f)` can be omitted,
if the codomain of `f` is a conditionally complete linear order or a complete la
ttice, see below.
-/
theorem _root_.Antitone.ciSup_comp_tendsto_atBot [Preorder β] [ConditionallyCompleteLattice γ]
    {l : Filter α} [l.NeBot] {f : β → γ} (hf : Antitone f) (hb : BddAbove (range f))
    {g : α → β} (hg : Tendsto g l atBot) : ⨆ a, f (g a) = ⨆ b, f b :=
  hf.dual_left.ciSup_comp_tendsto_atTop hb hg

/-- If `f` is an antitone function with bounded range
and `g` tends to `atTop` along a nontrivial filter,
then the indexed infimum of `f ∘ g` is equal to the indexed infimum of `f`.

The assumption `BddBelow (range f)` can be omitted,
if the codomain of `f` is a conditionally complete linear order or a complete lattice, see below.
-/
/-
**Filter._root_.Antitone.ciInf_comp_tendsto_atTop** 是 Mathlib 中的一个定理，位于命名空间 `Fil
ter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f` is an antitone function with bounded range
and `g` tends to `atTop` along a nontrivial filter,
then the indexed infimum of `f ∘ g` is equal to the indexed infimum of `f`.

The assumption `BddBelow (range f)` can be omitted,
if the codomain of `f` is a conditionally complete linear order or a complete la
ttice, see below.
-/
theorem _root_.Antitone.ciInf_comp_tendsto_atTop [Preorder β] [ConditionallyCompleteLattice γ]
    {l : Filter α} [l.NeBot] {f : β → γ} (hf : Antitone f) (hb : BddBelow (range f))
    {g : α → β} (hg : Tendsto g l atTop) : ⨅ a, f (g a) = ⨅ b, f b :=
  hf.dual.ciSup_comp_tendsto_atBot hb hg

/-- If `f` is a monotone function taking values in a conditionally complete linear order
and `g` tends to `atTop` along a nontrivial filter,
then the indexed supremum of `f ∘ g` is equal to the indexed supremum of `f`. -/
/-
**Filter._root_.Monotone.ciSup_comp_tendsto_atTop_of_linearOrder** 是 Mathlib 中的一
个定理，位于命名空间 `Filter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f` is a monotone function taking values in a conditionally complete linear o
rder
and `g` tends to `atTop` along a nontrivial filter,
then the indexed supremum of `f ∘ g` is equal to the indexed supremum of `f`.
-/
theorem _root_.Monotone.ciSup_comp_tendsto_atTop_of_linearOrder [Preorder β]
    [ConditionallyCompleteLinearOrder γ] {l : Filter α} [l.NeBot] {f : β → γ} (hf : Monotone f)
    {g : α → β} (hg : Tendsto g l atTop) : ⨆ a, f (g a) = ⨆ b, f b := by
  if hb : BddAbove (range f) then
    exact hf.ciSup_comp_tendsto_atTop hb hg
  else
    rw [iSup, iSup, csSup_of_not_bddAbove, csSup_of_not_bddAbove hb]
    rwa [BddAbove, ← Function.comp_def f g, hf.upperBounds_range_comp_tendsto_atTop hg]

/-- If `f` is a monotone function taking values in a conditionally complete linear order
and `g` tends to `atBot` along a nontrivial filter,
then the indexed infimum of `f ∘ g` is equal to the indexed infimum of `f`. -/
/-
**Filter._root_.Monotone.ciInf_comp_tendsto_atBot_of_linearOrder** 是 Mathlib 中的一
个定理，位于命名空间 `Filter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f` is a monotone function taking values in a conditionally complete linear o
rder
and `g` tends to `atBot` along a nontrivial filter,
then the indexed infimum of `f ∘ g` is equal to the indexed infimum of `f`.
-/
theorem _root_.Monotone.ciInf_comp_tendsto_atBot_of_linearOrder [Preorder β]
    [ConditionallyCompleteLinearOrder γ] {l : Filter α} [l.NeBot] {f : β → γ} (hf : Monotone f)
    {g : α → β} (hg : Tendsto g l atBot) : ⨅ a, f (g a) = ⨅ b, f b :=
  hf.dual.ciSup_comp_tendsto_atTop_of_linearOrder hg

/-- If `f` is an antitone function taking values in a conditionally complete linear order
and `g` tends to `atTop` along a nontrivial filter,
then the indexed infimum of `f ∘ g` is equal to the indexed infimum of `f`. -/
/-
**Filter._root_.Antitone.ciInf_comp_tendsto_atTop_of_linearOrder** 是 Mathlib 中的一
个定理，位于命名空间 `Filter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f` is an antitone function taking values in a conditionally complete linear 
order
and `g` tends to `atTop` along a nontrivial filter,
then the indexed infimum of `f ∘ g` is equal to the indexed infimum of `f`.
-/
theorem _root_.Antitone.ciInf_comp_tendsto_atTop_of_linearOrder [Preorder β]
    [ConditionallyCompleteLinearOrder γ] {l : Filter α} [l.NeBot] {f : β → γ} (hf : Antitone f)
    {g : α → β} (hg : Tendsto g l atTop) : ⨅ a, f (g a) = ⨅ b, f b :=
  hf.dual_left.ciInf_comp_tendsto_atBot_of_linearOrder hg

/-- If `f` is an antitone function taking values in a conditionally complete linear order
and `g` tends to `atBot` along a nontrivial filter,
then the indexed supremum of `f ∘ g` is equal to the indexed supremum of `f`. -/
/-
**Filter._root_.Antitone.ciSup_comp_tendsto_atBot_of_linearOrder** 是 Mathlib 中的一
个定理，位于命名空间 `Filter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f` is an antitone function taking values in a conditionally complete linear 
order
and `g` tends to `atBot` along a nontrivial filter,
then the indexed supremum of `f ∘ g` is equal to the indexed supremum of `f`.
-/
theorem _root_.Antitone.ciSup_comp_tendsto_atBot_of_linearOrder [Preorder β]
    [ConditionallyCompleteLinearOrder γ] {l : Filter α} [l.NeBot] {f : β → γ} (hf : Antitone f)
    {g : α → β} (hg : Tendsto g l atBot) : ⨆ a, f (g a) = ⨆ b, f b :=
  hf.dual_left.ciSup_comp_tendsto_atTop_of_linearOrder hg

/-- If `f` is a monotone function taking values in a complete lattice
and `g` tends to `atTop` along a nontrivial filter,
then the indexed supremum of `f ∘ g` is equal to the indexed supremum of `f`. -/
/-
**Filter._root_.Monotone.iSup_comp_tendsto_atTop** 是 Mathlib 中的一个定理，位于命名空间 `Filt
er`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f` is a monotone function taking values in a complete lattice
and `g` tends to `atTop` along a nontrivial filter,
then the indexed supremum of `f ∘ g` is equal to the indexed supremum of `f`.
-/
theorem _root_.Monotone.iSup_comp_tendsto_atTop
    [Preorder β] [ConditionallyCompleteLattice γ] [OrderTop γ]
    {l : Filter α} [l.NeBot] {f : β → γ} (hf : Monotone f) {g : α → β} (hg : Tendsto g l atTop) :
    ⨆ a, f (g a) = ⨆ b, f b :=
  hf.ciSup_comp_tendsto_atTop (OrderTop.bddAbove _) hg

/-- If `f` is a monotone function taking values in a complete lattice
and `g` tends to `atBot` along a nontrivial filter,
then the indexed infimum of `f ∘ g` is equal to the indexed infimum of `f`. -/
/-
**Filter._root_.Monotone.iInf_comp_tendsto_atBot** 是 Mathlib 中的一个定理，位于命名空间 `Filt
er`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f` is a monotone function taking values in a complete lattice
and `g` tends to `atBot` along a nontrivial filter,
then the indexed infimum of `f ∘ g` is equal to the indexed infimum of `f`.
-/
theorem _root_.Monotone.iInf_comp_tendsto_atBot
    [Preorder β] [ConditionallyCompleteLattice γ] [OrderBot γ]
    {l : Filter α} [l.NeBot] {f : β → γ} (hf : Monotone f) {g : α → β} (hg : Tendsto g l atBot) :
    ⨅ a, f (g a) = ⨅ b, f b :=
  hf.ciInf_comp_tendsto_atBot (OrderBot.bddBelow _) hg

/-- If `f` is an antitone function taking values in a complete lattice
and `g` tends to `atBot` along a nontrivial filter,
then the indexed supremum of `f ∘ g` is equal to the indexed supremum of `f`. -/
/-
**Filter._root_.Antitone.iSup_comp_tendsto_atBot** 是 Mathlib 中的一个定理，位于命名空间 `Filt
er`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f` is an antitone function taking values in a complete lattice
and `g` tends to `atBot` along a nontrivial filter,
then the indexed supremum of `f ∘ g` is equal to the indexed supremum of `f`.
-/
theorem _root_.Antitone.iSup_comp_tendsto_atBot
    [Preorder β] [ConditionallyCompleteLattice γ] [OrderTop γ]
    {l : Filter α} [l.NeBot] {f : β → γ} (hf : Antitone f) {g : α → β} (hg : Tendsto g l atBot) :
    ⨆ a, f (g a) = ⨆ b, f b :=
  hf.ciSup_comp_tendsto_atBot (OrderTop.bddAbove _) hg

/-- If `f` is an antitone function taking values in a complete lattice
and `g` tends to `atTop` along a nontrivial filter,
then the indexed infimum of `f ∘ g` is equal to the indexed infimum of `f`. -/
/-
**Filter._root_.Antitone.iInf_comp_tendsto_atTop** 是 Mathlib 中的一个定理，位于命名空间 `Filt
er`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f` is an antitone function taking values in a complete lattice
and `g` tends to `atTop` along a nontrivial filter,
then the indexed infimum of `f ∘ g` is equal to the indexed infimum of `f`.
-/
theorem _root_.Antitone.iInf_comp_tendsto_atTop
    [Preorder β] [ConditionallyCompleteLattice γ] [OrderBot γ]
    {l : Filter α} [l.NeBot] {f : β → γ} (hf : Antitone f) {g : α → β} (hg : Tendsto g l atTop) :
    ⨅ a, f (g a) = ⨅ b, f b :=
  hf.ciInf_comp_tendsto_atTop (OrderBot.bddBelow _) hg

/-- If `s` is a monotone family of sets and `f` tends to `atTop` along a nontrivial filter,
then the indexed union of `s ∘ f` is equal to the indexed union of `s`. -/
/-
**Filter._root_.Monotone.iUnion_comp_tendsto_atTop** 是 Mathlib 中的一个定理，位于命名空间 `Fi
lter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `s` is a monotone family of sets and `f` tends to `atTop` along a nontrivial 
filter,
then the indexed union of `s ∘ f` is equal to the indexed union of `s`.
-/
theorem _root_.Monotone.iUnion_comp_tendsto_atTop [Preorder β] {l : Filter α} [l.NeBot]
    {s : β → Set γ} (hs : Monotone s) {f : α → β} (hf : Tendsto f l atTop) :
    ⋃ a, s (f a) = ⋃ b, s b :=
  hs.iSup_comp_tendsto_atTop hf

/-- If `s` is a monotone family of sets and `f` tends to `atBot` along a nontrivial filter,
then the indexed intersection of `s ∘ f` is equal to the indexed intersection of `s`. -/
/-
**Filter._root_.Monotone.iInter_comp_tendsto_atBot** 是 Mathlib 中的一个定理，位于命名空间 `Fi
lter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `s` is a monotone family of sets and `f` tends to `atBot` along a nontrivial 
filter,
then the indexed intersection of `s ∘ f` is equal to the indexed intersection of
 `s`.
-/
theorem _root_.Monotone.iInter_comp_tendsto_atBot [Preorder β] {l : Filter α} [l.NeBot]
    {s : β → Set γ} (hs : Monotone s) {f : α → β} (hf : Tendsto f l atBot) :
    ⋂ a, s (f a) = ⋂ b, s b :=
  hs.iInf_comp_tendsto_atBot hf

/-- If `s` is an antitone family of sets and `f` tends to `atTop` along a nontrivial filter,
then the indexed intersection of `s ∘ f` is equal to the indexed intersection of `s`. -/
/-
**Filter._root_.Antitone.iInter_comp_tendsto_atTop** 是 Mathlib 中的一个定理，位于命名空间 `Fi
lter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `s` is an antitone family of sets and `f` tends to `atTop` along a nontrivial
 filter,
then the indexed intersection of `s ∘ f` is equal to the indexed intersection of
 `s`.
-/
theorem _root_.Antitone.iInter_comp_tendsto_atTop [Preorder β] {l : Filter α} [l.NeBot]
    {s : β → Set γ} (hs : Antitone s) {f : α → β} (hf : Tendsto f l atTop) :
    ⋂ a, s (f a) = ⋂ b, s b :=
  hs.iInf_comp_tendsto_atTop hf

/-- If `s` is a monotone family of sets and `f` tends to `atBot` along a nontrivial filter,
then the indexed union of `s ∘ f` is equal to the indexed union of `s`. -/
/-
**Filter._root_.Antitone.iUnion_comp_tendsto_atBot** 是 Mathlib 中的一个定理，位于命名空间 `Fi
lter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `s` is a monotone family of sets and `f` tends to `atBot` along a nontrivial 
filter,
then the indexed union of `s ∘ f` is equal to the indexed union of `s`.
-/
theorem _root_.Antitone.iUnion_comp_tendsto_atBot [Preorder β] {l : Filter α} [l.NeBot]
    {s : β → Set γ} (hs : Antitone s) {f : α → β} (hf : Tendsto f l atBot) :
    ⋃ a, s (f a) = ⋃ b, s b :=
  hs.iSup_comp_tendsto_atBot hf

end Filter

