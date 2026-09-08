/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Order.Filter.Extr
public import Mathlib.Topology.ContinuousOn

/-!
# Local extrema of functions on topological spaces

## Main definitions

This file defines special versions of `Is*Filter f a l`, `*=Min/Max/Extr`, from
`Mathlib/Order/Filter/Extr.lean` for two kinds of filters: `nhdsWithin` and `nhds`.
These versions are called `IsLocal*On` and `IsLocal*`, respectively.

## Main statements

Many lemmas in this file restate those from `Mathlib/Order/Filter/Extr.lean`, and you can find
detailed documentation there. These convenience lemmas are provided only to make the dot notation
return propositions of expected types, not just `Is*Filter`.

Here is the list of statements specific to these two types of filters:

* `IsLocal*.on`, `IsLocal*On.on_subset`: restrict to a subset;
* `IsLocal*On.inter` : intersect the set with another one;
* `Is*On.localize` : a global extremum is a local extremum too.
* `Is[Local]*On.isLocal*` : if we have `IsLocal*On f s a` and `s ∈ 𝓝 a`, then we have
  `IsLocal* f a`.
-/

@[expose] public section


universe u v w x

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type x} [TopologicalSpace α]

open Set Filter Topology

section Preorder

variable [Preorder β] [Preorder γ] (f : α → β) (s : Set α) (a : α)

/-- `IsLocalMinOn f s a` means that `f a ≤ f x` for all `x ∈ s` in some neighborhood of `a`. -/
/-
**IsLocalMinOn** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsLocalMinOn
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`IsLocalMinOn f s a` means that `f a ≤ f x` for all `x ∈ s` in some neighborhood
 of `a`.
-/
def IsLocalMinOn :=
  IsMinFilter f (𝓝[s] a) a

/-- `IsLocalMaxOn f s a` means that `f x ≤ f a` for all `x ∈ s` in some neighborhood of `a`. -/
/-
**IsLocalMaxOn** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsLocalMaxOn
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`IsLocalMaxOn f s a` means that `f x ≤ f a` for all `x ∈ s` in some neighborhood
 of `a`.
-/
def IsLocalMaxOn :=
  IsMaxFilter f (𝓝[s] a) a

/-- `IsLocalExtrOn f s a` means `IsLocalMinOn f s a ∨ IsLocalMaxOn f s a`. -/
/-
**IsLocalExtrOn** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsLocalExtrOn
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`IsLocalExtrOn f s a` means `IsLocalMinOn f s a ∨ IsLocalMaxOn f s a`.
-/
def IsLocalExtrOn :=
  IsExtrFilter f (𝓝[s] a) a

/-- `IsLocalMin f a` means that `f a ≤ f x` for all `x` in some neighborhood of `a`. -/
/-
**IsLocalMin** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsLocalMin
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`IsLocalMin f a` means that `f a ≤ f x` for all `x` in some neighborhood of `a`.
-/
def IsLocalMin :=
  IsMinFilter f (𝓝 a) a

/-- `IsLocalMax f a` means that `f x ≤ f a` for all `x ∈ s` in some neighborhood of `a`. -/
/-
**IsLocalMax** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsLocalMax
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`IsLocalMax f a` means that `f x ≤ f a` for all `x ∈ s` in some neighborhood of 
`a`.
-/
def IsLocalMax :=
  IsMaxFilter f (𝓝 a) a

/-- `IsLocalExtr f s a` means `IsLocalMin f s a ∨ IsLocalMax f s a`. -/
/-
**IsLocalExtr** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsLocalExtr
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`IsLocalExtr f s a` means `IsLocalMin f s a ∨ IsLocalMax f s a`.
-/
def IsLocalExtr :=
  IsExtrFilter f (𝓝 a) a

variable {f s a}
/-
**IsLocalExtrOn.elim** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLocalExtrOn.elim {p : Prop} : IsLocalExtrOn f s a -> (IsLocalMinOn f s a
 -> p) -> (IsLocalMaxOn f s a -> p) -> p
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
-/
theorem IsLocalExtrOn.elim {p : Prop} :
    IsLocalExtrOn f s a → (IsLocalMinOn f s a → p) → (IsLocalMaxOn f s a → p) → p :=
  Or.elim
/-
**IsLocalExtr.elim** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLocalExtr.elim {p : Prop} : IsLocalExtr f a -> (IsLocalMin f a -> p) -> 
(IsLocalMax f a -> p) -> p
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
-/
theorem IsLocalExtr.elim {p : Prop} :
    IsLocalExtr f a → (IsLocalMin f a → p) → (IsLocalMax f a → p) → p :=
  Or.elim

/-! ### Restriction to (sub)sets -/

/-
**IsLocalMin.on** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLocalMin.on (h : IsLocalMin f a) (s) : IsLocalMinOn f s a
参数：h : IsLocalMin f a；s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsMinFilter.filter_inf`：IsMinFilter.filter_inf (h : IsMinFilter f l a) (
l') : IsMinFilter f (l ⊓ l') a

--- 原说明 ---
### Restriction to (sub)sets
-/
theorem IsLocalMin.on (h : IsLocalMin f a) (s) : IsLocalMinOn f s a :=
  h.filter_inf _
/-
**IsLocalMax.on** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLocalMax.on (h : IsLocalMax f a) (s) : IsLocalMaxOn f s a
参数：h : IsLocalMax f a；s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsMaxFilter.filter_inf`：IsMaxFilter.filter_inf (h : IsMaxFilter f l a) (
l') : IsMaxFilter f (l ⊓ l') a
-/
theorem IsLocalMax.on (h : IsLocalMax f a) (s) : IsLocalMaxOn f s a :=
  h.filter_inf _
/-
**IsLocalExtr.on** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLocalExtr.on (h : IsLocalExtr f a) (s) : IsLocalExtrOn f s a
参数：h : IsLocalExtr f a；s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsExtrFilter.filter_inf`：IsExtrFilter.filter_inf (h : IsExtrFilter f l a
) (l') : IsExtrFilter f (l ⊓ l') a
-/
theorem IsLocalExtr.on (h : IsLocalExtr f a) (s) : IsLocalExtrOn f s a :=
  h.filter_inf _
/-
**IsLocalMinOn.on_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLocalMinOn.on_subset {t : Set α} (hf : IsLocalMinOn f t a) (h : s subset
eq t) : IsLocalMinOn f s a
参数：hf : IsLocalMinOn f t a；h : s subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsMinFilter.filter_mono`：IsMinFilter.filter_mono (h : IsMinFilter f l a)
 (hl : l' <= l) : IsMinFilter f l' a
· 使用定理 `nhdsWithin_mono`：nhdsWithin_mono (x : X) {s t : Set X} (h : s subseteq t
) : 𝓝[s] x <= 𝓝[t] x
-/
theorem IsLocalMinOn.on_subset {t : Set α} (hf : IsLocalMinOn f t a) (h : s ⊆ t) :
    IsLocalMinOn f s a :=
  hf.filter_mono <| nhdsWithin_mono a h
/-
**IsLocalMaxOn.on_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLocalMaxOn.on_subset {t : Set α} (hf : IsLocalMaxOn f t a) (h : s subset
eq t) : IsLocalMaxOn f s a
参数：hf : IsLocalMaxOn f t a；h : s subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsMaxFilter.filter_mono`：IsMaxFilter.filter_mono (h : IsMaxFilter f l a)
 (hl : l' <= l) : IsMaxFilter f l' a
· 使用定理 `nhdsWithin_mono`：nhdsWithin_mono (x : X) {s t : Set X} (h : s subseteq t
) : 𝓝[s] x <= 𝓝[t] x
-/
theorem IsLocalMaxOn.on_subset {t : Set α} (hf : IsLocalMaxOn f t a) (h : s ⊆ t) :
    IsLocalMaxOn f s a :=
  hf.filter_mono <| nhdsWithin_mono a h
/-
**IsLocalExtrOn.on_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLocalExtrOn.on_subset {t : Set α} (hf : IsLocalExtrOn f t a) (h : s subs
eteq t) : IsLocalExtrOn f s a
参数：hf : IsLocalExtrOn f t a；h : s subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsExtrFilter.filter_mono`：IsExtrFilter.filter_mono (h : IsExtrFilter f l
 a) (hl : l' <= l) : IsExtrFilter f l' a
· 使用定理 `nhdsWithin_mono`：nhdsWithin_mono (x : X) {s t : Set X} (h : s subseteq t
) : 𝓝[s] x <= 𝓝[t] x
-/
theorem IsLocalExtrOn.on_subset {t : Set α} (hf : IsLocalExtrOn f t a) (h : s ⊆ t) :
    IsLocalExtrOn f s a :=
  hf.filter_mono <| nhdsWithin_mono a h
/-
**IsLocalMinOn.inter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLocalMinOn.inter (hf : IsLocalMinOn f s a) (t) : IsLocalMinOn f (s inter
 t) a
参数：hf : IsLocalMinOn f s a；t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalMinOn.on_subset`：IsLocalMinOn.on_subset {t : Set α} (hf : IsLocal
MinOn f t a) (h : s subseteq t) : IsLocalMinOn f s a
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
-/
theorem IsLocalMinOn.inter (hf : IsLocalMinOn f s a) (t) : IsLocalMinOn f (s ∩ t) a :=
  hf.on_subset inter_subset_left
/-
**IsLocalMaxOn.inter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLocalMaxOn.inter (hf : IsLocalMaxOn f s a) (t) : IsLocalMaxOn f (s inter
 t) a
参数：hf : IsLocalMaxOn f s a；t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalMaxOn.on_subset`：IsLocalMaxOn.on_subset {t : Set α} (hf : IsLocal
MaxOn f t a) (h : s subseteq t) : IsLocalMaxOn f s a
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
-/
theorem IsLocalMaxOn.inter (hf : IsLocalMaxOn f s a) (t) : IsLocalMaxOn f (s ∩ t) a :=
  hf.on_subset inter_subset_left
/-
**IsLocalExtrOn.inter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLocalExtrOn.inter (hf : IsLocalExtrOn f s a) (t) : IsLocalExtrOn f (s in
ter t) a
参数：hf : IsLocalExtrOn f s a；t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalExtrOn.on_subset`：IsLocalExtrOn.on_subset {t : Set α} (hf : IsLoc
alExtrOn f t a) (h : s subseteq t) : IsLocalExtrOn f s a
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
-/
theorem IsLocalExtrOn.inter (hf : IsLocalExtrOn f s a) (t) : IsLocalExtrOn f (s ∩ t) a :=
  hf.on_subset inter_subset_left
/-
**IsMinOn.localize** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMinOn.localize (hf : IsMinOn f s a) : IsLocalMinOn f s a
参数：hf : IsMinOn f s a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsMinFilter.filter_mono`：IsMinFilter.filter_mono (h : IsMinFilter f l a)
 (hl : l' <= l) : IsMinFilter f l' a
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
-/
theorem IsMinOn.localize (hf : IsMinOn f s a) : IsLocalMinOn f s a :=
  hf.filter_mono <| inf_le_right
/-
**IsMaxOn.localize** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMaxOn.localize (hf : IsMaxOn f s a) : IsLocalMaxOn f s a
参数：hf : IsMaxOn f s a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsMaxFilter.filter_mono`：IsMaxFilter.filter_mono (h : IsMaxFilter f l a)
 (hl : l' <= l) : IsMaxFilter f l' a
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
-/
theorem IsMaxOn.localize (hf : IsMaxOn f s a) : IsLocalMaxOn f s a :=
  hf.filter_mono <| inf_le_right
/-
**IsExtrOn.localize** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsExtrOn.localize (hf : IsExtrOn f s a) : IsLocalExtrOn f s a
参数：hf : IsExtrOn f s a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsExtrFilter.filter_mono`：IsExtrFilter.filter_mono (h : IsExtrFilter f l
 a) (hl : l' <= l) : IsExtrFilter f l' a
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
-/
theorem IsExtrOn.localize (hf : IsExtrOn f s a) : IsLocalExtrOn f s a :=
  hf.filter_mono <| inf_le_right
/-
**IsLocalMinOn.isLocalMin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLocalMinOn.isLocalMin (hf : IsLocalMinOn f s a) (hs : s in 𝓝 a) : IsLoca
lMin f a
参数：hf : IsLocalMinOn f s a；hs : s in 𝓝 a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.le_principal_iff`：le_principal_iff {s : Set α} {f : Filter α} : f
 <= 𝓟 s ↔ s in f
· 使用定理 `IsMinFilter.filter_mono`：IsMinFilter.filter_mono (h : IsMinFilter f l a)
 (hl : l' <= l) : IsMinFilter f l' a
· 使用定理 `le_inf`：∀ {α : Type u} [inst : SemilatticeInf α] {c a b : α}, c ≤ a → c 
≤ b → c ≤ a ⊓ b
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem IsLocalMinOn.isLocalMin (hf : IsLocalMinOn f s a) (hs : s ∈ 𝓝 a) : IsLocalMin f a :=
  have : 𝓝 a ≤ 𝓟 s := le_principal_iff.2 hs
  hf.filter_mono <| le_inf le_rfl this
/-
**IsLocalMaxOn.isLocalMax** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLocalMaxOn.isLocalMax (hf : IsLocalMaxOn f s a) (hs : s in 𝓝 a) : IsLoca
lMax f a
参数：hf : IsLocalMaxOn f s a；hs : s in 𝓝 a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.le_principal_iff`：le_principal_iff {s : Set α} {f : Filter α} : f
 <= 𝓟 s ↔ s in f
· 使用定理 `IsMaxFilter.filter_mono`：IsMaxFilter.filter_mono (h : IsMaxFilter f l a)
 (hl : l' <= l) : IsMaxFilter f l' a
· 使用定理 `le_inf`：∀ {α : Type u} [inst : SemilatticeInf α] {c a b : α}, c ≤ a → c 
≤ b → c ≤ a ⊓ b
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem IsLocalMaxOn.isLocalMax (hf : IsLocalMaxOn f s a) (hs : s ∈ 𝓝 a) : IsLocalMax f a :=
  have : 𝓝 a ≤ 𝓟 s := le_principal_iff.2 hs
  hf.filter_mono <| le_inf le_rfl this
/-
**IsLocalExtrOn.isLocalExtr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLocalExtrOn.isLocalExtr (hf : IsLocalExtrOn f s a) (hs : s in 𝓝 a) : IsL
ocalExtr f a
参数：hf : IsLocalExtrOn f s a；hs : s in 𝓝 a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalExtrOn.elim`：IsLocalExtrOn.elim {p : Prop} : IsLocalExtrOn f s a 
-> (IsLocalMinOn f s a -> p) -> (IsLocalMaxOn f s a -> p) -> p
· 使用定理 `IsMinFilter.isExtr`：IsMinFilter.isExtr : IsMinFilter f l a -> IsExtrFilt
er f l a
· 使用定理 `IsLocalMinOn.isLocalMin`：IsLocalMinOn.isLocalMin (hf : IsLocalMinOn f s 
a) (hs : s in 𝓝 a) : IsLocalMin f a
· 使用定理 `IsMaxFilter.isExtr`：IsMaxFilter.isExtr : IsMaxFilter f l a -> IsExtrFilt
er f l a
· 使用定理 `IsLocalMaxOn.isLocalMax`：IsLocalMaxOn.isLocalMax (hf : IsLocalMaxOn f s 
a) (hs : s in 𝓝 a) : IsLocalMax f a
-/
theorem IsLocalExtrOn.isLocalExtr (hf : IsLocalExtrOn f s a) (hs : s ∈ 𝓝 a) : IsLocalExtr f a :=
  hf.elim (fun hf => (hf.isLocalMin hs).isExtr) fun hf => (hf.isLocalMax hs).isExtr
/-
**isLocalMinOn_univ_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isLocalMinOn_univ_iff : IsLocalMinOn f univ a ↔ IsLocalMin f a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhdsWithin_univ`：∀ {α : Type u_1} [inst : TopologicalSpace α] (a : α), n
hdsWithin a Set.univ = nhds a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma isLocalMinOn_univ_iff : IsLocalMinOn f univ a ↔ IsLocalMin f a := by
  simp only [IsLocalMinOn, IsLocalMin, nhdsWithin_univ]
/-
**isLocalMaxOn_univ_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isLocalMaxOn_univ_iff : IsLocalMaxOn f univ a ↔ IsLocalMax f a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhdsWithin_univ`：∀ {α : Type u_1} [inst : TopologicalSpace α] (a : α), n
hdsWithin a Set.univ = nhds a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma isLocalMaxOn_univ_iff : IsLocalMaxOn f univ a ↔ IsLocalMax f a := by
  simp only [IsLocalMaxOn, IsLocalMax, nhdsWithin_univ]
/-
**isLocalExtrOn_univ_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isLocalExtrOn_univ_iff : IsLocalExtrOn f univ a ↔ IsLocalExtr f a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.or`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∨ b ↔ c ∨ d)
· 使用引理 `isLocalMinOn_univ_iff`：isLocalMinOn_univ_iff : IsLocalMinOn f univ a ↔ I
sLocalMin f a
· 使用引理 `isLocalMaxOn_univ_iff`：isLocalMaxOn_univ_iff : IsLocalMaxOn f univ a ↔ I
sLocalMax f a
-/
lemma isLocalExtrOn_univ_iff : IsLocalExtrOn f univ a ↔ IsLocalExtr f a :=
  isLocalMinOn_univ_iff.or isLocalMaxOn_univ_iff
/-
**IsMinOn.isLocalMin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMinOn.isLocalMin (hf : IsMinOn f s a) (hs : s in 𝓝 a) : IsLocalMin f a
参数：hf : IsMinOn f s a；hs : s in 𝓝 a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalMinOn.isLocalMin`：IsLocalMinOn.isLocalMin (hf : IsLocalMinOn f s 
a) (hs : s in 𝓝 a) : IsLocalMin f a
· 使用定理 `IsMinOn.localize`：IsMinOn.localize (hf : IsMinOn f s a) : IsLocalMinOn f
 s a
-/
theorem IsMinOn.isLocalMin (hf : IsMinOn f s a) (hs : s ∈ 𝓝 a) : IsLocalMin f a :=
  hf.localize.isLocalMin hs
/-
**IsMaxOn.isLocalMax** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMaxOn.isLocalMax (hf : IsMaxOn f s a) (hs : s in 𝓝 a) : IsLocalMax f a
参数：hf : IsMaxOn f s a；hs : s in 𝓝 a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalMaxOn.isLocalMax`：IsLocalMaxOn.isLocalMax (hf : IsLocalMaxOn f s 
a) (hs : s in 𝓝 a) : IsLocalMax f a
· 使用定理 `IsMaxOn.localize`：IsMaxOn.localize (hf : IsMaxOn f s a) : IsLocalMaxOn f
 s a
-/
theorem IsMaxOn.isLocalMax (hf : IsMaxOn f s a) (hs : s ∈ 𝓝 a) : IsLocalMax f a :=
  hf.localize.isLocalMax hs
/-
**IsExtrOn.isLocalExtr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsExtrOn.isLocalExtr (hf : IsExtrOn f s a) (hs : s in 𝓝 a) : IsLocalExtr f
 a
参数：hf : IsExtrOn f s a；hs : s in 𝓝 a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalExtrOn.isLocalExtr`：IsLocalExtrOn.isLocalExtr (hf : IsLocalExtrOn
 f s a) (hs : s in 𝓝 a) : IsLocalExtr f a
· 使用定理 `IsExtrOn.localize`：IsExtrOn.localize (hf : IsExtrOn f s a) : IsLocalExtr
On f s a
-/
theorem IsExtrOn.isLocalExtr (hf : IsExtrOn f s a) (hs : s ∈ 𝓝 a) : IsLocalExtr f a :=
  hf.localize.isLocalExtr hs
/-
**IsLocalMinOn.not_nhds_le_map** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLocalMinOn.not_nhds_le_map [TopologicalSpace β] (hf : IsLocalMinOn f s a
) [NeBot (𝓝[<] f a)] : ¬𝓝 (f a) <= map f (𝓝[s] a)
参数：hf : IsLocalMinOn f s a；𝓝[<] f a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.filter_mono`：∀ {α : Type u} {f₁ f₂ : Filter α}, f₁ ≤ f
₂ → ∀ {p : α → Prop}, (∀ᶠ (x : α) in f₂, p x) → ∀ᶠ (x : α) in f₁, p x
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.eventually_map`：eventually_map {P : β -> Prop} : (forallᶠ b in ma
p m f, P b) ↔ forallᶠ a in f, P (m a)
· 使用定理 `Filter.Eventually.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α} [
f.NeBot], (∀ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem IsLocalMinOn.not_nhds_le_map [TopologicalSpace β] (hf : IsLocalMinOn f s a)
    [NeBot (𝓝[<] f a)] : ¬𝓝 (f a) ≤ map f (𝓝[s] a) := fun hle =>
  have : ∀ᶠ y in 𝓝[<] f a, f a ≤ y := (eventually_map.2 hf).filter_mono (inf_le_left.trans hle)
  let ⟨_y, hy⟩ := (this.and self_mem_nhdsWithin).exists
  hy.1.not_gt hy.2

set_option backward.isDefEq.respectTransparency false in
/-
**IsLocalMaxOn.not_nhds_le_map** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLocalMaxOn.not_nhds_le_map [TopologicalSpace β] (hf : IsLocalMaxOn f s a
) [NeBot (𝓝[>] f a)] : ¬𝓝 (f a) <= map f (𝓝[s] a)
参数：hf : IsLocalMaxOn f s a；𝓝[>] f a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalMinOn.not_nhds_le_map`：IsLocalMinOn.not_nhds_le_map [TopologicalS
pace β] (hf : IsLocalMinOn f s a) [NeBot (𝓝[<] f a)] : ¬𝓝 (f a) <= map f (𝓝[s] a
)
-/
theorem IsLocalMaxOn.not_nhds_le_map [TopologicalSpace β] (hf : IsLocalMaxOn f s a)
    [NeBot (𝓝[>] f a)] : ¬𝓝 (f a) ≤ map f (𝓝[s] a) :=
  @IsLocalMinOn.not_nhds_le_map α βᵒᵈ _ _ _ _ _ ‹_› hf ‹_›
/-
**IsLocalExtrOn.not_nhds_le_map** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLocalExtrOn.not_nhds_le_map [TopologicalSpace β] (hf : IsLocalExtrOn f s
 a) [NeBot (𝓝[<] f a)] [NeBot (𝓝[>] f a)] : ¬𝓝 (f a) <= map f (𝓝[s] a)
参数：hf : IsLocalExtrOn f s a；𝓝[<] f a；𝓝[>] f a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalExtrOn.elim`：IsLocalExtrOn.elim {p : Prop} : IsLocalExtrOn f s a 
-> (IsLocalMinOn f s a -> p) -> (IsLocalMaxOn f s a -> p) -> p
· 使用定理 `IsLocalMinOn.not_nhds_le_map`：IsLocalMinOn.not_nhds_le_map [TopologicalS
pace β] (hf : IsLocalMinOn f s a) [NeBot (𝓝[<] f a)] : ¬𝓝 (f a) <= map f (𝓝[s] a
)
· 使用定理 `IsLocalMaxOn.not_nhds_le_map`：IsLocalMaxOn.not_nhds_le_map [TopologicalS
pace β] (hf : IsLocalMaxOn f s a) [NeBot (𝓝[>] f a)] : ¬𝓝 (f a) <= map f (𝓝[s] a
)
-/
theorem IsLocalExtrOn.not_nhds_le_map [TopologicalSpace β] (hf : IsLocalExtrOn f s a)
    [NeBot (𝓝[<] f a)] [NeBot (𝓝[>] f a)] : ¬𝓝 (f a) ≤ map f (𝓝[s] a) :=
  hf.elim (fun h => h.not_nhds_le_map) fun h => h.not_nhds_le_map

/-! ### Constant -/


/-
**isLocalMinOn_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLocalMinOn_const {b : β} : IsLocalMinOn (fun _ => b) s a
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isMinFilter_const`：isMinFilter_const {b : β} : IsMinFilter (fun _ => b) 
l a

--- 原说明 ---
### Constant
-/
theorem isLocalMinOn_const {b : β} : IsLocalMinOn (fun _ => b) s a :=
  isMinFilter_const
/-
**isLocalMaxOn_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLocalMaxOn_const {b : β} : IsLocalMaxOn (fun _ => b) s a
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isMaxFilter_const`：isMaxFilter_const {b : β} : IsMaxFilter (fun _ => b) 
l a
-/
theorem isLocalMaxOn_const {b : β} : IsLocalMaxOn (fun _ => b) s a :=
  isMaxFilter_const
/-
**isLocalExtrOn_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLocalExtrOn_const {b : β} : IsLocalExtrOn (fun _ => b) s a
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isExtrFilter_const`：isExtrFilter_const {b : β} : IsExtrFilter (fun _ => 
b) l a
-/
theorem isLocalExtrOn_const {b : β} : IsLocalExtrOn (fun _ => b) s a :=
  isExtrFilter_const
/-
**isLocalMin_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLocalMin_const {b : β} : IsLocalMin (fun _ => b) a
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isMinFilter_const`：isMinFilter_const {b : β} : IsMinFilter (fun _ => b) 
l a
-/
theorem isLocalMin_const {b : β} : IsLocalMin (fun _ => b) a :=
  isMinFilter_const
/-
**isLocalMax_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLocalMax_const {b : β} : IsLocalMax (fun _ => b) a
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isMaxFilter_const`：isMaxFilter_const {b : β} : IsMaxFilter (fun _ => b) 
l a
-/
theorem isLocalMax_const {b : β} : IsLocalMax (fun _ => b) a :=
  isMaxFilter_const
/-
**isLocalExtr_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLocalExtr_const {b : β} : IsLocalExtr (fun _ => b) a
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isExtrFilter_const`：isExtrFilter_const {b : β} : IsExtrFilter (fun _ => 
b) l a
-/
theorem isLocalExtr_const {b : β} : IsLocalExtr (fun _ => b) a :=
  isExtrFilter_const

/-! ### Composition with (anti)monotone functions -/

nonrec theorem IsLocalMin.comp_mono (hf : IsLocalMin f a) {g : β → γ} (hg : Monotone g) :
    IsLocalMin (g ∘ f) a :=
  hf.comp_mono hg

nonrec theorem IsLocalMax.comp_mono (hf : IsLocalMax f a) {g : β → γ} (hg : Monotone g) :
    IsLocalMax (g ∘ f) a :=
  hf.comp_mono hg

nonrec theorem IsLocalExtr.comp_mono (hf : IsLocalExtr f a) {g : β → γ} (hg : Monotone g) :
    IsLocalExtr (g ∘ f) a :=
  hf.comp_mono hg

nonrec theorem IsLocalMin.comp_antitone (hf : IsLocalMin f a) {g : β → γ} (hg : Antitone g) :
    IsLocalMax (g ∘ f) a :=
  hf.comp_antitone hg

nonrec theorem IsLocalMax.comp_antitone (hf : IsLocalMax f a) {g : β → γ} (hg : Antitone g) :
    IsLocalMin (g ∘ f) a :=
  hf.comp_antitone hg

nonrec theorem IsLocalExtr.comp_antitone (hf : IsLocalExtr f a) {g : β → γ} (hg : Antitone g) :
    IsLocalExtr (g ∘ f) a :=
  hf.comp_antitone hg

nonrec theorem IsLocalMinOn.comp_mono (hf : IsLocalMinOn f s a) {g : β → γ} (hg : Monotone g) :
    IsLocalMinOn (g ∘ f) s a :=
  hf.comp_mono hg

nonrec theorem IsLocalMaxOn.comp_mono (hf : IsLocalMaxOn f s a) {g : β → γ} (hg : Monotone g) :
    IsLocalMaxOn (g ∘ f) s a :=
  hf.comp_mono hg

nonrec theorem IsLocalExtrOn.comp_mono (hf : IsLocalExtrOn f s a) {g : β → γ} (hg : Monotone g) :
    IsLocalExtrOn (g ∘ f) s a :=
  hf.comp_mono hg

nonrec theorem IsLocalMinOn.comp_antitone (hf : IsLocalMinOn f s a) {g : β → γ} (hg : Antitone g) :
    IsLocalMaxOn (g ∘ f) s a :=
  hf.comp_antitone hg

nonrec theorem IsLocalMaxOn.comp_antitone (hf : IsLocalMaxOn f s a) {g : β → γ} (hg : Antitone g) :
    IsLocalMinOn (g ∘ f) s a :=
  hf.comp_antitone hg

nonrec theorem IsLocalExtrOn.comp_antitone (hf : IsLocalExtrOn f s a) {g : β → γ}
    (hg : Antitone g) : IsLocalExtrOn (g ∘ f) s a :=
  hf.comp_antitone hg

open scoped Relator

nonrec theorem IsLocalMin.bicomp_mono [Preorder δ] {op : β → γ → δ}
    (hop : ((· ≤ ·) ⇒ (· ≤ ·) ⇒ (· ≤ ·)) op op) (hf : IsLocalMin f a) {g : α → γ}
    (hg : IsLocalMin g a) : IsLocalMin (fun x => op (f x) (g x)) a :=
  hf.bicomp_mono hop hg

nonrec theorem IsLocalMax.bicomp_mono [Preorder δ] {op : β → γ → δ}
    (hop : ((· ≤ ·) ⇒ (· ≤ ·) ⇒ (· ≤ ·)) op op) (hf : IsLocalMax f a) {g : α → γ}
    (hg : IsLocalMax g a) : IsLocalMax (fun x => op (f x) (g x)) a :=
  hf.bicomp_mono hop hg

nonrec theorem IsLocalMinOn.bicomp_mono [Preorder δ] {op : β → γ → δ}
    (hop : ((· ≤ ·) ⇒ (· ≤ ·) ⇒ (· ≤ ·)) op op) (hf : IsLocalMinOn f s a) {g : α → γ}
    (hg : IsLocalMinOn g s a) : IsLocalMinOn (fun x => op (f x) (g x)) s a :=
  hf.bicomp_mono hop hg

nonrec theorem IsLocalMaxOn.bicomp_mono [Preorder δ] {op : β → γ → δ}
    (hop : ((· ≤ ·) ⇒ (· ≤ ·) ⇒ (· ≤ ·)) op op) (hf : IsLocalMaxOn f s a) {g : α → γ}
    (hg : IsLocalMaxOn g s a) : IsLocalMaxOn (fun x => op (f x) (g x)) s a :=
  hf.bicomp_mono hop hg

/-! ### Composition with `ContinuousAt` -/


/-
**IsLocalMin.comp_continuous** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLocalMin.comp_continuous [TopologicalSpace δ] {g : δ -> α} {b : δ} (hf :
 IsLocalMin f (g b)) (hg : ContinuousAt g b) : IsLocalMin (f ∘ g) b
参数：hf : IsLocalMin f (g b)；hg : ContinuousAt g b。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Composition with `ContinuousAt`
-/
theorem IsLocalMin.comp_continuous [TopologicalSpace δ] {g : δ → α} {b : δ}
    (hf : IsLocalMin f (g b)) (hg : ContinuousAt g b) : IsLocalMin (f ∘ g) b :=
  hg hf
/-
**IsLocalMax.comp_continuous** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLocalMax.comp_continuous [TopologicalSpace δ] {g : δ -> α} {b : δ} (hf :
 IsLocalMax f (g b)) (hg : ContinuousAt g b) : IsLocalMax (f ∘ g) b
参数：hf : IsLocalMax f (g b)；hg : ContinuousAt g b。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IsLocalMax.comp_continuous [TopologicalSpace δ] {g : δ → α} {b : δ}
    (hf : IsLocalMax f (g b)) (hg : ContinuousAt g b) : IsLocalMax (f ∘ g) b :=
  hg hf
/-
**IsLocalExtr.comp_continuous** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLocalExtr.comp_continuous [TopologicalSpace δ] {g : δ -> α} {b : δ} (hf 
: IsLocalExtr f (g b)) (hg : ContinuousAt g b) : IsLocalExtr (f ∘ g) b
参数：hf : IsLocalExtr f (g b)；hg : ContinuousAt g b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsExtrFilter.comp_tendsto`：IsExtrFilter.comp_tendsto {g : δ -> α} {l' : 
Filter δ} {b : δ} (hf : IsExtrFilter f l (g b)) (hg : Tendsto g l' l) : IsExtrFi
lter (f ∘ g) l'…
-/
theorem IsLocalExtr.comp_continuous [TopologicalSpace δ] {g : δ → α} {b : δ}
    (hf : IsLocalExtr f (g b)) (hg : ContinuousAt g b) : IsLocalExtr (f ∘ g) b :=
  hf.comp_tendsto hg
/-
**IsLocalMin.comp_continuousOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLocalMin.comp_continuousOn [TopologicalSpace δ] {s : Set δ} {g : δ -> α}
 {b : δ} (hf : IsLocalMin f (g b)) (hg : ContinuousOn g s) (hb : b in s) : IsLoc
alMinOn (f ∘ g) s b
参数：hf : IsLocalMin f (g b)；hg : ContinuousOn g s；hb : b in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsMinFilter.comp_tendsto`：IsMinFilter.comp_tendsto {g : δ -> α} {l' : Fi
lter δ} {b : δ} (hf : IsMinFilter f l (g b)) (hg : Tendsto g l' l) : IsMinFilter
 (f ∘ g) l' b
-/
theorem IsLocalMin.comp_continuousOn [TopologicalSpace δ] {s : Set δ} {g : δ → α} {b : δ}
    (hf : IsLocalMin f (g b)) (hg : ContinuousOn g s) (hb : b ∈ s) : IsLocalMinOn (f ∘ g) s b :=
  hf.comp_tendsto (hg b hb)
/-
**IsLocalMax.comp_continuousOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLocalMax.comp_continuousOn [TopologicalSpace δ] {s : Set δ} {g : δ -> α}
 {b : δ} (hf : IsLocalMax f (g b)) (hg : ContinuousOn g s) (hb : b in s) : IsLoc
alMaxOn (f ∘ g) s b
参数：hf : IsLocalMax f (g b)；hg : ContinuousOn g s；hb : b in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsMaxFilter.comp_tendsto`：IsMaxFilter.comp_tendsto {g : δ -> α} {l' : Fi
lter δ} {b : δ} (hf : IsMaxFilter f l (g b)) (hg : Tendsto g l' l) : IsMaxFilter
 (f ∘ g) l' b
-/
theorem IsLocalMax.comp_continuousOn [TopologicalSpace δ] {s : Set δ} {g : δ → α} {b : δ}
    (hf : IsLocalMax f (g b)) (hg : ContinuousOn g s) (hb : b ∈ s) : IsLocalMaxOn (f ∘ g) s b :=
  hf.comp_tendsto (hg b hb)
/-
**IsLocalExtr.comp_continuousOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLocalExtr.comp_continuousOn [TopologicalSpace δ] {s : Set δ} (g : δ -> α
) {b : δ} (hf : IsLocalExtr f (g b)) (hg : ContinuousOn g s) (hb : b in s) : IsL
ocalExtrOn (f ∘ g) s b
参数：g : δ -> α；hf : IsLocalExtr f (g b)；hg : ContinuousOn g s；hb : b in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalExtr.elim`：IsLocalExtr.elim {p : Prop} : IsLocalExtr f a -> (IsLo
calMin f a -> p) -> (IsLocalMax f a -> p) -> p
· 使用定理 `IsMinFilter.isExtr`：IsMinFilter.isExtr : IsMinFilter f l a -> IsExtrFilt
er f l a
· 使用定理 `IsLocalMin.comp_continuousOn`：IsLocalMin.comp_continuousOn [TopologicalS
pace δ] {s : Set δ} {g : δ -> α} {b : δ} (hf : IsLocalMin f (g b)) (hg : Continu
ousOn g s) (hb : b…
· 使用定理 `IsMaxFilter.isExtr`：IsMaxFilter.isExtr : IsMaxFilter f l a -> IsExtrFilt
er f l a
· 使用定理 `IsLocalMax.comp_continuousOn`：IsLocalMax.comp_continuousOn [TopologicalS
pace δ] {s : Set δ} {g : δ -> α} {b : δ} (hf : IsLocalMax f (g b)) (hg : Continu
ousOn g s) (hb : b…
-/
theorem IsLocalExtr.comp_continuousOn [TopologicalSpace δ] {s : Set δ} (g : δ → α) {b : δ}
    (hf : IsLocalExtr f (g b)) (hg : ContinuousOn g s) (hb : b ∈ s) : IsLocalExtrOn (f ∘ g) s b :=
  hf.elim (fun hf => (hf.comp_continuousOn hg hb).isExtr) fun hf =>
    (IsLocalMax.comp_continuousOn hf hg hb).isExtr
/-
**IsLocalMinOn.comp_continuousOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLocalMinOn.comp_continuousOn [TopologicalSpace δ] {t : Set α} {s : Set δ
} {g : δ -> α} {b : δ} (hf : IsLocalMinOn f t (g b)) (hst : s subseteq g ⁻¹' t) 
(hg : ContinuousOn g s) (hb : b in s) : IsLocalMinOn (f ∘ g) s b
参数：hf : IsLocalMinOn f t (g b)；hst : s subseteq g ⁻¹' t；hg : ContinuousOn g s；hb
 : b in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsMinFilter.comp_tendsto`：IsMinFilter.comp_tendsto {g : δ -> α} {l' : Fi
lter δ} {b : δ} (hf : IsMinFilter f l (g b)) (hg : Tendsto g l' l) : IsMinFilter
 (f ∘ g) l' b
· 使用定理 `tendsto_nhdsWithin_mono_right`：tendsto_nhdsWithin_mono_right {f : β -> α
} {l : Filter β} {a : α} {s t : Set α} (hst : s subseteq t) (h : Tendsto f l (𝓝[
s] a)) : Tendsto f …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
· 使用定理 `ContinuousWithinAt.tendsto_nhdsWithin_image`：ContinuousWithinAt.tendsto_
nhdsWithin_image (h : ContinuousWithinAt f s x) : Tendsto f (𝓝[s] x) (𝓝[f '' s] 
f x)
-/
theorem IsLocalMinOn.comp_continuousOn [TopologicalSpace δ] {t : Set α} {s : Set δ} {g : δ → α}
    {b : δ} (hf : IsLocalMinOn f t (g b)) (hst : s ⊆ g ⁻¹' t) (hg : ContinuousOn g s) (hb : b ∈ s) :
    IsLocalMinOn (f ∘ g) s b :=
  hf.comp_tendsto
    (tendsto_nhdsWithin_mono_right (image_subset_iff.mpr hst)
      (ContinuousWithinAt.tendsto_nhdsWithin_image (hg b hb)))
/-
**IsLocalMaxOn.comp_continuousOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLocalMaxOn.comp_continuousOn [TopologicalSpace δ] {t : Set α} {s : Set δ
} {g : δ -> α} {b : δ} (hf : IsLocalMaxOn f t (g b)) (hst : s subseteq g ⁻¹' t) 
(hg : ContinuousOn g s) (hb : b in s) : IsLocalMaxOn (f ∘ g) s b
参数：hf : IsLocalMaxOn f t (g b)；hst : s subseteq g ⁻¹' t；hg : ContinuousOn g s；hb
 : b in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsMaxFilter.comp_tendsto`：IsMaxFilter.comp_tendsto {g : δ -> α} {l' : Fi
lter δ} {b : δ} (hf : IsMaxFilter f l (g b)) (hg : Tendsto g l' l) : IsMaxFilter
 (f ∘ g) l' b
· 使用定理 `tendsto_nhdsWithin_mono_right`：tendsto_nhdsWithin_mono_right {f : β -> α
} {l : Filter β} {a : α} {s t : Set α} (hst : s subseteq t) (h : Tendsto f l (𝓝[
s] a)) : Tendsto f …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
· 使用定理 `ContinuousWithinAt.tendsto_nhdsWithin_image`：ContinuousWithinAt.tendsto_
nhdsWithin_image (h : ContinuousWithinAt f s x) : Tendsto f (𝓝[s] x) (𝓝[f '' s] 
f x)
-/
theorem IsLocalMaxOn.comp_continuousOn [TopologicalSpace δ] {t : Set α} {s : Set δ} {g : δ → α}
    {b : δ} (hf : IsLocalMaxOn f t (g b)) (hst : s ⊆ g ⁻¹' t) (hg : ContinuousOn g s) (hb : b ∈ s) :
    IsLocalMaxOn (f ∘ g) s b :=
  hf.comp_tendsto
    (tendsto_nhdsWithin_mono_right (image_subset_iff.mpr hst)
      (ContinuousWithinAt.tendsto_nhdsWithin_image (hg b hb)))
/-
**IsLocalExtrOn.comp_continuousOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLocalExtrOn.comp_continuousOn [TopologicalSpace δ] {t : Set α} {s : Set 
δ} (g : δ -> α) {b : δ} (hf : IsLocalExtrOn f t (g b)) (hst : s subseteq g ⁻¹' t
) (hg : ContinuousOn g s) (hb : b in s) : IsLocalExtrOn (f ∘ g) s b
参数：g : δ -> α；hf : IsLocalExtrOn f t (g b)；hst : s subseteq g ⁻¹' t；hg : Continu
ousOn g s；hb : b in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalExtrOn.elim`：IsLocalExtrOn.elim {p : Prop} : IsLocalExtrOn f s a 
-> (IsLocalMinOn f s a -> p) -> (IsLocalMaxOn f s a -> p) -> p
· 使用定理 `IsMinFilter.isExtr`：IsMinFilter.isExtr : IsMinFilter f l a -> IsExtrFilt
er f l a
· 使用定理 `IsLocalMinOn.comp_continuousOn`：IsLocalMinOn.comp_continuousOn [Topologi
calSpace δ] {t : Set α} {s : Set δ} {g : δ -> α} {b : δ} (hf : IsLocalMinOn f t 
(g b)) (hst : s subs…
· 使用定理 `IsMaxFilter.isExtr`：IsMaxFilter.isExtr : IsMaxFilter f l a -> IsExtrFilt
er f l a
· 使用定理 `IsLocalMaxOn.comp_continuousOn`：IsLocalMaxOn.comp_continuousOn [Topologi
calSpace δ] {t : Set α} {s : Set δ} {g : δ -> α} {b : δ} (hf : IsLocalMaxOn f t 
(g b)) (hst : s subs…
-/
theorem IsLocalExtrOn.comp_continuousOn [TopologicalSpace δ] {t : Set α} {s : Set δ} (g : δ → α)
    {b : δ} (hf : IsLocalExtrOn f t (g b)) (hst : s ⊆ g ⁻¹' t) (hg : ContinuousOn g s)
    (hb : b ∈ s) : IsLocalExtrOn (f ∘ g) s b :=
  hf.elim (fun hf => (hf.comp_continuousOn hst hg hb).isExtr) fun hf =>
    (IsLocalMaxOn.comp_continuousOn hf hst hg hb).isExtr

end Preorder

/-! ### Pointwise addition -/


section OrderedAddCommMonoid

variable [AddCommMonoid β] [PartialOrder β] [IsOrderedAddMonoid β]
  {f g : α → β} {a : α} {s : Set α} {l : Filter α}

nonrec theorem IsLocalMin.add (hf : IsLocalMin f a) (hg : IsLocalMin g a) :
    IsLocalMin (fun x => f x + g x) a :=
  hf.add hg

nonrec theorem IsLocalMax.add (hf : IsLocalMax f a) (hg : IsLocalMax g a) :
    IsLocalMax (fun x => f x + g x) a :=
  hf.add hg

nonrec theorem IsLocalMinOn.add (hf : IsLocalMinOn f s a) (hg : IsLocalMinOn g s a) :
    IsLocalMinOn (fun x => f x + g x) s a :=
  hf.add hg

nonrec theorem IsLocalMaxOn.add (hf : IsLocalMaxOn f s a) (hg : IsLocalMaxOn g s a) :
    IsLocalMaxOn (fun x => f x + g x) s a :=
  hf.add hg

end OrderedAddCommMonoid

/-! ### Pointwise negation and subtraction -/


section OrderedAddCommGroup

variable [AddCommGroup β] [PartialOrder β] [IsOrderedAddMonoid β]
  {f g : α → β} {a : α} {s : Set α} {l : Filter α}

nonrec theorem IsLocalMin.neg (hf : IsLocalMin f a) : IsLocalMax (fun x => -f x) a :=
  hf.neg

nonrec theorem IsLocalMax.neg (hf : IsLocalMax f a) : IsLocalMin (fun x => -f x) a :=
  hf.neg

nonrec theorem IsLocalExtr.neg (hf : IsLocalExtr f a) : IsLocalExtr (fun x => -f x) a :=
  hf.neg

nonrec theorem IsLocalMinOn.neg (hf : IsLocalMinOn f s a) : IsLocalMaxOn (fun x => -f x) s a :=
  hf.neg

nonrec theorem IsLocalMaxOn.neg (hf : IsLocalMaxOn f s a) : IsLocalMinOn (fun x => -f x) s a :=
  hf.neg

nonrec theorem IsLocalExtrOn.neg (hf : IsLocalExtrOn f s a) : IsLocalExtrOn (fun x => -f x) s a :=
  hf.neg

nonrec theorem IsLocalMin.sub (hf : IsLocalMin f a) (hg : IsLocalMax g a) :
    IsLocalMin (fun x => f x - g x) a :=
  hf.sub hg

nonrec theorem IsLocalMax.sub (hf : IsLocalMax f a) (hg : IsLocalMin g a) :
    IsLocalMax (fun x => f x - g x) a :=
  hf.sub hg

nonrec theorem IsLocalMinOn.sub (hf : IsLocalMinOn f s a) (hg : IsLocalMaxOn g s a) :
    IsLocalMinOn (fun x => f x - g x) s a :=
  hf.sub hg

nonrec theorem IsLocalMaxOn.sub (hf : IsLocalMaxOn f s a) (hg : IsLocalMinOn g s a) :
    IsLocalMaxOn (fun x => f x - g x) s a :=
  hf.sub hg

end OrderedAddCommGroup

/-! ### Pointwise `sup`/`inf` -/


section SemilatticeSup

variable [SemilatticeSup β] {f g : α → β} {a : α} {s : Set α} {l : Filter α}

nonrec theorem IsLocalMin.sup (hf : IsLocalMin f a) (hg : IsLocalMin g a) :
    IsLocalMin (fun x => f x ⊔ g x) a :=
  hf.sup hg

nonrec theorem IsLocalMax.sup (hf : IsLocalMax f a) (hg : IsLocalMax g a) :
    IsLocalMax (fun x => f x ⊔ g x) a :=
  hf.sup hg

nonrec theorem IsLocalMinOn.sup (hf : IsLocalMinOn f s a) (hg : IsLocalMinOn g s a) :
    IsLocalMinOn (fun x => f x ⊔ g x) s a :=
  hf.sup hg

nonrec theorem IsLocalMaxOn.sup (hf : IsLocalMaxOn f s a) (hg : IsLocalMaxOn g s a) :
    IsLocalMaxOn (fun x => f x ⊔ g x) s a :=
  hf.sup hg

end SemilatticeSup

section SemilatticeInf

variable [SemilatticeInf β] {f g : α → β} {a : α} {s : Set α} {l : Filter α}

nonrec theorem IsLocalMin.inf (hf : IsLocalMin f a) (hg : IsLocalMin g a) :
    IsLocalMin (fun x => f x ⊓ g x) a :=
  hf.inf hg

nonrec theorem IsLocalMax.inf (hf : IsLocalMax f a) (hg : IsLocalMax g a) :
    IsLocalMax (fun x => f x ⊓ g x) a :=
  hf.inf hg

nonrec theorem IsLocalMinOn.inf (hf : IsLocalMinOn f s a) (hg : IsLocalMinOn g s a) :
    IsLocalMinOn (fun x => f x ⊓ g x) s a :=
  hf.inf hg

nonrec theorem IsLocalMaxOn.inf (hf : IsLocalMaxOn f s a) (hg : IsLocalMaxOn g s a) :
    IsLocalMaxOn (fun x => f x ⊓ g x) s a :=
  hf.inf hg

end SemilatticeInf

/-! ### Pointwise `min`/`max` -/


section LinearOrder

variable [LinearOrder β] {f g : α → β} {a : α} {s : Set α} {l : Filter α}

nonrec theorem IsLocalMin.min (hf : IsLocalMin f a) (hg : IsLocalMin g a) :
    IsLocalMin (fun x => min (f x) (g x)) a :=
  hf.min hg

nonrec theorem IsLocalMax.min (hf : IsLocalMax f a) (hg : IsLocalMax g a) :
    IsLocalMax (fun x => min (f x) (g x)) a :=
  hf.min hg

nonrec theorem IsLocalMinOn.min (hf : IsLocalMinOn f s a) (hg : IsLocalMinOn g s a) :
    IsLocalMinOn (fun x => min (f x) (g x)) s a :=
  hf.min hg

nonrec theorem IsLocalMaxOn.min (hf : IsLocalMaxOn f s a) (hg : IsLocalMaxOn g s a) :
    IsLocalMaxOn (fun x => min (f x) (g x)) s a :=
  hf.min hg

nonrec theorem IsLocalMin.max (hf : IsLocalMin f a) (hg : IsLocalMin g a) :
    IsLocalMin (fun x => max (f x) (g x)) a :=
  hf.max hg

nonrec theorem IsLocalMax.max (hf : IsLocalMax f a) (hg : IsLocalMax g a) :
    IsLocalMax (fun x => max (f x) (g x)) a :=
  hf.max hg

nonrec theorem IsLocalMinOn.max (hf : IsLocalMinOn f s a) (hg : IsLocalMinOn g s a) :
    IsLocalMinOn (fun x => max (f x) (g x)) s a :=
  hf.max hg

nonrec theorem IsLocalMaxOn.max (hf : IsLocalMaxOn f s a) (hg : IsLocalMaxOn g s a) :
    IsLocalMaxOn (fun x => max (f x) (g x)) s a :=
  hf.max hg

end LinearOrder

section Eventually

/-! ### Relation with `eventually` comparisons of two functions -/


variable [Preorder β] {s : Set α}

/-
**Filter.EventuallyLE.isLocalMaxOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.EventuallyLE.isLocalMaxOn {f g : α -> β} {a : α} (hle : g <=ᶠ[𝓝[s] 
a] f) (hfga : f a = g a) (h : IsLocalMaxOn f s a) : IsLocalMaxOn g s a
参数：hle : g <=ᶠ[𝓝[s] a] f；hfga : f a = g a；h : IsLocalMaxOn f s a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyLE.isMaxFilter`：Filter.EventuallyLE.isMaxFilter {α β : 
Type*} [Preorder β] {f g : α -> β} {a : α} {l : Filter α} (hle : g <=ᶠ[l] f) (hf
ga : f a = g a) (h : …
-/
theorem Filter.EventuallyLE.isLocalMaxOn {f g : α → β} {a : α} (hle : g ≤ᶠ[𝓝[s] a] f)
    (hfga : f a = g a) (h : IsLocalMaxOn f s a) : IsLocalMaxOn g s a :=
  hle.isMaxFilter hfga h

nonrec theorem IsLocalMaxOn.congr {f g : α → β} {a : α} (h : IsLocalMaxOn f s a)
    (heq : f =ᶠ[𝓝[s] a] g) (hmem : a ∈ s) : IsLocalMaxOn g s a :=
  h.congr heq <| heq.eq_of_nhdsWithin hmem
/-
**Filter.EventuallyEq.isLocalMaxOn_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.EventuallyEq.isLocalMaxOn_iff {f g : α -> β} {a : α} (heq : f =ᶠ[𝓝[
s] a] g) (hmem : a in s) : IsLocalMaxOn f s a ↔ IsLocalMaxOn g s a
参数：heq : f =ᶠ[𝓝[s] a] g；hmem : a in s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.isMaxFilter_iff`：Filter.EventuallyEq.isMaxFilter_iff
 {α β : Type*} [Preorder β] {f g : α -> β} {a : α} {l : Filter α} (heq : f =ᶠ[l]
 g) (hfga : f a = g a) : …
· 使用定理 `Filter.EventuallyEq.eq_of_nhdsWithin`：Filter.EventuallyEq.eq_of_nhdsWith
in {s : Set α} {f g : α -> β} {a : α} (h : f =ᶠ[𝓝[s] a] g) (hmem : a in s) : f a
 = g a
-/
theorem Filter.EventuallyEq.isLocalMaxOn_iff {f g : α → β} {a : α} (heq : f =ᶠ[𝓝[s] a] g)
    (hmem : a ∈ s) : IsLocalMaxOn f s a ↔ IsLocalMaxOn g s a :=
  heq.isMaxFilter_iff <| heq.eq_of_nhdsWithin hmem
/-
**Filter.EventuallyLE.isLocalMinOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.EventuallyLE.isLocalMinOn {f g : α -> β} {a : α} (hle : f <=ᶠ[𝓝[s] 
a] g) (hfga : f a = g a) (h : IsLocalMinOn f s a) : IsLocalMinOn g s a
参数：hle : f <=ᶠ[𝓝[s] a] g；hfga : f a = g a；h : IsLocalMinOn f s a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyLE.isMinFilter`：Filter.EventuallyLE.isMinFilter {α β : 
Type*} [Preorder β] {f g : α -> β} {a : α} {l : Filter α} (hle : f <=ᶠ[l] g) (hf
ga : f a = g a) (h : …
-/
theorem Filter.EventuallyLE.isLocalMinOn {f g : α → β} {a : α} (hle : f ≤ᶠ[𝓝[s] a] g)
    (hfga : f a = g a) (h : IsLocalMinOn f s a) : IsLocalMinOn g s a :=
  hle.isMinFilter hfga h

nonrec theorem IsLocalMinOn.congr {f g : α → β} {a : α} (h : IsLocalMinOn f s a)
    (heq : f =ᶠ[𝓝[s] a] g) (hmem : a ∈ s) : IsLocalMinOn g s a :=
  h.congr heq <| heq.eq_of_nhdsWithin hmem

nonrec theorem Filter.EventuallyEq.isLocalMinOn_iff {f g : α → β} {a : α} (heq : f =ᶠ[𝓝[s] a] g)
    (hmem : a ∈ s) : IsLocalMinOn f s a ↔ IsLocalMinOn g s a :=
  heq.isMinFilter_iff <| heq.eq_of_nhdsWithin hmem

nonrec theorem IsLocalExtrOn.congr {f g : α → β} {a : α} (h : IsLocalExtrOn f s a)
    (heq : f =ᶠ[𝓝[s] a] g) (hmem : a ∈ s) : IsLocalExtrOn g s a :=
  h.congr heq <| heq.eq_of_nhdsWithin hmem
/-
**Filter.EventuallyEq.isLocalExtrOn_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.EventuallyEq.isLocalExtrOn_iff {f g : α -> β} {a : α} (heq : f =ᶠ[𝓝
[s] a] g) (hmem : a in s) : IsLocalExtrOn f s a ↔ IsLocalExtrOn g s a
参数：heq : f =ᶠ[𝓝[s] a] g；hmem : a in s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.isExtrFilter_iff`：Filter.EventuallyEq.isExtrFilter_i
ff {α β : Type*} [Preorder β] {f g : α -> β} {a : α} {l : Filter α} (heq : f =ᶠ[
l] g) (hfga : f a = g a) :…
· 使用定理 `Filter.EventuallyEq.eq_of_nhdsWithin`：Filter.EventuallyEq.eq_of_nhdsWith
in {s : Set α} {f g : α -> β} {a : α} (h : f =ᶠ[𝓝[s] a] g) (hmem : a in s) : f a
 = g a
-/
theorem Filter.EventuallyEq.isLocalExtrOn_iff {f g : α → β} {a : α} (heq : f =ᶠ[𝓝[s] a] g)
    (hmem : a ∈ s) : IsLocalExtrOn f s a ↔ IsLocalExtrOn g s a :=
  heq.isExtrFilter_iff <| heq.eq_of_nhdsWithin hmem
/-
**Filter.EventuallyLE.isLocalMax** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.EventuallyLE.isLocalMax {f g : α -> β} {a : α} (hle : g <=ᶠ[𝓝 a] f)
 (hfga : f a = g a) (h : IsLocalMax f a) : IsLocalMax g a
参数：hle : g <=ᶠ[𝓝 a] f；hfga : f a = g a；h : IsLocalMax f a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyLE.isMaxFilter`：Filter.EventuallyLE.isMaxFilter {α β : 
Type*} [Preorder β] {f g : α -> β} {a : α} {l : Filter α} (hle : g <=ᶠ[l] f) (hf
ga : f a = g a) (h : …
-/
theorem Filter.EventuallyLE.isLocalMax {f g : α → β} {a : α} (hle : g ≤ᶠ[𝓝 a] f) (hfga : f a = g a)
    (h : IsLocalMax f a) : IsLocalMax g a :=
  hle.isMaxFilter hfga h

nonrec theorem IsLocalMax.congr {f g : α → β} {a : α} (h : IsLocalMax f a) (heq : f =ᶠ[𝓝 a] g) :
    IsLocalMax g a :=
  h.congr heq heq.eq_of_nhds
/-
**Filter.EventuallyEq.isLocalMax_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.EventuallyEq.isLocalMax_iff {f g : α -> β} {a : α} (heq : f =ᶠ[𝓝 a]
 g) : IsLocalMax f a ↔ IsLocalMax g a
参数：heq : f =ᶠ[𝓝 a] g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.isMaxFilter_iff`：Filter.EventuallyEq.isMaxFilter_iff
 {α β : Type*} [Preorder β] {f g : α -> β} {a : α} {l : Filter α} (heq : f =ᶠ[l]
 g) (hfga : f a = g a) : …
· 使用定理 `Filter.EventuallyEq.eq_of_nhds`：Filter.EventuallyEq.eq_of_nhds {f g : X 
-> α} (h : f =ᶠ[𝓝 x] g) : f x = g x
-/
theorem Filter.EventuallyEq.isLocalMax_iff {f g : α → β} {a : α} (heq : f =ᶠ[𝓝 a] g) :
    IsLocalMax f a ↔ IsLocalMax g a :=
  heq.isMaxFilter_iff heq.eq_of_nhds
/-
**Filter.EventuallyLE.isLocalMin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.EventuallyLE.isLocalMin {f g : α -> β} {a : α} (hle : f <=ᶠ[𝓝 a] g)
 (hfga : f a = g a) (h : IsLocalMin f a) : IsLocalMin g a
参数：hle : f <=ᶠ[𝓝 a] g；hfga : f a = g a；h : IsLocalMin f a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyLE.isMinFilter`：Filter.EventuallyLE.isMinFilter {α β : 
Type*} [Preorder β] {f g : α -> β} {a : α} {l : Filter α} (hle : f <=ᶠ[l] g) (hf
ga : f a = g a) (h : …
-/
theorem Filter.EventuallyLE.isLocalMin {f g : α → β} {a : α} (hle : f ≤ᶠ[𝓝 a] g) (hfga : f a = g a)
    (h : IsLocalMin f a) : IsLocalMin g a :=
  hle.isMinFilter hfga h

nonrec theorem IsLocalMin.congr {f g : α → β} {a : α} (h : IsLocalMin f a) (heq : f =ᶠ[𝓝 a] g) :
    IsLocalMin g a :=
  h.congr heq heq.eq_of_nhds
/-
**Filter.EventuallyEq.isLocalMin_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.EventuallyEq.isLocalMin_iff {f g : α -> β} {a : α} (heq : f =ᶠ[𝓝 a]
 g) : IsLocalMin f a ↔ IsLocalMin g a
参数：heq : f =ᶠ[𝓝 a] g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.isMinFilter_iff`：Filter.EventuallyEq.isMinFilter_iff
 {α β : Type*} [Preorder β] {f g : α -> β} {a : α} {l : Filter α} (heq : f =ᶠ[l]
 g) (hfga : f a = g a) : …
· 使用定理 `Filter.EventuallyEq.eq_of_nhds`：Filter.EventuallyEq.eq_of_nhds {f g : X 
-> α} (h : f =ᶠ[𝓝 x] g) : f x = g x
-/
theorem Filter.EventuallyEq.isLocalMin_iff {f g : α → β} {a : α} (heq : f =ᶠ[𝓝 a] g) :
    IsLocalMin f a ↔ IsLocalMin g a :=
  heq.isMinFilter_iff heq.eq_of_nhds

nonrec theorem IsLocalExtr.congr {f g : α → β} {a : α} (h : IsLocalExtr f a) (heq : f =ᶠ[𝓝 a] g) :
    IsLocalExtr g a :=
  h.congr heq heq.eq_of_nhds
/-
**Filter.EventuallyEq.isLocalExtr_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.EventuallyEq.isLocalExtr_iff {f g : α -> β} {a : α} (heq : f =ᶠ[𝓝 a
] g) : IsLocalExtr f a ↔ IsLocalExtr g a
参数：heq : f =ᶠ[𝓝 a] g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.isExtrFilter_iff`：Filter.EventuallyEq.isExtrFilter_i
ff {α β : Type*} [Preorder β] {f g : α -> β} {a : α} {l : Filter α} (heq : f =ᶠ[
l] g) (hfga : f a = g a) :…
· 使用定理 `Filter.EventuallyEq.eq_of_nhds`：Filter.EventuallyEq.eq_of_nhds {f g : X 
-> α} (h : f =ᶠ[𝓝 x] g) : f x = g x
-/
theorem Filter.EventuallyEq.isLocalExtr_iff {f g : α → β} {a : α} (heq : f =ᶠ[𝓝 a] g) :
    IsLocalExtr f a ↔ IsLocalExtr g a :=
  heq.isExtrFilter_iff heq.eq_of_nhds

end Eventually

/-- If `f` is monotone to the left and antitone to the right, then it has a local maximum. -/
/-
**isLocalMax_of_mono_anti'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isLocalMax_of_mono_anti' {α : Type*} [TopologicalSpace α] [LinearOrder α] 
{β : Type*} [Preorder β] {b : α} {f : α -> β} {a : Set α} (ha : a in 𝓝[<=] b) {c
 : Set α} (hc : c in 𝓝[>=] b) (h₀ : MonotoneOn f a) (h₁ : AntitoneOn f c) : IsLo
calMax f b
参数：ha : a in 𝓝[<=] b；hc : c in 𝓝[>=] b；h₀ : MonotoneOn f a；h₁ : AntitoneOn f c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mem_of_mem_nhdsWithin`：mem_of_mem_nhdsWithin {a : α} {s t : Set α} (ha :
 a in s) (ht : t in 𝓝[s] a) : a in t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `nhds_of_Ici_Iic`：nhds_of_Ici_Iic [LinearOrder α] {b : α} {L : Set α} (hL
 : L in 𝓝[<=] b) {R : Set α} (hR : R in 𝓝[>=] b) : L inter Iic b union R inter I
ci b …
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p

--- 原说明 ---
If `f` is monotone to the left and antitone to the right, then it has a local ma
ximum.
-/
lemma isLocalMax_of_mono_anti' {α : Type*} [TopologicalSpace α] [LinearOrder α]
    {β : Type*} [Preorder β] {b : α} {f : α → β}
    {a : Set α} (ha : a ∈ 𝓝[≤] b) {c : Set α} (hc : c ∈ 𝓝[≥] b)
    (h₀ : MonotoneOn f a) (h₁ : AntitoneOn f c) : IsLocalMax f b :=
  have : b ∈ a := mem_of_mem_nhdsWithin (by simp) ha
  have : b ∈ c := mem_of_mem_nhdsWithin (by simp) hc
  mem_of_superset (nhds_of_Ici_Iic ha hc) (fun x _ => by rcases le_total x b <;> aesop)

/-- If `f` is antitone to the left and monotone to the right, then it has a local minimum. -/
/-
**isLocalMin_of_anti_mono'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isLocalMin_of_anti_mono' {α : Type*} [TopologicalSpace α] [LinearOrder α] 
{β : Type*} [Preorder β] {b : α} {f : α -> β} {a : Set α} (ha : a in 𝓝[<=] b) {c
 : Set α} (hc : c in 𝓝[>=] b) (h₀ : AntitoneOn f a) (h₁ : MonotoneOn f c) : IsLo
calMin f b
参数：ha : a in 𝓝[<=] b；hc : c in 𝓝[>=] b；h₀ : AntitoneOn f a；h₁ : MonotoneOn f c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mem_of_mem_nhdsWithin`：mem_of_mem_nhdsWithin {a : α} {s t : Set α} (ha :
 a in s) (ht : t in 𝓝[s] a) : a in t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `nhds_of_Ici_Iic`：nhds_of_Ici_Iic [LinearOrder α] {b : α} {L : Set α} (hL
 : L in 𝓝[<=] b) {R : Set α} (hR : R in 𝓝[>=] b) : L inter Iic b union R inter I
ci b …
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p

--- 原说明 ---
If `f` is antitone to the left and monotone to the right, then it has a local mi
nimum.
-/
lemma isLocalMin_of_anti_mono' {α : Type*} [TopologicalSpace α] [LinearOrder α]
    {β : Type*} [Preorder β] {b : α} {f : α → β}
    {a : Set α} (ha : a ∈ 𝓝[≤] b) {c : Set α} (hc : c ∈ 𝓝[≥] b)
    (h₀ : AntitoneOn f a) (h₁ : MonotoneOn f c) : IsLocalMin f b :=
  have : b ∈ a := mem_of_mem_nhdsWithin (by simp) ha
  have : b ∈ c := mem_of_mem_nhdsWithin (by simp) hc
  mem_of_superset (nhds_of_Ici_Iic ha hc) (fun x _ => by rcases le_total x b <;> aesop)
