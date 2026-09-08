/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Order.Filter.Tendsto
public import Mathlib.Order.ConditionallyCompleteLattice.Indexed
public import Mathlib.Algebra.Order.Group.Defs
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Minimum and maximum w.r.t. a filter and on a set

## Main Definitions

This file defines six predicates of the form `isAB`, where `A` is `Min`, `Max`, or `Extr`,
and `B` is `Filter` or `On`.

* `isMinFilter f l a` means that `f a ≤ f x` in some `l`-neighborhood of `a`;
* `isMaxFilter f l a` means that `f x ≤ f a` in some `l`-neighborhood of `a`;
* `isExtrFilter f l a` means `isMinFilter f l a` or `isMaxFilter f l a`.

Similar predicates with `on` suffix are particular cases for `l = 𝓟 s`.

## Main statements

### Change of the filter (set) argument

* `is*Filter.filter_mono` : replace the filter with a smaller one;
* `is*Filter.filter_inf` : replace a filter `l` with `l ⊓ l'`;
* `is*On.on_subset` : restrict to a smaller set;
* `is*Pn.inter` : replace a set `s` with `s ∩ t`.

### Composition

* `is**.comp_mono` : if `x` is an extremum for `f` and `g` is a monotone function,
  then `x` is an extremum for `g ∘ f`;
* `is**.comp_antitone` : similarly for the case of antitone `g`;
* `is**.bicomp_mono` : if `x` is an extremum of the same type for `f` and `g`
  and a binary operation `op` is monotone in both arguments, then `x` is an extremum
  of the same type for `fun x => op (f x) (g x)`.
* `is*Filter.comp_tendsto` : if `g x` is an extremum for `f` w.r.t. `l'` and `Tendsto g l l'`,
  then `x` is an extremum for `f ∘ g` w.r.t. `l`.
* `is*On.on_preimage` : if `g x` is an extremum for `f` on `s`, then `x` is an extremum
  for `f ∘ g` on `g ⁻¹' s`.

### Algebraic operations

* `is**.add` : if `x` is an extremum of the same type for two functions,
  then it is an extremum of the same type for their sum;
* `is**.neg` : if `x` is an extremum for `f`, then it is an extremum
  of the opposite type for `-f`;
* `is**.sub` : if `x` is a minimum for `f` and a maximum for `g`,
  then it is a minimum for `f - g` and a maximum for `g - f`;
* `is**.max`, `is**.min`, `is**.sup`, `is**.inf` : similarly for `is**.add`
  for pointwise `max`, `min`, `sup`, `inf`, respectively.


### Miscellaneous definitions

* `is**_const` : any point is both a minimum and maximum for a constant function;
* `isMin/Max*.isExt` : any minimum/maximum point is an extremum;
* `is**.dual`, `is**.undual`: conversion between codomains `α` and `dual α`;

## Missing features (TODO)

* Multiplication and division;
* `is**.bicompl` : if `x` is a minimum for `f`, `y` is a minimum for `g`, and `op` is a monotone
  binary operation, then `(x, y)` is a minimum for `uncurry (bicompl op f g)`. From this point
  of view, `is**.bicomp` is a composition
* It would be nice to have a tactic that specializes `comp_(anti)mono` or `bicomp_mono`
  based on a proof of monotonicity of a given (binary) function. The tactic should maintain a `meta`
  list of known (anti)monotone (binary) functions with their names, as well as a list of special
  types of filters, and define the missing lemmas once one of these two lists grows.
-/

@[expose] public section


universe u v w x

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type x}

open Set Filter Relator

section Preorder

variable [Preorder β] [Preorder γ]
variable (f : α → β) (s : Set α) (l : Filter α) (a : α)

/-! ### Definitions -/


/-- `IsMinFilter f l a` means that `f a ≤ f x` for all `x` in some `l`-neighborhood of `a` -/
/-
**IsMinFilter** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsMinFilter : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`IsMinFilter f l a` means that `f a ≤ f x` for all `x` in some `l`-neighborhood 
of `a`
-/
def IsMinFilter : Prop :=
  ∀ᶠ x in l, f a ≤ f x

/-- `is_maxFilter f l a` means that `f x ≤ f a` for all `x` in some `l`-neighborhood of `a` -/
/-
**IsMaxFilter** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsMaxFilter : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`is_maxFilter f l a` means that `f x ≤ f a` for all `x` in some `l`-neighborhood
 of `a`
-/
def IsMaxFilter : Prop :=
  ∀ᶠ x in l, f x ≤ f a

/-- `IsExtrFilter f l a` means `IsMinFilter f l a` or `IsMaxFilter f l a` -/
/-
**IsExtrFilter** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsExtrFilter : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`IsExtrFilter f l a` means `IsMinFilter f l a` or `IsMaxFilter f l a`
-/
def IsExtrFilter : Prop :=
  IsMinFilter f l a ∨ IsMaxFilter f l a

/-- `IsMinOn f s a` means that `f a ≤ f x` for all `x ∈ s`. Note that we do not assume `a ∈ s`. -/
/-
**IsMinOn** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsMinOn
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`IsMinOn f s a` means that `f a ≤ f x` for all `x ∈ s`. Note that we do not assu
me `a ∈ s`.
-/
def IsMinOn :=
  IsMinFilter f (𝓟 s) a

/-- `IsMaxOn f s a` means that `f x ≤ f a` for all `x ∈ s`. Note that we do not assume `a ∈ s`. -/
/-
**IsMaxOn** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsMaxOn
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`IsMaxOn f s a` means that `f x ≤ f a` for all `x ∈ s`. Note that we do not assu
me `a ∈ s`.
-/
def IsMaxOn :=
  IsMaxFilter f (𝓟 s) a

/-- `IsExtrOn f s a` means `IsMinOn f s a` or `IsMaxOn f s a` -/
@[wikidata Q845060]
/-
**IsExtrOn** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsExtrOn : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`IsExtrOn f s a` means `IsMinOn f s a` or `IsMaxOn f s a`
-/
def IsExtrOn : Prop :=
  IsExtrFilter f (𝓟 s) a

variable {f s a l} {t : Set α} {l' : Filter α}
/-
**IsExtrOn.elim** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsExtrOn.elim {p : Prop} : IsExtrOn f s a -> (IsMinOn f s a -> p) -> (IsMa
xOn f s a -> p) -> p
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
-/
theorem IsExtrOn.elim {p : Prop} : IsExtrOn f s a → (IsMinOn f s a → p) → (IsMaxOn f s a → p) → p :=
  Or.elim
/-
**isMinOn_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isMinOn_iff : IsMinOn f s a ↔ forall x in s, f a <= f x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isMinOn_iff : IsMinOn f s a ↔ ∀ x ∈ s, f a ≤ f x :=
  Iff.rfl
/-
**isMaxOn_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isMaxOn_iff : IsMaxOn f s a ↔ forall x in s, f x <= f a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isMaxOn_iff : IsMaxOn f s a ↔ ∀ x ∈ s, f x ≤ f a :=
  Iff.rfl
/-
**isMinOn_univ_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isMinOn_univ_iff : IsMinOn f univ a ↔ forall x, f a <= f x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Set.univ_subset_iff`：univ_subset_iff {s : Set α} : univ subseteq s ↔ s =
 univ
· 使用定理 `Set.eq_univ_iff_forall`：eq_univ_iff_forall {s : Set α} : s = univ ↔ fora
ll x, x in s
-/
theorem isMinOn_univ_iff : IsMinOn f univ a ↔ ∀ x, f a ≤ f x :=
  univ_subset_iff.trans eq_univ_iff_forall
/-
**isMaxOn_univ_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isMaxOn_univ_iff : IsMaxOn f univ a ↔ forall x, f x <= f a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Set.univ_subset_iff`：univ_subset_iff {s : Set α} : univ subseteq s ↔ s =
 univ
· 使用定理 `Set.eq_univ_iff_forall`：eq_univ_iff_forall {s : Set α} : s = univ ↔ fora
ll x, x in s
-/
theorem isMaxOn_univ_iff : IsMaxOn f univ a ↔ ∀ x, f x ≤ f a :=
  univ_subset_iff.trans eq_univ_iff_forall
/-
**IsMinOn.bddBelow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMinOn.bddBelow (h : IsMinOn f s a) : BddBelow (f '' s)
参数：h : IsMinOn f s a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem IsMinOn.bddBelow (h : IsMinOn f s a) :
    BddBelow (f '' s) :=
  ⟨f a, by simpa [mem_lowerBounds] using! h⟩
/-
**IsMinOn.isGLB** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMinOn.isGLB (ha : a in s) (hfsa : IsMinOn f s a) : IsGLB {f x | x in s} 
(f a)
参数：ha : a in s；hfsa : IsMinOn f s a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isGLB_iff_le_iff`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α} {a : 
α}, IsGLB s a ↔ ∀ (b : α), b ≤ a ↔ b ∈ lowerBounds s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
-/
theorem IsMinOn.isGLB (ha : a ∈ s) (hfsa : IsMinOn f s a) :
    IsGLB {f x | x ∈ s} (f a) := by
  rw [isGLB_iff_le_iff]
  intro b
  simp only [mem_lowerBounds, mem_ofPred_eq, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  exact ⟨fun hba x hx ↦ le_trans hba (hfsa hx), fun hb ↦ hb a ha⟩
/-
**IsMaxOn.isLUB** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMaxOn.isLUB (ha : a in s) (hfsa : IsMaxOn f s a) : IsLUB {f x | x in s} 
(f a)
参数：ha : a in s；hfsa : IsMaxOn f s a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsMinOn.isGLB`：IsMinOn.isGLB (ha : a in s) (hfsa : IsMinOn f s a) : IsGL
B {f x | x in s} (f a)
-/
theorem IsMaxOn.isLUB (ha : a ∈ s) (hfsa : IsMaxOn f s a) :
    IsLUB {f x | x ∈ s} (f a) :=
  IsMinOn.isGLB (α := αᵒᵈ) (β := βᵒᵈ) ha hfsa
/-
**IsMaxOn.bddAbove** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMaxOn.bddAbove (h : IsMaxOn f s a) : BddAbove (f '' s)
参数：h : IsMaxOn f s a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem IsMaxOn.bddAbove (h : IsMaxOn f s a) :
    BddAbove (f '' s) :=
  ⟨f a, by simpa [mem_upperBounds] using! h⟩
/-
**IsMinFilter.tendsto_principal_Ici** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMinFilter.tendsto_principal_Ici (h : IsMinFilter f l a) : Tendsto f l (𝓟
 <| Ici (f a))
参数：h : IsMinFilter f l a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.tendsto_principal`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l
 : Filter α} {s : Set β},   Filter.Tendsto f l (Filter.principal s) ↔ ∀ᶠ (a : α)
 in l, f a ∈ s
-/
theorem IsMinFilter.tendsto_principal_Ici (h : IsMinFilter f l a) : Tendsto f l (𝓟 <| Ici (f a)) :=
  tendsto_principal.2 h
/-
**IsMaxFilter.tendsto_principal_Iic** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMaxFilter.tendsto_principal_Iic (h : IsMaxFilter f l a) : Tendsto f l (𝓟
 <| Iic (f a))
参数：h : IsMaxFilter f l a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.tendsto_principal`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l
 : Filter α} {s : Set β},   Filter.Tendsto f l (Filter.principal s) ↔ ∀ᶠ (a : α)
 in l, f a ∈ s
-/
theorem IsMaxFilter.tendsto_principal_Iic (h : IsMaxFilter f l a) : Tendsto f l (𝓟 <| Iic (f a)) :=
  tendsto_principal.2 h

/-! ### Conversion to `IsExtr*` -/


/-
**IsMinFilter.isExtr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMinFilter.isExtr : IsMinFilter f l a -> IsExtrFilter f l a
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Conversion to `IsExtr*`
-/
theorem IsMinFilter.isExtr : IsMinFilter f l a → IsExtrFilter f l a :=
  Or.inl
/-
**IsMaxFilter.isExtr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMaxFilter.isExtr : IsMaxFilter f l a -> IsExtrFilter f l a
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IsMaxFilter.isExtr : IsMaxFilter f l a → IsExtrFilter f l a :=
  Or.inr
/-
**IsMinOn.isExtr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMinOn.isExtr (h : IsMinOn f s a) : IsExtrOn f s a
参数：h : IsMinOn f s a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsMinFilter.isExtr`：IsMinFilter.isExtr : IsMinFilter f l a -> IsExtrFilt
er f l a
-/
theorem IsMinOn.isExtr (h : IsMinOn f s a) : IsExtrOn f s a :=
  IsMinFilter.isExtr h
/-
**IsMaxOn.isExtr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMaxOn.isExtr (h : IsMaxOn f s a) : IsExtrOn f s a
参数：h : IsMaxOn f s a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsMaxFilter.isExtr`：IsMaxFilter.isExtr : IsMaxFilter f l a -> IsExtrFilt
er f l a
-/
theorem IsMaxOn.isExtr (h : IsMaxOn f s a) : IsExtrOn f s a :=
  IsMaxFilter.isExtr h

/-! ### Constant function -/


/-
**isMinFilter_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isMinFilter_const {b : β} : IsMinFilter (fun _ => b) l a
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用引理 `le_rfl`：le_rfl : a <= a

--- 原说明 ---
### Constant function
-/
theorem isMinFilter_const {b : β} : IsMinFilter (fun _ => b) l a :=
  univ_mem' fun _ => le_rfl
/-
**isMaxFilter_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isMaxFilter_const {b : β} : IsMaxFilter (fun _ => b) l a
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem isMaxFilter_const {b : β} : IsMaxFilter (fun _ => b) l a :=
  univ_mem' fun _ => le_rfl
/-
**isExtrFilter_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isExtrFilter_const {b : β} : IsExtrFilter (fun _ => b) l a
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsMinFilter.isExtr`：IsMinFilter.isExtr : IsMinFilter f l a -> IsExtrFilt
er f l a
· 使用定理 `isMinFilter_const`：isMinFilter_const {b : β} : IsMinFilter (fun _ => b) 
l a
-/
theorem isExtrFilter_const {b : β} : IsExtrFilter (fun _ => b) l a :=
  isMinFilter_const.isExtr
/-
**isMinOn_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isMinOn_const {b : β} : IsMinOn (fun _ => b) s a
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isMinFilter_const`：isMinFilter_const {b : β} : IsMinFilter (fun _ => b) 
l a
-/
theorem isMinOn_const {b : β} : IsMinOn (fun _ => b) s a :=
  isMinFilter_const
/-
**isMaxOn_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isMaxOn_const {b : β} : IsMaxOn (fun _ => b) s a
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isMaxFilter_const`：isMaxFilter_const {b : β} : IsMaxFilter (fun _ => b) 
l a
-/
theorem isMaxOn_const {b : β} : IsMaxOn (fun _ => b) s a :=
  isMaxFilter_const
/-
**isExtrOn_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isExtrOn_const {b : β} : IsExtrOn (fun _ => b) s a
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isExtrFilter_const`：isExtrFilter_const {b : β} : IsExtrFilter (fun _ => 
b) l a
-/
theorem isExtrOn_const {b : β} : IsExtrOn (fun _ => b) s a :=
  isExtrFilter_const

/-- If `f` has a minimum and a maximum both given by `f a` along the filter `l`, then it is
eventually equal to `f a` along the filter. -/
/-
**eventuallyEq_of_isMinFilter_of_isMaxFilter** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：eventuallyEq_of_isMinFilter_of_isMaxFilter {β : Type*} [PartialOrder β] {f
 : α -> β} (h₁ : IsMinFilter f l a) (h₂ : IsMaxFilter f l a) : f =ᶠ[l] (fun _ =>
 f a)
参数：h₁ : IsMinFilter f l a；h₂ : IsMaxFilter f l a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f

--- 原说明 ---
If `f` has a minimum and a maximum both given by `f a` along the filter `l`, the
n it is
eventually equal to `f a` along the filter.
-/
lemma eventuallyEq_of_isMinFilter_of_isMaxFilter {β : Type*} [PartialOrder β] {f : α → β}
    (h₁ : IsMinFilter f l a) (h₂ : IsMaxFilter f l a) : f =ᶠ[l] (fun _ ↦ f a) := by
  filter_upwards [h₁, h₂] using by grind

/-! ### Order dual -/


open OrderDual (toDual)

/-
**isMinFilter_dual_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isMinFilter_dual_iff : IsMinFilter (toDual ∘ f) l a ↔ IsMaxFilter f l a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isMinFilter_dual_iff : IsMinFilter (toDual ∘ f) l a ↔ IsMaxFilter f l a :=
  Iff.rfl
/-
**isMaxFilter_dual_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isMaxFilter_dual_iff : IsMaxFilter (toDual ∘ f) l a ↔ IsMinFilter f l a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isMaxFilter_dual_iff : IsMaxFilter (toDual ∘ f) l a ↔ IsMinFilter f l a :=
  Iff.rfl
/-
**isExtrFilter_dual_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isExtrFilter_dual_iff : IsExtrFilter (toDual ∘ f) l a ↔ IsExtrFilter f l a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `or_comm`：∀ {a b : Prop}, a ∨ b ↔ b ∨ a
-/
theorem isExtrFilter_dual_iff : IsExtrFilter (toDual ∘ f) l a ↔ IsExtrFilter f l a :=
  or_comm

alias ⟨IsMinFilter.undual, IsMaxFilter.dual⟩ := isMinFilter_dual_iff

alias ⟨IsMaxFilter.undual, IsMinFilter.dual⟩ := isMaxFilter_dual_iff

alias ⟨IsExtrFilter.undual, IsExtrFilter.dual⟩ := isExtrFilter_dual_iff
/-
**isMinOn_dual_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isMinOn_dual_iff : IsMinOn (toDual ∘ f) s a ↔ IsMaxOn f s a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isMinOn_dual_iff : IsMinOn (toDual ∘ f) s a ↔ IsMaxOn f s a :=
  Iff.rfl
/-
**isMaxOn_dual_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isMaxOn_dual_iff : IsMaxOn (toDual ∘ f) s a ↔ IsMinOn f s a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isMaxOn_dual_iff : IsMaxOn (toDual ∘ f) s a ↔ IsMinOn f s a :=
  Iff.rfl
/-
**isExtrOn_dual_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isExtrOn_dual_iff : IsExtrOn (toDual ∘ f) s a ↔ IsExtrOn f s a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `or_comm`：∀ {a b : Prop}, a ∨ b ↔ b ∨ a
-/
theorem isExtrOn_dual_iff : IsExtrOn (toDual ∘ f) s a ↔ IsExtrOn f s a :=
  or_comm

alias ⟨IsMinOn.undual, IsMaxOn.dual⟩ := isMinOn_dual_iff

alias ⟨IsMaxOn.undual, IsMinOn.dual⟩ := isMaxOn_dual_iff

alias ⟨IsExtrOn.undual, IsExtrOn.dual⟩ := isExtrOn_dual_iff

/-! ### Operations on the filter/set -/


/-
**IsMinFilter.filter_mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMinFilter.filter_mono (h : IsMinFilter f l a) (hl : l' <= l) : IsMinFilt
er f l' a
参数：h : IsMinFilter f l a；hl : l' <= l。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Operations on the filter/set
-/
theorem IsMinFilter.filter_mono (h : IsMinFilter f l a) (hl : l' ≤ l) : IsMinFilter f l' a :=
  hl h
/-
**IsMaxFilter.filter_mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMaxFilter.filter_mono (h : IsMaxFilter f l a) (hl : l' <= l) : IsMaxFilt
er f l' a
参数：h : IsMaxFilter f l a；hl : l' <= l。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IsMaxFilter.filter_mono (h : IsMaxFilter f l a) (hl : l' ≤ l) : IsMaxFilter f l' a :=
  hl h
/-
**IsExtrFilter.filter_mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsExtrFilter.filter_mono (h : IsExtrFilter f l a) (hl : l' <= l) : IsExtrF
ilter f l' a
参数：h : IsExtrFilter f l a；hl : l' <= l。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `IsMinFilter.isExtr`：IsMinFilter.isExtr : IsMinFilter f l a -> IsExtrFilt
er f l a
· 使用定理 `IsMinFilter.filter_mono`：IsMinFilter.filter_mono (h : IsMinFilter f l a)
 (hl : l' <= l) : IsMinFilter f l' a
· 使用定理 `IsMaxFilter.isExtr`：IsMaxFilter.isExtr : IsMaxFilter f l a -> IsExtrFilt
er f l a
· 使用定理 `IsMaxFilter.filter_mono`：IsMaxFilter.filter_mono (h : IsMaxFilter f l a)
 (hl : l' <= l) : IsMaxFilter f l' a
-/
theorem IsExtrFilter.filter_mono (h : IsExtrFilter f l a) (hl : l' ≤ l) : IsExtrFilter f l' a :=
  h.elim (fun h => (h.filter_mono hl).isExtr) fun h => (h.filter_mono hl).isExtr
/-
**IsMinFilter.filter_inf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMinFilter.filter_inf (h : IsMinFilter f l a) (l') : IsMinFilter f (l ⊓ l
') a
参数：h : IsMinFilter f l a；l'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsMinFilter.filter_mono`：IsMinFilter.filter_mono (h : IsMinFilter f l a)
 (hl : l' <= l) : IsMinFilter f l' a
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
-/
theorem IsMinFilter.filter_inf (h : IsMinFilter f l a) (l') : IsMinFilter f (l ⊓ l') a :=
  h.filter_mono inf_le_left
/-
**IsMaxFilter.filter_inf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMaxFilter.filter_inf (h : IsMaxFilter f l a) (l') : IsMaxFilter f (l ⊓ l
') a
参数：h : IsMaxFilter f l a；l'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsMaxFilter.filter_mono`：IsMaxFilter.filter_mono (h : IsMaxFilter f l a)
 (hl : l' <= l) : IsMaxFilter f l' a
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
-/
theorem IsMaxFilter.filter_inf (h : IsMaxFilter f l a) (l') : IsMaxFilter f (l ⊓ l') a :=
  h.filter_mono inf_le_left
/-
**IsExtrFilter.filter_inf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsExtrFilter.filter_inf (h : IsExtrFilter f l a) (l') : IsExtrFilter f (l 
⊓ l') a
参数：h : IsExtrFilter f l a；l'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsExtrFilter.filter_mono`：IsExtrFilter.filter_mono (h : IsExtrFilter f l
 a) (hl : l' <= l) : IsExtrFilter f l' a
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
-/
theorem IsExtrFilter.filter_inf (h : IsExtrFilter f l a) (l') : IsExtrFilter f (l ⊓ l') a :=
  h.filter_mono inf_le_left
/-
**IsMinOn.on_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMinOn.on_subset (hf : IsMinOn f t a) (h : s subseteq t) : IsMinOn f s a
参数：hf : IsMinOn f t a；h : s subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsMinFilter.filter_mono`：IsMinFilter.filter_mono (h : IsMinFilter f l a)
 (hl : l' <= l) : IsMinFilter f l' a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.principal_mono`：principal_mono {s t : Set α} : 𝓟 s <= 𝓟 t ↔ s sub
seteq t
-/
theorem IsMinOn.on_subset (hf : IsMinOn f t a) (h : s ⊆ t) : IsMinOn f s a :=
  hf.filter_mono <| principal_mono.2 h
/-
**IsMaxOn.on_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMaxOn.on_subset (hf : IsMaxOn f t a) (h : s subseteq t) : IsMaxOn f s a
参数：hf : IsMaxOn f t a；h : s subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsMaxFilter.filter_mono`：IsMaxFilter.filter_mono (h : IsMaxFilter f l a)
 (hl : l' <= l) : IsMaxFilter f l' a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.principal_mono`：principal_mono {s t : Set α} : 𝓟 s <= 𝓟 t ↔ s sub
seteq t
-/
theorem IsMaxOn.on_subset (hf : IsMaxOn f t a) (h : s ⊆ t) : IsMaxOn f s a :=
  hf.filter_mono <| principal_mono.2 h
/-
**IsExtrOn.on_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsExtrOn.on_subset (hf : IsExtrOn f t a) (h : s subseteq t) : IsExtrOn f s
 a
参数：hf : IsExtrOn f t a；h : s subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsExtrFilter.filter_mono`：IsExtrFilter.filter_mono (h : IsExtrFilter f l
 a) (hl : l' <= l) : IsExtrFilter f l' a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.principal_mono`：principal_mono {s t : Set α} : 𝓟 s <= 𝓟 t ↔ s sub
seteq t
-/
theorem IsExtrOn.on_subset (hf : IsExtrOn f t a) (h : s ⊆ t) : IsExtrOn f s a :=
  hf.filter_mono <| principal_mono.2 h
/-
**IsMinOn.inter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMinOn.inter (hf : IsMinOn f s a) (t) : IsMinOn f (s inter t) a
参数：hf : IsMinOn f s a；t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsMinOn.on_subset`：IsMinOn.on_subset (hf : IsMinOn f t a) (h : s subsete
q t) : IsMinOn f s a
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
-/
theorem IsMinOn.inter (hf : IsMinOn f s a) (t) : IsMinOn f (s ∩ t) a :=
  hf.on_subset inter_subset_left
/-
**IsMaxOn.inter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMaxOn.inter (hf : IsMaxOn f s a) (t) : IsMaxOn f (s inter t) a
参数：hf : IsMaxOn f s a；t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsMaxOn.on_subset`：IsMaxOn.on_subset (hf : IsMaxOn f t a) (h : s subsete
q t) : IsMaxOn f s a
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
-/
theorem IsMaxOn.inter (hf : IsMaxOn f s a) (t) : IsMaxOn f (s ∩ t) a :=
  hf.on_subset inter_subset_left
/-
**IsExtrOn.inter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsExtrOn.inter (hf : IsExtrOn f s a) (t) : IsExtrOn f (s inter t) a
参数：hf : IsExtrOn f s a；t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsExtrOn.on_subset`：IsExtrOn.on_subset (hf : IsExtrOn f t a) (h : s subs
eteq t) : IsExtrOn f s a
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
-/
theorem IsExtrOn.inter (hf : IsExtrOn f s a) (t) : IsExtrOn f (s ∩ t) a :=
  hf.on_subset inter_subset_left

/-! ### Composition with (anti)monotone functions -/


/-
**IsMinFilter.comp_mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMinFilter.comp_mono (hf : IsMinFilter f l a) {g : β -> γ} (hg : Monotone
 g) : IsMinFilter (g ∘ f) l a
参数：hf : IsMinFilter f l a；hg : Monotone g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f

--- 原说明 ---
### Composition with (anti)monotone functions
-/
theorem IsMinFilter.comp_mono (hf : IsMinFilter f l a) {g : β → γ} (hg : Monotone g) :
    IsMinFilter (g ∘ f) l a :=
  mem_of_superset hf fun _x hx => hg hx
/-
**IsMaxFilter.comp_mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMaxFilter.comp_mono (hf : IsMaxFilter f l a) {g : β -> γ} (hg : Monotone
 g) : IsMaxFilter (g ∘ f) l a
参数：hf : IsMaxFilter f l a；hg : Monotone g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
-/
theorem IsMaxFilter.comp_mono (hf : IsMaxFilter f l a) {g : β → γ} (hg : Monotone g) :
    IsMaxFilter (g ∘ f) l a :=
  mem_of_superset hf fun _x hx => hg hx
/-
**IsExtrFilter.comp_mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsExtrFilter.comp_mono (hf : IsExtrFilter f l a) {g : β -> γ} (hg : Monoto
ne g) : IsExtrFilter (g ∘ f) l a
参数：hf : IsExtrFilter f l a；hg : Monotone g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `IsMinFilter.isExtr`：IsMinFilter.isExtr : IsMinFilter f l a -> IsExtrFilt
er f l a
· 使用定理 `IsMinFilter.comp_mono`：IsMinFilter.comp_mono (hf : IsMinFilter f l a) {g
 : β -> γ} (hg : Monotone g) : IsMinFilter (g ∘ f) l a
· 使用定理 `IsMaxFilter.isExtr`：IsMaxFilter.isExtr : IsMaxFilter f l a -> IsExtrFilt
er f l a
· 使用定理 `IsMaxFilter.comp_mono`：IsMaxFilter.comp_mono (hf : IsMaxFilter f l a) {g
 : β -> γ} (hg : Monotone g) : IsMaxFilter (g ∘ f) l a
-/
theorem IsExtrFilter.comp_mono (hf : IsExtrFilter f l a) {g : β → γ} (hg : Monotone g) :
    IsExtrFilter (g ∘ f) l a :=
  hf.elim (fun hf => (hf.comp_mono hg).isExtr) fun hf => (hf.comp_mono hg).isExtr
/-
**IsMinFilter.comp_antitone** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMinFilter.comp_antitone (hf : IsMinFilter f l a) {g : β -> γ} (hg : Anti
tone g) : IsMaxFilter (g ∘ f) l a
参数：hf : IsMinFilter f l a；hg : Antitone g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsMaxFilter.comp_mono`：IsMaxFilter.comp_mono (hf : IsMaxFilter f l a) {g
 : β -> γ} (hg : Monotone g) : IsMaxFilter (g ∘ f) l a
· 使用定理 `IsMinFilter.dual`：∀ {α : Type u} {β : Type v} [inst : Preorder β] {f : α
 → β} {l : Filter α} {a : α},   IsMinFilter f l a → IsMaxFilter (⇑OrderDual.toDu
al ∘ f…
-/
theorem IsMinFilter.comp_antitone (hf : IsMinFilter f l a) {g : β → γ} (hg : Antitone g) :
    IsMaxFilter (g ∘ f) l a :=
  hf.dual.comp_mono fun _ _ h => hg h
/-
**IsMaxFilter.comp_antitone** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMaxFilter.comp_antitone (hf : IsMaxFilter f l a) {g : β -> γ} (hg : Anti
tone g) : IsMinFilter (g ∘ f) l a
参数：hf : IsMaxFilter f l a；hg : Antitone g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsMinFilter.comp_mono`：IsMinFilter.comp_mono (hf : IsMinFilter f l a) {g
 : β -> γ} (hg : Monotone g) : IsMinFilter (g ∘ f) l a
· 使用定理 `IsMaxFilter.dual`：∀ {α : Type u} {β : Type v} [inst : Preorder β] {f : α
 → β} {l : Filter α} {a : α},   IsMaxFilter f l a → IsMinFilter (⇑OrderDual.toDu
al ∘ f…
-/
theorem IsMaxFilter.comp_antitone (hf : IsMaxFilter f l a) {g : β → γ} (hg : Antitone g) :
    IsMinFilter (g ∘ f) l a :=
  hf.dual.comp_mono fun _ _ h => hg h
/-
**IsExtrFilter.comp_antitone** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsExtrFilter.comp_antitone (hf : IsExtrFilter f l a) {g : β -> γ} (hg : An
titone g) : IsExtrFilter (g ∘ f) l a
参数：hf : IsExtrFilter f l a；hg : Antitone g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsExtrFilter.comp_mono`：IsExtrFilter.comp_mono (hf : IsExtrFilter f l a)
 {g : β -> γ} (hg : Monotone g) : IsExtrFilter (g ∘ f) l a
· 使用定理 `IsExtrFilter.dual`：∀ {α : Type u} {β : Type v} [inst : Preorder β] {f : 
α → β} {l : Filter α} {a : α},   IsExtrFilter f l a → IsExtrFilter (⇑OrderDual.t
oDual ∘…
-/
theorem IsExtrFilter.comp_antitone (hf : IsExtrFilter f l a) {g : β → γ} (hg : Antitone g) :
    IsExtrFilter (g ∘ f) l a :=
  hf.dual.comp_mono fun _ _ h => hg h
/-
**IsMinOn.comp_mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMinOn.comp_mono (hf : IsMinOn f s a) {g : β -> γ} (hg : Monotone g) : Is
MinOn (g ∘ f) s a
参数：hf : IsMinOn f s a；hg : Monotone g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsMinFilter.comp_mono`：IsMinFilter.comp_mono (hf : IsMinFilter f l a) {g
 : β -> γ} (hg : Monotone g) : IsMinFilter (g ∘ f) l a
-/
theorem IsMinOn.comp_mono (hf : IsMinOn f s a) {g : β → γ} (hg : Monotone g) :
    IsMinOn (g ∘ f) s a :=
  IsMinFilter.comp_mono hf hg
/-
**IsMaxOn.comp_mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMaxOn.comp_mono (hf : IsMaxOn f s a) {g : β -> γ} (hg : Monotone g) : Is
MaxOn (g ∘ f) s a
参数：hf : IsMaxOn f s a；hg : Monotone g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsMaxFilter.comp_mono`：IsMaxFilter.comp_mono (hf : IsMaxFilter f l a) {g
 : β -> γ} (hg : Monotone g) : IsMaxFilter (g ∘ f) l a
-/
theorem IsMaxOn.comp_mono (hf : IsMaxOn f s a) {g : β → γ} (hg : Monotone g) :
    IsMaxOn (g ∘ f) s a :=
  IsMaxFilter.comp_mono hf hg
/-
**IsExtrOn.comp_mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsExtrOn.comp_mono (hf : IsExtrOn f s a) {g : β -> γ} (hg : Monotone g) : 
IsExtrOn (g ∘ f) s a
参数：hf : IsExtrOn f s a；hg : Monotone g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsExtrFilter.comp_mono`：IsExtrFilter.comp_mono (hf : IsExtrFilter f l a)
 {g : β -> γ} (hg : Monotone g) : IsExtrFilter (g ∘ f) l a
-/
theorem IsExtrOn.comp_mono (hf : IsExtrOn f s a) {g : β → γ} (hg : Monotone g) :
    IsExtrOn (g ∘ f) s a :=
  IsExtrFilter.comp_mono hf hg
/-
**IsMinOn.comp_antitone** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMinOn.comp_antitone (hf : IsMinOn f s a) {g : β -> γ} (hg : Antitone g) 
: IsMaxOn (g ∘ f) s a
参数：hf : IsMinOn f s a；hg : Antitone g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsMinFilter.comp_antitone`：IsMinFilter.comp_antitone (hf : IsMinFilter f
 l a) {g : β -> γ} (hg : Antitone g) : IsMaxFilter (g ∘ f) l a
-/
theorem IsMinOn.comp_antitone (hf : IsMinOn f s a) {g : β → γ} (hg : Antitone g) :
    IsMaxOn (g ∘ f) s a :=
  IsMinFilter.comp_antitone hf hg
/-
**IsMaxOn.comp_antitone** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMaxOn.comp_antitone (hf : IsMaxOn f s a) {g : β -> γ} (hg : Antitone g) 
: IsMinOn (g ∘ f) s a
参数：hf : IsMaxOn f s a；hg : Antitone g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsMaxFilter.comp_antitone`：IsMaxFilter.comp_antitone (hf : IsMaxFilter f
 l a) {g : β -> γ} (hg : Antitone g) : IsMinFilter (g ∘ f) l a
-/
theorem IsMaxOn.comp_antitone (hf : IsMaxOn f s a) {g : β → γ} (hg : Antitone g) :
    IsMinOn (g ∘ f) s a :=
  IsMaxFilter.comp_antitone hf hg
/-
**IsExtrOn.comp_antitone** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsExtrOn.comp_antitone (hf : IsExtrOn f s a) {g : β -> γ} (hg : Antitone g
) : IsExtrOn (g ∘ f) s a
参数：hf : IsExtrOn f s a；hg : Antitone g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsExtrFilter.comp_antitone`：IsExtrFilter.comp_antitone (hf : IsExtrFilte
r f l a) {g : β -> γ} (hg : Antitone g) : IsExtrFilter (g ∘ f) l a
-/
theorem IsExtrOn.comp_antitone (hf : IsExtrOn f s a) {g : β → γ} (hg : Antitone g) :
    IsExtrOn (g ∘ f) s a :=
  IsExtrFilter.comp_antitone hf hg
/-
**IsMinFilter.bicomp_mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMinFilter.bicomp_mono [Preorder δ] {op : β -> γ -> δ} (hop : ((· <= ·) ⇒
 (· <= ·) ⇒ (· <= ·)) op op) (hf : IsMinFilter f l a) {g : α -> γ} (hg : IsMinFi
lter g l a) : IsMinFilter (fun x => op (f x) (g x)) l a
参数：hop : ((· <= ·) ⇒ (· <= ·) ⇒ (· <= ·)) op op；hf : IsMinFilter f l a；hg : IsMi
nFilter g l a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
-/
theorem IsMinFilter.bicomp_mono [Preorder δ] {op : β → γ → δ}
    (hop : ((· ≤ ·) ⇒ (· ≤ ·) ⇒ (· ≤ ·)) op op) (hf : IsMinFilter f l a) {g : α → γ}
    (hg : IsMinFilter g l a) : IsMinFilter (fun x => op (f x) (g x)) l a :=
  mem_of_superset (inter_mem hf hg) fun _x ⟨hfx, hgx⟩ => hop hfx hgx
/-
**IsMaxFilter.bicomp_mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMaxFilter.bicomp_mono [Preorder δ] {op : β -> γ -> δ} (hop : ((· <= ·) ⇒
 (· <= ·) ⇒ (· <= ·)) op op) (hf : IsMaxFilter f l a) {g : α -> γ} (hg : IsMaxFi
lter g l a) : IsMaxFilter (fun x => op (f x) (g x)) l a
参数：hop : ((· <= ·) ⇒ (· <= ·) ⇒ (· <= ·)) op op；hf : IsMaxFilter f l a；hg : IsMa
xFilter g l a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
-/
theorem IsMaxFilter.bicomp_mono [Preorder δ] {op : β → γ → δ}
    (hop : ((· ≤ ·) ⇒ (· ≤ ·) ⇒ (· ≤ ·)) op op) (hf : IsMaxFilter f l a) {g : α → γ}
    (hg : IsMaxFilter g l a) : IsMaxFilter (fun x => op (f x) (g x)) l a :=
  mem_of_superset (inter_mem hf hg) fun _x ⟨hfx, hgx⟩ => hop hfx hgx

-- No `Extr` version because we need `hf` and `hg` to be of the same kind
/-
**IsMinOn.bicomp_mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMinOn.bicomp_mono [Preorder δ] {op : β -> γ -> δ} (hop : ((· <= ·) ⇒ (· 
<= ·) ⇒ (· <= ·)) op op) (hf : IsMinOn f s a) {g : α -> γ} (hg : IsMinOn g s a) 
: IsMinOn (fun x => op (f x) (g x)) s a
参数：hop : ((· <= ·) ⇒ (· <= ·) ⇒ (· <= ·)) op op；hf : IsMinOn f s a；hg : IsMinOn 
g s a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsMinFilter.bicomp_mono`：IsMinFilter.bicomp_mono [Preorder δ] {op : β ->
 γ -> δ} (hop : ((· <= ·) ⇒ (· <= ·) ⇒ (· <= ·)) op op) (hf : IsMinFilter f l a)
 {g : α -> γ}…
-/
theorem IsMinOn.bicomp_mono [Preorder δ] {op : β → γ → δ}
    (hop : ((· ≤ ·) ⇒ (· ≤ ·) ⇒ (· ≤ ·)) op op) (hf : IsMinOn f s a) {g : α → γ}
    (hg : IsMinOn g s a) : IsMinOn (fun x => op (f x) (g x)) s a :=
  IsMinFilter.bicomp_mono hop hf hg
/-
**IsMaxOn.bicomp_mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMaxOn.bicomp_mono [Preorder δ] {op : β -> γ -> δ} (hop : ((· <= ·) ⇒ (· 
<= ·) ⇒ (· <= ·)) op op) (hf : IsMaxOn f s a) {g : α -> γ} (hg : IsMaxOn g s a) 
: IsMaxOn (fun x => op (f x) (g x)) s a
参数：hop : ((· <= ·) ⇒ (· <= ·) ⇒ (· <= ·)) op op；hf : IsMaxOn f s a；hg : IsMaxOn 
g s a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsMaxFilter.bicomp_mono`：IsMaxFilter.bicomp_mono [Preorder δ] {op : β ->
 γ -> δ} (hop : ((· <= ·) ⇒ (· <= ·) ⇒ (· <= ·)) op op) (hf : IsMaxFilter f l a)
 {g : α -> γ}…
-/
theorem IsMaxOn.bicomp_mono [Preorder δ] {op : β → γ → δ}
    (hop : ((· ≤ ·) ⇒ (· ≤ ·) ⇒ (· ≤ ·)) op op) (hf : IsMaxOn f s a) {g : α → γ}
    (hg : IsMaxOn g s a) : IsMaxOn (fun x => op (f x) (g x)) s a :=
  IsMaxFilter.bicomp_mono hop hf hg

/-! ### Composition with `Tendsto` -/


/-
**IsMinFilter.comp_tendsto** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMinFilter.comp_tendsto {g : δ -> α} {l' : Filter δ} {b : δ} (hf : IsMinF
ilter f l (g b)) (hg : Tendsto g l' l) : IsMinFilter (f ∘ g) l' b
参数：hf : IsMinFilter f l (g b)；hg : Tendsto g l' l。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Composition with `Tendsto`
-/
theorem IsMinFilter.comp_tendsto {g : δ → α} {l' : Filter δ} {b : δ} (hf : IsMinFilter f l (g b))
    (hg : Tendsto g l' l) : IsMinFilter (f ∘ g) l' b :=
  hg hf
/-
**IsMaxFilter.comp_tendsto** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMaxFilter.comp_tendsto {g : δ -> α} {l' : Filter δ} {b : δ} (hf : IsMaxF
ilter f l (g b)) (hg : Tendsto g l' l) : IsMaxFilter (f ∘ g) l' b
参数：hf : IsMaxFilter f l (g b)；hg : Tendsto g l' l。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IsMaxFilter.comp_tendsto {g : δ → α} {l' : Filter δ} {b : δ} (hf : IsMaxFilter f l (g b))
    (hg : Tendsto g l' l) : IsMaxFilter (f ∘ g) l' b :=
  hg hf
/-
**IsExtrFilter.comp_tendsto** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsExtrFilter.comp_tendsto {g : δ -> α} {l' : Filter δ} {b : δ} (hf : IsExt
rFilter f l (g b)) (hg : Tendsto g l' l) : IsExtrFilter (f ∘ g) l' b
参数：hf : IsExtrFilter f l (g b)；hg : Tendsto g l' l。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `IsMinFilter.isExtr`：IsMinFilter.isExtr : IsMinFilter f l a -> IsExtrFilt
er f l a
· 使用定理 `IsMinFilter.comp_tendsto`：IsMinFilter.comp_tendsto {g : δ -> α} {l' : Fi
lter δ} {b : δ} (hf : IsMinFilter f l (g b)) (hg : Tendsto g l' l) : IsMinFilter
 (f ∘ g) l' b
· 使用定理 `IsMaxFilter.isExtr`：IsMaxFilter.isExtr : IsMaxFilter f l a -> IsExtrFilt
er f l a
· 使用定理 `IsMaxFilter.comp_tendsto`：IsMaxFilter.comp_tendsto {g : δ -> α} {l' : Fi
lter δ} {b : δ} (hf : IsMaxFilter f l (g b)) (hg : Tendsto g l' l) : IsMaxFilter
 (f ∘ g) l' b
-/
theorem IsExtrFilter.comp_tendsto {g : δ → α} {l' : Filter δ} {b : δ} (hf : IsExtrFilter f l (g b))
    (hg : Tendsto g l' l) : IsExtrFilter (f ∘ g) l' b :=
  hf.elim (fun hf => (hf.comp_tendsto hg).isExtr) fun hf => (hf.comp_tendsto hg).isExtr
/-
**IsMinOn.on_preimage** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMinOn.on_preimage (g : δ -> α) {b : δ} (hf : IsMinOn f s (g b)) : IsMinO
n (f ∘ g) (g ⁻¹' s) b
参数：g : δ -> α；hf : IsMinOn f s (g b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsMinFilter.comp_tendsto`：IsMinFilter.comp_tendsto {g : δ -> α} {l' : Fi
lter δ} {b : δ} (hf : IsMinFilter f l (g b)) (hg : Tendsto g l' l) : IsMinFilter
 (f ∘ g) l' b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.tendsto_principal_principal`：tendsto_principal_principal {f : α -
> β} {s : Set α} {t : Set β} : Tendsto f (𝓟 s) (𝓟 t) ↔ forall a in s, f a in t
· 使用定理 `Set.Subset.refl`：∀ {α : Type u} (a : Set α), a ⊆ a
-/
theorem IsMinOn.on_preimage (g : δ → α) {b : δ} (hf : IsMinOn f s (g b)) :
    IsMinOn (f ∘ g) (g ⁻¹' s) b :=
  hf.comp_tendsto (tendsto_principal_principal.mpr <| Subset.refl _)
/-
**IsMaxOn.on_preimage** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMaxOn.on_preimage (g : δ -> α) {b : δ} (hf : IsMaxOn f s (g b)) : IsMaxO
n (f ∘ g) (g ⁻¹' s) b
参数：g : δ -> α；hf : IsMaxOn f s (g b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsMaxFilter.comp_tendsto`：IsMaxFilter.comp_tendsto {g : δ -> α} {l' : Fi
lter δ} {b : δ} (hf : IsMaxFilter f l (g b)) (hg : Tendsto g l' l) : IsMaxFilter
 (f ∘ g) l' b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.tendsto_principal_principal`：tendsto_principal_principal {f : α -
> β} {s : Set α} {t : Set β} : Tendsto f (𝓟 s) (𝓟 t) ↔ forall a in s, f a in t
· 使用定理 `Set.Subset.refl`：∀ {α : Type u} (a : Set α), a ⊆ a
-/
theorem IsMaxOn.on_preimage (g : δ → α) {b : δ} (hf : IsMaxOn f s (g b)) :
    IsMaxOn (f ∘ g) (g ⁻¹' s) b :=
  hf.comp_tendsto (tendsto_principal_principal.mpr <| Subset.refl _)
/-
**IsExtrOn.on_preimage** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsExtrOn.on_preimage (g : δ -> α) {b : δ} (hf : IsExtrOn f s (g b)) : IsEx
trOn (f ∘ g) (g ⁻¹' s) b
参数：g : δ -> α；hf : IsExtrOn f s (g b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsExtrOn.elim`：IsExtrOn.elim {p : Prop} : IsExtrOn f s a -> (IsMinOn f s
 a -> p) -> (IsMaxOn f s a -> p) -> p
· 使用定理 `IsMinOn.isExtr`：IsMinOn.isExtr (h : IsMinOn f s a) : IsExtrOn f s a
· 使用定理 `IsMinOn.on_preimage`：IsMinOn.on_preimage (g : δ -> α) {b : δ} (hf : IsMi
nOn f s (g b)) : IsMinOn (f ∘ g) (g ⁻¹' s) b
· 使用定理 `IsMaxOn.isExtr`：IsMaxOn.isExtr (h : IsMaxOn f s a) : IsExtrOn f s a
· 使用定理 `IsMaxOn.on_preimage`：IsMaxOn.on_preimage (g : δ -> α) {b : δ} (hf : IsMa
xOn f s (g b)) : IsMaxOn (f ∘ g) (g ⁻¹' s) b
-/
theorem IsExtrOn.on_preimage (g : δ → α) {b : δ} (hf : IsExtrOn f s (g b)) :
    IsExtrOn (f ∘ g) (g ⁻¹' s) b :=
  hf.elim (fun hf => (hf.on_preimage g).isExtr) fun hf => (hf.on_preimage g).isExtr
/-
**IsMinOn.comp_mapsTo** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMinOn.comp_mapsTo {t : Set δ} {g : δ -> α} {b : δ} (hf : IsMinOn f s a) 
(hg : MapsTo g t s) (ha : g b = a) : IsMinOn (f ∘ g) t b
参数：hf : IsMinOn f s a；hg : MapsTo g t s；ha : g b = a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem IsMinOn.comp_mapsTo {t : Set δ} {g : δ → α} {b : δ} (hf : IsMinOn f s a) (hg : MapsTo g t s)
    (ha : g b = a) : IsMinOn (f ∘ g) t b := fun y hy => by
  simpa only [ha, (· ∘ ·)] using! hf (hg hy)
/-
**IsMaxOn.comp_mapsTo** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMaxOn.comp_mapsTo {t : Set δ} {g : δ -> α} {b : δ} (hf : IsMaxOn f s a) 
(hg : MapsTo g t s) (ha : g b = a) : IsMaxOn (f ∘ g) t b
参数：hf : IsMaxOn f s a；hg : MapsTo g t s；ha : g b = a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsMinOn.comp_mapsTo`：IsMinOn.comp_mapsTo {t : Set δ} {g : δ -> α} {b : δ
} (hf : IsMinOn f s a) (hg : MapsTo g t s) (ha : g b = a) : IsMinOn (f ∘ g) t b
· 使用定理 `IsMaxOn.dual`：∀ {α : Type u} {β : Type v} [inst : Preorder β] {f : α → β
} {s : Set α} {a : α},   IsMaxOn f s a → IsMinOn (⇑OrderDual.toDual ∘ f) s a
-/
theorem IsMaxOn.comp_mapsTo {t : Set δ} {g : δ → α} {b : δ} (hf : IsMaxOn f s a) (hg : MapsTo g t s)
    (ha : g b = a) : IsMaxOn (f ∘ g) t b :=
  hf.dual.comp_mapsTo hg ha
/-
**IsExtrOn.comp_mapsTo** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsExtrOn.comp_mapsTo {t : Set δ} {g : δ -> α} {b : δ} (hf : IsExtrOn f s a
) (hg : MapsTo g t s) (ha : g b = a) : IsExtrOn (f ∘ g) t b
参数：hf : IsExtrOn f s a；hg : MapsTo g t s；ha : g b = a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsExtrOn.elim`：IsExtrOn.elim {p : Prop} : IsExtrOn f s a -> (IsMinOn f s
 a -> p) -> (IsMaxOn f s a -> p) -> p
· 使用定理 `IsMinOn.comp_mapsTo`：IsMinOn.comp_mapsTo {t : Set δ} {g : δ -> α} {b : δ
} (hf : IsMinOn f s a) (hg : MapsTo g t s) (ha : g b = a) : IsMinOn (f ∘ g) t b
· 使用定理 `IsMaxOn.comp_mapsTo`：IsMaxOn.comp_mapsTo {t : Set δ} {g : δ -> α} {b : δ
} (hf : IsMaxOn f s a) (hg : MapsTo g t s) (ha : g b = a) : IsMaxOn (f ∘ g) t b
-/
theorem IsExtrOn.comp_mapsTo {t : Set δ} {g : δ → α} {b : δ} (hf : IsExtrOn f s a)
    (hg : MapsTo g t s) (ha : g b = a) : IsExtrOn (f ∘ g) t b :=
  hf.elim (fun h => Or.inl <| h.comp_mapsTo hg ha) fun h => Or.inr <| h.comp_mapsTo hg ha

end Preorder

/-! ### Pointwise addition -/


section OrderedAddCommMonoid

variable [AddCommMonoid β] [PartialOrder β] [IsOrderedAddMonoid β]
  {f g : α → β} {a : α} {s : Set α} {l : Filter α}

/-
**IsMinFilter.add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMinFilter.add (hf : IsMinFilter f l a) (hg : IsMinFilter g l a) : IsMinF
ilter (fun x => f x + g x) l a
参数：hf : IsMinFilter f l a；hg : IsMinFilter g l a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsMinFilter.bicomp_mono`：IsMinFilter.bicomp_mono [Preorder δ] {op : β ->
 γ -> δ} (hop : ((· <= ·) ⇒ (· <= ·) ⇒ (· <= ·)) op op) (hf : IsMinFilter f l a)
 {g : α -> γ}…
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
-/
theorem IsMinFilter.add (hf : IsMinFilter f l a) (hg : IsMinFilter g l a) :
    IsMinFilter (fun x => f x + g x) l a :=
  show IsMinFilter (fun x => f x + g x) l a from
    hf.bicomp_mono (fun _x _x' hx _y _y' hy => add_le_add hx hy) hg
/-
**IsMaxFilter.add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMaxFilter.add (hf : IsMaxFilter f l a) (hg : IsMaxFilter g l a) : IsMaxF
ilter (fun x => f x + g x) l a
参数：hf : IsMaxFilter f l a；hg : IsMaxFilter g l a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsMaxFilter.bicomp_mono`：IsMaxFilter.bicomp_mono [Preorder δ] {op : β ->
 γ -> δ} (hop : ((· <= ·) ⇒ (· <= ·) ⇒ (· <= ·)) op op) (hf : IsMaxFilter f l a)
 {g : α -> γ}…
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
-/
theorem IsMaxFilter.add (hf : IsMaxFilter f l a) (hg : IsMaxFilter g l a) :
    IsMaxFilter (fun x => f x + g x) l a :=
  show IsMaxFilter (fun x => f x + g x) l a from
    hf.bicomp_mono (fun _x _x' hx _y _y' hy => add_le_add hx hy) hg
/-
**IsMinOn.add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMinOn.add (hf : IsMinOn f s a) (hg : IsMinOn g s a) : IsMinOn (fun x => 
f x + g x) s a
参数：hf : IsMinOn f s a；hg : IsMinOn g s a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsMinFilter.add`：IsMinFilter.add (hf : IsMinFilter f l a) (hg : IsMinFil
ter g l a) : IsMinFilter (fun x => f x + g x) l a
-/
theorem IsMinOn.add (hf : IsMinOn f s a) (hg : IsMinOn g s a) : IsMinOn (fun x => f x + g x) s a :=
  IsMinFilter.add hf hg
/-
**IsMaxOn.add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMaxOn.add (hf : IsMaxOn f s a) (hg : IsMaxOn g s a) : IsMaxOn (fun x => 
f x + g x) s a
参数：hf : IsMaxOn f s a；hg : IsMaxOn g s a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsMaxFilter.add`：IsMaxFilter.add (hf : IsMaxFilter f l a) (hg : IsMaxFil
ter g l a) : IsMaxFilter (fun x => f x + g x) l a
-/
theorem IsMaxOn.add (hf : IsMaxOn f s a) (hg : IsMaxOn g s a) : IsMaxOn (fun x => f x + g x) s a :=
  IsMaxFilter.add hf hg

end OrderedAddCommMonoid

/-! ### Pointwise negation and subtraction -/


section OrderedAddCommGroup

variable [AddCommGroup β] [PartialOrder β] [IsOrderedAddMonoid β]
  {f g : α → β} {a : α} {s : Set α} {l : Filter α}

/-
**IsMinFilter.neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMinFilter.neg (hf : IsMinFilter f l a) : IsMaxFilter (fun x => -f x) l a
参数：hf : IsMinFilter f l a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsMinFilter.comp_antitone`：IsMinFilter.comp_antitone (hf : IsMinFilter f
 l a) {g : β -> γ} (hg : Antitone g) : IsMaxFilter (g ∘ f) l a
· 使用定理 `neg_le_neg`：∀ {α : Type u} [inst : AddCommGroup α] [inst_1 : PartialOrde
r α] [IsOrderedAddMonoid α] {a b : α}, a ≤ b → -b ≤ -a
-/
theorem IsMinFilter.neg (hf : IsMinFilter f l a) : IsMaxFilter (fun x => -f x) l a :=
  hf.comp_antitone fun _x _y hx => neg_le_neg hx
/-
**IsMaxFilter.neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMaxFilter.neg (hf : IsMaxFilter f l a) : IsMinFilter (fun x => -f x) l a
参数：hf : IsMaxFilter f l a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsMaxFilter.comp_antitone`：IsMaxFilter.comp_antitone (hf : IsMaxFilter f
 l a) {g : β -> γ} (hg : Antitone g) : IsMinFilter (g ∘ f) l a
· 使用定理 `neg_le_neg`：∀ {α : Type u} [inst : AddCommGroup α] [inst_1 : PartialOrde
r α] [IsOrderedAddMonoid α] {a b : α}, a ≤ b → -b ≤ -a
-/
theorem IsMaxFilter.neg (hf : IsMaxFilter f l a) : IsMinFilter (fun x => -f x) l a :=
  hf.comp_antitone fun _x _y hx => neg_le_neg hx
/-
**IsExtrFilter.neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsExtrFilter.neg (hf : IsExtrFilter f l a) : IsExtrFilter (fun x => -f x) 
l a
参数：hf : IsExtrFilter f l a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `IsMaxFilter.isExtr`：IsMaxFilter.isExtr : IsMaxFilter f l a -> IsExtrFilt
er f l a
· 使用定理 `IsMinFilter.neg`：IsMinFilter.neg (hf : IsMinFilter f l a) : IsMaxFilter 
(fun x => -f x) l a
· 使用定理 `IsMinFilter.isExtr`：IsMinFilter.isExtr : IsMinFilter f l a -> IsExtrFilt
er f l a
· 使用定理 `IsMaxFilter.neg`：IsMaxFilter.neg (hf : IsMaxFilter f l a) : IsMinFilter 
(fun x => -f x) l a
-/
theorem IsExtrFilter.neg (hf : IsExtrFilter f l a) : IsExtrFilter (fun x => -f x) l a :=
  hf.elim (fun hf => hf.neg.isExtr) fun hf => hf.neg.isExtr
/-
**IsMinOn.neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMinOn.neg (hf : IsMinOn f s a) : IsMaxOn (fun x => -f x) s a
参数：hf : IsMinOn f s a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsMinOn.comp_antitone`：IsMinOn.comp_antitone (hf : IsMinOn f s a) {g : β
 -> γ} (hg : Antitone g) : IsMaxOn (g ∘ f) s a
· 使用定理 `neg_le_neg`：∀ {α : Type u} [inst : AddCommGroup α] [inst_1 : PartialOrde
r α] [IsOrderedAddMonoid α] {a b : α}, a ≤ b → -b ≤ -a
-/
theorem IsMinOn.neg (hf : IsMinOn f s a) : IsMaxOn (fun x => -f x) s a :=
  hf.comp_antitone fun _x _y hx => neg_le_neg hx
/-
**IsMaxOn.neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMaxOn.neg (hf : IsMaxOn f s a) : IsMinOn (fun x => -f x) s a
参数：hf : IsMaxOn f s a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsMaxOn.comp_antitone`：IsMaxOn.comp_antitone (hf : IsMaxOn f s a) {g : β
 -> γ} (hg : Antitone g) : IsMinOn (g ∘ f) s a
· 使用定理 `neg_le_neg`：∀ {α : Type u} [inst : AddCommGroup α] [inst_1 : PartialOrde
r α] [IsOrderedAddMonoid α] {a b : α}, a ≤ b → -b ≤ -a
-/
theorem IsMaxOn.neg (hf : IsMaxOn f s a) : IsMinOn (fun x => -f x) s a :=
  hf.comp_antitone fun _x _y hx => neg_le_neg hx
/-
**IsExtrOn.neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsExtrOn.neg (hf : IsExtrOn f s a) : IsExtrOn (fun x => -f x) s a
参数：hf : IsExtrOn f s a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsExtrOn.elim`：IsExtrOn.elim {p : Prop} : IsExtrOn f s a -> (IsMinOn f s
 a -> p) -> (IsMaxOn f s a -> p) -> p
· 使用定理 `IsMaxOn.isExtr`：IsMaxOn.isExtr (h : IsMaxOn f s a) : IsExtrOn f s a
· 使用定理 `IsMinOn.neg`：IsMinOn.neg (hf : IsMinOn f s a) : IsMaxOn (fun x => -f x) 
s a
· 使用定理 `IsMinOn.isExtr`：IsMinOn.isExtr (h : IsMinOn f s a) : IsExtrOn f s a
· 使用定理 `IsMaxOn.neg`：IsMaxOn.neg (hf : IsMaxOn f s a) : IsMinOn (fun x => -f x) 
s a
-/
theorem IsExtrOn.neg (hf : IsExtrOn f s a) : IsExtrOn (fun x => -f x) s a :=
  hf.elim (fun hf => hf.neg.isExtr) fun hf => hf.neg.isExtr
/-
**IsMinFilter.sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMinFilter.sub (hf : IsMinFilter f l a) (hg : IsMaxFilter g l a) : IsMinF
ilter (fun x => f x - g x) l a
参数：hf : IsMinFilter f l a；hg : IsMaxFilter g l a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `IsMinFilter.add`：IsMinFilter.add (hf : IsMinFilter f l a) (hg : IsMinFil
ter g l a) : IsMinFilter (fun x => f x + g x) l a
· 使用定理 `IsMaxFilter.neg`：IsMaxFilter.neg (hf : IsMaxFilter f l a) : IsMinFilter 
(fun x => -f x) l a
-/
theorem IsMinFilter.sub (hf : IsMinFilter f l a) (hg : IsMaxFilter g l a) :
    IsMinFilter (fun x => f x - g x) l a := by simpa only [sub_eq_add_neg] using hf.add hg.neg
/-
**IsMaxFilter.sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMaxFilter.sub (hf : IsMaxFilter f l a) (hg : IsMinFilter g l a) : IsMaxF
ilter (fun x => f x - g x) l a
参数：hf : IsMaxFilter f l a；hg : IsMinFilter g l a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `IsMaxFilter.add`：IsMaxFilter.add (hf : IsMaxFilter f l a) (hg : IsMaxFil
ter g l a) : IsMaxFilter (fun x => f x + g x) l a
· 使用定理 `IsMinFilter.neg`：IsMinFilter.neg (hf : IsMinFilter f l a) : IsMaxFilter 
(fun x => -f x) l a
-/
theorem IsMaxFilter.sub (hf : IsMaxFilter f l a) (hg : IsMinFilter g l a) :
    IsMaxFilter (fun x => f x - g x) l a := by simpa only [sub_eq_add_neg] using hf.add hg.neg
/-
**IsMinOn.sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMinOn.sub (hf : IsMinOn f s a) (hg : IsMaxOn g s a) : IsMinOn (fun x => 
f x - g x) s a
参数：hf : IsMinOn f s a；hg : IsMaxOn g s a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `IsMinOn.add`：IsMinOn.add (hf : IsMinOn f s a) (hg : IsMinOn g s a) : IsM
inOn (fun x => f x + g x) s a
· 使用定理 `IsMaxOn.neg`：IsMaxOn.neg (hf : IsMaxOn f s a) : IsMinOn (fun x => -f x) 
s a
-/
theorem IsMinOn.sub (hf : IsMinOn f s a) (hg : IsMaxOn g s a) :
    IsMinOn (fun x => f x - g x) s a := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg
/-
**IsMaxOn.sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMaxOn.sub (hf : IsMaxOn f s a) (hg : IsMinOn g s a) : IsMaxOn (fun x => 
f x - g x) s a
参数：hf : IsMaxOn f s a；hg : IsMinOn g s a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `IsMaxOn.add`：IsMaxOn.add (hf : IsMaxOn f s a) (hg : IsMaxOn g s a) : IsM
axOn (fun x => f x + g x) s a
· 使用定理 `IsMinOn.neg`：IsMinOn.neg (hf : IsMinOn f s a) : IsMaxOn (fun x => -f x) 
s a
-/
theorem IsMaxOn.sub (hf : IsMaxOn f s a) (hg : IsMinOn g s a) :
    IsMaxOn (fun x => f x - g x) s a := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

end OrderedAddCommGroup

/-! ### Pointwise `sup`/`inf` -/


section SemilatticeSup

variable [SemilatticeSup β] {f g : α → β} {a : α} {s : Set α} {l : Filter α}

/-
**IsMinFilter.sup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMinFilter.sup (hf : IsMinFilter f l a) (hg : IsMinFilter g l a) : IsMinF
ilter (fun x => f x ⊔ g x) l a
参数：hf : IsMinFilter f l a；hg : IsMinFilter g l a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsMinFilter.bicomp_mono`：IsMinFilter.bicomp_mono [Preorder δ] {op : β ->
 γ -> δ} (hop : ((· <= ·) ⇒ (· <= ·) ⇒ (· <= ·)) op op) (hf : IsMinFilter f l a)
 {g : α -> γ}…
· 使用定理 `sup_le_sup`：sup_le_sup (h₁ : a <= b) (h₂ : c <= d) : a ⊔ c <= b ⊔ d
-/
theorem IsMinFilter.sup (hf : IsMinFilter f l a) (hg : IsMinFilter g l a) :
    IsMinFilter (fun x => f x ⊔ g x) l a :=
  show IsMinFilter (fun x => f x ⊔ g x) l a from
    hf.bicomp_mono (fun _x _x' hx _y _y' hy => sup_le_sup hx hy) hg
/-
**IsMaxFilter.sup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMaxFilter.sup (hf : IsMaxFilter f l a) (hg : IsMaxFilter g l a) : IsMaxF
ilter (fun x => f x ⊔ g x) l a
参数：hf : IsMaxFilter f l a；hg : IsMaxFilter g l a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsMaxFilter.bicomp_mono`：IsMaxFilter.bicomp_mono [Preorder δ] {op : β ->
 γ -> δ} (hop : ((· <= ·) ⇒ (· <= ·) ⇒ (· <= ·)) op op) (hf : IsMaxFilter f l a)
 {g : α -> γ}…
· 使用定理 `sup_le_sup`：sup_le_sup (h₁ : a <= b) (h₂ : c <= d) : a ⊔ c <= b ⊔ d
-/
theorem IsMaxFilter.sup (hf : IsMaxFilter f l a) (hg : IsMaxFilter g l a) :
    IsMaxFilter (fun x => f x ⊔ g x) l a :=
  show IsMaxFilter (fun x => f x ⊔ g x) l a from
    hf.bicomp_mono (fun _x _x' hx _y _y' hy => sup_le_sup hx hy) hg
/-
**IsMinOn.sup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMinOn.sup (hf : IsMinOn f s a) (hg : IsMinOn g s a) : IsMinOn (fun x => 
f x ⊔ g x) s a
参数：hf : IsMinOn f s a；hg : IsMinOn g s a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsMinFilter.sup`：IsMinFilter.sup (hf : IsMinFilter f l a) (hg : IsMinFil
ter g l a) : IsMinFilter (fun x => f x ⊔ g x) l a
-/
theorem IsMinOn.sup (hf : IsMinOn f s a) (hg : IsMinOn g s a) : IsMinOn (fun x => f x ⊔ g x) s a :=
  IsMinFilter.sup hf hg
/-
**IsMaxOn.sup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMaxOn.sup (hf : IsMaxOn f s a) (hg : IsMaxOn g s a) : IsMaxOn (fun x => 
f x ⊔ g x) s a
参数：hf : IsMaxOn f s a；hg : IsMaxOn g s a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsMaxFilter.sup`：IsMaxFilter.sup (hf : IsMaxFilter f l a) (hg : IsMaxFil
ter g l a) : IsMaxFilter (fun x => f x ⊔ g x) l a
-/
theorem IsMaxOn.sup (hf : IsMaxOn f s a) (hg : IsMaxOn g s a) : IsMaxOn (fun x => f x ⊔ g x) s a :=
  IsMaxFilter.sup hf hg

end SemilatticeSup

section SemilatticeInf

variable [SemilatticeInf β] {f g : α → β} {a : α} {s : Set α} {l : Filter α}

/-
**IsMinFilter.inf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMinFilter.inf (hf : IsMinFilter f l a) (hg : IsMinFilter g l a) : IsMinF
ilter (fun x => f x ⊓ g x) l a
参数：hf : IsMinFilter f l a；hg : IsMinFilter g l a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsMinFilter.bicomp_mono`：IsMinFilter.bicomp_mono [Preorder δ] {op : β ->
 γ -> δ} (hop : ((· <= ·) ⇒ (· <= ·) ⇒ (· <= ·)) op op) (hf : IsMinFilter f l a)
 {g : α -> γ}…
· 使用定理 `inf_le_inf`：∀ {α : Type u} [inst : SemilatticeInf α] {a b c d : α}, b ≤ 
a → d ≤ c → b ⊓ d ≤ a ⊓ c
-/
theorem IsMinFilter.inf (hf : IsMinFilter f l a) (hg : IsMinFilter g l a) :
    IsMinFilter (fun x => f x ⊓ g x) l a :=
  show IsMinFilter (fun x => f x ⊓ g x) l a from
    hf.bicomp_mono (fun _x _x' hx _y _y' hy => inf_le_inf hx hy) hg
/-
**IsMaxFilter.inf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMaxFilter.inf (hf : IsMaxFilter f l a) (hg : IsMaxFilter g l a) : IsMaxF
ilter (fun x => f x ⊓ g x) l a
参数：hf : IsMaxFilter f l a；hg : IsMaxFilter g l a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsMaxFilter.bicomp_mono`：IsMaxFilter.bicomp_mono [Preorder δ] {op : β ->
 γ -> δ} (hop : ((· <= ·) ⇒ (· <= ·) ⇒ (· <= ·)) op op) (hf : IsMaxFilter f l a)
 {g : α -> γ}…
· 使用定理 `inf_le_inf`：∀ {α : Type u} [inst : SemilatticeInf α] {a b c d : α}, b ≤ 
a → d ≤ c → b ⊓ d ≤ a ⊓ c
-/
theorem IsMaxFilter.inf (hf : IsMaxFilter f l a) (hg : IsMaxFilter g l a) :
    IsMaxFilter (fun x => f x ⊓ g x) l a :=
  show IsMaxFilter (fun x => f x ⊓ g x) l a from
    hf.bicomp_mono (fun _x _x' hx _y _y' hy => inf_le_inf hx hy) hg
/-
**IsMinOn.inf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMinOn.inf (hf : IsMinOn f s a) (hg : IsMinOn g s a) : IsMinOn (fun x => 
f x ⊓ g x) s a
参数：hf : IsMinOn f s a；hg : IsMinOn g s a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsMinFilter.inf`：IsMinFilter.inf (hf : IsMinFilter f l a) (hg : IsMinFil
ter g l a) : IsMinFilter (fun x => f x ⊓ g x) l a
-/
theorem IsMinOn.inf (hf : IsMinOn f s a) (hg : IsMinOn g s a) : IsMinOn (fun x => f x ⊓ g x) s a :=
  IsMinFilter.inf hf hg
/-
**IsMaxOn.inf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMaxOn.inf (hf : IsMaxOn f s a) (hg : IsMaxOn g s a) : IsMaxOn (fun x => 
f x ⊓ g x) s a
参数：hf : IsMaxOn f s a；hg : IsMaxOn g s a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsMaxFilter.inf`：IsMaxFilter.inf (hf : IsMaxFilter f l a) (hg : IsMaxFil
ter g l a) : IsMaxFilter (fun x => f x ⊓ g x) l a
-/
theorem IsMaxOn.inf (hf : IsMaxOn f s a) (hg : IsMaxOn g s a) : IsMaxOn (fun x => f x ⊓ g x) s a :=
  IsMaxFilter.inf hf hg

end SemilatticeInf

/-! ### Pointwise `min`/`max` -/


section LinearOrder

variable [LinearOrder β] {f g : α → β} {a : α} {s : Set α} {l : Filter α}

/-
**IsMinFilter.min** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMinFilter.min (hf : IsMinFilter f l a) (hg : IsMinFilter g l a) : IsMinF
ilter (fun x => min (f x) (g x)) l a
参数：hf : IsMinFilter f l a；hg : IsMinFilter g l a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsMinFilter.bicomp_mono`：IsMinFilter.bicomp_mono [Preorder δ] {op : β ->
 γ -> δ} (hop : ((· <= ·) ⇒ (· <= ·) ⇒ (· <= ·)) op op) (hf : IsMinFilter f l a)
 {g : α -> γ}…
· 使用定理 `min_le_min`：∀ {α : Type u} [inst : LinearOrder α] {a b c d : α}, c ≤ a →
 d ≤ b → min c d ≤ min a b
-/
theorem IsMinFilter.min (hf : IsMinFilter f l a) (hg : IsMinFilter g l a) :
    IsMinFilter (fun x => min (f x) (g x)) l a :=
  show IsMinFilter (fun x => Min.min (f x) (g x)) l a from
    hf.bicomp_mono (fun _x _x' hx _y _y' hy => min_le_min hx hy) hg
/-
**IsMaxFilter.min** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMaxFilter.min (hf : IsMaxFilter f l a) (hg : IsMaxFilter g l a) : IsMaxF
ilter (fun x => min (f x) (g x)) l a
参数：hf : IsMaxFilter f l a；hg : IsMaxFilter g l a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsMaxFilter.bicomp_mono`：IsMaxFilter.bicomp_mono [Preorder δ] {op : β ->
 γ -> δ} (hop : ((· <= ·) ⇒ (· <= ·) ⇒ (· <= ·)) op op) (hf : IsMaxFilter f l a)
 {g : α -> γ}…
· 使用定理 `min_le_min`：∀ {α : Type u} [inst : LinearOrder α] {a b c d : α}, c ≤ a →
 d ≤ b → min c d ≤ min a b
-/
theorem IsMaxFilter.min (hf : IsMaxFilter f l a) (hg : IsMaxFilter g l a) :
    IsMaxFilter (fun x => min (f x) (g x)) l a :=
  show IsMaxFilter (fun x => Min.min (f x) (g x)) l a from
    hf.bicomp_mono (fun _x _x' hx _y _y' hy => min_le_min hx hy) hg
/-
**IsMinOn.min** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMinOn.min (hf : IsMinOn f s a) (hg : IsMinOn g s a) : IsMinOn (fun x => 
min (f x) (g x)) s a
参数：hf : IsMinOn f s a；hg : IsMinOn g s a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsMinFilter.min`：IsMinFilter.min (hf : IsMinFilter f l a) (hg : IsMinFil
ter g l a) : IsMinFilter (fun x => min (f x) (g x)) l a
-/
theorem IsMinOn.min (hf : IsMinOn f s a) (hg : IsMinOn g s a) :
    IsMinOn (fun x => min (f x) (g x)) s a :=
  IsMinFilter.min hf hg
/-
**IsMaxOn.min** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMaxOn.min (hf : IsMaxOn f s a) (hg : IsMaxOn g s a) : IsMaxOn (fun x => 
min (f x) (g x)) s a
参数：hf : IsMaxOn f s a；hg : IsMaxOn g s a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsMaxFilter.min`：IsMaxFilter.min (hf : IsMaxFilter f l a) (hg : IsMaxFil
ter g l a) : IsMaxFilter (fun x => min (f x) (g x)) l a
-/
theorem IsMaxOn.min (hf : IsMaxOn f s a) (hg : IsMaxOn g s a) :
    IsMaxOn (fun x => min (f x) (g x)) s a :=
  IsMaxFilter.min hf hg
/-
**IsMinFilter.max** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMinFilter.max (hf : IsMinFilter f l a) (hg : IsMinFilter g l a) : IsMinF
ilter (fun x => max (f x) (g x)) l a
参数：hf : IsMinFilter f l a；hg : IsMinFilter g l a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsMinFilter.bicomp_mono`：IsMinFilter.bicomp_mono [Preorder δ] {op : β ->
 γ -> δ} (hop : ((· <= ·) ⇒ (· <= ·) ⇒ (· <= ·)) op op) (hf : IsMinFilter f l a)
 {g : α -> γ}…
· 使用定理 `max_le_max`：max_le_max : a <= c -> b <= d -> max a b <= max c d
-/
theorem IsMinFilter.max (hf : IsMinFilter f l a) (hg : IsMinFilter g l a) :
    IsMinFilter (fun x => max (f x) (g x)) l a :=
  show IsMinFilter (fun x => Max.max (f x) (g x)) l a from
    hf.bicomp_mono (fun _x _x' hx _y _y' hy => max_le_max hx hy) hg
/-
**IsMaxFilter.max** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMaxFilter.max (hf : IsMaxFilter f l a) (hg : IsMaxFilter g l a) : IsMaxF
ilter (fun x => max (f x) (g x)) l a
参数：hf : IsMaxFilter f l a；hg : IsMaxFilter g l a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsMaxFilter.bicomp_mono`：IsMaxFilter.bicomp_mono [Preorder δ] {op : β ->
 γ -> δ} (hop : ((· <= ·) ⇒ (· <= ·) ⇒ (· <= ·)) op op) (hf : IsMaxFilter f l a)
 {g : α -> γ}…
· 使用定理 `max_le_max`：max_le_max : a <= c -> b <= d -> max a b <= max c d
-/
theorem IsMaxFilter.max (hf : IsMaxFilter f l a) (hg : IsMaxFilter g l a) :
    IsMaxFilter (fun x => max (f x) (g x)) l a :=
  show IsMaxFilter (fun x => Max.max (f x) (g x)) l a from
    hf.bicomp_mono (fun _x _x' hx _y _y' hy => max_le_max hx hy) hg
/-
**IsMinOn.max** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMinOn.max (hf : IsMinOn f s a) (hg : IsMinOn g s a) : IsMinOn (fun x => 
max (f x) (g x)) s a
参数：hf : IsMinOn f s a；hg : IsMinOn g s a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsMinFilter.max`：IsMinFilter.max (hf : IsMinFilter f l a) (hg : IsMinFil
ter g l a) : IsMinFilter (fun x => max (f x) (g x)) l a
-/
theorem IsMinOn.max (hf : IsMinOn f s a) (hg : IsMinOn g s a) :
    IsMinOn (fun x => max (f x) (g x)) s a :=
  IsMinFilter.max hf hg
/-
**IsMaxOn.max** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMaxOn.max (hf : IsMaxOn f s a) (hg : IsMaxOn g s a) : IsMaxOn (fun x => 
max (f x) (g x)) s a
参数：hf : IsMaxOn f s a；hg : IsMaxOn g s a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsMaxFilter.max`：IsMaxFilter.max (hf : IsMaxFilter f l a) (hg : IsMaxFil
ter g l a) : IsMaxFilter (fun x => max (f x) (g x)) l a
-/
theorem IsMaxOn.max (hf : IsMaxOn f s a) (hg : IsMaxOn g s a) :
    IsMaxOn (fun x => max (f x) (g x)) s a :=
  IsMaxFilter.max hf hg

/-! ### Extrema from monotonicity and antitonicity -/

variable {β : Type*} [LinearOrder α] [Preorder β] {a b c : α} {f : α → β}

/-- If `f` is monotone on `Ioc a b` and antitone on `Ico b c`, then the maximum of `f` on
`Ioo a c` is attained at `b`. -/
/-
**isMaxOn_Ioo_of_mono_anti** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isMaxOn_Ioo_of_mono_anti (h₀ : MonotoneOn f (Ioc a b)) (h₁ : AntitoneOn f 
(Ico b c)) : IsMaxOn f (Ioo a c) b
参数：h₀ : MonotoneOn f (Ioc a b)；h₁ : AntitoneOn f (Ico b c)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.right_mem_Ioc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ∈ S
et.Ioc b a ↔ b < a
· 使用定理 `LE.le.trans_lt'`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, b ≤ a
 → c < b → c < a
· 使用定理 `Set.left_mem_Ico`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ∈ Se
t.Ico a b ↔ a < b
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b

--- 原说明 ---
If `f` is monotone on `Ioc a b` and antitone on `Ico b c`, then the maximum of `
f` on
`Ioo a c` is attained at `b`.
-/
lemma isMaxOn_Ioo_of_mono_anti (h₀ : MonotoneOn f (Ioc a b)) (h₁ : AntitoneOn f (Ico b c)) :
    IsMaxOn f (Ioo a c) b := by
  intro x hx
  by_cases! g₀ : x ≤ b
  · exact h₀ ⟨hx.1, g₀⟩ (right_mem_Ioc.2 (g₀.trans_lt' hx.1)) g₀
  · refine h₁ (left_mem_Ico.2 (g₀.trans hx.2)) ⟨g₀.le, hx.2⟩ g₀.le

/-- If `f` is antitone on `Ioc a b` and monotone on `Ico b c`, then the minimum of `f` on
`Ioo a c` is attained at `b`. -/
/-
**isMinOn_Ioo_of_anti_mono** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isMinOn_Ioo_of_anti_mono (h₀ : AntitoneOn f (Ioc a b)) (h₁ : MonotoneOn f 
(Ico b c)) : IsMinOn f (Ioo a c) b
参数：h₀ : AntitoneOn f (Ioc a b)；h₁ : MonotoneOn f (Ico b c)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `isMaxOn_Ioo_of_mono_anti`：isMaxOn_Ioo_of_mono_anti (h₀ : MonotoneOn f (I
oc a b)) (h₁ : AntitoneOn f (Ico b c)) : IsMaxOn f (Ioo a c) b

--- 原说明 ---
If `f` is antitone on `Ioc a b` and monotone on `Ico b c`, then the minimum of `
f` on
`Ioo a c` is attained at `b`.
-/
lemma isMinOn_Ioo_of_anti_mono (h₀ : AntitoneOn f (Ioc a b)) (h₁ : MonotoneOn f (Ico b c)) :
    IsMinOn f (Ioo a c) b :=
  isMaxOn_Ioo_of_mono_anti (β := βᵒᵈ) h₀ h₁

/-- If `f` is monotone on `Icc a b` and antitone on `Ico b c`, then the maximum of `f` on
`Ico a c` is attained at `b`. -/
/-
**isMaxOn_Ico_of_mono_anti** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isMaxOn_Ico_of_mono_anti (h₀ : MonotoneOn f (Icc a b)) (h₁ : AntitoneOn f 
(Ico b c)) : IsMaxOn f (Ico a c) b
参数：h₀ : MonotoneOn f (Icc a b)；h₁ : AntitoneOn f (Ico b c)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.right_mem_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ∈ S
et.Icc b a ↔ b ≤ a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.left_mem_Ico`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ∈ Se
t.Ico a b ↔ a < b
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b

--- 原说明 ---
If `f` is monotone on `Icc a b` and antitone on `Ico b c`, then the maximum of `
f` on
`Ico a c` is attained at `b`.
-/
lemma isMaxOn_Ico_of_mono_anti (h₀ : MonotoneOn f (Icc a b)) (h₁ : AntitoneOn f (Ico b c)) :
    IsMaxOn f (Ico a c) b := by
  intro x hx
  by_cases! g₀ : x ≤ b
  · exact h₀ ⟨hx.1, g₀⟩ (right_mem_Icc.2 (hx.1.trans g₀)) g₀
  · exact h₁ (left_mem_Ico.2 (g₀.trans hx.2)) ⟨g₀.le, hx.2⟩ g₀.le

/-- If `f` is antitone on `Icc a b` and monotone on `Ico b c`, then the minimum of `f` on
`Ico a c` is attained at `b`. -/
/-
**isMinOn_Ico_of_anti_mono** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isMinOn_Ico_of_anti_mono (h₀ : AntitoneOn f (Icc a b)) (h₁ : MonotoneOn f 
(Ico b c)) : IsMinOn f (Ico a c) b
参数：h₀ : AntitoneOn f (Icc a b)；h₁ : MonotoneOn f (Ico b c)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `isMaxOn_Ico_of_mono_anti`：isMaxOn_Ico_of_mono_anti (h₀ : MonotoneOn f (I
cc a b)) (h₁ : AntitoneOn f (Ico b c)) : IsMaxOn f (Ico a c) b

--- 原说明 ---
If `f` is antitone on `Icc a b` and monotone on `Ico b c`, then the minimum of `
f` on
`Ico a c` is attained at `b`.
-/
lemma isMinOn_Ico_of_anti_mono (h₀ : AntitoneOn f (Icc a b)) (h₁ : MonotoneOn f (Ico b c)) :
    IsMinOn f (Ico a c) b :=
  isMaxOn_Ico_of_mono_anti (β := βᵒᵈ) h₀ h₁

/-- If `f` is monotone on `Ioc a b` and antitone on `Icc b c`, then the maximum of `f` on
`Ioc a c` is attained at `b`. -/
/-
**isMaxOn_Ioc_of_mono_anti** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isMaxOn_Ioc_of_mono_anti (h₀ : MonotoneOn f (Ioc a b)) (h₁ : AntitoneOn f 
(Icc b c)) : IsMaxOn f (Ioc a c) b
参数：h₀ : MonotoneOn f (Ioc a b)；h₁ : AntitoneOn f (Icc b c)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.right_mem_Ioc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ∈ S
et.Ioc b a ↔ b < a
· 使用定理 `LE.le.trans_lt'`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, b ≤ a
 → c < b → c < a
· 使用定理 `Set.left_mem_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ∈ Se
t.Icc a b ↔ a ≤ b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
If `f` is monotone on `Ioc a b` and antitone on `Icc b c`, then the maximum of `
f` on
`Ioc a c` is attained at `b`.
-/
lemma isMaxOn_Ioc_of_mono_anti (h₀ : MonotoneOn f (Ioc a b)) (h₁ : AntitoneOn f (Icc b c)) :
    IsMaxOn f (Ioc a c) b := by
  intro x hx
  by_cases! g₀ : x ≤ b
  · exact h₀ ⟨hx.1, g₀⟩ (right_mem_Ioc.2 (g₀.trans_lt' hx.1)) g₀
  · exact h₁ (left_mem_Icc.2 (g₀.le.trans hx.2)) ⟨g₀.le, hx.2⟩ g₀.le

/-- If `f` is antitone on `Ioc a b` and monotone on `Icc b c`, then the minimum of `f` on
`Ioc a c` is attained at `b`. -/
/-
**isMinOn_Ioc_of_anti_mono** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isMinOn_Ioc_of_anti_mono (h₀ : AntitoneOn f (Ioc a b)) (h₁ : MonotoneOn f 
(Icc b c)) : IsMinOn f (Ioc a c) b
参数：h₀ : AntitoneOn f (Ioc a b)；h₁ : MonotoneOn f (Icc b c)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `isMaxOn_Ioc_of_mono_anti`：isMaxOn_Ioc_of_mono_anti (h₀ : MonotoneOn f (I
oc a b)) (h₁ : AntitoneOn f (Icc b c)) : IsMaxOn f (Ioc a c) b

--- 原说明 ---
If `f` is antitone on `Ioc a b` and monotone on `Icc b c`, then the minimum of `
f` on
`Ioc a c` is attained at `b`.
-/
lemma isMinOn_Ioc_of_anti_mono (h₀ : AntitoneOn f (Ioc a b)) (h₁ : MonotoneOn f (Icc b c)) :
    IsMinOn f (Ioc a c) b :=
  isMaxOn_Ioc_of_mono_anti (β := βᵒᵈ) h₀ h₁

/-- If `f` is monotone on `Icc a b` and antitone on `Icc b c`, then the maximum of `f` on
`Icc a c` is attained at `b`. -/
/-
**isMaxOn_Icc_of_mono_anti** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isMaxOn_Icc_of_mono_anti (h₀ : MonotoneOn f (Icc a b)) (h₁ : AntitoneOn f 
(Icc b c)) : IsMaxOn f (Icc a c) b
参数：h₀ : MonotoneOn f (Icc a b)；h₁ : AntitoneOn f (Icc b c)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.right_mem_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ∈ S
et.Icc b a ↔ b ≤ a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.left_mem_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ∈ Se
t.Icc a b ↔ a ≤ b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
If `f` is monotone on `Icc a b` and antitone on `Icc b c`, then the maximum of `
f` on
`Icc a c` is attained at `b`.
-/
lemma isMaxOn_Icc_of_mono_anti (h₀ : MonotoneOn f (Icc a b)) (h₁ : AntitoneOn f (Icc b c)) :
    IsMaxOn f (Icc a c) b := by
  intro x hx
  by_cases! g₀ : x ≤ b
  · exact h₀ ⟨hx.1, g₀⟩ (right_mem_Icc.2 (hx.1.trans g₀)) g₀
  · exact h₁ (left_mem_Icc.2 (g₀.le.trans hx.2)) ⟨g₀.le, hx.2⟩ g₀.le

/-- If `f` is antitone on `Icc a b` and monotone on `Icc b c`, then the minimum of `f` on
`Icc a c` is attained at `b`. -/
/-
**isMinOn_Icc_of_anti_mono** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isMinOn_Icc_of_anti_mono (h₀ : AntitoneOn f (Icc a b)) (h₁ : MonotoneOn f 
(Icc b c)) : IsMinOn f (Icc a c) b
参数：h₀ : AntitoneOn f (Icc a b)；h₁ : MonotoneOn f (Icc b c)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `isMaxOn_Icc_of_mono_anti`：isMaxOn_Icc_of_mono_anti (h₀ : MonotoneOn f (I
cc a b)) (h₁ : AntitoneOn f (Icc b c)) : IsMaxOn f (Icc a c) b

--- 原说明 ---
If `f` is antitone on `Icc a b` and monotone on `Icc b c`, then the minimum of `
f` on
`Icc a c` is attained at `b`.
-/
lemma isMinOn_Icc_of_anti_mono (h₀ : AntitoneOn f (Icc a b)) (h₁ : MonotoneOn f (Icc b c)) :
    IsMinOn f (Icc a c) b :=
  isMaxOn_Icc_of_mono_anti (β := βᵒᵈ) h₀ h₁

/-- If `f` is monotone on `Ioc a b` and antitone on `Ici b`, then the maximum of `f` on `Ioi a` is
attained at `b`. -/
/-
**isMaxOn_Ioi_of_mono_anti** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isMaxOn_Ioi_of_mono_anti (h₀ : MonotoneOn f (Ioc a b)) (h₁ : AntitoneOn f 
(Ici b)) : IsMaxOn f (Ioi a) b
参数：h₀ : MonotoneOn f (Ioc a b)；h₁ : AntitoneOn f (Ici b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.right_mem_Ioc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ∈ S
et.Ioc b a ↔ b < a
· 使用定理 `LE.le.trans_lt'`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, b ≤ a
 → c < b → c < a
· 使用定理 `Set.self_mem_Ici`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, a ∈ Set.
Ici a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b

--- 原说明 ---
If `f` is monotone on `Ioc a b` and antitone on `Ici b`, then the maximum of `f`
 on `Ioi a` is
attained at `b`.
-/
lemma isMaxOn_Ioi_of_mono_anti (h₀ : MonotoneOn f (Ioc a b)) (h₁ : AntitoneOn f (Ici b)) :
    IsMaxOn f (Ioi a) b := by
  intro x hx
  by_cases! g₀ : x ≤ b
  · exact h₀ ⟨hx, g₀⟩ (right_mem_Ioc.2 (g₀.trans_lt' hx)) g₀
  · exact h₁ self_mem_Ici g₀.le g₀.le

/-- If `f` is antitone on `Ioc a b` and monotone on `Ici b`, then the minimum of `f` on `Ioi a` is
attained at `b`. -/
/-
**isMinOn_Ioi_of_anti_mono** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isMinOn_Ioi_of_anti_mono (h₀ : AntitoneOn f (Ioc a b)) (h₁ : MonotoneOn f 
(Ici b)) : IsMinOn f (Ioi a) b
参数：h₀ : AntitoneOn f (Ioc a b)；h₁ : MonotoneOn f (Ici b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `isMaxOn_Ioi_of_mono_anti`：isMaxOn_Ioi_of_mono_anti (h₀ : MonotoneOn f (I
oc a b)) (h₁ : AntitoneOn f (Ici b)) : IsMaxOn f (Ioi a) b

--- 原说明 ---
If `f` is antitone on `Ioc a b` and monotone on `Ici b`, then the minimum of `f`
 on `Ioi a` is
attained at `b`.
-/
lemma isMinOn_Ioi_of_anti_mono (h₀ : AntitoneOn f (Ioc a b)) (h₁ : MonotoneOn f (Ici b)) :
    IsMinOn f (Ioi a) b :=
  isMaxOn_Ioi_of_mono_anti (β := βᵒᵈ) h₀ h₁

/-- If `f` is monotone on `Icc a b` and antitone on `Ici b`, then the maximum of `f` on `Ici a` is
attained at `b`. -/
/-
**isMaxOn_Ici_of_mono_anti** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isMaxOn_Ici_of_mono_anti (h₀ : MonotoneOn f (Icc a b)) (h₁ : AntitoneOn f 
(Ici b)) : IsMaxOn f (Ici a) b
参数：h₀ : MonotoneOn f (Icc a b)；h₁ : AntitoneOn f (Ici b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.right_mem_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ∈ S
et.Icc b a ↔ b ≤ a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.self_mem_Ici`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, a ∈ Set.
Ici a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b

--- 原说明 ---
If `f` is monotone on `Icc a b` and antitone on `Ici b`, then the maximum of `f`
 on `Ici a` is
attained at `b`.
-/
lemma isMaxOn_Ici_of_mono_anti (h₀ : MonotoneOn f (Icc a b)) (h₁ : AntitoneOn f (Ici b)) :
    IsMaxOn f (Ici a) b := by
  intro x hx
  by_cases! g₀ : x ≤ b
  · exact h₀ ⟨hx, g₀⟩ (right_mem_Icc.2 (hx.trans g₀)) g₀
  · exact h₁ self_mem_Ici g₀.le g₀.le

/-- If `f` is antitone on `Icc a b` and monotone on `Ici b`, then the minimum of `f` on `Ici a` is
attained at `b`. -/
/-
**isMinOn_Ici_of_anti_mono** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isMinOn_Ici_of_anti_mono (h₀ : AntitoneOn f (Icc a b)) (h₁ : MonotoneOn f 
(Ici b)) : IsMinOn f (Ici a) b
参数：h₀ : AntitoneOn f (Icc a b)；h₁ : MonotoneOn f (Ici b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `isMaxOn_Ici_of_mono_anti`：isMaxOn_Ici_of_mono_anti (h₀ : MonotoneOn f (I
cc a b)) (h₁ : AntitoneOn f (Ici b)) : IsMaxOn f (Ici a) b

--- 原说明 ---
If `f` is antitone on `Icc a b` and monotone on `Ici b`, then the minimum of `f`
 on `Ici a` is
attained at `b`.
-/
lemma isMinOn_Ici_of_anti_mono (h₀ : AntitoneOn f (Icc a b)) (h₁ : MonotoneOn f (Ici b)) :
    IsMinOn f (Ici a) b :=
  isMaxOn_Ici_of_mono_anti (β := βᵒᵈ) h₀ h₁

/-- If `f` is monotone on `Iic b` and antitone on `Ico b a`, then the maximum of `f` on `Iio a`
is attained at `b`. -/
/-
**isMaxOn_Iio_of_mono_anti** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isMaxOn_Iio_of_mono_anti (h₀ : MonotoneOn f (Iic b)) (h₁ : AntitoneOn f (I
co b a)) : IsMaxOn f (Iio a) b
参数：h₀ : MonotoneOn f (Iic b)；h₁ : AntitoneOn f (Ico b a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.self_mem_Iic`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, a ∈ Set.
Iic a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.left_mem_Ico`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ∈ Se
t.Ico a b ↔ a < b
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b

--- 原说明 ---
If `f` is monotone on `Iic b` and antitone on `Ico b a`, then the maximum of `f`
 on `Iio a`
is attained at `b`.
-/
lemma isMaxOn_Iio_of_mono_anti (h₀ : MonotoneOn f (Iic b)) (h₁ : AntitoneOn f (Ico b a)) :
    IsMaxOn f (Iio a) b := by
  intro x hx
  by_cases! g₀ : x ≤ b
  · exact h₀ g₀ self_mem_Iic g₀
  · exact h₁ (left_mem_Ico.2 (g₀.trans hx)) ⟨g₀.le, hx⟩ g₀.le

/-- If `f` is antitone on `Iic b` and monotone on `Ico b a`, then the minimum of `f` on `Iio a`
is attained at `b`. -/
/-
**isMinOn_Iio_of_anti_mono** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isMinOn_Iio_of_anti_mono (h₀ : AntitoneOn f (Iic b)) (h₁ : MonotoneOn f (I
co b a)) : IsMinOn f (Iio a) b
参数：h₀ : AntitoneOn f (Iic b)；h₁ : MonotoneOn f (Ico b a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `isMaxOn_Iio_of_mono_anti`：isMaxOn_Iio_of_mono_anti (h₀ : MonotoneOn f (I
ic b)) (h₁ : AntitoneOn f (Ico b a)) : IsMaxOn f (Iio a) b

--- 原说明 ---
If `f` is antitone on `Iic b` and monotone on `Ico b a`, then the minimum of `f`
 on `Iio a`
is attained at `b`.
-/
lemma isMinOn_Iio_of_anti_mono (h₀ : AntitoneOn f (Iic b)) (h₁ : MonotoneOn f (Ico b a)) :
    IsMinOn f (Iio a) b :=
  isMaxOn_Iio_of_mono_anti (β := βᵒᵈ) h₀ h₁

/-- If `f` is monotone on `Iic b` and antitone on `Icc b a`, then the maximum of `f` on `Iic a`
is attained at `b`. -/
/-
**isMaxOn_Iic_of_mono_anti** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isMaxOn_Iic_of_mono_anti (h₀ : MonotoneOn f (Iic b)) (h₁ : AntitoneOn f (I
cc b a)) : IsMaxOn f (Iic a) b
参数：h₀ : MonotoneOn f (Iic b)；h₁ : AntitoneOn f (Icc b a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.self_mem_Iic`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, a ∈ Set.
Iic a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.left_mem_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ∈ Se
t.Icc a b ↔ a ≤ b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b

--- 原说明 ---
If `f` is monotone on `Iic b` and antitone on `Icc b a`, then the maximum of `f`
 on `Iic a`
is attained at `b`.
-/
lemma isMaxOn_Iic_of_mono_anti (h₀ : MonotoneOn f (Iic b)) (h₁ : AntitoneOn f (Icc b a)) :
    IsMaxOn f (Iic a) b := by
  intro x hx
  by_cases! g₀ : x ≤ b
  · exact h₀ g₀ self_mem_Iic g₀
  · exact h₁ (left_mem_Icc.2 (g₀.le.trans hx)) ⟨g₀.le, hx⟩ g₀.le

/-- If `f` is antitone on `Iic b` and monotone on `Icc b a`, then the minimum of `f` on `Iic a`
is attained at `b`. -/
/-
**isMinOn_Iic_of_anti_mono** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isMinOn_Iic_of_anti_mono (h₀ : AntitoneOn f (Iic b)) (h₁ : MonotoneOn f (I
cc b a)) : IsMinOn f (Iic a) b
参数：h₀ : AntitoneOn f (Iic b)；h₁ : MonotoneOn f (Icc b a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `isMaxOn_Iic_of_mono_anti`：isMaxOn_Iic_of_mono_anti (h₀ : MonotoneOn f (I
ic b)) (h₁ : AntitoneOn f (Icc b a)) : IsMaxOn f (Iic a) b

--- 原说明 ---
If `f` is antitone on `Iic b` and monotone on `Icc b a`, then the minimum of `f`
 on `Iic a`
is attained at `b`.
-/
lemma isMinOn_Iic_of_anti_mono (h₀ : AntitoneOn f (Iic b)) (h₁ : MonotoneOn f (Icc b a)) :
    IsMinOn f (Iic a) b :=
  isMaxOn_Iic_of_mono_anti (β := βᵒᵈ) h₀ h₁

/-- If `f` is monotone on `Iic b` and antitone on `Ici b`, then the maximum of `f` is attained
at `b`. -/
/-
**isMaxOn_univ_of_mono_anti** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isMaxOn_univ_of_mono_anti (h₀ : MonotoneOn f (Iic b)) (h₁ : AntitoneOn f (
Ici b)) : IsMaxOn f univ b
参数：h₀ : MonotoneOn f (Iic b)；h₁ : AntitoneOn f (Ici b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True

--- 原说明 ---
If `f` is monotone on `Iic b` and antitone on `Ici b`, then the maximum of `f` i
s attained
at `b`.
-/
lemma isMaxOn_univ_of_mono_anti (h₀ : MonotoneOn f (Iic b)) (h₁ : AntitoneOn f (Ici b)) :
    IsMaxOn f univ b :=
  fun x _ => by rcases le_total x b <;> aesop

/-- If `f` is antitone on `Iic b` and monotone on `Ici b`, then the minimum of `f` is attained
at `b`. -/
/-
**isMinOn_univ_of_anti_mono** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isMinOn_univ_of_anti_mono (h₀ : AntitoneOn f (Iic b)) (h₁ : MonotoneOn f (
Ici b)) : IsMinOn f univ b
参数：h₀ : AntitoneOn f (Iic b)；h₁ : MonotoneOn f (Ici b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `isMaxOn_univ_of_mono_anti`：isMaxOn_univ_of_mono_anti (h₀ : MonotoneOn f 
(Iic b)) (h₁ : AntitoneOn f (Ici b)) : IsMaxOn f univ b

--- 原说明 ---
If `f` is antitone on `Iic b` and monotone on `Ici b`, then the minimum of `f` i
s attained
at `b`.
-/
lemma isMinOn_univ_of_anti_mono (h₀ : AntitoneOn f (Iic b)) (h₁ : MonotoneOn f (Ici b)) :
    IsMinOn f univ b :=
  isMaxOn_univ_of_mono_anti (β := βᵒᵈ) h₀ h₁

end LinearOrder

section Eventually

/-! ### Relation with `eventually` comparisons of two functions -/


/-
**Filter.EventuallyLE.isMaxFilter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.EventuallyLE.isMaxFilter {α β : Type*} [Preorder β] {f g : α -> β} 
{a : α} {l : Filter α} (hle : g <=ᶠ[l] f) (hfga : f a = g a) (h : IsMaxFilter f 
l a) : IsMaxFilter g l a
参数：hle : g <=ᶠ[l] f；hfga : f a = g a；h : IsMaxFilter f l a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mp`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},   
(∀ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c

--- 原说明 ---
### Relation with `eventually` comparisons of two functions
-/
theorem Filter.EventuallyLE.isMaxFilter {α β : Type*} [Preorder β] {f g : α → β} {a : α}
    {l : Filter α} (hle : g ≤ᶠ[l] f) (hfga : f a = g a) (h : IsMaxFilter f l a) :
    IsMaxFilter g l a := by
  refine hle.mp (h.mono fun x hf hgf => ?_)
  rw [← hfga]
  exact le_trans hgf hf
/-
**IsMaxFilter.congr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMaxFilter.congr {α β : Type*} [Preorder β] {f g : α -> β} {a : α} {l : F
ilter α} (h : IsMaxFilter f l a) (heq : f =ᶠ[l] g) (hfga : f a = g a) : IsMaxFil
ter g l a
参数：h : IsMaxFilter f l a；heq : f =ᶠ[l] g；hfga : f a = g a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyLE.isMaxFilter`：Filter.EventuallyLE.isMaxFilter {α β : 
Type*} [Preorder β] {f g : α -> β} {a : α} {l : Filter α} (hle : g <=ᶠ[l] f) (hf
ga : f a = g a) (h : …
· 使用定理 `Filter.EventuallyEq.le`：∀ {α : Type u} {β : Type v} [inst : Preorder β] 
{l : Filter α} {f g : α → β}, f =ᶠ[l] g → f ≤ᶠ[l] g
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
-/
theorem IsMaxFilter.congr {α β : Type*} [Preorder β] {f g : α → β} {a : α} {l : Filter α}
    (h : IsMaxFilter f l a) (heq : f =ᶠ[l] g) (hfga : f a = g a) : IsMaxFilter g l a :=
  heq.symm.le.isMaxFilter hfga h
/-
**Filter.EventuallyEq.isMaxFilter_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.EventuallyEq.isMaxFilter_iff {α β : Type*} [Preorder β] {f g : α ->
 β} {a : α} {l : Filter α} (heq : f =ᶠ[l] g) (hfga : f a = g a) : IsMaxFilter f 
l a ↔ IsMaxFilter g l a
参数：heq : f =ᶠ[l] g；hfga : f a = g a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsMaxFilter.congr`：IsMaxFilter.congr {α β : Type*} [Preorder β] {f g : α
 -> β} {a : α} {l : Filter α} (h : IsMaxFilter f l a) (heq : f =ᶠ[l] g) (hfga : 
f a = g…
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem Filter.EventuallyEq.isMaxFilter_iff {α β : Type*} [Preorder β] {f g : α → β} {a : α}
    {l : Filter α} (heq : f =ᶠ[l] g) (hfga : f a = g a) : IsMaxFilter f l a ↔ IsMaxFilter g l a :=
  ⟨fun h => h.congr heq hfga, fun h => h.congr heq.symm hfga.symm⟩
/-
**Filter.EventuallyLE.isMinFilter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.EventuallyLE.isMinFilter {α β : Type*} [Preorder β] {f g : α -> β} 
{a : α} {l : Filter α} (hle : f <=ᶠ[l] g) (hfga : f a = g a) (h : IsMinFilter f 
l a) : IsMinFilter g l a
参数：hle : f <=ᶠ[l] g；hfga : f a = g a；h : IsMinFilter f l a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyLE.isMaxFilter`：Filter.EventuallyLE.isMaxFilter {α β : 
Type*} [Preorder β] {f g : α -> β} {a : α} {l : Filter α} (hle : g <=ᶠ[l] f) (hf
ga : f a = g a) (h : …
-/
theorem Filter.EventuallyLE.isMinFilter {α β : Type*} [Preorder β] {f g : α → β} {a : α}
    {l : Filter α} (hle : f ≤ᶠ[l] g) (hfga : f a = g a) (h : IsMinFilter f l a) :
    IsMinFilter g l a :=
  @Filter.EventuallyLE.isMaxFilter _ βᵒᵈ _ _ _ _ _ hle hfga h
/-
**IsMinFilter.congr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMinFilter.congr {α β : Type*} [Preorder β] {f g : α -> β} {a : α} {l : F
ilter α} (h : IsMinFilter f l a) (heq : f =ᶠ[l] g) (hfga : f a = g a) : IsMinFil
ter g l a
参数：h : IsMinFilter f l a；heq : f =ᶠ[l] g；hfga : f a = g a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyLE.isMinFilter`：Filter.EventuallyLE.isMinFilter {α β : 
Type*} [Preorder β] {f g : α -> β} {a : α} {l : Filter α} (hle : f <=ᶠ[l] g) (hf
ga : f a = g a) (h : …
· 使用定理 `Filter.EventuallyEq.le`：∀ {α : Type u} {β : Type v} [inst : Preorder β] 
{l : Filter α} {f g : α → β}, f =ᶠ[l] g → f ≤ᶠ[l] g
-/
theorem IsMinFilter.congr {α β : Type*} [Preorder β] {f g : α → β} {a : α} {l : Filter α}
    (h : IsMinFilter f l a) (heq : f =ᶠ[l] g) (hfga : f a = g a) : IsMinFilter g l a :=
  heq.le.isMinFilter hfga h
/-
**Filter.EventuallyEq.isMinFilter_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.EventuallyEq.isMinFilter_iff {α β : Type*} [Preorder β] {f g : α ->
 β} {a : α} {l : Filter α} (heq : f =ᶠ[l] g) (hfga : f a = g a) : IsMinFilter f 
l a ↔ IsMinFilter g l a
参数：heq : f =ᶠ[l] g；hfga : f a = g a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsMinFilter.congr`：IsMinFilter.congr {α β : Type*} [Preorder β] {f g : α
 -> β} {a : α} {l : Filter α} (h : IsMinFilter f l a) (heq : f =ᶠ[l] g) (hfga : 
f a = g…
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem Filter.EventuallyEq.isMinFilter_iff {α β : Type*} [Preorder β] {f g : α → β} {a : α}
    {l : Filter α} (heq : f =ᶠ[l] g) (hfga : f a = g a) : IsMinFilter f l a ↔ IsMinFilter g l a :=
  ⟨fun h => h.congr heq hfga, fun h => h.congr heq.symm hfga.symm⟩
/-
**IsExtrFilter.congr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsExtrFilter.congr {α β : Type*} [Preorder β] {f g : α -> β} {a : α} {l : 
Filter α} (h : IsExtrFilter f l a) (heq : f =ᶠ[l] g) (hfga : f a = g a) : IsExtr
Filter g l a
参数：h : IsExtrFilter f l a；heq : f =ᶠ[l] g；hfga : f a = g a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsExtrFilter.eq_1`：∀ {α : Type u} {β : Type v} [inst : Preorder β] (f : 
α → β) (l : Filter α) (a : α),   IsExtrFilter f l a = (IsMinFilter f l a ∨ IsMax
Filter …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.EventuallyEq.isMaxFilter_iff`：Filter.EventuallyEq.isMaxFilter_iff
 {α β : Type*} [Preorder β] {f g : α -> β} {a : α} {l : Filter α} (heq : f =ᶠ[l]
 g) (hfga : f a = g a) : …
· 使用定理 `Filter.EventuallyEq.isMinFilter_iff`：Filter.EventuallyEq.isMinFilter_iff
 {α β : Type*} [Preorder β] {f g : α -> β} {a : α} {l : Filter α} (heq : f =ᶠ[l]
 g) (hfga : f a = g a) : …
-/
theorem IsExtrFilter.congr {α β : Type*} [Preorder β] {f g : α → β} {a : α} {l : Filter α}
    (h : IsExtrFilter f l a) (heq : f =ᶠ[l] g) (hfga : f a = g a) : IsExtrFilter g l a := by
  rw [IsExtrFilter] at *
  rwa [← heq.isMaxFilter_iff hfga, ← heq.isMinFilter_iff hfga]
/-
**Filter.EventuallyEq.isExtrFilter_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.EventuallyEq.isExtrFilter_iff {α β : Type*} [Preorder β] {f g : α -
> β} {a : α} {l : Filter α} (heq : f =ᶠ[l] g) (hfga : f a = g a) : IsExtrFilter 
f l a ↔ IsExtrFilter g l a
参数：heq : f =ᶠ[l] g；hfga : f a = g a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsExtrFilter.congr`：IsExtrFilter.congr {α β : Type*} [Preorder β] {f g :
 α -> β} {a : α} {l : Filter α} (h : IsExtrFilter f l a) (heq : f =ᶠ[l] g) (hfga
 : f a =…
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem Filter.EventuallyEq.isExtrFilter_iff {α β : Type*} [Preorder β] {f g : α → β} {a : α}
    {l : Filter α} (heq : f =ᶠ[l] g) (hfga : f a = g a) : IsExtrFilter f l a ↔ IsExtrFilter g l a :=
  ⟨fun h => h.congr heq hfga, fun h => h.congr heq.symm hfga.symm⟩

end Eventually

/-! ### `isMaxOn`/`isMinOn` imply `ciSup`/`ciInf` -/


section ConditionallyCompleteLinearOrder

variable [ConditionallyCompleteLinearOrder α] {f : β → α} {s : Set β} {x₀ : β}

/-
**IsMaxOn.iSup_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMaxOn.iSup_eq (hx₀ : x₀ in s) (h : IsMaxOn f s x₀) : ⨆ x : s, f x = f x₀
参数：hx₀ : x₀ in s；h : IsMaxOn f s x₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ciSup_eq_of_forall_le_of_forall_lt_exists_gt`：ciSup_eq_of_forall_le_of_f
orall_lt_exists_gt [Nonempty ι] {f : ι -> α} (h₁ : forall i, f i <= b) (h₂ : for
all w, w < b -> exists i, w < f i)…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem IsMaxOn.iSup_eq (hx₀ : x₀ ∈ s) (h : IsMaxOn f s x₀) : ⨆ x : s, f x = f x₀ :=
  haveI : Nonempty s := ⟨⟨x₀, hx₀⟩⟩
  ciSup_eq_of_forall_le_of_forall_lt_exists_gt (fun x => h x.2) fun _w hw => ⟨⟨x₀, hx₀⟩, hw⟩
/-
**IsMinOn.iInf_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMinOn.iInf_eq (hx₀ : x₀ in s) (h : IsMinOn f s x₀) : ⨅ x : s, f x = f x₀
参数：hx₀ : x₀ in s；h : IsMinOn f s x₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsMaxOn.iSup_eq`：IsMaxOn.iSup_eq (hx₀ : x₀ in s) (h : IsMaxOn f s x₀) : 
⨆ x : s, f x = f x₀
-/
theorem IsMinOn.iInf_eq (hx₀ : x₀ ∈ s) (h : IsMinOn f s x₀) : ⨅ x : s, f x = f x₀ :=
  @IsMaxOn.iSup_eq αᵒᵈ β _ _ _ _ hx₀ h

end ConditionallyCompleteLinearOrder

/-! ### Value of `Finset.sup` / `Finset.inf` -/

section SemilatticeSup

variable [SemilatticeSup β] [OrderBot β] {D : α → β} {s : Finset α}

/-
**sup_eq_of_isMaxOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sup_eq_of_isMaxOn {a : α} (hmem : a in s) (hmax : IsMaxOn D s a) : s.sup D
 = D a
参数：hmem : a in s；hmax : IsMaxOn D s a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Finset.sup_le`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSup α]
 [inst_1 : OrderBot α] {s : Finset β} {f : β → α} {a : α},   (∀ b ∈ s, f b ≤ a) 
→ s…
· 使用定理 `Finset.le_sup`：le_sup {b : β} (hb : b in s) : f b <= s.sup f
-/
theorem sup_eq_of_isMaxOn {a : α} (hmem : a ∈ s) (hmax : IsMaxOn D s a) : s.sup D = D a :=
  (Finset.sup_le hmax).antisymm (Finset.le_sup hmem)
/-
**sup_eq_of_max** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sup_eq_of_max [Nonempty α] {b : β} (hb : b in Set.range D) (hmem : D.invFu
n b in s) (hmax : forall a in s, D a <= b) : s.sup D = b
参数：hb : b in Set.range D；hmem : D.invFun b in s；hmax : forall a in s, D a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.apply_invFun_apply`：apply_invFun_apply {α β : Type*} {f : α -> 
β} {a : α} : f (@invFun _ _ ⟨a⟩ f (f a)) = f a
· 使用定理 `sup_eq_of_isMaxOn`：sup_eq_of_isMaxOn {a : α} (hmem : a in s) (hmax : IsM
axOn D s a) : s.sup D = D a
-/
theorem sup_eq_of_max [Nonempty α] {b : β} (hb : b ∈ Set.range D) (hmem : D.invFun b ∈ s)
    (hmax : ∀ a ∈ s, D a ≤ b) : s.sup D = b := by
  obtain ⟨a, rfl⟩ := hb
  rw [← Function.apply_invFun_apply (f := D)]
  apply sup_eq_of_isMaxOn hmem; intro
  rw [Function.apply_invFun_apply (f := D)]; apply hmax

end SemilatticeSup

section SemilatticeInf

variable [SemilatticeInf β] [OrderTop β] {D : α → β} {s : Finset α}

/-
**inf_eq_of_isMinOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inf_eq_of_isMinOn {a : α} (hmem : a in s) (hmax : IsMinOn D s a) : s.inf D
 = D a
参数：hmem : a in s；hmax : IsMinOn D s a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_eq_of_isMaxOn`：sup_eq_of_isMaxOn {a : α} (hmem : a in s) (hmax : IsM
axOn D s a) : s.sup D = D a
· 使用定理 `IsMinOn.dual`：∀ {α : Type u} {β : Type v} [inst : Preorder β] {f : α → β
} {s : Set α} {a : α},   IsMinOn f s a → IsMaxOn (⇑OrderDual.toDual ∘ f) s a
-/
theorem inf_eq_of_isMinOn {a : α} (hmem : a ∈ s) (hmax : IsMinOn D s a) : s.inf D = D a :=
  sup_eq_of_isMaxOn (α := αᵒᵈ) (β := βᵒᵈ) hmem hmax.dual
/-
**inf_eq_of_min** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inf_eq_of_min [Nonempty α] {b : β} (hb : b in Set.range D) (hmem : D.invFu
n b in s) (hmin : forall a in s, b <= D a) : s.inf D = b
参数：hb : b in Set.range D；hmem : D.invFun b in s；hmin : forall a in s, b <= D a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_eq_of_max`：sup_eq_of_max [Nonempty α] {b : β} (hb : b in Set.range D
) (hmem : D.invFun b in s) (hmax : forall a in s, D a <= b) : s.sup D = b
· 使用定理 `OrderDual.instNonempty`：∀ (α : Type u_2) [h : Nonempty α], Nonempty αᵒᵈ
-/
theorem inf_eq_of_min [Nonempty α] {b : β} (hb : b ∈ Set.range D) (hmem : D.invFun b ∈ s)
    (hmin : ∀ a ∈ s, b ≤ D a) : s.inf D = b :=
  sup_eq_of_max (α := αᵒᵈ) (β := βᵒᵈ) hb hmem hmin

end SemilatticeInf

