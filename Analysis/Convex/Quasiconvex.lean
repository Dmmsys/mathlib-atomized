/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Antoine Chambert-Loir, Anatole Dedecker
-/
module

public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.Convex.PathConnected

/-!
# Quasiconvex and quasiconcave functions

This file defines quasiconvexity, quasiconcavity and quasilinearity of functions, which are
generalizations of unimodality and monotonicity. Convexity implies quasiconvexity, concavity implies
quasiconcavity, and monotonicity implies quasilinearity.

## Main declarations

* `QuasiconvexOn 𝕜 s f`: Quasiconvexity of the function `f` on the set `s` with scalars `𝕜`. This
  means that, for all `r`, `{x ∈ s | f x ≤ r}` is `𝕜`-convex.
* `QuasiconcaveOn 𝕜 s f`: Quasiconcavity of the function `f` on the set `s` with scalars `𝕜`. This
  means that, for all `r`, `{x ∈ s | r ≤ f x}` is `𝕜`-convex.
* `QuasilinearOn 𝕜 s f`: Quasilinearity of the function `f` on the set `s` with scalars `𝕜`. This
  means that `f` is both quasiconvex and quasiconcave.

## References

* https://en.wikipedia.org/wiki/Quasiconvex_function
-/

@[expose] public section


open Function OrderDual Set

variable {𝕜 E β : Type*}

section OrderedSemiring

variable [Semiring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E]

section LE_β

variable (𝕜) [LE β] [SMul 𝕜 E] (s : Set E) (f : E → β)

/-- A function is quasiconvex if all its sublevels are convex.
This means that, for all `r`, `{x ∈ s | f x ≤ r}` is `𝕜`-convex. -/
/-
**QuasiconvexOn** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：QuasiconvexOn : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function is quasiconvex if all its sublevels are convex.
This means that, for all `r`, `{x ∈ s | f x ≤ r}` is `𝕜`-convex.
-/
def QuasiconvexOn : Prop :=
  ∀ r, Convex 𝕜 ({ x ∈ s | f x ≤ r })

/-- A function is quasiconcave if all its superlevels are convex.
This means that, for all `r`, `{x ∈ s | r ≤ f x}` is `𝕜`-convex. -/
/-
**QuasiconcaveOn** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：QuasiconcaveOn : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function is quasiconcave if all its superlevels are convex.
This means that, for all `r`, `{x ∈ s | r ≤ f x}` is `𝕜`-convex.
-/
def QuasiconcaveOn : Prop :=
  ∀ r, Convex 𝕜 ({ x ∈ s | r ≤ f x })

/-- A function is quasilinear if it is both quasiconvex and quasiconcave.
This means that, for all `r`,
the sets `{x ∈ s | f x ≤ r}` and `{x ∈ s | r ≤ f x}` are `𝕜`-convex. -/
/-
**QuasilinearOn** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：QuasilinearOn : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function is quasilinear if it is both quasiconvex and quasiconcave.
This means that, for all `r`,
the sets `{x ∈ s | f x ≤ r}` and `{x ∈ s | r ≤ f x}` are `𝕜`-convex.
-/
def QuasilinearOn : Prop :=
  QuasiconvexOn 𝕜 s f ∧ QuasiconcaveOn 𝕜 s f

variable {𝕜 s f}
/-
**QuasiconvexOn.dual** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：QuasiconvexOn.dual : QuasiconvexOn 𝕜 s f -> QuasiconcaveOn 𝕜 s (toDual ∘ f
)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem QuasiconvexOn.dual : QuasiconvexOn 𝕜 s f → QuasiconcaveOn 𝕜 s (toDual ∘ f) :=
  id
/-
**QuasiconcaveOn.dual** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：QuasiconcaveOn.dual : QuasiconcaveOn 𝕜 s f -> QuasiconvexOn 𝕜 s (toDual ∘ 
f)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem QuasiconcaveOn.dual : QuasiconcaveOn 𝕜 s f → QuasiconvexOn 𝕜 s (toDual ∘ f) :=
  id
/-
**QuasilinearOn.dual** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：QuasilinearOn.dual : QuasilinearOn 𝕜 s f -> QuasilinearOn 𝕜 s (toDual ∘ f)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.symm`：∀ {a b : Prop}, a ∧ b → b ∧ a
-/
theorem QuasilinearOn.dual : QuasilinearOn 𝕜 s f → QuasilinearOn 𝕜 s (toDual ∘ f) :=
  And.symm
/-
**Convex.quasiconvexOn_of_convex_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Convex.quasiconvexOn_of_convex_le (hs : Convex 𝕜 s) (h : forall r, Convex 
𝕜 { x | f x <= r }) : QuasiconvexOn 𝕜 s f
参数：hs : Convex 𝕜 s；h : forall r, Convex 𝕜 { x | f x <= r }。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Convex.inter`：Convex.inter {t : Set E} (hs : Convex 𝕜 s) (ht : Convex 𝕜 
t) : Convex 𝕜 (s inter t)
-/
theorem Convex.quasiconvexOn_of_convex_le (hs : Convex 𝕜 s) (h : ∀ r, Convex 𝕜 { x | f x ≤ r }) :
    QuasiconvexOn 𝕜 s f := fun r => hs.inter (h r)
/-
**Convex.quasiconcaveOn_of_convex_ge** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Convex.quasiconcaveOn_of_convex_ge (hs : Convex 𝕜 s) (h : forall r, Convex
 𝕜 { x | r <= f x }) : QuasiconcaveOn 𝕜 s f
参数：hs : Convex 𝕜 s；h : forall r, Convex 𝕜 { x | r <= f x }。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Convex.quasiconvexOn_of_convex_le`：Convex.quasiconvexOn_of_convex_le (hs
 : Convex 𝕜 s) (h : forall r, Convex 𝕜 { x | f x <= r }) : QuasiconvexOn 𝕜 s f
-/
theorem Convex.quasiconcaveOn_of_convex_ge (hs : Convex 𝕜 s) (h : ∀ r, Convex 𝕜 { x | r ≤ f x }) :
    QuasiconcaveOn 𝕜 s f :=
  Convex.quasiconvexOn_of_convex_le (β := βᵒᵈ) hs h
/-
**QuasiconvexOn.convex** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：QuasiconvexOn.convex [IsDirectedOrder β] (hf : QuasiconvexOn 𝕜 s f) : Conv
ex 𝕜 s
参数：hf : QuasiconvexOn 𝕜 s f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_ge_ge`：exists_ge_ge [LE α] [IsDirectedOrder α] (a b : α) : exists
 c, a <= c ∧ b <= c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem QuasiconvexOn.convex [IsDirectedOrder β] (hf : QuasiconvexOn 𝕜 s f) : Convex 𝕜 s :=
  fun x hx y hy _ _ ha hb hab =>
  let ⟨_, hxz, hyz⟩ := exists_ge_ge (f x) (f y)
  (hf _ ⟨hx, hxz⟩ ⟨hy, hyz⟩ ha hb hab).1
/-
**QuasiconcaveOn.convex** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：QuasiconcaveOn.convex [IsCodirectedOrder β] (hf : QuasiconcaveOn 𝕜 s f) : 
Convex 𝕜 s
参数：hf : QuasiconcaveOn 𝕜 s f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuasiconvexOn.convex`：QuasiconvexOn.convex [IsDirectedOrder β] (hf : Qua
siconvexOn 𝕜 s f) : Convex 𝕜 s
· 使用定理 `OrderDual.isDirected_le`：∀ {α : Type u_1} [inst : LE α] [IsCodirectedOrd
er α], IsDirectedOrder αᵒᵈ
· 使用定理 `QuasiconcaveOn.dual`：QuasiconcaveOn.dual : QuasiconcaveOn 𝕜 s f -> Quasi
convexOn 𝕜 s (toDual ∘ f)
-/
theorem QuasiconcaveOn.convex [IsCodirectedOrder β] (hf : QuasiconcaveOn 𝕜 s f) : Convex 𝕜 s :=
  hf.dual.convex

end LE_β

section Composition

variable {𝕜 E : Type*} [Semiring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E] [SMul 𝕜 E]
variable {β γ : Type*} [LinearOrder β] [Preorder γ]
variable {s : Set E} {f : E → β} {g : β → γ}

/-
**QuasiconvexOn.monotone_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：QuasiconvexOn.monotone_comp (hg : Monotone g) (hf : QuasiconvexOn 𝕜 s f) :
 QuasiconvexOn 𝕜 s (g ∘ f)
参数：hg : Monotone g；hf : QuasiconvexOn 𝕜 s f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem QuasiconvexOn.monotone_comp
    (hg : Monotone g) (hf : QuasiconvexOn 𝕜 s f) :
    QuasiconvexOn 𝕜 s (g ∘ f) := fun c x hx y hy ↦ by
  simp only [Function.comp_apply, mem_ofPred_eq] at hx hy
  intro a b ha hb hab
  simp only [Function.comp_apply, mem_ofPred_eq]
  wlog h : f x ≤ f y
  · grind
  specialize hf (f y) ⟨hx.1, h⟩ ⟨hy.1, le_rfl⟩ ha hb hab
  simp only [mem_ofPred_eq] at hf
  exact ⟨hf.1, le_trans (hg hf.2) hy.2⟩
/-
**QuasiconvexOn.antitone_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：QuasiconvexOn.antitone_comp (hg : Antitone g) (hf : QuasiconvexOn 𝕜 s f) :
 QuasiconcaveOn 𝕜 s (g ∘ f)
参数：hg : Antitone g；hf : QuasiconvexOn 𝕜 s f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuasiconvexOn.monotone_comp`：QuasiconvexOn.monotone_comp (hg : Monotone 
g) (hf : QuasiconvexOn 𝕜 s f) : QuasiconvexOn 𝕜 s (g ∘ f)
-/
theorem QuasiconvexOn.antitone_comp (hg : Antitone g) (hf : QuasiconvexOn 𝕜 s f) :
    QuasiconcaveOn 𝕜 s (g ∘ f) :=
  hf.monotone_comp (γ := γᵒᵈ) hg
/-
**QuasiconcaveOn.monotone_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：QuasiconcaveOn.monotone_comp (hg : Monotone g) (hf : QuasiconcaveOn 𝕜 s f)
 : QuasiconcaveOn 𝕜 s (g ∘ f)
参数：hg : Monotone g；hf : QuasiconcaveOn 𝕜 s f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuasiconvexOn.monotone_comp`：QuasiconvexOn.monotone_comp (hg : Monotone 
g) (hf : QuasiconvexOn 𝕜 s f) : QuasiconvexOn 𝕜 s (g ∘ f)
· 使用定理 `Monotone.dual`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1 :
 Preorder β] {f : α → β},   Monotone f → Monotone (⇑OrderDual.toDual ∘ f ∘ ⇑Orde
rDu…
-/
theorem QuasiconcaveOn.monotone_comp (hg : Monotone g) (hf : QuasiconcaveOn 𝕜 s f) :
    QuasiconcaveOn 𝕜 s (g ∘ f) :=
  QuasiconvexOn.monotone_comp hg.dual hf
/-
**QuasiconcaveOn.antitone_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：QuasiconcaveOn.antitone_comp (hg : Antitone g) (hf : QuasiconcaveOn 𝕜 s f)
 : QuasiconvexOn 𝕜 s (g ∘ f)
参数：hg : Antitone g；hf : QuasiconcaveOn 𝕜 s f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuasiconvexOn.monotone_comp`：QuasiconvexOn.monotone_comp (hg : Monotone 
g) (hf : QuasiconvexOn 𝕜 s f) : QuasiconvexOn 𝕜 s (g ∘ f)
· 使用定理 `Antitone.dual`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1 :
 Preorder β] {f : α → β},   Antitone f → Antitone (⇑OrderDual.toDual ∘ f ∘ ⇑Orde
rDu…
-/
theorem QuasiconcaveOn.antitone_comp (hg : Antitone g) (hf : QuasiconcaveOn 𝕜 s f) :
    QuasiconvexOn 𝕜 s (g ∘ f) :=
  QuasiconvexOn.monotone_comp (β := βᵒᵈ) hg.dual hf
/-
**QuasilinearOn.monotone_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：QuasilinearOn.monotone_comp (hg : Monotone g) (hf : QuasilinearOn 𝕜 s f) :
 QuasilinearOn 𝕜 s (g ∘ f)
参数：hg : Monotone g；hf : QuasilinearOn 𝕜 s f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuasiconvexOn.monotone_comp`：QuasiconvexOn.monotone_comp (hg : Monotone 
g) (hf : QuasiconvexOn 𝕜 s f) : QuasiconvexOn 𝕜 s (g ∘ f)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `QuasiconcaveOn.monotone_comp`：QuasiconcaveOn.monotone_comp (hg : Monoton
e g) (hf : QuasiconcaveOn 𝕜 s f) : QuasiconcaveOn 𝕜 s (g ∘ f)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem QuasilinearOn.monotone_comp (hg : Monotone g) (hf : QuasilinearOn 𝕜 s f) :
    QuasilinearOn 𝕜 s (g ∘ f) :=
  ⟨hf.1.monotone_comp hg, hf.2.monotone_comp hg⟩
/-
**QuasilinearOn.antitone_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：QuasilinearOn.antitone_comp (hg : Antitone g) (hf : QuasilinearOn 𝕜 s f) :
 QuasilinearOn 𝕜 s (g ∘ f)
参数：hg : Antitone g；hf : QuasilinearOn 𝕜 s f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuasiconcaveOn.antitone_comp`：QuasiconcaveOn.antitone_comp (hg : Antiton
e g) (hf : QuasiconcaveOn 𝕜 s f) : QuasiconvexOn 𝕜 s (g ∘ f)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `QuasiconvexOn.antitone_comp`：QuasiconvexOn.antitone_comp (hg : Antitone 
g) (hf : QuasiconvexOn 𝕜 s f) : QuasiconcaveOn 𝕜 s (g ∘ f)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem QuasilinearOn.antitone_comp (hg : Antitone g) (hf : QuasilinearOn 𝕜 s f) :
    QuasilinearOn 𝕜 s (g ∘ f) :=
  ⟨hf.2.antitone_comp hg, hf.1.antitone_comp hg⟩

end Composition

section Restriction

variable {𝕜 E : Type*} [Semiring 𝕜] [PartialOrder 𝕜]
  [AddCommMonoid E] [SMul 𝕜 E]
variable {β : Type*} [Preorder β]
variable {s : Set E} {f : E → β}

/-
**Convex.quasiconvexOn_restrict** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Convex.quasiconvexOn_restrict {t : Set E} (hf : QuasiconvexOn 𝕜 s f) (hst 
: t subseteq s) (ht : Convex 𝕜 t) : QuasiconvexOn 𝕜 t f
参数：hf : QuasiconvexOn 𝕜 s f；hst : t subseteq s；ht : Convex 𝕜 t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sep_eq_inter_sep`：sep_eq_inter_sep {α : Type*} {s t : Set α} {p : α 
-> Prop} (hst : s subseteq t) : {x in s | p x} = s inter {x in t | p x}
· 使用定理 `Convex.inter`：Convex.inter {t : Set E} (hs : Convex 𝕜 s) (ht : Convex 𝕜 
t) : Convex 𝕜 (s inter t)
-/
theorem Convex.quasiconvexOn_restrict {t : Set E} (hf : QuasiconvexOn 𝕜 s f) (hst : t ⊆ s)
    (ht : Convex 𝕜 t) : QuasiconvexOn 𝕜 t f := by
  intro b
  rw [Set.sep_eq_inter_sep hst]
  exact Convex.inter ht (hf b)
/-
**Convex.quasiconcaveOn_restrict** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Convex.quasiconcaveOn_restrict {t : Set E} (hf : QuasiconcaveOn 𝕜 s f) (hs
t : t subseteq s) (ht : Convex 𝕜 t) : QuasiconcaveOn 𝕜 t f
参数：hf : QuasiconcaveOn 𝕜 s f；hst : t subseteq s；ht : Convex 𝕜 t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sep_eq_inter_sep`：sep_eq_inter_sep {α : Type*} {s t : Set α} {p : α 
-> Prop} (hst : s subseteq t) : {x in s | p x} = s inter {x in t | p x}
· 使用定理 `Convex.inter`：Convex.inter {t : Set E} (hs : Convex 𝕜 s) (ht : Convex 𝕜 
t) : Convex 𝕜 (s inter t)
-/
theorem Convex.quasiconcaveOn_restrict {t : Set E} (hf : QuasiconcaveOn 𝕜 s f) (hst : t ⊆ s)
    (ht : Convex 𝕜 t) : QuasiconcaveOn 𝕜 t f := by
  intro b
  rw [Set.sep_eq_inter_sep hst]
  exact Convex.inter ht (hf b)

end Restriction

section Preconnected

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

variable {β : Type*} [Preorder β] {f : E → β}

open scoped Set.Notation

/-- If `f` is quasiconcave, then its over-levels are connected. -/
/-
**QuasiconcaveOn.isPreconnected_preimage_subtype** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：QuasiconcaveOn.isPreconnected_preimage_subtype {s : Set E} {t : β} (hfc : 
QuasiconcaveOn Real s f) : IsPreconnected (s ↓inter (f ⁻¹' Ici t))
参数：hfc : QuasiconcaveOn Real s f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Topology.IsInducing.isPreconnected_image`：Topology.IsInducing.isPreconne
cted_image [TopologicalSpace β] {s : Set α} {f : α -> β} (hf : IsInducing f) : I
sPreconnected (f '' s) ↔ IsPre…
· 使用引理 `Topology.IsInducing.subtypeVal`：Topology.IsInducing.subtypeVal {t : Set 
Y} : IsInducing ((↑) : t -> Y)
· 使用定理 `Set.image_preimage_eq_inter_range`：image_preimage_eq_inter_range {f : α 
-> β} {t : Set β} : f '' f ⁻¹' t = t inter range f
· 使用定理 `Subtype.range_coe`：range_coe {s : Set α} : range ((↑) : s -> α) = s
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `Convex.isPreconnected`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst_1 
: _root_.Module ℝ E] [inst_2 : TopologicalSpace E] [ContinuousAdd E]   [Continuo
usSMul ℝ E]…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G

--- 原说明 ---
If `f` is quasiconcave, then its over-levels are connected.
-/
theorem QuasiconcaveOn.isPreconnected_preimage_subtype {s : Set E} {t : β}
    (hfc : QuasiconcaveOn ℝ s f) :
    IsPreconnected (s ↓∩ (f ⁻¹' Ici t)) := by
  rw [← Topology.IsInducing.subtypeVal.isPreconnected_image,
    image_preimage_eq_inter_range,
    Subtype.range_coe, inter_comm]
  exact (hfc t).isPreconnected

/-- If `f` is quasiconcave, then its under-levels are connected. -/
/-
**QuasiconvexOn.isPreconnected_preimage_subtype** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：QuasiconvexOn.isPreconnected_preimage_subtype {s : Set E} {t : β} (hfc : Q
uasiconvexOn Real s f) : IsPreconnected (s ↓inter (f ⁻¹' Iic t))
参数：hfc : QuasiconvexOn Real s f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuasiconcaveOn.isPreconnected_preimage_subtype`：QuasiconcaveOn.isPreconn
ected_preimage_subtype {s : Set E} {t : β} (hfc : QuasiconcaveOn Real s f) : IsP
reconnected (s ↓inter (f ⁻¹' Ici t))

--- 原说明 ---
If `f` is quasiconcave, then its under-levels are connected.
-/
theorem QuasiconvexOn.isPreconnected_preimage_subtype {s : Set E} {t : β}
    (hfc : QuasiconvexOn ℝ s f) :
    IsPreconnected (s ↓∩ (f ⁻¹' Iic t)) :=
  QuasiconcaveOn.isPreconnected_preimage_subtype (β := βᵒᵈ) hfc
/-
**QuasilinearOn.isPreconnected_preimage_subtype** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：QuasilinearOn.isPreconnected_preimage_subtype {s : Set E} {t : β} (hfc : Q
uasilinearOn Real s f) : IsPreconnected (s ↓inter f ⁻¹' Iic t)
参数：hfc : QuasilinearOn Real s f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuasiconvexOn.isPreconnected_preimage_subtype`：QuasiconvexOn.isPreconnec
ted_preimage_subtype {s : Set E} {t : β} (hfc : QuasiconvexOn Real s f) : IsPrec
onnected (s ↓inter (f ⁻¹' Iic t))
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem QuasilinearOn.isPreconnected_preimage_subtype {s : Set E} {t : β}
    (hfc : QuasilinearOn ℝ s f) :
    IsPreconnected (s ↓∩ f ⁻¹' Iic t) :=
  hfc.left.isPreconnected_preimage_subtype

end Preconnected

section Semilattice_β

variable [SMul 𝕜 E] {s : Set E} {f g : E → β}

/-
**QuasiconvexOn.sup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：QuasiconvexOn.sup [SemilatticeSup β] (hf : QuasiconvexOn 𝕜 s f) (hg : Quas
iconvexOn 𝕜 s g) : QuasiconvexOn 𝕜 s (f ⊔ g)
参数：hf : QuasiconvexOn 𝕜 s f；hg : QuasiconvexOn 𝕜 s g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.sep_and`：sep_and : { x in s | p x ∧ q x } = { x in s | p x } inter {
 x in s | q x }
· 使用定理 `Convex.inter`：Convex.inter {t : Set E} (hs : Convex 𝕜 s) (ht : Convex 𝕜 
t) : Convex 𝕜 (s inter t)
-/
theorem QuasiconvexOn.sup [SemilatticeSup β] (hf : QuasiconvexOn 𝕜 s f)
    (hg : QuasiconvexOn 𝕜 s g) : QuasiconvexOn 𝕜 s (f ⊔ g) := by
  intro r
  simp_rw [Pi.sup_def, sup_le_iff, Set.sep_and]
  exact (hf r).inter (hg r)
/-
**QuasiconcaveOn.inf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：QuasiconcaveOn.inf [SemilatticeInf β] (hf : QuasiconcaveOn 𝕜 s f) (hg : Qu
asiconcaveOn 𝕜 s g) : QuasiconcaveOn 𝕜 s (f ⊓ g)
参数：hf : QuasiconcaveOn 𝕜 s f；hg : QuasiconcaveOn 𝕜 s g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuasiconvexOn.sup`：QuasiconvexOn.sup [SemilatticeSup β] (hf : Quasiconve
xOn 𝕜 s f) (hg : QuasiconvexOn 𝕜 s g) : QuasiconvexOn 𝕜 s (f ⊔ g)
· 使用定理 `QuasiconcaveOn.dual`：QuasiconcaveOn.dual : QuasiconcaveOn 𝕜 s f -> Quasi
convexOn 𝕜 s (toDual ∘ f)
-/
theorem QuasiconcaveOn.inf [SemilatticeInf β] (hf : QuasiconcaveOn 𝕜 s f)
    (hg : QuasiconcaveOn 𝕜 s g) : QuasiconcaveOn 𝕜 s (f ⊓ g) :=
  hf.dual.sup hg

end Semilattice_β

section LinearOrder_β

variable [LinearOrder β] [SMul 𝕜 E] {s : Set E} {f : E → β}

/-
**quasiconvexOn_iff_le_max** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：quasiconvexOn_iff_le_max : QuasiconvexOn 𝕜 s f ↔ Convex 𝕜 s ∧ forall ⦃x⦄, 
x in s -> forall ⦃y⦄, y in s -> forall ⦃a b : 𝕜⦄, 0 <= a -> 0 <= b -> a + b = 1 
-> f (a • x + b • y) <= max (f x) (f y)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuasiconvexOn.convex`：QuasiconvexOn.convex [IsDirectedOrder β] (hf : Qua
siconvexOn 𝕜 s f) : Convex 𝕜 s
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `max_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b c : α}, a ≤ c → b ≤
 c → max a b ≤ c
-/
theorem quasiconvexOn_iff_le_max : QuasiconvexOn 𝕜 s f ↔ Convex 𝕜 s ∧ ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄,
    y ∈ s → ∀ ⦃a b : 𝕜⦄, 0 ≤ a → 0 ≤ b → a + b = 1 → f (a • x + b • y) ≤ max (f x) (f y) :=
  ⟨fun hf =>
    ⟨hf.convex, fun _ hx _ hy _ _ ha hb hab =>
      (hf _ ⟨hx, le_max_left _ _⟩ ⟨hy, le_max_right _ _⟩ ha hb hab).2⟩,
    fun hf _ _ hx _ hy _ _ ha hb hab =>
    ⟨hf.1 hx.1 hy.1 ha hb hab, (hf.2 hx.1 hy.1 ha hb hab).trans <| max_le hx.2 hy.2⟩⟩
/-
**quasiconcaveOn_iff_min_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：quasiconcaveOn_iff_min_le : QuasiconcaveOn 𝕜 s f ↔ Convex 𝕜 s ∧ forall ⦃x⦄
, x in s -> forall ⦃y⦄, y in s -> forall ⦃a b : 𝕜⦄, 0 <= a -> 0 <= b -> a + b = 
1 -> min (f x) (f y) <= f (a • x + b • y)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `quasiconvexOn_iff_le_max`：quasiconvexOn_iff_le_max : QuasiconvexOn 𝕜 s f
 ↔ Convex 𝕜 s ∧ forall ⦃x⦄, x in s -> forall ⦃y⦄, y in s -> forall ⦃a b : 𝕜⦄, 0 
<= a -> 0 <= b…
-/
theorem quasiconcaveOn_iff_min_le : QuasiconcaveOn 𝕜 s f ↔ Convex 𝕜 s ∧ ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄,
    y ∈ s → ∀ ⦃a b : 𝕜⦄, 0 ≤ a → 0 ≤ b → a + b = 1 → min (f x) (f y) ≤ f (a • x + b • y) :=
  quasiconvexOn_iff_le_max (β := βᵒᵈ)
/-
**quasilinearOn_iff_mem_uIcc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：quasilinearOn_iff_mem_uIcc : QuasilinearOn 𝕜 s f ↔ Convex 𝕜 s ∧ forall ⦃x⦄
, x in s -> forall ⦃y⦄, y in s -> forall ⦃a b : 𝕜⦄, 0 <= a -> 0 <= b -> a + b = 
1 -> f (a • x + b • y) in uIcc (f x) (f y)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `QuasilinearOn.eq_1`：∀ (𝕜 : Type u_1) {E : Type u_2} {β : Type u_3} [inst
 : Semiring 𝕜] [inst_1 : PartialOrder 𝕜] [inst_2 : AddCommMonoid E]   [inst_3 : 
LE β] [i…
· 使用定理 `quasiconvexOn_iff_le_max`：quasiconvexOn_iff_le_max : QuasiconvexOn 𝕜 s f
 ↔ Convex 𝕜 s ∧ forall ⦃x⦄, x in s -> forall ⦃y⦄, y in s -> forall ⦃a b : 𝕜⦄, 0 
<= a -> 0 <= b…
· 使用定理 `quasiconcaveOn_iff_min_le`：quasiconcaveOn_iff_min_le : QuasiconcaveOn 𝕜 
s f ↔ Convex 𝕜 s ∧ forall ⦃x⦄, x in s -> forall ⦃y⦄, y in s -> forall ⦃a b : 𝕜⦄,
 0 <= a -> 0 <=…
· 使用定理 `and_and_and_comm`：∀ {a b c d : Prop}, (a ∧ b) ∧ c ∧ d ↔ (a ∧ c) ∧ b ∧ d
· 使用定理 `and_self_iff`：∀ {a : Prop}, a ∧ a ↔ a
· 使用定理 `and_congr_right'`：∀ {b c a : Prop}, (b ↔ c) → (a ∧ b ↔ a ∧ c)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem quasilinearOn_iff_mem_uIcc : QuasilinearOn 𝕜 s f ↔ Convex 𝕜 s ∧ ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄,
    y ∈ s → ∀ ⦃a b : 𝕜⦄, 0 ≤ a → 0 ≤ b → a + b = 1 → f (a • x + b • y) ∈ uIcc (f x) (f y) := by
  rw [QuasilinearOn, quasiconvexOn_iff_le_max, quasiconcaveOn_iff_min_le, and_and_and_comm,
    and_self_iff]
  apply and_congr_right'
  simp_rw [← forall_and, ← Icc_min_max, mem_Icc, and_comm]
/-
**QuasiconvexOn.convex_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：QuasiconvexOn.convex_lt (hf : QuasiconvexOn 𝕜 s f) (r : β) : Convex 𝕜 ({ x
 in s | f x < r })
参数：hf : QuasiconvexOn 𝕜 s f；r : β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `max_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b c : α}, b < a → c <
 a → max b c < a
-/
theorem QuasiconvexOn.convex_lt (hf : QuasiconvexOn 𝕜 s f) (r : β) :
    Convex 𝕜 ({ x ∈ s | f x < r }) := by
  intro x hx y hy a b ha hb hab
  have h := hf _ ⟨hx.1, le_max_left _ _⟩ ⟨hy.1, le_max_right _ _⟩ ha hb hab
  exact ⟨h.1, h.2.trans_lt <| max_lt hx.2 hy.2⟩
/-
**QuasiconcaveOn.convex_gt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：QuasiconcaveOn.convex_gt (hf : QuasiconcaveOn 𝕜 s f) (r : β) : Convex 𝕜 ({
 x in s | r < f x })
参数：hf : QuasiconcaveOn 𝕜 s f；r : β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuasiconvexOn.convex_lt`：QuasiconvexOn.convex_lt (hf : QuasiconvexOn 𝕜 s
 f) (r : β) : Convex 𝕜 ({ x in s | f x < r })
· 使用定理 `QuasiconcaveOn.dual`：QuasiconcaveOn.dual : QuasiconcaveOn 𝕜 s f -> Quasi
convexOn 𝕜 s (toDual ∘ f)
-/
theorem QuasiconcaveOn.convex_gt (hf : QuasiconcaveOn 𝕜 s f) (r : β) :
    Convex 𝕜 ({ x ∈ s | r < f x }) :=
  hf.dual.convex_lt r

end LinearOrder_β

section PosSMulMono

variable [AddCommMonoid β] [PartialOrder β] [IsOrderedAddMonoid β]
  [Module 𝕜 E] [Module 𝕜 β] [PosSMulMono 𝕜 β]
  {s : Set E} {f : E → β}

/-
**ConvexOn.quasiconvexOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ConvexOn.quasiconvexOn (hf : ConvexOn 𝕜 s f) : QuasiconvexOn 𝕜 s f
参数：hf : ConvexOn 𝕜 s f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ConvexOn.convex_le`：ConvexOn.convex_le (hf : ConvexOn 𝕜 s f) (r : β) : C
onvex 𝕜 ({ x in s | f x <= r })
-/
theorem ConvexOn.quasiconvexOn (hf : ConvexOn 𝕜 s f) : QuasiconvexOn 𝕜 s f :=
  hf.convex_le
/-
**ConcaveOn.quasiconcaveOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ConcaveOn.quasiconcaveOn (hf : ConcaveOn 𝕜 s f) : QuasiconcaveOn 𝕜 s f
参数：hf : ConcaveOn 𝕜 s f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ConcaveOn.convex_ge`：ConcaveOn.convex_ge (hf : ConcaveOn 𝕜 s f) (r : β) 
: Convex 𝕜 ({ x in s | r <= f x })
-/
theorem ConcaveOn.quasiconcaveOn (hf : ConcaveOn 𝕜 s f) : QuasiconcaveOn 𝕜 s f :=
  hf.convex_ge

end PosSMulMono

section LinearOrder

variable [LinearOrder E] [IsOrderedAddMonoid E] [PartialOrder β] [Module 𝕜 E] [PosSMulMono 𝕜 E]
  {s : Set E} {f : E → β}

/-
**MonotoneOn.quasiconvexOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonotoneOn.quasiconvexOn (hf : MonotoneOn f s) (hs : Convex 𝕜 s) : Quasico
nvexOn 𝕜 s f
参数：hf : MonotoneOn f s；hs : Convex 𝕜 s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonotoneOn.convex_le`：MonotoneOn.convex_le (hf : MonotoneOn f s) (hs : C
onvex 𝕜 s) (r : β) : Convex 𝕜 ({ x in s | f x <= r })
-/
theorem MonotoneOn.quasiconvexOn (hf : MonotoneOn f s) (hs : Convex 𝕜 s) : QuasiconvexOn 𝕜 s f :=
  hf.convex_le hs
/-
**MonotoneOn.quasiconcaveOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonotoneOn.quasiconcaveOn (hf : MonotoneOn f s) (hs : Convex 𝕜 s) : Quasic
oncaveOn 𝕜 s f
参数：hf : MonotoneOn f s；hs : Convex 𝕜 s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonotoneOn.convex_ge`：MonotoneOn.convex_ge (hf : MonotoneOn f s) (hs : C
onvex 𝕜 s) (r : β) : Convex 𝕜 ({ x in s | r <= f x })
-/
theorem MonotoneOn.quasiconcaveOn (hf : MonotoneOn f s) (hs : Convex 𝕜 s) : QuasiconcaveOn 𝕜 s f :=
  hf.convex_ge hs
/-
**MonotoneOn.quasilinearOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonotoneOn.quasilinearOn (hf : MonotoneOn f s) (hs : Convex 𝕜 s) : Quasili
nearOn 𝕜 s f
参数：hf : MonotoneOn f s；hs : Convex 𝕜 s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonotoneOn.quasiconvexOn`：MonotoneOn.quasiconvexOn (hf : MonotoneOn f s)
 (hs : Convex 𝕜 s) : QuasiconvexOn 𝕜 s f
· 使用定理 `MonotoneOn.quasiconcaveOn`：MonotoneOn.quasiconcaveOn (hf : MonotoneOn f 
s) (hs : Convex 𝕜 s) : QuasiconcaveOn 𝕜 s f
-/
theorem MonotoneOn.quasilinearOn (hf : MonotoneOn f s) (hs : Convex 𝕜 s) : QuasilinearOn 𝕜 s f :=
  ⟨hf.quasiconvexOn hs, hf.quasiconcaveOn hs⟩
/-
**AntitoneOn.quasiconvexOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AntitoneOn.quasiconvexOn (hf : AntitoneOn f s) (hs : Convex 𝕜 s) : Quasico
nvexOn 𝕜 s f
参数：hf : AntitoneOn f s；hs : Convex 𝕜 s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AntitoneOn.convex_le`：AntitoneOn.convex_le (hf : AntitoneOn f s) (hs : C
onvex 𝕜 s) (r : β) : Convex 𝕜 ({ x in s | f x <= r })
-/
theorem AntitoneOn.quasiconvexOn (hf : AntitoneOn f s) (hs : Convex 𝕜 s) : QuasiconvexOn 𝕜 s f :=
  hf.convex_le hs
/-
**AntitoneOn.quasiconcaveOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AntitoneOn.quasiconcaveOn (hf : AntitoneOn f s) (hs : Convex 𝕜 s) : Quasic
oncaveOn 𝕜 s f
参数：hf : AntitoneOn f s；hs : Convex 𝕜 s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AntitoneOn.convex_ge`：AntitoneOn.convex_ge (hf : AntitoneOn f s) (hs : C
onvex 𝕜 s) (r : β) : Convex 𝕜 ({ x in s | r <= f x })
-/
theorem AntitoneOn.quasiconcaveOn (hf : AntitoneOn f s) (hs : Convex 𝕜 s) : QuasiconcaveOn 𝕜 s f :=
  hf.convex_ge hs
/-
**AntitoneOn.quasilinearOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AntitoneOn.quasilinearOn (hf : AntitoneOn f s) (hs : Convex 𝕜 s) : Quasili
nearOn 𝕜 s f
参数：hf : AntitoneOn f s；hs : Convex 𝕜 s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AntitoneOn.quasiconvexOn`：AntitoneOn.quasiconvexOn (hf : AntitoneOn f s)
 (hs : Convex 𝕜 s) : QuasiconvexOn 𝕜 s f
· 使用定理 `AntitoneOn.quasiconcaveOn`：AntitoneOn.quasiconcaveOn (hf : AntitoneOn f 
s) (hs : Convex 𝕜 s) : QuasiconcaveOn 𝕜 s f
-/
theorem AntitoneOn.quasilinearOn (hf : AntitoneOn f s) (hs : Convex 𝕜 s) : QuasilinearOn 𝕜 s f :=
  ⟨hf.quasiconvexOn hs, hf.quasiconcaveOn hs⟩
/-
**Monotone.quasiconvexOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Monotone.quasiconvexOn (hf : Monotone f) : QuasiconvexOn 𝕜 univ f
参数：hf : Monotone f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonotoneOn.quasiconvexOn`：MonotoneOn.quasiconvexOn (hf : MonotoneOn f s)
 (hs : Convex 𝕜 s) : QuasiconvexOn 𝕜 s f
· 使用定理 `Monotone.monotoneOn`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [in
st_1 : Preorder β] {f : α → β},   Monotone f → ∀ (s : Set α), MonotoneOn f s
· 使用定理 `convex_univ`：convex_univ : Convex 𝕜 (Set.univ : Set E)
-/
theorem Monotone.quasiconvexOn (hf : Monotone f) : QuasiconvexOn 𝕜 univ f :=
  (hf.monotoneOn _).quasiconvexOn convex_univ
/-
**Monotone.quasiconcaveOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Monotone.quasiconcaveOn (hf : Monotone f) : QuasiconcaveOn 𝕜 univ f
参数：hf : Monotone f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonotoneOn.quasiconcaveOn`：MonotoneOn.quasiconcaveOn (hf : MonotoneOn f 
s) (hs : Convex 𝕜 s) : QuasiconcaveOn 𝕜 s f
· 使用定理 `Monotone.monotoneOn`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [in
st_1 : Preorder β] {f : α → β},   Monotone f → ∀ (s : Set α), MonotoneOn f s
· 使用定理 `convex_univ`：convex_univ : Convex 𝕜 (Set.univ : Set E)
-/
theorem Monotone.quasiconcaveOn (hf : Monotone f) : QuasiconcaveOn 𝕜 univ f :=
  (hf.monotoneOn _).quasiconcaveOn convex_univ
/-
**Monotone.quasilinearOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Monotone.quasilinearOn (hf : Monotone f) : QuasilinearOn 𝕜 univ f
参数：hf : Monotone f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.quasiconvexOn`：Monotone.quasiconvexOn (hf : Monotone f) : Quasi
convexOn 𝕜 univ f
· 使用定理 `Monotone.quasiconcaveOn`：Monotone.quasiconcaveOn (hf : Monotone f) : Qua
siconcaveOn 𝕜 univ f
-/
theorem Monotone.quasilinearOn (hf : Monotone f) : QuasilinearOn 𝕜 univ f :=
  ⟨hf.quasiconvexOn, hf.quasiconcaveOn⟩
/-
**Antitone.quasiconvexOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Antitone.quasiconvexOn (hf : Antitone f) : QuasiconvexOn 𝕜 univ f
参数：hf : Antitone f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AntitoneOn.quasiconvexOn`：AntitoneOn.quasiconvexOn (hf : AntitoneOn f s)
 (hs : Convex 𝕜 s) : QuasiconvexOn 𝕜 s f
· 使用定理 `Antitone.antitoneOn`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [in
st_1 : Preorder β] {f : α → β},   Antitone f → ∀ (s : Set α), AntitoneOn f s
· 使用定理 `convex_univ`：convex_univ : Convex 𝕜 (Set.univ : Set E)
-/
theorem Antitone.quasiconvexOn (hf : Antitone f) : QuasiconvexOn 𝕜 univ f :=
  (hf.antitoneOn _).quasiconvexOn convex_univ
/-
**Antitone.quasiconcaveOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Antitone.quasiconcaveOn (hf : Antitone f) : QuasiconcaveOn 𝕜 univ f
参数：hf : Antitone f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AntitoneOn.quasiconcaveOn`：AntitoneOn.quasiconcaveOn (hf : AntitoneOn f 
s) (hs : Convex 𝕜 s) : QuasiconcaveOn 𝕜 s f
· 使用定理 `Antitone.antitoneOn`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [in
st_1 : Preorder β] {f : α → β},   Antitone f → ∀ (s : Set α), AntitoneOn f s
· 使用定理 `convex_univ`：convex_univ : Convex 𝕜 (Set.univ : Set E)
-/
theorem Antitone.quasiconcaveOn (hf : Antitone f) : QuasiconcaveOn 𝕜 univ f :=
  (hf.antitoneOn _).quasiconcaveOn convex_univ
/-
**Antitone.quasilinearOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Antitone.quasilinearOn (hf : Antitone f) : QuasilinearOn 𝕜 univ f
参数：hf : Antitone f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Antitone.quasiconvexOn`：Antitone.quasiconvexOn (hf : Antitone f) : Quasi
convexOn 𝕜 univ f
· 使用定理 `Antitone.quasiconcaveOn`：Antitone.quasiconcaveOn (hf : Antitone f) : Qua
siconcaveOn 𝕜 univ f
-/
theorem Antitone.quasilinearOn (hf : Antitone f) : QuasilinearOn 𝕜 univ f :=
  ⟨hf.quasiconvexOn, hf.quasiconcaveOn⟩

end LinearOrder
end OrderedSemiring

section LinearOrderedField

variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] {s : Set 𝕜} {f : 𝕜 → β}

/-
**QuasilinearOn.monotoneOn_or_antitoneOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：QuasilinearOn.monotoneOn_or_antitoneOn [LinearOrder β] (hf : QuasilinearOn
 𝕜 s f) : MonotoneOn f s ∨ AntitoneOn f s
参数：hf : QuasilinearOn 𝕜 s f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Convex.segment_subset`：Convex.segment_subset (h : Convex 𝕜 s) {x y : E} 
(hx : x in s) (hy : y in s) : [x -[𝕜] y] subseteq s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.sep_or`：sep_or : { x in s | p x ∨ q x } = { x in s | p x } union { x
 in s | q x }
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem QuasilinearOn.monotoneOn_or_antitoneOn [LinearOrder β] (hf : QuasilinearOn 𝕜 s f) :
    MonotoneOn f s ∨ AntitoneOn f s := by
  simp_rw [monotoneOn_or_antitoneOn_iff_uIcc, ← segment_eq_uIcc]
  rintro a ha b hb c _ h
  refine ⟨((hf.2 _).segment_subset ?_ ?_ h).2, ((hf.1 _).segment_subset ?_ ?_ h).2⟩ <;> simp [*]
/-
**quasilinearOn_iff_monotoneOn_or_antitoneOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：quasilinearOn_iff_monotoneOn_or_antitoneOn [LinearOrder β] (hs : Convex 𝕜 
s) : QuasilinearOn 𝕜 s f ↔ MonotoneOn f s ∨ AntitoneOn f s
参数：hs : Convex 𝕜 s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuasilinearOn.monotoneOn_or_antitoneOn`：QuasilinearOn.monotoneOn_or_anti
toneOn [LinearOrder β] (hf : QuasilinearOn 𝕜 s f) : MonotoneOn f s ∨ AntitoneOn 
f s
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `MonotoneOn.quasilinearOn`：MonotoneOn.quasilinearOn (hf : MonotoneOn f s)
 (hs : Convex 𝕜 s) : QuasilinearOn 𝕜 s f
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsOrderedModule.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `AntitoneOn.quasilinearOn`：AntitoneOn.quasilinearOn (hf : AntitoneOn f s)
 (hs : Convex 𝕜 s) : QuasilinearOn 𝕜 s f
-/
theorem quasilinearOn_iff_monotoneOn_or_antitoneOn [LinearOrder β]
    (hs : Convex 𝕜 s) : QuasilinearOn 𝕜 s f ↔ MonotoneOn f s ∨ AntitoneOn f s :=
  ⟨fun h => h.monotoneOn_or_antitoneOn, fun h =>
    h.elim (fun h => h.quasilinearOn hs) fun h => h.quasilinearOn hs⟩

end LinearOrderedField

