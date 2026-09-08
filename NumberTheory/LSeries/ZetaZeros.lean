/-
Copyright (c) 2026 Huanyu Zheng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Huanyu Zheng
-/
module

public import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# Discreteness of the zeros of the Riemann zeta function

We show that the zeros of the Riemann zeta function form a discrete subset of `ℂ`,
so that in particular any compact subset of `ℂ` contains only finitely many zeros.

## Main declarations

* `riemannZetaZeros`: The zeros of Riemann zeta function.

## Main results

* `isClosed_riemannZetaZeros`: `riemannZetaZeros` is closed.

* `isDiscrete_riemannZetaZeros`: `riemannZetaZeros` is discrete.

* `IsCompact.inter_riemannZetaZeros_finite`: for any compact set `S : Set ℂ`, the intersection
  `S ∩ riemannZetaZeros` is finite.
-/

@[expose] public section

/-- The zeros of Riemann's ζ-function. -/
-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- See https://github.com/leanprover/lean4/issues/14084.
/-
**riemannZetaZeros** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：riemannZetaZeros : Set Complex
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def riemannZetaZeros : Set ℂ := riemannZeta ⁻¹' {0}
/-
**mem_riemannZetaZeros** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mem_riemannZetaZeros {z : Complex} : z in riemannZetaZeros ↔ riemannZeta z
 = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_riemannZetaZeros {z : ℂ} :
    z ∈ riemannZetaZeros ↔ riemannZeta z = 0 := .rfl

/-- The complement of the zero set of `riemannZeta` is codiscrete within `{1}ᶜ`. -/
/-
**riemannZetaZeros_codiscreteWithin_compl_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The complement of the zero set of `riemannZeta` is codiscrete within `{1}ᶜ`.
-/
private lemma riemannZetaZeros_codiscreteWithin_compl_one :
    riemannZetaZerosᶜ ∈ Filter.codiscreteWithin {1}ᶜ := by
  refine analyticOn_riemannZeta.preimage_zero_mem_codiscreteWithin (x := 2) ?_ (by simp) ?_
  · exact riemannZeta_ne_zero_of_one_le_re Nat.one_le_ofNat
  · exact isConnected_compl_singleton_of_one_lt_rank (by simp) 1

/-- The complement of the zero set of `riemannZeta` is codiscrete. -/
/-
**compl_riemannZetaZeros_mem_codiscrete** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The complement of the zero set of `riemannZeta` is codiscrete.
-/
private lemma compl_riemannZetaZeros_mem_codiscrete :
    riemannZetaZerosᶜ ∈ Filter.codiscrete ℂ := by
  have := riemannZetaZeros_codiscreteWithin_compl_one
  simp only [mem_codiscreteWithin, Set.mem_compl_iff, Set.mem_singleton_iff, sdiff_compl,
    Set.inf_eq_inter, Filter.disjoint_principal_right, mem_codiscrete, compl_compl] at this ⊢
  intro x
  rcases eq_or_ne x 1 with rfl | hx
  · exact riemannZeta_eventually_ne_zero_nhds_one.filter_mono nhdsWithin_le_nhds
  · exact Filter.mem_of_superset (this x hx)
      (by grind [riemannZeta_one_ne_zero, mem_riemannZetaZeros])
/-
**isClosed_riemannZetaZeros** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isClosed_riemannZetaZeros : IsClosed riemannZetaZeros
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `mem_codiscrete'`：mem_codiscrete' {S : Set X} : S in codiscrete X ↔ IsOpe
n S ∧ IsDiscrete Sᶜ
· 使用定理 `_private.Mathlib.NumberTheory.LSeries.ZetaZeros.0.compl_riemannZetaZeros
_mem_codiscrete`：riemannZetaZerosᶜ ∈ Filter.codiscrete ℂ
-/
lemma isClosed_riemannZetaZeros : IsClosed riemannZetaZeros := by
  simpa using (mem_codiscrete'.mp compl_riemannZetaZeros_mem_codiscrete).1
/-
**isDiscrete_riemannZetaZeros** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isDiscrete_riemannZetaZeros : IsDiscrete riemannZetaZeros
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `mem_codiscrete'`：mem_codiscrete' {S : Set X} : S in codiscrete X ↔ IsOpe
n S ∧ IsDiscrete Sᶜ
· 使用定理 `_private.Mathlib.NumberTheory.LSeries.ZetaZeros.0.compl_riemannZetaZeros
_mem_codiscrete`：riemannZetaZerosᶜ ∈ Filter.codiscrete ℂ
-/
lemma isDiscrete_riemannZetaZeros : IsDiscrete riemannZetaZeros := by
  simpa using (mem_codiscrete'.mp compl_riemannZetaZeros_mem_codiscrete).2

/-- Any compact subset of `ℂ` contains only finitely many zeros of the Riemann zeta function. -/
/-
**IsCompact.inter_riemannZetaZeros_finite** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsCompact.inter_riemannZetaZeros_finite {S : Set Complex} (hS : IsCompact 
S) : (S inter riemannZetaZeros).Finite
参数：hS : IsCompact S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.finite`：IsCompact.finite (hs : IsCompact s) (hs' : IsDiscrete 
s) : s.Finite
· 使用定理 `IsCompact.inter_right`：IsCompact.inter_right (hs : IsCompact s) (ht : Is
Closed t) : IsCompact (s inter t)
· 使用引理 `isClosed_riemannZetaZeros`：isClosed_riemannZetaZeros : IsClosed riemannZ
etaZeros
· 使用引理 `IsDiscrete.mono`：IsDiscrete.mono {t : Set X} (hs : IsDiscrete s) (hst : 
t subseteq s) : IsDiscrete t
· 使用引理 `isDiscrete_riemannZetaZeros`：isDiscrete_riemannZetaZeros : IsDiscrete ri
emannZetaZeros
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t

--- 原说明 ---
Any compact subset of `ℂ` contains only finitely many zeros of the Riemann zeta 
function.
-/
lemma IsCompact.inter_riemannZetaZeros_finite {S : Set ℂ} (hS : IsCompact S) :
    (S ∩ riemannZetaZeros).Finite := by
  apply (hS.inter_right isClosed_riemannZetaZeros).finite
  exact isDiscrete_riemannZetaZeros.mono Set.inter_subset_right

open Filter in
/-
**tendsto_riemannZeta_cofinite_cocompact** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：tendsto_riemannZeta_cofinite_cocompact : Tendsto ((↑) : riemannZetaZeros -
> Complex) cofinite (cocompact Complex)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsClosed.tendsto_coe_cofinite_of_isDiscrete`：IsClosed.tendsto_coe_cofini
te_of_isDiscrete {s : Set X} (hs : IsClosed s) (hs' : IsDiscrete s) : Tendsto ((
↑) : s -> X) cofinite (cocompact …
· 使用引理 `isClosed_riemannZetaZeros`：isClosed_riemannZetaZeros : IsClosed riemannZ
etaZeros
· 使用引理 `isDiscrete_riemannZetaZeros`：isDiscrete_riemannZetaZeros : IsDiscrete ri
emannZetaZeros
-/
lemma tendsto_riemannZeta_cofinite_cocompact :
    Tendsto ((↑) : riemannZetaZeros → ℂ) cofinite (cocompact ℂ) :=
  isClosed_riemannZetaZeros.tendsto_coe_cofinite_of_isDiscrete isDiscrete_riemannZetaZeros

end

