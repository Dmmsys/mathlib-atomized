/-
Copyright (c) 2025 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Logic.Embedding.Basic

/-!
# Embedding a finitely supported function into a sigma type summand

This file provides `Finsupp.embSigma`, which embeds a finitely supported function `ι k →₀ M`
into the corresponding summand of `(Σ k, ι k) →₀ M`.

## Main declarations

* `Finsupp.embSigma`: Embed `ι k →₀ M` into `(Σ k, ι k) →₀ M` for a specific `k`.

## Implementation notes

This is a special case of `Finsupp.embDomain` using `Function.Embedding.sigmaMk`.
-/

@[expose] public section

noncomputable section

open Function

variable {κ : Type*} {ι : κ → Type*} {M : Type*}

namespace Finsupp

section EmbSigma

variable [Zero M]

/-- Embed a finitely supported function `f : ι k →₀ M` into the `k`-th summand
of the sigma type `(Σ k, ι k) →₀ M`.

This is `Finsupp.embDomain` specialized to `Function.Embedding.sigmaMk k`. -/
/-
**Finsupp.embSigma** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp`。
形式化陈述：embSigma {k : κ} (f : ι k ->₀ M) : (Σ k, ι k) ->₀ M
参数：f : ι k ->₀ M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Embed a finitely supported function `f : ι k →₀ M` into the `k`-th summand
of the sigma type `(Σ k, ι k) →₀ M`.

This is `Finsupp.embDomain` specialized to `Function.Embedding.sigmaMk k`.
-/
def embSigma {k : κ} (f : ι k →₀ M) : (Σ k, ι k) →₀ M :=
  embDomain (Embedding.sigmaMk k) f

@[grind =]
/-
**Finsupp.embSigma_apply** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：embSigma_apply [DecidableEq κ] {k : κ} (f : ι k ->₀ M) (i : Σ k, ι k) : em
bSigma f i = if h : i.1 = k then f (h ▸ i.2) else 0
参数：f : ι k ->₀ M；i : Σ k, ι k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Finsupp.embDomain_apply_self`：embDomain_apply_self (f : α ↪ β) (v : α ->
₀ M) (a : α) : embDomain f v (f a) = v a
· 使用定理 `sigma_mk_injective`：∀ {α : Type u_1} {β : α → Type u_4} {i : α}, Functio
n.Injective (Sigma.mk i)
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Finsupp.embDomain_of_notMem_range`：embDomain_of_notMem_range (f : α ↪ β)
 (v : α ->₀ M) (a : β) (h : a ∉ Set.range f) : embDomain f v a = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.range_sigmaMk`：range_sigmaMk (i : ι) : range (Sigma.mk i : α i -> Si
gma α) = Sigma.fst ⁻¹' {i}
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem embSigma_apply [DecidableEq κ] {k : κ} (f : ι k →₀ M) (i : Σ k, ι k) :
    embSigma f i = if h : i.1 = k then f (h ▸ i.2) else 0 := by
  rcases i with ⟨k, i⟩
  split_ifs with h
  · subst h
    simp only [embSigma, Embedding.sigmaMk]
    apply embDomain_apply_self
  · simp only [embSigma, Embedding.sigmaMk]
    rw [embDomain_of_notMem_range]
    simp_all

@[simp]
/-
**Finsupp.embSigma_apply_self** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：embSigma_apply_self {k : κ} (f : ι k ->₀ M) (i : ι k) : embSigma f ⟨k, i⟩ 
= f i
参数：f : ι k ->₀ M；i : ι k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.embSigma.eq_1`：∀ {κ : Type u_1} {ι : κ → Type u_2} {M : Type u_3
} [inst : Zero M] {k : κ} (f : ι k →₀ M),   f.embSigma = Finsupp.embDomain (Func
tion.Embedd…
· 使用定理 `Finsupp.embDomain_apply_self`：embDomain_apply_self (f : α ↪ β) (v : α ->
₀ M) (a : α) : embDomain f v (f a) = v a
-/
theorem embSigma_apply_self {k : κ} (f : ι k →₀ M) (i : ι k) :
    embSigma f ⟨k, i⟩ = f i := by
  rw [embSigma]
  exact embDomain_apply_self (Embedding.sigmaMk k) f i

/-- Values of `embSigma f` at indices outside the `k`-th summand are zero. -/
/-
**Finsupp.embSigma_apply_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：embSigma_apply_of_ne {k k' : κ} (f : ι k ->₀ M) (hk : k' != k) (i : ι k') 
: embSigma f ⟨k', i⟩ = 0
参数：f : ι k ->₀ M；hk : k' != k；i : ι k'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.embDomain_of_notMem_range`：embDomain_of_notMem_range (f : α ↪ β)
 (v : α ->₀ M) (a : β) (h : a ∉ Set.range f) : embDomain f v a = 0

--- 原说明 ---
Values of `embSigma f` at indices outside the `k`-th summand are zero.
-/
theorem embSigma_apply_of_ne {k k' : κ} (f : ι k →₀ M) (hk : k' ≠ k) (i : ι k') :
    embSigma f ⟨k', i⟩ = 0 := by
  apply embDomain_of_notMem_range
  grind

@[simp, grind =]
/-
**Finsupp.support_embSigma** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：support_embSigma {k : κ} (f : ι k ->₀ M) : (embSigma f).support = f.suppor
t.map (Embedding.sigmaMk k)
参数：f : ι k ->₀ M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem support_embSigma {k : κ} (f : ι k →₀ M) :
    (embSigma f).support = f.support.map (Embedding.sigmaMk k) := by
  simp [embSigma]

@[simp]
/-
**Finsupp.embSigma_zero** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：embSigma_zero {k : κ} : embSigma (0 : ι k ->₀ M) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem embSigma_zero {k : κ} : embSigma (0 : ι k →₀ M) = 0 := by
  simp [embSigma]

@[simp]
/-
**Finsupp.embSigma_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：embSigma_eq_zero {k : κ} {f : ι k ->₀ M} : embSigma f = 0 ↔ f = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem embSigma_eq_zero {k : κ} {f : ι k →₀ M} :
    embSigma f = 0 ↔ f = 0 := by
  simp [embSigma]
/-
**Finsupp.embSigma_injective** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：embSigma_injective {k : κ} : Injective (embSigma : (ι k ->₀ M) -> (Σ k, ι 
k) ->₀ M)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finsupp.embSigma_apply_self`：embSigma_apply_self {k : κ} (f : ι k ->₀ M)
 (i : ι k) : embSigma f ⟨k, i⟩ = f i
-/
theorem embSigma_injective {k : κ} :
    Injective (embSigma : (ι k →₀ M) → (Σ k, ι k) →₀ M) := by
  intro f g h
  ext i
  have := congr_fun (congrArg (⇑) h) ⟨k, i⟩
  simpa using this

@[simp]
/-
**Finsupp.embSigma_inj** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：embSigma_inj {k : κ} {f g : ι k ->₀ M} : embSigma f = embSigma g ↔ f = g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Finsupp.embSigma_injective`：embSigma_injective {k : κ} : Injective (embS
igma : (ι k ->₀ M) -> (Σ k, ι k) ->₀ M)
-/
theorem embSigma_inj {k : κ} {f g : ι k →₀ M} :
    embSigma f = embSigma g ↔ f = g :=
  embSigma_injective.eq_iff

end EmbSigma

section EmbSigmaAdd

variable [AddMonoid M]

/-
**Finsupp.embSigma_add** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：embSigma_add {k : κ} (f g : ι k ->₀ M) : embSigma (f + g) = embSigma f + e
mbSigma g
参数：f g : ι k ->₀ M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.embSigma_apply_self`：embSigma_apply_self {k : κ} (f : ι k ->₀ M)
 (i : ι k) : embSigma f ⟨k, i⟩ = f i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finsupp.embSigma_apply_of_ne`：embSigma_apply_of_ne {k k' : κ} (f : ι k -
>₀ M) (hk : k' != k) (i : ι k') : embSigma f ⟨k', i⟩ = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
theorem embSigma_add {k : κ} (f g : ι k →₀ M) :
    embSigma (f + g) = embSigma f + embSigma g := by
  ext ⟨k', i⟩
  by_cases hk : k' = k
  · subst hk
    simp
  · simp [embSigma_apply_of_ne _ hk]

-- TODO: `embSigma` could be bundled as e.g. an additive or linear map, when needed.

end EmbSigmaAdd

section EmbSigmaSingle

@[simp]
/-
**Finsupp.embSigma_single** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：embSigma_single [Zero M] {k : κ} (i : ι k) (m : M) : embSigma (single i m)
 = single ⟨k, i⟩ m
参数：i : ι k；m : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem embSigma_single [Zero M] {k : κ} (i : ι k) (m : M) :
    embSigma (single i m) = single ⟨k, i⟩ m := by
  classical
  grind

end EmbSigmaSingle

section Split

variable [Zero M]

/-- `embSigma` is a left inverse to `split` at the same index. -/
@[simp]
/-
**Finsupp.split_embSigma_self** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：split_embSigma_self {k : κ} (f : ι k ->₀ M) : split (embSigma f) k = f
参数：f : ι k ->₀ M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.split_apply`：split_apply (i : ι) (x : αs i) : split l i x = l ⟨i
, x⟩
· 使用定理 `Finsupp.embSigma_apply_self`：embSigma_apply_self {k : κ} (f : ι k ->₀ M)
 (i : ι k) : embSigma f ⟨k, i⟩ = f i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
`embSigma` is a left inverse to `split` at the same index.
-/
theorem split_embSigma_self {k : κ} (f : ι k →₀ M) :
    split (embSigma f) k = f := by
  ext i
  simp [split_apply]

/-- `split` returns zero at indices different from where `embSigma` embeds. -/
/-
**Finsupp.split_embSigma_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：split_embSigma_of_ne {k k' : κ} (f : ι k ->₀ M) (hk : k' != k) : split (em
bSigma f) k' = 0
参数：f : ι k ->₀ M；hk : k' != k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.split_apply`：split_apply (i : ι) (x : αs i) : split l i x = l ⟨i
, x⟩
· 使用定理 `Finsupp.embSigma_apply_of_ne`：embSigma_apply_of_ne {k k' : κ} (f : ι k -
>₀ M) (hk : k' != k) (i : ι k') : embSigma f ⟨k', i⟩ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
`split` returns zero at indices different from where `embSigma` embeds.
-/
theorem split_embSigma_of_ne {k k' : κ} (f : ι k →₀ M) (hk : k' ≠ k) :
    split (embSigma f) k' = 0 := by
  ext i
  simp [split_apply, embSigma_apply_of_ne _ hk]

end Split

end Finsupp

