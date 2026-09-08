/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Data.Finsupp.Single

/-!
# Building finitely supported functions off finsets

This file defines `Finsupp.indicator` to help create finsupps from finsets.

## Main declarations

* `Finsupp.indicator`: Turns a map from a `Finset` into a `Finsupp` from the entire type.
-/

@[expose] public section


noncomputable section

open Finset Function

variable {ι α : Type*}

namespace Finsupp

variable [Zero α] {s t : Finset ι} (f : ∀ i ∈ s, α) {i : ι}

/-- Create an element of `ι →₀ α` from a finset `s` and a function `f` defined on this finset. -/
/-
**Finsupp.indicator** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp`。
形式化陈述：indicator (s : Finset ι) (f : forall i in s, α) : ι ->₀ α where toFun i
参数：s : Finset ι；f : forall i in s, α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Create an element of `ι →₀ α` from a finset `s` and a function `f` defined on th
is finset.
-/
def indicator (s : Finset ι) (f : ∀ i ∈ s, α) : ι →₀ α where
  toFun i :=
    haveI := Classical.decEq ι
    if H : i ∈ s then f i H else 0
  support :=
    haveI := Classical.decEq α
    ({i | f i.1 i.2 ≠ 0} : Finset s).map (Embedding.subtype _)
  mem_support_toFun i := by
    simp
/-
**Finsupp.indicator_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：indicator_of_mem (hi : i in s) (f : forall i in s, α) : indicator s f i = 
f i hi
参数：hi : i in s；f : forall i in s, α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
-/
theorem indicator_of_mem (hi : i ∈ s) (f : ∀ i ∈ s, α) : indicator s f i = f i hi :=
  @dif_pos _ (id _) hi _ _ _
/-
**Finsupp.indicator_of_notMem** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：indicator_of_notMem (hi : i ∉ s) (f : forall i in s, α) : indicator s f i 
= 0
参数：hi : i ∉ s；f : forall i in s, α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
theorem indicator_of_notMem (hi : i ∉ s) (f : ∀ i ∈ s, α) : indicator s f i = 0 :=
  @dif_neg _ (id _) hi _ _ _

variable (s i)

@[simp]
/-
**Finsupp.indicator_apply** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：indicator_apply [DecidableEq ι] : indicator s f i = if hi : i in s then f 
i hi else 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `instSubsingletonDecidable`：∀ (p : Prop), Subsingleton (Decidable p)
-/
theorem indicator_apply [DecidableEq ι] : indicator s f i = if hi : i ∈ s then f i hi else 0 := by
  simp only [indicator, ne_eq, coe_mk]
  congr
/-
**Finsupp.indicator_injective** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：indicator_injective : Injective fun f : forall i in s, α => indicator s f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finsupp.indicator_of_mem`：indicator_of_mem (hi : i in s) (f : forall i i
n s, α) : indicator s f i = f i hi
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
-/
theorem indicator_injective : Injective fun f : ∀ i ∈ s, α => indicator s f := by
  intro a b h
  ext i hi
  rw [← indicator_of_mem hi a, ← indicator_of_mem hi b]
  exact DFunLike.congr_fun h i
/-
**Finsupp.support_indicator_subset** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：support_indicator_subset : (indicator s f).support subseteq s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.mem_support_iff`：mem_support_iff {f : α ->₀ M} : forall {a : α},
 a in f.support ↔ f a != 0
· 使用定理 `Finsupp.indicator_of_notMem`：indicator_of_notMem (hi : i ∉ s) (f : foral
l i in s, α) : indicator s f i = 0
-/
theorem support_indicator_subset : (indicator s f).support ⊆ s := by
  intro i hi
  rw [mem_support_iff] at hi
  by_contra h
  exact hi (indicator_of_notMem h _)
/-
**Finsupp.indicator_singleton** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：indicator_singleton (a : ι) (f : forall j in ({a} : Finset ι), α) : indica
tor {a} f = single a (f a (mem_singleton_self a))
参数：a : ι；f : forall j in ({a} : Finset ι), α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `Finset.mem_singleton_self`：mem_singleton_self (a : α) : a in ({a} : Fins
et α)
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finsupp.indicator_apply`：indicator_apply [DecidableEq ι] : indicator s f
 i = if hi : i in s then f i hi else 0
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `Finsupp.single_apply`：single_apply [Decidable (a = a')] : single a b a' 
= if a = a' then b else 0
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
lemma indicator_singleton (a : ι) (f : ∀ j ∈ ({a} : Finset ι), α) :
    indicator {a} f = single a (f a (mem_singleton_self a)) := by
  classical
  ext j
  simp only [single_apply, indicator_apply, mem_singleton, @eq_comm _ a j]
  split_ifs with h <;> simp [h]

@[deprecated indicator_singleton (since := "2026-04-27")]
/-
**Finsupp.single_eq_indicator** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：single_eq_indicator (b : α) : single i b = indicator {i} (fun _ _ => b)
参数：b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Finsupp.indicator_singleton`：indicator_singleton (a : ι) (f : forall j i
n ({a} : Finset ι), α) : indicator {a} f = single a (f a (mem_singleton_self a))
-/
lemma single_eq_indicator (b : α) : single i b = indicator {i} (fun _ _ => b) :=
  (indicator_singleton i (fun _ _ => b)).symm
/-
**Finsupp.indicator_eq_set_indicator** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：indicator_eq_set_indicator (s : Finset ι) (g : ι -> α) : ⇑(indicator s (fu
n i _ => g i)) = Set.indicator ↑s g
参数：s : Finset ι；g : ι -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.indicator_apply`：indicator_apply [DecidableEq ι] : indicator s f
 i = if hi : i in s then f i hi else 0
· 使用定理 `Set.indicator_apply`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] (s 
: Set α) (f : α → M) (a : α) [inst_1 : Decidable (a ∈ s)],   s.indicator f a = i
f a ∈ s t…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem indicator_eq_set_indicator (s : Finset ι) (g : ι → α) :
    ⇑(indicator s (fun i _ => g i)) = Set.indicator ↑s g := by
  classical
  ext i
  simp [indicator_apply, Set.indicator_apply]
/-
**Finsupp.indicator_indicator** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：indicator_indicator [DecidableEq ι] : indicator t (fun i _ => indicator s 
f i) = indicator (s inter t) (fun i hi => f i (Finset.mem_of_mem_inter_left hi))
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem indicator_indicator [DecidableEq ι] :
    indicator t (fun i _ ↦ indicator s f i) =
      indicator (s ∩ t) (fun i hi ↦ f i (Finset.mem_of_mem_inter_left hi)) := by
  grind [indicator_apply]
/-
**Finsupp.eq_indicator_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：eq_indicator_iff {g : ι -> α} : g = indicator s f ↔ g.support subseteq s ∧
 forall ⦃i⦄ (hi : i in s), f i hi = g i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.subset_def`：subset_def : (s subseteq t) = forall x, x in s -> x in t
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Finsupp.indicator_apply`：indicator_apply [DecidableEq ι] : indicator s f
 i = if hi : i in s then f i hi else 0
-/
theorem eq_indicator_iff {g : ι → α} :
    g = indicator s f ↔ g.support ⊆ s ∧ ∀ ⦃i⦄ (hi : i ∈ s), f i hi = g i := by
  classical
  suffices g.support ⊆ s ∧ (∀ i (hi : i ∈ s), f i hi = g i) ↔
      (∀ i, if hi : i ∈ s then f i hi = g i else g i = 0) by
    simp only [this, funext_iff, indicator_apply]
    grind
  rw [Set.subset_def, and_comm]
  have : (∀ (i : ι), if hi : i ∈ s then f i hi = g i else g i = 0) ↔
      ((∀ (i : ι) (hi : i ∈ s), f i hi = g i) ∧ ∀ i (hi : i ∉ s), g i = 0) := by grind
  simp [this, not_imp_comm]
/-
**Finsupp.eq_indicator_self_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：eq_indicator_self_iff {d : ι ->₀ α} : (d = indicator s fun i _ => d i) ↔ d
.support subseteq s
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eq_indicator_self_iff {d : ι →₀ α} : (d = indicator s fun i _ ↦ d i) ↔ d.support ⊆ s := by
  grind [indicator]

end Finsupp

