/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Group.Submonoid.BigOperators
public import Mathlib.Data.Finsupp.Ext
public import Mathlib.Data.Finsupp.Indicator

/-!
# Big operators for finsupps

This file contains theorems relevant to big operators in finitely supported functions.
-/

@[expose] public section

assert_not_exists Field

noncomputable section

open Finset Function

variable {α ι γ A B C : Type*} [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C]
variable {t : ι → A → C}
variable {s : Finset α} {f : α → ι →₀ A} (i : ι)
variable (g : ι →₀ A) (k : ι → A → γ → B) (x : γ)
variable {β M M' N P G H R S : Type*}

namespace Finsupp

/-!
### Declarations about `Finsupp.sum` and `Finsupp.prod`

In most of this section, the domain `β` is assumed to be an `AddMonoid`.
-/


section SumProd

/-- `prod f g` is the product of `g a (f a)` over the support of `f`. -/
@[to_additive /-- `sum f g` is the sum of `g a (f a)` over the support of `f`. -/]
/-
**Finsupp.prod** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp`。
形式化陈述：prod [Zero M] [CommMonoid N] (f : α ->₀ M) (g : α -> M -> N) : N
参数：f : α ->₀ M；g : α -> M -> N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`prod f g` is the product of `g a (f a)` over the support of `f`.
-/
def prod [Zero M] [CommMonoid N] (f : α →₀ M) (g : α → M → N) : N :=
  ∏ a ∈ f.support, g a (f a)

variable [Zero M] [Zero M'] [CommMonoid N]

@[to_additive (attr := simp)]
/-
**Finsupp.prod_fun_one** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：prod_fun_one (f : α ->₀ M) : f.prod (fun _ _ => (1 : N)) = 1
参数：f : α ->₀ M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.prod_const_one`：prod_const_one : (∏ _x in s, (1 : M)) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma prod_fun_one (f : α →₀ M) : f.prod (fun _ _ ↦ (1 : N)) = 1 := by simp [prod]

@[to_additive]
/-
**Finsupp.prod_of_support_subset** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：prod_of_support_subset (f : α ->₀ M) {s : Finset α} (hs : f.support subset
eq s) (g : α -> M -> N) (h : forall i in s, g i 0 = 1) : f.prod g = ∏ x in s, g 
x (f x)
参数：f : α ->₀ M；hs : f.support subseteq s；g : α -> M -> N；h : forall i in s, g i 
0 = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.prod_subset`：prod_subset (h : s₁ subseteq s₂) (hf : forall x in s
₂, x ∉ s₁ -> f x = 1) : ∏ x in s₁, f x = ∏ x in s₂, f x
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finsupp.notMem_support_iff`：notMem_support_iff {f : α ->₀ M} {a} : a ∉ f
.support ↔ f a = 0
-/
theorem prod_of_support_subset (f : α →₀ M) {s : Finset α} (hs : f.support ⊆ s) (g : α → M → N)
    (h : ∀ i ∈ s, g i 0 = 1) : f.prod g = ∏ x ∈ s, g x (f x) := by
  refine Finset.prod_subset hs fun x hxs hx => h x hxs ▸ (congr_arg (g x) ?_)
  exact notMem_support_iff.1 hx

@[to_additive]
/-
**Finsupp.prod_fintype** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：prod_fintype [Fintype α] (f : α ->₀ M) (g : α -> M -> N) (h : forall i, g 
i 0 = 1) : f.prod g = ∏ i, g i (f i)
参数：f : α ->₀ M；g : α -> M -> N；h : forall i, g i 0 = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.prod_of_support_subset`：prod_of_support_subset (f : α ->₀ M) {s 
: Finset α} (hs : f.support subseteq s) (g : α -> M -> N) (h : forall i in s, g 
i 0 = 1) : f.prod g …
· 使用定理 `Finset.subset_univ`：subset_univ (s : Finset α) : s subseteq univ
-/
theorem prod_fintype [Fintype α] (f : α →₀ M) (g : α → M → N) (h : ∀ i, g i 0 = 1) :
    f.prod g = ∏ i, g i (f i) :=
  f.prod_of_support_subset (subset_univ _) g fun x _ => h x

@[to_additive (attr := simp)]
/-
**Finsupp.prod_single_index** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：prod_single_index {a : α} {b : M} {h : α -> M -> N} (h_zero : h a 0 = 1) :
 (single a b).prod h = h a b
参数：h_zero : h a 0 = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.prod_of_support_subset`：prod_of_support_subset (f : α ->₀ M) {s 
: Finset α} (hs : f.support subseteq s) (g : α -> M -> N) (h : forall i in s, g 
i 0 = 1) : f.prod g …
· 使用定理 `Finsupp.support_single_subset`：support_single_subset : (single a b).supp
ort subseteq {a}
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_singleton`：mem_singleton {a b : α} : b in ({a} : Finset α) ↔ 
b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_singleton`：prod_singleton (f : ι -> M) (a : ι) : ∏ x in sing
leton a, f x = f a
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_single_index {a : α} {b : M} {h : α → M → N} (h_zero : h a 0 = 1) :
    (single a b).prod h = h a b :=
  calc
    (single a b).prod h = ∏ x ∈ {a}, h x (single a b x) :=
      prod_of_support_subset _ support_single_subset h fun _ hx =>
        (mem_singleton.1 hx).symm ▸ h_zero
    _ = h a b := by simp

@[to_additive]
/-
**Finsupp.prod_mapRange_index** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：prod_mapRange_index {f : M -> M'} {hf : f 0 = 0} {g : α ->₀ M} {h : α -> M
' -> N} (h0 : forall a, h a 0 = 1) : (mapRange f hf g).prod h = g.prod fun a b =
> h a (f b)
参数：h0 : forall a, h a 0 = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.prod_subset`：prod_subset (h : s₁ subseteq s₂) (hf : forall x in s
₂, x ∉ s₁ -> f x = 1) : ∏ x in s₁, f x = ∏ x in s₂, f x
· 使用定理 `Finsupp.support_mapRange`：support_mapRange {f : M -> N} {hf : f 0 = 0} {
g : α ->₀ M} : (mapRange f hf g).support subseteq g.support
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finsupp.notMem_support_iff`：notMem_support_iff {f : α ->₀ M} {a} : a ∉ f
.support ↔ f a = 0
-/
theorem prod_mapRange_index {f : M → M'} {hf : f 0 = 0} {g : α →₀ M} {h : α → M' → N}
    (h0 : ∀ a, h a 0 = 1) : (mapRange f hf g).prod h = g.prod fun a b => h a (f b) :=
  Finset.prod_subset support_mapRange fun _ _ H => by rw [notMem_support_iff.1 H, h0]

@[to_additive (attr := simp)]
/-
**Finsupp.prod_onFinset** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：prod_onFinset (s : Finset α) (f : α -> M) (hf) (g : α -> M -> N) (hg : for
all i in s, g i 0 = 1) : (onFinset s f hf).prod g = ∏ a in s, g a (f a)
参数：s : Finset α；f : α -> M；hf；g : α -> M -> N；hg : forall i in s, g i 0 = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.prod_of_support_subset`：prod_of_support_subset (f : α ->₀ M) {s 
: Finset α} (hs : f.support subseteq s) (g : α -> M -> N) (h : forall i in s, g 
i 0 = 1) : f.prod g …
· 使用定理 `Finsupp.support_onFinset_subset`：support_onFinset_subset {s : Finset α} 
{f : α -> M} {hf} : (onFinset s f hf).support subseteq s
-/
lemma prod_onFinset (s : Finset α) (f : α → M) (hf) (g : α → M → N) (hg : ∀ i ∈ s, g i 0 = 1) :
    (onFinset s f hf).prod g = ∏ a ∈ s, g a (f a) :=
  prod_of_support_subset _ support_onFinset_subset _ hg

@[to_additive (attr := simp)]
/-
**Finsupp.prod_zero_index** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：prod_zero_index {h : α -> M -> N} : (0 : α ->₀ M).prod h = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prod_zero_index {h : α → M → N} : (0 : α →₀ M).prod h = 1 :=
  rfl

@[to_additive]
/-
**Finsupp.prod_comm** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：prod_comm (f : α ->₀ M) (g : β ->₀ M') (h : α -> M -> β -> M' -> N) : (f.p
rod fun x v => g.prod fun x' v' => h x v x' v') = g.prod fun x' v' => f.prod fun
 x v => h x v x' v'
参数：f : α ->₀ M；g : β ->₀ M'；h : α -> M -> β -> M' -> N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.prod_comm`：prod_comm {s : Finset γ} {t : Finset α} {f : γ -> α ->
 β} : (∏ x in s, ∏ y in t, f x y) = ∏ y in t, ∏ x in s, f x y
-/
theorem prod_comm (f : α →₀ M) (g : β →₀ M') (h : α → M → β → M' → N) :
    (f.prod fun x v => g.prod fun x' v' => h x v x' v') =
      g.prod fun x' v' => f.prod fun x v => h x v x' v' :=
  Finset.prod_comm

@[to_additive]
/-
**Finsupp.prod_finsetProd_comm** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：prod_finsetProd_comm {s : Finset β} (f : α ->₀ M) (h : α -> M -> β -> N) :
 (f.prod fun a m => ∏ b in s, h a m b) = ∏ b in s, f.prod fun a m => h a m b
参数：f : α ->₀ M；h : α -> M -> β -> N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.prod_comm`：prod_comm {s : Finset γ} {t : Finset α} {f : γ -> α ->
 β} : (∏ x in s, ∏ y in t, f x y) = ∏ y in t, ∏ x in s, f x y
-/
theorem prod_finsetProd_comm {s : Finset β} (f : α →₀ M) (h : α → M → β → N) :
    (f.prod fun a m => ∏ b ∈ s, h a m b) = ∏ b ∈ s, f.prod fun a m => h a m b := Finset.prod_comm

@[to_additive (attr := simp)]
/-
**Finsupp.prod_ite_eq** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：prod_ite_eq [DecidableEq α] (f : α ->₀ M) (a : α) (b : α -> M -> N) : (f.p
rod fun x v => ite (a = x) (b x v) 1) = ite (a in f.support) (b a (f a)) 1
参数：f : α ->₀ M；a : α；b : α -> M -> N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_ite_eq`：prod_ite_eq [DecidableEq ι] (s : Finset ι) (a : ι) (
b : ι -> M) : (∏ x in s, ite (a = x) (b x) 1) = ite (a in s) (b a) 1
-/
theorem prod_ite_eq [DecidableEq α] (f : α →₀ M) (a : α) (b : α → M → N) :
    (f.prod fun x v => ite (a = x) (b x v) 1) = ite (a ∈ f.support) (b a (f a)) 1 := by
  dsimp [Finsupp.prod]
  rw [f.support.prod_ite_eq]
/-
**Finsupp.sum_ite_self_eq** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：sum_ite_self_eq [DecidableEq α] {N : Type*} [AddCommMonoid N] (f : α ->₀ N
) (a : α) : (f.sum fun x v => ite (a = x) v 0) = f a
参数：f : α ->₀ N；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.sum_ite_eq`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} [ins
t : Zero M] [inst_1 : AddCommMonoid N] [inst_2 : DecidableEq α]   (f : α →₀ M) (
a : α) (…
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem sum_ite_self_eq [DecidableEq α] {N : Type*} [AddCommMonoid N] (f : α →₀ N) (a : α) :
    (f.sum fun x v => ite (a = x) v 0) = f a := by
  simp_all

/--
The left-hand side of `sum_ite_self_eq` simplifies; this is the variant that is useful for `simp`.
-/
@[simp]
/-
**Finsupp.if_mem_support** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：if_mem_support [DecidableEq α] {N : Type*} [Zero N] (f : α ->₀ N) (a : α) 
: (if a in f.support then f a else 0) = f a
参数：f : α ->₀ N；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
The left-hand side of `sum_ite_self_eq` simplifies; this is the variant that is 
useful for `simp`.
-/
theorem if_mem_support [DecidableEq α] {N : Type*} [Zero N] (f : α →₀ N) (a : α) :
    (if a ∈ f.support then f a else 0) = f a := by
  simp only [mem_support_iff, ne_eq, ite_eq_left_iff, not_not]
  exact fun h ↦ h.symm

/-- A restatement of `prod_ite_eq` with the equality test reversed. -/
@[to_additive (attr := simp) /-- A restatement of `sum_ite_eq` with the equality test reversed. -/]
/-
**Finsupp.prod_ite_eq'** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：prod_ite_eq' [DecidableEq α] (f : α ->₀ M) (a : α) (b : α -> M -> N) : (f.
prod fun x v => ite (x = a) (b x v) 1) = ite (a in f.support) (b a (f a)) 1
参数：f : α ->₀ M；a : α；b : α -> M -> N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_ite_eq'`：prod_ite_eq' [DecidableEq ι] (s : Finset ι) (a : ι)
 (b : ι -> M) : (∏ x in s, ite (x = a) (b x) 1) = ite (a in s) (b a) 1

--- 原说明 ---
A restatement of `prod_ite_eq` with the equality test reversed.
-/
theorem prod_ite_eq' [DecidableEq α] (f : α →₀ M) (a : α) (b : α → M → N) :
    (f.prod fun x v => ite (x = a) (b x v) 1) = ite (a ∈ f.support) (b a (f a)) 1 := by
  dsimp [Finsupp.prod]
  rw [f.support.prod_ite_eq']

/-- A restatement of `sum_ite_self_eq` with the equality test reversed. -/
/-
**Finsupp.sum_ite_self_eq'** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：sum_ite_self_eq' [DecidableEq α] {N : Type*} [AddCommMonoid N] (f : α ->₀ 
N) (a : α) : (f.sum fun x v => ite (x = a) v 0) = f a
参数：f : α ->₀ N；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.sum_ite_eq'`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} [in
st : Zero M] [inst_1 : AddCommMonoid N] [inst_2 : DecidableEq α]   (f : α →₀ M) 
(a : α) (…
· 使用定理 `Finsupp.if_mem_support`：if_mem_support [DecidableEq α] {N : Type*} [Zero
 N] (f : α ->₀ N) (a : α) : (if a in f.support then f a else 0) = f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
A restatement of `sum_ite_self_eq` with the equality test reversed.
-/
theorem sum_ite_self_eq' [DecidableEq α] {N : Type*} [AddCommMonoid N] (f : α →₀ N) (a : α) :
    (f.sum fun x v => ite (x = a) v 0) = f a := by
  simp

@[to_additive (attr := simp)]
/-
**Finsupp.prod_pow** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：prod_pow [Fintype α] (f : α ->₀ Nat) (g : α -> N) : (f.prod fun a b => g a
 ^ b) = ∏ a, g a ^ f a
参数：f : α ->₀ Nat；g : α -> N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.prod_fintype`：prod_fintype [Fintype α] (f : α ->₀ M) (g : α -> M
 -> N) (h : forall i, g i 0 = 1) : f.prod g = ∏ i, g i (f i)
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
-/
theorem prod_pow [Fintype α] (f : α →₀ ℕ) (g : α → N) :
    (f.prod fun a b => g a ^ b) = ∏ a, g a ^ f a :=
  f.prod_fintype _ fun _ ↦ pow_zero _

@[to_additive (attr := simp)]
/-
**Finsupp.prod_zpow** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：prod_zpow {N} [DivisionCommMonoid N] [Fintype α] (f : α ->₀ Int) (g : α ->
 N) : (f.prod fun a b => g a ^ b) = ∏ a, g a ^ f a
参数：f : α ->₀ Int；g : α -> N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.prod_fintype`：prod_fintype [Fintype α] (f : α ->₀ M) (g : α -> M
 -> N) (h : forall i, g i 0 = 1) : f.prod g = ∏ i, g i (f i)
· 使用定理 `zpow_zero`：∀ {G : Type u_1} [inst : DivInvMonoid G] (a : G), a ^ 0 = 1
-/
theorem prod_zpow {N} [DivisionCommMonoid N] [Fintype α] (f : α →₀ ℤ) (g : α → N) :
    (f.prod fun a b => g a ^ b) = ∏ a, g a ^ f a :=
  f.prod_fintype _ fun _ ↦ zpow_zero _

/-- If `g` maps a second argument of 0 to 1, then multiplying it over the
result of `onFinset` is the same as multiplying it over the original `Finset`. -/
@[to_additive
      /-- If `g` maps a second argument of 0 to 0, summing it over the
      result of `onFinset` is the same as summing it over the original `Finset`. -/]
/-
**Finsupp.onFinset_prod** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：onFinset_prod {s : Finset α} {f : α -> M} {g : α -> M -> N} (hf : forall a
, f a != 0 -> a in s) (hg : forall a, g a 0 = 1) : (onFinset s f hf).prod g = ∏ 
a in s, g a (f a)
参数：hf : forall a, f a != 0 -> a in s；hg : forall a, g a 0 = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.prod_subset`：prod_subset (h : s₁ subseteq s₂) (hf : forall x in s
₂, x ∉ s₁ -> f x = 1) : ∏ x in s₁, f x = ∏ x in s₂, f x
· 使用定理 `Finsupp.support_onFinset_subset`：support_onFinset_subset {s : Finset α} 
{f : α -> M} {hf} : (onFinset s f hf).support subseteq s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem onFinset_prod {s : Finset α} {f : α → M} {g : α → M → N} (hf : ∀ a, f a ≠ 0 → a ∈ s)
    (hg : ∀ a, g a 0 = 1) : (onFinset s f hf).prod g = ∏ a ∈ s, g a (f a) :=
  Finset.prod_subset support_onFinset_subset <| by simp +contextual [*]

/-- Taking a product over `f : α →₀ M` is the same as multiplying the value on a single element
`y ∈ f.support` by the product over `erase y f`. -/
@[to_additive
      /-- Taking a sum over `f : α →₀ M` is the same as adding the value on a
      single element `y ∈ f.support` to the sum over `erase y f`. -/]
/-
**Finsupp.mul_prod_erase** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：mul_prod_erase (f : α ->₀ M) (y : α) (g : α -> M -> N) (hyf : y in f.suppo
rt) : g y (f y) * (erase y f).prod g = f.prod g
参数：f : α ->₀ M；y : α；g : α -> M -> N；hyf : y in f.support。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.prod.eq_1`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} [inst
 : Zero M] [inst_1 : CommMonoid N] (f : α →₀ M) (g : α → M → N),   f.prod g = ∏ 
a ∈ f.s…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.mul_prod_erase`：mul_prod_erase [DecidableEq ι] (s : Finset ι) (f 
: ι -> M) {a : ι} (h : a in s) : (f a * ∏ x in s.erase a, f x) = ∏ x in s, f x
· 使用定理 `Finsupp.support_erase`：support_erase [DecidableEq α] {a : α} {f : α ->₀ 
M} : (f.erase a).support = f.support.erase a
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finsupp.erase_ne`：erase_ne {a a' : α} {f : α ->₀ M} (h : a' != a) : (f.e
rase a) a' = f a'
· 使用定理 `Finset.ne_of_mem_erase`：ne_of_mem_erase : b in erase s a -> b != a
-/
theorem mul_prod_erase (f : α →₀ M) (y : α) (g : α → M → N) (hyf : y ∈ f.support) :
    g y (f y) * (erase y f).prod g = f.prod g := by
  classical
    rw [Finsupp.prod, Finsupp.prod, ← Finset.mul_prod_erase _ _ hyf, Finsupp.support_erase,
      Finset.prod_congr rfl]
    intro h hx
    rw [Finsupp.erase_ne (ne_of_mem_erase hx)]

/-- Generalization of `Finsupp.mul_prod_erase`: if `g` maps a second argument of 0 to 1,
then its product over `f : α →₀ M` is the same as multiplying the value on any element
`y : α` by the product over `erase y f`. -/
@[to_additive
      /-- Generalization of `Finsupp.add_sum_erase`: if `g` maps a second argument of 0
      to 0, then its sum over `f : α →₀ M` is the same as adding the value on any element
      `y : α` to the sum over `erase y f`. -/]
/-
**Finsupp.mul_prod_erase'** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：mul_prod_erase' (f : α ->₀ M) (y : α) (g : α -> M -> N) (hg : forall i : α
, g i 0 = 1) : g y (f y) * (erase y f).prod g = f.prod g
参数：f : α ->₀ M；y : α；g : α -> M -> N；hg : forall i : α, g i 0 = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.mul_prod_erase`：mul_prod_erase (f : α ->₀ M) (y : α) (g : α -> M
 -> N) (hyf : y in f.support) : g y (f y) * (erase y f).prod g = f.prod g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finsupp.notMem_support_iff`：notMem_support_iff {f : α ->₀ M} {a} : a ∉ f
.support ↔ f a = 0
· 使用定理 `Finsupp.erase_of_notMem_support`：erase_of_notMem_support {f : α ->₀ M} {
a} (haf : a ∉ f.support) : erase a f = f
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem mul_prod_erase' (f : α →₀ M) (y : α) (g : α → M → N) (hg : ∀ i : α, g i 0 = 1) :
    g y (f y) * (erase y f).prod g = f.prod g := by
  by_cases hyf : y ∈ f.support
  · exact Finsupp.mul_prod_erase f y g hyf
  · rw [notMem_support_iff.mp hyf, hg y, erase_of_notMem_support hyf, one_mul]

@[to_additive]
/-
**Finsupp._root_.SubmonoidClass.finsuppProd_mem** 是 Mathlib 中的一个定理，位于命名空间 `Finsu
pp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.SubmonoidClass.finsuppProd_mem {S : Type*} [SetLike S N] [SubmonoidClass S N]
    (s : S) (f : α →₀ M) (g : α → M → N) (h : ∀ c, f c ≠ 0 → g c (f c) ∈ s) : f.prod g ∈ s :=
  prod_mem fun _i hi => h _ (Finsupp.mem_support_iff.mp hi)

-- Note: Using `gcongr only` since `congr` doesn't accept this lemma.
@[to_additive (attr := gcongr only)]
/-
**Finsupp.prod_congr** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：prod_congr {f : α ->₀ M} {g1 g2 : α -> M -> N} (h : forall x in f.support,
 g1 x (f x) = g2 x (f x)) : f.prod g1 = f.prod g2
参数：h : forall x in f.support, g1 x (f x) = g2 x (f x)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
-/
theorem prod_congr {f : α →₀ M} {g1 g2 : α → M → N} (h : ∀ x ∈ f.support, g1 x (f x) = g2 x (f x)) :
    f.prod g1 = f.prod g2 :=
  Finset.prod_congr rfl h

/-- The product over two finsupps agree if the functions agree and are well-behaved within the
shared support. -/
@[to_additive (attr := gcongr only)
/-- The sum over two finsupps agree if the functions agree and are well-behaved within the
shared support. -/]
/-
**Finsupp.prod_congr_of_eq_on_union** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：prod_congr_of_eq_on_union [DecidableEq α] {f1 f2 : α ->₀ M} {g1 g2 : α -> 
M -> N} (h : forall x in f1.support union f2.support, g1 x (f1 x) = g2 x (f2 x))
 (h1 : forall x in f1.support union f2.support, g1 x 0 = 1) (h2 : forall x in f1
.support union f2.support, g2 x 0 = 1) : f1.prod g1 = f2.prod g2
参数：h : forall x in f1.support union f2.support, g1 x (f1 x) = g2 x (f2 x)；h1 : f
orall x in f1.support union f2.support, g1 x 0 = 1；h2 : forall x in f1.support u
nion f2.support, g2 x 0 = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.prod_of_support_subset`：prod_of_support_subset (f : α ->₀ M) {s 
: Finset α} (hs : f.support subseteq s) (g : α -> M -> N) (h : forall i in s, g 
i 0 = 1) : f.prod g …
· 使用定理 `Finset.subset_union_left`：∀ {α : Type u_1} [inst : DecidableEq α] {s₁ s₂
 : Finset α}, s₁ ⊆ s₁ ∪ s₂
· 使用定理 `Finset.subset_union_right`：∀ {α : Type u_1} [inst : DecidableEq α] {s₁ s
₂ : Finset α}, s₂ ⊆ s₁ ∪ s₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
-/
theorem prod_congr_of_eq_on_union [DecidableEq α] {f1 f2 : α →₀ M} {g1 g2 : α → M → N}
    (h : ∀ x ∈ f1.support ∪ f2.support, g1 x (f1 x) = g2 x (f2 x))
    (h1 : ∀ x ∈ f1.support ∪ f2.support, g1 x 0 = 1)
    (h2 : ∀ x ∈ f1.support ∪ f2.support, g2 x 0 = 1) :
    f1.prod g1 = f2.prod g2 := by
  rw [Finsupp.prod_of_support_subset f1 Finset.subset_union_left _ h1,
    Finsupp.prod_of_support_subset f2 Finset.subset_union_right _ h2]
  exact Finset.prod_congr rfl h

@[to_additive]
/-
**Finsupp.prod_eq_single** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：prod_eq_single {f : α ->₀ M} (a : α) {g : α -> M -> N} (h₀ : forall b, f b
 != 0 -> b != a -> g b (f b) = 1) (h₁ : f a = 0 -> g a 0 = 1) : f.prod g = g a (
f a)
参数：a : α；h₀ : forall b, f b != 0 -> b != a -> g b (f b) = 1；h₁ : f a = 0 -> g a 
0 = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.prod_eq_single`：prod_eq_single {s : Finset ι} {f : ι -> M} (a : ι
) (h₀ : forall b in s, b != a -> f b = 1) (h₁ : a ∉ s -> f a = 1) : ∏ x in s, f 
x = f a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finsupp.mem_support_iff`：mem_support_iff {f : α ->₀ M} : forall {a : α},
 a in f.support ↔ f a != 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem prod_eq_single {f : α →₀ M} (a : α) {g : α → M → N}
    (h₀ : ∀ b, f b ≠ 0 → b ≠ a → g b (f b) = 1) (h₁ : f a = 0 → g a 0 = 1) :
    f.prod g = g a (f a) := by
  refine Finset.prod_eq_single a (fun b hb₁ hb₂ => ?_) (fun h => ?_)
  · exact h₀ b (mem_support_iff.mp hb₁) hb₂
  · simp only [notMem_support_iff] at h
    rw [h]
    exact h₁ h

@[to_additive]
/-
**Finsupp.prod_unique** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：prod_unique [Unique α] {f : α ->₀ M} {g : α -> M -> N} (h₁ : f default = 0
 -> g default 0 = 1) : f.prod g = g default (f default)
参数：h₁ : f default = 0 -> g default 0 = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.prod_eq_single`：prod_eq_single {f : α ->₀ M} (a : α) {g : α -> M
 -> N} (h₀ : forall b, f b != 0 -> b != a -> g b (f b) = 1) (h₁ : f a = 0 -> g a
 0 = 1) : f.…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma prod_unique [Unique α] {f : α →₀ M} {g : α → M → N} (h₁ : f default = 0 → g default 0 = 1) :
    f.prod g = g default (f default) :=
  prod_eq_single _ (fun a ↦ by simp [Subsingleton.elim a default]) h₁

end SumProd

section CommMonoidWithZero
variable [Zero α] [CommMonoidWithZero β] [Nontrivial β] [NoZeroDivisors β]
  {f : ι →₀ α} (a : α) {g : ι → α → β}

@[simp]
/-
**Finsupp.prod_eq_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：prod_eq_zero_iff : f.prod g = 0 ↔ exists i in f.support, g i (f i) = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.prod_eq_zero_iff`：prod_eq_zero_iff : ∏ x in s, f x = 0 ↔ exists a
 in s, f a = 0
-/
lemma prod_eq_zero_iff : f.prod g = 0 ↔ ∃ i ∈ f.support, g i (f i) = 0 := Finset.prod_eq_zero_iff
/-
**Finsupp.prod_ne_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：prod_ne_zero_iff : f.prod g != 0 ↔ forall i in f.support, g i (f i) != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.prod_ne_zero_iff`：prod_ne_zero_iff : ∏ x in s, f x != 0 ↔ forall 
a in s, f a != 0
-/
lemma prod_ne_zero_iff : f.prod g ≠ 0 ↔ ∀ i ∈ f.support, g i (f i) ≠ 0 := Finset.prod_ne_zero_iff

end CommMonoidWithZero
end Finsupp

@[to_additive]
/-
**map_finsuppProd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_finsuppProd [Zero M] [CommMonoid N] [CommMonoid P] {H : Type*} [FunLik
e H N P] [MonoidHomClass H N P] (h : H) (f : α ->₀ M) (g : α -> M -> N) : h (f.p
rod g) = f.prod fun a b => h (g a b)
参数：h : H；f : α ->₀ M；g : α -> M -> N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_prod`：map_prod [CommMonoid M] [CommMonoid N] {G : Type*} [FunLike G 
M N] [MonoidHomClass G M N] (g : G) (f : ι -> M) (s : Finset ι) : g (∏ x in s,…
-/
theorem map_finsuppProd [Zero M] [CommMonoid N] [CommMonoid P] {H : Type*}
    [FunLike H N P] [MonoidHomClass H N P]
    (h : H) (f : α →₀ M) (g : α → M → N) : h (f.prod g) = f.prod fun a b => h (g a b) :=
  map_prod h _ _

@[to_additive]
/-
**MonoidHom.coe_finsuppProd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonoidHom.coe_finsuppProd [Zero β] [MulOneClass N] [CommMonoid P] (f : α -
>₀ β) (g : α -> β -> N ->* P) : ⇑(f.prod g) = f.prod fun i fi => ⇑(g i fi)
参数：f : α ->₀ β；g : α -> β -> N ->* P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.coe_finsetProd`：MonoidHom.coe_finsetProd [MulOneClass M] [Comm
Monoid N] (f : ι -> M ->* N) (s : Finset ι) : ⇑(∏ x in s, f x) = ∏ x in s, ⇑(f x
)
-/
theorem MonoidHom.coe_finsuppProd [Zero β] [MulOneClass N] [CommMonoid P] (f : α →₀ β)
    (g : α → β → N →* P) : ⇑(f.prod g) = f.prod fun i fi => ⇑(g i fi) :=
  MonoidHom.coe_finsetProd _ _

@[to_additive (attr := simp)]
/-
**MonoidHom.finsuppProd_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonoidHom.finsuppProd_apply [Zero β] [MulOneClass N] [CommMonoid P] (f : α
 ->₀ β) (g : α -> β -> N ->* P) (x : N) : f.prod g x = f.prod fun i fi => g i fi
 x
参数：f : α ->₀ β；g : α -> β -> N ->* P；x : N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.finsetProd_apply`：MonoidHom.finsetProd_apply [MulOneClass M] [
CommMonoid N] (f : ι -> M ->* N) (s : Finset ι) (b : M) : (∏ x in s, f x) b = ∏ 
x in s, f x b
-/
theorem MonoidHom.finsuppProd_apply [Zero β] [MulOneClass N] [CommMonoid P] (f : α →₀ β)
    (g : α → β → N →* P) (x : N) : f.prod g x = f.prod fun i fi => g i fi x :=
  MonoidHom.finsetProd_apply _ _ _

namespace Finsupp

/-
**Finsupp.single_multiset_sum** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：single_multiset_sum [AddCommMonoid M] (s : Multiset M) (a : α) : single a 
s.sum = (s.map (single a)).sum
参数：s : Multiset M；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction_on`：∀ {α : Type u_1} {p : Multiset α → Prop} (s : Mul
tiset α), p 0 → (∀ (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → p s
· 使用定理 `Finsupp.single_zero`：single_zero (a : α) : (single a 0 : α ->₀ M) = 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.sum_cons`：∀ {M : Type u_3} [inst : AddCommMonoid M] (a : M) (s 
: Multiset M), (a ::ₘ s).sum = a + s.sum
· 使用引理 `Finsupp.single_add`：single_add (a : ι) (b₁ b₂ : M) : single a (b₁ + b₂) 
= single a b₁ + single a b₂
· 使用定理 `Multiset.map_cons`：map_cons (f : α -> β) (a s) : map f (a ::ₘ s) = f a :
:ₘ map f s
-/
theorem single_multiset_sum [AddCommMonoid M] (s : Multiset M) (a : α) :
    single a s.sum = (s.map (single a)).sum :=
  Multiset.induction_on s (single_zero _) fun a s ih => by
    rw [Multiset.sum_cons, single_add, ih, Multiset.map_cons, Multiset.sum_cons]
/-
**Finsupp.single_finsetSum** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：single_finsetSum [AddCommMonoid M] (s : Finset ι) (f : ι -> M) (a : α) : s
ingle a (∑ b in s, f b) = ∑ b in s, single a (f b)
参数：s : Finset ι；f : ι -> M；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.single_multiset_sum`：single_multiset_sum [AddCommMonoid M] (s : 
Multiset M) (a : α) : single a s.sum = (s.map (single a)).sum
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
-/
theorem single_finsetSum [AddCommMonoid M] (s : Finset ι) (f : ι → M) (a : α) :
    single a (∑ b ∈ s, f b) = ∑ b ∈ s, single a (f b) := by
  trans
  · apply single_multiset_sum
  · rw [Multiset.map_map]
    rfl

@[deprecated (since := "2026-04-08")] alias single_finset_sum := single_finsetSum
/-
**Finsupp.single_sum** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：single_sum [Zero M] [AddCommMonoid N] (s : ι ->₀ M) (f : ι -> M -> N) (a :
 α) : single a (s.sum f) = s.sum fun d c => single a (f d c)
参数：s : ι ->₀ M；f : ι -> M -> N；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.single_finsetSum`：single_finsetSum [AddCommMonoid M] (s : Finset
 ι) (f : ι -> M) (a : α) : single a (∑ b in s, f b) = ∑ b in s, single a (f b)
-/
theorem single_sum [Zero M] [AddCommMonoid N] (s : ι →₀ M) (f : ι → M → N) (a : α) :
    single a (s.sum f) = s.sum fun d c => single a (f d c) :=
  single_finsetSum _ _ _

@[to_additive]
/-
**Finsupp.prod_neg_index** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：prod_neg_index [SubtractionMonoid G] [CommMonoid M] {g : α ->₀ G} {h : α -
> G -> M} (h0 : forall a, h a 0 = 1) : (-g).prod h = g.prod fun a b => h a (-b)
参数：h0 : forall a, h a 0 = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.prod_mapRange_index`：prod_mapRange_index {f : M -> M'} {hf : f 0
 = 0} {g : α ->₀ M} {h : α -> M' -> N} (h0 : forall a, h a 0 = 1) : (mapRange f 
hf g).prod h = g.…
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
-/
theorem prod_neg_index [SubtractionMonoid G] [CommMonoid M] {g : α →₀ G} {h : α → G → M}
    (h0 : ∀ a, h a 0 = 1) : (-g).prod h = g.prod fun a b => h a (-b) :=
  prod_mapRange_index h0
/-
**Finsupp.finsetSum_apply** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：finsetSum_apply [AddCommMonoid N] (S : Finset ι) (f : ι -> α ->₀ N) (a : α
) : (∑ i in S, f i) a = ∑ i in S, f i a
参数：S : Finset ι；f : ι -> α ->₀ N；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
theorem finsetSum_apply [AddCommMonoid N] (S : Finset ι) (f : ι → α →₀ N) (a : α) :
    (∑ i ∈ S, f i) a = ∑ i ∈ S, f i a :=
  map_sum (applyAddHom a) _ _

@[deprecated (since := "2026-04-08")] alias finset_sum_apply := finsetSum_apply

@[simp]
/-
**Finsupp.sum_apply** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：sum_apply [Zero M] [AddCommMonoid N] {f : α ->₀ M} {g : α -> M -> β ->₀ N}
 {a₂ : β} : (f.sum g) a₂ = f.sum fun a₁ b => g a₁ b a₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.finsetSum_apply`：finsetSum_apply [AddCommMonoid N] (S : Finset ι
) (f : ι -> α ->₀ N) (a : α) : (∑ i in S, f i) a = ∑ i in S, f i a
-/
theorem sum_apply [Zero M] [AddCommMonoid N] {f : α →₀ M} {g : α → M → β →₀ N} {a₂ : β} :
    (f.sum g) a₂ = f.sum fun a₁ b => g a₁ b a₂ :=
  finsetSum_apply _ _ _
/-
**Finsupp.coe_finsetSum** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_2} {N : Type u_10} [inst : AddCommMonoid N] (
S : Finset ι) (f : ι → α →₀ N),   ⇑(∑ i ∈ S, f i) = ∑ i ∈ S, ⇑(f i)
参数：S : Finset ι；f : ι → α →₀ N；∑ i ∈ S, f i；f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
@[simp, norm_cast] theorem coe_finsetSum [AddCommMonoid N] (S : Finset ι) (f : ι → α →₀ N) :
    ⇑(∑ i ∈ S, f i) = ∑ i ∈ S, ⇑(f i) :=
  map_sum (coeFnAddHom : (α →₀ N) →+ _) _ _

@[deprecated (since := "2026-04-08")] alias coe_finset_sum := coe_finsetSum
/-
**Finsupp.coe_sum** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：∀ {α : Type u_1} {β : Type u_7} {M : Type u_8} {N : Type u_10} [inst : Zer
o M] [inst_1 : AddCommMonoid N] (f : α →₀ M)   (g : α → M → β →₀ N), ⇑(f.sum g) 
= f.sum fun a₁ b => ⇑(g a₁ b)
参数：f : α →₀ M；g : α → M → β →₀ N；f.sum g；g a₁ b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.coe_finsetSum`：∀ {α : Type u_1} {ι : Type u_2} {N : Type u_10} [
inst : AddCommMonoid N] (S : Finset ι) (f : ι → α →₀ N),   ⇑(∑ i ∈ S, f i) = ∑ i
 ∈ S, ⇑(f i…
-/
@[simp, norm_cast] theorem coe_sum [Zero M] [AddCommMonoid N] (f : α →₀ M) (g : α → M → β →₀ N) :
    ⇑(f.sum g) = f.sum fun a₁ b => ⇑(g a₁ b) :=
  coe_finsetSum _ _
/-
**Finsupp.support_sum** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：support_sum [DecidableEq β] [Zero M] [AddCommMonoid N] {f : α ->₀ M} {g : 
α -> M -> β ->₀ N} : (f.sum g).support subseteq f.support.biUnion fun a => (g a 
(f a)).support
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.exists_ne_zero_of_sum_ne_zero`：∀ {ι : Type u_1} {M : Type u_4} {s
 : Finset ι} [inst : AddCommMonoid M] {f : ι → M}, ∑ x ∈ s, f x ≠ 0 → ∃ a ∈ s, f
 a ≠ 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finsupp.mem_support_iff`：mem_support_iff {f : α ->₀ M} : forall {a : α},
 a in f.support ↔ f a != 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.sum_apply`：sum_apply [Zero M] [AddCommMonoid N] {f : α ->₀ M} {g
 : α -> M -> β ->₀ N} {a₂ : β} : (f.sum g) a₂ = f.sum fun a₁ b => g a₁ b a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
-/
theorem support_sum [DecidableEq β] [Zero M] [AddCommMonoid N] {f : α →₀ M} {g : α → M → β →₀ N} :
    (f.sum g).support ⊆ f.support.biUnion fun a => (g a (f a)).support := by
  have : ∀ c, (f.sum fun a b => g a b c) ≠ 0 → ∃ a, f a ≠ 0 ∧ ¬(g a (f a)) c = 0 := fun a₁ h =>
    let ⟨a, ha, ne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    ⟨a, mem_support_iff.mp ha, ne⟩
  simpa only [Finset.subset_iff, mem_support_iff, Finset.mem_biUnion, sum_apply, exists_prop]
/-
**Finsupp.support_finsetSum** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：support_finsetSum [DecidableEq β] [AddCommMonoid M] {s : Finset α} {f : α 
-> β ->₀ M} : (Finset.sum s f).support subseteq s.biUnion fun x => (f x).support
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sup_eq_biUnion`：sup_eq_biUnion {α β} [DecidableEq β] (s : Finset 
α) (t : α -> Finset β) : s.sup t = s.biUnion t
· 使用定理 `Finset.cons_induction_on`：cons_induction_on {α : Type*} {motive : Finset
 α -> Prop} (s : Finset α) (empty : motive ∅) (cons : forall (a : α) (s : Finset
 α) (h : a ∉ s…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Finset.sum_cons`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι} 
[inst : AddCommMonoid M] {f : ι → M} (h : a ∉ s),   ∑ x ∈ Finset.cons a s h, f x
 = f …
· 使用定理 `Finset.sup_cons`：sup_cons {b : β} (h : b ∉ s) : (cons b s h).sup f = f b
 ⊔ s.sup f
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `Finsupp.support_add`：support_add [DecidableEq ι] : (g₁ + g₂).support sub
seteq g₁.support union g₂.support
· 使用定理 `Finset.union_subset_union`：union_subset_union (hsu : s subseteq u) (htv 
: t subseteq v) : s union t subseteq u union v
· 使用定理 `Finset.Subset.refl`：∀ {α : Type u_1} (s : Finset α), s ⊆ s
-/
theorem support_finsetSum [DecidableEq β] [AddCommMonoid M] {s : Finset α} {f : α → β →₀ M} :
    (Finset.sum s f).support ⊆ s.biUnion fun x => (f x).support := by
  rw [← Finset.sup_eq_biUnion]
  induction s using Finset.cons_induction_on with
  | empty => rfl
  | cons _ _ _ ih =>
    rw [Finset.sum_cons, Finset.sup_cons]
    exact support_add.trans (Finset.union_subset_union (Finset.Subset.refl _) ih)

@[deprecated (since := "2026-04-08")] alias support_finset_sum := support_finsetSum
/-
**Finsupp.sum_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：sum_eq_one_iff (d : α ->₀ Nat) : sum d (fun _ n => n) = 1 ↔ exists a, d = 
single a 1
参数：d : α ->₀ Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Finsupp.ne_iff`：ne_iff {f g : α ->₀ M} : f != g ↔ exists a, f a != g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finsupp.support_erase`：support_erase [DecidableEq α] {a : α} {f : α ->₀ 
M} : (f.erase a).support = f.support.erase a
· 使用定理 `Finset.erase_eq_of_notMem`：erase_eq_of_notMem {a : α} {s : Finset α} (h 
: a ∉ s) : erase s a = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Finsupp.erase_of_notMem_support`：erase_of_notMem_support {f : α ->₀ M} {
a} (haf : a ∉ f.support) : erase a f = f
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Finsupp.erase_ne`：erase_ne {a a' : α} {f : α ->₀ M} (h : a' != a) : (f.e
rase a) a' = f a'
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `Nat.add_eq_one_iff`：∀ {m n : ℕ}, m + n = 1 ↔ m = 0 ∧ n = 1 ∨ m = 1 ∧ n =
 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finsupp.add_sum_erase'`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} 
[inst : Zero M] [inst_1 : AddCommMonoid N] (f : α →₀ M) (y : α)   (g : α → M → N
), (∀ (i : α…
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
（共 32 条，此处仅展示前 30 条）
-/
theorem sum_eq_one_iff (d : α →₀ ℕ) : sum d (fun _ n ↦ n) = 1 ↔ ∃ a, d = single a 1 := by
  classical
  refine ⟨fun h1 ↦ ?_, ?_⟩
  · have hd0 : d ≠ 0 := (by simp [·] at h1)
    obtain ⟨a, ha⟩ := ne_iff.mp hd0
    obtain ⟨hda, hda'⟩ : d a = 1 ∧ ∀ i ≠ a, d i = 0 := by
      rw [← add_sum_erase' _ a _ (fun _ ↦ rfl), Nat.add_eq_one_iff, or_iff_not_imp_left] at h1
      simp_all +contextual [sum, support_erase, sum_eq_zero_iff, mem_erase, erase_ne]
    use a
    ext b
    by_cases hb : b = a
    · rw [hb, single_eq_same, hda]
    · simpa only [single_eq_of_ne hb] using hda' b hb
  · rintro ⟨a, rfl⟩
    rw [sum_eq_single a ?_ (fun _ ↦ rfl), single_eq_same]
    exact fun _ _ hba ↦ single_eq_of_ne hba

@[to_additive (attr := simp)]
/-
**Finsupp.prod_mul** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：prod_mul [Zero M] [CommMonoid N] {f : α ->₀ M} {h₁ h₂ : α -> M -> N} : (f.
prod fun a b => h₁ a b * h₂ a b) = f.prod h₁ * f.prod h₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.prod_mul_distrib`：prod_mul_distrib : ∏ x in s, f x * g x = (∏ x i
n s, f x) * ∏ x in s, g x
-/
theorem prod_mul [Zero M] [CommMonoid N] {f : α →₀ M} {h₁ h₂ : α → M → N} :
    (f.prod fun a b => h₁ a b * h₂ a b) = f.prod h₁ * f.prod h₂ :=
  Finset.prod_mul_distrib

@[to_additive (attr := simp)]
/-
**Finsupp.prod_inv** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：prod_inv [Zero M] [CommGroup G] {f : α ->₀ M} {h : α -> M -> G} : (f.prod 
fun a b => (h a b)⁻¹) = (f.prod h)⁻¹
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_prod`：map_prod [CommMonoid M] [CommMonoid N] {G : Type*} [FunLike G 
M N] [MonoidHomClass G M N] (g : G) (f : ι -> M) (s : Finset ι) : g (∏ x in s,…
-/
theorem prod_inv [Zero M] [CommGroup G] {f : α →₀ M} {h : α → M → G} :
    (f.prod fun a b => (h a b)⁻¹) = (f.prod h)⁻¹ :=
  (map_prod (MonoidHom.id G)⁻¹ _ _).symm

@[simp]
/-
**Finsupp.sum_sub** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：sum_sub [Zero M] [SubtractionCommMonoid G] {f : α ->₀ M} {h₁ h₂ : α -> M -
> G} : (f.sum fun a b => h₁ a b - h₂ a b) = f.sum h₁ - f.sum h₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sum_sub_distrib`：∀ {ι : Type u_1} {G : Type u_5} {s : Finset ι} [
inst : SubtractionCommMonoid G] (f g : ι → G),   ∑ x ∈ s, (f x - g x) = ∑ x ∈ s,
 f x - ∑ x ∈…
-/
theorem sum_sub [Zero M] [SubtractionCommMonoid G] {f : α →₀ M} {h₁ h₂ : α → M → G} :
    (f.sum fun a b => h₁ a b - h₂ a b) = f.sum h₁ - f.sum h₂ :=
  Finset.sum_sub_distrib ..

/-- Taking the product under `h` is an additive-to-multiplicative homomorphism of finsupps,
if `h` is an additive-to-multiplicative homomorphism on the support.
This is a more general version of `Finsupp.prod_add_index'`; the latter has simpler hypotheses. -/
@[to_additive
      /-- Taking the product under `h` is an additive homomorphism of finsupps, if `h` is an
      additive homomorphism on the support. This is a more general version of
      `Finsupp.sum_add_index'`; the latter has simpler hypotheses. -/]
/-
**Finsupp.prod_add_index** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：prod_add_index [DecidableEq α] [AddZeroClass M] [CommMonoid N] {f g : α ->
₀ M} {h : α -> M -> N} (h_zero : forall a in f.support union g.support, h a 0 = 
1) (h_add : forall a in f.support union g.support, forall (b₁ b₂), h a (b₁ + b₂)
 = h a b₁ * h a b₂) : (f + g).prod h = f.prod h * g.prod h
参数：h_zero : forall a in f.support union g.support, h a 0 = 1；h_add : forall a in
 f.support union g.support, forall (b₁ b₂), h a (b₁ + b₂) = h a b₁ * h a b₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.prod_of_support_subset`：prod_of_support_subset (f : α ->₀ M) {s 
: Finset α} (hs : f.support subseteq s) (g : α -> M -> N) (h : forall i in s, g 
i 0 = 1) : f.prod g …
· 使用定理 `Finset.subset_union_left`：∀ {α : Type u_1} [inst : DecidableEq α] {s₁ s₂
 : Finset α}, s₁ ⊆ s₁ ∪ s₂
· 使用定理 `Finset.subset_union_right`：∀ {α : Type u_1} [inst : DecidableEq α] {s₁ s
₂ : Finset α}, s₂ ⊆ s₁ ∪ s₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.prod_mul_distrib`：prod_mul_distrib : ∏ x in s, f x * g x = (∏ x i
n s, f x) * ∏ x in s, g x
· 使用引理 `Finsupp.support_add`：support_add [DecidableEq ι] : (g₁ + g₂).support sub
seteq g₁.support union g₂.support
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
-/
theorem prod_add_index [DecidableEq α] [AddZeroClass M] [CommMonoid N] {f g : α →₀ M}
    {h : α → M → N} (h_zero : ∀ a ∈ f.support ∪ g.support, h a 0 = 1)
    (h_add : ∀ a ∈ f.support ∪ g.support, ∀ (b₁ b₂), h a (b₁ + b₂) = h a b₁ * h a b₂) :
    (f + g).prod h = f.prod h * g.prod h := by
  rw [Finsupp.prod_of_support_subset f subset_union_left h h_zero,
    Finsupp.prod_of_support_subset g subset_union_right h h_zero, ←
    Finset.prod_mul_distrib, Finsupp.prod_of_support_subset (f + g) Finsupp.support_add h h_zero]
  exact Finset.prod_congr rfl fun x hx => by apply h_add x hx

/-- Taking the product under `h` is an additive-to-multiplicative homomorphism of finsupps,
if `h` is an additive-to-multiplicative homomorphism.
This is a more specialized version of `Finsupp.prod_add_index` with simpler hypotheses. -/
@[to_additive
      /-- Taking the sum under `h` is an additive homomorphism of finsupps,if `h` is an additive
      homomorphism. This is a more specific version of `Finsupp.sum_add_index` with simpler
      hypotheses. -/]
/-
**Finsupp.prod_add_index'** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：prod_add_index' [AddZeroClass M] [CommMonoid N] {f g : α ->₀ M} {h : α -> 
M -> N} (h_zero : forall a, h a 0 = 1) (h_add : forall a b₁ b₂, h a (b₁ + b₂) = 
h a b₁ * h a b₂) : (f + g).prod h = f.prod h * g.prod h
参数：h_zero : forall a, h a 0 = 1；h_add : forall a b₁ b₂, h a (b₁ + b₂) = h a b₁ *
 h a b₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.prod_add_index`：prod_add_index [DecidableEq α] [AddZeroClass M] 
[CommMonoid N] {f g : α ->₀ M} {h : α -> M -> N} (h_zero : forall a in f.support
 union g.sup…
-/
theorem prod_add_index' [AddZeroClass M] [CommMonoid N] {f g : α →₀ M} {h : α → M → N}
    (h_zero : ∀ a, h a 0 = 1) (h_add : ∀ a b₁ b₂, h a (b₁ + b₂) = h a b₁ * h a b₂) :
    (f + g).prod h = f.prod h * g.prod h := by
  classical exact prod_add_index (fun a _ => h_zero a) fun a _ => h_add a

@[simp]
/-
**Finsupp.sum_hom_add_index** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：sum_hom_add_index [AddZeroClass M] [AddCommMonoid N] {f g : α ->₀ M} (h : 
α -> M ->+ N) : ((f + g).sum fun x => h x) = (f.sum fun x => h x) + g.sum fun x 
=> h x
参数：h : α -> M ->+ N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.sum_add_index'`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} 
[inst : AddZeroClass M] [inst_1 : AddCommMonoid N] {f g : α →₀ M}   {h : α → M →
 N},   (∀ (a…
· 使用定理 `AddMonoidHom.map_zero`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZero M
] [inst_1 : AddZero N] (f : M →+ N), f 0 = 0
· 使用定理 `AddMonoidHom.map_add`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZero M]
 [inst_1 : AddZero N] (f : M →+ N) (a b : M), f (a + b) = f a + f b
-/
theorem sum_hom_add_index [AddZeroClass M] [AddCommMonoid N] {f g : α →₀ M} (h : α → M →+ N) :
    ((f + g).sum fun x => h x) = (f.sum fun x => h x) + g.sum fun x => h x :=
  sum_add_index' (fun a => (h a).map_zero) fun a => (h a).map_add

@[simp]
/-
**Finsupp.prod_hom_add_index** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：prod_hom_add_index [AddZeroClass M] [CommMonoid N] {f g : α ->₀ M} (h : α 
-> Multiplicative M ->* N) : ((f + g).prod fun a b => h a (Multiplicative.ofAdd 
b)) = (f.prod fun a b => h a (Multiplicative.ofAdd b)) * g.prod fun a b => h a (
Multiplicative.ofAdd b)
参数：h : α -> Multiplicative M ->* N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.prod_add_index'`：prod_add_index' [AddZeroClass M] [CommMonoid N]
 {f g : α ->₀ M} {h : α -> M -> N} (h_zero : forall a, h a 0 = 1) (h_add : foral
l a b₁ b₂, h …
· 使用定理 `MonoidHom.map_one`：∀ {M : Type u_4} {N : Type u_5} [inst : MulOne M] [in
st_1 : MulOne N] (f : M →* N), f 1 = 1
· 使用定理 `MonoidHom.map_mul`：∀ {M : Type u_4} {N : Type u_5} [inst : MulOne M] [in
st_1 : MulOne N] (f : M →* N) (a b : M), f (a * b) = f a * f b
-/
theorem prod_hom_add_index [AddZeroClass M] [CommMonoid N] {f g : α →₀ M}
    (h : α → Multiplicative M →* N) :
    ((f + g).prod fun a b => h a (Multiplicative.ofAdd b)) =
      (f.prod fun a b => h a (Multiplicative.ofAdd b)) *
        g.prod fun a b => h a (Multiplicative.ofAdd b) :=
  prod_add_index' (fun a => (h a).map_one) fun a => (h a).map_mul

/-- The canonical isomorphism between families of additive monoid homomorphisms `α → (M →+ N)`
and monoid homomorphisms `(α →₀ M) →+ N`. -/
/-
**Finsupp.liftAddHom** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp`。
形式化陈述：liftAddHom [AddZeroClass M] [AddCommMonoid N] : (α -> M ->+ N) ≃+ ((α ->₀ 
M) ->+ N) where toFun F
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.sum_hom_add_index`：sum_hom_add_index [AddZeroClass M] [AddCommMo
noid N] {f g : α ->₀ M} (h : α -> M ->+ N) : ((f + g).sum fun x => h x) = (f.sum
 fun x => h x) …

--- 原说明 ---
The canonical isomorphism between families of additive monoid homomorphisms `α →
 (M →+ N)`
and monoid homomorphisms `(α →₀ M) →+ N`.
-/
def liftAddHom [AddZeroClass M] [AddCommMonoid N] : (α → M →+ N) ≃+ ((α →₀ M) →+ N) where
  toFun F :=
    { toFun f := f.sum (F ·)
      map_zero' := Finsupp.sum_zero_index
      map_add' f g := Finsupp.sum_hom_add_index F }
  invFun F x := F.comp (singleAddHom x)
  left_inv F := by ext; simp
  right_inv F := by ext; simp
  map_add' F G := by ext; simp

@[simp]
/-
**Finsupp.liftAddHom_apply** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：liftAddHom_apply [AddZeroClass M] [AddCommMonoid N] (F : α -> M ->+ N) (f 
: α ->₀ M) : (liftAddHom (α
参数：F : α -> M ->+ N；f : α ->₀ M。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem liftAddHom_apply [AddZeroClass M] [AddCommMonoid N] (F : α → M →+ N) (f : α →₀ M) :
    (liftAddHom (α := α) (M := M) (N := N)) F f = f.sum fun x => F x :=
  rfl

@[simp]
/-
**Finsupp.liftAddHom_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：liftAddHom_symm_apply [AddZeroClass M] [AddCommMonoid N] (F : (α ->₀ M) ->
+ N) (x : α) : (liftAddHom (α
参数：F : (α ->₀ M) ->+ N；x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem liftAddHom_symm_apply [AddZeroClass M] [AddCommMonoid N] (F : (α →₀ M) →+ N) (x : α) :
    (liftAddHom (α := α) (M := M) (N := N)).symm F x = F.comp (singleAddHom x) :=
  rfl
/-
**Finsupp.liftAddHom_symm_apply_apply** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：liftAddHom_symm_apply_apply [AddZeroClass M] [AddCommMonoid N] (F : (α ->₀
 M) ->+ N) (x : α) (y : M) : (liftAddHom (α
参数：F : (α ->₀ M) ->+ N；x : α；y : M。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem liftAddHom_symm_apply_apply [AddZeroClass M] [AddCommMonoid N] (F : (α →₀ M) →+ N) (x : α)
    (y : M) : (liftAddHom (α := α) (M := M) (N := N)).symm F x y = F (single x y) :=
  rfl

@[simp]
/-
**Finsupp.liftAddHom_singleAddHom** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：liftAddHom_singleAddHom [AddCommMonoid M] : (liftAddHom (α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.eq_symm_apply`：eq_symm_apply {α β} (e : α ≃ β) {x y} : y = e.symm 
x ↔ e y = x
-/
theorem liftAddHom_singleAddHom [AddCommMonoid M] :
    (liftAddHom (α := α) (M := M) (N := α →₀ M)) (singleAddHom : α → M →+ α →₀ M) =
      AddMonoidHom.id _ :=
  liftAddHom.toEquiv.eq_symm_apply.1 rfl

@[simp]
/-
**Finsupp.sum_single** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：sum_single [AddCommMonoid M] (f : α ->₀ M) : f.sum single = f
参数：f : α ->₀ M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用定理 `Finsupp.liftAddHom_singleAddHom`：liftAddHom_singleAddHom [AddCommMonoid 
M] : (liftAddHom (α
-/
theorem sum_single [AddCommMonoid M] (f : α →₀ M) : f.sum single = f :=
  DFunLike.congr_fun liftAddHom_singleAddHom f

/-- The `Finsupp` version of `Finset.univ_sum_single` -/
@[simp]
/-
**Finsupp.univ_sum_single** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：univ_sum_single [Fintype α] [AddCommMonoid M] (f : α ->₀ M) : ∑ a : α, sin
gle a (f a) = f
参数：f : α ->₀ M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.coe_finsetSum`：∀ {α : Type u_1} {ι : Type u_2} {N : Type u_10} [
inst : AddCommMonoid N] (S : Finset ι) (f : ι → α →₀ N),   ⇑(∑ i ∈ S, f i) = ∑ i
 ∈ S, ⇑(f i…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finsupp.single_eq_pi_single`：single_eq_pi_single [DecidableEq α] (a : α)
 (b : M) : ⇑(single a b) = Pi.single a b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.univ_sum_single`：∀ {I : Type u_7} [inst : DecidableEq I] {M : I →
 Type u_8} [inst_1 : (i : I) → AddCommMonoid (M i)] [inst_2 : Fintype I]   (f : 
(i : I) → M …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The `Finsupp` version of `Finset.univ_sum_single`
-/
theorem univ_sum_single [Fintype α] [AddCommMonoid M] (f : α →₀ M) :
    ∑ a : α, single a (f a) = f := by
  classical
  refine DFunLike.coe_injective ?_
  simp_rw [coe_finsetSum, single_eq_pi_single, Finset.univ_sum_single]

@[simp]
/-
**Finsupp.univ_sum_single_apply** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：univ_sum_single_apply [AddCommMonoid M] [Fintype α] (i : α) (m : M) : ∑ j 
: α, single i m j = m
参数：i : α；m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.single.eq_1`：∀ {α : Type u_1} {M : Type u_5} [inst : Zero M] (a 
: α) (b : M),   (fun₀ | a => b) = { support := if b = 0 then ∅ else {a}, toFun :
= Pi.sing…
· 使用定理 `Finsupp.coe_mk`：coe_mk (f : α -> M) (s : Finset α) (h : forall a, a in s
 ↔ f a != 0) : ⇑(⟨s, f, h⟩ : α ->₀ M) = f
· 使用定理 `Finset.sum_pi_single'`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMo
noid M] [inst_1 : DecidableEq ι] (a : ι) (x : M) (s : Finset ι),   ∑ a' ∈ s, Pi.
single a x …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem univ_sum_single_apply [AddCommMonoid M] [Fintype α] (i : α) (m : M) :
    ∑ j : α, single i m j = m := by
  classical rw [single, coe_mk, Finset.sum_pi_single']
  simp

@[simp]
/-
**Finsupp.univ_sum_single_apply'** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：univ_sum_single_apply' [AddCommMonoid M] [Fintype α] (i : α) (m : M) : ∑ j
 : α, single j m i = m
参数：i : α；m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_pi_single`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : Decida
bleEq ι] [inst_1 : (a : ι) → AddCommMonoid (M a)] (a : ι)   (f : (a : ι) → M a) 
(s : Finse…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem univ_sum_single_apply' [AddCommMonoid M] [Fintype α] (i : α) (m : M) :
    ∑ j : α, single j m i = m := by
  simp_rw [single, coe_mk]
  classical rw [Finset.sum_pi_single]
  simp
/-
**Finsupp.sum_single_add_single** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：sum_single_add_single (f₁ f₂ : ι) (g₁ g₂ : A) (F : ι -> A -> B) (H : f₁ !=
 f₂) (HF : forall f, F f 0 = 0) : sum (single f₁ g₁ + single f₂ g₂) F = F f₁ g₁ 
+ F f₂ g₂
参数：f₁ f₂ : ι；g₁ g₂ : A；F : ι -> A -> B；H : f₁ != f₂；HF : forall f, F f 0 = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.sum_of_support_subset`：∀ {α : Type u_1} {M : Type u_8} {N : Type
 u_10} [inst : Zero M] [inst_1 : AddCommMonoid N] (f : α →₀ M) {s : Finset α},  
 f.support ⊆ s → ∀ …
· 使用引理 `Finsupp.support_single_add_single_subset`：support_single_add_single_subs
et [DecidableEq ι] {f₁ f₂ : ι} {g₁ g₂ : M} : (single f₁ g₁ + single f₂ g₂).suppo
rt subseteq {f₁, f₂}
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finsupp.single_apply`：single_apply [Decidable (a = a')] : single a b a' 
= if a = a' then b else 0
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
lemma sum_single_add_single (f₁ f₂ : ι) (g₁ g₂ : A) (F : ι → A → B) (H : f₁ ≠ f₂)
    (HF : ∀ f, F f 0 = 0) :
    sum (single f₁ g₁ + single f₂ g₂) F = F f₁ g₁ + F f₂ g₂ := by
  classical
  simp [sum_of_support_subset _ support_single_add_single_subset, single_apply, H, HF, H.symm]
/-
**Finsupp.equivFunOnFinite_symm_eq_sum** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：equivFunOnFinite_symm_eq_sum [Fintype α] [AddCommMonoid M] (f : α -> M) : 
equivFunOnFinite.symm f = ∑ a, single a (f a)
参数：f : α -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Finsupp.univ_sum_single`：univ_sum_single [Fintype α] [AddCommMonoid M] (
f : α ->₀ M) : ∑ a : α, single a (f a) = f
-/
theorem equivFunOnFinite_symm_eq_sum [Fintype α] [AddCommMonoid M] (f : α → M) :
    equivFunOnFinite.symm f = ∑ a, single a (f a) :=
  (univ_sum_single _).symm
/-
**Finsupp.coe_univ_sum_single** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：coe_univ_sum_single [Fintype α] [AddCommMonoid M] (f : α -> M) : ⇑(∑ a : α
, single a (f a)) = f
参数：f : α -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finsupp.equivFunOnFinite_symm_eq_sum`：equivFunOnFinite_symm_eq_sum [Fint
ype α] [AddCommMonoid M] (f : α -> M) : equivFunOnFinite.symm f = ∑ a, single a 
(f a)
-/
theorem coe_univ_sum_single [Fintype α] [AddCommMonoid M] (f : α → M) :
    ⇑(∑ a : α, single a (f a)) = f :=
  congrArg _ (equivFunOnFinite_symm_eq_sum f).symm
/-
**Finsupp.equivFunOnFinite_symm_sum** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：equivFunOnFinite_symm_sum [Fintype α] [AddCommMonoid M] (f : α -> M) : ((e
quivFunOnFinite.symm f).sum fun _ n => n) = ∑ a, f a
参数：f : α -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.equivFunOnFinite_symm_eq_sum`：equivFunOnFinite_symm_eq_sum [Fint
ype α] [AddCommMonoid M] (f : α -> M) : equivFunOnFinite.symm f = ∑ a, single a 
(f a)
· 使用定理 `Finsupp.sum_fintype`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} [in
st : Zero M] [inst_1 : AddCommMonoid N] [inst_2 : Fintype α]   (f : α →₀ M) (g :
 α → M → …
· 使用定理 `Finsupp.coe_univ_sum_single`：coe_univ_sum_single [Fintype α] [AddCommMon
oid M] (f : α -> M) : ⇑(∑ a : α, single a (f a)) = f
-/
theorem equivFunOnFinite_symm_sum [Fintype α] [AddCommMonoid M] (f : α → M) :
    ((equivFunOnFinite.symm f).sum fun _ n ↦ n) = ∑ a, f a := by
  rw [equivFunOnFinite_symm_eq_sum, sum_fintype _ _ fun _ ↦ rfl, coe_univ_sum_single]
/-
**Finsupp.liftAddHom_apply_single** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：liftAddHom_apply_single [AddZeroClass M] [AddCommMonoid N] (f : α -> M ->+
 N) (a : α) (b : M) : (liftAddHom (α
参数：f : α -> M ->+ N；a : α；b : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.sum_single_index`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10
} [inst : Zero M] [inst_1 : AddCommMonoid N] {a : α} {b : M}   {h : α → M → N}, 
h a 0 = 0 → (f…
· 使用定理 `AddMonoidHom.map_zero`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZero M
] [inst_1 : AddZero N] (f : M →+ N), f 0 = 0
-/
theorem liftAddHom_apply_single [AddZeroClass M] [AddCommMonoid N] (f : α → M →+ N) (a : α)
    (b : M) : (liftAddHom (α := α) (M := M) (N := N)) f (single a b) = f a b :=
  sum_single_index (f a).map_zero

@[simp]
/-
**Finsupp.liftAddHom_comp_single** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：liftAddHom_comp_single [AddZeroClass M] [AddCommMonoid N] (f : α -> M ->+ 
N) (a : α) : ((liftAddHom (α
参数：f : α -> M ->+ N；a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.ext`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZero M] [in
st_1 : AddZero N] ⦃f g : M →+ N⦄, (∀ (x : M), f x = g x) → f = g
· 使用定理 `Finsupp.liftAddHom_apply_single`：liftAddHom_apply_single [AddZeroClass M
] [AddCommMonoid N] (f : α -> M ->+ N) (a : α) (b : M) : (liftAddHom (α
-/
theorem liftAddHom_comp_single [AddZeroClass M] [AddCommMonoid N] (f : α → M →+ N) (a : α) :
    ((liftAddHom (α := α) (M := M) (N := N)) f).comp (singleAddHom a) = f a :=
  AddMonoidHom.ext fun b => liftAddHom_apply_single f a b
/-
**Finsupp.comp_liftAddHom** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：comp_liftAddHom [AddZeroClass M] [AddCommMonoid N] [AddCommMonoid P] (g : 
N ->+ P) (f : α -> M ->+ N) : g.comp ((liftAddHom (α
参数：g : N ->+ P；f : α -> M ->+ N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AddEquiv.symm_apply_eq`：∀ {M : Type u_4} {N : Type u_5} [inst : Add M] [
inst_1 : Add N] (e : M ≃+ N) {x : N} {y : M}, e.symm x = y ↔ x = e y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.liftAddHom_symm_apply`：liftAddHom_symm_apply [AddZeroClass M] [A
ddCommMonoid N] (F : (α ->₀ M) ->+ N) (x : α) : (liftAddHom (α
· 使用定理 `AddMonoidHom.comp_assoc`：∀ {M : Type u_4} {N : Type u_5} {P : Type u_6} 
{Q : Type u_10} [inst : AddZero M] [inst_1 : AddZero N]   [inst_2 : AddZero P] [
inst_3 : AddZ…
· 使用定理 `Finsupp.liftAddHom_comp_single`：liftAddHom_comp_single [AddZeroClass M] 
[AddCommMonoid N] (f : α -> M ->+ N) (a : α) : ((liftAddHom (α
-/
theorem comp_liftAddHom [AddZeroClass M] [AddCommMonoid N] [AddCommMonoid P] (g : N →+ P)
    (f : α → M →+ N) :
    g.comp ((liftAddHom (α := α) (M := M) (N := N)) f) =
      (liftAddHom (α := α) (M := M) (N := P)) fun a => g.comp (f a) :=
  liftAddHom.symm_apply_eq.1 <|
    funext fun a => by
      rw [liftAddHom_symm_apply, AddMonoidHom.comp_assoc, liftAddHom_comp_single]
/-
**Finsupp.sum_sub_index** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：sum_sub_index [AddGroup β] [AddCommGroup γ] {f g : α ->₀ β} {h : α -> β ->
 γ} (h_sub : forall a b₁ b₂, h a (b₁ - b₂) = h a b₁ - h a b₂) : (f - g).sum h = 
f.sum h - g.sum h
参数：h_sub : forall a b₁ b₂, h a (b₁ - b₂) = h a b₁ - h a b₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.map_sub`：∀ {α : Type u_2} {β : Type u_3} [inst : AddGroup α
] [inst_1 : SubtractionMonoid β] (f : α →+ β) (g h : α),   f (g - h) = f g - f h
-/
theorem sum_sub_index [AddGroup β] [AddCommGroup γ] {f g : α →₀ β} {h : α → β → γ}
    (h_sub : ∀ a b₁ b₂, h a (b₁ - b₂) = h a b₁ - h a b₂) : (f - g).sum h = f.sum h - g.sum h :=
  ((liftAddHom (α := α) (M := β) (N := γ)) fun a =>
    AddMonoidHom.ofMapSub (h a) (h_sub a)).map_sub f g

@[to_additive]
/-
**Finsupp.prod_embDomain** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：prod_embDomain [Zero M] [CommMonoid N] {v : α ->₀ M} {f : α ↪ β} {g : β ->
 M -> N} : (v.embDomain f).prod g = v.prod fun a b => g (f a) b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.prod.eq_1`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} [inst
 : Zero M] [inst_1 : CommMonoid N] (f : α →₀ M) (g : α → M → N),   f.prod g = ∏ 
a ∈ f.s…
· 使用定理 `Finsupp.support_embDomain`：support_embDomain (f : α ↪ β) (v : α ->₀ M) :
 (embDomain f v).support = v.support.map f
· 使用定理 `Finset.prod_map`：prod_map (s : Finset ι) (e : ι ↪ κ) (f : κ -> M) : ∏ x 
in s.map e, f x = ∏ x in s, f (e x)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finsupp.embDomain_apply_self`：embDomain_apply_self (f : α ↪ β) (v : α ->
₀ M) (a : α) : embDomain f v (f a) = v a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_embDomain [Zero M] [CommMonoid N] {v : α →₀ M} {f : α ↪ β} {g : β → M → N} :
    (v.embDomain f).prod g = v.prod fun a b => g (f a) b := by
  rw [prod, prod, support_embDomain, Finset.prod_map]
  simp_rw [embDomain_apply_self]

@[to_additive]
/-
**Finsupp.prod_finsetSum_index** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：prod_finsetSum_index [AddCommMonoid M] [CommMonoid N] {s : Finset ι} {g : 
ι -> α ->₀ M} {h : α -> M -> N} (h_zero : forall a, h a 0 = 1) (h_add : forall a
 b₁ b₂, h a (b₁ + b₂) = h a b₁ * h a b₂) : (∏ i in s, (g i).prod h) = (∑ i in s,
 g i).prod h
参数：h_zero : forall a, h a 0 = 1；h_add : forall a b₁ b₂, h a (b₁ + b₂) = h a b₁ *
 h a b₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.cons_induction_on`：cons_induction_on {α : Type*} {motive : Finset
 α -> Prop} (s : Finset α) (empty : motive ∅) (cons : forall (a : α) (s : Finset
 α) (h : a ∉ s…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_cons`：prod_cons (h : a ∉ s) : ∏ x in cons a s h, f x = f a *
 ∏ x in s, f x
· 使用定理 `Finset.sum_cons`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι} 
[inst : AddCommMonoid M] {f : ι → M} (h : a ∉ s),   ∑ x ∈ Finset.cons a s h, f x
 = f …
· 使用定理 `Finsupp.prod_add_index'`：prod_add_index' [AddZeroClass M] [CommMonoid N]
 {f g : α ->₀ M} {h : α -> M -> N} (h_zero : forall a, h a 0 = 1) (h_add : foral
l a b₁ b₂, h …
-/
theorem prod_finsetSum_index [AddCommMonoid M] [CommMonoid N] {s : Finset ι} {g : ι → α →₀ M}
    {h : α → M → N} (h_zero : ∀ a, h a 0 = 1) (h_add : ∀ a b₁ b₂, h a (b₁ + b₂) = h a b₁ * h a b₂) :
    (∏ i ∈ s, (g i).prod h) = (∑ i ∈ s, g i).prod h :=
  Finset.cons_induction_on s rfl fun a s has ih => by
    rw [prod_cons, ih, sum_cons, prod_add_index' h_zero h_add]

@[deprecated (since := "2026-04-08")] alias sum_finset_sum_index := sum_finsetSum_index

@[to_additive existing, deprecated (since := "2026-04-08")]
alias prod_finset_sum_index := prod_finsetSum_index

@[to_additive]
/-
**Finsupp.prod_sum_index** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：prod_sum_index [Zero M] [AddCommMonoid N] [CommMonoid P] {f : α ->₀ M} {g 
: α -> M -> β ->₀ N} {h : β -> N -> P} (h_zero : forall a, h a 0 = 1) (h_add : f
orall a b₁ b₂, h a (b₁ + b₂) = h a b₁ * h a b₂) : (f.sum g).prod h = f.prod fun 
a b => (g a b).prod h
参数：h_zero : forall a, h a 0 = 1；h_add : forall a b₁ b₂, h a (b₁ + b₂) = h a b₁ *
 h a b₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finsupp.prod_finsetSum_index`：prod_finsetSum_index [AddCommMonoid M] [Co
mmMonoid N] {s : Finset ι} {g : ι -> α ->₀ M} {h : α -> M -> N} (h_zero : forall
 a, h a 0 = 1) (h_…
-/
theorem prod_sum_index [Zero M] [AddCommMonoid N] [CommMonoid P] {f : α →₀ M}
    {g : α → M → β →₀ N} {h : β → N → P} (h_zero : ∀ a, h a 0 = 1)
    (h_add : ∀ a b₁ b₂, h a (b₁ + b₂) = h a b₁ * h a b₂) :
    (f.sum g).prod h = f.prod fun a b => (g a b).prod h :=
  (prod_finsetSum_index h_zero h_add).symm
/-
**Finsupp.multiset_sum_sum_index** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：multiset_sum_sum_index [AddCommMonoid M] [AddCommMonoid N] (f : Multiset (
α ->₀ M)) (h : α -> M -> N) (h₀ : forall a, h a 0 = 0) (h₁ : forall (a : α) (b₁ 
b₂ : M), h a (b₁ + b₂) = h a b₁ + h a b₂) : f.sum.sum h = (f.map fun g : α ->₀ M
 => g.sum h).sum
参数：f : Multiset (α ->₀ M)；h : α -> M -> N；h₀ : forall a, h a 0 = 0；h₁ : forall (
a : α) (b₁ b₂ : M), h a (b₁ + b₂) = h a b₁ + h a b₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction_on`：∀ {α : Type u_1} {p : Multiset α → Prop} (s : Mul
tiset α), p 0 → (∀ (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → p s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.sum_cons`：∀ {M : Type u_3} [inst : AddCommMonoid M] (a : M) (s 
: Multiset M), (a ::ₘ s).sum = a + s.sum
· 使用定理 `Multiset.map_cons`：map_cons (f : α -> β) (a s) : map f (a ::ₘ s) = f a :
:ₘ map f s
· 使用定理 `Finsupp.sum_add_index'`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} 
[inst : AddZeroClass M] [inst_1 : AddCommMonoid N] {f g : α →₀ M}   {h : α → M →
 N},   (∀ (a…
-/
theorem multiset_sum_sum_index [AddCommMonoid M] [AddCommMonoid N] (f : Multiset (α →₀ M))
    (h : α → M → N) (h₀ : ∀ a, h a 0 = 0)
    (h₁ : ∀ (a : α) (b₁ b₂ : M), h a (b₁ + b₂) = h a b₁ + h a b₂) :
    f.sum.sum h = (f.map fun g : α →₀ M => g.sum h).sum :=
  Multiset.induction_on f rfl fun a s ih => by
    rw [Multiset.sum_cons, Multiset.map_cons, Multiset.sum_cons, sum_add_index' h₀ h₁, ih]
/-
**Finsupp.support_sum_eq_biUnion** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：support_sum_eq_biUnion {α : Type*} {ι : Type*} {M : Type*} [DecidableEq α]
 [AddCommMonoid M] {g : ι -> α ->₀ M} (s : Finset ι) (h : forall i₁ i₂, i₁ != i₂
 -> Disjoint (g i₁).support (g i₂).support) : (∑ i in s, g i).support = s.biUnio
n fun i => (g i).support
参数：s : Finset ι；h : forall i₁ i₂, i₁ != i₂ -> Disjoint (g i₁).support (g i₂).sup
port。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用引理 `Finset.biUnion_insert`：biUnion_insert [DecidableEq α] {a : α} : (insert 
a s).biUnion t = t a union s.biUnion t
· 使用引理 `Finsupp.support_add_eq`：support_add_eq [DecidableEq ι] (h : Disjoint g₁.
support g₂.support) : (g₁ + g₂).support = g₁.support union g₂.support
· 使用引理 `Finset.disjoint_biUnion_right`：disjoint_biUnion_right (s : Finset β) (t 
: Finset α) (f : α -> Finset β) : Disjoint s (t.biUnion f) ↔ forall i in t, Disj
oint s (f i)
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `ne_of_mem_of_not_mem`：∀ {α : Type u_1} {β : Type u_2} [inst : Membership
 α β] {s : β} {a b : α}, a ∈ s → b ∉ s → a ≠ b
-/
theorem support_sum_eq_biUnion {α : Type*} {ι : Type*} {M : Type*} [DecidableEq α]
    [AddCommMonoid M] {g : ι → α →₀ M} (s : Finset ι)
    (h : ∀ i₁ i₂, i₁ ≠ i₂ → Disjoint (g i₁).support (g i₂).support) :
    (∑ i ∈ s, g i).support = s.biUnion fun i => (g i).support := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro i s hi
    simp only [hi, sum_insert, not_false_iff, biUnion_insert]
    intro hs
    rw [Finsupp.support_add_eq, hs]
    rw [hs, Finset.disjoint_biUnion_right]
    intro j hj
    exact h _ _ (ne_of_mem_of_not_mem hj hi).symm
/-
**Finsupp.multiset_map_sum** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：multiset_map_sum [Zero M] {f : α ->₀ M} {m : β -> γ} {h : α -> M -> Multis
et β} : Multiset.map m (f.sum h) = f.sum fun a b => (h a b).map m
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
theorem multiset_map_sum [Zero M] {f : α →₀ M} {m : β → γ} {h : α → M → Multiset β} :
    Multiset.map m (f.sum h) = f.sum fun a b => (h a b).map m :=
  map_sum (Multiset.mapAddMonoidHom m) _ f.support
/-
**Finsupp.multiset_sum_sum** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：multiset_sum_sum [Zero M] [AddCommMonoid N] {f : α ->₀ M} {h : α -> M -> M
ultiset N} : Multiset.sum (f.sum h) = f.sum fun a b => Multiset.sum (h a b)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
theorem multiset_sum_sum [Zero M] [AddCommMonoid N] {f : α →₀ M} {h : α → M → Multiset N} :
    Multiset.sum (f.sum h) = f.sum fun a b => Multiset.sum (h a b) :=
  map_sum Multiset.sumAddMonoidHom _ f.support

/-- For disjoint `f1` and `f2`, and function `g`, the product of the products of `g`
over `f1` and `f2` equals the product of `g` over `f1 + f2` -/
@[to_additive
      /-- For disjoint `f1` and `f2`, and function `g`, the sum of the sums of `g`
      over `f1` and `f2` equals the sum of `g` over `f1 + f2` -/]
/-
**Finsupp.prod_add_index_of_disjoint** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：prod_add_index_of_disjoint [AddCommMonoid M] {f1 f2 : α ->₀ M} (hd : Disjo
int f1.support f2.support) {β : Type*} [CommMonoid β] (g : α -> M -> β) : (f1 + 
f2).prod g = f1.prod g * f2.prod g
参数：hd : Disjoint f1.support f2.support；g : α -> M -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finsupp.notMem_support_iff`：notMem_support_iff {f : α ->₀ M} {a} : a ∉ f
.support ↔ f a = 0
· 使用定理 `Finset.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s 
-> a ∉ t
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Disjoint.symm`：Disjoint.symm (x y : Finmap β) (h : Disjoint x y) : Disjo
int y x
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用引理 `Finsupp.support_add_eq`：support_add_eq [DecidableEq ι] (h : Disjoint g₁.
support g₂.support) : (g₁ + g₂).support = g₁.support union g₂.support
· 使用定理 `Finset.prod_union`：prod_union [DecidableEq ι] (h : Disjoint s₁ s₂) : ∏ x
 in s₁ union s₂, f x = (∏ x in s₁, f x) * ∏ x in s₂, f x
-/
theorem prod_add_index_of_disjoint [AddCommMonoid M] {f1 f2 : α →₀ M}
    (hd : Disjoint f1.support f2.support) {β : Type*} [CommMonoid β] (g : α → M → β) :
    (f1 + f2).prod g = f1.prod g * f2.prod g := by
  have :
    ∀ {f1 f2 : α →₀ M},
      Disjoint f1.support f2.support → (∏ x ∈ f1.support, g x (f1 x + f2 x)) = f1.prod g :=
    fun hd =>
    Finset.prod_congr rfl fun x hx => by
      simp only [notMem_support_iff.mp (disjoint_left.mp hd hx), add_zero]
  classical simp_rw [← this hd, ← this hd.symm, add_comm (f2 _), Finsupp.prod, support_add_eq hd,
      prod_union hd, add_apply]
/-
**Finsupp.prod_dvd_prod_of_subset_of_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：prod_dvd_prod_of_subset_of_dvd [Zero M] [CommMonoid N] {f1 f2 : α ->₀ M} {
g1 g2 : α -> M -> N} (h1 : f1.support subseteq f2.support) (h2 : forall a : α, a
 in f1.support -> g1 a (f1 a) ∣ g2 a (f2 a)) : f1.prod g1 ∣ f2.prod g2
参数：h1 : f1.support subseteq f2.support；h2 : forall a : α, a in f1.support -> g1 
a (f1 a) ∣ g2 a (f2 a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sdiff_union_of_subset`：sdiff_union_of_subset {s₁ s₂ : Finset α} (
h : s₁ subseteq s₂) : s₂ \ s₁ union s₁ = s₂
· 使用定理 `Finset.prod_union`：prod_union [DecidableEq ι] (h : Disjoint s₁ s₂) : ∏ x
 in s₁ union s₂, f x = (∏ x in s₁, f x) * ∏ x in s₂, f x
· 使用定理 `Finset.sdiff_disjoint`：sdiff_disjoint : Disjoint (t \ s) s
· 使用定理 `dvd_mul_of_dvd_right`：dvd_mul_of_dvd_right (h : a ∣ b) (c : α) : a ∣ c *
 b
· 使用引理 `Finset.prod_dvd_prod_of_dvd`：prod_dvd_prod_of_dvd (f g : ι -> M) (h : fo
rall i in s, f i ∣ g i) : ∏ i in s, f i ∣ ∏ i in s, g i
-/
theorem prod_dvd_prod_of_subset_of_dvd [Zero M] [CommMonoid N] {f1 f2 : α →₀ M}
    {g1 g2 : α → M → N} (h1 : f1.support ⊆ f2.support)
    (h2 : ∀ a : α, a ∈ f1.support → g1 a (f1 a) ∣ g2 a (f2 a)) : f1.prod g1 ∣ f2.prod g2 := by
  classical
    simp only [Finsupp.prod]
    rw [← sdiff_union_of_subset h1, prod_union sdiff_disjoint]
    apply dvd_mul_of_dvd_right
    apply prod_dvd_prod_of_dvd
    exact h2
/-
**Finsupp.indicator_eq_sum_attach_single** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：indicator_eq_sum_attach_single [AddCommMonoid M] {s : Finset α} (f : foral
l a in s, M) : indicator s f = ∑ x in s.attach, single ↑x (f x x.2)
参数：f : forall a in s, M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finsupp.sum_single`：sum_single [AddCommMonoid M] (f : α ->₀ M) : f.sum s
ingle = f
· 使用定理 `Finsupp.sum.eq_1`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} [inst 
: Zero M] [inst_1 : AddCommMonoid N] (f : α →₀ M) (g : α → M → N),   f.sum g = ∑
 a ∈ f…
· 使用定理 `Finset.sum_subset`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [i
nst : AddCommMonoid M] {f : ι → M},   s₁ ⊆ s₂ → (∀ x ∈ s₂, x ∉ s₁ → f x = 0) → ∑
 x ∈ s₁…
· 使用定理 `Finsupp.support_indicator_subset`：support_indicator_subset : (indicator 
s f).support subseteq s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finsupp.notMem_support_iff`：notMem_support_iff {f : α ->₀ M} {a} : a ∉ f
.support ↔ f a = 0
· 使用定理 `Finsupp.single_zero`：single_zero (a : α) : (single a 0 : α ->₀ M) = 0
· 使用定理 `Finset.sum_attach`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMonoid
 M] (s : Finset ι) (f : ι → M), ∑ x ∈ s.attach, f ↑x = ∑ x ∈ s, f x
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finsupp.indicator_of_mem`：indicator_of_mem (hi : i in s) (f : forall i i
n s, α) : indicator s f i = f i hi
-/
lemma indicator_eq_sum_attach_single [AddCommMonoid M] {s : Finset α} (f : ∀ a ∈ s, M) :
    indicator s f = ∑ x ∈ s.attach, single ↑x (f x x.2) := by
  rw [← sum_single (indicator s f), sum, sum_subset (support_indicator_subset _ _), ← sum_attach]
  · refine Finset.sum_congr rfl (fun _ _ => ?_)
    rw [indicator_of_mem]
  · intro i _ hi
    rw [notMem_support_iff.mp hi, single_zero]
/-
**Finsupp.indicator_eq_sum_single** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：indicator_eq_sum_single [AddCommMonoid M] (s : Finset α) (f : α -> M) : in
dicator s (fun x _ => f x) = ∑ x in s, single x (f x)
参数：s : Finset α；f : α -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Finsupp.indicator_eq_sum_attach_single`：indicator_eq_sum_attach_single [
AddCommMonoid M] {s : Finset α} (f : forall a in s, M) : indicator s f = ∑ x in 
s.attach, single ↑x (f x x.2…
· 使用定理 `Finset.sum_attach`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMonoid
 M] (s : Finset ι) (f : ι → M), ∑ x ∈ s.attach, f ↑x = ∑ x ∈ s, f x
-/
lemma indicator_eq_sum_single [AddCommMonoid M] (s : Finset α) (f : α → M) :
    indicator s (fun x _ ↦ f x) = ∑ x ∈ s, single x (f x) :=
  (indicator_eq_sum_attach_single _).trans <| sum_attach _ fun x ↦ single x (f x)

@[to_additive (attr := simp)]
/-
**Finsupp.prod_indicator_index_eq_prod_attach** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp
`。
形式化陈述：prod_indicator_index_eq_prod_attach [Zero M] [CommMonoid N] {s : Finset α}
 (f : forall a in s, M) {h : α -> M -> N} (h_zero : forall a in s, h a 0 = 1) : 
(indicator s f).prod h = ∏ x in s.attach, h ↑x (f x x.2)
参数：f : forall a in s, M；h_zero : forall a in s, h a 0 = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.prod_of_support_subset`：prod_of_support_subset (f : α ->₀ M) {s 
: Finset α} (hs : f.support subseteq s) (g : α -> M -> N) (h : forall i in s, g 
i 0 = 1) : f.prod g …
· 使用定理 `Finsupp.support_indicator_subset`：support_indicator_subset : (indicator 
s f).support subseteq s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Finset.prod_attach`：prod_attach (s : Finset ι) (f : ι -> M) : ∏ x in s.a
ttach, f x = ∏ x in s, f x
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finsupp.indicator_of_mem`：indicator_of_mem (hi : i in s) (f : forall i i
n s, α) : indicator s f i = f i hi
-/
lemma prod_indicator_index_eq_prod_attach [Zero M] [CommMonoid N]
    {s : Finset α} (f : ∀ a ∈ s, M) {h : α → M → N} (h_zero : ∀ a ∈ s, h a 0 = 1) :
    (indicator s f).prod h = ∏ x ∈ s.attach, h ↑x (f x x.2) := by
  rw [prod_of_support_subset _ (support_indicator_subset _ _) h h_zero, ← prod_attach]
  refine Finset.prod_congr rfl (fun _ _ => ?_)
  rw [indicator_of_mem]

@[to_additive (attr := simp)]
/-
**Finsupp.prod_attach_index** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：prod_attach_index [CommMonoid N] {s : Finset α} (f : α -> M) {h : α -> M -
> N} : ∏ x in s.attach, h x (f x) = ∏ x in s, h x (f x)
参数：f : α -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.prod_attach`：prod_attach (s : Finset ι) (f : ι -> M) : ∏ x in s.a
ttach, f x = ∏ x in s, f x
-/
lemma prod_attach_index [CommMonoid N] {s : Finset α} (f : α → M) {h : α → M → N} :
    ∏ x ∈ s.attach, h x (f x) = ∏ x ∈ s, h x (f x) :=
  prod_attach _ fun x ↦ h x (f x)

@[to_additive]
/-
**Finsupp.prod_indicator_index** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：prod_indicator_index [Zero M] [CommMonoid N] {s : Finset α} (f : α -> M) {
h : α -> M -> N} (h_zero : forall a in s, h a 0 = 1) : (indicator s (fun x _ => 
f x)).prod h = ∏ x in s, h x (f x)
参数：f : α -> M；h_zero : forall a in s, h a 0 = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finsupp.prod_indicator_index_eq_prod_attach`：prod_indicator_index_eq_pro
d_attach [Zero M] [CommMonoid N] {s : Finset α} (f : forall a in s, M) {h : α ->
 M -> N} (h_zero : forall a in s,…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用引理 `Finsupp.prod_attach_index`：prod_attach_index [CommMonoid N] {s : Finset 
α} (f : α -> M) {h : α -> M -> N} : ∏ x in s.attach, h x (f x) = ∏ x in s, h x (
f x)
-/
lemma prod_indicator_index [Zero M] [CommMonoid N]
    {s : Finset α} (f : α → M) {h : α → M → N} (h_zero : ∀ a ∈ s, h a 0 = 1) :
    (indicator s (fun x _ ↦ f x)).prod h = ∏ x ∈ s, h x (f x) := by
  simp +contextual [h_zero]

@[to_additive]
/-
**Finsupp.prod_mul_eq_prod_mul_of_exists** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：prod_mul_eq_prod_mul_of_exists [Zero M] [CommMonoid N] {f : α ->₀ M} {g : 
α -> M -> N} {n₁ n₂ : N} (a : α) (ha : a in f.support) (h : g a (f a) * n₁ = g a
 (f a) * n₂) : f.prod g * n₁ = f.prod g * n₂
参数：a : α；ha : a in f.support；h : g a (f a) * n₁ = g a (f a) * n₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.prod_mul_eq_prod_mul_of_exists`：prod_mul_eq_prod_mul_of_exists {s
 : Finset ι} {f : ι -> M} {b₁ b₂ : M} (a : ι) (ha : a in s) (h : f a * b₁ = f a 
* b₂) : (∏ a in s, f a) * b…
-/
lemma prod_mul_eq_prod_mul_of_exists [Zero M] [CommMonoid N]
    {f : α →₀ M} {g : α → M → N} {n₁ n₂ : N}
    (a : α) (ha : a ∈ f.support)
    (h : g a (f a) * n₁ = g a (f a) * n₂) :
    f.prod g * n₁ = f.prod g * n₂ := by
  exact Finset.prod_mul_eq_prod_mul_of_exists a ha h

end Finsupp

/-
**Finset.sum_apply'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.sum_apply' : (∑ k in s, f k) i = ∑ k in s, f k i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
theorem Finset.sum_apply' : (∑ k ∈ s, f k) i = ∑ k ∈ s, f k i :=
  map_sum (Finsupp.applyAddHom i) f s
/-
**Finsupp.sum_apply'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finsupp.sum_apply' : g.sum k x = g.sum fun i b => k i b x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
-/
theorem Finsupp.sum_apply' : g.sum k x = g.sum fun i b => k i b x :=
  Finset.sum_apply _ _ _

/-- Version of `Finsupp.sum_apply'` that applies in large generality to linear combinations
of functions in any `FunLike` type on which addition is defined pointwise.

At the time of writing Mathlib does not have a typeclass to express the condition
that addition on a `FunLike` type is pointwise; hence this is asserted via explicit hypotheses. -/
/-
**Finsupp.sum_apply''** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finsupp.sum_apply'' {A F : Type*} [AddZeroClass A] [AddCommMonoid F] [FunL
ike F γ B] (g : ι ->₀ A) (k : ι -> A -> F) (x : γ) (h0 : (0 : F) x = 0) (hadd : 
forall (f g : F), (f + g : F) x = f x + g x) : g.sum k x = g.sum (fun i a => k i
 a x)
参数：g : ι ->₀ A；k : ι -> A -> F；x : γ；h0 : (0 : F) x = 0；hadd : forall (f g : F),
 (f + g : F) x = f x + g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst : De
cidableEq α],   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → motive s → motive 
(inser…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…

--- 原说明 ---
Version of `Finsupp.sum_apply'` that applies in large generality to linear combi
nations
of functions in any `FunLike` type on which addition is defined pointwise.

At the time of writing Mathlib does not have a typeclass to express the conditio
n
that addition on a `FunLike` type is pointwise; hence this is asserted via expli
cit hypotheses.
-/
theorem Finsupp.sum_apply'' {A F : Type*} [AddZeroClass A] [AddCommMonoid F] [FunLike F γ B]
    (g : ι →₀ A) (k : ι → A → F) (x : γ)
    (h0 : (0 : F) x = 0) (hadd : ∀ (f g : F), (f + g : F) x = f x + g x) :
    g.sum k x = g.sum (fun i a ↦ k i a x) := by
  classical
  unfold Finsupp.sum
  induction g.support using Finset.induction with
  | empty => simp [h0]
  | insert i s hi ih => simp [sum_insert hi, hadd, ih]

section

variable [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S]

/-
**Finsupp.sum_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finsupp.sum_mul (b : S) (s : α ->₀ R) {f : α -> R -> S} : s.sum f * b = s.
sum fun a c => f a c * b
参数：b : S；s : α ->₀ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.sum_mul`：sum_mul (s : Finset ι) (f : ι -> R) (a : R) : (∑ i in s,
 f i) * a = ∑ i in s, f i * a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Finsupp.sum_mul (b : S) (s : α →₀ R) {f : α → R → S} :
    s.sum f * b = s.sum fun a c => f a c * b := by simp only [Finsupp.sum, Finset.sum_mul]
/-
**Finsupp.mul_sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finsupp.mul_sum (b : S) (s : α ->₀ R) {f : α -> R -> S} : b * s.sum f = s.
sum fun a c => b * f a c
参数：b : S；s : α ->₀ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Finsupp.mul_sum (b : S) (s : α →₀ R) {f : α → R → S} :
    b * s.sum f = s.sum fun a c => b * f a c := by simp only [Finsupp.sum, Finset.mul_sum]

end

/-
**Multiset.card_finsuppSum** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_2} {M : Type u_8} [inst : Zero M] (f : ι →₀ M
) (g : ι → M → Multiset α),   (f.sum g).card = f.sum fun i m => (g i m).card
参数：f : ι →₀ M；g : ι → M → Multiset α；f.sum g；g i m。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_finsuppSum`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} {P : Typ
e u_11} [inst : Zero M] [inst_1 : AddCommMonoid N]   [inst_2 : AddCommMonoid P] 
{H :…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
@[simp] lemma Multiset.card_finsuppSum [Zero M] (f : ι →₀ M) (g : ι → M → Multiset α) :
    card (f.sum g) = f.sum fun i m ↦ card (g i m) := map_finsuppSum cardHom ..

namespace Nat

/-- If `0 : ℕ` is not in the support of `f : ℕ →₀ ℕ` then `0 < ∏ x ∈ f.support, x ^ (f x)`. -/
/-
**Nat.prod_pow_pos_of_zero_notMem_support** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：prod_pow_pos_of_zero_notMem_support {f : Nat ->₀ Nat} (nhf : 0 ∉ f.support
) : 0 < f.prod (· ^ ·)
参数：nhf : 0 ∉ f.support。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.pos_iff_ne_zero`：∀ {n : ℕ}, 0 < n ↔ n ≠ 0
· 使用引理 `Finset.prod_ne_zero_iff`：prod_ne_zero_iff : ∏ x in s, f x != 0 ↔ forall 
a in s, f a != 0
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Nat.instIsDomain`：IsDomain ℕ
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If `0 : ℕ` is not in the support of `f : ℕ →₀ ℕ` then `0 < ∏ x ∈ f.support, x ^ 
(f x)`.
-/
theorem prod_pow_pos_of_zero_notMem_support {f : ℕ →₀ ℕ} (nhf : 0 ∉ f.support) :
    0 < f.prod (· ^ ·) :=
  Nat.pos_iff_ne_zero.mpr <| Finset.prod_ne_zero_iff.mpr fun _ hf =>
    pow_ne_zero _ fun H => by subst H; exact nhf hf

end Nat

namespace MulOpposite
variable {ι M N : Type*} [AddCommMonoid M] [Zero N]

/-
**MulOpposite.op_finsuppSum** 是 Mathlib 中的一个引理，位于命名空间 `MulOpposite`。
形式化陈述：op_finsuppSum (f : ι ->₀ N) (g : ι -> N -> M) : op (f.sum g) = f.sum fun i
 n => op (g i n)
参数：f : ι ->₀ N；g : ι -> N -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.op_sum`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoid M] 
(s : Finset ι) (f : ι → M),   MulOpposite.op (∑ x ∈ s, f x) = ∑ x ∈ s, MulOpposi
te.…
-/
lemma op_finsuppSum (f : ι →₀ N) (g : ι → N → M) :
    op (f.sum g) = f.sum fun i n ↦ op (g i n) := op_sum ..
/-
**MulOpposite.unop_finsuppSum** 是 Mathlib 中的一个引理，位于命名空间 `MulOpposite`。
形式化陈述：unop_finsuppSum (f : ι ->₀ N) (g : ι -> N -> Mᵐᵒᵖ) : unop (f.sum g) = f.su
m fun i n => unop (g i n)
参数：f : ι ->₀ N；g : ι -> N -> Mᵐᵒᵖ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.unop_sum`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoid M
] (s : Finset ι) (f : ι → Mᵐᵒᵖ),   MulOpposite.unop (∑ x ∈ s, f x) = ∑ x ∈ s, Mu
lOppo…
-/
lemma unop_finsuppSum (f : ι →₀ N) (g : ι → N → Mᵐᵒᵖ) :
    unop (f.sum g) = f.sum fun i n ↦ unop (g i n) := unop_sum ..

end MulOpposite

namespace AddOpposite
variable {ι M N : Type*} [CommMonoid M] [Zero N]

/-
**AddOpposite.op_finsuppProd** 是 Mathlib 中的一个定理，位于命名空间 `AddOpposite`。
形式化陈述：∀ {ι : Type u_16} {M : Type u_17} {N : Type u_18} [inst : CommMonoid M] [i
nst_1 : Zero N] (f : ι →₀ N) (g : ι → N → M),   AddOpposite.op (f.prod g) = f.pr
od fun i n => AddOpposite.op (g i n)
参数：f : ι →₀ N；g : ι → N → M；f.prod g；g i n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.op_prod`：∀ {ι : Type u_1} {M : Type u_3} [inst : CommMonoid M] (s
 : Finset ι) (f : ι → M),   AddOpposite.op (∏ i ∈ s, f i) = ∏ i ∈ s, AddOpposite
.op …
-/
@[simp] lemma op_finsuppProd (f : ι →₀ N) (g : ι → N → M) :
    op (f.prod g) = f.prod fun i n ↦ op (g i n) := op_prod ..
/-
**AddOpposite.unop_finsuppProd** 是 Mathlib 中的一个定理，位于命名空间 `AddOpposite`。
形式化陈述：∀ {ι : Type u_16} {M : Type u_17} {N : Type u_18} [inst : CommMonoid M] [i
nst_1 : Zero N] (f : ι →₀ N)   (g : ι → N → Mᵐᵒᵖ), AddOpposite.unop (f.prod g) =
 f.prod fun i n => AddOpposite.unop (g i n)
参数：f : ι →₀ N；g : ι → N → Mᵐᵒᵖ；f.prod g；g i n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.unop_prod`：∀ {ι : Type u_1} {M : Type u_3} [inst : CommMonoid M] 
(s : Finset ι) (f : ι → Mᵐᵒᵖ),   AddOpposite.unop (∏ i ∈ s, f i) = ∏ i ∈ s, AddO
pposit…
-/
@[simp] lemma unop_finsuppProd (f : ι →₀ N) (g : ι → N → Mᵐᵒᵖ) :
    unop (f.prod g) = f.prod fun i n ↦ unop (g i n) := unop_prod ..

end AddOpposite

