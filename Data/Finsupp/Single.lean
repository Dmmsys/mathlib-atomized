/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kim Morrison
-/
module

public import Mathlib.Algebra.Group.Indicator
public import Mathlib.Data.Finsupp.Defs

/-!
# Finitely supported functions on exactly one point

This file contains definitions and basic results on defining/updating/removing `Finsupp`s
using one point of the domain.

## Main declarations

* `Finsupp.single`: The `Finsupp` which is nonzero in exactly one point.
* `Finsupp.update`: Changes one value of a `Finsupp`.
* `Finsupp.erase`: Replaces one value of a `Finsupp` by `0`.

## Implementation notes

This file is a `noncomputable theory` and uses classical logic throughout.
-/

@[expose] public section

assert_not_exists CompleteLattice

noncomputable section

open Finset Function

variable {α β γ ι M M' N P G H R S : Type*}

namespace Finsupp

/-! ### Declarations about `single` -/

section Single

variable [Zero M] {a a' : α} {b : M}

/-- `single a b` is the finitely supported function with value `b` at `a` and zero otherwise. -/
/-
**Finsupp.single** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp`。
形式化陈述：single (a : α) (b : M) : α ->₀ M where support
参数：a : α；b : M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`single a b` is the finitely supported function with value `b` at `a` and zero o
therwise.
-/
def single (a : α) (b : M) : α →₀ M where
  support :=
    haveI := Classical.decEq M
    if b = 0 then ∅ else {a}
  toFun :=
    haveI := Classical.decEq α
    Pi.single a b
  mem_support_toFun a' := by grind

@[grind =]
/-
**Finsupp.single_apply** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：single_apply [Decidable (a = a')] : single a b a' = if a = a' then b else 
0
参数：a = a'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Pi.single_apply`：∀ {ι : Type u_1} [inst : DecidableEq ι] {M : Type u_9} 
[inst_1 : Zero M] (i : ι) (x : M) (i' : ι),   Pi.single i x i' = if i' = i then 
x els…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem single_apply [Decidable (a = a')] : single a b a' = if a = a' then b else 0 := by
  classical
  simp_rw [@eq_comm _ a a', single, coe_mk, Pi.single_apply]
/-
**Finsupp.single_apply_left** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：single_apply_left {f : α -> β} (hf : Function.Injective f) (x z : α) (y : 
M) : single (f x) y (f z) = single x y z
参数：hf : Function.Injective f；x z : α；y : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.single_apply`：single_apply [Decidable (a = a')] : single a b a' 
= if a = a' then b else 0
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem single_apply_left {f : α → β} (hf : Function.Injective f) (x z : α) (y : M) :
    single (f x) y (f z) = single x y z := by classical simp only [single_apply, hf.eq_iff]
/-
**Finsupp.single_eq_pi_single** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：single_eq_pi_single [DecidableEq α] (a : α) (b : M) : ⇑(single a b) = Pi.s
ingle a b
参数：a : α；b : M。
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
· 使用定理 `Finsupp.single_apply`：single_apply [Decidable (a = a')] : single a b a' 
= if a = a' then b else 0
· 使用定理 `Pi.single_apply`：∀ {ι : Type u_1} [inst : DecidableEq ι] {M : Type u_9} 
[inst_1 : Zero M] (i : ι) (x : M) (i' : ι),   Pi.single i x i' = if i' = i then 
x els…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem single_eq_pi_single [DecidableEq α] (a : α) (b : M) : ⇑(single a b) = Pi.single a b := by
  ext; simp [single_apply, Pi.single_apply, eq_comm]
/-
**Finsupp.set_indicator_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：set_indicator_singleton (a : α) (f : α -> M) : Set.indicator {a} f = ⇑(sin
gle a (f a))
参数：a : α；f : α -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.indicator_singleton`：∀ {ι : Type u_6} [inst : DecidableEq ι] {M : Ty
pe u_7} [inst_1 : Zero M] (i : ι) (f : ι → M),   {i}.indicator f = Pi.single i (
f i)
· 使用定理 `Finsupp.single_eq_pi_single`：single_eq_pi_single [DecidableEq α] (a : α)
 (b : M) : ⇑(single a b) = Pi.single a b
-/
theorem set_indicator_singleton (a : α) (f : α → M) :
    Set.indicator {a} f = ⇑(single a (f a)) := by
  classical rw [Set.indicator_singleton, single_eq_pi_single]

@[deprecated set_indicator_singleton (since := "2026-04-27")]
/-
**Finsupp.single_eq_set_indicator** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：single_eq_set_indicator : ⇑(single a b) = Set.indicator {a} fun _ => b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finsupp.set_indicator_singleton`：set_indicator_singleton (a : α) (f : α 
-> M) : Set.indicator {a} f = ⇑(single a (f a))
-/
theorem single_eq_set_indicator : ⇑(single a b) = Set.indicator {a} fun _ => b :=
  (set_indicator_singleton a (fun _ => b)).symm

@[simp]
/-
**Finsupp.single_eq_same** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：single_eq_same : (single a b : α ->₀ M) a = b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Pi.single_eq_same`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) →
 Zero (M i)] [inst_1 : DecidableEq ι] (i : ι) (x : M i),   Pi.single i x i = x
-/
theorem single_eq_same : (single a b : α →₀ M) a = b := by
  classical exact Pi.single_eq_same (M := fun _ ↦ M) a b

@[simp]
/-
**Finsupp.single_eq_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：single_eq_of_ne (h : a' != a) : (single a b : α ->₀ M) a' = 0
参数：h : a' != a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Pi.single_eq_of_ne`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) 
→ Zero (M i)] [inst_1 : DecidableEq ι] {i i' : ι},   i' ≠ i → ∀ (x : M i), Pi.si
ngle i x…
-/
theorem single_eq_of_ne (h : a' ≠ a) : (single a b : α →₀ M) a' = 0 := by
  classical exact Pi.single_eq_of_ne h _

@[simp]
/-
**Finsupp.single_eq_of_ne'** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：single_eq_of_ne' (h : a != a') : (single a b : α ->₀ M) a' = 0
参数：h : a != a'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Pi.single_eq_of_ne'`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι)
 → Zero (M i)] [inst_1 : DecidableEq ι] {i i' : ι},   i ≠ i' → ∀ (x : M i), Pi.s
ingle i x…
-/
theorem single_eq_of_ne' (h : a ≠ a') : (single a b : α →₀ M) a' = 0 := by
  classical exact Pi.single_eq_of_ne' h _
/-
**Finsupp.single_eq_update** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：single_eq_update [DecidableEq α] (a : α) (b : M) : ⇑(single a b) = Functio
n.update (0 : _) a b
参数：a : α；b : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.single_eq_pi_single`：single_eq_pi_single [DecidableEq α] (a : α)
 (b : M) : ⇑(single a b) = Pi.single a b
-/
theorem single_eq_update [DecidableEq α] (a : α) (b : M) :
    ⇑(single a b) = Function.update (0 : _) a b :=
  single_eq_pi_single a b

@[simp, grind =]
/-
**Finsupp.single_zero** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：single_zero (a : α) : (single a 0 : α ->₀ M) = 0
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.single_eq_update`：single_eq_update [DecidableEq α] (a : α) (b : 
M) : ⇑(single a b) = Function.update (0 : _) a b
· 使用定理 `Function.update_eq_self`：update_eq_self (a : α) (f : forall a, β a) : up
date f a (f a) = f
-/
theorem single_zero (a : α) : (single a 0 : α →₀ M) = 0 :=
  DFunLike.coe_injective <| by
    classical simpa only [single_eq_update, coe_zero] using! Function.update_eq_self a (0 : α → M)
/-
**Finsupp.single_of_single_apply** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：single_of_single_apply (a a' : α) (b : M) : single a ((single a' b) a) = s
ingle a' (single a' b) a
参数：a a' : α；b : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem single_of_single_apply (a a' : α) (b : M) :
    single a ((single a' b) a) = single a' (single a' b) a := by
  classical
  grind
/-
**Finsupp.support_single** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：∀ {α : Type u_1} {M : Type u_5} [inst : Zero M] {b : M} (a : α), b ≠ 0 → (
fun₀ | a => b).support = {a}
参数：a : α；fun₀ | a => b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
@[simp] lemma support_single (a : α) (hb : b ≠ 0) : (single a b).support = {a} :=
  if_neg hb

@[deprecated (since := "2026-05-05")] alias support_single_ne_zero := support_single
/-
**Finsupp.support_single_subset** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：support_single_subset : (single a b).support subseteq {a}
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem support_single_subset : (single a b).support ⊆ {a} := by
  classical
  grind
/-
**Finsupp.single_apply_mem** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：single_apply_mem (x) : single a b x in ({0, b} : Set M)
参数：x。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem single_apply_mem (x) : single a b x ∈ ({0, b} : Set M) := by
  classical
  grind
/-
**Finsupp.range_single_subset** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：range_single_subset : Set.range (single a b) subseteq {0, b}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.range_subset_iff`：range_subset_iff : range f subseteq s ↔ forall y, 
f y in s
· 使用定理 `Finsupp.single_apply_mem`：single_apply_mem (x) : single a b x in ({0, b}
 : Set M)
-/
theorem range_single_subset : Set.range (single a b) ⊆ {0, b} :=
  Set.range_subset_iff.2 single_apply_mem

/-- `Finsupp.single a b` is injective in `b`. For the statement that it is injective in `a`, see
`Finsupp.single_left_injective` -/
/-
**Finsupp.single_injective** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：single_injective (a : α) : Function.Injective (single a : M -> α ->₀ M)
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b

--- 原说明 ---
`Finsupp.single a b` is injective in `b`. For the statement that it is injective
 in `a`, see
`Finsupp.single_left_injective`
-/
theorem single_injective (a : α) : Function.Injective (single a : M → α →₀ M) := fun b₁ b₂ eq => by
  have : (single a b₁ : α →₀ M) a = (single a b₂ : α →₀ M) a := by rw [eq]
  rwa [single_eq_same, single_eq_same] at this
/-
**Finsupp.single_apply_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：single_apply_eq_zero {a x : α} {b : M} : single a b x = 0 ↔ x = a -> b = 0
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
· 使用定理 `Finsupp.single_apply`：single_apply [Decidable (a = a')] : single a b a' 
= if a = a' then b else 0
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem single_apply_eq_zero {a x : α} {b : M} : single a b x = 0 ↔ x = a → b = 0 := by
  classical simp [single_apply, eq_comm]
/-
**Finsupp.single_apply_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：single_apply_ne_zero {a x : α} {b : M} : single a b x != 0 ↔ x = a ∧ b != 
0
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
theorem single_apply_ne_zero {a x : α} {b : M} : single a b x ≠ 0 ↔ x = a ∧ b ≠ 0 := by
  simp [single_apply_eq_zero]
/-
**Finsupp.mem_support_single** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：mem_support_single (a a' : α) (b : M) : a in (single a' b).support ↔ a = a
' ∧ b != 0
参数：a a' : α；b : M。
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
theorem mem_support_single (a a' : α) (b : M) : a ∈ (single a' b).support ↔ a = a' ∧ b ≠ 0 := by
  simp [single_apply_eq_zero]
/-
**Finsupp.eq_single_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：eq_single_iff {f : α ->₀ M} {a b} : f = single a b ↔ f.support subseteq {a
} ∧ f a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.support_single_subset`：support_single_subset : (single a b).supp
ort subseteq {a}
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finsupp.single_eq_of_ne`：single_eq_of_ne (h : a' != a) : (single a b : α
 ->₀ M) a' = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finsupp.notMem_support_iff`：notMem_support_iff {f : α ->₀ M} {a} : a ∉ f
.support ↔ f a = 0
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Finset.mem_singleton`：mem_singleton {a b : α} : b in ({a} : Finset α) ↔ 
b = a
-/
theorem eq_single_iff {f : α →₀ M} {a b} : f = single a b ↔ f.support ⊆ {a} ∧ f a = b := by
  refine ⟨fun h => h.symm ▸ ⟨support_single_subset, single_eq_same⟩, ?_⟩
  rintro ⟨h, rfl⟩
  ext x
  by_cases hx : x = a <;> simp only [hx, single_eq_same, single_eq_of_ne, Ne, not_false_iff]
  exact notMem_support_iff.1 (mt (fun hx => (mem_singleton.1 (h hx))) hx)
/-
**Finsupp.single_eq_single_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：single_eq_single_iff (a₁ a₂ : α) (b₁ b₂ : M) : single a₁ b₁ = single a₂ b₂
 ↔ a₁ = a₂ ∧ b₁ = b₂ ∨ b₁ = 0 ∧ b₂ = 0
参数：a₁ a₂ : α；b₁ b₂ : M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Finsupp.single_injective`：single_injective (a : α) : Function.Injective 
(single a : M -> α ->₀ M)
· 使用定理 `DFunLike.ext_iff`：ext_iff {f g : F} : f = g ↔ forall x, f x = g x
-/
theorem single_eq_single_iff (a₁ a₂ : α) (b₁ b₂ : M) :
    single a₁ b₁ = single a₂ b₂ ↔ a₁ = a₂ ∧ b₁ = b₂ ∨ b₁ = 0 ∧ b₂ = 0 := by
  classical
  constructor
  · intro eq
    by_cases h : a₁ = a₂
    · refine Or.inl ⟨h, ?_⟩
      rwa [h, (single_injective a₂).eq_iff] at eq
    · rw [DFunLike.ext_iff] at eq
      have h₁ := eq a₁
      have h₂ := eq a₂
      grind
  · grind

/-- `Finsupp.single a b` is injective in `a`. For the statement that it is injective in `b`, see
`Finsupp.single_injective` -/
/-
**Finsupp.single_left_injective** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：single_left_injective (h : b != 0) : Function.Injective fun a : α => singl
e a b
参数：h : b != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finsupp.single_eq_single_iff`：single_eq_single_iff (a₁ a₂ : α) (b₁ b₂ : 
M) : single a₁ b₁ = single a₂ b₂ ↔ a₁ = a₂ ∧ b₁ = b₂ ∨ b₁ = 0 ∧ b₂ = 0

--- 原说明 ---
`Finsupp.single a b` is injective in `a`. For the statement that it is injective
 in `b`, see
`Finsupp.single_injective`
-/
theorem single_left_injective (h : b ≠ 0) : Function.Injective fun a : α => single a b :=
  fun _a _a' H => (((single_eq_single_iff _ _ _ _).mp H).resolve_right fun hb => h hb.1).left
/-
**Finsupp.single_left_inj** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：single_left_inj (h : b != 0) : single a b = single a' b ↔ a = a'
参数：h : b != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Finsupp.single_left_injective`：single_left_injective (h : b != 0) : Func
tion.Injective fun a : α => single a b
-/
theorem single_left_inj (h : b ≠ 0) : single a b = single a' b ↔ a = a' :=
  (single_left_injective h).eq_iff
/-
**Finsupp.apply_surjective** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：apply_surjective (a : α) : Surjective fun f : α ->₀ M => f a
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.RightInverse.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α
 → β} {g : β → α}, Function.RightInverse g f → Function.Surjective f
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
-/
lemma apply_surjective (a : α) : Surjective fun f : α →₀ M ↦ f a :=
  RightInverse.surjective fun _ ↦ single_eq_same
/-
**Finsupp.support_single_ne_bot** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：support_single_ne_bot (i : α) (h : b != 0) : (single i b).support != ⊥
参数：i : α；h : b != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.support_single`：∀ {α : Type u_1} {M : Type u_5} [inst : Zero M] 
{b : M} (a : α), b ≠ 0 → (fun₀ | a => b).support = {a}
· 使用定理 `Finset.singleton_ne_empty`：singleton_ne_empty (a : α) : ({a} : Finset α)
 != ∅
-/
theorem support_single_ne_bot (i : α) (h : b ≠ 0) : (single i b).support ≠ ⊥ := by
  simpa only [support_single _ h] using! singleton_ne_empty _
/-
**Finsupp.support_single_disjoint** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：support_single_disjoint {b' : M} (hb : b != 0) (hb' : b' != 0) {i j : α} :
 Disjoint (single i b).support (single j b').support ↔ i != j
参数：hb : b != 0；hb' : b' != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.support_single`：∀ {α : Type u_1} {M : Type u_5} [inst : Zero M] 
{b : M} (a : α), b ≠ 0 → (fun₀ | a => b).support = {a}
· 使用定理 `Finset.disjoint_singleton`：disjoint_singleton : Disjoint ({a} : Finset α
) {b} ↔ a != b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem support_single_disjoint {b' : M} (hb : b ≠ 0) (hb' : b' ≠ 0) {i j : α} :
    Disjoint (single i b).support (single j b').support ↔ i ≠ j := by
  rw [support_single _ hb, support_single _ hb', disjoint_singleton]

@[simp]
/-
**Finsupp.single_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：single_eq_zero : single a b = 0 ↔ b = 0
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
· 使用定理 `Finsupp.single_apply`：single_apply [Decidable (a = a')] : single a b a' 
= if a = a' then b else 0
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem single_eq_zero : single a b = 0 ↔ b = 0 := by
  classical simp [DFunLike.ext_iff, single_apply]
/-
**Finsupp.single_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：single_ne_zero : single a b != 0 ↔ b != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Finsupp.single_eq_zero`：single_eq_zero : single a b = 0 ↔ b = 0
-/
theorem single_ne_zero : single a b ≠ 0 ↔ b ≠ 0 :=
  single_eq_zero.not
/-
**Finsupp.single_swap** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：single_swap (a₁ a₂ : α) (b : M) : single a₁ b a₂ = single a₂ b a₁
参数：a₁ a₂ : α；b : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.single_apply`：single_apply [Decidable (a = a')] : single a b a' 
= if a = a' then b else 0
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem single_swap (a₁ a₂ : α) (b : M) : single a₁ b a₂ = single a₂ b a₁ := by
  classical simp only [single_apply, eq_comm]
/-
**Finsupp.instNontrivial** 是 Mathlib 中的一个实例，位于命名空间 `Finsupp`。
形式化陈述：instNontrivial [Nonempty α] [Nontrivial M] : Nontrivial (α ->₀ M)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_ne`：exists_ne [Nontrivial α] (x : α) : exists y, y != x
· 使用定理 `nontrivial_of_ne`：nontrivial_of_ne (x y : α) (h : x != y) : Nontrivial α
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finsupp.single_eq_zero`：single_eq_zero : single a b = 0 ↔ b = 0
-/
instance instNontrivial [Nonempty α] [Nontrivial M] : Nontrivial (α →₀ M) := by
  inhabit α
  rcases exists_ne (0 : M) with ⟨x, hx⟩
  exact nontrivial_of_ne (single default x) 0 (mt single_eq_zero.1 hx)
/-
**Finsupp.nontrivial_iff** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：nontrivial_iff : Nontrivial (α ->₀ M) ↔ Nonempty α ∧ Nontrivial M where mp
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Finsupp.ne_iff`：ne_iff {f g : α ->₀ M} : f != g ↔ exists a, f a != g a
-/
lemma nontrivial_iff : Nontrivial (α →₀ M) ↔ Nonempty α ∧ Nontrivial M where
  mp := by
    rintro ⟨f, g, hfg⟩
    obtain ⟨a, ha⟩ := ne_iff.mp hfg
    exact ⟨⟨a⟩, _, _, ha⟩
  mpr | ⟨_, _⟩ => inferInstance
/-
**Finsupp.unique_single** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：unique_single [Unique α] (x : α ->₀ M) : x = single default (x default)
参数：x : α ->₀ M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Unique.forall_iff`：forall_iff {p : α -> Prop} : (forall a, p a) ↔ p defa
ult
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
-/
theorem unique_single [Unique α] (x : α →₀ M) : x = single default (x default) :=
  ext <| Unique.forall_iff.2 single_eq_same.symm

@[simp]
/-
**Finsupp.unique_single_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：unique_single_eq_iff [Unique α] {b' : M} : single a b = single a' b' ↔ b =
 b'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.unique_ext_iff`：∀ {α : Type u_1} {M : Type u_4} [inst : Zero M] 
[inst_1 : Unique α] {f g : α →₀ M}, f = g ↔ f default = g default
· 使用定理 `Unique.eq_default`：eq_default (a : α) : a = default
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem unique_single_eq_iff [Unique α] {b' : M} : single a b = single a' b' ↔ b = b' := by
  rw [Finsupp.unique_ext_iff, Unique.eq_default a, Unique.eq_default a', single_eq_same,
    single_eq_same]
/-
**Finsupp.apply_single'** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：apply_single' [Zero N] [Zero P] (e : N -> P) (he : e 0 = 0) (a : α) (n : N
) (b : α) : e ((single a n) b) = single a (e n) b
参数：e : N -> P；he : e 0 = 0；a : α；n : N；b : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma apply_single' [Zero N] [Zero P] (e : N → P) (he : e 0 = 0) (a : α) (n : N) (b : α) :
    e ((single a n) b) = single a (e n) b := by
  classical
  grind
/-
**Finsupp.support_eq_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：support_eq_singleton {f : α ->₀ M} {a : α} : f.support = {a} ↔ f a != 0 ∧ 
f = single a (f a)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finsupp.mem_support_iff`：mem_support_iff {f : α ->₀ M} : forall {a : α},
 a in f.support ↔ f a != 0
· 使用定理 `Finset.mem_singleton_self`：mem_singleton_self (a : α) : a in ({a} : Fins
et α)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finsupp.eq_single_iff`：eq_single_iff {f : α ->₀ M} {a b} : f = single a 
b ↔ f.support subseteq {a} ∧ f a = b
· 使用定理 `subset_of_eq`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preor
der α] {a b : α}, a = b → a ⊆ b
· 使用定理 `Finsupp.support_single`：∀ {α : Type u_1} {M : Type u_5} [inst : Zero M] 
{b : M} (a : α), b ≠ 0 → (fun₀ | a => b).support = {a}
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem support_eq_singleton {f : α →₀ M} {a : α} :
    f.support = {a} ↔ f a ≠ 0 ∧ f = single a (f a) :=
  ⟨fun h =>
    ⟨mem_support_iff.1 <| h.symm ▸ Finset.mem_singleton_self a,
      eq_single_iff.2 ⟨subset_of_eq h, rfl⟩⟩,
    fun h => h.2.symm ▸ support_single _ h.1⟩
/-
**Finsupp.support_eq_singleton'** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：support_eq_singleton' {f : α ->₀ M} {a : α} : f.support = {a} ↔ exists b !
= 0, f = single a b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finsupp.support_eq_singleton`：support_eq_singleton {f : α ->₀ M} {a : α}
 : f.support = {a} ↔ f a != 0 ∧ f = single a (f a)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Finsupp.support_single`：∀ {α : Type u_1} {M : Type u_5} [inst : Zero M] 
{b : M} (a : α), b ≠ 0 → (fun₀ | a => b).support = {a}
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem support_eq_singleton' {f : α →₀ M} {a : α} :
    f.support = {a} ↔ ∃ b ≠ 0, f = single a b :=
  ⟨fun h =>
    let h := support_eq_singleton.1 h
    ⟨_, h.1, h.2⟩,
    fun ⟨_b, hb, hf⟩ => hf.symm ▸ support_single _ hb⟩
/-
**Finsupp.card_support_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：card_support_eq_one {f : α ->₀ M} : #f.support = 1 ↔ exists a, f a != 0 ∧ 
f = single a (f a)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem card_support_eq_one {f : α →₀ M} :
    #f.support = 1 ↔ ∃ a, f a ≠ 0 ∧ f = single a (f a) := by
  simp only [card_eq_one, support_eq_singleton]
/-
**Finsupp.card_support_eq_one'** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：card_support_eq_one' {f : α ->₀ M} : #f.support = 1 ↔ exists a, exists b !
= 0, f = single a b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem card_support_eq_one' {f : α →₀ M} :
    #f.support = 1 ↔ ∃ a, ∃ b ≠ 0, f = single a b := by
  simp only [card_eq_one, support_eq_singleton']
/-
**Finsupp.support_subset_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：support_subset_singleton {f : α ->₀ M} {a : α} : f.support subseteq {a} ↔ 
f = single a (f a)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finsupp.eq_single_iff`：eq_single_iff {f : α ->₀ M} {a b} : f = single a 
b ↔ f.support subseteq {a} ∧ f a = b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
theorem support_subset_singleton {f : α →₀ M} {a : α} : f.support ⊆ {a} ↔ f = single a (f a) :=
  ⟨fun h => eq_single_iff.mpr ⟨h, rfl⟩, fun h => (eq_single_iff.mp h).left⟩
/-
**Finsupp.support_subset_singleton'** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：support_subset_singleton' {f : α ->₀ M} {a : α} : f.support subseteq {a} ↔
 exists b, f = single a b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finsupp.support_subset_singleton`：support_subset_singleton {f : α ->₀ M}
 {a : α} : f.support subseteq {a} ↔ f = single a (f a)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
-/
theorem support_subset_singleton' {f : α →₀ M} {a : α} : f.support ⊆ {a} ↔ ∃ b, f = single a b :=
  ⟨fun h => ⟨f a, support_subset_singleton.mp h⟩, fun ⟨b, hb⟩ => by
    rw [hb, support_subset_singleton, single_eq_same]⟩
/-
**Finsupp.card_support_le_one** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：card_support_le_one [Nonempty α] {f : α ->₀ M} : #f.support <= 1 ↔ exists 
a, f = single a (f a)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem card_support_le_one [Nonempty α] {f : α →₀ M} :
    #f.support ≤ 1 ↔ ∃ a, f = single a (f a) := by
  simp only [card_le_one_iff_subset_singleton, support_subset_singleton]
/-
**Finsupp.card_support_le_one'** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：card_support_le_one' [Nonempty α] {f : α ->₀ M} : #f.support <= 1 ↔ exists
 a b, f = single a b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem card_support_le_one' [Nonempty α] {f : α →₀ M} :
    #f.support ≤ 1 ↔ ∃ a b, f = single a b := by
  simp only [card_le_one_iff_subset_singleton, support_subset_singleton']

/-- If `α` has a unique term, then finitely supported functions `α →₀ M` are in bijection with `M`.
-/
@[simps]
/-
**Finsupp.uniqueEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp`。
形式化陈述：uniqueEquiv (a : α) [Subsingleton α] : (α ->₀ M) ≃ M where toFun f
参数：a : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `α` has a unique term, then finitely supported functions `α →₀ M` are in bije
ction with `M`.
-/
noncomputable def uniqueEquiv (a : α) [Subsingleton α] : (α →₀ M) ≃ M where
  toFun f := f a
  invFun := single a
  left_inv f := by ext b; simp [Subsingleton.elim b a]
  right_inv x := by simp

-- We want this lemma to fire before `uniqueEquiv_symm_apply`.
/-
**Finsupp.uniqueEquiv_symm_apply_apply** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：∀ {α : Type u_1} {M : Type u_5} [inst : Zero M] (a : α) [inst_1 : Subsingl
eton α] (m : M) (b : α),   ((Finsupp.uniqueEquiv a).symm m) b = m
参数：a : α；m : M；b : α；(Finsupp.uniqueEquiv a).symm m。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finsupp.uniqueEquiv_symm_apply`：∀ {α : Type u_1} {M : Type u_5} [inst : 
Zero M] (a : α) [inst_1 : Subsingleton α] (b : M),   (Finsupp.uniqueEquiv a).sym
m b = fun₀ | a => b
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp↓ high] lemma uniqueEquiv_symm_apply_apply (a : α) [Subsingleton α] (m : M) (b : α) :
    (uniqueEquiv a).symm m b = m := by simp [Subsingleton.elim b a]

/--
If `α` has a unique term, the type of finitely supported functions `α →₀ β` is equivalent to `β`.
-/
@[simps!, deprecated uniqueEquiv (since := "2026-05-06")]
/-
**Finsupp._root_.Equiv.finsuppUnique** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `α` has a unique term, the type of finitely supported functions `α →₀ β` is e
quivalent to `β`.
-/
noncomputable def _root_.Equiv.finsuppUnique {ι : Type*} [Unique ι] : (ι →₀ M) ≃ M :=
  Finsupp.equivFunOnFinite.trans (Equiv.funUnique ι M)

@[simp]
/-
**Finsupp.equivFunOnFinite_single** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：equivFunOnFinite_single [DecidableEq α] [Finite α] (x : α) (m : M) : Finsu
pp.equivFunOnFinite (Finsupp.single x m) = Pi.single x m
参数：x : α；m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.single_eq_pi_single`：single_eq_pi_single [DecidableEq α] (a : α)
 (b : M) : ⇑(single a b) = Pi.single a b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem equivFunOnFinite_single [DecidableEq α] [Finite α] (x : α) (m : M) :
    Finsupp.equivFunOnFinite (Finsupp.single x m) = Pi.single x m := by
  simp [Finsupp.single_eq_pi_single, equivFunOnFinite]

@[simp]
/-
**Finsupp.equivFunOnFinite_symm_single** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：equivFunOnFinite_symm_single [DecidableEq α] [Finite α] (x : α) (m : M) : 
Finsupp.equivFunOnFinite.symm (Pi.single x m) = Finsupp.single x m
参数：x : α；m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finsupp.equivFunOnFinite_single`：equivFunOnFinite_single [DecidableEq α]
 [Finite α] (x : α) (m : M) : Finsupp.equivFunOnFinite (Finsupp.single x m) = Pi
.single x m
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
-/
theorem equivFunOnFinite_symm_single [DecidableEq α] [Finite α] (x : α) (m : M) :
    Finsupp.equivFunOnFinite.symm (Pi.single x m) = Finsupp.single x m := by
  rw [← equivFunOnFinite_single, Equiv.symm_apply_apply]

end Single

/-! ### Declarations about `update` -/


section Update

variable [Zero M] (f : α →₀ M) (a : α) (b : M) (i : α)

/-- Replace the value of a `α →₀ M` at a given point `a : α` by a given value `b : M`.
If `b = 0`, this amounts to removing `a` from the `Finsupp.support`.
Otherwise, if `a` was not in the `Finsupp.support`, it is added to it.

This is the finitely-supported version of `Function.update`. -/
/-
**Finsupp.update** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp`。
形式化陈述：update (f : α ->₀ M) (a : α) (b : M) : α ->₀ M where support
参数：f : α ->₀ M；a : α；b : M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Replace the value of a `α →₀ M` at a given point `a : α` by a given value `b : M
`.
If `b = 0`, this amounts to removing `a` from the `Finsupp.support`.
Otherwise, if `a` was not in the `Finsupp.support`, it is added to it.

This is the finitely-supported version of `Function.update`.
-/
def update (f : α →₀ M) (a : α) (b : M) : α →₀ M where
  support := by
    haveI := Classical.decEq α; haveI := Classical.decEq M
    exact if b = 0 then f.support.erase a else insert a f.support
  toFun :=
    haveI := Classical.decEq α
    Function.update f a b
  mem_support_toFun i := by
    classical
    grind

@[grind =]
/-
**Finsupp.update_apply** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：update_apply [DecidableEq α] : (f.update a b) i = if i = a then b else f i
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem update_apply [DecidableEq α] : (f.update a b) i = if i = a then b else f i := by
  delta update Function.update
  grind

@[simp, norm_cast]
/-
**Finsupp.coe_update** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：coe_update [DecidableEq α] : (f.update a b : α -> M) = Function.update f a
 b
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_update [DecidableEq α] : (f.update a b : α → M) = Function.update f a b := by
  grind

@[simp]
/-
**Finsupp.update_self** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：update_self : f.update a (f a) = f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem update_self : f.update a (f a) = f := by
  classical
  grind

@[simp]
/-
**Finsupp.zero_update** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：zero_update : update 0 a b = single a b
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zero_update : update 0 a b = single a b := rfl
/-
**Finsupp.support_update** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：support_update [DecidableEq α] [DecidableEq M] : support (f.update a b) = 
if b = 0 then f.support.erase a else insert a f.support
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem support_update [DecidableEq α] [DecidableEq M] :
    support (f.update a b) = if b = 0 then f.support.erase a else insert a f.support := by
  grind

@[simp]
/-
**Finsupp.support_update_zero** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：support_update_zero [DecidableEq α] : support (f.update a 0) = f.support.e
rase a
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem support_update_zero [DecidableEq α] : support (f.update a 0) = f.support.erase a := by
  grind

variable {b}
/-
**Finsupp.support_update_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：support_update_ne_zero [DecidableEq α] (h : b != 0) : support (f.update a 
b) = insert a f.support
参数：h : b != 0。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem support_update_ne_zero [DecidableEq α] (h : b ≠ 0) :
    support (f.update a b) = insert a f.support := by
  grind
/-
**Finsupp.support_update_subset** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：support_update_subset [DecidableEq α] : support (f.update a b) subseteq in
sert a f.support
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem support_update_subset [DecidableEq α] :
    support (f.update a b) ⊆ insert a f.support := by
  grind
/-
**Finsupp.update_comm** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：update_comm (f : α ->₀ M) {a₁ a₂ : α} (h : a₁ != a₂) (m₁ m₂ : M) : update 
(update f a₁ m₁) a₂ m₂ = update (update f a₂ m₂) a₁ m₁
参数：f : α ->₀ M；h : a₁ != a₂；m₁ m₂ : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem update_comm (f : α →₀ M) {a₁ a₂ : α} (h : a₁ ≠ a₂) (m₁ m₂ : M) :
    update (update f a₁ m₁) a₂ m₂ = update (update f a₂ m₂) a₁ m₁ := by
  classical
  grind
/-
**Finsupp.update_idem** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：∀ {α : Type u_1} {M : Type u_5} [inst : Zero M] (f : α →₀ M) (a : α) (b c 
: M), (f.update a b).update a c = f.update a c
参数：f : α →₀ M；a : α；b c : M；f.update a b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem update_idem (f : α →₀ M) (a : α) (b c : M) :
    update (update f a b) a c = update f a c := by
  classical
  grind

end Update

/-! ### Declarations about `erase` -/


section Erase

variable [Zero M]

/--
`erase a f` is the finitely supported function equal to `f` except at `a` where it is equal to `0`.
If `a` is not in the support of `f` then `erase a f = f`.
-/
/-
**Finsupp.erase** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp`。
形式化陈述：erase (a : α) (f : α ->₀ M) : α ->₀ M where support
参数：a : α；f : α ->₀ M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`erase a f` is the finitely supported function equal to `f` except at `a` where 
it is equal to `0`.
If `a` is not in the support of `f` then `erase a f = f`.
-/
def erase (a : α) (f : α →₀ M) : α →₀ M where
  support :=
    haveI := Classical.decEq α
    f.support.erase a
  toFun a' :=
    haveI := Classical.decEq α
    if a' = a then 0 else f a'
  mem_support_toFun a' := by
    grind

@[grind =]
/-
**Finsupp.erase_apply** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：erase_apply [DecidableEq α] {a a' : α} {f : α ->₀ M} : f.erase a a' = if a
' = a then 0 else f a'
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.erase.eq_1`：∀ {α : Type u_1} {M : Type u_5} [inst : Zero M] (a :
 α) (f : α →₀ M),   Finsupp.erase a f =     { support := f.support.erase a, toFu
n := fun…
· 使用定理 `Finsupp.coe_mk`：coe_mk (f : α -> M) (s : Finset α) (h : forall a, a in s
 ↔ f a != 0) : ⇑(⟨s, f, h⟩ : α ->₀ M) = f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
theorem erase_apply [DecidableEq α] {a a' : α} {f : α →₀ M} :
    f.erase a a' = if a' = a then 0 else f a' := by
  rw [erase, coe_mk]
  simp only [ite_eq_ite]

@[simp]
/-
**Finsupp.support_erase** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：support_erase [DecidableEq α] {a : α} {f : α ->₀ M} : (f.erase a).support 
= f.support.erase a
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem support_erase [DecidableEq α] {a : α} {f : α →₀ M} :
    (f.erase a).support = f.support.erase a := by
  grind

@[simp]
/-
**Finsupp.erase_same** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：erase_same {a : α} {f : α ->₀ M} : (f.erase a) a = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem erase_same {a : α} {f : α →₀ M} : (f.erase a) a = 0 := by classical grind

@[simp]
/-
**Finsupp.erase_ne** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：erase_ne {a a' : α} {f : α ->₀ M} (h : a' != a) : (f.erase a) a' = f a'
参数：h : a' != a。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem erase_ne {a a' : α} {f : α →₀ M} (h : a' ≠ a) : (f.erase a) a' = f a' := by classical grind

@[simp]
/-
**Finsupp.erase_single** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：erase_single {a : α} {b : M} : erase a (single a b) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem erase_single {a : α} {b : M} : erase a (single a b) = 0 := by classical grind
/-
**Finsupp.erase_single_ne** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：erase_single_ne {a a' : α} {b : M} (h : a != a') : erase a (single a' b) =
 single a' b
参数：h : a != a'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem erase_single_ne {a a' : α} {b : M} (h : a ≠ a') : erase a (single a' b) = single a' b := by
  classical grind

@[simp]
/-
**Finsupp.erase_of_notMem_support** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：erase_of_notMem_support {f : α ->₀ M} {a} (haf : a ∉ f.support) : erase a 
f = f
参数：haf : a ∉ f.support。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem erase_of_notMem_support {f : α →₀ M} {a} (haf : a ∉ f.support) : erase a f = f := by
  classical grind
/-
**Finsupp.erase_zero** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：erase_zero (a : α) : erase a (0 : α ->₀ M) = 0
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.erase_of_notMem_support`：erase_of_notMem_support {f : α ->₀ M} {
a} (haf : a ∉ f.support) : erase a f = f
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem erase_zero (a : α) : erase a (0 : α →₀ M) = 0 := by
  simp
/-
**Finsupp.erase_eq_update_zero** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：erase_eq_update_zero (f : α ->₀ M) (a : α) : f.erase a = update f a 0
参数：f : α ->₀ M；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem erase_eq_update_zero (f : α →₀ M) (a : α) : f.erase a = update f a 0 := by classical grind

-- The name matches `Finset.erase_insert_of_ne`
/-
**Finsupp.erase_update_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：erase_update_of_ne (f : α ->₀ M) {a a' : α} (ha : a != a') (b : M) : erase
 a (update f a' b) = update (erase a f) a' b
参数：f : α ->₀ M；ha : a != a'；b : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem erase_update_of_ne (f : α →₀ M) {a a' : α} (ha : a ≠ a') (b : M) :
    erase a (update f a' b) = update (erase a f) a' b := by classical grind

-- not `simp` as `erase_of_notMem_support` can prove this
/-
**Finsupp.erase_idem** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：erase_idem (f : α ->₀ M) (a : α) : erase a (erase a f) = erase a f
参数：f : α ->₀ M；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem erase_idem (f : α →₀ M) (a : α) :
    erase a (erase a f) = erase a f := by classical grind
/-
**Finsupp.update_erase_eq_update** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：∀ {α : Type u_1} {M : Type u_5} [inst : Zero M] (f : α →₀ M) (a : α) (b : 
M),   (Finsupp.erase a f).update a b = f.update a b
参数：f : α →₀ M；a : α；b : M；Finsupp.erase a f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem update_erase_eq_update (f : α →₀ M) (a : α) (b : M) :
    update (erase a f) a b = update f a b := by classical grind
/-
**Finsupp.erase_update_eq_erase** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：∀ {α : Type u_1} {M : Type u_5} [inst : Zero M] (f : α →₀ M) (a : α) (b : 
M),   Finsupp.erase a (f.update a b) = Finsupp.erase a f
参数：f : α →₀ M；a : α；b : M；f.update a b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem erase_update_eq_erase (f : α →₀ M) (a : α) (b : M) :
    erase a (update f a b) = erase a f := by classical grind

end Erase

/-! ### Declarations about `mapRange` -/

section MapRange

variable [Zero M] [Zero N] [Zero P]

@[simp]
/-
**Finsupp.mapRange_single** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：mapRange_single {f : M -> N} {hf : f 0 = 0} {a : α} {b : M} : mapRange f h
f (single a b) = single a (f b)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapRange_single {f : M → N} {hf : f 0 = 0} {a : α} {b : M} :
    mapRange f hf (single a b) = single a (f b) := by
  classical grind

end MapRange

/-! ### Declarations about `embDomain` -/


section EmbDomain

variable [Zero M] [Zero N]

/-
**Finsupp.single_of_embDomain_single** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：single_of_embDomain_single (l : α ->₀ M) (f : α ↪ β) (a : β) (b : M) (hb :
 b != 0) (h : l.embDomain f = single a b) : exists x, l = single x b ∧ f x = a
参数：l : α ->₀ M；f : α ↪ β；a : β；b : M；hb : b != 0；h : l.embDomain f = single a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finsupp.support_embDomain`：support_embDomain (f : α ↪ β) (v : α ->₀ M) :
 (embDomain f v).support = v.support.map f
· 使用定理 `Finsupp.support_single`：∀ {α : Type u_1} {M : Type u_5} [inst : Zero M] 
{b : M} (a : α), b ≠ 0 → (fun₀ | a => b).support = {a}
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_map`：mem_map {b : β} : b in s.map f ↔ exists a in s, f a = b
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `Finsupp.embDomain_apply_self`：embDomain_apply_self (f : α ↪ β) (v : α ->
₀ M) (a : α) : embDomain f v (f a) = v a
-/
theorem single_of_embDomain_single (l : α →₀ M) (f : α ↪ β) (a : β) (b : M) (hb : b ≠ 0)
    (h : l.embDomain f = single a b) : ∃ x, l = single x b ∧ f x = a := by
  classical
    have h_map_support : Finset.map f l.support = {a} := by
      rw [← support_embDomain, h, support_single _ hb]
    have ha : a ∈ Finset.map f l.support := by simp only [h_map_support, Finset.mem_singleton]
    rcases Finset.mem_map.1 ha with ⟨c, _hc₁, hc₂⟩
    use c
    constructor
    · ext d
      rw [← embDomain_apply_self f l, h]
      grind
    · exact hc₂

@[simp]
/-
**Finsupp.embDomain_single** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：embDomain_single (f : α ↪ β) (a : α) (m : M) : embDomain f (single a m) = 
single (f a) m
参数：f : α ↪ β；a : α；m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
-/
theorem embDomain_single (f : α ↪ β) (a : α) (m : M) :
    embDomain f (single a m) = single (f a) m := by
  classical
    ext b
    by_cases h : b ∈ Set.range f <;> grind

end EmbDomain

/-! ### Declarations about `zipWith` -/


section ZipWith

variable [Zero M] [Zero N] [Zero P]

@[simp]
/-
**Finsupp.zipWith_single_single** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：zipWith_single_single (f : M -> N -> P) (hf : f 0 0 = 0) (a : α) (m : M) (
n : N) : zipWith f hf (single a m) (single a n) = single a (f m n)
参数：f : M -> N -> P；hf : f 0 0 = 0；a : α；m : M；n : N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zipWith_single_single (f : M → N → P) (hf : f 0 0 = 0) (a : α) (m : M) (n : N) :
    zipWith f hf (single a m) (single a n) = single a (f m n) := by
  classical
  grind

end ZipWith
end Finsupp

