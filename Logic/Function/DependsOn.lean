/-
Copyright (c) 2024 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
module

public import Mathlib.Data.Set.Restrict
public import Mathlib.Util.Delaborators

/-!
# Functions depending only on some variables

When dealing with a function `f : Π i, α i` depending on many variables, some operations
may get rid of the dependency on some variables (see `Function.updateFinset` or
`MeasureTheory.lmarginal` for example). However considering this new function
as having a different domain with fewer points is not comfortable in Lean, as it requires the use
of subtypes and can lead to tedious writing.

On the other hand one wants to be able for example to describe some function as constant
with respect to some variables, and be able to deduce this when applying transformations
mentioned above. This is why we introduce the predicate `DependsOn f s`, which states that
if `x` and `y` coincide over the set `s`, then `f x = f y`.
This is equivalent to `Function.FactorsThrough f s.domRestrict`.

## Main definition

* `DependsOn f s`: If `x` and `y` coincide over the set `s`, then `f x` equals `f y`.

## Main statement

* `dependsOn_iff_factorsThrough`: A function `f` depends on `s` if and only if it factors
  through `s.domRestrict`.

## Implementation notes

When we write `DependsOn f s`, i.e. `f` only depends on `s`, it should be interpreted as
"`f` _potentially_ depends only on variables in `s`". However it might be the case
that `f` does not depend at all on variables in `s`, for example if `f` is constant.
As a consequence, `DependsOn f univ` is always true, see `dependsOn_univ`.

The predicate `DependsOn f s` can also be interpreted as saying that `f` is independent of all
the variables which are not in `s`. Although this phrasing might seem more natural, we choose to go
with `DependsOn` because writing mathematically "independent of variables in `s`" would boil down to
`∀ x y, (∀ i ∉ s, x i = y i) → f x = f y`, which is the same as `DependsOn f sᶜ`.

## Tags

depends on
-/

@[expose] public section

open Function Set

variable {ι : Type*} {α : ι → Type*} {β : Type*}

/-- A function `f` depends on `s` if, whenever `x` and `y` coincide over `s`, `f x = f y`.

It should be interpreted as "`f` _potentially_ depends only on variables in `s`".
However it might be the case that `f` does not depend at all on variables in `s`,
for example if `f` is constant. As a consequence, `DependsOn f univ` is always true,
see `dependsOn_univ`. -/
/-
**DependsOn** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：DependsOn (f : (Π i, α i) -> β) (s : Set ι) : Prop
参数：f : (Π i, α i) -> β；s : Set ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function `f` depends on `s` if, whenever `x` and `y` coincide over `s`, `f x =
 f y`.

It should be interpreted as "`f` _potentially_ depends only on variables in `s`"
.
However it might be the case that `f` does not depend at all on variables in `s`
,
for example if `f` is constant. As a consequence, `DependsOn f univ` is always t
rue,
see `dependsOn_univ`.
-/
def DependsOn (f : (Π i, α i) → β) (s : Set ι) : Prop :=
  ∀ ⦃x y⦄, (∀ i ∈ s, x i = y i) → f x = f y
/-
**dependsOn_iff_factorsThrough** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：dependsOn_iff_factorsThrough {f : (Π i, α i) -> β} {s : Set ι} : DependsOn
 f s ↔ FactorsThrough f s.domRestrict
参数：Π i, α i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DependsOn.eq_1`：∀ {ι : Type u_1} {α : ι → Type u_2} {β : Type u_3} (f : 
((i : ι) → α i) → β) (s : Set ι),   DependsOn f s = ∀ ⦃x y : (i : ι) → α i⦄, (∀ 
i ∈ …
· 使用定理 `Function.FactorsThrough.eq_1`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort 
u_3} (g : α → γ) (f : α → β),   Function.FactorsThrough g f = ∀ ⦃a b : α⦄, f a =
 f b → g a = g b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma dependsOn_iff_factorsThrough {f : (Π i, α i) → β} {s : Set ι} :
    DependsOn f s ↔ FactorsThrough f s.domRestrict := by
  rw [DependsOn, FactorsThrough]
  simp [funext_iff]
/-
**dependsOn_iff_exists_comp** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：dependsOn_iff_exists_comp [Nonempty β] {f : (Π i, α i) -> β} {s : Set ι} :
 DependsOn f s ↔ exists g : (Π i : s, α i) -> β, f = g ∘ s.domRestrict
参数：Π i, α i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `dependsOn_iff_factorsThrough`：dependsOn_iff_factorsThrough {f : (Π i, α 
i) -> β} {s : Set ι} : DependsOn f s ↔ FactorsThrough f s.domRestrict
· 使用引理 `Function.factorsThrough_iff`：factorsThrough_iff (g : α -> γ) [Nonempty γ
] : g.FactorsThrough f ↔ exists (e : β -> γ), g = e ∘ f
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma dependsOn_iff_exists_comp [Nonempty β] {f : (Π i, α i) → β} {s : Set ι} :
    DependsOn f s ↔ ∃ g : (Π i : s, α i) → β, f = g ∘ s.domRestrict := by
  rw [dependsOn_iff_factorsThrough, factorsThrough_iff]
/-
**dependsOn_univ** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：dependsOn_univ (f : (Π i, α i) -> β) : DependsOn f univ
参数：f : (Π i, α i) -> β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `trivial`：True
-/
lemma dependsOn_univ (f : (Π i, α i) → β) : DependsOn f univ :=
  fun _ _ h ↦ congrArg _ <| funext fun i ↦ h i trivial

variable {f : (Π i, α i) → β}

/-- A constant function does not depend on any variable. -/
/-
**dependsOn_const** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：dependsOn_const (b : β) : DependsOn (fun _ : Π i, α i => b) ∅
参数：b : β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
A constant function does not depend on any variable.
-/
lemma dependsOn_const (b : β) : DependsOn (fun _ : Π i, α i ↦ b) ∅ := by simp [DependsOn]
/-
**DependsOn.mono** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：DependsOn.mono {s t : Set ι} (hst : s subseteq t) (hf : DependsOn f s) : D
ependsOn f t
参数：hst : s subseteq t；hf : DependsOn f s。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma DependsOn.mono {s t : Set ι} (hst : s ⊆ t) (hf : DependsOn f s) : DependsOn f t :=
  fun _ _ h ↦ hf fun i hi ↦ h i (hst hi)

/-- A function which depends on the empty set is constant. -/
/-
**DependsOn.empty** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：DependsOn.empty (hf : DependsOn f ∅) (x y : Π i, α i) : f x = f y
参数：hf : DependsOn f ∅；x y : Π i, α i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
A function which depends on the empty set is constant.
-/
lemma DependsOn.empty (hf : DependsOn f ∅) (x y : Π i, α i) : f x = f y := hf (by simp)
/-
**Set.dependsOn_domRestrict** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Set.dependsOn_domRestrict (s : Set ι) : DependsOn (s.domRestrict (π
参数：s : Set ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
lemma Set.dependsOn_domRestrict (s : Set ι) : DependsOn (s.domRestrict (π := α)) s :=
  fun _ _ h ↦ funext fun i ↦ h i.1 i.2

@[deprecated (since := "2026-07-19")] alias Set.dependsOn_restrict := Set.dependsOn_domRestrict
