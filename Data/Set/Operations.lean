/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Johannes Hölzl, Reid Barton, Kim Morrison, Patrick Massot, Kyle Miller,
Minchao Wu, Yury Kudryashov, Floris van Doorn
-/
module

public import Mathlib.Data.Set.CoeSort
public import Mathlib.Data.SProd
public import Mathlib.Data.Subtype
public import Mathlib.Order.Notation
public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Tactic.Push.Attr

import Mathlib.Tactic.Attr.Register
import Aesop.BuiltinRules
import Aesop.Frontend.Tactic
import Aesop.Main

/-!
# Basic definitions about sets

In this file we define various operations on sets.
We also provide basic lemmas needed to unfold the definitions.
More advanced theorems about these definitions are located in other files in `Mathlib/Data/Set`.

## Main definitions

- complement of a set and set difference;
- `Set.preimage f s`, a.k.a. `f ⁻¹' s`: preimage of a set;
- `Set.range f`: the range of a function;
  it is more general than `f '' univ` because it allows functions from `Sort*`;
- `s ×ˢ t`: product of `s : Set α` and `t : Set β` as a set in `α × β`;
- `Set.diagonal`: the diagonal in `α × α`;
- `Set.offDiag s`: the part of `s ×ˢ s` that is off the diagonal;
- `Set.pi`: indexed product of a family of sets `∀ i, Set (α i)`,
  as a set in `∀ i, α i`;
- `Set.EqOn f g s`: the predicate saying that two functions are equal on a set;
- `Set.MapsTo f s t`: the predicate saying that `f` sends all points of `s` to `t`;
- `Set.MapsTo.restrict`: restrict `f : α → β` to `f' : s → t` provided that `Set.MapsTo f s t`;
- `Set.restrictPreimage`: restrict `f : α → β` to `f' : (f ⁻¹' t) → t`;
- `Set.InjOn`: the predicate saying that `f` is injective on a set;
- `Set.SurjOn f s t`: the predicate saying that `t ⊆ f '' s`;
- `Set.BijOn f s t`: the predicate saying that `f` is injective on `s` and `f '' s = t`;
- `Set.graphOn`: the graph of a function on a set;
- `Set.LeftInvOn`, `Set.RightInvOn`, `Set.InvOn`:
  the predicates saying that `f'` is a left, right or two-sided inverse of `f` on `s`, `t`, or both;
- `Set.image2`: the image of a pair of sets under a binary operation,
  mostly useful to define pointwise algebraic operations on sets;
- `Set.seq`: monadic `seq` operation on sets;
  we don't use monadic notation to ensure support for maps between different universes.

## Notation

- `f '' s`: image of a set;
- `f ⁻¹' s`: preimage of a set;
- `s ×ˢ t`: the product of sets;
- `s ∪ t`: the union of two sets;
- `s ∩ t`: the intersection of two sets;
- `sᶜ`: the complement of a set;
- `s \ t`: the difference of two sets.

## Keywords

set, image, preimage
-/

@[expose] public section

universe u v w

namespace Set

variable {α : Type u} {β : Type v} {γ : Type w}

/-! ### Lemmas about `mem` and `Set.ofPred` -/

@[simp, mfld_simps, push]
/-
**Set.mem_ofPred_eq** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mem_ofPred_eq {x : α} {p : α -> Prop} : (x in {y | p y}) = p x
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Lemmas about `mem` and `Set.ofPred`
-/
theorem mem_ofPred_eq {x : α} {p : α → Prop} : (x ∈ {y | p y}) = p x := rfl

@[deprecated (since := "2026-07-09")] alias mem_setOf_eq := mem_ofPred_eq

grind_pattern mem_ofPred_eq => x ∈ Set.ofPred p

/-- This lemma is intended for use with `rw` where a membership predicate is needed,
hence the explicit argument and the equality in the reverse direction from normal.
See also `Set.mem_ofPred_eq` for the reverse direction applied to an argument. -/
/-
**Set.eq_mem_ofPred** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：eq_mem_ofPred (p : α -> Prop) : p = (· in {a | p a})
参数：p : α -> Prop。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This lemma is intended for use with `rw` where a membership predicate is needed,
hence the explicit argument and the equality in the reverse direction from norma
l.
See also `Set.mem_ofPred_eq` for the reverse direction applied to an argument.
-/
theorem eq_mem_ofPred (p : α → Prop) : p = (· ∈ {a | p a}) := rfl

@[deprecated (since := "2026-07-09")] alias eq_mem_setOf := eq_mem_ofPred
/-
**Set.mem_ofPred** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mem_ofPred {a : α} {p : α -> Prop} : a in { x | p x } ↔ p a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_ofPred {a : α} {p : α → Prop} : a ∈ { x | p x } ↔ p a := Iff.rfl

@[deprecated (since := "2026-07-09")] alias mem_setOf := mem_ofPred

/-- If `h : a ∈ {x | p x}` then `h.out : p x`. These are definitionally equal, but this can
nevertheless be useful for various reasons, e.g. to apply further projection notation or in an
argument to `simp`. -/
alias ⟨_root_.Membership.mem.out, _⟩ := mem_ofPred

/-
**Set.notMem_ofPred_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：notMem_ofPred_iff {a : α} {p : α -> Prop} : a ∉ { x | p x } ↔ ¬p a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem notMem_ofPred_iff {a : α} {p : α → Prop} : a ∉ { x | p x } ↔ ¬p a := Iff.rfl

@[deprecated (since := "2026-07-09")] alias notMem_setOf_iff := notMem_ofPred_iff
/-
**Set.ofPred_mem_eq** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u} {s : Set α}, {x | x ∈ s} = s
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem ofPred_mem_eq {s : Set α} : { x | x ∈ s } = s := rfl

@[deprecated (since := "2026-07-09")] alias setOf_mem_eq := ofPred_mem_eq

@[simp, mfld_simps, grind ←, push]
/-
**Set.mem_univ** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mem_univ (x : α) : x in @univ α
参数：x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `trivial`：True
-/
theorem mem_univ (x : α) : x ∈ @univ α := trivial

/-! ### Operations -/

/-
**Set.** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Operations
-/
instance : Compl (Set α) := ⟨fun s ↦ {x | x ∉ s}⟩

@[simp, grind =, push]
/-
**Set.mem_compl_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mem_compl_iff (s : Set α) (x : α) : x in sᶜ ↔ x ∉ s
参数：s : Set α；x : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_compl_iff (s : Set α) (x : α) : x ∈ sᶜ ↔ x ∉ s := Iff.rfl
/-
**Set.sdiff_eq** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sdiff_eq (s t : Set α) : s \ t = s inter tᶜ
参数：s t : Set α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sdiff_eq (s t : Set α) : s \ t = s ∩ tᶜ := rfl

@[deprecated (since := "2026-06-03")] alias diff_eq := sdiff_eq

@[simp, grind =, push]
/-
**Set.mem_sdiff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mem_sdiff {s t : Set α} (x : α) : x in s \ t ↔ x in s ∧ x ∉ t
参数：x : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_sdiff {s t : Set α} (x : α) : x ∈ s \ t ↔ x ∈ s ∧ x ∉ t := Iff.rfl

@[deprecated (since := "2026-06-03")] alias mem_diff := mem_sdiff
/-
**Set.mem_sdiff_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mem_sdiff_of_mem {s t : Set α} {x : α} (h1 : x in s) (h2 : x ∉ t) : x in s
 \ t
参数：h1 : x in s；h2 : x ∉ t。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mem_sdiff_of_mem {s t : Set α} {x : α} (h1 : x ∈ s) (h2 : x ∉ t) : x ∈ s \ t := ⟨h1, h2⟩

@[deprecated (since := "2026-06-03")] alias mem_diff_of_mem := mem_sdiff_of_mem

/-- The preimage of `s : Set β` by `f : α → β`, written `f ⁻¹' s`,
  is the set of `x : α` such that `f x ∈ s`. -/
@[implicit_reducible]
/-
**Set.preimage** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：preimage (f : α -> β) (s : Set β) : Set α
参数：f : α -> β；s : Set β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The preimage of `s : Set β` by `f : α → β`, written `f ⁻¹' s`,
  is the set of `x : α` such that `f x ∈ s`.
-/
def preimage (f : α → β) (s : Set β) : Set α := {x | f x ∈ s}

/-- `f ⁻¹' t` denotes the preimage of `t : Set β` under the function `f : α → β`. -/
infixr:80 " ⁻¹' " => preimage

@[simp, mfld_simps, grind =, push]
/-
**Set.mem_preimage** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mem_preimage {f : α -> β} {s : Set β} {a : α} : a in f ⁻¹' s ↔ f a in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_preimage {f : α → β} {s : Set β} {a : α} : a ∈ f ⁻¹' s ↔ f a ∈ s := Iff.rfl

/-- `f '' s` denotes the image of `s : Set α` under the function `f : α → β`. -/
infixr:80 " '' " => image

@[simp, grind =, push]
/-
**Set.mem_image** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mem_image (f : α -> β) (s : Set α) (y : β) : y in f '' s ↔ exists x in s, 
f x = y
参数：f : α -> β；s : Set α；y : β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_image (f : α → β) (s : Set α) (y : β) : y ∈ f '' s ↔ ∃ x ∈ s, f x = y :=
  Iff.rfl

@[mfld_simps]
/-
**Set.mem_image_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} (h : x in a) : f x in f 
'' a
参数：f : α -> β；h : x in a。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mem_image_of_mem (f : α → β) {x : α} {a : Set α} (h : x ∈ a) : f x ∈ f '' a :=
  ⟨_, h, rfl⟩

/-- Restriction of `f` to `s` factors through `s.imageFactorization f : s → f '' s`. -/
/-
**Set.imageFactorization** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：imageFactorization (f : α -> β) (s : Set α) : s -> f '' s
参数：f : α -> β；s : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Restriction of `f` to `s` factors through `s.imageFactorization f : s → f '' s`.
-/
def imageFactorization (f : α → β) (s : Set α) : s → f '' s := fun p =>
  ⟨f p.1, mem_image_of_mem f p.2⟩

/-- `kernImage f s` is the set of `y` such that `f ⁻¹ y ⊆ s`. -/
/-
**Set.kernImage** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：kernImage (f : α -> β) (s : Set α) : Set β
参数：f : α -> β；s : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`kernImage f s` is the set of `y` such that `f ⁻¹ y ⊆ s`.
-/
def kernImage (f : α → β) (s : Set α) : Set β := {y | ∀ ⦃x⦄, f x = y → x ∈ s}
/-
**Set.subset_kernImage_iff** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：subset_kernImage_iff {s : Set β} {t : Set α} {f : α -> β} : s subseteq ker
nImage f t ↔ f ⁻¹' s subseteq t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma subset_kernImage_iff {s : Set β} {t : Set α} {f : α → β} : s ⊆ kernImage f t ↔ f ⁻¹' s ⊆ t :=
  ⟨fun h _ hx ↦ h hx rfl,
    fun h _ hx y hy ↦ h (show f y ∈ s from hy.symm ▸ hx)⟩

section Range

variable {ι : Sort*} {f : ι → α}

/-- Range of a function.

This function is more flexible than `f '' univ`, as the image requires that the domain is in Type
and not an arbitrary Sort. -/
/-
**Set.range** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：range (f : ι -> α) : Set α
参数：f : ι -> α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Range of a function.

This function is more flexible than `f '' univ`, as the image requires that the 
domain is in Type
and not an arbitrary Sort.
-/
def range (f : ι → α) : Set α := {x | ∃ y, f y = x}
/-
**Set.mem_range** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} {x : α}, x ∈ Set.range f ↔ ∃ y, 
f y = x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp, grind =, push] theorem mem_range {x : α} : x ∈ range f ↔ ∃ y, f y = x := Iff.rfl
/-
**Set.mem_range_self** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f i ∈ Set.range f
参数：i : ι。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[mfld_simps] theorem mem_range_self (i : ι) : f i ∈ range f := ⟨i, rfl⟩

/-- Any map `f : ι → α` factors through a map `rangeFactorization f : ι → range f`. -/
/-
**Set.rangeFactorization** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：rangeFactorization (f : ι -> α) : ι -> range f
参数：f : ι -> α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f

--- 原说明 ---
Any map `f : ι → α` factors through a map `rangeFactorization f : ι → range f`.
-/
def rangeFactorization (f : ι → α) : ι → range f := fun i => ⟨f i, mem_range_self i⟩
/-
**Set.rangeFactorization_injective** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u} {ι : Sort u_1} {f : ι → α}, Function.Injective (Set.rangeFa
ctorization f) ↔ Function.Injective f
参数：Set.rangeFactorization f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma rangeFactorization_injective :
    (Set.rangeFactorization f).Injective ↔ f.Injective := by
  simp [Function.Injective, rangeFactorization]
/-
**Set.rangeFactorization_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u} {ι : Sort u_1} {f : ι → α}, Function.Surjective (Set.rangeF
actorization f)
参数：Set.rangeFactorization f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma rangeFactorization_surjective : (rangeFactorization f).Surjective :=
  fun ⟨_, i, rfl⟩ ↦ ⟨i, rfl⟩
/-
**Set.rangeFactorization_bijective** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u} {ι : Sort u_1} {f : ι → α}, Function.Bijective (Set.rangeFa
ctorization f) ↔ Function.Injective f
参数：Set.rangeFactorization f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma rangeFactorization_bijective :
    (Set.rangeFactorization f).Bijective ↔ f.Injective := by simp [Function.Bijective]
/-
**Set.rangeFactorization_eq_rangeFactorization_iff** 是 Mathlib 中的一个定理，位于命名空间 `Se
t`。
形式化陈述：∀ {ι : Sort u_2} {α : Type u_3} {f : ι → α} (a b : ι),   Set.rangeFactoriz
ation f a = Set.rangeFactorization f b ↔ f a = f b
参数：a b : ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma rangeFactorization_eq_rangeFactorization_iff {ι : Sort*} {α : Type*} {f : ι → α}
    (a b : ι) : Set.rangeFactorization f a = Set.rangeFactorization f b ↔ f a = f b := by
  simp [Set.rangeFactorization]
/-
**Set.rangeFactorization_eq_iff** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：rangeFactorization_eq_iff {ι : Sort*} {α : Type*} {f : ι -> α} (a : ι) (b 
: Set.range f) : Set.rangeFactorization f a = b ↔ f a = b
参数：a : ι；b : Set.range f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.rangeFactorization.eq_1`：∀ {α : Type u} {ι : Sort u_1} (f : ι → α) (
i : ι), Set.rangeFactorization f i = ⟨f i, ⋯⟩
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.coe_eta`：coe_eta (a : { a // p a }) (h : p a) : mk (↑a) h = a
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma rangeFactorization_eq_iff {ι : Sort*} {α : Type*} {f : ι → α} (a : ι) (b : Set.range f) :
    Set.rangeFactorization f a = b ↔ f a = b := by
  rw [Set.rangeFactorization, ← b.coe_eta b.2, Subtype.ext_iff]

end Range

/-- We can use the axiom of choice to pick a preimage for every element of `range f`. -/
/-
**Set.rangeSplitting** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：rangeSplitting (f : α -> β) : range f -> α
参数：f : α -> β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We can use the axiom of choice to pick a preimage for every element of `range f`
.
-/
noncomputable def rangeSplitting (f : α → β) : range f → α := fun x => x.2.choose

-- This cannot be a `@[simp]` lemma because the head of the left-hand side is a variable.
/-
**Set.apply_rangeSplitting** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：apply_rangeSplitting (f : α -> β) (x : range f) : f (rangeSplitting f x) =
 x
参数：f : α -> β；x : range f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem apply_rangeSplitting (f : α → β) (x : range f) : f (rangeSplitting f x) = x :=
  x.2.choose_spec

@[simp]
/-
**Set.comp_rangeSplitting** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：comp_rangeSplitting (f : α -> β) : f ∘ rangeSplitting f = Subtype.val
参数：f : α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.apply_rangeSplitting`：apply_rangeSplitting (f : α -> β) (x : range f
) : f (rangeSplitting f x) = x
-/
theorem comp_rangeSplitting (f : α → β) : f ∘ rangeSplitting f = Subtype.val := by
  ext
  simp only [Function.comp_apply]
  apply apply_rangeSplitting
/-
**Set.Subtype.range_coind** 是 Mathlib 中的一个定理，位于命名空间 `Set.Subtype`。
形式化陈述：∀ {α : Type u} {β : Type v} (f : α → β) {p : β → Prop} (h : ∀ (a : α), p (
f a)),   Set.range (Subtype.coind f h) = Subtype.val ⁻¹' Set.range f
参数：f : α → β；h : ∀ (a : α), p (f a)；Subtype.coind f h。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Subtype.coind_coe`：∀ {α : Sort u_4} {β : Sort u_5} (f : α → β) {p : β → 
Prop} (h : ∀ (a : α), p (f a)) (a : α),   ↑(Subtype.coind f h a) = f a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma Subtype.range_coind (f : α → β) {p : β → Prop} (h : ∀ (a : α), p (f a)) :
    range (Subtype.coind f h) = Subtype.val ⁻¹' range f := by
  simp [Set.ext_iff, Subtype.ext_iff]

section Prod

/-- The Cartesian product `Set.prod s t` is the set of `(a, b)` such that `a ∈ s` and `b ∈ t`. -/
@[wikidata Q173740]
/-
**Set.prod** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：prod (s : Set α) (t : Set β) : Set (α × β)
参数：s : Set α；t : Set β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Cartesian product `Set.prod s t` is the set of `(a, b)` such that `a ∈ s` an
d `b ∈ t`.
-/
def prod (s : Set α) (t : Set β) : Set (α × β) := {p | p.1 ∈ s ∧ p.2 ∈ t}

@[default_instance]
/-
**Set.instSProd** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
形式化陈述：instSProd : SProd (Set α) (Set β) (Set (α × β)) where sprod
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSProd : SProd (Set α) (Set β) (Set (α × β)) where
  sprod := Set.prod
/-
**Set.prod_eq** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：prod_eq (s : Set α) (t : Set β) : s ×ˢ t = Prod.fst ⁻¹' s inter Prod.snd ⁻
¹' t
参数：s : Set α；t : Set β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prod_eq (s : Set α) (t : Set β) : s ×ˢ t = Prod.fst ⁻¹' s ∩ Prod.snd ⁻¹' t := rfl

variable {a : α} {b : β} {s : Set α} {t : Set β} {p : α × β}
/-
**Set.mem_prod_eq** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mem_prod_eq : (p in s ×ˢ t) = (p.1 in s ∧ p.2 in t)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mem_prod_eq : (p ∈ s ×ˢ t) = (p.1 ∈ s ∧ p.2 ∈ t) := rfl

@[simp, mfld_simps, grind =, push]
/-
**Set.mem_prod** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mem_prod : p in s ×ˢ t ↔ p.1 in s ∧ p.2 in t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_prod : p ∈ s ×ˢ t ↔ p.1 ∈ s ∧ p.2 ∈ t := .rfl

@[mfld_simps, push only high] /- This `push` lemma is so that `(a, b) ∈ s ×ˢ t` gets turned
into `a ∈ s ∧ b ∈ t`, instead of getting `(a, b).1` and `(a, b).2`. -/
/-
**Set.prodMk_mem_set_prod_eq** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：prodMk_mem_set_prod_eq : ((a, b) in s ×ˢ t) = (a in s ∧ b in t)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This `push` lemma is so that `(a, b) ∈ s ×ˢ t` gets turned
into `a ∈ s ∧ b ∈ t`, instead of getting `(a, b).1` and `(a, b).2`.
-/
theorem prodMk_mem_set_prod_eq : ((a, b) ∈ s ×ˢ t) = (a ∈ s ∧ b ∈ t) :=
  rfl
/-
**Set.mk_mem_prod** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mk_mem_prod (ha : a in s) (hb : b in t) : (a, b) in s ×ˢ t
参数：ha : a in s；hb : b in t。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_mem_prod (ha : a ∈ s) (hb : b ∈ t) : (a, b) ∈ s ×ˢ t := ⟨ha, hb⟩
/-
**Set.prod_image_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：prod_image_left (f : α -> γ) (s : Set α) (t : Set β) : (f '' s) ×ˢ t = (fu
n x => (f x.1, x.2)) '' s ×ˢ t
参数：f : α -> γ；s : Set α；t : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
-/
theorem prod_image_left (f : α → γ) (s : Set α) (t : Set β) :
    (f '' s) ×ˢ t = (fun x ↦ (f x.1, x.2)) '' s ×ˢ t := by
  aesop
/-
**Set.prod_image_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：prod_image_right (f : α -> γ) (s : Set α) (t : Set β) : t ×ˢ (f '' s) = (f
un x => (x.1, f x.2)) '' t ×ˢ s
参数：f : α -> γ；s : Set α；t : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_image_right (f : α → γ) (s : Set α) (t : Set β) :
    t ×ˢ (f '' s) = (fun x ↦ (x.1, f x.2)) '' t ×ˢ s := by
  aesop

end Prod

section Diagonal

/-- `diagonal α` is the set of `α × α` consisting of all pairs of the form `(a, a)`. -/
/-
**Set.diagonal** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：diagonal (α : Type*) : Set (α × α)
参数：α : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`diagonal α` is the set of `α × α` consisting of all pairs of the form `(a, a)`.
-/
def diagonal (α : Type*) : Set (α × α) := {p | p.1 = p.2}
/-
**Set.mem_diagonal** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mem_diagonal (x : α) : (x, x) in diagonal α
参数：x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mem_diagonal (x : α) : (x, x) ∈ diagonal α := rfl
/-
**Set.mem_diagonal_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u} {x : α × α}, x ∈ Set.diagonal α ↔ x.1 = x.2
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp, grind =, push] theorem mem_diagonal_iff {x : α × α} : x ∈ diagonal α ↔ x.1 = x.2 := .rfl

/-- The off-diagonal of a set `s` is the set of pairs `(a, b)` with `a, b ∈ s` and `a ≠ b`. -/
/-
**Set.offDiag** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：offDiag (s : Set α) : Set (α × α)
参数：s : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The off-diagonal of a set `s` is the set of pairs `(a, b)` with `a, b ∈ s` and `
a ≠ b`.
-/
def offDiag (s : Set α) : Set (α × α) := {x | x.1 ∈ s ∧ x.2 ∈ s ∧ x.1 ≠ x.2}

@[simp, grind =, push]
/-
**Set.mem_offDiag** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mem_offDiag {x : α × α} {s : Set α} : x in s.offDiag ↔ x.1 in s ∧ x.2 in s
 ∧ x.1 != x.2
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_offDiag {x : α × α} {s : Set α} : x ∈ s.offDiag ↔ x.1 ∈ s ∧ x.2 ∈ s ∧ x.1 ≠ x.2 :=
  Iff.rfl

end Diagonal

section Pi

variable {ι : Type*} {α : ι → Type*}

/-- Given an index set `ι` and a family of sets `t : Π i, Set (α i)`, `pi s t`
is the set of dependent functions `f : Πa, π a` such that `f i` belongs to `t i`
whenever `i ∈ s`. -/
/-
**Set.pi** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：pi (s : Set ι) (t : forall i, Set (α i)) : Set (forall i, α i)
参数：s : Set ι；t : forall i, Set (α i)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an index set `ι` and a family of sets `t : Π i, Set (α i)`, `pi s t`
is the set of dependent functions `f : Πa, π a` such that `f i` belongs to `t i`
whenever `i ∈ s`.
-/
def pi (s : Set ι) (t : ∀ i, Set (α i)) : Set (∀ i, α i) := {f | ∀ i ∈ s, f i ∈ t i}

variable {s : Set ι} {t : ∀ i, Set (α i)} {f : ∀ i, α i}
/-
**Set.mem_pi** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {ι : Type u_1} {α : ι → Type u_2} {s : Set ι} {t : (i : ι) → Set (α i)} 
{f : (i : ι) → α i},   f ∈ s.pi t ↔ ∀ i ∈ s, f i ∈ t i
参数：i : ι；α i；i : ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp, grind =, push] theorem mem_pi : f ∈ s.pi t ↔ ∀ i ∈ s, f i ∈ t i := .rfl
/-
**Set.mem_univ_pi** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mem_univ_pi : f in pi univ t ↔ forall i, f i in t i
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
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_univ_pi : f ∈ pi univ t ↔ ∀ i, f i ∈ t i := by simp

end Pi

/-- Two functions `f₁ f₂ : α → β` are equal on `s` if `f₁ x = f₂ x` for all `x ∈ s`. -/
/-
**Set.EqOn** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：EqOn (f₁ f₂ : α -> β) (s : Set α) : Prop
参数：f₁ f₂ : α -> β；s : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Two functions `f₁ f₂ : α → β` are equal on `s` if `f₁ x = f₂ x` for all `x ∈ s`.
-/
def EqOn (f₁ f₂ : α → β) (s : Set α) : Prop := ∀ ⦃x⦄, x ∈ s → f₁ x = f₂ x

/-- `MapsTo f s t` means that the image of `s` is contained in `t`. -/
/-
**Set.MapsTo** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：MapsTo (f : α -> β) (s : Set α) (t : Set β) : Prop
参数：f : α -> β；s : Set α；t : Set β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`MapsTo f s t` means that the image of `s` is contained in `t`.
-/
def MapsTo (f : α → β) (s : Set α) (t : Set β) : Prop := ∀ ⦃x⦄, x ∈ s → f x ∈ t
/-
**Set.mapsTo_image** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mapsTo_image (f : α -> β) (s : Set α) : MapsTo f s (f '' s)
参数：f : α -> β；s : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
-/
theorem mapsTo_image (f : α → β) (s : Set α) : MapsTo f s (f '' s) := fun _ ↦ mem_image_of_mem f
/-
**Set.mapsTo_preimage** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mapsTo_preimage (f : α -> β) (t : Set β) : MapsTo f (f ⁻¹' t) t
参数：f : α -> β；t : Set β。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapsTo_preimage (f : α → β) (t : Set β) : MapsTo f (f ⁻¹' t) t := fun _ ↦ id

/-- Given a map `f` sending `s : Set α` into `t : Set β`, restrict domain of `f` to `s`
and the codomain to `t`. Same as `Subtype.map`. -/
/-
**Set.MapsTo.restrict** 是 Mathlib 中的一个定义，位于命名空间 `Set.MapsTo`。
形式化陈述：{α : Type u} → {β : Type v} → (f : α → β) → (s : Set α) → (t : Set β) → Se
t.MapsTo f s t → ↑s → ↑t
参数：f : α → β；s : Set α；t : Set β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a map `f` sending `s : Set α` into `t : Set β`, restrict domain of `f` to 
`s`
and the codomain to `t`. Same as `Subtype.map`.
-/
def MapsTo.restrict (f : α → β) (s : Set α) (t : Set β) (h : MapsTo f s t) : s → t :=
  Subtype.map f h

/-- The restriction of a function onto the preimage of a set. -/
@[simps!]
/-
**Set.restrictPreimage** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：restrictPreimage (t : Set β) (f : α -> β) : f ⁻¹' t -> t
参数：t : Set β；f : α -> β。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mapsTo_preimage`：mapsTo_preimage (f : α -> β) (t : Set β) : MapsTo f
 (f ⁻¹' t) t

--- 原说明 ---
The restriction of a function onto the preimage of a set.
-/
def restrictPreimage (t : Set β) (f : α → β) : f ⁻¹' t → t :=
  (Set.mapsTo_preimage f t).restrict _ _ _

/-- `f` is injective on `s` if the restriction of `f` to `s` is injective. -/
/-
**Set.InjOn** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：InjOn (f : α -> β) (s : Set α) : Prop
参数：f : α -> β；s : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`f` is injective on `s` if the restriction of `f` to `s` is injective.
-/
def InjOn (f : α → β) (s : Set α) : Prop :=
  ∀ ⦃x₁ : α⦄, x₁ ∈ s → ∀ ⦃x₂ : α⦄, x₂ ∈ s → f x₁ = f x₂ → x₁ = x₂

/-- The graph of a function `f : α → β` on a set `s`. -/
/-
**Set.graphOn** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：graphOn (f : α -> β) (s : Set α) : Set (α × β)
参数：f : α -> β；s : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The graph of a function `f : α → β` on a set `s`.
-/
def graphOn (f : α → β) (s : Set α) : Set (α × β) := (fun x ↦ (x, f x)) '' s

/-- `f` is surjective from `s` to `t` if `t` is contained in the image of `s`. -/
/-
**Set.SurjOn** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：SurjOn (f : α -> β) (s : Set α) (t : Set β) : Prop
参数：f : α -> β；s : Set α；t : Set β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`f` is surjective from `s` to `t` if `t` is contained in the image of `s`.
-/
def SurjOn (f : α → β) (s : Set α) (t : Set β) : Prop := t ⊆ f '' s

/-- `f` is bijective from `s` to `t` if `f` is injective on `s` and `f '' s = t`. -/
/-
**Set.BijOn** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：BijOn (f : α -> β) (s : Set α) (t : Set β) : Prop
参数：f : α -> β；s : Set α；t : Set β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`f` is bijective from `s` to `t` if `f` is injective on `s` and `f '' s = t`.
-/
def BijOn (f : α → β) (s : Set α) (t : Set β) : Prop := MapsTo f s t ∧ InjOn f s ∧ SurjOn f s t

/-- `g` is a left inverse to `f` on `s` means that `g (f x) = x` for all `x ∈ s`. -/
/-
**Set.LeftInvOn** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：LeftInvOn (g : β -> α) (f : α -> β) (s : Set α) : Prop
参数：g : β -> α；f : α -> β；s : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`g` is a left inverse to `f` on `s` means that `g (f x) = x` for all `x ∈ s`.
-/
def LeftInvOn (g : β → α) (f : α → β) (s : Set α) : Prop := ∀ ⦃x⦄, x ∈ s → g (f x) = x

/-- `g` is a right inverse to `f` on `t` if `f (g x) = x` for all `x ∈ t`. -/
/-
**Set.RightInvOn** 是 Mathlib 中的一个缩写定义，位于命名空间 `Set`。
形式化陈述：RightInvOn (g : β -> α) (f : α -> β) (t : Set β) : Prop
参数：g : β -> α；f : α -> β；t : Set β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`g` is a right inverse to `f` on `t` if `f (g x) = x` for all `x ∈ t`.
-/
abbrev RightInvOn (g : β → α) (f : α → β) (t : Set β) : Prop := LeftInvOn f g t

/-- `g` is an inverse to `f` viewed as a map from `s` to `t` -/
/-
**Set.InvOn** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：InvOn (g : β -> α) (f : α -> β) (s : Set α) (t : Set β) : Prop
参数：g : β -> α；f : α -> β；s : Set α；t : Set β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`g` is an inverse to `f` viewed as a map from `s` to `t`
-/
def InvOn (g : β → α) (f : α → β) (s : Set α) (t : Set β) : Prop :=
  LeftInvOn g f s ∧ RightInvOn g f t

section image2

/-- The image of a binary function `f : α → β → γ` as a function `Set α → Set β → Set γ`.
Mathematically this should be thought of as the image of the corresponding function `α × β → γ`. -/
/-
**Set.image2** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：image2 (f : α -> β -> γ) (s : Set α) (t : Set β) : Set γ
参数：f : α -> β -> γ；s : Set α；t : Set β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The image of a binary function `f : α → β → γ` as a function `Set α → Set β → Se
t γ`.
Mathematically this should be thought of as the image of the corresponding funct
ion `α × β → γ`.
-/
def image2 (f : α → β → γ) (s : Set α) (t : Set β) : Set γ := {c | ∃ a ∈ s, ∃ b ∈ t, f a b = c}

variable {f : α → β → γ} {s : Set α} {t : Set β} {a : α} {b : β} {c : γ}
/-
**Set.mem_image2** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u} {β : Type v} {γ : Type w} {f : α → β → γ} {s : Set α} {t : 
Set β} {c : γ},   c ∈ Set.image2 f s t ↔ ∃ a ∈ s, ∃ b ∈ t, f a b = c
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp, grind =] theorem mem_image2 : c ∈ image2 f s t ↔ ∃ a ∈ s, ∃ b ∈ t, f a b = c := .rfl
/-
**Set.mem_image2_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mem_image2_of_mem (ha : a in s) (hb : b in t) : f a b in image2 f s t
参数：ha : a in s；hb : b in t。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mem_image2_of_mem (ha : a ∈ s) (hb : b ∈ t) : f a b ∈ image2 f s t :=
  ⟨a, ha, b, hb, rfl⟩

end image2

/-- Given a set `s` of functions `α → β` and `t : Set α`, `seq s t` is the union of `f '' t` over
all `f ∈ s`. -/
/-
**Set.seq** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：seq (s : Set (α -> β)) (t : Set α) : Set β
参数：s : Set (α -> β)；t : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a set `s` of functions `α → β` and `t : Set α`, `seq s t` is the union of 
`f '' t` over
all `f ∈ s`.
-/
def seq (s : Set (α → β)) (t : Set α) : Set β := image2 (fun f ↦ f) s t

@[simp, grind =]
/-
**Set.mem_seq_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mem_seq_iff {s : Set (α -> β)} {t : Set α} {b : β} : b in seq s t ↔ exists
 f in s, exists a in t, (f : α -> β) a = b
参数：α -> β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_seq_iff {s : Set (α → β)} {t : Set α} {b : β} :
    b ∈ seq s t ↔ ∃ f ∈ s, ∃ a ∈ t, (f : α → β) a = b :=
  Iff.rfl
/-
**Set.seq_eq_image2** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：seq_eq_image2 (s : Set (α -> β)) (t : Set α) : seq s t = image2 (fun f a =
> f a) s t
参数：s : Set (α -> β)；t : Set α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma seq_eq_image2 (s : Set (α → β)) (t : Set α) : seq s t = image2 (fun f a ↦ f a) s t := rfl

end Set

