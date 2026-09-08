/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Finset.Image

/-!
# Constructors for `Fintype`

This file contains basic constructors for `Fintype` instances,
given maps from/to finite types.

## Main results

* `Fintype.ofBijective`, `Fintype.ofInjective`, `Fintype.ofSurjective`:
  a type is finite if there is a bi/in/surjection from/to a finite type.
-/

@[expose] public section

assert_not_exists Monoid

open Function

open Nat

universe u v

variable {α β γ : Type*}

open Finset

namespace Fintype

/-- Construct a proof of `Fintype α` from a universal multiset -/
@[instance_reducible]
/-
**Fintype.ofMultiset** 是 Mathlib 中的一个定义，位于命名空间 `Fintype`。
形式化陈述：ofMultiset [DecidableEq α] (s : Multiset α) (H : forall x : α, x in s) : F
intype α
参数：s : Multiset α；H : forall x : α, x in s。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a proof of `Fintype α` from a universal multiset
-/
def ofMultiset [DecidableEq α] (s : Multiset α) (H : ∀ x : α, x ∈ s) : Fintype α :=
  ⟨s.toFinset, by simpa using H⟩

/-- Construct a proof of `Fintype α` from a universal list -/
@[instance_reducible]
/-
**Fintype.ofList** 是 Mathlib 中的一个定义，位于命名空间 `Fintype`。
形式化陈述：ofList [DecidableEq α] (l : List α) (H : forall x : α, x in l) : Fintype α
参数：l : List α；H : forall x : α, x in l。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a proof of `Fintype α` from a universal list
-/
def ofList [DecidableEq α] (l : List α) (H : ∀ x : α, x ∈ l) : Fintype α :=
  ⟨l.toFinset, by simpa using H⟩

/-- If `f : α → β` is a bijection and `α` is a fintype, then `β` is also a fintype. -/
@[instance_reducible]
/-
**Fintype.ofBijective** 是 Mathlib 中的一个定义，位于命名空间 `Fintype`。
形式化陈述：ofBijective [Fintype α] (f : α -> β) (H : Function.Bijective f) : Fintype 
β
参数：f : α -> β；H : Function.Bijective f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f : α → β` is a bijection and `α` is a fintype, then `β` is also a fintype.
-/
def ofBijective [Fintype α] (f : α → β) (H : Function.Bijective f) : Fintype β :=
  ⟨univ.map ⟨f, H.1⟩, fun b =>
    let ⟨_, e⟩ := H.2 b
    e ▸ mem_map_of_mem _ (mem_univ _)⟩

/-- If `f : α → β` is a surjection and `α` is a fintype, then `β` is also a fintype. -/
@[instance_reducible]
/-
**Fintype.ofSurjective** 是 Mathlib 中的一个定义，位于命名空间 `Fintype`。
形式化陈述：ofSurjective [DecidableEq β] [Fintype α] (f : α -> β) (H : Function.Surjec
tive f) : Fintype β
参数：f : α -> β；H : Function.Surjective f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f : α → β` is a surjection and `α` is a fintype, then `β` is also a fintype.
-/
def ofSurjective [DecidableEq β] [Fintype α] (f : α → β) (H : Function.Surjective f) : Fintype β :=
  ⟨univ.image f, fun b =>
    let ⟨_, e⟩ := H b
    e ▸ mem_image_of_mem _ (mem_univ _)⟩

/-- Given an injective function to a fintype, the domain is also a
fintype. This is noncomputable because injectivity alone cannot be
used to construct preimages. -/
@[instance_reducible]
/-
**Fintype.ofInjective** 是 Mathlib 中的一个定义，位于命名空间 `Fintype`。
形式化陈述：ofInjective [Fintype β] (f : α -> β) (H : Function.Injective f) : Fintype 
α
参数：f : α -> β；H : Function.Injective f。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Function.invFun_surjective`：invFun_surjective (hf : Injective f) : Surje
ctive (invFun f)

--- 原说明 ---
Given an injective function to a fintype, the domain is also a
fintype. This is noncomputable because injectivity alone cannot be
used to construct preimages.
-/
noncomputable def ofInjective [Fintype β] (f : α → β) (H : Function.Injective f) : Fintype α :=
  letI := Classical.dec
  if hα : Nonempty α then
    letI := Classical.inhabited_of_nonempty hα
    ofSurjective (invFun f) (invFun_surjective H)
  else ⟨∅, fun x => (hα ⟨x⟩).elim⟩

/-- If `f : α ≃ β` and `α` is a fintype, then `β` is also a fintype. -/
@[instance_reducible]
/-
**Fintype.ofEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Fintype`。
形式化陈述：ofEquiv (α : Type*) [Fintype α] (f : α ≃ β) : Fintype β
参数：α : Type*；f : α ≃ β。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.bijective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Bijec
tive ⇑e

--- 原说明 ---
If `f : α ≃ β` and `α` is a fintype, then `β` is also a fintype.
-/
def ofEquiv (α : Type*) [Fintype α] (f : α ≃ β) : Fintype β :=
  ofBijective _ f.bijective

/-- Any subsingleton type with a witness is a fintype (with one term). -/
@[instance_reducible]
/-
**Fintype.ofSubsingleton** 是 Mathlib 中的一个定义，位于命名空间 `Fintype`。
形式化陈述：ofSubsingleton (a : α) [Subsingleton α] : Fintype α
参数：a : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any subsingleton type with a witness is a fintype (with one term).
-/
def ofSubsingleton (a : α) [Subsingleton α] : Fintype α :=
  ⟨{a}, fun _ => Finset.mem_singleton.2 (Subsingleton.elim _ _)⟩

-- In principle, this could be a `simp` theorem but it applies to any occurrence of `univ` and
-- required unification of the (possibly very complex) `Fintype` instances.
/-
**Fintype.univ_ofSubsingleton** 是 Mathlib 中的一个定理，位于命名空间 `Fintype`。
形式化陈述：univ_ofSubsingleton (a : α) [Subsingleton α] : @univ _ (ofSubsingleton a) 
= {a}
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem univ_ofSubsingleton (a : α) [Subsingleton α] : @univ _ (ofSubsingleton a) = {a} :=
  rfl

/-- An empty type is a fintype. Not registered as an instance, to make sure that there aren't two
conflicting `Fintype ι` instances around when casing over whether a fintype `ι` is empty or not. -/
@[instance_reducible]
/-
**Fintype.ofIsEmpty** 是 Mathlib 中的一个定义，位于命名空间 `Fintype`。
形式化陈述：ofIsEmpty [IsEmpty α] : Fintype α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An empty type is a fintype. Not registered as an instance, to make sure that the
re aren't two
conflicting `Fintype ι` instances around when casing over whether a fintype `ι` 
is empty or not.
-/
def ofIsEmpty [IsEmpty α] : Fintype α :=
  ⟨∅, isEmptyElim⟩

/-- Note: this lemma is specifically about `Fintype.ofIsEmpty`. For a statement about
arbitrary `Fintype` instances, use `Finset.univ_eq_empty`. -/
/-
**Fintype.univ_ofIsEmpty** 是 Mathlib 中的一个定理，位于命名空间 `Fintype`。
形式化陈述：univ_ofIsEmpty [IsEmpty α] : @univ α Fintype.ofIsEmpty = ∅
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Note: this lemma is specifically about `Fintype.ofIsEmpty`. For a statement abou
t
arbitrary `Fintype` instances, use `Finset.univ_eq_empty`.
-/
theorem univ_ofIsEmpty [IsEmpty α] : @univ α Fintype.ofIsEmpty = ∅ :=
  rfl
/-
**Fintype.** 是 Mathlib 中的一个实例，位于命名空间 `Fintype`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Fintype Empty := Fintype.ofIsEmpty
/-
**Fintype.** 是 Mathlib 中的一个实例，位于命名空间 `Fintype`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Fintype PEmpty := Fintype.ofIsEmpty

end Fintype

