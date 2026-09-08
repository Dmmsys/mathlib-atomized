/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Order.Category.PartOrd
public import Mathlib.Data.Finset.Empty
public import Mathlib.Data.Finset.Image

/-!
# Nonempty finite chains in a partially ordered type

Given a partially ordered type `X`, we introduce the type
`NonemptyFiniteChains` of nonempty finite chains in `X`, i.e.
nonempty finite subsets `A` of `X` such that all the elements
in `A` are comparable.

-/

@[expose] public section

universe v u

open CategoryTheory

namespace PartialOrder

/-- Given a partially ordered type `X`, this is the type of nonempty finite
subsets `A` of `X` such that all the elements of `A` are comparable. -/
@[ext]
/-
**PartialOrder.NonemptyFiniteChains** 是 Mathlib 中的一个结构，位于命名空间 `PartialOrder`。
形式化陈述：NonemptyFiniteChains (X : Type u) [PartialOrder X] where /-- a finite subs
et -/ finset : Finset X nonempty : finset.Nonempty
参数：X : Type u。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a partially ordered type `X`, this is the type of nonempty finite
subsets `A` of `X` such that all the elements of `A` are comparable.
-/
structure NonemptyFiniteChains (X : Type u) [PartialOrder X] where
  /-- a finite subset -/
  finset : Finset X
  nonempty : finset.Nonempty := by simp
  comparable (a b : finset) : a ≤ b ∨ b ≤ a

namespace NonemptyFiniteChains

attribute [simp] nonempty

/-
**PartialOrder.NonemptyFiniteChains.** 是 Mathlib 中的一个实例，位于命名空间 `PartialOrder.Non
emptyFiniteChains`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : Type u) [PartialOrder X] : PartialOrder (NonemptyFiniteChains X) :=
  PartialOrder.lift finset (fun _ _ _ ↦ by aesop)

variable {X Y : Type*} [PartialOrder X] [PartialOrder Y]

@[simp]
/-
**PartialOrder.NonemptyFiniteChains.le_iff** 是 Mathlib 中的一个引理，位于命名空间 `PartialOrd
er.NonemptyFiniteChains`。
形式化陈述：le_iff (A B : NonemptyFiniteChains X) : A <= B ↔ A.finset <= B.finset
参数：A B : NonemptyFiniteChains X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma le_iff (A B : NonemptyFiniteChains X) : A ≤ B ↔ A.finset ≤ B.finset := Iff.rfl

@[simp]
/-
**PartialOrder.NonemptyFiniteChains.lt_iff** 是 Mathlib 中的一个引理，位于命名空间 `PartialOrd
er.NonemptyFiniteChains`。
形式化陈述：lt_iff (A B : NonemptyFiniteChains X) : A < B ↔ A.finset < B.finset
参数：A B : NonemptyFiniteChains X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma lt_iff (A B : NonemptyFiniteChains X) : A < B ↔ A.finset < B.finset := Iff.rfl

open scoped Classical in
/-- The image of a nonempty finite chain by a monotone map. -/
/-
**PartialOrder.NonemptyFiniteChains.map** 是 Mathlib 中的一个定义，位于命名空间 `PartialOrder.
NonemptyFiniteChains`。
形式化陈述：map (s : NonemptyFiniteChains X) (f : X ->o Y) : NonemptyFiniteChains Y wh
ere finset
参数：s : NonemptyFiniteChains X；f : X ->o Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The image of a nonempty finite chain by a monotone map.
-/
noncomputable def map (s : NonemptyFiniteChains X) (f : X →o Y) :
    NonemptyFiniteChains Y where
  finset := Finset.image f s.finset
  comparable := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    simp only [Finset.mem_image] at ha hb
    obtain ⟨a, ha', rfl⟩ := ha
    obtain ⟨b, hb', rfl⟩ := hb
    obtain h | h := s.comparable ⟨_, ha'⟩ ⟨_, hb'⟩
    · exact Or.inl (f.monotone h)
    · exact Or.inr (f.monotone h)

@[simp]
/-
**PartialOrder.NonemptyFiniteChains.mem_map_iff** 是 Mathlib 中的一个引理，位于命名空间 `Parti
alOrder.NonemptyFiniteChains`。
形式化陈述：mem_map_iff (s : NonemptyFiniteChains X) (f : X ->o Y) (y : Y) : y in (s.m
ap f).finset ↔ exists x, x in s.finset ∧ f x = y
参数：s : NonemptyFiniteChains X；f : X ->o Y；y : Y。
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
lemma mem_map_iff (s : NonemptyFiniteChains X) (f : X →o Y) (y : Y) :
    y ∈ (s.map f).finset ↔ ∃ x, x ∈ s.finset ∧ f x = y := by
  simp [map]

/-- The monotone map `NonemptyFiniteChains X →o NonemptyFiniteChains Y`
that is induced by `f : X →o Y`. -/
@[simps]
/-
**PartialOrder.NonemptyFiniteChains.orderHomMap** 是 Mathlib 中的一个定义，位于命名空间 `Parti
alOrder.NonemptyFiniteChains`。
形式化陈述：orderHomMap (f : X ->o Y) : NonemptyFiniteChains X ->o NonemptyFiniteChain
s Y where toFun s
参数：f : X ->o Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The monotone map `NonemptyFiniteChains X →o NonemptyFiniteChains Y`
that is induced by `f : X →o Y`.
-/
noncomputable def orderHomMap (f : X →o Y) :
    NonemptyFiniteChains X →o NonemptyFiniteChains Y where
  toFun s := map s f
  monotone' a b h x hx := by
    simp only [mem_map_iff] at hx ⊢
    obtain ⟨x, hx, rfl⟩ := hx
    exact ⟨x, h hx, rfl⟩

end NonemptyFiniteChains

end PartialOrder

open PartialOrder in
/-- The functor `PartOrd ⥤ PartOrd` which sends a partially ordered type `X`
to `NonemptyFiniteChains X`. -/
@[simps]
/-
**PartOrd.nonemptyFiniteChainsFunctor** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：PartOrd.nonemptyFiniteChainsFunctor : PartOrd.{u} ⥤ PartOrd.{u} where obj 
X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `PartOrd ⥤ PartOrd` which sends a partially ordered type `X`
to `NonemptyFiniteChains X`.
-/
noncomputable def PartOrd.nonemptyFiniteChainsFunctor : PartOrd.{u} ⥤ PartOrd.{u} where
  obj X := .of (NonemptyFiniteChains X)
  map f := PartOrd.ofHom (NonemptyFiniteChains.orderHomMap f.hom)
