/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Simon Hudon
-/
module

public import Mathlib.Data.PFunctor.Multivariate.Basic

/-!
# Multivariate quotients of polynomial functors.

Basic definition of multivariate QPF. QPFs form a compositional framework
for defining inductive and coinductive types, their quotients and nesting.

The idea is based on building ever larger functors. For instance, we can define
a list using a shape functor:

```lean
inductive ListShape (a b : Type)
  | nil : ListShape
  | cons : a -> b -> ListShape
```

This shape can itself be decomposed as a sum of product which are themselves
QPFs. It follows that the shape is a QPF and we can take its fixed point
and create the list itself:

```lean
def List (a : Type) := fix ListShape a -- not the actual notation
```

We can continue and define the quotient on permutation of lists and create
the multiset type:

```lean
def Multiset (a : Type) := QPF.quot List.perm List a -- not the actual notion
```

And `Multiset` is also a QPF. We can then create a novel data type (for Lean):

```lean
inductive Tree (a : Type)
  | node : a -> Multiset Tree -> Tree
```

An unordered tree. This is currently not supported by Lean because it nests
an inductive type inside of a quotient. We can go further and define
unordered, possibly infinite trees:

```lean
coinductive Tree' (a : Type)
| node : a -> Multiset Tree' -> Tree'
```

by using the `cofix` construct. Those options can all be mixed and
matched because they preserve the properties of QPF. The latter example,
`Tree'`, combines fixed point, co-fixed point and quotients.

## Related modules

* constructions
  * Fix
  * Cofix
  * Quot
  * Comp
  * Sigma / Pi
  * Prj
  * Const

each proves that some operations on functors preserves the QPF structure
-/

@[expose] public section

set_option linter.style.longLine false in
/-!
## Reference

[Jeremy Avigad, Mario M. Carneiro and Simon Hudon, *Data Types as Quotients of Polynomial Functors*][avigad-carneiro-hudon2019]
-/


universe u

open MvFunctor

/-- Multivariate quotients of polynomial functors.
-/
/-
**MvQPF** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{n : ℕ} → (TypeVec.{u} n → Type u_1) → Type (max (u + 1) u_1)
参数：TypeVec.{u} n → Type u_1；max (u + 1) u_1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Multivariate quotients of polynomial functors.
-/
class MvQPF {n : ℕ} (F : TypeVec.{u} n → Type*) extends MvFunctor F where
  P : MvPFunctor.{u} n
  abs : ∀ {α}, P α → F α
  repr : ∀ {α}, F α → P α
  abs_repr : ∀ {α} (x : F α), abs (repr x) = x
  abs_map : ∀ {α β} (f : α ⟹ β) (p : P α), abs (f <$$> p) = f <$$> abs p

namespace MvQPF

variable {n : ℕ} {F : TypeVec.{u} n → Type*} [q : MvQPF F]

open MvFunctor (LiftP LiftR)

/-!
### Show that every MvQPF is a lawful MvFunctor.
-/


/-
**MvQPF.id_map** 是 Mathlib 中的一个定理，位于命名空间 `MvQPF`。
形式化陈述：∀ {n : ℕ} {F : TypeVec.{u} n → Type u_1} [q : MvQPF F] {α : TypeVec.{u} n}
 (x : F α), MvFunctor.map TypeVec.id x = x
参数：x : F α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvQPF.abs_repr`：∀ {n : ℕ} {F : TypeVec.{u} n → Type u_1} [self : MvQPF F
] {α : TypeVec.{u} n} (x : F α), MvQPF.abs (MvQPF.repr x) = x
· 使用定理 `MvQPF.abs_map`：∀ {n : ℕ} {F : TypeVec.{u} n → Type u_1} [self : MvQPF F]
 {α β : TypeVec.{u} n} (f : α.Arrow β) (p : ↑(MvQPF.P F) α),   MvQPF.abs (MvFunc
tor…

--- 原说明 ---
### Show that every MvQPF is a lawful MvFunctor.
-/
protected theorem id_map {α : TypeVec n} (x : F α) : TypeVec.id <$$> x = x := by
  rw [← abs_repr x, ← abs_map]
  rfl

@[simp]
/-
**MvQPF.comp_map** 是 Mathlib 中的一个定理，位于命名空间 `MvQPF`。
形式化陈述：comp_map {α β γ : TypeVec n} (f : α ⟹ β) (g : β ⟹ γ) (x : F α) : (g ⊚ f) <
 > x = g < > f < > x
参数：f : α ⟹ β；g : β ⟹ γ；x : F α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvQPF.abs_repr`：∀ {n : ℕ} {F : TypeVec.{u} n → Type u_1} [self : MvQPF F
] {α : TypeVec.{u} n} (x : F α), MvQPF.abs (MvQPF.repr x) = x
· 使用定理 `MvQPF.abs_map`：∀ {n : ℕ} {F : TypeVec.{u} n → Type u_1} [self : MvQPF F]
 {α β : TypeVec.{u} n} (f : α.Arrow β) (p : ↑(MvQPF.P F) α),   MvQPF.abs (MvFunc
tor…
-/
theorem comp_map {α β γ : TypeVec n} (f : α ⟹ β) (g : β ⟹ γ) (x : F α) :
    (g ⊚ f) <$$> x = g <$$> f <$$> x := by
  rw [← abs_repr x, ← abs_map, ← abs_map, ← abs_map]
  rfl
/-
**MvQPF.** 是 Mathlib 中的一个实例，位于命名空间 `MvQPF`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) lawfulMvFunctor : LawfulMvFunctor F where
  id_map := @MvQPF.id_map n F _
  comp_map := @comp_map n F _

set_option backward.isDefEq.respectTransparency false in
-- Lifting predicates and relations
/-
**MvQPF.liftP_iff** 是 Mathlib 中的一个定理，位于命名空间 `MvQPF`。
形式化陈述：liftP_iff {α : TypeVec n} (p : forall ⦃i⦄, α i -> Prop) (x : F α) : LiftP 
p x ↔ exists a f, x = abs ⟨a, f⟩ ∧ forall i j, p (f i j)
参数：p : forall ⦃i⦄, α i -> Prop；x : F α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvQPF.abs_repr`：∀ {n : ℕ} {F : TypeVec.{u} n → Type u_1} [self : MvQPF F
] {α : TypeVec.{u} n} (x : F α), MvQPF.abs (MvQPF.repr x) = x
· 使用定理 `MvQPF.abs_map`：∀ {n : ℕ} {F : TypeVec.{u} n → Type u_1} [self : MvQPF F]
 {α β : TypeVec.{u} n} (f : α.Arrow β) (p : ↑(MvQPF.P F) α),   MvQPF.abs (MvFunc
tor…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem liftP_iff {α : TypeVec n} (p : ∀ ⦃i⦄, α i → Prop) (x : F α) :
    LiftP p x ↔ ∃ a f, x = abs ⟨a, f⟩ ∧ ∀ i j, p (f i j) := by
  constructor
  · rintro ⟨y, hy⟩
    rcases h : repr y with ⟨a, f⟩
    use a, fun i j => (f i j).val
    constructor
    · rw [← hy, ← abs_repr y, h, ← abs_map]; rfl
    intro i j
    apply (f i j).property
  rintro ⟨a, f, h₀, h₁⟩
  use abs ⟨a, fun i j => ⟨f i j, h₁ i j⟩⟩
  rw [← abs_map, h₀]; rfl

set_option backward.isDefEq.respectTransparency false in
/-
**MvQPF.liftR_iff** 是 Mathlib 中的一个定理，位于命名空间 `MvQPF`。
形式化陈述：liftR_iff {α : TypeVec n} (r : forall ⦃i⦄, α i -> α i -> Prop) (x y : F α)
 : LiftR r x y ↔ exists a f₀ f₁, x = abs ⟨a, f₀⟩ ∧ y = abs ⟨a, f₁⟩ ∧ forall i j,
 r (f₀ i j) (f₁ i j)
参数：r : forall ⦃i⦄, α i -> α i -> Prop；x y : F α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvQPF.abs_repr`：∀ {n : ℕ} {F : TypeVec.{u} n → Type u_1} [self : MvQPF F
] {α : TypeVec.{u} n} (x : F α), MvQPF.abs (MvQPF.repr x) = x
· 使用定理 `MvQPF.abs_map`：∀ {n : ℕ} {F : TypeVec.{u} n → Type u_1} [self : MvQPF F]
 {α β : TypeVec.{u} n} (f : α.Arrow β) (p : ↑(MvQPF.P F) α),   MvQPF.abs (MvFunc
tor…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem liftR_iff {α : TypeVec n} (r : ∀ ⦃i⦄, α i → α i → Prop) (x y : F α) :
    LiftR r x y ↔ ∃ a f₀ f₁, x = abs ⟨a, f₀⟩ ∧ y = abs ⟨a, f₁⟩ ∧ ∀ i j, r (f₀ i j) (f₁ i j) := by
  constructor
  · rintro ⟨u, xeq, yeq⟩
    rcases h : repr u with ⟨a, f⟩
    use a, fun i j => (f i j).val.fst, fun i j => (f i j).val.snd
    constructor
    · rw [← xeq, ← abs_repr u, h, ← abs_map]; rfl
    constructor
    · rw [← yeq, ← abs_repr u, h, ← abs_map]; rfl
    intro i j
    exact (f i j).property
  rintro ⟨a, f₀, f₁, xeq, yeq, h⟩
  use abs ⟨a, fun i j => ⟨(f₀ i j, f₁ i j), h i j⟩⟩
  constructor
  · rw [xeq, ← abs_map]; rfl
  rw [yeq, ← abs_map]; rfl

open Set
/-
**MvQPF.mem_supp** 是 Mathlib 中的一个定理，位于命名空间 `MvQPF`。
形式化陈述：mem_supp {α : TypeVec n} (x : F α) (i) (u : α i) : u in supp x i ↔ forall 
a f, abs ⟨a, f⟩ = x -> u in f i '' univ
参数：x : F α；i；u : α i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvFunctor.supp.eq_1`：∀ {n : ℕ} {F : TypeVec.{u} n → Type v} [inst : MvFu
nctor F] {α : TypeVec.{u} n} (x : F α) (i : Fin2 n),   MvFunctor.supp x i = {y |
 ∀ ⦃P : (…
· 使用定理 `MvQPF.liftP_iff`：liftP_iff {α : TypeVec n} (p : forall ⦃i⦄, α i -> Prop)
 (x : F α) : LiftP p x ↔ exists a f, x = abs ⟨a, f⟩ ∧ forall i j, p (f i j)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
-/
theorem mem_supp {α : TypeVec n} (x : F α) (i) (u : α i) :
    u ∈ supp x i ↔ ∀ a f, abs ⟨a, f⟩ = x → u ∈ f i '' univ := by
  rw [supp]; dsimp; constructor
  · intro h a f haf
    have : LiftP (fun i u => u ∈ f i '' univ) x := by
      rw [liftP_iff]
      refine ⟨a, f, haf.symm, ?_⟩
      intro i u
      exact mem_image_of_mem _ (mem_univ _)
    exact h this
  grind [liftP_iff]
/-
**MvQPF.supp_eq** 是 Mathlib 中的一个定理，位于命名空间 `MvQPF`。
形式化陈述：supp_eq {α : TypeVec n} {i} (x : F α) : supp x i = { u | forall a f, abs ⟨
a, f⟩ = x -> u in f i '' univ }
参数：x : F α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `MvQPF.mem_supp`：mem_supp {α : TypeVec n} (x : F α) (i) (u : α i) : u in 
supp x i ↔ forall a f, abs ⟨a, f⟩ = x -> u in f i '' univ
-/
theorem supp_eq {α : TypeVec n} {i} (x : F α) :
    supp x i = { u | ∀ a f, abs ⟨a, f⟩ = x → u ∈ f i '' univ } := by ext; apply mem_supp

set_option backward.isDefEq.respectTransparency false in
/-
**MvQPF.has_good_supp_iff** 是 Mathlib 中的一个定理，位于命名空间 `MvQPF`。
形式化陈述：has_good_supp_iff {α : TypeVec n} (x : F α) : (forall p, LiftP p x ↔ foral
l (i), forall u in supp x i, p i u) ↔ exists a f, abs ⟨a, f⟩ = x ∧ forall i a' f
', abs ⟨a', f'⟩ = x -> f i '' univ subseteq f' i '' univ
参数：x : F α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvQPF.liftP_iff`：liftP_iff {α : TypeVec n} (p : forall ⦃i⦄, α i -> Prop)
 (x : F α) : LiftP p x ↔ exists a f, x = abs ⟨a, f⟩ ∧ forall i j, p (f i j)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MvQPF.mem_supp`：mem_supp {α : TypeVec n} (x : F α) (i) (u : α i) : u in 
supp x i ↔ forall a f, abs ⟨a, f⟩ = x -> u in f i '' univ
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
-/
theorem has_good_supp_iff {α : TypeVec n} (x : F α) :
    (∀ p, LiftP p x ↔ ∀ (i), ∀ u ∈ supp x i, p i u) ↔
      ∃ a f, abs ⟨a, f⟩ = x ∧ ∀ i a' f', abs ⟨a', f'⟩ = x → f i '' univ ⊆ f' i '' univ := by
  constructor
  · intro h
    have : LiftP (fun i u => u ∈ supp x i) x := by rw [h]; introv; exact id
    rw [liftP_iff] at this
    rcases this with ⟨a, f, xeq, h'⟩
    refine ⟨a, f, xeq.symm, ?_⟩
    intro a' f' h''
    rintro hu u ⟨j, _h₂, hfi⟩
    have hh : u ∈ supp x a' := by rw [← hfi]; apply h'
    exact (mem_supp x _ u).mp hh _ _ hu
  rintro ⟨a, f, xeq, h⟩ p; rw [liftP_iff]; constructor
  · rintro ⟨a', f', xeq', h'⟩ i u usuppx
    rcases (mem_supp x _ u).mp (@usuppx) a' f' xeq'.symm with ⟨i, _, f'ieq⟩
    rw [← f'ieq]
    apply h'
  intro h'
  refine ⟨a, f, xeq.symm, ?_⟩; intro j y
  apply h'; rw [mem_supp]
  intro a' f' xeq'
  apply h _ a' f' xeq'
  apply mem_image_of_mem _ (mem_univ _)

/-- A qpf is said to be uniform if every polynomial functor
representing a single value all have the same range. -/
/-
**MvQPF.IsUniform** 是 Mathlib 中的一个定义，位于命名空间 `MvQPF`。
形式化陈述：IsUniform : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A qpf is said to be uniform if every polynomial functor
representing a single value all have the same range.
-/
def IsUniform : Prop :=
  ∀ ⦃α : TypeVec n⦄ (a a' : q.P.A) (f : q.P.B a ⟹ α) (f' : q.P.B a' ⟹ α),
    abs ⟨a, f⟩ = abs ⟨a', f'⟩ → ∀ i, f i '' univ = f' i '' univ

/-- does `abs` preserve `liftp`? -/
/-
**MvQPF.LiftPPreservation** 是 Mathlib 中的一个定义，位于命名空间 `MvQPF`。
形式化陈述：LiftPPreservation : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
does `abs` preserve `liftp`?
-/
def LiftPPreservation : Prop :=
  ∀ ⦃α : TypeVec n⦄ (p : ∀ ⦃i⦄, α i → Prop) (x : q.P α), LiftP p (abs x) ↔ LiftP p x

/-- does `abs` preserve `supp`? -/
/-
**MvQPF.SuppPreservation** 是 Mathlib 中的一个定义，位于命名空间 `MvQPF`。
形式化陈述：SuppPreservation : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
does `abs` preserve `supp`?
-/
def SuppPreservation : Prop :=
  ∀ ⦃α⦄ (x : q.P α), supp (abs x) = supp x
/-
**MvQPF.supp_eq_of_isUniform** 是 Mathlib 中的一个定理，位于命名空间 `MvQPF`。
形式化陈述：supp_eq_of_isUniform (h : q.IsUniform) {α : TypeVec n} (a : q.P.A) (f : q.
P.B a ⟹ α) : forall i, supp (abs ⟨a, f⟩) i = f i '' univ
参数：h : q.IsUniform；a : q.P.A；f : q.P.B a ⟹ α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvQPF.mem_supp`：mem_supp {α : TypeVec n} (x : F α) (i) (u : α i) : u in 
supp x i ↔ forall a f, abs ⟨a, f⟩ = x -> u in f i '' univ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem supp_eq_of_isUniform (h : q.IsUniform) {α : TypeVec n} (a : q.P.A) (f : q.P.B a ⟹ α) :
    ∀ i, supp (abs ⟨a, f⟩) i = f i '' univ := by
  intro; ext u; rw [mem_supp]; constructor
  · intro h'
    apply h' _ _ rfl
  intro h' a' f' e
  rw [← h _ _ _ _ e.symm]; apply h'
/-
**MvQPF.liftP_iff_of_isUniform** 是 Mathlib 中的一个定理，位于命名空间 `MvQPF`。
形式化陈述：liftP_iff_of_isUniform (h : q.IsUniform) {α : TypeVec n} (x : F α) (p : fo
rall i, α i -> Prop) : LiftP p x ↔ forall (i), forall u in supp x i, p i u
参数：h : q.IsUniform；x : F α；p : forall i, α i -> Prop。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvQPF.liftP_iff`：liftP_iff {α : TypeVec n} (p : forall ⦃i⦄, α i -> Prop)
 (x : F α) : LiftP p x ↔ exists a f, x = abs ⟨a, f⟩ ∧ forall i j, p (f i j)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvQPF.abs_repr`：∀ {n : ℕ} {F : TypeVec.{u} n → Type u_1} [self : MvQPF F
] {α : TypeVec.{u} n} (x : F α), MvQPF.abs (MvQPF.repr x) = x
· 使用定理 `MvQPF.supp_eq_of_isUniform`：supp_eq_of_isUniform (h : q.IsUniform) {α : 
TypeVec n} (a : q.P.A) (f : q.P.B a ⟹ α) : forall i, supp (abs ⟨a, f⟩) i = f i '
' univ
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
-/
theorem liftP_iff_of_isUniform (h : q.IsUniform) {α : TypeVec n} (x : F α) (p : ∀ i, α i → Prop) :
    LiftP p x ↔ ∀ (i), ∀ u ∈ supp x i, p i u := by
  rw [liftP_iff, ← abs_repr x]
  obtain ⟨a, f⟩ := repr x; constructor
  · rintro ⟨a', f', abseq, hf⟩ u
    rw [supp_eq_of_isUniform h, h _ _ _ _ abseq]
    rintro b ⟨i, _, hi⟩
    rw [← hi]
    apply hf
  intro h'
  refine ⟨a, f, rfl, fun _ i => h' _ _ ?_⟩
  rw [supp_eq_of_isUniform h]
  exact ⟨i, mem_univ i, rfl⟩

set_option backward.isDefEq.respectTransparency false in
/-
**MvQPF.supp_map** 是 Mathlib 中的一个定理，位于命名空间 `MvQPF`。
形式化陈述：supp_map (h : q.IsUniform) {α β : TypeVec n} (g : α ⟹ β) (x : F α) (i) : s
upp (g <$$> x) i = g i '' supp x i
参数：h : q.IsUniform；g : α ⟹ β；x : F α；i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvQPF.abs_repr`：∀ {n : ℕ} {F : TypeVec.{u} n → Type u_1} [self : MvQPF F
] {α : TypeVec.{u} n} (x : F α), MvQPF.abs (MvQPF.repr x) = x
· 使用定理 `MvQPF.abs_map`：∀ {n : ℕ} {F : TypeVec.{u} n → Type u_1} [self : MvQPF F]
 {α β : TypeVec.{u} n} (f : α.Arrow β) (p : ↑(MvQPF.P F) α),   MvQPF.abs (MvFunc
tor…
· 使用定理 `MvPFunctor.map_eq`：map_eq {α β : TypeVec n} (g : α ⟹ β) (a : P.A) (f : P
.B a ⟹ α) : @MvFunctor.map _ P.Obj _ _ _ g ⟨a, f⟩ = ⟨a, g ⊚ f⟩
· 使用定理 `MvQPF.supp_eq_of_isUniform`：supp_eq_of_isUniform (h : q.IsUniform) {α : 
TypeVec n} (a : q.P.A) (f : q.P.B a ⟹ α) : forall i, supp (abs ⟨a, f⟩) i = f i '
' univ
· 使用定理 `Set.image_comp`：image_comp (f : β -> γ) (g : α -> β) (a : Set α) : f ∘ g
 '' a = f '' g '' a
-/
theorem supp_map (h : q.IsUniform) {α β : TypeVec n} (g : α ⟹ β) (x : F α) (i) :
    supp (g <$$> x) i = g i '' supp x i := by
  rw [← abs_repr x]; obtain ⟨a, f⟩ := repr x; rw [← abs_map, MvPFunctor.map_eq]
  rw [supp_eq_of_isUniform h, supp_eq_of_isUniform h, ← image_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-
**MvQPF.suppPreservation_iff_isUniform** 是 Mathlib 中的一个定理，位于命名空间 `MvQPF`。
形式化陈述：suppPreservation_iff_isUniform : q.SuppPreservation ↔ q.IsUniform
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPFunctor.supp_eq`：supp_eq {α : TypeVec n} (a : P.A) (f : P.B a ⟹ α) (i
) : @supp.{u} _ P.Obj _ α (⟨a, f⟩ : P α) i = f i '' univ
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `MvQPF.supp_eq_of_isUniform`：supp_eq_of_isUniform (h : q.IsUniform) {α : 
TypeVec n} (a : q.P.A) (f : q.P.B a ⟹ α) : forall i, supp (abs ⟨a, f⟩) i = f i '
' univ
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem suppPreservation_iff_isUniform : q.SuppPreservation ↔ q.IsUniform := by
  constructor
  · intro h α a a' f f' h' i
    rw [← MvPFunctor.supp_eq, ← MvPFunctor.supp_eq, ← h, h', h]
  · rintro h α ⟨a, f⟩
    ext
    rwa [supp_eq_of_isUniform, MvPFunctor.supp_eq]

set_option backward.isDefEq.respectTransparency false in
/-
**MvQPF.suppPreservation_iff_liftpPreservation** 是 Mathlib 中的一个定理，位于命名空间 `MvQPF`
。
形式化陈述：suppPreservation_iff_liftpPreservation : q.SuppPreservation ↔ q.LiftPPrese
rvation
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MvQPF.suppPreservation_iff_isUniform`：suppPreservation_iff_isUniform : q
.SuppPreservation ↔ q.IsUniform
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MvQPF.supp_eq_of_isUniform`：supp_eq_of_isUniform (h : q.IsUniform) {α : 
TypeVec n} (a : q.P.A) (f : q.P.B a ⟹ α) : forall i, supp (abs ⟨a, f⟩) i = f i '
' univ
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem suppPreservation_iff_liftpPreservation : q.SuppPreservation ↔ q.LiftPPreservation := by
  constructor <;> intro h
  · rintro α p ⟨a, f⟩
    have h' := h
    rw [suppPreservation_iff_isUniform] at h'
    dsimp only [SuppPreservation, supp] at h
    simp only [liftP_iff_of_isUniform, supp_eq_of_isUniform, MvPFunctor.liftP_iff', h',
      image_univ, mem_range, exists_imp]
    constructor <;> intros <;> subst_vars <;> solve_by_elim
  · rintro α ⟨a, f⟩
    simp only [LiftPPreservation] at h
    ext
    simp only [supp, h, mem_ofPred_eq]
/-
**MvQPF.liftpPreservation_iff_uniform** 是 Mathlib 中的一个定理，位于命名空间 `MvQPF`。
形式化陈述：liftpPreservation_iff_uniform : q.LiftPPreservation ↔ q.IsUniform
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvQPF.suppPreservation_iff_liftpPreservation`：suppPreservation_iff_liftp
Preservation : q.SuppPreservation ↔ q.LiftPPreservation
· 使用定理 `MvQPF.suppPreservation_iff_isUniform`：suppPreservation_iff_isUniform : q
.SuppPreservation ↔ q.IsUniform
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem liftpPreservation_iff_uniform : q.LiftPPreservation ↔ q.IsUniform := by
  rw [← suppPreservation_iff_liftpPreservation, suppPreservation_iff_isUniform]

set_option linter.style.whitespace false in -- manual alignment is not recognised
/-- Any type function `F` that is (extensionally) equivalent to a QPF, is itself a QPF,
assuming that the functorial map of `F` behaves similar to `MvFunctor.ofEquiv eqv` -/
@[instance_reducible]
/-
**MvQPF.ofEquiv** 是 Mathlib 中的一个定义，位于命名空间 `MvQPF`。
形式化陈述：ofEquiv {F F' : TypeVec.{u} n -> Type*} [q : MvQPF F'] [MvFunctor F] (eqv 
: forall α, F α ≃ F' α) (map_eq : forall (α β : TypeVec n) (f : α ⟹ β) (a : F α)
, f < > a = ((eqv _).symm <| f <$$> eqv _ a)
参数：eqv : forall α, F α ≃ F' α。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Any type function `F` that is (extensionally) equivalent to a QPF, is itself a Q
PF,
assuming that the functorial map of `F` behaves similar to `MvFunctor.ofEquiv eq
v`
-/
def ofEquiv {F F' : TypeVec.{u} n → Type*} [q : MvQPF F'] [MvFunctor F]
    (eqv : ∀ α, F α ≃ F' α)
    (map_eq : ∀ (α β : TypeVec n) (f : α ⟹ β) (a : F α),
      f <$$> a = ((eqv _).symm <| f <$$> eqv _ a) := by intros; rfl) :
    MvQPF F where
  P        := q.P
  abs α    := (eqv _).symm <| q.abs α
  repr α   := q.repr <| eqv _ α
  abs_repr := by simp [q.abs_repr]
  abs_map  := by simp [q.abs_map, map_eq]

end MvQPF

/-- Every polynomial functor is a (trivial) QPF -/
/-
**MvPFunctor.instMvQPFObj** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：MvPFunctor.instMvQPFObj {n} (P : MvPFunctor n) : MvQPF P where P
参数：P : MvPFunctor n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Every polynomial functor is a (trivial) QPF
-/
instance MvPFunctor.instMvQPFObj {n} (P : MvPFunctor n) : MvQPF P where
  P := P
  abs := id
  repr := id
  abs_repr := by intros; rfl
  abs_map := by intros; rfl
