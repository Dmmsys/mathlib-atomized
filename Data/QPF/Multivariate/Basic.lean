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

/--
Definition of `MvQPF` / `MvQPF` 的定义

English:
class MvQPF
  parameters: {n : Nat} (F : TypeVec.{u} n -> Type*)
  extends: MvFunctor F
  axioms and operations (4):
    - P : MvPFunctor.{u} n
    - abs : forall {α}, P α -> F α
    - repr : forall {α}, F α -> P α
    - abs_repr : forall {α} (x : F α), abs (repr x) = x

中文:
类 MvQPF
  参数: {n : 自然数} (F : TypeVec.{u} n -> 类型)
  继承: Mv函子 F
  公理与运算 (4 个):
    - P : MvP函子.{u} n
    - abs : 对任意 {α}, P α -> F α
    - repr : 对任意 {α}, F α -> P α
    - abs_repr : 对任意 {α} (x : F α), abs (repr x) = x
-/
class MvQPF {n : Nat} (F : TypeVec.{u} n -> Type*) extends MvFunctor F where
  P : MvPFunctor.{u} n
  abs : forall {α}, P α -> F α
  repr : forall {α}, F α -> P α
  abs_repr : forall {α} (x : F α), abs (repr x) = x
abs_map : forall {α β} (f : α ⟹ β) (p : P α), abs (f <$$> p) = f < > abs p

namespace MvQPF

variable {n : Nat} {F : TypeVec.{u} n -> Type*} [q : MvQPF F]

open MvFunctor (LiftP LiftR)



/--
theorem `id_map` / 定理 `id_map`

English:
theorem id_map
  given: {α : TypeVec n} (x : F α)
  statement: TypeVec.id < > x = x
  proof: by
  rw [← abs_repr x]; rw [← abs_map]
  rfl

@[simp]

中文:
定理 id_map
  条件: {α : TypeVec n} (x : F α)
  结论: TypeVec.id < > x = x
  证明: by
  rw [← abs_repr x]; rw [← abs_map]
  rfl

@[simp]
-/
protected theorem id_map {α : TypeVec n} (x : F α) : TypeVec.id < > x = x := by
  rw [← abs_repr x]; rw [← abs_map]
  rfl

@[simp]
/--
theorem `comp_map` / 定理 `comp_map`

English:
theorem comp_map
  given: {α β γ : TypeVec n} (f : α ⟹ β) (g : β ⟹ γ) (x : F α)
  proof: by
  rw [← abs_repr x]; rw [← abs_map]; rw [← abs_map]; rw [← abs_map]
  rfl

中文:
定理 comp_map
  条件: {α β γ : TypeVec n} (f : α ⟹ β) (g : β ⟹ γ) (x : F α)
  证明: by
  rw [← abs_repr x]; rw [← abs_map]; rw [← abs_map]; rw [← abs_map]
  rfl

Depends on / 依赖: abs_map, abs_repr
-/
theorem comp_map {α β γ : TypeVec n} (f : α ⟹ β) (g : β ⟹ γ) (x : F α) :
(g ⊚ f) < > x = g < > f < > x := by
  rw [← abs_repr x]; rw [← abs_map]; rw [← abs_map]; rw [← abs_map]
  rfl

instance (priority := 100) lawfulMvFunctor : LawfulMvFunctor F where
  id_map := @MvQPF.id_map n F _
  comp_map := @comp_map n F _

set_option backward.isDefEq.respectTransparency false in
-- Lifting predicates and relations
/--
theorem `liftP_iff` / 定理 `liftP_iff`

English:
theorem liftP_iff
  given: {α : TypeVec n} (p : forall ⦃i⦄, α i -> Prop) (x : F α)
  proof: by
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
  rw [← abs_map]; rw [h₀

中文:
定理 liftP_iff
  条件: {α : TypeVec n} (p : 对任意 ⦃i⦄, α i -> 命题) (x : F α)
  证明: by
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
  rw [← abs_map]; rw [h₀

Depends on / 依赖: abs_map, abs_repr, property
-/
theorem liftP_iff {α : TypeVec n} (p : forall ⦃i⦄, α i -> Prop) (x : F α) :
    LiftP p x ↔ exists a f, x = abs ⟨a, f⟩ ∧ forall i j, p (f i j) := by
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
  rw [← abs_map]; rw [h₀]; rfl

set_option backward.isDefEq.respectTransparency false in
/--
theorem `liftR_iff` / 定理 `liftR_iff`

English:
theorem liftR_iff
  given: {α : TypeVec n} (r : forall ⦃i⦄, α i -> α i -> Prop) (x y : F α)
  proof: by
  constructor
  · rintro ⟨u, xeq, yeq⟩
    rcases h : repr u with ⟨a, f⟩
    use a, fun i j => (f i j).val.fst, fun i j => (f i j).val.snd
    constructor
    · rw [← xeq, ← abs_repr u, h, ← abs_map]; rfl
    constructor
    · rw [← yeq, ← abs_repr u, h, ← abs_map]; rfl
    intro i j
    exact (f

中文:
定理 liftR_iff
  条件: {α : TypeVec n} (r : 对任意 ⦃i⦄, α i -> α i -> 命题) (x y : F α)
  证明: by
  constructor
  · rintro ⟨u, xeq, yeq⟩
    rcases h : repr u with ⟨a, f⟩
    use a, fun i j => (f i j).val.fst, fun i j => (f i j).val.snd
    constructor
    · rw [← xeq, ← abs_repr u, h, ← abs_map]; rfl
    constructor
    · rw [← yeq, ← abs_repr u, h, ← abs_map]; rfl
    intro i j
    exact (f

Depends on / 依赖: abs_map, abs_repr, property, val.fst, val.snd
-/
theorem liftR_iff {α : TypeVec n} (r : forall ⦃i⦄, α i -> α i -> Prop) (x y : F α) :
    LiftR r x y ↔ exists a f₀ f₁, x = abs ⟨a, f₀⟩ ∧ y = abs ⟨a, f₁⟩ ∧ forall i j, r (f₀ i j) (f₁ i j) := by
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
  rw [yeq]; rw [← abs_map]; rfl

open Set

/--
theorem `mem_supp` / 定理 `mem_supp`

English:
theorem mem_supp
  given: {α : TypeVec n} (x : F α) (i) (u : α i)
  proof: by
  rw [supp]; dsimp; constructor
  · intro h a f haf
    have : LiftP (fun i u => u in f i '' univ) x := by
      rw [liftP_iff]
      refine ⟨a, f, haf.symm, ?_⟩
      intro i u
      exact mem_image_of_mem _ (mem_univ _)
    exact h this
  grind [liftP_iff]

中文:
定理 mem_supp
  条件: {α : TypeVec n} (x : F α) (i) (u : α i)
  证明: by
  rw [supp]; dsimp; constructor
  · intro h a f haf
    have : LiftP (fun i u => u in f i '' univ) x := by
      rw [liftP_iff]
      refine ⟨a, f, haf.symm, ?_⟩
      intro i u
      exact mem_image_of_mem _ (mem_univ _)
    exact h this
  grind [liftP_iff]

Depends on / 依赖: haf.symm, liftP_iff, mem_image_of_mem, mem_univ
-/
theorem mem_supp {α : TypeVec n} (x : F α) (i) (u : α i) :
    u in supp x i ↔ forall a f, abs ⟨a, f⟩ = x -> u in f i '' univ := by
  rw [supp]; dsimp; constructor
  · intro h a f haf
    have : LiftP (fun i u => u in f i '' univ) x := by
      rw [liftP_iff]
      refine ⟨a, f, haf.symm, ?_⟩
      intro i u
      exact mem_image_of_mem _ (mem_univ _)
    exact h this
  grind [liftP_iff]

/--
theorem `supp_eq` / 定理 `supp_eq`

English:
theorem supp_eq
  given: {α : TypeVec n} {i} (x : F α)
  proof: by ext; apply mem_supp

中文:
定理 supp_eq
  条件: {α : TypeVec n} {i} (x : F α)
  证明: by ext; apply mem_supp

Depends on / 依赖: mem_supp
-/
theorem supp_eq {α : TypeVec n} {i} (x : F α) :
    supp x i = { u | forall a f, abs ⟨a, f⟩ = x -> u in f i '' univ } := by ext; apply mem_supp

set_option backward.isDefEq.respectTransparency false in
/--
theorem `has_good_supp_iff` / 定理 `has_good_supp_iff`

English:
theorem has_good_supp_iff
  given: {α : TypeVec n} (x : F α)
  proof: by
  constructor
  · intro h
    have : LiftP (fun i u => u in supp x i) x := by rw [h]; introv; exact id
    rw [liftP_iff] at this
    rcases this with ⟨a, f, xeq, h'⟩
    refine ⟨a, f, xeq.symm, ?_⟩
    intro a' f' h''
    rintro hu u ⟨j, _h₂, hfi⟩
    have hh : u in supp x a' := by rw [← hfi]; a

中文:
定理 has_good_supp_iff
  条件: {α : TypeVec n} (x : F α)
  证明: by
  constructor
  · intro h
    have : LiftP (fun i u => u in supp x i) x := by rw [h]; introv; exact id
    rw [liftP_iff] at this
    rcases this with ⟨a, f, xeq, h'⟩
    refine ⟨a, f, xeq.symm, ?_⟩
    intro a' f' h''
    rintro hu u ⟨j, _h₂, hfi⟩
    have hh : u in supp x a' := by rw [← hfi]; a

Depends on / 依赖: introv, liftP_iff, mem_supp, usuppx, xeq.symm
-/
theorem has_good_supp_iff {α : TypeVec n} (x : F α) :
    (forall p, LiftP p x ↔ forall (i), forall u in supp x i, p i u) ↔
      exists a f, abs ⟨a, f⟩ = x ∧ forall i a' f', abs ⟨a', f'⟩ = x -> f i '' univ subseteq f' i '' univ := by
  constructor
  · intro h
    have : LiftP (fun i u => u in supp x i) x := by rw [h]; introv; exact id
    rw [liftP_iff] at this
    rcases this with ⟨a, f, xeq, h'⟩
    refine ⟨a, f, xeq.symm, ?_⟩
    intro a' f' h''
    rintro hu u ⟨j, _h₂, hfi⟩
    have hh : u in supp x a' := by rw [← hfi]; apply h'
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

/--
Definition of `IsUniform` / `IsUniform` 的定义

English:
definition IsUniform
  signature: : Prop
  body: forall ⦃α : TypeVec n⦄ (a a' : q.P.A) (f : q.P.B a ⟹ α) (f' : q.P.B a' ⟹ α),
    abs ⟨a, f⟩ = abs ⟨a', f'⟩ -> forall i, f i '' univ = f' i '' univ

中文:
定义 是一致
  签名: : 命题
  定义体: forall ⦃α : TypeVec n⦄ (a a' : q.P.A) (f : q.P.B a ⟹ α) (f' : q.P.B a' ⟹ α),
    abs ⟨a, f⟩ = abs ⟨a', f'⟩ -> forall i, f i '' univ = f' i '' univ

Depends on / 依赖: TypeVec, q.P.A, q.P.B
-/
def IsUniform : Prop :=
  forall ⦃α : TypeVec n⦄ (a a' : q.P.A) (f : q.P.B a ⟹ α) (f' : q.P.B a' ⟹ α),
    abs ⟨a, f⟩ = abs ⟨a', f'⟩ -> forall i, f i '' univ = f' i '' univ

/--
Definition of `LiftPPreservation` / `LiftPPreservation` 的定义

English:
definition LiftPPreservation
  signature: : Prop
  body: forall ⦃α : TypeVec n⦄ (p : forall ⦃i⦄, α i -> Prop) (x : q.P α), LiftP p (abs x) ↔ LiftP p x

中文:
定义 LiftPPreservation
  签名: : 命题
  定义体: forall ⦃α : TypeVec n⦄ (p : forall ⦃i⦄, α i -> Prop) (x : q.P α), LiftP p (abs x) ↔ LiftP p x

Depends on / 依赖: TypeVec
-/
def LiftPPreservation : Prop :=
  forall ⦃α : TypeVec n⦄ (p : forall ⦃i⦄, α i -> Prop) (x : q.P α), LiftP p (abs x) ↔ LiftP p x

/--
Definition of `SuppPreservation` / `SuppPreservation` 的定义

English:
definition SuppPreservation
  signature: : Prop
  body: forall ⦃α⦄ (x : q.P α), supp (abs x) = supp x

中文:
定义 SuppPreservation
  签名: : 命题
  定义体: forall ⦃α⦄ (x : q.P α), supp (abs x) = supp x
-/
def SuppPreservation : Prop :=
  forall ⦃α⦄ (x : q.P α), supp (abs x) = supp x

/--
theorem `supp_eq_of_isUniform` / 定理 `supp_eq_of_isUniform`

English:
theorem supp_eq_of_isUniform
  given: (h : q.IsUniform) {α : TypeVec n} (a : q.P.A) (f : q.P.B a ⟹ α)
  proof: by
  intro; ext u; rw [mem_supp]; constructor
  · intro h'
    apply h' _ _ rfl
  intro h' a' f' e
  rw [← h _ _ _ _ e.symm]; apply h'

中文:
定理 supp_eq_of_isUniform
  条件: (h : q.是一致) {α : TypeVec n} (a : q.P.A) (f : q.P.B a ⟹ α)
  证明: by
  intro; ext u; rw [mem_supp]; constructor
  · intro h'
    apply h' _ _ rfl
  intro h' a' f' e
  rw [← h _ _ _ _ e.symm]; apply h'

Depends on / 依赖: e.symm, mem_supp
-/
theorem supp_eq_of_isUniform (h : q.IsUniform) {α : TypeVec n} (a : q.P.A) (f : q.P.B a ⟹ α) :
    forall i, supp (abs ⟨a, f⟩) i = f i '' univ := by
  intro; ext u; rw [mem_supp]; constructor
  · intro h'
    apply h' _ _ rfl
  intro h' a' f' e
  rw [← h _ _ _ _ e.symm]; apply h'

/--
theorem `liftP_iff_of_isUniform` / 定理 `liftP_iff_of_isUniform`

English:
theorem liftP_iff_of_isUniform
  given: (h : q.IsUniform) {α : TypeVec n} (x : F α) (p : forall i, α i -> Prop)
  proof: by
  rw [liftP_iff]; rw [← abs_repr x]
  obtain ⟨a, f⟩ := repr x; constructor
  · rintro ⟨a', f', abseq, hf⟩ u
    rw [supp_eq_of_isUniform h]; rw [h _ _ _ _ abseq]
    rintro b ⟨i, _, hi⟩
    rw [← hi]
    apply hf
  intro h'
  refine ⟨a, f, rfl, fun _ i => h' _ _ ?_⟩
  rw [supp_eq_of_isUniform h]


中文:
定理 liftP_iff_of_isUniform
  条件: (h : q.是一致) {α : TypeVec n} (x : F α) (p : 对任意 i, α i -> 命题)
  证明: by
  rw [liftP_iff]; rw [← abs_repr x]
  obtain ⟨a, f⟩ := repr x; constructor
  · rintro ⟨a', f', abseq, hf⟩ u
    rw [supp_eq_of_isUniform h]; rw [h _ _ _ _ abseq]
    rintro b ⟨i, _, hi⟩
    rw [← hi]
    apply hf
  intro h'
  refine ⟨a, f, rfl, fun _ i => h' _ _ ?_⟩
  rw [supp_eq_of_isUniform h]


Depends on / 依赖: abs_repr, liftP_iff, mem_univ, supp_eq_of_isUniform
-/
theorem liftP_iff_of_isUniform (h : q.IsUniform) {α : TypeVec n} (x : F α) (p : forall i, α i -> Prop) :
    LiftP p x ↔ forall (i), forall u in supp x i, p i u := by
  rw [liftP_iff]; rw [← abs_repr x]
  obtain ⟨a, f⟩ := repr x; constructor
  · rintro ⟨a', f', abseq, hf⟩ u
    rw [supp_eq_of_isUniform h]; rw [h _ _ _ _ abseq]
    rintro b ⟨i, _, hi⟩
    rw [← hi]
    apply hf
  intro h'
  refine ⟨a, f, rfl, fun _ i => h' _ _ ?_⟩
  rw [supp_eq_of_isUniform h]
  exact ⟨i, mem_univ i, rfl⟩

set_option backward.isDefEq.respectTransparency false in
/--
theorem `supp_map` / 定理 `supp_map`

English:
theorem supp_map
  given: (h : q.IsUniform) {α β : TypeVec n} (g : α ⟹ β) (x : F α) (i)
  proof: by
  rw [← abs_repr x]; obtain ⟨a, f⟩ := repr x; rw [← abs_map, MvPFunctor.map_eq]
  rw [supp_eq_of_isUniform h]; rw [supp_eq_of_isUniform h]; rw [← image_comp]
  rfl

中文:
定理 supp_map
  条件: (h : q.是一致) {α β : TypeVec n} (g : α ⟹ β) (x : F α) (i)
  证明: by
  rw [← abs_repr x]; obtain ⟨a, f⟩ := repr x; rw [← abs_map, MvPFunctor.map_eq]
  rw [supp_eq_of_isUniform h]; rw [supp_eq_of_isUniform h]; rw [← image_comp]
  rfl

Depends on / 依赖: MvPFunctor, MvPFunctor.map_eq, abs_map, abs_repr, image_comp, map_eq, supp_eq_of_isUniform
-/
theorem supp_map (h : q.IsUniform) {α β : TypeVec n} (g : α ⟹ β) (x : F α) (i) :
    supp (g <$$> x) i = g i '' supp x i := by
  rw [← abs_repr x]; obtain ⟨a, f⟩ := repr x; rw [← abs_map, MvPFunctor.map_eq]
  rw [supp_eq_of_isUniform h]; rw [supp_eq_of_isUniform h]; rw [← image_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
theorem `suppPreservation_iff_isUniform` / 定理 `suppPreservation_iff_isUniform`

English:
theorem suppPreservation_iff_isUniform
  statement: q.SuppPreservation ↔ q.IsUniform
  proof: by
  constructor
  · intro h α a a' f f' h' i
    rw [← MvPFunctor.supp_eq]; rw [← MvPFunctor.supp_eq]; rw [← h]; rw [h']; rw [h]
  · rintro h α ⟨a, f⟩
    ext
    rwa [supp_eq_of_isUniform, MvPFunctor.supp_eq]

中文:
定理 suppPreservation_iff_isUniform
  结论: q.SuppPreservation ↔ q.是一致
  证明: by
  constructor
  · intro h α a a' f f' h' i
    rw [← MvPFunctor.supp_eq]; rw [← MvPFunctor.supp_eq]; rw [← h]; rw [h']; rw [h]
  · rintro h α ⟨a, f⟩
    ext
    rwa [supp_eq_of_isUniform, MvPFunctor.supp_eq]

Depends on / 依赖: MvPFunctor, MvPFunctor.supp_eq, supp_eq, supp_eq_of_isUniform
-/
theorem suppPreservation_iff_isUniform : q.SuppPreservation ↔ q.IsUniform := by
  constructor
  · intro h α a a' f f' h' i
    rw [← MvPFunctor.supp_eq]; rw [← MvPFunctor.supp_eq]; rw [← h]; rw [h']; rw [h]
  · rintro h α ⟨a, f⟩
    ext
    rwa [supp_eq_of_isUniform, MvPFunctor.supp_eq]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `suppPreservation_iff_liftpPreservation` / 定理 `suppPreservation_iff_liftpPreservation`

English:
theorem suppPreservation_iff_liftpPreservation
  statement: q.SuppPreservation ↔ q.LiftPPreservation
  proof: by
  constructor <;> intro h
  · rintro α p ⟨a, f⟩
    have h' := h
    rw [suppPreservation_iff_isUniform] at h'
    dsimp only [SuppPreservation, supp] at h
    simp only [liftP_iff_of_isUniform, supp_eq_of_isUniform, MvPFunctor.liftP_iff', h',
      image_univ, mem_range, exists_imp]
    construc

中文:
定理 suppPreservation_iff_liftpPreservation
  结论: q.SuppPreservation ↔ q.LiftPPreservation
  证明: by
  constructor <;> intro h
  · rintro α p ⟨a, f⟩
    have h' := h
    rw [suppPreservation_iff_isUniform] at h'
    dsimp only [SuppPreservation, supp] at h
    simp only [liftP_iff_of_isUniform, supp_eq_of_isUniform, MvPFunctor.liftP_iff', h',
      image_univ, mem_range, exists_imp]
    construc

Depends on / 依赖: LiftPPreservation, MvPFunctor, MvPFunctor.liftP_iff, SuppPreservation, exists_imp, image_univ, intros, liftP_iff, liftP_iff_of_isUniform, mem_ofPred_eq, mem_range, solve_by_elim, suppPreservation_iff_isUniform, supp_eq_of_isUniform
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

/--
theorem `liftpPreservation_iff_uniform` / 定理 `liftpPreservation_iff_uniform`

English:
theorem liftpPreservation_iff_uniform
  statement: q.LiftPPreservation ↔ q.IsUniform
  proof: by
  rw [← suppPreservation_iff_liftpPreservation]; rw [suppPreservation_iff_isUniform]

中文:
定理 liftpPreservation_iff_uniform
  结论: q.LiftPPreservation ↔ q.是一致
  证明: by
  rw [← suppPreservation_iff_liftpPreservation]; rw [suppPreservation_iff_isUniform]

Depends on / 依赖: suppPreservation_iff_isUniform, suppPreservation_iff_liftpPreservation
-/
theorem liftpPreservation_iff_uniform : q.LiftPPreservation ↔ q.IsUniform := by
  rw [← suppPreservation_iff_liftpPreservation]; rw [suppPreservation_iff_isUniform]

set_option linter.style.whitespace false in -- manual alignment is not recognised
/-- Any type function `F` that is (extensionally) equivalent to a QPF, is itself a QPF,
assuming that the functorial map of `F` behaves similar to `MvFunctor.ofEquiv eqv` -/
@[instance_reducible]
/--
Definition of `ofEquiv` / `ofEquiv` 的定义

English:
definition ofEquiv
  signature: {F F' : TypeVec.{u} n -> Type*} [q : MvQPF F'] [MvFunctor F]
  body: q.P
abs α := (eqv _).symm q.abs α
repr α := q.repr eqv _ α
  abs_repr := by simp [q.abs_repr]
  abs_map := by simp [q.abs_map, map_eq]

中文:
定义 ofEquiv
  签名: {F F' : TypeVec.{u} n -> 类型} [q : MvQPF F'] [Mv函子 F]
  定义体: q.P
abs α := (eqv _).symm q.abs α
repr α := q.repr eqv _ α
  abs_repr := by simp [q.abs_repr]
  abs_map := by simp [q.abs_map, map_eq]

Depends on / 依赖: abs_map, abs_repr, intros, map_eq, q.abs, q.abs_map, q.abs_repr, q.repr
-/
def ofEquiv {F F' : TypeVec.{u} n -> Type*} [q : MvQPF F'] [MvFunctor F]
    (eqv : forall α, F α ≃ F' α)
    (map_eq : forall (α β : TypeVec n) (f : α ⟹ β) (a : F α),
f < > a = ((eqv _).symm <| f <$$> eqv _ a) := by intros; rfl) :
    MvQPF F where
  P := q.P
abs α := (eqv _).symm q.abs α
repr α := q.repr eqv _ α
  abs_repr := by simp [q.abs_repr]
  abs_map := by simp [q.abs_map, map_eq]

end MvQPF

/--
Instance `MvPFunctor.instMvQPFObj` / 实例 `MvPFunctor.instMvQPFObj`

English:
instance MvPFunctor.instMvQPFObj
  signature: {n} (P : MvPFunctor n)
  body: P
  abs := id
  repr := id
  abs_repr := by intros; rfl
  abs_map := by intros; rfl

中文:
实例 MvP函子.instMvQPFObj
  签名: {n} (P : MvP函子 n)
  定义体: P
  abs := id
  repr := id
  abs_repr := by intros; rfl
  abs_map := by intros; rfl
-/
instance MvPFunctor.instMvQPFObj {n} (P : MvPFunctor n) : MvQPF P where
  P := P
  abs := id
  repr := id
  abs_repr := by intros; rfl
  abs_map := by intros; rfl
