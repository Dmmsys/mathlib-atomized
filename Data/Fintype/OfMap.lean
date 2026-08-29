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
/--
Definition of `ofMultiset` / `ofMultiset` 的定义

English:
definition ofMultiset
  signature: [DecidableEq α] (s : Multiset α) (H : forall x : α, x in s)
  body: ⟨s.toFinset, by simpa using H⟩

中文:
定义 ofMultiset
  签名: [DecidableEq α] (s : Multiset α) (H : 对任意 x : α, x in s)
  定义体: ⟨s.toFinset, by simpa using H⟩

Depends on / 依赖: s.toFinset, toFinset
-/
def ofMultiset [DecidableEq α] (s : Multiset α) (H : forall x : α, x in s) : Fintype α :=
  ⟨s.toFinset, by simpa using H⟩

/-- Construct a proof of `Fintype α` from a universal list -/
@[instance_reducible]
/--
Definition of `ofList` / `ofList` 的定义

English:
definition ofList
  signature: [DecidableEq α] (l : List α) (H : forall x : α, x in l)
  body: ⟨l.toFinset, by simpa using H⟩

中文:
定义 ofList
  签名: [DecidableEq α] (l : List α) (H : 对任意 x : α, x in l)
  定义体: ⟨l.toFinset, by simpa using H⟩

Depends on / 依赖: l.toFinset, toFinset
-/
def ofList [DecidableEq α] (l : List α) (H : forall x : α, x in l) : Fintype α :=
  ⟨l.toFinset, by simpa using H⟩

/-- If `f : α → β` is a bijection and `α` is a fintype, then `β` is also a fintype. -/
@[instance_reducible]
/--
Definition of `ofBijective` / `ofBijective` 的定义

English:
definition ofBijective
  signature: [Fintype α] (f : α -> β) (H : Function.Bijective f)
  body: ⟨univ.map ⟨f, H.1⟩, fun b =>
    let ⟨_, e⟩ := H.2 b
    e ▸ mem_map_of_mem _ (mem_univ _)⟩

中文:
定义 ofBijective
  签名: [Fintype α] (f : α -> β) (H : Function.Bijective f)
  定义体: ⟨univ.map ⟨f, H.1⟩, fun b =>
    let ⟨_, e⟩ := H.2 b
    e ▸ mem_map_of_mem _ (mem_univ _)⟩

Depends on / 依赖: mem_map_of_mem, mem_univ, univ.map
-/
def ofBijective [Fintype α] (f : α -> β) (H : Function.Bijective f) : Fintype β :=
  ⟨univ.map ⟨f, H.1⟩, fun b =>
    let ⟨_, e⟩ := H.2 b
    e ▸ mem_map_of_mem _ (mem_univ _)⟩

/-- If `f : α → β` is a surjection and `α` is a fintype, then `β` is also a fintype. -/
@[instance_reducible]
/--
Definition of `ofSurjective` / `ofSurjective` 的定义

English:
definition ofSurjective
  signature: [DecidableEq β] [Fintype α] (f : α -> β) (H : Function.Surjective f)
  body: ⟨univ.image f, fun b =>
    let ⟨_, e⟩ := H b
    e ▸ mem_image_of_mem _ (mem_univ _)⟩

中文:
定义 ofSurjective
  签名: [DecidableEq β] [Fintype α] (f : α -> β) (H : Function.Surjective f)
  定义体: ⟨univ.image f, fun b =>
    let ⟨_, e⟩ := H b
    e ▸ mem_image_of_mem _ (mem_univ _)⟩

Depends on / 依赖: mem_image_of_mem, mem_univ, univ.image
-/
def ofSurjective [DecidableEq β] [Fintype α] (f : α -> β) (H : Function.Surjective f) : Fintype β :=
  ⟨univ.image f, fun b =>
    let ⟨_, e⟩ := H b
    e ▸ mem_image_of_mem _ (mem_univ _)⟩

/-- Given an injective function to a fintype, the domain is also a
fintype. This is noncomputable because injectivity alone cannot be
used to construct preimages. -/
@[instance_reducible]
/--
Definition of `ofInjective` / `ofInjective` 的定义

English:
definition ofInjective
  signature: [Fintype β] (f : α -> β) (H : Function.Injective f)
  body: letI := Classical.dec
  if hα : Nonempty α then
    letI := Classical.inhabited_of_nonempty hα
    ofSurjective (invFun f) (invFun_surjective H)
  else ⟨∅, fun x => (hα ⟨x⟩).elim⟩

中文:
定义 ofInjective
  签名: [Fintype β] (f : α -> β) (H : Function.Injective f)
  定义体: letI := Classical.dec
  if hα : Nonempty α then
    letI := Classical.inhabited_of_nonempty hα
    ofSurjective (invFun f) (invFun_surjective H)
  else ⟨∅, fun x => (hα ⟨x⟩).elim⟩

Depends on / 依赖: Classical, Classical.dec, Classical.inhabited_of_nonempty, Nonempty, inhabited_of_nonempty, invFun, invFun_surjective, ofSurjective
-/
noncomputable def ofInjective [Fintype β] (f : α -> β) (H : Function.Injective f) : Fintype α :=
  letI := Classical.dec
  if hα : Nonempty α then
    letI := Classical.inhabited_of_nonempty hα
    ofSurjective (invFun f) (invFun_surjective H)
  else ⟨∅, fun x => (hα ⟨x⟩).elim⟩

/-- If `f : α ≃ β` and `α` is a fintype, then `β` is also a fintype. -/
@[instance_reducible]
/--
Definition of `ofEquiv` / `ofEquiv` 的定义

English:
definition ofEquiv
  signature: (α : Type*) [Fintype α] (f : α ≃ β)
  body: ofBijective _ f.bijective

中文:
定义 ofEquiv
  签名: (α : 类型) [Fintype α] (f : α ≃ β)
  定义体: ofBijective _ f.bijective

Depends on / 依赖: bijective, f.bijective, ofBijective
-/
def ofEquiv (α : Type*) [Fintype α] (f : α ≃ β) : Fintype β :=
  ofBijective _ f.bijective

/-- Any subsingleton type with a witness is a fintype (with one term). -/
@[instance_reducible]
/--
Definition of `ofSubsingleton` / `ofSubsingleton` 的定义

English:
definition ofSubsingleton
  signature: (a : α) [Subsingleton α]
  body: ⟨{a}, fun _ => Finset.mem_singleton.2 (Subsingleton.elim _ _)⟩

中文:
定义 ofSubsingleton
  签名: (a : α) [Subsingleton α]
  定义体: ⟨{a}, fun _ => Finset.mem_singleton.2 (Subsingleton.elim _ _)⟩

Depends on / 依赖: Finset, Finset.mem_singleton, Subsingleton, Subsingleton.elim, mem_singleton
-/
def ofSubsingleton (a : α) [Subsingleton α] : Fintype α :=
  ⟨{a}, fun _ => Finset.mem_singleton.2 (Subsingleton.elim _ _)⟩

-- In principle, this could be a `simp` theorem but it applies to any occurrence of `univ` and
-- required unification of the (possibly very complex) `Fintype` instances.
/--
theorem `univ_ofSubsingleton` / 定理 `univ_ofSubsingleton`

English:
theorem univ_ofSubsingleton
  given: (a : α) [Subsingleton α]
  statement: @univ _ (ofSubsingleton a) = {a}
  proof: rfl

中文:
定理 univ_ofSubsingleton
  条件: (a : α) [Subsingleton α]
  结论: @univ _ (ofSubsingleton a) = {a}
  证明: rfl
-/
theorem univ_ofSubsingleton (a : α) [Subsingleton α] : @univ _ (ofSubsingleton a) = {a} :=
  rfl

/-- An empty type is a fintype. Not registered as an instance, to make sure that there aren't two
conflicting `Fintype ι` instances around when casing over whether a fintype `ι` is empty or not. -/
@[instance_reducible]
/--
Definition of `ofIsEmpty` / `ofIsEmpty` 的定义

English:
definition ofIsEmpty
  signature: [IsEmpty α]
  body: ⟨∅, isEmptyElim⟩

中文:
定义 ofIsEmpty
  签名: [IsEmpty α]
  定义体: ⟨∅, isEmptyElim⟩

Depends on / 依赖: isEmptyElim
-/
def ofIsEmpty [IsEmpty α] : Fintype α :=
  ⟨∅, isEmptyElim⟩

/--
theorem `univ_ofIsEmpty` / 定理 `univ_ofIsEmpty`

English:
theorem univ_ofIsEmpty
  given: [IsEmpty α]
  statement: @univ α Fintype.ofIsEmpty = ∅
  proof: rfl

中文:
定理 univ_ofIsEmpty
  条件: [IsEmpty α]
  结论: @univ α Fintype.ofIsEmpty = ∅
  证明: rfl
-/
theorem univ_ofIsEmpty [IsEmpty α] : @univ α Fintype.ofIsEmpty = ∅ :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Fintype Empty
  body: Fintype.ofIsEmpty

中文:
实例 :
  签名: Fintype Empty
  定义体: Fintype.ofIsEmpty

Depends on / 依赖: Fintype, Fintype.ofIsEmpty, ofIsEmpty
-/
instance : Fintype Empty := Fintype.ofIsEmpty
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Fintype PEmpty
  body: Fintype.ofIsEmpty

中文:
实例 :
  签名: Fintype PEmpty
  定义体: Fintype.ofIsEmpty

Depends on / 依赖: Fintype, Fintype.ofIsEmpty, ofIsEmpty
-/
instance : Fintype PEmpty := Fintype.ofIsEmpty

end Fintype
