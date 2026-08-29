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
/--
Definition of `NonemptyFiniteChains` / `NonemptyFiniteChains` 的定义

English:
structure NonemptyFiniteChains
  parameters: (X : Type u) [PartialOrder X]
  axioms and operations (3):
    - finset : Finset X
    - nonempty : finset.Nonempty  [default: by simp]
    - comparable((a b : finset)) : a <= b ∨ b <= a

中文:
结构 NonemptyFiniteChains
  参数: (X : 类型u) [偏序 X]
  公理与运算 (3 个):
    - finset : 有限集 X
    - nonempty : finset.非空  [默认: by simp]
    - comparable((a b : finset)) : a <= b ∨ b <= a

Depends on / 依赖: comparable, finset
-/
structure NonemptyFiniteChains (X : Type u) [PartialOrder X] where
  /-- a finite subset -/
  finset : Finset X
  nonempty : finset.Nonempty := by simp
  comparable (a b : finset) : a <= b ∨ b <= a

namespace NonemptyFiniteChains

attribute [simp] nonempty

instance (X : Type u) [PartialOrder X] : PartialOrder (NonemptyFiniteChains X) :=
  PartialOrder.lift finset (fun _ _ _ => by aesop)

variable {X Y : Type*} [PartialOrder X] [PartialOrder Y]

@[simp]
/--
lemma `le_iff` / 引理 `le_iff`

English:
lemma le_iff
  given: (A B : NonemptyFiniteChains X)
  statement: A <= B ↔ A.finset <= B.finset
  proof: Iff.rfl

@[simp]

中文:
引理 le_iff
  条件: (A B : NonemptyFiniteChains X)
  结论: A <= B ↔ A.finset <= B.finset
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
lemma le_iff (A B : NonemptyFiniteChains X) : A <= B ↔ A.finset <= B.finset := Iff.rfl

@[simp]
/--
lemma `lt_iff` / 引理 `lt_iff`

English:
lemma lt_iff
  given: (A B : NonemptyFiniteChains X)
  statement: A < B ↔ A.finset < B.finset
  proof: Iff.rfl

中文:
引理 lt_iff
  条件: (A B : NonemptyFiniteChains X)
  结论: A < B ↔ A.finset < B.finset
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma lt_iff (A B : NonemptyFiniteChains X) : A < B ↔ A.finset < B.finset := Iff.rfl

open scoped Classical in
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (s : NonemptyFiniteChains X) (f : X ->o Y)
  body: Finset.image f s.finset
  comparable := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    simp only [Finset.mem_image] at ha hb
    obtain ⟨a, ha', rfl⟩ := ha
    obtain ⟨b, hb', rfl⟩ := hb
    obtain h | h := s.comparable ⟨_, ha'⟩ ⟨_, hb'⟩
    · exact Or.inl (f.monotone h)
    · exact Or.inr (f.monotone h)

@[simp

中文:
定义 map
  签名: (s : NonemptyFiniteChains X) (f : X ->o Y)
  定义体: Finset.image f s.finset
  comparable := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    simp only [Finset.mem_image] at ha hb
    obtain ⟨a, ha', rfl⟩ := ha
    obtain ⟨b, hb', rfl⟩ := hb
    obtain h | h := s.comparable ⟨_, ha'⟩ ⟨_, hb'⟩
    · exact Or.inl (f.monotone h)
    · exact Or.inr (f.monotone h)

@[simp

Depends on / 依赖: Finset, Finset.image, finset, s.finset
-/
noncomputable def map (s : NonemptyFiniteChains X) (f : X ->o Y) :
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
/--
lemma `mem_map_iff` / 引理 `mem_map_iff`

English:
lemma mem_map_iff
  given: (s : NonemptyFiniteChains X) (f : X ->o Y) (y : Y)
  proof: by
  simp [map]

中文:
引理 mem_map_iff
  条件: (s : NonemptyFiniteChains X) (f : X ->o Y) (y : Y)
  证明: by
  simp [map]
-/
lemma mem_map_iff (s : NonemptyFiniteChains X) (f : X ->o Y) (y : Y) :
    y in (s.map f).finset ↔ exists x, x in s.finset ∧ f x = y := by
  simp [map]

/-- The monotone map `NonemptyFiniteChains X →o NonemptyFiniteChains Y`
that is induced by `f : X →o Y`. -/
@[simps]
/--
Definition of `orderHomMap` / `orderHomMap` 的定义

English:
definition orderHomMap
  signature: (f : X ->o Y)
  body: map s f
  monotone' a b h x hx := by
    simp only [mem_map_iff] at hx ⊢
    obtain ⟨x, hx, rfl⟩ := hx
    exact ⟨x, h hx, rfl⟩

中文:
定义 orderHomMap
  签名: (f : X ->o Y)
  定义体: map s f
  monotone' a b h x hx := by
    simp only [mem_map_iff] at hx ⊢
    obtain ⟨x, hx, rfl⟩ := hx
    exact ⟨x, h hx, rfl⟩
-/
noncomputable def orderHomMap (f : X ->o Y) :
    NonemptyFiniteChains X ->o NonemptyFiniteChains Y where
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
/--
Definition of `PartOrd.nonemptyFiniteChainsFunctor` / `PartOrd.nonemptyFiniteChainsFunctor` 的定义

English:
definition PartOrd.nonemptyFiniteChainsFunctor
  signature: : PartOrd.{u} ⥤ PartOrd.{u} where
  body: .of (NonemptyFiniteChains X)
  map f := PartOrd.ofHom (NonemptyFiniteChains.orderHomMap f.hom)

中文:
定义 偏序.nonemptyFiniteChainsFunctor
  签名: : 偏序.{u} ⥤ 偏序.{u} where
  定义体: .of (NonemptyFiniteChains X)
  map f := PartOrd.ofHom (NonemptyFiniteChains.orderHomMap f.hom)

Depends on / 依赖: NonemptyFiniteChains
-/
noncomputable def PartOrd.nonemptyFiniteChainsFunctor : PartOrd.{u} ⥤ PartOrd.{u} where
  obj X := .of (NonemptyFiniteChains X)
  map f := PartOrd.ofHom (NonemptyFiniteChains.orderHomMap f.hom)
