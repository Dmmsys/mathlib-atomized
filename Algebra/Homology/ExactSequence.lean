/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.CategoryTheory.ComposableArrows.Basic

/-!
# Exact sequences

A sequence of `n` composable arrows `S : ComposableArrows C` (i.e. a functor
`S : Fin (n + 1) ⥤ C`) is said to be exact (`S.Exact`) if the composition
of two consecutive arrows are zero (`S.IsComplex`) and the diagram is
exact at each `i` for `1 ≤ i < n`.

Together with the inductive construction of composable arrows
`ComposableArrows.precomp`, this is useful in order to state that certain
finite sequences of morphisms are exact (e.g the snake lemma), even though
in the applications it would usually be more convenient to use individual
lemmas expressing the exactness at a particular object.

This implementation is a refactor of `exact_seq` with appeared in the
Liquid Tensor Experiment as a property of lists in `Arrow C`.

-/

@[expose] public section

namespace CategoryTheory

open Limits

variable {C : Type*} [Category* C] [HasZeroMorphisms C]

/-- The composable arrows associated to a short complex. -/
@[simps!]
/--
Definition of `ShortComplex.toComposableArrows` / `ShortComplex.toComposableArrows` 的定义

English:
definition ShortComplex.toComposableArrows
  signature: (S : ShortComplex C)
  body: ComposableArrows.mk₂ S.f S.g

中文:
定义 短复形.toComposableArrows
  签名: (S : 短复形 C)
  定义体: ComposableArrows.mk₂ S.f S.g

Depends on / 依赖: ComposableArrows, ComposableArrows.mk
-/
def ShortComplex.toComposableArrows (S : ShortComplex C) : ComposableArrows C 2 :=
  ComposableArrows.mk₂ S.f S.g

/--
Definition of `ShortComplex.mapToComposableArrows` / `ShortComplex.mapToComposableArrows` 的定义

English:
definition ShortComplex.mapToComposableArrows
  signature: {S₁ S₂ : ShortComplex C} (φ : S₁ ⟶ S₂)
  body: ComposableArrows.homMk₂ φ.τ₁ φ.τ₂ φ.τ₃ φ.comm₁₂.symm φ.comm₂₃.symm

@[simp]

中文:
定义 短复形.mapToComposableArrows
  签名: {S₁ S₂ : 短复形 C} (φ : S₁ ⟶ S₂)
  定义体: ComposableArrows.homMk₂ φ.τ₁ φ.τ₂ φ.τ₃ φ.comm₁₂.symm φ.comm₂₃.symm

@[simp]

Depends on / 依赖: ComposableArrows, ComposableArrows.homMk
-/
def ShortComplex.mapToComposableArrows {S₁ S₂ : ShortComplex C} (φ : S₁ ⟶ S₂) :
    S₁.toComposableArrows ⟶ S₂.toComposableArrows :=
  ComposableArrows.homMk₂ φ.τ₁ φ.τ₂ φ.τ₃ φ.comm₁₂.symm φ.comm₂₃.symm

@[simp]
/--
theorem `ShortComplex.mapToComposableArrows_app_0` / 定理 `ShortComplex.mapToComposableArrows_app_0`

English:
theorem ShortComplex.mapToComposableArrows_app_0
  given: {S₁ S₂ : ShortComplex C} (φ : S₁ ⟶ S₂)
  proof: rfl

@[simp]

中文:
定理 短复形.mapToComposableArrows_app_0
  条件: {S₁ S₂ : 短复形 C} (φ : S₁ ⟶ S₂)
  证明: rfl

@[simp]
-/
theorem ShortComplex.mapToComposableArrows_app_0 {S₁ S₂ : ShortComplex C} (φ : S₁ ⟶ S₂) :
    (ShortComplex.mapToComposableArrows φ).app 0 = φ.τ₁ := rfl

@[simp]
/--
theorem `ShortComplex.mapToComposableArrows_app_1` / 定理 `ShortComplex.mapToComposableArrows_app_1`

English:
theorem ShortComplex.mapToComposableArrows_app_1
  given: {S₁ S₂ : ShortComplex C} (φ : S₁ ⟶ S₂)
  proof: rfl

@[simp]

中文:
定理 短复形.mapToComposableArrows_app_1
  条件: {S₁ S₂ : 短复形 C} (φ : S₁ ⟶ S₂)
  证明: rfl

@[simp]
-/
theorem ShortComplex.mapToComposableArrows_app_1 {S₁ S₂ : ShortComplex C} (φ : S₁ ⟶ S₂) :
    (ShortComplex.mapToComposableArrows φ).app 1 = φ.τ₂ := rfl

@[simp]
/--
theorem `ShortComplex.mapToComposableArrows_app_2` / 定理 `ShortComplex.mapToComposableArrows_app_2`

English:
theorem ShortComplex.mapToComposableArrows_app_2
  given: {S₁ S₂ : ShortComplex C} (φ : S₁ ⟶ S₂)
  proof: rfl

@[simp]

中文:
定理 短复形.mapToComposableArrows_app_2
  条件: {S₁ S₂ : 短复形 C} (φ : S₁ ⟶ S₂)
  证明: rfl

@[simp]
-/
theorem ShortComplex.mapToComposableArrows_app_2 {S₁ S₂ : ShortComplex C} (φ : S₁ ⟶ S₂) :
    (ShortComplex.mapToComposableArrows φ).app 2 = φ.τ₃ := rfl

@[simp]
/--
theorem `ShortComplex.mapToComposableArrows_id` / 定理 `ShortComplex.mapToComposableArrows_id`

English:
theorem ShortComplex.mapToComposableArrows_id
  given: {S₁ : ShortComplex C}
  proof: by
  cat_disch

@[simp]

中文:
定理 短复形.mapToComposableArrows_id
  条件: {S₁ : 短复形 C}
  证明: by
  cat_disch

@[simp]

Depends on / 依赖: cat_disch
-/
theorem ShortComplex.mapToComposableArrows_id {S₁ : ShortComplex C} :
    (ShortComplex.mapToComposableArrows (𝟙 S₁)) = 𝟙 S₁.toComposableArrows := by
  cat_disch

@[simp]
/--
theorem `ShortComplex.mapToComposableArrows_comp` / 定理 `ShortComplex.mapToComposableArrows_comp`

English:
theorem ShortComplex.mapToComposableArrows_comp
  statement: {S₁ S₂ S₃ : ShortComplex C} (φ : S₁ ⟶ S₂)
  proof: by
  cat_disch

中文:
定理 短复形.mapToComposableArrows_comp
  结论: {S₁ S₂ S₃ : 短复形 C} (φ : S₁ ⟶ S₂)
  证明: by
  cat_disch

Depends on / 依赖: cat_disch
-/
theorem ShortComplex.mapToComposableArrows_comp {S₁ S₂ S₃ : ShortComplex C} (φ : S₁ ⟶ S₂)
    (ψ : S₂ ⟶ S₃) : ShortComplex.mapToComposableArrows (φ ≫ ψ) =
      ShortComplex.mapToComposableArrows φ ≫ ShortComplex.mapToComposableArrows ψ := by
  cat_disch

namespace ComposableArrows

variable {n : Nat} (S : ComposableArrows C n)

-- We do not yet replace `omega` with `lia` here, as it is measurably slower.
/--
Definition of `IsComplex` / `IsComplex` 的定义

English:
structure IsComplex
  parameters: : Prop where
  axioms and operations (1):
    - zero((i : Nat) (hi : i + 2 <= n := by omega)) : S.map' i (i + 1) ≫ S.map' (i + 1) (i + 2) = 0

中文:
结构 是复形
  参数: : 命题 where
  公理与运算 (1 个):
    - zero((i : 自然数) (hi : i + 2 <= n := by omega)) : S.map' i (i + 1) ≫ S.map' (i + 1) (i + 2) = 0

Depends on / 依赖: S.map
-/
structure IsComplex : Prop where
  /-- the composition of two consecutive arrows is zero -/
  zero (i : Nat) (hi : i + 2 <= n := by omega) :
    S.map' i (i + 1) ≫ S.map' (i + 1) (i + 2) = 0

attribute [reassoc] IsComplex.zero

variable {S}

@[reassoc]
/--
lemma `IsComplex.zero'` / 引理 `IsComplex.zero'`

English:
lemma IsComplex.zero'
  statement: (hS : S.IsComplex) (i j k : Nat) (hij : i + 1 = j := by omega)
  proof: by
  subst hij hjk
  exact hS.zero i hk

中文:
引理 是复形.zero'
  结论: (hS : S.是复形) (i j k : 自然数) (hij : i + 1 = j := by omega)
  证明: by
  subst hij hjk
  exact hS.zero i hk

Depends on / 依赖: S.map, hS.zero
-/
lemma IsComplex.zero' (hS : S.IsComplex) (i j k : Nat) (hij : i + 1 = j := by omega)
    (hjk : j + 1 = k := by omega) (hk : k <= n := by omega) :
    S.map' i j ≫ S.map' j k = 0 := by
  subst hij hjk
  exact hS.zero i hk

/--
lemma `isComplex_of_iso` / 引理 `isComplex_of_iso`

English:
lemma isComplex_of_iso
  given: {S₁ S₂ : ComposableArrows C n} (e : S₁ ≅ S₂) (h₁ : S₁.IsComplex)
  proof: by
    rw [← cancel_epi (ComposableArrows.app' e.hom i)]; rw [comp_zero]; rw [← NatTrans.naturality_assoc]; rw [← NatTrans.naturality]; rw [reassoc_of% (h₁.zero i hi)]; rw [zero_comp]

中文:
引理 isComplex_of_iso
  条件: {S₁ S₂ : ComposableArrows C n} (e : S₁ ≅ S₂) (h₁ : S₁.是复形)
  证明: by
    rw [← cancel_epi (ComposableArrows.app' e.hom i)]; rw [comp_zero]; rw [← NatTrans.naturality_assoc]; rw [← NatTrans.naturality]; rw [reassoc_of% (h₁.zero i hi)]; rw [zero_comp]

Depends on / 依赖: ComposableArrows, ComposableArrows.app, NatTrans, NatTrans.naturality, NatTrans.naturality_assoc, cancel_epi, comp_zero, e.hom, naturality, naturality_assoc, reassoc_of, zero_comp
-/
lemma isComplex_of_iso {S₁ S₂ : ComposableArrows C n} (e : S₁ ≅ S₂) (h₁ : S₁.IsComplex) :
    S₂.IsComplex where
  zero i hi := by
    rw [← cancel_epi (ComposableArrows.app' e.hom i)]; rw [comp_zero]; rw [← NatTrans.naturality_assoc]; rw [← NatTrans.naturality]; rw [reassoc_of% (h₁.zero i hi)]; rw [zero_comp]

/--
lemma `isComplex_iff_of_iso` / 引理 `isComplex_iff_of_iso`

English:
lemma isComplex_iff_of_iso
  given: {S₁ S₂ : ComposableArrows C n} (e : S₁ ≅ S₂)
  proof: ⟨isComplex_of_iso e, isComplex_of_iso e.symm⟩

中文:
引理 isComplex_iff_of_iso
  条件: {S₁ S₂ : ComposableArrows C n} (e : S₁ ≅ S₂)
  证明: ⟨isComplex_of_iso e, isComplex_of_iso e.symm⟩

Depends on / 依赖: e.symm, isComplex_of_iso
-/
lemma isComplex_iff_of_iso {S₁ S₂ : ComposableArrows C n} (e : S₁ ≅ S₂) :
    S₁.IsComplex ↔ S₂.IsComplex :=
  ⟨isComplex_of_iso e, isComplex_of_iso e.symm⟩

/--
lemma `isComplex₀` / 引理 `isComplex₀`

English:
lemma isComplex₀
  given: (S : ComposableArrows C 0)
  statement: S.IsComplex where
  proof: by simp at hi

中文:
引理 isComplex₀
  条件: (S : ComposableArrows C 0)
  结论: S.是复形 where
  证明: by simp at hi
-/
lemma isComplex₀ (S : ComposableArrows C 0) : S.IsComplex where
  zero i hi := by simp at hi

/--
lemma `isComplex₁` / 引理 `isComplex₁`

English:
lemma isComplex₁
  given: (S : ComposableArrows C 1)
  statement: S.IsComplex where
  proof: by lia

中文:
引理 isComplex₁
  条件: (S : ComposableArrows C 1)
  结论: S.是复形 where
  证明: by lia
-/
lemma isComplex₁ (S : ComposableArrows C 1) : S.IsComplex where
  zero i hi := by lia

variable (S)

/--
Definition of `sc'` / `sc'` 的定义

English:
abbreviation sc'
  signature: (hS : S.IsComplex) (i j k : Nat) (hij : i + 1 = j := by omega)
  body: ShortComplex.mk (S.map' i j) (S.map' j k) (hS.zero' i j k)

中文:
缩写 sc'
  签名: (hS : S.是复形) (i j k : 自然数) (hij : i + 1 = j := by omega)
  定义体: ShortComplex.mk (S.map' i j) (S.map' j k) (hS.zero' i j k)

Depends on / 依赖: S.map, ShortComplex, ShortComplex.mk, hS.zero
-/
abbrev sc' (hS : S.IsComplex) (i j k : Nat) (hij : i + 1 = j := by omega)
    (hjk : j + 1 = k := by omega) (hk : k <= n := by omega) :
    ShortComplex C :=
  ShortComplex.mk (S.map' i j) (S.map' j k) (hS.zero' i j k)

/--
Definition of `sc` / `sc` 的定义

English:
abbreviation sc
  signature: (hS : S.IsComplex) (i : Nat) (hi : i + 2 <= n := by omega)
  body: S.sc' hS i (i + 1) (i + 2)

中文:
缩写 sc
  签名: (hS : S.是复形) (i : 自然数) (hi : i + 2 <= n := by omega)
  定义体: S.sc' hS i (i + 1) (i + 2)

Depends on / 依赖: S.sc, ShortComplex
-/
abbrev sc (hS : S.IsComplex) (i : Nat) (hi : i + 2 <= n := by omega) :
    ShortComplex C :=
  S.sc' hS i (i + 1) (i + 2)

/--
Definition of `Exact` / `Exact` 的定义

English:
structure Exact
  parameters: : Prop extends S.IsComplex where
  extends: S.IsComplex
  axioms and operations (1):
    - exact((i : Nat) (hi : i + 2 <= n := by omega)) : (S.sc toIsComplex i).Exact

中文:
结构 正合
  参数: : 命题 extends S.是复形 where
  继承: S.是复形
  公理与运算 (1 个):
    - exact((i : 自然数) (hi : i + 2 <= n := by omega)) : (S.sc toIsComplex i).正合

Depends on / 依赖: S.sc, toIsComplex
-/
structure Exact : Prop extends S.IsComplex where
  exact (i : Nat) (hi : i + 2 <= n := by omega) : (S.sc toIsComplex i).Exact

variable {S}

/--
lemma `Exact.exact'` / 引理 `Exact.exact'`

English:
lemma Exact.exact'
  statement: (hS : S.Exact) (i j k : Nat) (hij : i + 1 = j := by omega)
  proof: by
  subst hij hjk
  exact hS.exact i hk

中文:
引理 正合.exact'
  结论: (hS : S.正合) (i j k : 自然数) (hij : i + 1 = j := by omega)
  证明: by
  subst hij hjk
  exact hS.exact i hk

Depends on / 依赖: S.sc, hS.exact, hS.toIsComplex, toIsComplex
-/
lemma Exact.exact' (hS : S.Exact) (i j k : Nat) (hij : i + 1 = j := by omega)
    (hjk : j + 1 = k := by omega) (hk : k <= n := by omega) :
    (S.sc' hS.toIsComplex i j k).Exact := by
  subst hij hjk
  exact hS.exact i hk

/--
Definition of `Exact.sc'` / `Exact.sc'` 的定义

English:
abbreviation Exact.sc'
  signature: (hS : S.Exact) (i j k : Nat) (hij : i + 1 = j := by lia)
  body: S.sc' hS.toIsComplex i j k

中文:
缩写 正合.sc'
  签名: (hS : S.正合) (i j k : 自然数) (hij : i + 1 = j := by lia)
  定义体: S.sc' hS.toIsComplex i j k

Depends on / 依赖: S.sc, ShortComplex, hS.toIsComplex, toIsComplex
-/
abbrev Exact.sc' (hS : S.Exact) (i j k : Nat) (hij : i + 1 = j := by lia)
    (hjk : j + 1 = k := by lia) (hk : k <= n := by lia) :
    ShortComplex C :=
  S.sc' hS.toIsComplex i j k

/--
Definition of `Exact.sc` / `Exact.sc` 的定义

English:
abbreviation Exact.sc
  signature: (hS : S.Exact) (i : Nat) (hi : i + 2 <= n := by lia)
  body: S.sc' hS.toIsComplex i (i + 1) (i + 2)

中文:
缩写 正合.sc
  签名: (hS : S.正合) (i : 自然数) (hi : i + 2 <= n := by lia)
  定义体: S.sc' hS.toIsComplex i (i + 1) (i + 2)

Depends on / 依赖: S.sc, ShortComplex, hS.toIsComplex, toIsComplex
-/
abbrev Exact.sc (hS : S.Exact) (i : Nat) (hi : i + 2 <= n := by lia) :
    ShortComplex C :=
  S.sc' hS.toIsComplex i (i + 1) (i + 2)

/-- Functoriality maps for `ComposableArrows.sc'`. -/
@[simps]
/--
Definition of `sc'Map` / `sc'Map` 的定义

English:
definition sc'Map
  signature: {S₁ S₂ : ComposableArrows C n} (φ : S₁ ⟶ S₂) (h₁ : S₁.IsComplex) (h₂ : S₂.IsComplex)
  body: φ.app _
  τ₂ := φ.app _
  τ₃ := φ.app _

中文:
定义 sc'Map
  签名: {S₁ S₂ : ComposableArrows C n} (φ : S₁ ⟶ S₂) (h₁ : S₁.是复形) (h₂ : S₂.是复形)
  定义体: φ.app _
  τ₂ := φ.app _
  τ₃ := φ.app _
-/
def sc'Map {S₁ S₂ : ComposableArrows C n} (φ : S₁ ⟶ S₂) (h₁ : S₁.IsComplex) (h₂ : S₂.IsComplex)
    (i j k : Nat) (hij : i + 1 = j := by omega)
    (hjk : j + 1 = k := by omega) (hk : k <= n := by omega) :
    S₁.sc' h₁ i j k ⟶ S₂.sc' h₂ i j k where
  τ₁ := φ.app _
  τ₂ := φ.app _
  τ₃ := φ.app _

/-- Functoriality maps for `ComposableArrows.sc`. -/
@[simps!]
/--
Definition of `scMap` / `scMap` 的定义

English:
definition scMap
  signature: {S₁ S₂ : ComposableArrows C n} (φ : S₁ ⟶ S₂) (h₁ : S₁.IsComplex) (h₂ : S₂.IsComplex)
  body: sc'Map φ h₁ h₂ i (i + 1) (i + 2)

中文:
定义 scMap
  签名: {S₁ S₂ : ComposableArrows C n} (φ : S₁ ⟶ S₂) (h₁ : S₁.是复形) (h₂ : S₂.是复形)
  定义体: sc'Map φ h₁ h₂ i (i + 1) (i + 2)
-/
def scMap {S₁ S₂ : ComposableArrows C n} (φ : S₁ ⟶ S₂) (h₁ : S₁.IsComplex) (h₂ : S₂.IsComplex)
    (i : Nat) (hi : i + 2 <= n := by omega) :
    S₁.sc h₁ i ⟶ S₂.sc h₂ i :=
  sc'Map φ h₁ h₂ i (i + 1) (i + 2)

/-- The isomorphism `S₁.sc' _ i j k ≅ S₂.sc' _ i j k` induced by an isomorphism `S₁ ≅ S₂`
in `ComposableArrows C n`. -/
@[simps]
/--
Definition of `sc'MapIso` / `sc'MapIso` 的定义

English:
definition sc'MapIso
  signature: {S₁ S₂ : ComposableArrows C n} (e : S₁ ≅ S₂)
  body: sc'Map e.hom h₁ h₂ i j k
  inv := sc'Map e.inv h₂ h₁ i j k
  hom_inv_id := by ext <;> simp
  inv_hom_id := by ext <;> simp

中文:
定义 sc'MapIso
  签名: {S₁ S₂ : ComposableArrows C n} (e : S₁ ≅ S₂)
  定义体: sc'Map e.hom h₁ h₂ i j k
  inv := sc'Map e.inv h₂ h₁ i j k
  hom_inv_id := by ext <;> simp
  inv_hom_id := by ext <;> simp
-/
def sc'MapIso {S₁ S₂ : ComposableArrows C n} (e : S₁ ≅ S₂)
    (h₁ : S₁.IsComplex) (h₂ : S₂.IsComplex) (i j k : Nat) (hij : i + 1 = j := by omega)
    (hjk : j + 1 = k := by omega) (hk : k <= n := by omega) :
    S₁.sc' h₁ i j k ≅ S₂.sc' h₂ i j k where
  hom := sc'Map e.hom h₁ h₂ i j k
  inv := sc'Map e.inv h₂ h₁ i j k
  hom_inv_id := by ext <;> simp
  inv_hom_id := by ext <;> simp

/-- The isomorphism `S₁.sc _ i ≅ S₂.sc _ i` induced by an isomorphism `S₁ ≅ S₂`
in `ComposableArrows C n`. -/
@[simps]
/--
Definition of `scMapIso` / `scMapIso` 的定义

English:
definition scMapIso
  signature: {S₁ S₂ : ComposableArrows C n} (e : S₁ ≅ S₂)
  body: scMap e.hom h₁ h₂ i
  inv := scMap e.inv h₂ h₁ i
  hom_inv_id := by ext <;> simp
  inv_hom_id := by ext <;> simp

中文:
定义 scMapIso
  签名: {S₁ S₂ : ComposableArrows C n} (e : S₁ ≅ S₂)
  定义体: scMap e.hom h₁ h₂ i
  inv := scMap e.inv h₂ h₁ i
  hom_inv_id := by ext <;> simp
  inv_hom_id := by ext <;> simp

Depends on / 依赖: e.hom, e.inv, hom_inv_id, inv_hom_id
-/
def scMapIso {S₁ S₂ : ComposableArrows C n} (e : S₁ ≅ S₂)
    (h₁ : S₁.IsComplex) (h₂ : S₂.IsComplex)
    (i : Nat) (hi : i + 2 <= n := by omega) :
    S₁.sc h₁ i ≅ S₂.sc h₂ i where
  hom := scMap e.hom h₁ h₂ i
  inv := scMap e.inv h₂ h₁ i
  hom_inv_id := by ext <;> simp
  inv_hom_id := by ext <;> simp

/--
lemma `exact_of_iso` / 引理 `exact_of_iso`

English:
lemma exact_of_iso
  given: {S₁ S₂ : ComposableArrows C n} (e : S₁ ≅ S₂) (h₁ : S₁.Exact)
  proof: isComplex_of_iso e h₁.toIsComplex
  exact i hi := ShortComplex.exact_of_iso (scMapIso e h₁.toIsComplex
    (isComplex_of_iso e h₁.toIsComplex) i) (h₁.exact i hi)

中文:
引理 exact_of_iso
  条件: {S₁ S₂ : ComposableArrows C n} (e : S₁ ≅ S₂) (h₁ : S₁.正合)
  证明: isComplex_of_iso e h₁.toIsComplex
  exact i hi := ShortComplex.exact_of_iso (scMapIso e h₁.toIsComplex
    (isComplex_of_iso e h₁.toIsComplex) i) (h₁.exact i hi)

Depends on / 依赖: isComplex_of_iso, toIsComplex
-/
lemma exact_of_iso {S₁ S₂ : ComposableArrows C n} (e : S₁ ≅ S₂) (h₁ : S₁.Exact) :
    S₂.Exact where
  toIsComplex := isComplex_of_iso e h₁.toIsComplex
  exact i hi := ShortComplex.exact_of_iso (scMapIso e h₁.toIsComplex
    (isComplex_of_iso e h₁.toIsComplex) i) (h₁.exact i hi)

/--
lemma `exact_iff_of_iso` / 引理 `exact_iff_of_iso`

English:
lemma exact_iff_of_iso
  given: {S₁ S₂ : ComposableArrows C n} (e : S₁ ≅ S₂)
  proof: ⟨exact_of_iso e, exact_of_iso e.symm⟩

中文:
引理 exact_iff_of_iso
  条件: {S₁ S₂ : ComposableArrows C n} (e : S₁ ≅ S₂)
  证明: ⟨exact_of_iso e, exact_of_iso e.symm⟩

Depends on / 依赖: e.symm, exact_of_iso
-/
lemma exact_iff_of_iso {S₁ S₂ : ComposableArrows C n} (e : S₁ ≅ S₂) :
    S₁.Exact ↔ S₂.Exact :=
  ⟨exact_of_iso e, exact_of_iso e.symm⟩

/--
lemma `exact₀` / 引理 `exact₀`

English:
lemma exact₀
  given: (S : ComposableArrows C 0)
  statement: S.Exact where
  proof: S.isComplex₀
  exact i hi := by simp at hi

中文:
引理 exact₀
  条件: (S : ComposableArrows C 0)
  结论: S.正合 where
  证明: S.isComplex₀
  exact i hi := by simp at hi

Depends on / 依赖: S.isComplex
-/
lemma exact₀ (S : ComposableArrows C 0) : S.Exact where
  toIsComplex := S.isComplex₀
  exact i hi := by simp at hi

/--
lemma `exact₁` / 引理 `exact₁`

English:
lemma exact₁
  given: (S : ComposableArrows C 1)
  statement: S.Exact where
  proof: S.isComplex₁
  exact i hi := by exfalso; lia

中文:
引理 exact₁
  条件: (S : ComposableArrows C 1)
  结论: S.正合 where
  证明: S.isComplex₁
  exact i hi := by exfalso; lia

Depends on / 依赖: S.isComplex
-/
lemma exact₁ (S : ComposableArrows C 1) : S.Exact where
  toIsComplex := S.isComplex₁
  exact i hi := by exfalso; lia

/--
lemma `isComplex₂_iff` / 引理 `isComplex₂_iff`

English:
lemma isComplex₂_iff
  given: (S : ComposableArrows C 2)
  proof: by
  constructor
  · intro h
    exact h.zero 0 (by lia)
  · intro h
    refine IsComplex.mk (fun i hi => ?_)
    obtain rfl : i = 0 := by lia
    exact h

中文:
引理 isComplex₂_iff
  条件: (S : ComposableArrows C 2)
  证明: by
  constructor
  · intro h
    exact h.zero 0 (by lia)
  · intro h
    refine IsComplex.mk (fun i hi => ?_)
    obtain rfl : i = 0 := by lia
    exact h

Depends on / 依赖: IsComplex, IsComplex.mk, h.zero
-/
lemma isComplex₂_iff (S : ComposableArrows C 2) :
    S.IsComplex ↔ S.map' 0 1 ≫ S.map' 1 2 = 0 := by
  constructor
  · intro h
    exact h.zero 0 (by lia)
  · intro h
    refine IsComplex.mk (fun i hi => ?_)
    obtain rfl : i = 0 := by lia
    exact h

/--
lemma `isComplex₂_mk` / 引理 `isComplex₂_mk`

English:
lemma isComplex₂_mk
  given: (S : ComposableArrows C 2) (w : S.map' 0 1 ≫ S.map' 1 2 = 0)
  proof: S.isComplex₂_iff.2 w

中文:
引理 isComplex₂_mk
  条件: (S : ComposableArrows C 2) (w : S.map' 0 1 ≫ S.map' 1 2 = 0)
  证明: S.isComplex₂_iff.2 w

Depends on / 依赖: S.isComplex
-/
lemma isComplex₂_mk (S : ComposableArrows C 2) (w : S.map' 0 1 ≫ S.map' 1 2 = 0) :
    S.IsComplex :=
  S.isComplex₂_iff.2 w

set_option backward.isDefEq.respectTransparency false in
/--
lemma `_root_.CategoryTheory.ShortComplex.isComplex_toComposableArrows` / 引理 `_root_.CategoryTheory.ShortComplex.isComplex_toComposableArrows`

English:
lemma _root_.CategoryTheory.ShortComplex.isComplex_toComposableArrows
  given: (S : ShortComplex C)
  proof: -- Disable `Fin.reduceFinMk` because otherwise `Precompose.map_one_succ` does not apply. (https://github.com/leanprover-community/mathlib4/issues/27382)
  isComplex₂_mk _ (by simp [-Fin.reduceFinMk])

中文:
引理 _root_.范畴论.短复形.isComplex_toComposableArrows
  条件: (S : 短复形 C)
  证明: -- Disable `Fin.reduceFinMk` because otherwise `Precompose.map_one_succ` does not apply. (https://github.com/leanprover-community/mathlib4/issues/27382)
  isComplex₂_mk _ (by simp [-Fin.reduceFinMk])
-/
lemma _root_.CategoryTheory.ShortComplex.isComplex_toComposableArrows (S : ShortComplex C) :
    S.toComposableArrows.IsComplex :=
  -- Disable `Fin.reduceFinMk` because otherwise `Precompose.map_one_succ` does not apply. (https://github.com/leanprover-community/mathlib4/issues/27382)
  isComplex₂_mk _ (by simp [-Fin.reduceFinMk])

/--
lemma `exact₂_iff` / 引理 `exact₂_iff`

English:
lemma exact₂_iff
  given: (S : ComposableArrows C 2) (hS : S.IsComplex)
  proof: by
  constructor
  · intro h
    exact h.exact 0 (by lia)
  · intro h
    refine Exact.mk hS (fun i hi => ?_)
    obtain rfl : i = 0 := by lia
    exact h

中文:
引理 exact₂_iff
  条件: (S : ComposableArrows C 2) (hS : S.是复形)
  证明: by
  constructor
  · intro h
    exact h.exact 0 (by lia)
  · intro h
    refine Exact.mk hS (fun i hi => ?_)
    obtain rfl : i = 0 := by lia
    exact h

Depends on / 依赖: Exact.mk, h.exact
-/
lemma exact₂_iff (S : ComposableArrows C 2) (hS : S.IsComplex) :
    S.Exact ↔ (S.sc' hS 0 1 2).Exact := by
  constructor
  · intro h
    exact h.exact 0 (by lia)
  · intro h
    refine Exact.mk hS (fun i hi => ?_)
    obtain rfl : i = 0 := by lia
    exact h

/--
lemma `exact₂_mk` / 引理 `exact₂_mk`

English:
lemma exact₂_mk
  statement: (S : ComposableArrows C 2) (w : S.map' 0 1 ≫ S.map' 1 2 = 0)
  proof: (S.exact₂_iff (S.isComplex₂_mk w)).2 h

中文:
引理 exact₂_mk
  结论: (S : ComposableArrows C 2) (w : S.map' 0 1 ≫ S.map' 1 2 = 0)
  证明: (S.exact₂_iff (S.isComplex₂_mk w)).2 h

Depends on / 依赖: S.exact, S.isComplex
-/
lemma exact₂_mk (S : ComposableArrows C 2) (w : S.map' 0 1 ≫ S.map' 1 2 = 0)
    (h : (ShortComplex.mk _ _ w).Exact) : S.Exact :=
  (S.exact₂_iff (S.isComplex₂_mk w)).2 h

/--
lemma `_root_.CategoryTheory.ShortComplex.Exact.exact_toComposableArrows` / 引理 `_root_.CategoryTheory.ShortComplex.Exact.exact_toComposableArrows`

English:
lemma _root_.CategoryTheory.ShortComplex.Exact.exact_toComposableArrows
  proof: exact₂_mk _ _ hS

中文:
引理 _root_.范畴论.短复形.正合.exact_toComposableArrows
  证明: exact₂_mk _ _ hS
-/
lemma _root_.CategoryTheory.ShortComplex.Exact.exact_toComposableArrows
    {S : ShortComplex C} (hS : S.Exact) :
    S.toComposableArrows.Exact :=
  exact₂_mk _ _ hS

/--
lemma `_root_.CategoryTheory.ShortComplex.exact_iff_exact_toComposableArrows` / 引理 `_root_.CategoryTheory.ShortComplex.exact_iff_exact_toComposableArrows`

English:
lemma _root_.CategoryTheory.ShortComplex.exact_iff_exact_toComposableArrows
  proof: (S.toComposableArrows.exact₂_iff S.isComplex_toComposableArrows).symm

中文:
引理 _root_.范畴论.短复形.exact_iff_exact_toComposableArrows
  证明: (S.toComposableArrows.exact₂_iff S.isComplex_toComposableArrows).symm

Depends on / 依赖: S.isComplex_toComposableArrows, S.toComposableArrows.exact, isComplex_toComposableArrows, toComposableArrows
-/
lemma _root_.CategoryTheory.ShortComplex.exact_iff_exact_toComposableArrows
    (S : ShortComplex C) :
    S.Exact ↔ S.toComposableArrows.Exact :=
  (S.toComposableArrows.exact₂_iff S.isComplex_toComposableArrows).symm

/--
lemma `exact_iff_δ₀` / 引理 `exact_iff_δ₀`

English:
lemma exact_iff_δ₀
  given: (S : ComposableArrows C (n + 2))
  proof: by
  constructor
  · intro h
    constructor
    · rw [exact₂_iff]; swap
      · rw [isComplex₂_iff]
        exact h.toIsComplex.zero 0
      exact h.exact 0 (by lia)
    · exact Exact.mk (IsComplex.mk (fun i hi => h.toIsComplex.zero (i + 1)))
        (fun i hi => h.exact (i + 1))
  · rintro ⟨h, h₀⟩
    refine Exact.mk (IsComplex.mk (fun i hi => ?_)) (fun i hi => ?_)
    · obtain _ | i := i
      · exact h.toIsComplex.zero 0
      · exact h₀.toIsComplex.zero i
    · obtain _ | i := i
      · exact h.exact 0
      · exact h₀.exact i

中文:
引理 exact_iff_δ₀
  条件: (S : ComposableArrows C (n + 2))
  证明: by
  constructor
  · intro h
    constructor
    · rw [exact₂_iff]; swap
      · rw [isComplex₂_iff]
        exact h.toIsComplex.zero 0
      exact h.exact 0 (by lia)
    · exact Exact.mk (IsComplex.mk (fun i hi => h.toIsComplex.zero (i + 1)))
        (fun i hi => h.exact (i + 1))
  · rintro ⟨h, h₀⟩
    refine Exact.mk (IsComplex.mk (fun i hi => ?_)) (fun i hi => ?_)
    · obtain _ | i := i
      · exact h.toIsComplex.zero 0
      · exact h₀.toIsComplex.zero i
    · obtain _ | i := i
      · exact h.exact 0
      · exact h₀.exact i

Depends on / 依赖: Exact.mk, IsComplex, IsComplex.mk, h.exact, h.toIsComplex.zero, toIsComplex, toIsComplex.zero
-/
lemma exact_iff_δ₀ (S : ComposableArrows C (n + 2)) :
    S.Exact ↔ (mk₂ (S.map' 0 1) (S.map' 1 2)).Exact ∧ S.δ₀.Exact := by
  constructor
  · intro h
    constructor
    · rw [exact₂_iff]; swap
      · rw [isComplex₂_iff]
        exact h.toIsComplex.zero 0
      exact h.exact 0 (by lia)
    · exact Exact.mk (IsComplex.mk (fun i hi => h.toIsComplex.zero (i + 1)))
        (fun i hi => h.exact (i + 1))
  · rintro ⟨h, h₀⟩
    refine Exact.mk (IsComplex.mk (fun i hi => ?_)) (fun i hi => ?_)
    · obtain _ | i := i
      · exact h.toIsComplex.zero 0
      · exact h₀.toIsComplex.zero i
    · obtain _ | i := i
      · exact h.exact 0
      · exact h₀.exact i

/--
lemma `Exact.δ₀` / 引理 `Exact.δ₀`

English:
lemma Exact.δ₀
  given: {S : ComposableArrows C (n + 2)} (hS : S.Exact)
  proof: by
  rw [exact_iff_δ₀] at hS
  exact hS.2

中文:
引理 正合.δ₀
  条件: {S : ComposableArrows C (n + 2)} (hS : S.正合)
  证明: by
  rw [exact_iff_δ₀] at hS
  exact hS.2
-/
lemma Exact.δ₀ {S : ComposableArrows C (n + 2)} (hS : S.Exact) :
    S.δ₀.Exact := by
  rw [exact_iff_δ₀] at hS
  exact hS.2

/--
lemma `exact_of_δ₀` / 引理 `exact_of_δ₀`

English:
lemma exact_of_δ₀
  statement: {S : ComposableArrows C (n + 2)}
  proof: by
  rw [exact_iff_δ₀]
  constructor <;> assumption

中文:
引理 exact_of_δ₀
  结论: {S : ComposableArrows C (n + 2)}
  证明: by
  rw [exact_iff_δ₀]
  constructor <;> assumption
-/
lemma exact_of_δ₀ {S : ComposableArrows C (n + 2)}
    (h : (mk₂ (S.map' 0 1) (S.map' 1 2)).Exact) (h₀ : S.δ₀.Exact) : S.Exact := by
  rw [exact_iff_δ₀]
  constructor <;> assumption

/--
lemma `exact_iff_δlast` / 引理 `exact_iff_δlast`

English:
lemma exact_iff_δlast
  given: {n : Nat} (S : ComposableArrows C (n + 2))
  proof: by
  constructor
  · intro h
    constructor
    · exact Exact.mk (IsComplex.mk (fun i hi => h.toIsComplex.zero i))
        (fun i hi => h.exact i)
    · rw [exact₂_iff]; swap
      · rw [isComplex₂_iff]
        exact h.toIsComplex.zero n
      exact h.exact n (by lia)
  · rintro ⟨h, h'⟩
    refine Exact.mk (IsComplex.mk (fun i hi => ?_)) (fun i hi => ?_)
    · simp only [Nat.add_le_add_iff_right] at hi
      obtain hi | rfl := hi.lt_or_eq
      · exact h.toIsComplex.zero i
      · exact h'.toIsComplex.zero 0
    · simp only [Nat.add_le_add_iff_right] at hi
      obtain hi | rfl := hi.lt_or_eq
      · exact h.exact i
      · exact h'.exact 0

中文:
引理 exact_iff_δlast
  条件: {n : 自然数} (S : ComposableArrows C (n + 2))
  证明: by
  constructor
  · intro h
    constructor
    · exact Exact.mk (IsComplex.mk (fun i hi => h.toIsComplex.zero i))
        (fun i hi => h.exact i)
    · rw [exact₂_iff]; swap
      · rw [isComplex₂_iff]
        exact h.toIsComplex.zero n
      exact h.exact n (by lia)
  · rintro ⟨h, h'⟩
    refine Exact.mk (IsComplex.mk (fun i hi => ?_)) (fun i hi => ?_)
    · simp only [Nat.add_le_add_iff_right] at hi
      obtain hi | rfl := hi.lt_or_eq
      · exact h.toIsComplex.zero i
      · exact h'.toIsComplex.zero 0
    · simp only [Nat.add_le_add_iff_right] at hi
      obtain hi | rfl := hi.lt_or_eq
      · exact h.exact i
      · exact h'.exact 0

Depends on / 依赖: Exact.mk, IsComplex, IsComplex.mk, Nat.add_le_add_iff_right, add_le_add_iff_right, h.exact, h.toIsComplex.zero, hi.lt_or_eq, lt_or_eq, toIsComplex, toIsComplex.zero
-/
lemma exact_iff_δlast {n : Nat} (S : ComposableArrows C (n + 2)) :
    S.Exact ↔ S.δlast.Exact ∧ (mk₂ (S.map' n (n + 1)) (S.map' (n + 1) (n + 2))).Exact := by
  constructor
  · intro h
    constructor
    · exact Exact.mk (IsComplex.mk (fun i hi => h.toIsComplex.zero i))
        (fun i hi => h.exact i)
    · rw [exact₂_iff]; swap
      · rw [isComplex₂_iff]
        exact h.toIsComplex.zero n
      exact h.exact n (by lia)
  · rintro ⟨h, h'⟩
    refine Exact.mk (IsComplex.mk (fun i hi => ?_)) (fun i hi => ?_)
    · simp only [Nat.add_le_add_iff_right] at hi
      obtain hi | rfl := hi.lt_or_eq
      · exact h.toIsComplex.zero i
      · exact h'.toIsComplex.zero 0
    · simp only [Nat.add_le_add_iff_right] at hi
      obtain hi | rfl := hi.lt_or_eq
      · exact h.exact i
      · exact h'.exact 0

/--
lemma `Exact.δlast` / 引理 `Exact.δlast`

English:
lemma Exact.δlast
  given: {S : ComposableArrows C (n + 2)} (hS : S.Exact)
  proof: by
  rw [exact_iff_δlast] at hS
  exact hS.1

中文:
引理 正合.δlast
  条件: {S : ComposableArrows C (n + 2)} (hS : S.正合)
  证明: by
  rw [exact_iff_δlast] at hS
  exact hS.1
-/
lemma Exact.δlast {S : ComposableArrows C (n + 2)} (hS : S.Exact) :
    S.δlast.Exact := by
  rw [exact_iff_δlast] at hS
  exact hS.1

/--
lemma `exact_of_δlast` / 引理 `exact_of_δlast`

English:
lemma exact_of_δlast
  statement: {n : Nat} (S : ComposableArrows C (n + 2))
  proof: by
  rw [exact_iff_δlast]
  constructor <;> assumption

中文:
引理 exact_of_δlast
  结论: {n : 自然数} (S : ComposableArrows C (n + 2))
  证明: by
  rw [exact_iff_δlast]
  constructor <;> assumption
-/
lemma exact_of_δlast {n : Nat} (S : ComposableArrows C (n + 2))
    (h₁ : S.δlast.Exact) (h₂ : (mk₂ (S.map' n (n + 1)) (S.map' (n + 1) (n + 2))).Exact) :
    S.Exact := by
  rw [exact_iff_δlast]
  constructor <;> assumption

/--
theorem `natAddLEFunctor_obj_exact` / 定理 `natAddLEFunctor_obj_exact`

English:
theorem natAddLEFunctor_obj_exact
  statement: {n k l : Nat} (h : k + l <= n) {R : ComposableArrows C n}
  proof: ⟨⟨fun i _ => hR.1.1 (k + i)⟩, fun i _ => hR.exact (k + i)⟩

中文:
定理 natAddLEFunctor_obj_exact
  结论: {n k l : 自然数} (h : k + l <= n) {R : ComposableArrows C n}
  证明: ⟨⟨fun i _ => hR.1.1 (k + i)⟩, fun i _ => hR.exact (k + i)⟩

Depends on / 依赖: hR.exact
-/
theorem natAddLEFunctor_obj_exact {n k l : Nat} (h : k + l <= n) {R : ComposableArrows C n}
    (hR : R.Exact) :
    ((natAddLEFunctor h).obj R).Exact :=
  ⟨⟨fun i _ => hR.1.1 (k + i)⟩, fun i _ => hR.exact (k + i)⟩

/--
lemma `Exact.isIso_map'` / 引理 `Exact.isIso_map'`

English:
lemma Exact.isIso_map'
  statement: {C : Type*} [Category* C] [Preadditive C]
  proof: by
  have := (hS.exact k).mono_g h₀
  have := (hS.exact (k + 1)).epi_f h₁
  apply isIso_of_mono_of_epi

中文:
引理 正合.isIso_map'
  结论: {C : 类型} [范畴* C] [预加性 C]
  证明: by
  have := (hS.exact k).mono_g h₀
  have := (hS.exact (k + 1)).epi_f h₁
  apply isIso_of_mono_of_epi

Depends on / 依赖: epi_f, hS.exact, isIso_of_mono_of_epi, mono_g
-/
lemma Exact.isIso_map' {C : Type*} [Category* C] [Preadditive C]
    [Balanced C] {n : Nat} {S : ComposableArrows C n} (hS : S.Exact) (k : Nat) (hk : k + 3 <= n)
    (h₀ : S.map' k (k + 1) = 0) (h₁ : S.map' (k + 2) (k + 3) = 0) :
    IsIso (S.map' (k + 1) (k + 2)) := by
  have := (hS.exact k).mono_g h₀
  have := (hS.exact (k + 1)).epi_f h₁
  apply isIso_of_mono_of_epi

end ComposableArrows

end CategoryTheory
