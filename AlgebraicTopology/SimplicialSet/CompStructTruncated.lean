/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.AlgebraicTopology.SimplexCategory.Truncated

/-!
# Edges and "triangles" in truncated simplicial sets

Given a `2`-truncated simplicial set `X`, we introduce two types:
* Given `0`-simplices `x₀` and `x₁`, we define `Edge x₀ x₁`
  which is the type of `1`-simplices with faces `x₁` and `x₀` respectively;
* Given `0`-simplices `x₀`, `x₁`, `x₂`, edges `e₀₁ : Edge x₀ x₁`, `e₁₂ : Edge x₁ x₂`,
  `e₀₂ : Edge x₀ x₂`, a structure `CompStruct e₀₁ e₁₂ e₀₂` which records the
  data of a `2`-simplex with faces `e₁₂`, `e₀₂` and `e₀₁` respectively. This data
  will allow to obtain relations in the homotopy category of `X`.

-/

@[expose] public section

universe v u

open CategoryTheory Simplicial SimplicialObject.Truncated
  SimplexCategory.Truncated

namespace SSet.Truncated

variable {X Y : Truncated.{u} 2}

/-- In a `2`-truncated simplicial set, an edge from a vertex `x₀` to `x₁` is
a `1`-simplex with prescribed `0`-dimensional faces. -/
@[ext]
/--
Definition of `Edge` / `Edge` 的定义

English:
structure Edge
  parameters: (x₀ x₁ : X _⦋0⦌₂)
  axioms and operations (3):
    - edge : X _⦋1⦌₂
    - src_eq : X.map (δ₂ 1).op edge = x₀  [default: by cat_disch]
    - tgt_eq : X.map (δ₂ 0).op edge = x₁  [default: by cat_disch]

中文:
结构 边
  参数: (x₀ x₁ : X _⦋0⦌₂)
  公理与运算 (3 个):
    - edge : X _⦋1⦌₂
    - src_eq : X.map (δ₂ 1).op edge = x₀  [默认: by cat_disch]
    - tgt_eq : X.map (δ₂ 0).op edge = x₁  [默认: by cat_disch]

Depends on / 依赖: cat_disch
-/
structure Edge (x₀ x₁ : X _⦋0⦌₂) where
  /-- A `1`-simplex -/
  edge : X _⦋1⦌₂
  /-- The source of the edge is `x₀`. -/
  src_eq : X.map (δ₂ 1).op edge = x₀ := by cat_disch
  /-- The target of the edge is `x₁`. -/
  tgt_eq : X.map (δ₂ 0).op edge = x₁ := by cat_disch

namespace Edge

attribute [simp] src_eq tgt_eq

/-- The edge given by a `1`-simplex. -/
@[simps]
/--
Definition of `mk'` / `mk'` 的定义

English:
definition mk'
  signature: (s : X _⦋1⦌₂)
  body: s

中文:
定义 mk'
  签名: (s : X _⦋1⦌₂)
  定义体: s
-/
def mk' (s : X _⦋1⦌₂) : Edge (X.map (δ₂ 1).op s) (X.map (δ₂ 0).op s) where
  edge := s

/--
lemma `exists_of_simplex` / 引理 `exists_of_simplex`

English:
lemma exists_of_simplex
  given: (s : X _⦋1⦌₂)
  proof: ⟨_, _, mk' s, rfl⟩

中文:
引理 存在_of_simplex
  条件: (s : X _⦋1⦌₂)
  证明: ⟨_, _, mk' s, rfl⟩
-/
lemma exists_of_simplex (s : X _⦋1⦌₂) :
    exists (x₀ x₁ : X _⦋0⦌₂) (e : Edge x₀ x₁), e.edge = s :=
  ⟨_, _, mk' s, rfl⟩

/-- The constant edge on a `0`-simplex. -/
@[simps]
/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: (x : X _⦋0⦌₂)
  body: X.map (σ₂ 0).op x
  src_eq := by simp [← Functor.map_comp_apply, ← op_comp]
  tgt_eq := by simp [← Functor.map_comp_apply, ← op_comp]

中文:
定义 id
  签名: (x : X _⦋0⦌₂)
  定义体: X.map (σ₂ 0).op x
  src_eq := by simp [← Functor.map_comp_apply, ← op_comp]
  tgt_eq := by simp [← Functor.map_comp_apply, ← op_comp]

Depends on / 依赖: X.map
-/
def id (x : X _⦋0⦌₂) : Edge x x where
  edge := X.map (σ₂ 0).op x
  src_eq := by simp [← Functor.map_comp_apply, ← op_comp]
  tgt_eq := by simp [← Functor.map_comp_apply, ← op_comp]

/-- The image of an edge by a morphism of truncated simplicial sets. -/
@[simps]
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: {x₀ x₁ : X _⦋0⦌₂} (e : Edge x₀ x₁) (f : X ⟶ Y)
  body: f.app _ e.edge
  src_eq := by simp [← NatTrans.naturality_apply]
  tgt_eq := by simp [← NatTrans.naturality_apply]

@[simp]

中文:
定义 map
  签名: {x₀ x₁ : X _⦋0⦌₂} (e : 边 x₀ x₁) (f : X ⟶ Y)
  定义体: f.app _ e.edge
  src_eq := by simp [← NatTrans.naturality_apply]
  tgt_eq := by simp [← NatTrans.naturality_apply]

@[simp]

Depends on / 依赖: e.edge, f.app
-/
def map {x₀ x₁ : X _⦋0⦌₂} (e : Edge x₀ x₁) (f : X ⟶ Y) :
    Edge (f.app _ x₀) (f.app _ x₁) where
  edge := f.app _ e.edge
  src_eq := by simp [← NatTrans.naturality_apply]
  tgt_eq := by simp [← NatTrans.naturality_apply]

@[simp]
/--
lemma `map_id` / 引理 `map_id`

English:
lemma map_id
  given: (x : X _⦋0⦌₂) (f : X ⟶ Y)
  proof: by
  ext
  simp [NatTrans.naturality_apply]

中文:
引理 map_id
  条件: (x : X _⦋0⦌₂) (f : X ⟶ Y)
  证明: by
  ext
  simp [NatTrans.naturality_apply]

Depends on / 依赖: NatTrans, NatTrans.naturality_apply, naturality_apply
-/
lemma map_id (x : X _⦋0⦌₂) (f : X ⟶ Y) :
    (Edge.id x).map f = Edge.id (f.app _ x) := by
  ext
  simp [NatTrans.naturality_apply]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Subsingleton
  signature: (X _⦋1⦌₂)] {x y
  body: by ext; subsingleton

中文:
实例 [子单例
  签名: (X _⦋1⦌₂)] {x y
  定义体: by ext; subsingleton

Depends on / 依赖: subsingleton
-/
instance [Subsingleton (X _⦋1⦌₂)] {x y : X _⦋0⦌₂} :
    Subsingleton (X.Edge x y) where
  allEq f g := by ext; subsingleton

/-- Let `x₀`, `x₁`, `x₂` be `0`-simplices of a `2`-truncated simplicial set `X`,
`e₀₁` an edge from `x₀` to `x₁`, `e₁₂` an edge from `x₁` to `x₂`,
`e₀₂` an edge from `x₀` to `x₂`. This is the data of a `2`-simplex whose
faces are respectively `e₀₂`, `e₁₂` and `e₀₁`. Such structures shall provide
relations in the homotopy category of arbitrary (truncated) simplicial sets
(and specialized constructions for quasicategories and Kan complexes.). -/
@[ext]
/--
Definition of `CompStruct` / `CompStruct` 的定义

English:
structure CompStruct
  parameters: {x₀ x₁ x₂ : X _⦋0⦌₂}
  axioms and operations (4):
    - simplex : X _⦋2⦌₂
    - d₂ : X.map (δ₂ 2).op simplex = e₀₁.edge  [default: by cat_disch]
    - d₀ : X.map (δ₂ 0).op simplex = e₁₂.edge  [default: by cat_disch]
    - d₁ : X.map (δ₂ 1).op simplex = e₀₂.edge  [default: by cat_disch]

中文:
结构 余mpStruct
  参数: {x₀ x₁ x₂ : X _⦋0⦌₂}
  公理与运算 (4 个):
    - simplex : X _⦋2⦌₂
    - d₂ : X.map (δ₂ 2).op simplex = e₀₁.edge  [默认: by cat_disch]
    - d₀ : X.map (δ₂ 0).op simplex = e₁₂.edge  [默认: by cat_disch]
    - d₁ : X.map (δ₂ 1).op simplex = e₀₂.edge  [默认: by cat_disch]

Depends on / 依赖: X.map, cat_disch, simplex
-/
structure CompStruct {x₀ x₁ x₂ : X _⦋0⦌₂}
    (e₀₁ : Edge x₀ x₁) (e₁₂ : Edge x₁ x₂) (e₀₂ : Edge x₀ x₂) where
  /-- A `2`-simplex with prescribed `1`-dimensional faces -/
  simplex : X _⦋2⦌₂
  d₂ : X.map (δ₂ 2).op simplex = e₀₁.edge := by cat_disch
  d₀ : X.map (δ₂ 0).op simplex = e₁₂.edge := by cat_disch
  d₁ : X.map (δ₂ 1).op simplex = e₀₂.edge := by cat_disch

namespace CompStruct

attribute [simp] d₀ d₁ d₂

/--
lemma `exists_of_simplex` / 引理 `exists_of_simplex`

English:
lemma exists_of_simplex
  given: (s : X _⦋2⦌₂)
  proof: by
  refine ⟨X.map (Hom.tr (SimplexCategory.const _ _ 0)).op s,
    X.map (Hom.tr (SimplexCategory.const _ _ 1)).op s,
    X.map (Hom.tr (SimplexCategory.const _ _ 2)).op s,
    .mk _ ?_ ?_, .mk _ ?_ ?_, .mk _ ?_ ?_, .mk s rfl rfl rfl, rfl⟩
  all_goals
  · rw [← Functor.map_comp_apply, ← op_comp]
  

中文:
引理 存在_of_simplex
  条件: (s : X _⦋2⦌₂)
  证明: by
  refine ⟨X.map (Hom.tr (SimplexCategory.const _ _ 0)).op s,
    X.map (Hom.tr (SimplexCategory.const _ _ 1)).op s,
    X.map (Hom.tr (SimplexCategory.const _ _ 2)).op s,
    .mk _ ?_ ?_, .mk _ ?_ ?_, .mk _ ?_ ?_, .mk s rfl rfl rfl, rfl⟩
  all_goals
  · rw [← Functor.map_comp_apply, ← op_comp]
  

Depends on / 依赖: Functor, Functor.map_comp_apply, Hom.tr, SimplexCategory, SimplexCategory.const, X.map, all_goals, congr_fun, map_comp_apply, op_comp
-/
lemma exists_of_simplex (s : X _⦋2⦌₂) :
    exists (x₀ x₁ x₂ : X _⦋0⦌₂) (e₀₁ : Edge x₀ x₁) (e₁₂ : Edge x₁ x₂)
      (e₀₂ : Edge x₀ x₂) (h : CompStruct e₀₁ e₁₂ e₀₂), h.simplex = s := by
  refine ⟨X.map (Hom.tr (SimplexCategory.const _ _ 0)).op s,
    X.map (Hom.tr (SimplexCategory.const _ _ 1)).op s,
    X.map (Hom.tr (SimplexCategory.const _ _ 2)).op s,
    .mk _ ?_ ?_, .mk _ ?_ ?_, .mk _ ?_ ?_, .mk s rfl rfl rfl, rfl⟩
  all_goals
  · rw [← Functor.map_comp_apply, ← op_comp]
    apply congr_fun; congr
    decide

/--
Definition of `idComp` / `idComp` 的定义

English:
definition idComp
  signature: {x y : X _⦋0⦌₂} (e : Edge x y)
  body: X.map (σ₂ 0).op e.edge
  d₂ := by
    rw [← Functor.map_comp_apply]; rw [← op_comp]; rw [δ₂_two_comp_σ₂_zero]
    simp
  d₀ := by
    rw [← Functor.map_comp_apply]; rw [← op_comp]; rw [δ₂_zero_comp_σ₂_zero]
    simp
  d₁ := by
    rw [← Functor.map_comp_apply]; rw [← op_comp]; rw [δ₂_one_comp_σ₂_zer

中文:
定义 idComp
  签名: {x y : X _⦋0⦌₂} (e : 边 x y)
  定义体: X.map (σ₂ 0).op e.edge
  d₂ := by
    rw [← Functor.map_comp_apply]; rw [← op_comp]; rw [δ₂_two_comp_σ₂_zero]
    simp
  d₀ := by
    rw [← Functor.map_comp_apply]; rw [← op_comp]; rw [δ₂_zero_comp_σ₂_zero]
    simp
  d₁ := by
    rw [← Functor.map_comp_apply]; rw [← op_comp]; rw [δ₂_one_comp_σ₂_zer

Depends on / 依赖: X.map, e.edge
-/
def idComp {x y : X _⦋0⦌₂} (e : Edge x y) :
    CompStruct (.id x) e e where
  simplex := X.map (σ₂ 0).op e.edge
  d₂ := by
    rw [← Functor.map_comp_apply]; rw [← op_comp]; rw [δ₂_two_comp_σ₂_zero]
    simp
  d₀ := by
    rw [← Functor.map_comp_apply]; rw [← op_comp]; rw [δ₂_zero_comp_σ₂_zero]
    simp
  d₁ := by
    rw [← Functor.map_comp_apply]; rw [← op_comp]; rw [δ₂_one_comp_σ₂_zero]
    simp

/--
Definition of `compId` / `compId` 的定义

English:
definition compId
  signature: {x y : X _⦋0⦌₂} (e : Edge x y)
  body: X.map (σ₂ 1).op e.edge
  d₂ := by
    rw [← Functor.map_comp_apply]; rw [← op_comp]; rw [δ₂_two_comp_σ₂_one]
    simp
  d₀ := by
    rw [← Functor.map_comp_apply]; rw [← op_comp]; rw [δ₂_zero_comp_σ₂_one]
    simp
  d₁ := by
    rw [← Functor.map_comp_apply]; rw [← op_comp]; rw [δ₂_one_comp_σ₂_one]


中文:
定义 compId
  签名: {x y : X _⦋0⦌₂} (e : 边 x y)
  定义体: X.map (σ₂ 1).op e.edge
  d₂ := by
    rw [← Functor.map_comp_apply]; rw [← op_comp]; rw [δ₂_two_comp_σ₂_one]
    simp
  d₀ := by
    rw [← Functor.map_comp_apply]; rw [← op_comp]; rw [δ₂_zero_comp_σ₂_one]
    simp
  d₁ := by
    rw [← Functor.map_comp_apply]; rw [← op_comp]; rw [δ₂_one_comp_σ₂_one]


Depends on / 依赖: X.map, e.edge
-/
def compId {x y : X _⦋0⦌₂} (e : Edge x y) :
    CompStruct e (.id y) e where
  simplex := X.map (σ₂ 1).op e.edge
  d₂ := by
    rw [← Functor.map_comp_apply]; rw [← op_comp]; rw [δ₂_two_comp_σ₂_one]
    simp
  d₀ := by
    rw [← Functor.map_comp_apply]; rw [← op_comp]; rw [δ₂_zero_comp_σ₂_one]
    simp
  d₁ := by
    rw [← Functor.map_comp_apply]; rw [← op_comp]; rw [δ₂_one_comp_σ₂_one]
    simp

/-- `Edge.id x` is a composition of `Edge.id x` with `Edge.id x`. -/
@[simps!]
/--
Definition of `idCompId` / `idCompId` 的定义

English:
definition idCompId
  signature: (x : X _⦋0⦌₂)
  body: idComp _

中文:
定义 idCompId
  签名: (x : X _⦋0⦌₂)
  定义体: idComp _

Depends on / 依赖: idComp
-/
def idCompId (x : X _⦋0⦌₂) :
    CompStruct (.id x) (.id x) (.id x) :=
  idComp _

attribute [local simp ←] FunctorToTypes.naturality in
/-- The image of a `Edge.CompStruct` by a morphism of `2`-truncated
simplicial sets. -/
@[simps]
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: {x₀ x₁ x₂ : X _⦋0⦌₂}
  body: f.app _ h.simplex

中文:
定义 map
  签名: {x₀ x₁ x₂ : X _⦋0⦌₂}
  定义体: f.app _ h.simplex

Depends on / 依赖: f.app, h.simplex, simplex
-/
def map {x₀ x₁ x₂ : X _⦋0⦌₂}
    {e₀₁ : Edge x₀ x₁} {e₁₂ : Edge x₁ x₂} {e₀₂ : Edge x₀ x₂}
    (h : CompStruct e₀₁ e₁₂ e₀₂) (f : X ⟶ Y) :
    CompStruct (e₀₁.map f) (e₁₂.map f) (e₀₂.map f) where
  simplex := f.app _ h.simplex

end CompStruct

end Edge

end SSet.Truncated
