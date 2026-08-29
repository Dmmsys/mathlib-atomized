/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Arnoud van der Leer
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.CompStructTruncated

/-!
# Edges, "triangles" and isos in simplicial sets

Given a simplicial set `X`, we introduce two types:
* Given `0`-simplices `x₀` and `x₁`, we define `Edge x₀ x₁`
  which is the type of `1`-simplices with faces `x₁` and `x₀` respectively;
* Given `0`-simplices `x₀`, `x₁`, `x₂`, edges `e₀₁ : Edge x₀ x₁`, `e₁₂ : Edge x₁ x₂`,
  `e₀₂ : Edge x₀ x₂`, a structure `CompStruct e₀₁ e₁₂ e₀₂` which records the
  data of a `2`-simplex with faces `e₁₂`, `e₀₂` and `e₀₁` respectively. This data
  will allow to obtain relations in the homotopy category of `X`.

(This API parallels similar definitions for `2`-truncated simplicial sets.
The definitions in this file are definitionally equal to their `2`-truncated
counterparts.)

Given `0`-simplices `x₀` and `x₁`, and an edge `hom : Edge x₀ x₁`, `InvStruct hom` records the data
of an edge `inv : Edge x₁ x₀` and simplices `homInvId : CompStruct hom inv (id x₀)` and
`invHomId : CompStruct inv hom (id x₁)`, witnessing that `inv` is an inverse to `hom`.

-/

@[expose] public section

universe v u

open CategoryTheory Simplicial

namespace SSet

variable {X Y : SSet.{u}} {x₀ x₁ x₂ : X _⦋0⦌}

variable (x₀ x₁) in
/--
Definition of `Edge` / `Edge` 的定义

English:
definition Edge
  body: ((truncation 2).obj X).Edge x₀ x₁

中文:
定义 Edge
  定义体: ((truncation 2).obj X).Edge x₀ x₁

Depends on / 依赖: truncation
-/
def Edge := ((truncation 2).obj X).Edge x₀ x₁

namespace Edge

/--
Definition of `ofTruncated` / `ofTruncated` 的定义

English:
definition ofTruncated
  signature: (e : ((truncation 2).obj X).Edge x₀ x₁)
  body: e

中文:
定义 ofTruncated
  签名: (e : ((truncation 2).obj X).Edge x₀ x₁)
  定义体: e
-/
def ofTruncated (e : ((truncation 2).obj X).Edge x₀ x₁) :
    Edge x₀ x₁ := e

/--
Definition of `toTruncated` / `toTruncated` 的定义

English:
definition toTruncated
  signature: (e : Edge x₀ x₁)
  body: e

中文:
定义 toTruncated
  签名: (e : Edge x₀ x₁)
  定义体: e
-/
def toTruncated (e : Edge x₀ x₁) :
    ((truncation 2).obj X).Edge x₀ x₁ :=
  e

/--
Definition of `edge` / `edge` 的定义

English:
definition edge
  signature: (e : Edge x₀ x₁)
  body: e.toTruncated.edge

@[simp]

中文:
定义 edge
  签名: (e : Edge x₀ x₁)
  定义体: e.toTruncated.edge

@[simp]

Depends on / 依赖: e.toTruncated.edge, toTruncated
-/
def edge (e : Edge x₀ x₁) : X _⦋1⦌ := e.toTruncated.edge

@[simp]
/--
lemma `ofTruncated_edge` / 引理 `ofTruncated_edge`

English:
lemma ofTruncated_edge
  given: (e : ((truncation 2).obj X).Edge x₀ x₁)
  proof: rfl

@[simp]

中文:
引理 ofTruncated_edge
  条件: (e : ((truncation 2).obj X).Edge x₀ x₁)
  证明: rfl

@[simp]
-/
lemma ofTruncated_edge (e : ((truncation 2).obj X).Edge x₀ x₁) :
    (ofTruncated e).edge = e.edge := rfl

@[simp]
/--
lemma `toTruncated_edge` / 引理 `toTruncated_edge`

English:
lemma toTruncated_edge
  given: (e : Edge x₀ x₁)
  proof: rfl

@[simp]

中文:
引理 toTruncated_edge
  条件: (e : Edge x₀ x₁)
  证明: rfl

@[simp]
-/
lemma toTruncated_edge (e : Edge x₀ x₁) :
    (toTruncated e).edge = e.edge := rfl

@[simp]
/--
lemma `src_eq` / 引理 `src_eq`

English:
lemma src_eq
  given: (e : Edge x₀ x₁)
  statement: X.δ 1 e.edge = x₀
  proof: Truncated.Edge.src_eq e

@[simp]

中文:
引理 src_eq
  条件: (e : Edge x₀ x₁)
  结论: X.δ 1 e.edge = x₀
  证明: Truncated.Edge.src_eq e

@[simp]

Depends on / 依赖: Truncated, Truncated.Edge.src_eq, src_eq
-/
lemma src_eq (e : Edge x₀ x₁) : X.δ 1 e.edge = x₀ := Truncated.Edge.src_eq e

@[simp]
/--
lemma `tgt_eq` / 引理 `tgt_eq`

English:
lemma tgt_eq
  given: (e : Edge x₀ x₁)
  statement: X.δ 0 e.edge = x₁
  proof: Truncated.Edge.tgt_eq e

@[ext]

中文:
引理 tgt_eq
  条件: (e : Edge x₀ x₁)
  结论: X.δ 0 e.edge = x₁
  证明: Truncated.Edge.tgt_eq e

@[ext]

Depends on / 依赖: Truncated, Truncated.Edge.tgt_eq, tgt_eq
-/
lemma tgt_eq (e : Edge x₀ x₁) : X.δ 0 e.edge = x₁ := Truncated.Edge.tgt_eq e

@[ext]
/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  given: {e e' : Edge x₀ x₁} (h : e.edge = e'.edge)
  proof: Truncated.Edge.ext h

中文:
引理 ext
  条件: {e e' : Edge x₀ x₁} (h : e.edge = e'.edge)
  证明: Truncated.Edge.ext h

Depends on / 依赖: Truncated, Truncated.Edge.ext
-/
lemma ext {e e' : Edge x₀ x₁} (h : e.edge = e'.edge) :
    e = e' := Truncated.Edge.ext h

section

variable (edge : X _⦋1⦌) (src_eq : X.δ 1 edge = x₀ := by cat_disch)
  (tgt_eq : X.δ 0 edge = x₁ := by cat_disch)

set_option backward.privateInPublic true in
/--
Definition of `mk` / `mk` 的定义

English:
definition mk
  signature: : Edge x₀ x₁
  body: ofTruncated { edge := edge }

中文:
定义 mk
  签名: : Edge x₀ x₁
  定义体: ofTruncated { edge := edge }

Depends on / 依赖: ofTruncated
-/
def mk : Edge x₀ x₁ := ofTruncated { edge := edge }

set_option backward.privateInPublic true in
@[simp]
/--
lemma `mk_edge` / 引理 `mk_edge`

English:
lemma mk_edge
  statement: (mk edge src_eq tgt_eq).edge = edge
  proof: rfl

中文:
引理 mk_edge
  结论: (mk edge src_eq tgt_eq).edge = edge
  证明: rfl
-/
lemma mk_edge : (mk edge src_eq tgt_eq).edge = edge := rfl

end

variable (x₀) in
/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: : Edge x₀ x₀
  body: ofTruncated (.id _)

中文:
定义 id
  签名: : Edge x₀ x₀
  定义体: ofTruncated (.id _)

Depends on / 依赖: ofTruncated
-/
def id : Edge x₀ x₀ := ofTruncated (.id _)

variable (x₀) in
@[simp]
/--
lemma `toTruncated_id` / 引理 `toTruncated_id`

English:
lemma toTruncated_id
  proof: rfl

中文:
引理 toTruncated_id
  证明: rfl

Depends on / 依赖: truncation
-/
lemma toTruncated_id :
    toTruncated (id x₀) = Truncated.Edge.id (X := (truncation 2).obj X) x₀ := rfl

variable (x₀) in
@[simp]
/--
lemma `id_edge` / 引理 `id_edge`

English:
lemma id_edge
  statement: (id x₀).edge = X.σ 0 x₀
  proof: rfl

中文:
引理 id_edge
  结论: (id x₀).edge = X.σ 0 x₀
  证明: rfl
-/
lemma id_edge : (id x₀).edge = X.σ 0 x₀ := rfl

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (e : Edge x₀ x₁) (f : X ⟶ Y)
  body: ofTruncated (e.toTruncated.map ((truncation 2).map f))

@[simp]

中文:
定义 map
  签名: (e : Edge x₀ x₁) (f : X ⟶ Y)
  定义体: ofTruncated (e.toTruncated.map ((truncation 2).map f))

@[simp]

Depends on / 依赖: e.toTruncated.map, ofTruncated, toTruncated, truncation
-/
def map (e : Edge x₀ x₁) (f : X ⟶ Y) : Edge (f.app _ x₀) (f.app _ x₁) :=
  ofTruncated (e.toTruncated.map ((truncation 2).map f))

@[simp]
/--
lemma `map_edge` / 引理 `map_edge`

English:
lemma map_edge
  given: (e : Edge x₀ x₁) (f : X ⟶ Y)
  proof: rfl

中文:
引理 map_edge
  条件: (e : Edge x₀ x₁) (f : X ⟶ Y)
  证明: rfl
-/
lemma map_edge (e : Edge x₀ x₁) (f : X ⟶ Y) :
    (e.map f).edge = f.app _ e.edge := rfl

variable (x₀) in
@[simp]
/--
lemma `map_id` / 引理 `map_id`

English:
lemma map_id
  given: (f : X ⟶ Y)
  proof: Truncated.Edge.map_id _ _

中文:
引理 map_id
  条件: (f : X ⟶ Y)
  证明: Truncated.Edge.map_id _ _

Depends on / 依赖: Truncated, Truncated.Edge.map_id, map_id
-/
lemma map_id (f : X ⟶ Y) :
    (Edge.id x₀).map f = Edge.id (f.app _ x₀) :=
  Truncated.Edge.map_id _ _

/--
Definition of `mk'` / `mk'` 的定义

English:
definition mk'
  signature: (s : X _⦋1⦌)
  body: mk s

@[simp]

中文:
定义 mk'
  签名: (s : X _⦋1⦌)
  定义体: mk s

@[simp]
-/
def mk' (s : X _⦋1⦌) : Edge (X.δ 1 s) (X.δ 0 s) := mk s

@[simp]
/--
lemma `mk'_edge` / 引理 `mk'_edge`

English:
lemma mk'_edge
  given: (s : X _⦋1⦌)
  statement: (mk' s).edge = s
  proof: rfl

中文:
引理 mk'_edge
  条件: (s : X _⦋1⦌)
  结论: (mk' s).edge = s
  证明: rfl
-/
lemma mk'_edge (s : X _⦋1⦌) : (mk' s).edge = s := rfl

/--
lemma `exists_of_simplex` / 引理 `exists_of_simplex`

English:
lemma exists_of_simplex
  given: (s : X _⦋1⦌)
  proof: ⟨_, _, mk' s, rfl⟩

中文:
引理 exists_of_simplex
  条件: (s : X _⦋1⦌)
  证明: ⟨_, _, mk' s, rfl⟩
-/
lemma exists_of_simplex (s : X _⦋1⦌) :
    exists (x₀ x₁ : X _⦋0⦌) (e : Edge x₀ x₁), e.edge = s :=
  ⟨_, _, mk' s, rfl⟩

/-- Transports an edge between `x₀` and `x₁` to an edge between `y₀` and `y₁`, given `x₀ = y₀`
and `x₁ = y₁`. -/
@[simps]
/--
Definition of `ofEq` / `ofEq` 的定义

English:
definition ofEq
  signature: {y₀ y₁ : X _⦋0⦌} (e : Edge x₀ x₁) (h₀ : x₀ = y₀) (h₁ : x₁ = y₁)
  body: e.edge
  src_eq := e.src_eq.trans h₀
  tgt_eq := e.tgt_eq.trans h₁

中文:
定义 ofEq
  签名: {y₀ y₁ : X _⦋0⦌} (e : Edge x₀ x₁) (h₀ : x₀ = y₀) (h₁ : x₁ = y₁)
  定义体: e.edge
  src_eq := e.src_eq.trans h₀
  tgt_eq := e.tgt_eq.trans h₁

Depends on / 依赖: e.edge
-/
def ofEq {y₀ y₁ : X _⦋0⦌} (e : Edge x₀ x₁) (h₀ : x₀ = y₀) (h₁ : x₁ = y₁) :
    Edge y₀ y₁ where
  edge := e.edge
  src_eq := e.src_eq.trans h₀
  tgt_eq := e.tgt_eq.trans h₁

/--
Definition of `CompStruct` / `CompStruct` 的定义

English:
definition CompStruct
  signature: (e₀₁ : Edge x₀ x₁) (e₁₂ : Edge x₁ x₂) (e₀₂ : Edge x₀ x₂)
  body: Truncated.Edge.CompStruct e₀₁.toTruncated e₁₂.toTruncated e₀₂.toTruncated

中文:
定义 CompStruct
  签名: (e₀₁ : Edge x₀ x₁) (e₁₂ : Edge x₁ x₂) (e₀₂ : Edge x₀ x₂)
  定义体: Truncated.Edge.CompStruct e₀₁.toTruncated e₁₂.toTruncated e₀₂.toTruncated

Depends on / 依赖: CompStruct, Truncated, Truncated.Edge.CompStruct, toTruncated
-/
def CompStruct (e₀₁ : Edge x₀ x₁) (e₁₂ : Edge x₁ x₂) (e₀₂ : Edge x₀ x₂) :=
  Truncated.Edge.CompStruct e₀₁.toTruncated e₁₂.toTruncated e₀₂.toTruncated

namespace CompStruct

variable {e₀₁ : Edge x₀ x₁} {e₁₂ : Edge x₁ x₂} {e₀₂ : Edge x₀ x₂}

/--
Definition of `ofTruncated` / `ofTruncated` 的定义

English:
definition ofTruncated
  signature: (h : Truncated.Edge.CompStruct e₀₁.toTruncated e₁₂.toTruncated e₀₂.toTruncated)
  body: h

中文:
定义 ofTruncated
  签名: (h : Truncated.Edge.CompStruct e₀₁.toTruncated e₁₂.toTruncated e₀₂.toTruncated)
  定义体: h
-/
def ofTruncated (h : Truncated.Edge.CompStruct e₀₁.toTruncated e₁₂.toTruncated e₀₂.toTruncated) :
    CompStruct e₀₁ e₁₂ e₀₂ := h

/--
Definition of `toTruncated` / `toTruncated` 的定义

English:
definition toTruncated
  signature: (h : CompStruct e₀₁ e₁₂ e₀₂)
  body: h

中文:
定义 toTruncated
  签名: (h : CompStruct e₀₁ e₁₂ e₀₂)
  定义体: h
-/
def toTruncated (h : CompStruct e₀₁ e₁₂ e₀₂) :
    Truncated.Edge.CompStruct e₀₁.toTruncated e₁₂.toTruncated e₀₂.toTruncated :=
  h

section

variable (h : CompStruct e₀₁ e₁₂ e₀₂)

/--
Definition of `simplex` / `simplex` 的定义

English:
definition simplex
  signature: : X _⦋2⦌
  body: h.toTruncated.simplex

@[simp]

中文:
定义 simplex
  签名: : X _⦋2⦌
  定义体: h.toTruncated.simplex

@[simp]

Depends on / 依赖: h.toTruncated.simplex, simplex, toTruncated
-/
def simplex : X _⦋2⦌ := h.toTruncated.simplex

@[simp]
/--
lemma `d₂` / 引理 `d₂`

English:
lemma d₂
  statement: X.δ 2 h.simplex = e₀₁.edge
  proof: Truncated.Edge.CompStruct.d₂ h

@[simp]

中文:
引理 d₂
  结论: X.δ 2 h.simplex = e₀₁.edge
  证明: Truncated.Edge.CompStruct.d₂ h

@[simp]

Depends on / 依赖: CompStruct, Truncated, Truncated.Edge.CompStruct.d
-/
lemma d₂ : X.δ 2 h.simplex = e₀₁.edge := Truncated.Edge.CompStruct.d₂ h

@[simp]
/--
lemma `d₀` / 引理 `d₀`

English:
lemma d₀
  statement: X.δ 0 h.simplex = e₁₂.edge
  proof: Truncated.Edge.CompStruct.d₀ h

@[simp]

中文:
引理 d₀
  结论: X.δ 0 h.simplex = e₁₂.edge
  证明: Truncated.Edge.CompStruct.d₀ h

@[simp]

Depends on / 依赖: CompStruct, Truncated, Truncated.Edge.CompStruct.d
-/
lemma d₀ : X.δ 0 h.simplex = e₁₂.edge := Truncated.Edge.CompStruct.d₀ h

@[simp]
/--
lemma `d₁` / 引理 `d₁`

English:
lemma d₁
  statement: X.δ 1 h.simplex = e₀₂.edge
  proof: Truncated.Edge.CompStruct.d₁ h

中文:
引理 d₁
  结论: X.δ 1 h.simplex = e₀₂.edge
  证明: Truncated.Edge.CompStruct.d₁ h

Depends on / 依赖: CompStruct, Truncated, Truncated.Edge.CompStruct.d
-/
lemma d₁ : X.δ 1 h.simplex = e₀₂.edge := Truncated.Edge.CompStruct.d₁ h

end

section

variable (simplex : X _⦋2⦌)
  (d₂ : X.δ 2 simplex = e₀₁.edge := by cat_disch)
  (d₀ : X.δ 0 simplex = e₁₂.edge := by cat_disch)
  (d₁ : X.δ 1 simplex = e₀₂.edge := by cat_disch)

set_option backward.privateInPublic true in
/--
Definition of `mk` / `mk` 的定义

English:
definition mk
  signature: : CompStruct e₀₁ e₁₂ e₀₂ where
  body: simplex

中文:
定义 mk
  签名: : CompStruct e₀₁ e₁₂ e₀₂ where
  定义体: simplex

Depends on / 依赖: simplex
-/
def mk : CompStruct e₀₁ e₁₂ e₀₂ where
  simplex := simplex

set_option backward.privateInPublic true in
@[simp]
/--
lemma `mk_simplex` / 引理 `mk_simplex`

English:
lemma mk_simplex
  statement: (mk simplex).simplex = simplex
  proof: rfl

中文:
引理 mk_simplex
  结论: (mk simplex).simplex = simplex
  证明: rfl
-/
lemma mk_simplex : (mk simplex).simplex = simplex := rfl

end

@[ext]
/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  given: {h h' : CompStruct e₀₁ e₁₂ e₀₂} (eq : h.simplex = h'.simplex)
  proof: Truncated.Edge.CompStruct.ext eq

中文:
引理 ext
  条件: {h h' : CompStruct e₀₁ e₁₂ e₀₂} (eq : h.simplex = h'.simplex)
  证明: Truncated.Edge.CompStruct.ext eq

Depends on / 依赖: CompStruct, Truncated, Truncated.Edge.CompStruct.ext
-/
lemma ext {h h' : CompStruct e₀₁ e₁₂ e₀₂} (eq : h.simplex = h'.simplex) :
    h = h' :=
  Truncated.Edge.CompStruct.ext eq

/--
lemma `exists_of_simplex` / 引理 `exists_of_simplex`

English:
lemma exists_of_simplex
  given: (s : X _⦋2⦌)
  proof: Truncated.Edge.CompStruct.exists_of_simplex (X := (truncation 2).obj X) s

中文:
引理 exists_of_simplex
  条件: (s : X _⦋2⦌)
  证明: Truncated.Edge.CompStruct.exists_of_simplex (X := (truncation 2).obj X) s

Depends on / 依赖: CompStruct, Truncated, Truncated.Edge.CompStruct.exists_of_simplex, exists_of_simplex, truncation
-/
lemma exists_of_simplex (s : X _⦋2⦌) :
    exists (x₀ x₁ x₂ : X _⦋0⦌) (e₀₁ : Edge x₀ x₁) (e₁₂ : Edge x₁ x₂)
      (e₀₂ : Edge x₀ x₂) (h : CompStruct e₀₁ e₁₂ e₀₂), h.simplex = s :=
  Truncated.Edge.CompStruct.exists_of_simplex (X := (truncation 2).obj X) s

/--
Definition of `idComp` / `idComp` 的定义

English:
definition idComp
  signature: (e : Edge x₀ x₁)
  body: ofTruncated (.idComp _)

@[simp]

中文:
定义 idComp
  签名: (e : Edge x₀ x₁)
  定义体: ofTruncated (.idComp _)

@[simp]

Depends on / 依赖: idComp, ofTruncated
-/
def idComp (e : Edge x₀ x₁) : CompStruct (.id x₀) e e :=
  ofTruncated (.idComp _)

@[simp]
/--
lemma `idComp_simplex` / 引理 `idComp_simplex`

English:
lemma idComp_simplex
  given: (e : Edge x₀ x₁)
  statement: (idComp e).simplex = X.σ 0 e.edge
  proof: rfl

中文:
引理 idComp_simplex
  条件: (e : Edge x₀ x₁)
  结论: (idComp e).simplex = X.σ 0 e.edge
  证明: rfl
-/
lemma idComp_simplex (e : Edge x₀ x₁) : (idComp e).simplex = X.σ 0 e.edge := rfl

/--
Definition of `compId` / `compId` 的定义

English:
definition compId
  signature: (e : Edge x₀ x₁)
  body: ofTruncated (.compId _)

@[simp]

中文:
定义 compId
  签名: (e : Edge x₀ x₁)
  定义体: ofTruncated (.compId _)

@[simp]

Depends on / 依赖: compId, ofTruncated
-/
def compId (e : Edge x₀ x₁) : CompStruct e (.id x₁) e :=
  ofTruncated (.compId _)

@[simp]
/--
lemma `compId_simplex` / 引理 `compId_simplex`

English:
lemma compId_simplex
  given: (e : Edge x₀ x₁)
  statement: (compId e).simplex = X.σ 1 e.edge
  proof: rfl

中文:
引理 compId_simplex
  条件: (e : Edge x₀ x₁)
  结论: (compId e).simplex = X.σ 1 e.edge
  证明: rfl
-/
lemma compId_simplex (e : Edge x₀ x₁) : (compId e).simplex = X.σ 1 e.edge := rfl

/--
Definition of `idCompId` / `idCompId` 的定义

English:
definition idCompId
  signature: (x : X _⦋0⦌)
  body: ofTruncated (.idCompId _)

@[simp]

中文:
定义 idCompId
  签名: (x : X _⦋0⦌)
  定义体: ofTruncated (.idCompId _)

@[simp]

Depends on / 依赖: idCompId, ofTruncated
-/
def idCompId (x : X _⦋0⦌) : CompStruct (id x) (id x) (id x) :=
  ofTruncated (.idCompId _)

@[simp]
/--
lemma `idCompId_simplex` / 引理 `idCompId_simplex`

English:
lemma idCompId_simplex
  given: (x : X _⦋0⦌)
  statement: (idCompId x).simplex = X.σ 0 (X.σ 0 x)
  proof: Truncated.Edge.CompStruct.idCompId_simplex _

中文:
引理 idCompId_simplex
  条件: (x : X _⦋0⦌)
  结论: (idCompId x).simplex = X.σ 0 (X.σ 0 x)
  证明: Truncated.Edge.CompStruct.idCompId_simplex _

Depends on / 依赖: CompStruct, Truncated, Truncated.Edge.CompStruct.idCompId_simplex, idCompId_simplex
-/
lemma idCompId_simplex (x : X _⦋0⦌) : (idCompId x).simplex = X.σ 0 (X.σ 0 x) :=
  Truncated.Edge.CompStruct.idCompId_simplex _

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (h : CompStruct e₀₁ e₁₂ e₀₂) (f : X ⟶ Y)
  body: .ofTruncated (h.toTruncated.map ((truncation 2).map f))

@[simp]

中文:
定义 map
  签名: (h : CompStruct e₀₁ e₁₂ e₀₂) (f : X ⟶ Y)
  定义体: .ofTruncated (h.toTruncated.map ((truncation 2).map f))

@[simp]

Depends on / 依赖: h.toTruncated.map, ofTruncated, toTruncated, truncation
-/
def map (h : CompStruct e₀₁ e₁₂ e₀₂) (f : X ⟶ Y) :
    CompStruct (e₀₁.map f) (e₁₂.map f) (e₀₂.map f) :=
  .ofTruncated (h.toTruncated.map ((truncation 2).map f))

@[simp]
/--
lemma `map_simplex` / 引理 `map_simplex`

English:
lemma map_simplex
  given: (h : CompStruct e₀₁ e₁₂ e₀₂) (f : X ⟶ Y)
  proof: rfl

中文:
引理 map_simplex
  条件: (h : CompStruct e₀₁ e₁₂ e₀₂) (f : X ⟶ Y)
  证明: rfl
-/
lemma map_simplex (h : CompStruct e₀₁ e₁₂ e₀₂) (f : X ⟶ Y) :
    (h.map f).simplex = f.app _ h.simplex := rfl

/-- Transports a `CompStruct` between edges `e₀₁`, `e₁₂` and `e₀₂` to a `CompStruct` between edges
`f₀₁`, `f₁₂` and `f₀₂` along equalities of 1-simplices `eᵢⱼ.edge = fᵢⱼ.edge`. -/
@[simps]
/--
Definition of `ofEq` / `ofEq` 的定义

English:
definition ofEq
  signature: {y₀ y₁ y₂ : X _⦋0⦌}
  body: c.simplex
  d₂ := c.d₂.trans h₀₁
  d₀ := c.d₀.trans h₁₂
  d₁ := c.d₁.trans h₀₂

中文:
定义 ofEq
  签名: {y₀ y₁ y₂ : X _⦋0⦌}
  定义体: c.simplex
  d₂ := c.d₂.trans h₀₁
  d₀ := c.d₀.trans h₁₂
  d₁ := c.d₁.trans h₀₂

Depends on / 依赖: c.simplex, simplex
-/
def ofEq {y₀ y₁ y₂ : X _⦋0⦌}
    {e₀₁ : Edge x₀ x₁} {f₀₁ : Edge y₀ y₁}
    {e₁₂ : Edge x₁ x₂} {f₁₂ : Edge y₁ y₂}
    {e₀₂ : Edge x₀ x₂} {f₀₂ : Edge y₀ y₂}
    (c : CompStruct e₀₁ e₁₂ e₀₂)
    (h₀₁ : e₀₁.edge = f₀₁.edge)
    (h₁₂ : e₁₂.edge = f₁₂.edge)
    (h₀₂ : e₀₂.edge = f₀₂.edge) :
    CompStruct f₀₁ f₁₂ f₀₂ where
  simplex := c.simplex
  d₂ := c.d₂.trans h₀₁
  d₀ := c.d₀.trans h₁₂
  d₁ := c.d₁.trans h₀₂

end CompStruct

/-- For an edge `hom`, `InvStruct hom` encodes the data of a backward edge `inv`, and
2-simplices witnessing that `hom` and `inv` compose to the identity on their endpoints.
This implies that `hom` becomes an isomorphism in the homotopy category. -/
@[ext]
/--
Definition of `InvStruct` / `InvStruct` 的定义

English:
structure InvStruct
  parameters: (hom : Edge x₀ x₁)
  axioms and operations (3):
    - inv : Edge x₁ x₀
    - homInvId : CompStruct hom inv (id x₀)
    - invHomId : CompStruct inv hom (id x₁)

中文:
结构 InvStruct
  参数: (hom : Edge x₀ x₁)
  公理与运算 (3 个):
    - inv : Edge x₁ x₀
    - homInvId : CompStruct hom inv (id x₀)
    - invHomId : CompStruct inv hom (id x₁)
-/
structure InvStruct (hom : Edge x₀ x₁) where
  /-- The backwards edge -/
  inv : Edge x₁ x₀
  /-- The simplex witnessing that `hom` and `inv` compose to the identity -/
  homInvId : CompStruct hom inv (id x₀)
  /-- The simplex witnessing that `inv` and `hom` compose to the identity -/
  invHomId : CompStruct inv hom (id x₁)

namespace InvStruct

/-- The identity edge has an inverse. -/
@[simps]
/--
Definition of `invStructId` / `invStructId` 的定义

English:
definition invStructId
  signature: (x : X _⦋0⦌)
  body: id x
  homInvId := CompStruct.idCompId x
  invHomId := CompStruct.idCompId x

中文:
定义 invStructId
  签名: (x : X _⦋0⦌)
  定义体: id x
  homInvId := CompStruct.idCompId x
  invHomId := CompStruct.idCompId x
-/
def invStructId (x : X _⦋0⦌) : InvStruct (id x) where
  inv := id x
  homInvId := CompStruct.idCompId x
  invHomId := CompStruct.idCompId x

/-- The inverse has an inverse. -/
@[simps]
/--
Definition of `invStructInv` / `invStructInv` 的定义

English:
definition invStructInv
  signature: {hom : Edge x₀ x₁} (I : InvStruct hom)
  body: hom
  homInvId := I.invHomId
  invHomId := I.homInvId

中文:
定义 invStructInv
  签名: {hom : Edge x₀ x₁} (I : InvStruct hom)
  定义体: hom
  homInvId := I.invHomId
  invHomId := I.homInvId
-/
def invStructInv {hom : Edge x₀ x₁} (I : InvStruct hom) : InvStruct I.inv where
  inv := hom
  homInvId := I.invHomId
  invHomId := I.homInvId

/-- Maps an inverse along an morphism of simplicial sets. -/
@[simps]
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: {hom : Edge x₀ x₁} (I : InvStruct hom) (f : X ⟶ Y)
  body: I.inv.map f
  homInvId := (I.homInvId.map f).ofEq rfl rfl (Edge.ext_iff.mp (map_id _ _))
  invHomId := (I.invHomId.map f).ofEq rfl rfl (Edge.ext_iff.mp (map_id _ _))

中文:
定义 map
  签名: {hom : Edge x₀ x₁} (I : InvStruct hom) (f : X ⟶ Y)
  定义体: I.inv.map f
  homInvId := (I.homInvId.map f).ofEq rfl rfl (Edge.ext_iff.mp (map_id _ _))
  invHomId := (I.invHomId.map f).ofEq rfl rfl (Edge.ext_iff.mp (map_id _ _))

Depends on / 依赖: I.inv.map
-/
def map {hom : Edge x₀ x₁} (I : InvStruct hom) (f : X ⟶ Y) : InvStruct (hom.map f) where
  inv := I.inv.map f
  homInvId := (I.homInvId.map f).ofEq rfl rfl (Edge.ext_iff.mp (map_id _ _))
  invHomId := (I.invHomId.map f).ofEq rfl rfl (Edge.ext_iff.mp (map_id _ _))

/-- Transports an inverse for `hom` along an equality of 1-simplices `hom = hom'`.
  I.e. constructs an inverse for `hom'` from an inverse for `hom`. -/
@[simps]
/--
Definition of `ofEq` / `ofEq` 的定义

English:
definition ofEq
  signature: {y₀ y₁ : X _⦋0⦌} {hom : Edge x₀ x₁} {hom' : Edge y₀ y₁}
  body: I.inv.ofEq
    (by rw [← hom.tgt_eq, hhom, hom'.tgt_eq])
    (by rw [← hom.src_eq, hhom, hom'.src_eq])
  homInvId := I.homInvId.ofEq hhom rfl (by rw [← hom.src_eq, hhom, hom'.src_eq])
  invHomId := I.invHomId.ofEq rfl hhom (by rw [← hom.tgt_eq, hhom, hom'.tgt_eq])

中文:
定义 ofEq
  签名: {y₀ y₁ : X _⦋0⦌} {hom : Edge x₀ x₁} {hom' : Edge y₀ y₁}
  定义体: I.inv.ofEq
    (by rw [← hom.tgt_eq, hhom, hom'.tgt_eq])
    (by rw [← hom.src_eq, hhom, hom'.src_eq])
  homInvId := I.homInvId.ofEq hhom rfl (by rw [← hom.src_eq, hhom, hom'.src_eq])
  invHomId := I.invHomId.ofEq rfl hhom (by rw [← hom.tgt_eq, hhom, hom'.tgt_eq])

Depends on / 依赖: I.inv.ofEq
-/
def ofEq {y₀ y₁ : X _⦋0⦌} {hom : Edge x₀ x₁} {hom' : Edge y₀ y₁}
    (I : InvStruct hom)
    (hhom : hom.edge = hom'.edge) :
    InvStruct hom' where
  inv := I.inv.ofEq
    (by rw [← hom.tgt_eq, hhom, hom'.tgt_eq])
    (by rw [← hom.src_eq, hhom, hom'.src_eq])
  homInvId := I.homInvId.ofEq hhom rfl (by rw [← hom.src_eq, hhom, hom'.src_eq])
  invHomId := I.invHomId.ofEq rfl hhom (by rw [← hom.tgt_eq, hhom, hom'.tgt_eq])

end InvStruct

end Edge

end SSet
