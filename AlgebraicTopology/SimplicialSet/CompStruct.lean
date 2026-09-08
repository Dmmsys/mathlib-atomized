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
/-- In a simplicial set, an edge from a vertex `x₀` to `x₁` is
a `1`-simplex with prescribed `0`-dimensional faces. -/
/-
**SSet.Edge** 是 Mathlib 中的一个定义，位于命名空间 `SSet`。
形式化陈述：Edge
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In a simplicial set, an edge from a vertex `x₀` to `x₁` is
a `1`-simplex with prescribed `0`-dimensional faces.
-/
def Edge := ((truncation 2).obj X).Edge x₀ x₁

namespace Edge

/-- Constructor for `SSet.Edge` which takes as an input a term in the definitionally
equal type `SSet.Truncated.Edge` for the `2`-truncation of the simplicial set.
(This definition is made to contain abuse of defeq in other definitions.) -/
/-
**SSet.Edge.ofTruncated** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Edge`。
形式化陈述：ofTruncated (e : ((truncation 2).obj X).Edge x₀ x₁) : Edge x₀ x₁
参数：e : ((truncation 2).obj X).Edge x₀ x₁。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for `SSet.Edge` which takes as an input a term in the definitionally
equal type `SSet.Truncated.Edge` for the `2`-truncation of the simplicial set.
(This definition is made to contain abuse of defeq in other definitions.)
-/
def ofTruncated (e : ((truncation 2).obj X).Edge x₀ x₁) :
    Edge x₀ x₁ := e

/-- The edge of the `2`-truncation of a simplicial set `X` that is induced
by an edge of `X`. -/
/-
**SSet.Edge.toTruncated** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Edge`。
形式化陈述：toTruncated (e : Edge x₀ x₁) : ((truncation 2).obj X).Edge x₀ x₁
参数：e : Edge x₀ x₁。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The edge of the `2`-truncation of a simplicial set `X` that is induced
by an edge of `X`.
-/
def toTruncated (e : Edge x₀ x₁) :
    ((truncation 2).obj X).Edge x₀ x₁ :=
  e

/-- In a simplicial set, an edge from a vertex `x₀` to `x₁` is
a `1`-simplex with prescribed `0`-dimensional faces. -/
/-
**SSet.Edge.edge** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Edge`。
形式化陈述：edge (e : Edge x₀ x₁) : X _⦋1⦌
参数：e : Edge x₀ x₁。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In a simplicial set, an edge from a vertex `x₀` to `x₁` is
a `1`-simplex with prescribed `0`-dimensional faces.
-/
def edge (e : Edge x₀ x₁) : X _⦋1⦌ := e.toTruncated.edge

@[simp]
/-
**SSet.Edge.ofTruncated_edge** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Edge`。
形式化陈述：ofTruncated_edge (e : ((truncation 2).obj X).Edge x₀ x₁) : (ofTruncated e)
.edge = e.edge
参数：e : ((truncation 2).obj X).Edge x₀ x₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofTruncated_edge (e : ((truncation 2).obj X).Edge x₀ x₁) :
    (ofTruncated e).edge = e.edge := rfl

@[simp]
/-
**SSet.Edge.toTruncated_edge** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Edge`。
形式化陈述：toTruncated_edge (e : Edge x₀ x₁) : (toTruncated e).edge = e.edge
参数：e : Edge x₀ x₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toTruncated_edge (e : Edge x₀ x₁) :
    (toTruncated e).edge = e.edge := rfl

@[simp]
/-
**SSet.Edge.src_eq** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Edge`。
形式化陈述：src_eq (e : Edge x₀ x₁) : X.δ 1 e.edge = x₀
参数：e : Edge x₀ x₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SSet.Truncated.Edge.src_eq`：∀ {X : SSet.Truncated 2} {x₀ x₁ : X.obj (Opp
osite.op { obj := { len := 0 }, property := SSet.Truncated.Edge._proof_1 })}   (
self : SSet.Trun…
-/
lemma src_eq (e : Edge x₀ x₁) : X.δ 1 e.edge = x₀ := Truncated.Edge.src_eq e

@[simp]
/-
**SSet.Edge.tgt_eq** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Edge`。
形式化陈述：tgt_eq (e : Edge x₀ x₁) : X.δ 0 e.edge = x₁
参数：e : Edge x₀ x₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SSet.Truncated.Edge.tgt_eq`：∀ {X : SSet.Truncated 2} {x₀ x₁ : X.obj (Opp
osite.op { obj := { len := 0 }, property := SSet.Truncated.Edge._proof_1 })}   (
self : SSet.Trun…
-/
lemma tgt_eq (e : Edge x₀ x₁) : X.δ 0 e.edge = x₁ := Truncated.Edge.tgt_eq e

@[ext]
/-
**SSet.Edge.ext** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Edge`。
形式化陈述：ext {e e' : Edge x₀ x₁} (h : e.edge = e'.edge) : e = e'
参数：h : e.edge = e'.edge。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SSet.Truncated.Edge.ext`：∀ {X : SSet.Truncated 2} {x₀ x₁ : X.obj (Opposi
te.op { obj := { len := 0 }, property := SSet.Truncated.Edge._proof_1 })}   {x y
 : SSet.Trunc…
-/
lemma ext {e e' : Edge x₀ x₁} (h : e.edge = e'.edge) :
    e = e' := Truncated.Edge.ext h

section

variable (edge : X _⦋1⦌) (src_eq : X.δ 1 edge = x₀ := by cat_disch)
  (tgt_eq : X.δ 0 edge = x₁ := by cat_disch)

set_option backward.privateInPublic true in
/-- Constructor for edges in a simplicial set. -/
/-
**SSet.Edge.mk** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Edge`。
形式化陈述：mk : Edge x₀ x₁
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for edges in a simplicial set.
-/
def mk : Edge x₀ x₁ := ofTruncated { edge := edge }

set_option backward.privateInPublic true in
@[simp]
/-
**SSet.Edge.mk_edge** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Edge`。
形式化陈述：mk_edge : (mk edge src_eq tgt_eq).edge = edge
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
lemma mk_edge : (mk edge src_eq tgt_eq).edge = edge := rfl

end

variable (x₀) in
/-- The constant edge on a `0`-simplex. -/
/-
**SSet.Edge.id** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Edge`。
形式化陈述：id : Edge x₀ x₀
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The constant edge on a `0`-simplex.
-/
def id : Edge x₀ x₀ := ofTruncated (.id _)

variable (x₀) in
@[simp]
/-
**SSet.Edge.toTruncated_id** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Edge`。
形式化陈述：toTruncated_id : toTruncated (id x₀) = Truncated.Edge.id (X
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toTruncated_id :
    toTruncated (id x₀) = Truncated.Edge.id (X := (truncation 2).obj X) x₀ := rfl

variable (x₀) in
@[simp]
/-
**SSet.Edge.id_edge** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Edge`。
形式化陈述：id_edge : (id x₀).edge = X.σ 0 x₀
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma id_edge : (id x₀).edge = X.σ 0 x₀ := rfl

/-- The image of an edge by a morphism of simplicial sets. -/
/-
**SSet.Edge.map** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Edge`。
形式化陈述：map (e : Edge x₀ x₁) (f : X ⟶ Y) : Edge (f.app _ x₀) (f.app _ x₁)
参数：e : Edge x₀ x₁；f : X ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The image of an edge by a morphism of simplicial sets.
-/
def map (e : Edge x₀ x₁) (f : X ⟶ Y) : Edge (f.app _ x₀) (f.app _ x₁) :=
  ofTruncated (e.toTruncated.map ((truncation 2).map f))

@[simp]
/-
**SSet.Edge.map_edge** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Edge`。
形式化陈述：map_edge (e : Edge x₀ x₁) (f : X ⟶ Y) : (e.map f).edge = f.app _ e.edge
参数：e : Edge x₀ x₁；f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map_edge (e : Edge x₀ x₁) (f : X ⟶ Y) :
    (e.map f).edge = f.app _ e.edge := rfl

variable (x₀) in
@[simp]
/-
**SSet.Edge.map_id** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Edge`。
形式化陈述：map_id (f : X ⟶ Y) : (Edge.id x₀).map f = Edge.id (f.app _ x₀)
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SSet.Truncated.Edge.map_id`：map_id (x : X _⦋0⦌₂) (f : X ⟶ Y) : (Edge.id 
x).map f = Edge.id (f.app _ x)
-/
lemma map_id (f : X ⟶ Y) :
    (Edge.id x₀).map f = Edge.id (f.app _ x₀) :=
  Truncated.Edge.map_id _ _

/-- The edge given by a `1`-simplex. -/
/-
**SSet.Edge.mk'** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Edge`。
形式化陈述：mk' (s : X _⦋1⦌) : Edge (X.δ 1 s) (X.δ 0 s)
参数：s : X _⦋1⦌。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The edge given by a `1`-simplex.
-/
def mk' (s : X _⦋1⦌) : Edge (X.δ 1 s) (X.δ 0 s) := mk s

@[simp]
/-
**SSet.Edge.mk'_edge** 是 Mathlib 中的一个定理，位于命名空间 `SSet.Edge`。
形式化陈述：∀ {X : _root_.SSet} (s : X.obj (Opposite.op { len := 1 })), (SSet.Edge.mk'
 s).edge = s
参数：s : X.obj (Opposite.op { len := 1 })；SSet.Edge.mk' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
lemma mk'_edge (s : X _⦋1⦌) : (mk' s).edge = s := rfl
/-
**SSet.Edge.exists_of_simplex** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Edge`。
形式化陈述：exists_of_simplex (s : X _⦋1⦌) : exists (x₀ x₁ : X _⦋0⦌) (e : Edge x₀ x₁),
 e.edge = s
参数：s : X _⦋1⦌。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
lemma exists_of_simplex (s : X _⦋1⦌) :
    ∃ (x₀ x₁ : X _⦋0⦌) (e : Edge x₀ x₁), e.edge = s :=
  ⟨_, _, mk' s, rfl⟩

/-- Transports an edge between `x₀` and `x₁` to an edge between `y₀` and `y₁`, given `x₀ = y₀`
and `x₁ = y₁`. -/
@[simps]
/-
**SSet.Edge.ofEq** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Edge`。
形式化陈述：ofEq {y₀ y₁ : X _⦋0⦌} (e : Edge x₀ x₁) (h₀ : x₀ = y₀) (h₁ : x₁ = y₁) : Edg
e y₀ y₁ where edge
参数：e : Edge x₀ x₁；h₀ : x₀ = y₀；h₁ : x₁ = y₁。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Transports an edge between `x₀` and `x₁` to an edge between `y₀` and `y₁`, given
 `x₀ = y₀`
and `x₁ = y₁`.
-/
def ofEq {y₀ y₁ : X _⦋0⦌} (e : Edge x₀ x₁) (h₀ : x₀ = y₀) (h₁ : x₁ = y₁) :
    Edge y₀ y₁ where
  edge    := e.edge
  src_eq  := e.src_eq.trans h₀
  tgt_eq  := e.tgt_eq.trans h₁

/-- Let `x₀`, `x₁`, `x₂` be `0`-simplices of a simplicial set `X`,
`e₀₁` an edge from `x₀` to `x₁`, `e₁₂` an edge from `x₁` to `x₂`,
`e₀₂` an edge from `x₀` to `x₂`. This is the data of a `2`-simplex whose
faces are respectively `e₀₂`, `e₁₂` and `e₀₁`. Such structures shall provide
relations in the homotopy category of arbitrary simplicial sets
(and specialized constructions for quasicategories and Kan complexes.). -/
/-
**SSet.Edge.CompStruct** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Edge`。
形式化陈述：CompStruct (e₀₁ : Edge x₀ x₁) (e₁₂ : Edge x₁ x₂) (e₀₂ : Edge x₀ x₂)
参数：e₀₁ : Edge x₀ x₁；e₁₂ : Edge x₁ x₂；e₀₂ : Edge x₀ x₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `x₀`, `x₁`, `x₂` be `0`-simplices of a simplicial set `X`,
`e₀₁` an edge from `x₀` to `x₁`, `e₁₂` an edge from `x₁` to `x₂`,
`e₀₂` an edge from `x₀` to `x₂`. This is the data of a `2`-simplex whose
faces are respectively `e₀₂`, `e₁₂` and `e₀₁`. Such structures shall provide
relations in the homotopy category of arbitrary simplicial sets
(and specialized constructions for quasicategories and Kan complexes.).
-/
def CompStruct (e₀₁ : Edge x₀ x₁) (e₁₂ : Edge x₁ x₂) (e₀₂ : Edge x₀ x₂) :=
  Truncated.Edge.CompStruct e₀₁.toTruncated e₁₂.toTruncated e₀₂.toTruncated

namespace CompStruct

variable {e₀₁ : Edge x₀ x₁} {e₁₂ : Edge x₁ x₂} {e₀₂ : Edge x₀ x₂}

/-- Constructor for `SSet.Edge.CompStruct` which takes as an input a term in the
definitionally equal type `SSet.Truncated.Edge.CompStruct` for the `2`-truncation of
the simplicial set. (This definition is made to contain abuse of defeq in
other definitions.) -/
/-
**SSet.Edge.CompStruct.ofTruncated** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Edge.CompStru
ct`。
形式化陈述：ofTruncated (h : Truncated.Edge.CompStruct e₀₁.toTruncated e₁₂.toTruncated
 e₀₂.toTruncated) : CompStruct e₀₁ e₁₂ e₀₂
参数：h : Truncated.Edge.CompStruct e₀₁.toTruncated e₁₂.toTruncated e₀₂.toTruncated
。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for `SSet.Edge.CompStruct` which takes as an input a term in the
definitionally equal type `SSet.Truncated.Edge.CompStruct` for the `2`-truncatio
n of
the simplicial set. (This definition is made to contain abuse of defeq in
other definitions.)
-/
def ofTruncated (h : Truncated.Edge.CompStruct e₀₁.toTruncated e₁₂.toTruncated e₀₂.toTruncated) :
    CompStruct e₀₁ e₁₂ e₀₂ := h

/-- Conversion from `SSet.Edge.CompStruct` to `SSet.Truncated.Edge.CompStruct`. -/
/-
**SSet.Edge.CompStruct.toTruncated** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Edge.CompStru
ct`。
形式化陈述：toTruncated (h : CompStruct e₀₁ e₁₂ e₀₂) : Truncated.Edge.CompStruct e₀₁.t
oTruncated e₁₂.toTruncated e₀₂.toTruncated
参数：h : CompStruct e₀₁ e₁₂ e₀₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Conversion from `SSet.Edge.CompStruct` to `SSet.Truncated.Edge.CompStruct`.
-/
def toTruncated (h : CompStruct e₀₁ e₁₂ e₀₂) :
    Truncated.Edge.CompStruct e₀₁.toTruncated e₁₂.toTruncated e₀₂.toTruncated :=
  h

section

variable (h : CompStruct e₀₁ e₁₂ e₀₂)

/-- The underlying `2`-simplex in a structure `SSet.Edge.CompStruct`. -/
/-
**SSet.Edge.CompStruct.simplex** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Edge.CompStruct`。
形式化陈述：simplex : X _⦋2⦌
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The underlying `2`-simplex in a structure `SSet.Edge.CompStruct`.
-/
def simplex : X _⦋2⦌ := h.toTruncated.simplex

@[simp]
/-
**SSet.Edge.CompStruct.d** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Edge.CompStruct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma d₂ : X.δ 2 h.simplex = e₀₁.edge := Truncated.Edge.CompStruct.d₂ h

@[simp]
/-
**SSet.Edge.CompStruct.d** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Edge.CompStruct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma d₀ : X.δ 0 h.simplex = e₁₂.edge := Truncated.Edge.CompStruct.d₀ h

@[simp]
/-
**SSet.Edge.CompStruct.d** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Edge.CompStruct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma d₁ : X.δ 1 h.simplex = e₀₂.edge := Truncated.Edge.CompStruct.d₁ h

end

section

variable (simplex : X _⦋2⦌)
  (d₂ : X.δ 2 simplex = e₀₁.edge := by cat_disch)
  (d₀ : X.δ 0 simplex = e₁₂.edge := by cat_disch)
  (d₁ : X.δ 1 simplex = e₀₂.edge := by cat_disch)

set_option backward.privateInPublic true in
/-- Constructor for `SSet.Edge.CompStruct`. -/
/-
**SSet.Edge.CompStruct.mk** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Edge.CompStruct`。
形式化陈述：mk : CompStruct e₀₁ e₁₂ e₀₂ where simplex
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for `SSet.Edge.CompStruct`.
-/
def mk : CompStruct e₀₁ e₁₂ e₀₂ where
  simplex := simplex

set_option backward.privateInPublic true in
@[simp]
/-
**SSet.Edge.CompStruct.mk_simplex** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Edge.CompStruc
t`。
形式化陈述：mk_simplex : (mk simplex).simplex = simplex
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
lemma mk_simplex : (mk simplex).simplex = simplex := rfl

end

@[ext]
/-
**SSet.Edge.CompStruct.ext** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Edge.CompStruct`。
形式化陈述：ext {h h' : CompStruct e₀₁ e₁₂ e₀₂} (eq : h.simplex = h'.simplex) : h = h'
参数：eq : h.simplex = h'.simplex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SSet.Truncated.Edge.CompStruct.ext`：∀ {X : SSet.Truncated 2}   {x₀ x₁ x₂
 : X.obj (Opposite.op { obj := { len := 0 }, property := SSet.Truncated.Edge._pr
oof_1 })}   {e₀₁ : SSet.…
-/
lemma ext {h h' : CompStruct e₀₁ e₁₂ e₀₂} (eq : h.simplex = h'.simplex) :
    h = h' :=
  Truncated.Edge.CompStruct.ext eq
/-
**SSet.Edge.CompStruct.exists_of_simplex** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Edge.Co
mpStruct`。
形式化陈述：exists_of_simplex (s : X _⦋2⦌) : exists (x₀ x₁ x₂ : X _⦋0⦌) (e₀₁ : Edge x₀
 x₁) (e₁₂ : Edge x₁ x₂) (e₀₂ : Edge x₀ x₂) (h : CompStruct e₀₁ e₁₂ e₀₂), h.simpl
ex = s
参数：s : X _⦋2⦌。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SSet.Truncated.Edge.CompStruct.exists_of_simplex`：exists_of_simplex (s :
 X _⦋2⦌₂) : exists (x₀ x₁ x₂ : X _⦋0⦌₂) (e₀₁ : Edge x₀ x₁) (e₁₂ : Edge x₁ x₂) (e
₀₂ : Edge x₀ x₂) (h : CompStruct e₀₁ e…
-/
lemma exists_of_simplex (s : X _⦋2⦌) :
    ∃ (x₀ x₁ x₂ : X _⦋0⦌) (e₀₁ : Edge x₀ x₁) (e₁₂ : Edge x₁ x₂)
      (e₀₂ : Edge x₀ x₂) (h : CompStruct e₀₁ e₁₂ e₀₂), h.simplex = s :=
  Truncated.Edge.CompStruct.exists_of_simplex (X := (truncation 2).obj X) s

/-- `e : Edge x₀ x₁` is a composition of `Edge.id x₀` with `e`. -/
/-
**SSet.Edge.CompStruct.idComp** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Edge.CompStruct`。
形式化陈述：idComp (e : Edge x₀ x₁) : CompStruct (.id x₀) e e
参数：e : Edge x₀ x₁。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`e : Edge x₀ x₁` is a composition of `Edge.id x₀` with `e`.
-/
def idComp (e : Edge x₀ x₁) : CompStruct (.id x₀) e e :=
  ofTruncated (.idComp _)

@[simp]
/-
**SSet.Edge.CompStruct.idComp_simplex** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Edge.CompS
truct`。
形式化陈述：idComp_simplex (e : Edge x₀ x₁) : (idComp e).simplex = X.σ 0 e.edge
参数：e : Edge x₀ x₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma idComp_simplex (e : Edge x₀ x₁) : (idComp e).simplex = X.σ 0 e.edge := rfl

/-- `e : Edge x₀ x₁` is a composition of `e` with `Edge.id x₁` -/
/-
**SSet.Edge.CompStruct.compId** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Edge.CompStruct`。
形式化陈述：compId (e : Edge x₀ x₁) : CompStruct e (.id x₁) e
参数：e : Edge x₀ x₁。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`e : Edge x₀ x₁` is a composition of `e` with `Edge.id x₁`
-/
def compId (e : Edge x₀ x₁) : CompStruct e (.id x₁) e :=
  ofTruncated (.compId _)

@[simp]
/-
**SSet.Edge.CompStruct.compId_simplex** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Edge.CompS
truct`。
形式化陈述：compId_simplex (e : Edge x₀ x₁) : (compId e).simplex = X.σ 1 e.edge
参数：e : Edge x₀ x₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma compId_simplex (e : Edge x₀ x₁) : (compId e).simplex = X.σ 1 e.edge := rfl

/-- The identity edge on a point, composed with itself, gives the identity. -/
/-
**SSet.Edge.CompStruct.idCompId** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Edge.CompStruct`
。
形式化陈述：idCompId (x : X _⦋0⦌) : CompStruct (id x) (id x) (id x)
参数：x : X _⦋0⦌。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity edge on a point, composed with itself, gives the identity.
-/
def idCompId (x : X _⦋0⦌) : CompStruct (id x) (id x) (id x) :=
  ofTruncated (.idCompId _)

@[simp]
/-
**SSet.Edge.CompStruct.idCompId_simplex** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Edge.Com
pStruct`。
形式化陈述：idCompId_simplex (x : X _⦋0⦌) : (idCompId x).simplex = X.σ 0 (X.σ 0 x)
参数：x : X _⦋0⦌。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SSet.Truncated.Edge.CompStruct.idCompId_simplex`：∀ {X : SSet.Truncated 2
} (x : X.obj (Opposite.op { obj := { len := 0 }, property := SSet.Truncated.Edge
._proof_1 })),   (SSet.Truncated.Edge…
-/
lemma idCompId_simplex (x : X _⦋0⦌) : (idCompId x).simplex = X.σ 0 (X.σ 0 x) :=
  Truncated.Edge.CompStruct.idCompId_simplex _

/-- The image of a `Edge.CompStruct` by a morphism of simplicial sets. -/
/-
**SSet.Edge.CompStruct.map** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Edge.CompStruct`。
形式化陈述：map (h : CompStruct e₀₁ e₁₂ e₀₂) (f : X ⟶ Y) : CompStruct (e₀₁.map f) (e₁₂
.map f) (e₀₂.map f)
参数：h : CompStruct e₀₁ e₁₂ e₀₂；f : X ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The image of a `Edge.CompStruct` by a morphism of simplicial sets.
-/
def map (h : CompStruct e₀₁ e₁₂ e₀₂) (f : X ⟶ Y) :
    CompStruct (e₀₁.map f) (e₁₂.map f) (e₀₂.map f) :=
  .ofTruncated (h.toTruncated.map ((truncation 2).map f))

@[simp]
/-
**SSet.Edge.CompStruct.map_simplex** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Edge.CompStru
ct`。
形式化陈述：map_simplex (h : CompStruct e₀₁ e₁₂ e₀₂) (f : X ⟶ Y) : (h.map f).simplex =
 f.app _ h.simplex
参数：h : CompStruct e₀₁ e₁₂ e₀₂；f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map_simplex (h : CompStruct e₀₁ e₁₂ e₀₂) (f : X ⟶ Y) :
    (h.map f).simplex = f.app _ h.simplex := rfl

/-- Transports a `CompStruct` between edges `e₀₁`, `e₁₂` and `e₀₂` to a `CompStruct` between edges
`f₀₁`, `f₁₂` and `f₀₂` along equalities of 1-simplices `eᵢⱼ.edge = fᵢⱼ.edge`. -/
@[simps]
/-
**SSet.Edge.CompStruct.ofEq** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Edge.CompStruct`。
形式化陈述：ofEq {y₀ y₁ y₂ : X _⦋0⦌} {e₀₁ : Edge x₀ x₁} {f₀₁ : Edge y₀ y₁} {e₁₂ : Edge
 x₁ x₂} {f₁₂ : Edge y₁ y₂} {e₀₂ : Edge x₀ x₂} {f₀₂ : Edge y₀ y₂} (c : CompStruct
 e₀₁ e₁₂ e₀₂) (h₀₁ : e₀₁.edge = f₀₁.edge) (h₁₂ : e₁₂.edge = f₁₂.edge) (h₀₂ : e₀₂
.edge = f₀₂.edge) : CompStruct f₀₁ f₁₂ f₀₂ where simplex
参数：c : CompStruct e₀₁ e₁₂ e₀₂；h₀₁ : e₀₁.edge = f₀₁.edge；h₁₂ : e₁₂.edge = f₁₂.edg
e；h₀₂ : e₀₂.edge = f₀₂.edge。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Transports a `CompStruct` between edges `e₀₁`, `e₁₂` and `e₀₂` to a `CompStruct`
 between edges
`f₀₁`, `f₁₂` and `f₀₂` along equalities of 1-simplices `eᵢⱼ.edge = fᵢⱼ.edge`.
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
/-
**SSet.Edge.InvStruct** 是 Mathlib 中的一个归纳类型，位于命名空间 `SSet.Edge`。
形式化陈述：{X : _root_.SSet} → {x₀ x₁ : X.obj (Opposite.op { len := 0 })} → SSet.Edge
 x₀ x₁ → Type u
参数：Opposite.op { len := 0 }。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For an edge `hom`, `InvStruct hom` encodes the data of a backward edge `inv`, an
d
2-simplices witnessing that `hom` and `inv` compose to the identity on their end
points.
This implies that `hom` becomes an isomorphism in the homotopy category.
-/
structure InvStruct (hom : Edge x₀ x₁) where
  /-- The backwards edge -/
  inv : Edge x₁ x₀
  /-- The simplex witnessing that `hom` and `inv` compose to the identity -/
  homInvId  : CompStruct hom inv (id x₀)
  /-- The simplex witnessing that `inv` and `hom` compose to the identity -/
  invHomId  : CompStruct inv hom (id x₁)

namespace InvStruct

/-- The identity edge has an inverse. -/
@[simps]
/-
**SSet.Edge.InvStruct.invStructId** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Edge.InvStruct
`。
形式化陈述：invStructId (x : X _⦋0⦌) : InvStruct (id x) where inv
参数：x : X _⦋0⦌。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity edge has an inverse.
-/
def invStructId (x : X _⦋0⦌) : InvStruct (id x) where
  inv := id x
  homInvId := CompStruct.idCompId x
  invHomId := CompStruct.idCompId x

/-- The inverse has an inverse. -/
@[simps]
/-
**SSet.Edge.InvStruct.invStructInv** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Edge.InvStruc
t`。
形式化陈述：invStructInv {hom : Edge x₀ x₁} (I : InvStruct hom) : InvStruct I.inv wher
e inv
参数：I : InvStruct hom。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inverse has an inverse.
-/
def invStructInv {hom : Edge x₀ x₁} (I : InvStruct hom) : InvStruct I.inv where
  inv := hom
  homInvId := I.invHomId
  invHomId := I.homInvId

/-- Maps an inverse along an morphism of simplicial sets. -/
@[simps]
/-
**SSet.Edge.InvStruct.map** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Edge.InvStruct`。
形式化陈述：map {hom : Edge x₀ x₁} (I : InvStruct hom) (f : X ⟶ Y) : InvStruct (hom.ma
p f) where inv
参数：I : InvStruct hom；f : X ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Maps an inverse along an morphism of simplicial sets.
-/
def map {hom : Edge x₀ x₁} (I : InvStruct hom) (f : X ⟶ Y) : InvStruct (hom.map f) where
  inv := I.inv.map f
  homInvId := (I.homInvId.map f).ofEq rfl rfl (Edge.ext_iff.mp (map_id _ _))
  invHomId := (I.invHomId.map f).ofEq rfl rfl (Edge.ext_iff.mp (map_id _ _))

/-- Transports an inverse for `hom` along an equality of 1-simplices `hom = hom'`.
  I.e. constructs an inverse for `hom'` from an inverse for `hom`. -/
@[simps]
/-
**SSet.Edge.InvStruct.ofEq** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Edge.InvStruct`。
形式化陈述：ofEq {y₀ y₁ : X _⦋0⦌} {hom : Edge x₀ x₁} {hom' : Edge y₀ y₁} (I : InvStruc
t hom) (hhom : hom.edge = hom'.edge) : InvStruct hom' where inv
参数：I : InvStruct hom；hhom : hom.edge = hom'.edge。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Transports an inverse for `hom` along an equality of 1-simplices `hom = hom'`.
  I.e. constructs an inverse for `hom'` from an inverse for `hom`.
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

