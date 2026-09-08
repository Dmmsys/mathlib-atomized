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
/-
**SSet.Truncated.Edge** 是 Mathlib 中的一个结构，位于命名空间 `SSet.Truncated`。
形式化陈述：Edge (x₀ x₁ : X _⦋0⦌₂) where /-- A `1`-simplex -/ edge : X _⦋1⦌₂ /-- The s
ource of the edge is `x₀`. -/ src_eq : X.map (δ₂ 1).op edge = x₀
参数：x₀ x₁ : X _⦋0⦌₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In a `2`-truncated simplicial set, an edge from a vertex `x₀` to `x₁` is
a `1`-simplex with prescribed `0`-dimensional faces.
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
/-
**SSet.Truncated.Edge.mk'** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Truncated.Edge`。
形式化陈述：mk' (s : X _⦋1⦌₂) : Edge (X.map (δ₂ 1).op s) (X.map (δ₂ 0).op s) where edg
e
参数：s : X _⦋1⦌₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The edge given by a `1`-simplex.
-/
def mk' (s : X _⦋1⦌₂) : Edge (X.map (δ₂ 1).op s) (X.map (δ₂ 0).op s) where
  edge := s
/-
**SSet.Truncated.Edge.exists_of_simplex** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Truncate
d.Edge`。
形式化陈述：exists_of_simplex (s : X _⦋1⦌₂) : exists (x₀ x₁ : X _⦋0⦌₂) (e : Edge x₀ x₁
), e.edge = s
参数：s : X _⦋1⦌₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
lemma exists_of_simplex (s : X _⦋1⦌₂) :
    ∃ (x₀ x₁ : X _⦋0⦌₂) (e : Edge x₀ x₁), e.edge = s :=
  ⟨_, _, mk' s, rfl⟩

/-- The constant edge on a `0`-simplex. -/
@[simps]
/-
**SSet.Truncated.Edge.id** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Truncated.Edge`。
形式化陈述：id (x : X _⦋0⦌₂) : Edge x x where edge
参数：x : X _⦋0⦌₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The constant edge on a `0`-simplex.
-/
def id (x : X _⦋0⦌₂) : Edge x x where
  edge := X.map (σ₂ 0).op x
  src_eq := by simp [← Functor.map_comp_apply, ← op_comp]
  tgt_eq := by simp [← Functor.map_comp_apply, ← op_comp]

/-- The image of an edge by a morphism of truncated simplicial sets. -/
@[simps]
/-
**SSet.Truncated.Edge.map** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Truncated.Edge`。
形式化陈述：map {x₀ x₁ : X _⦋0⦌₂} (e : Edge x₀ x₁) (f : X ⟶ Y) : Edge (f.app _ x₀) (f.
app _ x₁) where edge
参数：e : Edge x₀ x₁；f : X ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The image of an edge by a morphism of truncated simplicial sets.
-/
def map {x₀ x₁ : X _⦋0⦌₂} (e : Edge x₀ x₁) (f : X ⟶ Y) :
    Edge (f.app _ x₀) (f.app _ x₁) where
  edge := f.app _ e.edge
  src_eq := by simp [← NatTrans.naturality_apply]
  tgt_eq := by simp [← NatTrans.naturality_apply]

@[simp]
/-
**SSet.Truncated.Edge.map_id** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Truncated.Edge`。
形式化陈述：map_id (x : X _⦋0⦌₂) (f : X ⟶ Y) : (Edge.id x).map f = Edge.id (f.app _ x)
参数：x : X _⦋0⦌₂；f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SSet.Truncated.Edge.ext`：∀ {X : SSet.Truncated 2} {x₀ x₁ : X.obj (Opposi
te.op { obj := { len := 0 }, property := SSet.Truncated.Edge._proof_1 })}   {x y
 : SSet.Trunc…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SSet.Truncated.Edge.map_edge`：∀ {X Y : SSet.Truncated 2}   {x₀ x₁ : X.ob
j (Opposite.op { obj := { len := 0 }, property := SSet.Truncated.Edge._proof_1 }
)}   (e : SSet.Tru…
· 使用定理 `SSet.Truncated.Edge.id_edge`：∀ {X : SSet.Truncated 2} (x : X.obj (Opposi
te.op { obj := { len := 0 }, property := SSet.Truncated.Edge._proof_1 })),   (SS
et.Truncated.Edge…
· 使用定理 `CategoryTheory.NatTrans.naturality_apply`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {D : Type u_1} [inst_1 : CategoryTheory.Category.{v_1
, u_1} D]   {FD : outParam (D …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_id (x : X _⦋0⦌₂) (f : X ⟶ Y) :
    (Edge.id x).map f = Edge.id (f.app _ x) := by
  ext
  simp [NatTrans.naturality_apply]
/-
**SSet.Truncated.Edge.** 是 Mathlib 中的一个实例，位于命名空间 `SSet.Truncated.Edge`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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
/-
**SSet.Truncated.Edge.CompStruct** 是 Mathlib 中的一个结构，位于命名空间 `SSet.Truncated.Edge`
。
形式化陈述：CompStruct {x₀ x₁ x₂ : X _⦋0⦌₂} (e₀₁ : Edge x₀ x₁) (e₁₂ : Edge x₁ x₂) (e₀₂
 : Edge x₀ x₂) where /-- A `2`-simplex with prescribed `1`-dimensional faces -/ 
simplex : X _⦋2⦌₂ d₂ : X.map (δ₂ 2).op simplex = e₀₁.edge
参数：e₀₁ : Edge x₀ x₁；e₁₂ : Edge x₁ x₂；e₀₂ : Edge x₀ x₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `x₀`, `x₁`, `x₂` be `0`-simplices of a `2`-truncated simplicial set `X`,
`e₀₁` an edge from `x₀` to `x₁`, `e₁₂` an edge from `x₁` to `x₂`,
`e₀₂` an edge from `x₀` to `x₂`. This is the data of a `2`-simplex whose
faces are respectively `e₀₂`, `e₁₂` and `e₀₁`. Such structures shall provide
relations in the homotopy category of arbitrary (truncated) simplicial sets
(and specialized constructions for quasicategories and Kan complexes.).
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

/-
**SSet.Truncated.Edge.CompStruct.exists_of_simplex** 是 Mathlib 中的一个引理，位于命名空间 `SS
et.Truncated.Edge.CompStruct`。
形式化陈述：exists_of_simplex (s : X _⦋2⦌₂) : exists (x₀ x₁ x₂ : X _⦋0⦌₂) (e₀₁ : Edge 
x₀ x₁) (e₁₂ : Edge x₁ x₂) (e₀₂ : Edge x₀ x₂) (h : CompStruct e₀₁ e₁₂ e₀₂), h.sim
plex = s
参数：s : X _⦋2⦌₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp_apply`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, 
u₂} D]   (self : CategoryTh…
· 使用定理 `CategoryTheory.op_comp`：op_comp {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} : (f
 ≫ g).op = g.op ≫ f.op
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
-/
lemma exists_of_simplex (s : X _⦋2⦌₂) :
    ∃ (x₀ x₁ x₂ : X _⦋0⦌₂) (e₀₁ : Edge x₀ x₁) (e₁₂ : Edge x₁ x₂)
      (e₀₂ : Edge x₀ x₂) (h : CompStruct e₀₁ e₁₂ e₀₂), h.simplex = s := by
  refine ⟨X.map (Hom.tr (SimplexCategory.const _ _ 0)).op s,
    X.map (Hom.tr (SimplexCategory.const _ _ 1)).op s,
    X.map (Hom.tr (SimplexCategory.const _ _ 2)).op s,
    .mk _ ?_ ?_, .mk _ ?_ ?_, .mk _ ?_ ?_, .mk s rfl rfl rfl, rfl⟩
  all_goals
  · rw [← Functor.map_comp_apply, ← op_comp]
    apply congr_fun; congr
    decide

/-- `e : Edge x y` is a composition of `Edge.id x` with `e`. -/
/-
**SSet.Truncated.Edge.CompStruct.idComp** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Truncate
d.Edge.CompStruct`。
形式化陈述：idComp {x y : X _⦋0⦌₂} (e : Edge x y) : CompStruct (.id x) e e where simpl
ex
参数：e : Edge x y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`e : Edge x y` is a composition of `Edge.id x` with `e`.
-/
def idComp {x y : X _⦋0⦌₂} (e : Edge x y) :
    CompStruct (.id x) e e where
  simplex := X.map (σ₂ 0).op e.edge
  d₂ := by
    rw [← Functor.map_comp_apply, ← op_comp, δ₂_two_comp_σ₂_zero]
    simp
  d₀ := by
    rw [← Functor.map_comp_apply, ← op_comp, δ₂_zero_comp_σ₂_zero]
    simp
  d₁ := by
    rw [← Functor.map_comp_apply, ← op_comp, δ₂_one_comp_σ₂_zero]
    simp

/-- `e : Edge x y` is a composition of `e` with `Edge.id y`. -/
/-
**SSet.Truncated.Edge.CompStruct.compId** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Truncate
d.Edge.CompStruct`。
形式化陈述：compId {x y : X _⦋0⦌₂} (e : Edge x y) : CompStruct e (.id y) e where simpl
ex
参数：e : Edge x y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`e : Edge x y` is a composition of `e` with `Edge.id y`.
-/
def compId {x y : X _⦋0⦌₂} (e : Edge x y) :
    CompStruct e (.id y) e where
  simplex := X.map (σ₂ 1).op e.edge
  d₂ := by
    rw [← Functor.map_comp_apply, ← op_comp, δ₂_two_comp_σ₂_one]
    simp
  d₀ := by
    rw [← Functor.map_comp_apply, ← op_comp, δ₂_zero_comp_σ₂_one]
    simp
  d₁ := by
    rw [← Functor.map_comp_apply, ← op_comp, δ₂_one_comp_σ₂_one]
    simp

/-- `Edge.id x` is a composition of `Edge.id x` with `Edge.id x`. -/
@[simps!]
/-
**SSet.Truncated.Edge.CompStruct.idCompId** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Trunca
ted.Edge.CompStruct`。
形式化陈述：idCompId (x : X _⦋0⦌₂) : CompStruct (.id x) (.id x) (.id x)
参数：x : X _⦋0⦌₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Edge.id x` is a composition of `Edge.id x` with `Edge.id x`.
-/
def idCompId (x : X _⦋0⦌₂) :
    CompStruct (.id x) (.id x) (.id x) :=
  idComp _

attribute [local simp ←] FunctorToTypes.naturality in
/-- The image of a `Edge.CompStruct` by a morphism of `2`-truncated
simplicial sets. -/
@[simps]
/-
**SSet.Truncated.Edge.CompStruct.map** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Truncated.E
dge.CompStruct`。
形式化陈述：map {x₀ x₁ x₂ : X _⦋0⦌₂} {e₀₁ : Edge x₀ x₁} {e₁₂ : Edge x₁ x₂} {e₀₂ : Edge
 x₀ x₂} (h : CompStruct e₀₁ e₁₂ e₀₂) (f : X ⟶ Y) : CompStruct (e₀₁.map f) (e₁₂.m
ap f) (e₀₂.map f) where simplex
参数：h : CompStruct e₀₁ e₁₂ e₀₂；f : X ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The image of a `Edge.CompStruct` by a morphism of `2`-truncated
simplicial sets.
-/
def map {x₀ x₁ x₂ : X _⦋0⦌₂}
    {e₀₁ : Edge x₀ x₁} {e₁₂ : Edge x₁ x₂} {e₀₂ : Edge x₀ x₂}
    (h : CompStruct e₀₁ e₁₂ e₀₂) (f : X ⟶ Y) :
    CompStruct (e₀₁.map f) (e₁₂.map f) (e₀₂.map f) where
  simplex := f.app _ h.simplex

end CompStruct

end Edge

end SSet.Truncated

