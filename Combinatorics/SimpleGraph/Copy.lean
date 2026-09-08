/-
Copyright (c) 2023 Yaël Dillies, Mitchell Horner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Mitchell Horner
-/
module

public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Combinatorics.SimpleGraph.Subgraph

/-!
# Containment of graphs

This file introduces the concept of one simple graph containing a copy of another.

For two simple graphs `G` and `H`, a *copy* of `G` in `H` is a (not necessarily induced) subgraph of
`H` isomorphic to `G`.

If there exists a copy of `G` in `H`, we say that `H` *contains* `G`. This is equivalent to saying
that there is an injective graph homomorphism `G → H` between them (this is **not** the same as a
graph embedding, as we do not require the subgraph to be induced).

If there exists an induced copy of `G` in `H`, we say that `H` *inducingly contains* `G`. This is
equivalent to saying that there is a graph embedding `G ↪ H`.

## Main declarations

Containment:
* `SimpleGraph.Copy G H` is the type of copies of `G` in `H`, implemented as the subtype of
  *injective* homomorphisms.
* `SimpleGraph.IsContained G H`, `G ⊑ H` is the relation that `H` contains a copy of `G`, that
  is, the type of copies of `G` in `H` is nonempty. This is equivalent to the existence of an
  isomorphism from `G` to a subgraph of `H`.
  This is similar to `SimpleGraph.IsSubgraph` except that the simple graphs here need not have the
  same underlying vertex type.
* `SimpleGraph.Free` is the predicate that `H` is `G`-free, that is, `H` does not contain a copy of
  `G`. This is the negation of `SimpleGraph.IsContained` implemented for convenience.
* `SimpleGraph.killCopies G H`: Subgraph of `G` that does not contain `H`. Obtained by arbitrarily
  removing an edge from each copy of `H` in `G`.
* `SimpleGraph.copyCount G H`: Number of copies of `H` in `G`, i.e. number of subgraphs of `G`
  isomorphic to `H`.
* `SimpleGraph.labelledCopyCount G H`: Number of labelled copies of `H` in `G`, i.e. number of
  graph embeddings from `H` to `G`.

Induced containment:
* Induced copies of `G` inside `H` are already defined as `G ↪g H`.
* `SimpleGraph.IsIndContained G H` : `G` is contained as an induced subgraph in `H`.

## Notation

The following notation is declared in scope `SimpleGraph`:
* `G ⊑ H` for `SimpleGraph.IsContained G H`.
* `G ⊴ H` for `SimpleGraph.IsIndContained G H`.

## TODO

* Relate `⊥ ⊴ H` to there being an independent set in `H`.
* Count induced copies of a graph inside another.
* Make `copyCount`/`labelledCopyCount` computable (not necessarily efficiently).
-/

@[expose] public section

open Finset Function
open Fintype (card)

namespace SimpleGraph
variable {V W X α β γ : Type*} {G G₁ G₂ G₃ : SimpleGraph V} {H : SimpleGraph W} {I : SimpleGraph X}
  {A : SimpleGraph α} {B : SimpleGraph β} {C : SimpleGraph γ}

/-!
### Copies

#### Not necessarily induced copies

A copy of a subgraph `G` inside a subgraph `H` is an embedding of the vertices of `G` into the
vertices of `H`, such that adjacency in `G` implies adjacency in `H`.

We capture this concept by injective graph homomorphisms.
-/

section Copy

/-- The type of copies as a subtype of *injective* homomorphisms. -/
/-
**SimpleGraph.Copy** 是 Mathlib 中的一个归纳类型，位于命名空间 `SimpleGraph`。
形式化陈述：{α : Type u_4} → {β : Type u_5} → SimpleGraph α → SimpleGraph β → Type (ma
x u_4 u_5)
参数：max u_4 u_5。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of copies as a subtype of *injective* homomorphisms.
-/
structure Copy (A : SimpleGraph α) (B : SimpleGraph β) where
  /-- A copy gives rise to a homomorphism. -/
  toHom : A →g B
  injective' : Injective toHom

/-- An injective homomorphism gives rise to a copy. -/
/-
**SimpleGraph.Hom.toCopy** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Hom`。
形式化陈述：{α : Type u_4} →   {β : Type u_5} → {A : SimpleGraph α} → {B : SimpleGraph
 β} → (f : A →g B) → Function.Injective ⇑f → A.Copy B
参数：f : A →g B。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An injective homomorphism gives rise to a copy.
-/
abbrev Hom.toCopy (f : A →g B) (h : Injective f) : Copy A B := .mk f h

/-- An embedding gives rise to a copy. -/
/-
**SimpleGraph.Embedding.toCopy** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Embedding`
。
形式化陈述：{α : Type u_4} → {β : Type u_5} → {A : SimpleGraph α} → {B : SimpleGraph β
} → A ↪g B → A.Copy B
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An embedding gives rise to a copy.
-/
abbrev Embedding.toCopy (f : A ↪g B) : Copy A B := f.toHom.toCopy f.injective

/-- An isomorphism gives rise to a copy. -/
/-
**SimpleGraph.Iso.toCopy** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Iso`。
形式化陈述：{α : Type u_4} → {β : Type u_5} → {A : SimpleGraph α} → {B : SimpleGraph β
} → A ≃g B → A.Copy B
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An isomorphism gives rise to a copy.
-/
abbrev Iso.toCopy (f : A ≃g B) : Copy A B := f.toEmbedding.toCopy

namespace Copy

/-
**SimpleGraph.Copy.** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph.Copy`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : FunLike (Copy A B) α β where
  coe f := DFunLike.coe f.toHom
  coe_injective f g h := by obtain ⟨⟨_, _⟩, _⟩ := f; congr!
/-
**SimpleGraph.Copy.injective** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.Copy`。
形式化陈述：injective (f : Copy A B) : Injective f.toHom
参数：f : Copy A B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Copy.injective'`：∀ {α : Type u_4} {β : Type u_5} {A : Simple
Graph α} {B : SimpleGraph β} (self : A.Copy B),   Function.Injective ⇑self.toHom
-/
lemma injective (f : Copy A B) : Injective f.toHom := f.injective'
/-
**SimpleGraph.Copy.ext** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Copy`。
形式化陈述：∀ {α : Type u_4} {β : Type u_5} {A : SimpleGraph α} {B : SimpleGraph β} {f
 g : A.Copy B}, (∀ (a : α), f a = g a) → f = g
参数：∀ (a : α), f a = g a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
@[ext] lemma ext {f g : Copy A B} : (∀ a, f a = g a) → f = g := DFunLike.ext _ _
/-
**SimpleGraph.Copy.coe_toHom** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Copy`。
形式化陈述：∀ {α : Type u_4} {β : Type u_5} {A : SimpleGraph α} {B : SimpleGraph β} (f
 : A.Copy B), ⇑f.toHom = ⇑f
参数：f : A.Copy B。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_toHom (f : Copy A B) : ⇑f.toHom = f := rfl
/-
**SimpleGraph.Copy.toHom_apply** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Copy`。
形式化陈述：∀ {α : Type u_4} {β : Type u_5} {A : SimpleGraph α} {B : SimpleGraph β} (f
 : A.Copy B) (a : α), f.toHom a = f a
参数：f : A.Copy B；a : α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toHom_apply (f : Copy A B) (a : α) : ⇑f.toHom a = f a := rfl
/-
**SimpleGraph.Copy.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Copy`。
形式化陈述：∀ {α : Type u_4} {β : Type u_5} {A : SimpleGraph α} {B : SimpleGraph β} (f
 : A →g B) (hf : Function.Injective ⇑f),   ⇑{ toHom := f, injective' := hf } = ⇑
f
参数：f : A →g B；hf : Function.Injective ⇑f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_mk (f : A →g B) (hf) : ⇑(.mk f hf : Copy A B) = f := rfl

/-- A copy induces an embedding of edge sets. -/
/-
**SimpleGraph.Copy.mapEdgeSet** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Copy`。
形式化陈述：mapEdgeSet (f : Copy A B) : A.edgeSet ↪ B.edgeSet where toFun
参数：f : Copy A B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A copy induces an embedding of edge sets.
-/
def mapEdgeSet (f : Copy A B) : A.edgeSet ↪ B.edgeSet where
  toFun := f.toHom.mapEdgeSet
  inj' := Hom.mapEdgeSet.injective f.toHom f.injective

/-- A copy induces an embedding of neighbor sets. -/
/-
**SimpleGraph.Copy.mapNeighborSet** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Copy`。
形式化陈述：mapNeighborSet (f : Copy A B) (a : α) : A.neighborSet a ↪ B.neighborSet (f
 a) where toFun v
参数：f : Copy A B；a : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A copy induces an embedding of neighbor sets.
-/
def mapNeighborSet (f : Copy A B) (a : α) :
    A.neighborSet a ↪ B.neighborSet (f a) where
  toFun v := ⟨f v, f.toHom.apply_mem_neighborSet v.prop⟩
  inj' _ _ h := by
    rw [Subtype.mk_eq_mk] at h ⊢
    exact f.injective h

/-- A copy gives rise to an embedding of vertex types. -/
/-
**SimpleGraph.Copy.toEmbedding** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Copy`。
形式化陈述：toEmbedding (f : Copy A B) : α ↪ β
参数：f : Copy A B。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `SimpleGraph.Copy.injective`：injective (f : Copy A B) : Injective f.toHom

--- 原说明 ---
A copy gives rise to an embedding of vertex types.
-/
def toEmbedding (f : Copy A B) : α ↪ β := ⟨f, f.injective⟩

/-- The identity copy from a simple graph to itself. -/
/-
**SimpleGraph.Copy.id** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Copy`。
形式化陈述：{V : Type u_1} → (G : SimpleGraph V) → G.Copy G
参数：G : SimpleGraph V。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Function.injective_id`：∀ {α : Sort u_1}, Function.Injective id

--- 原说明 ---
The identity copy from a simple graph to itself.
-/
@[refl] def id (G : SimpleGraph V) : Copy G G := ⟨Hom.id, Function.injective_id⟩
/-
**SimpleGraph.Copy.coe_id** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Copy`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V}, ⇑(SimpleGraph.Copy.id G) = id
参数：SimpleGraph.Copy.id G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity copy from a simple graph to itself.
-/
@[simp, norm_cast] lemma coe_id : ⇑(id G) = _root_.id := rfl

/-- The composition of copies is a copy. -/
/-
**SimpleGraph.Copy.comp** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Copy`。
形式化陈述：comp (g : Copy B C) (f : Copy A B) : Copy A C
参数：g : Copy B C；f : Copy A B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The composition of copies is a copy.
-/
def comp (g : Copy B C) (f : Copy A B) : Copy A C := by
  use g.toHom.comp f.toHom
  rw [Hom.coe_comp]
  exact g.injective.comp f.injective

@[simp]
/-
**SimpleGraph.Copy.comp_apply** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Copy`。
形式化陈述：comp_apply (g : Copy B C) (f : Copy A B) (a : α) : g.comp f a = g (f a)
参数：g : Copy B C；f : Copy A B；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RelHom.comp_apply`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {r : α
 → α → Prop} {s : β → β → Prop} {t : γ → γ → Prop} (g : s →r t)   (f : r →r s) (
x : α),…
-/
theorem comp_apply (g : Copy B C) (f : Copy A B) (a : α) : g.comp f a = g (f a) :=
  RelHom.comp_apply g.toHom f.toHom a

/-- The copy from a subgraph to the supergraph. -/
/-
**SimpleGraph.Copy.ofLE** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Copy`。
形式化陈述：ofLE (G₁ G₂ : SimpleGraph V) (h : G₁ <= G₂) : Copy G₁ G₂
参数：G₁ G₂ : SimpleGraph V；h : G₁ <= G₂。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Function.injective_id`：∀ {α : Sort u_1}, Function.Injective id

--- 原说明 ---
The copy from a subgraph to the supergraph.
-/
def ofLE (G₁ G₂ : SimpleGraph V) (h : G₁ ≤ G₂) : Copy G₁ G₂ := ⟨Hom.ofLE h, Function.injective_id⟩

@[simp, norm_cast]
/-
**SimpleGraph.Copy.coe_comp** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Copy`。
形式化陈述：coe_comp (g : Copy B C) (f : Copy A B) : ⇑(g.comp f) = g ∘ f
参数：g : Copy B C；f : Copy A B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Copy.comp_apply`：comp_apply (g : Copy B C) (f : Copy A B) (a
 : α) : g.comp f a = g (f a)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coe_comp (g : Copy B C) (f : Copy A B) : ⇑(g.comp f) = g ∘ f := by ext; simp
/-
**SimpleGraph.Copy.coe_ofLE** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Copy`。
形式化陈述：∀ {V : Type u_1} {G₁ G₂ : SimpleGraph V} (h : G₁ ≤ G₂), ⇑(SimpleGraph.Copy
.ofLE G₁ G₂ h) = id
参数：h : G₁ ≤ G₂；SimpleGraph.Copy.ofLE G₁ G₂ h。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_ofLE (h : G₁ ≤ G₂) : ⇑(ofLE G₁ G₂ h) = _root_.id := rfl
/-
**SimpleGraph.Copy.ofLE_refl** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Copy`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V}, SimpleGraph.Copy.ofLE G G ⋯ = Simple
Graph.Copy.id G
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Copy.ext`：∀ {α : Type u_4} {β : Type u_5} {A : SimpleGraph α
} {B : SimpleGraph β} {f g : A.Copy B}, (∀ (a : α), f a = g a) → f = g
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem ofLE_refl : ofLE G G le_rfl = id G := by ext; simp

@[simp]
/-
**SimpleGraph.Copy.ofLE_comp** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Copy`。
形式化陈述：ofLE_comp (h₁₂ : G₁ <= G₂) (h₂₃ : G₂ <= G₃) : (ofLE _ _ h₂₃).comp (ofLE _ 
_ h₁₂) = ofLE _ _ (h₁₂.trans h₂₃)
参数：h₁₂ : G₁ <= G₂；h₂₃ : G₂ <= G₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Copy.ext`：∀ {α : Type u_4} {β : Type u_5} {A : SimpleGraph α
} {B : SimpleGraph β} {f g : A.Copy B}, (∀ (a : α), f a = g a) → f = g
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Copy.comp_apply`：comp_apply (g : Copy B C) (f : Copy A B) (a
 : α) : g.comp f a = g (f a)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ofLE_comp (h₁₂ : G₁ ≤ G₂) (h₂₃ : G₂ ≤ G₃) :
    (ofLE _ _ h₂₃).comp (ofLE _ _ h₁₂) = ofLE _ _ (h₁₂.trans h₂₃) := by ext; simp

/-- The copy from an induced subgraph to the initial simple graph. -/
/-
**SimpleGraph.Copy.induce** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Copy`。
形式化陈述：induce (G : SimpleGraph V) (s : Set V) : Copy (G.induce s) G
参数：G : SimpleGraph V；s : Set V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The copy from an induced subgraph to the initial simple graph.
-/
def induce (G : SimpleGraph V) (s : Set V) : Copy (G.induce s) G := (Embedding.induce s).toCopy

/-- The copy of `⊥` in any simple graph that can embed its vertices. -/
/-
**SimpleGraph.Copy.bot** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Copy`。
形式化陈述：{α : Type u_4} → {β : Type u_5} → {B : SimpleGraph β} → (α ↪ β) → ⊥.Copy B
参数：α ↪ β。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Embedding.injective`：∀ {α : Sort u_1} {β : Sort u_2} (f : α ↪ β
), Function.Injective ⇑f

--- 原说明 ---
The copy of `⊥` in any simple graph that can embed its vertices.
-/
protected def bot (f : α ↪ β) : Copy (⊥ : SimpleGraph α) B := ⟨⟨f, False.elim⟩, f.injective⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The isomorphism from a subgraph of `A` to its map under a copy `f : Copy A B`. -/
/-
**SimpleGraph.Copy.isoSubgraphMap** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Copy`。
形式化陈述：isoSubgraphMap (f : Copy A B) (A' : A.Subgraph) : A'.coe ≃g (A'.map f.toHo
m).coe
参数：f : Copy A B；A' : A.Subgraph。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `SimpleGraph.Copy.injective`：injective (f : Copy A B) : Injective f.toHom

--- 原说明 ---
The isomorphism from a subgraph of `A` to its map under a copy `f : Copy A B`.
-/
noncomputable def isoSubgraphMap (f : Copy A B) (A' : A.Subgraph) :
    A'.coe ≃g (A'.map f.toHom).coe := by
  use Equiv.Set.image f.toHom _ f.injective
  simp_rw [Subgraph.map_verts, Equiv.Set.image_apply, Subgraph.coe_adj, Subgraph.map_adj,
    Relation.map_apply, f.injective.eq_iff, exists_eq_right_right, exists_eq_right, forall_true_iff]

/-- The subgraph of `B` corresponding to a copy of `A` inside `B`. -/
/-
**SimpleGraph.Copy.toSubgraph** 是 Mathlib 中的一个缩写定义，位于命名空间 `SimpleGraph.Copy`。
形式化陈述：toSubgraph (f : Copy A B) : B.Subgraph
参数：f : Copy A B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The subgraph of `B` corresponding to a copy of `A` inside `B`.
-/
abbrev toSubgraph (f : Copy A B) : B.Subgraph := .map f.toHom ⊤

/-- The isomorphism from `A` to its copy under `f : Copy A B`. -/
/-
**SimpleGraph.Copy.isoToSubgraph** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Copy`。
形式化陈述：isoToSubgraph (f : Copy A B) : A ≃g f.toSubgraph.coe
参数：f : Copy A B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism from `A` to its copy under `f : Copy A B`.
-/
noncomputable def isoToSubgraph (f : Copy A B) : A ≃g f.toSubgraph.coe :=
  (f.isoSubgraphMap ⊤).comp Subgraph.topIso.symm
/-
**SimpleGraph.Copy.range_toSubgraph** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Copy`
。
形式化陈述：∀ {α : Type u_4} {β : Type u_5} {A : SimpleGraph α} {B : SimpleGraph β},  
 Set.range SimpleGraph.Copy.toSubgraph = {B' | Nonempty (A ≃g B'.coe)}
参数：A ≃g B'.coe。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `SimpleGraph.Subgraph.hom_injective`：hom_injective {x : Subgraph G} : Fun
ction.Injective x.hom
· 使用定理 `RelIso.injective`：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s 
: β → β → Prop} (e : r ≃r s), Function.Injective ⇑e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SimpleGraph.Subgraph.map_comp`：map_comp {U : Type*} {G'' : SimpleGraph U
} (H : G.Subgraph) (f : G ->g G') (g : G' ->g G'') : H.map (g.comp f) = (H.map f
).map g
· 使用定理 `SimpleGraph.Subgraph.map_iso_top`：∀ {V : Type u} {W : Type v} {G : Simpl
eGraph V} {H : SimpleGraph W} (e : G ≃g H), SimpleGraph.Subgraph.map e.toHom ⊤ =
 ⊤
· 使用定理 `SimpleGraph.Subgraph.map_hom_top`：∀ {V : Type u} {G : SimpleGraph V} (G'
 : G.Subgraph), SimpleGraph.Subgraph.map G'.hom ⊤ = G'
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma range_toSubgraph :
    .range (toSubgraph (A := A)) = {B' : B.Subgraph | Nonempty (A ≃g B'.coe)} := by
  ext H'
  constructor
  · rintro ⟨f, hf, rfl⟩
    simpa [toSubgraph] using ⟨f.isoToSubgraph⟩
  · rintro ⟨e⟩
    refine ⟨⟨H'.hom.comp e.toHom, Subgraph.hom_injective.comp e.injective⟩, ?_⟩
    simp [toSubgraph, Subgraph.map_comp]
/-
**SimpleGraph.Copy.toSubgraph_surjOn** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.Copy
`。
形式化陈述：toSubgraph_surjOn : Set.SurjOn (toSubgraph (A
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `SimpleGraph.Copy.range_toSubgraph`：∀ {α : Type u_4} {β : Type u_5} {A : 
SimpleGraph α} {B : SimpleGraph β},   Set.range SimpleGraph.Copy.toSubgraph = {B
' | Nonempty (A ≃g B'.c…
-/
lemma toSubgraph_surjOn :
    Set.SurjOn (toSubgraph (A := A)) .univ {B' : B.Subgraph | Nonempty (A ≃g B'.coe)} :=
  fun H' hH' ↦ by simpa
/-
**SimpleGraph.Copy.** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph.Copy`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Subsingleton (V → W)] : Subsingleton (G.Copy H) := DFunLike.coe_injective.subsingleton
/-
**SimpleGraph.Copy.** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph.Copy`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Fintype {f : G →g H // Injective f}] : Fintype (G.Copy H) :=
  .ofEquiv {f : G →g H // Injective f} {
    toFun f := ⟨f.1, f.2⟩
    invFun f := ⟨f.1, f.2⟩
  }

/-- A copy of `⊤` gives rise to an embedding of `⊤`. -/
@[simps!]
/-
**SimpleGraph.Copy.topEmbedding** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Copy`。
形式化陈述：topEmbedding (f : Copy (⊤ : SimpleGraph α) G) : (⊤ : SimpleGraph α) ↪g G
参数：f : Copy (⊤ : SimpleGraph α) G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A copy of `⊤` gives rise to an embedding of `⊤`.
-/
def topEmbedding (f : Copy (⊤ : SimpleGraph α) G) : (⊤ : SimpleGraph α) ↪g G :=
  { f.toEmbedding with
    map_rel_iff' := fun {v w} ↦ ⟨fun h ↦ by simpa using h.ne, f.toHom.map_adj⟩}

end Copy

/-- A `Subgraph G` gives rise to a copy from the coercion to `G`. -/
/-
**SimpleGraph.Subgraph.coeCopy** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Subgraph`。
形式化陈述：{V : Type u_1} → {G : SimpleGraph V} → (G' : G.Subgraph) → G'.coe.Copy G
参数：G' : G.Subgraph。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Subgraph.hom_injective`：hom_injective {x : Subgraph G} : Fun
ction.Injective x.hom

--- 原说明 ---
A `Subgraph G` gives rise to a copy from the coercion to `G`.
-/
def Subgraph.coeCopy (G' : G.Subgraph) : Copy G'.coe G := G'.hom.toCopy hom_injective

end Copy

/-!
#### Induced copies

An induced copy of a graph `G` inside a graph `H` is an embedding from the vertices of
`G` into the vertices of `H` which preserves the adjacency relation.

This is already captured by the notion of graph embeddings, defined as `G ↪g H`.

### Containment

#### Not necessarily induced containment

A graph `H` *contains* a graph `G` if there is some copy `f : Copy G H` of `G` inside `H`. This
amounts to `H` having a subgraph isomorphic to `G`.

We denote "`G` is contained in `H`" by `G ⊑ H` (`\squb`).
-/

section IsContained

/-- The relation `IsContained A B`, `A ⊑ B` says that `B` contains a copy of `A`.

This is equivalent to the existence of an isomorphism from `A` to a subgraph of `B`. -/
/-
**SimpleGraph.IsContained** 是 Mathlib 中的一个缩写定义，位于命名空间 `SimpleGraph`。
形式化陈述：IsContained (A : SimpleGraph α) (B : SimpleGraph β)
参数：A : SimpleGraph α；B : SimpleGraph β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The relation `IsContained A B`, `A ⊑ B` says that `B` contains a copy of `A`.

This is equivalent to the existence of an isomorphism from `A` to a subgraph of 
`B`.
-/
abbrev IsContained (A : SimpleGraph α) (B : SimpleGraph β) := Nonempty (Copy A B)

@[inherit_doc] scoped infixl:50 " ⊑ " => SimpleGraph.IsContained

/-- A simple graph contains itself. -/
/-
**SimpleGraph.IsContained.refl** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.IsContaine
d`。
形式化陈述：∀ {V : Type u_1} (G : SimpleGraph V), G.IsContained G
参数：G : SimpleGraph V。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A simple graph contains itself.
-/
@[refl] protected theorem IsContained.refl (G : SimpleGraph V) : G ⊑ G := ⟨.id G⟩
/-
**SimpleGraph.IsContained.rfl** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.IsContained
`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V}, G.IsContained G
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.IsContained.refl`：∀ {V : Type u_1} (G : SimpleGraph V), G.Is
Contained G

--- 原说明 ---
A simple graph contains itself.
-/
protected theorem IsContained.rfl : G ⊑ G := IsContained.refl G

/-- A simple graph contains its subgraphs. -/
/-
**SimpleGraph.IsContained.of_le** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.IsContain
ed`。
形式化陈述：∀ {V : Type u_1} {G₁ G₂ : SimpleGraph V}, G₁ ≤ G₂ → G₁.IsContained G₂
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A simple graph contains its subgraphs.
-/
theorem IsContained.of_le (h : G₁ ≤ G₂) : G₁ ⊑ G₂ := ⟨.ofLE G₁ G₂ h⟩

/-- If `A` contains `B` and `B` contains `C`, then `A` contains `C`. -/
/-
**SimpleGraph.IsContained.trans** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.IsContain
ed`。
形式化陈述：∀ {α : Type u_4} {β : Type u_5} {γ : Type u_6} {A : SimpleGraph α} {B : Si
mpleGraph β} {C : SimpleGraph γ},   A.IsContained B → B.IsContained C → A.IsCont
ained C
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `A` contains `B` and `B` contains `C`, then `A` contains `C`.
-/
theorem IsContained.trans : A ⊑ B → B ⊑ C → A ⊑ C := fun ⟨f⟩ ⟨g⟩ ↦ ⟨g.comp f⟩

/-- If `B` contains `C` and `A` contains `B`, then `A` contains `C`. -/
/-
**SimpleGraph.IsContained.trans'** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.IsContai
ned`。
形式化陈述：∀ {α : Type u_4} {β : Type u_5} {γ : Type u_6} {A : SimpleGraph α} {B : Si
mpleGraph β} {C : SimpleGraph γ},   B.IsContained C → A.IsContained B → A.IsCont
ained C
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.IsContained.trans`：∀ {α : Type u_4} {β : Type u_5} {γ : Type
 u_6} {A : SimpleGraph α} {B : SimpleGraph β} {C : SimpleGraph γ},   A.IsContain
ed B → B.IsContaine…

--- 原说明 ---
If `B` contains `C` and `A` contains `B`, then `A` contains `C`.
-/
theorem IsContained.trans' : B ⊑ C → A ⊑ B → A ⊑ C := flip IsContained.trans

@[gcongr]
/-
**SimpleGraph.IsContained.mono_right** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.IsCo
ntained`。
形式化陈述：∀ {α : Type u_4} {β : Type u_5} {A : SimpleGraph α} {B B' : SimpleGraph β}
, A.IsContained B → B ≤ B' → A.IsContained B'
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.IsContained.trans`：∀ {α : Type u_4} {β : Type u_5} {γ : Type
 u_6} {A : SimpleGraph α} {B : SimpleGraph β} {C : SimpleGraph γ},   A.IsContain
ed B → B.IsContaine…
· 使用定理 `SimpleGraph.IsContained.of_le`：∀ {V : Type u_1} {G₁ G₂ : SimpleGraph V},
 G₁ ≤ G₂ → G₁.IsContained G₂
-/
lemma IsContained.mono_right {B' : SimpleGraph β} (h_isub : A ⊑ B) (h_sub : B ≤ B') : A ⊑ B' :=
  h_isub.trans <| IsContained.of_le h_sub

alias IsContained.trans_le := IsContained.mono_right

@[gcongr]
/-
**SimpleGraph.IsContained.mono_left** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.IsCon
tained`。
形式化陈述：∀ {α : Type u_4} {β : Type u_5} {A : SimpleGraph α} {B : SimpleGraph β} {A
' : SimpleGraph α},   A ≤ A' → A'.IsContained B → A.IsContained B
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.IsContained.trans`：∀ {α : Type u_4} {β : Type u_5} {γ : Type
 u_6} {A : SimpleGraph α} {B : SimpleGraph β} {C : SimpleGraph γ},   A.IsContain
ed B → B.IsContaine…
· 使用定理 `SimpleGraph.IsContained.of_le`：∀ {V : Type u_1} {G₁ G₂ : SimpleGraph V},
 G₁ ≤ G₂ → G₁.IsContained G₂
-/
lemma IsContained.mono_left {A' : SimpleGraph α} (h_sub : A ≤ A') (h_isub : A' ⊑ B) : A ⊑ B :=
  (IsContained.of_le h_sub).trans h_isub

alias IsContained.trans_le' := IsContained.mono_left

/-- If `A ≃g H` and `B ≃g G` then `A` is contained in `B` if and only if `H` is contained
in `G`. -/
/-
**SimpleGraph.isContained_congr** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：isContained_congr (e₁ : A ≃g H) (e₂ : B ≃g G) : A ⊑ B ↔ H ⊑ G
参数：e₁ : A ≃g H；e₂ : B ≃g G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.IsContained.trans'`：∀ {α : Type u_4} {β : Type u_5} {γ : Typ
e u_6} {A : SimpleGraph α} {B : SimpleGraph β} {C : SimpleGraph γ},   B.IsContai
ned C → A.IsContaine…
· 使用定理 `SimpleGraph.IsContained.trans`：∀ {α : Type u_4} {β : Type u_5} {γ : Type
 u_6} {A : SimpleGraph α} {B : SimpleGraph β} {C : SimpleGraph γ},   A.IsContain
ed B → B.IsContaine…

--- 原说明 ---
If `A ≃g H` and `B ≃g G` then `A` is contained in `B` if and only if `H` is cont
ained
in `G`.
-/
theorem isContained_congr (e₁ : A ≃g H) (e₂ : B ≃g G) : A ⊑ B ↔ H ⊑ G :=
  ⟨.trans' ⟨e₂.toCopy⟩ ∘ .trans ⟨e₁.symm.toCopy⟩, .trans' ⟨e₂.symm.toCopy⟩ ∘ .trans ⟨e₁.toCopy⟩⟩
/-
**SimpleGraph.isContained_congr_left** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：isContained_congr_left (e₁ : A ≃g B) : A ⊑ C ↔ B ⊑ C
参数：e₁ : A ≃g B。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.isContained_congr`：isContained_congr (e₁ : A ≃g H) (e₂ : B ≃
g G) : A ⊑ B ↔ H ⊑ G
-/
lemma isContained_congr_left (e₁ : A ≃g B) : A ⊑ C ↔ B ⊑ C := isContained_congr e₁ .refl

alias ⟨_, IsContained.congr_left⟩ := isContained_congr_left
/-
**SimpleGraph.isContained_congr_right** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：isContained_congr_right (e₂ : B ≃g C) : A ⊑ B ↔ A ⊑ C
参数：e₂ : B ≃g C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.isContained_congr`：isContained_congr (e₁ : A ≃g H) (e₂ : B ≃
g G) : A ⊑ B ↔ H ⊑ G
-/
lemma isContained_congr_right (e₂ : B ≃g C) : A ⊑ B ↔ A ⊑ C := isContained_congr .refl e₂

alias ⟨_, IsContained.congr_right⟩ := isContained_congr_right
/-
**SimpleGraph.** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsPreorder (SimpleGraph α) IsContained where
  refl := .refl
  trans _ _ _ := .trans
/-
**SimpleGraph.** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance :
    Trans (α := SimpleGraph α) (β := SimpleGraph β) (γ := SimpleGraph γ)
      IsContained IsContained IsContained where
  trans := .trans

/-- A simple graph having no vertices is contained in any simple graph. -/
/-
**SimpleGraph.IsContained.of_isEmpty** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.IsCo
ntained`。
形式化陈述：∀ {α : Type u_4} {β : Type u_5} {A : SimpleGraph α} {B : SimpleGraph β} [I
sEmpty α], A.IsContained B
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A simple graph having no vertices is contained in any simple graph.
-/
lemma IsContained.of_isEmpty [IsEmpty α] : A ⊑ B :=
  ⟨⟨isEmptyElim, fun {a} ↦ isEmptyElim a⟩, isEmptyElim⟩

/-- `⊥` is contained in any simple graph having sufficiently many vertices. -/
/-
**SimpleGraph.bot_isContained_iff_card_le** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph
`。
形式化陈述：bot_isContained_iff_card_le [Fintype α] [Fintype β] : (⊥ : SimpleGraph α) 
⊑ B ↔ Fintype.card α <= Fintype.card β
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fintype.card_le_of_embedding`：card_le_of_embedding (f : α ↪ β) : card α 
<= card β
· 使用定理 `Function.Embedding.nonempty_of_card_le`：nonempty_of_card_le [Fintype α] 
[Fintype β] (h : Fintype.card α <= Fintype.card β) : Nonempty (α ↪ β)

--- 原说明 ---
`⊥` is contained in any simple graph having sufficiently many vertices.
-/
lemma bot_isContained_iff_card_le [Fintype α] [Fintype β] :
    (⊥ : SimpleGraph α) ⊑ B ↔ Fintype.card α ≤ Fintype.card β :=
  ⟨fun ⟨f⟩ ↦ Fintype.card_le_of_embedding f.toEmbedding,
    fun h ↦ ⟨Copy.bot (Function.Embedding.nonempty_of_card_le h).some⟩⟩

protected alias IsContained.bot := bot_isContained_iff_card_le

/-- A simple graph `G` contains all `Subgraph G` coercions. -/
/-
**SimpleGraph.Subgraph.coe_isContained** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Su
bgraph`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V} (G' : G.Subgraph), G'.coe.IsContained
 G
参数：G' : G.Subgraph。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A simple graph `G` contains all `Subgraph G` coercions.
-/
lemma Subgraph.coe_isContained (G' : G.Subgraph) : G'.coe ⊑ G := ⟨G'.coeCopy⟩

/-- `B` contains `A` if and only if `B` has a subgraph `B'` and `B'` is isomorphic to `A`. -/
/-
**SimpleGraph.isContained_iff_exists_iso_subgraph** 是 Mathlib 中的一个定理，位于命名空间 `Sim
pleGraph`。
形式化陈述：isContained_iff_exists_iso_subgraph : A ⊑ B ↔ exists B' : B.Subgraph, None
mpty (A ≃g B'.coe) where mp
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.IsContained.trans'`：∀ {α : Type u_4} {β : Type u_5} {γ : Typ
e u_6} {A : SimpleGraph α} {B : SimpleGraph β} {C : SimpleGraph γ},   B.IsContai
ned C → A.IsContaine…
· 使用定理 `SimpleGraph.Subgraph.coe_isContained`：∀ {V : Type u_1} {G : SimpleGraph 
V} (G' : G.Subgraph), G'.coe.IsContained G

--- 原说明 ---
`B` contains `A` if and only if `B` has a subgraph `B'` and `B'` is isomorphic t
o `A`.
-/
theorem isContained_iff_exists_iso_subgraph :
    A ⊑ B ↔ ∃ B' : B.Subgraph, Nonempty (A ≃g B'.coe) where
  mp := fun ⟨f⟩ ↦ ⟨.map f.toHom ⊤, ⟨f.isoToSubgraph⟩⟩
  mpr := fun ⟨B', ⟨e⟩⟩ ↦ B'.coe_isContained.trans' ⟨e.toCopy⟩

alias ⟨IsContained.exists_iso_subgraph, IsContained.of_exists_iso_subgraph⟩ :=
  isContained_iff_exists_iso_subgraph
/-
**SimpleGraph.Copy.degree_le** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Copy`。
形式化陈述：∀ {V : Type u_1} {W : Type u_2} {G : SimpleGraph V} {H : SimpleGraph W} (f
 : G.Copy H) (v : V)   [inst : Fintype ↑(G.neighborSet v)] [inst_1 : Fintype ↑(H
.neighborSet (f v))], G.degree v ≤ H.degree (f v)
参数：f : G.Copy H；v : V；G.neighborSet v；H.neighborSet (f v)；f v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.card_neighborSet_eq_degree`：card_neighborSet_eq_degree : Fin
type.card (G.neighborSet v) = G.degree v
· 使用定理 `Fintype.card_le_of_injective`：card_le_of_injective (f : α -> β) (hf : Fu
nction.Injective f) : card α <= card β
· 使用定理 `Function.Embedding.injective`：∀ {α : Sort u_1} {β : Sort u_2} (f : α ↪ β
), Function.Injective ⇑f
-/
theorem Copy.degree_le (f : Copy G H) (v : V) [Fintype <| G.neighborSet v]
    [Fintype <| H.neighborSet (f v)] : G.degree v ≤ H.degree (f v) := by
  simpa [card_neighborSet_eq_degree] using
    Fintype.card_le_of_injective _ (f.mapNeighborSet v).injective
/-
**SimpleGraph.Copy.maxDegree_mono** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Copy`。
形式化陈述：∀ {V : Type u_1} {W : Type u_2} {G : SimpleGraph V} {H : SimpleGraph W} [i
nst : Fintype V] [inst_1 : Fintype W]   [inst_2 : DecidableRel G.Adj] [inst_3 : 
DecidableRel H.Adj] (f : G.Copy H), G.maxDegree ≤ H.maxDegree
参数：f : G.Copy H。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SimpleGraph.maxDegree_of_subsingleton`：maxDegree_of_subsingleton [Decida
bleRel G.Adj] [Subsingleton V] : G.maxDegree = 0
· 使用定理 `IsEmpty.instSubsingleton`：∀ {α : Sort u} [IsEmpty α], Subsingleton α
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `SimpleGraph.exists_maximal_degree_vertex`：exists_maximal_degree_vertex [
DecidableRel G.Adj] [Nonempty V] : exists v, G.maxDegree = G.degree v
-/
theorem Copy.maxDegree_mono [Fintype V] [Fintype W] [DecidableRel G.Adj] [DecidableRel H.Adj]
    (f : Copy G H) : G.maxDegree ≤ H.maxDegree := by
  cases isEmpty_or_nonempty V
  · simp
  obtain ⟨v, h⟩ := exists_maximal_degree_vertex G
  grind [degree_le_maxDegree H (f v), f.degree_le v]

@[deprecated (since := "2026-05-20")] alias Copy.max_degree_le := Copy.maxDegree_mono
/-
**SimpleGraph.IsContained.maxDegree_mono** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.
IsContained`。
形式化陈述：∀ {V : Type u_1} {W : Type u_2} {G : SimpleGraph V} {H : SimpleGraph W} [i
nst : Fintype V] [inst_1 : Fintype W]   [inst_2 : DecidableRel G.Adj] [inst_3 : 
DecidableRel H.Adj], G.IsContained H → G.maxDegree ≤ H.maxDegree
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Copy.maxDegree_mono`：∀ {V : Type u_1} {W : Type u_2} {G : Si
mpleGraph V} {H : SimpleGraph W} [inst : Fintype V] [inst_1 : Fintype W]   [inst
_2 : DecidableRel G.A…
-/
theorem IsContained.maxDegree_mono [Fintype V] [Fintype W] [DecidableRel G.Adj] [DecidableRel H.Adj]
    (h : G ⊑ H) : G.maxDegree ≤ H.maxDegree := by
  have ⟨f⟩ := h
  exact f.maxDegree_mono

@[deprecated (since := "2026-05-20")] alias IsContained.max_degree_le := IsContained.maxDegree_mono

@[gcongr]
/-
**SimpleGraph.maxDegree_mono** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：maxDegree_mono {H : SimpleGraph V} [Fintype V] [DecidableRel G.Adj] [Decid
ableRel H.Adj] (hle : G <= H) : G.maxDegree <= H.maxDegree
参数：hle : G <= H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.IsContained.maxDegree_mono`：∀ {V : Type u_1} {W : Type u_2} 
{G : SimpleGraph V} {H : SimpleGraph W} [inst : Fintype V] [inst_1 : Fintype W] 
  [inst_2 : DecidableRel G.A…
· 使用定理 `SimpleGraph.IsContained.of_le`：∀ {V : Type u_1} {G₁ G₂ : SimpleGraph V},
 G₁ ≤ G₂ → G₁.IsContained G₂
-/
lemma maxDegree_mono {H : SimpleGraph V} [Fintype V] [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hle : G ≤ H) : G.maxDegree ≤ H.maxDegree :=
  IsContained.of_le hle |>.maxDegree_mono
/-
**SimpleGraph.Copy.minDegree_mono** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Copy`。
形式化陈述：∀ {V : Type u_1} {W : Type u_2} {G : SimpleGraph V} {H : SimpleGraph W} [i
nst : Fintype V] [inst_1 : Fintype W]   [inst_2 : DecidableRel G.Adj] [inst_3 : 
DecidableRel H.Adj] {f : G.Copy H},   Function.Surjective ⇑f → G.minDegree ≤ H.m
inDegree
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `Function.isEmpty`：∀ {α : Sort u} {β : Sort v} [IsEmpty β] (f : α → β), I
sEmpty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SimpleGraph.minDegree_of_subsingleton`：minDegree_of_subsingleton [Decida
bleRel G.Adj] [Subsingleton V] : G.minDegree = 0
· 使用定理 `IsEmpty.instSubsingleton`：∀ {α : Sort u} [IsEmpty α], Subsingleton α
· 使用定理 `SimpleGraph.le_minDegree_of_forall_le_degree`：le_minDegree_of_forall_le_
degree [DecidableRel G.Adj] [Nonempty V] (k : Nat) (h : forall v, k <= G.degree 
v) : k <= G.minDegree
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `SimpleGraph.Copy.degree_le`：∀ {V : Type u_1} {W : Type u_2} {G : SimpleG
raph V} {H : SimpleGraph W} (f : G.Copy H) (v : V)   [inst : Fintype ↑(G.neighbo
rSet v)] [inst_1…
· 使用定理 `SimpleGraph.minDegree_le_degree`：minDegree_le_degree [DecidableRel G.Adj
] (v : V) : G.minDegree <= G.degree v
-/
theorem Copy.minDegree_mono [Fintype V] [Fintype W] [DecidableRel G.Adj] [DecidableRel H.Adj]
    {f : Copy G H} (hf : Function.Surjective f) : G.minDegree ≤ H.minDegree := by
  cases isEmpty_or_nonempty W
  · have := Function.isEmpty f
    simp
  refine H.le_minDegree_of_forall_le_degree _ fun w ↦ ?_
  obtain ⟨v, rfl⟩ := hf w
  grw [← f.degree_le, ← minDegree_le_degree]

@[deprecated (since := "2026-05-20")] alias Copy.minDegree_le := Copy.minDegree_mono
/-
**SimpleGraph.Hom.minDegree_mono** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Hom`。
形式化陈述：∀ {V : Type u_1} {W : Type u_2} {G : SimpleGraph V} {H : SimpleGraph W} [i
nst : Fintype V] [inst_1 : Fintype W]   [inst_2 : DecidableRel G.Adj] [inst_3 : 
DecidableRel H.Adj] {f : G →g H},   Function.Bijective ⇑f → G.minDegree ≤ H.minD
egree
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Copy.minDegree_mono`：∀ {V : Type u_1} {W : Type u_2} {G : Si
mpleGraph V} {H : SimpleGraph W} [inst : Fintype V] [inst_1 : Fintype W]   [inst
_2 : DecidableRel G.A…
· 使用定理 `Function.Bijective.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β
}, Function.Bijective f → Function.Injective f
· 使用定理 `Function.Bijective.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → 
β}, Function.Bijective f → Function.Surjective f
-/
theorem Hom.minDegree_mono [Fintype V] [Fintype W] [DecidableRel G.Adj] [DecidableRel H.Adj]
    {f : G →g H} (hf : Function.Bijective f) : G.minDegree ≤ H.minDegree :=
  Copy.minDegree_mono (f := ⟨f, hf.injective⟩) hf.surjective

@[deprecated (since := "2026-05-20")] alias Hom.minDegree_le := Hom.minDegree_mono
/-
**SimpleGraph.maxDegree_induce_of_support_subset** 是 Mathlib 中的一个定理，位于命名空间 `Simp
leGraph`。
形式化陈述：maxDegree_induce_of_support_subset [Fintype V] [DecidableRel G.Adj] {s : S
et V} [DecidablePred (· in s)] (h : G.support subseteq s) : (G.induce s).maxDegr
ee = G.maxDegree
参数：· in s；h : G.support subseteq s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `SimpleGraph.Copy.maxDegree_mono`：∀ {V : Type u_1} {W : Type u_2} {G : Si
mpleGraph V} {H : SimpleGraph W} [inst : Fintype V] [inst_1 : Fintype W]   [inst
_2 : DecidableRel G.A…
· 使用定理 `SimpleGraph.maxDegree_le_of_forall_degree_le`：maxDegree_le_of_forall_deg
ree_le [DecidableRel G.Adj] (k : Nat) (h : forall v, G.degree v <= k) : G.maxDeg
ree <= k
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.IsIsolated.degree_eq_zero`：∀ {V : Type u_1} (G : SimpleGraph
 V) (v : V) [inst : Fintype ↑(G.neighborSet v)], G.IsIsolated v → G.degree v = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `SimpleGraph.mem_support_iff_not_isIsolated`：mem_support_iff_not_isIsolat
ed : v in G.support ↔ ¬ G.IsIsolated v
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `SimpleGraph.degree_le_maxDegree`：degree_le_maxDegree [DecidableRel G.Adj
] (v : V) : G.degree v <= G.maxDegree
· 使用定理 `SimpleGraph.degree_induce_of_neighborSet_subset`：degree_induce_of_neighb
orSet_subset {v : s} (h : G.neighborSet v subseteq s) : (G.induce s).degree v = 
G.degree v
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `SimpleGraph.neighborSet_subset_support`：neighborSet_subset_support (v : 
V) : G.neighborSet v subseteq G.support
-/
theorem maxDegree_induce_of_support_subset [Fintype V] [DecidableRel G.Adj] {s : Set V}
    [DecidablePred (· ∈ s)] (h : G.support ⊆ s) : (G.induce s).maxDegree = G.maxDegree := by
  apply le_antisymm <| Copy.maxDegree_mono <| Embedding.induce s |>.toCopy
  refine G.maxDegree_le_of_forall_degree_le _ fun v ↦ ?_
  by_cases hv : G.IsIsolated v
  · simp [hv]
  grw [← degree_le_maxDegree _ ⟨v, h <| G.mem_support_iff_not_isIsolated.mpr hv⟩,
    degree_induce_of_neighborSet_subset <| G.neighborSet_subset_support v |>.trans h]

end IsContained

section Free

/-- `A.Free B` means that `B` does not contain a copy of `A`. -/
/-
**SimpleGraph.Free** 是 Mathlib 中的一个缩写定义，位于命名空间 `SimpleGraph`。
形式化陈述：Free (A : SimpleGraph α) (B : SimpleGraph β)
参数：A : SimpleGraph α；B : SimpleGraph β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`A.Free B` means that `B` does not contain a copy of `A`.
-/
abbrev Free (A : SimpleGraph α) (B : SimpleGraph β) := ¬A ⊑ B
/-
**SimpleGraph.not_free** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：not_free : ¬A.Free B ↔ A ⊑ B
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
-/
lemma not_free : ¬A.Free B ↔ A ⊑ B := not_not

/-- If `A ≃g H` and `B ≃g G` then `B` is `A`-free if and only if `G` is `H`-free. -/
/-
**SimpleGraph.free_congr** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：free_congr (e₁ : A ≃g H) (e₂ : B ≃g G) : A.Free B ↔ H.Free G
参数：e₁ : A ≃g H；e₂ : B ≃g G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `SimpleGraph.isContained_congr`：isContained_congr (e₁ : A ≃g H) (e₂ : B ≃
g G) : A ⊑ B ↔ H ⊑ G

--- 原说明 ---
If `A ≃g H` and `B ≃g G` then `B` is `A`-free if and only if `G` is `H`-free.
-/
theorem free_congr (e₁ : A ≃g H) (e₂ : B ≃g G) : A.Free B ↔ H.Free G :=
  (isContained_congr e₁ e₂).not
/-
**SimpleGraph.free_congr_left** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：free_congr_left (e₁ : A ≃g B) : A.Free C ↔ B.Free C
参数：e₁ : A ≃g B。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.free_congr`：free_congr (e₁ : A ≃g H) (e₂ : B ≃g G) : A.Free 
B ↔ H.Free G
-/
lemma free_congr_left (e₁ : A ≃g B) : A.Free C ↔ B.Free C := free_congr e₁ .refl

alias ⟨_, Free.congr_left⟩ := free_congr_left
/-
**SimpleGraph.free_congr_right** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：free_congr_right (e₂ : B ≃g C) : A.Free B ↔ A.Free C
参数：e₂ : B ≃g C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.free_congr`：free_congr (e₁ : A ≃g H) (e₂ : B ≃g G) : A.Free 
B ↔ H.Free G
-/
lemma free_congr_right (e₂ : B ≃g C) : A.Free B ↔ A.Free C := free_congr .refl e₂

alias ⟨_, Free.congr_right⟩ := free_congr_right
/-
**SimpleGraph.free_bot** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：free_bot (h : A != ⊥) : A.Free (⊥ : SimpleGraph β)
参数：h : A != ⊥。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.edgeSet_nonempty`：∀ {V : Type u} {G : SimpleGraph V}, G.edge
Set.Nonempty ↔ G ≠ ⊥
· 使用定理 `SimpleGraph.Hom.map_mem_edgeSet`：map_mem_edgeSet {e : Sym2 V} (h : e in 
G.edgeSet) : e.map f in G'.edgeSet
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `SimpleGraph.edgeSet_bot`：edgeSet_bot : (⊥ : SimpleGraph V).edgeSet = ∅
· 使用定理 `Set.notMem_empty`：notMem_empty (x : α) : x ∉ (∅ : Set α)
-/
lemma free_bot (h : A ≠ ⊥) : A.Free (⊥ : SimpleGraph β) := by
  rw [← edgeSet_nonempty] at h
  intro ⟨f, hf⟩
  absurd f.map_mem_edgeSet h.choose_spec
  rw [edgeSet_bot]
  exact Set.notMem_empty (h.choose.map f)

end Free

/-!
#### Induced containment

A graph `H` *inducingly contains* a graph `G` if there is some graph embedding `G ↪ H`. This amounts
to `H` having an induced subgraph isomorphic to `G`.

We denote "`G` is inducingly contained in `H`" by `G ⊴ H` (`\trianglelefteq`).
-/

/-- A simple graph `G` is inducingly contained in a simple graph `H` if there exists an induced
subgraph of `H` isomorphic to `G`. This is denoted by `G ⊴ H`. -/
/-
**SimpleGraph.IsIndContained** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：IsIndContained (G : SimpleGraph V) (H : SimpleGraph W) : Prop
参数：G : SimpleGraph V；H : SimpleGraph W。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A simple graph `G` is inducingly contained in a simple graph `H` if there exists
 an induced
subgraph of `H` isomorphic to `G`. This is denoted by `G ⊴ H`.
-/
def IsIndContained (G : SimpleGraph V) (H : SimpleGraph W) : Prop := Nonempty (G ↪g H)

@[inherit_doc] scoped infixl:50 " ⊴ " => SimpleGraph.IsIndContained
/-
**SimpleGraph.Copy.isContained** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Copy`。
形式化陈述：∀ {V : Type u_1} {W : Type u_2} {G : SimpleGraph V} {H : SimpleGraph W} (f
 : G.Copy H), G.IsContained H
参数：f : G.Copy H。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected lemma Copy.isContained (f : Copy G H) : G ⊑ H := ⟨f⟩
/-
**SimpleGraph.Embedding.isIndContained** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Em
bedding`。
形式化陈述：∀ {V : Type u_1} {W : Type u_2} {G : SimpleGraph V} {H : SimpleGraph W} (f
 : G ↪g H), G.IsIndContained H
参数：f : G ↪g H。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected lemma Embedding.isIndContained (f : G ↪g H) : G ⊴ H := ⟨f⟩
/-
**SimpleGraph.Embedding.isContained** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Embed
ding`。
形式化陈述：∀ {V : Type u_1} {W : Type u_2} {G : SimpleGraph V} {H : SimpleGraph W} (f
 : G ↪g H), G.IsContained H
参数：f : G ↪g H。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Copy.isContained`：∀ {V : Type u_1} {W : Type u_2} {G : Simpl
eGraph V} {H : SimpleGraph W} (f : G.Copy H), G.IsContained H
-/
protected lemma Embedding.isContained (f : G ↪g H) : G ⊑ H := f.toCopy.isContained
/-
**SimpleGraph.IsIndContained.isContained** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.
IsIndContained`。
形式化陈述：∀ {V : Type u_1} {W : Type u_2} {G : SimpleGraph V} {H : SimpleGraph W}, G
.IsIndContained H → G.IsContained H
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Embedding.isContained`：∀ {V : Type u_1} {W : Type u_2} {G : 
SimpleGraph V} {H : SimpleGraph W} (f : G ↪g H), G.IsContained H
-/
protected lemma IsIndContained.isContained : G ⊴ H → G ⊑ H := fun ⟨f⟩ ↦ f.isContained

/-- If `G` is isomorphic to `H`, then `G` is contained in `H`. -/
/-
**SimpleGraph.Iso.isContained** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Iso`。
形式化陈述：∀ {V : Type u_1} {W : Type u_2} {G : SimpleGraph V} {H : SimpleGraph W} (e
 : G ≃g H), G.IsContained H
参数：e : G ≃g H。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Copy.isContained`：∀ {V : Type u_1} {W : Type u_2} {G : Simpl
eGraph V} {H : SimpleGraph W} (f : G.Copy H), G.IsContained H

--- 原说明 ---
If `G` is isomorphic to `H`, then `G` is contained in `H`.
-/
protected lemma Iso.isContained (e : G ≃g H) : G ⊑ H := e.toCopy.isContained

/-- If `G` is isomorphic to `H`, then `H` is contained in `G`. -/
/-
**SimpleGraph.Iso.isContained'** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Iso`。
形式化陈述：∀ {V : Type u_1} {W : Type u_2} {G : SimpleGraph V} {H : SimpleGraph W} (e
 : G ≃g H), H.IsContained G
参数：e : G ≃g H。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Iso.isContained`：∀ {V : Type u_1} {W : Type u_2} {G : Simple
Graph V} {H : SimpleGraph W} (e : G ≃g H), G.IsContained H

--- 原说明 ---
If `G` is isomorphic to `H`, then `H` is contained in `G`.
-/
protected lemma Iso.isContained' (e : G ≃g H) : H ⊑ G := e.symm.isContained

/-- If `G` is isomorphic to `H`, then `G` is inducingly contained in `H`. -/
/-
**SimpleGraph.Iso.isIndContained** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Iso`。
形式化陈述：∀ {V : Type u_1} {W : Type u_2} {G : SimpleGraph V} {H : SimpleGraph W} (e
 : G ≃g H), G.IsIndContained H
参数：e : G ≃g H。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Embedding.isIndContained`：∀ {V : Type u_1} {W : Type u_2} {G
 : SimpleGraph V} {H : SimpleGraph W} (f : G ↪g H), G.IsIndContained H

--- 原说明 ---
If `G` is isomorphic to `H`, then `G` is inducingly contained in `H`.
-/
protected lemma Iso.isIndContained (e : G ≃g H) : G ⊴ H := e.toEmbedding.isIndContained

/-- If `G` is isomorphic to `H`, then `H` is inducingly contained in `G`. -/
/-
**SimpleGraph.Iso.isIndContained'** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Iso`。
形式化陈述：∀ {V : Type u_1} {W : Type u_2} {G : SimpleGraph V} {H : SimpleGraph W} (e
 : G ≃g H), H.IsIndContained G
参数：e : G ≃g H。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Iso.isIndContained`：∀ {V : Type u_1} {W : Type u_2} {G : Sim
pleGraph V} {H : SimpleGraph W} (e : G ≃g H), G.IsIndContained H

--- 原说明 ---
If `G` is isomorphic to `H`, then `H` is inducingly contained in `G`.
-/
protected lemma Iso.isIndContained' (e : G ≃g H) : H ⊴ G := e.symm.isIndContained
/-
**SimpleGraph.Subgraph.IsInduced.isIndContained** 是 Mathlib 中的一个定理，位于命名空间 `Simpl
eGraph.Subgraph.IsInduced`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V} {G' : G.Subgraph}, G'.IsInduced → G'.
coe.IsIndContained G
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `SimpleGraph.Subgraph.IsInduced.adj`：∀ {V : Type u} {G : SimpleGraph V} {
G' : G.Subgraph}, G'.IsInduced → ∀ {a b : ↑G'.verts}, G'.Adj ↑a ↑b ↔ G.Adj ↑a ↑b
-/
protected lemma Subgraph.IsInduced.isIndContained {G' : G.Subgraph} (hG' : G'.IsInduced) :
    G'.coe ⊴ G :=
  ⟨{ toFun := (↑)
     inj' := Subtype.coe_injective
     map_rel_iff' := hG'.adj.symm }⟩
/-
**SimpleGraph.IsIndContained.refl** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.IsIndCo
ntained`。
形式化陈述：∀ {V : Type u_1} (G : SimpleGraph V), G.IsIndContained G
参数：G : SimpleGraph V。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[refl] lemma IsIndContained.refl (G : SimpleGraph V) : G ⊴ G := ⟨Embedding.refl⟩
/-
**SimpleGraph.IsIndContained.rfl** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.IsIndCon
tained`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V}, G.IsIndContained G
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.IsIndContained.refl`：∀ {V : Type u_1} (G : SimpleGraph V), G
.IsIndContained G
-/
lemma IsIndContained.rfl : G ⊴ G := .refl _
/-
**SimpleGraph.IsIndContained.trans** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.IsIndC
ontained`。
形式化陈述：∀ {V : Type u_1} {W : Type u_2} {X : Type u_3} {G : SimpleGraph V} {H : Si
mpleGraph W} {I : SimpleGraph X},   G.IsIndContained H → H.IsIndContained I → G.
IsIndContained I
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[trans] lemma IsIndContained.trans : G ⊴ H → H ⊴ I → G ⊴ I := fun ⟨f⟩ ⟨g⟩ ↦ ⟨g.comp f⟩
/-
**SimpleGraph.** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsPreorder (SimpleGraph α) IsIndContained where
  refl := .refl
  trans _ _ _ := .trans
/-
**SimpleGraph.** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance :
    Trans (α := SimpleGraph α) (β := SimpleGraph β) (γ := SimpleGraph γ)
      IsIndContained IsIndContained IsIndContained where
  trans := .trans
/-
**SimpleGraph.IsIndContained.of_isEmpty** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.I
sIndContained`。
形式化陈述：∀ {V : Type u_1} {W : Type u_2} {G : SimpleGraph V} {H : SimpleGraph W} [I
sEmpty V], G.IsIndContained H
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma IsIndContained.of_isEmpty [IsEmpty V] : G ⊴ H :=
  ⟨{ toFun := isEmptyElim
     inj' := isEmptyElim
     map_rel_iff' := fun {a} ↦ isEmptyElim a }⟩
/-
**SimpleGraph.isIndContained_iff_exists_iso_subgraph** 是 Mathlib 中的一个引理，位于命名空间 `
SimpleGraph`。
形式化陈述：isIndContained_iff_exists_iso_subgraph : G ⊴ H ↔ exists (H' : H.Subgraph) 
(_e : G ≃g H'.coe), H'.IsInduced
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Subgraph.map_verts`：∀ {V : Type u} {W : Type v} {G : SimpleG
raph V} {G' : SimpleGraph W} (f : G →g G') (H : G.Subgraph),   (SimpleGraph.Subg
raph.map f H).verts …
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `SimpleGraph.Subgraph.map_adj`：∀ {V : Type u} {W : Type v} {G : SimpleGra
ph V} {G' : SimpleGraph W} (f : G →g G') (H : G.Subgraph) (a a_1 : W),   (Simple
Graph.Subgraph.map…
· 使用定理 `RelEmbedding.injective`：injective (f : r ↪r s) : Injective f
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `SimpleGraph.IsIndContained.trans`：∀ {V : Type u_1} {W : Type u_2} {X : T
ype u_3} {G : SimpleGraph V} {H : SimpleGraph W} {I : SimpleGraph X},   G.IsIndC
ontained H → H.IsIndCo…
· 使用定理 `SimpleGraph.Iso.isIndContained`：∀ {V : Type u_1} {W : Type u_2} {G : Sim
pleGraph V} {H : SimpleGraph W} (e : G ≃g H), G.IsIndContained H
· 使用定理 `SimpleGraph.Subgraph.IsInduced.isIndContained`：∀ {V : Type u_1} {G : Sim
pleGraph V} {G' : G.Subgraph}, G'.IsInduced → G'.coe.IsIndContained G
-/
lemma isIndContained_iff_exists_iso_subgraph :
    G ⊴ H ↔ ∃ (H' : H.Subgraph) (_e : G ≃g H'.coe), H'.IsInduced := by
  constructor
  · rintro ⟨f⟩
    refine ⟨f.toCopy.toSubgraph, f.toCopy.isoToSubgraph, ?_⟩
    simp [Subgraph.IsInduced, Relation.map_apply_apply, f.injective]
  · rintro ⟨H', e, hH'⟩
    exact e.isIndContained.trans hH'.isIndContained

alias ⟨IsIndContained.exists_iso_subgraph, IsIndContained.of_exists_iso_subgraph⟩ :=
  isIndContained_iff_exists_iso_subgraph
/-
**SimpleGraph.isIndContained_iff_exists_iso_induce** 是 Mathlib 中的一个定理，位于命名空间 `Si
mpleGraph`。
形式化陈述：isIndContained_iff_exists_iso_induce : G ⊴ H ↔ exists s, Nonempty (G ≃g H.
induce s)
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isIndContained_iff_exists_iso_induce : G ⊴ H ↔ ∃ s, Nonempty (G ≃g H.induce s) :=
  ⟨fun ⟨f⟩ ↦ ⟨Set.range f, ⟨f.isoInduceRange⟩⟩, fun ⟨s, ⟨f⟩⟩ ↦ ⟨.comp (.induce s) f⟩⟩
/-
**SimpleGraph.top_isIndContained_iff_top_isContained** 是 Mathlib 中的一个定理，位于命名空间 `
SimpleGraph`。
形式化陈述：∀ {V : Type u_1} {W : Type u_2} {H : SimpleGraph W}, ⊤.IsIndContained H ↔ 
⊤.IsContained H
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.IsIndContained.isContained`：∀ {V : Type u_1} {W : Type u_2} 
{G : SimpleGraph V} {H : SimpleGraph W}, G.IsIndContained H → G.IsContained H
-/
@[simp] lemma top_isIndContained_iff_top_isContained :
    (⊤ : SimpleGraph V) ⊴ H ↔ (⊤ : SimpleGraph V) ⊑ H :=
  ⟨IsIndContained.isContained, fun ⟨f⟩ ↦ ⟨f.topEmbedding⟩⟩
/-
**SimpleGraph.isContained_top_iff** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：isContained_top_iff {G : SimpleGraph V} : G ⊑ completeGraph W ↔ Nonempty (
V ↪ W)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.IsContained.trans`：∀ {α : Type u_4} {β : Type u_5} {γ : Type
 u_6} {A : SimpleGraph α} {B : SimpleGraph β} {C : SimpleGraph γ},   A.IsContain
ed B → B.IsContaine…
· 使用定理 `SimpleGraph.IsContained.of_le`：∀ {V : Type u_1} {G₁ G₂ : SimpleGraph V},
 G₁ ≤ G₂ → G₁.IsContained G₂
· 使用定理 `le_top`：le_top : a <= ⊤
-/
theorem isContained_top_iff {G : SimpleGraph V} : G ⊑ completeGraph W ↔ Nonempty (V ↪ W) :=
  ⟨(⟨·.some.toEmbedding⟩), (.trans (.of_le le_top) ⟨Embedding.completeGraph ·.some |>.toCopy⟩)⟩
/-
**SimpleGraph.top_isIndContained_top_iff** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`
。
形式化陈述：top_isIndContained_top_iff : completeGraph V ⊴ completeGraph W ↔ Nonempty 
(V ↪ W)
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem top_isIndContained_top_iff : completeGraph V ⊴ completeGraph W ↔ Nonempty (V ↪ W) :=
  ⟨(⟨·.some.toEmbedding⟩), (⟨.completeGraph ·.some⟩)⟩
/-
**SimpleGraph.eq_top_of_isIndContained_top** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGrap
h`。
形式化陈述：eq_top_of_isIndContained_top (h : G ⊴ completeGraph W) : G = ⊤
参数：h : G ⊴ completeGraph W。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SimpleGraph.comap_top`：comap_top {f : V -> W} (hf : f.Injective) : (comp
leteGraph W).comap f = completeGraph V
· 使用定理 `RelEmbedding.injective`：injective (f : r ↪r s) : Injective f
· 使用定理 `SimpleGraph.Embedding.comap_eq`：comap_eq (f : H ↪g G) : G.comap f = H
-/
theorem eq_top_of_isIndContained_top (h : G ⊴ completeGraph W) : G = ⊤ :=
  h.some.comap_eq ▸ comap_top h.some.injective
/-
**SimpleGraph.compl_isIndContained_compl** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`
。
形式化陈述：∀ {V : Type u_1} {W : Type u_2} {G : SimpleGraph V} {H : SimpleGraph W}, G
ᶜ.IsIndContained Hᶜ ↔ G.IsIndContained H
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.nonempty_congr`：nonempty_congr (e : α ≃ β) : Nonempty α ↔ Nonempty
 β
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
@[simp] lemma compl_isIndContained_compl : Gᶜ ⊴ Hᶜ ↔ G ⊴ H :=
  Embedding.complEquiv.symm.nonempty_congr

protected alias ⟨IsIndContained.of_compl, IsIndContained.compl⟩ := compl_isIndContained_compl
/-
**SimpleGraph.isContained_iff_exists_le_comap** 是 Mathlib 中的一个定理，位于命名空间 `SimpleG
raph`。
形式化陈述：isContained_iff_exists_le_comap : H ⊑ G ↔ exists (f : W ↪ V), H <= G.comap
 f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Hom.le_comap`：le_comap (f : H ->g G) : H <= G.comap f
· 使用定理 `Function.Embedding.injective`：∀ {α : Sort u_1} {β : Sort u_2} (f : α ↪ β
), Function.Injective ⇑f
-/
theorem isContained_iff_exists_le_comap : H ⊑ G ↔ ∃ (f : W ↪ V), H ≤ G.comap f :=
  ⟨fun ⟨f⟩ ↦ ⟨f.toEmbedding, f.toHom.le_comap⟩, fun ⟨f, h⟩ ↦ ⟨⟨f, (h ·)⟩, f.injective⟩⟩
/-
**SimpleGraph.isIndContained_iff_exists_comap_eq** 是 Mathlib 中的一个定理，位于命名空间 `Simp
leGraph`。
形式化陈述：isIndContained_iff_exists_comap_eq : H ⊴ G ↔ exists (f : W ↪ V), G.comap f
 = H
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Embedding.comap_eq`：comap_eq (f : H ↪g G) : G.comap f = H
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isIndContained_iff_exists_comap_eq : H ⊴ G ↔ ∃ (f : W ↪ V), G.comap f = H :=
  ⟨fun ⟨f⟩ ↦ ⟨f.toEmbedding, f.comap_eq⟩, fun ⟨f, h⟩ ↦ ⟨f, h ▸ .rfl⟩⟩

/-!
### Counting the copies

If `G` and `H` are finite graphs, we can count the number of unlabelled and labelled copies of `G`
in `H`.

#### Not necessarily induced copies
-/

section LabelledCopyCount
variable [Fintype V] [Fintype W]

/-- `G.labelledCopyCount H` is the number of labelled copies of `H` in `G`, i.e. the number of graph
embeddings from `H` to `G`. See `SimpleGraph.copyCount` for the number of unlabelled copies. -/
/-
**SimpleGraph.labelledCopyCount** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：labelledCopyCount (G : SimpleGraph V) (H : SimpleGraph W) : Nat
参数：G : SimpleGraph V；H : SimpleGraph W。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`G.labelledCopyCount H` is the number of labelled copies of `H` in `G`, i.e. the
 number of graph
embeddings from `H` to `G`. See `SimpleGraph.copyCount` for the number of unlabe
lled copies.
-/
noncomputable def labelledCopyCount (G : SimpleGraph V) (H : SimpleGraph W) : ℕ := by
  classical exact Fintype.card (Copy H G)
/-
**SimpleGraph.labelledCopyCount_of_isEmpty** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGrap
h`。
形式化陈述：∀ {V : Type u_1} {W : Type u_2} [inst : Fintype V] [inst_1 : Fintype W] [I
sEmpty W] (G : SimpleGraph V)   (H : SimpleGraph W), G.labelledCopyCount H = 1
参数：G : SimpleGraph V；H : SimpleGraph W。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fintype.card_unique`：card_unique [Unique α] [h : Fintype α] : Fintype.ca
rd α = 1
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `SimpleGraph.Copy.instSubsingletonOfForall`：∀ {V : Type u_1} {W : Type u_
2} {G : SimpleGraph V} {H : SimpleGraph W} [Subsingleton (V → W)], Subsingleton 
(G.Copy H)
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
-/
@[simp] lemma labelledCopyCount_of_isEmpty [IsEmpty W] (G : SimpleGraph V) (H : SimpleGraph W) :
    G.labelledCopyCount H = 1 := by
  convert! Fintype.card_unique
  exact { default := ⟨default, isEmptyElim⟩, uniq := fun _ ↦ Subsingleton.elim _ _ }
/-
**SimpleGraph.labelledCopyCount_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：∀ {V : Type u_1} {W : Type u_2} {G : SimpleGraph V} {H : SimpleGraph W} [i
nst : Fintype V] [inst_1 : Fintype W],   G.labelledCopyCount H = 0 ↔ H.Free G
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma labelledCopyCount_eq_zero : G.labelledCopyCount H = 0 ↔ H.Free G := by
  simp [labelledCopyCount, Fintype.card_eq_zero_iff]
/-
**SimpleGraph.labelledCopyCount_pos** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：∀ {V : Type u_1} {W : Type u_2} {G : SimpleGraph V} {H : SimpleGraph W} [i
nst : Fintype V] [inst_1 : Fintype W],   0 < G.labelledCopyCount H ↔ H.IsContain
ed G
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma labelledCopyCount_pos : 0 < G.labelledCopyCount H ↔ H ⊑ G := by
  simp [labelledCopyCount, IsContained, Fintype.card_pos_iff]

end LabelledCopyCount

section CopyCount
variable [Fintype V]

/-- `G.copyCount H` is the number of unlabelled copies of `H` in `G`, i.e. the number of subgraphs
of `G` isomorphic to `H`. See `SimpleGraph.labelledCopyCount` for the number of labelled copies. -/
/-
**SimpleGraph.copyCount** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：copyCount (G : SimpleGraph V) (H : SimpleGraph W) : Nat
参数：G : SimpleGraph V；H : SimpleGraph W。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`G.copyCount H` is the number of unlabelled copies of `H` in `G`, i.e. the numbe
r of subgraphs
of `G` isomorphic to `H`. See `SimpleGraph.labelledCopyCount` for the number of 
labelled copies.
-/
noncomputable def copyCount (G : SimpleGraph V) (H : SimpleGraph W) : ℕ := by
  classical exact #{G' : G.Subgraph | Nonempty (H ≃g G'.coe)}
/-
**SimpleGraph.copyCount_eq_card_image_copyToSubgraph** 是 Mathlib 中的一个引理，位于命名空间 `
SimpleGraph`。
形式化陈述：copyCount_eq_card_image_copyToSubgraph [Fintype {f : H ->g G // Injective 
f}] [DecidableEq G.Subgraph] : copyCount G H = #((Finset.univ : Finset (H.Copy G
)).image Copy.toSubgraph)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.copyCount.eq_1`：∀ {V : Type u_1} {W : Type u_2} [inst : Fint
ype V] (G : SimpleGraph V) (H : SimpleGraph W),   G.copyCount H = {G' | Nonempty
 (H ≃g G'.coe)}.…
· 使用定理 `Finset.coe_injective`：coe_injective {α} : Injective ((↑) : Finset α -> S
et α)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.coe_filter`：∀ {α : Type u_1} (p : α → Prop) [inst : DecidablePred
 p] (s : Finset α), ↑(Finset.filter p s) = {x | x ∈ s ∧ p x}
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Finset.coe_univ`：coe_univ : ↑(univ : Finset α) = (Set.univ : Set α)
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.Copy.range_toSubgraph`：∀ {α : Type u_4} {β : Type u_5} {A : 
SimpleGraph α} {B : SimpleGraph β},   Set.range SimpleGraph.Copy.toSubgraph = {B
' | Nonempty (A ≃g B'.c…
-/
lemma copyCount_eq_card_image_copyToSubgraph [Fintype {f : H →g G // Injective f}]
    [DecidableEq G.Subgraph] :
    copyCount G H = #((Finset.univ : Finset (H.Copy G)).image Copy.toSubgraph) := by
  rw [copyCount]
  congr
  refine Finset.coe_injective ?_
  simpa [-Copy.range_toSubgraph] using Copy.range_toSubgraph.symm
/-
**SimpleGraph.copyCount_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：∀ {V : Type u_1} {W : Type u_2} {G : SimpleGraph V} {H : SimpleGraph W} [i
nst : Fintype V], G.copyCount H = 0 ↔ H.Free G
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma copyCount_eq_zero : G.copyCount H = 0 ↔ H.Free G := by
  simp [copyCount, Free, -nonempty_subtype, isContained_iff_exists_iso_subgraph,
    filter_eq_empty_iff]
/-
**SimpleGraph.copyCount_pos** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：∀ {V : Type u_1} {W : Type u_2} {G : SimpleGraph V} {H : SimpleGraph W} [i
nst : Fintype V],   0 < G.copyCount H ↔ H.IsContained G
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma copyCount_pos : 0 < G.copyCount H ↔ H ⊑ G := by
  simp [copyCount, -nonempty_subtype, isContained_iff_exists_iso_subgraph, card_pos,
    filter_nonempty_iff]

/-- There's at least as many labelled copies of `H` in `G` than unlabelled ones. -/
/-
**SimpleGraph.copyCount_le_labelledCopyCount** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGr
aph`。
形式化陈述：copyCount_le_labelledCopyCount [Fintype W] : G.copyCount H <= G.labelledCo
pyCount H
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SimpleGraph.copyCount_eq_card_image_copyToSubgraph`：copyCount_eq_card_im
age_copyToSubgraph [Fintype {f : H ->g G // Injective f}] [DecidableEq G.Subgrap
h] : copyCount G H = #((Finset.univ : Fi…
· 使用定理 `Finset.card_image_le`：card_image_le [DecidableEq β] : #(s.image f) <= #s

--- 原说明 ---
There's at least as many labelled copies of `H` in `G` than unlabelled ones.
-/
lemma copyCount_le_labelledCopyCount [Fintype W] : G.copyCount H ≤ G.labelledCopyCount H := by
  classical rw [copyCount_eq_card_image_copyToSubgraph]; exact card_image_le
/-
**SimpleGraph.copyCount_bot** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：∀ {V : Type u_1} [inst : Fintype V] (G : SimpleGraph V), G.copyCount ⊥ = 1
参数：G : SimpleGraph V。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.copyCount.eq_1`：∀ {V : Type u_1} {W : Type u_2} [inst : Fint
ype V] (G : SimpleGraph V) (H : SimpleGraph W),   G.copyCount H = {G' | Nonempty
 (H ≃g G'.coe)}.…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `trivial`：True
· 使用定理 `Equiv.Set.univ_symm_apply`：∀ (α : Type u_3) (a : α), (Equiv.Set.univ α).
symm a = ⟨a, trivial⟩
· 使用定理 `SimpleGraph.Subgraph.coe_adj`：∀ {V : Type u} {G : SimpleGraph V} (G' : G
.Subgraph) (v w : ↑G'.verts), G'.coe.Adj v w = G'.Adj ↑v ↑w
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `SimpleGraph.Subgraph.ext`：∀ {V : Type u} {G : SimpleGraph V} {x y : G.Su
bgraph}, x.verts = y.verts → x.Adj = y.Adj → x = y
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `set_fintype_card_eq_univ_iff`：set_fintype_card_eq_univ_iff [Fintype α] (
s : Set α) [Fintype s] : Fintype.card s = Fintype.card α ↔ s = Set.univ
· 使用定理 `Fintype.card_congr`：card_congr {α β} [Fintype α] [Fintype β] (f : α ≃ β)
 : card α = card β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SimpleGraph.Subgraph.edge_vert`：∀ {V : Type u} {G : SimpleGraph V} (self
 : G.Subgraph) {v w : V}, self.Adj v w → v ∈ self.verts
· 使用定理 `SimpleGraph.Subgraph.Adj.symm`：∀ {V : Type u} {G : SimpleGraph V} {G' : 
G.Subgraph} {u v : V}, G'.Adj u v → G'.Adj v u
· 使用定理 `RelIso.map_rel_iff`：map_rel_iff (f : r ≃r s) {a b} : s (f a) (f b) ↔ r a
 b
· 使用定理 `SimpleGraph.Subgraph.Adj.coe`：∀ {V : Type u} {G : SimpleGraph V} {H : G.
Subgraph} {u v : V} (h : H.Adj u v), H.coe.Adj ⟨u, ⋯⟩ ⟨v, ⋯⟩
· 使用定理 `Finset.card_singleton`：card_singleton (a : α) : #{a} = 1
-/
@[simp] lemma copyCount_bot (G : SimpleGraph V) : copyCount G (⊥ : SimpleGraph V) = 1 := by
  classical
  rw [copyCount]
  convert!
    card_singleton (α := G.Subgraph)
      { verts := .univ
        Adj := ⊥
        adj_sub := False.elim
        edge_vert := False.elim }
  simp only [eq_singleton_iff_unique_mem, mem_filter_univ, Nonempty.forall]
  refine ⟨⟨⟨(Equiv.Set.univ _).symm, by simp⟩⟩, fun H' e ↦
    Subgraph.ext ((set_fintype_card_eq_univ_iff _).1 <| Fintype.card_congr e.toEquiv.symm) ?_⟩
  ext a b
  simp only [Prop.bot_eq_false, Pi.bot_apply, iff_false]
  exact fun hab ↦ e.symm.map_rel_iff.2 hab.coe
/-
**SimpleGraph.copyCount_of_isEmpty** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：∀ {V : Type u_1} {W : Type u_2} [inst : Fintype V] [IsEmpty W] (G : Simple
Graph V) (H : SimpleGraph W),   G.copyCount H = 1
参数：G : SimpleGraph V；H : SimpleGraph W。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `Finite.of_subsingleton`：Finite.of_subsingleton [Subsingleton α] (s : Set
 α) : s.Finite
· 使用定理 `IsEmpty.instSubsingleton`：∀ {α : Sort u} [IsEmpty α], Subsingleton α
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用引理 `SimpleGraph.copyCount_le_labelledCopyCount`：copyCount_le_labelledCopyCou
nt [Fintype W] : G.copyCount H <= G.labelledCopyCount H
· 使用定理 `SimpleGraph.labelledCopyCount_of_isEmpty`：∀ {V : Type u_1} {W : Type u_2
} [inst : Fintype V] [inst_1 : Fintype W] [IsEmpty W] (G : SimpleGraph V)   (H :
 SimpleGraph W), G.labelledCop…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SimpleGraph.copyCount_pos`：∀ {V : Type u_1} {W : Type u_2} {G : SimpleGr
aph V} {H : SimpleGraph W} [inst : Fintype V],   0 < G.copyCount H ↔ H.IsContain
ed G
· 使用定理 `SimpleGraph.IsContained.of_isEmpty`：∀ {α : Type u_4} {β : Type u_5} {A :
 SimpleGraph α} {B : SimpleGraph β} [IsEmpty α], A.IsContained B
-/
@[simp] lemma copyCount_of_isEmpty [IsEmpty W] (G : SimpleGraph V) (H : SimpleGraph W) :
    G.copyCount H = 1 := by
  cases nonempty_fintype W
  exact (copyCount_le_labelledCopyCount.trans_eq <| labelledCopyCount_of_isEmpty ..).antisymm <|
    copyCount_pos.2 <| .of_isEmpty

end CopyCount

/-!
#### Induced copies

TODO

### Killing a subgraph

An important aspect of graph containment is that we can remove not too many edges from a graph `H`
to get a graph `H'` that doesn't contain `G`.

#### Killing not necessarily induced copies

`SimpleGraph.killCopies G H` is a subgraph of `G` where an edge was removed from each copy of `H` in
`G`. By construction, it doesn't contain `H` and has at most the number of copies of `H` edges less
than `G`.
-/

set_option backward.privateInPublic true in
/-
**SimpleGraph.aux** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
#### Induced copies

TODO

### Killing a subgraph

An important aspect of graph containment is that we can remove not too many edge
s from a graph `H`
to get a graph `H'` that doesn't contain `G`.

#### Killing not necessarily induced copies

`SimpleGraph.killCopies G H` is a subgraph of `G` where an edge was removed from
 each copy of `H` in
`G`. By construction, it doesn't contain `H` and has at most the number of copie
s of `H` edges less
than `G`.
-/
private lemma aux (hH : H ≠ ⊥) {G' : G.Subgraph} :
    Nonempty (H ≃g G'.coe) → G'.edgeSet.Nonempty := by
  obtain ⟨e, he⟩ := edgeSet_nonempty.2 hH
  rw [← Subgraph.image_coe_edgeSet_coe]
  exact fun ⟨f⟩ ↦ Set.Nonempty.image _ ⟨_, f.map_mem_edgeSet_iff.2 he⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- `G.killCopies H` is a subgraph of `G` where an *arbitrary* edge was removed from each copy of
`H` in `G`. By construction, it doesn't contain `H` (unless `H` had no edges) and has at most the
number of copies of `H` edges less than `G`. See `free_killCopies` and
`le_card_edgeFinset_killCopies` for these two properties. -/
noncomputable irreducible_def killCopies (G : SimpleGraph V) (H : SimpleGraph W) :
    SimpleGraph V := by
  classical exact
  if hH : H = ⊥ then G
  else G.deleteEdges <| ⋃ (G' : G.Subgraph) (hG' : Nonempty (H ≃g G'.coe)), {(aux hH hG').some}

/-- Removing an edge from `G` for each subgraph isomorphic to `H` results in a subgraph of `G`. -/
/-
**SimpleGraph.killCopies_le_left** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：killCopies_le_left : G.killCopies H <= G
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.Combinatorics.SimpleGraph.Copy.0.SimpleGraph.aux`：∀ {V 
: Type u_1} {W : Type u_2} {G : SimpleGraph V} {H : SimpleGraph W},   H ≠ ⊥ → ∀ 
{G' : G.Subgraph}, Nonempty (H ≃g G'.coe) → G'.edgeSet.…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.killCopies_def`：∀ {V : Type u_7} {W : Type u_8} (G : SimpleG
raph V) (H : SimpleGraph W),   G.killCopies H = if hH : H = ⊥ then G else G.dele
teEdges (⋃ G', ⋃…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用引理 `SimpleGraph.deleteEdges_le`：deleteEdges_le (s : Set (Sym2 V)) : G.delete
Edges s <= G

--- 原说明 ---
Removing an edge from `G` for each subgraph isomorphic to `H` results in a subgr
aph of `G`.
-/
lemma killCopies_le_left : G.killCopies H ≤ G := by
  rw [killCopies]; split_ifs; exacts [le_rfl, deleteEdges_le _]
/-
**SimpleGraph.killCopies_bot** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：∀ {V : Type u_1} {W : Type u_2} (G : SimpleGraph V), G.killCopies ⊥ = G
参数：G : SimpleGraph V。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.Combinatorics.SimpleGraph.Copy.0.SimpleGraph.aux`：∀ {V 
: Type u_1} {W : Type u_2} {G : SimpleGraph V} {H : SimpleGraph W},   H ≠ ⊥ → ∀ 
{G' : G.Subgraph}, Nonempty (H ≃g G'.coe) → G'.edgeSet.…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.killCopies_def`：∀ {V : Type u_7} {W : Type u_8} (G : SimpleG
raph V) (H : SimpleGraph W),   G.killCopies H = if hH : H = ⊥ then G else G.dele
teEdges (⋃ G', ⋃…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
-/
@[simp] lemma killCopies_bot (G : SimpleGraph V) : G.killCopies (⊥ : SimpleGraph W) = G := by
  rw [killCopies]; exact dif_pos rfl
/-
**SimpleGraph.killCopies_of_ne_bot** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma killCopies_of_ne_bot (hH : H ≠ ⊥) (G : SimpleGraph V) :
    G.killCopies H =
      G.deleteEdges (⋃ (G' : G.Subgraph) (hG' : Nonempty (H ≃g G'.coe)), {(aux hH hG').some}) := by
  rw [killCopies]; exact dif_neg hH

/-- `G.killCopies H` has no effect on `G` if and only if `G` already contained no copies of `H`. See
`Free.killCopies_eq_left` for the reverse implication with no assumption on `H`. -/
/-
**SimpleGraph.killCopies_eq_left** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：killCopies_eq_left (hH : H != ⊥) : G.killCopies H = G ↔ H.Free G
参数：hH : H != ⊥。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.Combinatorics.SimpleGraph.Copy.0.SimpleGraph.aux`：∀ {V 
: Type u_1} {W : Type u_2} {G : SimpleGraph V} {H : SimpleGraph W},   H ≠ ⊥ → ∀ 
{G' : G.Subgraph}, Nonempty (H ≃g G'.coe) → G'.edgeSet.…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `_private.Mathlib.Combinatorics.SimpleGraph.Copy.0.SimpleGraph.killCopies
_of_ne_bot`：∀ {V : Type u_1} {W : Type u_2} {H : SimpleGraph W} (hH : H ≠ ⊥) (G 
: SimpleGraph V),   G.killCopies H = G.deleteEdges (⋃ G', ⋃ (hG' : Nonem…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `SimpleGraph.Subgraph.edgeSet_subset`：edgeSet_subset (G' : Subgraph G) : 
G'.edgeSet subseteq G.edgeSet
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose

--- 原说明 ---
`G.killCopies H` has no effect on `G` if and only if `G` already contained no co
pies of `H`. See
`Free.killCopies_eq_left` for the reverse implication with no assumption on `H`.
-/
lemma killCopies_eq_left (hH : H ≠ ⊥) : G.killCopies H = G ↔ H.Free G := by
  simp only [killCopies_of_ne_bot hH, Set.disjoint_left, isContained_iff_exists_iso_subgraph,
    @forall_comm _ G.Subgraph, deleteEdges_eq_self, Set.mem_iUnion,
    not_exists, not_nonempty_iff, Nonempty.forall, Free]
  exact forall_congr' fun G' ↦ ⟨fun h ↦ ⟨fun f ↦ h _
    (Subgraph.edgeSet_subset _ <| (aux hH ⟨f⟩).choose_spec) f rfl⟩, fun h _ _ ↦ h.elim⟩
/-
**SimpleGraph.Free.killCopies_eq_left** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Fre
e`。
形式化陈述：∀ {V : Type u_1} {W : Type u_2} {G : SimpleGraph V} {H : SimpleGraph W}, H
.Free G → G.killCopies H = G
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `SimpleGraph.killCopies_bot`：∀ {V : Type u_1} {W : Type u_2} (G : SimpleG
raph V), G.killCopies ⊥ = G
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `SimpleGraph.killCopies_eq_left`：killCopies_eq_left (hH : H != ⊥) : G.kil
lCopies H = G ↔ H.Free G
-/
protected lemma Free.killCopies_eq_left (hHG : H.Free G) : G.killCopies H = G := by
  obtain rfl | hH := eq_or_ne H ⊥
  · exact killCopies_bot _
  · exact (killCopies_eq_left hH).2 hHG

set_option backward.isDefEq.respectTransparency false in
/-- Removing an edge from `G` for each subgraph isomorphic to `H` results in a graph that doesn't
contain `H`. -/
/-
**SimpleGraph.free_killCopies** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：free_killCopies (hH : H != ⊥) : H.Free (G.killCopies H)
参数：hH : H != ⊥。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.Combinatorics.SimpleGraph.Copy.0.SimpleGraph.aux`：∀ {V 
: Type u_1} {W : Type u_2} {G : SimpleGraph V} {H : SimpleGraph W},   H ≠ ⊥ → ∀ 
{G' : G.Subgraph}, Nonempty (H ≃g G'.coe) → G'.edgeSet.…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.Combinatorics.SimpleGraph.Copy.0.SimpleGraph.killCopies
_of_ne_bot`：∀ {V : Type u_1} {W : Type u_2} {H : SimpleGraph W} (hH : H ≠ ⊥) (G 
: SimpleGraph V),   G.killCopies H = G.deleteEdges (⋃ G', ⋃ (hG' : Nonem…
· 使用定理 `SimpleGraph.deleteEdges.eq_1`：∀ {V : Type u_1} (G : SimpleGraph V) (s : 
Set (Sym2 V)), G.deleteEdges s = G \ SimpleGraph.fromEdgeSet s
· 使用定理 `SimpleGraph.Free.eq_1`：∀ {α : Type u_4} {β : Type u_5} (A : SimpleGraph 
α) (B : SimpleGraph β), A.Free B = ¬A.IsContained B
· 使用定理 `SimpleGraph.isContained_iff_exists_iso_subgraph`：isContained_iff_exists_
iso_subgraph : A ⊑ B ↔ exists B' : B.Subgraph, Nonempty (A ≃g B'.coe) where mp
· 使用定理 `sdiff_le`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] {a b :
 α}, a \ b ≤ a
· 使用定理 `SimpleGraph.Subgraph.edgeSet_map`：∀ {V : Type u} {W : Type v} {G : Simpl
eGraph V} {G' : SimpleGraph W} (f : G →g G') (H : G.Subgraph),   (SimpleGraph.Su
bgraph.map f H).edgeSe…
· 使用定理 `Set.Nonempty.image`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {s : Set
 α}, s.Nonempty → (f '' s).Nonempty
· 使用定理 `Set.Nonempty.some_mem`：∀ {α : Type u} {s : Set α} (h : s.Nonempty), h.so
me ∈ s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SimpleGraph.Iso.map_mem_edgeSet_iff`：map_mem_edgeSet_iff {e : Sym2 V} : 
e.map f in G'.edgeSet ↔ e in G.edgeSet
· 使用定理 `SimpleGraph.Subgraph.edgeSet_subset`：edgeSet_subset (G' : Subgraph G) : 
G'.edgeSet subseteq G.edgeSet
· 使用定理 `SimpleGraph.Subgraph.edgeSet_coe`：∀ {V : Type u} {G : SimpleGraph V} {G'
 : G.Subgraph}, G'.coe.edgeSet = Sym2.map Subtype.val ⁻¹' G'.edgeSet
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SimpleGraph.edgeSet_sdiff`：edgeSet_sdiff : (G₁ \ G₂).edgeSet = G₁.edgeSe
t \ G₂.edgeSet
· 使用定理 `SimpleGraph.edgeSet_fromEdgeSet`：edgeSet_fromEdgeSet : (fromEdgeSet s).e
dgeSet = s \ Sym2.diagSet
· 使用定理 `SimpleGraph.edgeSet_sdiff_sdiff_isDiag`：edgeSet_sdiff_sdiff_isDiag (G : 
SimpleGraph V) (s : Set (Sym2 V)) : G.edgeSet \ (s \ Sym2.diagSet) = G.edgeSet \
 s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Sym2.map_map`：map_map {g : β -> γ} {f : α -> β} (x : Sym2 α) : map g (ma
p f x) = map (g ∘ f) x
· 使用定理 `Set.mem_singleton_iff`：mem_singleton_iff {a b : α} : a in ({b} : Set α) 
↔ a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Function.injective_id`：∀ {α : Sort u_1}, Function.Injective id
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
（共 33 条，此处仅展示前 30 条）

--- 原说明 ---
Removing an edge from `G` for each subgraph isomorphic to `H` results in a graph
 that doesn't
contain `H`.
-/
lemma free_killCopies (hH : H ≠ ⊥) : H.Free (G.killCopies H) := by
  rw [killCopies_of_ne_bot hH, deleteEdges, Free, isContained_iff_exists_iso_subgraph]
  rintro ⟨G', hHG'⟩
  have hG' : (G'.map <| .ofLE (sdiff_le : G \ _ ≤ G)).edgeSet.Nonempty := by
    rw [Subgraph.edgeSet_map]
    exact (aux hH hHG').image _
  set e := hG'.some with he
  have : e ∈ _ := hG'.some_mem
  clear_value e
  rw [← Subgraph.image_coe_edgeSet_coe] at this
  subst he
  obtain ⟨e, he₀, he₁⟩ := this
  let e' : Sym2 G'.verts := Sym2.map (Copy.isoSubgraphMap (.ofLE _ _ _) _).symm e
  have he' : e' ∈ G'.coe.edgeSet := (Iso.map_mem_edgeSet_iff _).2 he₀
  rw [Subgraph.edgeSet_coe] at he'
  have := Subgraph.edgeSet_subset _ he'
  simp only [edgeSet_sdiff, edgeSet_fromEdgeSet, edgeSet_sdiff_sdiff_isDiag, Set.mem_sdiff,
    Set.mem_iUnion, not_exists] at this
  refine this.2 (G'.map <| .ofLE sdiff_le) ⟨((Copy.ofLE _ _ _).isoSubgraphMap _).comp hHG'.some⟩ ?_
  rw [Sym2.map_map, Set.mem_singleton_iff, ← he₁]
  congr 1 with x
  exact congr_arg _ (Equiv.Set.image_symm_apply _ _ injective_id _ _)

variable [Fintype G.edgeSet]
/-
**SimpleGraph.killCopies.edgeSet.instFintype** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGr
aph.killCopies.edgeSet`。
形式化陈述：{V : Type u_1} →   {W : Type u_2} → {G : SimpleGraph V} → {H : SimpleGraph
 W} → [Fintype ↑G.edgeSet] → Fintype ↑(G.killCopies H).edgeSet
参数：G.killCopies H。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance killCopies.edgeSet.instFintype : Fintype (G.killCopies H).edgeSet :=
  .ofInjective (Set.inclusion <| edgeSet_mono killCopies_le_left) <| Set.inclusion_injective _

/-- Removing an edge from `H` for each subgraph isomorphic to `G` means that the number of edges
we've removed is at most the number of copies of `G` in `H`. -/
/-
**SimpleGraph.le_card_edgeFinset_killCopies** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGra
ph`。
形式化陈述：le_card_edgeFinset_killCopies [Fintype V] : #G.edgeFinset - G.copyCount H 
<= #(G.killCopies H).edgeFinset
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Fintype.card_congr'`：card_congr' {α β} [Fintype α] [Fintype β] (h : α = 
β) : card α = card β
· 使用定理 `SimpleGraph.killCopies_bot`：∀ {V : Type u_1} {W : Type u_2} (G : SimpleG
raph V), G.killCopies ⊥ = G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `_private.Mathlib.Combinatorics.SimpleGraph.Copy.0.SimpleGraph.aux`：∀ {V 
: Type u_1} {W : Type u_2} {G : SimpleGraph V} {H : SimpleGraph W},   H ≠ ⊥ → ∀ 
{G' : G.Subgraph}, Nonempty (H ≃g G'.coe) → G'.edgeSet.…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Set.toFinset_card`：toFinset_card {α : Type*} (s : Set α) [Fintype s] : s
.toFinset.card = Fintype.card s
· 使用定理 `SimpleGraph.edgeFinset.eq_1`：∀ {V : Type u_1} (G : SimpleGraph V) [inst 
: Fintype ↑G.edgeSet], G.edgeFinset = G.edgeSet.toFinset
· 使用定理 `SimpleGraph.copyCount.eq_1`：∀ {V : Type u_1} {W : Type u_2} [inst : Fint
ype V] (G : SimpleGraph V) (H : SimpleGraph W),   G.copyCount H = {G' | Nonempty
 (H ≃g G'.coe)}.…
· 使用定理 `Finset.card_subtype`：card_subtype (p : α -> Prop) [DecidablePred p] (s :
 Finset α) : #(s.subtype p) = #(s.filter p)
· 使用定理 `Finset.subtype_univ`：∀ {α : Type u_1} [inst : Fintype α] (p : α → Prop) 
[inst_1 : DecidablePred p] [inst_2 : Fintype { a // p a }],   Finset.subtype p F
inset.uni…
· 使用定理 `Finset.card_univ`：Finset.card_univ [Fintype α] : #(univ : Finset α) = Fi
ntype.card α
· 使用定理 `Nat.sub_le_sub_left`：∀ {n m : ℕ}, n ≤ m → ∀ (k : ℕ), k - m ≤ k - n
· 使用定理 `Finset.card_image_le`：card_image_le [DecidableEq β] : #(s.image f) <= #s
· 使用定理 `Set.toFinset_range`：toFinset_range [DecidableEq α] [Fintype β] (f : β ->
 α) [Fintype (Set.range f)] : (Set.range f).toFinset = Finset.univ.image f
· 使用定理 `Finset.le_card_sdiff`：le_card_sdiff (s t : Finset α) : #t - #s <= #(t \ 
s)
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `Sym2.inductionOn`：∀ {α : Type u_1} {f : Sym2 α → Prop} (i : Sym2 α), (∀ 
(x y : α), f s(x, y)) → f i
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
（共 37 条，此处仅展示前 30 条）

--- 原说明 ---
Removing an edge from `H` for each subgraph isomorphic to `G` means that the num
ber of edges
we've removed is at most the number of copies of `G` in `H`.
-/
lemma le_card_edgeFinset_killCopies [Fintype V] :
    #G.edgeFinset - G.copyCount H ≤ #(G.killCopies H).edgeFinset := by
  classical
  obtain rfl | hH := eq_or_ne H ⊥
  · simp [← card_edgeSet]
  let f (G' : {G' : G.Subgraph // Nonempty (H ≃g G'.coe)}) := (aux hH G'.2).some
  calc
    _ = #G.edgeFinset - card {G' : G.Subgraph // Nonempty (H ≃g G'.coe)} := ?_
    _ ≤ #G.edgeFinset - #(univ.image f) := Nat.sub_le_sub_left card_image_le _
    _ = #G.edgeFinset - #(Set.range f).toFinset := by rw [Set.toFinset_range]
    _ ≤ #(G.edgeFinset \ (Set.range f).toFinset) := le_card_sdiff ..
    _ = #(G.killCopies H).edgeFinset := ?_
  · simp only [edgeFinset, Set.toFinset_card]
    rw [← Set.toFinset_card, ← edgeFinset, copyCount, ← card_subtype, subtype_univ, card_univ]
  congr 1
  ext e
  induction e using Sym2.inductionOn with | hf v w
  simp [mem_edgeSet, killCopies_of_ne_bot hH, f, eq_comm]

/-- Removing an edge from `H` for each subgraph isomorphic to `G` means that the number of edges
we've removed is at most the number of copies of `G` in `H`. -/
/-
**SimpleGraph.le_card_edgeFinset_killCopies_add_copyCount** 是 Mathlib 中的一个引理，位于命
名空间 `SimpleGraph`。
形式化陈述：le_card_edgeFinset_killCopies_add_copyCount [Fintype V] : #G.edgeFinset <=
 #(G.killCopies H).edgeFinset + G.copyCount H
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `tsub_le_iff_right`：tsub_le_iff_right [LE α] [Add α] [Sub α] [OrderedSub 
α] {a b c : α} : a - b <= c ↔ a <= c + b
· 使用引理 `SimpleGraph.le_card_edgeFinset_killCopies`：le_card_edgeFinset_killCopies
 [Fintype V] : #G.edgeFinset - G.copyCount H <= #(G.killCopies H).edgeFinset

--- 原说明 ---
Removing an edge from `H` for each subgraph isomorphic to `G` means that the num
ber of edges
we've removed is at most the number of copies of `G` in `H`.
-/
lemma le_card_edgeFinset_killCopies_add_copyCount [Fintype V] :
    #G.edgeFinset ≤ #(G.killCopies H).edgeFinset + G.copyCount H :=
  tsub_le_iff_right.1 le_card_edgeFinset_killCopies

/-!
#### Killing induced copies

TODO
-/

end SimpleGraph

