/-
Copyright (c) 2024 Rida Hamadani. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rida Hamadani
-/
module

public import Mathlib.Combinatorics.Digraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic

/-!

# Graph Orientation

This module introduces conversion operations between `Digraph`s and `SimpleGraph`s, by forgetting
the edge orientations of `Digraph`.

## Main Definitions

- `Digraph.toSimpleGraphInclusive`: Converts a `Digraph` to a `SimpleGraph` by creating an
  undirected edge if either orientation exists in the digraph.
- `Digraph.toSimpleGraphStrict`: Converts a `Digraph` to a `SimpleGraph` by creating an undirected
  edge only if both orientations exist in the digraph.

## TODO

- Show that there is an isomorphism between loopless complete digraphs and oriented graphs.
- Define more ways to orient a `SimpleGraph`.
- Provide lemmas on how `toSimpleGraphInclusive` and `toSimpleGraphStrict` relate to other lattice
  structures on `SimpleGraph`s and `Digraph`s.

## Tags

digraph, simple graph, oriented graphs
-/

@[expose] public section

variable {V : Type*}

namespace Digraph

section toSimpleGraph

/-! ### Orientation-forgetting maps on digraphs -/

/--
Orientation-forgetting map from `Digraph` to `SimpleGraph` that gives an unoriented edge if
either orientation is present.
-/
/-
**Digraph.toSimpleGraphInclusive** 是 Mathlib 中的一个定义，位于命名空间 `Digraph`。
形式化陈述：toSimpleGraphInclusive (G : Digraph V) : SimpleGraph V
参数：G : Digraph V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Orientation-forgetting map from `Digraph` to `SimpleGraph` that gives an unorien
ted edge if
either orientation is present.
-/
def toSimpleGraphInclusive (G : Digraph V) : SimpleGraph V := SimpleGraph.fromRel G.Adj

/--
Orientation-forgetting map from `Digraph` to `SimpleGraph` that gives an unoriented edge if
both orientations are present.
-/
/-
**Digraph.toSimpleGraphStrict** 是 Mathlib 中的一个定义，位于命名空间 `Digraph`。
形式化陈述：toSimpleGraphStrict (G : Digraph V) : SimpleGraph V where Adj v w
参数：G : Digraph V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Orientation-forgetting map from `Digraph` to `SimpleGraph` that gives an unorien
ted edge if
both orientations are present.
-/
def toSimpleGraphStrict (G : Digraph V) : SimpleGraph V where
  Adj v w := v ≠ w ∧ G.Adj v w ∧ G.Adj w v
/-
**Digraph.toSimpleGraphStrict_subgraph_toSimpleGraphInclusive** 是 Mathlib 中的一个引理
，位于命名空间 `Digraph`。
形式化陈述：toSimpleGraphStrict_subgraph_toSimpleGraphInclusive (G : Digraph V) : G.to
SimpleGraphStrict <= G.toSimpleGraphInclusive
参数：G : Digraph V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma toSimpleGraphStrict_subgraph_toSimpleGraphInclusive (G : Digraph V) :
    G.toSimpleGraphStrict ≤ G.toSimpleGraphInclusive :=
  fun _ _ h ↦ ⟨h.1, Or.inl h.2.1⟩

@[gcongr, mono]
/-
**Digraph.toSimpleGraphInclusive_mono** 是 Mathlib 中的一个引理，位于命名空间 `Digraph`。
形式化陈述：toSimpleGraphInclusive_mono : Monotone (toSimpleGraphInclusive : _ -> Simp
leGraph V)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma toSimpleGraphInclusive_mono : Monotone (toSimpleGraphInclusive : _ → SimpleGraph V) :=
  fun _ _ h₁ _ _ h₂ ↦ ⟨h₂.1, h₂.2.imp (@h₁ _ _) (@h₁ _ _)⟩

@[gcongr, mono]
/-
**Digraph.toSimpleGraphStrict_mono** 是 Mathlib 中的一个引理，位于命名空间 `Digraph`。
形式化陈述：toSimpleGraphStrict_mono : Monotone (toSimpleGraphStrict : _ -> SimpleGrap
h V)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma toSimpleGraphStrict_mono : Monotone (toSimpleGraphStrict : _ → SimpleGraph V) :=
  fun _ _ h₁ _ _ h₂ ↦ ⟨h₂.1, h₁ h₂.2.1, h₁ h₂.2.2⟩

@[simp]
/-
**Digraph.toSimpleGraphInclusive_top** 是 Mathlib 中的一个引理，位于命名空间 `Digraph`。
形式化陈述：toSimpleGraphInclusive_top : (⊤ : Digraph V).toSimpleGraphInclusive = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.ext`：∀ {V : Type u} {x y : SimpleGraph V}, x.Adj = y.Adj → x
 = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `SimpleGraph.Adj.ne`：∀ {V : Type u} {G : SimpleGraph V} {a b : V}, G.Adj 
a b → a ≠ b
· 使用定理 `trivial`：True
-/
lemma toSimpleGraphInclusive_top : (⊤ : Digraph V).toSimpleGraphInclusive = ⊤ := by
  ext; exact ⟨And.left, fun h ↦ ⟨h.ne, Or.inl trivial⟩⟩

@[simp]
/-
**Digraph.toSimpleGraphStrict_top** 是 Mathlib 中的一个引理，位于命名空间 `Digraph`。
形式化陈述：toSimpleGraphStrict_top : (⊤ : Digraph V).toSimpleGraphStrict = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.ext`：∀ {V : Type u} {x y : SimpleGraph V}, x.Adj = y.Adj → x
 = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `SimpleGraph.Adj.ne`：∀ {V : Type u} {G : SimpleGraph V} {a b : V}, G.Adj 
a b → a ≠ b
· 使用定理 `trivial`：True
-/
lemma toSimpleGraphStrict_top : (⊤ : Digraph V).toSimpleGraphStrict = ⊤ := by
  ext; exact ⟨And.left, fun h ↦ ⟨h.ne, trivial, trivial⟩⟩

@[simp]
/-
**Digraph.toSimpleGraphInclusive_bot** 是 Mathlib 中的一个引理，位于命名空间 `Digraph`。
形式化陈述：toSimpleGraphInclusive_bot : (⊥ : Digraph V).toSimpleGraphInclusive = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.ext`：∀ {V : Type u} {x y : SimpleGraph V}, x.Adj = y.Adj → x
 = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
lemma toSimpleGraphInclusive_bot : (⊥ : Digraph V).toSimpleGraphInclusive = ⊥ := by
  ext; exact ⟨fun ⟨_, h⟩ ↦ by tauto, False.elim⟩

@[simp]
/-
**Digraph.toSimpleGraphStrict_bot** 是 Mathlib 中的一个引理，位于命名空间 `Digraph`。
形式化陈述：toSimpleGraphStrict_bot : (⊥ : Digraph V).toSimpleGraphStrict = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.ext`：∀ {V : Type u} {x y : SimpleGraph V}, x.Adj = y.Adj → x
 = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
lemma toSimpleGraphStrict_bot : (⊥ : Digraph V).toSimpleGraphStrict = ⊥ := by
  ext; exact ⟨fun ⟨_, h⟩ ↦ by tauto, False.elim⟩

end toSimpleGraph

end Digraph

