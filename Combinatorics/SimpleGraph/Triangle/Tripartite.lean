/-
Copyright (c) 2023 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Triangle.Basic

/-!
# Construct a tripartite graph from its triangles

This file contains the construction of a simple graph on `α ⊕ β ⊕ γ` from a list of triangles
`(a, b, c)` (with `a` in the first component, `b` in the second, `c` in the third).

We call
* `t : Finset (α × β × γ)` the set of *triangle indices* (its elements are not triangles within the
  graph but instead index them).
* *explicit* a triangle of the constructed graph coming from a triangle index.
* *accidental* a triangle of the constructed graph not coming from a triangle index.

The two important properties of this construction are:
* `SimpleGraph.TripartiteFromTriangles.ExplicitDisjoint`: Whether the explicit triangles are
  edge-disjoint.
* `SimpleGraph.TripartiteFromTriangles.NoAccidental`: Whether all triangles are explicit.

This construction shows up unrelatedly twice in the theory of Roth numbers:
* The lower bound of the Ruzsa-Szemerédi problem: From a set `s` in a finite abelian group `G` of
  odd order, we construct a tripartite graph on `G ⊕ G ⊕ G`. The triangle indices are
  `(x, x + a, x + 2 * a)` for `x` any element and `a ∈ s`. The explicit triangles are always
  edge-disjoint and there is no accidental triangle if `s` is 3AP-free.
* The proof of the corners theorem from the triangle removal lemma: For a set `s` in a finite
  abelian group `G`, we construct a tripartite graph on `G ⊕ G ⊕ G`, whose vertices correspond to
  the horizontal, vertical and diagonal lines in `G × G`. The explicit triangles are `(h, v, d)`
  where `h`, `v`, `d` are horizontal, vertical, diagonal lines that intersect in an element of `s`.
  The explicit triangles are always edge-disjoint and there is no accidental triangle if `s` is
  corner-free.
-/

@[expose] public section

open Finset Function Sum3

variable {α β γ 𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  {t : Finset (α × β × γ)}

namespace SimpleGraph
namespace TripartiteFromTriangles

/-- The underlying relation of the tripartite-from-triangles graph.

Two vertices are related iff there exists a triangle index containing them both. -/
/-
**SimpleGraph.TripartiteFromTriangles.Rel** 是 Mathlib 中的一个归纳类型，位于命名空间 `SimpleGra
ph.TripartiteFromTriangles`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → {γ : Type u_3} → Finset (α × β × γ) → α 
⊕ β ⊕ γ → α ⊕ β ⊕ γ → Prop
参数：α × β × γ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The underlying relation of the tripartite-from-triangles graph.

Two vertices are related iff there exists a triangle index containing them both.
-/
@[mk_iff] inductive Rel (t : Finset (α × β × γ)) : α ⊕ β ⊕ γ → α ⊕ β ⊕ γ → Prop
| in₀₁ ⦃a b c⦄ : (a, b, c) ∈ t → Rel t (in₀ a) (in₁ b)
| in₁₀ ⦃a b c⦄ : (a, b, c) ∈ t → Rel t (in₁ b) (in₀ a)
| in₀₂ ⦃a b c⦄ : (a, b, c) ∈ t → Rel t (in₀ a) (in₂ c)
| in₂₀ ⦃a b c⦄ : (a, b, c) ∈ t → Rel t (in₂ c) (in₀ a)
| in₁₂ ⦃a b c⦄ : (a, b, c) ∈ t → Rel t (in₁ b) (in₂ c)
| in₂₁ ⦃a b c⦄ : (a, b, c) ∈ t → Rel t (in₂ c) (in₁ b)

open Rel
/-
**SimpleGraph.TripartiteFromTriangles.rel_irrefl** 是 Mathlib 中的一个实例，位于命名空间 `Simp
leGraph.TripartiteFromTriangles`。
形式化陈述：rel_irrefl : Std.Irrefl (Rel t) where irrefl _x hx
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance rel_irrefl : Std.Irrefl (Rel t) where
  irrefl _x hx := nomatch hx
/-
**SimpleGraph.TripartiteFromTriangles.rel_symm** 是 Mathlib 中的一个实例，位于命名空间 `Simple
Graph.TripartiteFromTriangles`。
形式化陈述：rel_symm : Std.Symm (Rel t) where symm x y h
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
instance rel_symm : Std.Symm (Rel t) where
  symm x y h := by cases h <;> constructor <;> assumption

/-- The tripartite-from-triangles graph. Two vertices are related iff there exists a triangle index
containing them both. -/
/-
**SimpleGraph.TripartiteFromTriangles.graph** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGra
ph.TripartiteFromTriangles`。
形式化陈述：graph (t : Finset (α × β × γ)) : SimpleGraph (α oplus β oplus γ) where Adj
参数：t : Finset (α × β × γ)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The tripartite-from-triangles graph. Two vertices are related iff there exists a
 triangle index
containing them both.
-/
def graph (t : Finset (α × β × γ)) : SimpleGraph (α ⊕ β ⊕ γ) where
  Adj := Rel t
  symm := inferInstance
  loopless := inferInstance

variable {a a' : α} {b b' : β} {c c' : γ} {x : α × β × γ}

namespace Graph

/-
**SimpleGraph.TripartiteFromTriangles.Graph.not_in** 是 Mathlib 中的一个引理，位于命名空间 `Si
mpleGraph.TripartiteFromTriangles.Graph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma not_in₀₀ : ¬ (graph t).Adj (in₀ a) (in₀ a') := fun h ↦ nomatch h
/-
**SimpleGraph.TripartiteFromTriangles.Graph.not_in** 是 Mathlib 中的一个引理，位于命名空间 `Si
mpleGraph.TripartiteFromTriangles.Graph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma not_in₁₁ : ¬ (graph t).Adj (in₁ b) (in₁ b') := fun h ↦ nomatch h
/-
**SimpleGraph.TripartiteFromTriangles.Graph.not_in** 是 Mathlib 中的一个引理，位于命名空间 `Si
mpleGraph.TripartiteFromTriangles.Graph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma not_in₂₂ : ¬ (graph t).Adj (in₂ c) (in₂ c') := fun h ↦ nomatch h
/-
**SimpleGraph.TripartiteFromTriangles.Graph.in** 是 Mathlib 中的一个引理，位于命名空间 `Simple
Graph.TripartiteFromTriangles.Graph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma in₀₁_iff : (graph t).Adj (in₀ a) (in₁ b) ↔ ∃ c, (a, b, c) ∈ t :=
  ⟨by rintro ⟨⟩; exact ⟨_, ‹_›⟩, fun ⟨_, h⟩ ↦ in₀₁ h⟩
/-
**SimpleGraph.TripartiteFromTriangles.Graph.in** 是 Mathlib 中的一个引理，位于命名空间 `Simple
Graph.TripartiteFromTriangles.Graph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma in₁₀_iff : (graph t).Adj (in₁ b) (in₀ a) ↔ ∃ c, (a, b, c) ∈ t :=
  ⟨by rintro ⟨⟩; exact ⟨_, ‹_›⟩, fun ⟨_, h⟩ ↦ in₁₀ h⟩
/-
**SimpleGraph.TripartiteFromTriangles.Graph.in** 是 Mathlib 中的一个引理，位于命名空间 `Simple
Graph.TripartiteFromTriangles.Graph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma in₀₂_iff : (graph t).Adj (in₀ a) (in₂ c) ↔ ∃ b, (a, b, c) ∈ t :=
  ⟨by rintro ⟨⟩; exact ⟨_, ‹_›⟩, fun ⟨_, h⟩ ↦ in₀₂ h⟩
/-
**SimpleGraph.TripartiteFromTriangles.Graph.in** 是 Mathlib 中的一个引理，位于命名空间 `Simple
Graph.TripartiteFromTriangles.Graph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma in₂₀_iff : (graph t).Adj (in₂ c) (in₀ a) ↔ ∃ b, (a, b, c) ∈ t :=
  ⟨by rintro ⟨⟩; exact ⟨_, ‹_›⟩, fun ⟨_, h⟩ ↦ in₂₀ h⟩
/-
**SimpleGraph.TripartiteFromTriangles.Graph.in** 是 Mathlib 中的一个引理，位于命名空间 `Simple
Graph.TripartiteFromTriangles.Graph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma in₁₂_iff : (graph t).Adj (in₁ b) (in₂ c) ↔ ∃ a, (a, b, c) ∈ t :=
  ⟨by rintro ⟨⟩; exact ⟨_, ‹_›⟩, fun ⟨_, h⟩ ↦ in₁₂ h⟩
/-
**SimpleGraph.TripartiteFromTriangles.Graph.in** 是 Mathlib 中的一个引理，位于命名空间 `Simple
Graph.TripartiteFromTriangles.Graph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma in₂₁_iff : (graph t).Adj (in₂ c) (in₁ b) ↔ ∃ a, (a, b, c) ∈ t :=
  ⟨by rintro ⟨⟩; exact ⟨_, ‹_›⟩, fun ⟨_, h⟩ ↦ in₂₁ h⟩
/-
**SimpleGraph.TripartiteFromTriangles.Graph.in** 是 Mathlib 中的一个引理，位于命名空间 `Simple
Graph.TripartiteFromTriangles.Graph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma in₀₁_iff' :
    (graph t).Adj (in₀ a) (in₁ b) ↔ ∃ x : α × β × γ, x ∈ t ∧ x.1 = a ∧ x.2.1 = b where
  mp := by rintro ⟨⟩; exact ⟨_, ‹_›, by simp⟩
  mpr := by rintro ⟨⟨a, b, c⟩, h, rfl, rfl⟩; constructor; assumption
/-
**SimpleGraph.TripartiteFromTriangles.Graph.in** 是 Mathlib 中的一个引理，位于命名空间 `Simple
Graph.TripartiteFromTriangles.Graph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma in₁₀_iff' :
    (graph t).Adj (in₁ b) (in₀ a) ↔ ∃ x : α × β × γ, x ∈ t ∧ x.2.1 = b ∧ x.1 = a where
  mp := by rintro ⟨⟩; exact ⟨_, ‹_›, by simp⟩
  mpr := by rintro ⟨⟨a, b, c⟩, h, rfl, rfl⟩; constructor; assumption
/-
**SimpleGraph.TripartiteFromTriangles.Graph.in** 是 Mathlib 中的一个引理，位于命名空间 `Simple
Graph.TripartiteFromTriangles.Graph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma in₀₂_iff' :
    (graph t).Adj (in₀ a) (in₂ c) ↔ ∃ x : α × β × γ, x ∈ t ∧ x.1 = a ∧ x.2.2 = c where
  mp := by rintro ⟨⟩; exact ⟨_, ‹_›, by simp⟩
  mpr := by rintro ⟨⟨a, b, c⟩, h, rfl, rfl⟩; constructor; assumption
/-
**SimpleGraph.TripartiteFromTriangles.Graph.in** 是 Mathlib 中的一个引理，位于命名空间 `Simple
Graph.TripartiteFromTriangles.Graph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma in₂₀_iff' :
    (graph t).Adj (in₂ c) (in₀ a) ↔ ∃ x : α × β × γ, x ∈ t ∧ x.2.2 = c ∧ x.1 = a where
  mp := by rintro ⟨⟩; exact ⟨_, ‹_›, by simp⟩
  mpr := by rintro ⟨⟨a, b, c⟩, h, rfl, rfl⟩; constructor; assumption
/-
**SimpleGraph.TripartiteFromTriangles.Graph.in** 是 Mathlib 中的一个引理，位于命名空间 `Simple
Graph.TripartiteFromTriangles.Graph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma in₁₂_iff' :
    (graph t).Adj (in₁ b) (in₂ c) ↔ ∃ x : α × β × γ, x ∈ t ∧ x.2.1 = b ∧ x.2.2 = c where
  mp := by rintro ⟨⟩; exact ⟨_, ‹_›, by simp⟩
  mpr := by rintro ⟨⟨a, b, c⟩, h, rfl, rfl⟩; constructor; assumption
/-
**SimpleGraph.TripartiteFromTriangles.Graph.in** 是 Mathlib 中的一个引理，位于命名空间 `Simple
Graph.TripartiteFromTriangles.Graph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma in₂₁_iff' :
    (graph t).Adj (in₂ c) (in₁ b) ↔ ∃ x : α × β × γ, x ∈ t ∧ x.2.2 = c ∧ x.2.1 = b where
  mp := by rintro ⟨⟩; exact ⟨_, ‹_›, by simp⟩
  mpr := by rintro ⟨⟨a, b, c⟩, h, rfl, rfl⟩; constructor; assumption

end Graph

open Graph

/-- Predicate on the triangle indices for the explicit triangles to be edge-disjoint. -/
/-
**SimpleGraph.TripartiteFromTriangles.ExplicitDisjoint** 是 Mathlib 中的一个归纳类型，位于命名
空间 `SimpleGraph.TripartiteFromTriangles`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → {γ : Type u_3} → Finset (α × β × γ) → Pr
op
参数：α × β × γ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Predicate on the triangle indices for the explicit triangles to be edge-disjoint
.
-/
class ExplicitDisjoint (t : Finset (α × β × γ)) : Prop where
  inj₀ : ∀ ⦃a b c a'⦄, (a, b, c) ∈ t → (a', b, c) ∈ t → a = a'
  inj₁ : ∀ ⦃a b c b'⦄, (a, b, c) ∈ t → (a, b', c) ∈ t → b = b'
  inj₂ : ∀ ⦃a b c c'⦄, (a, b, c) ∈ t → (a, b, c') ∈ t → c = c'

/-- Predicate on the triangle indices for there to be no accidental triangle.

Note that we cheat a bit, since the exact translation of this informal description would have
`(a', b', c') ∈ t` as a conclusion rather than `a = a' ∨ b = b' ∨ c = c'`. Those conditions are
equivalent when the explicit triangles are edge-disjoint (which is the case we care about). -/
/-
**SimpleGraph.TripartiteFromTriangles.NoAccidental** 是 Mathlib 中的一个归纳类型，位于命名空间 `
SimpleGraph.TripartiteFromTriangles`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → {γ : Type u_3} → Finset (α × β × γ) → Pr
op
参数：α × β × γ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Predicate on the triangle indices for there to be no accidental triangle.

Note that we cheat a bit, since the exact translation of this informal descripti
on would have
`(a', b', c') ∈ t` as a conclusion rather than `a = a' ∨ b = b' ∨ c = c'`. Those
 conditions are
equivalent when the explicit triangles are edge-disjoint (which is the case we c
are about).
-/
class NoAccidental (t : Finset (α × β × γ)) : Prop where
  eq_or_eq_or_eq : ∀ ⦃a a' b b' c c'⦄, (a', b, c) ∈ t → (a, b', c) ∈ t → (a, b, c') ∈ t →
    a = a' ∨ b = b' ∨ c = c'

section DecidableEq
variable [DecidableEq α] [DecidableEq β] [DecidableEq γ]

/-
**SimpleGraph.TripartiteFromTriangles.graph.instDecidableRelAdj** 是 Mathlib 中的一个
定义，位于命名空间 `SimpleGraph.TripartiteFromTriangles.graph`。
形式化陈述：{α : Type u_1} →   {β : Type u_2} →     {γ : Type u_3} →       {t : Finset
 (α × β × γ)} →         [DecidableEq α] →           [DecidableEq β] → [Decidable
Eq γ] → DecidableRel (SimpleGraph.TripartiteFromTriangles.graph t).Adj
参数：α × β × γ；SimpleGraph.TripartiteFromTriangles.graph t。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.TripartiteFromTriangles.Graph.not_in₀₀`：∀ {α : Type u_1} {β 
: Type u_2} {γ : Type u_3} {t : Finset (α × β × γ)} {a a' : α},   ¬(SimpleGraph.
TripartiteFromTriangles.graph t).Adj (Su…
· 使用引理 `SimpleGraph.TripartiteFromTriangles.Graph.in₀₁_iff'`：in₀₁_iff' : (graph 
t).Adj (in₀ a) (in₁ b) ↔ exists x : α × β × γ, x in t ∧ x.1 = a ∧ x.2.1 = b wher
e mp
· 使用引理 `SimpleGraph.TripartiteFromTriangles.Graph.in₀₂_iff'`：in₀₂_iff' : (graph 
t).Adj (in₀ a) (in₂ c) ↔ exists x : α × β × γ, x in t ∧ x.1 = a ∧ x.2.2 = c wher
e mp
· 使用引理 `SimpleGraph.TripartiteFromTriangles.Graph.in₁₀_iff'`：in₁₀_iff' : (graph 
t).Adj (in₁ b) (in₀ a) ↔ exists x : α × β × γ, x in t ∧ x.2.1 = b ∧ x.1 = a wher
e mp
· 使用定理 `SimpleGraph.TripartiteFromTriangles.Graph.not_in₁₁`：∀ {α : Type u_1} {β 
: Type u_2} {γ : Type u_3} {t : Finset (α × β × γ)} {b b' : β},   ¬(SimpleGraph.
TripartiteFromTriangles.graph t).Adj (Su…
· 使用引理 `SimpleGraph.TripartiteFromTriangles.Graph.in₁₂_iff'`：in₁₂_iff' : (graph 
t).Adj (in₁ b) (in₂ c) ↔ exists x : α × β × γ, x in t ∧ x.2.1 = b ∧ x.2.2 = c wh
ere mp
· 使用引理 `SimpleGraph.TripartiteFromTriangles.Graph.in₂₀_iff'`：in₂₀_iff' : (graph 
t).Adj (in₂ c) (in₀ a) ↔ exists x : α × β × γ, x in t ∧ x.2.2 = c ∧ x.1 = a wher
e mp
· 使用引理 `SimpleGraph.TripartiteFromTriangles.Graph.in₂₁_iff'`：in₂₁_iff' : (graph 
t).Adj (in₂ c) (in₁ b) ↔ exists x : α × β × γ, x in t ∧ x.2.2 = c ∧ x.2.1 = b wh
ere mp
· 使用定理 `SimpleGraph.TripartiteFromTriangles.Graph.not_in₂₂`：∀ {α : Type u_1} {β 
: Type u_2} {γ : Type u_3} {t : Finset (α × β × γ)} {c c' : γ},   ¬(SimpleGraph.
TripartiteFromTriangles.graph t).Adj (Su…
-/
instance graph.instDecidableRelAdj : DecidableRel (graph t).Adj
  | in₀ _a, in₀ _a' => Decidable.isFalse not_in₀₀
  | in₀ _a, in₁ _b' => decidable_of_iff' _ in₀₁_iff'
  | in₀ _a, in₂ _c' => decidable_of_iff' _ in₀₂_iff'
  | in₁ _b, in₀ _a' => decidable_of_iff' _ in₁₀_iff'
  | in₁ _b, in₁ _b' => Decidable.isFalse not_in₁₁
  | in₁ _b, in₂ _b' => decidable_of_iff' _ in₁₂_iff'
  | in₂ _c, in₀ _a' => decidable_of_iff' _ in₂₀_iff'
  | in₂ _c, in₁ _b' => decidable_of_iff' _ in₂₁_iff'
  | in₂ _c, in₂ _b' => Decidable.isFalse not_in₂₂

/-- This lemma reorders the elements of a triangle in the tripartite graph. It turns a triangle
`{x, y, z}` into a triangle `{a, b, c}` where `a : α `, `b : β`, `c : γ`. -/
/-
**SimpleGraph.TripartiteFromTriangles.graph_triple** 是 Mathlib 中的一个引理，位于命名空间 `Si
mpleGraph.TripartiteFromTriangles`。
形式化陈述：graph_triple ⦃x y z⦄ : (graph t).Adj x y -> (graph t).Adj x z -> (graph t)
.Adj y z -> exists a b c, ({in₀ a, in₁ b, in₂ c} : Finset (α oplus β oplus γ)) =
 {x, y, z} ∧ (graph t).Adj (in₀ a) (in₁ b) ∧ (graph t).Adj (in₀ a) (in₂ c) ∧ (gr
aph t).Adj (in₁ b) (in₂ c)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b

--- 原说明 ---
This lemma reorders the elements of a triangle in the tripartite graph. It turns
 a triangle
`{x, y, z}` into a triangle `{a, b, c}` where `a : α `, `b : β`, `c : γ`.
-/
lemma graph_triple ⦃x y z⦄ :
    (graph t).Adj x y → (graph t).Adj x z → (graph t).Adj y z → ∃ a b c,
    ({in₀ a, in₁ b, in₂ c} : Finset (α ⊕ β ⊕ γ)) = {x, y, z} ∧ (graph t).Adj (in₀ a) (in₁ b) ∧
      (graph t).Adj (in₀ a) (in₂ c) ∧ (graph t).Adj (in₁ b) (in₂ c) := by
  rintro (_ | _ | _) (_ | _ | _) (_ | _ | _) <;>
    refine ⟨_, _, _, by ext; simp only [Finset.mem_insert, Finset.mem_singleton]; try tauto,
      ?_, ?_, ?_⟩ <;> constructor <;> assumption

/-- The map that turns a triangle index into an explicit triangle. -/
/-
**SimpleGraph.TripartiteFromTriangles.toTriangle** 是 Mathlib 中的一个定义，位于命名空间 `Simp
leGraph.TripartiteFromTriangles`。
形式化陈述：{α : Type u_1} →   {β : Type u_2} → {γ : Type u_3} → [DecidableEq α] → [De
cidableEq β] → [DecidableEq γ] → α × β × γ ↪ Finset (α ⊕ β ⊕ γ)
参数：α ⊕ β ⊕ γ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map that turns a triangle index into an explicit triangle.
-/
@[simps] def toTriangle : α × β × γ ↪ Finset (α ⊕ β ⊕ γ) where
  toFun x := {in₀ x.1, in₁ x.2.1, in₂ x.2.2}
  inj' := fun ⟨a, b, c⟩ ⟨a', b', c'⟩ ↦ by simpa only [Finset.Subset.antisymm_iff, Finset.subset_iff,
    mem_insert, mem_singleton, forall_eq_or_imp, forall_eq, Prod.mk_inj, or_false, false_or,
    in₀, in₁, in₂, Sum.inl.inj_iff, Sum.inr.inj_iff, reduceCtorEq] using And.left
/-
**SimpleGraph.TripartiteFromTriangles.toTriangle_is3Clique** 是 Mathlib 中的一个引理，位于
命名空间 `SimpleGraph.TripartiteFromTriangles`。
形式化陈述：toTriangle_is3Clique (hx : x in t) : (graph t).IsNClique 3 (toTriangle x)
参数：hx : x in t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.TripartiteFromTriangles.toTriangle_apply`：∀ {α : Type u_1} {
β : Type u_2} {γ : Type u_3} [inst : DecidableEq α] [inst_1 : DecidableEq β] [in
st_2 : DecidableEq γ]   (x : α × β × γ), S…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
-/
lemma toTriangle_is3Clique (hx : x ∈ t) : (graph t).IsNClique 3 (toTriangle x) := by
  simp only [toTriangle_apply, is3Clique_triple_iff, in₀₁_iff, in₀₂_iff, in₁₂_iff]
  exact ⟨⟨_, hx⟩, ⟨_, hx⟩, _, hx⟩
/-
**SimpleGraph.TripartiteFromTriangles.exists_mem_toTriangle** 是 Mathlib 中的一个引理，位
于命名空间 `SimpleGraph.TripartiteFromTriangles`。
形式化陈述：exists_mem_toTriangle {x y : α oplus β oplus γ} (hxy : (graph t).Adj x y) 
: exists z in t, x in toTriangle z ∧ y in toTriangle z
参数：hxy : (graph t).Adj x y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SimpleGraph.TripartiteFromTriangles.toTriangle_apply`：∀ {α : Type u_1} {
β : Type u_2} {γ : Type u_3} [inst : DecidableEq α] [inst_1 : DecidableEq β] [in
st_2 : DecidableEq γ]   (x : α × β × γ), S…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `Sum.inr.injEq`：∀ {α : Type u} {β : Type v} (val val_1 : β), (Sum.inr val
 = Sum.inr val_1) = (val = val_1)
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma exists_mem_toTriangle {x y : α ⊕ β ⊕ γ} (hxy : (graph t).Adj x y) :
    ∃ z ∈ t, x ∈ toTriangle z ∧ y ∈ toTriangle z := by cases hxy <;> exact ⟨_, ‹_›, by simp⟩

nonrec lemma is3Clique_iff [NoAccidental t] {s : Finset (α ⊕ β ⊕ γ)} :
    (graph t).IsNClique 3 s ↔ ∃ x, x ∈ t ∧ toTriangle x = s := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · rw [is3Clique_iff] at h
    obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := h
    obtain ⟨a, b, c, habc, hab, hac, hbc⟩ := graph_triple hxy hxz hyz
    refine ⟨(a, b, c), ?_, habc⟩
    obtain ⟨c', hc'⟩ := in₀₁_iff.1 hab
    obtain ⟨b', hb'⟩ := in₀₂_iff.1 hac
    obtain ⟨a', ha'⟩ := in₁₂_iff.1 hbc
    obtain rfl | rfl | rfl := NoAccidental.eq_or_eq_or_eq ha' hb' hc' <;> assumption
  · rintro ⟨x, hx, rfl⟩
    exact toTriangle_is3Clique hx
/-
**SimpleGraph.TripartiteFromTriangles.toTriangle_surjOn** 是 Mathlib 中的一个引理，位于命名空
间 `SimpleGraph.TripartiteFromTriangles`。
形式化陈述：toTriangle_surjOn [NoAccidental t] : (t : Set (α × β × γ)).SurjOn toTriang
le ((graph t).cliqueSet 3)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SimpleGraph.TripartiteFromTriangles.is3Clique_iff`：∀ {α : Type u_1} {β :
 Type u_2} {γ : Type u_3} {t : Finset (α × β × γ)} [inst : DecidableEq α] [inst_
1 : DecidableEq β]   [inst_2 : Decidabl…
-/
lemma toTriangle_surjOn [NoAccidental t] :
    (t : Set (α × β × γ)).SurjOn toTriangle ((graph t).cliqueSet 3) := fun _ ↦ is3Clique_iff.1

variable (t)
/-
**SimpleGraph.TripartiteFromTriangles.map_toTriangle_disjoint** 是 Mathlib 中的一个引理
，位于命名空间 `SimpleGraph.TripartiteFromTriangles`。
形式化陈述：map_toTriangle_disjoint [ExplicitDisjoint t] : (t.map toTriangle : Set (Fi
nset (α oplus β oplus γ))).Pairwise fun x y => (x inter y : Set (α oplus β oplus
 γ)).Subsingleton
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_map`：coe_map (f : α ↪ β) (s : Finset α) : (s.map f : Set β) =
 f '' s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `ne_of_apply_ne`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) {x y : α}, f
 x ≠ f y → x ≠ y
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `SimpleGraph.TripartiteFromTriangles.toTriangle_apply`：∀ {α : Type u_1} {
β : Type u_2} {γ : Type u_3} [inst : DecidableEq α] [inst_1 : DecidableEq β] [in
st_2 : DecidableEq γ]   (x : α × β × γ), S…
· 使用定理 `SimpleGraph.TripartiteFromTriangles.ExplicitDisjoint.inj₂`：∀ {α : Type u
_1} {β : Type u_2} {γ : Type u_3} {t : Finset (α × β × γ)}   [self : SimpleGraph
.TripartiteFromTriangles.ExplicitDisjoint t] ⦃a…
· 使用定理 `SimpleGraph.TripartiteFromTriangles.ExplicitDisjoint.inj₁`：∀ {α : Type u
_1} {β : Type u_2} {γ : Type u_3} {t : Finset (α × β × γ)}   [self : SimpleGraph
.TripartiteFromTriangles.ExplicitDisjoint t] ⦃a…
· 使用定理 `SimpleGraph.TripartiteFromTriangles.ExplicitDisjoint.inj₀`：∀ {α : Type u
_1} {β : Type u_2} {γ : Type u_3} {t : Finset (α × β × γ)}   [self : SimpleGraph
.TripartiteFromTriangles.ExplicitDisjoint t] ⦃a…
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `Sum.inl.injEq`：∀ {α : Type u} {β : Type v} (val val_1 : α), (Sum.inl val
 = Sum.inl val_1) = (val = val_1)
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Sum.inr.injEq`：∀ {α : Type u} {β : Type v} (val val_1 : β), (Sum.inr val
 = Sum.inr val_1) = (val = val_1)
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `not_true_eq_false`：(¬True) = False
（共 31 条，此处仅展示前 30 条）
-/
lemma map_toTriangle_disjoint [ExplicitDisjoint t] :
    (t.map toTriangle : Set (Finset (α ⊕ β ⊕ γ))).Pairwise
      fun x y ↦ (x ∩ y : Set (α ⊕ β ⊕ γ)).Subsingleton := by
  intro
  simp only [Finset.coe_map, Set.mem_image, Finset.mem_coe, Prod.exists, Ne,
    forall_exists_index, and_imp]
  rintro a b c habc rfl e x y z hxyz rfl h'
  have := ne_of_apply_ne _ h'
  simp only [Ne, Prod.mk_inj, not_and] at this
  simp only [toTriangle_apply, in₀, in₁, in₂, Set.mem_inter_iff, mem_insert, mem_singleton,
    mem_coe, and_imp, Sum.forall,
    Set.Subsingleton]
  suffices ¬ (a = x ∧ b = y) ∧ ¬ (a = x ∧ c = z) ∧ ¬ (b = y ∧ c = z) by aesop
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨rfl, rfl⟩
    exact this rfl rfl (ExplicitDisjoint.inj₂ habc hxyz)
  · rintro ⟨rfl, rfl⟩
    exact this rfl (ExplicitDisjoint.inj₁ habc hxyz) rfl
  · rintro ⟨rfl, rfl⟩
    exact this (ExplicitDisjoint.inj₀ habc hxyz) rfl rfl
/-
**SimpleGraph.TripartiteFromTriangles.cliqueSet_eq_image** 是 Mathlib 中的一个引理，位于命名
空间 `SimpleGraph.TripartiteFromTriangles`。
形式化陈述：cliqueSet_eq_image [NoAccidental t] : (graph t).cliqueSet 3 = toTriangle '
' t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `SimpleGraph.TripartiteFromTriangles.is3Clique_iff`：∀ {α : Type u_1} {β :
 Type u_2} {γ : Type u_3} {t : Finset (α × β × γ)} [inst : DecidableEq α] [inst_
1 : DecidableEq β]   [inst_2 : Decidabl…
-/
lemma cliqueSet_eq_image [NoAccidental t] : (graph t).cliqueSet 3 = toTriangle '' t := by
  ext; exact is3Clique_iff

section Fintype
variable [Fintype α] [Fintype β] [Fintype γ]

/-
**SimpleGraph.TripartiteFromTriangles.cliqueFinset_eq_image** 是 Mathlib 中的一个引理，位
于命名空间 `SimpleGraph.TripartiteFromTriangles`。
形式化陈述：cliqueFinset_eq_image [NoAccidental t] : (graph t).cliqueFinset 3 = t.imag
e toTriangle
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_injective`：coe_injective {α} : Injective ((↑) : Finset α -> S
et α)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.coe_cliqueFinset`：coe_cliqueFinset (n : Nat) : (G.cliqueFins
et n : Set (Finset α)) = G.cliqueSet n
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用引理 `SimpleGraph.TripartiteFromTriangles.cliqueSet_eq_image`：cliqueSet_eq_ima
ge [NoAccidental t] : (graph t).cliqueSet 3 = toTriangle '' t
-/
lemma cliqueFinset_eq_image [NoAccidental t] : (graph t).cliqueFinset 3 = t.image toTriangle :=
  coe_injective <| by push_cast; exact cliqueSet_eq_image _
/-
**SimpleGraph.TripartiteFromTriangles.cliqueFinset_eq_map** 是 Mathlib 中的一个引理，位于命
名空间 `SimpleGraph.TripartiteFromTriangles`。
形式化陈述：cliqueFinset_eq_map [NoAccidental t] : (graph t).cliqueFinset 3 = t.map to
Triangle
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SimpleGraph.TripartiteFromTriangles.cliqueFinset_eq_image`：cliqueFinset_
eq_image [NoAccidental t] : (graph t).cliqueFinset 3 = t.image toTriangle
· 使用定理 `Finset.map_eq_image`：map_eq_image (f : α ↪ β) (s : Finset α) : s.map f =
 s.image f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma cliqueFinset_eq_map [NoAccidental t] : (graph t).cliqueFinset 3 = t.map toTriangle := by
  simp [cliqueFinset_eq_image, map_eq_image]
/-
**SimpleGraph.TripartiteFromTriangles.card_triangles** 是 Mathlib 中的一个定理，位于命名空间 `
SimpleGraph.TripartiteFromTriangles`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} (t : Finset (α × β × γ)) [i
nst : DecidableEq α] [inst_1 : DecidableEq β]   [inst_2 : DecidableEq γ] [inst_3
 : Fintype α] [inst_4 : Fintype β] [inst_5 : Fintype γ]   [SimpleGraph.Tripartit
eFromTriangles.NoAccidental t],   ((SimpleGraph.TripartiteFromTriangles.graph t)
.cliqueFinset 3).card = t.card
参数：t : Finset (α × β × γ)；(SimpleGraph.TripartiteFromTriangles.graph t).cliqueFi
nset 3。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SimpleGraph.TripartiteFromTriangles.cliqueFinset_eq_map`：cliqueFinset_eq
_map [NoAccidental t] : (graph t).cliqueFinset 3 = t.map toTriangle
· 使用定理 `Finset.card_map`：card_map (f : α ↪ β) : #(s.map f) = #s
-/
@[simp] lemma card_triangles [NoAccidental t] : #((graph t).cliqueFinset 3) = #t := by
  rw [cliqueFinset_eq_map, card_map]
/-
**SimpleGraph.TripartiteFromTriangles.farFromTriangleFree** 是 Mathlib 中的一个引理，位于命
名空间 `SimpleGraph.TripartiteFromTriangles`。
形式化陈述：farFromTriangleFree [ExplicitDisjoint t] {ε : 𝕜} (ht : ε * ((Fintype.card 
α + Fintype.card β + Fintype.card γ) ^ 2 : Nat) <= #t) : (graph t).FarFromTriang
leFree ε
参数：ht : ε * ((Fintype.card α + Fintype.card β + Fintype.card γ) ^ 2 : Nat) <= #t
。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SimpleGraph.farFromTriangleFree_of_disjoint_triangles`：farFromTriangleFr
ee_of_disjoint_triangles (tris : Finset (Finset α)) (htris : tris subseteq G.cli
queFinset 3) (pd : (tris : Set (Finset α)).…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `Function.Embedding.injective`：∀ {α : Sort u_1} {β : Sort u_2} (f : α ↪ β
), Function.Injective ⇑f
· 使用定理 `Finset.map_subset_iff_subset_preimage`：map_subset_iff_subset_preimage {f
 : α ↪ β} {s : Finset α} {t : Finset β} : s.map f subseteq t ↔ s subseteq t.prei
mage f f.injective.injOn
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.TripartiteFromTriangles.toTriangle_apply`：∀ {α : Type u_1} {
β : Type u_2} {γ : Type u_3} [inst : DecidableEq α] [inst_1 : DecidableEq β] [in
st_2 : DecidableEq γ]   (x : α × β × γ), S…
· 使用引理 `SimpleGraph.TripartiteFromTriangles.toTriangle_is3Clique`：toTriangle_is3
Clique (hx : x in t) : (graph t).IsNClique 3 (toTriangle x)
· 使用引理 `SimpleGraph.TripartiteFromTriangles.map_toTriangle_disjoint`：map_toTrian
gle_disjoint [ExplicitDisjoint t] : (t.map toTriangle : Set (Finset (α oplus β o
plus γ))).Pairwise fun x y => (x inter y : Set (α…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Fintype.card_sum`：Fintype.card_sum [Fintype α] [Fintype β] : Fintype.car
d (α oplus β) = Fintype.card α + Fintype.card β
· 使用定理 `Nat.cast_pow`：∀ {α : Type u_1} [inst : Semiring α] (m n : ℕ), ↑(m ^ n) =
 ↑m ^ n
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Finset.card_map`：card_map (f : α ↪ β) : #(s.map f) = #s
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
-/
lemma farFromTriangleFree [ExplicitDisjoint t] {ε : 𝕜}
    (ht : ε * ((Fintype.card α + Fintype.card β + Fintype.card γ) ^ 2 : ℕ) ≤ #t) :
    (graph t).FarFromTriangleFree ε :=
  farFromTriangleFree_of_disjoint_triangles (t.map toTriangle)
    (map_subset_iff_subset_preimage.2 fun x hx ↦ by simpa using toTriangle_is3Clique hx)
    (map_toTriangle_disjoint t) <| by simpa [add_assoc] using ht

end Fintype
end DecidableEq

variable (t)

/-
**SimpleGraph.TripartiteFromTriangles.locallyLinear** 是 Mathlib 中的一个引理，位于命名空间 `S
impleGraph.TripartiteFromTriangles`。
形式化陈述：locallyLinear [ExplicitDisjoint t] [NoAccidental t] : (graph t).LocallyLin
ear
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SimpleGraph.TripartiteFromTriangles.cliqueSet_eq_image`：cliqueSet_eq_ima
ge [NoAccidental t] : (graph t).cliqueSet 3 = toTriangle '' t
· 使用定理 `Finset.coe_map`：coe_map (f : α ↪ β) (s : Finset α) : (s.map f : Set β) =
 f '' s
· 使用引理 `SimpleGraph.TripartiteFromTriangles.map_toTriangle_disjoint`：map_toTrian
gle_disjoint [ExplicitDisjoint t] : (t.map toTriangle : Set (Finset (α oplus β o
plus γ))).Pairwise fun x y => (x inter y : Set (α…
· 使用引理 `SimpleGraph.TripartiteFromTriangles.exists_mem_toTriangle`：exists_mem_to
Triangle {x y : α oplus β oplus γ} (hxy : (graph t).Adj x y) : exists z in t, x 
in toTriangle z ∧ y in toTriangle z
· 使用引理 `SimpleGraph.TripartiteFromTriangles.toTriangle_is3Clique`：toTriangle_is3
Clique (hx : x in t) : (graph t).IsNClique 3 (toTriangle x)
-/
lemma locallyLinear [ExplicitDisjoint t] [NoAccidental t] : (graph t).LocallyLinear := by
  classical
  refine ⟨?_, fun x y hxy ↦ ?_⟩
  · unfold EdgeDisjointTriangles
    convert! map_toTriangle_disjoint t
    rw [cliqueSet_eq_image, coe_map]
  · obtain ⟨z, hz, hxy⟩ := exists_mem_toTriangle hxy
    exact ⟨_, toTriangle_is3Clique hz, hxy⟩

end TripartiteFromTriangles
end SimpleGraph

