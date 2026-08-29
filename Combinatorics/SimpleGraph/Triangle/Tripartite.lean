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

/--
Inductive type `Rel` / 归纳类型 `Rel`

English:
inductive Rel
  parameters: (t : Finset (α × β × γ))
  constructors (6):
    - in₀₁: ⦃a b c⦄ : (a, b, c) in t -> Rel t (in₀ a) (in₁ b)
    - in₁₀: ⦃a b c⦄ : (a, b, c) in t -> Rel t (in₁ b) (in₀ a)
    - in₀₂: ⦃a b c⦄ : (a, b, c) in t -> Rel t (in₀ a) (in₂ c)
    - in₂₀: ⦃a b c⦄ : (a, b, c) in t -> Rel t (in₂ c) (in₀ a)
    - in₁₂: ⦃a b c⦄ : (a, b, c) in t -> Rel t (in₁ b) (in₂ c)
    - in₂₁: ⦃a b c⦄ : (a, b, c) in t -> Rel t (in₂ c) (in₁ b)

中文:
归纳类型 关系
  参数: (t : 有限集 (α × β × γ))
  构造子 (6 个):
    - in₀₁: ⦃a b c⦄ : (a, b, c) in t -> 关系 t (in₀ a) (in₁ b)
    - in₁₀: ⦃a b c⦄ : (a, b, c) in t -> 关系 t (in₁ b) (in₀ a)
    - in₀₂: ⦃a b c⦄ : (a, b, c) in t -> 关系 t (in₀ a) (in₂ c)
    - in₂₀: ⦃a b c⦄ : (a, b, c) in t -> 关系 t (in₂ c) (in₀ a)
    - in₁₂: ⦃a b c⦄ : (a, b, c) in t -> 关系 t (in₁ b) (in₂ c)
    - in₂₁: ⦃a b c⦄ : (a, b, c) in t -> 关系 t (in₂ c) (in₁ b)
-/
@[mk_iff] inductive Rel (t : Finset (α × β × γ)) : α oplus β oplus γ -> α oplus β oplus γ -> Prop
| in₀₁ ⦃a b c⦄ : (a, b, c) in t -> Rel t (in₀ a) (in₁ b)
| in₁₀ ⦃a b c⦄ : (a, b, c) in t -> Rel t (in₁ b) (in₀ a)
| in₀₂ ⦃a b c⦄ : (a, b, c) in t -> Rel t (in₀ a) (in₂ c)
| in₂₀ ⦃a b c⦄ : (a, b, c) in t -> Rel t (in₂ c) (in₀ a)
| in₁₂ ⦃a b c⦄ : (a, b, c) in t -> Rel t (in₁ b) (in₂ c)
| in₂₁ ⦃a b c⦄ : (a, b, c) in t -> Rel t (in₂ c) (in₁ b)

open Rel

/--
Instance `rel_irrefl` / 实例 `rel_irrefl`

English:
instance rel_irrefl
  signature: : Std.Irrefl (Rel t) where
  body: nomatch hx

中文:
实例 rel_irrefl
  签名: : Std.Irrefl (关系 t) where
  定义体: nomatch hx

Depends on / 依赖: nomatch
-/
instance rel_irrefl : Std.Irrefl (Rel t) where
  irrefl _x hx := nomatch hx

/--
Instance `rel_symm` / 实例 `rel_symm`

English:
instance rel_symm
  signature: : Std.Symm (Rel t) where
  body: by cases h <;> constructor <;> assumption

中文:
实例 rel_symm
  签名: : Std.Symm (关系 t) where
  定义体: by cases h <;> constructor <;> assumption
-/
instance rel_symm : Std.Symm (Rel t) where
  symm x y h := by cases h <;> constructor <;> assumption

/--
Definition of `graph` / `graph` 的定义

English:
definition graph
  signature: (t : Finset (α × β × γ))
  body: Rel t
  symm := inferInstance
  loopless := inferInstance

中文:
定义 graph
  签名: (t : 有限集 (α × β × γ))
  定义体: Rel t
  symm := inferInstance
  loopless := inferInstance
-/
def graph (t : Finset (α × β × γ)) : SimpleGraph (α oplus β oplus γ) where
  Adj := Rel t
  symm := inferInstance
  loopless := inferInstance

variable {a a' : α} {b b' : β} {c c' : γ} {x : α × β × γ}

namespace Graph

/--
lemma `not_in₀₀` / 引理 `not_in₀₀`

English:
lemma not_in₀₀
  statement: ¬ (graph t).Adj (in₀ a) (in₀ a')
  proof: fun h => nomatch h

中文:
引理 not_in₀₀
  结论: ¬ (graph t).伴随 (in₀ a) (in₀ a')
  证明: fun h => nomatch h
-/
@[simp] lemma not_in₀₀ : ¬ (graph t).Adj (in₀ a) (in₀ a') := fun h => nomatch h
/--
lemma `not_in₁₁` / 引理 `not_in₁₁`

English:
lemma not_in₁₁
  statement: ¬ (graph t).Adj (in₁ b) (in₁ b')
  proof: fun h => nomatch h

中文:
引理 not_in₁₁
  结论: ¬ (graph t).伴随 (in₁ b) (in₁ b')
  证明: fun h => nomatch h
-/
@[simp] lemma not_in₁₁ : ¬ (graph t).Adj (in₁ b) (in₁ b') := fun h => nomatch h
/--
lemma `not_in₂₂` / 引理 `not_in₂₂`

English:
lemma not_in₂₂
  statement: ¬ (graph t).Adj (in₂ c) (in₂ c')
  proof: fun h => nomatch h

中文:
引理 not_in₂₂
  结论: ¬ (graph t).伴随 (in₂ c) (in₂ c')
  证明: fun h => nomatch h
-/
@[simp] lemma not_in₂₂ : ¬ (graph t).Adj (in₂ c) (in₂ c') := fun h => nomatch h

/--
lemma `in₀₁_iff` / 引理 `in₀₁_iff`

English:
lemma in₀₁_iff
  statement: (graph t).Adj (in₀ a) (in₁ b) ↔ exists c, (a, b, c) in t
  proof: ⟨by rintro ⟨⟩; exact ⟨_, ‹_›⟩, fun ⟨_, h⟩ => in₀₁ h⟩

中文:
引理 in₀₁_iff
  结论: (graph t).伴随 (in₀ a) (in₁ b) ↔ 存在 c, (a, b, c) in t
  证明: ⟨by rintro ⟨⟩; exact ⟨_, ‹_›⟩, fun ⟨_, h⟩ => in₀₁ h⟩
-/
@[simp] lemma in₀₁_iff : (graph t).Adj (in₀ a) (in₁ b) ↔ exists c, (a, b, c) in t :=
  ⟨by rintro ⟨⟩; exact ⟨_, ‹_›⟩, fun ⟨_, h⟩ => in₀₁ h⟩
/--
lemma `in₁₀_iff` / 引理 `in₁₀_iff`

English:
lemma in₁₀_iff
  statement: (graph t).Adj (in₁ b) (in₀ a) ↔ exists c, (a, b, c) in t
  proof: ⟨by rintro ⟨⟩; exact ⟨_, ‹_›⟩, fun ⟨_, h⟩ => in₁₀ h⟩

中文:
引理 in₁₀_iff
  结论: (graph t).伴随 (in₁ b) (in₀ a) ↔ 存在 c, (a, b, c) in t
  证明: ⟨by rintro ⟨⟩; exact ⟨_, ‹_›⟩, fun ⟨_, h⟩ => in₁₀ h⟩
-/
@[simp] lemma in₁₀_iff : (graph t).Adj (in₁ b) (in₀ a) ↔ exists c, (a, b, c) in t :=
  ⟨by rintro ⟨⟩; exact ⟨_, ‹_›⟩, fun ⟨_, h⟩ => in₁₀ h⟩
/--
lemma `in₀₂_iff` / 引理 `in₀₂_iff`

English:
lemma in₀₂_iff
  statement: (graph t).Adj (in₀ a) (in₂ c) ↔ exists b, (a, b, c) in t
  proof: ⟨by rintro ⟨⟩; exact ⟨_, ‹_›⟩, fun ⟨_, h⟩ => in₀₂ h⟩

中文:
引理 in₀₂_iff
  结论: (graph t).伴随 (in₀ a) (in₂ c) ↔ 存在 b, (a, b, c) in t
  证明: ⟨by rintro ⟨⟩; exact ⟨_, ‹_›⟩, fun ⟨_, h⟩ => in₀₂ h⟩
-/
@[simp] lemma in₀₂_iff : (graph t).Adj (in₀ a) (in₂ c) ↔ exists b, (a, b, c) in t :=
  ⟨by rintro ⟨⟩; exact ⟨_, ‹_›⟩, fun ⟨_, h⟩ => in₀₂ h⟩
/--
lemma `in₂₀_iff` / 引理 `in₂₀_iff`

English:
lemma in₂₀_iff
  statement: (graph t).Adj (in₂ c) (in₀ a) ↔ exists b, (a, b, c) in t
  proof: ⟨by rintro ⟨⟩; exact ⟨_, ‹_›⟩, fun ⟨_, h⟩ => in₂₀ h⟩

中文:
引理 in₂₀_iff
  结论: (graph t).伴随 (in₂ c) (in₀ a) ↔ 存在 b, (a, b, c) in t
  证明: ⟨by rintro ⟨⟩; exact ⟨_, ‹_›⟩, fun ⟨_, h⟩ => in₂₀ h⟩
-/
@[simp] lemma in₂₀_iff : (graph t).Adj (in₂ c) (in₀ a) ↔ exists b, (a, b, c) in t :=
  ⟨by rintro ⟨⟩; exact ⟨_, ‹_›⟩, fun ⟨_, h⟩ => in₂₀ h⟩
/--
lemma `in₁₂_iff` / 引理 `in₁₂_iff`

English:
lemma in₁₂_iff
  statement: (graph t).Adj (in₁ b) (in₂ c) ↔ exists a, (a, b, c) in t
  proof: ⟨by rintro ⟨⟩; exact ⟨_, ‹_›⟩, fun ⟨_, h⟩ => in₁₂ h⟩

中文:
引理 in₁₂_iff
  结论: (graph t).伴随 (in₁ b) (in₂ c) ↔ 存在 a, (a, b, c) in t
  证明: ⟨by rintro ⟨⟩; exact ⟨_, ‹_›⟩, fun ⟨_, h⟩ => in₁₂ h⟩
-/
@[simp] lemma in₁₂_iff : (graph t).Adj (in₁ b) (in₂ c) ↔ exists a, (a, b, c) in t :=
  ⟨by rintro ⟨⟩; exact ⟨_, ‹_›⟩, fun ⟨_, h⟩ => in₁₂ h⟩
/--
lemma `in₂₁_iff` / 引理 `in₂₁_iff`

English:
lemma in₂₁_iff
  statement: (graph t).Adj (in₂ c) (in₁ b) ↔ exists a, (a, b, c) in t
  proof: ⟨by rintro ⟨⟩; exact ⟨_, ‹_›⟩, fun ⟨_, h⟩ => in₂₁ h⟩

中文:
引理 in₂₁_iff
  结论: (graph t).伴随 (in₂ c) (in₁ b) ↔ 存在 a, (a, b, c) in t
  证明: ⟨by rintro ⟨⟩; exact ⟨_, ‹_›⟩, fun ⟨_, h⟩ => in₂₁ h⟩
-/
@[simp] lemma in₂₁_iff : (graph t).Adj (in₂ c) (in₁ b) ↔ exists a, (a, b, c) in t :=
  ⟨by rintro ⟨⟩; exact ⟨_, ‹_›⟩, fun ⟨_, h⟩ => in₂₁ h⟩

/--
lemma `in₀₁_iff'` / 引理 `in₀₁_iff'`

English:
lemma in₀₁_iff'
  proof: by rintro ⟨⟩; exact ⟨_, ‹_›, by simp⟩
  mpr := by rintro ⟨⟨a, b, c⟩, h, rfl, rfl⟩; constructor; assumption

中文:
引理 in₀₁_iff'
  证明: by rintro ⟨⟩; exact ⟨_, ‹_›, by simp⟩
  mpr := by rintro ⟨⟨a, b, c⟩, h, rfl, rfl⟩; constructor; assumption
-/
lemma in₀₁_iff' :
    (graph t).Adj (in₀ a) (in₁ b) ↔ exists x : α × β × γ, x in t ∧ x.1 = a ∧ x.2.1 = b where
  mp := by rintro ⟨⟩; exact ⟨_, ‹_›, by simp⟩
  mpr := by rintro ⟨⟨a, b, c⟩, h, rfl, rfl⟩; constructor; assumption
/--
lemma `in₁₀_iff'` / 引理 `in₁₀_iff'`

English:
lemma in₁₀_iff'
  proof: by rintro ⟨⟩; exact ⟨_, ‹_›, by simp⟩
  mpr := by rintro ⟨⟨a, b, c⟩, h, rfl, rfl⟩; constructor; assumption

中文:
引理 in₁₀_iff'
  证明: by rintro ⟨⟩; exact ⟨_, ‹_›, by simp⟩
  mpr := by rintro ⟨⟨a, b, c⟩, h, rfl, rfl⟩; constructor; assumption
-/
lemma in₁₀_iff' :
    (graph t).Adj (in₁ b) (in₀ a) ↔ exists x : α × β × γ, x in t ∧ x.2.1 = b ∧ x.1 = a where
  mp := by rintro ⟨⟩; exact ⟨_, ‹_›, by simp⟩
  mpr := by rintro ⟨⟨a, b, c⟩, h, rfl, rfl⟩; constructor; assumption
/--
lemma `in₀₂_iff'` / 引理 `in₀₂_iff'`

English:
lemma in₀₂_iff'
  proof: by rintro ⟨⟩; exact ⟨_, ‹_›, by simp⟩
  mpr := by rintro ⟨⟨a, b, c⟩, h, rfl, rfl⟩; constructor; assumption

中文:
引理 in₀₂_iff'
  证明: by rintro ⟨⟩; exact ⟨_, ‹_›, by simp⟩
  mpr := by rintro ⟨⟨a, b, c⟩, h, rfl, rfl⟩; constructor; assumption
-/
lemma in₀₂_iff' :
    (graph t).Adj (in₀ a) (in₂ c) ↔ exists x : α × β × γ, x in t ∧ x.1 = a ∧ x.2.2 = c where
  mp := by rintro ⟨⟩; exact ⟨_, ‹_›, by simp⟩
  mpr := by rintro ⟨⟨a, b, c⟩, h, rfl, rfl⟩; constructor; assumption
/--
lemma `in₂₀_iff'` / 引理 `in₂₀_iff'`

English:
lemma in₂₀_iff'
  proof: by rintro ⟨⟩; exact ⟨_, ‹_›, by simp⟩
  mpr := by rintro ⟨⟨a, b, c⟩, h, rfl, rfl⟩; constructor; assumption

中文:
引理 in₂₀_iff'
  证明: by rintro ⟨⟩; exact ⟨_, ‹_›, by simp⟩
  mpr := by rintro ⟨⟨a, b, c⟩, h, rfl, rfl⟩; constructor; assumption
-/
lemma in₂₀_iff' :
    (graph t).Adj (in₂ c) (in₀ a) ↔ exists x : α × β × γ, x in t ∧ x.2.2 = c ∧ x.1 = a where
  mp := by rintro ⟨⟩; exact ⟨_, ‹_›, by simp⟩
  mpr := by rintro ⟨⟨a, b, c⟩, h, rfl, rfl⟩; constructor; assumption
/--
lemma `in₁₂_iff'` / 引理 `in₁₂_iff'`

English:
lemma in₁₂_iff'
  proof: by rintro ⟨⟩; exact ⟨_, ‹_›, by simp⟩
  mpr := by rintro ⟨⟨a, b, c⟩, h, rfl, rfl⟩; constructor; assumption

中文:
引理 in₁₂_iff'
  证明: by rintro ⟨⟩; exact ⟨_, ‹_›, by simp⟩
  mpr := by rintro ⟨⟨a, b, c⟩, h, rfl, rfl⟩; constructor; assumption
-/
lemma in₁₂_iff' :
    (graph t).Adj (in₁ b) (in₂ c) ↔ exists x : α × β × γ, x in t ∧ x.2.1 = b ∧ x.2.2 = c where
  mp := by rintro ⟨⟩; exact ⟨_, ‹_›, by simp⟩
  mpr := by rintro ⟨⟨a, b, c⟩, h, rfl, rfl⟩; constructor; assumption
/--
lemma `in₂₁_iff'` / 引理 `in₂₁_iff'`

English:
lemma in₂₁_iff'
  proof: by rintro ⟨⟩; exact ⟨_, ‹_›, by simp⟩
  mpr := by rintro ⟨⟨a, b, c⟩, h, rfl, rfl⟩; constructor; assumption

中文:
引理 in₂₁_iff'
  证明: by rintro ⟨⟩; exact ⟨_, ‹_›, by simp⟩
  mpr := by rintro ⟨⟨a, b, c⟩, h, rfl, rfl⟩; constructor; assumption
-/
lemma in₂₁_iff' :
    (graph t).Adj (in₂ c) (in₁ b) ↔ exists x : α × β × γ, x in t ∧ x.2.2 = c ∧ x.2.1 = b where
  mp := by rintro ⟨⟩; exact ⟨_, ‹_›, by simp⟩
  mpr := by rintro ⟨⟨a, b, c⟩, h, rfl, rfl⟩; constructor; assumption

end Graph

open Graph

/--
Definition of `ExplicitDisjoint` / `ExplicitDisjoint` 的定义

English:
class ExplicitDisjoint
  parameters: (t : Finset (α × β × γ))
  axioms and operations (3):
    - inj₀ : forall ⦃a b c a'⦄, (a, b, c) in t -> (a', b, c) in t -> a = a'
    - inj₁ : forall ⦃a b c b'⦄, (a, b, c) in t -> (a, b', c) in t -> b = b'
    - inj₂ : forall ⦃a b c c'⦄, (a, b, c) in t -> (a, b, c') in t -> c = c'

中文:
类 ExplicitDisjoint
  参数: (t : 有限集 (α × β × γ))
  公理与运算 (3 个):
    - inj₀ : 对任意 ⦃a b c a'⦄, (a, b, c) in t -> (a', b, c) in t -> a = a'
    - inj₁ : 对任意 ⦃a b c b'⦄, (a, b, c) in t -> (a, b', c) in t -> b = b'
    - inj₂ : 对任意 ⦃a b c c'⦄, (a, b, c) in t -> (a, b, c') in t -> c = c'
-/
class ExplicitDisjoint (t : Finset (α × β × γ)) : Prop where
  inj₀ : forall ⦃a b c a'⦄, (a, b, c) in t -> (a', b, c) in t -> a = a'
  inj₁ : forall ⦃a b c b'⦄, (a, b, c) in t -> (a, b', c) in t -> b = b'
  inj₂ : forall ⦃a b c c'⦄, (a, b, c) in t -> (a, b, c') in t -> c = c'

/--
Definition of `NoAccidental` / `NoAccidental` 的定义

English:
class NoAccidental
  parameters: (t : Finset (α × β × γ))
  axioms and operations (1):
    - eq_or_eq_or_eq : forall ⦃a a' b b' c c'⦄, (a', b, c) in t -> (a, b', c) in t -> (a, b, c') in t -> a = a' ∨ b = b' ∨ c = c'

中文:
类 NoAccidental
  参数: (t : 有限集 (α × β × γ))
  公理与运算 (1 个):
    - eq_or_eq_or_eq : 对任意 ⦃a a' b b' c c'⦄, (a', b, c) in t -> (a, b', c) in t -> (a, b, c') in t -> a = a' ∨ b = b' ∨ c = c'
-/
class NoAccidental (t : Finset (α × β × γ)) : Prop where
  eq_or_eq_or_eq : forall ⦃a a' b b' c c'⦄, (a', b, c) in t -> (a, b', c) in t -> (a, b, c') in t ->
    a = a' ∨ b = b' ∨ c = c'

section DecidableEq
variable [DecidableEq α] [DecidableEq β] [DecidableEq γ]

/--
Instance `graph.instDecidableRelAdj` / 实例 `graph.instDecidableRelAdj`

English:
instance graph.instDecidableRelAdj
  signature: : DecidableRel (graph t).Adj

中文:
实例 graph.instDecidableRelAdj
  签名: : DecidableRel (graph t).伴随
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

/--
lemma `graph_triple` / 引理 `graph_triple`

English:
lemma graph_triple
  given: ⦃x y z⦄
  proof: by
  rintro (_ | _ | _) (_ | _ | _) (_ | _ | _) <;>
    refine ⟨_, _, _, by ext; simp only [Finset.mem_insert, Finset.mem_singleton]; try tauto,
      ?_, ?_, ?_⟩ <;> constructor <;> assumption

中文:
引理 graph_triple
  条件: ⦃x y z⦄
  证明: by
  rintro (_ | _ | _) (_ | _ | _) (_ | _ | _) <;>
    refine ⟨_, _, _, by ext; simp only [Finset.mem_insert, Finset.mem_singleton]; try tauto,
      ?_, ?_, ?_⟩ <;> constructor <;> assumption

Depends on / 依赖: Finset, Finset.mem_insert, Finset.mem_singleton, mem_insert, mem_singleton
-/
lemma graph_triple ⦃x y z⦄ :
    (graph t).Adj x y -> (graph t).Adj x z -> (graph t).Adj y z -> exists a b c,
    ({in₀ a, in₁ b, in₂ c} : Finset (α oplus β oplus γ)) = {x, y, z} ∧ (graph t).Adj (in₀ a) (in₁ b) ∧
      (graph t).Adj (in₀ a) (in₂ c) ∧ (graph t).Adj (in₁ b) (in₂ c) := by
  rintro (_ | _ | _) (_ | _ | _) (_ | _ | _) <;>
    refine ⟨_, _, _, by ext; simp only [Finset.mem_insert, Finset.mem_singleton]; try tauto,
      ?_, ?_, ?_⟩ <;> constructor <;> assumption

/--
Definition of `toTriangle` / `toTriangle` 的定义

English:
definition toTriangle
  signature: : α × β × γ ↪ Finset (α oplus β oplus γ) where
  body: {in₀ x.1, in₁ x.2.1, in₂ x.2.2}
  inj' := fun ⟨a, b, c⟩ ⟨a', b', c'⟩ => by simpa only [Finset.Subset.antisymm_iff, Finset.subset_iff,
    mem_insert, mem_singleton, forall_eq_or_imp, forall_eq, Prod.mk_inj, or_false, false_or,
    in₀, in₁, in₂, Sum.inl.inj_iff, Sum.inr.inj_iff, reduceCtorEq] using And.left

中文:
定义 toTriangle
  签名: : α × β × γ ↪ 有限集 (α oplus β oplus γ) where
  定义体: {in₀ x.1, in₁ x.2.1, in₂ x.2.2}
  inj' := fun ⟨a, b, c⟩ ⟨a', b', c'⟩ => by simpa only [Finset.Subset.antisymm_iff, Finset.subset_iff,
    mem_insert, mem_singleton, forall_eq_or_imp, forall_eq, Prod.mk_inj, or_false, false_or,
    in₀, in₁, in₂, Sum.inl.inj_iff, Sum.inr.inj_iff, reduceCtorEq] using And.left
-/
@[simps] def toTriangle : α × β × γ ↪ Finset (α oplus β oplus γ) where
  toFun x := {in₀ x.1, in₁ x.2.1, in₂ x.2.2}
  inj' := fun ⟨a, b, c⟩ ⟨a', b', c'⟩ => by simpa only [Finset.Subset.antisymm_iff, Finset.subset_iff,
    mem_insert, mem_singleton, forall_eq_or_imp, forall_eq, Prod.mk_inj, or_false, false_or,
    in₀, in₁, in₂, Sum.inl.inj_iff, Sum.inr.inj_iff, reduceCtorEq] using And.left

/--
lemma `toTriangle_is3Clique` / 引理 `toTriangle_is3Clique`

English:
lemma toTriangle_is3Clique
  given: (hx : x in t)
  statement: (graph t).IsNClique 3 (toTriangle x)
  proof: by
  simp only [toTriangle_apply, is3Clique_triple_iff, in₀₁_iff, in₀₂_iff, in₁₂_iff]
  exact ⟨⟨_, hx⟩, ⟨_, hx⟩, _, hx⟩

中文:
引理 toTriangle_is3Clique
  条件: (hx : x in t)
  结论: (graph t).是NClique 3 (toTriangle x)
  证明: by
  simp only [toTriangle_apply, is3Clique_triple_iff, in₀₁_iff, in₀₂_iff, in₁₂_iff]
  exact ⟨⟨_, hx⟩, ⟨_, hx⟩, _, hx⟩

Depends on / 依赖: is3Clique_triple_iff, toTriangle_apply
-/
lemma toTriangle_is3Clique (hx : x in t) : (graph t).IsNClique 3 (toTriangle x) := by
  simp only [toTriangle_apply, is3Clique_triple_iff, in₀₁_iff, in₀₂_iff, in₁₂_iff]
  exact ⟨⟨_, hx⟩, ⟨_, hx⟩, _, hx⟩

/--
lemma `exists_mem_toTriangle` / 引理 `exists_mem_toTriangle`

English:
lemma exists_mem_toTriangle
  given: {x y : α oplus β oplus γ} (hxy : (graph t).Adj x y)
  proof: by cases hxy <;> exact ⟨_, ‹_›, by simp⟩

nonrec lemma is3Clique_iff [NoAccidental t] {s : Finset (α oplus β oplus γ)} :
    (graph t).IsNClique 3 s ↔ exists x, x in t ∧ toTriangle x = s := by
  refine ⟨fun h => ?_, ?_⟩
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

中文:
引理 存在_mem_toTriangle
  条件: {x y : α oplus β oplus γ} (hxy : (graph t).伴随 x y)
  证明: by cases hxy <;> exact ⟨_, ‹_›, by simp⟩

nonrec lemma is3Clique_iff [NoAccidental t] {s : Finset (α oplus β oplus γ)} :
    (graph t).IsNClique 3 s ↔ exists x, x in t ∧ toTriangle x = s := by
  refine ⟨fun h => ?_, ?_⟩
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
-/
lemma exists_mem_toTriangle {x y : α oplus β oplus γ} (hxy : (graph t).Adj x y) :
    exists z in t, x in toTriangle z ∧ y in toTriangle z := by cases hxy <;> exact ⟨_, ‹_›, by simp⟩

nonrec lemma is3Clique_iff [NoAccidental t] {s : Finset (α oplus β oplus γ)} :
    (graph t).IsNClique 3 s ↔ exists x, x in t ∧ toTriangle x = s := by
  refine ⟨fun h => ?_, ?_⟩
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

/--
lemma `toTriangle_surjOn` / 引理 `toTriangle_surjOn`

English:
lemma toTriangle_surjOn
  given: [NoAccidental t]
  proof: fun _ => is3Clique_iff.1

中文:
引理 toTriangle_surjOn
  条件: [NoAccidental t]
  证明: fun _ => is3Clique_iff.1

Depends on / 依赖: is3Clique_iff
-/
lemma toTriangle_surjOn [NoAccidental t] :
    (t : Set (α × β × γ)).SurjOn toTriangle ((graph t).cliqueSet 3) := fun _ => is3Clique_iff.1

variable (t)

/--
lemma `map_toTriangle_disjoint` / 引理 `map_toTriangle_disjoint`

English:
lemma map_toTriangle_disjoint
  given: [ExplicitDisjoint t]
  proof: by
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

中文:
引理 map_toTriangle_disjoint
  条件: [ExplicitDisjoint t]
  证明: by
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

Depends on / 依赖: Finset, Finset.coe_map, Finset.mem_coe, Prod.exists, Prod.mk_inj, Set.Subsingleton, Set.mem_image, Set.mem_inter_iff, Subsingleton, Sum.forall, and_imp, coe_map, forall_exists_index, mem_coe, mem_image, mem_insert, mem_inter_iff, mem_singleton, mk_inj, ne_of_apply_ne
-/
lemma map_toTriangle_disjoint [ExplicitDisjoint t] :
    (t.map toTriangle : Set (Finset (α oplus β oplus γ))).Pairwise
      fun x y => (x inter y : Set (α oplus β oplus γ)).Subsingleton := by
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

/--
lemma `cliqueSet_eq_image` / 引理 `cliqueSet_eq_image`

English:
lemma cliqueSet_eq_image
  given: [NoAccidental t]
  statement: (graph t).cliqueSet 3 = toTriangle '' t
  proof: by
  ext; exact is3Clique_iff

中文:
引理 cliqueSet_eq_image
  条件: [NoAccidental t]
  结论: (graph t).cliqueSet 3 = toTriangle '' t
  证明: by
  ext; exact is3Clique_iff

Depends on / 依赖: is3Clique_iff
-/
lemma cliqueSet_eq_image [NoAccidental t] : (graph t).cliqueSet 3 = toTriangle '' t := by
  ext; exact is3Clique_iff

section Fintype
variable [Fintype α] [Fintype β] [Fintype γ]

/--
lemma `cliqueFinset_eq_image` / 引理 `cliqueFinset_eq_image`

English:
lemma cliqueFinset_eq_image
  given: [NoAccidental t]
  statement: (graph t).cliqueFinset 3 = t.image toTriangle
  proof: coe_injective by push_cast; exact cliqueSet_eq_image _

中文:
引理 cliqueFinset_eq_image
  条件: [NoAccidental t]
  结论: (graph t).cliqueFinset 3 = t.像 toTriangle
  证明: coe_injective by push_cast; exact cliqueSet_eq_image _

Depends on / 依赖: cliqueSet_eq_image, coe_injective
-/
lemma cliqueFinset_eq_image [NoAccidental t] : (graph t).cliqueFinset 3 = t.image toTriangle :=
coe_injective by push_cast; exact cliqueSet_eq_image _

/--
lemma `cliqueFinset_eq_map` / 引理 `cliqueFinset_eq_map`

English:
lemma cliqueFinset_eq_map
  given: [NoAccidental t]
  statement: (graph t).cliqueFinset 3 = t.map toTriangle
  proof: by
  simp [cliqueFinset_eq_image, map_eq_image]

中文:
引理 cliqueFinset_eq_map
  条件: [NoAccidental t]
  结论: (graph t).cliqueFinset 3 = t.map toTriangle
  证明: by
  simp [cliqueFinset_eq_image, map_eq_image]

Depends on / 依赖: cliqueFinset_eq_image, map_eq_image
-/
lemma cliqueFinset_eq_map [NoAccidental t] : (graph t).cliqueFinset 3 = t.map toTriangle := by
  simp [cliqueFinset_eq_image, map_eq_image]

/--
lemma `card_triangles` / 引理 `card_triangles`

English:
lemma card_triangles
  given: [NoAccidental t]
  statement: #((graph t).cliqueFinset 3) = #t
  proof: by
  rw [cliqueFinset_eq_map]; rw [card_map]

中文:
引理 card_triangles
  条件: [NoAccidental t]
  结论: #((graph t).cliqueFinset 3) = #t
  证明: by
  rw [cliqueFinset_eq_map]; rw [card_map]
-/
@[simp] lemma card_triangles [NoAccidental t] : #((graph t).cliqueFinset 3) = #t := by
  rw [cliqueFinset_eq_map]; rw [card_map]

/--
lemma `farFromTriangleFree` / 引理 `farFromTriangleFree`

English:
lemma farFromTriangleFree
  statement: [ExplicitDisjoint t] {ε : 𝕜}
  proof: farFromTriangleFree_of_disjoint_triangles (t.map toTriangle)
    (map_subset_iff_subset_preimage.2 fun x hx => by simpa using toTriangle_is3Clique hx)
(map_toTriangle_disjoint t) by simpa [add_assoc] using ht

中文:
引理 farFromTriangleFree
  结论: [ExplicitDisjoint t] {ε : 𝕜}
  证明: farFromTriangleFree_of_disjoint_triangles (t.map toTriangle)
    (map_subset_iff_subset_preimage.2 fun x hx => by simpa using toTriangle_is3Clique hx)
(map_toTriangle_disjoint t) by simpa [add_assoc] using ht

Depends on / 依赖: add_assoc, farFromTriangleFree_of_disjoint_triangles, map_subset_iff_subset_preimage, map_toTriangle_disjoint, t.map, toTriangle, toTriangle_is3Clique
-/
lemma farFromTriangleFree [ExplicitDisjoint t] {ε : 𝕜}
    (ht : ε * ((Fintype.card α + Fintype.card β + Fintype.card γ) ^ 2 : Nat) <= #t) :
    (graph t).FarFromTriangleFree ε :=
  farFromTriangleFree_of_disjoint_triangles (t.map toTriangle)
    (map_subset_iff_subset_preimage.2 fun x hx => by simpa using toTriangle_is3Clique hx)
(map_toTriangle_disjoint t) by simpa [add_assoc] using ht

end Fintype
end DecidableEq

variable (t)

/--
lemma `locallyLinear` / 引理 `locallyLinear`

English:
lemma locallyLinear
  given: [ExplicitDisjoint t] [NoAccidental t]
  statement: (graph t).LocallyLinear
  proof: by
  classical
  refine ⟨?_, fun x y hxy => ?_⟩
  · unfold EdgeDisjointTriangles
    convert! map_toTriangle_disjoint t
    rw [cliqueSet_eq_image]; rw [coe_map]
  · obtain ⟨z, hz, hxy⟩ := exists_mem_toTriangle hxy
    exact ⟨_, toTriangle_is3Clique hz, hxy⟩

中文:
引理 locallyLinear
  条件: [ExplicitDisjoint t] [NoAccidental t]
  结论: (graph t).LocallyLinear
  证明: by
  classical
  refine ⟨?_, fun x y hxy => ?_⟩
  · unfold EdgeDisjointTriangles
    convert! map_toTriangle_disjoint t
    rw [cliqueSet_eq_image]; rw [coe_map]
  · obtain ⟨z, hz, hxy⟩ := exists_mem_toTriangle hxy
    exact ⟨_, toTriangle_is3Clique hz, hxy⟩

Depends on / 依赖: EdgeDisjointTriangles, classical, cliqueSet_eq_image, coe_map, convert, exists_mem_toTriangle, map_toTriangle_disjoint, toTriangle_is3Clique
-/
lemma locallyLinear [ExplicitDisjoint t] [NoAccidental t] : (graph t).LocallyLinear := by
  classical
  refine ⟨?_, fun x y hxy => ?_⟩
  · unfold EdgeDisjointTriangles
    convert! map_toTriangle_disjoint t
    rw [cliqueSet_eq_image]; rw [coe_map]
  · obtain ⟨z, hz, hxy⟩ := exists_mem_toTriangle hxy
    exact ⟨_, toTriangle_is3Clique hz, hxy⟩

end TripartiteFromTriangles
end SimpleGraph
