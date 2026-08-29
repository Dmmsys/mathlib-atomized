/-
Copyright (c) 2021 David Wärn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn
-/
module

public import Mathlib.Combinatorics.Quiver.Path
public import Mathlib.Combinatorics.Quiver.Subquiver
public import Mathlib.Order.WellFounded

/-!
# Arborescences

A quiver `V` is an arborescence (or directed rooted tree) when we have a root vertex `root : V` such
that for every `b : V` there is a unique path from `root` to `b`.

## Main definitions

- `Quiver.Arborescence V`: a typeclass asserting that `V` is an arborescence
- `arborescenceMk`: a convenient way of proving that a quiver is an arborescence
- `RootedConnected r`: a typeclass asserting that there is at least one path from `r` to `b` for
  every `b`.
- `geodesicSubtree r`: given `[RootedConnected r]`, this is a subquiver of `V` which contains
  just enough edges to include a shortest path from `r` to `b` for every `b`.
- `geodesicArborescence : Arborescence (geodesicSubtree r)`: an instance saying that the geodesic
  subtree is an arborescence. This proves the directed analogue of 'every connected graph has a
  spanning tree'. This proof avoids the use of Zorn's lemma.
-/

@[expose] public section


open Opposite

universe v u

namespace Quiver

/--
Definition of `Arborescence` / `Arborescence` 的定义

English:
class Arborescence
  parameters: (V : Type u) [Quiver.{v} V]
  axioms and operations (2):
    - root : V
    - uniquePath : forall b : V, Unique (Path root b)

中文:
类 树形图
  参数: (V : 类型u) [箭图.{v} V]
  公理与运算 (2 个):
    - root : V
    - uniquePath : 对任意 b : V, 唯一 (道路 root b)
-/
class Arborescence (V : Type u) [Quiver.{v} V] : Type max u v where
  /-- The root of the arborescence. -/
  root : V
  /-- There is a unique path from the root to any other vertex. -/
  uniquePath : forall b : V, Unique (Path root b)

/--
Definition of `root` / `root` 的定义

English:
definition root
  signature: (V : Type u) [Quiver V] [Arborescence V]
  body: Arborescence.root

中文:
定义 root
  签名: (V : 类型u) [箭图 V] [树形图 V]
  定义体: Arborescence.root

Depends on / 依赖: Arborescence, Arborescence.root
-/
def root (V : Type u) [Quiver V] [Arborescence V] : V :=
  Arborescence.root

instance {V : Type u} [Quiver V] [Arborescence V] (b : V) : Unique (Path (root V) b) :=
  Arborescence.uniquePath b

/-- To show that `[Quiver V]` is an arborescence with root `r : V`, it suffices to
  - provide a height function `V → ℕ` such that every arrow goes from a
    lower vertex to a higher vertex,
  - show that every vertex has at most one arrow to it, and
  - show that every vertex other than `r` has an arrow to it. -/
@[instance_reducible]
/--
Definition of `arborescenceMk` / `arborescenceMk` 的定义

English:
definition arborescenceMk
  signature: {V : Type u} [Quiver V] (r : V) (height : V -> Nat)
  body: r
  uniquePath b :=
    ⟨Classical.inhabited_of_nonempty (by
      rcases show exists n, height b < n from ⟨_, Nat.lt_add_one _⟩ with ⟨n, hn⟩
      induction n generalizing b with
      | zero => exact False.elim (Nat.not_lt_zero _ hn)
      | succ n ih =>
      rcases root_or_arrow b with (⟨⟨⟩⟩ | ⟨

中文:
定义 arborescenceMk
  签名: {V : 类型u} [箭图 V] (r : V) (height : V -> 自然数)
  定义体: r
  uniquePath b :=
    ⟨Classical.inhabited_of_nonempty (by
      rcases show exists n, height b < n from ⟨_, Nat.lt_add_one _⟩ with ⟨n, hn⟩
      induction n generalizing b with
      | zero => exact False.elim (Nat.not_lt_zero _ hn)
      | succ n ih =>
      rcases root_or_arrow b with (⟨⟨⟩⟩ | ⟨
-/
noncomputable def arborescenceMk {V : Type u} [Quiver V] (r : V) (height : V -> Nat)
    (height_lt : forall ⦃a b⦄, (a ⟶ b) -> height a < height b)
    (unique_arrow : forall ⦃a b c : V⦄ (e : a ⟶ c) (f : b ⟶ c), a = b ∧ e ≍ f)
    (root_or_arrow : forall b, b = r ∨ exists a, Nonempty (a ⟶ b)) :
    Arborescence V where
  root := r
  uniquePath b :=
    ⟨Classical.inhabited_of_nonempty (by
      rcases show exists n, height b < n from ⟨_, Nat.lt_add_one _⟩ with ⟨n, hn⟩
      induction n generalizing b with
      | zero => exact False.elim (Nat.not_lt_zero _ hn)
      | succ n ih =>
      rcases root_or_arrow b with (⟨⟨⟩⟩ | ⟨a, ⟨e⟩⟩)
      · exact ⟨Path.nil⟩
      · rcases ih a (lt_of_lt_of_le (height_lt e) (Nat.lt_succ_iff.mp hn)) with ⟨p⟩
        exact ⟨p.cons e⟩), by
      have height_le : forall {a b}, Path a b -> height a <= height b := by
        intro a b p
        induction p with
        | nil => rfl
        | cons _ e ih => exact le_of_lt (lt_of_le_of_lt ih (height_lt e))
      suffices forall p q : Path r b, p = q by
        intro p
        apply this
      intro p q
      induction p with
      | nil =>
        rcases q with _ | ⟨q, f⟩
        · rfl
        · exact False.elim (lt_irrefl _ (lt_of_le_of_lt (height_le q) (height_lt f)))
      | cons p e ih =>
        rcases q with _ | ⟨q, f⟩
        · exact False.elim (lt_irrefl _ (lt_of_le_of_lt (height_le p) (height_lt e)))
        · rcases unique_arrow e f with ⟨⟨⟩, ⟨⟩⟩
          rw [ih]⟩

/--
Definition of `RootedConnected` / `RootedConnected` 的定义

English:
class RootedConnected
  parameters: {V : Type u} [Quiver V] (r : V)
  axioms and operations (1):
    - nonempty_path : forall b : V, Nonempty (Path r b)

中文:
类 RootedConnected
  参数: {V : 类型u} [箭图 V] (r : V)
  公理与运算 (1 个):
    - nonempty_path : 对任意 b : V, 非空 (道路 r b)
-/
class RootedConnected {V : Type u} [Quiver V] (r : V) : Prop where
  nonempty_path : forall b : V, Nonempty (Path r b)

attribute [instance] RootedConnected.nonempty_path

section GeodesicSubtree

variable {V : Type u} [Quiver.{v} V] (r : V) [RootedConnected r]

/--
Definition of `shortestPath` / `shortestPath` 的定义

English:
definition shortestPath
  signature: (b : V)
  body: WellFounded.min (measure Path.length).wf Set.univ Set.univ_nonempty

中文:
定义 shortestPath
  签名: (b : V)
  定义体: WellFounded.min (measure Path.length).wf Set.univ Set.univ_nonempty

Depends on / 依赖: Path.length, Set.univ, Set.univ_nonempty, WellFounded, WellFounded.min, length, measure, univ_nonempty
-/
noncomputable def shortestPath (b : V) : Path r b :=
  WellFounded.min (measure Path.length).wf Set.univ Set.univ_nonempty

/--
theorem `shortest_path_spec` / 定理 `shortest_path_spec`

English:
theorem shortest_path_spec
  given: {a : V} (p : Path r a)
  statement: (shortestPath r a).length <= p.length
  proof: not_lt.mp (WellFounded.not_lt_min (measure _).wf Set.univ trivial)

中文:
定理 shortest_path_spec
  条件: {a : V} (p : 道路 r a)
  结论: (shortestPath r a).length <= p.length
  证明: not_lt.mp (WellFounded.not_lt_min (measure _).wf Set.univ trivial)

Depends on / 依赖: Set.univ, WellFounded, WellFounded.not_lt_min, measure, not_lt, not_lt.mp, not_lt_min
-/
theorem shortest_path_spec {a : V} (p : Path r a) : (shortestPath r a).length <= p.length :=
  not_lt.mp (WellFounded.not_lt_min (measure _).wf Set.univ trivial)

/--
Definition of `geodesicSubtree` / `geodesicSubtree` 的定义

English:
definition geodesicSubtree
  signature: : WideSubquiver V
  body: fun a b =>
  { e | exists p : Path r a, shortestPath r b = p.cons e }

中文:
定义 geodesicSubtree
  签名: : WideSubquiver V
  定义体: fun a b =>
  { e | exists p : Path r a, shortestPath r b = p.cons e }
-/
def geodesicSubtree : WideSubquiver V := fun a b =>
  { e | exists p : Path r a, shortestPath r b = p.cons e }

set_option backward.isDefEq.respectTransparency false in
/--
Instance `geodesicArborescence` / 实例 `geodesicArborescence`

English:
instance geodesicArborescence
  signature: : Arborescence (geodesicSubtree r)
  body: arborescenceMk r (fun a => (shortestPath r a).length)
    (by
      rintro a b ⟨e, p, h⟩
      simp_rw [h, Path.length_cons, Nat.lt_succ_iff]
      apply shortest_path_spec)
    (by
      rintro a b c ⟨e, p, h⟩ ⟨f, q, j⟩
      cases h.symm.trans j
      constructor <;> rfl)
    (by
      intro b
   

中文:
实例 geodesicArborescence
  签名: : 树形图 (geodesicSubtree r)
  定义体: arborescenceMk r (fun a => (shortestPath r a).length)
    (by
      rintro a b ⟨e, p, h⟩
      simp_rw [h, Path.length_cons, Nat.lt_succ_iff]
      apply shortest_path_spec)
    (by
      rintro a b c ⟨e, p, h⟩ ⟨f, q, j⟩
      cases h.symm.trans j
      constructor <;> rfl)
    (by
      intro b
   

Depends on / 依赖: Nat.lt_succ_iff, Or.inl, Or.inr, Path.length_cons, arborescenceMk, h.symm.trans, length, length_cons, lt_succ_iff, shortestPath, shortest_path_spec, simp_rw
-/
noncomputable instance geodesicArborescence : Arborescence (geodesicSubtree r) :=
  arborescenceMk r (fun a => (shortestPath r a).length)
    (by
      rintro a b ⟨e, p, h⟩
      simp_rw [h, Path.length_cons, Nat.lt_succ_iff]
      apply shortest_path_spec)
    (by
      rintro a b c ⟨e, p, h⟩ ⟨f, q, j⟩
      cases h.symm.trans j
      constructor <;> rfl)
    (by
      intro b
      rcases hp : shortestPath r b with (_ | ⟨p, e⟩)
      · exact Or.inl rfl
      · exact Or.inr ⟨_, ⟨⟨e, p, hp⟩⟩⟩)

end GeodesicSubtree

end Quiver
