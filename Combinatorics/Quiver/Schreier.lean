/-
Copyright (c) 2026 Runtian Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Runtian Zhou
-/
module

public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Combinatorics.Quiver.Covering
public import Mathlib.Combinatorics.Quiver.SingleObj

/-!
# Schreier Graphs

This module defines Schreier graphs as quivers with labelled edges.

Given a monoid `M` acting on a type `V` and a map `ι : S → M`, the Schreier graph has
vertices `V` and a directed edge `x → ι(s) • x` for each `x : V` and `s : S`.

## Main definitions

* `SchreierGraph V ι` - The Schreier graph of an action, with vertices of type `V` and edges
  labelled by elements of `S` via `ι : S → M`.
* `SchreierGraph.labelling` - The prefunctor from a Schreier graph to `SingleObj S` that
  extracts edge labels.

## Main results

* `SchreierGraph.labelling_isCovering` - The labelling prefunctor is a covering when we have
  a group action.

## Examples

* The (left) **Cayley graph** of a group `M` with generators `ι : S → M` is the Schreier graph
  where `V = M` and the action is left multiplication.

## Implementation notes

Although referred to informally as graphs, Schreier graphs have multiple, directed, labelled
edges between nodes and so are implemented here as quivers.

## References

* [Y. Vorobets, *Notes on the Schreier graphs of the Grigorchuk group*][Vorobets2012]
-/

@[expose] public section

namespace Quiver

/-- A Schreier graph for a monoid `M` acting on `V` with generators `ι : S → M`.
Vertices are elements of `V`, and there is an edge from `x` to `y` for each `s : S`
such that `ι s • x = y`. -/
@[nolint unusedArguments, ext]
/--
Definition of `SchreierGraph` / `SchreierGraph` 的定义

English:
structure SchreierGraph
  parameters: (V : Type*) {M : Type*} [SMul M V] {S : Type*} (_ι : S -> M)
  axioms and operations (2):
    - ofVertex : :
    - toVertex : V

中文:
结构 Schreier图
  参数: (V : 类型) {M : 类型} [标量乘法 M V] {S : 类型} (_ι : S -> M)
  公理与运算 (2 个):
    - ofVertex : :
    - toVertex : V
-/
structure SchreierGraph (V : Type*) {M : Type*} [SMul M V] {S : Type*} (_ι : S -> M) where
  /-- Wraps a vertex of the acted-upon type into the Schreier graph. -/
  ofVertex ::
  /-- The underlying vertex. -/
  toVertex : V

namespace SchreierGraph

section Basic

variable (V : Type*) {M : Type*} [SMul M V] {S : Type*} (ι : S -> M)

/-- Equivalence between the original vertex type and the Schreier graph type. -/
@[simps]
/--
Definition of `equiv` / `equiv` 的定义

English:
definition equiv
  signature: : V ≃ SchreierGraph V ι where
  body: SchreierGraph.ofVertex
  invFun := SchreierGraph.toVertex
  left_inv _ := rfl
  right_inv _ := rfl

中文:
定义 equiv
  签名: : V ≃ Schreier图 V ι where
  定义体: SchreierGraph.ofVertex
  invFun := SchreierGraph.toVertex
  left_inv _ := rfl
  right_inv _ := rfl

Depends on / 依赖: SchreierGraph, SchreierGraph.ofVertex, ofVertex
-/
def equiv : V ≃ SchreierGraph V ι where
  toFun := SchreierGraph.ofVertex
  invFun := SchreierGraph.toVertex
  left_inv _ := rfl
  right_inv _ := rfl

/--
Instance `schreierGraphSMul` / 实例 `schreierGraphSMul`

English:
instance schreierGraphSMul
  signature: : SMul M (SchreierGraph V ι) where
  body: ⟨x • y.toVertex⟩

中文:
实例 schreierGraphSMul
  签名: : 标量乘法 M (Schreier图 V ι) where
  定义体: ⟨x • y.toVertex⟩

Depends on / 依赖: toVertex, y.toVertex
-/
instance schreierGraphSMul : SMul M (SchreierGraph V ι) where
  smul x y := ⟨x • y.toVertex⟩

/--
Instance `schreierGraphQuiver` / 实例 `schreierGraphQuiver`

English:
instance schreierGraphQuiver
  signature: : Quiver (SchreierGraph V ι) where
  body: { s : S // (ι s) • x = y }

中文:
实例 schreierGraphQuiver
  签名: : 箭图 (Schreier图 V ι) where
  定义体: { s : S // (ι s) • x = y }
-/
instance schreierGraphQuiver : Quiver (SchreierGraph V ι) where
  Hom x y := { s : S // (ι s) • x = y }

/-- The labelling of arrows in a Schreier graph by elements of `S`.
This is encoded as a prefunctor to `SingleObj S`. -/
@[simps]
/--
Definition of `labelling` / `labelling` 的定义

English:
definition labelling
  signature: : SchreierGraph V ι ⥤q SingleObj S where
  body: SingleObj.star S
  map e := e.val

中文:
定义 labelling
  签名: : Schreier图 V ι ⥤q SingleObj S where
  定义体: SingleObj.star S
  map e := e.val

Depends on / 依赖: SingleObj, SingleObj.star
-/
def labelling : SchreierGraph V ι ⥤q SingleObj S where
  obj _ := SingleObj.star S
  map e := e.val

end Basic

section MulAction

variable (V : Type*) {M : Type*} [Monoid M] [MulAction M V] {S : Type*} (ι : S -> M)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MulAction M (SchreierGraph V ι)
  body: by
    ext
    exact one_smul M x.toVertex
  mul_smul a b x := by
    ext
    exact mul_smul a b x.toVertex

中文:
实例 :
  签名: 乘法作用 M (Schreier图 V ι)
  定义体: by
    ext
    exact one_smul M x.toVertex
  mul_smul a b x := by
    ext
    exact mul_smul a b x.toVertex

Depends on / 依赖: mul_smul, one_smul, toVertex, x.toVertex
-/
instance : MulAction M (SchreierGraph V ι) where
  one_smul x := by
    ext
    exact one_smul M x.toVertex
  mul_smul a b x := by
    ext
    exact mul_smul a b x.toVertex

end MulAction

section GroupAction

/-!
### Schreier graphs for group actions

When we have a group action, the labelling becomes a covering.
-/

variable {V : Type*} {M : Type*} [Group M] [MulAction M V] {S : Type*} (ι : S -> M)

/-- The star map of the labelling prefunctor as an equivalence. -/
@[simps]
/--
Definition of `labellingStarEquiv` / `labellingStarEquiv` 的定义

English:
definition labellingStarEquiv
  signature: (x : SchreierGraph V ι)
  body: (labelling V ι).star x
  invFun := fun ⟨_, s⟩ => ⟨ι s • x, s, rfl⟩
  left_inv := fun ⟨_, _, rfl⟩ => rfl
  right_inv := fun ⟨_, _⟩ => rfl

中文:
定义 labellingStarEquiv
  签名: (x : Schreier图 V ι)
  定义体: (labelling V ι).star x
  invFun := fun ⟨_, s⟩ => ⟨ι s • x, s, rfl⟩
  left_inv := fun ⟨_, _, rfl⟩ => rfl
  right_inv := fun ⟨_, _⟩ => rfl

Depends on / 依赖: labelling
-/
def labellingStarEquiv (x : SchreierGraph V ι) :
    Quiver.Star x ≃ Quiver.Star (SingleObj.star S) where
  toFun := (labelling V ι).star x
  invFun := fun ⟨_, s⟩ => ⟨ι s • x, s, rfl⟩
  left_inv := fun ⟨_, _, rfl⟩ => rfl
  right_inv := fun ⟨_, _⟩ => rfl

/-- The costar map of the labelling prefunctor as an equivalence. -/
@[simps]
/--
Definition of `labellingCostarEquiv` / `labellingCostarEquiv` 的定义

English:
definition labellingCostarEquiv
  signature: (x : SchreierGraph V ι)
  body: (labelling V ι).costar x
  invFun := fun ⟨_, s⟩ => ⟨(ι s)⁻¹ • x, s, by simp⟩
  left_inv := by
    rintro ⟨v, s, hs⟩
    simp only [Prefunctor.costar_apply, labelling_map]
    have : (ι s)⁻¹ • x = v := by rw [← hs, inv_smul_smul]
    subst this; rfl
  right_inv := fun ⟨_, _⟩ => rfl

中文:
定义 labellingCostarEquiv
  签名: (x : Schreier图 V ι)
  定义体: (labelling V ι).costar x
  invFun := fun ⟨_, s⟩ => ⟨(ι s)⁻¹ • x, s, by simp⟩
  left_inv := by
    rintro ⟨v, s, hs⟩
    simp only [Prefunctor.costar_apply, labelling_map]
    have : (ι s)⁻¹ • x = v := by rw [← hs, inv_smul_smul]
    subst this; rfl
  right_inv := fun ⟨_, _⟩ => rfl

Depends on / 依赖: costar, labelling
-/
def labellingCostarEquiv (x : SchreierGraph V ι) :
    Quiver.Costar x ≃ Quiver.Costar (SingleObj.star S) where
  toFun := (labelling V ι).costar x
  invFun := fun ⟨_, s⟩ => ⟨(ι s)⁻¹ • x, s, by simp⟩
  left_inv := by
    rintro ⟨v, s, hs⟩
    simp only [Prefunctor.costar_apply, labelling_map]
    have : (ι s)⁻¹ • x = v := by rw [← hs, inv_smul_smul]
    subst this; rfl
  right_inv := fun ⟨_, _⟩ => rfl

/--
theorem `labelling_isCovering` / 定理 `labelling_isCovering`

English:
theorem labelling_isCovering
  statement: (labelling V ι).IsCovering where
  proof: (labellingStarEquiv ι u).bijective
  costar_bijective u := (labellingCostarEquiv ι u).bijective

中文:
定理 labelling_isCovering
  结论: (labelling V ι).是余vering where
  证明: (labellingStarEquiv ι u).bijective
  costar_bijective u := (labellingCostarEquiv ι u).bijective

Depends on / 依赖: bijective, labellingStarEquiv
-/
theorem labelling_isCovering : (labelling V ι).IsCovering where
  star_bijective u := (labellingStarEquiv ι u).bijective
  costar_bijective u := (labellingCostarEquiv ι u).bijective

/--
lemma `map_smul_of_comp_labelling_eq` / 引理 `map_smul_of_comp_labelling_eq`

English:
lemma map_smul_of_comp_labelling_eq
  statement: {W : Type*} [MulAction M W]
  proof: by
  -- The key is that φ preserves labels, so edges labelled 's' stay labelled 's'
  let e : v ⟶ ι s • v := ⟨s, rfl⟩
  -- φ.map e is an edge from φ.obj v, and its label is preserved
  have h := (φ.map e).property
  -- This says: `ι (φ.map e).val • φ.obj v = φ.obj (ι s • v)`
  -- We need to show `(φ.map e).val = s`
  have label_eq : (φ.map e).val = s := by
    -- `φm` says `φ ⋙q labelling = labelling`
    -- So `(φ ⋙q labelling).map e = labelling.map e`
    have : (φ ⋙q labelling W ι).map e = (labelling V ι).map e := by
      rw [φm]
    simp only [Prefunctor.comp_map, labelling_map] at this
    exact this
  rw [label_eq] at h
  exact h.symm

中文:
引理 map_smul_of_comp_labelling_eq
  结论: {W : 类型} [乘法作用 M W]
  证明: by
  -- The key is that φ preserves labels, so edges labelled 's' stay labelled 's'
  let e : v ⟶ ι s • v := ⟨s, rfl⟩
  -- φ.map e is an edge from φ.obj v, and its label is preserved
  have h := (φ.map e).property
  -- This says: `ι (φ.map e).val • φ.obj v = φ.obj (ι s • v)`
  -- We need to show `(φ.map e).val = s`
  have label_eq : (φ.map e).val = s := by
    -- `φm` says `φ ⋙q labelling = labelling`
    -- So `(φ ⋙q labelling).map e = labelling.map e`
    have : (φ ⋙q labelling W ι).map e = (labelling V ι).map e := by
      rw [φm]
    simp only [Prefunctor.comp_map, labelling_map] at this
    exact this
  rw [label_eq] at h
  exact h.symm
-/
lemma map_smul_of_comp_labelling_eq {W : Type*} [MulAction M W]
    (φ : SchreierGraph V ι ⥤q SchreierGraph W ι) (φm : φ ⋙q labelling W ι = labelling V ι)
    (v : SchreierGraph V ι) (s : S) :
    φ.obj (ι s • v) = ι s • (φ.obj v) := by
  -- The key is that φ preserves labels, so edges labelled 's' stay labelled 's'
  let e : v ⟶ ι s • v := ⟨s, rfl⟩
  -- φ.map e is an edge from φ.obj v, and its label is preserved
  have h := (φ.map e).property
  -- This says: `ι (φ.map e).val • φ.obj v = φ.obj (ι s • v)`
  -- We need to show `(φ.map e).val = s`
  have label_eq : (φ.map e).val = s := by
    -- `φm` says `φ ⋙q labelling = labelling`
    -- So `(φ ⋙q labelling).map e = labelling.map e`
    have : (φ ⋙q labelling W ι).map e = (labelling V ι).map e := by
      rw [φm]
    simp only [Prefunctor.comp_map, labelling_map] at this
    exact this
  rw [label_eq] at h
  exact h.symm

end GroupAction

end SchreierGraph

end Quiver
