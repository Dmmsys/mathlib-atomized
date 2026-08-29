/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Yury Kudryashov
-/
module

public import Mathlib.Order.Minimal
public import Mathlib.Order.Zorn
public import Mathlib.Topology.ContinuousOn
public import Mathlib.Topology.DiscreteSubset
public import Mathlib.Tactic.CrossRefAttribute
import Mathlib.Topology.WithTopology

/-!
# Irreducibility in topological spaces

## Main definitions

* `IrreducibleSpace`: a typeclass applying to topological spaces, stating that the space
  is nonempty and does not admit a nontrivial pair of disjoint opens.
* `IsIrreducible`: for a nonempty set in a topological space, the property that the set is an
  irreducible space in the subspace topology.

## On the definition of irreducible and connected sets/spaces

In informal mathematics, irreducible spaces are assumed to be nonempty.
We formalise the predicate without that assumption as `IsPreirreducible`.
In other words, the only difference is whether the empty space counts as irreducible.
There are good reasons to consider the empty space to be “too simple to be simple”
See also https://ncatlab.org/nlab/show/too+simple+to+be+simple,
and in particular
https://ncatlab.org/nlab/show/too+simple+to+be+simple#relationship_to_biased_definitions.

-/

@[expose] public section

open Set Topology

variable {X : Type*} {Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {s t : Set X}

section Preirreducible

/--
Definition of `IsPreirreducible` / `IsPreirreducible` 的定义

English:
definition IsPreirreducible
  signature: (s : Set X)
  body: forall u v : Set X, IsOpen u -> IsOpen v -> (s inter u).Nonempty -> (s inter v).Nonempty -> (s inter (u inter v)).Nonempty

中文:
定义 IsPreirreducible
  签名: (s : 集合 X)
  定义体: forall u v : Set X, IsOpen u -> IsOpen v -> (s inter u).Nonempty -> (s inter v).Nonempty -> (s inter (u inter v)).Nonempty

Depends on / 依赖: IsOpen, Nonempty
-/
def IsPreirreducible (s : Set X) : Prop :=
  forall u v : Set X, IsOpen u -> IsOpen v -> (s inter u).Nonempty -> (s inter v).Nonempty -> (s inter (u inter v)).Nonempty

/-- An irreducible set `s` is one that is nonempty and
where there is no non-trivial pair of disjoint opens on `s`. -/
@[stacks 004V "(1) as predicate on subsets of a space"]
/--
Definition of `IsIrreducible` / `IsIrreducible` 的定义

English:
definition IsIrreducible
  signature: (s : Set X)
  body: s.Nonempty ∧ IsPreirreducible s

中文:
定义 是不可约
  签名: (s : 集合 X)
  定义体: s.Nonempty ∧ IsPreirreducible s

Depends on / 依赖: IsPreirreducible, Nonempty, s.Nonempty
-/
def IsIrreducible (s : Set X) : Prop :=
  s.Nonempty ∧ IsPreirreducible s

/--
theorem `IsIrreducible.nonempty` / 定理 `IsIrreducible.nonempty`

English:
theorem IsIrreducible.nonempty
  given: (h : IsIrreducible s)
  statement: s.Nonempty
  proof: h.1

中文:
定理 是不可约.nonempty
  条件: (h : 是不可约 s)
  结论: s.非空
  证明: h.1
-/
theorem IsIrreducible.nonempty (h : IsIrreducible s) : s.Nonempty :=
  h.1

/--
theorem `IsIrreducible.isPreirreducible` / 定理 `IsIrreducible.isPreirreducible`

English:
theorem IsIrreducible.isPreirreducible
  given: (h : IsIrreducible s)
  statement: IsPreirreducible s
  proof: h.2

中文:
定理 是不可约.isPreirreducible
  条件: (h : 是不可约 s)
  结论: IsPreirreducible s
  证明: h.2
-/
theorem IsIrreducible.isPreirreducible (h : IsIrreducible s) : IsPreirreducible s :=
  h.2

/--
theorem `isPreirreducible_empty` / 定理 `isPreirreducible_empty`

English:
theorem isPreirreducible_empty
  statement: IsPreirreducible (∅ : Set X)
  proof: fun _ _ _ _ _ ⟨_, h1, _⟩ =>
  h1.elim

中文:
定理 isPreirreducible_empty
  结论: IsPreirreducible (∅ : 集合 X)
  证明: fun _ _ _ _ _ ⟨_, h1, _⟩ =>
  h1.elim
-/
theorem isPreirreducible_empty : IsPreirreducible (∅ : Set X) := fun _ _ _ _ _ ⟨_, h1, _⟩ =>
  h1.elim

/--
theorem `Set.Subsingleton.isPreirreducible` / 定理 `Set.Subsingleton.isPreirreducible`

English:
theorem Set.Subsingleton.isPreirreducible
  given: (hs : s.Subsingleton)
  statement: IsPreirreducible s
  proof: fun _u _v _ _ ⟨_x, hxs, hxu⟩ ⟨y, hys, hyv⟩ => ⟨y, hys, hs hxs hys ▸ hxu, hyv⟩

中文:
定理 集合.子单例.isPreirreducible
  条件: (hs : s.子单例)
  结论: IsPreirreducible s
  证明: fun _u _v _ _ ⟨_x, hxs, hxu⟩ ⟨y, hys, hyv⟩ => ⟨y, hys, hs hxs hys ▸ hxu, hyv⟩
-/
theorem Set.Subsingleton.isPreirreducible (hs : s.Subsingleton) : IsPreirreducible s :=
  fun _u _v _ _ ⟨_x, hxs, hxu⟩ ⟨y, hys, hyv⟩ => ⟨y, hys, hs hxs hys ▸ hxu, hyv⟩

/--
theorem `isPreirreducible_singleton` / 定理 `isPreirreducible_singleton`

English:
theorem isPreirreducible_singleton
  given: {x}
  statement: IsPreirreducible ({x} : Set X)
  proof: subsingleton_singleton.isPreirreducible

中文:
定理 isPreirreducible_singleton
  条件: {x}
  结论: IsPreirreducible ({x} : 集合 X)
  证明: subsingleton_singleton.isPreirreducible

Depends on / 依赖: isPreirreducible, subsingleton_singleton, subsingleton_singleton.isPreirreducible
-/
theorem isPreirreducible_singleton {x} : IsPreirreducible ({x} : Set X) :=
  subsingleton_singleton.isPreirreducible

/--
theorem `isIrreducible_singleton` / 定理 `isIrreducible_singleton`

English:
theorem isIrreducible_singleton
  given: {x}
  statement: IsIrreducible ({x} : Set X)
  proof: ⟨singleton_nonempty x, isPreirreducible_singleton⟩

中文:
定理 isIrreducible_singleton
  条件: {x}
  结论: 是不可约 ({x} : 集合 X)
  证明: ⟨singleton_nonempty x, isPreirreducible_singleton⟩

Depends on / 依赖: isPreirreducible_singleton, singleton_nonempty
-/
theorem isIrreducible_singleton {x} : IsIrreducible ({x} : Set X) :=
  ⟨singleton_nonempty x, isPreirreducible_singleton⟩

/--
theorem `isPreirreducible_iff_closure` / 定理 `isPreirreducible_iff_closure`

English:
theorem isPreirreducible_iff_closure
  statement: IsPreirreducible (closure s) ↔ IsPreirreducible s
  proof: forall₄_congr fun u v hu hv => by
    iterate 3 rw [closure_inter_open_nonempty_iff]
    exacts [hu.inter hv, hv, hu]

@[stacks 004W "(1)"]

中文:
定理 isPreirreducible_iff_closure
  结论: IsPreirreducible (closure s) ↔ IsPreirreducible s
  证明: forall₄_congr fun u v hu hv => by
    iterate 3 rw [closure_inter_open_nonempty_iff]
    exacts [hu.inter hv, hv, hu]

@[stacks 004W "(1)"]

Depends on / 依赖: closure_inter_open_nonempty_iff, exacts, hu.inter, iterate
-/
theorem isPreirreducible_iff_closure : IsPreirreducible (closure s) ↔ IsPreirreducible s :=
  forall₄_congr fun u v hu hv => by
    iterate 3 rw [closure_inter_open_nonempty_iff]
    exacts [hu.inter hv, hv, hu]

@[stacks 004W "(1)"]
/--
theorem `isIrreducible_iff_closure` / 定理 `isIrreducible_iff_closure`

English:
theorem isIrreducible_iff_closure
  statement: IsIrreducible (closure s) ↔ IsIrreducible s
  proof: and_congr closure_nonempty_iff isPreirreducible_iff_closure

protected alias ⟨_, IsPreirreducible.closure⟩ := isPreirreducible_iff_closure

protected alias ⟨_, IsIrreducible.closure⟩ := isIrreducible_iff_closure

中文:
定理 isIrreducible_iff_closure
  结论: 是不可约 (closure s) ↔ 是不可约 s
  证明: and_congr closure_nonempty_iff isPreirreducible_iff_closure

protected alias ⟨_, IsPreirreducible.closure⟩ := isPreirreducible_iff_closure

protected alias ⟨_, IsIrreducible.closure⟩ := isIrreducible_iff_closure

Depends on / 依赖: and_congr, closure_nonempty_iff, isPreirreducible_iff_closure
-/
theorem isIrreducible_iff_closure : IsIrreducible (closure s) ↔ IsIrreducible s :=
  and_congr closure_nonempty_iff isPreirreducible_iff_closure

protected alias ⟨_, IsPreirreducible.closure⟩ := isPreirreducible_iff_closure

protected alias ⟨_, IsIrreducible.closure⟩ := isIrreducible_iff_closure

/--
theorem `exists_preirreducible` / 定理 `exists_preirreducible`

English:
theorem exists_preirreducible
  given: (s : Set X) (H : IsPreirreducible s)
  proof: let ⟨m, hsm, hm⟩ :=
    zorn_subset_nonempty { t : Set X | IsPreirreducible t }
      (fun c hc hcc _ =>
        ⟨⋃₀ c, fun u v hu hv ⟨y, hy, hyu⟩ ⟨x, hx, hxv⟩ =>
          let ⟨p, hpc, hyp⟩ := mem_sUnion.1 hy
          let ⟨q, hqc, hxq⟩ := mem_sUnion.1 hx
          Or.casesOn (hcc.total hpc hqc)
            (fun hpq : p subseteq q =>
              let ⟨x, hxp, hxuv⟩ := hc hqc u v hu hv ⟨y, hpq hyp, hyu⟩ ⟨x, hxq, hxv⟩
              ⟨x, mem_sUnion_of_mem hxp hqc, hxuv⟩)
            fun hqp : q subseteq p =>
            let ⟨x, hxp, hxuv⟩ := hc hpc u v hu hv ⟨y, hyp, hyu⟩ ⟨x, hqp hxq, hxv⟩
            ⟨x, mem_sUnion_of_mem hxp hpc, hxuv⟩,
          fun _ hxc => subset_sUnion_of_mem hxc⟩)
      s H
  ⟨m, hm.prop, hsm, fun _u hu hmu => (hm.eq_of_subset hu hmu).symm⟩

中文:
定理 存在_preirreducible
  条件: (s : 集合 X) (H : IsPreirreducible s)
  证明: let ⟨m, hsm, hm⟩ :=
    zorn_subset_nonempty { t : Set X | IsPreirreducible t }
      (fun c hc hcc _ =>
        ⟨⋃₀ c, fun u v hu hv ⟨y, hy, hyu⟩ ⟨x, hx, hxv⟩ =>
          let ⟨p, hpc, hyp⟩ := mem_sUnion.1 hy
          let ⟨q, hqc, hxq⟩ := mem_sUnion.1 hx
          Or.casesOn (hcc.total hpc hqc)
            (fun hpq : p subseteq q =>
              let ⟨x, hxp, hxuv⟩ := hc hqc u v hu hv ⟨y, hpq hyp, hyu⟩ ⟨x, hxq, hxv⟩
              ⟨x, mem_sUnion_of_mem hxp hqc, hxuv⟩)
            fun hqp : q subseteq p =>
            let ⟨x, hxp, hxuv⟩ := hc hpc u v hu hv ⟨y, hyp, hyu⟩ ⟨x, hqp hxq, hxv⟩
            ⟨x, mem_sUnion_of_mem hxp hpc, hxuv⟩,
          fun _ hxc => subset_sUnion_of_mem hxc⟩)
      s H
  ⟨m, hm.prop, hsm, fun _u hu hmu => (hm.eq_of_subset hu hmu).symm⟩

Depends on / 依赖: IsPreirreducible, Or.casesOn, casesOn, hcc.total, mem_sUnion, mem_sUnion_of, mem_sUnion_of_mem, subseteq, zorn_subset_nonempty
-/
theorem exists_preirreducible (s : Set X) (H : IsPreirreducible s) :
    exists t : Set X, IsPreirreducible t ∧ s subseteq t ∧ forall u, IsPreirreducible u -> t subseteq u -> u = t :=
  let ⟨m, hsm, hm⟩ :=
    zorn_subset_nonempty { t : Set X | IsPreirreducible t }
      (fun c hc hcc _ =>
        ⟨⋃₀ c, fun u v hu hv ⟨y, hy, hyu⟩ ⟨x, hx, hxv⟩ =>
          let ⟨p, hpc, hyp⟩ := mem_sUnion.1 hy
          let ⟨q, hqc, hxq⟩ := mem_sUnion.1 hx
          Or.casesOn (hcc.total hpc hqc)
            (fun hpq : p subseteq q =>
              let ⟨x, hxp, hxuv⟩ := hc hqc u v hu hv ⟨y, hpq hyp, hyu⟩ ⟨x, hxq, hxv⟩
              ⟨x, mem_sUnion_of_mem hxp hqc, hxuv⟩)
            fun hqp : q subseteq p =>
            let ⟨x, hxp, hxuv⟩ := hc hpc u v hu hv ⟨y, hyp, hyu⟩ ⟨x, hqp hxq, hxv⟩
            ⟨x, mem_sUnion_of_mem hxp hpc, hxuv⟩,
          fun _ hxc => subset_sUnion_of_mem hxc⟩)
      s H
  ⟨m, hm.prop, hsm, fun _u hu hmu => (hm.eq_of_subset hu hmu).symm⟩

/-- The set of irreducible components of a topological space. -/
@[stacks 004V "(2)"]
/--
Definition of `irreducibleComponents` / `irreducibleComponents` 的定义

English:
definition irreducibleComponents
  signature: (X : Type*) [TopologicalSpace X]
  body: {s | Maximal IsIrreducible s}

@[stacks 004W "(2)"]

中文:
定义 irreducibleComponents
  签名: (X : 类型) [拓扑空间 X]
  定义体: {s | Maximal IsIrreducible s}

@[stacks 004W "(2)"]

Depends on / 依赖: IsIrreducible, Maximal
-/
def irreducibleComponents (X : Type*) [TopologicalSpace X] : Set (Set X) :=
  {s | Maximal IsIrreducible s}

@[stacks 004W "(2)"]
/--
theorem `isClosed_of_mem_irreducibleComponents` / 定理 `isClosed_of_mem_irreducibleComponents`

English:
theorem isClosed_of_mem_irreducibleComponents
  given: (s) (H : s in irreducibleComponents X)
  proof: by
  rw [← closure_eq_iff_isClosed]; rw [eq_comm]
  exact subset_closure.antisymm (H.2 H.1.closure subset_closure)

中文:
定理 isClosed_of_mem_irreducibleComponents
  条件: (s) (H : s in irreducibleComponents X)
  证明: by
  rw [← closure_eq_iff_isClosed]; rw [eq_comm]
  exact subset_closure.antisymm (H.2 H.1.closure subset_closure)

Depends on / 依赖: antisymm, closure, closure_eq_iff_isClosed, eq_comm, subset_closure, subset_closure.antisymm
-/
theorem isClosed_of_mem_irreducibleComponents (s) (H : s in irreducibleComponents X) :
    IsClosed s := by
  rw [← closure_eq_iff_isClosed]; rw [eq_comm]
  exact subset_closure.antisymm (H.2 H.1.closure subset_closure)

/--
theorem `irreducibleComponents_eq_maximals_closed` / 定理 `irreducibleComponents_eq_maximals_closed`

English:
theorem irreducibleComponents_eq_maximals_closed
  given: (X : Type*) [TopologicalSpace X]
  proof: by
  ext s
  constructor
  · intro H
    exact ⟨⟨isClosed_of_mem_irreducibleComponents _ H, H.1⟩, fun x h e => H.2 h.2 e⟩
  · intro H
    refine ⟨H.1.2, fun x h e => ?_⟩
    have : closure x <= s := H.2 ⟨isClosed_closure, h.closure⟩ (e.trans subset_closure)
    exact le_trans subset_closure this

@[stacks 004W "(3)"]

中文:
定理 irreducibleComponents_eq_maximals_closed
  条件: (X : 类型) [拓扑空间 X]
  证明: by
  ext s
  constructor
  · intro H
    exact ⟨⟨isClosed_of_mem_irreducibleComponents _ H, H.1⟩, fun x h e => H.2 h.2 e⟩
  · intro H
    refine ⟨H.1.2, fun x h e => ?_⟩
    have : closure x <= s := H.2 ⟨isClosed_closure, h.closure⟩ (e.trans subset_closure)
    exact le_trans subset_closure this

@[stacks 004W "(3)"]

Depends on / 依赖: closure, e.trans, h.closure, isClosed_closure, isClosed_of_mem_irreducibleComponents, le_trans, subset_closure
-/
theorem irreducibleComponents_eq_maximals_closed (X : Type*) [TopologicalSpace X] :
    irreducibleComponents X = { s | Maximal (fun x => IsClosed x ∧ IsIrreducible x) s} := by
  ext s
  constructor
  · intro H
    exact ⟨⟨isClosed_of_mem_irreducibleComponents _ H, H.1⟩, fun x h e => H.2 h.2 e⟩
  · intro H
    refine ⟨H.1.2, fun x h e => ?_⟩
    have : closure x <= s := H.2 ⟨isClosed_closure, h.closure⟩ (e.trans subset_closure)
    exact le_trans subset_closure this

@[stacks 004W "(3)"]
/--
lemma `exists_mem_irreducibleComponents_subset_of_isIrreducible` / 引理 `exists_mem_irreducibleComponents_subset_of_isIrreducible`

English:
lemma exists_mem_irreducibleComponents_subset_of_isIrreducible
  given: (s : Set X) (hs : IsIrreducible s)
  proof: by
  obtain ⟨u, hu⟩ := exists_preirreducible s hs.isPreirreducible
  use u, ⟨⟨hs.left.mono hu.right.left,hu.left⟩,fun _ h hl => (hu.right.right _ h.right hl).le⟩
  exact hu.right.left

中文:
引理 存在_mem_irreducibleComponents_subset_of_isIrreducible
  条件: (s : 集合 X) (hs : 是不可约 s)
  证明: by
  obtain ⟨u, hu⟩ := exists_preirreducible s hs.isPreirreducible
  use u, ⟨⟨hs.left.mono hu.right.left,hu.left⟩,fun _ h hl => (hu.right.right _ h.right hl).le⟩
  exact hu.right.left

Depends on / 依赖: exists_preirreducible, h.right, hs.isPreirreducible, hs.left.mono, hu.left, hu.right.left, hu.right.right, isPreirreducible
-/
lemma exists_mem_irreducibleComponents_subset_of_isIrreducible (s : Set X) (hs : IsIrreducible s) :
    exists u in irreducibleComponents X, s subseteq u := by
  obtain ⟨u, hu⟩ := exists_preirreducible s hs.isPreirreducible
  use u, ⟨⟨hs.left.mono hu.right.left,hu.left⟩,fun _ h hl => (hu.right.right _ h.right hl).le⟩
  exact hu.right.left

/-- A maximal irreducible set that contains a given point. -/
@[stacks 004W "(4)"]
-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- See https://github.com/leanprover/lean4/issues/14084.
/--
Definition of `irreducibleComponent` / `irreducibleComponent` 的定义

English:
definition irreducibleComponent
  signature: (x : X)
  body: Classical.choose (exists_preirreducible {x} isPreirreducible_singleton)

中文:
定义 irreducibleComponent
  签名: (x : X)
  定义体: Classical.choose (exists_preirreducible {x} isPreirreducible_singleton)

Depends on / 依赖: Classical, Classical.choose, exists_preirreducible, isPreirreducible_singleton
-/
noncomputable def irreducibleComponent (x : X) : Set X :=
  Classical.choose (exists_preirreducible {x} isPreirreducible_singleton)

/--
theorem `irreducibleComponent_property` / 定理 `irreducibleComponent_property`

English:
theorem irreducibleComponent_property
  given: (x : X)
  proof: Classical.choose_spec (exists_preirreducible {x} isPreirreducible_singleton)

@[stacks 004W "(4)"]

中文:
定理 irreducibleComponent_property
  条件: (x : X)
  证明: Classical.choose_spec (exists_preirreducible {x} isPreirreducible_singleton)

@[stacks 004W "(4)"]

Depends on / 依赖: Classical, Classical.choose_spec, choose_spec, exists_preirreducible, isPreirreducible_singleton
-/
theorem irreducibleComponent_property (x : X) :
    IsPreirreducible (irreducibleComponent x) ∧
      {x} subseteq irreducibleComponent x ∧
        forall u, IsPreirreducible u -> irreducibleComponent x subseteq u -> u = irreducibleComponent x :=
  Classical.choose_spec (exists_preirreducible {x} isPreirreducible_singleton)

@[stacks 004W "(4)"]
/--
theorem `mem_irreducibleComponent` / 定理 `mem_irreducibleComponent`

English:
theorem mem_irreducibleComponent
  given: {x : X}
  statement: x in irreducibleComponent x
  proof: singleton_subset_iff.1 (irreducibleComponent_property x).2.1

中文:
定理 mem_irreducibleComponent
  条件: {x : X}
  结论: x in irreducibleComponent x
  证明: singleton_subset_iff.1 (irreducibleComponent_property x).2.1

Depends on / 依赖: irreducibleComponent_property, singleton_subset_iff
-/
theorem mem_irreducibleComponent {x : X} : x in irreducibleComponent x :=
  singleton_subset_iff.1 (irreducibleComponent_property x).2.1

/--
theorem `isIrreducible_irreducibleComponent` / 定理 `isIrreducible_irreducibleComponent`

English:
theorem isIrreducible_irreducibleComponent
  given: {x : X}
  statement: IsIrreducible (irreducibleComponent x)
  proof: ⟨⟨x, mem_irreducibleComponent⟩, (irreducibleComponent_property x).1⟩

中文:
定理 isIrreducible_irreducibleComponent
  条件: {x : X}
  结论: 是不可约 (irreducibleComponent x)
  证明: ⟨⟨x, mem_irreducibleComponent⟩, (irreducibleComponent_property x).1⟩

Depends on / 依赖: irreducibleComponent_property, mem_irreducibleComponent
-/
theorem isIrreducible_irreducibleComponent {x : X} : IsIrreducible (irreducibleComponent x) :=
  ⟨⟨x, mem_irreducibleComponent⟩, (irreducibleComponent_property x).1⟩

/--
theorem `eq_irreducibleComponent` / 定理 `eq_irreducibleComponent`

English:
theorem eq_irreducibleComponent
  given: {x : X}
  proof: (irreducibleComponent_property x).2.2 _

中文:
定理 eq_irreducibleComponent
  条件: {x : X}
  证明: (irreducibleComponent_property x).2.2 _

Depends on / 依赖: irreducibleComponent_property
-/
theorem eq_irreducibleComponent {x : X} :
    IsPreirreducible s -> irreducibleComponent x subseteq s -> s = irreducibleComponent x :=
  (irreducibleComponent_property x).2.2 _

/--
theorem `irreducibleComponent_mem_irreducibleComponents` / 定理 `irreducibleComponent_mem_irreducibleComponents`

English:
theorem irreducibleComponent_mem_irreducibleComponents
  given: (x : X)
  proof: ⟨isIrreducible_irreducibleComponent, fun _ h₁ h₂ => (eq_irreducibleComponent h₁.2 h₂).le⟩

中文:
定理 irreducibleComponent_mem_irreducibleComponents
  条件: (x : X)
  证明: ⟨isIrreducible_irreducibleComponent, fun _ h₁ h₂ => (eq_irreducibleComponent h₁.2 h₂).le⟩

Depends on / 依赖: eq_irreducibleComponent, isIrreducible_irreducibleComponent
-/
theorem irreducibleComponent_mem_irreducibleComponents (x : X) :
    irreducibleComponent x in irreducibleComponents X :=
  ⟨isIrreducible_irreducibleComponent, fun _ h₁ h₂ => (eq_irreducibleComponent h₁.2 h₂).le⟩

/--
theorem `isClosed_irreducibleComponent` / 定理 `isClosed_irreducibleComponent`

English:
theorem isClosed_irreducibleComponent
  given: {x : X}
  statement: IsClosed (irreducibleComponent x)
  proof: isClosed_of_mem_irreducibleComponents _ (irreducibleComponent_mem_irreducibleComponents x)

中文:
定理 isClosed_irreducibleComponent
  条件: {x : X}
  结论: 是闭集 (irreducibleComponent x)
  证明: isClosed_of_mem_irreducibleComponents _ (irreducibleComponent_mem_irreducibleComponents x)

Depends on / 依赖: irreducibleComponent_mem_irreducibleComponents, isClosed_of_mem_irreducibleComponents
-/
theorem isClosed_irreducibleComponent {x : X} : IsClosed (irreducibleComponent x) :=
  isClosed_of_mem_irreducibleComponents _ (irreducibleComponent_mem_irreducibleComponents x)

/-- A preirreducible space is one where there is no non-trivial pair of disjoint opens. -/
@[mk_iff]
/--
Definition of `PreirreducibleSpace` / `PreirreducibleSpace` 的定义

English:
class PreirreducibleSpace
  parameters: (X : Type*) [TopologicalSpace X]
  axioms and operations (1):
    - isPreirreducible_univ : IsPreirreducible (univ : Set X)

中文:
类 Preirreducible空间
  参数: (X : 类型) [拓扑空间 X]
  公理与运算 (1 个):
    - isPreirreducible_univ : IsPreirreducible (univ : 集合 X)
-/
class PreirreducibleSpace (X : Type*) [TopologicalSpace X] : Prop where
  /-- In a preirreducible space, `Set.univ` is a preirreducible set. -/
  isPreirreducible_univ : IsPreirreducible (univ : Set X)

/-- An irreducible space is one that is nonempty
and where there is no non-trivial pair of disjoint opens. -/
@[stacks 004V "(1) as predicate on a space"]
/--
Definition of `IrreducibleSpace` / `IrreducibleSpace` 的定义

English:
class IrreducibleSpace
  parameters: (X : Type*) [TopologicalSpace X]
  extends: PreirreducibleSpace X
  axioms and operations (1):
    - toNonempty : Nonempty X

中文:
类 不可约空间
  参数: (X : 类型) [拓扑空间 X]
  继承: Preirreducible空间 X
  公理与运算 (1 个):
    - toNonempty : 非空 X
-/
class IrreducibleSpace (X : Type*) [TopologicalSpace X] : Prop extends PreirreducibleSpace X where
  toNonempty : Nonempty X

-- see Note [lower instance priority]
attribute [instance 50] IrreducibleSpace.toNonempty

/--
theorem `IrreducibleSpace.isIrreducible_univ` / 定理 `IrreducibleSpace.isIrreducible_univ`

English:
theorem IrreducibleSpace.isIrreducible_univ
  given: (X : Type*) [TopologicalSpace X] [IrreducibleSpace X]
  proof: ⟨univ_nonempty, PreirreducibleSpace.isPreirreducible_univ⟩

中文:
定理 不可约空间.isIrreducible_univ
  条件: (X : 类型) [拓扑空间 X] [不可约空间 X]
  证明: ⟨univ_nonempty, PreirreducibleSpace.isPreirreducible_univ⟩

Depends on / 依赖: PreirreducibleSpace, PreirreducibleSpace.isPreirreducible_univ, isPreirreducible_univ, univ_nonempty
-/
theorem IrreducibleSpace.isIrreducible_univ (X : Type*) [TopologicalSpace X] [IrreducibleSpace X] :
    IsIrreducible (univ : Set X) :=
  ⟨univ_nonempty, PreirreducibleSpace.isPreirreducible_univ⟩

/--
theorem `irreducibleSpace_def` / 定理 `irreducibleSpace_def`

English:
theorem irreducibleSpace_def
  given: (X : Type*) [TopologicalSpace X]
  proof: ⟨@IrreducibleSpace.isIrreducible_univ X _, fun h =>
    haveI : PreirreducibleSpace X := ⟨h.2⟩
    ⟨⟨h.1.some⟩⟩⟩

中文:
定理 irreducibleSpace_def
  条件: (X : 类型) [拓扑空间 X]
  证明: ⟨@IrreducibleSpace.isIrreducible_univ X _, fun h =>
    haveI : PreirreducibleSpace X := ⟨h.2⟩
    ⟨⟨h.1.some⟩⟩⟩

Depends on / 依赖: IrreducibleSpace, IrreducibleSpace.isIrreducible_univ, PreirreducibleSpace, isIrreducible_univ
-/
theorem irreducibleSpace_def (X : Type*) [TopologicalSpace X] :
    IrreducibleSpace X ↔ IsIrreducible (⊤ : Set X) :=
  ⟨@IrreducibleSpace.isIrreducible_univ X _, fun h =>
    haveI : PreirreducibleSpace X := ⟨h.2⟩
    ⟨⟨h.1.some⟩⟩⟩

/--
lemma `PreirreducibleSpace.of_forall_nonempty_inter` / 引理 `PreirreducibleSpace.of_forall_nonempty_inter`

English:
lemma PreirreducibleSpace.of_forall_nonempty_inter
  proof: by simp_all

中文:
引理 Preirreducible空间.of_对任意_nonempty_inter
  证明: by simp_all
-/
lemma PreirreducibleSpace.of_forall_nonempty_inter
    (H : forall ⦃U V : Set X⦄, IsOpen U -> IsOpen V -> U.Nonempty -> V.Nonempty -> (U inter V).Nonempty) :
    PreirreducibleSpace X where
  isPreirreducible_univ _ := by simp_all

/--
theorem `nonempty_preirreducible_inter` / 定理 `nonempty_preirreducible_inter`

English:
theorem nonempty_preirreducible_inter
  given: [PreirreducibleSpace X]
  proof: by
  simpa only [univ_inter, univ_subset_iff] using
    @PreirreducibleSpace.isPreirreducible_univ X _ _ s t

中文:
定理 nonempty_preirreducible_inter
  条件: [Preirreducible空间 X]
  证明: by
  simpa only [univ_inter, univ_subset_iff] using
    @PreirreducibleSpace.isPreirreducible_univ X _ _ s t

Depends on / 依赖: PreirreducibleSpace, PreirreducibleSpace.isPreirreducible_univ, isPreirreducible_univ, univ_inter, univ_subset_iff
-/
theorem nonempty_preirreducible_inter [PreirreducibleSpace X] :
    IsOpen s -> IsOpen t -> s.Nonempty -> t.Nonempty -> (s inter t).Nonempty := by
  simpa only [univ_inter, univ_subset_iff] using
    @PreirreducibleSpace.isPreirreducible_univ X _ _ s t

/--
theorem `IsOpen.dense` / 定理 `IsOpen.dense`

English:
theorem IsOpen.dense
  given: [PreirreducibleSpace X] (ho : IsOpen s) (hne : s.Nonempty)
  proof: dense_iff_inter_open.2 fun _t hto htne => nonempty_preirreducible_inter hto ho htne hne

中文:
定理 是开集.dense
  条件: [Preirreducible空间 X] (ho : 是开集 s) (hne : s.非空)
  证明: dense_iff_inter_open.2 fun _t hto htne => nonempty_preirreducible_inter hto ho htne hne
-/
protected theorem IsOpen.dense [PreirreducibleSpace X] (ho : IsOpen s) (hne : s.Nonempty) :
    Dense s :=
  dense_iff_inter_open.2 fun _t hto htne => nonempty_preirreducible_inter hto ho htne hne

/--
lemma `IsOpenMap.denseRange_of_isPreirreducibleSpace` / 引理 `IsOpenMap.denseRange_of_isPreirreducibleSpace`

English:
lemma IsOpenMap.denseRange_of_isPreirreducibleSpace
  statement: {U X : Type*} [TopologicalSpace U]
  proof: hf.isOpen_range.dense (Set.range_nonempty f)

中文:
引理 是开映射.denseRange_of_isPreirreducibleSpace
  结论: {U X : 类型} [拓扑空间 U]
  证明: hf.isOpen_range.dense (Set.range_nonempty f)

Depends on / 依赖: Set.range_nonempty, hf.isOpen_range.dense, isOpen_range, range_nonempty
-/
lemma IsOpenMap.denseRange_of_isPreirreducibleSpace {U X : Type*} [TopologicalSpace U]
    [Nonempty U] [TopologicalSpace X] (f : U -> X) (hf : IsOpenMap f) [PreirreducibleSpace X] :
    DenseRange f :=
  hf.isOpen_range.dense (Set.range_nonempty f)

/--
theorem `IsPreirreducible.image` / 定理 `IsPreirreducible.image`

English:
theorem IsPreirreducible.image
  given: (H : IsPreirreducible s) (f : X -> Y) (hf : ContinuousOn f s)
  proof: by
  rintro u v hu hv ⟨_, ⟨⟨x, hx, rfl⟩, hxu⟩⟩ ⟨_, ⟨⟨y, hy, rfl⟩, hyv⟩⟩
  rw [← mem_preimage] at hxu hyv
  rcases continuousOn_iff'.1 hf u hu with ⟨u', hu', u'_eq⟩
  rcases continuousOn_iff'.1 hf v hv with ⟨v', hv', v'_eq⟩
  have := H u' v' hu' hv'
  rw [inter_comm s u']; rw [← u'_eq] at this
  rw [inter_comm s v']; rw [← v'_eq] at this
  rcases this ⟨x, hxu, hx⟩ ⟨y, hyv, hy⟩ with ⟨x, hxs, hxu', hxv'⟩
  refine ⟨f x, mem_image_of_mem f hxs, ?_, ?_⟩
  all_goals
    rw [← mem_preimage]
    apply mem_of_mem_inter_left
    show x in _ inter s
    simp [*]

@[stacks 0379]

中文:
定理 IsPreirreducible.像
  条件: (H : IsPreirreducible s) (f : X -> Y) (hf : ContinuousOn f s)
  证明: by
  rintro u v hu hv ⟨_, ⟨⟨x, hx, rfl⟩, hxu⟩⟩ ⟨_, ⟨⟨y, hy, rfl⟩, hyv⟩⟩
  rw [← mem_preimage] at hxu hyv
  rcases continuousOn_iff'.1 hf u hu with ⟨u', hu', u'_eq⟩
  rcases continuousOn_iff'.1 hf v hv with ⟨v', hv', v'_eq⟩
  have := H u' v' hu' hv'
  rw [inter_comm s u']; rw [← u'_eq] at this
  rw [inter_comm s v']; rw [← v'_eq] at this
  rcases this ⟨x, hxu, hx⟩ ⟨y, hyv, hy⟩ with ⟨x, hxs, hxu', hxv'⟩
  refine ⟨f x, mem_image_of_mem f hxs, ?_, ?_⟩
  all_goals
    rw [← mem_preimage]
    apply mem_of_mem_inter_left
    show x in _ inter s
    simp [*]

@[stacks 0379]

Depends on / 依赖: all_goals, continuousOn_iff, inter_comm, mem_image_of_mem, mem_of_mem_inter_left, mem_preimage
-/
theorem IsPreirreducible.image (H : IsPreirreducible s) (f : X -> Y) (hf : ContinuousOn f s) :
    IsPreirreducible (f '' s) := by
  rintro u v hu hv ⟨_, ⟨⟨x, hx, rfl⟩, hxu⟩⟩ ⟨_, ⟨⟨y, hy, rfl⟩, hyv⟩⟩
  rw [← mem_preimage] at hxu hyv
  rcases continuousOn_iff'.1 hf u hu with ⟨u', hu', u'_eq⟩
  rcases continuousOn_iff'.1 hf v hv with ⟨v', hv', v'_eq⟩
  have := H u' v' hu' hv'
  rw [inter_comm s u']; rw [← u'_eq] at this
  rw [inter_comm s v']; rw [← v'_eq] at this
  rcases this ⟨x, hxu, hx⟩ ⟨y, hyv, hy⟩ with ⟨x, hxs, hxu', hxv'⟩
  refine ⟨f x, mem_image_of_mem f hxs, ?_, ?_⟩
  all_goals
    rw [← mem_preimage]
    apply mem_of_mem_inter_left
    show x in _ inter s
    simp [*]

@[stacks 0379]
/--
theorem `IsIrreducible.image` / 定理 `IsIrreducible.image`

English:
theorem IsIrreducible.image
  given: (H : IsIrreducible s) (f : X -> Y) (hf : ContinuousOn f s)
  proof: ⟨H.nonempty.image _, H.isPreirreducible.image f hf⟩

中文:
定理 是不可约.像
  条件: (H : 是不可约 s) (f : X -> Y) (hf : ContinuousOn f s)
  证明: ⟨H.nonempty.image _, H.isPreirreducible.image f hf⟩

Depends on / 依赖: H.isPreirreducible.image, H.nonempty.image, isPreirreducible, nonempty
-/
theorem IsIrreducible.image (H : IsIrreducible s) (f : X -> Y) (hf : ContinuousOn f s) :
    IsIrreducible (f '' s) :=
  ⟨H.nonempty.image _, H.isPreirreducible.image f hf⟩

/--
theorem `Subtype.preirreducibleSpace` / 定理 `Subtype.preirreducibleSpace`

English:
theorem Subtype.preirreducibleSpace
  given: (h : IsPreirreducible s)
  statement: PreirreducibleSpace s where
  proof: by
    rintro _ _ ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩ ⟨⟨x, hxs⟩, -, hxu⟩ ⟨⟨y, hys⟩, -, hyv⟩
    rcases h u v hu hv ⟨x, hxs, hxu⟩ ⟨y, hys, hyv⟩ with ⟨x, hxs, ⟨hxu, hxv⟩⟩
    exact ⟨⟨x, hxs⟩, ⟨Set.mem_univ _, ⟨hxu, hxv⟩⟩⟩

中文:
定理 子类型.preirreducibleSpace
  条件: (h : IsPreirreducible s)
  结论: Preirreducible空间 s where
  证明: by
    rintro _ _ ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩ ⟨⟨x, hxs⟩, -, hxu⟩ ⟨⟨y, hys⟩, -, hyv⟩
    rcases h u v hu hv ⟨x, hxs, hxu⟩ ⟨y, hys, hyv⟩ with ⟨x, hxs, ⟨hxu, hxv⟩⟩
    exact ⟨⟨x, hxs⟩, ⟨Set.mem_univ _, ⟨hxu, hxv⟩⟩⟩

Depends on / 依赖: Set.mem_univ, mem_univ
-/
theorem Subtype.preirreducibleSpace (h : IsPreirreducible s) : PreirreducibleSpace s where
  isPreirreducible_univ := by
    rintro _ _ ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩ ⟨⟨x, hxs⟩, -, hxu⟩ ⟨⟨y, hys⟩, -, hyv⟩
    rcases h u v hu hv ⟨x, hxs, hxu⟩ ⟨y, hys, hyv⟩ with ⟨x, hxs, ⟨hxu, hxv⟩⟩
    exact ⟨⟨x, hxs⟩, ⟨Set.mem_univ _, ⟨hxu, hxv⟩⟩⟩

/--
theorem `Subtype.irreducibleSpace` / 定理 `Subtype.irreducibleSpace`

English:
theorem Subtype.irreducibleSpace
  given: (h : IsIrreducible s)
  statement: IrreducibleSpace s where
  proof: (Subtype.preirreducibleSpace h.isPreirreducible).isPreirreducible_univ
  toNonempty := h.nonempty.to_subtype

中文:
定理 子类型.irreducibleSpace
  条件: (h : 是不可约 s)
  结论: 不可约空间 s where
  证明: (Subtype.preirreducibleSpace h.isPreirreducible).isPreirreducible_univ
  toNonempty := h.nonempty.to_subtype

Depends on / 依赖: Subtype, Subtype.preirreducibleSpace, h.isPreirreducible, h.nonempty.to_subtype, isPreirreducible, isPreirreducible_univ, nonempty, preirreducibleSpace, toNonempty, to_subtype
-/
theorem Subtype.irreducibleSpace (h : IsIrreducible s) : IrreducibleSpace s where
  isPreirreducible_univ :=
    (Subtype.preirreducibleSpace h.isPreirreducible).isPreirreducible_univ
  toNonempty := h.nonempty.to_subtype

/--
lemma `IsPreirreducible.of_subtype` / 引理 `IsPreirreducible.of_subtype`

English:
lemma IsPreirreducible.of_subtype
  given: [PreirreducibleSpace s]
  statement: IsPreirreducible s
  proof: by
  rw [← Subtype.range_coe (s := s)]; rw [← Set.image_univ]
  refine PreirreducibleSpace.isPreirreducible_univ.image Subtype.val ?_
  exact continuous_subtype_val.continuousOn

中文:
引理 IsPreirreducible.of_subtype
  条件: [Preirreducible空间 s]
  结论: IsPreirreducible s
  证明: by
  rw [← Subtype.range_coe (s := s)]; rw [← Set.image_univ]
  refine PreirreducibleSpace.isPreirreducible_univ.image Subtype.val ?_
  exact continuous_subtype_val.continuousOn

Depends on / 依赖: PreirreducibleSpace, PreirreducibleSpace.isPreirreducible_univ.image, Set.image_univ, Subtype, Subtype.range_coe, Subtype.val, continuousOn, continuous_subtype_val, continuous_subtype_val.continuousOn, image_univ, isPreirreducible_univ, range_coe
-/
lemma IsPreirreducible.of_subtype [PreirreducibleSpace s] : IsPreirreducible s := by
  rw [← Subtype.range_coe (s := s)]; rw [← Set.image_univ]
  refine PreirreducibleSpace.isPreirreducible_univ.image Subtype.val ?_
  exact continuous_subtype_val.continuousOn

/--
lemma `IsIrreducible.of_subtype` / 引理 `IsIrreducible.of_subtype`

English:
lemma IsIrreducible.of_subtype
  given: [IrreducibleSpace s]
  statement: IsIrreducible s
  proof: by
  exact ⟨.of_subtype, .of_subtype⟩

中文:
引理 是不可约.of_subtype
  条件: [不可约空间 s]
  结论: 是不可约 s
  证明: by
  exact ⟨.of_subtype, .of_subtype⟩

Depends on / 依赖: of_subtype
-/
lemma IsIrreducible.of_subtype [IrreducibleSpace s] : IsIrreducible s := by
  exact ⟨.of_subtype, .of_subtype⟩

/--
theorem `isPreirreducible_iff_preirreducibleSpace` / 定理 `isPreirreducible_iff_preirreducibleSpace`

English:
theorem isPreirreducible_iff_preirreducibleSpace
  proof: ⟨Subtype.preirreducibleSpace, fun _ => .of_subtype⟩

中文:
定理 isPreirreducible_iff_preirreducibleSpace
  证明: ⟨Subtype.preirreducibleSpace, fun _ => .of_subtype⟩

Depends on / 依赖: Subtype, Subtype.preirreducibleSpace, of_subtype, preirreducibleSpace
-/
theorem isPreirreducible_iff_preirreducibleSpace :
    IsPreirreducible s ↔ PreirreducibleSpace s :=
  ⟨Subtype.preirreducibleSpace, fun _ => .of_subtype⟩

/--
theorem `isIrreducible_iff_irreducibleSpace` / 定理 `isIrreducible_iff_irreducibleSpace`

English:
theorem isIrreducible_iff_irreducibleSpace
  proof: ⟨Subtype.irreducibleSpace, fun _ => .of_subtype⟩

中文:
定理 isIrreducible_iff_irreducibleSpace
  证明: ⟨Subtype.irreducibleSpace, fun _ => .of_subtype⟩

Depends on / 依赖: Subtype, Subtype.irreducibleSpace, irreducibleSpace, of_subtype
-/
theorem isIrreducible_iff_irreducibleSpace :
    IsIrreducible s ↔ IrreducibleSpace s :=
  ⟨Subtype.irreducibleSpace, fun _ => .of_subtype⟩

instance (priority := low) [Subsingleton X] : PreirreducibleSpace X :=
  ⟨(Set.subsingleton_univ_iff.mpr ‹_›).isPreirreducible⟩

instance (priority := 100) [IndiscreteTopology X] : PreirreducibleSpace X where
  isPreirreducible_univ u v := by
    simp only [IndiscreteTopology.isOpen_iff, univ_inter]
    rintro ⟨h | h⟩ <;> simp_all

/-- An infinite type with cofinite topology is an irreducible topological space. -/
instance (priority := 100) {X} [Infinite X] : IrreducibleSpace (CofiniteTopology X) where
  isPreirreducible_univ u v := by
    simp only [CofiniteTopology.isOpen_iff, univ_inter]
    intro hu hv hu' hv'
    simpa only [compl_union, compl_compl] using ((hu hu').union (hv hv')).infinite_compl.nonempty
  toNonempty := inferInstance

/--
theorem `irreducibleComponents_eq_singleton` / 定理 `irreducibleComponents_eq_singleton`

English:
theorem irreducibleComponents_eq_singleton
  given: [IrreducibleSpace X]
  proof: Set.ext fun _ => IsGreatest.maximal_iff (s := {s : Set X | IsIrreducible s})
    ⟨IrreducibleSpace.isIrreducible_univ X, fun _ _ => Set.subset_univ _⟩

中文:
定理 irreducibleComponents_eq_singleton
  条件: [不可约空间 X]
  证明: Set.ext fun _ => IsGreatest.maximal_iff (s := {s : Set X | IsIrreducible s})
    ⟨IrreducibleSpace.isIrreducible_univ X, fun _ _ => Set.subset_univ _⟩

Depends on / 依赖: IrreducibleSpace, IrreducibleSpace.isIrreducible_univ, IsGreatest, IsGreatest.maximal_iff, IsIrreducible, Set.ext, Set.subset_univ, isIrreducible_univ, maximal_iff, subset_univ
-/
theorem irreducibleComponents_eq_singleton [IrreducibleSpace X] :
    irreducibleComponents X = {univ} :=
  Set.ext fun _ => IsGreatest.maximal_iff (s := {s : Set X | IsIrreducible s})
    ⟨IrreducibleSpace.isIrreducible_univ X, fun _ _ => Set.subset_univ _⟩

/--
theorem `isIrreducible_iff_sInter` / 定理 `isIrreducible_iff_sInter`

English:
theorem isIrreducible_iff_sInter
  proof: by
  refine ⟨fun h U hu hU => ?_, fun h => ⟨?_, ?_⟩⟩
  · induction U using Finset.induction_on with
    | empty => simpa using h.nonempty
    | insert u U _ IH =>
      rw [Finset.coe_insert]; rw [sInter_insert]
      rw [Finset.forall_mem_insert] at hu hU
      exact h.2 _ _ hu.1 (U.finite_toSet.isOpen_sInter hu.2) hU.1 (IH hu.2 hU.2)
  · simpa using h ∅
  · intro u v hu hv hu' hv'
    simpa [*] using h {u, v}

中文:
定理 isIrreducible_iff_s整数er
  证明: by
  refine ⟨fun h U hu hU => ?_, fun h => ⟨?_, ?_⟩⟩
  · induction U using Finset.induction_on with
    | empty => simpa using h.nonempty
    | insert u U _ IH =>
      rw [Finset.coe_insert]; rw [sInter_insert]
      rw [Finset.forall_mem_insert] at hu hU
      exact h.2 _ _ hu.1 (U.finite_toSet.isOpen_sInter hu.2) hU.1 (IH hu.2 hU.2)
  · simpa using h ∅
  · intro u v hu hv hu' hv'
    simpa [*] using h {u, v}

Depends on / 依赖: Finset, Finset.coe_insert, Finset.forall_mem_insert, Finset.induction_on, U.finite_toSet.isOpen_sInter, coe_insert, finite_toSet, forall_mem_insert, h.nonempty, induction_on, insert, isOpen_sInter, nonempty, sInter_insert
-/
theorem isIrreducible_iff_sInter :
    IsIrreducible s ↔
      forall (U : Finset (Set X)), (forall u in U, IsOpen u) -> (forall u in U, (s inter u).Nonempty) ->
        (s inter ⋂₀ ↑U).Nonempty := by
  refine ⟨fun h U hu hU => ?_, fun h => ⟨?_, ?_⟩⟩
  · induction U using Finset.induction_on with
    | empty => simpa using h.nonempty
    | insert u U _ IH =>
      rw [Finset.coe_insert]; rw [sInter_insert]
      rw [Finset.forall_mem_insert] at hu hU
      exact h.2 _ _ hu.1 (U.finite_toSet.isOpen_sInter hu.2) hU.1 (IH hu.2 hU.2)
  · simpa using h ∅
  · intro u v hu hv hu' hv'
    simpa [*] using h {u, v}

/--
theorem `isPreirreducible_iff_isClosed_union_isClosed` / 定理 `isPreirreducible_iff_isClosed_union_isClosed`

English:
theorem isPreirreducible_iff_isClosed_union_isClosed
  proof: by
refine compl_surjective.forall.trans forall_congr' fun z₁ => compl_surjective.forall.trans
    forall_congr' fun z₂ => ?_
  simp only [isOpen_compl_iff, ← compl_union, inter_compl_nonempty_iff]
  refine forall₂_congr fun _ _ => ?_
  rw [← and_imp]; rw [← not_or]; rw [not_imp_not]

中文:
定理 isPreirreducible_iff_isClosed_union_isClosed
  证明: by
refine compl_surjective.forall.trans forall_congr' fun z₁ => compl_surjective.forall.trans
    forall_congr' fun z₂ => ?_
  simp only [isOpen_compl_iff, ← compl_union, inter_compl_nonempty_iff]
  refine forall₂_congr fun _ _ => ?_
  rw [← and_imp]; rw [← not_or]; rw [not_imp_not]

Depends on / 依赖: and_imp, compl_surjective, compl_surjective.forall.trans, compl_union, forall_congr, inter_compl_nonempty_iff, isOpen_compl_iff, not_imp_not, not_or
-/
theorem isPreirreducible_iff_isClosed_union_isClosed :
    IsPreirreducible s ↔
      forall z₁ z₂ : Set X, IsClosed z₁ -> IsClosed z₂ -> s subseteq z₁ union z₂ -> s subseteq z₁ ∨ s subseteq z₂ := by
refine compl_surjective.forall.trans forall_congr' fun z₁ => compl_surjective.forall.trans
    forall_congr' fun z₂ => ?_
  simp only [isOpen_compl_iff, ← compl_union, inter_compl_nonempty_iff]
  refine forall₂_congr fun _ _ => ?_
  rw [← and_imp]; rw [← not_or]; rw [not_imp_not]

/--
theorem `isIrreducible_iff_sUnion_isClosed` / 定理 `isIrreducible_iff_sUnion_isClosed`

English:
theorem isIrreducible_iff_sUnion_isClosed
  proof: by
  simp only [isIrreducible_iff_sInter]
  refine ((@compl_involutive (Set X) _).toPerm _).finsetCongr.forall_congr fun {t} => ?_
  simp_rw [Equiv.finsetCongr_apply, Finset.forall_mem_map, Finset.mem_map, Finset.coe_map,
    sUnion_image, Equiv.coe_toEmbedding, Function.Involutive.coe_toPerm, isClosed_compl_iff,
    exists_exists_and_eq_and]
  refine forall_congr' fun _ => Iff.trans ?_ not_imp_not
  simp only [not_exists, not_and, ← compl_iInter₂, ← sInter_eq_biInter,
    subset_compl_iff_disjoint_right, not_disjoint_iff_nonempty_inter]

中文:
定理 isIrreducible_iff_sUnion_isClosed
  证明: by
  simp only [isIrreducible_iff_sInter]
  refine ((@compl_involutive (Set X) _).toPerm _).finsetCongr.forall_congr fun {t} => ?_
  simp_rw [Equiv.finsetCongr_apply, Finset.forall_mem_map, Finset.mem_map, Finset.coe_map,
    sUnion_image, Equiv.coe_toEmbedding, Function.Involutive.coe_toPerm, isClosed_compl_iff,
    exists_exists_and_eq_and]
  refine forall_congr' fun _ => Iff.trans ?_ not_imp_not
  simp only [not_exists, not_and, ← compl_iInter₂, ← sInter_eq_biInter,
    subset_compl_iff_disjoint_right, not_disjoint_iff_nonempty_inter]

Depends on / 依赖: Equiv.coe_toEmbedding, Equiv.finsetCongr_apply, Finset, Finset.coe_map, Finset.forall_mem_map, Finset.mem_map, Function, Function.Involutive.coe_toPerm, Iff.trans, Involutive, coe_map, coe_toEmbedding, coe_toPerm, compl_involutive, exists_exists_and_eq_and, finsetCongr, finsetCongr.forall_congr, finsetCongr_apply, forall_congr, forall_mem_map
-/
theorem isIrreducible_iff_sUnion_isClosed :
    IsIrreducible s ↔
      forall t : Finset (Set X), (forall z in t, IsClosed z) -> (s subseteq ⋃₀ ↑t) -> exists z in t, s subseteq z := by
  simp only [isIrreducible_iff_sInter]
  refine ((@compl_involutive (Set X) _).toPerm _).finsetCongr.forall_congr fun {t} => ?_
  simp_rw [Equiv.finsetCongr_apply, Finset.forall_mem_map, Finset.mem_map, Finset.coe_map,
    sUnion_image, Equiv.coe_toEmbedding, Function.Involutive.coe_toPerm, isClosed_compl_iff,
    exists_exists_and_eq_and]
  refine forall_congr' fun _ => Iff.trans ?_ not_imp_not
  simp only [not_exists, not_and, ← compl_iInter₂, ← sInter_eq_biInter,
    subset_compl_iff_disjoint_right, not_disjoint_iff_nonempty_inter]

/--
theorem `subset_closure_inter_of_isPreirreducible_of_isOpen` / 定理 `subset_closure_inter_of_isPreirreducible_of_isOpen`

English:
theorem subset_closure_inter_of_isPreirreducible_of_isOpen
  statement: {S U : Set X} (hS : IsPreirreducible S)
  proof: by
  by_contra h'
  obtain ⟨x, h₁, h₂, h₃⟩ :=
    hS _ (closure (S inter U))ᶜ hU isClosed_closure.isOpen_compl h (inter_compl_nonempty_iff.mpr h')
  exact h₃ (subset_closure ⟨h₁, h₂⟩)

中文:
定理 subset_closure_inter_of_isPreirreducible_of_isOpen
  结论: {S U : 集合 X} (hS : IsPreirreducible S)
  证明: by
  by_contra h'
  obtain ⟨x, h₁, h₂, h₃⟩ :=
    hS _ (closure (S inter U))ᶜ hU isClosed_closure.isOpen_compl h (inter_compl_nonempty_iff.mpr h')
  exact h₃ (subset_closure ⟨h₁, h₂⟩)

Depends on / 依赖: closure, inter_compl_nonempty_iff, inter_compl_nonempty_iff.mpr, isClosed_closure, isClosed_closure.isOpen_compl, isOpen_compl, subset_closure
-/
theorem subset_closure_inter_of_isPreirreducible_of_isOpen {S U : Set X} (hS : IsPreirreducible S)
    (hU : IsOpen U) (h : (S inter U).Nonempty) : S subseteq closure (S inter U) := by
  by_contra h'
  obtain ⟨x, h₁, h₂, h₃⟩ :=
    hS _ (closure (S inter U))ᶜ hU isClosed_closure.isOpen_compl h (inter_compl_nonempty_iff.mpr h')
  exact h₃ (subset_closure ⟨h₁, h₂⟩)

/--
theorem `isPreirreducible_iff_subset_closure_inter_open` / 定理 `isPreirreducible_iff_subset_closure_inter_open`

English:
theorem isPreirreducible_iff_subset_closure_inter_open
  given: (S : Set X)
  proof: by
  refine ⟨fun h _ => ?_, fun h => ?_⟩
  · exact subset_closure_inter_of_isPreirreducible_of_isOpen h
  · intro a b ha hb ⟨p, pS, pa⟩ bS
    by_contra! h0
suffices p ∉ closure (S inter b) from this (h b hb bS) pS
    simp only [closure, mem_sInter, mem_ofPred_eq, and_imp, not_forall, exists_prop]
    use aᶜ
    grind [isClosed_compl_iff, subset_compl_iff_disjoint_left, disjoint_iff_inter_eq_empty]

中文:
定理 isPreirreducible_iff_subset_closure_inter_open
  条件: (S : 集合 X)
  证明: by
  refine ⟨fun h _ => ?_, fun h => ?_⟩
  · exact subset_closure_inter_of_isPreirreducible_of_isOpen h
  · intro a b ha hb ⟨p, pS, pa⟩ bS
    by_contra! h0
suffices p ∉ closure (S inter b) from this (h b hb bS) pS
    simp only [closure, mem_sInter, mem_ofPred_eq, and_imp, not_forall, exists_prop]
    use aᶜ
    grind [isClosed_compl_iff, subset_compl_iff_disjoint_left, disjoint_iff_inter_eq_empty]

Depends on / 依赖: and_imp, closure, disjoint_iff_inter_eq_empty, exists_prop, isClosed_compl_iff, mem_ofPred_eq, mem_sInter, not_forall, subset_closure_inter_of_isPreirreducible_of_isOpen, subset_compl_iff_disjoint_left
-/
theorem isPreirreducible_iff_subset_closure_inter_open (S : Set X) :
    IsPreirreducible S ↔
      (forall U : Set X, IsOpen U -> (S inter U).Nonempty -> S subseteq closure (S inter U)) := by
  refine ⟨fun h _ => ?_, fun h => ?_⟩
  · exact subset_closure_inter_of_isPreirreducible_of_isOpen h
  · intro a b ha hb ⟨p, pS, pa⟩ bS
    by_contra! h0
suffices p ∉ closure (S inter b) from this (h b hb bS) pS
    simp only [closure, mem_sInter, mem_ofPred_eq, and_imp, not_forall, exists_prop]
    use aᶜ
    grind [isClosed_compl_iff, subset_compl_iff_disjoint_left, disjoint_iff_inter_eq_empty]

/--
theorem `preirreducibleSpace_iff_open_dense` / 定理 `preirreducibleSpace_iff_open_dense`

English:
theorem preirreducibleSpace_iff_open_dense
  given: (X : Type*) [TopologicalSpace X]
  proof: by
  rw [preirreducibleSpace_iff]; rw [isPreirreducible_iff_subset_closure_inter_open]
  simp only [univ_inter, univ_subset_iff, Dense]
  grind

中文:
定理 preirreducibleSpace_iff_open_dense
  条件: (X : 类型) [拓扑空间 X]
  证明: by
  rw [preirreducibleSpace_iff]; rw [isPreirreducible_iff_subset_closure_inter_open]
  simp only [univ_inter, univ_subset_iff, Dense]
  grind

Depends on / 依赖: isPreirreducible_iff_subset_closure_inter_open, preirreducibleSpace_iff, univ_inter, univ_subset_iff
-/
theorem preirreducibleSpace_iff_open_dense (X : Type*) [TopologicalSpace X] :
    PreirreducibleSpace X ↔ forall ⦃U : Set X⦄, IsOpen U -> U.Nonempty -> Dense U := by
  rw [preirreducibleSpace_iff]; rw [isPreirreducible_iff_subset_closure_inter_open]
  simp only [univ_inter, univ_subset_iff, Dense]
  grind

/--
theorem `sUnion_irreducibleComponents` / 定理 `sUnion_irreducibleComponents`

English:
theorem sUnion_irreducibleComponents
  statement: ⋃₀ irreducibleComponents X = Set.univ
  proof: Set.eq_univ_of_forall fun x => Set.mem_sUnion_of_mem mem_irreducibleComponent
    (irreducibleComponent_mem_irreducibleComponents x)

中文:
定理 sUnion_irreducibleComponents
  结论: ⋃₀ irreducibleComponents X = 集合.univ
  证明: Set.eq_univ_of_forall fun x => Set.mem_sUnion_of_mem mem_irreducibleComponent
    (irreducibleComponent_mem_irreducibleComponents x)

Depends on / 依赖: Set.eq_univ_of_forall, Set.mem_sUnion_of_mem, eq_univ_of_forall, irreducibleComponent_mem_irreducibleComponents, mem_irreducibleComponent, mem_sUnion_of_mem
-/
theorem sUnion_irreducibleComponents : ⋃₀ irreducibleComponents X = Set.univ :=
  Set.eq_univ_of_forall fun x => Set.mem_sUnion_of_mem mem_irreducibleComponent
    (irreducibleComponent_mem_irreducibleComponents x)

/--
theorem `mem_of_subset_sUnion_irreducibleComponents` / 定理 `mem_of_subset_sUnion_irreducibleComponents`

English:
theorem mem_of_subset_sUnion_irreducibleComponents
  statement: (Z : Set X) (hZ : Z in irreducibleComponents X)
  proof: by
  obtain ⟨W, hWS, hZW⟩ := isIrreducible_iff_sUnion_isClosed.mp hZ.1 hS.toFinset
    (fun W hW => isClosed_of_mem_irreducibleComponents W (hSα (hS.mem_toFinset.mp hW)))
    (hS.coe_toFinset.symm ▸ hZS)
  rw [hS.mem_toFinset] at hWS
  rwa [Set.Subset.antisymm hZW (hZ.2 (hSα hWS).1 hZW)]

中文:
定理 mem_of_subset_sUnion_irreducibleComponents
  结论: (Z : 集合 X) (hZ : Z in irreducibleComponents X)
  证明: by
  obtain ⟨W, hWS, hZW⟩ := isIrreducible_iff_sUnion_isClosed.mp hZ.1 hS.toFinset
    (fun W hW => isClosed_of_mem_irreducibleComponents W (hSα (hS.mem_toFinset.mp hW)))
    (hS.coe_toFinset.symm ▸ hZS)
  rw [hS.mem_toFinset] at hWS
  rwa [Set.Subset.antisymm hZW (hZ.2 (hSα hWS).1 hZW)]

Depends on / 依赖: Set.Subset.antisymm, Subset, antisymm, coe_toFinset, hS.coe_toFinset.symm, hS.mem_toFinset, hS.mem_toFinset.mp, hS.toFinset, isClosed_of_mem_irreducibleComponents, isIrreducible_iff_sUnion_isClosed, isIrreducible_iff_sUnion_isClosed.mp, mem_toFinset, toFinset
-/
theorem mem_of_subset_sUnion_irreducibleComponents (Z : Set X) (hZ : Z in irreducibleComponents X)
    (S : Set (Set X)) (hS : S.Finite) (hSα : S subseteq irreducibleComponents X) (hZS : Z subseteq ⋃₀ S) :
    Z in S := by
  obtain ⟨W, hWS, hZW⟩ := isIrreducible_iff_sUnion_isClosed.mp hZ.1 hS.toFinset
    (fun W hW => isClosed_of_mem_irreducibleComponents W (hSα (hS.mem_toFinset.mp hW)))
    (hS.coe_toFinset.symm ▸ hZS)
  rw [hS.mem_toFinset] at hWS
  rwa [Set.Subset.antisymm hZW (hZ.2 (hSα hWS).1 hZW)]

/--
theorem `closure_sUnion_irreducibleComponents_sdiff_singleton` / 定理 `closure_sUnion_irreducibleComponents_sdiff_singleton`

English:
theorem closure_sUnion_irreducibleComponents_sdiff_singleton
  proof: by
  have h : (⋃₀ (irreducibleComponents X \ {Z}))ᶜ subseteq Z := by
    rw [Set.compl_subset_iff_union]; rw [← Set.sUnion_singleton Z]; rw [← Set.sUnion_union]; rw [Set.sUnion_singleton]; rw [Set.sdiff_union_of_subset]; rw [sUnion_irreducibleComponents]
    rwa [Set.singleton_subset_iff]
  apply Set.Subset.antisymm
  · rwa [(isClosed_of_mem_irreducibleComponents Z hZ).closure_subset_iff]
  · rw [← Set.inter_eq_right.mpr h]
    apply subset_closure_inter_of_isPreirreducible_of_isOpen hZ.1.2
    · rw [Set.sUnion_eq_biUnion, isOpen_compl_iff]
      exact hX.sdiff.isClosed_biUnion fun W hW => isClosed_of_mem_irreducibleComponents W hW.1
    · rw [Set.inter_compl_nonempty_iff]
      exact mt (mem_of_subset_sUnion_irreducibleComponents Z hZ _ hX.sdiff Set.sdiff_subset)
        (Set.notMem_sdiff_of_mem (Set.mem_singleton Z))

中文:
定理 closure_sUnion_irreducibleComponents_sdiff_singleton
  证明: by
  have h : (⋃₀ (irreducibleComponents X \ {Z}))ᶜ subseteq Z := by
    rw [Set.compl_subset_iff_union]; rw [← Set.sUnion_singleton Z]; rw [← Set.sUnion_union]; rw [Set.sUnion_singleton]; rw [Set.sdiff_union_of_subset]; rw [sUnion_irreducibleComponents]
    rwa [Set.singleton_subset_iff]
  apply Set.Subset.antisymm
  · rwa [(isClosed_of_mem_irreducibleComponents Z hZ).closure_subset_iff]
  · rw [← Set.inter_eq_right.mpr h]
    apply subset_closure_inter_of_isPreirreducible_of_isOpen hZ.1.2
    · rw [Set.sUnion_eq_biUnion, isOpen_compl_iff]
      exact hX.sdiff.isClosed_biUnion fun W hW => isClosed_of_mem_irreducibleComponents W hW.1
    · rw [Set.inter_compl_nonempty_iff]
      exact mt (mem_of_subset_sUnion_irreducibleComponents Z hZ _ hX.sdiff Set.sdiff_subset)
        (Set.notMem_sdiff_of_mem (Set.mem_singleton Z))

Depends on / 依赖: Set.Subset.antisymm, Set.compl_subset_iff_union, Set.inter_eq_right.mpr, Set.sUnion_eq_biUn, Set.sUnion_singleton, Set.sUnion_union, Set.sdiff_union_of_subset, Set.singleton_subset_iff, Subset, antisymm, closure_subset_iff, compl_subset_iff_union, inter_eq_right, irreducibleComponents, isClosed_of_mem_irreducibleComponents, sUnion_eq_biUn, sUnion_irreducibleComponents, sUnion_singleton, sUnion_union, sdiff_union_of_subset
-/
theorem closure_sUnion_irreducibleComponents_sdiff_singleton
    (hX : (irreducibleComponents X).Finite) (Z : Set X) (hZ : Z in irreducibleComponents X) :
    closure (⋃₀ (irreducibleComponents X \ {Z}))ᶜ = Z := by
  have h : (⋃₀ (irreducibleComponents X \ {Z}))ᶜ subseteq Z := by
    rw [Set.compl_subset_iff_union]; rw [← Set.sUnion_singleton Z]; rw [← Set.sUnion_union]; rw [Set.sUnion_singleton]; rw [Set.sdiff_union_of_subset]; rw [sUnion_irreducibleComponents]
    rwa [Set.singleton_subset_iff]
  apply Set.Subset.antisymm
  · rwa [(isClosed_of_mem_irreducibleComponents Z hZ).closure_subset_iff]
  · rw [← Set.inter_eq_right.mpr h]
    apply subset_closure_inter_of_isPreirreducible_of_isOpen hZ.1.2
    · rw [Set.sUnion_eq_biUnion, isOpen_compl_iff]
      exact hX.sdiff.isClosed_biUnion fun W hW => isClosed_of_mem_irreducibleComponents W hW.1
    · rw [Set.inter_compl_nonempty_iff]
      exact mt (mem_of_subset_sUnion_irreducibleComponents Z hZ _ hX.sdiff Set.sdiff_subset)
        (Set.notMem_sdiff_of_mem (Set.mem_singleton Z))

/--
theorem `IsPreirreducible.subset_irreducible` / 定理 `IsPreirreducible.subset_irreducible`

English:
theorem IsPreirreducible.subset_irreducible
  statement: {S U : Set X} (ht : IsPreirreducible t)
  proof: by
  obtain ⟨z, hz⟩ := hU
  replace ht : IsIrreducible t := ⟨⟨z, h₂ (h₁ hz)⟩, ht⟩
  refine ⟨⟨z, h₁ hz⟩, ?_⟩
  rintro u v hu hv ⟨x, hx, hx'⟩ ⟨y, hy, hy'⟩
  obtain ⟨x, -, hx'⟩ : Set.Nonempty (t inter ⋂₀ ↑({U, u, v} : Finset (Set X))) := by
    refine isIrreducible_iff_sInter.mp ht {U, u, v} ?_ ?_
    · simp [*]
    · intro U H
      simp only [Finset.mem_insert, Finset.mem_singleton] at H
      rcases H with (rfl | rfl | rfl)
      exacts [⟨z, h₂ (h₁ hz), hz⟩, ⟨x, h₂ hx, hx'⟩, ⟨y, h₂ hy, hy'⟩]
  replace hx' : x in U ∧ x in u ∧ x in v := by simpa using hx'
  exact ⟨x, h₁ hx'.1, hx'.2⟩

中文:
定理 IsPreirreducible.subset_irreducible
  结论: {S U : 集合 X} (ht : IsPreirreducible t)
  证明: by
  obtain ⟨z, hz⟩ := hU
  replace ht : IsIrreducible t := ⟨⟨z, h₂ (h₁ hz)⟩, ht⟩
  refine ⟨⟨z, h₁ hz⟩, ?_⟩
  rintro u v hu hv ⟨x, hx, hx'⟩ ⟨y, hy, hy'⟩
  obtain ⟨x, -, hx'⟩ : Set.Nonempty (t inter ⋂₀ ↑({U, u, v} : Finset (Set X))) := by
    refine isIrreducible_iff_sInter.mp ht {U, u, v} ?_ ?_
    · simp [*]
    · intro U H
      simp only [Finset.mem_insert, Finset.mem_singleton] at H
      rcases H with (rfl | rfl | rfl)
      exacts [⟨z, h₂ (h₁ hz), hz⟩, ⟨x, h₂ hx, hx'⟩, ⟨y, h₂ hy, hy'⟩]
  replace hx' : x in U ∧ x in u ∧ x in v := by simpa using hx'
  exact ⟨x, h₁ hx'.1, hx'.2⟩

Depends on / 依赖: Finset, Finset.mem_insert, Finset.mem_singleton, IsIrreducible, Nonempty, Set.Nonempty, exacts, isIrreducible_iff_sInter, isIrreducible_iff_sInter.mp, mem_insert, mem_singleton, replace
-/
theorem IsPreirreducible.subset_irreducible {S U : Set X} (ht : IsPreirreducible t)
    (hU : U.Nonempty) (hU' : IsOpen U) (h₁ : U subseteq S) (h₂ : S subseteq t) : IsIrreducible S := by
  obtain ⟨z, hz⟩ := hU
  replace ht : IsIrreducible t := ⟨⟨z, h₂ (h₁ hz)⟩, ht⟩
  refine ⟨⟨z, h₁ hz⟩, ?_⟩
  rintro u v hu hv ⟨x, hx, hx'⟩ ⟨y, hy, hy'⟩
  obtain ⟨x, -, hx'⟩ : Set.Nonempty (t inter ⋂₀ ↑({U, u, v} : Finset (Set X))) := by
    refine isIrreducible_iff_sInter.mp ht {U, u, v} ?_ ?_
    · simp [*]
    · intro U H
      simp only [Finset.mem_insert, Finset.mem_singleton] at H
      rcases H with (rfl | rfl | rfl)
      exacts [⟨z, h₂ (h₁ hz), hz⟩, ⟨x, h₂ hx, hx'⟩, ⟨y, h₂ hy, hy'⟩]
  replace hx' : x in U ∧ x in u ∧ x in v := by simpa using hx'
  exact ⟨x, h₁ hx'.1, hx'.2⟩

/--
theorem `IsPreirreducible.open_subset` / 定理 `IsPreirreducible.open_subset`

English:
theorem IsPreirreducible.open_subset
  statement: {U : Set X} (ht : IsPreirreducible t) (hU : IsOpen U)
  proof: U.eq_empty_or_nonempty.elim (fun h => h.symm ▸ isPreirreducible_empty) fun h =>
    (ht.subset_irreducible h hU (fun _ => id) hU').2

中文:
定理 IsPreirreducible.open_subset
  结论: {U : 集合 X} (ht : IsPreirreducible t) (hU : 是开集 U)
  证明: U.eq_empty_or_nonempty.elim (fun h => h.symm ▸ isPreirreducible_empty) fun h =>
    (ht.subset_irreducible h hU (fun _ => id) hU').2

Depends on / 依赖: U.eq_empty_or_nonempty.elim, eq_empty_or_nonempty, h.symm, ht.subset_irreducible, isPreirreducible_empty, subset_irreducible
-/
theorem IsPreirreducible.open_subset {U : Set X} (ht : IsPreirreducible t) (hU : IsOpen U)
    (hU' : U subseteq t) : IsPreirreducible U :=
  U.eq_empty_or_nonempty.elim (fun h => h.symm ▸ isPreirreducible_empty) fun h =>
    (ht.subset_irreducible h hU (fun _ => id) hU').2

/--
theorem `IsPreirreducible.interior` / 定理 `IsPreirreducible.interior`

English:
theorem IsPreirreducible.interior
  given: (ht : IsPreirreducible t)
  statement: IsPreirreducible (interior t)
  proof: ht.open_subset isOpen_interior interior_subset

中文:
定理 IsPreirreducible.interior
  条件: (ht : IsPreirreducible t)
  结论: IsPreirreducible (interior t)
  证明: ht.open_subset isOpen_interior interior_subset

Depends on / 依赖: ht.open_subset, interior_subset, isOpen_interior, open_subset
-/
theorem IsPreirreducible.interior (ht : IsPreirreducible t) : IsPreirreducible (interior t) :=
  ht.open_subset isOpen_interior interior_subset

section

open Set.Notation

@[stacks 004Z]
/--
lemma `IsPreirreducible.preimage_of_dense_isPreirreducible_fiber` / 引理 `IsPreirreducible.preimage_of_dense_isPreirreducible_fiber`

English:
lemma IsPreirreducible.preimage_of_dense_isPreirreducible_fiber
  proof: by
  rintro U₁ U₂ hU₁ hU₂ ⟨x, hxV, hxU₁⟩ ⟨y, hyV, hyU₂⟩
  obtain ⟨z, hzV, hz₁, hz₂⟩ :=
    hV _ _ (hf' _ hU₁) (hf' _ hU₂) ⟨f x, hxV, x, hxU₁, rfl⟩ ⟨f y, hyV, y, hyU₂, rfl⟩
  obtain ⟨z, ⟨⟨z₁, hz₁, e₁⟩, ⟨z₂, hz₂, e₂⟩⟩, hzV, hz⟩ :=
    mem_closure_iff.mp (hf'' hzV) _ ((hf' _ hU₁).inter (hf' _ hU₂)) ⟨hz₁, hz₂⟩
  obtain ⟨z₃, hz₃, hz₃'⟩ := hz _ _ hU₁ hU₂ ⟨z₁, e₁, hz₁⟩ ⟨z₂, e₂, hz₂⟩
  refine ⟨z₃, show f z₃ in _ from (show f z₃ = z from hz₃) ▸ hzV, hz₃'⟩

中文:
引理 IsPreirreducible.preimage_of_dense_isPreirreducible_fiber
  证明: by
  rintro U₁ U₂ hU₁ hU₂ ⟨x, hxV, hxU₁⟩ ⟨y, hyV, hyU₂⟩
  obtain ⟨z, hzV, hz₁, hz₂⟩ :=
    hV _ _ (hf' _ hU₁) (hf' _ hU₂) ⟨f x, hxV, x, hxU₁, rfl⟩ ⟨f y, hyV, y, hyU₂, rfl⟩
  obtain ⟨z, ⟨⟨z₁, hz₁, e₁⟩, ⟨z₂, hz₂, e₂⟩⟩, hzV, hz⟩ :=
    mem_closure_iff.mp (hf'' hzV) _ ((hf' _ hU₁).inter (hf' _ hU₂)) ⟨hz₁, hz₂⟩
  obtain ⟨z₃, hz₃, hz₃'⟩ := hz _ _ hU₁ hU₂ ⟨z₁, e₁, hz₁⟩ ⟨z₂, e₂, hz₂⟩
  refine ⟨z₃, show f z₃ in _ from (show f z₃ = z from hz₃) ▸ hzV, hz₃'⟩

Depends on / 依赖: mem_closure_iff, mem_closure_iff.mp
-/
lemma IsPreirreducible.preimage_of_dense_isPreirreducible_fiber
    {V : Set Y} (hV : IsPreirreducible V) (f : X -> Y) (hf' : IsOpenMap f)
    (hf'' : V subseteq closure (V inter { x | IsPreirreducible (f ⁻¹' {x}) })) :
    IsPreirreducible (f ⁻¹' V) := by
  rintro U₁ U₂ hU₁ hU₂ ⟨x, hxV, hxU₁⟩ ⟨y, hyV, hyU₂⟩
  obtain ⟨z, hzV, hz₁, hz₂⟩ :=
    hV _ _ (hf' _ hU₁) (hf' _ hU₂) ⟨f x, hxV, x, hxU₁, rfl⟩ ⟨f y, hyV, y, hyU₂, rfl⟩
  obtain ⟨z, ⟨⟨z₁, hz₁, e₁⟩, ⟨z₂, hz₂, e₂⟩⟩, hzV, hz⟩ :=
    mem_closure_iff.mp (hf'' hzV) _ ((hf' _ hU₁).inter (hf' _ hU₂)) ⟨hz₁, hz₂⟩
  obtain ⟨z₃, hz₃, hz₃'⟩ := hz _ _ hU₁ hU₂ ⟨z₁, e₁, hz₁⟩ ⟨z₂, e₂, hz₂⟩
  refine ⟨z₃, show f z₃ in _ from (show f z₃ = z from hz₃) ▸ hzV, hz₃'⟩

/--
lemma `IsPreirreducible.preimage_of_isPreirreducible_fiber` / 引理 `IsPreirreducible.preimage_of_isPreirreducible_fiber`

English:
lemma IsPreirreducible.preimage_of_isPreirreducible_fiber
  proof: by
  refine hV.preimage_of_dense_isPreirreducible_fiber f hf' ?_
  simp [hf'', subset_closure]

中文:
引理 IsPreirreducible.preimage_of_isPreirreducible_fiber
  证明: by
  refine hV.preimage_of_dense_isPreirreducible_fiber f hf' ?_
  simp [hf'', subset_closure]

Depends on / 依赖: hV.preimage_of_dense_isPreirreducible_fiber, preimage_of_dense_isPreirreducible_fiber, subset_closure
-/
lemma IsPreirreducible.preimage_of_isPreirreducible_fiber
    {V : Set Y} (hV : IsPreirreducible V)
    (f : X -> Y) (hf' : IsOpenMap f) (hf'' : forall x, IsPreirreducible (f ⁻¹' {x})) :
    IsPreirreducible (f ⁻¹' V) := by
  refine hV.preimage_of_dense_isPreirreducible_fiber f hf' ?_
  simp [hf'', subset_closure]

/--
lemma `IsPreirreducible.preimage` / 引理 `IsPreirreducible.preimage`

English:
lemma IsPreirreducible.preimage
  given: (ht : IsPreirreducible t) {f : Y -> X} (hf : IsOpenEmbedding f)
  proof: ht.preimage_of_isPreirreducible_fiber f hf.isOpenMap
    fun _ => (subsingleton_singleton.preimage hf.injective).isPreirreducible

中文:
引理 IsPreirreducible.原像
  条件: (ht : IsPreirreducible t) {f : Y -> X} (hf : 是开嵌入 f)
  证明: ht.preimage_of_isPreirreducible_fiber f hf.isOpenMap
    fun _ => (subsingleton_singleton.preimage hf.injective).isPreirreducible

Depends on / 依赖: hf.injective, hf.isOpenMap, ht.preimage_of_isPreirreducible_fiber, injective, isOpenMap, isPreirreducible, preimage, preimage_of_isPreirreducible_fiber, subsingleton_singleton, subsingleton_singleton.preimage
-/
lemma IsPreirreducible.preimage (ht : IsPreirreducible t) {f : Y -> X} (hf : IsOpenEmbedding f) :
    IsPreirreducible (f ⁻¹' t) :=
  ht.preimage_of_isPreirreducible_fiber f hf.isOpenMap
    fun _ => (subsingleton_singleton.preimage hf.injective).isPreirreducible

/--
lemma `IsIrreducible.preimage_of_isPreirreducible_fiber` / 引理 `IsIrreducible.preimage_of_isPreirreducible_fiber`

English:
lemma IsIrreducible.preimage_of_isPreirreducible_fiber
  statement: (ht : IsIrreducible t)
  proof: by
  refine ⟨?_, IsPreirreducible.preimage_of_isPreirreducible_fiber ht.2 f hf₂ hf₃⟩
  obtain ⟨-, hx, x, rfl⟩ := h
  exact ⟨x, hx⟩

中文:
引理 是不可约.preimage_of_isPreirreducible_fiber
  结论: (ht : 是不可约 t)
  证明: by
  refine ⟨?_, IsPreirreducible.preimage_of_isPreirreducible_fiber ht.2 f hf₂ hf₃⟩
  obtain ⟨-, hx, x, rfl⟩ := h
  exact ⟨x, hx⟩

Depends on / 依赖: IsPreirreducible, IsPreirreducible.preimage_of_isPreirreducible_fiber, preimage_of_isPreirreducible_fiber
-/
lemma IsIrreducible.preimage_of_isPreirreducible_fiber (ht : IsIrreducible t)
    (f : Y -> X) (hf₂ : IsOpenMap f) (hf₃ : forall x, IsPreirreducible (f ⁻¹' {x}))
    (h : (t inter Set.range f).Nonempty) :
    IsIrreducible (f ⁻¹' t) := by
  refine ⟨?_, IsPreirreducible.preimage_of_isPreirreducible_fiber ht.2 f hf₂ hf₃⟩
  obtain ⟨-, hx, x, rfl⟩ := h
  exact ⟨x, hx⟩

/--
lemma `IsIrreducible.preimage` / 引理 `IsIrreducible.preimage`

English:
lemma IsIrreducible.preimage
  statement: (ht : IsIrreducible t) {f : Y -> X}
  proof: by
  refine ht.preimage_of_isPreirreducible_fiber f hf.isOpenMap
    (fun _ => (subsingleton_singleton.preimage hf.injective).isPreirreducible) h

中文:
引理 是不可约.原像
  结论: (ht : 是不可约 t) {f : Y -> X}
  证明: by
  refine ht.preimage_of_isPreirreducible_fiber f hf.isOpenMap
    (fun _ => (subsingleton_singleton.preimage hf.injective).isPreirreducible) h

Depends on / 依赖: hf.injective, hf.isOpenMap, ht.preimage_of_isPreirreducible_fiber, injective, isOpenMap, isPreirreducible, preimage, preimage_of_isPreirreducible_fiber, subsingleton_singleton, subsingleton_singleton.preimage
-/
lemma IsIrreducible.preimage (ht : IsIrreducible t) {f : Y -> X}
    (hf : IsOpenEmbedding f) (h : (t inter Set.range f).Nonempty) : IsIrreducible (f ⁻¹' t) := by
  refine ht.preimage_of_isPreirreducible_fiber f hf.isOpenMap
    (fun _ => (subsingleton_singleton.preimage hf.injective).isPreirreducible) h

/--
lemma `Topology.IsOpenEmbedding.preirreducibleSpace` / 引理 `Topology.IsOpenEmbedding.preirreducibleSpace`

English:
lemma Topology.IsOpenEmbedding.preirreducibleSpace
  statement: {f : Y -> X} (hf : Topology.IsOpenEmbedding f)
  proof: by
    rw [← Set.preimage_univ]
    exact .preimage PreirreducibleSpace.isPreirreducible_univ hf

中文:
引理 拓扑.是开嵌入.preirreducibleSpace
  结论: {f : Y -> X} (hf : 拓扑.是开嵌入 f)
  证明: by
    rw [← Set.preimage_univ]
    exact .preimage PreirreducibleSpace.isPreirreducible_univ hf

Depends on / 依赖: PreirreducibleSpace, PreirreducibleSpace.isPreirreducible_univ, Set.preimage_univ, isPreirreducible_univ, preimage, preimage_univ
-/
lemma Topology.IsOpenEmbedding.preirreducibleSpace {f : Y -> X} (hf : Topology.IsOpenEmbedding f)
    [PreirreducibleSpace X] :
    PreirreducibleSpace Y where
  isPreirreducible_univ := by
    rw [← Set.preimage_univ]
    exact .preimage PreirreducibleSpace.isPreirreducible_univ hf

/--
lemma `Topology.IsOpenEmbedding.irreducibleSpace` / 引理 `Topology.IsOpenEmbedding.irreducibleSpace`

English:
lemma Topology.IsOpenEmbedding.irreducibleSpace
  statement: {f : Y -> X} (hf : Topology.IsOpenEmbedding f)
  proof: ‹_›
  __ := hf.preirreducibleSpace

中文:
引理 拓扑.是开嵌入.irreducibleSpace
  结论: {f : Y -> X} (hf : 拓扑.是开嵌入 f)
  证明: ‹_›
  __ := hf.preirreducibleSpace
-/
lemma Topology.IsOpenEmbedding.irreducibleSpace {f : Y -> X} (hf : Topology.IsOpenEmbedding f)
    [IrreducibleSpace X] [Nonempty Y] :
    IrreducibleSpace Y where
  toNonempty := ‹_›
  __ := hf.preirreducibleSpace

/--
lemma `preimage_mem_irreducibleComponents_of_isPreirreducible_fiber` / 引理 `preimage_mem_irreducibleComponents_of_isPreirreducible_fiber`

English:
lemma preimage_mem_irreducibleComponents_of_isPreirreducible_fiber
  proof: by
  refine ⟨ht.1.preimage_of_isPreirreducible_fiber f hf₂ hf₃ h, fun u hu htu => image_subset_iff.mp
    (subset_closure.trans (ht.2 (hu.image f hf₁.continuousOn).closure ?_))⟩
  suffices t <= closure (f '' f ⁻¹' t) from this.trans (closure_mono (image_mono htu))
  rw [image_preimage_eq_inter_range]
  exact subset_closure_inter_of_isPreirreducible_of_isOpen ht.1.2 hf₂.isOpen_range h

中文:
引理 preimage_mem_irreducibleComponents_of_isPreirreducible_fiber
  证明: by
  refine ⟨ht.1.preimage_of_isPreirreducible_fiber f hf₂ hf₃ h, fun u hu htu => image_subset_iff.mp
    (subset_closure.trans (ht.2 (hu.image f hf₁.continuousOn).closure ?_))⟩
  suffices t <= closure (f '' f ⁻¹' t) from this.trans (closure_mono (image_mono htu))
  rw [image_preimage_eq_inter_range]
  exact subset_closure_inter_of_isPreirreducible_of_isOpen ht.1.2 hf₂.isOpen_range h

Depends on / 依赖: closure, closure_mono, continuousOn, hu.image, image_mono, image_preimage_eq_inter_range, image_subset_iff, image_subset_iff.mp, isOpen_range, preimage_of_isPreirreducible_fiber, subset_closure, subset_closure.trans, subset_closure_inter_of_isPreirreducible_of_isOpen, this.trans
-/
lemma preimage_mem_irreducibleComponents_of_isPreirreducible_fiber
    (ht : t in irreducibleComponents X) {f : Y -> X} (hf₁ : Continuous f) (hf₂ : IsOpenMap f)
    (hf₃ : forall x, IsPreirreducible (f ⁻¹' {x})) (h : (t inter range f).Nonempty) :
    f ⁻¹' t in irreducibleComponents Y := by
  refine ⟨ht.1.preimage_of_isPreirreducible_fiber f hf₂ hf₃ h, fun u hu htu => image_subset_iff.mp
    (subset_closure.trans (ht.2 (hu.image f hf₁.continuousOn).closure ?_))⟩
  suffices t <= closure (f '' f ⁻¹' t) from this.trans (closure_mono (image_mono htu))
  rw [image_preimage_eq_inter_range]
  exact subset_closure_inter_of_isPreirreducible_of_isOpen ht.1.2 hf₂.isOpen_range h

/--
lemma `preimage_mem_irreducibleComponents` / 引理 `preimage_mem_irreducibleComponents`

English:
lemma preimage_mem_irreducibleComponents
  statement: (ht : t in irreducibleComponents X) {f : Y -> X}
  proof: by
  refine preimage_mem_irreducibleComponents_of_isPreirreducible_fiber ht hf.continuous hf.isOpenMap
    (fun _ => (subsingleton_singleton.preimage hf.injective).isPreirreducible) h

中文:
引理 preimage_mem_irreducibleComponents
  结论: (ht : t in irreducibleComponents X) {f : Y -> X}
  证明: by
  refine preimage_mem_irreducibleComponents_of_isPreirreducible_fiber ht hf.continuous hf.isOpenMap
    (fun _ => (subsingleton_singleton.preimage hf.injective).isPreirreducible) h

Depends on / 依赖: continuous, hf.continuous, hf.injective, hf.isOpenMap, injective, isOpenMap, isPreirreducible, preimage, preimage_mem_irreducibleComponents_of_isPreirreducible_fiber, subsingleton_singleton, subsingleton_singleton.preimage
-/
lemma preimage_mem_irreducibleComponents (ht : t in irreducibleComponents X) {f : Y -> X}
    (hf : IsOpenEmbedding f) (h : (t inter Set.range f).Nonempty) :
    f ⁻¹' t in irreducibleComponents Y := by
  refine preimage_mem_irreducibleComponents_of_isPreirreducible_fiber ht hf.continuous hf.isOpenMap
    (fun _ => (subsingleton_singleton.preimage hf.injective).isPreirreducible) h

/--
lemma `closure_image_preimage_of_isPreirreducible` / 引理 `closure_image_preimage_of_isPreirreducible`

English:
lemma closure_image_preimage_of_isPreirreducible
  statement: (f : Y -> X) (h : IsOpenMap f) (s : Set X)
  proof: by
  refine subset_antisymm (closure_minimal (by simp) hs') ?_
  refine subset_trans (subset_closure_inter_of_isPreirreducible_of_isOpen hs h.isOpen_range ?_) ?_
  · exact Set.nonempty_of_nonempty_preimage (f := f) (by simpa)
  · gcongr
    grind

中文:
引理 closure_image_preimage_of_isPreirreducible
  结论: (f : Y -> X) (h : 是开映射 f) (s : 集合 X)
  证明: by
  refine subset_antisymm (closure_minimal (by simp) hs') ?_
  refine subset_trans (subset_closure_inter_of_isPreirreducible_of_isOpen hs h.isOpen_range ?_) ?_
  · exact Set.nonempty_of_nonempty_preimage (f := f) (by simpa)
  · gcongr
    grind

Depends on / 依赖: Set.nonempty_of_nonempty_preimage, closure_minimal, h.isOpen_range, isOpen_range, nonempty_of_nonempty_preimage, subset_antisymm, subset_closure_inter_of_isPreirreducible_of_isOpen, subset_trans
-/
lemma closure_image_preimage_of_isPreirreducible (f : Y -> X) (h : IsOpenMap f) (s : Set X)
    (hne : (f ⁻¹' s).Nonempty) (hs : IsPreirreducible s) (hs' : IsClosed s) :
    closure (f '' f ⁻¹' s) = s := by
  refine subset_antisymm (closure_minimal (by simp) hs') ?_
  refine subset_trans (subset_closure_inter_of_isPreirreducible_of_isOpen hs h.isOpen_range ?_) ?_
  · exact Set.nonempty_of_nonempty_preimage (f := f) (by simpa)
  · gcongr
    grind

variable (f : X -> Y) (hf₁ : Continuous f) (hf₂ : IsOpenMap f)
variable (hf₃ : forall x, IsPreirreducible (f ⁻¹' {x})) (hf₄ : Function.Surjective f)

include hf₁ hf₂ hf₃ hf₄

/--
lemma `image_mem_irreducibleComponents_of_isPreirreducible_fiber` / 引理 `image_mem_irreducibleComponents_of_isPreirreducible_fiber`

English:
lemma image_mem_irreducibleComponents_of_isPreirreducible_fiber
  proof: ⟨hV.1.image _ hf₁.continuousOn, fun Z hZ hWZ => by
    have := hV.2 ⟨(by obtain ⟨x, hx⟩ := hV.1.1; exact ⟨x, hWZ ⟨x, hx, rfl⟩⟩),
      hZ.2.preimage_of_isPreirreducible_fiber f hf₂ hf₃⟩ (Set.image_subset_iff.mp hWZ)
    rw [← Set.image_preimage_eq Z hf₄]
    exact Set.image_mono this⟩

中文:
引理 image_mem_irreducibleComponents_of_isPreirreducible_fiber
  证明: ⟨hV.1.image _ hf₁.continuousOn, fun Z hZ hWZ => by
    have := hV.2 ⟨(by obtain ⟨x, hx⟩ := hV.1.1; exact ⟨x, hWZ ⟨x, hx, rfl⟩⟩),
      hZ.2.preimage_of_isPreirreducible_fiber f hf₂ hf₃⟩ (Set.image_subset_iff.mp hWZ)
    rw [← Set.image_preimage_eq Z hf₄]
    exact Set.image_mono this⟩

Depends on / 依赖: Set.image_mono, Set.image_preimage_eq, Set.image_subset_iff.mp, continuousOn, image_mono, image_preimage_eq, image_subset_iff, preimage_of_isPreirreducible_fiber
-/
lemma image_mem_irreducibleComponents_of_isPreirreducible_fiber
    {V : Set X} (hV : V in irreducibleComponents X) :
    f '' V in irreducibleComponents Y :=
  ⟨hV.1.image _ hf₁.continuousOn, fun Z hZ hWZ => by
    have := hV.2 ⟨(by obtain ⟨x, hx⟩ := hV.1.1; exact ⟨x, hWZ ⟨x, hx, rfl⟩⟩),
      hZ.2.preimage_of_isPreirreducible_fiber f hf₂ hf₃⟩ (Set.image_subset_iff.mp hWZ)
    rw [← Set.image_preimage_eq Z hf₄]
    exact Set.image_mono this⟩

set_option backward.isDefEq.respectTransparency false in
/-- If `f : X → Y` is continuous, open, and has irreducible fibers, then it induces an
bijection between irreducible components -/
@[stacks 037A]
/--
Definition of `irreducibleComponentsEquivOfIsPreirreducibleFiber` / `irreducibleComponentsEquivOfIsPreirreducibleFiber` 的定义

English:
definition irreducibleComponentsEquivOfIsPreirreducibleFiber
  signature: :
  body: ⟨f '' W.1,
    image_mem_irreducibleComponents_of_isPreirreducible_fiber f hf₁ hf₂ hf₃ hf₄ W.2⟩
  toFun W := ⟨f ⁻¹' W.1,
    preimage_mem_irreducibleComponents_of_isPreirreducible_fiber W.2 hf₁ hf₂ hf₃
      (by simp [hf₄.range_eq, W.2.1.1])⟩
right_inv W := Subtype.ext by
    refine (Set.subset_preimage_image _ _).antisymm' (W.2.2 ?_ (Set.subset_preimage_image _ _))
    refine ⟨?_, (W.2.1.image _ hf₁.continuousOn).2.preimage_of_isPreirreducible_fiber _ hf₂ hf₃⟩
    obtain ⟨x, hx⟩ := W.2.1.1
    exact ⟨_, x, hx, rfl⟩
left_inv _ := Subtype.ext Set.image_preimage_eq _ hf₄
  map_rel_iff' {W Z} := by
    refine ⟨fun H => ?_, Set.preimage_mono⟩
    simpa only [Equiv.coe_fn_mk, Set.image_preimage_eq _ hf₄] using! Set.image_mono (f := f) H

中文:
定义 irreducibleComponentsEquivOfIsPreirreducibleFiber
  签名: :
  定义体: ⟨f '' W.1,
    image_mem_irreducibleComponents_of_isPreirreducible_fiber f hf₁ hf₂ hf₃ hf₄ W.2⟩
  toFun W := ⟨f ⁻¹' W.1,
    preimage_mem_irreducibleComponents_of_isPreirreducible_fiber W.2 hf₁ hf₂ hf₃
      (by simp [hf₄.range_eq, W.2.1.1])⟩
right_inv W := Subtype.ext by
    refine (Set.subset_preimage_image _ _).antisymm' (W.2.2 ?_ (Set.subset_preimage_image _ _))
    refine ⟨?_, (W.2.1.image _ hf₁.continuousOn).2.preimage_of_isPreirreducible_fiber _ hf₂ hf₃⟩
    obtain ⟨x, hx⟩ := W.2.1.1
    exact ⟨_, x, hx, rfl⟩
left_inv _ := Subtype.ext Set.image_preimage_eq _ hf₄
  map_rel_iff' {W Z} := by
    refine ⟨fun H => ?_, Set.preimage_mono⟩
    simpa only [Equiv.coe_fn_mk, Set.image_preimage_eq _ hf₄] using! Set.image_mono (f := f) H
-/
def irreducibleComponentsEquivOfIsPreirreducibleFiber :
    irreducibleComponents Y ≃o irreducibleComponents X where
  invFun W := ⟨f '' W.1,
    image_mem_irreducibleComponents_of_isPreirreducible_fiber f hf₁ hf₂ hf₃ hf₄ W.2⟩
  toFun W := ⟨f ⁻¹' W.1,
    preimage_mem_irreducibleComponents_of_isPreirreducible_fiber W.2 hf₁ hf₂ hf₃
      (by simp [hf₄.range_eq, W.2.1.1])⟩
right_inv W := Subtype.ext by
    refine (Set.subset_preimage_image _ _).antisymm' (W.2.2 ?_ (Set.subset_preimage_image _ _))
    refine ⟨?_, (W.2.1.image _ hf₁.continuousOn).2.preimage_of_isPreirreducible_fiber _ hf₂ hf₃⟩
    obtain ⟨x, hx⟩ := W.2.1.1
    exact ⟨_, x, hx, rfl⟩
left_inv _ := Subtype.ext Set.image_preimage_eq _ hf₄
  map_rel_iff' {W Z} := by
    refine ⟨fun H => ?_, Set.preimage_mono⟩
    simpa only [Equiv.coe_fn_mk, Set.image_preimage_eq _ hf₄] using! Set.image_mono (f := f) H

end

/--
lemma `IsDiscrete.subsingleton_of_isPreirreducible` / 引理 `IsDiscrete.subsingleton_of_isPreirreducible`

English:
lemma IsDiscrete.subsingleton_of_isPreirreducible
  given: (hs : IsDiscrete s) (hs' : IsPreirreducible s)
  proof: by
  intro x hxs y hys
  obtain ⟨U, hU, hUx⟩ := isDiscrete_iff_forall_mem_exists_isOpen.mp hs x hxs
  obtain ⟨V, hV, hVy⟩ := isDiscrete_iff_forall_mem_exists_isOpen.mp hs y hys
  obtain ⟨z, hz⟩ := hs' _ _ hU hV ⟨x, by grind⟩ ⟨y, by grind⟩
  exact (hUx.le (by grind)).symm.trans (b := z) (hVy.le (by grind))

中文:
引理 是离散.subsingleton_of_isPreirreducible
  条件: (hs : 是离散 s) (hs' : IsPreirreducible s)
  证明: by
  intro x hxs y hys
  obtain ⟨U, hU, hUx⟩ := isDiscrete_iff_forall_mem_exists_isOpen.mp hs x hxs
  obtain ⟨V, hV, hVy⟩ := isDiscrete_iff_forall_mem_exists_isOpen.mp hs y hys
  obtain ⟨z, hz⟩ := hs' _ _ hU hV ⟨x, by grind⟩ ⟨y, by grind⟩
  exact (hUx.le (by grind)).symm.trans (b := z) (hVy.le (by grind))

Depends on / 依赖: hUx.le, hVy.le, isDiscrete_iff_forall_mem_exists_isOpen, isDiscrete_iff_forall_mem_exists_isOpen.mp, symm.trans
-/
lemma IsDiscrete.subsingleton_of_isPreirreducible (hs : IsDiscrete s) (hs' : IsPreirreducible s) :
    s.Subsingleton := by
  intro x hxs y hys
  obtain ⟨U, hU, hUx⟩ := isDiscrete_iff_forall_mem_exists_isOpen.mp hs x hxs
  obtain ⟨V, hV, hVy⟩ := isDiscrete_iff_forall_mem_exists_isOpen.mp hs y hys
  obtain ⟨z, hz⟩ := hs' _ _ hU hV ⟨x, by grind⟩ ⟨y, by grind⟩
  exact (hUx.le (by grind)).symm.trans (b := z) (hVy.le (by grind))

end Preirreducible

/--
lemma `Function.Surjective.preirreducibleSpace` / 引理 `Function.Surjective.preirreducibleSpace`

English:
lemma Function.Surjective.preirreducibleSpace
  statement: {f : X -> Y} (hfc : Continuous f)
  proof: by
    rw [← hf.range_eq]; rw [← Set.image_univ]
    exact (PreirreducibleSpace.isPreirreducible_univ).image _ hfc.continuousOn

中文:
引理 函数.满射.preirreducibleSpace
  结论: {f : X -> Y} (hfc : 连续 f)
  证明: by
    rw [← hf.range_eq]; rw [← Set.image_univ]
    exact (PreirreducibleSpace.isPreirreducible_univ).image _ hfc.continuousOn

Depends on / 依赖: PreirreducibleSpace, PreirreducibleSpace.isPreirreducible_univ, Set.image_univ, continuousOn, hf.range_eq, hfc.continuousOn, image_univ, isPreirreducible_univ, range_eq
-/
lemma Function.Surjective.preirreducibleSpace {f : X -> Y} (hfc : Continuous f)
    (hf : Function.Surjective f) [PreirreducibleSpace X] : PreirreducibleSpace Y where
  isPreirreducible_univ := by
    rw [← hf.range_eq]; rw [← Set.image_univ]
    exact (PreirreducibleSpace.isPreirreducible_univ).image _ hfc.continuousOn

/--
lemma `Function.Surjective.irreducibleSpace` / 引理 `Function.Surjective.irreducibleSpace`

English:
lemma Function.Surjective.irreducibleSpace
  statement: {f : X -> Y} (hfc : Continuous f)
  proof: by
    rw [← hf.range_eq]; rw [← Set.image_univ]
    exact (PreirreducibleSpace.isPreirreducible_univ).image _ hfc.continuousOn
  toNonempty := Nonempty.map f inferInstance

中文:
引理 函数.满射.irreducibleSpace
  结论: {f : X -> Y} (hfc : 连续 f)
  证明: by
    rw [← hf.range_eq]; rw [← Set.image_univ]
    exact (PreirreducibleSpace.isPreirreducible_univ).image _ hfc.continuousOn
  toNonempty := Nonempty.map f inferInstance

Depends on / 依赖: Nonempty, Nonempty.map, PreirreducibleSpace, PreirreducibleSpace.isPreirreducible_univ, Set.image_univ, continuousOn, hf.range_eq, hfc.continuousOn, image_univ, isPreirreducible_univ, range_eq, toNonempty
-/
lemma Function.Surjective.irreducibleSpace {f : X -> Y} (hfc : Continuous f)
    (hf : Function.Surjective f) [IrreducibleSpace X] : IrreducibleSpace Y where
  isPreirreducible_univ := by
    rw [← hf.range_eq]; rw [← Set.image_univ]
    exact (PreirreducibleSpace.isPreirreducible_univ).image _ hfc.continuousOn
  toNonempty := Nonempty.map f inferInstance

/--
lemma `Homeomorph.irreducibleSpace_iff` / 引理 `Homeomorph.irreducibleSpace_iff`

English:
lemma Homeomorph.irreducibleSpace_iff
  proof: ⟨fun _ => e.surjective.irreducibleSpace e.continuous,
    fun _ => e.symm.surjective.irreducibleSpace e.symm.continuous⟩

中文:
引理 同胚.irreducibleSpace_iff
  证明: ⟨fun _ => e.surjective.irreducibleSpace e.continuous,
    fun _ => e.symm.surjective.irreducibleSpace e.symm.continuous⟩

Depends on / 依赖: continuous, e.continuous, e.surjective.irreducibleSpace, e.symm.continuous, e.symm.surjective.irreducibleSpace, irreducibleSpace, surjective
-/
lemma Homeomorph.irreducibleSpace_iff
    (e : X ≃ₜ Y) : IrreducibleSpace X ↔ IrreducibleSpace Y :=
  ⟨fun _ => e.surjective.irreducibleSpace e.continuous,
    fun _ => e.symm.surjective.irreducibleSpace e.symm.continuous⟩
