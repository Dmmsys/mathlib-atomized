/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Peter Pfaffelhuber
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.Cylinders

/-! # Cylinders with closed compact bases

We define the set of all cylinders with closed compact bases. Those sets play a role in the
proof of Kolmogorov's extension theorem.

## Main definitions

* `closedCompactCylinders X`: the set of all cylinders of `Π i, X i` based on closed compact sets.

## Main statements

* `mem_measurableCylinders_of_mem_closedCompactCylinders`: in a topological space with second
  countable topology and measurable open sets, a set in `closedCompactCylinders X` is a measurable
  cylinder.

-/

@[expose] public section

open Set

namespace MeasureTheory

variable {ι : Type*} {X : ι -> Type*} [forall i, TopologicalSpace (X i)] {t : Set (Π i, X i)}

variable (X) in
/--
Definition of `closedCompactCylinders` / `closedCompactCylinders` 的定义

English:
definition closedCompactCylinders
  signature: : Set (Set (Π i, X i))
  body: ⋃ (s) (S) (_ : IsClosed S) (_ : IsCompact S), {cylinder s S}

中文:
定义 closedCompactCylinders
  签名: : 集合 (集合 (Π i, X i))
  定义体: ⋃ (s) (S) (_ : IsClosed S) (_ : IsCompact S), {cylinder s S}

Depends on / 依赖: IsClosed, IsCompact, cylinder
-/
def closedCompactCylinders : Set (Set (Π i, X i)) :=
  ⋃ (s) (S) (_ : IsClosed S) (_ : IsCompact S), {cylinder s S}

variable (X) in
/--
theorem `empty_mem_closedCompactCylinders` / 定理 `empty_mem_closedCompactCylinders`

English:
theorem empty_mem_closedCompactCylinders
  statement: ∅ in closedCompactCylinders X
  proof: by
  simp_rw [closedCompactCylinders, mem_iUnion, mem_singleton_iff]
  exact ⟨∅, ∅, isClosed_empty, isCompact_empty, (cylinder_empty _).symm⟩

中文:
定理 empty_mem_closedCompactCylinders
  结论: ∅ in closedCompactCylinders X
  证明: by
  simp_rw [closedCompactCylinders, mem_iUnion, mem_singleton_iff]
  exact ⟨∅, ∅, isClosed_empty, isCompact_empty, (cylinder_empty _).symm⟩

Depends on / 依赖: closedCompactCylinders, cylinder_empty, isClosed_empty, isCompact_empty, mem_iUnion, mem_singleton_iff, simp_rw
-/
theorem empty_mem_closedCompactCylinders : ∅ in closedCompactCylinders X := by
  simp_rw [closedCompactCylinders, mem_iUnion, mem_singleton_iff]
  exact ⟨∅, ∅, isClosed_empty, isCompact_empty, (cylinder_empty _).symm⟩

/--
theorem `mem_closedCompactCylinders` / 定理 `mem_closedCompactCylinders`

English:
theorem mem_closedCompactCylinders
  given: (t : Set (Π i, X i))
  proof: by
  simp_rw [closedCompactCylinders, mem_iUnion, mem_singleton_iff, exists_prop]

中文:
定理 mem_closedCompactCylinders
  条件: (t : 集合 (Π i, X i))
  证明: by
  simp_rw [closedCompactCylinders, mem_iUnion, mem_singleton_iff, exists_prop]

Depends on / 依赖: closedCompactCylinders, exists_prop, mem_iUnion, mem_singleton_iff, simp_rw
-/
theorem mem_closedCompactCylinders (t : Set (Π i, X i)) :
    t in closedCompactCylinders X
      ↔ exists (s S : _), IsClosed S ∧ IsCompact S ∧ t = cylinder s S := by
  simp_rw [closedCompactCylinders, mem_iUnion, mem_singleton_iff, exists_prop]

/--
Definition of `closedCompactCylinders.finset` / `closedCompactCylinders.finset` 的定义

English:
definition closedCompactCylinders.finset
  signature: (ht : t in closedCompactCylinders X)
  body: ((mem_closedCompactCylinders t).mp ht).choose

中文:
定义 closedCompactCylinders.finset
  签名: (ht : t in closedCompactCylinders X)
  定义体: ((mem_closedCompactCylinders t).mp ht).choose

Depends on / 依赖: mem_closedCompactCylinders
-/
noncomputable def closedCompactCylinders.finset (ht : t in closedCompactCylinders X) :
    Finset ι :=
  ((mem_closedCompactCylinders t).mp ht).choose

-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- See https://github.com/leanprover/lean4/issues/14084.
/--
Definition of `closedCompactCylinders.set` / `closedCompactCylinders.set` 的定义

English:
definition closedCompactCylinders.set
  signature: (ht : t in closedCompactCylinders X)
  body: ((mem_closedCompactCylinders t).mp ht).choose_spec.choose

中文:
定义 closedCompactCylinders.set
  签名: (ht : t in closedCompactCylinders X)
  定义体: ((mem_closedCompactCylinders t).mp ht).choose_spec.choose

Depends on / 依赖: choose_spec, choose_spec.choose, mem_closedCompactCylinders
-/
noncomputable def closedCompactCylinders.set (ht : t in closedCompactCylinders X) :
    Set (Π i : closedCompactCylinders.finset ht, X i) :=
  ((mem_closedCompactCylinders t).mp ht).choose_spec.choose

/--
theorem `closedCompactCylinders.isClosed` / 定理 `closedCompactCylinders.isClosed`

English:
theorem closedCompactCylinders.isClosed
  given: (ht : t in closedCompactCylinders X)
  proof: ((mem_closedCompactCylinders t).mp ht).choose_spec.choose_spec.1

中文:
定理 closedCompactCylinders.isClosed
  条件: (ht : t in closedCompactCylinders X)
  证明: ((mem_closedCompactCylinders t).mp ht).choose_spec.choose_spec.1

Depends on / 依赖: choose_spec, choose_spec.choose_spec, mem_closedCompactCylinders
-/
theorem closedCompactCylinders.isClosed (ht : t in closedCompactCylinders X) :
    IsClosed (closedCompactCylinders.set ht) :=
  ((mem_closedCompactCylinders t).mp ht).choose_spec.choose_spec.1

/--
theorem `closedCompactCylinders.isCompact` / 定理 `closedCompactCylinders.isCompact`

English:
theorem closedCompactCylinders.isCompact
  given: (ht : t in closedCompactCylinders X)
  proof: ((mem_closedCompactCylinders t).mp ht).choose_spec.choose_spec.2.1

中文:
定理 closedCompactCylinders.isCompact
  条件: (ht : t in closedCompactCylinders X)
  证明: ((mem_closedCompactCylinders t).mp ht).choose_spec.choose_spec.2.1

Depends on / 依赖: choose_spec, choose_spec.choose_spec, mem_closedCompactCylinders
-/
theorem closedCompactCylinders.isCompact (ht : t in closedCompactCylinders X) :
    IsCompact (closedCompactCylinders.set ht) :=
  ((mem_closedCompactCylinders t).mp ht).choose_spec.choose_spec.2.1

/--
theorem `closedCompactCylinders.eq_cylinder` / 定理 `closedCompactCylinders.eq_cylinder`

English:
theorem closedCompactCylinders.eq_cylinder
  given: (ht : t in closedCompactCylinders X)
  proof: ((mem_closedCompactCylinders t).mp ht).choose_spec.choose_spec.2.2

中文:
定理 closedCompactCylinders.eq_cylinder
  条件: (ht : t in closedCompactCylinders X)
  证明: ((mem_closedCompactCylinders t).mp ht).choose_spec.choose_spec.2.2

Depends on / 依赖: choose_spec, choose_spec.choose_spec, mem_closedCompactCylinders
-/
theorem closedCompactCylinders.eq_cylinder (ht : t in closedCompactCylinders X) :
    t = cylinder (closedCompactCylinders.finset ht) (closedCompactCylinders.set ht) :=
  ((mem_closedCompactCylinders t).mp ht).choose_spec.choose_spec.2.2

/--
theorem `cylinder_mem_closedCompactCylinders` / 定理 `cylinder_mem_closedCompactCylinders`

English:
theorem cylinder_mem_closedCompactCylinders
  statement: (s : Finset ι) (S : Set (Π i : s, X i))
  proof: by
  rw [mem_closedCompactCylinders]
  exact ⟨s, S, hS_closed, hS_compact, rfl⟩

中文:
定理 cylinder_mem_closedCompactCylinders
  结论: (s : 有限集 ι) (S : 集合 (Π i : s, X i))
  证明: by
  rw [mem_closedCompactCylinders]
  exact ⟨s, S, hS_closed, hS_compact, rfl⟩

Depends on / 依赖: hS_closed, hS_compact, mem_closedCompactCylinders
-/
theorem cylinder_mem_closedCompactCylinders (s : Finset ι) (S : Set (Π i : s, X i))
    (hS_closed : IsClosed S) (hS_compact : IsCompact S) :
    cylinder s S in closedCompactCylinders X := by
  rw [mem_closedCompactCylinders]
  exact ⟨s, S, hS_closed, hS_compact, rfl⟩

/--
theorem `mem_measurableCylinders_of_mem_closedCompactCylinders` / 定理 `mem_measurableCylinders_of_mem_closedCompactCylinders`

English:
theorem mem_measurableCylinders_of_mem_closedCompactCylinders
  statement: [forall i, MeasurableSpace (X i)]
  proof: by
  rw [mem_measurableCylinders]
  refine ⟨closedCompactCylinders.finset ht, closedCompactCylinders.set ht, ?_, ?_⟩
  · exact (closedCompactCylinders.isClosed ht).measurableSet
  · exact closedCompactCylinders.eq_cylinder ht

中文:
定理 mem_measurableCylinders_of_mem_closedCompactCylinders
  结论: [对任意 i, 可测空间 (X i)]
  证明: by
  rw [mem_measurableCylinders]
  refine ⟨closedCompactCylinders.finset ht, closedCompactCylinders.set ht, ?_, ?_⟩
  · exact (closedCompactCylinders.isClosed ht).measurableSet
  · exact closedCompactCylinders.eq_cylinder ht

Depends on / 依赖: closedCompactCylinders, closedCompactCylinders.eq_cylinder, closedCompactCylinders.finset, closedCompactCylinders.isClosed, closedCompactCylinders.set, eq_cylinder, finset, isClosed, measurableSet, mem_measurableCylinders
-/
theorem mem_measurableCylinders_of_mem_closedCompactCylinders [forall i, MeasurableSpace (X i)]
    [forall i, SecondCountableTopology (X i)] [forall i, OpensMeasurableSpace (X i)]
    (ht : t in closedCompactCylinders X) :
    t in measurableCylinders X := by
  rw [mem_measurableCylinders]
  refine ⟨closedCompactCylinders.finset ht, closedCompactCylinders.set ht, ?_, ?_⟩
  · exact (closedCompactCylinders.isClosed ht).measurableSet
  · exact closedCompactCylinders.eq_cylinder ht

end MeasureTheory
