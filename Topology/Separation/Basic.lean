/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Algebra.Notation.Support
public import Mathlib.Topology.Inseparable
public import Mathlib.Topology.Piecewise
public import Mathlib.Topology.Separation.SeparatedNhds
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Bases
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Separation properties of topological spaces

This file defines some of the weaker separation axioms (under the Kolmogorov classification),
notably T₀, R₀, T₁ and R₁ spaces. For T₂ (Hausdorff) spaces and other stronger
conditions, see the file `Mathlib/Topology/Separation/Hausdorff.lean`.

## Main definitions

* `SeparatedNhds`: Two `Set`s are separated by neighbourhoods if they are contained in disjoint
  open sets.
* `HasSeparatingCover`: A set has a countable cover that can be used with
  `hasSeparatingCovers_iff_separatedNhds` to witness when two `Set`s have `SeparatedNhds`.
* `T0Space`: A T₀/Kolmogorov space is a space where, for every two points `x ≠ y`,
  there is an open set that contains one, but not the other.
* `R0Space`: An R₀ space (sometimes called a *symmetric space*) is a topological space
  such that the `Specializes` relation is symmetric.
* `T1Space`: A T₁/Fréchet space is a space where every singleton set is closed.
  This is equivalent to, for every pair `x ≠ y`, there existing an open set containing `x`
  but not `y` (`t1Space_iff_exists_open` shows that these conditions are equivalent.)
  T₁ iff T₀ and R₀.
* `R1Space`: An R₁/preregular space is a space where any two topologically distinguishable points
  have disjoint neighbourhoods. R₁ implies R₀.

Note that `mathlib` adopts the modern convention that `m ≤ n` if and only if `T_m → T_n`, but
occasionally the literature swaps definitions for e.g. T₃ and regular.

## Main results

### T₀ spaces

* `IsClosed.exists_closed_singleton`: Given a closed set `S` in a compact T₀ space,
  there is some `x ∈ S` such that `{x}` is closed.
* `exists_isOpen_singleton_of_isOpen_finite`: Given an open finite set `S` in a T₀ space,
  there is some `x ∈ S` such that `{x}` is open.

### T₁ spaces

* `isClosedMap_const`: The constant map is a closed map.
* `Finite.instDiscreteTopology`: A finite T₁ space must have the discrete topology.

## References

* <https://en.wikipedia.org/wiki/Separation_axiom>
* [Willard's *General Topology*][zbMATH02107988]
-/

@[expose] public section

open Function Set Filter Topology TopologicalSpace

universe u v

variable {X : Type*} {Y : Type*} [TopologicalSpace X]

section Separation

/-- A T₀ space, also known as a Kolmogorov space, is a topological space such that for every pair
`x ≠ y`, there is an open set containing one but not the other. We formulate the definition in terms
of the `Inseparable` relation. -/
@[stacks 004X "(2)"]
/--
Definition of `T0Space` / `T0Space` 的定义

English:
class T0Space
  parameters: (X : Type u) [TopologicalSpace X]
  axioms and operations (1):
    - t0 : forall ⦃x y : X⦄, Inseparable x y -> x = y

中文:
类 T0Space
  参数: (X : 类型u) [TopologicalSpace X]
  公理与运算 (1 个):
    - t0 : 对任意 ⦃x y : X⦄, Inseparable x y -> x = y
-/
class T0Space (X : Type u) [TopologicalSpace X] : Prop where
  /-- Two inseparable points in a T₀ space are equal. -/
  t0 : forall ⦃x y : X⦄, Inseparable x y -> x = y

/--
theorem `t0Space_iff_inseparable` / 定理 `t0Space_iff_inseparable`

English:
theorem t0Space_iff_inseparable
  given: (X : Type u) [TopologicalSpace X]
  proof: ⟨fun ⟨h⟩ => h, fun h => ⟨h⟩⟩

中文:
定理 t0Space_iff_inseparable
  条件: (X : 类型u) [TopologicalSpace X]
  证明: ⟨fun ⟨h⟩ => h, fun h => ⟨h⟩⟩
-/
theorem t0Space_iff_inseparable (X : Type u) [TopologicalSpace X] :
    T0Space X ↔ forall x y : X, Inseparable x y -> x = y :=
  ⟨fun ⟨h⟩ => h, fun h => ⟨h⟩⟩

/--
theorem `t0Space_iff_not_inseparable` / 定理 `t0Space_iff_not_inseparable`

English:
theorem t0Space_iff_not_inseparable
  given: (X : Type u) [TopologicalSpace X]
  proof: by
  simp only [t0Space_iff_inseparable, Ne, not_imp_not, Pairwise]

中文:
定理 t0Space_iff_not_inseparable
  条件: (X : 类型u) [TopologicalSpace X]
  证明: by
  simp only [t0Space_iff_inseparable, Ne, not_imp_not, Pairwise]

Depends on / 依赖: Pairwise, not_imp_not, t0Space_iff_inseparable
-/
theorem t0Space_iff_not_inseparable (X : Type u) [TopologicalSpace X] :
    T0Space X ↔ Pairwise fun x y : X => ¬Inseparable x y := by
  simp only [t0Space_iff_inseparable, Ne, not_imp_not, Pairwise]

/--
theorem `Inseparable.eq` / 定理 `Inseparable.eq`

English:
theorem Inseparable.eq
  given: [T0Space X] {x y : X} (h : Inseparable x y)
  statement: x = y
  proof: T0Space.t0 h

中文:
定理 Inseparable.eq
  条件: [T0Space X] {x y : X} (h : Inseparable x y)
  结论: x = y
  证明: T0Space.t0 h

Depends on / 依赖: T0Space, T0Space.t0
-/
theorem Inseparable.eq [T0Space X] {x y : X} (h : Inseparable x y) : x = y :=
  T0Space.t0 h

/--
theorem `Topology.IsInducing.injective` / 定理 `Topology.IsInducing.injective`

English:
theorem Topology.IsInducing.injective
  statement: [TopologicalSpace Y] [T0Space X] {f : X -> Y}
  proof: fun _ _ h =>
  (hf.inseparable_iff.1 <| .of_eq h).eq

中文:
定理 Topology.IsInducing.injective
  结论: [TopologicalSpace Y] [T0Space X] {f : X -> Y}
  证明: fun _ _ h =>
  (hf.inseparable_iff.1 <| .of_eq h).eq
-/
protected theorem Topology.IsInducing.injective [TopologicalSpace Y] [T0Space X] {f : X -> Y}
    (hf : IsInducing f) : Injective f := fun _ _ h =>
  (hf.inseparable_iff.1 <| .of_eq h).eq

/--
theorem `Topology.IsInducing.isEmbedding` / 定理 `Topology.IsInducing.isEmbedding`

English:
theorem Topology.IsInducing.isEmbedding
  statement: [TopologicalSpace Y] [T0Space X] {f : X -> Y}
  proof: ⟨hf, hf.injective⟩

中文:
定理 Topology.IsInducing.isEmbedding
  结论: [TopologicalSpace Y] [T0Space X] {f : X -> Y}
  证明: ⟨hf, hf.injective⟩
-/
protected theorem Topology.IsInducing.isEmbedding [TopologicalSpace Y] [T0Space X] {f : X -> Y}
    (hf : IsInducing f) : IsEmbedding f :=
  ⟨hf, hf.injective⟩

/--
lemma `isEmbedding_iff_isInducing` / 引理 `isEmbedding_iff_isInducing`

English:
lemma isEmbedding_iff_isInducing
  given: [TopologicalSpace Y] [T0Space X] {f : X -> Y}
  proof: ⟨IsEmbedding.isInducing, IsInducing.isEmbedding⟩

中文:
引理 isEmbedding_iff_isInducing
  条件: [TopologicalSpace Y] [T0Space X] {f : X -> Y}
  证明: ⟨IsEmbedding.isInducing, IsInducing.isEmbedding⟩

Depends on / 依赖: IsEmbedding, IsEmbedding.isInducing, IsInducing, IsInducing.isEmbedding, isEmbedding, isInducing
-/
lemma isEmbedding_iff_isInducing [TopologicalSpace Y] [T0Space X] {f : X -> Y} :
    IsEmbedding f ↔ IsInducing f :=
  ⟨IsEmbedding.isInducing, IsInducing.isEmbedding⟩

/--
theorem `t0Space_iff_nhds_injective` / 定理 `t0Space_iff_nhds_injective`

English:
theorem t0Space_iff_nhds_injective
  given: (X : Type u) [TopologicalSpace X]
  proof: t0Space_iff_inseparable X

中文:
定理 t0Space_iff_nhds_injective
  条件: (X : 类型u) [TopologicalSpace X]
  证明: t0Space_iff_inseparable X

Depends on / 依赖: t0Space_iff_inseparable
-/
theorem t0Space_iff_nhds_injective (X : Type u) [TopologicalSpace X] :
    T0Space X ↔ Injective (𝓝 : X -> Filter X) :=
  t0Space_iff_inseparable X

/--
theorem `nhds_injective` / 定理 `nhds_injective`

English:
theorem nhds_injective
  given: [T0Space X]
  statement: Injective (𝓝 : X -> Filter X)
  proof: (t0Space_iff_nhds_injective X).1 ‹_›

中文:
定理 nhds_injective
  条件: [T0Space X]
  结论: Injective (𝓝 : X -> Filter X)
  证明: (t0Space_iff_nhds_injective X).1 ‹_›

Depends on / 依赖: t0Space_iff_nhds_injective
-/
theorem nhds_injective [T0Space X] : Injective (𝓝 : X -> Filter X) :=
  (t0Space_iff_nhds_injective X).1 ‹_›

/--
theorem `inseparable_iff_eq` / 定理 `inseparable_iff_eq`

English:
theorem inseparable_iff_eq
  given: [T0Space X] {x y : X}
  statement: Inseparable x y ↔ x = y
  proof: nhds_injective.eq_iff

@[simp]

中文:
定理 inseparable_iff_eq
  条件: [T0Space X] {x y : X}
  结论: Inseparable x y ↔ x = y
  证明: nhds_injective.eq_iff

@[simp]

Depends on / 依赖: eq_iff, nhds_injective, nhds_injective.eq_iff
-/
theorem inseparable_iff_eq [T0Space X] {x y : X} : Inseparable x y ↔ x = y :=
  nhds_injective.eq_iff

@[simp]
/--
theorem `nhds_eq_nhds_iff` / 定理 `nhds_eq_nhds_iff`

English:
theorem nhds_eq_nhds_iff
  given: [T0Space X] {a b : X}
  statement: 𝓝 a = 𝓝 b ↔ a = b
  proof: nhds_injective.eq_iff

@[simp]

中文:
定理 nhds_eq_nhds_iff
  条件: [T0Space X] {a b : X}
  结论: 𝓝 a = 𝓝 b ↔ a = b
  证明: nhds_injective.eq_iff

@[simp]

Depends on / 依赖: eq_iff, nhds_injective, nhds_injective.eq_iff
-/
theorem nhds_eq_nhds_iff [T0Space X] {a b : X} : 𝓝 a = 𝓝 b ↔ a = b :=
  nhds_injective.eq_iff

@[simp]
/--
theorem `inseparable_eq_eq` / 定理 `inseparable_eq_eq`

English:
theorem inseparable_eq_eq
  given: [T0Space X]
  statement: Inseparable = @Eq X
  proof: funext₂ fun _ _ => propext inseparable_iff_eq

中文:
定理 inseparable_eq_eq
  条件: [T0Space X]
  结论: Inseparable = @Eq X
  证明: funext₂ fun _ _ => propext inseparable_iff_eq

Depends on / 依赖: inseparable_iff_eq, propext
-/
theorem inseparable_eq_eq [T0Space X] : Inseparable = @Eq X :=
  funext₂ fun _ _ => propext inseparable_iff_eq

/--
theorem `TopologicalSpace.IsTopologicalBasis.inseparable_iff` / 定理 `TopologicalSpace.IsTopologicalBasis.inseparable_iff`

English:
theorem TopologicalSpace.IsTopologicalBasis.inseparable_iff
  statement: {b : Set (Set X)}
  proof: ⟨fun h _ hs => inseparable_iff_forall_isOpen.1 h _ (hb.isOpen hs),
fun h => hb.nhds_hasBasis.eq_of_same_basis by
      convert! hb.nhds_hasBasis using 2
      exact and_congr_right (h _)⟩

中文:
定理 TopologicalSpace.IsTopologicalBasis.inseparable_iff
  结论: {b : Set (Set X)}
  证明: ⟨fun h _ hs => inseparable_iff_forall_isOpen.1 h _ (hb.isOpen hs),
fun h => hb.nhds_hasBasis.eq_of_same_basis by
      convert! hb.nhds_hasBasis using 2
      exact and_congr_right (h _)⟩

Depends on / 依赖: and_congr_right, convert, eq_of_same_basis, hb.isOpen, hb.nhds_hasBasis, hb.nhds_hasBasis.eq_of_same_basis, inseparable_iff_forall_isOpen, isOpen, nhds_hasBasis
-/
theorem TopologicalSpace.IsTopologicalBasis.inseparable_iff {b : Set (Set X)}
    (hb : IsTopologicalBasis b) {x y : X} : Inseparable x y ↔ forall s in b, (x in s ↔ y in s) :=
  ⟨fun h _ hs => inseparable_iff_forall_isOpen.1 h _ (hb.isOpen hs),
fun h => hb.nhds_hasBasis.eq_of_same_basis by
      convert! hb.nhds_hasBasis using 2
      exact and_congr_right (h _)⟩

/--
theorem `TopologicalSpace.IsTopologicalBasis.eq_iff` / 定理 `TopologicalSpace.IsTopologicalBasis.eq_iff`

English:
theorem TopologicalSpace.IsTopologicalBasis.eq_iff
  statement: [T0Space X] {b : Set (Set X)}
  proof: inseparable_iff_eq.symm.trans hb.inseparable_iff

中文:
定理 TopologicalSpace.IsTopologicalBasis.eq_iff
  结论: [T0Space X] {b : Set (Set X)}
  证明: inseparable_iff_eq.symm.trans hb.inseparable_iff

Depends on / 依赖: hb.inseparable_iff, inseparable_iff, inseparable_iff_eq, inseparable_iff_eq.symm.trans
-/
theorem TopologicalSpace.IsTopologicalBasis.eq_iff [T0Space X] {b : Set (Set X)}
    (hb : IsTopologicalBasis b) {x y : X} : x = y ↔ forall s in b, (x in s ↔ y in s) :=
  inseparable_iff_eq.symm.trans hb.inseparable_iff

/--
theorem `t0Space_iff_exists_isOpen_xor_mem` / 定理 `t0Space_iff_exists_isOpen_xor_mem`

English:
theorem t0Space_iff_exists_isOpen_xor_mem
  given: (X : Type u) [TopologicalSpace X]
  proof: by
  simp only [t0Space_iff_not_inseparable, xor_iff_not_iff, not_forall, exists_prop,
    inseparable_iff_forall_isOpen, Pairwise]

@[deprecated (since := "2026-04-04")]
alias t0Space_iff_exists_isOpen_xor'_mem := t0Space_iff_exists_isOpen_xor_mem

中文:
定理 t0Space_iff_exists_isOpen_xor_mem
  条件: (X : 类型u) [TopologicalSpace X]
  证明: by
  simp only [t0Space_iff_not_inseparable, xor_iff_not_iff, not_forall, exists_prop,
    inseparable_iff_forall_isOpen, Pairwise]

@[deprecated (since := "2026-04-04")]
alias t0Space_iff_exists_isOpen_xor'_mem := t0Space_iff_exists_isOpen_xor_mem

Depends on / 依赖: Pairwise, exists_prop, inseparable_iff_forall_isOpen, not_forall, t0Space_iff_not_inseparable, xor_iff_not_iff
-/
theorem t0Space_iff_exists_isOpen_xor_mem (X : Type u) [TopologicalSpace X] :
    T0Space X ↔ Pairwise fun x y => exists U : Set X, IsOpen U ∧ Xor (x in U) (y in U) := by
  simp only [t0Space_iff_not_inseparable, xor_iff_not_iff, not_forall, exists_prop,
    inseparable_iff_forall_isOpen, Pairwise]

@[deprecated (since := "2026-04-04")]
alias t0Space_iff_exists_isOpen_xor'_mem := t0Space_iff_exists_isOpen_xor_mem

/--
theorem `exists_isOpen_xor_mem` / 定理 `exists_isOpen_xor_mem`

English:
theorem exists_isOpen_xor_mem
  given: [T0Space X] {x y : X} (h : x != y)
  proof: (t0Space_iff_exists_isOpen_xor_mem X).1 ‹_› h

@[deprecated (since := "2026-04-04")] alias exists_isOpen_xor'_mem := exists_isOpen_xor_mem

中文:
定理 exists_isOpen_xor_mem
  条件: [T0Space X] {x y : X} (h : x != y)
  证明: (t0Space_iff_exists_isOpen_xor_mem X).1 ‹_› h

@[deprecated (since := "2026-04-04")] alias exists_isOpen_xor'_mem := exists_isOpen_xor_mem

Depends on / 依赖: t0Space_iff_exists_isOpen_xor_mem
-/
theorem exists_isOpen_xor_mem [T0Space X] {x y : X} (h : x != y) :
    exists U : Set X, IsOpen U ∧ Xor (x in U) (y in U) :=
  (t0Space_iff_exists_isOpen_xor_mem X).1 ‹_› h

@[deprecated (since := "2026-04-04")] alias exists_isOpen_xor'_mem := exists_isOpen_xor_mem

/-- Specialization forms a partial order on a t0 topological space. -/
@[instance_reducible]
/--
Definition of `specializationOrder` / `specializationOrder` 的定义

English:
definition specializationOrder
  signature: (X) [TopologicalSpace X] [T0Space X]
  body: { specializationPreorder X, PartialOrder.lift (OrderDual.toDual ∘ 𝓝) nhds_injective with }

中文:
定义 specializationOrder
  签名: (X) [TopologicalSpace X] [T0Space X]
  定义体: { specializationPreorder X, PartialOrder.lift (OrderDual.toDual ∘ 𝓝) nhds_injective with }

Depends on / 依赖: OrderDual, OrderDual.toDual, PartialOrder, PartialOrder.lift, nhds_injective, specializationPreorder, toDual
-/
def specializationOrder (X) [TopologicalSpace X] [T0Space X] : PartialOrder X :=
  { specializationPreorder X, PartialOrder.lift (OrderDual.toDual ∘ 𝓝) nhds_injective with }

/--
Instance `SeparationQuotient.instT0Space` / 实例 `SeparationQuotient.instT0Space`

English:
instance SeparationQuotient.instT0Space
  signature: : T0Space (SeparationQuotient X)
  body: ⟨fun x y => Quotient.inductionOn₂' x y fun _ _ h =>
SeparationQuotient.mk_eq_mk.2 SeparationQuotient.isInducing_mk.inseparable_iff.1 h⟩

中文:
实例 SeparationQuotient.instT0Space
  签名: : T0Space (SeparationQuotient X)
  定义体: ⟨fun x y => Quotient.inductionOn₂' x y fun _ _ h =>
SeparationQuotient.mk_eq_mk.2 SeparationQuotient.isInducing_mk.inseparable_iff.1 h⟩

Depends on / 依赖: Quotient, Quotient.inductionOn, SeparationQuotient, SeparationQuotient.isInducing_mk.inseparable_iff, SeparationQuotient.mk_eq_mk, inseparable_iff, isInducing_mk, mk_eq_mk
-/
instance SeparationQuotient.instT0Space : T0Space (SeparationQuotient X) :=
  ⟨fun x y => Quotient.inductionOn₂' x y fun _ _ h =>
SeparationQuotient.mk_eq_mk.2 SeparationQuotient.isInducing_mk.inseparable_iff.1 h⟩

/--
theorem `minimal_nonempty_closed_subsingleton` / 定理 `minimal_nonempty_closed_subsingleton`

English:
theorem minimal_nonempty_closed_subsingleton
  statement: [T0Space X] {s : Set X} (hs : IsClosed s)
  proof: by
  refine fun x hx y hy => of_not_not fun hxy => ?_
  rcases exists_isOpen_xor_mem hxy with ⟨U, hUo, hU⟩
  wlog h : x in U ∧ y ∉ U
  · refine this hs hmin y hy x hx (Ne.symm hxy) U hUo hU.symm (hU.resolve_left h)
  obtain ⟨hxU, hyU⟩ := h
  have : s \ U = s := hmin (s \ U) sdiff_subset ⟨y, hy, hyU⟩

中文:
定理 minimal_nonempty_closed_subsingleton
  结论: [T0Space X] {s : Set X} (hs : IsClosed s)
  证明: by
  refine fun x hx y hy => of_not_not fun hxy => ?_
  rcases exists_isOpen_xor_mem hxy with ⟨U, hUo, hU⟩
  wlog h : x in U ∧ y ∉ U
  · refine this hs hmin y hy x hx (Ne.symm hxy) U hUo hU.symm (hU.resolve_left h)
  obtain ⟨hxU, hyU⟩ := h
  have : s \ U = s := hmin (s \ U) sdiff_subset ⟨y, hy, hyU⟩

Depends on / 依赖: Ne.symm, exists_isOpen_xor_mem, hU.resolve_left, hU.symm, hs.sdiff, of_not_not, resolve_left, sdiff_subset, subset, this.symm.subset
-/
theorem minimal_nonempty_closed_subsingleton [T0Space X] {s : Set X} (hs : IsClosed s)
    (hmin : forall t, t subseteq s -> t.Nonempty -> IsClosed t -> t = s) : s.Subsingleton := by
  refine fun x hx y hy => of_not_not fun hxy => ?_
  rcases exists_isOpen_xor_mem hxy with ⟨U, hUo, hU⟩
  wlog h : x in U ∧ y ∉ U
  · refine this hs hmin y hy x hx (Ne.symm hxy) U hUo hU.symm (hU.resolve_left h)
  obtain ⟨hxU, hyU⟩ := h
  have : s \ U = s := hmin (s \ U) sdiff_subset ⟨y, hy, hyU⟩ (hs.sdiff hUo)
  exact (this.symm.subset hx).2 hxU

/--
theorem `minimal_nonempty_closed_eq_singleton` / 定理 `minimal_nonempty_closed_eq_singleton`

English:
theorem minimal_nonempty_closed_eq_singleton
  statement: [T0Space X] {s : Set X} (hs : IsClosed s)
  proof: exists_eq_singleton_iff_nonempty_subsingleton.2
    ⟨hne, minimal_nonempty_closed_subsingleton hs hmin⟩

中文:
定理 minimal_nonempty_closed_eq_singleton
  结论: [T0Space X] {s : Set X} (hs : IsClosed s)
  证明: exists_eq_singleton_iff_nonempty_subsingleton.2
    ⟨hne, minimal_nonempty_closed_subsingleton hs hmin⟩

Depends on / 依赖: exists_eq_singleton_iff_nonempty_subsingleton, minimal_nonempty_closed_subsingleton
-/
theorem minimal_nonempty_closed_eq_singleton [T0Space X] {s : Set X} (hs : IsClosed s)
    (hne : s.Nonempty) (hmin : forall t, t subseteq s -> t.Nonempty -> IsClosed t -> t = s) : exists x, s = {x} :=
  exists_eq_singleton_iff_nonempty_subsingleton.2
    ⟨hne, minimal_nonempty_closed_subsingleton hs hmin⟩

/--
theorem `IsClosed.exists_closed_singleton` / 定理 `IsClosed.exists_closed_singleton`

English:
theorem IsClosed.exists_closed_singleton
  statement: [T0Space X] [CompactSpace X] {S : Set X}
  proof: by
  obtain ⟨V, Vsub, Vne, Vcls, hV⟩ := hS.exists_minimal_nonempty_closed_subset hne
  rcases minimal_nonempty_closed_eq_singleton Vcls Vne hV with ⟨x, rfl⟩
  exact ⟨x, Vsub (mem_singleton x), Vcls⟩

中文:
定理 IsClosed.exists_closed_singleton
  结论: [T0Space X] [CompactSpace X] {S : Set X}
  证明: by
  obtain ⟨V, Vsub, Vne, Vcls, hV⟩ := hS.exists_minimal_nonempty_closed_subset hne
  rcases minimal_nonempty_closed_eq_singleton Vcls Vne hV with ⟨x, rfl⟩
  exact ⟨x, Vsub (mem_singleton x), Vcls⟩

Depends on / 依赖: exists_minimal_nonempty_closed_subset, hS.exists_minimal_nonempty_closed_subset, mem_singleton, minimal_nonempty_closed_eq_singleton
-/
theorem IsClosed.exists_closed_singleton [T0Space X] [CompactSpace X] {S : Set X}
    (hS : IsClosed S) (hne : S.Nonempty) : exists x : X, x in S ∧ IsClosed ({x} : Set X) := by
  obtain ⟨V, Vsub, Vne, Vcls, hV⟩ := hS.exists_minimal_nonempty_closed_subset hne
  rcases minimal_nonempty_closed_eq_singleton Vcls Vne hV with ⟨x, rfl⟩
  exact ⟨x, Vsub (mem_singleton x), Vcls⟩

/--
theorem `minimal_nonempty_open_subsingleton` / 定理 `minimal_nonempty_open_subsingleton`

English:
theorem minimal_nonempty_open_subsingleton
  statement: [T0Space X] {s : Set X} (hs : IsOpen s)
  proof: by
  refine fun x hx y hy => of_not_not fun hxy => ?_
  rcases exists_isOpen_xor_mem hxy with ⟨U, hUo, hU⟩
  wlog h : x in U ∧ y ∉ U
  · exact this hs hmin y hy x hx (Ne.symm hxy) U hUo hU.symm (hU.resolve_left h)
  obtain ⟨hxU, hyU⟩ := h
  have : s inter U = s := hmin (s inter U) inter_subset_left 

中文:
定理 minimal_nonempty_open_subsingleton
  结论: [T0Space X] {s : Set X} (hs : IsOpen s)
  证明: by
  refine fun x hx y hy => of_not_not fun hxy => ?_
  rcases exists_isOpen_xor_mem hxy with ⟨U, hUo, hU⟩
  wlog h : x in U ∧ y ∉ U
  · exact this hs hmin y hy x hx (Ne.symm hxy) U hUo hU.symm (hU.resolve_left h)
  obtain ⟨hxU, hyU⟩ := h
  have : s inter U = s := hmin (s inter U) inter_subset_left 

Depends on / 依赖: Ne.symm, exists_isOpen_xor_mem, hU.resolve_left, hU.symm, hs.inter, inter_subset_left, of_not_not, resolve_left, subset, this.symm.subset
-/
theorem minimal_nonempty_open_subsingleton [T0Space X] {s : Set X} (hs : IsOpen s)
    (hmin : forall t, t subseteq s -> t.Nonempty -> IsOpen t -> t = s) : s.Subsingleton := by
  refine fun x hx y hy => of_not_not fun hxy => ?_
  rcases exists_isOpen_xor_mem hxy with ⟨U, hUo, hU⟩
  wlog h : x in U ∧ y ∉ U
  · exact this hs hmin y hy x hx (Ne.symm hxy) U hUo hU.symm (hU.resolve_left h)
  obtain ⟨hxU, hyU⟩ := h
  have : s inter U = s := hmin (s inter U) inter_subset_left ⟨x, hx, hxU⟩ (hs.inter hUo)
  exact hyU (this.symm.subset hy).2

/--
theorem `minimal_nonempty_open_eq_singleton` / 定理 `minimal_nonempty_open_eq_singleton`

English:
theorem minimal_nonempty_open_eq_singleton
  statement: [T0Space X] {s : Set X} (hs : IsOpen s)
  proof: exists_eq_singleton_iff_nonempty_subsingleton.2 ⟨hne, minimal_nonempty_open_subsingleton hs hmin⟩

中文:
定理 minimal_nonempty_open_eq_singleton
  结论: [T0Space X] {s : Set X} (hs : IsOpen s)
  证明: exists_eq_singleton_iff_nonempty_subsingleton.2 ⟨hne, minimal_nonempty_open_subsingleton hs hmin⟩

Depends on / 依赖: exists_eq_singleton_iff_nonempty_subsingleton, minimal_nonempty_open_subsingleton
-/
theorem minimal_nonempty_open_eq_singleton [T0Space X] {s : Set X} (hs : IsOpen s)
    (hne : s.Nonempty) (hmin : forall t, t subseteq s -> t.Nonempty -> IsOpen t -> t = s) : exists x, s = {x} :=
  exists_eq_singleton_iff_nonempty_subsingleton.2 ⟨hne, minimal_nonempty_open_subsingleton hs hmin⟩

/--
theorem `exists_isOpen_singleton_of_isOpen_finite` / 定理 `exists_isOpen_singleton_of_isOpen_finite`

English:
theorem exists_isOpen_singleton_of_isOpen_finite
  statement: [T0Space X] {s : Set X} (hfin : s.Finite)
  proof: by
  lift s to Finset X using hfin
  induction s using Finset.strongInductionOn
  rename_i s ihs
  rcases em (exists t, t ⊂ s ∧ t.Nonempty ∧ IsOpen (t : Set X)) with (⟨t, hts, htne, hto⟩ | ht)
  · rcases ihs t hts htne hto with ⟨x, hxt, hxo⟩
    exact ⟨x, hts.1 hxt, hxo⟩
  · -- Porting note: was `rc

中文:
定理 exists_isOpen_singleton_of_isOpen_finite
  结论: [T0Space X] {s : Set X} (hfin : s.Finite)
  证明: by
  lift s to Finset X using hfin
  induction s using Finset.strongInductionOn
  rename_i s ihs
  rcases em (exists t, t ⊂ s ∧ t.Nonempty ∧ IsOpen (t : Set X)) with (⟨t, hts, htne, hto⟩ | ht)
  · rcases ihs t hts htne hto with ⟨x, hxt, hxo⟩
    exact ⟨x, hts.1 hxt, hxo⟩
  · -- Porting note: was `rc

Depends on / 依赖: Finset, Finset.strongInductionOn, IsOpen, Nonempty, Porting, minimal_nonempty_open_eq_singleton, rename_i, strongInductionOn, t.Nonempty
-/
theorem exists_isOpen_singleton_of_isOpen_finite [T0Space X] {s : Set X} (hfin : s.Finite)
    (hne : s.Nonempty) (ho : IsOpen s) : exists x in s, IsOpen ({x} : Set X) := by
  lift s to Finset X using hfin
  induction s using Finset.strongInductionOn
  rename_i s ihs
  rcases em (exists t, t ⊂ s ∧ t.Nonempty ∧ IsOpen (t : Set X)) with (⟨t, hts, htne, hto⟩ | ht)
  · rcases ihs t hts htne hto with ⟨x, hxt, hxo⟩
    exact ⟨x, hts.1 hxt, hxo⟩
  · -- Porting note: was `rcases minimal_nonempty_open_eq_singleton ho hne _ with ⟨x, hx⟩`
    -- https://github.com/leanprover-community/batteries/issues/116
    rsuffices ⟨x, hx⟩ : exists x, (s : Set X) = {x}
    · exact ⟨x, hx.symm ▸ rfl, hx ▸ ho⟩
    refine minimal_nonempty_open_eq_singleton ho hne ?_
    refine fun t hts htne hto => of_not_not fun hts' => ht ?_
    lift t to Finset X using s.finite_toSet.subset hts
    exact ⟨t, ssubset_iff_subset_ne.2 ⟨hts, mt Finset.coe_inj.2 hts'⟩, htne, hto⟩

/--
theorem `exists_open_singleton_of_finite` / 定理 `exists_open_singleton_of_finite`

English:
theorem exists_open_singleton_of_finite
  given: [T0Space X] [Finite X] [Nonempty X]
  proof: let ⟨x, _, h⟩ := exists_isOpen_singleton_of_isOpen_finite (Set.toFinite _)
    univ_nonempty isOpen_univ
  ⟨x, h⟩

中文:
定理 exists_open_singleton_of_finite
  条件: [T0Space X] [Finite X] [Nonempty X]
  证明: let ⟨x, _, h⟩ := exists_isOpen_singleton_of_isOpen_finite (Set.toFinite _)
    univ_nonempty isOpen_univ
  ⟨x, h⟩

Depends on / 依赖: Set.toFinite, exists_isOpen_singleton_of_isOpen_finite, isOpen_univ, toFinite, univ_nonempty
-/
theorem exists_open_singleton_of_finite [T0Space X] [Finite X] [Nonempty X] :
    exists x : X, IsOpen ({x} : Set X) :=
  let ⟨x, _, h⟩ := exists_isOpen_singleton_of_isOpen_finite (Set.toFinite _)
    univ_nonempty isOpen_univ
  ⟨x, h⟩

/--
theorem `t0Space_of_injective_of_continuous` / 定理 `t0Space_of_injective_of_continuous`

English:
theorem t0Space_of_injective_of_continuous
  statement: [TopologicalSpace Y] {f : X -> Y}
  proof: ⟨fun _ _ h => hf (h.map hf').eq⟩

中文:
定理 t0Space_of_injective_of_continuous
  结论: [TopologicalSpace Y] {f : X -> Y}
  证明: ⟨fun _ _ h => hf (h.map hf').eq⟩

Depends on / 依赖: h.map
-/
theorem t0Space_of_injective_of_continuous [TopologicalSpace Y] {f : X -> Y}
    (hf : Function.Injective f) (hf' : Continuous f) [T0Space Y] : T0Space X :=
⟨fun _ _ h => hf (h.map hf').eq⟩

/--
theorem `Topology.IsEmbedding.t0Space` / 定理 `Topology.IsEmbedding.t0Space`

English:
theorem Topology.IsEmbedding.t0Space
  statement: [TopologicalSpace Y] [T0Space Y] {f : X -> Y}
  proof: t0Space_of_injective_of_continuous hf.injective hf.continuous

中文:
定理 Topology.IsEmbedding.t0Space
  结论: [TopologicalSpace Y] [T0Space Y] {f : X -> Y}
  证明: t0Space_of_injective_of_continuous hf.injective hf.continuous
-/
protected theorem Topology.IsEmbedding.t0Space [TopologicalSpace Y] [T0Space Y] {f : X -> Y}
    (hf : IsEmbedding f) : T0Space X :=
  t0Space_of_injective_of_continuous hf.injective hf.continuous

/--
theorem `Homeomorph.t0Space` / 定理 `Homeomorph.t0Space`

English:
theorem Homeomorph.t0Space
  given: [TopologicalSpace Y] [T0Space X] (h : X ≃ₜ Y)
  statement: T0Space Y
  proof: h.symm.isEmbedding.t0Space

@[stacks 0B31 "part 1"]

中文:
定理 Homeomorph.t0Space
  条件: [TopologicalSpace Y] [T0Space X] (h : X ≃ₜ Y)
  结论: T0Space Y
  证明: h.symm.isEmbedding.t0Space

@[stacks 0B31 "part 1"]
-/
protected theorem Homeomorph.t0Space [TopologicalSpace Y] [T0Space X] (h : X ≃ₜ Y) : T0Space Y :=
  h.symm.isEmbedding.t0Space

@[stacks 0B31 "part 1"]
/--
Instance `Subtype.t0Space` / 实例 `Subtype.t0Space`

English:
instance Subtype.t0Space
  signature: [T0Space X] {p : X -> Prop}
  body: IsEmbedding.subtypeVal.t0Space

中文:
实例 Subtype.t0Space
  签名: [T0Space X] {p : X -> 命题}
  定义体: IsEmbedding.subtypeVal.t0Space

Depends on / 依赖: IsEmbedding, IsEmbedding.subtypeVal.t0Space, subtypeVal, t0Space
-/
instance Subtype.t0Space [T0Space X] {p : X -> Prop} : T0Space (Subtype p) :=
  IsEmbedding.subtypeVal.t0Space

/--
theorem `t0Space_iff_or_notMem_closure` / 定理 `t0Space_iff_or_notMem_closure`

English:
theorem t0Space_iff_or_notMem_closure
  given: (X : Type u) [TopologicalSpace X]
  proof: by
  simp only [t0Space_iff_not_inseparable, inseparable_iff_mem_closure, not_and_or]

中文:
定理 t0Space_iff_or_notMem_closure
  条件: (X : 类型u) [TopologicalSpace X]
  证明: by
  simp only [t0Space_iff_not_inseparable, inseparable_iff_mem_closure, not_and_or]

Depends on / 依赖: inseparable_iff_mem_closure, not_and_or, t0Space_iff_not_inseparable
-/
theorem t0Space_iff_or_notMem_closure (X : Type u) [TopologicalSpace X] :
    T0Space X ↔ Pairwise fun a b : X => a ∉ closure ({b} : Set X) ∨ b ∉ closure ({a} : Set X) := by
  simp only [t0Space_iff_not_inseparable, inseparable_iff_mem_closure, not_and_or]

/--
Instance `Prod.instT0Space` / 实例 `Prod.instT0Space`

English:
instance Prod.instT0Space
  signature: [TopologicalSpace Y] [T0Space X] [T0Space Y]
  body: ⟨fun _ _ h => Prod.ext (h.map continuous_fst).eq (h.map continuous_snd).eq⟩

中文:
实例 Prod.instT0Space
  签名: [TopologicalSpace Y] [T0Space X] [T0Space Y]
  定义体: ⟨fun _ _ h => Prod.ext (h.map continuous_fst).eq (h.map continuous_snd).eq⟩

Depends on / 依赖: Prod.ext, continuous_fst, continuous_snd, h.map
-/
instance Prod.instT0Space [TopologicalSpace Y] [T0Space X] [T0Space Y] : T0Space (X × Y) :=
  ⟨fun _ _ h => Prod.ext (h.map continuous_fst).eq (h.map continuous_snd).eq⟩

/--
Instance `Pi.instT0Space` / 实例 `Pi.instT0Space`

English:
instance Pi.instT0Space
  signature: {ι : Type*} {X : ι -> Type*} [forall i, TopologicalSpace (X i)]
  body: ⟨fun _ _ h => funext fun i => (h.map (continuous_apply i)).eq⟩

中文:
实例 Pi.instT0Space
  签名: {ι : 类型} {X : ι -> 类型} [对任意 i, TopologicalSpace (X i)]
  定义体: ⟨fun _ _ h => funext fun i => (h.map (continuous_apply i)).eq⟩

Depends on / 依赖: continuous_apply, h.map
-/
instance Pi.instT0Space {ι : Type*} {X : ι -> Type*} [forall i, TopologicalSpace (X i)]
    [forall i, T0Space (X i)] :
    T0Space (forall i, X i) :=
  ⟨fun _ _ h => funext fun i => (h.map (continuous_apply i)).eq⟩

/--
Instance `ULift.instT0Space` / 实例 `ULift.instT0Space`

English:
instance ULift.instT0Space
  signature: [T0Space X]
  body: IsEmbedding.uliftDown.t0Space

中文:
实例 ULift.instT0Space
  签名: [T0Space X]
  定义体: IsEmbedding.uliftDown.t0Space

Depends on / 依赖: IsEmbedding, IsEmbedding.uliftDown.t0Space, t0Space, uliftDown
-/
instance ULift.instT0Space [T0Space X] : T0Space (ULift X) := IsEmbedding.uliftDown.t0Space

/--
theorem `T0Space.of_cover` / 定理 `T0Space.of_cover`

English:
theorem T0Space.of_cover
  given: (h : forall x y, Inseparable x y -> exists s : Set X, x in s ∧ y in s ∧ T0Space s)
  proof: by
  refine ⟨fun x y hxy => ?_⟩
  rcases h x y hxy with ⟨s, hxs, hys, hs⟩
  lift x to s using hxs; lift y to s using hys
  rw [← subtype_inseparable_iff] at hxy
  exact congr_arg Subtype.val hxy.eq

中文:
定理 T0Space.of_cover
  条件: (h : 对任意 x y, Inseparable x y -> 存在 s : Set X, x in s ∧ y in s ∧ T0Space s)
  证明: by
  refine ⟨fun x y hxy => ?_⟩
  rcases h x y hxy with ⟨s, hxs, hys, hs⟩
  lift x to s using hxs; lift y to s using hys
  rw [← subtype_inseparable_iff] at hxy
  exact congr_arg Subtype.val hxy.eq

Depends on / 依赖: Subtype, Subtype.val, congr_arg, hxy.eq, subtype_inseparable_iff
-/
theorem T0Space.of_cover (h : forall x y, Inseparable x y -> exists s : Set X, x in s ∧ y in s ∧ T0Space s) :
    T0Space X := by
  refine ⟨fun x y hxy => ?_⟩
  rcases h x y hxy with ⟨s, hxs, hys, hs⟩
  lift x to s using hxs; lift y to s using hys
  rw [← subtype_inseparable_iff] at hxy
  exact congr_arg Subtype.val hxy.eq

/--
theorem `T0Space.of_open_cover` / 定理 `T0Space.of_open_cover`

English:
theorem T0Space.of_open_cover
  given: (h : forall x, exists s : Set X, x in s ∧ IsOpen s ∧ T0Space s)
  statement: T0Space X
  proof: T0Space.of_cover fun x _ hxy =>
    let ⟨s, hxs, hso, hs⟩ := h x
    ⟨s, hxs, (hxy.mem_open_iff hso).1 hxs, hs⟩

中文:
定理 T0Space.of_open_cover
  条件: (h : 对任意 x, 存在 s : Set X, x in s ∧ IsOpen s ∧ T0Space s)
  结论: T0Space X
  证明: T0Space.of_cover fun x _ hxy =>
    let ⟨s, hxs, hso, hs⟩ := h x
    ⟨s, hxs, (hxy.mem_open_iff hso).1 hxs, hs⟩

Depends on / 依赖: T0Space, T0Space.of_cover, hxy.mem_open_iff, mem_open_iff, of_cover
-/
theorem T0Space.of_open_cover (h : forall x, exists s : Set X, x in s ∧ IsOpen s ∧ T0Space s) : T0Space X :=
  T0Space.of_cover fun x _ hxy =>
    let ⟨s, hxs, hso, hs⟩ := h x
    ⟨s, hxs, (hxy.mem_open_iff hso).1 hxs, hs⟩

/-- A topological space is called an R₀ space, if `Specializes` relation is symmetric.

In other words, given two points `x y : X`,
if every neighborhood of `y` contains `x`, then every neighborhood of `x` contains `y`. -/
@[mk_iff]
/--
Definition of `R0Space` / `R0Space` 的定义

English:
class R0Space
  parameters: (X : Type u) [TopologicalSpace X]
  axioms and operations (1):
    - specializes_symm : Std.Symm (Specializes : X -> X -> Prop)

中文:
类 R0Space
  参数: (X : 类型u) [TopologicalSpace X]
  公理与运算 (1 个):
    - specializes_symm : Std.Symm (Specializes : X -> X -> 命题)
-/
class R0Space (X : Type u) [TopologicalSpace X] : Prop where
  /-- In an R₀ space, the `Specializes` relation is symmetric. -/
  specializes_symm : Std.Symm (Specializes : X -> X -> Prop)

export R0Space (specializes_symm)

@[deprecated (since := "2026-06-10")]
alias R0Space.specializes_symmetric := R0Space.specializes_symm

export R0Space (specializes_symmetric)

section R0Space

variable [R0Space X] {x y : X}

/--
theorem `Specializes.symm` / 定理 `Specializes.symm`

English:
theorem Specializes.symm
  given: (h : x ⤳ y)
  statement: y ⤳ x
  proof: specializes_symm.symm x y h

中文:
定理 Specializes.symm
  条件: (h : x ⤳ y)
  结论: y ⤳ x
  证明: specializes_symm.symm x y h

Depends on / 依赖: specializes_symm, specializes_symm.symm
-/
theorem Specializes.symm (h : x ⤳ y) : y ⤳ x :=
  specializes_symm.symm x y h

/--
theorem `specializes_comm` / 定理 `specializes_comm`

English:
theorem specializes_comm
  statement: x ⤳ y ↔ y ⤳ x
  proof: ⟨Specializes.symm, Specializes.symm⟩

中文:
定理 specializes_comm
  结论: x ⤳ y ↔ y ⤳ x
  证明: ⟨Specializes.symm, Specializes.symm⟩

Depends on / 依赖: Specializes, Specializes.symm
-/
theorem specializes_comm : x ⤳ y ↔ y ⤳ x := ⟨Specializes.symm, Specializes.symm⟩

/--
theorem `specializes_iff_inseparable` / 定理 `specializes_iff_inseparable`

English:
theorem specializes_iff_inseparable
  statement: x ⤳ y ↔ Inseparable x y
  proof: ⟨fun h => h.antisymm h.symm, Inseparable.specializes⟩

中文:
定理 specializes_iff_inseparable
  结论: x ⤳ y ↔ Inseparable x y
  证明: ⟨fun h => h.antisymm h.symm, Inseparable.specializes⟩

Depends on / 依赖: Inseparable, Inseparable.specializes, antisymm, h.antisymm, h.symm, specializes
-/
theorem specializes_iff_inseparable : x ⤳ y ↔ Inseparable x y :=
  ⟨fun h => h.antisymm h.symm, Inseparable.specializes⟩

/-- In an R₀ space, `Specializes` implies `Inseparable`. -/
alias ⟨Specializes.inseparable, _⟩ := specializes_iff_inseparable

/--
theorem `Topology.IsInducing.r0Space` / 定理 `Topology.IsInducing.r0Space`

English:
theorem Topology.IsInducing.r0Space
  given: [TopologicalSpace Y] {f : Y -> X} (hf : IsInducing f)
  proof: by
    simpa only [← hf.specializes_iff] using Specializes.symm

中文:
定理 Topology.IsInducing.r0Space
  条件: [TopologicalSpace Y] {f : Y -> X} (hf : IsInducing f)
  证明: by
    simpa only [← hf.specializes_iff] using Specializes.symm

Depends on / 依赖: Specializes, Specializes.symm, hf.specializes_iff, specializes_iff
-/
theorem Topology.IsInducing.r0Space [TopologicalSpace Y] {f : Y -> X} (hf : IsInducing f) :
    R0Space Y where
  specializes_symm.symm a b := by
    simpa only [← hf.specializes_iff] using Specializes.symm

instance {p : X -> Prop} : R0Space {x // p x} := IsInducing.subtypeVal.r0Space

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [TopologicalSpace
  signature: Y] [R0Space Y] : R0Space (X × Y) where
  body: h.fst.symm.prod h.snd.symm

中文:
实例 [TopologicalSpace
  签名: Y] [R0Space Y] : R0Space (X × Y) where
  定义体: h.fst.symm.prod h.snd.symm

Depends on / 依赖: h.fst.symm.prod, h.snd.symm
-/
instance [TopologicalSpace Y] [R0Space Y] : R0Space (X × Y) where
  specializes_symm.symm _ _ h := h.fst.symm.prod h.snd.symm

instance {ι : Type*} {X : ι -> Type*} [forall i, TopologicalSpace (X i)] [forall i, R0Space (X i)] :
    R0Space (forall i, X i) where
  specializes_symm.symm _ _ h := specializes_pi.2 fun i => (specializes_pi.1 h i).symm

/--
lemma `R0Space.closure_singleton` / 引理 `R0Space.closure_singleton`

English:
lemma R0Space.closure_singleton
  given: (x : X)
  statement: closure {x} = (𝓝 x).ker
  proof: by
  ext; simp [ker_nhds_eq_specializes, ← specializes_iff_mem_closure, specializes_comm]

中文:
引理 R0Space.closure_singleton
  条件: (x : X)
  结论: closure {x} = (𝓝 x).ker
  证明: by
  ext; simp [ker_nhds_eq_specializes, ← specializes_iff_mem_closure, specializes_comm]

Depends on / 依赖: ker_nhds_eq_specializes, specializes_comm, specializes_iff_mem_closure
-/
lemma R0Space.closure_singleton (x : X) : closure {x} = (𝓝 x).ker := by
  ext; simp [ker_nhds_eq_specializes, ← specializes_iff_mem_closure, specializes_comm]

/--
theorem `isCompact_closure_singleton` / 定理 `isCompact_closure_singleton`

English:
theorem isCompact_closure_singleton
  statement: IsCompact (closure {x})
  proof: by
  refine isCompact_of_finite_subcover fun U hUo hxU => ?_
obtain ⟨i, hi⟩ : exists i, x in U i := mem_iUnion.1 hxU subset_closure rfl
  refine ⟨{i}, fun y hy => ?_⟩
  rw [← specializes_iff_mem_closure]; rw [specializes_comm] at hy
  simpa using hy.mem_open (hUo i) hi

中文:
定理 isCompact_closure_singleton
  结论: IsCompact (closure {x})
  证明: by
  refine isCompact_of_finite_subcover fun U hUo hxU => ?_
obtain ⟨i, hi⟩ : exists i, x in U i := mem_iUnion.1 hxU subset_closure rfl
  refine ⟨{i}, fun y hy => ?_⟩
  rw [← specializes_iff_mem_closure]; rw [specializes_comm] at hy
  simpa using hy.mem_open (hUo i) hi

Depends on / 依赖: hy.mem_open, isCompact_of_finite_subcover, mem_iUnion, mem_open, specializes_comm, specializes_iff_mem_closure, subset_closure
-/
theorem isCompact_closure_singleton : IsCompact (closure {x}) := by
  refine isCompact_of_finite_subcover fun U hUo hxU => ?_
obtain ⟨i, hi⟩ : exists i, x in U i := mem_iUnion.1 hxU subset_closure rfl
  refine ⟨{i}, fun y hy => ?_⟩
  rw [← specializes_iff_mem_closure]; rw [specializes_comm] at hy
  simpa using hy.mem_open (hUo i) hi

/--
theorem `Filter.coclosedCompact_le_cofinite` / 定理 `Filter.coclosedCompact_le_cofinite`

English:
theorem Filter.coclosedCompact_le_cofinite
  statement: coclosedCompact X <= cofinite
  proof: le_cofinite_iff_compl_singleton_mem.2 fun _ =>
    compl_mem_coclosedCompact.2 isCompact_closure_singleton

中文:
定理 Filter.coclosedCompact_le_cofinite
  结论: coclosedCompact X <= cofinite
  证明: le_cofinite_iff_compl_singleton_mem.2 fun _ =>
    compl_mem_coclosedCompact.2 isCompact_closure_singleton

Depends on / 依赖: compl_mem_coclosedCompact, isCompact_closure_singleton, le_cofinite_iff_compl_singleton_mem
-/
theorem Filter.coclosedCompact_le_cofinite : coclosedCompact X <= cofinite :=
  le_cofinite_iff_compl_singleton_mem.2 fun _ =>
    compl_mem_coclosedCompact.2 isCompact_closure_singleton

variable (X) in
/-- In an R₀ space, relatively compact sets form a bornology.
Its cobounded filter is `Filter.coclosedCompact`.
See also `Bornology.inCompact` the bornology of sets contained in a compact set. -/
@[instance_reducible]
/--
Definition of `Bornology.relativelyCompact` / `Bornology.relativelyCompact` 的定义

English:
definition Bornology.relativelyCompact
  signature: : Bornology X where
  body: Filter.coclosedCompact X
  le_cofinite := Filter.coclosedCompact_le_cofinite

中文:
定义 Bornology.relativelyCompact
  签名: : Bornology X where
  定义体: Filter.coclosedCompact X
  le_cofinite := Filter.coclosedCompact_le_cofinite

Depends on / 依赖: Filter, Filter.coclosedCompact, coclosedCompact
-/
def Bornology.relativelyCompact : Bornology X where
  cobounded := Filter.coclosedCompact X
  le_cofinite := Filter.coclosedCompact_le_cofinite

/--
theorem `Bornology.relativelyCompact.isBounded_iff` / 定理 `Bornology.relativelyCompact.isBounded_iff`

English:
theorem Bornology.relativelyCompact.isBounded_iff
  given: {s : Set X}
  proof: compl_mem_coclosedCompact

中文:
定理 Bornology.relativelyCompact.isBounded_iff
  条件: {s : Set X}
  证明: compl_mem_coclosedCompact

Depends on / 依赖: compl_mem_coclosedCompact
-/
theorem Bornology.relativelyCompact.isBounded_iff {s : Set X} :
    @Bornology.IsBounded _ (Bornology.relativelyCompact X) s ↔ IsCompact (closure s) :=
  compl_mem_coclosedCompact

/--
theorem `Set.Finite.isCompact_closure` / 定理 `Set.Finite.isCompact_closure`

English:
theorem Set.Finite.isCompact_closure
  given: {s : Set X} (hs : s.Finite)
  statement: IsCompact (closure s)
  proof: let _ : Bornology X := .relativelyCompact X
  Bornology.relativelyCompact.isBounded_iff.1 hs.isBounded

中文:
定理 Set.Finite.isCompact_closure
  条件: {s : Set X} (hs : s.Finite)
  结论: IsCompact (closure s)
  证明: let _ : Bornology X := .relativelyCompact X
  Bornology.relativelyCompact.isBounded_iff.1 hs.isBounded

Depends on / 依赖: Bornology, Bornology.relativelyCompact.isBounded_iff, hs.isBounded, isBounded, isBounded_iff, relativelyCompact
-/
theorem Set.Finite.isCompact_closure {s : Set X} (hs : s.Finite) : IsCompact (closure s) :=
  let _ : Bornology X := .relativelyCompact X
  Bornology.relativelyCompact.isBounded_iff.1 hs.isBounded

end R0Space

/--
Definition of `T1Space` / `T1Space` 的定义

English:
class T1Space
  parameters: (X : Type u) [TopologicalSpace X]
  axioms and operations (1):
    - t1 : forall x, IsClosed ({x} : Set X)

中文:
类 T1Space
  参数: (X : 类型u) [TopologicalSpace X]
  公理与运算 (1 个):
    - t1 : 对任意 x, IsClosed ({x} : Set X)
-/
class T1Space (X : Type u) [TopologicalSpace X] : Prop where
  /-- A singleton in a T₁ space is a closed set. -/
  t1 : forall x, IsClosed ({x} : Set X)

@[closedness .]
/--
theorem `isClosed_singleton` / 定理 `isClosed_singleton`

English:
theorem isClosed_singleton
  given: [T1Space X] {x : X}
  statement: IsClosed ({x} : Set X)
  proof: T1Space.t1 x

中文:
定理 isClosed_singleton
  条件: [T1Space X] {x : X}
  结论: IsClosed ({x} : Set X)
  证明: T1Space.t1 x

Depends on / 依赖: T1Space, T1Space.t1
-/
theorem isClosed_singleton [T1Space X] {x : X} : IsClosed ({x} : Set X) :=
  T1Space.t1 x

/--
theorem `isOpen_compl_singleton` / 定理 `isOpen_compl_singleton`

English:
theorem isOpen_compl_singleton
  given: [T1Space X] {x : X}
  statement: IsOpen ({x}ᶜ : Set X)
  proof: isClosed_singleton.isOpen_compl

中文:
定理 isOpen_compl_singleton
  条件: [T1Space X] {x : X}
  结论: IsOpen ({x}ᶜ : Set X)
  证明: isClosed_singleton.isOpen_compl

Depends on / 依赖: isClosed_singleton, isClosed_singleton.isOpen_compl, isOpen_compl
-/
theorem isOpen_compl_singleton [T1Space X] {x : X} : IsOpen ({x}ᶜ : Set X) :=
  isClosed_singleton.isOpen_compl

/--
theorem `isOpen_ne` / 定理 `isOpen_ne`

English:
theorem isOpen_ne
  given: [T1Space X] {x : X}
  statement: IsOpen { y | y != x }
  proof: isOpen_compl_singleton

@[to_additive]

中文:
定理 isOpen_ne
  条件: [T1Space X] {x : X}
  结论: IsOpen { y | y != x }
  证明: isOpen_compl_singleton

@[to_additive]

Depends on / 依赖: isOpen_compl_singleton
-/
theorem isOpen_ne [T1Space X] {x : X} : IsOpen { y | y != x } :=
  isOpen_compl_singleton

@[to_additive]
/--
theorem `Continuous.isOpen_mulSupport` / 定理 `Continuous.isOpen_mulSupport`

English:
theorem Continuous.isOpen_mulSupport
  statement: [T1Space X] [One X] [TopologicalSpace Y] {f : Y -> X}
  proof: isOpen_ne.preimage hf

中文:
定理 Continuous.isOpen_mulSupport
  结论: [T1Space X] [One X] [TopologicalSpace Y] {f : Y -> X}
  证明: isOpen_ne.preimage hf

Depends on / 依赖: isOpen_ne, isOpen_ne.preimage, preimage
-/
theorem Continuous.isOpen_mulSupport [T1Space X] [One X] [TopologicalSpace Y] {f : Y -> X}
    (hf : Continuous f) : IsOpen (mulSupport f) :=
  isOpen_ne.preimage hf

/--
theorem `Ne.nhdsWithin_compl_singleton` / 定理 `Ne.nhdsWithin_compl_singleton`

English:
theorem Ne.nhdsWithin_compl_singleton
  given: [T1Space X] {x y : X} (h : x != y)
  statement: 𝓝[{y}ᶜ] x = 𝓝 x
  proof: isOpen_ne.nhdsWithin_eq h

中文:
定理 Ne.nhdsWithin_compl_singleton
  条件: [T1Space X] {x y : X} (h : x != y)
  结论: 𝓝[{y}ᶜ] x = 𝓝 x
  证明: isOpen_ne.nhdsWithin_eq h

Depends on / 依赖: isOpen_ne, isOpen_ne.nhdsWithin_eq, nhdsWithin_eq
-/
theorem Ne.nhdsWithin_compl_singleton [T1Space X] {x y : X} (h : x != y) : 𝓝[{y}ᶜ] x = 𝓝 x :=
  isOpen_ne.nhdsWithin_eq h

/--
theorem `Ne.nhdsWithin_sdiff_singleton` / 定理 `Ne.nhdsWithin_sdiff_singleton`

English:
theorem Ne.nhdsWithin_sdiff_singleton
  given: [T1Space X] {x y : X} (h : x != y) (s : Set X)
  proof: by
  rw [sdiff_eq]; rw [inter_comm]; rw [nhdsWithin_inter_of_mem]
  exact mem_nhdsWithin_of_mem_nhds (isOpen_ne.mem_nhds h)

@[deprecated (since := "2026-06-03")]
alias Ne.nhdsWithin_diff_singleton := Ne.nhdsWithin_sdiff_singleton

中文:
定理 Ne.nhdsWithin_sdiff_singleton
  条件: [T1Space X] {x y : X} (h : x != y) (s : Set X)
  证明: by
  rw [sdiff_eq]; rw [inter_comm]; rw [nhdsWithin_inter_of_mem]
  exact mem_nhdsWithin_of_mem_nhds (isOpen_ne.mem_nhds h)

@[deprecated (since := "2026-06-03")]
alias Ne.nhdsWithin_diff_singleton := Ne.nhdsWithin_sdiff_singleton

Depends on / 依赖: inter_comm, isOpen_ne, isOpen_ne.mem_nhds, mem_nhds, mem_nhdsWithin_of_mem_nhds, nhdsWithin_inter_of_mem, sdiff_eq
-/
theorem Ne.nhdsWithin_sdiff_singleton [T1Space X] {x y : X} (h : x != y) (s : Set X) :
    𝓝[s \ {y}] x = 𝓝[s] x := by
  rw [sdiff_eq]; rw [inter_comm]; rw [nhdsWithin_inter_of_mem]
  exact mem_nhdsWithin_of_mem_nhds (isOpen_ne.mem_nhds h)

@[deprecated (since := "2026-06-03")]
alias Ne.nhdsWithin_diff_singleton := Ne.nhdsWithin_sdiff_singleton

/--
lemma `nhdsWithin_compl_singleton_le` / 引理 `nhdsWithin_compl_singleton_le`

English:
lemma nhdsWithin_compl_singleton_le
  given: [T1Space X] (x y : X)
  statement: 𝓝[{x}ᶜ] x <= 𝓝[{y}ᶜ] x
  proof: by
  rcases eq_or_ne x y with rfl | hy
  · exact Eq.le rfl
  · rw [Ne.nhdsWithin_compl_singleton hy]
    exact nhdsWithin_le_nhds

中文:
引理 nhdsWithin_compl_singleton_le
  条件: [T1Space X] (x y : X)
  结论: 𝓝[{x}ᶜ] x <= 𝓝[{y}ᶜ] x
  证明: by
  rcases eq_or_ne x y with rfl | hy
  · exact Eq.le rfl
  · rw [Ne.nhdsWithin_compl_singleton hy]
    exact nhdsWithin_le_nhds

Depends on / 依赖: Eq.le, Ne.nhdsWithin_compl_singleton, eq_or_ne, nhdsWithin_compl_singleton, nhdsWithin_le_nhds
-/
lemma nhdsWithin_compl_singleton_le [T1Space X] (x y : X) : 𝓝[{x}ᶜ] x <= 𝓝[{y}ᶜ] x := by
  rcases eq_or_ne x y with rfl | hy
  · exact Eq.le rfl
  · rw [Ne.nhdsWithin_compl_singleton hy]
    exact nhdsWithin_le_nhds

/--
theorem `isOpen_setOfPred_eventually_nhdsWithin` / 定理 `isOpen_setOfPred_eventually_nhdsWithin`

English:
theorem isOpen_setOfPred_eventually_nhdsWithin
  given: [T1Space X] {p : X -> Prop}
  proof: by
  refine isOpen_iff_mem_nhds.mpr fun a ha => ?_
  filter_upwards [eventually_nhds_nhdsWithin.mpr ha] with b hb
  rcases eq_or_ne a b with rfl | h
  · exact hb
  · rw [h.symm.nhdsWithin_compl_singleton] at hb
    exact hb.filter_mono nhdsWithin_le_nhds

@[deprecated (since := "2026-07-09")]
alias 

中文:
定理 isOpen_setOfPred_eventually_nhdsWithin
  条件: [T1Space X] {p : X -> 命题}
  证明: by
  refine isOpen_iff_mem_nhds.mpr fun a ha => ?_
  filter_upwards [eventually_nhds_nhdsWithin.mpr ha] with b hb
  rcases eq_or_ne a b with rfl | h
  · exact hb
  · rw [h.symm.nhdsWithin_compl_singleton] at hb
    exact hb.filter_mono nhdsWithin_le_nhds

@[deprecated (since := "2026-07-09")]
alias 

Depends on / 依赖: eq_or_ne, eventually_nhds_nhdsWithin, eventually_nhds_nhdsWithin.mpr, filter_mono, filter_upwards, h.symm.nhdsWithin_compl_singleton, hb.filter_mono, isOpen_iff_mem_nhds, isOpen_iff_mem_nhds.mpr, nhdsWithin_compl_singleton, nhdsWithin_le_nhds
-/
theorem isOpen_setOfPred_eventually_nhdsWithin [T1Space X] {p : X -> Prop} :
    IsOpen { x | forallᶠ y in 𝓝[!=] x, p y } := by
  refine isOpen_iff_mem_nhds.mpr fun a ha => ?_
  filter_upwards [eventually_nhds_nhdsWithin.mpr ha] with b hb
  rcases eq_or_ne a b with rfl | h
  · exact hb
  · rw [h.symm.nhdsWithin_compl_singleton] at hb
    exact hb.filter_mono nhdsWithin_le_nhds

@[deprecated (since := "2026-07-09")]
alias isOpen_setOf_eventually_nhdsWithin := isOpen_setOfPred_eventually_nhdsWithin

/--
lemma `Set.Finite.isClosed` / 引理 `Set.Finite.isClosed`

English:
lemma Set.Finite.isClosed
  given: [T1Space X] {s : Set X} (hs : s.Finite)
  proof: by
  rw [← biUnion_of_singleton s]
  exact hs.isClosed_biUnion fun i _ => isClosed_singleton

中文:
引理 Set.Finite.isClosed
  条件: [T1Space X] {s : Set X} (hs : s.Finite)
  证明: by
  rw [← biUnion_of_singleton s]
  exact hs.isClosed_biUnion fun i _ => isClosed_singleton
-/
@[simp] protected lemma Set.Finite.isClosed [T1Space X] {s : Set X} (hs : s.Finite) :
    IsClosed s := by
  rw [← biUnion_of_singleton s]
  exact hs.isClosed_biUnion fun i _ => isClosed_singleton

/--
theorem `TopologicalSpace.IsTopologicalBasis.exists_mem_of_ne` / 定理 `TopologicalSpace.IsTopologicalBasis.exists_mem_of_ne`

English:
theorem TopologicalSpace.IsTopologicalBasis.exists_mem_of_ne
  statement: [T1Space X] {b : Set (Set X)}
  proof: by
  rcases hb.isOpen_iff.1 isOpen_ne x h with ⟨a, ab, xa, ha⟩
  exact ⟨a, ab, xa, fun h => ha h rfl⟩

中文:
定理 TopologicalSpace.IsTopologicalBasis.exists_mem_of_ne
  结论: [T1Space X] {b : Set (Set X)}
  证明: by
  rcases hb.isOpen_iff.1 isOpen_ne x h with ⟨a, ab, xa, ha⟩
  exact ⟨a, ab, xa, fun h => ha h rfl⟩

Depends on / 依赖: hb.isOpen_iff, isOpen_iff, isOpen_ne
-/
theorem TopologicalSpace.IsTopologicalBasis.exists_mem_of_ne [T1Space X] {b : Set (Set X)}
    (hb : IsTopologicalBasis b) {x y : X} (h : x != y) : exists a in b, x in a ∧ y ∉ a := by
  rcases hb.isOpen_iff.1 isOpen_ne x h with ⟨a, ab, xa, ha⟩
  exact ⟨a, ab, xa, fun h => ha h rfl⟩

/--
theorem `Finset.isClosed` / 定理 `Finset.isClosed`

English:
theorem Finset.isClosed
  given: [T1Space X] (s : Finset X)
  statement: IsClosed (s : Set X)
  proof: s.finite_toSet.isClosed

中文:
定理 Finset.isClosed
  条件: [T1Space X] (s : Finset X)
  结论: IsClosed (s : Set X)
  证明: s.finite_toSet.isClosed
-/
protected theorem Finset.isClosed [T1Space X] (s : Finset X) : IsClosed (s : Set X) :=
  s.finite_toSet.isClosed

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: T1Space (CofiniteTopology X)
  body: CofiniteTopology.isClosed_iff.mpr by simp

中文:
实例 :
  签名: T1Space (CofiniteTopology X)
  定义体: CofiniteTopology.isClosed_iff.mpr by simp
-/
instance : T1Space (CofiniteTopology X) where
t1 x := CofiniteTopology.isClosed_iff.mpr by simp

/--
theorem `t1Space_TFAE` / 定理 `t1Space_TFAE`

English:
theorem t1Space_TFAE
  given: (X : Type u) [TopologicalSpace X]
  proof: by
  tfae_have 1 ↔ 2 := ⟨fun h => h.1, fun h => ⟨h⟩⟩
  tfae_have 2 ↔ 3 := by
    simp only [isOpen_compl_iff]
  tfae_have 5 ↔ 3 := by
    refine forall_comm.trans ?_
    simp only [isOpen_iff_mem_nhds, mem_compl_iff, mem_singleton_iff]
  tfae_have 5 ↔ 6 := by
    simp only [← subset_compl_singleton_

中文:
定理 t1Space_TFAE
  条件: (X : 类型u) [TopologicalSpace X]
  证明: by
  tfae_have 1 ↔ 2 := ⟨fun h => h.1, fun h => ⟨h⟩⟩
  tfae_have 2 ↔ 3 := by
    simp only [isOpen_compl_iff]
  tfae_have 5 ↔ 3 := by
    refine forall_comm.trans ?_
    simp only [isOpen_iff_mem_nhds, mem_compl_iff, mem_singleton_iff]
  tfae_have 5 ↔ 6 := by
    simp only [← subset_compl_singleton_

Depends on / 依赖: and_assoc, and_left_comm, disjoint_principal_righ, exists_mem_subset_iff, forall_comm, forall_comm.trans, isOpen_compl_iff, isOpen_iff_mem_nhds, mem_compl_iff, mem_iff, mem_singleton_iff, nhds_basis_opens, principal_singleton, subset_compl_singleton_iff, tfae_have
-/
theorem t1Space_TFAE (X : Type u) [TopologicalSpace X] :
    List.TFAE [T1Space X,
      forall x, IsClosed ({ x } : Set X),
      forall x, IsOpen ({ x }ᶜ : Set X),
      Continuous (@CofiniteTopology.of X),
      forall ⦃x y : X⦄, x != y -> {y}ᶜ in 𝓝 x,
      forall ⦃x y : X⦄, x != y -> exists s in 𝓝 x, y ∉ s,
      forall ⦃x y : X⦄, x != y -> exists U : Set X, IsOpen U ∧ x in U ∧ y ∉ U,
      forall ⦃x y : X⦄, x != y -> Disjoint (𝓝 x) (pure y),
      forall ⦃x y : X⦄, x != y -> Disjoint (pure x) (𝓝 y),
      forall ⦃x y : X⦄, x ⤳ y -> x = y,
      T0Space X ∧ R0Space X] := by
  tfae_have 1 ↔ 2 := ⟨fun h => h.1, fun h => ⟨h⟩⟩
  tfae_have 2 ↔ 3 := by
    simp only [isOpen_compl_iff]
  tfae_have 5 ↔ 3 := by
    refine forall_comm.trans ?_
    simp only [isOpen_iff_mem_nhds, mem_compl_iff, mem_singleton_iff]
  tfae_have 5 ↔ 6 := by
    simp only [← subset_compl_singleton_iff, exists_mem_subset_iff]
  tfae_have 5 ↔ 7 := by
    simp only [(nhds_basis_opens _).mem_iff, subset_compl_singleton_iff, and_assoc,
      and_left_comm]
  tfae_have 5 ↔ 8 := by
    simp only [← principal_singleton, disjoint_principal_right]
  tfae_have 8 ↔ 9 := forall_comm.trans (by simp only [disjoint_comm, ne_comm])
  tfae_have 1 -> 4 := by
    simp only [continuous_def, CofiniteTopology.isOpen_iff']
    rintro H s (rfl | hs)
    · exact isOpen_empty
    · rw [← compl_compl s, preimage_compl]
.isClosed.isOpen_compl exact hs.preimage (Equiv.injective _).injOn
  tfae_have 4 -> 2 := by
    intro h x
    rw [← CofiniteTopology.of.preimage_image {x}]
.preimage h exact (Set.Finite.isClosed <| by simp)
  tfae_have 2 ↔ 10 := by
    simp only [← closure_subset_iff_isClosed, specializes_iff_mem_closure, subset_def,
      mem_singleton_iff, eq_comm]
  tfae_have 10 ↔ 11 :=
    ⟨fun h => ⟨⟨fun _ _ h₂ => h h₂.specializes⟩, ⟨⟨fun _ _ h₂ => specializes_of_eq (h h₂).symm⟩⟩⟩,
      fun ⟨_, _⟩ _ _ h => (h.antisymm h.symm).eq⟩
  tfae_finish

/--
theorem `t1Space_iff_continuous_cofinite_of` / 定理 `t1Space_iff_continuous_cofinite_of`

English:
theorem t1Space_iff_continuous_cofinite_of
  statement: T1Space X ↔ Continuous (@CofiniteTopology.of X)
  proof: (t1Space_TFAE X).out 0 3

中文:
定理 t1Space_iff_continuous_cofinite_of
  结论: T1Space X ↔ Continuous (@CofiniteTopology.of X)
  证明: (t1Space_TFAE X).out 0 3

Depends on / 依赖: t1Space_TFAE
-/
theorem t1Space_iff_continuous_cofinite_of : T1Space X ↔ Continuous (@CofiniteTopology.of X) :=
  (t1Space_TFAE X).out 0 3

/--
theorem `CofiniteTopology.continuous_of` / 定理 `CofiniteTopology.continuous_of`

English:
theorem CofiniteTopology.continuous_of
  given: [T1Space X]
  statement: Continuous (@CofiniteTopology.of X)
  proof: t1Space_iff_continuous_cofinite_of.mp ‹_›

中文:
定理 CofiniteTopology.continuous_of
  条件: [T1Space X]
  结论: Continuous (@CofiniteTopology.of X)
  证明: t1Space_iff_continuous_cofinite_of.mp ‹_›

Depends on / 依赖: t1Space_iff_continuous_cofinite_of, t1Space_iff_continuous_cofinite_of.mp
-/
theorem CofiniteTopology.continuous_of [T1Space X] : Continuous (@CofiniteTopology.of X) :=
  t1Space_iff_continuous_cofinite_of.mp ‹_›

/--
theorem `t1Space_iff_exists_open` / 定理 `t1Space_iff_exists_open`

English:
theorem t1Space_iff_exists_open
  proof: (t1Space_TFAE X).out 0 6

中文:
定理 t1Space_iff_exists_open
  证明: (t1Space_TFAE X).out 0 6

Depends on / 依赖: t1Space_TFAE
-/
theorem t1Space_iff_exists_open :
    T1Space X ↔ Pairwise fun x y => exists U : Set X, IsOpen U ∧ x in U ∧ y ∉ U :=
  (t1Space_TFAE X).out 0 6

/--
theorem `t1Space_iff_disjoint_pure_nhds` / 定理 `t1Space_iff_disjoint_pure_nhds`

English:
theorem t1Space_iff_disjoint_pure_nhds
  statement: T1Space X ↔ forall ⦃x y : X⦄, x != y -> Disjoint (pure x) (𝓝 y)
  proof: (t1Space_TFAE X).out 0 8

中文:
定理 t1Space_iff_disjoint_pure_nhds
  结论: T1Space X ↔ 对任意 ⦃x y : X⦄, x != y -> Disjoint (pure x) (𝓝 y)
  证明: (t1Space_TFAE X).out 0 8

Depends on / 依赖: t1Space_TFAE
-/
theorem t1Space_iff_disjoint_pure_nhds : T1Space X ↔ forall ⦃x y : X⦄, x != y -> Disjoint (pure x) (𝓝 y) :=
  (t1Space_TFAE X).out 0 8

/--
theorem `t1Space_iff_disjoint_nhds_pure` / 定理 `t1Space_iff_disjoint_nhds_pure`

English:
theorem t1Space_iff_disjoint_nhds_pure
  statement: T1Space X ↔ forall ⦃x y : X⦄, x != y -> Disjoint (𝓝 x) (pure y)
  proof: (t1Space_TFAE X).out 0 7

中文:
定理 t1Space_iff_disjoint_nhds_pure
  结论: T1Space X ↔ 对任意 ⦃x y : X⦄, x != y -> Disjoint (𝓝 x) (pure y)
  证明: (t1Space_TFAE X).out 0 7

Depends on / 依赖: t1Space_TFAE
-/
theorem t1Space_iff_disjoint_nhds_pure : T1Space X ↔ forall ⦃x y : X⦄, x != y -> Disjoint (𝓝 x) (pure y) :=
  (t1Space_TFAE X).out 0 7

/--
theorem `t1Space_iff_specializes_imp_eq` / 定理 `t1Space_iff_specializes_imp_eq`

English:
theorem t1Space_iff_specializes_imp_eq
  statement: T1Space X ↔ forall ⦃x y : X⦄, x ⤳ y -> x = y
  proof: (t1Space_TFAE X).out 0 9

中文:
定理 t1Space_iff_specializes_imp_eq
  结论: T1Space X ↔ 对任意 ⦃x y : X⦄, x ⤳ y -> x = y
  证明: (t1Space_TFAE X).out 0 9

Depends on / 依赖: t1Space_TFAE
-/
theorem t1Space_iff_specializes_imp_eq : T1Space X ↔ forall ⦃x y : X⦄, x ⤳ y -> x = y :=
  (t1Space_TFAE X).out 0 9

/--
theorem `t1Space_iff_t0Space_and_r0Space` / 定理 `t1Space_iff_t0Space_and_r0Space`

English:
theorem t1Space_iff_t0Space_and_r0Space
  statement: T1Space X ↔ T0Space X ∧ R0Space X
  proof: (t1Space_TFAE X).out 0 10

中文:
定理 t1Space_iff_t0Space_and_r0Space
  结论: T1Space X ↔ T0Space X ∧ R0Space X
  证明: (t1Space_TFAE X).out 0 10

Depends on / 依赖: t1Space_TFAE
-/
theorem t1Space_iff_t0Space_and_r0Space : T1Space X ↔ T0Space X ∧ R0Space X :=
  (t1Space_TFAE X).out 0 10

/--
theorem `disjoint_pure_nhds` / 定理 `disjoint_pure_nhds`

English:
theorem disjoint_pure_nhds
  given: [T1Space X] {x y : X} (h : x != y)
  statement: Disjoint (pure x) (𝓝 y)
  proof: t1Space_iff_disjoint_pure_nhds.mp ‹_› h

中文:
定理 disjoint_pure_nhds
  条件: [T1Space X] {x y : X} (h : x != y)
  结论: Disjoint (pure x) (𝓝 y)
  证明: t1Space_iff_disjoint_pure_nhds.mp ‹_› h

Depends on / 依赖: t1Space_iff_disjoint_pure_nhds, t1Space_iff_disjoint_pure_nhds.mp
-/
theorem disjoint_pure_nhds [T1Space X] {x y : X} (h : x != y) : Disjoint (pure x) (𝓝 y) :=
  t1Space_iff_disjoint_pure_nhds.mp ‹_› h

/--
theorem `disjoint_nhds_pure` / 定理 `disjoint_nhds_pure`

English:
theorem disjoint_nhds_pure
  given: [T1Space X] {x y : X} (h : x != y)
  statement: Disjoint (𝓝 x) (pure y)
  proof: t1Space_iff_disjoint_nhds_pure.mp ‹_› h

中文:
定理 disjoint_nhds_pure
  条件: [T1Space X] {x y : X} (h : x != y)
  结论: Disjoint (𝓝 x) (pure y)
  证明: t1Space_iff_disjoint_nhds_pure.mp ‹_› h

Depends on / 依赖: t1Space_iff_disjoint_nhds_pure, t1Space_iff_disjoint_nhds_pure.mp
-/
theorem disjoint_nhds_pure [T1Space X] {x y : X} (h : x != y) : Disjoint (𝓝 x) (pure y) :=
  t1Space_iff_disjoint_nhds_pure.mp ‹_› h

/--
theorem `Specializes.eq` / 定理 `Specializes.eq`

English:
theorem Specializes.eq
  given: [T1Space X] {x y : X} (h : x ⤳ y)
  statement: x = y
  proof: t1Space_iff_specializes_imp_eq.1 ‹_› h

中文:
定理 Specializes.eq
  条件: [T1Space X] {x y : X} (h : x ⤳ y)
  结论: x = y
  证明: t1Space_iff_specializes_imp_eq.1 ‹_› h

Depends on / 依赖: t1Space_iff_specializes_imp_eq
-/
theorem Specializes.eq [T1Space X] {x y : X} (h : x ⤳ y) : x = y :=
  t1Space_iff_specializes_imp_eq.1 ‹_› h

/--
theorem `specializes_iff_eq` / 定理 `specializes_iff_eq`

English:
theorem specializes_iff_eq
  given: [T1Space X] {x y : X}
  statement: x ⤳ y ↔ x = y
  proof: ⟨Specializes.eq, fun h => h ▸ specializes_rfl⟩

中文:
定理 specializes_iff_eq
  条件: [T1Space X] {x y : X}
  结论: x ⤳ y ↔ x = y
  证明: ⟨Specializes.eq, fun h => h ▸ specializes_rfl⟩

Depends on / 依赖: Specializes, Specializes.eq, specializes_rfl
-/
theorem specializes_iff_eq [T1Space X] {x y : X} : x ⤳ y ↔ x = y :=
  ⟨Specializes.eq, fun h => h ▸ specializes_rfl⟩

/--
theorem `specializes_eq_eq` / 定理 `specializes_eq_eq`

English:
theorem specializes_eq_eq
  given: [T1Space X]
  statement: (· ⤳ ·) = @Eq X
  proof: funext₂ fun _ _ => propext specializes_iff_eq

@[simp]

中文:
定理 specializes_eq_eq
  条件: [T1Space X]
  结论: (· ⤳ ·) = @Eq X
  证明: funext₂ fun _ _ => propext specializes_iff_eq

@[simp]
-/
@[simp] theorem specializes_eq_eq [T1Space X] : (· ⤳ ·) = @Eq X :=
  funext₂ fun _ _ => propext specializes_iff_eq

@[simp]
/--
theorem `pure_le_nhds_iff` / 定理 `pure_le_nhds_iff`

English:
theorem pure_le_nhds_iff
  given: [T1Space X] {a b : X}
  statement: pure a <= 𝓝 b ↔ a = b
  proof: specializes_iff_pure.symm.trans specializes_iff_eq

@[simp]

中文:
定理 pure_le_nhds_iff
  条件: [T1Space X] {a b : X}
  结论: pure a <= 𝓝 b ↔ a = b
  证明: specializes_iff_pure.symm.trans specializes_iff_eq

@[simp]

Depends on / 依赖: specializes_iff_eq, specializes_iff_pure, specializes_iff_pure.symm.trans
-/
theorem pure_le_nhds_iff [T1Space X] {a b : X} : pure a <= 𝓝 b ↔ a = b :=
  specializes_iff_pure.symm.trans specializes_iff_eq

@[simp]
/--
theorem `nhds_le_nhds_iff` / 定理 `nhds_le_nhds_iff`

English:
theorem nhds_le_nhds_iff
  given: [T1Space X] {a b : X}
  statement: 𝓝 a <= 𝓝 b ↔ a = b
  proof: specializes_iff_eq

中文:
定理 nhds_le_nhds_iff
  条件: [T1Space X] {a b : X}
  结论: 𝓝 a <= 𝓝 b ↔ a = b
  证明: specializes_iff_eq

Depends on / 依赖: specializes_iff_eq
-/
theorem nhds_le_nhds_iff [T1Space X] {a b : X} : 𝓝 a <= 𝓝 b ↔ a = b :=
  specializes_iff_eq

instance (priority := 100) [T1Space X] : R0Space X :=
  (t1Space_iff_t0Space_and_r0Space.mp ‹T1Space X›).right

instance (priority := 80) [T0Space X] [R0Space X] : T1Space X :=
  t1Space_iff_t0Space_and_r0Space.mpr ⟨‹T0Space X›, ‹R0Space X›⟩

/--
theorem `t1Space_antitone` / 定理 `t1Space_antitone`

English:
theorem t1Space_antitone
  given: {X}
  statement: Antitone (@T1Space X)
  proof: fun a _ h _ =>
  @T1Space.mk _ a fun x => (T1Space.t1 x).mono h

中文:
定理 t1Space_antitone
  条件: {X}
  结论: Antitone (@T1Space X)
  证明: fun a _ h _ =>
  @T1Space.mk _ a fun x => (T1Space.t1 x).mono h
-/
theorem t1Space_antitone {X} : Antitone (@T1Space X) := fun a _ h _ =>
  @T1Space.mk _ a fun x => (T1Space.t1 x).mono h

/--
theorem `continuousWithinAt_update_of_ne` / 定理 `continuousWithinAt_update_of_ne`

English:
theorem continuousWithinAt_update_of_ne
  statement: [T1Space X] [DecidableEq X] [TopologicalSpace Y] {f : X -> Y}
  proof: EventuallyEq.congr_continuousWithinAt
    (mem_nhdsWithin_of_mem_nhds <| mem_of_superset (isOpen_ne.mem_nhds hne) fun _y' hy' =>
      Function.update_of_ne hy' _ _)
    (Function.update_of_ne hne ..)

中文:
定理 continuousWithinAt_update_of_ne
  结论: [T1Space X] [DecidableEq X] [TopologicalSpace Y] {f : X -> Y}
  证明: EventuallyEq.congr_continuousWithinAt
    (mem_nhdsWithin_of_mem_nhds <| mem_of_superset (isOpen_ne.mem_nhds hne) fun _y' hy' =>
      Function.update_of_ne hy' _ _)
    (Function.update_of_ne hne ..)

Depends on / 依赖: EventuallyEq, EventuallyEq.congr_continuousWithinAt, Function, Function.update_of_ne, congr_continuousWithinAt, isOpen_ne, isOpen_ne.mem_nhds, mem_nhds, mem_nhdsWithin_of_mem_nhds, mem_of_superset, update_of_ne
-/
theorem continuousWithinAt_update_of_ne [T1Space X] [DecidableEq X] [TopologicalSpace Y] {f : X -> Y}
    {s : Set X} {x x' : X} {y : Y} (hne : x' != x) :
    ContinuousWithinAt (Function.update f x y) s x' ↔ ContinuousWithinAt f s x' :=
  EventuallyEq.congr_continuousWithinAt
    (mem_nhdsWithin_of_mem_nhds <| mem_of_superset (isOpen_ne.mem_nhds hne) fun _y' hy' =>
      Function.update_of_ne hy' _ _)
    (Function.update_of_ne hne ..)

/--
theorem `continuousAt_update_of_ne` / 定理 `continuousAt_update_of_ne`

English:
theorem continuousAt_update_of_ne
  statement: [T1Space X] [DecidableEq X] [TopologicalSpace Y]
  proof: by
  simp only [← continuousWithinAt_univ, continuousWithinAt_update_of_ne hne]

中文:
定理 continuousAt_update_of_ne
  结论: [T1Space X] [DecidableEq X] [TopologicalSpace Y]
  证明: by
  simp only [← continuousWithinAt_univ, continuousWithinAt_update_of_ne hne]

Depends on / 依赖: continuousWithinAt_univ, continuousWithinAt_update_of_ne
-/
theorem continuousAt_update_of_ne [T1Space X] [DecidableEq X] [TopologicalSpace Y]
    {f : X -> Y} {x x' : X} {y : Y} (hne : x' != x) :
    ContinuousAt (Function.update f x y) x' ↔ ContinuousAt f x' := by
  simp only [← continuousWithinAt_univ, continuousWithinAt_update_of_ne hne]

/--
theorem `continuousOn_update_iff` / 定理 `continuousOn_update_iff`

English:
theorem continuousOn_update_iff
  statement: [T1Space X] [DecidableEq X] [TopologicalSpace Y] {f : X -> Y}
  proof: by
  rw [ContinuousOn]; rw [← and_forall_ne x]; rw [and_comm]
  refine and_congr ⟨fun H z hz => ?_, fun H z hzx hzs => ?_⟩ (forall_congr' fun _ => ?_)
  · specialize H z hz.2 hz.1
    rw [continuousWithinAt_update_of_ne hz.2] at H
    exact H.mono sdiff_subset
  · rw [continuousWithinAt_update_of_ne

中文:
定理 continuousOn_update_iff
  结论: [T1Space X] [DecidableEq X] [TopologicalSpace Y] {f : X -> Y}
  证明: by
  rw [ContinuousOn]; rw [← and_forall_ne x]; rw [and_comm]
  refine and_congr ⟨fun H z hz => ?_, fun H z hzx hzs => ?_⟩ (forall_congr' fun _ => ?_)
  · specialize H z hz.2 hz.1
    rw [continuousWithinAt_update_of_ne hz.2] at H
    exact H.mono sdiff_subset
  · rw [continuousWithinAt_update_of_ne

Depends on / 依赖: ContinuousOn, H.mono, and_comm, and_congr, and_forall_ne, continuousWithinAt_update_of_ne, continuousWithinAt_update_same, forall_congr, inter_mem_nhdsWithin, isOpen_ne, isOpen_ne.mem_nhds, mem_nhds, mono_of_mem_nhdsWithin, sdiff_subset, specialize
-/
theorem continuousOn_update_iff [T1Space X] [DecidableEq X] [TopologicalSpace Y] {f : X -> Y}
    {s : Set X} {x : X} {y : Y} :
    ContinuousOn (Function.update f x y) s ↔
      ContinuousOn f (s \ {x}) ∧ (x in s -> Tendsto f (𝓝[s \ {x}] x) (𝓝 y)) := by
  rw [ContinuousOn]; rw [← and_forall_ne x]; rw [and_comm]
  refine and_congr ⟨fun H z hz => ?_, fun H z hzx hzs => ?_⟩ (forall_congr' fun _ => ?_)
  · specialize H z hz.2 hz.1
    rw [continuousWithinAt_update_of_ne hz.2] at H
    exact H.mono sdiff_subset
  · rw [continuousWithinAt_update_of_ne hzx]
    refine (H z ⟨hzs, hzx⟩).mono_of_mem_nhdsWithin (inter_mem_nhdsWithin _ ?_)
    exact isOpen_ne.mem_nhds hzx
  · exact continuousWithinAt_update_same

/--
theorem `t1Space_of_injective_of_continuous` / 定理 `t1Space_of_injective_of_continuous`

English:
theorem t1Space_of_injective_of_continuous
  statement: [TopologicalSpace Y] {f : X -> Y}
  proof: t1Space_iff_specializes_imp_eq.2 fun _ _ h => hf (h.map hf').eq

中文:
定理 t1Space_of_injective_of_continuous
  结论: [TopologicalSpace Y] {f : X -> Y}
  证明: t1Space_iff_specializes_imp_eq.2 fun _ _ h => hf (h.map hf').eq

Depends on / 依赖: h.map, t1Space_iff_specializes_imp_eq
-/
theorem t1Space_of_injective_of_continuous [TopologicalSpace Y] {f : X -> Y}
    (hf : Function.Injective f) (hf' : Continuous f) [T1Space Y] : T1Space X :=
  t1Space_iff_specializes_imp_eq.2 fun _ _ h => hf (h.map hf').eq

/--
theorem `Topology.IsEmbedding.t1Space` / 定理 `Topology.IsEmbedding.t1Space`

English:
theorem Topology.IsEmbedding.t1Space
  statement: [TopologicalSpace Y] [T1Space Y] {f : X -> Y}
  proof: t1Space_of_injective_of_continuous hf.injective hf.continuous

中文:
定理 Topology.IsEmbedding.t1Space
  结论: [TopologicalSpace Y] [T1Space Y] {f : X -> Y}
  证明: t1Space_of_injective_of_continuous hf.injective hf.continuous
-/
protected theorem Topology.IsEmbedding.t1Space [TopologicalSpace Y] [T1Space Y] {f : X -> Y}
    (hf : IsEmbedding f) : T1Space X :=
  t1Space_of_injective_of_continuous hf.injective hf.continuous

/--
theorem `Homeomorph.t1Space` / 定理 `Homeomorph.t1Space`

English:
theorem Homeomorph.t1Space
  given: [TopologicalSpace Y] [T1Space X] (h : X ≃ₜ Y)
  statement: T1Space Y
  proof: h.symm.isEmbedding.t1Space

中文:
定理 Homeomorph.t1Space
  条件: [TopologicalSpace Y] [T1Space X] (h : X ≃ₜ Y)
  结论: T1Space Y
  证明: h.symm.isEmbedding.t1Space
-/
protected theorem Homeomorph.t1Space [TopologicalSpace Y] [T1Space X] (h : X ≃ₜ Y) : T1Space Y :=
  h.symm.isEmbedding.t1Space

/--
Instance `Subtype.t1Space` / 实例 `Subtype.t1Space`

English:
instance Subtype.t1Space
  signature: {X : Type u} [TopologicalSpace X] [T1Space X] {p : X -> Prop}
  body: IsEmbedding.subtypeVal.t1Space

中文:
实例 Subtype.t1Space
  签名: {X : 类型u} [TopologicalSpace X] [T1Space X] {p : X -> 命题}
  定义体: IsEmbedding.subtypeVal.t1Space

Depends on / 依赖: IsEmbedding, IsEmbedding.subtypeVal.t1Space, subtypeVal, t1Space
-/
instance Subtype.t1Space {X : Type u} [TopologicalSpace X] [T1Space X] {p : X -> Prop} :
    T1Space (Subtype p) :=
  IsEmbedding.subtypeVal.t1Space

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [TopologicalSpace
  signature: Y] [T1Space X] [T1Space Y] : T1Space (X × Y)
  body: ⟨fun ⟨a, b⟩ => @singleton_prod_singleton _ _ a b ▸ isClosed_singleton.prod isClosed_singleton⟩

中文:
实例 [TopologicalSpace
  签名: Y] [T1Space X] [T1Space Y] : T1Space (X × Y)
  定义体: ⟨fun ⟨a, b⟩ => @singleton_prod_singleton _ _ a b ▸ isClosed_singleton.prod isClosed_singleton⟩

Depends on / 依赖: isClosed_singleton, isClosed_singleton.prod, singleton_prod_singleton
-/
instance [TopologicalSpace Y] [T1Space X] [T1Space Y] : T1Space (X × Y) :=
  ⟨fun ⟨a, b⟩ => @singleton_prod_singleton _ _ a b ▸ isClosed_singleton.prod isClosed_singleton⟩

instance {ι : Type*} {X : ι -> Type*} [forall i, TopologicalSpace (X i)] [forall i, T1Space (X i)] :
    T1Space (forall i, X i) :=
  ⟨fun f => univ_pi_singleton f ▸ isClosed_set_pi fun _ _ => isClosed_singleton⟩

/--
Instance `ULift.instT1Space` / 实例 `ULift.instT1Space`

English:
instance ULift.instT1Space
  signature: [T1Space X]
  body: IsEmbedding.uliftDown.t1Space

中文:
实例 ULift.instT1Space
  签名: [T1Space X]
  定义体: IsEmbedding.uliftDown.t1Space

Depends on / 依赖: IsEmbedding, IsEmbedding.uliftDown.t1Space, t1Space, uliftDown
-/
instance ULift.instT1Space [T1Space X] : T1Space (ULift X) :=
  IsEmbedding.uliftDown.t1Space

-- see Note [lower instance priority]
instance (priority := 100) T1Space.t0Space [T1Space X] : T0Space X :=
  (t1Space_iff_t0Space_and_r0Space.mp ‹T1Space X›).left

@[simp]
/--
theorem `compl_singleton_mem_nhds_iff` / 定理 `compl_singleton_mem_nhds_iff`

English:
theorem compl_singleton_mem_nhds_iff
  given: [T1Space X] {x y : X}
  statement: {x}ᶜ in 𝓝 y ↔ y != x
  proof: isOpen_compl_singleton.mem_nhds_iff

中文:
定理 compl_singleton_mem_nhds_iff
  条件: [T1Space X] {x y : X}
  结论: {x}ᶜ in 𝓝 y ↔ y != x
  证明: isOpen_compl_singleton.mem_nhds_iff

Depends on / 依赖: isOpen_compl_singleton, isOpen_compl_singleton.mem_nhds_iff, mem_nhds_iff
-/
theorem compl_singleton_mem_nhds_iff [T1Space X] {x y : X} : {x}ᶜ in 𝓝 y ↔ y != x :=
  isOpen_compl_singleton.mem_nhds_iff

/--
theorem `compl_singleton_mem_nhds` / 定理 `compl_singleton_mem_nhds`

English:
theorem compl_singleton_mem_nhds
  given: [T1Space X] {x y : X} (h : y != x)
  statement: {x}ᶜ in 𝓝 y
  proof: compl_singleton_mem_nhds_iff.mpr h

@[closedness =]

中文:
定理 compl_singleton_mem_nhds
  条件: [T1Space X] {x y : X} (h : y != x)
  结论: {x}ᶜ in 𝓝 y
  证明: compl_singleton_mem_nhds_iff.mpr h

@[closedness =]

Depends on / 依赖: compl_singleton_mem_nhds_iff, compl_singleton_mem_nhds_iff.mpr
-/
theorem compl_singleton_mem_nhds [T1Space X] {x y : X} (h : y != x) : {x}ᶜ in 𝓝 y :=
  compl_singleton_mem_nhds_iff.mpr h

@[closedness =]
/--
theorem `closure_singleton` / 定理 `closure_singleton`

English:
theorem closure_singleton
  given: [T1Space X] {x : X}
  statement: closure ({x} : Set X) = {x}
  proof: isClosed_singleton.closure_eq

中文:
定理 closure_singleton
  条件: [T1Space X] {x : X}
  结论: closure ({x} : Set X) = {x}
  证明: isClosed_singleton.closure_eq

Depends on / 依赖: closure_eq, isClosed_singleton, isClosed_singleton.closure_eq
-/
theorem closure_singleton [T1Space X] {x : X} : closure ({x} : Set X) = {x} :=
  isClosed_singleton.closure_eq

/--
lemma `Set.Subsingleton.isClosed` / 引理 `Set.Subsingleton.isClosed`

English:
lemma Set.Subsingleton.isClosed
  given: [T1Space X] {s : Set X} (hs : s.Subsingleton)
  statement: IsClosed s
  proof: by
  rcases hs.eq_empty_or_singleton with rfl | ⟨x, rfl⟩
  · exact isClosed_empty
  · exact isClosed_singleton

中文:
引理 Set.Subsingleton.isClosed
  条件: [T1Space X] {s : Set X} (hs : s.Subsingleton)
  结论: IsClosed s
  证明: by
  rcases hs.eq_empty_or_singleton with rfl | ⟨x, rfl⟩
  · exact isClosed_empty
  · exact isClosed_singleton

Depends on / 依赖: eq_empty_or_singleton, hs.eq_empty_or_singleton, isClosed_empty, isClosed_singleton
-/
lemma Set.Subsingleton.isClosed [T1Space X] {s : Set X} (hs : s.Subsingleton) : IsClosed s := by
  rcases hs.eq_empty_or_singleton with rfl | ⟨x, rfl⟩
  · exact isClosed_empty
  · exact isClosed_singleton

/--
theorem `Set.Subsingleton.closure_eq` / 定理 `Set.Subsingleton.closure_eq`

English:
theorem Set.Subsingleton.closure_eq
  given: [T1Space X] {s : Set X} (hs : s.Subsingleton)
  proof: hs.isClosed.closure_eq

中文:
定理 Set.Subsingleton.closure_eq
  条件: [T1Space X] {s : Set X} (hs : s.Subsingleton)
  证明: hs.isClosed.closure_eq

Depends on / 依赖: closure_eq, hs.isClosed.closure_eq, isClosed
-/
theorem Set.Subsingleton.closure_eq [T1Space X] {s : Set X} (hs : s.Subsingleton) :
    closure s = s :=
  hs.isClosed.closure_eq

/--
theorem `Set.Subsingleton.closure` / 定理 `Set.Subsingleton.closure`

English:
theorem Set.Subsingleton.closure
  given: [T1Space X] {s : Set X} (hs : s.Subsingleton)
  proof: by
  rwa [hs.closure_eq]

@[simp]

中文:
定理 Set.Subsingleton.closure
  条件: [T1Space X] {s : Set X} (hs : s.Subsingleton)
  证明: by
  rwa [hs.closure_eq]

@[simp]

Depends on / 依赖: closure_eq, hs.closure_eq
-/
theorem Set.Subsingleton.closure [T1Space X] {s : Set X} (hs : s.Subsingleton) :
    (closure s).Subsingleton := by
  rwa [hs.closure_eq]

@[simp]
/--
theorem `subsingleton_closure` / 定理 `subsingleton_closure`

English:
theorem subsingleton_closure
  given: [T1Space X] {s : Set X}
  statement: (closure s).Subsingleton ↔ s.Subsingleton
  proof: ⟨fun h => h.anti subset_closure, fun h => h.closure⟩

中文:
定理 subsingleton_closure
  条件: [T1Space X] {s : Set X}
  结论: (closure s).Subsingleton ↔ s.Subsingleton
  证明: ⟨fun h => h.anti subset_closure, fun h => h.closure⟩

Depends on / 依赖: closure, h.anti, h.closure, subset_closure
-/
theorem subsingleton_closure [T1Space X] {s : Set X} : (closure s).Subsingleton ↔ s.Subsingleton :=
  ⟨fun h => h.anti subset_closure, fun h => h.closure⟩

set_option backward.isDefEq.respectTransparency false in
/--
theorem `isClosedMap_const` / 定理 `isClosedMap_const`

English:
theorem isClosedMap_const
  given: {X Y} [TopologicalSpace X] [TopologicalSpace Y] [T1Space Y] {y : Y}
  proof: IsClosedMap.of_nonempty fun s _ h2s => by simp_rw [const, h2s.image_const, isClosed_singleton]

中文:
定理 isClosedMap_const
  条件: {X Y} [TopologicalSpace X] [TopologicalSpace Y] [T1Space Y] {y : Y}
  证明: IsClosedMap.of_nonempty fun s _ h2s => by simp_rw [const, h2s.image_const, isClosed_singleton]

Depends on / 依赖: IsClosedMap, IsClosedMap.of_nonempty, h2s.image_const, image_const, isClosed_singleton, of_nonempty, simp_rw
-/
theorem isClosedMap_const {X Y} [TopologicalSpace X] [TopologicalSpace Y] [T1Space Y] {y : Y} :
    IsClosedMap (Function.const X y) :=
  IsClosedMap.of_nonempty fun s _ h2s => by simp_rw [const, h2s.image_const, isClosed_singleton]

/--
lemma `isClosedMap_prodMk_left` / 引理 `isClosedMap_prodMk_left`

English:
lemma isClosedMap_prodMk_left
  given: [TopologicalSpace Y] [T1Space X] (x : X)
  proof: fun _K hK => Set.singleton_prod ▸ isClosed_singleton.prod hK

中文:
引理 isClosedMap_prodMk_left
  条件: [TopologicalSpace Y] [T1Space X] (x : X)
  证明: fun _K hK => Set.singleton_prod ▸ isClosed_singleton.prod hK

Depends on / 依赖: Set.singleton_prod, isClosed_singleton, isClosed_singleton.prod, singleton_prod
-/
lemma isClosedMap_prodMk_left [TopologicalSpace Y] [T1Space X] (x : X) :
    IsClosedMap (fun y : Y => Prod.mk x y) :=
  fun _K hK => Set.singleton_prod ▸ isClosed_singleton.prod hK

/--
lemma `isClosedMap_prodMk_right` / 引理 `isClosedMap_prodMk_right`

English:
lemma isClosedMap_prodMk_right
  given: [TopologicalSpace Y] [T1Space Y] (y : Y)
  proof: fun _K hK => Set.prod_singleton ▸ hK.prod isClosed_singleton

中文:
引理 isClosedMap_prodMk_right
  条件: [TopologicalSpace Y] [T1Space Y] (y : Y)
  证明: fun _K hK => Set.prod_singleton ▸ hK.prod isClosed_singleton

Depends on / 依赖: Set.prod_singleton, hK.prod, isClosed_singleton, prod_singleton
-/
lemma isClosedMap_prodMk_right [TopologicalSpace Y] [T1Space Y] (y : Y) :
    IsClosedMap (fun x : X => Prod.mk x y) :=
  fun _K hK => Set.prod_singleton ▸ hK.prod isClosed_singleton

/--
theorem `nhdsWithin_insert_of_ne` / 定理 `nhdsWithin_insert_of_ne`

English:
theorem nhdsWithin_insert_of_ne
  given: [T1Space X] {x y : X} {s : Set X} (hxy : x != y)
  proof: by
  refine le_antisymm (Filter.le_def.2 fun t ht => ?_) (nhdsWithin_mono x <| subset_insert y s)
  obtain ⟨o, ho, hxo, host⟩ := mem_nhdsWithin.mp ht
  refine mem_nhdsWithin.mpr ⟨o \ {y}, ho.sdiff isClosed_singleton, ⟨hxo, hxy⟩, ?_⟩
  rw [inter_insert_of_notMem <| notMem_sdiff_of_mem (mem_singleton 

中文:
定理 nhdsWithin_insert_of_ne
  条件: [T1Space X] {x y : X} {s : Set X} (hxy : x != y)
  证明: by
  refine le_antisymm (Filter.le_def.2 fun t ht => ?_) (nhdsWithin_mono x <| subset_insert y s)
  obtain ⟨o, ho, hxo, host⟩ := mem_nhdsWithin.mp ht
  refine mem_nhdsWithin.mpr ⟨o \ {y}, ho.sdiff isClosed_singleton, ⟨hxo, hxy⟩, ?_⟩
  rw [inter_insert_of_notMem <| notMem_sdiff_of_mem (mem_singleton 

Depends on / 依赖: Filter, Filter.le_def, Subset, Subset.rfl, ho.sdiff, inter_insert_of_notMem, inter_subset_inter, isClosed_singleton, le_antisymm, le_def, mem_nhdsWithin, mem_nhdsWithin.mp, mem_nhdsWithin.mpr, mem_singleton, nhdsWithin_mono, notMem_sdiff_of_mem, sdiff_subset, subset_insert
-/
theorem nhdsWithin_insert_of_ne [T1Space X] {x y : X} {s : Set X} (hxy : x != y) :
    𝓝[insert y s] x = 𝓝[s] x := by
  refine le_antisymm (Filter.le_def.2 fun t ht => ?_) (nhdsWithin_mono x <| subset_insert y s)
  obtain ⟨o, ho, hxo, host⟩ := mem_nhdsWithin.mp ht
  refine mem_nhdsWithin.mpr ⟨o \ {y}, ho.sdiff isClosed_singleton, ⟨hxo, hxy⟩, ?_⟩
  rw [inter_insert_of_notMem <| notMem_sdiff_of_mem (mem_singleton y)]
  exact (inter_subset_inter sdiff_subset Subset.rfl).trans host

/--
theorem `insert_mem_nhdsWithin_of_subset_insert` / 定理 `insert_mem_nhdsWithin_of_subset_insert`

English:
theorem insert_mem_nhdsWithin_of_subset_insert
  statement: [T1Space X] {x y : X} {s t : Set X}
  proof: by
  rcases eq_or_ne x y with (rfl | h)
  · exact mem_of_superset self_mem_nhdsWithin hu
  refine nhdsWithin_mono x hu ?_
  rw [nhdsWithin_insert_of_ne h]
  exact mem_of_superset self_mem_nhdsWithin (subset_insert x s)

中文:
定理 insert_mem_nhdsWithin_of_subset_insert
  结论: [T1Space X] {x y : X} {s t : Set X}
  证明: by
  rcases eq_or_ne x y with (rfl | h)
  · exact mem_of_superset self_mem_nhdsWithin hu
  refine nhdsWithin_mono x hu ?_
  rw [nhdsWithin_insert_of_ne h]
  exact mem_of_superset self_mem_nhdsWithin (subset_insert x s)

Depends on / 依赖: eq_or_ne, mem_of_superset, nhdsWithin_insert_of_ne, nhdsWithin_mono, self_mem_nhdsWithin, subset_insert
-/
theorem insert_mem_nhdsWithin_of_subset_insert [T1Space X] {x y : X} {s t : Set X}
    (hu : t subseteq insert y s) : insert x s in 𝓝[t] x := by
  rcases eq_or_ne x y with (rfl | h)
  · exact mem_of_superset self_mem_nhdsWithin hu
  refine nhdsWithin_mono x hu ?_
  rw [nhdsWithin_insert_of_ne h]
  exact mem_of_superset self_mem_nhdsWithin (subset_insert x s)

/--
lemma `eventuallyEq_insert` / 引理 `eventuallyEq_insert`

English:
lemma eventuallyEq_insert
  given: [T1Space X] {s t : Set X} {x y : X} (h : s =ᶠ[𝓝[{y}ᶜ] x] t)
  proof: by
  simp_rw [eventuallyEq_set] at h ⊢
  simp_rw [← union_singleton, ← nhdsWithin_univ, ← compl_union_self {x},
    nhdsWithin_union, eventually_sup, nhdsWithin_singleton,
    eventually_pure, union_singleton, mem_insert_iff, true_or, and_true]
  filter_upwards [nhdsWithin_compl_singleton_le x y h] 

中文:
引理 eventuallyEq_insert
  条件: [T1Space X] {s t : Set X} {x y : X} (h : s =ᶠ[𝓝[{y}ᶜ] x] t)
  证明: by
  simp_rw [eventuallyEq_set] at h ⊢
  simp_rw [← union_singleton, ← nhdsWithin_univ, ← compl_union_self {x},
    nhdsWithin_union, eventually_sup, nhdsWithin_singleton,
    eventually_pure, union_singleton, mem_insert_iff, true_or, and_true]
  filter_upwards [nhdsWithin_compl_singleton_le x y h] 

Depends on / 依赖: Iff.rfl, and_true, compl_union_self, eventuallyEq_set, eventually_pure, eventually_sup, filter_upwards, mem_insert_iff, nhdsWithin_compl_singleton_le, nhdsWithin_singleton, nhdsWithin_union, nhdsWithin_univ, or_congr, simp_rw, true_or, union_singleton
-/
lemma eventuallyEq_insert [T1Space X] {s t : Set X} {x y : X} (h : s =ᶠ[𝓝[{y}ᶜ] x] t) :
    (insert x s : Set X) =ᶠ[𝓝 x] (insert x t : Set X) := by
  simp_rw [eventuallyEq_set] at h ⊢
  simp_rw [← union_singleton, ← nhdsWithin_univ, ← compl_union_self {x},
    nhdsWithin_union, eventually_sup, nhdsWithin_singleton,
    eventually_pure, union_singleton, mem_insert_iff, true_or, and_true]
  filter_upwards [nhdsWithin_compl_singleton_le x y h] with y using or_congr (Iff.rfl)

@[simp]
/--
theorem `ker_nhds` / 定理 `ker_nhds`

English:
theorem ker_nhds
  given: [T1Space X] (x : X)
  statement: (𝓝 x).ker = {x}
  proof: by
  simp [ker_nhds_eq_specializes]

中文:
定理 ker_nhds
  条件: [T1Space X] (x : X)
  结论: (𝓝 x).ker = {x}
  证明: by
  simp [ker_nhds_eq_specializes]

Depends on / 依赖: ker_nhds_eq_specializes
-/
theorem ker_nhds [T1Space X] (x : X) : (𝓝 x).ker = {x} := by
  simp [ker_nhds_eq_specializes]

/--
theorem `biInter_basis_nhds` / 定理 `biInter_basis_nhds`

English:
theorem biInter_basis_nhds
  statement: [T1Space X] {ι : Sort*} {p : ι -> Prop} {s : ι -> Set X} {x : X}
  proof: by
  rw [← h.ker]; rw [ker_nhds]

@[simp]

中文:
定理 biInter_basis_nhds
  结论: [T1Space X] {ι : Sort*} {p : ι -> 命题} {s : ι -> Set X} {x : X}
  证明: by
  rw [← h.ker]; rw [ker_nhds]

@[simp]

Depends on / 依赖: h.ker, ker_nhds
-/
theorem biInter_basis_nhds [T1Space X] {ι : Sort*} {p : ι -> Prop} {s : ι -> Set X} {x : X}
    (h : (𝓝 x).HasBasis p s) : ⋂ (i) (_ : p i), s i = {x} := by
  rw [← h.ker]; rw [ker_nhds]

@[simp]
/--
theorem `compl_singleton_mem_nhdsSet_iff` / 定理 `compl_singleton_mem_nhdsSet_iff`

English:
theorem compl_singleton_mem_nhdsSet_iff
  given: [T1Space X] {x : X} {s : Set X}
  statement: {x}ᶜ in 𝓝ˢ s ↔ x ∉ s
  proof: by
  rw [isOpen_compl_singleton.mem_nhdsSet]; rw [subset_compl_singleton_iff]

@[simp]

中文:
定理 compl_singleton_mem_nhdsSet_iff
  条件: [T1Space X] {x : X} {s : Set X}
  结论: {x}ᶜ in 𝓝ˢ s ↔ x ∉ s
  证明: by
  rw [isOpen_compl_singleton.mem_nhdsSet]; rw [subset_compl_singleton_iff]

@[simp]

Depends on / 依赖: isOpen_compl_singleton, isOpen_compl_singleton.mem_nhdsSet, mem_nhdsSet, subset_compl_singleton_iff
-/
theorem compl_singleton_mem_nhdsSet_iff [T1Space X] {x : X} {s : Set X} : {x}ᶜ in 𝓝ˢ s ↔ x ∉ s := by
  rw [isOpen_compl_singleton.mem_nhdsSet]; rw [subset_compl_singleton_iff]

@[simp]
/--
theorem `nhdsSet_le_iff` / 定理 `nhdsSet_le_iff`

English:
theorem nhdsSet_le_iff
  given: [T1Space X] {s t : Set X}
  statement: 𝓝ˢ s <= 𝓝ˢ t ↔ s subseteq t
  proof: by
  refine ⟨?_, fun h => monotone_nhdsSet h⟩
  simp_rw [Filter.le_def]; intro h x hx
  specialize h {x}ᶜ
  simp_rw [compl_singleton_mem_nhdsSet_iff] at h
  by_contra hxt
  exact h hxt hx

@[simp]

中文:
定理 nhdsSet_le_iff
  条件: [T1Space X] {s t : Set X}
  结论: 𝓝ˢ s <= 𝓝ˢ t ↔ s subseteq t
  证明: by
  refine ⟨?_, fun h => monotone_nhdsSet h⟩
  simp_rw [Filter.le_def]; intro h x hx
  specialize h {x}ᶜ
  simp_rw [compl_singleton_mem_nhdsSet_iff] at h
  by_contra hxt
  exact h hxt hx

@[simp]

Depends on / 依赖: Filter, Filter.le_def, compl_singleton_mem_nhdsSet_iff, le_def, monotone_nhdsSet, simp_rw, specialize
-/
theorem nhdsSet_le_iff [T1Space X] {s t : Set X} : 𝓝ˢ s <= 𝓝ˢ t ↔ s subseteq t := by
  refine ⟨?_, fun h => monotone_nhdsSet h⟩
  simp_rw [Filter.le_def]; intro h x hx
  specialize h {x}ᶜ
  simp_rw [compl_singleton_mem_nhdsSet_iff] at h
  by_contra hxt
  exact h hxt hx

@[simp]
/--
theorem `nhdsSet_inj_iff` / 定理 `nhdsSet_inj_iff`

English:
theorem nhdsSet_inj_iff
  given: [T1Space X] {s t : Set X}
  statement: 𝓝ˢ s = 𝓝ˢ t ↔ s = t
  proof: by
  simp_rw [le_antisymm_iff]
  exact and_congr nhdsSet_le_iff nhdsSet_le_iff

中文:
定理 nhdsSet_inj_iff
  条件: [T1Space X] {s t : Set X}
  结论: 𝓝ˢ s = 𝓝ˢ t ↔ s = t
  证明: by
  simp_rw [le_antisymm_iff]
  exact and_congr nhdsSet_le_iff nhdsSet_le_iff

Depends on / 依赖: and_congr, le_antisymm_iff, nhdsSet_le_iff, simp_rw
-/
theorem nhdsSet_inj_iff [T1Space X] {s t : Set X} : 𝓝ˢ s = 𝓝ˢ t ↔ s = t := by
  simp_rw [le_antisymm_iff]
  exact and_congr nhdsSet_le_iff nhdsSet_le_iff

/--
theorem `injective_nhdsSet` / 定理 `injective_nhdsSet`

English:
theorem injective_nhdsSet
  given: [T1Space X]
  statement: Function.Injective (𝓝ˢ : Set X -> Filter X)
  proof: fun _ _ hst =>
  nhdsSet_inj_iff.mp hst

中文:
定理 injective_nhdsSet
  条件: [T1Space X]
  结论: Function.Injective (𝓝ˢ : Set X -> Filter X)
  证明: fun _ _ hst =>
  nhdsSet_inj_iff.mp hst
-/
theorem injective_nhdsSet [T1Space X] : Function.Injective (𝓝ˢ : Set X -> Filter X) := fun _ _ hst =>
  nhdsSet_inj_iff.mp hst

/--
theorem `strictMono_nhdsSet` / 定理 `strictMono_nhdsSet`

English:
theorem strictMono_nhdsSet
  given: [T1Space X]
  statement: StrictMono (𝓝ˢ : Set X -> Filter X)
  proof: monotone_nhdsSet.strictMono_of_injective injective_nhdsSet

@[simp]

中文:
定理 strictMono_nhdsSet
  条件: [T1Space X]
  结论: StrictMono (𝓝ˢ : Set X -> Filter X)
  证明: monotone_nhdsSet.strictMono_of_injective injective_nhdsSet

@[simp]

Depends on / 依赖: injective_nhdsSet, monotone_nhdsSet, monotone_nhdsSet.strictMono_of_injective, strictMono_of_injective
-/
theorem strictMono_nhdsSet [T1Space X] : StrictMono (𝓝ˢ : Set X -> Filter X) :=
  monotone_nhdsSet.strictMono_of_injective injective_nhdsSet

@[simp]
/--
theorem `nhds_le_nhdsSet_iff` / 定理 `nhds_le_nhdsSet_iff`

English:
theorem nhds_le_nhdsSet_iff
  given: [T1Space X] {s : Set X} {x : X}
  statement: 𝓝 x <= 𝓝ˢ s ↔ x in s
  proof: by
  rw [← nhdsSet_singleton]; rw [nhdsSet_le_iff]; rw [singleton_subset_iff]

中文:
定理 nhds_le_nhdsSet_iff
  条件: [T1Space X] {s : Set X} {x : X}
  结论: 𝓝 x <= 𝓝ˢ s ↔ x in s
  证明: by
  rw [← nhdsSet_singleton]; rw [nhdsSet_le_iff]; rw [singleton_subset_iff]

Depends on / 依赖: nhdsSet_le_iff, nhdsSet_singleton, singleton_subset_iff
-/
theorem nhds_le_nhdsSet_iff [T1Space X] {s : Set X} {x : X} : 𝓝 x <= 𝓝ˢ s ↔ x in s := by
  rw [← nhdsSet_singleton]; rw [nhdsSet_le_iff]; rw [singleton_subset_iff]

/--
theorem `Dense.sdiff_singleton` / 定理 `Dense.sdiff_singleton`

English:
theorem Dense.sdiff_singleton
  given: [T1Space X] {s : Set X} (hs : Dense s) (x : X) [NeBot (𝓝[!=] x)]
  proof: hs.inter_of_isOpen_right (dense_compl_singleton x) isOpen_compl_singleton

@[deprecated (since := "2026-06-03")] alias Dense.diff_singleton := Dense.sdiff_singleton

中文:
定理 Dense.sdiff_singleton
  条件: [T1Space X] {s : Set X} (hs : Dense s) (x : X) [NeBot (𝓝[!=] x)]
  证明: hs.inter_of_isOpen_right (dense_compl_singleton x) isOpen_compl_singleton

@[deprecated (since := "2026-06-03")] alias Dense.diff_singleton := Dense.sdiff_singleton

Depends on / 依赖: dense_compl_singleton, hs.inter_of_isOpen_right, inter_of_isOpen_right, isOpen_compl_singleton
-/
theorem Dense.sdiff_singleton [T1Space X] {s : Set X} (hs : Dense s) (x : X) [NeBot (𝓝[!=] x)] :
    Dense (s \ {x}) :=
  hs.inter_of_isOpen_right (dense_compl_singleton x) isOpen_compl_singleton

@[deprecated (since := "2026-06-03")] alias Dense.diff_singleton := Dense.sdiff_singleton

/--
theorem `Dense.sdiff_finset` / 定理 `Dense.sdiff_finset`

English:
theorem Dense.sdiff_finset
  statement: [T1Space X] [forall x : X, NeBot (𝓝[!=] x)] {s : Set X} (hs : Dense s)
  proof: by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using hs
  | insert _ _ _ ih =>
    rw [Finset.coe_insert]; rw [← union_singleton]; rw [← sdiff_sdiff]
    exact ih.sdiff_singleton _

@[deprecated (since := "2026-06-03")] alias Dense.diff_finset := Dense.sdiff_finset

中文:
定理 Dense.sdiff_finset
  结论: [T1Space X] [对任意 x : X, NeBot (𝓝[!=] x)] {s : Set X} (hs : Dense s)
  证明: by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using hs
  | insert _ _ _ ih =>
    rw [Finset.coe_insert]; rw [← union_singleton]; rw [← sdiff_sdiff]
    exact ih.sdiff_singleton _

@[deprecated (since := "2026-06-03")] alias Dense.diff_finset := Dense.sdiff_finset

Depends on / 依赖: Finset, Finset.coe_insert, Finset.induction_on, classical, coe_insert, ih.sdiff_singleton, induction_on, insert, sdiff_sdiff, sdiff_singleton, union_singleton
-/
theorem Dense.sdiff_finset [T1Space X] [forall x : X, NeBot (𝓝[!=] x)] {s : Set X} (hs : Dense s)
    (t : Finset X) : Dense (s \ t) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using hs
  | insert _ _ _ ih =>
    rw [Finset.coe_insert]; rw [← union_singleton]; rw [← sdiff_sdiff]
    exact ih.sdiff_singleton _

@[deprecated (since := "2026-06-03")] alias Dense.diff_finset := Dense.sdiff_finset

/--
theorem `Dense.sdiff_finite` / 定理 `Dense.sdiff_finite`

English:
theorem Dense.sdiff_finite
  statement: [T1Space X] [forall x : X, NeBot (𝓝[!=] x)] {s : Set X} (hs : Dense s)
  proof: by
  convert! hs.sdiff_finset ht.toFinset
  exact (Finite.coe_toFinset _).symm

@[deprecated (since := "2026-06-03")] alias Dense.diff_finite := Dense.sdiff_finite

中文:
定理 Dense.sdiff_finite
  结论: [T1Space X] [对任意 x : X, NeBot (𝓝[!=] x)] {s : Set X} (hs : Dense s)
  证明: by
  convert! hs.sdiff_finset ht.toFinset
  exact (Finite.coe_toFinset _).symm

@[deprecated (since := "2026-06-03")] alias Dense.diff_finite := Dense.sdiff_finite

Depends on / 依赖: Finite, Finite.coe_toFinset, coe_toFinset, convert, hs.sdiff_finset, ht.toFinset, sdiff_finset, toFinset
-/
theorem Dense.sdiff_finite [T1Space X] [forall x : X, NeBot (𝓝[!=] x)] {s : Set X} (hs : Dense s)
    {t : Set X} (ht : t.Finite) : Dense (s \ t) := by
  convert! hs.sdiff_finset ht.toFinset
  exact (Finite.coe_toFinset _).symm

@[deprecated (since := "2026-06-03")] alias Dense.diff_finite := Dense.sdiff_finite

/--
theorem `eq_of_tendsto_nhds` / 定理 `eq_of_tendsto_nhds`

English:
theorem eq_of_tendsto_nhds
  statement: [TopologicalSpace Y] [T1Space Y] {f : X -> Y} {x : X} {y : Y}
  proof: by_contra fun hfa : f x != y =>
    have fact₁ : {f x}ᶜ in 𝓝 y := compl_singleton_mem_nhds hfa.symm
    have fact₂ : Tendsto f (pure x) (𝓝 y) := h.comp (tendsto_id'.2 <| pure_le_nhds x)
    fact₂ fact₁ (Eq.refl <| f x)

中文:
定理 eq_of_tendsto_nhds
  结论: [TopologicalSpace Y] [T1Space Y] {f : X -> Y} {x : X} {y : Y}
  证明: by_contra fun hfa : f x != y =>
    have fact₁ : {f x}ᶜ in 𝓝 y := compl_singleton_mem_nhds hfa.symm
    have fact₂ : Tendsto f (pure x) (𝓝 y) := h.comp (tendsto_id'.2 <| pure_le_nhds x)
    fact₂ fact₁ (Eq.refl <| f x)

Depends on / 依赖: Eq.refl, Tendsto, compl_singleton_mem_nhds, h.comp, hfa.symm, pure_le_nhds, tendsto_id
-/
theorem eq_of_tendsto_nhds [TopologicalSpace Y] [T1Space Y] {f : X -> Y} {x : X} {y : Y}
    (h : Tendsto f (𝓝 x) (𝓝 y)) : f x = y :=
  by_contra fun hfa : f x != y =>
    have fact₁ : {f x}ᶜ in 𝓝 y := compl_singleton_mem_nhds hfa.symm
    have fact₂ : Tendsto f (pure x) (𝓝 y) := h.comp (tendsto_id'.2 <| pure_le_nhds x)
    fact₂ fact₁ (Eq.refl <| f x)

/--
theorem `Filter.Tendsto.eventually_ne` / 定理 `Filter.Tendsto.eventually_ne`

English:
theorem Filter.Tendsto.eventually_ne
  statement: {X} [TopologicalSpace Y] [T1Space Y] {g : X -> Y}
  proof: hg.eventually (isOpen_compl_singleton.eventually_mem hb)

中文:
定理 Filter.Tendsto.eventually_ne
  结论: {X} [TopologicalSpace Y] [T1Space Y] {g : X -> Y}
  证明: hg.eventually (isOpen_compl_singleton.eventually_mem hb)

Depends on / 依赖: eventually, eventually_mem, hg.eventually, isOpen_compl_singleton, isOpen_compl_singleton.eventually_mem
-/
theorem Filter.Tendsto.eventually_ne {X} [TopologicalSpace Y] [T1Space Y] {g : X -> Y}
    {l : Filter X} {b₁ b₂ : Y} (hg : Tendsto g l (𝓝 b₁)) (hb : b₁ != b₂) : forallᶠ z in l, g z != b₂ :=
  hg.eventually (isOpen_compl_singleton.eventually_mem hb)

/--
theorem `ContinuousAt.eventually_ne` / 定理 `ContinuousAt.eventually_ne`

English:
theorem ContinuousAt.eventually_ne
  statement: [TopologicalSpace Y] [T1Space Y] {g : X -> Y} {x : X} {y : Y}
  proof: hg1.tendsto.eventually_ne hg2

中文:
定理 ContinuousAt.eventually_ne
  结论: [TopologicalSpace Y] [T1Space Y] {g : X -> Y} {x : X} {y : Y}
  证明: hg1.tendsto.eventually_ne hg2

Depends on / 依赖: eventually_ne, hg1.tendsto.eventually_ne, tendsto
-/
theorem ContinuousAt.eventually_ne [TopologicalSpace Y] [T1Space Y] {g : X -> Y} {x : X} {y : Y}
    (hg1 : ContinuousAt g x) (hg2 : g x != y) : forallᶠ z in 𝓝 x, g z != y :=
  hg1.tendsto.eventually_ne hg2

/--
theorem `eventually_ne_nhds` / 定理 `eventually_ne_nhds`

English:
theorem eventually_ne_nhds
  given: [T1Space X] {a b : X} (h : a != b)
  statement: forallᶠ x in 𝓝 a, x != b
  proof: IsOpen.eventually_mem isOpen_ne h

中文:
定理 eventually_ne_nhds
  条件: [T1Space X] {a b : X} (h : a != b)
  结论: 对任意ᶠ x in 𝓝 a, x != b
  证明: IsOpen.eventually_mem isOpen_ne h

Depends on / 依赖: IsOpen, IsOpen.eventually_mem, eventually_mem, isOpen_ne
-/
theorem eventually_ne_nhds [T1Space X] {a b : X} (h : a != b) : forallᶠ x in 𝓝 a, x != b :=
  IsOpen.eventually_mem isOpen_ne h

/--
theorem `eventually_ne_nhdsWithin` / 定理 `eventually_ne_nhdsWithin`

English:
theorem eventually_ne_nhdsWithin
  given: [T1Space X] {a b : X} {s : Set X} (h : a != b)
  proof: Filter.Eventually.filter_mono nhdsWithin_le_nhds eventually_ne_nhds h

中文:
定理 eventually_ne_nhdsWithin
  条件: [T1Space X] {a b : X} {s : Set X} (h : a != b)
  证明: Filter.Eventually.filter_mono nhdsWithin_le_nhds eventually_ne_nhds h

Depends on / 依赖: Eventually, Filter, Filter.Eventually.filter_mono, eventually_ne_nhds, filter_mono, nhdsWithin_le_nhds
-/
theorem eventually_ne_nhdsWithin [T1Space X] {a b : X} {s : Set X} (h : a != b) :
    forallᶠ x in 𝓝[s] a, x != b :=
Filter.Eventually.filter_mono nhdsWithin_le_nhds eventually_ne_nhds h

/--
theorem `eventually_nhdsWithin_eventually_nhds_iff_of_isOpen` / 定理 `eventually_nhdsWithin_eventually_nhds_iff_of_isOpen`

English:
theorem eventually_nhdsWithin_eventually_nhds_iff_of_isOpen
  statement: {s : Set X} {a : X} {p : X -> Prop}
  proof: by
  nth_rw 2 [← eventually_eventually_nhdsWithin]
  constructor
  · intro h
    filter_upwards [h] with _ hy
    exact eventually_nhdsWithin_of_eventually_nhds hy
  · intro h
    filter_upwards [h, eventually_nhdsWithin_of_forall fun _ a => a] with _ _ _
    simp_all [IsOpen.nhdsWithin_eq]

@[simp]

中文:
定理 eventually_nhdsWithin_eventually_nhds_iff_of_isOpen
  结论: {s : Set X} {a : X} {p : X -> 命题}
  证明: by
  nth_rw 2 [← eventually_eventually_nhdsWithin]
  constructor
  · intro h
    filter_upwards [h] with _ hy
    exact eventually_nhdsWithin_of_eventually_nhds hy
  · intro h
    filter_upwards [h, eventually_nhdsWithin_of_forall fun _ a => a] with _ _ _
    simp_all [IsOpen.nhdsWithin_eq]

@[simp]

Depends on / 依赖: IsOpen, IsOpen.nhdsWithin_eq, eventually_eventually_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds, eventually_nhdsWithin_of_forall, filter_upwards, nhdsWithin_eq, nth_rw
-/
theorem eventually_nhdsWithin_eventually_nhds_iff_of_isOpen {s : Set X} {a : X} {p : X -> Prop}
    (hs : IsOpen s) : (forallᶠ y in 𝓝[s] a, forallᶠ x in 𝓝 y, p x) ↔ forallᶠ x in 𝓝[s] a, p x := by
  nth_rw 2 [← eventually_eventually_nhdsWithin]
  constructor
  · intro h
    filter_upwards [h] with _ hy
    exact eventually_nhdsWithin_of_eventually_nhds hy
  · intro h
    filter_upwards [h, eventually_nhdsWithin_of_forall fun _ a => a] with _ _ _
    simp_all [IsOpen.nhdsWithin_eq]

@[simp]
/--
theorem `eventually_nhdsNE_eventually_nhds_iff` / 定理 `eventually_nhdsNE_eventually_nhds_iff`

English:
theorem eventually_nhdsNE_eventually_nhds_iff
  given: [T1Space X] {a : X} {p : X -> Prop}
  proof: eventually_nhdsWithin_eventually_nhds_iff_of_isOpen isOpen_ne

中文:
定理 eventually_nhdsNE_eventually_nhds_iff
  条件: [T1Space X] {a : X} {p : X -> 命题}
  证明: eventually_nhdsWithin_eventually_nhds_iff_of_isOpen isOpen_ne

Depends on / 依赖: eventually_nhdsWithin_eventually_nhds_iff_of_isOpen, isOpen_ne
-/
theorem eventually_nhdsNE_eventually_nhds_iff [T1Space X] {a : X} {p : X -> Prop} :
    (forallᶠ y in 𝓝[!=] a, forallᶠ x in 𝓝 y, p x) ↔ forallᶠ x in 𝓝[!=] a, p x :=
  eventually_nhdsWithin_eventually_nhds_iff_of_isOpen isOpen_ne

/--
theorem `continuousWithinAt_insert` / 定理 `continuousWithinAt_insert`

English:
theorem continuousWithinAt_insert
  statement: [TopologicalSpace Y] [T1Space X]
  proof: by
  rcases eq_or_ne x y with (rfl | h)
  · exact continuousWithinAt_insert_self
  simp_rw [ContinuousWithinAt, nhdsWithin_insert_of_ne h]

alias ⟨ContinuousWithinAt.of_insert, ContinuousWithinAt.insert'⟩ := continuousWithinAt_insert

中文:
定理 continuousWithinAt_insert
  结论: [TopologicalSpace Y] [T1Space X]
  证明: by
  rcases eq_or_ne x y with (rfl | h)
  · exact continuousWithinAt_insert_self
  simp_rw [ContinuousWithinAt, nhdsWithin_insert_of_ne h]

alias ⟨ContinuousWithinAt.of_insert, ContinuousWithinAt.insert'⟩ := continuousWithinAt_insert

Depends on / 依赖: ContinuousWithinAt, continuousWithinAt_insert_self, eq_or_ne, nhdsWithin_insert_of_ne, simp_rw
-/
theorem continuousWithinAt_insert [TopologicalSpace Y] [T1Space X]
    {x y : X} {s : Set X} {f : X -> Y} :
    ContinuousWithinAt f (insert y s) x ↔ ContinuousWithinAt f s x := by
  rcases eq_or_ne x y with (rfl | h)
  · exact continuousWithinAt_insert_self
  simp_rw [ContinuousWithinAt, nhdsWithin_insert_of_ne h]

alias ⟨ContinuousWithinAt.of_insert, ContinuousWithinAt.insert'⟩ := continuousWithinAt_insert

/--
theorem `continuousWithinAt_sdiff_singleton` / 定理 `continuousWithinAt_sdiff_singleton`

English:
theorem continuousWithinAt_sdiff_singleton
  statement: [TopologicalSpace Y] [T1Space X]
  proof: by
  rw [← continuousWithinAt_insert]; rw [insert_sdiff_singleton]; rw [continuousWithinAt_insert]

@[deprecated (since := "2026-06-03")]
alias continuousWithinAt_diff_singleton := continuousWithinAt_sdiff_singleton

中文:
定理 continuousWithinAt_sdiff_singleton
  结论: [TopologicalSpace Y] [T1Space X]
  证明: by
  rw [← continuousWithinAt_insert]; rw [insert_sdiff_singleton]; rw [continuousWithinAt_insert]

@[deprecated (since := "2026-06-03")]
alias continuousWithinAt_diff_singleton := continuousWithinAt_sdiff_singleton

Depends on / 依赖: continuousWithinAt_insert, insert_sdiff_singleton
-/
theorem continuousWithinAt_sdiff_singleton [TopologicalSpace Y] [T1Space X]
    {x y : X} {s : Set X} {f : X -> Y} :
    ContinuousWithinAt f (s \ {y}) x ↔ ContinuousWithinAt f s x := by
  rw [← continuousWithinAt_insert]; rw [insert_sdiff_singleton]; rw [continuousWithinAt_insert]

@[deprecated (since := "2026-06-03")]
alias continuousWithinAt_diff_singleton := continuousWithinAt_sdiff_singleton

/--
theorem `continuousWithinAt_congr_set'` / 定理 `continuousWithinAt_congr_set'`

English:
theorem continuousWithinAt_congr_set'
  statement: [TopologicalSpace Y] [T1Space X]
  proof: by
  rw [← continuousWithinAt_insert_self (s := s)]; rw [← continuousWithinAt_insert_self (s := t)]
  exact continuousWithinAt_congr_set (eventuallyEq_insert h)

中文:
定理 continuousWithinAt_congr_set'
  结论: [TopologicalSpace Y] [T1Space X]
  证明: by
  rw [← continuousWithinAt_insert_self (s := s)]; rw [← continuousWithinAt_insert_self (s := t)]
  exact continuousWithinAt_congr_set (eventuallyEq_insert h)

Depends on / 依赖: continuousWithinAt_congr_set, continuousWithinAt_insert_self, eventuallyEq_insert
-/
theorem continuousWithinAt_congr_set' [TopologicalSpace Y] [T1Space X]
    {x : X} {s t : Set X} {f : X -> Y} (y : X) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) :
    ContinuousWithinAt f s x ↔ ContinuousWithinAt f t x := by
  rw [← continuousWithinAt_insert_self (s := s)]; rw [← continuousWithinAt_insert_self (s := t)]
  exact continuousWithinAt_congr_set (eventuallyEq_insert h)

/--
theorem `ContinuousWithinAt.eq_const_of_mem_closure` / 定理 `ContinuousWithinAt.eq_const_of_mem_closure`

English:
theorem ContinuousWithinAt.eq_const_of_mem_closure
  statement: [TopologicalSpace Y] [T1Space Y]
  proof: by
  rw [← Set.mem_singleton_iff]; rw [← closure_singleton]
  exact h.mem_closure hx ht

中文:
定理 ContinuousWithinAt.eq_const_of_mem_closure
  结论: [TopologicalSpace Y] [T1Space Y]
  证明: by
  rw [← Set.mem_singleton_iff]; rw [← closure_singleton]
  exact h.mem_closure hx ht

Depends on / 依赖: Set.mem_singleton_iff, closure_singleton, h.mem_closure, mem_closure, mem_singleton_iff
-/
theorem ContinuousWithinAt.eq_const_of_mem_closure [TopologicalSpace Y] [T1Space Y]
    {f : X -> Y} {s : Set X} {x : X} {c : Y} (h : ContinuousWithinAt f s x) (hx : x in closure s)
    (ht : forall y in s, f y = c) : f x = c := by
  rw [← Set.mem_singleton_iff]; rw [← closure_singleton]
  exact h.mem_closure hx ht

/--
theorem `ContinuousWithinAt.eqOn_const_closure` / 定理 `ContinuousWithinAt.eqOn_const_closure`

English:
theorem ContinuousWithinAt.eqOn_const_closure
  statement: [TopologicalSpace Y] [T1Space Y]
  proof: by
  intro x hx
  apply ContinuousWithinAt.eq_const_of_mem_closure (h x hx) hx ht

中文:
定理 ContinuousWithinAt.eqOn_const_closure
  结论: [TopologicalSpace Y] [T1Space Y]
  证明: by
  intro x hx
  apply ContinuousWithinAt.eq_const_of_mem_closure (h x hx) hx ht

Depends on / 依赖: ContinuousWithinAt, ContinuousWithinAt.eq_const_of_mem_closure, eq_const_of_mem_closure
-/
theorem ContinuousWithinAt.eqOn_const_closure [TopologicalSpace Y] [T1Space Y]
    {f : X -> Y} {s : Set X} {c : Y} (h : forall x in closure s, ContinuousWithinAt f s x)
    (ht : s.EqOn f (fun _ => c)) : (closure s).EqOn f (fun _ => c) := by
  intro x hx
  apply ContinuousWithinAt.eq_const_of_mem_closure (h x hx) hx ht

/--
theorem `continuousAt_of_tendsto_nhds` / 定理 `continuousAt_of_tendsto_nhds`

English:
theorem continuousAt_of_tendsto_nhds
  statement: [TopologicalSpace Y] [T1Space Y] {f : X -> Y} {x : X} {y : Y}
  proof: by
  rwa [ContinuousAt, eq_of_tendsto_nhds h]

@[simp]

中文:
定理 continuousAt_of_tendsto_nhds
  结论: [TopologicalSpace Y] [T1Space Y] {f : X -> Y} {x : X} {y : Y}
  证明: by
  rwa [ContinuousAt, eq_of_tendsto_nhds h]

@[simp]

Depends on / 依赖: ContinuousAt, eq_of_tendsto_nhds
-/
theorem continuousAt_of_tendsto_nhds [TopologicalSpace Y] [T1Space Y] {f : X -> Y} {x : X} {y : Y}
    (h : Tendsto f (𝓝 x) (𝓝 y)) : ContinuousAt f x := by
  rwa [ContinuousAt, eq_of_tendsto_nhds h]

@[simp]
/--
theorem `tendsto_const_nhds_iff` / 定理 `tendsto_const_nhds_iff`

English:
theorem tendsto_const_nhds_iff
  given: [T1Space X] {l : Filter Y} [NeBot l] {c d : X}
  proof: by simp_rw [Tendsto, Filter.map_const, pure_le_nhds_iff]

中文:
定理 tendsto_const_nhds_iff
  条件: [T1Space X] {l : Filter Y} [NeBot l] {c d : X}
  证明: by simp_rw [Tendsto, Filter.map_const, pure_le_nhds_iff]

Depends on / 依赖: Filter, Filter.map_const, Tendsto, map_const, pure_le_nhds_iff, simp_rw
-/
theorem tendsto_const_nhds_iff [T1Space X] {l : Filter Y} [NeBot l] {c d : X} :
    Tendsto (fun _ => c) l (𝓝 d) ↔ c = d := by simp_rw [Tendsto, Filter.map_const, pure_le_nhds_iff]

/--
theorem `isOpen_singleton_of_finite_mem_nhds` / 定理 `isOpen_singleton_of_finite_mem_nhds`

English:
theorem isOpen_singleton_of_finite_mem_nhds
  statement: [T1Space X] (x : X)
  proof: by
  have A : {x} subseteq s := by simp only [singleton_subset_iff, mem_of_mem_nhds hs]
  have B : IsClosed (s \ {x}) := (hsf.subset sdiff_subset).isClosed
  have C : (s \ {x})ᶜ in 𝓝 x := B.isOpen_compl.mem_nhds fun h => h.2 rfl
  have D : {x} in 𝓝 x := by simpa only [← sdiff_eq, sdiff_sdiff_cancel_

中文:
定理 isOpen_singleton_of_finite_mem_nhds
  结论: [T1Space X] (x : X)
  证明: by
  have A : {x} subseteq s := by simp only [singleton_subset_iff, mem_of_mem_nhds hs]
  have B : IsClosed (s \ {x}) := (hsf.subset sdiff_subset).isClosed
  have C : (s \ {x})ᶜ in 𝓝 x := B.isOpen_compl.mem_nhds fun h => h.2 rfl
  have D : {x} in 𝓝 x := by simpa only [← sdiff_eq, sdiff_sdiff_cancel_

Depends on / 依赖: B.isOpen_compl.mem_nhds, IsClosed, hsf.subset, inter_mem, isClosed, isOpen_compl, mem_interior_iff_mem_nhds, mem_nhds, mem_of_mem_nhds, sdiff_eq, sdiff_sdiff_cancel_left, sdiff_subset, singleton_subset_iff, subset, subset_interior_iff_isOpen, subseteq
-/
theorem isOpen_singleton_of_finite_mem_nhds [T1Space X] (x : X)
    {s : Set X} (hs : s in 𝓝 x) (hsf : s.Finite) : IsOpen ({x} : Set X) := by
  have A : {x} subseteq s := by simp only [singleton_subset_iff, mem_of_mem_nhds hs]
  have B : IsClosed (s \ {x}) := (hsf.subset sdiff_subset).isClosed
  have C : (s \ {x})ᶜ in 𝓝 x := B.isOpen_compl.mem_nhds fun h => h.2 rfl
  have D : {x} in 𝓝 x := by simpa only [← sdiff_eq, sdiff_sdiff_cancel_left A] using inter_mem hs C
  rwa [← mem_interior_iff_mem_nhds, ← singleton_subset_iff, subset_interior_iff_isOpen] at D

/--
theorem `infinite_of_mem_nhds` / 定理 `infinite_of_mem_nhds`

English:
theorem infinite_of_mem_nhds
  statement: {X} [TopologicalSpace X] [T1Space X] (x : X) [hx : NeBot (𝓝[!=] x)]
  proof: by
  refine fun hsf => hx.1 ?_
  rw [← isOpen_singleton_iff_punctured_nhds]
  exact isOpen_singleton_of_finite_mem_nhds x hs hsf

中文:
定理 infinite_of_mem_nhds
  结论: {X} [TopologicalSpace X] [T1Space X] (x : X) [hx : NeBot (𝓝[!=] x)]
  证明: by
  refine fun hsf => hx.1 ?_
  rw [← isOpen_singleton_iff_punctured_nhds]
  exact isOpen_singleton_of_finite_mem_nhds x hs hsf

Depends on / 依赖: isOpen_singleton_iff_punctured_nhds, isOpen_singleton_of_finite_mem_nhds
-/
theorem infinite_of_mem_nhds {X} [TopologicalSpace X] [T1Space X] (x : X) [hx : NeBot (𝓝[!=] x)]
    {s : Set X} (hs : s in 𝓝 x) : Set.Infinite s := by
  refine fun hsf => hx.1 ?_
  rw [← isOpen_singleton_iff_punctured_nhds]
  exact isOpen_singleton_of_finite_mem_nhds x hs hsf

instance (priority := low) [DiscreteTopology X] : T1Space X where t1 _ := isClosed_discrete _

/--
Instance `Finite.instDiscreteTopology` / 实例 `Finite.instDiscreteTopology`

English:
instance Finite.instDiscreteTopology
  signature: [T1Space X] [Finite X]
  body: discreteTopology_iff_forall_isClosed.mpr (·.toFinite.isClosed)

中文:
实例 Finite.instDiscreteTopology
  签名: [T1Space X] [Finite X]
  定义体: discreteTopology_iff_forall_isClosed.mpr (·.toFinite.isClosed)

Depends on / 依赖: discreteTopology_iff_forall_isClosed, discreteTopology_iff_forall_isClosed.mpr, isClosed, toFinite, toFinite.isClosed
-/
instance Finite.instDiscreteTopology [T1Space X] [Finite X] : DiscreteTopology X :=
  discreteTopology_iff_forall_isClosed.mpr (·.toFinite.isClosed)

/--
lemma `Set.Finite.isDiscrete` / 引理 `Set.Finite.isDiscrete`

English:
lemma Set.Finite.isDiscrete
  given: [T1Space X] {s : Set X} (hs : s.Finite)
  statement: IsDiscrete s
  proof: ⟨@Finite.instDiscreteTopology _ _ _ hs.to_subtype⟩

中文:
引理 Set.Finite.isDiscrete
  条件: [T1Space X] {s : Set X} (hs : s.Finite)
  结论: IsDiscrete s
  证明: ⟨@Finite.instDiscreteTopology _ _ _ hs.to_subtype⟩

Depends on / 依赖: Finite, Finite.instDiscreteTopology, hs.to_subtype, instDiscreteTopology, to_subtype
-/
lemma Set.Finite.isDiscrete [T1Space X] {s : Set X} (hs : s.Finite) : IsDiscrete s :=
  ⟨@Finite.instDiscreteTopology _ _ _ hs.to_subtype⟩

/--
theorem `Set.Finite.continuousOn` / 定理 `Set.Finite.continuousOn`

English:
theorem Set.Finite.continuousOn
  statement: [T1Space X] [TopologicalSpace Y] {s : Set X} (hs : s.Finite)
  proof: by
  rw [continuousOn_iff_continuous_domRestrict]
  have : Finite s := hs
  fun_prop

中文:
定理 Set.Finite.continuousOn
  结论: [T1Space X] [TopologicalSpace Y] {s : Set X} (hs : s.Finite)
  证明: by
  rw [continuousOn_iff_continuous_domRestrict]
  have : Finite s := hs
  fun_prop

Depends on / 依赖: Finite, continuousOn_iff_continuous_domRestrict, fun_prop
-/
theorem Set.Finite.continuousOn [T1Space X] [TopologicalSpace Y] {s : Set X} (hs : s.Finite)
    (f : X -> Y) : ContinuousOn f s := by
  rw [continuousOn_iff_continuous_domRestrict]
  have : Finite s := hs
  fun_prop

/--
theorem `SeparationQuotient.t1Space_iff` / 定理 `SeparationQuotient.t1Space_iff`

English:
theorem SeparationQuotient.t1Space_iff
  statement: T1Space (SeparationQuotient X) ↔ R0Space X
  proof: by
  rw [r0Space_iff]; rw [((t1Space_TFAE (SeparationQuotient X)).out 0 9 :)]
  refine ⟨fun h => ⟨fun x y xspecy => ?_⟩, ?_⟩
  · rw [← IsInducing.specializes_iff isInducing_mk, h xspecy] at *
  · -- TODO is there are better way to do this,
    -- so the case split produces `SeparationQuotient.mk` di

中文:
定理 SeparationQuotient.t1Space_iff
  结论: T1Space (SeparationQuotient X) ↔ R0Space X
  证明: by
  rw [r0Space_iff]; rw [((t1Space_TFAE (SeparationQuotient X)).out 0 9 :)]
  refine ⟨fun h => ⟨fun x y xspecy => ?_⟩, ?_⟩
  · rw [← IsInducing.specializes_iff isInducing_mk, h xspecy] at *
  · -- TODO is there are better way to do this,
    -- so the case split produces `SeparationQuotient.mk` di

Depends on / 依赖: IsInducing, IsInducing.specializes_iff, SeparationQuotient, better, isInducing_mk, r0Space_iff, specializes_iff, t1Space_TFAE, xspecy
-/
theorem SeparationQuotient.t1Space_iff : T1Space (SeparationQuotient X) ↔ R0Space X := by
  rw [r0Space_iff]; rw [((t1Space_TFAE (SeparationQuotient X)).out 0 9 :)]
  refine ⟨fun h => ⟨fun x y xspecy => ?_⟩, ?_⟩
  · rw [← IsInducing.specializes_iff isInducing_mk, h xspecy] at *
  · -- TODO is there are better way to do this,
    -- so the case split produces `SeparationQuotient.mk` directly, rather than `Quot.mk`?
    -- Currently we need the `change` statement to recover this.
    rintro h ⟨x⟩ ⟨y⟩ sxspecsy
    change mk _ = mk _
    have xspecy : x ⤳ y := isInducing_mk.specializes_iff.mp sxspecsy
    have yspecx : y ⤳ x := h.symm x y xspecy
    rw [mk_eq_mk]; rw [inseparable_iff_specializes_and]
    exact ⟨xspecy, yspecx⟩

/--
lemma `isClosed_inter_singleton` / 引理 `isClosed_inter_singleton`

English:
lemma isClosed_inter_singleton
  given: [T1Space X] {A : Set X} {a : X}
  statement: IsClosed (A inter {a})
  proof: Subsingleton.inter_singleton.isClosed

中文:
引理 isClosed_inter_singleton
  条件: [T1Space X] {A : Set X} {a : X}
  结论: IsClosed (A inter {a})
  证明: Subsingleton.inter_singleton.isClosed

Depends on / 依赖: Subsingleton, Subsingleton.inter_singleton.isClosed, inter_singleton, isClosed
-/
lemma isClosed_inter_singleton [T1Space X] {A : Set X} {a : X} : IsClosed (A inter {a}) :=
  Subsingleton.inter_singleton.isClosed

/--
lemma `isClosed_singleton_inter` / 引理 `isClosed_singleton_inter`

English:
lemma isClosed_singleton_inter
  given: [T1Space X] {A : Set X} {a : X}
  statement: IsClosed ({a} inter A)
  proof: Subsingleton.singleton_inter.isClosed

中文:
引理 isClosed_singleton_inter
  条件: [T1Space X] {A : Set X} {a : X}
  结论: IsClosed ({a} inter A)
  证明: Subsingleton.singleton_inter.isClosed

Depends on / 依赖: Subsingleton, Subsingleton.singleton_inter.isClosed, isClosed, singleton_inter
-/
lemma isClosed_singleton_inter [T1Space X] {A : Set X} {a : X} : IsClosed ({a} inter A) :=
  Subsingleton.singleton_inter.isClosed

/--
theorem `singleton_mem_nhdsWithin_of_mem_discrete` / 定理 `singleton_mem_nhdsWithin_of_mem_discrete`

English:
theorem singleton_mem_nhdsWithin_of_mem_discrete
  statement: {s : Set X} (hs : IsDiscrete s) {x : X}
  proof: by
  rw [isDiscrete_iff_discreteTopology] at hs
  have : ({⟨x, hx⟩} : Set s) in 𝓝 (⟨x, hx⟩ : s) := by simp [nhds_discrete]
  simpa only [nhdsWithin_eq_map_subtype_coe hx, image_singleton] using
    @image_mem_map _ _ _ ((↑) : s -> X) _ this

中文:
定理 singleton_mem_nhdsWithin_of_mem_discrete
  结论: {s : Set X} (hs : IsDiscrete s) {x : X}
  证明: by
  rw [isDiscrete_iff_discreteTopology] at hs
  have : ({⟨x, hx⟩} : Set s) in 𝓝 (⟨x, hx⟩ : s) := by simp [nhds_discrete]
  simpa only [nhdsWithin_eq_map_subtype_coe hx, image_singleton] using
    @image_mem_map _ _ _ ((↑) : s -> X) _ this

Depends on / 依赖: image_mem_map, image_singleton, isDiscrete_iff_discreteTopology, nhdsWithin_eq_map_subtype_coe, nhds_discrete
-/
theorem singleton_mem_nhdsWithin_of_mem_discrete {s : Set X} (hs : IsDiscrete s) {x : X}
    (hx : x in s) : {x} in 𝓝[s] x := by
  rw [isDiscrete_iff_discreteTopology] at hs
  have : ({⟨x, hx⟩} : Set s) in 𝓝 (⟨x, hx⟩ : s) := by simp [nhds_discrete]
  simpa only [nhdsWithin_eq_map_subtype_coe hx, image_singleton] using
    @image_mem_map _ _ _ ((↑) : s -> X) _ this

/--
theorem `nhdsWithin_of_mem_discrete` / 定理 `nhdsWithin_of_mem_discrete`

English:
theorem nhdsWithin_of_mem_discrete
  given: {s : Set X} (hs : IsDiscrete s) {x : X} (hx : x in s)
  proof: (le_pure_iff.2 <| singleton_mem_nhdsWithin_of_mem_discrete hs hx).antisymm (pure_le_nhdsWithin hx)

中文:
定理 nhdsWithin_of_mem_discrete
  条件: {s : Set X} (hs : IsDiscrete s) {x : X} (hx : x in s)
  证明: (le_pure_iff.2 <| singleton_mem_nhdsWithin_of_mem_discrete hs hx).antisymm (pure_le_nhdsWithin hx)

Depends on / 依赖: antisymm, le_pure_iff, pure_le_nhdsWithin, singleton_mem_nhdsWithin_of_mem_discrete
-/
theorem nhdsWithin_of_mem_discrete {s : Set X} (hs : IsDiscrete s) {x : X} (hx : x in s) :
    𝓝[s] x = pure x :=
  (le_pure_iff.2 <| singleton_mem_nhdsWithin_of_mem_discrete hs hx).antisymm (pure_le_nhdsWithin hx)

/--
theorem `Filter.HasBasis.exists_inter_eq_singleton_of_mem_discrete` / 定理 `Filter.HasBasis.exists_inter_eq_singleton_of_mem_discrete`

English:
theorem Filter.HasBasis.exists_inter_eq_singleton_of_mem_discrete
  statement: {ι : Type*} {p : ι -> Prop}
  proof: by
  rcases (nhdsWithin_hasBasis hb s).mem_iff.1 (singleton_mem_nhdsWithin_of_mem_discrete hs hx) with
    ⟨i, hi, hix⟩
exact ⟨i, hi, hix.antisymm singleton_subset_iff.2 ⟨mem_of_mem_nhds hb.mem_of_mem hi, hx⟩⟩

中文:
定理 Filter.HasBasis.exists_inter_eq_singleton_of_mem_discrete
  结论: {ι : 类型} {p : ι -> 命题}
  证明: by
  rcases (nhdsWithin_hasBasis hb s).mem_iff.1 (singleton_mem_nhdsWithin_of_mem_discrete hs hx) with
    ⟨i, hi, hix⟩
exact ⟨i, hi, hix.antisymm singleton_subset_iff.2 ⟨mem_of_mem_nhds hb.mem_of_mem hi, hx⟩⟩

Depends on / 依赖: antisymm, hb.mem_of_mem, hix.antisymm, mem_iff, mem_of_mem, mem_of_mem_nhds, nhdsWithin_hasBasis, singleton_mem_nhdsWithin_of_mem_discrete, singleton_subset_iff
-/
theorem Filter.HasBasis.exists_inter_eq_singleton_of_mem_discrete {ι : Type*} {p : ι -> Prop}
    {t : ι -> Set X} {s : Set X} (hs : IsDiscrete s) {x : X} (hb : (𝓝 x).HasBasis p t)
    (hx : x in s) : exists i, p i ∧ t i inter s = {x} := by
  rcases (nhdsWithin_hasBasis hb s).mem_iff.1 (singleton_mem_nhdsWithin_of_mem_discrete hs hx) with
    ⟨i, hi, hix⟩
exact ⟨i, hi, hix.antisymm singleton_subset_iff.2 ⟨mem_of_mem_nhds hb.mem_of_mem hi, hx⟩⟩

/--
theorem `nhds_inter_eq_singleton_of_mem_discrete` / 定理 `nhds_inter_eq_singleton_of_mem_discrete`

English:
theorem nhds_inter_eq_singleton_of_mem_discrete
  statement: {s : Set X} (hs : IsDiscrete s) {x : X}
  proof: by
  simpa using (𝓝 x).basis_sets.exists_inter_eq_singleton_of_mem_discrete hs hx

中文:
定理 nhds_inter_eq_singleton_of_mem_discrete
  结论: {s : Set X} (hs : IsDiscrete s) {x : X}
  证明: by
  simpa using (𝓝 x).basis_sets.exists_inter_eq_singleton_of_mem_discrete hs hx

Depends on / 依赖: basis_sets, basis_sets.exists_inter_eq_singleton_of_mem_discrete, exists_inter_eq_singleton_of_mem_discrete
-/
theorem nhds_inter_eq_singleton_of_mem_discrete {s : Set X} (hs : IsDiscrete s) {x : X}
    (hx : x in s) : exists U in 𝓝 x, U inter s = {x} := by
  simpa using (𝓝 x).basis_sets.exists_inter_eq_singleton_of_mem_discrete hs hx

/--
theorem `isOpen_inter_eq_singleton_of_mem_discrete` / 定理 `isOpen_inter_eq_singleton_of_mem_discrete`

English:
theorem isOpen_inter_eq_singleton_of_mem_discrete
  statement: {s : Set X} (hs : IsDiscrete s) {x : X}
  proof: by
  obtain ⟨U, hU_nhds, hU_inter⟩ := nhds_inter_eq_singleton_of_mem_discrete hs hx
  obtain ⟨t, ht_sub, ht_open, ht_x⟩ := mem_nhds_iff.mp hU_nhds
  grind

中文:
定理 isOpen_inter_eq_singleton_of_mem_discrete
  结论: {s : Set X} (hs : IsDiscrete s) {x : X}
  证明: by
  obtain ⟨U, hU_nhds, hU_inter⟩ := nhds_inter_eq_singleton_of_mem_discrete hs hx
  obtain ⟨t, ht_sub, ht_open, ht_x⟩ := mem_nhds_iff.mp hU_nhds
  grind

Depends on / 依赖: hU_inter, hU_nhds, ht_open, ht_sub, ht_x, mem_nhds_iff, mem_nhds_iff.mp, nhds_inter_eq_singleton_of_mem_discrete
-/
theorem isOpen_inter_eq_singleton_of_mem_discrete {s : Set X} (hs : IsDiscrete s) {x : X}
    (hx : x in s) : exists U : Set X, IsOpen U ∧ U inter s = {x} := by
  obtain ⟨U, hU_nhds, hU_inter⟩ := nhds_inter_eq_singleton_of_mem_discrete hs hx
  obtain ⟨t, ht_sub, ht_open, ht_x⟩ := mem_nhds_iff.mp hU_nhds
  grind

/--
theorem `disjoint_nhdsWithin_of_mem_discrete` / 定理 `disjoint_nhdsWithin_of_mem_discrete`

English:
theorem disjoint_nhdsWithin_of_mem_discrete
  given: {s : Set X} (hs : IsDiscrete s) {x : X} (hx : x in s)
  proof: let ⟨V, h, h'⟩ := nhds_inter_eq_singleton_of_mem_discrete hs hx
  ⟨{x}ᶜ inter V, inter_mem_nhdsWithin _ h,
    disjoint_iff_inter_eq_empty.mpr (by rw [inter_assoc, h', compl_inter_self])⟩

中文:
定理 disjoint_nhdsWithin_of_mem_discrete
  条件: {s : Set X} (hs : IsDiscrete s) {x : X} (hx : x in s)
  证明: let ⟨V, h, h'⟩ := nhds_inter_eq_singleton_of_mem_discrete hs hx
  ⟨{x}ᶜ inter V, inter_mem_nhdsWithin _ h,
    disjoint_iff_inter_eq_empty.mpr (by rw [inter_assoc, h', compl_inter_self])⟩

Depends on / 依赖: compl_inter_self, disjoint_iff_inter_eq_empty, disjoint_iff_inter_eq_empty.mpr, inter_assoc, inter_mem_nhdsWithin, nhds_inter_eq_singleton_of_mem_discrete
-/
theorem disjoint_nhdsWithin_of_mem_discrete {s : Set X} (hs : IsDiscrete s) {x : X} (hx : x in s) :
    exists U in 𝓝[!=] x, Disjoint U s :=
  let ⟨V, h, h'⟩ := nhds_inter_eq_singleton_of_mem_discrete hs hx
  ⟨{x}ᶜ inter V, inter_mem_nhdsWithin _ h,
    disjoint_iff_inter_eq_empty.mpr (by rw [inter_assoc, h', compl_inter_self])⟩

/--
theorem `isClosedEmbedding_update` / 定理 `isClosedEmbedding_update`

English:
theorem isClosedEmbedding_update
  statement: {ι : Type*} {β : ι -> Type*}
  proof: by
  refine .of_continuous_injective_isClosedMap (continuous_const.update i continuous_id)
    (update_injective x i) fun s hs => ?_
  rw [update_image]
  apply isClosed_set_pi
  simp [forall_update_iff, hs]

中文:
定理 isClosedEmbedding_update
  结论: {ι : 类型} {β : ι -> 类型}
  证明: by
  refine .of_continuous_injective_isClosedMap (continuous_const.update i continuous_id)
    (update_injective x i) fun s hs => ?_
  rw [update_image]
  apply isClosed_set_pi
  simp [forall_update_iff, hs]

Depends on / 依赖: continuous_const, continuous_const.update, continuous_id, forall_update_iff, isClosed_set_pi, of_continuous_injective_isClosedMap, update, update_image, update_injective
-/
theorem isClosedEmbedding_update {ι : Type*} {β : ι -> Type*}
    [DecidableEq ι] [(i : ι) -> TopologicalSpace (β i)]
    (x : (i : ι) -> β i) (i : ι) [(i : ι) -> T1Space (β i)] :
    IsClosedEmbedding (update x i) := by
  refine .of_continuous_injective_isClosedMap (continuous_const.update i continuous_id)
    (update_injective x i) fun s hs => ?_
  rw [update_image]
  apply isClosed_set_pi
  simp [forall_update_iff, hs]

/--
lemma `nhdsNE_le_cofinite` / 引理 `nhdsNE_le_cofinite`

English:
lemma nhdsNE_le_cofinite
  given: {α : Type*} [TopologicalSpace α] [T1Space α] (a : α)
  proof: by
  refine le_cofinite_iff_compl_singleton_mem.mpr fun x => ?_
  rcases eq_or_ne a x with rfl | hx
  exacts [self_mem_nhdsWithin, eventually_ne_nhdsWithin hx]

中文:
引理 nhdsNE_le_cofinite
  条件: {α : 类型} [TopologicalSpace α] [T1Space α] (a : α)
  证明: by
  refine le_cofinite_iff_compl_singleton_mem.mpr fun x => ?_
  rcases eq_or_ne a x with rfl | hx
  exacts [self_mem_nhdsWithin, eventually_ne_nhdsWithin hx]

Depends on / 依赖: eq_or_ne, eventually_ne_nhdsWithin, exacts, le_cofinite_iff_compl_singleton_mem, le_cofinite_iff_compl_singleton_mem.mpr, self_mem_nhdsWithin
-/
lemma nhdsNE_le_cofinite {α : Type*} [TopologicalSpace α] [T1Space α] (a : α) :
    𝓝[!=] a <= cofinite := by
  refine le_cofinite_iff_compl_singleton_mem.mpr fun x => ?_
  rcases eq_or_ne a x with rfl | hx
  exacts [self_mem_nhdsWithin, eventually_ne_nhdsWithin hx]

/--
lemma `Function.update_eventuallyEq_nhdsNE` / 引理 `Function.update_eventuallyEq_nhdsNE`

English:
lemma Function.update_eventuallyEq_nhdsNE
  proof: (Function.update_eventuallyEq_cofinite f a b).filter_mono (nhdsNE_le_cofinite a')

中文:
引理 Function.update_eventuallyEq_nhdsNE
  证明: (Function.update_eventuallyEq_cofinite f a b).filter_mono (nhdsNE_le_cofinite a')

Depends on / 依赖: Function, Function.update_eventuallyEq_cofinite, filter_mono, nhdsNE_le_cofinite, update_eventuallyEq_cofinite
-/
lemma Function.update_eventuallyEq_nhdsNE
    {α β : Type*} [TopologicalSpace α] [T1Space α] [DecidableEq α] (f : α -> β) (a a' : α) (b : β) :
    Function.update f a b =ᶠ[𝓝[!=] a'] f :=
  (Function.update_eventuallyEq_cofinite f a b).filter_mono (nhdsNE_le_cofinite a')

/-! ### R₁ (preregular) spaces -/

section R1Space

/-- A topological space is called a *preregular* (a.k.a. R₁) space,
if any two topologically distinguishable points have disjoint neighbourhoods. -/
@[mk_iff r1Space_iff_specializes_or_disjoint_nhds]
/--
Definition of `R1Space` / `R1Space` 的定义

English:
class R1Space
  parameters: (X : Type*) [TopologicalSpace X]
  axioms and operations (1):
    - specializes_or_disjoint_nhds((x y : X)) : Specializes x y ∨ Disjoint (𝓝 x) (𝓝 y)

中文:
类 R1Space
  参数: (X : 类型) [TopologicalSpace X]
  公理与运算 (1 个):
    - specializes_or_disjoint_nhds((x y : X)) : Specializes x y ∨ Disjoint (𝓝 x) (𝓝 y)
-/
class R1Space (X : Type*) [TopologicalSpace X] : Prop where
  specializes_or_disjoint_nhds (x y : X) : Specializes x y ∨ Disjoint (𝓝 x) (𝓝 y)

export R1Space (specializes_or_disjoint_nhds)

variable [R1Space X] {x y : X}

instance (priority := 100) : R0Space X where
specializes_symm.symm _ _ h := (specializes_or_disjoint_nhds _ _).resolve_right fun hd =>
    h.not_disjoint hd.symm

/--
theorem `disjoint_nhds_nhds_iff_not_specializes` / 定理 `disjoint_nhds_nhds_iff_not_specializes`

English:
theorem disjoint_nhds_nhds_iff_not_specializes
  statement: Disjoint (𝓝 x) (𝓝 y) ↔ ¬x ⤳ y
  proof: ⟨fun hd hspec => hspec.not_disjoint hd, (specializes_or_disjoint_nhds _ _).resolve_left⟩

中文:
定理 disjoint_nhds_nhds_iff_not_specializes
  结论: Disjoint (𝓝 x) (𝓝 y) ↔ ¬x ⤳ y
  证明: ⟨fun hd hspec => hspec.not_disjoint hd, (specializes_or_disjoint_nhds _ _).resolve_left⟩

Depends on / 依赖: hspec.not_disjoint, not_disjoint, resolve_left, specializes_or_disjoint_nhds
-/
theorem disjoint_nhds_nhds_iff_not_specializes : Disjoint (𝓝 x) (𝓝 y) ↔ ¬x ⤳ y :=
  ⟨fun hd hspec => hspec.not_disjoint hd, (specializes_or_disjoint_nhds _ _).resolve_left⟩

/--
theorem `specializes_iff_not_disjoint` / 定理 `specializes_iff_not_disjoint`

English:
theorem specializes_iff_not_disjoint
  statement: x ⤳ y ↔ ¬Disjoint (𝓝 x) (𝓝 y)
  proof: disjoint_nhds_nhds_iff_not_specializes.not_left.symm

中文:
定理 specializes_iff_not_disjoint
  结论: x ⤳ y ↔ ¬Disjoint (𝓝 x) (𝓝 y)
  证明: disjoint_nhds_nhds_iff_not_specializes.not_left.symm

Depends on / 依赖: disjoint_nhds_nhds_iff_not_specializes, disjoint_nhds_nhds_iff_not_specializes.not_left.symm, not_left
-/
theorem specializes_iff_not_disjoint : x ⤳ y ↔ ¬Disjoint (𝓝 x) (𝓝 y) :=
  disjoint_nhds_nhds_iff_not_specializes.not_left.symm

/--
theorem `disjoint_nhds_nhds_iff_not_inseparable` / 定理 `disjoint_nhds_nhds_iff_not_inseparable`

English:
theorem disjoint_nhds_nhds_iff_not_inseparable
  statement: Disjoint (𝓝 x) (𝓝 y) ↔ ¬Inseparable x y
  proof: by
  rw [disjoint_nhds_nhds_iff_not_specializes]; rw [specializes_iff_inseparable]

中文:
定理 disjoint_nhds_nhds_iff_not_inseparable
  结论: Disjoint (𝓝 x) (𝓝 y) ↔ ¬Inseparable x y
  证明: by
  rw [disjoint_nhds_nhds_iff_not_specializes]; rw [specializes_iff_inseparable]

Depends on / 依赖: disjoint_nhds_nhds_iff_not_specializes, specializes_iff_inseparable
-/
theorem disjoint_nhds_nhds_iff_not_inseparable : Disjoint (𝓝 x) (𝓝 y) ↔ ¬Inseparable x y := by
  rw [disjoint_nhds_nhds_iff_not_specializes]; rw [specializes_iff_inseparable]

/--
theorem `r1Space_iff_inseparable_or_disjoint_nhds` / 定理 `r1Space_iff_inseparable_or_disjoint_nhds`

English:
theorem r1Space_iff_inseparable_or_disjoint_nhds
  given: {X : Type*} [TopologicalSpace X]
  proof: ⟨fun _h x y => (specializes_or_disjoint_nhds x y).imp_left Specializes.inseparable, fun h =>
    ⟨fun x y => (h x y).imp_left Inseparable.specializes⟩⟩

中文:
定理 r1Space_iff_inseparable_or_disjoint_nhds
  条件: {X : 类型} [TopologicalSpace X]
  证明: ⟨fun _h x y => (specializes_or_disjoint_nhds x y).imp_left Specializes.inseparable, fun h =>
    ⟨fun x y => (h x y).imp_left Inseparable.specializes⟩⟩

Depends on / 依赖: Inseparable, Inseparable.specializes, Specializes, Specializes.inseparable, imp_left, inseparable, specializes, specializes_or_disjoint_nhds
-/
theorem r1Space_iff_inseparable_or_disjoint_nhds {X : Type*} [TopologicalSpace X] :
    R1Space X ↔ forall x y : X, Inseparable x y ∨ Disjoint (𝓝 x) (𝓝 y) :=
  ⟨fun _h x y => (specializes_or_disjoint_nhds x y).imp_left Specializes.inseparable, fun h =>
    ⟨fun x y => (h x y).imp_left Inseparable.specializes⟩⟩

/--
theorem `Inseparable.of_nhds_neBot` / 定理 `Inseparable.of_nhds_neBot`

English:
theorem Inseparable.of_nhds_neBot
  given: {x y : X} (h : NeBot (𝓝 x ⊓ 𝓝 y))
  proof: (r1Space_iff_inseparable_or_disjoint_nhds.mp ‹_› _ _).resolve_right fun h' => h.ne h'.eq_bot

中文:
定理 Inseparable.of_nhds_neBot
  条件: {x y : X} (h : NeBot (𝓝 x ⊓ 𝓝 y))
  证明: (r1Space_iff_inseparable_or_disjoint_nhds.mp ‹_› _ _).resolve_right fun h' => h.ne h'.eq_bot

Depends on / 依赖: eq_bot, h.ne, r1Space_iff_inseparable_or_disjoint_nhds, r1Space_iff_inseparable_or_disjoint_nhds.mp, resolve_right
-/
theorem Inseparable.of_nhds_neBot {x y : X} (h : NeBot (𝓝 x ⊓ 𝓝 y)) :
    Inseparable x y :=
  (r1Space_iff_inseparable_or_disjoint_nhds.mp ‹_› _ _).resolve_right fun h' => h.ne h'.eq_bot

/--
theorem `r1_separation` / 定理 `r1_separation`

English:
theorem r1_separation
  given: {x y : X} (h : ¬Inseparable x y)
  proof: by
  rw [← disjoint_nhds_nhds_iff_not_inseparable]; rw [(nhds_basis_opens x).disjoint_iff (nhds_basis_opens y)] at h
  obtain ⟨u, ⟨hxu, hu⟩, v, ⟨hyv, hv⟩, huv⟩ := h
  exact ⟨u, v, hu, hv, hxu, hyv, huv⟩

中文:
定理 r1_separation
  条件: {x y : X} (h : ¬Inseparable x y)
  证明: by
  rw [← disjoint_nhds_nhds_iff_not_inseparable]; rw [(nhds_basis_opens x).disjoint_iff (nhds_basis_opens y)] at h
  obtain ⟨u, ⟨hxu, hu⟩, v, ⟨hyv, hv⟩, huv⟩ := h
  exact ⟨u, v, hu, hv, hxu, hyv, huv⟩

Depends on / 依赖: disjoint_iff, disjoint_nhds_nhds_iff_not_inseparable, nhds_basis_opens
-/
theorem r1_separation {x y : X} (h : ¬Inseparable x y) :
    exists u v : Set X, IsOpen u ∧ IsOpen v ∧ x in u ∧ y in v ∧ Disjoint u v := by
  rw [← disjoint_nhds_nhds_iff_not_inseparable]; rw [(nhds_basis_opens x).disjoint_iff (nhds_basis_opens y)] at h
  obtain ⟨u, ⟨hxu, hu⟩, v, ⟨hyv, hv⟩, huv⟩ := h
  exact ⟨u, v, hu, hv, hxu, hyv, huv⟩

/--
theorem `tendsto_nhds_unique_inseparable` / 定理 `tendsto_nhds_unique_inseparable`

English:
theorem tendsto_nhds_unique_inseparable
  statement: {f : Y -> X} {l : Filter Y} {a b : X} [NeBot l]
  proof: .of_nhds_neBot neBot_of_le le_inf ha hb

中文:
定理 tendsto_nhds_unique_inseparable
  结论: {f : Y -> X} {l : Filter Y} {a b : X} [NeBot l]
  证明: .of_nhds_neBot neBot_of_le le_inf ha hb

Depends on / 依赖: le_inf, neBot_of_le, of_nhds_neBot
-/
theorem tendsto_nhds_unique_inseparable {f : Y -> X} {l : Filter Y} {a b : X} [NeBot l]
    (ha : Tendsto f l (𝓝 a)) (hb : Tendsto f l (𝓝 b)) : Inseparable a b :=
.of_nhds_neBot neBot_of_le le_inf ha hb

/--
theorem `isClosed_setOfPred_specializes` / 定理 `isClosed_setOfPred_specializes`

English:
theorem isClosed_setOfPred_specializes
  statement: IsClosed { p : X × X | p.1 ⤳ p.2 }
  proof: by
  simp only [← isOpen_compl_iff, compl_ofPred, ← disjoint_nhds_nhds_iff_not_specializes,
    isOpen_setOfPred_disjoint_nhds_nhds]

@[deprecated (since := "2026-07-09")]
alias isClosed_setOf_specializes := isClosed_setOfPred_specializes

中文:
定理 isClosed_setOfPred_specializes
  结论: IsClosed { p : X × X | p.1 ⤳ p.2 }
  证明: by
  simp only [← isOpen_compl_iff, compl_ofPred, ← disjoint_nhds_nhds_iff_not_specializes,
    isOpen_setOfPred_disjoint_nhds_nhds]

@[deprecated (since := "2026-07-09")]
alias isClosed_setOf_specializes := isClosed_setOfPred_specializes

Depends on / 依赖: compl_ofPred, disjoint_nhds_nhds_iff_not_specializes, isOpen_compl_iff, isOpen_setOfPred_disjoint_nhds_nhds
-/
theorem isClosed_setOfPred_specializes : IsClosed { p : X × X | p.1 ⤳ p.2 } := by
  simp only [← isOpen_compl_iff, compl_ofPred, ← disjoint_nhds_nhds_iff_not_specializes,
    isOpen_setOfPred_disjoint_nhds_nhds]

@[deprecated (since := "2026-07-09")]
alias isClosed_setOf_specializes := isClosed_setOfPred_specializes

/--
theorem `isClosed_setOfPred_inseparable` / 定理 `isClosed_setOfPred_inseparable`

English:
theorem isClosed_setOfPred_inseparable
  statement: IsClosed { p : X × X | Inseparable p.1 p.2 }
  proof: by
  simp only [← specializes_iff_inseparable, isClosed_setOfPred_specializes]

@[deprecated (since := "2026-07-09")]
alias isClosed_setOf_inseparable := isClosed_setOfPred_inseparable

中文:
定理 isClosed_setOfPred_inseparable
  结论: IsClosed { p : X × X | Inseparable p.1 p.2 }
  证明: by
  simp only [← specializes_iff_inseparable, isClosed_setOfPred_specializes]

@[deprecated (since := "2026-07-09")]
alias isClosed_setOf_inseparable := isClosed_setOfPred_inseparable

Depends on / 依赖: isClosed_setOfPred_specializes, specializes_iff_inseparable
-/
theorem isClosed_setOfPred_inseparable : IsClosed { p : X × X | Inseparable p.1 p.2 } := by
  simp only [← specializes_iff_inseparable, isClosed_setOfPred_specializes]

@[deprecated (since := "2026-07-09")]
alias isClosed_setOf_inseparable := isClosed_setOfPred_inseparable

/--
theorem `IsCompact.mem_closure_iff_exists_inseparable` / 定理 `IsCompact.mem_closure_iff_exists_inseparable`

English:
theorem IsCompact.mem_closure_iff_exists_inseparable
  given: {K : Set X} (hK : IsCompact K)
  proof: by
  refine ⟨fun hy => ?_, fun ⟨x, hxK, hxy⟩ =>
(hxy.mem_closed_iff isClosed_closure).1 subset_closure hxK⟩
  contrapose! hy
  have : Disjoint (𝓝 y) (𝓝ˢ K) := hK.disjoint_nhdsSet_right.2 fun x hx =>
    (disjoint_nhds_nhds_iff_not_inseparable.2 (hy x hx)).symm
  simpa only [disjoint_iff, notMem_clos

中文:
定理 IsCompact.mem_closure_iff_exists_inseparable
  条件: {K : Set X} (hK : IsCompact K)
  证明: by
  refine ⟨fun hy => ?_, fun ⟨x, hxK, hxy⟩ =>
(hxy.mem_closed_iff isClosed_closure).1 subset_closure hxK⟩
  contrapose! hy
  have : Disjoint (𝓝 y) (𝓝ˢ K) := hK.disjoint_nhdsSet_right.2 fun x hx =>
    (disjoint_nhds_nhds_iff_not_inseparable.2 (hy x hx)).symm
  simpa only [disjoint_iff, notMem_clos

Depends on / 依赖: Disjoint, contrapose, disjoint_iff, disjoint_nhdsSet_right, disjoint_nhds_nhds_iff_not_inseparable, hK.disjoint_nhdsSet_right, hxy.mem_closed_iff, isClosed_closure, mem_closed_iff, mono_right, notMem_closure_iff_nhdsWithin_eq_bot, principal_le_nhdsSet, subset_closure, this.mono_right
-/
theorem IsCompact.mem_closure_iff_exists_inseparable {K : Set X} (hK : IsCompact K) :
    y in closure K ↔ exists x in K, Inseparable x y := by
  refine ⟨fun hy => ?_, fun ⟨x, hxK, hxy⟩ =>
(hxy.mem_closed_iff isClosed_closure).1 subset_closure hxK⟩
  contrapose! hy
  have : Disjoint (𝓝 y) (𝓝ˢ K) := hK.disjoint_nhdsSet_right.2 fun x hx =>
    (disjoint_nhds_nhds_iff_not_inseparable.2 (hy x hx)).symm
  simpa only [disjoint_iff, notMem_closure_iff_nhdsWithin_eq_bot]
    using! this.mono_right principal_le_nhdsSet

/--
theorem `IsCompact.closure_eq_biUnion_inseparable` / 定理 `IsCompact.closure_eq_biUnion_inseparable`

English:
theorem IsCompact.closure_eq_biUnion_inseparable
  given: {K : Set X} (hK : IsCompact K)
  proof: by
  ext; simp [hK.mem_closure_iff_exists_inseparable]

中文:
定理 IsCompact.closure_eq_biUnion_inseparable
  条件: {K : Set X} (hK : IsCompact K)
  证明: by
  ext; simp [hK.mem_closure_iff_exists_inseparable]

Depends on / 依赖: hK.mem_closure_iff_exists_inseparable, mem_closure_iff_exists_inseparable
-/
theorem IsCompact.closure_eq_biUnion_inseparable {K : Set X} (hK : IsCompact K) :
    closure K = ⋃ x in K, {y | Inseparable x y} := by
  ext; simp [hK.mem_closure_iff_exists_inseparable]

/--
theorem `IsCompact.closure_eq_biUnion_closure_singleton` / 定理 `IsCompact.closure_eq_biUnion_closure_singleton`

English:
theorem IsCompact.closure_eq_biUnion_closure_singleton
  given: {K : Set X} (hK : IsCompact K)
  proof: by
  simp only [hK.closure_eq_biUnion_inseparable, ← specializes_iff_inseparable,
    specializes_iff_mem_closure, ofPred_mem_eq]

中文:
定理 IsCompact.closure_eq_biUnion_closure_singleton
  条件: {K : Set X} (hK : IsCompact K)
  证明: by
  simp only [hK.closure_eq_biUnion_inseparable, ← specializes_iff_inseparable,
    specializes_iff_mem_closure, ofPred_mem_eq]

Depends on / 依赖: closure_eq_biUnion_inseparable, hK.closure_eq_biUnion_inseparable, ofPred_mem_eq, specializes_iff_inseparable, specializes_iff_mem_closure
-/
theorem IsCompact.closure_eq_biUnion_closure_singleton {K : Set X} (hK : IsCompact K) :
    closure K = ⋃ x in K, closure {x} := by
  simp only [hK.closure_eq_biUnion_inseparable, ← specializes_iff_inseparable,
    specializes_iff_mem_closure, ofPred_mem_eq]

/--
theorem `IsCompact.closure_subset_of_isOpen` / 定理 `IsCompact.closure_subset_of_isOpen`

English:
theorem IsCompact.closure_subset_of_isOpen
  statement: {K : Set X} (hK : IsCompact K)
  proof: by
  rw [hK.closure_eq_biUnion_inseparable]; rw [iUnion₂_subset_iff]
  exact fun x hx y hxy => (hxy.mem_open_iff hU).1 (hKU hx)

中文:
定理 IsCompact.closure_subset_of_isOpen
  结论: {K : Set X} (hK : IsCompact K)
  证明: by
  rw [hK.closure_eq_biUnion_inseparable]; rw [iUnion₂_subset_iff]
  exact fun x hx y hxy => (hxy.mem_open_iff hU).1 (hKU hx)

Depends on / 依赖: closure_eq_biUnion_inseparable, hK.closure_eq_biUnion_inseparable, hxy.mem_open_iff, mem_open_iff
-/
theorem IsCompact.closure_subset_of_isOpen {K : Set X} (hK : IsCompact K)
    {U : Set X} (hU : IsOpen U) (hKU : K subseteq U) : closure K subseteq U := by
  rw [hK.closure_eq_biUnion_inseparable]; rw [iUnion₂_subset_iff]
  exact fun x hx y hxy => (hxy.mem_open_iff hU).1 (hKU hx)

/--
theorem `IsCompact.closure` / 定理 `IsCompact.closure`

English:
theorem IsCompact.closure
  given: {K : Set X} (hK : IsCompact K)
  statement: IsCompact (closure K)
  proof: by
  refine isCompact_of_finite_subcover fun U hUo hKU => ?_
  rcases hK.elim_finite_subcover U hUo (subset_closure.trans hKU) with ⟨t, ht⟩
  exact ⟨t, hK.closure_subset_of_isOpen (isOpen_biUnion fun _ _ => hUo _) ht⟩

中文:
定理 IsCompact.closure
  条件: {K : Set X} (hK : IsCompact K)
  结论: IsCompact (closure K)
  证明: by
  refine isCompact_of_finite_subcover fun U hUo hKU => ?_
  rcases hK.elim_finite_subcover U hUo (subset_closure.trans hKU) with ⟨t, ht⟩
  exact ⟨t, hK.closure_subset_of_isOpen (isOpen_biUnion fun _ _ => hUo _) ht⟩
-/
protected theorem IsCompact.closure {K : Set X} (hK : IsCompact K) : IsCompact (closure K) := by
  refine isCompact_of_finite_subcover fun U hUo hKU => ?_
  rcases hK.elim_finite_subcover U hUo (subset_closure.trans hKU) with ⟨t, ht⟩
  exact ⟨t, hK.closure_subset_of_isOpen (isOpen_biUnion fun _ _ => hUo _) ht⟩

/--
theorem `IsCompact.closure_of_subset` / 定理 `IsCompact.closure_of_subset`

English:
theorem IsCompact.closure_of_subset
  given: {s K : Set X} (hK : IsCompact K) (h : s subseteq K)
  proof: hK.closure.of_isClosed_subset isClosed_closure (closure_mono h)

@[simp]

中文:
定理 IsCompact.closure_of_subset
  条件: {s K : Set X} (hK : IsCompact K) (h : s subseteq K)
  证明: hK.closure.of_isClosed_subset isClosed_closure (closure_mono h)

@[simp]

Depends on / 依赖: closure, closure_mono, hK.closure.of_isClosed_subset, isClosed_closure, of_isClosed_subset
-/
theorem IsCompact.closure_of_subset {s K : Set X} (hK : IsCompact K) (h : s subseteq K) :
    IsCompact (closure s) :=
  hK.closure.of_isClosed_subset isClosed_closure (closure_mono h)

@[simp]
/--
theorem `exists_isCompact_superset_iff` / 定理 `exists_isCompact_superset_iff`

English:
theorem exists_isCompact_superset_iff
  given: {s : Set X}
  proof: ⟨fun ⟨_K, hK, hsK⟩ => hK.closure_of_subset hsK, fun h => ⟨closure s, h, subset_closure⟩⟩

中文:
定理 exists_isCompact_superset_iff
  条件: {s : Set X}
  证明: ⟨fun ⟨_K, hK, hsK⟩ => hK.closure_of_subset hsK, fun h => ⟨closure s, h, subset_closure⟩⟩

Depends on / 依赖: closure, closure_of_subset, hK.closure_of_subset, subset_closure
-/
theorem exists_isCompact_superset_iff {s : Set X} :
    (exists K, IsCompact K ∧ s subseteq K) ↔ IsCompact (closure s) :=
  ⟨fun ⟨_K, hK, hsK⟩ => hK.closure_of_subset hsK, fun h => ⟨closure s, h, subset_closure⟩⟩

/--
theorem `SeparatedNhds.of_isCompact_isCompact_isClosed` / 定理 `SeparatedNhds.of_isCompact_isCompact_isClosed`

English:
theorem SeparatedNhds.of_isCompact_isCompact_isClosed
  statement: {K L : Set X} (hK : IsCompact K)
  proof: by
  simp_rw [separatedNhds_iff_disjoint, hK.disjoint_nhdsSet_left, hL.disjoint_nhdsSet_right,
    disjoint_nhds_nhds_iff_not_inseparable]
  intro x hx y hy h
exact absurd ((h.mem_closed_iff h'L).2 hy) disjoint_left.1 hd hx

中文:
定理 SeparatedNhds.of_isCompact_isCompact_isClosed
  结论: {K L : Set X} (hK : IsCompact K)
  证明: by
  simp_rw [separatedNhds_iff_disjoint, hK.disjoint_nhdsSet_left, hL.disjoint_nhdsSet_right,
    disjoint_nhds_nhds_iff_not_inseparable]
  intro x hx y hy h
exact absurd ((h.mem_closed_iff h'L).2 hy) disjoint_left.1 hd hx

Depends on / 依赖: absurd, disjoint_left, disjoint_nhdsSet_left, disjoint_nhdsSet_right, disjoint_nhds_nhds_iff_not_inseparable, h.mem_closed_iff, hK.disjoint_nhdsSet_left, hL.disjoint_nhdsSet_right, mem_closed_iff, separatedNhds_iff_disjoint, simp_rw
-/
theorem SeparatedNhds.of_isCompact_isCompact_isClosed {K L : Set X} (hK : IsCompact K)
    (hL : IsCompact L) (h'L : IsClosed L) (hd : Disjoint K L) : SeparatedNhds K L := by
  simp_rw [separatedNhds_iff_disjoint, hK.disjoint_nhdsSet_left, hL.disjoint_nhdsSet_right,
    disjoint_nhds_nhds_iff_not_inseparable]
  intro x hx y hy h
exact absurd ((h.mem_closed_iff h'L).2 hy) disjoint_left.1 hd hx

/--
theorem `IsCompact.binary_compact_cover` / 定理 `IsCompact.binary_compact_cover`

English:
theorem IsCompact.binary_compact_cover
  statement: {K U V : Set X}
  proof: by
  have hK' : IsCompact (closure K) := hK.closure
  have : SeparatedNhds (closure K \ U) (closure K \ V) := by
    apply SeparatedNhds.of_isCompact_isCompact_isClosed (hK'.diff hU) (hK'.diff hV)
      (isClosed_closure.sdiff hV)
    rw [disjoint_iff_inter_eq_empty]; rw [sdiff_inter_sdiff]; rw [sdi

中文:
定理 IsCompact.binary_compact_cover
  结论: {K U V : Set X}
  证明: by
  have hK' : IsCompact (closure K) := hK.closure
  have : SeparatedNhds (closure K \ U) (closure K \ V) := by
    apply SeparatedNhds.of_isCompact_isCompact_isClosed (hK'.diff hU) (hK'.diff hV)
      (isClosed_closure.sdiff hV)
    rw [disjoint_iff_inter_eq_empty]; rw [sdiff_inter_sdiff]; rw [sdi

Depends on / 依赖: IsCompact, SeparatedNhds, SeparatedNhds.of_isCompact_isCompact_isClosed, closure, closure_subset_of_isOpen, disjoint_iff_inter_eq_empty, hK.closure, hK.closure_subset_of_isOpen, hU.union, isClosed_closure, isClosed_closure.sdiff, of_isCompact_isCompact_isClosed, sdiff_eq_empty, sdiff_inter_sdiff, sdiff_subset_sdiff_left, subset_closure, this.mono
-/
theorem IsCompact.binary_compact_cover {K U V : Set X}
    (hK : IsCompact K) (hU : IsOpen U) (hV : IsOpen V) (h2K : K subseteq U union V) :
    exists K₁ K₂ : Set X, IsCompact K₁ ∧ IsCompact K₂ ∧ K₁ subseteq U ∧ K₂ subseteq V ∧ K = K₁ union K₂ := by
  have hK' : IsCompact (closure K) := hK.closure
  have : SeparatedNhds (closure K \ U) (closure K \ V) := by
    apply SeparatedNhds.of_isCompact_isCompact_isClosed (hK'.diff hU) (hK'.diff hV)
      (isClosed_closure.sdiff hV)
    rw [disjoint_iff_inter_eq_empty]; rw [sdiff_inter_sdiff]; rw [sdiff_eq_empty]
    exact hK.closure_subset_of_isOpen (hU.union hV) h2K
  have : SeparatedNhds (K \ U) (K \ V) :=
    this.mono (sdiff_subset_sdiff_left (subset_closure)) (sdiff_subset_sdiff_left (subset_closure))
  rcases this with ⟨O₁, O₂, h1O₁, h1O₂, h2O₁, h2O₂, hO⟩
  exact ⟨K \ O₁, K \ O₂, hK.diff h1O₁, hK.diff h1O₂, sdiff_subset_comm.mp h2O₁,
    sdiff_subset_comm.mp h2O₂, by rw [← sdiff_inter, hO.inter_eq, sdiff_empty]⟩

/--
theorem `IsCompact.finite_compact_cover` / 定理 `IsCompact.finite_compact_cover`

English:
theorem IsCompact.finite_compact_cover
  statement: {s : Set X} (hs : IsCompact s) {ι : Type*}
  proof: by
  classical
  induction t using Finset.induction generalizing U s with
  | empty =>
    refine ⟨fun _ => ∅, fun _ => isCompact_empty, fun i => empty_subset _, ?_⟩
    simpa only [subset_empty_iff, Finset.notMem_empty, iUnion_false, iUnion_empty] using hsC
  | insert x t hx ih =>
    simp only [Fi

中文:
定理 IsCompact.finite_compact_cover
  结论: {s : Set X} (hs : IsCompact s) {ι : 类型}
  证明: by
  classical
  induction t using Finset.induction generalizing U s with
  | empty =>
    refine ⟨fun _ => ∅, fun _ => isCompact_empty, fun i => empty_subset _, ?_⟩
    simpa only [subset_empty_iff, Finset.notMem_empty, iUnion_false, iUnion_empty] using hsC
  | insert x t hx ih =>
    simp only [Fi

Depends on / 依赖: Finset, Finset.forall_mem_insert, Finset.induction, Finset.notMem_empty, Finset.set_biUnion_insert, IsOpen, binary_compact_cover, classical, empty_subset, forall_mem_insert, generalizing, hs.binary_compact_cover, iUnion_empty, iUnion_false, insert, isCompact_empty, isOpen_biUnion, notMem_empty, set_biUnion_insert, subset_empty_iff
-/
theorem IsCompact.finite_compact_cover {s : Set X} (hs : IsCompact s) {ι : Type*}
    (t : Finset ι) (U : ι -> Set X) (hU : forall i in t, IsOpen (U i)) (hsC : s subseteq ⋃ i in t, U i) :
    exists K : ι -> Set X, (forall i, IsCompact (K i)) ∧ (forall i, K i subseteq U i) ∧ s = ⋃ i in t, K i := by
  classical
  induction t using Finset.induction generalizing U s with
  | empty =>
    refine ⟨fun _ => ∅, fun _ => isCompact_empty, fun i => empty_subset _, ?_⟩
    simpa only [subset_empty_iff, Finset.notMem_empty, iUnion_false, iUnion_empty] using hsC
  | insert x t hx ih =>
    simp only [Finset.set_biUnion_insert] at hsC
    simp only [Finset.forall_mem_insert] at hU
    have hU' : forall i in t, IsOpen (U i) := fun i hi => hU.2 i hi
    rcases hs.binary_compact_cover hU.1 (isOpen_biUnion hU') hsC with
      ⟨K₁, K₂, h1K₁, h1K₂, h2K₁, h2K₂, hK⟩
    rcases ih h1K₂ U hU' h2K₂ with ⟨K, h1K, h2K, h3K⟩
    refine ⟨update K x K₁, ?_, ?_, ?_⟩
    · intro i
      rcases eq_or_ne i x with rfl | hi
      · simp only [update_self, h1K₁]
      · simp only [update_of_ne hi, h1K]
    · intro i
      rcases eq_or_ne i x with rfl | hi
      · simp only [update_self, h2K₁]
      · simp only [update_of_ne hi, h2K]
    · simp only [Finset.set_biUnion_insert_update _ hx, hK, h3K]

/--
theorem `R1Space.of_continuous_specializes_imp` / 定理 `R1Space.of_continuous_specializes_imp`

English:
theorem R1Space.of_continuous_specializes_imp
  statement: [TopologicalSpace Y] {f : Y -> X} (hc : Continuous f)
  proof: (specializes_or_disjoint_nhds (f x) (f y)).imp (hspec x y)
    ((hc.tendsto _).disjoint · (hc.tendsto _))

中文:
定理 R1Space.of_continuous_specializes_imp
  结论: [TopologicalSpace Y] {f : Y -> X} (hc : Continuous f)
  证明: (specializes_or_disjoint_nhds (f x) (f y)).imp (hspec x y)
    ((hc.tendsto _).disjoint · (hc.tendsto _))

Depends on / 依赖: specializes_or_disjoint_nhds
-/
theorem R1Space.of_continuous_specializes_imp [TopologicalSpace Y] {f : Y -> X} (hc : Continuous f)
    (hspec : forall x y, f x ⤳ f y -> x ⤳ y) : R1Space Y where
specializes_or_disjoint_nhds x y := (specializes_or_disjoint_nhds (f x) (f y)).imp (hspec x y)
    ((hc.tendsto _).disjoint · (hc.tendsto _))

/--
theorem `Topology.IsInducing.r1Space` / 定理 `Topology.IsInducing.r1Space`

English:
theorem Topology.IsInducing.r1Space
  given: [TopologicalSpace Y] {f : Y -> X} (hf : IsInducing f)
  proof: .of_continuous_specializes_imp hf.continuous fun _ _ => hf.specializes_iff.1

中文:
定理 Topology.IsInducing.r1Space
  条件: [TopologicalSpace Y] {f : Y -> X} (hf : IsInducing f)
  证明: .of_continuous_specializes_imp hf.continuous fun _ _ => hf.specializes_iff.1

Depends on / 依赖: continuous, hf.continuous, hf.specializes_iff, of_continuous_specializes_imp, specializes_iff
-/
theorem Topology.IsInducing.r1Space [TopologicalSpace Y] {f : Y -> X} (hf : IsInducing f) :
    R1Space Y := .of_continuous_specializes_imp hf.continuous fun _ _ => hf.specializes_iff.1

/--
theorem `R1Space.induced` / 定理 `R1Space.induced`

English:
theorem R1Space.induced
  given: (f : Y -> X)
  statement: @R1Space Y (.induced f ‹_›)
  proof: @IsInducing.r1Space _ _ _ _ (.induced f _) f (.induced f)

中文:
定理 R1Space.induced
  条件: (f : Y -> X)
  结论: @R1Space Y (.induced f ‹_›)
  证明: @IsInducing.r1Space _ _ _ _ (.induced f _) f (.induced f)
-/
protected theorem R1Space.induced (f : Y -> X) : @R1Space Y (.induced f ‹_›) :=
  @IsInducing.r1Space _ _ _ _ (.induced f _) f (.induced f)

instance (p : X -> Prop) : R1Space (Subtype p) := .induced _

/--
theorem `R1Space.sInf` / 定理 `R1Space.sInf`

English:
theorem R1Space.sInf
  statement: {X : Type*} {T : Set (TopologicalSpace X)}
  proof: by
  let _ := sInf T
  refine ⟨fun x y => ?_⟩
  simp only [Specializes, nhds_sInf]
  by_cases! hTd : exists t in T, Disjoint (@nhds X t x) (@nhds X t y)
  · rcases hTd with ⟨t, htT, htd⟩
exact .inr htd.mono (iInf₂_le t htT) (iInf₂_le t htT)
· exact .inl iInf₂_mono fun t ht => ((hT t ht).1 x y).resol

中文:
定理 R1Space.sInf
  结论: {X : 类型} {T : Set (TopologicalSpace X)}
  证明: by
  let _ := sInf T
  refine ⟨fun x y => ?_⟩
  simp only [Specializes, nhds_sInf]
  by_cases! hTd : exists t in T, Disjoint (@nhds X t x) (@nhds X t y)
  · rcases hTd with ⟨t, htT, htd⟩
exact .inr htd.mono (iInf₂_le t htT) (iInf₂_le t htT)
· exact .inl iInf₂_mono fun t ht => ((hT t ht).1 x y).resol
-/
protected theorem R1Space.sInf {X : Type*} {T : Set (TopologicalSpace X)}
    (hT : forall t in T, @R1Space X t) : @R1Space X (sInf T) := by
  let _ := sInf T
  refine ⟨fun x y => ?_⟩
  simp only [Specializes, nhds_sInf]
  by_cases! hTd : exists t in T, Disjoint (@nhds X t x) (@nhds X t y)
  · rcases hTd with ⟨t, htT, htd⟩
exact .inr htd.mono (iInf₂_le t htT) (iInf₂_le t htT)
· exact .inl iInf₂_mono fun t ht => ((hT t ht).1 x y).resolve_right (hTd t ht)

/--
theorem `R1Space.iInf` / 定理 `R1Space.iInf`

English:
theorem R1Space.iInf
  statement: {ι X : Type*} {t : ι -> TopologicalSpace X}
  proof: .sInf forall_mem_range.2 ht

中文:
定理 R1Space.iInf
  结论: {ι X : 类型} {t : ι -> TopologicalSpace X}
  证明: .sInf forall_mem_range.2 ht
-/
protected theorem R1Space.iInf {ι X : Type*} {t : ι -> TopologicalSpace X}
    (ht : forall i, @R1Space X (t i)) : @R1Space X (iInf t) :=
.sInf forall_mem_range.2 ht

set_option backward.isDefEq.respectTransparency false in
/--
theorem `R1Space.inf` / 定理 `R1Space.inf`

English:
theorem R1Space.inf
  statement: {X : Type*} {t₁ t₂ : TopologicalSpace X}
  proof: by
  rw [inf_eq_iInf]
  apply R1Space.iInf
  simp [*]

中文:
定理 R1Space.inf
  结论: {X : 类型} {t₁ t₂ : TopologicalSpace X}
  证明: by
  rw [inf_eq_iInf]
  apply R1Space.iInf
  simp [*]
-/
protected theorem R1Space.inf {X : Type*} {t₁ t₂ : TopologicalSpace X}
    (h₁ : @R1Space X t₁) (h₂ : @R1Space X t₂) : @R1Space X (t₁ ⊓ t₂) := by
  rw [inf_eq_iInf]
  apply R1Space.iInf
  simp [*]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [TopologicalSpace
  signature: Y] [R1Space Y] : R1Space (X × Y)
  body: .inf (.induced _) (.induced _)

中文:
实例 [TopologicalSpace
  签名: Y] [R1Space Y] : R1Space (X × Y)
  定义体: .inf (.induced _) (.induced _)

Depends on / 依赖: induced
-/
instance [TopologicalSpace Y] [R1Space Y] : R1Space (X × Y) :=
  .inf (.induced _) (.induced _)

instance {ι : Type*} {X : ι -> Type*} [forall i, TopologicalSpace (X i)] [forall i, R1Space (X i)] :
    R1Space (forall i, X i) :=
  .iInf fun _ => .induced _

/--
theorem `exists_mem_nhds_isCompact_mapsTo_of_isCompact_mem_nhds` / 定理 `exists_mem_nhds_isCompact_mapsTo_of_isCompact_mem_nhds`

English:
theorem exists_mem_nhds_isCompact_mapsTo_of_isCompact_mem_nhds
  proof: by
  have hc : IsCompact (f '' K \ interior s) := (hKc.image hf).diff isOpen_interior
  obtain ⟨U, V, Uo, Vo, hxU, hV, hd⟩ : SeparatedNhds {f x} (f '' K \ interior s) := by
    simp_rw [separatedNhds_iff_disjoint, nhdsSet_singleton, hc.disjoint_nhdsSet_right,
      disjoint_nhds_nhds_iff_not_insepar

中文:
定理 exists_mem_nhds_isCompact_mapsTo_of_isCompact_mem_nhds
  证明: by
  have hc : IsCompact (f '' K \ interior s) := (hKc.image hf).diff isOpen_interior
  obtain ⟨U, V, Uo, Vo, hxU, hV, hd⟩ : SeparatedNhds {f x} (f '' K \ interior s) := by
    simp_rw [separatedNhds_iff_disjoint, nhdsSet_singleton, hc.disjoint_nhdsSet_right,
      disjoint_nhds_nhds_iff_not_insepar

Depends on / 依赖: IsCompact, SeparatedNhds, Vo.preimage, disjoint_nhdsSet_right, disjoint_nhds_nhds_iff_not_inseparable, filter_upwards, hKc.diff, hKc.image, hc.disjoint_nhdsSet_right, hf.co, hxy.mem_open_iff, interior, isOpen_interior, mem_interior_iff_mem_nhds, mem_open_iff, nhdsSet_singleton, preimage, sdiff_mem, separatedNhds_iff_disjoint, simp_rw
-/
theorem exists_mem_nhds_isCompact_mapsTo_of_isCompact_mem_nhds
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [R1Space Y] {f : X -> Y} {x : X}
    {K : Set X} {s : Set Y} (hf : Continuous f) (hs : s in 𝓝 (f x)) (hKc : IsCompact K)
    (hKx : K in 𝓝 x) : exists L in 𝓝 x, IsCompact L ∧ MapsTo f L s := by
  have hc : IsCompact (f '' K \ interior s) := (hKc.image hf).diff isOpen_interior
  obtain ⟨U, V, Uo, Vo, hxU, hV, hd⟩ : SeparatedNhds {f x} (f '' K \ interior s) := by
    simp_rw [separatedNhds_iff_disjoint, nhdsSet_singleton, hc.disjoint_nhdsSet_right,
      disjoint_nhds_nhds_iff_not_inseparable]
    rintro y ⟨-, hys⟩ hxy
refine hys (hxy.mem_open_iff isOpen_interior).1 ?_
    rwa [mem_interior_iff_mem_nhds]
refine ⟨K \ f ⁻¹' V, sdiff_mem hKx ?_, hKc.diff Vo.preimage hf, fun y hy => ?_⟩
  · filter_upwards [hf.continuousAt <| Uo.mem_nhds (hxU rfl)] with x hx
      using Set.disjoint_left.1 hd hx
  · by_contra hys
    exact hy.2 (hV ⟨mem_image_of_mem _ hy.1, notMem_subset interior_subset hys⟩)

instance (priority := 900) {X Y : Type*} [TopologicalSpace X] [WeaklyLocallyCompactSpace X]
    [TopologicalSpace Y] [R1Space Y] : LocallyCompactPair X Y where
  exists_mem_nhds_isCompact_mapsTo hf hs :=
    let ⟨_K, hKc, hKx⟩ := exists_compact_mem_nhds _
    exists_mem_nhds_isCompact_mapsTo_of_isCompact_mem_nhds hf hs hKc hKx

/--
theorem `IsCompact.isCompact_isClosed_basis_nhds` / 定理 `IsCompact.isCompact_isClosed_basis_nhds`

English:
theorem IsCompact.isCompact_isClosed_basis_nhds
  statement: {x : X} {L : Set X} (hLc : IsCompact L)
  proof: hasBasis_self.2 fun _U hU =>
    let ⟨K, hKx, hKc, hKU⟩ := exists_mem_nhds_isCompact_mapsTo_of_isCompact_mem_nhds
      continuous_id (interior_mem_nhds.2 hU) hLc hxL
    ⟨closure K, mem_of_superset hKx subset_closure, ⟨hKc.closure, isClosed_closure⟩,
      (hKc.closure_subset_of_isOpen isOpen_inter

中文:
定理 IsCompact.isCompact_isClosed_basis_nhds
  结论: {x : X} {L : Set X} (hLc : IsCompact L)
  证明: hasBasis_self.2 fun _U hU =>
    let ⟨K, hKx, hKc, hKU⟩ := exists_mem_nhds_isCompact_mapsTo_of_isCompact_mem_nhds
      continuous_id (interior_mem_nhds.2 hU) hLc hxL
    ⟨closure K, mem_of_superset hKx subset_closure, ⟨hKc.closure, isClosed_closure⟩,
      (hKc.closure_subset_of_isOpen isOpen_inter

Depends on / 依赖: closure, closure_subset_of_isOpen, continuous_id, exists_mem_nhds_isCompact_mapsTo_of_isCompact_mem_nhds, hKc.closure, hKc.closure_subset_of_isOpen, hasBasis_self, interior_mem_nhds, interior_subset, isClosed_closure, isOpen_interior, mem_of_superset, subset_closure
-/
theorem IsCompact.isCompact_isClosed_basis_nhds {x : X} {L : Set X} (hLc : IsCompact L)
    (hxL : L in 𝓝 x) : (𝓝 x).HasBasis (fun K => K in 𝓝 x ∧ IsCompact K ∧ IsClosed K) (·) :=
  hasBasis_self.2 fun _U hU =>
    let ⟨K, hKx, hKc, hKU⟩ := exists_mem_nhds_isCompact_mapsTo_of_isCompact_mem_nhds
      continuous_id (interior_mem_nhds.2 hU) hLc hxL
    ⟨closure K, mem_of_superset hKx subset_closure, ⟨hKc.closure, isClosed_closure⟩,
      (hKc.closure_subset_of_isOpen isOpen_interior hKU).trans interior_subset⟩

/-- In an R₁ space, the filters `coclosedCompact` and `cocompact` are equal. -/
@[simp]
/--
theorem `Filter.coclosedCompact_eq_cocompact` / 定理 `Filter.coclosedCompact_eq_cocompact`

English:
theorem Filter.coclosedCompact_eq_cocompact
  statement: coclosedCompact X = cocompact X
  proof: by
  refine le_antisymm ?_ cocompact_le_coclosedCompact
  rw [hasBasis_coclosedCompact.le_basis_iff hasBasis_cocompact]
  exact fun K hK => ⟨closure K, ⟨isClosed_closure, hK.closure⟩, compl_subset_compl.2 subset_closure⟩

中文:
定理 Filter.coclosedCompact_eq_cocompact
  结论: coclosedCompact X = cocompact X
  证明: by
  refine le_antisymm ?_ cocompact_le_coclosedCompact
  rw [hasBasis_coclosedCompact.le_basis_iff hasBasis_cocompact]
  exact fun K hK => ⟨closure K, ⟨isClosed_closure, hK.closure⟩, compl_subset_compl.2 subset_closure⟩

Depends on / 依赖: closure, cocompact_le_coclosedCompact, compl_subset_compl, hK.closure, hasBasis_coclosedCompact, hasBasis_coclosedCompact.le_basis_iff, hasBasis_cocompact, isClosed_closure, le_antisymm, le_basis_iff, subset_closure
-/
theorem Filter.coclosedCompact_eq_cocompact : coclosedCompact X = cocompact X := by
  refine le_antisymm ?_ cocompact_le_coclosedCompact
  rw [hasBasis_coclosedCompact.le_basis_iff hasBasis_cocompact]
  exact fun K hK => ⟨closure K, ⟨isClosed_closure, hK.closure⟩, compl_subset_compl.2 subset_closure⟩

/-- In an R₁ space, the bornologies `relativelyCompact` and `inCompact` are equal. -/
@[simp]
/--
theorem `Bornology.relativelyCompact_eq_inCompact` / 定理 `Bornology.relativelyCompact_eq_inCompact`

English:
theorem Bornology.relativelyCompact_eq_inCompact
  proof: Bornology.ext _ _ Filter.coclosedCompact_eq_cocompact

中文:
定理 Bornology.relativelyCompact_eq_inCompact
  证明: Bornology.ext _ _ Filter.coclosedCompact_eq_cocompact

Depends on / 依赖: Bornology, Bornology.ext, Filter, Filter.coclosedCompact_eq_cocompact, coclosedCompact_eq_cocompact
-/
theorem Bornology.relativelyCompact_eq_inCompact :
    Bornology.relativelyCompact X = Bornology.inCompact X :=
  Bornology.ext _ _ Filter.coclosedCompact_eq_cocompact

/-!
### Lemmas about a weakly locally compact R₁ space

In fact, a space with these properties is locally compact and regular.
Some lemmas are formulated using the latter assumptions below.
-/

variable [WeaklyLocallyCompactSpace X]

/--
theorem `isCompact_isClosed_basis_nhds` / 定理 `isCompact_isClosed_basis_nhds`

English:
theorem isCompact_isClosed_basis_nhds
  given: (x : X)
  proof: let ⟨_L, hLc, hLx⟩ := exists_compact_mem_nhds x
  hLc.isCompact_isClosed_basis_nhds hLx

中文:
定理 isCompact_isClosed_basis_nhds
  条件: (x : X)
  证明: let ⟨_L, hLc, hLx⟩ := exists_compact_mem_nhds x
  hLc.isCompact_isClosed_basis_nhds hLx

Depends on / 依赖: exists_compact_mem_nhds, hLc.isCompact_isClosed_basis_nhds, isCompact_isClosed_basis_nhds
-/
theorem isCompact_isClosed_basis_nhds (x : X) :
    (𝓝 x).HasBasis (fun K => K in 𝓝 x ∧ IsCompact K ∧ IsClosed K) (·) :=
  let ⟨_L, hLc, hLx⟩ := exists_compact_mem_nhds x
  hLc.isCompact_isClosed_basis_nhds hLx

/--
theorem `exists_mem_nhds_isCompact_isClosed` / 定理 `exists_mem_nhds_isCompact_isClosed`

English:
theorem exists_mem_nhds_isCompact_isClosed
  given: (x : X)
  statement: exists K in 𝓝 x, IsCompact K ∧ IsClosed K
  proof: (isCompact_isClosed_basis_nhds x).ex_mem

中文:
定理 exists_mem_nhds_isCompact_isClosed
  条件: (x : X)
  结论: 存在 K in 𝓝 x, IsCompact K ∧ IsClosed K
  证明: (isCompact_isClosed_basis_nhds x).ex_mem

Depends on / 依赖: ex_mem, isCompact_isClosed_basis_nhds
-/
theorem exists_mem_nhds_isCompact_isClosed (x : X) : exists K in 𝓝 x, IsCompact K ∧ IsClosed K :=
  (isCompact_isClosed_basis_nhds x).ex_mem

-- see Note [lower instance priority]
/-- A weakly locally compact R₁ space is locally compact. -/
instance (priority := 80) WeaklyLocallyCompactSpace.locallyCompactSpace : LocallyCompactSpace X :=
  .of_hasBasis isCompact_isClosed_basis_nhds fun _ _ ⟨_, h, _⟩ => h

/--
theorem `exists_isOpen_superset_and_isCompact_closure` / 定理 `exists_isOpen_superset_and_isCompact_closure`

English:
theorem exists_isOpen_superset_and_isCompact_closure
  given: {K : Set X} (hK : IsCompact K)
  proof: by
  rcases exists_compact_superset hK with ⟨K', hK', hKK'⟩
  exact ⟨interior K', isOpen_interior, hKK', hK'.closure_of_subset interior_subset⟩

中文:
定理 exists_isOpen_superset_and_isCompact_closure
  条件: {K : Set X} (hK : IsCompact K)
  证明: by
  rcases exists_compact_superset hK with ⟨K', hK', hKK'⟩
  exact ⟨interior K', isOpen_interior, hKK', hK'.closure_of_subset interior_subset⟩

Depends on / 依赖: closure_of_subset, exists_compact_superset, interior, interior_subset, isOpen_interior
-/
theorem exists_isOpen_superset_and_isCompact_closure {K : Set X} (hK : IsCompact K) :
    exists V, IsOpen V ∧ K subseteq V ∧ IsCompact (closure V) := by
  rcases exists_compact_superset hK with ⟨K', hK', hKK'⟩
  exact ⟨interior K', isOpen_interior, hKK', hK'.closure_of_subset interior_subset⟩

/--
theorem `exists_isOpen_mem_isCompact_closure` / 定理 `exists_isOpen_mem_isCompact_closure`

English:
theorem exists_isOpen_mem_isCompact_closure
  given: (x : X)
  proof: by
  simpa only [singleton_subset_iff]
    using exists_isOpen_superset_and_isCompact_closure isCompact_singleton

中文:
定理 exists_isOpen_mem_isCompact_closure
  条件: (x : X)
  证明: by
  simpa only [singleton_subset_iff]
    using exists_isOpen_superset_and_isCompact_closure isCompact_singleton

Depends on / 依赖: exists_isOpen_superset_and_isCompact_closure, isCompact_singleton, singleton_subset_iff
-/
theorem exists_isOpen_mem_isCompact_closure (x : X) :
    exists U : Set X, IsOpen U ∧ x in U ∧ IsCompact (closure U) := by
  simpa only [singleton_subset_iff]
    using exists_isOpen_superset_and_isCompact_closure isCompact_singleton

end R1Space

end Separation
