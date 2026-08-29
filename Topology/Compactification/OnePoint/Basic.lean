/-
Copyright (c) 2021 Yourong Zang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yourong Zang, Yury Kudryashov
-/
module

public import Mathlib.Data.Fintype.Option
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Sets.Opens
import Mathlib.Topology.WithTopology

/-!
# The one-point compactification

We construct the one-point compactification of an arbitrary topological space `X` and prove some
properties inherited from `X`.

## Main definitions

* `OnePoint`: the one-point compactification, we use coercion for the canonical embedding
  `X → OnePoint X`; when `X` is already compact, the compactification adds an isolated point
  to the space.
* `OnePoint.infty`: the extra point

## Main results

* The topological structure of `OnePoint X`
* The connectedness of `OnePoint X` for a noncompact, preconnected `X`
* `OnePoint X` is `T₀` for a T₀ space `X`
* `OnePoint X` is `T₁` for a T₁ space `X`
* `OnePoint X` is normal if `X` is a locally compact Hausdorff space

## Tags

one point compactification, Alexandroff compactification, compactness
-/

@[expose] public section


open Set Filter Topology

/-!
### Definition and basic properties

In this section we define `OnePoint X` to be the disjoint union of `X` and `∞`, implemented as
`Option X`. Then we restate some lemmas about `Option X` for `OnePoint X`.
-/


variable {X Y : Type*}

/--
Definition of `OnePoint` / `OnePoint` 的定义

English:
definition OnePoint
  signature: (X : Type*)
  body: Option X

中文:
定义 OnePoint
  签名: (X : 类型)
  定义体: Option X
-/
def OnePoint (X : Type*) :=
  Option X

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Repr
  signature: X] : Repr (OnePoint X)
  body: ⟨fun o _ =>
    match o with
    | none => "∞"
    | some a => "↑" ++ repr a⟩

中文:
实例 [Repr
  签名: X] : Repr (OnePoint X)
  定义体: ⟨fun o _ =>
    match o with
    | none => "∞"
    | some a => "↑" ++ repr a⟩
-/
instance [Repr X] : Repr (OnePoint X) :=
  ⟨fun o _ =>
    match o with
    | none => "∞"
    | some a => "↑" ++ repr a⟩

namespace OnePoint

/--
Definition of `infty` / `infty` 的定义

English:
definition infty
  signature: : OnePoint X
  body: none

@[inherit_doc]
scoped notation "∞" => OnePoint.infty

中文:
定义 infty
  签名: : OnePoint X
  定义体: none

@[inherit_doc]
scoped notation "∞" => OnePoint.infty
-/
@[match_pattern] def infty : OnePoint X := none

@[inherit_doc]
scoped notation "∞" => OnePoint.infty

/--
Definition of `some` / `some` 的定义

English:
definition some
  signature: : X -> OnePoint X
  body: Option.some

@[simp]

中文:
定义 some
  签名: : X -> OnePoint X
  定义体: Option.some

@[simp]
-/
@[coe, match_pattern] def some : X -> OnePoint X := Option.some

@[simp]
/--
lemma `some_eq_iff` / 引理 `some_eq_iff`

English:
lemma some_eq_iff
  given: (x₁ x₂ : X)
  statement: (some x₁ = some x₂) ↔ (x₁ = x₂)
  proof: by
  rw [iff_eq_eq]
  exact Option.some.injEq x₁ x₂

中文:
引理 some_eq_iff
  条件: (x₁ x₂ : X)
  结论: (some x₁ = some x₂) ↔ (x₁ = x₂)
  证明: by
  rw [iff_eq_eq]
  exact Option.some.injEq x₁ x₂

Depends on / 依赖: Option.some.injEq, iff_eq_eq
-/
lemma some_eq_iff (x₁ x₂ : X) : (some x₁ = some x₂) ↔ (x₁ = x₂) := by
  rw [iff_eq_eq]
  exact Option.some.injEq x₁ x₂

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeTC X (OnePoint X)
  body: ⟨some⟩

中文:
实例 :
  签名: CoeTC X (OnePoint X)
  定义体: ⟨some⟩
-/
instance : CoeTC X (OnePoint X) := ⟨some⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (OnePoint X)
  body: ⟨∞⟩

中文:
实例 :
  签名: 可居 (OnePoint X)
  定义体: ⟨∞⟩
-/
instance : Inhabited (OnePoint X) := ⟨∞⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsEmpty
  signature: X] : Subsingleton (OnePoint X)
  body: inferInstanceAs Subsingleton (Option X)

中文:
实例 [是空
  签名: X] : 子单例 (OnePoint X)
  定义体: inferInstanceAs Subsingleton (Option X)

Depends on / 依赖: Subsingleton
-/
instance [IsEmpty X] : Subsingleton (OnePoint X) :=
inferInstanceAs Subsingleton (Option X)

/--
lemma `«forall»` / 引理 `«forall»`

English:
lemma «forall»
  given: {p : OnePoint X -> Prop}
  proof: Option.forall

中文:
引理 «对任意»
  条件: {p : OnePoint X -> 命题}
  证明: Option.forall
-/
protected lemma «forall» {p : OnePoint X -> Prop} :
    (forall (x : OnePoint X), p x) ↔ p ∞ ∧ forall (x : X), p x :=
  Option.forall

/--
lemma `«exists»` / 引理 `«exists»`

English:
lemma «exists»
  given: {p : OnePoint X -> Prop}
  proof: Option.exists

中文:
引理 «存在»
  条件: {p : OnePoint X -> 命题}
  证明: Option.exists
-/
protected lemma «exists» {p : OnePoint X -> Prop} :
    (exists x, p x) ↔ p ∞ ∨ exists (x : X), p x :=
  Option.exists

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Fintype
  signature: X] : Fintype (OnePoint X)
  body: inferInstanceAs (Fintype (Option X))

中文:
实例 [有限类型
  签名: X] : 有限类型 (OnePoint X)
  定义体: inferInstanceAs (Fintype (Option X))

Depends on / 依赖: Fintype
-/
instance [Fintype X] : Fintype (OnePoint X) :=
  inferInstanceAs (Fintype (Option X))

/--
Instance `infinite` / 实例 `infinite`

English:
instance infinite
  signature: [Infinite X]
  body: inferInstanceAs (Infinite (Option X))

中文:
实例 infinite
  签名: [无限 X]
  定义体: inferInstanceAs (Infinite (Option X))

Depends on / 依赖: Infinite
-/
instance infinite [Infinite X] : Infinite (OnePoint X) :=
  inferInstanceAs (Infinite (Option X))

/--
theorem `coe_injective` / 定理 `coe_injective`

English:
theorem coe_injective
  statement: Function.Injective ((↑) : X -> OnePoint X)
  proof: Option.some_injective X

@[norm_cast]

中文:
定理 coe_injective
  结论: 函数.单射 ((↑) : X -> OnePoint X)
  证明: Option.some_injective X

@[norm_cast]

Depends on / 依赖: Option.some_injective, some_injective
-/
theorem coe_injective : Function.Injective ((↑) : X -> OnePoint X) :=
  Option.some_injective X

@[norm_cast]
/--
theorem `coe_eq_coe` / 定理 `coe_eq_coe`

English:
theorem coe_eq_coe
  given: {x y : X}
  statement: (x : OnePoint X) = y ↔ x = y
  proof: coe_injective.eq_iff

@[simp]

中文:
定理 coe_eq_coe
  条件: {x y : X}
  结论: (x : OnePoint X) = y ↔ x = y
  证明: coe_injective.eq_iff

@[simp]

Depends on / 依赖: coe_injective, coe_injective.eq_iff, eq_iff
-/
theorem coe_eq_coe {x y : X} : (x : OnePoint X) = y ↔ x = y :=
  coe_injective.eq_iff

@[simp]
/--
theorem `coe_ne_infty` / 定理 `coe_ne_infty`

English:
theorem coe_ne_infty
  given: (x : X)
  statement: (x : OnePoint X) != ∞
  proof: nofun

@[simp]

中文:
定理 coe_ne_infty
  条件: (x : X)
  结论: (x : OnePoint X) != ∞
  证明: nofun

@[simp]
-/
theorem coe_ne_infty (x : X) : (x : OnePoint X) != ∞ :=
  nofun

@[simp]
/--
theorem `infty_ne_coe` / 定理 `infty_ne_coe`

English:
theorem infty_ne_coe
  given: (x : X)
  statement: ∞ != (x : OnePoint X)
  proof: nofun

中文:
定理 infty_ne_coe
  条件: (x : X)
  结论: ∞ != (x : OnePoint X)
  证明: nofun
-/
theorem infty_ne_coe (x : X) : ∞ != (x : OnePoint X) :=
  nofun

/-- Recursor for `OnePoint` using the preferred forms `∞` and `↑x`. -/
@[elab_as_elim, induction_eliminator, cases_eliminator]
/--
Definition of `rec` / `rec` 的定义

English:
definition rec
  signature: {C : OnePoint X -> Sort*} (infty : C ∞) (coe : forall x : X, C x)

中文:
定义 rec
  签名: {C : OnePoint X -> 类型层*} (infty : C ∞) (coe : 对任意 x : X, C x)
-/
protected def rec {C : OnePoint X -> Sort*} (infty : C ∞) (coe : forall x : X, C x) :
    forall z : OnePoint X, C z
  | ∞ => infty
  | (x : X) => coe x

/--
Definition of `elim` / `elim` 的定义

English:
definition elim
  signature: : OnePoint X -> Y -> (X -> Y) -> Y
  body: Option.elim

中文:
定义 elim
  签名: : OnePoint X -> Y -> (X -> Y) -> Y
  定义体: Option.elim
-/
@[inline] protected def elim : OnePoint X -> Y -> (X -> Y) -> Y := Option.elim

/--
theorem `elim_infty` / 定理 `elim_infty`

English:
theorem elim_infty
  given: (y : Y) (f : X -> Y)
  statement: ∞.elim y f = y
  proof: rfl

中文:
定理 elim_infty
  条件: (y : Y) (f : X -> Y)
  结论: ∞.elim y f = y
  证明: rfl
-/
@[simp] theorem elim_infty (y : Y) (f : X -> Y) : ∞.elim y f = y := rfl

/--
theorem `elim_some` / 定理 `elim_some`

English:
theorem elim_some
  given: (y : Y) (f : X -> Y) (x : X)
  statement: (some x).elim y f = f x
  proof: rfl

中文:
定理 elim_some
  条件: (y : Y) (f : X -> Y) (x : X)
  结论: (some x).elim y f = f x
  证明: rfl
-/
@[simp] theorem elim_some (y : Y) (f : X -> Y) (x : X) : (some x).elim y f = f x := rfl

/--
theorem `isCompl_range_coe_infty` / 定理 `isCompl_range_coe_infty`

English:
theorem isCompl_range_coe_infty
  statement: IsCompl (range ((↑) : X -> OnePoint X)) {∞}
  proof: isCompl_range_some_none X

中文:
定理 isCompl_range_coe_infty
  结论: 是补集 (range ((↑) : X -> OnePoint X)) {∞}
  证明: isCompl_range_some_none X

Depends on / 依赖: isCompl_range_some_none
-/
theorem isCompl_range_coe_infty : IsCompl (range ((↑) : X -> OnePoint X)) {∞} :=
  isCompl_range_some_none X

/--
theorem `range_coe_union_infty` / 定理 `range_coe_union_infty`

English:
theorem range_coe_union_infty
  statement: range ((↑) : X -> OnePoint X) union {∞} = univ
  proof: range_some_union_none X

@[simp]

中文:
定理 range_coe_union_infty
  结论: range ((↑) : X -> OnePoint X) union {∞} = univ
  证明: range_some_union_none X

@[simp]

Depends on / 依赖: range_some_union_none
-/
theorem range_coe_union_infty : range ((↑) : X -> OnePoint X) union {∞} = univ :=
  range_some_union_none X

@[simp]
/--
theorem `insert_infty_range_coe` / 定理 `insert_infty_range_coe`

English:
theorem insert_infty_range_coe
  statement: insert ∞ (range (@some X)) = univ
  proof: insert_none_range_some _

@[simp]

中文:
定理 insert_infty_range_coe
  结论: insert ∞ (range (@some X)) = univ
  证明: insert_none_range_some _

@[simp]

Depends on / 依赖: insert_none_range_some
-/
theorem insert_infty_range_coe : insert ∞ (range (@some X)) = univ :=
  insert_none_range_some _

@[simp]
/--
theorem `compl_range_coe` / 定理 `compl_range_coe`

English:
theorem compl_range_coe
  statement: (range ((↑) : X -> OnePoint X))ᶜ = {∞}
  proof: compl_range_some X

中文:
定理 compl_range_coe
  结论: (range ((↑) : X -> OnePoint X))ᶜ = {∞}
  证明: compl_range_some X

Depends on / 依赖: compl_range_some
-/
theorem compl_range_coe : (range ((↑) : X -> OnePoint X))ᶜ = {∞} :=
  compl_range_some X

/--
theorem `compl_infty` / 定理 `compl_infty`

English:
theorem compl_infty
  statement: ({∞}ᶜ : Set (OnePoint X)) = range ((↑) : X -> OnePoint X)
  proof: (@isCompl_range_coe_infty X).symm.compl_eq

中文:
定理 compl_infty
  结论: ({∞}ᶜ : 集合 (OnePoint X)) = range ((↑) : X -> OnePoint X)
  证明: (@isCompl_range_coe_infty X).symm.compl_eq

Depends on / 依赖: compl_eq, isCompl_range_coe_infty, symm.compl_eq
-/
theorem compl_infty : ({∞}ᶜ : Set (OnePoint X)) = range ((↑) : X -> OnePoint X) :=
  (@isCompl_range_coe_infty X).symm.compl_eq

/--
theorem `compl_image_coe` / 定理 `compl_image_coe`

English:
theorem compl_image_coe
  given: (s : Set X)
  statement: ((↑) '' s : Set (OnePoint X))ᶜ = (↑) '' sᶜ union {∞}
  proof: by
  rw [coe_injective.compl_image_eq]; rw [compl_range_coe]

中文:
定理 compl_image_coe
  条件: (s : 集合 X)
  结论: ((↑) '' s : 集合 (OnePoint X))ᶜ = (↑) '' sᶜ union {∞}
  证明: by
  rw [coe_injective.compl_image_eq]; rw [compl_range_coe]

Depends on / 依赖: coe_injective, coe_injective.compl_image_eq, compl_image_eq, compl_range_coe
-/
theorem compl_image_coe (s : Set X) : ((↑) '' s : Set (OnePoint X))ᶜ = (↑) '' sᶜ union {∞} := by
  rw [coe_injective.compl_image_eq]; rw [compl_range_coe]

/--
theorem `ne_infty_iff_exists` / 定理 `ne_infty_iff_exists`

English:
theorem ne_infty_iff_exists
  given: {x : OnePoint X}
  statement: x != ∞ ↔ exists y : X, (y : OnePoint X) = x
  proof: by
  induction x using OnePoint.rec <;> simp

中文:
定理 ne_infty_iff_存在
  条件: {x : OnePoint X}
  结论: x != ∞ ↔ 存在 y : X, (y : OnePoint X) = x
  证明: by
  induction x using OnePoint.rec <;> simp

Depends on / 依赖: OnePoint, OnePoint.rec
-/
theorem ne_infty_iff_exists {x : OnePoint X} : x != ∞ ↔ exists y : X, (y : OnePoint X) = x := by
  induction x using OnePoint.rec <;> simp

/--
Instance `canLift` / 实例 `canLift`

English:
instance canLift
  signature: : CanLift (OnePoint X) X (↑) fun x => x != ∞
  body: WithTop.canLift

中文:
实例 canLift
  签名: : CanLift (OnePoint X) X (↑) fun x => x != ∞
  定义体: WithTop.canLift

Depends on / 依赖: WithTop, WithTop.canLift, canLift
-/
instance canLift : CanLift (OnePoint X) X (↑) fun x => x != ∞ :=
  WithTop.canLift

/--
theorem `notMem_range_coe_iff` / 定理 `notMem_range_coe_iff`

English:
theorem notMem_range_coe_iff
  given: {x : OnePoint X}
  statement: x ∉ range some ↔ x = ∞
  proof: by
  rw [← mem_compl_iff]; rw [compl_range_coe]; rw [mem_singleton_iff]

中文:
定理 notMem_range_coe_iff
  条件: {x : OnePoint X}
  结论: x ∉ range some ↔ x = ∞
  证明: by
  rw [← mem_compl_iff]; rw [compl_range_coe]; rw [mem_singleton_iff]

Depends on / 依赖: compl_range_coe, mem_compl_iff, mem_singleton_iff
-/
theorem notMem_range_coe_iff {x : OnePoint X} : x ∉ range some ↔ x = ∞ := by
  rw [← mem_compl_iff]; rw [compl_range_coe]; rw [mem_singleton_iff]

/--
theorem `infty_notMem_range_coe` / 定理 `infty_notMem_range_coe`

English:
theorem infty_notMem_range_coe
  statement: ∞ ∉ range ((↑) : X -> OnePoint X)
  proof: notMem_range_coe_iff.2 rfl

中文:
定理 infty_notMem_range_coe
  结论: ∞ ∉ range ((↑) : X -> OnePoint X)
  证明: notMem_range_coe_iff.2 rfl

Depends on / 依赖: notMem_range_coe_iff
-/
theorem infty_notMem_range_coe : ∞ ∉ range ((↑) : X -> OnePoint X) :=
  notMem_range_coe_iff.2 rfl

/--
theorem `infty_notMem_image_coe` / 定理 `infty_notMem_image_coe`

English:
theorem infty_notMem_image_coe
  given: {s : Set X}
  statement: ∞ ∉ ((↑) : X -> OnePoint X) '' s
  proof: notMem_subset (image_subset_range _ _) infty_notMem_range_coe

@[simp]

中文:
定理 infty_notMem_image_coe
  条件: {s : 集合 X}
  结论: ∞ ∉ ((↑) : X -> OnePoint X) '' s
  证明: notMem_subset (image_subset_range _ _) infty_notMem_range_coe

@[simp]

Depends on / 依赖: image_subset_range, infty_notMem_range_coe, notMem_subset
-/
theorem infty_notMem_image_coe {s : Set X} : ∞ ∉ ((↑) : X -> OnePoint X) '' s :=
  notMem_subset (image_subset_range _ _) infty_notMem_range_coe

@[simp]
/--
theorem `coe_preimage_infty` / 定理 `coe_preimage_infty`

English:
theorem coe_preimage_infty
  statement: ((↑) : X -> OnePoint X) ⁻¹' {∞} = ∅
  proof: by
  ext
  simp

中文:
定理 coe_preimage_infty
  结论: ((↑) : X -> OnePoint X) ⁻¹' {∞} = ∅
  证明: by
  ext
  simp
-/
theorem coe_preimage_infty : ((↑) : X -> OnePoint X) ⁻¹' {∞} = ∅ := by
  ext
  simp

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : X -> Y)
  body: Option.map f

中文:
定义 map
  签名: (f : X -> Y)
  定义体: Option.map f
-/
protected def map (f : X -> Y) : OnePoint X -> OnePoint Y :=
  Option.map f

/--
theorem `map_infty` / 定理 `map_infty`

English:
theorem map_infty
  given: (f : X -> Y)
  statement: OnePoint.map f ∞ = ∞
  proof: rfl

中文:
定理 map_infty
  条件: (f : X -> Y)
  结论: OnePoint.map f ∞ = ∞
  证明: rfl
-/
@[simp] theorem map_infty (f : X -> Y) : OnePoint.map f ∞ = ∞ := rfl
/--
theorem `map_some` / 定理 `map_some`

English:
theorem map_some
  given: (f : X -> Y) (x : X)
  statement: (x : OnePoint X).map f = f x
  proof: rfl

中文:
定理 map_some
  条件: (f : X -> Y) (x : X)
  结论: (x : OnePoint X).map f = f x
  证明: rfl
-/
@[simp] theorem map_some (f : X -> Y) (x : X) : (x : OnePoint X).map f = f x := rfl
/--
theorem `map_id` / 定理 `map_id`

English:
theorem map_id
  statement: OnePoint.map (id : X -> X) = id
  proof: Option.map_id

中文:
定理 map_id
  结论: OnePoint.map (id : X -> X) = id
  证明: Option.map_id
-/
@[simp] theorem map_id : OnePoint.map (id : X -> X) = id := Option.map_id

/--
theorem `map_comp` / 定理 `map_comp`

English:
theorem map_comp
  given: {Z : Type*} (f : Y -> Z) (g : X -> Y)
  proof: (Option.map_comp_map _ _).symm

中文:
定理 map_comp
  条件: {Z : 类型} (f : Y -> Z) (g : X -> Y)
  证明: (Option.map_comp_map _ _).symm

Depends on / 依赖: Option.map_comp_map, map_comp_map
-/
theorem map_comp {Z : Type*} (f : Y -> Z) (g : X -> Y) :
    OnePoint.map (f ∘ g) = OnePoint.map f ∘ OnePoint.map g :=
  (Option.map_comp_map _ _).symm

/-!
### Topological space structure on `OnePoint X`

We define a topological space structure on `OnePoint X` so that `s` is open if and only if

* `(↑) ⁻¹' s` is open in `X`;
* if `∞ ∈ s`, then `((↑) ⁻¹' s)ᶜ` is compact.

Then we reformulate this definition in a few different ways, and prove that
`(↑) : X → OnePoint X` is an open embedding. If `X` is not a compact space, then we also prove
that `(↑)` has dense range, so it is a dense embedding.
-/


variable [TopologicalSpace X]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: TopologicalSpace (OnePoint X)
  body: (∞ in s -> IsCompact (((↑) : X -> OnePoint X) ⁻¹' s)ᶜ) ∧
    IsOpen (((↑) : X -> OnePoint X) ⁻¹' s)
  isOpen_univ := by simp
  isOpen_inter s t := by
    rintro ⟨hms, hs⟩ ⟨hmt, ht⟩
    refine ⟨?_, hs.inter ht⟩
    rintro ⟨hms', hmt'⟩
    simpa [compl_inter] using (hms hms').union (hmt hmt')
  isOpen_sUnion S ho := by
    suffices IsOpen ((↑) ⁻¹' ⋃₀ S : Set X) by
      refine ⟨?_, this⟩
      rintro ⟨s, hsS : s in S, hs : ∞ in s⟩
      refine IsCompact.of_isClosed_subset ((ho s hsS).1 hs) this.isClosed_compl ?_
      exact compl_subset_compl.mpr (preimage_mono <| subset_sUnion_of_mem hsS)
    rw [preimage_sUnion]
    exact isOpen_biUnion fun s hs => (ho s hs).2

中文:
实例 :
  签名: 拓扑空间 (OnePoint X)
  定义体: (∞ in s -> IsCompact (((↑) : X -> OnePoint X) ⁻¹' s)ᶜ) ∧
    IsOpen (((↑) : X -> OnePoint X) ⁻¹' s)
  isOpen_univ := by simp
  isOpen_inter s t := by
    rintro ⟨hms, hs⟩ ⟨hmt, ht⟩
    refine ⟨?_, hs.inter ht⟩
    rintro ⟨hms', hmt'⟩
    simpa [compl_inter] using (hms hms').union (hmt hmt')
  isOpen_sUnion S ho := by
    suffices IsOpen ((↑) ⁻¹' ⋃₀ S : Set X) by
      refine ⟨?_, this⟩
      rintro ⟨s, hsS : s in S, hs : ∞ in s⟩
      refine IsCompact.of_isClosed_subset ((ho s hsS).1 hs) this.isClosed_compl ?_
      exact compl_subset_compl.mpr (preimage_mono <| subset_sUnion_of_mem hsS)
    rw [preimage_sUnion]
    exact isOpen_biUnion fun s hs => (ho s hs).2

Depends on / 依赖: IsCompact, OnePoint
-/
instance : TopologicalSpace (OnePoint X) where
  IsOpen s := (∞ in s -> IsCompact (((↑) : X -> OnePoint X) ⁻¹' s)ᶜ) ∧
    IsOpen (((↑) : X -> OnePoint X) ⁻¹' s)
  isOpen_univ := by simp
  isOpen_inter s t := by
    rintro ⟨hms, hs⟩ ⟨hmt, ht⟩
    refine ⟨?_, hs.inter ht⟩
    rintro ⟨hms', hmt'⟩
    simpa [compl_inter] using (hms hms').union (hmt hmt')
  isOpen_sUnion S ho := by
    suffices IsOpen ((↑) ⁻¹' ⋃₀ S : Set X) by
      refine ⟨?_, this⟩
      rintro ⟨s, hsS : s in S, hs : ∞ in s⟩
      refine IsCompact.of_isClosed_subset ((ho s hsS).1 hs) this.isClosed_compl ?_
      exact compl_subset_compl.mpr (preimage_mono <| subset_sUnion_of_mem hsS)
    rw [preimage_sUnion]
    exact isOpen_biUnion fun s hs => (ho s hs).2

variable {s : Set (OnePoint X)}

/--
theorem `isOpen_def` / 定理 `isOpen_def`

English:
theorem isOpen_def
  proof: Iff.rfl

中文:
定理 isOpen_def
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem isOpen_def :
    IsOpen s ↔ (∞ in s -> IsCompact ((↑) ⁻¹' s : Set X)ᶜ) ∧ IsOpen ((↑) ⁻¹' s : Set X) :=
  Iff.rfl

/--
theorem `isOpen_iff_of_mem'` / 定理 `isOpen_iff_of_mem'`

English:
theorem isOpen_iff_of_mem'
  given: (h : ∞ in s)
  proof: by
  simp [isOpen_def, h]

中文:
定理 isOpen_iff_of_mem'
  条件: (h : ∞ in s)
  证明: by
  simp [isOpen_def, h]

Depends on / 依赖: isOpen_def
-/
theorem isOpen_iff_of_mem' (h : ∞ in s) :
    IsOpen s ↔ IsCompact ((↑) ⁻¹' s : Set X)ᶜ ∧ IsOpen ((↑) ⁻¹' s : Set X) := by
  simp [isOpen_def, h]

/--
theorem `isOpen_iff_of_mem` / 定理 `isOpen_iff_of_mem`

English:
theorem isOpen_iff_of_mem
  given: (h : ∞ in s)
  proof: by
  simp only [isOpen_iff_of_mem' h, isClosed_compl_iff, and_comm]

中文:
定理 isOpen_iff_of_mem
  条件: (h : ∞ in s)
  证明: by
  simp only [isOpen_iff_of_mem' h, isClosed_compl_iff, and_comm]

Depends on / 依赖: and_comm, isClosed_compl_iff, isOpen_iff_of_mem
-/
theorem isOpen_iff_of_mem (h : ∞ in s) :
    IsOpen s ↔ IsClosed ((↑) ⁻¹' s : Set X)ᶜ ∧ IsCompact ((↑) ⁻¹' s : Set X)ᶜ := by
  simp only [isOpen_iff_of_mem' h, isClosed_compl_iff, and_comm]

/--
theorem `isOpen_iff_of_notMem` / 定理 `isOpen_iff_of_notMem`

English:
theorem isOpen_iff_of_notMem
  given: (h : ∞ ∉ s)
  statement: IsOpen s ↔ IsOpen ((↑) ⁻¹' s : Set X)
  proof: by
  simp [isOpen_def, h]

中文:
定理 isOpen_iff_of_notMem
  条件: (h : ∞ ∉ s)
  结论: 是开集 s ↔ 是开集 ((↑) ⁻¹' s : 集合 X)
  证明: by
  simp [isOpen_def, h]

Depends on / 依赖: isOpen_def
-/
theorem isOpen_iff_of_notMem (h : ∞ ∉ s) : IsOpen s ↔ IsOpen ((↑) ⁻¹' s : Set X) := by
  simp [isOpen_def, h]

/--
theorem `isClosed_iff_of_mem` / 定理 `isClosed_iff_of_mem`

English:
theorem isClosed_iff_of_mem
  given: (h : ∞ in s)
  statement: IsClosed s ↔ IsClosed ((↑) ⁻¹' s : Set X)
  proof: by
  have : ∞ ∉ sᶜ := fun H => H h
  rw [← isOpen_compl_iff]; rw [isOpen_iff_of_notMem this]; rw [← isOpen_compl_iff]; rw [preimage_compl]

中文:
定理 isClosed_iff_of_mem
  条件: (h : ∞ in s)
  结论: 是闭集 s ↔ 是闭集 ((↑) ⁻¹' s : 集合 X)
  证明: by
  have : ∞ ∉ sᶜ := fun H => H h
  rw [← isOpen_compl_iff]; rw [isOpen_iff_of_notMem this]; rw [← isOpen_compl_iff]; rw [preimage_compl]

Depends on / 依赖: isOpen_compl_iff, isOpen_iff_of_notMem, preimage_compl
-/
theorem isClosed_iff_of_mem (h : ∞ in s) : IsClosed s ↔ IsClosed ((↑) ⁻¹' s : Set X) := by
  have : ∞ ∉ sᶜ := fun H => H h
  rw [← isOpen_compl_iff]; rw [isOpen_iff_of_notMem this]; rw [← isOpen_compl_iff]; rw [preimage_compl]

/--
theorem `isClosed_iff_of_notMem` / 定理 `isClosed_iff_of_notMem`

English:
theorem isClosed_iff_of_notMem
  given: (h : ∞ ∉ s)
  proof: by
  rw [← isOpen_compl_iff]; rw [isOpen_iff_of_mem (mem_compl h)]; rw [← preimage_compl]; rw [compl_compl]

@[simp]

中文:
定理 isClosed_iff_of_notMem
  条件: (h : ∞ ∉ s)
  证明: by
  rw [← isOpen_compl_iff]; rw [isOpen_iff_of_mem (mem_compl h)]; rw [← preimage_compl]; rw [compl_compl]

@[simp]

Depends on / 依赖: compl_compl, isOpen_compl_iff, isOpen_iff_of_mem, mem_compl, preimage_compl
-/
theorem isClosed_iff_of_notMem (h : ∞ ∉ s) :
    IsClosed s ↔ IsClosed ((↑) ⁻¹' s : Set X) ∧ IsCompact ((↑) ⁻¹' s : Set X) := by
  rw [← isOpen_compl_iff]; rw [isOpen_iff_of_mem (mem_compl h)]; rw [← preimage_compl]; rw [compl_compl]

@[simp]
/--
theorem `isOpen_image_coe` / 定理 `isOpen_image_coe`

English:
theorem isOpen_image_coe
  given: {s : Set X}
  statement: IsOpen ((↑) '' s : Set (OnePoint X)) ↔ IsOpen s
  proof: by
  rw [isOpen_iff_of_notMem infty_notMem_image_coe]; rw [preimage_image_eq _ coe_injective]

中文:
定理 isOpen_image_coe
  条件: {s : 集合 X}
  结论: 是开集 ((↑) '' s : 集合 (OnePoint X)) ↔ 是开集 s
  证明: by
  rw [isOpen_iff_of_notMem infty_notMem_image_coe]; rw [preimage_image_eq _ coe_injective]

Depends on / 依赖: coe_injective, infty_notMem_image_coe, isOpen_iff_of_notMem, preimage_image_eq
-/
theorem isOpen_image_coe {s : Set X} : IsOpen ((↑) '' s : Set (OnePoint X)) ↔ IsOpen s := by
  rw [isOpen_iff_of_notMem infty_notMem_image_coe]; rw [preimage_image_eq _ coe_injective]

/--
theorem `isOpen_compl_image_coe` / 定理 `isOpen_compl_image_coe`

English:
theorem isOpen_compl_image_coe
  given: {s : Set X}
  proof: by
  rw [isOpen_iff_of_mem]; rw [← preimage_compl]; rw [compl_compl]; rw [preimage_image_eq _ coe_injective]
  exact infty_notMem_image_coe

@[simp]

中文:
定理 isOpen_compl_image_coe
  条件: {s : 集合 X}
  证明: by
  rw [isOpen_iff_of_mem]; rw [← preimage_compl]; rw [compl_compl]; rw [preimage_image_eq _ coe_injective]
  exact infty_notMem_image_coe

@[simp]

Depends on / 依赖: coe_injective, compl_compl, infty_notMem_image_coe, isOpen_iff_of_mem, preimage_compl, preimage_image_eq
-/
theorem isOpen_compl_image_coe {s : Set X} :
    IsOpen ((↑) '' s : Set (OnePoint X))ᶜ ↔ IsClosed s ∧ IsCompact s := by
  rw [isOpen_iff_of_mem]; rw [← preimage_compl]; rw [compl_compl]; rw [preimage_image_eq _ coe_injective]
  exact infty_notMem_image_coe

@[simp]
/--
theorem `isClosed_image_coe` / 定理 `isClosed_image_coe`

English:
theorem isClosed_image_coe
  given: {s : Set X}
  proof: by
  rw [← isOpen_compl_iff]; rw [isOpen_compl_image_coe]

中文:
定理 isClosed_image_coe
  条件: {s : 集合 X}
  证明: by
  rw [← isOpen_compl_iff]; rw [isOpen_compl_image_coe]

Depends on / 依赖: isOpen_compl_iff, isOpen_compl_image_coe
-/
theorem isClosed_image_coe {s : Set X} :
    IsClosed ((↑) '' s : Set (OnePoint X)) ↔ IsClosed s ∧ IsCompact s := by
  rw [← isOpen_compl_iff]; rw [isOpen_compl_image_coe]

/--
Definition of `opensOfCompl` / `opensOfCompl` 的定义

English:
definition opensOfCompl
  signature: (s : Set X) (h₁ : IsClosed s) (h₂ : IsCompact s)
  body: ⟨((↑) '' s)ᶜ, isOpen_compl_image_coe.2 ⟨h₁, h₂⟩⟩

中文:
定义 opensOfCompl
  签名: (s : 集合 X) (h₁ : 是闭集 s) (h₂ : 是紧集 s)
  定义体: ⟨((↑) '' s)ᶜ, isOpen_compl_image_coe.2 ⟨h₁, h₂⟩⟩

Depends on / 依赖: isOpen_compl_image_coe
-/
def opensOfCompl (s : Set X) (h₁ : IsClosed s) (h₂ : IsCompact s) :
    TopologicalSpace.Opens (OnePoint X) :=
  ⟨((↑) '' s)ᶜ, isOpen_compl_image_coe.2 ⟨h₁, h₂⟩⟩

/--
theorem `infty_mem_opensOfCompl` / 定理 `infty_mem_opensOfCompl`

English:
theorem infty_mem_opensOfCompl
  given: {s : Set X} (h₁ : IsClosed s) (h₂ : IsCompact s)
  proof: mem_compl infty_notMem_image_coe

@[continuity]

中文:
定理 infty_mem_opensOfCompl
  条件: {s : 集合 X} (h₁ : 是闭集 s) (h₂ : 是紧集 s)
  证明: mem_compl infty_notMem_image_coe

@[continuity]

Depends on / 依赖: infty_notMem_image_coe, mem_compl
-/
theorem infty_mem_opensOfCompl {s : Set X} (h₁ : IsClosed s) (h₂ : IsCompact s) :
    ∞ in opensOfCompl s h₁ h₂ :=
  mem_compl infty_notMem_image_coe

@[continuity]
/--
theorem `continuous_coe` / 定理 `continuous_coe`

English:
theorem continuous_coe
  statement: Continuous ((↑) : X -> OnePoint X)
  proof: continuous_def.mpr fun _s hs => hs.right

中文:
定理 continuous_coe
  结论: 连续 ((↑) : X -> OnePoint X)
  证明: continuous_def.mpr fun _s hs => hs.right

Depends on / 依赖: continuous_def, continuous_def.mpr, hs.right
-/
theorem continuous_coe : Continuous ((↑) : X -> OnePoint X) :=
  continuous_def.mpr fun _s hs => hs.right

/--
theorem `isOpenMap_coe` / 定理 `isOpenMap_coe`

English:
theorem isOpenMap_coe
  statement: IsOpenMap ((↑) : X -> OnePoint X)
  proof: fun _ => isOpen_image_coe.2

中文:
定理 isOpenMap_coe
  结论: 是开映射 ((↑) : X -> OnePoint X)
  证明: fun _ => isOpen_image_coe.2

Depends on / 依赖: isOpen_image_coe
-/
theorem isOpenMap_coe : IsOpenMap ((↑) : X -> OnePoint X) := fun _ => isOpen_image_coe.2

/--
theorem `isOpenEmbedding_coe` / 定理 `isOpenEmbedding_coe`

English:
theorem isOpenEmbedding_coe
  statement: IsOpenEmbedding ((↑) : X -> OnePoint X)
  proof: .of_continuous_injective_isOpenMap continuous_coe coe_injective isOpenMap_coe

中文:
定理 isOpenEmbedding_coe
  结论: 是开嵌入 ((↑) : X -> OnePoint X)
  证明: .of_continuous_injective_isOpenMap continuous_coe coe_injective isOpenMap_coe

Depends on / 依赖: coe_injective, continuous_coe, isOpenMap_coe, of_continuous_injective_isOpenMap
-/
theorem isOpenEmbedding_coe : IsOpenEmbedding ((↑) : X -> OnePoint X) :=
  .of_continuous_injective_isOpenMap continuous_coe coe_injective isOpenMap_coe

/--
theorem `isOpen_range_coe` / 定理 `isOpen_range_coe`

English:
theorem isOpen_range_coe
  statement: IsOpen (range ((↑) : X -> OnePoint X))
  proof: isOpenEmbedding_coe.isOpen_range

中文:
定理 isOpen_range_coe
  结论: 是开集 (range ((↑) : X -> OnePoint X))
  证明: isOpenEmbedding_coe.isOpen_range

Depends on / 依赖: isOpenEmbedding_coe, isOpenEmbedding_coe.isOpen_range, isOpen_range
-/
theorem isOpen_range_coe : IsOpen (range ((↑) : X -> OnePoint X)) :=
  isOpenEmbedding_coe.isOpen_range

/--
theorem `isClosed_infty` / 定理 `isClosed_infty`

English:
theorem isClosed_infty
  statement: IsClosed ({∞} : Set (OnePoint X))
  proof: by
  rw [← compl_range_coe]; rw [isClosed_compl_iff]
  exact isOpen_range_coe

中文:
定理 isClosed_infty
  结论: 是闭集 ({∞} : 集合 (OnePoint X))
  证明: by
  rw [← compl_range_coe]; rw [isClosed_compl_iff]
  exact isOpen_range_coe

Depends on / 依赖: compl_range_coe, isClosed_compl_iff, isOpen_range_coe
-/
theorem isClosed_infty : IsClosed ({∞} : Set (OnePoint X)) := by
  rw [← compl_range_coe]; rw [isClosed_compl_iff]
  exact isOpen_range_coe

/--
theorem `nhds_coe_eq` / 定理 `nhds_coe_eq`

English:
theorem nhds_coe_eq
  given: (x : X)
  statement: 𝓝 ↑x = map ((↑) : X -> OnePoint X) (𝓝 x)
  proof: (isOpenEmbedding_coe.map_nhds_eq x).symm

中文:
定理 nhds_coe_eq
  条件: (x : X)
  结论: 𝓝 ↑x = map ((↑) : X -> OnePoint X) (𝓝 x)
  证明: (isOpenEmbedding_coe.map_nhds_eq x).symm

Depends on / 依赖: isOpenEmbedding_coe, isOpenEmbedding_coe.map_nhds_eq, map_nhds_eq
-/
theorem nhds_coe_eq (x : X) : 𝓝 ↑x = map ((↑) : X -> OnePoint X) (𝓝 x) :=
  (isOpenEmbedding_coe.map_nhds_eq x).symm

/--
theorem `nhdsWithin_coe_image` / 定理 `nhdsWithin_coe_image`

English:
theorem nhdsWithin_coe_image
  given: (s : Set X) (x : X)
  proof: (isOpenEmbedding_coe.isEmbedding.map_nhdsWithin_eq _ _).symm

中文:
定理 nhdsWithin_coe_image
  条件: (s : 集合 X) (x : X)
  证明: (isOpenEmbedding_coe.isEmbedding.map_nhdsWithin_eq _ _).symm

Depends on / 依赖: isEmbedding, isOpenEmbedding_coe, isOpenEmbedding_coe.isEmbedding.map_nhdsWithin_eq, map_nhdsWithin_eq
-/
theorem nhdsWithin_coe_image (s : Set X) (x : X) :
    𝓝[(↑) '' s] (x : OnePoint X) = map (↑) (𝓝[s] x) :=
  (isOpenEmbedding_coe.isEmbedding.map_nhdsWithin_eq _ _).symm

/--
theorem `nhdsWithin_coe` / 定理 `nhdsWithin_coe`

English:
theorem nhdsWithin_coe
  given: (s : Set (OnePoint X)) (x : X)
  statement: 𝓝[s] ↑x = map (↑) (𝓝[(↑) ⁻¹' s] x)
  proof: (isOpenEmbedding_coe.map_nhdsWithin_preimage_eq _ _).symm

中文:
定理 nhdsWithin_coe
  条件: (s : 集合 (OnePoint X)) (x : X)
  结论: 𝓝[s] ↑x = map (↑) (𝓝[(↑) ⁻¹' s] x)
  证明: (isOpenEmbedding_coe.map_nhdsWithin_preimage_eq _ _).symm

Depends on / 依赖: isOpenEmbedding_coe, isOpenEmbedding_coe.map_nhdsWithin_preimage_eq, map_nhdsWithin_preimage_eq
-/
theorem nhdsWithin_coe (s : Set (OnePoint X)) (x : X) : 𝓝[s] ↑x = map (↑) (𝓝[(↑) ⁻¹' s] x) :=
  (isOpenEmbedding_coe.map_nhdsWithin_preimage_eq _ _).symm

/--
theorem `comap_coe_nhds` / 定理 `comap_coe_nhds`

English:
theorem comap_coe_nhds
  given: (x : X)
  statement: comap ((↑) : X -> OnePoint X) (𝓝 x) = 𝓝 x
  proof: (isOpenEmbedding_coe.isInducing.nhds_eq_comap x).symm

中文:
定理 comap_coe_nhds
  条件: (x : X)
  结论: comap ((↑) : X -> OnePoint X) (𝓝 x) = 𝓝 x
  证明: (isOpenEmbedding_coe.isInducing.nhds_eq_comap x).symm

Depends on / 依赖: isInducing, isOpenEmbedding_coe, isOpenEmbedding_coe.isInducing.nhds_eq_comap, nhds_eq_comap
-/
theorem comap_coe_nhds (x : X) : comap ((↑) : X -> OnePoint X) (𝓝 x) = 𝓝 x :=
  (isOpenEmbedding_coe.isInducing.nhds_eq_comap x).symm

/--
Instance `nhdsNE_coe_neBot` / 实例 `nhdsNE_coe_neBot`

English:
instance nhdsNE_coe_neBot
  signature: (x : X) [h : NeBot (𝓝[!=] x)]
  body: by
  simpa [nhdsWithin_coe, preimage, coe_eq_coe] using! h.map some

中文:
实例 nhdsNE_coe_neBot
  签名: (x : X) [h : NeBot (𝓝[!=] x)]
  定义体: by
  simpa [nhdsWithin_coe, preimage, coe_eq_coe] using! h.map some

Depends on / 依赖: coe_eq_coe, h.map, nhdsWithin_coe, preimage
-/
instance nhdsNE_coe_neBot (x : X) [h : NeBot (𝓝[!=] x)] : NeBot (𝓝[!=] (x : OnePoint X)) := by
  simpa [nhdsWithin_coe, preimage, coe_eq_coe] using! h.map some

/--
theorem `nhdsNE_infty_eq` / 定理 `nhdsNE_infty_eq`

English:
theorem nhdsNE_infty_eq
  statement: 𝓝[!=] (∞ : OnePoint X) = map (↑) (coclosedCompact X)
  proof: by
  refine (nhdsWithin_basis_open ∞ _).ext (hasBasis_coclosedCompact.map _) ?_ ?_
  · rintro s ⟨hs, hso⟩
    refine ⟨_, (isOpen_iff_of_mem hs).mp hso, ?_⟩
    simp
  · rintro s ⟨h₁, h₂⟩
    refine ⟨_, ⟨mem_compl infty_notMem_image_coe, isOpen_compl_image_coe.2 ⟨h₁, h₂⟩⟩, ?_⟩
    simp [compl_image_coe, ← sdiff_eq]

中文:
定理 nhdsNE_infty_eq
  结论: 𝓝[!=] (∞ : OnePoint X) = map (↑) (coclosedCompact X)
  证明: by
  refine (nhdsWithin_basis_open ∞ _).ext (hasBasis_coclosedCompact.map _) ?_ ?_
  · rintro s ⟨hs, hso⟩
    refine ⟨_, (isOpen_iff_of_mem hs).mp hso, ?_⟩
    simp
  · rintro s ⟨h₁, h₂⟩
    refine ⟨_, ⟨mem_compl infty_notMem_image_coe, isOpen_compl_image_coe.2 ⟨h₁, h₂⟩⟩, ?_⟩
    simp [compl_image_coe, ← sdiff_eq]

Depends on / 依赖: compl_image_coe, hasBasis_coclosedCompact, hasBasis_coclosedCompact.map, infty_notMem_image_coe, isOpen_compl_image_coe, isOpen_iff_of_mem, mem_compl, nhdsWithin_basis_open, sdiff_eq
-/
theorem nhdsNE_infty_eq : 𝓝[!=] (∞ : OnePoint X) = map (↑) (coclosedCompact X) := by
  refine (nhdsWithin_basis_open ∞ _).ext (hasBasis_coclosedCompact.map _) ?_ ?_
  · rintro s ⟨hs, hso⟩
    refine ⟨_, (isOpen_iff_of_mem hs).mp hso, ?_⟩
    simp
  · rintro s ⟨h₁, h₂⟩
    refine ⟨_, ⟨mem_compl infty_notMem_image_coe, isOpen_compl_image_coe.2 ⟨h₁, h₂⟩⟩, ?_⟩
    simp [compl_image_coe, ← sdiff_eq]

/--
Instance `nhdsNE_infty_neBot` / 实例 `nhdsNE_infty_neBot`

English:
instance nhdsNE_infty_neBot
  signature: [NoncompactSpace X]
  body: by
  rw [nhdsNE_infty_eq]
  infer_instance

中文:
实例 nhdsNE_infty_neBot
  签名: [Noncompact空间 X]
  定义体: by
  rw [nhdsNE_infty_eq]
  infer_instance

Depends on / 依赖: infer_instance, nhdsNE_infty_eq
-/
instance nhdsNE_infty_neBot [NoncompactSpace X] : NeBot (𝓝[!=] (∞ : OnePoint X)) := by
  rw [nhdsNE_infty_eq]
  infer_instance

instance (priority := 900) nhdsNE_neBot [forall x : X, NeBot (𝓝[!=] x)] [NoncompactSpace X]
    (x : OnePoint X) : NeBot (𝓝[!=] x) :=
  OnePoint.rec OnePoint.nhdsNE_infty_neBot (fun y => OnePoint.nhdsNE_coe_neBot y) x

/--
theorem `nhds_infty_eq` / 定理 `nhds_infty_eq`

English:
theorem nhds_infty_eq
  statement: 𝓝 (∞ : OnePoint X) = map (↑) (coclosedCompact X) ⊔ pure ∞
  proof: by
  rw [← nhdsNE_infty_eq]; rw [nhdsNE_sup_pure]

中文:
定理 nhds_infty_eq
  结论: 𝓝 (∞ : OnePoint X) = map (↑) (coclosedCompact X) ⊔ pure ∞
  证明: by
  rw [← nhdsNE_infty_eq]; rw [nhdsNE_sup_pure]

Depends on / 依赖: nhdsNE_infty_eq, nhdsNE_sup_pure
-/
theorem nhds_infty_eq : 𝓝 (∞ : OnePoint X) = map (↑) (coclosedCompact X) ⊔ pure ∞ := by
  rw [← nhdsNE_infty_eq]; rw [nhdsNE_sup_pure]

/--
theorem `tendsto_coe_infty` / 定理 `tendsto_coe_infty`

English:
theorem tendsto_coe_infty
  statement: Tendsto (↑) (coclosedCompact X) (𝓝 (∞ : OnePoint X))
  proof: by
  rw [nhds_infty_eq]
  exact Filter.Tendsto.mono_right tendsto_map le_sup_left

中文:
定理 tendsto_coe_infty
  结论: 收敛 (↑) (coclosedCompact X) (𝓝 (∞ : OnePoint X))
  证明: by
  rw [nhds_infty_eq]
  exact Filter.Tendsto.mono_right tendsto_map le_sup_left

Depends on / 依赖: Filter, Filter.Tendsto.mono_right, Tendsto, le_sup_left, mono_right, nhds_infty_eq, tendsto_map
-/
theorem tendsto_coe_infty : Tendsto (↑) (coclosedCompact X) (𝓝 (∞ : OnePoint X)) := by
  rw [nhds_infty_eq]
  exact Filter.Tendsto.mono_right tendsto_map le_sup_left

/--
theorem `hasBasis_nhds_infty` / 定理 `hasBasis_nhds_infty`

English:
theorem hasBasis_nhds_infty
  proof: by
  rw [nhds_infty_eq]
  exact (hasBasis_coclosedCompact.map _).sup_pure _

@[simp]

中文:
定理 hasBasis_nhds_infty
  证明: by
  rw [nhds_infty_eq]
  exact (hasBasis_coclosedCompact.map _).sup_pure _

@[simp]

Depends on / 依赖: hasBasis_coclosedCompact, hasBasis_coclosedCompact.map, nhds_infty_eq, sup_pure
-/
theorem hasBasis_nhds_infty :
    (𝓝 (∞ : OnePoint X)).HasBasis (fun s : Set X => IsClosed s ∧ IsCompact s) fun s =>
      (↑) '' sᶜ union {∞} := by
  rw [nhds_infty_eq]
  exact (hasBasis_coclosedCompact.map _).sup_pure _

@[simp]
/--
theorem `comap_coe_nhds_infty` / 定理 `comap_coe_nhds_infty`

English:
theorem comap_coe_nhds_infty
  statement: comap ((↑) : X -> OnePoint X) (𝓝 ∞) = coclosedCompact X
  proof: by
  simp [nhds_infty_eq, comap_sup, comap_map coe_injective]

中文:
定理 comap_coe_nhds_infty
  结论: comap ((↑) : X -> OnePoint X) (𝓝 ∞) = coclosedCompact X
  证明: by
  simp [nhds_infty_eq, comap_sup, comap_map coe_injective]

Depends on / 依赖: coe_injective, comap_map, comap_sup, nhds_infty_eq
-/
theorem comap_coe_nhds_infty : comap ((↑) : X -> OnePoint X) (𝓝 ∞) = coclosedCompact X := by
  simp [nhds_infty_eq, comap_sup, comap_map coe_injective]

/--
theorem `le_nhds_infty` / 定理 `le_nhds_infty`

English:
theorem le_nhds_infty
  given: {f : Filter (OnePoint X)}
  proof: by
  simp only [hasBasis_nhds_infty.ge_iff, and_imp]

中文:
定理 le_nhds_infty
  条件: {f : 滤子 (OnePoint X)}
  证明: by
  simp only [hasBasis_nhds_infty.ge_iff, and_imp]

Depends on / 依赖: and_imp, ge_iff, hasBasis_nhds_infty, hasBasis_nhds_infty.ge_iff
-/
theorem le_nhds_infty {f : Filter (OnePoint X)} :
    f <= 𝓝 ∞ ↔ forall s : Set X, IsClosed s -> IsCompact s -> (↑) '' sᶜ union {∞} in f := by
  simp only [hasBasis_nhds_infty.ge_iff, and_imp]

/--
theorem `ultrafilter_le_nhds_infty` / 定理 `ultrafilter_le_nhds_infty`

English:
theorem ultrafilter_le_nhds_infty
  given: {f : Ultrafilter (OnePoint X)}
  proof: by
  simp only [le_nhds_infty, ← compl_image_coe, Ultrafilter.mem_coe,
    Ultrafilter.compl_mem_iff_notMem]

中文:
定理 ultrafilter_le_nhds_infty
  条件: {f : Ultrafilter (OnePoint X)}
  证明: by
  simp only [le_nhds_infty, ← compl_image_coe, Ultrafilter.mem_coe,
    Ultrafilter.compl_mem_iff_notMem]

Depends on / 依赖: Ultrafilter, Ultrafilter.compl_mem_iff_notMem, Ultrafilter.mem_coe, compl_image_coe, compl_mem_iff_notMem, le_nhds_infty, mem_coe
-/
theorem ultrafilter_le_nhds_infty {f : Ultrafilter (OnePoint X)} :
    (f : Filter (OnePoint X)) <= 𝓝 ∞ ↔ forall s : Set X, IsClosed s -> IsCompact s -> (↑) '' s ∉ f := by
  simp only [le_nhds_infty, ← compl_image_coe, Ultrafilter.mem_coe,
    Ultrafilter.compl_mem_iff_notMem]

/--
theorem `tendsto_nhds_infty'` / 定理 `tendsto_nhds_infty'`

English:
theorem tendsto_nhds_infty'
  given: {α : Type*} {f : OnePoint X -> α} {l : Filter α}
  proof: by
  simp [nhds_infty_eq, and_comm]

中文:
定理 tendsto_nhds_infty'
  条件: {α : 类型} {f : OnePoint X -> α} {l : 滤子 α}
  证明: by
  simp [nhds_infty_eq, and_comm]

Depends on / 依赖: and_comm, nhds_infty_eq
-/
theorem tendsto_nhds_infty' {α : Type*} {f : OnePoint X -> α} {l : Filter α} :
    Tendsto f (𝓝 ∞) l ↔ Tendsto f (pure ∞) l ∧ Tendsto (f ∘ (↑)) (coclosedCompact X) l := by
  simp [nhds_infty_eq, and_comm]

/--
theorem `tendsto_nhds_infty` / 定理 `tendsto_nhds_infty`

English:
theorem tendsto_nhds_infty
  given: {α : Type*} {f : OnePoint X -> α} {l : Filter α}
  proof: tendsto_nhds_infty'.trans by
    simp only [tendsto_pure_left, hasBasis_coclosedCompact.tendsto_left_iff, forall_and,
      and_assoc]

中文:
定理 tendsto_nhds_infty
  条件: {α : 类型} {f : OnePoint X -> α} {l : 滤子 α}
  证明: tendsto_nhds_infty'.trans by
    simp only [tendsto_pure_left, hasBasis_coclosedCompact.tendsto_left_iff, forall_and,
      and_assoc]

Depends on / 依赖: and_assoc, forall_and, hasBasis_coclosedCompact, hasBasis_coclosedCompact.tendsto_left_iff, tendsto_left_iff, tendsto_nhds_infty, tendsto_pure_left
-/
theorem tendsto_nhds_infty {α : Type*} {f : OnePoint X -> α} {l : Filter α} :
    Tendsto f (𝓝 ∞) l ↔
      forall s in l, f ∞ in s ∧ exists t : Set X, IsClosed t ∧ IsCompact t ∧ MapsTo (f ∘ (↑)) tᶜ s :=
tendsto_nhds_infty'.trans by
    simp only [tendsto_pure_left, hasBasis_coclosedCompact.tendsto_left_iff, forall_and,
      and_assoc]

/--
theorem `continuousAt_infty'` / 定理 `continuousAt_infty'`

English:
theorem continuousAt_infty'
  given: {Y : Type*} [TopologicalSpace Y] {f : OnePoint X -> Y}
  proof: tendsto_nhds_infty'.trans and_iff_right (tendsto_pure_nhds _ _)

中文:
定理 continuousAt_infty'
  条件: {Y : 类型} [拓扑空间 Y] {f : OnePoint X -> Y}
  证明: tendsto_nhds_infty'.trans and_iff_right (tendsto_pure_nhds _ _)

Depends on / 依赖: and_iff_right, tendsto_nhds_infty, tendsto_pure_nhds
-/
theorem continuousAt_infty' {Y : Type*} [TopologicalSpace Y] {f : OnePoint X -> Y} :
    ContinuousAt f ∞ ↔ Tendsto (f ∘ (↑)) (coclosedCompact X) (𝓝 (f ∞)) :=
tendsto_nhds_infty'.trans and_iff_right (tendsto_pure_nhds _ _)

/--
theorem `continuousAt_infty` / 定理 `continuousAt_infty`

English:
theorem continuousAt_infty
  given: {Y : Type*} [TopologicalSpace Y] {f : OnePoint X -> Y}
  proof: continuousAt_infty'.trans by simp only [hasBasis_coclosedCompact.tendsto_left_iff, and_assoc]

中文:
定理 continuousAt_infty
  条件: {Y : 类型} [拓扑空间 Y] {f : OnePoint X -> Y}
  证明: continuousAt_infty'.trans by simp only [hasBasis_coclosedCompact.tendsto_left_iff, and_assoc]

Depends on / 依赖: and_assoc, continuousAt_infty, hasBasis_coclosedCompact, hasBasis_coclosedCompact.tendsto_left_iff, tendsto_left_iff
-/
theorem continuousAt_infty {Y : Type*} [TopologicalSpace Y] {f : OnePoint X -> Y} :
    ContinuousAt f ∞ ↔
      forall s in 𝓝 (f ∞), exists t : Set X, IsClosed t ∧ IsCompact t ∧ MapsTo (f ∘ (↑)) tᶜ s :=
continuousAt_infty'.trans by simp only [hasBasis_coclosedCompact.tendsto_left_iff, and_assoc]

/--
theorem `continuousAt_coe` / 定理 `continuousAt_coe`

English:
theorem continuousAt_coe
  given: {Y : Type*} [TopologicalSpace Y] {f : OnePoint X -> Y} {x : X}
  proof: by
  rw [ContinuousAt]; rw [nhds_coe_eq]; rw [tendsto_map'_iff]; rw [ContinuousAt]; rfl

中文:
定理 continuousAt_coe
  条件: {Y : 类型} [拓扑空间 Y] {f : OnePoint X -> Y} {x : X}
  证明: by
  rw [ContinuousAt]; rw [nhds_coe_eq]; rw [tendsto_map'_iff]; rw [ContinuousAt]; rfl

Depends on / 依赖: ContinuousAt, _iff, nhds_coe_eq, tendsto_map
-/
theorem continuousAt_coe {Y : Type*} [TopologicalSpace Y] {f : OnePoint X -> Y} {x : X} :
    ContinuousAt f x ↔ ContinuousAt (f ∘ (↑)) x := by
  rw [ContinuousAt]; rw [nhds_coe_eq]; rw [tendsto_map'_iff]; rw [ContinuousAt]; rfl

/--
lemma `continuous_iff` / 引理 `continuous_iff`

English:
lemma continuous_iff
  given: {Y : Type*} [TopologicalSpace Y] (f : OnePoint X -> Y)
  statement: Continuous f ↔
  proof: by
  simp only [continuous_iff_continuousAt, OnePoint.forall, continuousAt_coe, continuousAt_infty',
    Function.comp_def]

中文:
引理 continuous_iff
  条件: {Y : 类型} [拓扑空间 Y] (f : OnePoint X -> Y)
  结论: 连续 f ↔
  证明: by
  simp only [continuous_iff_continuousAt, OnePoint.forall, continuousAt_coe, continuousAt_infty',
    Function.comp_def]

Depends on / 依赖: Function, Function.comp_def, OnePoint, OnePoint.forall, comp_def, continuousAt_coe, continuousAt_infty, continuous_iff_continuousAt
-/
lemma continuous_iff {Y : Type*} [TopologicalSpace Y] (f : OnePoint X -> Y) : Continuous f ↔
    Tendsto (fun x : X => f x) (coclosedCompact X) (𝓝 (f ∞)) ∧ Continuous (fun x : X => f x) := by
  simp only [continuous_iff_continuousAt, OnePoint.forall, continuousAt_coe, continuousAt_infty',
    Function.comp_def]

/--
Definition of `continuousMapMk` / `continuousMapMk` 的定义

English:
definition continuousMapMk
  signature: {Y : Type*} [TopologicalSpace Y] (f : C(X, Y)) (y : Y)
  body: x.elim y f
  continuous_toFun := by
    rw [continuous_iff]
    refine ⟨h, f.continuous⟩

中文:
定义 continuousMapMk
  签名: {Y : 类型} [拓扑空间 Y] (f : C(X, Y)) (y : Y)
  定义体: x.elim y f
  continuous_toFun := by
    rw [continuous_iff]
    refine ⟨h, f.continuous⟩

Depends on / 依赖: x.elim
-/
def continuousMapMk {Y : Type*} [TopologicalSpace Y] (f : C(X, Y)) (y : Y)
    (h : Tendsto f (coclosedCompact X) (𝓝 y)) : C(OnePoint X, Y) where
  toFun x := x.elim y f
  continuous_toFun := by
    rw [continuous_iff]
    refine ⟨h, f.continuous⟩

/--
lemma `continuous_iff_from_discrete` / 引理 `continuous_iff_from_discrete`

English:
lemma continuous_iff_from_discrete
  statement: {Y : Type*} [TopologicalSpace Y]
  proof: by
  simp [continuous_iff, cocompact_eq_cofinite, continuous_of_discreteTopology]

中文:
引理 continuous_iff_from_discrete
  结论: {Y : 类型} [拓扑空间 Y]
  证明: by
  simp [continuous_iff, cocompact_eq_cofinite, continuous_of_discreteTopology]

Depends on / 依赖: cocompact_eq_cofinite, continuous_iff, continuous_of_discreteTopology
-/
lemma continuous_iff_from_discrete {Y : Type*} [TopologicalSpace Y]
    [DiscreteTopology X] (f : OnePoint X -> Y) :
    Continuous f ↔ Tendsto (fun x : X => f x) cofinite (𝓝 (f ∞)) := by
  simp [continuous_iff, cocompact_eq_cofinite, continuous_of_discreteTopology]

/--
Definition of `continuousMapMkDiscrete` / `continuousMapMkDiscrete` 的定义

English:
definition continuousMapMkDiscrete
  signature: {Y : Type*} [TopologicalSpace Y]
  body: continuousMapMk ⟨f, continuous_of_discreteTopology⟩ y (by simpa [cocompact_eq_cofinite])

中文:
定义 continuousMapMkDiscrete
  签名: {Y : 类型} [拓扑空间 Y]
  定义体: continuousMapMk ⟨f, continuous_of_discreteTopology⟩ y (by simpa [cocompact_eq_cofinite])

Depends on / 依赖: cocompact_eq_cofinite, continuousMapMk, continuous_of_discreteTopology
-/
def continuousMapMkDiscrete {Y : Type*} [TopologicalSpace Y]
    [DiscreteTopology X] (f : X -> Y) (y : Y) (h : Tendsto f cofinite (𝓝 y)) :
    C(OnePoint X, Y) :=
  continuousMapMk ⟨f, continuous_of_discreteTopology⟩ y (by simpa [cocompact_eq_cofinite])

variable (X) in
/--
Definition of `continuousMapDiscreteEquiv` / `continuousMapDiscreteEquiv` 的定义

English:
definition continuousMapDiscreteEquiv
  signature: (Y : Type*) [DiscreteTopology X] [TopologicalSpace Y]
  body: ⟨(f ·), ⟨f ∞, continuous_iff_from_discrete _
  invFun f :=
    { toFun := fun x => match x with
        | ∞ => Classical.choose f.2
        | some x => f.1 x
.mpr Classical.choose_spec f.2 } continuous_toFun := continuous_iff_from_discrete _
  left_inv f := by
    ext x
    refine OnePoint.rec ?_ ?_ x
    · refine tendsto_nhds_unique ?_ (continuous_iff_from_discrete _ |>.mp <| map_continuous f)
      let f' : { f : X -> Y // exists L, Tendsto (fun x : X => f x) cofinite (𝓝 L) } :=
.mp map_continuous f⟩⟩ ⟨fun x => f x, ⟨f ∞, continuous_iff_from_discrete f
      exact Classical.choose_spec f'.property
    · simp

中文:
定义 continuousMapDiscreteEquiv
  签名: (Y : 类型) [离散拓扑 X] [拓扑空间 Y]
  定义体: ⟨(f ·), ⟨f ∞, continuous_iff_from_discrete _
  invFun f :=
    { toFun := fun x => match x with
        | ∞ => Classical.choose f.2
        | some x => f.1 x
.mpr Classical.choose_spec f.2 } continuous_toFun := continuous_iff_from_discrete _
  left_inv f := by
    ext x
    refine OnePoint.rec ?_ ?_ x
    · refine tendsto_nhds_unique ?_ (continuous_iff_from_discrete _ |>.mp <| map_continuous f)
      let f' : { f : X -> Y // exists L, Tendsto (fun x : X => f x) cofinite (𝓝 L) } :=
.mp map_continuous f⟩⟩ ⟨fun x => f x, ⟨f ∞, continuous_iff_from_discrete f
      exact Classical.choose_spec f'.property
    · simp

Depends on / 依赖: continuous_iff_from_discrete
-/
noncomputable def continuousMapDiscreteEquiv (Y : Type*) [DiscreteTopology X] [TopologicalSpace Y]
    [T2Space Y] [Infinite X] :
    C(OnePoint X, Y) ≃ { f : X -> Y // exists L, Tendsto (fun x : X => f x) cofinite (𝓝 L) } where
.mp (map_continuous f)⟩⟩ toFun f := ⟨(f ·), ⟨f ∞, continuous_iff_from_discrete _
  invFun f :=
    { toFun := fun x => match x with
        | ∞ => Classical.choose f.2
        | some x => f.1 x
.mpr Classical.choose_spec f.2 } continuous_toFun := continuous_iff_from_discrete _
  left_inv f := by
    ext x
    refine OnePoint.rec ?_ ?_ x
    · refine tendsto_nhds_unique ?_ (continuous_iff_from_discrete _ |>.mp <| map_continuous f)
      let f' : { f : X -> Y // exists L, Tendsto (fun x : X => f x) cofinite (𝓝 L) } :=
.mp map_continuous f⟩⟩ ⟨fun x => f x, ⟨f ∞, continuous_iff_from_discrete f
      exact Classical.choose_spec f'.property
    · simp

/--
lemma `continuous_iff_from_nat` / 引理 `continuous_iff_from_nat`

English:
lemma continuous_iff_from_nat
  given: {Y : Type*} [TopologicalSpace Y] (f : OnePoint Nat -> Y)
  proof: by
  rw [continuous_iff_from_discrete]; rw [Nat.cofinite_eq_atTop]

中文:
引理 continuous_iff_from_nat
  条件: {Y : 类型} [拓扑空间 Y] (f : OnePoint 自然数 -> Y)
  证明: by
  rw [continuous_iff_from_discrete]; rw [Nat.cofinite_eq_atTop]

Depends on / 依赖: Nat.cofinite_eq_atTop, cofinite_eq_atTop, continuous_iff_from_discrete
-/
lemma continuous_iff_from_nat {Y : Type*} [TopologicalSpace Y] (f : OnePoint Nat -> Y) :
    Continuous f ↔ Tendsto (fun x : Nat => f x) atTop (𝓝 (f ∞)) := by
  rw [continuous_iff_from_discrete]; rw [Nat.cofinite_eq_atTop]

/--
Definition of `continuousMapMkNat` / `continuousMapMkNat` 的定义

English:
definition continuousMapMkNat
  signature: {Y : Type*} [TopologicalSpace Y]
  body: continuousMapMkDiscrete f y (by rwa [Nat.cofinite_eq_atTop])

中文:
定义 continuousMapMk自然数
  签名: {Y : 类型} [拓扑空间 Y]
  定义体: continuousMapMkDiscrete f y (by rwa [Nat.cofinite_eq_atTop])

Depends on / 依赖: Nat.cofinite_eq_atTop, cofinite_eq_atTop, continuousMapMkDiscrete
-/
def continuousMapMkNat {Y : Type*} [TopologicalSpace Y]
    (f : Nat -> Y) (y : Y) (h : Tendsto f atTop (𝓝 y)) :
    C(OnePoint Nat, Y) :=
  continuousMapMkDiscrete f y (by rwa [Nat.cofinite_eq_atTop])

/--
Definition of `continuousMapNatEquiv` / `continuousMapNatEquiv` 的定义

English:
definition continuousMapNatEquiv
  signature: (Y : Type*) [TopologicalSpace Y] [T2Space Y]
  body: by
  refine (continuousMapDiscreteEquiv Nat Y).trans {
    toFun := fun ⟨f, hf⟩ => ⟨f, by rwa [← Nat.cofinite_eq_atTop]⟩
    invFun := fun ⟨f, hf⟩ => ⟨f, by rwa [Nat.cofinite_eq_atTop]⟩ }

中文:
定义 continuousMap自然数Equiv
  签名: (Y : 类型) [拓扑空间 Y] [T2空间 Y]
  定义体: by
  refine (continuousMapDiscreteEquiv Nat Y).trans {
    toFun := fun ⟨f, hf⟩ => ⟨f, by rwa [← Nat.cofinite_eq_atTop]⟩
    invFun := fun ⟨f, hf⟩ => ⟨f, by rwa [Nat.cofinite_eq_atTop]⟩ }

Depends on / 依赖: Nat.cofinite_eq_atTop, cofinite_eq_atTop, continuousMapDiscreteEquiv, invFun
-/
noncomputable def continuousMapNatEquiv (Y : Type*) [TopologicalSpace Y] [T2Space Y] :
    C(OnePoint Nat, Y) ≃ { f : Nat -> Y // exists L, Tendsto (f ·) atTop (𝓝 L) } := by
  refine (continuousMapDiscreteEquiv Nat Y).trans {
    toFun := fun ⟨f, hf⟩ => ⟨f, by rwa [← Nat.cofinite_eq_atTop]⟩
    invFun := fun ⟨f, hf⟩ => ⟨f, by rwa [Nat.cofinite_eq_atTop]⟩ }

/--
theorem `denseRange_coe` / 定理 `denseRange_coe`

English:
theorem denseRange_coe
  given: [NoncompactSpace X]
  statement: DenseRange ((↑) : X -> OnePoint X)
  proof: by
  rw [DenseRange]; rw [← compl_infty]
  exact dense_compl_singleton _

中文:
定理 denseRange_coe
  条件: [Noncompact空间 X]
  结论: DenseRange ((↑) : X -> OnePoint X)
  证明: by
  rw [DenseRange]; rw [← compl_infty]
  exact dense_compl_singleton _

Depends on / 依赖: DenseRange, compl_infty, dense_compl_singleton
-/
theorem denseRange_coe [NoncompactSpace X] : DenseRange ((↑) : X -> OnePoint X) := by
  rw [DenseRange]; rw [← compl_infty]
  exact dense_compl_singleton _

/--
theorem `isDenseEmbedding_coe` / 定理 `isDenseEmbedding_coe`

English:
theorem isDenseEmbedding_coe
  given: [NoncompactSpace X]
  statement: IsDenseEmbedding ((↑) : X -> OnePoint X)
  proof: { isOpenEmbedding_coe with dense := denseRange_coe }

@[simp, norm_cast]

中文:
定理 isDenseEmbedding_coe
  条件: [Noncompact空间 X]
  结论: 是稠密嵌入 ((↑) : X -> OnePoint X)
  证明: { isOpenEmbedding_coe with dense := denseRange_coe }

@[simp, norm_cast]

Depends on / 依赖: denseRange_coe, isOpenEmbedding_coe
-/
theorem isDenseEmbedding_coe [NoncompactSpace X] : IsDenseEmbedding ((↑) : X -> OnePoint X) :=
  { isOpenEmbedding_coe with dense := denseRange_coe }

@[simp, norm_cast]
/--
theorem `specializes_coe` / 定理 `specializes_coe`

English:
theorem specializes_coe
  given: {x y : X}
  statement: (x : OnePoint X) ⤳ y ↔ x ⤳ y
  proof: isOpenEmbedding_coe.isInducing.specializes_iff

@[simp, norm_cast]

中文:
定理 specializes_coe
  条件: {x y : X}
  结论: (x : OnePoint X) ⤳ y ↔ x ⤳ y
  证明: isOpenEmbedding_coe.isInducing.specializes_iff

@[simp, norm_cast]

Depends on / 依赖: isInducing, isOpenEmbedding_coe, isOpenEmbedding_coe.isInducing.specializes_iff, specializes_iff
-/
theorem specializes_coe {x y : X} : (x : OnePoint X) ⤳ y ↔ x ⤳ y :=
  isOpenEmbedding_coe.isInducing.specializes_iff

@[simp, norm_cast]
/--
theorem `inseparable_coe` / 定理 `inseparable_coe`

English:
theorem inseparable_coe
  given: {x y : X}
  statement: Inseparable (x : OnePoint X) y ↔ Inseparable x y
  proof: isOpenEmbedding_coe.isInducing.inseparable_iff

中文:
定理 inseparable_coe
  条件: {x y : X}
  结论: 不可分 (x : OnePoint X) y ↔ 不可分 x y
  证明: isOpenEmbedding_coe.isInducing.inseparable_iff

Depends on / 依赖: inseparable_iff, isInducing, isOpenEmbedding_coe, isOpenEmbedding_coe.isInducing.inseparable_iff
-/
theorem inseparable_coe {x y : X} : Inseparable (x : OnePoint X) y ↔ Inseparable x y :=
  isOpenEmbedding_coe.isInducing.inseparable_iff

/--
theorem `not_specializes_infty_coe` / 定理 `not_specializes_infty_coe`

English:
theorem not_specializes_infty_coe
  given: {x : X}
  statement: ¬Specializes ∞ (x : OnePoint X)
  proof: isClosed_infty.not_specializes rfl (coe_ne_infty x)

中文:
定理 not_specializes_infty_coe
  条件: {x : X}
  结论: ¬Specializes ∞ (x : OnePoint X)
  证明: isClosed_infty.not_specializes rfl (coe_ne_infty x)

Depends on / 依赖: coe_ne_infty, isClosed_infty, isClosed_infty.not_specializes, not_specializes
-/
theorem not_specializes_infty_coe {x : X} : ¬Specializes ∞ (x : OnePoint X) :=
  isClosed_infty.not_specializes rfl (coe_ne_infty x)

/--
theorem `not_inseparable_infty_coe` / 定理 `not_inseparable_infty_coe`

English:
theorem not_inseparable_infty_coe
  given: {x : X}
  statement: ¬Inseparable ∞ (x : OnePoint X)
  proof: fun h =>
  not_specializes_infty_coe h.specializes

中文:
定理 not_inseparable_infty_coe
  条件: {x : X}
  结论: ¬不可分 ∞ (x : OnePoint X)
  证明: fun h =>
  not_specializes_infty_coe h.specializes
-/
theorem not_inseparable_infty_coe {x : X} : ¬Inseparable ∞ (x : OnePoint X) := fun h =>
  not_specializes_infty_coe h.specializes

/--
theorem `not_inseparable_coe_infty` / 定理 `not_inseparable_coe_infty`

English:
theorem not_inseparable_coe_infty
  given: {x : X}
  statement: ¬Inseparable (x : OnePoint X) ∞
  proof: fun h =>
  not_specializes_infty_coe h.specializes'

中文:
定理 not_inseparable_coe_infty
  条件: {x : X}
  结论: ¬不可分 (x : OnePoint X) ∞
  证明: fun h =>
  not_specializes_infty_coe h.specializes'
-/
theorem not_inseparable_coe_infty {x : X} : ¬Inseparable (x : OnePoint X) ∞ := fun h =>
  not_specializes_infty_coe h.specializes'

/--
theorem `inseparable_iff` / 定理 `inseparable_iff`

English:
theorem inseparable_iff
  given: {x y : OnePoint X}
  proof: by
  induction x using OnePoint.rec <;> induction y using OnePoint.rec <;>
    simp [not_inseparable_infty_coe, not_inseparable_coe_infty, coe_eq_coe, Inseparable.refl]

中文:
定理 inseparable_iff
  条件: {x y : OnePoint X}
  证明: by
  induction x using OnePoint.rec <;> induction y using OnePoint.rec <;>
    simp [not_inseparable_infty_coe, not_inseparable_coe_infty, coe_eq_coe, Inseparable.refl]

Depends on / 依赖: Inseparable, Inseparable.refl, OnePoint, OnePoint.rec, coe_eq_coe, not_inseparable_coe_infty, not_inseparable_infty_coe
-/
theorem inseparable_iff {x y : OnePoint X} :
    Inseparable x y ↔ x = ∞ ∧ y = ∞ ∨ exists x' : X, x = x' ∧ exists y' : X, y = y' ∧ Inseparable x' y' := by
  induction x using OnePoint.rec <;> induction y using OnePoint.rec <;>
    simp [not_inseparable_infty_coe, not_inseparable_coe_infty, coe_eq_coe, Inseparable.refl]

/--
theorem `continuous_map_iff` / 定理 `continuous_map_iff`

English:
theorem continuous_map_iff
  given: [TopologicalSpace Y] {f : X -> Y}
  proof: by
  simp_rw [continuous_iff, map_some, ← comap_coe_nhds_infty, tendsto_comap_iff, map_infty,
    isOpenEmbedding_coe.isInducing.continuous_iff (Y := Y)]
  exact and_comm

中文:
定理 continuous_map_iff
  条件: [拓扑空间 Y] {f : X -> Y}
  证明: by
  simp_rw [continuous_iff, map_some, ← comap_coe_nhds_infty, tendsto_comap_iff, map_infty,
    isOpenEmbedding_coe.isInducing.continuous_iff (Y := Y)]
  exact and_comm

Depends on / 依赖: and_comm, comap_coe_nhds_infty, continuous_iff, isInducing, isOpenEmbedding_coe, isOpenEmbedding_coe.isInducing.continuous_iff, map_infty, map_some, simp_rw, tendsto_comap_iff
-/
theorem continuous_map_iff [TopologicalSpace Y] {f : X -> Y} :
    Continuous (OnePoint.map f) ↔
      Continuous f ∧ Tendsto f (coclosedCompact X) (coclosedCompact Y) := by
  simp_rw [continuous_iff, map_some, ← comap_coe_nhds_infty, tendsto_comap_iff, map_infty,
    isOpenEmbedding_coe.isInducing.continuous_iff (Y := Y)]
  exact and_comm

/--
theorem `continuous_map` / 定理 `continuous_map`

English:
theorem continuous_map
  statement: [TopologicalSpace Y] {f : X -> Y} (hc : Continuous f)
  proof: continuous_map_iff.mpr ⟨hc, h⟩

中文:
定理 continuous_map
  结论: [拓扑空间 Y] {f : X -> Y} (hc : 连续 f)
  证明: continuous_map_iff.mpr ⟨hc, h⟩

Depends on / 依赖: continuous_map_iff, continuous_map_iff.mpr
-/
theorem continuous_map [TopologicalSpace Y] {f : X -> Y} (hc : Continuous f)
    (h : Tendsto f (coclosedCompact X) (coclosedCompact Y)) :
    Continuous (OnePoint.map f) :=
  continuous_map_iff.mpr ⟨hc, h⟩

/-!
### Compactness and separation properties

In this section we prove that `OnePoint X` is a compact space; it is a T₀ (resp., T₁) space if
the original space satisfies the same separation axiom. If the original space is a locally compact
Hausdorff space, then `OnePoint X` is a normal (hence, T₃ and Hausdorff) space.

Finally, if the original space `X` is *not* compact and is a preconnected space, then
`OnePoint X` is a connected space.
-/

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CompactSpace (OnePoint X)
  body: by
    have : Tendsto ((↑) : X -> OnePoint X) (cocompact X) (𝓝 ∞) := by
      rw [nhds_infty_eq]
      exact (tendsto_map.mono_left cocompact_le_coclosedCompact).mono_right le_sup_left
    rw [← insert_none_range_some X]
    exact this.isCompact_insert_range_of_cocompact continuous_coe

中文:
实例 :
  签名: 紧空间 (OnePoint X)
  定义体: by
    have : Tendsto ((↑) : X -> OnePoint X) (cocompact X) (𝓝 ∞) := by
      rw [nhds_infty_eq]
      exact (tendsto_map.mono_left cocompact_le_coclosedCompact).mono_right le_sup_left
    rw [← insert_none_range_some X]
    exact this.isCompact_insert_range_of_cocompact continuous_coe

Depends on / 依赖: OnePoint, Tendsto, cocompact, cocompact_le_coclosedCompact, continuous_coe, insert_none_range_some, isCompact_insert_range_of_cocompact, le_sup_left, mono_left, mono_right, nhds_infty_eq, tendsto_map, tendsto_map.mono_left, this.isCompact_insert_range_of_cocompact
-/
instance : CompactSpace (OnePoint X) where
  isCompact_univ := by
    have : Tendsto ((↑) : X -> OnePoint X) (cocompact X) (𝓝 ∞) := by
      rw [nhds_infty_eq]
      exact (tendsto_map.mono_left cocompact_le_coclosedCompact).mono_right le_sup_left
    rw [← insert_none_range_some X]
    exact this.isCompact_insert_range_of_cocompact continuous_coe

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [T0Space
  signature: X] : T0Space (OnePoint X)
  body: by
  refine ⟨fun x y hxy => ?_⟩
  rcases inseparable_iff.1 hxy with (⟨rfl, rfl⟩ | ⟨x, rfl, y, rfl, h⟩)
  exacts [rfl, congr_arg some h.eq]

中文:
实例 [T0空间
  签名: X] : T0空间 (OnePoint X)
  定义体: by
  refine ⟨fun x y hxy => ?_⟩
  rcases inseparable_iff.1 hxy with (⟨rfl, rfl⟩ | ⟨x, rfl, y, rfl, h⟩)
  exacts [rfl, congr_arg some h.eq]

Depends on / 依赖: congr_arg, exacts, h.eq, inseparable_iff
-/
instance [T0Space X] : T0Space (OnePoint X) := by
  refine ⟨fun x y hxy => ?_⟩
  rcases inseparable_iff.1 hxy with (⟨rfl, rfl⟩ | ⟨x, rfl, y, rfl, h⟩)
  exacts [rfl, congr_arg some h.eq]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [T1Space
  signature: X] : T1Space (OnePoint X) where
  body: by
    induction z using OnePoint.rec
    · exact isClosed_infty
    · rw [← image_singleton, isClosed_image_coe]
      exact ⟨isClosed_singleton, isCompact_singleton⟩

中文:
实例 [T1空间
  签名: X] : T1空间 (OnePoint X) where
  定义体: by
    induction z using OnePoint.rec
    · exact isClosed_infty
    · rw [← image_singleton, isClosed_image_coe]
      exact ⟨isClosed_singleton, isCompact_singleton⟩

Depends on / 依赖: OnePoint, OnePoint.rec, image_singleton, isClosed_image_coe, isClosed_infty, isClosed_singleton, isCompact_singleton
-/
instance [T1Space X] : T1Space (OnePoint X) where
  t1 z := by
    induction z using OnePoint.rec
    · exact isClosed_infty
    · rw [← image_singleton, isClosed_image_coe]
      exact ⟨isClosed_singleton, isCompact_singleton⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [WeaklyLocallyCompactSpace
  signature: X] [R1Space X] : NormalSpace (OnePoint X)
  body: by
  suffices R1Space (OnePoint X) by infer_instance
  have key : forall z : X, Disjoint (𝓝 (some z)) (𝓝 ∞) := fun z => by
    rw [nhds_infty_eq]; rw [disjoint_sup_right]; rw [nhds_coe_eq]; rw [coclosedCompact_eq_cocompact]; rw [disjoint_map coe_injective]; rw [← principal_singleton]; rw [disjoint_principal_right]; rw [compl_infty]
    exact ⟨disjoint_nhds_cocompact z, range_mem_map⟩
  refine ⟨fun x y => ?_⟩
  induction x using OnePoint.rec <;> induction y using OnePoint.rec
  · exact .inl le_rfl
  · exact .inr (key _).symm
  · exact .inr (key _)
  · rw [nhds_coe_eq, nhds_coe_eq, disjoint_map coe_injective, specializes_coe]
    apply specializes_or_disjoint_nhds

中文:
实例 [WeaklyLocallyCompact空间
  签名: X] [R1空间 X] : 正规空间 (OnePoint X)
  定义体: by
  suffices R1Space (OnePoint X) by infer_instance
  have key : forall z : X, Disjoint (𝓝 (some z)) (𝓝 ∞) := fun z => by
    rw [nhds_infty_eq]; rw [disjoint_sup_right]; rw [nhds_coe_eq]; rw [coclosedCompact_eq_cocompact]; rw [disjoint_map coe_injective]; rw [← principal_singleton]; rw [disjoint_principal_right]; rw [compl_infty]
    exact ⟨disjoint_nhds_cocompact z, range_mem_map⟩
  refine ⟨fun x y => ?_⟩
  induction x using OnePoint.rec <;> induction y using OnePoint.rec
  · exact .inl le_rfl
  · exact .inr (key _).symm
  · exact .inr (key _)
  · rw [nhds_coe_eq, nhds_coe_eq, disjoint_map coe_injective, specializes_coe]
    apply specializes_or_disjoint_nhds

Depends on / 依赖: Disjoint, OnePoint, OnePoint.rec, R1Space, coclosedCompact_eq_cocompact, coe_injective, compl_infty, disjoint_map, disjoint_nhds_cocompact, disjoint_principal_right, disjoint_sup_right, infer_instance, le_rfl, nhds_coe_eq, nhds_infty_eq, principal_singleton, range_mem_map
-/
instance [WeaklyLocallyCompactSpace X] [R1Space X] : NormalSpace (OnePoint X) := by
  suffices R1Space (OnePoint X) by infer_instance
  have key : forall z : X, Disjoint (𝓝 (some z)) (𝓝 ∞) := fun z => by
    rw [nhds_infty_eq]; rw [disjoint_sup_right]; rw [nhds_coe_eq]; rw [coclosedCompact_eq_cocompact]; rw [disjoint_map coe_injective]; rw [← principal_singleton]; rw [disjoint_principal_right]; rw [compl_infty]
    exact ⟨disjoint_nhds_cocompact z, range_mem_map⟩
  refine ⟨fun x y => ?_⟩
  induction x using OnePoint.rec <;> induction y using OnePoint.rec
  · exact .inl le_rfl
  · exact .inr (key _).symm
  · exact .inr (key _)
  · rw [nhds_coe_eq, nhds_coe_eq, disjoint_map coe_injective, specializes_coe]
    apply specializes_or_disjoint_nhds

/-- The one point compactification of a weakly locally compact Hausdorff space is a T₄
(hence, Hausdorff and regular) topological space. -/
example [WeaklyLocallyCompactSpace X] [T2Space X] : T4Space (OnePoint X) := inferInstance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [PreconnectedSpace
  signature: X] [NoncompactSpace X] : ConnectedSpace (OnePoint X) where
  body: isDenseEmbedding_coe.isDenseInducing.preconnectedSpace
  toNonempty := inferInstance

中文:
实例 [预连通空间
  签名: X] [Noncompact空间 X] : 连通空间 (OnePoint X) where
  定义体: isDenseEmbedding_coe.isDenseInducing.preconnectedSpace
  toNonempty := inferInstance

Depends on / 依赖: isDenseEmbedding_coe, isDenseEmbedding_coe.isDenseInducing.preconnectedSpace, isDenseInducing, preconnectedSpace
-/
instance [PreconnectedSpace X] [NoncompactSpace X] : ConnectedSpace (OnePoint X) where
  toPreconnectedSpace := isDenseEmbedding_coe.isDenseInducing.preconnectedSpace
  toNonempty := inferInstance

/--
theorem `not_continuous_cofiniteTopology_of_symm` / 定理 `not_continuous_cofiniteTopology_of_symm`

English:
theorem not_continuous_cofiniteTopology_of_symm
  given: [Infinite X] [DiscreteTopology X]
  proof: by
  inhabit X
  simp only [continuous_iff_continuousAt, ContinuousAt, not_forall]
  use CofiniteTopology.of ↑(default : X)
  simpa [nhds_coe_eq, nhds_discrete, CofiniteTopology.nhds_eq, Equiv.symm_apply_eq,
    Set.compl_def, Set.mem_singleton_iff] using (finite_singleton _).infinite_compl

中文:
定理 not_continuous_cofiniteTopology_of_symm
  条件: [无限 X] [离散拓扑 X]
  证明: by
  inhabit X
  simp only [continuous_iff_continuousAt, ContinuousAt, not_forall]
  use CofiniteTopology.of ↑(default : X)
  simpa [nhds_coe_eq, nhds_discrete, CofiniteTopology.nhds_eq, Equiv.symm_apply_eq,
    Set.compl_def, Set.mem_singleton_iff] using (finite_singleton _).infinite_compl

Depends on / 依赖: CofiniteTopology, CofiniteTopology.nhds_eq, CofiniteTopology.of, ContinuousAt, Equiv.symm_apply_eq, Set.compl_def, Set.mem_singleton_iff, compl_def, continuous_iff_continuousAt, finite_singleton, infinite_compl, inhabit, mem_singleton_iff, nhds_coe_eq, nhds_discrete, nhds_eq, not_forall, symm_apply_eq
-/
theorem not_continuous_cofiniteTopology_of_symm [Infinite X] [DiscreteTopology X] :
    ¬Continuous (@CofiniteTopology.of (OnePoint X)).symm := by
  inhabit X
  simp only [continuous_iff_continuousAt, ContinuousAt, not_forall]
  use CofiniteTopology.of ↑(default : X)
  simpa [nhds_coe_eq, nhds_discrete, CofiniteTopology.nhds_eq, Equiv.symm_apply_eq,
    Set.compl_def, Set.mem_singleton_iff] using (finite_singleton _).infinite_compl

instance (X : Type*) [TopologicalSpace X] [DiscreteTopology X] :
    TotallySeparatedSpace (OnePoint X) where
  isTotallySeparated_univ x _ y _ hxy := by
    cases x with
    | infty =>
      refine ⟨{y}ᶜ, {y}, isOpen_compl_singleton, ?_, hxy, rfl, (compl_union_self _).symm.subset,
        disjoint_compl_left⟩
      rw [OnePoint.isOpen_iff_of_notMem]
      exacts [isOpen_discrete _, hxy]
    | coe val =>
      refine ⟨{some val}, {some val}ᶜ, ?_, isOpen_compl_singleton, rfl, hxy.symm, by simp,
        disjoint_compl_right⟩
      rw [OnePoint.isOpen_iff_of_notMem]
      exacts [isOpen_discrete _, (Option.some_ne_none val).symm]

section Uniqueness

variable [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
  (y : Y) (f : X -> Y) (hf : IsEmbedding f) (hy : range f = {y}ᶜ)

open scoped Classical in
/--
Definition of `equivOfIsEmbeddingOfRangeEq` / `equivOfIsEmbeddingOfRangeEq` 的定义

English:
definition equivOfIsEmbeddingOfRangeEq
  signature: :
  body: have _i := hf.t2Space
  have : Tendsto f (coclosedCompact X) (𝓝 y) := by
    rw [coclosedCompact_eq_cocompact]; rw [hasBasis_cocompact.tendsto_left_iff]
    intro N hN
    obtain ⟨U, hU₁, hU₂, hU₃⟩ := mem_nhds_iff.mp hN
    refine ⟨f⁻¹' Uᶜ, ?_, by simpa using (mapsTo_preimage f U).mono_right hU₁⟩
    rw [hf.isCompact_iff]; rw [image_preimage_eq_iff.mpr (by simpa [hy])]
    exact (isClosed_compl_iff.mpr hU₂).isCompact
  let e : OnePoint X ≃ Y :=
    { toFun := fun p => p.elim y f
      invFun := fun q => if hq : q = y then ∞ else ↑(show q in range f by simpa [hy]).choose
      left_inv := fun p => by
        induction p using OnePoint.rec with
        | infty => simp
        | coe p =>
          have hp : f p != y := by simpa [hy] using mem_range_self (f := f) p
          simpa [hp] using hf.injective (mem_range_self p).choose_spec
      right_inv := fun q => by
        rcases eq_or_ne q y with rfl | hq
        · simp
        · have hq' : q in range f := by simpa [hy]
          simpa [hq] using hq'.choose_spec }
Continuous.homeoOfEquivCompactToT2 (continuous_iff e).mpr ⟨this, hf.continuous⟩

@[simp]

中文:
定义 equivOfIsEmbeddingOfRangeEq
  签名: :
  定义体: have _i := hf.t2Space
  have : Tendsto f (coclosedCompact X) (𝓝 y) := by
    rw [coclosedCompact_eq_cocompact]; rw [hasBasis_cocompact.tendsto_left_iff]
    intro N hN
    obtain ⟨U, hU₁, hU₂, hU₃⟩ := mem_nhds_iff.mp hN
    refine ⟨f⁻¹' Uᶜ, ?_, by simpa using (mapsTo_preimage f U).mono_right hU₁⟩
    rw [hf.isCompact_iff]; rw [image_preimage_eq_iff.mpr (by simpa [hy])]
    exact (isClosed_compl_iff.mpr hU₂).isCompact
  let e : OnePoint X ≃ Y :=
    { toFun := fun p => p.elim y f
      invFun := fun q => if hq : q = y then ∞ else ↑(show q in range f by simpa [hy]).choose
      left_inv := fun p => by
        induction p using OnePoint.rec with
        | infty => simp
        | coe p =>
          have hp : f p != y := by simpa [hy] using mem_range_self (f := f) p
          simpa [hp] using hf.injective (mem_range_self p).choose_spec
      right_inv := fun q => by
        rcases eq_or_ne q y with rfl | hq
        · simp
        · have hq' : q in range f := by simpa [hy]
          simpa [hq] using hq'.choose_spec }
Continuous.homeoOfEquivCompactToT2 (continuous_iff e).mpr ⟨this, hf.continuous⟩

@[simp]

Depends on / 依赖: OnePoint, Tendsto, coclosedCompact, coclosedCompact_eq_cocompact, hasBasis_cocompact, hasBasis_cocompact.tendsto_left_iff, hf.isCompact_iff, hf.t2Space, image_preimage_eq_iff, image_preimage_eq_iff.mpr, invFun, isClosed_compl_iff, isClosed_compl_iff.mpr, isCompact, isCompact_iff, mapsTo_preimage, mem_nhds_iff, mem_nhds_iff.mp, mono_right, p.elim
-/
noncomputable def equivOfIsEmbeddingOfRangeEq :
    OnePoint X ≃ₜ Y :=
  have _i := hf.t2Space
  have : Tendsto f (coclosedCompact X) (𝓝 y) := by
    rw [coclosedCompact_eq_cocompact]; rw [hasBasis_cocompact.tendsto_left_iff]
    intro N hN
    obtain ⟨U, hU₁, hU₂, hU₃⟩ := mem_nhds_iff.mp hN
    refine ⟨f⁻¹' Uᶜ, ?_, by simpa using (mapsTo_preimage f U).mono_right hU₁⟩
    rw [hf.isCompact_iff]; rw [image_preimage_eq_iff.mpr (by simpa [hy])]
    exact (isClosed_compl_iff.mpr hU₂).isCompact
  let e : OnePoint X ≃ Y :=
    { toFun := fun p => p.elim y f
      invFun := fun q => if hq : q = y then ∞ else ↑(show q in range f by simpa [hy]).choose
      left_inv := fun p => by
        induction p using OnePoint.rec with
        | infty => simp
        | coe p =>
          have hp : f p != y := by simpa [hy] using mem_range_self (f := f) p
          simpa [hp] using hf.injective (mem_range_self p).choose_spec
      right_inv := fun q => by
        rcases eq_or_ne q y with rfl | hq
        · simp
        · have hq' : q in range f := by simpa [hy]
          simpa [hq] using hq'.choose_spec }
Continuous.homeoOfEquivCompactToT2 (continuous_iff e).mpr ⟨this, hf.continuous⟩

@[simp]
/--
lemma `equivOfIsEmbeddingOfRangeEq_apply_coe` / 引理 `equivOfIsEmbeddingOfRangeEq_apply_coe`

English:
lemma equivOfIsEmbeddingOfRangeEq_apply_coe
  given: (x : X)
  proof: rfl

@[simp]

中文:
引理 equivOfIsEmbeddingOfRangeEq_apply_coe
  条件: (x : X)
  证明: rfl

@[simp]
-/
lemma equivOfIsEmbeddingOfRangeEq_apply_coe (x : X) :
    equivOfIsEmbeddingOfRangeEq y f hf hy x = f x :=
  rfl

@[simp]
/--
lemma `equivOfIsEmbeddingOfRangeEq_apply_infty` / 引理 `equivOfIsEmbeddingOfRangeEq_apply_infty`

English:
lemma equivOfIsEmbeddingOfRangeEq_apply_infty
  proof: rfl

中文:
引理 equivOfIsEmbeddingOfRangeEq_apply_infty
  证明: rfl
-/
lemma equivOfIsEmbeddingOfRangeEq_apply_infty :
    equivOfIsEmbeddingOfRangeEq y f hf hy ∞ = y :=
  rfl

end Uniqueness

end OnePoint

namespace Homeomorph

variable [TopologicalSpace X] [TopologicalSpace Y]

open OnePoint

/-- Extend a homeomorphism of topological spaces
to the homeomorphism of their one point compactifications. -/
@[simps]
/--
Definition of `onePointCongr` / `onePointCongr` 的定义

English:
definition onePointCongr
  signature: (h : X ≃ₜ Y)
  body: h.toEquiv.withTopCongr
  toFun := OnePoint.map h
  invFun := OnePoint.map h.symm
  continuous_toFun := continuous_map (map_continuous h) h.map_coclosedCompact.le
  continuous_invFun := continuous_map (map_continuous h.symm) h.symm.map_coclosedCompact.le

中文:
定义 onePointCongr
  签名: (h : X ≃ₜ Y)
  定义体: h.toEquiv.withTopCongr
  toFun := OnePoint.map h
  invFun := OnePoint.map h.symm
  continuous_toFun := continuous_map (map_continuous h) h.map_coclosedCompact.le
  continuous_invFun := continuous_map (map_continuous h.symm) h.symm.map_coclosedCompact.le

Depends on / 依赖: h.toEquiv.withTopCongr, toEquiv, withTopCongr
-/
def onePointCongr (h : X ≃ₜ Y) : OnePoint X ≃ₜ OnePoint Y where
  __ := h.toEquiv.withTopCongr
  toFun := OnePoint.map h
  invFun := OnePoint.map h.symm
  continuous_toFun := continuous_map (map_continuous h) h.map_coclosedCompact.le
  continuous_invFun := continuous_map (map_continuous h.symm) h.symm.map_coclosedCompact.le

end Homeomorph

/--
theorem `Continuous.homeoOfEquivCompactToT2.t1_counterexample` / 定理 `Continuous.homeoOfEquivCompactToT2.t1_counterexample`

English:
theorem Continuous.homeoOfEquivCompactToT2.t1_counterexample
  proof: ⟨OnePoint Nat, CofiniteTopology (OnePoint Nat), inferInstance, inferInstance, inferInstance,
    inferInstance, CofiniteTopology.of, CofiniteTopology.continuous_of,
    OnePoint.not_continuous_cofiniteTopology_of_symm⟩

中文:
定理 连续.homeoOfEquivCompactToT2.t1_counterexample
  证明: ⟨OnePoint Nat, CofiniteTopology (OnePoint Nat), inferInstance, inferInstance, inferInstance,
    inferInstance, CofiniteTopology.of, CofiniteTopology.continuous_of,
    OnePoint.not_continuous_cofiniteTopology_of_symm⟩

Depends on / 依赖: CofiniteTopology, CofiniteTopology.continuous_of, CofiniteTopology.of, OnePoint, OnePoint.not_continuous_cofiniteTopology_of_symm, continuous_of, not_continuous_cofiniteTopology_of_symm
-/
theorem Continuous.homeoOfEquivCompactToT2.t1_counterexample :
    exists (α β : Type) (_ : TopologicalSpace α) (_ : TopologicalSpace β),
      CompactSpace α ∧ T1Space β ∧ exists f : α ≃ β, Continuous f ∧ ¬Continuous f.symm :=
  ⟨OnePoint Nat, CofiniteTopology (OnePoint Nat), inferInstance, inferInstance, inferInstance,
    inferInstance, CofiniteTopology.of, CofiniteTopology.continuous_of,
    OnePoint.not_continuous_cofiniteTopology_of_symm⟩
