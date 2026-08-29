/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Topology.Connected.LocallyConnected
public import Mathlib.Topology.Sets.Closeds

/-!
# Locally constant functions

This file sets up the theory of locally constant function from a topological space to a type.

## Main definitions and constructions

* `IsLocallyConstant f` : a map `f : X → Y` where `X` is a topological space is locally
                            constant if every set in `Y` has an open preimage.
* `LocallyConstant X Y` : the type of locally constant maps from `X` to `Y`
* `LocallyConstant.map` : push-forward of locally constant maps
* `LocallyConstant.comap` : pull-back of locally constant maps
-/

@[expose] public section

variable {X Y Z α : Type*} [TopologicalSpace X]

open Set Filter
open scoped Topology

/--
Definition of `IsLocallyConstant` / `IsLocallyConstant` 的定义

English:
definition IsLocallyConstant
  signature: (f : X -> Y)
  body: forall s : Set Y, IsOpen (f ⁻¹' s)

中文:
定义 IsLocallyConstant
  签名: (f : X -> Y)
  定义体: forall s : Set Y, IsOpen (f ⁻¹' s)

Depends on / 依赖: IsOpen
-/
def IsLocallyConstant (f : X -> Y) : Prop :=
  forall s : Set Y, IsOpen (f ⁻¹' s)

namespace IsLocallyConstant

open List in
/--
theorem `tfae` / 定理 `tfae`

English:
theorem tfae
  given: (f : X -> Y)
  proof: by
  tfae_have 1 -> 4 := fun h y => h {y}
  tfae_have 4 -> 3 := fun h x => h (f x)
  tfae_have 3 -> 2 := fun h x => IsOpen.mem_nhds (h x) rfl
  tfae_have 2 -> 5
  | h, x => by
    rcases mem_nhds_iff.1 (h x) with ⟨U, eq, hU, hx⟩
    exact ⟨U, hU, hx, eq⟩
  tfae_have 5 -> 1
  | h, s => by
    refine 

中文:
定理 tfae
  条件: (f : X -> Y)
  证明: by
  tfae_have 1 -> 4 := fun h y => h {y}
  tfae_have 4 -> 3 := fun h x => h (f x)
  tfae_have 3 -> 2 := fun h x => IsOpen.mem_nhds (h x) rfl
  tfae_have 2 -> 5
  | h, x => by
    rcases mem_nhds_iff.1 (h x) with ⟨U, eq, hU, hx⟩
    exact ⟨U, hU, hx, eq⟩
  tfae_have 5 -> 1
  | h, s => by
    refine 
-/
protected theorem tfae (f : X -> Y) :
    TFAE [IsLocallyConstant f,
      forall x, forallᶠ x' in 𝓝 x, f x' = f x,
      forall x, IsOpen { x' | f x' = f x },
      forall y, IsOpen (f ⁻¹' {y}),
      forall x, exists U : Set X, IsOpen U ∧ x in U ∧ forall x' in U, f x' = f x] := by
  tfae_have 1 -> 4 := fun h y => h {y}
  tfae_have 4 -> 3 := fun h x => h (f x)
  tfae_have 3 -> 2 := fun h x => IsOpen.mem_nhds (h x) rfl
  tfae_have 2 -> 5
  | h, x => by
    rcases mem_nhds_iff.1 (h x) with ⟨U, eq, hU, hx⟩
    exact ⟨U, hU, hx, eq⟩
  tfae_have 5 -> 1
  | h, s => by
    refine isOpen_iff_forall_mem_open.2 fun x hx => ?_
    rcases h x with ⟨U, hU, hxU, eq⟩
exact ⟨U, fun x' hx' => mem_preimage.2 (eq x' hx').symm ▸ hx, hU, hxU⟩
  tfae_finish

@[nontriviality]
/--
theorem `of_discrete` / 定理 `of_discrete`

English:
theorem of_discrete
  given: [DiscreteTopology X] (f : X -> Y)
  statement: IsLocallyConstant f
  proof: fun _ =>
  isOpen_discrete _

中文:
定理 of_discrete
  条件: [DiscreteTopology X] (f : X -> Y)
  结论: IsLocallyConstant f
  证明: fun _ =>
  isOpen_discrete _
-/
theorem of_discrete [DiscreteTopology X] (f : X -> Y) : IsLocallyConstant f := fun _ =>
  isOpen_discrete _

/--
theorem `isOpen_fiber` / 定理 `isOpen_fiber`

English:
theorem isOpen_fiber
  given: {f : X -> Y} (hf : IsLocallyConstant f) (y : Y)
  statement: IsOpen { x | f x = y }
  proof: hf {y}

中文:
定理 isOpen_fiber
  条件: {f : X -> Y} (hf : IsLocallyConstant f) (y : Y)
  结论: IsOpen { x | f x = y }
  证明: hf {y}
-/
theorem isOpen_fiber {f : X -> Y} (hf : IsLocallyConstant f) (y : Y) : IsOpen { x | f x = y } :=
  hf {y}

/--
theorem `isClosed_fiber` / 定理 `isClosed_fiber`

English:
theorem isClosed_fiber
  given: {f : X -> Y} (hf : IsLocallyConstant f) (y : Y)
  statement: IsClosed { x | f x = y }
  proof: ⟨hf {y}ᶜ⟩

中文:
定理 isClosed_fiber
  条件: {f : X -> Y} (hf : IsLocallyConstant f) (y : Y)
  结论: IsClosed { x | f x = y }
  证明: ⟨hf {y}ᶜ⟩
-/
theorem isClosed_fiber {f : X -> Y} (hf : IsLocallyConstant f) (y : Y) : IsClosed { x | f x = y } :=
  ⟨hf {y}ᶜ⟩

/--
theorem `isClopen_fiber` / 定理 `isClopen_fiber`

English:
theorem isClopen_fiber
  given: {f : X -> Y} (hf : IsLocallyConstant f) (y : Y)
  statement: IsClopen { x | f x = y }
  proof: ⟨isClosed_fiber hf _, isOpen_fiber hf _⟩

中文:
定理 isClopen_fiber
  条件: {f : X -> Y} (hf : IsLocallyConstant f) (y : Y)
  结论: IsClopen { x | f x = y }
  证明: ⟨isClosed_fiber hf _, isOpen_fiber hf _⟩

Depends on / 依赖: isClosed_fiber, isOpen_fiber
-/
theorem isClopen_fiber {f : X -> Y} (hf : IsLocallyConstant f) (y : Y) : IsClopen { x | f x = y } :=
  ⟨isClosed_fiber hf _, isOpen_fiber hf _⟩

/--
theorem `iff_exists_open` / 定理 `iff_exists_open`

English:
theorem iff_exists_open
  given: (f : X -> Y)
  proof: (IsLocallyConstant.tfae f).out 0 4

中文:
定理 iff_exists_open
  条件: (f : X -> Y)
  证明: (IsLocallyConstant.tfae f).out 0 4

Depends on / 依赖: IsLocallyConstant, IsLocallyConstant.tfae
-/
theorem iff_exists_open (f : X -> Y) :
    IsLocallyConstant f ↔ forall x, exists U : Set X, IsOpen U ∧ x in U ∧ forall x' in U, f x' = f x :=
  (IsLocallyConstant.tfae f).out 0 4

/--
theorem `iff_eventually_eq` / 定理 `iff_eventually_eq`

English:
theorem iff_eventually_eq
  given: (f : X -> Y)
  statement: IsLocallyConstant f ↔ forall x, forallᶠ y in 𝓝 x, f y = f x
  proof: (IsLocallyConstant.tfae f).out 0 1

中文:
定理 iff_eventually_eq
  条件: (f : X -> Y)
  结论: IsLocallyConstant f ↔ 对任意 x, 对任意ᶠ y in 𝓝 x, f y = f x
  证明: (IsLocallyConstant.tfae f).out 0 1

Depends on / 依赖: IsLocallyConstant, IsLocallyConstant.tfae
-/
theorem iff_eventually_eq (f : X -> Y) : IsLocallyConstant f ↔ forall x, forallᶠ y in 𝓝 x, f y = f x :=
  (IsLocallyConstant.tfae f).out 0 1

/--
theorem `exists_open` / 定理 `exists_open`

English:
theorem exists_open
  given: {f : X -> Y} (hf : IsLocallyConstant f) (x : X)
  proof: (iff_exists_open f).1 hf x

中文:
定理 exists_open
  条件: {f : X -> Y} (hf : IsLocallyConstant f) (x : X)
  证明: (iff_exists_open f).1 hf x

Depends on / 依赖: iff_exists_open
-/
theorem exists_open {f : X -> Y} (hf : IsLocallyConstant f) (x : X) :
    exists U : Set X, IsOpen U ∧ x in U ∧ forall x' in U, f x' = f x :=
  (iff_exists_open f).1 hf x

/--
theorem `eventually_eq` / 定理 `eventually_eq`

English:
theorem eventually_eq
  given: {f : X -> Y} (hf : IsLocallyConstant f) (x : X)
  proof: (iff_eventually_eq f).1 hf x

中文:
定理 eventually_eq
  条件: {f : X -> Y} (hf : IsLocallyConstant f) (x : X)
  证明: (iff_eventually_eq f).1 hf x
-/
protected theorem eventually_eq {f : X -> Y} (hf : IsLocallyConstant f) (x : X) :
    forallᶠ y in 𝓝 x, f y = f x :=
  (iff_eventually_eq f).1 hf x

/--
theorem `iff_isOpen_fiber_apply` / 定理 `iff_isOpen_fiber_apply`

English:
theorem iff_isOpen_fiber_apply
  given: {f : X -> Y}
  statement: IsLocallyConstant f ↔ forall x, IsOpen (f ⁻¹' {f x})
  proof: (IsLocallyConstant.tfae f).out 0 2

中文:
定理 iff_isOpen_fiber_apply
  条件: {f : X -> Y}
  结论: IsLocallyConstant f ↔ 对任意 x, IsOpen (f ⁻¹' {f x})
  证明: (IsLocallyConstant.tfae f).out 0 2

Depends on / 依赖: IsLocallyConstant, IsLocallyConstant.tfae
-/
theorem iff_isOpen_fiber_apply {f : X -> Y} : IsLocallyConstant f ↔ forall x, IsOpen (f ⁻¹' {f x}) :=
  (IsLocallyConstant.tfae f).out 0 2

/--
theorem `iff_isOpen_fiber` / 定理 `iff_isOpen_fiber`

English:
theorem iff_isOpen_fiber
  given: {f : X -> Y}
  statement: IsLocallyConstant f ↔ forall y, IsOpen (f ⁻¹' {y})
  proof: (IsLocallyConstant.tfae f).out 0 3

中文:
定理 iff_isOpen_fiber
  条件: {f : X -> Y}
  结论: IsLocallyConstant f ↔ 对任意 y, IsOpen (f ⁻¹' {y})
  证明: (IsLocallyConstant.tfae f).out 0 3

Depends on / 依赖: IsLocallyConstant, IsLocallyConstant.tfae
-/
theorem iff_isOpen_fiber {f : X -> Y} : IsLocallyConstant f ↔ forall y, IsOpen (f ⁻¹' {y}) :=
  (IsLocallyConstant.tfae f).out 0 3

/--
theorem `continuous` / 定理 `continuous`

English:
theorem continuous
  given: [TopologicalSpace Y] {f : X -> Y} (hf : IsLocallyConstant f)
  proof: ⟨fun _ _ => hf _⟩

中文:
定理 continuous
  条件: [TopologicalSpace Y] {f : X -> Y} (hf : IsLocallyConstant f)
  证明: ⟨fun _ _ => hf _⟩
-/
protected theorem continuous [TopologicalSpace Y] {f : X -> Y} (hf : IsLocallyConstant f) :
    Continuous f :=
  ⟨fun _ _ => hf _⟩

/--
theorem `iff_continuous` / 定理 `iff_continuous`

English:
theorem iff_continuous
  given: {_ : TopologicalSpace Y} [DiscreteTopology Y] (f : X -> Y)
  proof: ⟨IsLocallyConstant.continuous, fun h s => h.isOpen_preimage s (isOpen_discrete _)⟩

中文:
定理 iff_continuous
  条件: {_ : TopologicalSpace Y} [DiscreteTopology Y] (f : X -> Y)
  证明: ⟨IsLocallyConstant.continuous, fun h s => h.isOpen_preimage s (isOpen_discrete _)⟩

Depends on / 依赖: IsLocallyConstant, IsLocallyConstant.continuous, continuous, h.isOpen_preimage, isOpen_discrete, isOpen_preimage
-/
theorem iff_continuous {_ : TopologicalSpace Y} [DiscreteTopology Y] (f : X -> Y) :
    IsLocallyConstant f ↔ Continuous f :=
  ⟨IsLocallyConstant.continuous, fun h s => h.isOpen_preimage s (isOpen_discrete _)⟩

/--
theorem `of_constant` / 定理 `of_constant`

English:
theorem of_constant
  given: (f : X -> Y) (h : forall x y, f x = f y)
  statement: IsLocallyConstant f
  proof: (iff_eventually_eq f).2 fun _ => Eventually.of_forall fun _ => h _ _

中文:
定理 of_constant
  条件: (f : X -> Y) (h : 对任意 x y, f x = f y)
  结论: IsLocallyConstant f
  证明: (iff_eventually_eq f).2 fun _ => Eventually.of_forall fun _ => h _ _

Depends on / 依赖: Eventually, Eventually.of_forall, iff_eventually_eq, of_forall
-/
theorem of_constant (f : X -> Y) (h : forall x y, f x = f y) : IsLocallyConstant f :=
  (iff_eventually_eq f).2 fun _ => Eventually.of_forall fun _ => h _ _

/--
theorem `const` / 定理 `const`

English:
theorem const
  given: (y : Y)
  statement: IsLocallyConstant (Function.const X y)
  proof: of_constant _ fun _ _ => rfl

中文:
定理 const
  条件: (y : Y)
  结论: IsLocallyConstant (Function.const X y)
  证明: of_constant _ fun _ _ => rfl
-/
protected theorem const (y : Y) : IsLocallyConstant (Function.const X y) :=
  of_constant _ fun _ _ => rfl

/--
theorem `comp` / 定理 `comp`

English:
theorem comp
  given: {f : X -> Y} (hf : IsLocallyConstant f) (g : Y -> Z)
  proof: fun s => by
  rw [Set.preimage_comp]
  exact hf _

中文:
定理 comp
  条件: {f : X -> Y} (hf : IsLocallyConstant f) (g : Y -> Z)
  证明: fun s => by
  rw [Set.preimage_comp]
  exact hf _
-/
protected theorem comp {f : X -> Y} (hf : IsLocallyConstant f) (g : Y -> Z) :
    IsLocallyConstant (g ∘ f) := fun s => by
  rw [Set.preimage_comp]
  exact hf _

/--
theorem `prodMk` / 定理 `prodMk`

English:
theorem prodMk
  statement: {Y'} {f : X -> Y} {f' : X -> Y'} (hf : IsLocallyConstant f)
  proof: (iff_eventually_eq _).2 fun x =>
(hf.eventually_eq x).mp (hf'.eventually_eq x).mono fun _ hf' hf => Prod.ext hf hf'

中文:
定理 prodMk
  结论: {Y'} {f : X -> Y} {f' : X -> Y'} (hf : IsLocallyConstant f)
  证明: (iff_eventually_eq _).2 fun x =>
(hf.eventually_eq x).mp (hf'.eventually_eq x).mono fun _ hf' hf => Prod.ext hf hf'

Depends on / 依赖: Prod.ext, eventually_eq, hf.eventually_eq, iff_eventually_eq
-/
theorem prodMk {Y'} {f : X -> Y} {f' : X -> Y'} (hf : IsLocallyConstant f)
    (hf' : IsLocallyConstant f') : IsLocallyConstant fun x => (f x, f' x) :=
  (iff_eventually_eq _).2 fun x =>
(hf.eventually_eq x).mp (hf'.eventually_eq x).mono fun _ hf' hf => Prod.ext hf hf'

/--
theorem `comp₂` / 定理 `comp₂`

English:
theorem comp₂
  statement: {Y₁ Y₂ Z : Type*} {f : X -> Y₁} {g : X -> Y₂} (hf : IsLocallyConstant f)
  proof: (hf.prodMk hg).comp fun x : Y₁ × Y₂ => h x.1 x.2

中文:
定理 comp₂
  结论: {Y₁ Y₂ Z : 类型} {f : X -> Y₁} {g : X -> Y₂} (hf : IsLocallyConstant f)
  证明: (hf.prodMk hg).comp fun x : Y₁ × Y₂ => h x.1 x.2

Depends on / 依赖: hf.prodMk, prodMk
-/
theorem comp₂ {Y₁ Y₂ Z : Type*} {f : X -> Y₁} {g : X -> Y₂} (hf : IsLocallyConstant f)
    (hg : IsLocallyConstant g) (h : Y₁ -> Y₂ -> Z) : IsLocallyConstant fun x => h (f x) (g x) :=
  (hf.prodMk hg).comp fun x : Y₁ × Y₂ => h x.1 x.2

/--
theorem `comp_continuous` / 定理 `comp_continuous`

English:
theorem comp_continuous
  statement: [TopologicalSpace Y] {g : Y -> Z} {f : X -> Y} (hg : IsLocallyConstant g)
  proof: fun s => by
  rw [Set.preimage_comp]
  exact hf.isOpen_preimage _ (hg _)

中文:
定理 comp_continuous
  结论: [TopologicalSpace Y] {g : Y -> Z} {f : X -> Y} (hg : IsLocallyConstant g)
  证明: fun s => by
  rw [Set.preimage_comp]
  exact hf.isOpen_preimage _ (hg _)

Depends on / 依赖: Set.preimage_comp, hf.isOpen_preimage, isOpen_preimage, preimage_comp
-/
theorem comp_continuous [TopologicalSpace Y] {g : Y -> Z} {f : X -> Y} (hg : IsLocallyConstant g)
    (hf : Continuous f) : IsLocallyConstant (g ∘ f) := fun s => by
  rw [Set.preimage_comp]
  exact hf.isOpen_preimage _ (hg _)

/--
theorem `apply_eq_of_isPreconnected` / 定理 `apply_eq_of_isPreconnected`

English:
theorem apply_eq_of_isPreconnected
  statement: {f : X -> Y} (hf : IsLocallyConstant f) {s : Set X}
  proof: by
  let U := f ⁻¹' {f y}
  suffices x ∉ Uᶜ from Classical.not_not.1 this
  intro hxV
  specialize hs U Uᶜ (hf {f y}) (hf {f y}ᶜ) _ ⟨y, ⟨hy, rfl⟩⟩ ⟨x, ⟨hx, hxV⟩⟩
  · simp only [union_compl_self, subset_univ]
  · simp only [inter_empty, Set.not_nonempty_empty, inter_compl_self] at hs

中文:
定理 apply_eq_of_isPreconnected
  结论: {f : X -> Y} (hf : IsLocallyConstant f) {s : Set X}
  证明: by
  let U := f ⁻¹' {f y}
  suffices x ∉ Uᶜ from Classical.not_not.1 this
  intro hxV
  specialize hs U Uᶜ (hf {f y}) (hf {f y}ᶜ) _ ⟨y, ⟨hy, rfl⟩⟩ ⟨x, ⟨hx, hxV⟩⟩
  · simp only [union_compl_self, subset_univ]
  · simp only [inter_empty, Set.not_nonempty_empty, inter_compl_self] at hs

Depends on / 依赖: Classical, Classical.not_not, Set.not_nonempty_empty, inter_compl_self, inter_empty, not_nonempty_empty, not_not, specialize, subset_univ, union_compl_self
-/
theorem apply_eq_of_isPreconnected {f : X -> Y} (hf : IsLocallyConstant f) {s : Set X}
    (hs : IsPreconnected s) {x y : X} (hx : x in s) (hy : y in s) : f x = f y := by
  let U := f ⁻¹' {f y}
  suffices x ∉ Uᶜ from Classical.not_not.1 this
  intro hxV
  specialize hs U Uᶜ (hf {f y}) (hf {f y}ᶜ) _ ⟨y, ⟨hy, rfl⟩⟩ ⟨x, ⟨hx, hxV⟩⟩
  · simp only [union_compl_self, subset_univ]
  · simp only [inter_empty, Set.not_nonempty_empty, inter_compl_self] at hs

/--
theorem `apply_eq_of_preconnectedSpace` / 定理 `apply_eq_of_preconnectedSpace`

English:
theorem apply_eq_of_preconnectedSpace
  statement: [PreconnectedSpace X] {f : X -> Y} (hf : IsLocallyConstant f)
  proof: hf.apply_eq_of_isPreconnected isPreconnected_univ trivial trivial

中文:
定理 apply_eq_of_preconnectedSpace
  结论: [PreconnectedSpace X] {f : X -> Y} (hf : IsLocallyConstant f)
  证明: hf.apply_eq_of_isPreconnected isPreconnected_univ trivial trivial

Depends on / 依赖: apply_eq_of_isPreconnected, hf.apply_eq_of_isPreconnected, isPreconnected_univ
-/
theorem apply_eq_of_preconnectedSpace [PreconnectedSpace X] {f : X -> Y} (hf : IsLocallyConstant f)
    (x y : X) : f x = f y :=
  hf.apply_eq_of_isPreconnected isPreconnected_univ trivial trivial

/--
theorem `eq_const` / 定理 `eq_const`

English:
theorem eq_const
  given: [PreconnectedSpace X] {f : X -> Y} (hf : IsLocallyConstant f) (x : X)
  proof: funext fun y => hf.apply_eq_of_preconnectedSpace y x

中文:
定理 eq_const
  条件: [PreconnectedSpace X] {f : X -> Y} (hf : IsLocallyConstant f) (x : X)
  证明: funext fun y => hf.apply_eq_of_preconnectedSpace y x

Depends on / 依赖: apply_eq_of_preconnectedSpace, hf.apply_eq_of_preconnectedSpace
-/
theorem eq_const [PreconnectedSpace X] {f : X -> Y} (hf : IsLocallyConstant f) (x : X) :
    f = Function.const X (f x) :=
  funext fun y => hf.apply_eq_of_preconnectedSpace y x

/--
theorem `exists_eq_const` / 定理 `exists_eq_const`

English:
theorem exists_eq_const
  given: [PreconnectedSpace X] [Nonempty Y] {f : X -> Y} (hf : IsLocallyConstant f)
  proof: by
  rcases isEmpty_or_nonempty X with h | h
· exact ⟨Classical.arbitrary Y, funext h.elim⟩
  · exact ⟨f (Classical.arbitrary X), hf.eq_const _⟩

中文:
定理 exists_eq_const
  条件: [PreconnectedSpace X] [Nonempty Y] {f : X -> Y} (hf : IsLocallyConstant f)
  证明: by
  rcases isEmpty_or_nonempty X with h | h
· exact ⟨Classical.arbitrary Y, funext h.elim⟩
  · exact ⟨f (Classical.arbitrary X), hf.eq_const _⟩

Depends on / 依赖: Classical, Classical.arbitrary, arbitrary, eq_const, h.elim, hf.eq_const, isEmpty_or_nonempty
-/
theorem exists_eq_const [PreconnectedSpace X] [Nonempty Y] {f : X -> Y} (hf : IsLocallyConstant f) :
    exists y, f = Function.const X y := by
  rcases isEmpty_or_nonempty X with h | h
· exact ⟨Classical.arbitrary Y, funext h.elim⟩
  · exact ⟨f (Classical.arbitrary X), hf.eq_const _⟩

/--
theorem `iff_is_const` / 定理 `iff_is_const`

English:
theorem iff_is_const
  given: [PreconnectedSpace X] {f : X -> Y}
  statement: IsLocallyConstant f ↔ forall x y, f x = f y
  proof: ⟨fun h _ _ => h.apply_eq_of_isPreconnected isPreconnected_univ trivial trivial, of_constant _⟩

中文:
定理 iff_is_const
  条件: [PreconnectedSpace X] {f : X -> Y}
  结论: IsLocallyConstant f ↔ 对任意 x y, f x = f y
  证明: ⟨fun h _ _ => h.apply_eq_of_isPreconnected isPreconnected_univ trivial trivial, of_constant _⟩

Depends on / 依赖: apply_eq_of_isPreconnected, h.apply_eq_of_isPreconnected, isPreconnected_univ, of_constant
-/
theorem iff_is_const [PreconnectedSpace X] {f : X -> Y} : IsLocallyConstant f ↔ forall x y, f x = f y :=
  ⟨fun h _ _ => h.apply_eq_of_isPreconnected isPreconnected_univ trivial trivial, of_constant _⟩

/--
theorem `range_finite` / 定理 `range_finite`

English:
theorem range_finite
  given: [CompactSpace X] {f : X -> Y} (hf : IsLocallyConstant f)
  proof: by
  let : TopologicalSpace Y := ⊥; have := discreteTopology_bot Y
  exact (isCompact_range hf.continuous).finite_of_discrete

@[to_additive]

中文:
定理 range_finite
  条件: [CompactSpace X] {f : X -> Y} (hf : IsLocallyConstant f)
  证明: by
  let : TopologicalSpace Y := ⊥; have := discreteTopology_bot Y
  exact (isCompact_range hf.continuous).finite_of_discrete

@[to_additive]

Depends on / 依赖: TopologicalSpace, continuous, discreteTopology_bot, finite_of_discrete, hf.continuous, isCompact_range
-/
theorem range_finite [CompactSpace X] {f : X -> Y} (hf : IsLocallyConstant f) :
    (Set.range f).Finite := by
  let : TopologicalSpace Y := ⊥; have := discreteTopology_bot Y
  exact (isCompact_range hf.continuous).finite_of_discrete

@[to_additive]
/--
theorem `one` / 定理 `one`

English:
theorem one
  given: [One Y]
  statement: IsLocallyConstant (1 : X -> Y)
  proof: IsLocallyConstant.const 1

@[to_additive]

中文:
定理 one
  条件: [One Y]
  结论: IsLocallyConstant (1 : X -> Y)
  证明: IsLocallyConstant.const 1

@[to_additive]

Depends on / 依赖: IsLocallyConstant, IsLocallyConstant.const
-/
theorem one [One Y] : IsLocallyConstant (1 : X -> Y) := IsLocallyConstant.const 1

@[to_additive]
/--
theorem `inv` / 定理 `inv`

English:
theorem inv
  given: [Inv Y] ⦃f
  statement: X -> Y⦄ (hf : IsLocallyConstant f) : IsLocallyConstant f⁻¹
  proof: hf.comp fun x => x⁻¹

@[to_additive]

中文:
定理 inv
  条件: [Inv Y] ⦃f
  结论: X -> Y⦄ (hf : IsLocallyConstant f) : IsLocallyConstant f⁻¹
  证明: hf.comp fun x => x⁻¹

@[to_additive]

Depends on / 依赖: hf.comp
-/
theorem inv [Inv Y] ⦃f : X -> Y⦄ (hf : IsLocallyConstant f) : IsLocallyConstant f⁻¹ :=
  hf.comp fun x => x⁻¹

@[to_additive]
/--
theorem `mul` / 定理 `mul`

English:
theorem mul
  given: [Mul Y] ⦃f g
  statement: X -> Y⦄ (hf : IsLocallyConstant f) (hg : IsLocallyConstant g) :
  proof: hf.comp₂ hg (· * ·)

@[to_additive]

中文:
定理 mul
  条件: [Mul Y] ⦃f g
  结论: X -> Y⦄ (hf : IsLocallyConstant f) (hg : IsLocallyConstant g) :
  证明: hf.comp₂ hg (· * ·)

@[to_additive]

Depends on / 依赖: hf.comp
-/
theorem mul [Mul Y] ⦃f g : X -> Y⦄ (hf : IsLocallyConstant f) (hg : IsLocallyConstant g) :
    IsLocallyConstant (f * g) :=
  hf.comp₂ hg (· * ·)

@[to_additive]
/--
theorem `div` / 定理 `div`

English:
theorem div
  given: [Div Y] ⦃f g
  statement: X -> Y⦄ (hf : IsLocallyConstant f) (hg : IsLocallyConstant g) :
  proof: hf.comp₂ hg (· / ·)

中文:
定理 div
  条件: [Div Y] ⦃f g
  结论: X -> Y⦄ (hf : IsLocallyConstant f) (hg : IsLocallyConstant g) :
  证明: hf.comp₂ hg (· / ·)

Depends on / 依赖: hf.comp
-/
theorem div [Div Y] ⦃f g : X -> Y⦄ (hf : IsLocallyConstant f) (hg : IsLocallyConstant g) :
    IsLocallyConstant (f / g) :=
  hf.comp₂ hg (· / ·)

/--
theorem `desc` / 定理 `desc`

English:
theorem desc
  statement: {α β : Type*} (f : X -> α) (g : α -> β) (h : IsLocallyConstant (g ∘ f))
  proof: fun s => by
  rw [← preimage_image_eq s inj]; rw [preimage_preimage]
  exact h (g '' s)

中文:
定理 desc
  结论: {α β : 类型} (f : X -> α) (g : α -> β) (h : IsLocallyConstant (g ∘ f))
  证明: fun s => by
  rw [← preimage_image_eq s inj]; rw [preimage_preimage]
  exact h (g '' s)

Depends on / 依赖: preimage_image_eq, preimage_preimage
-/
theorem desc {α β : Type*} (f : X -> α) (g : α -> β) (h : IsLocallyConstant (g ∘ f))
    (inj : Function.Injective g) : IsLocallyConstant f := fun s => by
  rw [← preimage_image_eq s inj]; rw [preimage_preimage]
  exact h (g '' s)

/--
theorem `of_constant_on_connected_components` / 定理 `of_constant_on_connected_components`

English:
theorem of_constant_on_connected_components
  statement: [LocallyConnectedSpace X] {f : X -> Y}
  proof: (iff_exists_open _).2 fun x =>
    ⟨connectedComponent x, isOpen_connectedComponent, mem_connectedComponent, h x⟩

中文:
定理 of_constant_on_connected_components
  结论: [LocallyConnectedSpace X] {f : X -> Y}
  证明: (iff_exists_open _).2 fun x =>
    ⟨connectedComponent x, isOpen_connectedComponent, mem_connectedComponent, h x⟩

Depends on / 依赖: connectedComponent, iff_exists_open, isOpen_connectedComponent, mem_connectedComponent
-/
theorem of_constant_on_connected_components [LocallyConnectedSpace X] {f : X -> Y}
    (h : forall x, forall y in connectedComponent x, f y = f x) : IsLocallyConstant f :=
  (iff_exists_open _).2 fun x =>
    ⟨connectedComponent x, isOpen_connectedComponent, mem_connectedComponent, h x⟩

/--
theorem `of_constant_on_connected_clopens` / 定理 `of_constant_on_connected_clopens`

English:
theorem of_constant_on_connected_clopens
  statement: [LocallyConnectedSpace X] {f : X -> Y}
  proof: of_constant_on_connected_components fun x =>
    h (connectedComponent x) isConnected_connectedComponent isClopen_connectedComponent x
      mem_connectedComponent

中文:
定理 of_constant_on_connected_clopens
  结论: [LocallyConnectedSpace X] {f : X -> Y}
  证明: of_constant_on_connected_components fun x =>
    h (connectedComponent x) isConnected_connectedComponent isClopen_connectedComponent x
      mem_connectedComponent

Depends on / 依赖: connectedComponent, isClopen_connectedComponent, isConnected_connectedComponent, mem_connectedComponent, of_constant_on_connected_components
-/
theorem of_constant_on_connected_clopens [LocallyConnectedSpace X] {f : X -> Y}
    (h : forall U : Set X, IsConnected U -> IsClopen U -> forall x in U, forall y in U, f y = f x) :
    IsLocallyConstant f :=
  of_constant_on_connected_components fun x =>
    h (connectedComponent x) isConnected_connectedComponent isClopen_connectedComponent x
      mem_connectedComponent

/--
theorem `of_constant_on_preconnected_clopens` / 定理 `of_constant_on_preconnected_clopens`

English:
theorem of_constant_on_preconnected_clopens
  statement: [LocallyConnectedSpace X] {f : X -> Y}
  proof: of_constant_on_connected_clopens fun U hU => h U hU.isPreconnected

中文:
定理 of_constant_on_preconnected_clopens
  结论: [LocallyConnectedSpace X] {f : X -> Y}
  证明: of_constant_on_connected_clopens fun U hU => h U hU.isPreconnected

Depends on / 依赖: hU.isPreconnected, isPreconnected, of_constant_on_connected_clopens
-/
theorem of_constant_on_preconnected_clopens [LocallyConnectedSpace X] {f : X -> Y}
    (h : forall U : Set X, IsPreconnected U -> IsClopen U -> forall x in U, forall y in U, f y = f x) :
    IsLocallyConstant f :=
  of_constant_on_connected_clopens fun U hU => h U hU.isPreconnected

end IsLocallyConstant

/--
Definition of `LocallyConstant` / `LocallyConstant` 的定义

English:
structure LocallyConstant
  parameters: (X Y : Type*) [TopologicalSpace X]
  axioms and operations (2):
    - toFun : X -> Y
    - isLocallyConstant : IsLocallyConstant toFun

中文:
结构 LocallyConstant
  参数: (X Y : 类型) [TopologicalSpace X]
  公理与运算 (2 个):
    - toFun : X -> Y
    - isLocallyConstant : IsLocallyConstant toFun
-/
structure LocallyConstant (X Y : Type*) [TopologicalSpace X] where
  /-- The underlying function. -/
  protected toFun : X -> Y
  /-- The map is locally constant. -/
  protected isLocallyConstant : IsLocallyConstant toFun

namespace LocallyConstant

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Inhabited
  signature: Y] : Inhabited (LocallyConstant X Y)
  body: ⟨⟨_, IsLocallyConstant.const default⟩⟩

中文:
实例 [Inhabited
  签名: Y] : Inhabited (LocallyConstant X Y)
  定义体: ⟨⟨_, IsLocallyConstant.const default⟩⟩

Depends on / 依赖: IsLocallyConstant, IsLocallyConstant.const
-/
instance [Inhabited Y] : Inhabited (LocallyConstant X Y) :=
  ⟨⟨_, IsLocallyConstant.const default⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FunLike (LocallyConstant X Y) X Y
  body: LocallyConstant.toFun
  coe_injective := by rintro ⟨_, _⟩ ⟨_, _⟩ _; congr

中文:
实例 :
  签名: FunLike (LocallyConstant X Y) X Y
  定义体: LocallyConstant.toFun
  coe_injective := by rintro ⟨_, _⟩ ⟨_, _⟩ _; congr

Depends on / 依赖: LocallyConstant, LocallyConstant.toFun
-/
instance : FunLike (LocallyConstant X Y) X Y where
  coe := LocallyConstant.toFun
  coe_injective := by rintro ⟨_, _⟩ ⟨_, _⟩ _; congr

/--
Definition of `Simps.apply` / `Simps.apply` 的定义

English:
definition Simps.apply
  signature: (f : LocallyConstant X Y)
  body: f

initialize_simps_projections LocallyConstant (toFun -> apply)

@[simp]

中文:
定义 Simps.apply
  签名: (f : LocallyConstant X Y)
  定义体: f

initialize_simps_projections LocallyConstant (toFun -> apply)

@[simp]
-/
def Simps.apply (f : LocallyConstant X Y) : X -> Y := f

initialize_simps_projections LocallyConstant (toFun -> apply)

@[simp]
/--
theorem `toFun_eq_coe` / 定理 `toFun_eq_coe`

English:
theorem toFun_eq_coe
  given: (f : LocallyConstant X Y)
  statement: f.toFun = f
  proof: rfl

@[simp]

中文:
定理 toFun_eq_coe
  条件: (f : LocallyConstant X Y)
  结论: f.toFun = f
  证明: rfl

@[simp]
-/
theorem toFun_eq_coe (f : LocallyConstant X Y) : f.toFun = f :=
  rfl

@[simp]
/--
theorem `coe_mk` / 定理 `coe_mk`

English:
theorem coe_mk
  given: (f : X -> Y) (h)
  statement: ⇑(⟨f, h⟩ : LocallyConstant X Y) = f
  proof: rfl

中文:
定理 coe_mk
  条件: (f : X -> Y) (h)
  结论: ⇑(⟨f, h⟩ : LocallyConstant X Y) = f
  证明: rfl
-/
theorem coe_mk (f : X -> Y) (h) : ⇑(⟨f, h⟩ : LocallyConstant X Y) = f :=
  rfl

/--
theorem `congr_fun` / 定理 `congr_fun`

English:
theorem congr_fun
  given: {f g : LocallyConstant X Y} (h : f = g) (x : X)
  statement: f x = g x
  proof: DFunLike.congr_fun h x

中文:
定理 congr_fun
  条件: {f g : LocallyConstant X Y} (h : f = g) (x : X)
  结论: f x = g x
  证明: DFunLike.congr_fun h x
-/
protected theorem congr_fun {f g : LocallyConstant X Y} (h : f = g) (x : X) : f x = g x :=
  DFunLike.congr_fun h x

/--
theorem `congr_arg` / 定理 `congr_arg`

English:
theorem congr_arg
  given: (f : LocallyConstant X Y) {x y : X} (h : x = y)
  statement: f x = f y
  proof: DFunLike.congr_arg f h

中文:
定理 congr_arg
  条件: (f : LocallyConstant X Y) {x y : X} (h : x = y)
  结论: f x = f y
  证明: DFunLike.congr_arg f h
-/
protected theorem congr_arg (f : LocallyConstant X Y) {x y : X} (h : x = y) : f x = f y :=
  DFunLike.congr_arg f h

/--
theorem `coe_injective` / 定理 `coe_injective`

English:
theorem coe_injective
  statement: @Function.Injective (LocallyConstant X Y) (X -> Y) (↑)
  proof: fun _ _ =>
  DFunLike.ext'

@[norm_cast]

中文:
定理 coe_injective
  结论: @Function.Injective (LocallyConstant X Y) (X -> Y) (↑)
  证明: fun _ _ =>
  DFunLike.ext'

@[norm_cast]
-/
theorem coe_injective : @Function.Injective (LocallyConstant X Y) (X -> Y) (↑) := fun _ _ =>
  DFunLike.ext'

@[norm_cast]
/--
theorem `coe_inj` / 定理 `coe_inj`

English:
theorem coe_inj
  given: {f g : LocallyConstant X Y}
  statement: (f : X -> Y) = g ↔ f = g
  proof: coe_injective.eq_iff

@[ext]

中文:
定理 coe_inj
  条件: {f g : LocallyConstant X Y}
  结论: (f : X -> Y) = g ↔ f = g
  证明: coe_injective.eq_iff

@[ext]

Depends on / 依赖: coe_injective, coe_injective.eq_iff, eq_iff
-/
theorem coe_inj {f g : LocallyConstant X Y} : (f : X -> Y) = g ↔ f = g :=
  coe_injective.eq_iff

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: ⦃f g
  statement: LocallyConstant X Y⦄ (h : forall x, f x = g x) : f = g
  proof: DFunLike.ext _ _ h

中文:
定理 ext
  条件: ⦃f g
  结论: LocallyConstant X Y⦄ (h : 对任意 x, f x = g x) : f = g
  证明: DFunLike.ext _ _ h

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem ext ⦃f g : LocallyConstant X Y⦄ (h : forall x, f x = g x) : f = g :=
  DFunLike.ext _ _ h

section CodomainTopologicalSpace

variable [TopologicalSpace Y] (f : LocallyConstant X Y)

/--
theorem `continuous` / 定理 `continuous`

English:
theorem continuous
  statement: Continuous f
  proof: f.isLocallyConstant.continuous

中文:
定理 continuous
  结论: Continuous f
  证明: f.isLocallyConstant.continuous
-/
protected theorem continuous : Continuous f :=
  f.isLocallyConstant.continuous

/--
Definition of `toContinuousMap` / `toContinuousMap` 的定义

English:
definition toContinuousMap
  signature: : C(X, Y)
  body: ⟨f, f.continuous⟩

中文:
定义 toContinuousMap
  签名: : C(X, Y)
  定义体: ⟨f, f.continuous⟩
-/
@[coe] def toContinuousMap : C(X, Y) :=
  ⟨f, f.continuous⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Coe (LocallyConstant X Y) C(X, Y)
  body: ⟨toContinuousMap⟩

中文:
实例 :
  签名: Coe (LocallyConstant X Y) C(X, Y)
  定义体: ⟨toContinuousMap⟩

Depends on / 依赖: toContinuousMap
-/
instance : Coe (LocallyConstant X Y) C(X, Y) := ⟨toContinuousMap⟩

/--
theorem `coe_continuousMap` / 定理 `coe_continuousMap`

English:
theorem coe_continuousMap
  statement: ((f : C(X, Y)) : X -> Y) = (f : X -> Y)
  proof: rfl

中文:
定理 coe_continuousMap
  结论: ((f : C(X, Y)) : X -> Y) = (f : X -> Y)
  证明: rfl
-/
@[simp] theorem coe_continuousMap : ((f : C(X, Y)) : X -> Y) = (f : X -> Y) := rfl

/--
theorem `toContinuousMap_injective` / 定理 `toContinuousMap_injective`

English:
theorem toContinuousMap_injective
  proof: fun _ _ h =>
  ext (ContinuousMap.congr_fun h)

中文:
定理 toContinuousMap_injective
  证明: fun _ _ h =>
  ext (ContinuousMap.congr_fun h)
-/
theorem toContinuousMap_injective :
    Function.Injective (toContinuousMap : LocallyConstant X Y -> C(X, Y)) := fun _ _ h =>
  ext (ContinuousMap.congr_fun h)

end CodomainTopologicalSpace

/--
Definition of `const` / `const` 的定义

English:
definition const
  signature: (X : Type*) {Y : Type*} [TopologicalSpace X] (y : Y)
  body: ⟨Function.const X y, IsLocallyConstant.const _⟩

@[simp]

中文:
定义 const
  签名: (X : 类型) {Y : 类型} [TopologicalSpace X] (y : Y)
  定义体: ⟨Function.const X y, IsLocallyConstant.const _⟩

@[simp]

Depends on / 依赖: Function, Function.const, IsLocallyConstant, IsLocallyConstant.const
-/
def const (X : Type*) {Y : Type*} [TopologicalSpace X] (y : Y) : LocallyConstant X Y :=
  ⟨Function.const X y, IsLocallyConstant.const _⟩

@[simp]
/--
theorem `coe_const` / 定理 `coe_const`

English:
theorem coe_const
  given: (y : Y)
  statement: (const X y : X -> Y) = Function.const X y
  proof: rfl

中文:
定理 coe_const
  条件: (y : Y)
  结论: (const X y : X -> Y) = Function.const X y
  证明: rfl
-/
theorem coe_const (y : Y) : (const X y : X -> Y) = Function.const X y :=
  rfl

/-- Evaluation/projection as a locally constant function. -/
@[simps]
/--
Definition of `eval` / `eval` 的定义

English:
definition eval
  signature: {ι : Type*} {X : ι -> Type*}
  body: fun f => f i
isLocallyConstant := (IsLocallyConstant.iff_continuous _).mpr continuous_apply i

中文:
定义 eval
  签名: {ι : 类型} {X : ι -> 类型}
  定义体: fun f => f i
isLocallyConstant := (IsLocallyConstant.iff_continuous _).mpr continuous_apply i
-/
def eval {ι : Type*} {X : ι -> Type*}
    [forall i, TopologicalSpace (X i)] (i : ι) [DiscreteTopology (X i)] :
    LocallyConstant (Π i, X i) (X i) where
  toFun := fun f => f i
isLocallyConstant := (IsLocallyConstant.iff_continuous _).mpr continuous_apply i

/--
Definition of `ofIsClopen` / `ofIsClopen` 的定义

English:
definition ofIsClopen
  signature: {X : Type*} [TopologicalSpace X] {U : Set X} [forall x, Decidable (x in U)]
  body: if x in U then 0 else 1
  isLocallyConstant := by
refine IsLocallyConstant.iff_isOpen_fiber.2 Fin.forall_fin_two.2 ⟨?_, ?_⟩
    · convert! hU.2 using 1
      ext
      simp only [mem_singleton_iff, Fin.one_eq_zero_iff, mem_preimage, ite_eq_left_iff,
        Nat.succ_succ_ne_one]
      tauto
    · rw

中文:
定义 ofIsClopen
  签名: {X : 类型} [TopologicalSpace X] {U : Set X} [对任意 x, Decidable (x in U)]
  定义体: if x in U then 0 else 1
  isLocallyConstant := by
refine IsLocallyConstant.iff_isOpen_fiber.2 Fin.forall_fin_two.2 ⟨?_, ?_⟩
    · convert! hU.2 using 1
      ext
      simp only [mem_singleton_iff, Fin.one_eq_zero_iff, mem_preimage, ite_eq_left_iff,
        Nat.succ_succ_ne_one]
      tauto
    · rw
-/
def ofIsClopen {X : Type*} [TopologicalSpace X] {U : Set X} [forall x, Decidable (x in U)]
    (hU : IsClopen U) : LocallyConstant X (Fin 2) where
  toFun x := if x in U then 0 else 1
  isLocallyConstant := by
refine IsLocallyConstant.iff_isOpen_fiber.2 Fin.forall_fin_two.2 ⟨?_, ?_⟩
    · convert! hU.2 using 1
      ext
      simp only [mem_singleton_iff, Fin.one_eq_zero_iff, mem_preimage, ite_eq_left_iff,
        Nat.succ_succ_ne_one]
      tauto
    · rw [← isClosed_compl_iff]
      convert! hU.1
      ext
      simp

@[simp]
/--
theorem `ofIsClopen_fiber_zero` / 定理 `ofIsClopen_fiber_zero`

English:
theorem ofIsClopen_fiber_zero
  statement: {X : Type*} [TopologicalSpace X] {U : Set X} [forall x, Decidable (x in U)]
  proof: by
  ext
  simp only [ofIsClopen, mem_singleton_iff, Fin.one_eq_zero_iff, coe_mk, mem_preimage,
    ite_eq_left_iff, Nat.succ_succ_ne_one]
  tauto

@[simp]

中文:
定理 ofIsClopen_fiber_zero
  结论: {X : 类型} [TopologicalSpace X] {U : Set X} [对任意 x, Decidable (x in U)]
  证明: by
  ext
  simp only [ofIsClopen, mem_singleton_iff, Fin.one_eq_zero_iff, coe_mk, mem_preimage,
    ite_eq_left_iff, Nat.succ_succ_ne_one]
  tauto

@[simp]

Depends on / 依赖: Fin.one_eq_zero_iff, Nat.succ_succ_ne_one, coe_mk, ite_eq_left_iff, mem_preimage, mem_singleton_iff, ofIsClopen, one_eq_zero_iff, succ_succ_ne_one
-/
theorem ofIsClopen_fiber_zero {X : Type*} [TopologicalSpace X] {U : Set X} [forall x, Decidable (x in U)]
    (hU : IsClopen U) : ofIsClopen hU ⁻¹' ({0} : Set (Fin 2)) = U := by
  ext
  simp only [ofIsClopen, mem_singleton_iff, Fin.one_eq_zero_iff, coe_mk, mem_preimage,
    ite_eq_left_iff, Nat.succ_succ_ne_one]
  tauto

@[simp]
/--
theorem `ofIsClopen_fiber_one` / 定理 `ofIsClopen_fiber_one`

English:
theorem ofIsClopen_fiber_one
  statement: {X : Type*} [TopologicalSpace X] {U : Set X} [forall x, Decidable (x in U)]
  proof: by
  ext
  simp only [ofIsClopen, mem_singleton_iff, coe_mk, Fin.zero_eq_one_iff, mem_preimage,
    ite_eq_right_iff, mem_compl_iff, Nat.succ_succ_ne_one]

中文:
定理 ofIsClopen_fiber_one
  结论: {X : 类型} [TopologicalSpace X] {U : Set X} [对任意 x, Decidable (x in U)]
  证明: by
  ext
  simp only [ofIsClopen, mem_singleton_iff, coe_mk, Fin.zero_eq_one_iff, mem_preimage,
    ite_eq_right_iff, mem_compl_iff, Nat.succ_succ_ne_one]

Depends on / 依赖: Fin.zero_eq_one_iff, Nat.succ_succ_ne_one, coe_mk, ite_eq_right_iff, mem_compl_iff, mem_preimage, mem_singleton_iff, ofIsClopen, succ_succ_ne_one, zero_eq_one_iff
-/
theorem ofIsClopen_fiber_one {X : Type*} [TopologicalSpace X] {U : Set X} [forall x, Decidable (x in U)]
    (hU : IsClopen U) : ofIsClopen hU ⁻¹' ({1} : Set (Fin 2)) = Uᶜ := by
  ext
  simp only [ofIsClopen, mem_singleton_iff, coe_mk, Fin.zero_eq_one_iff, mem_preimage,
    ite_eq_right_iff, mem_compl_iff, Nat.succ_succ_ne_one]

/--
theorem `locallyConstant_eq_of_fiber_zero_eq` / 定理 `locallyConstant_eq_of_fiber_zero_eq`

English:
theorem locallyConstant_eq_of_fiber_zero_eq
  statement: {X : Type*} [TopologicalSpace X]
  proof: by
  simp only [Set.ext_iff, mem_singleton_iff, mem_preimage] at h
  ext1 x
  exact Fin.fin_two_eq_of_eq_zero_iff (h x)

中文:
定理 locallyConstant_eq_of_fiber_zero_eq
  结论: {X : 类型} [TopologicalSpace X]
  证明: by
  simp only [Set.ext_iff, mem_singleton_iff, mem_preimage] at h
  ext1 x
  exact Fin.fin_two_eq_of_eq_zero_iff (h x)

Depends on / 依赖: Fin.fin_two_eq_of_eq_zero_iff, Set.ext_iff, ext_iff, fin_two_eq_of_eq_zero_iff, mem_preimage, mem_singleton_iff
-/
theorem locallyConstant_eq_of_fiber_zero_eq {X : Type*} [TopologicalSpace X]
    (f g : LocallyConstant X (Fin 2)) (h : f ⁻¹' ({0} : Set (Fin 2)) = g ⁻¹' {0}) : f = g := by
  simp only [Set.ext_iff, mem_singleton_iff, mem_preimage] at h
  ext1 x
  exact Fin.fin_two_eq_of_eq_zero_iff (h x)

/--
theorem `range_finite` / 定理 `range_finite`

English:
theorem range_finite
  given: [CompactSpace X] (f : LocallyConstant X Y)
  statement: (Set.range f).Finite
  proof: f.isLocallyConstant.range_finite

中文:
定理 range_finite
  条件: [CompactSpace X] (f : LocallyConstant X Y)
  结论: (Set.range f).Finite
  证明: f.isLocallyConstant.range_finite

Depends on / 依赖: f.isLocallyConstant.range_finite, isLocallyConstant, range_finite
-/
theorem range_finite [CompactSpace X] (f : LocallyConstant X Y) : (Set.range f).Finite :=
  f.isLocallyConstant.range_finite

/--
theorem `apply_eq_of_isPreconnected` / 定理 `apply_eq_of_isPreconnected`

English:
theorem apply_eq_of_isPreconnected
  statement: (f : LocallyConstant X Y) {s : Set X} (hs : IsPreconnected s)
  proof: f.isLocallyConstant.apply_eq_of_isPreconnected hs hx hy

中文:
定理 apply_eq_of_isPreconnected
  结论: (f : LocallyConstant X Y) {s : Set X} (hs : IsPreconnected s)
  证明: f.isLocallyConstant.apply_eq_of_isPreconnected hs hx hy

Depends on / 依赖: apply_eq_of_isPreconnected, f.isLocallyConstant.apply_eq_of_isPreconnected, isLocallyConstant
-/
theorem apply_eq_of_isPreconnected (f : LocallyConstant X Y) {s : Set X} (hs : IsPreconnected s)
    {x y : X} (hx : x in s) (hy : y in s) : f x = f y :=
  f.isLocallyConstant.apply_eq_of_isPreconnected hs hx hy

/--
theorem `apply_eq_of_preconnectedSpace` / 定理 `apply_eq_of_preconnectedSpace`

English:
theorem apply_eq_of_preconnectedSpace
  given: [PreconnectedSpace X] (f : LocallyConstant X Y) (x y : X)
  proof: f.isLocallyConstant.apply_eq_of_isPreconnected isPreconnected_univ trivial trivial

中文:
定理 apply_eq_of_preconnectedSpace
  条件: [PreconnectedSpace X] (f : LocallyConstant X Y) (x y : X)
  证明: f.isLocallyConstant.apply_eq_of_isPreconnected isPreconnected_univ trivial trivial

Depends on / 依赖: apply_eq_of_isPreconnected, f.isLocallyConstant.apply_eq_of_isPreconnected, isLocallyConstant, isPreconnected_univ
-/
theorem apply_eq_of_preconnectedSpace [PreconnectedSpace X] (f : LocallyConstant X Y) (x y : X) :
    f x = f y :=
  f.isLocallyConstant.apply_eq_of_isPreconnected isPreconnected_univ trivial trivial

/--
theorem `eq_const` / 定理 `eq_const`

English:
theorem eq_const
  given: [PreconnectedSpace X] (f : LocallyConstant X Y) (x : X)
  statement: f = const X (f x)
  proof: ext fun _ => apply_eq_of_preconnectedSpace f _ _

中文:
定理 eq_const
  条件: [PreconnectedSpace X] (f : LocallyConstant X Y) (x : X)
  结论: f = const X (f x)
  证明: ext fun _ => apply_eq_of_preconnectedSpace f _ _

Depends on / 依赖: apply_eq_of_preconnectedSpace
-/
theorem eq_const [PreconnectedSpace X] (f : LocallyConstant X Y) (x : X) : f = const X (f x) :=
  ext fun _ => apply_eq_of_preconnectedSpace f _ _

/--
theorem `exists_eq_const` / 定理 `exists_eq_const`

English:
theorem exists_eq_const
  given: [PreconnectedSpace X] [Nonempty Y] (f : LocallyConstant X Y)
  proof: by
  rcases Classical.em (Nonempty X) with (⟨⟨x⟩⟩ | hX)
  · exact ⟨f x, f.eq_const x⟩
  · exact ⟨Classical.arbitrary Y, ext fun x => (hX ⟨x⟩).elim⟩

中文:
定理 exists_eq_const
  条件: [PreconnectedSpace X] [Nonempty Y] (f : LocallyConstant X Y)
  证明: by
  rcases Classical.em (Nonempty X) with (⟨⟨x⟩⟩ | hX)
  · exact ⟨f x, f.eq_const x⟩
  · exact ⟨Classical.arbitrary Y, ext fun x => (hX ⟨x⟩).elim⟩

Depends on / 依赖: Classical, Classical.arbitrary, Classical.em, Nonempty, arbitrary, eq_const, f.eq_const
-/
theorem exists_eq_const [PreconnectedSpace X] [Nonempty Y] (f : LocallyConstant X Y) :
    exists y, f = const X y := by
  rcases Classical.em (Nonempty X) with (⟨⟨x⟩⟩ | hX)
  · exact ⟨f x, f.eq_const x⟩
  · exact ⟨Classical.arbitrary Y, ext fun x => (hX ⟨x⟩).elim⟩

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : Y -> Z) (g : LocallyConstant X Y)
  body: ⟨f ∘ g, g.isLocallyConstant.comp f⟩

@[simp]

中文:
定义 map
  签名: (f : Y -> Z) (g : LocallyConstant X Y)
  定义体: ⟨f ∘ g, g.isLocallyConstant.comp f⟩

@[simp]

Depends on / 依赖: g.isLocallyConstant.comp, isLocallyConstant
-/
def map (f : Y -> Z) (g : LocallyConstant X Y) : LocallyConstant X Z :=
  ⟨f ∘ g, g.isLocallyConstant.comp f⟩

@[simp]
/--
theorem `map_apply` / 定理 `map_apply`

English:
theorem map_apply
  given: (f : Y -> Z) (g : LocallyConstant X Y)
  statement: ⇑(map f g) = f ∘ g
  proof: rfl

@[simp]

中文:
定理 map_apply
  条件: (f : Y -> Z) (g : LocallyConstant X Y)
  结论: ⇑(map f g) = f ∘ g
  证明: rfl

@[simp]
-/
theorem map_apply (f : Y -> Z) (g : LocallyConstant X Y) : ⇑(map f g) = f ∘ g :=
  rfl

@[simp]
/--
theorem `map_id` / 定理 `map_id`

English:
theorem map_id
  statement: @map X Y Y _ id = id
  proof: rfl

@[simp]

中文:
定理 map_id
  结论: @map X Y Y _ id = id
  证明: rfl

@[simp]
-/
theorem map_id : @map X Y Y _ id = id := rfl

@[simp]
/--
theorem `map_comp` / 定理 `map_comp`

English:
theorem map_comp
  given: {Y₁ Y₂ Y₃ : Type*} (g : Y₂ -> Y₃) (f : Y₁ -> Y₂)
  proof: rfl

中文:
定理 map_comp
  条件: {Y₁ Y₂ Y₃ : 类型} (g : Y₂ -> Y₃) (f : Y₁ -> Y₂)
  证明: rfl
-/
theorem map_comp {Y₁ Y₂ Y₃ : Type*} (g : Y₂ -> Y₃) (f : Y₁ -> Y₂) :
    @map X _ _ _ g ∘ map f = map (g ∘ f) := rfl

/--
Definition of `flip` / `flip` 的定义

English:
definition flip
  signature: {X α β : Type*} [TopologicalSpace X] (f : LocallyConstant X (α -> β)) (a : α)
  body: f.map fun f => f a

中文:
定义 flip
  签名: {X α β : 类型} [TopologicalSpace X] (f : LocallyConstant X (α -> β)) (a : α)
  定义体: f.map fun f => f a

Depends on / 依赖: f.map
-/
def flip {X α β : Type*} [TopologicalSpace X] (f : LocallyConstant X (α -> β)) (a : α) :
    LocallyConstant X β :=
  f.map fun f => f a

/--
Definition of `unflip` / `unflip` 的定义

English:
definition unflip
  signature: {X α β : Type*} [Finite α] [TopologicalSpace X] (f : α -> LocallyConstant X β)
  body: f a x
  isLocallyConstant := IsLocallyConstant.iff_isOpen_fiber.2 fun g => by
    have : (fun (x : X) (a : α) => f a x) ⁻¹' {g} = ⋂ a : α, f a ⁻¹' {g a} := by
      ext; simp [funext_iff]
    rw [this]
    exact isOpen_iInter_of_finite fun a => (f a).isLocallyConstant _

@[simp]

中文:
定义 unflip
  签名: {X α β : 类型} [Finite α] [TopologicalSpace X] (f : α -> LocallyConstant X β)
  定义体: f a x
  isLocallyConstant := IsLocallyConstant.iff_isOpen_fiber.2 fun g => by
    have : (fun (x : X) (a : α) => f a x) ⁻¹' {g} = ⋂ a : α, f a ⁻¹' {g a} := by
      ext; simp [funext_iff]
    rw [this]
    exact isOpen_iInter_of_finite fun a => (f a).isLocallyConstant _

@[simp]
-/
def unflip {X α β : Type*} [Finite α] [TopologicalSpace X] (f : α -> LocallyConstant X β) :
    LocallyConstant X (α -> β) where
  toFun x a := f a x
  isLocallyConstant := IsLocallyConstant.iff_isOpen_fiber.2 fun g => by
    have : (fun (x : X) (a : α) => f a x) ⁻¹' {g} = ⋂ a : α, f a ⁻¹' {g a} := by
      ext; simp [funext_iff]
    rw [this]
    exact isOpen_iInter_of_finite fun a => (f a).isLocallyConstant _

@[simp]
/--
theorem `unflip_flip` / 定理 `unflip_flip`

English:
theorem unflip_flip
  statement: {X α β : Type*} [Finite α] [TopologicalSpace X]
  proof: rfl

@[simp]

中文:
定理 unflip_flip
  结论: {X α β : 类型} [Finite α] [TopologicalSpace X]
  证明: rfl

@[simp]
-/
theorem unflip_flip {X α β : Type*} [Finite α] [TopologicalSpace X]
    (f : LocallyConstant X (α -> β)) : unflip f.flip = f := rfl

@[simp]
/--
theorem `flip_unflip` / 定理 `flip_unflip`

English:
theorem flip_unflip
  statement: {X α β : Type*} [Finite α] [TopologicalSpace X]
  proof: rfl

中文:
定理 flip_unflip
  结论: {X α β : 类型} [Finite α] [TopologicalSpace X]
  证明: rfl
-/
theorem flip_unflip {X α β : Type*} [Finite α] [TopologicalSpace X]
    (f : α -> LocallyConstant X β) : (unflip f).flip = f := rfl

section Comap

variable [TopologicalSpace Y]

/--
Definition of `comap` / `comap` 的定义

English:
definition comap
  signature: (f : C(X, Y)) (g : LocallyConstant Y Z)
  body: ⟨g ∘ f, g.isLocallyConstant.comp_continuous f.continuous⟩

@[simp]

中文:
定义 comap
  签名: (f : C(X, Y)) (g : LocallyConstant Y Z)
  定义体: ⟨g ∘ f, g.isLocallyConstant.comp_continuous f.continuous⟩

@[simp]

Depends on / 依赖: comp_continuous, continuous, f.continuous, g.isLocallyConstant.comp_continuous, isLocallyConstant
-/
def comap (f : C(X, Y)) (g : LocallyConstant Y Z) : LocallyConstant X Z :=
  ⟨g ∘ f, g.isLocallyConstant.comp_continuous f.continuous⟩

@[simp]
/--
theorem `coe_comap` / 定理 `coe_comap`

English:
theorem coe_comap
  given: (f : C(X, Y)) (g : LocallyConstant Y Z)
  proof: rfl

中文:
定理 coe_comap
  条件: (f : C(X, Y)) (g : LocallyConstant Y Z)
  证明: rfl
-/
theorem coe_comap (f : C(X, Y)) (g : LocallyConstant Y Z) :
    (comap f g) = g ∘ f := rfl

/--
theorem `coe_comap_apply` / 定理 `coe_comap_apply`

English:
theorem coe_comap_apply
  given: (f : C(X, Y)) (g : LocallyConstant Y Z) (x : X)
  proof: rfl

@[simp]

中文:
定理 coe_comap_apply
  条件: (f : C(X, Y)) (g : LocallyConstant Y Z) (x : X)
  证明: rfl

@[simp]
-/
theorem coe_comap_apply (f : C(X, Y)) (g : LocallyConstant Y Z) (x : X) :
    comap f g x = g (f x) := rfl

@[simp]
/--
theorem `comap_id` / 定理 `comap_id`

English:
theorem comap_id
  statement: comap (@ContinuousMap.id X _) = @id (LocallyConstant X Z)
  proof: rfl

中文:
定理 comap_id
  结论: comap (@ContinuousMap.id X _) = @id (LocallyConstant X Z)
  证明: rfl
-/
theorem comap_id : comap (@ContinuousMap.id X _) = @id (LocallyConstant X Z) := rfl

/--
theorem `comap_comp` / 定理 `comap_comp`

English:
theorem comap_comp
  given: {W : Type*} [TopologicalSpace W] (f : C(W, X)) (g : C(X, Y))
  proof: rfl

中文:
定理 comap_comp
  条件: {W : 类型} [TopologicalSpace W] (f : C(W, X)) (g : C(X, Y))
  证明: rfl

Depends on / 依赖: g.comp
-/
theorem comap_comp {W : Type*} [TopologicalSpace W] (f : C(W, X)) (g : C(X, Y)) :
    comap (Z := Z) (g.comp f) = comap f ∘ comap g := rfl

/--
theorem `comap_comap` / 定理 `comap_comap`

English:
theorem comap_comap
  statement: {W : Type*} [TopologicalSpace W] (f : C(W, X)) (g : C(X, Y))
  proof: rfl

中文:
定理 comap_comap
  结论: {W : 类型} [TopologicalSpace W] (f : C(W, X)) (g : C(X, Y))
  证明: rfl
-/
theorem comap_comap {W : Type*} [TopologicalSpace W] (f : C(W, X)) (g : C(X, Y))
    (x : LocallyConstant Y Z) : comap f (comap g x) = comap (g.comp f) x := rfl

/--
theorem `comap_const` / 定理 `comap_const`

English:
theorem comap_const
  given: (f : C(X, Y)) (y : Y) (h : forall x, f x = y)
  proof: by
  ext; simp [h]

中文:
定理 comap_const
  条件: (f : C(X, Y)) (y : Y) (h : 对任意 x, f x = y)
  证明: by
  ext; simp [h]
-/
theorem comap_const (f : C(X, Y)) (y : Y) (h : forall x, f x = y) :
    (comap f : LocallyConstant Y Z -> LocallyConstant X Z) = fun g => const X (g y) := by
  ext; simp [h]

/--
lemma `comap_injective` / 引理 `comap_injective`

English:
lemma comap_injective
  given: (f : C(X, Y)) (hfs : f.1.Surjective)
  proof: by
  intro a b h
  ext y
  obtain ⟨x, hx⟩ := hfs y
  simpa [← hx] using LocallyConstant.congr_fun h x

中文:
引理 comap_injective
  条件: (f : C(X, Y)) (hfs : f.1.Surjective)
  证明: by
  intro a b h
  ext y
  obtain ⟨x, hx⟩ := hfs y
  simpa [← hx] using LocallyConstant.congr_fun h x

Depends on / 依赖: Injective, LocallyConstant, LocallyConstant.congr_fun, congr_fun
-/
lemma comap_injective (f : C(X, Y)) (hfs : f.1.Surjective) :
    (comap (Z := Z) f).Injective := by
  intro a b h
  ext y
  obtain ⟨x, hx⟩ := hfs y
  simpa [← hx] using LocallyConstant.congr_fun h x

end Comap

section Desc

/--
Definition of `desc` / `desc` 的定义

English:
definition desc
  signature: {X α β : Type*} [TopologicalSpace X] {g : α -> β} (f : X -> α) (h : LocallyConstant X β)
  body: f
  isLocallyConstant := IsLocallyConstant.desc _ g (cond.symm ▸ h.isLocallyConstant) inj

@[simp]

中文:
定义 desc
  签名: {X α β : 类型} [TopologicalSpace X] {g : α -> β} (f : X -> α) (h : LocallyConstant X β)
  定义体: f
  isLocallyConstant := IsLocallyConstant.desc _ g (cond.symm ▸ h.isLocallyConstant) inj

@[simp]
-/
def desc {X α β : Type*} [TopologicalSpace X] {g : α -> β} (f : X -> α) (h : LocallyConstant X β)
    (cond : g ∘ f = h) (inj : Function.Injective g) : LocallyConstant X α where
  toFun := f
  isLocallyConstant := IsLocallyConstant.desc _ g (cond.symm ▸ h.isLocallyConstant) inj

@[simp]
/--
theorem `coe_desc` / 定理 `coe_desc`

English:
theorem coe_desc
  statement: {X α β : Type*} [TopologicalSpace X] (f : X -> α) (g : α -> β)
  proof: rfl

中文:
定理 coe_desc
  结论: {X α β : 类型} [TopologicalSpace X] (f : X -> α) (g : α -> β)
  证明: rfl
-/
theorem coe_desc {X α β : Type*} [TopologicalSpace X] (f : X -> α) (g : α -> β)
    (h : LocallyConstant X β) (cond : g ∘ f = h) (inj : Function.Injective g) :
    ⇑(desc f h cond inj) = f :=
  rfl

end Desc

section Indicator

variable {R : Type*} [One R] {U : Set X} (f : LocallyConstant X R)

/-- Given a clopen set `U` and a locally constant function `f`, `LocallyConstant.mulIndicator`
  returns the locally constant function that is `f` on `U` and `1` otherwise. -/
@[to_additive (attr := simps) /-- Given a clopen set `U` and a locally constant function `f`,
  `LocallyConstant.indicator` returns the locally constant function that is `f` on `U` and `0`
  otherwise. -/]
/--
Definition of `mulIndicator` / `mulIndicator` 的定义

English:
definition mulIndicator
  signature: (hU : IsClopen U)
  body: Set.mulIndicator U f
  isLocallyConstant := fun s => by
    rw [mulIndicator_preimage]; rw [Set.ite]; rw [Set.sdiff_eq]
    exact ((f.2 s).inter hU.isOpen).union ((IsLocallyConstant.const 1 s).inter hU.compl.isOpen)

中文:
定义 mulIndicator
  签名: (hU : IsClopen U)
  定义体: Set.mulIndicator U f
  isLocallyConstant := fun s => by
    rw [mulIndicator_preimage]; rw [Set.ite]; rw [Set.sdiff_eq]
    exact ((f.2 s).inter hU.isOpen).union ((IsLocallyConstant.const 1 s).inter hU.compl.isOpen)

Depends on / 依赖: Set.mulIndicator, mulIndicator
-/
noncomputable def mulIndicator (hU : IsClopen U) : LocallyConstant X R where
  toFun := Set.mulIndicator U f
  isLocallyConstant := fun s => by
    rw [mulIndicator_preimage]; rw [Set.ite]; rw [Set.sdiff_eq]
    exact ((f.2 s).inter hU.isOpen).union ((IsLocallyConstant.const 1 s).inter hU.compl.isOpen)

variable (a : X)

open scoped Classical in
@[to_additive]
/--
theorem `mulIndicator_apply_eq_if` / 定理 `mulIndicator_apply_eq_if`

English:
theorem mulIndicator_apply_eq_if
  given: (hU : IsClopen U)
  proof: Set.mulIndicator_apply U f a

中文:
定理 mulIndicator_apply_eq_if
  条件: (hU : IsClopen U)
  证明: Set.mulIndicator_apply U f a

Depends on / 依赖: Set.mulIndicator_apply, mulIndicator_apply
-/
theorem mulIndicator_apply_eq_if (hU : IsClopen U) :
    mulIndicator f hU a = if a in U then f a else 1 :=
  Set.mulIndicator_apply U f a

variable {a}

@[to_additive]
/--
theorem `mulIndicator_of_mem` / 定理 `mulIndicator_of_mem`

English:
theorem mulIndicator_of_mem
  given: (hU : IsClopen U) (h : a in U)
  statement: f.mulIndicator hU a = f a
  proof: Set.mulIndicator_of_mem h _

@[to_additive]

中文:
定理 mulIndicator_of_mem
  条件: (hU : IsClopen U) (h : a in U)
  结论: f.mulIndicator hU a = f a
  证明: Set.mulIndicator_of_mem h _

@[to_additive]

Depends on / 依赖: Set.mulIndicator_of_mem, mulIndicator_of_mem
-/
theorem mulIndicator_of_mem (hU : IsClopen U) (h : a in U) : f.mulIndicator hU a = f a :=
  Set.mulIndicator_of_mem h _

@[to_additive]
/--
theorem `mulIndicator_of_notMem` / 定理 `mulIndicator_of_notMem`

English:
theorem mulIndicator_of_notMem
  given: (hU : IsClopen U) (h : a ∉ U)
  statement: f.mulIndicator hU a = 1
  proof: Set.mulIndicator_of_notMem h _

中文:
定理 mulIndicator_of_notMem
  条件: (hU : IsClopen U) (h : a ∉ U)
  结论: f.mulIndicator hU a = 1
  证明: Set.mulIndicator_of_notMem h _

Depends on / 依赖: Set.mulIndicator_of_notMem, mulIndicator_of_notMem
-/
theorem mulIndicator_of_notMem (hU : IsClopen U) (h : a ∉ U) : f.mulIndicator hU a = 1 :=
  Set.mulIndicator_of_notMem h _

end Indicator

section Equiv

/--
The equivalence between `LocallyConstant X Z` and `LocallyConstant Y Z` given a
homeomorphism `X ≃ₜ Y`
-/
@[simps]
/--
Definition of `congrLeft` / `congrLeft` 的定义

English:
definition congrLeft
  signature: [TopologicalSpace Y] (e : X ≃ₜ Y)
  body: comap e.symm
  invFun := comap e
  left_inv := by
    intro
    simp [comap_comap]
  right_inv := by
    intro
    simp [comap_comap]

中文:
定义 congrLeft
  签名: [TopologicalSpace Y] (e : X ≃ₜ Y)
  定义体: comap e.symm
  invFun := comap e
  left_inv := by
    intro
    simp [comap_comap]
  right_inv := by
    intro
    simp [comap_comap]

Depends on / 依赖: e.symm
-/
def congrLeft [TopologicalSpace Y] (e : X ≃ₜ Y) : LocallyConstant X Z ≃ LocallyConstant Y Z where
  toFun := comap e.symm
  invFun := comap e
  left_inv := by
    intro
    simp [comap_comap]
  right_inv := by
    intro
    simp [comap_comap]

/--
The equivalence between `LocallyConstant X Y` and `LocallyConstant X Z` given an
equivalence `Y ≃ Z`
-/
@[simps]
/--
Definition of `congrRight` / `congrRight` 的定义

English:
definition congrRight
  signature: (e : Y ≃ Z)
  body: map e
  invFun := map e.symm
  left_inv := by intro; ext; simp
  right_inv := by intro; ext; simp

中文:
定义 congrRight
  签名: (e : Y ≃ Z)
  定义体: map e
  invFun := map e.symm
  left_inv := by intro; ext; simp
  right_inv := by intro; ext; simp
-/
def congrRight (e : Y ≃ Z) : LocallyConstant X Y ≃ LocallyConstant X Z where
  toFun := map e
  invFun := map e.symm
  left_inv := by intro; ext; simp
  right_inv := by intro; ext; simp

variable (X) in
/--
Definition of `equivClopens` / `equivClopens` 的定义

English:
definition equivClopens
  signature: [forall (s : Set X) x, Decidable (x in s)]
  body: ⟨f ⁻¹' {0}, f.2.isClopen_fiber _⟩
  invFun s := ofIsClopen s.2
  left_inv _ := locallyConstant_eq_of_fiber_zero_eq _ _ (by simp)
  right_inv _ := by simp

中文:
定义 equivClopens
  签名: [对任意 (s : Set X) x, Decidable (x in s)]
  定义体: ⟨f ⁻¹' {0}, f.2.isClopen_fiber _⟩
  invFun s := ofIsClopen s.2
  left_inv _ := locallyConstant_eq_of_fiber_zero_eq _ _ (by simp)
  right_inv _ := by simp

Depends on / 依赖: isClopen_fiber
-/
def equivClopens [forall (s : Set X) x, Decidable (x in s)] :
    LocallyConstant X (Fin 2) ≃ TopologicalSpace.Clopens X where
  toFun f := ⟨f ⁻¹' {0}, f.2.isClopen_fiber _⟩
  invFun s := ofIsClopen s.2
  left_inv _ := locallyConstant_eq_of_fiber_zero_eq _ _ (by simp)
  right_inv _ := by simp

end Equiv

section Piecewise

/--
Definition of `piecewise` / `piecewise` 的定义

English:
definition piecewise
  signature: {C₁ C₂ : Set X} (h₁ : IsClosed C₁) (h₂ : IsClosed C₂) (h : C₁ union C₂ = Set.univ)
  body: if hi : i in C₁ then f ⟨i, hi⟩ else g ⟨i, (Set.compl_subset_iff_union.mpr h) hi⟩
  isLocallyConstant := by
    let dZ : TopologicalSpace Z := ⊥
    have : DiscreteTopology Z := discreteTopology_bot Z
    obtain ⟨f, hf⟩ := f
    obtain ⟨g, hg⟩ := g
    rw [IsLocallyConstant.iff_continuous] at hf hg ⊢

中文:
定义 piecewise
  签名: {C₁ C₂ : Set X} (h₁ : IsClosed C₁) (h₂ : IsClosed C₂) (h : C₁ union C₂ = Set.univ)
  定义体: if hi : i in C₁ then f ⟨i, hi⟩ else g ⟨i, (Set.compl_subset_iff_union.mpr h) hi⟩
  isLocallyConstant := by
    let dZ : TopologicalSpace Z := ⊥
    have : DiscreteTopology Z := discreteTopology_bot Z
    obtain ⟨f, hf⟩ := f
    obtain ⟨g, hg⟩ := g
    rw [IsLocallyConstant.iff_continuous] at hf hg ⊢

Depends on / 依赖: Set.compl_subset_iff_union.mpr, compl_subset_iff_union
-/
def piecewise {C₁ C₂ : Set X} (h₁ : IsClosed C₁) (h₂ : IsClosed C₂) (h : C₁ union C₂ = Set.univ)
    (f : LocallyConstant C₁ Z) (g : LocallyConstant C₂ Z)
    (hfg : forall (x : X) (hx : x in C₁ inter C₂), f ⟨x, hx.1⟩ = g ⟨x, hx.2⟩)
    [DecidablePred (· in C₁)] : LocallyConstant X Z where
  toFun i := if hi : i in C₁ then f ⟨i, hi⟩ else g ⟨i, (Set.compl_subset_iff_union.mpr h) hi⟩
  isLocallyConstant := by
    let dZ : TopologicalSpace Z := ⊥
    have : DiscreteTopology Z := discreteTopology_bot Z
    obtain ⟨f, hf⟩ := f
    obtain ⟨g, hg⟩ := g
    rw [IsLocallyConstant.iff_continuous] at hf hg ⊢
    dsimp only [coe_mk]
    rw [Set.union_eq_iUnion] at h
    refine (locallyFinite_of_finite _).continuous h (fun i => ?_) (fun i => ?_)
    · cases i <;> [exact h₂; exact h₁]
    · cases i <;> rw [continuousOn_iff_continuous_domRestrict]
      · convert! hg
        ext x
        simp only [cond_false, domRestrict_apply, Subtype.coe_eta, dite_eq_right_iff]
        exact fun hx => hfg x ⟨hx, x.prop⟩
      · simp only [cond_true, domRestrict_dite, Subtype.coe_eta]
        exact hf

@[simp]
/--
lemma `piecewise_apply_left` / 引理 `piecewise_apply_left`

English:
lemma piecewise_apply_left
  statement: {C₁ C₂ : Set X} (h₁ : IsClosed C₁) (h₂ : IsClosed C₂)
  proof: by
  simp only [piecewise,
    coe_mk]
  rw [dif_pos hx]

@[simp]

中文:
引理 piecewise_apply_left
  结论: {C₁ C₂ : Set X} (h₁ : IsClosed C₁) (h₂ : IsClosed C₂)
  证明: by
  simp only [piecewise,
    coe_mk]
  rw [dif_pos hx]

@[simp]

Depends on / 依赖: coe_mk, dif_pos, piecewise
-/
lemma piecewise_apply_left {C₁ C₂ : Set X} (h₁ : IsClosed C₁) (h₂ : IsClosed C₂)
    (h : C₁ union C₂ = Set.univ) (f : LocallyConstant C₁ Z) (g : LocallyConstant C₂ Z)
    (hfg : forall (x : X) (hx : x in C₁ inter C₂), f ⟨x, hx.1⟩ = g ⟨x, hx.2⟩)
    [DecidablePred (· in C₁)] (x : X) (hx : x in C₁) :
    piecewise h₁ h₂ h f g hfg x = f ⟨x, hx⟩ := by
  simp only [piecewise,
    coe_mk]
  rw [dif_pos hx]

@[simp]
/--
lemma `piecewise_apply_right` / 引理 `piecewise_apply_right`

English:
lemma piecewise_apply_right
  statement: {C₁ C₂ : Set X} (h₁ : IsClosed C₁) (h₂ : IsClosed C₂)
  proof: by
  simp only [piecewise,
    coe_mk]
  split_ifs with h
  · exact hfg x ⟨h, hx⟩
  · rfl

中文:
引理 piecewise_apply_right
  结论: {C₁ C₂ : Set X} (h₁ : IsClosed C₁) (h₂ : IsClosed C₂)
  证明: by
  simp only [piecewise,
    coe_mk]
  split_ifs with h
  · exact hfg x ⟨h, hx⟩
  · rfl

Depends on / 依赖: coe_mk, piecewise, split_ifs
-/
lemma piecewise_apply_right {C₁ C₂ : Set X} (h₁ : IsClosed C₁) (h₂ : IsClosed C₂)
    (h : C₁ union C₂ = Set.univ) (f : LocallyConstant C₁ Z) (g : LocallyConstant C₂ Z)
    (hfg : forall (x : X) (hx : x in C₁ inter C₂), f ⟨x, hx.1⟩ = g ⟨x, hx.2⟩)
    [DecidablePred (· in C₁)] (x : X) (hx : x in C₂) :
    piecewise h₁ h₂ h f g hfg x = g ⟨x, hx⟩ := by
  simp only [piecewise,
    coe_mk]
  split_ifs with h
  · exact hfg x ⟨h, hx⟩
  · rfl

/--
Definition of `piecewise'` / `piecewise'` 的定义

English:
definition piecewise'
  signature: {C₀ C₁ C₂ : Set X} (h₀ : C₀ subseteq C₁ union C₂) (h₁ : IsClosed C₁)
  body: letI : forall j : C₀, Decidable (j in Subtype.val ⁻¹' C₁) := fun j => decidable_of_iff (↑j in C₁) Iff.rfl
  piecewise (h₁.preimage continuous_subtype_val) (h₂.preimage continuous_subtype_val)
    (by simpa [eq_univ_iff_forall] using! h₀)
    (f₁.comap ⟨(restrictPreimage C₁ ((↑) : C₀ -> X)), continuo

中文:
定义 piecewise'
  签名: {C₀ C₁ C₂ : Set X} (h₀ : C₀ subseteq C₁ union C₂) (h₁ : IsClosed C₁)
  定义体: letI : forall j : C₀, Decidable (j in Subtype.val ⁻¹' C₁) := fun j => decidable_of_iff (↑j in C₁) Iff.rfl
  piecewise (h₁.preimage continuous_subtype_val) (h₂.preimage continuous_subtype_val)
    (by simpa [eq_univ_iff_forall] using! h₀)
    (f₁.comap ⟨(restrictPreimage C₁ ((↑) : C₀ -> X)), continuo

Depends on / 依赖: Decidable, Iff.rfl, Subtype, Subtype.val, continuous_subtype_val, continuous_subtype_val.restrictPreimage, decidable_of_iff, eq_univ_iff_forall, piecewise, preimage, restrictPreimage
-/
def piecewise' {C₀ C₁ C₂ : Set X} (h₀ : C₀ subseteq C₁ union C₂) (h₁ : IsClosed C₁)
    (h₂ : IsClosed C₂) (f₁ : LocallyConstant C₁ Z) (f₂ : LocallyConstant C₂ Z)
    [DecidablePred (· in C₁)] (hf : forall x (hx : x in C₁ inter C₂), f₁ ⟨x, hx.1⟩ = f₂ ⟨x, hx.2⟩) :
    LocallyConstant C₀ Z :=
  letI : forall j : C₀, Decidable (j in Subtype.val ⁻¹' C₁) := fun j => decidable_of_iff (↑j in C₁) Iff.rfl
  piecewise (h₁.preimage continuous_subtype_val) (h₂.preimage continuous_subtype_val)
    (by simpa [eq_univ_iff_forall] using! h₀)
    (f₁.comap ⟨(restrictPreimage C₁ ((↑) : C₀ -> X)), continuous_subtype_val.restrictPreimage⟩)
(f₂.comap ⟨(restrictPreimage C₂ ((↑) : C₀ -> X)), continuous_subtype_val.restrictPreimage⟩) by
      rintro ⟨x, hx₀⟩ ⟨hx₁ : x in C₁, hx₂ : x in C₂⟩
      simpa using hf x ⟨hx₁, hx₂⟩

@[simp]
/--
lemma `piecewise'_apply_left` / 引理 `piecewise'_apply_left`

English:
lemma piecewise'_apply_left
  statement: {C₀ C₁ C₂ : Set X} (h₀ : C₀ subseteq C₁ union C₂) (h₁ : IsClosed C₁)
  proof: by
  let : forall j : C₀, Decidable (j in Subtype.val ⁻¹' C₁) := fun j => decidable_of_iff (↑j in C₁) Iff.rfl
  rw [piecewise']; rw [piecewise_apply_left (f := (f₁.comap
    ⟨(restrictPreimage C₁ ((↑) : C₀ -> X))]; rw [continuous_subtype_val.restrictPreimage⟩))
    (hx := hx)]
  rfl

@[simp]

中文:
引理 piecewise'_apply_left
  结论: {C₀ C₁ C₂ : Set X} (h₀ : C₀ subseteq C₁ union C₂) (h₁ : IsClosed C₁)
  证明: by
  let : forall j : C₀, Decidable (j in Subtype.val ⁻¹' C₁) := fun j => decidable_of_iff (↑j in C₁) Iff.rfl
  rw [piecewise']; rw [piecewise_apply_left (f := (f₁.comap
    ⟨(restrictPreimage C₁ ((↑) : C₀ -> X))]; rw [continuous_subtype_val.restrictPreimage⟩))
    (hx := hx)]
  rfl

@[simp]
-/
lemma piecewise'_apply_left {C₀ C₁ C₂ : Set X} (h₀ : C₀ subseteq C₁ union C₂) (h₁ : IsClosed C₁)
    (h₂ : IsClosed C₂) (f₁ : LocallyConstant C₁ Z) (f₂ : LocallyConstant C₂ Z)
    [DecidablePred (· in C₁)] (hf : forall x (hx : x in C₁ inter C₂), f₁ ⟨x, hx.1⟩ = f₂ ⟨x, hx.2⟩)
    (x : C₀) (hx : x.val in C₁) :
    piecewise' h₀ h₁ h₂ f₁ f₂ hf x = f₁ ⟨x.val, hx⟩ := by
  let : forall j : C₀, Decidable (j in Subtype.val ⁻¹' C₁) := fun j => decidable_of_iff (↑j in C₁) Iff.rfl
  rw [piecewise']; rw [piecewise_apply_left (f := (f₁.comap
    ⟨(restrictPreimage C₁ ((↑) : C₀ -> X))]; rw [continuous_subtype_val.restrictPreimage⟩))
    (hx := hx)]
  rfl

@[simp]
/--
lemma `piecewise'_apply_right` / 引理 `piecewise'_apply_right`

English:
lemma piecewise'_apply_right
  statement: {C₀ C₁ C₂ : Set X} (h₀ : C₀ subseteq C₁ union C₂) (h₁ : IsClosed C₁)
  proof: by
  let : forall j : C₀, Decidable (j in Subtype.val ⁻¹' C₁) := fun j => decidable_of_iff (↑j in C₁) Iff.rfl
  rw [piecewise']; rw [piecewise_apply_right (f := (f₁.comap
    ⟨(restrictPreimage C₁ ((↑) : C₀ -> X))]; rw [continuous_subtype_val.restrictPreimage⟩))
    (hx := hx)]
  rfl

中文:
引理 piecewise'_apply_right
  结论: {C₀ C₁ C₂ : Set X} (h₀ : C₀ subseteq C₁ union C₂) (h₁ : IsClosed C₁)
  证明: by
  let : forall j : C₀, Decidable (j in Subtype.val ⁻¹' C₁) := fun j => decidable_of_iff (↑j in C₁) Iff.rfl
  rw [piecewise']; rw [piecewise_apply_right (f := (f₁.comap
    ⟨(restrictPreimage C₁ ((↑) : C₀ -> X))]; rw [continuous_subtype_val.restrictPreimage⟩))
    (hx := hx)]
  rfl
-/
lemma piecewise'_apply_right {C₀ C₁ C₂ : Set X} (h₀ : C₀ subseteq C₁ union C₂) (h₁ : IsClosed C₁)
    (h₂ : IsClosed C₂) (f₁ : LocallyConstant C₁ Z) (f₂ : LocallyConstant C₂ Z)
    [DecidablePred (· in C₁)] (hf : forall x (hx : x in C₁ inter C₂), f₁ ⟨x, hx.1⟩ = f₂ ⟨x, hx.2⟩)
    (x : C₀) (hx : x.val in C₂) :
    piecewise' h₀ h₁ h₂ f₁ f₂ hf x = f₂ ⟨x.val, hx⟩ := by
  let : forall j : C₀, Decidable (j in Subtype.val ⁻¹' C₁) := fun j => decidable_of_iff (↑j in C₁) Iff.rfl
  rw [piecewise']; rw [piecewise_apply_right (f := (f₁.comap
    ⟨(restrictPreimage C₁ ((↑) : C₀ -> X))]; rw [continuous_subtype_val.restrictPreimage⟩))
    (hx := hx)]
  rfl

end Piecewise

end LocallyConstant
