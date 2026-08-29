/-
Copyright (c) 2019 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
module

public import Mathlib.Topology.UniformSpace.UniformEmbedding
public import Mathlib.Topology.UniformSpace.Equiv

/-!
# Abstract theory of Hausdorff completions of uniform spaces

This file characterizes Hausdorff completions of a uniform space α as complete Hausdorff spaces
equipped with a map from α which has dense image and induces the original uniform structure on α.
Assuming these properties we "extend" uniformly continuous maps from α to complete Hausdorff spaces
to the completions of α. This is the universal property expected from a completion.
It is then used to extend uniformly continuous maps from α to α' to maps between
completions of α and α'.

This file does not construct any such completion; it only studies consequences of their existence.
The first advantage is that formal properties are clearly highlighted without interference from
construction details. The second advantage is that this framework can then be used to compare
different completion constructions. See `Topology/UniformSpace/CompareReals` for an example.
Of course the comparison comes from the universal property as usual.

A general explicit construction of completions is done in `UniformSpace/Completion`, leading
to a functor from uniform spaces to complete Hausdorff uniform spaces that is left adjoint to the
inclusion, see `UniformSpace/UniformSpaceCat` for the category packaging.

## Implementation notes

A tiny technical advantage of using a characteristic predicate such as the properties listed in
`AbstractCompletion` instead of stating the universal property is that the universal property
derived from the predicate is more universe polymorphic.

## References

We don't know any traditional text discussing this. Real world mathematics simply silently
identify the results of any two constructions that lead to something one could reasonably
call a completion.

## Tags

uniform spaces, completion, universal property
-/

@[expose] public section


noncomputable section

open Filter Set Function

/-- A completion of `α` is the data of a complete separated uniform space
and a map from `α` with dense range and inducing the original uniform structure on `α`. -/
@[pp_with_univ]
/--
Definition of `AbstractCompletion.` / `AbstractCompletion.` 的定义

English:
structure AbstractCompletion.{v,
  parameters: u} (α
  axioms and operations (7):
    - space : Type v
    - coe : α -> space
    - uniformStruct : UniformSpace space
    - complete : CompleteSpace space
    - separation : T0Space space
    - isUniformInducing : IsUniformInducing coe
    - dense : DenseRange coe

中文:
结构 AbstractCompletion.{v,
  参数: u} (α
  公理与运算 (7 个):
    - space : 类型v
    - coe : α -> space
    - uniformStruct : UniformSpace space
    - complete : CompleteSpace space
    - separation : T0Space space
    - isUniformInducing : IsUniformInducing coe
    - dense : DenseRange coe
-/
structure AbstractCompletion.{v, u} (α : Type u) [UniformSpace α] where
  /-- The underlying space of the completion. -/
  space : Type v
  /-- A map from a space to its completion. -/
  coe : α -> space
  /-- The completion carries a uniform structure. -/
  uniformStruct : UniformSpace space
  /-- The completion is complete. -/
  complete : CompleteSpace space
  /-- The completion is a T₀ space. -/
  separation : T0Space space
  /-- The map into the completion is uniform-inducing. -/
  isUniformInducing : IsUniformInducing coe
  /-- The map into the completion has dense range. -/
  dense : DenseRange coe

attribute [local instance]
  AbstractCompletion.uniformStruct AbstractCompletion.complete AbstractCompletion.separation

namespace AbstractCompletion

universe uα vα vα' uβ vβ uγ vγ

variable {α : Type uα} [UniformSpace α] (pkg : AbstractCompletion.{vα} α)

local notation "hatα" => pkg.space

local notation "ι" => pkg.coe

/--
Definition of `ofComplete` / `ofComplete` 的定义

English:
definition ofComplete
  signature: [T0Space α] [CompleteSpace α]
  body: mk α id inferInstance inferInstance inferInstance .id denseRange_id

中文:
定义 ofComplete
  签名: [T0Space α] [CompleteSpace α]
  定义体: mk α id inferInstance inferInstance inferInstance .id denseRange_id

Depends on / 依赖: denseRange_id
-/
def ofComplete [T0Space α] [CompleteSpace α] : AbstractCompletion α :=
  mk α id inferInstance inferInstance inferInstance .id denseRange_id

/--
theorem `closure_range` / 定理 `closure_range`

English:
theorem closure_range
  statement: closure (range ι) = univ
  proof: pkg.dense.closure_range

中文:
定理 closure_range
  结论: closure (range ι) = univ
  证明: pkg.dense.closure_range

Depends on / 依赖: closure_range, pkg.dense.closure_range
-/
theorem closure_range : closure (range ι) = univ :=
  pkg.dense.closure_range

/--
theorem `isDenseInducing` / 定理 `isDenseInducing`

English:
theorem isDenseInducing
  statement: IsDenseInducing ι
  proof: ⟨pkg.isUniformInducing.isInducing, pkg.dense⟩

@[fun_prop]

中文:
定理 isDenseInducing
  结论: IsDenseInducing ι
  证明: ⟨pkg.isUniformInducing.isInducing, pkg.dense⟩

@[fun_prop]

Depends on / 依赖: isInducing, isUniformInducing, pkg.dense, pkg.isUniformInducing.isInducing
-/
theorem isDenseInducing : IsDenseInducing ι :=
  ⟨pkg.isUniformInducing.isInducing, pkg.dense⟩

@[fun_prop]
/--
theorem `uniformContinuous_coe` / 定理 `uniformContinuous_coe`

English:
theorem uniformContinuous_coe
  statement: UniformContinuous ι
  proof: IsUniformInducing.uniformContinuous pkg.isUniformInducing

中文:
定理 uniformContinuous_coe
  结论: UniformContinuous ι
  证明: IsUniformInducing.uniformContinuous pkg.isUniformInducing

Depends on / 依赖: IsUniformInducing, IsUniformInducing.uniformContinuous, isUniformInducing, pkg.isUniformInducing, uniformContinuous
-/
theorem uniformContinuous_coe : UniformContinuous ι :=
  IsUniformInducing.uniformContinuous pkg.isUniformInducing

/--
theorem `continuous_coe` / 定理 `continuous_coe`

English:
theorem continuous_coe
  statement: Continuous ι
  proof: pkg.uniformContinuous_coe.continuous

@[elab_as_elim]

中文:
定理 continuous_coe
  结论: Continuous ι
  证明: pkg.uniformContinuous_coe.continuous

@[elab_as_elim]

Depends on / 依赖: continuous, pkg.uniformContinuous_coe.continuous, uniformContinuous_coe
-/
theorem continuous_coe : Continuous ι :=
  pkg.uniformContinuous_coe.continuous

@[elab_as_elim]
/--
theorem `induction_on` / 定理 `induction_on`

English:
theorem induction_on
  given: {p : hatα -> Prop} (a : hatα) (hp : IsClosed { a | p a }) (ih : forall a, p (ι a))
  proof: isClosed_property pkg.dense hp ih a

中文:
定理 induction_on
  条件: {p : hatα -> 命题} (a : hatα) (hp : IsClosed { a | p a }) (ih : 对任意 a, p (ι a))
  证明: isClosed_property pkg.dense hp ih a

Depends on / 依赖: isClosed_property, pkg.dense
-/
theorem induction_on {p : hatα -> Prop} (a : hatα) (hp : IsClosed { a | p a }) (ih : forall a, p (ι a)) :
    p a :=
  isClosed_property pkg.dense hp ih a

variable {β : Type uβ}

/--
theorem `funext` / 定理 `funext`

English:
theorem funext
  statement: [TopologicalSpace β] [T2Space β] {f g : hatα -> β} (hf : Continuous f)
  proof: funext fun a => pkg.induction_on a (isClosed_eq hf hg) h

中文:
定理 funext
  结论: [TopologicalSpace β] [T2Space β] {f g : hatα -> β} (hf : Continuous f)
  证明: funext fun a => pkg.induction_on a (isClosed_eq hf hg) h
-/
protected theorem funext [TopologicalSpace β] [T2Space β] {f g : hatα -> β} (hf : Continuous f)
    (hg : Continuous g) (h : forall a, f (ι a) = g (ι a)) : f = g :=
  funext fun a => pkg.induction_on a (isClosed_eq hf hg) h

variable [UniformSpace β]

section Extend

/--
Definition of `extend` / `extend` 的定义

English:
definition extend
  signature: (f : α -> β)
  body: open scoped Classical in
  if UniformContinuous f then pkg.isDenseInducing.extend f else fun x => f (pkg.dense.some x)

中文:
定义 extend
  签名: (f : α -> β)
  定义体: open scoped Classical in
  if UniformContinuous f then pkg.isDenseInducing.extend f else fun x => f (pkg.dense.some x)
-/
protected def extend (f : α -> β) : hatα -> β :=
  open scoped Classical in
  if UniformContinuous f then pkg.isDenseInducing.extend f else fun x => f (pkg.dense.some x)

variable {f : α -> β}

/--
theorem `extend_def` / 定理 `extend_def`

English:
theorem extend_def
  given: (hf : UniformContinuous f)
  statement: pkg.extend f = pkg.isDenseInducing.extend f
  proof: if_pos hf

中文:
定理 extend_def
  条件: (hf : UniformContinuous f)
  结论: pkg.extend f = pkg.isDenseInducing.extend f
  证明: if_pos hf

Depends on / 依赖: if_pos
-/
theorem extend_def (hf : UniformContinuous f) : pkg.extend f = pkg.isDenseInducing.extend f :=
  if_pos hf

/--
theorem `inseparable_extend_coe` / 定理 `inseparable_extend_coe`

English:
theorem inseparable_extend_coe
  given: (hf : UniformContinuous f) (x : α)
  proof: by
  rw [extend_def _ hf]
  exact pkg.isDenseInducing.inseparable_extend hf.continuous.continuousAt

中文:
定理 inseparable_extend_coe
  条件: (hf : UniformContinuous f) (x : α)
  证明: by
  rw [extend_def _ hf]
  exact pkg.isDenseInducing.inseparable_extend hf.continuous.continuousAt

Depends on / 依赖: continuous, continuousAt, extend_def, hf.continuous.continuousAt, inseparable_extend, isDenseInducing, pkg.isDenseInducing.inseparable_extend
-/
theorem inseparable_extend_coe (hf : UniformContinuous f) (x : α) :
    Inseparable (pkg.extend f (ι x)) (f x) := by
  rw [extend_def _ hf]
  exact pkg.isDenseInducing.inseparable_extend hf.continuous.continuousAt

/--
theorem `extend_coe` / 定理 `extend_coe`

English:
theorem extend_coe
  given: [T2Space β] (hf : UniformContinuous f) (a : α)
  statement: (pkg.extend f) (ι a) = f a
  proof: by
  rw [pkg.extend_def hf]
  exact pkg.isDenseInducing.extend_eq hf.continuous a

中文:
定理 extend_coe
  条件: [T2Space β] (hf : UniformContinuous f) (a : α)
  结论: (pkg.extend f) (ι a) = f a
  证明: by
  rw [pkg.extend_def hf]
  exact pkg.isDenseInducing.extend_eq hf.continuous a

Depends on / 依赖: continuous, extend_def, extend_eq, hf.continuous, isDenseInducing, pkg.extend_def, pkg.isDenseInducing.extend_eq
-/
theorem extend_coe [T2Space β] (hf : UniformContinuous f) (a : α) : (pkg.extend f) (ι a) = f a := by
  rw [pkg.extend_def hf]
  exact pkg.isDenseInducing.extend_eq hf.continuous a

variable [CompleteSpace β]

@[fun_prop]
/--
theorem `uniformContinuous_extend` / 定理 `uniformContinuous_extend`

English:
theorem uniformContinuous_extend
  statement: UniformContinuous (pkg.extend f)
  proof: by
  by_cases hf : UniformContinuous f
  · rw [pkg.extend_def hf]
    exact uniformContinuous_uniformly_extend pkg.isUniformInducing pkg.dense hf
  · unfold AbstractCompletion.extend
    rw [if_neg hf]
    exact uniformContinuous_of_const fun a b => by congr 1

中文:
定理 uniformContinuous_extend
  结论: UniformContinuous (pkg.extend f)
  证明: by
  by_cases hf : UniformContinuous f
  · rw [pkg.extend_def hf]
    exact uniformContinuous_uniformly_extend pkg.isUniformInducing pkg.dense hf
  · unfold AbstractCompletion.extend
    rw [if_neg hf]
    exact uniformContinuous_of_const fun a b => by congr 1

Depends on / 依赖: AbstractCompletion, AbstractCompletion.extend, UniformContinuous, extend, extend_def, if_neg, isUniformInducing, pkg.dense, pkg.extend_def, pkg.isUniformInducing, uniformContinuous_of_const, uniformContinuous_uniformly_extend
-/
theorem uniformContinuous_extend : UniformContinuous (pkg.extend f) := by
  by_cases hf : UniformContinuous f
  · rw [pkg.extend_def hf]
    exact uniformContinuous_uniformly_extend pkg.isUniformInducing pkg.dense hf
  · unfold AbstractCompletion.extend
    rw [if_neg hf]
    exact uniformContinuous_of_const fun a b => by congr 1

/--
theorem `continuous_extend` / 定理 `continuous_extend`

English:
theorem continuous_extend
  statement: Continuous (pkg.extend f)
  proof: pkg.uniformContinuous_extend.continuous

@[fun_prop]

中文:
定理 continuous_extend
  结论: Continuous (pkg.extend f)
  证明: pkg.uniformContinuous_extend.continuous

@[fun_prop]

Depends on / 依赖: continuous, pkg.uniformContinuous_extend.continuous, uniformContinuous_extend
-/
theorem continuous_extend : Continuous (pkg.extend f) :=
  pkg.uniformContinuous_extend.continuous

@[fun_prop]
/--
lemma `isUniformInducing_extend` / 引理 `isUniformInducing_extend`

English:
lemma isUniformInducing_extend
  given: (h : IsUniformInducing f)
  proof: by
  rw [extend_def _ h.uniformContinuous]
  exact pkg.isDenseInducing.isUniformInducing_extend pkg.isUniformInducing h

中文:
引理 isUniformInducing_extend
  条件: (h : IsUniformInducing f)
  证明: by
  rw [extend_def _ h.uniformContinuous]
  exact pkg.isDenseInducing.isUniformInducing_extend pkg.isUniformInducing h

Depends on / 依赖: extend_def, h.uniformContinuous, isDenseInducing, isUniformInducing, isUniformInducing_extend, pkg.isDenseInducing.isUniformInducing_extend, pkg.isUniformInducing, uniformContinuous
-/
lemma isUniformInducing_extend (h : IsUniformInducing f) :
    IsUniformInducing (pkg.extend f) := by
  rw [extend_def _ h.uniformContinuous]
  exact pkg.isDenseInducing.isUniformInducing_extend pkg.isUniformInducing h

variable [T0Space β]

/--
theorem `extend_unique` / 定理 `extend_unique`

English:
theorem extend_unique
  statement: (hf : UniformContinuous f) {g : hatα -> β} (hg : UniformContinuous g)
  proof: by
  apply pkg.funext pkg.continuous_extend hg.continuous
  simpa only [pkg.extend_coe hf] using h

@[simp]

中文:
定理 extend_unique
  结论: (hf : UniformContinuous f) {g : hatα -> β} (hg : UniformContinuous g)
  证明: by
  apply pkg.funext pkg.continuous_extend hg.continuous
  simpa only [pkg.extend_coe hf] using h

@[simp]

Depends on / 依赖: continuous, continuous_extend, extend_coe, hg.continuous, pkg.continuous_extend, pkg.extend_coe, pkg.funext
-/
theorem extend_unique (hf : UniformContinuous f) {g : hatα -> β} (hg : UniformContinuous g)
    (h : forall a : α, f a = g (ι a)) : pkg.extend f = g := by
  apply pkg.funext pkg.continuous_extend hg.continuous
  simpa only [pkg.extend_coe hf] using h

@[simp]
/--
theorem `extend_comp_coe` / 定理 `extend_comp_coe`

English:
theorem extend_comp_coe
  given: {f : hatα -> β} (hf : UniformContinuous f)
  statement: pkg.extend (f ∘ ι) = f
  proof: funext fun x =>
    pkg.induction_on x (isClosed_eq pkg.continuous_extend hf.continuous) fun y =>
      pkg.extend_coe (hf.comp <| pkg.uniformContinuous_coe) y

中文:
定理 extend_comp_coe
  条件: {f : hatα -> β} (hf : UniformContinuous f)
  结论: pkg.extend (f ∘ ι) = f
  证明: funext fun x =>
    pkg.induction_on x (isClosed_eq pkg.continuous_extend hf.continuous) fun y =>
      pkg.extend_coe (hf.comp <| pkg.uniformContinuous_coe) y

Depends on / 依赖: continuous, continuous_extend, extend_coe, hf.comp, hf.continuous, induction_on, isClosed_eq, pkg.continuous_extend, pkg.extend_coe, pkg.induction_on, pkg.uniformContinuous_coe, uniformContinuous_coe
-/
theorem extend_comp_coe {f : hatα -> β} (hf : UniformContinuous f) : pkg.extend (f ∘ ι) = f :=
  funext fun x =>
    pkg.induction_on x (isClosed_eq pkg.continuous_extend hf.continuous) fun y =>
      pkg.extend_coe (hf.comp <| pkg.uniformContinuous_coe) y

end Extend

section MapSec

variable (pkg' : AbstractCompletion.{vβ} β)

local notation "hatβ" => pkg'.space

local notation "ι'" => pkg'.coe

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : α -> β)
  body: pkg.extend (ι' ∘ f)

local notation "map" => pkg.map pkg'

中文:
定义 map
  签名: (f : α -> β)
  定义体: pkg.extend (ι' ∘ f)

local notation "map" => pkg.map pkg'
-/
protected def map (f : α -> β) : hatα -> hatβ :=
  pkg.extend (ι' ∘ f)

local notation "map" => pkg.map pkg'

variable (f : α -> β)

@[fun_prop]
/--
theorem `uniformContinuous_map` / 定理 `uniformContinuous_map`

English:
theorem uniformContinuous_map
  statement: UniformContinuous (map f)
  proof: pkg.uniformContinuous_extend

@[continuity]

中文:
定理 uniformContinuous_map
  结论: UniformContinuous (map f)
  证明: pkg.uniformContinuous_extend

@[continuity]

Depends on / 依赖: pkg.uniformContinuous_extend, uniformContinuous_extend
-/
theorem uniformContinuous_map : UniformContinuous (map f) :=
  pkg.uniformContinuous_extend

@[continuity]
/--
theorem `continuous_map` / 定理 `continuous_map`

English:
theorem continuous_map
  statement: Continuous (map f)
  proof: pkg.continuous_extend

中文:
定理 continuous_map
  结论: Continuous (map f)
  证明: pkg.continuous_extend

Depends on / 依赖: continuous_extend, pkg.continuous_extend
-/
theorem continuous_map : Continuous (map f) :=
  pkg.continuous_extend

variable {f}

@[simp]
/--
theorem `map_coe` / 定理 `map_coe`

English:
theorem map_coe
  given: (hf : UniformContinuous f) (a : α)
  statement: map f (ι a) = ι' (f a)
  proof: pkg.extend_coe (pkg'.uniformContinuous_coe.comp hf) a

中文:
定理 map_coe
  条件: (hf : UniformContinuous f) (a : α)
  结论: map f (ι a) = ι' (f a)
  证明: pkg.extend_coe (pkg'.uniformContinuous_coe.comp hf) a

Depends on / 依赖: extend_coe, pkg.extend_coe, uniformContinuous_coe, uniformContinuous_coe.comp
-/
theorem map_coe (hf : UniformContinuous f) (a : α) : map f (ι a) = ι' (f a) :=
  pkg.extend_coe (pkg'.uniformContinuous_coe.comp hf) a

/--
theorem `map_unique` / 定理 `map_unique`

English:
theorem map_unique
  statement: {f : α -> β} {g : hatα -> hatβ} (hg : UniformContinuous g)
  proof: pkg.funext (pkg.continuous_map _ _) hg.continuous by
    intro a
    change pkg.extend (ι' ∘ f) _ = _
    simp_rw [Function.comp_def, h, ← comp_apply (f := g)]
    rw [pkg.extend_coe (hg.comp pkg.uniformContinuous_coe)]

@[simp]

中文:
定理 map_unique
  结论: {f : α -> β} {g : hatα -> hatβ} (hg : UniformContinuous g)
  证明: pkg.funext (pkg.continuous_map _ _) hg.continuous by
    intro a
    change pkg.extend (ι' ∘ f) _ = _
    simp_rw [Function.comp_def, h, ← comp_apply (f := g)]
    rw [pkg.extend_coe (hg.comp pkg.uniformContinuous_coe)]

@[simp]

Depends on / 依赖: Function, Function.comp_def, comp_apply, comp_def, continuous, continuous_map, extend, extend_coe, hg.comp, hg.continuous, pkg.continuous_map, pkg.extend, pkg.extend_coe, pkg.funext, pkg.uniformContinuous_coe, simp_rw, uniformContinuous_coe
-/
theorem map_unique {f : α -> β} {g : hatα -> hatβ} (hg : UniformContinuous g)
    (h : forall a, ι' (f a) = g (ι a)) : map f = g :=
pkg.funext (pkg.continuous_map _ _) hg.continuous by
    intro a
    change pkg.extend (ι' ∘ f) _ = _
    simp_rw [Function.comp_def, h, ← comp_apply (f := g)]
    rw [pkg.extend_coe (hg.comp pkg.uniformContinuous_coe)]

@[simp]
/--
theorem `map_id` / 定理 `map_id`

English:
theorem map_id
  statement: pkg.map pkg id = id
  proof: pkg.map_unique pkg uniformContinuous_id fun _ => rfl

中文:
定理 map_id
  结论: pkg.map pkg id = id
  证明: pkg.map_unique pkg uniformContinuous_id fun _ => rfl

Depends on / 依赖: map_unique, pkg.map_unique, uniformContinuous_id
-/
theorem map_id : pkg.map pkg id = id :=
  pkg.map_unique pkg uniformContinuous_id fun _ => rfl

variable {γ : Type uγ} [UniformSpace γ]

/--
theorem `extend_map` / 定理 `extend_map`

English:
theorem extend_map
  statement: [CompleteSpace γ] [T0Space γ] {f : β -> γ} {g : α -> β}
  proof: pkg.funext (pkg'.continuous_extend.comp (pkg.continuous_map pkg' _)) pkg.continuous_extend
    fun a => by
    rw [pkg.extend_coe (hf.comp hg)]; rw [comp_apply]; rw [pkg.map_coe pkg' hg]; rw [pkg'.extend_coe hf]
    rfl

中文:
定理 extend_map
  结论: [CompleteSpace γ] [T0Space γ] {f : β -> γ} {g : α -> β}
  证明: pkg.funext (pkg'.continuous_extend.comp (pkg.continuous_map pkg' _)) pkg.continuous_extend
    fun a => by
    rw [pkg.extend_coe (hf.comp hg)]; rw [comp_apply]; rw [pkg.map_coe pkg' hg]; rw [pkg'.extend_coe hf]
    rfl

Depends on / 依赖: comp_apply, continuous_extend, continuous_extend.comp, continuous_map, extend_coe, hf.comp, map_coe, pkg.continuous_extend, pkg.continuous_map, pkg.extend_coe, pkg.funext, pkg.map_coe
-/
theorem extend_map [CompleteSpace γ] [T0Space γ] {f : β -> γ} {g : α -> β}
    (hf : UniformContinuous f) (hg : UniformContinuous g) :
    pkg'.extend f ∘ map g = pkg.extend (f ∘ g) :=
  pkg.funext (pkg'.continuous_extend.comp (pkg.continuous_map pkg' _)) pkg.continuous_extend
    fun a => by
    rw [pkg.extend_coe (hf.comp hg)]; rw [comp_apply]; rw [pkg.map_coe pkg' hg]; rw [pkg'.extend_coe hf]
    rfl

variable (pkg'' : AbstractCompletion.{vγ} γ)

/--
theorem `map_comp` / 定理 `map_comp`

English:
theorem map_comp
  given: {g : β -> γ} {f : α -> β} (hg : UniformContinuous g) (hf : UniformContinuous f)
  proof: pkg.extend_map pkg' (pkg''.uniformContinuous_coe.comp hg) hf

中文:
定理 map_comp
  条件: {g : β -> γ} {f : α -> β} (hg : UniformContinuous g) (hf : UniformContinuous f)
  证明: pkg.extend_map pkg' (pkg''.uniformContinuous_coe.comp hg) hf

Depends on / 依赖: extend_map, pkg.extend_map, uniformContinuous_coe, uniformContinuous_coe.comp
-/
theorem map_comp {g : β -> γ} {f : α -> β} (hg : UniformContinuous g) (hf : UniformContinuous f) :
    pkg'.map pkg'' g ∘ pkg.map pkg' f = pkg.map pkg'' (g ∘ f) :=
  pkg.extend_map pkg' (pkg''.uniformContinuous_coe.comp hg) hf

/--
Definition of `mapEquiv` / `mapEquiv` 的定义

English:
definition mapEquiv
  signature: (e : α ≃ᵤ β)
  body: pkg.map pkg' e
  invFun := pkg'.map pkg e.symm
  uniformContinuous_toFun := uniformContinuous_map ..
  uniformContinuous_invFun := uniformContinuous_map ..
left_inv := Function.leftInverse_iff_comp.2 by
    simp [map_comp _ _ _ e.symm.uniformContinuous e.uniformContinuous]
right_inv := Function.righ

中文:
定义 mapEquiv
  签名: (e : α ≃ᵤ β)
  定义体: pkg.map pkg' e
  invFun := pkg'.map pkg e.symm
  uniformContinuous_toFun := uniformContinuous_map ..
  uniformContinuous_invFun := uniformContinuous_map ..
left_inv := Function.leftInverse_iff_comp.2 by
    simp [map_comp _ _ _ e.symm.uniformContinuous e.uniformContinuous]
right_inv := Function.righ

Depends on / 依赖: pkg.map
-/
def mapEquiv (e : α ≃ᵤ β) : hatα ≃ᵤ hatβ where
  toFun := pkg.map pkg' e
  invFun := pkg'.map pkg e.symm
  uniformContinuous_toFun := uniformContinuous_map ..
  uniformContinuous_invFun := uniformContinuous_map ..
left_inv := Function.leftInverse_iff_comp.2 by
    simp [map_comp _ _ _ e.symm.uniformContinuous e.uniformContinuous]
right_inv := Function.rightInverse_iff_comp.2 by
    simp [map_comp _ _ _ e.uniformContinuous e.symm.uniformContinuous]

@[simp]
/--
theorem `mapEquiv_symm` / 定理 `mapEquiv_symm`

English:
theorem mapEquiv_symm
  given: (e : α ≃ᵤ β)
  proof: rfl

@[simp]

中文:
定理 mapEquiv_symm
  条件: (e : α ≃ᵤ β)
  证明: rfl

@[simp]
-/
theorem mapEquiv_symm (e : α ≃ᵤ β) :
    (pkg.mapEquiv pkg' e).symm = pkg'.mapEquiv pkg e.symm := rfl

@[simp]
/--
theorem `mapEquiv_coe` / 定理 `mapEquiv_coe`

English:
theorem mapEquiv_coe
  given: (e : α ≃ᵤ β) (a : α)
  statement: pkg.mapEquiv pkg' e (ι a) = ι' (e a)
  proof: pkg.map_coe pkg' e.uniformContinuous _

中文:
定理 mapEquiv_coe
  条件: (e : α ≃ᵤ β) (a : α)
  结论: pkg.mapEquiv pkg' e (ι a) = ι' (e a)
  证明: pkg.map_coe pkg' e.uniformContinuous _

Depends on / 依赖: e.uniformContinuous, map_coe, pkg.map_coe, uniformContinuous
-/
theorem mapEquiv_coe (e : α ≃ᵤ β) (a : α) : pkg.mapEquiv pkg' e (ι a) = ι' (e a) :=
  pkg.map_coe pkg' e.uniformContinuous _

end MapSec

section Compare

-- We can now compare two completion packages for the same uniform space
variable (pkg' : AbstractCompletion.{vα'} α)

/--
Definition of `compare` / `compare` 的定义

English:
definition compare
  signature: : pkg.space -> pkg'.space
  body: pkg.extend pkg'.coe

@[fun_prop]

中文:
定义 compare
  签名: : pkg.space -> pkg'.space
  定义体: pkg.extend pkg'.coe

@[fun_prop]

Depends on / 依赖: extend, pkg.extend
-/
def compare : pkg.space -> pkg'.space :=
  pkg.extend pkg'.coe

@[fun_prop]
/--
theorem `uniformContinuous_compare` / 定理 `uniformContinuous_compare`

English:
theorem uniformContinuous_compare
  statement: UniformContinuous (pkg.compare pkg')
  proof: pkg.uniformContinuous_extend

中文:
定理 uniformContinuous_compare
  结论: UniformContinuous (pkg.compare pkg')
  证明: pkg.uniformContinuous_extend

Depends on / 依赖: pkg.uniformContinuous_extend, uniformContinuous_extend
-/
theorem uniformContinuous_compare : UniformContinuous (pkg.compare pkg') :=
  pkg.uniformContinuous_extend

/--
theorem `compare_coe` / 定理 `compare_coe`

English:
theorem compare_coe
  given: (a : α)
  statement: pkg.compare pkg' (pkg.coe a) = pkg'.coe a
  proof: pkg.extend_coe pkg'.uniformContinuous_coe a

中文:
定理 compare_coe
  条件: (a : α)
  结论: pkg.compare pkg' (pkg.coe a) = pkg'.coe a
  证明: pkg.extend_coe pkg'.uniformContinuous_coe a

Depends on / 依赖: extend_coe, pkg.extend_coe, uniformContinuous_coe
-/
theorem compare_coe (a : α) : pkg.compare pkg' (pkg.coe a) = pkg'.coe a :=
  pkg.extend_coe pkg'.uniformContinuous_coe a

/--
theorem `inverse_compare` / 定理 `inverse_compare`

English:
theorem inverse_compare
  statement: pkg.compare pkg' ∘ pkg'.compare pkg = id
  proof: by
  have uc := pkg.uniformContinuous_compare pkg'
  have uc' := pkg'.uniformContinuous_compare pkg
  apply pkg'.funext (uc.comp uc').continuous continuous_id
  intro a
  rw [comp_apply]; rw [pkg'.compare_coe pkg]; rw [pkg.compare_coe pkg']
  rfl

中文:
定理 inverse_compare
  结论: pkg.compare pkg' ∘ pkg'.compare pkg = id
  证明: by
  have uc := pkg.uniformContinuous_compare pkg'
  have uc' := pkg'.uniformContinuous_compare pkg
  apply pkg'.funext (uc.comp uc').continuous continuous_id
  intro a
  rw [comp_apply]; rw [pkg'.compare_coe pkg]; rw [pkg.compare_coe pkg']
  rfl

Depends on / 依赖: comp_apply, compare_coe, continuous, continuous_id, pkg.compare_coe, pkg.uniformContinuous_compare, uc.comp, uniformContinuous_compare
-/
theorem inverse_compare : pkg.compare pkg' ∘ pkg'.compare pkg = id := by
  have uc := pkg.uniformContinuous_compare pkg'
  have uc' := pkg'.uniformContinuous_compare pkg
  apply pkg'.funext (uc.comp uc').continuous continuous_id
  intro a
  rw [comp_apply]; rw [pkg'.compare_coe pkg]; rw [pkg.compare_coe pkg']
  rfl

/--
Definition of `compareEquiv` / `compareEquiv` 的定义

English:
definition compareEquiv
  signature: : pkg.space ≃ᵤ pkg'.space where
  body: pkg.compare pkg'
  invFun := pkg'.compare pkg
  left_inv := congr_fun (pkg'.inverse_compare pkg)
  right_inv := congr_fun (pkg.inverse_compare pkg')
  uniformContinuous_toFun := uniformContinuous_compare _ _
  uniformContinuous_invFun := uniformContinuous_compare _ _

@[fun_prop]

中文:
定义 compareEquiv
  签名: : pkg.space ≃ᵤ pkg'.space where
  定义体: pkg.compare pkg'
  invFun := pkg'.compare pkg
  left_inv := congr_fun (pkg'.inverse_compare pkg)
  right_inv := congr_fun (pkg.inverse_compare pkg')
  uniformContinuous_toFun := uniformContinuous_compare _ _
  uniformContinuous_invFun := uniformContinuous_compare _ _

@[fun_prop]

Depends on / 依赖: compare, pkg.compare
-/
def compareEquiv : pkg.space ≃ᵤ pkg'.space where
  toFun := pkg.compare pkg'
  invFun := pkg'.compare pkg
  left_inv := congr_fun (pkg'.inverse_compare pkg)
  right_inv := congr_fun (pkg.inverse_compare pkg')
  uniformContinuous_toFun := uniformContinuous_compare _ _
  uniformContinuous_invFun := uniformContinuous_compare _ _

@[fun_prop]
/--
theorem `uniformContinuous_compareEquiv` / 定理 `uniformContinuous_compareEquiv`

English:
theorem uniformContinuous_compareEquiv
  statement: UniformContinuous (pkg.compareEquiv pkg')
  proof: pkg.uniformContinuous_compare pkg'

@[fun_prop]

中文:
定理 uniformContinuous_compareEquiv
  结论: UniformContinuous (pkg.compareEquiv pkg')
  证明: pkg.uniformContinuous_compare pkg'

@[fun_prop]

Depends on / 依赖: pkg.uniformContinuous_compare, uniformContinuous_compare
-/
theorem uniformContinuous_compareEquiv : UniformContinuous (pkg.compareEquiv pkg') :=
  pkg.uniformContinuous_compare pkg'

@[fun_prop]
/--
theorem `uniformContinuous_compareEquiv_symm` / 定理 `uniformContinuous_compareEquiv_symm`

English:
theorem uniformContinuous_compareEquiv_symm
  statement: UniformContinuous (pkg.compareEquiv pkg').symm
  proof: pkg'.uniformContinuous_compare pkg

中文:
定理 uniformContinuous_compareEquiv_symm
  结论: UniformContinuous (pkg.compareEquiv pkg').symm
  证明: pkg'.uniformContinuous_compare pkg

Depends on / 依赖: uniformContinuous_compare
-/
theorem uniformContinuous_compareEquiv_symm : UniformContinuous (pkg.compareEquiv pkg').symm :=
  pkg'.uniformContinuous_compare pkg


open scoped Topology

/--
theorem `compare_comp_eq_compare` / 定理 `compare_comp_eq_compare`

English:
theorem compare_comp_eq_compare
  statement: (γ : Type uγ) [TopologicalSpace γ]
  proof: pkg.uniformStruct.toTopologicalSpace
    letI := pkg'.uniformStruct.toTopologicalSpace
    (forall a : pkg.space,
      Filter.Tendsto f (Filter.comap pkg.coe (𝓝 a)) (𝓝 ((pkg.isDenseInducing.extend f) a))) ->
      pkg.isDenseInducing.extend f ∘ pkg'.compare pkg = pkg'.isDenseInducing.extend f := by

中文:
定理 compare_comp_eq_compare
  结论: (γ : 类型uγ) [TopologicalSpace γ]
  证明: pkg.uniformStruct.toTopologicalSpace
    letI := pkg'.uniformStruct.toTopologicalSpace
    (forall a : pkg.space,
      Filter.Tendsto f (Filter.comap pkg.coe (𝓝 a)) (𝓝 ((pkg.isDenseInducing.extend f) a))) ->
      pkg.isDenseInducing.extend f ∘ pkg'.compare pkg = pkg'.isDenseInducing.extend f := by

Depends on / 依赖: pkg.uniformStruct.toTopologicalSpace, toTopologicalSpace, uniformStruct
-/
theorem compare_comp_eq_compare (γ : Type uγ) [TopologicalSpace γ]
    [T3Space γ] {f : α -> γ} (cont_f : Continuous f) :
    letI := pkg.uniformStruct.toTopologicalSpace
    letI := pkg'.uniformStruct.toTopologicalSpace
    (forall a : pkg.space,
      Filter.Tendsto f (Filter.comap pkg.coe (𝓝 a)) (𝓝 ((pkg.isDenseInducing.extend f) a))) ->
      pkg.isDenseInducing.extend f ∘ pkg'.compare pkg = pkg'.isDenseInducing.extend f := by
  intro h
  have (x : α) : (pkg.isDenseInducing.extend f ∘ pkg'.compare pkg) (pkg'.coe x) = f x := by
    simp only [Function.comp_apply, compare_coe, IsDenseInducing.extend_eq _ cont_f]
  apply (IsDenseInducing.extend_unique (AbstractCompletion.isDenseInducing _) this
    (Continuous.comp _ (uniformContinuous_compare pkg' pkg).continuous)).symm
  apply IsDenseInducing.continuous_extend
  exact fun a => ⟨(pkg.isDenseInducing.extend f) a, h a⟩

end Compare

section Prod

variable (pkg' : AbstractCompletion.{vβ} β)

local notation "hatβ" => pkg'.space

local notation "ι'" => pkg'.coe

/--
Definition of `prod` / `prod` 的定义

English:
definition prod
  signature: : AbstractCompletion (α × β) where
  body: hatα × hatβ
  coe p := ⟨ι p.1, ι' p.2⟩
  uniformStruct := inferInstance
  complete := inferInstance
  separation := inferInstance
  isUniformInducing := IsUniformInducing.prod pkg.isUniformInducing pkg'.isUniformInducing
  dense := pkg.dense.prodMap pkg'.dense

中文:
定义 prod
  签名: : AbstractCompletion (α × β) where
  定义体: hatα × hatβ
  coe p := ⟨ι p.1, ι' p.2⟩
  uniformStruct := inferInstance
  complete := inferInstance
  separation := inferInstance
  isUniformInducing := IsUniformInducing.prod pkg.isUniformInducing pkg'.isUniformInducing
  dense := pkg.dense.prodMap pkg'.dense
-/
protected def prod : AbstractCompletion (α × β) where
  space := hatα × hatβ
  coe p := ⟨ι p.1, ι' p.2⟩
  uniformStruct := inferInstance
  complete := inferInstance
  separation := inferInstance
  isUniformInducing := IsUniformInducing.prod pkg.isUniformInducing pkg'.isUniformInducing
  dense := pkg.dense.prodMap pkg'.dense

end Prod

section Extension₂

variable (pkg' : AbstractCompletion.{vβ} β)

local notation "hatβ" => pkg'.space

local notation "ι'" => pkg'.coe

variable {γ : Type uγ} [UniformSpace γ]

open Function

/--
Definition of `extend₂` / `extend₂` 的定义

English:
definition extend₂
  signature: (f : α -> β -> γ)
  body: curry (pkg.prod pkg').extend (uncurry f)

中文:
定义 extend₂
  签名: (f : α -> β -> γ)
  定义体: curry (pkg.prod pkg').extend (uncurry f)
-/
protected def extend₂ (f : α -> β -> γ) : hatα -> hatβ -> γ :=
curry (pkg.prod pkg').extend (uncurry f)

section T0Space

variable [T0Space γ] {f : α -> β -> γ}

/--
theorem `extension₂_coe_coe` / 定理 `extension₂_coe_coe`

English:
theorem extension₂_coe_coe
  given: (hf : UniformContinuous <| uncurry f) (a : α) (b : β)
  proof: show (pkg.prod pkg').extend (uncurry f) ((pkg.prod pkg').coe (a, b)) = uncurry f (a, b) from
    (pkg.prod pkg').extend_coe hf _

中文:
定理 extension₂_coe_coe
  条件: (hf : UniformContinuous <| uncurry f) (a : α) (b : β)
  证明: show (pkg.prod pkg').extend (uncurry f) ((pkg.prod pkg').coe (a, b)) = uncurry f (a, b) from
    (pkg.prod pkg').extend_coe hf _

Depends on / 依赖: extend, extend_coe, pkg.prod, uncurry
-/
theorem extension₂_coe_coe (hf : UniformContinuous <| uncurry f) (a : α) (b : β) :
    pkg.extend₂ pkg' f (ι a) (ι' b) = f a b :=
  show (pkg.prod pkg').extend (uncurry f) ((pkg.prod pkg').coe (a, b)) = uncurry f (a, b) from
    (pkg.prod pkg').extend_coe hf _

end T0Space

variable {f : α -> β -> γ}
variable [CompleteSpace γ] (f)

set_option backward.isDefEq.respectTransparency false in
@[fun_prop]
/--
theorem `uniformContinuous_extension₂` / 定理 `uniformContinuous_extension₂`

English:
theorem uniformContinuous_extension₂
  statement: UniformContinuous₂ (pkg.extend₂ pkg' f)
  proof: by
  rw [uniformContinuous₂_def]; rw [AbstractCompletion.extend₂]; rw [uncurry_curry]
  apply uniformContinuous_extend

中文:
定理 uniformContinuous_extension₂
  结论: UniformContinuous₂ (pkg.extend₂ pkg' f)
  证明: by
  rw [uniformContinuous₂_def]; rw [AbstractCompletion.extend₂]; rw [uncurry_curry]
  apply uniformContinuous_extend

Depends on / 依赖: AbstractCompletion, AbstractCompletion.extend, uncurry_curry, uniformContinuous_extend
-/
theorem uniformContinuous_extension₂ : UniformContinuous₂ (pkg.extend₂ pkg' f) := by
  rw [uniformContinuous₂_def]; rw [AbstractCompletion.extend₂]; rw [uncurry_curry]
  apply uniformContinuous_extend

end Extension₂

section Map₂

variable (pkg' : AbstractCompletion β)

local notation "hatβ" => pkg'.space

local notation "ι'" => pkg'.coe

variable {γ : Type uγ} [UniformSpace γ] (pkg'' : AbstractCompletion.{vγ} γ)

local notation "hatγ" => pkg''.space

local notation "ι''" => pkg''.coe

local notation f " ∘₂ " g => bicompr f g

/--
Definition of `map₂` / `map₂` 的定义

English:
definition map₂
  signature: (f : α -> β -> γ)
  body: pkg.extend₂ pkg' (pkg''.coe ∘₂ f)

@[fun_prop]

中文:
定义 map₂
  签名: (f : α -> β -> γ)
  定义体: pkg.extend₂ pkg' (pkg''.coe ∘₂ f)

@[fun_prop]
-/
protected def map₂ (f : α -> β -> γ) : hatα -> hatβ -> hatγ :=
  pkg.extend₂ pkg' (pkg''.coe ∘₂ f)

@[fun_prop]
/--
theorem `uniformContinuous_map₂` / 定理 `uniformContinuous_map₂`

English:
theorem uniformContinuous_map₂
  given: (f : α -> β -> γ)
  statement: UniformContinuous₂ (pkg.map₂ pkg' pkg'' f)
  proof: AbstractCompletion.uniformContinuous_extension₂ pkg pkg' _

中文:
定理 uniformContinuous_map₂
  条件: (f : α -> β -> γ)
  结论: UniformContinuous₂ (pkg.map₂ pkg' pkg'' f)
  证明: AbstractCompletion.uniformContinuous_extension₂ pkg pkg' _

Depends on / 依赖: AbstractCompletion, AbstractCompletion.uniformContinuous_extension
-/
theorem uniformContinuous_map₂ (f : α -> β -> γ) : UniformContinuous₂ (pkg.map₂ pkg' pkg'' f) :=
  AbstractCompletion.uniformContinuous_extension₂ pkg pkg' _

/--
theorem `continuous_map₂` / 定理 `continuous_map₂`

English:
theorem continuous_map₂
  statement: {δ} [TopologicalSpace δ] {f : α -> β -> γ} {a : δ -> hatα} {b : δ -> hatβ}
  proof: (pkg.uniformContinuous_map₂ pkg' pkg'' f).continuous.comp₂ ha hb

中文:
定理 continuous_map₂
  结论: {δ} [TopologicalSpace δ] {f : α -> β -> γ} {a : δ -> hatα} {b : δ -> hatβ}
  证明: (pkg.uniformContinuous_map₂ pkg' pkg'' f).continuous.comp₂ ha hb

Depends on / 依赖: continuous, continuous.comp, pkg.uniformContinuous_map
-/
theorem continuous_map₂ {δ} [TopologicalSpace δ] {f : α -> β -> γ} {a : δ -> hatα} {b : δ -> hatβ}
    (ha : Continuous a) (hb : Continuous b) :
    Continuous fun d : δ => pkg.map₂ pkg' pkg'' f (a d) (b d) :=
  (pkg.uniformContinuous_map₂ pkg' pkg'' f).continuous.comp₂ ha hb

/--
theorem `map₂_coe_coe` / 定理 `map₂_coe_coe`

English:
theorem map₂_coe_coe
  given: (a : α) (b : β) (f : α -> β -> γ) (hf : UniformContinuous₂ f)
  proof: pkg.extension₂_coe_coe (f := pkg''.coe ∘₂ f) pkg' (pkg''.uniformContinuous_coe.comp hf) a b

中文:
定理 map₂_coe_coe
  条件: (a : α) (b : β) (f : α -> β -> γ) (hf : UniformContinuous₂ f)
  证明: pkg.extension₂_coe_coe (f := pkg''.coe ∘₂ f) pkg' (pkg''.uniformContinuous_coe.comp hf) a b

Depends on / 依赖: pkg.extension, uniformContinuous_coe, uniformContinuous_coe.comp
-/
theorem map₂_coe_coe (a : α) (b : β) (f : α -> β -> γ) (hf : UniformContinuous₂ f) :
    pkg.map₂ pkg' pkg'' f (ι a) (ι' b) = ι'' (f a b) :=
  pkg.extension₂_coe_coe (f := pkg''.coe ∘₂ f) pkg' (pkg''.uniformContinuous_coe.comp hf) a b

end Map₂

end AbstractCompletion
