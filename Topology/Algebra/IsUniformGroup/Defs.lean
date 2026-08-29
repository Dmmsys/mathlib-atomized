/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl, Anatole Dedecker
-/
module

public import Mathlib.Topology.UniformSpace.Basic
public import Mathlib.Topology.Algebra.Group.Basic

/-!
# Uniform structure on topological groups

Given a topological group `G`, one can naturally build two uniform structures
(the "left" and "right" ones) on `G` inducing its topology.
This file defines typeclasses for groups equipped with either of these uniform structures, as well
as a separate typeclass for the (very common) case where the given uniform structure
coincides with **both** the left and right uniform structures.

## Main declarations

* `IsRightUniformGroup` and `IsRightUniformAddGroup`: Multiplicative and additive topological groups
  endowed with the associated right uniform structure. This means that two points `x` and `y`
  are close precisely when `y * x⁻¹` is close to `1` / `y + (-x)` close to `0`.
* `IsLeftUniformGroup` and `IsLeftUniformAddGroup`: Multiplicative and additive topological groups
  endowed with the associated left uniform structure. This means that two points `x` and `y`
  are close precisely when `x⁻¹ * y` is close to `1` / `(-x) + y` close to `0`.
* `IsUniformGroup` and `IsUniformAddGroup`: Multiplicative and additive uniform groups,
  i.e., groups with uniformly continuous `(*)` and `(⁻¹)` / `(+)` and `(-)`. This corresponds
  to the conjunction of the two conditions above, although this result is not in Mathlib yet.

## Main results

* `IsTopologicalAddGroup.rightUniformSpace` and `comm_topologicalAddGroup_is_uniform` can be used
  to construct a canonical uniformity for a topological additive group.

See `Mathlib/Topology/Algebra/IsUniformGroup/Basic.lean` for further results.

## Implementation Notes

Since the most frequent use case is `G` being a commutative additive groups, `Mathlib` originally
did essentially all the theory under the assumption `IsUniformGroup G`.
For this reason, you may find results stated under this assumption even though they may hold
under either `IsRightUniformGroup G` or `IsLeftUniformGroup G`.
-/

@[expose] public section

assert_not_exists Cauchy

noncomputable section

open Uniformity Topology Filter Pointwise

section LeftRight

open Filter Set

variable {G Gₗ Gᵣ Hₗ Hᵣ X : Type*}

/--
Definition of `IsRightUniformAddGroup` / `IsRightUniformAddGroup` 的定义

English:
class IsRightUniformAddGroup
  parameters: (G : Type*) [UniformSpace G] [AddGroup G]
  extends: IsTopologicalAddGroup G
  axioms and operations (1):
    - uniformity_eq : 𝓤 G = comap (fun x : G × G => x.2 + (-x.1)) (𝓝 0)

中文:
类 是RightUniformAdd群
  参数: (G : 类型) [一致空间 G] [加法群 G]
  继承: 是拓扑加群 G
  公理与运算 (1 个):
    - uniformity_eq : 𝓤 G = comap (fun x : G × G => x.2 + (-x.1)) (𝓝 0)
-/
class IsRightUniformAddGroup (G : Type*) [UniformSpace G] [AddGroup G] : Prop
    extends IsTopologicalAddGroup G where
  uniformity_eq :
    𝓤 G = comap (fun x : G × G => x.2 + (-x.1)) (𝓝 0)

/-- A **right-uniform group** is a topological group endowed with the associated
right uniform structure: the uniformity filter `𝓤 G` is the inverse image of `𝓝 1` by the map
`(x, y) ↦ y * x⁻¹`.

In other words, we declare that two points `x` and `y` are infinitely close
precisely when `y * x⁻¹` is infinitely close to `1`. -/
@[to_additive]
/--
Definition of `IsRightUniformGroup` / `IsRightUniformGroup` 的定义

English:
class IsRightUniformGroup
  parameters: (G : Type*) [UniformSpace G] [Group G]
  extends: IsTopologicalGroup G
  axioms and operations (1):
    - uniformity_eq : 𝓤 G = comap (fun x : G × G => x.2 * x.1⁻¹) (𝓝 1)

中文:
类 是RightUniform群
  参数: (G : 类型) [一致空间 G] [群 G]
  继承: 是拓扑群 G
  公理与运算 (1 个):
    - uniformity_eq : 𝓤 G = comap (fun x : G × G => x.2 * x.1⁻¹) (𝓝 1)
-/
class IsRightUniformGroup (G : Type*) [UniformSpace G] [Group G] : Prop
    extends IsTopologicalGroup G where
  uniformity_eq :
    𝓤 G = comap (fun x : G × G => x.2 * x.1⁻¹) (𝓝 1)

/--
Definition of `IsLeftUniformAddGroup` / `IsLeftUniformAddGroup` 的定义

English:
class IsLeftUniformAddGroup
  parameters: (G : Type*) [UniformSpace G] [AddGroup G]
  extends: IsTopologicalAddGroup G
  axioms and operations (1):
    - uniformity_eq : 𝓤 G = comap (fun x : G × G => (-x.1) + x.2) (𝓝 0)

中文:
类 是LeftUniformAdd群
  参数: (G : 类型) [一致空间 G] [加法群 G]
  继承: 是拓扑加群 G
  公理与运算 (1 个):
    - uniformity_eq : 𝓤 G = comap (fun x : G × G => (-x.1) + x.2) (𝓝 0)
-/
class IsLeftUniformAddGroup (G : Type*) [UniformSpace G] [AddGroup G] : Prop
    extends IsTopologicalAddGroup G where
  uniformity_eq :
    𝓤 G = comap (fun x : G × G => (-x.1) + x.2) (𝓝 0)

/-- A **left-uniform group** is a topological group endowed with the associated
left uniform structure: the uniformity filter `𝓤 G` is the inverse image of `𝓝 1` by the map
`(x, y) ↦ x⁻¹ * y`.

In other words, we declare that two points `x` and `y` are infinitely close
precisely when `x⁻¹ * y` is infinitely close to `1`. -/
@[to_additive]
/--
Definition of `IsLeftUniformGroup` / `IsLeftUniformGroup` 的定义

English:
class IsLeftUniformGroup
  parameters: (G : Type*) [UniformSpace G] [Group G]
  extends: IsTopologicalGroup G
  axioms and operations (1):
    - uniformity_eq : 𝓤 G = comap (fun x : G × G => x.1⁻¹ * x.2) (𝓝 1)

中文:
类 是LeftUniform群
  参数: (G : 类型) [一致空间 G] [群 G]
  继承: 是拓扑群 G
  公理与运算 (1 个):
    - uniformity_eq : 𝓤 G = comap (fun x : G × G => x.1⁻¹ * x.2) (𝓝 1)
-/
class IsLeftUniformGroup (G : Type*) [UniformSpace G] [Group G] : Prop
    extends IsTopologicalGroup G where
  uniformity_eq :
    𝓤 G = comap (fun x : G × G => x.1⁻¹ * x.2) (𝓝 1)

attribute [instance 10] IsRightUniformAddGroup.toIsTopologicalAddGroup
attribute [instance 10] IsRightUniformGroup.toIsTopologicalGroup
attribute [instance 10] IsLeftUniformAddGroup.toIsTopologicalAddGroup
attribute [instance 10] IsLeftUniformGroup.toIsTopologicalGroup

variable [UniformSpace Gₗ] [UniformSpace Gᵣ] [Group Gₗ] [Group Gᵣ]
variable [UniformSpace Hₗ] [UniformSpace Hᵣ] [Group Hₗ] [Group Hᵣ]
variable [IsLeftUniformGroup Gₗ] [IsRightUniformGroup Gᵣ]
variable [IsLeftUniformGroup Hₗ] [IsRightUniformGroup Hᵣ]
variable [UniformSpace X]

variable (Gₗ Gᵣ)

@[to_additive]
/--
lemma `uniformity_eq_comap_mul_inv_nhds_one` / 引理 `uniformity_eq_comap_mul_inv_nhds_one`

English:
lemma uniformity_eq_comap_mul_inv_nhds_one
  proof: IsRightUniformGroup.uniformity_eq

@[to_additive]

中文:
引理 uniformity_eq_comap_mul_inv_nhds_one
  证明: IsRightUniformGroup.uniformity_eq

@[to_additive]

Depends on / 依赖: IsRightUniformGroup, IsRightUniformGroup.uniformity_eq, uniformity_eq
-/
lemma uniformity_eq_comap_mul_inv_nhds_one :
    𝓤 Gᵣ = comap (fun x : Gᵣ × Gᵣ => x.2 * x.1⁻¹) (𝓝 1) :=
  IsRightUniformGroup.uniformity_eq

@[to_additive]
/--
lemma `uniformity_eq_comap_inv_mul_nhds_one` / 引理 `uniformity_eq_comap_inv_mul_nhds_one`

English:
lemma uniformity_eq_comap_inv_mul_nhds_one
  proof: IsLeftUniformGroup.uniformity_eq

@[to_additive]

中文:
引理 uniformity_eq_comap_inv_mul_nhds_one
  证明: IsLeftUniformGroup.uniformity_eq

@[to_additive]

Depends on / 依赖: IsLeftUniformGroup, IsLeftUniformGroup.uniformity_eq, uniformity_eq
-/
lemma uniformity_eq_comap_inv_mul_nhds_one :
    𝓤 Gₗ = comap (fun x : Gₗ × Gₗ => x.1⁻¹ * x.2) (𝓝 1) :=
  IsLeftUniformGroup.uniformity_eq

@[to_additive]
/--
lemma `uniformity_eq_comap_mul_inv_nhds_one_swapped` / 引理 `uniformity_eq_comap_mul_inv_nhds_one_swapped`

English:
lemma uniformity_eq_comap_mul_inv_nhds_one_swapped
  proof: by
  rw [← comap_swap_uniformity]; rw [uniformity_eq_comap_mul_inv_nhds_one]; rw [comap_comap]; rw [Function.comp_def]
  simp

@[to_additive]

中文:
引理 uniformity_eq_comap_mul_inv_nhds_one_swapped
  证明: by
  rw [← comap_swap_uniformity]; rw [uniformity_eq_comap_mul_inv_nhds_one]; rw [comap_comap]; rw [Function.comp_def]
  simp

@[to_additive]

Depends on / 依赖: Function, Function.comp_def, comap_comap, comap_swap_uniformity, comp_def, uniformity_eq_comap_mul_inv_nhds_one
-/
lemma uniformity_eq_comap_mul_inv_nhds_one_swapped :
    𝓤 Gᵣ = comap (fun x : Gᵣ × Gᵣ => x.1 * x.2⁻¹) (𝓝 1) := by
  rw [← comap_swap_uniformity]; rw [uniformity_eq_comap_mul_inv_nhds_one]; rw [comap_comap]; rw [Function.comp_def]
  simp

@[to_additive]
/--
lemma `uniformity_eq_comap_inv_mul_nhds_one_swapped` / 引理 `uniformity_eq_comap_inv_mul_nhds_one_swapped`

English:
lemma uniformity_eq_comap_inv_mul_nhds_one_swapped
  proof: by
  rw [← comap_swap_uniformity]; rw [uniformity_eq_comap_inv_mul_nhds_one]; rw [comap_comap]; rw [Function.comp_def]
  simp

@[to_additive]

中文:
引理 uniformity_eq_comap_inv_mul_nhds_one_swapped
  证明: by
  rw [← comap_swap_uniformity]; rw [uniformity_eq_comap_inv_mul_nhds_one]; rw [comap_comap]; rw [Function.comp_def]
  simp

@[to_additive]

Depends on / 依赖: Function, Function.comp_def, comap_comap, comap_swap_uniformity, comp_def, uniformity_eq_comap_inv_mul_nhds_one
-/
lemma uniformity_eq_comap_inv_mul_nhds_one_swapped :
    𝓤 Gₗ = comap (fun x : Gₗ × Gₗ => x.2⁻¹ * x.1) (𝓝 1) := by
  rw [← comap_swap_uniformity]; rw [uniformity_eq_comap_inv_mul_nhds_one]; rw [comap_comap]; rw [Function.comp_def]
  simp

@[to_additive]
/--
theorem `uniformity_eq_comap_nhds_one` / 定理 `uniformity_eq_comap_nhds_one`

English:
theorem uniformity_eq_comap_nhds_one
  statement: 𝓤 Gᵣ = comap (fun x : Gᵣ × Gᵣ => x.2 / x.1) (𝓝 1)
  proof: by
  simp_rw [div_eq_mul_inv]
  exact uniformity_eq_comap_mul_inv_nhds_one Gᵣ

@[to_additive]

中文:
定理 uniformity_eq_comap_nhds_one
  结论: 𝓤 Gᵣ = comap (fun x : Gᵣ × Gᵣ => x.2 / x.1) (𝓝 1)
  证明: by
  simp_rw [div_eq_mul_inv]
  exact uniformity_eq_comap_mul_inv_nhds_one Gᵣ

@[to_additive]

Depends on / 依赖: div_eq_mul_inv, simp_rw, uniformity_eq_comap_mul_inv_nhds_one
-/
theorem uniformity_eq_comap_nhds_one : 𝓤 Gᵣ = comap (fun x : Gᵣ × Gᵣ => x.2 / x.1) (𝓝 1) := by
  simp_rw [div_eq_mul_inv]
  exact uniformity_eq_comap_mul_inv_nhds_one Gᵣ

@[to_additive]
/--
theorem `uniformity_eq_comap_nhds_one_swapped` / 定理 `uniformity_eq_comap_nhds_one_swapped`

English:
theorem uniformity_eq_comap_nhds_one_swapped
  proof: by
  rw [← comap_swap_uniformity]; rw [uniformity_eq_comap_nhds_one]; rw [comap_comap]; rw [Function.comp_def]
  simp

中文:
定理 uniformity_eq_comap_nhds_one_swapped
  证明: by
  rw [← comap_swap_uniformity]; rw [uniformity_eq_comap_nhds_one]; rw [comap_comap]; rw [Function.comp_def]
  simp

Depends on / 依赖: Function, Function.comp_def, comap_comap, comap_swap_uniformity, comp_def, uniformity_eq_comap_nhds_one
-/
theorem uniformity_eq_comap_nhds_one_swapped :
    𝓤 Gᵣ = comap (fun x : Gᵣ × Gᵣ => x.1 / x.2) (𝓝 1) := by
  rw [← comap_swap_uniformity]; rw [uniformity_eq_comap_nhds_one]; rw [comap_comap]; rw [Function.comp_def]
  simp

end LeftRight

section IsUniformGroup

open Filter Set

variable {α : Type*} {β : Type*}

/--
Definition of `IsUniformGroup` / `IsUniformGroup` 的定义

English:
class IsUniformGroup
  parameters: (α : Type*) [UniformSpace α] [Group α]
  axioms and operations (1):
    - uniformContinuous_div : UniformContinuous fun p : α × α => p.1 / p.2

中文:
类 是一致群
  参数: (α : 类型) [一致空间 α] [群 α]
  公理与运算 (1 个):
    - uniformContinuous_div : 一致连续 fun p : α × α => p.1 / p.2
-/
class IsUniformGroup (α : Type*) [UniformSpace α] [Group α] : Prop where
  uniformContinuous_div : UniformContinuous fun p : α × α => p.1 / p.2

/--
Definition of `IsUniformAddGroup` / `IsUniformAddGroup` 的定义

English:
class IsUniformAddGroup
  parameters: (α : Type*) [UniformSpace α] [AddGroup α]
  axioms and operations (1):
    - uniformContinuous_sub : UniformContinuous fun p : α × α => p.1 - p.2

中文:
类 是UniformAdd群
  参数: (α : 类型) [一致空间 α] [加法群 α]
  公理与运算 (1 个):
    - uniformContinuous_sub : 一致连续 fun p : α × α => p.1 - p.2
-/
class IsUniformAddGroup (α : Type*) [UniformSpace α] [AddGroup α] : Prop where
  uniformContinuous_sub : UniformContinuous fun p : α × α => p.1 - p.2

attribute [to_additive] IsUniformGroup

@[to_additive]
/--
theorem `IsUniformGroup.mk'` / 定理 `IsUniformGroup.mk'`

English:
theorem IsUniformGroup.mk'
  statement: {α} [UniformSpace α] [Group α]
  proof: ⟨by simpa only [div_eq_mul_inv] using!
    h₁.comp (uniformContinuous_fst.prodMk (h₂.comp uniformContinuous_snd))⟩

中文:
定理 是一致群.mk'
  结论: {α} [一致空间 α] [群 α]
  证明: ⟨by simpa only [div_eq_mul_inv] using!
    h₁.comp (uniformContinuous_fst.prodMk (h₂.comp uniformContinuous_snd))⟩

Depends on / 依赖: div_eq_mul_inv, prodMk, uniformContinuous_fst, uniformContinuous_fst.prodMk, uniformContinuous_snd
-/
theorem IsUniformGroup.mk' {α} [UniformSpace α] [Group α]
    (h₁ : UniformContinuous fun p : α × α => p.1 * p.2) (h₂ : UniformContinuous fun p : α => p⁻¹) :
    IsUniformGroup α :=
  ⟨by simpa only [div_eq_mul_inv] using!
    h₁.comp (uniformContinuous_fst.prodMk (h₂.comp uniformContinuous_snd))⟩

variable [UniformSpace α] [Group α] [IsUniformGroup α]

@[to_additive]
/--
theorem `uniformContinuous_div` / 定理 `uniformContinuous_div`

English:
theorem uniformContinuous_div
  statement: UniformContinuous fun p : α × α => p.1 / p.2
  proof: IsUniformGroup.uniformContinuous_div

@[to_additive (attr := fun_prop)]

中文:
定理 uniformContinuous_div
  结论: 一致连续 fun p : α × α => p.1 / p.2
  证明: IsUniformGroup.uniformContinuous_div

@[to_additive (attr := fun_prop)]

Depends on / 依赖: IsUniformGroup, IsUniformGroup.uniformContinuous_div, uniformContinuous_div
-/
theorem uniformContinuous_div : UniformContinuous fun p : α × α => p.1 / p.2 :=
  IsUniformGroup.uniformContinuous_div

@[to_additive (attr := fun_prop)]
/--
theorem `UniformContinuous.div` / 定理 `UniformContinuous.div`

English:
theorem UniformContinuous.div
  statement: [UniformSpace β] {f : β -> α} {g : β -> α} (hf : UniformContinuous f)
  proof: uniformContinuous_div.comp (hf.prodMk hg)

@[to_additive (attr := fun_prop)]

中文:
定理 一致连续.div
  结论: [一致空间 β] {f : β -> α} {g : β -> α} (hf : 一致连续 f)
  证明: uniformContinuous_div.comp (hf.prodMk hg)

@[to_additive (attr := fun_prop)]

Depends on / 依赖: hf.prodMk, prodMk, uniformContinuous_div, uniformContinuous_div.comp
-/
theorem UniformContinuous.div [UniformSpace β] {f : β -> α} {g : β -> α} (hf : UniformContinuous f)
    (hg : UniformContinuous g) : UniformContinuous fun x => f x / g x :=
  uniformContinuous_div.comp (hf.prodMk hg)

@[to_additive (attr := fun_prop)]
/--
theorem `UniformContinuous.inv` / 定理 `UniformContinuous.inv`

English:
theorem UniformContinuous.inv
  given: [UniformSpace β] {f : β -> α} (hf : UniformContinuous f)
  proof: by
  have : UniformContinuous fun x => 1 / f x := uniformContinuous_const.div hf
  simp_all

@[to_additive]

中文:
定理 一致连续.inv
  条件: [一致空间 β] {f : β -> α} (hf : 一致连续 f)
  证明: by
  have : UniformContinuous fun x => 1 / f x := uniformContinuous_const.div hf
  simp_all

@[to_additive]

Depends on / 依赖: UniformContinuous, uniformContinuous_const, uniformContinuous_const.div
-/
theorem UniformContinuous.inv [UniformSpace β] {f : β -> α} (hf : UniformContinuous f) :
    UniformContinuous fun x => (f x)⁻¹ := by
  have : UniformContinuous fun x => 1 / f x := uniformContinuous_const.div hf
  simp_all

@[to_additive]
/--
theorem `uniformContinuous_inv` / 定理 `uniformContinuous_inv`

English:
theorem uniformContinuous_inv
  statement: UniformContinuous fun x : α => x⁻¹
  proof: uniformContinuous_id.inv

@[to_additive (attr := fun_prop)]

中文:
定理 uniformContinuous_inv
  结论: 一致连续 fun x : α => x⁻¹
  证明: uniformContinuous_id.inv

@[to_additive (attr := fun_prop)]

Depends on / 依赖: uniformContinuous_id, uniformContinuous_id.inv
-/
theorem uniformContinuous_inv : UniformContinuous fun x : α => x⁻¹ :=
  uniformContinuous_id.inv

@[to_additive (attr := fun_prop)]
/--
theorem `UniformContinuous.mul` / 定理 `UniformContinuous.mul`

English:
theorem UniformContinuous.mul
  statement: [UniformSpace β] {f : β -> α} {g : β -> α} (hf : UniformContinuous f)
  proof: by
  have : UniformContinuous fun x => f x / (g x)⁻¹ := hf.div hg.inv
  simp_all

@[to_additive]

中文:
定理 一致连续.mul
  结论: [一致空间 β] {f : β -> α} {g : β -> α} (hf : 一致连续 f)
  证明: by
  have : UniformContinuous fun x => f x / (g x)⁻¹ := hf.div hg.inv
  simp_all

@[to_additive]

Depends on / 依赖: UniformContinuous, hf.div, hg.inv
-/
theorem UniformContinuous.mul [UniformSpace β] {f : β -> α} {g : β -> α} (hf : UniformContinuous f)
    (hg : UniformContinuous g) : UniformContinuous fun x => f x * g x := by
  have : UniformContinuous fun x => f x / (g x)⁻¹ := hf.div hg.inv
  simp_all

@[to_additive]
/--
theorem `Finset.uniformContinuous_prod` / 定理 `Finset.uniformContinuous_prod`

English:
theorem Finset.uniformContinuous_prod
  statement: {α β ι : Type*} [UniformSpace α] [CommGroup α]
  proof: by
  induction s using Finset.cons_induction with
  | empty => simpa using uniformContinuous_const
  | cons a s ha ih =>
    simp_rw [Finset.mem_cons, forall_eq_or_imp] at h
    simpa [Finset.prod_cons] using h.1.mul (ih h.2)

@[to_additive]

中文:
定理 有限集.uniformContinuous_prod
  结论: {α β ι : 类型} [一致空间 α] [交换群 α]
  证明: by
  induction s using Finset.cons_induction with
  | empty => simpa using uniformContinuous_const
  | cons a s ha ih =>
    simp_rw [Finset.mem_cons, forall_eq_or_imp] at h
    simpa [Finset.prod_cons] using h.1.mul (ih h.2)

@[to_additive]

Depends on / 依赖: Finset, Finset.cons_induction, Finset.mem_cons, Finset.prod_cons, cons_induction, forall_eq_or_imp, mem_cons, prod_cons, simp_rw, uniformContinuous_const
-/
theorem Finset.uniformContinuous_prod {α β ι : Type*} [UniformSpace α] [CommGroup α]
    [IsUniformGroup α] [UniformSpace β] {f : ι -> β -> α} (s : Finset ι)
    (h : forall i in s, UniformContinuous (f i)) :
    UniformContinuous (∏ i in s, f i ·) := by
  induction s using Finset.cons_induction with
  | empty => simpa using uniformContinuous_const
  | cons a s ha ih =>
    simp_rw [Finset.mem_cons, forall_eq_or_imp] at h
    simpa [Finset.prod_cons] using h.1.mul (ih h.2)

@[to_additive]
/--
theorem `uniformContinuous_mul` / 定理 `uniformContinuous_mul`

English:
theorem uniformContinuous_mul
  statement: UniformContinuous fun p : α × α => p.1 * p.2
  proof: uniformContinuous_fst.mul uniformContinuous_snd

@[to_additive]

中文:
定理 uniformContinuous_mul
  结论: 一致连续 fun p : α × α => p.1 * p.2
  证明: uniformContinuous_fst.mul uniformContinuous_snd

@[to_additive]

Depends on / 依赖: uniformContinuous_fst, uniformContinuous_fst.mul, uniformContinuous_snd
-/
theorem uniformContinuous_mul : UniformContinuous fun p : α × α => p.1 * p.2 :=
  uniformContinuous_fst.mul uniformContinuous_snd

@[to_additive]
/--
theorem `UniformContinuous.mul_const` / 定理 `UniformContinuous.mul_const`

English:
theorem UniformContinuous.mul_const
  statement: [UniformSpace β] {f : β -> α} (hf : UniformContinuous f)
  proof: hf.mul uniformContinuous_const

@[to_additive]

中文:
定理 一致连续.mul_const
  结论: [一致空间 β] {f : β -> α} (hf : 一致连续 f)
  证明: hf.mul uniformContinuous_const

@[to_additive]

Depends on / 依赖: hf.mul, uniformContinuous_const
-/
theorem UniformContinuous.mul_const [UniformSpace β] {f : β -> α} (hf : UniformContinuous f)
    (a : α) : UniformContinuous fun x => f x * a :=
  hf.mul uniformContinuous_const

@[to_additive]
/--
theorem `UniformContinuous.const_mul` / 定理 `UniformContinuous.const_mul`

English:
theorem UniformContinuous.const_mul
  statement: [UniformSpace β] {f : β -> α} (hf : UniformContinuous f)
  proof: uniformContinuous_const.mul hf

@[to_additive]

中文:
定理 一致连续.const_mul
  结论: [一致空间 β] {f : β -> α} (hf : 一致连续 f)
  证明: uniformContinuous_const.mul hf

@[to_additive]

Depends on / 依赖: uniformContinuous_const, uniformContinuous_const.mul
-/
theorem UniformContinuous.const_mul [UniformSpace β] {f : β -> α} (hf : UniformContinuous f)
    (a : α) : UniformContinuous fun x => a * f x :=
  uniformContinuous_const.mul hf

@[to_additive]
/--
theorem `uniformContinuous_mul_left` / 定理 `uniformContinuous_mul_left`

English:
theorem uniformContinuous_mul_left
  given: (a : α)
  statement: UniformContinuous fun b : α => a * b
  proof: uniformContinuous_id.const_mul _

@[to_additive]

中文:
定理 uniformContinuous_mul_left
  条件: (a : α)
  结论: 一致连续 fun b : α => a * b
  证明: uniformContinuous_id.const_mul _

@[to_additive]

Depends on / 依赖: const_mul, uniformContinuous_id, uniformContinuous_id.const_mul
-/
theorem uniformContinuous_mul_left (a : α) : UniformContinuous fun b : α => a * b :=
  uniformContinuous_id.const_mul _

@[to_additive]
/--
theorem `uniformContinuous_mul_right` / 定理 `uniformContinuous_mul_right`

English:
theorem uniformContinuous_mul_right
  given: (a : α)
  statement: UniformContinuous fun b : α => b * a
  proof: uniformContinuous_id.mul_const _

@[to_additive]

中文:
定理 uniformContinuous_mul_right
  条件: (a : α)
  结论: 一致连续 fun b : α => b * a
  证明: uniformContinuous_id.mul_const _

@[to_additive]

Depends on / 依赖: mul_const, uniformContinuous_id, uniformContinuous_id.mul_const
-/
theorem uniformContinuous_mul_right (a : α) : UniformContinuous fun b : α => b * a :=
  uniformContinuous_id.mul_const _

@[to_additive]
/--
theorem `UniformContinuous.div_const` / 定理 `UniformContinuous.div_const`

English:
theorem UniformContinuous.div_const
  statement: [UniformSpace β] {f : β -> α} (hf : UniformContinuous f)
  proof: hf.div uniformContinuous_const

@[to_additive]

中文:
定理 一致连续.div_const
  结论: [一致空间 β] {f : β -> α} (hf : 一致连续 f)
  证明: hf.div uniformContinuous_const

@[to_additive]

Depends on / 依赖: hf.div, uniformContinuous_const
-/
theorem UniformContinuous.div_const [UniformSpace β] {f : β -> α} (hf : UniformContinuous f)
    (a : α) : UniformContinuous fun x => f x / a :=
  hf.div uniformContinuous_const

@[to_additive]
/--
theorem `uniformContinuous_div_const` / 定理 `uniformContinuous_div_const`

English:
theorem uniformContinuous_div_const
  given: (a : α)
  statement: UniformContinuous fun b : α => b / a
  proof: uniformContinuous_id.div_const _

@[to_additive]

中文:
定理 uniformContinuous_div_const
  条件: (a : α)
  结论: 一致连续 fun b : α => b / a
  证明: uniformContinuous_id.div_const _

@[to_additive]

Depends on / 依赖: div_const, uniformContinuous_id, uniformContinuous_id.div_const
-/
theorem uniformContinuous_div_const (a : α) : UniformContinuous fun b : α => b / a :=
  uniformContinuous_id.div_const _

@[to_additive]
/--
theorem `Filter.Tendsto.uniformity_mul` / 定理 `Filter.Tendsto.uniformity_mul`

English:
theorem Filter.Tendsto.uniformity_mul
  statement: {ι : Type*} {f g : ι -> α × α} {l : Filter ι}
  proof: have : Tendsto (fun (p : (α × α) × (α × α)) => p.1 * p.2) (𝓤 α ×ˢ 𝓤 α) (𝓤 α) := by
    simpa [UniformContinuous, uniformity_prod_eq_prod] using! uniformContinuous_mul (α := α)
  this.comp (hf.prodMk hg)

@[to_additive]

中文:
定理 滤子.收敛.uniformity_mul
  结论: {ι : 类型} {f g : ι -> α × α} {l : 滤子 ι}
  证明: have : Tendsto (fun (p : (α × α) × (α × α)) => p.1 * p.2) (𝓤 α ×ˢ 𝓤 α) (𝓤 α) := by
    simpa [UniformContinuous, uniformity_prod_eq_prod] using! uniformContinuous_mul (α := α)
  this.comp (hf.prodMk hg)

@[to_additive]

Depends on / 依赖: Tendsto, UniformContinuous, hf.prodMk, prodMk, this.comp, uniformContinuous_mul, uniformity_prod_eq_prod
-/
theorem Filter.Tendsto.uniformity_mul {ι : Type*} {f g : ι -> α × α} {l : Filter ι}
    (hf : Tendsto f l (𝓤 α)) (hg : Tendsto g l (𝓤 α)) :
    Tendsto (f * g) l (𝓤 α) :=
  have : Tendsto (fun (p : (α × α) × (α × α)) => p.1 * p.2) (𝓤 α ×ˢ 𝓤 α) (𝓤 α) := by
    simpa [UniformContinuous, uniformity_prod_eq_prod] using! uniformContinuous_mul (α := α)
  this.comp (hf.prodMk hg)

@[to_additive]
/--
theorem `Filter.Tendsto.uniformity_inv` / 定理 `Filter.Tendsto.uniformity_inv`

English:
theorem Filter.Tendsto.uniformity_inv
  statement: {ι : Type*} {f : ι -> α × α} {l : Filter ι}
  proof: have : Tendsto (· ⁻¹) (𝓤 α) (𝓤 α) := uniformContinuous_inv
  this.comp hf

@[to_additive]

中文:
定理 滤子.收敛.uniformity_inv
  结论: {ι : 类型} {f : ι -> α × α} {l : 滤子 ι}
  证明: have : Tendsto (· ⁻¹) (𝓤 α) (𝓤 α) := uniformContinuous_inv
  this.comp hf

@[to_additive]

Depends on / 依赖: Tendsto, this.comp, uniformContinuous_inv
-/
theorem Filter.Tendsto.uniformity_inv {ι : Type*} {f : ι -> α × α} {l : Filter ι}
    (hf : Tendsto f l (𝓤 α)) :
    Tendsto (f⁻¹) l (𝓤 α) :=
  have : Tendsto (· ⁻¹) (𝓤 α) (𝓤 α) := uniformContinuous_inv
  this.comp hf

@[to_additive]
/--
theorem `Filter.Tendsto.uniformity_inv_iff` / 定理 `Filter.Tendsto.uniformity_inv_iff`

English:
theorem Filter.Tendsto.uniformity_inv_iff
  given: {ι : Type*} {f : ι -> α × α} {l : Filter ι}
  proof: ⟨fun H => inv_inv f ▸ H.uniformity_inv, Filter.Tendsto.uniformity_inv⟩

@[to_additive]

中文:
定理 滤子.收敛.uniformity_inv_iff
  条件: {ι : 类型} {f : ι -> α × α} {l : 滤子 ι}
  证明: ⟨fun H => inv_inv f ▸ H.uniformity_inv, Filter.Tendsto.uniformity_inv⟩

@[to_additive]

Depends on / 依赖: Filter, Filter.Tendsto.uniformity_inv, H.uniformity_inv, Tendsto, inv_inv, uniformity_inv
-/
theorem Filter.Tendsto.uniformity_inv_iff {ι : Type*} {f : ι -> α × α} {l : Filter ι} :
    Tendsto (f⁻¹) l (𝓤 α) ↔ Tendsto f l (𝓤 α) :=
  ⟨fun H => inv_inv f ▸ H.uniformity_inv, Filter.Tendsto.uniformity_inv⟩

@[to_additive]
/--
theorem `Filter.Tendsto.uniformity_div` / 定理 `Filter.Tendsto.uniformity_div`

English:
theorem Filter.Tendsto.uniformity_div
  statement: {ι : Type*} {f g : ι -> α × α} {l : Filter ι}
  proof: by
  rw [div_eq_mul_inv]
  exact hf.uniformity_mul hg.uniformity_inv

中文:
定理 滤子.收敛.uniformity_div
  结论: {ι : 类型} {f g : ι -> α × α} {l : 滤子 ι}
  证明: by
  rw [div_eq_mul_inv]
  exact hf.uniformity_mul hg.uniformity_inv

Depends on / 依赖: div_eq_mul_inv, hf.uniformity_mul, hg.uniformity_inv, uniformity_inv, uniformity_mul
-/
theorem Filter.Tendsto.uniformity_div {ι : Type*} {f g : ι -> α × α} {l : Filter ι}
    (hf : Tendsto f l (𝓤 α)) (hg : Tendsto g l (𝓤 α)) :
    Tendsto (f / g) l (𝓤 α) := by
  rw [div_eq_mul_inv]
  exact hf.uniformity_mul hg.uniformity_inv

/-- If `f : ι → G × G` converges to the uniformity, then any `g : ι → G × G` converges to the
uniformity iff `f * g` does. This is often useful when `f` is valued in the diagonal,
in which case its convergence is automatic. -/
@[to_additive /-- If `f : ι → G × G` converges to the uniformity, then any `g : ι → G × G`
converges to the uniformity iff `f + g` does. This is often useful when `f` is valued in the
diagonal, in which case its convergence is automatic. -/]
/--
theorem `Filter.Tendsto.uniformity_mul_iff_right` / 定理 `Filter.Tendsto.uniformity_mul_iff_right`

English:
theorem Filter.Tendsto.uniformity_mul_iff_right
  statement: {ι : Type*} {f g : ι -> α × α} {l : Filter ι}
  proof: ⟨fun hfg => by simpa using hf.uniformity_inv.uniformity_mul hfg, hf.uniformity_mul⟩

中文:
定理 滤子.收敛.uniformity_mul_iff_right
  结论: {ι : 类型} {f g : ι -> α × α} {l : 滤子 ι}
  证明: ⟨fun hfg => by simpa using hf.uniformity_inv.uniformity_mul hfg, hf.uniformity_mul⟩

Depends on / 依赖: hf.uniformity_inv.uniformity_mul, hf.uniformity_mul, uniformity_inv, uniformity_mul
-/
theorem Filter.Tendsto.uniformity_mul_iff_right {ι : Type*} {f g : ι -> α × α} {l : Filter ι}
    (hf : Tendsto f l (𝓤 α)) :
    Tendsto (f * g) l (𝓤 α) ↔ Tendsto g l (𝓤 α) :=
  ⟨fun hfg => by simpa using hf.uniformity_inv.uniformity_mul hfg, hf.uniformity_mul⟩

/-- If `g : ι → G × G` converges to the uniformity, then any `f : ι → G × G` converges to the
uniformity iff `f * g` does. This is often useful when `g` is valued in the diagonal,
in which case its convergence is automatic. -/
@[to_additive /-- If `g : ι → G × G` converges to the uniformity, then any `f : ι → G × G`
converges to the uniformity iff `f + g` does. This is often useful when `g` is valued in the
diagonal, in which case its convergence is automatic. -/]
/--
theorem `Filter.Tendsto.uniformity_mul_iff_left` / 定理 `Filter.Tendsto.uniformity_mul_iff_left`

English:
theorem Filter.Tendsto.uniformity_mul_iff_left
  statement: {ι : Type*} {f g : ι -> α × α} {l : Filter ι}
  proof: ⟨fun hfg => by simpa using hfg.uniformity_mul hg.uniformity_inv, fun hf => hf.uniformity_mul hg⟩

@[to_additive (attr := fun_prop) UniformContinuous.const_nsmul]

中文:
定理 滤子.收敛.uniformity_mul_iff_left
  结论: {ι : 类型} {f g : ι -> α × α} {l : 滤子 ι}
  证明: ⟨fun hfg => by simpa using hfg.uniformity_mul hg.uniformity_inv, fun hf => hf.uniformity_mul hg⟩

@[to_additive (attr := fun_prop) UniformContinuous.const_nsmul]

Depends on / 依赖: hf.uniformity_mul, hfg.uniformity_mul, hg.uniformity_inv, uniformity_inv, uniformity_mul
-/
theorem Filter.Tendsto.uniformity_mul_iff_left {ι : Type*} {f g : ι -> α × α} {l : Filter ι}
    (hg : Tendsto g l (𝓤 α)) :
    Tendsto (f * g) l (𝓤 α) ↔ Tendsto f l (𝓤 α) :=
  ⟨fun hfg => by simpa using hfg.uniformity_mul hg.uniformity_inv, fun hf => hf.uniformity_mul hg⟩

@[to_additive (attr := fun_prop) UniformContinuous.const_nsmul]
/--
theorem `UniformContinuous.pow_const` / 定理 `UniformContinuous.pow_const`

English:
theorem UniformContinuous.pow_const
  given: [UniformSpace β] {f : β -> α} (hf : UniformContinuous f)

中文:
定理 一致连续.pow_const
  条件: [一致空间 β] {f : β -> α} (hf : 一致连续 f)
-/
theorem UniformContinuous.pow_const [UniformSpace β] {f : β -> α} (hf : UniformContinuous f) :
    forall n : Nat, UniformContinuous fun x => f x ^ n
  | 0 => by
    simp_rw [pow_zero]
    exact uniformContinuous_const
  | n + 1 => by
    simp_rw [pow_succ']
    exact hf.mul (hf.pow_const n)

@[to_additive uniformContinuous_const_nsmul]
/--
theorem `uniformContinuous_pow_const` / 定理 `uniformContinuous_pow_const`

English:
theorem uniformContinuous_pow_const
  given: (n : Nat)
  statement: UniformContinuous fun x : α => x ^ n
  proof: uniformContinuous_id.pow_const n

@[to_additive (attr := fun_prop) UniformContinuous.const_zsmul]

中文:
定理 uniformContinuous_pow_const
  条件: (n : 自然数)
  结论: 一致连续 fun x : α => x ^ n
  证明: uniformContinuous_id.pow_const n

@[to_additive (attr := fun_prop) UniformContinuous.const_zsmul]

Depends on / 依赖: pow_const, uniformContinuous_id, uniformContinuous_id.pow_const
-/
theorem uniformContinuous_pow_const (n : Nat) : UniformContinuous fun x : α => x ^ n :=
  uniformContinuous_id.pow_const n

@[to_additive (attr := fun_prop) UniformContinuous.const_zsmul]
/--
theorem `UniformContinuous.zpow_const` / 定理 `UniformContinuous.zpow_const`

English:
theorem UniformContinuous.zpow_const
  given: [UniformSpace β] {f : β -> α} (hf : UniformContinuous f)

中文:
定理 一致连续.zpow_const
  条件: [一致空间 β] {f : β -> α} (hf : 一致连续 f)
-/
theorem UniformContinuous.zpow_const [UniformSpace β] {f : β -> α} (hf : UniformContinuous f) :
    forall n : Int, UniformContinuous fun x => f x ^ n
  | (n : Nat) => by
    simp_rw [zpow_natCast]
    exact hf.pow_const _
  | Int.negSucc n => by
    simp_rw [zpow_negSucc]
    exact (hf.pow_const _).inv

@[to_additive uniformContinuous_const_zsmul]
/--
theorem `uniformContinuous_zpow_const` / 定理 `uniformContinuous_zpow_const`

English:
theorem uniformContinuous_zpow_const
  given: (n : Int)
  statement: UniformContinuous fun x : α => x ^ n
  proof: uniformContinuous_id.zpow_const n

@[to_additive]

中文:
定理 uniformContinuous_zpow_const
  条件: (n : 整数)
  结论: 一致连续 fun x : α => x ^ n
  证明: uniformContinuous_id.zpow_const n

@[to_additive]

Depends on / 依赖: uniformContinuous_id, uniformContinuous_id.zpow_const, zpow_const
-/
theorem uniformContinuous_zpow_const (n : Int) : UniformContinuous fun x : α => x ^ n :=
  uniformContinuous_id.zpow_const n

@[to_additive]
instance (priority := 10) IsUniformGroup.to_topologicalGroup : IsTopologicalGroup α where
  continuous_mul := uniformContinuous_mul.continuous
  continuous_inv := uniformContinuous_inv.continuous

@[to_additive]
/--
theorem `uniformity_translate_mul` / 定理 `uniformity_translate_mul`

English:
theorem uniformity_translate_mul
  given: (a : α)
  statement: ((𝓤 α).map fun x : α × α => (x.1 * a, x.2 * a)) = 𝓤 α
  proof: le_antisymm (uniformContinuous_id.mul uniformContinuous_const)
    (calc
      𝓤 α =
          ((𝓤 α).map fun x : α × α => (x.1 * a⁻¹, x.2 * a⁻¹)).map fun x : α × α =>
            (x.1 * a, x.2 * a) := by simp [Filter.map_map, Function.comp_def]
      _ <= (𝓤 α).map fun x : α × α => (x.1 * a, x.2 * a) :=
        Filter.map_mono (uniformContinuous_id.mul uniformContinuous_const))

中文:
定理 uniformity_translate_mul
  条件: (a : α)
  结论: ((𝓤 α).map fun x : α × α => (x.1 * a, x.2 * a)) = 𝓤 α
  证明: le_antisymm (uniformContinuous_id.mul uniformContinuous_const)
    (calc
      𝓤 α =
          ((𝓤 α).map fun x : α × α => (x.1 * a⁻¹, x.2 * a⁻¹)).map fun x : α × α =>
            (x.1 * a, x.2 * a) := by simp [Filter.map_map, Function.comp_def]
      _ <= (𝓤 α).map fun x : α × α => (x.1 * a, x.2 * a) :=
        Filter.map_mono (uniformContinuous_id.mul uniformContinuous_const))

Depends on / 依赖: Filter, Filter.map_map, Filter.map_mono, Function, Function.comp_def, comp_def, le_antisymm, map_map, map_mono, uniformContinuous_const, uniformContinuous_id, uniformContinuous_id.mul
-/
theorem uniformity_translate_mul (a : α) : ((𝓤 α).map fun x : α × α => (x.1 * a, x.2 * a)) = 𝓤 α :=
  le_antisymm (uniformContinuous_id.mul uniformContinuous_const)
    (calc
      𝓤 α =
          ((𝓤 α).map fun x : α × α => (x.1 * a⁻¹, x.2 * a⁻¹)).map fun x : α × α =>
            (x.1 * a, x.2 * a) := by simp [Filter.map_map, Function.comp_def]
      _ <= (𝓤 α).map fun x : α × α => (x.1 * a, x.2 * a) :=
        Filter.map_mono (uniformContinuous_id.mul uniformContinuous_const))

namespace MulOpposite

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsUniformGroup αᵐᵒᵖ
  body: ⟨uniformContinuous_op.comp
      ((uniformContinuous_unop.comp uniformContinuous_snd).inv.mul <|
        uniformContinuous_unop.comp uniformContinuous_fst)⟩

中文:
实例 :
  签名: 是一致群 αᵐᵒᵖ
  定义体: ⟨uniformContinuous_op.comp
      ((uniformContinuous_unop.comp uniformContinuous_snd).inv.mul <|
        uniformContinuous_unop.comp uniformContinuous_fst)⟩

Depends on / 依赖: inv.mul, uniformContinuous_fst, uniformContinuous_op, uniformContinuous_op.comp, uniformContinuous_snd, uniformContinuous_unop, uniformContinuous_unop.comp
-/
instance : IsUniformGroup αᵐᵒᵖ :=
  ⟨uniformContinuous_op.comp
      ((uniformContinuous_unop.comp uniformContinuous_snd).inv.mul <|
        uniformContinuous_unop.comp uniformContinuous_fst)⟩

end MulOpposite

section

variable (α)

@[to_additive]
/--
Instance `IsUniformGroup.isRightUniformGroup` / 实例 `IsUniformGroup.isRightUniformGroup`

English:
instance IsUniformGroup.isRightUniformGroup
  signature: : IsRightUniformGroup α where
  body: by
    refine eq_of_forall_le_iff fun 𝓕 => ?_
    rw [nhds_eq_comap_uniformity]; rw [comap_comap]; rw [← tendsto_iff_comap]; rw [← (tendsto_diag_uniformity Prod.fst 𝓕).uniformity_mul_iff_left]; rw [← tendsto_id']
    congrm Tendsto ?_ _ _
    ext <;> simp

@[to_additive]

中文:
实例 是一致群.isRightUniformGroup
  签名: : 是RightUniform群 α where
  定义体: by
    refine eq_of_forall_le_iff fun 𝓕 => ?_
    rw [nhds_eq_comap_uniformity]; rw [comap_comap]; rw [← tendsto_iff_comap]; rw [← (tendsto_diag_uniformity Prod.fst 𝓕).uniformity_mul_iff_left]; rw [← tendsto_id']
    congrm Tendsto ?_ _ _
    ext <;> simp

@[to_additive]

Depends on / 依赖: Prod.fst, Tendsto, comap_comap, congrm, eq_of_forall_le_iff, nhds_eq_comap_uniformity, tendsto_diag_uniformity, tendsto_id, tendsto_iff_comap, uniformity_mul_iff_left
-/
instance IsUniformGroup.isRightUniformGroup : IsRightUniformGroup α where
  uniformity_eq := by
    refine eq_of_forall_le_iff fun 𝓕 => ?_
    rw [nhds_eq_comap_uniformity]; rw [comap_comap]; rw [← tendsto_iff_comap]; rw [← (tendsto_diag_uniformity Prod.fst 𝓕).uniformity_mul_iff_left]; rw [← tendsto_id']
    congrm Tendsto ?_ _ _
    ext <;> simp

@[to_additive]
/--
Instance `IsUniformGroup.isLeftUniformGroup` / 实例 `IsUniformGroup.isLeftUniformGroup`

English:
instance IsUniformGroup.isLeftUniformGroup
  signature: : IsLeftUniformGroup α where
  body: by
    refine eq_of_forall_le_iff fun 𝓕 => ?_
    rw [nhds_eq_comap_uniformity]; rw [comap_comap]; rw [← tendsto_iff_comap]; rw [← (tendsto_diag_uniformity Prod.fst 𝓕).uniformity_mul_iff_right]; rw [← tendsto_id']
    congrm Tendsto ?_ _ _
    ext <;> simp

@[to_additive]

中文:
实例 是一致群.isLeftUniformGroup
  签名: : 是LeftUniform群 α where
  定义体: by
    refine eq_of_forall_le_iff fun 𝓕 => ?_
    rw [nhds_eq_comap_uniformity]; rw [comap_comap]; rw [← tendsto_iff_comap]; rw [← (tendsto_diag_uniformity Prod.fst 𝓕).uniformity_mul_iff_right]; rw [← tendsto_id']
    congrm Tendsto ?_ _ _
    ext <;> simp

@[to_additive]

Depends on / 依赖: Prod.fst, Tendsto, comap_comap, congrm, eq_of_forall_le_iff, nhds_eq_comap_uniformity, tendsto_diag_uniformity, tendsto_id, tendsto_iff_comap, uniformity_mul_iff_right
-/
instance IsUniformGroup.isLeftUniformGroup : IsLeftUniformGroup α where
  uniformity_eq := by
    refine eq_of_forall_le_iff fun 𝓕 => ?_
    rw [nhds_eq_comap_uniformity]; rw [comap_comap]; rw [← tendsto_iff_comap]; rw [← (tendsto_diag_uniformity Prod.fst 𝓕).uniformity_mul_iff_right]; rw [← tendsto_id']
    congrm Tendsto ?_ _ _
    ext <;> simp

@[to_additive]
/--
theorem `IsUniformGroup.ext` / 定理 `IsUniformGroup.ext`

English:
theorem IsUniformGroup.ext
  statement: {G : Type*} [Group G] {u v : UniformSpace G} (hu : @IsUniformGroup G u _)
  proof: UniformSpace.ext by
    rw [(have := hu; uniformity_eq_comap_nhds_one)]; rw [(have := hv; uniformity_eq_comap_nhds_one)]; rw [h]

@[to_additive]

中文:
定理 是一致群.ext
  结论: {G : 类型} [群 G] {u v : 一致空间 G} (hu : @是一致群 G u _)
  证明: UniformSpace.ext by
    rw [(have := hu; uniformity_eq_comap_nhds_one)]; rw [(have := hv; uniformity_eq_comap_nhds_one)]; rw [h]

@[to_additive]

Depends on / 依赖: UniformSpace, UniformSpace.ext, uniformity_eq_comap_nhds_one
-/
theorem IsUniformGroup.ext {G : Type*} [Group G] {u v : UniformSpace G} (hu : @IsUniformGroup G u _)
    (hv : @IsUniformGroup G v _)
    (h : @nhds _ u.toTopologicalSpace 1 = @nhds _ v.toTopologicalSpace 1) : u = v :=
UniformSpace.ext by
    rw [(have := hu; uniformity_eq_comap_nhds_one)]; rw [(have := hv; uniformity_eq_comap_nhds_one)]; rw [h]

@[to_additive]
/--
theorem `IsUniformGroup.ext_iff` / 定理 `IsUniformGroup.ext_iff`

English:
theorem IsUniformGroup.ext_iff
  statement: {G : Type*} [Group G] {u v : UniformSpace G}
  proof: ⟨fun h => h ▸ rfl, hu.ext hv⟩

中文:
定理 是一致群.ext_iff
  结论: {G : 类型} [群 G] {u v : 一致空间 G}
  证明: ⟨fun h => h ▸ rfl, hu.ext hv⟩

Depends on / 依赖: hu.ext
-/
theorem IsUniformGroup.ext_iff {G : Type*} [Group G] {u v : UniformSpace G}
    (hu : @IsUniformGroup G u _) (hv : @IsUniformGroup G v _) :
    u = v ↔ @nhds _ u.toTopologicalSpace 1 = @nhds _ v.toTopologicalSpace 1 :=
  ⟨fun h => h ▸ rfl, hu.ext hv⟩

variable {α}

@[to_additive]
/--
theorem `IsUniformGroup.uniformity_countably_generated` / 定理 `IsUniformGroup.uniformity_countably_generated`

English:
theorem IsUniformGroup.uniformity_countably_generated
  given: [(𝓝 (1 : α)).IsCountablyGenerated]
  proof: by
  rw [uniformity_eq_comap_nhds_one]
  exact Filter.comap.isCountablyGenerated _ _

中文:
定理 是一致群.uniformity_countably_generated
  条件: [(𝓝 (1 : α)).是余untablyGenerated]
  证明: by
  rw [uniformity_eq_comap_nhds_one]
  exact Filter.comap.isCountablyGenerated _ _

Depends on / 依赖: Filter, Filter.comap.isCountablyGenerated, isCountablyGenerated, uniformity_eq_comap_nhds_one
-/
theorem IsUniformGroup.uniformity_countably_generated [(𝓝 (1 : α)).IsCountablyGenerated] :
    (𝓤 α).IsCountablyGenerated := by
  rw [uniformity_eq_comap_nhds_one]
  exact Filter.comap.isCountablyGenerated _ _

end

section OfLeftAndRight

variable [UniformSpace β] [Group β] [IsLeftUniformGroup β] [IsRightUniformGroup β]

open Prod (snd) in
/-- Note: this assumes `[IsLeftUniformGroup β] [IsRightUniformGroup β]` instead of the more typical
(and equivalent) `[IsUniformGroup β]` because this is used in the proof of said equivalence. -/
@[to_additive /-- Note: this assumes `[IsLeftUniformAddGroup β] [IsRightUniformAddGroup β]`
instead of the more typical (and equivalent) `[IsUniformAddGroup β]` because this is used
in the proof of said equivalence. -/]
/--
theorem `comap_conj_nhds_one` / 定理 `comap_conj_nhds_one`

English:
theorem comap_conj_nhds_one
  proof: by
  let dr : β × β -> β := fun xy => xy.2 * xy.1⁻¹
  let dl : β × β -> β := fun xy => xy.1⁻¹ * xy.2
  let conj : β × β -> β := fun gx => gx.1 * gx.2 * gx.1⁻¹
  let φ : β × β ≃ β × β := (Equiv.refl β).prodShear (fun b => (Equiv.mulLeft b).symm)
  have conj_φ : conj ∘ φ = dr := by
    ext; simp [conj, φ, dr]
  have snd_φ : snd ∘ φ = dl := by
    ext; simp [φ, dl]
  rw [← (comap_injective φ.surjective).eq_iff]; rw [comap_comap]; rw [comap_comap]; rw [conj_φ]; rw [snd_φ]; rw [← uniformity_eq_comap_inv_mul_nhds_one]; rw [← uniformity_eq_comap_mul_inv_nhds_one]

中文:
定理 comap_conj_nhds_one
  证明: by
  let dr : β × β -> β := fun xy => xy.2 * xy.1⁻¹
  let dl : β × β -> β := fun xy => xy.1⁻¹ * xy.2
  let conj : β × β -> β := fun gx => gx.1 * gx.2 * gx.1⁻¹
  let φ : β × β ≃ β × β := (Equiv.refl β).prodShear (fun b => (Equiv.mulLeft b).symm)
  have conj_φ : conj ∘ φ = dr := by
    ext; simp [conj, φ, dr]
  have snd_φ : snd ∘ φ = dl := by
    ext; simp [φ, dl]
  rw [← (comap_injective φ.surjective).eq_iff]; rw [comap_comap]; rw [comap_comap]; rw [conj_φ]; rw [snd_φ]; rw [← uniformity_eq_comap_inv_mul_nhds_one]; rw [← uniformity_eq_comap_mul_inv_nhds_one]

Depends on / 依赖: Equiv.mulLeft, Equiv.refl, comap_comap, comap_injective, eq_iff, mulLeft, prodShear, surjective, uniformity_eq_comap_inv_mul_nhds_one
-/
theorem comap_conj_nhds_one :
    comap (fun gx : β × β => gx.1 * gx.2 * gx.1⁻¹) (𝓝 1) = comap snd (𝓝 1) := by
  let dr : β × β -> β := fun xy => xy.2 * xy.1⁻¹
  let dl : β × β -> β := fun xy => xy.1⁻¹ * xy.2
  let conj : β × β -> β := fun gx => gx.1 * gx.2 * gx.1⁻¹
  let φ : β × β ≃ β × β := (Equiv.refl β).prodShear (fun b => (Equiv.mulLeft b).symm)
  have conj_φ : conj ∘ φ = dr := by
    ext; simp [conj, φ, dr]
  have snd_φ : snd ∘ φ = dl := by
    ext; simp [φ, dl]
  rw [← (comap_injective φ.surjective).eq_iff]; rw [comap_comap]; rw [comap_comap]; rw [conj_φ]; rw [snd_φ]; rw [← uniformity_eq_comap_inv_mul_nhds_one]; rw [← uniformity_eq_comap_mul_inv_nhds_one]

open Prod (snd) in
/-- Note: this assumes `[IsLeftUniformGroup β] [IsRightUniformGroup β]` instead of the more typical
(and equivalent) `[IsUniformGroup β]` because this is used in the proof of said equivalence. -/
@[to_additive /-- Note: this assumes `[IsLeftUniformAddGroup β] [IsRightUniformAddGroup β]`
instead of the more typical (and equivalent) `[IsUniformAddGroup β]` because this is used
in the proof of said equivalence. -/]
/--
theorem `tendsto_conj_nhds_one` / 定理 `tendsto_conj_nhds_one`

English:
theorem tendsto_conj_nhds_one
  proof: by
  rw [tendsto_iff_comap]; rw [comap_conj_nhds_one]

中文:
定理 tendsto_conj_nhds_one
  证明: by
  rw [tendsto_iff_comap]; rw [comap_conj_nhds_one]

Depends on / 依赖: comap_conj_nhds_one, tendsto_iff_comap
-/
theorem tendsto_conj_nhds_one :
    Tendsto (fun gx : β × β => gx.1 * gx.2 * gx.1⁻¹) (comap snd (𝓝 1)) (𝓝 1) := by
  rw [tendsto_iff_comap]; rw [comap_conj_nhds_one]

/-- Note: this assumes `[IsLeftUniformGroup β] [IsRightUniformGroup β]` instead of the more typical
(and equivalent) `[IsUniformGroup β]` because this is used in the proof of said equivalence. -/
@[to_additive /-- Note: this assumes `[IsLeftUniformAddGroup β] [IsRightUniformAddGroup β]`
instead of the more typical (and equivalent) `[IsUniformAddGroup β]` because this is used
in the proof of said equivalence. -/]
/--
theorem `Filter.Tendsto.conj_nhds_one` / 定理 `Filter.Tendsto.conj_nhds_one`

English:
theorem Filter.Tendsto.conj_nhds_one
  statement: {ι : Type*} {l : Filter ι} {x : ι -> β}
  proof: by
  have : Tendsto (fun i => (g i, x i)) l (comap Prod.snd (𝓝 1)) := by
    rwa [tendsto_comap_iff]
  -- `exact` works but is quite slow...
  convert! tendsto_conj_nhds_one.comp this

中文:
定理 滤子.收敛.conj_nhds_one
  结论: {ι : 类型} {l : 滤子 ι} {x : ι -> β}
  证明: by
  have : Tendsto (fun i => (g i, x i)) l (comap Prod.snd (𝓝 1)) := by
    rwa [tendsto_comap_iff]
  -- `exact` works but is quite slow...
  convert! tendsto_conj_nhds_one.comp this

Depends on / 依赖: Prod.snd, Tendsto, tendsto_comap_iff
-/
theorem Filter.Tendsto.conj_nhds_one {ι : Type*} {l : Filter ι} {x : ι -> β}
    (hx : Tendsto x l (𝓝 1)) (g : ι -> β) :
    Tendsto (g * x * g⁻¹) l (𝓝 1) := by
  have : Tendsto (fun i => (g i, x i)) l (comap Prod.snd (𝓝 1)) := by
    rwa [tendsto_comap_iff]
  -- `exact` works but is quite slow...
  convert! tendsto_conj_nhds_one.comp this

/--
theorem `IsUniformGroup.of_left_right` / 定理 `IsUniformGroup.of_left_right`

English:
theorem IsUniformGroup.of_left_right
  statement: IsUniformGroup β where
  proof: by
    let φ : (β × β) × (β × β) -> β := fun ⟨⟨x₁, x₂⟩, ⟨y₁, y₂⟩⟩ => x₂ * y₂⁻¹ * y₁ * x₁⁻¹
    let ψ : (β × β) × (β × β) -> β := fun ⟨⟨x₁, x₂⟩, ⟨y₁, y₂⟩⟩ => (x₁⁻¹ * x₂) * (y₂⁻¹ * y₁)
    let g : (β × β) × (β × β) -> β := fun ⟨⟨x₁, x₂⟩, ⟨y₁, y₂⟩⟩ => x₁
    suffices Tendsto φ (𝓤 β ×ˢ 𝓤 β) (𝓝 1) by
      rw [UniformContinuous]; rw [uniformity_eq_comap_mul_inv_nhds_one β]; rw [tendsto_comap_iff]; rw [uniformity_prod_eq_prod]; rw [tendsto_map'_iff]
      simpa [Function.comp_def, div_eq_mul_inv, ← mul_assoc]
    have φ_ψ_conj : φ = g * ψ * g⁻¹ := by
      ext
      simp [φ, ψ, g, mul_assoc]
    have ψ_tendsto : Tendsto ψ (𝓤 β ×ˢ 𝓤 β) (𝓝 1) := by
      rw [← one_mul 1]
      refine .mul ?_ ?_
      · rw [uniformity_eq_comap_inv_mul_nhds_one]
        exact tendsto_comap.comp tendsto_fst
      · rw [uniformity_eq_comap_inv_mul_nhds_one_swapped]
        exact tendsto_comap.comp tendsto_snd
    exact φ_ψ_conj ▸ ψ_tendsto.conj_nhds_one g

中文:
定理 是一致群.of_left_right
  结论: 是一致群 β where
  证明: by
    let φ : (β × β) × (β × β) -> β := fun ⟨⟨x₁, x₂⟩, ⟨y₁, y₂⟩⟩ => x₂ * y₂⁻¹ * y₁ * x₁⁻¹
    let ψ : (β × β) × (β × β) -> β := fun ⟨⟨x₁, x₂⟩, ⟨y₁, y₂⟩⟩ => (x₁⁻¹ * x₂) * (y₂⁻¹ * y₁)
    let g : (β × β) × (β × β) -> β := fun ⟨⟨x₁, x₂⟩, ⟨y₁, y₂⟩⟩ => x₁
    suffices Tendsto φ (𝓤 β ×ˢ 𝓤 β) (𝓝 1) by
      rw [UniformContinuous]; rw [uniformity_eq_comap_mul_inv_nhds_one β]; rw [tendsto_comap_iff]; rw [uniformity_prod_eq_prod]; rw [tendsto_map'_iff]
      simpa [Function.comp_def, div_eq_mul_inv, ← mul_assoc]
    have φ_ψ_conj : φ = g * ψ * g⁻¹ := by
      ext
      simp [φ, ψ, g, mul_assoc]
    have ψ_tendsto : Tendsto ψ (𝓤 β ×ˢ 𝓤 β) (𝓝 1) := by
      rw [← one_mul 1]
      refine .mul ?_ ?_
      · rw [uniformity_eq_comap_inv_mul_nhds_one]
        exact tendsto_comap.comp tendsto_fst
      · rw [uniformity_eq_comap_inv_mul_nhds_one_swapped]
        exact tendsto_comap.comp tendsto_snd
    exact φ_ψ_conj ▸ ψ_tendsto.conj_nhds_one g

Depends on / 依赖: Function, Function.comp_def, Tendsto, UniformContinuous, _iff, comp_def, div_eq_mul_inv, mul_assoc, tendsto_comap_iff, tendsto_map, uniformity_eq_comap_mul_inv_nhds_one, uniformity_prod_eq_prod
-/
theorem IsUniformGroup.of_left_right : IsUniformGroup β where
  uniformContinuous_div := by
    let φ : (β × β) × (β × β) -> β := fun ⟨⟨x₁, x₂⟩, ⟨y₁, y₂⟩⟩ => x₂ * y₂⁻¹ * y₁ * x₁⁻¹
    let ψ : (β × β) × (β × β) -> β := fun ⟨⟨x₁, x₂⟩, ⟨y₁, y₂⟩⟩ => (x₁⁻¹ * x₂) * (y₂⁻¹ * y₁)
    let g : (β × β) × (β × β) -> β := fun ⟨⟨x₁, x₂⟩, ⟨y₁, y₂⟩⟩ => x₁
    suffices Tendsto φ (𝓤 β ×ˢ 𝓤 β) (𝓝 1) by
      rw [UniformContinuous]; rw [uniformity_eq_comap_mul_inv_nhds_one β]; rw [tendsto_comap_iff]; rw [uniformity_prod_eq_prod]; rw [tendsto_map'_iff]
      simpa [Function.comp_def, div_eq_mul_inv, ← mul_assoc]
    have φ_ψ_conj : φ = g * ψ * g⁻¹ := by
      ext
      simp [φ, ψ, g, mul_assoc]
    have ψ_tendsto : Tendsto ψ (𝓤 β ×ˢ 𝓤 β) (𝓝 1) := by
      rw [← one_mul 1]
      refine .mul ?_ ?_
      · rw [uniformity_eq_comap_inv_mul_nhds_one]
        exact tendsto_comap.comp tendsto_fst
      · rw [uniformity_eq_comap_inv_mul_nhds_one_swapped]
        exact tendsto_comap.comp tendsto_snd
    exact φ_ψ_conj ▸ ψ_tendsto.conj_nhds_one g

/--
theorem `isUniformGroup_iff_left_right` / 定理 `isUniformGroup_iff_left_right`

English:
theorem isUniformGroup_iff_left_right
  given: {γ : Type*} [Group γ] [UniformSpace γ]
  proof: ⟨fun _ => ⟨inferInstance, inferInstance⟩, fun ⟨_, _⟩ => .of_left_right⟩

中文:
定理 isUniformGroup_iff_left_right
  条件: {γ : 类型} [群 γ] [一致空间 γ]
  证明: ⟨fun _ => ⟨inferInstance, inferInstance⟩, fun ⟨_, _⟩ => .of_left_right⟩

Depends on / 依赖: of_left_right
-/
theorem isUniformGroup_iff_left_right {γ : Type*} [Group γ] [UniformSpace γ] :
    IsUniformGroup γ ↔ IsLeftUniformGroup γ ∧ IsRightUniformGroup γ :=
  ⟨fun _ => ⟨inferInstance, inferInstance⟩, fun ⟨_, _⟩ => .of_left_right⟩

/--
theorem `eventually_forall_conj_nhds_one` / 定理 `eventually_forall_conj_nhds_one`

English:
theorem eventually_forall_conj_nhds_one
  statement: {p : α -> Prop}
  proof: by
  simpa using tendsto_conj_nhds_one.eventually hp

中文:
定理 eventually_对任意_conj_nhds_one
  结论: {p : α -> 命题}
  证明: by
  simpa using tendsto_conj_nhds_one.eventually hp

Depends on / 依赖: eventually, tendsto_conj_nhds_one, tendsto_conj_nhds_one.eventually
-/
theorem eventually_forall_conj_nhds_one {p : α -> Prop}
    (hp : forallᶠ x in 𝓝 1, p x) :
    forallᶠ x in 𝓝 1, forall g, p (g * x * g⁻¹) := by
  simpa using tendsto_conj_nhds_one.eventually hp

end OfLeftAndRight

@[to_additive]
/--
theorem `Filter.HasBasis.uniformity_of_nhds_one` / 定理 `Filter.HasBasis.uniformity_of_nhds_one`

English:
theorem Filter.HasBasis.uniformity_of_nhds_one
  statement: {ι} {p : ι -> Prop} {U : ι -> Set α}
  proof: by
  rw [uniformity_eq_comap_nhds_one]
  exact h.comap _

@[to_additive]

中文:
定理 滤子.有基.uniformity_of_nhds_one
  结论: {ι} {p : ι -> 命题} {U : ι -> 集合 α}
  证明: by
  rw [uniformity_eq_comap_nhds_one]
  exact h.comap _

@[to_additive]

Depends on / 依赖: h.comap, uniformity_eq_comap_nhds_one
-/
theorem Filter.HasBasis.uniformity_of_nhds_one {ι} {p : ι -> Prop} {U : ι -> Set α}
    (h : (𝓝 (1 : α)).HasBasis p U) :
    (𝓤 α).HasBasis p fun i => { x : α × α | x.2 / x.1 in U i } := by
  rw [uniformity_eq_comap_nhds_one]
  exact h.comap _

@[to_additive]
/--
theorem `Filter.HasBasis.uniformity_of_nhds_one_inv_mul` / 定理 `Filter.HasBasis.uniformity_of_nhds_one_inv_mul`

English:
theorem Filter.HasBasis.uniformity_of_nhds_one_inv_mul
  statement: {ι} {p : ι -> Prop} {U : ι -> Set α}
  proof: by
  rw [uniformity_eq_comap_inv_mul_nhds_one]
  exact h.comap _

@[to_additive]

中文:
定理 滤子.有基.uniformity_of_nhds_one_inv_mul
  结论: {ι} {p : ι -> 命题} {U : ι -> 集合 α}
  证明: by
  rw [uniformity_eq_comap_inv_mul_nhds_one]
  exact h.comap _

@[to_additive]

Depends on / 依赖: h.comap, uniformity_eq_comap_inv_mul_nhds_one
-/
theorem Filter.HasBasis.uniformity_of_nhds_one_inv_mul {ι} {p : ι -> Prop} {U : ι -> Set α}
    (h : (𝓝 (1 : α)).HasBasis p U) :
    (𝓤 α).HasBasis p fun i => { x : α × α | x.1⁻¹ * x.2 in U i } := by
  rw [uniformity_eq_comap_inv_mul_nhds_one]
  exact h.comap _

@[to_additive]
/--
theorem `Filter.HasBasis.uniformity_of_nhds_one_swapped` / 定理 `Filter.HasBasis.uniformity_of_nhds_one_swapped`

English:
theorem Filter.HasBasis.uniformity_of_nhds_one_swapped
  statement: {ι} {p : ι -> Prop} {U : ι -> Set α}
  proof: by
  rw [uniformity_eq_comap_nhds_one_swapped]
  exact h.comap _

@[to_additive]

中文:
定理 滤子.有基.uniformity_of_nhds_one_swapped
  结论: {ι} {p : ι -> 命题} {U : ι -> 集合 α}
  证明: by
  rw [uniformity_eq_comap_nhds_one_swapped]
  exact h.comap _

@[to_additive]

Depends on / 依赖: h.comap, uniformity_eq_comap_nhds_one_swapped
-/
theorem Filter.HasBasis.uniformity_of_nhds_one_swapped {ι} {p : ι -> Prop} {U : ι -> Set α}
    (h : (𝓝 (1 : α)).HasBasis p U) :
    (𝓤 α).HasBasis p fun i => { x : α × α | x.1 / x.2 in U i } := by
  rw [uniformity_eq_comap_nhds_one_swapped]
  exact h.comap _

@[to_additive]
/--
theorem `Filter.HasBasis.uniformity_of_nhds_one_inv_mul_swapped` / 定理 `Filter.HasBasis.uniformity_of_nhds_one_inv_mul_swapped`

English:
theorem Filter.HasBasis.uniformity_of_nhds_one_inv_mul_swapped
  statement: {ι} {p : ι -> Prop} {U : ι -> Set α}
  proof: by
  rw [uniformity_eq_comap_inv_mul_nhds_one_swapped]
  exact h.comap _

@[to_additive]

中文:
定理 滤子.有基.uniformity_of_nhds_one_inv_mul_swapped
  结论: {ι} {p : ι -> 命题} {U : ι -> 集合 α}
  证明: by
  rw [uniformity_eq_comap_inv_mul_nhds_one_swapped]
  exact h.comap _

@[to_additive]

Depends on / 依赖: h.comap, uniformity_eq_comap_inv_mul_nhds_one_swapped
-/
theorem Filter.HasBasis.uniformity_of_nhds_one_inv_mul_swapped {ι} {p : ι -> Prop} {U : ι -> Set α}
    (h : (𝓝 (1 : α)).HasBasis p U) :
    (𝓤 α).HasBasis p fun i => { x : α × α | x.2⁻¹ * x.1 in U i } := by
  rw [uniformity_eq_comap_inv_mul_nhds_one_swapped]
  exact h.comap _

@[to_additive]
/--
theorem `uniformContinuous_of_tendsto_one` / 定理 `uniformContinuous_of_tendsto_one`

English:
theorem uniformContinuous_of_tendsto_one
  statement: {hom : Type*} [UniformSpace β] [Group β] [IsUniformGroup β]
  proof: by
  have :
    ((fun x : β × β => x.2 / x.1) ∘ fun x : α × α => (f x.1, f x.2)) = fun x : α × α =>
      f (x.2 / x.1) := by ext; simp only [Function.comp_apply, map_div]
  rw [UniformContinuous]; rw [uniformity_eq_comap_nhds_one α]; rw [uniformity_eq_comap_nhds_one β]; rw [tendsto_comap_iff]; rw [this]
  exact Tendsto.comp h tendsto_comap

中文:
定理 uniformContinuous_of_tendsto_one
  结论: {hom : 类型} [一致空间 β] [群 β] [是一致群 β]
  证明: by
  have :
    ((fun x : β × β => x.2 / x.1) ∘ fun x : α × α => (f x.1, f x.2)) = fun x : α × α =>
      f (x.2 / x.1) := by ext; simp only [Function.comp_apply, map_div]
  rw [UniformContinuous]; rw [uniformity_eq_comap_nhds_one α]; rw [uniformity_eq_comap_nhds_one β]; rw [tendsto_comap_iff]; rw [this]
  exact Tendsto.comp h tendsto_comap

Depends on / 依赖: Function, Function.comp_apply, Tendsto, Tendsto.comp, UniformContinuous, comp_apply, map_div, tendsto_comap, tendsto_comap_iff, uniformity_eq_comap_nhds_one
-/
theorem uniformContinuous_of_tendsto_one {hom : Type*} [UniformSpace β] [Group β] [IsUniformGroup β]
    [FunLike hom α β] [MonoidHomClass hom α β] {f : hom} (h : Tendsto f (𝓝 1) (𝓝 1)) :
    UniformContinuous f := by
  have :
    ((fun x : β × β => x.2 / x.1) ∘ fun x : α × α => (f x.1, f x.2)) = fun x : α × α =>
      f (x.2 / x.1) := by ext; simp only [Function.comp_apply, map_div]
  rw [UniformContinuous]; rw [uniformity_eq_comap_nhds_one α]; rw [uniformity_eq_comap_nhds_one β]; rw [tendsto_comap_iff]; rw [this]
  exact Tendsto.comp h tendsto_comap

/-- A group homomorphism (a bundled morphism of a type that implements `MonoidHomClass`) between
two uniform groups is uniformly continuous provided that it is continuous at one. See also
`continuous_of_continuousAt_one`. -/
@[to_additive /-- An additive group homomorphism (a bundled morphism of a type that implements
`AddMonoidHomClass`) between two uniform additive groups is uniformly continuous provided that it
is continuous at zero. See also `continuous_of_continuousAt_zero`. -/]
/--
theorem `uniformContinuous_of_continuousAt_one` / 定理 `uniformContinuous_of_continuousAt_one`

English:
theorem uniformContinuous_of_continuousAt_one
  statement: {hom : Type*} [UniformSpace β] [Group β]
  proof: uniformContinuous_of_tendsto_one (by simpa using hf.tendsto)

@[to_additive]

中文:
定理 uniformContinuous_of_continuousAt_one
  结论: {hom : 类型} [一致空间 β] [群 β]
  证明: uniformContinuous_of_tendsto_one (by simpa using hf.tendsto)

@[to_additive]

Depends on / 依赖: hf.tendsto, tendsto, uniformContinuous_of_tendsto_one
-/
theorem uniformContinuous_of_continuousAt_one {hom : Type*} [UniformSpace β] [Group β]
    [IsUniformGroup β] [FunLike hom α β] [MonoidHomClass hom α β]
    (f : hom) (hf : ContinuousAt f 1) :
    UniformContinuous f :=
  uniformContinuous_of_tendsto_one (by simpa using hf.tendsto)

@[to_additive]
/--
theorem `MonoidHom.uniformContinuous_of_continuousAt_one` / 定理 `MonoidHom.uniformContinuous_of_continuousAt_one`

English:
theorem MonoidHom.uniformContinuous_of_continuousAt_one
  statement: [UniformSpace β] [Group β]
  proof: _root_.uniformContinuous_of_continuousAt_one f hf

中文:
定理 幺半群态射.uniformContinuous_of_continuousAt_one
  结论: [一致空间 β] [群 β]
  证明: _root_.uniformContinuous_of_continuousAt_one f hf

Depends on / 依赖: _root_, _root_.uniformContinuous_of_continuousAt_one, uniformContinuous_of_continuousAt_one
-/
theorem MonoidHom.uniformContinuous_of_continuousAt_one [UniformSpace β] [Group β]
    [IsUniformGroup β] (f : α ->* β) (hf : ContinuousAt f 1) : UniformContinuous f :=
  _root_.uniformContinuous_of_continuousAt_one f hf

/-- A homomorphism from a uniform group to a discrete uniform group is continuous if and only if
its kernel is open. -/
@[to_additive /-- A homomorphism from a uniform additive group to a discrete uniform additive group
is continuous if and only if its kernel is open. -/]
/--
theorem `IsUniformGroup.uniformContinuous_iff_isOpen_ker` / 定理 `IsUniformGroup.uniformContinuous_iff_isOpen_ker`

English:
theorem IsUniformGroup.uniformContinuous_iff_isOpen_ker
  statement: {hom : Type*} [UniformSpace β]
  proof: by
  refine ⟨fun hf => ?_, fun hf => ?_⟩
  · apply (isOpen_discrete ({1} : Set β)).preimage hf.continuous
  · apply uniformContinuous_of_continuousAt_one
    rw [ContinuousAt]; rw [nhds_discrete β]; rw [map_one]; rw [tendsto_pure]
    exact hf.mem_nhds (map_one f)

@[to_additive]

中文:
定理 是一致群.uniformContinuous_iff_isOpen_ker
  结论: {hom : 类型} [一致空间 β]
  证明: by
  refine ⟨fun hf => ?_, fun hf => ?_⟩
  · apply (isOpen_discrete ({1} : Set β)).preimage hf.continuous
  · apply uniformContinuous_of_continuousAt_one
    rw [ContinuousAt]; rw [nhds_discrete β]; rw [map_one]; rw [tendsto_pure]
    exact hf.mem_nhds (map_one f)

@[to_additive]

Depends on / 依赖: ContinuousAt, continuous, hf.continuous, hf.mem_nhds, isOpen_discrete, map_one, mem_nhds, nhds_discrete, preimage, tendsto_pure, uniformContinuous_of_continuousAt_one
-/
theorem IsUniformGroup.uniformContinuous_iff_isOpen_ker {hom : Type*} [UniformSpace β]
    [DiscreteTopology β] [Group β] [IsUniformGroup β] [FunLike hom α β] [MonoidHomClass hom α β]
    {f : hom} :
    UniformContinuous f ↔ IsOpen ((f : α ->* β).ker : Set α) := by
  refine ⟨fun hf => ?_, fun hf => ?_⟩
  · apply (isOpen_discrete ({1} : Set β)).preimage hf.continuous
  · apply uniformContinuous_of_continuousAt_one
    rw [ContinuousAt]; rw [nhds_discrete β]; rw [map_one]; rw [tendsto_pure]
    exact hf.mem_nhds (map_one f)

@[to_additive]
/--
theorem `uniformContinuous_monoidHom_of_continuous` / 定理 `uniformContinuous_monoidHom_of_continuous`

English:
theorem uniformContinuous_monoidHom_of_continuous
  statement: {hom : Type*} [UniformSpace β] [Group β]
  proof: uniformContinuous_of_tendsto_one
    suffices Tendsto f (𝓝 1) (𝓝 (f 1)) by rwa [map_one] at this
    h.tendsto 1

@[to_additive]

中文:
定理 uniformContinuous_monoidHom_of_continuous
  结论: {hom : 类型} [一致空间 β] [群 β]
  证明: uniformContinuous_of_tendsto_one
    suffices Tendsto f (𝓝 1) (𝓝 (f 1)) by rwa [map_one] at this
    h.tendsto 1

@[to_additive]

Depends on / 依赖: Tendsto, h.tendsto, map_one, tendsto, uniformContinuous_of_tendsto_one
-/
theorem uniformContinuous_monoidHom_of_continuous {hom : Type*} [UniformSpace β] [Group β]
    [IsUniformGroup β] [FunLike hom α β] [MonoidHomClass hom α β] {f : hom} (h : Continuous f) :
    UniformContinuous f :=
uniformContinuous_of_tendsto_one
    suffices Tendsto f (𝓝 1) (𝓝 (f 1)) by rwa [map_one] at this
    h.tendsto 1

@[to_additive]
/--
theorem `MonoidHom.isUniformInducing_of_isInducing` / 定理 `MonoidHom.isUniformInducing_of_isInducing`

English:
theorem MonoidHom.isUniformInducing_of_isInducing
  statement: {Hom : Type*} [UniformSpace β] [Group β]
  proof: by
    simp [uniformity_eq_comap_nhds_one, comap_comap, Function.comp_def, h.nhds_eq_comap]

@[to_additive]

中文:
定理 幺半群态射.isUniformInducing_of_isInducing
  结论: {态射 : 类型} [一致空间 β] [群 β]
  证明: by
    simp [uniformity_eq_comap_nhds_one, comap_comap, Function.comp_def, h.nhds_eq_comap]

@[to_additive]

Depends on / 依赖: Function, Function.comp_def, comap_comap, comp_def, h.nhds_eq_comap, nhds_eq_comap, uniformity_eq_comap_nhds_one
-/
theorem MonoidHom.isUniformInducing_of_isInducing {Hom : Type*} [UniformSpace β] [Group β]
    [IsUniformGroup β] [FunLike Hom α β] [MonoidHomClass Hom α β] {f : Hom} (h : IsInducing f) :
    IsUniformInducing f where
  comap_uniformity := by
    simp [uniformity_eq_comap_nhds_one, comap_comap, Function.comp_def, h.nhds_eq_comap]

@[to_additive]
/--
theorem `MonoidHom.isUniformEmbedding_of_isEmbedding` / 定理 `MonoidHom.isUniformEmbedding_of_isEmbedding`

English:
theorem MonoidHom.isUniformEmbedding_of_isEmbedding
  statement: {Hom : Type*} [UniformSpace β] [Group β]
  proof: MonoidHom.isUniformInducing_of_isInducing h.isInducing
  injective := h.injective

中文:
定理 幺半群态射.isUniformEmbedding_of_isEmbedding
  结论: {态射 : 类型} [一致空间 β] [群 β]
  证明: MonoidHom.isUniformInducing_of_isInducing h.isInducing
  injective := h.injective

Depends on / 依赖: MonoidHom, MonoidHom.isUniformInducing_of_isInducing, h.isInducing, isInducing, isUniformInducing_of_isInducing
-/
theorem MonoidHom.isUniformEmbedding_of_isEmbedding {Hom : Type*} [UniformSpace β] [Group β]
    [IsUniformGroup β] [FunLike Hom α β] [MonoidHomClass Hom α β] {f : Hom} (h : IsEmbedding f) :
    IsUniformEmbedding f where
  toIsUniformInducing := MonoidHom.isUniformInducing_of_isInducing h.isInducing
  injective := h.injective

end IsUniformGroup

section IsTopologicalGroup

open Filter

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The right uniformity on a topological group (as opposed to the left uniformity).

Warning: in general the right and left uniformities do not coincide and so one does not obtain a
`IsUniformGroup` structure. Two important special cases where they _do_ coincide are for
commutative groups (see `isUniformGroup_of_commGroup`) and for compact groups (see
`IsUniformGroup.of_compactSpace`). -/
@[to_additive (attr := instance_reducible)
/-- The right uniformity on a topological additive group (as opposed to the left
uniformity).

Warning: in general the right and left uniformities do not coincide and so one does not obtain a
`IsUniformAddGroup` structure. Two important special cases where they _do_ coincide are for
commutative additive groups (see `isUniformAddGroup_of_addCommGroup`) and for compact
additive groups (see `IsUniformAddGroup.of_compactSpace`). -/]
/--
Definition of `IsTopologicalGroup.rightUniformSpace` / `IsTopologicalGroup.rightUniformSpace` 的定义

English:
definition IsTopologicalGroup.rightUniformSpace
  signature: : UniformSpace G where
  body: comap (fun p : G × G => p.2 * p.1⁻¹) (𝓝 1)
  symm :=
    have : Tendsto (fun p : G × G => (p.2 * p.1⁻¹)⁻¹) (comap (fun p : G × G => p.2 * p.1⁻¹) (𝓝 1))
      (𝓝 1⁻¹) := tendsto_id.inv.comp tendsto_comap
    by simpa [tendsto_comap_iff]
  comp := Tendsto.le_comap fun U H => by
    rcases exists_nhds_one_split H with ⟨V, V_nhds, V_mul⟩
    refine mem_map.2 (mem_of_superset (mem_lift' <| preimage_mem_comap V_nhds) ?_)
    rintro ⟨x, y⟩ ⟨z, hz₁, hz₂⟩
    simpa using V_mul _ hz₂ _ hz₁
  nhds_eq_comap_uniformity _ := by
    simp only [comap_comap, Function.comp_def, nhds_translation_mul_inv]

中文:
定义 是拓扑群.rightUniformSpace
  签名: : 一致空间 G where
  定义体: comap (fun p : G × G => p.2 * p.1⁻¹) (𝓝 1)
  symm :=
    have : Tendsto (fun p : G × G => (p.2 * p.1⁻¹)⁻¹) (comap (fun p : G × G => p.2 * p.1⁻¹) (𝓝 1))
      (𝓝 1⁻¹) := tendsto_id.inv.comp tendsto_comap
    by simpa [tendsto_comap_iff]
  comp := Tendsto.le_comap fun U H => by
    rcases exists_nhds_one_split H with ⟨V, V_nhds, V_mul⟩
    refine mem_map.2 (mem_of_superset (mem_lift' <| preimage_mem_comap V_nhds) ?_)
    rintro ⟨x, y⟩ ⟨z, hz₁, hz₂⟩
    simpa using V_mul _ hz₂ _ hz₁
  nhds_eq_comap_uniformity _ := by
    simp only [comap_comap, Function.comp_def, nhds_translation_mul_inv]
-/
def IsTopologicalGroup.rightUniformSpace : UniformSpace G where
  uniformity := comap (fun p : G × G => p.2 * p.1⁻¹) (𝓝 1)
  symm :=
    have : Tendsto (fun p : G × G => (p.2 * p.1⁻¹)⁻¹) (comap (fun p : G × G => p.2 * p.1⁻¹) (𝓝 1))
      (𝓝 1⁻¹) := tendsto_id.inv.comp tendsto_comap
    by simpa [tendsto_comap_iff]
  comp := Tendsto.le_comap fun U H => by
    rcases exists_nhds_one_split H with ⟨V, V_nhds, V_mul⟩
    refine mem_map.2 (mem_of_superset (mem_lift' <| preimage_mem_comap V_nhds) ?_)
    rintro ⟨x, y⟩ ⟨z, hz₁, hz₂⟩
    simpa using V_mul _ hz₂ _ hz₁
  nhds_eq_comap_uniformity _ := by
    simp only [comap_comap, Function.comp_def, nhds_translation_mul_inv]

attribute [local instance] IsTopologicalGroup.rightUniformSpace

@[to_additive]
/--
theorem `uniformity_eq_comap_nhds_one'` / 定理 `uniformity_eq_comap_nhds_one'`

English:
theorem uniformity_eq_comap_nhds_one'
  statement: 𝓤 G = comap (fun p : G × G => p.2 * p.1⁻¹) (𝓝 (1 : G))
  proof: rfl

中文:
定理 uniformity_eq_comap_nhds_one'
  结论: 𝓤 G = comap (fun p : G × G => p.2 * p.1⁻¹) (𝓝 (1 : G))
  证明: rfl
-/
theorem uniformity_eq_comap_nhds_one' : 𝓤 G = comap (fun p : G × G => p.2 * p.1⁻¹) (𝓝 (1 : G)) :=
  rfl

end IsTopologicalGroup


section IsTopologicalGroup

open Filter

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The left uniformity on a topological group (as opposed to the right uniformity).

Warning: in general the right and left uniformities do not coincide and so one does not obtain a
`IsUniformGroup` structure. Two important special cases where they _do_ coincide are for
commutative groups (see `isUniformGroup_of_commGroup`) and for compact groups (see
`IsUniformGroup.of_compactSpace`). -/
@[to_additive (attr := instance_reducible)
/-- The left uniformity on a topological additive group (as opposed to the right
uniformity).

Warning: in general the right and left uniformities do not coincide and so one does not obtain a
`IsUniformAddGroup` structure. Two important special cases where they _do_ coincide are for
commutative additive groups (see `isUniformAddGroup_of_addCommGroup`) and for compact
additive groups (see `IsUniformAddGroup.of_compactSpace`). -/]
/--
Definition of `IsTopologicalGroup.leftUniformSpace` / `IsTopologicalGroup.leftUniformSpace` 的定义

English:
definition IsTopologicalGroup.leftUniformSpace
  signature: : UniformSpace G where
  body: comap (fun p : G × G => p.1⁻¹ * p.2) (𝓝 1)
  symm :=
    have : Tendsto (fun p : G × G => (p.1⁻¹ * p.2)⁻¹) (comap (fun p : G × G => p.1⁻¹ * p.2) (𝓝 1))
      (𝓝 1⁻¹) := tendsto_id.inv.comp tendsto_comap
    by simpa [tendsto_comap_iff]
  comp := Tendsto.le_comap fun U H => by
    rcases exists_nhds_one_split H with ⟨V, V_nhds, V_mul⟩
    refine mem_map.2 (mem_of_superset (mem_lift' <| preimage_mem_comap V_nhds) ?_)
    rintro ⟨x, y⟩ ⟨z, hz₁, hz₂⟩
    simpa using V_mul _ hz₁ _ hz₂
  nhds_eq_comap_uniformity _ := by
    simp only [comap_comap, Function.comp_def, nhds_translation_inv_mul]

中文:
定义 是拓扑群.leftUniformSpace
  签名: : 一致空间 G where
  定义体: comap (fun p : G × G => p.1⁻¹ * p.2) (𝓝 1)
  symm :=
    have : Tendsto (fun p : G × G => (p.1⁻¹ * p.2)⁻¹) (comap (fun p : G × G => p.1⁻¹ * p.2) (𝓝 1))
      (𝓝 1⁻¹) := tendsto_id.inv.comp tendsto_comap
    by simpa [tendsto_comap_iff]
  comp := Tendsto.le_comap fun U H => by
    rcases exists_nhds_one_split H with ⟨V, V_nhds, V_mul⟩
    refine mem_map.2 (mem_of_superset (mem_lift' <| preimage_mem_comap V_nhds) ?_)
    rintro ⟨x, y⟩ ⟨z, hz₁, hz₂⟩
    simpa using V_mul _ hz₁ _ hz₂
  nhds_eq_comap_uniformity _ := by
    simp only [comap_comap, Function.comp_def, nhds_translation_inv_mul]
-/
def IsTopologicalGroup.leftUniformSpace : UniformSpace G where
  uniformity := comap (fun p : G × G => p.1⁻¹ * p.2) (𝓝 1)
  symm :=
    have : Tendsto (fun p : G × G => (p.1⁻¹ * p.2)⁻¹) (comap (fun p : G × G => p.1⁻¹ * p.2) (𝓝 1))
      (𝓝 1⁻¹) := tendsto_id.inv.comp tendsto_comap
    by simpa [tendsto_comap_iff]
  comp := Tendsto.le_comap fun U H => by
    rcases exists_nhds_one_split H with ⟨V, V_nhds, V_mul⟩
    refine mem_map.2 (mem_of_superset (mem_lift' <| preimage_mem_comap V_nhds) ?_)
    rintro ⟨x, y⟩ ⟨z, hz₁, hz₂⟩
    simpa using V_mul _ hz₁ _ hz₂
  nhds_eq_comap_uniformity _ := by
    simp only [comap_comap, Function.comp_def, nhds_translation_inv_mul]

attribute [local instance] IsTopologicalGroup.leftUniformSpace

@[to_additive]
/--
theorem `uniformity_eq_comap_nhds_one_left` / 定理 `uniformity_eq_comap_nhds_one_left`

English:
theorem uniformity_eq_comap_nhds_one_left
  proof: rfl

中文:
定理 uniformity_eq_comap_nhds_one_left
  证明: rfl
-/
theorem uniformity_eq_comap_nhds_one_left :
    𝓤 G = comap (fun p : G × G => p.1⁻¹ * p.2) (𝓝 (1 : G)) :=
  rfl

end IsTopologicalGroup

section TopologicalCommGroup

universe u v w x

open Filter

variable (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]

section

attribute [local instance] IsTopologicalGroup.rightUniformSpace

variable {G}

@[to_additive]
/--
theorem `isUniformGroup_of_commGroup` / 定理 `isUniformGroup_of_commGroup`

English:
theorem isUniformGroup_of_commGroup
  statement: IsUniformGroup G
  proof: by
  constructor
  have : (fun (x : (G × G) × (G × G)) => x.1.2 * x.2.2⁻¹ * (x.2.1 * x.1.1⁻¹)) =
    (fun (p : G × G) => p.1 * p.2⁻¹)
      ∘ (fun (p : (G × G) × (G × G)) => (p.1.2 * p.1.1⁻¹, p.2.2 * p.2.1⁻¹)) := by
    ext x
    simp only [Function.comp_apply, mul_inv_rev, inv_inv]
    rw [mul_assoc]; rw [mul_comm x.2.2⁻¹]; rw [mul_comm x.2.1]
    simp [mul_assoc]
  simp only [UniformContinuous, div_eq_mul_inv, uniformity_prod_eq_prod,
    uniformity_eq_comap_nhds_one', prod_comap_comap_eq, ← nhds_prod_eq, tendsto_comap_iff,
    Function.comp_def, mul_inv_rev, inv_inv, tendsto_map'_iff]
  rw [this]
  apply Tendsto.comp ?_ tendsto_comap
  nth_rewrite 3 [show (1 : G) = 1 * 1⁻¹ by simp]
  apply Continuous.tendsto (by fun_prop)

alias comm_topologicalGroup_is_uniform := isUniformGroup_of_commGroup

中文:
定理 isUniformGroup_of_commGroup
  结论: 是一致群 G
  证明: by
  constructor
  have : (fun (x : (G × G) × (G × G)) => x.1.2 * x.2.2⁻¹ * (x.2.1 * x.1.1⁻¹)) =
    (fun (p : G × G) => p.1 * p.2⁻¹)
      ∘ (fun (p : (G × G) × (G × G)) => (p.1.2 * p.1.1⁻¹, p.2.2 * p.2.1⁻¹)) := by
    ext x
    simp only [Function.comp_apply, mul_inv_rev, inv_inv]
    rw [mul_assoc]; rw [mul_comm x.2.2⁻¹]; rw [mul_comm x.2.1]
    simp [mul_assoc]
  simp only [UniformContinuous, div_eq_mul_inv, uniformity_prod_eq_prod,
    uniformity_eq_comap_nhds_one', prod_comap_comap_eq, ← nhds_prod_eq, tendsto_comap_iff,
    Function.comp_def, mul_inv_rev, inv_inv, tendsto_map'_iff]
  rw [this]
  apply Tendsto.comp ?_ tendsto_comap
  nth_rewrite 3 [show (1 : G) = 1 * 1⁻¹ by simp]
  apply Continuous.tendsto (by fun_prop)

alias comm_topologicalGroup_is_uniform := isUniformGroup_of_commGroup

Depends on / 依赖: Function, Function.comp_apply, UniformContinuous, comp_apply, div_eq_mul_inv, inv_inv, mul_assoc, mul_comm, mul_inv_rev, nhds_prod_eq, prod_comap_comap_eq, tendsto_comap_iff, uniformity_eq_comap_nhds_one, uniformity_prod_eq_prod
-/
theorem isUniformGroup_of_commGroup : IsUniformGroup G := by
  constructor
  have : (fun (x : (G × G) × (G × G)) => x.1.2 * x.2.2⁻¹ * (x.2.1 * x.1.1⁻¹)) =
    (fun (p : G × G) => p.1 * p.2⁻¹)
      ∘ (fun (p : (G × G) × (G × G)) => (p.1.2 * p.1.1⁻¹, p.2.2 * p.2.1⁻¹)) := by
    ext x
    simp only [Function.comp_apply, mul_inv_rev, inv_inv]
    rw [mul_assoc]; rw [mul_comm x.2.2⁻¹]; rw [mul_comm x.2.1]
    simp [mul_assoc]
  simp only [UniformContinuous, div_eq_mul_inv, uniformity_prod_eq_prod,
    uniformity_eq_comap_nhds_one', prod_comap_comap_eq, ← nhds_prod_eq, tendsto_comap_iff,
    Function.comp_def, mul_inv_rev, inv_inv, tendsto_map'_iff]
  rw [this]
  apply Tendsto.comp ?_ tendsto_comap
  nth_rewrite 3 [show (1 : G) = 1 * 1⁻¹ by simp]
  apply Continuous.tendsto (by fun_prop)

alias comm_topologicalGroup_is_uniform := isUniformGroup_of_commGroup

end

@[to_additive]
/--
theorem `IsUniformGroup.rightUniformSpace_eq` / 定理 `IsUniformGroup.rightUniformSpace_eq`

English:
theorem IsUniformGroup.rightUniformSpace_eq
  statement: {G : Type*} [u : UniformSpace G] [Group G]
  proof: by
  ext : 1
  rw [uniformity_eq_comap_nhds_one' G]; rw [uniformity_eq_comap_mul_inv_nhds_one]

中文:
定理 是一致群.rightUniformSpace_eq
  结论: {G : 类型} [u : 一致空间 G] [群 G]
  证明: by
  ext : 1
  rw [uniformity_eq_comap_nhds_one' G]; rw [uniformity_eq_comap_mul_inv_nhds_one]

Depends on / 依赖: uniformity_eq_comap_mul_inv_nhds_one, uniformity_eq_comap_nhds_one
-/
theorem IsUniformGroup.rightUniformSpace_eq {G : Type*} [u : UniformSpace G] [Group G]
    [IsUniformGroup G] : IsTopologicalGroup.rightUniformSpace G = u := by
  ext : 1
  rw [uniformity_eq_comap_nhds_one' G]; rw [uniformity_eq_comap_mul_inv_nhds_one]

end TopologicalCommGroup
