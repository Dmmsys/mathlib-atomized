/-
Copyright (c) 2020 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
module

public import Mathlib.Topology.Order.ProjIcc
public import Mathlib.Topology.CompactOpen
public import Mathlib.Topology.UnitInterval

/-!
# Paths in topological spaces

This file introduces continuous paths and provides API for them.

## Main definitions

In this file the unit interval `[0, 1]` in `ℝ` is denoted by `I`, and `X` is a topological space.

* `Path x y` is the type of paths from `x` to `y`, i.e., continuous maps from `I` to `X`
  mapping `0` to `x` and `1` to `y`.
* `Path.refl x : Path x x` is the constant path at `x`.
* `Path.symm γ : Path y x` is the reverse of a path `γ : Path x y`.
* `Path.trans γ γ' : Path x z` is the concatenation of two paths `γ : Path x y`, `γ' : Path y z`.
* `Path.map γ hf : Path (f x) (f y)` is the image of `γ : Path x y` under a continuous map `f`.
* `Path.reparam γ f hf hf₀ hf₁ : Path x y` is the reparametrisation of `γ : Path x y` by
  a continuous map `f : I → I` fixing `0` and `1`.
* `Path.truncate γ t₀ t₁ : Path (γ t₀) (γ t₁)` is the path that follows `γ` from `t₀` to `t₁` and
  stays constant otherwise.
* `Path.extend γ : C(ℝ, X)` is the extension `γ` to `ℝ` that is constant before `0` and after `1`.

`Path x y` is equipped with the topology induced by the compact-open topology on `C(I,X)`, and
several of the above constructions are shown to be continuous.

## Implementation notes

By default, all paths have `I` as their source and `X` as their target, but there is an
operation `Set.IccExtend` that will extend any continuous map `γ : I → X` into a continuous map
`IccExtend zero_le_one γ : ℝ → X` that is constant before `0` and after `1`.

This is used to define `Path.extend` that turns `γ : Path x y` into a continuous map
`γ.extend : ℝ → X` whose restriction to `I` is the original `γ`, and is equal to `x`
on `(-∞, 0]` and to `y` on `[1, +∞)`.
-/

@[expose] public section

noncomputable section

open Topology Filter unitInterval Set Function

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {x y z : X} {ι : Type*}

/-! ### Paths -/

/--
Definition of `Path` / `Path` 的定义

English:
structure Path
  parameters: (x y : X)
  extends: C(I, X)
  axioms and operations (2):
    - source' : toFun 0 = x
    - target' : toFun 1 = y

中文:
结构 道路
  参数: (x y : X)
  继承: C(I, X)
  公理与运算 (2 个):
    - source' : toFun 0 = x
    - target' : toFun 1 = y
-/
structure Path (x y : X) extends C(I, X) where
  /-- The start point of a `Path`. -/
  source' : toFun 0 = x
  /-- The end point of a `Path`. -/
  target' : toFun 1 = y

/--
Instance `Path.instFunLike` / 实例 `Path.instFunLike`

English:
instance Path.instFunLike
  signature: : FunLike (Path x y) I X where
  body: ⇑γ.toContinuousMap
  coe_injective γ₁ γ₂ h := by
    simp only [DFunLike.coe_fn_eq] at h
    cases γ₁; cases γ₂; congr

中文:
实例 道路.instFunLike
  签名: : 函数状 (道路 x y) I X where
  定义体: ⇑γ.toContinuousMap
  coe_injective γ₁ γ₂ h := by
    simp only [DFunLike.coe_fn_eq] at h
    cases γ₁; cases γ₂; congr

Depends on / 依赖: toContinuousMap
-/
instance Path.instFunLike : FunLike (Path x y) I X where
  coe γ := ⇑γ.toContinuousMap
  coe_injective γ₁ γ₂ h := by
    simp only [DFunLike.coe_fn_eq] at h
    cases γ₁; cases γ₂; congr

/--
Instance `Path.continuousMapClass` / 实例 `Path.continuousMapClass`

English:
instance Path.continuousMapClass
  signature: : ContinuousMapClass (Path x y) I X where
  body: show Continuous γ.toContinuousMap by fun_prop

@[ext, grind ext]

中文:
实例 道路.continuousMapClass
  签名: : 连续映射类 (道路 x y) I X where
  定义体: show Continuous γ.toContinuousMap by fun_prop

@[ext, grind ext]

Depends on / 依赖: Continuous, fun_prop, toContinuousMap
-/
instance Path.continuousMapClass : ContinuousMapClass (Path x y) I X where
  map_continuous γ := show Continuous γ.toContinuousMap by fun_prop

@[ext, grind ext]
/--
theorem `Path.ext` / 定理 `Path.ext`

English:
theorem Path.ext
  statement: forall {γ₁ γ₂ : Path x y}, (γ₁ : I -> X) = γ₂ -> γ₁ = γ₂
  proof: by
  rintro ⟨⟨x, h11⟩, h12, h13⟩ ⟨⟨x, h21⟩, h22, h23⟩ rfl
  rfl

中文:
定理 道路.ext
  结论: 对任意 {γ₁ γ₂ : 道路 x y}, (γ₁ : I -> X) = γ₂ -> γ₁ = γ₂
  证明: by
  rintro ⟨⟨x, h11⟩, h12, h13⟩ ⟨⟨x, h21⟩, h22, h23⟩ rfl
  rfl
-/
protected theorem Path.ext : forall {γ₁ γ₂ : Path x y}, (γ₁ : I -> X) = γ₂ -> γ₁ = γ₂ := by
  rintro ⟨⟨x, h11⟩, h12, h13⟩ ⟨⟨x, h21⟩, h22, h23⟩ rfl
  rfl

namespace Path

/-- A path constructed from a continuous map `f` has the same underlying function. -/
@[simp]
/--
theorem `coe_mk'` / 定理 `coe_mk'`

English:
theorem coe_mk'
  given: (f : C(I, X)) (h₁ h₂)
  statement: ⇑(mk f h₁ h₂ : Path x y) = f
  proof: rfl

中文:
定理 coe_mk'
  条件: (f : C(I, X)) (h₁ h₂)
  结论: ⇑(mk f h₁ h₂ : 道路 x y) = f
  证明: rfl
-/
theorem coe_mk' (f : C(I, X)) (h₁ h₂) : ⇑(mk f h₁ h₂ : Path x y) = f := rfl

/--
theorem `coe_mk_mk` / 定理 `coe_mk_mk`

English:
theorem coe_mk_mk
  given: (f : I -> X) (h₁) (h₂ : f 0 = x) (h₃ : f 1 = y)
  proof: rfl

中文:
定理 coe_mk_mk
  条件: (f : I -> X) (h₁) (h₂ : f 0 = x) (h₃ : f 1 = y)
  证明: rfl
-/
theorem coe_mk_mk (f : I -> X) (h₁) (h₂ : f 0 = x) (h₃ : f 1 = y) :
    ⇑(mk ⟨f, h₁⟩ h₂ h₃ : Path x y) = f :=
  rfl

variable (γ : Path x y)

@[continuity]
/--
theorem `continuous` / 定理 `continuous`

English:
theorem continuous
  statement: Continuous γ
  proof: γ.continuous_toFun

@[simp, grind =]

中文:
定理 continuous
  结论: 连续 γ
  证明: γ.continuous_toFun

@[simp, grind =]
-/
protected theorem continuous : Continuous γ :=
  γ.continuous_toFun

@[simp, grind =]
/--
theorem `source` / 定理 `source`

English:
theorem source
  statement: γ 0 = x
  proof: γ.source'

@[simp, grind =]

中文:
定理 source
  结论: γ 0 = x
  证明: γ.source'

@[simp, grind =]
-/
protected theorem source : γ 0 = x :=
  γ.source'

@[simp, grind =]
/--
theorem `target` / 定理 `target`

English:
theorem target
  statement: γ 1 = y
  proof: γ.target'

中文:
定理 target
  结论: γ 1 = y
  证明: γ.target'
-/
protected theorem target : γ 1 = y :=
  γ.target'

/--
Definition of `simps.apply` / `simps.apply` 的定义

English:
definition simps.apply
  signature: : I -> X
  body: γ

initialize_simps_projections Path (toFun -> simps.apply, -toContinuousMap)

@[simp]

中文:
定义 simps.apply
  签名: : I -> X
  定义体: γ

initialize_simps_projections Path (toFun -> simps.apply, -toContinuousMap)

@[simp]
-/
def simps.apply : I -> X :=
  γ

initialize_simps_projections Path (toFun -> simps.apply, -toContinuousMap)

@[simp]
/--
theorem `coe_toContinuousMap` / 定理 `coe_toContinuousMap`

English:
theorem coe_toContinuousMap
  statement: ⇑γ.toContinuousMap = γ
  proof: rfl

@[simp]

中文:
定理 coe_toContinuousMap
  结论: ⇑γ.toContinuousMap = γ
  证明: rfl

@[simp]
-/
theorem coe_toContinuousMap : ⇑γ.toContinuousMap = γ :=
  rfl

@[simp]
/--
theorem `range_coe` / 定理 `range_coe`

English:
theorem range_coe
  statement: range ((↑) : Path x y -> C(I, X)) = {f | f 0 = x ∧ f 1 = y}
  proof: Subset.antisymm (range_subset_iff.mpr fun γ => ⟨γ.source, γ.target⟩) fun f ⟨hf₀, hf₁⟩ =>
    ⟨⟨f, hf₀, hf₁⟩, rfl⟩

中文:
定理 range_coe
  结论: range ((↑) : 道路 x y -> C(I, X)) = {f | f 0 = x ∧ f 1 = y}
  证明: Subset.antisymm (range_subset_iff.mpr fun γ => ⟨γ.source, γ.target⟩) fun f ⟨hf₀, hf₁⟩ =>
    ⟨⟨f, hf₀, hf₁⟩, rfl⟩

Depends on / 依赖: Subset, Subset.antisymm, antisymm, range_subset_iff, range_subset_iff.mpr, source, target
-/
theorem range_coe : range ((↑) : Path x y -> C(I, X)) = {f | f 0 = x ∧ f 1 = y} :=
  Subset.antisymm (range_subset_iff.mpr fun γ => ⟨γ.source, γ.target⟩) fun f ⟨hf₀, hf₁⟩ =>
    ⟨⟨f, hf₀, hf₁⟩, rfl⟩

/--
Instance `instHasUncurryPath` / 实例 `instHasUncurryPath`

English:
instance instHasUncurryPath
  signature: {α : Type*} {x y : α -> X}
  body: ⟨fun φ p => φ p.1 p.2⟩

@[simp high, grind! .]

中文:
实例 instHasUncurryPath
  签名: {α : 类型} {x y : α -> X}
  定义体: ⟨fun φ p => φ p.1 p.2⟩

@[simp high, grind! .]
-/
instance instHasUncurryPath {α : Type*} {x y : α -> X} :
    HasUncurry (forall a : α, Path (x a) (y a)) (α × I) X :=
  ⟨fun φ p => φ p.1 p.2⟩

@[simp high, grind! .]
/--
lemma `source_mem_range` / 引理 `source_mem_range`

English:
lemma source_mem_range
  given: (γ : Path x y)
  statement: x in range ⇑γ
  proof: ⟨0, Path.source γ⟩

@[simp high, grind! .]

中文:
引理 source_mem_range
  条件: (γ : 道路 x y)
  结论: x in range ⇑γ
  证明: ⟨0, Path.source γ⟩

@[simp high, grind! .]

Depends on / 依赖: Path.source, source
-/
lemma source_mem_range (γ : Path x y) : x in range ⇑γ :=
  ⟨0, Path.source γ⟩

@[simp high, grind! .]
/--
lemma `target_mem_range` / 引理 `target_mem_range`

English:
lemma target_mem_range
  given: (γ : Path x y)
  statement: y in range ⇑γ
  proof: ⟨1, Path.target γ⟩

中文:
引理 target_mem_range
  条件: (γ : 道路 x y)
  结论: y in range ⇑γ
  证明: ⟨1, Path.target γ⟩

Depends on / 依赖: Path.target, target
-/
lemma target_mem_range (γ : Path x y) : y in range ⇑γ :=
  ⟨1, Path.target γ⟩

/-- The path 0 ⟶ 1 in `I` -/
@[simps!]
/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: : Path (0 : I) 1 where
  body: .id _
  source' := rfl
  target' := rfl

中文:
定义 id
  签名: : 道路 (0 : I) 1 where
  定义体: .id _
  source' := rfl
  target' := rfl
-/
protected def id : Path (0 : I) 1 where
  toContinuousMap := .id _
  source' := rfl
  target' := rfl

/-- The constant path from a point to itself -/
@[refl, simps! (attr := grind =)]
/--
Definition of `refl` / `refl` 的定义

English:
definition refl
  signature: (x : X)
  body: .const I x
  source' := rfl
  target' := rfl

@[simp]

中文:
定义 refl
  签名: (x : X)
  定义体: .const I x
  source' := rfl
  target' := rfl

@[simp]
-/
def refl (x : X) : Path x x where
  toContinuousMap := .const I x
  source' := rfl
  target' := rfl

@[simp]
/--
theorem `refl_range` / 定理 `refl_range`

English:
theorem refl_range
  given: {a : X}
  statement: range (Path.refl a) = {a}
  proof: range_const

中文:
定理 refl_range
  条件: {a : X}
  结论: range (道路.refl a) = {a}
  证明: range_const

Depends on / 依赖: range_const
-/
theorem refl_range {a : X} : range (Path.refl a) = {a} := range_const

/-- The reverse of a path from `x` to `y`, as a path from `y` to `x` -/
@[symm, simps (attr := grind =)]
/--
Definition of `symm` / `symm` 的定义

English:
definition symm
  signature: (γ : Path x y)
  body: γ ∘ σ
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by simp

@[simp]

中文:
定义 symm
  签名: (γ : 道路 x y)
  定义体: γ ∘ σ
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by simp

@[simp]
-/
def symm (γ : Path x y) : Path y x where
  toFun := γ ∘ σ
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by simp

@[simp]
/--
theorem `symm_symm` / 定理 `symm_symm`

English:
theorem symm_symm
  given: (γ : Path x y)
  statement: γ.symm.symm = γ
  proof: by grind

中文:
定理 symm_symm
  条件: (γ : 道路 x y)
  结论: γ.symm.symm = γ
  证明: by grind
-/
theorem symm_symm (γ : Path x y) : γ.symm.symm = γ := by grind

/--
theorem `symm_bijective` / 定理 `symm_bijective`

English:
theorem symm_bijective
  statement: Function.Bijective (Path.symm : Path x y -> Path y x)
  proof: Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

@[simp]

中文:
定理 symm_bijective
  结论: 函数.双射 (道路.symm : 道路 x y -> 道路 y x)
  证明: Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

@[simp]

Depends on / 依赖: Function, Function.bijective_iff_has_inverse.mpr, bijective_iff_has_inverse, symm_symm
-/
theorem symm_bijective : Function.Bijective (Path.symm : Path x y -> Path y x) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

@[simp]
/--
theorem `refl_symm` / 定理 `refl_symm`

English:
theorem refl_symm
  given: {a : X}
  statement: (Path.refl a).symm = Path.refl a
  proof: rfl

@[simp]

中文:
定理 refl_symm
  条件: {a : X}
  结论: (道路.refl a).symm = 道路.refl a
  证明: rfl

@[simp]
-/
theorem refl_symm {a : X} : (Path.refl a).symm = Path.refl a := rfl

@[simp]
/--
theorem `symm_range` / 定理 `symm_range`

English:
theorem symm_range
  given: {a b : X} (γ : Path a b)
  statement: range γ.symm = range γ
  proof: symm_involutive.surjective.range_comp γ

中文:
定理 symm_range
  条件: {a b : X} (γ : 道路 a b)
  结论: range γ.symm = range γ
  证明: symm_involutive.surjective.range_comp γ

Depends on / 依赖: range_comp, surjective, symm_involutive, symm_involutive.surjective.range_comp
-/
theorem symm_range {a b : X} (γ : Path a b) : range γ.symm = range γ :=
  symm_involutive.surjective.range_comp γ

/-! #### Space of paths -/


open ContinuousMap

/--
Instance `instTopologicalSpace` / 实例 `instTopologicalSpace`

English:
instance instTopologicalSpace
  signature: : TopologicalSpace (Path x y)
  body: TopologicalSpace.induced ((↑) : _ -> C(I, X)) ContinuousMap.compactOpen

中文:
实例 instTopologicalSpace
  签名: : 拓扑空间 (道路 x y)
  定义体: TopologicalSpace.induced ((↑) : _ -> C(I, X)) ContinuousMap.compactOpen

Depends on / 依赖: ContinuousMap, ContinuousMap.compactOpen, TopologicalSpace, TopologicalSpace.induced, compactOpen, induced
-/
instance instTopologicalSpace : TopologicalSpace (Path x y) :=
  TopologicalSpace.induced ((↑) : _ -> C(I, X)) ContinuousMap.compactOpen

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ContinuousEval (Path x y) I X
  body: .of_continuous_forget continuous_induced_dom

中文:
实例 :
  签名: 余ntinuousEval (道路 x y) I X
  定义体: .of_continuous_forget continuous_induced_dom

Depends on / 依赖: continuous_induced_dom, of_continuous_forget
-/
instance : ContinuousEval (Path x y) I X := .of_continuous_forget continuous_induced_dom

/--
theorem `continuous_uncurry_iff` / 定理 `continuous_uncurry_iff`

English:
theorem continuous_uncurry_iff
  given: {Y} [TopologicalSpace Y] {g : Y -> Path x y}
  proof: Iff.symm continuous_induced_rng.trans
    ⟨fun h => continuous_uncurry_of_continuous ⟨_, h⟩,
    continuous_of_continuous_uncurry (fun (y : Y) => ContinuousMap.mk (g y))⟩

中文:
定理 continuous_uncurry_iff
  条件: {Y} [拓扑空间 Y] {g : Y -> 道路 x y}
  证明: Iff.symm continuous_induced_rng.trans
    ⟨fun h => continuous_uncurry_of_continuous ⟨_, h⟩,
    continuous_of_continuous_uncurry (fun (y : Y) => ContinuousMap.mk (g y))⟩

Depends on / 依赖: ContinuousMap, ContinuousMap.mk, Iff.symm, continuous_induced_rng, continuous_induced_rng.trans, continuous_of_continuous_uncurry, continuous_uncurry_of_continuous
-/
theorem continuous_uncurry_iff {Y} [TopologicalSpace Y] {g : Y -> Path x y} :
    Continuous ↿g ↔ Continuous g :=
Iff.symm continuous_induced_rng.trans
    ⟨fun h => continuous_uncurry_of_continuous ⟨_, h⟩,
    continuous_of_continuous_uncurry (fun (y : Y) => ContinuousMap.mk (g y))⟩

/--
Definition of `extend` / `extend` 的定义

English:
definition extend
  signature: : C(Real, X) where
  body: IccExtend zero_le_one γ

中文:
定义 extend
  签名: : C(实数, X) where
  定义体: IccExtend zero_le_one γ

Depends on / 依赖: IccExtend, zero_le_one
-/
def extend : C(Real, X) where
  toFun := IccExtend zero_le_one γ

/-- See Note [continuity lemma statement]. -/
@[continuity, fun_prop]
/--
theorem `_root_.Continuous.pathExtend` / 定理 `_root_.Continuous.pathExtend`

English:
theorem _root_.Continuous.pathExtend
  statement: {γ : Y -> Path x y} {f : Y -> Real} (hγ : Continuous ↿γ)
  proof: Continuous.IccExtend hγ hf

中文:
定理 _root_.连续.pathExtend
  结论: {γ : Y -> 道路 x y} {f : Y -> 实数} (hγ : 连续 ↿γ)
  证明: Continuous.IccExtend hγ hf

Depends on / 依赖: Continuous, Continuous.IccExtend, IccExtend
-/
theorem _root_.Continuous.pathExtend {γ : Y -> Path x y} {f : Y -> Real} (hγ : Continuous ↿γ)
    (hf : Continuous f) : Continuous fun t => (γ t).extend (f t) :=
  Continuous.IccExtend hγ hf

/--
theorem `continuous_extend` / 定理 `continuous_extend`

English:
theorem continuous_extend
  statement: Continuous γ.extend
  proof: γ.continuous.Icc_extend'

中文:
定理 continuous_extend
  结论: 连续 γ.extend
  证明: γ.continuous.Icc_extend'

Depends on / 依赖: Icc_extend, continuous, continuous.Icc_extend
-/
theorem continuous_extend : Continuous γ.extend :=
  γ.continuous.Icc_extend'

/--
theorem `_root_.Filter.Tendsto.pathExtend` / 定理 `_root_.Filter.Tendsto.pathExtend`

English:
theorem _root_.Filter.Tendsto.pathExtend
  proof: Filter.Tendsto.IccExtend _ hγ

中文:
定理 _root_.滤子.收敛.pathExtend
  证明: Filter.Tendsto.IccExtend _ hγ

Depends on / 依赖: Filter, Filter.Tendsto.IccExtend, IccExtend, Tendsto
-/
theorem _root_.Filter.Tendsto.pathExtend
    {l r : Y -> X} {y : Y} {l₁ : Filter Real} {l₂ : Filter X} {γ : forall y, Path (l y) (r y)}
    (hγ : Tendsto ↿γ (𝓝 y ×ˢ l₁.map (projIcc 0 1 zero_le_one)) l₂) :
    Tendsto (↿fun x => ⇑(γ x).extend) (𝓝 y ×ˢ l₁) l₂ :=
  Filter.Tendsto.IccExtend _ hγ

/--
theorem `_root_.ContinuousAt.pathExtend` / 定理 `_root_.ContinuousAt.pathExtend`

English:
theorem _root_.ContinuousAt.pathExtend
  statement: {g : Y -> Real} {l r : Y -> X} (γ : forall y, Path (l y) (r y))
  proof: hγ.IccExtend (fun x => γ x) hg

@[simp, grind =]

中文:
定理 _root_.ContinuousAt.pathExtend
  结论: {g : Y -> 实数} {l r : Y -> X} (γ : 对任意 y, 道路 (l y) (r y))
  证明: hγ.IccExtend (fun x => γ x) hg

@[simp, grind =]

Depends on / 依赖: IccExtend
-/
theorem _root_.ContinuousAt.pathExtend {g : Y -> Real} {l r : Y -> X} (γ : forall y, Path (l y) (r y))
    {y : Y} (hγ : ContinuousAt ↿γ (y, projIcc 0 1 zero_le_one (g y))) (hg : ContinuousAt g y) :
    ContinuousAt (fun i => (γ i).extend (g i)) y :=
  hγ.IccExtend (fun x => γ x) hg

@[simp, grind =]
/--
theorem `extend_apply` / 定理 `extend_apply`

English:
theorem extend_apply
  statement: {a b : X} (γ : Path a b) {t : Real}
  proof: IccExtend_of_mem _ γ ht

中文:
定理 extend_apply
  结论: {a b : X} (γ : 道路 a b) {t : 实数}
  证明: IccExtend_of_mem _ γ ht

Depends on / 依赖: IccExtend_of_mem
-/
theorem extend_apply {a b : X} (γ : Path a b) {t : Real}
    (ht : t in (Icc 0 1 : Set Real)) : γ.extend t = γ ⟨t, ht⟩ :=
  IccExtend_of_mem _ γ ht

/--
theorem `extend_zero` / 定理 `extend_zero`

English:
theorem extend_zero
  statement: γ.extend 0 = x
  proof: by simp

中文:
定理 extend_zero
  结论: γ.extend 0 = x
  证明: by simp
-/
theorem extend_zero : γ.extend 0 = x := by simp

/--
theorem `extend_one` / 定理 `extend_one`

English:
theorem extend_one
  statement: γ.extend 1 = y
  proof: by simp

中文:
定理 extend_one
  结论: γ.extend 1 = y
  证明: by simp
-/
theorem extend_one : γ.extend 1 = y := by simp

/--
theorem `extend_extends'` / 定理 `extend_extends'`

English:
theorem extend_extends'
  given: {a b : X} (γ : Path a b) (t : (Icc 0 1 : Set Real))
  statement: γ.extend t = γ t
  proof: IccExtend_val _ γ t

@[simp]

中文:
定理 extend_extends'
  条件: {a b : X} (γ : 道路 a b) (t : (闭区间 0 1 : 集合 实数))
  结论: γ.extend t = γ t
  证明: IccExtend_val _ γ t

@[simp]

Depends on / 依赖: IccExtend_val
-/
theorem extend_extends' {a b : X} (γ : Path a b) (t : (Icc 0 1 : Set Real)) : γ.extend t = γ t :=
  IccExtend_val _ γ t

@[simp]
/--
theorem `extend_range` / 定理 `extend_range`

English:
theorem extend_range
  given: {a b : X} (γ : Path a b)
  proof: IccExtend_range _ γ

中文:
定理 extend_range
  条件: {a b : X} (γ : 道路 a b)
  证明: IccExtend_range _ γ

Depends on / 依赖: IccExtend_range
-/
theorem extend_range {a b : X} (γ : Path a b) :
    range γ.extend = range γ :=
  IccExtend_range _ γ

/--
theorem `image_extend_of_subset` / 定理 `image_extend_of_subset`

English:
theorem image_extend_of_subset
  given: (γ : Path x y) {s : Set Real} (h : I subseteq s)
  proof: (γ.extend_range ▸ image_subset_range _ _).antisymm range_subset_iff.mpr fun t =>
    ⟨t, h t.2, extend_extends' _ _⟩

中文:
定理 image_extend_of_subset
  条件: (γ : 道路 x y) {s : 集合 实数} (h : I subseteq s)
  证明: (γ.extend_range ▸ image_subset_range _ _).antisymm range_subset_iff.mpr fun t =>
    ⟨t, h t.2, extend_extends' _ _⟩

Depends on / 依赖: antisymm, extend_extends, extend_range, image_subset_range, range_subset_iff, range_subset_iff.mpr
-/
theorem image_extend_of_subset (γ : Path x y) {s : Set Real} (h : I subseteq s) :
    γ.extend '' s = range γ :=
(γ.extend_range ▸ image_subset_range _ _).antisymm range_subset_iff.mpr fun t =>
    ⟨t, h t.2, extend_extends' _ _⟩

/--
theorem `extend_of_le_zero` / 定理 `extend_of_le_zero`

English:
theorem extend_of_le_zero
  statement: {a b : X} (γ : Path a b) {t : Real}
  proof: (IccExtend_of_le_left _ _ ht).trans γ.source

中文:
定理 extend_of_le_zero
  结论: {a b : X} (γ : 道路 a b) {t : 实数}
  证明: (IccExtend_of_le_left _ _ ht).trans γ.source

Depends on / 依赖: IccExtend_of_le_left, source
-/
theorem extend_of_le_zero {a b : X} (γ : Path a b) {t : Real}
    (ht : t <= 0) : γ.extend t = a :=
  (IccExtend_of_le_left _ _ ht).trans γ.source

/--
theorem `extend_of_one_le` / 定理 `extend_of_one_le`

English:
theorem extend_of_one_le
  statement: {a b : X} (γ : Path a b) {t : Real}
  proof: (IccExtend_of_right_le _ _ ht).trans γ.target

@[simp]

中文:
定理 extend_of_one_le
  结论: {a b : X} (γ : 道路 a b) {t : 实数}
  证明: (IccExtend_of_right_le _ _ ht).trans γ.target

@[simp]

Depends on / 依赖: IccExtend_of_right_le, target
-/
theorem extend_of_one_le {a b : X} (γ : Path a b) {t : Real}
    (ht : 1 <= t) : γ.extend t = b :=
  (IccExtend_of_right_le _ _ ht).trans γ.target

@[simp]
/--
theorem `refl_extend` / 定理 `refl_extend`

English:
theorem refl_extend
  given: {a : X}
  statement: (Path.refl a).extend = .const Real a
  proof: rfl

中文:
定理 refl_extend
  条件: {a : X}
  结论: (道路.refl a).extend = .const 实数 a
  证明: rfl
-/
theorem refl_extend {a : X} : (Path.refl a).extend = .const Real a :=
  rfl

/--
theorem `extend_symm_apply` / 定理 `extend_symm_apply`

English:
theorem extend_symm_apply
  given: (γ : Path x y) (t : Real)
  statement: γ.symm.extend t = γ.extend (1 - t)
  proof: congrArg γ symm_projIcc _

@[simp]

中文:
定理 extend_symm_apply
  条件: (γ : 道路 x y) (t : 实数)
  结论: γ.symm.extend t = γ.extend (1 - t)
  证明: congrArg γ symm_projIcc _

@[simp]

Depends on / 依赖: symm_projIcc
-/
theorem extend_symm_apply (γ : Path x y) (t : Real) : γ.symm.extend t = γ.extend (1 - t) :=
congrArg γ symm_projIcc _

@[simp]
/--
theorem `extend_symm` / 定理 `extend_symm`

English:
theorem extend_symm
  given: (γ : Path x y)
  statement: γ.symm.extend = (γ.extend <| 1 - ·)
  proof: funext γ.extend_symm_apply

中文:
定理 extend_symm
  条件: (γ : 道路 x y)
  结论: γ.symm.extend = (γ.extend <| 1 - ·)
  证明: funext γ.extend_symm_apply

Depends on / 依赖: extend_symm_apply
-/
theorem extend_symm (γ : Path x y) : γ.symm.extend = (γ.extend <| 1 - ·) :=
  funext γ.extend_symm_apply

/--
Definition of `ofLine` / `ofLine` 的定义

English:
definition ofLine
  signature: {f : Real -> X} (hf : ContinuousOn f I) (h₀ : f 0 = x) (h₁ : f 1 = y)
  body: f ∘ ((↑) : unitInterval -> Real)
  continuous_toFun := hf.comp_continuous continuous_subtype_val Subtype.prop
  source' := h₀
  target' := h₁

中文:
定义 ofLine
  签名: {f : 实数 -> X} (hf : ContinuousOn f I) (h₀ : f 0 = x) (h₁ : f 1 = y)
  定义体: f ∘ ((↑) : unitInterval -> Real)
  continuous_toFun := hf.comp_continuous continuous_subtype_val Subtype.prop
  source' := h₀
  target' := h₁

Depends on / 依赖: unitInterval
-/
def ofLine {f : Real -> X} (hf : ContinuousOn f I) (h₀ : f 0 = x) (h₁ : f 1 = y) : Path x y where
  toFun := f ∘ ((↑) : unitInterval -> Real)
  continuous_toFun := hf.comp_continuous continuous_subtype_val Subtype.prop
  source' := h₀
  target' := h₁

/--
theorem `ofLine_mem` / 定理 `ofLine_mem`

English:
theorem ofLine_mem
  given: {f : Real -> X} (hf : ContinuousOn f I) (h₀ : f 0 = x) (h₁ : f 1 = y)
  proof: fun ⟨t, t_in⟩ => ⟨t, t_in, rfl⟩

@[simp]

中文:
定理 ofLine_mem
  条件: {f : 实数 -> X} (hf : ContinuousOn f I) (h₀ : f 0 = x) (h₁ : f 1 = y)
  证明: fun ⟨t, t_in⟩ => ⟨t, t_in, rfl⟩

@[simp]

Depends on / 依赖: t_in
-/
theorem ofLine_mem {f : Real -> X} (hf : ContinuousOn f I) (h₀ : f 0 = x) (h₁ : f 1 = y) :
    forall t, ofLine hf h₀ h₁ t in f '' I := fun ⟨t, t_in⟩ => ⟨t, t_in, rfl⟩

@[simp]
/--
theorem `ofLine_extend` / 定理 `ofLine_extend`

English:
theorem ofLine_extend
  given: (γ : Path x y)
  statement: ofLine (by fun_prop) (extend_zero γ) (extend_one γ) = γ
  proof: by
  ext t
  simp [ofLine]

中文:
定理 ofLine_extend
  条件: (γ : 道路 x y)
  结论: ofLine (by fun_prop) (extend_zero γ) (extend_one γ) = γ
  证明: by
  ext t
  simp [ofLine]

Depends on / 依赖: ofLine
-/
theorem ofLine_extend (γ : Path x y) : ofLine (by fun_prop) (extend_zero γ) (extend_one γ) = γ := by
  ext t
  simp [ofLine]

attribute [local simp] Iic_def

/-- Concatenation of two paths from `x` to `y` and from `y` to `z`, putting the first
path on `[0, 1/2]` and the second one on `[1/2, 1]`. -/
@[trans]
/--
Definition of `trans` / `trans` 的定义

English:
definition trans
  signature: (γ : Path x y) (γ' : Path y z)
  body: (fun t : Real => if t <= 1 / 2 then γ.extend (2 * t) else γ'.extend (2 * t - 1)) ∘ (↑)
  continuous_toFun := by
    refine
      (Continuous.if_le ?_ ?_ continuous_id continuous_const (by simp)).comp
        continuous_subtype_val <;>
    fun_prop
  source' := by simp
  target' := by norm_num

@[gri

中文:
定义 trans
  签名: (γ : 道路 x y) (γ' : 道路 y z)
  定义体: (fun t : Real => if t <= 1 / 2 then γ.extend (2 * t) else γ'.extend (2 * t - 1)) ∘ (↑)
  continuous_toFun := by
    refine
      (Continuous.if_le ?_ ?_ continuous_id continuous_const (by simp)).comp
        continuous_subtype_val <;>
    fun_prop
  source' := by simp
  target' := by norm_num

@[gri

Depends on / 依赖: extend
-/
def trans (γ : Path x y) (γ' : Path y z) : Path x z where
  toFun := (fun t : Real => if t <= 1 / 2 then γ.extend (2 * t) else γ'.extend (2 * t - 1)) ∘ (↑)
  continuous_toFun := by
    refine
      (Continuous.if_le ?_ ?_ continuous_id continuous_const (by simp)).comp
        continuous_subtype_val <;>
    fun_prop
  source' := by simp
  target' := by norm_num

@[grind =]
/--
theorem `trans_apply` / 定理 `trans_apply`

English:
theorem trans_apply
  given: (γ : Path x y) (γ' : Path y z) (t : I)
  proof: show ite _ _ _ = _ by split_ifs <;> rw [extend_apply]

@[simp]

中文:
定理 trans_apply
  条件: (γ : 道路 x y) (γ' : 道路 y z) (t : I)
  证明: show ite _ _ _ = _ by split_ifs <;> rw [extend_apply]

@[simp]

Depends on / 依赖: extend_apply, split_ifs
-/
theorem trans_apply (γ : Path x y) (γ' : Path y z) (t : I) :
    (γ.trans γ') t =
      if h : (t : Real) <= 1 / 2 then γ ⟨2 * t, (mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, h⟩⟩
      else γ' ⟨2 * t - 1, two_mul_sub_one_mem_iff.2 ⟨(not_le.1 h).le, t.2.2⟩⟩ :=
  show ite _ _ _ = _ by split_ifs <;> rw [extend_apply]

@[simp]
/--
theorem `trans_symm` / 定理 `trans_symm`

English:
theorem trans_symm
  given: (γ : Path x y) (γ' : Path y z)
  statement: (γ.trans γ').symm = γ'.symm.trans γ.symm
  proof: by
  ext t
  simp only [trans_apply, symm_apply, Function.comp_apply]
  split_ifs with h h₁ h₂ <;> rw [coe_symm_eq] at h
  · have ht : (t : Real) = 1 / 2 := by linarith
    norm_num [ht]
  · refine congr_arg _ (Subtype.ext ?_)
    norm_num [sub_sub_eq_add_sub, mul_sub]
  · refine congr_arg _ (Subtyp

中文:
定理 trans_symm
  条件: (γ : 道路 x y) (γ' : 道路 y z)
  结论: (γ.trans γ').symm = γ'.symm.trans γ.symm
  证明: by
  ext t
  simp only [trans_apply, symm_apply, Function.comp_apply]
  split_ifs with h h₁ h₂ <;> rw [coe_symm_eq] at h
  · have ht : (t : Real) = 1 / 2 := by linarith
    norm_num [ht]
  · refine congr_arg _ (Subtype.ext ?_)
    norm_num [sub_sub_eq_add_sub, mul_sub]
  · refine congr_arg _ (Subtyp

Depends on / 依赖: Function, Function.comp_apply, Subtype, Subtype.ext, coe_symm_eq, comp_apply, congr_arg, mul_sub, split_ifs, sub_sub_eq_add_sub, symm_apply, trans_apply
-/
theorem trans_symm (γ : Path x y) (γ' : Path y z) : (γ.trans γ').symm = γ'.symm.trans γ.symm := by
  ext t
  simp only [trans_apply, symm_apply, Function.comp_apply]
  split_ifs with h h₁ h₂ <;> rw [coe_symm_eq] at h
  · have ht : (t : Real) = 1 / 2 := by linarith
    norm_num [ht]
  · refine congr_arg _ (Subtype.ext ?_)
    norm_num [sub_sub_eq_add_sub, mul_sub]
  · refine congr_arg _ (Subtype.ext ?_)
    simp only [coe_symm_eq]
    ring
  · exfalso
    linarith

/--
theorem `extend_trans_of_le_half` / 定理 `extend_trans_of_le_half`

English:
theorem extend_trans_of_le_half
  given: (γ₁ : Path x y) (γ₂ : Path y z) {t : Real} (ht : t <= 1 / 2)
  proof: by
  obtain _ | ht₀ := le_total t 0
  · repeat rw [extend_of_le_zero _ (by linarith)]
  · rwa [extend_apply _ ⟨ht₀, by linarith⟩, trans_apply, dif_pos, extend_apply]

中文:
定理 extend_trans_of_le_half
  条件: (γ₁ : 道路 x y) (γ₂ : 道路 y z) {t : 实数} (ht : t <= 1 / 2)
  证明: by
  obtain _ | ht₀ := le_total t 0
  · repeat rw [extend_of_le_zero _ (by linarith)]
  · rwa [extend_apply _ ⟨ht₀, by linarith⟩, trans_apply, dif_pos, extend_apply]

Depends on / 依赖: dif_pos, extend_apply, extend_of_le_zero, le_total, repeat, trans_apply
-/
theorem extend_trans_of_le_half (γ₁ : Path x y) (γ₂ : Path y z) {t : Real} (ht : t <= 1 / 2) :
    (γ₁.trans γ₂).extend t = γ₁.extend (2 * t) := by
  obtain _ | ht₀ := le_total t 0
  · repeat rw [extend_of_le_zero _ (by linarith)]
  · rwa [extend_apply _ ⟨ht₀, by linarith⟩, trans_apply, dif_pos, extend_apply]

/--
theorem `extend_trans_of_half_le` / 定理 `extend_trans_of_half_le`

English:
theorem extend_trans_of_half_le
  given: (γ₁ : Path x y) (γ₂ : Path y z) {t : Real} (ht : 1 / 2 <= t)
  proof: by
  conv_lhs => rw [← sub_sub_cancel 1 t]
  rw [← extend_symm_apply]; rw [trans_symm]; rw [extend_trans_of_le_half _ _ (by linarith)]; rw [extend_symm_apply]
  congr 1
  linarith

@[simp]

中文:
定理 extend_trans_of_half_le
  条件: (γ₁ : 道路 x y) (γ₂ : 道路 y z) {t : 实数} (ht : 1 / 2 <= t)
  证明: by
  conv_lhs => rw [← sub_sub_cancel 1 t]
  rw [← extend_symm_apply]; rw [trans_symm]; rw [extend_trans_of_le_half _ _ (by linarith)]; rw [extend_symm_apply]
  congr 1
  linarith

@[simp]

Depends on / 依赖: conv_lhs, extend_symm_apply, extend_trans_of_le_half, sub_sub_cancel, trans_symm
-/
theorem extend_trans_of_half_le (γ₁ : Path x y) (γ₂ : Path y z) {t : Real} (ht : 1 / 2 <= t) :
    (γ₁.trans γ₂).extend t = γ₂.extend (2 * t - 1) := by
  conv_lhs => rw [← sub_sub_cancel 1 t]
  rw [← extend_symm_apply]; rw [trans_symm]; rw [extend_trans_of_le_half _ _ (by linarith)]; rw [extend_symm_apply]
  congr 1
  linarith

@[simp]
/--
theorem `refl_trans_refl` / 定理 `refl_trans_refl`

English:
theorem refl_trans_refl
  given: {a : X}
  proof: by
  ext
  simp [Path.trans]

中文:
定理 refl_trans_refl
  条件: {a : X}
  证明: by
  ext
  simp [Path.trans]

Depends on / 依赖: Path.trans
-/
theorem refl_trans_refl {a : X} :
    (Path.refl a).trans (Path.refl a) = Path.refl a := by
  ext
  simp [Path.trans]

/--
theorem `trans_range` / 定理 `trans_range`

English:
theorem trans_range
  given: {a b c : X} (γ₁ : Path a b) (γ₂ : Path b c)
  proof: by
  rw [← extend_range]; rw [← image_univ]; rw [← Iic_union_Ici (a := 1 / 2)]; rw [image_union]; rw [EqOn.image_eq fun t ht => extend_trans_of_le_half _ _ (mem_Iic.1 ht)]; rw [EqOn.image_eq fun t ht => extend_trans_of_half_le _ _ (mem_Ici.1 ht)]; rw [← image_image γ₁.extend]; rw [← image_image (γ₂.

中文:
定理 trans_range
  条件: {a b c : X} (γ₁ : 道路 a b) (γ₂ : 道路 b c)
  证明: by
  rw [← extend_range]; rw [← image_univ]; rw [← Iic_union_Ici (a := 1 / 2)]; rw [image_union]; rw [EqOn.image_eq fun t ht => extend_trans_of_le_half _ _ (mem_Iic.1 ht)]; rw [EqOn.image_eq fun t ht => extend_trans_of_half_le _ _ (mem_Ici.1 ht)]; rw [← image_image γ₁.extend]; rw [← image_image (γ₂.

Depends on / 依赖: EqOn.image_eq, Icc_subset_Ici_self, Icc_subset_Iic_self, Iic_union_Ici, extend, extend_range, extend_trans_of_half_le, extend_trans_of_le_half, image_eq, image_extend_of_subset, image_image, image_mul_left_Ici, image_mul_left_Iic, image_union, image_univ, mem_Ici, mem_Iic
-/
theorem trans_range {a b c : X} (γ₁ : Path a b) (γ₂ : Path b c) :
    range (γ₁.trans γ₂) = range γ₁ union range γ₂ := by
  rw [← extend_range]; rw [← image_univ]; rw [← Iic_union_Ici (a := 1 / 2)]; rw [image_union]; rw [EqOn.image_eq fun t ht => extend_trans_of_le_half _ _ (mem_Iic.1 ht)]; rw [EqOn.image_eq fun t ht => extend_trans_of_half_le _ _ (mem_Ici.1 ht)]; rw [← image_image γ₁.extend]; rw [← image_image (γ₂.extend <| · - 1)]; rw [← image_image γ₂.extend]
  norm_num [image_mul_left_Ici, image_mul_left_Iic,
    image_extend_of_subset, Icc_subset_Iic_self, Icc_subset_Ici_self]

/--
Definition of `map'` / `map'` 的定义

English:
definition map'
  signature: (γ : Path x y) {f : X -> Y} (h : ContinuousOn f (range γ))
  body: f ∘ γ
  continuous_toFun := h.comp_continuous γ.continuous (fun x => mem_range_self x)
  source' := by simp
  target' := by simp

中文:
定义 map'
  签名: (γ : 道路 x y) {f : X -> Y} (h : ContinuousOn f (range γ))
  定义体: f ∘ γ
  continuous_toFun := h.comp_continuous γ.continuous (fun x => mem_range_self x)
  source' := by simp
  target' := by simp
-/
def map' (γ : Path x y) {f : X -> Y} (h : ContinuousOn f (range γ)) : Path (f x) (f y) where
  toFun := f ∘ γ
  continuous_toFun := h.comp_continuous γ.continuous (fun x => mem_range_self x)
  source' := by simp
  target' := by simp

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (γ : Path x y) {f : X -> Y} (h : Continuous f)
  body: γ.map' h.continuousOn

@[simp, grind =]

中文:
定义 map
  签名: (γ : 道路 x y) {f : X -> Y} (h : 连续 f)
  定义体: γ.map' h.continuousOn

@[simp, grind =]

Depends on / 依赖: continuousOn, h.continuousOn
-/
def map (γ : Path x y) {f : X -> Y} (h : Continuous f) :
    Path (f x) (f y) := γ.map' h.continuousOn

@[simp, grind =]
/--
theorem `map_coe` / 定理 `map_coe`

English:
theorem map_coe
  given: (γ : Path x y) {f : X -> Y} (h : Continuous f)
  proof: by
  ext t
  rfl

@[simp]

中文:
定理 map_coe
  条件: (γ : 道路 x y) {f : X -> Y} (h : 连续 f)
  证明: by
  ext t
  rfl

@[simp]
-/
theorem map_coe (γ : Path x y) {f : X -> Y} (h : Continuous f) :
    (γ.map h : I -> Y) = f ∘ γ := by
  ext t
  rfl

@[simp]
/--
theorem `map_symm` / 定理 `map_symm`

English:
theorem map_symm
  given: (γ : Path x y) {f : X -> Y} (h : Continuous f)
  proof: rfl

@[simp]

中文:
定理 map_symm
  条件: (γ : 道路 x y) {f : X -> Y} (h : 连续 f)
  证明: rfl

@[simp]
-/
theorem map_symm (γ : Path x y) {f : X -> Y} (h : Continuous f) :
    (γ.map h).symm = γ.symm.map h :=
  rfl

@[simp]
/--
theorem `map_trans` / 定理 `map_trans`

English:
theorem map_trans
  statement: (γ : Path x y) (γ' : Path y z) {f : X -> Y}
  proof: by
  ext t
  rw [trans_apply]; rw [map_coe]; rw [Function.comp_apply]; rw [trans_apply]; rw [map_coe]; rw [map_coe]
  grind

@[simp]

中文:
定理 map_trans
  结论: (γ : 道路 x y) (γ' : 道路 y z) {f : X -> Y}
  证明: by
  ext t
  rw [trans_apply]; rw [map_coe]; rw [Function.comp_apply]; rw [trans_apply]; rw [map_coe]; rw [map_coe]
  grind

@[simp]

Depends on / 依赖: Function, Function.comp_apply, comp_apply, map_coe, trans_apply
-/
theorem map_trans (γ : Path x y) (γ' : Path y z) {f : X -> Y}
    (h : Continuous f) : (γ.trans γ').map h = (γ.map h).trans (γ'.map h) := by
  ext t
  rw [trans_apply]; rw [map_coe]; rw [Function.comp_apply]; rw [trans_apply]; rw [map_coe]; rw [map_coe]
  grind

@[simp]
/--
theorem `map_id` / 定理 `map_id`

English:
theorem map_id
  given: (γ : Path x y)
  statement: γ.map continuous_id = γ
  proof: by
  ext
  rfl

@[simp]

中文:
定理 map_id
  条件: (γ : 道路 x y)
  结论: γ.map continuous_id = γ
  证明: by
  ext
  rfl

@[simp]
-/
theorem map_id (γ : Path x y) : γ.map continuous_id = γ := by
  ext
  rfl

@[simp]
/--
theorem `map_map` / 定理 `map_map`

English:
theorem map_map
  statement: (γ : Path x y) {Z : Type*} [TopologicalSpace Z]
  proof: by
  ext
  rfl

中文:
定理 map_map
  结论: (γ : 道路 x y) {Z : 类型} [拓扑空间 Z]
  证明: by
  ext
  rfl
-/
theorem map_map (γ : Path x y) {Z : Type*} [TopologicalSpace Z]
    {f : X -> Y} (hf : Continuous f) {g : Y -> Z} (hg : Continuous g) :
    (γ.map hf).map hg = γ.map (hg.comp hf) := by
  ext
  rfl

/--
Definition of `cast` / `cast` 的定义

English:
definition cast
  signature: (γ : Path x y) {x' y'} (hx : x' = x) (hy : y' = y)
  body: γ
  continuous_toFun := γ.continuous
  source' := by simp [hx]
  target' := by simp [hy]

中文:
定义 cast
  签名: (γ : 道路 x y) {x' y'} (hx : x' = x) (hy : y' = y)
  定义体: γ
  continuous_toFun := γ.continuous
  source' := by simp [hx]
  target' := by simp [hy]
-/
def cast (γ : Path x y) {x' y'} (hx : x' = x) (hy : y' = y) : Path x' y' where
  toFun := γ
  continuous_toFun := γ.continuous
  source' := by simp [hx]
  target' := by simp [hy]

/--
theorem `cast_rfl_rfl` / 定理 `cast_rfl_rfl`

English:
theorem cast_rfl_rfl
  given: (γ : Path x y)
  statement: γ.cast rfl rfl = γ
  proof: rfl

@[simp]

中文:
定理 cast_rfl_rfl
  条件: (γ : 道路 x y)
  结论: γ.cast rfl rfl = γ
  证明: rfl

@[simp]
-/
@[simp] theorem cast_rfl_rfl (γ : Path x y) : γ.cast rfl rfl = γ := rfl

@[simp]
/--
theorem `cast_symm` / 定理 `cast_symm`

English:
theorem cast_symm
  given: {a₁ a₂ b₁ b₂ : X} (γ : Path a₂ b₂) (ha : a₁ = a₂) (hb : b₁ = b₂)
  proof: rfl

@[simp]

中文:
定理 cast_symm
  条件: {a₁ a₂ b₁ b₂ : X} (γ : 道路 a₂ b₂) (ha : a₁ = a₂) (hb : b₁ = b₂)
  证明: rfl

@[simp]
-/
theorem cast_symm {a₁ a₂ b₁ b₂ : X} (γ : Path a₂ b₂) (ha : a₁ = a₂) (hb : b₁ = b₂) :
    (γ.symm).cast hb ha = (γ.cast ha hb).symm :=
  rfl

@[simp]
/--
theorem `cast_trans` / 定理 `cast_trans`

English:
theorem cast_trans
  statement: {a₁ a₂ b₁ b₂ c₁ c₂ : X} (γ : Path a₂ b₂)
  proof: rfl

@[simp]

中文:
定理 cast_trans
  结论: {a₁ a₂ b₁ b₂ c₁ c₂ : X} (γ : 道路 a₂ b₂)
  证明: rfl

@[simp]
-/
theorem cast_trans {a₁ a₂ b₁ b₂ c₁ c₂ : X} (γ : Path a₂ b₂)
    (γ' : Path b₂ c₂) (ha : a₁ = a₂) (hb : b₁ = b₂) (hc : c₁ = c₂) :
    (γ.trans γ').cast ha hc = (γ.cast ha hb).trans (γ'.cast hb hc) :=
  rfl

@[simp]
/--
theorem `extend_cast` / 定理 `extend_cast`

English:
theorem extend_cast
  given: {x' y'} (γ : Path x y) (hx : x' = x) (hy : y' = y)
  proof: rfl

@[simp]

中文:
定理 extend_cast
  条件: {x' y'} (γ : 道路 x y) (hx : x' = x) (hy : y' = y)
  证明: rfl

@[simp]
-/
theorem extend_cast {x' y'} (γ : Path x y) (hx : x' = x) (hy : y' = y) :
    (γ.cast hx hy).extend = γ.extend := rfl

@[simp]
/--
theorem `cast_coe` / 定理 `cast_coe`

English:
theorem cast_coe
  given: (γ : Path x y) {x' y'} (hx : x' = x) (hy : y' = y)
  statement: (γ.cast hx hy : I -> X) = γ
  proof: rfl

中文:
定理 cast_coe
  条件: (γ : 道路 x y) {x' y'} (hx : x' = x) (hy : y' = y)
  结论: (γ.cast hx hy : I -> X) = γ
  证明: rfl
-/
theorem cast_coe (γ : Path x y) {x' y'} (hx : x' = x) (hy : y' = y) : (γ.cast hx hy : I -> X) = γ :=
  rfl

/--
lemma `bijective_cast` / 引理 `bijective_cast`

English:
lemma bijective_cast
  given: {x' y' : X} (hx : x' = x) (hy : y' = y)
  statement: Bijective (Path.cast · hx hy)
  proof: by
  subst_vars; exact bijective_id

@[congr]

中文:
引理 bijective_cast
  条件: {x' y' : X} (hx : x' = x) (hy : y' = y)
  结论: 双射 (道路.cast · hx hy)
  证明: by
  subst_vars; exact bijective_id

@[congr]

Depends on / 依赖: bijective_id
-/
lemma bijective_cast {x' y' : X} (hx : x' = x) (hy : y' = y) : Bijective (Path.cast · hx hy) := by
  subst_vars; exact bijective_id

@[congr]
/--
lemma `exists_congr` / 引理 `exists_congr`

English:
lemma exists_congr
  statement: {x₁ x₂ y₁ y₂ : X} {p : Path x₁ y₁ -> Prop}
  proof: .surjective.exists bijective_cast hx hy

@[continuity, fun_prop]

中文:
引理 存在_congr
  结论: {x₁ x₂ y₁ y₂ : X} {p : 道路 x₁ y₁ -> 命题}
  证明: .surjective.exists bijective_cast hx hy

@[continuity, fun_prop]

Depends on / 依赖: bijective_cast, surjective, surjective.exists
-/
lemma exists_congr {x₁ x₂ y₁ y₂ : X} {p : Path x₁ y₁ -> Prop}
    (hx : x₁ = x₂) (hy : y₁ = y₂) :
    (exists γ, p γ) ↔ (exists (γ : Path x₂ y₂), p (γ.cast hx hy)) :=
.surjective.exists bijective_cast hx hy

@[continuity, fun_prop]
/--
theorem `symm_continuous_family` / 定理 `symm_continuous_family`

English:
theorem symm_continuous_family
  statement: {ι : Type*} [TopologicalSpace ι]
  proof: h.comp (continuous_id.prodMap continuous_symm)

@[continuity]

中文:
定理 symm_continuous_family
  结论: {ι : 类型} [拓扑空间 ι]
  证明: h.comp (continuous_id.prodMap continuous_symm)

@[continuity]

Depends on / 依赖: continuous_id, continuous_id.prodMap, continuous_symm, h.comp, prodMap
-/
theorem symm_continuous_family {ι : Type*} [TopologicalSpace ι]
    {a b : ι -> X} (γ : forall t : ι, Path (a t) (b t)) (h : Continuous ↿γ) :
    Continuous ↿fun t => (γ t).symm :=
  h.comp (continuous_id.prodMap continuous_symm)

@[continuity]
/--
theorem `continuous_symm` / 定理 `continuous_symm`

English:
theorem continuous_symm
  statement: Continuous (symm : Path x y -> Path y x)
  proof: continuous_uncurry_iff.mp symm_continuous_family _ (by fun_prop)

@[continuity]

中文:
定理 continuous_symm
  结论: 连续 (symm : 道路 x y -> 道路 y x)
  证明: continuous_uncurry_iff.mp symm_continuous_family _ (by fun_prop)

@[continuity]

Depends on / 依赖: continuous_uncurry_iff, continuous_uncurry_iff.mp, fun_prop, symm_continuous_family
-/
theorem continuous_symm : Continuous (symm : Path x y -> Path y x) :=
continuous_uncurry_iff.mp symm_continuous_family _ (by fun_prop)

@[continuity]
/--
theorem `continuous_uncurry_extend_of_continuous_family` / 定理 `continuous_uncurry_extend_of_continuous_family`

English:
theorem continuous_uncurry_extend_of_continuous_family
  statement: {ι : Type*} [TopologicalSpace ι]
  proof: by
  apply h.comp (continuous_id.prodMap continuous_projIcc)
  exact zero_le_one

@[continuity]

中文:
定理 continuous_uncurry_extend_of_continuous_family
  结论: {ι : 类型} [拓扑空间 ι]
  证明: by
  apply h.comp (continuous_id.prodMap continuous_projIcc)
  exact zero_le_one

@[continuity]

Depends on / 依赖: continuous_id, continuous_id.prodMap, continuous_projIcc, h.comp, prodMap, zero_le_one
-/
theorem continuous_uncurry_extend_of_continuous_family {ι : Type*} [TopologicalSpace ι]
    {a b : ι -> X} (γ : forall t : ι, Path (a t) (b t)) (h : Continuous ↿γ) :
    Continuous ↿fun t => ⇑(γ t).extend := by
  apply h.comp (continuous_id.prodMap continuous_projIcc)
  exact zero_le_one

@[continuity]
/--
theorem `trans_continuous_family` / 定理 `trans_continuous_family`

English:
theorem trans_continuous_family
  statement: {ι : Type*} [TopologicalSpace ι]
  proof: by
  have h₁' := Path.continuous_uncurry_extend_of_continuous_family γ₁ h₁
  have h₂' := Path.continuous_uncurry_extend_of_continuous_family γ₂ h₂
  simp only [HasUncurry.uncurry, Path.trans]
  refine Continuous.if_le ?_ ?_ (continuous_subtype_val.comp continuous_snd) continuous_const ?_
  · change


中文:
定理 trans_continuous_family
  结论: {ι : 类型} [拓扑空间 ι]
  证明: by
  have h₁' := Path.continuous_uncurry_extend_of_continuous_family γ₁ h₁
  have h₂' := Path.continuous_uncurry_extend_of_continuous_family γ₂ h₂
  simp only [HasUncurry.uncurry, Path.trans]
  refine Continuous.if_le ?_ ?_ (continuous_subtype_val.comp continuous_snd) continuous_const ?_
  · change


Depends on / 依赖: Continuous, Continuous.if_le, HasUncurry, HasUncurry.uncurry, Path.continuous_uncurry_extend_of_continuous_family, Path.trans, Prod.map, continuous_const, continuous_snd, continuous_subtype_val, continuous_subtype_val.comp, continuous_uncurry_extend_of_continuous_family, extend, fun_prop, if_le, uncurry
-/
theorem trans_continuous_family {ι : Type*} [TopologicalSpace ι]
    {a b c : ι -> X} (γ₁ : forall t : ι, Path (a t) (b t)) (h₁ : Continuous ↿γ₁)
    (γ₂ : forall t : ι, Path (b t) (c t)) (h₂ : Continuous ↿γ₂) :
    Continuous ↿fun t => (γ₁ t).trans (γ₂ t) := by
  have h₁' := Path.continuous_uncurry_extend_of_continuous_family γ₁ h₁
  have h₂' := Path.continuous_uncurry_extend_of_continuous_family γ₂ h₂
  simp only [HasUncurry.uncurry, Path.trans]
  refine Continuous.if_le ?_ ?_ (continuous_subtype_val.comp continuous_snd) continuous_const ?_
  · change
      Continuous ((fun p : ι × Real => (γ₁ p.1).extend p.2) ∘ Prod.map id (fun x => 2 * x : I -> Real))
    exact h₁'.comp (by fun_prop)
  · change
      Continuous ((fun p : ι × Real => (γ₂ p.1).extend p.2) ∘ Prod.map id (fun x => 2 * x - 1 : I -> Real))
    exact h₂'.comp (by fun_prop)
  · rintro st hst
    simp [hst]

@[continuity, fun_prop]
/--
theorem `_root_.Continuous.path_trans` / 定理 `_root_.Continuous.path_trans`

English:
theorem _root_.Continuous.path_trans
  given: {f : Y -> Path x y} {g : Y -> Path y z}
  proof: by
  intro hf hg
  apply continuous_uncurry_iff.mp
  exact trans_continuous_family _ (continuous_uncurry_iff.mpr hf) _ (continuous_uncurry_iff.mpr hg)

@[continuity, fun_prop]

中文:
定理 _root_.连续.path_trans
  条件: {f : Y -> 道路 x y} {g : Y -> 道路 y z}
  证明: by
  intro hf hg
  apply continuous_uncurry_iff.mp
  exact trans_continuous_family _ (continuous_uncurry_iff.mpr hf) _ (continuous_uncurry_iff.mpr hg)

@[continuity, fun_prop]

Depends on / 依赖: continuous_uncurry_iff, continuous_uncurry_iff.mp, continuous_uncurry_iff.mpr, trans_continuous_family
-/
theorem _root_.Continuous.path_trans {f : Y -> Path x y} {g : Y -> Path y z} :
    Continuous f -> Continuous g -> Continuous fun t => (f t).trans (g t) := by
  intro hf hg
  apply continuous_uncurry_iff.mp
  exact trans_continuous_family _ (continuous_uncurry_iff.mpr hf) _ (continuous_uncurry_iff.mpr hg)

@[continuity, fun_prop]
/--
theorem `continuous_trans` / 定理 `continuous_trans`

English:
theorem continuous_trans
  given: {x y z : X}
  statement: Continuous fun ρ : Path x y × Path y z => ρ.1.trans ρ.2
  proof: by
  fun_prop

中文:
定理 continuous_trans
  条件: {x y z : X}
  结论: 连续 fun ρ : 道路 x y × 道路 y z => ρ.1.trans ρ.2
  证明: by
  fun_prop

Depends on / 依赖: fun_prop
-/
theorem continuous_trans {x y z : X} : Continuous fun ρ : Path x y × Path y z => ρ.1.trans ρ.2 := by
  fun_prop


/-! #### Product of paths -/
section Prod

variable {a₁ a₂ a₃ : X} {b₁ b₂ b₃ : Y}

/--
Definition of `prod` / `prod` 的定义

English:
definition prod
  signature: (γ₁ : Path a₁ a₂) (γ₂ : Path b₁ b₂)
  body: ContinuousMap.prodMk γ₁.toContinuousMap γ₂.toContinuousMap
  source' := by simp
  target' := by simp

@[simp, grind =]

中文:
定义 乘积
  签名: (γ₁ : 道路 a₁ a₂) (γ₂ : 道路 b₁ b₂)
  定义体: ContinuousMap.prodMk γ₁.toContinuousMap γ₂.toContinuousMap
  source' := by simp
  target' := by simp

@[simp, grind =]
-/
protected def prod (γ₁ : Path a₁ a₂) (γ₂ : Path b₁ b₂) : Path (a₁, b₁) (a₂, b₂) where
  toContinuousMap := ContinuousMap.prodMk γ₁.toContinuousMap γ₂.toContinuousMap
  source' := by simp
  target' := by simp

@[simp, grind =]
/--
theorem `prod_coe` / 定理 `prod_coe`

English:
theorem prod_coe
  given: (γ₁ : Path a₁ a₂) (γ₂ : Path b₁ b₂)
  proof: rfl

中文:
定理 prod_coe
  条件: (γ₁ : 道路 a₁ a₂) (γ₂ : 道路 b₁ b₂)
  证明: rfl
-/
theorem prod_coe (γ₁ : Path a₁ a₂) (γ₂ : Path b₁ b₂) :
    ⇑(γ₁.prod γ₂) = fun t => (γ₁ t, γ₂ t) :=
  rfl

/--
theorem `trans_prod_eq_prod_trans` / 定理 `trans_prod_eq_prod_trans`

English:
theorem trans_prod_eq_prod_trans
  statement: (γ₁ : Path a₁ a₂) (δ₁ : Path a₂ a₃) (γ₂ : Path b₁ b₂)
  proof: by
  grind

中文:
定理 trans_prod_eq_prod_trans
  结论: (γ₁ : 道路 a₁ a₂) (δ₁ : 道路 a₂ a₃) (γ₂ : 道路 b₁ b₂)
  证明: by
  grind
-/
theorem trans_prod_eq_prod_trans (γ₁ : Path a₁ a₂) (δ₁ : Path a₂ a₃) (γ₂ : Path b₁ b₂)
    (δ₂ : Path b₂ b₃) : (γ₁.prod γ₂).trans (δ₁.prod δ₂) = (γ₁.trans δ₁).prod (γ₂.trans δ₂) := by
  grind

end Prod

section Pi

variable {χ : ι -> Type*} [forall i, TopologicalSpace (χ i)] {as bs cs : forall i, χ i}

/--
Definition of `pi` / `pi` 的定义

English:
definition pi
  signature: (γ : forall i, Path (as i) (bs i))
  body: ContinuousMap.pi fun i => (γ i).toContinuousMap
  source' := by simp
  target' := by simp

@[simp, grind =]

中文:
定义 pi
  签名: (γ : 对任意 i, 道路 (as i) (bs i))
  定义体: ContinuousMap.pi fun i => (γ i).toContinuousMap
  source' := by simp
  target' := by simp

@[simp, grind =]
-/
protected def pi (γ : forall i, Path (as i) (bs i)) : Path as bs where
  toContinuousMap := ContinuousMap.pi fun i => (γ i).toContinuousMap
  source' := by simp
  target' := by simp

@[simp, grind =]
/--
theorem `pi_coe` / 定理 `pi_coe`

English:
theorem pi_coe
  given: (γ : forall i, Path (as i) (bs i))
  statement: ⇑(Path.pi γ) = fun t i => γ i t
  proof: rfl

中文:
定理 pi_coe
  条件: (γ : 对任意 i, 道路 (as i) (bs i))
  结论: ⇑(道路.pi γ) = fun t i => γ i t
  证明: rfl
-/
theorem pi_coe (γ : forall i, Path (as i) (bs i)) : ⇑(Path.pi γ) = fun t i => γ i t :=
  rfl

/--
theorem `trans_pi_eq_pi_trans` / 定理 `trans_pi_eq_pi_trans`

English:
theorem trans_pi_eq_pi_trans
  given: (γ₀ : forall i, Path (as i) (bs i)) (γ₁ : forall i, Path (bs i) (cs i))
  proof: by
  ext t i
  unfold Path.trans
  simp only [Path.coe_mk_mk, Function.comp_apply, pi_coe]
  split_ifs
  · rfl
  · rfl

中文:
定理 trans_pi_eq_pi_trans
  条件: (γ₀ : 对任意 i, 道路 (as i) (bs i)) (γ₁ : 对任意 i, 道路 (bs i) (cs i))
  证明: by
  ext t i
  unfold Path.trans
  simp only [Path.coe_mk_mk, Function.comp_apply, pi_coe]
  split_ifs
  · rfl
  · rfl

Depends on / 依赖: Function, Function.comp_apply, Path.coe_mk_mk, Path.trans, coe_mk_mk, comp_apply, pi_coe, split_ifs
-/
theorem trans_pi_eq_pi_trans (γ₀ : forall i, Path (as i) (bs i)) (γ₁ : forall i, Path (bs i) (cs i)) :
    (Path.pi γ₀).trans (Path.pi γ₁) = Path.pi fun i => (γ₀ i).trans (γ₁ i) := by
  ext t i
  unfold Path.trans
  simp only [Path.coe_mk_mk, Function.comp_apply, pi_coe]
  split_ifs
  · rfl
  · rfl

end Pi

/-! #### Pointwise operations on paths in a topological (additive) group -/


/-- Pointwise multiplication of paths in a topological group. -/
@[to_additive (attr := simps!) /-- Pointwise addition of paths in a topological additive group. -/]
/--
Definition of `mul` / `mul` 的定义

English:
definition mul
  signature: [Mul X] [ContinuousMul X] {a₁ b₁ a₂ b₂ : X} (γ₁ : Path a₁ b₁) (γ₂ : Path a₂ b₂)
  body: (γ₁.prod γ₂).map continuous_mul

中文:
定义 mul
  签名: [乘法 X] [连续乘法 X] {a₁ b₁ a₂ b₂ : X} (γ₁ : 道路 a₁ b₁) (γ₂ : 道路 a₂ b₂)
  定义体: (γ₁.prod γ₂).map continuous_mul
-/
protected def mul [Mul X] [ContinuousMul X] {a₁ b₁ a₂ b₂ : X} (γ₁ : Path a₁ b₁) (γ₂ : Path a₂ b₂) :
    Path (a₁ * a₂) (b₁ * b₂) :=
  (γ₁.prod γ₂).map continuous_mul

/-- Pointwise inversion of paths in a topological group. -/
@[to_additive (attr := simps!) /-- Pointwise negation of paths in a topological group. -/]
/--
Definition of `inv` / `inv` 的定义

English:
definition inv
  signature: {a b : X} [Inv X] [ContinuousInv X] (γ : Path a b)
  body: γ.map continuous_inv

中文:
定义 inv
  签名: {a b : X} [取逆 X] [连续取逆 X] (γ : 道路 a b)
  定义体: γ.map continuous_inv

Depends on / 依赖: continuous_inv
-/
def inv {a b : X} [Inv X] [ContinuousInv X] (γ : Path a b) :
    Path a⁻¹ b⁻¹ :=
  γ.map continuous_inv

/-! #### Truncating a path -/


/--
Definition of `truncate` / `truncate` 的定义

English:
definition truncate
  signature: {X : Type*} [TopologicalSpace X] {a b : X} (γ : Path a b) (t₀ t₁ : Real)
  body: γ.extend (min (max s t₀) t₁)
  continuous_toFun := γ.continuous_extend.comp (by fun_prop)
  source' := by
    simp only [min_def, max_def']
    split_ifs with h₁ h₂ h₃ h₄
    · simp [γ.extend_of_le_zero h₁]
    · congr
      linarith
    · have h₄ : t₁ <= 0 := le_of_lt (by simpa using h₂)
      simp

中文:
定义 truncate
  签名: {X : 类型} [拓扑空间 X] {a b : X} (γ : 道路 a b) (t₀ t₁ : 实数)
  定义体: γ.extend (min (max s t₀) t₁)
  continuous_toFun := γ.continuous_extend.comp (by fun_prop)
  source' := by
    simp only [min_def, max_def']
    split_ifs with h₁ h₂ h₃ h₄
    · simp [γ.extend_of_le_zero h₁]
    · congr
      linarith
    · have h₄ : t₁ <= 0 := le_of_lt (by simpa using h₂)
      simp

Depends on / 依赖: extend
-/
def truncate {X : Type*} [TopologicalSpace X] {a b : X} (γ : Path a b) (t₀ t₁ : Real) :
    Path (γ.extend <| min t₀ t₁) (γ.extend t₁) where
  toFun s := γ.extend (min (max s t₀) t₁)
  continuous_toFun := γ.continuous_extend.comp (by fun_prop)
  source' := by
    simp only [min_def, max_def']
    split_ifs with h₁ h₂ h₃ h₄
    · simp [γ.extend_of_le_zero h₁]
    · congr
      linarith
    · have h₄ : t₁ <= 0 := le_of_lt (by simpa using h₂)
      simp [γ.extend_of_le_zero h₄, γ.extend_of_le_zero h₁]
    all_goals rfl
  target' := by
    simp only [min_def, max_def']
    split_ifs with h₁ h₂ h₃
    · simp [γ.extend_of_one_le h₂]
    · rfl
    · have h₄ : 1 <= t₀ := le_of_lt (by simpa using h₁)
      simp [γ.extend_of_one_le h₄, γ.extend_of_one_le (h₄.trans h₃)]
    · rfl

/--
Definition of `truncateOfLE` / `truncateOfLE` 的定义

English:
definition truncateOfLE
  signature: {X : Type*} [TopologicalSpace X] {a b : X} (γ : Path a b) {t₀ t₁ : Real}
  body: (γ.truncate t₀ t₁).cast (by rw [min_eq_left h]) rfl

中文:
定义 truncateOfLE
  签名: {X : 类型} [拓扑空间 X] {a b : X} (γ : 道路 a b) {t₀ t₁ : 实数}
  定义体: (γ.truncate t₀ t₁).cast (by rw [min_eq_left h]) rfl

Depends on / 依赖: min_eq_left, truncate
-/
def truncateOfLE {X : Type*} [TopologicalSpace X] {a b : X} (γ : Path a b) {t₀ t₁ : Real}
    (h : t₀ <= t₁) : Path (γ.extend t₀) (γ.extend t₁) :=
  (γ.truncate t₀ t₁).cast (by rw [min_eq_left h]) rfl

/--
theorem `truncate_range` / 定理 `truncate_range`

English:
theorem truncate_range
  given: {a b : X} (γ : Path a b) {t₀ t₁ : Real}
  proof: by
  rw [← γ.extend_range]
  simp only [range_subset_iff, SetCoe.forall]
  intro x _hx
  simp only [DFunLike.coe, Path.truncate, mem_range_self]

中文:
定理 truncate_range
  条件: {a b : X} (γ : 道路 a b) {t₀ t₁ : 实数}
  证明: by
  rw [← γ.extend_range]
  simp only [range_subset_iff, SetCoe.forall]
  intro x _hx
  simp only [DFunLike.coe, Path.truncate, mem_range_self]

Depends on / 依赖: DFunLike, DFunLike.coe, Path.truncate, SetCoe, SetCoe.forall, extend_range, mem_range_self, range_subset_iff, truncate
-/
theorem truncate_range {a b : X} (γ : Path a b) {t₀ t₁ : Real} :
    range (γ.truncate t₀ t₁) subseteq range γ := by
  rw [← γ.extend_range]
  simp only [range_subset_iff, SetCoe.forall]
  intro x _hx
  simp only [DFunLike.coe, Path.truncate, mem_range_self]

/-- For a path `γ`, `γ.truncate` gives a "continuous family of paths", by which we mean
the uncurried function which maps `(t₀, t₁, s)` to `γ.truncate t₀ t₁ s` is continuous. -/
@[continuity]
/--
theorem `truncate_continuous_family` / 定理 `truncate_continuous_family`

English:
theorem truncate_continuous_family
  given: {a b : X} (γ : Path a b)
  proof: γ.continuous_extend.comp
    (((continuous_subtype_val.comp (continuous_snd.comp continuous_snd)).max continuous_fst).min
      (continuous_fst.comp continuous_snd))

@[continuity]

中文:
定理 truncate_continuous_family
  条件: {a b : X} (γ : 道路 a b)
  证明: γ.continuous_extend.comp
    (((continuous_subtype_val.comp (continuous_snd.comp continuous_snd)).max continuous_fst).min
      (continuous_fst.comp continuous_snd))

@[continuity]

Depends on / 依赖: continuous_extend, continuous_extend.comp, continuous_fst, continuous_fst.comp, continuous_snd, continuous_snd.comp, continuous_subtype_val, continuous_subtype_val.comp
-/
theorem truncate_continuous_family {a b : X} (γ : Path a b) :
    Continuous (fun x => γ.truncate x.1 x.2.1 x.2.2 : Real × Real × I -> X) :=
  γ.continuous_extend.comp
    (((continuous_subtype_val.comp (continuous_snd.comp continuous_snd)).max continuous_fst).min
      (continuous_fst.comp continuous_snd))

@[continuity]
/--
theorem `truncate_const_continuous_family` / 定理 `truncate_const_continuous_family`

English:
theorem truncate_const_continuous_family
  statement: {a b : X} (γ : Path a b)
  proof: by
  have key : Continuous (fun x => (t, x) : Real × I -> Real × Real × I) := by fun_prop
  exact γ.truncate_continuous_family.comp key

@[simp]

中文:
定理 truncate_const_continuous_family
  结论: {a b : X} (γ : 道路 a b)
  证明: by
  have key : Continuous (fun x => (t, x) : Real × I -> Real × Real × I) := by fun_prop
  exact γ.truncate_continuous_family.comp key

@[simp]

Depends on / 依赖: Continuous, fun_prop, truncate_continuous_family, truncate_continuous_family.comp
-/
theorem truncate_const_continuous_family {a b : X} (γ : Path a b)
    (t : Real) : Continuous ↿(γ.truncate t) := by
  have key : Continuous (fun x => (t, x) : Real × I -> Real × Real × I) := by fun_prop
  exact γ.truncate_continuous_family.comp key

@[simp]
/--
theorem `truncate_self` / 定理 `truncate_self`

English:
theorem truncate_self
  given: {a b : X} (γ : Path a b) (t : Real)
  proof: by
  ext x
  by_cases hx : x <= t <;> simp [truncate]

中文:
定理 truncate_self
  条件: {a b : X} (γ : 道路 a b) (t : 实数)
  证明: by
  ext x
  by_cases hx : x <= t <;> simp [truncate]

Depends on / 依赖: truncate
-/
theorem truncate_self {a b : X} (γ : Path a b) (t : Real) :
    γ.truncate t t = (Path.refl <| γ.extend t).cast (by rw [min_self]) rfl := by
  ext x
  by_cases hx : x <= t <;> simp [truncate]

/--
theorem `truncate_zero_zero` / 定理 `truncate_zero_zero`

English:
theorem truncate_zero_zero
  given: {a b : X} (γ : Path a b)
  proof: by
  convert! γ.truncate_self 0

中文:
定理 truncate_zero_zero
  条件: {a b : X} (γ : 道路 a b)
  证明: by
  convert! γ.truncate_self 0

Depends on / 依赖: convert, truncate_self
-/
theorem truncate_zero_zero {a b : X} (γ : Path a b) :
    γ.truncate 0 0 = (Path.refl a).cast (by rw [min_self, γ.extend_zero]) γ.extend_zero := by
  convert! γ.truncate_self 0

/--
theorem `truncate_one_one` / 定理 `truncate_one_one`

English:
theorem truncate_one_one
  given: {a b : X} (γ : Path a b)
  proof: by
  convert! γ.truncate_self 1

@[simp]

中文:
定理 truncate_one_one
  条件: {a b : X} (γ : 道路 a b)
  证明: by
  convert! γ.truncate_self 1

@[simp]

Depends on / 依赖: convert, truncate_self
-/
theorem truncate_one_one {a b : X} (γ : Path a b) :
    γ.truncate 1 1 = (Path.refl b).cast (by rw [min_self, γ.extend_one]) γ.extend_one := by
  convert! γ.truncate_self 1

@[simp]
/--
theorem `truncate_zero_one` / 定理 `truncate_zero_one`

English:
theorem truncate_zero_one
  given: {a b : X} (γ : Path a b)
  proof: by
  ext x
  rw [cast_coe]
  have : ↑x in (Icc 0 1 : Set Real) := x.2
  rw [truncate]; rw [coe_mk_mk]; rw [max_eq_left this.1]; rw [min_eq_left this.2]; rw [extend_extends']

中文:
定理 truncate_zero_one
  条件: {a b : X} (γ : 道路 a b)
  证明: by
  ext x
  rw [cast_coe]
  have : ↑x in (Icc 0 1 : Set Real) := x.2
  rw [truncate]; rw [coe_mk_mk]; rw [max_eq_left this.1]; rw [min_eq_left this.2]; rw [extend_extends']

Depends on / 依赖: cast_coe, coe_mk_mk, extend_extends, max_eq_left, min_eq_left, truncate
-/
theorem truncate_zero_one {a b : X} (γ : Path a b) :
    γ.truncate 0 1 = γ.cast (by simp) (by simp) := by
  ext x
  rw [cast_coe]
  have : ↑x in (Icc 0 1 : Set Real) := x.2
  rw [truncate]; rw [coe_mk_mk]; rw [max_eq_left this.1]; rw [min_eq_left this.2]; rw [extend_extends']

/-! #### Reparametrising a path -/


/--
Definition of `reparam` / `reparam` 的定义

English:
definition reparam
  signature: (γ : Path x y) (f : I -> I) (hfcont : Continuous f) (hf₀ : f 0 = 0) (hf₁ : f 1 = 1)
  body: γ ∘ f
  continuous_toFun := by fun_prop
  source' := by simp [hf₀]
  target' := by simp [hf₁]

@[simp]

中文:
定义 reparam
  签名: (γ : 道路 x y) (f : I -> I) (hfcont : 连续 f) (hf₀ : f 0 = 0) (hf₁ : f 1 = 1)
  定义体: γ ∘ f
  continuous_toFun := by fun_prop
  source' := by simp [hf₀]
  target' := by simp [hf₁]

@[simp]
-/
def reparam (γ : Path x y) (f : I -> I) (hfcont : Continuous f) (hf₀ : f 0 = 0) (hf₁ : f 1 = 1) :
    Path x y where
  toFun := γ ∘ f
  continuous_toFun := by fun_prop
  source' := by simp [hf₀]
  target' := by simp [hf₁]

@[simp]
/--
theorem `coe_reparam` / 定理 `coe_reparam`

English:
theorem coe_reparam
  statement: (γ : Path x y) {f : I -> I} (hfcont : Continuous f) (hf₀ : f 0 = 0)
  proof: rfl

@[simp]

中文:
定理 coe_reparam
  结论: (γ : 道路 x y) {f : I -> I} (hfcont : 连续 f) (hf₀ : f 0 = 0)
  证明: rfl

@[simp]
-/
theorem coe_reparam (γ : Path x y) {f : I -> I} (hfcont : Continuous f) (hf₀ : f 0 = 0)
    (hf₁ : f 1 = 1) : ⇑(γ.reparam f hfcont hf₀ hf₁) = γ ∘ f :=
  rfl

@[simp]
/--
theorem `reparam_id` / 定理 `reparam_id`

English:
theorem reparam_id
  given: (γ : Path x y)
  statement: γ.reparam id continuous_id rfl rfl = γ
  proof: by
  ext
  rfl

中文:
定理 reparam_id
  条件: (γ : 道路 x y)
  结论: γ.reparam id continuous_id rfl rfl = γ
  证明: by
  ext
  rfl
-/
theorem reparam_id (γ : Path x y) : γ.reparam id continuous_id rfl rfl = γ := by
  ext
  rfl

/--
theorem `range_reparam` / 定理 `range_reparam`

English:
theorem range_reparam
  statement: (γ : Path x y) {f : I -> I} (hfcont : Continuous f) (hf₀ : f 0 = 0)
  proof: by
  change range (γ ∘ f) = range γ
  have : range f = univ := by
    rw [range_eq_univ]
    intro t
    have h₁ : Continuous (Set.IccExtend (zero_le_one' Real) f) := by fun_prop
    have := intermediate_value_Icc (zero_le_one' Real) h₁.continuousOn
    · rw [IccExtend_left, IccExtend_right, Icc.mk_

中文:
定理 range_reparam
  结论: (γ : 道路 x y) {f : I -> I} (hfcont : 连续 f) (hf₀ : f 0 = 0)
  证明: by
  change range (γ ∘ f) = range γ
  have : range f = univ := by
    rw [range_eq_univ]
    intro t
    have h₁ : Continuous (Set.IccExtend (zero_le_one' Real) f) := by fun_prop
    have := intermediate_value_Icc (zero_le_one' Real) h₁.continuousOn
    · rw [IccExtend_left, IccExtend_right, Icc.mk_

Depends on / 依赖: Continuous, Icc.mk_one, Icc.mk_zero, IccExtend, IccExtend_left, IccExtend_of_mem, IccExtend_right, Set.IccExtend, continuousOn, fun_prop, image_univ, intermediate_value_Icc, mk_one, mk_zero, range_comp, range_eq_univ, zero_le_one
-/
theorem range_reparam (γ : Path x y) {f : I -> I} (hfcont : Continuous f) (hf₀ : f 0 = 0)
    (hf₁ : f 1 = 1) : range (γ.reparam f hfcont hf₀ hf₁) = range γ := by
  change range (γ ∘ f) = range γ
  have : range f = univ := by
    rw [range_eq_univ]
    intro t
    have h₁ : Continuous (Set.IccExtend (zero_le_one' Real) f) := by fun_prop
    have := intermediate_value_Icc (zero_le_one' Real) h₁.continuousOn
    · rw [IccExtend_left, IccExtend_right, Icc.mk_zero, Icc.mk_one, hf₀, hf₁] at this
      rcases this t.2 with ⟨w, hw₁, hw₂⟩
      rw [IccExtend_of_mem _ _ hw₁] at hw₂
      exact ⟨_, hw₂⟩
  rw [range_comp]; rw [this]; rw [image_univ]

/--
theorem `refl_reparam` / 定理 `refl_reparam`

English:
theorem refl_reparam
  given: {f : I -> I} (hfcont : Continuous f) (hf₀ : f 0 = 0) (hf₁ : f 1 = 1)
  proof: by
  ext
  simp

中文:
定理 refl_reparam
  条件: {f : I -> I} (hfcont : 连续 f) (hf₀ : f 0 = 0) (hf₁ : f 1 = 1)
  证明: by
  ext
  simp
-/
theorem refl_reparam {f : I -> I} (hfcont : Continuous f) (hf₀ : f 0 = 0) (hf₁ : f 1 = 1) :
    (refl x).reparam f hfcont hf₀ hf₁ = refl x := by
  ext
  simp

end Path
