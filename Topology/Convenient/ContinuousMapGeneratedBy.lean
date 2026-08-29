/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Topology.Convenient.GeneratedBy

/-!
# `X`-continuous maps

Given a family `X i` of topological spaces, we introduce a predicate
`ContinuousGeneratedBy X` on maps `g : Y ⟶ Z` saying that
`g` is `X`-continuous, i.e. for any continuous map `f : X i → Y`,
the composition `g ∘ f` is continuous.

## References
* [Martín Escardó, Jimmie Lawson and Alex Simpson, *Comparing Cartesian closed
  categories of (core) compactly generated spaces*][escardo-lawson-simpson-2004]

-/

universe v v' t u

@[expose] public section

open Topology

variable {ι : Type t} {X : ι -> Type u} [forall i, TopologicalSpace (X i)]
  {Y : Type v} [TopologicalSpace Y] {Z : Type v'} [TopologicalSpace Z]

namespace Topology

variable (X) in
/--
Definition of `ContinuousGeneratedBy` / `ContinuousGeneratedBy` 的定义

English:
definition ContinuousGeneratedBy
  signature: (g : Y -> Z)
  body: forall ⦃i : ι⦄ (f : C(X i, Y)), Continuous (g ∘ f)

中文:
定义 ContinuousGeneratedBy
  签名: (g : Y -> Z)
  定义体: forall ⦃i : ι⦄ (f : C(X i, Y)), Continuous (g ∘ f)

Depends on / 依赖: Continuous
-/
def ContinuousGeneratedBy (g : Y -> Z) : Prop :=
  forall ⦃i : ι⦄ (f : C(X i, Y)), Continuous (g ∘ f)

/--
lemma `continuousGeneratedBy_def` / 引理 `continuousGeneratedBy_def`

English:
lemma continuousGeneratedBy_def
  given: (g : Y -> Z)
  proof: Iff.rfl

中文:
引理 continuousGeneratedBy_def
  条件: (g : Y -> Z)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma continuousGeneratedBy_def (g : Y -> Z) :
    ContinuousGeneratedBy X g ↔
      forall ⦃i : ι⦄ (f : C(X i, Y)), Continuous (g ∘ f) := Iff.rfl

/--
lemma `continuousGeneratedBy_iff` / 引理 `continuousGeneratedBy_iff`

English:
lemma continuousGeneratedBy_iff
  given: (g : Y -> Z)
  proof: by
  rw [IsGeneratedBy.equiv_symm_comp_continuous_iff]; rw [WithGeneratedByTopology.continuous_from_iff]
  rfl

中文:
引理 continuousGeneratedBy_iff
  条件: (g : Y -> Z)
  证明: by
  rw [IsGeneratedBy.equiv_symm_comp_continuous_iff]; rw [WithGeneratedByTopology.continuous_from_iff]
  rfl
-/
lemma continuousGeneratedBy_iff (g : Y -> Z) :
    ContinuousGeneratedBy X g ↔
      Continuous ((WithGeneratedByTopology.equiv (X := X)).symm ∘ g ∘
        WithGeneratedByTopology.equiv (X := X)) := by
  rw [IsGeneratedBy.equiv_symm_comp_continuous_iff]; rw [WithGeneratedByTopology.continuous_from_iff]
  rfl

/--
Definition of `ContinuousGeneratedBy.continuousMap` / `ContinuousGeneratedBy.continuousMap` 的定义

English:
definition ContinuousGeneratedBy.continuousMap
  signature: {g : Y -> Z}
  body: ⟨WithGeneratedByTopology.equiv.symm ∘ g ∘ WithGeneratedByTopology.equiv, by
    rwa [← continuousGeneratedBy_iff]⟩

@[simp]

中文:
定义 ContinuousGeneratedBy.continuousMap
  签名: {g : Y -> Z}
  定义体: ⟨WithGeneratedByTopology.equiv.symm ∘ g ∘ WithGeneratedByTopology.equiv, by
    rwa [← continuousGeneratedBy_iff]⟩

@[simp]

Depends on / 依赖: WithGeneratedByTopology, WithGeneratedByTopology.equiv, WithGeneratedByTopology.equiv.symm, continuousGeneratedBy_iff
-/
def ContinuousGeneratedBy.continuousMap {g : Y -> Z}
    (hg : ContinuousGeneratedBy X g) :
    C(WithGeneratedByTopology X Y, WithGeneratedByTopology X Z) :=
  ⟨WithGeneratedByTopology.equiv.symm ∘ g ∘ WithGeneratedByTopology.equiv, by
    rwa [← continuousGeneratedBy_iff]⟩

@[simp]
/--
lemma `ContinuousGeneratedBy.continuousMap_coe` / 引理 `ContinuousGeneratedBy.continuousMap_coe`

English:
lemma ContinuousGeneratedBy.continuousMap_coe
  statement: {g : Y -> Z}
  proof: rfl

@[simp]

中文:
引理 ContinuousGeneratedBy.continuousMap_coe
  结论: {g : Y -> Z}
  证明: rfl

@[simp]
-/
lemma ContinuousGeneratedBy.continuousMap_coe {g : Y -> Z}
    (hg : ContinuousGeneratedBy X g) :
    ⇑hg.continuousMap = WithGeneratedByTopology.equiv.symm ∘ g ∘ WithGeneratedByTopology.equiv :=
  rfl

@[simp]
/--
lemma `ContinuousGeneratedBy.id` / 引理 `ContinuousGeneratedBy.id`

English:
lemma ContinuousGeneratedBy.id
  proof: by
  simpa [continuousGeneratedBy_iff] using continuous_id

中文:
引理 ContinuousGeneratedBy.id
  证明: by
  simpa [continuousGeneratedBy_iff] using continuous_id

Depends on / 依赖: continuousGeneratedBy_iff, continuous_id
-/
lemma ContinuousGeneratedBy.id :
    ContinuousGeneratedBy X (id : Y -> Y) := by
  simpa [continuousGeneratedBy_iff] using continuous_id

/--
lemma `ContinuousGeneratedBy.comp` / 引理 `ContinuousGeneratedBy.comp`

English:
lemma ContinuousGeneratedBy.comp
  statement: {g : Y -> Z} (hg : ContinuousGeneratedBy X g)
  proof: by
  rw [continuousGeneratedBy_iff]
  exact (hg.continuousMap.comp hf.continuousMap).continuous

中文:
引理 ContinuousGeneratedBy.comp
  结论: {g : Y -> Z} (hg : ContinuousGeneratedBy X g)
  证明: by
  rw [continuousGeneratedBy_iff]
  exact (hg.continuousMap.comp hf.continuousMap).continuous

Depends on / 依赖: continuous, continuousGeneratedBy_iff, continuousMap, hf.continuousMap, hg.continuousMap.comp
-/
lemma ContinuousGeneratedBy.comp {g : Y -> Z} (hg : ContinuousGeneratedBy X g)
    {T : Type*} [TopologicalSpace T] {f : T -> Y} (hf : ContinuousGeneratedBy X f) :
    ContinuousGeneratedBy X (g ∘ f) := by
  rw [continuousGeneratedBy_iff]
  exact (hg.continuousMap.comp hf.continuousMap).continuous

end Topology

/--
lemma `Continuous.continuousGeneratedBy` / 引理 `Continuous.continuousGeneratedBy`

English:
lemma Continuous.continuousGeneratedBy
  statement: {g : Y -> Z}
  proof: by
  rw [continuousGeneratedBy_def]
  exact fun _ f => hg.comp f.continuous

中文:
引理 连续.continuousGeneratedBy
  结论: {g : Y -> Z}
  证明: by
  rw [continuousGeneratedBy_def]
  exact fun _ f => hg.comp f.continuous

Depends on / 依赖: continuous, continuousGeneratedBy_def, f.continuous, hg.comp
-/
lemma Continuous.continuousGeneratedBy {g : Y -> Z}
    (hg : Continuous g) : ContinuousGeneratedBy X g := by
  rw [continuousGeneratedBy_def]
  exact fun _ f => hg.comp f.continuous

namespace Topology

variable (X Y Z) in
/-- The (bundled) type of `X`-continuous maps `Y → Z`. -/
@[ext]
/--
Definition of `ContinuousMapGeneratedBy` / `ContinuousMapGeneratedBy` 的定义

English:
structure ContinuousMapGeneratedBy
  parameters: where
  axioms and operations (2):
    - toFun : Y -> Z
    - prop : ContinuousGeneratedBy X toFun

中文:
结构 余ntinuousMapGeneratedBy
  参数: where
  公理与运算 (2 个):
    - toFun : Y -> Z
    - prop : ContinuousGeneratedBy X toFun
-/
structure ContinuousMapGeneratedBy where
  /-- the underlying map of a `X`-continuous map -/
  toFun : Y -> Z
  prop : ContinuousGeneratedBy X toFun

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FunLike (ContinuousMapGeneratedBy X Y Z) Y Z
  body: f.toFun
  coe_injective _ _ _ := by aesop

initialize_simps_projections ContinuousMapGeneratedBy (toFun -> apply)

中文:
实例 :
  签名: 函数状 (余ntinuousMapGeneratedBy X Y Z) Y Z
  定义体: f.toFun
  coe_injective _ _ _ := by aesop

initialize_simps_projections ContinuousMapGeneratedBy (toFun -> apply)

Depends on / 依赖: f.toFun
-/
instance : FunLike (ContinuousMapGeneratedBy X Y Z) Y Z where
  coe f := f.toFun
  coe_injective _ _ _ := by aesop

initialize_simps_projections ContinuousMapGeneratedBy (toFun -> apply)

/-- The identity, as a `X`-continous map. -/
@[simps]
/--
Definition of `ContinuousMapGeneratedBy.id` / `ContinuousMapGeneratedBy.id` 的定义

English:
definition ContinuousMapGeneratedBy.id
  signature: : ContinuousMapGeneratedBy X Y Y where
  body: _root_.id
  prop := continuous_id.continuousGeneratedBy

中文:
定义 余ntinuousMapGeneratedBy.id
  签名: : 余ntinuousMapGeneratedBy X Y Y where
  定义体: _root_.id
  prop := continuous_id.continuousGeneratedBy

Depends on / 依赖: _root_, _root_.id
-/
def ContinuousMapGeneratedBy.id : ContinuousMapGeneratedBy X Y Y where
  toFun := _root_.id
  prop := continuous_id.continuousGeneratedBy

/-- The composition of `X`-continuous maps. -/
@[simps]
/--
Definition of `ContinuousMapGeneratedBy.comp` / `ContinuousMapGeneratedBy.comp` 的定义

English:
definition ContinuousMapGeneratedBy.comp
  body: g.toFun.comp f.toFun
  prop := g.prop.comp f.prop

中文:
定义 余ntinuousMapGeneratedBy.comp
  定义体: g.toFun.comp f.toFun
  prop := g.prop.comp f.prop

Depends on / 依赖: f.toFun, g.toFun.comp
-/
def ContinuousMapGeneratedBy.comp
    {Z : Type*} [TopologicalSpace Z]
    {T : Type*} [TopologicalSpace T]
    (g : ContinuousMapGeneratedBy X Y Z)
    (f : ContinuousMapGeneratedBy X T Y) :
    ContinuousMapGeneratedBy X T Z where
  toFun := g.toFun.comp f.toFun
  prop := g.prop.comp f.prop

namespace WithGeneratedByTopology

variable (X Y)

/--
Definition of `equivSymmAsContinuousMapGeneratedBy` / `equivSymmAsContinuousMapGeneratedBy` 的定义

English:
definition equivSymmAsContinuousMapGeneratedBy
  signature: :
  body: equiv.symm
  prop := by
    rw [continuousGeneratedBy_def]
    intro i f
    rw [IsGeneratedBy.equiv_symm_comp_continuous_iff]
    fun_prop

@[simp]

中文:
定义 equivSymmAsContinuousMapGeneratedBy
  签名: :
  定义体: equiv.symm
  prop := by
    rw [continuousGeneratedBy_def]
    intro i f
    rw [IsGeneratedBy.equiv_symm_comp_continuous_iff]
    fun_prop

@[simp]

Depends on / 依赖: equiv.symm
-/
def equivSymmAsContinuousMapGeneratedBy :
    ContinuousMapGeneratedBy X Y (WithGeneratedByTopology X Y) where
  toFun := equiv.symm
  prop := by
    rw [continuousGeneratedBy_def]
    intro i f
    rw [IsGeneratedBy.equiv_symm_comp_continuous_iff]
    fun_prop

@[simp]
/--
lemma `equivSymmAsContinuousMapGeneratedBy_coe` / 引理 `equivSymmAsContinuousMapGeneratedBy_coe`

English:
lemma equivSymmAsContinuousMapGeneratedBy_coe
  proof: rfl

中文:
引理 equivSymmAsContinuousMapGeneratedBy_coe
  证明: rfl
-/
lemma equivSymmAsContinuousMapGeneratedBy_coe :
    ⇑(equivSymmAsContinuousMapGeneratedBy X Y) = equiv.symm := rfl

/--
Definition of `equivAsContinuousMapGeneratedBy` / `equivAsContinuousMapGeneratedBy` 的定义

English:
definition equivAsContinuousMapGeneratedBy
  signature: :
  body: equiv
  prop := continuous_equiv.continuousGeneratedBy

@[simp]

中文:
定义 equivAsContinuousMapGeneratedBy
  签名: :
  定义体: equiv
  prop := continuous_equiv.continuousGeneratedBy

@[simp]
-/
def equivAsContinuousMapGeneratedBy :
    ContinuousMapGeneratedBy X (WithGeneratedByTopology X Y) Y where
  toFun := equiv
  prop := continuous_equiv.continuousGeneratedBy

@[simp]
/--
lemma `equivAsContinuousMapGeneratedBy_coe` / 引理 `equivAsContinuousMapGeneratedBy_coe`

English:
lemma equivAsContinuousMapGeneratedBy_coe
  proof: rfl

中文:
引理 equivAsContinuousMapGeneratedBy_coe
  证明: rfl
-/
lemma equivAsContinuousMapGeneratedBy_coe :
    ⇑(equivAsContinuousMapGeneratedBy X Y) = equiv := rfl

end WithGeneratedByTopology

end Topology
