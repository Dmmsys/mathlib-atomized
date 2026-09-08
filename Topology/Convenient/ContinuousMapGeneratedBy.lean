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

variable {ι : Type t} {X : ι → Type u} [∀ i, TopologicalSpace (X i)]
  {Y : Type v} [TopologicalSpace Y] {Z : Type v'} [TopologicalSpace Z]

namespace Topology

variable (X) in
/-- Given a family `X i` of topological space, this is a predicate
on maps `g : Y → Z` between topological spaces saying that for any
continuous map `f : X i → Y`, the composition `g ∘ f` is continuous.
We say that `g` is `X`-continuous. -/
/-
**Topology.ContinuousGeneratedBy** 是 Mathlib 中的一个定义，位于命名空间 `Topology`。
形式化陈述：ContinuousGeneratedBy (g : Y -> Z) : Prop
参数：g : Y -> Z。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a family `X i` of topological space, this is a predicate
on maps `g : Y → Z` between topological spaces saying that for any
continuous map `f : X i → Y`, the composition `g ∘ f` is continuous.
We say that `g` is `X`-continuous.
-/
def ContinuousGeneratedBy (g : Y → Z) : Prop :=
  ∀ ⦃i : ι⦄ (f : C(X i, Y)), Continuous (g ∘ f)
/-
**Topology.continuousGeneratedBy_def** 是 Mathlib 中的一个引理，位于命名空间 `Topology`。
形式化陈述：continuousGeneratedBy_def (g : Y -> Z) : ContinuousGeneratedBy X g ↔ foral
l ⦃i : ι⦄ (f : C(X i, Y)), Continuous (g ∘ f)
参数：g : Y -> Z。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma continuousGeneratedBy_def (g : Y → Z) :
    ContinuousGeneratedBy X g ↔
      ∀ ⦃i : ι⦄ (f : C(X i, Y)), Continuous (g ∘ f) := Iff.rfl
/-
**Topology.continuousGeneratedBy_iff** 是 Mathlib 中的一个引理，位于命名空间 `Topology`。
形式化陈述：continuousGeneratedBy_iff (g : Y -> Z) : ContinuousGeneratedBy X g ↔ Conti
nuous ((WithGeneratedByTopology.equiv (X
参数：g : Y -> Z。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Topology.IsGeneratedBy.equiv_symm_comp_continuous_iff`：equiv_symm_comp_c
ontinuous_iff (g : Y -> Z) : Continuous ((WithGeneratedByTopology.equiv (X
· 使用定理 `Topology.IsGeneratedBy.instWithGeneratedByTopology`：∀ {ι : Type t} {X : 
ι → Type u} [inst : (i : ι) → TopologicalSpace (X i)] {Y : Type v} [tY : Topolog
icalSpace Y],   Topology.IsGeneratedBy X…
· 使用引理 `Topology.WithGeneratedByTopology.continuous_from_iff`：continuous_from_if
f (g : WithGeneratedByTopology X Y -> Z) : Continuous g ↔ forall ⦃i : ι⦄ (f : C(
X i, Y)), Continuous (g ∘ equiv.symm ∘ f :…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma continuousGeneratedBy_iff (g : Y → Z) :
    ContinuousGeneratedBy X g ↔
      Continuous ((WithGeneratedByTopology.equiv (X := X)).symm ∘ g ∘
        WithGeneratedByTopology.equiv (X := X)) := by
  rw [IsGeneratedBy.equiv_symm_comp_continuous_iff,
    WithGeneratedByTopology.continuous_from_iff]
  rfl

/-- A `X`-continuous map `g : Y → Z` induces a continuous map
between the types `Y` and `Z` equipped with the `X`-generated topology. -/
/-
**Topology.ContinuousGeneratedBy.continuousMap** 是 Mathlib 中的一个定义，位于命名空间 `Topolo
gy.ContinuousGeneratedBy`。
形式化陈述：{ι : Type t} →   {X : ι → Type u} →     [inst : (i : ι) → TopologicalSpace
 (X i)] →       {Y : Type v} →         [inst_1 : TopologicalSpace Y] →          
 {Z : Type v'} →             [inst_2 : TopologicalSpace Z] →               {g : 
Y → Z} →                 Topology.ContinuousGeneratedBy X g →                   
C(Topology.WithGeneratedByTopology X Y, Topology.WithGeneratedByTopology X Z)
参数：i : ι；X i；Topology.WithGeneratedByTopology X Y, Topology.WithGeneratedByTopol
ogy X Z。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
A `X`-continuous map `g : Y → Z` induces a continuous map
between the types `Y` and `Z` equipped with the `X`-generated topology.
-/
def ContinuousGeneratedBy.continuousMap {g : Y → Z}
    (hg : ContinuousGeneratedBy X g) :
    C(WithGeneratedByTopology X Y, WithGeneratedByTopology X Z) :=
  ⟨WithGeneratedByTopology.equiv.symm ∘ g ∘ WithGeneratedByTopology.equiv, by
    rwa [← continuousGeneratedBy_iff]⟩

@[simp]
/-
**Topology.ContinuousGeneratedBy.continuousMap_coe** 是 Mathlib 中的一个定理，位于命名空间 `To
pology.ContinuousGeneratedBy`。
形式化陈述：∀ {ι : Type t} {X : ι → Type u} [inst : (i : ι) → TopologicalSpace (X i)] 
{Y : Type v} [inst_1 : TopologicalSpace Y]   {Z : Type v'} [inst_2 : Topological
Space Z] {g : Y → Z} (hg : Topology.ContinuousGeneratedBy X g),   ⇑hg.continuous
Map = ⇑Topology.WithGeneratedByTopology.equiv.symm ∘ g ∘ ⇑Topology.WithGenerated
ByTopology.equiv
参数：i : ι；X i；hg : Topology.ContinuousGeneratedBy X g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ContinuousGeneratedBy.continuousMap_coe {g : Y → Z}
    (hg : ContinuousGeneratedBy X g) :
    ⇑hg.continuousMap = WithGeneratedByTopology.equiv.symm ∘ g ∘ WithGeneratedByTopology.equiv :=
  rfl

@[simp]
/-
**Topology.ContinuousGeneratedBy.id** 是 Mathlib 中的一个定理，位于命名空间 `Topology.Continuo
usGeneratedBy`。
形式化陈述：∀ {ι : Type t} {X : ι → Type u} [inst : (i : ι) → TopologicalSpace (X i)] 
{Y : Type v} [inst_1 : TopologicalSpace Y],   Topology.ContinuousGeneratedBy X i
d
参数：i : ι；X i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm_comp_self`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), ⇑e.symm ∘
 ⇑e = id
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
-/
lemma ContinuousGeneratedBy.id :
    ContinuousGeneratedBy X (id : Y → Y) := by
  simpa [continuousGeneratedBy_iff] using continuous_id
/-
**Topology.ContinuousGeneratedBy.comp** 是 Mathlib 中的一个定理，位于命名空间 `Topology.Contin
uousGeneratedBy`。
形式化陈述：∀ {ι : Type t} {X : ι → Type u} [inst : (i : ι) → TopologicalSpace (X i)] 
{Y : Type v} [inst_1 : TopologicalSpace Y]   {Z : Type v'} [inst_2 : Topological
Space Z] {g : Y → Z},   Topology.ContinuousGeneratedBy X g →     ∀ {T : Type u_1
} [inst_3 : TopologicalSpace T] {f : T → Y},       Topology.ContinuousGeneratedB
y X f → Topology.ContinuousGeneratedBy X (g ∘ f)
参数：i : ι；X i；g ∘ f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Topology.continuousGeneratedBy_iff`：continuousGeneratedBy_iff (g : Y -> 
Z) : ContinuousGeneratedBy X g ↔ Continuous ((WithGeneratedByTopology.equiv (X
· 使用定理 `ContinuousMap.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y] (f : C(X, Y)), Continuous ⇑f
-/
lemma ContinuousGeneratedBy.comp {g : Y → Z} (hg : ContinuousGeneratedBy X g)
    {T : Type*} [TopologicalSpace T] {f : T → Y} (hf : ContinuousGeneratedBy X f) :
    ContinuousGeneratedBy X (g ∘ f) := by
  rw [continuousGeneratedBy_iff]
  exact (hg.continuousMap.comp hf.continuousMap).continuous

end Topology

/-
**Continuous.continuousGeneratedBy** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Continuous.continuousGeneratedBy {g : Y -> Z} (hg : Continuous g) : Contin
uousGeneratedBy X g
参数：hg : Continuous g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Topology.continuousGeneratedBy_def`：continuousGeneratedBy_def (g : Y -> 
Z) : ContinuousGeneratedBy X g ↔ forall ⦃i : ι⦄ (f : C(X i, Y)), Continuous (g ∘
 f)
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `ContinuousMap.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y] (f : C(X, Y)), Continuous ⇑f
-/
lemma Continuous.continuousGeneratedBy {g : Y → Z}
    (hg : Continuous g) : ContinuousGeneratedBy X g := by
  rw [continuousGeneratedBy_def]
  exact fun _ f ↦ hg.comp f.continuous

namespace Topology

variable (X Y Z) in
/-- The (bundled) type of `X`-continuous maps `Y → Z`. -/
@[ext]
/-
**Topology.ContinuousMapGeneratedBy** 是 Mathlib 中的一个归纳类型，位于命名空间 `Topology`。
形式化陈述：{ι : Type t} →   (X : ι → Type u) →     [(i : ι) → TopologicalSpace (X i)]
 →       (Y : Type v) → [TopologicalSpace Y] → (Z : Type v') → [TopologicalSpace
 Z] → Type (max v v')
参数：X : ι → Type u；i : ι；X i；Y : Type v；Z : Type v'；max v v'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The (bundled) type of `X`-continuous maps `Y → Z`.
-/
structure ContinuousMapGeneratedBy where
  /-- the underlying map of a `X`-continuous map -/
  toFun : Y → Z
  prop : ContinuousGeneratedBy X toFun
/-
**Topology.** 是 Mathlib 中的一个实例，位于命名空间 `Topology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : FunLike (ContinuousMapGeneratedBy X Y Z) Y Z where
  coe f := f.toFun
  coe_injective _ _ _ := by aesop

initialize_simps_projections ContinuousMapGeneratedBy (toFun → apply)

/-- The identity, as a `X`-continous map. -/
@[simps]
/-
**Topology.ContinuousMapGeneratedBy.id** 是 Mathlib 中的一个定义，位于命名空间 `Topology.Conti
nuousMapGeneratedBy`。
形式化陈述：{ι : Type t} →   {X : ι → Type u} →     [inst : (i : ι) → TopologicalSpace
 (X i)] →       {Y : Type v} → [inst_1 : TopologicalSpace Y] → Topology.Continuo
usMapGeneratedBy X Y Y
参数：i : ι；X i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity, as a `X`-continous map.
-/
def ContinuousMapGeneratedBy.id : ContinuousMapGeneratedBy X Y Y where
  toFun := _root_.id
  prop := continuous_id.continuousGeneratedBy

/-- The composition of `X`-continuous maps. -/
@[simps]
/-
**Topology.ContinuousMapGeneratedBy.comp** 是 Mathlib 中的一个定义，位于命名空间 `Topology.Con
tinuousMapGeneratedBy`。
形式化陈述：{ι : Type t} →   {X : ι → Type u} →     [inst : (i : ι) → TopologicalSpace
 (X i)] →       {Y : Type v} →         [inst_1 : TopologicalSpace Y] →          
 {Z : Type u_1} →             [inst_2 : TopologicalSpace Z] →               {T :
 Type u_2} →                 [inst_3 : TopologicalSpace T] →                   T
opology.ContinuousMapGeneratedBy X Y Z →                     Topology.Continuous
MapGeneratedBy X T Y → Topology.ContinuousMapGeneratedBy X T Z
参数：i : ι；X i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The composition of `X`-continuous maps.
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

/-- The identity `WithGeneratedByTopology.equiv.symm : Y → WithGeneratedByTopology X Y`
as a `X`-continuous map. -/
/-
**Topology.WithGeneratedByTopology.equivSymmAsContinuousMapGeneratedBy** 是 Mathl
ib 中的一个定义，位于命名空间 `Topology.WithGeneratedByTopology`。
形式化陈述：equivSymmAsContinuousMapGeneratedBy : ContinuousMapGeneratedBy X Y (WithGe
neratedByTopology X Y) where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The identity `WithGeneratedByTopology.equiv.symm : Y → WithGeneratedByTopology X
 Y`
as a `X`-continuous map.
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
/-
**Topology.WithGeneratedByTopology.equivSymmAsContinuousMapGeneratedBy_coe** 是 M
athlib 中的一个引理，位于命名空间 `Topology.WithGeneratedByTopology`。
形式化陈述：equivSymmAsContinuousMapGeneratedBy_coe : ⇑(equivSymmAsContinuousMapGenera
tedBy X Y) = equiv.symm
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma equivSymmAsContinuousMapGeneratedBy_coe :
    ⇑(equivSymmAsContinuousMapGeneratedBy X Y) = equiv.symm := rfl

/-- The identity `WithGeneratedByTopology.equiv : WithGeneratedByTopology X Y → Y`
as a `X`-continuous map. -/
/-
**Topology.WithGeneratedByTopology.equivAsContinuousMapGeneratedBy** 是 Mathlib 中
的一个定义，位于命名空间 `Topology.WithGeneratedByTopology`。
形式化陈述：equivAsContinuousMapGeneratedBy : ContinuousMapGeneratedBy X (WithGenerate
dByTopology X Y) Y where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity `WithGeneratedByTopology.equiv : WithGeneratedByTopology X Y → Y`
as a `X`-continuous map.
-/
def equivAsContinuousMapGeneratedBy :
    ContinuousMapGeneratedBy X (WithGeneratedByTopology X Y) Y where
  toFun := equiv
  prop := continuous_equiv.continuousGeneratedBy

@[simp]
/-
**Topology.WithGeneratedByTopology.equivAsContinuousMapGeneratedBy_coe** 是 Mathl
ib 中的一个引理，位于命名空间 `Topology.WithGeneratedByTopology`。
形式化陈述：equivAsContinuousMapGeneratedBy_coe : ⇑(equivAsContinuousMapGeneratedBy X 
Y) = equiv
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma equivAsContinuousMapGeneratedBy_coe :
    ⇑(equivAsContinuousMapGeneratedBy X Y) = equiv := rfl

end WithGeneratedByTopology

end Topology

