/-
Copyright (c) 2023 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
module

public import Mathlib.Geometry.Manifold.LocalInvariantProperties
public import Mathlib.Topology.Sheaves.LocalPredicate

/-! # Generic construction of a sheaf from a `LocalInvariantProp` on a manifold

This file constructs the sheaf-of-types of functions `f : M → M'` (for charted spaces `M`, `M'`)
which satisfy the lifted property `LiftProp P` associated to some locally invariant (in the sense
of `StructureGroupoid.LocalInvariantProp`) property `P` on the model spaces of `M` and `M'`. For
example, differentiability and smoothness are locally invariant properties in this sense, so this
construction can be used to construct the sheaf of differentiable functions on a manifold and the
sheaf of smooth functions on a manifold.

The mathematical work is in associating a `TopCat.LocalPredicate` to a
`StructureGroupoid.LocalInvariantProp`: that is, showing that a differential-geometric "locally
invariant" property is preserved under restriction and gluing.

## Main definitions

* `StructureGroupoid.LocalInvariantProp.localPredicate`: the `TopCat.LocalPredicate` (in the
  sheaf-theoretic sense) on functions from open subsets of `M` into `M'`, which states whether
  such functions satisfy `LiftProp P`.
* `StructureGroupoid.LocalInvariantProp.sheaf`: the sheaf-of-types of functions `f : M → M'`
  which satisfy the lifted property `LiftProp P`.
-/

@[expose] public section


open scoped Manifold Topology

open Set TopologicalSpace StructureGroupoid StructureGroupoid.LocalInvariantProp Opposite

universe u

variable {H : Type*} [TopologicalSpace H] {H' : Type*} [TopologicalSpace H']
  {G : StructureGroupoid H} {G' : StructureGroupoid H'} {P : (H → H') → Set H → H → Prop}
  (M : Type u) [TopologicalSpace M] [ChartedSpace H M] (M' : Type u) [TopologicalSpace M']
  [ChartedSpace H' M']

/-
**TopCat.of.chartedSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：TopCat.of.chartedSpace : ChartedSpace H (TopCat.of M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance TopCat.of.chartedSpace : ChartedSpace H (TopCat.of M) :=
  inferInstanceAs <| ChartedSpace H M
/-
**TopCat.of.hasGroupoid** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：TopCat.of.hasGroupoid [HasGroupoid M G] : HasGroupoid (TopCat.of M) G
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance TopCat.of.hasGroupoid [HasGroupoid M G] : HasGroupoid (TopCat.of M) G :=
  inferInstanceAs <| HasGroupoid M G

/-- Let `P` be a `LocalInvariantProp` for functions between spaces with the groupoids `G`, `G'`
and let `M`, `M'` be charted spaces modelled on the model spaces of those groupoids.  Then there is
an induced `LocalPredicate` on the functions from `M` to `M'`, given by `LiftProp P`. -/
/-
**StructureGroupoid.LocalInvariantProp.localPredicate** 是 Mathlib 中的一个定义，位于命名空间 
``。
形式化陈述：StructureGroupoid.LocalInvariantProp.localPredicate (hG : LocalInvariantPr
op G G' P) : TopCat.LocalPredicate fun _ : TopCat.of M => M' where pred {U : Ope
ns (TopCat.of M)}
参数：hG : LocalInvariantProp G G' P。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `P` be a `LocalInvariantProp` for functions between spaces with the groupoid
s `G`, `G'`
and let `M`, `M'` be charted spaces modelled on the model spaces of those groupo
ids.  Then there is
an induced `LocalPredicate` on the functions from `M` to `M'`, given by `LiftPro
p P`.
-/
def StructureGroupoid.LocalInvariantProp.localPredicate (hG : LocalInvariantProp G G' P) :
    TopCat.LocalPredicate fun _ : TopCat.of M => M' where
  pred {U : Opens (TopCat.of M)} := fun f : U → M' => ChartedSpace.LiftProp P f
  res := by
    intro U V i f h x
    have hUV : U ≤ V := CategoryTheory.leOfHom i
    change ChartedSpace.LiftPropAt P (f ∘ Opens.inclusion hUV) x
    rw [← hG.liftPropAt_iff_comp_inclusion hUV]
    apply h
  locality := by
    intro V f h x
    obtain ⟨U, hxU, i, hU : ChartedSpace.LiftProp P (f ∘ _)⟩ := h x
    let x' : U := ⟨x, hxU⟩
    have hUV : U ≤ V := CategoryTheory.leOfHom i
    have : ChartedSpace.LiftPropAt P f (Opens.inclusion hUV x') := by
      rw [hG.liftPropAt_iff_comp_inclusion hUV]
      exact hU x'
    convert! this

/-- Let `P` be a `LocalInvariantProp` for functions between spaces with the groupoids `G`, `G'`
and let `M`, `M'` be charted spaces modelled on the model spaces of those groupoids.  Then there is
a sheaf of types on `M` which, to each open set `U` in `M`, associates the type of bundled
functions from `U` to `M'` satisfying the lift of `P`. -/
/-
**StructureGroupoid.LocalInvariantProp.sheaf** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：StructureGroupoid.LocalInvariantProp.sheaf (hG : LocalInvariantProp G G' P
) : TopCat.Sheaf (Type u) (TopCat.of M)
参数：hG : LocalInvariantProp G G' P。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `P` be a `LocalInvariantProp` for functions between spaces with the groupoid
s `G`, `G'`
and let `M`, `M'` be charted spaces modelled on the model spaces of those groupo
ids.  Then there is
a sheaf of types on `M` which, to each open set `U` in `M`, associates the type 
of bundled
functions from `U` to `M'` satisfying the lift of `P`.
-/
def StructureGroupoid.LocalInvariantProp.sheaf (hG : LocalInvariantProp G G' P) :
    TopCat.Sheaf (Type u) (TopCat.of M) :=
  TopCat.subsheafToTypes (hG.localPredicate M M')
/-
**StructureGroupoid.LocalInvariantProp.sheafHasCoeToFun** 是 Mathlib 中的一个实例，位于命名空
间 ``。
形式化陈述：StructureGroupoid.LocalInvariantProp.sheafHasCoeToFun (hG : LocalInvariant
Prop G G' P) (U : (Opens (TopCat.of M))ᵒᵖ) : CoeFun ((hG.sheaf M M').obj.obj U) 
fun _ => ↑(unop U) -> M' where coe a
参数：hG : LocalInvariantProp G G' P；U : (Opens (TopCat.of M))ᵒᵖ。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance StructureGroupoid.LocalInvariantProp.sheafHasCoeToFun (hG : LocalInvariantProp G G' P)
    (U : (Opens (TopCat.of M))ᵒᵖ) : CoeFun ((hG.sheaf M M').obj.obj U) fun _ => ↑(unop U) → M' where
  coe a := a.1
/-
**StructureGroupoid.LocalInvariantProp.section_spec** 是 Mathlib 中的一个定理，位于命名空间 ``
。
形式化陈述：StructureGroupoid.LocalInvariantProp.section_spec (hG : LocalInvariantProp
 G G' P) (U : (Opens (TopCat.of M))ᵒᵖ) (f : (hG.sheaf M M').obj.obj U) : Charted
Space.LiftProp P f
参数：hG : LocalInvariantProp G G' P；U : (Opens (TopCat.of M))ᵒᵖ；f : (hG.sheaf M M'
).obj.obj U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem StructureGroupoid.LocalInvariantProp.section_spec (hG : LocalInvariantProp G G' P)
    (U : (Opens (TopCat.of M))ᵒᵖ) (f : (hG.sheaf M M').obj.obj U) : ChartedSpace.LiftProp P f :=
  f.2
