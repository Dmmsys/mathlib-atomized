/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.GroupTheory.GroupAction.DomAct.Basic

/-!
# Topological space structure on `Mᵈᵐᵃ` and `Mᵈᵃᵃ`

In this file we define `TopologicalSpace` structure on `Mᵈᵐᵃ` and `Mᵈᵃᵃ`
and prove basic theorems about these topologies.
The topologies on `Mᵈᵐᵃ` and `Mᵈᵃᵃ` are the same as the topology on `M`.
Formally, they are induced by `DomMulAct.mk.symm` and `DomAddAct.mk.symm`,
since the types aren't definitionally equal.

## Tags

topological space, group action, domain action
-/

@[expose] public section

open Filter TopologicalSpace Topology

namespace DomMulAct

variable {M : Type*} [TopologicalSpace M]

/-- Put the same topological space structure on `Mᵈᵐᵃ` as on the original space. -/
@[to_additive /-- Put the same topological space structure on `Mᵈᵃᵃ` as on the original space. -/]
/-
**DomMulAct.instTopologicalSpace** 是 Mathlib 中的一个实例，位于命名空间 `DomMulAct`。
形式化陈述：instTopologicalSpace : TopologicalSpace Mᵈᵐᵃ
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Put the same topological space structure on `Mᵈᵐᵃ` as on the original space.
-/
instance instTopologicalSpace : TopologicalSpace Mᵈᵐᵃ := .induced mk.symm ‹_›

@[to_additive (attr := continuity, fun_prop)]
/-
**DomMulAct.continuous_mk** 是 Mathlib 中的一个定理，位于命名空间 `DomMulAct`。
形式化陈述：continuous_mk : Continuous (@mk M)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `continuous_induced_rng`：continuous_induced_rng {g : γ -> α} {t₂ : Topolo
gicalSpace β} {t₁ : TopologicalSpace γ} : Continuous[t₁, induced f t₂] g ↔ Conti
nuous[t₁, t₂…
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
-/
theorem continuous_mk : Continuous (@mk M) := continuous_induced_rng.2 continuous_id

@[to_additive (attr := continuity, fun_prop)]
/-
**DomMulAct.continuous_mk_symm** 是 Mathlib 中的一个定理，位于命名空间 `DomMulAct`。
形式化陈述：continuous_mk_symm : Continuous (@mk M).symm
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_induced_dom`：continuous_induced_dom {t : TopologicalSpace β} 
: Continuous[induced f t, t] f
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem continuous_mk_symm : Continuous (@mk M).symm := continuous_induced_dom

/-- `DomMulAct.mk` as a homeomorphism. -/
@[to_additive (attr := simps toEquiv) /-- `DomAddAct.mk` as a homeomorphism. -/]
/-
**DomMulAct.mkHomeomorph** 是 Mathlib 中的一个定义，位于命名空间 `DomMulAct`。
形式化陈述：mkHomeomorph : M ≃ₜ Mᵈᵐᵃ where toEquiv
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`DomMulAct.mk` as a homeomorphism.
-/
def mkHomeomorph : M ≃ₜ Mᵈᵐᵃ where
  toEquiv := mk
/-
**DomMulAct.coe_mkHomeomorph** 是 Mathlib 中的一个定理，位于命名空间 `DomMulAct`。
形式化陈述：∀ {M : Type u_1} [inst : TopologicalSpace M], ⇑DomMulAct.mkHomeomorph = ⇑D
omMulAct.mk
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive (attr := simp)] theorem coe_mkHomeomorph : ⇑(mkHomeomorph : M ≃ₜ Mᵈᵐᵃ) = mk := rfl

@[to_additive (attr := simp)]
/-
**DomMulAct.coe_mkHomeomorph_symm** 是 Mathlib 中的一个定理，位于命名空间 `DomMulAct`。
形式化陈述：coe_mkHomeomorph_symm : ⇑(mkHomeomorph : M ≃ₜ Mᵈᵐᵃ).symm = mk.symm
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mkHomeomorph_symm : ⇑(mkHomeomorph : M ≃ₜ Mᵈᵐᵃ).symm = mk.symm := rfl
/-
**DomMulAct.isInducing_mk** 是 Mathlib 中的一个定理，位于命名空间 `DomMulAct`。
形式化陈述：∀ {M : Type u_1} [inst : TopologicalSpace M], Topology.IsInducing ⇑DomMulA
ct.mk
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Homeomorph.isInducing`：isInducing (h : X ≃ₜ Y) : IsInducing h
-/
@[to_additive] theorem isInducing_mk : IsInducing (@mk M) := mkHomeomorph.isInducing
/-
**DomMulAct.isEmbedding_mk** 是 Mathlib 中的一个定理，位于命名空间 `DomMulAct`。
形式化陈述：∀ {M : Type u_1} [inst : TopologicalSpace M], Topology.IsEmbedding ⇑DomMul
Act.mk
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.isEmbedding`：isEmbedding (h : X ≃ₜ Y) : IsEmbedding h
-/
@[to_additive] theorem isEmbedding_mk : IsEmbedding (@mk M) := mkHomeomorph.isEmbedding
/-
**DomMulAct.isOpenEmbedding_mk** 是 Mathlib 中的一个定理，位于命名空间 `DomMulAct`。
形式化陈述：∀ {M : Type u_1} [inst : TopologicalSpace M], Topology.IsOpenEmbedding ⇑Do
mMulAct.mk
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.isOpenEmbedding`：isOpenEmbedding (h : X ≃ₜ Y) : IsOpenEmbeddi
ng h
-/
@[to_additive] theorem isOpenEmbedding_mk : IsOpenEmbedding (@mk M) := mkHomeomorph.isOpenEmbedding
/-
**DomMulAct.isClosedEmbedding_mk** 是 Mathlib 中的一个定理，位于命名空间 `DomMulAct`。
形式化陈述：∀ {M : Type u_1} [inst : TopologicalSpace M], Topology.IsClosedEmbedding ⇑
DomMulAct.mk
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.isClosedEmbedding`：isClosedEmbedding (h : X ≃ₜ Y) : IsClosedE
mbedding h
-/
@[to_additive] theorem isClosedEmbedding_mk : IsClosedEmbedding (@mk M) :=
  mkHomeomorph.isClosedEmbedding
/-
**DomMulAct.isQuotientMap_mk** 是 Mathlib 中的一个定理，位于命名空间 `DomMulAct`。
形式化陈述：∀ {M : Type u_1} [inst : TopologicalSpace M], Topology.IsQuotientMap ⇑DomM
ulAct.mk
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.isQuotientMap`：isQuotientMap (h : X ≃ₜ Y) : IsQuotientMap h
-/
@[to_additive] theorem isQuotientMap_mk : IsQuotientMap (@mk M) := mkHomeomorph.isQuotientMap
/-
**DomMulAct.isInducing_mk_symm** 是 Mathlib 中的一个定理，位于命名空间 `DomMulAct`。
形式化陈述：∀ {M : Type u_1} [inst : TopologicalSpace M], Topology.IsInducing ⇑DomMulA
ct.mk.symm
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Homeomorph.isInducing`：isInducing (h : X ≃ₜ Y) : IsInducing h
-/
@[to_additive] theorem isInducing_mk_symm : IsInducing (@mk M).symm := mkHomeomorph.symm.isInducing
/-
**DomMulAct.isEmbedding_mk_symm** 是 Mathlib 中的一个定理，位于命名空间 `DomMulAct`。
形式化陈述：∀ {M : Type u_1} [inst : TopologicalSpace M], Topology.IsEmbedding ⇑DomMul
Act.mk.symm
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.isEmbedding`：isEmbedding (h : X ≃ₜ Y) : IsEmbedding h
-/
@[to_additive] theorem isEmbedding_mk_symm : IsEmbedding (@mk M).symm :=
  mkHomeomorph.symm.isEmbedding

@[to_additive]
/-
**DomMulAct.isOpenEmbedding_mk_symm** 是 Mathlib 中的一个定理，位于命名空间 `DomMulAct`。
形式化陈述：isOpenEmbedding_mk_symm : IsOpenEmbedding (@mk M).symm
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.isOpenEmbedding`：isOpenEmbedding (h : X ≃ₜ Y) : IsOpenEmbeddi
ng h
-/
theorem isOpenEmbedding_mk_symm : IsOpenEmbedding (@mk M).symm := mkHomeomorph.symm.isOpenEmbedding

@[to_additive]
/-
**DomMulAct.isClosedEmbedding_mk_symm** 是 Mathlib 中的一个定理，位于命名空间 `DomMulAct`。
形式化陈述：isClosedEmbedding_mk_symm : IsClosedEmbedding (@mk M).symm
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.isClosedEmbedding`：isClosedEmbedding (h : X ≃ₜ Y) : IsClosedE
mbedding h
-/
theorem isClosedEmbedding_mk_symm : IsClosedEmbedding (@mk M).symm :=
  mkHomeomorph.symm.isClosedEmbedding

@[to_additive]
/-
**DomMulAct.isQuotientMap_mk_symm** 是 Mathlib 中的一个定理，位于命名空间 `DomMulAct`。
形式化陈述：isQuotientMap_mk_symm : IsQuotientMap (@mk M).symm
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.isQuotientMap`：isQuotientMap (h : X ≃ₜ Y) : IsQuotientMap h
-/
theorem isQuotientMap_mk_symm : IsQuotientMap (@mk M).symm := mkHomeomorph.symm.isQuotientMap
/-
**DomMulAct.instT0Space** 是 Mathlib 中的一个定理，位于命名空间 `DomMulAct`。
形式化陈述：∀ {M : Type u_1} [inst : TopologicalSpace M] [T0Space M], T0Space Mᵈᵐᵃ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.t0Space`：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalS
pace X] [inst_1 : TopologicalSpace Y] [T0Space X] (h : X ≃ₜ Y),   T0Space Y
-/
@[to_additive] instance instT0Space [T0Space M] : T0Space Mᵈᵐᵃ := mkHomeomorph.t0Space
/-
**DomMulAct.instT1Space** 是 Mathlib 中的一个定理，位于命名空间 `DomMulAct`。
形式化陈述：∀ {M : Type u_1} [inst : TopologicalSpace M] [T1Space M], T1Space Mᵈᵐᵃ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.t1Space`：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalS
pace X] [inst_1 : TopologicalSpace Y] [T1Space X] (h : X ≃ₜ Y),   T1Space Y
-/
@[to_additive] instance instT1Space [T1Space M] : T1Space Mᵈᵐᵃ := mkHomeomorph.t1Space
/-
**DomMulAct.instT2Space** 是 Mathlib 中的一个定理，位于命名空间 `DomMulAct`。
形式化陈述：∀ {M : Type u_1} [inst : TopologicalSpace M] [T2Space M], T2Space Mᵈᵐᵃ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.t2Space`：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalS
pace X] [inst_1 : TopologicalSpace Y] [T2Space X] (h : X ≃ₜ Y),   T2Space Y
-/
@[to_additive] instance instT2Space [T2Space M] : T2Space Mᵈᵐᵃ := mkHomeomorph.t2Space
/-
**DomMulAct.instT25Space** 是 Mathlib 中的一个定理，位于命名空间 `DomMulAct`。
形式化陈述：∀ {M : Type u_1} [inst : TopologicalSpace M] [T25Space M], T25Space Mᵈᵐᵃ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.t25Space`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topological
Space X] [inst_1 : TopologicalSpace Y] [T25Space X] (h : X ≃ₜ Y),   T25Space Y
-/
@[to_additive] instance instT25Space [T25Space M] : T25Space Mᵈᵐᵃ := mkHomeomorph.t25Space
/-
**DomMulAct.instT3Space** 是 Mathlib 中的一个定理，位于命名空间 `DomMulAct`。
形式化陈述：∀ {M : Type u_1} [inst : TopologicalSpace M] [T3Space M], T3Space Mᵈᵐᵃ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.t3Space`：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalS
pace X] [inst_1 : TopologicalSpace Y] [T3Space X] (h : X ≃ₜ Y),   T3Space Y
-/
@[to_additive] instance instT3Space [T3Space M] : T3Space Mᵈᵐᵃ := mkHomeomorph.t3Space
/-
**DomMulAct.instT4Space** 是 Mathlib 中的一个定理，位于命名空间 `DomMulAct`。
形式化陈述：∀ {M : Type u_1} [inst : TopologicalSpace M] [T4Space M], T4Space Mᵈᵐᵃ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.t4Space`：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalS
pace X] [inst_1 : TopologicalSpace Y] [T4Space X] (h : X ≃ₜ Y),   T4Space Y
-/
@[to_additive] instance instT4Space [T4Space M] : T4Space Mᵈᵐᵃ := mkHomeomorph.t4Space
/-
**DomMulAct.instT5Space** 是 Mathlib 中的一个定理，位于命名空间 `DomMulAct`。
形式化陈述：∀ {M : Type u_1} [inst : TopologicalSpace M] [T5Space M], T5Space Mᵈᵐᵃ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.t5Space`：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalS
pace X] [inst_1 : TopologicalSpace Y] [T5Space X] (h : X ≃ₜ Y),   T5Space Y
-/
@[to_additive] instance instT5Space [T5Space M] : T5Space Mᵈᵐᵃ := mkHomeomorph.t5Space
/-
**DomMulAct.instR0Space** 是 Mathlib 中的一个定理，位于命名空间 `DomMulAct`。
形式化陈述：∀ {M : Type u_1} [inst : TopologicalSpace M] [R0Space M], R0Space Mᵈᵐᵃ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsInducing.r0Space`：Topology.IsInducing.r0Space [TopologicalSpa
ce Y] {f : Y -> X} (hf : IsInducing f) : R0Space Y where specializes_symm.symm a
 b
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Topology.IsEmbedding.toIsInducing`：∀ {X : Type u_1} {Y : Type u_2} [tX :
 TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbeddi
ng f → Topology.IsInduc…
· 使用定理 `DomMulAct.isEmbedding_mk_symm`：∀ {M : Type u_1} [inst : TopologicalSpace
 M], Topology.IsEmbedding ⇑DomMulAct.mk.symm
-/
@[to_additive] instance instR0Space [R0Space M] : R0Space Mᵈᵐᵃ := isEmbedding_mk_symm.r0Space
/-
**DomMulAct.instR1Space** 是 Mathlib 中的一个定理，位于命名空间 `DomMulAct`。
形式化陈述：∀ {M : Type u_1} [inst : TopologicalSpace M] [R1Space M], R1Space Mᵈᵐᵃ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsInducing.r1Space`：Topology.IsInducing.r1Space [TopologicalSpa
ce Y] {f : Y -> X} (hf : IsInducing f) : R1Space Y
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Topology.IsEmbedding.toIsInducing`：∀ {X : Type u_1} {Y : Type u_2} [tX :
 TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbeddi
ng f → Topology.IsInduc…
· 使用定理 `DomMulAct.isEmbedding_mk_symm`：∀ {M : Type u_1} [inst : TopologicalSpace
 M], Topology.IsEmbedding ⇑DomMulAct.mk.symm
-/
@[to_additive] instance instR1Space [R1Space M] : R1Space Mᵈᵐᵃ := isEmbedding_mk_symm.r1Space

@[to_additive]
/-
**DomMulAct.instRegularSpace** 是 Mathlib 中的一个实例，位于命名空间 `DomMulAct`。
形式化陈述：instRegularSpace [RegularSpace M] : RegularSpace Mᵈᵐᵃ
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsInducing.regularSpace`：∀ {X : Type u_1} {Y : Type u_2} [inst 
: TopologicalSpace X] [RegularSpace X] [inst_2 : TopologicalSpace Y] {f : Y → X}
,   Topology.IsInducin…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Topology.IsEmbedding.toIsInducing`：∀ {X : Type u_1} {Y : Type u_2} [tX :
 TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbeddi
ng f → Topology.IsInduc…
· 使用定理 `DomMulAct.isEmbedding_mk_symm`：∀ {M : Type u_1} [inst : TopologicalSpace
 M], Topology.IsEmbedding ⇑DomMulAct.mk.symm
-/
instance instRegularSpace [RegularSpace M] : RegularSpace Mᵈᵐᵃ := isEmbedding_mk_symm.regularSpace

@[to_additive]
/-
**DomMulAct.instNormalSpace** 是 Mathlib 中的一个实例，位于命名空间 `DomMulAct`。
形式化陈述：instNormalSpace [NormalSpace M] : NormalSpace Mᵈᵐᵃ
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.normalSpace`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologi
calSpace X] [inst_1 : TopologicalSpace Y] [NormalSpace X] (h : X ≃ₜ Y),   Normal
Space Y
-/
instance instNormalSpace [NormalSpace M] : NormalSpace Mᵈᵐᵃ := mkHomeomorph.normalSpace

@[to_additive]
/-
**DomMulAct.instCompletelyNormalSpace** 是 Mathlib 中的一个实例，位于命名空间 `DomMulAct`。
形式化陈述：instCompletelyNormalSpace [CompletelyNormalSpace M] : CompletelyNormalSpac
e Mᵈᵐᵃ
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsInducing.completelyNormalSpace`：Topology.IsInducing.completel
yNormalSpace [TopologicalSpace Y] [CompletelyNormalSpace Y] {e : X -> Y} (he : I
sInducing e) : CompletelyNormal…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Topology.IsEmbedding.toIsInducing`：∀ {X : Type u_1} {Y : Type u_2} [tX :
 TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbeddi
ng f → Topology.IsInduc…
· 使用定理 `DomMulAct.isEmbedding_mk_symm`：∀ {M : Type u_1} [inst : TopologicalSpace
 M], Topology.IsEmbedding ⇑DomMulAct.mk.symm
-/
instance instCompletelyNormalSpace [CompletelyNormalSpace M] : CompletelyNormalSpace Mᵈᵐᵃ :=
  isEmbedding_mk_symm.completelyNormalSpace

@[to_additive]
/-
**DomMulAct.instDiscreteTopology** 是 Mathlib 中的一个实例，位于命名空间 `DomMulAct`。
形式化陈述：instDiscreteTopology [DiscreteTopology M] : DiscreteTopology Mᵈᵐᵃ
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.discreteTopology`：∀ {X : Type u_1} {Y : Type u_2} {
f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   [Discrete
Topology Y], Topology.IsEmb…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `DomMulAct.isEmbedding_mk_symm`：∀ {M : Type u_1} [inst : TopologicalSpace
 M], Topology.IsEmbedding ⇑DomMulAct.mk.symm
-/
instance instDiscreteTopology [DiscreteTopology M] : DiscreteTopology Mᵈᵐᵃ :=
  isEmbedding_mk_symm.discreteTopology

@[to_additive]
/-
**DomMulAct.instSeparableSpace** 是 Mathlib 中的一个实例，位于命名空间 `DomMulAct`。
形式化陈述：instSeparableSpace [SeparableSpace M] : SeparableSpace Mᵈᵐᵃ
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsQuotientMap.separableSpace`：∀ {α : Type u} {β : Type u_1} [t 
: TopologicalSpace α] [TopologicalSpace.SeparableSpace α] [inst : TopologicalSpa
ce β]   {f : α → β}, Topolo…
· 使用定理 `DomMulAct.isQuotientMap_mk`：∀ {M : Type u_1} [inst : TopologicalSpace M]
, Topology.IsQuotientMap ⇑DomMulAct.mk
-/
instance instSeparableSpace [SeparableSpace M] : SeparableSpace Mᵈᵐᵃ :=
  isQuotientMap_mk.separableSpace

@[to_additive]
/-
**DomMulAct.instFirstCountableTopology** 是 Mathlib 中的一个实例，位于命名空间 `DomMulAct`。
形式化陈述：instFirstCountableTopology [FirstCountableTopology M] : FirstCountableTopo
logy Mᵈᵐᵃ
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsInducing.firstCountableTopology`：∀ {α : Type u} [t : Topologi
calSpace α] {β : Type u_1} [inst : TopologicalSpace β] [FirstCountableTopology β
]   {f : α → β}, Topology.IsIndu…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `DomMulAct.isInducing_mk_symm`：∀ {M : Type u_1} [inst : TopologicalSpace 
M], Topology.IsInducing ⇑DomMulAct.mk.symm
-/
instance instFirstCountableTopology [FirstCountableTopology M] : FirstCountableTopology Mᵈᵐᵃ :=
  isInducing_mk_symm.firstCountableTopology

@[to_additive]
/-
**DomMulAct.instSecondCountableTopology** 是 Mathlib 中的一个实例，位于命名空间 `DomMulAct`。
形式化陈述：instSecondCountableTopology [SecondCountableTopology M] : SecondCountableT
opology Mᵈᵐᵃ
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsInducing.secondCountableTopology`：∀ {α : Type u_1} {β : Type 
u_2} [inst : TopologicalSpace α] {f : α → β} [inst_1 : TopologicalSpace β]   [Se
condCountableTopology β], Topolog…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `DomMulAct.isInducing_mk_symm`：∀ {M : Type u_1} [inst : TopologicalSpace 
M], Topology.IsInducing ⇑DomMulAct.mk.symm
-/
instance instSecondCountableTopology [SecondCountableTopology M] : SecondCountableTopology Mᵈᵐᵃ :=
  isInducing_mk_symm.secondCountableTopology

@[to_additive]
/-
**DomMulAct.instCompactSpace** 是 Mathlib 中的一个实例，位于命名空间 `DomMulAct`。
形式化陈述：instCompactSpace [CompactSpace M] : CompactSpace Mᵈᵐᵃ
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.compactSpace`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolog
icalSpace X] [inst_1 : TopologicalSpace Y] [CompactSpace X] (h : X ≃ₜ Y),   Comp
actSpace Y
-/
instance instCompactSpace [CompactSpace M] : CompactSpace Mᵈᵐᵃ :=
  mkHomeomorph.compactSpace

@[to_additive]
/-
**DomMulAct.instLocallyCompactSpace** 是 Mathlib 中的一个实例，位于命名空间 `DomMulAct`。
形式化陈述：instLocallyCompactSpace [LocallyCompactSpace M] : LocallyCompactSpace Mᵈᵐᵃ
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsOpenEmbedding.locallyCompactSpace`：∀ {X : Type u_1} {Y : Type
 u_2} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y] [LocallyCompactS
pace Y]   {f : X → Y}, Topology.Is…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `DomMulAct.isOpenEmbedding_mk_symm`：isOpenEmbedding_mk_symm : IsOpenEmbed
ding (@mk M).symm
-/
instance instLocallyCompactSpace [LocallyCompactSpace M] : LocallyCompactSpace Mᵈᵐᵃ :=
  isOpenEmbedding_mk_symm.locallyCompactSpace

@[to_additive]
/-
**DomMulAct.instWeaklyLocallyCompactSpace** 是 Mathlib 中的一个实例，位于命名空间 `DomMulAct`。
形式化陈述：instWeaklyLocallyCompactSpace [WeaklyLocallyCompactSpace M] : WeaklyLocall
yCompactSpace Mᵈᵐᵃ
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsClosedEmbedding.weaklyLocallyCompactSpace`：∀ {X : Type u_1} {
Y : Type u_2} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y] [WeaklyL
ocallyCompactSpace Y]   {f : X → Y}, Topol…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `DomMulAct.isClosedEmbedding_mk_symm`：isClosedEmbedding_mk_symm : IsClose
dEmbedding (@mk M).symm
-/
instance instWeaklyLocallyCompactSpace [WeaklyLocallyCompactSpace M] :
    WeaklyLocallyCompactSpace Mᵈᵐᵃ :=
  isClosedEmbedding_mk_symm.weaklyLocallyCompactSpace

@[to_additive (attr := simp)]
/-
**DomMulAct.map_mk_nhds** 是 Mathlib 中的一个定理，位于命名空间 `DomMulAct`。
形式化陈述：map_mk_nhds (x : M) : map (mk : M -> Mᵈᵐᵃ) (𝓝 x) = 𝓝 (mk x)
参数：x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.map_nhds_eq`：map_nhds_eq (h : X ≃ₜ Y) (x : X) : map h (𝓝 x) =
 𝓝 (h x)
-/
theorem map_mk_nhds (x : M) : map (mk : M → Mᵈᵐᵃ) (𝓝 x) = 𝓝 (mk x) :=
  mkHomeomorph.map_nhds_eq x

@[to_additive (attr := simp)]
/-
**DomMulAct.map_mk_symm_nhds** 是 Mathlib 中的一个定理，位于命名空间 `DomMulAct`。
形式化陈述：map_mk_symm_nhds (x : Mᵈᵐᵃ) : map (mk.symm : Mᵈᵐᵃ -> M) (𝓝 x) = 𝓝 (mk.symm
 x)
参数：x : Mᵈᵐᵃ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.map_nhds_eq`：map_nhds_eq (h : X ≃ₜ Y) (x : X) : map h (𝓝 x) =
 𝓝 (h x)
-/
theorem map_mk_symm_nhds (x : Mᵈᵐᵃ) : map (mk.symm : Mᵈᵐᵃ → M) (𝓝 x) = 𝓝 (mk.symm x) :=
  mkHomeomorph.symm.map_nhds_eq x

@[to_additive (attr := simp)]
/-
**DomMulAct.comap_mk_nhds** 是 Mathlib 中的一个定理，位于命名空间 `DomMulAct`。
形式化陈述：comap_mk_nhds (x : Mᵈᵐᵃ) : comap (mk : M -> Mᵈᵐᵃ) (𝓝 x) = 𝓝 (mk.symm x)
参数：x : Mᵈᵐᵃ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.comap_nhds_eq`：comap_nhds_eq (h : X ≃ₜ Y) (y : Y) : comap h (
𝓝 y) = 𝓝 (h.symm y)
-/
theorem comap_mk_nhds (x : Mᵈᵐᵃ) : comap (mk : M → Mᵈᵐᵃ) (𝓝 x) = 𝓝 (mk.symm x) :=
  mkHomeomorph.comap_nhds_eq x

@[to_additive (attr := simp)]
/-
**DomMulAct.comap_mk.symm_nhds** 是 Mathlib 中的一个定理，位于命名空间 `DomMulAct.comap_mk`。
形式化陈述：∀ {M : Type u_1} [inst : TopologicalSpace M] (x : M), Filter.comap (⇑DomMu
lAct.mk.symm) (nhds x) = nhds (DomMulAct.mk x)
参数：x : M；⇑DomMulAct.mk.symm；nhds x；DomMulAct.mk x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.comap_nhds_eq`：comap_nhds_eq (h : X ≃ₜ Y) (y : Y) : comap h (
𝓝 y) = 𝓝 (h.symm y)
-/
theorem comap_mk.symm_nhds (x : M) : comap (mk.symm : Mᵈᵐᵃ → M) (𝓝 x) = 𝓝 (mk x) :=
  mkHomeomorph.symm.comap_nhds_eq x

end DomMulAct

