/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Alex Kontorovich, Heather Macbeth
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Measure.Haar.Quotient
public import Mathlib.Topology.Algebra.Order.Floor

/-!
# Integrals of periodic functions

In this file we prove that the half-open interval `Ioc t (t + T)` in `ℝ` is a fundamental domain of
the action of the subgroup `ℤ ∙ T` on `ℝ`.

A consequence is `AddCircle.measurePreserving_mk`: the covering map from `ℝ` to the "additive
circle" `ℝ ⧸ (ℤ ∙ T)` is measure-preserving, with respect to the restriction of Lebesgue measure to
`Ioc t (t + T)` (upstairs) and with respect to Haar measure (downstairs).

Another consequence (`Function.Periodic.intervalIntegral_add_eq` and related declarations) is that
`∫ x in t..t + T, f x = ∫ x in s..s + T, f x` for any (not necessarily measurable) function with
period `T`.
-/

@[expose] public section

open Set Function MeasureTheory MeasureTheory.Measure TopologicalSpace AddSubgroup intervalIntegral

open scoped MeasureTheory NNReal ENNReal

/-!
## Measures and integrability on ℝ and on the circle
-/

@[fun_prop]
/-
**AddCircle.measurable_mk'** 是 Mathlib 中的一个定理，位于命名空间 `AddCircle`。
形式化陈述：∀ {a : ℝ}, Measurable QuotientAddGroup.mk
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.measurable`：Continuous.measurable {f : α -> γ} (hf : Continuo
us f) : Measurable f
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `QuotientAddGroup.borelSpace`：∀ {G : Type u_3} [inst : TopologicalSpace G
] [PolishSpace G] [inst_2 : AddGroup G] [IsTopologicalAddGroup G]   [inst_4 : Me
asurableSpace G] …
· 使用定理 `instPolishSpaceOfSeparableSpaceOfIsCompletelyMetrizableSpace`：∀ {α : Typ
e u_1} [inst : TopologicalSpace α] [TopologicalSpace.SeparableSpace α]   [Topolo
gicalSpace.IsCompletelyMetrizableSpace α], PolishS…
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `TopologicalSpace.IsCompletelyMetrizableSpace.of_completeSpace_metrizable
`：∀ {X : Type u_1} [inst : UniformSpace X] [CompleteSpace X] [(uniformity X).IsC
ountablyGenerated] [T0Space X],   TopologicalSpace.IsCompletel…
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `T6Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T6
Space X], T0Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `AddSubgroup.normal_of_isAddCommutative`：∀ {G : Type u_1} [inst : AddGrou
p G] [IsAddCommutative G] (H : AddSubgroup G), H.Normal
· 使用定理 `AddCommMagma.to_isCommutative`：∀ {G : Type u_1} [inst : AddCommMagma G],
 IsAddCommutative G
· 使用定理 `AddSubgroup.isClosed_of_discrete`：∀ {G : Type u_1} [inst : AddGroup G] [
inst_1 : TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G]   {H : AddSub
group G} [DiscreteTopo…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `Int.instDiscreteTopologySubtypeRealMemAddSubgroupZmultiples`：∀ {a : ℝ}, 
DiscreteTopology ↥(AddSubgroup.zmultiples a)
· 使用定理 `AddCircle.continuous_mk'`：∀ {𝕜 : Type u_1} [inst : AddCommGroup 𝕜] (p : 
𝕜) [inst_1 : TopologicalSpace 𝕜],   Continuous ⇑(QuotientAddGroup.mk' (AddSubgro
up.zmultiples …

--- 原说明 ---
## Measures and integrability on ℝ and on the circle
-/
protected theorem AddCircle.measurable_mk' {a : ℝ} :
    Measurable (β := AddCircle a) ((↑) : ℝ → AddCircle a) :=
  Continuous.measurable <| AddCircle.continuous_mk' a
/-
**isAddFundamentalDomain_Ioc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isAddFundamentalDomain_Ioc {T : Real} (hT : 0 < T) (t : Real) (μ : Measure
 Real
参数：hT : 0 < T；t : Real。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IsAddFundamentalDomain.mk'`：∀ {G : Type u_1} {α : Type u_3
} [inst : AddGroup G] [inst_1 : AddAction G α] [inst_2 : MeasurableSpace α] {s :
 Set α}   {μ : MeasureTheory.M…
· 使用定理 `nullMeasurableSet_Ioc`：nullMeasurableSet_Ioc [ClosedIicTopology α] : Nul
lMeasurableSet (Ioc a b) μ
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `Equiv.bijective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Bijec
tive ⇑e
· 使用定理 `StrictMono.injective`：StrictMono.injective (hf : StrictMono f) : Injecti
ve f
· 使用定理 `zsmul_left_strictMono`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 
: PartialOrder α] [IsOrderedAddMonoid α] {a : α},   0 < a → StrictMono fun n => 
n • a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.Bijective.existsUnique_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f 
: α → β}, Function.Bijective f → ∀ {p : β → Prop}, (∃! y, p y) ↔ ∃! x, p (f x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `existsUnique_add_zsmul_mem_Ioc`：∀ {G : Type u_1} [inst : AddCommGroup G]
 [inst_1 : LinearOrder G] [IsOrderedAddMonoid G] [Archimedean G] {a : G},   0 < 
a → ∀ (b c : G), ∃! …
-/
theorem isAddFundamentalDomain_Ioc {T : ℝ} (hT : 0 < T) (t : ℝ)
    (μ : Measure ℝ := by volume_tac) :
    IsAddFundamentalDomain (AddSubgroup.zmultiples T) (Ioc t (t + T)) μ := by
  refine IsAddFundamentalDomain.mk' nullMeasurableSet_Ioc fun x => ?_
  have : Bijective (codRestrict (fun n : ℤ => n • T) (AddSubgroup.zmultiples T) _) :=
    (Equiv.ofInjective (fun n : ℤ => n • T) (zsmul_left_strictMono hT).injective).bijective
  refine this.existsUnique_iff.2 ?_
  simpa only [add_comm x] using! existsUnique_add_zsmul_mem_Ioc hT x t
/-
**isAddFundamentalDomain_Ioc'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isAddFundamentalDomain_Ioc' {T : Real} (hT : 0 < T) (t : Real) (μ : Measur
e Real
参数：hT : 0 < T；t : Real。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IsAddFundamentalDomain.mk'`：∀ {G : Type u_1} {α : Type u_3
} [inst : AddGroup G] [inst_1 : AddAction G α] [inst_2 : MeasurableSpace α] {s :
 Set α}   {μ : MeasureTheory.M…
· 使用定理 `nullMeasurableSet_Ioc`：nullMeasurableSet_Ioc [ClosedIicTopology α] : Nul
lMeasurableSet (Ioc a b) μ
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `Equiv.bijective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Bijec
tive ⇑e
· 使用定理 `StrictMono.injective`：StrictMono.injective (hf : StrictMono f) : Injecti
ve f
· 使用定理 `zsmul_left_strictMono`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 
: PartialOrder α] [IsOrderedAddMonoid α] {a : α},   0 < a → StrictMono fun n => 
n • a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.Bijective.existsUnique_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f 
: α → β}, Function.Bijective f → ∀ {p : β → Prop}, (∃! y, p y) ↔ ∃! x, p (f x)
· 使用定理 `Function.Bijective.comp`：∀ {α : Sort u₁} {β : Sort u₂} {φ : Sort u₃} {g 
: β → φ} {f : α → β},   Function.Bijective g → Function.Bijective f → Function.B
ijective (g ∘…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `zsmul_eq_mul`：∀ {α : Type u_3} [inst : NonAssocRing α] (a : α) (n : ℤ), 
n • a = ↑n * a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.codRestrict.congr_simp`：∀ {α : Type u_1} {ι : Sort u_5} (f f_1 : ι →
 α) (e_f : f = f_1) (s : Set α) (h : ∀ (x : ι), f x ∈ s) (a a_1 : ι),   a = a_1 
→ Set.codRestric…
· 使用定理 `existsUnique_add_zsmul_mem_Ioc`：∀ {G : Type u_1} [inst : AddCommGroup G]
 [inst_1 : LinearOrder G] [IsOrderedAddMonoid G] [Archimedean G] {a : G},   0 < 
a → ∀ (b c : G), ∃! …
-/
theorem isAddFundamentalDomain_Ioc' {T : ℝ} (hT : 0 < T) (t : ℝ) (μ : Measure ℝ := by volume_tac) :
    IsAddFundamentalDomain (AddSubgroup.op <| .zmultiples T) (Ioc t (t + T)) μ := by
  refine IsAddFundamentalDomain.mk' nullMeasurableSet_Ioc fun x => ?_
  have : Bijective (codRestrict (fun n : ℤ => n • T) (AddSubgroup.zmultiples T) _) :=
    (Equiv.ofInjective (fun n : ℤ => n • T) (zsmul_left_strictMono hT).injective).bijective
  refine (AddSubgroup.equivOp _).bijective.comp this |>.existsUnique_iff.2 ?_
  simpa using! existsUnique_add_zsmul_mem_Ioc hT x t

namespace AddCircle

variable (T : ℝ) [hT : Fact (0 < T)]

/-- Equip the "additive circle" `ℝ ⧸ (ℤ ∙ T)` with, as a standard measure, the Haar measure of total
mass `T` -/
/-
**AddCircle.measureSpace** 是 Mathlib 中的一个实例，位于命名空间 `AddCircle`。
形式化陈述：measureSpace : MeasureSpace (AddCircle T)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Equip the "additive circle" `ℝ ⧸ (ℤ ∙ T)` with, as a standard measure, the Haar 
measure of total
mass `T`
-/
noncomputable instance measureSpace : MeasureSpace (AddCircle T) :=
  { QuotientAddGroup.measurableSpace _ with volume := ENNReal.ofReal T • addHaarMeasure ⊤ }

@[simp]
/-
**AddCircle.measure_univ** 是 Mathlib 中的一个定理，位于命名空间 `AddCircle`。
形式化陈述：∀ (T : ℝ) [hT : Fact (0 < T)], MeasureTheory.volume Set.univ = ENNReal.ofR
eal T
参数：T : ℝ；0 < T。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `TopologicalSpace.PositiveCompacts.coe_top`：coe_top [CompactSpace α] [Non
empty α] : (↑(⊤ : PositiveCompacts α) : Set α) = univ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.Measure.addHaarMeasure_self`：∀ {G : Type u_1} [inst : AddG
roup G] [inst_1 : TopologicalSpace G] [inst_2 : IsTopologicalAddGroup G]   [inst
_3 : MeasurableSpace G] [inst_4…
· 使用定理 `AddSubgroup.normal_of_isAddCommutative`：∀ {G : Type u_1} [inst : AddGrou
p G] [IsAddCommutative G] (H : AddSubgroup G), H.Normal
· 使用定理 `AddCommMagma.to_isCommutative`：∀ {G : Type u_1} [inst : AddCommMagma G],
 IsAddCommutative G
· 使用定理 `QuotientAddGroup.instIsTopologicalAddGroup`：∀ {G : Type u_1} [inst : Top
ologicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G] (N : AddSubgrou
p G)   [inst_3 : N.Normal], IsTo…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `QuotientAddGroup.borelSpace`：∀ {G : Type u_3} [inst : TopologicalSpace G
] [PolishSpace G] [inst_2 : AddGroup G] [IsTopologicalAddGroup G]   [inst_4 : Me
asurableSpace G] …
· 使用定理 `instPolishSpaceOfSeparableSpaceOfIsCompletelyMetrizableSpace`：∀ {α : Typ
e u_1} [inst : TopologicalSpace α] [TopologicalSpace.SeparableSpace α]   [Topolo
gicalSpace.IsCompletelyMetrizableSpace α], PolishS…
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `TopologicalSpace.IsCompletelyMetrizableSpace.of_completeSpace_metrizable
`：∀ {X : Type u_1} [inst : UniformSpace X] [CompleteSpace X] [(uniformity X).IsC
ountablyGenerated] [T0Space X],   TopologicalSpace.IsCompletel…
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `T6Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T6
Space X], T0Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `AddSubgroup.isClosed_of_discrete`：∀ {G : Type u_1} [inst : AddGroup G] [
inst_1 : TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G]   {H : AddSub
group G} [DiscreteTopo…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `Int.instDiscreteTopologySubtypeRealMemAddSubgroupZmultiples`：∀ {a : ℝ}, 
DiscreteTopology ↥(AddSubgroup.zmultiples a)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem measure_univ : volume (Set.univ : Set (AddCircle T)) = ENNReal.ofReal T := by
  dsimp [volume]
  rw [← PositiveCompacts.coe_top]
  simp [addHaarMeasure_self (G := AddCircle T), -PositiveCompacts.coe_top]
/-
**AddCircle.** 是 Mathlib 中的一个实例，位于命名空间 `AddCircle`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsAddHaarMeasure (volume : Measure (AddCircle T)) :=
  IsAddHaarMeasure.smul _ (by simp [hT.out]) ENNReal.ofReal_ne_top
/-
**AddCircle.isFiniteMeasure** 是 Mathlib 中的一个实例，位于命名空间 `AddCircle`。
形式化陈述：isFiniteMeasure : IsFiniteMeasure (volume : Measure (AddCircle T)) where m
easure_univ_lt_top
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddCircle.measure_univ`：∀ (T : ℝ) [hT : Fact (0 < T)], MeasureTheory.vol
ume Set.univ = ENNReal.ofReal T
-/
instance isFiniteMeasure : IsFiniteMeasure (volume : Measure (AddCircle T)) where
  measure_univ_lt_top := by simp
/-
**AddCircle.** 是 Mathlib 中的一个实例，位于命名空间 `AddCircle`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasAddFundamentalDomain (AddSubgroup.op <| .zmultiples T) ℝ where
  ExistsIsAddFundamentalDomain := ⟨Ioc 0 (0 + T), isAddFundamentalDomain_Ioc' Fact.out 0⟩
/-
**AddCircle.** 是 Mathlib 中的一个实例，位于命名空间 `AddCircle`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddQuotientMeasureEqMeasurePreimage volume (volume : Measure (AddCircle T)) := by
  apply MeasureTheory.leftInvariantIsAddQuotientMeasureEqMeasurePreimage
  simp [(isAddFundamentalDomain_Ioc' hT.out 0).covolume_eq_volume, AddCircle.measure_univ]

/-- The covering map from `ℝ` to the "additive circle" `ℝ ⧸ (ℤ ∙ T)` is measure-preserving,
considered with respect to the standard measure (defined to be the Haar measure of total mass `T`)
on the additive circle, and with respect to the restriction of Lebesgue measure on `ℝ` to an
interval $(t, t + T]$. -/
/-
**AddCircle.measurePreserving_mk** 是 Mathlib 中的一个定理，位于命名空间 `AddCircle`。
形式化陈述：∀ (T : ℝ) [hT : Fact (0 < T)] (t : ℝ),   MeasureTheory.MeasurePreserving Q
uotientAddGroup.mk (MeasureTheory.volume.restrict (Set.Ioc t (t + T)))     Measu
reTheory.volume
参数：T : ℝ；0 < T；t : ℝ；MeasureTheory.volume.restrict (Set.Ioc t (t + T))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `measurePreserving_quotientAddGroup_mk_of_AddQuotientMeasureEqMeasurePrei
mage`：∀ {G : Type u_1} [inst : AddGroup G] [inst_1 : MeasurableSpace G] (ν : Mea
sureTheory.Measure G) {Γ : AddSubgroup G}   {𝓕 : Set G},   Measure…
· 使用定理 `isAddFundamentalDomain_Ioc'`：isAddFundamentalDomain_Ioc' {T : Real} (hT 
: 0 < T) (t : Real) (μ : Measure Real
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `AddCircle.instAddQuotientMeasureEqMeasurePreimageSubtypeAddOppositeRealM
emAddSubgroupOpZmultiplesVolume`：∀ (T : ℝ) [hT : Fact (0 < T)],   MeasureTheory.
AddQuotientMeasureEqMeasurePreimage MeasureTheory.volume MeasureTheory.volume

--- 原说明 ---
The covering map from `ℝ` to the "additive circle" `ℝ ⧸ (ℤ ∙ T)` is measure-pres
erving,
considered with respect to the standard measure (defined to be the Haar measure 
of total mass `T`)
on the additive circle, and with respect to the restriction of Lebesgue measure 
on `ℝ` to an
interval $(t, t + T]$.
-/
protected theorem measurePreserving_mk (t : ℝ) :
    MeasurePreserving (β := AddCircle T) ((↑) : ℝ → AddCircle T)
      (volume.restrict (Ioc t (t + T))) :=
  measurePreserving_quotientAddGroup_mk_of_AddQuotientMeasureEqMeasurePreimage
    volume (𝓕 := Ioc t (t + T)) (isAddFundamentalDomain_Ioc' hT.out _) _
/-
**AddCircle.add_projection_respects_measure** 是 Mathlib 中的一个引理，位于命名空间 `AddCircle
`。
形式化陈述：add_projection_respects_measure (t : Real) {U : Set (AddCircle T)} (meas_U
 : MeasurableSet U) : volume U = volume (QuotientAddGroup.mk ⁻¹' U inter (Ioc t 
(t + T)))
参数：t : Real；AddCircle T；meas_U : MeasurableSet U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IsAddFundamentalDomain.addProjection_respects_measure_appl
y`：∀ {G : Type u_1} {α : Type u_3} [inst : AddGroup G] [inst_1 : AddAction G α] 
[inst_2 : MeasurableSpace α]   {ν : MeasureTheory.Measure α} (μ…
· 使用定理 `AddCircle.instAddQuotientMeasureEqMeasurePreimageSubtypeAddOppositeRealM
emAddSubgroupOpZmultiplesVolume`：∀ (T : ℝ) [hT : Fact (0 < T)],   MeasureTheory.
AddQuotientMeasureEqMeasurePreimage MeasureTheory.volume MeasureTheory.volume
· 使用定理 `isAddFundamentalDomain_Ioc'`：isAddFundamentalDomain_Ioc' {T : Real} (hT 
: 0 < T) (t : Real) (μ : Measure Real
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
-/
lemma add_projection_respects_measure (t : ℝ) {U : Set (AddCircle T)} (meas_U : MeasurableSet U) :
    volume U = volume (QuotientAddGroup.mk ⁻¹' U ∩ (Ioc t (t + T))) :=
  (isAddFundamentalDomain_Ioc' hT.out _).addProjection_respects_measure_apply
    (volume : Measure (AddCircle T)) meas_U
/-
**AddCircle.volume_closedBall** 是 Mathlib 中的一个定理，位于命名空间 `AddCircle`。
形式化陈述：volume_closedBall {x : AddCircle T} (ε : Real) : volume (Metric.closedBall
 x ε) = ENNReal.ofReal (min T (2 * ε))
参数：ε : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `abs_eq_self`：∀ {G : Type u_1} [inst : AddCommGroup G] [inst_1 : LinearOr
der G] [IsOrderedAddMonoid G] {a : G}, |a| = a ↔ 0 ≤ a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.inter_eq_left`：∀ {α : Type u} {s t : Set α}, s ∩ t = s ↔ s ⊆ t
· 使用定理 `Real.closedBall_eq_Icc`：Real.closedBall_eq_Icc {x r : Real} : closedBall
 x r = Icc (x - r) (x + r)
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
（共 117 条，此处仅展示前 30 条）
-/
theorem volume_closedBall {x : AddCircle T} (ε : ℝ) :
    volume (Metric.closedBall x ε) = ENNReal.ofReal (min T (2 * ε)) := by
  have hT' : |T| = T := abs_eq_self.mpr hT.out.le
  let I := Ioc (-(T / 2)) (T / 2)
  have h₁ : ε < T / 2 → Metric.closedBall (0 : ℝ) ε ∩ I = Metric.closedBall (0 : ℝ) ε := by
    intro hε
    rw [inter_eq_left, Real.closedBall_eq_Icc, zero_sub, zero_add]
    rintro y ⟨hy₁, hy₂⟩; constructor <;> linarith
  have h₂ : (↑) ⁻¹' Metric.closedBall (0 : AddCircle T) ε ∩ I =
      if ε < T / 2 then Metric.closedBall (0 : ℝ) ε else I := by
    conv_rhs => rw [← if_ctx_congr (Iff.rfl : ε < T / 2 ↔ ε < T / 2) h₁ fun _ => rfl, ← hT']
    apply coe_real_preimage_closedBall_inter_eq
    simpa only [hT', Real.closedBall_eq_Icc, zero_add, zero_sub] using Ioc_subset_Icc_self
  rw [addHaar_closedBall_center, add_projection_respects_measure T (-(T / 2))
    measurableSet_closedBall, (by linarith : -(T / 2) + T = T / 2), h₂]
  by_cases hε : ε < T / 2
  · simp [hε, min_eq_right (by linarith : 2 * ε ≤ T)]
  · simp [I, hε, min_eq_left (by linarith : T ≤ 2 * ε)]
/-
**AddCircle.** 是 Mathlib 中的一个实例，位于命名空间 `AddCircle`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsUnifLocDoublingMeasure (volume : Measure (AddCircle T)) := by
  refine ⟨⟨Real.toNNReal 2, Filter.Eventually.of_forall fun ε x => ?_⟩⟩
  rw [volume_closedBall, volume_closedBall, ENNReal.ofNNReal_toNNReal 2,
    ← ENNReal.ofReal_mul zero_le_two]
  apply ENNReal.ofReal_le_ofReal
  rw [mul_min_of_nonneg _ _ (zero_le_two : (0 : ℝ) ≤ 2)]
  exact min_le_min (by linarith [hT.out]) (le_refl _)

/-- The isomorphism `AddCircle T ≃ Ioc a (a + T)` whose inverse is the natural quotient map,
  as an equivalence of measurable spaces. -/
/-
**AddCircle.measurableEquivIoc** 是 Mathlib 中的一个定义，位于命名空间 `AddCircle`。
形式化陈述：measurableEquivIoc (a : Real) : AddCircle T ≃ᵐ Ioc a (a + T) where toEquiv
参数：a : Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism `AddCircle T ≃ Ioc a (a + T)` whose inverse is the natural quoti
ent map,
  as an equivalence of measurable spaces.
-/
noncomputable def measurableEquivIoc (a : ℝ) : AddCircle T ≃ᵐ Ioc a (a + T) where
  toEquiv := equivIoc T a
  measurable_toFun := measurable_of_measurable_on_compl_singleton _
    (continuousOn_iff_continuous_domRestrict.mp <| continuousOn_of_forall_continuousAt fun _x hx =>
      continuousAt_equivIoc T a hx).measurable
  measurable_invFun := AddCircle.measurable_mk'.comp measurable_subtype_coe

/-- The isomorphism `AddCircle T ≃ Ico a (a + T)` whose inverse is the natural quotient map,
  as an equivalence of measurable spaces. -/
/-
**AddCircle.measurableEquivIco** 是 Mathlib 中的一个定义，位于命名空间 `AddCircle`。
形式化陈述：measurableEquivIco (a : Real) : AddCircle T ≃ᵐ Ico a (a + T) where toEquiv
参数：a : Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism `AddCircle T ≃ Ico a (a + T)` whose inverse is the natural quoti
ent map,
  as an equivalence of measurable spaces.
-/
noncomputable def measurableEquivIco (a : ℝ) : AddCircle T ≃ᵐ Ico a (a + T) where
  toEquiv := equivIco T a
  measurable_toFun := measurable_of_measurable_on_compl_singleton _
    (continuousOn_iff_continuous_domRestrict.mp <| continuousOn_of_forall_continuousAt fun _x hx =>
      continuousAt_equivIco T a hx).measurable
  measurable_invFun := AddCircle.measurable_mk'.comp measurable_subtype_coe

/-- The equivalence `equivIoc` is measure preserving with respect to the natural volume measures. -/
/-
**AddCircle.measurePreserving_equivIoc** 是 Mathlib 中的一个引理，位于命名空间 `AddCircle`。
形式化陈述：measurePreserving_equivIoc {a : Real} : MeasurePreserving (equivIoc T a) v
olume (Measure.comap Subtype.val volume)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableEquiv.measurable`：∀ {α : Type u_1} {β : Type u_2} [inst : Meas
urableSpace α] [inst_1 : MeasurableSpace β] (e : α ≃ᵐ β), Measurable ⇑e
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.comap_apply`：comap_apply (f : α -> β) (hfi : Injec
tive f) (hf : forall s, MeasurableSet s -> MeasurableSet (f '' s)) (μ : Measure 
β) (hs : MeasurableSet …
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `MeasurableSet.subtype_image`：MeasurableSet.subtype_image {s : Set α} {t 
: Set s} (hs : MeasurableSet s) : MeasurableSet t -> MeasurableSet (((↑) : s -> 
α) '' t)
· 使用定理 `measurableSet_Ioc`：measurableSet_Ioc [ClosedIicTopology α] : MeasurableS
et (Ioc a b)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `MeasureTheory.Measure.map_apply`：map_apply (hf : Measurable f) {s : Set 
β} (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)
· 使用引理 `AddCircle.add_projection_respects_measure`：add_projection_respects_measu
re (t : Real) {U : Set (AddCircle T)} (meas_U : MeasurableSet U) : volume U = vo
lume (QuotientAddGroup.mk ⁻¹' U…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
· 使用定理 `exists_prop`：∀ {b a : Prop}, (∃ (_ : a), b) ↔ a ∧ b
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `AddCircle.equivIoc_coe_eq`：equivIoc_coe_eq {x : 𝕜} (hx : x in Ioc a (a +
 p)) : (equivIoc p a) x = ⟨x, hx⟩
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf

--- 原说明 ---
The equivalence `equivIoc` is measure preserving with respect to the natural vol
ume measures.
-/
lemma measurePreserving_equivIoc {a : ℝ} :
    MeasurePreserving (equivIoc T a) volume (Measure.comap Subtype.val volume) := by
  have h := (measurableEquivIoc T a).measurable
  refine ⟨h, ?_⟩
  ext s hs
  rw [comap_apply _ Subtype.val_injective (fun _ ↦ measurableSet_Ioc.subtype_image) _ hs,
    map_apply (by measurability) hs, add_projection_respects_measure T a (by exact h hs)]
  congr!
  ext x
  simp only [mem_inter_iff, mem_preimage, mem_image, Subtype.exists, exists_and_right,
    exists_eq_right]
  rw [and_comm, ← exists_prop]
  congr! with hx
  rw [equivIoc_coe_eq hx]

set_option backward.isDefEq.respectTransparency.types false in
attribute [local instance] Subtype.measureSpace in
/-- The lower integral of a function over `AddCircle T` is equal to the lower integral over an
interval $(t, t + T]$ in `ℝ` of its lift to `ℝ`. -/
/-
**AddCircle.lintegral_preimage** 是 Mathlib 中的一个定理，位于命名空间 `AddCircle`。
形式化陈述：∀ (T : ℝ) [hT : Fact (0 < T)] (t : ℝ) (f : AddCircle T → ENNReal),   ∫⁻ (a
 : ℝ) in Set.Ioc t (t + T), f ↑a = ∫⁻ (b : AddCircle T), f b
参数：T : ℝ；0 < T；t : ℝ；f : AddCircle T → ENNReal；a : ℝ；t + T；b : AddCircle T。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `measurableSet_Ioc`：measurableSet_Ioc [ClosedIicTopology α] : MeasurableS
et (Ioc a b)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `MeasureTheory.lintegral_map_equiv`：lintegral_map_equiv (f : β -> Real>=0
∞) (g : α ≃ᵐ β) : ∫⁻ a, f a ∂map g μ = ∫⁻ a, f (g a) ∂μ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.MeasurePreserving.map_eq`：∀ {α : Type u_1} {β : Type u_2} 
[inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β}   {μa : auto
Param (MeasureTheory.Measure…
· 使用定理 `AddCircle.measurePreserving_mk`：∀ (T : ℝ) [hT : Fact (0 < T)] (t : ℝ),  
 MeasureTheory.MeasurePreserving QuotientAddGroup.mk (MeasureTheory.volume.restr
ict (Set.Ioc t (t + …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `map_comap_subtype_coe`：map_comap_subtype_coe {m0 : MeasurableSpace α} {s
 : Set α} (hs : MeasurableSet s) (μ : Measure α) : (comap (↑) μ).map ((↑) : s ->
 α) = μ.res…
· 使用定理 `MeasurableEmbedding.lintegral_map`：∀ {α : Type u_1} {β : Type u_2} [inst
 : MeasurableSpace α] [inst_1 : MeasurableSpace β] {μ : MeasureTheory.Measure α}
   {g : α → β},   Measu…
· 使用定理 `MeasurableEmbedding.subtype_coe`：subtype_coe (hs : MeasurableSet s) : Me
asurableEmbedding ((↑) : s -> α) where injective
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.Measure.map_map`：map_map {g : β -> γ} {f : α -> β} (hg : M
easurable g) (hf : Measurable f) : (μ.map f).map g = μ.map (g ∘ f)
· 使用定理 `AddCircle.measurable_mk'`：∀ {a : ℝ}, Measurable QuotientAddGroup.mk
· 使用定理 `measurable_subtype_coe`：measurable_subtype_coe {p : α -> Prop} : Measura
ble ((↑) : Subtype p -> α)

--- 原说明 ---
The lower integral of a function over `AddCircle T` is equal to the lower integr
al over an
interval $(t, t + T]$ in `ℝ` of its lift to `ℝ`.
-/
protected theorem lintegral_preimage (t : ℝ) (f : AddCircle T → ℝ≥0∞) :
    (∫⁻ a in Ioc t (t + T), f a) = ∫⁻ b : AddCircle T, f b := by
  have m : MeasurableSet (Ioc t (t + T)) := measurableSet_Ioc
  have := lintegral_map_equiv (μ := volume) f (measurableEquivIoc T t).symm
  simp only [measurableEquivIoc, equivIoc, QuotientAddGroup.equivIocMod, MeasurableEquiv.symm_mk,
    MeasurableEquiv.coe_mk, Equiv.coe_fn_symm_mk] at this
  rw [← (AddCircle.measurePreserving_mk T t).map_eq]
  convert! this.symm using 1
  · rw [← map_comap_subtype_coe m _]
    exact MeasurableEmbedding.lintegral_map (MeasurableEmbedding.subtype_coe m) _
  · congr 1
    have : ((↑) : Ioc t (t + T) → AddCircle T) = ((↑) : ℝ → AddCircle T) ∘ ((↑) : _ → ℝ) := by
      ext1 x; rfl
    simp_rw [this]
    rw [← map_map AddCircle.measurable_mk' measurable_subtype_coe, ← map_comap_subtype_coe m]
    rfl

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

set_option backward.isDefEq.respectTransparency.types false in
attribute [local instance] Subtype.measureSpace in
/-- The integral of an almost-everywhere strongly measurable function over `AddCircle T` is equal
to the integral over an interval $(t, t + T]$ in `ℝ` of its lift to `ℝ`. -/
/-
**AddCircle.integral_preimage** 是 Mathlib 中的一个定理，位于命名空间 `AddCircle`。
形式化陈述：∀ (T : ℝ) [hT : Fact (0 < T)] {E : Type u_1} [inst : NormedAddCommGroup E]
 [inst_1 : NormedSpace ℝ E] (t : ℝ)   (f : AddCircle T → E), ∫ (a : ℝ) in Set.Io
c t (t + T), f ↑a = ∫ (b : AddCircle T), f b
参数：T : ℝ；0 < T；t : ℝ；f : AddCircle T → E；a : ℝ；t + T；b : AddCircle T。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `measurableSet_Ioc`：measurableSet_Ioc [ClosedIicTopology α] : MeasurableS
et (Ioc a b)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `MeasureTheory.integral_map_equiv`：integral_map_equiv {β} [MeasurableSpac
e β] (e : α ≃ᵐ β) (f : β -> G) : ∫ y, f y ∂Measure.map e μ = ∫ x, f (e x) ∂μ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.MeasurePreserving.map_eq`：∀ {α : Type u_1} {β : Type u_2} 
[inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β}   {μa : auto
Param (MeasureTheory.Measure…
· 使用定理 `AddCircle.measurePreserving_mk`：∀ (T : ℝ) [hT : Fact (0 < T)] (t : ℝ),  
 MeasureTheory.MeasurePreserving QuotientAddGroup.mk (MeasureTheory.volume.restr
ict (Set.Ioc t (t + …
· 使用定理 `MeasureTheory.integral_subtype`：integral_subtype {α} [MeasureSpace α] {s
 : Set α} (hs : MeasurableSet s) (f : α -> G) : ∫ x : s, f x = ∫ x in s, f x
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.Measure.map_map`：map_map {g : β -> γ} {f : α -> β} (hg : M
easurable g) (hf : Measurable f) : (μ.map f).map g = μ.map (g ∘ f)
· 使用定理 `AddCircle.measurable_mk'`：∀ {a : ℝ}, Measurable QuotientAddGroup.mk
· 使用定理 `measurable_subtype_coe`：measurable_subtype_coe {p : α -> Prop} : Measura
ble ((↑) : Subtype p -> α)
· 使用定理 `map_comap_subtype_coe`：map_comap_subtype_coe {m0 : MeasurableSpace α} {s
 : Set α} (hs : MeasurableSet s) (μ : Measure α) : (comap (↑) μ).map ((↑) : s ->
 α) = μ.res…

--- 原说明 ---
The integral of an almost-everywhere strongly measurable function over `AddCircl
e T` is equal
to the integral over an interval $(t, t + T]$ in `ℝ` of its lift to `ℝ`.
-/
protected theorem integral_preimage (t : ℝ) (f : AddCircle T → E) :
    (∫ a in Ioc t (t + T), f a) = ∫ b : AddCircle T, f b := by
  have m : MeasurableSet (Ioc t (t + T)) := measurableSet_Ioc
  have := integral_map_equiv (μ := volume) (measurableEquivIoc T t).symm f
  simp only [measurableEquivIoc, equivIoc, QuotientAddGroup.equivIocMod, MeasurableEquiv.symm_mk,
    MeasurableEquiv.coe_mk, Equiv.coe_fn_symm_mk] at this
  rw [← (AddCircle.measurePreserving_mk T t).map_eq, ← integral_subtype m, ← this]
  have : ((↑) : Ioc t (t + T) → AddCircle T) = ((↑) : ℝ → AddCircle T) ∘ ((↑) : _ → ℝ) := by
    ext1 x; rfl
  simp_rw [this]
  rw [← map_map AddCircle.measurable_mk' measurable_subtype_coe, ← map_comap_subtype_coe m]
  rfl

/-- The integral of an almost-everywhere strongly measurable function over `AddCircle T` is equal
to the integral over an interval $(t, t + T]$ in `ℝ` of its lift to `ℝ`. -/
/-
**AddCircle.intervalIntegral_preimage** 是 Mathlib 中的一个定理，位于命名空间 `AddCircle`。
形式化陈述：∀ (T : ℝ) [hT : Fact (0 < T)] {E : Type u_1} [inst : NormedAddCommGroup E]
 [inst_1 : NormedSpace ℝ E] (t : ℝ)   (f : AddCircle T → E), ∫ (a : ℝ) in t..t +
 T, f ↑a = ∫ (b : AddCircle T), f b
参数：T : ℝ；0 < T；t : ℝ；f : AddCircle T → E；a : ℝ；b : AddCircle T。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `intervalIntegral.integral_of_le`：integral_of_le (h : a <= b) : ∫ x in a.
.b, f x ∂μ = ∫ x in Ioc a b, f x ∂μ
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero`：∀ {R : Type u_1} [in
st : CommSemiring R] {a₁ a₂ b₁ b₂ c : R},   Mathlib.Meta.NormNum.IsNat (a₁ + b₁)
 0 → a₂ + b₂ = c → a₁ + a₂ + (b₁ + b₂) =…
· 使用定理 `Mathlib.Tactic.Ring.Common.add_overlap_pf_zero`：∀ {R : Type u_1} [inst :
 CommSemiring R] {a b : R} (x : R) (e : ℕ),   Mathlib.Meta.NormNum.IsNat (a + b)
 0 → Mathlib.Meta.NormNum.IsNat (x ^…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isInt_add`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HAdd.hAdd →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Mathlib.Tactic.Linarith.add_neg`：add_neg [IsStrictOrderedRing α] {a b : 
α} (ha : a < 0) (hb : b < 0) : a + b < 0
· 使用定理 `Mathlib.Tactic.Linarith.sub_neg_of_lt`：sub_neg_of_lt [IsOrderedRing α] {
a b : α} : a < b -> a - b < 0
（共 32 条，此处仅展示前 30 条）

--- 原说明 ---
The integral of an almost-everywhere strongly measurable function over `AddCircl
e T` is equal
to the integral over an interval $(t, t + T]$ in `ℝ` of its lift to `ℝ`.
-/
protected theorem intervalIntegral_preimage (t : ℝ) (f : AddCircle T → E) :
    ∫ a in t..t + T, f a = ∫ b : AddCircle T, f b := by
  rw [integral_of_le, AddCircle.integral_preimage T t f]
  linarith [hT.out]

/-- The integral of a function lifted to AddCircle from an interval `(t, t + T]` to `AddCircle T`
is equal to the intervalIntegral over the interval. -/
/-
**AddCircle.integral_liftIoc_eq_intervalIntegral** 是 Mathlib 中的一个引理，位于命名空间 `AddC
ircle`。
形式化陈述：integral_liftIoc_eq_intervalIntegral {t : Real} {f : Real -> E} : ∫ a, lif
tIoc T t f a = ∫ a in t..t + T, f a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AddCircle.intervalIntegral_preimage`：∀ (T : ℝ) [hT : Fact (0 < T)] {E : 
Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] (t : ℝ)   (f 
: AddCircle T → E), ∫ (a …
· 使用定理 `intervalIntegral.integral_congr_ae`：integral_congr_ae (h : forallᵐ x ∂μ,
 x in Ι a b -> f x = g x) : ∫ x in a..b, f x ∂μ = ∫ x in a..b, g x ∂μ
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `AddCircle.liftIoc_coe_apply`：liftIoc_coe_apply {f : 𝕜 -> B} {x : 𝕜} (hx 
: x in Ioc a (a + p)) : liftIoc p a f ↑x = f x
· 使用定理 `Set.uIoc_of_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a ≤ b
 → Set.uIoc a b = Set.Ioc a b
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero`：∀ {R : Type u_1} [in
st : CommSemiring R] {a₁ a₂ b₁ b₂ c : R},   Mathlib.Meta.NormNum.IsNat (a₁ + b₁)
 0 → a₂ + b₂ = c → a₁ + a₂ + (b₁ + b₂) =…
· 使用定理 `Mathlib.Tactic.Ring.Common.add_overlap_pf_zero`：∀ {R : Type u_1} [inst :
 CommSemiring R] {a b : R} (x : R) (e : ℕ),   Mathlib.Meta.NormNum.IsNat (a + b)
 0 → Mathlib.Meta.NormNum.IsNat (x ^…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isInt_add`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HAdd.hAdd →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
（共 36 条，此处仅展示前 30 条）

--- 原说明 ---
The integral of a function lifted to AddCircle from an interval `(t, t + T]` to 
`AddCircle T`
is equal to the intervalIntegral over the interval.
-/
lemma integral_liftIoc_eq_intervalIntegral {t : ℝ} {f : ℝ → E} :
    ∫ a, liftIoc T t f a = ∫ a in t..t + T, f a := by
  rw [← AddCircle.intervalIntegral_preimage T t]
  apply intervalIntegral.integral_congr_ae
  refine .of_forall fun x hx ↦ ?_
  rw [uIoc_of_le (by linarith [hT.out])] at hx
  rw [liftIoc_coe_apply hx]

end AddCircle

/-- If a function satisfies `MemLp` on the interval `(t, t + T]`, then its lift to the AddCircle
also satisfies `MemLp` with respect to the Haar measure. -/
/-
**MeasureTheory.MemLp.memLp_liftIoc** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MeasureTheory.MemLp.memLp_liftIoc {T : Real} [hT : Fact (0 < T)] {t : Real
} {f : Real -> Complex} {p : Real>=0∞} (hLp : MemLp f p (volume.restrict (Ioc t 
(t + T)))) : MemLp (AddCircle.liftIoc T t f) p
参数：0 < T；hLp : MemLp f p (volume.restrict (Ioc t (t + T)))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.MemLp.comp_measurePreserving`：∀ {α : Type u_1} {m0 : Measu
rableSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α} {ε : Type u_7}   [inst
 : TopologicalSpace ε] [inst_1 :…
· 使用定理 `MeasureTheory.MeasurePreserving.comp`：∀ {α : Type u_1} {β : Type u_2} {γ
 : Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   [inst_2 :
 MeasurableSpace γ] {μa : …
· 使用引理 `MeasureTheory.measurePreserving_subtype_coe`：measurePreserving_subtype_c
oe {s : Set α} (hs : MeasurableSet s) : MeasurePreserving (Subtype.val : s -> α)
 (μa.comap Subtype.val) (μa.restr…
· 使用定理 `measurableSet_Ioc`：measurableSet_Ioc [ClosedIicTopology α] : MeasurableS
et (Ioc a b)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用引理 `AddCircle.measurePreserving_equivIoc`：measurePreserving_equivIoc {a : Re
al} : MeasurePreserving (equivIoc T a) volume (Measure.comap Subtype.val volume)

--- 原说明 ---
If a function satisfies `MemLp` on the interval `(t, t + T]`, then its lift to t
he AddCircle
also satisfies `MemLp` with respect to the Haar measure.
-/
lemma MeasureTheory.MemLp.memLp_liftIoc {T : ℝ} [hT : Fact (0 < T)] {t : ℝ} {f : ℝ → ℂ} {p : ℝ≥0∞}
    (hLp : MemLp f p (volume.restrict (Ioc t (t + T)))) :
      MemLp (AddCircle.liftIoc T t f) p := by
  simp only [AddCircle.liftIoc, Set.domRestrict_def, Function.comp_def]
  apply hLp.comp_measurePreserving
  refine .comp (measurePreserving_subtype_coe measurableSet_Ioc) ?_
  exact AddCircle.measurePreserving_equivIoc T

namespace UnitAddCircle

/-
**UnitAddCircle.measure_univ** 是 Mathlib 中的一个定理，位于命名空间 `UnitAddCircle`。
形式化陈述：MeasureTheory.volume Set.univ = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddCircle.measure_univ`：∀ (T : ℝ) [hT : Fact (0 < T)], MeasureTheory.vol
ume Set.univ = ENNReal.ofReal T
· 使用定理 `ENNReal.ofReal_one`：ENNReal.ofReal 1 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem measure_univ : volume (Set.univ : Set UnitAddCircle) = 1 := by simp

/-- The covering map from `ℝ` to the "unit additive circle" `ℝ ⧸ ℤ` is measure-preserving,
considered with respect to the standard measure (defined to be the Haar measure of total mass 1)
on the additive circle, and with respect to the restriction of Lebesgue measure on `ℝ` to an
interval $(t, t + 1]$. -/
/-
**UnitAddCircle.measurePreserving_mk** 是 Mathlib 中的一个定理，位于命名空间 `UnitAddCircle`。
形式化陈述：∀ (t : ℝ),   MeasureTheory.MeasurePreserving QuotientAddGroup.mk (MeasureT
heory.volume.restrict (Set.Ioc t (t + 1)))     MeasureTheory.volume
参数：t : ℝ；MeasureTheory.volume.restrict (Set.Ioc t (t + 1))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddCircle.measurePreserving_mk`：∀ (T : ℝ) [hT : Fact (0 < T)] (t : ℝ),  
 MeasureTheory.MeasurePreserving QuotientAddGroup.mk (MeasureTheory.volume.restr
ict (Set.Ioc t (t + …
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α

--- 原说明 ---
The covering map from `ℝ` to the "unit additive circle" `ℝ ⧸ ℤ` is measure-prese
rving,
considered with respect to the standard measure (defined to be the Haar measure 
of total mass 1)
on the additive circle, and with respect to the restriction of Lebesgue measure 
on `ℝ` to an
interval $(t, t + 1]$.
-/
protected theorem measurePreserving_mk (t : ℝ) :
    MeasurePreserving (β := UnitAddCircle) ((↑) : ℝ → UnitAddCircle)
      (volume.restrict (Ioc t (t + 1))) :=
  AddCircle.measurePreserving_mk 1 t

/-- The integral of a measurable function over `UnitAddCircle` is equal to the integral over an
interval $(t, t + 1]$ in `ℝ` of its lift to `ℝ`. -/
/-
**UnitAddCircle.lintegral_preimage** 是 Mathlib 中的一个定理，位于命名空间 `UnitAddCircle`。
形式化陈述：∀ (t : ℝ) (f : UnitAddCircle → ENNReal), ∫⁻ (a : ℝ) in Set.Ioc t (t + 1), 
f ↑a = ∫⁻ (b : UnitAddCircle), f b
参数：t : ℝ；f : UnitAddCircle → ENNReal；a : ℝ；t + 1；b : UnitAddCircle。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddCircle.lintegral_preimage`：∀ (T : ℝ) [hT : Fact (0 < T)] (t : ℝ) (f :
 AddCircle T → ENNReal),   ∫⁻ (a : ℝ) in Set.Ioc t (t + T), f ↑a = ∫⁻ (b : AddCi
rcle T), f b
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α

--- 原说明 ---
The integral of a measurable function over `UnitAddCircle` is equal to the integ
ral over an
interval $(t, t + 1]$ in `ℝ` of its lift to `ℝ`.
-/
protected theorem lintegral_preimage (t : ℝ) (f : UnitAddCircle → ℝ≥0∞) :
    (∫⁻ a in Ioc t (t + 1), f a) = ∫⁻ b : UnitAddCircle, f b :=
  AddCircle.lintegral_preimage 1 t f

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The integral of an almost-everywhere strongly measurable function over `UnitAddCircle` is
equal to the integral over an interval $(t, t + 1]$ in `ℝ` of its lift to `ℝ`. -/
/-
**UnitAddCircle.integral_preimage** 是 Mathlib 中的一个定理，位于命名空间 `UnitAddCircle`。
形式化陈述：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] 
(t : ℝ) (f : UnitAddCircle → E),   ∫ (a : ℝ) in Set.Ioc t (t + 1), f ↑a = ∫ (b :
 UnitAddCircle), f b
参数：t : ℝ；f : UnitAddCircle → E；a : ℝ；t + 1；b : UnitAddCircle。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddCircle.integral_preimage`：∀ (T : ℝ) [hT : Fact (0 < T)] {E : Type u_1
} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] (t : ℝ)   (f : AddCir
cle T → E), ∫ (a …
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α

--- 原说明 ---
The integral of an almost-everywhere strongly measurable function over `UnitAddC
ircle` is
equal to the integral over an interval $(t, t + 1]$ in `ℝ` of its lift to `ℝ`.
-/
protected theorem integral_preimage (t : ℝ) (f : UnitAddCircle → E) :
    (∫ a in Ioc t (t + 1), f a) = ∫ b : UnitAddCircle, f b :=
  AddCircle.integral_preimage 1 t f

/-- The integral of an almost-everywhere strongly measurable function over `UnitAddCircle` is
equal to the integral over an interval $(t, t + 1]$ in `ℝ` of its lift to `ℝ`. -/
/-
**UnitAddCircle.intervalIntegral_preimage** 是 Mathlib 中的一个定理，位于命名空间 `UnitAddCirc
le`。
形式化陈述：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] 
(t : ℝ) (f : UnitAddCircle → E),   ∫ (a : ℝ) in t..t + 1, f ↑a = ∫ (b : UnitAddC
ircle), f b
参数：t : ℝ；f : UnitAddCircle → E；a : ℝ；b : UnitAddCircle。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddCircle.intervalIntegral_preimage`：∀ (T : ℝ) [hT : Fact (0 < T)] {E : 
Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] (t : ℝ)   (f 
: AddCircle T → E), ∫ (a …
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α

--- 原说明 ---
The integral of an almost-everywhere strongly measurable function over `UnitAddC
ircle` is
equal to the integral over an interval $(t, t + 1]$ in `ℝ` of its lift to `ℝ`.
-/
protected theorem intervalIntegral_preimage (t : ℝ) (f : UnitAddCircle → E) :
    ∫ a in t..t + 1, f a = ∫ b : UnitAddCircle, f b :=
  AddCircle.intervalIntegral_preimage 1 t f

end UnitAddCircle

/-!
## Interval integrability of periodic functions
-/
namespace Function

namespace Periodic

variable {E : Type*} [NormedAddCommGroup E]

variable {f : ℝ → E} {T : ℝ}

/--
A periodic function is interval integrable over every interval if it is interval integrable over one
period.
-/
/-
**Function.Periodic.intervalIntegrable** 是 Mathlib 中的一个定理，位于命名空间 `Function.Perio
dic`。
形式化陈述：intervalIntegrable {t : Real} (h₁f : Function.Periodic f T) (hT : T != 0) 
(h₂f : IntervalIntegrable f volume t (t + T)) (a₁ a₂ : Real) : IntervalIntegrabl
e f volume a₁ a₂
参数：h₁f : Function.Periodic f T；hT : T != 0；h₂f : IntervalIntegrable f volume t (
t + T)；a₁ a₂ : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `exists_nat_ge`：exists_nat_ge (x : R) : exists n : Nat, x <= n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.uIcc_subset_uIcc_iff_le`：uIcc_subset_uIcc_iff_le : [[a₁, b₁]] subset
eq [[a₂, b₂]] ↔ min a₂ b₂ <= min a₁ b₁ ∧ max a₁ b₁ <= max a₂ b₂
· 使用引理 `min_le_left`：min_le_left (a b : α) : min a b <= a
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
（共 83 条，此处仅展示前 30 条）

--- 原说明 ---
A periodic function is interval integrable over every interval if it is interval
 integrable over one
period.
-/
theorem intervalIntegrable {t : ℝ} (h₁f : Function.Periodic f T)
    (hT : T ≠ 0) (h₂f : IntervalIntegrable f volume t (t + T)) (a₁ a₂ : ℝ) :
    IntervalIntegrable f volume a₁ a₂ := by
  wlog hT : 0 < T
  · rcases (not_lt.1 hT).eq_or_lt with h | h
    · tauto
    · have hnT : 0 < -T := neg_pos.mpr h
      nth_rw 1 [(by ring : t = (t + T) + (-T))] at h₂f
      apply this h₁f.neg hnT.ne' h₂f.symm _ _ hnT
  -- Replace [a₁, a₂] by [t - n₁ * T, t + n₂ * T], where n₁ and n₂ are natural numbers
  obtain ⟨n₁, hn₁⟩ := exists_nat_ge ((t - min a₁ a₂) / T)
  obtain ⟨n₂, hn₂⟩ := exists_nat_ge ((max a₁ a₂ - t) / T)
  have : Set.uIcc a₁ a₂ ⊆ Set.uIcc (t - n₁ * T) (t + n₂ * T) := by
    rw [Set.uIcc_subset_uIcc_iff_le]
    constructor
    · calc min (t - n₁ * T) (t + n₂ * T)
      _ ≤ (t - n₁ * T) := by apply min_le_left
      _ ≤ min a₁ a₂ := by linarith [(div_le_iff₀ hT).1 hn₁]
    · calc max a₁ a₂
      _ ≤ t + n₂ * T := by linarith [(div_le_iff₀ hT).1 hn₂]
      _ ≤ max (t - n₁ * T) (t + n₂ * T) := by apply le_max_right
  apply IntervalIntegrable.mono_set _ this
  -- Suffices to show integrability over shifted periods
  let a : ℕ → ℝ := fun n ↦ t + (n - n₁) * T
  rw [(by ring : t - n₁ * T = a 0), (by simp [a] : t + n₂ * T = a (n₁ + n₂))]
  apply IntervalIntegrable.trans_iterate
  -- Show integrability over a shifted period
  intro k hk
  convert! (IntervalIntegrable.comp_sub_right h₂f ((k - n₁) * T) enorm_ne_top) using 1
  · funext x
    simpa using (h₁f.sub_int_mul_eq (k - n₁)).symm
  · simp [a, Nat.cast_add]
    ring

/--
A periodic function is interval integrable over one full period if and only if it is interval
integrable over any other full period.

Special case of `Function.Periodic.intervalIntegrable`.
-/
/-
**Function.Periodic.intervalIntegrable_iff** 是 Mathlib 中的一个定理，位于命名空间 `Function.P
eriodic`。
形式化陈述：intervalIntegrable_iff {t₁ t₂ : Real} (hf : Periodic f T) : IntervalIntegr
able f volume t₁ (t₁ + T) ↔ IntervalIntegrable f volume t₂ (t₂ + T)
参数：hf : Periodic f T。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `Function.Periodic.intervalIntegrable`：intervalIntegrable {t : Real} (h₁f
 : Function.Periodic f T) (hT : T != 0) (h₂f : IntervalIntegrable f volume t (t 
+ T)) (a₁ a₂ : Real) : Int…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A periodic function is interval integrable over one full period if and only if i
t is interval
integrable over any other full period.

Special case of `Function.Periodic.intervalIntegrable`.
-/
theorem intervalIntegrable_iff {t₁ t₂ : ℝ} (hf : Periodic f T) :
    IntervalIntegrable f volume t₁ (t₁ + T) ↔ IntervalIntegrable f volume t₂ (t₂ + T) := by
  wlog hT : T ≠ 0
  · simp_all
  exact ⟨(hf.intervalIntegrable hT · t₂ (t₂ + T)), (hf.intervalIntegrable hT · t₁ (t₁ + T))⟩

/--
Special case of `Function.Periodic.intervalIntegrable`: A periodic function is interval integrable
over every interval if it is interval integrable over the period starting from zero.
-/
/-
**Function.Periodic.intervalIntegrable** 是 Mathlib 中的一个定理，位于命名空间 `Function.Perio
dic`。
形式化陈述：intervalIntegrable {t : Real} (h₁f : Function.Periodic f T) (hT : T != 0) 
(h₂f : IntervalIntegrable f volume t (t + T)) (a₁ a₂ : Real) : IntervalIntegrabl
e f volume a₁ a₂
参数：h₁f : Function.Periodic f T；hT : T != 0；h₂f : IntervalIntegrable f volume t (
t + T)；a₁ a₂ : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `exists_nat_ge`：exists_nat_ge (x : R) : exists n : Nat, x <= n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.uIcc_subset_uIcc_iff_le`：uIcc_subset_uIcc_iff_le : [[a₁, b₁]] subset
eq [[a₂, b₂]] ↔ min a₂ b₂ <= min a₁ b₁ ∧ max a₁ b₁ <= max a₂ b₂
· 使用引理 `min_le_left`：min_le_left (a b : α) : min a b <= a
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
（共 83 条，此处仅展示前 30 条）

--- 原说明 ---
Special case of `Function.Periodic.intervalIntegrable`: A periodic function is i
nterval integrable
over every interval if it is interval integrable over the period starting from z
ero.
-/
theorem intervalIntegrable₀ (h₁f : Function.Periodic f T) (hT : T ≠ 0)
    (h₂f : IntervalIntegrable f MeasureTheory.volume 0 T) (a₁ a₂ : ℝ) :
    IntervalIntegrable f MeasureTheory.volume a₁ a₂ := by
  apply h₁f.intervalIntegrable hT (t := 0)
  simpa

/-!
## Interval integrals of periodic functions
-/

variable [NormedSpace ℝ E]

/-- If `f` is a periodic function with period `T`, then its integral over `[t, t + T]` does not
depend on `t`. -/
/-
**Function.Periodic.intervalIntegral_add_eq** 是 Mathlib 中的一个定理，位于命名空间 `Function.
Periodic`。
形式化陈述：intervalIntegral_add_eq (hf : Periodic f T) (t s : Real) : ∫ x in t..t + T
, f x = ∫ x in s..s + T, f x
参数：hf : Periodic f T；t s : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `intervalIntegral.integral_of_le`：integral_of_le (h : a <= b) : ∫ x in a.
.b, f x ∂μ = ∫ x in Ioc a b, f x ∂μ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `MeasureTheory.measure_preimage_add`：∀ {G : Type u_1} [inst : MeasurableS
pace G] [inst_1 : AddGroup G] [MeasurableAdd G] (μ : MeasureTheory.Measure G)   
[μ.IsAddLeftInvariant] (…
· 使用定理 `ContinuousAdd.measurableAdd`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Add γ]   [SeparatelyCont
inuousAdd γ], Mea…
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.toIsAddLeftInvariant`：∀ {G : Type
 u_3} {inst : AddGroup G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpac
e G}   {μ : MeasureTheory.Measure G} [self : μ.Is…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `MeasureTheory.IsAddFundamentalDomain.setIntegral_eq`：∀ {G : Type u_1} {α
 : Type u_3} {E : Type u_5} [inst : AddGroup G] [inst_1 : AddAction G α] [inst_2
 : MeasurableSpace α]   [inst_3 : NormedA…
· 使用定理 `AddSubgroup.instMeasurableConstVAdd`：∀ {G : Type u_2} {α : Type u_3} [in
st : MeasurableSpace α] [inst_1 : AddGroup G] [inst_2 : AddAction G α]   [Measur
ableConstVAdd G α] (s : A…
· 使用定理 `MeasurableVAdd.toMeasurableConstVAdd`：∀ {M : Type u_2} {α : Type u_3} {i
nst : VAdd M α} {inst_1 : MeasurableSpace M} {inst_2 : MeasurableSpace α}   [sel
f : MeasurableVAdd M α], M…
· 使用定理 `measurableVAdd_of_add`：∀ (M : Type u_2) [inst : Add M] [inst_1 : Measura
bleSpace M] [MeasurableAdd M], MeasurableVAdd M M
· 使用定理 `AddSubgroup.instCountableSubtypeMemZMultiples`：∀ {G : Type u_1} [inst : 
AddGroup G] (a : G), Countable ↥(AddSubgroup.zmultiples a)
· 使用定理 `isAddFundamentalDomain_Ioc`：isAddFundamentalDomain_Ioc {T : Real} (hT : 
0 < T) (t : Real) (μ : Measure Real
· 使用定理 `Function.Periodic.map_vadd_zmultiples`：∀ {α : Type u_1} {β : Type u_2} {
f : α → β} {c : α} [inst : AddCommGroup α],   Function.Periodic f c → ∀ (a : ↥(A
ddSubgroup.zmultiples c)) (…
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
（共 43 条，此处仅展示前 30 条）

--- 原说明 ---
If `f` is a periodic function with period `T`, then its integral over `[t, t + T
]` does not
depend on `t`.
-/
theorem intervalIntegral_add_eq (hf : Periodic f T) (t s : ℝ) :
    ∫ x in t..t + T, f x = ∫ x in s..s + T, f x := by
  wlog hT : 0 < T
  · rcases (not_lt.1 hT).eq_or_lt with hT | hT
    · simp [hT]
    · rw [← neg_inj, ← integral_symm, ← integral_symm]
      simpa only [← sub_eq_add_neg, add_sub_cancel_right] using
        this hf.neg (t + T) (s + T) (neg_pos.mpr hT)
  simp only [integral_of_le, hT.le, le_add_iff_nonneg_right]
  have : VAddInvariantMeasure (AddSubgroup.zmultiples T) ℝ volume :=
    ⟨fun c s _ => measure_preimage_add _ _ _⟩
  apply IsAddFundamentalDomain.setIntegral_eq (G := AddSubgroup.zmultiples T)
  exacts [isAddFundamentalDomain_Ioc hT t, isAddFundamentalDomain_Ioc hT s, hf.map_vadd_zmultiples]

/-- If `f` is an integrable periodic function with period `T`, then its integral over `[t, s + T]`
is the sum of its integrals over the intervals `[t, s]` and `[t, t + T]`. -/
/-
**Function.Periodic.intervalIntegral_add_eq_add** 是 Mathlib 中的一个定理，位于命名空间 `Funct
ion.Periodic`。
形式化陈述：intervalIntegral_add_eq_add (hf : Periodic f T) (t s : Real) (h_int : fora
ll t₁ t₂, IntervalIntegrable f MeasureSpace.volume t₁ t₂) : ∫ x in t..s + T, f x
 = (∫ x in t..s, f x) + ∫ x in t..t + T, f x
参数：hf : Periodic f T；t s : Real；h_int : forall t₁ t₂, IntervalIntegrable f Measu
reSpace.volume t₁ t₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Periodic.intervalIntegral_add_eq`：intervalIntegral_add_eq (hf :
 Periodic f T) (t s : Real) : ∫ x in t..t + T, f x = ∫ x in s..s + T, f x
· 使用定理 `intervalIntegral.integral_add_adjacent_intervals`：integral_add_adjacent_
intervals (hab : IntervalIntegrable f μ a b) (hbc : IntervalIntegrable f μ b c) 
: ((∫ x in a..b, f x ∂μ) + ∫ x in b..c…

--- 原说明 ---
If `f` is an integrable periodic function with period `T`, then its integral ove
r `[t, s + T]`
is the sum of its integrals over the intervals `[t, s]` and `[t, t + T]`.
-/
theorem intervalIntegral_add_eq_add (hf : Periodic f T) (t s : ℝ)
    (h_int : ∀ t₁ t₂, IntervalIntegrable f MeasureSpace.volume t₁ t₂) :
    ∫ x in t..s + T, f x = (∫ x in t..s, f x) + ∫ x in t..t + T, f x := by
  rw [hf.intervalIntegral_add_eq t s, integral_add_adjacent_intervals (h_int t s) (h_int s _)]

/-- If `f` is an integrable periodic function with period `T`, and `n` is an integer, then its
integral over `[t, t + n • T]` is `n` times its integral over `[t, t + T]`. -/
/-
**Function.Periodic.intervalIntegral_add_zsmul_eq** 是 Mathlib 中的一个定理，位于命名空间 `Fun
ction.Periodic`。
形式化陈述：intervalIntegral_add_zsmul_eq (hf : Periodic f T) (n : Int) (t : Real) (h_
int : forall t₁ t₂, IntervalIntegrable f MeasureSpace.volume t₁ t₂) : ∫ x in t..
t + n • T, f x = n • ∫ x in t..t + T, f x
参数：hf : Periodic f T；n : Int；t : Real；h_int : forall t₁ t₂, IntervalIntegrable f
 MeasureSpace.volume t₁ t₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M), 0 • a = 0
· 使用定理 `intervalIntegral.integral_same`：integral_same : ∫ x in a..a, f x ∂μ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `succ_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M) (n : ℕ), (n + 
1) • a = n • a + a
· 使用定理 `Function.Periodic.intervalIntegral_add_eq_add`：intervalIntegral_add_eq_a
dd (hf : Periodic f T) (t s : Real) (h_int : forall t₁ t₂, IntervalIntegrable f 
MeasureSpace.volume t₁ t₂) : ∫ x in…
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `zsmul_eq_mul`：∀ {α : Type u_3} [inst : NonAssocRing α] (a : α) (n : ℤ), 
n • a = ↑n * a
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `natCast_zsmul`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G) (n : ℕ),
 ↑n • a = n • a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `negSucc_zsmul`：negSucc_zsmul {G} [SubNegMonoid G] (a : G) (n : Nat) : In
t.negSucc n • a = -((n + 1) • a)
· 使用定理 `Int.cast_negSucc`：cast_negSucc (n : Nat) : (-[n+1] : R) = -(n + 1 : Nat)
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `neg_add_rev`：∀ {G : Type u_1} [inst : SubtractionMonoid G] (a b : G), -(
a + b) = -b + -a
· 使用引理 `Mathlib.Tactic.Linarith.eq_of_not_lt_of_not_gt`：eq_of_not_lt_of_not_gt {
α} [LinearOrder α] (a b : α) (h1 : ¬ a < b) (h2 : ¬ b < a) : a = b
· 使用定理 `Not.intro`：∀ {a : Prop}, (a → False) → ¬a
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
（共 69 条，此处仅展示前 30 条）

--- 原说明 ---
If `f` is an integrable periodic function with period `T`, and `n` is an integer
, then its
integral over `[t, t + n • T]` is `n` times its integral over `[t, t + T]`.
-/
theorem intervalIntegral_add_zsmul_eq (hf : Periodic f T) (n : ℤ) (t : ℝ)
    (h_int : ∀ t₁ t₂, IntervalIntegrable f MeasureSpace.volume t₁ t₂) :
    ∫ x in t..t + n • T, f x = n • ∫ x in t..t + T, f x := by
  -- Reduce to the case `b = 0`
  suffices (∫ x in 0..(n • T), f x) = n • ∫ x in 0..T, f x by
    simp only [hf.intervalIntegral_add_eq t 0, (hf.zsmul n).intervalIntegral_add_eq t 0, zero_add,
      this]
  -- First prove it for natural numbers
  have : ∀ m : ℕ, (∫ x in 0..m • T, f x) = m • ∫ x in 0..T, f x := fun m ↦ by
    induction m with
    | zero => simp
    | succ m ih =>
      simp only [succ_nsmul, hf.intervalIntegral_add_eq_add 0 (m • T) h_int, ih, zero_add]
  -- Then prove it for all integers
  rcases n with n | n
  · simp [← this n]
  · conv_rhs => rw [negSucc_zsmul]
    have h₀ : Int.negSucc n • T + (n + 1) • T = 0 := by simp; linarith
    rw [integral_symm, ← (hf.nsmul (n + 1)).funext, neg_inj]
    simp_rw [integral_comp_add_right, h₀, zero_add, this (n + 1), add_comm T,
      hf.intervalIntegral_add_eq ((n + 1) • T) 0, zero_add]

section RealValued

open Filter

variable {g : ℝ → ℝ}
variable (hg : Periodic g T)
include hg

/-- If `g : ℝ → ℝ` is periodic with period `T > 0`, then for any `t : ℝ`, the function
`t ↦ ∫ x in 0..t, g x` is bounded below by `t ↦ X + ⌊t/T⌋ • Y` for appropriate constants `X` and
`Y`. -/
/-
**Function.Periodic.sInf_add_zsmul_le_integral_of_pos** 是 Mathlib 中的一个定理，位于命名空间 
`Function.Periodic`。
形式化陈述：sInf_add_zsmul_le_integral_of_pos (h_int : IntervalIntegrable g MeasureSpa
ce.volume 0 T) (hT : 0 < T) (t : Real) : (sInf ((fun t => ∫ x in 0..t, g x) '' I
cc 0 T) + ⌊t / T⌋ • ∫ x in 0..T, g x) <= ∫ x in 0..t, g x
参数：h_int : IntervalIntegrable g MeasureSpace.volume 0 T；hT : 0 < T；t : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Periodic.intervalIntegrable₀`：intervalIntegrable₀ (h₁f : Functi
on.Periodic f T) (hT : T != 0) (h₂f : IntervalIntegrable f MeasureTheory.volume 
0 T) (a₁ a₂ : Real) : Inter…
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.fract_div_mul_self_add_zsmul_eq`：fract_div_mul_self_add_zsmul_eq (a 
b : k) (ha : a != 0) : fract (b / a) * a + ⌊b / a⌋ • a = b
· 使用定理 `intervalIntegral.integral_add_adjacent_intervals`：integral_add_adjacent_
intervals (hab : IntervalIntegrable f μ a b) (hbc : IntervalIntegrable f μ b c) 
: ((∫ x in a..b, f x ∂μ) + ∫ x in b..c…
· 使用定理 `Function.Periodic.intervalIntegral_add_zsmul_eq`：intervalIntegral_add_zs
mul_eq (hf : Periodic f T) (n : Int) (t : Real) (h_int : forall t₁ t₂, IntervalI
ntegrable f MeasureSpace.volume t₁ t₂…
· 使用定理 `Function.Periodic.intervalIntegral_add_eq`：intervalIntegral_add_eq (hf :
 Periodic f T) (t s : Real) : ∫ x in t..t + T, f x = ∫ x in s..s + T, f x
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `add_le_add_iff_right`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LE α] [A
ddRightMono α] [AddRightReflectLE α] (a : α) {b c : α},   b + a ≤ c + a ↔ b ≤ c
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsRightCancelAdd.addRightReflectLE_of_addRightReflectLT`：∀ (N : Type u_2
) [inst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightReflect
LT N],   AddRightReflectLE N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `ContinuousOn.sInf_image_Icc_le`：sInf_image_Icc_le (h : ContinuousOn f <|
 Icc a b) (hc : c in Icc a b) : sInf (f '' Icc a b) <= f c
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `intervalIntegral.continuous_primitive`：continuous_primitive (h_int : for
all a b, IntervalIntegrable f μ a b) (a : Real) : Continuous fun b => ∫ x in a..
b, f x ∂μ
· 使用定理 `Set.mem_Icc_of_Ico`：∀ {α : Type u_1} [inst : Preorder α] {a b x : α}, x 
∈ Set.Ico b a → x ∈ Set.Icc b a
· 使用定理 `Int.fract_div_mul_self_mem_Ico`：fract_div_mul_self_mem_Ico (a b : k) (ha
 : 0 < a) : fract (b / a) * a in Ico 0 a

--- 原说明 ---
If `g : ℝ → ℝ` is periodic with period `T > 0`, then for any `t : ℝ`, the functi
on
`t ↦ ∫ x in 0..t, g x` is bounded below by `t ↦ X + ⌊t/T⌋ • Y` for appropriate c
onstants `X` and
`Y`.
-/
theorem sInf_add_zsmul_le_integral_of_pos (h_int : IntervalIntegrable g MeasureSpace.volume 0 T)
    (hT : 0 < T) (t : ℝ) :
    (sInf ((fun t => ∫ x in 0..t, g x) '' Icc 0 T) + ⌊t / T⌋ • ∫ x in 0..T, g x) ≤
      ∫ x in 0..t, g x := by
  let h'_int := hg.intervalIntegrable₀ hT.ne' h_int
  let ε := Int.fract (t / T) * T
  conv_rhs =>
    rw [← Int.fract_div_mul_self_add_zsmul_eq T t hT.ne',
      ← integral_add_adjacent_intervals (h'_int 0 ε) (h'_int _ _)]
  rw [hg.intervalIntegral_add_zsmul_eq ⌊t / T⌋ ε (hg.intervalIntegrable₀ hT.ne' h_int),
    hg.intervalIntegral_add_eq ε 0, zero_add, add_le_add_iff_right]
  exact (continuous_primitive h'_int 0).continuousOn.sInf_image_Icc_le <|
    mem_Icc_of_Ico (Int.fract_div_mul_self_mem_Ico T t hT)

/-- If `g : ℝ → ℝ` is periodic with period `T > 0`, then for any `t : ℝ`, the function
`t ↦ ∫ x in 0..t, g x` is bounded above by `t ↦ X + ⌊t/T⌋ • Y` for appropriate constants `X` and
`Y`. -/
/-
**Function.Periodic.integral_le_sSup_add_zsmul_of_pos** 是 Mathlib 中的一个定理，位于命名空间 
`Function.Periodic`。
形式化陈述：integral_le_sSup_add_zsmul_of_pos (h_int : IntervalIntegrable g MeasureSpa
ce.volume 0 T) (hT : 0 < T) (t : Real) : (∫ x in 0..t, g x) <= sSup ((fun t => ∫
 x in 0..t, g x) '' Icc 0 T) + ⌊t / T⌋ • ∫ x in 0..T, g x
参数：h_int : IntervalIntegrable g MeasureSpace.volume 0 T；hT : 0 < T；t : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Periodic.intervalIntegrable₀`：intervalIntegrable₀ (h₁f : Functi
on.Periodic f T) (hT : T != 0) (h₂f : IntervalIntegrable f MeasureTheory.volume 
0 T) (a₁ a₂ : Real) : Inter…
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.fract_div_mul_self_add_zsmul_eq`：fract_div_mul_self_add_zsmul_eq (a 
b : k) (ha : a != 0) : fract (b / a) * a + ⌊b / a⌋ • a = b
· 使用定理 `intervalIntegral.integral_add_adjacent_intervals`：integral_add_adjacent_
intervals (hab : IntervalIntegrable f μ a b) (hbc : IntervalIntegrable f μ b c) 
: ((∫ x in a..b, f x ∂μ) + ∫ x in b..c…
· 使用定理 `Function.Periodic.intervalIntegral_add_zsmul_eq`：intervalIntegral_add_zs
mul_eq (hf : Periodic f T) (n : Int) (t : Real) (h_int : forall t₁ t₂, IntervalI
ntegrable f MeasureSpace.volume t₁ t₂…
· 使用定理 `Function.Periodic.intervalIntegral_add_eq`：intervalIntegral_add_eq (hf :
 Periodic f T) (t s : Real) : ∫ x in t..t + T, f x = ∫ x in s..s + T, f x
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `add_le_add_iff_right`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LE α] [A
ddRightMono α] [AddRightReflectLE α] (a : α) {b c : α},   b + a ≤ c + a ↔ b ≤ c
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsRightCancelAdd.addRightReflectLE_of_addRightReflectLT`：∀ (N : Type u_2
) [inst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightReflect
LT N],   AddRightReflectLE N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `ContinuousOn.le_sSup_image_Icc`：le_sSup_image_Icc (h : ContinuousOn f <|
 Icc a b) (hc : c in Icc a b) : f c <= sSup (f '' Icc a b)
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `intervalIntegral.continuous_primitive`：continuous_primitive (h_int : for
all a b, IntervalIntegrable f μ a b) (a : Real) : Continuous fun b => ∫ x in a..
b, f x ∂μ
· 使用定理 `Set.mem_Icc_of_Ico`：∀ {α : Type u_1} [inst : Preorder α] {a b x : α}, x 
∈ Set.Ico b a → x ∈ Set.Icc b a
· 使用定理 `Int.fract_div_mul_self_mem_Ico`：fract_div_mul_self_mem_Ico (a b : k) (ha
 : 0 < a) : fract (b / a) * a in Ico 0 a

--- 原说明 ---
If `g : ℝ → ℝ` is periodic with period `T > 0`, then for any `t : ℝ`, the functi
on
`t ↦ ∫ x in 0..t, g x` is bounded above by `t ↦ X + ⌊t/T⌋ • Y` for appropriate c
onstants `X` and
`Y`.
-/
theorem integral_le_sSup_add_zsmul_of_pos (h_int : IntervalIntegrable g MeasureSpace.volume 0 T)
    (hT : 0 < T) (t : ℝ) :
    (∫ x in 0..t, g x) ≤
      sSup ((fun t => ∫ x in 0..t, g x) '' Icc 0 T) + ⌊t / T⌋ • ∫ x in 0..T, g x := by
  let h'_int := hg.intervalIntegrable₀ hT.ne' h_int
  let ε := Int.fract (t / T) * T
  conv_lhs =>
    rw [← Int.fract_div_mul_self_add_zsmul_eq T t hT.ne', ←
      integral_add_adjacent_intervals (h'_int 0 ε) (h'_int _ _)]
  rw [hg.intervalIntegral_add_zsmul_eq ⌊t / T⌋ ε h'_int, hg.intervalIntegral_add_eq ε 0, zero_add,
    add_le_add_iff_right]
  exact (continuous_primitive h'_int 0).continuousOn.le_sSup_image_Icc
    (mem_Icc_of_Ico (Int.fract_div_mul_self_mem_Ico T t hT))

/-- If `g : ℝ → ℝ` is periodic with period `T > 0` and `0 < ∫ x in 0..T, g x`, then
`t ↦ ∫ x in 0..t, g x` tends to `∞` as `t` tends to `∞`. -/
/-
**Function.Periodic.tendsto_atTop_intervalIntegral_of_pos** 是 Mathlib 中的一个定理，位于命
名空间 `Function.Periodic`。
形式化陈述：tendsto_atTop_intervalIntegral_of_pos (h₀ : 0 < ∫ x in 0..T, g x) (hT : 0 
< T) : Tendsto (fun t => ∫ x in 0..t, g x) atTop atTop
参数：h₀ : 0 < ∫ x in 0..T, g x；hT : 0 < T。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `intervalIntegral.intervalIntegrable_of_integral_ne_zero`：intervalIntegra
ble_of_integral_ne_zero {a b : Real} {f : Real -> E} {μ : Measure Real} (h : (∫ 
x in a..b, f x ∂μ) != 0) : IntervalIntegrable…
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Filter.tendsto_atTop_mono`：tendsto_atTop_mono [Preorder β] {l : Filter α
} {f g : α -> β} (h : forall n, f n <= g n) : Tendsto f l atTop -> Tendsto g l a
tTop
· 使用定理 `Function.Periodic.sInf_add_zsmul_le_integral_of_pos`：sInf_add_zsmul_le_i
ntegral_of_pos (h_int : IntervalIntegrable g MeasureSpace.volume 0 T) (hT : 0 < 
T) (t : Real) : (sInf ((fun t => ∫ x in 0…
· 使用定理 `Filter.tendsto_atTop_add_const_left`：∀ {α : Type u_1} {G : Type u_2} [in
st : AddCommGroup G] [inst_1 : PartialOrder G] [IsOrderedAddMonoid G] (l : Filte
r α)   {f : α → G} (C : G…
· 使用定理 `Filter.Tendsto.atTop_zsmul_const`：∀ {α : Type u_1} {R : Type u_2} {l : F
ilter α} {r : R} [inst : AddCommGroup R] [inst_1 : LinearOrder R]   [IsOrderedAd
dMonoid R] [Archimedea…
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `tendsto_floor_atTop`：tendsto_floor_atTop : Tendsto (floor : α -> Int) at
Top atTop
· 使用定理 `Filter.Tendsto.atTop_mul_const`：∀ {α : Type u_1} {β : Type u_2} [inst : 
Semifield α] [inst_1 : LinearOrder α] [IsStrictOrderedRing α] {l : Filter β}   {
f : β → α} {r : α}, …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inv_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : PartialOr
der G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a⁻¹ ↔ 0 < a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Filter.tendsto_id`：tendsto_id {x : Filter α} : Tendsto id x x

--- 原说明 ---
If `g : ℝ → ℝ` is periodic with period `T > 0` and `0 < ∫ x in 0..T, g x`, then
`t ↦ ∫ x in 0..t, g x` tends to `∞` as `t` tends to `∞`.
-/
theorem tendsto_atTop_intervalIntegral_of_pos (h₀ : 0 < ∫ x in 0..T, g x) (hT : 0 < T) :
    Tendsto (fun t => ∫ x in 0..t, g x) atTop atTop := by
  have h_int := intervalIntegrable_of_integral_ne_zero h₀.ne'
  apply tendsto_atTop_mono (hg.sInf_add_zsmul_le_integral_of_pos h_int hT)
  apply atTop.tendsto_atTop_add_const_left (sInf <| (fun t => ∫ x in 0..t, g x) '' Icc 0 T)
  apply Tendsto.atTop_zsmul_const h₀
  exact tendsto_floor_atTop.comp (tendsto_id.atTop_mul_const (inv_pos.mpr hT))

/-- If `g : ℝ → ℝ` is periodic with period `T > 0` and `0 < ∫ x in 0..T, g x`, then
`t ↦ ∫ x in 0..t, g x` tends to `-∞` as `t` tends to `-∞`. -/
/-
**Function.Periodic.tendsto_atBot_intervalIntegral_of_pos** 是 Mathlib 中的一个定理，位于命
名空间 `Function.Periodic`。
形式化陈述：tendsto_atBot_intervalIntegral_of_pos (h₀ : 0 < ∫ x in 0..T, g x) (hT : 0 
< T) : Tendsto (fun t => ∫ x in 0..t, g x) atBot atBot
参数：h₀ : 0 < ∫ x in 0..T, g x；hT : 0 < T。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `intervalIntegral.intervalIntegrable_of_integral_ne_zero`：intervalIntegra
ble_of_integral_ne_zero {a b : Real} {f : Real -> E} {μ : Measure Real} (h : (∫ 
x in a..b, f x ∂μ) != 0) : IntervalIntegrable…
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Filter.tendsto_atBot_mono`：∀ {α : Type u_3} {β : Type u_4} [inst : Preor
der β] {l : Filter α} {f g : α → β},   (∀ (n : α), g n ≤ f n) → Filter.Tendsto f
 l Filter.atBot…
· 使用定理 `Function.Periodic.integral_le_sSup_add_zsmul_of_pos`：integral_le_sSup_ad
d_zsmul_of_pos (h_int : IntervalIntegrable g MeasureSpace.volume 0 T) (hT : 0 < 
T) (t : Real) : (∫ x in 0..t, g x) <= sSu…
· 使用定理 `Filter.tendsto_atBot_add_const_left`：∀ {α : Type u_1} {G : Type u_2} [in
st : AddCommGroup G] [inst_1 : PartialOrder G] [IsOrderedAddMonoid G] (l : Filte
r α)   {f : α → G} (C : G…
· 使用定理 `Filter.Tendsto.atBot_zsmul_const`：∀ {α : Type u_1} {R : Type u_2} {l : F
ilter α} {r : R} [inst : AddCommGroup R] [inst_1 : LinearOrder R]   [IsOrderedAd
dMonoid R] [Archimedea…
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `tendsto_floor_atBot`：tendsto_floor_atBot : Tendsto (floor : α -> Int) at
Bot atBot
· 使用定理 `Filter.Tendsto.atBot_mul_const`：∀ {α : Type u_1} {β : Type u_2} [inst : 
Field α] [inst_1 : LinearOrder α] [IsStrictOrderedRing α] {l : Filter β}   {f : 
β → α} {r : α}, 0 < …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inv_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : PartialOr
der G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a⁻¹ ↔ 0 < a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Filter.tendsto_id`：tendsto_id {x : Filter α} : Tendsto id x x

--- 原说明 ---
If `g : ℝ → ℝ` is periodic with period `T > 0` and `0 < ∫ x in 0..T, g x`, then
`t ↦ ∫ x in 0..t, g x` tends to `-∞` as `t` tends to `-∞`.
-/
theorem tendsto_atBot_intervalIntegral_of_pos (h₀ : 0 < ∫ x in 0..T, g x) (hT : 0 < T) :
    Tendsto (fun t => ∫ x in 0..t, g x) atBot atBot := by
  have h_int := intervalIntegrable_of_integral_ne_zero h₀.ne'
  apply tendsto_atBot_mono (hg.integral_le_sSup_add_zsmul_of_pos h_int hT)
  apply atBot.tendsto_atBot_add_const_left (sSup <| (fun t => ∫ x in 0..t, g x) '' Icc 0 T)
  apply Tendsto.atBot_zsmul_const h₀
  exact tendsto_floor_atBot.comp (tendsto_id.atBot_mul_const (inv_pos.mpr hT))

/-- If `g : ℝ → ℝ` is periodic with period `T > 0` and `∀ x, 0 < g x`, then `t ↦ ∫ x in 0..t, g x`
tends to `∞` as `t` tends to `∞`. -/
/-
**Function.Periodic.tendsto_atTop_intervalIntegral_of_pos'** 是 Mathlib 中的一个定理，位于
命名空间 `Function.Periodic`。
形式化陈述：tendsto_atTop_intervalIntegral_of_pos' (h_int : IntervalIntegrable g Measu
reSpace.volume 0 T) (h₀ : forall x, 0 < g x) (hT : 0 < T) : Tendsto (fun t => ∫ 
x in 0..t, g x) atTop atTop
参数：h_int : IntervalIntegrable g MeasureSpace.volume 0 T；h₀ : forall x, 0 < g x；h
T : 0 < T。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Periodic.tendsto_atTop_intervalIntegral_of_pos`：tendsto_atTop_i
ntervalIntegral_of_pos (h₀ : 0 < ∫ x in 0..T, g x) (hT : 0 < T) : Tendsto (fun t
 => ∫ x in 0..t, g x) atTop atTop
· 使用定理 `intervalIntegral.intervalIntegral_pos_of_pos`：intervalIntegral_pos_of_po
s {f : Real -> Real} {a b : Real} (hfi : IntervalIntegrable f MeasureSpace.volum
e a b) (hpos : forall x, 0 < f x) …

--- 原说明 ---
If `g : ℝ → ℝ` is periodic with period `T > 0` and `∀ x, 0 < g x`, then `t ↦ ∫ x
 in 0..t, g x`
tends to `∞` as `t` tends to `∞`.
-/
theorem tendsto_atTop_intervalIntegral_of_pos'
    (h_int : IntervalIntegrable g MeasureSpace.volume 0 T) (h₀ : ∀ x, 0 < g x) (hT : 0 < T) :
    Tendsto (fun t => ∫ x in 0..t, g x) atTop atTop :=
  hg.tendsto_atTop_intervalIntegral_of_pos (intervalIntegral_pos_of_pos h_int h₀ hT) hT

/-- If `g : ℝ → ℝ` is periodic with period `T > 0` and `∀ x, 0 < g x`, then `t ↦ ∫ x in 0..t, g x`
tends to `-∞` as `t` tends to `-∞`. -/
/-
**Function.Periodic.tendsto_atBot_intervalIntegral_of_pos'** 是 Mathlib 中的一个定理，位于
命名空间 `Function.Periodic`。
形式化陈述：tendsto_atBot_intervalIntegral_of_pos' (h_int : IntervalIntegrable g Measu
reSpace.volume 0 T) (h₀ : forall x, 0 < g x) (hT : 0 < T) : Tendsto (fun t => ∫ 
x in 0..t, g x) atBot atBot
参数：h_int : IntervalIntegrable g MeasureSpace.volume 0 T；h₀ : forall x, 0 < g x；h
T : 0 < T。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Periodic.tendsto_atBot_intervalIntegral_of_pos`：tendsto_atBot_i
ntervalIntegral_of_pos (h₀ : 0 < ∫ x in 0..T, g x) (hT : 0 < T) : Tendsto (fun t
 => ∫ x in 0..t, g x) atBot atBot
· 使用定理 `intervalIntegral.intervalIntegral_pos_of_pos`：intervalIntegral_pos_of_po
s {f : Real -> Real} {a b : Real} (hfi : IntervalIntegrable f MeasureSpace.volum
e a b) (hpos : forall x, 0 < f x) …

--- 原说明 ---
If `g : ℝ → ℝ` is periodic with period `T > 0` and `∀ x, 0 < g x`, then `t ↦ ∫ x
 in 0..t, g x`
tends to `-∞` as `t` tends to `-∞`.
-/
theorem tendsto_atBot_intervalIntegral_of_pos'
    (h_int : IntervalIntegrable g MeasureSpace.volume 0 T) (h₀ : ∀ x, 0 < g x) (hT : 0 < T) :
    Tendsto (fun t => ∫ x in 0..t, g x) atBot atBot := by
  exact hg.tendsto_atBot_intervalIntegral_of_pos (intervalIntegral_pos_of_pos h_int h₀ hT) hT

end RealValued

end Periodic

end Function

