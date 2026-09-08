/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public import Mathlib.Algebra.Group.Pointwise.Set.Card
public import Mathlib.GroupTheory.Complement
public import Mathlib.MeasureTheory.Group.Action
public import Mathlib.MeasureTheory.Group.Pointwise
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Topology.Algebra.Module.Equiv
public import Mathlib.Topology.ContinuousMap.CocompactMap

/-!
# Measures on Groups

We develop some properties of measures on (topological) groups

* We define properties on measures: measures that are left or right invariant w.r.t. multiplication.
* We define the measure `μ.inv : A ↦ μ(A⁻¹)` and show that it is right invariant iff
  `μ` is left invariant.
* We define a class `IsHaarMeasure μ`, requiring that the measure `μ` is left-invariant, finite
  on compact sets, and positive on open sets.

We also give analogues of all these notions in the additive world.
-/

@[expose] public section


noncomputable section

open scoped NNReal ENNReal Pointwise Topology

open Inv Set Function MeasureTheory.Measure Filter

variable {G H : Type*} [MeasurableSpace G] [MeasurableSpace H]

namespace MeasureTheory

section Mul

variable [Mul G] {μ : Measure G}

@[to_additive]
/-
**MeasureTheory.map_mul_left_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：map_mul_left_eq_self (μ : Measure G) [IsMulLeftInvariant μ] (g : G) : map 
(g * ·) μ = μ
参数：μ : Measure G；g : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.IsMulLeftInvariant.map_mul_left_eq_self`：∀ {G : Ty
pe u_1} {inst : MeasurableSpace G} {inst_1 : Mul G} {μ : MeasureTheory.Measure G
} [self : μ.IsMulLeftInvariant]   (g : G), MeasureT…
-/
theorem map_mul_left_eq_self (μ : Measure G) [IsMulLeftInvariant μ] (g : G) :
    map (g * ·) μ = μ :=
  IsMulLeftInvariant.map_mul_left_eq_self g

@[to_additive]
/-
**MeasureTheory.map_mul_right_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：map_mul_right_eq_self (μ : Measure G) [IsMulRightInvariant μ] (g : G) : ma
p (· * g) μ = μ
参数：μ : Measure G；g : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.IsMulRightInvariant.map_mul_right_eq_self`：∀ {G : 
Type u_1} {inst : MeasurableSpace G} {inst_1 : Mul G} {μ : MeasureTheory.Measure
 G}   [self : μ.IsMulRightInvariant] (g : G), Measure…
-/
theorem map_mul_right_eq_self (μ : Measure G) [IsMulRightInvariant μ] (g : G) : map (· * g) μ = μ :=
  IsMulRightInvariant.map_mul_right_eq_self g

@[to_additive MeasureTheory.isAddLeftInvariant_smul]
/-
**MeasureTheory.isMulLeftInvariant_smul** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory
`。
形式化陈述：isMulLeftInvariant_smul [IsMulLeftInvariant μ] (c : Real>=0∞) : IsMulLeftI
nvariant (c • μ)
参数：c : Real>=0∞。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.map_smul`：∀ {α : Type u_1} {β : Type u_2} {mα : Me
asurableSpace α} {mβ : MeasurableSpace β} {R : Type u_4} [inst : SMul R ENNReal]
   [inst_1 : IsScala…
· 使用定理 `MeasureTheory.map_mul_left_eq_self`：map_mul_left_eq_self (μ : Measure G)
 [IsMulLeftInvariant μ] (g : G) : map (g * ·) μ = μ
-/
instance isMulLeftInvariant_smul [IsMulLeftInvariant μ] (c : ℝ≥0∞) : IsMulLeftInvariant (c • μ) :=
  ⟨fun g => by rw [Measure.map_smul, map_mul_left_eq_self]⟩

@[to_additive MeasureTheory.isAddRightInvariant_smul]
/-
**MeasureTheory.isMulRightInvariant_smul** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheor
y`。
形式化陈述：isMulRightInvariant_smul [IsMulRightInvariant μ] (c : Real>=0∞) : IsMulRig
htInvariant (c • μ)
参数：c : Real>=0∞。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.map_smul`：∀ {α : Type u_1} {β : Type u_2} {mα : Me
asurableSpace α} {mβ : MeasurableSpace β} {R : Type u_4} [inst : SMul R ENNReal]
   [inst_1 : IsScala…
· 使用定理 `MeasureTheory.map_mul_right_eq_self`：map_mul_right_eq_self (μ : Measure 
G) [IsMulRightInvariant μ] (g : G) : map (· * g) μ = μ
-/
instance isMulRightInvariant_smul [IsMulRightInvariant μ] (c : ℝ≥0∞) :
    IsMulRightInvariant (c • μ) :=
  ⟨fun g => by rw [Measure.map_smul, map_mul_right_eq_self]⟩

@[to_additive MeasureTheory.isAddLeftInvariant_smul_nnreal]
/-
**MeasureTheory.isMulLeftInvariant_smul_nnreal** 是 Mathlib 中的一个实例，位于命名空间 `Measur
eTheory`。
形式化陈述：isMulLeftInvariant_smul_nnreal [IsMulLeftInvariant μ] (c : Real>=0) : IsMu
lLeftInvariant (c • μ)
参数：c : Real>=0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance isMulLeftInvariant_smul_nnreal [IsMulLeftInvariant μ] (c : ℝ≥0) :
    IsMulLeftInvariant (c • μ) :=
  MeasureTheory.isMulLeftInvariant_smul (c : ℝ≥0∞)

@[to_additive MeasureTheory.isAddRightInvariant_smul_nnreal]
/-
**MeasureTheory.isMulRightInvariant_smul_nnreal** 是 Mathlib 中的一个实例，位于命名空间 `Measu
reTheory`。
形式化陈述：isMulRightInvariant_smul_nnreal [IsMulRightInvariant μ] (c : Real>=0) : Is
MulRightInvariant (c • μ)
参数：c : Real>=0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance isMulRightInvariant_smul_nnreal [IsMulRightInvariant μ] (c : ℝ≥0) :
    IsMulRightInvariant (c • μ) :=
  MeasureTheory.isMulRightInvariant_smul (c : ℝ≥0∞)

section MeasurableMul

variable [MeasurableMul G]

@[to_additive]
/-
**MeasureTheory.measurePreserving_mul_left** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory`。
形式化陈述：measurePreserving_mul_left (μ : Measure G) [IsMulLeftInvariant μ] (g : G) 
: MeasurePreserving (g * ·) μ μ
参数：μ : Measure G；g : G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableMul.measurable_const_mul`：∀ {M : Type u_2} {inst : MeasurableS
pace M} {inst_1 : Mul M} [self : MeasurableMul M] (c : M), Measurable fun x => c
 * x
· 使用定理 `MeasureTheory.map_mul_left_eq_self`：map_mul_left_eq_self (μ : Measure G)
 [IsMulLeftInvariant μ] (g : G) : map (g * ·) μ = μ
-/
theorem measurePreserving_mul_left (μ : Measure G) [IsMulLeftInvariant μ] (g : G) :
    MeasurePreserving (g * ·) μ μ :=
  ⟨measurable_const_mul g, map_mul_left_eq_self μ g⟩

@[to_additive]
/-
**MeasureTheory.MeasurePreserving.mul_left** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.MeasurePreserving`。
形式化陈述：∀ {G : Type u_1} [inst : MeasurableSpace G] [inst_1 : Mul G] [MeasurableMu
l G] (μ : MeasureTheory.Measure G)   [μ.IsMulLeftInvariant] (g : G) {X : Type u_
3} [inst_4 : MeasurableSpace X] {μ' : MeasureTheory.Measure X} {f : X → G},   Me
asureTheory.MeasurePreserving f μ' μ → MeasureTheory.MeasurePreserving (fun x =>
 g * f x) μ' μ
参数：μ : MeasureTheory.Measure G；g : G；fun x => g * f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.MeasurePreserving.comp`：∀ {α : Type u_1} {β : Type u_2} {γ
 : Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   [inst_2 :
 MeasurableSpace γ] {μa : …
· 使用定理 `MeasureTheory.measurePreserving_mul_left`：measurePreserving_mul_left (μ 
: Measure G) [IsMulLeftInvariant μ] (g : G) : MeasurePreserving (g * ·) μ μ
-/
theorem MeasurePreserving.mul_left (μ : Measure G) [IsMulLeftInvariant μ] (g : G) {X : Type*}
    [MeasurableSpace X] {μ' : Measure X} {f : X → G} (hf : MeasurePreserving f μ' μ) :
    MeasurePreserving (fun x => g * f x) μ' μ :=
  (measurePreserving_mul_left μ g).comp hf

@[to_additive]
/-
**MeasureTheory.measurePreserving_mul_right** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory`。
形式化陈述：measurePreserving_mul_right (μ : Measure G) [IsMulRightInvariant μ] (g : G
) : MeasurePreserving (· * g) μ μ
参数：μ : Measure G；g : G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableMul.measurable_mul_const`：∀ {M : Type u_2} {inst : MeasurableS
pace M} {inst_1 : Mul M} [self : MeasurableMul M] (c : M), Measurable fun x => x
 * c
· 使用定理 `MeasureTheory.map_mul_right_eq_self`：map_mul_right_eq_self (μ : Measure 
G) [IsMulRightInvariant μ] (g : G) : map (· * g) μ = μ
-/
theorem measurePreserving_mul_right (μ : Measure G) [IsMulRightInvariant μ] (g : G) :
    MeasurePreserving (· * g) μ μ :=
  ⟨measurable_mul_const g, map_mul_right_eq_self μ g⟩

@[to_additive]
/-
**MeasureTheory.MeasurePreserving.mul_right** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.MeasurePreserving`。
形式化陈述：∀ {G : Type u_1} [inst : MeasurableSpace G] [inst_1 : Mul G] [MeasurableMu
l G] (μ : MeasureTheory.Measure G)   [μ.IsMulRightInvariant] (g : G) {X : Type u
_3} [inst_4 : MeasurableSpace X] {μ' : MeasureTheory.Measure X}   {f : X → G}, M
easureTheory.MeasurePreserving f μ' μ → MeasureTheory.MeasurePreserving (fun x =
> f x * g) μ' μ
参数：μ : MeasureTheory.Measure G；g : G；fun x => f x * g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.MeasurePreserving.comp`：∀ {α : Type u_1} {β : Type u_2} {γ
 : Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   [inst_2 :
 MeasurableSpace γ] {μa : …
· 使用定理 `MeasureTheory.measurePreserving_mul_right`：measurePreserving_mul_right (
μ : Measure G) [IsMulRightInvariant μ] (g : G) : MeasurePreserving (· * g) μ μ
-/
theorem MeasurePreserving.mul_right (μ : Measure G) [IsMulRightInvariant μ] (g : G) {X : Type*}
    [MeasurableSpace X] {μ' : Measure X} {f : X → G} (hf : MeasurePreserving f μ' μ) :
    MeasurePreserving (fun x => f x * g) μ' μ :=
  (measurePreserving_mul_right μ g).comp hf

@[to_additive]
/-
**MeasureTheory.Subgroup.smulInvariantMeasure** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.Subgroup`。
形式化陈述：∀ {G : Type u_3} {α : Type u_4} [inst : Group G] [inst_1 : MulAction G α] 
[inst_2 : MeasurableSpace α]   {μ : MeasureTheory.Measure α} [MeasureTheory.SMul
InvariantMeasure G α μ] (H : Subgroup G),   MeasureTheory.SMulInvariantMeasure (
↥H) α μ
参数：H : Subgroup G；↥H。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.SMulInvariantMeasure.measure_preimage_smul`：∀ {M : Type u_
1} {α : Type u_2} {inst : SMul M α} {x : MeasurableSpace α} {μ : MeasureTheory.M
easure α}   [self : MeasureTheory.SMulInvarian…
-/
instance Subgroup.smulInvariantMeasure {G α : Type*} [Group G] [MulAction G α] [MeasurableSpace α]
    {μ : Measure α} [SMulInvariantMeasure G α μ] (H : Subgroup G) : SMulInvariantMeasure H α μ :=
  ⟨fun y s hs => by convert! SMulInvariantMeasure.measure_preimage_smul (μ := μ) (y : G) hs⟩

/-- An alternative way to prove that `μ` is left invariant under multiplication. -/
@[to_additive /-- An alternative way to prove that `μ` is left invariant under addition. -/]
/-
**MeasureTheory.forall_measure_preimage_mul_iff** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory`。
形式化陈述：forall_measure_preimage_mul_iff (μ : Measure G) : (forall (g : G) (A : Set
 G), MeasurableSet A -> μ ((fun h => g * h) ⁻¹' A) = μ A) ↔ IsMulLeftInvariant μ
参数：μ : Measure G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `MeasureTheory.Measure.map_apply`：map_apply (hf : Measurable f) {s : Set 
β} (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)
· 使用定理 `MeasurableMul.measurable_const_mul`：∀ {M : Type u_2} {inst : MeasurableS
pace M} {inst_1 : Mul M} [self : MeasurableMul M] (c : M), Measurable fun x => c
 * x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `MeasureTheory.Measure.IsMulLeftInvariant.map_mul_left_eq_self`：∀ {G : Ty
pe u_1} {inst : MeasurableSpace G} {inst_1 : Mul G} {μ : MeasureTheory.Measure G
} [self : μ.IsMulLeftInvariant]   (g : G), MeasureT…

--- 原说明 ---
An alternative way to prove that `μ` is left invariant under multiplication.
-/
theorem forall_measure_preimage_mul_iff (μ : Measure G) :
    (∀ (g : G) (A : Set G), MeasurableSet A → μ ((fun h => g * h) ⁻¹' A) = μ A) ↔
      IsMulLeftInvariant μ := by
  trans ∀ g, map (g * ·) μ = μ
  · simp_rw [Measure.ext_iff]
    refine forall_congr' fun g => forall_congr' fun A => forall_congr' fun hA => ?_
    rw [map_apply (measurable_const_mul g) hA]
  exact ⟨fun h => ⟨h⟩, fun h => h.1⟩

/-- An alternative way to prove that `μ` is right invariant under multiplication. -/
@[to_additive /-- An alternative way to prove that `μ` is right invariant under addition. -/]
/-
**MeasureTheory.forall_measure_preimage_mul_right_iff** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory`。
形式化陈述：forall_measure_preimage_mul_right_iff (μ : Measure G) : (forall (g : G) (A
 : Set G), MeasurableSet A -> μ ((fun h => h * g) ⁻¹' A) = μ A) ↔ IsMulRightInva
riant μ
参数：μ : Measure G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `MeasureTheory.Measure.map_apply`：map_apply (hf : Measurable f) {s : Set 
β} (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)
· 使用定理 `MeasurableMul.measurable_mul_const`：∀ {M : Type u_2} {inst : MeasurableS
pace M} {inst_1 : Mul M} [self : MeasurableMul M] (c : M), Measurable fun x => x
 * c
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `MeasureTheory.Measure.IsMulRightInvariant.map_mul_right_eq_self`：∀ {G : 
Type u_1} {inst : MeasurableSpace G} {inst_1 : Mul G} {μ : MeasureTheory.Measure
 G}   [self : μ.IsMulRightInvariant] (g : G), Measure…

--- 原说明 ---
An alternative way to prove that `μ` is right invariant under multiplication.
-/
theorem forall_measure_preimage_mul_right_iff (μ : Measure G) :
    (∀ (g : G) (A : Set G), MeasurableSet A → μ ((fun h => h * g) ⁻¹' A) = μ A) ↔
      IsMulRightInvariant μ := by
  trans ∀ g, map (· * g) μ = μ
  · simp_rw [Measure.ext_iff]
    refine forall_congr' fun g => forall_congr' fun A => forall_congr' fun hA => ?_
    rw [map_apply (measurable_mul_const g) hA]
  exact ⟨fun h => ⟨h⟩, fun h => h.1⟩

@[to_additive]
/-
**MeasureTheory.Measure.prod.instIsMulLeftInvariant** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory.Measure.prod`。
形式化陈述：∀ {G : Type u_1} [inst : MeasurableSpace G] [inst_1 : Mul G] {μ : MeasureT
heory.Measure G} [MeasurableMul G]   [μ.IsMulLeftInvariant] [MeasureTheory.SFini
te μ] {H : Type u_3} [inst_5 : Mul H] {mH : MeasurableSpace H}   {ν : MeasureThe
ory.Measure H} [MeasurableMul H] [ν.IsMulLeftInvariant] [MeasureTheory.SFinite ν
],   (μ.prod ν).IsMulLeftInvariant
参数：μ.prod ν。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.map_prod_map`：map_prod_map {δ} [MeasurableSpace δ]
 {f : α -> β} {g : γ -> δ} (μa : Measure α) (μc : Measure γ) [SFinite μa] [SFini
te μc] (hf : Measurable …
· 使用定理 `MeasurableMul.measurable_const_mul`：∀ {M : Type u_2} {inst : MeasurableS
pace M} {inst_1 : Mul M} [self : MeasurableMul M] (c : M), Measurable fun x => c
 * x
· 使用定理 `MeasureTheory.map_mul_left_eq_self`：map_mul_left_eq_self (μ : Measure G)
 [IsMulLeftInvariant μ] (g : G) : map (g * ·) μ = μ
-/
instance Measure.prod.instIsMulLeftInvariant [IsMulLeftInvariant μ] [SFinite μ] {H : Type*}
    [Mul H] {mH : MeasurableSpace H} {ν : Measure H} [MeasurableMul H] [IsMulLeftInvariant ν]
    [SFinite ν] : IsMulLeftInvariant (μ.prod ν) := by
  constructor
  rintro ⟨g, h⟩
  change map (Prod.map (g * ·) (h * ·)) (μ.prod ν) = μ.prod ν
  rw [← map_prod_map _ _ (measurable_const_mul g) (measurable_const_mul h),
    map_mul_left_eq_self μ g, map_mul_left_eq_self ν h]

@[to_additive]
/-
**MeasureTheory.Measure.prod.instIsMulRightInvariant** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory.Measure.prod`。
形式化陈述：∀ {G : Type u_1} [inst : MeasurableSpace G] [inst_1 : Mul G] {μ : MeasureT
heory.Measure G} [MeasurableMul G]   [μ.IsMulRightInvariant] [MeasureTheory.SFin
ite μ] {H : Type u_3} [inst_5 : Mul H] {mH : MeasurableSpace H}   {ν : MeasureTh
eory.Measure H} [MeasurableMul H] [ν.IsMulRightInvariant] [MeasureTheory.SFinite
 ν],   (μ.prod ν).IsMulRightInvariant
参数：μ.prod ν。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.map_prod_map`：map_prod_map {δ} [MeasurableSpace δ]
 {f : α -> β} {g : γ -> δ} (μa : Measure α) (μc : Measure γ) [SFinite μa] [SFini
te μc] (hf : Measurable …
· 使用定理 `MeasurableMul.measurable_mul_const`：∀ {M : Type u_2} {inst : MeasurableS
pace M} {inst_1 : Mul M} [self : MeasurableMul M] (c : M), Measurable fun x => x
 * c
· 使用定理 `MeasureTheory.map_mul_right_eq_self`：map_mul_right_eq_self (μ : Measure 
G) [IsMulRightInvariant μ] (g : G) : map (· * g) μ = μ
-/
instance Measure.prod.instIsMulRightInvariant [IsMulRightInvariant μ] [SFinite μ] {H : Type*}
    [Mul H] {mH : MeasurableSpace H} {ν : Measure H} [MeasurableMul H] [IsMulRightInvariant ν]
    [SFinite ν] : IsMulRightInvariant (μ.prod ν) := by
  constructor
  rintro ⟨g, h⟩
  change map (Prod.map (· * g) (· * h)) (μ.prod ν) = μ.prod ν
  rw [← map_prod_map _ _ (measurable_mul_const g) (measurable_mul_const h),
    map_mul_right_eq_self μ g, map_mul_right_eq_self ν h]

@[to_additive]
/-
**MeasureTheory.isMulLeftInvariant_map** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`
。
形式化陈述：isMulLeftInvariant_map {H : Type*} [MeasurableSpace H] [Mul H] [Measurable
Mul H] [IsMulLeftInvariant μ] (f : G ->ₙ* H) (hf : Measurable f) (h_surj : Surje
ctive f) : IsMulLeftInvariant (Measure.map f μ)
参数：f : G ->ₙ* H；hf : Measurable f；h_surj : Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.map_map`：map_map {g : β -> γ} {f : α -> β} (hg : M
easurable g) (hf : Measurable f) : (μ.map f).map g = μ.map (g ∘ f)
· 使用定理 `MeasurableMul.measurable_const_mul`：∀ {M : Type u_2} {inst : MeasurableS
pace M} {inst_1 : Mul M} [self : MeasurableMul M] (c : M), Measurable fun x => c
 * x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.map_mul_left_eq_self`：map_mul_left_eq_self (μ : Measure G)
 [IsMulLeftInvariant μ] (g : G) : map (g * ·) μ = μ
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem isMulLeftInvariant_map {H : Type*} [MeasurableSpace H] [Mul H] [MeasurableMul H]
    [IsMulLeftInvariant μ] (f : G →ₙ* H) (hf : Measurable f) (h_surj : Surjective f) :
    IsMulLeftInvariant (Measure.map f μ) := by
  refine ⟨fun h => ?_⟩
  rw [map_map (measurable_const_mul _) hf]
  obtain ⟨g, rfl⟩ := h_surj h
  conv_rhs => rw [← map_mul_left_eq_self μ g]
  rw [map_map hf (measurable_const_mul _)]
  congr 2
  ext y
  simp only [comp_apply, map_mul]

end MeasurableMul

end Mul

section Semigroup

variable [Semigroup G] [MeasurableMul G] {μ : Measure G}

/-- The image of a left invariant measure under a left action is left invariant, assuming that
the action preserves multiplication. -/
@[to_additive /-- The image of a left invariant measure under a left additive action is left
invariant, assuming that the action preserves addition. -/]
/-
**MeasureTheory.isMulLeftInvariant_map_smul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory`。
形式化陈述：isMulLeftInvariant_map_smul {α} [SMul α G] [SMulCommClass α G G] [Measurab
leConstSMul α G] [IsMulLeftInvariant μ] (a : α) : IsMulLeftInvariant (map (a • ·
 : G -> G) μ)
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.forall_measure_preimage_mul_iff`：forall_measure_preimage_m
ul_iff (μ : Measure G) : (forall (g : G) (A : Set G), MeasurableSet A -> μ ((fun
 h => g * h) ⁻¹' A) = μ A) ↔ IsMulL…
· 使用定理 `MeasureTheory.SMulInvariantMeasure.measure_preimage_smul`：∀ {M : Type u_
1} {α : Type u_2} {inst : SMul M α} {x : MeasurableSpace α} {μ : MeasureTheory.M
easure α}   [self : MeasureTheory.SMulInvarian…
· 使用定理 `MeasurableSMul.toMeasurableConstSMul`：∀ {M : Type u_2} {α : Type u_3} {i
nst : SMul M α} {inst_1 : MeasurableSpace M} {inst_2 : MeasurableSpace α}   [sel
f : MeasurableSMul M α], M…
· 使用定理 `measurableSMul_of_mul`：∀ (M : Type u_2) [inst : Mul M] [inst_1 : Measura
bleSpace M] [MeasurableMul M], MeasurableSMul M M
· 使用定理 `MeasureTheory.Measure.IsMulLeftInvariant.smulInvariantMeasure`：∀ {G : Ty
pe u_1} [inst : MeasurableSpace G] {μ : MeasureTheory.Measure G} [inst_1 : Mul G
] [μ.IsMulLeftInvariant],   MeasureTheory.SMulInvar…
-/
theorem isMulLeftInvariant_map_smul
    {α} [SMul α G] [SMulCommClass α G G] [MeasurableConstSMul α G]
    [IsMulLeftInvariant μ] (a : α) :
    IsMulLeftInvariant (map (a • · : G → G) μ) :=
  (forall_measure_preimage_mul_iff _).1 fun x _ hs =>
    (smulInvariantMeasure_map_smul μ a).measure_preimage_smul x hs

/-- The image of a right invariant measure under a left action is right invariant, assuming that
the action preserves multiplication. -/
@[to_additive /-- The image of a right invariant measure under a left additive action is right
invariant, assuming that the action preserves addition. -/]
/-
**MeasureTheory.isMulRightInvariant_map_smul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory`。
形式化陈述：isMulRightInvariant_map_smul {α} [SMul α G] [SMulCommClass α Gᵐᵒᵖ G] [Meas
urableConstSMul α G] [IsMulRightInvariant μ] (a : α) : IsMulRightInvariant (map 
(a • · : G -> G) μ)
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.forall_measure_preimage_mul_right_iff`：forall_measure_prei
mage_mul_right_iff (μ : Measure G) : (forall (g : G) (A : Set G), MeasurableSet 
A -> μ ((fun h => h * g) ⁻¹' A) = μ A) ↔ …
· 使用定理 `MeasureTheory.SMulInvariantMeasure.measure_preimage_smul`：∀ {M : Type u_
1} {α : Type u_2} {inst : SMul M α} {x : MeasurableSpace α} {μ : MeasureTheory.M
easure α}   [self : MeasureTheory.SMulInvarian…
· 使用定理 `MeasurableSMul.toMeasurableConstSMul`：∀ {M : Type u_2} {α : Type u_3} {i
nst : SMul M α} {inst_1 : MeasurableSpace M} {inst_2 : MeasurableSpace α}   [sel
f : MeasurableSMul M α], M…
· 使用定理 `MeasureTheory.Measure.IsMulRightInvariant.toSMulInvariantMeasure_op`：∀ {
G : Type u_1} [inst : MeasurableSpace G] {μ : MeasureTheory.Measure G} [inst_1 :
 Mul G] [μ.IsMulRightInvariant],   MeasureTheory.SMulInva…
-/
theorem isMulRightInvariant_map_smul
    {α} [SMul α G] [SMulCommClass α Gᵐᵒᵖ G] [MeasurableConstSMul α G]
    [IsMulRightInvariant μ] (a : α) :
    IsMulRightInvariant (map (a • · : G → G) μ) :=
  (forall_measure_preimage_mul_right_iff _).1 fun x _ hs =>
    (smulInvariantMeasure_map_smul μ a).measure_preimage_smul (MulOpposite.op x) hs

/-- The image of a left invariant measure under right multiplication is left invariant. -/
@[to_additive isMulLeftInvariant_map_add_right
/-- The image of a left invariant measure under right addition is left invariant. -/]
/-
**MeasureTheory.isMulLeftInvariant_map_mul_right** 是 Mathlib 中的一个实例，位于命名空间 `Meas
ureTheory`。
形式化陈述：isMulLeftInvariant_map_mul_right [IsMulLeftInvariant μ] (g : G) : IsMulLef
tInvariant (map (· * g) μ)
参数：g : G。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.isMulLeftInvariant_map_smul`：isMulLeftInvariant_map_smul {
α} [SMul α G] [SMulCommClass α G G] [MeasurableConstSMul α G] [IsMulLeftInvarian
t μ] (a : α) : IsMulLeftInvaria…
· 使用定理 `MeasurableSMul.toMeasurableConstSMul`：∀ {M : Type u_2} {α : Type u_3} {i
nst : SMul M α} {inst_1 : MeasurableSpace M} {inst_2 : MeasurableSpace α}   [sel
f : MeasurableSMul M α], M…
-/
instance isMulLeftInvariant_map_mul_right [IsMulLeftInvariant μ] (g : G) :
    IsMulLeftInvariant (map (· * g) μ) :=
  isMulLeftInvariant_map_smul (MulOpposite.op g)

/-- The image of a right invariant measure under left multiplication is right invariant. -/
@[to_additive isMulRightInvariant_map_add_left
/-- The image of a right invariant measure under left addition is right invariant. -/]
/-
**MeasureTheory.isMulRightInvariant_map_mul_left** 是 Mathlib 中的一个实例，位于命名空间 `Meas
ureTheory`。
形式化陈述：isMulRightInvariant_map_mul_left [IsMulRightInvariant μ] (g : G) : IsMulRi
ghtInvariant (map (g * ·) μ)
参数：g : G。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.isMulRightInvariant_map_smul`：isMulRightInvariant_map_smul
 {α} [SMul α G] [SMulCommClass α Gᵐᵒᵖ G] [MeasurableConstSMul α G] [IsMulRightIn
variant μ] (a : α) : IsMulRightI…
· 使用定理 `MeasurableSMul.toMeasurableConstSMul`：∀ {M : Type u_2} {α : Type u_3} {i
nst : SMul M α} {inst_1 : MeasurableSpace M} {inst_2 : MeasurableSpace α}   [sel
f : MeasurableSMul M α], M…
· 使用定理 `measurableSMul_of_mul`：∀ (M : Type u_2) [inst : Mul M] [inst_1 : Measura
bleSpace M] [MeasurableMul M], MeasurableSMul M M
-/
instance isMulRightInvariant_map_mul_left [IsMulRightInvariant μ] (g : G) :
    IsMulRightInvariant (map (g * ·) μ) :=
  isMulRightInvariant_map_smul g

end Semigroup

section DivInvMonoid

variable [DivInvMonoid G]

@[to_additive]
/-
**MeasureTheory.map_div_right_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：map_div_right_eq_self (μ : Measure G) [IsMulRightInvariant μ] (g : G) : ma
p (· / g) μ = μ
参数：μ : Measure G；g : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.map_mul_right_eq_self`：map_mul_right_eq_self (μ : Measure 
G) [IsMulRightInvariant μ] (g : G) : map (· * g) μ = μ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_div_right_eq_self (μ : Measure G) [IsMulRightInvariant μ] (g : G) :
    map (· / g) μ = μ := by simp_rw [div_eq_mul_inv, map_mul_right_eq_self μ g⁻¹]

end DivInvMonoid

section Group

variable [Group G] [MeasurableMul G]

@[to_additive]
/-
**MeasureTheory.measurePreserving_div_right** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory`。
形式化陈述：measurePreserving_div_right (μ : Measure G) [IsMulRightInvariant μ] (g : G
) : MeasurePreserving (· / g) μ μ
参数：μ : Measure G；g : G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `MeasureTheory.measurePreserving_mul_right`：measurePreserving_mul_right (
μ : Measure G) [IsMulRightInvariant μ] (g : G) : MeasurePreserving (· * g) μ μ
-/
theorem measurePreserving_div_right (μ : Measure G) [IsMulRightInvariant μ] (g : G) :
    MeasurePreserving (· / g) μ μ := by simp_rw [div_eq_mul_inv, measurePreserving_mul_right μ g⁻¹]

/-- We shorten this from `measure_preimage_mul_left`, since left invariant is the preferred option
  for measures in this formalization. -/
@[to_additive (attr := simp)
/-- We shorten this from `measure_preimage_add_left`, since left invariant is the preferred option
for measures in this formalization. -/]
/-
**MeasureTheory.measure_preimage_mul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：measure_preimage_mul (μ : Measure G) [IsMulLeftInvariant μ] (g : G) (A : S
et G) : μ ((fun h => g * h) ⁻¹' A) = μ A
参数：μ : Measure G；g : G；A : Set G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasurableEquiv.map_apply`：∀ {α : Type u_1} {β : Type u_2} {x : Measurab
leSpace α} [inst : MeasurableSpace β] {μ : MeasureTheory.Measure α}   (f : α ≃ᵐ 
β) (s : Set β),…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.map_mul_left_eq_self`：map_mul_left_eq_self (μ : Measure G)
 [IsMulLeftInvariant μ] (g : G) : map (g * ·) μ = μ
-/
theorem measure_preimage_mul (μ : Measure G) [IsMulLeftInvariant μ] (g : G) (A : Set G) :
    μ ((fun h => g * h) ⁻¹' A) = μ A :=
  calc
    μ ((fun h => g * h) ⁻¹' A) = map (fun h => g * h) μ A :=
      ((MeasurableEquiv.mulLeft g).map_apply A).symm
    _ = μ A := by rw [map_mul_left_eq_self μ g]

@[to_additive (attr := simp)]
/-
**MeasureTheory.measure_preimage_mul_right** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory`。
形式化陈述：measure_preimage_mul_right (μ : Measure G) [IsMulRightInvariant μ] (g : G)
 (A : Set G) : μ ((fun h => h * g) ⁻¹' A) = μ A
参数：μ : Measure G；g : G；A : Set G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasurableEquiv.map_apply`：∀ {α : Type u_1} {β : Type u_2} {x : Measurab
leSpace α} [inst : MeasurableSpace β] {μ : MeasureTheory.Measure α}   (f : α ≃ᵐ 
β) (s : Set β),…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.map_mul_right_eq_self`：map_mul_right_eq_self (μ : Measure 
G) [IsMulRightInvariant μ] (g : G) : map (· * g) μ = μ
-/
theorem measure_preimage_mul_right (μ : Measure G) [IsMulRightInvariant μ] (g : G) (A : Set G) :
    μ ((fun h => h * g) ⁻¹' A) = μ A :=
  calc
    μ ((fun h => h * g) ⁻¹' A) = map (fun h => h * g) μ A :=
      ((MeasurableEquiv.mulRight g).map_apply A).symm
    _ = μ A := by rw [map_mul_right_eq_self μ g]

@[to_additive]
/-
**MeasureTheory.map_mul_left_ae** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：map_mul_left_ae (μ : Measure G) [IsMulLeftInvariant μ] (x : G) : Filter.ma
p (fun h => x * h) (ae μ) = ae μ
参数：μ : Measure G；x : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasurableEquiv.map_ae`：map_ae (f : α ≃ᵐ β) (μ : Measure α) : Filter.map
 f (ae μ) = ae (map f μ)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `MeasureTheory.map_mul_left_eq_self`：map_mul_left_eq_self (μ : Measure G)
 [IsMulLeftInvariant μ] (g : G) : map (g * ·) μ = μ
-/
theorem map_mul_left_ae (μ : Measure G) [IsMulLeftInvariant μ] (x : G) :
    Filter.map (fun h => x * h) (ae μ) = ae μ :=
  ((MeasurableEquiv.mulLeft x).map_ae μ).trans <| congr_arg ae <| map_mul_left_eq_self μ x

@[to_additive]
/-
**MeasureTheory.map_mul_right_ae** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：map_mul_right_ae (μ : Measure G) [IsMulRightInvariant μ] (x : G) : Filter.
map (fun h => h * x) (ae μ) = ae μ
参数：μ : Measure G；x : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasurableEquiv.map_ae`：map_ae (f : α ≃ᵐ β) (μ : Measure α) : Filter.map
 f (ae μ) = ae (map f μ)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `MeasureTheory.map_mul_right_eq_self`：map_mul_right_eq_self (μ : Measure 
G) [IsMulRightInvariant μ] (g : G) : map (· * g) μ = μ
-/
theorem map_mul_right_ae (μ : Measure G) [IsMulRightInvariant μ] (x : G) :
    Filter.map (fun h => h * x) (ae μ) = ae μ :=
  ((MeasurableEquiv.mulRight x).map_ae μ).trans <| congr_arg ae <| map_mul_right_eq_self μ x

@[to_additive]
/-
**MeasureTheory.map_div_right_ae** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：map_div_right_ae (μ : Measure G) [IsMulRightInvariant μ] (x : G) : Filter.
map (fun t => t / x) (ae μ) = ae μ
参数：μ : Measure G；x : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasurableEquiv.map_ae`：map_ae (f : α ≃ᵐ β) (μ : Measure α) : Filter.map
 f (ae μ) = ae (map f μ)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `MeasureTheory.map_div_right_eq_self`：map_div_right_eq_self (μ : Measure 
G) [IsMulRightInvariant μ] (g : G) : map (· / g) μ = μ
-/
theorem map_div_right_ae (μ : Measure G) [IsMulRightInvariant μ] (x : G) :
    Filter.map (fun t => t / x) (ae μ) = ae μ :=
  ((MeasurableEquiv.divRight x).map_ae μ).trans <| congr_arg ae <| map_div_right_eq_self μ x

@[to_additive]
/-
**MeasureTheory.eventually_mul_left_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
`。
形式化陈述：eventually_mul_left_iff (μ : Measure G) [IsMulLeftInvariant μ] (t : G) {p 
: G -> Prop} : (forallᵐ x ∂μ, p (t * x)) ↔ forallᵐ x ∂μ, p x
参数：μ : Measure G；t : G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.Eventually.eq_1`：∀ {α : Type u_1} (p : α → Prop) (f : Filter α), 
Filter.Eventually p f = ({x | p x} ∈ f)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.map_mul_left_ae`：map_mul_left_ae (μ : Measure G) [IsMulLef
tInvariant μ] (x : G) : Filter.map (fun h => x * h) (ae μ) = ae μ
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem eventually_mul_left_iff (μ : Measure G) [IsMulLeftInvariant μ] (t : G) {p : G → Prop} :
    (∀ᵐ x ∂μ, p (t * x)) ↔ ∀ᵐ x ∂μ, p x := by
  conv_rhs => rw [Filter.Eventually, ← map_mul_left_ae μ t]
  rfl

@[to_additive]
/-
**MeasureTheory.eventually_mul_right_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y`。
形式化陈述：eventually_mul_right_iff (μ : Measure G) [IsMulRightInvariant μ] (t : G) {
p : G -> Prop} : (forallᵐ x ∂μ, p (x * t)) ↔ forallᵐ x ∂μ, p x
参数：μ : Measure G；t : G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.Eventually.eq_1`：∀ {α : Type u_1} (p : α → Prop) (f : Filter α), 
Filter.Eventually p f = ({x | p x} ∈ f)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.map_mul_right_ae`：map_mul_right_ae (μ : Measure G) [IsMulR
ightInvariant μ] (x : G) : Filter.map (fun h => h * x) (ae μ) = ae μ
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem eventually_mul_right_iff (μ : Measure G) [IsMulRightInvariant μ] (t : G) {p : G → Prop} :
    (∀ᵐ x ∂μ, p (x * t)) ↔ ∀ᵐ x ∂μ, p x := by
  conv_rhs => rw [Filter.Eventually, ← map_mul_right_ae μ t]
  rfl

@[to_additive]
/-
**MeasureTheory.eventually_div_right_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y`。
形式化陈述：eventually_div_right_iff (μ : Measure G) [IsMulRightInvariant μ] (t : G) {
p : G -> Prop} : (forallᵐ x ∂μ, p (x / t)) ↔ forallᵐ x ∂μ, p x
参数：μ : Measure G；t : G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.Eventually.eq_1`：∀ {α : Type u_1} (p : α → Prop) (f : Filter α), 
Filter.Eventually p f = ({x | p x} ∈ f)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.map_div_right_ae`：map_div_right_ae (μ : Measure G) [IsMulR
ightInvariant μ] (x : G) : Filter.map (fun t => t / x) (ae μ) = ae μ
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem eventually_div_right_iff (μ : Measure G) [IsMulRightInvariant μ] (t : G) {p : G → Prop} :
    (∀ᵐ x ∂μ, p (x / t)) ↔ ∀ᵐ x ∂μ, p x := by
  conv_rhs => rw [Filter.Eventually, ← map_div_right_ae μ t]
  rfl

@[to_additive AddSubgroup.index_mul_measure]
/-
**MeasureTheory.Subgroup.index_mul_measure** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.Subgroup`。
形式化陈述：∀ {G : Type u_1} [inst : MeasurableSpace G] [inst_1 : Group G] [Measurable
Mul G] (H : Subgroup G) [H.FiniteIndex],   MeasurableSet ↑H → ∀ (μ : MeasureTheo
ry.Measure G) [μ.IsMulLeftInvariant], ↑H.index * μ ↑H = μ Set.univ
参数：H : Subgroup G；μ : MeasureTheory.Measure G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Subgroup.exists_isComplement_left`：exists_isComplement_left (H : Subgrou
p G) (g : G) : exists S, IsComplement S H ∧ g in S
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subgroup.IsComplement.finite_left_iff`：finite_left_iff (h : IsComplement
 S H) : Finite S ↔ H.FiniteIndex
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.measure_smul`：measure_smul (c : G) (s : Set α) : μ (c • s)
 = μ s
· 使用定理 `MeasureTheory.Measure.IsMulLeftInvariant.smulInvariantMeasure`：∀ {G : Ty
pe u_1} [inst : MeasurableSpace G] {μ : MeasureTheory.Measure G} [inst_1 : Mul G
] [μ.IsMulLeftInvariant],   MeasureTheory.SMulInvar…
· 使用引理 `ENNReal.tsum_const`：tsum_const (c : Real>=0∞) : ∑' _ : α, c = ENat.card 
α * c
· 使用定理 `Subgroup.IsComplement.encard_left`：encard_left [H.FiniteIndex] (h : IsCo
mplement S H) : S.encard = H.index
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.measure_iUnion`：measure_iUnion {m0 : MeasurableSpace α} {μ
 : Measure α} [Countable ι] {f : ι -> Set α} (hn : Pairwise (Disjoint on f)) (h 
: forall i, Measur…
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `Subgroup.IsComplement.pairwiseDisjoint_smul`：∀ {G : Type u_1} [inst : Gr
oup G] {S T : Set G}, Subgroup.IsComplement S T → S.PairwiseDisjoint fun x => x 
• T
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Function.Injective.ne`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Func
tion.Injective f → ∀ {a₁ a₂ : α}, a₁ ≠ a₂ → f a₁ ≠ f a₂
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `MeasurableSet.const_smul`：MeasurableSet.const_smul {G α : Type*} [Group 
G] [MulAction G α] [MeasurableSpace α] [MeasurableConstSMul G α] {s : Set α} (hs
 : MeasurableS…
· 使用定理 `MeasurableSMul.toMeasurableConstSMul`：∀ {M : Type u_2} {α : Type u_3} {i
nst : SMul M α} {inst_1 : MeasurableSpace M} {inst_2 : MeasurableSpace α}   [sel
f : MeasurableSMul M α], M…
· 使用定理 `measurableSMul_of_mul`：∀ (M : Type u_2) [inst : Mul M] [inst_1 : Measura
bleSpace M] [MeasurableMul M], MeasurableSMul M M
· 使用定理 `Set.iUnion_coe_set`：iUnion_coe_set {α β : Type*} (s : Set α) (f : s -> S
et β) : ⋃ i, f i = ⋃ i in s, f ⟨i, ‹i in s›⟩
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用引理 `Set.iUnion_smul_set`：iUnion_smul_set (s : Set α) (t : Set β) : ⋃ a in s,
 a • t = s • t
· 使用定理 `Subgroup.IsComplement.mul_eq`：∀ {G : Type u_1} [inst : Group G] {S T : S
et G}, Subgroup.IsComplement S T → S * T = Set.univ
-/
lemma Subgroup.index_mul_measure (H : Subgroup G) [H.FiniteIndex] (hH : MeasurableSet (H : Set G))
    (μ : Measure G) [IsMulLeftInvariant μ] : H.index * μ H = μ univ := by
  obtain ⟨s, hs, -⟩ := H.exists_isComplement_left 1
  have hs' : Finite s := hs.finite_left_iff.mpr inferInstance
  calc
    H.index * μ H = ∑' a : s, μ (a.val • H) := by simp [measure_smul, hs.encard_left]
    _ = μ univ := by
      rw [← measure_iUnion _ fun _ ↦ hH.const_smul _]
      · simp [hs.mul_eq]
      · exact fun a b hab ↦ hs.pairwiseDisjoint_smul a.2 b.2 (Subtype.val_injective.ne hab)

end Group

namespace Measure

-- TODO: noncomputable has to be specified explicitly. https://github.com/leanprover-community/mathlib4/issues/1074 (item 8)

/-- The measure `A ↦ μ (A⁻¹)`, where `A⁻¹` is the pointwise inverse of `A`. -/
@[to_additive /-- The measure `A ↦ μ (- A)`, where `- A` is the pointwise negation of `A`. -/]
/-
**MeasureTheory.Measure.inv** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：{G : Type u_1} → [inst : MeasurableSpace G] → [Inv G] → MeasureTheory.Meas
ure G → MeasureTheory.Measure G
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The measure `A ↦ μ (A⁻¹)`, where `A⁻¹` is the pointwise inverse of `A`.
-/
protected noncomputable def inv [Inv G] (μ : Measure G) : Measure G :=
  Measure.map inv μ

/-- A measure is invariant under negation if `- μ = μ`. Equivalently, this means that for all
measurable `A` we have `μ (- A) = μ A`, where `- A` is the pointwise negation of `A`. -/
/-
**MeasureTheory.Measure.IsNegInvariant** 是 Mathlib 中的一个归纳类型，位于命名空间 `MeasureTheor
y.Measure`。
形式化陈述：{G : Type u_1} → [inst : MeasurableSpace G] → [Neg G] → MeasureTheory.Meas
ure G → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A measure is invariant under negation if `- μ = μ`. Equivalently, this means tha
t for all
measurable `A` we have `μ (- A) = μ A`, where `- A` is the pointwise negation of
 `A`.
-/
class IsNegInvariant [Neg G] (μ : Measure G) : Prop where
  neg_eq_self : μ.neg = μ

/-- A measure is invariant under inversion if `μ⁻¹ = μ`. Equivalently, this means that for all
measurable `A` we have `μ (A⁻¹) = μ A`, where `A⁻¹` is the pointwise inverse of `A`. -/
@[to_additive existing]
/-
**MeasureTheory.Measure.IsInvInvariant** 是 Mathlib 中的一个归纳类型，位于命名空间 `MeasureTheor
y.Measure`。
形式化陈述：{G : Type u_1} → [inst : MeasurableSpace G] → [Inv G] → MeasureTheory.Meas
ure G → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A measure is invariant under inversion if `μ⁻¹ = μ`. Equivalently, this means th
at for all
measurable `A` we have `μ (A⁻¹) = μ A`, where `A⁻¹` is the pointwise inverse of 
`A`.
-/
class IsInvInvariant [Inv G] (μ : Measure G) : Prop where
  inv_eq_self : μ.inv = μ

section Inv

variable [Inv G]

@[to_additive]
/-
**MeasureTheory.Measure.inv_def** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measure
`。
形式化陈述：inv_def (μ : Measure G) : μ.inv = Measure.map inv μ
参数：μ : Measure G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inv_def (μ : Measure G) : μ.inv = Measure.map inv μ := rfl

@[to_additive (attr := simp)]
/-
**MeasureTheory.Measure.inv_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Mea
sure`。
形式化陈述：inv_eq_self (μ : Measure G) [IsInvInvariant μ] : μ.inv = μ
参数：μ : Measure G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.IsInvInvariant.inv_eq_self`：∀ {G : Type u_1} {inst
 : MeasurableSpace G} {inst_1 : Inv G} {μ : MeasureTheory.Measure G} [self : μ.I
sInvInvariant],   μ.inv = μ
-/
theorem inv_eq_self (μ : Measure G) [IsInvInvariant μ] : μ.inv = μ :=
  IsInvInvariant.inv_eq_self

@[to_additive (attr := simp)]
/-
**MeasureTheory.Measure.map_inv_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.Measure`。
形式化陈述：map_inv_eq_self (μ : Measure G) [IsInvInvariant μ] : map Inv.inv μ = μ
参数：μ : Measure G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.IsInvInvariant.inv_eq_self`：∀ {G : Type u_1} {inst
 : MeasurableSpace G} {inst_1 : Inv G} {μ : MeasureTheory.Measure G} [self : μ.I
sInvInvariant],   μ.inv = μ
-/
theorem map_inv_eq_self (μ : Measure G) [IsInvInvariant μ] : map Inv.inv μ = μ :=
  IsInvInvariant.inv_eq_self

variable [MeasurableInv G]

@[to_additive]
/-
**MeasureTheory.Measure.measurePreserving_inv** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.Measure`。
形式化陈述：measurePreserving_inv (μ : Measure G) [IsInvInvariant μ] : MeasurePreservi
ng Inv.inv μ μ
参数：μ : Measure G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableInv.measurable_inv`：∀ {G : Type u_2} {inst : Inv G} {inst_1 : 
MeasurableSpace G} [self : MeasurableInv G], Measurable Inv.inv
· 使用定理 `MeasureTheory.Measure.map_inv_eq_self`：map_inv_eq_self (μ : Measure G) [
IsInvInvariant μ] : map Inv.inv μ = μ
-/
theorem measurePreserving_inv (μ : Measure G) [IsInvInvariant μ] : MeasurePreserving Inv.inv μ μ :=
  ⟨measurable_inv, map_inv_eq_self μ⟩

@[to_additive]
/-
**MeasureTheory.Measure.inv.instSFinite** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.Measure.inv`。
形式化陈述：∀ {G : Type u_1} [inst : MeasurableSpace G] [inst_1 : Inv G] (μ : MeasureT
heory.Measure G) [MeasureTheory.SFinite μ],   MeasureTheory.SFinite μ.inv
参数：μ : MeasureTheory.Measure G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.inv.eq_1`：∀ {G : Type u_1} [inst : MeasurableSpace
 G] [inst_1 : Inv G] (μ : MeasureTheory.Measure G),   μ.inv = MeasureTheory.Meas
ure.map Inv.inv μ
· 使用定理 `MeasureTheory.Measure.instSFiniteMap`：∀ {α : Type u_2} {β : Type u_3} {m
0 : MeasurableSpace α} [inst : MeasurableSpace β] (μ : MeasureTheory.Measure α) 
  (f : α → β) [MeasureTheo…
-/
instance inv.instSFinite (μ : Measure G) [SFinite μ] : SFinite μ.inv := by
  rw [Measure.inv]; infer_instance

end Inv

section InvolutiveInv

variable [InvolutiveInv G] [MeasurableInv G]

@[to_additive (attr := simp)]
/-
**MeasureTheory.Measure.inv_apply** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measu
re`。
形式化陈述：inv_apply (μ : Measure G) (s : Set G) : μ.inv s = μ s⁻¹
参数：μ : Measure G；s : Set G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableEquiv.map_apply`：∀ {α : Type u_1} {β : Type u_2} {x : Measurab
leSpace α} [inst : MeasurableSpace β] {μ : MeasureTheory.Measure α}   (f : α ≃ᵐ 
β) (s : Set β),…
-/
theorem inv_apply (μ : Measure G) (s : Set G) : μ.inv s = μ s⁻¹ :=
  (MeasurableEquiv.inv G).map_apply s

@[to_additive (attr := simp)]
/-
**MeasureTheory.Measure.inv_inv** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measure
`。
形式化陈述：∀ {G : Type u_1} [inst : MeasurableSpace G] [inst_1 : InvolutiveInv G] [Me
asurableInv G] (μ : MeasureTheory.Measure G),   μ.inv.inv = μ
参数：μ : MeasureTheory.Measure G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableEquiv.map_symm_map`：map_symm_map (e : α ≃ᵐ β) : (μ.map e).map 
e.symm = μ
-/
protected theorem inv_inv (μ : Measure G) : μ.inv.inv = μ :=
  (MeasurableEquiv.inv G).map_symm_map

@[to_additive (attr := simp)]
/-
**MeasureTheory.Measure.measure_inv** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Mea
sure`。
形式化陈述：measure_inv (μ : Measure G) [IsInvInvariant μ] (A : Set G) : μ A⁻¹ = μ A
参数：μ : Measure G；A : Set G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.inv_apply`：inv_apply (μ : Measure G) (s : Set G) :
 μ.inv s = μ s⁻¹
· 使用定理 `MeasureTheory.Measure.inv_eq_self`：inv_eq_self (μ : Measure G) [IsInvInv
ariant μ] : μ.inv = μ
-/
theorem measure_inv (μ : Measure G) [IsInvInvariant μ] (A : Set G) : μ A⁻¹ = μ A := by
  rw [← inv_apply, inv_eq_self]

@[to_additive]
/-
**MeasureTheory.Measure.measure_preimage_inv** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.Measure`。
形式化陈述：measure_preimage_inv (μ : Measure G) [IsInvInvariant μ] (A : Set G) : μ (I
nv.inv ⁻¹' A) = μ A
参数：μ : Measure G；A : Set G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.measure_inv`：measure_inv (μ : Measure G) [IsInvInv
ariant μ] (A : Set G) : μ A⁻¹ = μ A
-/
theorem measure_preimage_inv (μ : Measure G) [IsInvInvariant μ] (A : Set G) :
    μ (Inv.inv ⁻¹' A) = μ A :=
  μ.measure_inv A

@[to_additive]
/-
**MeasureTheory.Measure.inv.instSigmaFinite** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.Measure.inv`。
形式化陈述：∀ {G : Type u_1} [inst : MeasurableSpace G] [inst_1 : InvolutiveInv G] [Me
asurableInv G] (μ : MeasureTheory.Measure G)   [MeasureTheory.SigmaFinite μ], Me
asureTheory.SigmaFinite μ.inv
参数：μ : MeasureTheory.Measure G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableEquiv.sigmaFinite_map`：∀ {α : Type u_1} {β : Type u_2} {m0 : M
easurableSpace α} [inst : MeasurableSpace β] {μ : MeasureTheory.Measure α}   (f 
: α ≃ᵐ β) [MeasureThe…
-/
instance inv.instSigmaFinite (μ : Measure G) [SigmaFinite μ] : SigmaFinite μ.inv :=
  (MeasurableEquiv.inv G).sigmaFinite_map

end InvolutiveInv

section DivisionMonoid

variable [DivisionMonoid G] [MeasurableMul G] [MeasurableInv G] {μ : Measure G}

@[to_additive]
/-
**MeasureTheory.Measure.inv.instIsMulRightInvariant** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory.Measure.inv`。
形式化陈述：∀ {G : Type u_1} [inst : MeasurableSpace G] [inst_1 : DivisionMonoid G] [M
easurableMul G] [MeasurableInv G]   {μ : MeasureTheory.Measure G} [μ.IsMulLeftIn
variant], μ.inv.IsMulRightInvariant
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.map_mul_left_eq_self`：map_mul_left_eq_self (μ : Measure G)
 [IsMulLeftInvariant μ] (g : G) : map (g * ·) μ = μ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.Measure.map_map`：map_map {g : β -> γ} {f : α -> β} (hg : M
easurable g) (hf : Measurable f) : (μ.map f).map g = μ.map (g ∘ f)
· 使用定理 `MeasurableMul.measurable_mul_const`：∀ {M : Type u_2} {inst : MeasurableS
pace M} {inst_1 : Mul M} [self : MeasurableMul M] (c : M), Measurable fun x => x
 * c
· 使用定理 `MeasurableInv.measurable_inv`：∀ {G : Type u_2} {inst : Inv G} {inst_1 : 
MeasurableSpace G} [self : MeasurableInv G], Measurable Inv.inv
· 使用定理 `MeasurableMul.measurable_const_mul`：∀ {M : Type u_2} {inst : MeasurableS
pace M} {inst_1 : Mul M} [self : MeasurableMul M] (c : M), Measurable fun x => c
 * x
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance inv.instIsMulRightInvariant [IsMulLeftInvariant μ] : IsMulRightInvariant μ.inv := by
  constructor
  intro g
  conv_rhs => rw [← map_mul_left_eq_self μ g⁻¹]
  simp_rw [Measure.inv, map_map (measurable_mul_const g) measurable_inv,
    map_map measurable_inv (measurable_const_mul g⁻¹), Function.comp_def, mul_inv_rev, inv_inv]

@[to_additive]
/-
**MeasureTheory.Measure.inv.instIsMulLeftInvariant** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory.Measure.inv`。
形式化陈述：∀ {G : Type u_1} [inst : MeasurableSpace G] [inst_1 : DivisionMonoid G] [M
easurableMul G] [MeasurableInv G]   {μ : MeasureTheory.Measure G} [μ.IsMulRightI
nvariant], μ.inv.IsMulLeftInvariant
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.map_mul_right_eq_self`：map_mul_right_eq_self (μ : Measure 
G) [IsMulRightInvariant μ] (g : G) : map (· * g) μ = μ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.Measure.map_map`：map_map {g : β -> γ} {f : α -> β} (hg : M
easurable g) (hf : Measurable f) : (μ.map f).map g = μ.map (g ∘ f)
· 使用定理 `MeasurableMul.measurable_const_mul`：∀ {M : Type u_2} {inst : MeasurableS
pace M} {inst_1 : Mul M} [self : MeasurableMul M] (c : M), Measurable fun x => c
 * x
· 使用定理 `MeasurableInv.measurable_inv`：∀ {G : Type u_2} {inst : Inv G} {inst_1 : 
MeasurableSpace G} [self : MeasurableInv G], Measurable Inv.inv
· 使用定理 `MeasurableMul.measurable_mul_const`：∀ {M : Type u_2} {inst : MeasurableS
pace M} {inst_1 : Mul M} [self : MeasurableMul M] (c : M), Measurable fun x => x
 * c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance inv.instIsMulLeftInvariant [IsMulRightInvariant μ] : IsMulLeftInvariant μ.inv := by
  constructor
  intro g
  conv_rhs => rw [← map_mul_right_eq_self μ g⁻¹]
  simp_rw [Measure.inv, map_map (measurable_const_mul g) measurable_inv,
    map_map measurable_inv (measurable_mul_const g⁻¹), Function.comp_def, mul_inv_rev, inv_inv]

@[to_additive]
/-
**MeasureTheory.Measure.measurePreserving_div_left** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory.Measure`。
形式化陈述：measurePreserving_div_left (μ : Measure G) [IsInvInvariant μ] [IsMulLeftIn
variant μ] (g : G) : MeasurePreserving (fun t => g / t) μ μ
参数：μ : Measure G；g : G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `MeasureTheory.MeasurePreserving.comp`：∀ {α : Type u_1} {β : Type u_2} {γ
 : Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   [inst_2 :
 MeasurableSpace γ] {μa : …
· 使用定理 `MeasureTheory.measurePreserving_mul_left`：measurePreserving_mul_left (μ 
: Measure G) [IsMulLeftInvariant μ] (g : G) : MeasurePreserving (g * ·) μ μ
· 使用定理 `MeasureTheory.Measure.measurePreserving_inv`：measurePreserving_inv (μ : 
Measure G) [IsInvInvariant μ] : MeasurePreserving Inv.inv μ μ
-/
theorem measurePreserving_div_left (μ : Measure G) [IsInvInvariant μ] [IsMulLeftInvariant μ]
    (g : G) : MeasurePreserving (fun t => g / t) μ μ := by
  simp_rw [div_eq_mul_inv]
  exact (measurePreserving_mul_left μ g).comp (measurePreserving_inv μ)

@[to_additive]
/-
**MeasureTheory.Measure.map_div_left_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.Measure`。
形式化陈述：map_div_left_eq_self (μ : Measure G) [IsInvInvariant μ] [IsMulLeftInvarian
t μ] (g : G) : map (fun t => g / t) μ = μ
参数：μ : Measure G；g : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.MeasurePreserving.map_eq`：∀ {α : Type u_1} {β : Type u_2} 
[inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β}   {μa : auto
Param (MeasureTheory.Measure…
· 使用定理 `MeasureTheory.Measure.measurePreserving_div_left`：measurePreserving_div_
left (μ : Measure G) [IsInvInvariant μ] [IsMulLeftInvariant μ] (g : G) : Measure
Preserving (fun t => g / t) μ μ
-/
theorem map_div_left_eq_self (μ : Measure G) [IsInvInvariant μ] [IsMulLeftInvariant μ] (g : G) :
    map (fun t => g / t) μ = μ :=
  (measurePreserving_div_left μ g).map_eq

@[to_additive]
/-
**MeasureTheory.Measure.measurePreserving_mul_right_inv** 是 Mathlib 中的一个定理，位于命名空
间 `MeasureTheory.Measure`。
形式化陈述：measurePreserving_mul_right_inv (μ : Measure G) [IsInvInvariant μ] [IsMulL
eftInvariant μ] (g : G) : MeasurePreserving (fun t => (g * t)⁻¹) μ μ
参数：μ : Measure G；g : G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.MeasurePreserving.comp`：∀ {α : Type u_1} {β : Type u_2} {γ
 : Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   [inst_2 :
 MeasurableSpace γ] {μa : …
· 使用定理 `MeasureTheory.Measure.measurePreserving_inv`：measurePreserving_inv (μ : 
Measure G) [IsInvInvariant μ] : MeasurePreserving Inv.inv μ μ
· 使用定理 `MeasureTheory.measurePreserving_mul_left`：measurePreserving_mul_left (μ 
: Measure G) [IsMulLeftInvariant μ] (g : G) : MeasurePreserving (g * ·) μ μ
-/
theorem measurePreserving_mul_right_inv (μ : Measure G) [IsInvInvariant μ] [IsMulLeftInvariant μ]
    (g : G) : MeasurePreserving (fun t => (g * t)⁻¹) μ μ :=
  (measurePreserving_inv μ).comp <| measurePreserving_mul_left μ g

@[to_additive]
/-
**MeasureTheory.Measure.map_mul_right_inv_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory.Measure`。
形式化陈述：map_mul_right_inv_eq_self (μ : Measure G) [IsInvInvariant μ] [IsMulLeftInv
ariant μ] (g : G) : map (fun t => (g * t)⁻¹) μ = μ
参数：μ : Measure G；g : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.MeasurePreserving.map_eq`：∀ {α : Type u_1} {β : Type u_2} 
[inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β}   {μa : auto
Param (MeasureTheory.Measure…
· 使用定理 `MeasureTheory.Measure.measurePreserving_mul_right_inv`：measurePreserving
_mul_right_inv (μ : Measure G) [IsInvInvariant μ] [IsMulLeftInvariant μ] (g : G)
 : MeasurePreserving (fun t => (g * t)⁻¹) μ…
-/
theorem map_mul_right_inv_eq_self (μ : Measure G) [IsInvInvariant μ] [IsMulLeftInvariant μ]
    (g : G) : map (fun t => (g * t)⁻¹) μ = μ :=
  (measurePreserving_mul_right_inv μ g).map_eq

end DivisionMonoid

section Group

variable [Group G] {μ : Measure G}

section MeasurableMul

variable [MeasurableMul G]

@[to_additive]
/-
**MeasureTheory.Measure.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (count : Measure G).IsMulLeftInvariant where
  map_mul_left_eq_self g := by
    ext s hs
    rw [count_apply hs, map_apply (measurable_const_mul _) hs,
      count_apply (measurable_const_mul _ hs),
      encard_preimage_of_bijective (Group.mulLeft_bijective _)]

@[to_additive]
/-
**MeasureTheory.Measure.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (count : Measure G).IsMulRightInvariant where
  map_mul_right_eq_self g := by
    ext s hs
    rw [count_apply hs, map_apply (measurable_mul_const _) hs,
      count_apply (measurable_mul_const _ hs),
      encard_preimage_of_bijective (Group.mulRight_bijective _)]

/- TODO: To avoid repeating the proofs, the following two lemmas should be consequences of
a similar result about `SMulInvariantMeasure`. -/

@[to_additive]
/-
**MeasureTheory.Measure.IsMulLeftInvariant.comap** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.Measure.IsMulLeftInvariant`。
形式化陈述：∀ {G : Type u_1} [inst : MeasurableSpace G] [inst_1 : Group G] [Measurable
Mul G] {H : Type u_3} [inst_3 : Group H]   {mH : MeasurableSpace H} [MeasurableM
ul H] (μ : MeasureTheory.Measure H) [μ.IsMulLeftInvariant] {f : G →* H},   Measu
rableEmbedding ⇑f → (MeasureTheory.Measure.comap (⇑f) μ).IsMulLeftInvariant
参数：μ : MeasureTheory.Measure H；MeasureTheory.Measure.comap (⇑f) μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.map_apply`：map_apply (hf : Measurable f) {s : Set 
β} (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)
· 使用定理 `Measurable.const_mul`：Measurable.const_mul [MeasurableMul M] (hf : Measu
rable f) (c : M) : Measurable fun x => c * f x
· 使用定理 `measurable_id'`：measurable_id' {_ : MeasurableSpace α} : Measurable fun 
a : α => a
· 使用定理 `MeasurableEmbedding.comap_apply`：comap_apply (μ : Measure β) (s : Set α)
 : comap f μ s = μ (f '' s)
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `mul_inv_cancel_left`：mul_inv_cancel_left (a b : G) : a * (a⁻¹ * b) = b
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_inv`：map_inv [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f 
: F) (a : G) : f a⁻¹ = (f a)⁻¹
· 使用定理 `inv_mul_cancel_left`：inv_mul_cancel_left (a b : G) : a⁻¹ * (a * b) = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasurableEmbedding.measurableSet_image`：measurableSet_image (hf : Measu
rableEmbedding f) : MeasurableSet (f '' s) ↔ MeasurableSet s
· 使用定理 `MeasureTheory.Measure.IsMulLeftInvariant.map_mul_left_eq_self`：∀ {G : Ty
pe u_1} {inst : MeasurableSpace G} {inst_1 : Mul G} {μ : MeasureTheory.Measure G
} [self : μ.IsMulLeftInvariant]   (g : G), MeasureT…

--- 原说明 ---
TODO: To avoid repeating the proofs, the following two lemmas should be conseque
nces of
a similar result about `SMulInvariantMeasure`.
-/
protected theorem IsMulLeftInvariant.comap {H} [Group H] {mH : MeasurableSpace H} [MeasurableMul H]
    (μ : Measure H) [IsMulLeftInvariant μ] {f : G →* H} (hf : MeasurableEmbedding f) :
    (μ.comap f).IsMulLeftInvariant where
  map_mul_left_eq_self g := by
    ext s hs
    rw [map_apply (by fun_prop) hs]
    repeat rw [hf.comap_apply]
    have : f '' (g * ·) ⁻¹' s = (f g * ·) ⁻¹' f '' s := by
      ext
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨g * y, hy, by simp⟩
      · intro ⟨y, yins, hy⟩
        exact ⟨g⁻¹ * y, by simp [yins], by simp [hy]⟩
    rw [this, ← map_apply (by fun_prop), IsMulLeftInvariant.map_mul_left_eq_self]
    exact hf.measurableSet_image.mpr hs

@[to_additive]
/-
**MeasureTheory.Measure.IsMulRightInvariant.comap** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory.Measure.IsMulRightInvariant`。
形式化陈述：∀ {G : Type u_1} [inst : MeasurableSpace G] [inst_1 : Group G] [Measurable
Mul G] {H : Type u_3} [inst_3 : Group H]   {mH : MeasurableSpace H} [MeasurableM
ul H] (μ : MeasureTheory.Measure H) [μ.IsMulRightInvariant] {f : G →* H},   Meas
urableEmbedding ⇑f → (MeasureTheory.Measure.comap (⇑f) μ).IsMulRightInvariant
参数：μ : MeasureTheory.Measure H；MeasureTheory.Measure.comap (⇑f) μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.map_apply`：map_apply (hf : Measurable f) {s : Set 
β} (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)
· 使用定理 `Measurable.mul_const`：Measurable.mul_const [MeasurableMul M] (hf : Measu
rable f) (c : M) : Measurable fun x => f x * c
· 使用定理 `measurable_id'`：measurable_id' {_ : MeasurableSpace α} : Measurable fun 
a : α => a
· 使用定理 `MeasurableEmbedding.comap_apply`：comap_apply (μ : Measure β) (s : Set α)
 : comap f μ s = μ (f '' s)
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `inv_mul_cancel_right`：inv_mul_cancel_right (a b : G) : a * b⁻¹ * b = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_inv`：map_inv [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f 
: F) (a : G) : f a⁻¹ = (f a)⁻¹
· 使用定理 `mul_inv_cancel_right`：mul_inv_cancel_right (a b : G) : a * b * b⁻¹ = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasurableEmbedding.measurableSet_image`：measurableSet_image (hf : Measu
rableEmbedding f) : MeasurableSet (f '' s) ↔ MeasurableSet s
· 使用定理 `MeasureTheory.Measure.IsMulRightInvariant.map_mul_right_eq_self`：∀ {G : 
Type u_1} {inst : MeasurableSpace G} {inst_1 : Mul G} {μ : MeasureTheory.Measure
 G}   [self : μ.IsMulRightInvariant] (g : G), Measure…
-/
protected theorem IsMulRightInvariant.comap {H} [Group H] {mH : MeasurableSpace H} [MeasurableMul H]
    (μ : Measure H) [IsMulRightInvariant μ] {f : G →* H} (hf : MeasurableEmbedding f) :
    (μ.comap f).IsMulRightInvariant where
  map_mul_right_eq_self g := by
    ext s hs
    rw [map_apply (by fun_prop) hs]
    repeat rw [hf.comap_apply]
    have : f '' (· * g) ⁻¹' s = (· * f g) ⁻¹' f '' s := by
      ext
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y * g, hy, by simp⟩
      · intro ⟨y, yins, hy⟩
        exact ⟨y * g⁻¹, by simp [yins], by simp [hy]⟩
    rw [this, ← map_apply (by fun_prop), IsMulRightInvariant.map_mul_right_eq_self]
    exact hf.measurableSet_image.mpr hs

end MeasurableMul

variable [MeasurableInv G]

@[to_additive]
/-
**MeasureTheory.Measure.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (count : Measure G).IsInvInvariant where
  inv_eq_self := by ext s hs; rw [count_apply hs, inv_apply, count_apply hs.inv, encard_inv]

variable [MeasurableMul G]

@[to_additive]
/-
**MeasureTheory.Measure.map_div_left_ae** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.Measure`。
形式化陈述：map_div_left_ae (μ : Measure G) [IsMulLeftInvariant μ] [IsInvInvariant μ] 
(x : G) : Filter.map (fun t => x / t) (ae μ) = ae μ
参数：μ : Measure G；x : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasurableEquiv.map_ae`：map_ae (f : α ≃ᵐ β) (μ : Measure α) : Filter.map
 f (ae μ) = ae (map f μ)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.map_div_left_eq_self`：map_div_left_eq_self (μ : Me
asure G) [IsInvInvariant μ] [IsMulLeftInvariant μ] (g : G) : map (fun t => g / t
) μ = μ
-/
theorem map_div_left_ae (μ : Measure G) [IsMulLeftInvariant μ] [IsInvInvariant μ] (x : G) :
    Filter.map (fun t => x / t) (ae μ) = ae μ :=
  ((MeasurableEquiv.divLeft x).map_ae μ).trans <| congr_arg ae <| map_div_left_eq_self μ x

end Group

end Measure

section IsTopologicalGroup

variable [TopologicalSpace G] [BorelSpace G] {μ : Measure G} [Group G]

@[to_additive]
/-
**MeasureTheory.Measure.IsFiniteMeasureOnCompacts.inv** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory.Measure.IsFiniteMeasureOnCompacts`。
形式化陈述：∀ {G : Type u_1} [inst : MeasurableSpace G] [inst_1 : TopologicalSpace G] 
[BorelSpace G] {μ : MeasureTheory.Measure G}   [inst_3 : Group G] [ContinuousInv
 G] [MeasureTheory.IsFiniteMeasureOnCompacts μ],   MeasureTheory.IsFiniteMeasure
OnCompacts μ.inv
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.IsFiniteMeasureOnCompacts.map`：∀ {α : Type u_1} {β
 : Type u_2} [inst : TopologicalSpace α] {mα : MeasurableSpace α} [BorelSpace α]
   [mβ : TopologicalSpace β] [inst_2 : Me…
-/
instance Measure.IsFiniteMeasureOnCompacts.inv [ContinuousInv G] [IsFiniteMeasureOnCompacts μ] :
    IsFiniteMeasureOnCompacts μ.inv :=
  IsFiniteMeasureOnCompacts.map μ (Homeomorph.inv G)

@[to_additive]
/-
**MeasureTheory.Measure.IsOpenPosMeasure.inv** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.Measure.IsOpenPosMeasure`。
形式化陈述：∀ {G : Type u_1} [inst : MeasurableSpace G] [inst_1 : TopologicalSpace G] 
[BorelSpace G] {μ : MeasureTheory.Measure G}   [inst_3 : Group G] [ContinuousInv
 G] [μ.IsOpenPosMeasure], μ.inv.IsOpenPosMeasure
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.isOpenPosMeasure_map`：∀ {X : Type u_1} [inst : TopologicalSpa
ce X] {m : MeasurableSpace X} {μ : MeasureTheory.Measure X} [μ.IsOpenPosMeasure]
   [OpensMeasurableSp…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `Homeomorph.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologic
alSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y), Continuous ⇑h
· 使用定理 `Homeomorph.surjective`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologic
alSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y),   Function.Surjective ⇑h
-/
instance Measure.IsOpenPosMeasure.inv [ContinuousInv G] [IsOpenPosMeasure μ] :
    IsOpenPosMeasure μ.inv :=
  (Homeomorph.inv G).continuous.isOpenPosMeasure_map (Homeomorph.inv G).surjective

@[to_additive]
/-
**MeasureTheory.Measure.Regular.inv** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Mea
sure.Regular`。
形式化陈述：∀ {G : Type u_1} [inst : MeasurableSpace G] [inst_1 : TopologicalSpace G] 
[BorelSpace G] {μ : MeasureTheory.Measure G}   [inst_3 : Group G] [ContinuousInv
 G] [μ.Regular], μ.inv.Regular
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.Regular.map`：∀ {α : Type u_1} {β : Type u_2} [inst
 : MeasurableSpace α] {μ : MeasureTheory.Measure α} [inst_1 : TopologicalSpace α
]   [BorelSpace α] [ins…
-/
instance Measure.Regular.inv [ContinuousInv G] [Regular μ] : Regular μ.inv :=
  Regular.map (Homeomorph.inv G)

@[to_additive]
/-
**MeasureTheory.Measure.InnerRegular.inv** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.Measure.InnerRegular`。
形式化陈述：∀ {G : Type u_1} [inst : MeasurableSpace G] [inst_1 : TopologicalSpace G] 
[BorelSpace G] {μ : MeasureTheory.Measure G}   [inst_3 : Group G] [ContinuousInv
 G] [μ.InnerRegular], μ.inv.InnerRegular
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.InnerRegular.map`：∀ {α : Type u_1} {β : Type u_2} 
[inst : MeasurableSpace α] {μ : MeasureTheory.Measure α} [inst_1 : TopologicalSp
ace α]   [BorelSpace α] [ins…
-/
instance Measure.InnerRegular.inv [ContinuousInv G] [InnerRegular μ] : InnerRegular μ.inv :=
  InnerRegular.map (Homeomorph.inv G)

/-- The image of an inner regular measure under map of a left action is again inner regular. -/
@[to_additive
/-- The image of an inner regular measure under map of a left additive action is again
inner regular -/]
/-
**MeasureTheory.innerRegular_map_smul** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory`。
形式化陈述：innerRegular_map_smul {α} [Monoid α] [MulAction α G] [ContinuousConstSMul 
α G] [InnerRegular μ] (a : α) : InnerRegular (Measure.map (a • · : G -> G) μ)
参数：a : α。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.InnerRegular.map_of_continuous`：∀ {α : Type u_1} {
β : Type u_2} [inst : MeasurableSpace α] {μ : MeasureTheory.Measure α} [inst_1 :
 TopologicalSpace α]   [BorelSpace α] [ins…
· 使用定理 `ContinuousConstSMul.continuous_const_smul`：∀ {Γ : Type u_1} {T : Type u_
2} {inst : TopologicalSpace T} {inst_1 : SMul Γ T} [self : ContinuousConstSMul Γ
 T]   (γ : Γ), Continuous fun x…
-/
instance innerRegular_map_smul {α} [Monoid α] [MulAction α G] [ContinuousConstSMul α G]
    [InnerRegular μ] (a : α) : InnerRegular (Measure.map (a • · : G → G) μ) :=
  InnerRegular.map_of_continuous (continuous_const_smul a)

/-- The image of an inner regular measure under left multiplication is again inner regular. -/
@[to_additive
/-- The image of an inner regular measure under left addition is again inner regular. -/]
/-
**MeasureTheory.innerRegular_map_mul_left** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheo
ry`。
形式化陈述：innerRegular_map_mul_left [IsTopologicalGroup G] [InnerRegular μ] (g : G) 
: InnerRegular (Measure.map (g * ·) μ)
参数：g : G。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.InnerRegular.map_of_continuous`：∀ {α : Type u_1} {
β : Type u_2} [inst : MeasurableSpace α] {μ : MeasureTheory.Measure α} [inst_1 :
 TopologicalSpace α]   [BorelSpace α] [ins…
· 使用定理 `continuous_const_mul`：continuous_const_mul (m : M) : Continuous (m * ·)
· 使用定理 `instSeparatelyContinuousMulOfContinuousMul`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Mul M] [ContinuousMul M], SeparatelyContinuousMul M
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
-/
instance innerRegular_map_mul_left [IsTopologicalGroup G] [InnerRegular μ] (g : G) :
    InnerRegular (Measure.map (g * ·) μ) := InnerRegular.map_of_continuous (continuous_const_mul g)

/-- The image of an inner regular measure under right multiplication is again inner regular. -/
@[to_additive
/-- The image of an inner regular measure under right addition is again inner regular. -/]
/-
**MeasureTheory.innerRegular_map_mul_right** 是 Mathlib 中的一个实例，位于命名空间 `MeasureThe
ory`。
形式化陈述：innerRegular_map_mul_right [IsTopologicalGroup G] [InnerRegular μ] (g : G)
 : InnerRegular (Measure.map (· * g) μ)
参数：g : G。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.InnerRegular.map_of_continuous`：∀ {α : Type u_1} {
β : Type u_2} [inst : MeasurableSpace α] {μ : MeasureTheory.Measure α} [inst_1 :
 TopologicalSpace α]   [BorelSpace α] [ins…
· 使用定理 `continuous_mul_const`：continuous_mul_const (m : M) : Continuous (· * m)
· 使用定理 `instSeparatelyContinuousMulOfContinuousMul`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Mul M] [ContinuousMul M], SeparatelyContinuousMul M
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
-/
instance innerRegular_map_mul_right [IsTopologicalGroup G] [InnerRegular μ] (g : G) :
    InnerRegular (Measure.map (· * g) μ) := InnerRegular.map_of_continuous (continuous_mul_const g)

variable [IsTopologicalGroup G]

@[to_additive]
/-
**MeasureTheory.regular_inv_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：regular_inv_iff : μ.inv.Regular ↔ μ.Regular
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.Regular.map_iff`：∀ {α : Type u_1} {β : Type u_2} [
inst : MeasurableSpace α] {μ : MeasureTheory.Measure α} [inst_1 : TopologicalSpa
ce α]   [BorelSpace α] [ins…
· 使用定理 `IsTopologicalGroup.toContinuousInv`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousInv G
-/
theorem regular_inv_iff : μ.inv.Regular ↔ μ.Regular :=
  Regular.map_iff (Homeomorph.inv G)

@[to_additive]
/-
**MeasureTheory.innerRegular_inv_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：innerRegular_inv_iff : μ.inv.InnerRegular ↔ μ.InnerRegular
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.InnerRegular.map_iff`：∀ {α : Type u_1} {β : Type u
_2} [inst : MeasurableSpace α] {μ : MeasureTheory.Measure α} [inst_1 : Topologic
alSpace α]   [BorelSpace α] [ins…
· 使用定理 `IsTopologicalGroup.toContinuousInv`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousInv G
-/
theorem innerRegular_inv_iff : μ.inv.InnerRegular ↔ μ.InnerRegular :=
  InnerRegular.map_iff (Homeomorph.inv G)

/-- Continuity of the measure of translates of a compact set: Given a compact set `k` in a
topological group, for `g` close enough to the origin, `μ (g • k \ k)` is arbitrarily small. -/
@[to_additive /-- Continuity of the measure of translates of a compact set: Given a compact set `k`
in an additive topological group, for `g` close enough to the origin, `μ (g +ᵥ k \ k)` is
arbitrarily small. -/]
/-
**MeasureTheory.eventually_nhds_one_measure_smul_sdiff_lt** 是 Mathlib 中的一个引理，位于命
名空间 `MeasureTheory`。
形式化陈述：eventually_nhds_one_measure_smul_sdiff_lt [LocallyCompactSpace G] [IsFinit
eMeasureOnCompacts μ] [InnerRegularCompactLTTop μ] {k : Set G} (hk : IsCompact k
) (h'k : IsClosed k) {ε : Real>=0∞} (hε : ε != 0) : forallᶠ g in 𝓝 (1 : G), μ (g
 • k \ k) < ε
参数：hk : IsCompact k；h'k : IsClosed k；hε : ε != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.exists_isOpen_lt_add`：∀ {α : Type u_1} [inst : MeasurableSpace
 α] {μ : MeasureTheory.Measure α} [inst_1 : TopologicalSpace α]   [μ.InnerRegula
rCompactLTTop] [Meas…
· 使用定理 `MeasureTheory.isLocallyFiniteMeasure_of_isFiniteMeasureOnCompacts`：∀ {α 
: Type u_1} {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : Topol
ogicalSpace α]   [WeaklyLocallyCompactSpace α] [Measure…
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `instR1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [RegularSpace 
X], R1Space X
· 使用定理 `IsTopologicalGroup.regularSpace`：∀ (G : Type w) [inst : TopologicalSpace
 G] [inst_1 : Group G] [IsTopologicalGroup G], RegularSpace G
· 使用定理 `compact_open_separated_mul_left`：compact_open_separated_mul_left {K U : 
Set G} (hK : IsCompact K) (hU : IsOpen U) (hKU : K subseteq U) : exists V in 𝓝 (
1 : G), V * K subsete…
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `sdiff_le_sdiff`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] 
{a b c d : α}, d ≤ c → b ≤ a → d \ a ≤ c \ b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `Set.smul_set_subset_smul`：smul_set_subset_smul {s : Set α} : a in s -> a
 • t subseteq s • t
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `MeasureTheory.measure_sdiff_lt_of_lt_add`：measure_sdiff_lt_of_lt_add (hs
 : NullMeasurableSet s μ) (hst : s subseteq t) (hs' : μ s != ∞) {ε : Real>=0∞} (
h : μ t < μ s + ε) : μ (t \ s)…
· 使用定理 `IsClosed.nullMeasurableSet`：IsClosed.nullMeasurableSet {μ} (h : IsClosed
 s) : NullMeasurableSet s μ
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `IsCompact.measure_lt_top`：∀ {α : Type u_1} {m0 : MeasurableSpace α} [ins
t : TopologicalSpace α] {μ : MeasureTheory.Measure α}   [MeasureTheory.IsFiniteM
easureOnCompac…
-/
lemma eventually_nhds_one_measure_smul_sdiff_lt [LocallyCompactSpace G]
    [IsFiniteMeasureOnCompacts μ] [InnerRegularCompactLTTop μ] {k : Set G}
    (hk : IsCompact k) (h'k : IsClosed k) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∀ᶠ g in 𝓝 (1 : G), μ (g • k \ k) < ε := by
  obtain ⟨U, hUk, hU, hμUk⟩ : ∃ (U : Set G), k ⊆ U ∧ IsOpen U ∧ μ U < μ k + ε :=
    hk.exists_isOpen_lt_add hε
  obtain ⟨V, hV1, hVkU⟩ : ∃ V ∈ 𝓝 (1 : G), V * k ⊆ U := compact_open_separated_mul_left hk hU hUk
  filter_upwards [hV1] with g hg
  calc
    μ (g • k \ k) ≤ μ (U \ k) := by
      gcongr
      exact (smul_set_subset_smul hg).trans hVkU
    _ < ε := measure_sdiff_lt_of_lt_add h'k.nullMeasurableSet hUk hk.measure_lt_top.ne hμUk

@[deprecated (since := "2026-06-03")]
alias eventually_nhds_one_measure_smul_diff_lt := eventually_nhds_one_measure_smul_sdiff_lt

/-- Continuity of the measure of translates of a compact set:
Given a closed compact set `k` in a topological group,
the measure of `g • k \ k` tends to zero as `g` tends to `1`. -/
@[to_additive /-- Continuity of the measure of translates of a compact set:
Given a closed compact set `k` in an additive topological group,
the measure of `g +ᵥ k \ k` tends to zero as `g` tends to `0`. -/]
/-
**MeasureTheory.tendsto_measure_smul_sdiff_isCompact_isClosed** 是 Mathlib 中的一个引理
，位于命名空间 `MeasureTheory`。
形式化陈述：tendsto_measure_smul_sdiff_isCompact_isClosed [LocallyCompactSpace G] [IsF
initeMeasureOnCompacts μ] [InnerRegularCompactLTTop μ] {k : Set G} (hk : IsCompa
ct k) (h'k : IsClosed k) : Tendsto (fun g : G => μ (g • k \ k)) (𝓝 1) (𝓝 0)
参数：hk : IsCompact k；h'k : IsClosed k。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.HasBasis.tendsto_right_iff`：∀ {α : Type u_1} {β : Type u_2} {ι' :
 Sort u_5} {la : Filter α} {lb : Filter β} {pb : ι' → Prop} {sb : ι' → Set β}   
{f : α → β}, lb.HasBasi…
· 使用定理 `ENNReal.nhds_zero_basis`：nhds_zero_basis : (𝓝 (0 : Real>=0∞)).HasBasis (
fun a : Real>=0∞ => 0 < a) fun a => Iio a
· 使用引理 `MeasureTheory.eventually_nhds_one_measure_smul_sdiff_lt`：eventually_nhds
_one_measure_smul_sdiff_lt [LocallyCompactSpace G] [IsFiniteMeasureOnCompacts μ]
 [InnerRegularCompactLTTop μ] {k : Set G} (hk…
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
-/
lemma tendsto_measure_smul_sdiff_isCompact_isClosed [LocallyCompactSpace G]
    [IsFiniteMeasureOnCompacts μ] [InnerRegularCompactLTTop μ] {k : Set G}
    (hk : IsCompact k) (h'k : IsClosed k) :
    Tendsto (fun g : G ↦ μ (g • k \ k)) (𝓝 1) (𝓝 0) :=
  ENNReal.nhds_zero_basis.tendsto_right_iff.mpr <| fun _ h ↦
    eventually_nhds_one_measure_smul_sdiff_lt hk h'k h.ne'

@[deprecated (since := "2026-06-03")]
alias tendsto_measure_smul_diff_isCompact_isClosed := tendsto_measure_smul_sdiff_isCompact_isClosed

section IsMulLeftInvariant
variable [IsMulLeftInvariant μ]

/-- If a left-invariant measure gives positive mass to a compact set, then it gives positive mass to
any open set. -/
@[to_additive
/-- If a left-invariant measure gives positive mass to a compact set, then it gives positive mass to
any open set. -/]
/-
**MeasureTheory.isOpenPosMeasure_of_mulLeftInvariant_of_compact** 是 Mathlib 中的一个
定理，位于命名空间 `MeasureTheory`。
形式化陈述：isOpenPosMeasure_of_mulLeftInvariant_of_compact (K : Set G) (hK : IsCompac
t K) (h : μ K != 0) : IsOpenPosMeasure μ
参数：K : Set G；hK : IsCompact K；h : μ K != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nonpos_iff_eq_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [in
st_1 : Zero α] [IsBotZeroClass α], a ≤ 0 ↔ a = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `compact_covered_by_mul_left_translates`：compact_covered_by_mul_left_tran
slates {K V : Set G} (hK : IsCompact K) (hV : (interior V).Nonempty) : exists t 
: Finset G, K subseteq ⋃ g i…
· 使用定理 `IsOpen.interior_eq`：IsOpen.interior_eq (h : IsOpen s) : interior s = s
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.measure_biUnion_finset_le`：measure_biUnion_finset_le (I : 
Finset ι) (s : ι -> Set α) : μ (⋃ i in I, s i) <= ∑ i in I, μ (s i)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `MeasureTheory.measure_preimage_mul`：measure_preimage_mul (μ : Measure G)
 [IsMulLeftInvariant μ] (g : G) (A : Set G) : μ ((fun h => g * h) ⁻¹' A) = μ A
· 使用定理 `ContinuousMul.measurableMul`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Mul γ]   [SeparatelyCont
inuousMul γ], Mea…
· 使用定理 `instSeparatelyContinuousMulOfContinuousMul`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Mul M] [ContinuousMul M], SeparatelyContinuousMul M
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem isOpenPosMeasure_of_mulLeftInvariant_of_compact (K : Set G) (hK : IsCompact K)
    (h : μ K ≠ 0) : IsOpenPosMeasure μ := by
  refine ⟨fun U hU hne => ?_⟩
  contrapose h
  rw [← nonpos_iff_eq_zero]
  rw [← hU.interior_eq] at hne
  obtain ⟨t, hKt⟩ : ∃ t : Finset G, K ⊆ ⋃ (g : G) (_ : g ∈ t), (fun h : G => g * h) ⁻¹' U :=
    compact_covered_by_mul_left_translates hK hne
  calc
    μ K ≤ μ (⋃ (g : G) (_ : g ∈ t), (fun h : G => g * h) ⁻¹' U) := measure_mono hKt
    _ ≤ ∑ g ∈ t, μ ((fun h : G => g * h) ⁻¹' U) := measure_biUnion_finset_le _ _
    _ = 0 := by simp [measure_preimage_mul, h]

/-- A nonzero left-invariant regular measure gives positive mass to any open set. -/
@[to_additive /-- A nonzero left-invariant regular measure gives positive mass to any open set. -/]
/-
**MeasureTheory.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A nonzero left-invariant regular measure gives positive mass to any open set.
-/
instance (priority := 80) isOpenPosMeasure_of_mulLeftInvariant_of_regular [Regular μ] [NeZero μ] :
    IsOpenPosMeasure μ :=
  let ⟨K, hK, h2K⟩ := Regular.exists_isCompact_not_null.mpr (NeZero.ne μ)
  isOpenPosMeasure_of_mulLeftInvariant_of_compact K hK h2K

/-- A nonzero left-invariant inner regular measure gives positive mass to any open set. -/
@[to_additive
/-- A nonzero left-invariant inner regular measure gives positive mass to any open set. -/]
/-
**MeasureTheory.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 80) isOpenPosMeasure_of_mulLeftInvariant_of_innerRegular
    [InnerRegular μ] [NeZero μ] :
    IsOpenPosMeasure μ :=
  let ⟨K, hK, h2K⟩ := InnerRegular.exists_isCompact_not_null.mpr (NeZero.ne μ)
  isOpenPosMeasure_of_mulLeftInvariant_of_compact K hK h2K

@[to_additive]
/-
**MeasureTheory.null_iff_of_isMulLeftInvariant** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory`。
形式化陈述：null_iff_of_isMulLeftInvariant [Regular μ] {s : Set G} (hs : IsOpen s) : μ
 s = 0 ↔ s = ∅ ∨ μ = 0
参数：hs : IsOpen s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_zero_or_neZero`：eq_zero_or_neZero (a : R) : a = 0 ∨ NeZero a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsOpen.measure_eq_zero_iff`：∀ {X : Type u_1} [inst : TopologicalSpace X]
 {m : MeasurableSpace X} (μ : MeasureTheory.Measure X) [μ.IsOpenPosMeasure]   {U
 : Set X}, IsOpe…
· 使用定理 `MeasureTheory.isOpenPosMeasure_of_mulLeftInvariant_of_regular`：∀ {G : Ty
pe u_1} [inst : MeasurableSpace G] [inst_1 : TopologicalSpace G] [BorelSpace G] 
{μ : MeasureTheory.Measure G}   [inst_3 : Group G] …
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
-/
theorem null_iff_of_isMulLeftInvariant [Regular μ] {s : Set G} (hs : IsOpen s) :
    μ s = 0 ↔ s = ∅ ∨ μ = 0 := by
  rcases eq_zero_or_neZero μ with rfl | hμ
  · simp
  · simp only [or_false, hs.measure_eq_zero_iff μ, NeZero.ne μ]

@[to_additive]
/-
**MeasureTheory.measure_ne_zero_iff_nonempty_of_isMulLeftInvariant** 是 Mathlib 中
的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：measure_ne_zero_iff_nonempty_of_isMulLeftInvariant [Regular μ] (hμ : μ != 
0) {s : Set G} (hs : IsOpen s) : μ s != 0 ↔ s.Nonempty
参数：hμ : μ != 0；hs : IsOpen s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.null_iff_of_isMulLeftInvariant`：null_iff_of_isMulLeftInvar
iant [Regular μ] {s : Set G} (hs : IsOpen s) : μ s = 0 ↔ s = ∅ ∨ μ = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Set.nonempty_iff_ne_empty`：nonempty_iff_ne_empty : s.Nonempty ↔ s != ∅
-/
theorem measure_ne_zero_iff_nonempty_of_isMulLeftInvariant [Regular μ] (hμ : μ ≠ 0) {s : Set G}
    (hs : IsOpen s) : μ s ≠ 0 ↔ s.Nonempty := by
  simpa [null_iff_of_isMulLeftInvariant (μ := μ) hs, hμ] using nonempty_iff_ne_empty.symm

@[to_additive]
/-
**MeasureTheory.measure_pos_iff_nonempty_of_isMulLeftInvariant** 是 Mathlib 中的一个定
理，位于命名空间 `MeasureTheory`。
形式化陈述：measure_pos_iff_nonempty_of_isMulLeftInvariant [Regular μ] (h3μ : μ != 0) 
{s : Set G} (hs : IsOpen s) : 0 < μ s ↔ s.Nonempty
参数：h3μ : μ != 0；hs : IsOpen s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `MeasureTheory.measure_ne_zero_iff_nonempty_of_isMulLeftInvariant`：measur
e_ne_zero_iff_nonempty_of_isMulLeftInvariant [Regular μ] (hμ : μ != 0) {s : Set 
G} (hs : IsOpen s) : μ s != 0 ↔ s.Nonempty
-/
theorem measure_pos_iff_nonempty_of_isMulLeftInvariant [Regular μ] (h3μ : μ ≠ 0) {s : Set G}
    (hs : IsOpen s) : 0 < μ s ↔ s.Nonempty :=
  pos_iff_ne_zero.trans <| measure_ne_zero_iff_nonempty_of_isMulLeftInvariant h3μ hs

/-- If a left-invariant measure gives finite mass to a nonempty open set, then it gives finite mass
to any compact set. -/
@[to_additive
/-- If a left-invariant measure gives finite mass to a nonempty open set, then it gives finite mass
to any compact set. -/]
/-
**MeasureTheory.measure_lt_top_of_isCompact_of_isMulLeftInvariant** 是 Mathlib 中的
一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：measure_lt_top_of_isCompact_of_isMulLeftInvariant (U : Set G) (hU : IsOpen
 U) (h'U : U.Nonempty) (h : μ U != ∞) {K : Set G} (hK : IsCompact K) : μ K < ∞
参数：U : Set G；hU : IsOpen U；h'U : U.Nonempty；h : μ U != ∞；hK : IsCompact K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `compact_covered_by_mul_left_translates`：compact_covered_by_mul_left_tran
slates {K V : Set G} (hK : IsCompact K) (hV : (interior V).Nonempty) : exists t 
: Finset G, K subseteq ⋃ g i…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsOpen.interior_eq`：IsOpen.interior_eq (h : IsOpen s) : interior s = s
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.measure_biUnion_lt_top`：measure_biUnion_lt_top {s : Set β}
 {f : β -> Set α} (hs : s.Finite) (hfin : forall i in s, μ (f i) < ∞) : μ (⋃ i i
n s, f i) < ∞
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.measure_preimage_mul`：measure_preimage_mul (μ : Measure G)
 [IsMulLeftInvariant μ] (g : G) (A : Set G) : μ ((fun h => g * h) ⁻¹' A) = μ A
· 使用定理 `ContinuousMul.measurableMul`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Mul γ]   [SeparatelyCont
inuousMul γ], Mea…
· 使用定理 `instSeparatelyContinuousMulOfContinuousMul`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Mul M] [ContinuousMul M], SeparatelyContinuousMul M
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem measure_lt_top_of_isCompact_of_isMulLeftInvariant (U : Set G) (hU : IsOpen U)
    (h'U : U.Nonempty) (h : μ U ≠ ∞) {K : Set G} (hK : IsCompact K) : μ K < ∞ := by
  rw [← hU.interior_eq] at h'U
  obtain ⟨t, hKt⟩ : ∃ t : Finset G, K ⊆ ⋃ g ∈ t, (fun h : G => g * h) ⁻¹' U :=
    compact_covered_by_mul_left_translates hK h'U
  exact (measure_mono hKt).trans_lt <| measure_biUnion_lt_top t.finite_toSet <| by simp [h.lt_top]

/-- If a left-invariant measure gives finite mass to a set with nonempty interior, then
it gives finite mass to any compact set. -/
@[to_additive
/-- If a left-invariant measure gives finite mass to a set with nonempty interior, then it gives
finite mass to any compact set. -/]
/-
**MeasureTheory.measure_lt_top_of_isCompact_of_isMulLeftInvariant'** 是 Mathlib 中
的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：measure_lt_top_of_isCompact_of_isMulLeftInvariant' {U : Set G} (hU : (inte
rior U).Nonempty) (h : μ U != ∞) {K : Set G} (hK : IsCompact K) : μ K < ∞
参数：hU : (interior U).Nonempty；h : μ U != ∞；hK : IsCompact K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.measure_lt_top_of_isCompact_of_isMulLeftInvariant`：measure
_lt_top_of_isCompact_of_isMulLeftInvariant (U : Set G) (hU : IsOpen U) (h'U : U.
Nonempty) (h : μ U != ∞) {K : Set G} (hK : IsCompact …
· 使用定理 `isOpen_interior`：isOpen_interior : IsOpen (interior s)
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `lt_top_iff_ne_top`：lt_top_iff_ne_top : a < ⊤ ↔ a != ⊤
-/
theorem measure_lt_top_of_isCompact_of_isMulLeftInvariant' {U : Set G}
    (hU : (interior U).Nonempty) (h : μ U ≠ ∞) {K : Set G} (hK : IsCompact K) : μ K < ∞ :=
  measure_lt_top_of_isCompact_of_isMulLeftInvariant (interior U) isOpen_interior hU
    ((measure_mono interior_subset).trans_lt (lt_top_iff_ne_top.2 h)).ne hK

/-- In a noncompact locally compact group, a left-invariant measure which is positive
on open sets has infinite mass. -/
@[to_additive (attr := simp)
/-- In a noncompact locally compact additive group, a left-invariant measure which is positive on
open sets has infinite mass. -/]
/-
**MeasureTheory.measure_univ_of_isMulLeftInvariant** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory`。
形式化陈述：measure_univ_of_isMulLeftInvariant [WeaklyLocallyCompactSpace G] [Noncompa
ctSpace G] (μ : Measure G) [IsOpenPosMeasure μ] [μ.IsMulLeftInvariant] : μ univ 
= ∞
参数：μ : Measure G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_mem_nhds_isCompact_isClosed`：exists_mem_nhds_isCompact_isClosed (
x : X) : exists K in 𝓝 x, IsCompact K ∧ IsClosed K
· 使用定理 `instR1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [RegularSpace 
X], R1Space X
· 使用定理 `IsTopologicalGroup.regularSpace`：∀ (G : Type w) [inst : TopologicalSpace
 G] [inst_1 : Group G] [IsTopologicalGroup G], RegularSpace G
· 使用定理 `MeasureTheory.Measure.measure_pos_of_mem_nhds`：measure_pos_of_mem_nhds (
h : s in 𝓝 x) : 0 < μ s
· 使用定理 `exists_disjoint_smul_of_isCompact`：exists_disjoint_smul_of_isCompact [No
ncompactSpace G] {K L : Set G} (hK : IsCompact K) (hL : IsCompact L) : exists g 
: G, Disjoint K (g • L)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Function.iterate_succ'`：iterate_succ' (n : Nat) : f^[n.succ] = f ∘ f^[n]
· 使用定理 `IsCompact.union`：IsCompact.union (hs : IsCompact s) (ht : IsCompact t) :
 IsCompact (s union t)
· 使用定理 `IsCompact.smul`：IsCompact.smul {α β} [SMul α β] [TopologicalSpace β] [Co
ntinuousConstSMul α β] (a : α) {s : Set β} (hs : IsCompact s) : IsCompact (a • s
)
· 使用定理 `instSeparatelyContinuousMulOfContinuousMul`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Mul M] [ContinuousMul M], SeparatelyContinuousMul M
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `IsClosed.union`：IsClosed.union : IsClosed s₁ -> IsClosed s₂ -> IsClosed 
(s₁ union s₂)
· 使用定理 `IsClosed.smul`：IsClosed.smul {s : Set α} (hs : IsClosed s) (c : G) : IsC
losed (c • s)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.zero_add`：∀ (n : ℕ), 0 + n = n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.measure_union'`：measure_union' (hd : Disjoint s₁ s₂) (h : 
MeasurableSet s₁) : μ (s₁ union s₂) = μ s₁ + μ s₂
· 使用定理 `IsClosed.measurableSet`：IsClosed.measurableSet (h : IsClosed s) : Measur
ableSet s
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `MeasureTheory.measure_smul`：measure_smul (c : G) (s : Set α) : μ (c • s)
 = μ s
· 使用定理 `MeasureTheory.Measure.IsMulLeftInvariant.smulInvariantMeasure`：∀ {G : Ty
pe u_1} [inst : MeasurableSpace G] {μ : MeasureTheory.Measure G} [inst_1 : Mul G
] [μ.IsMulLeftInvariant],   MeasureTheory.SMulInvar…
（共 57 条，此处仅展示前 30 条）
-/
theorem measure_univ_of_isMulLeftInvariant [WeaklyLocallyCompactSpace G] [NoncompactSpace G]
    (μ : Measure G) [IsOpenPosMeasure μ] [μ.IsMulLeftInvariant] : μ univ = ∞ := by
  /- Consider a closed compact set `K` with nonempty interior. For any compact set `L`, one may
    find `g = g (L)` such that `L` is disjoint from `g • K`. Iterating this, one finds
    infinitely many translates of `K` which are disjoint from each other. As they all have the
    same positive mass, it follows that the space has infinite measure. -/
  obtain ⟨K, K1, hK, Kclosed⟩ : ∃ K ∈ 𝓝 (1 : G), IsCompact K ∧ IsClosed K :=
    exists_mem_nhds_isCompact_isClosed 1
  have K_pos : 0 < μ K := measure_pos_of_mem_nhds μ K1
  have A : ∀ L : Set G, IsCompact L → ∃ g : G, Disjoint L (g • K) := fun L hL =>
    exists_disjoint_smul_of_isCompact hL hK
  choose! g hg using A
  set L : ℕ → Set G := fun n => (fun T => T ∪ g T • K)^[n] K
  have Lcompact : ∀ n, IsCompact (L n) := fun n ↦ by
    induction n with
    | zero => exact hK
    | succ n IH =>
      simp_rw [L, iterate_succ']
      apply IsCompact.union IH (hK.smul (g (L n)))
  have Lclosed : ∀ n, IsClosed (L n) := fun n ↦ by
    induction n with
    | zero => exact Kclosed
    | succ n IH =>
      simp_rw [L, iterate_succ']
      apply IsClosed.union IH (Kclosed.smul (g (L n)))
  have M : ∀ n, μ (L n) = (n + 1 : ℕ) * μ K := fun n ↦ by
    induction n with
    | zero => simp only [L, one_mul, Nat.cast_one, iterate_zero, id, Nat.zero_add]
    | succ n IH =>
      calc
        μ (L (n + 1)) = μ (L n) + μ (g (L n) • K) := by
          simp_rw [L, iterate_succ']
          exact measure_union' (hg _ (Lcompact _)) (Lclosed _).measurableSet
        _ = (n + 1 + 1 : ℕ) * μ K := by
          simp only [IH, measure_smul, add_mul, Nat.cast_add, Nat.cast_one, one_mul]
  have N : Tendsto (fun n => μ (L n)) atTop (𝓝 (∞ * μ K)) := by
    simp_rw [M]
    apply ENNReal.Tendsto.mul_const _ (Or.inl ENNReal.top_ne_zero)
    exact ENNReal.tendsto_nat_nhds_top.comp (tendsto_add_atTop_nat _)
  simp only [ENNReal.top_mul', K_pos.ne', if_false] at N
  apply top_le_iff.1
  exact le_of_tendsto' N fun n => measure_mono (subset_univ _)

@[to_additive]
/-
**MeasureTheory._root_.MeasurableSet.mul_closure_one_eq** 是 Mathlib 中的一个引理，位于命名空
间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.MeasurableSet.mul_closure_one_eq {s : Set G} (hs : MeasurableSet s) :
    s * (closure {1} : Set G) = s := by
  induction s, hs using MeasurableSet.induction_on_open with
  | isOpen U hU => exact hU.mul_closure_one_eq
  | compl t _ iht => exact compl_mul_closure_one_eq_iff.2 iht
  | iUnion f _ _ ihf => simp_rw [iUnion_mul f, ihf]

@[to_additive (attr := simp)]
/-
**MeasureTheory.measure_mul_closure_one** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory
`。
形式化陈述：measure_mul_closure_one (s : Set G) (μ : Measure G) : μ (s * (closure {1} 
: Set G)) = μ s
参数：s : Set G；μ : Measure G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.measure_eq_iInf`：measure_eq_iInf (s : Set α) : μ s = ⨅ (t)
 (_ : s subseteq t) (_ : MeasurableSet t), μ t
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasurableSet.mul_closure_one_eq`：∀ {G : Type u_1} [inst : MeasurableSpa
ce G] [inst_1 : TopologicalSpace G] [BorelSpace G] [inst_3 : Group G]   [IsTopol
ogicalGroup G] {s : Se…
· 使用引理 `Set.smul_subset_smul_right`：smul_subset_smul_right : s₁ subseteq s₂ -> s
₁ • t subseteq s₂ • t
· 使用引理 `subset_mul_closure_one`：subset_mul_closure_one {G} [MulOneClass G] [Topo
logicalSpace G] (s : Set G) : s subseteq s * (closure {1} : Set G)
-/
lemma measure_mul_closure_one (s : Set G) (μ : Measure G) :
    μ (s * (closure {1} : Set G)) = μ s := by
  apply le_antisymm ?_ (measure_mono (subset_mul_closure_one s))
  conv_rhs => rw [measure_eq_iInf]
  simp only [le_iInf_iff]
  intro t kt t_meas
  apply measure_mono
  rw [← t_meas.mul_closure_one_eq]
  exact smul_subset_smul_right kt

end IsMulLeftInvariant

@[to_additive]
/-
**MeasureTheory.innerRegularWRT_isCompact_isClosed_measure_ne_top_of_group** 是 M
athlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：innerRegularWRT_isCompact_isClosed_measure_ne_top_of_group [h : InnerRegul
arCompactLTTop μ] : InnerRegularWRT μ (fun s => IsCompact s ∧ IsClosed s) (fun s
 => MeasurableSet s ∧ μ s != ∞)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.InnerRegularCompactLTTop.innerRegular`：∀ {α : Type
 u_1} {inst : MeasurableSpace α} {inst_1 : TopologicalSpace α} {μ : MeasureTheor
y.Measure α}   [self : μ.InnerRegularCompactLTTop…
· 使用定理 `IsCompact.closure_subset_measurableSet`：IsCompact.closure_subset_measura
bleSet [R1Space γ] {K s : Set γ} (hK : IsCompact K) (hs : MeasurableSet s) (hKs 
: K subseteq s) : closure K …
· 使用定理 `instR1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [RegularSpace 
X], R1Space X
· 使用定理 `IsTopologicalGroup.regularSpace`：∀ (G : Type w) [inst : TopologicalSpace
 G] [inst_1 : Group G] [IsTopologicalGroup G], RegularSpace G
· 使用定理 `IsCompact.closure`：∀ {X : Type u_1} [inst : TopologicalSpace X] [R1Space
 X] {K : Set X}, IsCompact K → IsCompact (closure K)
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsCompact.measure_closure`：IsCompact.measure_closure [R1Space γ] {K : Se
t γ} (hK : IsCompact K) (μ : Measure γ) : μ (closure K) = μ K
-/
lemma innerRegularWRT_isCompact_isClosed_measure_ne_top_of_group [h : InnerRegularCompactLTTop μ] :
    InnerRegularWRT μ (fun s ↦ IsCompact s ∧ IsClosed s) (fun s ↦ MeasurableSet s ∧ μ s ≠ ∞) := by
  intro s ⟨s_meas, μs⟩ r hr
  rcases h.innerRegular ⟨s_meas, μs⟩ r hr with ⟨K, Ks, K_comp, hK⟩
  refine ⟨closure K, ?_, ⟨K_comp.closure, isClosed_closure⟩, ?_⟩
  · exact IsCompact.closure_subset_measurableSet K_comp s_meas Ks
  · rwa [K_comp.measure_closure]

end IsTopologicalGroup

section CommSemigroup

variable [CommSemigroup G]

/-- In an abelian group every left invariant measure is also right-invariant.
  We don't declare the converse as an instance, since that would loop type-class inference, and
  we use `IsMulLeftInvariant` as the default hypothesis in abelian groups. -/
@[to_additive IsAddLeftInvariant.isAddRightInvariant
/-- In an abelian additive group every left invariant measure is also right-invariant. We don't
declare the converse as an instance, since that would loop type-class inference, and we use
`IsAddLeftInvariant` as the default hypothesis in abelian groups. -/]
/-
**MeasureTheory.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) IsMulLeftInvariant.isMulRightInvariant {μ : Measure G}
    [IsMulLeftInvariant μ] : IsMulRightInvariant μ :=
  ⟨fun g => by simp_rw [mul_comm, map_mul_left_eq_self]⟩

end CommSemigroup

section Haar

namespace Measure

/-- A measure on an additive group is an additive Haar measure if it is left-invariant, and
gives finite mass to compact sets and positive mass to open sets.

Textbooks generally require an additional regularity assumption to ensure nice behavior on
arbitrary locally compact groups. Use `[IsAddHaarMeasure μ] [Regular μ]` or
`[IsAddHaarMeasure μ] [InnerRegular μ]` in these situations. Note that a Haar measure in our
sense is automatically regular and inner regular on second countable locally compact groups, as
checked just below this definition. -/
/-
**MeasureTheory.Measure.IsAddHaarMeasure** 是 Mathlib 中的一个归纳类型，位于命名空间 `MeasureThe
ory.Measure`。
形式化陈述：{G : Type u_3} → [AddGroup G] → [TopologicalSpace G] → [inst : MeasurableS
pace G] → MeasureTheory.Measure G → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A measure on an additive group is an additive Haar measure if it is left-invaria
nt, and
gives finite mass to compact sets and positive mass to open sets.

Textbooks generally require an additional regularity assumption to ensure nice b
ehavior on
arbitrary locally compact groups. Use `[IsAddHaarMeasure μ] [Regular μ]` or
`[IsAddHaarMeasure μ] [InnerRegular μ]` in these situations. Note that a Haar me
asure in our
sense is automatically regular and inner regular on second countable locally com
pact groups, as
checked just below this definition.
-/
class IsAddHaarMeasure {G : Type*} [AddGroup G] [TopologicalSpace G] [MeasurableSpace G]
    (μ : Measure G) : Prop
    extends IsFiniteMeasureOnCompacts μ, IsAddLeftInvariant μ, IsOpenPosMeasure μ

/-- A measure on a group is a Haar measure if it is left-invariant, and gives finite mass to
compact sets and positive mass to open sets.

Textbooks generally require an additional regularity assumption to ensure nice behavior on
arbitrary locally compact groups. Use `[IsHaarMeasure μ] [Regular μ]` or
`[IsHaarMeasure μ] [InnerRegular μ]` in these situations. Note that a Haar measure in our
sense is automatically regular and inner regular on second countable locally compact groups, as
checked just below this definition. -/
@[to_additive existing]
/-
**MeasureTheory.Measure.IsHaarMeasure** 是 Mathlib 中的一个归纳类型，位于命名空间 `MeasureTheory
.Measure`。
形式化陈述：{G : Type u_3} → [Group G] → [TopologicalSpace G] → [inst : MeasurableSpac
e G] → MeasureTheory.Measure G → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A measure on a group is a Haar measure if it is left-invariant, and gives finite
 mass to
compact sets and positive mass to open sets.

Textbooks generally require an additional regularity assumption to ensure nice b
ehavior on
arbitrary locally compact groups. Use `[IsHaarMeasure μ] [Regular μ]` or
`[IsHaarMeasure μ] [InnerRegular μ]` in these situations. Note that a Haar measu
re in our
sense is automatically regular and inner regular on second countable locally com
pact groups, as
checked just below this definition.
-/
class IsHaarMeasure {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G]
    (μ : Measure G) : Prop
    extends IsFiniteMeasureOnCompacts μ, IsMulLeftInvariant μ, IsOpenPosMeasure μ

variable [Group G] [TopologicalSpace G] (μ : Measure G) [IsHaarMeasure μ]

@[to_additive (attr := simp)]
/-
**MeasureTheory.Measure.haar_singleton** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
Measure`。
形式化陈述：haar_singleton [ContinuousMul G] [BorelSpace G] (g : G) : μ {g} = μ {(1 : 
G)}
参数：g : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.preimage_mul_left_singleton`：preimage_mul_left_singleton : (a * ·) ⁻
¹' {b} = {a⁻¹ * b}
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.measure_preimage_mul`：measure_preimage_mul (μ : Measure G)
 [IsMulLeftInvariant μ] (g : G) (A : Set G) : μ ((fun h => g * h) ⁻¹' A) = μ A
· 使用定理 `ContinuousMul.measurableMul`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Mul γ]   [SeparatelyCont
inuousMul γ], Mea…
· 使用定理 `instSeparatelyContinuousMulOfContinuousMul`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Mul M] [ContinuousMul M], SeparatelyContinuousMul M
· 使用定理 `MeasureTheory.Measure.IsHaarMeasure.toIsMulLeftInvariant`：∀ {G : Type u_
3} {inst : Group G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpace G}  
 {μ : MeasureTheory.Measure G} [self : μ.IsHaa…
-/
theorem haar_singleton [ContinuousMul G] [BorelSpace G] (g : G) : μ {g} = μ {(1 : G)} := by
  convert! measure_preimage_mul μ g⁻¹ _
  simp only [mul_one, preimage_mul_left_singleton, inv_inv]

@[to_additive IsAddHaarMeasure.smul]
/-
**MeasureTheory.Measure.IsHaarMeasure.smul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.Measure.IsHaarMeasure`。
形式化陈述：∀ {G : Type u_1} [inst : MeasurableSpace G] [inst_1 : Group G] [inst_2 : T
opologicalSpace G]   (μ : MeasureTheory.Measure G) [μ.IsHaarMeasure] {c : ENNRea
l}, c ≠ 0 → c ≠ ⊤ → (c • μ).IsHaarMeasure
参数：μ : MeasureTheory.Measure G；c • μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MeasureTheory.Measure.isOpenPosMeasure_smul`：isOpenPosMeasure_smul {c : 
Real>=0∞} (h : c != 0) : IsOpenPosMeasure (c • μ)
· 使用定理 `MeasureTheory.Measure.IsHaarMeasure.toIsOpenPosMeasure`：∀ {G : Type u_3}
 {inst : Group G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpace G}   {
μ : MeasureTheory.Measure G} [self : μ.IsHaa…
· 使用定理 `ENNReal.mul_lt_top`：mul_lt_top : a < ∞ -> b < ∞ -> a * b < ∞
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
· 使用定理 `IsCompact.measure_lt_top`：∀ {α : Type u_1} {m0 : MeasurableSpace α} [ins
t : TopologicalSpace α] {μ : MeasureTheory.Measure α}   [MeasureTheory.IsFiniteM
easureOnCompac…
· 使用定理 `MeasureTheory.Measure.IsHaarMeasure.toIsFiniteMeasureOnCompacts`：∀ {G : 
Type u_3} {inst : Group G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpa
ce G}   {μ : MeasureTheory.Measure G} [self : μ.IsHaa…
· 使用定理 `MeasureTheory.Measure.IsHaarMeasure.toIsMulLeftInvariant`：∀ {G : Type u_
3} {inst : Group G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpace G}  
 {μ : MeasureTheory.Measure G} [self : μ.IsHaa…
-/
theorem IsHaarMeasure.smul {c : ℝ≥0∞} (cpos : c ≠ 0) (ctop : c ≠ ∞) : IsHaarMeasure (c • μ) :=
  { lt_top_of_isCompact := fun _K hK => ENNReal.mul_lt_top ctop.lt_top hK.measure_lt_top
    toIsOpenPosMeasure := isOpenPosMeasure_smul μ cpos }

@[to_additive IsAddHaarMeasure.nnreal_smul]
/-
**MeasureTheory.Measure.IsHaarMeasure.nnreal_smul** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory.Measure.IsHaarMeasure`。
形式化陈述：∀ {G : Type u_1} [inst : MeasurableSpace G] [inst_1 : Group G] [inst_2 : T
opologicalSpace G]   (μ : MeasureTheory.Measure G) [μ.IsHaarMeasure] {c : NNReal
}, c ≠ 0 → (c • μ).IsHaarMeasure
参数：μ : MeasureTheory.Measure G；c • μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.IsHaarMeasure.smul`：∀ {G : Type u_1} [inst : Measu
rableSpace G] [inst_1 : Group G] [inst_2 : TopologicalSpace G]   (μ : MeasureThe
ory.Measure G) [μ.IsHaarMeasur…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Option.some_ne_none`：∀ {α : Type u_1} (x : α), some x ≠ none
-/
lemma IsHaarMeasure.nnreal_smul {c : ℝ≥0} (hc : c ≠ 0) : IsHaarMeasure (c • μ) :=
  .smul _ (by simp [hc]) (Option.some_ne_none _)

/-- If a left-invariant measure gives positive mass to some compact set with nonempty interior, then
it is a Haar measure. -/
@[to_additive
/-- If a left-invariant measure gives positive mass to some compact set with nonempty interior, then
it is an additive Haar measure. -/]
/-
**MeasureTheory.Measure.isHaarMeasure_of_isCompact_nonempty_interior** 是 Mathlib
 中的一个定理，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：isHaarMeasure_of_isCompact_nonempty_interior [IsTopologicalGroup G] [Borel
Space G] (μ : Measure G) [IsMulLeftInvariant μ] (K : Set G) (hK : IsCompact K) (
h'K : (interior K).Nonempty) (h : μ K != 0) (h' : μ K != ∞) : IsHaarMeasure μ
参数：μ : Measure G；K : Set G；hK : IsCompact K；h'K : (interior K).Nonempty；h : μ K 
!= 0；h' : μ K != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.isOpenPosMeasure_of_mulLeftInvariant_of_compact`：isOpenPos
Measure_of_mulLeftInvariant_of_compact (K : Set G) (hK : IsCompact K) (h : μ K !
= 0) : IsOpenPosMeasure μ
· 使用定理 `MeasureTheory.measure_lt_top_of_isCompact_of_isMulLeftInvariant'`：measur
e_lt_top_of_isCompact_of_isMulLeftInvariant' {U : Set G} (hU : (interior U).None
mpty) (h : μ U != ∞) {K : Set G} (hK : IsCompact K) : …
-/
theorem isHaarMeasure_of_isCompact_nonempty_interior [IsTopologicalGroup G] [BorelSpace G]
    (μ : Measure G) [IsMulLeftInvariant μ] (K : Set G) (hK : IsCompact K)
    (h'K : (interior K).Nonempty) (h : μ K ≠ 0) (h' : μ K ≠ ∞) : IsHaarMeasure μ :=
  { lt_top_of_isCompact := fun _L hL =>
      measure_lt_top_of_isCompact_of_isMulLeftInvariant' h'K h' hL
    toIsOpenPosMeasure := isOpenPosMeasure_of_mulLeftInvariant_of_compact K hK h }

/-- The image of a Haar measure under a continuous surjective proper group homomorphism is again
a Haar measure. See also `MulEquiv.isHaarMeasure_map` and `ContinuousMulEquiv.isHaarMeasure_map`. -/
@[to_additive
/-- The image of an additive Haar measure under a continuous surjective proper additive group
homomorphism is again an additive Haar measure. See also `AddEquiv.isAddHaarMeasure_map`,
`ContinuousAddEquiv.isAddHaarMeasure_map` and `ContinuousLinearEquiv.isAddHaarMeasure_map`. -/]
/-
**MeasureTheory.Measure.isHaarMeasure_map** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.Measure`。
形式化陈述：isHaarMeasure_map [BorelSpace G] [ContinuousMul G] {H : Type*} [Group H] [
TopologicalSpace H] [MeasurableSpace H] [BorelSpace H] [IsTopologicalGroup H] (f
 : G ->* H) (hf : Continuous f) (h_surj : Surjective f) (h_prop : Tendsto f (coc
ompact G) (cocompact H)) : IsHaarMeasure (Measure.map f μ)
参数：f : G ->* H；hf : Continuous f；h_surj : Surjective f；h_prop : Tendsto f (cocom
pact G) (cocompact H)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.isMulLeftInvariant_map`：isMulLeftInvariant_map {H : Type*}
 [MeasurableSpace H] [Mul H] [MeasurableMul H] [IsMulLeftInvariant μ] (f : G ->ₙ
* H) (hf : Measurable f) (…
· 使用定理 `ContinuousMul.measurableMul`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Mul γ]   [SeparatelyCont
inuousMul γ], Mea…
· 使用定理 `instSeparatelyContinuousMulOfContinuousMul`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Mul M] [ContinuousMul M], SeparatelyContinuousMul M
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `MeasureTheory.Measure.IsHaarMeasure.toIsMulLeftInvariant`：∀ {G : Type u_
3} {inst : Group G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpace G}  
 {μ : MeasureTheory.Measure G} [self : μ.IsHaa…
· 使用定理 `Continuous.measurable`：Continuous.measurable {f : α -> γ} (hf : Continuo
us f) : Measurable f
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `Continuous.isOpenPosMeasure_map`：∀ {X : Type u_1} [inst : TopologicalSpa
ce X] {m : MeasurableSpace X} {μ : MeasureTheory.Measure X} [μ.IsOpenPosMeasure]
   [OpensMeasurableSp…
· 使用定理 `MeasureTheory.Measure.IsHaarMeasure.toIsOpenPosMeasure`：∀ {G : Type u_3}
 {inst : Group G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpace G}   {
μ : MeasureTheory.Measure G} [self : μ.IsHaa…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsCompact.measure_closure`：IsCompact.measure_closure [R1Space γ] {K : Se
t γ} (hK : IsCompact K) (μ : Measure γ) : μ (closure K) = μ K
· 使用定理 `instR1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [RegularSpace 
X], R1Space X
· 使用定理 `IsTopologicalGroup.regularSpace`：∀ (G : Type w) [inst : TopologicalSpace
 G] [inst_1 : Group G] [IsTopologicalGroup G], RegularSpace G
· 使用定理 `MeasureTheory.Measure.map_apply`：map_apply (hf : Measurable f) {s : Set 
β} (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)
· 使用定理 `IsClosed.measurableSet`：IsClosed.measurableSet (h : IsClosed s) : Measur
ableSet s
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
· 使用定理 `IsCompact.measure_lt_top`：∀ {α : Type u_1} {m0 : MeasurableSpace α} [ins
t : TopologicalSpace α] {μ : MeasureTheory.Measure α}   [MeasureTheory.IsFiniteM
easureOnCompac…
· 使用定理 `MeasureTheory.Measure.IsHaarMeasure.toIsFiniteMeasureOnCompacts`：∀ {G : 
Type u_3} {inst : Group G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpa
ce G}   {μ : MeasureTheory.Measure G} [self : μ.IsHaa…
· 使用定理 `CocompactMap.isCompact_preimage_of_isClosed`：isCompact_preimage_of_isClo
sed (f : CocompactMap α β) ⦃s : Set β⦄ (hs : IsCompact s) (h's : IsClosed s) : I
sCompact (f ⁻¹' s)
· 使用定理 `IsCompact.closure`：∀ {X : Type u_1} [inst : TopologicalSpace X] [R1Space
 X] {K : Set X}, IsCompact K → IsCompact (closure K)
-/
theorem isHaarMeasure_map [BorelSpace G] [ContinuousMul G] {H : Type*} [Group H]
    [TopologicalSpace H] [MeasurableSpace H] [BorelSpace H] [IsTopologicalGroup H]
    (f : G →* H) (hf : Continuous f) (h_surj : Surjective f)
    (h_prop : Tendsto f (cocompact G) (cocompact H)) : IsHaarMeasure (Measure.map f μ) :=
  { toIsMulLeftInvariant := isMulLeftInvariant_map f.toMulHom hf.measurable h_surj
    lt_top_of_isCompact := by
      intro K hK
      rw [← hK.measure_closure, map_apply hf.measurable isClosed_closure.measurableSet]
      set g : CocompactMap G H := ⟨⟨f, hf⟩, h_prop⟩
      exact IsCompact.measure_lt_top (g.isCompact_preimage_of_isClosed hK.closure isClosed_closure)
    toIsOpenPosMeasure := hf.isOpenPosMeasure_map h_surj }

@[to_additive]
/-
**MeasureTheory.Measure.IsHaarMeasure.comap** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.Measure.IsHaarMeasure`。
形式化陈述：∀ {G : Type u_1} {H : Type u_2} [inst : MeasurableSpace G] [inst_1 : Measu
rableSpace H] [inst_2 : Group G]   [inst_3 : TopologicalSpace G] [BorelSpace G] 
[MeasurableMul G] [inst_6 : Group H] [inst_7 : TopologicalSpace H]   [BorelSpace
 H] {mH : MeasurableMul H} (μ : MeasureTheory.Measure H) [μ.IsHaarMeasure] {f : 
G →* H},   Topology.IsOpenEmbedding ⇑f → (MeasureTheory.Measure.comap (⇑f) μ).Is
HaarMeasure
参数：μ : MeasureTheory.Measure H；MeasureTheory.Measure.comap (⇑f) μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IsFiniteMeasureOnCompacts.comap'`：∀ {α : Type u_1} {β : Ty
pe u_2} {m0 : MeasurableSpace α} {mβ : MeasurableSpace β} [inst : TopologicalSpa
ce α]   [inst_1 : TopologicalSpace β…
· 使用定理 `MeasureTheory.Measure.IsHaarMeasure.toIsFiniteMeasureOnCompacts`：∀ {G : 
Type u_3} {inst : Group G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpa
ce G}   {μ : MeasureTheory.Measure G} [self : μ.IsHaa…
· 使用定理 `Topology.IsOpenEmbedding.continuous`：∀ {X : Type u_1} {Y : Type u_2} {f 
: X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.I
sOpenEmbedding f → Contin…
· 使用定理 `Topology.IsOpenEmbedding.measurableEmbedding`：∀ {α : Type u_1} {β : Type
 u_2} [inst : TopologicalSpace α] [mα : MeasurableSpace α] [BorelSpace α]   [mβ 
: TopologicalSpace β] [inst_2 : Me…
· 使用定理 `MeasureTheory.Measure.IsMulLeftInvariant.comap`：∀ {G : Type u_1} [inst :
 MeasurableSpace G] [inst_1 : Group G] [MeasurableMul G] {H : Type u_3} [inst_3 
: Group H]   {mH : MeasurableSpace H…
· 使用定理 `MeasureTheory.Measure.IsHaarMeasure.toIsMulLeftInvariant`：∀ {G : Type u_
3} {inst : Group G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpace G}  
 {μ : MeasureTheory.Measure G} [self : μ.IsHaa…
· 使用定理 `MeasureTheory.Measure.IsOpenPosMeasure.comap`：∀ {X : Type u_1} [inst : T
opologicalSpace X] {m : MeasurableSpace X} [BorelSpace X] {Z : Type u_3}   [inst
_2 : TopologicalSpace Z] {mZ : Mea…
· 使用定理 `MeasureTheory.Measure.IsHaarMeasure.toIsOpenPosMeasure`：∀ {G : Type u_3}
 {inst : Group G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpace G}   {
μ : MeasureTheory.Measure G} [self : μ.IsHaa…
-/
protected theorem IsHaarMeasure.comap [BorelSpace G] [MeasurableMul G]
    [Group H] [TopologicalSpace H] [BorelSpace H] {mH : MeasurableMul H}
    (μ : Measure H) [IsHaarMeasure μ] {f : G →* H} (hf : Topology.IsOpenEmbedding f) :
    (μ.comap f).IsHaarMeasure where
  map_mul_left_eq_self := (IsMulLeftInvariant.comap μ hf.measurableEmbedding).map_mul_left_eq_self
  lt_top_of_isCompact := (IsFiniteMeasureOnCompacts.comap' μ hf.continuous
    hf.measurableEmbedding).lt_top_of_isCompact
  open_pos := (IsOpenPosMeasure.comap μ hf).open_pos

/-- The image of a finite Haar measure under a continuous surjective group homomorphism is again
a Haar measure. See also `isHaarMeasure_map`. -/
@[to_additive
/-- The image of a finite additive Haar measure under a continuous surjective additive group
homomorphism is again an additive Haar measure. See also `isAddHaarMeasure_map`. -/]
/-
**MeasureTheory.Measure.isHaarMeasure_map_of_isFiniteMeasure** 是 Mathlib 中的一个定理，
位于命名空间 `MeasureTheory.Measure`。
形式化陈述：isHaarMeasure_map_of_isFiniteMeasure [BorelSpace G] [ContinuousMul G] {H :
 Type*} [Group H] [TopologicalSpace H] [MeasurableSpace H] [BorelSpace H] [Conti
nuousMul H] [IsFiniteMeasure μ] (f : G ->* H) (hf : Continuous f) (h_surj : Surj
ective f) : IsHaarMeasure (Measure.map f μ) where toIsMulLeftInvariant
参数：f : G ->* H；hf : Continuous f；h_surj : Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.isMulLeftInvariant_map`：isMulLeftInvariant_map {H : Type*}
 [MeasurableSpace H] [Mul H] [MeasurableMul H] [IsMulLeftInvariant μ] (f : G ->ₙ
* H) (hf : Measurable f) (…
· 使用定理 `ContinuousMul.measurableMul`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Mul γ]   [SeparatelyCont
inuousMul γ], Mea…
· 使用定理 `instSeparatelyContinuousMulOfContinuousMul`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Mul M] [ContinuousMul M], SeparatelyContinuousMul M
· 使用定理 `MeasureTheory.Measure.IsHaarMeasure.toIsMulLeftInvariant`：∀ {G : Type u_
3} {inst : Group G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpace G}  
 {μ : MeasureTheory.Measure G} [self : μ.IsHaa…
· 使用定理 `Continuous.measurable`：Continuous.measurable {f : α -> γ} (hf : Continuo
us f) : Measurable f
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `Continuous.isOpenPosMeasure_map`：∀ {X : Type u_1} [inst : TopologicalSpa
ce X] {m : MeasurableSpace X} {μ : MeasureTheory.Measure X} [μ.IsOpenPosMeasure]
   [OpensMeasurableSp…
· 使用定理 `MeasureTheory.Measure.IsHaarMeasure.toIsOpenPosMeasure`：∀ {G : Type u_3}
 {inst : Group G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpace G}   {
μ : MeasureTheory.Measure G} [self : μ.IsHaa…
· 使用定理 `isFiniteMeasureOnCompacts_of_isLocallyFiniteMeasure`：∀ {α : Type u_1} [i
nst : TopologicalSpace α] {x : MeasurableSpace α} {μ : MeasureTheory.Measure α} 
  [MeasureTheory.IsLocallyFiniteMeasure μ…
· 使用定理 `MeasureTheory.IsFiniteMeasure.toIsLocallyFiniteMeasure`：∀ {α : Type u_1}
 {m0 : MeasurableSpace α} [inst : TopologicalSpace α] (μ : MeasureTheory.Measure
 α)   [MeasureTheory.IsFiniteMeasure μ], Mea…
· 使用定理 `MeasureTheory.Measure.isFiniteMeasure_map`：∀ {α : Type u_1} {β : Type u_
2} [mβ : MeasurableSpace β] {m : MeasurableSpace α} (μ : MeasureTheory.Measure α
)   [MeasureTheory.IsFiniteMeas…
-/
theorem isHaarMeasure_map_of_isFiniteMeasure
    [BorelSpace G] [ContinuousMul G] {H : Type*} [Group H]
    [TopologicalSpace H] [MeasurableSpace H] [BorelSpace H] [ContinuousMul H]
    [IsFiniteMeasure μ] (f : G →* H) (hf : Continuous f) (h_surj : Surjective f) :
    IsHaarMeasure (Measure.map f μ) where
  toIsMulLeftInvariant := isMulLeftInvariant_map f.toMulHom hf.measurable h_surj
  toIsOpenPosMeasure := hf.isOpenPosMeasure_map h_surj

/-- The image of a Haar measure under map of a left action is again a Haar measure. -/
@[to_additive
/-- The image of a Haar measure under map of a left additive action is again a Haar measure -/]
/-
**MeasureTheory.Measure.isHaarMeasure_map_smul** 是 Mathlib 中的一个实例，位于命名空间 `Measur
eTheory.Measure`。
形式化陈述：isHaarMeasure_map_smul {α} [BorelSpace G] [IsTopologicalGroup G] [Group α]
 [MulAction α G] [SMulCommClass α G G] [ContinuousConstSMul α G] (a : α) : IsHaa
rMeasure (Measure.map (a • · : G -> G) μ) where toIsMulLeftInvariant
参数：a : α。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.isMulLeftInvariant_map_smul`：isMulLeftInvariant_map_smul {
α} [SMul α G] [SMulCommClass α G G] [MeasurableConstSMul α G] [IsMulLeftInvarian
t μ] (a : α) : IsMulLeftInvaria…
· 使用定理 `ContinuousMul.measurableMul`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Mul γ]   [SeparatelyCont
inuousMul γ], Mea…
· 使用定理 `instSeparatelyContinuousMulOfContinuousMul`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Mul M] [ContinuousMul M], SeparatelyContinuousMul M
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `ContinuousConstSMul.toMeasurableConstSMul`：∀ {M : Type u_7} {α : Type u_
8} [inst : TopologicalSpace α] [inst_1 : MeasurableSpace α] [BorelSpace α]   [in
st_3 : SMul M α] [ContinuousCon…
· 使用定理 `MeasureTheory.Measure.IsHaarMeasure.toIsMulLeftInvariant`：∀ {G : Type u_
3} {inst : Group G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpace G}  
 {μ : MeasureTheory.Measure G} [self : μ.IsHaa…
· 使用定理 `Continuous.isOpenPosMeasure_map`：∀ {X : Type u_1} [inst : TopologicalSpa
ce X] {m : MeasurableSpace X} {μ : MeasureTheory.Measure X} [μ.IsOpenPosMeasure]
   [OpensMeasurableSp…
· 使用定理 `MeasureTheory.Measure.IsHaarMeasure.toIsOpenPosMeasure`：∀ {G : Type u_3}
 {inst : Group G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpace G}   {
μ : MeasureTheory.Measure G} [self : μ.IsHaa…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `ContinuousConstSMul.continuous_const_smul`：∀ {Γ : Type u_1} {T : Type u_
2} {inst : TopologicalSpace T} {inst_1 : SMul Γ T} [self : ContinuousConstSMul Γ
 T]   (γ : Γ), Continuous fun x…
· 使用定理 `MulAction.surjective`：∀ {α : Type u_5} {β : Type u_6} [inst : Group α] [
inst_1 : MulAction α β] (g : α), Function.Surjective fun x => g • x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasurableEquiv.map_apply`：∀ {α : Type u_1} {β : Type u_2} {x : Measurab
leSpace α} [inst : MeasurableSpace β] {μ : MeasureTheory.Measure α}   (f : α ≃ᵐ 
β) (s : Set β),…
· 使用定理 `IsCompact.measure_lt_top`：∀ {α : Type u_1} {m0 : MeasurableSpace α} [ins
t : TopologicalSpace α] {μ : MeasureTheory.Measure α}   [MeasureTheory.IsFiniteM
easureOnCompac…
· 使用定理 `MeasureTheory.Measure.IsHaarMeasure.toIsFiniteMeasureOnCompacts`：∀ {G : 
Type u_3} {inst : Group G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpa
ce G}   {μ : MeasureTheory.Measure G} [self : μ.IsHaa…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Homeomorph.isCompact_preimage`：isCompact_preimage {s : Set Y} (h : X ≃ₜ 
Y) : IsCompact (h ⁻¹' s) ↔ IsCompact s
-/
instance isHaarMeasure_map_smul {α} [BorelSpace G] [IsTopologicalGroup G]
    [Group α] [MulAction α G] [SMulCommClass α G G] [ContinuousConstSMul α G] (a : α) :
    IsHaarMeasure (Measure.map (a • · : G → G) μ) where
  toIsMulLeftInvariant := isMulLeftInvariant_map_smul _
  lt_top_of_isCompact K hK := by
    let F := (Homeomorph.smul a (α := G)).toMeasurableEquiv
    change map F μ K < ∞
    rw [F.map_apply K]
    exact IsCompact.measure_lt_top <| (Homeomorph.isCompact_preimage (Homeomorph.smul a)).2 hK
  toIsOpenPosMeasure :=
    (continuous_const_smul a).isOpenPosMeasure_map (MulAction.surjective a)

/-- The image of a Haar measure under right multiplication is again a Haar measure. -/
@[to_additive isHaarMeasure_map_add_right
  /-- The image of a Haar measure under right addition is again a Haar measure. -/]
/-
**MeasureTheory.Measure.isHaarMeasure_map_mul_right** 是 Mathlib 中的一个实例，位于命名空间 `M
easureTheory.Measure`。
形式化陈述：isHaarMeasure_map_mul_right [BorelSpace G] [IsTopologicalGroup G] (g : G) 
: IsHaarMeasure (Measure.map (· * g) μ)
参数：g : G。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `instSeparatelyContinuousMulOfContinuousMul`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Mul M] [ContinuousMul M], SeparatelyContinuousMul M
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
-/
instance isHaarMeasure_map_mul_right [BorelSpace G] [IsTopologicalGroup G] (g : G) :
    IsHaarMeasure (Measure.map (· * g) μ) :=
  isHaarMeasure_map_smul μ (MulOpposite.op g)

/-- A convenience wrapper for `MeasureTheory.Measure.isHaarMeasure_map`. -/
@[to_additive /-- A convenience wrapper for `MeasureTheory.Measure.isAddHaarMeasure_map`. -/]
nonrec theorem _root_.MulEquiv.isHaarMeasure_map [BorelSpace G] [ContinuousMul G] {H : Type*}
    [Group H] [TopologicalSpace H] [MeasurableSpace H] [BorelSpace H]
    [IsTopologicalGroup H] (e : G ≃* H) (he : Continuous e) (hesymm : Continuous e.symm) :
    IsHaarMeasure (Measure.map e μ) :=
  let f : G ≃ₜ H := .mk e he hesymm
  -- We need to write `e.toMonoidHom` instead of just `e`, to avoid unification issues.
  isHaarMeasure_map μ e.toMonoidHom he e.surjective f.isClosedEmbedding.tendsto_cocompact

/--
A convenience wrapper for `MeasureTheory.Measure.isHaarMeasure_map`.
-/
@[to_additive /-- A convenience wrapper for `MeasureTheory.Measure.isAddHaarMeasure_map`. -/]
/-
**MeasureTheory.Measure._root_.ContinuousMulEquiv.isHaarMeasure_map** 是 Mathlib 
中的一个实例，位于命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A convenience wrapper for `MeasureTheory.Measure.isHaarMeasure_map`.
-/
instance _root_.ContinuousMulEquiv.isHaarMeasure_map [BorelSpace G] [IsTopologicalGroup G]
    {H : Type*} [Group H] [TopologicalSpace H] [MeasurableSpace H] [BorelSpace H]
    [IsTopologicalGroup H] (e : G ≃ₜ* H) : (μ.map e).IsHaarMeasure :=
  e.toMulEquiv.isHaarMeasure_map μ e.continuous e.symm.continuous

/-- A convenience wrapper for `MeasureTheory.Measure.isAddHaarMeasure_map`. -/
/-
**MeasureTheory.Measure._root_.ContinuousLinearEquiv.isAddHaarMeasure_map** 是 Ma
thlib 中的一个实例，位于命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A convenience wrapper for `MeasureTheory.Measure.isAddHaarMeasure_map`.
-/
instance _root_.ContinuousLinearEquiv.isAddHaarMeasure_map
    {E F R S : Type*} [Semiring R] [Semiring S]
    [AddCommGroup E] [Module R E] [AddCommGroup F] [Module S F]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [TopologicalSpace F]
    [IsTopologicalAddGroup F]
    {σ : R →+* S} {σ' : S →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
    (L : E ≃SL[σ] F) (μ : Measure E) [IsAddHaarMeasure μ] :
    IsAddHaarMeasure (μ.map L) :=
  AddEquiv.isAddHaarMeasure_map _ (L : E ≃+ F) L.continuous L.symm.continuous

/-- A Haar measure on a σ-compact space is σ-finite.

See Note [lower instance priority] -/
@[to_additive
/-- A Haar measure on a σ-compact space is σ-finite.

See Note [lower instance priority] -/]
/-
**MeasureTheory.Measure.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) IsHaarMeasure.sigmaFinite [SigmaCompactSpace G] : SigmaFinite μ :=
  ⟨⟨{   set := compactCovering G
        set_mem := fun _ => mem_univ _
        finite := fun n => IsCompact.measure_lt_top <| isCompact_compactCovering G n
        spanning := iUnion_compactCovering G }⟩⟩

@[to_additive]
/-
**MeasureTheory.Measure.prod.instIsHaarMeasure** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.Measure.prod`。
形式化陈述：∀ {G : Type u_3} [inst : Group G] [inst_1 : TopologicalSpace G] {x : Measu
rableSpace G} {H : Type u_4}   [inst_2 : Group H] [inst_3 : TopologicalSpace H] 
{x_1 : MeasurableSpace H} (μ : MeasureTheory.Measure G)   (ν : MeasureTheory.Mea
sure H) [μ.IsHaarMeasure] [ν.IsHaarMeasure] [MeasureTheory.SFinite μ] [MeasureTh
eory.SFinite ν]   [MeasurableMul G] [MeasurableMul H], (μ.prod ν).IsHaarMeasure
参数：μ : MeasureTheory.Measure G；ν : MeasureTheory.Measure H；μ.prod ν。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.prod.instIsFiniteMeasureOnCompacts`：∀ {α : Type u_
4} {β : Type u_5} [inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] {mα 
: MeasurableSpace α}   {mβ : MeasurableSpace β…
· 使用定理 `MeasureTheory.Measure.IsHaarMeasure.toIsFiniteMeasureOnCompacts`：∀ {G : 
Type u_3} {inst : Group G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpa
ce G}   {μ : MeasureTheory.Measure G} [self : μ.IsHaa…
· 使用定理 `MeasureTheory.Measure.prod.instIsMulLeftInvariant`：∀ {G : Type u_1} [ins
t : MeasurableSpace G] [inst_1 : Mul G] {μ : MeasureTheory.Measure G} [Measurabl
eMul G]   [μ.IsMulLeftInvariant] [Measu…
· 使用定理 `MeasureTheory.Measure.IsHaarMeasure.toIsMulLeftInvariant`：∀ {G : Type u_
3} {inst : Group G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpace G}  
 {μ : MeasureTheory.Measure G} [self : μ.IsHaa…
· 使用定理 `MeasureTheory.Measure.prod.instIsOpenPosMeasure`：∀ {X : Type u_4} {Y : T
ype u_5} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y] {m : Measurab
leSpace X}   {μ : MeasureTheory.Measu…
· 使用定理 `MeasureTheory.Measure.IsHaarMeasure.toIsOpenPosMeasure`：∀ {G : Type u_3}
 {inst : Group G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpace G}   {
μ : MeasureTheory.Measure G} [self : μ.IsHaa…
-/
instance prod.instIsHaarMeasure {G : Type*} [Group G] [TopologicalSpace G] {_ : MeasurableSpace G}
    {H : Type*} [Group H] [TopologicalSpace H] {_ : MeasurableSpace H} (μ : Measure G)
    (ν : Measure H) [IsHaarMeasure μ] [IsHaarMeasure ν] [SFinite μ] [SFinite ν]
    [MeasurableMul G] [MeasurableMul H] : IsHaarMeasure (μ.prod ν) where

/-- If the neutral element of a group is not isolated, then a Haar measure on this group has value
zero on singletons.

The additive version of this instance applies in particular to show that an additive Haar
measure on a nontrivial finite-dimensional real vector space has no atom. -/
@[to_additive
/-- If the zero element of an additive group is not isolated, then an additive Haar measure on this
group has value zero on singletons.

This applies in particular to show that an additive Haar measure on a nontrivial
finite-dimensional real vector space has no atom. -/]
/-
**MeasureTheory.Measure.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) IsHaarMeasure.nullSingletonClass [IsTopologicalGroup G] [BorelSpace G]
    [T1Space G] [WeaklyLocallyCompactSpace G] [(𝓝[≠] (1 : G)).NeBot] (μ : Measure G)
    [μ.IsHaarMeasure] : NullSingletonClass μ := by
  cases eq_or_ne (μ 1) 0 with
  | inl h => constructor; simpa
  | inr h =>
    obtain ⟨K, K_compact, K_nhds⟩ : ∃ K : Set G, IsCompact K ∧ K ∈ 𝓝 1 := exists_compact_mem_nhds 1
    have K_inf : Set.Infinite K := infinite_of_mem_nhds (1 : G) K_nhds
    exact absurd (K_inf.meas_eq_top ⟨_, h, fun x _ ↦ (haar_singleton _ _).ge⟩)
      K_compact.measure_lt_top.ne

@[deprecated (since := "2026-06-09")]
alias IsHaarMeasure.noAtoms := IsHaarMeasure.nullSingletonClass
/-
**MeasureTheory.Measure.IsAddHaarMeasure.domSMul** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.Measure.IsAddHaarMeasure`。
形式化陈述：∀ {G : Type u_3} {A : Type u_4} [inst : Group G] [inst_1 : AddCommGroup A]
 [inst_2 : DistribMulAction G A]   [inst_3 : MeasurableSpace A] [inst_4 : Topolo
gicalSpace A] [inst_5 : BorelSpace A] [IsTopologicalAddGroup A]   [inst_7 : Cont
inuousConstSMul G A] {μ : MeasureTheory.Measure A} [μ.IsAddHaarMeasure] (g : Gᵈᵐ
ᵃ),   (g • μ).IsAddHaarMeasure
参数：g : Gᵈᵐᵃ；g • μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddEquiv.isAddHaarMeasure_map`：∀ {G : Type u_1} [inst : MeasurableSpace 
G] [inst_1 : AddGroup G] [inst_2 : TopologicalSpace G]   (μ : MeasureTheory.Meas
ure G) [μ.IsAddHaar…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `ContinuousConstSMul.continuous_const_smul`：∀ {Γ : Type u_1} {T : Type u_
2} {inst : TopologicalSpace T} {inst_1 : SMul Γ T} [self : ContinuousConstSMul Γ
 T]   (γ : Γ), Continuous fun x…
-/
instance IsAddHaarMeasure.domSMul {G A : Type*} [Group G] [AddCommGroup A] [DistribMulAction G A]
    [MeasurableSpace A] [TopologicalSpace A] [BorelSpace A] [IsTopologicalAddGroup A]
    [ContinuousConstSMul G A] {μ : Measure A} [μ.IsAddHaarMeasure] (g : Gᵈᵐᵃ) :
    (g • μ).IsAddHaarMeasure :=
  (DistribMulAction.toAddEquiv _ (DomMulAct.mk.symm g⁻¹)).isAddHaarMeasure_map _
    (continuous_const_smul _) (continuous_const_smul _)

end Measure

end Haar

end MeasureTheory

