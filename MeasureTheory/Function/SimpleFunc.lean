/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl
-/
module

public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Simple functions

A function `f` from a measurable space to any type is called *simple*, if every preimage `f ⁻¹' {x}`
is measurable, and the range is finite. In this file, we define simple functions and establish their
basic properties; and we construct a sequence of simple functions approximating an arbitrary Borel
measurable function `f : α → ℝ≥0∞`.

The theorem `Measurable.ennreal_induction` shows that in order to prove something for an arbitrary
measurable function into `ℝ≥0∞`, it is sufficient to show that the property holds for (multiples of)
characteristic functions and is closed under addition and supremum of increasing sequences of
functions.
-/

@[expose] public section


noncomputable section

open Set hiding restrict restrict_apply

open Filter ENNReal

open Function (support)

open Topology NNReal ENNReal MeasureTheory

namespace MeasureTheory

variable {α β γ δ : Type*}

/--
Definition of `SimpleFunc.` / `SimpleFunc.` 的定义

English:
structure SimpleFunc.{u,
  parameters: v} (α
  axioms and operations (3):
    - toFun : α -> β
    - measurableSet_fiber' : forall x, MeasurableSet (toFun ⁻¹' {x})
    - finite_range' : (Set.range toFun).Finite

中文:
结构 SimpleFunc.{u,
  参数: v} (α
  公理与运算 (3 个):
    - toFun : α -> β
    - measurableSet_fiber' : 对任意 x, MeasurableSet (toFun ⁻¹' {x})
    - finite_range' : (Set.range toFun).Finite
-/
structure SimpleFunc.{u, v} (α : Type u) [MeasurableSpace α] (β : Type v) where
  /-- The underlying function -/
  toFun : α -> β
  measurableSet_fiber' : forall x, MeasurableSet (toFun ⁻¹' {x})
  finite_range' : (Set.range toFun).Finite

local infixr:25 " ->ₛ " => SimpleFunc

namespace SimpleFunc

section Measurable

variable [MeasurableSpace α]

/--
Instance `instFunLike` / 实例 `instFunLike`

English:
instance instFunLike
  signature: : FunLike (α ->ₛ β) α β where
  body: toFun
  coe_injective | ⟨_, _, _⟩, ⟨_, _, _⟩, rfl => rfl

中文:
实例 instFunLike
  签名: : FunLike (α ->ₛ β) α β where
  定义体: toFun
  coe_injective | ⟨_, _, _⟩, ⟨_, _, _⟩, rfl => rfl
-/
instance instFunLike : FunLike (α ->ₛ β) α β where
  coe := toFun
  coe_injective | ⟨_, _, _⟩, ⟨_, _, _⟩, rfl => rfl

/--
theorem `coe_injective` / 定理 `coe_injective`

English:
theorem coe_injective
  given: ⦃f g
  statement: α ->ₛ β⦄ (H : (f : α -> β) = g) : f = g
  proof: DFunLike.ext' H

@[ext]

中文:
定理 coe_injective
  条件: ⦃f g
  结论: α ->ₛ β⦄ (H : (f : α -> β) = g) : f = g
  证明: DFunLike.ext' H

@[ext]

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem coe_injective ⦃f g : α ->ₛ β⦄ (H : (f : α -> β) = g) : f = g := DFunLike.ext' H

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {f g : α ->ₛ β} (H : forall a, f a = g a)
  statement: f = g
  proof: DFunLike.ext _ _ H

中文:
定理 ext
  条件: {f g : α ->ₛ β} (H : 对任意 a, f a = g a)
  结论: f = g
  证明: DFunLike.ext _ _ H

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem ext {f g : α ->ₛ β} (H : forall a, f a = g a) : f = g := DFunLike.ext _ _ H

/--
theorem `finite_range` / 定理 `finite_range`

English:
theorem finite_range
  given: (f : α ->ₛ β)
  statement: (Set.range f).Finite
  proof: f.finite_range'

中文:
定理 finite_range
  条件: (f : α ->ₛ β)
  结论: (Set.range f).Finite
  证明: f.finite_range'

Depends on / 依赖: f.finite_range, finite_range
-/
theorem finite_range (f : α ->ₛ β) : (Set.range f).Finite :=
  f.finite_range'

/--
theorem `measurableSet_fiber` / 定理 `measurableSet_fiber`

English:
theorem measurableSet_fiber
  given: (f : α ->ₛ β) (x : β)
  statement: MeasurableSet (f ⁻¹' {x})
  proof: f.measurableSet_fiber' x

中文:
定理 measurableSet_fiber
  条件: (f : α ->ₛ β) (x : β)
  结论: MeasurableSet (f ⁻¹' {x})
  证明: f.measurableSet_fiber' x

Depends on / 依赖: f.measurableSet_fiber, measurableSet_fiber
-/
theorem measurableSet_fiber (f : α ->ₛ β) (x : β) : MeasurableSet (f ⁻¹' {x}) :=
  f.measurableSet_fiber' x

/--
theorem `coe_mk` / 定理 `coe_mk`

English:
theorem coe_mk
  given: (f : α -> β) (h h')
  statement: ⇑(mk f h h') = f
  proof: rfl

中文:
定理 coe_mk
  条件: (f : α -> β) (h h')
  结论: ⇑(mk f h h') = f
  证明: rfl
-/
@[simp] theorem coe_mk (f : α -> β) (h h') : ⇑(mk f h h') = f := rfl

/--
theorem `apply_mk` / 定理 `apply_mk`

English:
theorem apply_mk
  given: (f : α -> β) (h h') (x : α)
  statement: SimpleFunc.mk f h h' x = f x
  proof: rfl

中文:
定理 apply_mk
  条件: (f : α -> β) (h h') (x : α)
  结论: SimpleFunc.mk f h h' x = f x
  证明: rfl
-/
theorem apply_mk (f : α -> β) (h h') (x : α) : SimpleFunc.mk f h h' x = f x :=
  rfl

/--
Definition of `ofFinite` / `ofFinite` 的定义

English:
definition ofFinite
  signature: [Finite α] [MeasurableSingletonClass α] (f : α -> β)
  body: f
  measurableSet_fiber' x := (toFinite (f ⁻¹' {x})).measurableSet
  finite_range' := Set.finite_range f

中文:
定义 ofFinite
  签名: [Finite α] [MeasurableSingletonClass α] (f : α -> β)
  定义体: f
  measurableSet_fiber' x := (toFinite (f ⁻¹' {x})).measurableSet
  finite_range' := Set.finite_range f
-/
def ofFinite [Finite α] [MeasurableSingletonClass α] (f : α -> β) : α ->ₛ β where
  toFun := f
  measurableSet_fiber' x := (toFinite (f ⁻¹' {x})).measurableSet
  finite_range' := Set.finite_range f


/--
Definition of `ofIsEmpty` / `ofIsEmpty` 的定义

English:
definition ofIsEmpty
  signature: [IsEmpty α]
  body: ofFinite isEmptyElim

中文:
定义 ofIsEmpty
  签名: [IsEmpty α]
  定义体: ofFinite isEmptyElim

Depends on / 依赖: isEmptyElim, ofFinite
-/
def ofIsEmpty [IsEmpty α] : α ->ₛ β := ofFinite isEmptyElim

/--
Definition of `range` / `range` 的定义

English:
definition range
  signature: (f : α ->ₛ β)
  body: f.finite_range.toFinset

@[simp]

中文:
定义 range
  签名: (f : α ->ₛ β)
  定义体: f.finite_range.toFinset

@[simp]
-/
protected def range (f : α ->ₛ β) : Finset β :=
  f.finite_range.toFinset

@[simp]
/--
theorem `mem_range` / 定理 `mem_range`

English:
theorem mem_range
  given: {f : α ->ₛ β} {b}
  statement: b in f.range ↔ b in range f
  proof: Finite.mem_toFinset _

中文:
定理 mem_range
  条件: {f : α ->ₛ β} {b}
  结论: b in f.range ↔ b in range f
  证明: Finite.mem_toFinset _

Depends on / 依赖: Finite, Finite.mem_toFinset, mem_toFinset
-/
theorem mem_range {f : α ->ₛ β} {b} : b in f.range ↔ b in range f :=
  Finite.mem_toFinset _

/--
theorem `mem_range_self` / 定理 `mem_range_self`

English:
theorem mem_range_self
  given: (f : α ->ₛ β) (x : α)
  statement: f x in f.range
  proof: mem_range.2 ⟨x, rfl⟩

@[simp]

中文:
定理 mem_range_self
  条件: (f : α ->ₛ β) (x : α)
  结论: f x in f.range
  证明: mem_range.2 ⟨x, rfl⟩

@[simp]

Depends on / 依赖: mem_range
-/
theorem mem_range_self (f : α ->ₛ β) (x : α) : f x in f.range :=
  mem_range.2 ⟨x, rfl⟩

@[simp]
/--
theorem `coe_range` / 定理 `coe_range`

English:
theorem coe_range
  given: (f : α ->ₛ β)
  statement: (↑f.range : Set β) = Set.range f
  proof: f.finite_range.coe_toFinset

中文:
定理 coe_range
  条件: (f : α ->ₛ β)
  结论: (↑f.range : Set β) = Set.range f
  证明: f.finite_range.coe_toFinset

Depends on / 依赖: coe_toFinset, f.finite_range.coe_toFinset, finite_range
-/
theorem coe_range (f : α ->ₛ β) : (↑f.range : Set β) = Set.range f :=
  f.finite_range.coe_toFinset

/--
theorem `mem_range_of_measure_ne_zero` / 定理 `mem_range_of_measure_ne_zero`

English:
theorem mem_range_of_measure_ne_zero
  given: {f : α ->ₛ β} {x : β} {μ : Measure α} (H : μ (f ⁻¹' {x}) != 0)
  proof: let ⟨a, ha⟩ := nonempty_of_measure_ne_zero H
  mem_range.2 ⟨a, ha⟩

中文:
定理 mem_range_of_measure_ne_zero
  条件: {f : α ->ₛ β} {x : β} {μ : Measure α} (H : μ (f ⁻¹' {x}) != 0)
  证明: let ⟨a, ha⟩ := nonempty_of_measure_ne_zero H
  mem_range.2 ⟨a, ha⟩

Depends on / 依赖: mem_range, nonempty_of_measure_ne_zero
-/
theorem mem_range_of_measure_ne_zero {f : α ->ₛ β} {x : β} {μ : Measure α} (H : μ (f ⁻¹' {x}) != 0) :
    x in f.range :=
  let ⟨a, ha⟩ := nonempty_of_measure_ne_zero H
  mem_range.2 ⟨a, ha⟩

/--
theorem `forall_mem_range` / 定理 `forall_mem_range`

English:
theorem forall_mem_range
  given: {f : α ->ₛ β} {p : β -> Prop}
  statement: (forall y in f.range, p y) ↔ forall x, p (f x)
  proof: by
  simp only [mem_range, Set.forall_mem_range]

中文:
定理 forall_mem_range
  条件: {f : α ->ₛ β} {p : β -> 命题}
  结论: (对任意 y in f.range, p y) ↔ 对任意 x, p (f x)
  证明: by
  simp only [mem_range, Set.forall_mem_range]

Depends on / 依赖: Set.forall_mem_range, forall_mem_range, mem_range
-/
theorem forall_mem_range {f : α ->ₛ β} {p : β -> Prop} : (forall y in f.range, p y) ↔ forall x, p (f x) := by
  simp only [mem_range, Set.forall_mem_range]

/--
theorem `exists_range_iff` / 定理 `exists_range_iff`

English:
theorem exists_range_iff
  given: {f : α ->ₛ β} {p : β -> Prop}
  statement: (exists y in f.range, p y) ↔ exists x, p (f x)
  proof: by
  simpa only [mem_range, exists_prop] using Set.exists_range_iff

中文:
定理 exists_range_iff
  条件: {f : α ->ₛ β} {p : β -> 命题}
  结论: (存在 y in f.range, p y) ↔ 存在 x, p (f x)
  证明: by
  simpa only [mem_range, exists_prop] using Set.exists_range_iff

Depends on / 依赖: Set.exists_range_iff, exists_prop, exists_range_iff, mem_range
-/
theorem exists_range_iff {f : α ->ₛ β} {p : β -> Prop} : (exists y in f.range, p y) ↔ exists x, p (f x) := by
  simpa only [mem_range, exists_prop] using Set.exists_range_iff

/--
theorem `preimage_eq_empty_iff` / 定理 `preimage_eq_empty_iff`

English:
theorem preimage_eq_empty_iff
  given: (f : α ->ₛ β) (b : β)
  statement: f ⁻¹' {b} = ∅ ↔ b ∉ f.range
  proof: preimage_singleton_eq_empty.trans not_congr mem_range.symm

中文:
定理 preimage_eq_empty_iff
  条件: (f : α ->ₛ β) (b : β)
  结论: f ⁻¹' {b} = ∅ ↔ b ∉ f.range
  证明: preimage_singleton_eq_empty.trans not_congr mem_range.symm

Depends on / 依赖: mem_range, mem_range.symm, not_congr, preimage_singleton_eq_empty, preimage_singleton_eq_empty.trans
-/
theorem preimage_eq_empty_iff (f : α ->ₛ β) (b : β) : f ⁻¹' {b} = ∅ ↔ b ∉ f.range :=
preimage_singleton_eq_empty.trans not_congr mem_range.symm

/--
theorem `exists_forall_le` / 定理 `exists_forall_le`

English:
theorem exists_forall_le
  given: [Nonempty β] [Preorder β] [IsDirectedOrder β] (f : α ->ₛ β)
  proof: f.range.exists_le.imp fun _ => forall_mem_range.1

中文:
定理 exists_forall_le
  条件: [Nonempty β] [Preorder β] [IsDirectedOrder β] (f : α ->ₛ β)
  证明: f.range.exists_le.imp fun _ => forall_mem_range.1

Depends on / 依赖: exists_le, f.range.exists_le.imp, forall_mem_range
-/
theorem exists_forall_le [Nonempty β] [Preorder β] [IsDirectedOrder β] (f : α ->ₛ β) :
    exists C, forall x, f x <= C :=
  f.range.exists_le.imp fun _ => forall_mem_range.1

/--
Definition of `const` / `const` 的定义

English:
definition const
  signature: (α) {β} [MeasurableSpace α] (b : β)
  body: ⟨fun _ => b, fun _ => MeasurableSet.const _, finite_range_const⟩

中文:
定义 const
  签名: (α) {β} [MeasurableSpace α] (b : β)
  定义体: ⟨fun _ => b, fun _ => MeasurableSet.const _, finite_range_const⟩

Depends on / 依赖: MeasurableSet, MeasurableSet.const, finite_range_const
-/
def const (α) {β} [MeasurableSpace α] (b : β) : α ->ₛ β :=
  ⟨fun _ => b, fun _ => MeasurableSet.const _, finite_range_const⟩

/--
Instance `instInhabited` / 实例 `instInhabited`

English:
instance instInhabited
  signature: [Inhabited β]
  body: ⟨const _ default⟩

中文:
实例 instInhabited
  签名: [Inhabited β]
  定义体: ⟨const _ default⟩
-/
instance instInhabited [Inhabited β] : Inhabited (α ->ₛ β) :=
  ⟨const _ default⟩

/--
theorem `const_apply` / 定理 `const_apply`

English:
theorem const_apply
  given: (a : α) (b : β)
  statement: (const α b) a = b
  proof: rfl

@[simp]

中文:
定理 const_apply
  条件: (a : α) (b : β)
  结论: (const α b) a = b
  证明: rfl

@[simp]
-/
theorem const_apply (a : α) (b : β) : (const α b) a = b :=
  rfl

@[simp]
/--
theorem `coe_const` / 定理 `coe_const`

English:
theorem coe_const
  given: (b : β)
  statement: ⇑(const α b) = Function.const α b
  proof: rfl

@[simp]

中文:
定理 coe_const
  条件: (b : β)
  结论: ⇑(const α b) = Function.const α b
  证明: rfl

@[simp]
-/
theorem coe_const (b : β) : ⇑(const α b) = Function.const α b :=
  rfl

@[simp]
/--
theorem `range_const` / 定理 `range_const`

English:
theorem range_const
  given: (α) [MeasurableSpace α] [Nonempty α] (b : β)
  statement: (const α b).range = {b}
  proof: Finset.coe_injective by simp +unfoldPartialApp [Function.const]

中文:
定理 range_const
  条件: (α) [MeasurableSpace α] [Nonempty α] (b : β)
  结论: (const α b).range = {b}
  证明: Finset.coe_injective by simp +unfoldPartialApp [Function.const]

Depends on / 依赖: Finset, Finset.coe_injective, Function, Function.const, coe_injective, unfoldPartialApp
-/
theorem range_const (α) [MeasurableSpace α] [Nonempty α] (b : β) : (const α b).range = {b} :=
Finset.coe_injective by simp +unfoldPartialApp [Function.const]

/--
theorem `range_const_subset` / 定理 `range_const_subset`

English:
theorem range_const_subset
  given: (α) [MeasurableSpace α] (b : β)
  statement: (const α b).range subseteq {b}
  proof: Finset.coe_subset.1 by simp

中文:
定理 range_const_subset
  条件: (α) [MeasurableSpace α] (b : β)
  结论: (const α b).range subseteq {b}
  证明: Finset.coe_subset.1 by simp

Depends on / 依赖: Finset, Finset.coe_subset, coe_subset
-/
theorem range_const_subset (α) [MeasurableSpace α] (b : β) : (const α b).range subseteq {b} :=
Finset.coe_subset.1 by simp

/--
theorem `simpleFunc_bot` / 定理 `simpleFunc_bot`

English:
theorem simpleFunc_bot
  given: {α} (f : @SimpleFunc α ⊥ β) [Nonempty β]
  statement: exists c, forall x, f x = c
  proof: by
  have hf_meas := @SimpleFunc.measurableSet_fiber α _ ⊥ f
  simp_rw [MeasurableSpace.measurableSet_bot_iff] at hf_meas
  exact (exists_eq_const_of_preimage_singleton hf_meas).imp fun c hc => congr_fun hc

中文:
定理 simpleFunc_bot
  条件: {α} (f : @SimpleFunc α ⊥ β) [Nonempty β]
  结论: 存在 c, 对任意 x, f x = c
  证明: by
  have hf_meas := @SimpleFunc.measurableSet_fiber α _ ⊥ f
  simp_rw [MeasurableSpace.measurableSet_bot_iff] at hf_meas
  exact (exists_eq_const_of_preimage_singleton hf_meas).imp fun c hc => congr_fun hc

Depends on / 依赖: MeasurableSpace, MeasurableSpace.measurableSet_bot_iff, SimpleFunc, SimpleFunc.measurableSet_fiber, congr_fun, exists_eq_const_of_preimage_singleton, hf_meas, measurableSet_bot_iff, measurableSet_fiber, simp_rw
-/
theorem simpleFunc_bot {α} (f : @SimpleFunc α ⊥ β) [Nonempty β] : exists c, forall x, f x = c := by
  have hf_meas := @SimpleFunc.measurableSet_fiber α _ ⊥ f
  simp_rw [MeasurableSpace.measurableSet_bot_iff] at hf_meas
  exact (exists_eq_const_of_preimage_singleton hf_meas).imp fun c hc => congr_fun hc

/--
theorem `simpleFunc_bot'` / 定理 `simpleFunc_bot'`

English:
theorem simpleFunc_bot'
  given: {α} [Nonempty β] (f : @SimpleFunc α ⊥ β)
  proof: letI : MeasurableSpace α := ⊥; (simpleFunc_bot f).imp fun _ => ext

中文:
定理 simpleFunc_bot'
  条件: {α} [Nonempty β] (f : @SimpleFunc α ⊥ β)
  证明: letI : MeasurableSpace α := ⊥; (simpleFunc_bot f).imp fun _ => ext

Depends on / 依赖: MeasurableSpace, simpleFunc_bot
-/
theorem simpleFunc_bot' {α} [Nonempty β] (f : @SimpleFunc α ⊥ β) :
    exists c, f = @SimpleFunc.const α _ ⊥ c :=
  letI : MeasurableSpace α := ⊥; (simpleFunc_bot f).imp fun _ => ext

/--
theorem `measurableSet_cut` / 定理 `measurableSet_cut`

English:
theorem measurableSet_cut
  given: (r : α -> β -> Prop) (f : α ->ₛ β) (h : forall b, MeasurableSet { a | r a b })
  proof: by
  have : { a | r a (f a) } = ⋃ b in range f, { a | r a b } inter f ⁻¹' {b} := by
    ext a
    suffices r a (f a) ↔ exists i, r a (f i) ∧ f a = f i by simpa
    exact ⟨fun h => ⟨a, ⟨h, rfl⟩⟩, fun ⟨a', ⟨h', e⟩⟩ => e.symm ▸ h'⟩
  rw [this]
  exact
    MeasurableSet.biUnion f.finite_range.countable 

中文:
定理 measurableSet_cut
  条件: (r : α -> β -> 命题) (f : α ->ₛ β) (h : 对任意 b, MeasurableSet { a | r a b })
  证明: by
  have : { a | r a (f a) } = ⋃ b in range f, { a | r a b } inter f ⁻¹' {b} := by
    ext a
    suffices r a (f a) ↔ exists i, r a (f i) ∧ f a = f i by simpa
    exact ⟨fun h => ⟨a, ⟨h, rfl⟩⟩, fun ⟨a', ⟨h', e⟩⟩ => e.symm ▸ h'⟩
  rw [this]
  exact
    MeasurableSet.biUnion f.finite_range.countable 

Depends on / 依赖: MeasurableSet, MeasurableSet.biUnion, MeasurableSet.inter, biUnion, countable, e.symm, f.finite_range.countable, f.measurableSet_fiber, finite_range, measurableSet_fiber
-/
theorem measurableSet_cut (r : α -> β -> Prop) (f : α ->ₛ β) (h : forall b, MeasurableSet { a | r a b }) :
    MeasurableSet { a | r a (f a) } := by
  have : { a | r a (f a) } = ⋃ b in range f, { a | r a b } inter f ⁻¹' {b} := by
    ext a
    suffices r a (f a) ↔ exists i, r a (f i) ∧ f a = f i by simpa
    exact ⟨fun h => ⟨a, ⟨h, rfl⟩⟩, fun ⟨a', ⟨h', e⟩⟩ => e.symm ▸ h'⟩
  rw [this]
  exact
    MeasurableSet.biUnion f.finite_range.countable fun b _ =>
      MeasurableSet.inter (h b) (f.measurableSet_fiber _)

@[measurability]
/--
theorem `measurableSet_preimage` / 定理 `measurableSet_preimage`

English:
theorem measurableSet_preimage
  given: (f : α ->ₛ β) (s)
  statement: MeasurableSet (f ⁻¹' s)
  proof: measurableSet_cut (fun _ b => b in s) f fun b => MeasurableSet.const (b in s)

中文:
定理 measurableSet_preimage
  条件: (f : α ->ₛ β) (s)
  结论: MeasurableSet (f ⁻¹' s)
  证明: measurableSet_cut (fun _ b => b in s) f fun b => MeasurableSet.const (b in s)

Depends on / 依赖: MeasurableSet, MeasurableSet.const, measurableSet_cut
-/
theorem measurableSet_preimage (f : α ->ₛ β) (s) : MeasurableSet (f ⁻¹' s) :=
  measurableSet_cut (fun _ b => b in s) f fun b => MeasurableSet.const (b in s)

/-- A simple function is measurable -/
@[fun_prop]
/--
theorem `measurable` / 定理 `measurable`

English:
theorem measurable
  given: [MeasurableSpace β] (f : α ->ₛ β)
  statement: Measurable f
  proof: fun s _ =>
  measurableSet_preimage f s

@[fun_prop]

中文:
定理 measurable
  条件: [MeasurableSpace β] (f : α ->ₛ β)
  结论: Measurable f
  证明: fun s _ =>
  measurableSet_preimage f s

@[fun_prop]
-/
protected theorem measurable [MeasurableSpace β] (f : α ->ₛ β) : Measurable f := fun s _ =>
  measurableSet_preimage f s

@[fun_prop]
/--
theorem `aemeasurable` / 定理 `aemeasurable`

English:
theorem aemeasurable
  given: [MeasurableSpace β] {μ : Measure α} (f : α ->ₛ β)
  proof: f.measurable.aemeasurable

中文:
定理 aemeasurable
  条件: [MeasurableSpace β] {μ : Measure α} (f : α ->ₛ β)
  证明: f.measurable.aemeasurable
-/
protected theorem aemeasurable [MeasurableSpace β] {μ : Measure α} (f : α ->ₛ β) :
    AEMeasurable f μ :=
  f.measurable.aemeasurable

/--
theorem `sum_measure_preimage_singleton` / 定理 `sum_measure_preimage_singleton`

English:
theorem sum_measure_preimage_singleton
  given: (f : α ->ₛ β) {μ : Measure α} (s : Finset β)
  proof: sum_measure_preimage_singleton _ fun _ _ => f.measurableSet_fiber _

中文:
定理 sum_measure_preimage_singleton
  条件: (f : α ->ₛ β) {μ : Measure α} (s : Finset β)
  证明: sum_measure_preimage_singleton _ fun _ _ => f.measurableSet_fiber _
-/
protected theorem sum_measure_preimage_singleton (f : α ->ₛ β) {μ : Measure α} (s : Finset β) :
    (∑ y in s, μ (f ⁻¹' {y})) = μ (f ⁻¹' ↑s) :=
  sum_measure_preimage_singleton _ fun _ _ => f.measurableSet_fiber _

/--
theorem `sum_range_measure_preimage_singleton` / 定理 `sum_range_measure_preimage_singleton`

English:
theorem sum_range_measure_preimage_singleton
  given: (f : α ->ₛ β) (μ : Measure α)
  proof: by
  rw [f.sum_measure_preimage_singleton]; rw [coe_range]; rw [preimage_range]

中文:
定理 sum_range_measure_preimage_singleton
  条件: (f : α ->ₛ β) (μ : Measure α)
  证明: by
  rw [f.sum_measure_preimage_singleton]; rw [coe_range]; rw [preimage_range]

Depends on / 依赖: coe_range, f.sum_measure_preimage_singleton, preimage_range, sum_measure_preimage_singleton
-/
theorem sum_range_measure_preimage_singleton (f : α ->ₛ β) (μ : Measure α) :
    (∑ y in f.range, μ (f ⁻¹' {y})) = μ univ := by
  rw [f.sum_measure_preimage_singleton]; rw [coe_range]; rw [preimage_range]

open scoped Classical in
/--
Definition of `piecewise` / `piecewise` 的定义

English:
definition piecewise
  signature: (s : Set α) (hs : MeasurableSet s) (f g : α ->ₛ β)
  body: ⟨s.piecewise f g, fun _ =>
    letI : MeasurableSpace β := ⊤
    f.measurable.piecewise hs g.measurable trivial,
    (f.finite_range.union g.finite_range).subset range_ite_subset⟩

中文:
定义 piecewise
  签名: (s : Set α) (hs : MeasurableSet s) (f g : α ->ₛ β)
  定义体: ⟨s.piecewise f g, fun _ =>
    letI : MeasurableSpace β := ⊤
    f.measurable.piecewise hs g.measurable trivial,
    (f.finite_range.union g.finite_range).subset range_ite_subset⟩

Depends on / 依赖: MeasurableSpace, f.finite_range.union, f.measurable.piecewise, finite_range, g.finite_range, g.measurable, measurable, piecewise, range_ite_subset, s.piecewise, subset
-/
def piecewise (s : Set α) (hs : MeasurableSet s) (f g : α ->ₛ β) : α ->ₛ β :=
  ⟨s.piecewise f g, fun _ =>
    letI : MeasurableSpace β := ⊤
    f.measurable.piecewise hs g.measurable trivial,
    (f.finite_range.union g.finite_range).subset range_ite_subset⟩

open scoped Classical in
@[simp]
/--
theorem `coe_piecewise` / 定理 `coe_piecewise`

English:
theorem coe_piecewise
  given: {s : Set α} (hs : MeasurableSet s) (f g : α ->ₛ β)
  proof: rfl

中文:
定理 coe_piecewise
  条件: {s : Set α} (hs : MeasurableSet s) (f g : α ->ₛ β)
  证明: rfl
-/
theorem coe_piecewise {s : Set α} (hs : MeasurableSet s) (f g : α ->ₛ β) :
    ⇑(piecewise s hs f g) = s.piecewise f g :=
  rfl

open scoped Classical in
/--
theorem `piecewise_apply` / 定理 `piecewise_apply`

English:
theorem piecewise_apply
  given: {s : Set α} (hs : MeasurableSet s) (f g : α ->ₛ β) (a)
  proof: rfl

中文:
定理 piecewise_apply
  条件: {s : Set α} (hs : MeasurableSet s) (f g : α ->ₛ β) (a)
  证明: rfl
-/
theorem piecewise_apply {s : Set α} (hs : MeasurableSet s) (f g : α ->ₛ β) (a) :
    piecewise s hs f g a = if a in s then f a else g a :=
  rfl

open scoped Classical in
@[simp]
/--
theorem `piecewise_compl` / 定理 `piecewise_compl`

English:
theorem piecewise_compl
  given: {s : Set α} (hs : MeasurableSet sᶜ) (f g : α ->ₛ β)
  proof: coe_injective by simp

@[simp]

中文:
定理 piecewise_compl
  条件: {s : Set α} (hs : MeasurableSet sᶜ) (f g : α ->ₛ β)
  证明: coe_injective by simp

@[simp]

Depends on / 依赖: coe_injective
-/
theorem piecewise_compl {s : Set α} (hs : MeasurableSet sᶜ) (f g : α ->ₛ β) :
    piecewise sᶜ hs f g = piecewise s hs.of_compl g f :=
coe_injective by simp

@[simp]
/--
theorem `piecewise_univ` / 定理 `piecewise_univ`

English:
theorem piecewise_univ
  given: (f g : α ->ₛ β)
  statement: piecewise univ MeasurableSet.univ f g = f
  proof: coe_injective by simp

@[simp]

中文:
定理 piecewise_univ
  条件: (f g : α ->ₛ β)
  结论: piecewise univ MeasurableSet.univ f g = f
  证明: coe_injective by simp

@[simp]

Depends on / 依赖: coe_injective
-/
theorem piecewise_univ (f g : α ->ₛ β) : piecewise univ MeasurableSet.univ f g = f :=
coe_injective by simp

@[simp]
/--
theorem `piecewise_empty` / 定理 `piecewise_empty`

English:
theorem piecewise_empty
  given: (f g : α ->ₛ β)
  statement: piecewise ∅ MeasurableSet.empty f g = g
  proof: coe_injective by simp

@[simp]

中文:
定理 piecewise_empty
  条件: (f g : α ->ₛ β)
  结论: piecewise ∅ MeasurableSet.empty f g = g
  证明: coe_injective by simp

@[simp]

Depends on / 依赖: coe_injective
-/
theorem piecewise_empty (f g : α ->ₛ β) : piecewise ∅ MeasurableSet.empty f g = g :=
coe_injective by simp

@[simp]
/--
theorem `piecewise_same` / 定理 `piecewise_same`

English:
theorem piecewise_same
  given: (f : α ->ₛ β) {s : Set α} (hs : MeasurableSet s)
  proof: by
  classical
exact coe_injective Set.piecewise_same _ _

中文:
定理 piecewise_same
  条件: (f : α ->ₛ β) {s : Set α} (hs : MeasurableSet s)
  证明: by
  classical
exact coe_injective Set.piecewise_same _ _

Depends on / 依赖: Set.piecewise_same, classical, coe_injective, piecewise_same
-/
theorem piecewise_same (f : α ->ₛ β) {s : Set α} (hs : MeasurableSet s) :
    piecewise s hs f f = f := by
  classical
exact coe_injective Set.piecewise_same _ _

/-- Dependent If-then-else as a `SimpleFunc`. -/
@[simps]
/--
Definition of `dite` / `dite` 的定义

English:
definition dite
  signature: (s : Set α) (hs : MeasurableSet s) (f : s ->ₛ β) (g : (sᶜ : Set α) ->ₛ β)
  body: open scoped Classical in if hx : x in s then f ⟨x, hx⟩ else g ⟨x, hx⟩
  measurableSet_fiber' x := by
    classical
    let : MeasurableSpace β := ⊤
    exact Measurable.dite f.measurable g.measurable hs trivial
  finite_range' := (f.finite_range.union g.finite_range).subset (by grind)

中文:
定义 dite
  签名: (s : Set α) (hs : MeasurableSet s) (f : s ->ₛ β) (g : (sᶜ : Set α) ->ₛ β)
  定义体: open scoped Classical in if hx : x in s then f ⟨x, hx⟩ else g ⟨x, hx⟩
  measurableSet_fiber' x := by
    classical
    let : MeasurableSpace β := ⊤
    exact Measurable.dite f.measurable g.measurable hs trivial
  finite_range' := (f.finite_range.union g.finite_range).subset (by grind)

Depends on / 依赖: Classical, scoped
-/
def dite (s : Set α) (hs : MeasurableSet s) (f : s ->ₛ β) (g : (sᶜ : Set α) ->ₛ β) : α ->ₛ β where
  toFun x := open scoped Classical in if hx : x in s then f ⟨x, hx⟩ else g ⟨x, hx⟩
  measurableSet_fiber' x := by
    classical
    let : MeasurableSpace β := ⊤
    exact Measurable.dite f.measurable g.measurable hs trivial
  finite_range' := (f.finite_range.union g.finite_range).subset (by grind)

/--
theorem `support_indicator` / 定理 `support_indicator`

English:
theorem support_indicator
  given: [Zero β] {s : Set α} (hs : MeasurableSet s) (f : α ->ₛ β)
  proof: Set.support_indicator

中文:
定理 support_indicator
  条件: [Zero β] {s : Set α} (hs : MeasurableSet s) (f : α ->ₛ β)
  证明: Set.support_indicator

Depends on / 依赖: Set.support_indicator, support_indicator
-/
theorem support_indicator [Zero β] {s : Set α} (hs : MeasurableSet s) (f : α ->ₛ β) :
    Function.support (f.piecewise s hs (SimpleFunc.const α 0)) = s inter Function.support f :=
  Set.support_indicator

set_option backward.isDefEq.respectTransparency false in
open scoped Classical in
/--
theorem `range_indicator` / 定理 `range_indicator`

English:
theorem range_indicator
  statement: {s : Set α} (hs : MeasurableSet s) (hs_nonempty : s.Nonempty)
  proof: by
  simp only [← Finset.coe_inj, coe_range, coe_piecewise, range_piecewise, coe_const,
    Finset.coe_insert, Finset.coe_singleton, hs_nonempty.image_const,
    (nonempty_compl.2 hs_ne_univ).image_const, singleton_union, Function.const]

中文:
定理 range_indicator
  结论: {s : Set α} (hs : MeasurableSet s) (hs_nonempty : s.Nonempty)
  证明: by
  simp only [← Finset.coe_inj, coe_range, coe_piecewise, range_piecewise, coe_const,
    Finset.coe_insert, Finset.coe_singleton, hs_nonempty.image_const,
    (nonempty_compl.2 hs_ne_univ).image_const, singleton_union, Function.const]

Depends on / 依赖: Finset, Finset.coe_inj, Finset.coe_insert, Finset.coe_singleton, Function, Function.const, coe_const, coe_inj, coe_insert, coe_piecewise, coe_range, coe_singleton, hs_ne_univ, hs_nonempty, hs_nonempty.image_const, image_const, nonempty_compl, range_piecewise, singleton_union
-/
theorem range_indicator {s : Set α} (hs : MeasurableSet s) (hs_nonempty : s.Nonempty)
    (hs_ne_univ : s != univ) (x y : β) :
    (piecewise s hs (const α x) (const α y)).range = {x, y} := by
  simp only [← Finset.coe_inj, coe_range, coe_piecewise, range_piecewise, coe_const,
    Finset.coe_insert, Finset.coe_singleton, hs_nonempty.image_const,
    (nonempty_compl.2 hs_ne_univ).image_const, singleton_union, Function.const]

/--
theorem `measurable_bind` / 定理 `measurable_bind`

English:
theorem measurable_bind
  statement: [MeasurableSpace γ] (f : α ->ₛ β) (g : β -> α -> γ)
  proof: fun s hs =>
  f.measurableSet_cut (fun a b => g b a in s) fun b => hg b hs

中文:
定理 measurable_bind
  结论: [MeasurableSpace γ] (f : α ->ₛ β) (g : β -> α -> γ)
  证明: fun s hs =>
  f.measurableSet_cut (fun a b => g b a in s) fun b => hg b hs
-/
theorem measurable_bind [MeasurableSpace γ] (f : α ->ₛ β) (g : β -> α -> γ)
    (hg : forall b, Measurable (g b)) : Measurable fun a => g (f a) a := fun s hs =>
  f.measurableSet_cut (fun a b => g b a in s) fun b => hg b hs

/--
Definition of `bind` / `bind` 的定义

English:
definition bind
  signature: (f : α ->ₛ β) (g : β -> α ->ₛ γ)
  body: ⟨fun a => g (f a) a, fun c =>
    f.measurableSet_cut (fun a b => g b a = c) fun b => (g b).measurableSet_preimage {c},
(f.finite_range.biUnion fun b _ => (g b).finite_range).subset by
      rintro _ ⟨a, rfl⟩; simp⟩

@[simp]

中文:
定义 bind
  签名: (f : α ->ₛ β) (g : β -> α ->ₛ γ)
  定义体: ⟨fun a => g (f a) a, fun c =>
    f.measurableSet_cut (fun a b => g b a = c) fun b => (g b).measurableSet_preimage {c},
(f.finite_range.biUnion fun b _ => (g b).finite_range).subset by
      rintro _ ⟨a, rfl⟩; simp⟩

@[simp]

Depends on / 依赖: biUnion, f.finite_range.biUnion, f.measurableSet_cut, finite_range, measurableSet_cut, measurableSet_preimage, subset
-/
def bind (f : α ->ₛ β) (g : β -> α ->ₛ γ) : α ->ₛ γ :=
  ⟨fun a => g (f a) a, fun c =>
    f.measurableSet_cut (fun a b => g b a = c) fun b => (g b).measurableSet_preimage {c},
(f.finite_range.biUnion fun b _ => (g b).finite_range).subset by
      rintro _ ⟨a, rfl⟩; simp⟩

@[simp]
/--
theorem `bind_apply` / 定理 `bind_apply`

English:
theorem bind_apply
  given: (f : α ->ₛ β) (g : β -> α ->ₛ γ) (a)
  statement: f.bind g a = g (f a) a
  proof: rfl

中文:
定理 bind_apply
  条件: (f : α ->ₛ β) (g : β -> α ->ₛ γ) (a)
  结论: f.bind g a = g (f a) a
  证明: rfl
-/
theorem bind_apply (f : α ->ₛ β) (g : β -> α ->ₛ γ) (a) : f.bind g a = g (f a) a :=
  rfl

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (g : β -> γ) (f : α ->ₛ β)
  body: bind f (const α ∘ g)

中文:
定义 map
  签名: (g : β -> γ) (f : α ->ₛ β)
  定义体: bind f (const α ∘ g)
-/
def map (g : β -> γ) (f : α ->ₛ β) : α ->ₛ γ :=
  bind f (const α ∘ g)

/--
theorem `map_apply` / 定理 `map_apply`

English:
theorem map_apply
  given: (g : β -> γ) (f : α ->ₛ β) (a)
  statement: f.map g a = g (f a)
  proof: rfl

中文:
定理 map_apply
  条件: (g : β -> γ) (f : α ->ₛ β) (a)
  结论: f.map g a = g (f a)
  证明: rfl
-/
theorem map_apply (g : β -> γ) (f : α ->ₛ β) (a) : f.map g a = g (f a) :=
  rfl

/--
theorem `map_map` / 定理 `map_map`

English:
theorem map_map
  given: (g : β -> γ) (h : γ -> δ) (f : α ->ₛ β)
  statement: (f.map g).map h = f.map (h ∘ g)
  proof: rfl

@[simp]

中文:
定理 map_map
  条件: (g : β -> γ) (h : γ -> δ) (f : α ->ₛ β)
  结论: (f.map g).map h = f.map (h ∘ g)
  证明: rfl

@[simp]
-/
theorem map_map (g : β -> γ) (h : γ -> δ) (f : α ->ₛ β) : (f.map g).map h = f.map (h ∘ g) :=
  rfl

@[simp]
/--
theorem `coe_map` / 定理 `coe_map`

English:
theorem coe_map
  given: (g : β -> γ) (f : α ->ₛ β)
  statement: (f.map g : α -> γ) = g ∘ f
  proof: rfl

@[simp]

中文:
定理 coe_map
  条件: (g : β -> γ) (f : α ->ₛ β)
  结论: (f.map g : α -> γ) = g ∘ f
  证明: rfl

@[simp]
-/
theorem coe_map (g : β -> γ) (f : α ->ₛ β) : (f.map g : α -> γ) = g ∘ f :=
  rfl

@[simp]
/--
theorem `range_map` / 定理 `range_map`

English:
theorem range_map
  given: [DecidableEq γ] (g : β -> γ) (f : α ->ₛ β)
  statement: (f.map g).range = f.range.image g
  proof: Finset.coe_injective by simp only [coe_range, coe_map, Finset.coe_image, range_comp]

@[simp]

中文:
定理 range_map
  条件: [DecidableEq γ] (g : β -> γ) (f : α ->ₛ β)
  结论: (f.map g).range = f.range.image g
  证明: Finset.coe_injective by simp only [coe_range, coe_map, Finset.coe_image, range_comp]

@[simp]

Depends on / 依赖: Finset, Finset.coe_image, Finset.coe_injective, coe_image, coe_injective, coe_map, coe_range, range_comp
-/
theorem range_map [DecidableEq γ] (g : β -> γ) (f : α ->ₛ β) : (f.map g).range = f.range.image g :=
Finset.coe_injective by simp only [coe_range, coe_map, Finset.coe_image, range_comp]

@[simp]
/--
theorem `map_const` / 定理 `map_const`

English:
theorem map_const
  given: (g : β -> γ) (b : β)
  statement: (const α b).map g = const α (g b)
  proof: rfl

中文:
定理 map_const
  条件: (g : β -> γ) (b : β)
  结论: (const α b).map g = const α (g b)
  证明: rfl
-/
theorem map_const (g : β -> γ) (b : β) : (const α b).map g = const α (g b) :=
  rfl

open scoped Classical in
/--
theorem `map_preimage` / 定理 `map_preimage`

English:
theorem map_preimage
  given: (f : α ->ₛ β) (g : β -> γ) (s : Set γ)
  proof: by
  simp only [coe_range, sep_mem_eq, coe_map, Finset.coe_filter,
    ← mem_preimage, inter_comm, preimage_inter_range, ← Finset.mem_coe]
  exact preimage_comp

中文:
定理 map_preimage
  条件: (f : α ->ₛ β) (g : β -> γ) (s : Set γ)
  证明: by
  simp only [coe_range, sep_mem_eq, coe_map, Finset.coe_filter,
    ← mem_preimage, inter_comm, preimage_inter_range, ← Finset.mem_coe]
  exact preimage_comp

Depends on / 依赖: Finset, Finset.coe_filter, Finset.mem_coe, coe_filter, coe_map, coe_range, inter_comm, mem_coe, mem_preimage, preimage_comp, preimage_inter_range, sep_mem_eq
-/
theorem map_preimage (f : α ->ₛ β) (g : β -> γ) (s : Set γ) :
    f.map g ⁻¹' s = f ⁻¹' ↑{b in f.range | g b in s} := by
  simp only [coe_range, sep_mem_eq, coe_map, Finset.coe_filter,
    ← mem_preimage, inter_comm, preimage_inter_range, ← Finset.mem_coe]
  exact preimage_comp

open scoped Classical in
/--
theorem `map_preimage_singleton` / 定理 `map_preimage_singleton`

English:
theorem map_preimage_singleton
  given: (f : α ->ₛ β) (g : β -> γ) (c : γ)
  proof: map_preimage _ _ _

中文:
定理 map_preimage_singleton
  条件: (f : α ->ₛ β) (g : β -> γ) (c : γ)
  证明: map_preimage _ _ _

Depends on / 依赖: map_preimage
-/
theorem map_preimage_singleton (f : α ->ₛ β) (g : β -> γ) (c : γ) :
    f.map g ⁻¹' {c} = f ⁻¹' ↑{b in f.range | g b = c} :=
  map_preimage _ _ _

/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: [MeasurableSpace β] (f : β ->ₛ γ) (g : α -> β) (hgm : Measurable g)
  body: f ∘ g
finite_range' := f.finite_range.subset Set.range_comp_subset_range _ _
  measurableSet_fiber' z := hgm (f.measurableSet_fiber z)

@[simp]

中文:
定义 comp
  签名: [MeasurableSpace β] (f : β ->ₛ γ) (g : α -> β) (hgm : Measurable g)
  定义体: f ∘ g
finite_range' := f.finite_range.subset Set.range_comp_subset_range _ _
  measurableSet_fiber' z := hgm (f.measurableSet_fiber z)

@[simp]
-/
def comp [MeasurableSpace β] (f : β ->ₛ γ) (g : α -> β) (hgm : Measurable g) : α ->ₛ γ where
  toFun := f ∘ g
finite_range' := f.finite_range.subset Set.range_comp_subset_range _ _
  measurableSet_fiber' z := hgm (f.measurableSet_fiber z)

@[simp]
/--
theorem `coe_comp` / 定理 `coe_comp`

English:
theorem coe_comp
  given: [MeasurableSpace β] (f : β ->ₛ γ) {g : α -> β} (hgm : Measurable g)
  proof: rfl

中文:
定理 coe_comp
  条件: [MeasurableSpace β] (f : β ->ₛ γ) {g : α -> β} (hgm : Measurable g)
  证明: rfl
-/
theorem coe_comp [MeasurableSpace β] (f : β ->ₛ γ) {g : α -> β} (hgm : Measurable g) :
    ⇑(f.comp g hgm) = f ∘ g :=
  rfl

/--
theorem `range_comp_subset_range` / 定理 `range_comp_subset_range`

English:
theorem range_comp_subset_range
  given: [MeasurableSpace β] (f : β ->ₛ γ) {g : α -> β} (hgm : Measurable g)
  proof: Finset.coe_subset.1 by simp only [coe_range, coe_comp, Set.range_comp_subset_range]

中文:
定理 range_comp_subset_range
  条件: [MeasurableSpace β] (f : β ->ₛ γ) {g : α -> β} (hgm : Measurable g)
  证明: Finset.coe_subset.1 by simp only [coe_range, coe_comp, Set.range_comp_subset_range]

Depends on / 依赖: Finset, Finset.coe_subset, Set.range_comp_subset_range, coe_comp, coe_range, coe_subset, range_comp_subset_range
-/
theorem range_comp_subset_range [MeasurableSpace β] (f : β ->ₛ γ) {g : α -> β} (hgm : Measurable g) :
    (f.comp g hgm).range subseteq f.range :=
Finset.coe_subset.1 by simp only [coe_range, coe_comp, Set.range_comp_subset_range]

/--
Definition of `extend` / `extend` 的定义

English:
definition extend
  signature: [MeasurableSpace β] (f₁ : α ->ₛ γ) (g : α -> β) (hg : MeasurableEmbedding g)
  body: Function.extend g f₁ f₂
  finite_range' :=
    (f₁.finite_range.union <| f₂.finite_range.subset (image_subset_range _ _)).subset
      (range_extend_subset _ _ _)
  measurableSet_fiber' := by
    let : MeasurableSpace γ := ⊤; have : MeasurableSingletonClass γ := ⟨fun _ => trivial⟩
    exact fun x =>

中文:
定义 extend
  签名: [MeasurableSpace β] (f₁ : α ->ₛ γ) (g : α -> β) (hg : MeasurableEmbedding g)
  定义体: Function.extend g f₁ f₂
  finite_range' :=
    (f₁.finite_range.union <| f₂.finite_range.subset (image_subset_range _ _)).subset
      (range_extend_subset _ _ _)
  measurableSet_fiber' := by
    let : MeasurableSpace γ := ⊤; have : MeasurableSingletonClass γ := ⟨fun _ => trivial⟩
    exact fun x =>

Depends on / 依赖: Function, Function.extend, extend
-/
def extend [MeasurableSpace β] (f₁ : α ->ₛ γ) (g : α -> β) (hg : MeasurableEmbedding g)
    (f₂ : β ->ₛ γ) : β ->ₛ γ where
  toFun := Function.extend g f₁ f₂
  finite_range' :=
    (f₁.finite_range.union <| f₂.finite_range.subset (image_subset_range _ _)).subset
      (range_extend_subset _ _ _)
  measurableSet_fiber' := by
    let : MeasurableSpace γ := ⊤; have : MeasurableSingletonClass γ := ⟨fun _ => trivial⟩
    exact fun x => hg.measurable_extend f₁.measurable f₂.measurable (measurableSet_singleton _)

@[simp]
/--
theorem `extend_apply` / 定理 `extend_apply`

English:
theorem extend_apply
  statement: [MeasurableSpace β] (f₁ : α ->ₛ γ) {g : α -> β} (hg : MeasurableEmbedding g)
  proof: hg.injective.extend_apply _ _ _

@[simp]

中文:
定理 extend_apply
  结论: [MeasurableSpace β] (f₁ : α ->ₛ γ) {g : α -> β} (hg : MeasurableEmbedding g)
  证明: hg.injective.extend_apply _ _ _

@[simp]

Depends on / 依赖: extend_apply, hg.injective.extend_apply, injective
-/
theorem extend_apply [MeasurableSpace β] (f₁ : α ->ₛ γ) {g : α -> β} (hg : MeasurableEmbedding g)
    (f₂ : β ->ₛ γ) (x : α) : (f₁.extend g hg f₂) (g x) = f₁ x :=
  hg.injective.extend_apply _ _ _

@[simp]
/--
theorem `extend_apply'` / 定理 `extend_apply'`

English:
theorem extend_apply'
  statement: [MeasurableSpace β] (f₁ : α ->ₛ γ) {g : α -> β} (hg : MeasurableEmbedding g)
  proof: Function.extend_apply' _ _ _ h

@[simp]

中文:
定理 extend_apply'
  结论: [MeasurableSpace β] (f₁ : α ->ₛ γ) {g : α -> β} (hg : MeasurableEmbedding g)
  证明: Function.extend_apply' _ _ _ h

@[simp]

Depends on / 依赖: Function, Function.extend_apply, extend_apply
-/
theorem extend_apply' [MeasurableSpace β] (f₁ : α ->ₛ γ) {g : α -> β} (hg : MeasurableEmbedding g)
    (f₂ : β ->ₛ γ) {y : β} (h : ¬exists x, g x = y) : (f₁.extend g hg f₂) y = f₂ y :=
  Function.extend_apply' _ _ _ h

@[simp]
/--
theorem `extend_comp_eq'` / 定理 `extend_comp_eq'`

English:
theorem extend_comp_eq'
  statement: [MeasurableSpace β] (f₁ : α ->ₛ γ) {g : α -> β} (hg : MeasurableEmbedding g)
  proof: funext fun _ => extend_apply _ _ _ _

@[simp]

中文:
定理 extend_comp_eq'
  结论: [MeasurableSpace β] (f₁ : α ->ₛ γ) {g : α -> β} (hg : MeasurableEmbedding g)
  证明: funext fun _ => extend_apply _ _ _ _

@[simp]

Depends on / 依赖: extend_apply
-/
theorem extend_comp_eq' [MeasurableSpace β] (f₁ : α ->ₛ γ) {g : α -> β} (hg : MeasurableEmbedding g)
    (f₂ : β ->ₛ γ) : f₁.extend g hg f₂ ∘ g = f₁ :=
  funext fun _ => extend_apply _ _ _ _

@[simp]
/--
theorem `extend_comp_eq` / 定理 `extend_comp_eq`

English:
theorem extend_comp_eq
  statement: [MeasurableSpace β] (f₁ : α ->ₛ γ) {g : α -> β} (hg : MeasurableEmbedding g)
  proof: coe_injective extend_comp_eq' _ hg _

中文:
定理 extend_comp_eq
  结论: [MeasurableSpace β] (f₁ : α ->ₛ γ) {g : α -> β} (hg : MeasurableEmbedding g)
  证明: coe_injective extend_comp_eq' _ hg _

Depends on / 依赖: coe_injective, extend_comp_eq
-/
theorem extend_comp_eq [MeasurableSpace β] (f₁ : α ->ₛ γ) {g : α -> β} (hg : MeasurableEmbedding g)
    (f₂ : β ->ₛ γ) : (f₁.extend g hg f₂).comp g hg.measurable = f₁ :=
coe_injective extend_comp_eq' _ hg _

/--
Definition of `seq` / `seq` 的定义

English:
definition seq
  signature: (f : α ->ₛ β -> γ) (g : α ->ₛ β)
  body: f.bind fun f => g.map f

@[simp]

中文:
定义 seq
  签名: (f : α ->ₛ β -> γ) (g : α ->ₛ β)
  定义体: f.bind fun f => g.map f

@[simp]

Depends on / 依赖: f.bind, g.map
-/
def seq (f : α ->ₛ β -> γ) (g : α ->ₛ β) : α ->ₛ γ :=
  f.bind fun f => g.map f

@[simp]
/--
theorem `seq_apply` / 定理 `seq_apply`

English:
theorem seq_apply
  given: (f : α ->ₛ β -> γ) (g : α ->ₛ β) (a : α)
  statement: f.seq g a = f a (g a)
  proof: rfl

中文:
定理 seq_apply
  条件: (f : α ->ₛ β -> γ) (g : α ->ₛ β) (a : α)
  结论: f.seq g a = f a (g a)
  证明: rfl
-/
theorem seq_apply (f : α ->ₛ β -> γ) (g : α ->ₛ β) (a : α) : f.seq g a = f a (g a) :=
  rfl

/--
Definition of `pair` / `pair` 的定义

English:
definition pair
  signature: (f : α ->ₛ β) (g : α ->ₛ γ)
  body: (f.map Prod.mk).seq g

@[simp]

中文:
定义 pair
  签名: (f : α ->ₛ β) (g : α ->ₛ γ)
  定义体: (f.map Prod.mk).seq g

@[simp]

Depends on / 依赖: Prod.mk, f.map
-/
def pair (f : α ->ₛ β) (g : α ->ₛ γ) : α ->ₛ β × γ :=
  (f.map Prod.mk).seq g

@[simp]
/--
theorem `pair_apply` / 定理 `pair_apply`

English:
theorem pair_apply
  given: (f : α ->ₛ β) (g : α ->ₛ γ) (a)
  statement: pair f g a = (f a, g a)
  proof: rfl

中文:
定理 pair_apply
  条件: (f : α ->ₛ β) (g : α ->ₛ γ) (a)
  结论: pair f g a = (f a, g a)
  证明: rfl
-/
theorem pair_apply (f : α ->ₛ β) (g : α ->ₛ γ) (a) : pair f g a = (f a, g a) :=
  rfl

/--
theorem `pair_preimage` / 定理 `pair_preimage`

English:
theorem pair_preimage
  given: (f : α ->ₛ β) (g : α ->ₛ γ) (s : Set β) (t : Set γ)
  proof: rfl

中文:
定理 pair_preimage
  条件: (f : α ->ₛ β) (g : α ->ₛ γ) (s : Set β) (t : Set γ)
  证明: rfl
-/
theorem pair_preimage (f : α ->ₛ β) (g : α ->ₛ γ) (s : Set β) (t : Set γ) :
    pair f g ⁻¹' s ×ˢ t = f ⁻¹' s inter g ⁻¹' t :=
  rfl

-- A special form of `pair_preimage`
/--
theorem `pair_preimage_singleton` / 定理 `pair_preimage_singleton`

English:
theorem pair_preimage_singleton
  given: (f : α ->ₛ β) (g : α ->ₛ γ) (b : β) (c : γ)
  proof: by
  rw [← singleton_prod_singleton]
  exact pair_preimage _ _ _ _

中文:
定理 pair_preimage_singleton
  条件: (f : α ->ₛ β) (g : α ->ₛ γ) (b : β) (c : γ)
  证明: by
  rw [← singleton_prod_singleton]
  exact pair_preimage _ _ _ _

Depends on / 依赖: pair_preimage, singleton_prod_singleton
-/
theorem pair_preimage_singleton (f : α ->ₛ β) (g : α ->ₛ γ) (b : β) (c : γ) :
    pair f g ⁻¹' {(b, c)} = f ⁻¹' {b} inter g ⁻¹' {c} := by
  rw [← singleton_prod_singleton]
  exact pair_preimage _ _ _ _

/--
theorem `map_fst_pair` / 定理 `map_fst_pair`

English:
theorem map_fst_pair
  given: (f : α ->ₛ β) (g : α ->ₛ γ)
  statement: (f.pair g).map Prod.fst = f
  proof: rfl

中文:
定理 map_fst_pair
  条件: (f : α ->ₛ β) (g : α ->ₛ γ)
  结论: (f.pair g).map Prod.fst = f
  证明: rfl
-/
@[simp] theorem map_fst_pair (f : α ->ₛ β) (g : α ->ₛ γ) : (f.pair g).map Prod.fst = f := rfl
/--
theorem `map_snd_pair` / 定理 `map_snd_pair`

English:
theorem map_snd_pair
  given: (f : α ->ₛ β) (g : α ->ₛ γ)
  statement: (f.pair g).map Prod.snd = g
  proof: rfl

@[simp]

中文:
定理 map_snd_pair
  条件: (f : α ->ₛ β) (g : α ->ₛ γ)
  结论: (f.pair g).map Prod.snd = g
  证明: rfl

@[simp]
-/
@[simp] theorem map_snd_pair (f : α ->ₛ β) (g : α ->ₛ γ) : (f.pair g).map Prod.snd = g := rfl

@[simp]
/--
theorem `bind_const` / 定理 `bind_const`

English:
theorem bind_const
  given: (f : α ->ₛ β)
  statement: f.bind (const α) = f
  proof: by ext; simp

@[to_additive]

中文:
定理 bind_const
  条件: (f : α ->ₛ β)
  结论: f.bind (const α) = f
  证明: by ext; simp

@[to_additive]
-/
theorem bind_const (f : α ->ₛ β) : f.bind (const α) = f := by ext; simp

@[to_additive]
/--
Instance `instOne` / 实例 `instOne`

English:
instance instOne
  signature: [One β]
  body: ⟨const α 1⟩

@[to_additive]

中文:
实例 instOne
  签名: [One β]
  定义体: ⟨const α 1⟩

@[to_additive]
-/
instance instOne [One β] : One (α ->ₛ β) :=
  ⟨const α 1⟩

@[to_additive]
/--
Instance `instMul` / 实例 `instMul`

English:
instance instMul
  signature: [Mul β]
  body: ⟨fun f g => (f.map (· * ·)).seq g⟩

@[to_additive]

中文:
实例 instMul
  签名: [Mul β]
  定义体: ⟨fun f g => (f.map (· * ·)).seq g⟩

@[to_additive]

Depends on / 依赖: f.map
-/
instance instMul [Mul β] : Mul (α ->ₛ β) :=
  ⟨fun f g => (f.map (· * ·)).seq g⟩

@[to_additive]
/--
Instance `instDiv` / 实例 `instDiv`

English:
instance instDiv
  signature: [Div β]
  body: ⟨fun f g => (f.map (· / ·)).seq g⟩

@[to_additive]

中文:
实例 instDiv
  签名: [Div β]
  定义体: ⟨fun f g => (f.map (· / ·)).seq g⟩

@[to_additive]

Depends on / 依赖: f.map
-/
instance instDiv [Div β] : Div (α ->ₛ β) :=
  ⟨fun f g => (f.map (· / ·)).seq g⟩

@[to_additive]
/--
Instance `instInv` / 实例 `instInv`

English:
instance instInv
  signature: [Inv β]
  body: ⟨fun f => f.map Inv.inv⟩

中文:
实例 instInv
  签名: [Inv β]
  定义体: ⟨fun f => f.map Inv.inv⟩

Depends on / 依赖: Inv.inv, f.map
-/
instance instInv [Inv β] : Inv (α ->ₛ β) :=
  ⟨fun f => f.map Inv.inv⟩

/--
Instance `instSup` / 实例 `instSup`

English:
instance instSup
  signature: [Max β]
  body: ⟨fun f g => (f.map (· ⊔ ·)).seq g⟩

中文:
实例 instSup
  签名: [Max β]
  定义体: ⟨fun f g => (f.map (· ⊔ ·)).seq g⟩

Depends on / 依赖: f.map
-/
instance instSup [Max β] : Max (α ->ₛ β) :=
  ⟨fun f g => (f.map (· ⊔ ·)).seq g⟩

/--
Instance `instInf` / 实例 `instInf`

English:
instance instInf
  signature: [Min β]
  body: ⟨fun f g => (f.map (· ⊓ ·)).seq g⟩

中文:
实例 instInf
  签名: [Min β]
  定义体: ⟨fun f g => (f.map (· ⊓ ·)).seq g⟩

Depends on / 依赖: f.map
-/
instance instInf [Min β] : Min (α ->ₛ β) :=
  ⟨fun f g => (f.map (· ⊓ ·)).seq g⟩

/--
Instance `instLE` / 实例 `instLE`

English:
instance instLE
  signature: [LE β]
  body: ⟨fun f g => forall a, f a <= g a⟩

@[to_additive (attr := simp)]

中文:
实例 instLE
  签名: [LE β]
  定义体: ⟨fun f g => forall a, f a <= g a⟩

@[to_additive (attr := simp)]
-/
instance instLE [LE β] : LE (α ->ₛ β) :=
  ⟨fun f g => forall a, f a <= g a⟩

@[to_additive (attr := simp)]
/--
theorem `const_one` / 定理 `const_one`

English:
theorem const_one
  given: [One β]
  statement: const α (1 : β) = 1
  proof: rfl

@[to_additive (attr := simp, norm_cast)]

中文:
定理 const_one
  条件: [One β]
  结论: const α (1 : β) = 1
  证明: rfl

@[to_additive (attr := simp, norm_cast)]
-/
theorem const_one [One β] : const α (1 : β) = 1 :=
  rfl

@[to_additive (attr := simp, norm_cast)]
/--
theorem `coe_one` / 定理 `coe_one`

English:
theorem coe_one
  given: [One β]
  statement: ⇑(1 : α ->ₛ β) = 1
  proof: rfl

@[to_additive (attr := simp, norm_cast)]

中文:
定理 coe_one
  条件: [One β]
  结论: ⇑(1 : α ->ₛ β) = 1
  证明: rfl

@[to_additive (attr := simp, norm_cast)]
-/
theorem coe_one [One β] : ⇑(1 : α ->ₛ β) = 1 :=
  rfl

@[to_additive (attr := simp, norm_cast)]
/--
theorem `coe_mul` / 定理 `coe_mul`

English:
theorem coe_mul
  given: [Mul β] (f g : α ->ₛ β)
  statement: ⇑(f * g) = ⇑f * ⇑g
  proof: rfl

@[to_additive (attr := simp, norm_cast)]

中文:
定理 coe_mul
  条件: [Mul β] (f g : α ->ₛ β)
  结论: ⇑(f * g) = ⇑f * ⇑g
  证明: rfl

@[to_additive (attr := simp, norm_cast)]
-/
theorem coe_mul [Mul β] (f g : α ->ₛ β) : ⇑(f * g) = ⇑f * ⇑g :=
  rfl

@[to_additive (attr := simp, norm_cast)]
/--
theorem `coe_inv` / 定理 `coe_inv`

English:
theorem coe_inv
  given: [Inv β] (f : α ->ₛ β)
  statement: ⇑(f⁻¹) = (⇑f)⁻¹
  proof: rfl

@[to_additive (attr := simp, norm_cast)]

中文:
定理 coe_inv
  条件: [Inv β] (f : α ->ₛ β)
  结论: ⇑(f⁻¹) = (⇑f)⁻¹
  证明: rfl

@[to_additive (attr := simp, norm_cast)]
-/
theorem coe_inv [Inv β] (f : α ->ₛ β) : ⇑(f⁻¹) = (⇑f)⁻¹ :=
  rfl

@[to_additive (attr := simp, norm_cast)]
/--
theorem `coe_div` / 定理 `coe_div`

English:
theorem coe_div
  given: [Div β] (f g : α ->ₛ β)
  statement: ⇑(f / g) = ⇑f / ⇑g
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_div
  条件: [Div β] (f g : α ->ₛ β)
  结论: ⇑(f / g) = ⇑f / ⇑g
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_div [Div β] (f g : α ->ₛ β) : ⇑(f / g) = ⇑f / ⇑g :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_sup` / 定理 `coe_sup`

English:
theorem coe_sup
  given: [Max β] (f g : α ->ₛ β)
  statement: ⇑(f ⊔ g) = ⇑f ⊔ ⇑g
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_sup
  条件: [Max β] (f g : α ->ₛ β)
  结论: ⇑(f ⊔ g) = ⇑f ⊔ ⇑g
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_sup [Max β] (f g : α ->ₛ β) : ⇑(f ⊔ g) = ⇑f ⊔ ⇑g :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_inf` / 定理 `coe_inf`

English:
theorem coe_inf
  given: [Min β] (f g : α ->ₛ β)
  statement: ⇑(f ⊓ g) = ⇑f ⊓ ⇑g
  proof: rfl

@[to_additive]

中文:
定理 coe_inf
  条件: [Min β] (f g : α ->ₛ β)
  结论: ⇑(f ⊓ g) = ⇑f ⊓ ⇑g
  证明: rfl

@[to_additive]
-/
theorem coe_inf [Min β] (f g : α ->ₛ β) : ⇑(f ⊓ g) = ⇑f ⊓ ⇑g :=
  rfl

@[to_additive]
/--
theorem `mul_apply` / 定理 `mul_apply`

English:
theorem mul_apply
  given: [Mul β] (f g : α ->ₛ β) (a : α)
  statement: (f * g) a = f a * g a
  proof: rfl

@[to_additive]

中文:
定理 mul_apply
  条件: [Mul β] (f g : α ->ₛ β) (a : α)
  结论: (f * g) a = f a * g a
  证明: rfl

@[to_additive]
-/
theorem mul_apply [Mul β] (f g : α ->ₛ β) (a : α) : (f * g) a = f a * g a :=
  rfl

@[to_additive]
/--
theorem `div_apply` / 定理 `div_apply`

English:
theorem div_apply
  given: [Div β] (f g : α ->ₛ β) (x : α)
  statement: (f / g) x = f x / g x
  proof: rfl

@[to_additive]

中文:
定理 div_apply
  条件: [Div β] (f g : α ->ₛ β) (x : α)
  结论: (f / g) x = f x / g x
  证明: rfl

@[to_additive]
-/
theorem div_apply [Div β] (f g : α ->ₛ β) (x : α) : (f / g) x = f x / g x :=
  rfl

@[to_additive]
/--
theorem `inv_apply` / 定理 `inv_apply`

English:
theorem inv_apply
  given: [Inv β] (f : α ->ₛ β) (x : α)
  statement: f⁻¹ x = (f x)⁻¹
  proof: rfl

中文:
定理 inv_apply
  条件: [Inv β] (f : α ->ₛ β) (x : α)
  结论: f⁻¹ x = (f x)⁻¹
  证明: rfl
-/
theorem inv_apply [Inv β] (f : α ->ₛ β) (x : α) : f⁻¹ x = (f x)⁻¹ :=
  rfl

/--
theorem `sup_apply` / 定理 `sup_apply`

English:
theorem sup_apply
  given: [Max β] (f g : α ->ₛ β) (a : α)
  statement: (f ⊔ g) a = f a ⊔ g a
  proof: rfl

中文:
定理 sup_apply
  条件: [Max β] (f g : α ->ₛ β) (a : α)
  结论: (f ⊔ g) a = f a ⊔ g a
  证明: rfl
-/
theorem sup_apply [Max β] (f g : α ->ₛ β) (a : α) : (f ⊔ g) a = f a ⊔ g a :=
  rfl

/--
theorem `inf_apply` / 定理 `inf_apply`

English:
theorem inf_apply
  given: [Min β] (f g : α ->ₛ β) (a : α)
  statement: (f ⊓ g) a = f a ⊓ g a
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 inf_apply
  条件: [Min β] (f g : α ->ₛ β) (a : α)
  结论: (f ⊓ g) a = f a ⊓ g a
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem inf_apply [Min β] (f g : α ->ₛ β) (a : α) : (f ⊓ g) a = f a ⊓ g a :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `range_one` / 定理 `range_one`

English:
theorem range_one
  given: [Nonempty α] [One β]
  statement: (1 : α ->ₛ β).range = {1}
  proof: Finset.ext fun x => by simp

@[simp]

中文:
定理 range_one
  条件: [Nonempty α] [One β]
  结论: (1 : α ->ₛ β).range = {1}
  证明: Finset.ext fun x => by simp

@[simp]

Depends on / 依赖: Finset, Finset.ext
-/
theorem range_one [Nonempty α] [One β] : (1 : α ->ₛ β).range = {1} :=
  Finset.ext fun x => by simp

@[simp]
/--
theorem `range_eq_empty_of_isEmpty` / 定理 `range_eq_empty_of_isEmpty`

English:
theorem range_eq_empty_of_isEmpty
  given: {β} [hα : IsEmpty α] (f : α ->ₛ β)
  statement: f.range = ∅
  proof: by
  ext
  simp

中文:
定理 range_eq_empty_of_isEmpty
  条件: {β} [hα : IsEmpty α] (f : α ->ₛ β)
  结论: f.range = ∅
  证明: by
  ext
  simp
-/
theorem range_eq_empty_of_isEmpty {β} [hα : IsEmpty α] (f : α ->ₛ β) : f.range = ∅ := by
  ext
  simp

/--
theorem `eq_zero_of_mem_range_zero` / 定理 `eq_zero_of_mem_range_zero`

English:
theorem eq_zero_of_mem_range_zero
  given: [Zero β]
  statement: forall {y : β}, y in (0 : α ->ₛ β).range -> y = 0
  proof: @(forall_mem_range.2 fun _ => rfl)

@[to_additive]

中文:
定理 eq_zero_of_mem_range_zero
  条件: [Zero β]
  结论: 对任意 {y : β}, y in (0 : α ->ₛ β).range -> y = 0
  证明: @(forall_mem_range.2 fun _ => rfl)

@[to_additive]

Depends on / 依赖: forall_mem_range
-/
theorem eq_zero_of_mem_range_zero [Zero β] : forall {y : β}, y in (0 : α ->ₛ β).range -> y = 0 :=
  @(forall_mem_range.2 fun _ => rfl)

@[to_additive]
/--
theorem `mul_eq_map₂` / 定理 `mul_eq_map₂`

English:
theorem mul_eq_map₂
  given: [Mul β] (f g : α ->ₛ β)
  statement: f * g = (pair f g).map fun p : β × β => p.1 * p.2
  proof: rfl

中文:
定理 mul_eq_map₂
  条件: [Mul β] (f g : α ->ₛ β)
  结论: f * g = (pair f g).map fun p : β × β => p.1 * p.2
  证明: rfl
-/
theorem mul_eq_map₂ [Mul β] (f g : α ->ₛ β) : f * g = (pair f g).map fun p : β × β => p.1 * p.2 :=
  rfl

/--
theorem `sup_eq_map₂` / 定理 `sup_eq_map₂`

English:
theorem sup_eq_map₂
  given: [Max β] (f g : α ->ₛ β)
  statement: f ⊔ g = (pair f g).map fun p : β × β => p.1 ⊔ p.2
  proof: rfl

@[to_additive]

中文:
定理 sup_eq_map₂
  条件: [Max β] (f g : α ->ₛ β)
  结论: f ⊔ g = (pair f g).map fun p : β × β => p.1 ⊔ p.2
  证明: rfl

@[to_additive]
-/
theorem sup_eq_map₂ [Max β] (f g : α ->ₛ β) : f ⊔ g = (pair f g).map fun p : β × β => p.1 ⊔ p.2 :=
  rfl

@[to_additive]
/--
theorem `const_mul_eq_map` / 定理 `const_mul_eq_map`

English:
theorem const_mul_eq_map
  given: [Mul β] (f : α ->ₛ β) (b : β)
  statement: const α b * f = f.map fun a => b * a
  proof: rfl

@[to_additive]

中文:
定理 const_mul_eq_map
  条件: [Mul β] (f : α ->ₛ β) (b : β)
  结论: const α b * f = f.map fun a => b * a
  证明: rfl

@[to_additive]
-/
theorem const_mul_eq_map [Mul β] (f : α ->ₛ β) (b : β) : const α b * f = f.map fun a => b * a :=
  rfl

@[to_additive]
/--
theorem `map_mul` / 定理 `map_mul`

English:
theorem map_mul
  given: [Mul β] [Mul γ] {g : β -> γ} (hg : forall x y, g (x * y) = g x * g y) (f₁ f₂ : α ->ₛ β)
  proof: ext fun _ => hg _ _

中文:
定理 map_mul
  条件: [Mul β] [Mul γ] {g : β -> γ} (hg : 对任意 x y, g (x * y) = g x * g y) (f₁ f₂ : α ->ₛ β)
  证明: ext fun _ => hg _ _
-/
theorem map_mul [Mul β] [Mul γ] {g : β -> γ} (hg : forall x y, g (x * y) = g x * g y) (f₁ f₂ : α ->ₛ β) :
    (f₁ * f₂).map g = f₁.map g * f₂.map g :=
  ext fun _ => hg _ _

variable {K : Type*}

@[to_additive]
/--
Instance `instSMul` / 实例 `instSMul`

English:
instance instSMul
  signature: [SMul K β]
  body: ⟨fun k f => f.map (k • ·)⟩

@[to_additive (attr := simp)]

中文:
实例 instSMul
  签名: [SMul K β]
  定义体: ⟨fun k f => f.map (k • ·)⟩

@[to_additive (attr := simp)]

Depends on / 依赖: f.map
-/
instance instSMul [SMul K β] : SMul K (α ->ₛ β) :=
  ⟨fun k f => f.map (k • ·)⟩

@[to_additive (attr := simp)]
/--
theorem `coe_smul` / 定理 `coe_smul`

English:
theorem coe_smul
  given: [SMul K β] (c : K) (f : α ->ₛ β)
  statement: ⇑(c • f) = c • ⇑f
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 coe_smul
  条件: [SMul K β] (c : K) (f : α ->ₛ β)
  结论: ⇑(c • f) = c • ⇑f
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem coe_smul [SMul K β] (c : K) (f : α ->ₛ β) : ⇑(c • f) = c • ⇑f :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `smul_apply` / 定理 `smul_apply`

English:
theorem smul_apply
  given: [SMul K β] (k : K) (f : α ->ₛ β) (a : α)
  statement: (k • f) a = k • f a
  proof: rfl

中文:
定理 smul_apply
  条件: [SMul K β] (k : K) (f : α ->ₛ β) (a : α)
  结论: (k • f) a = k • f a
  证明: rfl
-/
theorem smul_apply [SMul K β] (k : K) (f : α ->ₛ β) (a : α) : (k • f) a = k • f a :=
  rfl

/--
Instance `hasNatSMul` / 实例 `hasNatSMul`

English:
instance hasNatSMul
  signature: [AddMonoid β]
  body: inferInstance

@[to_additive existing hasNatSMul]

中文:
实例 hasNatSMul
  签名: [AddMonoid β]
  定义体: inferInstance

@[to_additive existing hasNatSMul]
-/
instance hasNatSMul [AddMonoid β] : SMul Nat (α ->ₛ β) := inferInstance

@[to_additive existing hasNatSMul]
/--
Instance `hasNatPow` / 实例 `hasNatPow`

English:
instance hasNatPow
  signature: [Monoid β]
  body: ⟨fun f n => f.map (· ^ n)⟩

@[simp]

中文:
实例 hasNatPow
  签名: [Monoid β]
  定义体: ⟨fun f n => f.map (· ^ n)⟩

@[simp]

Depends on / 依赖: f.map
-/
instance hasNatPow [Monoid β] : Pow (α ->ₛ β) Nat :=
  ⟨fun f n => f.map (· ^ n)⟩

@[simp]
/--
theorem `coe_pow` / 定理 `coe_pow`

English:
theorem coe_pow
  given: [Monoid β] (f : α ->ₛ β) (n : Nat)
  statement: ⇑(f ^ n) = (⇑f) ^ n
  proof: rfl

中文:
定理 coe_pow
  条件: [Monoid β] (f : α ->ₛ β) (n : 自然数)
  结论: ⇑(f ^ n) = (⇑f) ^ n
  证明: rfl
-/
theorem coe_pow [Monoid β] (f : α ->ₛ β) (n : Nat) : ⇑(f ^ n) = (⇑f) ^ n :=
  rfl

/--
theorem `pow_apply` / 定理 `pow_apply`

English:
theorem pow_apply
  given: [Monoid β] (n : Nat) (f : α ->ₛ β) (a : α)
  statement: (f ^ n) a = f a ^ n
  proof: rfl

中文:
定理 pow_apply
  条件: [Monoid β] (n : 自然数) (f : α ->ₛ β) (a : α)
  结论: (f ^ n) a = f a ^ n
  证明: rfl
-/
theorem pow_apply [Monoid β] (n : Nat) (f : α ->ₛ β) (a : α) : (f ^ n) a = f a ^ n :=
  rfl

/--
Instance `hasIntPow` / 实例 `hasIntPow`

English:
instance hasIntPow
  signature: [DivInvMonoid β]
  body: ⟨fun f n => f.map (· ^ n)⟩

@[simp]

中文:
实例 hasIntPow
  签名: [DivInvMonoid β]
  定义体: ⟨fun f n => f.map (· ^ n)⟩

@[simp]

Depends on / 依赖: f.map
-/
instance hasIntPow [DivInvMonoid β] : Pow (α ->ₛ β) Int :=
  ⟨fun f n => f.map (· ^ n)⟩

@[simp]
/--
theorem `coe_zpow` / 定理 `coe_zpow`

English:
theorem coe_zpow
  given: [DivInvMonoid β] (f : α ->ₛ β) (z : Int)
  statement: ⇑(f ^ z) = (⇑f) ^ z
  proof: rfl

中文:
定理 coe_zpow
  条件: [DivInvMonoid β] (f : α ->ₛ β) (z : 整数)
  结论: ⇑(f ^ z) = (⇑f) ^ z
  证明: rfl
-/
theorem coe_zpow [DivInvMonoid β] (f : α ->ₛ β) (z : Int) : ⇑(f ^ z) = (⇑f) ^ z :=
  rfl

/--
theorem `zpow_apply` / 定理 `zpow_apply`

English:
theorem zpow_apply
  given: [DivInvMonoid β] (z : Int) (f : α ->ₛ β) (a : α)
  statement: (f ^ z) a = f a ^ z
  proof: rfl

中文:
定理 zpow_apply
  条件: [DivInvMonoid β] (z : 整数) (f : α ->ₛ β) (a : α)
  结论: (f ^ z) a = f a ^ z
  证明: rfl
-/
theorem zpow_apply [DivInvMonoid β] (z : Int) (f : α ->ₛ β) (a : α) : (f ^ z) a = f a ^ z :=
  rfl

-- TODO: work out how to generate these instances with `to_additive`, which gets confused by the
-- argument order swap between `coe_smul` and `coe_pow`.
section Additive

/--
Instance `instAddMonoid` / 实例 `instAddMonoid`

English:
instance instAddMonoid
  signature: [AddMonoid β]
  body: fast_instance% Function.Injective.addMonoid (fun f => show α -> β from f) coe_injective coe_zero
    coe_add fun _ _ => coe_smul _ _

中文:
实例 instAddMonoid
  签名: [AddMonoid β]
  定义体: fast_instance% Function.Injective.addMonoid (fun f => show α -> β from f) coe_injective coe_zero
    coe_add fun _ _ => coe_smul _ _

Depends on / 依赖: Function, Function.Injective.addMonoid, Injective, addMonoid, coe_add, coe_injective, coe_smul, coe_zero, fast_instance
-/
instance instAddMonoid [AddMonoid β] : AddMonoid (α ->ₛ β) :=
  fast_instance% Function.Injective.addMonoid (fun f => show α -> β from f) coe_injective coe_zero
    coe_add fun _ _ => coe_smul _ _

/--
Instance `instAddCommMonoid` / 实例 `instAddCommMonoid`

English:
instance instAddCommMonoid
  signature: [AddCommMonoid β]
  body: fast_instance% Function.Injective.addCommMonoid (fun f => show α -> β from f)
    coe_injective coe_zero coe_add fun _ _ => coe_smul _ _

中文:
实例 instAddCommMonoid
  签名: [AddCommMonoid β]
  定义体: fast_instance% Function.Injective.addCommMonoid (fun f => show α -> β from f)
    coe_injective coe_zero coe_add fun _ _ => coe_smul _ _

Depends on / 依赖: Function, Function.Injective.addCommMonoid, Injective, addCommMonoid, coe_add, coe_injective, coe_smul, coe_zero, fast_instance
-/
instance instAddCommMonoid [AddCommMonoid β] : AddCommMonoid (α ->ₛ β) :=
  fast_instance% Function.Injective.addCommMonoid (fun f => show α -> β from f)
    coe_injective coe_zero coe_add fun _ _ => coe_smul _ _

/--
Instance `instAddGroup` / 实例 `instAddGroup`

English:
instance instAddGroup
  signature: [AddGroup β]
  body: Function.Injective.addGroup (fun f => show α -> β from f) coe_injective coe_zero coe_add coe_neg
    coe_sub (fun _ _ => coe_smul _ _) fun _ _ => coe_smul _ _

中文:
实例 instAddGroup
  签名: [AddGroup β]
  定义体: Function.Injective.addGroup (fun f => show α -> β from f) coe_injective coe_zero coe_add coe_neg
    coe_sub (fun _ _ => coe_smul _ _) fun _ _ => coe_smul _ _

Depends on / 依赖: Function, Function.Injective.addGroup, Injective, addGroup, coe_add, coe_injective, coe_neg, coe_smul, coe_sub, coe_zero
-/
instance instAddGroup [AddGroup β] : AddGroup (α ->ₛ β) :=
  Function.Injective.addGroup (fun f => show α -> β from f) coe_injective coe_zero coe_add coe_neg
    coe_sub (fun _ _ => coe_smul _ _) fun _ _ => coe_smul _ _

/--
Instance `instAddCommGroup` / 实例 `instAddCommGroup`

English:
instance instAddCommGroup
  signature: [AddCommGroup β]
  body: fast_instance% Function.Injective.addCommGroup (fun f => show α -> β from f) coe_injective
    coe_zero coe_add coe_neg coe_sub (fun _ _ => coe_smul _ _) fun _ _ => coe_smul _ _

中文:
实例 instAddCommGroup
  签名: [AddCommGroup β]
  定义体: fast_instance% Function.Injective.addCommGroup (fun f => show α -> β from f) coe_injective
    coe_zero coe_add coe_neg coe_sub (fun _ _ => coe_smul _ _) fun _ _ => coe_smul _ _

Depends on / 依赖: Function, Function.Injective.addCommGroup, Injective, addCommGroup, coe_add, coe_injective, coe_neg, coe_smul, coe_sub, coe_zero, fast_instance
-/
instance instAddCommGroup [AddCommGroup β] : AddCommGroup (α ->ₛ β) :=
  fast_instance% Function.Injective.addCommGroup (fun f => show α -> β from f) coe_injective
    coe_zero coe_add coe_neg coe_sub (fun _ _ => coe_smul _ _) fun _ _ => coe_smul _ _

end Additive

@[to_additive existing]
/--
Instance `instMonoid` / 实例 `instMonoid`

English:
instance instMonoid
  signature: [Monoid β]
  body: fast_instance% Function.Injective.monoid (fun f => show α -> β from f) coe_injective coe_one
    coe_mul coe_pow

@[to_additive existing]

中文:
实例 instMonoid
  签名: [Monoid β]
  定义体: fast_instance% Function.Injective.monoid (fun f => show α -> β from f) coe_injective coe_one
    coe_mul coe_pow

@[to_additive existing]

Depends on / 依赖: Function, Function.Injective.monoid, Injective, coe_injective, coe_mul, coe_one, coe_pow, fast_instance, monoid
-/
instance instMonoid [Monoid β] : Monoid (α ->ₛ β) :=
  fast_instance% Function.Injective.monoid (fun f => show α -> β from f) coe_injective coe_one
    coe_mul coe_pow

@[to_additive existing]
/--
Instance `instCommMonoid` / 实例 `instCommMonoid`

English:
instance instCommMonoid
  signature: [CommMonoid β]
  body: fast_instance% Function.Injective.commMonoid (fun f => show α -> β from f) coe_injective coe_one
    coe_mul coe_pow

@[to_additive existing]

中文:
实例 instCommMonoid
  签名: [CommMonoid β]
  定义体: fast_instance% Function.Injective.commMonoid (fun f => show α -> β from f) coe_injective coe_one
    coe_mul coe_pow

@[to_additive existing]

Depends on / 依赖: Function, Function.Injective.commMonoid, Injective, coe_injective, coe_mul, coe_one, coe_pow, commMonoid, fast_instance
-/
instance instCommMonoid [CommMonoid β] : CommMonoid (α ->ₛ β) :=
  fast_instance% Function.Injective.commMonoid (fun f => show α -> β from f) coe_injective coe_one
    coe_mul coe_pow

@[to_additive existing]
/--
Instance `instGroup` / 实例 `instGroup`

English:
instance instGroup
  signature: [Group β]
  body: fast_instance% Function.Injective.group (fun f => show α -> β from f) coe_injective coe_one
    coe_mul coe_inv coe_div coe_pow coe_zpow

@[to_additive existing]

中文:
实例 instGroup
  签名: [Group β]
  定义体: fast_instance% Function.Injective.group (fun f => show α -> β from f) coe_injective coe_one
    coe_mul coe_inv coe_div coe_pow coe_zpow

@[to_additive existing]

Depends on / 依赖: Function, Function.Injective.group, Injective, coe_div, coe_injective, coe_inv, coe_mul, coe_one, coe_pow, coe_zpow, fast_instance
-/
instance instGroup [Group β] : Group (α ->ₛ β) :=
  fast_instance% Function.Injective.group (fun f => show α -> β from f) coe_injective coe_one
    coe_mul coe_inv coe_div coe_pow coe_zpow

@[to_additive existing]
/--
Instance `instCommGroup` / 实例 `instCommGroup`

English:
instance instCommGroup
  signature: [CommGroup β]
  body: fast_instance% Function.Injective.commGroup (fun f => show α -> β from f) coe_injective coe_one
    coe_mul coe_inv coe_div coe_pow coe_zpow

中文:
实例 instCommGroup
  签名: [CommGroup β]
  定义体: fast_instance% Function.Injective.commGroup (fun f => show α -> β from f) coe_injective coe_one
    coe_mul coe_inv coe_div coe_pow coe_zpow

Depends on / 依赖: Function, Function.Injective.commGroup, Injective, coe_div, coe_injective, coe_inv, coe_mul, coe_one, coe_pow, coe_zpow, commGroup, fast_instance
-/
instance instCommGroup [CommGroup β] : CommGroup (α ->ₛ β) :=
  fast_instance% Function.Injective.commGroup (fun f => show α -> β from f) coe_injective coe_one
    coe_mul coe_inv coe_div coe_pow coe_zpow

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Monoid
  signature: K] [MulAction K β] : MulAction K (α ->ₛ β)
  body: fast_instance% Function.Injective.mulAction (fun f => show α -> β from f) coe_injective coe_smul

中文:
实例 [Monoid
  签名: K] [MulAction K β] : MulAction K (α ->ₛ β)
  定义体: fast_instance% Function.Injective.mulAction (fun f => show α -> β from f) coe_injective coe_smul

Depends on / 依赖: Function, Function.Injective.mulAction, Injective, coe_injective, coe_smul, fast_instance, mulAction
-/
instance [Monoid K] [MulAction K β] : MulAction K (α ->ₛ β) :=
  fast_instance% Function.Injective.mulAction (fun f => show α -> β from f) coe_injective coe_smul

/--
Instance `instModule` / 实例 `instModule`

English:
instance instModule
  signature: [Semiring K] [AddCommMonoid β] [Module K β]
  body: fast_instance% Function.Injective.module K ⟨⟨fun f => show α -> β from f, coe_zero⟩, coe_add⟩
    coe_injective coe_smul

中文:
实例 instModule
  签名: [Semiring K] [AddCommMonoid β] [Module K β]
  定义体: fast_instance% Function.Injective.module K ⟨⟨fun f => show α -> β from f, coe_zero⟩, coe_add⟩
    coe_injective coe_smul

Depends on / 依赖: Function, Function.Injective.module, Injective, coe_add, coe_injective, coe_smul, coe_zero, fast_instance, module
-/
instance instModule [Semiring K] [AddCommMonoid β] [Module K β] : Module K (α ->ₛ β) :=
  fast_instance% Function.Injective.module K ⟨⟨fun f => show α -> β from f, coe_zero⟩, coe_add⟩
    coe_injective coe_smul

/--
theorem `smul_eq_map` / 定理 `smul_eq_map`

English:
theorem smul_eq_map
  given: [SMul K β] (k : K) (f : α ->ₛ β)
  statement: k • f = f.map (k • ·)
  proof: rfl

中文:
定理 smul_eq_map
  条件: [SMul K β] (k : K) (f : α ->ₛ β)
  结论: k • f = f.map (k • ·)
  证明: rfl
-/
theorem smul_eq_map [SMul K β] (k : K) (f : α ->ₛ β) : k • f = f.map (k • ·) :=
  rfl

/--
lemma `smul_const` / 引理 `smul_const`

English:
lemma smul_const
  given: [SMul K β] (k : K) (b : β)
  proof: ext fun _ => rfl

中文:
引理 smul_const
  条件: [SMul K β] (k : K) (b : β)
  证明: ext fun _ => rfl
-/
lemma smul_const [SMul K β] (k : K) (b : β) :
    (k • const α b : α ->ₛ β) = const α (k • b) := ext fun _ => rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonUnitalNonAssocSemiring
  signature: β] : NonUnitalNonAssocSemiring (α ->ₛ β)
  body: fast_instance% Function.Injective.nonUnitalNonAssocSemiring (fun f => show α -> β from f)
    coe_injective coe_zero coe_add coe_mul coe_smul

中文:
实例 [NonUnitalNonAssocSemiring
  签名: β] : NonUnitalNonAssocSemiring (α ->ₛ β)
  定义体: fast_instance% Function.Injective.nonUnitalNonAssocSemiring (fun f => show α -> β from f)
    coe_injective coe_zero coe_add coe_mul coe_smul

Depends on / 依赖: Function, Function.Injective.nonUnitalNonAssocSemiring, Injective, coe_add, coe_injective, coe_mul, coe_smul, coe_zero, fast_instance, nonUnitalNonAssocSemiring
-/
instance [NonUnitalNonAssocSemiring β] : NonUnitalNonAssocSemiring (α ->ₛ β) :=
  fast_instance% Function.Injective.nonUnitalNonAssocSemiring (fun f => show α -> β from f)
    coe_injective coe_zero coe_add coe_mul coe_smul

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonUnitalSemiring
  signature: β] : NonUnitalSemiring (α ->ₛ β)
  body: fast_instance% Function.Injective.nonUnitalSemiring (fun f => show α -> β from f)
    SimpleFunc.coe_injective coe_zero coe_add coe_mul coe_smul

中文:
实例 [NonUnitalSemiring
  签名: β] : NonUnitalSemiring (α ->ₛ β)
  定义体: fast_instance% Function.Injective.nonUnitalSemiring (fun f => show α -> β from f)
    SimpleFunc.coe_injective coe_zero coe_add coe_mul coe_smul

Depends on / 依赖: Function, Function.Injective.nonUnitalSemiring, Injective, SimpleFunc, SimpleFunc.coe_injective, coe_add, coe_injective, coe_mul, coe_smul, coe_zero, fast_instance, nonUnitalSemiring
-/
instance [NonUnitalSemiring β] : NonUnitalSemiring (α ->ₛ β) :=
  fast_instance% Function.Injective.nonUnitalSemiring (fun f => show α -> β from f)
    SimpleFunc.coe_injective coe_zero coe_add coe_mul coe_smul

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NatCast
  signature: β] : NatCast (α ->ₛ β) where
  body: const _ (NatCast.natCast n)

@[simp, norm_cast]

中文:
实例 [NatCast
  签名: β] : 自然数Cast (α ->ₛ β) where
  定义体: const _ (NatCast.natCast n)

@[simp, norm_cast]

Depends on / 依赖: I.bot_lt_of_maximal, I.finiteQuotientOfFreeOfNeBot, NatCast, NatCast.natCast, RingOfIntegers, RingOfIntegers.not_isField, bot_lt_of_maximal, finiteQuotientOfFreeOfNeBot, natCast, not_isField
-/
instance [NatCast β] : NatCast (α ->ₛ β) where
  natCast n := const _ (NatCast.natCast n)

@[simp, norm_cast]
/--
lemma `coe_natCast` / 引理 `coe_natCast`

English:
lemma coe_natCast
  given: [NatCast β] (n : Nat)
  proof: rfl

中文:
引理 coe_natCast
  条件: [自然数Cast β] (n : 自然数)
  证明: rfl
-/
lemma coe_natCast [NatCast β] (n : Nat) :
    ⇑(↑n : α ->ₛ β) = fun _ => ↑n := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonAssocSemiring
  signature: β] : NonAssocSemiring (α ->ₛ β)
  body: fast_instance% Function.Injective.nonAssocSemiring (fun f => show α -> β from f)
    coe_injective coe_zero coe_one coe_add coe_mul coe_smul coe_natCast

中文:
实例 [NonAssocSemiring
  签名: β] : NonAssocSemiring (α ->ₛ β)
  定义体: fast_instance% Function.Injective.nonAssocSemiring (fun f => show α -> β from f)
    coe_injective coe_zero coe_one coe_add coe_mul coe_smul coe_natCast

Depends on / 依赖: Function, Function.Injective.nonAssocSemiring, Injective, coe_add, coe_injective, coe_mul, coe_natCast, coe_one, coe_smul, coe_zero, fast_instance, nonAssocSemiring
-/
instance [NonAssocSemiring β] : NonAssocSemiring (α ->ₛ β) :=
  fast_instance% Function.Injective.nonAssocSemiring (fun f => show α -> β from f)
    coe_injective coe_zero coe_one coe_add coe_mul coe_smul coe_natCast

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IntCast
  signature: β] : IntCast (α ->ₛ β) where
  body: const _ (IntCast.intCast n)

@[simp, norm_cast]

中文:
实例 [IntCast
  签名: β] : 整数Cast (α ->ₛ β) where
  定义体: const _ (IntCast.intCast n)

@[simp, norm_cast]

Depends on / 依赖: IntCast, IntCast.intCast, intCast
-/
instance [IntCast β] : IntCast (α ->ₛ β) where
  intCast n := const _ (IntCast.intCast n)

@[simp, norm_cast]
/--
lemma `coe_intCast` / 引理 `coe_intCast`

English:
lemma coe_intCast
  given: [IntCast β] (n : Int)
  proof: rfl

中文:
引理 coe_intCast
  条件: [整数Cast β] (n : 整数)
  证明: rfl
-/
lemma coe_intCast [IntCast β] (n : Int) :
    ⇑(↑n : α ->ₛ β) = fun _ => ↑n := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonAssocRing
  signature: β] : NonAssocRing (α ->ₛ β)
  body: fast_instance% Function.Injective.nonAssocRing (fun f => show α -> β from f) coe_injective
    coe_zero coe_one coe_add coe_mul coe_neg coe_sub coe_smul coe_smul coe_natCast coe_intCast

中文:
实例 [NonAssocRing
  签名: β] : NonAssocRing (α ->ₛ β)
  定义体: fast_instance% Function.Injective.nonAssocRing (fun f => show α -> β from f) coe_injective
    coe_zero coe_one coe_add coe_mul coe_neg coe_sub coe_smul coe_smul coe_natCast coe_intCast

Depends on / 依赖: Function, Function.Injective.nonAssocRing, Injective, coe_add, coe_injective, coe_intCast, coe_mul, coe_natCast, coe_neg, coe_one, coe_smul, coe_sub, coe_zero, fast_instance, nonAssocRing
-/
instance [NonAssocRing β] : NonAssocRing (α ->ₛ β) :=
  fast_instance% Function.Injective.nonAssocRing (fun f => show α -> β from f) coe_injective
    coe_zero coe_one coe_add coe_mul coe_neg coe_sub coe_smul coe_smul coe_natCast coe_intCast

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonUnitalCommSemiring
  signature: β] : NonUnitalCommSemiring (α ->ₛ β)
  body: fast_instance% Function.Injective.nonUnitalCommSemiring (fun f => show α -> β from f)
    coe_injective coe_zero coe_add coe_mul coe_smul

中文:
实例 [NonUnitalCommSemiring
  签名: β] : NonUnitalCommSemiring (α ->ₛ β)
  定义体: fast_instance% Function.Injective.nonUnitalCommSemiring (fun f => show α -> β from f)
    coe_injective coe_zero coe_add coe_mul coe_smul

Depends on / 依赖: Function, Function.Injective.nonUnitalCommSemiring, Injective, coe_add, coe_injective, coe_mul, coe_smul, coe_zero, fast_instance, nonUnitalCommSemiring
-/
instance [NonUnitalCommSemiring β] : NonUnitalCommSemiring (α ->ₛ β) :=
  fast_instance% Function.Injective.nonUnitalCommSemiring (fun f => show α -> β from f)
    coe_injective coe_zero coe_add coe_mul coe_smul

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CommSemiring
  signature: β] : CommSemiring (α ->ₛ β)
  body: fast_instance% Function.Injective.commSemiring (fun f => show α -> β from f)
    coe_injective coe_zero coe_one coe_add coe_mul coe_smul coe_pow coe_natCast

中文:
实例 [CommSemiring
  签名: β] : CommSemiring (α ->ₛ β)
  定义体: fast_instance% Function.Injective.commSemiring (fun f => show α -> β from f)
    coe_injective coe_zero coe_one coe_add coe_mul coe_smul coe_pow coe_natCast

Depends on / 依赖: Function, Function.Injective.commSemiring, Injective, coe_add, coe_injective, coe_mul, coe_natCast, coe_one, coe_pow, coe_smul, coe_zero, commSemiring, fast_instance
-/
instance [CommSemiring β] : CommSemiring (α ->ₛ β) :=
  fast_instance% Function.Injective.commSemiring (fun f => show α -> β from f)
    coe_injective coe_zero coe_one coe_add coe_mul coe_smul coe_pow coe_natCast

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonUnitalCommRing
  signature: β] : NonUnitalCommRing (α ->ₛ β)
  body: fast_instance% Function.Injective.nonUnitalCommRing (fun f => show α -> β from f)
    coe_injective coe_zero coe_add coe_mul coe_neg coe_sub coe_smul coe_smul

中文:
实例 [NonUnitalCommRing
  签名: β] : NonUnitalCommRing (α ->ₛ β)
  定义体: fast_instance% Function.Injective.nonUnitalCommRing (fun f => show α -> β from f)
    coe_injective coe_zero coe_add coe_mul coe_neg coe_sub coe_smul coe_smul

Depends on / 依赖: Function, Function.Injective.nonUnitalCommRing, Injective, coe_add, coe_injective, coe_mul, coe_neg, coe_smul, coe_sub, coe_zero, fast_instance, nonUnitalCommRing
-/
instance [NonUnitalCommRing β] : NonUnitalCommRing (α ->ₛ β) :=
  fast_instance% Function.Injective.nonUnitalCommRing (fun f => show α -> β from f)
    coe_injective coe_zero coe_add coe_mul coe_neg coe_sub coe_smul coe_smul

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CommRing
  signature: β] : CommRing (α ->ₛ β)
  body: fast_instance% Function.Injective.commRing (fun f => show α -> β from f) coe_injective coe_zero
    coe_one coe_add coe_mul coe_neg coe_sub coe_smul coe_smul coe_pow coe_natCast coe_intCast

中文:
实例 [CommRing
  签名: β] : CommRing (α ->ₛ β)
  定义体: fast_instance% Function.Injective.commRing (fun f => show α -> β from f) coe_injective coe_zero
    coe_one coe_add coe_mul coe_neg coe_sub coe_smul coe_smul coe_pow coe_natCast coe_intCast

Depends on / 依赖: Function, Function.Injective.commRing, Injective, coe_add, coe_injective, coe_intCast, coe_mul, coe_natCast, coe_neg, coe_one, coe_pow, coe_smul, coe_sub, coe_zero, commRing, fast_instance
-/
instance [CommRing β] : CommRing (α ->ₛ β) :=
  fast_instance% Function.Injective.commRing (fun f => show α -> β from f) coe_injective coe_zero
    coe_one coe_add coe_mul coe_neg coe_sub coe_smul coe_smul coe_pow coe_natCast coe_intCast

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Semiring
  signature: β] : Semiring (α ->ₛ β)
  body: fast_instance% Function.Injective.semiring (fun f => show α -> β from f) coe_injective coe_zero
    coe_one coe_add coe_mul coe_smul coe_pow coe_natCast

中文:
实例 [Semiring
  签名: β] : Semiring (α ->ₛ β)
  定义体: fast_instance% Function.Injective.semiring (fun f => show α -> β from f) coe_injective coe_zero
    coe_one coe_add coe_mul coe_smul coe_pow coe_natCast

Depends on / 依赖: Function, Function.Injective.semiring, Injective, coe_add, coe_injective, coe_mul, coe_natCast, coe_one, coe_pow, coe_smul, coe_zero, fast_instance, semiring
-/
instance [Semiring β] : Semiring (α ->ₛ β) :=
  fast_instance% Function.Injective.semiring (fun f => show α -> β from f) coe_injective coe_zero
    coe_one coe_add coe_mul coe_smul coe_pow coe_natCast

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonUnitalRing
  signature: β] : NonUnitalRing (α ->ₛ β)
  body: fast_instance% Function.Injective.nonUnitalRing (fun f => show α -> β from f) coe_injective
    coe_zero coe_add coe_mul coe_neg coe_sub coe_smul coe_smul

中文:
实例 [NonUnitalRing
  签名: β] : NonUnitalRing (α ->ₛ β)
  定义体: fast_instance% Function.Injective.nonUnitalRing (fun f => show α -> β from f) coe_injective
    coe_zero coe_add coe_mul coe_neg coe_sub coe_smul coe_smul

Depends on / 依赖: Function, Function.Injective.nonUnitalRing, Injective, coe_add, coe_injective, coe_mul, coe_neg, coe_smul, coe_sub, coe_zero, fast_instance, nonUnitalRing
-/
instance [NonUnitalRing β] : NonUnitalRing (α ->ₛ β) :=
  fast_instance% Function.Injective.nonUnitalRing (fun f => show α -> β from f) coe_injective
    coe_zero coe_add coe_mul coe_neg coe_sub coe_smul coe_smul

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Ring
  signature: β] : Ring (α ->ₛ β)
  body: fast_instance% Function.Injective.ring (fun f => show α -> β from f) coe_injective coe_zero
    coe_one coe_add coe_mul coe_neg coe_sub coe_smul coe_smul coe_pow coe_natCast coe_intCast

中文:
实例 [Ring
  签名: β] : Ring (α ->ₛ β)
  定义体: fast_instance% Function.Injective.ring (fun f => show α -> β from f) coe_injective coe_zero
    coe_one coe_add coe_mul coe_neg coe_sub coe_smul coe_smul coe_pow coe_natCast coe_intCast

Depends on / 依赖: Function, Function.Injective.ring, Injective, coe_add, coe_injective, coe_intCast, coe_mul, coe_natCast, coe_neg, coe_one, coe_pow, coe_smul, coe_sub, coe_zero, fast_instance
-/
instance [Ring β] : Ring (α ->ₛ β) :=
  fast_instance% Function.Injective.ring (fun f => show α -> β from f) coe_injective coe_zero
    coe_one coe_add coe_mul coe_neg coe_sub coe_smul coe_smul coe_pow coe_natCast coe_intCast

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: K γ] [SMul γ β] [SMul K β] [IsScalarTower K γ β] : IsScalarTower K γ (α ->ₛ β) where
  body: ext fun _ => smul_assoc ..

中文:
实例 [SMul
  签名: K γ] [SMul γ β] [SMul K β] [IsScalarTower K γ β] : IsScalarTower K γ (α ->ₛ β) where
  定义体: ext fun _ => smul_assoc ..

Depends on / 依赖: smul_assoc
-/
instance [SMul K γ] [SMul γ β] [SMul K β] [IsScalarTower K γ β] : IsScalarTower K γ (α ->ₛ β) where
  smul_assoc _ _ _ := ext fun _ => smul_assoc ..

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: γ β] [SMul K β] [SMulCommClass K γ β] : SMulCommClass K γ (α ->ₛ β) where
  body: ext fun _ => smul_comm ..

中文:
实例 [SMul
  签名: γ β] [SMul K β] [SMulCommClass K γ β] : SMulCommClass K γ (α ->ₛ β) where
  定义体: ext fun _ => smul_comm ..

Depends on / 依赖: smul_comm
-/
instance [SMul γ β] [SMul K β] [SMulCommClass K γ β] : SMulCommClass K γ (α ->ₛ β) where
  smul_comm _ _ _ := ext fun _ => smul_comm ..

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CommSemiring
  signature: K] [Semiring β] [Algebra K β] : Algebra K (α ->ₛ β) where
  body: {
toFun r := const α algebraMap K β r
.map_one ▸ rfl map_one' := ext fun _ => algebraMap K β
.map_mul .. map_mul' _ _ := ext fun _ => algebraMap K β
.map_zero ▸ rfl map_zero' := ext fun _ => algebraMap K β
.map_add .. } map_add' _ _ := ext fun _ => algebraMap K β
  commutes' _ _ := ext fun _ => Alge

中文:
实例 [CommSemiring
  签名: K] [Semiring β] [Algebra K β] : Algebra K (α ->ₛ β) where
  定义体: {
toFun r := const α algebraMap K β r
.map_one ▸ rfl map_one' := ext fun _ => algebraMap K β
.map_mul .. map_mul' _ _ := ext fun _ => algebraMap K β
.map_zero ▸ rfl map_zero' := ext fun _ => algebraMap K β
.map_add .. } map_add' _ _ := ext fun _ => algebraMap K β
  commutes' _ _ := ext fun _ => Alge
-/
instance [CommSemiring K] [Semiring β] [Algebra K β] : Algebra K (α ->ₛ β) where
  algebraMap := {
toFun r := const α algebraMap K β r
.map_one ▸ rfl map_one' := ext fun _ => algebraMap K β
.map_mul .. map_mul' _ _ := ext fun _ => algebraMap K β
.map_zero ▸ rfl map_zero' := ext fun _ => algebraMap K β
.map_add .. } map_add' _ _ := ext fun _ => algebraMap K β
  commutes' _ _ := ext fun _ => Algebra.commutes ..
  smul_def' _ _ := ext fun _ => Algebra.smul_def ..

@[simp]
/--
lemma `const_algebraMap` / 引理 `const_algebraMap`

English:
lemma const_algebraMap
  given: [CommSemiring K] [Semiring β] [Algebra K β] (k : K)
  proof: rfl

@[simp]

中文:
引理 const_algebraMap
  条件: [CommSemiring K] [Semiring β] [Algebra K β] (k : K)
  证明: rfl

@[simp]
-/
lemma const_algebraMap [CommSemiring K] [Semiring β] [Algebra K β] (k : K) :
    const α (algebraMap K β k) = algebraMap K (α ->ₛ β) k := rfl

@[simp]
/--
lemma `coe_algebraMap` / 引理 `coe_algebraMap`

English:
lemma coe_algebraMap
  given: [CommSemiring K] [Semiring β] [Algebra K β] (k : K) (x : α)
  proof: rfl

中文:
引理 coe_algebraMap
  条件: [CommSemiring K] [Semiring β] [Algebra K β] (k : K) (x : α)
  证明: rfl
-/
lemma coe_algebraMap [CommSemiring K] [Semiring β] [Algebra K β] (k : K) (x : α) :
    ⇑(algebraMap K (α ->ₛ β)) k x = algebraMap K (α -> β) k x := rfl

section Star

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Star
  signature: β] : Star (α ->ₛ β) where
  body: f.map Star.star

@[simp]

中文:
实例 [Star
  签名: β] : Star (α ->ₛ β) where
  定义体: f.map Star.star

@[simp]

Depends on / 依赖: Star.star, f.map
-/
instance [Star β] : Star (α ->ₛ β) where
  star f := f.map Star.star

@[simp]
/--
lemma `coe_star` / 引理 `coe_star`

English:
lemma coe_star
  given: [Star β] {f : α ->ₛ β}
  statement: ⇑(star f) = star ⇑f
  proof: rfl

中文:
引理 coe_star
  条件: [Star β] {f : α ->ₛ β}
  结论: ⇑(star f) = star ⇑f
  证明: rfl
-/
lemma coe_star [Star β] {f : α ->ₛ β} : ⇑(star f) = star ⇑f := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [InvolutiveStar
  signature: β] : InvolutiveStar (α ->ₛ β) where
  body: ext fun _ => star_star _

中文:
实例 [InvolutiveStar
  签名: β] : InvolutiveStar (α ->ₛ β) where
  定义体: ext fun _ => star_star _

Depends on / 依赖: star_star
-/
instance [InvolutiveStar β] : InvolutiveStar (α ->ₛ β) where
  star_involutive _ := ext fun _ => star_star _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddMonoid
  signature: β] [StarAddMonoid β] : StarAddMonoid (α ->ₛ β) where
  body: ext fun _ => star_add ..

中文:
实例 [AddMonoid
  签名: β] [StarAddMonoid β] : StarAddMonoid (α ->ₛ β) where
  定义体: ext fun _ => star_add ..

Depends on / 依赖: star_add
-/
instance [AddMonoid β] [StarAddMonoid β] : StarAddMonoid (α ->ₛ β) where
  star_add _ _ := ext fun _ => star_add ..

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Mul
  signature: β] [StarMul β] : StarMul (α ->ₛ β) where
  body: ext fun _ => star_mul ..

中文:
实例 [Mul
  签名: β] [StarMul β] : StarMul (α ->ₛ β) where
  定义体: ext fun _ => star_mul ..

Depends on / 依赖: star_mul
-/
instance [Mul β] [StarMul β] : StarMul (α ->ₛ β) where
  star_mul _ _ := ext fun _ => star_mul ..

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonUnitalNonAssocSemiring
  signature: β] [StarRing β] : StarRing (α ->ₛ β) where
  body: ext fun _ => star_add ..

中文:
实例 [NonUnitalNonAssocSemiring
  签名: β] [StarRing β] : StarRing (α ->ₛ β) where
  定义体: ext fun _ => star_add ..

Depends on / 依赖: star_add
-/
instance [NonUnitalNonAssocSemiring β] [StarRing β] : StarRing (α ->ₛ β) where
  star_add _ _ := ext fun _ => star_add ..

end Star

section Preorder
variable [Preorder β] {s : Set α} {f f₁ f₂ g g₁ g₂ : α ->ₛ β} {hs : MeasurableSet s}

/--
Instance `instPreorder` / 实例 `instPreorder`

English:
instance instPreorder
  signature: : Preorder (α ->ₛ β)
  body: Preorder.lift (⇑)

中文:
实例 instPreorder
  签名: : Preorder (α ->ₛ β)
  定义体: Preorder.lift (⇑)

Depends on / 依赖: Preorder, Preorder.lift
-/
instance instPreorder : Preorder (α ->ₛ β) := Preorder.lift (⇑)

/--
lemma `coe_le_coe` / 引理 `coe_le_coe`

English:
lemma coe_le_coe
  statement: ⇑f <= g ↔ f <= g
  proof: .rfl

中文:
引理 coe_le_coe
  结论: ⇑f <= g ↔ f <= g
  证明: .rfl
-/
@[simp, norm_cast, gcongr] lemma coe_le_coe : ⇑f <= g ↔ f <= g := .rfl
/--
lemma `coe_lt_coe` / 引理 `coe_lt_coe`

English:
lemma coe_lt_coe
  statement: ⇑f < g ↔ f < g
  proof: .rfl

@[simp, gcongr]

中文:
引理 coe_lt_coe
  结论: ⇑f < g ↔ f < g
  证明: .rfl

@[simp, gcongr]
-/
@[simp, norm_cast, gcongr] lemma coe_lt_coe : ⇑f < g ↔ f < g := .rfl

@[simp, gcongr]
/--
lemma `mk_le_mk` / 引理 `mk_le_mk`

English:
lemma mk_le_mk
  given: {f g : α -> β} {hf hg hf' hg'}
  statement: mk f hf hf' <= mk g hg hg' ↔ f <= g
  proof: Iff.rfl

@[simp, gcongr]

中文:
引理 mk_le_mk
  条件: {f g : α -> β} {hf hg hf' hg'}
  结论: mk f hf hf' <= mk g hg hg' ↔ f <= g
  证明: Iff.rfl

@[simp, gcongr]

Depends on / 依赖: Iff.rfl
-/
lemma mk_le_mk {f g : α -> β} {hf hg hf' hg'} : mk f hf hf' <= mk g hg hg' ↔ f <= g := Iff.rfl

@[simp, gcongr]
/--
lemma `mk_lt_mk` / 引理 `mk_lt_mk`

English:
lemma mk_lt_mk
  given: {f g : α -> β} {hf hg hf' hg'}
  statement: mk f hf hf' < mk g hg hg' ↔ f < g
  proof: Iff.rfl

@[gcongr only]

中文:
引理 mk_lt_mk
  条件: {f g : α -> β} {hf hg hf' hg'}
  结论: mk f hf hf' < mk g hg hg' ↔ f < g
  证明: Iff.rfl

@[gcongr only]

Depends on / 依赖: Iff.rfl
-/
lemma mk_lt_mk {f g : α -> β} {hf hg hf' hg'} : mk f hf hf' < mk g hg hg' ↔ f < g := Iff.rfl

@[gcongr only]
/--
lemma `piecewise_mono` / 引理 `piecewise_mono`

English:
lemma piecewise_mono
  given: (hf : forall a in s, f₁ a <= f₂ a) (hg : forall a ∉ s, g₁ a <= g₂ a)
  proof: by
  classical
  exact Set.piecewise_mono hf hg

中文:
引理 piecewise_mono
  条件: (hf : 对任意 a in s, f₁ a <= f₂ a) (hg : 对任意 a ∉ s, g₁ a <= g₂ a)
  证明: by
  classical
  exact Set.piecewise_mono hf hg

Depends on / 依赖: Set.piecewise_mono, classical, piecewise_mono
-/
lemma piecewise_mono (hf : forall a in s, f₁ a <= f₂ a) (hg : forall a ∉ s, g₁ a <= g₂ a) :
    piecewise s hs f₁ g₁ <= piecewise s hs f₂ g₂ := by
  classical
  exact Set.piecewise_mono hf hg

end Preorder

/--
Instance `instPartialOrder` / 实例 `instPartialOrder`

English:
instance instPartialOrder
  signature: [PartialOrder β]
  body: { SimpleFunc.instPreorder with
    le_antisymm := fun _f _g hfg hgf => ext fun a => le_antisymm (hfg a) (hgf a) }

中文:
实例 instPartialOrder
  签名: [PartialOrder β]
  定义体: { SimpleFunc.instPreorder with
    le_antisymm := fun _f _g hfg hgf => ext fun a => le_antisymm (hfg a) (hgf a) }

Depends on / 依赖: SimpleFunc, SimpleFunc.instPreorder, instPreorder, le_antisymm
-/
instance instPartialOrder [PartialOrder β] : PartialOrder (α ->ₛ β) :=
  { SimpleFunc.instPreorder with
    le_antisymm := fun _f _g hfg hgf => ext fun a => le_antisymm (hfg a) (hgf a) }

/--
Instance `instOrderBot` / 实例 `instOrderBot`

English:
instance instOrderBot
  signature: [LE β] [OrderBot β]
  body: const α ⊥
  bot_le _ _ := bot_le

中文:
实例 instOrderBot
  签名: [LE β] [OrderBot β]
  定义体: const α ⊥
  bot_le _ _ := bot_le
-/
instance instOrderBot [LE β] [OrderBot β] : OrderBot (α ->ₛ β) where
  bot := const α ⊥
  bot_le _ _ := bot_le

/--
Instance `instOrderTop` / 实例 `instOrderTop`

English:
instance instOrderTop
  signature: [LE β] [OrderTop β]
  body: const α ⊤
  le_top _ _ := le_top

@[to_additive]

中文:
实例 instOrderTop
  签名: [LE β] [OrderTop β]
  定义体: const α ⊤
  le_top _ _ := le_top

@[to_additive]
-/
instance instOrderTop [LE β] [OrderTop β] : OrderTop (α ->ₛ β) where
  top := const α ⊤
  le_top _ _ := le_top

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CommMonoid
  signature: β] [Preorder β] [IsOrderedMonoid β] :
  body: mul_le_mul_left (h _) _

中文:
实例 [CommMonoid
  签名: β] [Preorder β] [IsOrderedMonoid β] :
  定义体: mul_le_mul_left (h _) _

Depends on / 依赖: mul_le_mul_left
-/
instance [CommMonoid β] [Preorder β] [IsOrderedMonoid β] :
    IsOrderedMonoid (α ->ₛ β) where
  mul_le_mul_left _ _ h _ _ := mul_le_mul_left (h _) _

/--
Instance `instSemilatticeInf` / 实例 `instSemilatticeInf`

English:
instance instSemilatticeInf
  signature: [SemilatticeInf β]
  body: { SimpleFunc.instPartialOrder with
    inf := (· ⊓ ·)
    inf_le_left := fun _ _ _ => inf_le_left
    inf_le_right := fun _ _ _ => inf_le_right
    le_inf := fun _f _g _h hfh hgh a => le_inf (hfh a) (hgh a) }

中文:
实例 instSemilatticeInf
  签名: [SemilatticeInf β]
  定义体: { SimpleFunc.instPartialOrder with
    inf := (· ⊓ ·)
    inf_le_left := fun _ _ _ => inf_le_left
    inf_le_right := fun _ _ _ => inf_le_right
    le_inf := fun _f _g _h hfh hgh a => le_inf (hfh a) (hgh a) }

Depends on / 依赖: SimpleFunc, SimpleFunc.instPartialOrder, inf_le_left, inf_le_right, instPartialOrder, le_inf
-/
instance instSemilatticeInf [SemilatticeInf β] : SemilatticeInf (α ->ₛ β) :=
  { SimpleFunc.instPartialOrder with
    inf := (· ⊓ ·)
    inf_le_left := fun _ _ _ => inf_le_left
    inf_le_right := fun _ _ _ => inf_le_right
    le_inf := fun _f _g _h hfh hgh a => le_inf (hfh a) (hgh a) }

/--
Instance `instSemilatticeSup` / 实例 `instSemilatticeSup`

English:
instance instSemilatticeSup
  signature: [SemilatticeSup β]
  body: { SimpleFunc.instPartialOrder with
    sup := (· ⊔ ·)
    le_sup_left := fun _ _ _ => le_sup_left
    le_sup_right := fun _ _ _ => le_sup_right
    sup_le := fun _f _g _h hfh hgh a => sup_le (hfh a) (hgh a) }

中文:
实例 instSemilatticeSup
  签名: [SemilatticeSup β]
  定义体: { SimpleFunc.instPartialOrder with
    sup := (· ⊔ ·)
    le_sup_left := fun _ _ _ => le_sup_left
    le_sup_right := fun _ _ _ => le_sup_right
    sup_le := fun _f _g _h hfh hgh a => sup_le (hfh a) (hgh a) }

Depends on / 依赖: SimpleFunc, SimpleFunc.instPartialOrder, instPartialOrder, le_sup_left, le_sup_right, sup_le
-/
instance instSemilatticeSup [SemilatticeSup β] : SemilatticeSup (α ->ₛ β) :=
  { SimpleFunc.instPartialOrder with
    sup := (· ⊔ ·)
    le_sup_left := fun _ _ _ => le_sup_left
    le_sup_right := fun _ _ _ => le_sup_right
    sup_le := fun _f _g _h hfh hgh a => sup_le (hfh a) (hgh a) }

/--
Instance `instLattice` / 实例 `instLattice`

English:
instance instLattice
  signature: [Lattice β]
  body: { SimpleFunc.instSemilatticeSup, SimpleFunc.instSemilatticeInf with }

中文:
实例 instLattice
  签名: [Lattice β]
  定义体: { SimpleFunc.instSemilatticeSup, SimpleFunc.instSemilatticeInf with }

Depends on / 依赖: SimpleFunc, SimpleFunc.instSemilatticeInf, SimpleFunc.instSemilatticeSup, instSemilatticeInf, instSemilatticeSup
-/
instance instLattice [Lattice β] : Lattice (α ->ₛ β) :=
  { SimpleFunc.instSemilatticeSup, SimpleFunc.instSemilatticeInf with }

/--
Instance `instBoundedOrder` / 实例 `instBoundedOrder`

English:
instance instBoundedOrder
  signature: [LE β] [BoundedOrder β]
  body: { SimpleFunc.instOrderBot, SimpleFunc.instOrderTop with }

中文:
实例 instBoundedOrder
  签名: [LE β] [BoundedOrder β]
  定义体: { SimpleFunc.instOrderBot, SimpleFunc.instOrderTop with }

Depends on / 依赖: SimpleFunc, SimpleFunc.instOrderBot, SimpleFunc.instOrderTop, instOrderBot, instOrderTop
-/
instance instBoundedOrder [LE β] [BoundedOrder β] : BoundedOrder (α ->ₛ β) :=
  { SimpleFunc.instOrderBot, SimpleFunc.instOrderTop with }

/--
theorem `finset_sup_apply` / 定理 `finset_sup_apply`

English:
theorem finset_sup_apply
  given: [SemilatticeSup β] [OrderBot β] {f : γ -> α ->ₛ β} (s : Finset γ) (a : α)
  proof: by
  classical
  refine Finset.induction_on s rfl ?_
  intro a s _ ih
  rw [Finset.sup_insert]; rw [Finset.sup_insert]; rw [sup_apply]; rw [ih]

中文:
定理 finset_sup_apply
  条件: [SemilatticeSup β] [OrderBot β] {f : γ -> α ->ₛ β} (s : Finset γ) (a : α)
  证明: by
  classical
  refine Finset.induction_on s rfl ?_
  intro a s _ ih
  rw [Finset.sup_insert]; rw [Finset.sup_insert]; rw [sup_apply]; rw [ih]

Depends on / 依赖: Finset, Finset.induction_on, Finset.sup_insert, classical, induction_on, sup_apply, sup_insert
-/
theorem finset_sup_apply [SemilatticeSup β] [OrderBot β] {f : γ -> α ->ₛ β} (s : Finset γ) (a : α) :
    s.sup f a = s.sup fun c => f c a := by
  classical
  refine Finset.induction_on s rfl ?_
  intro a s _ ih
  rw [Finset.sup_insert]; rw [Finset.sup_insert]; rw [sup_apply]; rw [ih]

section Restrict

variable [Zero β]

open scoped Classical in
/--
Definition of `restrict` / `restrict` 的定义

English:
definition restrict
  signature: (f : α ->ₛ β) (s : Set α)
  body: if hs : MeasurableSet s then piecewise s hs f 0 else 0

中文:
定义 restrict
  签名: (f : α ->ₛ β) (s : Set α)
  定义体: if hs : MeasurableSet s then piecewise s hs f 0 else 0

Depends on / 依赖: MeasurableSet, piecewise
-/
def restrict (f : α ->ₛ β) (s : Set α) : α ->ₛ β :=
  if hs : MeasurableSet s then piecewise s hs f 0 else 0

/--
theorem `restrict_of_not_measurable` / 定理 `restrict_of_not_measurable`

English:
theorem restrict_of_not_measurable
  given: {f : α ->ₛ β} {s : Set α} (hs : ¬MeasurableSet s)
  proof: dif_neg hs

@[simp]

中文:
定理 restrict_of_not_measurable
  条件: {f : α ->ₛ β} {s : Set α} (hs : ¬MeasurableSet s)
  证明: dif_neg hs

@[simp]

Depends on / 依赖: dif_neg
-/
theorem restrict_of_not_measurable {f : α ->ₛ β} {s : Set α} (hs : ¬MeasurableSet s) :
    restrict f s = 0 :=
  dif_neg hs

@[simp]
/--
theorem `coe_restrict` / 定理 `coe_restrict`

English:
theorem coe_restrict
  given: (f : α ->ₛ β) {s : Set α} (hs : MeasurableSet s)
  proof: by
  classical
  rw [restrict]; rw [dif_pos hs]; rw [coe_piecewise]; rw [coe_zero]; rw [piecewise_eq_indicator]

@[simp]

中文:
定理 coe_restrict
  条件: (f : α ->ₛ β) {s : Set α} (hs : MeasurableSet s)
  证明: by
  classical
  rw [restrict]; rw [dif_pos hs]; rw [coe_piecewise]; rw [coe_zero]; rw [piecewise_eq_indicator]

@[simp]

Depends on / 依赖: classical, coe_piecewise, coe_zero, dif_pos, piecewise_eq_indicator, restrict
-/
theorem coe_restrict (f : α ->ₛ β) {s : Set α} (hs : MeasurableSet s) :
    ⇑(restrict f s) = indicator s f := by
  classical
  rw [restrict]; rw [dif_pos hs]; rw [coe_piecewise]; rw [coe_zero]; rw [piecewise_eq_indicator]

@[simp]
/--
theorem `restrict_univ` / 定理 `restrict_univ`

English:
theorem restrict_univ
  given: (f : α ->ₛ β)
  statement: restrict f univ = f
  proof: by simp [restrict]

@[simp]

中文:
定理 restrict_univ
  条件: (f : α ->ₛ β)
  结论: restrict f univ = f
  证明: by simp [restrict]

@[simp]

Depends on / 依赖: restrict
-/
theorem restrict_univ (f : α ->ₛ β) : restrict f univ = f := by simp [restrict]

@[simp]
/--
theorem `restrict_empty` / 定理 `restrict_empty`

English:
theorem restrict_empty
  given: (f : α ->ₛ β)
  statement: restrict f ∅ = 0
  proof: by simp [restrict]

中文:
定理 restrict_empty
  条件: (f : α ->ₛ β)
  结论: restrict f ∅ = 0
  证明: by simp [restrict]

Depends on / 依赖: restrict
-/
theorem restrict_empty (f : α ->ₛ β) : restrict f ∅ = 0 := by simp [restrict]

/--
theorem `map_restrict_of_zero` / 定理 `map_restrict_of_zero`

English:
theorem map_restrict_of_zero
  given: [Zero γ] {g : β -> γ} (hg : g 0 = 0) (f : α ->ₛ β) (s : Set α)
  proof: by
  classical
  exact ext fun x =>
    if hs : MeasurableSet s then by simp [hs, Set.indicator_comp_of_zero hg]
    else by simp [restrict_of_not_measurable hs, hg]

中文:
定理 map_restrict_of_zero
  条件: [Zero γ] {g : β -> γ} (hg : g 0 = 0) (f : α ->ₛ β) (s : Set α)
  证明: by
  classical
  exact ext fun x =>
    if hs : MeasurableSet s then by simp [hs, Set.indicator_comp_of_zero hg]
    else by simp [restrict_of_not_measurable hs, hg]

Depends on / 依赖: MeasurableSet, Set.indicator_comp_of_zero, classical, indicator_comp_of_zero, restrict_of_not_measurable
-/
theorem map_restrict_of_zero [Zero γ] {g : β -> γ} (hg : g 0 = 0) (f : α ->ₛ β) (s : Set α) :
    (f.restrict s).map g = (f.map g).restrict s := by
  classical
  exact ext fun x =>
    if hs : MeasurableSet s then by simp [hs, Set.indicator_comp_of_zero hg]
    else by simp [restrict_of_not_measurable hs, hg]

/--
theorem `map_coe_ennreal_restrict` / 定理 `map_coe_ennreal_restrict`

English:
theorem map_coe_ennreal_restrict
  given: (f : α ->ₛ Real>=0) (s : Set α)
  proof: map_restrict_of_zero ENNReal.coe_zero _ _

中文:
定理 map_coe_ennreal_restrict
  条件: (f : α ->ₛ 实数>=0) (s : Set α)
  证明: map_restrict_of_zero ENNReal.coe_zero _ _

Depends on / 依赖: ENNReal, ENNReal.coe_zero, coe_zero, map_restrict_of_zero
-/
theorem map_coe_ennreal_restrict (f : α ->ₛ Real>=0) (s : Set α) :
    (f.restrict s).map ((↑) : Real>=0 -> Real>=0∞) = (f.map (↑)).restrict s :=
  map_restrict_of_zero ENNReal.coe_zero _ _

/--
theorem `map_coe_nnreal_restrict` / 定理 `map_coe_nnreal_restrict`

English:
theorem map_coe_nnreal_restrict
  given: (f : α ->ₛ Real>=0) (s : Set α)
  proof: map_restrict_of_zero NNReal.coe_zero _ _

中文:
定理 map_coe_nnreal_restrict
  条件: (f : α ->ₛ 实数>=0) (s : Set α)
  证明: map_restrict_of_zero NNReal.coe_zero _ _

Depends on / 依赖: NNReal, NNReal.coe_zero, coe_zero, map_restrict_of_zero
-/
theorem map_coe_nnreal_restrict (f : α ->ₛ Real>=0) (s : Set α) :
    (f.restrict s).map ((↑) : Real>=0 -> Real) = (f.map (↑)).restrict s :=
  map_restrict_of_zero NNReal.coe_zero _ _

/--
theorem `restrict_apply` / 定理 `restrict_apply`

English:
theorem restrict_apply
  given: (f : α ->ₛ β) {s : Set α} (hs : MeasurableSet s) (a)
  proof: by simp only [f.coe_restrict hs]

中文:
定理 restrict_apply
  条件: (f : α ->ₛ β) {s : Set α} (hs : MeasurableSet s) (a)
  证明: by simp only [f.coe_restrict hs]

Depends on / 依赖: coe_restrict, f.coe_restrict
-/
theorem restrict_apply (f : α ->ₛ β) {s : Set α} (hs : MeasurableSet s) (a) :
    restrict f s a = indicator s f a := by simp only [f.coe_restrict hs]

/--
theorem `restrict_preimage` / 定理 `restrict_preimage`

English:
theorem restrict_preimage
  statement: (f : α ->ₛ β) {s : Set α} (hs : MeasurableSet s) {t : Set β}
  proof: by
  simp [hs, indicator_preimage_of_notMem _ _ ht, inter_comm]

中文:
定理 restrict_preimage
  结论: (f : α ->ₛ β) {s : Set α} (hs : MeasurableSet s) {t : Set β}
  证明: by
  simp [hs, indicator_preimage_of_notMem _ _ ht, inter_comm]

Depends on / 依赖: indicator_preimage_of_notMem, inter_comm
-/
theorem restrict_preimage (f : α ->ₛ β) {s : Set α} (hs : MeasurableSet s) {t : Set β}
    (ht : (0 : β) ∉ t) : restrict f s ⁻¹' t = s inter f ⁻¹' t := by
  simp [hs, indicator_preimage_of_notMem _ _ ht, inter_comm]

/--
theorem `restrict_preimage_singleton` / 定理 `restrict_preimage_singleton`

English:
theorem restrict_preimage_singleton
  statement: (f : α ->ₛ β) {s : Set α} (hs : MeasurableSet s) {r : β}
  proof: f.restrict_preimage hs hr.symm

中文:
定理 restrict_preimage_singleton
  结论: (f : α ->ₛ β) {s : Set α} (hs : MeasurableSet s) {r : β}
  证明: f.restrict_preimage hs hr.symm

Depends on / 依赖: f.restrict_preimage, hr.symm, restrict_preimage
-/
theorem restrict_preimage_singleton (f : α ->ₛ β) {s : Set α} (hs : MeasurableSet s) {r : β}
    (hr : r != 0) : restrict f s ⁻¹' {r} = s inter f ⁻¹' {r} :=
  f.restrict_preimage hs hr.symm

/--
theorem `mem_restrict_range` / 定理 `mem_restrict_range`

English:
theorem mem_restrict_range
  given: {r : β} {s : Set α} {f : α ->ₛ β} (hs : MeasurableSet s)
  proof: by
  rw [← Finset.mem_coe]; rw [coe_range]; rw [coe_restrict _ hs]; rw [mem_range_indicator]

中文:
定理 mem_restrict_range
  条件: {r : β} {s : Set α} {f : α ->ₛ β} (hs : MeasurableSet s)
  证明: by
  rw [← Finset.mem_coe]; rw [coe_range]; rw [coe_restrict _ hs]; rw [mem_range_indicator]

Depends on / 依赖: Finset, Finset.mem_coe, coe_range, coe_restrict, mem_coe, mem_range_indicator
-/
theorem mem_restrict_range {r : β} {s : Set α} {f : α ->ₛ β} (hs : MeasurableSet s) :
    r in (restrict f s).range ↔ r = 0 ∧ s != univ ∨ r in f '' s := by
  rw [← Finset.mem_coe]; rw [coe_range]; rw [coe_restrict _ hs]; rw [mem_range_indicator]

/--
theorem `mem_image_of_mem_range_restrict` / 定理 `mem_image_of_mem_range_restrict`

English:
theorem mem_image_of_mem_range_restrict
  statement: {r : β} {s : Set α} {f : α ->ₛ β}
  proof: by
  classical
  exact if hs : MeasurableSet s then by simpa [mem_restrict_range hs, h0, -mem_range] using hr
  else by
    rw [restrict_of_not_measurable hs] at hr
    exact (h0 <| eq_zero_of_mem_range_zero hr).elim

@[gcongr, mono]

中文:
定理 mem_image_of_mem_range_restrict
  结论: {r : β} {s : Set α} {f : α ->ₛ β}
  证明: by
  classical
  exact if hs : MeasurableSet s then by simpa [mem_restrict_range hs, h0, -mem_range] using hr
  else by
    rw [restrict_of_not_measurable hs] at hr
    exact (h0 <| eq_zero_of_mem_range_zero hr).elim

@[gcongr, mono]

Depends on / 依赖: MeasurableSet, classical, eq_zero_of_mem_range_zero, mem_range, mem_restrict_range, restrict_of_not_measurable
-/
theorem mem_image_of_mem_range_restrict {r : β} {s : Set α} {f : α ->ₛ β}
    (hr : r in (restrict f s).range) (h0 : r != 0) : r in f '' s := by
  classical
  exact if hs : MeasurableSet s then by simpa [mem_restrict_range hs, h0, -mem_range] using hr
  else by
    rw [restrict_of_not_measurable hs] at hr
    exact (h0 <| eq_zero_of_mem_range_zero hr).elim

@[gcongr, mono]
/--
theorem `restrict_mono` / 定理 `restrict_mono`

English:
theorem restrict_mono
  given: [Preorder β] (s : Set α) {f g : α ->ₛ β} (H : f <= g)
  proof: by
  classical
  exact if hs : MeasurableSet s then fun x => by
    simp only [coe_restrict _ hs, indicator_le_indicator (H x)]
  else by simp only [restrict_of_not_measurable hs, le_refl]

中文:
定理 restrict_mono
  条件: [Preorder β] (s : Set α) {f g : α ->ₛ β} (H : f <= g)
  证明: by
  classical
  exact if hs : MeasurableSet s then fun x => by
    simp only [coe_restrict _ hs, indicator_le_indicator (H x)]
  else by simp only [restrict_of_not_measurable hs, le_refl]

Depends on / 依赖: MeasurableSet, classical, coe_restrict, indicator_le_indicator, le_refl, restrict_of_not_measurable
-/
theorem restrict_mono [Preorder β] (s : Set α) {f g : α ->ₛ β} (H : f <= g) :
    f.restrict s <= g.restrict s := by
  classical
  exact if hs : MeasurableSet s then fun x => by
    simp only [coe_restrict _ hs, indicator_le_indicator (H x)]
  else by simp only [restrict_of_not_measurable hs, le_refl]

end Restrict

section Approx

section

variable [SemilatticeSup β] [OrderBot β] [Zero β]

/--
Definition of `approx` / `approx` 的定义

English:
definition approx
  signature: (i : Nat -> β) (f : α -> β) (n : Nat)
  body: (Finset.range n).sup fun k => restrict (const α (i k)) { a : α | i k <= f a }

中文:
定义 approx
  签名: (i : 自然数 -> β) (f : α -> β) (n : 自然数)
  定义体: (Finset.range n).sup fun k => restrict (const α (i k)) { a : α | i k <= f a }

Depends on / 依赖: Finset, Finset.range, restrict
-/
def approx (i : Nat -> β) (f : α -> β) (n : Nat) : α ->ₛ β :=
  (Finset.range n).sup fun k => restrict (const α (i k)) { a : α | i k <= f a }

open scoped Classical in
/--
theorem `approx_apply` / 定理 `approx_apply`

English:
theorem approx_apply
  statement: [TopologicalSpace β] [OrderClosedTopology β] [MeasurableSpace β]
  proof: by
  dsimp only [approx]
  rw [finset_sup_apply]
  congr
  funext k
  rw [restrict_apply]
  · simp only [coe_const, mem_ofPred_eq, indicator_apply, Function.const_apply]
  · exact hf measurableSet_Ici

中文:
定理 approx_apply
  结论: [TopologicalSpace β] [OrderClosedTopology β] [MeasurableSpace β]
  证明: by
  dsimp only [approx]
  rw [finset_sup_apply]
  congr
  funext k
  rw [restrict_apply]
  · simp only [coe_const, mem_ofPred_eq, indicator_apply, Function.const_apply]
  · exact hf measurableSet_Ici

Depends on / 依赖: Function, Function.const_apply, approx, coe_const, const_apply, finset_sup_apply, indicator_apply, measurableSet_Ici, mem_ofPred_eq, restrict_apply
-/
theorem approx_apply [TopologicalSpace β] [OrderClosedTopology β] [MeasurableSpace β]
    [OpensMeasurableSpace β] {i : Nat -> β} {f : α -> β} {n : Nat} (a : α) (hf : Measurable f) :
    (approx i f n : α ->ₛ β) a = (Finset.range n).sup fun k => if i k <= f a then i k else 0 := by
  dsimp only [approx]
  rw [finset_sup_apply]
  congr
  funext k
  rw [restrict_apply]
  · simp only [coe_const, mem_ofPred_eq, indicator_apply, Function.const_apply]
  · exact hf measurableSet_Ici

/--
theorem `monotone_approx` / 定理 `monotone_approx`

English:
theorem monotone_approx
  given: (i : Nat -> β) (f : α -> β)
  statement: Monotone (approx i f)
  proof: fun _ _ h =>
Finset.sup_mono Finset.range_subset_range.2 h

中文:
定理 monotone_approx
  条件: (i : 自然数 -> β) (f : α -> β)
  结论: Monotone (approx i f)
  证明: fun _ _ h =>
Finset.sup_mono Finset.range_subset_range.2 h
-/
theorem monotone_approx (i : Nat -> β) (f : α -> β) : Monotone (approx i f) := fun _ _ h =>
Finset.sup_mono Finset.range_subset_range.2 h

/--
theorem `approx_comp` / 定理 `approx_comp`

English:
theorem approx_comp
  statement: [TopologicalSpace β] [OrderClosedTopology β] [MeasurableSpace β]
  proof: by
  rw [approx_apply _ hf]; rw [approx_apply _ (hf.comp hg)]; rw [Function.comp_apply]

中文:
定理 approx_comp
  结论: [TopologicalSpace β] [OrderClosedTopology β] [MeasurableSpace β]
  证明: by
  rw [approx_apply _ hf]; rw [approx_apply _ (hf.comp hg)]; rw [Function.comp_apply]

Depends on / 依赖: Function, Function.comp_apply, approx_apply, comp_apply, hf.comp
-/
theorem approx_comp [TopologicalSpace β] [OrderClosedTopology β] [MeasurableSpace β]
    [OpensMeasurableSpace β] [MeasurableSpace γ] {i : Nat -> β} {f : γ -> β} {g : α -> γ} {n : Nat} (a : α)
    (hf : Measurable f) (hg : Measurable g) :
    (approx i (f ∘ g) n : α ->ₛ β) a = (approx i f n : γ ->ₛ β) (g a) := by
  rw [approx_apply _ hf]; rw [approx_apply _ (hf.comp hg)]; rw [Function.comp_apply]

end

/--
theorem `iSup_approx_apply` / 定理 `iSup_approx_apply`

English:
theorem iSup_approx_apply
  statement: [TopologicalSpace β] [CompleteLattice β] [OrderClosedTopology β] [Zero β]
  proof: by
  refine le_antisymm (iSup_le fun n => ?_) (iSup_le fun k => iSup_le fun hk => ?_)
  · rw [approx_apply a hf, h_zero]
    refine Finset.sup_le fun k _ => ?_
    split_ifs with h
    · exact le_iSup_of_le k (le_iSup (fun _ : i k <= f a => i k) h)
    · exact bot_le
  · refine le_iSup_of_le (k + 1)

中文:
定理 iSup_approx_apply
  结论: [TopologicalSpace β] [CompleteLattice β] [OrderClosedTopology β] [Zero β]
  证明: by
  refine le_antisymm (iSup_le fun n => ?_) (iSup_le fun k => iSup_le fun hk => ?_)
  · rw [approx_apply a hf, h_zero]
    refine Finset.sup_le fun k _ => ?_
    split_ifs with h
    · exact le_iSup_of_le k (le_iSup (fun _ : i k <= f a => i k) h)
    · exact bot_le
  · refine le_iSup_of_le (k + 1)

Depends on / 依赖: Finset, Finset.le_sup, Finset.mem_range, Finset.range, Finset.sup_le, Nat.lt_succ_self, approx_apply, bot_le, h_zero, iSup_le, if_pos, le_antisymm, le_iSup, le_iSup_of_le, le_of_eq, le_sup, le_trans, lt_succ_self, mem_range, split_ifs
-/
theorem iSup_approx_apply [TopologicalSpace β] [CompleteLattice β] [OrderClosedTopology β] [Zero β]
    [MeasurableSpace β] [OpensMeasurableSpace β] (i : Nat -> β) (f : α -> β) (a : α) (hf : Measurable f)
    (h_zero : (0 : β) = ⊥) : ⨆ n, (approx i f n : α ->ₛ β) a = ⨆ (k) (_ : i k <= f a), i k := by
  refine le_antisymm (iSup_le fun n => ?_) (iSup_le fun k => iSup_le fun hk => ?_)
  · rw [approx_apply a hf, h_zero]
    refine Finset.sup_le fun k _ => ?_
    split_ifs with h
    · exact le_iSup_of_le k (le_iSup (fun _ : i k <= f a => i k) h)
    · exact bot_le
  · refine le_iSup_of_le (k + 1) ?_
    rw [approx_apply a hf]
    have : k in Finset.range (k + 1) := Finset.mem_range.2 (Nat.lt_succ_self _)
    refine le_trans (le_of_eq ?_) (Finset.le_sup this)
    rw [if_pos hk]

end Approx

section EApprox
variable {f : α -> Real>=0∞}

/--
Definition of `ennrealRatEmbed` / `ennrealRatEmbed` 的定义

English:
definition ennrealRatEmbed
  signature: (n : Nat)
  body: ENNReal.ofReal ((Encodable.decode (α := Rat) n).getD (0 : Rat))

中文:
定义 ennrealRatEmbed
  签名: (n : 自然数)
  定义体: ENNReal.ofReal ((Encodable.decode (α := Rat) n).getD (0 : Rat))

Depends on / 依赖: ENNReal, ENNReal.ofReal, Encodable, Encodable.decode, decode, ofReal
-/
def ennrealRatEmbed (n : Nat) : Real>=0∞ :=
  ENNReal.ofReal ((Encodable.decode (α := Rat) n).getD (0 : Rat))

/--
theorem `ennrealRatEmbed_encode` / 定理 `ennrealRatEmbed_encode`

English:
theorem ennrealRatEmbed_encode
  given: (q : Rat)
  proof: by
  rw [ennrealRatEmbed]; rw [Encodable.encodek]; rfl

中文:
定理 ennrealRatEmbed_encode
  条件: (q : Rat)
  证明: by
  rw [ennrealRatEmbed]; rw [Encodable.encodek]; rfl

Depends on / 依赖: Encodable, Encodable.encodek, encodek, ennrealRatEmbed
-/
theorem ennrealRatEmbed_encode (q : Rat) :
    ennrealRatEmbed (Encodable.encode q) = Real.toNNReal q := by
  rw [ennrealRatEmbed]; rw [Encodable.encodek]; rfl

/--
Definition of `eapprox` / `eapprox` 的定义

English:
definition eapprox
  signature: : (α -> Real>=0∞) -> Nat -> α ->ₛ Real>=0∞
  body: approx ennrealRatEmbed

中文:
定义 eapprox
  签名: : (α -> 实数>=0∞) -> 自然数 -> α ->ₛ 实数>=0∞
  定义体: approx ennrealRatEmbed

Depends on / 依赖: approx, ennrealRatEmbed
-/
def eapprox : (α -> Real>=0∞) -> Nat -> α ->ₛ Real>=0∞ :=
  approx ennrealRatEmbed

/--
theorem `eapprox_lt_top` / 定理 `eapprox_lt_top`

English:
theorem eapprox_lt_top
  given: (f : α -> Real>=0∞) (n : Nat) (a : α)
  statement: eapprox f n a < ∞
  proof: by
  simp only [eapprox, approx, finset_sup_apply, restrict]
  rw [Finset.sup_lt_iff (α := Real>=0∞) bot_lt_top]
  intro b _
  split_ifs
  · simp only [coe_zero, coe_piecewise, piecewise_eq_indicator, coe_const]
    calc
      { a : α | ennrealRatEmbed b <= f a }.indicator (fun _ => ennrealRatEmbed 

中文:
定理 eapprox_lt_top
  条件: (f : α -> 实数>=0∞) (n : 自然数) (a : α)
  结论: eapprox f n a < ∞
  证明: by
  simp only [eapprox, approx, finset_sup_apply, restrict]
  rw [Finset.sup_lt_iff (α := Real>=0∞) bot_lt_top]
  intro b _
  split_ifs
  · simp only [coe_zero, coe_piecewise, piecewise_eq_indicator, coe_const]
    calc
      { a : α | ennrealRatEmbed b <= f a }.indicator (fun _ => ennrealRatEmbed 

Depends on / 依赖: ENNReal, ENNReal.coe_lt_top, Finset, Finset.sup_lt_iff, WithTop, WithTop.top_pos, approx, bot_lt_top, coe_const, coe_lt_top, coe_piecewise, coe_zero, eapprox, ennrealRatEmbed, finset_sup_apply, indicator, indicator_le_self, piecewise_eq_indicator, restrict, split_ifs
-/
theorem eapprox_lt_top (f : α -> Real>=0∞) (n : Nat) (a : α) : eapprox f n a < ∞ := by
  simp only [eapprox, approx, finset_sup_apply, restrict]
  rw [Finset.sup_lt_iff (α := Real>=0∞) bot_lt_top]
  intro b _
  split_ifs
  · simp only [coe_zero, coe_piecewise, piecewise_eq_indicator, coe_const]
    calc
      { a : α | ennrealRatEmbed b <= f a }.indicator (fun _ => ennrealRatEmbed b) a <=
          ennrealRatEmbed b :=
        indicator_le_self _ _ a
      _ < ⊤ := ENNReal.coe_lt_top
  · exact WithTop.top_pos

@[gcongr, mono]
/--
theorem `monotone_eapprox` / 定理 `monotone_eapprox`

English:
theorem monotone_eapprox
  given: (f : α -> Real>=0∞)
  statement: Monotone (eapprox f)
  proof: monotone_approx _ f

中文:
定理 monotone_eapprox
  条件: (f : α -> 实数>=0∞)
  结论: Monotone (eapprox f)
  证明: monotone_approx _ f

Depends on / 依赖: monotone_approx
-/
theorem monotone_eapprox (f : α -> Real>=0∞) : Monotone (eapprox f) :=
  monotone_approx _ f

/--
lemma `iSup_eapprox_apply` / 引理 `iSup_eapprox_apply`

English:
lemma iSup_eapprox_apply
  given: (hf : Measurable f) (a : α)
  statement: ⨆ n, (eapprox f n : α ->ₛ Real>=0∞) a = f a
  proof: by
  rw [eapprox]; rw [iSup_approx_apply ennrealRatEmbed f a hf rfl]
  refine le_antisymm (iSup_le fun i => iSup_le fun hi => hi) (le_of_not_gt ?_)
  intro h
  rcases ENNReal.lt_iff_exists_rat_btwn.1 h with ⟨q, _, lt_q, q_lt⟩
  have :
    (Real.toNNReal q : Real>=0∞) <= ⨆ (k : Nat) (_ : ennrealRatEm

中文:
引理 iSup_eapprox_apply
  条件: (hf : Measurable f) (a : α)
  结论: ⨆ n, (eapprox f n : α ->ₛ 实数>=0∞) a = f a
  证明: by
  rw [eapprox]; rw [iSup_approx_apply ennrealRatEmbed f a hf rfl]
  refine le_antisymm (iSup_le fun i => iSup_le fun hi => hi) (le_of_not_gt ?_)
  intro h
  rcases ENNReal.lt_iff_exists_rat_btwn.1 h with ⟨q, _, lt_q, q_lt⟩
  have :
    (Real.toNNReal q : Real>=0∞) <= ⨆ (k : Nat) (_ : ennrealRatEm

Depends on / 依赖: ENNReal, ENNReal.lt_iff_exists_rat_btwn, Encodable, Encodable.encode, Real.toNNReal, eapprox, encode, ennrealRatEmbed, ennrealRatEmbed_encode, iSup_approx_apply, iSup_le, le_antisymm, le_iSup_of_le, le_of_lt, le_of_not_gt, le_rfl, lt_iff_exists_rat_btwn, lt_irrefl, lt_of_le_of_lt, lt_q
-/
lemma iSup_eapprox_apply (hf : Measurable f) (a : α) : ⨆ n, (eapprox f n : α ->ₛ Real>=0∞) a = f a := by
  rw [eapprox]; rw [iSup_approx_apply ennrealRatEmbed f a hf rfl]
  refine le_antisymm (iSup_le fun i => iSup_le fun hi => hi) (le_of_not_gt ?_)
  intro h
  rcases ENNReal.lt_iff_exists_rat_btwn.1 h with ⟨q, _, lt_q, q_lt⟩
  have :
    (Real.toNNReal q : Real>=0∞) <= ⨆ (k : Nat) (_ : ennrealRatEmbed k <= f a), ennrealRatEmbed k := by
    refine le_iSup_of_le (Encodable.encode q) ?_
    rw [ennrealRatEmbed_encode q]
    exact le_iSup_of_le (le_of_lt q_lt) le_rfl
  exact lt_irrefl _ (lt_of_le_of_lt this lt_q)

/--
lemma `iSup_coe_eapprox` / 引理 `iSup_coe_eapprox`

English:
lemma iSup_coe_eapprox
  given: (hf : Measurable f)
  statement: ⨆ n, ⇑(eapprox f n) = f
  proof: by
  simpa [funext_iff] using iSup_eapprox_apply hf

中文:
引理 iSup_coe_eapprox
  条件: (hf : Measurable f)
  结论: ⨆ n, ⇑(eapprox f n) = f
  证明: by
  simpa [funext_iff] using iSup_eapprox_apply hf

Depends on / 依赖: funext_iff, iSup_eapprox_apply
-/
lemma iSup_coe_eapprox (hf : Measurable f) : ⨆ n, ⇑(eapprox f n) = f := by
  simpa [funext_iff] using iSup_eapprox_apply hf

/--
theorem `eapprox_comp` / 定理 `eapprox_comp`

English:
theorem eapprox_comp
  statement: [MeasurableSpace γ] {f : γ -> Real>=0∞} {g : α -> γ} {n : Nat} (hf : Measurable f)
  proof: funext fun a => approx_comp a hf hg

中文:
定理 eapprox_comp
  结论: [MeasurableSpace γ] {f : γ -> 实数>=0∞} {g : α -> γ} {n : 自然数} (hf : Measurable f)
  证明: funext fun a => approx_comp a hf hg

Depends on / 依赖: approx_comp
-/
theorem eapprox_comp [MeasurableSpace γ] {f : γ -> Real>=0∞} {g : α -> γ} {n : Nat} (hf : Measurable f)
    (hg : Measurable g) : (eapprox (f ∘ g) n : α -> Real>=0∞) = (eapprox f n : γ ->ₛ Real>=0∞) ∘ g :=
  funext fun a => approx_comp a hf hg

/--
lemma `tendsto_eapprox` / 引理 `tendsto_eapprox`

English:
lemma tendsto_eapprox
  given: {f : α -> Real>=0∞} (hf_meas : Measurable f) (a : α)
  proof: by
  nth_rw 2 [← iSup_coe_eapprox hf_meas]
  rw [iSup_apply]
  exact tendsto_atTop_iSup fun _ _ hnm => monotone_eapprox f hnm a

中文:
引理 tendsto_eapprox
  条件: {f : α -> 实数>=0∞} (hf_meas : Measurable f) (a : α)
  证明: by
  nth_rw 2 [← iSup_coe_eapprox hf_meas]
  rw [iSup_apply]
  exact tendsto_atTop_iSup fun _ _ hnm => monotone_eapprox f hnm a

Depends on / 依赖: hf_meas, iSup_apply, iSup_coe_eapprox, monotone_eapprox, nth_rw, tendsto_atTop_iSup
-/
lemma tendsto_eapprox {f : α -> Real>=0∞} (hf_meas : Measurable f) (a : α) :
    Tendsto (fun n => eapprox f n a) atTop (𝓝 (f a)) := by
  nth_rw 2 [← iSup_coe_eapprox hf_meas]
  rw [iSup_apply]
  exact tendsto_atTop_iSup fun _ _ hnm => monotone_eapprox f hnm a

/--
Definition of `eapproxDiff` / `eapproxDiff` 的定义

English:
definition eapproxDiff
  signature: (f : α -> Real>=0∞)

中文:
定义 eapproxDiff
  签名: (f : α -> 实数>=0∞)
-/
def eapproxDiff (f : α -> Real>=0∞) : Nat -> α ->ₛ Real>=0
  | 0 => (eapprox f 0).map ENNReal.toNNReal
  | n + 1 => (eapprox f (n + 1) - eapprox f n).map ENNReal.toNNReal

/--
theorem `sum_eapproxDiff` / 定理 `sum_eapproxDiff`

English:
theorem sum_eapproxDiff
  given: (f : α -> Real>=0∞) (n : Nat) (a : α)
  proof: by
  induction n with
  | zero =>
    simp [eapproxDiff, (eapprox_lt_top f 0 a).ne]
  | succ n IH =>
    rw [Finset.sum_range_succ]; rw [IH]; rw [eapproxDiff]; rw [coe_map]; rw [Function.comp_apply]; rw [coe_sub]; rw [Pi.sub_apply]; rw [ENNReal.coe_toNNReal]; rw [add_tsub_cancel_of_le (monotone_eapp

中文:
定理 sum_eapproxDiff
  条件: (f : α -> 实数>=0∞) (n : 自然数) (a : α)
  证明: by
  induction n with
  | zero =>
    simp [eapproxDiff, (eapprox_lt_top f 0 a).ne]
  | succ n IH =>
    rw [Finset.sum_range_succ]; rw [IH]; rw [eapproxDiff]; rw [coe_map]; rw [Function.comp_apply]; rw [coe_sub]; rw [Pi.sub_apply]; rw [ENNReal.coe_toNNReal]; rw [add_tsub_cancel_of_le (monotone_eapp

Depends on / 依赖: ENNReal, ENNReal.coe_toNNReal, Finset, Finset.sum_range_succ, Function, Function.comp_apply, Nat.le_succ, Pi.sub_apply, add_tsub_cancel_of_le, coe_map, coe_sub, coe_toNNReal, comp_apply, eapproxDiff, eapprox_lt_top, le_self_add, le_succ, lt_of_le_of_lt, monotone_eapprox, sub_apply
-/
theorem sum_eapproxDiff (f : α -> Real>=0∞) (n : Nat) (a : α) :
    (∑ k in Finset.range (n + 1), (eapproxDiff f k a : Real>=0∞)) = eapprox f n a := by
  induction n with
  | zero =>
    simp [eapproxDiff, (eapprox_lt_top f 0 a).ne]
  | succ n IH =>
    rw [Finset.sum_range_succ]; rw [IH]; rw [eapproxDiff]; rw [coe_map]; rw [Function.comp_apply]; rw [coe_sub]; rw [Pi.sub_apply]; rw [ENNReal.coe_toNNReal]; rw [add_tsub_cancel_of_le (monotone_eapprox f (Nat.le_succ _) _)]
    apply (lt_of_le_of_lt _ (eapprox_lt_top f (n + 1) a)).ne
    rw [tsub_le_iff_right]
    exact le_self_add

/--
theorem `tsum_eapproxDiff` / 定理 `tsum_eapproxDiff`

English:
theorem tsum_eapproxDiff
  given: (f : α -> Real>=0∞) (hf : Measurable f) (a : α)
  proof: by
  simp_rw [ENNReal.tsum_eq_iSup_nat' (tendsto_add_atTop_nat 1), sum_eapproxDiff,
    iSup_eapprox_apply hf a]

中文:
定理 tsum_eapproxDiff
  条件: (f : α -> 实数>=0∞) (hf : Measurable f) (a : α)
  证明: by
  simp_rw [ENNReal.tsum_eq_iSup_nat' (tendsto_add_atTop_nat 1), sum_eapproxDiff,
    iSup_eapprox_apply hf a]

Depends on / 依赖: ENNReal, ENNReal.tsum_eq_iSup_nat, iSup_eapprox_apply, simp_rw, sum_eapproxDiff, tendsto_add_atTop_nat, tsum_eq_iSup_nat
-/
theorem tsum_eapproxDiff (f : α -> Real>=0∞) (hf : Measurable f) (a : α) :
    (∑' n, (eapproxDiff f n a : Real>=0∞)) = f a := by
  simp_rw [ENNReal.tsum_eq_iSup_nat' (tendsto_add_atTop_nat 1), sum_eapproxDiff,
    iSup_eapprox_apply hf a]

end EApprox

end Measurable

section Measure

variable {m : MeasurableSpace α} {μ ν : Measure α}

/--
Definition of `lintegral` / `lintegral` 的定义

English:
definition lintegral
  signature: {_m : MeasurableSpace α} (f : α ->ₛ Real>=0∞) (μ : Measure α)
  body: ∑ x in f.range, x * μ (f ⁻¹' {x})

中文:
定义 lintegral
  签名: {_m : MeasurableSpace α} (f : α ->ₛ 实数>=0∞) (μ : Measure α)
  定义体: ∑ x in f.range, x * μ (f ⁻¹' {x})

Depends on / 依赖: f.range
-/
def lintegral {_m : MeasurableSpace α} (f : α ->ₛ Real>=0∞) (μ : Measure α) : Real>=0∞ :=
  ∑ x in f.range, x * μ (f ⁻¹' {x})

/--
theorem `lintegral_eq_of_subset` / 定理 `lintegral_eq_of_subset`

English:
theorem lintegral_eq_of_subset
  statement: (f : α ->ₛ Real>=0∞) {s : Finset Real>=0∞}
  proof: by
  refine Finset.sum_bij_ne_zero (fun r _ _ => r) ?_ ?_ ?_ ?_
  · simpa only [forall_mem_range, mul_ne_zero_iff, and_imp]
  · intros
    assumption
  · intro b _ hb
    refine ⟨b, ?_, hb, rfl⟩
    rw [mem_range]; rw [← preimage_singleton_nonempty]
    exact nonempty_of_measure_ne_zero (mul_ne_zero

中文:
定理 lintegral_eq_of_subset
  结论: (f : α ->ₛ 实数>=0∞) {s : Finset 实数>=0∞}
  证明: by
  refine Finset.sum_bij_ne_zero (fun r _ _ => r) ?_ ?_ ?_ ?_
  · simpa only [forall_mem_range, mul_ne_zero_iff, and_imp]
  · intros
    assumption
  · intro b _ hb
    refine ⟨b, ?_, hb, rfl⟩
    rw [mem_range]; rw [← preimage_singleton_nonempty]
    exact nonempty_of_measure_ne_zero (mul_ne_zero

Depends on / 依赖: Finset, Finset.sum_bij_ne_zero, and_imp, forall_mem_range, intros, mem_range, mul_ne_zero_iff, nonempty_of_measure_ne_zero, preimage_singleton_nonempty, sum_bij_ne_zero
-/
theorem lintegral_eq_of_subset (f : α ->ₛ Real>=0∞) {s : Finset Real>=0∞}
    (hs : forall x, f x != 0 -> μ (f ⁻¹' {f x}) != 0 -> f x in s) :
    f.lintegral μ = ∑ x in s, x * μ (f ⁻¹' {x}) := by
  refine Finset.sum_bij_ne_zero (fun r _ _ => r) ?_ ?_ ?_ ?_
  · simpa only [forall_mem_range, mul_ne_zero_iff, and_imp]
  · intros
    assumption
  · intro b _ hb
    refine ⟨b, ?_, hb, rfl⟩
    rw [mem_range]; rw [← preimage_singleton_nonempty]
    exact nonempty_of_measure_ne_zero (mul_ne_zero_iff.1 hb).2
  · intros
    rfl

/--
theorem `lintegral_eq_of_subset'` / 定理 `lintegral_eq_of_subset'`

English:
theorem lintegral_eq_of_subset'
  given: (f : α ->ₛ Real>=0∞) {s : Finset Real>=0∞} (hs : f.range \ {0} subseteq s)
  proof: f.lintegral_eq_of_subset fun x hfx _ =>
hs Finset.mem_sdiff.2 ⟨f.mem_range_self x, mt Finset.mem_singleton.1 hfx⟩

中文:
定理 lintegral_eq_of_subset'
  条件: (f : α ->ₛ 实数>=0∞) {s : Finset 实数>=0∞} (hs : f.range \ {0} subseteq s)
  证明: f.lintegral_eq_of_subset fun x hfx _ =>
hs Finset.mem_sdiff.2 ⟨f.mem_range_self x, mt Finset.mem_singleton.1 hfx⟩

Depends on / 依赖: Finset, Finset.mem_sdiff, Finset.mem_singleton, f.lintegral_eq_of_subset, f.mem_range_self, lintegral_eq_of_subset, mem_range_self, mem_sdiff, mem_singleton
-/
theorem lintegral_eq_of_subset' (f : α ->ₛ Real>=0∞) {s : Finset Real>=0∞} (hs : f.range \ {0} subseteq s) :
    f.lintegral μ = ∑ x in s, x * μ (f ⁻¹' {x}) :=
  f.lintegral_eq_of_subset fun x hfx _ =>
hs Finset.mem_sdiff.2 ⟨f.mem_range_self x, mt Finset.mem_singleton.1 hfx⟩

/--
theorem `map_lintegral` / 定理 `map_lintegral`

English:
theorem map_lintegral
  given: (g : β -> Real>=0∞) (f : α ->ₛ β)
  proof: by
  simp only [lintegral, range_map]
  refine Finset.sum_image' _ fun b hb => ?_
  rcases mem_range.1 hb with ⟨a, rfl⟩
  rw [map_preimage_singleton]; rw [← f.sum_measure_preimage_singleton]; rw [Finset.mul_sum]
  refine Finset.sum_congr ?_ ?_
  · congr
  · grind

中文:
定理 map_lintegral
  条件: (g : β -> 实数>=0∞) (f : α ->ₛ β)
  证明: by
  simp only [lintegral, range_map]
  refine Finset.sum_image' _ fun b hb => ?_
  rcases mem_range.1 hb with ⟨a, rfl⟩
  rw [map_preimage_singleton]; rw [← f.sum_measure_preimage_singleton]; rw [Finset.mul_sum]
  refine Finset.sum_congr ?_ ?_
  · congr
  · grind

Depends on / 依赖: Finset, Finset.mul_sum, Finset.sum_congr, Finset.sum_image, f.sum_measure_preimage_singleton, lintegral, map_preimage_singleton, mem_range, mul_sum, range_map, sum_congr, sum_image, sum_measure_preimage_singleton
-/
theorem map_lintegral (g : β -> Real>=0∞) (f : α ->ₛ β) :
    (f.map g).lintegral μ = ∑ x in f.range, g x * μ (f ⁻¹' {x}) := by
  simp only [lintegral, range_map]
  refine Finset.sum_image' _ fun b hb => ?_
  rcases mem_range.1 hb with ⟨a, rfl⟩
  rw [map_preimage_singleton]; rw [← f.sum_measure_preimage_singleton]; rw [Finset.mul_sum]
  refine Finset.sum_congr ?_ ?_
  · congr
  · grind

/--
theorem `add_lintegral` / 定理 `add_lintegral`

English:
theorem add_lintegral
  given: (f g : α ->ₛ Real>=0∞)
  statement: (f + g).lintegral μ = f.lintegral μ + g.lintegral μ
  proof: calc
    (f + g).lintegral μ =
        ∑ x in (pair f g).range, (x.1 * μ (pair f g ⁻¹' {x}) + x.2 * μ (pair f g ⁻¹' {x})) := by
      rw [add_eq_map₂]; rw [map_lintegral]; exact Finset.sum_congr rfl fun a _ => add_mul _ _ _
    _ = (∑ x in (pair f g).range, x.1 * μ (pair f g ⁻¹' {x})) +
          ∑ 

中文:
定理 add_lintegral
  条件: (f g : α ->ₛ 实数>=0∞)
  结论: (f + g).lintegral μ = f.lintegral μ + g.lintegral μ
  证明: calc
    (f + g).lintegral μ =
        ∑ x in (pair f g).range, (x.1 * μ (pair f g ⁻¹' {x}) + x.2 * μ (pair f g ⁻¹' {x})) := by
      rw [add_eq_map₂]; rw [map_lintegral]; exact Finset.sum_congr rfl fun a _ => add_mul _ _ _
    _ = (∑ x in (pair f g).range, x.1 * μ (pair f g ⁻¹' {x})) +
          ∑ 

Depends on / 依赖: Finset, Finset.sum_add_distrib, Finset.sum_congr, Prod.fst, Prod.snd, add_mul, lintegral, map_lintegral, sum_add_distrib, sum_congr
-/
theorem add_lintegral (f g : α ->ₛ Real>=0∞) : (f + g).lintegral μ = f.lintegral μ + g.lintegral μ :=
  calc
    (f + g).lintegral μ =
        ∑ x in (pair f g).range, (x.1 * μ (pair f g ⁻¹' {x}) + x.2 * μ (pair f g ⁻¹' {x})) := by
      rw [add_eq_map₂]; rw [map_lintegral]; exact Finset.sum_congr rfl fun a _ => add_mul _ _ _
    _ = (∑ x in (pair f g).range, x.1 * μ (pair f g ⁻¹' {x})) +
          ∑ x in (pair f g).range, x.2 * μ (pair f g ⁻¹' {x}) := by
      rw [Finset.sum_add_distrib]
    _ = ((pair f g).map Prod.fst).lintegral μ + ((pair f g).map Prod.snd).lintegral μ := by
      rw [map_lintegral]; rw [map_lintegral]
    _ = lintegral f μ + lintegral g μ := rfl

/--
theorem `const_mul_lintegral` / 定理 `const_mul_lintegral`

English:
theorem const_mul_lintegral
  given: (f : α ->ₛ Real>=0∞) (x : Real>=0∞)
  proof: calc
    (f.map fun a => x * a).lintegral μ = ∑ r in f.range, x * r * μ (f ⁻¹' {r}) := map_lintegral _ _
    _ = x * ∑ r in f.range, r * μ (f ⁻¹' {r}) := by simp_rw [Finset.mul_sum, mul_assoc]

中文:
定理 const_mul_lintegral
  条件: (f : α ->ₛ 实数>=0∞) (x : 实数>=0∞)
  证明: calc
    (f.map fun a => x * a).lintegral μ = ∑ r in f.range, x * r * μ (f ⁻¹' {r}) := map_lintegral _ _
    _ = x * ∑ r in f.range, r * μ (f ⁻¹' {r}) := by simp_rw [Finset.mul_sum, mul_assoc]

Depends on / 依赖: Finset, Finset.mul_sum, f.map, f.range, lintegral, map_lintegral, mul_assoc, mul_sum, simp_rw
-/
theorem const_mul_lintegral (f : α ->ₛ Real>=0∞) (x : Real>=0∞) :
    (const α x * f).lintegral μ = x * f.lintegral μ :=
  calc
    (f.map fun a => x * a).lintegral μ = ∑ r in f.range, x * r * μ (f ⁻¹' {r}) := map_lintegral _ _
    _ = x * ∑ r in f.range, r * μ (f ⁻¹' {r}) := by simp_rw [Finset.mul_sum, mul_assoc]

/--
Definition of `lintegralₗ` / `lintegralₗ` 的定义

English:
definition lintegralₗ
  signature: {m : MeasurableSpace α}
  body: { toFun := lintegral f
      map_add' := by simp [lintegral, mul_add, Finset.sum_add_distrib]
      map_smul' := fun c μ => by
        simp [lintegral, mul_left_comm _ c, Finset.mul_sum, Measure.smul_apply c] }
  map_add' f g := LinearMap.ext fun _ => add_lintegral f g
  map_smul' c f := LinearMap.e

中文:
定义 lintegralₗ
  签名: {m : MeasurableSpace α}
  定义体: { toFun := lintegral f
      map_add' := by simp [lintegral, mul_add, Finset.sum_add_distrib]
      map_smul' := fun c μ => by
        simp [lintegral, mul_left_comm _ c, Finset.mul_sum, Measure.smul_apply c] }
  map_add' f g := LinearMap.ext fun _ => add_lintegral f g
  map_smul' c f := LinearMap.e

Depends on / 依赖: Finset, Finset.mul_sum, Finset.sum_add_distrib, LinearMap, LinearMap.ext, Measure, Measure.smul_apply, add_lintegral, const_mul_lintegral, lintegral, map_add, map_smul, mul_add, mul_left_comm, mul_sum, smul_apply, sum_add_distrib
-/
def lintegralₗ {m : MeasurableSpace α} : (α ->ₛ Real>=0∞) ->ₗ[Real>=0∞] Measure α ->ₗ[Real>=0∞] Real>=0∞ where
  toFun f :=
    { toFun := lintegral f
      map_add' := by simp [lintegral, mul_add, Finset.sum_add_distrib]
      map_smul' := fun c μ => by
        simp [lintegral, mul_left_comm _ c, Finset.mul_sum, Measure.smul_apply c] }
  map_add' f g := LinearMap.ext fun _ => add_lintegral f g
  map_smul' c f := LinearMap.ext fun _ => const_mul_lintegral f c

@[simp]
/--
theorem `zero_lintegral` / 定理 `zero_lintegral`

English:
theorem zero_lintegral
  statement: (0 : α ->ₛ Real>=0∞).lintegral μ = 0
  proof: LinearMap.ext_iff.1 lintegralₗ.map_zero μ

中文:
定理 zero_lintegral
  结论: (0 : α ->ₛ 实数>=0∞).lintegral μ = 0
  证明: LinearMap.ext_iff.1 lintegralₗ.map_zero μ

Depends on / 依赖: LinearMap, LinearMap.ext_iff, ext_iff, map_zero
-/
theorem zero_lintegral : (0 : α ->ₛ Real>=0∞).lintegral μ = 0 :=
  LinearMap.ext_iff.1 lintegralₗ.map_zero μ

/--
theorem `lintegral_add` / 定理 `lintegral_add`

English:
theorem lintegral_add
  given: {ν} (f : α ->ₛ Real>=0∞)
  statement: f.lintegral (μ + ν) = f.lintegral μ + f.lintegral ν
  proof: (lintegralₗ f).map_add μ ν

中文:
定理 lintegral_add
  条件: {ν} (f : α ->ₛ 实数>=0∞)
  结论: f.lintegral (μ + ν) = f.lintegral μ + f.lintegral ν
  证明: (lintegralₗ f).map_add μ ν

Depends on / 依赖: map_add
-/
theorem lintegral_add {ν} (f : α ->ₛ Real>=0∞) : f.lintegral (μ + ν) = f.lintegral μ + f.lintegral ν :=
  (lintegralₗ f).map_add μ ν

/--
theorem `lintegral_smul` / 定理 `lintegral_smul`

English:
theorem lintegral_smul
  statement: {R : Type*} [SMul R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞]
  proof: by
  simpa only [smul_one_smul] using! (lintegralₗ f).map_smul (c • 1) μ

@[simp]

中文:
定理 lintegral_smul
  结论: {R : 类型} [SMul R 实数>=0∞] [IsScalarTower R 实数>=0∞ 实数>=0∞]
  证明: by
  simpa only [smul_one_smul] using! (lintegralₗ f).map_smul (c • 1) μ

@[simp]

Depends on / 依赖: map_smul, smul_one_smul
-/
theorem lintegral_smul {R : Type*} [SMul R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞]
    (f : α ->ₛ Real>=0∞) (c : R) : f.lintegral (c • μ) = c • f.lintegral μ := by
  simpa only [smul_one_smul] using! (lintegralₗ f).map_smul (c • 1) μ

@[simp]
/--
theorem `lintegral_zero` / 定理 `lintegral_zero`

English:
theorem lintegral_zero
  given: [MeasurableSpace α] (f : α ->ₛ Real>=0∞)
  statement: f.lintegral 0 = 0
  proof: (lintegralₗ f).map_zero

中文:
定理 lintegral_zero
  条件: [MeasurableSpace α] (f : α ->ₛ 实数>=0∞)
  结论: f.lintegral 0 = 0
  证明: (lintegralₗ f).map_zero

Depends on / 依赖: map_zero
-/
theorem lintegral_zero [MeasurableSpace α] (f : α ->ₛ Real>=0∞) : f.lintegral 0 = 0 :=
  (lintegralₗ f).map_zero

/--
theorem `lintegral_finsetSum` / 定理 `lintegral_finsetSum`

English:
theorem lintegral_finsetSum
  given: {ι} (f : α ->ₛ Real>=0∞) (μ : ι -> Measure α) (s : Finset ι)
  proof: map_sum (lintegralₗ f) ..

@[deprecated (since := "2026-04-08")] alias lintegral_finset_sum := lintegral_finsetSum

中文:
定理 lintegral_finsetSum
  条件: {ι} (f : α ->ₛ 实数>=0∞) (μ : ι -> Measure α) (s : Finset ι)
  证明: map_sum (lintegralₗ f) ..

@[deprecated (since := "2026-04-08")] alias lintegral_finset_sum := lintegral_finsetSum

Depends on / 依赖: map_sum
-/
theorem lintegral_finsetSum {ι} (f : α ->ₛ Real>=0∞) (μ : ι -> Measure α) (s : Finset ι) :
    f.lintegral (∑ i in s, μ i) = ∑ i in s, f.lintegral (μ i) :=
  map_sum (lintegralₗ f) ..

@[deprecated (since := "2026-04-08")] alias lintegral_finset_sum := lintegral_finsetSum

/--
theorem `lintegral_sum` / 定理 `lintegral_sum`

English:
theorem lintegral_sum
  given: {m : MeasurableSpace α} {ι} (f : α ->ₛ Real>=0∞) (μ : ι -> Measure α)
  proof: by
  simp only [lintegral, Measure.sum_apply, f.measurableSet_preimage, ← Finset.tsum_subtype, ←
    ENNReal.tsum_mul_left]
  apply ENNReal.tsum_comm

中文:
定理 lintegral_sum
  条件: {m : MeasurableSpace α} {ι} (f : α ->ₛ 实数>=0∞) (μ : ι -> Measure α)
  证明: by
  simp only [lintegral, Measure.sum_apply, f.measurableSet_preimage, ← Finset.tsum_subtype, ←
    ENNReal.tsum_mul_left]
  apply ENNReal.tsum_comm

Depends on / 依赖: ENNReal, ENNReal.tsum_comm, ENNReal.tsum_mul_left, Finset, Finset.tsum_subtype, Measure, Measure.sum_apply, f.measurableSet_preimage, lintegral, measurableSet_preimage, sum_apply, tsum_comm, tsum_mul_left, tsum_subtype
-/
theorem lintegral_sum {m : MeasurableSpace α} {ι} (f : α ->ₛ Real>=0∞) (μ : ι -> Measure α) :
    f.lintegral (Measure.sum μ) = ∑' i, f.lintegral (μ i) := by
  simp only [lintegral, Measure.sum_apply, f.measurableSet_preimage, ← Finset.tsum_subtype, ←
    ENNReal.tsum_mul_left]
  apply ENNReal.tsum_comm

/--
theorem `restrict_lintegral` / 定理 `restrict_lintegral`

English:
theorem restrict_lintegral
  given: (f : α ->ₛ Real>=0∞) {s : Set α} (hs : MeasurableSet s)
  proof: by
  classical
  exact calc
    (restrict f s).lintegral μ = ∑ r in f.range, r * μ (restrict f s ⁻¹' {r}) :=
      lintegral_eq_of_subset _ fun x hx =>
        if hxs : x in s then fun _ => by
          simp only [f.restrict_apply hs, indicator_of_mem hxs, mem_range_self]
else False.elim hx by simp 

中文:
定理 restrict_lintegral
  条件: (f : α ->ₛ 实数>=0∞) {s : Set α} (hs : MeasurableSet s)
  证明: by
  classical
  exact calc
    (restrict f s).lintegral μ = ∑ r in f.range, r * μ (restrict f s ⁻¹' {r}) :=
      lintegral_eq_of_subset _ fun x hx =>
        if hxs : x in s then fun _ => by
          simp only [f.restrict_apply hs, indicator_of_mem hxs, mem_range_self]
else False.elim hx by simp 

Depends on / 依赖: False.elim, Finset, Finset.sum_congr, classical, f.range, f.restrict_apply, forall_mem_range, indicator_of_mem, inter_comm, lintegral, lintegral_eq_of_subset, mem_range_self, restrict, restrict_apply, restrict_preimage_singleton, sum_congr, zero_mul
-/
theorem restrict_lintegral (f : α ->ₛ Real>=0∞) {s : Set α} (hs : MeasurableSet s) :
    (restrict f s).lintegral μ = ∑ r in f.range, r * μ (f ⁻¹' {r} inter s) := by
  classical
  exact calc
    (restrict f s).lintegral μ = ∑ r in f.range, r * μ (restrict f s ⁻¹' {r}) :=
      lintegral_eq_of_subset _ fun x hx =>
        if hxs : x in s then fun _ => by
          simp only [f.restrict_apply hs, indicator_of_mem hxs, mem_range_self]
else False.elim hx by simp [*]
    _ = ∑ r in f.range, r * μ (f ⁻¹' {r} inter s) :=
Finset.sum_congr rfl
        forall_mem_range.2 fun b =>
          if hb : f b = 0 then by simp only [hb, zero_mul]
          else by rw [restrict_preimage_singleton _ hs hb, inter_comm]

/--
theorem `lintegral_restrict` / 定理 `lintegral_restrict`

English:
theorem lintegral_restrict
  given: {m : MeasurableSpace α} (f : α ->ₛ Real>=0∞) (s : Set α) (μ : Measure α)
  proof: by
  simp only [lintegral, Measure.restrict_apply, f.measurableSet_preimage]

中文:
定理 lintegral_restrict
  条件: {m : MeasurableSpace α} (f : α ->ₛ 实数>=0∞) (s : Set α) (μ : Measure α)
  证明: by
  simp only [lintegral, Measure.restrict_apply, f.measurableSet_preimage]

Depends on / 依赖: Measure, Measure.restrict_apply, f.measurableSet_preimage, lintegral, measurableSet_preimage, restrict_apply
-/
theorem lintegral_restrict {m : MeasurableSpace α} (f : α ->ₛ Real>=0∞) (s : Set α) (μ : Measure α) :
    f.lintegral (μ.restrict s) = ∑ y in f.range, y * μ (f ⁻¹' {y} inter s) := by
  simp only [lintegral, Measure.restrict_apply, f.measurableSet_preimage]

/--
theorem `restrict_lintegral_eq_lintegral_restrict` / 定理 `restrict_lintegral_eq_lintegral_restrict`

English:
theorem restrict_lintegral_eq_lintegral_restrict
  statement: (f : α ->ₛ Real>=0∞) {s : Set α}
  proof: by
  rw [f.restrict_lintegral hs]; rw [lintegral_restrict]

中文:
定理 restrict_lintegral_eq_lintegral_restrict
  结论: (f : α ->ₛ 实数>=0∞) {s : Set α}
  证明: by
  rw [f.restrict_lintegral hs]; rw [lintegral_restrict]

Depends on / 依赖: f.restrict_lintegral, lintegral_restrict, restrict_lintegral
-/
theorem restrict_lintegral_eq_lintegral_restrict (f : α ->ₛ Real>=0∞) {s : Set α}
    (hs : MeasurableSet s) : (restrict f s).lintegral μ = f.lintegral (μ.restrict s) := by
  rw [f.restrict_lintegral hs]; rw [lintegral_restrict]

/--
theorem `lintegral_restrict_iUnion_of_directed` / 定理 `lintegral_restrict_iUnion_of_directed`

English:
theorem lintegral_restrict_iUnion_of_directed
  statement: {ι : Type*} [Countable ι]
  proof: by
  simp only [lintegral, Measure.restrict_iUnion_apply_eq_iSup hd (measurableSet_preimage ..),
    ENNReal.mul_iSup]
  refine finsetSum_iSup fun i j => (hd i j).imp fun k ⟨hik, hjk⟩ => fun a => ?_
  constructor <;> gcongr

中文:
定理 lintegral_restrict_iUnion_of_directed
  结论: {ι : 类型} [Countable ι]
  证明: by
  simp only [lintegral, Measure.restrict_iUnion_apply_eq_iSup hd (measurableSet_preimage ..),
    ENNReal.mul_iSup]
  refine finsetSum_iSup fun i j => (hd i j).imp fun k ⟨hik, hjk⟩ => fun a => ?_
  constructor <;> gcongr

Depends on / 依赖: ENNReal, ENNReal.mul_iSup, Measure, Measure.restrict_iUnion_apply_eq_iSup, finsetSum_iSup, lintegral, measurableSet_preimage, mul_iSup, restrict_iUnion_apply_eq_iSup
-/
theorem lintegral_restrict_iUnion_of_directed {ι : Type*} [Countable ι]
    (f : α ->ₛ Real>=0∞) {s : ι -> Set α} (hd : Directed (· subseteq ·) s) (μ : Measure α) :
    f.lintegral (μ.restrict (⋃ i, s i)) = ⨆ i, f.lintegral (μ.restrict (s i)) := by
  simp only [lintegral, Measure.restrict_iUnion_apply_eq_iSup hd (measurableSet_preimage ..),
    ENNReal.mul_iSup]
  refine finsetSum_iSup fun i j => (hd i j).imp fun k ⟨hik, hjk⟩ => fun a => ?_
  constructor <;> gcongr

/--
theorem `const_lintegral` / 定理 `const_lintegral`

English:
theorem const_lintegral
  given: (c : Real>=0∞)
  statement: (const α c).lintegral μ = c * μ univ
  proof: by
  rw [lintegral]
  cases isEmpty_or_nonempty α
  · simp [μ.eq_zero_of_isEmpty]
  · simp only [range_const, coe_const, Finset.sum_singleton]
    unfold Function.const; rw [preimage_const_of_mem (mem_singleton c)]

中文:
定理 const_lintegral
  条件: (c : 实数>=0∞)
  结论: (const α c).lintegral μ = c * μ univ
  证明: by
  rw [lintegral]
  cases isEmpty_or_nonempty α
  · simp [μ.eq_zero_of_isEmpty]
  · simp only [range_const, coe_const, Finset.sum_singleton]
    unfold Function.const; rw [preimage_const_of_mem (mem_singleton c)]

Depends on / 依赖: Finset, Finset.sum_singleton, Function, Function.const, coe_const, eq_zero_of_isEmpty, isEmpty_or_nonempty, lintegral, mem_singleton, preimage_const_of_mem, range_const, sum_singleton
-/
theorem const_lintegral (c : Real>=0∞) : (const α c).lintegral μ = c * μ univ := by
  rw [lintegral]
  cases isEmpty_or_nonempty α
  · simp [μ.eq_zero_of_isEmpty]
  · simp only [range_const, coe_const, Finset.sum_singleton]
    unfold Function.const; rw [preimage_const_of_mem (mem_singleton c)]

/--
theorem `const_lintegral_restrict` / 定理 `const_lintegral_restrict`

English:
theorem const_lintegral_restrict
  given: (c : Real>=0∞) (s : Set α)
  proof: by
  rw [const_lintegral]; rw [Measure.restrict_apply MeasurableSet.univ]; rw [univ_inter]

中文:
定理 const_lintegral_restrict
  条件: (c : 实数>=0∞) (s : Set α)
  证明: by
  rw [const_lintegral]; rw [Measure.restrict_apply MeasurableSet.univ]; rw [univ_inter]

Depends on / 依赖: MeasurableSet, MeasurableSet.univ, Measure, Measure.restrict_apply, const_lintegral, restrict_apply, univ_inter
-/
theorem const_lintegral_restrict (c : Real>=0∞) (s : Set α) :
    (const α c).lintegral (μ.restrict s) = c * μ s := by
  rw [const_lintegral]; rw [Measure.restrict_apply MeasurableSet.univ]; rw [univ_inter]

/--
theorem `restrict_const_lintegral` / 定理 `restrict_const_lintegral`

English:
theorem restrict_const_lintegral
  given: (c : Real>=0∞) {s : Set α} (hs : MeasurableSet s)
  proof: by
  rw [restrict_lintegral_eq_lintegral_restrict _ hs]; rw [const_lintegral_restrict]

中文:
定理 restrict_const_lintegral
  条件: (c : 实数>=0∞) {s : Set α} (hs : MeasurableSet s)
  证明: by
  rw [restrict_lintegral_eq_lintegral_restrict _ hs]; rw [const_lintegral_restrict]

Depends on / 依赖: const_lintegral_restrict, restrict_lintegral_eq_lintegral_restrict
-/
theorem restrict_const_lintegral (c : Real>=0∞) {s : Set α} (hs : MeasurableSet s) :
    ((const α c).restrict s).lintegral μ = c * μ s := by
  rw [restrict_lintegral_eq_lintegral_restrict _ hs]; rw [const_lintegral_restrict]

/--
theorem `lintegral_mono_fun` / 定理 `lintegral_mono_fun`

English:
theorem lintegral_mono_fun
  given: {f g : α ->ₛ Real>=0∞} (h : f <= g)
  statement: f.lintegral μ <= g.lintegral μ
  proof: by
  refine Monotone.of_left_le_map_sup (f := (lintegral · μ)) (fun f g => ?_) h
  calc
    f.lintegral μ = ((pair f g).map Prod.fst).lintegral μ := by rw [map_fst_pair]
    _ <= ((pair f g).map fun p => p.1 ⊔ p.2).lintegral μ := by
      simp only [map_lintegral]
      gcongr
      exact le_sup_lef

中文:
定理 lintegral_mono_fun
  条件: {f g : α ->ₛ 实数>=0∞} (h : f <= g)
  结论: f.lintegral μ <= g.lintegral μ
  证明: by
  refine Monotone.of_left_le_map_sup (f := (lintegral · μ)) (fun f g => ?_) h
  calc
    f.lintegral μ = ((pair f g).map Prod.fst).lintegral μ := by rw [map_fst_pair]
    _ <= ((pair f g).map fun p => p.1 ⊔ p.2).lintegral μ := by
      simp only [map_lintegral]
      gcongr
      exact le_sup_lef

Depends on / 依赖: Monotone, Monotone.of_left_le_map_sup, Prod.fst, f.lintegral, le_sup_left, lintegral, map_fst_pair, map_lintegral, of_left_le_map_sup
-/
theorem lintegral_mono_fun {f g : α ->ₛ Real>=0∞} (h : f <= g) : f.lintegral μ <= g.lintegral μ := by
  refine Monotone.of_left_le_map_sup (f := (lintegral · μ)) (fun f g => ?_) h
  calc
    f.lintegral μ = ((pair f g).map Prod.fst).lintegral μ := by rw [map_fst_pair]
    _ <= ((pair f g).map fun p => p.1 ⊔ p.2).lintegral μ := by
      simp only [map_lintegral]
      gcongr
      exact le_sup_left

/--
theorem `le_sup_lintegral` / 定理 `le_sup_lintegral`

English:
theorem le_sup_lintegral
  given: (f g : α ->ₛ Real>=0∞)
  statement: f.lintegral μ ⊔ g.lintegral μ <= (f ⊔ g).lintegral μ
  proof: Monotone.le_map_sup (fun _ _ => lintegral_mono_fun) f g

中文:
定理 le_sup_lintegral
  条件: (f g : α ->ₛ 实数>=0∞)
  结论: f.lintegral μ ⊔ g.lintegral μ <= (f ⊔ g).lintegral μ
  证明: Monotone.le_map_sup (fun _ _ => lintegral_mono_fun) f g

Depends on / 依赖: Monotone, Monotone.le_map_sup, le_map_sup, lintegral_mono_fun
-/
theorem le_sup_lintegral (f g : α ->ₛ Real>=0∞) : f.lintegral μ ⊔ g.lintegral μ <= (f ⊔ g).lintegral μ :=
  Monotone.le_map_sup (fun _ _ => lintegral_mono_fun) f g

/--
theorem `lintegral_mono_measure` / 定理 `lintegral_mono_measure`

English:
theorem lintegral_mono_measure
  given: {f : α ->ₛ Real>=0∞} (h : μ <= ν)
  statement: f.lintegral μ <= f.lintegral ν
  proof: by
  simp only [lintegral]
  gcongr

中文:
定理 lintegral_mono_measure
  条件: {f : α ->ₛ 实数>=0∞} (h : μ <= ν)
  结论: f.lintegral μ <= f.lintegral ν
  证明: by
  simp only [lintegral]
  gcongr

Depends on / 依赖: lintegral
-/
theorem lintegral_mono_measure {f : α ->ₛ Real>=0∞} (h : μ <= ν) : f.lintegral μ <= f.lintegral ν := by
  simp only [lintegral]
  gcongr

/-- `SimpleFunc.lintegral` is monotone both in function and in measure. -/
@[mono, gcongr]
/--
theorem `lintegral_mono` / 定理 `lintegral_mono`

English:
theorem lintegral_mono
  given: {f g : α ->ₛ Real>=0∞} (hfg : f <= g) (hμν : μ <= ν)
  proof: (lintegral_mono_fun hfg).trans (lintegral_mono_measure hμν)

中文:
定理 lintegral_mono
  条件: {f g : α ->ₛ 实数>=0∞} (hfg : f <= g) (hμν : μ <= ν)
  证明: (lintegral_mono_fun hfg).trans (lintegral_mono_measure hμν)

Depends on / 依赖: lintegral_mono_fun, lintegral_mono_measure
-/
theorem lintegral_mono {f g : α ->ₛ Real>=0∞} (hfg : f <= g) (hμν : μ <= ν) :
    f.lintegral μ <= g.lintegral ν :=
  (lintegral_mono_fun hfg).trans (lintegral_mono_measure hμν)

/--
theorem `lintegral_eq_of_measure_preimage` / 定理 `lintegral_eq_of_measure_preimage`

English:
theorem lintegral_eq_of_measure_preimage
  statement: [MeasurableSpace β] {f : α ->ₛ Real>=0∞} {g : β ->ₛ Real>=0∞}
  proof: by
  simp only [lintegral, ← H]
  apply lintegral_eq_of_subset
  simp only [H]
  intros
  exact mem_range_of_measure_ne_zero ‹_›

中文:
定理 lintegral_eq_of_measure_preimage
  结论: [MeasurableSpace β] {f : α ->ₛ 实数>=0∞} {g : β ->ₛ 实数>=0∞}
  证明: by
  simp only [lintegral, ← H]
  apply lintegral_eq_of_subset
  simp only [H]
  intros
  exact mem_range_of_measure_ne_zero ‹_›

Depends on / 依赖: intros, lintegral, lintegral_eq_of_subset, mem_range_of_measure_ne_zero
-/
theorem lintegral_eq_of_measure_preimage [MeasurableSpace β] {f : α ->ₛ Real>=0∞} {g : β ->ₛ Real>=0∞}
    {ν : Measure β} (H : forall y, μ (f ⁻¹' {y}) = ν (g ⁻¹' {y})) : f.lintegral μ = g.lintegral ν := by
  simp only [lintegral, ← H]
  apply lintegral_eq_of_subset
  simp only [H]
  intros
  exact mem_range_of_measure_ne_zero ‹_›

/--
theorem `lintegral_congr` / 定理 `lintegral_congr`

English:
theorem lintegral_congr
  given: {f g : α ->ₛ Real>=0∞} (h : f =ᵐ[μ] g)
  statement: f.lintegral μ = g.lintegral μ
  proof: lintegral_eq_of_measure_preimage fun y =>
measure_congr Eventually.set_eq h.mono fun x hx => by simp [hx]

中文:
定理 lintegral_congr
  条件: {f g : α ->ₛ 实数>=0∞} (h : f =ᵐ[μ] g)
  结论: f.lintegral μ = g.lintegral μ
  证明: lintegral_eq_of_measure_preimage fun y =>
measure_congr Eventually.set_eq h.mono fun x hx => by simp [hx]

Depends on / 依赖: Eventually, Eventually.set_eq, h.mono, lintegral_eq_of_measure_preimage, measure_congr, set_eq
-/
theorem lintegral_congr {f g : α ->ₛ Real>=0∞} (h : f =ᵐ[μ] g) : f.lintegral μ = g.lintegral μ :=
  lintegral_eq_of_measure_preimage fun y =>
measure_congr Eventually.set_eq h.mono fun x hx => by simp [hx]

/--
theorem `lintegral_map'` / 定理 `lintegral_map'`

English:
theorem lintegral_map'
  statement: {β} [MeasurableSpace β] {μ' : Measure β} (f : α ->ₛ Real>=0∞) (g : β ->ₛ Real>=0∞)
  proof: lintegral_eq_of_measure_preimage fun y => by
    simp only [preimage, eq]
    exact (h (g ⁻¹' {y}) (g.measurableSet_preimage _)).symm

中文:
定理 lintegral_map'
  结论: {β} [MeasurableSpace β] {μ' : Measure β} (f : α ->ₛ 实数>=0∞) (g : β ->ₛ 实数>=0∞)
  证明: lintegral_eq_of_measure_preimage fun y => by
    simp only [preimage, eq]
    exact (h (g ⁻¹' {y}) (g.measurableSet_preimage _)).symm

Depends on / 依赖: g.measurableSet_preimage, lintegral_eq_of_measure_preimage, measurableSet_preimage, preimage
-/
theorem lintegral_map' {β} [MeasurableSpace β] {μ' : Measure β} (f : α ->ₛ Real>=0∞) (g : β ->ₛ Real>=0∞)
    (m' : α -> β) (eq : forall a, f a = g (m' a)) (h : forall s, MeasurableSet s -> μ' s = μ (m' ⁻¹' s)) :
    f.lintegral μ = g.lintegral μ' :=
  lintegral_eq_of_measure_preimage fun y => by
    simp only [preimage, eq]
    exact (h (g ⁻¹' {y}) (g.measurableSet_preimage _)).symm

/--
theorem `lintegral_map` / 定理 `lintegral_map`

English:
theorem lintegral_map
  given: {β} [MeasurableSpace β] (g : β ->ₛ Real>=0∞) {f : α -> β} (hf : Measurable f)
  proof: Eq.symm lintegral_map' _ _ f (fun _ => rfl) fun _s hs => Measure.map_apply hf hs

中文:
定理 lintegral_map
  条件: {β} [MeasurableSpace β] (g : β ->ₛ 实数>=0∞) {f : α -> β} (hf : Measurable f)
  证明: Eq.symm lintegral_map' _ _ f (fun _ => rfl) fun _s hs => Measure.map_apply hf hs

Depends on / 依赖: Eq.symm, Measure, Measure.map_apply, lintegral_map, map_apply
-/
theorem lintegral_map {β} [MeasurableSpace β] (g : β ->ₛ Real>=0∞) {f : α -> β} (hf : Measurable f) :
    g.lintegral (Measure.map f μ) = (g.comp f hf).lintegral μ :=
Eq.symm lintegral_map' _ _ f (fun _ => rfl) fun _s hs => Measure.map_apply hf hs

end Measure

section FinMeasSupp

open Finset Function

open scoped Classical in
/--
theorem `support_eq` / 定理 `support_eq`

English:
theorem support_eq
  given: [MeasurableSpace α] [Zero β] (f : α ->ₛ β)
  proof: Set.ext fun x => by
    simp only [mem_support, Set.mem_preimage, mem_filter, mem_range_self, true_and, exists_prop,
      mem_iUnion, mem_singleton_iff, exists_eq_right']

中文:
定理 support_eq
  条件: [MeasurableSpace α] [Zero β] (f : α ->ₛ β)
  证明: Set.ext fun x => by
    simp only [mem_support, Set.mem_preimage, mem_filter, mem_range_self, true_and, exists_prop,
      mem_iUnion, mem_singleton_iff, exists_eq_right']

Depends on / 依赖: Set.ext, Set.mem_preimage, exists_eq_right, exists_prop, mem_filter, mem_iUnion, mem_preimage, mem_range_self, mem_singleton_iff, mem_support, true_and
-/
theorem support_eq [MeasurableSpace α] [Zero β] (f : α ->ₛ β) :
    support f = ⋃ y in {y in f.range | y != 0}, f ⁻¹' {y} :=
  Set.ext fun x => by
    simp only [mem_support, Set.mem_preimage, mem_filter, mem_range_self, true_and, exists_prop,
      mem_iUnion, mem_singleton_iff, exists_eq_right']

variable {m : MeasurableSpace α} [Zero β] [Zero γ] {μ : Measure α} {f : α ->ₛ β}

/--
theorem `measurableSet_support` / 定理 `measurableSet_support`

English:
theorem measurableSet_support
  given: [MeasurableSpace α] (f : α ->ₛ β)
  statement: MeasurableSet (support f)
  proof: by
  rw [f.support_eq]
  exact Finset.measurableSet_biUnion _ fun y _ => measurableSet_fiber _ _

中文:
定理 measurableSet_support
  条件: [MeasurableSpace α] (f : α ->ₛ β)
  结论: MeasurableSet (support f)
  证明: by
  rw [f.support_eq]
  exact Finset.measurableSet_biUnion _ fun y _ => measurableSet_fiber _ _

Depends on / 依赖: Finset, Finset.measurableSet_biUnion, f.support_eq, measurableSet_biUnion, measurableSet_fiber, support_eq
-/
theorem measurableSet_support [MeasurableSpace α] (f : α ->ₛ β) : MeasurableSet (support f) := by
  rw [f.support_eq]
  exact Finset.measurableSet_biUnion _ fun y _ => measurableSet_fiber _ _

/--
lemma `measure_support_lt_top` / 引理 `measure_support_lt_top`

English:
lemma measure_support_lt_top
  given: (f : α ->ₛ β) (hf : forall y, y != 0 -> μ (f ⁻¹' {y}) < ∞)
  proof: by
  classical
  rw [support_eq]
  refine (measure_biUnion_finset_le _ _).trans_lt (ENNReal.sum_lt_top.mpr fun y hy => ?_)
  rw [Finset.mem_filter] at hy
  exact hf y hy.2

中文:
引理 measure_support_lt_top
  条件: (f : α ->ₛ β) (hf : 对任意 y, y != 0 -> μ (f ⁻¹' {y}) < ∞)
  证明: by
  classical
  rw [support_eq]
  refine (measure_biUnion_finset_le _ _).trans_lt (ENNReal.sum_lt_top.mpr fun y hy => ?_)
  rw [Finset.mem_filter] at hy
  exact hf y hy.2

Depends on / 依赖: ENNReal, ENNReal.sum_lt_top.mpr, Finset, Finset.mem_filter, classical, measure_biUnion_finset_le, mem_filter, sum_lt_top, support_eq, trans_lt
-/
lemma measure_support_lt_top (f : α ->ₛ β) (hf : forall y, y != 0 -> μ (f ⁻¹' {y}) < ∞) :
    μ (support f) < ∞ := by
  classical
  rw [support_eq]
  refine (measure_biUnion_finset_le _ _).trans_lt (ENNReal.sum_lt_top.mpr fun y hy => ?_)
  rw [Finset.mem_filter] at hy
  exact hf y hy.2

/--
Definition of `FinMeasSupp` / `FinMeasSupp` 的定义

English:
definition FinMeasSupp
  signature: {_m : MeasurableSpace α} (f : α ->ₛ β) (μ : Measure α)
  body: f =ᶠ[μ.cofinite] 0

中文:
定义 FinMeasSupp
  签名: {_m : MeasurableSpace α} (f : α ->ₛ β) (μ : Measure α)
  定义体: f =ᶠ[μ.cofinite] 0
-/
protected def FinMeasSupp {_m : MeasurableSpace α} (f : α ->ₛ β) (μ : Measure α) : Prop :=
  f =ᶠ[μ.cofinite] 0

/--
theorem `finMeasSupp_iff_support` / 定理 `finMeasSupp_iff_support`

English:
theorem finMeasSupp_iff_support
  statement: f.FinMeasSupp μ ↔ μ (support f) < ∞
  proof: Iff.rfl

中文:
定理 finMeasSupp_iff_support
  结论: f.FinMeasSupp μ ↔ μ (support f) < ∞
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem finMeasSupp_iff_support : f.FinMeasSupp μ ↔ μ (support f) < ∞ :=
  Iff.rfl

/--
theorem `finMeasSupp_iff` / 定理 `finMeasSupp_iff`

English:
theorem finMeasSupp_iff
  statement: f.FinMeasSupp μ ↔ forall y, y != 0 -> μ (f ⁻¹' {y}) < ∞
  proof: by
  classical
  constructor
  · refine fun h y hy => lt_of_le_of_lt (measure_mono ?_) h
exact fun x hx (H : f x = 0) => hy H ▸ Eq.symm hx
  · intro H
    rw [finMeasSupp_iff_support]; rw [support_eq]
    exact measure_biUnion_lt_top (finite_toSet _) fun y hy => H y (mem_filter.1 hy).2

中文:
定理 finMeasSupp_iff
  结论: f.FinMeasSupp μ ↔ 对任意 y, y != 0 -> μ (f ⁻¹' {y}) < ∞
  证明: by
  classical
  constructor
  · refine fun h y hy => lt_of_le_of_lt (measure_mono ?_) h
exact fun x hx (H : f x = 0) => hy H ▸ Eq.symm hx
  · intro H
    rw [finMeasSupp_iff_support]; rw [support_eq]
    exact measure_biUnion_lt_top (finite_toSet _) fun y hy => H y (mem_filter.1 hy).2

Depends on / 依赖: Eq.symm, classical, finMeasSupp_iff_support, finite_toSet, lt_of_le_of_lt, measure_biUnion_lt_top, measure_mono, mem_filter, support_eq
-/
theorem finMeasSupp_iff : f.FinMeasSupp μ ↔ forall y, y != 0 -> μ (f ⁻¹' {y}) < ∞ := by
  classical
  constructor
  · refine fun h y hy => lt_of_le_of_lt (measure_mono ?_) h
exact fun x hx (H : f x = 0) => hy H ▸ Eq.symm hx
  · intro H
    rw [finMeasSupp_iff_support]; rw [support_eq]
    exact measure_biUnion_lt_top (finite_toSet _) fun y hy => H y (mem_filter.1 hy).2

namespace FinMeasSupp

/--
theorem `meas_preimage_singleton_ne_zero` / 定理 `meas_preimage_singleton_ne_zero`

English:
theorem meas_preimage_singleton_ne_zero
  given: (h : f.FinMeasSupp μ) {y : β} (hy : y != 0)
  proof: finMeasSupp_iff.1 h y hy

中文:
定理 meas_preimage_singleton_ne_zero
  条件: (h : f.FinMeasSupp μ) {y : β} (hy : y != 0)
  证明: finMeasSupp_iff.1 h y hy

Depends on / 依赖: finMeasSupp_iff
-/
theorem meas_preimage_singleton_ne_zero (h : f.FinMeasSupp μ) {y : β} (hy : y != 0) :
    μ (f ⁻¹' {y}) < ∞ :=
  finMeasSupp_iff.1 h y hy

/--
theorem `map` / 定理 `map`

English:
theorem map
  given: {g : β -> γ} (hf : f.FinMeasSupp μ) (hg : g 0 = 0)
  statement: (f.map g).FinMeasSupp μ
  proof: flip lt_of_le_of_lt hf (measure_mono <| support_comp_subset hg f)

中文:
定理 map
  条件: {g : β -> γ} (hf : f.FinMeasSupp μ) (hg : g 0 = 0)
  结论: (f.map g).FinMeasSupp μ
  证明: flip lt_of_le_of_lt hf (measure_mono <| support_comp_subset hg f)
-/
protected theorem map {g : β -> γ} (hf : f.FinMeasSupp μ) (hg : g 0 = 0) : (f.map g).FinMeasSupp μ :=
  flip lt_of_le_of_lt hf (measure_mono <| support_comp_subset hg f)

/--
theorem `of_map` / 定理 `of_map`

English:
theorem of_map
  given: {g : β -> γ} (h : (f.map g).FinMeasSupp μ) (hg : forall b, g b = 0 -> b = 0)
  proof: flip lt_of_le_of_lt h measure_mono support_subset_comp @hg _

中文:
定理 of_map
  条件: {g : β -> γ} (h : (f.map g).FinMeasSupp μ) (hg : 对任意 b, g b = 0 -> b = 0)
  证明: flip lt_of_le_of_lt h measure_mono support_subset_comp @hg _

Depends on / 依赖: lt_of_le_of_lt, measure_mono, support_subset_comp
-/
theorem of_map {g : β -> γ} (h : (f.map g).FinMeasSupp μ) (hg : forall b, g b = 0 -> b = 0) :
    f.FinMeasSupp μ :=
flip lt_of_le_of_lt h measure_mono support_subset_comp @hg _

/--
theorem `map_iff` / 定理 `map_iff`

English:
theorem map_iff
  given: {g : β -> γ} (hg : forall {b}, g b = 0 ↔ b = 0)
  proof: ⟨fun h => h.of_map fun _ => hg.1, fun h => h.map hg.2 rfl⟩

中文:
定理 map_iff
  条件: {g : β -> γ} (hg : 对任意 {b}, g b = 0 ↔ b = 0)
  证明: ⟨fun h => h.of_map fun _ => hg.1, fun h => h.map hg.2 rfl⟩

Depends on / 依赖: h.map, h.of_map, of_map
-/
theorem map_iff {g : β -> γ} (hg : forall {b}, g b = 0 ↔ b = 0) :
    (f.map g).FinMeasSupp μ ↔ f.FinMeasSupp μ :=
⟨fun h => h.of_map fun _ => hg.1, fun h => h.map hg.2 rfl⟩

/--
theorem `pair` / 定理 `pair`

English:
theorem pair
  given: {g : α ->ₛ γ} (hf : f.FinMeasSupp μ) (hg : g.FinMeasSupp μ)
  proof: calc
μ (support <| pair f g) = μ (support f union support g) := congr_arg μ support_prodMk f g
    _ <= μ (support f) + μ (support g) := measure_union_le _ _
    _ < _ := add_lt_top.2 ⟨hf, hg⟩

中文:
定理 pair
  条件: {g : α ->ₛ γ} (hf : f.FinMeasSupp μ) (hg : g.FinMeasSupp μ)
  证明: calc
μ (support <| pair f g) = μ (support f union support g) := congr_arg μ support_prodMk f g
    _ <= μ (support f) + μ (support g) := measure_union_le _ _
    _ < _ := add_lt_top.2 ⟨hf, hg⟩
-/
protected theorem pair {g : α ->ₛ γ} (hf : f.FinMeasSupp μ) (hg : g.FinMeasSupp μ) :
    (pair f g).FinMeasSupp μ :=
  calc
μ (support <| pair f g) = μ (support f union support g) := congr_arg μ support_prodMk f g
    _ <= μ (support f) + μ (support g) := measure_union_le _ _
    _ < _ := add_lt_top.2 ⟨hf, hg⟩

/--
theorem `map₂` / 定理 `map₂`

English:
theorem map₂
  statement: [Zero δ] (hf : f.FinMeasSupp μ) {g : α ->ₛ γ} (hg : g.FinMeasSupp μ)
  proof: (hf.pair hg).map H

中文:
定理 map₂
  结论: [Zero δ] (hf : f.FinMeasSupp μ) {g : α ->ₛ γ} (hg : g.FinMeasSupp μ)
  证明: (hf.pair hg).map H
-/
protected theorem map₂ [Zero δ] (hf : f.FinMeasSupp μ) {g : α ->ₛ γ} (hg : g.FinMeasSupp μ)
    {op : β -> γ -> δ} (H : op 0 0 = 0) : ((pair f g).map (Function.uncurry op)).FinMeasSupp μ :=
  (hf.pair hg).map H

/--
theorem `add` / 定理 `add`

English:
theorem add
  statement: {β} [AddZeroClass β] {f g : α ->ₛ β} (hf : f.FinMeasSupp μ)
  proof: by
  rw [add_eq_map₂]
  exact hf.map₂ hg (zero_add 0)

中文:
定理 add
  结论: {β} [AddZeroClass β] {f g : α ->ₛ β} (hf : f.FinMeasSupp μ)
  证明: by
  rw [add_eq_map₂]
  exact hf.map₂ hg (zero_add 0)
-/
protected theorem add {β} [AddZeroClass β] {f g : α ->ₛ β} (hf : f.FinMeasSupp μ)
    (hg : g.FinMeasSupp μ) : (f + g).FinMeasSupp μ := by
  rw [add_eq_map₂]
  exact hf.map₂ hg (zero_add 0)

/--
theorem `mul` / 定理 `mul`

English:
theorem mul
  statement: {β} [MulZeroClass β] {f g : α ->ₛ β} (hf : f.FinMeasSupp μ)
  proof: by
  rw [mul_eq_map₂]
  exact hf.map₂ hg (zero_mul 0)

中文:
定理 mul
  结论: {β} [MulZeroClass β] {f g : α ->ₛ β} (hf : f.FinMeasSupp μ)
  证明: by
  rw [mul_eq_map₂]
  exact hf.map₂ hg (zero_mul 0)
-/
protected theorem mul {β} [MulZeroClass β] {f g : α ->ₛ β} (hf : f.FinMeasSupp μ)
    (hg : g.FinMeasSupp μ) : (f * g).FinMeasSupp μ := by
  rw [mul_eq_map₂]
  exact hf.map₂ hg (zero_mul 0)

/--
theorem `lintegral_lt_top` / 定理 `lintegral_lt_top`

English:
theorem lintegral_lt_top
  given: {f : α ->ₛ Real>=0∞} (hm : f.FinMeasSupp μ) (hf : forallᵐ a ∂μ, f a != ∞)
  proof: by
  refine sum_lt_top.2 fun a ha => ?_
  rcases eq_or_ne a ∞ with (rfl | ha)
  · simp only [ae_iff, Ne, Classical.not_not] at hf
    simp [Set.preimage, hf]
  · by_cases ha0 : a = 0
    · subst a
      simp
    · exact mul_lt_top ha.lt_top (finMeasSupp_iff.1 hm _ ha0)

中文:
定理 lintegral_lt_top
  条件: {f : α ->ₛ 实数>=0∞} (hm : f.FinMeasSupp μ) (hf : 对任意ᵐ a ∂μ, f a != ∞)
  证明: by
  refine sum_lt_top.2 fun a ha => ?_
  rcases eq_or_ne a ∞ with (rfl | ha)
  · simp only [ae_iff, Ne, Classical.not_not] at hf
    simp [Set.preimage, hf]
  · by_cases ha0 : a = 0
    · subst a
      simp
    · exact mul_lt_top ha.lt_top (finMeasSupp_iff.1 hm _ ha0)

Depends on / 依赖: Classical, Classical.not_not, Set.preimage, ae_iff, eq_or_ne, finMeasSupp_iff, ha.lt_top, lt_top, mul_lt_top, not_not, preimage, sum_lt_top
-/
theorem lintegral_lt_top {f : α ->ₛ Real>=0∞} (hm : f.FinMeasSupp μ) (hf : forallᵐ a ∂μ, f a != ∞) :
    f.lintegral μ < ∞ := by
  refine sum_lt_top.2 fun a ha => ?_
  rcases eq_or_ne a ∞ with (rfl | ha)
  · simp only [ae_iff, Ne, Classical.not_not] at hf
    simp [Set.preimage, hf]
  · by_cases ha0 : a = 0
    · subst a
      simp
    · exact mul_lt_top ha.lt_top (finMeasSupp_iff.1 hm _ ha0)

/--
theorem `of_lintegral_ne_top` / 定理 `of_lintegral_ne_top`

English:
theorem of_lintegral_ne_top
  given: {f : α ->ₛ Real>=0∞} (h : f.lintegral μ != ∞)
  statement: f.FinMeasSupp μ
  proof: by
  refine finMeasSupp_iff.2 fun b hb => ?_
  rw [f.lintegral_eq_of_subset' (Finset.subset_insert b _)] at h
  refine ENNReal.lt_top_of_mul_ne_top_right ?_ hb
  exact (lt_top_of_sum_ne_top h (Finset.mem_insert_self _ _)).ne

中文:
定理 of_lintegral_ne_top
  条件: {f : α ->ₛ 实数>=0∞} (h : f.lintegral μ != ∞)
  结论: f.FinMeasSupp μ
  证明: by
  refine finMeasSupp_iff.2 fun b hb => ?_
  rw [f.lintegral_eq_of_subset' (Finset.subset_insert b _)] at h
  refine ENNReal.lt_top_of_mul_ne_top_right ?_ hb
  exact (lt_top_of_sum_ne_top h (Finset.mem_insert_self _ _)).ne

Depends on / 依赖: ENNReal, ENNReal.lt_top_of_mul_ne_top_right, Finset, Finset.mem_insert_self, Finset.subset_insert, f.lintegral_eq_of_subset, finMeasSupp_iff, lintegral_eq_of_subset, lt_top_of_mul_ne_top_right, lt_top_of_sum_ne_top, mem_insert_self, subset_insert
-/
theorem of_lintegral_ne_top {f : α ->ₛ Real>=0∞} (h : f.lintegral μ != ∞) : f.FinMeasSupp μ := by
  refine finMeasSupp_iff.2 fun b hb => ?_
  rw [f.lintegral_eq_of_subset' (Finset.subset_insert b _)] at h
  refine ENNReal.lt_top_of_mul_ne_top_right ?_ hb
  exact (lt_top_of_sum_ne_top h (Finset.mem_insert_self _ _)).ne

/--
theorem `iff_lintegral_lt_top` / 定理 `iff_lintegral_lt_top`

English:
theorem iff_lintegral_lt_top
  given: {f : α ->ₛ Real>=0∞} (hf : forallᵐ a ∂μ, f a != ∞)
  proof: ⟨fun h => h.lintegral_lt_top hf, fun h => of_lintegral_ne_top h.ne⟩

中文:
定理 iff_lintegral_lt_top
  条件: {f : α ->ₛ 实数>=0∞} (hf : 对任意ᵐ a ∂μ, f a != ∞)
  证明: ⟨fun h => h.lintegral_lt_top hf, fun h => of_lintegral_ne_top h.ne⟩

Depends on / 依赖: h.lintegral_lt_top, h.ne, lintegral_lt_top, of_lintegral_ne_top
-/
theorem iff_lintegral_lt_top {f : α ->ₛ Real>=0∞} (hf : forallᵐ a ∂μ, f a != ∞) :
    f.FinMeasSupp μ ↔ f.lintegral μ < ∞ :=
  ⟨fun h => h.lintegral_lt_top hf, fun h => of_lintegral_ne_top h.ne⟩

end FinMeasSupp

/--
lemma `measure_support_lt_top_of_lintegral_ne_top` / 引理 `measure_support_lt_top_of_lintegral_ne_top`

English:
lemma measure_support_lt_top_of_lintegral_ne_top
  given: {f : α ->ₛ Real>=0∞} (hf : f.lintegral μ != ∞)
  proof: by
  refine measure_support_lt_top f ?_
  rw [← finMeasSupp_iff]
  exact FinMeasSupp.of_lintegral_ne_top hf

中文:
引理 measure_support_lt_top_of_lintegral_ne_top
  条件: {f : α ->ₛ 实数>=0∞} (hf : f.lintegral μ != ∞)
  证明: by
  refine measure_support_lt_top f ?_
  rw [← finMeasSupp_iff]
  exact FinMeasSupp.of_lintegral_ne_top hf

Depends on / 依赖: FinMeasSupp, FinMeasSupp.of_lintegral_ne_top, finMeasSupp_iff, measure_support_lt_top, of_lintegral_ne_top
-/
lemma measure_support_lt_top_of_lintegral_ne_top {f : α ->ₛ Real>=0∞} (hf : f.lintegral μ != ∞) :
    μ (support f) < ∞ := by
  refine measure_support_lt_top f ?_
  rw [← finMeasSupp_iff]
  exact FinMeasSupp.of_lintegral_ne_top hf

end FinMeasSupp

/-- To prove something for an arbitrary simple function, it suffices to show
that the property holds for (multiples of) characteristic functions and is closed under
addition (of functions with disjoint support).

It is possible to make the hypotheses in `h_add` a bit stronger, and such conditions can be added
once we need them (for example it is only necessary to consider the case where `g` is a multiple
of a characteristic function, and that this multiple doesn't appear in the image of `f`).

To use in an induction proof, the syntax is `induction f using SimpleFunc.induction with`. -/
@[elab_as_elim]
/--
theorem `induction` / 定理 `induction`

English:
theorem induction
  statement: {α γ} [MeasurableSpace α] [AddZeroClass γ]
  proof: by
  classical
  generalize h : f.range \ {0} = s
  rw [← Finset.coe_inj]; rw [Finset.coe_sdiff]; rw [Finset.coe_singleton]; rw [SimpleFunc.coe_range] at h
  induction s using Finset.induction generalizing f with
  | empty =>
    rw [Finset.coe_empty]; rw [sdiff_eq_empty]; rw [range_subset_singleton

中文:
定理 induction
  结论: {α γ} [MeasurableSpace α] [AddZeroClass γ]
  证明: by
  classical
  generalize h : f.range \ {0} = s
  rw [← Finset.coe_inj]; rw [Finset.coe_sdiff]; rw [Finset.coe_singleton]; rw [SimpleFunc.coe_range] at h
  induction s using Finset.induction generalizing f with
  | empty =>
    rw [Finset.coe_empty]; rw [sdiff_eq_empty]; rw [range_subset_singleton
-/
protected theorem induction {α γ} [MeasurableSpace α] [AddZeroClass γ]
    {motive : SimpleFunc α γ -> Prop}
    (const : forall (c) {s} (hs : MeasurableSet s),
      motive (SimpleFunc.piecewise s hs (SimpleFunc.const _ c) (SimpleFunc.const _ 0)))
    (add : forall ⦃f g : SimpleFunc α γ⦄,
      Disjoint (support f) (support g) -> motive f -> motive g -> motive (f + g))
    (f : SimpleFunc α γ) : motive f := by
  classical
  generalize h : f.range \ {0} = s
  rw [← Finset.coe_inj]; rw [Finset.coe_sdiff]; rw [Finset.coe_singleton]; rw [SimpleFunc.coe_range] at h
  induction s using Finset.induction generalizing f with
  | empty =>
    rw [Finset.coe_empty]; rw [sdiff_eq_empty]; rw [range_subset_singleton] at h
    convert! const 0 MeasurableSet.univ
    ext x
    simp [h]
  | insert x s hxs ih =>
    have mx := f.measurableSet_preimage {x}
    let g := SimpleFunc.piecewise (f ⁻¹' {x}) mx 0 f
    have Pg : motive g := by
      apply ih
      simp only [g, SimpleFunc.coe_piecewise, range_piecewise]
      rw [image_compl_preimage]; rw [union_sdiff_distrib]; rw [sdiff_sdiff_comm]; rw [h]; rw [Finset.coe_insert]; rw [insert_sdiff_self_of_notMem]; rw [sdiff_eq_empty.mpr]; rw [Set.empty_union]
      · rw [Set.image_subset_iff]
        convert! Set.subset_univ _
        exact preimage_const_of_mem (mem_singleton _)
      · rwa [Finset.mem_coe]
    convert! add _ Pg (const x mx)
    · ext1 y
      by_cases hy : y in f ⁻¹' {x}
      · simpa [g, hy]
      · simp [g, hy]
    rw [disjoint_iff_inf_le]
    rintro y
    by_cases hy : y in f ⁻¹' {x} <;> simp [g, hy]

/-- To prove something for an arbitrary simple function, it suffices to show
that the property holds for constant functions and that it is closed under piecewise combinations
of functions.

To use in an induction proof, the syntax is `induction f with`. -/
@[induction_eliminator]
/--
theorem `induction'` / 定理 `induction'`

English:
theorem induction'
  statement: {α γ} [MeasurableSpace α] [Nonempty γ] {P : SimpleFunc α γ -> Prop}
  proof: by
  let c : γ := Classical.ofNonempty
  classical
  generalize h : f.range \ {c} = s
  rw [← Finset.coe_inj]; rw [Finset.coe_sdiff]; rw [Finset.coe_singleton]; rw [SimpleFunc.coe_range] at h
  induction s using Finset.induction generalizing f with
  | empty =>
    rw [Finset.coe_empty]; rw [sdiff_e

中文:
定理 induction'
  结论: {α γ} [MeasurableSpace α] [Nonempty γ] {P : SimpleFunc α γ -> 命题}
  证明: by
  let c : γ := Classical.ofNonempty
  classical
  generalize h : f.range \ {c} = s
  rw [← Finset.coe_inj]; rw [Finset.coe_sdiff]; rw [Finset.coe_singleton]; rw [SimpleFunc.coe_range] at h
  induction s using Finset.induction generalizing f with
  | empty =>
    rw [Finset.coe_empty]; rw [sdiff_e
-/
protected theorem induction' {α γ} [MeasurableSpace α] [Nonempty γ] {P : SimpleFunc α γ -> Prop}
    (const : forall (c), P (SimpleFunc.const _ c))
    (pcw : forall ⦃f g : SimpleFunc α γ⦄ {s} (hs : MeasurableSet s), P f -> P g ->
      P (f.piecewise s hs g))
    (f : SimpleFunc α γ) : P f := by
  let c : γ := Classical.ofNonempty
  classical
  generalize h : f.range \ {c} = s
  rw [← Finset.coe_inj]; rw [Finset.coe_sdiff]; rw [Finset.coe_singleton]; rw [SimpleFunc.coe_range] at h
  induction s using Finset.induction generalizing f with
  | empty =>
    rw [Finset.coe_empty]; rw [sdiff_eq_empty]; rw [range_subset_singleton] at h
    convert! const c
    ext x
    simp [h]
  | insert x s hxs ih =>
    have mx := f.measurableSet_preimage {x}
    let g := SimpleFunc.piecewise (f ⁻¹' {x}) mx (SimpleFunc.const α c) f
    have Pg : P g := by
      apply ih
      simp only [g, SimpleFunc.coe_piecewise, range_piecewise]
      rw [image_compl_preimage]; rw [union_sdiff_distrib]; rw [sdiff_sdiff_comm]; rw [h]; rw [Finset.coe_insert]; rw [insert_sdiff_self_of_notMem]; rw [sdiff_eq_empty.mpr]; rw [Set.empty_union]
      · rw [Set.image_subset_iff]
        convert! Set.subset_univ _
        exact preimage_const_of_mem (mem_singleton _)
      · rwa [Finset.mem_coe]
    convert! pcw mx.compl Pg (const x)
    · ext1 y
      by_cases hy : y in f ⁻¹' {x}
      · simpa [g, hy]
      · simp [g, hy]

/--
theorem `_root_.Measurable.add_simpleFunc` / 定理 `_root_.Measurable.add_simpleFunc`

English:
theorem _root_.Measurable.add_simpleFunc
  proof: f.measurable_bind (fun b a => g a + b) fun b => hg.add_const b

中文:
定理 _root_.Measurable.add_simpleFunc
  证明: f.measurable_bind (fun b a => g a + b) fun b => hg.add_const b

Depends on / 依赖: add_const, f.measurable_bind, hg.add_const, measurable_bind
-/
theorem _root_.Measurable.add_simpleFunc
    {E : Type*} {_ : MeasurableSpace α} [MeasurableSpace E] [AddCancelMonoid E] [MeasurableAdd E]
    {g : α -> E} (hg : Measurable g) (f : SimpleFunc α E) : Measurable (g + (f : α -> E)) :=
  f.measurable_bind (fun b a => g a + b) fun b => hg.add_const b

/--
theorem `_root_.Measurable.simpleFunc_add` / 定理 `_root_.Measurable.simpleFunc_add`

English:
theorem _root_.Measurable.simpleFunc_add
  proof: f.measurable_bind (fun b a => b + g a) fun b => hg.const_add b

中文:
定理 _root_.Measurable.simpleFunc_add
  证明: f.measurable_bind (fun b a => b + g a) fun b => hg.const_add b

Depends on / 依赖: const_add, f.measurable_bind, hg.const_add, measurable_bind
-/
theorem _root_.Measurable.simpleFunc_add
    {E : Type*} {_ : MeasurableSpace α} [MeasurableSpace E] [AddCancelMonoid E] [MeasurableAdd E]
    {g : α -> E} (hg : Measurable g) (f : SimpleFunc α E) : Measurable ((f : α -> E) + g) :=
  f.measurable_bind (fun b a => b + g a) fun b => hg.const_add b

end SimpleFunc

end MeasureTheory

open MeasureTheory MeasureTheory.SimpleFunc

variable {α : Type*} {mα : MeasurableSpace α} {μ : Measure α}

/-- To prove something for an arbitrary measurable function into `ℝ≥0∞`, it suffices to show
that the property holds for (multiples of) characteristic functions and is closed under addition
and supremum of increasing sequences of functions.

It is possible to make the hypotheses in the induction steps a bit stronger, and such conditions
can be added once we need them (for example in `h_add` it is only necessary to consider the sum of
a simple function with a multiple of a characteristic function and that the intersection
of their images is a subset of `{0}`). -/
@[elab_as_elim]
/--
theorem `Measurable.ennreal_induction` / 定理 `Measurable.ennreal_induction`

English:
theorem Measurable.ennreal_induction
  statement: {motive : (α -> Real>=0∞) -> Prop}
  proof: by
  convert! iSup (fun n => (eapprox f n).measurable) (monotone_eapprox f) _ using 2
  · rw [iSup_eapprox_apply hf]
  · exact fun n =>
      SimpleFunc.induction (fun c s hs => indicator c hs)
        (fun f g hfg hf hg => add hfg f.measurable g.measurable hf hg) (eapprox f n)

中文:
定理 Measurable.ennreal_induction
  结论: {motive : (α -> 实数>=0∞) -> 命题}
  证明: by
  convert! iSup (fun n => (eapprox f n).measurable) (monotone_eapprox f) _ using 2
  · rw [iSup_eapprox_apply hf]
  · exact fun n =>
      SimpleFunc.induction (fun c s hs => indicator c hs)
        (fun f g hfg hf hg => add hfg f.measurable g.measurable hf hg) (eapprox f n)

Depends on / 依赖: SimpleFunc, SimpleFunc.induction, convert, eapprox, f.measurable, g.measurable, iSup_eapprox_apply, indicator, measurable, monotone_eapprox
-/
theorem Measurable.ennreal_induction {motive : (α -> Real>=0∞) -> Prop}
    (indicator : forall (c : Real>=0∞) ⦃s⦄, MeasurableSet s -> motive (Set.indicator s fun _ => c))
    (add : forall ⦃f g : α -> Real>=0∞⦄, Disjoint (support f) (support g) ->
      Measurable f -> Measurable g -> motive f -> motive g -> motive (f + g))
    (iSup : forall ⦃f : Nat -> α -> Real>=0∞⦄, (forall n, Measurable (f n)) -> Monotone f ->
      (forall n, motive (f n)) -> motive fun x => ⨆ n, f n x)
    ⦃f : α -> Real>=0∞⦄ (hf : Measurable f) : motive f := by
  convert! iSup (fun n => (eapprox f n).measurable) (monotone_eapprox f) _ using 2
  · rw [iSup_eapprox_apply hf]
  · exact fun n =>
      SimpleFunc.induction (fun c s hs => indicator c hs)
        (fun f g hfg hf hg => add hfg f.measurable g.measurable hf hg) (eapprox f n)

/-- To prove something for an arbitrary measurable function into `ℝ≥0∞`, it suffices to show
that the property holds for (multiples of) characteristic functions with finite mass according to
some sigma-finite measure and is closed under addition and supremum of increasing sequences of
functions.

It is possible to make the hypotheses in the induction steps a bit stronger, and such conditions
can be added once we need them (for example in `h_add` it is only necessary to consider the sum of
a simple function with a multiple of a characteristic function and that the intersection
of their images is a subset of `{0}`). -/
@[elab_as_elim]
/--
lemma `Measurable.ennreal_sigmaFinite_induction` / 引理 `Measurable.ennreal_sigmaFinite_induction`

English:
lemma Measurable.ennreal_sigmaFinite_induction
  statement: [SigmaFinite μ] {motive : (α -> Real>=0∞) -> Prop}
  proof: by
  refine Measurable.ennreal_induction (fun c s hs => ?_) add iSup hf
  convert!
    iSup (f := fun n => (s inter spanningSets μ n).indicator fun _ => c)
      (fun n => measurable_const.indicator (hs.inter (measurableSet_spanningSets ..)))
      (fun m n hmn a => by dsimp; grw [hmn])
      (fun n

中文:
引理 Measurable.ennreal_sigmaFinite_induction
  结论: [SigmaFinite μ] {motive : (α -> 实数>=0∞) -> 命题}
  证明: by
  refine Measurable.ennreal_induction (fun c s hs => ?_) add iSup hf
  convert!
    iSup (f := fun n => (s inter spanningSets μ n).indicator fun _ => c)
      (fun n => measurable_const.indicator (hs.inter (measurableSet_spanningSets ..)))
      (fun m n hmn a => by dsimp; grw [hmn])
      (fun n

Depends on / 依赖: Measurable, Measurable.ennreal_induction, Set.indicator_iUnion_apply, Set.inter_iUnion, convert, ennreal_induction, hs.inter, indicator, indicator_iUnion_apply, inter_iUnion, measurableSet_spanningSets, measurable_const, measurable_const.indicator, measure_inter_lt_top_of_right_ne_top, measure_spanningSets_lt_top, spanningSets
-/
lemma Measurable.ennreal_sigmaFinite_induction [SigmaFinite μ] {motive : (α -> Real>=0∞) -> Prop}
    (indicator : forall (c : Real>=0∞) ⦃s⦄, MeasurableSet s -> μ s < ∞ -> motive (Set.indicator s fun _ => c))
    (add : forall ⦃f g : α -> Real>=0∞⦄, Disjoint (support f) (support g) ->
      Measurable f -> Measurable g -> motive f -> motive g -> motive (f + g))
    (iSup : forall ⦃f : Nat -> α -> Real>=0∞⦄, (forall n, Measurable (f n)) -> Monotone f ->
      (forall n, motive (f n)) -> motive fun x => ⨆ n, f n x)
    ⦃f : α -> Real>=0∞⦄ (hf : Measurable f) : motive f := by
  refine Measurable.ennreal_induction (fun c s hs => ?_) add iSup hf
  convert!
    iSup (f := fun n => (s inter spanningSets μ n).indicator fun _ => c)
      (fun n => measurable_const.indicator (hs.inter (measurableSet_spanningSets ..)))
      (fun m n hmn a => by dsimp; grw [hmn])
      (fun n =>
        indicator _ (hs.inter (measurableSet_spanningSets ..))
          (measure_inter_lt_top_of_right_ne_top (measure_spanningSets_lt_top ..).ne)) with
    a
  simp [← Set.indicator_iUnion_apply (M := Real>=0∞) rfl, ← Set.inter_iUnion]
