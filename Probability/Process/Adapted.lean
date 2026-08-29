/-
Copyright (c) 2021 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying, Rémy Degenne
-/
module

public import Mathlib.Probability.Process.Filtration
public import Mathlib.Topology.Instances.Discrete

/-!
# Adapted and progressively measurable processes

This file defines the related notions of a process `u` being (strongly) `Adapted` or
`Progressive` (progressively measurable) with respect to a filtration `f`, and proves some
basic facts about them.

## Main definitions

* `MeasureTheory.Adapted`: a sequence of functions `u` is said to be adapted to a
  filtration `f` if at each point in time `i`, `u i` is `f i`-measurable
* `MeasureTheory.IsProgressive`: a sequence of functions `u` is said to be progressive with respect
  to a filtration `f` if at each point in time `i`, `u` restricted to `Set.Iic i × Ω` is strongly
  measurable with respect to the product `MeasurableSpace` structure where the σ-algebra used for
  `Ω` is `f i`.
We also provide the following variants, which use `MeasureTheory.StronglyMeasurable` instead
of `Measurable`:
* `MeasureTheory.StronglyAdapted`
* `MeasureTheory.IsStronglyProgressive`

## Main results

* `StronglyAdapted.isStronglyProgressive_of_continuous`: a continuous strongly adapted process is
  strongly progressive.

## Tags

adapted, progressively measurable

-/

@[expose] public section

open Filter Order TopologicalSpace

open scoped MeasureTheory NNReal ENNReal Topology

namespace MeasureTheory

variable {Ω ι : Type*} {m : MeasurableSpace Ω} [Preorder ι] {f : Filtration ι m}

section Adapted

variable {β : ι -> Type*} [forall i, MeasurableSpace (β i)] {u v : (i : ι) -> Ω -> β i}

/--
Definition of `Adapted` / `Adapted` 的定义

English:
definition Adapted
  signature: (f : Filtration ι m) (u : (i : ι) -> Ω -> β i)
  body: forall i : ι, Measurable[f i] (u i)

中文:
定义 Adapted
  签名: (f : 滤子 ι m) (u : (i : ι) -> Ω -> β i)
  定义体: forall i : ι, Measurable[f i] (u i)

Depends on / 依赖: Measurable
-/
def Adapted (f : Filtration ι m) (u : (i : ι) -> Ω -> β i) : Prop :=
  forall i : ι, Measurable[f i] (u i)

namespace Adapted

@[to_additive]
/--
theorem `mul` / 定理 `mul`

English:
theorem mul
  statement: [forall i, Mul (β i)] [forall i, MeasurableMul₂ (β i)]
  proof: fun i => (hu i).mul (hv i)

@[to_additive]

中文:
定理 mul
  结论: [对任意 i, 乘法 (β i)] [对任意 i, MeasurableMul₂ (β i)]
  证明: fun i => (hu i).mul (hv i)

@[to_additive]
-/
protected theorem mul [forall i, Mul (β i)] [forall i, MeasurableMul₂ (β i)]
    (hu : Adapted f u) (hv : Adapted f v) :
    Adapted f (u * v) := fun i => (hu i).mul (hv i)

@[to_additive]
/--
theorem `div` / 定理 `div`

English:
theorem div
  statement: [forall i, Div (β i)] [forall i, MeasurableDiv₂ (β i)]
  proof: fun i => (hu i).div (hv i)

@[to_additive]

中文:
定理 div
  结论: [对任意 i, 除法 (β i)] [对任意 i, MeasurableDiv₂ (β i)]
  证明: fun i => (hu i).div (hv i)

@[to_additive]
-/
protected theorem div [forall i, Div (β i)] [forall i, MeasurableDiv₂ (β i)]
    (hu : Adapted f u) (hv : Adapted f v) :
    Adapted f (u / v) := fun i => (hu i).div (hv i)

@[to_additive]
/--
theorem `inv` / 定理 `inv`

English:
theorem inv
  given: [forall i, Group (β i)] [forall i, MeasurableInv (β i)] (hu : Adapted f u)
  proof: fun i => (hu i).inv

中文:
定理 inv
  条件: [对任意 i, 群 (β i)] [对任意 i, MeasurableInv (β i)] (hu : Adapted f u)
  证明: fun i => (hu i).inv
-/
protected theorem inv [forall i, Group (β i)] [forall i, MeasurableInv (β i)] (hu : Adapted f u) :
    Adapted f u⁻¹ := fun i => (hu i).inv

/--
theorem `smul` / 定理 `smul`

English:
theorem smul
  statement: {𝕂 : Type*} [MeasurableSpace 𝕂]
  proof: fun i => (hu i).const_smul c

中文:
定理 smul
  结论: {𝕂 : 类型} [可测空间 𝕂]
  证明: fun i => (hu i).const_smul c
-/
protected theorem smul {𝕂 : Type*} [MeasurableSpace 𝕂]
    [forall i, SMul 𝕂 (β i)] [forall i, MeasurableSMul 𝕂 (β i)] (c : 𝕂) (hu : Adapted f u) :
    Adapted f (c • u) := fun i => (hu i).const_smul c

/--
theorem `measurable` / 定理 `measurable`

English:
theorem measurable
  given: {i : ι} (hf : Adapted f u)
  statement: Measurable[m] (u i)
  proof: (hf i).mono (f.le i) (by rfl)

中文:
定理 measurable
  条件: {i : ι} (hf : Adapted f u)
  结论: 可测[m] (u i)
  证明: (hf i).mono (f.le i) (by rfl)
-/
protected theorem measurable {i : ι} (hf : Adapted f u) : Measurable[m] (u i) :=
  (hf i).mono (f.le i) (by rfl)

/--
theorem `measurable_le` / 定理 `measurable_le`

English:
theorem measurable_le
  given: {i j : ι} (hf : Adapted f u) (hij : i <= j)
  statement: Measurable[f j] (u i)
  proof: (hf i).mono (f.mono hij) (by rfl)

中文:
定理 measurable_le
  条件: {i j : ι} (hf : Adapted f u) (hij : i <= j)
  结论: 可测[f j] (u i)
  证明: (hf i).mono (f.mono hij) (by rfl)

Depends on / 依赖: f.mono
-/
theorem measurable_le {i j : ι} (hf : Adapted f u) (hij : i <= j) : Measurable[f j] (u i) :=
  (hf i).mono (f.mono hij) (by rfl)

end Adapted

/--
theorem `adapted_const'` / 定理 `adapted_const'`

English:
theorem adapted_const'
  given: (f : Filtration ι m) (x : (i : ι) -> β i)
  statement: Adapted f fun i _ => x i
  proof: fun _ => measurable_const

中文:
定理 adapted_const'
  条件: (f : 滤子 ι m) (x : (i : ι) -> β i)
  结论: Adapted f fun i _ => x i
  证明: fun _ => measurable_const

Depends on / 依赖: measurable_const
-/
theorem adapted_const' (f : Filtration ι m) (x : (i : ι) -> β i) : Adapted f fun i _ => x i :=
  fun _ => measurable_const

/--
theorem `adapted_const` / 定理 `adapted_const`

English:
theorem adapted_const
  given: {β : Type*} [MeasurableSpace β] (f : Filtration ι m) (x : β)
  proof: adapted_const' _ _

中文:
定理 adapted_const
  条件: {β : 类型} [可测空间 β] (f : 滤子 ι m) (x : β)
  证明: adapted_const' _ _

Depends on / 依赖: adapted_const
-/
theorem adapted_const {β : Type*} [MeasurableSpace β] (f : Filtration ι m) (x : β) :
    Adapted f fun _ _ => x := adapted_const' _ _

end Adapted

section StronglyAdapted

variable {β : ι -> Type*} [forall i, TopologicalSpace (β i)] {u v : (i : ι) -> Ω -> β i}

/--
Definition of `StronglyAdapted` / `StronglyAdapted` 的定义

English:
definition StronglyAdapted
  signature: (f : Filtration ι m) (u : (i : ι) -> Ω -> β i)
  body: forall i : ι, StronglyMeasurable[f i] (u i)

中文:
定义 StronglyAdapted
  签名: (f : 滤子 ι m) (u : (i : ι) -> Ω -> β i)
  定义体: forall i : ι, StronglyMeasurable[f i] (u i)

Depends on / 依赖: StronglyMeasurable
-/
def StronglyAdapted (f : Filtration ι m) (u : (i : ι) -> Ω -> β i) : Prop :=
  forall i : ι, StronglyMeasurable[f i] (u i)

namespace StronglyAdapted

@[to_additive]
/--
theorem `mul` / 定理 `mul`

English:
theorem mul
  statement: [forall i, Mul (β i)] [forall i, ContinuousMul (β i)]
  proof: fun i => (hu i).mul (hv i)

@[to_additive sub]

中文:
定理 mul
  结论: [对任意 i, 乘法 (β i)] [对任意 i, 连续乘法 (β i)]
  证明: fun i => (hu i).mul (hv i)

@[to_additive sub]
-/
protected theorem mul [forall i, Mul (β i)] [forall i, ContinuousMul (β i)]
    (hu : StronglyAdapted f u) (hv : StronglyAdapted f v) :
    StronglyAdapted f (u * v) := fun i => (hu i).mul (hv i)

@[to_additive sub]
/--
theorem `div'` / 定理 `div'`

English:
theorem div'
  statement: [forall i, Div (β i)] [forall i, ContinuousDiv (β i)]
  proof: fun i => (hu i).div' (hv i)

@[to_additive]

中文:
定理 div'
  结论: [对任意 i, 除法 (β i)] [对任意 i, 余ntinuousDiv (β i)]
  证明: fun i => (hu i).div' (hv i)

@[to_additive]
-/
protected theorem div' [forall i, Div (β i)] [forall i, ContinuousDiv (β i)]
    (hu : StronglyAdapted f u) (hv : StronglyAdapted f v) :
    StronglyAdapted f (u / v) := fun i => (hu i).div' (hv i)

@[to_additive]
/--
theorem `inv` / 定理 `inv`

English:
theorem inv
  given: [forall i, Group (β i)] [forall i, ContinuousInv (β i)] (hu : StronglyAdapted f u)
  proof: fun i => (hu i).inv

中文:
定理 inv
  条件: [对任意 i, 群 (β i)] [对任意 i, 连续取逆 (β i)] (hu : StronglyAdapted f u)
  证明: fun i => (hu i).inv
-/
protected theorem inv [forall i, Group (β i)] [forall i, ContinuousInv (β i)] (hu : StronglyAdapted f u) :
    StronglyAdapted f u⁻¹ := fun i => (hu i).inv

/--
theorem `smul` / 定理 `smul`

English:
theorem smul
  statement: [forall i, SMul Real (β i)] [forall i, ContinuousConstSMul Real (β i)]
  proof: fun i => (hu i).const_smul c

中文:
定理 smul
  结论: [对任意 i, 标量乘法 实数 (β i)] [对任意 i, 连续常数标量乘法 实数 (β i)]
  证明: fun i => (hu i).const_smul c
-/
protected theorem smul [forall i, SMul Real (β i)] [forall i, ContinuousConstSMul Real (β i)]
    (c : Real) (hu : StronglyAdapted f u) :
    StronglyAdapted f (c • u) := fun i => (hu i).const_smul c

/--
lemma `norm` / 引理 `norm`

English:
lemma norm
  statement: {β : ι -> Type*} {u : (i : ι) -> Ω -> β i} [forall i, SeminormedAddCommGroup (β i)]
  proof: fun t => (hu t).norm

中文:
引理 norm
  结论: {β : ι -> 类型} {u : (i : ι) -> Ω -> β i} [对任意 i, SeminormedAddComm群 (β i)]
  证明: fun t => (hu t).norm
-/
protected lemma norm {β : ι -> Type*} {u : (i : ι) -> Ω -> β i} [forall i, SeminormedAddCommGroup (β i)]
    (hu : StronglyAdapted f u) :
    StronglyAdapted f (fun t ω => ‖u t ω‖) := fun t => (hu t).norm

/--
theorem `stronglyMeasurable` / 定理 `stronglyMeasurable`

English:
theorem stronglyMeasurable
  given: {i : ι} (hf : StronglyAdapted f u)
  proof: (hf i).mono (f.le i)

中文:
定理 stronglyMeasurable
  条件: {i : ι} (hf : StronglyAdapted f u)
  证明: (hf i).mono (f.le i)
-/
protected theorem stronglyMeasurable {i : ι} (hf : StronglyAdapted f u) :
    StronglyMeasurable[m] (u i) := (hf i).mono (f.le i)

/--
theorem `stronglyMeasurable_le` / 定理 `stronglyMeasurable_le`

English:
theorem stronglyMeasurable_le
  given: {i j : ι} (hf : StronglyAdapted f u) (hij : i <= j)
  proof: (hf i).mono (f.mono hij)

中文:
定理 stronglyMeasurable_le
  条件: {i j : ι} (hf : StronglyAdapted f u) (hij : i <= j)
  证明: (hf i).mono (f.mono hij)

Depends on / 依赖: f.mono
-/
theorem stronglyMeasurable_le {i j : ι} (hf : StronglyAdapted f u) (hij : i <= j) :
    StronglyMeasurable[f j] (u i) := (hf i).mono (f.mono hij)

end StronglyAdapted

/--
theorem `StronglyAdapted.adapted` / 定理 `StronglyAdapted.adapted`

English:
theorem StronglyAdapted.adapted
  statement: [mΒ : forall i, MeasurableSpace (β i)] [forall i, BorelSpace (β i)]
  proof: fun _ => (hf _).measurable

中文:
定理 StronglyAdapted.adapted
  结论: [mΒ : 对任意 i, 可测空间 (β i)] [对任意 i, Borel空间 (β i)]
  证明: fun _ => (hf _).measurable

Depends on / 依赖: measurable
-/
theorem StronglyAdapted.adapted [mΒ : forall i, MeasurableSpace (β i)] [forall i, BorelSpace (β i)]
    [forall i, PseudoMetrizableSpace (β i)] (hf : StronglyAdapted f u) :
    Adapted f u := fun _ => (hf _).measurable

/--
theorem `Adapted.stronglyAdapted` / 定理 `Adapted.stronglyAdapted`

English:
theorem Adapted.stronglyAdapted
  statement: [mΒ : forall i, MeasurableSpace (β i)]
  proof: fun _ => (hf _).stronglyMeasurable

中文:
定理 Adapted.stronglyAdapted
  结论: [mΒ : 对任意 i, 可测空间 (β i)]
  证明: fun _ => (hf _).stronglyMeasurable

Depends on / 依赖: stronglyMeasurable
-/
theorem Adapted.stronglyAdapted [mΒ : forall i, MeasurableSpace (β i)]
    [forall i, OpensMeasurableSpace (β i)] [forall i, PseudoMetrizableSpace (β i)]
    [forall i, SecondCountableTopology (β i)] (hf : Adapted f u) :
    StronglyAdapted f u := fun _ => (hf _).stronglyMeasurable

/--
theorem `stronglyAdapted_iff_adapted` / 定理 `stronglyAdapted_iff_adapted`

English:
theorem stronglyAdapted_iff_adapted
  statement: [mΒ : forall i, MeasurableSpace (β i)]
  proof: ⟨fun h => h.adapted, fun h => h.stronglyAdapted⟩

中文:
定理 stronglyAdapted_iff_adapted
  结论: [mΒ : 对任意 i, 可测空间 (β i)]
  证明: ⟨fun h => h.adapted, fun h => h.stronglyAdapted⟩

Depends on / 依赖: adapted, h.adapted, h.stronglyAdapted, stronglyAdapted
-/
theorem stronglyAdapted_iff_adapted [mΒ : forall i, MeasurableSpace (β i)]
    [forall i, BorelSpace (β i)] [forall i, PseudoMetrizableSpace (β i)]
    [forall i, SecondCountableTopology (β i)] :
    StronglyAdapted f u ↔ Adapted f u := ⟨fun h => h.adapted, fun h => h.stronglyAdapted⟩

/--
theorem `stronglyAdapted_const'` / 定理 `stronglyAdapted_const'`

English:
theorem stronglyAdapted_const'
  given: (f : Filtration ι m) (x : (i : ι) -> β i)
  proof: fun _ => stronglyMeasurable_const

中文:
定理 stronglyAdapted_const'
  条件: (f : 滤子 ι m) (x : (i : ι) -> β i)
  证明: fun _ => stronglyMeasurable_const

Depends on / 依赖: stronglyMeasurable_const
-/
theorem stronglyAdapted_const' (f : Filtration ι m) (x : (i : ι) -> β i) :
    StronglyAdapted f fun i _ => x i :=
  fun _ => stronglyMeasurable_const

/--
theorem `stronglyAdapted_const` / 定理 `stronglyAdapted_const`

English:
theorem stronglyAdapted_const
  given: {β : Type*} [TopologicalSpace β] (f : Filtration ι m) (x : β)
  proof: stronglyAdapted_const' _ _

中文:
定理 stronglyAdapted_const
  条件: {β : 类型} [拓扑空间 β] (f : 滤子 ι m) (x : β)
  证明: stronglyAdapted_const' _ _

Depends on / 依赖: stronglyAdapted_const
-/
theorem stronglyAdapted_const {β : Type*} [TopologicalSpace β] (f : Filtration ι m) (x : β) :
    StronglyAdapted f fun _ _ => x :=
  stronglyAdapted_const' _ _

variable (β) in
/--
theorem `stronglyAdapted_zero'` / 定理 `stronglyAdapted_zero'`

English:
theorem stronglyAdapted_zero'
  given: [forall i, Zero (β i)] (f : Filtration ι m)
  proof: fun i => @stronglyMeasurable_zero Ω (β i) (f i) _ _

中文:
定理 stronglyAdapted_zero'
  条件: [对任意 i, 零 (β i)] (f : 滤子 ι m)
  证明: fun i => @stronglyMeasurable_zero Ω (β i) (f i) _ _

Depends on / 依赖: stronglyMeasurable_zero
-/
theorem stronglyAdapted_zero' [forall i, Zero (β i)] (f : Filtration ι m) :
    StronglyAdapted f (0 : (i : ι) -> Ω -> β i) :=
  fun i => @stronglyMeasurable_zero Ω (β i) (f i) _ _

/--
theorem `stronglyAdapted_zero` / 定理 `stronglyAdapted_zero`

English:
theorem stronglyAdapted_zero
  given: (β : Type*) [TopologicalSpace β] [Zero β] (f : Filtration ι m)
  proof: fun i => @stronglyMeasurable_zero Ω β (f i) _ _

中文:
定理 stronglyAdapted_zero
  条件: (β : 类型) [拓扑空间 β] [零 β] (f : 滤子 ι m)
  证明: fun i => @stronglyMeasurable_zero Ω β (f i) _ _

Depends on / 依赖: stronglyMeasurable_zero
-/
theorem stronglyAdapted_zero (β : Type*) [TopologicalSpace β] [Zero β] (f : Filtration ι m) :
    StronglyAdapted f (0 : ι -> Ω -> β) :=
  fun i => @stronglyMeasurable_zero Ω β (f i) _ _

/--
theorem `Filtration.stronglyAdapted_natural` / 定理 `Filtration.stronglyAdapted_natural`

English:
theorem Filtration.stronglyAdapted_natural
  statement: [forall i, MetrizableSpace (β i)]
  proof: by
  intro i
  refine StronglyMeasurable.mono ?_ (le_iSup₂_of_le i (le_refl i) le_rfl)
  rw [stronglyMeasurable_iff_measurable_separable]
  exact ⟨measurable_iff_comap_le.2 le_rfl, (hum i).isSeparable_range⟩

中文:
定理 滤子.stronglyAdapted_natural
  结论: [对任意 i, Metrizable空间 (β i)]
  证明: by
  intro i
  refine StronglyMeasurable.mono ?_ (le_iSup₂_of_le i (le_refl i) le_rfl)
  rw [stronglyMeasurable_iff_measurable_separable]
  exact ⟨measurable_iff_comap_le.2 le_rfl, (hum i).isSeparable_range⟩

Depends on / 依赖: StronglyMeasurable, StronglyMeasurable.mono, isSeparable_range, le_refl, le_rfl, measurable_iff_comap_le, stronglyMeasurable_iff_measurable_separable
-/
theorem Filtration.stronglyAdapted_natural [forall i, MetrizableSpace (β i)]
    [mβ : forall i, MeasurableSpace (β i)] [forall i, BorelSpace (β i)]
    (hum : forall i, StronglyMeasurable[m] (u i)) :
    StronglyAdapted (Filtration.natural u hum) u := by
  intro i
  refine StronglyMeasurable.mono ?_ (le_iSup₂_of_le i (le_refl i) le_rfl)
  rw [stronglyMeasurable_iff_measurable_separable]
  exact ⟨measurable_iff_comap_le.2 le_rfl, (hum i).isSeparable_range⟩

end StronglyAdapted

section Progressive

variable {β : Type*} {u v : ι -> Ω -> β}

/--
Definition of `IsProgressive` / `IsProgressive` 的定义

English:
definition IsProgressive
  signature: [MeasurableSpace ι] [MeasurableSpace β] (f : Filtration ι m)
  body: forall i, Measurable[Subtype.instMeasurableSpace.prod (f i)] fun p : Set.Iic i × Ω => u p.1 p.2

中文:
定义 IsProgressive
  签名: [可测空间 ι] [可测空间 β] (f : 滤子 ι m)
  定义体: forall i, Measurable[Subtype.instMeasurableSpace.prod (f i)] fun p : Set.Iic i × Ω => u p.1 p.2

Depends on / 依赖: Measurable, Set.Iic, Subtype, Subtype.instMeasurableSpace.prod, instMeasurableSpace
-/
def IsProgressive [MeasurableSpace ι] [MeasurableSpace β] (f : Filtration ι m)
    (u : ι -> Ω -> β) : Prop :=
  forall i, Measurable[Subtype.instMeasurableSpace.prod (f i)] fun p : Set.Iic i × Ω => u p.1 p.2

/--
theorem `isProgressive_const` / 定理 `isProgressive_const`

English:
theorem isProgressive_const
  statement: {mi : MeasurableSpace ι} {mβ : MeasurableSpace β} (f : Filtration ι m)
  proof: fun _ => by exact measurable_const

中文:
定理 isProgressive_const
  结论: {mi : 可测空间 ι} {mβ : 可测空间 β} (f : 滤子 ι m)
  证明: fun _ => by exact measurable_const

Depends on / 依赖: measurable_const
-/
theorem isProgressive_const {mi : MeasurableSpace ι} {mβ : MeasurableSpace β} (f : Filtration ι m)
    (b : β) : IsProgressive f (fun _ _ => b : ι -> Ω -> β) :=
  fun _ => by exact measurable_const

namespace IsProgressive

variable {mi : MeasurableSpace ι} {mβ : MeasurableSpace β}

/--
theorem `adapted` / 定理 `adapted`

English:
theorem adapted
  given: (h : IsProgressive f u)
  statement: Adapted f u
  proof: by
  intro i
  have : u i = (fun p : Set.Iic i × Ω => u p.1 p.2) ∘ fun x => (⟨i, Set.mem_Iic.mpr le_rfl⟩, x) :=
    rfl
  rw [this]
  exact (h i).comp measurable_prodMk_left

中文:
定理 adapted
  条件: (h : IsProgressive f u)
  结论: Adapted f u
  证明: by
  intro i
  have : u i = (fun p : Set.Iic i × Ω => u p.1 p.2) ∘ fun x => (⟨i, Set.mem_Iic.mpr le_rfl⟩, x) :=
    rfl
  rw [this]
  exact (h i).comp measurable_prodMk_left
-/
protected theorem adapted (h : IsProgressive f u) : Adapted f u := by
  intro i
  have : u i = (fun p : Set.Iic i × Ω => u p.1 p.2) ∘ fun x => (⟨i, Set.mem_Iic.mpr le_rfl⟩, x) :=
    rfl
  rw [this]
  exact (h i).comp measurable_prodMk_left

/--
theorem `comp` / 定理 `comp`

English:
theorem comp
  statement: {t : ι -> Ω -> ι} (h : IsProgressive f u) (ht : IsProgressive f t)
  proof: by
  intro i
  have : (fun p : ↥(Set.Iic i) × Ω => u (t (p.fst : ι) p.snd) p.snd) =
    (fun p : ↥(Set.Iic i) × Ω => u (p.fst : ι) p.snd) ∘ fun p : ↥(Set.Iic i) × Ω =>
      (⟨t (p.fst : ι) p.snd, Set.mem_Iic.mpr ((ht_le _ _).trans p.fst.prop)⟩, p.snd) := rfl
  rw [this]
  exact (h i).comp ((ht i).s

中文:
定理 comp
  结论: {t : ι -> Ω -> ι} (h : IsProgressive f u) (ht : IsProgressive f t)
  证明: by
  intro i
  have : (fun p : ↥(Set.Iic i) × Ω => u (t (p.fst : ι) p.snd) p.snd) =
    (fun p : ↥(Set.Iic i) × Ω => u (p.fst : ι) p.snd) ∘ fun p : ↥(Set.Iic i) × Ω =>
      (⟨t (p.fst : ι) p.snd, Set.mem_Iic.mpr ((ht_le _ _).trans p.fst.prop)⟩, p.snd) := rfl
  rw [this]
  exact (h i).comp ((ht i).s
-/
protected theorem comp {t : ι -> Ω -> ι} (h : IsProgressive f u) (ht : IsProgressive f t)
    (ht_le : forall i ω, t i ω <= i) :
    IsProgressive f fun i ω => u (t i ω) ω := by
  intro i
  have : (fun p : ↥(Set.Iic i) × Ω => u (t (p.fst : ι) p.snd) p.snd) =
    (fun p : ↥(Set.Iic i) × Ω => u (p.fst : ι) p.snd) ∘ fun p : ↥(Set.Iic i) × Ω =>
      (⟨t (p.fst : ι) p.snd, Set.mem_Iic.mpr ((ht_le _ _).trans p.fst.prop)⟩, p.snd) := rfl
  rw [this]
  exact (h i).comp ((ht i).subtype_mk.prodMk measurable_snd)

section Arithmetic

@[to_additive]
/--
theorem `mul` / 定理 `mul`

English:
theorem mul
  statement: [Mul β] [MeasurableMul₂ β] (hu : IsProgressive f u)
  proof: fun i => Measurable.mul (hu i) (hv i)

@[to_additive]

中文:
定理 mul
  结论: [乘法 β] [MeasurableMul₂ β] (hu : IsProgressive f u)
  证明: fun i => Measurable.mul (hu i) (hv i)

@[to_additive]
-/
protected theorem mul [Mul β] [MeasurableMul₂ β] (hu : IsProgressive f u)
    (hv : IsProgressive f v) : IsProgressive f fun i ω => (u i ω * v i ω) :=
  fun i => Measurable.mul (hu i) (hv i)

@[to_additive]
/--
theorem `finsetProd` / 定理 `finsetProd`

English:
theorem finsetProd
  statement: {γ} [CommMonoid β] [MeasurableMul₂ β] {U : γ -> ι -> Ω -> β}
  proof: fun i => s.measurable_prod fun c hc => h c hc i

@[to_additive]

中文:
定理 finsetProd
  结论: {γ} [交换幺半群 β] [MeasurableMul₂ β] {U : γ -> ι -> Ω -> β}
  证明: fun i => s.measurable_prod fun c hc => h c hc i

@[to_additive]
-/
protected theorem finsetProd {γ} [CommMonoid β] [MeasurableMul₂ β] {U : γ -> ι -> Ω -> β}
    {s : Finset γ} (h : forall c in s, IsProgressive f (U c)) :
    IsProgressive f fun i ω => ∏ c in s, U c i ω :=
  fun i => s.measurable_prod fun c hc => h c hc i

@[to_additive]
/--
theorem `inv` / 定理 `inv`

English:
theorem inv
  given: [Group β] [MeasurableInv β] (hu : IsProgressive f u)
  proof: fun i => (hu i).inv

@[to_additive]

中文:
定理 inv
  条件: [群 β] [MeasurableInv β] (hu : IsProgressive f u)
  证明: fun i => (hu i).inv

@[to_additive]
-/
protected theorem inv [Group β] [MeasurableInv β] (hu : IsProgressive f u) :
    IsProgressive f fun i ω => (u i ω)⁻¹ := fun i => (hu i).inv

@[to_additive]
/--
theorem `div` / 定理 `div`

English:
theorem div
  statement: [Group β] [MeasurableDiv₂ β] (hu : IsProgressive f u)
  proof: fun i => Measurable.div (hu i) (hv i)

中文:
定理 div
  结论: [群 β] [MeasurableDiv₂ β] (hu : IsProgressive f u)
  证明: fun i => Measurable.div (hu i) (hv i)
-/
protected theorem div [Group β] [MeasurableDiv₂ β] (hu : IsProgressive f u)
    (hv : IsProgressive f v) : IsProgressive f fun i ω => u i ω / v i ω :=
  fun i => Measurable.div (hu i) (hv i)

/--
lemma `norm` / 引理 `norm`

English:
lemma norm
  given: [NormedAddCommGroup β] [OpensMeasurableSpace β] (hu : IsProgressive f u)
  proof: fun i => by apply @(hu i).norm; infer_instance

中文:
引理 norm
  条件: [赋范交换加群 β] [OpensMeasurable空间 β] (hu : IsProgressive f u)
  证明: fun i => by apply @(hu i).norm; infer_instance
-/
protected lemma norm [NormedAddCommGroup β] [OpensMeasurableSpace β] (hu : IsProgressive f u) :
    IsProgressive f fun t ω => ‖u t ω‖ :=
  fun i => by apply @(hu i).norm; infer_instance

end Arithmetic

end IsProgressive

end Progressive

variable {β : Type*} [TopologicalSpace β] {u v : ι -> Ω -> β}

/--
Definition of `IsStronglyProgressive` / `IsStronglyProgressive` 的定义

English:
definition IsStronglyProgressive
  signature: [MeasurableSpace ι] (f : Filtration ι m) (u : ι -> Ω -> β)
  body: forall i, StronglyMeasurable[Subtype.instMeasurableSpace.prod (f i)] fun p : Set.Iic i × Ω => u p.1 p.2

中文:
定义 IsStronglyProgressive
  签名: [可测空间 ι] (f : 滤子 ι m) (u : ι -> Ω -> β)
  定义体: forall i, StronglyMeasurable[Subtype.instMeasurableSpace.prod (f i)] fun p : Set.Iic i × Ω => u p.1 p.2

Depends on / 依赖: Set.Iic, StronglyMeasurable, Subtype, Subtype.instMeasurableSpace.prod, instMeasurableSpace
-/
def IsStronglyProgressive [MeasurableSpace ι] (f : Filtration ι m) (u : ι -> Ω -> β) : Prop :=
  forall i, StronglyMeasurable[Subtype.instMeasurableSpace.prod (f i)] fun p : Set.Iic i × Ω => u p.1 p.2

/--
theorem `isStronglyProgressive_const` / 定理 `isStronglyProgressive_const`

English:
theorem isStronglyProgressive_const
  given: [MeasurableSpace ι] (f : Filtration ι m) (b : β)
  proof: fun i =>
  @stronglyMeasurable_const _ _ (Subtype.instMeasurableSpace.prod (f i)) _ _

中文:
定理 isStronglyProgressive_const
  条件: [可测空间 ι] (f : 滤子 ι m) (b : β)
  证明: fun i =>
  @stronglyMeasurable_const _ _ (Subtype.instMeasurableSpace.prod (f i)) _ _
-/
theorem isStronglyProgressive_const [MeasurableSpace ι] (f : Filtration ι m) (b : β) :
    IsStronglyProgressive f (fun _ _ => b : ι -> Ω -> β) := fun i =>
  @stronglyMeasurable_const _ _ (Subtype.instMeasurableSpace.prod (f i)) _ _

namespace IsStronglyProgressive

variable [MeasurableSpace ι]

/--
theorem `stronglyAdapted` / 定理 `stronglyAdapted`

English:
theorem stronglyAdapted
  given: (h : IsStronglyProgressive f u)
  statement: StronglyAdapted f u
  proof: by
  intro i
  have : u i = (fun p : Set.Iic i × Ω => u p.1 p.2) ∘ fun x => (⟨i, Set.mem_Iic.mpr le_rfl⟩, x) :=
    rfl
  rw [this]
  exact (h i).comp_measurable measurable_prodMk_left

中文:
定理 stronglyAdapted
  条件: (h : IsStronglyProgressive f u)
  结论: StronglyAdapted f u
  证明: by
  intro i
  have : u i = (fun p : Set.Iic i × Ω => u p.1 p.2) ∘ fun x => (⟨i, Set.mem_Iic.mpr le_rfl⟩, x) :=
    rfl
  rw [this]
  exact (h i).comp_measurable measurable_prodMk_left
-/
protected theorem stronglyAdapted (h : IsStronglyProgressive f u) : StronglyAdapted f u := by
  intro i
  have : u i = (fun p : Set.Iic i × Ω => u p.1 p.2) ∘ fun x => (⟨i, Set.mem_Iic.mpr le_rfl⟩, x) :=
    rfl
  rw [this]
  exact (h i).comp_measurable measurable_prodMk_left

/--
theorem `comp` / 定理 `comp`

English:
theorem comp
  statement: {t : ι -> Ω -> ι} [TopologicalSpace ι] [BorelSpace ι] [PseudoMetrizableSpace ι]
  proof: by
  intro i
  have : (fun p : ↥(Set.Iic i) × Ω => u (t (p.fst : ι) p.snd) p.snd) =
    (fun p : ↥(Set.Iic i) × Ω => u (p.fst : ι) p.snd) ∘ fun p : ↥(Set.Iic i) × Ω =>
      (⟨t (p.fst : ι) p.snd, Set.mem_Iic.mpr ((ht_le _ _).trans p.fst.prop)⟩, p.snd) := rfl
  rw [this]
  exact (h i).comp_measurabl

中文:
定理 comp
  结论: {t : ι -> Ω -> ι} [拓扑空间 ι] [Borel空间 ι] [PseudoMetrizable空间 ι]
  证明: by
  intro i
  have : (fun p : ↥(Set.Iic i) × Ω => u (t (p.fst : ι) p.snd) p.snd) =
    (fun p : ↥(Set.Iic i) × Ω => u (p.fst : ι) p.snd) ∘ fun p : ↥(Set.Iic i) × Ω =>
      (⟨t (p.fst : ι) p.snd, Set.mem_Iic.mpr ((ht_le _ _).trans p.fst.prop)⟩, p.snd) := rfl
  rw [this]
  exact (h i).comp_measurabl
-/
protected theorem comp {t : ι -> Ω -> ι} [TopologicalSpace ι] [BorelSpace ι] [PseudoMetrizableSpace ι]
    (h : IsStronglyProgressive f u) (ht : IsStronglyProgressive f t) (ht_le : forall i ω, t i ω <= i) :
    IsStronglyProgressive f fun i ω => u (t i ω) ω := by
  intro i
  have : (fun p : ↥(Set.Iic i) × Ω => u (t (p.fst : ι) p.snd) p.snd) =
    (fun p : ↥(Set.Iic i) × Ω => u (p.fst : ι) p.snd) ∘ fun p : ↥(Set.Iic i) × Ω =>
      (⟨t (p.fst : ι) p.snd, Set.mem_Iic.mpr ((ht_le _ _).trans p.fst.prop)⟩, p.snd) := rfl
  rw [this]
  exact (h i).comp_measurable ((ht i).measurable.subtype_mk.prodMk measurable_snd)

section Arithmetic

@[to_additive]
/--
theorem `mul` / 定理 `mul`

English:
theorem mul
  statement: [Mul β] [ContinuousMul β] (hu : IsStronglyProgressive f u)
  proof: fun i =>
  (hu i).mul (hv i)

@[to_additive]

中文:
定理 mul
  结论: [乘法 β] [连续乘法 β] (hu : IsStronglyProgressive f u)
  证明: fun i =>
  (hu i).mul (hv i)

@[to_additive]
-/
protected theorem mul [Mul β] [ContinuousMul β] (hu : IsStronglyProgressive f u)
    (hv : IsStronglyProgressive f v) : IsStronglyProgressive f fun i ω => u i ω * v i ω := fun i =>
  (hu i).mul (hv i)

@[to_additive]
/--
theorem `finsetProd'` / 定理 `finsetProd'`

English:
theorem finsetProd'
  statement: {γ} [CommMonoid β] [ContinuousMul β] {U : γ -> ι -> Ω -> β}
  proof: Finset.prod_induction U (IsStronglyProgressive f) (fun _ _ => .mul)
    (isStronglyProgressive_const _ 1) h

@[deprecated (since := "2026-04-08")]
protected alias finset_sum' := MeasureTheory.IsStronglyProgressive.finsetSum'

@[to_additive existing, deprecated (since := "2026-04-08")]
protected alia

中文:
定理 finsetProd'
  结论: {γ} [交换幺半群 β] [连续乘法 β] {U : γ -> ι -> Ω -> β}
  证明: Finset.prod_induction U (IsStronglyProgressive f) (fun _ _ => .mul)
    (isStronglyProgressive_const _ 1) h

@[deprecated (since := "2026-04-08")]
protected alias finset_sum' := MeasureTheory.IsStronglyProgressive.finsetSum'

@[to_additive existing, deprecated (since := "2026-04-08")]
protected alia
-/
protected theorem finsetProd' {γ} [CommMonoid β] [ContinuousMul β] {U : γ -> ι -> Ω -> β}
    {s : Finset γ} (h : forall c in s, IsStronglyProgressive f (U c)) :
    IsStronglyProgressive f (∏ c in s, U c) :=
  Finset.prod_induction U (IsStronglyProgressive f) (fun _ _ => .mul)
    (isStronglyProgressive_const _ 1) h

@[deprecated (since := "2026-04-08")]
protected alias finset_sum' := MeasureTheory.IsStronglyProgressive.finsetSum'

@[to_additive existing, deprecated (since := "2026-04-08")]
protected alias finset_prod' := MeasureTheory.IsStronglyProgressive.finsetProd'

@[to_additive]
/--
theorem `finsetProd` / 定理 `finsetProd`

English:
theorem finsetProd
  statement: {γ} [CommMonoid β] [ContinuousMul β] {U : γ -> ι -> Ω -> β}
  proof: by
  convert! IsStronglyProgressive.finsetProd' h using 1; ext (i a); simp only [Finset.prod_apply]

@[deprecated (since := "2026-04-08")]
protected alias finset_sum := MeasureTheory.IsStronglyProgressive.finsetSum

@[to_additive existing, deprecated (since := "2026-04-08")]
protected alias finset_p

中文:
定理 finsetProd
  结论: {γ} [交换幺半群 β] [连续乘法 β] {U : γ -> ι -> Ω -> β}
  证明: by
  convert! IsStronglyProgressive.finsetProd' h using 1; ext (i a); simp only [Finset.prod_apply]

@[deprecated (since := "2026-04-08")]
protected alias finset_sum := MeasureTheory.IsStronglyProgressive.finsetSum

@[to_additive existing, deprecated (since := "2026-04-08")]
protected alias finset_p
-/
protected theorem finsetProd {γ} [CommMonoid β] [ContinuousMul β] {U : γ -> ι -> Ω -> β}
    {s : Finset γ} (h : forall c in s, IsStronglyProgressive f (U c)) :
    IsStronglyProgressive f fun i a => ∏ c in s, U c i a := by
  convert! IsStronglyProgressive.finsetProd' h using 1; ext (i a); simp only [Finset.prod_apply]

@[deprecated (since := "2026-04-08")]
protected alias finset_sum := MeasureTheory.IsStronglyProgressive.finsetSum

@[to_additive existing, deprecated (since := "2026-04-08")]
protected alias finset_prod := MeasureTheory.IsStronglyProgressive.finsetProd

@[to_additive]
/--
theorem `inv` / 定理 `inv`

English:
theorem inv
  given: [Group β] [ContinuousInv β] (hu : IsStronglyProgressive f u)
  proof: fun i => (hu i).inv

@[to_additive sub]

中文:
定理 inv
  条件: [群 β] [连续取逆 β] (hu : IsStronglyProgressive f u)
  证明: fun i => (hu i).inv

@[to_additive sub]
-/
protected theorem inv [Group β] [ContinuousInv β] (hu : IsStronglyProgressive f u) :
    IsStronglyProgressive f fun i ω => (u i ω)⁻¹ := fun i => (hu i).inv

@[to_additive sub]
/--
theorem `div'` / 定理 `div'`

English:
theorem div'
  statement: [Group β] [ContinuousDiv β] (hu : IsStronglyProgressive f u)
  proof: fun i =>
  (hu i).div' (hv i)

中文:
定理 div'
  结论: [群 β] [余ntinuousDiv β] (hu : IsStronglyProgressive f u)
  证明: fun i =>
  (hu i).div' (hv i)
-/
protected theorem div' [Group β] [ContinuousDiv β] (hu : IsStronglyProgressive f u)
    (hv : IsStronglyProgressive f v) : IsStronglyProgressive f fun i ω => u i ω / v i ω := fun i =>
  (hu i).div' (hv i)

/--
lemma `norm` / 引理 `norm`

English:
lemma norm
  statement: {β : Type*} {u : ι -> Ω -> β} [SeminormedAddCommGroup β]
  proof: fun t => (hu t).norm

中文:
引理 norm
  结论: {β : 类型} {u : ι -> Ω -> β} [SeminormedAddComm群 β]
  证明: fun t => (hu t).norm
-/
protected lemma norm {β : Type*} {u : ι -> Ω -> β} [SeminormedAddCommGroup β]
    (hu : IsStronglyProgressive f u) :
    IsStronglyProgressive f fun t ω => ‖u t ω‖ := fun t => (hu t).norm

end Arithmetic

end IsStronglyProgressive

/--
lemma `IsProgressive.isStronglyProgressive` / 引理 `IsProgressive.isStronglyProgressive`

English:
lemma IsProgressive.isStronglyProgressive
  statement: {mi : MeasurableSpace ι} {mβ : MeasurableSpace β}
  proof: fun i => (h i).stronglyMeasurable

中文:
引理 IsProgressive.isStronglyProgressive
  结论: {mi : 可测空间 ι} {mβ : 可测空间 β}
  证明: fun i => (h i).stronglyMeasurable

Depends on / 依赖: stronglyMeasurable
-/
lemma IsProgressive.isStronglyProgressive {mi : MeasurableSpace ι} {mβ : MeasurableSpace β}
    [PseudoMetrizableSpace β] [SecondCountableTopology β] [OpensMeasurableSpace β]
  (h : IsProgressive f u) : IsStronglyProgressive f u :=
  fun i => (h i).stronglyMeasurable

/--
lemma `IsStronglyProgressive.isProgressive` / 引理 `IsStronglyProgressive.isProgressive`

English:
lemma IsStronglyProgressive.isProgressive
  statement: {mi : MeasurableSpace ι} {mβ : MeasurableSpace β}
  proof: fun i => (h i).measurable

中文:
引理 IsStronglyProgressive.isProgressive
  结论: {mi : 可测空间 ι} {mβ : 可测空间 β}
  证明: fun i => (h i).measurable

Depends on / 依赖: measurable
-/
lemma IsStronglyProgressive.isProgressive {mi : MeasurableSpace ι} {mβ : MeasurableSpace β}
    [PseudoMetrizableSpace β] [BorelSpace β] (h : IsStronglyProgressive f u) : IsProgressive f u :=
  fun i => (h i).measurable

/--
theorem `isStronglyProgressive_of_tendsto'` / 定理 `isStronglyProgressive_of_tendsto'`

English:
theorem isStronglyProgressive_of_tendsto'
  statement: {γ} [MeasurableSpace ι] [PseudoMetrizableSpace β]
  proof: by
  intro i
  apply @stronglyMeasurable_of_tendsto (Set.Iic i × Ω) β γ
    (MeasurableSpace.prod _ (f i)) _ _ fltr _ _ _ _ fun l => h l i
  rw [tendsto_pi_nhds] at h_tendsto ⊢
  exact fun _ => Tendsto.apply_nhds (h_tendsto _) _

中文:
定理 isStronglyProgressive_of_tendsto'
  结论: {γ} [可测空间 ι] [PseudoMetrizable空间 β]
  证明: by
  intro i
  apply @stronglyMeasurable_of_tendsto (Set.Iic i × Ω) β γ
    (MeasurableSpace.prod _ (f i)) _ _ fltr _ _ _ _ fun l => h l i
  rw [tendsto_pi_nhds] at h_tendsto ⊢
  exact fun _ => Tendsto.apply_nhds (h_tendsto _) _

Depends on / 依赖: MeasurableSpace, MeasurableSpace.prod, Set.Iic, Tendsto, Tendsto.apply_nhds, apply_nhds, h_tendsto, stronglyMeasurable_of_tendsto, tendsto_pi_nhds
-/
theorem isStronglyProgressive_of_tendsto' {γ} [MeasurableSpace ι] [PseudoMetrizableSpace β]
    (fltr : Filter γ) [fltr.NeBot] [fltr.IsCountablyGenerated] {U : γ -> ι -> Ω -> β}
    (h : forall l, IsStronglyProgressive f (U l)) (h_tendsto : Tendsto U fltr (𝓝 u)) :
    IsStronglyProgressive f u := by
  intro i
  apply @stronglyMeasurable_of_tendsto (Set.Iic i × Ω) β γ
    (MeasurableSpace.prod _ (f i)) _ _ fltr _ _ _ _ fun l => h l i
  rw [tendsto_pi_nhds] at h_tendsto ⊢
  exact fun _ => Tendsto.apply_nhds (h_tendsto _) _

/--
theorem `isStronglyProgressive_of_tendsto` / 定理 `isStronglyProgressive_of_tendsto`

English:
theorem isStronglyProgressive_of_tendsto
  statement: [MeasurableSpace ι] [PseudoMetrizableSpace β]
  proof: isStronglyProgressive_of_tendsto' atTop h h_tendsto

中文:
定理 isStronglyProgressive_of_tendsto
  结论: [可测空间 ι] [PseudoMetrizable空间 β]
  证明: isStronglyProgressive_of_tendsto' atTop h h_tendsto

Depends on / 依赖: h_tendsto, isStronglyProgressive_of_tendsto
-/
theorem isStronglyProgressive_of_tendsto [MeasurableSpace ι] [PseudoMetrizableSpace β]
    {U : Nat -> ι -> Ω -> β} (h : forall l, IsStronglyProgressive f (U l))
    (h_tendsto : Tendsto U atTop (𝓝 u)) : IsStronglyProgressive f u :=
  isStronglyProgressive_of_tendsto' atTop h h_tendsto

/--
theorem `StronglyAdapted.isStronglyProgressive_of_continuous` / 定理 `StronglyAdapted.isStronglyProgressive_of_continuous`

English:
theorem StronglyAdapted.isStronglyProgressive_of_continuous
  statement: [TopologicalSpace ι] [MetrizableSpace ι]
  proof: fun i =>
  @stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable _ _ (Set.Iic i) _ _ _ _ _ _ _
    (f i) _ (fun ω => (hu_cont ω).comp continuous_induced_dom) fun j => (h j).mono (f.mono j.prop)

中文:
定理 StronglyAdapted.isStronglyProgressive_of_continuous
  结论: [拓扑空间 ι] [Metrizable空间 ι]
  证明: fun i =>
  @stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable _ _ (Set.Iic i) _ _ _ _ _ _ _
    (f i) _ (fun ω => (hu_cont ω).comp continuous_induced_dom) fun j => (h j).mono (f.mono j.prop)
-/
theorem StronglyAdapted.isStronglyProgressive_of_continuous [TopologicalSpace ι] [MetrizableSpace ι]
    [SecondCountableTopology ι] [MeasurableSpace ι] [OpensMeasurableSpace ι]
    [PseudoMetrizableSpace β] (h : StronglyAdapted f u) (hu_cont : forall ω, Continuous fun i => u i ω) :
    IsStronglyProgressive f u := fun i =>
  @stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable _ _ (Set.Iic i) _ _ _ _ _ _ _
    (f i) _ (fun ω => (hu_cont ω).comp continuous_induced_dom) fun j => (h j).mono (f.mono j.prop)

/--
theorem `StronglyAdapted.isStronglyProgressive_of_discrete` / 定理 `StronglyAdapted.isStronglyProgressive_of_discrete`

English:
theorem StronglyAdapted.isStronglyProgressive_of_discrete
  statement: [TopologicalSpace ι] [DiscreteTopology ι]
  proof: h.isStronglyProgressive_of_continuous fun _ => continuous_of_discreteTopology

@[deprecated (since := "2026-04-24")] alias ProgMeasurable := IsStronglyProgressive

@[deprecated (since := "2026-04-24")] alias progMeasurable_const := isStronglyProgressive_const

@[deprecated (since := "2026-04-24")]
a

中文:
定理 StronglyAdapted.isStronglyProgressive_of_discrete
  结论: [拓扑空间 ι] [离散拓扑 ι]
  证明: h.isStronglyProgressive_of_continuous fun _ => continuous_of_discreteTopology

@[deprecated (since := "2026-04-24")] alias ProgMeasurable := IsStronglyProgressive

@[deprecated (since := "2026-04-24")] alias progMeasurable_const := isStronglyProgressive_const

@[deprecated (since := "2026-04-24")]
a

Depends on / 依赖: continuous_of_discreteTopology, h.isStronglyProgressive_of_continuous, isStronglyProgressive_of_continuous
-/
theorem StronglyAdapted.isStronglyProgressive_of_discrete [TopologicalSpace ι] [DiscreteTopology ι]
    [SecondCountableTopology ι] [MeasurableSpace ι] [OpensMeasurableSpace ι]
    [PseudoMetrizableSpace β] (h : StronglyAdapted f u) : IsStronglyProgressive f u :=
  h.isStronglyProgressive_of_continuous fun _ => continuous_of_discreteTopology

@[deprecated (since := "2026-04-24")] alias ProgMeasurable := IsStronglyProgressive

@[deprecated (since := "2026-04-24")] alias progMeasurable_const := isStronglyProgressive_const

@[deprecated (since := "2026-04-24")]
alias ProgMeasurable.stronglyAdapted := IsStronglyProgressive.stronglyAdapted

@[deprecated (since := "2026-04-24")] alias ProgMeasurable.comp := IsStronglyProgressive.comp

@[deprecated (since := "2026-04-24")] alias ProgMeasurable.add := IsStronglyProgressive.add

@[to_additive existing, deprecated (since := "2026-04-24")]
alias ProgMeasurable.mul := IsStronglyProgressive.mul

@[deprecated (since := "2026-04-24")]
alias ProgMeasurable.finset_sum' := IsStronglyProgressive.finsetSum'

@[to_additive existing, deprecated (since := "2026-04-24")]
alias ProgMeasurable.finset_prod' := IsStronglyProgressive.finsetProd'

@[deprecated (since := "2026-04-24")]
alias ProgMeasurable.finset_sum := IsStronglyProgressive.finsetSum

@[to_additive existing, deprecated (since := "2026-04-24")]
alias ProgMeasurable.finset_prod := IsStronglyProgressive.finsetProd

@[deprecated (since := "2026-04-24")]
alias ProgMeasurable.neg := IsStronglyProgressive.neg

@[to_additive existing, deprecated (since := "2026-04-24")]
alias ProgMeasurable.inv := IsStronglyProgressive.inv

@[deprecated (since := "2026-04-24")] alias ProgMeasurable.sub := IsStronglyProgressive.sub

@[to_additive existing ProgMeasurable.sub, deprecated (since := "2026-04-24")]
alias ProgMeasurable.div' := IsStronglyProgressive.div'

@[deprecated (since := "2026-04-24")] alias ProgMeasurable.norm := IsStronglyProgressive.norm

@[deprecated (since := "2026-04-24")]
alias progMeasurable_of_tendsto := isStronglyProgressive_of_tendsto

@[deprecated (since := "2026-04-24")]
alias progMeasurable_of_tendsto' := isStronglyProgressive_of_tendsto'

@[deprecated (since := "2026-04-24")]
alias StronglyAdapted.progMeasurable_of_continuous :=
  StronglyAdapted.isStronglyProgressive_of_continuous

@[deprecated (since := "2026-04-24")]
alias StronglyAdapted.progMeasurable_of_discrete :=
  StronglyAdapted.isStronglyProgressive_of_discrete

end MeasureTheory
