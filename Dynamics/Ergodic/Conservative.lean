/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.Combinatorics.Pigeonhole

/-!
# Conservative systems

In this file we define `f : α → α` to be a *conservative* system w.r.t. a measure `μ` if `f` is
non-singular (`MeasureTheory.QuasiMeasurePreserving`) and for every measurable set `s` of
positive measure at least one point `x ∈ s` returns back to `s` after some number of iterations of
`f`. There are several properties that look like they are stronger than this one but actually follow
from it:

* `MeasureTheory.Conservative.frequently_measure_inter_ne_zero`,
  `MeasureTheory.Conservative.exists_gt_measure_inter_ne_zero`: if `μ s ≠ 0`, then for infinitely
  many `n`, the measure of `s ∩ f^[n] ⁻¹' s` is positive.

* `MeasureTheory.Conservative.measure_mem_forall_ge_image_notMem_eq_zero`,
  `MeasureTheory.Conservative.ae_mem_imp_frequently_image_mem`: a.e. every point of `s` visits `s`
  infinitely many times (Poincaré recurrence theorem).

We also prove the topological Poincaré recurrence theorem
`MeasureTheory.Conservative.ae_frequently_mem_of_mem_nhds`. Let `f : α → α` be a conservative
dynamical system on a topological space with second countable topology and measurable open
sets. Then almost every point `x : α` is recurrent: it visits every neighborhood `s ∈ 𝓝 x`
infinitely many times.

## Tags

conservative dynamical system, Poincare recurrence theorem
-/

public section


noncomputable section

namespace MeasureTheory

open Set Filter Finset Function TopologicalSpace Topology

variable {α : Type*} [MeasurableSpace α] {f : α → α} {s : Set α} {μ : Measure α}

open Measure

/-- We say that a non-singular (`MeasureTheory.QuasiMeasurePreserving`) self-map is
*conservative* if for any measurable set `s` of positive measure there exists `x ∈ s` such that `x`
returns back to `s` under some iteration of `f`. -/
/-
**MeasureTheory.Conservative** 是 Mathlib 中的一个结构，位于命名空间 `MeasureTheory`。
形式化陈述：Conservative (f : α -> α) (μ : Measure α) : Prop extends QuasiMeasurePrese
rving f μ μ where /-- If `f` is a conservative self-map and `s` is a measurable 
set of nonzero measure, then there exists a point `x ∈ s` that returns to `s` un
der a non-zero iteration of `f`. -/ exists_mem_iterate_mem' : forall ⦃s⦄, Measur
ableSet s -> μ s != 0 -> exists x in s, exists m != 0, f^[m] x in s  /-- A self-
map preserving a finite measure is conservative. -/ protected theorem MeasurePre
serving.conservative [IsFi
参数：f : α -> α；μ : Measure α。
继承自：QuasiMeasurePreserving f μ μ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say that a non-singular (`MeasureTheory.QuasiMeasurePreserving`) self-map is
*conservative* if for any measurable set `s` of positive measure there exists `x
 ∈ s` such that `x`
returns back to `s` under some iteration of `f`.
-/
structure Conservative (f : α → α) (μ : Measure α) : Prop extends QuasiMeasurePreserving f μ μ where
  /-- If `f` is a conservative self-map and `s` is a measurable set of nonzero measure,
  then there exists a point `x ∈ s` that returns to `s` under a non-zero iteration of `f`. -/
  exists_mem_iterate_mem' : ∀ ⦃s⦄, MeasurableSet s → μ s ≠ 0 → ∃ x ∈ s, ∃ m ≠ 0, f^[m] x ∈ s

/-- A self-map preserving a finite measure is conservative. -/
/-
**MeasureTheory.MeasurePreserving.conservative** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.MeasurePreserving`。
形式化陈述：∀ {α : Type u_1} [inst : MeasurableSpace α] {f : α → α} {μ : MeasureTheory
.Measure α} [MeasureTheory.IsFiniteMeasure μ],   MeasureTheory.MeasurePreserving
 f μ μ → MeasureTheory.Conservative f μ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.MeasurePreserving.quasiMeasurePreserving`：∀ {α : Type u_1}
 {β : Type u_2} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {μa : Me
asureTheory.Measure α}   {μb : MeasureTheory…
· 使用定理 `MeasureTheory.MeasurePreserving.exists_mem_iterate_mem`：exists_mem_itera
te_mem [IsFiniteMeasure μ] (hf : MeasurePreserving f μ μ) (hs : NullMeasurableSe
t s μ) (hs' : μ s != 0) : exists x in s, exi…
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ

--- 原说明 ---
A self-map preserving a finite measure is conservative.
-/
protected theorem MeasurePreserving.conservative [IsFiniteMeasure μ] (h : MeasurePreserving f μ μ) :
    Conservative f μ :=
  ⟨h.quasiMeasurePreserving, fun _ hsm h0 => h.exists_mem_iterate_mem hsm.nullMeasurableSet h0⟩

namespace Conservative

/-- The identity map is conservative w.r.t. any measure. -/
/-
**MeasureTheory.Conservative.id** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Conserv
ative`。
形式化陈述：∀ {α : Type u_1} [inst : MeasurableSpace α] (μ : MeasureTheory.Measure α),
 MeasureTheory.Conservative id μ
参数：μ : MeasureTheory.Measure α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.QuasiMeasurePreserving.id`：∀ {α : Type u_1} {_m0 :
 MeasurableSpace α} (μ : MeasureTheory.Measure α),   MeasureTheory.Measure.Quasi
MeasurePreserving id μ μ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Function.iterate_id`：iterate_id (n : Nat) : (id : α -> α)^[n] = id
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `MeasureTheory.nonempty_of_measure_ne_zero`：nonempty_of_measure_ne_zero (
h : μ s != 0) : s.Nonempty

--- 原说明 ---
The identity map is conservative w.r.t. any measure.
-/
protected theorem id (μ : Measure α) : Conservative id μ :=
  { toQuasiMeasurePreserving := QuasiMeasurePreserving.id μ
    exists_mem_iterate_mem' := fun _ _ h0 => by
      simpa [exists_ne] using! nonempty_of_measure_ne_zero h0 }
/-
**MeasureTheory.Conservative.of_absolutelyContinuous** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory.Conservative`。
形式化陈述：of_absolutelyContinuous {ν : Measure α} (h : Conservative f μ) (hν : ν ≪ μ
) (h' : QuasiMeasurePreserving f ν ν) : Conservative f ν
参数：h : Conservative f μ；hν : ν ≪ μ；h' : QuasiMeasurePreserving f ν ν。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Conservative.exists_mem_iterate_mem'`：∀ {α : Type u_1} [in
st : MeasurableSpace α] {f : α → α} {μ : MeasureTheory.Measure α},   MeasureTheo
ry.Conservative f μ → ∀ ⦃s : Set α⦄, Mea…
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
-/
theorem of_absolutelyContinuous {ν : Measure α} (h : Conservative f μ) (hν : ν ≪ μ)
    (h' : QuasiMeasurePreserving f ν ν) : Conservative f ν :=
  ⟨h', fun _ hsm h0 ↦ h.exists_mem_iterate_mem' hsm (mt (@hν _) h0)⟩

/-- Restriction of a conservative system to an invariant set is a conservative system,
formulated in terms of the restriction of the measure. -/
/-
**MeasureTheory.Conservative.measureRestrict** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.Conservative`。
形式化陈述：measureRestrict (h : Conservative f μ) (hs : MapsTo f s s) : Conservative 
f (μ.restrict s)
参数：h : Conservative f μ；hs : MapsTo f s s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Conservative.of_absolutelyContinuous`：of_absolutelyContinu
ous {ν : Measure α} (h : Conservative f μ) (hν : ν ≪ μ) (h' : QuasiMeasurePreser
ving f ν ν) : Conservative f ν
· 使用定理 `MeasureTheory.Measure.absolutelyContinuous_of_le`：absolutelyContinuous_o
f_le (h : μ <= ν) : μ ≪ ν
· 使用定理 `MeasureTheory.Measure.restrict_le_self`：restrict_le_self : μ.restrict s 
<= μ
· 使用定理 `MeasureTheory.Measure.QuasiMeasurePreserving.restrict`：∀ {α : Type u_2} 
{β : Type u_3} {m0 : MeasurableSpace α} [inst : MeasurableSpace β] {μ : MeasureT
heory.Measure α}   {s : Set α} {ν : Measure…
· 使用定理 `MeasureTheory.Conservative.toQuasiMeasurePreserving`：∀ {α : Type u_1} [i
nst : MeasurableSpace α] {f : α → α} {μ : MeasureTheory.Measure α},   MeasureThe
ory.Conservative f μ → MeasureTheory.Meas…

--- 原说明 ---
Restriction of a conservative system to an invariant set is a conservative syste
m,
formulated in terms of the restriction of the measure.
-/
theorem measureRestrict (h : Conservative f μ) (hs : MapsTo f s s) :
    Conservative f (μ.restrict s) :=
  .of_absolutelyContinuous h (absolutelyContinuous_of_le restrict_le_self) <|
    h.toQuasiMeasurePreserving.restrict hs
/-
**MeasureTheory.Conservative.congr_ae** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.C
onservative`。
形式化陈述：congr_ae {ν : Measure α} (hf : Conservative f μ) (h : ae μ = ae ν) : Conse
rvative f ν
参数：hf : Conservative f μ；h : ae μ = ae ν。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Conservative.of_absolutelyContinuous`：of_absolutelyContinu
ous {ν : Measure α} (h : Conservative f μ) (hν : ν ≪ μ) (h' : QuasiMeasurePreser
ving f ν ν) : Conservative f ν
· 使用定理 `LE.le.absolutelyContinuous_of_ae`：∀ {α : Type u_1} {mα : MeasurableSpace
 α} {μ ν : MeasureTheory.Measure α},   MeasureTheory.ae μ ≤ MeasureTheory.ae ν →
 μ.AbsolutelyContinuou…
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `MeasureTheory.Measure.QuasiMeasurePreserving.mono`：mono (ha : μa' ≪ μa) 
(hb : μb ≪ μb') (h : QuasiMeasurePreserving f μa μb) : QuasiMeasurePreserving f 
μa' μb'
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `MeasureTheory.Conservative.toQuasiMeasurePreserving`：∀ {α : Type u_1} [i
nst : MeasurableSpace α] {f : α → α} {μ : MeasureTheory.Measure α},   MeasureThe
ory.Conservative f μ → MeasureTheory.Meas…
-/
theorem congr_ae {ν : Measure α} (hf : Conservative f μ) (h : ae μ = ae ν) :
    Conservative f ν :=
  .of_absolutelyContinuous hf h.ge.absolutelyContinuous_of_ae <|
    hf.toQuasiMeasurePreserving.mono h.ge.absolutelyContinuous_of_ae h.le.absolutelyContinuous_of_ae
/-
**MeasureTheory.Conservative._root_.MeasureTheory.conservative_congr** 是 Mathlib
 中的一个定理，位于命名空间 `MeasureTheory.Conservative`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MeasureTheory.conservative_congr {ν : Measure α} (h : ae μ = ae ν) :
    Conservative f μ ↔ Conservative f ν :=
  ⟨(congr_ae · h), (congr_ae · h.symm)⟩

/-- If `f` is a conservative self-map and `s` is a null measurable set of nonzero measure,
then there exists a point `x ∈ s` that returns to `s` under a non-zero iteration of `f`. -/
/-
**MeasureTheory.Conservative.exists_mem_iterate_mem** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory.Conservative`。
形式化陈述：exists_mem_iterate_mem (hf : Conservative f μ) (hsm : NullMeasurableSet s 
μ) (hs₀ : μ s != 0) : exists x in s, exists m != 0, f^[m] x in s
参数：hf : Conservative f μ；hsm : NullMeasurableSet s μ；hs₀ : μ s != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.NullMeasurableSet.exists_measurable_subset_ae_eq`：exists_m
easurable_subset_ae_eq (h : NullMeasurableSet s μ) : exists t subseteq s, Measur
ableSet t ∧ t =ᵐ[μ] s
· 使用定理 `MeasureTheory.Conservative.exists_mem_iterate_mem'`：∀ {α : Type u_1} [in
st : MeasurableSpace α] {f : α → α} {μ : MeasureTheory.Measure α},   MeasureTheo
ry.Conservative f μ → ∀ ⦃s : Set α⦄, Mea…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.measure_congr`：measure_congr (H : s =ᵐ[μ] t) : μ s = μ t

--- 原说明 ---
If `f` is a conservative self-map and `s` is a null measurable set of nonzero me
asure,
then there exists a point `x ∈ s` that returns to `s` under a non-zero iteration
 of `f`.
-/
theorem exists_mem_iterate_mem (hf : Conservative f μ)
    (hsm : NullMeasurableSet s μ) (hs₀ : μ s ≠ 0) :
    ∃ x ∈ s, ∃ m ≠ 0, f^[m] x ∈ s := by
  rcases hsm.exists_measurable_subset_ae_eq with ⟨t, hsub, htm, hts⟩
  rcases hf.exists_mem_iterate_mem' htm (by rwa [measure_congr hts]) with ⟨x, hxt, m, hm₀, hmt⟩
  exact ⟨x, hsub hxt, m, hm₀, hsub hmt⟩

/-- If `f` is a conservative map and `s` is a measurable set of nonzero measure, then
for infinitely many values of `m` a positive measure of points `x ∈ s` returns back to `s`
after `m` iterations of `f`. -/
/-
**MeasureTheory.Conservative.frequently_measure_inter_ne_zero** 是 Mathlib 中的一个定理
，位于命名空间 `MeasureTheory.Conservative`。
形式化陈述：frequently_measure_inter_ne_zero (hf : Conservative f μ) (hs : NullMeasura
bleSet s μ) (h0 : μ s != 0) : existsᶠ m in atTop, μ (s inter f^[m] ⁻¹' s) != 0
参数：hf : Conservative f μ；hs : NullMeasurableSet s μ；h0 : μ s != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `pi_congr`：∀ {α : Sort u} {β β' : α → Sort v}, (∀ (a : α), β a = β' a) → 
((a : α) → β a) = ((a : α) → β' a)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `gt_iff_lt`：∀ {α : Type u_1} [inst : LT α] {x y : α}, x > y ↔ y < x
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `not_imp_comm`：not_imp_comm : ¬a -> b ↔ ¬b -> a
· 使用定理 `Set.mem_ofPred`：mem_ofPred {a : α} {p : α -> Prop} : a in { x | p x } ↔ 
p a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Set.exists_max_image`：∀ {α : Type u} {β : Type v} [inst : LinearOrder β]
 (s : Set α) (f : α → β),   s.Finite → s.Nonempty → ∃ a ∈ s, ∀ b ∈ s, f b ≤ f a
· 使用定理 `Set.not_infinite`：not_infinite {s : Set α} : ¬s.Infinite ↔ s.Finite
· 使用定理 `Nat.frequently_atTop_iff_infinite`：Nat.frequently_atTop_iff_infinite {p 
: Nat -> Prop} : (existsᶠ n in atTop, p n) ↔ Set.Infinite { n | p n }
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.inter_self`：inter_self (a : Set α) : a inter a = a
· 使用定理 `MeasureTheory.NullMeasurableSet.inter`：∀ {α : Type u_2} {m0 : Measurable
Space α} {μ : MeasureTheory.Measure α} {s t : Set α},   MeasureTheory.NullMeasur
ableSet s μ → MeasureTheory…
· 使用定理 `MeasureTheory.NullMeasurableSet.preimage`：∀ {α : Type u_1} {β : Type u_2
} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μa : MeasureTheory.Measure 
α}   {μb : MeasureTheory.Measu…
· 使用定理 `MeasureTheory.Measure.QuasiMeasurePreserving.iterate`：∀ {α : Type u_1} {
mα : MeasurableSpace α} {μa : MeasureTheory.Measure α} {f : α → α},   MeasureThe
ory.Measure.QuasiMeasurePreserving f μa μa…
· 使用定理 `MeasureTheory.Conservative.toQuasiMeasurePreserving`：∀ {α : Type u_1} [i
nst : MeasurableSpace α] {f : α → α} {μ : MeasureTheory.Measure α},   MeasureThe
ory.Conservative f μ → MeasureTheory.Meas…
· 使用定理 `MeasureTheory.measure_sdiff_null`：measure_sdiff_null (ht : μ t = 0) : μ 
(s \ t) = μ s
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.measure_biUnion_null_iff`：measure_biUnion_null_iff {I : Se
t ι} (hI : I.Countable) {s : ι -> Set α} : μ (⋃ i in I, s i) = 0 ↔ forall i in I
, μ (s i) = 0
· 使用定理 `Set.to_countable`：to_countable (s : Set α) [Countable s] : s.Countable
· 使用定理 `SetCoe.countable`：∀ {α : Type u} [Countable α] (s : Set α), Countable ↑s
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `MeasureTheory.NullMeasurableSet.diff`：∀ {α : Type u_2} {m0 : MeasurableS
pace α} {μ : MeasureTheory.Measure α} {s t : Set α},   MeasureTheory.NullMeasura
bleSet s μ → MeasureTheory…
· 使用定理 `MeasureTheory.NullMeasurableSet.biUnion`：∀ {ι : Type u_1} {α : Type u_2}
 {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} {f : ι → Set α} {s : Set
 ι},   s.Countable → (∀ b ∈ s…
· 使用定理 `MeasureTheory.Conservative.exists_mem_iterate_mem`：exists_mem_iterate_me
m (hf : Conservative f μ) (hsm : NullMeasurableSet s μ) (hs₀ : μ s != 0) : exist
s x in s, exists m != 0, f^[m] x in s
（共 40 条，此处仅展示前 30 条）

--- 原说明 ---
If `f` is a conservative map and `s` is a measurable set of nonzero measure, the
n
for infinitely many values of `m` a positive measure of points `x ∈ s` returns b
ack to `s`
after `m` iterations of `f`.
-/
theorem frequently_measure_inter_ne_zero (hf : Conservative f μ) (hs : NullMeasurableSet s μ)
    (h0 : μ s ≠ 0) : ∃ᶠ m in atTop, μ (s ∩ f^[m] ⁻¹' s) ≠ 0 := by
  set t : ℕ → Set α := fun n ↦ s ∩ f^[n] ⁻¹' s
  -- Assume that `μ (t n) ≠ 0`, where `t n = s ∩ f^[n] ⁻¹' s`, only for finitely many `n`.
  by_contra H
  -- Let `N` be the maximal `n` such that `μ (t n) ≠ 0`.
  obtain ⟨N, hN, hmax⟩ : ∃ N, μ (t N) ≠ 0 ∧ ∀ n > N, μ (t n) = 0 := by
    rw [Nat.frequently_atTop_iff_infinite, not_infinite] at H
    convert! exists_max_image _ (·) H ⟨0, by simpa⟩ using 4
    rw [gt_iff_lt, ← not_le, not_imp_comm, mem_ofPred]
  have htm {n : ℕ} : NullMeasurableSet (t n) μ :=
    hs.inter <| hs.preimage <| hf.toQuasiMeasurePreserving.iterate n
  -- Then all `t n`, `n > N`, are null sets, hence `T = t N \ ⋃ n > N, t n` has positive measure.
  set T := t N \ ⋃ n > N, t n with hT
  have hμT : μ T ≠ 0 := by
    rwa [hT, measure_sdiff_null]
    exact (measure_biUnion_null_iff {n | N < n}.to_countable).2 hmax
  have hTm : NullMeasurableSet T μ := htm.diff <| .biUnion {n | N < n}.to_countable fun _ _ ↦ htm
  -- Take `x ∈ T` and `m ≠ 0` such that `f^[m] x ∈ T`.
  rcases hf.exists_mem_iterate_mem hTm hμT with ⟨x, hxt, m, hm₀, hmt⟩
  -- Then `N + m > N`, `x ∈ s`, and `f^[N + m] x = f^[N] (f^[m] x) ∈ s`.
  -- This contradicts `x ∈ T ⊆ (⋃ n > N, t n)ᶜ`.
  refine hxt.2 <| mem_iUnion₂.2 ⟨N + m, ?_, hxt.1.1, ?_⟩
  · simpa [pos_iff_ne_zero]
  · simpa only [iterate_add] using! hmt.1.2

/-- If `f` is a conservative map and `s` is a measurable set of nonzero measure, then
for an arbitrarily large `m` a positive measure of points `x ∈ s` returns back to `s`
after `m` iterations of `f`. -/
/-
**MeasureTheory.Conservative.exists_gt_measure_inter_ne_zero** 是 Mathlib 中的一个定理，
位于命名空间 `MeasureTheory.Conservative`。
形式化陈述：exists_gt_measure_inter_ne_zero (hf : Conservative f μ) (hs : NullMeasurab
leSet s μ) (h0 : μ s != 0) (N : Nat) : exists m > N, μ (s inter f^[m] ⁻¹' s) != 
0
参数：hf : Conservative f μ；hs : NullMeasurableSet s μ；h0 : μ s != 0；N : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Frequently.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α}, 
(∃ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `Filter.Frequently.and_eventually`：∀ {α : Type u} {p q : α → Prop} {f : F
ilter α},   (∃ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, q x) → ∃ᶠ (x : α) in f, p
 x ∧ q x
· 使用定理 `MeasureTheory.Conservative.frequently_measure_inter_ne_zero`：frequently_
measure_inter_ne_zero (hf : Conservative f μ) (hs : NullMeasurableSet s μ) (h0 :
 μ s != 0) : existsᶠ m in atTop, μ (s inter f^[m]…
· 使用定理 `Filter.eventually_gt_atTop`：eventually_gt_atTop [Preorder α] [NoTopOrder
 α] (a : α) : forallᶠ x in atTop, a < x
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α

--- 原说明 ---
If `f` is a conservative map and `s` is a measurable set of nonzero measure, the
n
for an arbitrarily large `m` a positive measure of points `x ∈ s` returns back t
o `s`
after `m` iterations of `f`.
-/
theorem exists_gt_measure_inter_ne_zero (hf : Conservative f μ) (hs : NullMeasurableSet s μ)
    (h0 : μ s ≠ 0) (N : ℕ) : ∃ m > N, μ (s ∩ f^[m] ⁻¹' s) ≠ 0 :=
  let ⟨m, hm, hmN⟩ :=
    ((hf.frequently_measure_inter_ne_zero hs h0).and_eventually (eventually_gt_atTop N)).exists
  ⟨m, hmN, hm⟩

/-- Poincaré recurrence theorem: given a conservative map `f` and a measurable set `s`, the set
of points `x ∈ s` such that `x` does not return to `s` after `≥ n` iterations has measure zero. -/
/-
**MeasureTheory.Conservative.measure_mem_forall_ge_image_notMem_eq_zero** 是 Math
lib 中的一个定理，位于命名空间 `MeasureTheory.Conservative`。
形式化陈述：measure_mem_forall_ge_image_notMem_eq_zero (hf : Conservative f μ) (hs : N
ullMeasurableSet s μ) (n : Nat) : μ ({ x in s | forall m >= n, f^[m] x ∉ s }) = 
0
参数：hf : Conservative f μ；hs : NullMeasurableSet s μ；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.ofPred_forall`：ofPred_forall (p : ι -> β -> Prop) : { x | forall i, 
p i x } = ⋂ i, { x | p i x }
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `MeasureTheory.NullMeasurableSet.inter`：∀ {α : Type u_2} {m0 : Measurable
Space α} {μ : MeasureTheory.Measure α} {s t : Set α},   MeasureTheory.NullMeasur
ableSet s μ → MeasureTheory…
· 使用定理 `MeasureTheory.NullMeasurableSet.biInter`：∀ {α : Type u_2} {β : Type u_3}
 {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} {f : β → Set α} {s : Set
 β},   s.Countable → (∀ b ∈ s…
· 使用定理 `Set.to_countable`：to_countable (s : Set α) [Countable s] : s.Countable
· 使用定理 `Subtype.countable`：∀ {α : Sort u} [Countable α] {p : α → Prop}, Countabl
e { x // p x }
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `MeasureTheory.NullMeasurableSet.compl`：compl (h : NullMeasurableSet s μ)
 : NullMeasurableSet sᶜ μ
· 使用定理 `MeasureTheory.NullMeasurableSet.preimage`：∀ {α : Type u_1} {β : Type u_2
} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μa : MeasureTheory.Measure 
α}   {μb : MeasureTheory.Measu…
· 使用定理 `MeasureTheory.Measure.QuasiMeasurePreserving.iterate`：∀ {α : Type u_1} {
mα : MeasurableSpace α} {μa : MeasureTheory.Measure α} {f : α → α},   MeasureThe
ory.Measure.QuasiMeasurePreserving f μa μa…
· 使用定理 `MeasureTheory.Conservative.toQuasiMeasurePreserving`：∀ {α : Type u_1} [i
nst : MeasurableSpace α] {f : α → α} {μ : MeasureTheory.Measure α},   MeasureThe
ory.Conservative f μ → MeasureTheory.Meas…
· 使用定理 `MeasureTheory.Conservative.exists_gt_measure_inter_ne_zero`：exists_gt_me
asure_inter_ne_zero (hf : Conservative f μ) (hs : NullMeasurableSet s μ) (h0 : μ
 s != 0) (N : Nat) : exists m > N, μ (s inter f^…
· 使用定理 `MeasureTheory.nonempty_of_measure_ne_zero`：nonempty_of_measure_ne_zero (
h : μ s != 0) : s.Nonempty
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `GT.gt.lt`：∀ {α : Type u_2} [inst : LT α] {a b : α}, a > b → b < a

--- 原说明 ---
Poincaré recurrence theorem: given a conservative map `f` and a measurable set `
s`, the set
of points `x ∈ s` such that `x` does not return to `s` after `≥ n` iterations ha
s measure zero.
-/
theorem measure_mem_forall_ge_image_notMem_eq_zero (hf : Conservative f μ)
    (hs : NullMeasurableSet s μ) (n : ℕ) :
    μ ({ x ∈ s | ∀ m ≥ n, f^[m] x ∉ s }) = 0 := by
  by_contra H
  have : NullMeasurableSet (s ∩ { x | ∀ m ≥ n, f^[m] x ∉ s }) μ := by
    simp only [ofPred_forall, ← compl_ofPred]
    exact hs.inter <| .biInter (to_countable _) fun m _ ↦
      (hs.preimage <| hf.toQuasiMeasurePreserving.iterate m).compl
  rcases (hf.exists_gt_measure_inter_ne_zero this H) n with ⟨m, hmn, hm⟩
  rcases nonempty_of_measure_ne_zero hm with ⟨x, ⟨_, hxn⟩, hxm, -⟩
  exact hxn m hmn.lt.le hxm

/-- Poincaré recurrence theorem: given a conservative map `f` and a measurable set `s`,
almost every point `x ∈ s` returns back to `s` infinitely many times. -/
/-
**MeasureTheory.Conservative.ae_mem_imp_frequently_image_mem** 是 Mathlib 中的一个定理，
位于命名空间 `MeasureTheory.Conservative`。
形式化陈述：ae_mem_imp_frequently_image_mem (hf : Conservative f μ) (hs : NullMeasurab
leSet s μ) : forallᵐ x ∂μ, x in s -> existsᶠ n in atTop, f^[n] x in s
参数：hf : Conservative f μ；hs : NullMeasurableSet s μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.measure_eq_zero_iff_ae_notMem`：measure_eq_zero_iff_ae_notM
em {s : Set α} : μ s = 0 ↔ forallᵐ a ∂μ, a ∉ s
· 使用定理 `MeasureTheory.Conservative.measure_mem_forall_ge_image_notMem_eq_zero`：m
easure_mem_forall_ge_image_notMem_eq_zero (hf : Conservative f μ) (hs : NullMeas
urableSet s μ) (n : Nat) : μ ({ x in s | forall m >= n, f^[…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
Poincaré recurrence theorem: given a conservative map `f` and a measurable set `
s`,
almost every point `x ∈ s` returns back to `s` infinitely many times.
-/
theorem ae_mem_imp_frequently_image_mem (hf : Conservative f μ) (hs : NullMeasurableSet s μ) :
    ∀ᵐ x ∂μ, x ∈ s → ∃ᶠ n in atTop, f^[n] x ∈ s := by
  simp only [frequently_atTop, @forall_comm (_ ∈ s), ae_all_iff]
  intro n
  filter_upwards
    [measure_eq_zero_iff_ae_notMem.1 (hf.measure_mem_forall_ge_image_notMem_eq_zero hs n)]
  simp
/-
**MeasureTheory.Conservative.inter_frequently_image_mem_ae_eq** 是 Mathlib 中的一个定理
，位于命名空间 `MeasureTheory.Conservative`。
形式化陈述：inter_frequently_image_mem_ae_eq (hf : Conservative f μ) (hs : NullMeasura
bleSet s μ) : (s inter { x | existsᶠ n in atTop, f^[n] x in s } : Set α) =ᵐ[μ] s
参数：hf : Conservative f μ；hs : NullMeasurableSet s μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.inter_eventuallyEq_left`：inter_eventuallyEq_left {s t : Set α} {l
 : Filter α} : (s inter t : Set α) =ᶠ[l] s ↔ forallᶠ x in l, x in s -> x in t
· 使用定理 `MeasureTheory.Conservative.ae_mem_imp_frequently_image_mem`：ae_mem_imp_f
requently_image_mem (hf : Conservative f μ) (hs : NullMeasurableSet s μ) : foral
lᵐ x ∂μ, x in s -> existsᶠ n in atTop, f^[n] x i…
-/
theorem inter_frequently_image_mem_ae_eq (hf : Conservative f μ) (hs : NullMeasurableSet s μ) :
    (s ∩ { x | ∃ᶠ n in atTop, f^[n] x ∈ s } : Set α) =ᵐ[μ] s :=
  inter_eventuallyEq_left.2 <| hf.ae_mem_imp_frequently_image_mem hs
/-
**MeasureTheory.Conservative.measure_inter_frequently_image_mem_eq** 是 Mathlib 中
的一个定理，位于命名空间 `MeasureTheory.Conservative`。
形式化陈述：measure_inter_frequently_image_mem_eq (hf : Conservative f μ) (hs : NullMe
asurableSet s μ) : μ (s inter { x | existsᶠ n in atTop, f^[n] x in s }) = μ s
参数：hf : Conservative f μ；hs : NullMeasurableSet s μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.measure_congr`：measure_congr (H : s =ᵐ[μ] t) : μ s = μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Conservative.inter_frequently_image_mem_ae_eq`：inter_frequ
ently_image_mem_ae_eq (hf : Conservative f μ) (hs : NullMeasurableSet s μ) : (s 
inter { x | existsᶠ n in atTop, f^[n] x in s } : …
-/
theorem measure_inter_frequently_image_mem_eq (hf : Conservative f μ) (hs : NullMeasurableSet s μ) :
    μ (s ∩ { x | ∃ᶠ n in atTop, f^[n] x ∈ s }) = μ s :=
  measure_congr (hf.inter_frequently_image_mem_ae_eq hs)

/-- Poincaré recurrence theorem: if `f` is a conservative dynamical system and `s` is a measurable
set, then for `μ`-a.e. `x`, if the orbit of `x` visits `s` at least once, then it visits `s`
infinitely many times. -/
/-
**MeasureTheory.Conservative.ae_forall_image_mem_imp_frequently_image_mem** 是 Ma
thlib 中的一个定理，位于命名空间 `MeasureTheory.Conservative`。
形式化陈述：ae_forall_image_mem_imp_frequently_image_mem (hf : Conservative f μ) (hs :
 NullMeasurableSet s μ) : forallᵐ x ∂μ, forall k, f^[k] x in s -> existsᶠ n in a
tTop, f^[n] x in s
参数：hf : Conservative f μ；hs : NullMeasurableSet s μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.ae_all_iff`：ae_all_iff {ι : Sort*} [Countable ι] {p : α ->
 ι -> Prop} : (forallᵐ a ∂μ, forall i, p a i) ↔ forall i, forallᵐ a ∂μ, p a i
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `MeasureTheory.Conservative.ae_mem_imp_frequently_image_mem`：ae_mem_imp_f
requently_image_mem (hf : Conservative f μ) (hs : NullMeasurableSet s μ) : foral
lᵐ x ∂μ, x in s -> existsᶠ n in atTop, f^[n] x i…
· 使用定理 `MeasureTheory.NullMeasurableSet.preimage`：∀ {α : Type u_1} {β : Type u_2
} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μa : MeasureTheory.Measure 
α}   {μb : MeasureTheory.Measu…
· 使用定理 `MeasureTheory.Measure.QuasiMeasurePreserving.iterate`：∀ {α : Type u_1} {
mα : MeasurableSpace α} {μa : MeasureTheory.Measure α} {f : α → α},   MeasureThe
ory.Measure.QuasiMeasurePreserving f μa μa…
· 使用定理 `MeasureTheory.Conservative.toQuasiMeasurePreserving`：∀ {α : Type u_1} [i
nst : MeasurableSpace α] {f : α → α} {μ : MeasureTheory.Measure α},   MeasureThe
ory.Conservative f μ → MeasureTheory.Meas…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.map_add_atTop_eq_nat`：map_add_atTop_eq_nat (k : Nat) : map (fun a
 => a + k) atTop = atTop
· 使用定理 `Filter.frequently_map`：frequently_map {P : β -> Prop} : (existsᶠ b in ma
p m f, P b) ↔ existsᶠ a in f, P (m a)
· 使用定理 `Filter.Frequently.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∃ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∃ᶠ (x : α) in f, q x
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Function.iterate_add_apply`：iterate_add_apply (m n : Nat) (x : α) : f^[m
 + n] x = f^[m] (f^[n] x)

--- 原说明 ---
Poincaré recurrence theorem: if `f` is a conservative dynamical system and `s` i
s a measurable
set, then for `μ`-a.e. `x`, if the orbit of `x` visits `s` at least once, then i
t visits `s`
infinitely many times.
-/
theorem ae_forall_image_mem_imp_frequently_image_mem (hf : Conservative f μ)
    (hs : NullMeasurableSet s μ) : ∀ᵐ x ∂μ, ∀ k, f^[k] x ∈ s → ∃ᶠ n in atTop, f^[n] x ∈ s := by
  refine ae_all_iff.2 fun k => ?_
  refine (hf.ae_mem_imp_frequently_image_mem
    (hs.preimage <| hf.toQuasiMeasurePreserving.iterate k)).mono fun x hx hk => ?_
  rw [← map_add_atTop_eq_nat k, frequently_map]
  refine (hx hk).mono fun n hn => ?_
  rwa [add_comm, iterate_add_apply]

/-- If `f` is a conservative self-map and `s` is a measurable set of positive measure, then
`ae μ`-frequently we have `x ∈ s` and `s` returns to `s` under infinitely many iterations of `f`. -/
/-
**MeasureTheory.Conservative.frequently_ae_mem_and_frequently_image_mem** 是 Math
lib 中的一个定理，位于命名空间 `MeasureTheory.Conservative`。
形式化陈述：frequently_ae_mem_and_frequently_image_mem (hf : Conservative f μ) (hs : N
ullMeasurableSet s μ) (h0 : μ s != 0) : existsᵐ x ∂μ, x in s ∧ existsᶠ n in atTo
p, f^[n] x in s
参数：hf : Conservative f μ；hs : NullMeasurableSet s μ；h0 : μ s != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Frequently.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∃ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∃ᶠ (x : α) in f, q x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.Frequently.and_eventually`：∀ {α : Type u} {p q : α → Prop} {f : F
ilter α},   (∃ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, q x) → ∃ᶠ (x : α) in f, p
 x ∧ q x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.frequently_ae_mem_iff`：frequently_ae_mem_iff {s : Set α} :
 (existsᵐ a ∂μ, a in s) ↔ μ s != 0
· 使用定理 `MeasureTheory.Conservative.ae_mem_imp_frequently_image_mem`：ae_mem_imp_f
requently_image_mem (hf : Conservative f μ) (hs : NullMeasurableSet s μ) : foral
lᵐ x ∂μ, x in s -> existsᶠ n in atTop, f^[n] x i…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
If `f` is a conservative self-map and `s` is a measurable set of positive measur
e, then
`ae μ`-frequently we have `x ∈ s` and `s` returns to `s` under infinitely many i
terations of `f`.
-/
theorem frequently_ae_mem_and_frequently_image_mem (hf : Conservative f μ)
    (hs : NullMeasurableSet s μ) (h0 : μ s ≠ 0) : ∃ᵐ x ∂μ, x ∈ s ∧ ∃ᶠ n in atTop, f^[n] x ∈ s :=
  ((frequently_ae_mem_iff.2 h0).and_eventually (hf.ae_mem_imp_frequently_image_mem hs)).mono
    fun _ hx => ⟨hx.1, hx.2 hx.1⟩

/-- Poincaré recurrence theorem. Let `f : α → α` be a conservative dynamical system on a topological
space with second countable topology and measurable open sets. Then almost every point `x : α`
is recurrent: it visits every neighborhood `s ∈ 𝓝 x` infinitely many times. -/
/-
**MeasureTheory.Conservative.ae_frequently_mem_of_mem_nhds** 是 Mathlib 中的一个定理，位于
命名空间 `MeasureTheory.Conservative`。
形式化陈述：ae_frequently_mem_of_mem_nhds [TopologicalSpace α] [SecondCountableTopolog
y α] [OpensMeasurableSpace α] {f : α -> α} {μ : Measure α} (h : Conservative f μ
) : forallᵐ x ∂μ, forall s in 𝓝 x, existsᶠ n in atTop, f^[n] x in s
参数：h : Conservative f μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Conservative.ae_mem_imp_frequently_image_mem`：ae_mem_imp_f
requently_image_mem (hf : Conservative f μ) (hs : NullMeasurableSet s μ) : foral
lᵐ x ∂μ, x in s -> existsᶠ n in atTop, f^[n] x i…
· 使用定理 `IsOpen.nullMeasurableSet`：IsOpen.nullMeasurableSet {μ} (h : IsOpen s) : 
NullMeasurableSet s μ
· 使用定理 `TopologicalSpace.isOpen_of_mem_countableBasis`：isOpen_of_mem_countableBa
sis [SecondCountableTopology α] {s : Set α} (hs : s in countableBasis α) : IsOpe
n s
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.ae_ball_iff`：ae_ball_iff {ι : Type*} {S : Set ι} (hS : S.C
ountable) {p : α -> forall i in S, Prop} : (forallᵐ x ∂μ, forall i (hi : i in S)
, p x i hi) ↔ f…
· 使用定理 `TopologicalSpace.countable_countableBasis`：countable_countableBasis [Sec
ondCountableTopology α] : (countableBasis α).Countable
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `TopologicalSpace.IsTopologicalBasis.mem_nhds_iff`：∀ {α : Type u} [t : To
pologicalSpace α] {a : α} {s : Set α} {b : Set (Set α)},   TopologicalSpace.IsTo
pologicalBasis b → (s ∈ nhds a ↔ ∃ t ∈…
· 使用定理 `TopologicalSpace.isBasis_countableBasis`：isBasis_countableBasis [SecondC
ountableTopology α] : IsTopologicalBasis (countableBasis α)
· 使用定理 `Filter.Frequently.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∃ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∃ᶠ (x : α) in f, q x

--- 原说明 ---
Poincaré recurrence theorem. Let `f : α → α` be a conservative dynamical system 
on a topological
space with second countable topology and measurable open sets. Then almost every
 point `x : α`
is recurrent: it visits every neighborhood `s ∈ 𝓝 x` infinitely many times.
-/
theorem ae_frequently_mem_of_mem_nhds [TopologicalSpace α] [SecondCountableTopology α]
    [OpensMeasurableSpace α] {f : α → α} {μ : Measure α} (h : Conservative f μ) :
    ∀ᵐ x ∂μ, ∀ s ∈ 𝓝 x, ∃ᶠ n in atTop, f^[n] x ∈ s := by
  have : ∀ s ∈ countableBasis α, ∀ᵐ x ∂μ, x ∈ s → ∃ᶠ n in atTop, f^[n] x ∈ s := fun s hs =>
    h.ae_mem_imp_frequently_image_mem (isOpen_of_mem_countableBasis hs).nullMeasurableSet
  refine ((ae_ball_iff <| countable_countableBasis α).2 this).mono fun x hx s hs => ?_
  rcases (isBasis_countableBasis α).mem_nhds_iff.1 hs with ⟨o, hoS, hxo, hos⟩
  exact (hx o hoS hxo).mono fun n hn => hos hn

/-- Iteration of a conservative system is a conservative system. -/
/-
**MeasureTheory.Conservative.iterate** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Co
nservative`。
形式化陈述：∀ {α : Type u_1} [inst : MeasurableSpace α] {f : α → α} {μ : MeasureTheory
.Measure α},   MeasureTheory.Conservative f μ → ∀ (n : ℕ), MeasureTheory.Conserv
ative f^[n] μ
参数：n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Conservative.id`：∀ {α : Type u_1} [inst : MeasurableSpace 
α] (μ : MeasureTheory.Measure α), MeasureTheory.Conservative id μ
· 使用定理 `MeasureTheory.Measure.QuasiMeasurePreserving.iterate`：∀ {α : Type u_1} {
mα : MeasurableSpace α} {μa : MeasureTheory.Measure α} {f : α → α},   MeasureThe
ory.Measure.QuasiMeasurePreserving f μa μa…
· 使用定理 `MeasureTheory.Conservative.toQuasiMeasurePreserving`：∀ {α : Type u_1} [i
nst : MeasurableSpace α] {f : α → α} {μ : MeasureTheory.Measure α},   MeasureThe
ory.Conservative f μ → MeasureTheory.Meas…
· 使用定理 `Filter.Frequently.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α}, 
(∃ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Conservative.frequently_ae_mem_and_frequently_image_mem`：f
requently_ae_mem_and_frequently_image_mem (hf : Conservative f μ) (hs : NullMeas
urableSet s μ) (h0 : μ s != 0) : existsᵐ x ∂μ, x in s ∧ exi…
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
· 使用定理 `Nat.exists_lt_modEq_of_infinite`：exists_lt_modEq_of_infinite {s : Set Na
t} (hs : s.Infinite) {k : Nat} (hk : 0 < k) : exists m in s, exists n in s, m < 
n ∧ m ≡ n [MOD k]
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.frequently_atTop_iff_infinite`：Nat.frequently_atTop_iff_infinite {p 
: Nat -> Prop} : (existsᶠ n in atTop, p n) ↔ Set.Infinite { n | p n }
· 使用定理 `Nat.succ_pos`：∀ (n : ℕ), 0 < n.succ
· 使用定理 `Nat.mul_div_cancel'`：∀ {n m : ℕ}, n ∣ m → n * (m / n) = m
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.modEq_iff_dvd'`：modEq_iff_dvd' (h : a <= b) : a ≡ b [MOD n] ↔ n ∣ b 
- a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `tsub_eq_zero_iff_le`：tsub_eq_zero_iff_le : a - b = 0 ↔ a <= b
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.iterate_mul`：∀ {α : Type u} (f : α → α) (m n : ℕ), f^[m * n] = 
f^[m] ^[n]
· 使用定理 `Function.iterate_add_apply`：iterate_add_apply (m n : Nat) (x : α) : f^[m
 + n] x = f^[m] (f^[n] x)
· 使用定理 `tsub_add_cancel_of_le`：tsub_add_cancel_of_le (h : a <= b) : b - a + a = 
b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α

--- 原说明 ---
Iteration of a conservative system is a conservative system.
-/
protected theorem iterate (hf : Conservative f μ) (n : ℕ) : Conservative f^[n] μ := by
  -- Discharge the trivial case `n = 0`
  rcases n with - | n
  · exact Conservative.id μ
  refine ⟨hf.1.iterate _, fun s hs hs0 => ?_⟩
  rcases (hf.frequently_ae_mem_and_frequently_image_mem hs.nullMeasurableSet hs0).exists
    with ⟨x, _, hx⟩
  /- We take a point `x ∈ s` such that `f^[k] x ∈ s` for infinitely many values of `k`,
    then we choose two of these values `k < l` such that `k ≡ l [MOD (n + 1)]`.
    Then `f^[k] x ∈ s` and `f^[n + 1]^[(l - k) / (n + 1)] (f^[k] x) = f^[l] x ∈ s`. -/
  rw [Nat.frequently_atTop_iff_infinite] at hx
  rcases Nat.exists_lt_modEq_of_infinite hx n.succ_pos with ⟨k, hk, l, hl, hkl, hn⟩
  set m := (l - k) / (n + 1)
  have : (n + 1) * m = l - k := by
    apply Nat.mul_div_cancel'
    exact (Nat.modEq_iff_dvd' hkl.le).1 hn
  refine ⟨f^[k] x, hk, m, ?_, ?_⟩
  · intro hm
    rw [hm, mul_zero, eq_comm, tsub_eq_zero_iff_le] at this
    exact this.not_gt hkl
  · rwa [← iterate_mul, this, ← iterate_add_apply, tsub_add_cancel_of_le]
    exact hkl.le

end Conservative

end MeasureTheory

