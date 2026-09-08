/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis, Johannes Hölzl, Mario Carneiro, Sébastien Gouëzel
-/
module

public import Mathlib.Data.ENNReal.Inv
public import Mathlib.Topology.UniformSpace.Basic
public import Mathlib.Topology.UniformSpace.OfFun

/-!
# Extended metric spaces

This file is devoted to the definition and study of `EMetricSpace`s, i.e., metric
spaces in which the distance is allowed to take the value ∞. This extended distance is
called `edist`, and takes values in `ℝ≥0∞`.

Many definitions and theorems expected on emetric spaces are already introduced on uniform spaces
and topological spaces. For example: open and closed sets, compactness, completeness, continuity and
uniform continuity.

The class `EMetricSpace` therefore extends `UniformSpace` (and `TopologicalSpace`).

Since a lot of elementary properties don't require `eq_of_edist_eq_zero` we start setting up the
theory of `PseudoEMetricSpace`, where we don't require `edist x y = 0 → x = y` and we specialize
to `EMetricSpace` at the end.
-/

@[expose] public section


assert_not_exists Nat.instLocallyFiniteOrder IsUniformEmbedding.prod TendstoUniformlyOnFilter

open Filter Set Topology Set.Notation

universe u v w

variable {α : Type u} {β : Type v} {X : Type*}

/-- Characterizing uniformities associated to a (generalized) distance function `D`
in terms of the elements of the uniformity. -/
/-
**uniformity_dist_of_mem_uniformity** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniformity_dist_of_mem_uniformity [LT β] {U : Filter (α × α)} (z : β) (D :
 α -> α -> β) (H : forall s, s in U ↔ exists ε > z, forall {a b : α}, D a b < ε 
-> (a, b) in s) : U = ⨅ ε > z, 𝓟 { p : α × α | D p.1 p.2 < ε }
参数：α × α；z : β；D : α -> α -> β；H : forall s, s in U ↔ exists ε > z, forall {a b 
: α}, D a b < ε -> (a, b) in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.eq_biInf`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α}
 {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → l = ⨅ i, ⨅ (_ : p i), Filter
.principal (s …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Characterizing uniformities associated to a (generalized) distance function `D`
in terms of the elements of the uniformity.
-/
theorem uniformity_dist_of_mem_uniformity [LT β] {U : Filter (α × α)} (z : β)
    (D : α → α → β) (H : ∀ s, s ∈ U ↔ ∃ ε > z, ∀ {a b : α}, D a b < ε → (a, b) ∈ s) :
    U = ⨅ ε > z, 𝓟 { p : α × α | D p.1 p.2 < ε } :=
  HasBasis.eq_biInf ⟨fun s => by simp only [H, subset_def, Prod.forall, mem_ofPred]⟩

open scoped Uniformity Topology Filter NNReal ENNReal Pointwise

/-- `EDist α` means that `α` is equipped with an extended distance. -/
@[ext]
/-
**EDist** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u_2 → Type u_2
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`EDist α` means that `α` is equipped with an extended distance.
-/
class EDist (α : Type*) where
  /-- Extended distance between two points -/
  edist : α → α → ℝ≥0∞

export EDist (edist)

section

variable {x y z : α} {ε : ℝ≥0∞} [EDist α]

/-- `EMetric.ball x ε` is the set of all points `y` with `edist y x < ε` -/
/-
**Metric.eball** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Metric.eball (x : α) (ε : Real>=0∞) : Set α
参数：x : α；ε : Real>=0∞。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`EMetric.ball x ε` is the set of all points `y` with `edist y x < ε`
-/
def Metric.eball (x : α) (ε : ℝ≥0∞) : Set α :=
  { y | edist y x < ε }
/-
**Metric.mem_eball** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：∀ {α : Type u} [inst : EDist α] {x y : α} {ε : ENNReal}, y ∈ Metric.eball 
x ε ↔ edist y x < ε
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] theorem Metric.mem_eball {x y : α} {ε : ℝ≥0∞} : y ∈ eball x ε ↔ edist y x < ε := Iff.rfl

end

/-- Creating a uniform space from an extended distance. -/
@[reducible]
/-
**uniformSpaceOfEDist** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：uniformSpaceOfEDist (edist : α -> α -> Real>=0∞) (edist_self : forall x : 
α, edist x x = 0) (edist_comm : forall x y : α, edist x y = edist y x) (edist_tr
iangle : forall x y z : α, edist x z <= edist x y + edist y z) : UniformSpace α
参数：edist : α -> α -> Real>=0∞；edist_self : forall x : α, edist x x = 0；edist_com
m : forall x y : α, edist x y = edist y x；edist_triangle : forall x y z : α, edi
st x z <= edist x y + edist y z。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Creating a uniform space from an extended distance.
-/
noncomputable def uniformSpaceOfEDist (edist : α → α → ℝ≥0∞) (edist_self : ∀ x : α, edist x x = 0)
    (edist_comm : ∀ x y : α, edist x y = edist y x)
    (edist_triangle : ∀ x y z : α, edist x z ≤ edist x y + edist y z) : UniformSpace α :=
  .ofFun edist edist_self edist_comm edist_triangle fun ε ε0 =>
    ⟨ε / 2, ENNReal.half_pos ε0.ne', fun _ h₁ _ h₂ =>
      (ENNReal.add_lt_add h₁ h₂).trans_eq (ENNReal.add_halves _)⟩

/-- Creating a uniform space from an extended distance. We assume that
there is a preexisting topology, for which the neighborhoods can be expressed using the distance,
and we make sure that the uniform space structure we construct has a topology which is defeq
to the original one. -/
/-
**uniformSpaceOfEDistOfHasBasis** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：{α : Type u} →   [inst : TopologicalSpace α] →     (edist : α → α → ENNRea
l) →       (∀ (x : α), edist x x = 0) →         (∀ (x y : α), edist x y = edist 
y x) →           (∀ (x y z : α), edist x z ≤ edist x y + edist y z) →           
  (∀ (x : α), (nhds x).HasBasis (fun c => 0 < c) fun c => {y | edist x y < c}) →
 UniformSpace α
参数：edist : α → α → ENNReal；∀ (x : α), edist x x = 0；∀ (x y : α), edist x y = edi
st y x；∀ (x y z : α), edist x z ≤ edist x y + edist y z；∀ (x : α), (nhds x).HasB
asis (fun c => 0 < c) fun c => {y | edist x y < c}。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Creating a uniform space from an extended distance. We assume that
there is a preexisting topology, for which the neighborhoods can be expressed us
ing the distance,
and we make sure that the uniform space structure we construct has a topology wh
ich is defeq
to the original one.
-/
@[reducible] noncomputable def uniformSpaceOfEDistOfHasBasis [TopologicalSpace α]
    (edist : α → α → ℝ≥0∞)
    (edist_self : ∀ x : α, edist x x = 0)
    (edist_comm : ∀ x y : α, edist x y = edist y x)
    (edist_triangle : ∀ x y z : α, edist x z ≤ edist x y + edist y z)
    (basis : ∀ x, (𝓝 x).HasBasis (fun c ↦ 0 < c) (fun c ↦ {y | edist x y < c})) :
    UniformSpace α :=
  .ofFunOfHasBasis edist edist_self edist_comm edist_triangle (fun ε ε0 =>
    ⟨ε / 2, ENNReal.half_pos ε0.ne', fun _ h₁ _ h₂ =>
      (ENNReal.add_lt_add h₁ h₂).trans_eq (ENNReal.add_halves _)⟩) basis

/-- A pseudo extended metric space is a type endowed with a `ℝ≥0∞`-valued distance `edist`
satisfying reflexivity `edist x x = 0`, commutativity `edist x y = edist y x`, and the triangle
inequality `edist x z ≤ edist x y + edist y z`.

Note that we do not require `edist x y = 0 → x = y`. See extended metric spaces (`EMetricSpace`) for
the similar class with that stronger assumption.

Any pseudo extended metric space is a topological space and a uniform space (see `TopologicalSpace`,
`UniformSpace`), where the topology and uniformity come from the metric.
Note that a T1 pseudo extended metric space is just an extended metric space.

We make the uniformity/topology part of the data instead of deriving it from the metric. This e.g.
ensures that we do not get a diamond when doing
`[PseudoEMetricSpace α] [PseudoEMetricSpace β] : TopologicalSpace (α × β)`:
The product metric and product topology agree, but not definitionally so.
See Note [forgetful inheritance]. -/
/-
**PseudoEMetricSpace** 是 Mathlib 中的一个类，位于命名空间 ``。
形式化陈述：PseudoEMetricSpace (α : Type u) : Type u extends EDist α where edist_self 
: forall x : α, edist x x = 0 edist_comm : forall x y : α, edist x y = edist y x
 edist_triangle : forall x y z : α, edist x z <= edist x y + edist y z toUniform
Space : UniformSpace α
参数：α : Type u。
继承自：EDist α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A pseudo extended metric space is a type endowed with a `ℝ≥0∞`-valued distance `
edist`
satisfying reflexivity `edist x x = 0`, commutativity `edist x y = edist y x`, a
nd the triangle
inequality `edist x z ≤ edist x y + edist y z`.

Note that we do not require `edist x y = 0 → x = y`. See extended metric spaces 
(`EMetricSpace`) for
the similar class with that stronger assumption.

Any pseudo extended metric space is a topological space and a uniform space (see
 `TopologicalSpace`,
`UniformSpace`), where the topology and uniformity come from the metric.
Note that a T1 pseudo extended metric space is just an extended metric space.

We make the uniformity/topology part of the data instead of deriving it from the
 metric. This e.g.
ensures that we do not get a diamond when doing
`[PseudoEMetricSpace α] [PseudoEMetricSpace β] : TopologicalSpace (α × β)`:
The product metric and product topology agree, but not definitionally so.
See Note [forgetful inheritance].
-/
class PseudoEMetricSpace (α : Type u) : Type u extends EDist α where
  edist_self : ∀ x : α, edist x x = 0
  edist_comm : ∀ x y : α, edist x y = edist y x
  edist_triangle : ∀ x y z : α, edist x z ≤ edist x y + edist y z
  toUniformSpace : UniformSpace α := uniformSpaceOfEDist edist edist_self edist_comm edist_triangle
  uniformity_edist : 𝓤 α = ⨅ ε > 0, 𝓟 { p : α × α | edist p.1 p.2 < ε } := by rfl

attribute [instance_reducible, instance] PseudoEMetricSpace.toUniformSpace

/- Pseudoemetric spaces are less common than metric spaces. Therefore, we work in a dedicated
namespace, while notions associated to metric spaces are mostly in the root namespace. -/

/-- Two pseudo emetric space structures with the same edistance function coincide. -/
@[ext]
/-
**PseudoEMetricSpace.ext** 是 Mathlib 中的一个定理，位于命名空间 `PseudoEMetricSpace`。
形式化陈述：∀ {α : Type u_2} {m m' : PseudoEMetricSpace α}, m.toEDist = m'.toEDist → m
 = m'
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformSpace.ext`：∀ {α : Type ua} {u₁ u₂ : UniformSpace α}, uniformity α
 = uniformity α → u₁ = u₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
Two pseudo emetric space structures with the same edistance function coincide.
-/
protected theorem PseudoEMetricSpace.ext {α : Type*} {m m' : PseudoEMetricSpace α}
    (h : m.toEDist = m'.toEDist) : m = m' := by
  obtain ⟨_, _, _, U, hU⟩ := m; rename EDist α => ed
  obtain ⟨_, _, _, U', hU'⟩ := m'; rename EDist α => ed'
  congr 1
  exact UniformSpace.ext (((show ed = ed' from h) ▸ hU).trans hU'.symm)

variable [PseudoEMetricSpace α]

export PseudoEMetricSpace (edist_self edist_comm edist_triangle)

attribute [simp] edist_self

/-- Triangle inequality for the extended distance -/
/-
**edist_triangle_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：edist_triangle_left (x y z : α) : edist x y <= edist z x + edist z y
参数：x y z : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PseudoEMetricSpace.edist_comm`：∀ {α : Type u} [self : PseudoEMetricSpace
 α] (x y : α), edist x y = edist y x
· 使用定理 `PseudoEMetricSpace.edist_triangle`：∀ {α : Type u} [self : PseudoEMetricS
pace α] (x y z : α), edist x z ≤ edist x y + edist y z

--- 原说明 ---
Triangle inequality for the extended distance
-/
theorem edist_triangle_left (x y z : α) : edist x y ≤ edist z x + edist z y := by
  rw [edist_comm z]; apply edist_triangle
/-
**edist_triangle_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：edist_triangle_right (x y z : α) : edist x y <= edist x z + edist y z
参数：x y z : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PseudoEMetricSpace.edist_comm`：∀ {α : Type u} [self : PseudoEMetricSpace
 α] (x y : α), edist x y = edist y x
· 使用定理 `PseudoEMetricSpace.edist_triangle`：∀ {α : Type u} [self : PseudoEMetricS
pace α] (x y z : α), edist x z ≤ edist x y + edist y z
-/
theorem edist_triangle_right (x y z : α) : edist x y ≤ edist x z + edist y z := by
  rw [edist_comm y]; apply edist_triangle
/-
**edist_congr_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：edist_congr_right {x y z : α} (h : edist x y = 0) : edist x z = edist y z
参数：h : edist x y = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `PseudoEMetricSpace.edist_triangle`：∀ {α : Type u} [self : PseudoEMetricS
pace α] (x y z : α), edist x z ≤ edist x y + edist y z
· 使用定理 `PseudoEMetricSpace.edist_comm`：∀ {α : Type u} [self : PseudoEMetricSpace
 α] (x y : α), edist x y = edist y x
-/
theorem edist_congr_right {x y z : α} (h : edist x y = 0) : edist x z = edist y z := by
  apply le_antisymm
  · rw [← zero_add (edist y z), ← h]
    apply edist_triangle
  · rw [edist_comm] at h
    rw [← zero_add (edist x z), ← h]
    apply edist_triangle
/-
**edist_congr_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：edist_congr_left {x y z : α} (h : edist x y = 0) : edist z x = edist z y
参数：h : edist x y = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PseudoEMetricSpace.edist_comm`：∀ {α : Type u} [self : PseudoEMetricSpace
 α] (x y : α), edist x y = edist y x
· 使用定理 `edist_congr_right`：edist_congr_right {x y z : α} (h : edist x y = 0) : e
dist x z = edist y z
-/
theorem edist_congr_left {x y z : α} (h : edist x y = 0) : edist z x = edist z y := by
  rw [edist_comm z x, edist_comm z y]
  apply edist_congr_right h
/-
**edist_congr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：edist_congr {w x y z : α} (hl : edist w x = 0) (hr : edist y z = 0) : edis
t w y = edist x z
参数：hl : edist w x = 0；hr : edist y z = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `edist_congr_right`：edist_congr_right {x y z : α} (h : edist x y = 0) : e
dist x z = edist y z
· 使用定理 `edist_congr_left`：edist_congr_left {x y z : α} (h : edist x y = 0) : edi
st z x = edist z y
-/
theorem edist_congr {w x y z : α} (hl : edist w x = 0) (hr : edist y z = 0) :
    edist w y = edist x z :=
  (edist_congr_right hl).trans (edist_congr_left hr)
/-
**edist_triangle4** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：edist_triangle4 (x y z t : α) : edist x t <= edist x y + edist y z + edist
 z t
参数：x y z t : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `PseudoEMetricSpace.edist_triangle`：∀ {α : Type u} [self : PseudoEMetricS
pace α] (x y z : α), edist x z ≤ edist x y + edist y z
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
-/
theorem edist_triangle4 (x y z t : α) : edist x t ≤ edist x y + edist y z + edist z t := by
  grw [edist_triangle _ z, edist_triangle]

/-- Reformulation of the uniform structure in terms of the extended distance -/
/-
**uniformity_pseudoedist** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniformity_pseudoedist : 𝓤 α = ⨅ ε > 0, 𝓟 { p : α × α | edist p.1 p.2 < ε 
}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PseudoEMetricSpace.uniformity_edist`：∀ {α : Type u} [self : PseudoEMetri
cSpace α],   uniformity α = ⨅ ε, ⨅ (_ : ε > 0), Filter.principal {p | edist p.1 
p.2 < ε}

--- 原说明 ---
Reformulation of the uniform structure in terms of the extended distance
-/
theorem uniformity_pseudoedist : 𝓤 α = ⨅ ε > 0, 𝓟 { p : α × α | edist p.1 p.2 < ε } :=
  PseudoEMetricSpace.uniformity_edist
/-
**uniformSpace_edist** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniformSpace_edist : ‹PseudoEMetricSpace α›.toUniformSpace = uniformSpaceO
fEDist edist edist_self edist_comm edist_triangle
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformSpace.ext`：∀ {α : Type ua} {u₁ u₂ : UniformSpace α}, uniformity α
 = uniformity α → u₁ = u₂
· 使用定理 `PseudoEMetricSpace.edist_self`：∀ {α : Type u} [self : PseudoEMetricSpace
 α] (x : α), edist x x = 0
· 使用定理 `PseudoEMetricSpace.edist_comm`：∀ {α : Type u} [self : PseudoEMetricSpace
 α] (x y : α), edist x y = edist y x
· 使用定理 `PseudoEMetricSpace.edist_triangle`：∀ {α : Type u} [self : PseudoEMetricS
pace α] (x y z : α), edist x z ≤ edist x y + edist y z
· 使用定理 `uniformity_pseudoedist`：uniformity_pseudoedist : 𝓤 α = ⨅ ε > 0, 𝓟 { p : 
α × α | edist p.1 p.2 < ε }
-/
theorem uniformSpace_edist :
    ‹PseudoEMetricSpace α›.toUniformSpace =
      uniformSpaceOfEDist edist edist_self edist_comm edist_triangle :=
  UniformSpace.ext uniformity_pseudoedist
/-
**uniformity_basis_edist** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniformity_basis_edist : (𝓤 α).HasBasis (fun ε : Real>=0∞ => 0 < ε) fun ε 
=> { p : α × α | edist p.1 p.2 < ε }
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PseudoEMetricSpace.edist_self`：∀ {α : Type u} [self : PseudoEMetricSpace
 α] (x : α), edist x x = 0
· 使用定理 `PseudoEMetricSpace.edist_comm`：∀ {α : Type u} [self : PseudoEMetricSpace
 α] (x y : α), edist x y = edist y x
· 使用定理 `PseudoEMetricSpace.edist_triangle`：∀ {α : Type u} [self : PseudoEMetricS
pace α] (x y z : α), edist x z ≤ edist x y + edist y z
· 使用定理 `UniformSpace.hasBasis_ofFun`：hasBasis_ofFun [AddCommMonoid M] [LinearOrd
er M] (h₀ : exists x : M, 0 < x) (d : X -> X -> M) (refl : forall x, d x x = 0) 
(symm : forall x …
· 使用定理 `one_pos`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 : Par
tialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `ENNReal.instIsOrderedRing`：IsOrderedRing ENNReal
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `uniformSpace_edist`：uniformSpace_edist : ‹PseudoEMetricSpace α›.toUnifor
mSpace = uniformSpaceOfEDist edist edist_self edist_comm edist_triangle
-/
theorem uniformity_basis_edist :
    (𝓤 α).HasBasis (fun ε : ℝ≥0∞ => 0 < ε) fun ε => { p : α × α | edist p.1 p.2 < ε } :=
  (@uniformSpace_edist α _).symm ▸ UniformSpace.hasBasis_ofFun ⟨1, one_pos⟩ _ _ _ _ _

/-- Characterization of the elements of the uniformity in terms of the extended distance -/
/-
**mem_uniformity_edist** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_uniformity_edist {s : Set (α × α)} : s in 𝓤 α ↔ exists ε > 0, forall {
a b : α}, edist a b < ε -> (a, b) in s
参数：α × α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.mem_uniformity_iff`：Filter.HasBasis.mem_uniformity_iff {
p : β -> Prop} {s : β -> SetRel α α} (h : (𝓤 α).HasBasis p s) {t : SetRel α α} :
 t in 𝓤 α ↔ exists i, p …
· 使用定理 `uniformity_basis_edist`：uniformity_basis_edist : (𝓤 α).HasBasis (fun ε :
 Real>=0∞ => 0 < ε) fun ε => { p : α × α | edist p.1 p.2 < ε }

--- 原说明 ---
Characterization of the elements of the uniformity in terms of the extended dist
ance
-/
theorem mem_uniformity_edist {s : Set (α × α)} :
    s ∈ 𝓤 α ↔ ∃ ε > 0, ∀ {a b : α}, edist a b < ε → (a, b) ∈ s :=
  uniformity_basis_edist.mem_uniformity_iff

/-- Make a `PseudoEMetricSpace` from a metric. Warning: the uniformity and topology included herein
are the ones generated by the metric. If the type has a pre-existing topology or uniformity,
`PseudoEMetricSpace.ofEDistOfTopology` should be used instead. -/
/-
**PseudoEMetricSpace.ofEDist** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：PseudoEMetricSpace.ofEDist {α : Type u} (edist : α -> α -> Real>=0∞) (edis
t_self : forall x : α, edist x x = 0) (edist_comm : forall x y : α, edist x y = 
edist y x) (edist_triangle : forall x y z : α, edist x z <= edist x y + edist y 
z) : PseudoEMetricSpace α where edist
参数：edist : α -> α -> Real>=0∞；edist_self : forall x : α, edist x x = 0；edist_com
m : forall x y : α, edist x y = edist y x；edist_triangle : forall x y z : α, edi
st x z <= edist x y + edist y z。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Make a `PseudoEMetricSpace` from a metric. Warning: the uniformity and topology 
included herein
are the ones generated by the metric. If the type has a pre-existing topology or
 uniformity,
`PseudoEMetricSpace.ofEDistOfTopology` should be used instead.
-/
noncomputable abbrev PseudoEMetricSpace.ofEDist
    {α : Type u} (edist : α → α → ℝ≥0∞) (edist_self : ∀ x : α, edist x x = 0)
    (edist_comm : ∀ x y : α, edist x y = edist y x) (edist_triangle : ∀ x y z :
    α, edist x z ≤ edist x y + edist y z) : PseudoEMetricSpace α where
  edist := edist
  edist_self := edist_self
  edist_comm := edist_comm
  edist_triangle := edist_triangle
  toUniformSpace := uniformSpaceOfEDist edist edist_self edist_comm edist_triangle
  uniformity_edist := by rfl
/-
**EMetric.toUniformSpace_ofEDist** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：EMetric.toUniformSpace_ofEDist {α : Type u} [EDist α] (edist_self : forall
 x : α, edist x x = 0) (edist_comm : forall x y : α, edist x y = edist y x) (edi
st_triangle : forall x y z : α, edist x z <= edist x y + edist y z) : (PseudoEMe
tricSpace.ofEDist edist edist_self edist_comm edist_triangle).toUniformSpace = (
uniformSpaceOfEDist edist edist_self edist_comm edist_triangle)
参数：edist_self : forall x : α, edist x x = 0；edist_comm : forall x y : α, edist x
 y = edist y x；edist_triangle : forall x y z : α, edist x z <= edist x y + edist
 y z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem EMetric.toUniformSpace_ofEDist {α : Type u} [EDist α] (edist_self : ∀ x : α, edist x x = 0)
    (edist_comm : ∀ x y : α, edist x y = edist y x)
    (edist_triangle : ∀ x y z : α, edist x z ≤ edist x y + edist y z) :
    (PseudoEMetricSpace.ofEDist edist edist_self edist_comm edist_triangle).toUniformSpace =
      (uniformSpaceOfEDist edist edist_self edist_comm edist_triangle) := by rfl

/-- Given `f : β → ℝ≥0∞`, if `f` sends `{i | p i}` to a set of positive numbers
accumulating to zero, then `f i`-neighborhoods of the diagonal form a basis of `𝓤 α`.

For specific bases see `uniformity_basis_edist`, `uniformity_basis_edist'`,
`uniformity_basis_edist_nnreal`, and `uniformity_basis_edist_inv_nat`. -/
/-
**EMetric.mk_uniformity_basis** 是 Mathlib 中的一个定理，位于命名空间 `EMetric`。
形式化陈述：∀ {α : Type u} [inst : PseudoEMetricSpace α] {β : Type u_2} {p : β → Prop}
 {f : β → ENNReal},   (∀ (x : β), p x → 0 < f x) →     (∀ (ε : ENNReal), 0 < ε →
 ∃ x, p x ∧ f x ≤ ε) → (uniformity α).HasBasis p fun x => {p | edist p.1 p.2 < f
 x}
参数：∀ (x : β), p x → 0 < f x；∀ (ε : ENNReal), 0 < ε → ∃ x, p x ∧ f x ≤ ε；uniformi
ty α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `uniformity_basis_edist`：uniformity_basis_edist : (𝓤 α).HasBasis (fun ε :
 Real>=0∞ => 0 < ε) fun ε => { p : α × α | edist p.1 p.2 < ε }
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `Membership.mem.out`：∀ {α : Type u} {a : α} {p : α → Prop}, a ∈ {x | p x}
 → p a

--- 原说明 ---
Given `f : β → ℝ≥0∞`, if `f` sends `{i | p i}` to a set of positive numbers
accumulating to zero, then `f i`-neighborhoods of the diagonal form a basis of `
𝓤 α`.

For specific bases see `uniformity_basis_edist`, `uniformity_basis_edist'`,
`uniformity_basis_edist_nnreal`, and `uniformity_basis_edist_inv_nat`.
-/
protected theorem EMetric.mk_uniformity_basis {β : Type*} {p : β → Prop} {f : β → ℝ≥0∞}
    (hf₀ : ∀ x, p x → 0 < f x) (hf : ∀ ε, 0 < ε → ∃ x, p x ∧ f x ≤ ε) :
    (𝓤 α).HasBasis p fun x => { p : α × α | edist p.1 p.2 < f x } := by
  refine ⟨fun s => uniformity_basis_edist.mem_iff.trans ?_⟩
  constructor
  · rintro ⟨ε, ε₀, hε⟩
    rcases hf ε ε₀ with ⟨i, hi, H⟩
    exact ⟨i, hi, fun x hx => hε <| lt_of_lt_of_le hx.out H⟩
  · exact fun ⟨i, hi, H⟩ => ⟨f i, hf₀ i hi, H⟩

/-- Given `f : β → ℝ≥0∞`, if `f` sends `{i | p i}` to a set of positive numbers
accumulating to zero, then closed `f i`-neighborhoods of the diagonal form a basis of `𝓤 α`.

For specific bases see `uniformity_basis_edist_le` and `uniformity_basis_edist_le'`. -/
/-
**EMetric.mk_uniformity_basis_le** 是 Mathlib 中的一个定理，位于命名空间 `EMetric`。
形式化陈述：∀ {α : Type u} [inst : PseudoEMetricSpace α] {β : Type u_2} {p : β → Prop}
 {f : β → ENNReal},   (∀ (x : β), p x → 0 < f x) →     (∀ (ε : ENNReal), 0 < ε →
 ∃ x, p x ∧ f x ≤ ε) → (uniformity α).HasBasis p fun x => {p | edist p.1 p.2 ≤ f
 x}
参数：∀ (x : β), p x → 0 < f x；∀ (ε : ENNReal), 0 < ε → ∃ x, p x ∧ f x ≤ ε；uniformi
ty α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `uniformity_basis_edist`：uniformity_basis_edist : (𝓤 α).HasBasis (fun ε :
 Real>=0∞ => 0 < ε) fun ε => { p : α × α | edist p.1 p.2 < ε }
· 使用定理 `exists_between`：exists_between [LT α] [DenselyOrdered α] {a₁ a₂ : α} : a
₁ < a₂ -> exists a, a₁ < a ∧ a < a₂
· 使用定理 `ENNReal.instDenselyOrdered`：DenselyOrdered ENNReal
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Membership.mem.out`：∀ {α : Type u} {a : α} {p : α → Prop}, a ∈ {x | p x}
 → p a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b

--- 原说明 ---
Given `f : β → ℝ≥0∞`, if `f` sends `{i | p i}` to a set of positive numbers
accumulating to zero, then closed `f i`-neighborhoods of the diagonal form a bas
is of `𝓤 α`.

For specific bases see `uniformity_basis_edist_le` and `uniformity_basis_edist_l
e'`.
-/
protected theorem EMetric.mk_uniformity_basis_le {β : Type*} {p : β → Prop} {f : β → ℝ≥0∞}
    (hf₀ : ∀ x, p x → 0 < f x) (hf : ∀ ε, 0 < ε → ∃ x, p x ∧ f x ≤ ε) :
    (𝓤 α).HasBasis p fun x => { p : α × α | edist p.1 p.2 ≤ f x } := by
  refine ⟨fun s => uniformity_basis_edist.mem_iff.trans ?_⟩
  constructor
  · rintro ⟨ε, ε₀, hε⟩
    rcases exists_between ε₀ with ⟨ε', hε'⟩
    rcases hf ε' hε'.1 with ⟨i, hi, H⟩
    exact ⟨i, hi, fun x hx => hε <| lt_of_le_of_lt (le_trans hx.out H) hε'.2⟩
  · exact fun ⟨i, hi, H⟩ => ⟨f i, hf₀ i hi, fun x hx => H (le_of_lt hx.out)⟩
/-
**uniformity_basis_edist_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniformity_basis_edist_le : (𝓤 α).HasBasis (fun ε : Real>=0∞ => 0 < ε) fun
 ε => { p : α × α | edist p.1 p.2 <= ε }
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EMetric.mk_uniformity_basis_le`：∀ {α : Type u} [inst : PseudoEMetricSpac
e α] {β : Type u_2} {p : β → Prop} {f : β → ENNReal},   (∀ (x : β), p x → 0 < f 
x) →     (∀ (ε : ENN…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem uniformity_basis_edist_le :
    (𝓤 α).HasBasis (fun ε : ℝ≥0∞ => 0 < ε) fun ε => { p : α × α | edist p.1 p.2 ≤ ε } :=
  EMetric.mk_uniformity_basis_le (fun _ => id) fun ε ε₀ => ⟨ε, ε₀, le_refl ε⟩
/-
**uniformity_basis_edist'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniformity_basis_edist' (ε' : Real>=0∞) (hε' : 0 < ε') : (𝓤 α).HasBasis (f
un ε : Real>=0∞ => ε in Ioo 0 ε') fun ε => { p : α × α | edist p.1 p.2 < ε }
参数：ε' : Real>=0∞；hε' : 0 < ε'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EMetric.mk_uniformity_basis`：∀ {α : Type u} [inst : PseudoEMetricSpace α
] {β : Type u_2} {p : β → Prop} {f : β → ENNReal},   (∀ (x : β), p x → 0 < f x) 
→     (∀ (ε : ENN…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `exists_between`：exists_between [LT α] [DenselyOrdered α] {a₁ a₂ : α} : a
₁ < a₂ -> exists a, a₁ < a ∧ a < a₂
· 使用定理 `ENNReal.instDenselyOrdered`：DenselyOrdered ENNReal
· 使用引理 `lt_min`：lt_min (h₁ : a < b) (h₂ : a < c) : a < min b c
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用引理 `min_le_right`：min_le_right (a b : α) : min a b <= b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `min_le_left`：min_le_left (a b : α) : min a b <= a
-/
theorem uniformity_basis_edist' (ε' : ℝ≥0∞) (hε' : 0 < ε') :
    (𝓤 α).HasBasis (fun ε : ℝ≥0∞ => ε ∈ Ioo 0 ε') fun ε => { p : α × α | edist p.1 p.2 < ε } :=
  EMetric.mk_uniformity_basis (fun _ => And.left) fun ε ε₀ =>
    let ⟨δ, hδ⟩ := exists_between hε'
    ⟨min ε δ, ⟨lt_min ε₀ hδ.1, lt_of_le_of_lt (min_le_right _ _) hδ.2⟩, min_le_left _ _⟩
/-
**uniformity_basis_edist_le'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniformity_basis_edist_le' (ε' : Real>=0∞) (hε' : 0 < ε') : (𝓤 α).HasBasis
 (fun ε : Real>=0∞ => ε in Ioo 0 ε') fun ε => { p : α × α | edist p.1 p.2 <= ε }
参数：ε' : Real>=0∞；hε' : 0 < ε'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EMetric.mk_uniformity_basis_le`：∀ {α : Type u} [inst : PseudoEMetricSpac
e α] {β : Type u_2} {p : β → Prop} {f : β → ENNReal},   (∀ (x : β), p x → 0 < f 
x) →     (∀ (ε : ENN…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `exists_between`：exists_between [LT α] [DenselyOrdered α] {a₁ a₂ : α} : a
₁ < a₂ -> exists a, a₁ < a ∧ a < a₂
· 使用定理 `ENNReal.instDenselyOrdered`：DenselyOrdered ENNReal
· 使用引理 `lt_min`：lt_min (h₁ : a < b) (h₂ : a < c) : a < min b c
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用引理 `min_le_right`：min_le_right (a b : α) : min a b <= b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `min_le_left`：min_le_left (a b : α) : min a b <= a
-/
theorem uniformity_basis_edist_le' (ε' : ℝ≥0∞) (hε' : 0 < ε') :
    (𝓤 α).HasBasis (fun ε : ℝ≥0∞ => ε ∈ Ioo 0 ε') fun ε => { p : α × α | edist p.1 p.2 ≤ ε } :=
  EMetric.mk_uniformity_basis_le (fun _ => And.left) fun ε ε₀ =>
    let ⟨δ, hδ⟩ := exists_between hε'
    ⟨min ε δ, ⟨lt_min ε₀ hδ.1, lt_of_le_of_lt (min_le_right _ _) hδ.2⟩, min_le_left _ _⟩
/-
**uniformity_basis_edist_nnreal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniformity_basis_edist_nnreal : (𝓤 α).HasBasis (fun ε : Real>=0 => 0 < ε) 
fun ε => { p : α × α | edist p.1 p.2 < ε }
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EMetric.mk_uniformity_basis`：∀ {α : Type u} [inst : PseudoEMetricSpace α
] {β : Type u_2} {p : β → Prop} {f : β → ENNReal},   (∀ (x : β), p x → 0 < f x) 
→     (∀ (ε : ENN…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.coe_pos`：∀ {r : NNReal}, 0 < ↑r ↔ 0 < r
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ENNReal.lt_iff_exists_nnreal_btwn`：lt_iff_exists_nnreal_btwn : a < b ↔ e
xists r : Real>=0, a < r ∧ (r : Real>=0∞) < b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem uniformity_basis_edist_nnreal :
    (𝓤 α).HasBasis (fun ε : ℝ≥0 => 0 < ε) fun ε => { p : α × α | edist p.1 p.2 < ε } :=
  EMetric.mk_uniformity_basis (fun _ => ENNReal.coe_pos.2) fun _ε ε₀ =>
    let ⟨δ, hδ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ε₀
    ⟨δ, ENNReal.coe_pos.1 hδ.1, le_of_lt hδ.2⟩
/-
**uniformity_basis_edist_nnreal_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniformity_basis_edist_nnreal_le : (𝓤 α).HasBasis (fun ε : Real>=0 => 0 < 
ε) fun ε => { p : α × α | edist p.1 p.2 <= ε }
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EMetric.mk_uniformity_basis_le`：∀ {α : Type u} [inst : PseudoEMetricSpac
e α] {β : Type u_2} {p : β → Prop} {f : β → ENNReal},   (∀ (x : β), p x → 0 < f 
x) →     (∀ (ε : ENN…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.coe_pos`：∀ {r : NNReal}, 0 < ↑r ↔ 0 < r
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ENNReal.lt_iff_exists_nnreal_btwn`：lt_iff_exists_nnreal_btwn : a < b ↔ e
xists r : Real>=0, a < r ∧ (r : Real>=0∞) < b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem uniformity_basis_edist_nnreal_le :
    (𝓤 α).HasBasis (fun ε : ℝ≥0 => 0 < ε) fun ε => { p : α × α | edist p.1 p.2 ≤ ε } :=
  EMetric.mk_uniformity_basis_le (fun _ => ENNReal.coe_pos.2) fun _ε ε₀ =>
    let ⟨δ, hδ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ε₀
    ⟨δ, ENNReal.coe_pos.1 hδ.1, le_of_lt hδ.2⟩
/-
**uniformity_basis_edist_inv_nat** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniformity_basis_edist_inv_nat : (𝓤 α).HasBasis (fun _ => True) fun n : Na
t => { p : α × α | edist p.1 p.2 < (↑n)⁻¹ }
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EMetric.mk_uniformity_basis`：∀ {α : Type u} [inst : PseudoEMetricSpace α
] {β : Type u_2} {p : β → Prop} {f : β → ENNReal},   (∀ (x : β), p x → 0 < f x) 
→     (∀ (ε : ENN…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.inv_pos`：∀ {a : ENNReal}, 0 < a⁻¹ ↔ a ≠ ⊤
· 使用定理 `ENNReal.natCast_ne_top`：natCast_ne_top (n : Nat) : (n : Real>=0∞) != ∞
· 使用定理 `ENNReal.exists_inv_nat_lt`：exists_inv_nat_lt {a : Real>=0∞} (h : a != 0)
 : exists n : Nat, (n : Real>=0∞)⁻¹ < a
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `trivial`：True
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem uniformity_basis_edist_inv_nat :
    (𝓤 α).HasBasis (fun _ => True) fun n : ℕ => { p : α × α | edist p.1 p.2 < (↑n)⁻¹ } :=
  EMetric.mk_uniformity_basis (fun n _ ↦ ENNReal.inv_pos.2 <| ENNReal.natCast_ne_top n) fun _ε ε₀ ↦
    let ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt (ne_of_gt ε₀)
    ⟨n, trivial, le_of_lt hn⟩
/-
**uniformity_basis_edist_inv_two_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniformity_basis_edist_inv_two_pow : (𝓤 α).HasBasis (fun _ => True) fun n 
: Nat => { p : α × α | edist p.1 p.2 < 2⁻¹ ^ n }
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EMetric.mk_uniformity_basis`：∀ {α : Type u} [inst : PseudoEMetricSpace α
] {β : Type u_2} {p : β → Prop} {f : β → ENNReal},   (∀ (x : β), p x → 0 < f x) 
→     (∀ (ε : ENN…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `ENNReal.pow_pos`：∀ {a : ENNReal}, 0 < a → ∀ (n : ℕ), 0 < a ^ n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.inv_pos`：∀ {a : ENNReal}, 0 < a⁻¹ ↔ a ≠ ⊤
· 使用引理 `ENNReal.ofNat_ne_top`：ofNat_ne_top {n : Nat} [Nat.AtLeastTwo n] : ofNat(
n) != ∞
· 使用定理 `ENNReal.exists_inv_two_pow_lt`：exists_inv_two_pow_lt (ha : a != 0) : exi
sts n : Nat, 2⁻¹ ^ n < a
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `trivial`：True
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem uniformity_basis_edist_inv_two_pow :
    (𝓤 α).HasBasis (fun _ => True) fun n : ℕ => { p : α × α | edist p.1 p.2 < 2⁻¹ ^ n } :=
  EMetric.mk_uniformity_basis (fun _ _ ↦ ENNReal.pow_pos (ENNReal.inv_pos.2 ENNReal.ofNat_ne_top) _)
    fun _ε ε₀ ↦
    let ⟨n, hn⟩ := ENNReal.exists_inv_two_pow_lt (ne_of_gt ε₀)
    ⟨n, trivial, le_of_lt hn⟩

/-- Fixed size neighborhoods of the diagonal belong to the uniform structure -/
/-
**edist_mem_uniformity** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：edist_mem_uniformity {ε : Real>=0∞} (ε0 : 0 < ε) : { p : α × α | edist p.1
 p.2 < ε } in 𝓤 α
参数：ε0 : 0 < ε。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mem_uniformity_edist`：mem_uniformity_edist {s : Set (α × α)} : s in 𝓤 α 
↔ exists ε > 0, forall {a b : α}, edist a b < ε -> (a, b) in s

--- 原说明 ---
Fixed size neighborhoods of the diagonal belong to the uniform structure
-/
theorem edist_mem_uniformity {ε : ℝ≥0∞} (ε0 : 0 < ε) : { p : α × α | edist p.1 p.2 < ε } ∈ 𝓤 α :=
  mem_uniformity_edist.2 ⟨ε, ε0, id⟩

namespace EMetric

/-
**EMetric.** 是 Mathlib 中的一个实例，位于命名空间 `EMetric`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 900) instIsCountablyGeneratedUniformity : IsCountablyGenerated (𝓤 α) :=
  isCountablyGenerated_of_seq ⟨_, uniformity_basis_edist_inv_nat.eq_iInf⟩

/-- ε-δ characterization of uniform continuity on a set for pseudoemetric spaces -/
/-
**EMetric.uniformContinuousOn_iff** 是 Mathlib 中的一个定理，位于命名空间 `EMetric`。
形式化陈述：uniformContinuousOn_iff [PseudoEMetricSpace β] {f : α -> β} {s : Set α} : 
UniformContinuousOn f s ↔ forall ε > 0, exists δ > 0, forall {a}, a in s -> fora
ll {b}, b in s -> edist a b < δ -> edist (f a) (f b) < ε
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.uniformContinuousOn_iff`：Filter.HasBasis.uniformContinuo
usOn_iff {ι'} {p : ι -> Prop} {s : ι -> SetRel α α} (ha : (𝓤 α).HasBasis p s) {q
 : ι' -> Prop} {t : ι' -> Set…
· 使用定理 `uniformity_basis_edist`：uniformity_basis_edist : (𝓤 α).HasBasis (fun ε :
 Real>=0∞ => 0 < ε) fun ε => { p : α × α | edist p.1 p.2 < ε }

--- 原说明 ---
ε-δ characterization of uniform continuity on a set for pseudoemetric spaces
-/
theorem uniformContinuousOn_iff [PseudoEMetricSpace β] {f : α → β} {s : Set α} :
    UniformContinuousOn f s ↔
      ∀ ε > 0, ∃ δ > 0, ∀ {a}, a ∈ s → ∀ {b}, b ∈ s → edist a b < δ → edist (f a) (f b) < ε :=
  uniformity_basis_edist.uniformContinuousOn_iff uniformity_basis_edist

/-- ε-δ characterization of uniform continuity on pseudoemetric spaces -/
/-
**EMetric.uniformContinuous_iff** 是 Mathlib 中的一个定理，位于命名空间 `EMetric`。
形式化陈述：uniformContinuous_iff [PseudoEMetricSpace β] {f : α -> β} : UniformContinu
ous f ↔ forall ε > 0, exists δ > 0, forall {a b : α}, edist a b < δ -> edist (f 
a) (f b) < ε
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.uniformContinuous_iff`：Filter.HasBasis.uniformContinuous
_iff {ι'} {p : ι -> Prop} {s : ι -> SetRel α α} (ha : (𝓤 α).HasBasis p s) {q : ι
' -> Prop} {t : ι' -> Set (…
· 使用定理 `uniformity_basis_edist`：uniformity_basis_edist : (𝓤 α).HasBasis (fun ε :
 Real>=0∞ => 0 < ε) fun ε => { p : α × α | edist p.1 p.2 < ε }

--- 原说明 ---
ε-δ characterization of uniform continuity on pseudoemetric spaces
-/
theorem uniformContinuous_iff [PseudoEMetricSpace β] {f : α → β} :
    UniformContinuous f ↔ ∀ ε > 0, ∃ δ > 0, ∀ {a b : α}, edist a b < δ → edist (f a) (f b) < ε :=
  uniformity_basis_edist.uniformContinuous_iff uniformity_basis_edist

end EMetric

open EMetric

/-- Auxiliary function to replace the uniformity on a pseudoemetric space with
a uniformity which is equal to the original one, but maybe not defeq.
This is useful if one wants to construct a pseudoemetric space with a
specified uniformity. See Note [forgetful inheritance] explaining why having definitionally
the right uniformity is often important.
See note [reducible non-instances].
-/
/-
**PseudoEMetricSpace.replaceUniformity** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：PseudoEMetricSpace.replaceUniformity {α} [U : UniformSpace α] (m : PseudoE
MetricSpace α) (H : 𝓤[U] = 𝓤[PseudoEMetricSpace.toUniformSpace]) : PseudoEMetric
Space α where edist
参数：m : PseudoEMetricSpace α；H : 𝓤[U] = 𝓤[PseudoEMetricSpace.toUniformSpace]。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `PseudoEMetricSpace.edist_self`：∀ {α : Type u} [self : PseudoEMetricSpace
 α] (x : α), edist x x = 0
· 使用定理 `PseudoEMetricSpace.edist_comm`：∀ {α : Type u} [self : PseudoEMetricSpace
 α] (x y : α), edist x y = edist y x
· 使用定理 `PseudoEMetricSpace.edist_triangle`：∀ {α : Type u} [self : PseudoEMetricS
pace α] (x y z : α), edist x z ≤ edist x y + edist y z

--- 原说明 ---
Auxiliary function to replace the uniformity on a pseudoemetric space with
a uniformity which is equal to the original one, but maybe not defeq.
This is useful if one wants to construct a pseudoemetric space with a
specified uniformity. See Note [forgetful inheritance] explaining why having def
initionally
the right uniformity is often important.
See note [reducible non-instances].
-/
abbrev PseudoEMetricSpace.replaceUniformity {α} [U : UniformSpace α] (m : PseudoEMetricSpace α)
    (H : 𝓤[U] = 𝓤[PseudoEMetricSpace.toUniformSpace]) : PseudoEMetricSpace α where
  edist := @edist _ m.toEDist
  edist_self := edist_self
  edist_comm := edist_comm
  edist_triangle := edist_triangle
  toUniformSpace := U
  uniformity_edist := H.trans (@PseudoEMetricSpace.uniformity_edist α _)

/-- The extended pseudometric induced by a function taking values in a pseudoemetric space.
See note [reducible non-instances]. -/
/-
**PseudoEMetricSpace.induced** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：PseudoEMetricSpace.induced {α β} (f : α -> β) (m : PseudoEMetricSpace β) :
 PseudoEMetricSpace α where edist x y
参数：f : α -> β；m : PseudoEMetricSpace β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The extended pseudometric induced by a function taking values in a pseudoemetric
 space.
See note [reducible non-instances].
-/
abbrev PseudoEMetricSpace.induced {α β} (f : α → β) (m : PseudoEMetricSpace β) :
    PseudoEMetricSpace α where
  edist x y := edist (f x) (f y)
  edist_self _ := edist_self _
  edist_comm _ _ := edist_comm _ _
  edist_triangle _ _ _ := edist_triangle _ _ _
  toUniformSpace := UniformSpace.comap f m.toUniformSpace
  uniformity_edist := (uniformity_basis_edist.comap (Prod.map f f)).eq_biInf

/-- Pseudoemetric space instance on subsets of pseudoemetric spaces -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Pseudoemetric space instance on subsets of pseudoemetric spaces
-/
instance {α : Type*} {p : α → Prop} [PseudoEMetricSpace α] : PseudoEMetricSpace (Subtype p) :=
  PseudoEMetricSpace.induced Subtype.val ‹_›

/-- The extended pseudodistance on a subset of a pseudoemetric space is the restriction of
the original pseudodistance, by definition. -/
/-
**Subtype.edist_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subtype.edist_eq {p : α -> Prop} (x y : Subtype p) : edist x y = edist (x 
: α) y
参数：x y : Subtype p。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The extended pseudodistance on a subset of a pseudoemetric space is the restrict
ion of
the original pseudodistance, by definition.
-/
theorem Subtype.edist_eq {p : α → Prop} (x y : Subtype p) : edist x y = edist (x : α) y := rfl

/-- The extended pseudodistance on a subtype of a pseudoemetric space is the restriction of
the original pseudodistance, by definition. -/
@[simp]
/-
**Subtype.edist_mk_mk** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subtype.edist_mk_mk {p : α -> Prop} {x y : α} (hx : p x) (hy : p y) : edis
t (⟨x, hx⟩ : Subtype p) ⟨y, hy⟩ = edist x y
参数：hx : p x；hy : p y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The extended pseudodistance on a subtype of a pseudoemetric space is the restric
tion of
the original pseudodistance, by definition.
-/
theorem Subtype.edist_mk_mk {p : α → Prop} {x y : α} (hx : p x) (hy : p y) :
    edist (⟨x, hx⟩ : Subtype p) ⟨y, hy⟩ = edist x y :=
  rfl

/-- Consider an extended distance on a topological space, for which the neighborhoods can be
expressed in terms of the distance. Then we define the emetric space structure associated to this
distance, with a topology defeq to the initial one. -/
/-
**PseudoEMetricSpace.ofEDistOfTopology** 是 Mathlib 中的一个定义，位于命名空间 `PseudoEMetricS
pace`。
形式化陈述：{α : Type u_2} →   [inst : TopologicalSpace α] →     (d : α → α → ENNReal)
 →       (∀ (x : α), d x x = 0) →         (∀ (x y : α), d x y = d y x) →        
   (∀ (x y z : α), d x z ≤ d x y + d y z) →             (∀ (x : α), (nhds x).Has
Basis (fun c => 0 < c) fun c => {y | d x y < c}) → PseudoEMetricSpace α
参数：d : α → α → ENNReal；∀ (x : α), d x x = 0；∀ (x y : α), d x y = d y x；∀ (x y z 
: α), d x z ≤ d x y + d y z；∀ (x : α), (nhds x).HasBasis (fun c => 0 < c) fun c 
=> {y | d x y < c}。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Consider an extended distance on a topological space, for which the neighborhood
s can be
expressed in terms of the distance. Then we define the emetric space structure a
ssociated to this
distance, with a topology defeq to the initial one.
-/
@[reducible] noncomputable def PseudoEMetricSpace.ofEDistOfTopology {α : Type*} [TopologicalSpace α]
    (d : α → α → ℝ≥0∞) (h_self : ∀ x, d x x = 0) (h_comm : ∀ x y, d x y = d y x)
    (h_triangle : ∀ x y z, d x z ≤ d x y + d y z)
    (h_basis : ∀ x, (𝓝 x).HasBasis (fun c ↦ 0 < c) (fun c ↦ {y | d x y < c})) :
    PseudoEMetricSpace α where
  edist := d
  edist_self := h_self
  edist_comm := h_comm
  edist_triangle := h_triangle
  toUniformSpace := uniformSpaceOfEDistOfHasBasis d h_self h_comm h_triangle h_basis
  uniformity_edist := rfl

@[deprecated (since := "2026-01-08")]
alias PseudoEmetricSpace.ofEdistOfTopology := PseudoEMetricSpace.ofEDistOfTopology

namespace MulOpposite

/-- Pseudoemetric space instance on the multiplicative opposite of a pseudoemetric space. -/
@[to_additive
/-- Pseudoemetric space instance on the additive opposite of a pseudoemetric space. -/]
/-
**MulOpposite.** 是 Mathlib 中的一个实例，位于命名空间 `MulOpposite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {α : Type*} [PseudoEMetricSpace α] : PseudoEMetricSpace αᵐᵒᵖ :=
  PseudoEMetricSpace.induced unop ‹_›

@[to_additive]
/-
**MulOpposite.edist_unop** 是 Mathlib 中的一个定理，位于命名空间 `MulOpposite`。
形式化陈述：edist_unop (x y : αᵐᵒᵖ) : edist (unop x) (unop y) = edist x y
参数：x y : αᵐᵒᵖ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem edist_unop (x y : αᵐᵒᵖ) : edist (unop x) (unop y) = edist x y := rfl

@[to_additive]
/-
**MulOpposite.edist_op** 是 Mathlib 中的一个定理，位于命名空间 `MulOpposite`。
形式化陈述：edist_op (x y : α) : edist (op x) (op y) = edist x y
参数：x y : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem edist_op (x y : α) : edist (op x) (op y) = edist x y := rfl

end MulOpposite

section ULift

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PseudoEMetricSpace (ULift α) := PseudoEMetricSpace.induced ULift.down ‹_›
/-
**ULift.edist_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ULift.edist_eq (x y : ULift α) : edist x y = edist x.down y.down
参数：x y : ULift α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ULift.edist_eq (x y : ULift α) : edist x y = edist x.down y.down := rfl

@[simp]
/-
**ULift.edist_up_up** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ULift.edist_up_up (x y : α) : edist (ULift.up x) (ULift.up y) = edist x y
参数：x y : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ULift.edist_up_up (x y : α) : edist (ULift.up x) (ULift.up y) = edist x y := rfl

end ULift

/-- The product of two pseudoemetric spaces, with the max distance, is an extended
pseudometric spaces. We make sure that the uniform structure thus constructed is the one
corresponding to the product of uniform spaces, to avoid diamond problems. -/
/-
**Prod.pseudoEMetricSpaceMax** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Prod.pseudoEMetricSpaceMax [PseudoEMetricSpace β] : PseudoEMetricSpace (α 
× β) where edist x y
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The product of two pseudoemetric spaces, with the max distance, is an extended
pseudometric spaces. We make sure that the uniform structure thus constructed is
 the one
corresponding to the product of uniform spaces, to avoid diamond problems.
-/
instance Prod.pseudoEMetricSpaceMax [PseudoEMetricSpace β] :
    PseudoEMetricSpace (α × β) where
  edist x y := edist x.1 y.1 ⊔ edist x.2 y.2
  edist_self x := by simp
  edist_comm x y := by simp [edist_comm]
  edist_triangle _ _ _ :=
    max_le (le_trans (edist_triangle _ _ _) (add_le_add (le_max_left _ _) (le_max_left _ _)))
      (le_trans (edist_triangle _ _ _) (add_le_add (le_max_right _ _) (le_max_right _ _)))
  uniformity_edist := uniformity_prod.trans <| by
    simp [PseudoEMetricSpace.uniformity_edist, ← iInf_inf_eq, ofPred_and]
  toUniformSpace := inferInstance
/-
**Prod.edist_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Prod.edist_eq [PseudoEMetricSpace β] (x y : α × β) : edist x y = max (edis
t x.1 y.1) (edist x.2 y.2)
参数：x y : α × β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Prod.edist_eq [PseudoEMetricSpace β] (x y : α × β) :
    edist x y = max (edist x.1 y.1) (edist x.2 y.2) :=
  rfl

namespace Metric

variable {x y z : α} {ε ε₁ ε₂ : ℝ≥0∞} {s t : Set α}

/-
**Metric.mem_eball'** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：mem_eball' : y in eball x ε ↔ edist x y < ε
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PseudoEMetricSpace.edist_comm`：∀ {α : Type u} [self : PseudoEMetricSpace
 α] (x y : α), edist x y = edist y x
· 使用定理 `Metric.mem_eball`：∀ {α : Type u} [inst : EDist α] {x y : α} {ε : ENNReal
}, y ∈ Metric.eball x ε ↔ edist y x < ε
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_eball' : y ∈ eball x ε ↔ edist x y < ε := by rw [edist_comm, mem_eball]

/-- `Metric.closedEBall x ε` is the set of all points `y` with `edist y x ≤ ε` -/
/-
**Metric.closedEBall** 是 Mathlib 中的一个定义，位于命名空间 `Metric`。
形式化陈述：closedEBall (x : α) (ε : Real>=0∞)
参数：x : α；ε : Real>=0∞。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Metric.closedEBall x ε` is the set of all points `y` with `edist y x ≤ ε`
-/
def closedEBall (x : α) (ε : ℝ≥0∞) :=
  { y | edist y x ≤ ε }
/-
**Metric.mem_closedEBall** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：∀ {α : Type u} [inst : PseudoEMetricSpace α] {x y : α} {ε : ENNReal}, y ∈ 
Metric.closedEBall x ε ↔ edist y x ≤ ε
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] theorem mem_closedEBall : y ∈ closedEBall x ε ↔ edist y x ≤ ε := Iff.rfl
/-
**Metric.mem_closedEBall'** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：mem_closedEBall' : y in closedEBall x ε ↔ edist x y <= ε
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PseudoEMetricSpace.edist_comm`：∀ {α : Type u} [self : PseudoEMetricSpace
 α] (x y : α), edist x y = edist y x
· 使用定理 `Metric.mem_closedEBall`：∀ {α : Type u} [inst : PseudoEMetricSpace α] {x 
y : α} {ε : ENNReal}, y ∈ Metric.closedEBall x ε ↔ edist y x ≤ ε
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_closedEBall' : y ∈ closedEBall x ε ↔ edist x y ≤ ε := by
  rw [edist_comm, mem_closedEBall]

@[simp]
/-
**Metric.closedEBall_top** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：closedEBall_top (x : α) : closedEBall x ∞ = univ
参数：x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_univ_of_forall`：eq_univ_of_forall {s : Set α} : (forall x, x in s
) -> s = univ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_ofPred`：mem_ofPred {a : α} {p : α -> Prop} : a in { x | p x } ↔ 
p a
· 使用定理 `le_top`：le_top : a <= ⊤
-/
theorem closedEBall_top (x : α) : closedEBall x ∞ = univ :=
  eq_univ_of_forall fun _ => mem_ofPred.2 le_top
/-
**Metric.eball_subset_closedEBall** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：eball_subset_closedEBall : eball x ε subseteq closedEBall x ε
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Membership.mem.out`：∀ {α : Type u} {a : α} {p : α → Prop}, a ∈ {x | p x}
 → p a
-/
theorem eball_subset_closedEBall : eball x ε ⊆ closedEBall x ε := fun _ h => le_of_lt h.out
/-
**Metric.pos_of_mem_eball** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：pos_of_mem_eball (hy : y in eball x ε) : 0 < ε
参数：hy : y in eball x ε。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.pos`：∀ {α : Type u_1} {a b : α} [inst : Preorder α] [inst_1 : Zero
 α] [IsBotZeroClass α], a < b → 0 < b
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
-/
theorem pos_of_mem_eball (hy : y ∈ eball x ε) : 0 < ε :=
  hy.pos
/-
**Metric.mem_eball_self** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：mem_eball_self (h : 0 < ε) : x in eball x ε
参数：h : 0 < ε。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.mem_eball`：∀ {α : Type u} [inst : EDist α] {x y : α} {ε : ENNReal
}, y ∈ Metric.eball x ε ↔ edist y x < ε
· 使用定理 `PseudoEMetricSpace.edist_self`：∀ {α : Type u} [self : PseudoEMetricSpace
 α] (x : α), edist x x = 0
-/
theorem mem_eball_self (h : 0 < ε) : x ∈ eball x ε := by
  rwa [mem_eball, edist_self]
/-
**Metric.mem_closedEBall_self** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：mem_closedEBall_self : x in closedEBall x ε
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.mem_closedEBall`：∀ {α : Type u} [inst : PseudoEMetricSpace α] {x 
y : α} {ε : ENNReal}, y ∈ Metric.closedEBall x ε ↔ edist y x ≤ ε
· 使用定理 `PseudoEMetricSpace.edist_self`：∀ {α : Type u} [self : PseudoEMetricSpace
 α] (x : α), edist x x = 0
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
-/
theorem mem_closedEBall_self : x ∈ closedEBall x ε := by
  rw [mem_closedEBall, edist_self]; apply zero_le
/-
**Metric.mem_eball_comm** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：mem_eball_comm : x in eball y ε ↔ y in eball x ε
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.mem_eball'`：mem_eball' : y in eball x ε ↔ edist x y < ε
· 使用定理 `Metric.mem_eball`：∀ {α : Type u} [inst : EDist α] {x y : α} {ε : ENNReal
}, y ∈ Metric.eball x ε ↔ edist y x < ε
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_eball_comm : x ∈ eball y ε ↔ y ∈ eball x ε := by rw [mem_eball', mem_eball]
/-
**Metric.mem_closedEBall_comm** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：mem_closedEBall_comm : x in closedEBall y ε ↔ y in closedEBall x ε
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.mem_closedEBall'`：mem_closedEBall' : y in closedEBall x ε ↔ edist
 x y <= ε
· 使用定理 `Metric.mem_closedEBall`：∀ {α : Type u} [inst : PseudoEMetricSpace α] {x 
y : α} {ε : ENNReal}, y ∈ Metric.closedEBall x ε ↔ edist y x ≤ ε
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_closedEBall_comm : x ∈ closedEBall y ε ↔ y ∈ closedEBall x ε := by
  rw [mem_closedEBall', mem_closedEBall]

@[gcongr]
/-
**Metric.eball_subset_eball** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：eball_subset_eball (h : ε₁ <= ε₂) : eball x ε₁ subseteq eball x ε₂
参数：h : ε₁ <= ε₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
-/
theorem eball_subset_eball (h : ε₁ ≤ ε₂) : eball x ε₁ ⊆ eball x ε₂ := fun _y (yx : _ < ε₁) =>
  lt_of_lt_of_le yx h

@[gcongr]
/-
**Metric.closedEBall_subset_closedEBall** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：closedEBall_subset_closedEBall (h : ε₁ <= ε₂) : closedEBall x ε₁ subseteq 
closedEBall x ε₂
参数：h : ε₁ <= ε₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
-/
theorem closedEBall_subset_closedEBall (h : ε₁ ≤ ε₂) : closedEBall x ε₁ ⊆ closedEBall x ε₂ :=
  fun _y (yx : _ ≤ ε₁) => le_trans yx h
/-
**Metric.eball_disjoint** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：eball_disjoint (h : ε₁ + ε₂ <= edist x y) : Disjoint (eball x ε₁) (eball y
 ε₂)
参数：h : ε₁ + ε₂ <= edist x y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s -> 
a ∉ t
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `edist_triangle_left`：edist_triangle_left (x y z : α) : edist x y <= edis
t z x + edist z y
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `ENNReal.add_lt_add`：∀ {a b c d : ENNReal}, a < c → b < d → a + b < c + d
-/
theorem eball_disjoint (h : ε₁ + ε₂ ≤ edist x y) : Disjoint (eball x ε₁) (eball y ε₂) :=
  Set.disjoint_left.mpr fun z h₁ h₂ =>
    (edist_triangle_left x y z).not_gt <| (ENNReal.add_lt_add h₁ h₂).trans_le h
/-
**Metric.eball_subset** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：eball_subset (h : edist x y + ε₁ <= ε₂) (h' : edist x y != ∞) : eball x ε₁
 subseteq eball y ε₂
参数：h : edist x y + ε₁ <= ε₂；h' : edist x y != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PseudoEMetricSpace.edist_triangle`：∀ {α : Type u} [self : PseudoEMetricS
pace α] (x y z : α), edist x z ≤ edist x y + edist y z
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `ENNReal.add_lt_add_left`：∀ {a b c : ENNReal}, a ≠ ⊤ → b < c → a + b < a 
+ c
-/
theorem eball_subset (h : edist x y + ε₁ ≤ ε₂) (h' : edist x y ≠ ∞) : eball x ε₁ ⊆ eball y ε₂ :=
  fun z zx =>
  calc
    edist z y ≤ edist z x + edist x y := edist_triangle _ _ _
    _ = edist x y + edist z x := add_comm _ _
    _ < edist x y + ε₁ := ENNReal.add_lt_add_left h' zx
    _ ≤ ε₂ := h
/-
**Metric.exists_eball_subset_eball** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：exists_eball_subset_eball (h : y in eball x ε) : exists ε' > 0, eball y ε'
 subseteq eball x ε
参数：h : y in eball x ε。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
· 使用定理 `Metric.eball_subset`：eball_subset (h : edist x y + ε₁ <= ε₂) (h' : edist
 x y != ∞) : eball x ε₁ subseteq eball y ε₂
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `add_tsub_cancel_of_le`：add_tsub_cancel_of_le (h : a <= b) : a + (b - a) 
= b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Metric.mem_eball`：∀ {α : Type u} [inst : EDist α] {x y : α} {ε : ENNReal
}, y ∈ Metric.eball x ε ↔ edist y x < ε
· 使用定理 `ne_top_of_lt`：ne_top_of_lt (h : a < b) : a != ⊤
-/
theorem exists_eball_subset_eball (h : y ∈ eball x ε) : ∃ ε' > 0, eball y ε' ⊆ eball x ε := by
  have : 0 < ε - edist y x := by simpa using h
  refine ⟨ε - edist y x, this, eball_subset ?_ (ne_top_of_lt h)⟩
  exact (add_tsub_cancel_of_le (mem_eball.mp h).le).le
/-
**Metric.eball_eq_empty_iff** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：eball_eq_empty_iff : eball x ε = ∅ ↔ ε = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Set.eq_empty_iff_forall_notMem`：eq_empty_iff_forall_notMem {s : Set α} :
 s = ∅ ↔ forall x, x ∉ s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `le_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ ↔ a = ⊥
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Metric.mem_eball_self`：mem_eball_self (h : 0 < ε) : x in eball x ε
· 使用定理 `not_lt_of_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Metric.pos_of_mem_eball`：pos_of_mem_eball (hy : y in eball x ε) : 0 < ε
-/
theorem eball_eq_empty_iff : eball x ε = ∅ ↔ ε = 0 :=
  eq_empty_iff_forall_notMem.trans
    ⟨fun h => le_bot_iff.1 (le_of_not_gt fun ε0 => h _ (mem_eball_self ε0)), fun ε0 _ h =>
      not_lt_of_ge (le_of_eq ε0) (pos_of_mem_eball h)⟩
/-
**Metric.ordConnected_setOfPred_closedEBall_subset** 是 Mathlib 中的一个定理，位于命名空间 `Me
tric`。
形式化陈述：ordConnected_setOfPred_closedEBall_subset (x : α) (s : Set α) : OrdConnect
ed { r | closedEBall x r subseteq s }
参数：x : α；s : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Metric.closedEBall_subset_closedEBall`：closedEBall_subset_closedEBall (h
 : ε₁ <= ε₂) : closedEBall x ε₁ subseteq closedEBall x ε₂
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem ordConnected_setOfPred_closedEBall_subset (x : α) (s : Set α) :
    OrdConnected { r | closedEBall x r ⊆ s } :=
  ⟨fun _ _ _ h₁ _ h₂ => (closedEBall_subset_closedEBall h₂.2).trans h₁⟩

@[deprecated (since := "2026-07-09")]
alias ordConnected_setOf_closedEBall_subset := ordConnected_setOfPred_closedEBall_subset
/-
**Metric.ordConnected_setOfPred_eball_subset** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：ordConnected_setOfPred_eball_subset (x : α) (s : Set α) : OrdConnected { r
 | eball x r subseteq s }
参数：x : α；s : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Metric.eball_subset_eball`：eball_subset_eball (h : ε₁ <= ε₂) : eball x ε
₁ subseteq eball x ε₂
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem ordConnected_setOfPred_eball_subset (x : α) (s : Set α) :
    OrdConnected { r | eball x r ⊆ s } :=
  ⟨fun _ _ _ h₁ _ h₂ => (eball_subset_eball h₂.2).trans h₁⟩

@[deprecated (since := "2026-07-09")]
alias ordConnected_setOf_eball_subset := ordConnected_setOfPred_eball_subset

/-- Relation “two points are at a finite edistance” is an equivalence relation. -/
@[instance_reducible]
/-
**Metric.edistLtTopSetoid** 是 Mathlib 中的一个定义，位于命名空间 `Metric`。
形式化陈述：edistLtTopSetoid : Setoid α where r x y
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Relation “two points are at a finite edistance” is an equivalence relation.
-/
def edistLtTopSetoid : Setoid α where
  r x y := edist x y < ⊤
  iseqv :=
    { refl x := by rw [edist_self]; exact ENNReal.coe_lt_top
      symm h := by rwa [edist_comm]
      trans hxy hyz := lt_of_le_of_lt (edist_triangle _ _ _) (ENNReal.add_lt_top.2 ⟨hxy, hyz⟩) }

@[simp]
/-
**Metric.eball_zero** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：eball_zero : eball x 0 = ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.eball_eq_empty_iff`：eball_eq_empty_iff : eball x ε = ∅ ↔ ε = 0
-/
theorem eball_zero : eball x 0 = ∅ := by rw [eball_eq_empty_iff]
/-
**Metric.nhds_basis_eball** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：nhds_basis_eball : (𝓝 x).HasBasis (fun ε : Real>=0∞ => 0 < ε) (eball x)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nhds_basis_uniformity`：nhds_basis_uniformity {p : ι -> Prop} {s : ι -> S
etRel α α} (h : (𝓤 α).HasBasis p s) {x : α} : (𝓝 x).HasBasis p fun i => { y | (y
, x) in s i…
· 使用定理 `uniformity_basis_edist`：uniformity_basis_edist : (𝓤 α).HasBasis (fun ε :
 Real>=0∞ => 0 < ε) fun ε => { p : α × α | edist p.1 p.2 < ε }
-/
theorem nhds_basis_eball : (𝓝 x).HasBasis (fun ε : ℝ≥0∞ => 0 < ε) (eball x) :=
  nhds_basis_uniformity uniformity_basis_edist
/-
**Metric.nhdsWithin_basis_eball** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：nhdsWithin_basis_eball : (𝓝[s] x).HasBasis (fun ε : Real>=0∞ => 0 < ε) fun
 ε => eball x ε inter s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nhdsWithin_hasBasis`：nhdsWithin_hasBasis {ι : Sort*} {p : ι -> Prop} {s 
: ι -> Set α} {a : α} (h : (𝓝 a).HasBasis p s) (t : Set α) : (𝓝[t] a).HasBasis p
 fun i =>…
· 使用定理 `Metric.nhds_basis_eball`：nhds_basis_eball : (𝓝 x).HasBasis (fun ε : Real
>=0∞ => 0 < ε) (eball x)
-/
theorem nhdsWithin_basis_eball : (𝓝[s] x).HasBasis (fun ε : ℝ≥0∞ => 0 < ε) fun ε => eball x ε ∩ s :=
  nhdsWithin_hasBasis nhds_basis_eball s
/-
**Metric.nhds_basis_closedEBall** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：nhds_basis_closedEBall : (𝓝 x).HasBasis (fun ε : Real>=0∞ => 0 < ε) (close
dEBall x)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nhds_basis_uniformity`：nhds_basis_uniformity {p : ι -> Prop} {s : ι -> S
etRel α α} (h : (𝓤 α).HasBasis p s) {x : α} : (𝓝 x).HasBasis p fun i => { y | (y
, x) in s i…
· 使用定理 `uniformity_basis_edist_le`：uniformity_basis_edist_le : (𝓤 α).HasBasis (f
un ε : Real>=0∞ => 0 < ε) fun ε => { p : α × α | edist p.1 p.2 <= ε }
-/
theorem nhds_basis_closedEBall : (𝓝 x).HasBasis (fun ε : ℝ≥0∞ => 0 < ε) (closedEBall x) :=
  nhds_basis_uniformity uniformity_basis_edist_le
/-
**Metric.nhdsWithin_basis_closedEBall** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：nhdsWithin_basis_closedEBall : (𝓝[s] x).HasBasis (fun ε : Real>=0∞ => 0 < 
ε) fun ε => closedEBall x ε inter s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nhdsWithin_hasBasis`：nhdsWithin_hasBasis {ι : Sort*} {p : ι -> Prop} {s 
: ι -> Set α} {a : α} (h : (𝓝 a).HasBasis p s) (t : Set α) : (𝓝[t] a).HasBasis p
 fun i =>…
· 使用定理 `Metric.nhds_basis_closedEBall`：nhds_basis_closedEBall : (𝓝 x).HasBasis (
fun ε : Real>=0∞ => 0 < ε) (closedEBall x)
-/
theorem nhdsWithin_basis_closedEBall :
    (𝓝[s] x).HasBasis (fun ε : ℝ≥0∞ => 0 < ε) fun ε => closedEBall x ε ∩ s :=
  nhdsWithin_hasBasis nhds_basis_closedEBall s

end Metric

namespace EMetric
variable {x : α} {ε : ℝ≥0∞} {s t : Set α}

open Metric

/-
**EMetric.nhds_eq** 是 Mathlib 中的一个定理，位于命名空间 `EMetric`。
形式化陈述：nhds_eq : 𝓝 x = ⨅ ε > 0, 𝓟 (eball x ε)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.eq_biInf`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α}
 {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → l = ⨅ i, ⨅ (_ : p i), Filter
.principal (s …
· 使用定理 `Metric.nhds_basis_eball`：nhds_basis_eball : (𝓝 x).HasBasis (fun ε : Real
>=0∞ => 0 < ε) (eball x)
-/
theorem nhds_eq : 𝓝 x = ⨅ ε > 0, 𝓟 (eball x ε) :=
  nhds_basis_eball.eq_biInf
/-
**EMetric.mem_nhds_iff** 是 Mathlib 中的一个定理，位于命名空间 `EMetric`。
形式化陈述：mem_nhds_iff : s in 𝓝 x ↔ exists ε > 0, eball x ε subseteq s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `Metric.nhds_basis_eball`：nhds_basis_eball : (𝓝 x).HasBasis (fun ε : Real
>=0∞ => 0 < ε) (eball x)
-/
theorem mem_nhds_iff : s ∈ 𝓝 x ↔ ∃ ε > 0, eball x ε ⊆ s :=
  nhds_basis_eball.mem_iff
/-
**EMetric.mem_nhdsWithin_iff** 是 Mathlib 中的一个定理，位于命名空间 `EMetric`。
形式化陈述：mem_nhdsWithin_iff : s in 𝓝[t] x ↔ exists ε > 0, eball x ε inter t subsete
q s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `Metric.nhdsWithin_basis_eball`：nhdsWithin_basis_eball : (𝓝[s] x).HasBasi
s (fun ε : Real>=0∞ => 0 < ε) fun ε => eball x ε inter s
-/
theorem mem_nhdsWithin_iff : s ∈ 𝓝[t] x ↔ ∃ ε > 0, eball x ε ∩ t ⊆ s :=
  nhdsWithin_basis_eball.mem_iff
/-
**EMetric.isOpen_iff** 是 Mathlib 中的一个定理，位于命名空间 `EMetric`。
形式化陈述：isOpen_iff : IsOpen s ↔ forall x in s, exists ε > 0, eball x ε subseteq s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isOpen_iff : IsOpen s ↔ ∀ x ∈ s, ∃ ε > 0, eball x ε ⊆ s := by
  simp [isOpen_iff_nhds, mem_nhds_iff]

/-- ε-characterization of the closure in pseudoemetric spaces -/
/-
**EMetric.mem_closure_iff** 是 Mathlib 中的一个定理，位于命名空间 `EMetric`。
形式化陈述：mem_closure_iff : x in closure s ↔ forall ε > 0, exists y in s, edist x y 
< ε
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `mem_closure_iff_nhds_basis`：mem_closure_iff_nhds_basis {p : ι -> Prop} {
s : ι -> Set X} (h : (𝓝 x).HasBasis p s) : x in closure t ↔ forall i, p i -> exi
sts y in t, y in…
· 使用定理 `Metric.nhds_basis_eball`：nhds_basis_eball : (𝓝 x).HasBasis (fun ε : Real
>=0∞ => 0 < ε) (eball x)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `PseudoEMetricSpace.edist_comm`：∀ {α : Type u} [self : PseudoEMetricSpace
 α] (x y : α), edist x y = edist y x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
ε-characterization of the closure in pseudoemetric spaces
-/
theorem mem_closure_iff : x ∈ closure s ↔ ∀ ε > 0, ∃ y ∈ s, edist x y < ε :=
  (mem_closure_iff_nhds_basis nhds_basis_eball).trans <| by simp only [mem_eball, edist_comm x]
/-
**EMetric.dense_iff** 是 Mathlib 中的一个引理，位于命名空间 `EMetric`。
形式化陈述：dense_iff : Dense s ↔ forall (x : α), forall r > 0, (eball x r inter s).No
nempty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma dense_iff : Dense s ↔ ∀ (x : α), ∀ r > 0, (eball x r ∩ s).Nonempty :=
  forall_congr' fun x => by
    simp only [mem_closure_iff, Set.Nonempty, mem_inter_iff, and_comm, mem_eball']
/-
**EMetric.tendsto_nhds** 是 Mathlib 中的一个定理，位于命名空间 `EMetric`。
形式化陈述：tendsto_nhds {f : Filter β} {u : β -> α} {a : α} : Tendsto u f (𝓝 a) ↔ for
all ε > 0, forallᶠ x in f, edist (u x) a < ε
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.tendsto_right_iff`：∀ {α : Type u_1} {β : Type u_2} {ι' :
 Sort u_5} {la : Filter α} {lb : Filter β} {pb : ι' → Prop} {sb : ι' → Set β}   
{f : α → β}, lb.HasBasi…
· 使用定理 `Metric.nhds_basis_eball`：nhds_basis_eball : (𝓝 x).HasBasis (fun ε : Real
>=0∞ => 0 < ε) (eball x)
-/
theorem tendsto_nhds {f : Filter β} {u : β → α} {a : α} :
    Tendsto u f (𝓝 a) ↔ ∀ ε > 0, ∀ᶠ x in f, edist (u x) a < ε :=
  nhds_basis_eball.tendsto_right_iff
/-
**EMetric.tendsto_atTop** 是 Mathlib 中的一个定理，位于命名空间 `EMetric`。
形式化陈述：tendsto_atTop [Nonempty β] [SemilatticeSup β] {u : β -> α} {a : α} : Tends
to u atTop (𝓝 a) ↔ forall ε > 0, exists N, forall n >= N, edist (u n) a < ε
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Filter.HasBasis.tendsto_iff`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u
_4} {ι' : Sort u_5} {la : Filter α} {pa : ι → Prop} {sa : ι → Set α}   {lb : Fil
ter β} {pb : ι' →…
· 使用定理 `Filter.atTop_basis`：atTop_basis [Nonempty α] : (@atTop α _).HasBasis (fu
n _ => True) Ici
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `Metric.nhds_basis_eball`：nhds_basis_eball : (𝓝 x).HasBasis (fun ε : Real
>=0∞ => 0 < ε) (eball x)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem tendsto_atTop [Nonempty β] [SemilatticeSup β] {u : β → α} {a : α} :
    Tendsto u atTop (𝓝 a) ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, edist (u n) a < ε :=
  (atTop_basis.tendsto_iff nhds_basis_eball).trans <| by
    simp only [true_and, mem_Ici, mem_eball]

section

variable [PseudoEMetricSpace β] {f : α → β}

/-
**EMetric.tendsto_nhdsWithin_nhdsWithin** 是 Mathlib 中的一个定理，位于命名空间 `EMetric`。
形式化陈述：tendsto_nhdsWithin_nhdsWithin {t : Set β} {a b} : Tendsto f (𝓝[s] a) (𝓝[t]
 b) ↔ forall ε > 0, exists δ > 0, forall ⦃x⦄, x in s -> edist x a < δ -> f x in 
t ∧ edist (f x) b < ε
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Filter.HasBasis.tendsto_iff`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u
_4} {ι' : Sort u_5} {la : Filter α} {pa : ι → Prop} {sa : ι → Set α}   {lb : Fil
ter β} {pb : ι' →…
· 使用定理 `Metric.nhdsWithin_basis_eball`：nhdsWithin_basis_eball : (𝓝[s] x).HasBasi
s (fun ε : Real>=0∞ => 0 < ε) fun ε => eball x ε inter s
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `and_congr_right`：∀ {a b c : Prop}, (a → (b ↔ c)) → (a ∧ b ↔ a ∧ c)
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Decidable.not_or_of_imp`：∀ {a b : Prop} [Decidable a], (a → b) → ¬a ∨ b
-/
theorem tendsto_nhdsWithin_nhdsWithin {t : Set β} {a b} :
    Tendsto f (𝓝[s] a) (𝓝[t] b) ↔
      ∀ ε > 0, ∃ δ > 0, ∀ ⦃x⦄, x ∈ s → edist x a < δ → f x ∈ t ∧ edist (f x) b < ε :=
  (nhdsWithin_basis_eball.tendsto_iff nhdsWithin_basis_eball).trans <|
    forall₂_congr fun ε _ => exists_congr fun δ => and_congr_right fun _ =>
      forall_congr' fun x => by simp; tauto
/-
**EMetric.tendsto_nhdsWithin_nhds** 是 Mathlib 中的一个定理，位于命名空间 `EMetric`。
形式化陈述：tendsto_nhdsWithin_nhds {a b} : Tendsto f (𝓝[s] a) (𝓝 b) ↔ forall ε > 0, e
xists δ > 0, forall {x : α}, x in s -> edist x a < δ -> edist (f x) b < ε
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nhdsWithin_univ`：∀ {α : Type u_1} [inst : TopologicalSpace α] (a : α), n
hdsWithin a Set.univ = nhds a
· 使用定理 `EMetric.tendsto_nhdsWithin_nhdsWithin`：tendsto_nhdsWithin_nhdsWithin {t 
: Set β} {a b} : Tendsto f (𝓝[s] a) (𝓝[t] b) ↔ forall ε > 0, exists δ > 0, foral
l ⦃x⦄, x in s -> edist x a …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem tendsto_nhdsWithin_nhds {a b} :
    Tendsto f (𝓝[s] a) (𝓝 b) ↔
      ∀ ε > 0, ∃ δ > 0, ∀ {x : α}, x ∈ s → edist x a < δ → edist (f x) b < ε := by
  rw [← nhdsWithin_univ b, tendsto_nhdsWithin_nhdsWithin]
  simp only [mem_univ, true_and]
/-
**EMetric.tendsto_nhds_nhds** 是 Mathlib 中的一个定理，位于命名空间 `EMetric`。
形式化陈述：tendsto_nhds_nhds {a b} : Tendsto f (𝓝 a) (𝓝 b) ↔ forall ε > 0, exists δ >
 0, forall ⦃x⦄, edist x a < δ -> edist (f x) b < ε
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.tendsto_iff`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u
_4} {ι' : Sort u_5} {la : Filter α} {pa : ι → Prop} {sa : ι → Set α}   {lb : Fil
ter β} {pb : ι' →…
· 使用定理 `Metric.nhds_basis_eball`：nhds_basis_eball : (𝓝 x).HasBasis (fun ε : Real
>=0∞ => 0 < ε) (eball x)
-/
theorem tendsto_nhds_nhds {a b} :
    Tendsto f (𝓝 a) (𝓝 b) ↔ ∀ ε > 0, ∃ δ > 0, ∀ ⦃x⦄, edist x a < δ → edist (f x) b < ε :=
  nhds_basis_eball.tendsto_iff nhds_basis_eball
/-
**EMetric.continuousAt_iff** 是 Mathlib 中的一个定理，位于命名空间 `EMetric`。
形式化陈述：continuousAt_iff {a} : ContinuousAt f a ↔ forall ε > 0, exists δ > 0, fora
ll ⦃x : α⦄, edist x a < δ -> edist (f x) (f a) < ε
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousAt.eq_1`：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSp
ace X] [inst_1 : TopologicalSpace Y] (f : X → Y) (x : X),   ContinuousAt f x = F
ilter.T…
· 使用定理 `EMetric.tendsto_nhds_nhds`：tendsto_nhds_nhds {a b} : Tendsto f (𝓝 a) (𝓝 
b) ↔ forall ε > 0, exists δ > 0, forall ⦃x⦄, edist x a < δ -> edist (f x) b < ε
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem continuousAt_iff {a} :
    ContinuousAt f a ↔ ∀ ε > 0, ∃ δ > 0, ∀ ⦃x : α⦄, edist x a < δ → edist (f x) (f a) < ε := by
  rw [ContinuousAt, tendsto_nhds_nhds]
/-
**EMetric.continuousWithinAt_iff** 是 Mathlib 中的一个定理，位于命名空间 `EMetric`。
形式化陈述：continuousWithinAt_iff {a s} : ContinuousWithinAt f s a ↔ forall ε > 0, ex
ists δ > 0, forall ⦃x : α⦄, x in s -> edist x a < δ -> edist (f x) (f a) < ε
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousWithinAt.eq_1`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolog
icalSpace X] [inst_1 : TopologicalSpace Y] (f : X → Y) (s : Set X)   (x : X), Co
ntinuousWithi…
· 使用定理 `EMetric.tendsto_nhdsWithin_nhds`：tendsto_nhdsWithin_nhds {a b} : Tendsto
 f (𝓝[s] a) (𝓝 b) ↔ forall ε > 0, exists δ > 0, forall {x : α}, x in s -> edist 
x a < δ -> edist (f x…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem continuousWithinAt_iff {a s} :
    ContinuousWithinAt f s a ↔
      ∀ ε > 0, ∃ δ > 0, ∀ ⦃x : α⦄, x ∈ s → edist x a < δ → edist (f x) (f a) < ε := by
  rw [ContinuousWithinAt, tendsto_nhdsWithin_nhds]
/-
**EMetric.continuousOn_iff** 是 Mathlib 中的一个定理，位于命名空间 `EMetric`。
形式化陈述：continuousOn_iff {s} : ContinuousOn f s ↔ forall b in s, forall ε > 0, exi
sts δ > 0, forall a in s, edist a b < δ -> edist (f a) (f b) < ε
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem continuousOn_iff {s} :
    ContinuousOn f s ↔
      ∀ b ∈ s, ∀ ε > 0, ∃ δ > 0, ∀ a ∈ s, edist a b < δ → edist (f a) (f b) < ε := by
  simp [ContinuousOn, continuousWithinAt_iff]
/-
**EMetric.continuous_iff** 是 Mathlib 中的一个定理，位于命名空间 `EMetric`。
形式化陈述：continuous_iff : Continuous f ↔ forall b, forall ε > 0, exists δ > 0, fora
ll a, edist a b < δ -> edist (f a) (f b) < ε
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `continuous_iff_continuousAt`：continuous_iff_continuousAt : Continuous f 
↔ forall x, ContinuousAt f x
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `EMetric.tendsto_nhds_nhds`：tendsto_nhds_nhds {a b} : Tendsto f (𝓝 a) (𝓝 
b) ↔ forall ε > 0, exists δ > 0, forall ⦃x⦄, edist x a < δ -> edist (f x) b < ε
-/
theorem continuous_iff :
    Continuous f ↔ ∀ b, ∀ ε > 0, ∃ δ > 0, ∀ a, edist a b < δ → edist (f a) (f b) < ε :=
  continuous_iff_continuousAt.trans <| forall_congr' fun _ ↦ tendsto_nhds_nhds

end

section

variable [TopologicalSpace β] {f : β → α}

/-
**EMetric.continuousAt_iff'** 是 Mathlib 中的一个定理，位于命名空间 `EMetric`。
形式化陈述：continuousAt_iff' {b} : ContinuousAt f b ↔ forall ε > 0, forallᶠ x in 𝓝 b,
 edist (f x) (f b) < ε
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousAt.eq_1`：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSp
ace X] [inst_1 : TopologicalSpace Y] (f : X → Y) (x : X),   ContinuousAt f x = F
ilter.T…
· 使用定理 `EMetric.tendsto_nhds`：tendsto_nhds {f : Filter β} {u : β -> α} {a : α} :
 Tendsto u f (𝓝 a) ↔ forall ε > 0, forallᶠ x in f, edist (u x) a < ε
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem continuousAt_iff' {b} :
    ContinuousAt f b ↔ ∀ ε > 0, ∀ᶠ x in 𝓝 b, edist (f x) (f b) < ε := by
  rw [ContinuousAt, tendsto_nhds]
/-
**EMetric.continuousWithinAt_iff'** 是 Mathlib 中的一个定理，位于命名空间 `EMetric`。
形式化陈述：continuousWithinAt_iff' {b s} : ContinuousWithinAt f s b ↔ forall ε > 0, f
orallᶠ x in 𝓝[s] b, edist (f x) (f b) < ε
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousWithinAt.eq_1`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolog
icalSpace X] [inst_1 : TopologicalSpace Y] (f : X → Y) (s : Set X)   (x : X), Co
ntinuousWithi…
· 使用定理 `EMetric.tendsto_nhds`：tendsto_nhds {f : Filter β} {u : β -> α} {a : α} :
 Tendsto u f (𝓝 a) ↔ forall ε > 0, forallᶠ x in f, edist (u x) a < ε
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem continuousWithinAt_iff' {b s} :
    ContinuousWithinAt f s b ↔ ∀ ε > 0, ∀ᶠ x in 𝓝[s] b, edist (f x) (f b) < ε := by
  rw [ContinuousWithinAt, tendsto_nhds]
/-
**EMetric.continuousOn_iff'** 是 Mathlib 中的一个定理，位于命名空间 `EMetric`。
形式化陈述：continuousOn_iff' {s} : ContinuousOn f s ↔ forall b in s, forall ε > 0, fo
rallᶠ x in 𝓝[s] b, edist (f x) (f b) < ε
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem continuousOn_iff' {s} :
    ContinuousOn f s ↔ ∀ b ∈ s, ∀ ε > 0, ∀ᶠ x in 𝓝[s] b, edist (f x) (f b) < ε := by
  simp [ContinuousOn, continuousWithinAt_iff']
/-
**EMetric.continuous_iff'** 是 Mathlib 中的一个定理，位于命名空间 `EMetric`。
形式化陈述：continuous_iff' : Continuous f ↔ forall a, forall ε > 0, forallᶠ x in 𝓝 a,
 edist (f x) (f a) < ε
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `continuous_iff_continuousAt`：continuous_iff_continuousAt : Continuous f 
↔ forall x, ContinuousAt f x
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `EMetric.tendsto_nhds`：tendsto_nhds {f : Filter β} {u : β -> α} {a : α} :
 Tendsto u f (𝓝 a) ↔ forall ε > 0, forallᶠ x in f, edist (u x) a < ε
-/
theorem continuous_iff' :
    Continuous f ↔ ∀ a, ∀ ε > 0, ∀ᶠ x in 𝓝 a, edist (f x) (f a) < ε :=
  continuous_iff_continuousAt.trans <| forall_congr' fun _ ↦ tendsto_nhds

end

end EMetric

namespace Metric
variable {x : α} {ε : ℝ≥0∞} {s t : Set α}

/-
**Metric.isOpen_eball** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：∀ {α : Type u} [inst : PseudoEMetricSpace α] {x : α} {ε : ENNReal}, IsOpen
 (Metric.eball x ε)
参数：Metric.eball x ε。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `EMetric.isOpen_iff`：isOpen_iff : IsOpen s ↔ forall x in s, exists ε > 0,
 eball x ε subseteq s
· 使用定理 `Metric.exists_eball_subset_eball`：exists_eball_subset_eball (h : y in eb
all x ε) : exists ε' > 0, eball y ε' subseteq eball x ε
-/
@[simp] theorem isOpen_eball : IsOpen (eball x ε) :=
  EMetric.isOpen_iff.2 fun _ => exists_eball_subset_eball
/-
**Metric.isClosed_eball_top** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：isClosed_eball_top : IsClosed (eball x ⊤)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isOpen_compl_iff`：∀ {X : Type u} {s : Set X} [inst : TopologicalSpace X]
, IsOpen sᶜ ↔ IsClosed s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `EMetric.isOpen_iff`：isOpen_iff : IsOpen s ↔ forall x in s, exists ε > 0,
 eball x ε subseteq s
· 使用定理 `ENNReal.coe_lt_top`：∀ {r : NNReal}, ↑r < ⊤
· 使用定理 `Setoid.trans`：∀ {α : Sort u} [inst : Setoid α] {a b c : α}, a ≈ b → b ≈ 
c → a ≈ c
· 使用定理 `Setoid.symm`：∀ {α : Sort u} [inst : Setoid α] {a b : α}, a ≈ b → b ≈ a
-/
theorem isClosed_eball_top : IsClosed (eball x ⊤) :=
  isOpen_compl_iff.1 <| EMetric.isOpen_iff.2 fun _y hy =>
    ⟨⊤, ENNReal.coe_lt_top, fun _z hzy hzx =>
      hy (edistLtTopSetoid.trans (edistLtTopSetoid.symm hzy) hzx)⟩
/-
**Metric.eball_mem_nhds** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：eball_mem_nhds (x : α) {ε : Real>=0∞} (ε0 : 0 < ε) : eball x ε in 𝓝 x
参数：x : α；ε0 : 0 < ε。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `Metric.isOpen_eball`：∀ {α : Type u} [inst : PseudoEMetricSpace α] {x : α
} {ε : ENNReal}, IsOpen (Metric.eball x ε)
· 使用定理 `Metric.mem_eball_self`：mem_eball_self (h : 0 < ε) : x in eball x ε
-/
theorem eball_mem_nhds (x : α) {ε : ℝ≥0∞} (ε0 : 0 < ε) : eball x ε ∈ 𝓝 x :=
  isOpen_eball.mem_nhds (mem_eball_self ε0)
/-
**Metric.closedEBall_mem_nhds** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：closedEBall_mem_nhds (x : α) {ε : Real>=0∞} (ε0 : 0 < ε) : closedEBall x ε
 in 𝓝 x
参数：x : α；ε0 : 0 < ε。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Metric.eball_mem_nhds`：eball_mem_nhds (x : α) {ε : Real>=0∞} (ε0 : 0 < ε
) : eball x ε in 𝓝 x
· 使用定理 `Metric.eball_subset_closedEBall`：eball_subset_closedEBall : eball x ε su
bseteq closedEBall x ε
-/
theorem closedEBall_mem_nhds (x : α) {ε : ℝ≥0∞} (ε0 : 0 < ε) : closedEBall x ε ∈ 𝓝 x :=
  mem_of_superset (eball_mem_nhds x ε0) eball_subset_closedEBall
/-
**Metric.eball_prod_same** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：eball_prod_same [PseudoEMetricSpace β] (x : α) (y : β) (r : Real>=0∞) : eb
all x r ×ˢ eball y r = eball (x, y) r
参数：x : α；y : β；r : Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem eball_prod_same [PseudoEMetricSpace β] (x : α) (y : β) (r : ℝ≥0∞) :
    eball x r ×ˢ eball y r = eball (x, y) r :=
  ext fun z => by simp [Prod.edist_eq]
/-
**Metric.closedEBall_prod_same** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：closedEBall_prod_same [PseudoEMetricSpace β] (x : α) (y : β) (r : Real>=0∞
) : closedEBall x r ×ˢ closedEBall y r = closedEBall (x, y) r
参数：x : α；y : β；r : Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem closedEBall_prod_same [PseudoEMetricSpace β] (x : α) (y : β) (r : ℝ≥0∞) :
    closedEBall x r ×ˢ closedEBall y r = closedEBall (x, y) r :=
  ext fun z => by simp [Prod.edist_eq]

end Metric

namespace EMetric

open Metric

@[deprecated (since := "2026-01-24")] alias ball := eball
@[deprecated (since := "2026-01-24")] alias mem_ball := mem_eball
@[deprecated (since := "2026-01-24")] alias mem_ball' := mem_eball'
@[deprecated (since := "2026-01-24")] alias closedBall := closedEBall
@[deprecated (since := "2026-01-24")] alias mem_closedBall := mem_closedEBall
@[deprecated (since := "2026-01-24")] alias mem_closedBall' := mem_closedEBall'
@[deprecated (since := "2026-01-24")] alias closedBall_top := closedEBall_top
@[deprecated (since := "2026-01-24")] alias ball_subset_closedBall := eball_subset_closedEBall
@[deprecated (since := "2026-01-24")] alias pos_of_mem_ball := pos_of_mem_eball
@[deprecated (since := "2026-01-24")] alias mem_ball_self := mem_eball_self
@[deprecated (since := "2026-01-24")] alias mem_closedBall_self := mem_closedEBall_self
@[deprecated (since := "2026-01-24")] alias mem_ball_comm := mem_eball_comm
@[deprecated (since := "2026-01-24")] alias mem_closedBall_comm := mem_closedEBall_comm
@[deprecated (since := "2026-01-24")] alias ball_subset_ball := eball_subset_eball

@[deprecated (since := "2026-01-24")]
alias closedBall_subset_closedBall := closedEBall_subset_closedEBall

@[deprecated (since := "2026-01-24")] alias ball_disjoint := eball_disjoint
@[deprecated (since := "2026-01-24")] alias ball_subset := eball_subset
@[deprecated (since := "2026-01-24")] alias exists_ball_subset_ball := exists_eball_subset_eball
@[deprecated (since := "2026-01-24")] alias ball_eq_empty_iff := eball_eq_empty_iff

@[deprecated (since := "2026-01-24")]
alias ordConnected_setOf_closedBall_subset := ordConnected_setOfPred_closedEBall_subset

@[deprecated (since := "2026-01-24")]
alias ordConnected_setOf_ball_subset := ordConnected_setOfPred_eball_subset

@[deprecated (since := "2026-01-24")] alias edistLtTopSetoid := edistLtTopSetoid
@[deprecated (since := "2026-01-24")] alias ball_zero := eball_zero

@[deprecated (since := "2026-01-24")]
protected alias nhds_basis_eball := nhds_basis_eball

@[deprecated (since := "2026-01-24")] alias nhdsWithin_basis_eball := nhdsWithin_basis_eball
@[deprecated (since := "2026-01-24")] alias nhds_basis_closed_eball := nhds_basis_closedEBall

@[deprecated (since := "2026-01-24")]
alias nhdsWithin_basis_closed_eball := nhdsWithin_basis_closedEBall

@[deprecated (since := "2026-01-24")] alias isOpen_ball := isOpen_eball
@[deprecated (since := "2026-01-24")] alias isClosed_ball_top := isClosed_eball_top
@[deprecated (since := "2026-01-24")] alias ball_mem_nhds := eball_mem_nhds
@[deprecated (since := "2026-01-24")] alias closedBall_mem_nhds := closedEBall_mem_nhds
@[deprecated (since := "2026-01-24")] alias ball_prod_same := eball_prod_same
@[deprecated (since := "2026-01-24")] alias closedBall_prod_same := closedEBall_prod_same

end EMetric

namespace Subtype

open Metric

@[simp]
/-
**Subtype.preimage_eball** 是 Mathlib 中的一个定理，位于命名空间 `Subtype`。
形式化陈述：preimage_eball {p : α -> Prop} (a : {a // p a}) (r : Real>=0∞) : Subtype.v
al ⁻¹' (eball a.1 r) = eball a r
参数：a : {a // p a}；r : Real>=0∞。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem preimage_eball {p : α → Prop} (a : {a // p a}) (r : ℝ≥0∞) :
    Subtype.val ⁻¹' (eball a.1 r) = eball a r :=
  rfl

@[deprecated (since := "2026-01-24")]
alias preimage_emetricBall := preimage_eball

@[simp]
/-
**Subtype.preimage_closedEBall** 是 Mathlib 中的一个定理，位于命名空间 `Subtype`。
形式化陈述：preimage_closedEBall {p : α -> Prop} (a : {a // p a}) (r : Real>=0∞) : Sub
type.val ⁻¹' (closedEBall a.1 r) = closedEBall a r
参数：a : {a // p a}；r : Real>=0∞。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem preimage_closedEBall {p : α → Prop} (a : {a // p a}) (r : ℝ≥0∞) :
    Subtype.val ⁻¹' (closedEBall a.1 r) = closedEBall a r :=
  rfl

@[deprecated (since := "2026-01-24")]
alias preimage_emetricClosedBall := preimage_closedEBall

@[simp]
/-
**Subtype.image_eball** 是 Mathlib 中的一个定理，位于命名空间 `Subtype`。
形式化陈述：image_eball {p : α -> Prop} (a : {a // p a}) (r : Real>=0∞) : Subtype.val 
'' (eball a r) = eball a.1 r inter {a | p a}
参数：a : {a // p a}；r : Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.preimage_eball`：preimage_eball {p : α -> Prop} (a : {a // p a}) 
(r : Real>=0∞) : Subtype.val ⁻¹' (eball a.1 r) = eball a r
· 使用定理 `Set.image_preimage_eq_inter_range`：image_preimage_eq_inter_range {f : α 
-> β} {t : Set β} : f '' f ⁻¹' t = t inter range f
· 使用定理 `Subtype.range_val_subtype`：range_val_subtype {p : α -> Prop} : range (Su
btype.val : Subtype p -> α) = { x | p x }
-/
theorem image_eball {p : α → Prop} (a : {a // p a}) (r : ℝ≥0∞) :
    Subtype.val '' (eball a r) = eball a.1 r ∩ {a | p a} := by
  rw [← preimage_eball, image_preimage_eq_inter_range, range_val_subtype]

@[deprecated (since := "2026-01-24")]
alias image_emetricBall := image_eball

@[simp]
/-
**Subtype.image_closedEBall** 是 Mathlib 中的一个定理，位于命名空间 `Subtype`。
形式化陈述：image_closedEBall {p : α -> Prop} (a : {a // p a}) (r : Real>=0∞) : Subtyp
e.val '' (closedEBall a r) = closedEBall a.1 r inter {a | p a}
参数：a : {a // p a}；r : Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.preimage_closedEBall`：preimage_closedEBall {p : α -> Prop} (a : 
{a // p a}) (r : Real>=0∞) : Subtype.val ⁻¹' (closedEBall a.1 r) = closedEBall a
 r
· 使用定理 `Set.image_preimage_eq_inter_range`：image_preimage_eq_inter_range {f : α 
-> β} {t : Set β} : f '' f ⁻¹' t = t inter range f
· 使用定理 `Subtype.range_val_subtype`：range_val_subtype {p : α -> Prop} : range (Su
btype.val : Subtype p -> α) = { x | p x }
-/
theorem image_closedEBall {p : α → Prop} (a : {a // p a}) (r : ℝ≥0∞) :
    Subtype.val '' (closedEBall a r) = closedEBall a.1 r ∩ {a | p a} := by
  rw [← preimage_closedEBall, image_preimage_eq_inter_range, range_val_subtype]

@[deprecated (since := "2026-01-24")]
alias image_emetricClosedBall := image_closedEBall

end Subtype

/-- An extended metric space is a type endowed with a `ℝ≥0∞`-valued distance `edist` satisfying
`edist x y = 0 ↔ x = y`, commutativity `edist x y = edist y x`, and the triangle inequality
`edist x z ≤ edist x y + edist y z`.

See pseudo extended metric spaces (`PseudoEMetricSpace`) for the similar class with the
`edist x y = 0 ↔ x = y` assumption weakened to `edist x x = 0`.

Any extended metric space is a T1 topological space and a uniform space (see `TopologicalSpace`,
`T1Space`, `UniformSpace`), where the topology and uniformity come from the metric.

We make the uniformity/topology part of the data instead of deriving it from the metric.
This e.g. ensures that we do not get a diamond when doing
`[EMetricSpace α] [EMetricSpace β] : TopologicalSpace (α × β)`:
The product metric and product topology agree, but not definitionally so.
See Note [forgetful inheritance]. -/
/-
**EMetricSpace** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An extended metric space is a type endowed with a `ℝ≥0∞`-valued distance `edist`
 satisfying
`edist x y = 0 ↔ x = y`, commutativity `edist x y = edist y x`, and the triangle
 inequality
`edist x z ≤ edist x y + edist y z`.

See pseudo extended metric spaces (`PseudoEMetricSpace`) for the similar class w
ith the
`edist x y = 0 ↔ x = y` assumption weakened to `edist x x = 0`.

Any extended metric space is a T1 topological space and a uniform space (see `To
pologicalSpace`,
`T1Space`, `UniformSpace`), where the topology and uniformity come from the metr
ic.

We make the uniformity/topology part of the data instead of deriving it from the
 metric.
This e.g. ensures that we do not get a diamond when doing
`[EMetricSpace α] [EMetricSpace β] : TopologicalSpace (α × β)`:
The product metric and product topology agree, but not definitionally so.
See Note [forgetful inheritance].
-/
class EMetricSpace (α : Type u) : Type u extends PseudoEMetricSpace α where
  eq_of_edist_eq_zero : ∀ {x y : α}, edist x y = 0 → x = y

@[ext]
/-
**EMetricSpace.ext** 是 Mathlib 中的一个定理，位于命名空间 `EMetricSpace`。
形式化陈述：∀ {α : Type u_2} {m m' : EMetricSpace α}, m.toEDist = m'.toEDist → m = m'
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PseudoEMetricSpace.ext`：∀ {α : Type u_2} {m m' : PseudoEMetricSpace α}, 
m.toEDist = m'.toEDist → m = m'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
protected theorem EMetricSpace.ext
    {α : Type*} {m m' : EMetricSpace α} (h : m.toEDist = m'.toEDist) : m = m' := by
  cases m
  cases m'
  congr
  ext1
  assumption

variable {γ : Type w} [EMetricSpace γ]

export EMetricSpace (eq_of_edist_eq_zero)

/-- Characterize the equality of points by the vanishing of their extended distance -/
@[simp]
/-
**edist_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：edist_eq_zero {x y : γ} : edist x y = 0 ↔ x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EMetricSpace.eq_of_edist_eq_zero`：∀ {α : Type u} [self : EMetricSpace α]
 {x y : α}, edist x y = 0 → x = y
· 使用定理 `PseudoEMetricSpace.edist_self`：∀ {α : Type u} [self : PseudoEMetricSpace
 α] (x : α), edist x x = 0

--- 原说明 ---
Characterize the equality of points by the vanishing of their extended distance
-/
theorem edist_eq_zero {x y : γ} : edist x y = 0 ↔ x = y :=
  ⟨eq_of_edist_eq_zero, fun h => h ▸ edist_self _⟩

@[simp]
/-
**zero_eq_edist** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：zero_eq_edist {x y : γ} : 0 = edist x y ↔ x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `edist_eq_zero`：edist_eq_zero {x y : γ} : edist x y = 0 ↔ x = y
-/
theorem zero_eq_edist {x y : γ} : 0 = edist x y ↔ x = y := eq_comm.trans edist_eq_zero
/-
**edist_le_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：edist_le_zero {x y : γ} : edist x y <= 0 ↔ x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `nonpos_iff_eq_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [in
st_1 : Zero α] [IsBotZeroClass α], a ≤ 0 ↔ a = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `edist_eq_zero`：edist_eq_zero {x y : γ} : edist x y = 0 ↔ x = y
-/
theorem edist_le_zero {x y : γ} : edist x y ≤ 0 ↔ x = y :=
  nonpos_iff_eq_zero.trans edist_eq_zero

@[simp]
/-
**edist_pos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：edist_pos {x y : γ} : 0 < edist x y ↔ x != y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem edist_pos {x y : γ} : 0 < edist x y ↔ x ≠ y := by simp [← not_le]
/-
**Metric.closedEBall_zero** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：∀ {γ : Type w} [inst : EMetricSpace γ] (x : γ), Metric.closedEBall x 0 = {
x}
参数：x : γ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma Metric.closedEBall_zero (x : γ) : closedEBall x 0 = {x} := by ext; simp

@[deprecated (since := "2026-01-24")]
alias EMetric.closedBall_zero := Metric.closedEBall_zero

/-- Two points coincide if their distance is `< ε` for all positive ε -/
/-
**eq_of_forall_edist_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_of_forall_edist_le {x y : γ} (h : forall ε > 0, edist x y <= ε) : x = y
参数：h : forall ε > 0, edist x y <= ε。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EMetricSpace.eq_of_edist_eq_zero`：∀ {α : Type u} [self : EMetricSpace α]
 {x y : α}, edist x y = 0 → x = y
· 使用引理 `eq_of_le_of_forall_lt_imp_le_of_dense`：eq_of_le_of_forall_lt_imp_le_of_d
ense (h₁ : a₂ <= a₁) (h₂ : forall a, a₂ < a -> a₁ <= a) : a₁ = a₂
· 使用定理 `ENNReal.instDenselyOrdered`：DenselyOrdered ENNReal
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a

--- 原说明 ---
Two points coincide if their distance is `< ε` for all positive ε
-/
theorem eq_of_forall_edist_le {x y : γ} (h : ∀ ε > 0, edist x y ≤ ε) : x = y :=
  eq_of_edist_eq_zero (eq_of_le_of_forall_lt_imp_le_of_dense bot_le h)

/-- Auxiliary function to replace the uniformity on an emetric space with
a uniformity which is equal to the original one, but maybe not defeq.
This is useful if one wants to construct an emetric space with a
specified uniformity. See Note [forgetful inheritance] explaining why having definitionally
the right uniformity is often important.
See note [reducible non-instances].
-/
/-
**EMetricSpace.replaceUniformity** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：EMetricSpace.replaceUniformity {γ} [U : UniformSpace γ] (m : EMetricSpace 
γ) (H : 𝓤[U] = 𝓤[PseudoEMetricSpace.toUniformSpace]) : EMetricSpace γ where edis
t
参数：m : EMetricSpace γ；H : 𝓤[U] = 𝓤[PseudoEMetricSpace.toUniformSpace]。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `EMetricSpace.eq_of_edist_eq_zero`：∀ {α : Type u} [self : EMetricSpace α]
 {x y : α}, edist x y = 0 → x = y

--- 原说明 ---
Auxiliary function to replace the uniformity on an emetric space with
a uniformity which is equal to the original one, but maybe not defeq.
This is useful if one wants to construct an emetric space with a
specified uniformity. See Note [forgetful inheritance] explaining why having def
initionally
the right uniformity is often important.
See note [reducible non-instances].
-/
abbrev EMetricSpace.replaceUniformity {γ} [U : UniformSpace γ] (m : EMetricSpace γ)
    (H : 𝓤[U] = 𝓤[PseudoEMetricSpace.toUniformSpace]) : EMetricSpace γ where
  edist := @edist _ m.toEDist
  edist_self := edist_self
  eq_of_edist_eq_zero := @eq_of_edist_eq_zero _ _
  edist_comm := edist_comm
  edist_triangle := edist_triangle
  toUniformSpace := U
  uniformity_edist := H.trans (@PseudoEMetricSpace.uniformity_edist γ _)

/-- Auxiliary function to replace the topology on an emetric space with
a topology which is equal to the original one, but maybe not defeq.
This is useful if one wants to construct an emetric space with a
specified topology. See Note [forgetful inheritance] explaining why having definitionally
the right topology is often important.
See note [reducible non-instances].
-/
/-
**EMetricSpace.replaceTopology** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：EMetricSpace.replaceTopology {γ} [T : TopologicalSpace γ] (m : EMetricSpac
e γ) (H : T = m.toUniformSpace.toTopologicalSpace) : EMetricSpace γ where edist
参数：m : EMetricSpace γ；H : T = m.toUniformSpace.toTopologicalSpace。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `EMetricSpace.eq_of_edist_eq_zero`：∀ {α : Type u} [self : EMetricSpace α]
 {x y : α}, edist x y = 0 → x = y

--- 原说明 ---
Auxiliary function to replace the topology on an emetric space with
a topology which is equal to the original one, but maybe not defeq.
This is useful if one wants to construct an emetric space with a
specified topology. See Note [forgetful inheritance] explaining why having defin
itionally
the right topology is often important.
See note [reducible non-instances].
-/
abbrev EMetricSpace.replaceTopology {γ} [T : TopologicalSpace γ] (m : EMetricSpace γ)
    (H : T = m.toUniformSpace.toTopologicalSpace) : EMetricSpace γ where
  edist := @edist _ m.toEDist
  edist_self := edist_self
  eq_of_edist_eq_zero := @eq_of_edist_eq_zero _ _
  edist_comm := edist_comm
  edist_triangle := edist_triangle
  toUniformSpace := m.toUniformSpace.replaceTopology H
  uniformity_edist := PseudoEMetricSpace.uniformity_edist

/-- The extended metric induced by an injective function taking values in an emetric space.
See Note [reducible non-instances]. -/
/-
**EMetricSpace.induced** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：EMetricSpace.induced {γ β} (f : γ -> β) (hf : Function.Injective f) (m : E
MetricSpace β) : EMetricSpace γ
参数：f : γ -> β；hf : Function.Injective f；m : EMetricSpace β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The extended metric induced by an injective function taking values in an emetric
 space.
See Note [reducible non-instances].
-/
abbrev EMetricSpace.induced {γ β} (f : γ → β) (hf : Function.Injective f) (m : EMetricSpace β) :
    EMetricSpace γ :=
  { PseudoEMetricSpace.induced f m.toPseudoEMetricSpace with
    eq_of_edist_eq_zero := fun h => hf (edist_eq_zero.1 h) }

/-- EMetric space instance on subsets of emetric spaces -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
EMetric space instance on subsets of emetric spaces
-/
instance {α : Type*} {p : α → Prop} [EMetricSpace α] : EMetricSpace (Subtype p) :=
  EMetricSpace.induced Subtype.val Subtype.coe_injective ‹_›

/-- EMetric space instance on the multiplicative opposite of an emetric space. -/
@[to_additive /-- EMetric space instance on the additive opposite of an emetric space. -/]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
EMetric space instance on the multiplicative opposite of an emetric space.
-/
instance {α : Type*} [EMetricSpace α] : EMetricSpace αᵐᵒᵖ :=
  EMetricSpace.induced MulOpposite.unop MulOpposite.unop_injective ‹_›
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {α : Type*} [EMetricSpace α] : EMetricSpace (ULift α) :=
  EMetricSpace.induced ULift.down ULift.down_injective ‹_›

/-- Reformulation of the uniform structure in terms of the extended distance -/
/-
**uniformity_edist** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniformity_edist : 𝓤 γ = ⨅ ε > 0, 𝓟 { p : γ × γ | edist p.1 p.2 < ε }
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PseudoEMetricSpace.uniformity_edist`：∀ {α : Type u} [self : PseudoEMetri
cSpace α],   uniformity α = ⨅ ε, ⨅ (_ : ε > 0), Filter.principal {p | edist p.1 
p.2 < ε}

--- 原说明 ---
Reformulation of the uniform structure in terms of the extended distance
-/
theorem uniformity_edist : 𝓤 γ = ⨅ ε > 0, 𝓟 { p : γ × γ | edist p.1 p.2 < ε } :=
  PseudoEMetricSpace.uniformity_edist

/-!
### `Additive`, `Multiplicative`

The distance on those type synonyms is inherited without change.
-/


open Additive Multiplicative

section

variable [EDist X]

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : EDist (Additive X) := ‹EDist X›
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : EDist (Multiplicative X) := ‹EDist X›

@[simp]
/-
**edist_ofMul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：edist_ofMul (a b : X) : edist (ofMul a) (ofMul b) = edist a b
参数：a b : X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem edist_ofMul (a b : X) : edist (ofMul a) (ofMul b) = edist a b :=
  rfl

@[simp]
/-
**edist_ofAdd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：edist_ofAdd (a b : X) : edist (ofAdd a) (ofAdd b) = edist a b
参数：a b : X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem edist_ofAdd (a b : X) : edist (ofAdd a) (ofAdd b) = edist a b :=
  rfl

@[simp]
/-
**edist_toMul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：edist_toMul (a b : Additive X) : edist a.toMul b.toMul = edist a b
参数：a b : Additive X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem edist_toMul (a b : Additive X) : edist a.toMul b.toMul = edist a b :=
  rfl

@[simp]
/-
**edist_toAdd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：edist_toAdd (a b : Multiplicative X) : edist a.toAdd b.toAdd = edist a b
参数：a b : Multiplicative X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem edist_toAdd (a b : Multiplicative X) : edist a.toAdd b.toAdd = edist a b :=
  rfl

end

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [PseudoEMetricSpace X] : PseudoEMetricSpace (Additive X) := ‹PseudoEMetricSpace X›
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [PseudoEMetricSpace X] : PseudoEMetricSpace (Multiplicative X) := ‹PseudoEMetricSpace X›
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [EMetricSpace X] : EMetricSpace (Additive X) := ‹EMetricSpace X›
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [EMetricSpace X] : EMetricSpace (Multiplicative X) := ‹EMetricSpace X›

/-!
### Order dual

The distance on this type synonym is inherited without change.
-/


open OrderDual

section

variable [EDist X]

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : EDist Xᵒᵈ := ‹EDist X›

@[simp]
/-
**edist_toDual** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：edist_toDual (a b : X) : edist (toDual a) (toDual b) = edist a b
参数：a b : X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem edist_toDual (a b : X) : edist (toDual a) (toDual b) = edist a b :=
  rfl

@[simp]
/-
**edist_ofDual** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：edist_ofDual (a b : Xᵒᵈ) : edist (ofDual a) (ofDual b) = edist a b
参数：a b : Xᵒᵈ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem edist_ofDual (a b : Xᵒᵈ) : edist (ofDual a) (ofDual b) = edist a b :=
  rfl

end

section

/-- A `WeakPseudoEMetricSpace` is a topological space endowed with a `ℝ≥0∞`-value distance `edist`
which is *almost* an extended pseudometric space: the `edist` is reflexive, commutative and
satisfies the triangle inequality, but the topology on `α` need not *equal* the topology induced
by the `edist`. (It must be at least as fine, and agree with it on eballs of finite radius.)

This generalises both pseudo extended metric spaces and `ℝ≥0∞` (which have an extended distance,
which does not induce the order topology there). -/
/-
**WeakPseudoEMetricSpace** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u) → [τ : TopologicalSpace α] → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `WeakPseudoEMetricSpace` is a topological space endowed with a `ℝ≥0∞`-value di
stance `edist`
which is *almost* an extended pseudometric space: the `edist` is reflexive, comm
utative and
satisfies the triangle inequality, but the topology on `α` need not *equal* the 
topology induced
by the `edist`. (It must be at least as fine, and agree with it on eballs of fin
ite radius.)

This generalises both pseudo extended metric spaces and `ℝ≥0∞` (which have an ex
tended distance,
which does not induce the order topology there).
-/
class WeakPseudoEMetricSpace
    (α : Type u) [τ : TopologicalSpace α] : Type u extends EDist α  where
  edist_self : ∀ x : α, edist x x = 0
  edist_comm : ∀ x y : α, edist x y = edist y x
  edist_triangle : ∀ x y z : α, edist x z ≤ edist x y + edist y z
  /-- The topology on `α` is at most as fine as the topology generated by the `edist`. -/
  topology_le :
    (uniformSpaceOfEDist edist edist_self edist_comm edist_triangle).toTopologicalSpace ≤ τ
  /-- The ambient topology on `α` matches the `edist` topology on eballs. -/
  topology_eq_on_restrict :
    ∀ (x : α) (r : ℝ≥0∞),
    IsOpen ((Metric.eball x ⊤) ↓∩ (Metric.eball x r))

@[ext]
/-
**WeakPseudoEMetricSpace.ext** 是 Mathlib 中的一个定理，位于命名空间 `WeakPseudoEMetricSpace`。
形式化陈述：∀ {α : Type u_2} [inst : TopologicalSpace α] {m m' : WeakPseudoEMetricSpac
e α}, m.toEDist = m'.toEDist → m = m'
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
protected theorem WeakPseudoEMetricSpace.ext
    {α : Type*} [TopologicalSpace α] {m m' : WeakPseudoEMetricSpace α}
      (h : m.toEDist = m'.toEDist) : m = m' := by
  cases m; cases m'; congr

/-- Every `PseudoEMetricSpace` has a `WeakPseudoEMetricSpace` structure by
using the topology induced by `edist`. -/
/-
**PseudoEMetricSpace.toWeakPseudoEMetricSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：PseudoEMetricSpace.toWeakPseudoEMetricSpace (α : Type u) [inst : PseudoEMe
tricSpace α] : WeakPseudoEMetricSpace α where edist_self
参数：α : Type u。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `PseudoEMetricSpace.edist_self`：∀ {α : Type u} [self : PseudoEMetricSpace
 α] (x : α), edist x x = 0
· 使用定理 `PseudoEMetricSpace.edist_comm`：∀ {α : Type u} [self : PseudoEMetricSpace
 α] (x y : α), edist x y = edist y x
· 使用定理 `PseudoEMetricSpace.edist_triangle`：∀ {α : Type u} [self : PseudoEMetricS
pace α] (x y z : α), edist x z ≤ edist x y + edist y z

--- 原说明 ---
Every `PseudoEMetricSpace` has a `WeakPseudoEMetricSpace` structure by
using the topology induced by `edist`.
-/
instance PseudoEMetricSpace.toWeakPseudoEMetricSpace (α : Type u) [inst : PseudoEMetricSpace α] :
    WeakPseudoEMetricSpace α where
  edist_self := edist_self
  edist_comm := edist_comm
  edist_triangle := edist_triangle
  topology_le := by rw [uniformSpace_edist]
  topology_eq_on_restrict _ _ := Metric.isOpen_eball.preimage_val

/-- `WeakPseudoEMetricSpace` can be induced backwards. -/
/-
**WeakPseudoEMetricSpace.IsInducing** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：WeakPseudoEMetricSpace.IsInducing {α β : Type*} [e : TopologicalSpace α] [
n : TopologicalSpace β] {f : α -> β} (hf : IsInducing f) (m : WeakPseudoEMetricS
pace β) : WeakPseudoEMetricSpace α where edist
参数：hf : IsInducing f；m : WeakPseudoEMetricSpace β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`WeakPseudoEMetricSpace` can be induced backwards.
-/
abbrev WeakPseudoEMetricSpace.IsInducing {α β : Type*} [e : TopologicalSpace α]
  [n : TopologicalSpace β] {f : α → β} (hf : IsInducing f) (m : WeakPseudoEMetricSpace β) :
    WeakPseudoEMetricSpace α where
  edist := fun x y ↦ edist (f x) (f y)
  edist_self x := edist_self (f x)
  edist_comm x y := edist_comm (f x) (f y)
  edist_triangle x y z := edist_triangle (f x) (f y) (f z)
  topology_le := by
    let hα := PseudoEMetricSpace.ofEDist (fun x y ↦ edist (f x) (f y))
      (fun x ↦ edist_self (f x)) (fun x y ↦ edist_comm (f x) (f y))
      (fun x y z ↦ edist_triangle (f x) (f y) (f z))
    let hβ := PseudoEMetricSpace.ofEDist m.edist edist_self edist_comm edist_triangle
    rw [(isInducing_iff f).mp hf]
    refine (continuous_le_rng m.topology_le ?_).le_induced
    refine @Continuous.mk α β hα.toUniformSpace.toTopologicalSpace
      hβ.toUniformSpace.toTopologicalSpace f fun s hs ↦ ?_
    rw [isOpen_iff] at hs ⊢
    intro x (hx : f x ∈ s)
    obtain ⟨ε, hε, hεs⟩ := hs (f x) hx
    exact ⟨ε, hε, fun y hy ↦ hεs hy⟩
  topology_eq_on_restrict x r := by
    obtain ⟨u, hu, uy⟩ := m.topology_eq_on_restrict (f x) r
    rw [(isInducing_iff f).mp hf]
    exact ⟨f ⁻¹' u, isOpen_induced hu, by aesop (add simp [Set.ext_iff])⟩

/-- Weak pseudo-emetric space instance on subsets of weak pseudo-emetric spaces -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Weak pseudo-emetric space instance on subsets of weak pseudo-emetric spaces
-/
instance {α : Type*} {p : α → Prop} [TopologicalSpace α] [WeakPseudoEMetricSpace α] :
    WeakPseudoEMetricSpace (Subtype p) :=
  WeakPseudoEMetricSpace.IsInducing IsInducing.subtypeVal ‹_›

/-- A weak extended metric space extends a `WeakPseudoEMetricSpace` with the condition
`edist x y = 0 ↔ x = y`. -/
/-
**WeakEMetricSpace** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u) → [TopologicalSpace α] → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A weak extended metric space extends a `WeakPseudoEMetricSpace` with the conditi
on
`edist x y = 0 ↔ x = y`.
-/
class WeakEMetricSpace
    (α : Type u) [TopologicalSpace α] : Type u extends WeakPseudoEMetricSpace α where
  eq_of_edist_eq_zero : ∀ {x y : α}, edist x y = 0 → x = y

@[ext]
/-
**WeakEMetricSpace.ext** 是 Mathlib 中的一个定理，位于命名空间 `WeakEMetricSpace`。
形式化陈述：∀ {α : Type u_2} [inst : TopologicalSpace α] {m m' : WeakEMetricSpace α}, 
m.toEDist = m'.toEDist → m = m'
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WeakPseudoEMetricSpace.ext`：∀ {α : Type u_2} [inst : TopologicalSpace α]
 {m m' : WeakPseudoEMetricSpace α}, m.toEDist = m'.toEDist → m = m'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
protected theorem WeakEMetricSpace.ext {α : Type*} [TopologicalSpace α] {m m' : WeakEMetricSpace α}
    (h : m.toEDist = m'.toEDist) : m = m' := by
  cases m
  cases m'
  congr
  ext1
  assumption

/--
Every `EMetricSpace` has a `WeakEMetricSpace` structure by using the topology induced by edist. -/
/-
**EMetricSpace.toWeakEMetricSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：EMetricSpace.toWeakEMetricSpace (α : Type u) [EMetricSpace α] : WeakEMetri
cSpace α where eq_of_edist_eq_zero
参数：α : Type u。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `EMetricSpace.eq_of_edist_eq_zero`：∀ {α : Type u} [self : EMetricSpace α]
 {x y : α}, edist x y = 0 → x = y

--- 原说明 ---
Every `EMetricSpace` has a `WeakEMetricSpace` structure by using the topology in
duced by edist.
-/
instance EMetricSpace.toWeakEMetricSpace (α : Type u) [EMetricSpace α] :
    WeakEMetricSpace α where
  eq_of_edist_eq_zero := eq_of_edist_eq_zero

/-- The `WeakEMetric` space induced by pulling back a topology along an injective function. -/
/-
**WeakEMetricSpace.induced** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：WeakEMetricSpace.induced {α β : Type*} [n : TopologicalSpace β] {f : α -> 
β} (hf : Function.Injective f) (m : WeakEMetricSpace β) : @WeakEMetricSpace α (T
opologicalSpace.induced f n)
参数：hf : Function.Injective f；m : WeakEMetricSpace β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `WeakEMetric` space induced by pulling back a topology along an injective fu
nction.
-/
abbrev WeakEMetricSpace.induced
  {α β : Type*} [n : TopologicalSpace β]
  {f : α → β} (hf : Function.Injective f) (m : WeakEMetricSpace β) :
    @WeakEMetricSpace α (TopologicalSpace.induced f n) :=
  letI := TopologicalSpace.induced f n
  { WeakPseudoEMetricSpace.IsInducing (f := f) {eq_induced := rfl} m.toWeakPseudoEMetricSpace with
    eq_of_edist_eq_zero := fun h => hf (m.eq_of_edist_eq_zero h) }

/-- `WeakEMetricSpace` instance on subsets of emetric spaces -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`WeakEMetricSpace` instance on subsets of emetric spaces
-/
instance {α : Type*} {p : α → Prop} [TopologicalSpace α] [WeakEMetricSpace α] :
    WeakEMetricSpace (Subtype p) :=
  WeakEMetricSpace.induced Subtype.coe_injective ‹_›

end

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [TopologicalSpace X] [WeakPseudoEMetricSpace X] : WeakPseudoEMetricSpace Xᵒᵈ :=
  ‹WeakPseudoEMetricSpace X›
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [TopologicalSpace X] [WeakEMetricSpace X] : WeakEMetricSpace Xᵒᵈ :=
  ‹WeakEMetricSpace X›
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [PseudoEMetricSpace X] : PseudoEMetricSpace Xᵒᵈ :=
  ‹PseudoEMetricSpace X›
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [EMetricSpace X] : EMetricSpace Xᵒᵈ :=
  ‹EMetricSpace X›
