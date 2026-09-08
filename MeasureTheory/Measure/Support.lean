/-
Copyright (c) 2025 Jon Bannon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Bannon, Jireh Loreaux
-/
module

public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Measure.Regular

/-!
# Support of a Measure

This file develops the theory of the **support** of a measure `μ` on a
topological measurable space. The support is defined as the set of points whose every open
neighborhood has positive measure. We give equivalent characterizations, prove basic
measure-theoretic properties, and study interactions with sums, restrictions, and
absolute continuity. Under various Lindelöf or regularity conditions, the support is conull,
and various descriptions of the complement of the support are provided.

## Main definitions

* `Measure.support` : the support of a measure `μ`, defined as
  `{x | ∃ᶠ u in (𝓝 x).smallSets, 0 < μ u}` — equivalently, every neighborhood of `x`
  has positive `μ`-measure.

## Main results

* `compl_support_eq_sUnion` and `support_eq_sInter` : the complement of the support is the
  union of open measure-zero sets, and the support is the intersection of closed sets whose
  complements have measure zero.
* `isClosed_support` : the support is a closed set.
* `support_mem_ae_of_isLindelof` and `support_mem_ae` : under Lindelöf (or hereditarily
  Lindelöf) hypotheses, the support is conull.
* `support_mem_ae_of_innerRegularWRT_isCompact_isOpen` and
  `measure_compl_support_of_innerRegularWRT_isCompact_isOpen` : inner regularity by compact
  sets on open sets imply that the support is conull.

## Tags

measure, support, Lindelöf
-/

@[expose] public section

section Support

namespace MeasureTheory

namespace Measure

open scoped Topology ENNReal

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]

/-- A point `x` is in the support of `μ` if any open neighborhood of `x` has positive measure.
We provide the definition in terms of the filter-theoretic equivalent
`∃ᶠ u in (𝓝 x).smallSets, 0 < μ u`. -/
/-
**MeasureTheory.Measure.support** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.Measure
`。
形式化陈述：{X : Type u_1} → [TopologicalSpace X] → [inst : MeasurableSpace X] → Measu
reTheory.Measure X → Set X
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A point `x` is in the support of `μ` if any open neighborhood of `x` has positiv
e measure.
We provide the definition in terms of the filter-theoretic equivalent
`∃ᶠ u in (𝓝 x).smallSets, 0 < μ u`.
-/
protected def support (μ : Measure X) : Set X := {x : X | ∃ᶠ u in (𝓝 x).smallSets, 0 < μ u}

variable {μ : Measure X}
/-
**MeasureTheory.Measure._root_.Filter.HasBasis.mem_measureSupport** 是 Mathlib 中的
一个定理，位于命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Filter.HasBasis.mem_measureSupport {ι : Sort*} {p : ι → Prop}
    {s : ι → Set X} {x : X} (hl : (𝓝 x).HasBasis p s) :
    x ∈ μ.support ↔ ∀ (i : ι), p i → 0 < μ (s i) :=
  hl.frequently_smallSets pos_mono

/-- A point `x` is in the support of measure `μ` iff any neighborhood of `x` contains a
subset with positive measure. -/
/-
**MeasureTheory.Measure.mem_support_iff** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory
.Measure`。
形式化陈述：mem_support_iff {x : X} : x in μ.support ↔ existsᶠ u in (𝓝 x).smallSets, 0
 < μ u
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
A point `x` is in the support of measure `μ` iff any neighborhood of `x` contain
s a
subset with positive measure.
-/
lemma mem_support_iff {x : X} : x ∈ μ.support ↔
    ∃ᶠ u in (𝓝 x).smallSets, 0 < μ u := Iff.rfl

/-- A point `x` is in the support of measure `μ` iff every neighborhood of `x` has positive
measure. -/
/-
**MeasureTheory.Measure.mem_support_iff_forall** 是 Mathlib 中的一个引理，位于命名空间 `Measur
eTheory.Measure`。
形式化陈述：mem_support_iff_forall (x : X) : x in μ.support ↔ forall U in 𝓝 x, 0 < μ U
参数：x : X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.mem_measureSupport`：∀ {X : Type u_1} [inst : Topological
Space X] [inst_1 : MeasurableSpace X] {μ : MeasureTheory.Measure X} {ι : Sort u_
2}   {p : ι → Prop} {s :…
· 使用定理 `Filter.basis_sets`：basis_sets (l : Filter α) : l.HasBasis (fun s : Set α
 => s in l) id

--- 原说明 ---
A point `x` is in the support of measure `μ` iff every neighborhood of `x` has p
ositive
measure.
-/
lemma mem_support_iff_forall (x : X) : x ∈ μ.support ↔ ∀ U ∈ 𝓝 x, 0 < μ U :=
  (𝓝 x).basis_sets.mem_measureSupport
/-
**MeasureTheory.Measure.support_eq_univ** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory
.Measure`。
形式化陈述：support_eq_univ [μ.IsOpenPosMeasure] : μ.support = Set.univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `MeasureTheory.Measure.measure_pos_of_mem_nhds`：measure_pos_of_mem_nhds (
h : s in 𝓝 x) : 0 < μ s
-/
lemma support_eq_univ [μ.IsOpenPosMeasure] : μ.support = Set.univ := by
  simpa [Set.eq_univ_iff_forall, mem_support_iff_forall] using fun _ _ ↦ μ.measure_pos_of_mem_nhds
/-
**MeasureTheory.Measure.AbsolutelyContinuous.support_mono** 是 Mathlib 中的一个定理，位于命
名空间 `MeasureTheory.Measure.AbsolutelyContinuous`。
形式化陈述：∀ {X : Type u_1} [inst : TopologicalSpace X] [inst_1 : MeasurableSpace X] 
{μ ν : MeasureTheory.Measure X},   μ.AbsolutelyContinuous ν → μ.support ⊆ ν.supp
ort
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Frequently.mp`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},   
(∃ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, p x → q x) → ∃ᶠ (x : α) in f, q x
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用引理 `MeasureTheory.Measure.AbsolutelyContinuous.pos_mono`：pos_mono {μ ν : Mea
sure α} (hμν : μ ≪ ν) ⦃t : Set α⦄ (ht : 0 < μ t) : 0 < ν t
-/
lemma AbsolutelyContinuous.support_mono {μ ν : Measure X} (hμν : μ ≪ ν) :
    μ.support ⊆ ν.support :=
  fun _ hx ↦ hx.mp <| .of_forall hμν.pos_mono
/-
**MeasureTheory.Measure.support_mono** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.Me
asure`。
形式化陈述：support_mono {ν : Measure X} (h : μ <= ν) : μ.support subseteq ν.support
参数：h : μ <= ν。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.support_mono`：∀ {X : Type u_1
} [inst : TopologicalSpace X] [inst_1 : MeasurableSpace X] {μ ν : MeasureTheory.
Measure X},   μ.AbsolutelyContinuous ν → μ.su…
· 使用定理 `LE.le.absolutelyContinuous`：∀ {α : Type u_1} {mα : MeasurableSpace α} {μ
 ν : MeasureTheory.Measure α}, μ ≤ ν → μ.AbsolutelyContinuous ν
-/
lemma support_mono {ν : Measure X} (h : μ ≤ ν) : μ.support ⊆ ν.support :=
  h.absolutelyContinuous.support_mono

/-- A point `x` lies outside the support of `μ` iff all of the subsets of one of its neighborhoods
have measure zero. -/
/-
**MeasureTheory.Measure.notMem_support_iff** 是 Mathlib 中的一个引理，位于命名空间 `MeasureThe
ory.Measure`。
形式化陈述：notMem_support_iff {x : X} : x ∉ μ.support ↔ forallᶠ u in (𝓝 x).smallSets,
 μ u = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A point `x` lies outside the support of `μ` iff all of the subsets of one of its
 neighborhoods
have measure zero.
-/
lemma notMem_support_iff {x : X} : x ∉ μ.support ↔ ∀ᶠ u in (𝓝 x).smallSets, μ u = 0 := by
  simp [mem_support_iff]
/-
**MeasureTheory.Measure._root_.Filter.HasBasis.notMem_measureSupport** 是 Mathlib
 中的一个定理，位于命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Filter.HasBasis.notMem_measureSupport {ι : Sort*} {p : ι → Prop}
    {s : ι → Set X} {x : X} (hl : (𝓝 x).HasBasis p s) :
    x ∉ μ.support ↔ ∃ i, p i ∧ μ (s i) = 0 := by
  simp [hl.mem_measureSupport]

@[simp]
/-
**MeasureTheory.Measure.support_zero** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.Me
asure`。
形式化陈述：support_zero : (0 : Measure X).support = ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma support_zero : (0 : Measure X).support = ∅ := by simp [Measure.support]

/-- The support of the sum of two measures is the union of the supports. -/
/-
**MeasureTheory.Measure.support_add** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.Mea
sure`。
形式化陈述：support_add (μ ν : Measure X) : (μ + ν).support = μ.support union ν.suppor
t
参数：μ ν : Measure X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
The support of the sum of two measures is the union of the supports.
-/
lemma support_add (μ ν : Measure X) : (μ + ν).support = μ.support ∪ ν.support := by
  ext; simp [mem_support_iff]

/-- A point `x` lies outside the support of `μ` iff some neighborhood of `x` has measure zero. -/
/-
**MeasureTheory.Measure.notMem_support_iff_exists** 是 Mathlib 中的一个引理，位于命名空间 `Mea
sureTheory.Measure`。
形式化陈述：notMem_support_iff_exists {x : X} : x ∉ μ.support ↔ exists U in 𝓝 x, μ U =
 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A point `x` lies outside the support of `μ` iff some neighborhood of `x` has mea
sure zero.
-/
lemma notMem_support_iff_exists {x : X} : x ∉ μ.support ↔ ∃ U ∈ 𝓝 x, μ U = 0 := by
  simp [mem_support_iff_forall]

/-- The support of a measure equals the set of points whose open neighborhoods
all have positive measure. -/
/-
**MeasureTheory.Measure.support_eq_forall_isOpen** 是 Mathlib 中的一个引理，位于命名空间 `Meas
ureTheory.Measure`。
形式化陈述：support_eq_forall_isOpen : μ.support = {x : X | forall u : Set X, x in u -
> IsOpen u -> 0 < μ u}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.HasBasis.mem_measureSupport`：∀ {X : Type u_1} [inst : Topological
Space X] [inst_1 : MeasurableSpace X] {μ : MeasureTheory.Measure X} {ι : Sort u_
2}   {p : ι → Prop} {s :…
· 使用定理 `nhds_basis_opens`：nhds_basis_opens (x : X) : (𝓝 x).HasBasis (fun s : Set
 X => x in s ∧ IsOpen s) fun s => s
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
The support of a measure equals the set of points whose open neighborhoods
all have positive measure.
-/
lemma support_eq_forall_isOpen : μ.support =
    {x : X | ∀ u : Set X, x ∈ u → IsOpen u → 0 < μ u} := by
  simp [Set.ext_iff, nhds_basis_opens _ |>.mem_measureSupport]
/-
**MeasureTheory.Measure.isClosed_support** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheor
y.Measure`。
形式化陈述：isClosed_support {μ : Measure X} : IsClosed μ.support
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.HasBasis.mem_measureSupport`：∀ {X : Type u_1} [inst : Topological
Space X] [inst_1 : MeasurableSpace X] {μ : MeasureTheory.Measure X} {ι : Sort u_
2}   {p : ι → Prop} {s :…
· 使用定理 `nhds_basis_opens`：nhds_basis_opens (x : X) : (𝓝 x).HasBasis (fun s : Set
 X => x in s ∧ IsOpen s) fun s => s
· 使用定理 `Filter.HasBasis.frequently_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Fil
ter α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → ∀ {q : α → Prop}, (∃ᶠ 
(x : α) in l, q x) ↔…
-/
lemma isClosed_support {μ : Measure X} : IsClosed μ.support := by
  simp_rw [isClosed_iff_frequently, nhds_basis_opens _ |>.mem_measureSupport,
    nhds_basis_opens _ |>.frequently_iff]
  grind
/-
**MeasureTheory.Measure.isOpen_compl_support** 是 Mathlib 中的一个引理，位于命名空间 `MeasureT
heory.Measure`。
形式化陈述：isOpen_compl_support {μ : Measure X} : IsOpen μ.supportᶜ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isOpen_compl_iff`：∀ {X : Type u} {s : Set X} [inst : TopologicalSpace X]
, IsOpen sᶜ ↔ IsClosed s
· 使用引理 `MeasureTheory.Measure.isClosed_support`：isClosed_support {μ : Measure X}
 : IsClosed μ.support
-/
lemma isOpen_compl_support {μ : Measure X} : IsOpen μ.supportᶜ :=
  isOpen_compl_iff.mpr μ.isClosed_support
/-
**MeasureTheory.Measure.subset_compl_support_of_isOpen** 是 Mathlib 中的一个引理，位于命名空间
 `MeasureTheory.Measure`。
形式化陈述：subset_compl_support_of_isOpen {t : Set X} (ht : IsOpen t) (h : μ t = 0) :
 t subseteq μ.supportᶜ
参数：ht : IsOpen t；h : μ t = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `MeasureTheory.Measure.notMem_support_iff_exists`：notMem_support_iff_exis
ts {x : X} : x ∉ μ.support ↔ exists U in 𝓝 x, μ U = 0
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
-/
lemma subset_compl_support_of_isOpen {t : Set X} (ht : IsOpen t) (h : μ t = 0) :
    t ⊆ μ.supportᶜ :=
  fun _ hx ↦ notMem_support_iff_exists.mpr ⟨t, ht.mem_nhds hx, h⟩
/-
**MeasureTheory.Measure.support_subset_of_isClosed** 是 Mathlib 中的一个引理，位于命名空间 `Me
asureTheory.Measure`。
形式化陈述：support_subset_of_isClosed {t : Set X} (ht : IsClosed t) (h : t in ae μ) :
 μ.support subseteq t
参数：ht : IsClosed t；h : t in ae μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.compl_subset_compl`：compl_subset_compl : sᶜ subseteq tᶜ ↔ t subseteq
 s
· 使用引理 `MeasureTheory.Measure.subset_compl_support_of_isOpen`：subset_compl_suppo
rt_of_isOpen {t : Set X} (ht : IsOpen t) (h : μ t = 0) : t subseteq μ.supportᶜ
· 使用定理 `IsClosed.isOpen_compl`：∀ {X : Type u} {inst : TopologicalSpace X} {s : S
et X} [self : IsClosed s], IsOpen sᶜ
-/
lemma support_subset_of_isClosed {t : Set X} (ht : IsClosed t) (h : t ∈ ae μ) :
    μ.support ⊆ t :=
  Set.compl_subset_compl.mp <| subset_compl_support_of_isOpen ht.isOpen_compl h
/-
**MeasureTheory.Measure.compl_support_eq_sUnion** 是 Mathlib 中的一个引理，位于命名空间 `Measu
reTheory.Measure`。
形式化陈述：compl_support_eq_sUnion : μ.supportᶜ = ⋃₀ {t : Set X | IsOpen t ∧ μ t = 0}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.HasBasis.notMem_measureSupport`：∀ {X : Type u_1} [inst : Topologi
calSpace X] [inst_1 : MeasurableSpace X] {μ : MeasureTheory.Measure X} {ι : Sort
 u_2}   {p : ι → Prop} {s :…
· 使用定理 `nhds_basis_opens`：nhds_basis_opens (x : X) : (𝓝 x).HasBasis (fun s : Set
 X => x in s ∧ IsOpen s) fun s => s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma compl_support_eq_sUnion : μ.supportᶜ = ⋃₀ {t : Set X | IsOpen t ∧ μ t = 0} := by
  ext x
  simp only [Set.mem_compl_iff, Set.mem_sUnion, Set.mem_ofPred_eq, and_right_comm,
    nhds_basis_opens x |>.notMem_measureSupport, fun t ↦ and_comm (b := x ∈ t)]
/-
**MeasureTheory.Measure.support_eq_sInter** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheo
ry.Measure`。
形式化陈述：support_eq_sInter : μ.support = ⋂₀ {t : Set X | IsClosed t ∧ μ tᶜ = 0}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.compl_sUnion`：compl_sUnion (S : Set (Set α)) : (⋃₀ S)ᶜ = ⋂₀ (compl '
' S)
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Function.Involutive.image_eq_preimage_symm`：∀ {α : Type u_1} {f : α → α}
, Function.Involutive f → Set.image f = Set.preimage f
· 使用定理 `compl_involutive`：compl_involutive : Function.Involutive (compl : α -> α
)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `MeasureTheory.Measure.compl_support_eq_sUnion`：compl_support_eq_sUnion :
 μ.supportᶜ = ⋃₀ {t : Set X | IsOpen t ∧ μ t = 0}
-/
lemma support_eq_sInter : μ.support = ⋂₀ {t : Set X | IsClosed t ∧ μ tᶜ = 0} := by
  convert! congr($(compl_support_eq_sUnion (μ := μ))ᶜ)
  all_goals simp [Set.compl_sUnion, compl_involutive.image_eq_preimage_symm]

section Regular

/-- Any compact set contained in the complement of the support has zero measure. -/
/-
**MeasureTheory.Measure.measure_eq_zero_of_isCompact_subset_compl_support** 是 Ma
thlib 中的一个引理，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：measure_eq_zero_of_isCompact_subset_compl_support {K : Set X} (hK : IsComp
act K) (hKsub : K subseteq μ.supportᶜ) : μ K = 0
参数：hK : IsCompact K；hKsub : K subseteq μ.supportᶜ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.induction_on`：IsCompact.induction_on (hs : IsCompact s) {p : S
et X -> Prop} (he : p ∅) (hmono : forall ⦃s t⦄, s subseteq t -> p t -> p s) (hun
ion : forall…
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.measure_mono_null`：measure_mono_null (h : s subseteq t) (h
t : μ t = 0) : μ s = 0
· 使用定理 `MeasureTheory.measure_union_null`：measure_union_null (hs : μ s = 0) (ht 
: μ t = 0) : μ (s union t) = 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `MeasureTheory.Measure.notMem_support_iff_exists`：notMem_support_iff_exis
ts {x : X} : x ∉ μ.support ↔ exists U in 𝓝 x, μ U = 0
· 使用定理 `mem_nhdsWithin_of_mem_nhds`：mem_nhdsWithin_of_mem_nhds {s t : Set α} {a 
: α} (h : s in 𝓝 a) : s in 𝓝[t] a

--- 原说明 ---
Any compact set contained in the complement of the support has zero measure.
-/
lemma measure_eq_zero_of_isCompact_subset_compl_support {K : Set X} (hK : IsCompact K)
    (hKsub : K ⊆ μ.supportᶜ) : μ K = 0 := by
  refine hK.induction_on measure_empty ?_ ?_ ?_
  · exact fun _ _ hst ht ↦ measure_mono_null hst ht
  · exact fun _ _ hs ht ↦ measure_union_null hs ht
  · intro x hxK
    obtain ⟨U, hUnhds, hU0⟩ := notMem_support_iff_exists.1 (hKsub hxK)
    exact ⟨U, mem_nhdsWithin_of_mem_nhds hUnhds, hU0⟩

/-- A measure which is compact-inner-regular on open sets has conull support. -/
/-
**MeasureTheory.Measure.support_mem_ae_of_innerRegularWRT_isCompact_isOpen** 是 M
athlib 中的一个引理，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：support_mem_ae_of_innerRegularWRT_isCompact_isOpen (hμ : μ.InnerRegularWRT
 IsCompact IsOpen) : μ.support in ae μ
参数：hμ : μ.InnerRegularWRT IsCompact IsOpen。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `MeasureTheory.Measure.isOpen_compl_support`：isOpen_compl_support {μ : Me
asure X} : IsOpen μ.supportᶜ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.Measure.measure_eq_zero_of_isCompact_subset_compl_support`
：measure_eq_zero_of_isCompact_subset_compl_support {K : Set X} (hK : IsCompact K
) (hKsub : K subseteq μ.supportᶜ) : μ K = 0

--- 原说明 ---
A measure which is compact-inner-regular on open sets has conull support.
-/
lemma support_mem_ae_of_innerRegularWRT_isCompact_isOpen
    (hμ : μ.InnerRegularWRT IsCompact IsOpen) : μ.support ∈ ae μ := by
  by_contra hne
  obtain ⟨K, hKsub, hKcompact, hKpos⟩ := hμ isOpen_compl_support 0 (pos_iff_ne_zero.2 hne)
  simp [measure_eq_zero_of_isCompact_subset_compl_support hKcompact hKsub] at hKpos

/-- A measure which is compact-inner-regular on open sets has conull support. -/
@[simp]
/-
**MeasureTheory.Measure.measure_compl_support_of_innerRegularWRT_isCompact_isOpe
n** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：measure_compl_support_of_innerRegularWRT_isCompact_isOpen (hμ : μ.InnerReg
ularWRT IsCompact IsOpen) : μ μ.supportᶜ = 0
参数：hμ : μ.InnerRegularWRT IsCompact IsOpen。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.Measure.support_mem_ae_of_innerRegularWRT_isCompact_isOpen
`：support_mem_ae_of_innerRegularWRT_isCompact_isOpen (hμ : μ.InnerRegularWRT IsC
ompact IsOpen) : μ.support in ae μ

--- 原说明 ---
A measure which is compact-inner-regular on open sets has conull support.
-/
lemma measure_compl_support_of_innerRegularWRT_isCompact_isOpen
    (hμ : μ.InnerRegularWRT IsCompact IsOpen) : μ μ.supportᶜ = 0 :=
  support_mem_ae_of_innerRegularWRT_isCompact_isOpen hμ

/-- An inner regular measure has conull support when open sets are measurable. -/
/-
**MeasureTheory.Measure.support_mem_ae_of_innerRegular** 是 Mathlib 中的一个引理，位于命名空间
 `MeasureTheory.Measure`。
形式化陈述：support_mem_ae_of_innerRegular [OpensMeasurableSpace X] [μ.InnerRegular] :
 μ.support in ae μ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.Measure.support_mem_ae_of_innerRegularWRT_isCompact_isOpen
`：support_mem_ae_of_innerRegularWRT_isCompact_isOpen (hμ : μ.InnerRegularWRT IsC
ompact IsOpen) : μ.support in ae μ
· 使用定理 `MeasureTheory.Measure.InnerRegular.innerRegular`：∀ {α : Type u_1} {inst 
: MeasurableSpace α} {inst_1 : TopologicalSpace α} {μ : MeasureTheory.Measure α}
   [self : μ.InnerRegular], μ.InnerRe…
· 使用定理 `IsOpen.measurableSet`：IsOpen.measurableSet (h : IsOpen s) : MeasurableSe
t s

--- 原说明 ---
An inner regular measure has conull support when open sets are measurable.
-/
lemma support_mem_ae_of_innerRegular [OpensMeasurableSpace X] [μ.InnerRegular] :
    μ.support ∈ ae μ :=
  support_mem_ae_of_innerRegularWRT_isCompact_isOpen fun _ hU r hr =>
    InnerRegular.innerRegular hU.measurableSet r hr

/-- An inner regular measure has conull support when open sets are measurable. -/
@[simp]
/-
**MeasureTheory.Measure.measure_compl_support_of_innerRegular** 是 Mathlib 中的一个引理
，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：measure_compl_support_of_innerRegular [OpensMeasurableSpace X] [μ.InnerReg
ular] : μ μ.supportᶜ = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.Measure.support_mem_ae_of_innerRegular`：support_mem_ae_of_
innerRegular [OpensMeasurableSpace X] [μ.InnerRegular] : μ.support in ae μ

--- 原说明 ---
An inner regular measure has conull support when open sets are measurable.
-/
lemma measure_compl_support_of_innerRegular [OpensMeasurableSpace X] [μ.InnerRegular] :
    μ μ.supportᶜ = 0 := support_mem_ae_of_innerRegular

/-- A regular measure has conull support. -/
/-
**MeasureTheory.Measure.support_mem_ae_of_regular** 是 Mathlib 中的一个引理，位于命名空间 `Mea
sureTheory.Measure`。
形式化陈述：support_mem_ae_of_regular [μ.Regular] : μ.support in ae μ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.Measure.support_mem_ae_of_innerRegularWRT_isCompact_isOpen
`：support_mem_ae_of_innerRegularWRT_isCompact_isOpen (hμ : μ.InnerRegularWRT IsC
ompact IsOpen) : μ.support in ae μ
· 使用定理 `MeasureTheory.Measure.Regular.innerRegular`：∀ {α : Type u_1} {inst : Mea
surableSpace α} {inst_1 : TopologicalSpace α} {μ : MeasureTheory.Measure α}   [s
elf : μ.Regular], μ.InnerRegular…

--- 原说明 ---
A regular measure has conull support.
-/
lemma support_mem_ae_of_regular [μ.Regular] : μ.support ∈ ae μ :=
  support_mem_ae_of_innerRegularWRT_isCompact_isOpen Regular.innerRegular

/-- A regular measure has conull support. -/
@[simp]
/-
**MeasureTheory.Measure.measure_compl_support_of_regular** 是 Mathlib 中的一个引理，位于命名
空间 `MeasureTheory.Measure`。
形式化陈述：measure_compl_support_of_regular [μ.Regular] : μ μ.supportᶜ = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.Measure.support_mem_ae_of_regular`：support_mem_ae_of_regul
ar [μ.Regular] : μ.support in ae μ

--- 原说明 ---
A regular measure has conull support.
-/
lemma measure_compl_support_of_regular [μ.Regular] : μ μ.supportᶜ = 0 :=
  support_mem_ae_of_regular

end Regular

section Lindelof

/-- If the complement of the support is Lindelöf, then the support of a measure is conull. -/
/-
**MeasureTheory.Measure.support_mem_ae_of_isLindelof** 是 Mathlib 中的一个引理，位于命名空间 `
MeasureTheory.Measure`。
形式化陈述：support_mem_ae_of_isLindelof (h : IsLindelof μ.supportᶜ) : μ.support in ae
 μ
参数：h : IsLindelof μ.supportᶜ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `IsLindelof.compl_mem_sets_of_nhdsWithin`：IsLindelof.compl_mem_sets_of_nh
dsWithin (hs : IsLindelof s) {f : Filter X} [CountableInterFilter f] (hf : foral
l x in s, exists t in 𝓝[s] x,…
· 使用定理 `MeasureTheory.instCountableInterFilterAe`：∀ {α : Type u_1} {F : Type u_2
} [inst : FunLike F (Set α) ENNReal] [inst_1 : MeasureTheory.OuterMeasureClass F
 α]   (μ : F), CountableInterF…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsOpen.nhdsWithin_eq`：IsOpen.nhdsWithin_eq {a : α} {s : Set α} (h : IsOp
en s) (ha : a in s) : 𝓝[s] a = 𝓝 a
· 使用引理 `MeasureTheory.Measure.isOpen_compl_support`：isOpen_compl_support {μ : Me
asure X} : IsOpen μ.supportᶜ
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `MeasureTheory.Measure.notMem_support_iff_exists`：notMem_support_iff_exis
ts {x : X} : x ∉ μ.support ↔ exists U in 𝓝 x, μ U = 0
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x

--- 原说明 ---
If the complement of the support is Lindelöf, then the support of a measure is c
onull.
-/
lemma support_mem_ae_of_isLindelof (h : IsLindelof μ.supportᶜ) : μ.support ∈ ae μ := by
  refine compl_compl μ.support ▸ h.compl_mem_sets_of_nhdsWithin fun s hs ↦ ?_
  simpa [compl_mem_ae_iff, isOpen_compl_support.nhdsWithin_eq hs]
    using notMem_support_iff_exists.mp hs

variable [HereditarilyLindelofSpace X]

/-- In a hereditarily Lindelöf space, the support of a measure is conull. -/
/-
**MeasureTheory.Measure.support_mem_ae** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.
Measure`。
形式化陈述：support_mem_ae : μ.support in ae μ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.Measure.support_mem_ae_of_isLindelof`：support_mem_ae_of_is
Lindelof (h : IsLindelof μ.supportᶜ) : μ.support in ae μ
· 使用定理 `HereditarilyLindelofSpace.isLindelof`：HereditarilyLindelofSpace.isLindel
of [HereditarilyLindelofSpace X] (s : Set X) : IsLindelof s

--- 原说明 ---
In a hereditarily Lindelöf space, the support of a measure is conull.
-/
lemma support_mem_ae : μ.support ∈ ae μ :=
  support_mem_ae_of_isLindelof <| HereditarilyLindelofSpace.isLindelof μ.supportᶜ

@[simp]
/-
**MeasureTheory.Measure.measure_compl_support** 是 Mathlib 中的一个引理，位于命名空间 `Measure
Theory.Measure`。
形式化陈述：measure_compl_support : μ μ.supportᶜ = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.Measure.support_mem_ae`：support_mem_ae : μ.support in ae μ
-/
lemma measure_compl_support : μ μ.supportᶜ = 0 := support_mem_ae

open Set
/-
**MeasureTheory.Measure.nonempty_inter_support_of_pos** 是 Mathlib 中的一个引理，位于命名空间 
`MeasureTheory.Measure`。
形式化陈述：nonempty_inter_support_of_pos {s : Set X} (hμ : 0 < μ s) : (s inter μ.supp
ort).Nonempty
参数：hμ : 0 < μ s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Set.not_disjoint_iff_nonempty_inter`：not_disjoint_iff_nonempty_inter : ¬
 Disjoint s t ↔ (s inter t).Nonempty
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₃`：contrapose₃ {p q : Prop} : (q -> 
¬ p) -> (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `MeasureTheory.OuterMeasure.mono`：∀ {α : Type u_2} (self : MeasureTheory.
OuterMeasure α) {s₁ s₂ : Set α}, s₁ ⊆ s₂ → self.measureOf s₁ ≤ self.measureOf s₂
· 使用定理 `Disjoint.subset_compl_right`：∀ {α : Type u_1} {s t : Set α}, Disjoint s 
t → s ⊆ tᶜ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `MeasureTheory.Measure.measure_compl_support`：measure_compl_support : μ μ
.supportᶜ = 0
-/
lemma nonempty_inter_support_of_pos {s : Set X} (hμ : 0 < μ s) :
    (s ∩ μ.support).Nonempty := by
  rw [← Set.not_disjoint_iff_nonempty_inter]
  contrapose! hμ
  exact μ.mono hμ.subset_compl_right |>.trans <| by simp

/-- Under the assumption `OpensMeasurableSpace`, this is redundant because
the complement of the support is open, and therefore measurable. -/
/-
**MeasureTheory.Measure.nullMeasurableSet_compl_support** 是 Mathlib 中的一个引理，位于命名空
间 `MeasureTheory.Measure`。
形式化陈述：nullMeasurableSet_compl_support : NullMeasurableSet (μ.supportᶜ) μ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.NullMeasurableSet.of_null`：of_null (h : μ s = 0) : NullMea
surableSet s μ
· 使用引理 `MeasureTheory.Measure.measure_compl_support`：measure_compl_support : μ μ
.supportᶜ = 0

--- 原说明 ---
Under the assumption `OpensMeasurableSpace`, this is redundant because
the complement of the support is open, and therefore measurable.
-/
lemma nullMeasurableSet_compl_support : NullMeasurableSet (μ.supportᶜ) μ :=
  NullMeasurableSet.of_null measure_compl_support

/-- Under the assumption `OpensMeasurableSpace`, this is redundant because
the support is closed, and therefore measurable. -/
/-
**MeasureTheory.Measure.nullMeasurableSet_support** 是 Mathlib 中的一个引理，位于命名空间 `Mea
sureTheory.Measure`。
形式化陈述：nullMeasurableSet_support : NullMeasurableSet μ.support μ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.NullMeasurableSet.compl_iff`：compl_iff : NullMeasurableSet
 sᶜ μ ↔ NullMeasurableSet s μ
· 使用引理 `MeasureTheory.Measure.nullMeasurableSet_compl_support`：nullMeasurableSet
_compl_support : NullMeasurableSet (μ.supportᶜ) μ

--- 原说明 ---
Under the assumption `OpensMeasurableSpace`, this is redundant because
the support is closed, and therefore measurable.
-/
lemma nullMeasurableSet_support : NullMeasurableSet μ.support μ :=
  NullMeasurableSet.compl_iff.mp nullMeasurableSet_compl_support
/-
**MeasureTheory.Measure.nonempty_support** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheor
y.Measure`。
形式化陈述：nonempty_support (hμ : μ != 0) : μ.support.Nonempty
参数：hμ : μ != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Nonempty.right`：∀ {α : Type u} {s t : Set α}, (s ∩ t).Nonempty → t.N
onempty
· 使用引理 `MeasureTheory.Measure.nonempty_inter_support_of_pos`：nonempty_inter_supp
ort_of_pos {s : Set X} (hμ : 0 < μ s) : (s inter μ.support).Nonempty
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.Measure.measure_univ_pos`：measure_univ_pos : 0 < μ univ ↔ 
μ != 0
-/
lemma nonempty_support (hμ : μ ≠ 0) : μ.support.Nonempty :=
   Nonempty.right <| nonempty_inter_support_of_pos <| measure_univ_pos.mpr hμ
/-
**MeasureTheory.Measure.nonempty_support_iff** 是 Mathlib 中的一个引理，位于命名空间 `MeasureT
heory.Measure`。
形式化陈述：nonempty_support_iff : μ.support.Nonempty ↔ μ != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.not_nonempty_iff_eq_empty`：not_nonempty_iff_eq_empty : ¬s.Nonempty ↔
 s = ∅
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.Measure.support_zero`：support_zero : (0 : Measure X).suppo
rt = ∅
· 使用引理 `MeasureTheory.Measure.nonempty_support`：nonempty_support (hμ : μ != 0) :
 μ.support.Nonempty
-/
lemma nonempty_support_iff : μ.support.Nonempty ↔ μ ≠ 0 :=
  ⟨fun h e ↦ (not_nonempty_iff_eq_empty.mpr <| congrArg Measure.support e |>.trans
    <| support_zero) h, fun h ↦ nonempty_support h⟩

@[simp]
/-
**MeasureTheory.Measure.support_eq_empty_iff** 是 Mathlib 中的一个引理，位于命名空间 `MeasureT
heory.Measure`。
形式化陈述：support_eq_empty_iff : μ.support = ∅ ↔ μ = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_congr`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用引理 `MeasureTheory.Measure.nonempty_support_iff`：nonempty_support_iff : μ.sup
port.Nonempty ↔ μ != 0
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma support_eq_empty_iff : μ.support = ∅ ↔ μ = 0 := by
  simp [← Set.not_nonempty_iff_eq_empty, not_congr nonempty_support_iff]

end Lindelof

section Restrict

variable [OpensMeasurableSpace X]

/-
**MeasureTheory.Measure.mem_support_restrict** 是 Mathlib 中的一个引理，位于命名空间 `MeasureT
heory.Measure`。
形式化陈述：mem_support_restrict {s : Set X} {x : X} : x in (μ.restrict s).support ↔ e
xistsᶠ u in (𝓝[s] x).smallSets, 0 < μ u
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.HasBasis.mem_measureSupport`：∀ {X : Type u_1} [inst : Topological
Space X] [inst_1 : MeasurableSpace X] {μ : MeasureTheory.Measure X} {ι : Sort u_
2}   {p : ι → Prop} {s :…
· 使用定理 `nhds_basis_opens`：nhds_basis_opens (x : X) : (𝓝 x).HasBasis (fun s : Set
 X => x in s ∧ IsOpen s) fun s => s
· 使用定理 `Filter.HasBasis.frequently_smallSets`：∀ {α : Type u_4} {ι : Sort u_5} {p
 : ι → Prop} {l : Filter α} {s : ι → Set α} {q : Set α → Prop} {hl : l.HasBasis 
p s},   (∀ ⦃s t : Set α⦄, …
· 使用定理 `nhdsWithin_basis_open`：nhdsWithin_basis_open (a : α) (t : Set α) : (𝓝[t]
 a).HasBasis (fun u => a in u ∧ IsOpen u) fun u => u inter t
· 使用引理 `MeasureTheory.pos_mono`：pos_mono ⦃s t : Set α⦄ (h : s subseteq t) (hs : 
0 < μ s) : 0 < μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
-/
lemma mem_support_restrict {s : Set X} {x : X} :
    x ∈ (μ.restrict s).support ↔ ∃ᶠ u in (𝓝[s] x).smallSets, 0 < μ u := by
  rw [nhds_basis_opens x |>.mem_measureSupport,
    (nhdsWithin_basis_open x s).frequently_smallSets pos_mono]
  grind [IsOpen.measurableSet, restrict_apply]
/-
**MeasureTheory.Measure.interior_inter_support** 是 Mathlib 中的一个引理，位于命名空间 `Measur
eTheory.Measure`。
形式化陈述：interior_inter_support {s : Set X} : interior s inter μ.support subseteq (
μ.restrict s).support
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.Measure.mem_support_restrict`：mem_support_restrict {s : Se
t X} {x : X} : x in (μ.restrict s).support ↔ existsᶠ u in (𝓝[s] x).smallSets, 0 
< μ u
· 使用定理 `Filter.HasBasis.frequently_smallSets`：∀ {α : Type u_4} {ι : Sort u_5} {p
 : ι → Prop} {l : Filter α} {s : ι → Set α} {q : Set α → Prop} {hl : l.HasBasis 
p s},   (∀ ⦃s t : Set α⦄, …
· 使用定理 `nhdsWithin_basis_open`：nhdsWithin_basis_open (a : α) (t : Set α) : (𝓝[t]
 a).HasBasis (fun u => a in u ∧ IsOpen u) fun u => u inter t
· 使用引理 `MeasureTheory.pos_mono`：pos_mono ⦃s t : Set α⦄ (h : s subseteq t) (hs : 
0 < μ s) : 0 < μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Filter.HasBasis.mem_measureSupport`：∀ {X : Type u_1} [inst : Topological
Space X] [inst_1 : MeasurableSpace X] {μ : MeasureTheory.Measure X} {ι : Sort u_
2}   {p : ι → Prop} {s :…
· 使用定理 `nhds_basis_opens`：nhds_basis_opens (x : X) : (𝓝 x).HasBasis (fun s : Set
 X => x in s ∧ IsOpen s) fun s => s
· 使用定理 `IsOpen.inter`：IsOpen.inter (s t : Set α) : IsOpen α s -> IsOpen α t -> I
sOpen α (s inter t)
· 使用定理 `isOpen_interior`：isOpen_interior : IsOpen (interior s)
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `Set.inter_subset_inter`：inter_subset_inter {s₁ s₂ t₁ t₂ : Set α} (h₁ : s
₁ subseteq t₁) (h₂ : s₂ subseteq t₂) : s₁ inter s₂ subseteq t₁ inter t₂
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s
-/
lemma interior_inter_support {s : Set X} :
    interior s ∩ μ.support ⊆ (μ.restrict s).support := by
  rintro x ⟨hxs, hxμ⟩
  rw [mem_support_restrict, (nhdsWithin_basis_open x s).frequently_smallSets pos_mono]
  rw [(nhds_basis_opens x).mem_measureSupport] at hxμ
  rintro u ⟨hxu, hu⟩
  apply hxμ (u ∩ interior s) ⟨⟨hxu, hxs⟩, hu.inter isOpen_interior⟩ |>.trans_le
  gcongr
  exact interior_subset
/-
**MeasureTheory.Measure.support_restrict_subset** 是 Mathlib 中的一个引理，位于命名空间 `Measu
reTheory.Measure`。
形式化陈述：support_restrict_subset {s : Set X} : (μ.restrict s).support subseteq clos
ure s inter μ.support
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.subset_inter`：subset_inter {s t r : Set α} (rs : r subseteq s) (rt :
 r subseteq t) : r subseteq s inter t
· 使用引理 `MeasureTheory.Measure.support_subset_of_isClosed`：support_subset_of_isCl
osed {t : Set X} (ht : IsClosed t) (h : t in ae μ) : μ.support subseteq t
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.mem_ae_iff`：mem_ae_iff {s : Set α} : s in ae μ ↔ μ sᶜ = 0
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `IsOpen.measurableSet`：IsOpen.measurableSet (h : IsOpen s) : MeasurableSe
t s
· 使用定理 `IsClosed.isOpen_compl`：∀ {X : Type u} {inst : TopologicalSpace X} {s : S
et X} [self : IsClosed s], IsOpen sᶜ
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Disjoint.eq_bot`：Disjoint.eq_bot : Disjoint a b -> a ⊓ b = ⊥
· 使用定理 `LE.le.disjoint_compl_left`：LE.le.disjoint_compl_left (h : b <= a) : Disj
oint aᶜ b
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `MeasureTheory.OuterMeasure.empty`：∀ {α : Type u_2} (self : MeasureTheory
.OuterMeasure α), self.measureOf ∅ = 0
· 使用引理 `MeasureTheory.Measure.support_mono`：support_mono {ν : Measure X} (h : μ 
<= ν) : μ.support subseteq ν.support
· 使用定理 `MeasureTheory.Measure.restrict_le_self`：restrict_le_self : μ.restrict s 
<= μ
-/
lemma support_restrict_subset {s : Set X} :
    (μ.restrict s).support ⊆ closure s ∩ μ.support := by
  refine Set.subset_inter (support_subset_of_isClosed isClosed_closure ?_)
    (support_mono restrict_le_self)
  rw [mem_ae_iff, μ.restrict_apply isClosed_closure.isOpen_compl.measurableSet]
  convert! μ.empty
  exact subset_closure.disjoint_compl_left.eq_bot

end Restrict

end Measure

end MeasureTheory

end Support

