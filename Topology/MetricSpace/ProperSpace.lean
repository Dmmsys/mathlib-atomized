/-
Copyright (c) 2018 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Topology.MetricSpace.Pseudo.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
public import Mathlib.Topology.MetricSpace.Pseudo.Pi
public import Mathlib.Topology.Order.IsLUB

/-! ## Proper spaces

## Main definitions and results
* `ProperSpace α`: a `PseudoMetricSpace` where all closed balls are compact

* `isCompact_sphere`: any sphere in a proper space is compact.
* `proper_of_compact`: compact spaces are proper.
* `secondCountable_of_proper`: proper spaces are sigma-compact, hence second countable.
* `locallyCompact_of_proper`: proper spaces are locally compact.
* `pi_properSpace`: finite products of proper spaces are proper.

-/

public section

open Set Filter

universe u v w

variable {α : Type u} {β : Type v} {X ι : Type*}

section ProperSpace

open Metric

/-- A pseudometric space is proper if all closed balls are compact. -/
/-
**ProperSpace** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u) → [PseudoMetricSpace α] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A pseudometric space is proper if all closed balls are compact.
-/
class ProperSpace (α : Type u) [PseudoMetricSpace α] : Prop where
  isCompact_closedBall : ∀ x : α, ∀ r, IsCompact (closedBall x r)

export ProperSpace (isCompact_closedBall)
attribute [compactness .] isCompact_closedBall

/-- In a proper pseudometric space, all spheres are compact. -/
@[compactness .]
/-
**isCompact_sphere** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCompact_sphere {α : Type*} [PseudoMetricSpace α] [ProperSpace α] (x : α)
 (r : Real) : IsCompact (sphere x r)
参数：x : α；r : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.of_isClosed_subset`：IsCompact.of_isClosed_subset (hs : IsCompa
ct s) (ht : IsClosed t) (h : t subseteq s) : IsCompact t
· 使用定理 `ProperSpace.isCompact_closedBall`：∀ {α : Type u} {inst : PseudoMetricSpa
ce α} [self : ProperSpace α] (x : α) (r : ℝ), IsCompact (Metric.closedBall x r)
· 使用引理 `Metric.isClosed_sphere`：isClosed_sphere : IsClosed (sphere x ε)
· 使用定理 `Metric.sphere_subset_closedBall`：sphere_subset_closedBall : sphere x ε s
ubseteq closedBall x ε

--- 原说明 ---
In a proper pseudometric space, all spheres are compact.
-/
theorem isCompact_sphere {α : Type*} [PseudoMetricSpace α] [ProperSpace α] (x : α) (r : ℝ) :
    IsCompact (sphere x r) :=
  (isCompact_closedBall x r).of_isClosed_subset isClosed_sphere sphere_subset_closedBall

/-- In a proper pseudometric space, any closed ball is a `CompactSpace` when considered as a
subtype. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In a proper pseudometric space, any closed ball is a `CompactSpace` when conside
red as a
subtype.
-/
instance {α : Type*} [PseudoMetricSpace α] [ProperSpace α] (x : α) (r : ℝ) :
    CompactSpace (closedBall x r) :=
  isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)

/-- In a proper pseudometric space, any sphere is a `CompactSpace` when considered as a subtype. -/
/-
**Metric.sphere.compactSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Metric.sphere.compactSpace {α : Type*} [PseudoMetricSpace α] [ProperSpace 
α] (x : α) (r : Real) : CompactSpace (sphere x r)
参数：x : α；r : Real。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isCompact_iff_compactSpace`：isCompact_iff_compactSpace : IsCompact s ↔ C
ompactSpace s
· 使用定理 `isCompact_sphere`：isCompact_sphere {α : Type*} [PseudoMetricSpace α] [Pr
operSpace α] (x : α) (r : Real) : IsCompact (sphere x r)

--- 原说明 ---
In a proper pseudometric space, any sphere is a `CompactSpace` when considered a
s a subtype.
-/
instance Metric.sphere.compactSpace {α : Type*} [PseudoMetricSpace α] [ProperSpace α]
    (x : α) (r : ℝ) : CompactSpace (sphere x r) :=
  isCompact_iff_compactSpace.mp (isCompact_sphere _ _)

variable [PseudoMetricSpace α]

-- see Note [lower instance priority]
/-- A proper pseudometric space is sigma compact, and therefore second countable. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A proper pseudometric space is sigma compact, and therefore second countable.
-/
instance (priority := 100) secondCountable_of_proper [ProperSpace α] :
    SecondCountableTopology α := by
  -- We already have `sigmaCompactSpace_of_locallyCompact_secondCountable`, so we don't
  -- add an instance for `SigmaCompactSpace`.
  suffices SigmaCompactSpace α from EMetric.secondCountable_of_sigmaCompact α
  rcases em (Nonempty α) with (⟨⟨x⟩⟩ | hn)
  · exact ⟨⟨fun n => closedBall x n, fun n => isCompact_closedBall _ _, iUnion_closedBall_nat _⟩⟩
  · exact ⟨⟨fun _ => ∅, fun _ => isCompact_empty, iUnion_eq_univ_iff.2 fun x => (hn ⟨x⟩).elim⟩⟩

/-- If all closed balls of large enough radius are compact, then the space is proper. Especially
useful when the lower bound for the radius is 0. -/
/-
**ProperSpace.of_isCompact_closedBall_of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ProperSpace.of_isCompact_closedBall_of_le (R : Real) (h : forall x : α, fo
rall r, R <= r -> IsCompact (closedBall x r)) : ProperSpace α
参数：R : Real；h : forall x : α, forall r, R <= r -> IsCompact (closedBall x r)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.of_isClosed_subset`：IsCompact.of_isClosed_subset (hs : IsCompa
ct s) (ht : IsClosed t) (h : t subseteq s) : IsCompact t
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
· 使用引理 `Metric.isClosed_closedBall`：isClosed_closedBall : IsClosed (closedBall x
 ε)
· 使用定理 `Metric.closedBall_subset_closedBall`：closedBall_subset_closedBall (h : ε
₁ <= ε₂) : closedBall x ε₁ subseteq closedBall x ε₂
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b

--- 原说明 ---
If all closed balls of large enough radius are compact, then the space is proper
. Especially
useful when the lower bound for the radius is 0.
-/
theorem ProperSpace.of_isCompact_closedBall_of_le (R : ℝ)
    (h : ∀ x : α, ∀ r, R ≤ r → IsCompact (closedBall x r)) : ProperSpace α :=
  ⟨fun x r => IsCompact.of_isClosed_subset (h x (max r R) (le_max_right _ _)) isClosed_closedBall
    (closedBall_subset_closedBall <| le_max_left _ _)⟩

/-- If there exists a sequence of compact closed balls with the same center
such that the radii tend to infinity, then the space is proper. -/
/-
**ProperSpace.of_seq_closedBall** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ProperSpace.of_seq_closedBall {β : Type*} {l : Filter β} [NeBot l] {x : α}
 {r : β -> Real} (hr : Tendsto r l atTop) (hc : forallᶠ i in l, IsCompact (close
dBall x (r i))) : ProperSpace α where isCompact_closedBall a r
参数：hr : Tendsto r l atTop；hc : forallᶠ i in l, IsCompact (closedBall x (r i))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α} [
f.NeBot], (∀ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x
· 使用定理 `Filter.Tendsto.eventually_ge_atTop`：∀ {α : Type u_3} {β : Type u_4} [ins
t : Preorder β] {f : α → β} {l : Filter α},   Filter.Tendsto f l Filter.atTop → 
∀ (c : β), ∀ᶠ (x : α) in…
· 使用定理 `IsCompact.of_isClosed_subset`：IsCompact.of_isClosed_subset (hs : IsCompa
ct s) (ht : IsClosed t) (h : t subseteq s) : IsCompact t
· 使用引理 `Metric.isClosed_closedBall`：isClosed_closedBall : IsClosed (closedBall x
 ε)
· 使用定理 `Metric.closedBall_subset_closedBall'`：closedBall_subset_closedBall' (h :
 ε₁ + dist x y <= ε₂) : closedBall x ε₁ subseteq closedBall y ε₂

--- 原说明 ---
If there exists a sequence of compact closed balls with the same center
such that the radii tend to infinity, then the space is proper.
-/
theorem ProperSpace.of_seq_closedBall {β : Type*} {l : Filter β} [NeBot l] {x : α} {r : β → ℝ}
    (hr : Tendsto r l atTop) (hc : ∀ᶠ i in l, IsCompact (closedBall x (r i))) :
    ProperSpace α where
  isCompact_closedBall a r :=
    let ⟨_i, hci, hir⟩ := (hc.and <| hr.eventually_ge_atTop <| r + dist a x).exists
    hci.of_isClosed_subset isClosed_closedBall <| closedBall_subset_closedBall' hir

-- A compact pseudometric space is proper
-- see Note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) proper_of_compact [CompactSpace α] : ProperSpace α :=
  ⟨fun _ _ => isClosed_closedBall.isCompact⟩

-- see Note [lower instance priority]
/-- A proper space is locally compact -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A proper space is locally compact
-/
instance (priority := 100) locallyCompact_of_proper [ProperSpace α] : LocallyCompactSpace α :=
  .of_hasBasis (fun _ => nhds_basis_closedBall) fun _ _ _ =>
    isCompact_closedBall _ _

-- see Note [lower instance priority]
/-- A proper space is complete -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A proper space is complete
-/
instance (priority := 100) complete_of_proper [ProperSpace α] : CompleteSpace α :=
  ⟨fun {f} hf => by
    /- We want to show that the Cauchy filter `f` is converging. It suffices to find a closed
      ball (therefore compact by properness) where it is nontrivial. -/
    obtain ⟨t, t_fset, ht⟩ : ∃ t ∈ f, ∀ x ∈ t, ∀ y ∈ t, dist x y < 1 :=
      (Metric.cauchy_iff.1 hf).2 1 zero_lt_one
    rcases hf.1.nonempty_of_mem t_fset with ⟨x, xt⟩
    have : closedBall x 1 ∈ f := mem_of_superset t_fset fun y yt => (ht y yt x xt).le
    rcases (isCompact_iff_totallyBounded_isComplete.1 (isCompact_closedBall x 1)).2 f hf
        (le_principal_iff.2 this) with
      ⟨y, -, hy⟩
    exact ⟨y, hy⟩⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ProperSpace ℝ where isCompact_closedBall _ _ :=
  Real.closedBall_eq_Icc ▸ ConditionallyCompleteLinearOrder.isCompact_Icc _ _

-- shortcut instance for performance reasons
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SecondCountableTopology ℝ := inferInstance

/-- A binary product of proper spaces is proper. -/
/-
**prod_properSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：prod_properSpace {α : Type*} {β : Type*} [PseudoMetricSpace α] [PseudoMetr
icSpace β] [ProperSpace α] [ProperSpace β] : ProperSpace (α × β) where isCompact
_closedBall
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `closedBall_prod_same`：closedBall_prod_same (x : α) (y : β) (r : Real) : 
closedBall x r ×ˢ closedBall y r = closedBall (x, y) r
· 使用定理 `IsCompact.prod`：IsCompact.prod {t : Set Y} (hs : IsCompact s) (ht : IsCo
mpact t) : IsCompact (s ×ˢ t)
· 使用定理 `ProperSpace.isCompact_closedBall`：∀ {α : Type u} {inst : PseudoMetricSpa
ce α} [self : ProperSpace α] (x : α) (r : ℝ), IsCompact (Metric.closedBall x r)

--- 原说明 ---
A binary product of proper spaces is proper.
-/
instance prod_properSpace {α : Type*} {β : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β]
    [ProperSpace α] [ProperSpace β] : ProperSpace (α × β) where
  isCompact_closedBall := by
    rintro ⟨x, y⟩ r
    rw [← closedBall_prod_same x y]
    exact (isCompact_closedBall x r).prod (isCompact_closedBall y r)

/-- A finite product of proper spaces is proper. -/
/-
**pi_properSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：pi_properSpace {X : β -> Type*} [Fintype β] [forall b, PseudoMetricSpace (
X b)] [h : forall b, ProperSpace (X b)] : ProperSpace (forall b, X b)
参数：X b；X b。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `ProperSpace.of_isCompact_closedBall_of_le`：ProperSpace.of_isCompact_clos
edBall_of_le (R : Real) (h : forall x : α, forall r, R <= r -> IsCompact (closed
Ball x r)) : ProperSpace α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `closedBall_pi`：closedBall_pi (x : forall b, X b) {r : Real} (hr : 0 <= r
) : closedBall x r = Set.pi univ fun b => closedBall (x b) r
· 使用定理 `isCompact_univ_pi`：isCompact_univ_pi {s : forall i, Set (X i)} (h : fora
ll i, IsCompact (s i)) : IsCompact (pi univ s)
· 使用定理 `ProperSpace.isCompact_closedBall`：∀ {α : Type u} {inst : PseudoMetricSpa
ce α} [self : ProperSpace α] (x : α) (r : ℝ), IsCompact (Metric.closedBall x r)

--- 原说明 ---
A finite product of proper spaces is proper.
-/
instance pi_properSpace {X : β → Type*} [Fintype β] [∀ b, PseudoMetricSpace (X b)]
    [h : ∀ b, ProperSpace (X b)] : ProperSpace (∀ b, X b) := by
  refine .of_isCompact_closedBall_of_le 0 fun x r hr => ?_
  rw [closedBall_pi _ hr]
  exact isCompact_univ_pi fun _ => isCompact_closedBall _ _

/-- A closed subspace of a proper space is proper.
This is true for any proper lipschitz map. See `LipschitzWith.properSpace`. -/
/-
**ProperSpace.of_isClosed** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ProperSpace.of_isClosed {X : Type*} [PseudoMetricSpace X] [ProperSpace X] 
{s : Set X} (hs : IsClosed s) : ProperSpace s
参数：hs : IsClosed s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Topology.IsEmbedding.isCompact_iff`：Topology.IsEmbedding.isCompact_iff {
f : X -> Y} (hf : IsEmbedding f) : IsCompact s ↔ IsCompact (f '' s)
· 使用引理 `Topology.IsEmbedding.subtypeVal`：Topology.IsEmbedding.subtypeVal : IsEmb
edding ((↑) : Subtype p -> X)
· 使用定理 `IsCompact.of_isClosed_subset`：IsCompact.of_isClosed_subset (hs : IsCompa
ct s) (ht : IsClosed t) (h : t subseteq s) : IsCompact t
· 使用定理 `ProperSpace.isCompact_closedBall`：∀ {α : Type u} {inst : PseudoMetricSpa
ce α} [self : ProperSpace α] (x : α) (r : ℝ), IsCompact (Metric.closedBall x r)
· 使用定理 `IsClosed.isClosedMap_subtype_val`：IsClosed.isClosedMap_subtype_val {s : 
Set X} (hs : IsClosed s) : IsClosedMap ((↑) : s -> X)
· 使用引理 `Metric.isClosed_closedBall`：isClosed_closedBall : IsClosed (closedBall x
 ε)
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
· 使用定理 `subset_rfl`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorde
r α] {a : α}, a ⊆ a

--- 原说明 ---
A closed subspace of a proper space is proper.
This is true for any proper lipschitz map. See `LipschitzWith.properSpace`.
-/
lemma ProperSpace.of_isClosed {X : Type*} [PseudoMetricSpace X] [ProperSpace X]
    {s : Set X} (hs : IsClosed s) :
    ProperSpace s :=
  ⟨fun x r ↦ Topology.IsEmbedding.subtypeVal.isCompact_iff.mpr
    ((isCompact_closedBall x.1 r).of_isClosed_subset
    (hs.isClosedMap_subtype_val _ isClosed_closedBall) (Set.image_subset_iff.mpr subset_rfl))⟩

end ProperSpace

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [PseudoMetricSpace X] [ProperSpace X] : ProperSpace (Additive X) := ‹ProperSpace X›
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [PseudoMetricSpace X] [ProperSpace X] : ProperSpace (Multiplicative X) := ‹ProperSpace X›
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [PseudoMetricSpace X] [ProperSpace X] : ProperSpace Xᵒᵈ := ‹ProperSpace X›
