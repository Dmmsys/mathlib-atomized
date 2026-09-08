/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Topology.ContinuousMap.Bounded.Star
public import Mathlib.Topology.ContinuousMap.Star
public import Mathlib.Topology.UniformSpace.Compact
public import Mathlib.Topology.CompactOpen
public import Mathlib.Topology.Sets.Compacts
public import Mathlib.Analysis.Normed.Group.InfiniteSum

/-!
# Continuous functions on a compact space

Continuous functions `C(α, β)` from a compact space `α` to a metric space `β`
are automatically bounded, and so acquire various structures inherited from `α →ᵇ β`.

This file transfers these structures, and restates some lemmas
characterising these structures.

If you need a lemma which is proved about `α →ᵇ β` but not for `C(α, β)` when `α` is compact,
you should restate it here. You can also use
`ContinuousMap.equivBoundedOfCompact` to move functions back and forth.
-/

@[expose] public section

noncomputable section

open NNReal BoundedContinuousFunction Set Metric

namespace ContinuousMap

variable {α β E : Type*}
variable [TopologicalSpace α] [CompactSpace α] [PseudoMetricSpace β] [SeminormedAddCommGroup E]

section

variable (α β)

/-- When `α` is compact, the bounded continuous maps `α →ᵇ β` are
equivalent to `C(α, β)`.
-/
@[simps -fullyApplied]
/-
**ContinuousMap.equivBoundedOfCompact** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMap`。
形式化陈述：equivBoundedOfCompact : C(α, β) ≃ (α ->ᵇ β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `α` is compact, the bounded continuous maps `α →ᵇ β` are
equivalent to `C(α, β)`.
-/
def equivBoundedOfCompact : C(α, β) ≃ (α →ᵇ β) :=
  ⟨mkOfCompact, BoundedContinuousFunction.toContinuousMap, fun f => by
    ext
    rfl, fun f => by
    ext
    rfl⟩
/-
**ContinuousMap.isUniformInducing_equivBoundedOfCompact** 是 Mathlib 中的一个定理，位于命名空
间 `ContinuousMap`。
形式化陈述：isUniformInducing_equivBoundedOfCompact : IsUniformInducing (equivBoundedO
fCompact α β)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUniformInducing.mk'`：IsUniformInducing.mk' {f : α -> β} (h : forall s,
 s in 𝓤 α ↔ exists t in 𝓤 β, forall x y : α, (f x, f y) in t -> (x, y) in s) : I
sUniformInd…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `ContinuousMap.hasBasis_compactConvergenceUniformity`：hasBasis_compactCon
vergenceUniformity : HasBasis (𝓤 C(α, β)) (fun p : Set α × Set (β × β) => IsComp
act p.1 ∧ p.2 in 𝓤 β) fun p => { fg : C(α…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Metric.uniformity_basis_dist_le`：uniformity_basis_dist_le : (𝓤 α).HasBas
is ((0 : Real) < ·) fun ε => { p : α × α | dist p.1 p.2 <= ε }
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `BoundedContinuousFunction.dist_le`：dist_le (C0 : (0 : Real) <= C) : dist
 f g <= C ↔ forall x : α, dist (f x) (g x) <= C
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `isCompact_univ`：isCompact_univ [h : CompactSpace X] : IsCompact (univ : 
Set X)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
-/
theorem isUniformInducing_equivBoundedOfCompact : IsUniformInducing (equivBoundedOfCompact α β) :=
  IsUniformInducing.mk'
    (by
      simp only [hasBasis_compactConvergenceUniformity.mem_iff, uniformity_basis_dist_le.mem_iff]
      exact fun s =>
        ⟨fun ⟨⟨a, b⟩, ⟨_, ⟨ε, hε, hb⟩⟩, hs⟩ =>
          ⟨{ p | ∀ x, (p.1 x, p.2 x) ∈ b }, ⟨ε, hε, fun _ h x => hb ((dist_le hε.le).mp h x)⟩,
            fun f g h => hs fun x _ => h x⟩,
          fun ⟨_, ⟨ε, hε, ht⟩, hs⟩ =>
          ⟨⟨Set.univ, { p | dist p.1 p.2 ≤ ε }⟩, ⟨isCompact_univ, ⟨ε, hε, fun _ h => h⟩⟩,
            fun ⟨f, g⟩ h => hs _ _ (ht ((dist_le hε.le).mpr fun x => h x (mem_univ x)))⟩⟩)
/-
**ContinuousMap.isUniformEmbedding_equivBoundedOfCompact** 是 Mathlib 中的一个定理，位于命名
空间 `ContinuousMap`。
形式化陈述：isUniformEmbedding_equivBoundedOfCompact : IsUniformEmbedding (equivBounde
dOfCompact α β)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.isUniformInducing_equivBoundedOfCompact`：isUniformInducing
_equivBoundedOfCompact : IsUniformInducing (equivBoundedOfCompact α β)
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
-/
theorem isUniformEmbedding_equivBoundedOfCompact : IsUniformEmbedding (equivBoundedOfCompact α β) :=
  { isUniformInducing_equivBoundedOfCompact α β with
    injective := (equivBoundedOfCompact α β).injective }

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- When `α` is compact, the bounded continuous maps `α →ᵇ 𝕜` are
additively equivalent to `C(α, 𝕜)`.
-/
@[simps! -fullyApplied apply symm_apply]
/-
**ContinuousMap.addEquivBoundedOfCompact** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMa
p`。
形式化陈述：addEquivBoundedOfCompact [AddMonoid β] [LipschitzAdd β] : C(α, β) ≃+ (α ->
ᵇ β)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instBoundedAddOfLipschitzAdd`：∀ {R : Type u_1} [inst : PseudoMetricSpace
 R] [inst_1 : AddMonoid R] [LipschitzAdd R], BoundedAdd R
· 使用定理 `LipschitzAdd.continuousAdd`：∀ {β : Type u_2} [inst : PseudoMetricSpace β
] [inst_1 : AddMonoid β] [LipschitzAdd β], ContinuousAdd β
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
When `α` is compact, the bounded continuous maps `α →ᵇ 𝕜` are
additively equivalent to `C(α, 𝕜)`.
-/
def addEquivBoundedOfCompact [AddMonoid β] [LipschitzAdd β] : C(α, β) ≃+ (α →ᵇ β) :=
  ({ toContinuousMapAddMonoidHom α β, (equivBoundedOfCompact α β).symm with } :
    (α →ᵇ β) ≃+ C(α, β)).symm
/-
**ContinuousMap.instPseudoMetricSpace** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMap`。
形式化陈述：instPseudoMetricSpace : PseudoMetricSpace C(α, β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instPseudoMetricSpace : PseudoMetricSpace C(α, β) :=
  (isUniformEmbedding_equivBoundedOfCompact α β).comapPseudoMetricSpace _
/-
**ContinuousMap.instMetricSpace** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMap`。
形式化陈述：instMetricSpace {β : Type*} [MetricSpace β] : MetricSpace C(α, β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instMetricSpace {β : Type*} [MetricSpace β] :
    MetricSpace C(α, β) :=
  (isUniformEmbedding_equivBoundedOfCompact α β).comapMetricSpace _


/-- When `α` is compact, and `β` is a metric space, the bounded continuous maps `α →ᵇ β` are
isometric to `C(α, β)`.
-/
@[simps! -fullyApplied toEquiv apply symm_apply]
/-
**ContinuousMap.isometryEquivBoundedOfCompact** 是 Mathlib 中的一个定义，位于命名空间 `Continu
ousMap`。
形式化陈述：isometryEquivBoundedOfCompact : C(α, β) ≃ᵢ (α ->ᵇ β) where isometry_toFun 
_ _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `α` is compact, and `β` is a metric space, the bounded continuous maps `α →
ᵇ β` are
isometric to `C(α, β)`.
-/
def isometryEquivBoundedOfCompact : C(α, β) ≃ᵢ (α →ᵇ β) where
  isometry_toFun _ _ := rfl
  toEquiv := equivBoundedOfCompact α β

end

@[simp]
/-
**ContinuousMap._root_.BoundedContinuousFunction.dist_mkOfCompact** 是 Mathlib 中的
一个定理，位于命名空间 `ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.BoundedContinuousFunction.dist_mkOfCompact (f g : C(α, β)) :
    dist (mkOfCompact f) (mkOfCompact g) = dist f g :=
  rfl

@[simp]
/-
**ContinuousMap._root_.BoundedContinuousFunction.dist_toContinuousMap** 是 Mathli
b 中的一个定理，位于命名空间 `ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.BoundedContinuousFunction.dist_toContinuousMap (f g : α →ᵇ β) :
    dist f.toContinuousMap g.toContinuousMap = dist f g :=
  rfl

open BoundedContinuousFunction

section

variable {f g : C(α, β)} {C : ℝ}

/-- The pointwise distance is controlled by the distance between functions, by definition. -/
/-
**ContinuousMap.dist_apply_le_dist** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：dist_apply_le_dist (x : α) : dist (f x) (g x) <= dist f g
参数：x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p

--- 原说明 ---
The pointwise distance is controlled by the distance between functions, by defin
ition.
-/
theorem dist_apply_le_dist (x : α) : dist (f x) (g x) ≤ dist f g := by
  simp only [← dist_mkOfCompact, dist_coe_le_dist, ← mkOfCompact_apply]

/-- The distance between two functions is controlled by the supremum of the pointwise distances. -/
/-
**ContinuousMap.dist_le** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：dist_le (C0 : (0 : Real) <= C) : dist f g <= C ↔ forall x : α, dist (f x) 
(g x) <= C
参数：C0 : (0 : Real) <= C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `BoundedContinuousFunction.dist_le`：dist_le (C0 : (0 : Real) <= C) : dist
 f g <= C ↔ forall x : α, dist (f x) (g x) <= C
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
The distance between two functions is controlled by the supremum of the pointwis
e distances.
-/
theorem dist_le (C0 : (0 : ℝ) ≤ C) : dist f g ≤ C ↔ ∀ x : α, dist (f x) (g x) ≤ C := by
  simp only [← dist_mkOfCompact, BoundedContinuousFunction.dist_le C0, mkOfCompact_apply]
/-
**ContinuousMap.dist_le_iff_of_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap
`。
形式化陈述：dist_le_iff_of_nonempty [Nonempty α] : dist f g <= C ↔ forall x, dist (f x
) (g x) <= C
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem dist_le_iff_of_nonempty [Nonempty α] : dist f g ≤ C ↔ ∀ x, dist (f x) (g x) ≤ C := by
  simp only [← dist_mkOfCompact, BoundedContinuousFunction.dist_le_iff_of_nonempty,
    mkOfCompact_apply]
/-
**ContinuousMap.dist_lt_iff_of_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap
`。
形式化陈述：dist_lt_iff_of_nonempty [Nonempty α] : dist f g < C ↔ forall x : α, dist (
f x) (g x) < C
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem dist_lt_iff_of_nonempty [Nonempty α] : dist f g < C ↔ ∀ x : α, dist (f x) (g x) < C := by
  simp only [← dist_mkOfCompact, dist_lt_iff_of_nonempty_compact, mkOfCompact_apply]
/-
**ContinuousMap.dist_lt_of_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：dist_lt_of_nonempty [Nonempty α] (w : forall x : α, dist (f x) (g x) < C) 
: dist f g < C
参数：w : forall x : α, dist (f x) (g x) < C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ContinuousMap.dist_lt_iff_of_nonempty`：dist_lt_iff_of_nonempty [Nonempty
 α] : dist f g < C ↔ forall x : α, dist (f x) (g x) < C
-/
theorem dist_lt_of_nonempty [Nonempty α] (w : ∀ x : α, dist (f x) (g x) < C) : dist f g < C :=
  dist_lt_iff_of_nonempty.2 w
/-
**ContinuousMap.dist_lt_iff** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：dist_lt_iff (C0 : (0 : Real) < C) : dist f g < C ↔ forall x : α, dist (f x
) (g x) < C
参数：C0 : (0 : Real) < C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `BoundedContinuousFunction.dist_mkOfCompact`：∀ {α : Type u_1} {β : Type u
_2} [inst : TopologicalSpace α] [inst_1 : CompactSpace α] [inst_2 : PseudoMetric
Space β]   (f g : C(α, β)), dist…
· 使用定理 `BoundedContinuousFunction.dist_lt_iff_of_compact`：dist_lt_iff_of_compact
 [CompactSpace α] (C0 : (0 : Real) < C) : dist f g < C ↔ forall x : α, dist (f x
) (g x) < C
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem dist_lt_iff (C0 : (0 : ℝ) < C) : dist f g < C ↔ ∀ x : α, dist (f x) (g x) < C := by
  rw [← dist_mkOfCompact, dist_lt_iff_of_compact C0]
  simp only [mkOfCompact_apply]
/-
**ContinuousMap.dist_eq_iSup** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：dist_eq_iSup : dist f g = ⨆ x, dist (f x) (g x)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsometryEquiv.dist_eq`：∀ {α : Type u_3} {β : Type u_4} [inst : PseudoMet
ricSpace α] [inst_1 : PseudoMetricSpace β] (h : α ≃ᵢ β) (x y : α),   dist (h x) 
(h y) = dis…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `ContinuousMap.isometryEquivBoundedOfCompact_apply`：∀ (α : Type u_1) (β :
 Type u_2) [inst : TopologicalSpace α] [inst_1 : CompactSpace α] [inst_2 : Pseud
oMetricSpace β],   ⇑(ContinuousMap.isom…
· 使用定理 `BoundedContinuousFunction.dist_eq_iSup`：dist_eq_iSup : dist f g = ⨆ x : 
α, dist (f x) (g x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem dist_eq_iSup : dist f g = ⨆ x, dist (f x) (g x) := by
  simp [← isometryEquivBoundedOfCompact α β |>.dist_eq f g,
    BoundedContinuousFunction.dist_eq_iSup]
/-
**ContinuousMap.nndist_eq_iSup** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：nndist_eq_iSup : nndist f g = ⨆ x, nndist (f x) (g x)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsometryEquiv.nndist_eq`：∀ {α : Type u_3} {β : Type u_4} [inst : PseudoM
etricSpace α] [inst_1 : PseudoMetricSpace β] (h : α ≃ᵢ β) (x y : α),   nndist (h
 x) (h y) = n…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `ContinuousMap.isometryEquivBoundedOfCompact_apply`：∀ (α : Type u_1) (β :
 Type u_2) [inst : TopologicalSpace α] [inst_1 : CompactSpace α] [inst_2 : Pseud
oMetricSpace β],   ⇑(ContinuousMap.isom…
· 使用定理 `BoundedContinuousFunction.nndist_eq_iSup`：nndist_eq_iSup : nndist f g = 
⨆ x : α, nndist (f x) (g x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem nndist_eq_iSup : nndist f g = ⨆ x, nndist (f x) (g x) := by
  simp [← isometryEquivBoundedOfCompact α β |>.nndist_eq f g,
    BoundedContinuousFunction.nndist_eq_iSup]
/-
**ContinuousMap.edist_eq_iSup** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：edist_eq_iSup : edist f g = ⨆ (x : α), edist (f x) (g x)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsometryEquiv.edist_eq`：∀ {α : Type u} {β : Type v} [inst : PseudoEMetri
cSpace α] [inst_1 : PseudoEMetricSpace β] (h : α ≃ᵢ β) (x y : α),   edist (h x) 
(h y) = edis…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `ContinuousMap.isometryEquivBoundedOfCompact_apply`：∀ (α : Type u_1) (β :
 Type u_2) [inst : TopologicalSpace α] [inst_1 : CompactSpace α] [inst_2 : Pseud
oMetricSpace β],   ⇑(ContinuousMap.isom…
· 使用定理 `BoundedContinuousFunction.edist_eq_iSup`：edist_eq_iSup : edist f g = ⨆ x
, edist (f x) (g x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem edist_eq_iSup : edist f g = ⨆ (x : α), edist (f x) (g x) := by
  simp [← isometryEquivBoundedOfCompact α β |>.edist_eq f g,
    BoundedContinuousFunction.edist_eq_iSup]
/-
**ContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R} [Zero R] [Zero β] [PseudoMetricSpace R] [SMul R β] [IsBoundedSMul R β] :
    IsBoundedSMul R C(α, β) where
  dist_smul_pair' r f g := by
    simpa only [← dist_mkOfCompact] using! dist_smul_pair r (mkOfCompact f) (mkOfCompact g)
  dist_pair_smul' r₁ r₂ f := by
    simpa only [← dist_mkOfCompact] using! dist_pair_smul r₁ r₂ (mkOfCompact f)

end

-- TODO at some point we will need lemmas characterising this norm!
-- At the moment the only way to reason about it is to transfer `f : C(α,E)` back to `α →ᵇ E`.
/-
**ContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Norm C(α, E) where norm x := dist x 0

@[simp]
/-
**ContinuousMap._root_.BoundedContinuousFunction.norm_mkOfCompact** 是 Mathlib 中的
一个定理，位于命名空间 `ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.BoundedContinuousFunction.norm_mkOfCompact (f : C(α, E)) : ‖mkOfCompact f‖ = ‖f‖ :=
  rfl

@[simp]
/-
**ContinuousMap._root_.BoundedContinuousFunction.norm_toContinuousMap_eq** 是 Mat
hlib 中的一个定理，位于命名空间 `ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.BoundedContinuousFunction.norm_toContinuousMap_eq (f : α →ᵇ E) :
    ‖f.toContinuousMap‖ = ‖f‖ :=
  rfl

open BoundedContinuousFunction
/-
**ContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SeminormedAddCommGroup C(α, E) where
  __ := ContinuousMap.instPseudoMetricSpace _ _
  __ := ContinuousMap.instAddCommGroupContinuousMap
  dist_eq x y := by rw [← norm_mkOfCompact, ← dist_mkOfCompact, dist_eq_norm_neg_add,
    mkOfCompact_add, mkOfCompact_neg]
  dist := dist
  norm := norm
/-
**ContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {E : Type*} [NormedAddCommGroup E] : NormedAddCommGroup C(α, E) where
  __ : SeminormedAddCommGroup C(α, E) := inferInstance
  __ : MetricSpace C(α, E) := inferInstance
/-
**ContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Nonempty α] {E : Type*} [NormedAddCommGroup E] [Nontrivial E] :
    NontrivialTopology C(α, E) := by
  simpa [nontrivialTopology_iff_exists_norm_ne_zero] using exists_ne (0 : C(α, E))
/-
**ContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Nonempty α] [One E] [NormOneClass E] : NormOneClass C(α, E) where
  norm_one := by simp only [← norm_mkOfCompact, mkOfCompact_one, norm_one]

section

variable (f : C(α, E))

-- The corresponding lemmas for `BoundedContinuousFunction` are stated with `{f}`,
-- and so cannot be used in dot notation.
/-
**ContinuousMap.norm_coe_le_norm** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：norm_coe_le_norm (x : α) : ‖f x‖ <= ‖f‖
参数：x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BoundedContinuousFunction.norm_coe_le_norm`：norm_coe_le_norm (x : α) : ‖
f x‖ <= ‖f‖
-/
theorem norm_coe_le_norm (x : α) : ‖f x‖ ≤ ‖f‖ :=
  (mkOfCompact f).norm_coe_le_norm x

/-- Distance between the images of any two points is at most twice the norm of the function. -/
/-
**ContinuousMap.dist_le_two_norm** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：dist_le_two_norm (x y : α) : dist (f x) (f y) <= 2 * ‖f‖
参数：x y : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BoundedContinuousFunction.dist_le_two_norm`：dist_le_two_norm (x y : α) :
 dist (f x) (f y) <= 2 * ‖f‖

--- 原说明 ---
Distance between the images of any two points is at most twice the norm of the f
unction.
-/
theorem dist_le_two_norm (x y : α) : dist (f x) (f y) ≤ 2 * ‖f‖ :=
  (mkOfCompact f).dist_le_two_norm x y

/-- The norm of a function is controlled by the supremum of the pointwise norms. -/
/-
**ContinuousMap.norm_le** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：norm_le {C : Real} (C0 : (0 : Real) <= C) : ‖f‖ <= C ↔ forall x : α, ‖f x‖
 <= C
参数：C0 : (0 : Real) <= C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BoundedContinuousFunction.norm_le`：norm_le (C0 : (0 : Real) <= C) : ‖f‖ 
<= C ↔ forall x : α, ‖f x‖ <= C

--- 原说明 ---
The norm of a function is controlled by the supremum of the pointwise norms.
-/
theorem norm_le {C : ℝ} (C0 : (0 : ℝ) ≤ C) : ‖f‖ ≤ C ↔ ∀ x : α, ‖f x‖ ≤ C :=
  @BoundedContinuousFunction.norm_le _ _ _ _ (mkOfCompact f) _ C0
/-
**ContinuousMap.norm_le_of_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：norm_le_of_nonempty [Nonempty α] {M : Real} : ‖f‖ <= M ↔ forall x, ‖f x‖ <
= M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BoundedContinuousFunction.norm_le_of_nonempty`：norm_le_of_nonempty [None
mpty α] {f : α ->ᵇ β} {M : Real} : ‖f‖ <= M ↔ forall x, ‖f x‖ <= M
-/
theorem norm_le_of_nonempty [Nonempty α] {M : ℝ} : ‖f‖ ≤ M ↔ ∀ x, ‖f x‖ ≤ M :=
  @BoundedContinuousFunction.norm_le_of_nonempty _ _ _ _ _ (mkOfCompact f) _
/-
**ContinuousMap.norm_lt_iff** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：norm_lt_iff {M : Real} (M0 : 0 < M) : ‖f‖ < M ↔ forall x, ‖f x‖ < M
参数：M0 : 0 < M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BoundedContinuousFunction.norm_lt_iff_of_compact`：norm_lt_iff_of_compact
 [CompactSpace α] {f : α ->ᵇ β} {M : Real} (M0 : 0 < M) : ‖f‖ < M ↔ forall x, ‖f
 x‖ < M
-/
theorem norm_lt_iff {M : ℝ} (M0 : 0 < M) : ‖f‖ < M ↔ ∀ x, ‖f x‖ < M :=
  @BoundedContinuousFunction.norm_lt_iff_of_compact _ _ _ _ _ (mkOfCompact f) _ M0
/-
**ContinuousMap.nnnorm_lt_iff** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：nnnorm_lt_iff {M : Real>=0} (M0 : 0 < M) : ‖f‖₊ < M ↔ forall x : α, ‖f x‖₊
 < M
参数：M0 : 0 < M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.norm_lt_iff`：norm_lt_iff {M : Real} (M0 : 0 < M) : ‖f‖ < M
 ↔ forall x, ‖f x‖ < M
-/
theorem nnnorm_lt_iff {M : ℝ≥0} (M0 : 0 < M) : ‖f‖₊ < M ↔ ∀ x : α, ‖f x‖₊ < M :=
  f.norm_lt_iff M0
/-
**ContinuousMap.norm_lt_iff_of_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap
`。
形式化陈述：norm_lt_iff_of_nonempty [Nonempty α] {M : Real} : ‖f‖ < M ↔ forall x, ‖f x
‖ < M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BoundedContinuousFunction.norm_lt_iff_of_nonempty_compact`：norm_lt_iff_o
f_nonempty_compact [Nonempty α] [CompactSpace α] {f : α ->ᵇ β} {M : Real} : ‖f‖ 
< M ↔ forall x, ‖f x‖ < M
-/
theorem norm_lt_iff_of_nonempty [Nonempty α] {M : ℝ} : ‖f‖ < M ↔ ∀ x, ‖f x‖ < M :=
  @BoundedContinuousFunction.norm_lt_iff_of_nonempty_compact _ _ _ _ _ _ (mkOfCompact f) _
/-
**ContinuousMap.nnnorm_lt_iff_of_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousM
ap`。
形式化陈述：nnnorm_lt_iff_of_nonempty [Nonempty α] {M : Real>=0} : ‖f‖₊ < M ↔ forall x
, ‖f x‖₊ < M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.norm_lt_iff_of_nonempty`：norm_lt_iff_of_nonempty [Nonempty
 α] {M : Real} : ‖f‖ < M ↔ forall x, ‖f x‖ < M
-/
theorem nnnorm_lt_iff_of_nonempty [Nonempty α] {M : ℝ≥0} : ‖f‖₊ < M ↔ ∀ x, ‖f x‖₊ < M :=
  f.norm_lt_iff_of_nonempty
/-
**ContinuousMap.apply_le_norm** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：apply_le_norm (f : C(α, Real)) (x : α) : f x <= ‖f‖
参数：f : C(α, Real)；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `le_abs`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LinearOrder α] {a
 b : α}, a ≤ |b| ↔ a ≤ b ∨ a ≤ -b
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `ContinuousMap.norm_coe_le_norm`：norm_coe_le_norm (x : α) : ‖f x‖ <= ‖f‖
-/
theorem apply_le_norm (f : C(α, ℝ)) (x : α) : f x ≤ ‖f‖ :=
  le_trans (le_abs.mpr (Or.inl (le_refl (f x)))) (f.norm_coe_le_norm x)
/-
**ContinuousMap.neg_norm_le_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：neg_norm_le_apply (f : C(α, Real)) (x : α) : -‖f‖ <= f x
参数：f : C(α, Real)；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `neg_le_neg`：∀ {α : Type u} [inst : AddCommGroup α] [inst_1 : PartialOrde
r α] [IsOrderedAddMonoid α] {a b : α}, a ≤ b → -b ≤ -a
· 使用定理 `ContinuousMap.norm_coe_le_norm`：norm_coe_le_norm (x : α) : ‖f x‖ <= ‖f‖
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `neg_le`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddLeftMono 
α] [AddRightMono α] {a b : α}, -a ≤ b ↔ -b ≤ a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `neg_le_abs`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (a
 : α), -a ≤ |a|
-/
theorem neg_norm_le_apply (f : C(α, ℝ)) (x : α) : -‖f‖ ≤ f x :=
  le_trans (neg_le_neg (f.norm_coe_le_norm x)) (neg_le.mp (neg_le_abs (f x)))
/-
**ContinuousMap.nnnorm_eq_iSup_nnnorm** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：nnnorm_eq_iSup_nnnorm : ‖f‖₊ = ⨆ x : α, ‖f x‖₊
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BoundedContinuousFunction.nnnorm_eq_iSup_nnnorm`：nnnorm_eq_iSup_nnnorm :
 ‖f‖₊ = ⨆ x : α, ‖f x‖₊
-/
theorem nnnorm_eq_iSup_nnnorm : ‖f‖₊ = ⨆ x : α, ‖f x‖₊ :=
  (mkOfCompact f).nnnorm_eq_iSup_nnnorm
/-
**ContinuousMap.norm_eq_iSup_norm** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：norm_eq_iSup_norm : ‖f‖ = ⨆ x : α, ‖f x‖
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BoundedContinuousFunction.norm_eq_iSup_norm`：norm_eq_iSup_norm : ‖f‖ = ⨆
 x : α, ‖f x‖
-/
theorem norm_eq_iSup_norm : ‖f‖ = ⨆ x : α, ‖f x‖ :=
  (mkOfCompact f).norm_eq_iSup_norm
/-
**ContinuousMap.enorm_eq_iSup_enorm** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：enorm_eq_iSup_enorm : ‖f‖ₑ = ⨆ x, ‖f x‖ₑ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BoundedContinuousFunction.enorm_eq_iSup_enorm`：enorm_eq_iSup_enorm : ‖f‖
ₑ = ⨆ x, ‖f x‖ₑ
-/
theorem enorm_eq_iSup_enorm : ‖f‖ₑ = ⨆ x, ‖f x‖ₑ :=
  (mkOfCompact f).enorm_eq_iSup_enorm

-- A version with better keys
/-
**ContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X : Type*} [TopologicalSpace X] (K : TopologicalSpace.Compacts X) :
    CompactSpace (K : Set X) :=
  TopologicalSpace.Compacts.instCompactSpaceSubtypeMem ..
/-
**ContinuousMap.norm_restrict_mono_set** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`
。
形式化陈述：norm_restrict_mono_set {X : Type*} [TopologicalSpace X] (f : C(X, E)) {K L
 : TopologicalSpace.Compacts X} (hKL : K <= L) : ‖f.restrict K‖ <= ‖f.restrict L
‖
参数：f : C(X, E)；hKL : K <= L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ContinuousMap.instCompactSpaceElemCoeCompacts`：∀ {X : Type u_4} [inst : 
TopologicalSpace X] (K : TopologicalSpace.Compacts X), CompactSpace ↑↑K
· 使用定理 `ContinuousMap.norm_le`：norm_le {C : Real} (C0 : (0 : Real) <= C) : ‖f‖ <
= C ↔ forall x : α, ‖f x‖ <= C
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `ContinuousMap.norm_coe_le_norm`：norm_coe_le_norm (x : α) : ‖f x‖ <= ‖f‖
-/
theorem norm_restrict_mono_set {X : Type*} [TopologicalSpace X] (f : C(X, E))
    {K L : TopologicalSpace.Compacts X} (hKL : K ≤ L) : ‖f.restrict K‖ ≤ ‖f.restrict L‖ :=
  (norm_le _ (norm_nonneg _)).mpr fun x => norm_coe_le_norm (f.restrict L) <| Set.inclusion hKL x
/-
**ContinuousMap.norm_eq_norm_coeFn** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousMap`。
形式化陈述：norm_eq_norm_coeFn [Fintype α] : ‖f‖ = ‖(f : α -> E)‖
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousMap.norm_le`：norm_le {C : Real} (C0 : (0 : Real) <= C) : ‖f‖ <
= C ↔ forall x : α, ‖f x‖ <= C
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `norm_le_pi_norm`：∀ {ι : Type u_1} {G : ι → Type u_4} [inst : Fintype ι] 
[inst_1 : (i : ι) → SeminormedAddGroup (G i)] (f : (i : ι) → G i)   (i : ι), ‖f 
i‖ ≤ …
· 使用定理 `pi_norm_le_iff_of_nonneg`：∀ {ι : Type u_1} {G : ι → Type u_4} [inst : Fi
ntype ι] [inst_1 : (i : ι) → SeminormedAddGroup (G i)] {x : (i : ι) → G i}   {r 
: ℝ}, 0 ≤ r → …
· 使用定理 `ContinuousMap.norm_coe_le_norm`：norm_coe_le_norm (x : α) : ‖f x‖ <= ‖f‖
-/
lemma norm_eq_norm_coeFn [Fintype α] : ‖f‖ = ‖(f : α → E)‖ := by
  apply le_antisymm
  · rw [ContinuousMap.norm_le _ (by positivity)]
    exact norm_le_pi_norm _
  · rw [pi_norm_le_iff_of_nonneg (by positivity)]
    exact f.norm_coe_le_norm

end

section

variable {R : Type*}

/-
**ContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonUnitalSeminormedRing R] : NonUnitalSeminormedRing C(α, R) where
  __ : SeminormedAddCommGroup C(α, R) := inferInstance
  __ : NonUnitalRing C(α, R) := inferInstance
  norm_mul_le f g := norm_mul_le (mkOfCompact f) (mkOfCompact g)
/-
**ContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonUnitalSeminormedCommRing R] : NonUnitalSeminormedCommRing C(α, R) where
  __ : NonUnitalSeminormedRing C(α, R) := inferInstance
  __ : NonUnitalCommRing C(α, R) := inferInstance
/-
**ContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SeminormedRing R] : SeminormedRing C(α, R) where
  __ : NonUnitalSeminormedRing C(α, R) := inferInstance
  __ : Ring C(α, R) := inferInstance
/-
**ContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SeminormedCommRing R] : SeminormedCommRing C(α, R) where
  __ : SeminormedRing C(α, R) := inferInstance
  __ : CommRing C(α, R) := inferInstance
/-
**ContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonUnitalNormedRing R] : NonUnitalNormedRing C(α, R) where
  __ : NormedAddCommGroup C(α, R) := inferInstance
  __ : NonUnitalSeminormedRing C(α, R) := inferInstance
/-
**ContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonUnitalNormedCommRing R] : NonUnitalNormedCommRing C(α, R) where
  __ : NonUnitalNormedRing C(α, R) := inferInstance
  __ : NonUnitalCommRing C(α, R) := inferInstance
/-
**ContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NormedRing R] : NormedRing C(α, R) where
  __ : NormedAddCommGroup C(α, R) := inferInstance
  __ : SeminormedRing C(α, R) := inferInstance
/-
**ContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NormedCommRing R] : NormedCommRing C(α, R) where
  __ : NormedRing C(α, R) := inferInstance
  __ : CommRing C(α, R) := inferInstance

end

section

variable {𝕜 : Type*} [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]

/-
**ContinuousMap.normedSpace** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMap`。
形式化陈述：normedSpace {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 E] : NormedSpace 𝕜 
C(α, E) where norm_smul_le
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance normedSpace {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 E] : NormedSpace 𝕜 C(α, E) where
  norm_smul_le := norm_smul_le

section

variable (α 𝕜 E)

/-- When `α` is compact and `𝕜` is a normed field,
the `𝕜`-algebra of bounded continuous maps `α →ᵇ β` is
`𝕜`-linearly isometric to `C(α, β)`.
-/
/-
**ContinuousMap.linearIsometryBoundedOfCompact** 是 Mathlib 中的一个定义，位于命名空间 `Contin
uousMap`。
形式化陈述：linearIsometryBoundedOfCompact : C(α, E) ≃ₗᵢ[𝕜] α ->ᵇ E
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.to_lipschitzAdd`：∀ {E : Type u_2} [inst : Seminor
medAddCommGroup E], LipschitzAdd E

--- 原说明 ---
When `α` is compact and `𝕜` is a normed field,
the `𝕜`-algebra of bounded continuous maps `α →ᵇ β` is
`𝕜`-linearly isometric to `C(α, β)`.
-/
def linearIsometryBoundedOfCompact : C(α, E) ≃ₗᵢ[𝕜] α →ᵇ E :=
  { addEquivBoundedOfCompact α E with
    map_smul' := fun c f => by
      ext
      norm_cast
    norm_map' := fun _ => rfl }

end

-- this lemma and the next are the analogues of those autogenerated by `@[simps]` for
-- `equivBoundedOfCompact`, `addEquivBoundedOfCompact`
@[simp]
/-
**ContinuousMap.linearIsometryBoundedOfCompact_symm_apply** 是 Mathlib 中的一个定理，位于命
名空间 `ContinuousMap`。
形式化陈述：linearIsometryBoundedOfCompact_symm_apply (f : α ->ᵇ E) : (linearIsometryB
oundedOfCompact α E 𝕜).symm f = f.toContinuousMap
参数：f : α ->ᵇ E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
-/
theorem linearIsometryBoundedOfCompact_symm_apply (f : α →ᵇ E) :
    (linearIsometryBoundedOfCompact α E 𝕜).symm f = f.toContinuousMap :=
  rfl

@[simp]
/-
**ContinuousMap.linearIsometryBoundedOfCompact_apply_apply** 是 Mathlib 中的一个定理，位于
命名空间 `ContinuousMap`。
形式化陈述：linearIsometryBoundedOfCompact_apply_apply (f : C(α, E)) (a : α) : (linear
IsometryBoundedOfCompact α E 𝕜 f) a = f a
参数：f : C(α, E)；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
-/
theorem linearIsometryBoundedOfCompact_apply_apply (f : C(α, E)) (a : α) :
    (linearIsometryBoundedOfCompact α E 𝕜 f) a = f a :=
  rfl

@[simp]
/-
**ContinuousMap.linearIsometryBoundedOfCompact_toIsometryEquiv** 是 Mathlib 中的一个定
理，位于命名空间 `ContinuousMap`。
形式化陈述：linearIsometryBoundedOfCompact_toIsometryEquiv : (linearIsometryBoundedOfC
ompact α E 𝕜).toIsometryEquiv = isometryEquivBoundedOfCompact α E
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
-/
theorem linearIsometryBoundedOfCompact_toIsometryEquiv :
    (linearIsometryBoundedOfCompact α E 𝕜).toIsometryEquiv = isometryEquivBoundedOfCompact α E :=
  rfl

@[simp]
/-
**ContinuousMap.linearIsometryBoundedOfCompact_toAddEquiv** 是 Mathlib 中的一个定理，位于命
名空间 `ContinuousMap`。
形式化陈述：linearIsometryBoundedOfCompact_toAddEquiv : ((linearIsometryBoundedOfCompa
ct α E 𝕜).toLinearEquiv : C(α, E) ≃+ (α ->ᵇ E)) = addEquivBoundedOfCompact α E
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `instBoundedAddOfLipschitzAdd`：∀ {R : Type u_1} [inst : PseudoMetricSpace
 R] [inst_1 : AddMonoid R] [LipschitzAdd R], BoundedAdd R
· 使用定理 `SeminormedAddCommGroup.to_lipschitzAdd`：∀ {E : Type u_2} [inst : Seminor
medAddCommGroup E], LipschitzAdd E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `SemilinearEquivClass.toAddEquivClass`：∀ {F : Type u_14} {R : outParam (T
ype u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S} 
  {σ : outParam (R →+* S)}…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
-/
theorem linearIsometryBoundedOfCompact_toAddEquiv :
    ((linearIsometryBoundedOfCompact α E 𝕜).toLinearEquiv : C(α, E) ≃+ (α →ᵇ E)) =
      addEquivBoundedOfCompact α E :=
  rfl

@[simp]
/-
**ContinuousMap.linearIsometryBoundedOfCompact_of_compact_toEquiv** 是 Mathlib 中的
一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：linearIsometryBoundedOfCompact_of_compact_toEquiv : (linearIsometryBounded
OfCompact α E 𝕜).toLinearEquiv.toEquiv = equivBoundedOfCompact α E
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
-/
theorem linearIsometryBoundedOfCompact_of_compact_toEquiv :
    (linearIsometryBoundedOfCompact α E 𝕜).toLinearEquiv.toEquiv = equivBoundedOfCompact α E :=
  rfl

end

/-
**ContinuousMap.nnnorm_smul_const** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：∀ {α : Type u_1} [inst : TopologicalSpace α] [inst_1 : CompactSpace α] {R 
: Type u_4} {β : Type u_5}   [inst_2 : SeminormedAddCommGroup β] [inst_3 : Semin
ormedRing R] [inst_4 : _root_.Module R β]   [inst_5 : NormSMulClass R β] (f : C(
α, R)) (b : β), ‖f • ContinuousMap.const α b‖₊ = ‖f‖₊ * ‖b‖₊
参数：f : C(α, R)；b : β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousMap.nnnorm_eq_iSup_nnnorm`：nnnorm_eq_iSup_nnnorm : ‖f‖₊ = ⨆ x 
: α, ‖f x‖₊
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `nnnorm_smul`：nnnorm_smul (r : α) (x : β) : ‖r • x‖₊ = ‖r‖₊ * ‖x‖₊
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `NNReal.iSup_mul`：iSup_mul (f : ι -> Real>=0) (a : Real>=0) : (⨆ i, f i) 
* a = ⨆ i, f i * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma nnnorm_smul_const {R β : Type*} [SeminormedAddCommGroup β] [SeminormedRing R]
    [Module R β] [NormSMulClass R β] (f : C(α, R)) (b : β) :
    ‖f • const α b‖₊ = ‖f‖₊ * ‖b‖₊ := by
  simp only [nnnorm_eq_iSup_nnnorm, smul_apply', const_apply, nnnorm_smul, iSup_mul]
/-
**ContinuousMap.norm_smul_const** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：∀ {α : Type u_1} [inst : TopologicalSpace α] [inst_1 : CompactSpace α] {R 
: Type u_4} {β : Type u_5}   [inst_2 : SeminormedAddCommGroup β] [inst_3 : Semin
ormedRing R] [inst_4 : _root_.Module R β]   [inst_5 : NormSMulClass R β] (f : C(
α, R)) (b : β), ‖f • ContinuousMap.const α b‖ = ‖f‖ * ‖b‖
参数：f : C(α, R)；b : β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousMap.nnnorm_smul_const`：∀ {α : Type u_1} [inst : TopologicalSpa
ce α] [inst_1 : CompactSpace α] {R : Type u_4} {β : Type u_5}   [inst_2 : Semino
rmedAddCommGroup β] […
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma norm_smul_const {R β : Type*} [SeminormedAddCommGroup β] [SeminormedRing R]
    [Module R β] [NormSMulClass R β] (f : C(α, R)) (b : β) :
    ‖f • const α b‖ = ‖f‖ * ‖b‖ := by
  simp only [← coe_nnnorm, NNReal.coe_mul, nnnorm_smul_const]

section NormSum

variable {R : Type*} [NonUnitalSeminormedRing R] [IsCancelMulZero R]

open BoundedContinuousFunction

/-- If the product of continuous functions on a compact space is zero, then the norm of their sum
is the maximum of their norms. -/
/-
**ContinuousMap.norm_add_eq_max** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousMap`。
形式化陈述：norm_add_eq_max {f g : C(α, R)} (h : f * g = 0) : ‖f + g‖ = max ‖f‖ ‖g‖
参数：α, R；h : f * g = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `instBoundedMul`：∀ {R : Type u_1} [inst : NonUnitalSeminormedRing R], Bou
ndedMul R
· 使用定理 `BoundedContinuousFunction.ext`：ext (h : forall x, f x = g x) : f = g
· 使用定理 `IsRightCancelMulZero.to_noZeroDivisors`：∀ (M₀ : Type u_1) [inst : MulZer
oClass M₀] [IsRightCancelMulZero M₀], NoZeroDivisors M₀
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `BoundedContinuousFunction.norm_add_eq_max`：norm_add_eq_max [IsCancelMulZ
ero R] {f g : α ->ᵇ R} (h : f * g = 0) : ‖f + g‖ = max ‖f‖ ‖g‖

--- 原说明 ---
If the product of continuous functions on a compact space is zero, then the norm
 of their sum
is the maximum of their norms.
-/
lemma norm_add_eq_max {f g : C(α, R)} (h : f * g = 0) :
    ‖f + g‖ = max ‖f‖ ‖g‖ := by
  replace h : mkOfCompact f * mkOfCompact g = 0 := by ext x; simpa using! congr($h x)
  simpa using! BoundedContinuousFunction.norm_add_eq_max h

/-- If the product of continuous functions on a compact space is zero, then the norm of their sum
is the maximum of their norms. -/
/-
**ContinuousMap.nnnorm_add_eq_max** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousMap`。
形式化陈述：nnnorm_add_eq_max {f g : C(α, R)} (h : f * g = 0) : ‖f + g‖₊ = max ‖f‖₊ ‖g
‖₊
参数：α, R；h : f * g = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用引理 `ContinuousMap.norm_add_eq_max`：norm_add_eq_max {f g : C(α, R)} (h : f * 
g = 0) : ‖f + g‖ = max ‖f‖ ‖g‖

--- 原说明 ---
If the product of continuous functions on a compact space is zero, then the norm
 of their sum
is the maximum of their norms.
-/
lemma nnnorm_add_eq_max {f g : C(α, R)} (h : f * g = 0) :
    ‖f + g‖₊ = max ‖f‖₊ ‖g‖₊ :=
  NNReal.eq <| norm_add_eq_max h
/-
**ContinuousMap.norm_sub_eq_max** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousMap`。
形式化陈述：norm_sub_eq_max {f g : C(α, R)} (h : f * g = 0) : ‖f - g‖ = max ‖f‖ ‖g‖
参数：α, R；h : f * g = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsSemitopologicalRing.toContinuousNeg`：∀ {R : Type u_2} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopologicalRing R],
   ContinuousNeg R
· 使用定理 `norm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ =
 ‖a‖
· 使用引理 `ContinuousMap.norm_add_eq_max`：norm_add_eq_max {f g : C(α, R)} (h : f * 
g = 0) : ‖f + g‖ = max ‖f‖ ‖g‖
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
-/
lemma norm_sub_eq_max {f g : C(α, R)} (h : f * g = 0) :
    ‖f - g‖ = max ‖f‖ ‖g‖ := by
  simpa [sub_eq_add_neg] using norm_add_eq_max (f := f) (g := -g) (by simpa)
/-
**ContinuousMap.nnnorm_sub_eq_max** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousMap`。
形式化陈述：nnnorm_sub_eq_max {f g : C(α, R)} (h : f * g = 0) : ‖f - g‖₊ = max ‖f‖₊ ‖g
‖₊
参数：α, R；h : f * g = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用引理 `ContinuousMap.norm_sub_eq_max`：norm_sub_eq_max {f g : C(α, R)} (h : f * 
g = 0) : ‖f - g‖ = max ‖f‖ ‖g‖
-/
lemma nnnorm_sub_eq_max {f g : C(α, R)} (h : f * g = 0) :
    ‖f - g‖₊ = max ‖f‖₊ ‖g‖₊ :=
  NNReal.eq <| norm_sub_eq_max h

open scoped Function in
/-- If the pairwise products of continuous functions on a compact space are all zero, then the norm
of their sum is the maximum of their norms. -/
/-
**ContinuousMap.nnnorm_sum_eq_sup** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousMap`。
形式化陈述：nnnorm_sum_eq_sup {ι : Type*} {f : ι -> C(α, R)} (s : Finset ι) (h : Pairw
ise ((· * · = 0) on f)) : ‖∑ i in s, f i‖₊ = s.sup (‖f ·‖₊)
参数：α, R；s : Finset ι；h : Pairwise ((· * · = 0) on f)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nnnorm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖₊ = 0
· 使用定理 `Finset.sup_empty`：sup_empty : (∅ : Finset β).sup f = ⊥
· 使用定理 `bot_eq_zero'`：∀ {α : Type u} [inst : AddMonoid α] [inst_1 : LinearOrder 
α] [CanonicallyOrderedAdd α] [inst_3 : OrderBot α], ⊥ = 0
· 使用定理 `NNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd NNReal
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用定理 `Finset.sum_eq_zero`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst
 : AddCommMonoid M] {f : ι → M},   (∀ x ∈ s, f x = 0) → ∑ x ∈ s, f x = 0
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Finset.sup_insert`：sup_insert [DecidableEq β] {b : β} : (insert b s : Fi
nset β).sup f = f b ⊔ s.sup f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ContinuousMap.nnnorm_add_eq_max`：nnnorm_add_eq_max {f g : C(α, R)} (h : 
f * g = 0) : ‖f + g‖₊ = max ‖f‖₊ ‖g‖₊

--- 原说明 ---
If the pairwise products of continuous functions on a compact space are all zero
, then the norm
of their sum is the maximum of their norms.
-/
lemma nnnorm_sum_eq_sup {ι : Type*} {f : ι → C(α, R)} (s : Finset ι)
    (h : Pairwise ((· * · = 0) on f)) :
    ‖∑ i ∈ s, f i‖₊ = s.sup (‖f ·‖₊) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    suffices f j * ∑ i ∈ s, f i = 0 by simpa [hj, ← ih] using nnnorm_add_eq_max this
    simpa [Finset.mul_sum] using Finset.sum_eq_zero fun i hi ↦ h (by grind)

end NormSum

section

variable {𝕜 : Type*} {γ : Type*} [NormedField 𝕜] [SeminormedRing γ] [NormedAlgebra 𝕜 γ]

/-
**ContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : NormedAlgebra 𝕜 C(α, γ) :=
  { ContinuousMap.normedSpace, ContinuousMap.algebra with }

end

end ContinuousMap

namespace ContinuousMap

section UniformContinuity

variable {α β : Type*}
variable [PseudoMetricSpace α] [CompactSpace α] [PseudoMetricSpace β]

/-!
We now set up some declarations making it convenient to use uniform continuity.
-/


/-
**ContinuousMap.uniform_continuity** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：uniform_continuity (f : C(α, β)) (ε : Real) (h : 0 < ε) : exists δ > 0, fo
rall {x y}, dist x y < δ -> dist (f x) (f y) < ε
参数：f : C(α, β)；ε : Real；h : 0 < ε。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Metric.uniformContinuous_iff`：uniformContinuous_iff [PseudoMetricSpace β
] {f : α -> β} : UniformContinuous f ↔ forall ε > 0, exists δ > 0, forall ⦃a b :
 α⦄, dist a b < δ …
· 使用定理 `CompactSpace.uniformContinuous_of_continuous`：CompactSpace.uniformContin
uous_of_continuous [CompactSpace α] {f : α -> β} (h : Continuous f) : UniformCon
tinuous f
· 使用定理 `ContinuousMap.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y] (f : C(X, Y)), Continuous ⇑f

--- 原说明 ---
We now set up some declarations making it convenient to use uniform continuity.
-/
theorem uniform_continuity (f : C(α, β)) (ε : ℝ) (h : 0 < ε) :
    ∃ δ > 0, ∀ {x y}, dist x y < δ → dist (f x) (f y) < ε :=
  Metric.uniformContinuous_iff.mp (CompactSpace.uniformContinuous_of_continuous f.continuous) ε h

-- This definition allows us to separate the choice of some `δ`,
-- and the corresponding use of `dist a b < δ → dist (f a) (f b) < ε`,
-- even across different declarations.
/-- An arbitrarily chosen modulus of uniform continuity for a given function `f` and `ε > 0`. -/
/-
**ContinuousMap.modulus** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMap`。
形式化陈述：modulus (f : C(α, β)) (ε : Real) (h : 0 < ε) : Real
参数：f : C(α, β)；ε : Real；h : 0 < ε。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.uniform_continuity`：uniform_continuity (f : C(α, β)) (ε : 
Real) (h : 0 < ε) : exists δ > 0, forall {x y}, dist x y < δ -> dist (f x) (f y)
 < ε

--- 原说明 ---
An arbitrarily chosen modulus of uniform continuity for a given function `f` and
 `ε > 0`.
-/
def modulus (f : C(α, β)) (ε : ℝ) (h : 0 < ε) : ℝ :=
  Classical.choose (uniform_continuity f ε h)
/-
**ContinuousMap.modulus_pos** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：modulus_pos (f : C(α, β)) {ε : Real} {h : 0 < ε} : 0 < f.modulus ε h
参数：f : C(α, β)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `ContinuousMap.uniform_continuity`：uniform_continuity (f : C(α, β)) (ε : 
Real) (h : 0 < ε) : exists δ > 0, forall {x y}, dist x y < δ -> dist (f x) (f y)
 < ε
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem modulus_pos (f : C(α, β)) {ε : ℝ} {h : 0 < ε} : 0 < f.modulus ε h :=
  (Classical.choose_spec (uniform_continuity f ε h)).1
/-
**ContinuousMap.dist_lt_of_dist_lt_modulus** 是 Mathlib 中的一个定理，位于命名空间 `Continuous
Map`。
形式化陈述：dist_lt_of_dist_lt_modulus (f : C(α, β)) (ε : Real) (h : 0 < ε) {a b : α} 
(w : dist a b < f.modulus ε h) : dist (f a) (f b) < ε
参数：f : C(α, β)；ε : Real；h : 0 < ε；w : dist a b < f.modulus ε h。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `ContinuousMap.uniform_continuity`：uniform_continuity (f : C(α, β)) (ε : 
Real) (h : 0 < ε) : exists δ > 0, forall {x y}, dist x y < δ -> dist (f x) (f y)
 < ε
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem dist_lt_of_dist_lt_modulus (f : C(α, β)) (ε : ℝ) (h : 0 < ε) {a b : α}
    (w : dist a b < f.modulus ε h) : dist (f a) (f b) < ε :=
  (Classical.choose_spec (uniform_continuity f ε h)).2 w

end UniformContinuity

end ContinuousMap

namespace ContinuousMap

section LocalNormalConvergence

/-! ### Local normal convergence

A sum of continuous functions (on a locally compact space) is "locally normally convergent" if the
sum of its sup-norms on any compact subset is summable. This implies convergence in the topology
of `C(X, E)` (i.e. locally uniform convergence). -/

open TopologicalSpace

variable {X : Type*} [TopologicalSpace X] [LocallyCompactSpace X]
variable {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]

/-
**ContinuousMap.summable_of_locally_summable_norm** 是 Mathlib 中的一个定理，位于命名空间 `Con
tinuousMap`。
形式化陈述：summable_of_locally_summable_norm {ι : Type*} {F : ι -> C(X, E)} (hF : for
all K : Compacts X, Summable fun i => ‖(F i).restrict K‖) : Summable F
参数：X, E；hF : forall K : Compacts X, Summable fun i => ‖(F i).restrict K‖。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.instCompactSpaceElemCoeCompacts`：∀ {X : Type u_4} [inst : 
TopologicalSpace X] (K : TopologicalSpace.Compacts X), CompactSpace ↑↑K
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContinuousMap.exists_tendsto_compactOpen_iff_forall`：exists_tendsto_comp
actOpen_iff_forall [WeaklyLocallyCompactSpace X] [T2Space Y] {ι : Type*} {l : Fi
lter ι} [Filter.NeBot l] (F : ι -> C(X, Y…
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `SummationFilter.instNeBotFinsetFilterOfNeBot`：∀ {β : Type u_2} (L : Summ
ationFilter β) [L.NeBot], L.filter.NeBot
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `TopologicalSpace.Compacts.instCanLiftSetCoeIsCompact`：∀ {α : Type u_1} [
inst : TopologicalSpace α], CanLift (Set α) (TopologicalSpace.Compacts α) SetLik
e.coe IsCompact
· 使用定理 `ContinuousMap.ext`：ext {f g : C(X, Y)} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `ContinuousMap.coe_sum`：∀ {α : Type u_1} {β : Type u_2} [inst : Topologic
alSpace α] [inst_1 : TopologicalSpace β] [inst_2 : AddCommMonoid β]   [inst_3 : 
ContinuousA…
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Summable.of_norm`：Summable.of_norm {f : ι -> E} (hf : Summable fun a => 
‖f a‖) : Summable f
· 使用定理 `instWeaklyLocallyCompactSpaceOfCompactSpace`：∀ {X : Type u_1} [inst : To
pologicalSpace X] [CompactSpace X], WeaklyLocallyCompactSpace X
-/
theorem summable_of_locally_summable_norm {ι : Type*} {F : ι → C(X, E)}
    (hF : ∀ K : Compacts X, Summable fun i => ‖(F i).restrict K‖) : Summable F := by
  refine (ContinuousMap.exists_tendsto_compactOpen_iff_forall _).2 fun K hK => ?_
  lift K to Compacts X using hK
  have A : ∀ s : Finset ι, restrict K (∑ i ∈ s, F i) = ∑ i ∈ s, restrict K (F i) := by
    intro s
    ext1 x
    -- TODO: there is a non-confluence problem in the lemmas here,
    -- and `SetLike.coe_sort_coe` prevents `restrict_apply` from being used.
    simp [-SetLike.coe_sort_coe]
  simpa only [HasSum, A] using! (hF K).of_norm

end LocalNormalConvergence

/-!
### Star structures

In this section, if `β` is a normed ⋆-group, then so is the space of
continuous functions from `α` to `β`, by using the star operation pointwise.

Furthermore, if `α` is compact and `β` is a C⋆-ring, then `C(α, β)` is a C⋆-ring. -/


section NormedSpace

variable {α : Type*} {β : Type*}
variable [TopologicalSpace α] [SeminormedAddCommGroup β] [StarAddMonoid β] [NormedStarGroup β]

/-
**ContinuousMap._root_.BoundedContinuousFunction.mkOfCompact_star** 是 Mathlib 中的
一个定理，位于命名空间 `ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.BoundedContinuousFunction.mkOfCompact_star [CompactSpace α] (f : C(α, β)) :
    mkOfCompact (star f) = star (mkOfCompact f) :=
  rfl
/-
**ContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CompactSpace α] : NormedStarGroup C(α, β) where
  norm_star_le f := by
    rw [← BoundedContinuousFunction.norm_mkOfCompact, BoundedContinuousFunction.mkOfCompact_star,
      norm_star, BoundedContinuousFunction.norm_mkOfCompact]

end NormedSpace

section CStarRing

variable {α : Type*} {β : Type*}
variable [TopologicalSpace α] [CompactSpace α]

/-
**ContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonUnitalNormedRing β] [StarRing β] [CStarRing β] : CStarRing C(α, β) where
  norm_mul_self_le f := by
    rw [← sq, ← Real.le_sqrt (norm_nonneg _) (norm_nonneg _),
      ContinuousMap.norm_le _ (Real.sqrt_nonneg _)]
    intro x
    rw [Real.le_sqrt (norm_nonneg _) (norm_nonneg _), sq, ← CStarRing.norm_star_mul_self]
    exact ContinuousMap.norm_coe_le_norm (star f * f) x

end CStarRing

end ContinuousMap

