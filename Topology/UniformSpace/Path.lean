/-
Copyright (c) 2025 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Topology.Path
public import Mathlib.Topology.UniformSpace.CompactConvergence
public import Mathlib.Topology.UniformSpace.HeineCantor
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Topology.ContinuousMap.Interval

/-!
# Paths in uniform spaces

In this file we define a `UniformSpace` structure on `Path`s
between two points in a uniform space
and prove that various functions associated with `Path`s are uniformly continuous.

The uniform space structure is induced from the space of continuous maps `C(I, X)`,
and corresponds to uniform convergence of paths on `I`, see `Path.hasBasis_uniformity`.
-/

public section

open scoped unitInterval Topology Uniformity

variable {X : Type*} [UniformSpace X] {x y z : X}

namespace Path

/-
**Path.instUniformSpace** 是 Mathlib 中的一个实例，位于命名空间 `Path`。
形式化陈述：instUniformSpace : UniformSpace (Path x y)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instUniformSpace : UniformSpace (Path x y) :=
  .comap ((↑) : _ → C(I, X)) ContinuousMap.compactConvergenceUniformSpace
/-
**Path.isUniformEmbedding_coe** 是 Mathlib 中的一个定理，位于命名空间 `Path`。
形式化陈述：isUniformEmbedding_coe : IsUniformEmbedding ((↑) : Path x y -> C(I, X)) wh
ere comap_uniformity
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.coe_injective'`：∀ {X : Type u_1} {Y : Type u_2} [inst : To
pologicalSpace X] [inst_1 : TopologicalSpace Y] {F : Type u_3}   [inst_2 : FunLi
ke F X Y] [inst_3 …
-/
theorem isUniformEmbedding_coe : IsUniformEmbedding ((↑) : Path x y → C(I, X)) where
  comap_uniformity := rfl
  injective := ContinuousMap.coe_injective'
/-
**Path.uniformContinuous** 是 Mathlib 中的一个定理，位于命名空间 `Path`。
形式化陈述：uniformContinuous (γ : Path x y) : UniformContinuous γ
参数：γ : Path x y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CompactSpace.uniformContinuous_of_continuous`：CompactSpace.uniformContin
uous_of_continuous [CompactSpace α] {f : α -> β} (h : Continuous f) : UniformCon
tinuous f
· 使用定理 `ConditionallyCompleteLinearOrder.toCompactIccSpace`：∀ (α : Type u_2) [in
st : ConditionallyCompleteLinearOrder α] [inst_1 : TopologicalSpace α] [OrderTop
ology α],   CompactIccSpace α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `ContinuousMapClass.map_continuous`：∀ {F : Type u_1} {X : outParam (Type 
u_2)} {Y : outParam (Type u_3)} {inst : TopologicalSpace X}   {inst_1 : Topologi
calSpace Y} {inst_2 : F…
-/
theorem uniformContinuous (γ : Path x y) : UniformContinuous γ :=
  CompactSpace.uniformContinuous_of_continuous <| map_continuous _

/-- Given a path `γ`, it extension to the real line `γ.extend : C(ℝ, X)`
is a uniformly continuous function. -/
/-
**Path.uniformContinuous_extend** 是 Mathlib 中的一个定理，位于命名空间 `Path`。
形式化陈述：uniformContinuous_extend (γ : Path x y) : UniformContinuous γ.extend
参数：γ : Path x y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuous.comp`：∀ {α : Type ua} {β : Type ub} {γ : Type uc} [ins
t : UniformSpace α] [inst_1 : UniformSpace β] [inst_2 : UniformSpace γ]   {g : β
 → γ} {f : α…
· 使用定理 `Path.uniformContinuous`：uniformContinuous (γ : Path x y) : UniformContin
uous γ
· 使用定理 `LipschitzWith.uniformContinuous`：∀ {α : Type u} {β : Type v} [inst : Pse
udoEMetricSpace α] [inst_1 : PseudoEMetricSpace β] {K : NNReal} {f : α → β},   L
ipschitzWith K f → Un…
· 使用定理 `LipschitzWith.projIcc`：∀ {a b : ℝ} (h : a ≤ b), LipschitzWith 1 (Set.pro
jIcc a b h)

--- 原说明 ---
Given a path `γ`, it extension to the real line `γ.extend : C(ℝ, X)`
is a uniformly continuous function.
-/
theorem uniformContinuous_extend (γ : Path x y) : UniformContinuous γ.extend :=
  γ.uniformContinuous.comp <| LipschitzWith.projIcc _ |>.uniformContinuous

/-- The function sending a path `γ` to its extension `γ.extend : ℝ → X`
is uniformly continuous in `γ`. -/
/-
**Path.uniformContinuous_extend_left** 是 Mathlib 中的一个定理，位于命名空间 `Path`。
形式化陈述：uniformContinuous_extend_left : UniformContinuous (Path.extend : Path x y 
-> C(Real, X))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuous.comp`：∀ {α : Type ua} {β : Type ub} {γ : Type uc} [ins
t : UniformSpace α] [inst_1 : UniformSpace β] [inst_2 : UniformSpace γ]   {g : β
 → γ} {f : α…
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `ContinuousMap.uniformContinuous_comp_left`：uniformContinuous_comp_left (
g : C(α, γ)) : UniformContinuous (fun f => f.comp g : C(γ, β) -> C(α, β))
· 使用定理 `IsUniformInducing.uniformContinuous`：IsUniformInducing.uniformContinuous
 {f : α -> β} (hf : IsUniformInducing f) : UniformContinuous f
· 使用定理 `IsUniformEmbedding.toIsUniformInducing`：∀ {α : Type ua} {β : Type ub} [i
nst : UniformSpace α] [inst_1 : UniformSpace β] {f : α → β},   IsUniformEmbeddin
g f → IsUniformInducing f
· 使用定理 `Path.isUniformEmbedding_coe`：isUniformEmbedding_coe : IsUniformEmbedding
 ((↑) : Path x y -> C(I, X)) where comap_uniformity

--- 原说明 ---
The function sending a path `γ` to its extension `γ.extend : ℝ → X`
is uniformly continuous in `γ`.
-/
theorem uniformContinuous_extend_left : UniformContinuous (Path.extend : Path x y → C(ℝ, X)) :=
  ContinuousMap.projIccCM.uniformContinuous_comp_left.comp isUniformEmbedding_coe.uniformContinuous

/-- If `{U i | p i}` form a basis of entourages of `X`,
then the entourages `{V i | p i}`, `V i = {(γ₁, γ₂) | ∀ t, (γ₁ t, γ₂ t) ∈ U i}`,
form a basis of entourages of paths between `x` and `y`. -/
/-
**Path._root_.Filter.HasBasis.uniformityPath** 是 Mathlib 中的一个定理，位于命名空间 `Path`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `{U i | p i}` form a basis of entourages of `X`,
then the entourages `{V i | p i}`, `V i = {(γ₁, γ₂) | ∀ t, (γ₁ t, γ₂ t) ∈ U i}`,
form a basis of entourages of paths between `x` and `y`.
-/
theorem _root_.Filter.HasBasis.uniformityPath {ι : Sort*} {p : ι → Prop} {U : ι → Set (X × X)}
    (hU : (𝓤 X).HasBasis p U) :
    (𝓤 (Path x y)).HasBasis p fun i ↦ {γ | ∀ t, (γ.1 t, γ.2 t) ∈ U i} :=
  hU.compactConvergenceUniformity_of_compact.comap _
/-
**Path.hasBasis_uniformity** 是 Mathlib 中的一个定理，位于命名空间 `Path`。
形式化陈述：hasBasis_uniformity : (𝓤 (Path x y)).HasBasis (· in 𝓤 X) ({γ | forall t, (
γ.1 t, γ.2 t) in ·})
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.uniformityPath`：∀ {X : Type u_1} [inst : UniformSpace X]
 {x y : X} {ι : Sort u_2} {p : ι → Prop} {U : ι → Set (X × X)},   (uniformity X)
.HasBasis p U →     …
· 使用定理 `Filter.basis_sets`：basis_sets (l : Filter α) : l.HasBasis (fun s : Set α
 => s in l) id
-/
theorem hasBasis_uniformity :
    (𝓤 (Path x y)).HasBasis (· ∈ 𝓤 X) ({γ | ∀ t, (γ.1 t, γ.2 t) ∈ ·}) :=
  (𝓤 X).basis_sets.uniformityPath
/-
**Path.uniformContinuous_symm** 是 Mathlib 中的一个定理，位于命名空间 `Path`。
形式化陈述：uniformContinuous_symm : UniformContinuous (Path.symm : Path x y -> Path y
 x)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.HasBasis.uniformContinuous_iff`：Filter.HasBasis.uniformContinuous
_iff {ι'} {p : ι -> Prop} {s : ι -> SetRel α α} (ha : (𝓤 α).HasBasis p s) {q : ι
' -> Prop} {t : ι' -> Set (…
· 使用定理 `Path.hasBasis_uniformity`：hasBasis_uniformity : (𝓤 (Path x y)).HasBasis 
(· in 𝓤 X) ({γ | forall t, (γ.1 t, γ.2 t) in ·})
-/
theorem uniformContinuous_symm : UniformContinuous (Path.symm : Path x y → Path y x) :=
  hasBasis_uniformity.uniformContinuous_iff hasBasis_uniformity |>.mpr fun U hU ↦
    ⟨U, hU, fun _ _ h x ↦ h (σ x)⟩

/-- The function `Path.trans` that concatenates two paths `γ₁ : Path x y` and `γ₂ : Path y z`
is uniformly continuous in `(γ₁, γ₂)`. -/
/-
**Path.uniformContinuous_trans** 是 Mathlib 中的一个定理，位于命名空间 `Path`。
形式化陈述：uniformContinuous_trans : UniformContinuous (Path.trans : Path x y -> Path
 y z -> Path x z).uncurry
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.HasBasis.uniformContinuous_iff`：Filter.HasBasis.uniformContinuous
_iff {ι'} {p : ι -> Prop} {s : ι -> SetRel α α} (ha : (𝓤 α).HasBasis p s) {q : ι
' -> Prop} {t : ι' -> Set (…
· 使用定理 `Filter.HasBasis.uniformity_prod`：Filter.HasBasis.uniformity_prod {ιa ιb 
: Type*} [UniformSpace α] [UniformSpace β] {pa : ιa -> Prop} {pb : ιb -> Prop} {
sa : ιa -> SetRel α α…
· 使用定理 `Path.hasBasis_uniformity`：hasBasis_uniformity : (𝓤 (Path x y)).HasBasis 
(· in 𝓤 X) ({γ | forall t, (γ.1 t, γ.2 t) in ·})
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `unitInterval.mul_pos_mem_iff`：mul_pos_mem_iff {a t : Real} (ha : 0 < a) 
: a * t in I ↔ t in Set.Icc (0 : Real) (1 / a)
· 使用定理 `zero_lt_two`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : Part
ialOrder α] [ZeroLEOneClass α] [NeZero 1] [AddLeftMono α],   0 < 2
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `unitInterval.two_mul_sub_one_mem_iff`：two_mul_sub_one_mem_iff {t : Real}
 : 2 * t - 1 in I ↔ t in Set.Icc (1 / 2 : Real) 1
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Path.trans_apply`：trans_apply (γ : Path x y) (γ' : Path y z) (t : I) : (
γ.trans γ') t = if h : (t : Real) <= 1 / 2 then γ ⟨2 * t, (mul_pos_mem_iff zero_
lt_two…
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `of_eq_false`：∀ {p : Prop}, p = False → ¬p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯

--- 原说明 ---
The function `Path.trans` that concatenates two paths `γ₁ : Path x y` and `γ₂ : 
Path y z`
is uniformly continuous in `(γ₁, γ₂)`.
-/
theorem uniformContinuous_trans :
    UniformContinuous (Path.trans : Path x y → Path y z → Path x z).uncurry :=
  hasBasis_uniformity.uniformity_prod hasBasis_uniformity
    |>.uniformContinuous_iff hasBasis_uniformity |>.mpr fun U hU ↦
      ⟨(U, U), ⟨hU, hU⟩, fun ⟨_, _⟩ ⟨_, _⟩ ⟨h₁, h₂⟩ t ↦ by
        by_cases ht : (t : ℝ) ≤ 2⁻¹ <;> simp [Path.trans_apply, ht, h₁ _, h₂ _]⟩

/-- The space of paths between two points in a complete uniform space
is a complete uniform space. -/
/-
**Path.instCompleteSpace** 是 Mathlib 中的一个实例，位于命名空间 `Path`。
形式化陈述：instCompleteSpace [CompleteSpace X] : CompleteSpace (Path x y)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUniformInducing.completeSpace`：∀ {α : Type u} {β : Type v} [inst : Uni
formSpace α] [inst_1 : UniformSpace β] {f : α → β},   IsUniformInducing f → IsCo
mplete (Set.range f) …
· 使用定理 `IsUniformEmbedding.toIsUniformInducing`：∀ {α : Type ua} {β : Type ub} [i
nst : UniformSpace α] [inst_1 : UniformSpace β] {f : α → β},   IsUniformEmbeddin
g f → IsUniformInducing f
· 使用定理 `Path.isUniformEmbedding_coe`：isUniformEmbedding_coe : IsUniformEmbedding
 ((↑) : Path x y -> C(I, X)) where comap_uniformity
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Path.range_coe`：range_coe : range ((↑) : Path x y -> C(I, X)) = {f | f 0
 = x ∧ f 1 = y}
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `unitInterval.instNontrivialElemReal`：Nontrivial ↑unitInterval
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `ContinuousMap.isComplete_setOfPred_eqOn`：isComplete_setOfPred_eqOn [Comp
leteSpace C(α, β)] (f : α -> β) (s : Set α) : IsComplete {g : C(α, β) | EqOn g f
 s}
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `proper_of_compact`：∀ {α : Type u} [inst : PseudoMetricSpace α] [CompactS
pace α], ProperSpace α
· 使用定理 `ConditionallyCompleteLinearOrder.toCompactIccSpace`：∀ (α : Type u_2) [in
st : ConditionallyCompleteLinearOrder α] [inst_1 : TopologicalSpace α] [OrderTop
ology α],   CompactIccSpace α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ

--- 原说明 ---
The space of paths between two points in a complete uniform space
is a complete uniform space.
-/
instance instCompleteSpace [CompleteSpace X] : CompleteSpace (Path x y) :=
  isUniformEmbedding_coe.completeSpace <| by simpa [Set.EqOn, range_coe]
    using ContinuousMap.isComplete_setOfPred_eqOn (Function.update (fun _ : I ↦ y) 0 x) {0, 1}

end Path

