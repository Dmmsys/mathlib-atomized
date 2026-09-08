/-
Copyright (c) 2025 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
module

public import Mathlib.Analysis.BoundedVariation
public import Mathlib.Order.SuccPred.IntervalSucc
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# Absolutely Continuous Functions

This file defines absolutely continuous functions on a closed interval `uIcc a b` and proves some
basic properties about absolutely continuous functions.

A function `f` is *absolutely continuous* on `uIcc a b` if for any `ε > 0`, there is `δ > 0` such
that for any finite disjoint collection of intervals `uIoc (a i) (b i)` for `i < n` where `a i`,
`b i` are all in `uIcc a b` for `i < n`, if `∑ i ∈ range n, dist (a i) (b i) < δ`, then
`∑ i ∈ range n, dist (f (a i)) (f (b i)) < ε`.

We give a filter version of the definition of absolutely continuous functions in
`AbsolutelyContinuousOnInterval` based on `AbsolutelyContinuousOnInterval.totalLengthFilter`
and `AbsolutelyContinuousOnInterval.disjWithin` and prove its equivalence with the `ε`-`δ`
definition in `absolutelyContinuousOnInterval_iff`.

We use the filter version to prove that absolutely continuous functions are closed under
* addition - `AbsolutelyContinuousOnInterval.add`;
* negation - `AbsolutelyContinuousOnInterval.neg`;
* subtraction - `AbsolutelyContinuousOnInterval.sub`;
* scalar multiplication - `AbsolutelyContinuousOnInterval.const_smul`,
  `AbsolutelyContinuousOnInterval.const_mul`;
* multiplication - `AbsolutelyContinuousOnInterval.smul`,
  `AbsolutelyContinuousOnInterval.mul`;

and that absolutely continuous implies uniformly continuous in
`AbsolutelyContinuousOnInterval.uniformContinuousOn`.

We use the `ε`-`δ` definition to prove that
* Lipschitz continuous functions are absolutely continuous -
  `LipschitzOnWith.absolutelyContinuousOnInterval`;
* absolutely continuous functions have bounded variation -
  `AbsolutelyContinuousOnInterval.boundedVariationOn`.

We conclude that
* absolutely continuous functions are a.e. differentiable -
  `AbsolutelyContinuousOnInterval.ae_differentiableAt`;
* if `f` is integrable on `uIcc a b`, then for any `c` in `uIcc a b`, `fun x ↦ ∫ v in c..x, f v`
  is absolutely continuous on `uIcc a b` -
  `IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral`.

## Tags
absolutely continuous
-/

@[expose] public section

variable {X F : Type*} [PseudoMetricSpace X] [SeminormedAddCommGroup F]

open Set Filter Function MeasureTheory

open scoped Topology NNReal

namespace AbsolutelyContinuousOnInterval

/-- The filter on the collection of all the finite sequences of `uIoc` intervals induced by the
function that maps the finite sequence of the intervals to the total length of the intervals.
Details:
1. Technically the filter is on `ℕ × (ℕ → X × X)`. A finite sequence `uIoc (a i) (b i)`, `i < n`
   is represented by any `E : ℕ × (ℕ → X × X)` which satisfies `E.1 = n` and `E.2 i = (a i, b i)`
   for `i < n`. Its total length is `∑ i ∈ Finset.range n, dist (a i) (b i)`.
2. For a sequence `G : ℕ → ℕ × (ℕ → X × X)`, convergence of `G` along `totalLengthFilter` means that
   the total length of `G j`, i.e., `∑ i ∈ Finset.range (G j).1, dist ((G j).2 i).1 ((G j).2 i).2)`,
   tends to `0` as `j` tends to infinity.
-/
/-
**AbsolutelyContinuousOnInterval.totalLengthFilter** 是 Mathlib 中的一个定义，位于命名空间 `Ab
solutelyContinuousOnInterval`。
形式化陈述：totalLengthFilter : Filter (Nat × (Nat -> X × X))
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The filter on the collection of all the finite sequences of `uIoc` intervals ind
uced by the
function that maps the finite sequence of the intervals to the total length of t
he intervals.
Details:
1. Technically the filter is on `ℕ × (ℕ → X × X)`. A finite sequence `uIoc (a i)
 (b i)`, `i < n`
   is represented by any `E : ℕ × (ℕ → X × X)` which satisfies `E.1 = n` and `E.
2 i = (a i, b i)`
   for `i < n`. Its total length is `∑ i ∈ Finset.range n, dist (a i) (b i)`.
2. For a sequence `G : ℕ → ℕ × (ℕ → X × X)`, convergence of `G` along `totalLeng
thFilter` means that
   the total length of `G j`, i.e., `∑ i ∈ Finset.range (G j).1, dist ((G j).2 i
).1 ((G j).2 i).2)`,
   tends to `0` as `j` tends to infinity.
-/
def totalLengthFilter : Filter (ℕ × (ℕ → X × X)) := Filter.comap
  (fun E ↦ ∑ i ∈ Finset.range E.1, dist (E.2 i).1 (E.2 i).2) (𝓝 0)
/-
**AbsolutelyContinuousOnInterval.hasBasis_totalLengthFilter** 是 Mathlib 中的一个引理，位
于命名空间 `AbsolutelyContinuousOnInterval`。
形式化陈述：hasBasis_totalLengthFilter : totalLengthFilter.HasBasis (fun (ε : Real) =>
 0 < ε) (fun (ε : Real) => {E : Nat × (Nat -> X × X) | ∑ i in Finset.range E.1, 
dist (E.2 i).1 (E.2 i).2 < ε})
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Finset.sum_nonneg`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈ s
, 0 ≤ f…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `dist_nonneg`：dist_nonneg {x y : α} : 0 <= dist x y
· 使用定理 `Filter.HasBasis.comap`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {l
 : Filter α} {p : ι → Prop} {s : ι → Set α} (f : β → α),   l.HasBasis p s → (Fil
ter.comap f…
· 使用定理 `nhds_basis_Ioo_pos`：∀ {α : Type u_1} [inst : TopologicalSpace α] [inst_1
 : AddCommGroup α] [inst_2 : LinearOrder α] [IsOrderedAddMonoid α]   [OrderTopol
ogy α] […
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
-/
lemma hasBasis_totalLengthFilter : totalLengthFilter.HasBasis (fun (ε : ℝ) => 0 < ε)
    (fun (ε : ℝ) =>
      {E : ℕ × (ℕ → X × X) | ∑ i ∈ Finset.range E.1, dist (E.2 i).1 (E.2 i).2 < ε}) := by
  convert! Filter.HasBasis.comap (α := ℝ) _ (nhds_basis_Ioo_pos _) using 1
  ext ε E
  simp only [mem_ofPred_eq, zero_sub, zero_add, mem_preimage, mem_Ioo, iff_and_self]
  suffices 0 ≤ ∑ i ∈ Finset.range E.1, dist (E.2 i).1 (E.2 i).2 by grind
  exact Finset.sum_nonneg (fun _ _ ↦ dist_nonneg)

/-- The subcollection of all the finite sequences of `uIoc` intervals consisting of
`uIoc (a i) (b i)`, `i < n` where `a i`, `b i` are all in `uIcc a b` for `i < n` and
`uIoc (a i) (b i)` are mutually disjoint for `i < n`. Technically the finite sequence
`uIoc (a i) (b i)`, `i < n` is represented by any `E : ℕ × (ℕ → ℝ × ℝ)` which satisfies
`E.1 = n` and `E.2 i = (a i, b i)` for `i < n`. -/
/-
**AbsolutelyContinuousOnInterval.disjWithin** 是 Mathlib 中的一个定义，位于命名空间 `Absolutel
yContinuousOnInterval`。
形式化陈述：disjWithin (a b : Real)
参数：a b : Real。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The subcollection of all the finite sequences of `uIoc` intervals consisting of
`uIoc (a i) (b i)`, `i < n` where `a i`, `b i` are all in `uIcc a b` for `i < n`
 and
`uIoc (a i) (b i)` are mutually disjoint for `i < n`. Technically the finite seq
uence
`uIoc (a i) (b i)`, `i < n` is represented by any `E : ℕ × (ℕ → ℝ × ℝ)` which sa
tisfies
`E.1 = n` and `E.2 i = (a i, b i)` for `i < n`.
-/
def disjWithin (a b : ℝ) := {E : ℕ × (ℕ → ℝ × ℝ) |
  (∀ i ∈ Finset.range E.1, (E.2 i).1 ∈ uIcc a b ∧ (E.2 i).2 ∈ uIcc a b) ∧
  Set.PairwiseDisjoint (Finset.range E.1) (fun i ↦ uIoc (E.2 i).1 (E.2 i).2)}
/-
**AbsolutelyContinuousOnInterval.disjWithin_comm** 是 Mathlib 中的一个引理，位于命名空间 `Abso
lutelyContinuousOnInterval`。
形式化陈述：disjWithin_comm (a b : Real) : disjWithin a b = disjWithin b a
参数：a b : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AbsolutelyContinuousOnInterval.disjWithin.eq_1`：∀ (a b : ℝ),   Absolutel
yContinuousOnInterval.disjWithin a b =     {E |       (∀ i ∈ Finset.range E.1, (
E.2 i).1 ∈ Set.uIcc a b ∧ (E.2 i).2 …
· 使用引理 `Set.uIcc_comm`：uIcc_comm (a b : α) : [[a, b]] = [[b, a]]
-/
lemma disjWithin_comm (a b : ℝ) : disjWithin a b = disjWithin b a := by
  rw [disjWithin, disjWithin, uIcc_comm]
/-
**AbsolutelyContinuousOnInterval.disjWithin_mono** 是 Mathlib 中的一个引理，位于命名空间 `Abso
lutelyContinuousOnInterval`。
形式化陈述：disjWithin_mono {a b c d : Real} (habcd : uIcc c d subseteq uIcc a b) : di
sjWithin c d subseteq disjWithin a b
参数：habcd : uIcc c d subseteq uIcc a b。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma disjWithin_mono {a b c d : ℝ} (habcd : uIcc c d ⊆ uIcc a b) :
    disjWithin c d ⊆ disjWithin a b := by
  grind [disjWithin]
/-
**AbsolutelyContinuousOnInterval.uIoc_subset_of_mem_disjWithin** 是 Mathlib 中的一个引
理，位于命名空间 `AbsolutelyContinuousOnInterval`。
形式化陈述：uIoc_subset_of_mem_disjWithin {a b : Real} {n : Nat} {I : Nat -> Real × Re
al} (hnI : (n, I) in disjWithin a b) {i : Nat} (hi : i < n) : uIoc (I i).1 (I i)
.2 subseteq uIoc a b
参数：hnI : (n, I) in disjWithin a b；hi : i < n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
-/
lemma uIoc_subset_of_mem_disjWithin {a b : ℝ} {n : ℕ} {I : ℕ → ℝ × ℝ}
    (hnI : (n, I) ∈ disjWithin a b) {i : ℕ} (hi : i < n) : uIoc (I i).1 (I i).2 ⊆ uIoc a b := by
  simp only [disjWithin, Finset.mem_range, mem_ofPred_eq, uIcc, mem_Icc] at hnI
  grind
/-
**AbsolutelyContinuousOnInterval.biUnion_uIoc_subset_of_mem_disjWithin** 是 Mathl
ib 中的一个引理，位于命名空间 `AbsolutelyContinuousOnInterval`。
形式化陈述：biUnion_uIoc_subset_of_mem_disjWithin {a b : Real} {n : Nat} {I : Nat -> R
eal × Real} (hnI : (n, I) in disjWithin a b) : (⋃ i in Finset.range n, uIoc (I i
).1 (I i).2) subseteq uIoc a b
参数：hnI : (n, I) in disjWithin a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用引理 `AbsolutelyContinuousOnInterval.uIoc_subset_of_mem_disjWithin`：uIoc_subse
t_of_mem_disjWithin {a b : Real} {n : Nat} {I : Nat -> Real × Real} (hnI : (n, I
) in disjWithin a b) {i : Nat} (hi : i < n) : uIoc…
-/
lemma biUnion_uIoc_subset_of_mem_disjWithin {a b : ℝ} {n : ℕ} {I : ℕ → ℝ × ℝ}
    (hnI : (n, I) ∈ disjWithin a b) :
    (⋃ i ∈ Finset.range n, uIoc (I i).1 (I i).2) ⊆ uIoc a b := by
  simp only [iUnion_subset_iff, Finset.mem_range]
  exact fun i hi ↦ uIoc_subset_of_mem_disjWithin hnI hi
/-
**AbsolutelyContinuousOnInterval.tendsto_volume_totalLengthFilter_nhds_zero** 是 
Mathlib 中的一个引理，位于命名空间 `AbsolutelyContinuousOnInterval`。
形式化陈述：tendsto_volume_totalLengthFilter_nhds_zero : Tendsto (fun E : Nat × (Nat -
> Real × Real) => volume (⋃ i in Finset.range E.1, uIoc (E.2 i).1 (E.2 i).2)) to
talLengthFilter (𝓝 0)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_of_tendsto_of_tendsto_of_le_of_le`：tendsto_of_tendsto_of_tendsto
_of_le_of_le [OrderTopology α] {f g h : β -> α} {b : Filter β} {a : α} (hg : Ten
dsto g b (𝓝 a)) (hh : Tendsto h…
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.ofReal_zero`：ENNReal.ofReal 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ENNReal.tendsto_ofReal`：tendsto_ofReal {f : Filter α} {m : α -> Real} {a
 : Real} (h : Tendsto m f (𝓝 a)) : Tendsto (fun a => ENNReal.ofReal (m a)) f (𝓝 
(ENNReal.ofR…
· 使用定理 `Filter.tendsto_comap`：tendsto_comap {f : α -> β} {x : Filter β} : Tendst
o f (comap f x) x
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `MeasureTheory.measure_biUnion_finset_le`：measure_biUnion_finset_le (I : 
Finset ι) (s : ι -> Set α) : μ (⋃ i in I, s i) <= ∑ i in I, μ (s i)
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `ENNReal.ofReal_sum_of_nonneg`：ofReal_sum_of_nonneg {s : Finset α} {f : α
 -> Real} (hf : forall i, i in s -> 0 <= f i) : ENNReal.ofReal (∑ i in s, f i) =
 ∑ i in s, ENNReal…
· 使用定理 `dist_nonneg`：dist_nonneg {x y : α} : 0 <= dist x y
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Real.volume_Ioc`：volume_Ioc {a b : Real} : volume (Ioc a b) = ofReal (b 
- a)
· 使用定理 `max_sub_min_eq_abs'`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : Line
arOrder α] [AddLeftMono α] [AddRightMono α] (a b : α),   max a b - min a b = |a 
- b|
（共 33 条，此处仅展示前 30 条）
-/
lemma tendsto_volume_totalLengthFilter_nhds_zero :
    Tendsto (fun E : ℕ × (ℕ → ℝ × ℝ) ↦ volume (⋃ i ∈ Finset.range E.1, uIoc (E.2 i).1 (E.2 i).2))
    totalLengthFilter (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (h := fun E ↦ ENNReal.ofReal (∑ i ∈ Finset.range E.1, (dist (E.2 i).1 (E.2 i).2)))
  · convert! ENNReal.tendsto_ofReal (Filter.tendsto_comap)
    simp
  · intro; simp
  · intro E
    simp only
    grw [measure_biUnion_finset_le]
    rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ ↦ dist_nonneg)]
    apply Eq.le
    apply Finset.sum_congr rfl
    simp [uIoc, Real.dist_eq, max_sub_min_eq_abs']
/-
**AbsolutelyContinuousOnInterval.tendsto_volume_restrict_totalLengthFilter_disjW
ithin_nhds_zero** 是 Mathlib 中的一个引理，位于命名空间 `AbsolutelyContinuousOnInterval`。
形式化陈述：tendsto_volume_restrict_totalLengthFilter_disjWithin_nhds_zero (a b : Real
) : Tendsto (fun E : Nat × (Nat -> Real × Real) => volume.restrict (uIoc a b) (⋃
 i in Finset.range E.1, uIoc (E.2 i).1 (E.2 i).2)) (totalLengthFilter ⊓ 𝓟 (disjW
ithin a b)) (𝓝 0)
参数：a b : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_of_tendsto_of_tendsto_of_le_of_le`：tendsto_of_tendsto_of_tendsto
_of_le_of_le [OrderTopology α] {f g h : β -> α} {b : Filter β} {a : α} (hg : Ten
dsto g b (𝓝 a)) (hh : Tendsto h…
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `Filter.Tendsto.mono_left`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x
 y : Filter α} {z : Filter β},   Filter.Tendsto f x z → y ≤ x → Filter.Tendsto f
 y z
· 使用引理 `AbsolutelyContinuousOnInterval.tendsto_volume_totalLengthFilter_nhds_zer
o`：tendsto_volume_totalLengthFilter_nhds_zero : Tendsto (fun E : Nat × (Nat -> R
eal × Real) => volume (⋃ i in Finset.range E.1, uIoc (E.2 i).1 …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.Measure.restrict_le_self`：restrict_le_self : μ.restrict s 
<= μ
-/
lemma tendsto_volume_restrict_totalLengthFilter_disjWithin_nhds_zero (a b : ℝ) :
    Tendsto (fun E : ℕ × (ℕ → ℝ × ℝ) ↦ volume.restrict (uIoc a b)
        (⋃ i ∈ Finset.range E.1, uIoc (E.2 i).1 (E.2 i).2))
      (totalLengthFilter ⊓ 𝓟 (disjWithin a b))
      (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (h := fun E : ℕ × (ℕ → ℝ × ℝ) ↦ volume (⋃ i ∈ Finset.range E.1, uIoc (E.2 i).1 (E.2 i).2))
  · apply tendsto_volume_totalLengthFilter_nhds_zero.mono_left
    simp
  · intro; simp
  · intro E
    simp only [Finset.mem_range]
    apply Measure.restrict_le_self

/-- `AbsolutelyContinuousOnInterval f a b`: A function `f` is *absolutely continuous* on `uIcc a b`
if the function which (intuitively) maps `uIoc (a i) (b i)`, `i < n` to
`∑ i ∈ Finset.range n, dist (f (a i)) (f (b i))` tendsto `𝓝 0` wrt `totalLengthFilter` restricted
to `disjWithin a b`. This is equivalent to the traditional `ε`-`δ` definition: for any `ε > 0`,
there is `δ > 0` such that for any finite disjoint collection of intervals `uIoc (a i) (b i)` for
`i < n` where `a i`, `b i` are all in `uIcc a b` for `i < n`, if
`∑ i ∈ range n, dist (a i) (b i) < δ`, then `∑ i ∈ range n, dist (f (a i)) (f (b i)) < ε`. -/
/-
**AbsolutelyContinuousOnInterval._root_.AbsolutelyContinuousOnInterval** 是 Mathl
ib 中的一个定义，位于命名空间 `AbsolutelyContinuousOnInterval`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`AbsolutelyContinuousOnInterval f a b`: A function `f` is *absolutely continuous
* on `uIcc a b`
if the function which (intuitively) maps `uIoc (a i) (b i)`, `i < n` to
`∑ i ∈ Finset.range n, dist (f (a i)) (f (b i))` tendsto `𝓝 0` wrt `totalLengthF
ilter` restricted
to `disjWithin a b`. This is equivalent to the traditional `ε`-`δ` definition: f
or any `ε > 0`,
there is `δ > 0` such that for any finite disjoint collection of intervals `uIoc
 (a i) (b i)` for
`i < n` where `a i`, `b i` are all in `uIcc a b` for `i < n`, if
`∑ i ∈ range n, dist (a i) (b i) < δ`, then `∑ i ∈ range n, dist (f (a i)) (f (b
 i)) < ε`.
-/
def _root_.AbsolutelyContinuousOnInterval (f : ℝ → X) (a b : ℝ) :=
  Tendsto (fun E ↦ ∑ i ∈ Finset.range E.1, dist (f (E.2 i).1) (f (E.2 i).2))
    (totalLengthFilter ⊓ 𝓟 (disjWithin a b)) (𝓝 0)

/-- The traditional `ε`-`δ` definition of absolutely continuous: A function `f` is
*absolutely continuous* on `uIcc a b` if for any `ε > 0`, there is `δ > 0` such that for
any finite disjoint collection of intervals `uIoc (a i) (b i)` for `i < n` where `a i`, `b i` are
all in `uIcc a b` for `i < n`, if `∑ i ∈ range n, dist (a i) (b i) < δ`, then
`∑ i ∈ range n, dist (f (a i)) (f (b i)) < ε`. -/
/-
**AbsolutelyContinuousOnInterval._root_.absolutelyContinuousOnInterval_iff** 是 M
athlib 中的一个定理，位于命名空间 `AbsolutelyContinuousOnInterval`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The traditional `ε`-`δ` definition of absolutely continuous: A function `f` is
*absolutely continuous* on `uIcc a b` if for any `ε > 0`, there is `δ > 0` such 
that for
any finite disjoint collection of intervals `uIoc (a i) (b i)` for `i < n` where
 `a i`, `b i` are
all in `uIcc a b` for `i < n`, if `∑ i ∈ range n, dist (a i) (b i) < δ`, then
`∑ i ∈ range n, dist (f (a i)) (f (b i)) < ε`.
-/
theorem _root_.absolutelyContinuousOnInterval_iff (f : ℝ → X) (a b : ℝ) :
    AbsolutelyContinuousOnInterval f a b ↔
    ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ E, E ∈ disjWithin a b →
    ∑ i ∈ Finset.range E.1, dist (E.2 i).1 (E.2 i).2 < δ →
    ∑ i ∈ Finset.range E.1, dist (f (E.2 i).1) (f (E.2 i).2) < ε := by
  simp [AbsolutelyContinuousOnInterval, Metric.tendsto_nhds,
    Filter.HasBasis.eventually_iff (hasBasis_totalLengthFilter.inf_principal _),
    imp.swap, abs_of_nonneg (Finset.sum_nonneg (fun _ _ ↦ dist_nonneg))]

variable {f g : ℝ → X} {a b c d : ℝ}
/-
**AbsolutelyContinuousOnInterval.symm** 是 Mathlib 中的一个定理，位于命名空间 `AbsolutelyConti
nuousOnInterval`。
形式化陈述：symm (hf : AbsolutelyContinuousOnInterval f a b) : AbsolutelyContinuousOnI
nterval f b a
参数：hf : AbsolutelyContinuousOnInterval f a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AbsolutelyContinuousOnInterval.disjWithin_comm`：disjWithin_comm (a b : R
eal) : disjWithin a b = disjWithin b a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
theorem symm (hf : AbsolutelyContinuousOnInterval f a b) :
    AbsolutelyContinuousOnInterval f b a := by
  simp_all [AbsolutelyContinuousOnInterval, disjWithin_comm]
/-
**AbsolutelyContinuousOnInterval.mono** 是 Mathlib 中的一个定理，位于命名空间 `AbsolutelyConti
nuousOnInterval`。
形式化陈述：mono (hf : AbsolutelyContinuousOnInterval f a b) (habcd : uIcc c d subsete
q uIcc a b) : AbsolutelyContinuousOnInterval f c d
参数：hf : AbsolutelyContinuousOnInterval f a b；habcd : uIcc c d subseteq uIcc a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Filter.map_mono`：map_mono : Monotone (map m)
· 使用定理 `inf_le_inf`：∀ {α : Type u} [inst : SemilatticeInf α] {a b c d : α}, b ≤ 
a → d ≤ c → b ⊓ d ≤ a ⊓ c
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Filter.principal_mono._gcongr_1`：∀ {α : Type u} {s t : Set α}, s ⊆ t → F
ilter.principal s ≤ Filter.principal t
· 使用引理 `AbsolutelyContinuousOnInterval.disjWithin_mono`：disjWithin_mono {a b c d
 : Real} (habcd : uIcc c d subseteq uIcc a b) : disjWithin c d subseteq disjWith
in a b
-/
theorem mono (hf : AbsolutelyContinuousOnInterval f a b) (habcd : uIcc c d ⊆ uIcc a b) :
    AbsolutelyContinuousOnInterval f c d := by
  simp only [AbsolutelyContinuousOnInterval, Tendsto] at *
  refine le_trans (Filter.map_mono ?_) hf
  gcongr; exact disjWithin_mono habcd

variable {f g : ℝ → F}

@[to_fun]
/-
**AbsolutelyContinuousOnInterval.add** 是 Mathlib 中的一个定理，位于命名空间 `AbsolutelyContin
uousOnInterval`。
形式化陈述：add (hf : AbsolutelyContinuousOnInterval f a b) (hg : AbsolutelyContinuous
OnInterval g a b) : AbsolutelyContinuousOnInterval (f + g) a b
参数：hf : AbsolutelyContinuousOnInterval f a b；hg : AbsolutelyContinuousOnInterval
 g a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `squeeze_zero`：squeeze_zero {α} {f g : α -> Real} {t₀ : Filter α} (hf : f
orall t, 0 <= f t) (hft : forall t, f t <= g t) (g0 : Tendsto g t₀ (𝓝 0)) : Tend
st…
· 使用定理 `Finset.sum_nonneg`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈ s
, 0 ≤ f…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `dist_nonneg`：dist_nonneg {x y : α} : 0 <= dist x y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_add_distrib`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [
inst : AddCommMonoid M] {f g : ι → M},   ∑ x ∈ s, (f x + g x) = ∑ x ∈ s, f x + ∑
 x ∈ s, g x
· 使用定理 `Finset.sum_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f g : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈
 s, f i…
· 使用定理 `dist_add_add_le`：∀ {E : Type u_2} [inst : SeminormedAddCommGroup E] (a₁ 
a₂ b₁ b₂ : E), dist (a₁ + a₂) (b₁ + b₂) ≤ dist a₁ b₁ + dist a₂ b₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Filter.Tendsto.add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst_1
 : Add M] [ContinuousAdd M] {α : Type u_2} {f g : α → M}   {x : Filter α} {a b :
 M},   F…
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
-/
theorem add (hf : AbsolutelyContinuousOnInterval f a b)
    (hg : AbsolutelyContinuousOnInterval g a b) :
    AbsolutelyContinuousOnInterval (f + g) a b := by
  apply squeeze_zero (fun t ↦ ?_) (fun t ↦ ?_) (by simpa using Tendsto.add hf hg)
  · exact Finset.sum_nonneg (fun i hi ↦ by positivity)
  · rw [← Finset.sum_add_distrib]
    gcongr
    exact dist_add_add_le _ _ _ _

@[to_fun]
/-
**AbsolutelyContinuousOnInterval.neg** 是 Mathlib 中的一个定理，位于命名空间 `AbsolutelyContin
uousOnInterval`。
形式化陈述：neg (hf : AbsolutelyContinuousOnInterval f a b) : AbsolutelyContinuousOnIn
terval (-f) a b
参数：hf : AbsolutelyContinuousOnInterval f a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `squeeze_zero`：squeeze_zero {α} {f g : α -> Real} {t₀ : Filter α} (hf : f
orall t, 0 <= f t) (hft : forall t, f t <= g t) (g0 : Tendsto g t₀ (𝓝 0)) : Tend
st…
· 使用定理 `Finset.sum_nonneg`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈ s
, 0 ≤ f…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `dist_nonneg`：dist_nonneg {x y : α} : 0 <= dist x y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `dist_neg_neg`：∀ {G : Type v} [inst : AddGroup G] [inst_1 : PseudoMetricS
pace G] [IsIsometricVAdd G G] [IsIsometricVAdd Gᵃᵒᵖ G]   (a b : G), dist (-a) (-
b)…
· 使用定理 `NormedAddGroup.to_isIsometricVAdd`：∀ {E : Type u_2} [inst : SeminormedAd
dGroup E], IsIsometricVAdd E E
· 使用定理 `NormedAddGroup.to_isIsometricVAdd_right`：∀ {E : Type u_2} [inst : Semino
rmedAddCommGroup E], IsIsometricVAdd Eᵃᵒᵖ E
-/
theorem neg (hf : AbsolutelyContinuousOnInterval f a b) :
    AbsolutelyContinuousOnInterval (-f) a b := by
  apply squeeze_zero (fun t ↦ ?_) (fun t ↦ ?_) (by simpa using! hf)
  · exact Finset.sum_nonneg (fun i hi ↦ by positivity)
  · simp

@[to_fun]
/-
**AbsolutelyContinuousOnInterval.sub** 是 Mathlib 中的一个定理，位于命名空间 `AbsolutelyContin
uousOnInterval`。
形式化陈述：sub (hf : AbsolutelyContinuousOnInterval f a b) (hg : AbsolutelyContinuous
OnInterval g a b) : AbsolutelyContinuousOnInterval (f - g) a b
参数：hf : AbsolutelyContinuousOnInterval f a b；hg : AbsolutelyContinuousOnInterval
 g a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `AbsolutelyContinuousOnInterval.add`：add (hf : AbsolutelyContinuousOnInte
rval f a b) (hg : AbsolutelyContinuousOnInterval g a b) : AbsolutelyContinuousOn
Interval (f + g) a b
· 使用定理 `AbsolutelyContinuousOnInterval.neg`：neg (hf : AbsolutelyContinuousOnInte
rval f a b) : AbsolutelyContinuousOnInterval (-f) a b
-/
theorem sub (hf : AbsolutelyContinuousOnInterval f a b)
    (hg : AbsolutelyContinuousOnInterval g a b) :
    AbsolutelyContinuousOnInterval (f - g) a b := by
  simpa [sub_eq_add_neg] using hf.add (hg.neg)
/-
**AbsolutelyContinuousOnInterval.const_smul** 是 Mathlib 中的一个定理，位于命名空间 `Absolutel
yContinuousOnInterval`。
形式化陈述：const_smul {M : Type*} [SeminormedRing M] [Module M F] [NormSMulClass M F]
 (α : M) (hf : AbsolutelyContinuousOnInterval f a b) : AbsolutelyContinuousOnInt
erval (fun x => α • f x) a b
参数：α : M；hf : AbsolutelyContinuousOnInterval f a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `squeeze_zero`：squeeze_zero {α} {f g : α -> Real} {t₀ : Filter α} (hf : f
orall t, 0 <= f t) (hft : forall t, f t <= g t) (g0 : Tendsto g t₀ (𝓝 0)) : Tend
st…
· 使用定理 `Finset.sum_nonneg`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈ s
, 0 ≤ f…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `dist_nonneg`：dist_nonneg {x y : α} : 0 <= dist x y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `dist_smul₀`：dist_smul₀ (s : α) (x y : β) : dist (s • x) (s • y) = ‖s‖ * 
dist x y
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Filter.Tendsto.const_mul`：Filter.Tendsto.const_mul {α : Type*} {f : α ->
 M} {x : Filter α} {a : M} (b : M) (hf : Tendsto f x (𝓝 a)) : Tendsto (b * f ·) 
x (𝓝 (b * a))
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
-/
theorem const_smul {M : Type*} [SeminormedRing M] [Module M F] [NormSMulClass M F]
    (α : M) (hf : AbsolutelyContinuousOnInterval f a b) :
    AbsolutelyContinuousOnInterval (fun x ↦ α • f x) a b := by
  apply squeeze_zero (fun t ↦ ?_) (fun t ↦ ?_) (by simpa using hf.const_mul ‖α‖)
  · exact Finset.sum_nonneg (fun i hi ↦ by positivity)
  · simp [Finset.mul_sum, dist_smul₀]
/-
**AbsolutelyContinuousOnInterval.const_mul** 是 Mathlib 中的一个定理，位于命名空间 `Absolutely
ContinuousOnInterval`。
形式化陈述：const_mul {f : Real -> Real} (α : Real) (hf : AbsolutelyContinuousOnInterv
al f a b) : AbsolutelyContinuousOnInterval (fun x => α * f x) a b
参数：α : Real；hf : AbsolutelyContinuousOnInterval f a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AbsolutelyContinuousOnInterval.const_smul`：const_smul {M : Type*} [Semin
ormedRing M] [Module M F] [NormSMulClass M F] (α : M) (hf : AbsolutelyContinuous
OnInterval f a b) : AbsolutelyC…
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
-/
theorem const_mul {f : ℝ → ℝ} (α : ℝ) (hf : AbsolutelyContinuousOnInterval f a b) :
    AbsolutelyContinuousOnInterval (fun x ↦ α * f x) a b :=
  hf.const_smul α
/-
**AbsolutelyContinuousOnInterval.uniformity_eq_comap_totalLengthFilter** 是 Mathl
ib 中的一个引理，位于命名空间 `AbsolutelyContinuousOnInterval`。
形式化陈述：uniformity_eq_comap_totalLengthFilter : uniformity X = comap (fun x => (1,
 fun _ => x)) totalLengthFilter
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.eq_of_same_basis`：∀ {α : Type u_1} {ι : Sort u_4} {l l' 
: Filter α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → l'.HasBasis p s →
 l = l'
· 使用定理 `Metric.uniformity_basis_dist`：uniformity_basis_dist : (𝓤 α).HasBasis (fu
n ε : Real => 0 < ε) fun ε => { p : α × α | dist p.1 p.2 < ε }
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `Finset.card_singleton`：card_singleton (a : α) : #{a} = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Filter.HasBasis.comap`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {l
 : Filter α} {p : ι → Prop} {s : ι → Set α} (f : β → α),   l.HasBasis p s → (Fil
ter.comap f…
· 使用引理 `AbsolutelyContinuousOnInterval.hasBasis_totalLengthFilter`：hasBasis_tota
lLengthFilter : totalLengthFilter.HasBasis (fun (ε : Real) => 0 < ε) (fun (ε : R
eal) => {E : Nat × (Nat -> X × X) | ∑ i in Fins…
-/
lemma uniformity_eq_comap_totalLengthFilter :
    uniformity X = comap (fun x ↦ (1, fun _ ↦ x)) totalLengthFilter := by
  refine Filter.HasBasis.eq_of_same_basis Metric.uniformity_basis_dist ?_
  convert! hasBasis_totalLengthFilter.comap _
  simp

/-- If `f` is absolutely continuous on `uIcc a b`, then `f` is uniformly continuous on `uIcc a b`.
-/
/-
**AbsolutelyContinuousOnInterval.uniformContinuousOn** 是 Mathlib 中的一个定理，位于命名空间 `
AbsolutelyContinuousOnInterval`。
形式化陈述：uniformContinuousOn (hf : AbsolutelyContinuousOnInterval f a b) : UniformC
ontinuousOn f (uIcc a b)
参数：hf : AbsolutelyContinuousOnInterval f a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `AbsolutelyContinuousOnInterval.uniformity_eq_comap_totalLengthFilter`：un
iformity_eq_comap_totalLengthFilter : uniformity X = comap (fun x => (1, fun _ =
> x)) totalLengthFilter
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.comap_inf`：∀ {α : Type u_1} {β : Type u_2} {g₁ g₂ : Filter β} {m 
: α → β},   Filter.comap m (g₁ ⊓ g₂) = Filter.comap m g₁ ⊓ Filter.comap m g₂
· 使用定理 `Filter.comap_principal`：comap_principal {t : Set β} : comap m (𝓟 t) = 𝓟 
(m ⁻¹' t)
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Finset.coe_singleton`：coe_singleton (a : α) : (({a} : Finset α) : Set α)
 = {a}
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Filter.comap_comap`：comap_comap {m : γ -> β} {n : β -> α} : comap m (com
ap n f) = comap (n ∘ m) f
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `Finset.card_singleton`：card_singleton (a : α) : #{a} = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Filter.comap_mono`：comap_mono : Monotone (comap m)

--- 原说明 ---
If `f` is absolutely continuous on `uIcc a b`, then `f` is uniformly continuous 
on `uIcc a b`.
-/
theorem uniformContinuousOn (hf : AbsolutelyContinuousOnInterval f a b) :
    UniformContinuousOn f (uIcc a b) := by
  simp only [UniformContinuousOn, Filter.tendsto_iff_comap, uniformity_eq_comap_totalLengthFilter]
  simp only [AbsolutelyContinuousOnInterval, Filter.tendsto_iff_comap] at hf
  convert! Filter.comap_mono hf
  · simp only [comap_inf, comap_principal]
    congr
    ext p
    simp only [disjWithin, Finset.mem_range, preimage_ofPred_eq, Nat.lt_one_iff,
      forall_eq, mem_ofPred_eq, mem_prod]
    simp
  · simp [totalLengthFilter, comap_comap, Function.comp_def]

@[deprecated (since := "2026-02-03")] alias uniformlyContinuousOn :=
  uniformContinuousOn

/-- If `f` is absolutely continuous on `uIcc a b`, then `f` is continuous on `uIcc a b`. -/
/-
**AbsolutelyContinuousOnInterval.continuousOn** 是 Mathlib 中的一个定理，位于命名空间 `Absolut
elyContinuousOnInterval`。
形式化陈述：continuousOn (hf : AbsolutelyContinuousOnInterval f a b) : ContinuousOn f 
(uIcc a b)
参数：hf : AbsolutelyContinuousOnInterval f a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuousOn.continuousOn`：UniformContinuousOn.continuousOn [Unif
ormSpace α] [UniformSpace β] {f : α -> β} {s : Set α} (h : UniformContinuousOn f
 s) : ContinuousOn f s
· 使用定理 `AbsolutelyContinuousOnInterval.uniformContinuousOn`：uniformContinuousOn 
(hf : AbsolutelyContinuousOnInterval f a b) : UniformContinuousOn f (uIcc a b)

--- 原说明 ---
If `f` is absolutely continuous on `uIcc a b`, then `f` is continuous on `uIcc a
 b`.
-/
theorem continuousOn (hf : AbsolutelyContinuousOnInterval f a b) :
    ContinuousOn f (uIcc a b) :=
  hf.uniformContinuousOn.continuousOn

/-- If `f` is absolutely continuous on `uIcc a b`, then `f` is bounded on `uIcc a b`. -/
/-
**AbsolutelyContinuousOnInterval.exists_bound** 是 Mathlib 中的一个定理，位于命名空间 `Absolut
elyContinuousOnInterval`。
形式化陈述：exists_bound (hf : AbsolutelyContinuousOnInterval f a b) : exists (C : Rea
l), forall x in uIcc a b, ‖f x‖ <= C
参数：hf : AbsolutelyContinuousOnInterval f a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.exists_bound_of_continuousOn`：∀ {α : Type u_1} {E : Type u_2} 
[inst : SeminormedAddGroup E] [inst_1 : TopologicalSpace α] {s : Set α},   IsCom
pact s → ∀ {f : α → E}, Cont…
· 使用定理 `CompactIccSpace.isCompact_Icc`：∀ {α : Type u_1} {inst : TopologicalSpace
 α} {inst_1 : Preorder α} [self : CompactIccSpace α] {a b : α},   IsCompact (Set
.Icc a b)
· 使用定理 `ConditionallyCompleteLinearOrder.toCompactIccSpace`：∀ (α : Type u_2) [in
st : ConditionallyCompleteLinearOrder α] [inst_1 : TopologicalSpace α] [OrderTop
ology α],   CompactIccSpace α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `AbsolutelyContinuousOnInterval.continuousOn`：continuousOn (hf : Absolute
lyContinuousOnInterval f a b) : ContinuousOn f (uIcc a b)

--- 原说明 ---
If `f` is absolutely continuous on `uIcc a b`, then `f` is bounded on `uIcc a b`
.
-/
theorem exists_bound (hf : AbsolutelyContinuousOnInterval f a b) :
    ∃ (C : ℝ), ∀ x ∈ uIcc a b, ‖f x‖ ≤ C :=
  isCompact_Icc.exists_bound_of_continuousOn (hf.continuousOn)

/-- If `f` and `g` are absolutely continuous on `uIcc a b`, then `f • g` is absolutely continuous
on `uIcc a b`. -/
@[to_fun]
/-
**AbsolutelyContinuousOnInterval.smul** 是 Mathlib 中的一个定理，位于命名空间 `AbsolutelyConti
nuousOnInterval`。
形式化陈述：smul {M : Type*} [SeminormedRing M] [Module M F] [NormSMulClass M F] {f : 
Real -> M} {g : Real -> F} (hf : AbsolutelyContinuousOnInterval f a b) (hg : Abs
olutelyContinuousOnInterval g a b) : AbsolutelyContinuousOnInterval (f • g) a b
参数：hf : AbsolutelyContinuousOnInterval f a b；hg : AbsolutelyContinuousOnInterval
 g a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AbsolutelyContinuousOnInterval.exists_bound`：exists_bound (hf : Absolute
lyContinuousOnInterval f a b) : exists (C : Real), forall x in uIcc a b, ‖f x‖ <
= C
· 使用引理 `squeeze_zero'`：squeeze_zero' {α} {f g : α -> Real} {t₀ : Filter α} (hf :
 forallᶠ t in t₀, 0 <= f t) (hft : forallᶠ t in t₀, f t <= g t) (g0 : Tendsto g 
t₀ …
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `Finset.sum_nonneg`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈ s
, 0 ≤ f…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `dist_nonneg`：dist_nonneg {x y : α} : 0 <= dist x y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.eventually_inf_principal`：eventually_inf_principal {f : Filter α}
 {p : α -> Prop} {s : Set α} : (forallᶠ x in f ⊓ 𝓟 s, p x) ↔ forallᶠ x in f, x i
n s -> p x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用定理 `Finset.sum_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f g : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈
 s, f i…
· 使用定理 `dist_triangle`：dist_triangle (x y z : α) : dist x z <= dist x y + dist y
 z
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `dist_smul₀`：dist_smul₀ (s : α) (x y : β) : dist (s • x) (s • y) = ‖s‖ * 
dist x y
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `dist_pair_smul`：dist_pair_smul (x₁ x₂ : α) (y : β) : dist (x₁ • y) (x₂ •
 y) <= dist x₁ x₂ * dist y 0
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `dist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E),
 dist a 0 = ‖a‖
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
（共 38 条，此处仅展示前 30 条）

--- 原说明 ---
If `f` and `g` are absolutely continuous on `uIcc a b`, then `f • g` is absolute
ly continuous
on `uIcc a b`.
-/
theorem smul {M : Type*} [SeminormedRing M] [Module M F] [NormSMulClass M F]
    {f : ℝ → M} {g : ℝ → F}
    (hf : AbsolutelyContinuousOnInterval f a b) (hg : AbsolutelyContinuousOnInterval g a b) :
    AbsolutelyContinuousOnInterval (f • g) a b := by
  obtain ⟨C, hC⟩ := hf.exists_bound
  obtain ⟨D, hD⟩ := hg.exists_bound
  unfold AbsolutelyContinuousOnInterval at hf hg
  apply squeeze_zero' ?_ ?_
    (by simpa using (hg.const_mul C).add (hf.const_mul D))
  · exact Filter.Eventually.of_forall <| fun _ ↦ Finset.sum_nonneg (fun i hi ↦ dist_nonneg)
  rw [eventually_inf_principal]
  filter_upwards with (n, I) hnI
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  gcongr with i hi
  trans dist (f (I i).1 • g (I i).1) (f (I i).1 • g (I i).2) +
    dist (f (I i).1 • g (I i).2) (f (I i).2 • g (I i).2)
  · exact dist_triangle _ _ _
  · simp only [disjWithin, mem_ofPred_eq] at hnI
    gcongr
    · rw [dist_smul₀]
      gcongr
      exact hC _ (hnI.left i hi |>.left)
    · rw [mul_comm]
      grw [dist_pair_smul]
      gcongr
      rw [dist_zero_right]
      exact hD _ (hnI.left i hi |>.right)

/-- If `f` and `g` are absolutely continuous on `uIcc a b`, then `f * g` is absolutely continuous
on `uIcc a b`. -/
@[to_fun]
/-
**AbsolutelyContinuousOnInterval.mul** 是 Mathlib 中的一个定理，位于命名空间 `AbsolutelyContin
uousOnInterval`。
形式化陈述：mul {f g : Real -> Real} (hf : AbsolutelyContinuousOnInterval f a b) (hg :
 AbsolutelyContinuousOnInterval g a b) : AbsolutelyContinuousOnInterval (f * g) 
a b
参数：hf : AbsolutelyContinuousOnInterval f a b；hg : AbsolutelyContinuousOnInterval
 g a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AbsolutelyContinuousOnInterval.smul`：smul {M : Type*} [SeminormedRing M]
 [Module M F] [NormSMulClass M F] {f : Real -> M} {g : Real -> F} (hf : Absolute
lyContinuousOnInterval f …
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E

--- 原说明 ---
If `f` and `g` are absolutely continuous on `uIcc a b`, then `f * g` is absolute
ly continuous
on `uIcc a b`.
-/
theorem mul {f g : ℝ → ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) (hg : AbsolutelyContinuousOnInterval g a b) :
    AbsolutelyContinuousOnInterval (f * g) a b :=
  hf.smul hg

/-- If `f` is Lipschitz on `uIcc a b`, then `f` is absolutely continuous on `uIcc a b`. -/
/-
**AbsolutelyContinuousOnInterval._root_.LipschitzOnWith.absolutelyContinuousOnIn
terval** 是 Mathlib 中的一个定理，位于命名空间 `AbsolutelyContinuousOnInterval`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f` is Lipschitz on `uIcc a b`, then `f` is absolutely continuous on `uIcc a 
b`.
-/
theorem _root_.LipschitzOnWith.absolutelyContinuousOnInterval {f : ℝ → X} {K : ℝ≥0}
    (hfK : LipschitzOnWith K f (uIcc a b)) : AbsolutelyContinuousOnInterval f a b := by
  rw [absolutelyContinuousOnInterval_iff]
  intro ε hε
  refine ⟨ε / (K + 1), by positivity, fun (n, I) hnI₁ hnI₂ ↦ ?_⟩
  calc
    _ ≤ ∑ i ∈ Finset.range n, K * dist (I i).1 (I i).2 := by
      apply Finset.sum_le_sum
      intro i hi
      have := hfK (hnI₁.left i hi).left (hnI₁.left i hi).right
      apply ENNReal.toReal_mono (Ne.symm (not_eq_of_beq_eq_false rfl)) at this
      rwa [ENNReal.toReal_mul, ← dist_edist, ← dist_edist] at this
    _ = K * ∑ i ∈ Finset.range n, dist (I i).1 (I i).2 := by symm; exact Finset.mul_sum _ _ _
    _ ≤ K * (ε / (K + 1)) := by gcongr
    _ < (K + 1) * (ε / (K + 1)) := by gcongr; linarith
    _ = ε := by field

/-- If `f` is `C^1` on `uIcc a b`, then `f` is absolutely continuous on `uIcc a b`. -/
/-
**AbsolutelyContinuousOnInterval._root_.ContDiffOn.absolutelyContinuousOnInterva
l** 是 Mathlib 中的一个定理，位于命名空间 `AbsolutelyContinuousOnInterval`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f` is `C^1` on `uIcc a b`, then `f` is absolutely continuous on `uIcc a b`.
-/
theorem _root_.ContDiffOn.absolutelyContinuousOnInterval {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : ℝ → E} (hf : ContDiffOn ℝ 1 f (uIcc a b)) :
    AbsolutelyContinuousOnInterval f a b := by
  obtain ⟨K, hK⟩ := hf.exists_lipschitzOnWith (by decide) (convex_Icc _ _) isCompact_Icc
  exact hK.absolutelyContinuousOnInterval

/-- If `f` is absolutely continuous on `uIcc a b`, then `f` has bounded variation on `uIcc a b`. -/
/-
**AbsolutelyContinuousOnInterval.boundedVariationOn** 是 Mathlib 中的一个定理，位于命名空间 `A
bsolutelyContinuousOnInterval`。
形式化陈述：boundedVariationOn (hf : AbsolutelyContinuousOnInterval f a b) : BoundedVa
riationOn f (uIcc a b)
参数：hf : AbsolutelyContinuousOnInterval f a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.uIcc_of_le`：uIcc_of_le (h : a <= b) : [[a, b]] = Icc a b
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.Icc_self`：Icc_self (a : α) : Icc a a = {a}
· 使用定理 `eVariationOn.subsingleton`：∀ {α : Type u_1} [inst : LinearOrder α] {E : 
Type u_2} [inst_1 : PseudoEMetricSpace E] (f : α → E) {s : Set α},   s.Subsingle
ton → eVariatio…
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `absolutelyContinuousOnInterval_iff`：∀ {X : Type u_1} [inst : PseudoMetri
cSpace X] (f : ℝ → X) (a b : ℝ),   AbsolutelyContinuousOnInterval f a b ↔     ∀ 
ε > 0,       ∃ δ > 0,   …
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
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
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
（共 151 条，此处仅展示前 30 条）

--- 原说明 ---
If `f` is absolutely continuous on `uIcc a b`, then `f` has bounded variation on
 `uIcc a b`.
-/
theorem boundedVariationOn (hf : AbsolutelyContinuousOnInterval f a b) :
    BoundedVariationOn f (uIcc a b) := by
  -- We may assume wlog that `a ≤ b`.
  wlog hab₀ : a ≤ b generalizing a b
  · specialize @this b a hf.symm (by linarith)
    rwa [uIcc_comm]
  rw [uIcc_of_le hab₀]
  -- Split the cases `a = b` (which is trivial) and `a < b`.
  rcases hab₀.eq_or_lt with rfl | hab
  · simp [BoundedVariationOn]
  -- Now remains the case `a < b`.
  -- Use the `ε`-`δ` definition of AC to get a `δ > 0` such that whenever a finite set of disjoint
  --   intervals `uIoc (a i) (b i)`, `i < n` have total length `< δ` and `a i, b i` are all in
  --  `[a, b]`, we have `∑ i ∈ range n, dist (f (a i)) (f (b i)) < 1`.
  rw [absolutelyContinuousOnInterval_iff] at hf
  obtain ⟨δ, hδ₁, hδ₂⟩ := hf 1 (by linarith)
  have hab₁ : 0 < b - a := by linarith
  -- Split `[a, b]` into subintervals `[a + i * δ', a + (i + 1) * δ']` for `i = 0, ..., n`, where
  --   `a + (n + 1) * δ' = b` and `δ' < δ`.
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (div_pos hδ₁ hab₁)
  set δ' := (b - a) / (n + 1)
  have hδ₃ : δ' < δ := by
    dsimp only [δ']
    convert! mul_lt_mul_of_pos_right hn hab₁ using 1 <;> field
  have h_mono : Monotone fun (i : ℕ) ↦ a + ↑i * δ' := by
    apply Monotone.const_add
    apply Monotone.mul_const Nat.mono_cast
    simp only [δ']
    refine div_nonneg ?_ ?_ <;> linarith
  -- The variation of `f` on `[a, b]` is the sum of the variations on these subintervals.
  have v_sum : eVariationOn f (Icc a b) =
      ∑ i ∈ Finset.range (n + 1), eVariationOn f (Icc (a + i * δ') (a + (i + 1) * δ')) := by
    convert! eVariationOn.sum' f (I := fun i ↦ a + i * δ') h_mono |>.symm
    · simp
    · simp only [Nat.cast_add, Nat.cast_one, δ']; field
    · norm_cast
  -- The variation of `f` on any subinterval `[x, y]` of `[a, b]` of length `< δ` is `≤ 1`.
  have v_each (x y : ℝ) (_ : a ≤ x) (_ : x ≤ y) (_ : y < x + δ) (_ : y ≤ b) :
      eVariationOn f (Icc x y) ≤ 1 := by
    simp only [eVariationOn, iSup_le_iff]
    intro p
    obtain ⟨hp₁, hp₂⟩ := p.2.property
    -- Focus on a partition `p` of `[x, y]` and show its variation with `f` is `≤ 1`.
    have vf : ∑ i ∈ Finset.range p.1, dist (f (p.2.val i)) (f (p.2.val (i + 1))) < 1 := by
      apply hδ₂ (p.1, (fun i ↦ (p.2.val i, p.2.val (i + 1))))
      · constructor
        · have : Icc x y ⊆ uIcc a b := by rw [uIcc_of_le hab₀]; gcongr
          intro i hi
          constructor <;> exact this (hp₂ _)
        · rw [PairwiseDisjoint]
          convert! hp₁.pairwise_disjoint_on_Ioc_succ.set_pairwise (Finset.range p.1) using 3
          rw [uIoc_of_le (hp₁ (by lia)), Nat.succ_eq_succ]
      · suffices p.2.val p.1 - p.2.val 0 < δ by
          convert! this
          rw [← Finset.sum_range_sub]
          congr; ext i
          rw [dist_comm, Real.dist_eq, abs_eq_self.mpr]
          linarith [@hp₁ i (i + 1) (by lia)]
        linarith [mem_Icc.mp (hp₂ p.1), mem_Icc.mp (hp₂ 0)]
    -- Reduce edist in the goal to dist and clear up
    have veq : (∑ i ∈ Finset.range p.1, edist (f (p.2.val (i + 1))) (f (p.2.val i))).toReal =
        ∑ i ∈ Finset.range p.1, dist (f (p.2.val i)) (f (p.2.val (i + 1))) := by
      rw [ENNReal.toReal_sum (by simp [edist_ne_top])]
      simp_rw [← dist_edist]; congr; ext i; nth_rw 1 [dist_comm]
    have not_top : ∑ i ∈ Finset.range p.1, edist (f (p.2.val (i + 1))) (f (p.2.val i)) ≠ ⊤ := by
      simp [edist_ne_top]
    rw [← ENNReal.ofReal_toReal not_top]
    convert! ENNReal.ofReal_le_ofReal (veq.symm ▸ vf.le)
    simp
  -- Reduce to goal that the variation of `f` on each of these subintervals is finite.
  simp only [BoundedVariationOn, v_sum, ne_eq, ENNReal.sum_eq_top, Finset.mem_range, not_exists,
    not_and]
  intro i hi
  -- Reduce finiteness to `≤ 1`.
  suffices eVariationOn f (Icc (a + i * δ') (a + (i + 1) * δ')) ≤ 1 from
    fun hC ↦ by simp [hC] at this
  -- Verify that `[a + i * δ', a + (i + 1) * δ']` is indeed a subinterval of `[a, b]`
  apply v_each
  · convert! h_mono (show 0 ≤ i by lia); simp
  · convert! h_mono (show i ≤ i + 1 by lia); norm_cast
  · rw [add_mul, ← add_assoc]; simpa
  · convert! h_mono (show i + 1 ≤ n + 1 by lia)
    · norm_cast
    · simp only [Nat.cast_add, Nat.cast_one, δ']; field

/-- If `f` is absolute continuous on `uIcc a b`, then `f'` exists a.e. on `uIcc a b`. -/
/-
**AbsolutelyContinuousOnInterval.ae_differentiableAt** 是 Mathlib 中的一个定理，位于命名空间 `
AbsolutelyContinuousOnInterval`。
形式化陈述：ae_differentiableAt {f : Real -> Real} {a b : Real} (hf : AbsolutelyContin
uousOnInterval f a b) : forallᵐ (x : Real), x in uIcc a b -> DifferentiableAt Re
al f x
参数：hf : AbsolutelyContinuousOnInterval f a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BoundedVariationOn.ae_differentiableAt_of_mem_uIcc`：∀ {V : Type u_1} [in
st : NormedAddCommGroup V] [inst_1 : NormedSpace ℝ V] [FiniteDimensional ℝ V] {f
 : ℝ → V} {a b : ℝ},   BoundedVariationO…
· 使用定理 `AbsolutelyContinuousOnInterval.boundedVariationOn`：boundedVariationOn (h
f : AbsolutelyContinuousOnInterval f a b) : BoundedVariationOn f (uIcc a b)

--- 原说明 ---
If `f` is absolute continuous on `uIcc a b`, then `f'` exists a.e. on `uIcc a b`
.
-/
theorem ae_differentiableAt {f : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) :
    ∀ᵐ (x : ℝ), x ∈ uIcc a b → DifferentiableAt ℝ f x :=
  hf.boundedVariationOn.ae_differentiableAt_of_mem_uIcc

/-- If `f` is interval integrable on `a..b` and `c ∈ uIcc a b`, then `fun x ↦ ∫ v in c..x, f v` is
absolutely continuous on `uIcc a b`. -/
/-
**AbsolutelyContinuousOnInterval._root_.IntervalIntegrable.absolutelyContinuousO
nInterval_intervalIntegral** 是 Mathlib 中的一个定理，位于命名空间 `AbsolutelyContinuousOnInte
rval`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f` is interval integrable on `a..b` and `c ∈ uIcc a b`, then `fun x ↦ ∫ v in
 c..x, f v` is
absolutely continuous on `uIcc a b`.
-/
theorem _root_.IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral {f : ℝ → ℝ}
    {a b c : ℝ} (h : IntervalIntegrable f volume a b) (hc : c ∈ uIcc a b) :
    AbsolutelyContinuousOnInterval (fun x ↦ ∫ v in c..x, f v) a b := by
  -- Step 1: Use `MeasureTheory.tendsto_setLIntegral_zero` to conclude that the function sending
  -- `E` to `∫⁻ (x : ℝ) in s E, ‖f x‖ₑ ∂volume.restrict (uIoc a b))` tends to `0` along
  -- `totalLengthFilter ⊓ 𝓟 (disjWithin a b)`.
  let s := fun E : ℕ × (ℕ → ℝ × ℝ) ↦ ⋃ i ∈ Finset.range E.1, uIoc (E.2 i).1 (E.2 i).2
  have : Tendsto (fun i ↦ ∫⁻ (x : ℝ) in s i, ‖f x‖ₑ ∂volume.restrict (uIoc a b))
      (totalLengthFilter ⊓ 𝓟 (disjWithin a b)) (𝓝 0) :=
    tendsto_setLIntegral_zero
    (ne_of_lt <| intervalIntegrable_iff.mp h |>.hasFiniteIntegral)
    (tendsto_volume_restrict_totalLengthFilter_disjWithin_nhds_zero _ _)
  -- Step 2: Use the lintegral in Step 1 to bound the sum of the distances between
  -- `∫ v in c..(E.2 i).2, f v` and `∫ v in c..(E.2 i).2, f v` that occurs in the definition
  -- of absolutely continuous.
  have := ENNReal.toReal_zero ▸ (ENNReal.continuousAt_toReal (by simp)).tendsto.comp this
  refine squeeze_zero' ?_ ?_ this
  · filter_upwards with (n, I)
    exact Finset.sum_nonneg (fun _ _ ↦ dist_nonneg)
  simp only [comp_apply, s]
  have : ∀ᶠ (E : ℕ × (ℕ → ℝ × ℝ)) in totalLengthFilter ⊓ 𝓟 (disjWithin a b),
      E ∈ disjWithin a b :=
    eventually_inf_principal.mpr (by simp)
  filter_upwards [this] with (n, I) hnI
  obtain ⟨hnI1, hnI2⟩ := mem_ofPred_eq ▸ hnI
  simp only
  rw [← integral_norm_eq_lintegral_enorm (h.aestronglyMeasurable_restrict_uIoc.restrict),
      integral_biUnion_finset _ (by simp +contextual [uIoc]) hnI2]
  · refine Finset.sum_le_sum (fun i hi ↦ ?_)
    rw [Real.dist_eq,
        intervalIntegral.integral_interval_sub_left
          (by apply IntervalIntegrable.mono_set' h; grind [uIoc, uIcc])
          (by apply IntervalIntegrable.mono_set' h; grind [uIoc, uIcc]),
        Measure.restrict_restrict_of_subset
          (uIoc_subset_of_mem_disjWithin hnI (Finset.mem_range.mp hi)),
        intervalIntegral.integral_symm, abs_neg,
        intervalIntegral.abs_intervalIntegral_eq]
    exact abs_integral_le_integral_abs
  · intro i hi
    unfold IntegrableOn
    have h_subset := uIoc_subset_of_mem_disjWithin hnI (Finset.mem_range.mp hi)
    rw [Measure.restrict_restrict_of_subset h_subset]
    exact IntegrableOn.mono_set h.def'.norm h_subset |>.integrable

end AbsolutelyContinuousOnInterval

