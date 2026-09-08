/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.Topology.Sets.Compacts

/-!
# Contents

In this file we work with *contents*. A content `λ` is a function from a certain class of subsets
(such as the compact subsets) to `ℝ≥0` that is
* additive: If `K₁` and `K₂` are disjoint sets in the domain of `λ`,
  then `λ(K₁ ∪ K₂) = λ(K₁) + λ(K₂)`;
* subadditive: If `K₁` and `K₂` are in the domain of `λ`, then `λ(K₁ ∪ K₂) ≤ λ(K₁) + λ(K₂)`;
* monotone: If `K₁ ⊆ K₂` are in the domain of `λ`, then `λ(K₁) ≤ λ(K₂)`.

We show that:
* Given a content `λ` on compact sets, let us define a function `λ*` on open sets, by letting
  `λ* U` be the supremum of `λ K` for `K` included in `U`. This is a countably subadditive map that
  vanishes at `∅`. In Halmos (1950) this is called the *inner content* `λ*` of `λ`, and formalized
  as `innerContent`.
* Given an inner content, we define an outer measure `μ*`, by letting `μ* E` be the infimum of
  `λ* U` over the open sets `U` containing `E`. This is indeed an outer measure. It is formalized
  as `outerMeasure`.
* Restricting this outer measure to Borel sets gives a regular measure `μ`.

We define bundled contents as `Content`.
In this file we only work on contents on compact sets, and inner contents on open sets, and both
contents and inner contents map into the extended nonnegative reals. However, in other applications
other choices can be made, and it is not a priori clear what the best interface should be.

## Main definitions

For `μ : Content G`, we define
* `μ.innerContent` : the inner content associated to `μ`.
* `μ.outerMeasure` : the outer measure associated to `μ`.
* `μ.measure`      : the Borel measure associated to `μ`.

These definitions are given for spaces which are R₁.
The resulting measure `μ.measure` is always outer regular by design.
When the space is locally compact, `μ.measure` is also regular.

## References

* Paul Halmos (1950), Measure Theory, §53
* <https://en.wikipedia.org/wiki/Content_(measure_theory)>
-/

@[expose] public section


universe u v w

noncomputable section

open Set TopologicalSpace

open NNReal ENNReal MeasureTheory

namespace MeasureTheory

variable {G : Type w} [TopologicalSpace G]

/-- A content is an additive function on compact sets taking values in `ℝ≥0`. It is a device
from which one can define a measure. -/
/-
**MeasureTheory.Content** 是 Mathlib 中的一个归纳类型，位于命名空间 `MeasureTheory`。
形式化陈述：(G : Type w) → [TopologicalSpace G] → Type w
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A content is an additive function on compact sets taking values in `ℝ≥0`. It is 
a device
from which one can define a measure.
-/
structure Content (G : Type w) [TopologicalSpace G] where
  /-- The underlying additive function -/
  toFun : Compacts G → ℝ≥0
  mono' : ∀ K₁ K₂ : Compacts G, (K₁ : Set G) ⊆ K₂ → toFun K₁ ≤ toFun K₂
  sup_disjoint' :
    ∀ K₁ K₂ : Compacts G, Disjoint (K₁ : Set G) K₂ → IsClosed (K₁ : Set G) → IsClosed (K₂ : Set G)
      → toFun (K₁ ⊔ K₂) = toFun K₁ + toFun K₂
  sup_le' : ∀ K₁ K₂ : Compacts G, toFun (K₁ ⊔ K₂) ≤ toFun K₁ + toFun K₂
/-
**MeasureTheory.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (Content G) :=
  ⟨{  toFun := fun _ => 0
      mono' := by simp
      sup_disjoint' := by simp
      sup_le' := by simp }⟩

namespace Content

/-
**MeasureTheory.Content.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Content`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : FunLike (Content G) (Compacts G) ℝ≥0∞ where
  coe μ s := μ.toFun s
  coe_injective := by
    rintro ⟨μ, _, _⟩ ⟨v, _, _⟩ h; congr!; ext s : 1; exact ENNReal.coe_injective <| congr_fun h s

variable (μ : Content G)
/-
**MeasureTheory.Content.toFun_eq_toNNReal_apply** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.Content`。
形式化陈述：∀ {G : Type w} [inst : TopologicalSpace G] (μ : MeasureTheory.Content G) (
K : TopologicalSpace.Compacts G),   μ.toFun K = (μ K).toNNReal
参数：μ : MeasureTheory.Content G；K : TopologicalSpace.Compacts G；μ K。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toFun_eq_toNNReal_apply (K : Compacts G) : μ.toFun K = (μ K).toNNReal := rfl

@[simp]
/-
**MeasureTheory.Content.mk_apply** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.Conten
t`。
形式化陈述：mk_apply (toFun : Compacts G -> Real>=0) (mono' sup_disjoint' sup_le') (K 
: Compacts G) : mk toFun mono' sup_disjoint' sup_le' K = toFun K
参数：toFun : Compacts G -> Real>=0；mono' sup_disjoint' sup_le'；K : Compacts G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mk_apply (toFun : Compacts G → ℝ≥0) (mono' sup_disjoint' sup_le') (K : Compacts G) :
    mk toFun mono' sup_disjoint' sup_le' K = toFun K := rfl
/-
**MeasureTheory.Content.apply_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Co
ntent`。
形式化陈述：∀ {G : Type w} [inst : TopologicalSpace G] (μ : MeasureTheory.Content G) {
K : TopologicalSpace.Compacts G}, μ K ≠ ⊤
参数：μ : MeasureTheory.Content G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.coe_ne_top`：coe_ne_top : (r : Real>=0∞) != ∞
-/
@[simp] lemma apply_ne_top {K : Compacts G} : μ K ≠ ∞ := coe_ne_top
/-
**MeasureTheory.Content.mono** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Content`。
形式化陈述：mono (K₁ K₂ : Compacts G) (h : (K₁ : Set G) subseteq K₂) : μ K₁ <= μ K₂
参数：K₁ K₂ : Compacts G；h : (K₁ : Set G) subseteq K₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `MeasureTheory.Content.mono'`：∀ {G : Type w} [inst : TopologicalSpace G] 
(self : MeasureTheory.Content G) (K₁ K₂ : TopologicalSpace.Compacts G),   ↑K₁ ⊆ 
↑K₂ → self.toFun …
-/
theorem mono (K₁ K₂ : Compacts G) (h : (K₁ : Set G) ⊆ K₂) : μ K₁ ≤ μ K₂ := by
  simpa using μ.mono' _ _ h
/-
**MeasureTheory.Content.sup_disjoint** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Co
ntent`。
形式化陈述：sup_disjoint (K₁ K₂ : Compacts G) (h : Disjoint (K₁ : Set G) K₂) (h₁ : IsC
losed (K₁ : Set G)) (h₂ : IsClosed (K₂ : Set G)) : μ (K₁ ⊔ K₂) = μ K₁ + μ K₂
参数：K₁ K₂ : Compacts G；h : Disjoint (K₁ : Set G) K₂；h₁ : IsClosed (K₁ : Set G)；h₂
 : IsClosed (K₂ : Set G)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `MeasureTheory.Content.sup_disjoint'`：∀ {G : Type w} [inst : TopologicalS
pace G] (self : MeasureTheory.Content G) (K₁ K₂ : TopologicalSpace.Compacts G), 
  Disjoint ↑K₁ ↑K₂ → IsCl…
-/
theorem sup_disjoint (K₁ K₂ : Compacts G) (h : Disjoint (K₁ : Set G) K₂)
    (h₁ : IsClosed (K₁ : Set G)) (h₂ : IsClosed (K₂ : Set G)) :
    μ (K₁ ⊔ K₂) = μ K₁ + μ K₂ := by
  simpa [toNNReal_eq_toNNReal_iff, ← toNNReal_add] using μ.sup_disjoint' _ _ h h₁ h₂
/-
**MeasureTheory.Content.sup_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Content`
。
形式化陈述：sup_le (K₁ K₂ : Compacts G) : μ (K₁ ⊔ K₂) <= μ K₁ + μ K₂
参数：K₁ K₂ : Compacts G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `MeasureTheory.Content.sup_le'`：∀ {G : Type w} [inst : TopologicalSpace G
] (self : MeasureTheory.Content G) (K₁ K₂ : TopologicalSpace.Compacts G),   self
.toFun (K₁ ⊔ K₂) ≤ …
-/
theorem sup_le (K₁ K₂ : Compacts G) : μ (K₁ ⊔ K₂) ≤ μ K₁ + μ K₂ := by
  simpa [← toNNReal_add] using μ.sup_le' _ _
/-
**MeasureTheory.Content.lt_top** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Content`
。
形式化陈述：lt_top (K : Compacts G) : μ K < ∞
参数：K : Compacts G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.coe_lt_top`：∀ {r : NNReal}, ↑r < ⊤
-/
theorem lt_top (K : Compacts G) : μ K < ∞ :=
  ENNReal.coe_lt_top
/-
**MeasureTheory.Content.empty** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Content`。
形式化陈述：empty : μ ⊥ = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `NNReal.instIsStrictOrderedRing_1`：IsStrictOrderedRing NNReal
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `MeasureTheory.Content.sup_disjoint'`：∀ {G : Type w} [inst : TopologicalS
pace G] (self : MeasureTheory.Content G) (K₁ K₂ : TopologicalSpace.Compacts G), 
  Disjoint ↑K₁ ↑K₂ → IsCl…
-/
theorem empty : μ ⊥ = 0 := by simpa [toNNReal_eq_zero_iff] using μ.sup_disjoint' ⊥ ⊥

/-- Constructing the inner content of a content. From a content defined on the compact sets, we
  obtain a function defined on all open sets, by taking the supremum of the content of all compact
  subsets. -/
/-
**MeasureTheory.Content.innerContent** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.Co
ntent`。
形式化陈述：innerContent (U : Opens G) : Real>=0∞
参数：U : Opens G。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructing the inner content of a content. From a content defined on the compa
ct sets, we
  obtain a function defined on all open sets, by taking the supremum of the cont
ent of all compact
  subsets.
-/
def innerContent (U : Opens G) : ℝ≥0∞ :=
  ⨆ (K : Compacts G) (_ : (K : Set G) ⊆ U), μ K
/-
**MeasureTheory.Content.le_innerContent** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.Content`。
形式化陈述：le_innerContent (K : Compacts G) (U : Opens G) (h2 : (K : Set G) subseteq 
U) : μ K <= μ.innerContent U
参数：K : Compacts G；U : Opens G；h2 : (K : Set G) subseteq U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_iSup_of_le`：le_iSup_of_le (i : ι) (h : a <= f i) : a <= iSup f
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
-/
theorem le_innerContent (K : Compacts G) (U : Opens G) (h2 : (K : Set G) ⊆ U) :
    μ K ≤ μ.innerContent U :=
  le_iSup_of_le K <| le_iSup (fun _ ↦ (μ.toFun K : ℝ≥0∞)) h2
/-
**MeasureTheory.Content.innerContent_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.Content`。
形式化陈述：innerContent_le (U : Opens G) (K : Compacts G) (h2 : (U : Set G) subseteq 
K) : μ.innerContent U <= μ K
参数：U : Opens G；K : Compacts G；h2 : (U : Set G) subseteq K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup₂_le`：iSup₂_le {f : forall i, κ i -> α} (h : forall i j, f i j <= a)
 : ⨆ (i) (j), f i j <= a
· 使用定理 `MeasureTheory.Content.mono`：mono (K₁ K₂ : Compacts G) (h : (K₁ : Set G) 
subseteq K₂) : μ K₁ <= μ K₂
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
-/
theorem innerContent_le (U : Opens G) (K : Compacts G) (h2 : (U : Set G) ⊆ K) :
    μ.innerContent U ≤ μ K :=
  iSup₂_le fun _ hK' => μ.mono _ _ (Subset.trans hK' h2)
/-
**MeasureTheory.Content.innerContent_of_isCompact** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory.Content`。
形式化陈述：innerContent_of_isCompact {K : Set G} (h1K : IsCompact K) (h2K : IsOpen K)
 : μ.innerContent ⟨K, h2K⟩ = μ ⟨K, h1K⟩
参数：h1K : IsCompact K；h2K : IsOpen K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `iSup₂_le`：iSup₂_le {f : forall i, κ i -> α} (h : forall i j, f i j <= a)
 : ⨆ (i) (j), f i j <= a
· 使用定理 `MeasureTheory.Content.mono`：mono (K₁ K₂ : Compacts G) (h : (K₁ : Set G) 
subseteq K₂) : μ K₁ <= μ K₂
· 使用定理 `MeasureTheory.Content.le_innerContent`：le_innerContent (K : Compacts G) 
(U : Opens G) (h2 : (K : Set G) subseteq U) : μ K <= μ.innerContent U
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
-/
theorem innerContent_of_isCompact {K : Set G} (h1K : IsCompact K) (h2K : IsOpen K) :
    μ.innerContent ⟨K, h2K⟩ = μ ⟨K, h1K⟩ :=
  le_antisymm (iSup₂_le fun _ hK' => μ.mono _ ⟨K, h1K⟩ hK') (μ.le_innerContent _ _ Subset.rfl)
/-
**MeasureTheory.Content.innerContent_bot** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.Content`。
形式化陈述：innerContent_bot : μ.innerContent ⊥ = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nonpos_iff_eq_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [in
st_1 : Zero α] [IsBotZeroClass α], a ≤ 0 ↔ a = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `MeasureTheory.Content.empty`：empty : μ ⊥ = 0
· 使用定理 `iSup₂_le`：iSup₂_le {f : forall i, κ i -> α} (h : forall i j, f i j <= a)
 : ⨆ (i) (j), f i j <= a
· 使用定理 `TopologicalSpace.Compacts.ext`：∀ {α : Type u_1} [inst : TopologicalSpace
 α] {s t : TopologicalSpace.Compacts α}, ↑s = ↑t → s = t
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.subset_empty_iff`：subset_empty_iff {s : Set α} : s subseteq ∅ ↔ s = 
∅
· 使用定理 `TopologicalSpace.Compacts.coe_bot`：coe_bot : (↑(⊥ : Compacts α) : Set α)
 = ∅
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem innerContent_bot : μ.innerContent ⊥ = 0 := by
  rw [← nonpos_iff_eq_zero, ← μ.empty]
  refine iSup₂_le fun K hK => ?_
  have : K = ⊥ := by
    ext1
    rw [subset_empty_iff.mp hK, Compacts.coe_bot]
  rw [this]

/-- This is "unbundled", because that is required for the API of `inducedOuterMeasure`. -/
/-
**MeasureTheory.Content.innerContent_mono** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.Content`。
形式化陈述：innerContent_mono ⦃U V : Set G⦄ (hU : IsOpen U) (hV : IsOpen V) (h2 : U su
bseteq V) : μ.innerContent ⟨U, hU⟩ <= μ.innerContent ⟨V, hV⟩
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `biSup_mono`：biSup_mono {p q : ι -> Prop} (hpq : forall i, p i -> q i) : 
⨆ (i) (_ : p i), f i <= ⨆ (i) (_ : q i), f i
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c

--- 原说明 ---
This is "unbundled", because that is required for the API of `inducedOuterMeasur
e`.
-/
theorem innerContent_mono ⦃U V : Set G⦄ (hU : IsOpen U) (hV : IsOpen V) (h2 : U ⊆ V) :
    μ.innerContent ⟨U, hU⟩ ≤ μ.innerContent ⟨V, hV⟩ :=
  biSup_mono fun _ hK => hK.trans h2
/-
**MeasureTheory.Content.innerContent_exists_compact** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory.Content`。
形式化陈述：innerContent_exists_compact {U : Opens G} (hU : μ.innerContent U != ∞) {ε 
: Real>=0} (hε : ε != 0) : exists K : Compacts G, (K : Set G) subseteq U ∧ μ.inn
erContent U <= μ K + ε
参数：hU : μ.innerContent U != ∞；hε : ε != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.coe_ne_zero`：coe_ne_zero : (r : Real>=0∞) != 0 ↔ r != 0
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `Set.empty_subset`：empty_subset (s : Set α) : ∅ subseteq s
· 使用定理 `le_add_left`：∀ {α : Type u} [inst : Add α] [inst_1 : Preorder α] [Canoni
callyOrderedAdd α] {a b c : α}, a ≤ c → a ≤ b + c
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `ENNReal.sub_lt_self`：∀ {a b : ENNReal}, a ≠ ⊤ → a ≠ 0 → b ≠ 0 → a - b < 
a
· 使用定理 `LT.lt.ne_bot`：∀ {α : Type u} [inst : Preorder α] [inst_1 : OrderBot α] {
a b : α}, b < a → a ≠ ⊥
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.Content.innerContent.eq_1`：∀ {G : Type w} [inst : Topologi
calSpace G] (μ : MeasureTheory.Content G) (U : TopologicalSpace.Opens G),   μ.in
nerContent U = ⨆ K, ⨆ (_ : ↑K…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `tsub_le_iff_right`：tsub_le_iff_right [LE α] [Add α] [Sub α] [OrderedSub 
α] {a b c : α} : a - b <= c ↔ a <= c + b
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem innerContent_exists_compact {U : Opens G} (hU : μ.innerContent U ≠ ∞) {ε : ℝ≥0}
    (hε : ε ≠ 0) : ∃ K : Compacts G, (K : Set G) ⊆ U ∧ μ.innerContent U ≤ μ K + ε := by
  have h'ε := ENNReal.coe_ne_zero.2 hε
  rcases le_or_gt (μ.innerContent U) ε with h | h
  · exact ⟨⊥, empty_subset _, le_add_left h⟩
  have h₂ := ENNReal.sub_lt_self hU h.ne_bot h'ε
  conv at h₂ => rhs; rw [innerContent]
  simp only [lt_iSup_iff] at h₂
  rcases h₂ with ⟨U, h1U, h2U⟩; refine ⟨U, h1U, ?_⟩
  rw [← tsub_le_iff_right]; exact le_of_lt h2U

/-- The inner content of a supremum of opens is at most the sum of the individual inner contents. -/
/-
**MeasureTheory.Content.innerContent_iSup_nat** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.Content`。
形式化陈述：innerContent_iSup_nat [R1Space G] (U : Nat -> Opens G) : μ.innerContent (⨆
 i : Nat, U i) <= ∑' i : Nat, μ.innerContent (U i)
参数：U : Nat -> Opens G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sup_empty`：sup_empty : (∅ : Finset β).sup f = ⊥
· 使用定理 `MeasureTheory.Content.empty`：empty : μ ⊥ = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.sup_insert`：sup_insert [DecidableEq β] {b : β} : (insert b s : Fi
nset β).sup f = f b ⊔ s.sup f
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `MeasureTheory.Content.sup_le`：sup_le (K₁ K₂ : Compacts G) : μ (K₁ ⊔ K₂) 
<= μ K₁ + μ K₂
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `iSup₂_le`：iSup₂_le {f : forall i, κ i -> α} (h : forall i j, f i j <= a)
 : ⨆ (i) (j), f i j <= a
· 使用定理 `IsCompact.elim_finite_subcover`：IsCompact.elim_finite_subcover {ι : Type
 v} (hs : IsCompact s) (U : ι -> Set X) (hUo : forall i, IsOpen (U i)) (hsU : s 
subseteq ⋃ i, U i) :…
· 使用定理 `TopologicalSpace.Compacts.isCompact`：∀ {α : Type u_1} [inst : Topologica
lSpace α] (s : TopologicalSpace.Compacts α), IsCompact ↑s
· 使用定理 `TopologicalSpace.Opens.isOpen`：∀ {α : Type u_2} [inst : TopologicalSpace
 α] (U : TopologicalSpace.Opens α), IsOpen ↑U
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `TopologicalSpace.Opens.coe_iSup`：coe_iSup {ι} (s : ι -> Opens α) : ((⨆ i
, s i : Opens α) : Set α) = ⋃ i, s i
· 使用定理 `IsCompact.finite_compact_cover`：IsCompact.finite_compact_cover {s : Set 
X} (hs : IsCompact s) {ι : Type*} (t : Finset ι) (U : ι -> Set X) (hU : forall i
 in t, IsOpen (U i))…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `TopologicalSpace.Compacts.ext`：∀ {α : Type u_1} [inst : TopologicalSpace
 α] {s t : TopologicalSpace.Compacts α}, ↑s = ↑t → s = t
· 使用定理 `TopologicalSpace.Compacts.coe_finset_sup`：coe_finset_sup {ι : Type*} {s 
: Finset ι} {f : ι -> Compacts α} : (↑(s.sup f) : Set α) = s.sup fun i => ↑(f i)
· 使用定理 `Finset.sup_eq_iSup`：sup_eq_iSup [CompleteLattice β] (s : Finset α) (f : 
α -> β) : s.sup f = ⨆ a in s, f a
（共 34 条，此处仅展示前 30 条）

--- 原说明 ---
The inner content of a supremum of opens is at most the sum of the individual in
ner contents.
-/
theorem innerContent_iSup_nat [R1Space G] (U : ℕ → Opens G) :
    μ.innerContent (⨆ i : ℕ, U i) ≤ ∑' i : ℕ, μ.innerContent (U i) := by
  have h3 : ∀ (t : Finset ℕ) (K : ℕ → Compacts G), μ (t.sup K) ≤ t.sum fun i => μ (K i) := by
    intro t K
    refine Finset.induction_on t ?_ ?_
    · simp only [μ.empty, nonpos_iff_eq_zero, Finset.sum_empty, Finset.sup_empty]
    · intro n s hn ih
      grw [Finset.sup_insert, Finset.sum_insert hn, μ.sup_le, ih]
  refine iSup₂_le fun K hK => ?_
  obtain ⟨t, ht⟩ :=
    K.isCompact.elim_finite_subcover _ (fun i => (U i).isOpen) (by rwa [← Opens.coe_iSup])
  rcases K.isCompact.finite_compact_cover t (SetLike.coe ∘ U) (fun i _ => (U i).isOpen) ht with
    ⟨K', h1K', h2K', h3K'⟩
  let L : ℕ → Compacts G := fun n => ⟨K' n, h1K' n⟩
  convert! le_trans (h3 t L) _
  · ext1
    rw [Compacts.coe_finset_sup, Finset.sup_eq_iSup]
    exact h3K'
  refine le_trans (Finset.sum_le_sum ?_) (ENNReal.sum_le_tsum t)
  intro i _
  refine le_trans ?_ (le_iSup _ (L i))
  refine le_trans ?_ (le_iSup _ (h2K' i))
  rfl

/-- The inner content of a union of sets is at most the sum of the individual inner contents.
  This is the "unbundled" version of `innerContent_iSup_nat`.
  It is required for the API of `inducedOuterMeasure`. -/
/-
**MeasureTheory.Content.innerContent_iUnion_nat** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.Content`。
形式化陈述：innerContent_iUnion_nat [R1Space G] ⦃U : Nat -> Set G⦄ (hU : forall i : Na
t, IsOpen (U i)) : μ.innerContent ⟨⋃ i : Nat, U i, isOpen_iUnion hU⟩ <= ∑' i : N
at, μ.innerContent ⟨U i, hU i⟩
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Content.innerContent_iSup_nat`：innerContent_iSup_nat [R1Sp
ace G] (U : Nat -> Opens G) : μ.innerContent (⨆ i : Nat, U i) <= ∑' i : Nat, μ.i
nnerContent (U i)
· 使用定理 `isOpen_iUnion`：isOpen_iUnion {f : ι -> Set X} (h : forall i, IsOpen (f i
)) : IsOpen (⋃ i, f i)
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TopologicalSpace.Opens.iSup_def`：iSup_def {ι} (s : ι -> Opens α) : ⨆ i, 
s i = ⟨⋃ i, s i, isOpen_iUnion fun i => (s i).2⟩

--- 原说明 ---
The inner content of a union of sets is at most the sum of the individual inner 
contents.
  This is the "unbundled" version of `innerContent_iSup_nat`.
  It is required for the API of `inducedOuterMeasure`.
-/
theorem innerContent_iUnion_nat [R1Space G] ⦃U : ℕ → Set G⦄
    (hU : ∀ i : ℕ, IsOpen (U i)) :
    μ.innerContent ⟨⋃ i : ℕ, U i, isOpen_iUnion hU⟩ ≤ ∑' i : ℕ, μ.innerContent ⟨U i, hU i⟩ := by
  have := μ.innerContent_iSup_nat fun i => ⟨U i, hU i⟩
  rwa [Opens.iSup_def] at this
/-
**MeasureTheory.Content.innerContent_comap** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.Content`。
形式化陈述：innerContent_comap (f : G ≃ₜ G) (h : forall ⦃K : Compacts G⦄, μ (K.map f f
.continuous) = μ K) (U : Opens G) : μ.innerContent (Opens.comap f U) = μ.innerCo
ntent U
参数：f : G ≃ₜ G；h : forall ⦃K : Compacts G⦄, μ (K.map f f.continuous) = μ K；U : Op
ens G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologic
alSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y), Continuous ⇑h
· 使用定理 `Function.Surjective.iSup_congr`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : So
rt u_5} [inst : SupSet α] {f : ι → α} {g : ι' → α} (h : ι → ι'),   Function.Surj
ective h → (∀ (x : ι…
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
-/
theorem innerContent_comap (f : G ≃ₜ G) (h : ∀ ⦃K : Compacts G⦄, μ (K.map f f.continuous) = μ K)
    (U : Opens G) : μ.innerContent (Opens.comap f U) = μ.innerContent U := by
  refine (Compacts.equiv f).surjective.iSup_congr _ fun K => iSup_congr_Prop image_subset_iff ?_
  intro hK
  simp only [Compacts.equiv]
  apply h

@[to_additive]
/-
**MeasureTheory.Content.is_mul_left_invariant_innerContent** 是 Mathlib 中的一个定理，位于
命名空间 `MeasureTheory.Content`。
形式化陈述：is_mul_left_invariant_innerContent [Group G] [SeparatelyContinuousMul G] (
h : forall (g : G) {K : Compacts G}, μ (K.map _ <| continuous_const_mul g) = μ K
) (g : G) (U : Opens G) : μ.innerContent (Opens.comap (Homeomorph.mulLeft g) U) 
= μ.innerContent U
参数：h : forall (g : G) {K : Compacts G}, μ (K.map _ <| continuous_const_mul g) = 
μ K；g : G；U : Opens G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_const_mul`：continuous_const_mul (m : M) : Continuous (m * ·)
· 使用定理 `MeasureTheory.Content.innerContent_comap`：innerContent_comap (f : G ≃ₜ G
) (h : forall ⦃K : Compacts G⦄, μ (K.map f f.continuous) = μ K) (U : Opens G) : 
μ.innerContent (Opens.comap f …
-/
theorem is_mul_left_invariant_innerContent [Group G] [SeparatelyContinuousMul G]
    (h : ∀ (g : G) {K : Compacts G}, μ (K.map _ <| continuous_const_mul g) = μ K) (g : G)
    (U : Opens G) :
    μ.innerContent (Opens.comap (Homeomorph.mulLeft g) U) = μ.innerContent U := by
  convert! μ.innerContent_comap (Homeomorph.mulLeft g) (fun K => h g) U

@[to_additive]
/-
**MeasureTheory.Content.innerContent_pos_of_is_mul_left_invariant** 是 Mathlib 中的
一个定理，位于命名空间 `MeasureTheory.Content`。
形式化陈述：innerContent_pos_of_is_mul_left_invariant [Group G] [IsTopologicalGroup G]
 (h3 : forall (g : G) {K : Compacts G}, μ (K.map _ <| continuous_const_mul g) = 
μ K) (K : Compacts G) (hK : μ K != 0) (U : Opens G) (hU : (U : Set G).Nonempty) 
: 0 < μ.innerContent U
参数：h3 : forall (g : G) {K : Compacts G}, μ (K.map _ <| continuous_const_mul g) =
 μ K；K : Compacts G；hK : μ K != 0；U : Opens G；hU : (U : Set G).Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_const_mul`：continuous_const_mul (m : M) : Continuous (m * ·)
· 使用定理 `instSeparatelyContinuousMulOfContinuousMul`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Mul M] [ContinuousMul M], SeparatelyContinuousMul M
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsOpen.interior_eq`：IsOpen.interior_eq (h : IsOpen s) : interior s = s
· 使用定理 `TopologicalSpace.Opens.isOpen`：∀ {α : Type u_2} [inst : TopologicalSpace
 α] (U : TopologicalSpace.Opens α), IsOpen ↑U
· 使用定理 `compact_covered_by_mul_left_translates`：compact_covered_by_mul_left_tran
slates {K V : Set G} (hK : IsCompact K) (hV : (interior V).Nonempty) : exists t 
: Finset G, K subseteq ⋃ g i…
· 使用定理 `TopologicalSpace.Compacts.isCompact'`：∀ {α : Type u_4} [inst : Topologic
alSpace α] (self : TopologicalSpace.Compacts α), IsCompact self.carrier
· 使用定理 `isOpen_iUnion`：isOpen_iUnion {f : ι -> Set X} (h : forall i, IsOpen (f i
)) : IsOpen (⋃ i, f i)
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `TopologicalSpace.Opens.iSup_def`：iSup_def {ι} (s : ι -> Opens α) : ⨆ i, 
s i = ⟨⋃ i, s i, isOpen_iUnion fun i => (s i).2⟩
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `MeasureTheory.Content.le_innerContent`：le_innerContent (K : Compacts G) 
(U : Opens G) (h2 : (K : Set G) subseteq U) : μ K <= μ.innerContent U
· 使用定理 `rel_iSup_sum`：∀ {M : Type u_1} [inst : AddCommMonoid M] [inst_1 : Topolo
gicalSpace M] {α : Type u_3} {γ : Type u_5}   [inst_2 : CompleteLattice α] (m : 
α …
· 使用定理 `MeasureTheory.Content.innerContent_bot`：innerContent_bot : μ.innerConten
t ⊥ = 0
· 使用定理 `MeasureTheory.Content.innerContent_iSup_nat`：innerContent_iSup_nat [R1Sp
ace G] (U : Nat -> Opens G) : μ.innerContent (⨆ i : Nat, U i) <= ∑' i : Nat, μ.i
nnerContent (U i)
· 使用定理 `instR1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [RegularSpace 
X], R1Space X
· 使用定理 `IsTopologicalGroup.regularSpace`：∀ (G : Type w) [inst : TopologicalSpace
 G] [inst_1 : Group G] [IsTopologicalGroup G], RegularSpace G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `MeasureTheory.Content.is_mul_left_invariant_innerContent`：is_mul_left_in
variant_innerContent [Group G] [SeparatelyContinuousMul G] (h : forall (g : G) {
K : Compacts G}, μ (K.map _ <| continuous_cons…
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ENNReal.mul_pos_iff`：mul_pos_iff : 0 < a * b ↔ 0 < a ∧ 0 < b
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
（共 31 条，此处仅展示前 30 条）
-/
theorem innerContent_pos_of_is_mul_left_invariant [Group G] [IsTopologicalGroup G]
    (h3 : ∀ (g : G) {K : Compacts G}, μ (K.map _ <| continuous_const_mul g) = μ K) (K : Compacts G)
    (hK : μ K ≠ 0) (U : Opens G) (hU : (U : Set G).Nonempty) : 0 < μ.innerContent U := by
  have : (interior (U : Set G)).Nonempty := by rwa [U.isOpen.interior_eq]
  rcases compact_covered_by_mul_left_translates K.2 this with ⟨s, hs⟩
  suffices μ K ≤ s.card * μ.innerContent U by
    exact (ENNReal.mul_pos_iff.mp <| hK.bot_lt.trans_le this).2
  have : (K : Set G) ⊆ ↑(⨆ g ∈ s, Opens.comap (Homeomorph.mulLeft g : C(G, G)) U) := by
    simpa only [Opens.iSup_def, Opens.coe_comap, Subtype.coe_mk]
  refine (μ.le_innerContent _ _ this).trans ?_
  refine
    (rel_iSup_sum μ.innerContent μ.innerContent_bot (· ≤ ·) μ.innerContent_iSup_nat _ _).trans ?_
  simp only [μ.is_mul_left_invariant_innerContent h3, Finset.sum_const, nsmul_eq_mul, le_refl]
/-
**MeasureTheory.Content.innerContent_mono'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.Content`。
形式化陈述：innerContent_mono' ⦃U V : Set G⦄ (hU : IsOpen U) (hV : IsOpen V) (h2 : U s
ubseteq V) : μ.innerContent ⟨U, hU⟩ <= μ.innerContent ⟨V, hV⟩
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `biSup_mono`：biSup_mono {p q : ι -> Prop} (hpq : forall i, p i -> q i) : 
⨆ (i) (_ : p i), f i <= ⨆ (i) (_ : q i), f i
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
theorem innerContent_mono' ⦃U V : Set G⦄ (hU : IsOpen U) (hV : IsOpen V) (h2 : U ⊆ V) :
    μ.innerContent ⟨U, hU⟩ ≤ μ.innerContent ⟨V, hV⟩ :=
  biSup_mono fun _ hK => hK.trans h2

section OuterMeasure

/-- Extending a content on compact sets to an outer measure on all sets. -/
/-
**MeasureTheory.Content.outerMeasure** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.Co
ntent`。
形式化陈述：{G : Type w} → [inst : TopologicalSpace G] → MeasureTheory.Content G → Mea
sureTheory.OuterMeasure G
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `isOpen_empty`：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen ∅
· 使用定理 `MeasureTheory.Content.innerContent_bot`：innerContent_bot : μ.innerConten
t ⊥ = 0

--- 原说明 ---
Extending a content on compact sets to an outer measure on all sets.
-/
protected def outerMeasure : OuterMeasure G :=
  inducedOuterMeasure (fun U hU => μ.innerContent ⟨U, hU⟩) isOpen_empty μ.innerContent_bot

variable [R1Space G]
/-
**MeasureTheory.Content.outerMeasure_opens** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.Content`。
形式化陈述：outerMeasure_opens (U : Opens G) : μ.outerMeasure U = μ.innerContent U
参数：U : Opens G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.inducedOuterMeasure_eq'`：inducedOuterMeasure_eq' {s : Set 
α} (hs : P s) : inducedOuterMeasure m P0 m0 s = m s hs
· 使用定理 `isOpen_empty`：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen ∅
· 使用定理 `MeasureTheory.Content.innerContent_bot`：innerContent_bot : μ.innerConten
t ⊥ = 0
· 使用定理 `isOpen_iUnion`：isOpen_iUnion {f : ι -> Set X} (h : forall i, IsOpen (f i
)) : IsOpen (⋃ i, f i)
· 使用定理 `MeasureTheory.Content.innerContent_iUnion_nat`：innerContent_iUnion_nat [
R1Space G] ⦃U : Nat -> Set G⦄ (hU : forall i : Nat, IsOpen (U i)) : μ.innerConte
nt ⟨⋃ i : Nat, U i, isOpen_iUnion h…
· 使用定理 `MeasureTheory.Content.innerContent_mono`：innerContent_mono ⦃U V : Set G⦄
 (hU : IsOpen U) (hV : IsOpen V) (h2 : U subseteq V) : μ.innerContent ⟨U, hU⟩ <=
 μ.innerContent ⟨V, hV⟩
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
-/
theorem outerMeasure_opens (U : Opens G) : μ.outerMeasure U = μ.innerContent U :=
  inducedOuterMeasure_eq' (fun _ => isOpen_iUnion) μ.innerContent_iUnion_nat μ.innerContent_mono U.2
/-
**MeasureTheory.Content.outerMeasure_of_isOpen** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.Content`。
形式化陈述：outerMeasure_of_isOpen (U : Set G) (hU : IsOpen U) : μ.outerMeasure U = μ.
innerContent ⟨U, hU⟩
参数：U : Set G；hU : IsOpen U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Content.outerMeasure_opens`：outerMeasure_opens (U : Opens 
G) : μ.outerMeasure U = μ.innerContent U
-/
theorem outerMeasure_of_isOpen (U : Set G) (hU : IsOpen U) :
    μ.outerMeasure U = μ.innerContent ⟨U, hU⟩ :=
  μ.outerMeasure_opens ⟨U, hU⟩
/-
**MeasureTheory.Content.outerMeasure_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.Content`。
形式化陈述：outerMeasure_le (U : Opens G) (K : Compacts G) (hUK : (U : Set G) subseteq
 K) : μ.outerMeasure U <= μ K
参数：U : Opens G；K : Compacts G；hUK : (U : Set G) subseteq K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `MeasureTheory.Content.outerMeasure_opens`：outerMeasure_opens (U : Opens 
G) : μ.outerMeasure U = μ.innerContent U
· 使用定理 `MeasureTheory.Content.innerContent_le`：innerContent_le (U : Opens G) (K 
: Compacts G) (h2 : (U : Set G) subseteq K) : μ.innerContent U <= μ K
-/
theorem outerMeasure_le (U : Opens G) (K : Compacts G) (hUK : (U : Set G) ⊆ K) :
    μ.outerMeasure U ≤ μ K :=
  (μ.outerMeasure_opens U).le.trans <| μ.innerContent_le U K hUK

set_option backward.isDefEq.respectTransparency false in
/-
**MeasureTheory.Content.le_outerMeasure_compacts** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.Content`。
形式化陈述：le_outerMeasure_compacts (K : Compacts G) : μ K <= μ.outerMeasure K
参数：K : Compacts G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isOpen_empty`：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen ∅
· 使用定理 `MeasureTheory.Content.innerContent_bot`：innerContent_bot : μ.innerConten
t ⊥ = 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Content.outerMeasure.eq_1`：∀ {G : Type w} [inst : Topologi
calSpace G] (μ : MeasureTheory.Content G),   μ.outerMeasure = MeasureTheory.indu
cedOuterMeasure (fun U hU => …
· 使用定理 `MeasureTheory.inducedOuterMeasure_eq_iInf`：inducedOuterMeasure_eq_iInf (
s : Set α) : inducedOuterMeasure m P0 m0 s = ⨅ (t : Set α) (ht : P t) (_ : s sub
seteq t), m t ht
· 使用定理 `isOpen_iUnion`：isOpen_iUnion {f : ι -> Set X} (h : forall i, IsOpen (f i
)) : IsOpen (⋃ i, f i)
· 使用定理 `MeasureTheory.Content.innerContent_iUnion_nat`：innerContent_iUnion_nat [
R1Space G] ⦃U : Nat -> Set G⦄ (hU : forall i : Nat, IsOpen (U i)) : μ.innerConte
nt ⟨⋃ i : Nat, U i, isOpen_iUnion h…
· 使用定理 `MeasureTheory.Content.innerContent_mono`：innerContent_mono ⦃U V : Set G⦄
 (hU : IsOpen U) (hV : IsOpen V) (h2 : U subseteq V) : μ.innerContent ⟨U, hU⟩ <=
 μ.innerContent ⟨V, hV⟩
· 使用定理 `le_iInf`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] {f :
 ι → α} {a : α}, (∀ (i : ι), a ≤ f i) → a ≤ iInf f
· 使用定理 `MeasureTheory.Content.le_innerContent`：le_innerContent (K : Compacts G) 
(U : Opens G) (h2 : (K : Set G) subseteq U) : μ K <= μ.innerContent U
-/
theorem le_outerMeasure_compacts (K : Compacts G) : μ K ≤ μ.outerMeasure K := by
  rw [Content.outerMeasure, inducedOuterMeasure_eq_iInf]
  · exact le_iInf fun U => le_iInf fun hU => le_iInf <| μ.le_innerContent K ⟨U, hU⟩
  · exact fun U hU => isOpen_iUnion hU
  · exact μ.innerContent_iUnion_nat
  · exact μ.innerContent_mono
/-
**MeasureTheory.Content.outerMeasure_eq_iInf** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.Content`。
形式化陈述：outerMeasure_eq_iInf (A : Set G) : μ.outerMeasure A = ⨅ (U : Set G) (hU : 
IsOpen U) (_ : A subseteq U), μ.innerContent ⟨U, hU⟩
参数：A : Set G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.inducedOuterMeasure_eq_iInf`：inducedOuterMeasure_eq_iInf (
s : Set α) : inducedOuterMeasure m P0 m0 s = ⨅ (t : Set α) (ht : P t) (_ : s sub
seteq t), m t ht
· 使用定理 `isOpen_empty`：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen ∅
· 使用定理 `MeasureTheory.Content.innerContent_bot`：innerContent_bot : μ.innerConten
t ⊥ = 0
· 使用定理 `isOpen_iUnion`：isOpen_iUnion {f : ι -> Set X} (h : forall i, IsOpen (f i
)) : IsOpen (⋃ i, f i)
· 使用定理 `MeasureTheory.Content.innerContent_iUnion_nat`：innerContent_iUnion_nat [
R1Space G] ⦃U : Nat -> Set G⦄ (hU : forall i : Nat, IsOpen (U i)) : μ.innerConte
nt ⟨⋃ i : Nat, U i, isOpen_iUnion h…
· 使用定理 `MeasureTheory.Content.innerContent_mono`：innerContent_mono ⦃U V : Set G⦄
 (hU : IsOpen U) (hV : IsOpen V) (h2 : U subseteq V) : μ.innerContent ⟨U, hU⟩ <=
 μ.innerContent ⟨V, hV⟩
-/
theorem outerMeasure_eq_iInf (A : Set G) :
    μ.outerMeasure A = ⨅ (U : Set G) (hU : IsOpen U) (_ : A ⊆ U), μ.innerContent ⟨U, hU⟩ :=
  inducedOuterMeasure_eq_iInf _ μ.innerContent_iUnion_nat μ.innerContent_mono A
/-
**MeasureTheory.Content.outerMeasure_interior_compacts** 是 Mathlib 中的一个定理，位于命名空间
 `MeasureTheory.Content`。
形式化陈述：outerMeasure_interior_compacts (K : Compacts G) : μ.outerMeasure (interior
 K) <= μ K
参数：K : Compacts G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `MeasureTheory.Content.outerMeasure_opens`：outerMeasure_opens (U : Opens 
G) : μ.outerMeasure U = μ.innerContent U
· 使用定理 `MeasureTheory.Content.innerContent_le`：innerContent_le (U : Opens G) (K 
: Compacts G) (h2 : (U : Set G) subseteq K) : μ.innerContent U <= μ K
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s
-/
theorem outerMeasure_interior_compacts (K : Compacts G) : μ.outerMeasure (interior K) ≤ μ K :=
  (μ.outerMeasure_opens <| Opens.interior K).le.trans <| μ.innerContent_le _ _ interior_subset
/-
**MeasureTheory.Content.outerMeasure_exists_compact** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory.Content`。
形式化陈述：outerMeasure_exists_compact {U : Opens G} (hU : μ.outerMeasure U != ∞) {ε 
: Real>=0} (hε : ε != 0) : exists K : Compacts G, (K : Set G) subseteq U ∧ μ.out
erMeasure U <= μ.outerMeasure K + ε
参数：hU : μ.outerMeasure U != ∞；hε : ε != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Content.outerMeasure_opens`：outerMeasure_opens (U : Opens 
G) : μ.outerMeasure U = μ.innerContent U
· 使用定理 `MeasureTheory.Content.innerContent_exists_compact`：innerContent_exists_c
ompact {U : Opens G} (hU : μ.innerContent U != ∞) {ε : Real>=0} (hε : ε != 0) : 
exists K : Compacts G, (K : Set G) subs…
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `MeasureTheory.Content.le_outerMeasure_compacts`：le_outerMeasure_compacts
 (K : Compacts G) : μ K <= μ.outerMeasure K
-/
theorem outerMeasure_exists_compact {U : Opens G} (hU : μ.outerMeasure U ≠ ∞) {ε : ℝ≥0}
    (hε : ε ≠ 0) : ∃ K : Compacts G, (K : Set G) ⊆ U ∧ μ.outerMeasure U ≤ μ.outerMeasure K + ε := by
  rw [μ.outerMeasure_opens] at hU ⊢
  rcases μ.innerContent_exists_compact hU hε with ⟨K, h1K, h2K⟩
  exact ⟨K, h1K, by grw [h2K, μ.le_outerMeasure_compacts K]⟩
/-
**MeasureTheory.Content.outerMeasure_exists_open** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.Content`。
形式化陈述：outerMeasure_exists_open {A : Set G} (hA : μ.outerMeasure A != ∞) {ε : Rea
l>=0} (hε : ε != 0) : exists U : Opens G, A subseteq U ∧ μ.outerMeasure U <= μ.o
uterMeasure A + ε
参数：hA : μ.outerMeasure A != ∞；hε : ε != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isOpen_empty`：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen ∅
· 使用定理 `MeasureTheory.Content.innerContent_bot`：innerContent_bot : μ.innerConten
t ⊥ = 0
· 使用定理 `MeasureTheory.inducedOuterMeasure_exists_set`：inducedOuterMeasure_exists
_set {s : Set α} (hs : inducedOuterMeasure m P0 m0 s != ∞) {ε : Real>=0∞} (hε : 
ε != 0) : exists t : Set α, P t ∧ …
· 使用定理 `isOpen_iUnion`：isOpen_iUnion {f : ι -> Set X} (h : forall i, IsOpen (f i
)) : IsOpen (⋃ i, f i)
· 使用定理 `MeasureTheory.Content.innerContent_iUnion_nat`：innerContent_iUnion_nat [
R1Space G] ⦃U : Nat -> Set G⦄ (hU : forall i : Nat, IsOpen (U i)) : μ.innerConte
nt ⟨⋃ i : Nat, U i, isOpen_iUnion h…
· 使用定理 `MeasureTheory.Content.innerContent_mono`：innerContent_mono ⦃U V : Set G⦄
 (hU : IsOpen U) (hV : IsOpen V) (h2 : U subseteq V) : μ.innerContent ⟨U, hU⟩ <=
 μ.innerContent ⟨V, hV⟩
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.coe_ne_zero`：coe_ne_zero : (r : Real>=0∞) != 0 ↔ r != 0
-/
theorem outerMeasure_exists_open {A : Set G} (hA : μ.outerMeasure A ≠ ∞) {ε : ℝ≥0} (hε : ε ≠ 0) :
    ∃ U : Opens G, A ⊆ U ∧ μ.outerMeasure U ≤ μ.outerMeasure A + ε := by
  rcases inducedOuterMeasure_exists_set _ μ.innerContent_iUnion_nat μ.innerContent_mono hA
      (ENNReal.coe_ne_zero.2 hε) with
    ⟨U, hU, h2U, h3U⟩
  exact ⟨⟨U, hU⟩, h2U, h3U⟩
/-
**MeasureTheory.Content.outerMeasure_preimage** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.Content`。
形式化陈述：outerMeasure_preimage (f : G ≃ₜ G) (h : forall ⦃K : Compacts G⦄, μ (K.map 
f f.continuous) = μ K) (A : Set G) : μ.outerMeasure (f ⁻¹' A) = μ.outerMeasure A
参数：f : G ≃ₜ G；h : forall ⦃K : Compacts G⦄, μ (K.map f f.continuous) = μ K；A : Se
t G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologic
alSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y), Continuous ⇑h
· 使用定理 `MeasureTheory.inducedOuterMeasure_preimage`：inducedOuterMeasure_preimage
 (f : α ≃ α) (Pm : forall s : Set α, P (f ⁻¹' s) ↔ P s) (mm : forall (s : Set α)
 (hs : P s), m (f ⁻¹' s) ((Pm _)…
· 使用定理 `isOpen_empty`：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen ∅
· 使用定理 `MeasureTheory.Content.innerContent_bot`：innerContent_bot : μ.innerConten
t ⊥ = 0
· 使用定理 `isOpen_iUnion`：isOpen_iUnion {f : ι -> Set X} (h : forall i, IsOpen (f i
)) : IsOpen (⋃ i, f i)
· 使用定理 `MeasureTheory.Content.innerContent_iUnion_nat`：innerContent_iUnion_nat [
R1Space G] ⦃U : Nat -> Set G⦄ (hU : forall i : Nat, IsOpen (U i)) : μ.innerConte
nt ⟨⋃ i : Nat, U i, isOpen_iUnion h…
· 使用定理 `MeasureTheory.Content.innerContent_mono`：innerContent_mono ⦃U V : Set G⦄
 (hU : IsOpen U) (hV : IsOpen V) (h2 : U subseteq V) : μ.innerContent ⟨U, hU⟩ <=
 μ.innerContent ⟨V, hV⟩
· 使用定理 `Homeomorph.isOpen_preimage`：isOpen_preimage (h : X ≃ₜ Y) {s : Set Y} : I
sOpen (h ⁻¹' s) ↔ IsOpen s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
· 使用定理 `MeasureTheory.Content.innerContent_comap`：innerContent_comap (f : G ≃ₜ G
) (h : forall ⦃K : Compacts G⦄, μ (K.map f f.continuous) = μ K) (U : Opens G) : 
μ.innerContent (Opens.comap f …
-/
theorem outerMeasure_preimage (f : G ≃ₜ G) (h : ∀ ⦃K : Compacts G⦄, μ (K.map f f.continuous) = μ K)
    (A : Set G) : μ.outerMeasure (f ⁻¹' A) = μ.outerMeasure A := by
  refine inducedOuterMeasure_preimage _ μ.innerContent_iUnion_nat μ.innerContent_mono _
    (fun _ => f.isOpen_preimage) ?_
  intro s hs
  convert! μ.innerContent_comap f h ⟨s, hs⟩
/-
**MeasureTheory.Content.outerMeasure_lt_top_of_isCompact** 是 Mathlib 中的一个定理，位于命名
空间 `MeasureTheory.Content`。
形式化陈述：outerMeasure_lt_top_of_isCompact [WeaklyLocallyCompactSpace G] {K : Set G}
 (hK : IsCompact K) : μ.outerMeasure K < ∞
参数：hK : IsCompact K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_compact_superset`：exists_compact_superset [WeaklyLocallyCompactSp
ace X] {K : Set X} (hK : IsCompact K) : exists K', IsCompact K' ∧ K subseteq int
erior K'
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.OuterMeasure.instOuterMeasureClass`：∀ {α : Type u_1}, Meas
ureTheory.OuterMeasureClass (MeasureTheory.OuterMeasure α) α
· 使用定理 `MeasureTheory.Content.outerMeasure_le`：outerMeasure_le (U : Opens G) (K 
: Compacts G) (hUK : (U : Set G) subseteq K) : μ.outerMeasure U <= μ K
· 使用定理 `isOpen_interior`：isOpen_interior : IsOpen (interior s)
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s
· 使用定理 `MeasureTheory.Content.lt_top`：lt_top (K : Compacts G) : μ K < ∞
-/
theorem outerMeasure_lt_top_of_isCompact [WeaklyLocallyCompactSpace G]
    {K : Set G} (hK : IsCompact K) :
    μ.outerMeasure K < ∞ := by
  rcases exists_compact_superset hK with ⟨F, h1F, h2F⟩
  calc
    μ.outerMeasure K ≤ μ.outerMeasure (interior F) := measure_mono h2F
    _ ≤ μ ⟨F, h1F⟩ := by
      apply μ.outerMeasure_le ⟨interior F, isOpen_interior⟩ ⟨F, h1F⟩ interior_subset
    _ < ⊤ := μ.lt_top _

@[to_additive]
/-
**MeasureTheory.Content.is_mul_left_invariant_outerMeasure** 是 Mathlib 中的一个定理，位于
命名空间 `MeasureTheory.Content`。
形式化陈述：is_mul_left_invariant_outerMeasure [Group G] [SeparatelyContinuousMul G] (
h : forall (g : G) {K : Compacts G}, μ (K.map _ <| continuous_const_mul g) = μ K
) (g : G) (A : Set G) : μ.outerMeasure ((g * ·) ⁻¹' A) = μ.outerMeasure A
参数：h : forall (g : G) {K : Compacts G}, μ (K.map _ <| continuous_const_mul g) = 
μ K；g : G；A : Set G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_const_mul`：continuous_const_mul (m : M) : Continuous (m * ·)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.Content.outerMeasure_preimage`：outerMeasure_preimage (f : 
G ≃ₜ G) (h : forall ⦃K : Compacts G⦄, μ (K.map f f.continuous) = μ K) (A : Set G
) : μ.outerMeasure (f ⁻¹' A) = μ.…
-/
theorem is_mul_left_invariant_outerMeasure [Group G] [SeparatelyContinuousMul G]
    (h : ∀ (g : G) {K : Compacts G}, μ (K.map _ <| continuous_const_mul g) = μ K) (g : G)
    (A : Set G) : μ.outerMeasure ((g * ·) ⁻¹' A) = μ.outerMeasure A := by
  convert! μ.outerMeasure_preimage (Homeomorph.mulLeft g) (fun K => h g) A
/-
**MeasureTheory.Content.outerMeasure_caratheodory** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory.Content`。
形式化陈述：outerMeasure_caratheodory (A : Set G) : MeasurableSet[μ.outerMeasure.carat
heodory] A ↔ forall U : Opens G, μ.outerMeasure (U inter A) + μ.outerMeasure (U 
\ A) <= μ.outerMeasure U
参数：A : Set G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TopologicalSpace.Opens.forall`：∀ {α : Type u_2} [inst : TopologicalSpace
 α] {p : TopologicalSpace.Opens α → Prop},   (∀ (U : TopologicalSpace.Opens α), 
p U) ↔ ∀ (U : Set α…
· 使用定理 `MeasureTheory.inducedOuterMeasure_caratheodory`：inducedOuterMeasure_cara
theodory (s : Set α) : MeasurableSet[(inducedOuterMeasure m P0 m0).caratheodory]
 s ↔ forall t : Set α, P t -> induce…
· 使用定理 `isOpen_empty`：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen ∅
· 使用定理 `MeasureTheory.Content.innerContent_bot`：innerContent_bot : μ.innerConten
t ⊥ = 0
· 使用定理 `isOpen_iUnion`：isOpen_iUnion {f : ι -> Set X} (h : forall i, IsOpen (f i
)) : IsOpen (⋃ i, f i)
· 使用定理 `MeasureTheory.Content.innerContent_iUnion_nat`：innerContent_iUnion_nat [
R1Space G] ⦃U : Nat -> Set G⦄ (hU : forall i : Nat, IsOpen (U i)) : μ.innerConte
nt ⟨⋃ i : Nat, U i, isOpen_iUnion h…
· 使用定理 `MeasureTheory.Content.innerContent_mono'`：innerContent_mono' ⦃U V : Set 
G⦄ (hU : IsOpen U) (hV : IsOpen V) (h2 : U subseteq V) : μ.innerContent ⟨U, hU⟩ 
<= μ.innerContent ⟨V, hV⟩
-/
theorem outerMeasure_caratheodory (A : Set G) :
    MeasurableSet[μ.outerMeasure.caratheodory] A ↔
      ∀ U : Opens G, μ.outerMeasure (U ∩ A) + μ.outerMeasure (U \ A) ≤ μ.outerMeasure U := by
  rw [Opens.forall]
  apply inducedOuterMeasure_caratheodory
  · apply innerContent_iUnion_nat
  · apply innerContent_mono'

@[to_additive]
/-
**MeasureTheory.Content.outerMeasure_pos_of_is_mul_left_invariant** 是 Mathlib 中的
一个定理，位于命名空间 `MeasureTheory.Content`。
形式化陈述：outerMeasure_pos_of_is_mul_left_invariant [Group G] [IsTopologicalGroup G]
 (h3 : forall (g : G) {K : Compacts G}, μ (K.map _ <| continuous_const_mul g) = 
μ K) (K : Compacts G) (hK : μ K != 0) {U : Set G} (h1U : IsOpen U) (h2U : U.None
mpty) : 0 < μ.outerMeasure U
参数：h3 : forall (g : G) {K : Compacts G}, μ (K.map _ <| continuous_const_mul g) =
 μ K；K : Compacts G；hK : μ K != 0；h1U : IsOpen U；h2U : U.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_const_mul`：continuous_const_mul (m : M) : Continuous (m * ·)
· 使用定理 `instSeparatelyContinuousMulOfContinuousMul`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Mul M] [ContinuousMul M], SeparatelyContinuousMul M
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Content.outerMeasure_opens`：outerMeasure_opens (U : Opens 
G) : μ.outerMeasure U = μ.innerContent U
· 使用定理 `MeasureTheory.Content.innerContent_pos_of_is_mul_left_invariant`：innerCo
ntent_pos_of_is_mul_left_invariant [Group G] [IsTopologicalGroup G] (h3 : forall
 (g : G) {K : Compacts G}, μ (K.map _ <| continuous_c…
-/
theorem outerMeasure_pos_of_is_mul_left_invariant [Group G] [IsTopologicalGroup G]
    (h3 : ∀ (g : G) {K : Compacts G}, μ (K.map _ <| continuous_const_mul g) = μ K) (K : Compacts G)
    (hK : μ K ≠ 0) {U : Set G} (h1U : IsOpen U) (h2U : U.Nonempty) : 0 < μ.outerMeasure U := by
  convert! μ.innerContent_pos_of_is_mul_left_invariant h3 K hK ⟨U, h1U⟩ h2U
  exact μ.outerMeasure_opens ⟨U, h1U⟩

variable [S : MeasurableSpace G] [BorelSpace G]

/-- For the outer measure coming from a content, all Borel sets are measurable. -/
/-
**MeasureTheory.Content.borel_le_caratheodory** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.Content`。
形式化陈述：borel_le_caratheodory : S <= μ.outerMeasure.caratheodory
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `BorelSpace.measurable_eq`：∀ {α : Type u_6} {inst : TopologicalSpace α} {
inst_1 : MeasurableSpace α} [self : BorelSpace α], inst_1 = borel α
· 使用定理 `MeasurableSpace.generateFrom_le`：generateFrom_le {s : Set (Set α)} {m : 
MeasurableSpace α} (h : forall t in s, MeasurableSet[m] t) : generateFrom s <= m
· 使用定理 `MeasureTheory.Content.outerMeasure_caratheodory`：outerMeasure_caratheodo
ry (A : Set G) : MeasurableSet[μ.outerMeasure.caratheodory] A ↔ forall U : Opens
 G, μ.outerMeasure (U inter A) + μ.ou…
· 使用定理 `IsOpen.inter`：IsOpen.inter (s t : Set α) : IsOpen α s -> IsOpen α t -> I
sOpen α (s inter t)
· 使用定理 `TopologicalSpace.Opens.isOpen`：∀ {α : Type u_2} [inst : TopologicalSpace
 α] (U : TopologicalSpace.Opens α), IsOpen ↑U
· 使用定理 `MeasureTheory.Content.outerMeasure_of_isOpen`：outerMeasure_of_isOpen (U 
: Set G) (hU : IsOpen U) : μ.outerMeasure U = μ.innerContent ⟨U, hU⟩
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iSup_subtype'`：iSup_subtype' {p : ι -> Prop} {f : forall i, p i -> α} : 
⨆ (i) (h), f i h = ⨆ x : Subtype p, f x x.property
· 使用定理 `TopologicalSpace.Opens.coe_mk`：coe_mk {U : Set α} {hU : IsOpen U} : ↑(⟨U
, hU⟩ : Opens α) = U
· 使用定理 `Set.empty_subset`：empty_subset (s : Set α) : ∅ subseteq s
· 使用引理 `ENNReal.iSup_add`：iSup_add [Nonempty ι] (f : ι -> Real>=0∞) : (⨆ i, f i)
 + a = ⨆ i, f i + a
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `IsCompact.closure`：∀ {X : Type u_1} [inst : TopologicalSpace X] [R1Space
 X] {K : Set X}, IsCompact K → IsCompact (closure K)
· 使用定理 `TopologicalSpace.Compacts.isCompact`：∀ {α : Type u_1} [inst : Topologica
lSpace α] (s : TopologicalSpace.Compacts α), IsCompact ↑s
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `MeasureTheory.Content.mono`：mono (K₁ K₂ : Compacts G) (h : (K₁ : Set G) 
subseteq K₂) : μ K₁ <= μ K₂
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `IsCompact.closure_subset_of_isOpen`：IsCompact.closure_subset_of_isOpen {
K : Set X} (hK : IsCompact K) {U : Set X} (hU : IsOpen U) (hKU : K subseteq U) :
 closure K subseteq U
· 使用定理 `TopologicalSpace.Compacts.isCompact'`：∀ {α : Type u_4} [inst : Topologic
alSpace α] (self : TopologicalSpace.Compacts α), IsCompact self.carrier
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Set.sdiff_subset_sdiff_right`：sdiff_subset_sdiff_right {s t u : Set α} (
h : t subseteq u) : s \ u subseteq s \ t
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
（共 46 条，此处仅展示前 30 条）

--- 原说明 ---
For the outer measure coming from a content, all Borel sets are measurable.
-/
theorem borel_le_caratheodory : S ≤ μ.outerMeasure.caratheodory := by
  rw [BorelSpace.measurable_eq (α := G)]
  refine MeasurableSpace.generateFrom_le ?_
  intro U hU
  rw [μ.outerMeasure_caratheodory]
  intro U'
  rw [μ.outerMeasure_of_isOpen ((U' : Set G) ∩ U) (U'.isOpen.inter hU)]
  simp only [innerContent, iSup_subtype']
  rw [Opens.coe_mk]
  have : Nonempty { L : Compacts G // (L : Set G) ⊆ U' ∩ U } := ⟨⟨⊥, empty_subset _⟩⟩
  rw [ENNReal.iSup_add]
  refine iSup_le ?_
  rintro ⟨L, hL⟩
  let L' : Compacts G := ⟨closure L, L.isCompact.closure⟩
  dsimp
  grw [show μ L ≤ μ L' from μ.mono _ _ subset_closure]
  simp only [subset_inter_iff] at hL
  have hL'U : (L' : Set G) ⊆ U := IsCompact.closure_subset_of_isOpen L.2 hU hL.2
  have hL'U' : (L' : Set G) ⊆ (U' : Set G) := IsCompact.closure_subset_of_isOpen L.2 U'.2 hL.1
  have : ↑U' \ U ⊆ U' \ L' := sdiff_subset_sdiff_right hL'U
  grw [this]
  rw [μ.outerMeasure_of_isOpen (↑U' \ L') (IsOpen.sdiff U'.2 isClosed_closure)]
  simp only [innerContent, iSup_subtype']
  rw [Opens.coe_mk]
  have : Nonempty { M : Compacts G // (M : Set G) ⊆ ↑U' \ closure L } := ⟨⟨⊥, empty_subset _⟩⟩
  rw [ENNReal.add_iSup]
  refine iSup_le ?_
  rintro ⟨M, hM⟩
  let M' : Compacts G := ⟨closure M, M.isCompact.closure⟩
  dsimp
  grw [show μ M ≤ μ M' from μ.mono _ _ subset_closure]
  have hM' : (M' : Set G) ⊆ U' \ L' :=
    IsCompact.closure_subset_of_isOpen M.2 (IsOpen.sdiff U'.2 isClosed_closure) hM
  have : (↑(L' ⊔ M') : Set G) ⊆ U' := by
    simp only [Compacts.coe_sup, union_subset_iff, hL'U', true_and]
    exact hM'.trans sdiff_subset
  rw [μ.outerMeasure_of_isOpen (↑U') U'.2]
  refine le_trans (ge_of_eq ?_) (μ.le_innerContent _ _ this)
  exact μ.sup_disjoint L' M' (subset_sdiff.1 hM').2.symm isClosed_closure isClosed_closure

/-- The measure induced by the outer measure coming from a content, on the Borel sigma-algebra. -/
/-
**MeasureTheory.Content.measure** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.Content
`。
形式化陈述：{G : Type w} →   [inst : TopologicalSpace G] →     MeasureTheory.Content G
 → [R1Space G] → [S : MeasurableSpace G] → [BorelSpace G] → MeasureTheory.Measur
e G
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Content.borel_le_caratheodory`：borel_le_caratheodory : S <
= μ.outerMeasure.caratheodory

--- 原说明 ---
The measure induced by the outer measure coming from a content, on the Borel sig
ma-algebra.
-/
protected def measure : Measure G :=
  μ.outerMeasure.toMeasure μ.borel_le_caratheodory
/-
**MeasureTheory.Content.measure_apply** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.C
ontent`。
形式化陈述：measure_apply {s : Set G} (hs : MeasurableSet s) : μ.measure s = μ.outerMe
asure s
参数：hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.toMeasure_apply`：toMeasure_apply (m : OuterMeasure α) (h :
 ms <= m.caratheodory) {s : Set α} (hs : MeasurableSet s) : m.toMeasure h s = m 
s
· 使用定理 `MeasureTheory.Content.borel_le_caratheodory`：borel_le_caratheodory : S <
= μ.outerMeasure.caratheodory
-/
theorem measure_apply {s : Set G} (hs : MeasurableSet s) : μ.measure s = μ.outerMeasure s :=
  toMeasure_apply _ _ hs
/-
**MeasureTheory.Content.outerRegular** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Co
ntent`。
形式化陈述：outerRegular : μ.measure.OuterRegular
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `MeasureTheory.Content.outerMeasure_eq_iInf`：outerMeasure_eq_iInf (A : Se
t G) : μ.outerMeasure A = ⨅ (U : Set G) (hU : IsOpen U) (_ : A subseteq U), μ.in
nerContent ⟨U, hU⟩
· 使用定理 `MeasureTheory.Content.measure_apply`：measure_apply {s : Set G} (hs : Mea
surableSet s) : μ.measure s = μ.outerMeasure s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsOpen.measurableSet`：IsOpen.measurableSet (h : IsOpen s) : MeasurableSe
t s
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `MeasureTheory.Content.outerMeasure_of_isOpen`：outerMeasure_of_isOpen (U 
: Set G) (hU : IsOpen U) : μ.outerMeasure U = μ.innerContent ⟨U, hU⟩
-/
instance outerRegular : μ.measure.OuterRegular := by
  refine ⟨fun A hA r (hr : _ < _) ↦ ?_⟩
  rw [μ.measure_apply hA, outerMeasure_eq_iInf] at hr
  simp only [iInf_lt_iff] at hr
  rcases hr with ⟨U, hUo, hAU, hr⟩
  rw [← μ.outerMeasure_of_isOpen U hUo, ← μ.measure_apply hUo.measurableSet] at hr
  exact ⟨U, hAU, hUo, hr⟩

/-- In a locally compact space, any measure constructed from a content is regular. -/
/-
**MeasureTheory.Content.regular** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Content
`。
形式化陈述：regular [WeaklyLocallyCompactSpace G] : μ.measure.Regular
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Content.measure_apply`：measure_apply {s : Set G} (hs : Mea
surableSet s) : μ.measure s = μ.outerMeasure s
· 使用定理 `IsClosed.measurableSet`：IsClosed.measurableSet (h : IsClosed s) : Measur
ableSet s
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
· 使用定理 `MeasureTheory.Content.outerMeasure_lt_top_of_isCompact`：outerMeasure_lt_
top_of_isCompact [WeaklyLocallyCompactSpace G] {K : Set G} (hK : IsCompact K) : 
μ.outerMeasure K < ∞
· 使用定理 `IsCompact.closure`：∀ {X : Type u_1} [inst : TopologicalSpace X] [R1Space
 X] {K : Set X}, IsCompact K → IsCompact (closure K)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.Content.outerMeasure_of_isOpen`：outerMeasure_of_isOpen (U 
: Set G) (hU : IsOpen U) : μ.outerMeasure U = μ.innerContent ⟨U, hU⟩
· 使用定理 `IsOpen.measurableSet`：IsOpen.measurableSet (h : IsOpen s) : MeasurableSe
t s
· 使用定理 `TopologicalSpace.Compacts.isCompact'`：∀ {α : Type u_4} [inst : Topologic
alSpace α] (self : TopologicalSpace.Compacts α), IsCompact self.carrier
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `MeasureTheory.Content.le_outerMeasure_compacts`：le_outerMeasure_compacts
 (K : Compacts G) : μ K <= μ.outerMeasure K
· 使用定理 `MeasureTheory.le_toMeasure_apply`：le_toMeasure_apply (m : OuterMeasure α
) (h : ms <= m.caratheodory) (s : Set α) : m s <= m.toMeasure h s
· 使用定理 `MeasureTheory.Content.borel_le_caratheodory`：borel_le_caratheodory : S <
= μ.outerMeasure.caratheodory

--- 原说明 ---
In a locally compact space, any measure constructed from a content is regular.
-/
instance regular [WeaklyLocallyCompactSpace G] : μ.measure.Regular := by
  have : IsFiniteMeasureOnCompacts μ.measure := by
    refine ⟨fun K hK => ?_⟩
    apply (measure_mono subset_closure).trans_lt _
    rw [measure_apply _ isClosed_closure.measurableSet]
    exact μ.outerMeasure_lt_top_of_isCompact hK.closure
  refine ⟨fun U hU r hr => ?_⟩
  rw [measure_apply _ hU.measurableSet, μ.outerMeasure_of_isOpen U hU] at hr
  simp only [innerContent, lt_iSup_iff] at hr
  rcases hr with ⟨K, hKU, hr⟩
  refine ⟨K, hKU, K.2, hr.trans_le ?_⟩
  exact (μ.le_outerMeasure_compacts K).trans (le_toMeasure_apply _ _ _)

end OuterMeasure

section RegularContents

/-- A content `μ` is called regular if for every compact set `K`,
  `μ(K) = inf {μ(K') : K ⊂ int K' ⊂ K'}`. See Paul Halmos (1950), Measure Theory, §54. -/
/-
**MeasureTheory.Content.ContentRegular** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.
Content`。
形式化陈述：ContentRegular
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A content `μ` is called regular if for every compact set `K`,
  `μ(K) = inf {μ(K') : K ⊂ int K' ⊂ K'}`. See Paul Halmos (1950), Measure Theory
, §54.
-/
def ContentRegular :=
  ∀ ⦃K : TopologicalSpace.Compacts G⦄,
    μ K = ⨅ (K' : TopologicalSpace.Compacts G) (_ : (K : Set G) ⊆ interior (K' : Set G)), μ K'
/-
**MeasureTheory.Content.contentRegular_exists_compact** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory.Content`。
形式化陈述：contentRegular_exists_compact (H : ContentRegular μ) (K : TopologicalSpace
.Compacts G) {ε : NNReal} (hε : ε != 0) : exists K' : TopologicalSpace.Compacts 
G, K.carrier subseteq interior K'.carrier ∧ μ K' <= μ K + ε
参数：H : ContentRegular μ；K : TopologicalSpace.Compacts G；hε : ε != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `le_iInf`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] {f :
 ι → α} {a : α}, (∀ (i : ι), a ≤ f i) → a ≤ iInf f
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `lt_self_iff_false`：lt_self_iff_false (x : α) : x < x ↔ False
· 使用定理 `lt_of_le_of_lt'`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, b ≤ a
 → c < b → c < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.lt_add_right`：lt_add_right (ha : a != ∞) (hb : b != 0) : a < a +
 b
· 使用定理 `ne_top_of_lt`：ne_top_of_lt (h : a < b) : a != ⊤
· 使用定理 `MeasureTheory.Content.lt_top`：lt_top (K : Compacts G) : μ K < ∞
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.coe_ne_zero`：coe_ne_zero : (r : Real>=0∞) != 0 ↔ r != 0
-/
theorem contentRegular_exists_compact (H : ContentRegular μ) (K : TopologicalSpace.Compacts G)
    {ε : NNReal} (hε : ε ≠ 0) :
    ∃ K' : TopologicalSpace.Compacts G, K.carrier ⊆ interior K'.carrier ∧ μ K' ≤ μ K + ε := by
  by_contra hc
  simp only [not_exists, not_and, not_le] at hc
  have lower_bound_iInf : μ K + ε ≤
      ⨅ (K' : TopologicalSpace.Compacts G) (_ : (K : Set G) ⊆ interior (K' : Set G)), μ K' :=
    le_iInf fun K' => le_iInf fun K'_hyp => le_of_lt (hc K' K'_hyp)
  rw [← H] at lower_bound_iInf
  exact (lt_self_iff_false (μ K)).mp (lt_of_le_of_lt' lower_bound_iInf
    (ENNReal.lt_add_right (ne_top_of_lt (μ.lt_top K)) (ENNReal.coe_ne_zero.mpr hε)))

variable [MeasurableSpace G] [R1Space G] [BorelSpace G]

/-- If `μ` is a regular content, then the measure induced by `μ` will agree with `μ`
  on compact sets. -/
/-
**MeasureTheory.Content.measure_eq_content_of_regular** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory.Content`。
形式化陈述：measure_eq_content_of_regular (H : MeasureTheory.Content.ContentRegular μ)
 (K : TopologicalSpace.Compacts G) : μ.measure ↑K = μ K
参数：H : MeasureTheory.Content.ContentRegular μ；K : TopologicalSpace.Compacts G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `ENNReal.le_of_forall_pos_le_add`：le_of_forall_pos_le_add (h : forall ε :
 Real>=0, 0 < ε -> b < ∞ -> a <= b + ε) : a <= b
· 使用定理 `MeasureTheory.Content.contentRegular_exists_compact`：contentRegular_exis
ts_compact (H : ContentRegular μ) (K : TopologicalSpace.Compacts G) {ε : NNReal}
 (hε : ε != 0) : exists K' : TopologicalS…
· 使用定理 `ne_bot_of_gt`：∀ {α : Type u} [inst : Preorder α] [inst_1 : OrderBot α] {
a b : α}, b < a → a ≠ ⊥
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Content.measure_apply`：measure_apply {s : Set G} (hs : Mea
surableSet s) : μ.measure s = μ.outerMeasure s
· 使用定理 `IsOpen.measurableSet`：IsOpen.measurableSet (h : IsOpen s) : MeasurableSe
t s
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `isOpen_interior`：isOpen_interior : IsOpen (interior s)
· 使用定理 `MeasureTheory.Content.outerMeasure_interior_compacts`：outerMeasure_inter
ior_compacts (K : Compacts G) : μ.outerMeasure (interior K) <= μ K
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `IsCompact.closure`：∀ {X : Type u_1} [inst : TopologicalSpace X] [R1Space
 X] {K : Set X}, IsCompact K → IsCompact (closure K)
· 使用定理 `TopologicalSpace.Compacts.isCompact'`：∀ {α : Type u_4} [inst : Topologic
alSpace α] (self : TopologicalSpace.Compacts α), IsCompact self.carrier
· 使用定理 `MeasureTheory.Content.mono`：mono (K₁ K₂ : Compacts G) (h : (K₁ : Set G) 
subseteq K₂) : μ K₁ <= μ K₂
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `IsClosed.measurableSet`：IsClosed.measurableSet (h : IsClosed s) : Measur
ableSet s
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
· 使用定理 `MeasureTheory.Content.le_outerMeasure_compacts`：le_outerMeasure_compacts
 (K : Compacts G) : μ K <= μ.outerMeasure K
· 使用定理 `IsCompact.measure_closure`：IsCompact.measure_closure [R1Space γ] {K : Se
t γ} (hK : IsCompact K) (μ : Measure γ) : μ (closure K) = μ K

--- 原说明 ---
If `μ` is a regular content, then the measure induced by `μ` will agree with `μ`
  on compact sets.
-/
theorem measure_eq_content_of_regular (H : MeasureTheory.Content.ContentRegular μ)
    (K : TopologicalSpace.Compacts G) : μ.measure ↑K = μ K := by
  refine le_antisymm ?_ ?_
  · apply ENNReal.le_of_forall_pos_le_add
    intro ε εpos _
    obtain ⟨K', K'_hyp⟩ := contentRegular_exists_compact μ H K (ne_bot_of_gt εpos)
    calc
      μ.measure ↑K ≤ μ.measure (interior ↑K') := measure_mono K'_hyp.1
      _ ≤ μ K' := by
        rw [μ.measure_apply (IsOpen.measurableSet isOpen_interior)]
        exact μ.outerMeasure_interior_compacts K'
      _ ≤ μ K + ε := K'_hyp.right
  · calc
    μ K ≤ μ ⟨closure K, K.2.closure⟩ := μ.mono _ _ subset_closure
    _ ≤ μ.measure (closure K) := by
      rw [μ.measure_apply (isClosed_closure.measurableSet)]
      exact μ.le_outerMeasure_compacts _
    _ = μ.measure K := K.2.measure_closure _

end RegularContents

end Content

end MeasureTheory

