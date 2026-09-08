/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.BigOperators.Option
public import Mathlib.Analysis.BoxIntegral.Box.Basic
public import Mathlib.Data.Set.Pairwise.Lattice

/-!
# Partitions of rectangular boxes in `ℝⁿ`

In this file we define (pre)partitions of rectangular boxes in `ℝⁿ`. A partition of a box `I` in
`ℝⁿ` (see `BoxIntegral.Prepartition` and `BoxIntegral.Prepartition.IsPartition`) is a finite set
of pairwise disjoint boxes such that their union is exactly `I`. We use `boxes : Finset (Box ι)` to
store the set of boxes.

Many lemmas about box integrals deal with pairwise disjoint collections of subboxes, so we define a
structure `BoxIntegral.Prepartition (I : BoxIntegral.Box ι)` that stores a collection of boxes
such that

* each box `J ∈ boxes` is a subbox of `I`;
* the boxes are pairwise disjoint as sets in `ℝⁿ`.

Then we define a predicate `BoxIntegral.Prepartition.IsPartition`; `π.IsPartition` means that the
boxes of `π` actually cover the whole `I`. We also define some operations on prepartitions:

* `BoxIntegral.Prepartition.biUnion`: split each box of a partition into smaller boxes;
* `BoxIntegral.Prepartition.restrict`: restrict a partition to a smaller box.

We also define a `SemilatticeInf` structure on `BoxIntegral.Prepartition I` for all
`I : BoxIntegral.Box ι`.

## Tags

rectangular box, partition
-/

@[expose] public section

open Set Finset Function
open scoped NNReal

noncomputable section

namespace BoxIntegral

variable {ι : Type*}

/-- A prepartition of `I : BoxIntegral.Box ι` is a finite set of pairwise disjoint subboxes of
`I`. -/
/-
**BoxIntegral.Prepartition** 是 Mathlib 中的一个归纳类型，位于命名空间 `BoxIntegral`。
形式化陈述：{ι : Type u_1} → BoxIntegral.Box ι → Type u_1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A prepartition of `I : BoxIntegral.Box ι` is a finite set of pairwise disjoint s
ubboxes of
`I`.
-/
structure Prepartition (I : Box ι) where
  /-- The underlying set of boxes -/
  boxes : Finset (Box ι)
  /-- Each box is a sub-box of `I` -/
  le_of_mem' : ∀ J ∈ boxes, J ≤ I
  /-- The boxes in a prepartition are pairwise disjoint. -/
  pairwiseDisjoint : Set.Pairwise (↑boxes) (Disjoint on ((↑) : Box ι → Set (ι → ℝ)))

namespace Prepartition

variable {I J J₁ J₂ : Box ι} (π : Prepartition I) {π₁ π₂ : Prepartition I} {x : ι → ℝ}

/-
**BoxIntegral.Prepartition.** 是 Mathlib 中的一个实例，位于命名空间 `BoxIntegral.Prepartition`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Membership (Box ι) (Prepartition I) :=
  ⟨fun π J => J ∈ π.boxes⟩

@[simp]
/-
**BoxIntegral.Prepartition.mem_boxes** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.Prep
artition`。
形式化陈述：mem_boxes : J in π.boxes ↔ J in π
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_boxes : J ∈ π.boxes ↔ J ∈ π := Iff.rfl

@[simp]
/-
**BoxIntegral.Prepartition.mem_mk** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.Prepart
ition`。
形式化陈述：mem_mk {s h₁ h₂} : J in (mk s h₁ h₂ : Prepartition I) ↔ J in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_mk {s h₁ h₂} : J ∈ (mk s h₁ h₂ : Prepartition I) ↔ J ∈ s := Iff.rfl
/-
**BoxIntegral.Prepartition.disjoint_coe_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `BoxInt
egral.Prepartition`。
形式化陈述：disjoint_coe_of_mem (h₁ : J₁ in π) (h₂ : J₂ in π) (h : J₁ != J₂) : Disjoin
t (J₁ : Set (ι -> Real)) J₂
参数：h₁ : J₁ in π；h₂ : J₂ in π；h : J₁ != J₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BoxIntegral.Prepartition.pairwiseDisjoint`：∀ {ι : Type u_1} {I : BoxInte
gral.Box ι} (self : BoxIntegral.Prepartition I),   (↑self.boxes).Pairwise (Funct
ion.onFun Disjoint BoxIntegral.…
-/
theorem disjoint_coe_of_mem (h₁ : J₁ ∈ π) (h₂ : J₂ ∈ π) (h : J₁ ≠ J₂) :
    Disjoint (J₁ : Set (ι → ℝ)) J₂ :=
  π.pairwiseDisjoint h₁ h₂ h
/-
**BoxIntegral.Prepartition.eq_of_mem_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegr
al.Prepartition`。
形式化陈述：eq_of_mem_of_mem (h₁ : J₁ in π) (h₂ : J₂ in π) (hx₁ : x in J₁) (hx₂ : x in
 J₂) : J₁ = J₂
参数：h₁ : J₁ in π；h₂ : J₂ in π；hx₁ : x in J₁；hx₂ : x in J₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `by_contra`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Disjoint.le_bot`：Disjoint.le_bot : Disjoint a b -> a ⊓ b <= ⊥
· 使用定理 `BoxIntegral.Prepartition.disjoint_coe_of_mem`：disjoint_coe_of_mem (h₁ : 
J₁ in π) (h₂ : J₂ in π) (h : J₁ != J₂) : Disjoint (J₁ : Set (ι -> Real)) J₂
-/
theorem eq_of_mem_of_mem (h₁ : J₁ ∈ π) (h₂ : J₂ ∈ π) (hx₁ : x ∈ J₁) (hx₂ : x ∈ J₂) : J₁ = J₂ :=
  by_contra fun H => (π.disjoint_coe_of_mem h₁ h₂ H).le_bot ⟨hx₁, hx₂⟩
/-
**BoxIntegral.Prepartition.eq_of_le_of_le** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral
.Prepartition`。
形式化陈述：eq_of_le_of_le (h₁ : J₁ in π) (h₂ : J₂ in π) (hle₁ : J <= J₁) (hle₂ : J <=
 J₂) : J₁ = J₂
参数：h₁ : J₁ in π；h₂ : J₂ in π；hle₁ : J <= J₁；hle₂ : J <= J₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BoxIntegral.Prepartition.eq_of_mem_of_mem`：eq_of_mem_of_mem (h₁ : J₁ in 
π) (h₂ : J₂ in π) (hx₁ : x in J₁) (hx₂ : x in J₂) : J₁ = J₂
· 使用定理 `BoxIntegral.Box.upper_mem`：upper_mem : I.upper in I
-/
theorem eq_of_le_of_le (h₁ : J₁ ∈ π) (h₂ : J₂ ∈ π) (hle₁ : J ≤ J₁) (hle₂ : J ≤ J₂) : J₁ = J₂ :=
  π.eq_of_mem_of_mem h₁ h₂ (hle₁ J.upper_mem) (hle₂ J.upper_mem)
/-
**BoxIntegral.Prepartition.eq_of_le** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.Prepa
rtition`。
形式化陈述：eq_of_le (h₁ : J₁ in π) (h₂ : J₂ in π) (hle : J₁ <= J₂) : J₁ = J₂
参数：h₁ : J₁ in π；h₂ : J₂ in π；hle : J₁ <= J₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BoxIntegral.Prepartition.eq_of_le_of_le`：eq_of_le_of_le (h₁ : J₁ in π) (
h₂ : J₂ in π) (hle₁ : J <= J₁) (hle₂ : J <= J₂) : J₁ = J₂
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem eq_of_le (h₁ : J₁ ∈ π) (h₂ : J₂ ∈ π) (hle : J₁ ≤ J₂) : J₁ = J₂ :=
  π.eq_of_le_of_le h₁ h₂ le_rfl hle
/-
**BoxIntegral.Prepartition.le_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.Prep
artition`。
形式化陈述：le_of_mem (hJ : J in π) : J <= I
参数：hJ : J in π。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BoxIntegral.Prepartition.le_of_mem'`：∀ {ι : Type u_1} {I : BoxIntegral.B
ox ι} (self : BoxIntegral.Prepartition I), ∀ J ∈ self.boxes, J ≤ I
-/
theorem le_of_mem (hJ : J ∈ π) : J ≤ I :=
  π.le_of_mem' J hJ
/-
**BoxIntegral.Prepartition.lower_le_lower** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral
.Prepartition`。
形式化陈述：lower_le_lower (hJ : J in π) : I.lower <= J.lower
参数：hJ : J in π。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BoxIntegral.Box.antitone_lower`：antitone_lower : Antitone fun I : Box ι 
=> I.lower
· 使用定理 `BoxIntegral.Prepartition.le_of_mem`：le_of_mem (hJ : J in π) : J <= I
-/
theorem lower_le_lower (hJ : J ∈ π) : I.lower ≤ J.lower :=
  Box.antitone_lower (π.le_of_mem hJ)
/-
**BoxIntegral.Prepartition.upper_le_upper** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral
.Prepartition`。
形式化陈述：upper_le_upper (hJ : J in π) : J.upper <= I.upper
参数：hJ : J in π。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BoxIntegral.Box.monotone_upper`：monotone_upper : Monotone fun I : Box ι 
=> I.upper
· 使用定理 `BoxIntegral.Prepartition.le_of_mem`：le_of_mem (hJ : J in π) : J <= I
-/
theorem upper_le_upper (hJ : J ∈ π) : J.upper ≤ I.upper :=
  Box.monotone_upper (π.le_of_mem hJ)
/-
**BoxIntegral.Prepartition.injective_boxes** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegra
l.Prepartition`。
形式化陈述：injective_boxes : Function.Injective (boxes : Prepartition I -> Finset (Bo
x ι))
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem injective_boxes : Function.Injective (boxes : Prepartition I → Finset (Box ι)) := by
  rintro ⟨s₁, h₁, h₁'⟩ ⟨s₂, h₂, h₂'⟩ (rfl : s₁ = s₂)
  rfl

@[ext]
/-
**BoxIntegral.Prepartition.ext** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.Prepartiti
on`。
形式化陈述：ext (h : forall J, J in π₁ ↔ J in π₂) : π₁ = π₂
参数：h : forall J, J in π₁ ↔ J in π₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BoxIntegral.Prepartition.injective_boxes`：injective_boxes : Function.Inj
ective (boxes : Prepartition I -> Finset (Box ι))
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
-/
theorem ext (h : ∀ J, J ∈ π₁ ↔ J ∈ π₂) : π₁ = π₂ :=
  injective_boxes <| Finset.ext h

/-- The singleton prepartition `{J}`, `J ≤ I`. -/
@[simps]
/-
**BoxIntegral.Prepartition.single** 是 Mathlib 中的一个定义，位于命名空间 `BoxIntegral.Prepart
ition`。
形式化陈述：single (I J : Box ι) (h : J <= I) : Prepartition I
参数：I J : Box ι；h : J <= I。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The singleton prepartition `{J}`, `J ≤ I`.
-/
def single (I J : Box ι) (h : J ≤ I) : Prepartition I :=
  ⟨{J}, by simpa, by simp⟩

@[simp]
/-
**BoxIntegral.Prepartition.mem_single** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.Pre
partition`。
形式化陈述：mem_single {J'} (h : J <= I) : J' in single I J h ↔ J' = J
参数：h : J <= I。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.mem_singleton`：mem_singleton {a b : α} : b in ({a} : Finset α) ↔ 
b = a
-/
theorem mem_single {J'} (h : J ≤ I) : J' ∈ single I J h ↔ J' = J :=
  mem_singleton

/-- We say that `π ≤ π'` if each box of `π` is a subbox of some box of `π'`. -/
/-
**BoxIntegral.Prepartition.** 是 Mathlib 中的一个实例，位于命名空间 `BoxIntegral.Prepartition`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say that `π ≤ π'` if each box of `π` is a subbox of some box of `π'`.
-/
instance : LE (Prepartition I) :=
  ⟨fun π π' => ∀ ⦃I⦄, I ∈ π → ∃ I' ∈ π', I ≤ I'⟩
/-
**BoxIntegral.Prepartition.partialOrder** 是 Mathlib 中的一个实例，位于命名空间 `BoxIntegral.P
repartition`。
形式化陈述：partialOrder : PartialOrder (Prepartition I) where le_refl _ I hI
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance partialOrder : PartialOrder (Prepartition I) where
  le_refl _ I hI := ⟨I, hI, le_rfl⟩
  le_trans _ _ _ h₁₂ h₂₃ _ hI₁ :=
    let ⟨_, hI₂, hI₁₂⟩ := h₁₂ hI₁
    let ⟨I₃, hI₃, hI₂₃⟩ := h₂₃ hI₂
    ⟨I₃, hI₃, hI₁₂.trans hI₂₃⟩
  le_antisymm := by
    suffices ∀ {π₁ π₂ : Prepartition I}, π₁ ≤ π₂ → π₂ ≤ π₁ → π₁.boxes ⊆ π₂.boxes from
      fun π₁ π₂ h₁ h₂ => injective_boxes (Subset.antisymm (this h₁ h₂) (this h₂ h₁))
    intro π₁ π₂ h₁ h₂ J hJ
    rcases h₁ hJ with ⟨J', hJ', hle⟩; rcases h₂ hJ' with ⟨J'', hJ'', hle'⟩
    obtain rfl : J = J'' := π₁.eq_of_le hJ hJ'' (hle.trans hle')
    obtain rfl : J' = J := le_antisymm ‹_› ‹_›
    assumption
/-
**BoxIntegral.Prepartition.** 是 Mathlib 中的一个实例，位于命名空间 `BoxIntegral.Prepartition`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : OrderTop (Prepartition I) where
  top := single I I le_rfl
  le_top π _ hJ := ⟨I, by simp, π.le_of_mem hJ⟩
/-
**BoxIntegral.Prepartition.** 是 Mathlib 中的一个实例，位于命名空间 `BoxIntegral.Prepartition`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : OrderBot (Prepartition I) where
  bot := ⟨∅,
    fun _ hJ => (Finset.notMem_empty _ hJ).elim,
    fun _ hJ => (Set.notMem_empty _ <| Finset.coe_empty ▸ hJ).elim⟩
  bot_le _ _ hJ := (Finset.notMem_empty _ hJ).elim
/-
**BoxIntegral.Prepartition.** 是 Mathlib 中的一个实例，位于命名空间 `BoxIntegral.Prepartition`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (Prepartition I) := ⟨⊤⟩
/-
**BoxIntegral.Prepartition.le_def** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.Prepart
ition`。
形式化陈述：le_def : π₁ <= π₂ ↔ forall J in π₁, exists J' in π₂, J <= J'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem le_def : π₁ ≤ π₂ ↔ ∀ J ∈ π₁, ∃ J' ∈ π₂, J ≤ J' := Iff.rfl

@[simp]
/-
**BoxIntegral.Prepartition.mem_top** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.Prepar
tition`。
形式化陈述：mem_top : J in (⊤ : Prepartition I) ↔ J = I
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.mem_singleton`：mem_singleton {a b : α} : b in ({a} : Finset α) ↔ 
b = a
-/
theorem mem_top : J ∈ (⊤ : Prepartition I) ↔ J = I :=
  mem_singleton

@[simp]
/-
**BoxIntegral.Prepartition.top_boxes** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.Prep
artition`。
形式化陈述：top_boxes : (⊤ : Prepartition I).boxes = {I}
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem top_boxes : (⊤ : Prepartition I).boxes = {I} := rfl

@[simp]
/-
**BoxIntegral.Prepartition.notMem_bot** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.Pre
partition`。
形式化陈述：notMem_bot : J ∉ (⊥ : Prepartition I)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.notMem_empty`：notMem_empty (a : α) : a ∉ (∅ : Finset α)
-/
theorem notMem_bot : J ∉ (⊥ : Prepartition I) :=
  Finset.notMem_empty _

@[simp]
/-
**BoxIntegral.Prepartition.bot_boxes** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.Prep
artition`。
形式化陈述：bot_boxes : (⊥ : Prepartition I).boxes = ∅
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bot_boxes : (⊥ : Prepartition I).boxes = ∅ := rfl

/-- An auxiliary lemma used to prove that the same point can't belong to more than
`2 ^ Fintype.card ι` closed boxes of a prepartition. -/
/-
**BoxIntegral.Prepartition.injOn_setOfPred_mem_Icc_setOfPred_lower_eq** 是 Mathli
b 中的一个定理，位于命名空间 `BoxIntegral.Prepartition`。
形式化陈述：injOn_setOfPred_mem_Icc_setOfPred_lower_eq (x : ι -> Real) : InjOn (fun J 
: Box ι => { i | J.lower i = x i }) { J | J in π ∧ x in Box.Icc J }
参数：x : ι -> Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `BoxIntegral.Box.lower_lt_upper`：∀ {ι : Type u_2} (self : BoxIntegral.Box
 ι) (i : ι), self.lower i < self.upper i
· 使用定理 `Set.Ioc_inter_Ioc`：∀ {α : Type u_1} [inst : LinearOrder α] {a₁ a₂ b₁ b₂ 
: α},   Set.Ioc b₁ a₁ ∩ Set.Ioc b₂ a₂ = Set.Ioc (max b₁ b₂) (min a₁ a₂)
· 使用定理 `sup_idem`：sup_idem (a : α) : a ⊔ a = a
· 使用定理 `Set.nonempty_Ioc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, (Set.I
oc b a).Nonempty ↔ b < a
· 使用引理 `lt_min`：lt_min (h₁ : a < b) (h₂ : a < c) : a < min b c
· 使用定理 `LE.le.lt_of_ne`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a ≠ b → a < b
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `BoxIntegral.Prepartition.eq_of_mem_of_mem`：eq_of_mem_of_mem (h₁ : J₁ in 
π) (h₂ : J₂ in π) (hx₁ : x in J₁) (hx₂ : x in J₂) : J₁ = J₂
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)

--- 原说明 ---
An auxiliary lemma used to prove that the same point can't belong to more than
`2 ^ Fintype.card ι` closed boxes of a prepartition.
-/
theorem injOn_setOfPred_mem_Icc_setOfPred_lower_eq (x : ι → ℝ) :
    InjOn (fun J : Box ι => { i | J.lower i = x i }) { J | J ∈ π ∧ x ∈ Box.Icc J } := by
  rintro J₁ ⟨h₁, hx₁⟩ J₂ ⟨h₂, hx₂⟩ (H : { i | J₁.lower i = x i } = { i | J₂.lower i = x i })
  suffices ∀ i, (Ioc (J₁.lower i) (J₁.upper i) ∩ Ioc (J₂.lower i) (J₂.upper i)).Nonempty by
    choose y hy₁ hy₂ using this
    exact π.eq_of_mem_of_mem h₁ h₂ hy₁ hy₂
  intro i
  simp only [Set.ext_iff, mem_ofPred] at H
  rcases (hx₁.1 i).eq_or_lt with hi₁ | hi₁
  · have hi₂ : J₂.lower i = x i := (H _).1 hi₁
    have H₁ : x i < J₁.upper i := by simpa only [hi₁] using J₁.lower_lt_upper i
    have H₂ : x i < J₂.upper i := by simpa only [hi₂] using J₂.lower_lt_upper i
    rw [Set.Ioc_inter_Ioc, hi₁, hi₂, sup_idem, Set.nonempty_Ioc]
    exact lt_min H₁ H₂
  · have hi₂ : J₂.lower i < x i := (hx₂.1 i).lt_of_ne (mt (H _).2 hi₁.ne)
    exact ⟨x i, ⟨hi₁, hx₁.2 i⟩, ⟨hi₂, hx₂.2 i⟩⟩

@[deprecated (since := "2026-07-09")]
alias injOn_setOf_mem_Icc_setOf_lower_eq := injOn_setOfPred_mem_Icc_setOfPred_lower_eq

open scoped Classical in
/-- The set of boxes of a prepartition that contain `x` in their closures has cardinality
at most `2 ^ Fintype.card ι`. -/
/-
**BoxIntegral.Prepartition.card_filter_mem_Icc_le** 是 Mathlib 中的一个定理，位于命名空间 `Box
Integral.Prepartition`。
形式化陈述：card_filter_mem_Icc_le [Fintype ι] (x : ι -> Real) : #{J in π.boxes | x in
 Box.Icc J} <= 2 ^ Fintype.card ι
参数：x : ι -> Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fintype.card_set`：Fintype.card_set [Fintype α] : Fintype.card (Set α) = 
2 ^ Fintype.card α
· 使用引理 `Finset.card_le_card_of_injOn`：card_le_card_of_injOn (f : α -> β) (hf : S
et.MapsTo f s t) (f_inj : (s : Set α).InjOn f) : #s <= #t
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.coe_filter`：∀ {α : Type u_1} (p : α → Prop) [inst : DecidablePred
 p] (s : Finset α), ↑(Finset.filter p s) = {x | x ∈ s ∧ p x}
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `BoxIntegral.Prepartition.injOn_setOfPred_mem_Icc_setOfPred_lower_eq`：inj
On_setOfPred_mem_Icc_setOfPred_lower_eq (x : ι -> Real) : InjOn (fun J : Box ι =
> { i | J.lower i = x i }) { J | J in π ∧ x in Box.Icc J …

--- 原说明 ---
The set of boxes of a prepartition that contain `x` in their closures has cardin
ality
at most `2 ^ Fintype.card ι`.
-/
theorem card_filter_mem_Icc_le [Fintype ι] (x : ι → ℝ) :
    #{J ∈ π.boxes | x ∈ Box.Icc J} ≤ 2 ^ Fintype.card ι := by
  rw [← Fintype.card_set]
  refine Finset.card_le_card_of_injOn (fun J : Box ι => { i | J.lower i = x i })
    (fun _ _ => Finset.mem_univ _) ?_
  simpa using π.injOn_setOfPred_mem_Icc_setOfPred_lower_eq x

/-- Given a prepartition `π : BoxIntegral.Prepartition I`, `π.iUnion` is the part of `I` covered by
the boxes of `π`. -/
/-
**BoxIntegral.Prepartition.iUnion** 是 Mathlib 中的一个定义，位于命名空间 `BoxIntegral.Prepart
ition`。
形式化陈述：{ι : Type u_1} → {I : BoxIntegral.Box ι} → BoxIntegral.Prepartition I → Se
t (ι → ℝ)
参数：ι → ℝ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a prepartition `π : BoxIntegral.Prepartition I`, `π.iUnion` is the part of
 `I` covered by
the boxes of `π`.
-/
protected def iUnion : Set (ι → ℝ) :=
  ⋃ J ∈ π, ↑J
/-
**BoxIntegral.Prepartition.iUnion_def** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.Pre
partition`。
形式化陈述：iUnion_def : π.iUnion = ⋃ J in π, ↑J
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem iUnion_def : π.iUnion = ⋃ J ∈ π, ↑J := rfl
/-
**BoxIntegral.Prepartition.iUnion_def'** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.Pr
epartition`。
形式化陈述：iUnion_def' : π.iUnion = ⋃ J in π.boxes, ↑J
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem iUnion_def' : π.iUnion = ⋃ J ∈ π.boxes, ↑J := rfl

@[simp]
/-
**BoxIntegral.Prepartition.mem_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.Pre
partition`。
形式化陈述：mem_iUnion : x in π.iUnion ↔ exists J in π, x in J
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `BoxIntegral.Box.mem_coe`：mem_coe : x in (I : Set (ι -> Real)) ↔ x in I
· 使用定理 `exists_prop`：∀ {b a : Prop}, (∃ (_ : a), b) ↔ a ∧ b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Set.mem_iUnion₂`：mem_iUnion₂ {x : γ} {s : forall i, κ i -> Set γ} : (x i
n ⋃ (i) (j), s i j) ↔ exists i j, x in s i j
-/
theorem mem_iUnion : x ∈ π.iUnion ↔ ∃ J ∈ π, x ∈ J := by
  convert! Set.mem_iUnion₂
  rw [Box.mem_coe, exists_prop]

@[simp]
/-
**BoxIntegral.Prepartition.iUnion_single** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.
Prepartition`。
形式化陈述：iUnion_single (h : J <= I) : (single I J h).iUnion = J
参数：h : J <= I。
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
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iUnion_iUnion_eq_left`：iUnion_iUnion_eq_left {b : β} {s : forall x :
 β, x = b -> Set α} : ⋃ (x) (h : x = b), s x h = s b rfl
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iUnion_single (h : J ≤ I) : (single I J h).iUnion = J := by simp [iUnion_def]

@[simp]
/-
**BoxIntegral.Prepartition.iUnion_top** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.Pre
partition`。
形式化陈述：iUnion_top : (⊤ : Prepartition I).iUnion = I
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
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iUnion_iUnion_eq_left`：iUnion_iUnion_eq_left {b : β} {s : forall x :
 β, x = b -> Set α} : ⋃ (x) (h : x = b), s x h = s b rfl
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iUnion_top : (⊤ : Prepartition I).iUnion = I := by simp [Prepartition.iUnion]

@[simp]
/-
**BoxIntegral.Prepartition.iUnion_eq_empty** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegra
l.Prepartition`。
形式化陈述：iUnion_eq_empty : π₁.iUnion = ∅ ↔ π₁ = ⊥
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
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `BoxIntegral.Prepartition.injective_boxes`：injective_boxes : Function.Inj
ective (boxes : Prepartition I -> Finset (Box ι))
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem iUnion_eq_empty : π₁.iUnion = ∅ ↔ π₁ = ⊥ := by
  simp [← injective_boxes.eq_iff, Finset.ext_iff, Prepartition.iUnion, imp_false]

@[simp]
/-
**BoxIntegral.Prepartition.iUnion_bot** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.Pre
partition`。
形式化陈述：iUnion_bot : (⊥ : Prepartition I).iUnion = ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `BoxIntegral.Prepartition.iUnion_eq_empty`：iUnion_eq_empty : π₁.iUnion = 
∅ ↔ π₁ = ⊥
-/
theorem iUnion_bot : (⊥ : Prepartition I).iUnion = ∅ :=
  iUnion_eq_empty.2 rfl
/-
**BoxIntegral.Prepartition.subset_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.
Prepartition`。
形式化陈述：subset_iUnion (h : J in π) : ↑J subseteq π.iUnion
参数：h : J in π。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.subset_biUnion_of_mem`：subset_biUnion_of_mem {s : Set α} {u : α -> S
et β} {x : α} (xs : x in s) : u x subseteq ⋃ x in s, u x
-/
theorem subset_iUnion (h : J ∈ π) : ↑J ⊆ π.iUnion :=
  subset_biUnion_of_mem h
/-
**BoxIntegral.Prepartition.iUnion_subset** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.
Prepartition`。
形式化陈述：iUnion_subset : π.iUnion subseteq I
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.iUnion₂_subset`：iUnion₂_subset {s : forall i, κ i -> Set α} {t : Set
 α} (h : forall i j, s i j subseteq t) : ⋃ (i) (j), s i j subseteq t
· 使用定理 `BoxIntegral.Prepartition.le_of_mem'`：∀ {ι : Type u_1} {I : BoxIntegral.B
ox ι} (self : BoxIntegral.Prepartition I), ∀ J ∈ self.boxes, J ≤ I
-/
theorem iUnion_subset : π.iUnion ⊆ I :=
  iUnion₂_subset π.le_of_mem'

@[gcongr, mono]
/-
**BoxIntegral.Prepartition.iUnion_mono** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.Pr
epartition`。
形式化陈述：iUnion_mono (h : π₁ <= π₂) : π₁.iUnion subseteq π₂.iUnion
参数：h : π₁ <= π₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `BoxIntegral.Prepartition.mem_iUnion`：mem_iUnion : x in π.iUnion ↔ exists
 J in π, x in J
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem iUnion_mono (h : π₁ ≤ π₂) : π₁.iUnion ⊆ π₂.iUnion := fun _ hx =>
  let ⟨_, hJ₁, hx⟩ := π₁.mem_iUnion.1 hx
  let ⟨J₂, hJ₂, hle⟩ := h hJ₁
  π₂.mem_iUnion.2 ⟨J₂, hJ₂, hle hx⟩
/-
**BoxIntegral.Prepartition.disjoint_boxes_of_disjoint_iUnion** 是 Mathlib 中的一个定理，
位于命名空间 `BoxIntegral.Prepartition`。
形式化陈述：disjoint_boxes_of_disjoint_iUnion (h : Disjoint π₁.iUnion π₂.iUnion) : Dis
joint π₁.boxes π₂.boxes
参数：h : Disjoint π₁.iUnion π₂.iUnion。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s 
-> a ∉ t
· 使用定理 `Disjoint.le_bot`：Disjoint.le_bot : Disjoint a b -> a ⊓ b <= ⊥
· 使用定理 `Disjoint.mono`：Disjoint.mono {x y : Perm α} (h : Disjoint f g) (hf : x.s
upport <= f.support) (hg : y.support <= g.support) : Disjoint x y
· 使用定理 `BoxIntegral.Prepartition.subset_iUnion`：subset_iUnion (h : J in π) : ↑J 
subseteq π.iUnion
· 使用定理 `BoxIntegral.Box.upper_mem`：upper_mem : I.upper in I
-/
theorem disjoint_boxes_of_disjoint_iUnion (h : Disjoint π₁.iUnion π₂.iUnion) :
    Disjoint π₁.boxes π₂.boxes :=
  Finset.disjoint_left.2 fun J h₁ h₂ =>
    Disjoint.le_bot (h.mono (π₁.subset_iUnion h₁) (π₂.subset_iUnion h₂)) ⟨J.upper_mem, J.upper_mem⟩
/-
**BoxIntegral.Prepartition.le_iff_nonempty_imp_le_and_iUnion_subset** 是 Mathlib 
中的一个定理，位于命名空间 `BoxIntegral.Prepartition`。
形式化陈述：le_iff_nonempty_imp_le_and_iUnion_subset : π₁ <= π₂ ↔ (forall J in π₁, for
all J' in π₂, (J inter J' : Set (ι -> Real)).Nonempty -> J <= J') ∧ π₁.iUnion su
bseteq π₂.iUnion
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `BoxIntegral.Prepartition.eq_of_mem_of_mem`：eq_of_mem_of_mem (h₁ : J₁ in 
π) (h₂ : J₂ in π) (hx₁ : x in J₁) (hx₂ : x in J₂) : J₁ = J₂
· 使用定理 `BoxIntegral.Prepartition.iUnion_mono`：iUnion_mono (h : π₁ <= π₂) : π₁.iU
nion subseteq π₂.iUnion
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `BoxIntegral.Box.upper_mem`：upper_mem : I.upper in I
-/
theorem le_iff_nonempty_imp_le_and_iUnion_subset :
    π₁ ≤ π₂ ↔
      (∀ J ∈ π₁, ∀ J' ∈ π₂, (J ∩ J' : Set (ι → ℝ)).Nonempty → J ≤ J') ∧ π₁.iUnion ⊆ π₂.iUnion := by
  constructor
  · refine fun H => ⟨fun J hJ J' hJ' Hne => ?_, iUnion_mono H⟩
    rcases H hJ with ⟨J'', hJ'', Hle⟩
    rcases Hne with ⟨x, hx, hx'⟩
    rwa [π₂.eq_of_mem_of_mem hJ' hJ'' hx' (Hle hx)]
  · rintro ⟨H, HU⟩ J hJ
    simp only [Set.subset_def, mem_iUnion] at HU
    rcases HU J.upper ⟨J, hJ, J.upper_mem⟩ with ⟨J₂, hJ₂, hx⟩
    exact ⟨J₂, hJ₂, H _ hJ _ hJ₂ ⟨_, J.upper_mem, hx⟩⟩
/-
**BoxIntegral.Prepartition.eq_of_boxes_subset_iUnion_superset** 是 Mathlib 中的一个定理
，位于命名空间 `BoxIntegral.Prepartition`。
形式化陈述：eq_of_boxes_subset_iUnion_superset (h₁ : π₁.boxes subseteq π₂.boxes) (h₂ :
 π₂.iUnion subseteq π₁.iUnion) : π₁ = π₂
参数：h₁ : π₁.boxes subseteq π₂.boxes；h₂ : π₂.iUnion subseteq π₁.iUnion。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `BoxIntegral.Prepartition.le_iff_nonempty_imp_le_and_iUnion_subset`：le_if
f_nonempty_imp_le_and_iUnion_subset : π₁ <= π₂ ↔ (forall J in π₁, forall J' in π
₂, (J inter J' : Set (ι -> Real)).Nonempty -> J <= J') …
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `BoxIntegral.Prepartition.eq_of_mem_of_mem`：eq_of_mem_of_mem (h₁ : J₁ in 
π) (h₂ : J₂ in π) (hx₁ : x in J₁) (hx₂ : x in J₂) : J₁ = J₂
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem eq_of_boxes_subset_iUnion_superset (h₁ : π₁.boxes ⊆ π₂.boxes) (h₂ : π₂.iUnion ⊆ π₁.iUnion) :
    π₁ = π₂ :=
  le_antisymm (fun J hJ => ⟨J, h₁ hJ, le_rfl⟩) <|
    le_iff_nonempty_imp_le_and_iUnion_subset.2
      ⟨fun _ hJ₁ _ hJ₂ Hne =>
        (π₂.eq_of_mem_of_mem hJ₁ (h₁ hJ₂) Hne.choose_spec.1 Hne.choose_spec.2).le, h₂⟩

open scoped Classical in
/-- Given a prepartition `π` of a box `I` and a collection of prepartitions `πi J` of all boxes
`J ∈ π`, returns the prepartition of `I` into the union of the boxes of all `πi J`.

Though we only use the values of `πi` on the boxes of `π`, we require `πi` to be a globally defined
function. -/
@[simps]
/-
**BoxIntegral.Prepartition.biUnion** 是 Mathlib 中的一个定义，位于命名空间 `BoxIntegral.Prepar
tition`。
形式化陈述：biUnion (πi : forall J : Box ι, Prepartition J) : Prepartition I where box
es
参数：πi : forall J : Box ι, Prepartition J。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a prepartition `π` of a box `I` and a collection of prepartitions `πi J` o
f all boxes
`J ∈ π`, returns the prepartition of `I` into the union of the boxes of all `πi 
J`.

Though we only use the values of `πi` on the boxes of `π`, we require `πi` to be
 a globally defined
function.
-/
def biUnion (πi : ∀ J : Box ι, Prepartition J) : Prepartition I where
  boxes := π.boxes.biUnion fun J => (πi J).boxes
  le_of_mem' J hJ := by
    simp only [Finset.mem_biUnion, mem_boxes] at hJ
    rcases hJ with ⟨J', hJ', hJ⟩
    exact ((πi J').le_of_mem hJ).trans (π.le_of_mem hJ')
  pairwiseDisjoint := by
    simp only [Set.Pairwise, Finset.mem_coe, Finset.mem_biUnion]
    rintro J₁' ⟨J₁, hJ₁, hJ₁'⟩ J₂' ⟨J₂, hJ₂, hJ₂'⟩ Hne
    rw [Function.onFun, Set.disjoint_left]
    rintro x hx₁ hx₂; apply Hne
    obtain rfl : J₁ = J₂ :=
      π.eq_of_mem_of_mem hJ₁ hJ₂ ((πi J₁).le_of_mem hJ₁' hx₁) ((πi J₂).le_of_mem hJ₂' hx₂)
    exact (πi J₁).eq_of_mem_of_mem hJ₁' hJ₂' hx₁ hx₂

variable {πi πi₁ πi₂ : ∀ J : Box ι, Prepartition J}

@[simp]
/-
**BoxIntegral.Prepartition.mem_biUnion** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.Pr
epartition`。
形式化陈述：mem_biUnion : J in π.biUnion πi ↔ exists J' in π, J in πi J'
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
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_biUnion : J ∈ π.biUnion πi ↔ ∃ J' ∈ π, J ∈ πi J' := by simp [biUnion]
/-
**BoxIntegral.Prepartition.biUnion_le** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.Pre
partition`。
形式化陈述：biUnion_le (πi : forall J, Prepartition J) : π.biUnion πi <= π
参数：πi : forall J, Prepartition J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `BoxIntegral.Prepartition.mem_biUnion`：mem_biUnion : J in π.biUnion πi ↔ 
exists J' in π, J in πi J'
· 使用定理 `BoxIntegral.Prepartition.le_of_mem`：le_of_mem (hJ : J in π) : J <= I
-/
theorem biUnion_le (πi : ∀ J, Prepartition J) : π.biUnion πi ≤ π := fun _ hJ =>
  let ⟨J', hJ', hJ⟩ := π.mem_biUnion.1 hJ
  ⟨J', hJ', (πi J').le_of_mem hJ⟩

@[simp]
/-
**BoxIntegral.Prepartition.biUnion_top** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.Pr
epartition`。
形式化陈述：biUnion_top : (π.biUnion fun _ => ⊤) = π
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BoxIntegral.Prepartition.ext`：ext (h : forall J, J in π₁ ↔ J in π₂) : π₁
 = π₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem biUnion_top : (π.biUnion fun _ => ⊤) = π := by
  ext
  simp

@[congr]
/-
**BoxIntegral.Prepartition.biUnion_congr** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.
Prepartition`。
形式化陈述：biUnion_congr (h : π₁ = π₂) (hi : forall J in π₁, πi₁ J = πi₂ J) : π₁.biUn
ion πi₁ = π₂.biUnion πi₂
参数：h : π₁ = π₂；hi : forall J in π₁, πi₁ J = πi₂ J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BoxIntegral.Prepartition.ext`：ext (h : forall J, J in π₁ ↔ J in π₂) : π₁
 = π₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem biUnion_congr (h : π₁ = π₂) (hi : ∀ J ∈ π₁, πi₁ J = πi₂ J) :
    π₁.biUnion πi₁ = π₂.biUnion πi₂ := by
  subst π₂
  ext J
  simp only [mem_biUnion]
  constructor <;> exact fun ⟨J', h₁, h₂⟩ => ⟨J', h₁, hi J' h₁ ▸ h₂⟩
/-
**BoxIntegral.Prepartition.biUnion_congr_of_le** 是 Mathlib 中的一个定理，位于命名空间 `BoxInt
egral.Prepartition`。
形式化陈述：biUnion_congr_of_le (h : π₁ = π₂) (hi : forall J <= I, πi₁ J = πi₂ J) : π₁
.biUnion πi₁ = π₂.biUnion πi₂
参数：h : π₁ = π₂；hi : forall J <= I, πi₁ J = πi₂ J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BoxIntegral.Prepartition.biUnion_congr`：biUnion_congr (h : π₁ = π₂) (hi 
: forall J in π₁, πi₁ J = πi₂ J) : π₁.biUnion πi₁ = π₂.biUnion πi₂
· 使用定理 `BoxIntegral.Prepartition.le_of_mem`：le_of_mem (hJ : J in π) : J <= I
-/
theorem biUnion_congr_of_le (h : π₁ = π₂) (hi : ∀ J ≤ I, πi₁ J = πi₂ J) :
    π₁.biUnion πi₁ = π₂.biUnion πi₂ :=
  biUnion_congr h fun J hJ => hi J (π₁.le_of_mem hJ)

@[simp]
/-
**BoxIntegral.Prepartition.iUnion_biUnion** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral
.Prepartition`。
形式化陈述：iUnion_biUnion (πi : forall J : Box ι, Prepartition J) : (π.biUnion πi).iU
nion = ⋃ J in π, (πi J).iUnion
参数：πi : forall J : Box ι, Prepartition J。
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
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iUnion_exists`：iUnion_exists {p : ι -> Prop} {f : Exists p -> Set α}
 : ⋃ x, f x = ⋃ (i) (h : p i), f ⟨i, h⟩
· 使用定理 `Set.biUnion_and'`：biUnion_and' (p : ι' -> Prop) (q : ι -> ι' -> Prop) (s
 : forall x y, p y ∧ q x y -> Set α) : ⋃ (x : ι) (y : ι') (h : p y ∧ q x y), s x
 y h =…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iUnion_biUnion (πi : ∀ J : Box ι, Prepartition J) :
    (π.biUnion πi).iUnion = ⋃ J ∈ π, (πi J).iUnion := by simp [Prepartition.iUnion]

open scoped Classical in
@[simp]
/-
**BoxIntegral.Prepartition.sum_biUnion_boxes** 是 Mathlib 中的一个定理，位于命名空间 `BoxInteg
ral.Prepartition`。
形式化陈述：sum_biUnion_boxes {M : Type*} [AddCommMonoid M] (π : Prepartition I) (πi :
 forall J, Prepartition J) (f : Box ι -> M) : (∑ J in π.boxes.biUnion fun J => (
πi J).boxes, f J) = ∑ J in π.boxes, ∑ J' in (πi J).boxes, f J'
参数：π : Prepartition I；πi : forall J, Prepartition J；f : Box ι -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sum_biUnion`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_4} [inst
 : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι]   {s : Finset κ} {t : κ
 → Finse…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s 
-> a ∉ t
· 使用定理 `BoxIntegral.Prepartition.eq_of_le_of_le`：eq_of_le_of_le (h₁ : J₁ in π) (
h₂ : J₂ in π) (hle₁ : J <= J₁) (hle₂ : J <= J₂) : J₁ = J₂
· 使用定理 `BoxIntegral.Prepartition.le_of_mem`：le_of_mem (hJ : J in π) : J <= I
-/
theorem sum_biUnion_boxes {M : Type*} [AddCommMonoid M] (π : Prepartition I)
    (πi : ∀ J, Prepartition J) (f : Box ι → M) :
    (∑ J ∈ π.boxes.biUnion fun J => (πi J).boxes, f J) =
      ∑ J ∈ π.boxes, ∑ J' ∈ (πi J).boxes, f J' := by
  refine Finset.sum_biUnion fun J₁ h₁ J₂ h₂ hne => Finset.disjoint_left.2 fun J' h₁' h₂' => ?_
  exact hne (π.eq_of_le_of_le h₁ h₂ ((πi J₁).le_of_mem h₁') ((πi J₂).le_of_mem h₂'))

open scoped Classical in
/-- Given a box `J ∈ π.biUnion πi`, returns the box `J' ∈ π` such that `J ∈ πi J'`.
For `J ∉ π.biUnion πi`, returns `I`. -/
/-
**BoxIntegral.Prepartition.biUnionIndex** 是 Mathlib 中的一个定义，位于命名空间 `BoxIntegral.P
repartition`。
形式化陈述：biUnionIndex (πi : forall (J : Box ι), Prepartition J) (J : Box ι) : Box ι
参数：πi : forall (J : Box ι), Prepartition J；J : Box ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a box `J ∈ π.biUnion πi`, returns the box `J' ∈ π` such that `J ∈ πi J'`.
For `J ∉ π.biUnion πi`, returns `I`.
-/
def biUnionIndex (πi : ∀ (J : Box ι), Prepartition J) (J : Box ι) : Box ι :=
  if hJ : J ∈ π.biUnion πi then (π.mem_biUnion.1 hJ).choose else I
/-
**BoxIntegral.Prepartition.biUnionIndex_mem** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegr
al.Prepartition`。
形式化陈述：biUnionIndex_mem (hJ : J in π.biUnion πi) : π.biUnionIndex πi J in π
参数：hJ : J in π.biUnion πi。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `BoxIntegral.Prepartition.biUnionIndex.eq_1`：∀ {ι : Type u_1} {I : BoxInt
egral.Box ι} (π : BoxIntegral.Prepartition I)   (πi : (J : BoxIntegral.Box ι) → 
BoxIntegral.Prepartition J) (J :…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `BoxIntegral.Prepartition.mem_biUnion`：mem_biUnion : J in π.biUnion πi ↔ 
exists J' in π, J in πi J'
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
theorem biUnionIndex_mem (hJ : J ∈ π.biUnion πi) : π.biUnionIndex πi J ∈ π := by
  rw [biUnionIndex, dif_pos hJ]
  exact (π.mem_biUnion.1 hJ).choose_spec.1
/-
**BoxIntegral.Prepartition.biUnionIndex_le** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegra
l.Prepartition`。
形式化陈述：biUnionIndex_le (πi : forall J, Prepartition J) (J : Box ι) : π.biUnionInd
ex πi J <= I
参数：πi : forall J, Prepartition J；J : Box ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BoxIntegral.Prepartition.le_of_mem`：le_of_mem (hJ : J in π) : J <= I
· 使用定理 `BoxIntegral.Prepartition.biUnionIndex_mem`：biUnionIndex_mem (hJ : J in π
.biUnion πi) : π.biUnionIndex πi J in π
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `BoxIntegral.Prepartition.biUnionIndex.eq_1`：∀ {ι : Type u_1} {I : BoxInt
egral.Box ι} (π : BoxIntegral.Prepartition I)   (πi : (J : BoxIntegral.Box ι) → 
BoxIntegral.Prepartition J) (J :…
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem biUnionIndex_le (πi : ∀ J, Prepartition J) (J : Box ι) : π.biUnionIndex πi J ≤ I := by
  by_cases hJ : J ∈ π.biUnion πi
  · exact π.le_of_mem (π.biUnionIndex_mem hJ)
  · rw [biUnionIndex, dif_neg hJ]
/-
**BoxIntegral.Prepartition.mem_biUnionIndex** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegr
al.Prepartition`。
形式化陈述：mem_biUnionIndex (hJ : J in π.biUnion πi) : J in πi (π.biUnionIndex πi J)
参数：hJ : J in π.biUnion πi。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `BoxIntegral.Prepartition.mem_biUnion`：mem_biUnion : J in π.biUnion πi ↔ 
exists J' in π, J in πi J'
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
theorem mem_biUnionIndex (hJ : J ∈ π.biUnion πi) : J ∈ πi (π.biUnionIndex πi J) := by
  convert! (π.mem_biUnion.1 hJ).choose_spec.2 <;> exact dif_pos hJ
/-
**BoxIntegral.Prepartition.le_biUnionIndex** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegra
l.Prepartition`。
形式化陈述：le_biUnionIndex (hJ : J in π.biUnion πi) : J <= π.biUnionIndex πi J
参数：hJ : J in π.biUnion πi。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BoxIntegral.Prepartition.le_of_mem`：le_of_mem (hJ : J in π) : J <= I
· 使用定理 `BoxIntegral.Prepartition.mem_biUnionIndex`：mem_biUnionIndex (hJ : J in π
.biUnion πi) : J in πi (π.biUnionIndex πi J)
-/
theorem le_biUnionIndex (hJ : J ∈ π.biUnion πi) : J ≤ π.biUnionIndex πi J :=
  le_of_mem _ (π.mem_biUnionIndex hJ)

/-- Uniqueness property of `BoxIntegral.Prepartition.biUnionIndex`. -/
/-
**BoxIntegral.Prepartition.biUnionIndex_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `BoxInt
egral.Prepartition`。
形式化陈述：biUnionIndex_of_mem (hJ : J in π) {J'} (hJ' : J' in πi J) : π.biUnionIndex
 πi J' = J
参数：hJ : J in π；hJ' : J' in πi J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `BoxIntegral.Prepartition.mem_biUnion`：mem_biUnion : J in π.biUnion πi ↔ 
exists J' in π, J in πi J'
· 使用定理 `BoxIntegral.Prepartition.eq_of_le_of_le`：eq_of_le_of_le (h₁ : J₁ in π) (
h₂ : J₂ in π) (hle₁ : J <= J₁) (hle₂ : J <= J₂) : J₁ = J₂
· 使用定理 `BoxIntegral.Prepartition.biUnionIndex_mem`：biUnionIndex_mem (hJ : J in π
.biUnion πi) : π.biUnionIndex πi J in π
· 使用定理 `BoxIntegral.Prepartition.le_biUnionIndex`：le_biUnionIndex (hJ : J in π.b
iUnion πi) : J <= π.biUnionIndex πi J
· 使用定理 `BoxIntegral.Prepartition.le_of_mem`：le_of_mem (hJ : J in π) : J <= I

--- 原说明 ---
Uniqueness property of `BoxIntegral.Prepartition.biUnionIndex`.
-/
theorem biUnionIndex_of_mem (hJ : J ∈ π) {J'} (hJ' : J' ∈ πi J) : π.biUnionIndex πi J' = J :=
  have : J' ∈ π.biUnion πi := π.mem_biUnion.2 ⟨J, hJ, hJ'⟩
  π.eq_of_le_of_le (π.biUnionIndex_mem this) hJ (π.le_biUnionIndex this) (le_of_mem _ hJ')
/-
**BoxIntegral.Prepartition.biUnion_assoc** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.
Prepartition`。
形式化陈述：biUnion_assoc (πi : forall J, Prepartition J) (πi' : Box ι -> forall J : B
ox ι, Prepartition J) : (π.biUnion fun J => (πi J).biUnion (πi' J)) = (π.biUnion
 πi).biUnion fun J => πi' (π.biUnionIndex πi J) J
参数：πi : forall J, Prepartition J；πi' : Box ι -> forall J : Box ι, Prepartition J
。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BoxIntegral.Prepartition.ext`：ext (h : forall J, J in π₁ ↔ J in π₂) : π₁
 = π₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `BoxIntegral.Prepartition.biUnionIndex_of_mem`：biUnionIndex_of_mem (hJ : 
J in π) {J'} (hJ' : J' in πi J) : π.biUnionIndex πi J' = J
-/
theorem biUnion_assoc (πi : ∀ J, Prepartition J) (πi' : Box ι → ∀ J : Box ι, Prepartition J) :
    (π.biUnion fun J => (πi J).biUnion (πi' J)) =
      (π.biUnion πi).biUnion fun J => πi' (π.biUnionIndex πi J) J := by
  ext J
  simp only [mem_biUnion]
  constructor
  · rintro ⟨J₁, hJ₁, J₂, hJ₂, hJ⟩
    refine ⟨J₂, ⟨J₁, hJ₁, hJ₂⟩, ?_⟩
    rwa [π.biUnionIndex_of_mem hJ₁ hJ₂]
  · rintro ⟨J₁, ⟨J₂, hJ₂, hJ₁⟩, hJ⟩
    refine ⟨J₂, hJ₂, J₁, hJ₁, ?_⟩
    rwa [π.biUnionIndex_of_mem hJ₂ hJ₁] at hJ

set_option backward.isDefEq.respectTransparency false in
/-- Create a `BoxIntegral.Prepartition` from a collection of possibly empty boxes by filtering out
the empty one if it exists. -/
/-
**BoxIntegral.Prepartition.ofWithBot** 是 Mathlib 中的一个定义，位于命名空间 `BoxIntegral.Prep
artition`。
形式化陈述：ofWithBot (boxes : Finset (WithBot (Box ι))) (le_of_mem : forall J in boxe
s, (J : WithBot (Box ι)) <= I) (pairwise_disjoint : Set.Pairwise (boxes : Set (W
ithBot (Box ι))) Disjoint) : Prepartition I where boxes
参数：boxes : Finset (WithBot (Box ι))；le_of_mem : forall J in boxes, (J : WithBot 
(Box ι)) <= I；pairwise_disjoint : Set.Pairwise (boxes : Set (WithBot (Box ι))) D
isjoint。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Create a `BoxIntegral.Prepartition` from a collection of possibly empty boxes by
 filtering out
the empty one if it exists.
-/
def ofWithBot (boxes : Finset (WithBot (Box ι)))
    (le_of_mem : ∀ J ∈ boxes, (J : WithBot (Box ι)) ≤ I)
    (pairwise_disjoint : Set.Pairwise (boxes : Set (WithBot (Box ι))) Disjoint) :
    Prepartition I where
  boxes := Finset.eraseNone boxes
  le_of_mem' J hJ := by
    rw [mem_eraseNone] at hJ
    simpa only [WithBot.some_eq_coe, WithBot.coe_le_coe] using le_of_mem _ hJ
  pairwiseDisjoint J₁ h₁ J₂ h₂ hne := by
    simp only [mem_coe, mem_eraseNone] at h₁ h₂
    exact Box.disjoint_coe.1 (pairwise_disjoint h₁ h₂ (mt Option.some_inj.1 hne))

@[simp]
/-
**BoxIntegral.Prepartition.mem_ofWithBot** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.
Prepartition`。
形式化陈述：mem_ofWithBot {boxes : Finset (WithBot (Box ι))} {h₁ h₂} : J in (ofWithBot
 boxes h₁ h₂ : Prepartition I) ↔ (J : WithBot (Box ι)) in boxes
参数：WithBot (Box ι)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.mem_eraseNone`：mem_eraseNone {s : Finset (Option α)} {x : α} : x 
in eraseNone s ↔ some x in s
-/
theorem mem_ofWithBot {boxes : Finset (WithBot (Box ι))} {h₁ h₂} :
    J ∈ (ofWithBot boxes h₁ h₂ : Prepartition I) ↔ (J : WithBot (Box ι)) ∈ boxes :=
  mem_eraseNone

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**BoxIntegral.Prepartition.iUnion_ofWithBot** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegr
al.Prepartition`。
形式化陈述：iUnion_ofWithBot (boxes : Finset (WithBot (Box ι))) (le_of_mem : forall J 
in boxes, (J : WithBot (Box ι)) <= I) (pairwise_disjoint : Set.Pairwise (boxes :
 Set (WithBot (Box ι))) Disjoint) : (ofWithBot boxes le_of_mem pairwise_disjoint
).iUnion = ⋃ J in boxes, ↑J
参数：boxes : Finset (WithBot (Box ι))；le_of_mem : forall J in boxes, (J : WithBot 
(Box ι)) <= I；pairwise_disjoint : Set.Pairwise (boxes : Set (WithBot (Box ι))) D
isjoint。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `Set.iUnion_comm`：iUnion_comm (s : ι -> ι' -> Set α) : ⋃ (i) (i'), s i i'
 = ⋃ (i') (i), s i i'
· 使用定理 `Set.iUnion_iUnion_eq_right`：iUnion_iUnion_eq_right {b : β} {s : forall x
 : β, b = x -> Set α} : ⋃ (x) (h : b = x), s x h = s b rfl
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
theorem iUnion_ofWithBot (boxes : Finset (WithBot (Box ι)))
    (le_of_mem : ∀ J ∈ boxes, (J : WithBot (Box ι)) ≤ I)
    (pairwise_disjoint : Set.Pairwise (boxes : Set (WithBot (Box ι))) Disjoint) :
    (ofWithBot boxes le_of_mem pairwise_disjoint).iUnion = ⋃ J ∈ boxes, ↑J := by
  suffices ⋃ (J : Box ι) (_ : ↑J ∈ boxes), ↑J = ⋃ J ∈ boxes, (J : Set (ι → ℝ)) by
    simpa [ofWithBot, Prepartition.iUnion]
  simp only [← Box.biUnion_coe_eq_coe, @iUnion_comm _ _ (Box ι), @iUnion_comm _ _ (@Eq _ _ _),
    iUnion_iUnion_eq_right]

set_option backward.isDefEq.respectTransparency false in
/-
**BoxIntegral.Prepartition.ofWithBot_le** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.P
repartition`。
形式化陈述：ofWithBot_le {boxes : Finset (WithBot (Box ι))} {le_of_mem : forall J in b
oxes, (J : WithBot (Box ι)) <= I} {pairwise_disjoint : Set.Pairwise (boxes : Set
 (WithBot (Box ι))) Disjoint} (H : forall J in boxes, J != ⊥ -> exists J' in π, 
J <= ↑J') : ofWithBot boxes le_of_mem pairwise_disjoint <= π
参数：WithBot (Box ι)；J : WithBot (Box ι)；boxes : Set (WithBot (Box ι))；H : forall 
J in boxes, J != ⊥ -> exists J' in π, J <= ↑J'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `WithBot.coe_ne_bot`：coe_ne_bot : (a : WithBot α) != ⊥
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem ofWithBot_le {boxes : Finset (WithBot (Box ι))}
    {le_of_mem : ∀ J ∈ boxes, (J : WithBot (Box ι)) ≤ I}
    {pairwise_disjoint : Set.Pairwise (boxes : Set (WithBot (Box ι))) Disjoint}
    (H : ∀ J ∈ boxes, J ≠ ⊥ → ∃ J' ∈ π, J ≤ ↑J') :
    ofWithBot boxes le_of_mem pairwise_disjoint ≤ π := by
  have : ∀ J : Box ι, ↑J ∈ boxes → ∃ J' ∈ π, J ≤ J' := fun J hJ => by
    simpa only [WithBot.coe_le_coe] using H J hJ WithBot.coe_ne_bot
  simpa [ofWithBot, le_def]
/-
**BoxIntegral.Prepartition.le_ofWithBot** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.P
repartition`。
形式化陈述：le_ofWithBot {boxes : Finset (WithBot (Box ι))} {le_of_mem : forall J in b
oxes, (J : WithBot (Box ι)) <= I} {pairwise_disjoint : Set.Pairwise (boxes : Set
 (WithBot (Box ι))) Disjoint} (H : forall J in π, exists J' in boxes, ↑J <= J') 
: π <= ofWithBot boxes le_of_mem pairwise_disjoint
参数：WithBot (Box ι)；J : WithBot (Box ι)；boxes : Set (WithBot (Box ι))；H : forall 
J in π, exists J' in boxes, ↑J <= J'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `ne_bot_of_le_ne_bot`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : Or
derBot α] {a b : α}, b ≠ ⊥ → b ≤ a → a ≠ ⊥
· 使用定理 `WithBot.coe_ne_bot`：coe_ne_bot : (a : WithBot α) != ⊥
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `BoxIntegral.Prepartition.mem_ofWithBot`：mem_ofWithBot {boxes : Finset (W
ithBot (Box ι))} {h₁ h₂} : J in (ofWithBot boxes h₁ h₂ : Prepartition I) ↔ (J : 
WithBot (Box ι)) in boxes
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `WithBot.coe_le_coe`：coe_le_coe : (a : WithBot α) <= b ↔ a <= b
-/
theorem le_ofWithBot {boxes : Finset (WithBot (Box ι))}
    {le_of_mem : ∀ J ∈ boxes, (J : WithBot (Box ι)) ≤ I}
    {pairwise_disjoint : Set.Pairwise (boxes : Set (WithBot (Box ι))) Disjoint}
    (H : ∀ J ∈ π, ∃ J' ∈ boxes, ↑J ≤ J') : π ≤ ofWithBot boxes le_of_mem pairwise_disjoint := by
  intro J hJ
  rcases H J hJ with ⟨J', J'mem, hle⟩
  lift J' to Box ι using ne_bot_of_le_ne_bot WithBot.coe_ne_bot hle
  exact ⟨J', mem_ofWithBot.2 J'mem, WithBot.coe_le_coe.1 hle⟩
/-
**BoxIntegral.Prepartition.ofWithBot_mono** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral
.Prepartition`。
形式化陈述：ofWithBot_mono {boxes₁ : Finset (WithBot (Box ι))} {le_of_mem₁ : forall J 
in boxes₁, (J : WithBot (Box ι)) <= I} {pairwise_disjoint₁ : Set.Pairwise (boxes
₁ : Set (WithBot (Box ι))) Disjoint} {boxes₂ : Finset (WithBot (Box ι))} {le_of_
mem₂ : forall J in boxes₂, (J : WithBot (Box ι)) <= I} {pairwise_disjoint₂ : Set
.Pairwise (boxes₂ : Set (WithBot (Box ι))) Disjoint} (H : forall J in boxes₁, J 
!= ⊥ -> exists J' in boxes₂, J <= J') : ofWithBot boxes₁ le_of_mem₁ pairwise_dis
joint₁ <= ofWithBot boxes₂
参数：WithBot (Box ι)；J : WithBot (Box ι)；boxes₁ : Set (WithBot (Box ι))；WithBot (B
ox ι)；J : WithBot (Box ι)；boxes₂ : Set (WithBot (Box ι))；H : forall J in boxes₁,
 J != ⊥ -> exists J' in boxes₂, J <= J'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BoxIntegral.Prepartition.le_ofWithBot`：le_ofWithBot {boxes : Finset (Wit
hBot (Box ι))} {le_of_mem : forall J in boxes, (J : WithBot (Box ι)) <= I} {pair
wise_disjoint : Set.Pairwis…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `BoxIntegral.Prepartition.mem_ofWithBot`：mem_ofWithBot {boxes : Finset (W
ithBot (Box ι))} {h₁ h₂} : J in (ofWithBot boxes h₁ h₂ : Prepartition I) ↔ (J : 
WithBot (Box ι)) in boxes
· 使用定理 `WithBot.coe_ne_bot`：coe_ne_bot : (a : WithBot α) != ⊥
-/
theorem ofWithBot_mono {boxes₁ : Finset (WithBot (Box ι))}
    {le_of_mem₁ : ∀ J ∈ boxes₁, (J : WithBot (Box ι)) ≤ I}
    {pairwise_disjoint₁ : Set.Pairwise (boxes₁ : Set (WithBot (Box ι))) Disjoint}
    {boxes₂ : Finset (WithBot (Box ι))} {le_of_mem₂ : ∀ J ∈ boxes₂, (J : WithBot (Box ι)) ≤ I}
    {pairwise_disjoint₂ : Set.Pairwise (boxes₂ : Set (WithBot (Box ι))) Disjoint}
    (H : ∀ J ∈ boxes₁, J ≠ ⊥ → ∃ J' ∈ boxes₂, J ≤ J') :
    ofWithBot boxes₁ le_of_mem₁ pairwise_disjoint₁ ≤
      ofWithBot boxes₂ le_of_mem₂ pairwise_disjoint₂ :=
  le_ofWithBot _ fun J hJ => H J (mem_ofWithBot.1 hJ) WithBot.coe_ne_bot
/-
**BoxIntegral.Prepartition.sum_ofWithBot** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.
Prepartition`。
形式化陈述：sum_ofWithBot {M : Type*} [AddCommMonoid M] (boxes : Finset (WithBot (Box 
ι))) (le_of_mem : forall J in boxes, (J : WithBot (Box ι)) <= I) (pairwise_disjo
int : Set.Pairwise (boxes : Set (WithBot (Box ι))) Disjoint) (f : Box ι -> M) : 
(∑ J in (ofWithBot boxes le_of_mem pairwise_disjoint).boxes, f J) = ∑ J in boxes
, Option.elim' 0 f J
参数：boxes : Finset (WithBot (Box ι))；le_of_mem : forall J in boxes, (J : WithBot 
(Box ι)) <= I；pairwise_disjoint : Set.Pairwise (boxes : Set (WithBot (Box ι))) D
isjoint；f : Box ι -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sum_eraseNone`：∀ {α : Type u_1} {M : Type u_2} [inst : AddCommMon
oid M] (f : α → M) (s : Finset (Option α)),   ∑ x ∈ Finset.eraseNone s, f x = ∑ 
x ∈ s, Opt…
-/
theorem sum_ofWithBot {M : Type*} [AddCommMonoid M] (boxes : Finset (WithBot (Box ι)))
    (le_of_mem : ∀ J ∈ boxes, (J : WithBot (Box ι)) ≤ I)
    (pairwise_disjoint : Set.Pairwise (boxes : Set (WithBot (Box ι))) Disjoint) (f : Box ι → M) :
    (∑ J ∈ (ofWithBot boxes le_of_mem pairwise_disjoint).boxes, f J) =
      ∑ J ∈ boxes, Option.elim' 0 f J :=
  Finset.sum_eraseNone _ _

open scoped Classical in
/-- Restrict a prepartition to a box. -/
/-
**BoxIntegral.Prepartition.restrict** 是 Mathlib 中的一个定义，位于命名空间 `BoxIntegral.Prepa
rtition`。
形式化陈述：restrict (π : Prepartition I) (J : Box ι) : Prepartition J
参数：π : Prepartition I；J : Box ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Restrict a prepartition to a box.
-/
def restrict (π : Prepartition I) (J : Box ι) : Prepartition J :=
  ofWithBot (π.boxes.image fun J' : Box ι => J ⊓ J')
    (fun J' hJ' => by
      rcases Finset.mem_image.1 hJ' with ⟨J', -, rfl⟩
      exact inf_le_left)
    (by
      simp only [Set.Pairwise, Finset.mem_coe, Finset.mem_image]
      rintro _ ⟨J₁, h₁, rfl⟩ _ ⟨J₂, h₂, rfl⟩ Hne
      have : J₁ ≠ J₂ := by
        rintro rfl
        exact Hne rfl
      exact ((Box.disjoint_coe.2 <| π.disjoint_coe_of_mem h₁ h₂ this).inf_left' _).inf_right' _)

@[simp]
/-
**BoxIntegral.Prepartition.mem_restrict** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.P
repartition`。
形式化陈述：mem_restrict : J₁ in π.restrict J ↔ exists J' in π, (J₁ : WithBot (Box ι))
 = ↑J ⊓ ↑J'
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
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_restrict : J₁ ∈ π.restrict J ↔ ∃ J' ∈ π, (J₁ : WithBot (Box ι)) = ↑J ⊓ ↑J' := by
  simp [restrict, eq_comm]
/-
**BoxIntegral.Prepartition.mem_restrict'** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.
Prepartition`。
形式化陈述：mem_restrict' : J₁ in π.restrict J ↔ exists J' in π, (J₁ : Set (ι -> Real)
) = ↑J inter ↑J'
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
· 使用定理 `BoxIntegral.Box.coe_inf`：coe_inf (I J : WithBot (Box ι)) : (↑(I ⊓ J) : S
et (ι -> Real)) = (I : Set _) inter J
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_restrict' : J₁ ∈ π.restrict J ↔ ∃ J' ∈ π, (J₁ : Set (ι → ℝ)) = ↑J ∩ ↑J' := by
  simp only [mem_restrict, ← Box.withBotCoe_inj, Box.coe_inf, Box.coe_coe]

@[gcongr, mono]
/-
**BoxIntegral.Prepartition.restrict_mono** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.
Prepartition`。
形式化陈述：restrict_mono {π₁ π₂ : Prepartition I} (Hle : π₁ <= π₂) : π₁.restrict J <=
 π₂.restrict J
参数：Hle : π₁ <= π₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BoxIntegral.Prepartition.ofWithBot_mono`：ofWithBot_mono {boxes₁ : Finset
 (WithBot (Box ι))} {le_of_mem₁ : forall J in boxes₁, (J : WithBot (Box ι)) <= I
} {pairwise_disjoint₁ : Set.P…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.mem_image`：mem_image : b in s.image f ↔ exists a in s, f a = b
· 使用定理 `Finset.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {a} (h : a in s) 
: f a in s.image f
· 使用定理 `inf_le_inf_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α} (c :
 α), b ≤ a → c ⊓ b ≤ c ⊓ a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `WithBot.coe_le_coe`：coe_le_coe : (a : WithBot α) <= b ↔ a <= b
-/
theorem restrict_mono {π₁ π₂ : Prepartition I} (Hle : π₁ ≤ π₂) : π₁.restrict J ≤ π₂.restrict J := by
  classical
  refine ofWithBot_mono fun J₁ hJ₁ hne => ?_
  rw [Finset.mem_image] at hJ₁; rcases hJ₁ with ⟨J₁, hJ₁, rfl⟩
  rcases Hle hJ₁ with ⟨J₂, hJ₂, hle⟩
  exact ⟨_, Finset.mem_image_of_mem _ hJ₂, inf_le_inf_left _ <| WithBot.coe_le_coe.2 hle⟩
/-
**BoxIntegral.Prepartition.monotone_restrict** 是 Mathlib 中的一个定理，位于命名空间 `BoxInteg
ral.Prepartition`。
形式化陈述：monotone_restrict : Monotone fun π : Prepartition I => restrict π J
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BoxIntegral.Prepartition.restrict_mono`：restrict_mono {π₁ π₂ : Prepartit
ion I} (Hle : π₁ <= π₂) : π₁.restrict J <= π₂.restrict J
-/
theorem monotone_restrict : Monotone fun π : Prepartition I => restrict π J :=
  fun _ _ => restrict_mono

set_option backward.isDefEq.respectTransparency false in
/-- Restricting to a larger box does not change the set of boxes. We cannot claim equality
of prepartitions because they have different types. -/
/-
**BoxIntegral.Prepartition.restrict_boxes_of_le** 是 Mathlib 中的一个定理，位于命名空间 `BoxIn
tegral.Prepartition`。
形式化陈述：restrict_boxes_of_le (π : Prepartition I) (h : I <= J) : (π.restrict J).bo
xes = π.boxes
参数：π : Prepartition I；h : I <= J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.eraseNone_eq_biUnion`：eraseNone_eq_biUnion [DecidableEq α] (s : F
inset (Option α)) : eraseNone s = s.biUnion Option.toFinset
· 使用定理 `BoxIntegral.Prepartition.mk.congr_simp`：∀ {ι : Type u_1} {I : BoxIntegra
l.Box ι} (boxes boxes_1 : Finset (BoxIntegral.Box ι)) (e_boxes : boxes = boxes_1
)   (le_of_mem' : ∀ J ∈ boxe…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.image_biUnion`：image_biUnion [DecidableEq γ] {f : α -> β} {s : Fi
nset α} {t : β -> Finset γ} : (s.image f).biUnion t = s.biUnion fun a => t (f a)
· 使用引理 `Finset.biUnion_congr`：biUnion_congr (hs : s₁ = s₂) (ht : forall a in s₁,
 t₁ a = t₂ a) : s₁.biUnion t₁ = s₂.biUnion t₂
· 使用定理 `inf_of_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, b ≤
 a → a ⊓ b = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `WithBot.coe_le_coe`：coe_le_coe : (a : WithBot α) <= b ↔ a <= b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `BoxIntegral.Prepartition.le_of_mem`：le_of_mem (hJ : J in π) : J <= I
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithBot.some_eq_coe`：some_eq_coe (a : α) : (Option.some a : WithBot α) =
 (↑a : WithBot α)
· 使用定理 `Option.toFinset_some`：toFinset_some {a : α} : (some a).toFinset = {a}
· 使用引理 `Finset.biUnion_singleton_eq_self`：biUnion_singleton_eq_self [DecidableEq
 α] : s.biUnion (singleton : α -> Finset α) = s

--- 原说明 ---
Restricting to a larger box does not change the set of boxes. We cannot claim eq
uality
of prepartitions because they have different types.
-/
theorem restrict_boxes_of_le (π : Prepartition I) (h : I ≤ J) : (π.restrict J).boxes = π.boxes := by
  classical
  simp only [restrict, ofWithBot, eraseNone_eq_biUnion]
  refine Finset.image_biUnion.trans ?_
  refine (Finset.biUnion_congr rfl ?_).trans Finset.biUnion_singleton_eq_self
  intro J' hJ'
  rw [inf_of_le_right, ← WithBot.some_eq_coe, Option.toFinset_some]
  exact WithBot.coe_le_coe.2 ((π.le_of_mem hJ').trans h)

@[simp]
/-
**BoxIntegral.Prepartition.restrict_self** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.
Prepartition`。
形式化陈述：restrict_self : π.restrict I = π
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BoxIntegral.Prepartition.injective_boxes`：injective_boxes : Function.Inj
ective (boxes : Prepartition I -> Finset (Box ι))
· 使用定理 `BoxIntegral.Prepartition.restrict_boxes_of_le`：restrict_boxes_of_le (π :
 Prepartition I) (h : I <= J) : (π.restrict J).boxes = π.boxes
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem restrict_self : π.restrict I = π :=
  injective_boxes <| restrict_boxes_of_le π le_rfl

@[simp]
/-
**BoxIntegral.Prepartition.iUnion_restrict** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegra
l.Prepartition`。
形式化陈述：iUnion_restrict : (π.restrict J).iUnion = (J : Set (ι -> Real)) inter (π.i
Union)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `BoxIntegral.Prepartition.iUnion_ofWithBot`：iUnion_ofWithBot (boxes : Fin
set (WithBot (Box ι))) (le_of_mem : forall J in boxes, (J : WithBot (Box ι)) <= 
I) (pairwise_disjoint : Set.Pai…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iUnion_exists`：iUnion_exists {p : ι -> Prop} {f : Exists p -> Set α}
 : ⋃ x, f x = ⋃ (i) (h : p i), f ⟨i, h⟩
· 使用定理 `Set.biUnion_and'`：biUnion_and' (p : ι' -> Prop) (q : ι -> ι' -> Prop) (s
 : forall x y, p y ∧ q x y -> Set α) : ⋃ (x : ι) (y : ι') (h : p y ∧ q x y), s x
 y h =…
· 使用定理 `Set.iUnion_iUnion_eq_right`：iUnion_iUnion_eq_right {b : β} {s : forall x
 : β, b = x -> Set α} : ⋃ (x) (h : b = x), s x h = s b rfl
· 使用定理 `BoxIntegral.Box.coe_inf`：coe_inf (I J : WithBot (Box ι)) : (↑(I ⊓ J) : S
et (ι -> Real)) = (I : Set _) inter J
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iUnion_restrict : (π.restrict J).iUnion = (J : Set (ι → ℝ)) ∩ (π.iUnion) := by
  simp [restrict, ← inter_iUnion, ← iUnion_def]

@[simp]
/-
**BoxIntegral.Prepartition.restrict_biUnion** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegr
al.Prepartition`。
形式化陈述：restrict_biUnion (πi : forall J, Prepartition J) (hJ : J in π) : (π.biUnio
n πi).restrict J = πi J
参数：πi : forall J, Prepartition J；hJ : J in π。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `BoxIntegral.Prepartition.eq_of_boxes_subset_iUnion_superset`：eq_of_boxes
_subset_iUnion_superset (h₁ : π₁.boxes subseteq π₂.boxes) (h₂ : π₂.iUnion subset
eq π₁.iUnion) : π₁ = π₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `BoxIntegral.Prepartition.mem_restrict`：mem_restrict : J₁ in π.restrict J
 ↔ exists J' in π, (J₁ : WithBot (Box ι)) = ↑J ⊓ ↑J'
· 使用定理 `BoxIntegral.Prepartition.mem_biUnion`：mem_biUnion : J in π.biUnion πi ↔ 
exists J' in π, J in πi J'
· 使用定理 `inf_of_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, b ≤
 a → a ⊓ b = b
· 使用引理 `WithBot.coe_le_coe`：coe_le_coe : (a : WithBot α) <= b ↔ a <= b
· 使用定理 `BoxIntegral.Prepartition.le_of_mem`：le_of_mem (hJ : J in π) : J <= I
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `BoxIntegral.Prepartition.iUnion_restrict`：iUnion_restrict : (π.restrict 
J).iUnion = (J : Set (ι -> Real)) inter (π.iUnion)
· 使用定理 `BoxIntegral.Prepartition.iUnion_biUnion`：iUnion_biUnion (πi : forall J :
 Box ι, Prepartition J) : (π.biUnion πi).iUnion = ⋃ J in π, (πi J).iUnion
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `BoxIntegral.Prepartition.eq_of_mem_of_mem`：eq_of_mem_of_mem (h₁ : J₁ in 
π) (h₂ : J₂ in π) (hx₁ : x in J₁) (hx₂ : x in J₂) : J₁ = J₂
· 使用定理 `BoxIntegral.Prepartition.iUnion_subset`：iUnion_subset : π.iUnion subsete
q I
-/
theorem restrict_biUnion (πi : ∀ J, Prepartition J) (hJ : J ∈ π) :
    (π.biUnion πi).restrict J = πi J := by
  refine (eq_of_boxes_subset_iUnion_superset (fun J₁ h₁ => ?_) ?_).symm
  · refine (mem_restrict _).2 ⟨J₁, π.mem_biUnion.2 ⟨J, hJ, h₁⟩, (inf_of_le_right ?_).symm⟩
    exact WithBot.coe_le_coe.2 (le_of_mem _ h₁)
  · simp only [iUnion_restrict, iUnion_biUnion, Set.subset_def, Set.mem_inter_iff, Set.mem_iUnion]
    rintro x ⟨hxJ, J₁, h₁, hx⟩
    obtain rfl : J = J₁ := π.eq_of_mem_of_mem hJ h₁ hxJ (iUnion_subset _ hx)
    exact hx
/-
**BoxIntegral.Prepartition.biUnion_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral
.Prepartition`。
形式化陈述：biUnion_le_iff {πi : forall J, Prepartition J} {π' : Prepartition I} : π.b
iUnion πi <= π' ↔ forall J in π, πi J <= π'.restrict J
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `BoxIntegral.Prepartition.restrict_biUnion`：restrict_biUnion (πi : forall
 J, Prepartition J) (hJ : J in π) : (π.biUnion πi).restrict J = πi J
· 使用定理 `BoxIntegral.Prepartition.restrict_mono`：restrict_mono {π₁ π₂ : Prepartit
ion I} (Hle : π₁ <= π₂) : π₁.restrict J <= π₂.restrict J
· 使用定理 `BoxIntegral.Prepartition.mem_biUnion`：mem_biUnion : J in π.biUnion πi ↔ 
exists J' in π, J in πi J'
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `BoxIntegral.Prepartition.mem_restrict`：mem_restrict : J₁ in π.restrict J
 ↔ exists J' in π, (J₁ : WithBot (Box ι)) = ↑J ⊓ ↑J'
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `WithBot.coe_le_coe`：coe_le_coe : (a : WithBot α) <= b ↔ a <= b
· 使用定理 `Eq.trans_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ c →
 a ≤ c
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
-/
theorem biUnion_le_iff {πi : ∀ J, Prepartition J} {π' : Prepartition I} :
    π.biUnion πi ≤ π' ↔ ∀ J ∈ π, πi J ≤ π'.restrict J := by
  constructor <;> intro H J hJ
  · rw [← π.restrict_biUnion πi hJ]
    exact restrict_mono H
  · rw [mem_biUnion] at hJ
    rcases hJ with ⟨J₁, h₁, hJ⟩
    rcases H J₁ h₁ hJ with ⟨J₂, h₂, Hle⟩
    rcases π'.mem_restrict.mp h₂ with ⟨J₃, h₃, H⟩
    exact ⟨J₃, h₃, Hle.trans <| WithBot.coe_le_coe.1 <| H.trans_le inf_le_right⟩
/-
**BoxIntegral.Prepartition.le_biUnion_iff** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral
.Prepartition`。
形式化陈述：le_biUnion_iff {πi : forall J, Prepartition J} {π' : Prepartition I} : π' 
<= π.biUnion πi ↔ π' <= π ∧ forall J in π, π'.restrict J <= πi J
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `BoxIntegral.Prepartition.biUnion_le`：biUnion_le (πi : forall J, Preparti
tion J) : π.biUnion πi <= π
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `BoxIntegral.Prepartition.restrict_biUnion`：restrict_biUnion (πi : forall
 J, Prepartition J) (hJ : J in π) : (π.biUnion πi).restrict J = πi J
· 使用定理 `BoxIntegral.Prepartition.restrict_mono`：restrict_mono {π₁ π₂ : Prepartit
ion I} (Hle : π₁ <= π₂) : π₁.restrict J <= π₂.restrict J
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `BoxIntegral.Prepartition.mem_restrict`：mem_restrict : J₁ in π.restrict J
 ↔ exists J' in π, (J₁ : WithBot (Box ι)) = ↑J ⊓ ↑J'
· 使用定理 `inf_of_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, b ≤
 a → a ⊓ b = b
· 使用引理 `WithBot.coe_le_coe`：coe_le_coe : (a : WithBot α) <= b ↔ a <= b
· 使用定理 `BoxIntegral.Prepartition.mem_biUnion`：mem_biUnion : J in π.biUnion πi ↔ 
exists J' in π, J in πi J'
-/
theorem le_biUnion_iff {πi : ∀ J, Prepartition J} {π' : Prepartition I} :
    π' ≤ π.biUnion πi ↔ π' ≤ π ∧ ∀ J ∈ π, π'.restrict J ≤ πi J := by
  refine ⟨fun H => ⟨H.trans (π.biUnion_le πi), fun J hJ => ?_⟩, ?_⟩
  · rw [← π.restrict_biUnion πi hJ]
    exact restrict_mono H
  · rintro ⟨H, Hi⟩ J' hJ'
    rcases H hJ' with ⟨J, hJ, hle⟩
    have : J' ∈ π'.restrict J :=
      π'.mem_restrict.2 ⟨J', hJ', (inf_of_le_right <| WithBot.coe_le_coe.2 hle).symm⟩
    rcases Hi J hJ this with ⟨Ji, hJi, hlei⟩
    exact ⟨Ji, π.mem_biUnion.2 ⟨J, hJ, hJi⟩, hlei⟩
/-
**BoxIntegral.Prepartition.** 是 Mathlib 中的一个实例，位于命名空间 `BoxIntegral.Prepartition`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SemilatticeInf (Prepartition I) :=
  { inf := fun π₁ π₂ => π₁.biUnion fun J => π₂.restrict J
    inf_le_left := fun π₁ _ => π₁.biUnion_le _
    inf_le_right := fun _ _ => (biUnion_le_iff _).2 fun _ _ => le_rfl
    le_inf := fun _ π₁ _ h₁ h₂ => π₁.le_biUnion_iff.2 ⟨h₁, fun _ _ => restrict_mono h₂⟩ }
/-
**BoxIntegral.Prepartition.inf_def** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.Prepar
tition`。
形式化陈述：inf_def (π₁ π₂ : Prepartition I) : π₁ ⊓ π₂ = π₁.biUnion fun J => π₂.restri
ct J
参数：π₁ π₂ : Prepartition I。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inf_def (π₁ π₂ : Prepartition I) : π₁ ⊓ π₂ = π₁.biUnion fun J => π₂.restrict J := rfl

@[simp]
/-
**BoxIntegral.Prepartition.mem_inf** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.Prepar
tition`。
形式化陈述：mem_inf {π₁ π₂ : Prepartition I} : J in π₁ ⊓ π₂ ↔ exists J₁ in π₁, exists 
J₂ in π₂, (J : WithBot (Box ι)) = ↑J₁ ⊓ ↑J₂
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_inf {π₁ π₂ : Prepartition I} :
    J ∈ π₁ ⊓ π₂ ↔ ∃ J₁ ∈ π₁, ∃ J₂ ∈ π₂, (J : WithBot (Box ι)) = ↑J₁ ⊓ ↑J₂ := by
  simp only [inf_def, mem_biUnion, mem_restrict]

@[simp]
/-
**BoxIntegral.Prepartition.iUnion_inf** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.Pre
partition`。
形式化陈述：iUnion_inf (π₁ π₂ : Prepartition I) : (π₁ ⊓ π₂).iUnion = π₁.iUnion inter π
₂.iUnion
参数：π₁ π₂ : Prepartition I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `BoxIntegral.Prepartition.iUnion_biUnion`：iUnion_biUnion (πi : forall J :
 Box ι, Prepartition J) : (π.biUnion πi).iUnion = ⋃ J in π, (πi J).iUnion
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `BoxIntegral.Prepartition.iUnion_restrict`：iUnion_restrict : (π.restrict 
J).iUnion = (J : Set (ι -> Real)) inter (π.iUnion)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iUnion_inf (π₁ π₂ : Prepartition I) : (π₁ ⊓ π₂).iUnion = π₁.iUnion ∩ π₂.iUnion := by
  simp only [inf_def, iUnion_biUnion, iUnion_restrict, ← iUnion_inter, ← iUnion_def]

open scoped Classical in
/-- The prepartition with boxes `{J ∈ π | p J}`. -/
@[simps]
/-
**BoxIntegral.Prepartition.filter** 是 Mathlib 中的一个定义，位于命名空间 `BoxIntegral.Prepart
ition`。
形式化陈述：filter (π : Prepartition I) (p : Box ι -> Prop) : Prepartition I where box
es
参数：π : Prepartition I；p : Box ι -> Prop。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The prepartition with boxes `{J ∈ π | p J}`.
-/
def filter (π : Prepartition I) (p : Box ι → Prop) : Prepartition I where
  boxes := {J ∈ π.boxes | p J}
  le_of_mem' _ hJ := π.le_of_mem (mem_filter.1 hJ).1
  pairwiseDisjoint _ h₁ _ h₂ := π.disjoint_coe_of_mem (mem_filter.1 h₁).1 (mem_filter.1 h₂).1

@[simp]
/-
**BoxIntegral.Prepartition.mem_filter** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.Pre
partition`。
形式化陈述：mem_filter {p : Box ι -> Prop} : J in π.filter p ↔ J in π ∧ p J
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
-/
theorem mem_filter {p : Box ι → Prop} : J ∈ π.filter p ↔ J ∈ π ∧ p J := by
  classical
  exact Finset.mem_filter
/-
**BoxIntegral.Prepartition.filter_le** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.Prep
artition`。
形式化陈述：filter_le (π : Prepartition I) (p : Box ι -> Prop) : π.filter p <= π
参数：π : Prepartition I；p : Box ι -> Prop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `BoxIntegral.Prepartition.mem_filter`：mem_filter {p : Box ι -> Prop} : J 
in π.filter p ↔ J in π ∧ p J
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem filter_le (π : Prepartition I) (p : Box ι → Prop) : π.filter p ≤ π := fun J hJ =>
  let ⟨hπ, _⟩ := π.mem_filter.1 hJ
  ⟨J, hπ, le_rfl⟩
/-
**BoxIntegral.Prepartition.filter_of_true** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral
.Prepartition`。
形式化陈述：filter_of_true {p : Box ι -> Prop} (hp : forall J in π, p J) : π.filter p 
= π
参数：hp : forall J in π, p J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BoxIntegral.Prepartition.ext`：ext (h : forall J, J in π₁ ↔ J in π₂) : π₁
 = π₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem filter_of_true {p : Box ι → Prop} (hp : ∀ J ∈ π, p J) : π.filter p = π := by
  ext J
  simpa using hp J

@[simp]
/-
**BoxIntegral.Prepartition.filter_true** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.Pr
epartition`。
形式化陈述：filter_true : (π.filter fun _ => True) = π
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BoxIntegral.Prepartition.filter_of_true`：filter_of_true {p : Box ι -> Pr
op} (hp : forall J in π, p J) : π.filter p = π
· 使用定理 `trivial`：True
-/
theorem filter_true : (π.filter fun _ => True) = π :=
  π.filter_of_true fun _ _ => trivial

@[simp]
/-
**BoxIntegral.Prepartition.iUnion_filter_not** 是 Mathlib 中的一个定理，位于命名空间 `BoxInteg
ral.Prepartition`。
形式化陈述：iUnion_filter_not (π : Prepartition I) (p : Box ι -> Prop) : (π.filter fun
 J => ¬p J).iUnion = π.iUnion \ (π.filter p).iUnion
参数：π : Prepartition I；p : Box ι -> Prop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `BoxIntegral.Prepartition.filter_boxes`：∀ {ι : Type u_1} {I : BoxIntegral
.Box ι} (π : BoxIntegral.Prepartition I) (p : BoxIntegral.Box ι → Prop),   (π.fi
lter p).boxes = {J ∈ π.boxe…
· 使用定理 `Finset.coe_filter`：∀ {α : Type u_1} (p : α → Prop) [inst : DecidablePred
 p] (s : Finset α), ↑(Finset.filter p s) = {x | x ∈ s ∧ p x}
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Set.biUnion_sdiff_biUnion_eq`：biUnion_sdiff_biUnion_eq {s t : Set ι} {f 
: ι -> Set α} (h : (s union t).PairwiseDisjoint f) : ((⋃ i in s, f i) \ ⋃ i in t
, f i) = ⋃ i in s …
· 使用定理 `Set.PairwiseDisjoint.eq_1`：∀ {α : Type u_1} {ι : Type u_4} [inst : Parti
alOrder α] [inst_1 : OrderBot α] (s : Set ι) (f : ι → α),   s.PairwiseDisjoint f
 = s.Pairwise (…
· 使用定理 `Set.union_eq_left`：union_eq_left {s t : Set α} : s union t = s ↔ t subse
teq s
· 使用定理 `BoxIntegral.Prepartition.pairwiseDisjoint`：∀ {ι : Type u_1} {I : BoxInte
gral.Box ι} (self : BoxIntegral.Prepartition I),   (↑self.boxes).Pairwise (Funct
ion.onFun Disjoint BoxIntegral.…
-/
theorem iUnion_filter_not (π : Prepartition I) (p : Box ι → Prop) :
    (π.filter fun J => ¬p J).iUnion = π.iUnion \ (π.filter p).iUnion := by
  simp only [Prepartition.iUnion]
  convert!
    (@Set.biUnion_sdiff_biUnion_eq (ι → ℝ) (Box ι) π.boxes (π.filter p).boxes (↑) _).symm using 4
  · simp +contextual
  · rw [Set.PairwiseDisjoint]
    convert! π.pairwiseDisjoint
    rw [Set.union_eq_left, filter_boxes, coe_filter]
    exact fun _ ⟨h, _⟩ => h

open scoped Classical in
/-
**BoxIntegral.Prepartition.sum_fiberwise** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.
Prepartition`。
形式化陈述：sum_fiberwise {α M} [AddCommMonoid M] (π : Prepartition I) (f : Box ι -> α
) (g : Box ι -> M) : (∑ y in π.boxes.image f, ∑ J in (π.filter fun J => f J = y)
.boxes, g J) = ∑ J in π.boxes, g J
参数：π : Prepartition I；f : Box ι -> α；g : Box ι -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_fiberwise_of_maps_to`：∀ {ι : Type u_1} {κ : Type u_2} {M : Ty
pe u_4} [inst : AddCommMonoid M] {s : Finset ι} {t : Finset κ}   [inst_1 : Decid
ableEq κ] {g : ι → κ}…
· 使用定理 `Finset.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {a} (h : a in s) 
: f a in s.image f
-/
theorem sum_fiberwise {α M} [AddCommMonoid M] (π : Prepartition I) (f : Box ι → α) (g : Box ι → M) :
    (∑ y ∈ π.boxes.image f, ∑ J ∈ (π.filter fun J => f J = y).boxes, g J) =
      ∑ J ∈ π.boxes, g J := by
  convert! sum_fiberwise_of_maps_to (fun _ => Finset.mem_image_of_mem f) g

open scoped Classical in
/-- Union of two disjoint prepartitions. -/
@[simps]
/-
**BoxIntegral.Prepartition.disjUnion** 是 Mathlib 中的一个定义，位于命名空间 `BoxIntegral.Prep
artition`。
形式化陈述：disjUnion (π₁ π₂ : Prepartition I) (h : Disjoint π₁.iUnion π₂.iUnion) : Pr
epartition I where boxes
参数：π₁ π₂ : Prepartition I；h : Disjoint π₁.iUnion π₂.iUnion。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Union of two disjoint prepartitions.
-/
def disjUnion (π₁ π₂ : Prepartition I) (h : Disjoint π₁.iUnion π₂.iUnion) : Prepartition I where
  boxes := π₁.boxes ∪ π₂.boxes
  le_of_mem' _ hJ := (Finset.mem_union.1 hJ).elim π₁.le_of_mem π₂.le_of_mem
  pairwiseDisjoint :=
    suffices ∀ J₁ ∈ π₁, ∀ J₂ ∈ π₂, J₁ ≠ J₂ → Disjoint (J₁ : Set (ι → ℝ)) J₂ by
      simpa [pairwise_union_of_symm, pairwiseDisjoint]
    fun _ h₁ _ h₂ _ => h.mono (π₁.subset_iUnion h₁) (π₂.subset_iUnion h₂)

@[simp]
/-
**BoxIntegral.Prepartition.mem_disjUnion** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.
Prepartition`。
形式化陈述：mem_disjUnion (H : Disjoint π₁.iUnion π₂.iUnion) : J in π₁.disjUnion π₂ H 
↔ J in π₁ ∨ J in π₂
参数：H : Disjoint π₁.iUnion π₂.iUnion。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.mem_union`：mem_union : a in s union t ↔ a in s ∨ a in t
-/
theorem mem_disjUnion (H : Disjoint π₁.iUnion π₂.iUnion) :
    J ∈ π₁.disjUnion π₂ H ↔ J ∈ π₁ ∨ J ∈ π₂ := by
  classical exact Finset.mem_union

@[simp]
/-
**BoxIntegral.Prepartition.iUnion_disjUnion** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegr
al.Prepartition`。
形式化陈述：iUnion_disjUnion (h : Disjoint π₁.iUnion π₂.iUnion) : (π₁.disjUnion π₂ h).
iUnion = π₁.iUnion union π₂.iUnion
参数：h : Disjoint π₁.iUnion π₂.iUnion。
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
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.iUnion_or`：iUnion_or {p q : Prop} (s : p ∨ q -> Set α) : ⋃ h, s h = 
(⋃ i, s (Or.inl i)) union ⋃ j, s (Or.inr j)
· 使用定理 `Set.iUnion_union_distrib`：iUnion_union_distrib (s : ι -> Set β) (t : ι -
> Set β) : ⋃ i, s i union t i = (⋃ i, s i) union ⋃ i, t i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iUnion_disjUnion (h : Disjoint π₁.iUnion π₂.iUnion) :
    (π₁.disjUnion π₂ h).iUnion = π₁.iUnion ∪ π₂.iUnion := by
  simp [disjUnion, Prepartition.iUnion, iUnion_or, iUnion_union_distrib]

open scoped Classical in
@[simp]
/-
**BoxIntegral.Prepartition.sum_disj_union_boxes** 是 Mathlib 中的一个定理，位于命名空间 `BoxIn
tegral.Prepartition`。
形式化陈述：sum_disj_union_boxes {M : Type*} [AddCommMonoid M] (h : Disjoint π₁.iUnion
 π₂.iUnion) (f : Box ι -> M) : ∑ J in π₁.boxes union π₂.boxes, f J = (∑ J in π₁.
boxes, f J) + ∑ J in π₂.boxes, f J
参数：h : Disjoint π₁.iUnion π₂.iUnion；f : Box ι -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sum_union`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   Disjoint s₁ s₂ → ∑
 x ∈ s…
· 使用定理 `BoxIntegral.Prepartition.disjoint_boxes_of_disjoint_iUnion`：disjoint_box
es_of_disjoint_iUnion (h : Disjoint π₁.iUnion π₂.iUnion) : Disjoint π₁.boxes π₂.
boxes
-/
theorem sum_disj_union_boxes {M : Type*} [AddCommMonoid M] (h : Disjoint π₁.iUnion π₂.iUnion)
    (f : Box ι → M) :
    ∑ J ∈ π₁.boxes ∪ π₂.boxes, f J = (∑ J ∈ π₁.boxes, f J) + ∑ J ∈ π₂.boxes, f J :=
  sum_union <| disjoint_boxes_of_disjoint_iUnion h

section Distortion

variable [Fintype ι]

/-- The distortion of a prepartition is the maximum of the distortions of the boxes of this
prepartition. -/
/-
**BoxIntegral.Prepartition.distortion** 是 Mathlib 中的一个定义，位于命名空间 `BoxIntegral.Pre
partition`。
形式化陈述：distortion : Real>=0
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The distortion of a prepartition is the maximum of the distortions of the boxes 
of this
prepartition.
-/
def distortion : ℝ≥0 :=
  π.boxes.sup Box.distortion
/-
**BoxIntegral.Prepartition.distortion_le_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `BoxIn
tegral.Prepartition`。
形式化陈述：distortion_le_of_mem (h : J in π) : J.distortion <= π.distortion
参数：h : J in π。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.le_sup`：le_sup {b : β} (hb : b in s) : f b <= s.sup f
-/
theorem distortion_le_of_mem (h : J ∈ π) : J.distortion ≤ π.distortion :=
  le_sup h
/-
**BoxIntegral.Prepartition.distortion_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `BoxInteg
ral.Prepartition`。
形式化陈述：distortion_le_iff {c : Real>=0} : π.distortion <= c ↔ forall J in π, Box.d
istortion J <= c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sup_le_iff`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSu
p α] [inst_1 : OrderBot α] {s : Finset β} {f : β → α} {a : α},   s.sup f ≤ a ↔ ∀
 b ∈ s,…
-/
theorem distortion_le_iff {c : ℝ≥0} : π.distortion ≤ c ↔ ∀ J ∈ π, Box.distortion J ≤ c :=
  Finset.sup_le_iff
/-
**BoxIntegral.Prepartition.distortion_biUnion** 是 Mathlib 中的一个定理，位于命名空间 `BoxInte
gral.Prepartition`。
形式化陈述：distortion_biUnion (π : Prepartition I) (πi : forall J, Prepartition J) : 
(π.biUnion πi).distortion = π.boxes.sup fun J => (πi J).distortion
参数：π : Prepartition I；πi : forall J, Prepartition J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sup_biUnion`：sup_biUnion [DecidableEq β] (s : Finset γ) (t : γ ->
 Finset β) : (s.biUnion t).sup f = s.sup fun x => (t x).sup f
-/
theorem distortion_biUnion (π : Prepartition I) (πi : ∀ J, Prepartition J) :
    (π.biUnion πi).distortion = π.boxes.sup fun J => (πi J).distortion := by
  classical exact sup_biUnion _ _

@[simp]
/-
**BoxIntegral.Prepartition.distortion_disjUnion** 是 Mathlib 中的一个定理，位于命名空间 `BoxIn
tegral.Prepartition`。
形式化陈述：distortion_disjUnion (h : Disjoint π₁.iUnion π₂.iUnion) : (π₁.disjUnion π₂
 h).distortion = max π₁.distortion π₂.distortion
参数：h : Disjoint π₁.iUnion π₂.iUnion。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sup_union`：sup_union [DecidableEq β] : (s₁ union s₂).sup f = s₁.s
up f ⊔ s₂.sup f
-/
theorem distortion_disjUnion (h : Disjoint π₁.iUnion π₂.iUnion) :
    (π₁.disjUnion π₂ h).distortion = max π₁.distortion π₂.distortion := by
  classical exact sup_union
/-
**BoxIntegral.Prepartition.distortion_of_const** 是 Mathlib 中的一个定理，位于命名空间 `BoxInt
egral.Prepartition`。
形式化陈述：distortion_of_const {c} (h₁ : π.boxes.Nonempty) (h₂ : forall J in π, Box.d
istortion J = c) : π.distortion = c
参数：h₁ : π.boxes.Nonempty；h₂ : forall J in π, Box.distortion J = c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sup_congr`：sup_congr {f g : β -> α} (hs : s₁ = s₂) (hfg : forall 
a in s₂, f a = g a) : s₁.sup f = s₂.sup g
· 使用定理 `Finset.sup_const`：sup_const {s : Finset β} (h : s.Nonempty) (c : α) : (s
.sup fun _ => c) = c
-/
theorem distortion_of_const {c} (h₁ : π.boxes.Nonempty) (h₂ : ∀ J ∈ π, Box.distortion J = c) :
    π.distortion = c :=
  (sup_congr rfl h₂).trans (sup_const h₁ _)

@[simp]
/-
**BoxIntegral.Prepartition.distortion_top** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral
.Prepartition`。
形式化陈述：distortion_top (I : Box ι) : distortion (⊤ : Prepartition I) = I.distortio
n
参数：I : Box ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sup_singleton`：sup_singleton {b : β} : ({b} : Finset β).sup f = f
 b
-/
theorem distortion_top (I : Box ι) : distortion (⊤ : Prepartition I) = I.distortion :=
  sup_singleton

@[simp]
/-
**BoxIntegral.Prepartition.distortion_bot** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral
.Prepartition`。
形式化陈述：distortion_bot (I : Box ι) : distortion (⊥ : Prepartition I) = 0
参数：I : Box ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sup_empty`：sup_empty : (∅ : Finset β).sup f = ⊥
-/
theorem distortion_bot (I : Box ι) : distortion (⊥ : Prepartition I) = 0 :=
  sup_empty

end Distortion

/-- A prepartition `π` of `I` is a partition if the boxes of `π` cover the whole `I`. -/
/-
**BoxIntegral.Prepartition.IsPartition** 是 Mathlib 中的一个定义，位于命名空间 `BoxIntegral.Pr
epartition`。
形式化陈述：IsPartition (π : Prepartition I)
参数：π : Prepartition I。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A prepartition `π` of `I` is a partition if the boxes of `π` cover the whole `I`
.
-/
def IsPartition (π : Prepartition I) :=
  ∀ x ∈ I, ∃ J ∈ π, x ∈ J
/-
**BoxIntegral.Prepartition.isPartition_iff_iUnion_eq** 是 Mathlib 中的一个定理，位于命名空间 `
BoxIntegral.Prepartition`。
形式化陈述：isPartition_iff_iUnion_eq {π : Prepartition I} : π.IsPartition ↔ π.iUnion 
= I
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `BoxIntegral.Prepartition.iUnion_subset`：iUnion_subset : π.iUnion subsete
q I
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isPartition_iff_iUnion_eq {π : Prepartition I} : π.IsPartition ↔ π.iUnion = I := by
  simp_rw [IsPartition, Set.Subset.antisymm_iff, π.iUnion_subset, true_and, Set.subset_def,
    mem_iUnion, Box.mem_coe]

@[simp]
/-
**BoxIntegral.Prepartition.isPartition_single_iff** 是 Mathlib 中的一个定理，位于命名空间 `Box
Integral.Prepartition`。
形式化陈述：isPartition_single_iff (h : J <= I) : IsPartition (single I J h) ↔ J = I
参数：h : J <= I。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `BoxIntegral.Prepartition.iUnion_single`：iUnion_single (h : J <= I) : (si
ngle I J h).iUnion = J
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isPartition_single_iff (h : J ≤ I) : IsPartition (single I J h) ↔ J = I := by
  simp [isPartition_iff_iUnion_eq]
/-
**BoxIntegral.Prepartition.isPartitionTop** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral
.Prepartition`。
形式化陈述：isPartitionTop (I : Box ι) : IsPartition (⊤ : Prepartition I)
参数：I : Box ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `BoxIntegral.Prepartition.mem_top`：mem_top : J in (⊤ : Prepartition I) ↔ 
J = I
-/
theorem isPartitionTop (I : Box ι) : IsPartition (⊤ : Prepartition I) :=
  fun _ hx => ⟨I, mem_top.2 rfl, hx⟩

namespace IsPartition

variable {π}

/-
**BoxIntegral.Prepartition.IsPartition.iUnion_eq** 是 Mathlib 中的一个定理，位于命名空间 `BoxI
ntegral.Prepartition.IsPartition`。
形式化陈述：iUnion_eq (h : π.IsPartition) : π.iUnion = I
参数：h : π.IsPartition。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `BoxIntegral.Prepartition.isPartition_iff_iUnion_eq`：isPartition_iff_iUni
on_eq {π : Prepartition I} : π.IsPartition ↔ π.iUnion = I
-/
theorem iUnion_eq (h : π.IsPartition) : π.iUnion = I :=
  isPartition_iff_iUnion_eq.1 h
/-
**BoxIntegral.Prepartition.IsPartition.iUnion_subset** 是 Mathlib 中的一个定理，位于命名空间 `
BoxIntegral.Prepartition.IsPartition`。
形式化陈述：iUnion_subset (h : π.IsPartition) (π₁ : Prepartition I) : π₁.iUnion subset
eq π.iUnion
参数：h : π.IsPartition；π₁ : Prepartition I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BoxIntegral.Prepartition.iUnion_subset`：iUnion_subset : π.iUnion subsete
q I
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `BoxIntegral.Prepartition.IsPartition.iUnion_eq`：iUnion_eq (h : π.IsParti
tion) : π.iUnion = I
-/
theorem iUnion_subset (h : π.IsPartition) (π₁ : Prepartition I) : π₁.iUnion ⊆ π.iUnion :=
  h.iUnion_eq.symm ▸ π₁.iUnion_subset
/-
**BoxIntegral.Prepartition.IsPartition.existsUnique** 是 Mathlib 中的一个定理，位于命名空间 `B
oxIntegral.Prepartition.IsPartition`。
形式化陈述：∀ {ι : Type u_1} {I : BoxIntegral.Box ι} {π : BoxIntegral.Prepartition I} 
{x : ι → ℝ},   π.IsPartition → x ∈ I → ∃! J, J ∈ π ∧ x ∈ J
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ExistsUnique.intro`：ExistsUnique.intro {p : α -> Prop} (w : α) (h₁ : p w
) (h₂ : forall y, p y -> y = w) : exists! x, p x
· 使用定理 `BoxIntegral.Prepartition.eq_of_mem_of_mem`：eq_of_mem_of_mem (h₁ : J₁ in 
π) (h₂ : J₂ in π) (hx₁ : x in J₁) (hx₂ : x in J₂) : J₁ = J₂
-/
protected theorem existsUnique (h : π.IsPartition) (hx : x ∈ I) :
    ∃! J ∈ π, x ∈ J := by
  rcases h x hx with ⟨J, h, hx⟩
  exact ExistsUnique.intro J ⟨h, hx⟩ fun J' ⟨h', hx'⟩ => π.eq_of_mem_of_mem h' h hx' hx
/-
**BoxIntegral.Prepartition.IsPartition.nonempty_boxes** 是 Mathlib 中的一个定理，位于命名空间 
`BoxIntegral.Prepartition.IsPartition`。
形式化陈述：nonempty_boxes (h : π.IsPartition) : π.boxes.Nonempty
参数：h : π.IsPartition。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BoxIntegral.Box.upper_mem`：upper_mem : I.upper in I
-/
theorem nonempty_boxes (h : π.IsPartition) : π.boxes.Nonempty :=
  let ⟨J, hJ, _⟩ := h _ I.upper_mem
  ⟨J, hJ⟩
/-
**BoxIntegral.Prepartition.IsPartition.eq_of_boxes_subset** 是 Mathlib 中的一个定理，位于命
名空间 `BoxIntegral.Prepartition.IsPartition`。
形式化陈述：eq_of_boxes_subset (h₁ : π₁.IsPartition) (h₂ : π₁.boxes subseteq π₂.boxes)
 : π₁ = π₂
参数：h₁ : π₁.IsPartition；h₂ : π₁.boxes subseteq π₂.boxes。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BoxIntegral.Prepartition.eq_of_boxes_subset_iUnion_superset`：eq_of_boxes
_subset_iUnion_superset (h₁ : π₁.boxes subseteq π₂.boxes) (h₂ : π₂.iUnion subset
eq π₁.iUnion) : π₁ = π₂
· 使用定理 `BoxIntegral.Prepartition.IsPartition.iUnion_subset`：iUnion_subset (h : π
.IsPartition) (π₁ : Prepartition I) : π₁.iUnion subseteq π.iUnion
-/
theorem eq_of_boxes_subset (h₁ : π₁.IsPartition) (h₂ : π₁.boxes ⊆ π₂.boxes) : π₁ = π₂ :=
  eq_of_boxes_subset_iUnion_superset h₂ <| h₁.iUnion_subset _
/-
**BoxIntegral.Prepartition.IsPartition.le_iff** 是 Mathlib 中的一个定理，位于命名空间 `BoxInte
gral.Prepartition.IsPartition`。
形式化陈述：le_iff (h : π₂.IsPartition) : π₁ <= π₂ ↔ forall J in π₁, forall J' in π₂, 
(J inter J' : Set (ι -> Real)).Nonempty -> J <= J'
参数：h : π₂.IsPartition。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `BoxIntegral.Prepartition.le_iff_nonempty_imp_le_and_iUnion_subset`：le_if
f_nonempty_imp_le_and_iUnion_subset : π₁ <= π₂ ↔ (forall J in π₁, forall J' in π
₂, (J inter J' : Set (ι -> Real)).Nonempty -> J <= J') …
· 使用定理 `and_iff_left`：∀ {b a : Prop}, b → (a ∧ b ↔ a)
· 使用定理 `BoxIntegral.Prepartition.IsPartition.iUnion_subset`：iUnion_subset (h : π
.IsPartition) (π₁ : Prepartition I) : π₁.iUnion subseteq π.iUnion
-/
theorem le_iff (h : π₂.IsPartition) :
    π₁ ≤ π₂ ↔ ∀ J ∈ π₁, ∀ J' ∈ π₂, (J ∩ J' : Set (ι → ℝ)).Nonempty → J ≤ J' :=
  le_iff_nonempty_imp_le_and_iUnion_subset.trans <| and_iff_left <| h.iUnion_subset _
/-
**BoxIntegral.Prepartition.IsPartition.biUnion** 是 Mathlib 中的一个定理，位于命名空间 `BoxInt
egral.Prepartition.IsPartition`。
形式化陈述：∀ {ι : Type u_1} {I : BoxIntegral.Box ι} {π : BoxIntegral.Prepartition I} 
  {πi : (J : BoxIntegral.Box ι) → BoxIntegral.Prepartition J},   π.IsPartition →
 (∀ J ∈ π, (πi J).IsPartition) → (π.biUnion πi).IsPartition
参数：J : BoxIntegral.Box ι；∀ J ∈ π, (πi J).IsPartition；π.biUnion πi。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `BoxIntegral.Prepartition.mem_biUnion`：mem_biUnion : J in π.biUnion πi ↔ 
exists J' in π, J in πi J'
-/
protected theorem biUnion (h : IsPartition π) (hi : ∀ J ∈ π, IsPartition (πi J)) :
    IsPartition (π.biUnion πi) := fun x hx =>
  let ⟨J, hJ, hxi⟩ := h x hx
  let ⟨Ji, hJi, hx⟩ := hi J hJ x hxi
  ⟨Ji, π.mem_biUnion.2 ⟨J, hJ, hJi⟩, hx⟩
/-
**BoxIntegral.Prepartition.IsPartition.restrict** 是 Mathlib 中的一个定理，位于命名空间 `BoxIn
tegral.Prepartition.IsPartition`。
形式化陈述：∀ {ι : Type u_1} {I J : BoxIntegral.Box ι} {π : BoxIntegral.Prepartition I
},   π.IsPartition → J ≤ I → (π.restrict J).IsPartition
参数：π.restrict J。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `BoxIntegral.Prepartition.isPartition_iff_iUnion_eq`：isPartition_iff_iUni
on_eq {π : Prepartition I} : π.IsPartition ↔ π.iUnion = I
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `BoxIntegral.Prepartition.iUnion_restrict`：iUnion_restrict : (π.restrict 
J).iUnion = (J : Set (ι -> Real)) inter (π.iUnion)
· 使用定理 `BoxIntegral.Prepartition.IsPartition.iUnion_eq`：iUnion_eq (h : π.IsParti
tion) : π.iUnion = I
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
protected theorem restrict (h : IsPartition π) (hJ : J ≤ I) : IsPartition (π.restrict J) :=
  isPartition_iff_iUnion_eq.2 <| by simp [h.iUnion_eq, hJ]
/-
**BoxIntegral.Prepartition.IsPartition.inf** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegra
l.Prepartition.IsPartition`。
形式化陈述：∀ {ι : Type u_1} {I : BoxIntegral.Box ι} {π₁ π₂ : BoxIntegral.Prepartition
 I},   π₁.IsPartition → π₂.IsPartition → (π₁ ⊓ π₂).IsPartition
参数：π₁ ⊓ π₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `BoxIntegral.Prepartition.isPartition_iff_iUnion_eq`：isPartition_iff_iUni
on_eq {π : Prepartition I} : π.IsPartition ↔ π.iUnion = I
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `BoxIntegral.Prepartition.iUnion_inf`：iUnion_inf (π₁ π₂ : Prepartition I)
 : (π₁ ⊓ π₂).iUnion = π₁.iUnion inter π₂.iUnion
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `BoxIntegral.Prepartition.IsPartition.iUnion_eq`：iUnion_eq (h : π.IsParti
tion) : π.iUnion = I
· 使用定理 `Set.inter_self`：inter_self (a : Set α) : a inter a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem inf (h₁ : IsPartition π₁) (h₂ : IsPartition π₂) : IsPartition (π₁ ⊓ π₂) :=
  isPartition_iff_iUnion_eq.2 <| by simp [h₁.iUnion_eq, h₂.iUnion_eq]

end IsPartition

/-
**BoxIntegral.Prepartition.iUnion_biUnion_partition** 是 Mathlib 中的一个定理，位于命名空间 `B
oxIntegral.Prepartition`。
形式化陈述：iUnion_biUnion_partition (h : forall J in π, (πi J).IsPartition) : (π.biUn
ion πi).iUnion = π.iUnion
参数：h : forall J in π, (πi J).IsPartition。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `BoxIntegral.Prepartition.iUnion_biUnion`：iUnion_biUnion (πi : forall J :
 Box ι, Prepartition J) : (π.biUnion πi).iUnion = ⋃ J in π, (πi J).iUnion
· 使用定理 `Set.iUnion_congr_of_surjective`：iUnion_congr_of_surjective {f : ι -> Set
 α} {g : ι₂ -> Set α} (h : ι -> ι₂) (h1 : Surjective h) (h2 : forall x, g (h x) 
= f x) : ⋃ x, f x = …
· 使用定理 `Function.surjective_id`：∀ {α : Sort u_1}, Function.Surjective id
· 使用定理 `BoxIntegral.Prepartition.IsPartition.iUnion_eq`：iUnion_eq (h : π.IsParti
tion) : π.iUnion = I
-/
theorem iUnion_biUnion_partition (h : ∀ J ∈ π, (πi J).IsPartition) :
    (π.biUnion πi).iUnion = π.iUnion :=
  (iUnion_biUnion _ _).trans <|
    iUnion_congr_of_surjective id surjective_id fun J =>
      iUnion_congr_of_surjective id surjective_id fun hJ => (h J hJ).iUnion_eq
/-
**BoxIntegral.Prepartition.isPartitionDisjUnionOfEqDiff** 是 Mathlib 中的一个定理，位于命名空
间 `BoxIntegral.Prepartition`。
形式化陈述：isPartitionDisjUnionOfEqDiff (h : π₂.iUnion = ↑I \ π₁.iUnion) : IsPartitio
n (π₁.disjUnion π₂ <| h.symm ▸ disjoint_sdiff_self_right)
参数：h : π₂.iUnion = ↑I \ π₁.iUnion。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `disjoint_sdiff_self_right`：disjoint_sdiff_self_right : Disjoint x (y \ x
)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `BoxIntegral.Prepartition.isPartition_iff_iUnion_eq`：isPartition_iff_iUni
on_eq {π : Prepartition I} : π.IsPartition ↔ π.iUnion = I
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `BoxIntegral.Prepartition.iUnion_disjUnion`：iUnion_disjUnion (h : Disjoin
t π₁.iUnion π₂.iUnion) : (π₁.disjUnion π₂ h).iUnion = π₁.iUnion union π₂.iUnion
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.union_sdiff_self`：union_sdiff_self {s t : Set α} : s union t \ s = s
 union t
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `BoxIntegral.Prepartition.iUnion_subset`：iUnion_subset : π.iUnion subsete
q I
-/
theorem isPartitionDisjUnionOfEqDiff (h : π₂.iUnion = ↑I \ π₁.iUnion) :
    IsPartition (π₁.disjUnion π₂ <| h.symm ▸ disjoint_sdiff_self_right) :=
  isPartition_iff_iUnion_eq.2 <| (iUnion_disjUnion _).trans <| by simp [h, π₁.iUnion_subset]

end Prepartition

end BoxIntegral

