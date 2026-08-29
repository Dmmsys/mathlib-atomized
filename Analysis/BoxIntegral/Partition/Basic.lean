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

/--
Definition of `Prepartition` / `Prepartition` 的定义

English:
structure Prepartition
  parameters: (I : Box ι)
  axioms and operations (3):
    - boxes : Finset (Box ι)
    - le_of_mem' : forall J in boxes, J <= I
    - pairwiseDisjoint : Set.Pairwise (↑boxes) (Disjoint on ((↑) : Box ι -> Set (ι -> Real)))

中文:
结构 预分拆
  参数: (I : Box ι)
  公理与运算 (3 个):
    - boxes : 有限集 (Box ι)
    - le_of_mem' : 对任意 J in boxes, J <= I
    - pairwiseDisjoint : 集合.两两 (↑boxes) (Disjoint on ((↑) : Box ι -> 集合 (ι -> 实数)))
-/
structure Prepartition (I : Box ι) where
  /-- The underlying set of boxes -/
  boxes : Finset (Box ι)
  /-- Each box is a sub-box of `I` -/
  le_of_mem' : forall J in boxes, J <= I
  /-- The boxes in a prepartition are pairwise disjoint. -/
  pairwiseDisjoint : Set.Pairwise (↑boxes) (Disjoint on ((↑) : Box ι -> Set (ι -> Real)))

namespace Prepartition

variable {I J J₁ J₂ : Box ι} (π : Prepartition I) {π₁ π₂ : Prepartition I} {x : ι -> Real}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Membership (Box ι) (Prepartition I)
  body: ⟨fun π J => J in π.boxes⟩

@[simp]

中文:
实例 :
  签名: Membership (Box ι) (预分拆 I)
  定义体: ⟨fun π J => J in π.boxes⟩

@[simp]
-/
instance : Membership (Box ι) (Prepartition I) :=
  ⟨fun π J => J in π.boxes⟩

@[simp]
/--
theorem `mem_boxes` / 定理 `mem_boxes`

English:
theorem mem_boxes
  statement: J in π.boxes ↔ J in π
  proof: Iff.rfl

@[simp]

中文:
定理 mem_boxes
  结论: J in π.boxes ↔ J in π
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem mem_boxes : J in π.boxes ↔ J in π := Iff.rfl

@[simp]
/--
theorem `mem_mk` / 定理 `mem_mk`

English:
theorem mem_mk
  given: {s h₁ h₂}
  statement: J in (mk s h₁ h₂ : Prepartition I) ↔ J in s
  proof: Iff.rfl

中文:
定理 mem_mk
  条件: {s h₁ h₂}
  结论: J in (mk s h₁ h₂ : 预分拆 I) ↔ J in s
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_mk {s h₁ h₂} : J in (mk s h₁ h₂ : Prepartition I) ↔ J in s := Iff.rfl

/--
theorem `disjoint_coe_of_mem` / 定理 `disjoint_coe_of_mem`

English:
theorem disjoint_coe_of_mem
  given: (h₁ : J₁ in π) (h₂ : J₂ in π) (h : J₁ != J₂)
  proof: π.pairwiseDisjoint h₁ h₂ h

中文:
定理 disjoint_coe_of_mem
  条件: (h₁ : J₁ in π) (h₂ : J₂ in π) (h : J₁ != J₂)
  证明: π.pairwiseDisjoint h₁ h₂ h

Depends on / 依赖: pairwiseDisjoint
-/
theorem disjoint_coe_of_mem (h₁ : J₁ in π) (h₂ : J₂ in π) (h : J₁ != J₂) :
    Disjoint (J₁ : Set (ι -> Real)) J₂ :=
  π.pairwiseDisjoint h₁ h₂ h

/--
theorem `eq_of_mem_of_mem` / 定理 `eq_of_mem_of_mem`

English:
theorem eq_of_mem_of_mem
  given: (h₁ : J₁ in π) (h₂ : J₂ in π) (hx₁ : x in J₁) (hx₂ : x in J₂)
  statement: J₁ = J₂
  proof: by_contra fun H => (π.disjoint_coe_of_mem h₁ h₂ H).le_bot ⟨hx₁, hx₂⟩

中文:
定理 eq_of_mem_of_mem
  条件: (h₁ : J₁ in π) (h₂ : J₂ in π) (hx₁ : x in J₁) (hx₂ : x in J₂)
  结论: J₁ = J₂
  证明: by_contra fun H => (π.disjoint_coe_of_mem h₁ h₂ H).le_bot ⟨hx₁, hx₂⟩

Depends on / 依赖: disjoint_coe_of_mem, le_bot
-/
theorem eq_of_mem_of_mem (h₁ : J₁ in π) (h₂ : J₂ in π) (hx₁ : x in J₁) (hx₂ : x in J₂) : J₁ = J₂ :=
  by_contra fun H => (π.disjoint_coe_of_mem h₁ h₂ H).le_bot ⟨hx₁, hx₂⟩

/--
theorem `eq_of_le_of_le` / 定理 `eq_of_le_of_le`

English:
theorem eq_of_le_of_le
  given: (h₁ : J₁ in π) (h₂ : J₂ in π) (hle₁ : J <= J₁) (hle₂ : J <= J₂)
  statement: J₁ = J₂
  proof: π.eq_of_mem_of_mem h₁ h₂ (hle₁ J.upper_mem) (hle₂ J.upper_mem)

中文:
定理 eq_of_le_of_le
  条件: (h₁ : J₁ in π) (h₂ : J₂ in π) (hle₁ : J <= J₁) (hle₂ : J <= J₂)
  结论: J₁ = J₂
  证明: π.eq_of_mem_of_mem h₁ h₂ (hle₁ J.upper_mem) (hle₂ J.upper_mem)

Depends on / 依赖: J.upper_mem, eq_of_mem_of_mem, upper_mem
-/
theorem eq_of_le_of_le (h₁ : J₁ in π) (h₂ : J₂ in π) (hle₁ : J <= J₁) (hle₂ : J <= J₂) : J₁ = J₂ :=
  π.eq_of_mem_of_mem h₁ h₂ (hle₁ J.upper_mem) (hle₂ J.upper_mem)

/--
theorem `eq_of_le` / 定理 `eq_of_le`

English:
theorem eq_of_le
  given: (h₁ : J₁ in π) (h₂ : J₂ in π) (hle : J₁ <= J₂)
  statement: J₁ = J₂
  proof: π.eq_of_le_of_le h₁ h₂ le_rfl hle

中文:
定理 eq_of_le
  条件: (h₁ : J₁ in π) (h₂ : J₂ in π) (hle : J₁ <= J₂)
  结论: J₁ = J₂
  证明: π.eq_of_le_of_le h₁ h₂ le_rfl hle

Depends on / 依赖: eq_of_le_of_le, le_rfl
-/
theorem eq_of_le (h₁ : J₁ in π) (h₂ : J₂ in π) (hle : J₁ <= J₂) : J₁ = J₂ :=
  π.eq_of_le_of_le h₁ h₂ le_rfl hle

/--
theorem `le_of_mem` / 定理 `le_of_mem`

English:
theorem le_of_mem
  given: (hJ : J in π)
  statement: J <= I
  proof: π.le_of_mem' J hJ

中文:
定理 le_of_mem
  条件: (hJ : J in π)
  结论: J <= I
  证明: π.le_of_mem' J hJ

Depends on / 依赖: le_of_mem
-/
theorem le_of_mem (hJ : J in π) : J <= I :=
  π.le_of_mem' J hJ

/--
theorem `lower_le_lower` / 定理 `lower_le_lower`

English:
theorem lower_le_lower
  given: (hJ : J in π)
  statement: I.lower <= J.lower
  proof: Box.antitone_lower (π.le_of_mem hJ)

中文:
定理 lower_le_lower
  条件: (hJ : J in π)
  结论: I.lower <= J.lower
  证明: Box.antitone_lower (π.le_of_mem hJ)

Depends on / 依赖: Box.antitone_lower, antitone_lower, le_of_mem
-/
theorem lower_le_lower (hJ : J in π) : I.lower <= J.lower :=
  Box.antitone_lower (π.le_of_mem hJ)

/--
theorem `upper_le_upper` / 定理 `upper_le_upper`

English:
theorem upper_le_upper
  given: (hJ : J in π)
  statement: J.upper <= I.upper
  proof: Box.monotone_upper (π.le_of_mem hJ)

中文:
定理 upper_le_upper
  条件: (hJ : J in π)
  结论: J.upper <= I.upper
  证明: Box.monotone_upper (π.le_of_mem hJ)

Depends on / 依赖: Box.monotone_upper, le_of_mem, monotone_upper
-/
theorem upper_le_upper (hJ : J in π) : J.upper <= I.upper :=
  Box.monotone_upper (π.le_of_mem hJ)

/--
theorem `injective_boxes` / 定理 `injective_boxes`

English:
theorem injective_boxes
  statement: Function.Injective (boxes : Prepartition I -> Finset (Box ι))
  proof: by
  rintro ⟨s₁, h₁, h₁'⟩ ⟨s₂, h₂, h₂'⟩ (rfl : s₁ = s₂)
  rfl

@[ext]

中文:
定理 injective_boxes
  结论: 函数.单射 (boxes : 预分拆 I -> 有限集 (Box ι))
  证明: by
  rintro ⟨s₁, h₁, h₁'⟩ ⟨s₂, h₂, h₂'⟩ (rfl : s₁ = s₂)
  rfl

@[ext]
-/
theorem injective_boxes : Function.Injective (boxes : Prepartition I -> Finset (Box ι)) := by
  rintro ⟨s₁, h₁, h₁'⟩ ⟨s₂, h₂, h₂'⟩ (rfl : s₁ = s₂)
  rfl

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: (h : forall J, J in π₁ ↔ J in π₂)
  statement: π₁ = π₂
  proof: injective_boxes Finset.ext h

中文:
定理 ext
  条件: (h : 对任意 J, J in π₁ ↔ J in π₂)
  结论: π₁ = π₂
  证明: injective_boxes Finset.ext h

Depends on / 依赖: Finset, Finset.ext, injective_boxes
-/
theorem ext (h : forall J, J in π₁ ↔ J in π₂) : π₁ = π₂ :=
injective_boxes Finset.ext h

/-- The singleton prepartition `{J}`, `J ≤ I`. -/
@[simps]
/--
Definition of `single` / `single` 的定义

English:
definition single
  signature: (I J : Box ι) (h : J <= I)
  body: ⟨{J}, by simpa, by simp⟩

@[simp]

中文:
定义 single
  签名: (I J : Box ι) (h : J <= I)
  定义体: ⟨{J}, by simpa, by simp⟩

@[simp]
-/
def single (I J : Box ι) (h : J <= I) : Prepartition I :=
  ⟨{J}, by simpa, by simp⟩

@[simp]
/--
theorem `mem_single` / 定理 `mem_single`

English:
theorem mem_single
  given: {J'} (h : J <= I)
  statement: J' in single I J h ↔ J' = J
  proof: mem_singleton

中文:
定理 mem_single
  条件: {J'} (h : J <= I)
  结论: J' in single I J h ↔ J' = J
  证明: mem_singleton

Depends on / 依赖: mem_singleton
-/
theorem mem_single {J'} (h : J <= I) : J' in single I J h ↔ J' = J :=
  mem_singleton

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LE (Prepartition I)
  body: ⟨fun π π' => forall ⦃I⦄, I in π -> exists I' in π', I <= I'⟩

中文:
实例 :
  签名: LE (预分拆 I)
  定义体: ⟨fun π π' => forall ⦃I⦄, I in π -> exists I' in π', I <= I'⟩
-/
instance : LE (Prepartition I) :=
  ⟨fun π π' => forall ⦃I⦄, I in π -> exists I' in π', I <= I'⟩

/--
Instance `partialOrder` / 实例 `partialOrder`

English:
instance partialOrder
  signature: : PartialOrder (Prepartition I) where
  body: ⟨I, hI, le_rfl⟩
  le_trans _ _ _ h₁₂ h₂₃ _ hI₁ :=
    let ⟨_, hI₂, hI₁₂⟩ := h₁₂ hI₁
    let ⟨I₃, hI₃, hI₂₃⟩ := h₂₃ hI₂
    ⟨I₃, hI₃, hI₁₂.trans hI₂₃⟩
  le_antisymm := by
    suffices forall {π₁ π₂ : Prepartition I}, π₁ <= π₂ -> π₂ <= π₁ -> π₁.boxes subseteq π₂.boxes from
      fun π₁ π₂ h₁ h₂ => injective_boxes (Subset.antisymm (this h₁ h₂) (this h₂ h₁))
    intro π₁ π₂ h₁ h₂ J hJ
    rcases h₁ hJ with ⟨J', hJ', hle⟩; rcases h₂ hJ' with ⟨J'', hJ'', hle'⟩
    obtain rfl : J = J'' := π₁.eq_of_le hJ hJ'' (hle.trans hle')
    obtain rfl : J' = J := le_antisymm ‹_› ‹_›
    assumption

中文:
实例 partialOrder
  签名: : 偏序 (预分拆 I) where
  定义体: ⟨I, hI, le_rfl⟩
  le_trans _ _ _ h₁₂ h₂₃ _ hI₁ :=
    let ⟨_, hI₂, hI₁₂⟩ := h₁₂ hI₁
    let ⟨I₃, hI₃, hI₂₃⟩ := h₂₃ hI₂
    ⟨I₃, hI₃, hI₁₂.trans hI₂₃⟩
  le_antisymm := by
    suffices forall {π₁ π₂ : Prepartition I}, π₁ <= π₂ -> π₂ <= π₁ -> π₁.boxes subseteq π₂.boxes from
      fun π₁ π₂ h₁ h₂ => injective_boxes (Subset.antisymm (this h₁ h₂) (this h₂ h₁))
    intro π₁ π₂ h₁ h₂ J hJ
    rcases h₁ hJ with ⟨J', hJ', hle⟩; rcases h₂ hJ' with ⟨J'', hJ'', hle'⟩
    obtain rfl : J = J'' := π₁.eq_of_le hJ hJ'' (hle.trans hle')
    obtain rfl : J' = J := le_antisymm ‹_› ‹_›
    assumption

Depends on / 依赖: le_rfl
-/
instance partialOrder : PartialOrder (Prepartition I) where
  le_refl _ I hI := ⟨I, hI, le_rfl⟩
  le_trans _ _ _ h₁₂ h₂₃ _ hI₁ :=
    let ⟨_, hI₂, hI₁₂⟩ := h₁₂ hI₁
    let ⟨I₃, hI₃, hI₂₃⟩ := h₂₃ hI₂
    ⟨I₃, hI₃, hI₁₂.trans hI₂₃⟩
  le_antisymm := by
    suffices forall {π₁ π₂ : Prepartition I}, π₁ <= π₂ -> π₂ <= π₁ -> π₁.boxes subseteq π₂.boxes from
      fun π₁ π₂ h₁ h₂ => injective_boxes (Subset.antisymm (this h₁ h₂) (this h₂ h₁))
    intro π₁ π₂ h₁ h₂ J hJ
    rcases h₁ hJ with ⟨J', hJ', hle⟩; rcases h₂ hJ' with ⟨J'', hJ'', hle'⟩
    obtain rfl : J = J'' := π₁.eq_of_le hJ hJ'' (hle.trans hle')
    obtain rfl : J' = J := le_antisymm ‹_› ‹_›
    assumption

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: OrderTop (Prepartition I)
  body: single I I le_rfl
  le_top π _ hJ := ⟨I, by simp, π.le_of_mem hJ⟩

中文:
实例 :
  签名: 有顶序 (预分拆 I)
  定义体: single I I le_rfl
  le_top π _ hJ := ⟨I, by simp, π.le_of_mem hJ⟩

Depends on / 依赖: le_rfl, single
-/
instance : OrderTop (Prepartition I) where
  top := single I I le_rfl
  le_top π _ hJ := ⟨I, by simp, π.le_of_mem hJ⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: OrderBot (Prepartition I)
  body: ⟨∅,
    fun _ hJ => (Finset.notMem_empty _ hJ).elim,
    fun _ hJ => (Set.notMem_empty _ <| Finset.coe_empty ▸ hJ).elim⟩
  bot_le _ _ hJ := (Finset.notMem_empty _ hJ).elim

中文:
实例 :
  签名: 有底序 (预分拆 I)
  定义体: ⟨∅,
    fun _ hJ => (Finset.notMem_empty _ hJ).elim,
    fun _ hJ => (Set.notMem_empty _ <| Finset.coe_empty ▸ hJ).elim⟩
  bot_le _ _ hJ := (Finset.notMem_empty _ hJ).elim
-/
instance : OrderBot (Prepartition I) where
  bot := ⟨∅,
    fun _ hJ => (Finset.notMem_empty _ hJ).elim,
    fun _ hJ => (Set.notMem_empty _ <| Finset.coe_empty ▸ hJ).elim⟩
  bot_le _ _ hJ := (Finset.notMem_empty _ hJ).elim

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (Prepartition I)
  body: ⟨⊤⟩

中文:
实例 :
  签名: 可居 (预分拆 I)
  定义体: ⟨⊤⟩
-/
instance : Inhabited (Prepartition I) := ⟨⊤⟩

/--
theorem `le_def` / 定理 `le_def`

English:
theorem le_def
  statement: π₁ <= π₂ ↔ forall J in π₁, exists J' in π₂, J <= J'
  proof: Iff.rfl

@[simp]

中文:
定理 le_def
  结论: π₁ <= π₂ ↔ 对任意 J in π₁, 存在 J' in π₂, J <= J'
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem le_def : π₁ <= π₂ ↔ forall J in π₁, exists J' in π₂, J <= J' := Iff.rfl

@[simp]
/--
theorem `mem_top` / 定理 `mem_top`

English:
theorem mem_top
  statement: J in (⊤ : Prepartition I) ↔ J = I
  proof: mem_singleton

@[simp]

中文:
定理 mem_top
  结论: J in (⊤ : 预分拆 I) ↔ J = I
  证明: mem_singleton

@[simp]

Depends on / 依赖: mem_singleton
-/
theorem mem_top : J in (⊤ : Prepartition I) ↔ J = I :=
  mem_singleton

@[simp]
/--
theorem `top_boxes` / 定理 `top_boxes`

English:
theorem top_boxes
  statement: (⊤ : Prepartition I).boxes = {I}
  proof: rfl

@[simp]

中文:
定理 top_boxes
  结论: (⊤ : 预分拆 I).boxes = {I}
  证明: rfl

@[simp]
-/
theorem top_boxes : (⊤ : Prepartition I).boxes = {I} := rfl

@[simp]
/--
theorem `notMem_bot` / 定理 `notMem_bot`

English:
theorem notMem_bot
  statement: J ∉ (⊥ : Prepartition I)
  proof: Finset.notMem_empty _

@[simp]

中文:
定理 notMem_bot
  结论: J ∉ (⊥ : 预分拆 I)
  证明: Finset.notMem_empty _

@[simp]

Depends on / 依赖: Finset, Finset.notMem_empty, notMem_empty
-/
theorem notMem_bot : J ∉ (⊥ : Prepartition I) :=
  Finset.notMem_empty _

@[simp]
/--
theorem `bot_boxes` / 定理 `bot_boxes`

English:
theorem bot_boxes
  statement: (⊥ : Prepartition I).boxes = ∅
  proof: rfl

中文:
定理 bot_boxes
  结论: (⊥ : 预分拆 I).boxes = ∅
  证明: rfl
-/
theorem bot_boxes : (⊥ : Prepartition I).boxes = ∅ := rfl

/--
theorem `injOn_setOfPred_mem_Icc_setOfPred_lower_eq` / 定理 `injOn_setOfPred_mem_Icc_setOfPred_lower_eq`

English:
theorem injOn_setOfPred_mem_Icc_setOfPred_lower_eq
  given: (x : ι -> Real)
  proof: by
  rintro J₁ ⟨h₁, hx₁⟩ J₂ ⟨h₂, hx₂⟩ (H : { i | J₁.lower i = x i } = { i | J₂.lower i = x i })
  suffices forall i, (Ioc (J₁.lower i) (J₁.upper i) inter Ioc (J₂.lower i) (J₂.upper i)).Nonempty by
    choose y hy₁ hy₂ using this
    exact π.eq_of_mem_of_mem h₁ h₂ hy₁ hy₂
  intro i
  simp only [Set.ext_iff, mem_ofPred] at H
  rcases (hx₁.1 i).eq_or_lt with hi₁ | hi₁
  · have hi₂ : J₂.lower i = x i := (H _).1 hi₁
    have H₁ : x i < J₁.upper i := by simpa only [hi₁] using J₁.lower_lt_upper i
    have H₂ : x i < J₂.upper i := by simpa only [hi₂] using J₂.lower_lt_upper i
    rw [Set.Ioc_inter_Ioc]; rw [hi₁]; rw [hi₂]; rw [sup_idem]; rw [Set.nonempty_Ioc]
    exact lt_min H₁ H₂
  · have hi₂ : J₂.lower i < x i := (hx₂.1 i).lt_of_ne (mt (H _).2 hi₁.ne)
    exact ⟨x i, ⟨hi₁, hx₁.2 i⟩, ⟨hi₂, hx₂.2 i⟩⟩

@[deprecated (since := "2026-07-09")]
alias injOn_setOf_mem_Icc_setOf_lower_eq := injOn_setOfPred_mem_Icc_setOfPred_lower_eq

中文:
定理 injOn_setOfPred_mem_Icc_setOfPred_lower_eq
  条件: (x : ι -> 实数)
  证明: by
  rintro J₁ ⟨h₁, hx₁⟩ J₂ ⟨h₂, hx₂⟩ (H : { i | J₁.lower i = x i } = { i | J₂.lower i = x i })
  suffices forall i, (Ioc (J₁.lower i) (J₁.upper i) inter Ioc (J₂.lower i) (J₂.upper i)).Nonempty by
    choose y hy₁ hy₂ using this
    exact π.eq_of_mem_of_mem h₁ h₂ hy₁ hy₂
  intro i
  simp only [Set.ext_iff, mem_ofPred] at H
  rcases (hx₁.1 i).eq_or_lt with hi₁ | hi₁
  · have hi₂ : J₂.lower i = x i := (H _).1 hi₁
    have H₁ : x i < J₁.upper i := by simpa only [hi₁] using J₁.lower_lt_upper i
    have H₂ : x i < J₂.upper i := by simpa only [hi₂] using J₂.lower_lt_upper i
    rw [Set.Ioc_inter_Ioc]; rw [hi₁]; rw [hi₂]; rw [sup_idem]; rw [Set.nonempty_Ioc]
    exact lt_min H₁ H₂
  · have hi₂ : J₂.lower i < x i := (hx₂.1 i).lt_of_ne (mt (H _).2 hi₁.ne)
    exact ⟨x i, ⟨hi₁, hx₁.2 i⟩, ⟨hi₂, hx₂.2 i⟩⟩

@[deprecated (since := "2026-07-09")]
alias injOn_setOf_mem_Icc_setOf_lower_eq := injOn_setOfPred_mem_Icc_setOfPred_lower_eq

Depends on / 依赖: Nonempty, Set.ext_iff, eq_of_mem_of_mem, eq_or_lt, ext_iff, lower_lt_upper, mem_ofPred
-/
theorem injOn_setOfPred_mem_Icc_setOfPred_lower_eq (x : ι -> Real) :
    InjOn (fun J : Box ι => { i | J.lower i = x i }) { J | J in π ∧ x in Box.Icc J } := by
  rintro J₁ ⟨h₁, hx₁⟩ J₂ ⟨h₂, hx₂⟩ (H : { i | J₁.lower i = x i } = { i | J₂.lower i = x i })
  suffices forall i, (Ioc (J₁.lower i) (J₁.upper i) inter Ioc (J₂.lower i) (J₂.upper i)).Nonempty by
    choose y hy₁ hy₂ using this
    exact π.eq_of_mem_of_mem h₁ h₂ hy₁ hy₂
  intro i
  simp only [Set.ext_iff, mem_ofPred] at H
  rcases (hx₁.1 i).eq_or_lt with hi₁ | hi₁
  · have hi₂ : J₂.lower i = x i := (H _).1 hi₁
    have H₁ : x i < J₁.upper i := by simpa only [hi₁] using J₁.lower_lt_upper i
    have H₂ : x i < J₂.upper i := by simpa only [hi₂] using J₂.lower_lt_upper i
    rw [Set.Ioc_inter_Ioc]; rw [hi₁]; rw [hi₂]; rw [sup_idem]; rw [Set.nonempty_Ioc]
    exact lt_min H₁ H₂
  · have hi₂ : J₂.lower i < x i := (hx₂.1 i).lt_of_ne (mt (H _).2 hi₁.ne)
    exact ⟨x i, ⟨hi₁, hx₁.2 i⟩, ⟨hi₂, hx₂.2 i⟩⟩

@[deprecated (since := "2026-07-09")]
alias injOn_setOf_mem_Icc_setOf_lower_eq := injOn_setOfPred_mem_Icc_setOfPred_lower_eq

open scoped Classical in
/--
theorem `card_filter_mem_Icc_le` / 定理 `card_filter_mem_Icc_le`

English:
theorem card_filter_mem_Icc_le
  given: [Fintype ι] (x : ι -> Real)
  proof: by
  rw [← Fintype.card_set]
  refine Finset.card_le_card_of_injOn (fun J : Box ι => { i | J.lower i = x i })
    (fun _ _ => Finset.mem_univ _) ?_
  simpa using π.injOn_setOfPred_mem_Icc_setOfPred_lower_eq x

中文:
定理 card_filter_mem_Icc_le
  条件: [有限类型 ι] (x : ι -> 实数)
  证明: by
  rw [← Fintype.card_set]
  refine Finset.card_le_card_of_injOn (fun J : Box ι => { i | J.lower i = x i })
    (fun _ _ => Finset.mem_univ _) ?_
  simpa using π.injOn_setOfPred_mem_Icc_setOfPred_lower_eq x

Depends on / 依赖: Finset, Finset.card_le_card_of_injOn, Finset.mem_univ, Fintype, Fintype.card_set, J.lower, card_le_card_of_injOn, card_set, injOn_setOfPred_mem_Icc_setOfPred_lower_eq, mem_univ
-/
theorem card_filter_mem_Icc_le [Fintype ι] (x : ι -> Real) :
    #{J in π.boxes | x in Box.Icc J} <= 2 ^ Fintype.card ι := by
  rw [← Fintype.card_set]
  refine Finset.card_le_card_of_injOn (fun J : Box ι => { i | J.lower i = x i })
    (fun _ _ => Finset.mem_univ _) ?_
  simpa using π.injOn_setOfPred_mem_Icc_setOfPred_lower_eq x

/--
Definition of `iUnion` / `iUnion` 的定义

English:
definition iUnion
  signature: : Set (ι -> Real)
  body: ⋃ J in π, ↑J

中文:
定义 iUnion
  签名: : 集合 (ι -> 实数)
  定义体: ⋃ J in π, ↑J
-/
protected def iUnion : Set (ι -> Real) :=
  ⋃ J in π, ↑J

/--
theorem `iUnion_def` / 定理 `iUnion_def`

English:
theorem iUnion_def
  statement: π.iUnion = ⋃ J in π, ↑J
  proof: rfl

中文:
定理 iUnion_def
  结论: π.iUnion = ⋃ J in π, ↑J
  证明: rfl
-/
theorem iUnion_def : π.iUnion = ⋃ J in π, ↑J := rfl

/--
theorem `iUnion_def'` / 定理 `iUnion_def'`

English:
theorem iUnion_def'
  statement: π.iUnion = ⋃ J in π.boxes, ↑J
  proof: rfl

@[simp]

中文:
定理 iUnion_def'
  结论: π.iUnion = ⋃ J in π.boxes, ↑J
  证明: rfl

@[simp]
-/
theorem iUnion_def' : π.iUnion = ⋃ J in π.boxes, ↑J := rfl

@[simp]
/--
theorem `mem_iUnion` / 定理 `mem_iUnion`

English:
theorem mem_iUnion
  statement: x in π.iUnion ↔ exists J in π, x in J
  proof: by
  convert! Set.mem_iUnion₂
  rw [Box.mem_coe]; rw [exists_prop]

@[simp]

中文:
定理 mem_iUnion
  结论: x in π.iUnion ↔ 存在 J in π, x in J
  证明: by
  convert! Set.mem_iUnion₂
  rw [Box.mem_coe]; rw [exists_prop]

@[simp]

Depends on / 依赖: Box.mem_coe, Set.mem_iUnion, convert, exists_prop, mem_coe
-/
theorem mem_iUnion : x in π.iUnion ↔ exists J in π, x in J := by
  convert! Set.mem_iUnion₂
  rw [Box.mem_coe]; rw [exists_prop]

@[simp]
/--
theorem `iUnion_single` / 定理 `iUnion_single`

English:
theorem iUnion_single
  given: (h : J <= I)
  statement: (single I J h).iUnion = J
  proof: by simp [iUnion_def]

@[simp]

中文:
定理 iUnion_single
  条件: (h : J <= I)
  结论: (single I J h).iUnion = J
  证明: by simp [iUnion_def]

@[simp]

Depends on / 依赖: iUnion_def
-/
theorem iUnion_single (h : J <= I) : (single I J h).iUnion = J := by simp [iUnion_def]

@[simp]
/--
theorem `iUnion_top` / 定理 `iUnion_top`

English:
theorem iUnion_top
  statement: (⊤ : Prepartition I).iUnion = I
  proof: by simp [Prepartition.iUnion]

@[simp]

中文:
定理 iUnion_top
  结论: (⊤ : 预分拆 I).iUnion = I
  证明: by simp [Prepartition.iUnion]

@[simp]

Depends on / 依赖: Prepartition, Prepartition.iUnion, iUnion
-/
theorem iUnion_top : (⊤ : Prepartition I).iUnion = I := by simp [Prepartition.iUnion]

@[simp]
/--
theorem `iUnion_eq_empty` / 定理 `iUnion_eq_empty`

English:
theorem iUnion_eq_empty
  statement: π₁.iUnion = ∅ ↔ π₁ = ⊥
  proof: by
  simp [← injective_boxes.eq_iff, Finset.ext_iff, Prepartition.iUnion, imp_false]

@[simp]

中文:
定理 iUnion_eq_empty
  结论: π₁.iUnion = ∅ ↔ π₁ = ⊥
  证明: by
  simp [← injective_boxes.eq_iff, Finset.ext_iff, Prepartition.iUnion, imp_false]

@[simp]

Depends on / 依赖: Finset, Finset.ext_iff, Prepartition, Prepartition.iUnion, eq_iff, ext_iff, iUnion, imp_false, injective_boxes, injective_boxes.eq_iff
-/
theorem iUnion_eq_empty : π₁.iUnion = ∅ ↔ π₁ = ⊥ := by
  simp [← injective_boxes.eq_iff, Finset.ext_iff, Prepartition.iUnion, imp_false]

@[simp]
/--
theorem `iUnion_bot` / 定理 `iUnion_bot`

English:
theorem iUnion_bot
  statement: (⊥ : Prepartition I).iUnion = ∅
  proof: iUnion_eq_empty.2 rfl

中文:
定理 iUnion_bot
  结论: (⊥ : 预分拆 I).iUnion = ∅
  证明: iUnion_eq_empty.2 rfl

Depends on / 依赖: iUnion_eq_empty
-/
theorem iUnion_bot : (⊥ : Prepartition I).iUnion = ∅ :=
  iUnion_eq_empty.2 rfl

/--
theorem `subset_iUnion` / 定理 `subset_iUnion`

English:
theorem subset_iUnion
  given: (h : J in π)
  statement: ↑J subseteq π.iUnion
  proof: subset_biUnion_of_mem h

中文:
定理 subset_iUnion
  条件: (h : J in π)
  结论: ↑J subseteq π.iUnion
  证明: subset_biUnion_of_mem h

Depends on / 依赖: subset_biUnion_of_mem
-/
theorem subset_iUnion (h : J in π) : ↑J subseteq π.iUnion :=
  subset_biUnion_of_mem h

/--
theorem `iUnion_subset` / 定理 `iUnion_subset`

English:
theorem iUnion_subset
  statement: π.iUnion subseteq I
  proof: iUnion₂_subset π.le_of_mem'

@[gcongr, mono]

中文:
定理 iUnion_subset
  结论: π.iUnion subseteq I
  证明: iUnion₂_subset π.le_of_mem'

@[gcongr, mono]

Depends on / 依赖: le_of_mem
-/
theorem iUnion_subset : π.iUnion subseteq I :=
  iUnion₂_subset π.le_of_mem'

@[gcongr, mono]
/--
theorem `iUnion_mono` / 定理 `iUnion_mono`

English:
theorem iUnion_mono
  given: (h : π₁ <= π₂)
  statement: π₁.iUnion subseteq π₂.iUnion
  proof: fun _ hx =>
  let ⟨_, hJ₁, hx⟩ := π₁.mem_iUnion.1 hx
  let ⟨J₂, hJ₂, hle⟩ := h hJ₁
  π₂.mem_iUnion.2 ⟨J₂, hJ₂, hle hx⟩

中文:
定理 iUnion_mono
  条件: (h : π₁ <= π₂)
  结论: π₁.iUnion subseteq π₂.iUnion
  证明: fun _ hx =>
  let ⟨_, hJ₁, hx⟩ := π₁.mem_iUnion.1 hx
  let ⟨J₂, hJ₂, hle⟩ := h hJ₁
  π₂.mem_iUnion.2 ⟨J₂, hJ₂, hle hx⟩
-/
theorem iUnion_mono (h : π₁ <= π₂) : π₁.iUnion subseteq π₂.iUnion := fun _ hx =>
  let ⟨_, hJ₁, hx⟩ := π₁.mem_iUnion.1 hx
  let ⟨J₂, hJ₂, hle⟩ := h hJ₁
  π₂.mem_iUnion.2 ⟨J₂, hJ₂, hle hx⟩

/--
theorem `disjoint_boxes_of_disjoint_iUnion` / 定理 `disjoint_boxes_of_disjoint_iUnion`

English:
theorem disjoint_boxes_of_disjoint_iUnion
  given: (h : Disjoint π₁.iUnion π₂.iUnion)
  proof: Finset.disjoint_left.2 fun J h₁ h₂ =>
    Disjoint.le_bot (h.mono (π₁.subset_iUnion h₁) (π₂.subset_iUnion h₂)) ⟨J.upper_mem, J.upper_mem⟩

中文:
定理 disjoint_boxes_of_disjoint_iUnion
  条件: (h : Disjoint π₁.iUnion π₂.iUnion)
  证明: Finset.disjoint_left.2 fun J h₁ h₂ =>
    Disjoint.le_bot (h.mono (π₁.subset_iUnion h₁) (π₂.subset_iUnion h₂)) ⟨J.upper_mem, J.upper_mem⟩

Depends on / 依赖: Disjoint, Disjoint.le_bot, Finset, Finset.disjoint_left, J.upper_mem, disjoint_left, h.mono, le_bot, subset_iUnion, upper_mem
-/
theorem disjoint_boxes_of_disjoint_iUnion (h : Disjoint π₁.iUnion π₂.iUnion) :
    Disjoint π₁.boxes π₂.boxes :=
  Finset.disjoint_left.2 fun J h₁ h₂ =>
    Disjoint.le_bot (h.mono (π₁.subset_iUnion h₁) (π₂.subset_iUnion h₂)) ⟨J.upper_mem, J.upper_mem⟩

/--
theorem `le_iff_nonempty_imp_le_and_iUnion_subset` / 定理 `le_iff_nonempty_imp_le_and_iUnion_subset`

English:
theorem le_iff_nonempty_imp_le_and_iUnion_subset
  proof: by
  constructor
  · refine fun H => ⟨fun J hJ J' hJ' Hne => ?_, iUnion_mono H⟩
    rcases H hJ with ⟨J'', hJ'', Hle⟩
    rcases Hne with ⟨x, hx, hx'⟩
    rwa [π₂.eq_of_mem_of_mem hJ' hJ'' hx' (Hle hx)]
  · rintro ⟨H, HU⟩ J hJ
    simp only [Set.subset_def, mem_iUnion] at HU
    rcases HU J.upper ⟨J, hJ, J.upper_mem⟩ with ⟨J₂, hJ₂, hx⟩
    exact ⟨J₂, hJ₂, H _ hJ _ hJ₂ ⟨_, J.upper_mem, hx⟩⟩

中文:
定理 le_iff_nonempty_imp_le_and_iUnion_subset
  证明: by
  constructor
  · refine fun H => ⟨fun J hJ J' hJ' Hne => ?_, iUnion_mono H⟩
    rcases H hJ with ⟨J'', hJ'', Hle⟩
    rcases Hne with ⟨x, hx, hx'⟩
    rwa [π₂.eq_of_mem_of_mem hJ' hJ'' hx' (Hle hx)]
  · rintro ⟨H, HU⟩ J hJ
    simp only [Set.subset_def, mem_iUnion] at HU
    rcases HU J.upper ⟨J, hJ, J.upper_mem⟩ with ⟨J₂, hJ₂, hx⟩
    exact ⟨J₂, hJ₂, H _ hJ _ hJ₂ ⟨_, J.upper_mem, hx⟩⟩

Depends on / 依赖: J.upper, J.upper_mem, Set.subset_def, eq_of_mem_of_mem, iUnion_mono, mem_iUnion, subset_def, upper_mem
-/
theorem le_iff_nonempty_imp_le_and_iUnion_subset :
    π₁ <= π₂ ↔
      (forall J in π₁, forall J' in π₂, (J inter J' : Set (ι -> Real)).Nonempty -> J <= J') ∧ π₁.iUnion subseteq π₂.iUnion := by
  constructor
  · refine fun H => ⟨fun J hJ J' hJ' Hne => ?_, iUnion_mono H⟩
    rcases H hJ with ⟨J'', hJ'', Hle⟩
    rcases Hne with ⟨x, hx, hx'⟩
    rwa [π₂.eq_of_mem_of_mem hJ' hJ'' hx' (Hle hx)]
  · rintro ⟨H, HU⟩ J hJ
    simp only [Set.subset_def, mem_iUnion] at HU
    rcases HU J.upper ⟨J, hJ, J.upper_mem⟩ with ⟨J₂, hJ₂, hx⟩
    exact ⟨J₂, hJ₂, H _ hJ _ hJ₂ ⟨_, J.upper_mem, hx⟩⟩

/--
theorem `eq_of_boxes_subset_iUnion_superset` / 定理 `eq_of_boxes_subset_iUnion_superset`

English:
theorem eq_of_boxes_subset_iUnion_superset
  given: (h₁ : π₁.boxes subseteq π₂.boxes) (h₂ : π₂.iUnion subseteq π₁.iUnion)
  proof: le_antisymm (fun J hJ => ⟨J, h₁ hJ, le_rfl⟩)
    le_iff_nonempty_imp_le_and_iUnion_subset.2
      ⟨fun _ hJ₁ _ hJ₂ Hne =>
        (π₂.eq_of_mem_of_mem hJ₁ (h₁ hJ₂) Hne.choose_spec.1 Hne.choose_spec.2).le, h₂⟩

中文:
定理 eq_of_boxes_subset_iUnion_superset
  条件: (h₁ : π₁.boxes subseteq π₂.boxes) (h₂ : π₂.iUnion subseteq π₁.iUnion)
  证明: le_antisymm (fun J hJ => ⟨J, h₁ hJ, le_rfl⟩)
    le_iff_nonempty_imp_le_and_iUnion_subset.2
      ⟨fun _ hJ₁ _ hJ₂ Hne =>
        (π₂.eq_of_mem_of_mem hJ₁ (h₁ hJ₂) Hne.choose_spec.1 Hne.choose_spec.2).le, h₂⟩

Depends on / 依赖: Hne.choose_spec, choose_spec, eq_of_mem_of_mem, le_antisymm, le_iff_nonempty_imp_le_and_iUnion_subset, le_rfl
-/
theorem eq_of_boxes_subset_iUnion_superset (h₁ : π₁.boxes subseteq π₂.boxes) (h₂ : π₂.iUnion subseteq π₁.iUnion) :
    π₁ = π₂ :=
le_antisymm (fun J hJ => ⟨J, h₁ hJ, le_rfl⟩)
    le_iff_nonempty_imp_le_and_iUnion_subset.2
      ⟨fun _ hJ₁ _ hJ₂ Hne =>
        (π₂.eq_of_mem_of_mem hJ₁ (h₁ hJ₂) Hne.choose_spec.1 Hne.choose_spec.2).le, h₂⟩

open scoped Classical in
/-- Given a prepartition `π` of a box `I` and a collection of prepartitions `πi J` of all boxes
`J ∈ π`, returns the prepartition of `I` into the union of the boxes of all `πi J`.

Though we only use the values of `πi` on the boxes of `π`, we require `πi` to be a globally defined
function. -/
@[simps]
/--
Definition of `biUnion` / `biUnion` 的定义

English:
definition biUnion
  signature: (πi : forall J : Box ι, Prepartition J)
  body: π.boxes.biUnion fun J => (πi J).boxes
  le_of_mem' J hJ := by
    simp only [Finset.mem_biUnion, mem_boxes] at hJ
    rcases hJ with ⟨J', hJ', hJ⟩
    exact ((πi J').le_of_mem hJ).trans (π.le_of_mem hJ')
  pairwiseDisjoint := by
    simp only [Set.Pairwise, Finset.mem_coe, Finset.mem_biUnion]
    rintro J₁' ⟨J₁, hJ₁, hJ₁'⟩ J₂' ⟨J₂, hJ₂, hJ₂'⟩ Hne
    rw [Function.onFun]; rw [Set.disjoint_left]
    rintro x hx₁ hx₂; apply Hne
    obtain rfl : J₁ = J₂ :=
      π.eq_of_mem_of_mem hJ₁ hJ₂ ((πi J₁).le_of_mem hJ₁' hx₁) ((πi J₂).le_of_mem hJ₂' hx₂)
    exact (πi J₁).eq_of_mem_of_mem hJ₁' hJ₂' hx₁ hx₂

中文:
定义 biUnion
  签名: (πi : 对任意 J : Box ι, 预分拆 J)
  定义体: π.boxes.biUnion fun J => (πi J).boxes
  le_of_mem' J hJ := by
    simp only [Finset.mem_biUnion, mem_boxes] at hJ
    rcases hJ with ⟨J', hJ', hJ⟩
    exact ((πi J').le_of_mem hJ).trans (π.le_of_mem hJ')
  pairwiseDisjoint := by
    simp only [Set.Pairwise, Finset.mem_coe, Finset.mem_biUnion]
    rintro J₁' ⟨J₁, hJ₁, hJ₁'⟩ J₂' ⟨J₂, hJ₂, hJ₂'⟩ Hne
    rw [Function.onFun]; rw [Set.disjoint_left]
    rintro x hx₁ hx₂; apply Hne
    obtain rfl : J₁ = J₂ :=
      π.eq_of_mem_of_mem hJ₁ hJ₂ ((πi J₁).le_of_mem hJ₁' hx₁) ((πi J₂).le_of_mem hJ₂' hx₂)
    exact (πi J₁).eq_of_mem_of_mem hJ₁' hJ₂' hx₁ hx₂

Depends on / 依赖: biUnion, boxes.biUnion
-/
def biUnion (πi : forall J : Box ι, Prepartition J) : Prepartition I where
  boxes := π.boxes.biUnion fun J => (πi J).boxes
  le_of_mem' J hJ := by
    simp only [Finset.mem_biUnion, mem_boxes] at hJ
    rcases hJ with ⟨J', hJ', hJ⟩
    exact ((πi J').le_of_mem hJ).trans (π.le_of_mem hJ')
  pairwiseDisjoint := by
    simp only [Set.Pairwise, Finset.mem_coe, Finset.mem_biUnion]
    rintro J₁' ⟨J₁, hJ₁, hJ₁'⟩ J₂' ⟨J₂, hJ₂, hJ₂'⟩ Hne
    rw [Function.onFun]; rw [Set.disjoint_left]
    rintro x hx₁ hx₂; apply Hne
    obtain rfl : J₁ = J₂ :=
      π.eq_of_mem_of_mem hJ₁ hJ₂ ((πi J₁).le_of_mem hJ₁' hx₁) ((πi J₂).le_of_mem hJ₂' hx₂)
    exact (πi J₁).eq_of_mem_of_mem hJ₁' hJ₂' hx₁ hx₂

variable {πi πi₁ πi₂ : forall J : Box ι, Prepartition J}

@[simp]
/--
theorem `mem_biUnion` / 定理 `mem_biUnion`

English:
theorem mem_biUnion
  statement: J in π.biUnion πi ↔ exists J' in π, J in πi J'
  proof: by simp [biUnion]

中文:
定理 mem_biUnion
  结论: J in π.biUnion πi ↔ 存在 J' in π, J in πi J'
  证明: by simp [biUnion]

Depends on / 依赖: biUnion
-/
theorem mem_biUnion : J in π.biUnion πi ↔ exists J' in π, J in πi J' := by simp [biUnion]

/--
theorem `biUnion_le` / 定理 `biUnion_le`

English:
theorem biUnion_le
  given: (πi : forall J, Prepartition J)
  statement: π.biUnion πi <= π
  proof: fun _ hJ =>
  let ⟨J', hJ', hJ⟩ := π.mem_biUnion.1 hJ
  ⟨J', hJ', (πi J').le_of_mem hJ⟩

@[simp]

中文:
定理 biUnion_le
  条件: (πi : 对任意 J, 预分拆 J)
  结论: π.biUnion πi <= π
  证明: fun _ hJ =>
  let ⟨J', hJ', hJ⟩ := π.mem_biUnion.1 hJ
  ⟨J', hJ', (πi J').le_of_mem hJ⟩

@[simp]
-/
theorem biUnion_le (πi : forall J, Prepartition J) : π.biUnion πi <= π := fun _ hJ =>
  let ⟨J', hJ', hJ⟩ := π.mem_biUnion.1 hJ
  ⟨J', hJ', (πi J').le_of_mem hJ⟩

@[simp]
/--
theorem `biUnion_top` / 定理 `biUnion_top`

English:
theorem biUnion_top
  statement: (π.biUnion fun _ => ⊤) = π
  proof: by
  ext
  simp

@[congr]

中文:
定理 biUnion_top
  结论: (π.biUnion fun _ => ⊤) = π
  证明: by
  ext
  simp

@[congr]
-/
theorem biUnion_top : (π.biUnion fun _ => ⊤) = π := by
  ext
  simp

@[congr]
/--
theorem `biUnion_congr` / 定理 `biUnion_congr`

English:
theorem biUnion_congr
  given: (h : π₁ = π₂) (hi : forall J in π₁, πi₁ J = πi₂ J)
  proof: by
  subst π₂
  ext J
  simp only [mem_biUnion]
  constructor <;> exact fun ⟨J', h₁, h₂⟩ => ⟨J', h₁, hi J' h₁ ▸ h₂⟩

中文:
定理 biUnion_congr
  条件: (h : π₁ = π₂) (hi : 对任意 J in π₁, πi₁ J = πi₂ J)
  证明: by
  subst π₂
  ext J
  simp only [mem_biUnion]
  constructor <;> exact fun ⟨J', h₁, h₂⟩ => ⟨J', h₁, hi J' h₁ ▸ h₂⟩

Depends on / 依赖: mem_biUnion
-/
theorem biUnion_congr (h : π₁ = π₂) (hi : forall J in π₁, πi₁ J = πi₂ J) :
    π₁.biUnion πi₁ = π₂.biUnion πi₂ := by
  subst π₂
  ext J
  simp only [mem_biUnion]
  constructor <;> exact fun ⟨J', h₁, h₂⟩ => ⟨J', h₁, hi J' h₁ ▸ h₂⟩

/--
theorem `biUnion_congr_of_le` / 定理 `biUnion_congr_of_le`

English:
theorem biUnion_congr_of_le
  given: (h : π₁ = π₂) (hi : forall J <= I, πi₁ J = πi₂ J)
  proof: biUnion_congr h fun J hJ => hi J (π₁.le_of_mem hJ)

@[simp]

中文:
定理 biUnion_congr_of_le
  条件: (h : π₁ = π₂) (hi : 对任意 J <= I, πi₁ J = πi₂ J)
  证明: biUnion_congr h fun J hJ => hi J (π₁.le_of_mem hJ)

@[simp]

Depends on / 依赖: biUnion_congr, le_of_mem
-/
theorem biUnion_congr_of_le (h : π₁ = π₂) (hi : forall J <= I, πi₁ J = πi₂ J) :
    π₁.biUnion πi₁ = π₂.biUnion πi₂ :=
  biUnion_congr h fun J hJ => hi J (π₁.le_of_mem hJ)

@[simp]
/--
theorem `iUnion_biUnion` / 定理 `iUnion_biUnion`

English:
theorem iUnion_biUnion
  given: (πi : forall J : Box ι, Prepartition J)
  proof: by simp [Prepartition.iUnion]

中文:
定理 iUnion_biUnion
  条件: (πi : 对任意 J : Box ι, 预分拆 J)
  证明: by simp [Prepartition.iUnion]

Depends on / 依赖: Prepartition, Prepartition.iUnion, iUnion
-/
theorem iUnion_biUnion (πi : forall J : Box ι, Prepartition J) :
    (π.biUnion πi).iUnion = ⋃ J in π, (πi J).iUnion := by simp [Prepartition.iUnion]

open scoped Classical in
@[simp]
/--
theorem `sum_biUnion_boxes` / 定理 `sum_biUnion_boxes`

English:
theorem sum_biUnion_boxes
  statement: {M : Type*} [AddCommMonoid M] (π : Prepartition I)
  proof: by
  refine Finset.sum_biUnion fun J₁ h₁ J₂ h₂ hne => Finset.disjoint_left.2 fun J' h₁' h₂' => ?_
  exact hne (π.eq_of_le_of_le h₁ h₂ ((πi J₁).le_of_mem h₁') ((πi J₂).le_of_mem h₂'))

中文:
定理 sum_biUnion_boxes
  结论: {M : 类型} [加法交换幺半群 M] (π : 预分拆 I)
  证明: by
  refine Finset.sum_biUnion fun J₁ h₁ J₂ h₂ hne => Finset.disjoint_left.2 fun J' h₁' h₂' => ?_
  exact hne (π.eq_of_le_of_le h₁ h₂ ((πi J₁).le_of_mem h₁') ((πi J₂).le_of_mem h₂'))

Depends on / 依赖: Finset, Finset.disjoint_left, Finset.sum_biUnion, disjoint_left, eq_of_le_of_le, le_of_mem, sum_biUnion
-/
theorem sum_biUnion_boxes {M : Type*} [AddCommMonoid M] (π : Prepartition I)
    (πi : forall J, Prepartition J) (f : Box ι -> M) :
    (∑ J in π.boxes.biUnion fun J => (πi J).boxes, f J) =
      ∑ J in π.boxes, ∑ J' in (πi J).boxes, f J' := by
  refine Finset.sum_biUnion fun J₁ h₁ J₂ h₂ hne => Finset.disjoint_left.2 fun J' h₁' h₂' => ?_
  exact hne (π.eq_of_le_of_le h₁ h₂ ((πi J₁).le_of_mem h₁') ((πi J₂).le_of_mem h₂'))

open scoped Classical in
/--
Definition of `biUnionIndex` / `biUnionIndex` 的定义

English:
definition biUnionIndex
  signature: (πi : forall (J : Box ι), Prepartition J) (J : Box ι)
  body: if hJ : J in π.biUnion πi then (π.mem_biUnion.1 hJ).choose else I

中文:
定义 biUnionIndex
  签名: (πi : 对任意 (J : Box ι), 预分拆 J) (J : Box ι)
  定义体: if hJ : J in π.biUnion πi then (π.mem_biUnion.1 hJ).choose else I

Depends on / 依赖: biUnion, mem_biUnion
-/
def biUnionIndex (πi : forall (J : Box ι), Prepartition J) (J : Box ι) : Box ι :=
  if hJ : J in π.biUnion πi then (π.mem_biUnion.1 hJ).choose else I

/--
theorem `biUnionIndex_mem` / 定理 `biUnionIndex_mem`

English:
theorem biUnionIndex_mem
  given: (hJ : J in π.biUnion πi)
  statement: π.biUnionIndex πi J in π
  proof: by
  rw [biUnionIndex]; rw [dif_pos hJ]
  exact (π.mem_biUnion.1 hJ).choose_spec.1

中文:
定理 biUnionIndex_mem
  条件: (hJ : J in π.biUnion πi)
  结论: π.biUnionIndex πi J in π
  证明: by
  rw [biUnionIndex]; rw [dif_pos hJ]
  exact (π.mem_biUnion.1 hJ).choose_spec.1

Depends on / 依赖: biUnionIndex, choose_spec, dif_pos, mem_biUnion
-/
theorem biUnionIndex_mem (hJ : J in π.biUnion πi) : π.biUnionIndex πi J in π := by
  rw [biUnionIndex]; rw [dif_pos hJ]
  exact (π.mem_biUnion.1 hJ).choose_spec.1

/--
theorem `biUnionIndex_le` / 定理 `biUnionIndex_le`

English:
theorem biUnionIndex_le
  given: (πi : forall J, Prepartition J) (J : Box ι)
  statement: π.biUnionIndex πi J <= I
  proof: by
  by_cases hJ : J in π.biUnion πi
  · exact π.le_of_mem (π.biUnionIndex_mem hJ)
  · rw [biUnionIndex, dif_neg hJ]

中文:
定理 biUnionIndex_le
  条件: (πi : 对任意 J, 预分拆 J) (J : Box ι)
  结论: π.biUnionIndex πi J <= I
  证明: by
  by_cases hJ : J in π.biUnion πi
  · exact π.le_of_mem (π.biUnionIndex_mem hJ)
  · rw [biUnionIndex, dif_neg hJ]

Depends on / 依赖: biUnion, biUnionIndex, biUnionIndex_mem, dif_neg, le_of_mem
-/
theorem biUnionIndex_le (πi : forall J, Prepartition J) (J : Box ι) : π.biUnionIndex πi J <= I := by
  by_cases hJ : J in π.biUnion πi
  · exact π.le_of_mem (π.biUnionIndex_mem hJ)
  · rw [biUnionIndex, dif_neg hJ]

/--
theorem `mem_biUnionIndex` / 定理 `mem_biUnionIndex`

English:
theorem mem_biUnionIndex
  given: (hJ : J in π.biUnion πi)
  statement: J in πi (π.biUnionIndex πi J)
  proof: by
  convert! (π.mem_biUnion.1 hJ).choose_spec.2 <;> exact dif_pos hJ

中文:
定理 mem_biUnionIndex
  条件: (hJ : J in π.biUnion πi)
  结论: J in πi (π.biUnionIndex πi J)
  证明: by
  convert! (π.mem_biUnion.1 hJ).choose_spec.2 <;> exact dif_pos hJ

Depends on / 依赖: choose_spec, convert, dif_pos, mem_biUnion
-/
theorem mem_biUnionIndex (hJ : J in π.biUnion πi) : J in πi (π.biUnionIndex πi J) := by
  convert! (π.mem_biUnion.1 hJ).choose_spec.2 <;> exact dif_pos hJ

/--
theorem `le_biUnionIndex` / 定理 `le_biUnionIndex`

English:
theorem le_biUnionIndex
  given: (hJ : J in π.biUnion πi)
  statement: J <= π.biUnionIndex πi J
  proof: le_of_mem _ (π.mem_biUnionIndex hJ)

中文:
定理 le_biUnionIndex
  条件: (hJ : J in π.biUnion πi)
  结论: J <= π.biUnionIndex πi J
  证明: le_of_mem _ (π.mem_biUnionIndex hJ)

Depends on / 依赖: le_of_mem, mem_biUnionIndex
-/
theorem le_biUnionIndex (hJ : J in π.biUnion πi) : J <= π.biUnionIndex πi J :=
  le_of_mem _ (π.mem_biUnionIndex hJ)

/--
theorem `biUnionIndex_of_mem` / 定理 `biUnionIndex_of_mem`

English:
theorem biUnionIndex_of_mem
  given: (hJ : J in π) {J'} (hJ' : J' in πi J)
  statement: π.biUnionIndex πi J' = J
  proof: have : J' in π.biUnion πi := π.mem_biUnion.2 ⟨J, hJ, hJ'⟩
  π.eq_of_le_of_le (π.biUnionIndex_mem this) hJ (π.le_biUnionIndex this) (le_of_mem _ hJ')

中文:
定理 biUnionIndex_of_mem
  条件: (hJ : J in π) {J'} (hJ' : J' in πi J)
  结论: π.biUnionIndex πi J' = J
  证明: have : J' in π.biUnion πi := π.mem_biUnion.2 ⟨J, hJ, hJ'⟩
  π.eq_of_le_of_le (π.biUnionIndex_mem this) hJ (π.le_biUnionIndex this) (le_of_mem _ hJ')

Depends on / 依赖: biUnion, biUnionIndex_mem, eq_of_le_of_le, le_biUnionIndex, le_of_mem, mem_biUnion
-/
theorem biUnionIndex_of_mem (hJ : J in π) {J'} (hJ' : J' in πi J) : π.biUnionIndex πi J' = J :=
  have : J' in π.biUnion πi := π.mem_biUnion.2 ⟨J, hJ, hJ'⟩
  π.eq_of_le_of_le (π.biUnionIndex_mem this) hJ (π.le_biUnionIndex this) (le_of_mem _ hJ')

/--
theorem `biUnion_assoc` / 定理 `biUnion_assoc`

English:
theorem biUnion_assoc
  given: (πi : forall J, Prepartition J) (πi' : Box ι -> forall J : Box ι, Prepartition J)
  proof: by
  ext J
  simp only [mem_biUnion]
  constructor
  · rintro ⟨J₁, hJ₁, J₂, hJ₂, hJ⟩
    refine ⟨J₂, ⟨J₁, hJ₁, hJ₂⟩, ?_⟩
    rwa [π.biUnionIndex_of_mem hJ₁ hJ₂]
  · rintro ⟨J₁, ⟨J₂, hJ₂, hJ₁⟩, hJ⟩
    refine ⟨J₂, hJ₂, J₁, hJ₁, ?_⟩
    rwa [π.biUnionIndex_of_mem hJ₂ hJ₁] at hJ

中文:
定理 biUnion_assoc
  条件: (πi : 对任意 J, 预分拆 J) (πi' : Box ι -> 对任意 J : Box ι, 预分拆 J)
  证明: by
  ext J
  simp only [mem_biUnion]
  constructor
  · rintro ⟨J₁, hJ₁, J₂, hJ₂, hJ⟩
    refine ⟨J₂, ⟨J₁, hJ₁, hJ₂⟩, ?_⟩
    rwa [π.biUnionIndex_of_mem hJ₁ hJ₂]
  · rintro ⟨J₁, ⟨J₂, hJ₂, hJ₁⟩, hJ⟩
    refine ⟨J₂, hJ₂, J₁, hJ₁, ?_⟩
    rwa [π.biUnionIndex_of_mem hJ₂ hJ₁] at hJ

Depends on / 依赖: biUnionIndex_of_mem, mem_biUnion
-/
theorem biUnion_assoc (πi : forall J, Prepartition J) (πi' : Box ι -> forall J : Box ι, Prepartition J) :
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
/--
Definition of `ofWithBot` / `ofWithBot` 的定义

English:
definition ofWithBot
  signature: (boxes : Finset (WithBot (Box ι)))
  body: Finset.eraseNone boxes
  le_of_mem' J hJ := by
    rw [mem_eraseNone] at hJ
    simpa only [WithBot.some_eq_coe, WithBot.coe_le_coe] using le_of_mem _ hJ
  pairwiseDisjoint J₁ h₁ J₂ h₂ hne := by
    simp only [mem_coe, mem_eraseNone] at h₁ h₂
    exact Box.disjoint_coe.1 (pairwise_disjoint h₁ h₂ (mt Option.some_inj.1 hne))

@[simp]

中文:
定义 ofWithBot
  签名: (boxes : 有限集 (WithBot (Box ι)))
  定义体: Finset.eraseNone boxes
  le_of_mem' J hJ := by
    rw [mem_eraseNone] at hJ
    simpa only [WithBot.some_eq_coe, WithBot.coe_le_coe] using le_of_mem _ hJ
  pairwiseDisjoint J₁ h₁ J₂ h₂ hne := by
    simp only [mem_coe, mem_eraseNone] at h₁ h₂
    exact Box.disjoint_coe.1 (pairwise_disjoint h₁ h₂ (mt Option.some_inj.1 hne))

@[simp]

Depends on / 依赖: Finset, Finset.eraseNone, eraseNone
-/
def ofWithBot (boxes : Finset (WithBot (Box ι)))
    (le_of_mem : forall J in boxes, (J : WithBot (Box ι)) <= I)
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
/--
theorem `mem_ofWithBot` / 定理 `mem_ofWithBot`

English:
theorem mem_ofWithBot
  given: {boxes : Finset (WithBot (Box ι))} {h₁ h₂}
  proof: mem_eraseNone

中文:
定理 mem_ofWithBot
  条件: {boxes : 有限集 (WithBot (Box ι))} {h₁ h₂}
  证明: mem_eraseNone

Depends on / 依赖: mem_eraseNone
-/
theorem mem_ofWithBot {boxes : Finset (WithBot (Box ι))} {h₁ h₂} :
    J in (ofWithBot boxes h₁ h₂ : Prepartition I) ↔ (J : WithBot (Box ι)) in boxes :=
  mem_eraseNone

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `iUnion_ofWithBot` / 定理 `iUnion_ofWithBot`

English:
theorem iUnion_ofWithBot
  statement: (boxes : Finset (WithBot (Box ι)))
  proof: by
  suffices ⋃ (J : Box ι) (_ : ↑J in boxes), ↑J = ⋃ J in boxes, (J : Set (ι -> Real)) by
    simpa [ofWithBot, Prepartition.iUnion]
  simp only [← Box.biUnion_coe_eq_coe, @iUnion_comm _ _ (Box ι), @iUnion_comm _ _ (@Eq _ _ _),
    iUnion_iUnion_eq_right]

中文:
定理 iUnion_ofWithBot
  结论: (boxes : 有限集 (WithBot (Box ι)))
  证明: by
  suffices ⋃ (J : Box ι) (_ : ↑J in boxes), ↑J = ⋃ J in boxes, (J : Set (ι -> Real)) by
    simpa [ofWithBot, Prepartition.iUnion]
  simp only [← Box.biUnion_coe_eq_coe, @iUnion_comm _ _ (Box ι), @iUnion_comm _ _ (@Eq _ _ _),
    iUnion_iUnion_eq_right]

Depends on / 依赖: Box.biUnion_coe_eq_coe, Prepartition, Prepartition.iUnion, biUnion_coe_eq_coe, iUnion, iUnion_comm, iUnion_iUnion_eq_right, ofWithBot
-/
theorem iUnion_ofWithBot (boxes : Finset (WithBot (Box ι)))
    (le_of_mem : forall J in boxes, (J : WithBot (Box ι)) <= I)
    (pairwise_disjoint : Set.Pairwise (boxes : Set (WithBot (Box ι))) Disjoint) :
    (ofWithBot boxes le_of_mem pairwise_disjoint).iUnion = ⋃ J in boxes, ↑J := by
  suffices ⋃ (J : Box ι) (_ : ↑J in boxes), ↑J = ⋃ J in boxes, (J : Set (ι -> Real)) by
    simpa [ofWithBot, Prepartition.iUnion]
  simp only [← Box.biUnion_coe_eq_coe, @iUnion_comm _ _ (Box ι), @iUnion_comm _ _ (@Eq _ _ _),
    iUnion_iUnion_eq_right]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `ofWithBot_le` / 定理 `ofWithBot_le`

English:
theorem ofWithBot_le
  statement: {boxes : Finset (WithBot (Box ι))}
  proof: by
  have : forall J : Box ι, ↑J in boxes -> exists J' in π, J <= J' := fun J hJ => by
    simpa only [WithBot.coe_le_coe] using H J hJ WithBot.coe_ne_bot
  simpa [ofWithBot, le_def]

中文:
定理 ofWithBot_le
  结论: {boxes : 有限集 (WithBot (Box ι))}
  证明: by
  have : forall J : Box ι, ↑J in boxes -> exists J' in π, J <= J' := fun J hJ => by
    simpa only [WithBot.coe_le_coe] using H J hJ WithBot.coe_ne_bot
  simpa [ofWithBot, le_def]

Depends on / 依赖: WithBot, WithBot.coe_le_coe, WithBot.coe_ne_bot, coe_le_coe, coe_ne_bot, le_def, ofWithBot
-/
theorem ofWithBot_le {boxes : Finset (WithBot (Box ι))}
    {le_of_mem : forall J in boxes, (J : WithBot (Box ι)) <= I}
    {pairwise_disjoint : Set.Pairwise (boxes : Set (WithBot (Box ι))) Disjoint}
    (H : forall J in boxes, J != ⊥ -> exists J' in π, J <= ↑J') :
    ofWithBot boxes le_of_mem pairwise_disjoint <= π := by
  have : forall J : Box ι, ↑J in boxes -> exists J' in π, J <= J' := fun J hJ => by
    simpa only [WithBot.coe_le_coe] using H J hJ WithBot.coe_ne_bot
  simpa [ofWithBot, le_def]

/--
theorem `le_ofWithBot` / 定理 `le_ofWithBot`

English:
theorem le_ofWithBot
  statement: {boxes : Finset (WithBot (Box ι))}
  proof: by
  intro J hJ
  rcases H J hJ with ⟨J', J'mem, hle⟩
  lift J' to Box ι using ne_bot_of_le_ne_bot WithBot.coe_ne_bot hle
  exact ⟨J', mem_ofWithBot.2 J'mem, WithBot.coe_le_coe.1 hle⟩

中文:
定理 le_ofWithBot
  结论: {boxes : 有限集 (WithBot (Box ι))}
  证明: by
  intro J hJ
  rcases H J hJ with ⟨J', J'mem, hle⟩
  lift J' to Box ι using ne_bot_of_le_ne_bot WithBot.coe_ne_bot hle
  exact ⟨J', mem_ofWithBot.2 J'mem, WithBot.coe_le_coe.1 hle⟩

Depends on / 依赖: WithBot, WithBot.coe_le_coe, WithBot.coe_ne_bot, coe_le_coe, coe_ne_bot, mem_ofWithBot, ne_bot_of_le_ne_bot
-/
theorem le_ofWithBot {boxes : Finset (WithBot (Box ι))}
    {le_of_mem : forall J in boxes, (J : WithBot (Box ι)) <= I}
    {pairwise_disjoint : Set.Pairwise (boxes : Set (WithBot (Box ι))) Disjoint}
    (H : forall J in π, exists J' in boxes, ↑J <= J') : π <= ofWithBot boxes le_of_mem pairwise_disjoint := by
  intro J hJ
  rcases H J hJ with ⟨J', J'mem, hle⟩
  lift J' to Box ι using ne_bot_of_le_ne_bot WithBot.coe_ne_bot hle
  exact ⟨J', mem_ofWithBot.2 J'mem, WithBot.coe_le_coe.1 hle⟩

/--
theorem `ofWithBot_mono` / 定理 `ofWithBot_mono`

English:
theorem ofWithBot_mono
  statement: {boxes₁ : Finset (WithBot (Box ι))}
  proof: le_ofWithBot _ fun J hJ => H J (mem_ofWithBot.1 hJ) WithBot.coe_ne_bot

中文:
定理 ofWithBot_mono
  结论: {boxes₁ : 有限集 (WithBot (Box ι))}
  证明: le_ofWithBot _ fun J hJ => H J (mem_ofWithBot.1 hJ) WithBot.coe_ne_bot

Depends on / 依赖: WithBot, WithBot.coe_ne_bot, coe_ne_bot, le_ofWithBot, mem_ofWithBot
-/
theorem ofWithBot_mono {boxes₁ : Finset (WithBot (Box ι))}
    {le_of_mem₁ : forall J in boxes₁, (J : WithBot (Box ι)) <= I}
    {pairwise_disjoint₁ : Set.Pairwise (boxes₁ : Set (WithBot (Box ι))) Disjoint}
    {boxes₂ : Finset (WithBot (Box ι))} {le_of_mem₂ : forall J in boxes₂, (J : WithBot (Box ι)) <= I}
    {pairwise_disjoint₂ : Set.Pairwise (boxes₂ : Set (WithBot (Box ι))) Disjoint}
    (H : forall J in boxes₁, J != ⊥ -> exists J' in boxes₂, J <= J') :
    ofWithBot boxes₁ le_of_mem₁ pairwise_disjoint₁ <=
      ofWithBot boxes₂ le_of_mem₂ pairwise_disjoint₂ :=
  le_ofWithBot _ fun J hJ => H J (mem_ofWithBot.1 hJ) WithBot.coe_ne_bot

/--
theorem `sum_ofWithBot` / 定理 `sum_ofWithBot`

English:
theorem sum_ofWithBot
  statement: {M : Type*} [AddCommMonoid M] (boxes : Finset (WithBot (Box ι)))
  proof: Finset.sum_eraseNone _ _

中文:
定理 sum_ofWithBot
  结论: {M : 类型} [加法交换幺半群 M] (boxes : 有限集 (WithBot (Box ι)))
  证明: Finset.sum_eraseNone _ _

Depends on / 依赖: Finset, Finset.sum_eraseNone, sum_eraseNone
-/
theorem sum_ofWithBot {M : Type*} [AddCommMonoid M] (boxes : Finset (WithBot (Box ι)))
    (le_of_mem : forall J in boxes, (J : WithBot (Box ι)) <= I)
    (pairwise_disjoint : Set.Pairwise (boxes : Set (WithBot (Box ι))) Disjoint) (f : Box ι -> M) :
    (∑ J in (ofWithBot boxes le_of_mem pairwise_disjoint).boxes, f J) =
      ∑ J in boxes, Option.elim' 0 f J :=
  Finset.sum_eraseNone _ _

open scoped Classical in
/--
Definition of `restrict` / `restrict` 的定义

English:
definition restrict
  signature: (π : Prepartition I) (J : Box ι)
  body: ofWithBot (π.boxes.image fun J' : Box ι => J ⊓ J')
    (fun J' hJ' => by
      rcases Finset.mem_image.1 hJ' with ⟨J', -, rfl⟩
      exact inf_le_left)
    (by
      simp only [Set.Pairwise, Finset.mem_coe, Finset.mem_image]
      rintro _ ⟨J₁, h₁, rfl⟩ _ ⟨J₂, h₂, rfl⟩ Hne
      have : J₁ != J₂ := by
        rintro rfl
        exact Hne rfl
      exact ((Box.disjoint_coe.2 <| π.disjoint_coe_of_mem h₁ h₂ this).inf_left' _).inf_right' _)

@[simp]

中文:
定义 restrict
  签名: (π : 预分拆 I) (J : Box ι)
  定义体: ofWithBot (π.boxes.image fun J' : Box ι => J ⊓ J')
    (fun J' hJ' => by
      rcases Finset.mem_image.1 hJ' with ⟨J', -, rfl⟩
      exact inf_le_left)
    (by
      simp only [Set.Pairwise, Finset.mem_coe, Finset.mem_image]
      rintro _ ⟨J₁, h₁, rfl⟩ _ ⟨J₂, h₂, rfl⟩ Hne
      have : J₁ != J₂ := by
        rintro rfl
        exact Hne rfl
      exact ((Box.disjoint_coe.2 <| π.disjoint_coe_of_mem h₁ h₂ this).inf_left' _).inf_right' _)

@[simp]

Depends on / 依赖: Box.disjoint_coe, Finset, Finset.mem_coe, Finset.mem_image, Pairwise, Set.Pairwise, boxes.image, disjoint_coe, disjoint_coe_of_mem, inf_le_left, inf_left, inf_right, mem_coe, mem_image, ofWithBot
-/
def restrict (π : Prepartition I) (J : Box ι) : Prepartition J :=
  ofWithBot (π.boxes.image fun J' : Box ι => J ⊓ J')
    (fun J' hJ' => by
      rcases Finset.mem_image.1 hJ' with ⟨J', -, rfl⟩
      exact inf_le_left)
    (by
      simp only [Set.Pairwise, Finset.mem_coe, Finset.mem_image]
      rintro _ ⟨J₁, h₁, rfl⟩ _ ⟨J₂, h₂, rfl⟩ Hne
      have : J₁ != J₂ := by
        rintro rfl
        exact Hne rfl
      exact ((Box.disjoint_coe.2 <| π.disjoint_coe_of_mem h₁ h₂ this).inf_left' _).inf_right' _)

@[simp]
/--
theorem `mem_restrict` / 定理 `mem_restrict`

English:
theorem mem_restrict
  statement: J₁ in π.restrict J ↔ exists J' in π, (J₁ : WithBot (Box ι)) = ↑J ⊓ ↑J'
  proof: by
  simp [restrict, eq_comm]

中文:
定理 mem_restrict
  结论: J₁ in π.restrict J ↔ 存在 J' in π, (J₁ : WithBot (Box ι)) = ↑J ⊓ ↑J'
  证明: by
  simp [restrict, eq_comm]

Depends on / 依赖: eq_comm, restrict
-/
theorem mem_restrict : J₁ in π.restrict J ↔ exists J' in π, (J₁ : WithBot (Box ι)) = ↑J ⊓ ↑J' := by
  simp [restrict, eq_comm]

/--
theorem `mem_restrict'` / 定理 `mem_restrict'`

English:
theorem mem_restrict'
  statement: J₁ in π.restrict J ↔ exists J' in π, (J₁ : Set (ι -> Real)) = ↑J inter ↑J'
  proof: by
  simp only [mem_restrict, ← Box.withBotCoe_inj, Box.coe_inf, Box.coe_coe]

@[gcongr, mono]

中文:
定理 mem_restrict'
  结论: J₁ in π.restrict J ↔ 存在 J' in π, (J₁ : 集合 (ι -> 实数)) = ↑J inter ↑J'
  证明: by
  simp only [mem_restrict, ← Box.withBotCoe_inj, Box.coe_inf, Box.coe_coe]

@[gcongr, mono]

Depends on / 依赖: Box.coe_coe, Box.coe_inf, Box.withBotCoe_inj, coe_coe, coe_inf, mem_restrict, withBotCoe_inj
-/
theorem mem_restrict' : J₁ in π.restrict J ↔ exists J' in π, (J₁ : Set (ι -> Real)) = ↑J inter ↑J' := by
  simp only [mem_restrict, ← Box.withBotCoe_inj, Box.coe_inf, Box.coe_coe]

@[gcongr, mono]
/--
theorem `restrict_mono` / 定理 `restrict_mono`

English:
theorem restrict_mono
  given: {π₁ π₂ : Prepartition I} (Hle : π₁ <= π₂)
  statement: π₁.restrict J <= π₂.restrict J
  proof: by
  classical
  refine ofWithBot_mono fun J₁ hJ₁ hne => ?_
  rw [Finset.mem_image] at hJ₁; rcases hJ₁ with ⟨J₁, hJ₁, rfl⟩
  rcases Hle hJ₁ with ⟨J₂, hJ₂, hle⟩
exact ⟨_, Finset.mem_image_of_mem _ hJ₂, inf_le_inf_left _ WithBot.coe_le_coe.2 hle⟩

中文:
定理 restrict_mono
  条件: {π₁ π₂ : 预分拆 I} (Hle : π₁ <= π₂)
  结论: π₁.restrict J <= π₂.restrict J
  证明: by
  classical
  refine ofWithBot_mono fun J₁ hJ₁ hne => ?_
  rw [Finset.mem_image] at hJ₁; rcases hJ₁ with ⟨J₁, hJ₁, rfl⟩
  rcases Hle hJ₁ with ⟨J₂, hJ₂, hle⟩
exact ⟨_, Finset.mem_image_of_mem _ hJ₂, inf_le_inf_left _ WithBot.coe_le_coe.2 hle⟩

Depends on / 依赖: Finset, Finset.mem_image, Finset.mem_image_of_mem, WithBot, WithBot.coe_le_coe, classical, coe_le_coe, inf_le_inf_left, mem_image, mem_image_of_mem, ofWithBot_mono
-/
theorem restrict_mono {π₁ π₂ : Prepartition I} (Hle : π₁ <= π₂) : π₁.restrict J <= π₂.restrict J := by
  classical
  refine ofWithBot_mono fun J₁ hJ₁ hne => ?_
  rw [Finset.mem_image] at hJ₁; rcases hJ₁ with ⟨J₁, hJ₁, rfl⟩
  rcases Hle hJ₁ with ⟨J₂, hJ₂, hle⟩
exact ⟨_, Finset.mem_image_of_mem _ hJ₂, inf_le_inf_left _ WithBot.coe_le_coe.2 hle⟩

/--
theorem `monotone_restrict` / 定理 `monotone_restrict`

English:
theorem monotone_restrict
  statement: Monotone fun π : Prepartition I => restrict π J
  proof: fun _ _ => restrict_mono

中文:
定理 monotone_restrict
  结论: 递增 fun π : 预分拆 I => restrict π J
  证明: fun _ _ => restrict_mono

Depends on / 依赖: restrict_mono
-/
theorem monotone_restrict : Monotone fun π : Prepartition I => restrict π J :=
  fun _ _ => restrict_mono

set_option backward.isDefEq.respectTransparency false in
/--
theorem `restrict_boxes_of_le` / 定理 `restrict_boxes_of_le`

English:
theorem restrict_boxes_of_le
  given: (π : Prepartition I) (h : I <= J)
  statement: (π.restrict J).boxes = π.boxes
  proof: by
  classical
  simp only [restrict, ofWithBot, eraseNone_eq_biUnion]
  refine Finset.image_biUnion.trans ?_
  refine (Finset.biUnion_congr rfl ?_).trans Finset.biUnion_singleton_eq_self
  intro J' hJ'
  rw [inf_of_le_right]; rw [← WithBot.some_eq_coe]; rw [Option.toFinset_some]
  exact WithBot.coe_le_coe.2 ((π.le_of_mem hJ').trans h)

@[simp]

中文:
定理 restrict_boxes_of_le
  条件: (π : 预分拆 I) (h : I <= J)
  结论: (π.restrict J).boxes = π.boxes
  证明: by
  classical
  simp only [restrict, ofWithBot, eraseNone_eq_biUnion]
  refine Finset.image_biUnion.trans ?_
  refine (Finset.biUnion_congr rfl ?_).trans Finset.biUnion_singleton_eq_self
  intro J' hJ'
  rw [inf_of_le_right]; rw [← WithBot.some_eq_coe]; rw [Option.toFinset_some]
  exact WithBot.coe_le_coe.2 ((π.le_of_mem hJ').trans h)

@[simp]

Depends on / 依赖: Finset, Finset.biUnion_congr, Finset.biUnion_singleton_eq_self, Finset.image_biUnion.trans, Option.toFinset_some, WithBot, WithBot.coe_le_coe, WithBot.some_eq_coe, biUnion_congr, biUnion_singleton_eq_self, classical, coe_le_coe, eraseNone_eq_biUnion, image_biUnion, inf_of_le_right, le_of_mem, ofWithBot, restrict, some_eq_coe, toFinset_some
-/
theorem restrict_boxes_of_le (π : Prepartition I) (h : I <= J) : (π.restrict J).boxes = π.boxes := by
  classical
  simp only [restrict, ofWithBot, eraseNone_eq_biUnion]
  refine Finset.image_biUnion.trans ?_
  refine (Finset.biUnion_congr rfl ?_).trans Finset.biUnion_singleton_eq_self
  intro J' hJ'
  rw [inf_of_le_right]; rw [← WithBot.some_eq_coe]; rw [Option.toFinset_some]
  exact WithBot.coe_le_coe.2 ((π.le_of_mem hJ').trans h)

@[simp]
/--
theorem `restrict_self` / 定理 `restrict_self`

English:
theorem restrict_self
  statement: π.restrict I = π
  proof: injective_boxes restrict_boxes_of_le π le_rfl

@[simp]

中文:
定理 restrict_self
  结论: π.restrict I = π
  证明: injective_boxes restrict_boxes_of_le π le_rfl

@[simp]

Depends on / 依赖: injective_boxes, le_rfl, restrict_boxes_of_le
-/
theorem restrict_self : π.restrict I = π :=
injective_boxes restrict_boxes_of_le π le_rfl

@[simp]
/--
theorem `iUnion_restrict` / 定理 `iUnion_restrict`

English:
theorem iUnion_restrict
  statement: (π.restrict J).iUnion = (J : Set (ι -> Real)) inter (π.iUnion)
  proof: by
  simp [restrict, ← inter_iUnion, ← iUnion_def]

@[simp]

中文:
定理 iUnion_restrict
  结论: (π.restrict J).iUnion = (J : 集合 (ι -> 实数)) inter (π.iUnion)
  证明: by
  simp [restrict, ← inter_iUnion, ← iUnion_def]

@[simp]

Depends on / 依赖: iUnion_def, inter_iUnion, restrict
-/
theorem iUnion_restrict : (π.restrict J).iUnion = (J : Set (ι -> Real)) inter (π.iUnion) := by
  simp [restrict, ← inter_iUnion, ← iUnion_def]

@[simp]
/--
theorem `restrict_biUnion` / 定理 `restrict_biUnion`

English:
theorem restrict_biUnion
  given: (πi : forall J, Prepartition J) (hJ : J in π)
  proof: by
  refine (eq_of_boxes_subset_iUnion_superset (fun J₁ h₁ => ?_) ?_).symm
  · refine (mem_restrict _).2 ⟨J₁, π.mem_biUnion.2 ⟨J, hJ, h₁⟩, (inf_of_le_right ?_).symm⟩
    exact WithBot.coe_le_coe.2 (le_of_mem _ h₁)
  · simp only [iUnion_restrict, iUnion_biUnion, Set.subset_def, Set.mem_inter_iff, Set.mem_iUnion]
    rintro x ⟨hxJ, J₁, h₁, hx⟩
    obtain rfl : J = J₁ := π.eq_of_mem_of_mem hJ h₁ hxJ (iUnion_subset _ hx)
    exact hx

中文:
定理 restrict_biUnion
  条件: (πi : 对任意 J, 预分拆 J) (hJ : J in π)
  证明: by
  refine (eq_of_boxes_subset_iUnion_superset (fun J₁ h₁ => ?_) ?_).symm
  · refine (mem_restrict _).2 ⟨J₁, π.mem_biUnion.2 ⟨J, hJ, h₁⟩, (inf_of_le_right ?_).symm⟩
    exact WithBot.coe_le_coe.2 (le_of_mem _ h₁)
  · simp only [iUnion_restrict, iUnion_biUnion, Set.subset_def, Set.mem_inter_iff, Set.mem_iUnion]
    rintro x ⟨hxJ, J₁, h₁, hx⟩
    obtain rfl : J = J₁ := π.eq_of_mem_of_mem hJ h₁ hxJ (iUnion_subset _ hx)
    exact hx

Depends on / 依赖: Set.mem_iUnion, Set.mem_inter_iff, Set.subset_def, WithBot, WithBot.coe_le_coe, coe_le_coe, eq_of_boxes_subset_iUnion_superset, eq_of_mem_of_mem, iUnion_biUnion, iUnion_restrict, iUnion_subset, inf_of_le_right, le_of_mem, mem_biUnion, mem_iUnion, mem_inter_iff, mem_restrict, subset_def
-/
theorem restrict_biUnion (πi : forall J, Prepartition J) (hJ : J in π) :
    (π.biUnion πi).restrict J = πi J := by
  refine (eq_of_boxes_subset_iUnion_superset (fun J₁ h₁ => ?_) ?_).symm
  · refine (mem_restrict _).2 ⟨J₁, π.mem_biUnion.2 ⟨J, hJ, h₁⟩, (inf_of_le_right ?_).symm⟩
    exact WithBot.coe_le_coe.2 (le_of_mem _ h₁)
  · simp only [iUnion_restrict, iUnion_biUnion, Set.subset_def, Set.mem_inter_iff, Set.mem_iUnion]
    rintro x ⟨hxJ, J₁, h₁, hx⟩
    obtain rfl : J = J₁ := π.eq_of_mem_of_mem hJ h₁ hxJ (iUnion_subset _ hx)
    exact hx

/--
theorem `biUnion_le_iff` / 定理 `biUnion_le_iff`

English:
theorem biUnion_le_iff
  given: {πi : forall J, Prepartition J} {π' : Prepartition I}
  proof: by
  constructor <;> intro H J hJ
  · rw [← π.restrict_biUnion πi hJ]
    exact restrict_mono H
  · rw [mem_biUnion] at hJ
    rcases hJ with ⟨J₁, h₁, hJ⟩
    rcases H J₁ h₁ hJ with ⟨J₂, h₂, Hle⟩
    rcases π'.mem_restrict.mp h₂ with ⟨J₃, h₃, H⟩
exact ⟨J₃, h₃, Hle.trans WithBot.coe_le_coe.1 H.trans_le inf_le_right⟩

中文:
定理 biUnion_le_iff
  条件: {πi : 对任意 J, 预分拆 J} {π' : 预分拆 I}
  证明: by
  constructor <;> intro H J hJ
  · rw [← π.restrict_biUnion πi hJ]
    exact restrict_mono H
  · rw [mem_biUnion] at hJ
    rcases hJ with ⟨J₁, h₁, hJ⟩
    rcases H J₁ h₁ hJ with ⟨J₂, h₂, Hle⟩
    rcases π'.mem_restrict.mp h₂ with ⟨J₃, h₃, H⟩
exact ⟨J₃, h₃, Hle.trans WithBot.coe_le_coe.1 H.trans_le inf_le_right⟩

Depends on / 依赖: H.trans_le, Hle.trans, WithBot, WithBot.coe_le_coe, coe_le_coe, inf_le_right, mem_biUnion, mem_restrict, mem_restrict.mp, restrict_biUnion, restrict_mono, trans_le
-/
theorem biUnion_le_iff {πi : forall J, Prepartition J} {π' : Prepartition I} :
    π.biUnion πi <= π' ↔ forall J in π, πi J <= π'.restrict J := by
  constructor <;> intro H J hJ
  · rw [← π.restrict_biUnion πi hJ]
    exact restrict_mono H
  · rw [mem_biUnion] at hJ
    rcases hJ with ⟨J₁, h₁, hJ⟩
    rcases H J₁ h₁ hJ with ⟨J₂, h₂, Hle⟩
    rcases π'.mem_restrict.mp h₂ with ⟨J₃, h₃, H⟩
exact ⟨J₃, h₃, Hle.trans WithBot.coe_le_coe.1 H.trans_le inf_le_right⟩

/--
theorem `le_biUnion_iff` / 定理 `le_biUnion_iff`

English:
theorem le_biUnion_iff
  given: {πi : forall J, Prepartition J} {π' : Prepartition I}
  proof: by
  refine ⟨fun H => ⟨H.trans (π.biUnion_le πi), fun J hJ => ?_⟩, ?_⟩
  · rw [← π.restrict_biUnion πi hJ]
    exact restrict_mono H
  · rintro ⟨H, Hi⟩ J' hJ'
    rcases H hJ' with ⟨J, hJ, hle⟩
    have : J' in π'.restrict J :=
      π'.mem_restrict.2 ⟨J', hJ', (inf_of_le_right <| WithBot.coe_le_coe.2 hle).symm⟩
    rcases Hi J hJ this with ⟨Ji, hJi, hlei⟩
    exact ⟨Ji, π.mem_biUnion.2 ⟨J, hJ, hJi⟩, hlei⟩

中文:
定理 le_biUnion_iff
  条件: {πi : 对任意 J, 预分拆 J} {π' : 预分拆 I}
  证明: by
  refine ⟨fun H => ⟨H.trans (π.biUnion_le πi), fun J hJ => ?_⟩, ?_⟩
  · rw [← π.restrict_biUnion πi hJ]
    exact restrict_mono H
  · rintro ⟨H, Hi⟩ J' hJ'
    rcases H hJ' with ⟨J, hJ, hle⟩
    have : J' in π'.restrict J :=
      π'.mem_restrict.2 ⟨J', hJ', (inf_of_le_right <| WithBot.coe_le_coe.2 hle).symm⟩
    rcases Hi J hJ this with ⟨Ji, hJi, hlei⟩
    exact ⟨Ji, π.mem_biUnion.2 ⟨J, hJ, hJi⟩, hlei⟩

Depends on / 依赖: H.trans, WithBot, WithBot.coe_le_coe, biUnion_le, coe_le_coe, inf_of_le_right, mem_biUnion, mem_restrict, restrict, restrict_biUnion, restrict_mono
-/
theorem le_biUnion_iff {πi : forall J, Prepartition J} {π' : Prepartition I} :
    π' <= π.biUnion πi ↔ π' <= π ∧ forall J in π, π'.restrict J <= πi J := by
  refine ⟨fun H => ⟨H.trans (π.biUnion_le πi), fun J hJ => ?_⟩, ?_⟩
  · rw [← π.restrict_biUnion πi hJ]
    exact restrict_mono H
  · rintro ⟨H, Hi⟩ J' hJ'
    rcases H hJ' with ⟨J, hJ, hle⟩
    have : J' in π'.restrict J :=
      π'.mem_restrict.2 ⟨J', hJ', (inf_of_le_right <| WithBot.coe_le_coe.2 hle).symm⟩
    rcases Hi J hJ this with ⟨Ji, hJi, hlei⟩
    exact ⟨Ji, π.mem_biUnion.2 ⟨J, hJ, hJi⟩, hlei⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SemilatticeInf (Prepartition I)
  body: { inf := fun π₁ π₂ => π₁.biUnion fun J => π₂.restrict J
    inf_le_left := fun π₁ _ => π₁.biUnion_le _
    inf_le_right := fun _ _ => (biUnion_le_iff _).2 fun _ _ => le_rfl
    le_inf := fun _ π₁ _ h₁ h₂ => π₁.le_biUnion_iff.2 ⟨h₁, fun _ _ => restrict_mono h₂⟩ }

中文:
实例 :
  签名: SemilatticeInf (预分拆 I)
  定义体: { inf := fun π₁ π₂ => π₁.biUnion fun J => π₂.restrict J
    inf_le_left := fun π₁ _ => π₁.biUnion_le _
    inf_le_right := fun _ _ => (biUnion_le_iff _).2 fun _ _ => le_rfl
    le_inf := fun _ π₁ _ h₁ h₂ => π₁.le_biUnion_iff.2 ⟨h₁, fun _ _ => restrict_mono h₂⟩ }

Depends on / 依赖: biUnion, biUnion_le, biUnion_le_iff, inf_le_left, inf_le_right, le_biUnion_iff, le_inf, le_rfl, restrict, restrict_mono
-/
instance : SemilatticeInf (Prepartition I) :=
  { inf := fun π₁ π₂ => π₁.biUnion fun J => π₂.restrict J
    inf_le_left := fun π₁ _ => π₁.biUnion_le _
    inf_le_right := fun _ _ => (biUnion_le_iff _).2 fun _ _ => le_rfl
    le_inf := fun _ π₁ _ h₁ h₂ => π₁.le_biUnion_iff.2 ⟨h₁, fun _ _ => restrict_mono h₂⟩ }

/--
theorem `inf_def` / 定理 `inf_def`

English:
theorem inf_def
  given: (π₁ π₂ : Prepartition I)
  statement: π₁ ⊓ π₂ = π₁.biUnion fun J => π₂.restrict J
  proof: rfl

@[simp]

中文:
定理 inf_def
  条件: (π₁ π₂ : 预分拆 I)
  结论: π₁ ⊓ π₂ = π₁.biUnion fun J => π₂.restrict J
  证明: rfl

@[simp]
-/
theorem inf_def (π₁ π₂ : Prepartition I) : π₁ ⊓ π₂ = π₁.biUnion fun J => π₂.restrict J := rfl

@[simp]
/--
theorem `mem_inf` / 定理 `mem_inf`

English:
theorem mem_inf
  given: {π₁ π₂ : Prepartition I}
  proof: by
  simp only [inf_def, mem_biUnion, mem_restrict]

@[simp]

中文:
定理 mem_inf
  条件: {π₁ π₂ : 预分拆 I}
  证明: by
  simp only [inf_def, mem_biUnion, mem_restrict]

@[simp]

Depends on / 依赖: inf_def, mem_biUnion, mem_restrict
-/
theorem mem_inf {π₁ π₂ : Prepartition I} :
    J in π₁ ⊓ π₂ ↔ exists J₁ in π₁, exists J₂ in π₂, (J : WithBot (Box ι)) = ↑J₁ ⊓ ↑J₂ := by
  simp only [inf_def, mem_biUnion, mem_restrict]

@[simp]
/--
theorem `iUnion_inf` / 定理 `iUnion_inf`

English:
theorem iUnion_inf
  given: (π₁ π₂ : Prepartition I)
  statement: (π₁ ⊓ π₂).iUnion = π₁.iUnion inter π₂.iUnion
  proof: by
  simp only [inf_def, iUnion_biUnion, iUnion_restrict, ← iUnion_inter, ← iUnion_def]

中文:
定理 iUnion_inf
  条件: (π₁ π₂ : 预分拆 I)
  结论: (π₁ ⊓ π₂).iUnion = π₁.iUnion inter π₂.iUnion
  证明: by
  simp only [inf_def, iUnion_biUnion, iUnion_restrict, ← iUnion_inter, ← iUnion_def]

Depends on / 依赖: iUnion_biUnion, iUnion_def, iUnion_inter, iUnion_restrict, inf_def
-/
theorem iUnion_inf (π₁ π₂ : Prepartition I) : (π₁ ⊓ π₂).iUnion = π₁.iUnion inter π₂.iUnion := by
  simp only [inf_def, iUnion_biUnion, iUnion_restrict, ← iUnion_inter, ← iUnion_def]

open scoped Classical in
/-- The prepartition with boxes `{J ∈ π | p J}`. -/
@[simps]
/--
Definition of `filter` / `filter` 的定义

English:
definition filter
  signature: (π : Prepartition I) (p : Box ι -> Prop)
  body: {J in π.boxes | p J}
  le_of_mem' _ hJ := π.le_of_mem (mem_filter.1 hJ).1
  pairwiseDisjoint _ h₁ _ h₂ := π.disjoint_coe_of_mem (mem_filter.1 h₁).1 (mem_filter.1 h₂).1

@[simp]

中文:
定义 filter
  签名: (π : 预分拆 I) (p : Box ι -> 命题)
  定义体: {J in π.boxes | p J}
  le_of_mem' _ hJ := π.le_of_mem (mem_filter.1 hJ).1
  pairwiseDisjoint _ h₁ _ h₂ := π.disjoint_coe_of_mem (mem_filter.1 h₁).1 (mem_filter.1 h₂).1

@[simp]
-/
def filter (π : Prepartition I) (p : Box ι -> Prop) : Prepartition I where
  boxes := {J in π.boxes | p J}
  le_of_mem' _ hJ := π.le_of_mem (mem_filter.1 hJ).1
  pairwiseDisjoint _ h₁ _ h₂ := π.disjoint_coe_of_mem (mem_filter.1 h₁).1 (mem_filter.1 h₂).1

@[simp]
/--
theorem `mem_filter` / 定理 `mem_filter`

English:
theorem mem_filter
  given: {p : Box ι -> Prop}
  statement: J in π.filter p ↔ J in π ∧ p J
  proof: by
  classical
  exact Finset.mem_filter

中文:
定理 mem_filter
  条件: {p : Box ι -> 命题}
  结论: J in π.filter p ↔ J in π ∧ p J
  证明: by
  classical
  exact Finset.mem_filter

Depends on / 依赖: Finset, Finset.mem_filter, classical, mem_filter
-/
theorem mem_filter {p : Box ι -> Prop} : J in π.filter p ↔ J in π ∧ p J := by
  classical
  exact Finset.mem_filter

/--
theorem `filter_le` / 定理 `filter_le`

English:
theorem filter_le
  given: (π : Prepartition I) (p : Box ι -> Prop)
  statement: π.filter p <= π
  proof: fun J hJ =>
  let ⟨hπ, _⟩ := π.mem_filter.1 hJ
  ⟨J, hπ, le_rfl⟩

中文:
定理 filter_le
  条件: (π : 预分拆 I) (p : Box ι -> 命题)
  结论: π.filter p <= π
  证明: fun J hJ =>
  let ⟨hπ, _⟩ := π.mem_filter.1 hJ
  ⟨J, hπ, le_rfl⟩
-/
theorem filter_le (π : Prepartition I) (p : Box ι -> Prop) : π.filter p <= π := fun J hJ =>
  let ⟨hπ, _⟩ := π.mem_filter.1 hJ
  ⟨J, hπ, le_rfl⟩

/--
theorem `filter_of_true` / 定理 `filter_of_true`

English:
theorem filter_of_true
  given: {p : Box ι -> Prop} (hp : forall J in π, p J)
  statement: π.filter p = π
  proof: by
  ext J
  simpa using hp J

@[simp]

中文:
定理 filter_of_true
  条件: {p : Box ι -> 命题} (hp : 对任意 J in π, p J)
  结论: π.filter p = π
  证明: by
  ext J
  simpa using hp J

@[simp]
-/
theorem filter_of_true {p : Box ι -> Prop} (hp : forall J in π, p J) : π.filter p = π := by
  ext J
  simpa using hp J

@[simp]
/--
theorem `filter_true` / 定理 `filter_true`

English:
theorem filter_true
  statement: (π.filter fun _ => True) = π
  proof: π.filter_of_true fun _ _ => trivial

@[simp]

中文:
定理 filter_true
  结论: (π.filter fun _ => 真) = π
  证明: π.filter_of_true fun _ _ => trivial

@[simp]

Depends on / 依赖: filter_of_true
-/
theorem filter_true : (π.filter fun _ => True) = π :=
  π.filter_of_true fun _ _ => trivial

@[simp]
/--
theorem `iUnion_filter_not` / 定理 `iUnion_filter_not`

English:
theorem iUnion_filter_not
  given: (π : Prepartition I) (p : Box ι -> Prop)
  proof: by
  simp only [Prepartition.iUnion]
  convert!
    (@Set.biUnion_sdiff_biUnion_eq (ι -> Real) (Box ι) π.boxes (π.filter p).boxes (↑) _).symm using 4
  · simp +contextual
  · rw [Set.PairwiseDisjoint]
    convert! π.pairwiseDisjoint
    rw [Set.union_eq_left]; rw [filter_boxes]; rw [coe_filter]
    exact fun _ ⟨h, _⟩ => h

中文:
定理 iUnion_filter_not
  条件: (π : 预分拆 I) (p : Box ι -> 命题)
  证明: by
  simp only [Prepartition.iUnion]
  convert!
    (@Set.biUnion_sdiff_biUnion_eq (ι -> Real) (Box ι) π.boxes (π.filter p).boxes (↑) _).symm using 4
  · simp +contextual
  · rw [Set.PairwiseDisjoint]
    convert! π.pairwiseDisjoint
    rw [Set.union_eq_left]; rw [filter_boxes]; rw [coe_filter]
    exact fun _ ⟨h, _⟩ => h

Depends on / 依赖: PairwiseDisjoint, Prepartition, Prepartition.iUnion, Set.PairwiseDisjoint, Set.biUnion_sdiff_biUnion_eq, Set.union_eq_left, biUnion_sdiff_biUnion_eq, coe_filter, contextual, convert, filter, filter_boxes, iUnion, pairwiseDisjoint, union_eq_left
-/
theorem iUnion_filter_not (π : Prepartition I) (p : Box ι -> Prop) :
    (π.filter fun J => ¬p J).iUnion = π.iUnion \ (π.filter p).iUnion := by
  simp only [Prepartition.iUnion]
  convert!
    (@Set.biUnion_sdiff_biUnion_eq (ι -> Real) (Box ι) π.boxes (π.filter p).boxes (↑) _).symm using 4
  · simp +contextual
  · rw [Set.PairwiseDisjoint]
    convert! π.pairwiseDisjoint
    rw [Set.union_eq_left]; rw [filter_boxes]; rw [coe_filter]
    exact fun _ ⟨h, _⟩ => h

open scoped Classical in
/--
theorem `sum_fiberwise` / 定理 `sum_fiberwise`

English:
theorem sum_fiberwise
  given: {α M} [AddCommMonoid M] (π : Prepartition I) (f : Box ι -> α) (g : Box ι -> M)
  proof: by
  convert! sum_fiberwise_of_maps_to (fun _ => Finset.mem_image_of_mem f) g

中文:
定理 sum_fiberwise
  条件: {α M} [加法交换幺半群 M] (π : 预分拆 I) (f : Box ι -> α) (g : Box ι -> M)
  证明: by
  convert! sum_fiberwise_of_maps_to (fun _ => Finset.mem_image_of_mem f) g

Depends on / 依赖: Finset, Finset.mem_image_of_mem, convert, mem_image_of_mem, sum_fiberwise_of_maps_to
-/
theorem sum_fiberwise {α M} [AddCommMonoid M] (π : Prepartition I) (f : Box ι -> α) (g : Box ι -> M) :
    (∑ y in π.boxes.image f, ∑ J in (π.filter fun J => f J = y).boxes, g J) =
      ∑ J in π.boxes, g J := by
  convert! sum_fiberwise_of_maps_to (fun _ => Finset.mem_image_of_mem f) g

open scoped Classical in
/-- Union of two disjoint prepartitions. -/
@[simps]
/--
Definition of `disjUnion` / `disjUnion` 的定义

English:
definition disjUnion
  signature: (π₁ π₂ : Prepartition I) (h : Disjoint π₁.iUnion π₂.iUnion)
  body: π₁.boxes union π₂.boxes
  le_of_mem' _ hJ := (Finset.mem_union.1 hJ).elim π₁.le_of_mem π₂.le_of_mem
  pairwiseDisjoint :=
    suffices forall J₁ in π₁, forall J₂ in π₂, J₁ != J₂ -> Disjoint (J₁ : Set (ι -> Real)) J₂ by
      simpa [pairwise_union_of_symm, pairwiseDisjoint]
    fun _ h₁ _ h₂ _ => h.mono (π₁.subset_iUnion h₁) (π₂.subset_iUnion h₂)

@[simp]

中文:
定义 disjUnion
  签名: (π₁ π₂ : 预分拆 I) (h : Disjoint π₁.iUnion π₂.iUnion)
  定义体: π₁.boxes union π₂.boxes
  le_of_mem' _ hJ := (Finset.mem_union.1 hJ).elim π₁.le_of_mem π₂.le_of_mem
  pairwiseDisjoint :=
    suffices forall J₁ in π₁, forall J₂ in π₂, J₁ != J₂ -> Disjoint (J₁ : Set (ι -> Real)) J₂ by
      simpa [pairwise_union_of_symm, pairwiseDisjoint]
    fun _ h₁ _ h₂ _ => h.mono (π₁.subset_iUnion h₁) (π₂.subset_iUnion h₂)

@[simp]
-/
def disjUnion (π₁ π₂ : Prepartition I) (h : Disjoint π₁.iUnion π₂.iUnion) : Prepartition I where
  boxes := π₁.boxes union π₂.boxes
  le_of_mem' _ hJ := (Finset.mem_union.1 hJ).elim π₁.le_of_mem π₂.le_of_mem
  pairwiseDisjoint :=
    suffices forall J₁ in π₁, forall J₂ in π₂, J₁ != J₂ -> Disjoint (J₁ : Set (ι -> Real)) J₂ by
      simpa [pairwise_union_of_symm, pairwiseDisjoint]
    fun _ h₁ _ h₂ _ => h.mono (π₁.subset_iUnion h₁) (π₂.subset_iUnion h₂)

@[simp]
/--
theorem `mem_disjUnion` / 定理 `mem_disjUnion`

English:
theorem mem_disjUnion
  given: (H : Disjoint π₁.iUnion π₂.iUnion)
  proof: by
  classical exact Finset.mem_union

@[simp]

中文:
定理 mem_disjUnion
  条件: (H : Disjoint π₁.iUnion π₂.iUnion)
  证明: by
  classical exact Finset.mem_union

@[simp]

Depends on / 依赖: Finset, Finset.mem_union, classical, mem_union
-/
theorem mem_disjUnion (H : Disjoint π₁.iUnion π₂.iUnion) :
    J in π₁.disjUnion π₂ H ↔ J in π₁ ∨ J in π₂ := by
  classical exact Finset.mem_union

@[simp]
/--
theorem `iUnion_disjUnion` / 定理 `iUnion_disjUnion`

English:
theorem iUnion_disjUnion
  given: (h : Disjoint π₁.iUnion π₂.iUnion)
  proof: by
  simp [disjUnion, Prepartition.iUnion, iUnion_or, iUnion_union_distrib]

中文:
定理 iUnion_disjUnion
  条件: (h : Disjoint π₁.iUnion π₂.iUnion)
  证明: by
  simp [disjUnion, Prepartition.iUnion, iUnion_or, iUnion_union_distrib]

Depends on / 依赖: Prepartition, Prepartition.iUnion, disjUnion, iUnion, iUnion_or, iUnion_union_distrib
-/
theorem iUnion_disjUnion (h : Disjoint π₁.iUnion π₂.iUnion) :
    (π₁.disjUnion π₂ h).iUnion = π₁.iUnion union π₂.iUnion := by
  simp [disjUnion, Prepartition.iUnion, iUnion_or, iUnion_union_distrib]

open scoped Classical in
@[simp]
/--
theorem `sum_disj_union_boxes` / 定理 `sum_disj_union_boxes`

English:
theorem sum_disj_union_boxes
  statement: {M : Type*} [AddCommMonoid M] (h : Disjoint π₁.iUnion π₂.iUnion)
  proof: sum_union disjoint_boxes_of_disjoint_iUnion h

中文:
定理 sum_disj_union_boxes
  结论: {M : 类型} [加法交换幺半群 M] (h : Disjoint π₁.iUnion π₂.iUnion)
  证明: sum_union disjoint_boxes_of_disjoint_iUnion h

Depends on / 依赖: disjoint_boxes_of_disjoint_iUnion, sum_union
-/
theorem sum_disj_union_boxes {M : Type*} [AddCommMonoid M] (h : Disjoint π₁.iUnion π₂.iUnion)
    (f : Box ι -> M) :
    ∑ J in π₁.boxes union π₂.boxes, f J = (∑ J in π₁.boxes, f J) + ∑ J in π₂.boxes, f J :=
sum_union disjoint_boxes_of_disjoint_iUnion h

section Distortion

variable [Fintype ι]

/--
Definition of `distortion` / `distortion` 的定义

English:
definition distortion
  signature: : Real>=0
  body: π.boxes.sup Box.distortion

中文:
定义 distortion
  签名: : 实数>=0
  定义体: π.boxes.sup Box.distortion

Depends on / 依赖: Box.distortion, boxes.sup, distortion
-/
def distortion : Real>=0 :=
  π.boxes.sup Box.distortion

/--
theorem `distortion_le_of_mem` / 定理 `distortion_le_of_mem`

English:
theorem distortion_le_of_mem
  given: (h : J in π)
  statement: J.distortion <= π.distortion
  proof: le_sup h

中文:
定理 distortion_le_of_mem
  条件: (h : J in π)
  结论: J.distortion <= π.distortion
  证明: le_sup h

Depends on / 依赖: le_sup
-/
theorem distortion_le_of_mem (h : J in π) : J.distortion <= π.distortion :=
  le_sup h

/--
theorem `distortion_le_iff` / 定理 `distortion_le_iff`

English:
theorem distortion_le_iff
  given: {c : Real>=0}
  statement: π.distortion <= c ↔ forall J in π, Box.distortion J <= c
  proof: Finset.sup_le_iff

中文:
定理 distortion_le_iff
  条件: {c : 实数>=0}
  结论: π.distortion <= c ↔ 对任意 J in π, Box.distortion J <= c
  证明: Finset.sup_le_iff

Depends on / 依赖: Finset, Finset.sup_le_iff, sup_le_iff
-/
theorem distortion_le_iff {c : Real>=0} : π.distortion <= c ↔ forall J in π, Box.distortion J <= c :=
  Finset.sup_le_iff

/--
theorem `distortion_biUnion` / 定理 `distortion_biUnion`

English:
theorem distortion_biUnion
  given: (π : Prepartition I) (πi : forall J, Prepartition J)
  proof: by
  classical exact sup_biUnion _ _

@[simp]

中文:
定理 distortion_biUnion
  条件: (π : 预分拆 I) (πi : 对任意 J, 预分拆 J)
  证明: by
  classical exact sup_biUnion _ _

@[simp]

Depends on / 依赖: classical, sup_biUnion
-/
theorem distortion_biUnion (π : Prepartition I) (πi : forall J, Prepartition J) :
    (π.biUnion πi).distortion = π.boxes.sup fun J => (πi J).distortion := by
  classical exact sup_biUnion _ _

@[simp]
/--
theorem `distortion_disjUnion` / 定理 `distortion_disjUnion`

English:
theorem distortion_disjUnion
  given: (h : Disjoint π₁.iUnion π₂.iUnion)
  proof: by
  classical exact sup_union

中文:
定理 distortion_disjUnion
  条件: (h : Disjoint π₁.iUnion π₂.iUnion)
  证明: by
  classical exact sup_union

Depends on / 依赖: classical, sup_union
-/
theorem distortion_disjUnion (h : Disjoint π₁.iUnion π₂.iUnion) :
    (π₁.disjUnion π₂ h).distortion = max π₁.distortion π₂.distortion := by
  classical exact sup_union

/--
theorem `distortion_of_const` / 定理 `distortion_of_const`

English:
theorem distortion_of_const
  given: {c} (h₁ : π.boxes.Nonempty) (h₂ : forall J in π, Box.distortion J = c)
  proof: (sup_congr rfl h₂).trans (sup_const h₁ _)

@[simp]

中文:
定理 distortion_of_const
  条件: {c} (h₁ : π.boxes.非空) (h₂ : 对任意 J in π, Box.distortion J = c)
  证明: (sup_congr rfl h₂).trans (sup_const h₁ _)

@[simp]

Depends on / 依赖: sup_congr, sup_const
-/
theorem distortion_of_const {c} (h₁ : π.boxes.Nonempty) (h₂ : forall J in π, Box.distortion J = c) :
    π.distortion = c :=
  (sup_congr rfl h₂).trans (sup_const h₁ _)

@[simp]
/--
theorem `distortion_top` / 定理 `distortion_top`

English:
theorem distortion_top
  given: (I : Box ι)
  statement: distortion (⊤ : Prepartition I) = I.distortion
  proof: sup_singleton

@[simp]

中文:
定理 distortion_top
  条件: (I : Box ι)
  结论: distortion (⊤ : 预分拆 I) = I.distortion
  证明: sup_singleton

@[simp]

Depends on / 依赖: sup_singleton
-/
theorem distortion_top (I : Box ι) : distortion (⊤ : Prepartition I) = I.distortion :=
  sup_singleton

@[simp]
/--
theorem `distortion_bot` / 定理 `distortion_bot`

English:
theorem distortion_bot
  given: (I : Box ι)
  statement: distortion (⊥ : Prepartition I) = 0
  proof: sup_empty

中文:
定理 distortion_bot
  条件: (I : Box ι)
  结论: distortion (⊥ : 预分拆 I) = 0
  证明: sup_empty

Depends on / 依赖: sup_empty
-/
theorem distortion_bot (I : Box ι) : distortion (⊥ : Prepartition I) = 0 :=
  sup_empty

end Distortion

/--
Definition of `IsPartition` / `IsPartition` 的定义

English:
definition IsPartition
  signature: (π : Prepartition I)
  body: forall x in I, exists J in π, x in J

中文:
定义 IsPartition
  签名: (π : 预分拆 I)
  定义体: forall x in I, exists J in π, x in J
-/
def IsPartition (π : Prepartition I) :=
  forall x in I, exists J in π, x in J

/--
theorem `isPartition_iff_iUnion_eq` / 定理 `isPartition_iff_iUnion_eq`

English:
theorem isPartition_iff_iUnion_eq
  given: {π : Prepartition I}
  statement: π.IsPartition ↔ π.iUnion = I
  proof: by
  simp_rw [IsPartition, Set.Subset.antisymm_iff, π.iUnion_subset, true_and, Set.subset_def,
    mem_iUnion, Box.mem_coe]

@[simp]

中文:
定理 isPartition_iff_iUnion_eq
  条件: {π : 预分拆 I}
  结论: π.IsPartition ↔ π.iUnion = I
  证明: by
  simp_rw [IsPartition, Set.Subset.antisymm_iff, π.iUnion_subset, true_and, Set.subset_def,
    mem_iUnion, Box.mem_coe]

@[simp]

Depends on / 依赖: Box.mem_coe, IsPartition, Set.Subset.antisymm_iff, Set.subset_def, Subset, antisymm_iff, iUnion_subset, mem_coe, mem_iUnion, simp_rw, subset_def, true_and
-/
theorem isPartition_iff_iUnion_eq {π : Prepartition I} : π.IsPartition ↔ π.iUnion = I := by
  simp_rw [IsPartition, Set.Subset.antisymm_iff, π.iUnion_subset, true_and, Set.subset_def,
    mem_iUnion, Box.mem_coe]

@[simp]
/--
theorem `isPartition_single_iff` / 定理 `isPartition_single_iff`

English:
theorem isPartition_single_iff
  given: (h : J <= I)
  statement: IsPartition (single I J h) ↔ J = I
  proof: by
  simp [isPartition_iff_iUnion_eq]

中文:
定理 isPartition_single_iff
  条件: (h : J <= I)
  结论: IsPartition (single I J h) ↔ J = I
  证明: by
  simp [isPartition_iff_iUnion_eq]

Depends on / 依赖: isPartition_iff_iUnion_eq
-/
theorem isPartition_single_iff (h : J <= I) : IsPartition (single I J h) ↔ J = I := by
  simp [isPartition_iff_iUnion_eq]

/--
theorem `isPartitionTop` / 定理 `isPartitionTop`

English:
theorem isPartitionTop
  given: (I : Box ι)
  statement: IsPartition (⊤ : Prepartition I)
  proof: fun _ hx => ⟨I, mem_top.2 rfl, hx⟩

中文:
定理 isPartitionTop
  条件: (I : Box ι)
  结论: IsPartition (⊤ : 预分拆 I)
  证明: fun _ hx => ⟨I, mem_top.2 rfl, hx⟩

Depends on / 依赖: mem_top
-/
theorem isPartitionTop (I : Box ι) : IsPartition (⊤ : Prepartition I) :=
  fun _ hx => ⟨I, mem_top.2 rfl, hx⟩

namespace IsPartition

variable {π}

/--
theorem `iUnion_eq` / 定理 `iUnion_eq`

English:
theorem iUnion_eq
  given: (h : π.IsPartition)
  statement: π.iUnion = I
  proof: isPartition_iff_iUnion_eq.1 h

中文:
定理 iUnion_eq
  条件: (h : π.IsPartition)
  结论: π.iUnion = I
  证明: isPartition_iff_iUnion_eq.1 h

Depends on / 依赖: isPartition_iff_iUnion_eq
-/
theorem iUnion_eq (h : π.IsPartition) : π.iUnion = I :=
  isPartition_iff_iUnion_eq.1 h

/--
theorem `iUnion_subset` / 定理 `iUnion_subset`

English:
theorem iUnion_subset
  given: (h : π.IsPartition) (π₁ : Prepartition I)
  statement: π₁.iUnion subseteq π.iUnion
  proof: h.iUnion_eq.symm ▸ π₁.iUnion_subset

中文:
定理 iUnion_subset
  条件: (h : π.IsPartition) (π₁ : 预分拆 I)
  结论: π₁.iUnion subseteq π.iUnion
  证明: h.iUnion_eq.symm ▸ π₁.iUnion_subset

Depends on / 依赖: h.iUnion_eq.symm, iUnion_eq, iUnion_subset
-/
theorem iUnion_subset (h : π.IsPartition) (π₁ : Prepartition I) : π₁.iUnion subseteq π.iUnion :=
  h.iUnion_eq.symm ▸ π₁.iUnion_subset

/--
theorem `existsUnique` / 定理 `existsUnique`

English:
theorem existsUnique
  given: (h : π.IsPartition) (hx : x in I)
  proof: by
  rcases h x hx with ⟨J, h, hx⟩
  exact ExistsUnique.intro J ⟨h, hx⟩ fun J' ⟨h', hx'⟩ => π.eq_of_mem_of_mem h' h hx' hx

中文:
定理 存在Unique
  条件: (h : π.IsPartition) (hx : x in I)
  证明: by
  rcases h x hx with ⟨J, h, hx⟩
  exact ExistsUnique.intro J ⟨h, hx⟩ fun J' ⟨h', hx'⟩ => π.eq_of_mem_of_mem h' h hx' hx
-/
protected theorem existsUnique (h : π.IsPartition) (hx : x in I) :
    exists! J in π, x in J := by
  rcases h x hx with ⟨J, h, hx⟩
  exact ExistsUnique.intro J ⟨h, hx⟩ fun J' ⟨h', hx'⟩ => π.eq_of_mem_of_mem h' h hx' hx

/--
theorem `nonempty_boxes` / 定理 `nonempty_boxes`

English:
theorem nonempty_boxes
  given: (h : π.IsPartition)
  statement: π.boxes.Nonempty
  proof: let ⟨J, hJ, _⟩ := h _ I.upper_mem
  ⟨J, hJ⟩

中文:
定理 nonempty_boxes
  条件: (h : π.IsPartition)
  结论: π.boxes.非空
  证明: let ⟨J, hJ, _⟩ := h _ I.upper_mem
  ⟨J, hJ⟩

Depends on / 依赖: I.upper_mem, upper_mem
-/
theorem nonempty_boxes (h : π.IsPartition) : π.boxes.Nonempty :=
  let ⟨J, hJ, _⟩ := h _ I.upper_mem
  ⟨J, hJ⟩

/--
theorem `eq_of_boxes_subset` / 定理 `eq_of_boxes_subset`

English:
theorem eq_of_boxes_subset
  given: (h₁ : π₁.IsPartition) (h₂ : π₁.boxes subseteq π₂.boxes)
  statement: π₁ = π₂
  proof: eq_of_boxes_subset_iUnion_superset h₂ h₁.iUnion_subset _

中文:
定理 eq_of_boxes_subset
  条件: (h₁ : π₁.IsPartition) (h₂ : π₁.boxes subseteq π₂.boxes)
  结论: π₁ = π₂
  证明: eq_of_boxes_subset_iUnion_superset h₂ h₁.iUnion_subset _

Depends on / 依赖: eq_of_boxes_subset_iUnion_superset, iUnion_subset
-/
theorem eq_of_boxes_subset (h₁ : π₁.IsPartition) (h₂ : π₁.boxes subseteq π₂.boxes) : π₁ = π₂ :=
eq_of_boxes_subset_iUnion_superset h₂ h₁.iUnion_subset _

/--
theorem `le_iff` / 定理 `le_iff`

English:
theorem le_iff
  given: (h : π₂.IsPartition)
  proof: le_iff_nonempty_imp_le_and_iUnion_subset.trans and_iff_left h.iUnion_subset _

中文:
定理 le_iff
  条件: (h : π₂.IsPartition)
  证明: le_iff_nonempty_imp_le_and_iUnion_subset.trans and_iff_left h.iUnion_subset _

Depends on / 依赖: and_iff_left, h.iUnion_subset, iUnion_subset, le_iff_nonempty_imp_le_and_iUnion_subset, le_iff_nonempty_imp_le_and_iUnion_subset.trans
-/
theorem le_iff (h : π₂.IsPartition) :
    π₁ <= π₂ ↔ forall J in π₁, forall J' in π₂, (J inter J' : Set (ι -> Real)).Nonempty -> J <= J' :=
le_iff_nonempty_imp_le_and_iUnion_subset.trans and_iff_left h.iUnion_subset _

/--
theorem `biUnion` / 定理 `biUnion`

English:
theorem biUnion
  given: (h : IsPartition π) (hi : forall J in π, IsPartition (πi J))
  proof: fun x hx =>
  let ⟨J, hJ, hxi⟩ := h x hx
  let ⟨Ji, hJi, hx⟩ := hi J hJ x hxi
  ⟨Ji, π.mem_biUnion.2 ⟨J, hJ, hJi⟩, hx⟩

中文:
定理 biUnion
  条件: (h : IsPartition π) (hi : 对任意 J in π, IsPartition (πi J))
  证明: fun x hx =>
  let ⟨J, hJ, hxi⟩ := h x hx
  let ⟨Ji, hJi, hx⟩ := hi J hJ x hxi
  ⟨Ji, π.mem_biUnion.2 ⟨J, hJ, hJi⟩, hx⟩
-/
protected theorem biUnion (h : IsPartition π) (hi : forall J in π, IsPartition (πi J)) :
    IsPartition (π.biUnion πi) := fun x hx =>
  let ⟨J, hJ, hxi⟩ := h x hx
  let ⟨Ji, hJi, hx⟩ := hi J hJ x hxi
  ⟨Ji, π.mem_biUnion.2 ⟨J, hJ, hJi⟩, hx⟩

/--
theorem `restrict` / 定理 `restrict`

English:
theorem restrict
  given: (h : IsPartition π) (hJ : J <= I)
  statement: IsPartition (π.restrict J)
  proof: isPartition_iff_iUnion_eq.2 by simp [h.iUnion_eq, hJ]

中文:
定理 restrict
  条件: (h : IsPartition π) (hJ : J <= I)
  结论: IsPartition (π.restrict J)
  证明: isPartition_iff_iUnion_eq.2 by simp [h.iUnion_eq, hJ]
-/
protected theorem restrict (h : IsPartition π) (hJ : J <= I) : IsPartition (π.restrict J) :=
isPartition_iff_iUnion_eq.2 by simp [h.iUnion_eq, hJ]

/--
theorem `inf` / 定理 `inf`

English:
theorem inf
  given: (h₁ : IsPartition π₁) (h₂ : IsPartition π₂)
  statement: IsPartition (π₁ ⊓ π₂)
  proof: isPartition_iff_iUnion_eq.2 by simp [h₁.iUnion_eq, h₂.iUnion_eq]

中文:
定理 下确界
  条件: (h₁ : IsPartition π₁) (h₂ : IsPartition π₂)
  结论: IsPartition (π₁ ⊓ π₂)
  证明: isPartition_iff_iUnion_eq.2 by simp [h₁.iUnion_eq, h₂.iUnion_eq]
-/
protected theorem inf (h₁ : IsPartition π₁) (h₂ : IsPartition π₂) : IsPartition (π₁ ⊓ π₂) :=
isPartition_iff_iUnion_eq.2 by simp [h₁.iUnion_eq, h₂.iUnion_eq]

end IsPartition

/--
theorem `iUnion_biUnion_partition` / 定理 `iUnion_biUnion_partition`

English:
theorem iUnion_biUnion_partition
  given: (h : forall J in π, (πi J).IsPartition)
  proof: (iUnion_biUnion _ _).trans
    iUnion_congr_of_surjective id surjective_id fun J =>
      iUnion_congr_of_surjective id surjective_id fun hJ => (h J hJ).iUnion_eq

中文:
定理 iUnion_biUnion_partition
  条件: (h : 对任意 J in π, (πi J).IsPartition)
  证明: (iUnion_biUnion _ _).trans
    iUnion_congr_of_surjective id surjective_id fun J =>
      iUnion_congr_of_surjective id surjective_id fun hJ => (h J hJ).iUnion_eq

Depends on / 依赖: iUnion_biUnion, iUnion_congr_of_surjective, iUnion_eq, surjective_id
-/
theorem iUnion_biUnion_partition (h : forall J in π, (πi J).IsPartition) :
    (π.biUnion πi).iUnion = π.iUnion :=
(iUnion_biUnion _ _).trans
    iUnion_congr_of_surjective id surjective_id fun J =>
      iUnion_congr_of_surjective id surjective_id fun hJ => (h J hJ).iUnion_eq

/--
theorem `isPartitionDisjUnionOfEqDiff` / 定理 `isPartitionDisjUnionOfEqDiff`

English:
theorem isPartitionDisjUnionOfEqDiff
  given: (h : π₂.iUnion = ↑I \ π₁.iUnion)
  proof: isPartition_iff_iUnion_eq.2 (iUnion_disjUnion _).trans by simp [h, π₁.iUnion_subset]

中文:
定理 isPartitionDisjUnionOfEqDiff
  条件: (h : π₂.iUnion = ↑I \ π₁.iUnion)
  证明: isPartition_iff_iUnion_eq.2 (iUnion_disjUnion _).trans by simp [h, π₁.iUnion_subset]

Depends on / 依赖: iUnion_disjUnion, iUnion_subset, isPartition_iff_iUnion_eq
-/
theorem isPartitionDisjUnionOfEqDiff (h : π₂.iUnion = ↑I \ π₁.iUnion) :
    IsPartition (π₁.disjUnion π₂ <| h.symm ▸ disjoint_sdiff_self_right) :=
isPartition_iff_iUnion_eq.2 (iUnion_disjUnion _).trans by simp [h, π₁.iUnion_subset]

end Prepartition

end BoxIntegral
