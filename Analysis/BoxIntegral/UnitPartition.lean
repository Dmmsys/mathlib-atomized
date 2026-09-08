/-
Copyright (c) 2024 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.Analysis.BoxIntegral.Integrability
public import Mathlib.Analysis.BoxIntegral.Partition.Measure
public import Mathlib.Analysis.BoxIntegral.Partition.Tagged

/-!
# Unit Partition

Fix `n` a positive integer. `BoxIntegral.unitPartition.box` are boxes in `ι → ℝ` obtained by
dividing the unit box uniformly into boxes of side length `1 / n` and translating the boxes by
vectors `ν : ι → ℤ`.

Let `B` be a `BoxIntegral`. A `unitPartition.box` is admissible for `B` (more precisely its index is
admissible) if it is contained in `B`. There are finitely many admissible `unitPartition.box` for
`B` and thus we can form the corresponding tagged prepartition, see
`BoxIntegral.unitPartition.prepartition` (note that each `unitPartition.box` comes with its
tag situated at its "upper most" vertex). If `B` satisfies `hasIntegralVertices`, that
is its vertices are in `ι → ℤ`, then the corresponding prepartition is actually a partition.

## Main definitions and results

* `BoxIntegral.hasIntegralVertices`: a `Prop` that states that the vertices of the box have
  coordinates in `ℤ`

* `BoxIntegral.unitPartition.box`: a `BoxIntegral`, indexed by `ν : ι → ℤ`, with vertices
  `ν i / n` and of side length `1 / n`.

* `BoxIntegral.unitPartition.admissibleIndex`: For `B : BoxIntegral.Box`, the set of indices of
  `unitPartition.box` that are subsets of `B`. This is a finite set.

* `BoxIntegral.unitPartition.prepartition_isPartition`: For `B : BoxIntegral.Box`, if `B`
  has integral vertices, then the prepartition of `unitPartition.box` admissible for `B` is a
  partition of `B`.

* `tendsto_tsum_div_pow_atTop_integral`: let `s` be a bounded, measurable set of `ι → ℝ`
  whose frontier has zero volume and let `F` be a continuous function. Then the limit as `n → ∞`
  of `∑ F x / n ^ card ι`, where the sum is over the points in `s ∩ n⁻¹ • (ι → ℤ)`, tends to the
  integral of `F` over `s`.

* `tendsto_card_div_pow_atTop_volume`: let `s` be a bounded, measurable set of `ι → ℝ` whose
  frontier has zero volume. Then the limit as `n → ∞` of `card (s ∩ n⁻¹ • (ι → ℤ)) / n ^ card ι`
  tends to the volume of `s`.

* `tendsto_card_div_pow_atTop_volume'`: a version of `tendsto_card_div_pow_atTop_volume` where we
  assume in addition that `x • s ⊆ y • s` whenever `0 < x ≤ y`. Then we get the same limit
  `card (s ∩ x⁻¹ • (ι → ℤ)) / x ^ card ι → volume s` but the limit is over a real variable `x`.

-/

@[expose] public section

noncomputable section

variable {ι : Type*}

open scoped Topology

section hasIntegralVertices

open Bornology

/-- A `BoxIntegral.Box` has integral vertices if its vertices have coordinates in `ℤ`. -/
/-
**BoxIntegral.hasIntegralVertices** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：BoxIntegral.hasIntegralVertices (B : Box ι) : Prop
参数：B : Box ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `BoxIntegral.Box` has integral vertices if its vertices have coordinates in `ℤ
`.
-/
def BoxIntegral.hasIntegralVertices (B : Box ι) : Prop :=
  ∃ l u : ι → ℤ, (∀ i, B.lower i = l i) ∧ (∀ i, B.upper i = u i)

/-- Any bounded set is contained in a `BoxIntegral.Box` with integral vertices. -/
/-
**BoxIntegral.le_hasIntegralVertices_of_isBounded** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：BoxIntegral.le_hasIntegralVertices_of_isBounded [Finite ι] {s : Set (ι -> 
Real)} (h : IsBounded s) : exists B : BoxIntegral.Box ι, hasIntegralVertices B ∧
 s <= B
参数：ι -> Real；h : IsBounded s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Bornology.IsBounded.subset_ball_lt`：∀ {α : Type u} {s : Set α} [inst : P
seudoMetricSpace α],   Bornology.IsBounded s → ∀ (a : ℝ) (c : α), ∃ r, a < r ∧ s
 ⊆ Metric.ball c r
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.ceil_pos`：ceil_pos : 0 < ⌈a⌉₊ ↔ 0 < a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.cast_neg_natCast`：cast_neg_natCast {R} [DivisionRing R] (n : Nat) : 
((-n : Int) : R) = -n
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `pi_norm_lt_iff`：∀ {ι : Type u_1} {G : ι → Type u_4} [inst : Fintype ι] [
inst_1 : (i : ι) → SeminormedAddGroup (G i)] {x : (i : ι) → G i}   {r : ℝ}, 0 < 
r → …
· 使用定理 `Nat.cast_pos`：cast_pos {α} [Semiring α] [PartialOrder α] [IsOrderedRing 
α] [Nontrivial α] {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Metric.ball_subset_ball`：ball_subset_ball (h : ε₁ <= ε₂) : ball x ε₁ sub
seteq ball x ε₂
· 使用定理 `Nat.le_ceil`：le_ceil (a : R) : a <= ⌈a⌉₊

--- 原说明 ---
Any bounded set is contained in a `BoxIntegral.Box` with integral vertices.
-/
theorem BoxIntegral.le_hasIntegralVertices_of_isBounded [Finite ι] {s : Set (ι → ℝ)}
    (h : IsBounded s) :
    ∃ B : BoxIntegral.Box ι, hasIntegralVertices B ∧ s ≤ B := by
  have := Fintype.ofFinite ι
  obtain ⟨R, hR₁, hR₂⟩ := IsBounded.subset_ball_lt h 0 0
  let C : ℕ := ⌈R⌉₊
  have hC := Nat.ceil_pos.mpr hR₁
  let I : Box ι := Box.mk (fun _ ↦ -C) (fun _ ↦ C)
    (fun _ ↦ by simp [C, neg_lt_self_iff, Nat.cast_pos, hC])
  refine ⟨I, ⟨fun _ ↦ - C, fun _ ↦ C, fun i ↦ (Int.cast_neg_natCast C).symm, fun _ ↦ rfl⟩,
    le_trans hR₂ ?_⟩
  suffices Metric.ball (0 : ι → ℝ) C ≤ I from
    le_trans (Metric.ball_subset_ball (Nat.le_ceil R)) this
  intro x hx
  simp_rw [C, mem_ball_zero_iff, pi_norm_lt_iff (Nat.cast_pos.mpr hC),
    Real.norm_eq_abs, abs_lt] at hx
  exact fun i ↦ ⟨(hx i).1, le_of_lt (hx i).2⟩

end hasIntegralVertices

namespace BoxIntegral.unitPartition

open Bornology MeasureTheory Fintype BoxIntegral

variable (n : ℕ)

/-- A `BoxIntegral`, indexed by a positive integer `n` and `ν : ι → ℤ`, with corners `ν i / n`
and of side length `1 / n`. -/
/-
**BoxIntegral.unitPartition.box** 是 Mathlib 中的一个定义，位于命名空间 `BoxIntegral.unitParti
tion`。
形式化陈述：box [NeZero n] (ν : ι -> Int) : Box ι where lower
参数：ν : ι -> Int。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `BoxIntegral`, indexed by a positive integer `n` and `ν : ι → ℤ`, with corners
 `ν i / n`
and of side length `1 / n`.
-/
def box [NeZero n] (ν : ι → ℤ) : Box ι where
  lower := fun i ↦ ν i / n
  upper := fun i ↦ (ν i + 1) / n
  lower_lt_upper := fun _ ↦ by simp [add_div, n.pos_of_neZero]

@[simp]
/-
**BoxIntegral.unitPartition.box_lower** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.uni
tPartition`。
形式化陈述：box_lower [NeZero n] (ν : ι -> Int) : (box n ν).lower = fun i => (ν i / n 
: Real)
参数：ν : ι -> Int。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem box_lower [NeZero n] (ν : ι → ℤ) :
    (box n ν).lower = fun i ↦ (ν i / n : ℝ) := rfl

@[simp]
/-
**BoxIntegral.unitPartition.box_upper** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.uni
tPartition`。
形式化陈述：box_upper [NeZero n] (ν : ι -> Int) : (box n ν).upper = fun i => ((ν i + 1
) / n : Real)
参数：ν : ι -> Int。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem box_upper [NeZero n] (ν : ι → ℤ) :
    (box n ν).upper = fun i ↦ ((ν i + 1) / n : ℝ) := rfl

variable {n} in
@[simp]
/-
**BoxIntegral.unitPartition.mem_box_iff** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.u
nitPartition`。
形式化陈述：mem_box_iff [NeZero n] {ν : ι -> Int} {x : ι -> Real} : x in box n ν ↔ for
all i, ν i / n < x i ∧ x i <= (ν i + 1) / n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_box_iff [NeZero n] {ν : ι → ℤ} {x : ι → ℝ} :
    x ∈ box n ν ↔ ∀ i, ν i / n < x i ∧ x i ≤ (ν i + 1) / n := by
  simp_rw [Box.mem_def, box, Set.mem_Ioc]

variable {n} in
/-
**BoxIntegral.unitPartition.mem_box_iff'** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.
unitPartition`。
形式化陈述：mem_box_iff' [NeZero n] {ν : ι -> Int} {x : ι -> Real} : x in box n ν ↔ fo
rall i, ν i < n * x i ∧ n * x i <= ν i + 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_pos`：cast_pos {α} [Semiring α] [PartialOrder α] [IsOrderedRing 
α] [Nontrivial α] {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `Nat.pos_of_neZero`：∀ (n : ℕ) [NeZero n], 0 < n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `le_div_iff₀'`：le_div_iff₀' (hc : 0 < c) : a <= b / c ↔ c * a <= b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `div_lt_iff₀'`：div_lt_iff₀' (hc : 0 < c) : b / c < a ↔ b < c * a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_box_iff' [NeZero n] {ν : ι → ℤ} {x : ι → ℝ} :
    x ∈ box n ν ↔ ∀ i, ν i < n * x i ∧ n * x i ≤ ν i + 1 := by
  have h : 0 < (n : ℝ) := Nat.cast_pos.mpr <| n.pos_of_neZero
  simp_rw [mem_box_iff, ← _root_.le_div_iff₀' h, ← div_lt_iff₀' h]

/-- The tag of (the index of) a `unitPartition.box`. -/
/-
**BoxIntegral.unitPartition.tag** 是 Mathlib 中的一个缩写定义，位于命名空间 `BoxIntegral.unitPar
tition`。
形式化陈述：tag (ν : ι -> Int) : ι -> Real
参数：ν : ι -> Int。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The tag of (the index of) a `unitPartition.box`.
-/
abbrev tag (ν : ι → ℤ) : ι → ℝ := fun i ↦ (ν i + 1) / n

@[simp]
/-
**BoxIntegral.unitPartition.tag_apply** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.uni
tPartition`。
形式化陈述：tag_apply (ν : ι -> Int) (i : ι) : tag n ν i = (ν i + 1) / n
参数：ν : ι -> Int；i : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem tag_apply (ν : ι → ℤ) (i : ι) : tag n ν i = (ν i + 1) / n := rfl

variable [NeZero n]
/-
**BoxIntegral.unitPartition.tag_injective** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral
.unitPartition`。
形式化陈述：tag_injective : Function.Injective (fun ν : ι -> Int => tag n ν)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `funext_iff`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g
 ↔ ∀ (x : α), f x = g x
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `div_left_inj'`：div_left_inj' (hc : c != 0) : a / c = b / c ↔ a = b
· 使用定理 `Nat.cast_ne_zero`：cast_ne_zero {n : Nat} : (n : R) != 0 ↔ n != 0
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
-/
theorem tag_injective : Function.Injective (fun ν : ι → ℤ ↦ tag n ν) := by
  refine fun _ _ h ↦ funext_iff.mpr fun i ↦ ?_
  have := congr_arg (fun x ↦ x i) h
  simp_rw [tag_apply, div_left_inj' (c := (n : ℝ)) (Nat.cast_ne_zero.mpr (NeZero.ne n)),
    add_left_inj, Int.cast_inj] at this
  exact this
/-
**BoxIntegral.unitPartition.tag_mem** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.unitP
artition`。
形式化陈述：tag_mem (ν : ι -> Int) : tag n ν in box n ν
参数：ν : ι -> Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `BoxIntegral.unitPartition.mem_box_iff`：mem_box_iff [NeZero n] {ν : ι -> 
Int} {x : ι -> Real} : x in box n ν ↔ forall i, ν i / n < x i ∧ x i <= (ν i + 1)
 / n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `BoxIntegral.unitPartition.tag.eq_1`：∀ {ι : Type u_1} (n : ℕ) (ν : ι → ℤ)
 (i : ι), BoxIntegral.unitPartition.tag n ν i = (↑(ν i) + 1) / ↑n
· 使用定理 `add_div`：add_div (a b c : K) : (a + b) / c = a / c + b / c
· 使用定理 `Nat.cast_pos`：cast_pos {α} [Semiring α] [PartialOrder α] [IsOrderedRing 
α] [Nontrivial α] {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `Nat.pos_of_neZero`：∀ (n : ℕ) [NeZero n], 0 < n
· 使用定理 `lt_add_of_pos_right`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : 
LT α] [AddLeftStrictMono α] (a : α) {b : α}, 0 < b → a < a + b
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem tag_mem (ν : ι → ℤ) :
    tag n ν ∈ box n ν := by
  refine mem_box_iff.mpr fun _ ↦ ?_
  rw [tag, add_div]
  have h : 0 < (n : ℝ) := Nat.cast_pos.mpr <| n.pos_of_neZero
  exact ⟨lt_add_of_pos_right _ (by positivity), le_rfl⟩

/-- For `x : ι → ℝ`, its index is the index of the unique `unitPartition.box` to which
it belongs. -/
/-
**BoxIntegral.unitPartition.index** 是 Mathlib 中的一个定义，位于命名空间 `BoxIntegral.unitPar
tition`。
形式化陈述：index (x : ι -> Real) (i : ι) : Int
参数：x : ι -> Real；i : ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For `x : ι → ℝ`, its index is the index of the unique `unitPartition.box` to whi
ch
it belongs.
-/
def index (x : ι → ℝ) (i : ι) : ℤ := ⌈n * x i⌉ - 1

@[simp]
/-
**BoxIntegral.unitPartition.index_apply** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.u
nitPartition`。
形式化陈述：index_apply (m : Nat) {x : ι -> Real} (i : ι) : index m x i = ⌈m * x i⌉ - 
1
参数：m : Nat；i : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem index_apply (m : ℕ) {x : ι → ℝ} (i : ι) :
    index m x i = ⌈m * x i⌉ - 1 := rfl

variable {n} in
/-
**BoxIntegral.unitPartition.mem_box_iff_index** 是 Mathlib 中的一个定理，位于命名空间 `BoxInte
gral.unitPartition`。
形式化陈述：mem_box_iff_index {x : ι -> Real} {ν : ι -> Int} : x in box n ν ↔ index n 
x = ν
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Int.cast_add`：∀ {R : Type u} [inst : AddGroupWithOne R] (m n : ℤ), ↑(m +
 n) = ↑m + ↑n
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_box_iff_index {x : ι → ℝ} {ν : ι → ℤ} :
    x ∈ box n ν ↔ index n x = ν := by
  simp_rw [mem_box_iff', funext_iff, index_apply, sub_eq_iff_eq_add, Int.ceil_eq_iff,
    Int.cast_add, Int.cast_one, add_sub_cancel_right]

@[simp]
/-
**BoxIntegral.unitPartition.index_tag** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.uni
tPartition`。
形式化陈述：index_tag (ν : ι -> Int) : index n (tag n ν) = ν
参数：ν : ι -> Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `BoxIntegral.unitPartition.mem_box_iff_index`：mem_box_iff_index {x : ι ->
 Real} {ν : ι -> Int} : x in box n ν ↔ index n x = ν
· 使用定理 `BoxIntegral.unitPartition.tag_mem`：tag_mem (ν : ι -> Int) : tag n ν in b
ox n ν
-/
theorem index_tag (ν : ι → ℤ) :
    index n (tag n ν) = ν := mem_box_iff_index.mp (tag_mem n ν)

variable {n} in
/-
**BoxIntegral.unitPartition.disjoint** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.unit
Partition`。
形式化陈述：disjoint {ν ν' : ι -> Int} : ν != ν' ↔ Disjoint (box n ν).toSet (box n ν')
.toSet
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_iff_comm`：not_iff_comm : (¬a ↔ b) ↔ (¬b ↔ a)
· 使用引理 `Set.not_disjoint_iff`：not_disjoint_iff : ¬Disjoint s t ↔ exists x, x in 
s ∧ x in t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `BoxIntegral.unitPartition.mem_box_iff_index`：mem_box_iff_index {x : ι ->
 Real} {ν : ι -> Int} : x in box n ν ↔ index n x = ν
· 使用定理 `BoxIntegral.unitPartition.tag_mem`：tag_mem (ν : ι -> Int) : tag n ν in b
ox n ν
-/
theorem disjoint {ν ν' : ι → ℤ} :
    ν ≠ ν' ↔ Disjoint (box n ν).toSet (box n ν').toSet := by
  rw [not_iff_comm, Set.not_disjoint_iff]
  refine ⟨fun ⟨x, hx, hx'⟩ ↦ ?_, fun h ↦ ⟨tag n ν, tag_mem n ν, h ▸ tag_mem n ν⟩⟩
  rw [← mem_box_iff_index.mp hx, ← mem_box_iff_index.mp hx']
/-
**BoxIntegral.unitPartition.box_injective** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral
.unitPartition`。
形式化陈述：box_injective : Function.Injective (fun ν : ι -> Int => box n ν)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `BoxIntegral.Box.ne_of_disjoint_coe`：ne_of_disjoint_coe (h : Disjoint (I 
: Set (ι -> Real)) J) : I != J
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `BoxIntegral.unitPartition.disjoint`：disjoint {ν ν' : ι -> Int} : ν != ν'
 ↔ Disjoint (box n ν).toSet (box n ν').toSet
-/
theorem box_injective : Function.Injective (fun ν : ι → ℤ ↦ box n ν) := by
  intro _ _ h
  contrapose! h
  exact Box.ne_of_disjoint_coe (disjoint.mp h)
/-
**BoxIntegral.unitPartition.box.upper_sub_lower** 是 Mathlib 中的一个定理，位于命名空间 `BoxIn
tegral.unitPartition.box`。
形式化陈述：∀ {ι : Type u_1} (n : ℕ) [inst : NeZero n] (ν : ι → ℤ) (i : ι),   (BoxInte
gral.unitPartition.box n ν).upper i - (BoxIntegral.unitPartition.box n ν).lower 
i = 1 / ↑n
参数：n : ℕ；ν : ι → ℤ；i : ι；BoxIntegral.unitPartition.box n ν；BoxIntegral.unitParti
tion.box n ν。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_div`：add_div (a b c : K) : (a + b) / c = a / c + b / c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma box.upper_sub_lower (ν : ι → ℤ) (i : ι) :
    (box n ν).upper i - (box n ν).lower i = 1 / n := by
  simp_rw [box, add_div, add_sub_cancel_left]

section fintype

variable [Fintype ι]

/-
**BoxIntegral.unitPartition.diam_boxIcc** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.u
nitPartition`。
形式化陈述：diam_boxIcc (ν : ι -> Int) : Metric.diam (Box.Icc (box n ν)) <= 1 / n
参数：ν : ι -> Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `BoxIntegral.Box.Icc_eq_pi`：Icc_eq_pi : Box.Icc I = pi univ fun i => Icc 
(I.lower i) (I.upper i)
· 使用定理 `ENNReal.toReal_le_of_le_ofReal`：toReal_le_of_le_ofReal {a : Real>=0∞} {b
 : Real} (hb : 0 <= b) (h : a <= ENNReal.ofReal b) : ENNReal.toReal a <= b
· 使用引理 `Mathlib.Meta.Positivity.div_nonneg_of_pos_of_nonneg`：div_nonneg_of_pos_o
f_nonneg [PosMulReflectLT α] (ha : 0 < a) (hb : 0 <= b) : 0 <= a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Nat.cast_nonneg'`：cast_nonneg' (n : Nat) : 0 <= (n : α)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Metric.ediam_pi_le_of_le`：ediam_pi_le_of_le {ι : Type*} {X : ι -> Type*}
 [Fintype ι] [forall i, PseudoEMetricSpace (X i)] {s : forall i : ι, Set (X i)} 
{c : Real>=0∞}…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Real.ediam_Icc`：ediam_Icc (a b : Real) : Metric.ediam (Icc a b) = ENNRea
l.ofReal (b - a)
· 使用定理 `BoxIntegral.unitPartition.box.upper_sub_lower`：∀ {ι : Type u_1} (n : ℕ) 
[inst : NeZero n] (ν : ι → ℤ) (i : ι),   (BoxIntegral.unitPartition.box n ν).upp
er i - (BoxIntegral.unitPartition.b…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
theorem diam_boxIcc (ν : ι → ℤ) :
    Metric.diam (Box.Icc (box n ν)) ≤ 1 / n := by
  rw [BoxIntegral.Box.Icc_eq_pi]
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) <| Metric.ediam_pi_le_of_le fun i ↦ ?_
  simp_rw [Real.ediam_Icc, box.upper_sub_lower, le_rfl]

@[simp]
/-
**BoxIntegral.unitPartition.volume_box** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.un
itPartition`。
形式化陈述：volume_box (ν : ι -> Int) : volume (box n ν : Set (ι -> Real)) = 1 / n ^ c
ard ι
参数：ν : ι -> Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `BoxIntegral.Box.coe_eq_pi`：coe_eq_pi : (I : Set (ι -> Real)) = pi univ f
un i => Ioc (I.lower i) (I.upper i)
· 使用定理 `MeasureTheory.Measure.pi_pi`：pi_pi [forall i, SigmaFinite (μ i)] (s : (i
 : ι) -> Set (α i)) : Measure.pi μ (pi univ s) = ∏ i, μ i (s i)
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.sigmaFinite`：∀ {G : Type u_1} [in
st : MeasurableSpace G] [inst_1 : AddGroup G] [inst_2 : TopologicalSpace G]   (μ
 : MeasureTheory.Measure G) [μ.IsAddHaar…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `SeparableWeaklyLocallyCompactAddGroup.sigmaCompactSpace`：∀ {G : Type w} 
[inst : TopologicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G]   [T
opologicalSpace.SeparableSpace G] [WeaklyLoca…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `instProperSpaceReal`：ProperSpace ℝ
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Real.volume_Ioc`：volume_Ioc {a b : Real} : volume (Ioc a b) = ofReal (b 
- a)
· 使用定理 `BoxIntegral.unitPartition.box.upper_sub_lower`：∀ {ι : Type u_1} (n : ℕ) 
[inst : NeZero n] (ν : ι → ℤ) (i : ι),   (BoxIntegral.unitPartition.box n ν).upp
er i - (BoxIntegral.unitPartition.b…
· 使用定理 `Finset.prod_const`：prod_const (b : M) : ∏ _x in s, b = b ^ #s
· 使用定理 `ENNReal.ofReal_div_of_pos`：ofReal_div_of_pos {x y : Real} (hy : 0 < y) :
 ENNReal.ofReal (x / y) = ENNReal.ofReal x / ENNReal.ofReal y
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_pos`：cast_pos {α} [Semiring α] [PartialOrder α] [IsOrderedRing 
α] [Nontrivial α] {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `Nat.pos_of_neZero`：∀ (n : ℕ) [NeZero n], 0 < n
· 使用定理 `ENNReal.ofReal_one`：ENNReal.ofReal 1 = 1
· 使用定理 `ENNReal.ofReal_natCast`：∀ (n : ℕ), ENNReal.ofReal ↑n = ↑n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `ENNReal.inv_pow`：∀ {a : ENNReal} {n : ℕ}, (a ^ n)⁻¹ = a⁻¹ ^ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem volume_box (ν : ι → ℤ) :
    volume (box n ν : Set (ι → ℝ)) = 1 / n ^ card ι := by
  simp_rw [volume_pi, BoxIntegral.Box.coe_eq_pi, Measure.pi_pi, Real.volume_Ioc,
    box.upper_sub_lower, Finset.prod_const, ENNReal.ofReal_div_of_pos (Nat.cast_pos.mpr
    n.pos_of_neZero), ENNReal.ofReal_one, ENNReal.ofReal_natCast, one_div, ENNReal.inv_pow,
    Finset.card_univ]
/-
**BoxIntegral.unitPartition.setFinite_index** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegr
al.unitPartition`。
形式化陈述：setFinite_index {s : Set (ι -> Real)} (hs₁ : NullMeasurableSet s) (hs₂ : v
olume s != ⊤) : Set.Finite {ν : ι -> Int | ↑(box n ν) subseteq s}
参数：ι -> Real；hs₁ : NullMeasurableSet s；hs₂ : volume s != ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `MeasureTheory.Measure.finite_const_le_meas_of_disjoint_iUnion₀`：finite_c
onst_le_meas_of_disjoint_iUnion₀ {ι : Type*} [MeasurableSpace α] (μ : Measure α)
 {ε : Real>=0∞} (ε_pos : 0 < ε) {As : ι -> Set α} (A…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `MeasureTheory.NullMeasurableSet.inter`：∀ {α : Type u_2} {m0 : Measurable
Space α} {μ : MeasureTheory.Measure α} {s t : Set α},   MeasureTheory.NullMeasur
ableSet s μ → MeasureTheory…
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
· 使用定理 `BoxIntegral.Box.measurableSet_coe`：measurableSet_coe : MeasurableSet (I 
: Set (ι -> Real))
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Disjoint.aedisjoint`：∀ {α : Type u_2} {m : MeasurableSpace α} {μ : Measu
reTheory.Measure α} {s t : Set α},   Disjoint s t → MeasureTheory.AEDisjoint μ s
 t
· 使用定理 `Disjoint.inter_left`：inter_left (u : Set α) (h : Disjoint s t) : Disjoin
t (s inter u) t
· 使用定理 `Disjoint.inter_right`：inter_right (u : Set α) (h : Disjoint s t) : Disjo
int s (t inter u)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `BoxIntegral.unitPartition.disjoint`：disjoint {ν ν' : ι -> Int} : ν != ν'
 ↔ Disjoint (box n ν).toSet (box n ν').toSet
· 使用定理 `lt_top_iff_ne_top`：lt_top_iff_ne_top : a < ⊤ ↔ a != ⊤
· 使用定理 `MeasureTheory.measure_lt_top_of_subset`：measure_lt_top_of_subset (hst : 
t subseteq s) (hs : μ s != ∞) : μ t < ∞
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Set.mem_ofPred`：mem_ofPred {a : α} {p : α -> Prop} : a in { x | p x } ↔ 
p a
· 使用定理 `Set.inter_eq_self_of_subset_left`：inter_eq_self_of_subset_left {s t : Se
t α} : s subseteq t -> s inter t = s
· 使用定理 `BoxIntegral.unitPartition.volume_box`：volume_box (ν : ι -> Int) : volume
 (box n ν : Set (ι -> Real)) = 1 / n ^ card ι
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem setFinite_index {s : Set (ι → ℝ)} (hs₁ : NullMeasurableSet s) (hs₂ : volume s ≠ ⊤) :
    Set.Finite {ν : ι → ℤ | ↑(box n ν) ⊆ s} := by
  refine (Measure.finite_const_le_meas_of_disjoint_iUnion₀ volume (ε := 1 / n ^ card ι)
    (by simp) (As := fun ν : ι → ℤ ↦ (box n ν) ∩ s) (fun ν ↦ ?_) (fun _ _ h ↦ ?_) ?_).subset
      (fun _ hν ↦ ?_)
  · refine NullMeasurableSet.inter ?_ hs₁
    exact (box n ν).measurableSet_coe.nullMeasurableSet
  · exact ((Disjoint.inter_right _ (disjoint.mp h)).inter_left _).aedisjoint
  · exact lt_top_iff_ne_top.mp <| measure_lt_top_of_subset
      (by simp only [Set.iUnion_subset_iff, Set.inter_subset_right, implies_true]) hs₂
  · rw [Set.mem_ofPred, Set.inter_eq_self_of_subset_left hν, volume_box]

/-- For `B : BoxIntegral.Box`, the set of indices of `unitPartition.box` that are subsets of `B`.
This is a finite set. These boxes cover `B` if it has integral vertices, see
`unitPartition.prepartition_isPartition`. -/
/-
**BoxIntegral.unitPartition.admissibleIndex** 是 Mathlib 中的一个定义，位于命名空间 `BoxIntegr
al.unitPartition`。
形式化陈述：admissibleIndex (B : Box ι) : Finset (ι -> Int)
参数：B : Box ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For `B : BoxIntegral.Box`, the set of indices of `unitPartition.box` that are su
bsets of `B`.
This is a finite set. These boxes cover `B` if it has integral vertices, see
`unitPartition.prepartition_isPartition`.
-/
def admissibleIndex (B : Box ι) : Finset (ι → ℤ) := by
  refine (setFinite_index n B.measurableSet_coe.nullMeasurableSet ?_).toFinset
  exact lt_top_iff_ne_top.mp (IsBounded.measure_lt_top B.isBounded)

variable {n} in
/-
**BoxIntegral.unitPartition.mem_admissibleIndex_iff** 是 Mathlib 中的一个定理，位于命名空间 `B
oxIntegral.unitPartition`。
形式化陈述：mem_admissibleIndex_iff {B : Box ι} {ν : ι -> Int} : ν in admissibleIndex 
n B ↔ box n ν <= B
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `BoxIntegral.unitPartition.admissibleIndex.eq_1`：∀ {ι : Type u_1} (n : ℕ)
 [inst : NeZero n] [inst_1 : Fintype ι] (B : BoxIntegral.Box ι),   BoxIntegral.u
nitPartition.admissibleIndex n B = ⋯…
· 使用定理 `Set.Finite.mem_toFinset`：∀ {α : Type u} {s : Set α} {a : α} (hs : s.Fini
te), a ∈ hs.toFinset ↔ a ∈ s
· 使用定理 `Set.mem_ofPred_eq`：mem_ofPred_eq {x : α} {p : α -> Prop} : (x in {y | p 
y}) = p x
· 使用定理 `BoxIntegral.Box.coe_subset_coe`：coe_subset_coe : (I : Set (ι -> Real)) s
ubseteq J ↔ I <= J
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_admissibleIndex_iff {B : Box ι} {ν : ι → ℤ} :
    ν ∈ admissibleIndex n B ↔ box n ν ≤ B := by
  rw [admissibleIndex, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, Box.coe_subset_coe]

open scoped Classical in
/-- For `B : BoxIntegral.Box`, the `TaggedPrepartition` formed by the set of all
`unitPartition.box` whose index is `B`-admissible. -/
/-
**BoxIntegral.unitPartition.prepartition** 是 Mathlib 中的一个定义，位于命名空间 `BoxIntegral.
unitPartition`。
形式化陈述：prepartition (B : Box ι) : TaggedPrepartition B where boxes
参数：B : Box ι。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `BoxIntegral.Box.exists_mem`：exists_mem : exists x, x in I

--- 原说明 ---
For `B : BoxIntegral.Box`, the `TaggedPrepartition` formed by the set of all
`unitPartition.box` whose index is `B`-admissible.
-/
def prepartition (B : Box ι) : TaggedPrepartition B where
  boxes := Finset.image (fun ν ↦ box n ν) (admissibleIndex n B)
  le_of_mem' _ hI := by
    obtain ⟨_, hν, rfl⟩ := Finset.mem_image.mp hI
    exact mem_admissibleIndex_iff.mp hν
  pairwiseDisjoint _ hI₁ _ hI₂ h := by
    obtain ⟨_, _, rfl⟩ := Finset.mem_image.mp hI₁
    obtain ⟨_, _, rfl⟩ := Finset.mem_image.mp hI₂
    exact disjoint.mp fun x ↦ h (congrArg (box n) x)
  tag I :=
    if hI : ∃ ν ∈ admissibleIndex n B, I = box n ν then tag n hI.choose else B.exists_mem.choose
  tag_mem_Icc I := by
    by_cases hI : ∃ ν ∈ admissibleIndex n B, I = box n ν
    · simp_rw [dif_pos hI]
      exact Box.coe_subset_Icc <| (mem_admissibleIndex_iff.mp hI.choose_spec.1) (tag_mem n _)
    · simp_rw [dif_neg hI]
      exact Box.coe_subset_Icc B.exists_mem.choose_spec

set_option backward.isDefEq.respectTransparency.types false in
variable {n} in
@[simp]
/-
**BoxIntegral.unitPartition.mem_prepartition_iff** 是 Mathlib 中的一个定理，位于命名空间 `BoxI
ntegral.unitPartition`。
形式化陈述：mem_prepartition_iff {B I : Box ι} : I in prepartition n B ↔ exists ν in a
dmissibleIndex n B, box n ν = I
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BoxIntegral.Box.exists_mem`：exists_mem : exists x, x in I
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `BoxIntegral.unitPartition.prepartition.eq_1`：∀ {ι : Type u_1} (n : ℕ) [i
nst : NeZero n] [inst_1 : Fintype ι] (B : BoxIntegral.Box ι),   BoxIntegral.unit
Partition.prepartition n B =     …
· 使用定理 `BoxIntegral.TaggedPrepartition.mem_mk`：mem_mk (π : Prepartition I) (f h)
 : J in mk π f h ↔ J in π
· 使用定理 `BoxIntegral.Prepartition.mem_mk`：mem_mk {s h₁ h₂} : J in (mk s h₁ h₂ : P
repartition I) ↔ J in s
· 使用定理 `Finset.mem_image`：mem_image : b in s.image f ↔ exists a in s, f a = b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_prepartition_iff {B I : Box ι} :
    I ∈ prepartition n B ↔ ∃ ν ∈ admissibleIndex n B, box n ν = I := by
  classical
  rw [prepartition, TaggedPrepartition.mem_mk, Prepartition.mem_mk, Finset.mem_image]

variable {n} in
/-
**BoxIntegral.unitPartition.mem_prepartition_boxes_iff** 是 Mathlib 中的一个定理，位于命名空间
 `BoxIntegral.unitPartition`。
形式化陈述：mem_prepartition_boxes_iff {B I : Box ι} : I in (prepartition n B).boxes ↔
 exists ν in admissibleIndex n B, box n ν = I
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BoxIntegral.unitPartition.mem_prepartition_iff`：mem_prepartition_iff {B 
I : Box ι} : I in prepartition n B ↔ exists ν in admissibleIndex n B, box n ν = 
I
-/
theorem mem_prepartition_boxes_iff {B I : Box ι} :
    I ∈ (prepartition n B).boxes ↔ ∃ ν ∈ admissibleIndex n B, box n ν = I :=
  mem_prepartition_iff
/-
**BoxIntegral.unitPartition.prepartition_tag** 是 Mathlib 中的一个定理，位于命名空间 `BoxInteg
ral.unitPartition`。
形式化陈述：prepartition_tag {ν : ι -> Int} {B : Box ι} (hν : ν in admissibleIndex n B
) : (prepartition n B).tag (box n ν) = tag n ν
参数：hν : ν in admissibleIndex n B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BoxIntegral.Box.exists_mem`：exists_mem : exists x, x in I
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `BoxIntegral.unitPartition.tag_injective`：tag_injective : Function.Inject
ive (fun ν : ι -> Int => tag n ν)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `BoxIntegral.unitPartition.box_injective`：box_injective : Function.Inject
ive (fun ν : ι -> Int => box n ν)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
theorem prepartition_tag {ν : ι → ℤ} {B : Box ι} (hν : ν ∈ admissibleIndex n B) :
    (prepartition n B).tag (box n ν) = tag n ν := by
  dsimp only [prepartition]
  have h : ∃ ν' ∈ admissibleIndex n B, box n ν = box n ν' := ⟨ν, hν, rfl⟩
  rw [dif_pos h, (tag_injective n).eq_iff, ← (box_injective n).eq_iff]
  exact h.choose_spec.2.symm
/-
**BoxIntegral.unitPartition.box_index_tag_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `Box
Integral.unitPartition`。
形式化陈述：box_index_tag_eq_self {B I : Box ι} (hI : I in (prepartition n B).boxes) :
 box n (index n ((prepartition n B).tag I)) = I
参数：hI : I in (prepartition n B).boxes。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `BoxIntegral.unitPartition.mem_prepartition_boxes_iff`：mem_prepartition_b
oxes_iff {B I : Box ι} : I in (prepartition n B).boxes ↔ exists ν in admissibleI
ndex n B, box n ν = I
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `BoxIntegral.unitPartition.prepartition_tag`：prepartition_tag {ν : ι -> I
nt} {B : Box ι} (hν : ν in admissibleIndex n B) : (prepartition n B).tag (box n 
ν) = tag n ν
· 使用定理 `BoxIntegral.unitPartition.index_tag`：index_tag (ν : ι -> Int) : index n 
(tag n ν) = ν
-/
theorem box_index_tag_eq_self {B I : Box ι} (hI : I ∈ (prepartition n B).boxes) :
    box n (index n ((prepartition n B).tag I)) = I := by
  obtain ⟨ν, hν, rfl⟩ := mem_prepartition_boxes_iff.mp hI
  rw [prepartition_tag n hν, index_tag]
/-
**BoxIntegral.unitPartition.prepartition_isHenstock** 是 Mathlib 中的一个定理，位于命名空间 `B
oxIntegral.unitPartition`。
形式化陈述：prepartition_isHenstock (B : Box ι) : (prepartition n B).IsHenstock
参数：B : Box ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `BoxIntegral.unitPartition.mem_prepartition_iff`：mem_prepartition_iff {B 
I : Box ι} : I in prepartition n B ↔ exists ν in admissibleIndex n B, box n ν = 
I
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `BoxIntegral.unitPartition.prepartition_tag`：prepartition_tag {ν : ι -> I
nt} {B : Box ι} (hν : ν in admissibleIndex n B) : (prepartition n B).tag (box n 
ν) = tag n ν
· 使用定理 `BoxIntegral.Box.coe_subset_Icc`：coe_subset_Icc : ↑I subseteq Box.Icc I
· 使用定理 `BoxIntegral.unitPartition.tag_mem`：tag_mem (ν : ι -> Int) : tag n ν in b
ox n ν
-/
theorem prepartition_isHenstock (B : Box ι) :
    (prepartition n B).IsHenstock := by
  intro _ hI
  obtain ⟨ν, hν, rfl⟩ := mem_prepartition_iff.mp hI
  rw [prepartition_tag n hν]
  exact Box.coe_subset_Icc (tag_mem _ _)
/-
**BoxIntegral.unitPartition.prepartition_isSubordinate** 是 Mathlib 中的一个定理，位于命名空间
 `BoxIntegral.unitPartition`。
形式化陈述：prepartition_isSubordinate (B : Box ι) {r : Real} (hr : 0 < r) (hn : 1 / n
 <= r) : (prepartition n B).IsSubordinate (fun _ => ⟨r, hr⟩)
参数：B : Box ι；hr : 0 < r；hn : 1 / n <= r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `BoxIntegral.unitPartition.mem_prepartition_iff`：mem_prepartition_iff {B 
I : Box ι} : I in prepartition n B ↔ exists ν in admissibleIndex n B, box n ν = 
I
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Metric.dist_le_diam_of_mem`：dist_le_diam_of_mem (h : IsBounded s) (hx : 
x in s) (hy : y in s) : dist x y <= diam s
· 使用定理 `BoxIntegral.Box.isBounded_Icc`：isBounded_Icc [Finite ι] (I : Box ι) : Bo
rnology.IsBounded (Box.Icc I)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `BoxIntegral.unitPartition.prepartition_tag`：prepartition_tag {ν : ι -> I
nt} {B : Box ι} (hν : ν in admissibleIndex n B) : (prepartition n B).tag (box n 
ν) = tag n ν
· 使用定理 `BoxIntegral.Box.coe_subset_Icc`：coe_subset_Icc : ↑I subseteq Box.Icc I
· 使用定理 `BoxIntegral.unitPartition.tag_mem`：tag_mem (ν : ι -> Int) : tag n ν in b
ox n ν
· 使用定理 `BoxIntegral.unitPartition.diam_boxIcc`：diam_boxIcc (ν : ι -> Int) : Metr
ic.diam (Box.Icc (box n ν)) <= 1 / n
-/
theorem prepartition_isSubordinate (B : Box ι) {r : ℝ} (hr : 0 < r) (hn : 1 / n ≤ r) :
    (prepartition n B).IsSubordinate (fun _ ↦ ⟨r, hr⟩) := by
  intro _ hI
  obtain ⟨ν, hν, rfl⟩ := mem_prepartition_iff.mp hI
  refine fun _ h ↦ le_trans (Metric.dist_le_diam_of_mem (Box.isBounded_Icc _) h ?_) ?_
  · rw [prepartition_tag n hν]
    exact Box.coe_subset_Icc (tag_mem _ _)
  · exact le_trans (diam_boxIcc n ν) hn
/-
**BoxIntegral.unitPartition.mem_admissibleIndex_of_mem_box_aux** 是 Mathlib 中的一个定
理，位于命名空间 `BoxIntegral.unitPartition`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem mem_admissibleIndex_of_mem_box_aux₁ (x : ℝ) (a : ℤ) :
    a < x ↔ a ≤ (⌈n * x⌉ - 1) / (n : ℝ) := by
  have h : 0 < (n : ℝ) := Nat.cast_pos.mpr <| n.pos_of_neZero
  rw [le_div_iff₀' h, le_sub_iff_add_le,
    show (n : ℝ) * a + 1 = (n * a + 1 : ℤ) by norm_cast,
    Int.cast_le, Int.add_one_le_iff, Int.lt_ceil, Int.cast_mul, Int.cast_natCast,
    mul_lt_mul_iff_right₀ h]
/-
**BoxIntegral.unitPartition.mem_admissibleIndex_of_mem_box_aux** 是 Mathlib 中的一个定
理，位于命名空间 `BoxIntegral.unitPartition`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem mem_admissibleIndex_of_mem_box_aux₂ (x : ℝ) (a : ℤ) :
    x ≤ a ↔ (⌈n * x⌉ - 1 + 1) / (n : ℝ) ≤ a := by
  have h : 0 < (n : ℝ) := Nat.cast_pos.mpr <| n.pos_of_neZero
  rw [sub_add_cancel, div_le_iff₀' h,
    show (n : ℝ) * a = (n * a : ℤ) by norm_cast,
    Int.cast_le, Int.ceil_le, Int.cast_mul, Int.cast_natCast, mul_le_mul_iff_right₀ h]

/-- If `B : BoxIntegral.Box` has integral vertices and contains the point `x`, then the index of
`x` is admissible for `B`. -/
/-
**BoxIntegral.unitPartition.mem_admissibleIndex_of_mem_box** 是 Mathlib 中的一个定理，位于
命名空间 `BoxIntegral.unitPartition`。
形式化陈述：mem_admissibleIndex_of_mem_box {B : Box ι} (hB : hasIntegralVertices B) {x
 : ι -> Real} (hx : x in B) : index n x in admissibleIndex n B
参数：hB : hasIntegralVertices B；hx : x in B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Int.cast_sub`：cast_sub (m n) : ((m - n : Int) : R) = m - n
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `_private.Mathlib.Analysis.BoxIntegral.UnitPartition.0.BoxIntegral.unitPa
rtition.mem_admissibleIndex_of_mem_box_aux₁`：∀ (n : ℕ) [NeZero n] (x : ℝ) (a : ℤ
), ↑a < x ↔ ↑a ≤ (↑⌈↑n * x⌉ - 1) / ↑n
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `_private.Mathlib.Analysis.BoxIntegral.UnitPartition.0.BoxIntegral.unitPa
rtition.mem_admissibleIndex_of_mem_box_aux₂`：∀ (n : ℕ) [NeZero n] (x : ℝ) (a : ℤ
), x ≤ ↑a ↔ (↑⌈↑n * x⌉ - 1 + 1) / ↑n ≤ ↑a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
If `B : BoxIntegral.Box` has integral vertices and contains the point `x`, then 
the index of
`x` is admissible for `B`.
-/
theorem mem_admissibleIndex_of_mem_box {B : Box ι} (hB : hasIntegralVertices B) {x : ι → ℝ}
    (hx : x ∈ B) : index n x ∈ admissibleIndex n B := by
  obtain ⟨l, u, hl, hu⟩ := hB
  simp_rw [mem_admissibleIndex_iff, Box.le_iff_bounds, box_lower, box_upper, Pi.le_def,
    index_apply, hl, hu, ← forall_and]
  push_cast
  refine fun i ↦ ⟨?_, ?_⟩
  · exact (mem_admissibleIndex_of_mem_box_aux₁ n (x i) (l i)).mp ((hl i) ▸ (hx i).1)
  · exact (mem_admissibleIndex_of_mem_box_aux₂ n (x i) (u i)).mp ((hu i) ▸ (hx i).2)

/-- If `B : BoxIntegral.Box` has integral vertices, then `prepartition n B` is a partition of
`B`. -/
/-
**BoxIntegral.unitPartition.prepartition_isPartition** 是 Mathlib 中的一个定理，位于命名空间 `
BoxIntegral.unitPartition`。
形式化陈述：prepartition_isPartition {B : Box ι} (hB : hasIntegralVertices B) : (prepa
rtition n B).IsPartition
参数：hB : hasIntegralVertices B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `BoxIntegral.TaggedPrepartition.mem_toPrepartition`：mem_toPrepartition {π
 : TaggedPrepartition I} : J in π.toPrepartition ↔ J in π
· 使用定理 `BoxIntegral.unitPartition.mem_prepartition_iff`：mem_prepartition_iff {B 
I : Box ι} : I in prepartition n B ↔ exists ν in admissibleIndex n B, box n ν = 
I
· 使用定理 `BoxIntegral.unitPartition.mem_admissibleIndex_of_mem_box`：mem_admissible
Index_of_mem_box {B : Box ι} (hB : hasIntegralVertices B) {x : ι -> Real} (hx : 
x in B) : index n x in admissibleIndex n B
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `BoxIntegral.unitPartition.mem_box_iff_index`：mem_box_iff_index {x : ι ->
 Real} {ν : ι -> Int} : x in box n ν ↔ index n x = ν

--- 原说明 ---
If `B : BoxIntegral.Box` has integral vertices, then `prepartition n B` is a par
tition of
`B`.
-/
theorem prepartition_isPartition {B : Box ι} (hB : hasIntegralVertices B) :
    (prepartition n B).IsPartition := by
  refine fun x hx ↦ ⟨box n (index n x), ?_, mem_box_iff_index.mpr rfl⟩
  rw [TaggedPrepartition.mem_toPrepartition, mem_prepartition_iff]
  exact ⟨index n x, mem_admissibleIndex_of_mem_box n hB hx, rfl⟩

end fintype

open Submodule Pointwise

open scoped Pointwise

variable (c : ℝ) (s : Set (ι → ℝ)) (F : (ι → ℝ) → ℝ)

-- The image of `ι → ℤ` inside `ι → ℝ`
local notation "L" => span ℤ (Set.range (Pi.basisFun ℝ ι))

section finite

variable [Finite ι]

variable {n} in
/-
**BoxIntegral.unitPartition.mem_smul_span_iff** 是 Mathlib 中的一个定理，位于命名空间 `BoxInte
gral.unitPartition`。
形式化陈述：mem_smul_span_iff {v : ι -> Real} : v in (n : Real)⁻¹ • L ↔ forall i, n * 
v i in Set.range (algebraMap Int Real)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ne.isUnit`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 →
 IsUnit a
· 使用定理 `inv_ne_zero`：inv_ne_zero (h : a != 0) : a⁻¹ != 0
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ZSpan.smul`：smul {c : K} (hc : c != 0) : c • span Int (Set.range b) = sp
an Int (Set.range (b.isUnitSMul (fun _ => hc.isUnit)))
· 使用定理 `Module.Basis.mem_span_iff_repr_mem`：∀ {ι : Type u_1} (R : Type u_3) {M :
 Type u_5} {S : Type u_7} [inst : CommRing R] [IsDomain R] [inst_2 : Ring S]   [
Nontrivial S] [inst_4 : …
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `instIsTorsionFreeIntOfIsAddTorsionFree`：∀ {M : Type u_3} [inst : AddComm
Group M] [IsAddTorsionFree M], Module.IsTorsionFree ℤ M
· 使用定理 `instIsAddTorsionFreeOfAddLeftStrictMonoOfAddRightStrictMono`：∀ {M : Type
 u_3} [inst : AddMonoid M] [inst_1 : LinearOrder M] [AddLeftStrictMono M] [AddRi
ghtStrictMono M],   IsAddTorsionFree M
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Module.Basis.repr_isUnitSMul`：repr_isUnitSMul {v : Basis ι R₂ M} {w : ι 
-> R₂} (hw : forall i, IsUnit (w i)) (x : M) (i : ι) : (v.isUnitSMul hw).repr x 
i = (hw i).unit⁻¹ …
· 使用定理 `Pi.basisFun_repr`：basisFun_repr (x : η -> R) (i : η) : (Pi.basisFun R η)
.repr x i = x i
· 使用定理 `Units.val_inv_eq_inv_val`：∀ {α : Type u} [inst : DivisionMonoid α] (u : 
αˣ), ↑u⁻¹ = (↑u)⁻¹
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_smul_span_iff {v : ι → ℝ} :
    v ∈ (n : ℝ)⁻¹ • L ↔ ∀ i, n * v i ∈ Set.range (algebraMap ℤ ℝ) := by
  have := Fintype.ofFinite ι
  rw [ZSpan.smul _ (inv_ne_zero (NeZero.ne _)), Module.Basis.mem_span_iff_repr_mem]
  simp_rw [Module.Basis.repr_isUnitSMul, Pi.basisFun_repr, Units.smul_def, Units.val_inv_eq_inv_val,
    IsUnit.unit_spec, inv_inv, smul_eq_mul]
/-
**BoxIntegral.unitPartition.tag_mem_smul_span** 是 Mathlib 中的一个定理，位于命名空间 `BoxInte
gral.unitPartition`。
形式化陈述：tag_mem_smul_span (ν : ι -> Int) : tag n ν in (n : Real)⁻¹ • L
参数：ν : ι -> Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `BoxIntegral.unitPartition.mem_smul_span_iff`：mem_smul_span_iff {v : ι ->
 Real} : v in (n : Real)⁻¹ • L ↔ forall i, n * v i in Set.range (algebraMap Int 
Real)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `BoxIntegral.unitPartition.tag_apply`：tag_apply (ν : ι -> Int) (i : ι) : 
tag n ν i = (ν i + 1) / n
· 使用定理 `div_eq_inv_mul`：div_eq_inv_mul : a / b = b⁻¹ * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_inv_cancel_of_invertible`：mul_inv_cancel_of_invertible (a : α) [Inve
rtible a] : a * a⁻¹ = 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `eq_intCast`：eq_intCast [FunLike F Int α] [RingHomClass F Int α] (f : F) 
(n : Int) : f n = n
-/
theorem tag_mem_smul_span (ν : ι → ℤ) :
    tag n ν ∈ (n : ℝ)⁻¹ • L := by
  refine mem_smul_span_iff.mpr fun i ↦ ⟨ν i + 1, ?_⟩
  rw [tag_apply, div_eq_inv_mul, ← mul_assoc, mul_inv_cancel_of_invertible, one_mul, map_add,
    map_one, eq_intCast]
/-
**BoxIntegral.unitPartition.tag_index_eq_self_of_mem_smul_span** 是 Mathlib 中的一个定
理，位于命名空间 `BoxIntegral.unitPartition`。
形式化陈述：tag_index_eq_self_of_mem_smul_span {x : ι -> Real} (hx : x in (n : Real)⁻¹
 • L) : tag n (index n x) = x
参数：hx : x in (n : Real)⁻¹ • L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `BoxIntegral.unitPartition.mem_smul_span_iff`：mem_smul_span_iff {v : ι ->
 Real} : v in (n : Real)⁻¹ • L ↔ forall i, n * v i in Set.range (algebraMap Int 
Real)
· 使用定理 `BoxIntegral.unitPartition.tag_apply`：tag_apply (ν : ι -> Int) (i : ι) : 
tag n ν i = (ν i + 1) / n
· 使用定理 `BoxIntegral.unitPartition.index_apply`：index_apply (m : Nat) {x : ι -> R
eal} (i : ι) : index m x i = ⌈m * x i⌉ - 1
· 使用定理 `Int.cast_sub`：cast_sub (m n) : ((m - n : Int) : R) = m - n
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.ceil_intCast`：ceil_intCast (z : Int) : ⌈(z : R)⌉ = z
· 使用引理 `div_eq_iff`：div_eq_iff (hb : b != 0) : a / b = c ↔ a = c * b
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem tag_index_eq_self_of_mem_smul_span {x : ι → ℝ} (hx : x ∈ (n : ℝ)⁻¹ • L) :
    tag n (index n x) = x := by
  rw [mem_smul_span_iff] at hx
  ext i
  obtain ⟨a, ha⟩ : ∃ a : ℤ, a = n * x i := hx i
  rwa [tag_apply, index_apply, Int.cast_sub, Int.cast_one, sub_add_cancel, ← ha, Int.ceil_intCast,
    div_eq_iff (NeZero.ne _), mul_comm]
/-
**BoxIntegral.unitPartition.eq_of_mem_smul_span_of_index_eq_index** 是 Mathlib 中的
一个定理，位于命名空间 `BoxIntegral.unitPartition`。
形式化陈述：eq_of_mem_smul_span_of_index_eq_index {x y : ι -> Real} (hx : x in (n : Re
al)⁻¹ • L) (hy : y in (n : Real)⁻¹ • L) (h : index n x = index n y) : x = y
参数：hx : x in (n : Real)⁻¹ • L；hy : y in (n : Real)⁻¹ • L；h : index n x = index n
 y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `BoxIntegral.unitPartition.tag_index_eq_self_of_mem_smul_span`：tag_index_
eq_self_of_mem_smul_span {x : ι -> Real} (hx : x in (n : Real)⁻¹ • L) : tag n (i
ndex n x) = x
-/
theorem eq_of_mem_smul_span_of_index_eq_index {x y : ι → ℝ} (hx : x ∈ (n : ℝ)⁻¹ • L)
    (hy : y ∈ (n : ℝ)⁻¹ • L) (h : index n x = index n y) : x = y := by
  rw [← tag_index_eq_self_of_mem_smul_span n hx, ← tag_index_eq_self_of_mem_smul_span n hy, h]
/-
**BoxIntegral.unitPartition.tendsto_card_div_pow** 是 Mathlib 中的一个定义，位于命名空间 `BoxI
ntegral.unitPartition`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private def tendsto_card_div_pow₁ {c : ℝ} (hc : c ≠ 0) :
    ↑(s ∩ c⁻¹ • L) ≃ ↑(c • s ∩ L) :=
  Equiv.subtypeEquiv (Equiv.smulRight hc) (fun x ↦ by
    simp_rw [Set.mem_inter_iff, Equiv.smulRight_apply, Set.smul_mem_smul_set_iff₀ hc,
      ← Set.mem_inv_smul_set_iff₀ hc])
/-
**BoxIntegral.unitPartition.tendsto_card_div_pow** 是 Mathlib 中的一个定理，位于命名空间 `BoxI
ntegral.unitPartition`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem tendsto_card_div_pow₂ (hs₁ : IsBounded s)
    (hs₄ : ∀ ⦃x y : ℝ⦄, 0 < x → x ≤ y → x • s ⊆ y • s) {x y : ℝ} (hx : 0 < x) (hy : x ≤ y) :
    Nat.card ↑(s ∩ x⁻¹ • L) ≤ Nat.card ↑(s ∩ y⁻¹ • L) := by
  have := Fintype.ofFinite ι
  rw [Nat.card_congr (tendsto_card_div_pow₁ s hx.ne'),
      Nat.card_congr (tendsto_card_div_pow₁ s (hx.trans_le hy).ne')]
  refine Nat.card_mono ?_ ?_
  · exact ZSpan.setFinite_inter _ (IsBounded.smul₀ hs₁ y)
  · exact Set.inter_subset_inter_left _ <| hs₄ hx hy

end finite

section fintype

variable [Fintype ι]

/-
**BoxIntegral.unitPartition.integralSum_eq_tsum_div** 是 Mathlib 中的一个定理，位于命名空间 `B
oxIntegral.unitPartition`。
形式化陈述：integralSum_eq_tsum_div {B : Box ι} (hB : hasIntegralVertices B) (hs₀ : s 
<= B) : integralSum (Set.indicator s F) (BoxAdditiveMap.toSMul (Measure.toBoxAdd
itive volume)) (prepartition n B) = (∑' x : ↑(s inter (n : Real)⁻¹ • L), F x) / 
n ^ card ι
参数：hB : hasIntegralVertices B；hs₀ : s <= B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `MeasureTheory.Measure.instIsLocallyFiniteMeasureForallVolumeOfSigmaFinit
e`：∀ {ι : Type u_1} [inst : Fintype ι] {X : ι → Type u_4} [inst_1 : (i : ι) → To
pologicalSpace (X i)]   [inst_2 : (i : ι) → MeasureTheory.Measu…
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.sigmaFinite`：∀ {G : Type u_1} [in
st : MeasurableSpace G] [inst_1 : AddGroup G] [inst_2 : TopologicalSpace G]   (μ
 : MeasureTheory.Measure G) [μ.IsAddHaar…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `SeparableWeaklyLocallyCompactAddGroup.sigmaCompactSpace`：∀ {G : Type w} 
[inst : TopologicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G]   [T
opologicalSpace.SeparableSpace G] [WeaklyLoca…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `instProperSpaceReal`：ProperSpace ℝ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.coe_pointwise_smul`：coe_pointwise_smul (a : α) (S : Submodule 
R M) : ↑(a • S) = a • (S : Set M)
· 使用定理 `Ne.isUnit`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 →
 IsUnit a
· 使用定理 `inv_ne_zero`：inv_ne_zero (h : a != 0) : a⁻¹ != 0
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `ZSpan.smul`：smul {c : K} (hc : c != 0) : c • span Int (Set.range b) = sp
an Int (Set.range (b.isUnitSMul (fun _ => hc.isUnit)))
· 使用定理 `ZSpan.setFinite_inter`：setFinite_inter [ProperSpace E] [Finite ι] {s : S
et E} (hs : Bornology.IsBounded s) : Set.Finite (s inter span Int (Set.range b))
· 使用定理 `Bornology.IsBounded.subset`：∀ {α : Type u_2} {x : Bornology α} {s t : Se
t α}, Bornology.IsBounded t → s ⊆ t → Bornology.IsBounded s
· 使用定理 `BoxIntegral.Box.isBounded`：isBounded [Finite ι] (I : Box ι) : Bornology.
IsBounded I.toSet
· 使用定理 `tsum_fintype`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [
inst_1 : TopologicalSpace α] {L : SummationFilter β}   [L.LeAtTop] [inst_3 : Fin
ty…
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
· 使用定理 `Finset.sum_set_coe`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMonoi
d M] {f : ι → M} (s : Set ι) [inst_1 : Fintype ↑s],   ∑ i, f ↑i = ∑ i ∈ s.toFins
et, f i
· 使用引理 `Finset.sum_div`：Finset.sum_div (s : Finset ι) (f : ι -> K) (a : K) : (∑ 
i in s, f i) / a = ∑ i in s, f i / a
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Set.indicator_apply`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] (s 
: Set α) (f : α → M) (a : α) [inst_1 : Decidable (a ∈ s)],   s.indicator f a = i
f a ∈ s t…
· 使用定理 `apply_ite`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [inst 
: Decidable P] (x y : α),   f (if P then x else y) = if P then f x else f y
（共 59 条，此处仅展示前 30 条）
-/
theorem integralSum_eq_tsum_div {B : Box ι} (hB : hasIntegralVertices B) (hs₀ : s ≤ B) :
    integralSum (Set.indicator s F) (BoxAdditiveMap.toSMul (Measure.toBoxAdditive volume))
      (prepartition n B) = (∑' x : ↑(s ∩ (n : ℝ)⁻¹ • L), F x) / n ^ card ι := by
  classical
  unfold integralSum
  have : Fintype ↑(s ∩ (n : ℝ)⁻¹ • L) := by
    apply Set.Finite.fintype
    rw [← coe_pointwise_smul, ZSpan.smul _ (inv_ne_zero (NeZero.ne _))]
    exact ZSpan.setFinite_inter _ (B.isBounded.subset hs₀)
  rw [tsum_fintype, Finset.sum_set_coe, Finset.sum_div, eq_comm]
  simp_rw [Set.indicator_apply, apply_ite, BoxAdditiveMap.toSMul_apply, Measure.toBoxAdditive_apply,
    smul_eq_mul, mul_zero, Finset.sum_ite, Finset.sum_const_zero, add_zero]
  refine Finset.sum_bij (fun x _ ↦ box n (index n x)) (fun _ hx ↦ Finset.mem_filter.mpr ?_)
    (fun _ hx _ hy h ↦ ?_) (fun I hI ↦ ?_) (fun _ hx ↦ ?_)
  · rw [Set.mem_toFinset] at hx
    refine ⟨mem_prepartition_boxes_iff.mpr
      ⟨index n _, mem_admissibleIndex_of_mem_box n hB (hs₀ hx.1), rfl⟩, ?_⟩
    simp_rw [prepartition_tag n (mem_admissibleIndex_of_mem_box n hB (hs₀ hx.1)),
      tag_index_eq_self_of_mem_smul_span n hx.2, hx.1]
  · rw [Set.mem_toFinset] at hx hy
    exact eq_of_mem_smul_span_of_index_eq_index n hx.2 hy.2 (box_injective n h)
  · rw [Finset.mem_filter] at hI
    refine ⟨(prepartition n B).tag I, Set.mem_toFinset.mpr ⟨hI.2, ?_⟩, box_index_tag_eq_self n hI.1⟩
    rw [← box_index_tag_eq_self n hI.1, prepartition_tag n
      (mem_admissibleIndex_of_mem_box n hB (hs₀ hI.2))]
    exact tag_mem_smul_span _ _
  · rw [Set.mem_toFinset] at hx
    rw [measureReal_def, volume_box,
      prepartition_tag n (mem_admissibleIndex_of_mem_box n hB (hs₀ hx.1)),
      tag_index_eq_self_of_mem_smul_span n hx.2, ENNReal.toReal_div,
      ENNReal.toReal_one, ENNReal.toReal_pow, ENNReal.toReal_natCast, mul_comm_div, one_mul]

open Filter

/-- Let `s` be a bounded, measurable set of `ι → ℝ` whose frontier has zero volume and let `F`
be a continuous function. Then the limit as `n → ∞` of `∑ F x / n ^ card ι`, where the sum is
over the points in `s ∩ n⁻¹ • (ι → ℤ)`, tends to the integral of `F` over `s`. -/
/-
**BoxIntegral.unitPartition._root_.tendsto_tsum_div_pow_atTop_integral** 是 Mathl
ib 中的一个定理，位于命名空间 `BoxIntegral.unitPartition`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `s` be a bounded, measurable set of `ι → ℝ` whose frontier has zero volume a
nd let `F`
be a continuous function. Then the limit as `n → ∞` of `∑ F x / n ^ card ι`, whe
re the sum is
over the points in `s ∩ n⁻¹ • (ι → ℤ)`, tends to the integral of `F` over `s`.
-/
theorem _root_.tendsto_tsum_div_pow_atTop_integral (hF : Continuous F) (hs₁ : IsBounded s)
    (hs₂ : MeasurableSet s) (hs₃ : volume (frontier s) = 0) :
    Tendsto (fun n : ℕ ↦ (∑' x : ↑(s ∩ (n : ℝ)⁻¹ • L), F x) / n ^ card ι)
      atTop (nhds (∫ x in s, F x)) := by
  obtain ⟨B, hB, hs₀⟩ := le_hasIntegralVertices_of_isBounded hs₁
  refine Metric.tendsto_atTop.mpr fun ε hε ↦ ?_
  have h₁ : ∃ C, ∀ x ∈ Box.Icc B, ‖Set.indicator s F x‖ ≤ C := by
    obtain ⟨C₀, h₀⟩ := (Box.isCompact_Icc B).exists_bound_of_continuousOn hF.continuousOn
    refine ⟨max 0 C₀, fun x hx ↦ ?_⟩
    rw [Set.indicator]
    split_ifs with hs
    · exact le_max_of_le_right (h₀ x hx)
    · exact norm_zero.trans_le <| le_max_left 0 _
  have h₂ : ∀ᵐ x, ContinuousAt (s.indicator F) x := by
    filter_upwards [compl_mem_ae_iff.mpr hs₃] with _ h
      using (hF.continuousOn).continuousAt_indicator h
  obtain ⟨r, hr₁, hr₂⟩ := (hasIntegral_iff.mp <|
      AEContinuous.hasBoxIntegral (volume : Measure (ι → ℝ)) h₁ h₂
        IntegrationParams.Riemann) (ε / 2) (half_pos hε)
  refine ⟨⌈(r 0 0 : ℝ)⁻¹⌉₊, fun n hn ↦ lt_of_le_of_lt ?_ (half_lt_self_iff.mpr hε)⟩
  have : NeZero n :=
    ⟨Nat.ne_zero_iff_zero_lt.mpr <| (Nat.ceil_pos.mpr (inv_pos.mpr (r 0 0).prop)).trans_le hn⟩
  rw [← integralSum_eq_tsum_div _ s F hB hs₀, ← Measure.restrict_restrict_of_subset hs₀,
    ← integral_indicator hs₂]
  refine hr₂ 0 _ ⟨?_, fun _ ↦ ?_, fun h ↦ ?_, fun h ↦ ?_⟩ (prepartition_isPartition _ hB)
  · rw [show r 0 = fun _ ↦ r 0 0 from funext_iff.mpr (hr₁ 0 rfl)]
    apply prepartition_isSubordinate n B
    rw [one_div, inv_le_comm₀ (mod_cast (Nat.pos_of_neZero n)) (r 0 0).prop]
    exact le_trans (Nat.le_ceil _) (Nat.cast_le.mpr hn)
  · exact prepartition_isHenstock n B
  · simp only [IntegrationParams.Riemann, Bool.false_eq_true] at h
  · simp only [IntegrationParams.Riemann, Bool.false_eq_true] at h

/-- Let `s` be a bounded, measurable set of `ι → ℝ` whose frontier has zero volume. Then the limit
as `n → ∞` of `card (s ∩ n⁻¹ • (ι → ℤ)) / n ^ card ι` tends to the volume of `s`. This is a
special case of `tendsto_card_div_pow` with `F = 1`. -/
/-
**BoxIntegral.unitPartition._root_.tendsto_card_div_pow_atTop_volume** 是 Mathlib
 中的一个定理，位于命名空间 `BoxIntegral.unitPartition`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `s` be a bounded, measurable set of `ι → ℝ` whose frontier has zero volume. 
Then the limit
as `n → ∞` of `card (s ∩ n⁻¹ • (ι → ℤ)) / n ^ card ι` tends to the volume of `s`
. This is a
special case of `tendsto_card_div_pow` with `F = 1`.
-/
theorem _root_.tendsto_card_div_pow_atTop_volume (hs₁ : IsBounded s)
    (hs₂ : MeasurableSet s) (hs₃ : volume (frontier s) = 0) :
    Tendsto (fun n : ℕ ↦ (Nat.card ↑(s ∩ (n : ℝ)⁻¹ • L) : ℝ) / n ^ card ι)
      atTop (𝓝 (volume.real s)) := by
  convert! tendsto_tsum_div_pow_atTop_integral s (fun _ ↦ 1) continuous_const hs₁ hs₂ hs₃
  · rw [tsum_const, nsmul_eq_mul, mul_one, Nat.cast_inj]
  · rw [setIntegral_const, smul_eq_mul, mul_one]
/-
**BoxIntegral.unitPartition.tendsto_card_div_pow** 是 Mathlib 中的一个定理，位于命名空间 `BoxI
ntegral.unitPartition`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem tendsto_card_div_pow₃ (hs₁ : IsBounded s)
    (hs₄ : ∀ ⦃x y : ℝ⦄, 0 < x → x ≤ y → x • s ⊆ y • s) :
    ∀ᶠ x : ℝ in atTop, (Nat.card ↑(s ∩ (⌊x⌋₊ : ℝ)⁻¹ • L) : ℝ) / x ^ card ι ≤
      (Nat.card ↑(s ∩ x⁻¹ • L) : ℝ) / x ^ card ι := by
  filter_upwards [eventually_ge_atTop 1] with x hx
  gcongr
  exact tendsto_card_div_pow₂ s hs₁ hs₄ (Nat.cast_pos.mpr (Nat.floor_pos.mpr hx))
    (Nat.floor_le (zero_le_one.trans hx))
/-
**BoxIntegral.unitPartition.tendsto_card_div_pow** 是 Mathlib 中的一个定理，位于命名空间 `BoxI
ntegral.unitPartition`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem tendsto_card_div_pow₄ (hs₁ : IsBounded s)
    (hs₄ : ∀ ⦃x y : ℝ⦄, 0 < x → x ≤ y → x • s ⊆ y • s) :
    ∀ᶠ x : ℝ in atTop, (Nat.card ↑(s ∩ x⁻¹ • L) : ℝ) / x ^ card ι ≤
      (Nat.card ↑(s ∩ (⌈x⌉₊ : ℝ)⁻¹ • L) : ℝ) / x ^ card ι := by
  filter_upwards [eventually_gt_atTop 0] with x hx
  gcongr
  exact tendsto_card_div_pow₂ s hs₁ hs₄ hx (Nat.le_ceil _)
/-
**BoxIntegral.unitPartition.tendsto_card_div_pow** 是 Mathlib 中的一个定理，位于命名空间 `BoxI
ntegral.unitPartition`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem tendsto_card_div_pow₅ :
    (fun x ↦ (Nat.card ↑(s ∩ (⌊x⌋₊ : ℝ)⁻¹ • L) : ℝ) / ⌊x⌋₊ ^ card ι * (⌊x⌋₊ / x) ^ card ι)
      =ᶠ[atTop] (fun x ↦ (Nat.card ↑(s ∩ (⌊x⌋₊ : ℝ)⁻¹ • L) : ℝ) / x ^ card ι) := by
  filter_upwards [eventually_ge_atTop 1] with x hx
  have : 0 < ⌊x⌋₊ := Nat.floor_pos.mpr hx
  rw [div_pow, mul_div, div_mul_cancel₀ _ (by positivity)]
/-
**BoxIntegral.unitPartition.tendsto_card_div_pow** 是 Mathlib 中的一个定理，位于命名空间 `BoxI
ntegral.unitPartition`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem tendsto_card_div_pow₆ :
    (fun x ↦ (Nat.card ↑(s ∩ (⌈x⌉₊ : ℝ)⁻¹ • L) : ℝ) / ⌈x⌉₊ ^ card ι * (⌈x⌉₊ / x) ^ card ι)
          =ᶠ[atTop] (fun x ↦ (Nat.card ↑(s ∩ (⌈x⌉₊ : ℝ)⁻¹ • L) : ℝ) / x ^ card ι) := by
  filter_upwards [eventually_ge_atTop 1] with x hx
  rw [div_pow, mul_div, div_mul_cancel₀ _ (by positivity)]

/-- A version of `tendsto_card_div_pow_atTop_volume` for a real variable. -/
/-
**BoxIntegral.unitPartition._root_.tendsto_card_div_pow_atTop_volume'** 是 Mathli
b 中的一个定理，位于命名空间 `BoxIntegral.unitPartition`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A version of `tendsto_card_div_pow_atTop_volume` for a real variable.
-/
theorem _root_.tendsto_card_div_pow_atTop_volume' (hs₁ : IsBounded s)
    (hs₂ : MeasurableSet s) (hs₃ : volume (frontier s) = 0)
    (hs₄ : ∀ ⦃x y : ℝ⦄, 0 < x → x ≤ y → x • s ⊆ y • s) :
    Tendsto (fun x : ℝ ↦ (Nat.card ↑(s ∩ x⁻¹ • L) : ℝ) / x ^ card ι)
      atTop (𝓝 (volume.real s)) := by
  rw [show volume.real s = volume.real s * 1 ^ card ι by ring]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' ?_ ?_
    (tendsto_card_div_pow₃ s hs₁ hs₄) (tendsto_card_div_pow₄ s hs₁ hs₄)
  · refine Tendsto.congr' (tendsto_card_div_pow₅ s) (Tendsto.mul ?_ (Tendsto.pow ?_ _))
    · exact Tendsto.comp (tendsto_card_div_pow_atTop_volume s hs₁ hs₂ hs₃) tendsto_nat_floor_atTop
    · exact tendsto_nat_floor_div_atTop
  · refine Tendsto.congr' (tendsto_card_div_pow₆ s) (Tendsto.mul ?_ (Tendsto.pow ?_ _))
    · exact Tendsto.comp (tendsto_card_div_pow_atTop_volume s hs₁ hs₂ hs₃) tendsto_nat_ceil_atTop
    · exact tendsto_nat_ceil_div_atTop

end fintype

end BoxIntegral.unitPartition

