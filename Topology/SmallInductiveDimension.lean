/-
Copyright (c) 2026 Fernando Chu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Chu, Andrew Yang
-/
module

public import Mathlib.Data.ENat.Lattice
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Clopen

/-!
# Small inductive dimension

The small inductive dimension of a space is inductively defined as follows. Empty spaces have
small inductive dimension less than 0, and a topological space has dimension less than `n + 1` if
it has a topological basis whose elements have frontiers of dimension strictly less `n`.

In this file we formalize this notion, and characterize the cases `n = 0` and `n = 1`.

## Main definitions

* `HasSmallInductiveDimensionLT X n` : Provides a class stating that `X` has small inductive
  dimension less than `n`.
* `HasSmallInductiveDimensionLE X n` : Provides an abbrev for
  `HasSmallInductiveDimensionLT X (n + 1)`.
* `smallInductiveDimension X` : The small inductive dimension of `X`, with values in `WithBot ℕ∞`.

## References

* https://en.wikipedia.org/wiki/Inductive_dimension
-/

@[expose] public section

open Set Topology TopologicalSpace

/--
For a topological space, the property of having small inductive dimension less than `n : ℕ`  is
inductively defined as follows. Empty spaces have small inductive dimension less than 0, and a
topological space has dimension less than `n + 1` if it has a topological basis whose elements have
frontiers of dimension strictly less `n`.
-/
/-
**inductive** 是 Mathlib 中的一个类，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For a topological space, the property of having small inductive dimension less t
han `n : ℕ`  is
inductively defined as follows. Empty spaces have small inductive dimension less
 than 0, and a
topological space has dimension less than `n + 1` if it has a topological basis 
whose elements have
frontiers of dimension strictly less `n`.
-/
class inductive HasSmallInductiveDimensionLT.{u} :
  ∀ (X : Type u) [TopologicalSpace X], ℕ → Prop where
  | zero {X : Type u} [TopologicalSpace X] [IsEmpty X] : HasSmallInductiveDimensionLT X 0
  | succ {X : Type u} [TopologicalSpace X] (n : ℕ) (s : Set (Set X)) (hs : IsTopologicalBasis s)
      (h : ∀ U ∈ s, HasSmallInductiveDimensionLT (frontier U) n) :
      HasSmallInductiveDimensionLT X (n + 1)

variable {X : Type*} [TopologicalSpace X]

variable (X) in
/-- A topological space has dimension `≤ n` if it has dimension `< n + 1`. -/
/-
**HasSmallInductiveDimensionLE** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：HasSmallInductiveDimensionLE (n : Nat)
参数：n : Nat。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A topological space has dimension `≤ n` if it has dimension `< n + 1`.
-/
abbrev HasSmallInductiveDimensionLE (n : ℕ) :=
  HasSmallInductiveDimensionLT X (n + 1)

@[simp]
/-
**hasSmallInductiveDimensionLT_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasSmallInductiveDimensionLT_zero_iff : HasSmallInductiveDimensionLT X 0 ↔
 IsEmpty X
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
-/
theorem hasSmallInductiveDimensionLT_zero_iff : HasSmallInductiveDimensionLT X 0 ↔ IsEmpty X :=
  ⟨fun h ↦ by cases h; assumption, fun _ ↦ .zero⟩

@[deprecated (since := "2026-06-21")]
alias HasSmallInductiveDimensionLT_zero_iff := hasSmallInductiveDimensionLT_zero_iff
/-
**hasSmallInductiveDimensionLT_one_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：hasSmallInductiveDimensionLT_one_iff : HasSmallInductiveDimensionLT X 1 ↔ 
IsTopologicalBasis { s : Set X | IsClopen s }
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.IsTopologicalBasis.of_isOpen_of_subset`：∀ {α : Type u} 
[t : TopologicalSpace α] {s s' : Set (Set α)},   (∀ u ∈ s', IsOpen u) → Topologi
calSpace.IsTopologicalBasis s → s ⊆ s' → Topo…
· 使用定理 `IsClopen.isOpen`：∀ {X : Type u} [inst : TopologicalSpace X] {s : Set X},
 IsClopen s → IsOpen s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `closure_subset_iff_isClosed`：closure_subset_iff_isClosed : closure s sub
seteq s ↔ IsClosed s
· 使用定理 `Set.sdiff_eq_empty`：sdiff_eq_empty {s t : Set α} : s \ t = ∅ ↔ s subsete
q t
· 使用定理 `IsOpen.frontier_eq`：IsOpen.frontier_eq (hs : IsOpen s) : frontier s = cl
osure s \ s
· 使用定理 `TopologicalSpace.IsTopologicalBasis.isOpen`：∀ {α : Type u} [t : Topologi
calSpace α] {s : Set α} {b : Set (Set α)},   TopologicalSpace.IsTopologicalBasis
 b → s ∈ b → IsOpen s
· 使用定理 `Set.isEmpty_coe_sort`：isEmpty_coe_sort {s : Set α} : IsEmpty (↥s) ↔ s = 
∅
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `Set.instIsEmptyElemEmptyCollection`：∀ (α : Type u), IsEmpty ↑∅
· 使用定理 `IsClopen.frontier_eq`：∀ {X : Type u} [inst : TopologicalSpace X] {s : Se
t X}, IsClopen s → frontier s = ∅
-/
lemma hasSmallInductiveDimensionLT_one_iff :
    HasSmallInductiveDimensionLT X 1 ↔ IsTopologicalBasis { s : Set X | IsClopen s } := by
  constructor
  · intro (.succ _ s hs h)
    refine hs.of_isOpen_of_subset (fun _ hU ↦ hU.isOpen) (fun U hU ↦ ⟨?_, hs.isOpen hU⟩)
    rw [← closure_subset_iff_isClosed]
    cases h U hU
    rwa [isEmpty_coe_sort, (hs.isOpen hU).frontier_eq, sdiff_eq_empty] at ‹_›
  · exact fun h ↦ .succ 0 _ h fun _ hU ↦ hU.frontier_eq ▸ .zero

@[deprecated (since := "2026-06-21")]
alias HasSmallInductiveDimensionLT_one_iff := hasSmallInductiveDimensionLT_one_iff
/-
**HasSmallInductiveDimensionLT.mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasSmallInductiveDimensionLT.mono {m n : Nat} (hmn : m <= n) (H : HasSmall
InductiveDimensionLT X m) : HasSmallInductiveDimensionLT X n
参数：hmn : m <= n；H : HasSmallInductiveDimensionLT X m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `add_le_add_iff_right`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LE α] [A
ddRightMono α] [AddRightReflectLE α] (a : α) {b c : α},   b + a ≤ c + a ↔ b ≤ c
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsRightCancelAdd.addRightReflectLE_of_addRightReflectLT`：∀ (N : Type u_2
) [inst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightReflect
LT N],   AddRightReflectLE N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
-/
theorem HasSmallInductiveDimensionLT.mono {m n : ℕ} (hmn : m ≤ n)
    (H : HasSmallInductiveDimensionLT X m) : HasSmallInductiveDimensionLT X n := by
  induction n generalizing m X with
  | zero => simp_all
  | succ m IH =>
    cases H with
    | zero => exact .succ _ ∅ (by simpa) (by simp)
    | succ n s hs h =>
      refine .succ _ s hs fun U hU ↦ IH ?_ (h U hU)
      rwa [add_le_add_iff_right] at hmn
/-
**HasSmallInductiveDimensionLE.mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasSmallInductiveDimensionLE.mono {m n : Nat} (hmn : m <= n) (H : HasSmall
InductiveDimensionLE X m) : HasSmallInductiveDimensionLE X n
参数：hmn : m <= n；H : HasSmallInductiveDimensionLE X m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasSmallInductiveDimensionLT.mono`：HasSmallInductiveDimensionLT.mono {m 
n : Nat} (hmn : m <= n) (H : HasSmallInductiveDimensionLT X m) : HasSmallInducti
veDimensionLT X n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_le_add_iff_right`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LE α] [A
ddRightMono α] [AddRightReflectLE α] (a : α) {b c : α},   b + a ≤ c + a ↔ b ≤ c
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsRightCancelAdd.addRightReflectLE_of_addRightReflectLT`：∀ (N : Type u_2
) [inst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightReflect
LT N],   AddRightReflectLE N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
-/
theorem HasSmallInductiveDimensionLE.mono {m n : ℕ} (hmn : m ≤ n)
    (H : HasSmallInductiveDimensionLE X m) : HasSmallInductiveDimensionLE X n := by
  apply HasSmallInductiveDimensionLT.mono _ H
  rwa [add_le_add_iff_right]
/-
**HasSmallInductiveDimensionLT.hasSmallInductiveDimensionLE** 是 Mathlib 中的一个定理，位
于命名空间 ``。
形式化陈述：HasSmallInductiveDimensionLT.hasSmallInductiveDimensionLE {n : Nat} (H : H
asSmallInductiveDimensionLT X n) : HasSmallInductiveDimensionLE X n
参数：H : HasSmallInductiveDimensionLT X n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasSmallInductiveDimensionLT.mono`：HasSmallInductiveDimensionLT.mono {m 
n : Nat} (hmn : m <= n) (H : HasSmallInductiveDimensionLT X m) : HasSmallInducti
veDimensionLT X n
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ
-/
theorem HasSmallInductiveDimensionLT.hasSmallInductiveDimensionLE {n : ℕ}
    (H : HasSmallInductiveDimensionLT X n) : HasSmallInductiveDimensionLE X n :=
  HasSmallInductiveDimensionLT.mono n.le_succ H
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (n : ℕ) [IsEmpty X] : HasSmallInductiveDimensionLT X n :=
  .mono zero_le <| hasSmallInductiveDimensionLT_zero_iff.2 ‹_›

/-! ### Small inductive dimension -/

variable (X) in
/-- The small inductive dimension of a topological space. -/
/-
**smallInductiveDimension** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：smallInductiveDimension : WithBot Nat∞
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The small inductive dimension of a topological space.
-/
noncomputable def smallInductiveDimension : WithBot ℕ∞ :=
  sInf {n | ∀ i : ℕ, n < i → HasSmallInductiveDimensionLT X i}
/-
**hasSmallInductiveDimensionLT_of_smallInductiveDimension_lt** 是 Mathlib 中的一个定理，
位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem hasSmallInductiveDimensionLT_of_smallInductiveDimension_lt {n : ℕ}
    (h : smallInductiveDimension X < n) : HasSmallInductiveDimensionLT X n := by
  contrapose! h
  simp only [smallInductiveDimension, le_sInf_iff, mem_ofPred_eq]
  intro a ha
  contrapose! ha
  exact ⟨n, ha, h⟩
/-
**hasSmallInductiveDimensionLE_of_smallInductiveDimension_le** 是 Mathlib 中的一个定理，
位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem hasSmallInductiveDimensionLE_of_smallInductiveDimension_le {n : ℕ}
    (h : smallInductiveDimension X ≤ n) : HasSmallInductiveDimensionLE X n := by
  apply hasSmallInductiveDimensionLT_of_smallInductiveDimension_lt (h.trans_lt _)
  exact_mod_cast n.lt_add_one
/-
**smallInductiveDimension_le_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：smallInductiveDimension_le_iff {n : Nat} : smallInductiveDimension X <= n 
↔ HasSmallInductiveDimensionLE X n where mp
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.Topology.SmallInductiveDimension.0.hasSmallInductiveDim
ensionLE_of_smallInductiveDimension_le`：∀ {X : Type u_1} [inst : TopologicalSpac
e X] {n : ℕ}, smallInductiveDimension X ≤ ↑n → HasSmallInductiveDimensionLE X n
· 使用定理 `sInf_le`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, a ∈ s → sInf s ≤ a
· 使用定理 `HasSmallInductiveDimensionLT.mono`：HasSmallInductiveDimensionLT.mono {m 
n : Nat} (hmn : m <= n) (H : HasSmallInductiveDimensionLT X m) : HasSmallInducti
veDimensionLT X n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
-/
theorem smallInductiveDimension_le_iff {n : ℕ} :
    smallInductiveDimension X ≤ n ↔ HasSmallInductiveDimensionLE X n where
  mp := hasSmallInductiveDimensionLE_of_smallInductiveDimension_le
  mpr h := sInf_le fun m hm ↦ .mono (by simpa using hm) h
/-
**smallInductiveDimension_lt_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：smallInductiveDimension_lt_iff {n : Nat} : smallInductiveDimension X < n ↔
 HasSmallInductiveDimensionLT X n where mp
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.Topology.SmallInductiveDimension.0.hasSmallInductiveDim
ensionLT_of_smallInductiveDimension_lt`：∀ {X : Type u_1} [inst : TopologicalSpac
e X] {n : ℕ}, smallInductiveDimension X < ↑n → HasSmallInductiveDimensionLT X n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smallInductiveDimension.eq_1`：∀ (X : Type u_1) [inst : TopologicalSpace 
X],   smallInductiveDimension X = sInf {n | ∀ (i : ℕ), n < ↑i → HasSmallInductiv
eDimensionLT X i}
· 使用定理 `csInf_eq_bot_of_bot_mem`：∀ {α : Type u_1} [inst : ConditionallyCompleteL
inearOrder α] [inst_1 : OrderBot α] {s : Set α}, ⊥ ∈ s → sInf s = ⊥
· 使用定理 `HasSmallInductiveDimensionLT.mono`：HasSmallInductiveDimensionLT.mono {m 
n : Nat} (hmn : m <= n) (H : HasSmallInductiveDimensionLT X m) : HasSmallInducti
veDimensionLT X n
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `smallInductiveDimension_le_iff`：smallInductiveDimension_le_iff {n : Nat}
 : smallInductiveDimension X <= n ↔ HasSmallInductiveDimensionLE X n where mp
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `Nat.lt_add_one`：∀ (n : ℕ), n < n + 1
-/
theorem smallInductiveDimension_lt_iff {n : ℕ} :
    smallInductiveDimension X < n ↔ HasSmallInductiveDimensionLT X n where
  mp := hasSmallInductiveDimensionLT_of_smallInductiveDimension_lt
  mpr h := by
    cases n with
    | zero =>
      rw [smallInductiveDimension, csInf_eq_bot_of_bot_mem]
      · simp
      · exact fun _ _ ↦ h.mono zero_le
    | succ n =>
      apply (smallInductiveDimension_le_iff.2 h).trans_lt
      exact_mod_cast n.lt_add_one

variable (X) in
/-
**smallInductiveDimension_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：smallInductiveDimension_le (n : Nat) [H : HasSmallInductiveDimensionLE X n
] : smallInductiveDimension X <= n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `smallInductiveDimension_le_iff`：smallInductiveDimension_le_iff {n : Nat}
 : smallInductiveDimension X <= n ↔ HasSmallInductiveDimensionLE X n where mp
-/
theorem smallInductiveDimension_le (n : ℕ) [H : HasSmallInductiveDimensionLE X n] :
    smallInductiveDimension X ≤ n :=
  smallInductiveDimension_le_iff.2 H

variable (X) in
/-
**smallInductiveDimension_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：smallInductiveDimension_lt (n : Nat) [H : HasSmallInductiveDimensionLT X n
] : smallInductiveDimension X < n
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `smallInductiveDimension_lt_iff`：smallInductiveDimension_lt_iff {n : Nat}
 : smallInductiveDimension X < n ↔ HasSmallInductiveDimensionLT X n where mp
-/
theorem smallInductiveDimension_lt (n : ℕ) [H : HasSmallInductiveDimensionLT X n] :
    smallInductiveDimension X < n :=
  smallInductiveDimension_lt_iff.2 H
/-
**smallInductiveDimension_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：smallInductiveDimension_eq (n : Nat) (hle : HasSmallInductiveDimensionLE X
 n) (hlt : ¬ HasSmallInductiveDimensionLT X n) : smallInductiveDimension X = n
参数：n : Nat；hle : HasSmallInductiveDimensionLE X n；hlt : ¬ HasSmallInductiveDimen
sionLT X n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `smallInductiveDimension_le_iff`：smallInductiveDimension_le_iff {n : Nat}
 : smallInductiveDimension X <= n ↔ HasSmallInductiveDimensionLE X n where mp
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `smallInductiveDimension_lt_iff`：smallInductiveDimension_lt_iff {n : Nat}
 : smallInductiveDimension X < n ↔ HasSmallInductiveDimensionLT X n where mp
-/
theorem smallInductiveDimension_eq (n : ℕ)
    (hle : HasSmallInductiveDimensionLE X n) (hlt : ¬ HasSmallInductiveDimensionLT X n) :
    smallInductiveDimension X = n := by
  apply (smallInductiveDimension_le_iff.2 hle).antisymm
  rwa [← not_lt, smallInductiveDimension_lt_iff]

@[simp]
/-
**smallInductiveDimension_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：smallInductiveDimension_eq_bot : smallInductiveDimension X = ⊥ ↔ IsEmpty X
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `WithBot.lt_coe_bot`：lt_coe_bot [OrderBot α] : x < (⊥ : α) ↔ x = ⊥
· 使用定理 `bot_eq_zero'`：∀ {α : Type u} [inst : AddMonoid α] [inst_1 : LinearOrder 
α] [CanonicallyOrderedAdd α] [inst_3 : OrderBot α], ⊥ = 0
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem smallInductiveDimension_eq_bot : smallInductiveDimension X = ⊥ ↔ IsEmpty X := by
  simp_rw [← hasSmallInductiveDimensionLT_zero_iff, ← smallInductiveDimension_lt_iff,
    WithBot.lt_coe_bot.symm, bot_eq_zero', Nat.cast_zero, WithBot.coe_zero]

variable (X) in
@[simp]
/-
**smallInductiveDimension_of_isEmpty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：smallInductiveDimension_of_isEmpty [IsEmpty X] : smallInductiveDimension X
 = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `smallInductiveDimension_eq_bot`：smallInductiveDimension_eq_bot : smallIn
ductiveDimension X = ⊥ ↔ IsEmpty X
-/
theorem smallInductiveDimension_of_isEmpty [IsEmpty X] : smallInductiveDimension X = ⊥ :=
  smallInductiveDimension_eq_bot.2 ‹_›
