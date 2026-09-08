/-
Copyright (c) 2022 Jesse Reimann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Reimann, Kalle Kytölä
-/
module

public import Mathlib.MeasureTheory.Measure.Content
public import Mathlib.Topology.ContinuousMap.CompactlySupported
public import Mathlib.Topology.PartitionOfUnity

/-!
# Riesz–Markov–Kakutani representation theorem

This file prepares technical definitions and results for the Riesz-Markov-Kakutani representation
theorem on a locally compact T2 space `X`. As a special case, the statements about linear
functionals on bounded continuous functions follows. Actual theorems, depending on the
linearity (`ℝ`, `ℝ≥0` or `ℂ`), are proven in separate files
(`Mathlib/MeasureTheory/Integral/RieszMarkovKakutani/Real.lean`,
`Mathlib/MeasureTheory/Integral/RieszMarkovKakutani/NNReal.lean`...)

To make use of the existing API, the measure is constructed from a content `λ` on the
compact subsets of a locally compact space X, rather than the usual construction of open sets in the
literature.

## References

* [Walter Rudin, Real and Complex Analysis.][Rud87]

-/

@[expose] public section


noncomputable section

open scoped BoundedContinuousFunction NNReal ENNReal
open Set Function TopologicalSpace CompactlySupported CompactlySupportedContinuousMap
  MeasureTheory

variable {X : Type*} [TopologicalSpace X]
variable (Λ : C_c(X, ℝ≥0) →ₗ[ℝ≥0] ℝ≥0)

/-! ### Construction of the content: -/

section Monotone

/-
**CompactlySupportedContinuousMap.monotone_of_nnreal** 是 Mathlib 中的一个引理，位于命名空间 `
`。
形式化陈述：CompactlySupportedContinuousMap.monotone_of_nnreal : Monotone Λ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsTopologicalSemiring.toIsSemitopologicalSemiring`：∀ (R : Type u_2) [ins
t : TopologicalSpace R] [inst_1 : NonUnitalNonAssocSemiring R] [IsTopologicalSem
iring R],   IsSemitopologicalSemiring R
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `CompactlySupportedContinuousMap.exists_add_of_le`：∀ {α : Type u_2} [inst
 : TopologicalSpace α] {f₁ f₂ : CompactlySupportedContinuousMap α NNReal},   f₁ 
≤ f₂ → ∃ g, f₁ + g = f₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
-/
lemma CompactlySupportedContinuousMap.monotone_of_nnreal : Monotone Λ := by
  intro f₁ f₂ h
  obtain ⟨g, hg⟩ := CompactlySupportedContinuousMap.exists_add_of_le h
  rw [← hg]
  simp

end Monotone

/-- Given a positive linear functional `Λ` on continuous compactly supported functions on `X`
with values in `ℝ≥0`, for `K ⊆ X` compact define `λ(K) = inf {Λf | 1≤f on K}`.
When `X` is a locally compact T2 space, this will be shown to be a
content, and will be shown to agree with the Riesz measure on the compact subsets `K ⊆ X`. -/
/-
**rieszContentAux** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：rieszContentAux : Compacts X -> Real>=0
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a positive linear functional `Λ` on continuous compactly supported functio
ns on `X`
with values in `ℝ≥0`, for `K ⊆ X` compact define `λ(K) = inf {Λf | 1≤f on K}`.
When `X` is a locally compact T2 space, this will be shown to be a
content, and will be shown to agree with the Riesz measure on the compact subset
s `K ⊆ X`.
-/
def rieszContentAux : Compacts X → ℝ≥0 := fun K =>
  sInf (Λ '' { f : C_c(X, ℝ≥0) | ∀ x ∈ K, (1 : ℝ≥0) ≤ f x })

section RieszMonotone

variable [T2Space X] [LocallyCompactSpace X]

/-- For any compact subset `K ⊆ X`, there exist some compactly supported continuous nonnegative
functions `f` on `X` such that `f ≥ 1` on `K`. -/
/-
**rieszContentAux_image_nonempty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rieszContentAux_image_nonempty (K : Compacts X) : (Λ '' { f : C_c(X, Real>
=0) | forall x in K, (1 : Real>=0) <= f x }).Nonempty
参数：K : Compacts X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsTopologicalSemiring.toIsSemitopologicalSemiring`：∀ (R : Type u_2) [ins
t : TopologicalSpace R] [inst_1 : NonUnitalNonAssocSemiring R] [IsTopologicalSem
iring R],   IsSemitopologicalSemiring R
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_nonempty`：image_nonempty {f : α -> β} {s : Set α} : (f '' s).N
onempty ↔ s.Nonempty
· 使用定理 `exists_compact_superset`：exists_compact_superset [WeaklyLocallyCompactSp
ace X] {K : Set X} (hK : IsCompact K) : exists K', IsCompact K' ∧ K subseteq int
erior K'
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `TopologicalSpace.Compacts.isCompact'`：∀ {α : Type u_4} [inst : Topologic
alSpace α] (self : TopologicalSpace.Compacts α), IsCompact self.carrier
· 使用定理 `IsCompact.of_isClosed_subset`：IsCompact.of_isClosed_subset (hs : IsCompa
ct s) (ht : IsClosed t) (h : t subseteq s) : IsCompact t
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `closure_eq_iff_isClosed`：closure_eq_iff_isClosed : closure s = s ↔ IsClo
sed s
· 使用定理 `IsCompact.isClosed`：IsCompact.isClosed [T2Space X] {s : Set X} (hs : IsC
ompact s) : IsClosed s
· 使用定理 `closure_mono`：closure_mono (h : s subseteq t) : closure s subseteq closu
re t
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s
· 使用引理 `exists_tsupport_one_of_isOpen_isClosed`：exists_tsupport_one_of_isOpen_is
Closed [R1Space X] {s t : Set X} (hs : IsOpen s) (hscp : IsCompact (closure s)) 
(ht : IsClosed t) (hst : t s…
· 使用定理 `T2Space.r1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], R1Space X
· 使用定理 `isOpen_interior`：isOpen_interior : IsOpen (interior s)
· 使用定理 `isClosed_tsupport`：∀ {X : Type u_1} {α : Type u_2} [inst : Zero α] [inst
_1 : TopologicalSpace X] (f : X → α), IsClosed (tsupport f)
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Real.toNNReal_one`：toNNReal_one : Real.toNNReal 1 = 1
· 使用定理 `Real.toNNReal_eq_toNNReal_iff`：toNNReal_eq_toNNReal_iff {r p : Real} (hr
 : 0 <= r) (hp : 0 <= p) : toNNReal r = toNNReal p ↔ r = p
· 使用引理 `zero_le_one'`：zero_le_one' (α) [Zero α] [One α] [LE α] [ZeroLEOneClass α
] : (0 : α) <= 1
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Set.EqOn.symm`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f₁ f₂ : α → 
β}, Set.EqOn f₁ f₂ s → Set.EqOn f₂ f₁ s

--- 原说明 ---
For any compact subset `K ⊆ X`, there exist some compactly supported continuous 
nonnegative
functions `f` on `X` such that `f ≥ 1` on `K`.
-/
theorem rieszContentAux_image_nonempty (K : Compacts X) :
    (Λ '' { f : C_c(X, ℝ≥0) | ∀ x ∈ K, (1 : ℝ≥0) ≤ f x }).Nonempty := by
  rw [image_nonempty]
  obtain ⟨V, hVcp, hKsubintV⟩ := exists_compact_superset K.2
  have hIsCompact_closure_interior : IsCompact (closure (interior V)) := by
    apply IsCompact.of_isClosed_subset hVcp isClosed_closure
    nth_rw 2 [← closure_eq_iff_isClosed.mpr (IsCompact.isClosed hVcp)]
    exact closure_mono interior_subset
  obtain ⟨f, hsuppfsubV, hfeq1onK, hfinicc⟩ :=
    exists_tsupport_one_of_isOpen_isClosed isOpen_interior hIsCompact_closure_interior
      (IsCompact.isClosed K.2) hKsubintV
  have hfHasCompactSupport : HasCompactSupport f :=
    IsCompact.of_isClosed_subset hVcp (isClosed_tsupport f)
      (Set.Subset.trans hsuppfsubV interior_subset)
  use nnrealPart ⟨f, hfHasCompactSupport⟩
  intro x hx
  apply le_of_eq
  simp only [nnrealPart_apply, CompactlySupportedContinuousMap.coe_mk]
  rw [← Real.toNNReal_one, Real.toNNReal_eq_toNNReal_iff (zero_le_one' ℝ) (hfinicc x).1]
  exact hfeq1onK.symm hx

/-- Riesz content `λ` (associated with a positive linear functional `Λ`) is
monotone: if `K₁ ⊆ K₂` are compact subsets in `X`, then `λ(K₁) ≤ λ(K₂)`. -/
/-
**rieszContentAux_mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rieszContentAux_mono {K₁ K₂ : Compacts X} (h : K₁ <= K₂) : rieszContentAux
 Λ K₁ <= rieszContentAux Λ K₂
参数：h : K₁ <= K₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsTopologicalSemiring.toIsSemitopologicalSemiring`：∀ (R : Type u_2) [ins
t : TopologicalSpace R] [inst_1 : NonUnitalNonAssocSemiring R] [IsTopologicalSem
iring R],   IsSemitopologicalSemiring R
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `csInf_le_csInf'`：csInf_le_csInf' {s t : Set α} (h₁ : t.Nonempty) (h₂ : t
 subseteq s) : sInf s <= sInf t
· 使用定理 `rieszContentAux_image_nonempty`：rieszContentAux_image_nonempty (K : Comp
acts X) : (Λ '' { f : C_c(X, Real>=0) | forall x in K, (1 : Real>=0) <= f x }).N
onempty
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
· 使用定理 `Set.ofPred_subset_ofPred_of_imp`：∀ {α : Type u} {p q : α → Prop}, (∀ (a 
: α), p a → q a) → {a | p a} ⊆ {a | q a}
· 使用定理 `forall_imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∀ (a : α), p a) → ∀ (a : α), q a
· 使用引理 `Mathlib.Tactic.GCongr.imp_mono`：imp_mono (h₁ : c -> a) (h₂ : c -> b -> d
) : (a -> b) -> c -> d
· 使用定理 `mem_of_le_of_mem`：∀ {A : Type u_1} {B : Type u_2} [inst : SetLike A B] [
inst_1 : LE A] [IsConcreteLE A B] {S T : A},   S ≤ T → ∀ ⦃x : B⦄, x ∈ S → x ∈ T
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B

--- 原说明 ---
Riesz content `λ` (associated with a positive linear functional `Λ`) is
monotone: if `K₁ ⊆ K₂` are compact subsets in `X`, then `λ(K₁) ≤ λ(K₂)`.
-/
theorem rieszContentAux_mono {K₁ K₂ : Compacts X} (h : K₁ ≤ K₂) :
    rieszContentAux Λ K₁ ≤ rieszContentAux Λ K₂ := by
  unfold rieszContentAux
  gcongr
  apply rieszContentAux_image_nonempty

end RieszMonotone

section RieszSubadditive

/-- Any compactly supported continuous nonnegative `f` such that `f ≥ 1` on `K` gives an upper bound
on the content of `K`; namely `λ(K) ≤ Λ f`. -/
/-
**rieszContentAux_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rieszContentAux_le {K : Compacts X} {f : C_c(X, Real>=0)} (h : forall x in
 K, (1 : Real>=0) <= f x) : rieszContentAux Λ K <= Λ f
参数：X, Real>=0；h : forall x in K, (1 : Real>=0) <= f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsTopologicalSemiring.toIsSemitopologicalSemiring`：∀ (R : Type u_2) [ins
t : TopologicalSpace R] [inst_1 : NonUnitalNonAssocSemiring R] [IsTopologicalSem
iring R],   IsSemitopologicalSemiring R
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `csInf_le`：∀ {α : Type u_1} [inst : ConditionallyCompleteLattice α] {s : 
Set α} {a : α}, BddBelow s → a ∈ s → sInf s ≤ a
· 使用定理 `OrderBot.bddBelow`：∀ {α : Type u_1} [inst : Preorder α] [OrderBot α] (s 
: Set α), BddBelow s

--- 原说明 ---
Any compactly supported continuous nonnegative `f` such that `f ≥ 1` on `K` give
s an upper bound
on the content of `K`; namely `λ(K) ≤ Λ f`.
-/
theorem rieszContentAux_le {K : Compacts X} {f : C_c(X, ℝ≥0)} (h : ∀ x ∈ K, (1 : ℝ≥0) ≤ f x) :
    rieszContentAux Λ K ≤ Λ f :=
  csInf_le (OrderBot.bddBelow _) ⟨f, ⟨h, rfl⟩⟩

variable [T2Space X] [LocallyCompactSpace X]

/-- The Riesz content can be approximated arbitrarily well by evaluating the positive linear
functional on test functions: for any `ε > 0`, there exists a compactly supported continuous
nonnegative function `f` on `X` such that `f ≥ 1` on `K` and such that `λ(K) ≤ Λ f < λ(K) + ε`. -/
/-
**exists_lt_rieszContentAux_add_pos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_lt_rieszContentAux_add_pos (K : Compacts X) {ε : Real>=0} (εpos : 0
 < ε) : exists f : C_c(X, Real>=0), (forall x in K, (1 : Real>=0) <= f x) ∧ Λ f 
< rieszContentAux Λ K + ε
参数：K : Compacts X；εpos : 0 < ε。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsTopologicalSemiring.toIsSemitopologicalSemiring`：∀ (R : Type u_2) [ins
t : TopologicalSpace R] [inst_1 : NonUnitalNonAssocSemiring R] [IsTopologicalSem
iring R],   IsSemitopologicalSemiring R
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `exists_lt_of_csInf_lt`：∀ {α : Type u_1} [inst : ConditionallyCompleteLin
earOrder α] {s : Set α} {b : α},   s.Nonempty → sInf s < b → ∃ a ∈ s, a < b
· 使用定理 `rieszContentAux_image_nonempty`：rieszContentAux_image_nonempty (K : Comp
acts X) : (Λ '' { f : C_c(X, Real>=0) | forall x in K, (1 : Real>=0) <= f x }).N
onempty
· 使用定理 `lt_add_of_pos_right`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : 
LT α] [AddLeftStrictMono α] (a : α) {b : α}, 0 < b → a < a + b
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `NNReal.instIsStrictOrderedRing_1`：IsStrictOrderedRing NNReal
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
The Riesz content can be approximated arbitrarily well by evaluating the positiv
e linear
functional on test functions: for any `ε > 0`, there exists a compactly supporte
d continuous
nonnegative function `f` on `X` such that `f ≥ 1` on `K` and such that `λ(K) ≤ Λ
 f < λ(K) + ε`.
-/
theorem exists_lt_rieszContentAux_add_pos (K : Compacts X) {ε : ℝ≥0} (εpos : 0 < ε) :
    ∃ f : C_c(X, ℝ≥0), (∀ x ∈ K, (1 : ℝ≥0) ≤ f x) ∧ Λ f < rieszContentAux Λ K + ε := by
  --choose a test function `f` s.t. `Λf = α < λ(K) + ε`
  obtain ⟨α, ⟨⟨f, f_hyp⟩, α_hyp⟩⟩ :=
    exists_lt_of_csInf_lt (rieszContentAux_image_nonempty Λ K)
      (lt_add_of_pos_right (rieszContentAux Λ K) εpos)
  refine ⟨f, f_hyp.left, ?_⟩
  rw [f_hyp.right]
  exact α_hyp

/-- The Riesz content `λ` associated to a given positive linear functional `Λ` is
finitely subadditive: `λ(K₁ ∪ K₂) ≤ λ(K₁) + λ(K₂)` for any compact subsets `K₁, K₂ ⊆ X`. -/
/-
**rieszContentAux_sup_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rieszContentAux_sup_le (K1 K2 : Compacts X) : rieszContentAux Λ (K1 ⊔ K2) 
<= rieszContentAux Λ K1 + rieszContentAux Λ K2
参数：K1 K2 : Compacts X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsTopologicalSemiring.toIsSemitopologicalSemiring`：∀ (R : Type u_2) [ins
t : TopologicalSpace R] [inst_1 : NonUnitalNonAssocSemiring R] [IsTopologicalSem
iring R],   IsSemitopologicalSemiring R
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `le_of_forall_pos_le_add`：∀ {α : Type u} [inst : LinearOrder α] [DenselyO
rdered α] [inst_2 : AddMonoid α] [ExistsAddOfLE α] [AddLeftReflectLT α]   {a b :
 α}, (∀ (ε : …
· 使用定理 `NNReal.instDenselyOrdered`：DenselyOrdered NNReal
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `NNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd NNReal
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `exists_lt_rieszContentAux_add_pos`：exists_lt_rieszContentAux_add_pos (K 
: Compacts X) {ε : Real>=0} (εpos : 0 < ε) : exists f : C_c(X, Real>=0), (forall
 x in K, (1 : Real>=0) …
· 使用定理 `half_pos`：half_pos (h : 0 < a) : 0 < a / 2
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `NNReal.instIsStrictOrderedRing_1`：IsStrictOrderedRing NNReal
· 使用定理 `le_add_right`：∀ {α : Type u} [inst : Add α] [inst_1 : Preorder α] [Canon
icallyOrderedAdd α] {a b c : α}, a ≤ b → a ≤ b + c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `le_add_left`：∀ {α : Type u} [inst : Add α] [inst_1 : Preorder α] [Canoni
callyOrderedAdd α] {a b c : α}, a ≤ c → a ≤ b + c
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `rieszContentAux_le`：rieszContentAux_le {K : Compacts X} {f : C_c(X, Real
>=0)} (h : forall x in K, (1 : Real>=0) <= f x) : rieszContentAux Λ K <= Λ f
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `add_lt_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftStrictMono α] [AddRightStrictMono α] {a b c d : α},   a < b → c < d → a + c < 
…
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
（共 43 条，此处仅展示前 30 条）

--- 原说明 ---
The Riesz content `λ` associated to a given positive linear functional `Λ` is
finitely subadditive: `λ(K₁ ∪ K₂) ≤ λ(K₁) + λ(K₂)` for any compact subsets `K₁, 
K₂ ⊆ X`.
-/
theorem rieszContentAux_sup_le (K1 K2 : Compacts X) :
    rieszContentAux Λ (K1 ⊔ K2) ≤ rieszContentAux Λ K1 + rieszContentAux Λ K2 := by
  apply _root_.le_of_forall_pos_le_add
  intro ε εpos
  --get test functions s.t. `λ(Ki) ≤ Λfi ≤ λ(Ki) + ε/2, i=1,2`
  obtain ⟨f1, f_test_function_K1⟩ := exists_lt_rieszContentAux_add_pos Λ K1 (half_pos εpos)
  obtain ⟨f2, f_test_function_K2⟩ := exists_lt_rieszContentAux_add_pos Λ K2 (half_pos εpos)
  --let `f := f1 + f2` test function for the content of `K`
  have f_test_function_union : ∀ x ∈ K1 ⊔ K2, (1 : ℝ≥0) ≤ (f1 + f2) x := by
    rintro x (x_in_K1 | x_in_K2)
    · exact le_add_right (f_test_function_K1.left x x_in_K1)
    · exact le_add_left (f_test_function_K2.left x x_in_K2)
  --use that `Λf` is an upper bound for `λ(K1⊔K2)`
  apply (rieszContentAux_le Λ f_test_function_union).trans (le_of_lt _)
  rw [map_add]
  --use that `Λfi` are lower bounds for `λ(Ki) + ε/2`
  apply lt_of_lt_of_le (_root_.add_lt_add f_test_function_K1.right f_test_function_K2.right)
    (le_of_eq _)
  rw [add_assoc, add_comm (ε / 2), add_assoc, add_halves ε, add_assoc]

end RieszSubadditive


section PartitionOfUnity

variable [T2Space X] [LocallyCompactSpace X]

/-
**exists_continuous_add_one_of_isCompact_nnreal** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：exists_continuous_add_one_of_isCompact_nnreal {s₀ s₁ : Set X} {t : Set X} 
(s₀_compact : IsCompact s₀) (s₁_compact : IsCompact s₁) (t_compact : IsCompact t
) (disj : Disjoint s₀ s₁) (hst : s₀ union s₁ subseteq t) : exists (f₀ f₁ : C_c(X
, Real>=0)), EqOn f₀ 1 s₀ ∧ EqOn f₁ 1 s₁ ∧ EqOn (f₀ + f₁) 1 t
参数：s₀_compact : IsCompact s₀；s₁_compact : IsCompact s₁；t_compact : IsCompact t；d
isj : Disjoint s₀ s₁；hst : s₀ union s₁ subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IsCompact.isClosed`：IsCompact.isClosed [T2Space X] {s : Set X} (hs : IsC
ompact s) : IsClosed s
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `Fin.instNeZeroHAddNatOfNat_mathlib_1`：∀ (n : ℕ) [NeZero n], NeZero 1
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.mem_union`：mem_union (x : α) (a b : Set α) : x in a union b ↔ x in a
 ∨ x in b
· 使用定理 `Set.compl_subset_iff_union`：compl_subset_iff_union {s t : Set α} : sᶜ su
bseteq t ↔ s union t = univ
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用引理 `Set.subset_compl_iff_disjoint_right`：subset_compl_iff_disjoint_right : s
 subseteq tᶜ ↔ Disjoint s t
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsTopologicalSemiring.toIsSemitopologicalSemiring`：∀ (R : Type u_2) [ins
t : TopologicalSpace R] [inst_1 : NonUnitalNonAssocSemiring R] [IsTopologicalSem
iring R],   IsSemitopologicalSemiring R
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `exists_continuous_sum_one_of_isOpen_isCompact`：exists_continuous_sum_one
_of_isOpen_isCompact [T2Space X] [LocallyCompactSpace X] {n : Nat} {t : Set X} {
s : Fin n -> Set X} (hs : forall (i…
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `Fin.sum_univ_two`：∀ {M : Type u_2} [inst : AddCommMonoid M] (f : Fin 2 →
 M), ∑ i, f i = f 0 + f 1
· 使用定理 `Function.notMem_support`：∀ {ι : Type u_1} {M : Type u_3} [inst : Zero M]
 {f : ι → M} {x : ι}, x ∉ Function.support f ↔ f x = 0
（共 45 条，此处仅展示前 30 条）
-/
lemma exists_continuous_add_one_of_isCompact_nnreal
    {s₀ s₁ : Set X} {t : Set X} (s₀_compact : IsCompact s₀) (s₁_compact : IsCompact s₁)
    (t_compact : IsCompact t) (disj : Disjoint s₀ s₁) (hst : s₀ ∪ s₁ ⊆ t) :
    ∃ (f₀ f₁ : C_c(X, ℝ≥0)), EqOn f₀ 1 s₀ ∧ EqOn f₁ 1 s₁ ∧ EqOn (f₀ + f₁) 1 t := by
  set so : Fin 2 → Set X := fun j => if j = 0 then s₀ᶜ else s₁ᶜ with hso
  have soopen (j : Fin 2) : IsOpen (so j) := by
    fin_cases j
    · simp only [hso, Fin.zero_eta, Fin.isValue, ↓reduceIte, isOpen_compl_iff]
      exact IsCompact.isClosed <| s₀_compact
    · simp only [hso, Fin.isValue, Fin.mk_one, one_ne_zero, ↓reduceIte, isOpen_compl_iff]
      exact IsCompact.isClosed <| s₁_compact
  have hsot : t ⊆ ⋃ j, so j := by
    rw [hso]
    simp only [Fin.isValue]
    intro x hx
    rw [mem_iUnion]
    rw [← subset_compl_iff_disjoint_right, ← compl_compl s₀, compl_subset_iff_union] at disj
    have h : x ∈ s₀ᶜ ∨ x ∈ s₁ᶜ := by
      rw [← mem_union, disj]
      exact mem_univ _
    apply Or.elim h
    · intro h0
      use 0
      simp only [Fin.isValue, ↓reduceIte]
      exact h0
    · intro h1
      use 1
      simp only [Fin.isValue, one_ne_zero, ↓reduceIte]
      exact h1
  obtain ⟨f, f_supp_in_so, sum_f_one_on_t, f_in_icc, f_hcs⟩ :=
    exists_continuous_sum_one_of_isOpen_isCompact soopen t_compact hsot
  use (nnrealPart (⟨f 1, f_hcs 1⟩ : C_c(X, ℝ))),
    (nnrealPart (⟨f 0, f_hcs 0⟩ : C_c(X, ℝ)))
  simp only [Fin.isValue, CompactlySupportedContinuousMap.coe_add]
  have sum_one_x (x : X) (hx : x ∈ t) : (f 0) x + (f 1) x = 1 := by
    simpa only [Finset.sum_apply, Fin.sum_univ_two, Fin.isValue, Pi.one_apply]
      using sum_f_one_on_t hx
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    simp only [Fin.isValue, nnrealPart_apply,
      CompactlySupportedContinuousMap.coe_mk, Pi.one_apply, Real.toNNReal_eq_one]
    have : (f 0) x = 0 := by
      rw [← notMem_support]
      have : s₀ ⊆ (tsupport (f 0))ᶜ := by
        apply subset_trans _ (compl_subset_compl.mpr (f_supp_in_so 0))
        rw [hso]
        simp only [Fin.isValue, ↓reduceIte, compl_compl, subset_refl]
      apply notMem_of_mem_compl
      exact mem_of_subset_of_mem (subset_trans this (compl_subset_compl_of_subset subset_closure))
        hx
    rw [union_subset_iff] at hst
    rw [← sum_one_x x (mem_of_subset_of_mem hst.1 hx), this]
    exact Eq.symm (AddZeroClass.zero_add ((f 1) x))
  · intro x hx
    simp only [Fin.isValue, nnrealPart_apply,
      CompactlySupportedContinuousMap.coe_mk, Pi.one_apply, Real.toNNReal_eq_one]
    have : (f 1) x = 0 := by
      rw [← notMem_support]
      have : s₁ ⊆ (tsupport (f 1))ᶜ := by
        apply subset_trans _ (compl_subset_compl.mpr (f_supp_in_so 1))
        rw [hso]
        simp only [Fin.isValue, one_ne_zero, ↓reduceIte, compl_compl, subset_refl]
      apply notMem_of_mem_compl
      exact mem_of_subset_of_mem (subset_trans this (compl_subset_compl_of_subset subset_closure))
        hx
    rw [union_subset_iff] at hst
    rw [← sum_one_x x (mem_of_subset_of_mem hst.2 hx), this]
    exact Eq.symm (AddMonoid.add_zero ((f 0) x))
  · intro x hx
    simp only [Fin.isValue, Pi.add_apply, nnrealPart_apply,
      CompactlySupportedContinuousMap.coe_mk, Pi.one_apply]
    rw [Real.toNNReal_add_toNNReal (f_in_icc 1 x).1 (f_in_icc 0 x).1, add_comm]
    simp only [Fin.isValue, Real.toNNReal_eq_one]
    exact sum_one_x x hx

end PartitionOfUnity

section RieszContentAdditive

variable [T2Space X] [LocallyCompactSpace X]

/-
**rieszContentAux_union** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：rieszContentAux_union {K₁ K₂ : TopologicalSpace.Compacts X} (disj : Disjoi
nt (K₁ : Set X) K₂) : rieszContentAux Λ (K₁ ⊔ K₂) = rieszContentAux Λ K₁ + riesz
ContentAux Λ K₂
参数：disj : Disjoint (K₁ : Set X) K₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsTopologicalSemiring.toIsSemitopologicalSemiring`：∀ (R : Type u_2) [ins
t : TopologicalSpace R] [inst_1 : NonUnitalNonAssocSemiring R] [IsTopologicalSem
iring R],   IsSemitopologicalSemiring R
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `rieszContentAux_sup_le`：rieszContentAux_sup_le (K1 K2 : Compacts X) : ri
eszContentAux Λ (K1 ⊔ K2) <= rieszContentAux Λ K1 + rieszContentAux Λ K2
· 使用定理 `le_csInf`：∀ {α : Type u_1} [inst : ConditionallyCompleteLattice α] {s : 
Set α} {a : α}, s.Nonempty → (∀ b ∈ s, a ≤ b) → a ≤ sInf s
· 使用定理 `rieszContentAux_image_nonempty`：rieszContentAux_image_nonempty (K : Comp
acts X) : (Λ '' { f : C_c(X, Real>=0) | forall x in K, (1 : Real>=0) <= f x }).N
onempty
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.mem_support`：∀ {ι : Type u_1} {M : Type u_3} [inst : Zero M] {f
 : ι → M} {x : ι}, x ∈ Function.support f ↔ f x ≠ 0
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用引理 `zero_lt_one'`：zero_lt_one' : (0 : α) < 1
· 使用定理 `FloorSemiring.instZeroLEOneClass`：∀ {α : Type u_2} [inst : Semiring α] [
inst_1 : PartialOrder α] [FloorSemiring α], ZeroLEOneClass α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `subset_trans`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preor
der α] {a b c : α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用引理 `exists_continuous_add_one_of_isCompact_nnreal`：exists_continuous_add_one
_of_isCompact_nnreal {s₀ s₁ : Set X} {t : Set X} (s₀_compact : IsCompact s₀) (s₁
_compact : IsCompact s₁) (t_compact…
· 使用定理 `TopologicalSpace.Compacts.isCompact'`：∀ {α : Type u_4} [inst : Topologic
alSpace α] (self : TopologicalSpace.Compacts α), IsCompact self.carrier
· 使用定理 `HasCompactSupport.isCompact`：∀ {α : Type u_2} {β : Type u_4} [inst : Top
ologicalSpace α] [inst_1 : Zero β] {f : α → β},   HasCompactSupport f → IsCompac
t (tsupport f)
· 使用定理 `CompactlySupportedContinuousMap.hasCompactSupport'`：∀ {α : Type u_5} {β 
: Type u_6} [inst : TopologicalSpace α] [inst_1 : Zero β] [inst_2 : TopologicalS
pace β]   (self : CompactlySupportedCont…
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `CompactlySupportedContinuousMap.ext`：ext {f g : C_c(α, β)} (h : forall x
, f x = g x) : f = g
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RightDistribClass.right_distrib`：∀ {R : Type u_1} {inst : Mul R} {inst_1
 : Add R} [self : RightDistribClass R] (a b c : R), (a + b) * c = a * c + b * c
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
（共 43 条，此处仅展示前 30 条）
-/
lemma rieszContentAux_union {K₁ K₂ : TopologicalSpace.Compacts X}
    (disj : Disjoint (K₁ : Set X) K₂) :
    rieszContentAux Λ (K₁ ⊔ K₂) = rieszContentAux Λ K₁ + rieszContentAux Λ K₂ := by
  refine le_antisymm (rieszContentAux_sup_le Λ K₁ K₂) ?_
  refine le_csInf (rieszContentAux_image_nonempty Λ (K₁ ⊔ K₂)) ?_
  intro b ⟨f, ⟨hf, Λf_eq_b⟩⟩
  have hsuppf : ∀ x ∈ K₁ ⊔ K₂, x ∈ support f := by
    intro x hx
    rw [mem_support]
    exact ne_of_gt <| lt_of_lt_of_le (zero_lt_one' ℝ≥0) (hf x hx)
  have hsubsuppf : (K₁ : Set X) ∪ (K₂ : Set X) ⊆ tsupport f := subset_trans hsuppf subset_closure
  obtain ⟨g₁, g₂, hg₁, hg₂, sum_g⟩ := exists_continuous_add_one_of_isCompact_nnreal K₁.isCompact'
    K₂.isCompact' f.hasCompactSupport'.isCompact disj hsubsuppf
  have f_eq_sum : f = g₁ * f + g₂ * f := by
    ext x
    simp only [CompactlySupportedContinuousMap.coe_add, CompactlySupportedContinuousMap.coe_mul,
      Pi.mul_apply, NNReal.coe_mul,
      Eq.symm (RightDistribClass.right_distrib _ _ _)]
    by_cases h : f x = 0
    · rw [h]
      simp only [NNReal.coe_zero, mul_zero]
    · simp only [CompactlySupportedContinuousMap.coe_add, ContinuousMap.toFun_eq_coe,
        CompactlySupportedContinuousMap.coe_toContinuousMap] at sum_g
      rw [sum_g (mem_of_subset_of_mem subset_closure (mem_support.mpr h))]
      simp only [Pi.one_apply, NNReal.coe_one, one_mul]
  rw [← Λf_eq_b, f_eq_sum, map_add]
  have aux₁ : ∀ x ∈ K₁, 1 ≤ (g₁ * f) x := by
    intro x x_in_K₁
    simp [hg₁ x_in_K₁, hf x (mem_union_left _ x_in_K₁)]
  have aux₂ : ∀ x ∈ K₂, 1 ≤ (g₂ * f) x := by
    intro x x_in_K₂
    simp [hg₂ x_in_K₂, hf x (mem_union_right _ x_in_K₂)]
  exact add_le_add (rieszContentAux_le Λ aux₁) (rieszContentAux_le Λ aux₂)

end RieszContentAdditive

section RieszContentRegular

variable [T2Space X] [LocallyCompactSpace X]

/-- The content induced by the linear functional `Λ`. -/
/-
**rieszContent** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：rieszContent (Λ : C_c(X, Real>=0) ->ₗ[Real>=0] Real>=0) : Content X where 
toFun
参数：Λ : C_c(X, Real>=0) ->ₗ[Real>=0] Real>=0。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `rieszContentAux_mono`：rieszContentAux_mono {K₁ K₂ : Compacts X} (h : K₁ 
<= K₂) : rieszContentAux Λ K₁ <= rieszContentAux Λ K₂
· 使用引理 `rieszContentAux_union`：rieszContentAux_union {K₁ K₂ : TopologicalSpace.C
ompacts X} (disj : Disjoint (K₁ : Set X) K₂) : rieszContentAux Λ (K₁ ⊔ K₂) = rie
szContentAu…
· 使用定理 `rieszContentAux_sup_le`：rieszContentAux_sup_le (K1 K2 : Compacts X) : ri
eszContentAux Λ (K1 ⊔ K2) <= rieszContentAux Λ K1 + rieszContentAux Λ K2

--- 原说明 ---
The content induced by the linear functional `Λ`.
-/
noncomputable def rieszContent (Λ : C_c(X, ℝ≥0) →ₗ[ℝ≥0] ℝ≥0) : Content X where
  toFun := rieszContentAux Λ
  mono' := fun _ _ ↦ rieszContentAux_mono Λ
  sup_disjoint' := fun _ _ disj _ _ ↦ rieszContentAux_union Λ disj
  sup_le' := rieszContentAux_sup_le Λ
/-
**rieszContent_ne_top** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：rieszContent_ne_top {K : Compacts X} : rieszContent Λ K != ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsTopologicalSemiring.toIsSemitopologicalSemiring`：∀ (R : Type u_2) [ins
t : TopologicalSpace R] [inst_1 : NonUnitalNonAssocSemiring R] [IsTopologicalSem
iring R],   IsSemitopologicalSemiring R
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `rieszContentAux_mono`：rieszContentAux_mono {K₁ K₂ : Compacts X} (h : K₁ 
<= K₂) : rieszContentAux Λ K₁ <= rieszContentAux Λ K₂
· 使用引理 `rieszContentAux_union`：rieszContentAux_union {K₁ K₂ : TopologicalSpace.C
ompacts X} (disj : Disjoint (K₁ : Set X) K₂) : rieszContentAux Λ (K₁ ⊔ K₂) = rie
szContentAu…
· 使用定理 `rieszContentAux_sup_le`：rieszContentAux_sup_le (K1 K2 : Compacts X) : ri
eszContentAux Λ (K1 ⊔ K2) <= rieszContentAux Λ K1 + rieszContentAux Λ K2
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma rieszContent_ne_top {K : Compacts X} : rieszContent Λ K ≠ ⊤ := by
  simp [rieszContent, ne_eq, not_false_eq_true]

set_option backward.isDefEq.respectTransparency false in
/-
**contentRegular_rieszContent** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：contentRegular_rieszContent : (rieszContent Λ).ContentRegular
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsTopologicalSemiring.toIsSemitopologicalSemiring`：∀ (R : Type u_2) [ins
t : TopologicalSpace R] [inst_1 : NonUnitalNonAssocSemiring R] [IsTopologicalSem
iring R],   IsSemitopologicalSemiring R
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `rieszContentAux_mono`：rieszContentAux_mono {K₁ K₂ : Compacts X} (h : K₁ 
<= K₂) : rieszContentAux Λ K₁ <= rieszContentAux Λ K₂
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s
· 使用定理 `iInf_le_iff`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteSemilattice
Inf α] {a : α} {s : ι → α},   iInf s ≤ a ↔ ∀ (b : α), (∀ (i : ι), b ≤ s i) → b ≤
 …
· 使用定理 `rieszContentAux.eq_1`：∀ {X : Type u_1} [inst : TopologicalSpace X] (Λ : 
CompactlySupportedContinuousMap X NNReal →ₗ[NNReal] NNReal)   (K : TopologicalSp
ace.Compac…
· 使用定理 `ENNReal.le_coe_iff`：le_coe_iff : a <= ↑r ↔ exists p : Real>=0, a = p ∧ p
 <= r
· 使用定理 `exists_compact_superset`：exists_compact_superset [WeaklyLocallyCompactSp
ace X] {K : Set X} (hK : IsCompact K) : exists K', IsCompact K' ∧ K subseteq int
erior K'
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `TopologicalSpace.Compacts.isCompact'`：∀ {α : Type u_4} [inst : Topologic
alSpace α] (self : TopologicalSpace.Compacts α), IsCompact self.carrier
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `le_iInf_iff`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] 
{f : ι → α} {a : α}, a ≤ iInf f ↔ ∀ (i : ι), a ≤ f i
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `ENNReal.coe_lt_top`：∀ {r : NNReal}, ↑r < ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.coe_toNNReal`：∀ {a : ENNReal}, a ≠ ⊤ → ↑a.toNNReal = a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
（共 87 条，此处仅展示前 30 条）
-/
lemma contentRegular_rieszContent : (rieszContent Λ).ContentRegular := by
  intro K
  simp only [rieszContent, le_antisymm_iff, le_iInf_iff, ENNReal.coe_le_coe, Content.mk_apply]
  refine ⟨fun K' hK' ↦ rieszContentAux_mono Λ (hK'.trans interior_subset), ?_⟩
  rw [iInf_le_iff]
  intro b hb
  rw [rieszContentAux, ENNReal.le_coe_iff]
  have : b < ⊤ := by
    obtain ⟨F, hF⟩ := exists_compact_superset K.2
    exact (le_iInf_iff.mp (hb ⟨F, hF.1⟩) hF.2).trans_lt ENNReal.coe_lt_top
  refine ⟨b.toNNReal, (ENNReal.coe_toNNReal this.ne).symm, NNReal.coe_le_coe.mp ?_⟩
  apply le_iff_forall_pos_le_add.mpr
  intro ε hε
  lift ε to ℝ≥0 using hε.le
  obtain ⟨f, hfleoneonK, hfle⟩ := exists_lt_rieszContentAux_add_pos Λ K (Real.toNNReal_pos.mpr hε)
  rw [rieszContentAux, Real.toNNReal_of_nonneg hε.le, ← NNReal.coe_lt_coe] at hfle
  refine ((le_iff_forall_one_lt_le_mul₀ (zero_le (a := Λ f))).mpr fun α hα ↦ ?_).trans hfle.le
  rw [mul_comm, ← smul_eq_mul, ← map_smul]
  set K' := f ⁻¹' Ici α⁻¹
  have hKK' : ↑K ⊆ interior K' :=
    subset_interior_iff.2 ⟨f ⁻¹' Ioi α⁻¹, isOpen_Ioi.preimage f.1.2,
      fun x hx ↦ (inv_lt_one_of_one_lt₀ hα).trans_le (hfleoneonK x hx),
      preimage_mono Ioi_subset_Ici_self⟩
  have hK'cp : IsCompact K' := .of_isClosed_subset f.2 (isClosed_Ici.preimage f.1.2) fun x hx ↦
    subset_closure ((inv_pos_of_pos <| zero_lt_one.trans hα).trans_le hx).ne'
  set hb' := hb ⟨K', hK'cp⟩
  simp only [Compacts.coe_mk, le_iInf_iff] at hb'
  exact (ENNReal.toNNReal_mono (by simp) <| hb' hKK').trans <| csInf_le'
    ⟨α • f, fun x ↦ (inv_le_iff_one_le_mul₀' (zero_lt_one.trans hα)).mp, by simp⟩

end RieszContentRegular

namespace NNRealRMK

variable [T2Space X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]

/-- `rieszContent` gives a `Content` from `Λ : C_c(X, ℝ≥0) →ₗ[ℝ≥0] ℝ≥0`. Here `rieszContent Λ` is
promoted to a measure. It will be later shown that
`∫ (x : X), f x ∂(rieszMeasure Λ hΛ) = Λ f` for all `f : C_c(X, ℝ≥0)`. -/
/-
**NNRealRMK.rieszMeasure** 是 Mathlib 中的一个定义，位于命名空间 `NNRealRMK`。
形式化陈述：rieszMeasure
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `T2Space.r1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], R1Space X

--- 原说明 ---
`rieszContent` gives a `Content` from `Λ : C_c(X, ℝ≥0) →ₗ[ℝ≥0] ℝ≥0`. Here `riesz
Content Λ` is
promoted to a measure. It will be later shown that
`∫ (x : X), f x ∂(rieszMeasure Λ hΛ) = Λ f` for all `f : C_c(X, ℝ≥0)`.
-/
def rieszMeasure := (rieszContent Λ).measure

set_option backward.isDefEq.respectTransparency false in
/-
**NNRealRMK.le_rieszMeasure_of_isCompact_tsupport_subset** 是 Mathlib 中的一个引理，位于命名
空间 `NNRealRMK`。
形式化陈述：le_rieszMeasure_of_isCompact_tsupport_subset {f : C_c(X, Real>=0)} (hf : f
orall x, f x <= 1) {K : Set X} (hK : IsCompact K) (h : tsupport f subseteq K) : 
.ofNNReal (Λ f) <= rieszMeasure Λ K
参数：X, Real>=0；hf : forall x, f x <= 1；hK : IsCompact K；h : tsupport f subseteq K
。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsTopologicalSemiring.toIsSemitopologicalSemiring`：∀ (R : Type u_2) [ins
t : TopologicalSpace R] [inst_1 : NonUnitalNonAssocSemiring R] [IsTopologicalSem
iring R],   IsSemitopologicalSemiring R
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `TopologicalSpace.Compacts.coe_mk`：coe_mk (s : Set α) (h) : (mk s h : Set
 α) = s
· 使用定理 `MeasureTheory.Content.measure_eq_content_of_regular`：measure_eq_content_
of_regular (H : MeasureTheory.Content.ContentRegular μ) (K : TopologicalSpace.Co
mpacts G) : μ.measure ↑K = μ K
· 使用定理 `T2Space.r1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], R1Space X
· 使用引理 `contentRegular_rieszContent`：contentRegular_rieszContent : (rieszContent
 Λ).ContentRegular
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `le_iff_forall_pos_le_add`：∀ {α : Type u} [inst : LinearOrder α] [Densely
Ordered α] [inst_2 : AddMonoid α] [ExistsAddOfLE α] [AddLeftReflectLT α]   {a b 
: α} [AddLeftS…
· 使用定理 `NNReal.instDenselyOrdered`：DenselyOrdered NNReal
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `NNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd NNReal
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `NNReal.instIsStrictOrderedRing_1`：IsStrictOrderedRing NNReal
· 使用定理 `exists_lt_rieszContentAux_add_pos`：exists_lt_rieszContentAux_add_pos (K 
: Compacts X) {ε : Real>=0} (εpos : 0 < ε) : exists f : C_c(X, Real>=0), (forall
 x in K, (1 : Real>=0) …
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用引理 `CompactlySupportedContinuousMap.monotone_of_nnreal`：CompactlySupportedCo
ntinuousMap.monotone_of_nnreal : Monotone Λ
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Set.mem_of_subset_of_mem`：∀ {α : Type u} {s₁ s₂ : Set α} {a : α}, s₁ ⊆ s
₂ → a ∈ s₁ → a ∈ s₂
· 使用定理 `image_eq_zero_of_notMem_tsupport`：∀ {X : Type u_1} {α : Type u_2} [inst 
: Zero α] [inst_1 : TopologicalSpace X] {f : X → α} {x : X},   x ∉ tsupport f → 
f x = 0
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma le_rieszMeasure_of_isCompact_tsupport_subset {f : C_c(X, ℝ≥0)} (hf : ∀ x, f x ≤ 1)
    {K : Set X} (hK : IsCompact K) (h : tsupport f ⊆ K) : .ofNNReal (Λ f) ≤ rieszMeasure Λ K := by
  rw [← TopologicalSpace.Compacts.coe_mk K hK]
  simp only [rieszMeasure, Content.measure_eq_content_of_regular (rieszContent Λ)
    (contentRegular_rieszContent Λ)]
  simp only [rieszContent, ENNReal.coe_le_coe, Content.mk_apply]
  apply le_iff_forall_pos_le_add.mpr
  intro ε hε
  obtain ⟨g, hg⟩ := exists_lt_rieszContentAux_add_pos Λ ⟨K, hK⟩ hε
  apply le_trans _ hg.2.le
  apply monotone_of_nnreal Λ
  intro x
  simp only
  by_cases hx : x ∈ tsupport f
  · exact le_trans (hf x) (hg.1 x (Set.mem_of_subset_of_mem h hx))
  · rw [image_eq_zero_of_notMem_tsupport hx]
    exact zero_le
/-
**NNRealRMK.le_rieszMeasure_of_tsupport_subset** 是 Mathlib 中的一个引理，位于命名空间 `NNReal
RMK`。
形式化陈述：le_rieszMeasure_of_tsupport_subset {f : C_c(X, Real>=0)} (hf : forall x, f
 x <= 1) {V : Set X} (h : tsupport f subseteq V) : .ofNNReal (Λ f) <= rieszMeasu
re Λ V
参数：X, Real>=0；hf : forall x, f x <= 1；h : tsupport f subseteq V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsTopologicalSemiring.toIsSemitopologicalSemiring`：∀ (R : Type u_2) [ins
t : TopologicalSpace R] [inst_1 : NonUnitalNonAssocSemiring R] [IsTopologicalSem
iring R],   IsSemitopologicalSemiring R
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用引理 `NNRealRMK.le_rieszMeasure_of_isCompact_tsupport_subset`：le_rieszMeasure_
of_isCompact_tsupport_subset {f : C_c(X, Real>=0)} (hf : forall x, f x <= 1) {K 
: Set X} (hK : IsCompact K) (h : tsupport f …
· 使用定理 `CompactlySupportedContinuousMap.hasCompactSupport`：∀ {α : Type u_2} {β :
 Type u_3} [inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [inst_2 : Z
ero β]   (f : CompactlySupportedContinu…
· 使用定理 `subset_rfl`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorde
r α] {a : α}, a ⊆ a
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
-/
lemma le_rieszMeasure_of_tsupport_subset {f : C_c(X, ℝ≥0)} (hf : ∀ x, f x ≤ 1) {V : Set X}
    (h : tsupport f ⊆ V) : .ofNNReal (Λ f) ≤ rieszMeasure Λ V := by
  apply le_trans _ (measure_mono h)
  apply le_rieszMeasure_of_isCompact_tsupport_subset Λ hf f.hasCompactSupport
  exact subset_rfl

end NNRealRMK

