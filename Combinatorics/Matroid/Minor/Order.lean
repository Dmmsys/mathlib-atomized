/-
Copyright (c) 2025 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson
-/
module

public import Mathlib.Combinatorics.Matroid.Minor.Contract

/-!
# Matroid Minors

A matroid `N = M ／ C ＼ D` obtained from a matroid `M` by a contraction then a delete,
(or equivalently, by any number of contractions/deletions in any order) is a *minor* of `M`.
This gives a partial order on `Matroid α` that is ubiquitous in matroid theory,
and interacts nicely with duality and linear representations.

Although we provide a `PartialOrder` instance on `Matroid α` corresponding to the minor order,
we do not use the `M ≤ N` / `N < M` notation directly,
instead writing `N ≤m M` and `N <m M` for more convenient dot notation.

## Main Declarations

* `Matroid.IsMinor N M`, written `N ≤m M`, means that `N = M ／ C ＼ D` for some
  subset `C` and `D` of `M.E`.
* `Matroid.IsStrictMinor N M`, written `N <m M`, means that `N = M ／ C ＼ D`
  for some subsets `C` and `D` of `M.E` that are not both nonempty.
* `Matroid.IsMinor.exists_eq_contract_delete_disjoint` : we can choose `C` and `D` disjoint.

-/

@[expose] public section

namespace Matroid

open Set

section Minor

variable {α : Type*} {M M' N : Matroid α} {e f : α} {I C D : Set α}

/-! ### Minors -/

/-- `N` is a minor of `M` if `N = M ／ C ＼ D` for some `C` and `D`.
The definition itself does not require `C` and `D` to be disjoint,
or even to be subsets of the ground set. See `Matroid.IsMinor.exists_eq_contract_delete_disjoint`
for the fact that we can choose `C` and `D` with these properties. -/
/-
**Matroid.IsMinor** 是 Mathlib 中的一个定义，位于命名空间 `Matroid`。
形式化陈述：IsMinor (N M : Matroid α) : Prop
参数：N M : Matroid α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`N` is a minor of `M` if `N = M ／ C ＼ D` for some `C` and `D`.
The definition itself does not require `C` and `D` to be disjoint,
or even to be subsets of the ground set. See `Matroid.IsMinor.exists_eq_contract
_delete_disjoint`
for the fact that we can choose `C` and `D` with these properties.
-/
def IsMinor (N M : Matroid α) : Prop := ∃ C D, N = M ／ C ＼ D

/-- `≤m` denotes the minor relation on matroids. -/
infixl:50 " ≤m " => Matroid.IsMinor

@[simp]
/-
**Matroid.contract_delete_isMinor** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：contract_delete_isMinor (M : Matroid α) (C D : Set α) : M ／ C ＼ D <=m M
参数：M : Matroid α；C D : Set α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma contract_delete_isMinor (M : Matroid α) (C D : Set α) : M ／ C ＼ D ≤m M :=
  ⟨C, D, rfl⟩
/-
**Matroid.IsMinor.exists_eq_contract_delete_disjoint** 是 Mathlib 中的一个定理，位于命名空间 `
Matroid.IsMinor`。
形式化陈述：∀ {α : Type u_1} {M N : Matroid α}, N ≤m M → ∃ C D, C ⊆ M.E ∧ D ⊆ M.E ∧ Di
sjoint C D ∧ N = (M.contract C).delete D
参数：M.contract C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
· 使用定理 `Disjoint.mono_left`：Disjoint.mono_left (h : a <= b) : Disjoint b c -> Di
sjoint a c
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用引理 `Set.disjoint_sdiff_right`：disjoint_sdiff_right : Disjoint s (t \ s)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Matroid.contract_inter_ground_eq`：∀ {α : Type u_1} (M : Matroid α) (C : 
Set α), M.contract (C ∩ M.E) = M.contract C
· 使用引理 `Set.inter_sdiff_assoc`：inter_sdiff_assoc (a b c : Set α) : (a inter b) \
 c = a inter (b \ c)
· 使用定理 `Set.inter_assoc`：inter_assoc (a b c : Set α) : a inter b inter c = a int
er (b inter c)
· 使用定理 `Set.inter_self`：inter_self (a : Set α) : a inter a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma IsMinor.exists_eq_contract_delete_disjoint (h : N ≤m M) :
    ∃ (C D : Set α), C ⊆ M.E ∧ D ⊆ M.E ∧ Disjoint C D ∧ N = M ／ C ＼ D := by
  obtain ⟨C, D, rfl⟩ := h
  exact ⟨C ∩ M.E, (D ∩ M.E) \ C, inter_subset_right, sdiff_subset.trans inter_subset_right,
    disjoint_sdiff_right.mono_left inter_subset_left,
    by simp [delete_eq_delete_iff, inter_assoc, inter_sdiff_assoc]⟩

/-- `N` is a strict minor of `M` if `N` is a minor of `M` and `N ≠ M`.
Equivalently, `N` is obtained from `M` by deleting/contracting subsets of the ground set
that are not both empty. -/
/-
**Matroid.IsStrictMinor** 是 Mathlib 中的一个定义，位于命名空间 `Matroid`。
形式化陈述：IsStrictMinor (N M : Matroid α) : Prop
参数：N M : Matroid α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`N` is a strict minor of `M` if `N` is a minor of `M` and `N ≠ M`.
Equivalently, `N` is obtained from `M` by deleting/contracting subsets of the gr
ound set
that are not both empty.
-/
def IsStrictMinor (N M : Matroid α) : Prop := N ≤m M ∧ ¬ M ≤m N

/-- `<m` denotes the strict minor relation on matroids. -/
infixl:50 " <m " => Matroid.IsStrictMinor

/-
**Matroid.IsMinor.subset** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsMinor`。
形式化陈述：∀ {α : Type u_1} {M N : Matroid α}, N ≤m M → N.E ⊆ M.E
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma IsMinor.subset (h : N ≤m M) : N.E ⊆ M.E := by
  obtain ⟨C, D, rfl⟩ := h
  exact sdiff_subset.trans sdiff_subset
/-
**Matroid.IsMinor.refl** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsMinor`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α}, M ≤m M
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matroid.contract_empty`：∀ {α : Type u_1} (M : Matroid α), M.contract ∅ =
 M
· 使用引理 `Matroid.delete_empty`：delete_empty (M : Matroid α) : M ＼ ∅ = M
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma IsMinor.refl {M : Matroid α} : M ≤m M := ⟨∅, ∅, by simp⟩
/-
**Matroid.IsMinor.trans** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsMinor`。
形式化陈述：∀ {α : Type u_1} {M₁ M₂ M₃ : Matroid α}, M₁ ≤m M₂ → M₂ ≤m M₃ → M₁ ≤m M₃
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matroid.contract_delete_contract_delete'`：contract_delete_contract_delet
e' (M : Matroid α) (C D C' D' : Set α) : M ／ C ＼ D ／ C' ＼ D' = M ／ (C union C' \
 D) ＼ (D union D')
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma IsMinor.trans {M₁ M₂ M₃ : Matroid α} (h : M₁ ≤m M₂) (h' : M₂ ≤m M₃) : M₁ ≤m M₃ := by
  obtain ⟨C₁, D₁, rfl⟩ := h
  obtain ⟨C₂, D₂, rfl⟩ := h'
  exact ⟨C₂ ∪ C₁ \ D₂, D₂ ∪ D₁, by rw [contract_delete_contract_delete']⟩
/-
**Matroid.IsMinor.eq_of_ground_subset** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsMinor
`。
形式化陈述：∀ {α : Type u_1} {M N : Matroid α}, N ≤m M → M.E ⊆ N.E → M = N
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.contract_inter_ground_eq`：∀ {α : Type u_1} (M : Matroid α) (C : 
Set α), M.contract (C ∩ M.E) = M.contract C
· 使用定理 `Disjoint.inter_eq`：∀ {α : Type u} {s t : Set α}, Disjoint s t → s ∩ t = 
∅
· 使用定理 `Disjoint.symm`：Disjoint.symm (x y : Finmap β) (h : Disjoint x y) : Disjo
int y x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `Set.subset_sdiff`：subset_sdiff : s subseteq t \ u ↔ s subseteq t ∧ Disjo
int s u
· 使用定理 `Matroid.contract_ground`：∀ {α : Type u_1} (M : Matroid α) (C : Set α), (
M.contract C).E = M.E \ C
· 使用引理 `Matroid.delete_ground`：delete_ground (M : Matroid α) (D : Set α) : (M ＼ 
D).E = M.E \ D
· 使用定理 `Matroid.contract_empty`：∀ {α : Type u_1} (M : Matroid α), M.contract ∅ =
 M
· 使用引理 `Matroid.delete_inter_ground_eq`：delete_inter_ground_eq (M : Matroid α) (
D : Set α) : M ＼ (D inter M.E) = M ＼ D
· 使用引理 `Matroid.delete_empty`：delete_empty (M : Matroid α) : M ＼ ∅ = M
-/
lemma IsMinor.eq_of_ground_subset (h : N ≤m M) (hE : M.E ⊆ N.E) : M = N := by
  obtain ⟨C, D, rfl⟩ := h
  rw [delete_ground, contract_ground, subset_sdiff, subset_sdiff] at hE
  rw [← contract_inter_ground_eq, hE.1.2.symm.inter_eq, contract_empty, ← delete_inter_ground_eq,
    hE.2.symm.inter_eq, delete_empty]
/-
**Matroid.IsMinor.antisymm** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsMinor`。
形式化陈述：∀ {α : Type u_1} {M N : Matroid α}, N ≤m M → M ≤m N → N = M
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsMinor.eq_of_ground_subset`：∀ {α : Type u_1} {M N : Matroid α},
 N ≤m M → M.E ⊆ N.E → M = N
· 使用定理 `Matroid.IsMinor.subset`：∀ {α : Type u_1} {M N : Matroid α}, N ≤m M → N.E
 ⊆ M.E
-/
lemma IsMinor.antisymm (h : N ≤m M) (h' : M ≤m N) : N = M :=
  h'.eq_of_ground_subset h.subset

/-- The minor order is a `PartialOrder` on `Matroid α`.
We prefer the spelling `N ≤m M` over `N ≤ M` for the dot notation. -/
/-
**Matroid.** 是 Mathlib 中的一个实例，位于命名空间 `Matroid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The minor order is a `PartialOrder` on `Matroid α`.
We prefer the spelling `N ≤m M` over `N ≤ M` for the dot notation.
-/
instance (α : Type*) : PartialOrder (Matroid α) where
  le N M := N ≤m M
  lt N M := N <m M
  le_refl _ := IsMinor.refl
  le_trans _ _ _ := IsMinor.trans
  le_antisymm _ _ := IsMinor.antisymm
/-
**Matroid.IsMinor.le** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsMinor`。
形式化陈述：∀ {α : Type u_1} {M N : Matroid α}, N ≤m M → N ≤ M
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma IsMinor.le (h : N ≤m M) : N ≤ M := h
/-
**Matroid.IsStrictMinor.lt** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsStrictMinor`。
形式化陈述：∀ {α : Type u_1} {M N : Matroid α}, N <m M → N < M
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma IsStrictMinor.lt (h : N <m M) : N < M := h

@[simp]
/-
**Matroid.le_eq_isMinor** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：le_eq_isMinor : (fun M M' : Matroid α => M <= M') = Matroid.IsMinor
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma le_eq_isMinor : (fun M M' : Matroid α ↦ M ≤ M') = Matroid.IsMinor := rfl

@[simp]
/-
**Matroid.lt_eq_isStrictMinor** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：lt_eq_isStrictMinor : (fun M M' : Matroid α => M < M') = Matroid.IsStrictM
inor
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma lt_eq_isStrictMinor : (fun M M' : Matroid α ↦ M < M') = Matroid.IsStrictMinor := rfl
/-
**Matroid.isStrictMinor_iff_isMinor_ne** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：isStrictMinor_iff_isMinor_ne : N <m M ↔ N <=m M ∧ N != M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_iff_le_and_ne`：lt_iff_le_and_ne : a < b ↔ a <= b ∧ a != b
-/
lemma isStrictMinor_iff_isMinor_ne : N <m M ↔ N ≤m M ∧ N ≠ M :=
  lt_iff_le_and_ne (α := Matroid α)
/-
**Matroid.IsStrictMinor.ne** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsStrictMinor`。
形式化陈述：∀ {α : Type u_1} {M N : Matroid α}, N <m M → N ≠ M
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Matroid.IsStrictMinor.lt`：∀ {α : Type u_1} {M N : Matroid α}, N <m M → N
 < M
-/
lemma IsStrictMinor.ne (h : N <m M) : N ≠ M :=
  h.lt.ne
/-
**Matroid.isStrictMinor_irrefl** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：isStrictMinor_irrefl (M : Matroid α) : ¬ (M <m M)
参数：M : Matroid α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
-/
lemma isStrictMinor_irrefl (M : Matroid α) : ¬ (M <m M) :=
  lt_irrefl M
/-
**Matroid.IsStrictMinor.isMinor** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsStrictMinor
`。
形式化陈述：∀ {α : Type u_1} {M N : Matroid α}, N <m M → N ≤m M
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Matroid.IsStrictMinor.lt`：∀ {α : Type u_1} {M N : Matroid α}, N <m M → N
 < M
-/
lemma IsStrictMinor.isMinor (h : N <m M) : N ≤m M :=
  h.lt.le
/-
**Matroid.IsStrictMinor.not_isMinor** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsStrictM
inor`。
形式化陈述：∀ {α : Type u_1} {M N : Matroid α}, N <m M → ¬M ≤m N
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `Matroid.IsStrictMinor.lt`：∀ {α : Type u_1} {M N : Matroid α}, N <m M → N
 < M
-/
lemma IsStrictMinor.not_isMinor (h : N <m M) : ¬ (M ≤m N) :=
  h.lt.not_ge
/-
**Matroid.IsStrictMinor.ssubset** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsStrictMinor
`。
形式化陈述：∀ {α : Type u_1} {M N : Matroid α}, N <m M → N.E ⊂ M.E
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.ssubset_of_ne`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst 
: PartialOrder α] {a b : α}, a ⊆ b → a ≠ b → a ⊂ b
· 使用定理 `Matroid.IsMinor.subset`：∀ {α : Type u_1} {M N : Matroid α}, N ≤m M → N.E
 ⊆ M.E
· 使用定理 `Matroid.IsStrictMinor.isMinor`：∀ {α : Type u_1} {M N : Matroid α}, N <m 
M → N ≤m M
· 使用定理 `Matroid.IsStrictMinor.ne`：∀ {α : Type u_1} {M N : Matroid α}, N <m M → N
 ≠ M
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.IsMinor.eq_of_ground_subset`：∀ {α : Type u_1} {M N : Matroid α},
 N ≤m M → M.E ⊆ N.E → M = N
· 使用定理 `Eq.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorder
 α] {a b : α}, a = b → a ⊆ b
-/
lemma IsStrictMinor.ssubset (h : N <m M) : N.E ⊂ M.E :=
  h.isMinor.subset.ssubset_of_ne (fun hE ↦ h.ne (h.isMinor.eq_of_ground_subset hE.symm.subset).symm)
/-
**Matroid.isStrictMinor_iff_isMinor_ssubset** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：isStrictMinor_iff_isMinor_ssubset : N <m M ↔ N <=m M ∧ N.E ⊂ M.E
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsStrictMinor.isMinor`：∀ {α : Type u_1} {M N : Matroid α}, N <m 
M → N ≤m M
· 使用定理 `Matroid.IsStrictMinor.ssubset`：∀ {α : Type u_1} {M N : Matroid α}, N <m 
M → N.E ⊂ M.E
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.IsMinor.antisymm`：∀ {α : Type u_1} {M N : Matroid α}, N ≤m M → M
 ≤m N → N = M
-/
lemma isStrictMinor_iff_isMinor_ssubset : N <m M ↔ N ≤m M ∧ N.E ⊂ M.E :=
  ⟨fun h ↦ ⟨h.isMinor, h.ssubset⟩, fun ⟨h, hss⟩ ↦ ⟨h, fun h' ↦ hss.ne <| by rw [h'.antisymm h]⟩⟩
/-
**Matroid.IsStrictMinor.trans_isMinor** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsStric
tMinor`。
形式化陈述：∀ {α : Type u_1} {M M' N : Matroid α}, N <m M → M ≤m M' → N <m M'
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Matroid.IsStrictMinor.lt`：∀ {α : Type u_1} {M N : Matroid α}, N <m M → N
 < M
-/
lemma IsStrictMinor.trans_isMinor (h : N <m M) (h' : M ≤m M') : N <m M' :=
  h.lt.trans_le h'
/-
**Matroid.IsMinor.trans_isStrictMinor** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsMinor
`。
形式化陈述：∀ {α : Type u_1} {M M' N : Matroid α}, N ≤m M → M <m M' → N <m M'
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Matroid.IsMinor.le`：∀ {α : Type u_1} {M N : Matroid α}, N ≤m M → N ≤ M
-/
lemma IsMinor.trans_isStrictMinor (h : N ≤m M) (h' : M <m M') : N <m M' :=
  h.le.trans_lt h'
/-
**Matroid.IsStrictMinor.trans** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsStrictMinor`。
形式化陈述：∀ {α : Type u_1} {M M' N : Matroid α}, N <m M → M <m M' → N <m M'
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `Matroid.IsStrictMinor.lt`：∀ {α : Type u_1} {M N : Matroid α}, N <m M → N
 < M
-/
lemma IsStrictMinor.trans (h : N <m M) (h' : M <m M') : N <m M' :=
  h.lt.trans h'
/-
**Matroid.Indep.of_isMinor** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Indep`。
形式化陈述：∀ {α : Type u_1} {M N : Matroid α} {I : Set α}, N.Indep I → N ≤m M → M.Ind
ep I
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.Indep.of_contract`：∀ {α : Type u_1} {M : Matroid α} {I C : Set α
}, (M.contract C).Indep I → M.Indep I
· 使用定理 `Matroid.Indep.of_delete`：∀ {α : Type u_1} {M : Matroid α} {I D : Set α},
 (M.delete D).Indep I → M.Indep I
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma Indep.of_isMinor (hI : N.Indep I) (hNM : N ≤m M) : M.Indep I := by
  obtain ⟨C, D, rfl⟩ := hNM
  exact hI.of_delete.of_contract
/-
**Matroid.IsNonloop.of_isMinor** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsNonloop`。
形式化陈述：∀ {α : Type u_1} {M N : Matroid α} {e : α}, N.IsNonloop e → N ≤m M → M.IsN
onloop e
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsNonloop.of_contract`：∀ {α : Type u_1} {M : Matroid α} {e : α} 
{C : Set α}, (M.contract C).IsNonloop e → M.IsNonloop e
· 使用定理 `Matroid.IsNonloop.of_delete`：∀ {α : Type u_1} {M : Matroid α} {e : α} {D
 : Set α}, (M.delete D).IsNonloop e → M.IsNonloop e
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma IsNonloop.of_isMinor (h : N.IsNonloop e) (hNM : N ≤m M) : M.IsNonloop e := by
  obtain ⟨C, D, rfl⟩ := hNM
  exact h.of_delete.of_contract
/-
**Matroid.Dep.of_isMinor** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Dep`。
形式化陈述：∀ {α : Type u_1} {M N : Matroid α} {D : Set α}, M.Dep D → D ⊆ N.E → N ≤m M
 → N.Dep D
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.Dep.not_indep`：∀ {α : Type u_1} {M : Matroid α} {D : Set α}, M.D
ep D → ¬M.Indep D
· 使用定理 `Matroid.Indep.of_isMinor`：∀ {α : Type u_1} {M N : Matroid α} {I : Set α}
, N.Indep I → N ≤m M → M.Indep I
-/
lemma Dep.of_isMinor {D : Set α} (hD : M.Dep D) (hDN : D ⊆ N.E) (hNM : N ≤m M) : N.Dep D :=
  ⟨fun h ↦ hD.not_indep <| h.of_isMinor hNM, hDN⟩
/-
**Matroid.IsLoop.of_isMinor** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsLoop`。
形式化陈述：∀ {α : Type u_1} {M N : Matroid α} {e : α}, M.IsLoop e → e ∈ N.E → N ≤m M 
→ N.IsLoop e
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Matroid.singleton_dep`：singleton_dep : M.Dep {e} ↔ M.IsLoop e
· 使用定理 `Matroid.Dep.of_isMinor`：∀ {α : Type u_1} {M N : Matroid α} {D : Set α}, 
M.Dep D → D ⊆ N.E → N ≤m M → N.Dep D
-/
lemma IsLoop.of_isMinor (he : M.IsLoop e) (heN : e ∈ N.E) (hNM : N ≤m M) : N.IsLoop e := by
  rw [← singleton_dep] at he ⊢
  exact he.of_isMinor (by simpa) hNM

end Minor

end Matroid

