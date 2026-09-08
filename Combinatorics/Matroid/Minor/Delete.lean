/-
Copyright (c) 2025 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson
-/
module

public import Mathlib.Combinatorics.Matroid.Loop

/-!
# Matroid Deletion

For `M : Matroid α` and `X : Set α`, the *deletion* of `X` from `M` is the matroid `M ＼ X`
with ground set `M.E \ X`, in which a subset of `M.E \ X` is independent if and only if it is
independent in `M`.

The deletion `M ＼ X` is equal to the restriction `M ↾ (M.E \ X)`, but is of special importance
in the theory because it is the dual notion of *contraction*, and thus plays a more central
and natural role than restriction in many contexts.

Because of the implementation of the restriction `M ↾ R` allowing `R` to not be a subset of `M.E`,
the relation `M ↾ R ≤r M` holds only with the assumption `R ⊆ M.E`,
whereas `M ＼ D`, being defined as `M ↾ (M.E \ D)`, satisfies `M ＼ D ≤r M` unconditionally.
This is often quite convenient.

## Main Declarations

* `Matroid.delete M D`, written `M ＼ D`, is the restriction of `M` to the set `M.E \ D`,
  or equivalently the matroid on `M.E \ D` whose independent sets are the `M`-independent sets.

## Naming conventions

We use the abbreviation `deleteElem` in lemma names to refer to the deletion `M ＼ {e}`
of a single element `e : α` from `M : Matroid α`.
-/

@[expose] public section

open Set

variable {α : Type*} {M M' N : Matroid α} {e f : α} {I B D R X : Set α}

namespace Matroid

/-! ## Deletion -/

section Delete

/-- The deletion `M ＼ D` is the restriction of a matroid `M` to `M.E \ D`.
Its independent sets are the `M`-independent subsets of `M.E \ D`. -/
/-
**Matroid.delete** 是 Mathlib 中的一个定义，位于命名空间 `Matroid`。
形式化陈述：delete (M : Matroid α) (D : Set α) : Matroid α
参数：M : Matroid α；D : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The deletion `M ＼ D` is the restriction of a matroid `M` to `M.E \ D`.
Its independent sets are the `M`-independent subsets of `M.E \ D`.
-/
def delete (M : Matroid α) (D : Set α) : Matroid α := M ↾ (M.E \ D)

/-- `M ＼ D` refers to the deletion of a set `D` from the matroid `M`. -/
scoped infixl:75 " ＼ " => Matroid.delete

/-
**Matroid.delete_eq_restrict** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：delete_eq_restrict (M : Matroid α) (D : Set α) : M ＼ D = M ↾ (M.E \ D)
参数：M : Matroid α；D : Set α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma delete_eq_restrict (M : Matroid α) (D : Set α) : M ＼ D = M ↾ (M.E \ D) := rfl
/-
**Matroid.restrict_compl** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：restrict_compl (M : Matroid α) (D : Set α) : M ↾ (M.E \ D) = M ＼ D
参数：M : Matroid α；D : Set α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma restrict_compl (M : Matroid α) (D : Set α) : M ↾ (M.E \ D) = M ＼ D := rfl

@[simp]
/-
**Matroid.delete_compl** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：delete_compl (hR : R subseteq M.E
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Matroid.restrict_compl`：restrict_compl (M : Matroid α) (D : Set α) : M ↾
 (M.E \ D) = M ＼ D
· 使用定理 `Set.sdiff_sdiff_cancel_left`：sdiff_sdiff_cancel_left {s t : Set α} (h : 
s subseteq t) : t \ (t \ s) = s
-/
lemma delete_compl (hR : R ⊆ M.E := by aesop_mat) : M ＼ (M.E \ R) = M ↾ R := by
  rw [← restrict_compl, sdiff_sdiff_cancel_left hR]

@[simp]
/-
**Matroid.delete_isRestriction** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：delete_isRestriction (M : Matroid α) (D : Set α) : M ＼ D <=r M
参数：M : Matroid α；D : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.restrict_isRestriction`：restrict_isRestriction (M : Matroid α) (
R : Set α) (hR : R subseteq M.E
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
-/
lemma delete_isRestriction (M : Matroid α) (D : Set α) : M ＼ D ≤r M :=
  restrict_isRestriction _ _ sdiff_subset
/-
**Matroid.IsRestriction.exists_eq_delete** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsRe
striction`。
形式化陈述：∀ {α : Type u_1} {M N : Matroid α}, N.IsRestriction M → ∃ D ⊆ M.E, N = M.d
elete D
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matroid.delete_compl`：delete_compl (hR : R subseteq M.E
· 使用定理 `Matroid.restrict_ground_eq`：∀ {α : Type u_1} {M : Matroid α} {R : Set α}
, (M.restrict R).E = R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma IsRestriction.exists_eq_delete (hNM : N ≤r M) : ∃ D ⊆ M.E, N = M ＼ D :=
  ⟨M.E \ N.E, sdiff_subset, by obtain ⟨R, hR, rfl⟩ := hNM; rw [delete_compl, restrict_ground_eq]⟩
/-
**Matroid.isRestriction_iff_exists_eq_delete** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`
。
形式化陈述：isRestriction_iff_exists_eq_delete : N <=r M ↔ exists D subseteq M.E, N = 
M ＼ D
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsRestriction.exists_eq_delete`：∀ {α : Type u_1} {M N : Matroid 
α}, N.IsRestriction M → ∃ D ⊆ M.E, N = M.delete D
· 使用引理 `Matroid.delete_isRestriction`：delete_isRestriction (M : Matroid α) (D : 
Set α) : M ＼ D <=r M
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma isRestriction_iff_exists_eq_delete : N ≤r M ↔ ∃ D ⊆ M.E, N = M ＼ D :=
  ⟨IsRestriction.exists_eq_delete, by rintro ⟨D, -, rfl⟩; apply delete_isRestriction⟩

@[simp]
/-
**Matroid.delete_ground** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：delete_ground (M : Matroid α) (D : Set α) : (M ＼ D).E = M.E \ D
参数：M : Matroid α；D : Set α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma delete_ground (M : Matroid α) (D : Set α) : (M ＼ D).E = M.E \ D := rfl

@[aesop unsafe 10% (rule_sets := [Matroid])]
/-
**Matroid.delete_subset_ground** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：delete_subset_ground (M : Matroid α) (D : Set α) : (M ＼ D).E subseteq M.E
参数：M : Matroid α；D : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
-/
lemma delete_subset_ground (M : Matroid α) (D : Set α) : (M ＼ D).E ⊆ M.E :=
  sdiff_subset

@[simp]
/-
**Matroid.delete_eq_self_iff** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：delete_eq_self_iff : M ＼ D = M ↔ Disjoint D M.E
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Matroid.restrict_compl`：restrict_compl (M : Matroid α) (D : Set α) : M ↾
 (M.E \ D) = M ＼ D
· 使用定理 `Matroid.restrict_eq_self_iff`：∀ {α : Type u_1} {M : Matroid α} {R : Set 
α}, M.restrict R = M ↔ R = M.E
· 使用定理 `sdiff_eq_left`：∀ {α : Type u} {x y : α} [inst : GeneralizedBooleanAlgebr
a α], x \ y = x ↔ Disjoint x y
· 使用定理 `disjoint_comm`：disjoint_comm : Disjoint a b ↔ Disjoint b a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma delete_eq_self_iff : M ＼ D = M ↔ Disjoint D M.E := by
  rw [← restrict_compl, restrict_eq_self_iff, sdiff_eq_left, disjoint_comm]

alias ⟨_, delete_eq_self⟩ := delete_eq_self_iff
/-
**Matroid.deleteElem_eq_self** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：deleteElem_eq_self (he : e ∉ M.E) : M ＼ {e} = M
参数：he : e ∉ M.E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
lemma deleteElem_eq_self (he : e ∉ M.E) : M ＼ {e} = M := by
  simpa

@[simp]
/-
**Matroid.delete_delete** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：delete_delete (M : Matroid α) (D₁ D₂ : Set α) : M ＼ D₁ ＼ D₂ = M ＼ (D₁ unio
n D₂)
参数：M : Matroid α；D₁ D₂ : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Matroid.restrict_compl`：restrict_compl (M : Matroid α) (D : Set α) : M ↾
 (M.E \ D) = M ＼ D
· 使用定理 `Matroid.restrict_restrict_eq`：restrict_restrict_eq {R₁ R₂ : Set α} (M : 
Matroid α) (hR : R₂ subseteq R₁) : (M ↾ R₁) ↾ R₂ = M ↾ R₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Matroid.restrict_ground_eq`：∀ {α : Type u_1} {M : Matroid α} {R : Set α}
, (M.restrict R).E = R
· 使用定理 `Set.sdiff_sdiff`：sdiff_sdiff {u : Set α} : (s \ t) \ u = s \ (t union u)
-/
lemma delete_delete (M : Matroid α) (D₁ D₂ : Set α) : M ＼ D₁ ＼ D₂ = M ＼ (D₁ ∪ D₂) := by
  rw [← restrict_compl, ← restrict_compl, ← restrict_compl, restrict_restrict_eq,
    restrict_ground_eq, sdiff_sdiff]
  simp
/-
**Matroid.delete_comm** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：delete_comm (M : Matroid α) (D₁ D₂ : Set α) : M ＼ D₁ ＼ D₂ = M ＼ D₂ ＼ D₁
参数：M : Matroid α；D₁ D₂ : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matroid.delete_delete`：delete_delete (M : Matroid α) (D₁ D₂ : Set α) : M
 ＼ D₁ ＼ D₂ = M ＼ (D₁ union D₂)
· 使用定理 `Set.union_comm`：union_comm (a b : Set α) : a union b = b union a
-/
lemma delete_comm (M : Matroid α) (D₁ D₂ : Set α) : M ＼ D₁ ＼ D₂ = M ＼ D₂ ＼ D₁ := by
  rw [delete_delete, union_comm, delete_delete]
/-
**Matroid.delete_inter_ground_eq** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：delete_inter_ground_eq (M : Matroid α) (D : Set α) : M ＼ (D inter M.E) = M
 ＼ D
参数：M : Matroid α；D : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Matroid.restrict_compl`：restrict_compl (M : Matroid α) (D : Set α) : M ↾
 (M.E \ D) = M ＼ D
· 使用定理 `Set.sdiff_inter_self_eq_sdiff`：sdiff_inter_self_eq_sdiff {s t : Set α} :
 s \ (t inter s) = s \ t
-/
lemma delete_inter_ground_eq (M : Matroid α) (D : Set α) : M ＼ (D ∩ M.E) = M ＼ D := by
  rw [← restrict_compl, ← restrict_compl, sdiff_inter_self_eq_sdiff]
/-
**Matroid.delete_eq_delete_iff** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：delete_eq_delete_iff {D₁ D₂ : Set α} : M ＼ D₁ = M ＼ D₂ ↔ D₁ inter M.E = D₂
 inter M.E
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Matroid.delete_inter_ground_eq`：delete_inter_ground_eq (M : Matroid α) (
D : Set α) : M ＼ (D inter M.E) = M ＼ D
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.sdiff_sdiff_cancel_left`：sdiff_sdiff_cancel_left {s t : Set α} (h : 
s subseteq t) : t \ (t \ s) = s
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
lemma delete_eq_delete_iff {D₁ D₂ : Set α} : M ＼ D₁ = M ＼ D₂ ↔ D₁ ∩ M.E = D₂ ∩ M.E := by
  rw [← delete_inter_ground_eq, ← M.delete_inter_ground_eq D₂]
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h]⟩
  apply_fun (M.E \ Matroid.E ·) at h
  simp_rw [delete_ground, sdiff_sdiff_cancel_left inter_subset_right] at h
  assumption

@[simp]
/-
**Matroid.delete_empty** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：delete_empty (M : Matroid α) : M ＼ ∅ = M
参数：M : Matroid α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matroid.delete_eq_self_iff`：delete_eq_self_iff : M ＼ D = M ↔ Disjoint D 
M.E
· 使用定理 `Set.empty_disjoint`：∀ {α : Type u} (s : Set α), Disjoint ∅ s
-/
lemma delete_empty (M : Matroid α) : M ＼ ∅ = M := by
  rw [delete_eq_self_iff]
  exact empty_disjoint _
/-
**Matroid.delete_delete_eq_delete_sdiff** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：delete_delete_eq_delete_sdiff (M : Matroid α) (D₁ D₂ : Set α) : M ＼ D₁ ＼ D
₂ = M ＼ D₁ ＼ (D₂ \ D₁)
参数：M : Matroid α；D₁ D₂ : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matroid.delete_delete`：delete_delete (M : Matroid α) (D₁ D₂ : Set α) : M
 ＼ D₁ ＼ D₂ = M ＼ (D₁ union D₂)
· 使用定理 `Set.union_sdiff_self`：union_sdiff_self {s t : Set α} : s union t \ s = s
 union t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma delete_delete_eq_delete_sdiff (M : Matroid α) (D₁ D₂ : Set α) :
    M ＼ D₁ ＼ D₂ = M ＼ D₁ ＼ (D₂ \ D₁) := by
  simp

@[deprecated (since := "2026-06-03")]
alias delete_delete_eq_delete_diff := delete_delete_eq_delete_sdiff
/-
**Matroid.IsRestriction.restrict_delete_of_disjoint** 是 Mathlib 中的一个定理，位于命名空间 `M
atroid.IsRestriction`。
形式化陈述：∀ {α : Type u_1} {M N : Matroid α} {X : Set α}, N.IsRestriction M → Disjoi
nt X N.E → N.IsRestriction (M.delete X)
参数：M.delete X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Matroid.isRestriction_iff_exists_eq_delete`：isRestriction_iff_exists_eq_
delete : N <=r M ↔ exists D subseteq M.E, N = M ＼ D
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.sdiff_subset_sdiff_left`：sdiff_subset_sdiff_left {s₁ s₂ t : Set α} (
h : s₁ subseteq s₂) : s₁ \ t subseteq s₂ \ t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matroid.delete_delete`：delete_delete (M : Matroid α) (D₁ D₂ : Set α) : M
 ＼ D₁ ＼ D₂ = M ＼ (D₁ union D₂)
· 使用定理 `Set.union_sdiff_self`：union_sdiff_self {s t : Set α} : s union t \ s = s
 union t
· 使用定理 `Set.union_comm`：union_comm (a b : Set α) : a union b = b union a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用引理 `Matroid.delete_eq_self_iff`：delete_eq_self_iff : M ＼ D = M ↔ Disjoint D 
M.E
-/
lemma IsRestriction.restrict_delete_of_disjoint (h : N ≤r M) (hX : Disjoint X N.E) :
    N ≤r (M ＼ X) := by
  obtain ⟨D, hD, rfl⟩ := isRestriction_iff_exists_eq_delete.1 h
  refine isRestriction_iff_exists_eq_delete.2 ⟨D \ X, sdiff_subset_sdiff_left hD, ?_⟩
  rwa [delete_delete, union_sdiff_self, union_comm, ← delete_delete, eq_comm,
    delete_eq_self_iff]
/-
**Matroid.IsRestriction.isRestriction_deleteElem** 是 Mathlib 中的一个定理，位于命名空间 `Matr
oid.IsRestriction`。
形式化陈述：∀ {α : Type u_1} {M N : Matroid α} {e : α}, N.IsRestriction M → e ∉ N.E → 
N.IsRestriction (M.delete {e})
参数：M.delete {e}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsRestriction.restrict_delete_of_disjoint`：∀ {α : Type u_1} {M N
 : Matroid α} {X : Set α}, N.IsRestriction M → Disjoint X N.E → N.IsRestriction 
(M.delete X)
-/
lemma IsRestriction.isRestriction_deleteElem (h : N ≤r M) (he : e ∉ N.E) : N ≤r M ＼ {e} :=
  h.restrict_delete_of_disjoint (by simpa)

/-! ### Independence and Bases -/

@[simp]
/-
**Matroid.delete_indep_iff** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：delete_indep_iff : (M ＼ D).Indep I ↔ M.Indep I ∧ Disjoint I D
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Matroid.restrict_compl`：restrict_compl (M : Matroid α) (D : Set α) : M ↾
 (M.E \ D) = M ＼ D
· 使用定理 `Matroid.restrict_indep_iff`：∀ {α : Type u_1} {M : Matroid α} {R I : Set 
α}, (M.restrict R).Indep I ↔ M.Indep I ∧ I ⊆ R
· 使用引理 `Set.subset_sdiff`：subset_sdiff : s subseteq t \ u ↔ s subseteq t ∧ Disjo
int s u
· 使用定理 `and_assoc`：∀ {a b c : Prop}, (a ∧ b) ∧ c ↔ a ∧ b ∧ c
· 使用定理 `and_iff_left_of_imp`：∀ {a b : Prop}, (a → b) → (a ∧ b ↔ a)
· 使用定理 `Matroid.Indep.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {I : Set α
}, M.Indep I → I ⊆ M.E
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
### Independence and Bases
-/
lemma delete_indep_iff : (M ＼ D).Indep I ↔ M.Indep I ∧ Disjoint I D := by
  rw [← restrict_compl, restrict_indep_iff, subset_sdiff, ← and_assoc,
    and_iff_left_of_imp Indep.subset_ground]
/-
**Matroid.deleteElem_indep_iff** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：deleteElem_indep_iff : (M ＼ {e}).Indep I ↔ M.Indep I ∧ e ∉ I
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
lemma deleteElem_indep_iff : (M ＼ {e}).Indep I ↔ M.Indep I ∧ e ∉ I := by
  simp
/-
**Matroid.Indep.of_delete** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Indep`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I D : Set α}, (M.delete D).Indep I → M.I
ndep I
参数：M.delete D。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Matroid.delete_indep_iff`：delete_indep_iff : (M ＼ D).Indep I ↔ M.Indep I
 ∧ Disjoint I D
-/
lemma Indep.of_delete (h : (M ＼ D).Indep I) : M.Indep I :=
  (delete_indep_iff.mp h).1
/-
**Matroid.Indep.indep_delete_of_disjoint** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Inde
p`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I D : Set α}, M.Indep I → Disjoint I D →
 (M.delete D).Indep I
参数：M.delete D。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Matroid.delete_indep_iff`：delete_indep_iff : (M ＼ D).Indep I ↔ M.Indep I
 ∧ Disjoint I D
-/
lemma Indep.indep_delete_of_disjoint (h : M.Indep I) (hID : Disjoint I D) : (M ＼ D).Indep I :=
  delete_indep_iff.mpr ⟨h, hID⟩
/-
**Matroid.indep_iff_delete_of_disjoint** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：indep_iff_delete_of_disjoint (hID : Disjoint I D) : M.Indep I ↔ (M ＼ D).In
dep I
参数：hID : Disjoint I D。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.Indep.indep_delete_of_disjoint`：∀ {α : Type u_1} {M : Matroid α}
 {I D : Set α}, M.Indep I → Disjoint I D → (M.delete D).Indep I
· 使用定理 `Matroid.Indep.of_delete`：∀ {α : Type u_1} {M : Matroid α} {I D : Set α},
 (M.delete D).Indep I → M.Indep I
-/
lemma indep_iff_delete_of_disjoint (hID : Disjoint I D) : M.Indep I ↔ (M ＼ D).Indep I :=
  ⟨fun h ↦ h.indep_delete_of_disjoint hID, fun h ↦ h.of_delete⟩

@[simp]
/-
**Matroid.delete_dep_iff** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：delete_dep_iff : (M ＼ D).Dep X ↔ M.Dep X ∧ Disjoint X D
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.dep_iff`：dep_iff : M.Dep D ↔ ¬M.Indep D ∧ D subseteq M.E
· 使用引理 `Matroid.delete_indep_iff`：delete_indep_iff : (M ＼ D).Indep I ↔ M.Indep I
 ∧ Disjoint I D
· 使用引理 `Matroid.delete_ground`：delete_ground (M : Matroid α) (D : Set α) : (M ＼ 
D).E = M.E \ D
· 使用引理 `Set.subset_sdiff`：subset_sdiff : s subseteq t \ u ↔ s subseteq t ∧ Disjo
int s u
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Decidable.not_and_iff_not_or_not'`：∀ {b a : Prop} [Decidable b], ¬(a ∧ b
) ↔ ¬a ∨ ¬b
-/
lemma delete_dep_iff : (M ＼ D).Dep X ↔ M.Dep X ∧ Disjoint X D := by
  rw [dep_iff, dep_iff, delete_indep_iff, delete_ground, subset_sdiff]; tauto

@[simp]
/-
**Matroid.delete_isBase_iff** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：delete_isBase_iff : (M ＼ D).IsBase B ↔ M.IsBasis B (M.E \ D)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Matroid.restrict_compl`：restrict_compl (M : Matroid α) (D : Set α) : M ↾
 (M.E \ D) = M ＼ D
· 使用定理 `Matroid.isBase_restrict_iff`：∀ {α : Type u_1} {M : Matroid α} {I X : Set
 α},   autoParam (X ⊆ M.E) Matroid.isBase_restrict_iff._auto_1 → ((M.restrict X)
.IsBase I ↔ M.IsB…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma delete_isBase_iff : (M ＼ D).IsBase B ↔ M.IsBasis B (M.E \ D) := by
  rw [← restrict_compl, isBase_restrict_iff]

@[simp]
/-
**Matroid.delete_isBasis_iff** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：delete_isBasis_iff : (M ＼ D).IsBasis I X ↔ M.IsBasis I X ∧ Disjoint X D
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Matroid.restrict_compl`：restrict_compl (M : Matroid α) (D : Set α) : M ↾
 (M.E \ D) = M ＼ D
· 使用定理 `Matroid.isBasis_restrict_iff`：isBasis_restrict_iff (hR : R subseteq M.E
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Set.subset_sdiff`：subset_sdiff : s subseteq t \ u ↔ s subseteq t ∧ Disjo
int s u
· 使用定理 `and_assoc`：∀ {a b c : Prop}, (a ∧ b) ∧ c ↔ a ∧ b ∧ c
· 使用定理 `and_iff_left_of_imp`：∀ {a b : Prop}, (a → b) → (a ∧ b ↔ a)
· 使用定理 `Matroid.IsBasis.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {I X : S
et α}, M.IsBasis I X → X ⊆ M.E
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma delete_isBasis_iff : (M ＼ D).IsBasis I X ↔ M.IsBasis I X ∧ Disjoint X D := by
  rw [← restrict_compl, isBasis_restrict_iff, subset_sdiff, ← and_assoc,
    and_iff_left_of_imp IsBasis.subset_ground]

@[simp]
/-
**Matroid.delete_isBasis'_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I D X : Set α}, (M.delete D).IsBasis' I 
X ↔ M.IsBasis' I (X \ D)
参数：M.delete D；X \ D。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.isBasis'_iff_isBasis_inter_ground`：∀ {α : Type u_1} {M : Matroid
 α} {I X : Set α}, M.IsBasis' I X ↔ M.IsBasis I (X ∩ M.E)
· 使用引理 `Matroid.delete_isBasis_iff`：delete_isBasis_iff : (M ＼ D).IsBasis I X ↔ M
.IsBasis I X ∧ Disjoint X D
· 使用引理 `Matroid.delete_ground`：delete_ground (M : Matroid α) (D : Set α) : (M ＼ 
D).E = M.E \ D
· 使用定理 `Set.sdiff_eq`：sdiff_eq (s t : Set α) : s \ t = s inter tᶜ
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.inter_assoc`：inter_assoc (a b c : Set α) : a inter b inter c = a int
er (b inter c)
· 使用定理 `and_iff_left_iff_imp`：∀ {a b : Prop}, (a ∧ b ↔ a) ↔ a → b
· 使用引理 `Set.inter_sdiff_assoc`：inter_sdiff_assoc (a b c : Set α) : (a inter b) \
 c = a inter (b \ c)
· 使用引理 `Set.disjoint_sdiff_left`：disjoint_sdiff_left : Disjoint (t \ s) s
-/
lemma delete_isBasis'_iff : (M ＼ D).IsBasis' I X ↔ M.IsBasis' I (X \ D) := by
  rw [isBasis'_iff_isBasis_inter_ground, delete_isBasis_iff, delete_ground, sdiff_eq,
    inter_comm M.E, ← inter_assoc, ← sdiff_eq, ← isBasis'_iff_isBasis_inter_ground,
    and_iff_left_iff_imp, inter_comm, ← inter_sdiff_assoc]
  exact fun _ ↦ disjoint_sdiff_left
/-
**Matroid.IsBasis.of_delete** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBasis`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I D X : Set α}, (M.delete D).IsBasis I X
 → M.IsBasis I X
参数：M.delete D。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Matroid.delete_isBasis_iff`：delete_isBasis_iff : (M ＼ D).IsBasis I X ↔ M
.IsBasis I X ∧ Disjoint X D
-/
lemma IsBasis.of_delete (h : (M ＼ D).IsBasis I X) : M.IsBasis I X :=
  (delete_isBasis_iff.mp h).1
/-
**Matroid.IsBasis.delete** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBasis`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I D X : Set α}, M.IsBasis I X → Disjoint
 X D → (M.delete D).IsBasis I X
参数：M.delete D。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matroid.delete_isBasis_iff`：delete_isBasis_iff : (M ＼ D).IsBasis I X ↔ M
.IsBasis I X ∧ Disjoint X D
-/
lemma IsBasis.delete (h : M.IsBasis I X) (hX : Disjoint X D) : (M ＼ D).IsBasis I X := by
  rw [delete_isBasis_iff]; exact ⟨h, hX⟩
/-
**Matroid.Coindep.delete_isBase_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Coindep`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {B D : Set α}, M.Coindep D → ((M.delete D
).IsBase B ↔ M.IsBase B ∧ Disjoint B D)
参数：(M.delete D).IsBase B ↔ M.IsBase B ∧ Disjoint B D。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matroid.delete_isBase_iff`：delete_isBase_iff : (M ＼ D).IsBase B ↔ M.IsBa
sis B (M.E \ D)
· 使用定理 `Matroid.IsBasis.subset`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, 
M.IsBasis I X → I ⊆ X
· 使用定理 `Matroid.IsBasis.isBasis_closure_right`：∀ {α : Type u_2} {M : Matroid α} 
{X I : Set α}, M.IsBasis I X → M.IsBasis I (M.closure X)
· 使用定理 `Matroid.isBasis_ground_iff`：∀ {α : Type u_1} {M : Matroid α} {B : Set α}
, M.IsBasis B M.E ↔ M.IsBase B
· 使用定理 `Matroid.Coindep.closure_compl`：∀ {α : Type u_2} {M : Matroid α} {X : Set
 α}, M.Coindep X → M.closure (M.E \ X) = M.E
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `Set.subset_sdiff`：subset_sdiff : s subseteq t \ u ↔ s subseteq t ∧ Disjo
int s u
· 使用定理 `Matroid.IsBasis.isBasis_subset`：∀ {α : Type u_1} {M : Matroid α} {I X Y 
: Set α}, M.IsBasis I X → I ⊆ Y → Y ⊆ X → M.IsBasis I Y
· 使用定理 `Matroid.IsBase.isBasis_ground`：∀ {α : Type u_1} {M : Matroid α} {B : Set
 α}, M.IsBase B → M.IsBasis B M.E
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Matroid.IsBase.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {B : Set 
α}, M.IsBase B → B ⊆ M.E
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
-/
lemma Coindep.delete_isBase_iff (hD : M.Coindep D) :
    (M ＼ D).IsBase B ↔ M.IsBase B ∧ Disjoint B D := by
  rw [Matroid.delete_isBase_iff]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have hss := h.subset
    rw [subset_sdiff] at hss
    have hcl := h.isBasis_closure_right
    rw [hD.closure_compl, isBasis_ground_iff] at hcl
    exact ⟨hcl, hss.2⟩
  exact h.1.isBasis_ground.isBasis_subset (by simp [subset_sdiff, h.1.subset_ground, h.2])
    sdiff_subset
/-
**Matroid.Coindep.delete_rankPos** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Coindep`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {D : Set α} [M.RankPos], M.Coindep D → (M
.delete D).RankPos
参数：M.delete D。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.rankPos_iff`：∀ {α : Type u_1} (M : Matroid α), M.RankPos ↔ ¬M.Is
Base ∅
· 使用定理 `Matroid.Coindep.delete_isBase_iff`：∀ {α : Type u_1} {M : Matroid α} {B D
 : Set α}, M.Coindep D → ((M.delete D).IsBase B ↔ M.IsBase B ∧ Disjoint B D)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Matroid.empty_not_isBase`：empty_not_isBase [h : RankPos M] : ¬M.IsBase ∅
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma Coindep.delete_rankPos [M.RankPos] (hD : M.Coindep D) : (M ＼ D).RankPos := by
  rw [rankPos_iff, hD.delete_isBase_iff]
  simp [M.empty_not_isBase]
/-
**Matroid.Coindep.delete_spanning_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Coindep
`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {D S : Set α}, M.Coindep D → ((M.delete D
).Spanning S ↔ M.Spanning S ∧ Disjoint S D)
参数：(M.delete D).Spanning S ↔ M.Spanning S ∧ Disjoint S D。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matroid.Coindep.delete_isBase_iff`：∀ {α : Type u_1} {M : Matroid α} {B D
 : Set α}, M.Coindep D → ((M.delete D).IsBase B ↔ M.IsBase B ∧ Disjoint B D)
· 使用定理 `Disjoint.mono_left`：Disjoint.mono_left (h : a <= b) : Disjoint b c -> Di
sjoint a c
-/
lemma Coindep.delete_spanning_iff {S : Set α} (hD : M.Coindep D) :
    (M ＼ D).Spanning S ↔ M.Spanning S ∧ Disjoint S D := by
  simp only [spanning_iff_exists_isBase_subset', hD.delete_isBase_iff, and_assoc, delete_ground,
    subset_sdiff, and_congr_left_iff, and_imp]
  refine fun hSE hSD ↦ ⟨fun ⟨B, hB, hBD, hBS⟩ ↦ ⟨B, hB, hBS⟩, fun ⟨B, hB, hBS⟩ ↦ ⟨B, hB, ?_, hBS⟩⟩
  exact hSD.mono_left hBS

/-! ### Loops, circuits and closure -/

@[simp]
/-
**Matroid.delete_isLoop_iff** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：delete_isLoop_iff : (M ＼ D).IsLoop e ↔ M.IsLoop e ∧ e ∉ D
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Matroid.singleton_dep`：singleton_dep : M.Dep {e} ↔ M.IsLoop e
· 使用引理 `Matroid.delete_dep_iff`：delete_dep_iff : (M ＼ D).Dep X ↔ M.Dep X ∧ Disjo
int X D
· 使用引理 `Set.disjoint_singleton_left`：disjoint_singleton_left : Disjoint {a} s ↔ 
a ∉ s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
### Loops, circuits and closure
-/
lemma delete_isLoop_iff : (M ＼ D).IsLoop e ↔ M.IsLoop e ∧ e ∉ D := by
  rw [← singleton_dep, delete_dep_iff, disjoint_singleton_left, singleton_dep]

@[simp]
/-
**Matroid.delete_isNonloop_iff** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：delete_isNonloop_iff : (M ＼ D).IsNonloop e ↔ M.IsNonloop e ∧ e ∉ D
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Matroid.indep_singleton`：indep_singleton : M.Indep {e} ↔ M.IsNonloop e
· 使用引理 `Matroid.delete_indep_iff`：delete_indep_iff : (M ＼ D).Indep I ↔ M.Indep I
 ∧ Disjoint I D
· 使用引理 `Set.disjoint_singleton_left`：disjoint_singleton_left : Disjoint {a} s ↔ 
a ∉ s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma delete_isNonloop_iff : (M ＼ D).IsNonloop e ↔ M.IsNonloop e ∧ e ∉ D := by
  rw [← indep_singleton, delete_indep_iff, disjoint_singleton_left, indep_singleton]
/-
**Matroid.IsNonloop.of_delete** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsNonloop`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {e : α} {D : Set α}, (M.delete D).IsNonlo
op e → M.IsNonloop e
参数：M.delete D。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Matroid.delete_isNonloop_iff`：delete_isNonloop_iff : (M ＼ D).IsNonloop e
 ↔ M.IsNonloop e ∧ e ∉ D
-/
lemma IsNonloop.of_delete (h : (M ＼ D).IsNonloop e) : M.IsNonloop e :=
  (delete_isNonloop_iff.1 h).1
/-
**Matroid.isNonloop_iff_delete_of_notMem** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：isNonloop_iff_delete_of_notMem (he : e ∉ D) : M.IsNonloop e ↔ (M ＼ D).IsNo
nloop e
参数：he : e ∉ D。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Matroid.delete_isNonloop_iff`：delete_isNonloop_iff : (M ＼ D).IsNonloop e
 ↔ M.IsNonloop e ∧ e ∉ D
· 使用定理 `Matroid.IsNonloop.of_delete`：∀ {α : Type u_1} {M : Matroid α} {e : α} {D
 : Set α}, (M.delete D).IsNonloop e → M.IsNonloop e
-/
lemma isNonloop_iff_delete_of_notMem (he : e ∉ D) : M.IsNonloop e ↔ (M ＼ D).IsNonloop e :=
  ⟨fun h ↦ delete_isNonloop_iff.2 ⟨h, he⟩, fun h ↦ h.of_delete⟩
/-
**Matroid.delete_loops_eq_removeLoops** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：delete_loops_eq_removeLoops (M : Matroid α) : M ＼ M.loops = M.removeLoops
参数：M : Matroid α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.removeLoops.eq_1`：∀ {α : Type u_1} (M : Matroid α), M.removeLoop
s = M.restrict {e | M.IsNonloop e}
· 使用引理 `Matroid.delete_eq_restrict`：delete_eq_restrict (M : Matroid α) (D : Set 
α) : M ＼ D = M ↾ (M.E \ D)
· 使用引理 `Matroid.compl_loops_eq`：compl_loops_eq (M : Matroid α) : M.E \ M.loops =
 {e | M.IsNonloop e}
-/
lemma delete_loops_eq_removeLoops (M : Matroid α) : M ＼ M.loops = M.removeLoops := by
  rw [removeLoops, delete_eq_restrict, compl_loops_eq]

@[simp]
/-
**Matroid.delete_isCircuit_iff** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：delete_isCircuit_iff {C : Set α} : (M ＼ D).IsCircuit C ↔ M.IsCircuit C ∧ D
isjoint C D
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matroid.delete_eq_restrict`：delete_eq_restrict (M : Matroid α) (D : Set 
α) : M ＼ D = M ↾ (M.E \ D)
· 使用引理 `Matroid.restrict_isCircuit_iff`：restrict_isCircuit_iff (hR : R subseteq 
M.E
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `and_congr_right_iff`：∀ {a b c : Prop}, (a ∧ b ↔ a ∧ c) ↔ a → (b ↔ c)
· 使用引理 `Set.subset_sdiff`：subset_sdiff : s subseteq t \ u ↔ s subseteq t ∧ Disjo
int s u
· 使用定理 `and_iff_right_iff_imp`：∀ {a b : Prop}, (a ∧ b ↔ b) ↔ b → a
· 使用定理 `Matroid.IsCircuit.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {C : S
et α}, M.IsCircuit C → C ⊆ M.E
-/
lemma delete_isCircuit_iff {C : Set α} :
    (M ＼ D).IsCircuit C ↔ M.IsCircuit C ∧ Disjoint C D := by
  rw [delete_eq_restrict, restrict_isCircuit_iff, and_congr_right_iff, subset_sdiff,
    and_iff_right_iff_imp]
  exact fun h _ ↦ h.subset_ground
/-
**Matroid.IsCircuit.of_delete** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsCircuit`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {D C : Set α}, (M.delete D).IsCircuit C →
 M.IsCircuit C
参数：M.delete D。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Matroid.delete_isCircuit_iff`：delete_isCircuit_iff {C : Set α} : (M ＼ D)
.IsCircuit C ↔ M.IsCircuit C ∧ Disjoint C D
-/
lemma IsCircuit.of_delete {C : Set α} (h : (M ＼ D).IsCircuit C) : M.IsCircuit C :=
  (delete_isCircuit_iff.1 h).1
/-
**Matroid.circuit_iff_delete_of_disjoint** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：circuit_iff_delete_of_disjoint {C : Set α} (hCD : Disjoint C D) : M.IsCirc
uit C ↔ (M ＼ D).IsCircuit C
参数：hCD : Disjoint C D。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Matroid.delete_isCircuit_iff`：delete_isCircuit_iff {C : Set α} : (M ＼ D)
.IsCircuit C ↔ M.IsCircuit C ∧ Disjoint C D
· 使用定理 `Matroid.IsCircuit.of_delete`：∀ {α : Type u_1} {M : Matroid α} {D C : Set
 α}, (M.delete D).IsCircuit C → M.IsCircuit C
-/
lemma circuit_iff_delete_of_disjoint {C : Set α} (hCD : Disjoint C D) :
    M.IsCircuit C ↔ (M ＼ D).IsCircuit C :=
  ⟨fun h ↦ delete_isCircuit_iff.2 ⟨h, hCD⟩, fun h ↦ h.of_delete⟩

@[simp]
/-
**Matroid.delete_closure_eq** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：delete_closure_eq (M : Matroid α) (D X : Set α) : (M ＼ D).closure X = M.cl
osure (X \ D) \ D
参数：M : Matroid α；D X : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Matroid.restrict_compl`：restrict_compl (M : Matroid α) (D : Set α) : M ↾
 (M.E \ D) = M ＼ D
· 使用定理 `Matroid.restrict_closure_eq'`：∀ {α : Type u_2} (M : Matroid α) (X R : Se
t α), (M.restrict R).closure X = M.closure (X ∩ R) ∩ R ∪ R \ M.E
· 使用定理 `sdiff_sdiff_self`：sdiff_sdiff_self : (a \ b) \ a = ⊥
· 使用定理 `Set.bot_eq_empty`：bot_eq_empty : (⊥ : Set α) = ∅
· 使用定理 `Set.union_empty`：union_empty (a : Set α) : a union ∅ = a
· 使用定理 `Set.sdiff_eq`：sdiff_eq (s t : Set α) : s \ t = s inter tᶜ
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `Set.inter_assoc`：inter_assoc (a b c : Set α) : a inter b inter c = a int
er (b inter c)
· 使用定理 `Matroid.closure_inter_ground`：∀ {α : Type u_2} (M : Matroid α) (X : Set 
α), M.closure (X ∩ M.E) = M.closure X
· 使用定理 `Set.inter_eq_left`：∀ {α : Type u} {s t : Set α}, s ∩ t = s ↔ s ⊆ t
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
· 使用引理 `Matroid.closure_subset_ground`：closure_subset_ground (M : Matroid α) (X 
: Set α) : M.closure X subseteq M.E
-/
lemma delete_closure_eq (M : Matroid α) (D X : Set α) :
    (M ＼ D).closure X = M.closure (X \ D) \ D := by
  rw [← restrict_compl, restrict_closure_eq', sdiff_sdiff_self, bot_eq_empty, union_empty,
    sdiff_eq, inter_comm M.E, ← inter_assoc X, ← sdiff_eq, closure_inter_ground,
    ← inter_assoc, ← sdiff_eq, inter_eq_left]
  exact sdiff_subset.trans (M.closure_subset_ground _)
/-
**Matroid.delete_closure_eq_of_disjoint** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：delete_closure_eq_of_disjoint (M : Matroid α) {D X : Set α} (hXD : Disjoin
t X D) : (M ＼ D).closure X = M.closure X \ D
参数：M : Matroid α；hXD : Disjoint X D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matroid.delete_closure_eq`：delete_closure_eq (M : Matroid α) (D X : Set 
α) : (M ＼ D).closure X = M.closure (X \ D) \ D
· 使用定理 `Disjoint.sdiff_eq_left`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlg
ebra α] {a b : α}, Disjoint a b → a \ b = a
-/
lemma delete_closure_eq_of_disjoint (M : Matroid α) {D X : Set α} (hXD : Disjoint X D) :
    (M ＼ D).closure X = M.closure X \ D := by
  rw [delete_closure_eq, hXD.sdiff_eq_left]

@[simp]
/-
**Matroid.delete_loops_eq** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：delete_loops_eq (M : Matroid α) (D : Set α) : (M ＼ D).loops = M.loops \ D
参数：M : Matroid α；D : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matroid.delete_closure_eq`：delete_closure_eq (M : Matroid α) (D X : Set 
α) : (M ＼ D).closure X = M.closure (X \ D) \ D
· 使用定理 `Set.empty_sdiff`：empty_sdiff (s : Set α) : (∅ \ s : Set α) = ∅
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma delete_loops_eq (M : Matroid α) (D : Set α) : (M ＼ D).loops = M.loops \ D := by
  simp [loops]
/-
**Matroid.delete_isColoop_iff** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：delete_isColoop_iff (M : Matroid α) (D : Set α) : (M ＼ D).IsColoop e ↔ e ∉
 M.closure ((M.E \ D) \ {e}) ∧ e in M.E ∧ e ∉ D
参数：M : Matroid α；D : Set α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matroid.delete_eq_restrict`：delete_eq_restrict (M : Matroid α) (D : Set 
α) : M ＼ D = M ↾ (M.E \ D)
· 使用引理 `Matroid.restrict_isColoop_iff`：restrict_isColoop_iff {R : Set α} (hRE : 
R subseteq M.E) : (M ↾ R).IsColoop e ↔ e ∉ M.closure (R \ {e}) ∧ e in R
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
· 使用定理 `Set.mem_sdiff`：mem_sdiff {s t : Set α} (x : α) : x in s \ t ↔ x in s ∧ x
 ∉ t
· 使用定理 `and_congr_left_iff`：∀ {a c b : Prop}, (a ∧ c ↔ b ∧ c) ↔ c → (a ↔ b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma delete_isColoop_iff (M : Matroid α) (D : Set α) :
    (M ＼ D).IsColoop e ↔ e ∉ M.closure ((M.E \ D) \ {e}) ∧ e ∈ M.E ∧ e ∉ D := by
  rw [delete_eq_restrict, restrict_isColoop_iff sdiff_subset, mem_sdiff, and_congr_left_iff]
  simp

/-! ### Finiteness -/

/-
**Matroid.delete_finitary** 是 Mathlib 中的一个实例，位于命名空间 `Matroid`。
形式化陈述：delete_finitary (M : Matroid α) [Finitary M] (D : Set α) : Finitary (M ＼ D
)
参数：M : Matroid α；D : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Finiteness
-/
instance delete_finitary (M : Matroid α) [Finitary M] (D : Set α) : Finitary (M ＼ D) :=
  inferInstanceAs <| Finitary (M ↾ (M.E \ D))
/-
**Matroid.delete_finite** 是 Mathlib 中的一个实例，位于命名空间 `Matroid`。
形式化陈述：delete_finite [M.Finite] : (M ＼ D).Finite
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.sdiff`：∀ {α : Type u} {s t : Set α}, s.Finite → (s \ t).Finit
e
· 使用定理 `Matroid.ground_finite`：ground_finite (M : Matroid α) [M.Finite] : M.E.Fi
nite
-/
instance delete_finite [M.Finite] : (M ＼ D).Finite :=
  ⟨M.ground_finite.sdiff⟩
/-
**Matroid.delete_rankFinite** 是 Mathlib 中的一个实例，位于命名空间 `Matroid`。
形式化陈述：delete_rankFinite [RankFinite M] : RankFinite (M ＼ D)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance delete_rankFinite [RankFinite M] : RankFinite (M ＼ D) :=
  restrict_rankFinite _

end Delete

end Matroid

