/-
Copyright (c) 2025 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson
-/
module

public import Mathlib.Combinatorics.Matroid.Minor.Delete
public import Mathlib.Tactic.TautoSet

/-!
# Matroid Contraction

Instead of deleting the elements of `X : Set α` from `M : Matroid α`, we can contract them.
The *contraction* of `X` from `M`, denoted `M ／ X`, is the matroid on ground set `M.E \ X`
in which a set `I` is independent if and only if `I ∪ J` is independent in `M`,
where `J` is an arbitrarily chosen basis for `X`. Contraction corresponds to contracting
edges in graphic matroids (hence the name) and corresponds to projecting to a quotient
space in the case of linearly representable matroids. It is an important notion in both
these settings.

We can also define contraction much more tersely in terms of deletion and duality
with `M ／ X = (M✶ ＼ X)✶`: that is, contraction is the dual operation of deletion.
While this is perhaps less intuitive, we use this very concise expression as the definition,
and prove with the lemma `Matroid.IsBasis.contract_indep_iff` that this is equivalent to
the more verbose definition above.

## Main Declarations

* `Matroid.contract M C`, written `M ／ C`, is the matroid on ground set `M.E \ C` in which a set
  `I ⊆ M.E \ C` is independent if and only if `I ∪ J` is independent in `M`,
  where `J` is an arbitrary basis for `C`.
* `Matroid.contract_dual M C : (M ／ X)✶ = M✶ ＼ X`; the dual of contraction is deletion.
* `Matroid.delete_dual M C : (M ＼ X)✶ = M✶ ／ X`; the dual of deletion is contraction.
* `Matroid.IsBasis.contract_indep_iff`; if `I` is a basis for `C`, then the independent
  sets of `M ／ C` are exactly the `J ⊆ M.E \ C` for which `I ∪ J` is independent in `M`.
* `Matroid.contract_delete_comm` : `M ／ C ＼ D = M ＼ D ／ C` for disjoint `C` and `D`.

## Naming conventions

Mirroring the convention for deletion, we use the abbreviation `contractElem` in lemma names
to refer to the contraction `M ／ {e}` of a single element `e : α` from `M : Matroid α`.
-/

@[expose] public section

open Set

variable {α : Type*} {M M' N : Matroid α} {e f : α} {I J R D B X Y Z K : Set α}

namespace Matroid

section Contract

variable {C C₁ C₂ : Set α}

/-- The contraction `M ／ C` is the matroid on `M.E \ C` in which a set `I ⊆ M.E \ C` is independent
if and only if `I ∪ J` is independent, where `J` is an arbitrarily chosen basis for `C`.
It is also equal by definition to `(M✶ ＼ C)✶`; see `Matroid.IsBasis.contract_indep_iff` for
a proof that its independent sets are the claimed ones. -/
/-
**Matroid.contract** 是 Mathlib 中的一个定义，位于命名空间 `Matroid`。
形式化陈述：contract (M : Matroid α) (C : Set α) : Matroid α
参数：M : Matroid α；C : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The contraction `M ／ C` is the matroid on `M.E \ C` in which a set `I ⊆ M.E \ C`
 is independent
if and only if `I ∪ J` is independent, where `J` is an arbitrarily chosen basis 
for `C`.
It is also equal by definition to `(M✶ ＼ C)✶`; see `Matroid.IsBasis.contract_ind
ep_iff` for
a proof that its independent sets are the claimed ones.
-/
def contract (M : Matroid α) (C : Set α) : Matroid α := (M✶ ＼ C)✶

/-- `M ／ C` refers to the contraction of a set `C` from the matroid `M`. -/
scoped infixl:75 " ／ " => Matroid.contract

/-
**Matroid.contract_ground** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_1} (M : Matroid α) (C : Set α), (M.contract C).E = M.E \ C
参数：M : Matroid α；C : Set α；M.contract C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma contract_ground (M : Matroid α) (C : Set α) : (M ／ C).E = M.E \ C := rfl
/-
**Matroid.dual_delete_dual** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：dual_delete_dual (M : Matroid α) (X : Set α) : (M✶ ＼ X)✶ = M ／ X
参数：M : Matroid α；X : Set α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma dual_delete_dual (M : Matroid α) (X : Set α) : (M✶ ＼ X)✶ = M ／ X := rfl

@[simp]
/-
**Matroid.dual_delete** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：dual_delete (M : Matroid α) (X : Set α) : (M ＼ X)✶ = M✶ ／ X
参数：M : Matroid α；X : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.dual_dual`：∀ {α : Type u_1} (M : Matroid α), M✶✶ = M
· 使用引理 `Matroid.dual_delete_dual`：dual_delete_dual (M : Matroid α) (X : Set α) :
 (M✶ ＼ X)✶ = M ／ X
-/
lemma dual_delete (M : Matroid α) (X : Set α) : (M ＼ X)✶ = M✶ ／ X := by
  rw [← dual_dual M, dual_delete_dual, dual_dual]

@[simp]
/-
**Matroid.dual_contract** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：dual_contract (M : Matroid α) (X : Set α) : (M ／ X)✶ = M✶ ＼ X
参数：M : Matroid α；X : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Matroid.dual_delete_dual`：dual_delete_dual (M : Matroid α) (X : Set α) :
 (M✶ ＼ X)✶ = M ／ X
· 使用定理 `Matroid.dual_dual`：∀ {α : Type u_1} (M : Matroid α), M✶✶ = M
-/
lemma dual_contract (M : Matroid α) (X : Set α) : (M ／ X)✶ = M✶ ＼ X := by
  rw [← dual_delete_dual, dual_dual]
/-
**Matroid.dual_contract_dual** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：dual_contract_dual (M : Matroid α) (X : Set α) : (M✶ ／ X)✶ = M ＼ X
参数：M : Matroid α；X : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matroid.dual_contract`：dual_contract (M : Matroid α) (X : Set α) : (M ／ 
X)✶ = M✶ ＼ X
· 使用定理 `Matroid.dual_dual`：∀ {α : Type u_1} (M : Matroid α), M✶✶ = M
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma dual_contract_dual (M : Matroid α) (X : Set α) : (M✶ ／ X)✶ = M ＼ X := by
  simp

@[simp]
/-
**Matroid.contract_contract** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：contract_contract (M : Matroid α) (C₁ C₂ : Set α) : M ／ C₁ ／ C₂ = M ／ (C₁ 
union C₂)
参数：M : Matroid α；C₁ C₂ : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matroid.dual_contract`：dual_contract (M : Matroid α) (X : Set α) : (M ／ 
X)✶ = M✶ ＼ X
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Matroid.delete_delete`：delete_delete (M : Matroid α) (D₁ D₂ : Set α) : M
 ＼ D₁ ＼ D₂ = M ＼ (D₁ union D₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma contract_contract (M : Matroid α) (C₁ C₂ : Set α) : M ／ C₁ ／ C₂ = M ／ (C₁ ∪ C₂) := by
  simp [← dual_inj]
/-
**Matroid.contract_comm** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：contract_comm (M : Matroid α) (C₁ C₂ : Set α) : M ／ C₁ ／ C₂ = M ／ C₂ ／ C₁
参数：M : Matroid α；C₁ C₂ : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matroid.contract_contract`：contract_contract (M : Matroid α) (C₁ C₂ : Se
t α) : M ／ C₁ ／ C₂ = M ／ (C₁ union C₂)
· 使用定理 `Set.union_comm`：union_comm (a b : Set α) : a union b = b union a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma contract_comm (M : Matroid α) (C₁ C₂ : Set α) : M ／ C₁ ／ C₂ = M ／ C₂ ／ C₁ := by
  simp [union_comm]
/-
**Matroid.dual_contract_delete** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：dual_contract_delete (M : Matroid α) (X Y : Set α) : (M ／ X ＼ Y)✶ = M✶ ＼ X
 ／ Y
参数：M : Matroid α；X Y : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matroid.dual_delete`：dual_delete (M : Matroid α) (X : Set α) : (M ＼ X)✶ 
= M✶ ／ X
· 使用引理 `Matroid.dual_contract`：dual_contract (M : Matroid α) (X : Set α) : (M ／ 
X)✶ = M✶ ＼ X
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma dual_contract_delete (M : Matroid α) (X Y : Set α) : (M ／ X ＼ Y)✶ = M✶ ＼ X ／ Y := by
  simp
/-
**Matroid.dual_delete_contract** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：dual_delete_contract (M : Matroid α) (X Y : Set α) : (M ＼ X ／ Y)✶ = M✶ ／ X
 ＼ Y
参数：M : Matroid α；X Y : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matroid.dual_contract`：dual_contract (M : Matroid α) (X : Set α) : (M ／ 
X)✶ = M✶ ＼ X
· 使用引理 `Matroid.dual_delete`：dual_delete (M : Matroid α) (X : Set α) : (M ＼ X)✶ 
= M✶ ／ X
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma dual_delete_contract (M : Matroid α) (X Y : Set α) : (M ＼ X ／ Y)✶ = M✶ ／ X ＼ Y := by
  simp
/-
**Matroid.contract_eq_self_iff** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：contract_eq_self_iff : M ／ C = M ↔ Disjoint C M.E
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Matroid.dual_delete_dual`：dual_delete_dual (M : Matroid α) (X : Set α) :
 (M✶ ＼ X)✶ = M ／ X
· 使用定理 `Matroid.dual_inj`：∀ {α : Type u_1} {M₁ M₂ : Matroid α}, M₁✶ = M₂✶ ↔ M₁ =
 M₂
· 使用定理 `Matroid.dual_dual`：∀ {α : Type u_1} (M : Matroid α), M✶✶ = M
· 使用引理 `Matroid.delete_eq_self_iff`：delete_eq_self_iff : M ＼ D = M ↔ Disjoint D 
M.E
· 使用定理 `Matroid.dual_ground`：∀ {α : Type u_1} {M : Matroid α}, M✶.E = M.E
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma contract_eq_self_iff : M ／ C = M ↔ Disjoint C M.E := by
  rw [← dual_delete_dual, ← dual_inj, dual_dual, delete_eq_self_iff, dual_ground]
/-
**Matroid.contractElem_eq_self** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：contractElem_eq_self (he : e ∉ M.E) : M ／ {e} = M
参数：he : e ∉ M.E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Matroid.dual_delete_dual`：dual_delete_dual (M : Matroid α) (X : Set α) :
 (M✶ ＼ X)✶ = M ／ X
· 使用引理 `Matroid.deleteElem_eq_self`：deleteElem_eq_self (he : e ∉ M.E) : M ＼ {e} 
= M
· 使用定理 `Matroid.dual_dual`：∀ {α : Type u_1} (M : Matroid α), M✶✶ = M
-/
lemma contractElem_eq_self (he : e ∉ M.E) : M ／ {e} = M := by
  rw [← dual_delete_dual, deleteElem_eq_self (by simpa), dual_dual]
/-
**Matroid.contract_empty** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_1} (M : Matroid α), M.contract ∅ = M
参数：M : Matroid α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Matroid.dual_delete_dual`：dual_delete_dual (M : Matroid α) (X : Set α) :
 (M✶ ＼ X)✶ = M ／ X
· 使用引理 `Matroid.delete_empty`：delete_empty (M : Matroid α) : M ＼ ∅ = M
· 使用定理 `Matroid.dual_dual`：∀ {α : Type u_1} (M : Matroid α), M✶✶ = M
-/
@[simp] lemma contract_empty (M : Matroid α) : M ／ ∅ = M := by
  rw [← dual_delete_dual, delete_empty, dual_dual]
/-
**Matroid.contract_contract_eq_contract_sdiff** 是 Mathlib 中的一个引理，位于命名空间 `Matroid
`。
形式化陈述：contract_contract_eq_contract_sdiff (M : Matroid α) (C₁ C₂ : Set α) : M ／ 
C₁ ／ C₂ = M ／ C₁ ／ (C₂ \ C₁)
参数：M : Matroid α；C₁ C₂ : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matroid.contract_contract`：contract_contract (M : Matroid α) (C₁ C₂ : Se
t α) : M ／ C₁ ／ C₂ = M ／ (C₁ union C₂)
· 使用定理 `Set.union_sdiff_self`：union_sdiff_self {s t : Set α} : s union t \ s = s
 union t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma contract_contract_eq_contract_sdiff (M : Matroid α) (C₁ C₂ : Set α) :
    M ／ C₁ ／ C₂ = M ／ C₁ ／ (C₂ \ C₁) := by
  simp

@[deprecated (since := "2026-06-03")]
alias contract_contract_eq_contract_diff := contract_contract_eq_contract_sdiff
/-
**Matroid.contract_eq_contract_iff** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：contract_eq_contract_iff : M ／ C₁ = M ／ C₂ ↔ C₁ inter M.E = C₂ inter M.E
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Matroid.dual_delete_dual`：dual_delete_dual (M : Matroid α) (X : Set α) :
 (M✶ ＼ X)✶ = M ／ X
· 使用定理 `Matroid.dual_inj`：∀ {α : Type u_1} {M₁ M₂ : Matroid α}, M₁✶ = M₂✶ ↔ M₁ =
 M₂
· 使用引理 `Matroid.delete_eq_delete_iff`：delete_eq_delete_iff {D₁ D₂ : Set α} : M ＼
 D₁ = M ＼ D₂ ↔ D₁ inter M.E = D₂ inter M.E
· 使用定理 `Matroid.dual_ground`：∀ {α : Type u_1} {M : Matroid α}, M✶.E = M.E
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma contract_eq_contract_iff : M ／ C₁ = M ／ C₂ ↔ C₁ ∩ M.E = C₂ ∩ M.E := by
  rw [← dual_delete_dual, ← dual_delete_dual, dual_inj, delete_eq_delete_iff, dual_ground]
/-
**Matroid.contract_inter_ground_eq** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_1} (M : Matroid α) (C : Set α), M.contract (C ∩ M.E) = M.con
tract C
参数：M : Matroid α；C : Set α；C ∩ M.E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Matroid.dual_delete_dual`：dual_delete_dual (M : Matroid α) (X : Set α) :
 (M✶ ＼ X)✶ = M ／ X
· 使用定理 `Matroid.dual_ground`：∀ {α : Type u_1} {M : Matroid α}, M✶.E = M.E
· 使用引理 `Matroid.delete_inter_ground_eq`：delete_inter_ground_eq (M : Matroid α) (
D : Set α) : M ＼ (D inter M.E) = M ＼ D
-/
@[simp] lemma contract_inter_ground_eq (M : Matroid α) (C : Set α) : M ／ (C ∩ M.E) = M ／ C := by
  rw [← dual_delete_dual, ← dual_ground, delete_inter_ground_eq, dual_delete_dual]

@[aesop unsafe 10% (rule_sets := [Matroid])]
/-
**Matroid.contract_ground_subset_ground** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：contract_ground_subset_ground (M : Matroid α) (C : Set α) : (M ／ C).E subs
eteq M.E
参数：M : Matroid α；C : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans_subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] {a b c : α
} [inst : LE α], a = b → b ⊆ c → a ⊆ c
· 使用定理 `Matroid.contract_ground`：∀ {α : Type u_1} (M : Matroid α) (C : Set α), (
M.contract C).E = M.E \ C
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
-/
lemma contract_ground_subset_ground (M : Matroid α) (C : Set α) : (M ／ C).E ⊆ M.E :=
  (M.contract_ground C).trans_subset sdiff_subset

/-! ### Independence and Coindependence -/

/-
**Matroid.coindep_contract_iff** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：coindep_contract_iff : (M ／ C).Coindep X ↔ M.Coindep X ∧ Disjoint X C
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.coindep_def`：coindep_def : M.Coindep X ↔ M✶.Indep X
· 使用引理 `Matroid.dual_contract`：dual_contract (M : Matroid α) (X : Set α) : (M ／ 
X)✶ = M✶ ＼ X
· 使用引理 `Matroid.delete_indep_iff`：delete_indep_iff : (M ＼ D).Indep I ↔ M.Indep I
 ∧ Disjoint I D
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
### Independence and Coindependence
-/
lemma coindep_contract_iff : (M ／ C).Coindep X ↔ M.Coindep X ∧ Disjoint X C := by
  rw [coindep_def, dual_contract, delete_indep_iff, ← coindep_def]
/-
**Matroid.Coindep.coindep_contract_of_disjoint** 是 Mathlib 中的一个定理，位于命名空间 `Matroi
d.Coindep`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {X C : Set α}, M.Coindep X → Disjoint X C
 → (M.contract C).Coindep X
参数：M.contract C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Matroid.coindep_contract_iff`：coindep_contract_iff : (M ／ C).Coindep X ↔
 M.Coindep X ∧ Disjoint X C
-/
lemma Coindep.coindep_contract_of_disjoint (hX : M.Coindep X) (hXC : Disjoint X C) :
    (M ／ C).Coindep X :=
  coindep_contract_iff.2 ⟨hX, hXC⟩
/-
**Matroid.contract_isCocircuit_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {K C : Set α}, (M.contract C).IsCocircuit
 K ↔ M.IsCocircuit K ∧ Disjoint K C
参数：M.contract C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matroid.isCocircuit_def`：isCocircuit_def : M.IsCocircuit K ↔ M✶.IsCircui
t K
· 使用引理 `Matroid.dual_contract`：dual_contract (M : Matroid α) (X : Set α) : (M ／ 
X)✶ = M✶ ＼ X
· 使用引理 `Matroid.delete_isCircuit_iff`：delete_isCircuit_iff {C : Set α} : (M ＼ D)
.IsCircuit C ↔ M.IsCircuit C ∧ Disjoint C D
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma contract_isCocircuit_iff :
    (M ／ C).IsCocircuit K ↔ M.IsCocircuit K ∧ Disjoint K C := by
  rw [isCocircuit_def, dual_contract, delete_isCircuit_iff]
/-
**Matroid.Indep.contract_isBase_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Indep`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I B : Set α}, M.Indep I → ((M.contract I
).IsBase B ↔ M.IsBase (B ∪ I) ∧ Disjoint B I)
参数：(M.contract I).IsBase B ↔ M.IsBase (B ∪ I) ∧ Disjoint B I。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Matroid.dual_delete_dual`：dual_delete_dual (M : Matroid α) (X : Set α) :
 (M✶ ＼ X)✶ = M ／ X
· 使用定理 `Matroid.dual_isBase_iff'`：dual_isBase_iff' : M✶.IsBase B ↔ M.IsBase (M.E
 \ B) ∧ B subseteq M.E
· 使用引理 `Matroid.delete_ground`：delete_ground (M : Matroid α) (D : Set α) : (M ＼ 
D).E = M.E \ D
· 使用定理 `Matroid.dual_ground`：∀ {α : Type u_1} {M : Matroid α}, M✶.E = M.E
· 使用引理 `Matroid.delete_isBase_iff`：delete_isBase_iff : (M ＼ D).IsBase B ↔ M.IsBa
sis B (M.E \ D)
· 使用引理 `Set.subset_sdiff`：subset_sdiff : s subseteq t \ u ↔ s subseteq t ∧ Disjo
int s u
· 使用定理 `and_assoc`：∀ {a b c : Prop}, (a ∧ b) ∧ c ↔ a ∧ b ∧ c
· 使用定理 `and_congr_left_iff`：∀ {a c b : Prop}, (a ∧ c ↔ b ∧ c) ↔ c → (a ↔ b)
· 使用定理 `Matroid.dual_dual`：∀ {α : Type u_1} (M : Matroid α), M✶✶ = M
· 使用定理 `Set.union_comm`：union_comm (a b : Set α) : a union b = b union a
· 使用定理 `Set.union_subset_iff`：union_subset_iff {s t u : Set α} : s union t subse
teq u ↔ s subseteq u ∧ t subseteq u
· 使用定理 `and_iff_right`：∀ {a b : Prop}, a → (a ∧ b ↔ b)
· 使用定理 `Matroid.Indep.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {I : Set α
}, M.Indep I → I ⊆ M.E
· 使用定理 `Matroid.isBase_restrict_iff`：∀ {α : Type u_1} {M : Matroid α} {I X : Set
 α},   autoParam (X ⊆ M.E) Matroid.isBase_restrict_iff._auto_1 → ((M.restrict X)
.IsBase I ↔ M.IsB…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.sdiff_sdiff`：sdiff_sdiff {u : Set α} : (s \ t) \ u = s \ (t union u)
· 使用定理 `Matroid.Spanning.isBase_restrict_iff`：∀ {α : Type u_2} {M : Matroid α} {
S B : Set α}, M.Spanning S → ((M.restrict S).IsBase B ↔ M.IsBase B ∧ B ⊆ S)
· 使用引理 `Matroid.coindep_iff_compl_spanning`：coindep_iff_compl_spanning (hI : I s
ubseteq M.E
· 使用定理 `Matroid.dual_coindep_iff`：∀ {α : Type u_1} {M : Matroid α} {X : Set α}, 
M✶.Coindep X ↔ M.Indep X
· 使用定理 `and_iff_left`：∀ {b a : Prop}, b → (a ∧ b ↔ a)
· 使用定理 `Set.sdiff_subset_sdiff_right`：sdiff_subset_sdiff_right {s t u : Set α} (
h : t subseteq u) : s \ u subseteq s \ t
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `sdiff_sdiff_right_self`：sdiff_sdiff_right_self : x \ (x \ y) = x ⊓ y
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma Indep.contract_isBase_iff (hI : M.Indep I) :
    (M ／ I).IsBase B ↔ M.IsBase (B ∪ I) ∧ Disjoint B I := by
  rw [← dual_delete_dual, dual_isBase_iff', delete_ground, dual_ground, delete_isBase_iff,
    subset_sdiff, ← and_assoc, and_congr_left_iff, ← dual_dual M, dual_isBase_iff', dual_dual,
    dual_dual, union_comm, dual_ground, union_subset_iff, and_iff_right hI.subset_ground,
    and_congr_left_iff, ← isBase_restrict_iff, sdiff_sdiff, Spanning.isBase_restrict_iff,
    and_iff_left (sdiff_subset_sdiff_right subset_union_left)]
  · simp
  rwa [← dual_ground, ← coindep_iff_compl_spanning, dual_coindep_iff]
/-
**Matroid.Indep.contract_indep_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Indep`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I J : Set α}, M.Indep I → ((M.contract I
).Indep J ↔ Disjoint J I ∧ M.Indep (J ∪ I))
参数：(M.contract I).Indep J ↔ Disjoint J I ∧ M.Indep (J ∪ I)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Matroid.Indep.contract_isBase_iff`：∀ {α : Type u_1} {M : Matroid α} {I B
 : Set α}, M.Indep I → ((M.contract I).IsBase B ↔ M.IsBase (B ∪ I) ∧ Disjoint B 
I)
· 使用引理 `Set.disjoint_of_subset_left`：disjoint_of_subset_left (h : s subseteq u) 
(d : Disjoint u t) : Disjoint s t
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
· 使用定理 `Set.subset_union_right`：subset_union_right {s t : Set α} : t subseteq s 
union t
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.sdiff_union_self`：sdiff_union_self {s t : Set α} : s \ t union t = s
 union t
· 使用定理 `Set.union_eq_self_of_subset_right`：union_eq_self_of_subset_right {s t : 
Set α} (h : t subseteq s) : s union t = s
· 使用引理 `Set.disjoint_sdiff_left`：disjoint_sdiff_left : Disjoint (t \ s) s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Set.subset_sdiff`：subset_sdiff : s subseteq t \ u ↔ s subseteq t ∧ Disjo
int s u
-/
lemma Indep.contract_indep_iff (hI : M.Indep I) :
    (M ／ I).Indep J ↔ Disjoint J I ∧ M.Indep (J ∪ I) := by
  simp_rw [indep_iff, hI.contract_isBase_iff, union_subset_iff]
  exact ⟨fun ⟨B, ⟨hBI, hdj⟩, hJB⟩ ↦ ⟨disjoint_of_subset_left hJB hdj, _, hBI,
    hJB.trans subset_union_left, subset_union_right⟩,
    fun ⟨hdj, B, hB, hJB, hIB⟩ ↦ ⟨B \ I,⟨by simpa [union_eq_self_of_subset_right hIB],
      disjoint_sdiff_left⟩, subset_sdiff.2 ⟨hJB, hdj⟩ ⟩⟩
/-
**Matroid.IsNonloop.contractElem_indep_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Is
Nonloop`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {e : α} {I : Set α},   M.IsNonloop e → ((
M.contract {e}).Indep I ↔ e ∉ I ∧ M.Indep (insert e I))
参数：(M.contract {e}).Indep I ↔ e ∉ I ∧ M.Indep (insert e I)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.Indep.contract_indep_iff`：∀ {α : Type u_1} {M : Matroid α} {I J 
: Set α}, M.Indep I → ((M.contract I).Indep J ↔ Disjoint J I ∧ M.Indep (J ∪ I))
· 使用定理 `Matroid.IsNonloop.indep`：∀ {α : Type u_1} {M : Matroid α} {e : α}, M.IsN
onloop e → M.Indep {e}
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.union_singleton`：union_singleton : s union {a} = insert a s
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma IsNonloop.contractElem_indep_iff (he : M.IsNonloop e) :
    (M ／ {e}).Indep I ↔ e ∉ I ∧ M.Indep (insert e I) := by
  simp [he.indep.contract_indep_iff]
/-
**Matroid.Indep.union_indep_iff_contract_indep** 是 Mathlib 中的一个定理，位于命名空间 `Matroi
d.Indep`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I J : Set α}, M.Indep I → (M.Indep (I ∪ 
J) ↔ (M.contract I).Indep (J \ I))
参数：M.Indep (I ∪ J) ↔ (M.contract I).Indep (J \ I)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.Indep.contract_indep_iff`：∀ {α : Type u_1} {M : Matroid α} {I J 
: Set α}, M.Indep I → ((M.contract I).Indep J ↔ Disjoint J I ∧ M.Indep (J ∪ I))
· 使用定理 `and_iff_right`：∀ {a b : Prop}, a → (a ∧ b ↔ b)
· 使用引理 `Set.disjoint_sdiff_left`：disjoint_sdiff_left : Disjoint (t \ s) s
· 使用定理 `Set.sdiff_union_self`：sdiff_union_self {s t : Set α} : s \ t union t = s
 union t
· 使用定理 `Set.union_comm`：union_comm (a b : Set α) : a union b = b union a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma Indep.union_indep_iff_contract_indep (hI : M.Indep I) :
    M.Indep (I ∪ J) ↔ (M ／ I).Indep (J \ I) := by
  rw [hI.contract_indep_iff, and_iff_right disjoint_sdiff_left, sdiff_union_self, union_comm]
/-
**Matroid.Indep.diff_indep_contract_of_subset** 是 Mathlib 中的一个定理，位于命名空间 `Matroid
.Indep`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I J : Set α}, M.Indep J → I ⊆ J → (M.con
tract I).Indep (J \ I)
参数：M.contract I；J \ I。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.Indep.union_indep_iff_contract_indep`：∀ {α : Type u_1} {M : Matr
oid α} {I J : Set α}, M.Indep I → (M.Indep (I ∪ J) ↔ (M.contract I).Indep (J \ I
))
· 使用定理 `Matroid.Indep.subset`：∀ {α : Type u_1} {M : Matroid α} {I J : Set α}, M.
Indep J → I ⊆ J → M.Indep I
· 使用定理 `Set.union_eq_self_of_subset_left`：union_eq_self_of_subset_left {s t : Se
t α} (h : s subseteq t) : s union t = t
-/
lemma Indep.diff_indep_contract_of_subset (hJ : M.Indep J) (hIJ : I ⊆ J) :
    (M ／ I).Indep (J \ I) := by
  rwa [← (hJ.subset hIJ).union_indep_iff_contract_indep, union_eq_self_of_subset_left hIJ]
/-
**Matroid.Indep.contract_dep_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Indep`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I J : Set α}, M.Indep I → ((M.contract I
).Dep J ↔ Disjoint J I ∧ M.Dep (J ∪ I))
参数：(M.contract I).Dep J ↔ Disjoint J I ∧ M.Dep (J ∪ I)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.dep_iff`：dep_iff : M.Dep D ↔ ¬M.Indep D ∧ D subseteq M.E
· 使用定理 `Matroid.Indep.contract_indep_iff`：∀ {α : Type u_1} {M : Matroid α} {I J 
: Set α}, M.Indep I → ((M.contract I).Indep J ↔ Disjoint J I ∧ M.Indep (J ∪ I))
· 使用定理 `Matroid.contract_ground`：∀ {α : Type u_1} (M : Matroid α) (C : Set α), (
M.contract C).E = M.E \ C
· 使用引理 `Set.subset_sdiff`：subset_sdiff : s subseteq t \ u ↔ s subseteq t ∧ Disjo
int s u
· 使用定理 `disjoint_comm`：disjoint_comm : Disjoint a b ↔ Disjoint b a
· 使用定理 `Set.union_subset_iff`：union_subset_iff {s t u : Set α} : s union t subse
teq u ↔ s subseteq u ∧ t subseteq u
· 使用定理 `and_iff_left`：∀ {b a : Prop}, b → (a ∧ b ↔ a)
· 使用定理 `Matroid.Indep.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {I : Set α
}, M.Indep I → I ⊆ M.E
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Decidable.not_and_iff_not_or_not'`：∀ {b a : Prop} [Decidable b], ¬(a ∧ b
) ↔ ¬a ∨ ¬b
-/
lemma Indep.contract_dep_iff (hI : M.Indep I) :
    (M ／ I).Dep J ↔ Disjoint J I ∧ M.Dep (J ∪ I) := by
  rw [dep_iff, hI.contract_indep_iff, dep_iff, contract_ground, subset_sdiff, disjoint_comm,
    union_subset_iff, and_iff_left hI.subset_ground]
  tauto

/-! ### Bases -/

/-- Contracting a set is the same as contracting a basis for the set, and deleting the rest. -/
/-
**Matroid.IsBasis.contract_eq_contract_delete** 是 Mathlib 中的一个定理，位于命名空间 `Matroid
.IsBasis`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, M.IsBasis I X → M.contract
 X = (M.contract I).delete (X \ I)
参数：M.contract I；X \ I。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.sdiff_union_of_subset`：sdiff_union_of_subset {s t : Set α} (h : t su
bseteq s) : s \ t union t = s
· 使用定理 `Matroid.IsBasis.subset`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, 
M.IsBasis I X → I ⊆ X
· 使用定理 `Matroid.dual_inj`：∀ {α : Type u_1} {M₁ M₂ : Matroid α}, M₁✶ = M₂✶ ↔ M₁ =
 M₂
· 使用引理 `Matroid.dual_contract_delete`：dual_contract_delete (M : Matroid α) (X Y 
: Set α) : (M ／ X ＼ Y)✶ = M✶ ＼ X ／ Y
· 使用引理 `Matroid.dual_contract`：dual_contract (M : Matroid α) (X : Set α) : (M ／ 
X)✶ = M✶ ＼ X
· 使用定理 `Set.union_comm`：union_comm (a b : Set α) : a union b = b union a
· 使用引理 `Matroid.delete_delete`：delete_delete (M : Matroid α) (D₁ D₂ : Set α) : M
 ＼ D₁ ＼ D₂ = M ＼ (D₁ union D₂)
· 使用定理 `Matroid.ext_iff_indep`：ext_iff_indep {M₁ M₂ : Matroid α} : M₁ = M₂ ↔ (M₁
.E = M₂.E) ∧ forall ⦃I⦄, I subseteq M₁.E -> (M₁.Indep I ↔ M₂.Indep I)
· 使用引理 `Matroid.dual_coloops`：dual_coloops : M✶.coloops = M.loops
· 使用定理 `Matroid.IsLoop.eq_1`：∀ {α : Type u_1} (M : Matroid α) (e : α), M.IsLoop 
e = (e ∈ M.loops)
· 使用引理 `Matroid.singleton_dep`：singleton_dep : M.Dep {e} ↔ M.IsLoop e
· 使用定理 `Matroid.Indep.contract_dep_iff`：∀ {α : Type u_1} {M : Matroid α} {I J : 
Set α}, M.Indep I → ((M.contract I).Dep J ↔ Disjoint J I ∧ M.Dep (J ∪ I))
· 使用定理 `Matroid.IsBasis.indep`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, M
.IsBasis I X → M.Indep I
· 使用定理 `Set.singleton_union`：singleton_union : {a} union s = insert a s
· 使用定理 `and_iff_right`：∀ {a b : Prop}, a → (a ∧ b ↔ b)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Matroid.Indep.insert_dep_iff`：∀ {α : Type u_2} {M : Matroid α} {e : α} {
I : Set α}, M.Indep I → (M.Dep (insert e I) ↔ e ∈ M.closure I \ I)
· 使用定理 `Matroid.IsBasis.closure_eq_closure`：∀ {α : Type u_2} {M : Matroid α} {X 
I : Set α}, M.IsBasis I X → M.closure I = M.closure X
· 使用定理 `Set.sdiff_subset_sdiff_left`：sdiff_subset_sdiff_left {s₁ s₂ t : Set α} (
h : s₁ subseteq s₂) : s₁ \ t subseteq s₂ \ t
· 使用引理 `Matroid.subset_closure`：subset_closure (M : Matroid α) (X : Set α) (hX :
 X subseteq M.E
· 使用定理 `Matroid.IsBasis.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {I X : S
et α}, M.IsBasis I X → X ⊆ M.E
· 使用定理 `Matroid.Indep.contract_indep_iff`：∀ {α : Type u_1} {M : Matroid α} {I J 
: Set α}, M.Indep I → ((M.contract I).Indep J ↔ Disjoint J I ∧ M.Indep (J ∪ I))
· 使用定理 `Matroid.Indep.subset`：∀ {α : Type u_1} {M : Matroid α} {I J : Set α}, M.
Indep J → I ⊆ J → M.Indep I
· 使用引理 `Matroid.coloops_indep`：coloops_indep (M : Matroid α) : M.Indep M.coloops
· 使用引理 `Matroid.delete_indep_iff`：delete_indep_iff : (M ＼ D).Indep I ↔ M.Indep I
 ∧ Disjoint I D
· 使用引理 `Matroid.union_indep_iff_indep_of_subset_coloops`：union_indep_iff_indep_o
f_subset_coloops (hK : K subseteq M.coloops) : M.Indep (I union K) ↔ M.Indep I
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Contracting a set is the same as contracting a basis for the set, and deleting t
he rest.
-/
lemma IsBasis.contract_eq_contract_delete (hI : M.IsBasis I X) : M ／ X = M ／ I ＼ (X \ I) := by
  nth_rw 1 [← sdiff_union_of_subset hI.subset, ← dual_inj, dual_contract_delete, dual_contract,
    union_comm, ← delete_delete, ext_iff_indep]
  refine ⟨rfl, fun J hJ ↦ ?_⟩
  have hss : X \ I ⊆ (M✶ ＼ I).coloops := fun e he ↦ by
    rw [← dual_contract, dual_coloops, ← IsLoop, ← singleton_dep, hI.indep.contract_dep_iff,
      singleton_union, and_iff_right (by simpa using he.2), hI.indep.insert_dep_iff,
      hI.closure_eq_closure]
    exact sdiff_subset_sdiff_left (M.subset_closure X) he
  rw [((coloops_indep _).subset hss).contract_indep_iff, delete_indep_iff,
    union_indep_iff_indep_of_subset_coloops hss, and_comm]
/-
**Matroid.Indep.union_isBasis_union_of_contract_isBasis** 是 Mathlib 中的一个定理，位于命名空
间 `Matroid.Indep`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I J X : Set α}, M.Indep I → (M.contract 
I).IsBasis J X → M.IsBasis (J ∪ I) (X ∪ I)
参数：M.contract I；J ∪ I；X ∪ I。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.Indep.isBasis_of_maximal_subset`：∀ {α : Type u_1} {M : Matroid α
} {I X : Set α},   M.Indep I →     I ⊆ X →       (∀ ⦃J : Set α⦄, M.Indep J → I ⊆
 J → J ⊆ X → J ⊆ I) →        …
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Matroid.Indep.contract_indep_iff`：∀ {α : Type u_1} {M : Matroid α} {I J 
: Set α}, M.Indep I → ((M.contract I).Indep J ↔ Disjoint J I ∧ M.Indep (J ∪ I))
· 使用定理 `Set.union_subset_union_left`：union_subset_union_left {s₁ s₂ : Set α} (t)
 (h : s₁ subseteq s₂) : s₁ union t subseteq s₂ union t
· 使用引理 `Set.disjoint_sdiff_left`：disjoint_sdiff_left : Disjoint (t \ s) s
· 使用定理 `Set.sdiff_union_of_subset`：sdiff_union_of_subset {s t : Set α} (h : t su
bseteq s) : s \ t union t = s
· 使用定理 `Set.union_subset_iff`：union_subset_iff {s t u : Set α} : s union t subse
teq u ↔ s subseteq u ∧ t subseteq u
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.sdiff_subset_iff`：sdiff_subset_iff {s t u : Set α} : s \ t subseteq 
u ↔ s subseteq t union u
· 使用定理 `Set.union_comm`：union_comm (a b : Set α) : a union b = b union a
· 使用引理 `Set.subset_sdiff`：subset_sdiff : s subseteq t \ u ↔ s subseteq t ∧ Disjo
int s u
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Matroid.Indep.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {I : Set α
}, M.Indep I → I ⊆ M.E
-/
lemma Indep.union_isBasis_union_of_contract_isBasis (hI : M.Indep I) (hB : (M ／ I).IsBasis J X) :
    M.IsBasis (J ∪ I) (X ∪ I) := by
  simp_rw [IsBasis, hI.contract_indep_iff, contract_ground, subset_sdiff,
    maximal_subset_iff, and_imp] at hB
  refine hB.1.1.1.2.isBasis_of_maximal_subset (union_subset_union_left _ hB.1.1.2)
    fun K hK hKJ hKX ↦ ?_
  rw [union_subset_iff] at hKJ
  rw [hB.1.2 (t := K \ I) disjoint_sdiff_left (by simpa [sdiff_union_of_subset hKJ.2])
    (sdiff_subset_iff.2 (by rwa [union_comm])) (subset_sdiff.2 ⟨hKJ.1, hB.1.1.1.1⟩),
    sdiff_union_of_subset hKJ.2]
/-
**Matroid.IsBasis'.contract_isBasis'_sdiff_sdiff_of_subset** 是 Mathlib 中的一个定理，位于
命名空间 `Matroid.IsBasis'`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I J X : Set α}, M.IsBasis' I X → J ⊆ I →
 (M.contract J).IsBasis' (I \ J) (X \ J)
参数：M.contract J；I \ J；X \ J。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.IsBasis'.eq_of_subset_indep`：∀ {α : Type u_1} {M : Matroid α} {I
 J X : Set α}, M.IsBasis' I X → M.Indep J → I ⊆ J → J ⊆ X → I = J
· 使用定理 `Set.union_subset`：union_subset {s t r : Set α} (sr : s subseteq r) (tr :
 t subseteq r) : s union t subseteq r
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Matroid.IsBasis'.subset`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α},
 M.IsBasis' I X → I ⊆ X
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Matroid.Indep.contract_indep_iff`：∀ {α : Type u_1} {M : Matroid α} {I J 
: Set α}, M.Indep I → ((M.contract I).Indep J ↔ Disjoint J I ∧ M.Indep (J ∪ I))
· 使用定理 `Matroid.Indep.subset`：∀ {α : Type u_1} {M : Matroid α} {I J : Set α}, M.
Indep J → I ⊆ J → M.Indep I
· 使用定理 `Matroid.IsBasis'.indep`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, 
M.IsBasis' I X → M.Indep I
· 使用定理 `Set.sdiff_union_self`：sdiff_union_self {s t : Set α} : s \ t union t = s
 union t
· 使用定理 `Set.union_eq_self_of_subset_right`：union_eq_self_of_subset_right {s t : 
Set α} (h : t subseteq s) : s union t = s
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `Set.union_comm`：union_comm (a b : Set α) : a union b = b union a
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
lemma IsBasis'.contract_isBasis'_sdiff_sdiff_of_subset (hIX : M.IsBasis' I X) (hJI : J ⊆ I) :
    (M ／ J).IsBasis' (I \ J) (X \ J) := by
  suffices ∀ ⦃K⦄, Disjoint K J → M.Indep (K ∪ J) → K ⊆ X → I ⊆ K ∪ J → K ⊆ I by
    simpa +contextual [IsBasis', (hIX.indep.subset hJI).contract_indep_iff,
      subset_sdiff, maximal_subset_iff, disjoint_sdiff_left,
      union_eq_self_of_subset_right hJI, hIX.indep, sdiff_subset.trans hIX.subset,
      sdiff_subset_iff, subset_antisymm_iff, union_comm J]
  exact fun K hJK hKJi hKX hIJK ↦ by
    simp [hIX.eq_of_subset_indep hKJi hIJK (union_subset hKX (hJI.trans hIX.subset))]

@[deprecated (since := "2026-06-03")]
alias IsBasis'.contract_isBasis'_diff_diff_of_subset :=
  IsBasis'.contract_isBasis'_sdiff_sdiff_of_subset
/-
**Matroid.IsBasis'.contract_isBasis'_sdiff_of_subset** 是 Mathlib 中的一个定理，位于命名空间 `
Matroid.IsBasis'`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I J X : Set α}, M.IsBasis' I X → J ⊆ I →
 (M.contract J).IsBasis' (I \ J) X
参数：M.contract J；I \ J。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Set.inter_sdiff_assoc`：inter_sdiff_assoc (a b c : Set α) : (a inter b) \
 c = a inter (b \ c)
· 使用定理 `Matroid.IsBasis'.isBasis_inter_ground`：∀ {α : Type u_1} {M : Matroid α} 
{I X : Set α}, M.IsBasis' I X → M.IsBasis I (X ∩ M.E)
· 使用定理 `Matroid.IsBasis'.contract_isBasis'_sdiff_sdiff_of_subset`：∀ {α : Type u_
1} {M : Matroid α} {I J X : Set α}, M.IsBasis' I X → J ⊆ I → (M.contract J).IsBa
sis' (I \ J) (X \ J)
-/
lemma IsBasis'.contract_isBasis'_sdiff_of_subset (hIX : M.IsBasis' I X) (hJI : J ⊆ I) :
    (M ／ J).IsBasis' (I \ J) X := by
  simpa [isBasis'_iff_isBasis_inter_ground, inter_sdiff_assoc, ← sdiff_inter_distrib_right] using
    (hIX.contract_isBasis'_sdiff_sdiff_of_subset hJI).isBasis_inter_ground

@[deprecated (since := "2026-06-03")]
alias IsBasis'.contract_isBasis'_diff_of_subset := IsBasis'.contract_isBasis'_sdiff_of_subset
/-
**Matroid.IsBasis.contract_isBasis_sdiff_sdiff_of_subset** 是 Mathlib 中的一个定理，位于命名
空间 `Matroid.IsBasis`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I J X : Set α}, M.IsBasis I X → J ⊆ I → 
(M.contract J).IsBasis (I \ J) (X \ J)
参数：M.contract J；I \ J；X \ J。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsBasis'.isBasis_inter_ground`：∀ {α : Type u_1} {M : Matroid α} 
{I X : Set α}, M.IsBasis' I X → M.IsBasis I (X ∩ M.E)
· 使用定理 `Matroid.IsBasis'.contract_isBasis'_sdiff_of_subset`：∀ {α : Type u_1} {M 
: Matroid α} {I J X : Set α}, M.IsBasis' I X → J ⊆ I → (M.contract J).IsBasis' (
I \ J) X
· 使用定理 `Matroid.IsBasis.isBasis'`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}
, M.IsBasis I X → M.IsBasis' I X
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.inter_eq_self_of_subset_left`：inter_eq_self_of_subset_left {s t : Se
t α} : s subseteq t -> s inter t = s
· 使用定理 `Matroid.IsBasis.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {I X : S
et α}, M.IsBasis I X → X ⊆ M.E
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Set.inter_sdiff_assoc`：inter_sdiff_assoc (a b c : Set α) : (a inter b) \
 c = a inter (b \ c)
· 使用定理 `Matroid.contract_ground`：∀ {α : Type u_1} (M : Matroid α) (C : Set α), (
M.contract C).E = M.E \ C
-/
lemma IsBasis.contract_isBasis_sdiff_sdiff_of_subset (hIX : M.IsBasis I X) (hJI : J ⊆ I) :
    (M ／ J).IsBasis (I \ J) (X \ J) := by
  have h := (hIX.isBasis'.contract_isBasis'_sdiff_of_subset hJI).isBasis_inter_ground
  rwa [contract_ground, ← inter_sdiff_assoc, inter_eq_self_of_subset_left hIX.subset_ground] at h

@[deprecated (since := "2026-06-03")]
alias IsBasis.contract_isBasis_diff_diff_of_subset := IsBasis.contract_isBasis_sdiff_sdiff_of_subset
/-
**Matroid.IsBasis.contract_sdiff_isBasis_sdiff** 是 Mathlib 中的一个定理，位于命名空间 `Matroi
d.IsBasis`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I J X Y : Set α},   M.IsBasis I X → M.Is
Basis J Y → I ⊆ J → (M.contract I).IsBasis (J \ I) (Y \ X)
参数：M.contract I；J \ I；Y \ X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsBasis.isBasis_subset`：∀ {α : Type u_1} {M : Matroid α} {I X Y 
: Set α}, M.IsBasis I X → I ⊆ Y → Y ⊆ X → M.IsBasis I Y
· 使用定理 `Matroid.IsBasis.contract_isBasis_sdiff_sdiff_of_subset`：∀ {α : Type u_1}
 {M : Matroid α} {I J X : Set α}, M.IsBasis I X → J ⊆ I → (M.contract J).IsBasis
 (I \ J) (X \ J)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.subset_sdiff`：subset_sdiff : s subseteq t \ u ↔ s subseteq t ∧ Disjo
int s u
· 使用定理 `and_iff_right`：∀ {a b : Prop}, a → (a ∧ b ↔ b)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
· 使用定理 `Matroid.IsBasis.subset`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, 
M.IsBasis I X → I ⊆ X
· 使用定理 `Matroid.IsBasis.eq_of_subset_indep`：∀ {α : Type u_1} {M : Matroid α} {I 
J X : Set α}, M.IsBasis I X → M.Indep J → I ⊆ J → J ⊆ X → I = J
· 使用定理 `Matroid.Indep.inter_right`：∀ {α : Type u_1} {M : Matroid α} {I : Set α},
 M.Indep I → ∀ (X : Set α), M.Indep (I ∩ X)
· 使用定理 `Matroid.IsBasis.indep`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, M
.IsBasis I X → M.Indep I
· 使用定理 `Set.subset_inter`：subset_inter {s t r : Set α} (rs : r subseteq s) (rt :
 r subseteq t) : r subseteq s inter t
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `Set.sdiff_self_inter`：sdiff_self_inter {s t : Set α} : s \ (s inter t) =
 s \ t
· 使用引理 `Set.disjoint_sdiff_left`：disjoint_sdiff_left : Disjoint (t \ s) s
· 使用定理 `Set.sdiff_subset_sdiff_right`：sdiff_subset_sdiff_right {s t u : Set α} (
h : t subseteq u) : s \ u subseteq s \ t
-/
lemma IsBasis.contract_sdiff_isBasis_sdiff (hIX : M.IsBasis I X) (hJY : M.IsBasis J Y)
    (hIJ : I ⊆ J) : (M ／ I).IsBasis (J \ I) (Y \ X) := by
  refine (hJY.contract_isBasis_sdiff_sdiff_of_subset hIJ).isBasis_subset ?_ ?_
  · rw [subset_sdiff, and_iff_right (sdiff_subset.trans hJY.subset),
      hIX.eq_of_subset_indep (hJY.indep.inter_right X) (subset_inter hIJ hIX.subset)
      inter_subset_right, sdiff_self_inter]
    exact disjoint_sdiff_left
  refine sdiff_subset_sdiff_right hIX.subset

@[deprecated (since := "2026-06-03")]
alias IsBasis.contract_diff_isBasis_diff := IsBasis.contract_sdiff_isBasis_sdiff
/-
**Matroid.IsBasis'.contract_isBasis_union_union** 是 Mathlib 中的一个定理，位于命名空间 `Matro
id.IsBasis'`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I J X : Set α},   M.IsBasis' (J ∪ I) (X 
∪ I) → Disjoint J I → Disjoint X I → (M.contract I).IsBasis' J X
参数：J ∪ I；X ∪ I；M.contract I。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.union_sdiff_right`：union_sdiff_right {s t : Set α} : (s union t) \ t
 = s \ t
· 使用定理 `Disjoint.sdiff_eq_left`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlg
ebra α] {a b : α}, Disjoint a b → a \ b = a
· 使用定理 `Matroid.IsBasis'.contract_isBasis'_sdiff_sdiff_of_subset`：∀ {α : Type u_
1} {M : Matroid α} {I J X : Set α}, M.IsBasis' I X → J ⊆ I → (M.contract J).IsBa
sis' (I \ J) (X \ J)
· 使用定理 `Set.subset_union_right`：subset_union_right {s t : Set α} : t subseteq s 
union t
-/
lemma IsBasis'.contract_isBasis_union_union (h : M.IsBasis' (J ∪ I) (X ∪ I))
    (hJI : Disjoint J I) (hXI : Disjoint X I) : (M ／ I).IsBasis' J X := by
  simpa [hJI.sdiff_eq_left, hXI.sdiff_eq_left] using
    h.contract_isBasis'_sdiff_sdiff_of_subset subset_union_right
/-
**Matroid.IsBasis.contract_isBasis_union_union** 是 Mathlib 中的一个定理，位于命名空间 `Matroi
d.IsBasis`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I J X : Set α},   M.IsBasis (J ∪ I) (X ∪
 I) → Disjoint J I → Disjoint X I → (M.contract I).IsBasis J X
参数：J ∪ I；X ∪ I；M.contract I。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Matroid.isBasis'_iff_isBasis`：∀ {α : Type u_1} {M : Matroid α} {I X : Se
t α},   autoParam (X ⊆ M.E) Matroid.isBasis'_iff_isBasis._auto_1 → (M.IsBasis' I
 X ↔ M.IsBasis I X…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.contract_ground`：∀ {α : Type u_1} (M : Matroid α) (C : Set α), (
M.contract C).E = M.E \ C
· 使用引理 `Set.subset_sdiff`：subset_sdiff : s subseteq t \ u ↔ s subseteq t ∧ Disjo
int s u
· 使用定理 `and_iff_left`：∀ {b a : Prop}, b → (a ∧ b ↔ a)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
· 使用定理 `Matroid.IsBasis.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {I X : S
et α}, M.IsBasis I X → X ⊆ M.E
· 使用定理 `Matroid.IsBasis'.contract_isBasis_union_union`：∀ {α : Type u_1} {M : Mat
roid α} {I J X : Set α},   M.IsBasis' (J ∪ I) (X ∪ I) → Disjoint J I → Disjoint 
X I → (M.contract I).IsBasis' J X
· 使用定理 `Matroid.IsBasis.isBasis'`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}
, M.IsBasis I X → M.IsBasis' I X
-/
lemma IsBasis.contract_isBasis_union_union (h : M.IsBasis (J ∪ I) (X ∪ I))
    (hJI : Disjoint J I) (hXI : Disjoint X I) : (M ／ I).IsBasis J X := by
  refine (isBasis'_iff_isBasis ?_).1 <| h.isBasis'.contract_isBasis_union_union hJI hXI
  rw [contract_ground, subset_sdiff, and_iff_left hXI]
  exact subset_union_left.trans h.subset_ground
/-
**Matroid.IsBasis'.contract_eq_contract_delete** 是 Mathlib 中的一个定理，位于命名空间 `Matroi
d.IsBasis'`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, M.IsBasis' I X → M.contrac
t X = (M.contract I).delete (X \ I)
参数：M.contract I；X \ I。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.contract_inter_ground_eq`：∀ {α : Type u_1} (M : Matroid α) (C : 
Set α), M.contract (C ∩ M.E) = M.contract C
· 使用定理 `Matroid.IsBasis.contract_eq_contract_delete`：∀ {α : Type u_1} {M : Matro
id α} {I X : Set α}, M.IsBasis I X → M.contract X = (M.contract I).delete (X \ I
)
· 使用定理 `Matroid.IsBasis'.isBasis_inter_ground`：∀ {α : Type u_1} {M : Matroid α} 
{I X : Set α}, M.IsBasis' I X → M.IsBasis I (X ∩ M.E)
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用引理 `Matroid.delete_inter_ground_eq`：delete_inter_ground_eq (M : Matroid α) (
D : Set α) : M ＼ (D inter M.E) = M ＼ D
· 使用定理 `Matroid.contract_ground`：∀ {α : Type u_1} (M : Matroid α) (C : Set α), (
M.contract C).E = M.E \ C
· 使用定理 `Set.sdiff_eq`：sdiff_eq (s t : Set α) : s \ t = s inter tᶜ
· 使用定理 `Set.inter_inter_distrib_right`：inter_inter_distrib_right (s t u : Set α)
 : s inter t inter u = s inter u inter (t inter u)
-/
lemma IsBasis'.contract_eq_contract_delete (hI : M.IsBasis' I X) : M ／ X = M ／ I ＼ (X \ I) := by
  rw [← contract_inter_ground_eq, hI.isBasis_inter_ground.contract_eq_contract_delete, eq_comm,
    ← delete_inter_ground_eq, contract_ground, sdiff_eq, sdiff_eq, ← inter_inter_distrib_right,
    ← sdiff_eq]
/-
**Matroid.IsBasis'.contract_indep_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBasis
'`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I J X : Set α},   M.IsBasis' I X → ((M.c
ontract X).Indep J ↔ M.Indep (J ∪ I) ∧ Disjoint X J)
参数：(M.contract X).Indep J ↔ M.Indep (J ∪ I) ∧ Disjoint X J。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.IsBasis'.contract_eq_contract_delete`：∀ {α : Type u_1} {M : Matr
oid α} {I X : Set α}, M.IsBasis' I X → M.contract X = (M.contract I).delete (X \
 I)
· 使用引理 `Matroid.delete_indep_iff`：delete_indep_iff : (M ＼ D).Indep I ↔ M.Indep I
 ∧ Disjoint I D
· 使用定理 `Matroid.Indep.contract_indep_iff`：∀ {α : Type u_1} {M : Matroid α} {I J 
: Set α}, M.Indep I → ((M.contract I).Indep J ↔ Disjoint J I ∧ M.Indep (J ∪ I))
· 使用定理 `Matroid.IsBasis'.indep`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, 
M.IsBasis' I X → M.Indep I
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `and_assoc`：∀ {a b c : Prop}, (a ∧ b) ∧ c ↔ a ∧ b ∧ c
· 使用引理 `Set.disjoint_union_right`：disjoint_union_right : Disjoint s (t union u) 
↔ Disjoint s t ∧ Disjoint s u
· 使用定理 `Set.sdiff_union_self`：sdiff_union_self {s t : Set α} : s \ t union t = s
 union t
· 使用定理 `Set.union_eq_self_of_subset_right`：union_eq_self_of_subset_right {s t : 
Set α} (h : t subseteq s) : s union t = s
· 使用定理 `Matroid.IsBasis'.subset`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α},
 M.IsBasis' I X → I ⊆ X
· 使用定理 `disjoint_comm`：disjoint_comm : Disjoint a b ↔ Disjoint b a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma IsBasis'.contract_indep_iff (hI : M.IsBasis' I X) :
    (M ／ X).Indep J ↔ M.Indep (J ∪ I) ∧ Disjoint X J := by
  rw [hI.contract_eq_contract_delete, delete_indep_iff, hI.indep.contract_indep_iff,
    and_comm, ← and_assoc, ← disjoint_union_right, sdiff_union_self,
    union_eq_self_of_subset_right hI.subset, and_comm, disjoint_comm]
/-
**Matroid.IsBasis.contract_indep_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBasis`
。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I J X : Set α},   M.IsBasis I X → ((M.co
ntract X).Indep J ↔ M.Indep (J ∪ I) ∧ Disjoint X J)
参数：(M.contract X).Indep J ↔ M.Indep (J ∪ I) ∧ Disjoint X J。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsBasis'.contract_indep_iff`：∀ {α : Type u_1} {M : Matroid α} {I
 J X : Set α},   M.IsBasis' I X → ((M.contract X).Indep J ↔ M.Indep (J ∪ I) ∧ Di
sjoint X J)
· 使用定理 `Matroid.IsBasis.isBasis'`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}
, M.IsBasis I X → M.IsBasis' I X
-/
lemma IsBasis.contract_indep_iff (hI : M.IsBasis I X) :
    (M ／ X).Indep J ↔ M.Indep (J ∪ I) ∧ Disjoint X J :=
  hI.isBasis'.contract_indep_iff
/-
**Matroid.IsBasis'.contract_dep_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBasis'`
。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I X : Set α},   M.IsBasis' I X → ∀ {D : 
Set α}, (M.contract X).Dep D ↔ M.Dep (D ∪ I) ∧ Disjoint X D
参数：M.contract X；D ∪ I。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.IsBasis'.contract_eq_contract_delete`：∀ {α : Type u_1} {M : Matr
oid α} {I X : Set α}, M.IsBasis' I X → M.contract X = (M.contract I).delete (X \
 I)
· 使用引理 `Matroid.delete_dep_iff`：delete_dep_iff : (M ＼ D).Dep X ↔ M.Dep X ∧ Disjo
int X D
· 使用定理 `Matroid.Indep.contract_dep_iff`：∀ {α : Type u_1} {M : Matroid α} {I J : 
Set α}, M.Indep I → ((M.contract I).Dep J ↔ Disjoint J I ∧ M.Dep (J ∪ I))
· 使用定理 `Matroid.IsBasis'.indep`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, 
M.IsBasis' I X → M.Indep I
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `and_assoc`：∀ {a b c : Prop}, (a ∧ b) ∧ c ↔ a ∧ b ∧ c
· 使用引理 `Set.disjoint_union_right`：disjoint_union_right : Disjoint s (t union u) 
↔ Disjoint s t ∧ Disjoint s u
· 使用定理 `Set.sdiff_union_of_subset`：sdiff_union_of_subset {s t : Set α} (h : t su
bseteq s) : s \ t union t = s
· 使用定理 `Matroid.IsBasis'.subset`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α},
 M.IsBasis' I X → I ⊆ X
· 使用定理 `disjoint_comm`：disjoint_comm : Disjoint a b ↔ Disjoint b a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma IsBasis'.contract_dep_iff (hI : M.IsBasis' I X) {D : Set α} :
    (M ／ X).Dep D ↔ M.Dep (D ∪ I) ∧ Disjoint X D := by
  rw [hI.contract_eq_contract_delete, delete_dep_iff, hI.indep.contract_dep_iff, and_comm,
    ← and_assoc, ← disjoint_union_right, sdiff_union_of_subset hI.subset, disjoint_comm, and_comm]
/-
**Matroid.IsBasis.contract_dep_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBasis`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I X : Set α},   M.IsBasis I X → ∀ {D : S
et α}, (M.contract X).Dep D ↔ M.Dep (D ∪ I) ∧ Disjoint X D
参数：M.contract X；D ∪ I。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsBasis'.contract_dep_iff`：∀ {α : Type u_1} {M : Matroid α} {I X
 : Set α},   M.IsBasis' I X → ∀ {D : Set α}, (M.contract X).Dep D ↔ M.Dep (D ∪ I
) ∧ Disjoint X D
· 使用定理 `Matroid.IsBasis.isBasis'`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}
, M.IsBasis I X → M.IsBasis' I X
-/
lemma IsBasis.contract_dep_iff (hI : M.IsBasis I X) {D : Set α} :
    (M ／ X).Dep D ↔ M.Dep (D ∪ I) ∧ Disjoint X D :=
  hI.isBasis'.contract_dep_iff
/-
**Matroid.IsBasis.contract_indep_iff_of_disjoint** 是 Mathlib 中的一个定理，位于命名空间 `Matr
oid.IsBasis`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I J X : Set α},   M.IsBasis I X → Disjoi
nt X J → ((M.contract X).Indep J ↔ M.Indep (J ∪ I))
参数：(M.contract X).Indep J ↔ M.Indep (J ∪ I)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.IsBasis.contract_indep_iff`：∀ {α : Type u_1} {M : Matroid α} {I 
J X : Set α},   M.IsBasis I X → ((M.contract X).Indep J ↔ M.Indep (J ∪ I) ∧ Disj
oint X J)
· 使用定理 `and_iff_left`：∀ {b a : Prop}, b → (a ∧ b ↔ a)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma IsBasis.contract_indep_iff_of_disjoint (hI : M.IsBasis I X) (hdj : Disjoint X J) :
    (M ／ X).Indep J ↔ M.Indep (J ∪ I) := by
  rw [hI.contract_indep_iff, and_iff_left hdj]
/-
**Matroid.IsBasis.contract_indep_sdiff_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Is
Basis`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I J X : Set α}, M.IsBasis I X → ((M.cont
ract X).Indep (J \ X) ↔ M.Indep (J \ X ∪ I))
参数：(M.contract X).Indep (J \ X) ↔ M.Indep (J \ X ∪ I)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.IsBasis.contract_indep_iff`：∀ {α : Type u_1} {M : Matroid α} {I 
J X : Set α},   M.IsBasis I X → ((M.contract X).Indep J ↔ M.Indep (J ∪ I) ∧ Disj
oint X J)
· 使用定理 `and_iff_left`：∀ {b a : Prop}, b → (a ∧ b ↔ a)
· 使用引理 `Set.disjoint_sdiff_right`：disjoint_sdiff_right : Disjoint s (t \ s)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma IsBasis.contract_indep_sdiff_iff (hI : M.IsBasis I X) :
    (M ／ X).Indep (J \ X) ↔ M.Indep ((J \ X) ∪ I) := by
  rw [hI.contract_indep_iff, and_iff_left disjoint_sdiff_right]

@[deprecated (since := "2026-06-03")]
alias IsBasis.contract_indep_diff_iff := IsBasis.contract_indep_sdiff_iff
/-
**Matroid.IsBasis'.contract_indep_sdiff_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.I
sBasis'`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I J X : Set α}, M.IsBasis' I X → ((M.con
tract X).Indep (J \ X) ↔ M.Indep (J \ X ∪ I))
参数：(M.contract X).Indep (J \ X) ↔ M.Indep (J \ X ∪ I)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.IsBasis'.contract_indep_iff`：∀ {α : Type u_1} {M : Matroid α} {I
 J X : Set α},   M.IsBasis' I X → ((M.contract X).Indep J ↔ M.Indep (J ∪ I) ∧ Di
sjoint X J)
· 使用定理 `and_iff_left`：∀ {b a : Prop}, b → (a ∧ b ↔ a)
· 使用引理 `Set.disjoint_sdiff_right`：disjoint_sdiff_right : Disjoint s (t \ s)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma IsBasis'.contract_indep_sdiff_iff (hI : M.IsBasis' I X) :
    (M ／ X).Indep (J \ X) ↔ M.Indep ((J \ X) ∪ I) := by
  rw [hI.contract_indep_iff, and_iff_left disjoint_sdiff_right]

@[deprecated (since := "2026-06-03")]
alias IsBasis'.contract_indep_diff_iff := IsBasis'.contract_indep_sdiff_iff
/-
**Matroid.IsBasis.contract_isBasis_of_isBasis'** 是 Mathlib 中的一个定理，位于命名空间 `Matroi
d.IsBasis`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I J X C : Set α},   M.IsBasis I X → M.Is
Basis' J C → M.Indep (I \ C ∪ J) → (M.contract C).IsBasis (I \ C) (X \ C)
参数：I \ C ∪ J；M.contract C；I \ C；X \ C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsBasis.subset`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, 
M.IsBasis I X → I ⊆ X
· 使用定理 `Matroid.IsBasis'.subset`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α},
 M.IsBasis' I X → I ⊆ X
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.IsBasis'.contract_eq_contract_delete`：∀ {α : Type u_1} {M : Matr
oid α} {I X : Set α}, M.IsBasis' I X → M.contract X = (M.contract I).delete (X \
 I)
· 使用引理 `Matroid.delete_isBasis_iff`：delete_isBasis_iff : (M ＼ D).IsBasis I X ↔ M
.IsBasis I X ∧ Disjoint X D
· 使用定理 `Matroid.IsBasis.contract_isBasis_union_union`：∀ {α : Type u_1} {M : Matr
oid α} {I J X : Set α},   M.IsBasis (J ∪ I) (X ∪ I) → Disjoint J I → Disjoint X 
I → (M.contract I).IsBasis J X
· 使用定理 `Matroid.Indep.isBasis_of_subset_of_subset_closure`：∀ {α : Type u_2} {M :
 Matroid α} {X I : Set α}, M.Indep I → I ⊆ X → X ⊆ M.closure I → M.IsBasis I X
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Decidable.not_or_of_imp`：∀ {a b : Prop} [Decidable a], (a → b) → ¬a ∨ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Decidable.not_and_iff_not_or_not'`：∀ {b a : Prop} [Decidable b], ¬(a ∧ b
) ↔ ¬a ∨ ¬b
· 使用引理 `Matroid.closure_union_congr_right`：closure_union_congr_right {Y' : Set α
} (h : M.closure Y = M.closure Y') : M.closure (X union Y) = M.closure (X union 
Y')
· 使用定理 `Matroid.IsBasis'.closure_eq_closure`：∀ {α : Type u_2} {M : Matroid α} {X
 I : Set α}, M.IsBasis' I X → M.closure I = M.closure X
· 使用定理 `Set.sdiff_union_self`：sdiff_union_self {s t : Set α} : s \ t union t = s
 union t
· 使用引理 `Matroid.closure_union_congr_left`：closure_union_congr_left {X' : Set α} 
(h : M.closure X = M.closure X') : M.closure (X union Y) = M.closure (X' union Y
)
· 使用定理 `Matroid.IsBasis.closure_eq_closure`：∀ {α : Type u_2} {M : Matroid α} {X 
I : Set α}, M.IsBasis I X → M.closure I = M.closure X
· 使用引理 `Matroid.subset_closure_of_subset'`：subset_closure_of_subset' (M : Matroi
d α) (hXY : X subseteq Y) (hX : X subseteq M.E
· 使用定理 `Set.union_subset`：union_subset {s t r : Set α} (sr : s subseteq r) (tr :
 t subseteq r) : s union t subseteq r
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
· 使用定理 `Matroid.IsBasis.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {I X : S
et α}, M.IsBasis I X → X ⊆ M.E
· 使用定理 `Matroid.Indep.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {I : Set α
}, M.Indep I → I ⊆ M.E
· 使用定理 `Matroid.IsBasis'.indep`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, 
M.IsBasis' I X → M.Indep I
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
-/
lemma IsBasis.contract_isBasis_of_isBasis' (h : M.IsBasis I X) (hJC : M.IsBasis' J C)
    (h_ind : M.Indep (I \ C ∪ J)) : (M ／ C).IsBasis (I \ C) (X \ C) := by
  have hIX := h.subset
  have hJCss := hJC.subset
  rw [hJC.contract_eq_contract_delete, delete_isBasis_iff]
  refine ⟨contract_isBasis_union_union (h_ind.isBasis_of_subset_of_subset_closure ?_ ?_) ?_ ?_, ?_⟩
  rotate_left
  · rw [closure_union_congr_right hJC.closure_eq_closure, sdiff_union_self,
      closure_union_congr_left h.closure_eq_closure]
    exact subset_closure_of_subset' _ (by tauto_set)
      (union_subset (sdiff_subset.trans h.subset_ground) hJC.indep.subset_ground)
  all_goals tauto_set
/-
**Matroid.IsBasis'.contract_isBasis'** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBasis'
`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I J X C : Set α},   M.IsBasis' I X → M.I
sBasis' J C → M.Indep (I \ C ∪ J) → (M.contract C).IsBasis' (I \ C) (X \ C)
参数：I \ C ∪ J；M.contract C；I \ C；X \ C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.isBasis'_iff_isBasis_inter_ground`：∀ {α : Type u_1} {M : Matroid
 α} {I X : Set α}, M.IsBasis' I X ↔ M.IsBasis I (X ∩ M.E)
· 使用定理 `Matroid.contract_ground`：∀ {α : Type u_1} (M : Matroid α) (C : Set α), (
M.contract C).E = M.E \ C
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.sdiff_inter_distrib_right`：sdiff_inter_distrib_right (s t r : Set α)
 : (t inter r) \ s = (t \ s) inter (r \ s)
· 使用定理 `Matroid.IsBasis.contract_isBasis_of_isBasis'`：∀ {α : Type u_1} {M : Matr
oid α} {I J X C : Set α},   M.IsBasis I X → M.IsBasis' J C → M.Indep (I \ C ∪ J)
 → (M.contract C).IsBasis (I \ C) …
· 使用定理 `Matroid.IsBasis'.isBasis_inter_ground`：∀ {α : Type u_1} {M : Matroid α} 
{I X : Set α}, M.IsBasis' I X → M.IsBasis I (X ∩ M.E)
-/
lemma IsBasis'.contract_isBasis' (h : M.IsBasis' I X) (hJC : M.IsBasis' J C)
    (h_ind : M.Indep (I \ C ∪ J)) : (M ／ C).IsBasis' (I \ C) (X \ C) := by
  rw [isBasis'_iff_isBasis_inter_ground, contract_ground, ← sdiff_inter_distrib_right]
  exact h.isBasis_inter_ground.contract_isBasis_of_isBasis' hJC h_ind
/-
**Matroid.IsBasis.contract_isBasis** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBasis`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I J X C : Set α},   M.IsBasis I X → M.Is
Basis J C → M.Indep (I \ C ∪ J) → (M.contract C).IsBasis (I \ C) (X \ C)
参数：I \ C ∪ J；M.contract C；I \ C；X \ C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsBasis.contract_isBasis_of_isBasis'`：∀ {α : Type u_1} {M : Matr
oid α} {I J X C : Set α},   M.IsBasis I X → M.IsBasis' J C → M.Indep (I \ C ∪ J)
 → (M.contract C).IsBasis (I \ C) …
· 使用定理 `Matroid.IsBasis.isBasis'`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}
, M.IsBasis I X → M.IsBasis' I X
-/
lemma IsBasis.contract_isBasis (h : M.IsBasis I X) (hJC : M.IsBasis J C)
    (h_ind : M.Indep (I \ C ∪ J)) : (M ／ C).IsBasis (I \ C) (X \ C) :=
  h.contract_isBasis_of_isBasis' hJC.isBasis' h_ind
/-
**Matroid.IsBasis.contract_isBasis_of_disjoint** 是 Mathlib 中的一个定理，位于命名空间 `Matroi
d.IsBasis`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I J X C : Set α},   M.IsBasis I X → M.Is
Basis J C → Disjoint C X → M.Indep (I ∪ J) → (M.contract C).IsBasis I X
参数：I ∪ J；M.contract C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsBasis.contract_isBasis`：∀ {α : Type u_1} {M : Matroid α} {I J 
X C : Set α},   M.IsBasis I X → M.IsBasis J C → M.Indep (I \ C ∪ J) → (M.contrac
t C).IsBasis (I \ C) (…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `imp_iff_right`：∀ {b a : Prop}, a → (a → b ↔ b)
· 使用定理 `Disjoint.sdiff_eq_right`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAl
gebra α] {a b : α}, Disjoint a b → b \ a = b
· 使用定理 `Disjoint.mono_right`：Disjoint.mono_right (h : b <= c) : Disjoint a c -> 
Disjoint a b
· 使用定理 `Matroid.IsBasis.subset`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, 
M.IsBasis I X → I ⊆ X
-/
lemma IsBasis.contract_isBasis_of_disjoint (h : M.IsBasis I X) (hJC : M.IsBasis J C)
    (hdj : Disjoint C X) (h_ind : M.Indep (I ∪ J)) : (M ／ C).IsBasis I X := by
  have h' := h.contract_isBasis hJC
  rwa [(hdj.mono_right h.subset).sdiff_eq_right, hdj.sdiff_eq_right, imp_iff_right h_ind] at h'
/-
**Matroid.IsBasis'.contract_isBasis_of_indep** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.
IsBasis'`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I J X : Set α},   M.IsBasis' I X → M.Ind
ep (I ∪ J) → (M.contract J).IsBasis' (I \ J) (X \ J)
参数：I ∪ J；M.contract J；I \ J；X \ J。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsBasis'.contract_isBasis'`：∀ {α : Type u_1} {M : Matroid α} {I 
J X C : Set α},   M.IsBasis' I X → M.IsBasis' J C → M.Indep (I \ C ∪ J) → (M.con
tract C).IsBasis' (I \ C…
· 使用定理 `Matroid.IsBasis.isBasis'`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}
, M.IsBasis I X → M.IsBasis' I X
· 使用定理 `Matroid.Indep.isBasis_self`：∀ {α : Type u_1} {M : Matroid α} {I : Set α}
, M.Indep I → M.IsBasis I I
· 使用定理 `Matroid.Indep.subset`：∀ {α : Type u_1} {M : Matroid α} {I J : Set α}, M.
Indep J → I ⊆ J → M.Indep I
· 使用定理 `Set.subset_union_right`：subset_union_right {s t : Set α} : t subseteq s 
union t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sdiff_union_self`：sdiff_union_self {s t : Set α} : s \ t union t = s
 union t
-/
lemma IsBasis'.contract_isBasis_of_indep (h : M.IsBasis' I X) (h_ind : M.Indep (I ∪ J)) :
    (M ／ J).IsBasis' (I \ J) (X \ J) :=
  h.contract_isBasis' (h_ind.subset subset_union_right).isBasis_self.isBasis' (by simpa)
/-
**Matroid.IsBasis.contract_isBasis_of_indep** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.I
sBasis`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I J X : Set α},   M.IsBasis I X → M.Inde
p (I ∪ J) → (M.contract J).IsBasis (I \ J) (X \ J)
参数：I ∪ J；M.contract J；I \ J；X \ J。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsBasis.contract_isBasis`：∀ {α : Type u_1} {M : Matroid α} {I J 
X C : Set α},   M.IsBasis I X → M.IsBasis J C → M.Indep (I \ C ∪ J) → (M.contrac
t C).IsBasis (I \ C) (…
· 使用定理 `Matroid.Indep.isBasis_self`：∀ {α : Type u_1} {M : Matroid α} {I : Set α}
, M.Indep I → M.IsBasis I I
· 使用定理 `Matroid.Indep.subset`：∀ {α : Type u_1} {M : Matroid α} {I J : Set α}, M.
Indep J → I ⊆ J → M.Indep I
· 使用定理 `Set.subset_union_right`：subset_union_right {s t : Set α} : t subseteq s 
union t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sdiff_union_self`：sdiff_union_self {s t : Set α} : s \ t union t = s
 union t
-/
lemma IsBasis.contract_isBasis_of_indep (h : M.IsBasis I X) (h_ind : M.Indep (I ∪ J)) :
    (M ／ J).IsBasis (I \ J) (X \ J) :=
  h.contract_isBasis (h_ind.subset subset_union_right).isBasis_self (by simpa)
/-
**Matroid.IsBasis.contract_isBasis_of_disjoint_indep** 是 Mathlib 中的一个定理，位于命名空间 `
Matroid.IsBasis`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I J X : Set α},   M.IsBasis I X → Disjoi
nt J X → M.Indep (I ∪ J) → (M.contract J).IsBasis I X
参数：I ∪ J；M.contract J。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Disjoint.sdiff_eq_right`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAl
gebra α] {a b : α}, Disjoint a b → b \ a = b
· 使用定理 `Disjoint.mono_right`：Disjoint.mono_right (h : b <= c) : Disjoint a c -> 
Disjoint a b
· 使用定理 `Matroid.IsBasis.subset`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, 
M.IsBasis I X → I ⊆ X
· 使用定理 `Matroid.IsBasis.contract_isBasis_of_indep`：∀ {α : Type u_1} {M : Matroid
 α} {I J X : Set α},   M.IsBasis I X → M.Indep (I ∪ J) → (M.contract J).IsBasis 
(I \ J) (X \ J)
-/
lemma IsBasis.contract_isBasis_of_disjoint_indep (h : M.IsBasis I X) (hdj : Disjoint J X)
    (h_ind : M.Indep (I ∪ J)) : (M ／ J).IsBasis I X := by
  rw [← hdj.sdiff_eq_right, ← (hdj.mono_right h.subset).sdiff_eq_right]
  exact h.contract_isBasis_of_indep h_ind
/-
**Matroid.Indep.of_contract** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Indep`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I C : Set α}, (M.contract C).Indep I → M
.Indep I
参数：M.contract C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.Indep.subset`：∀ {α : Type u_1} {M : Matroid α} {I J : Set α}, M.
Indep J → I ⊆ J → M.Indep I
· 使用定理 `Matroid.exists_isBasis'`：exists_isBasis' (M : Matroid α) (X : Set α) : e
xists I, M.IsBasis' I X
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Matroid.IsBasis'.contract_indep_iff`：∀ {α : Type u_1} {M : Matroid α} {I
 J X : Set α},   M.IsBasis' I X → ((M.contract X).Indep J ↔ M.Indep (J ∪ I) ∧ Di
sjoint X J)
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
-/
lemma Indep.of_contract (hI : (M ／ C).Indep I) : M.Indep I :=
  ((M.exists_isBasis' C).choose_spec.contract_indep_iff.1 hI).1.subset subset_union_left
/-
**Matroid.Dep.of_contract** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Dep`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {X C : Set α},   (M.contract C).Dep X → a
utoParam (C ⊆ M.E) Matroid.Dep.of_contract._auto_1 → M.Dep (C ∪ X)
参数：M.contract C；C ⊆ M.E；C ∪ X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.Dep.eq_1`：∀ {α : Type u_1} (M : Matroid α) (D : Set α), M.Dep D 
= (¬M.Indep D ∧ D ⊆ M.E)
· 使用定理 `and_iff_left`：∀ {b a : Prop}, b → (a ∧ b ↔ a)
· 使用定理 `Set.union_subset`：union_subset {s t r : Set α} (sr : s subseteq r) (tr :
 t subseteq r) : s union t subseteq r
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Matroid.Dep.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {D : Set α},
 M.Dep D → D ⊆ M.E
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Set.union_comm`：union_comm (a b : Set α) : a union b = b union a
· 使用定理 `Matroid.Indep.contract_indep_iff`：∀ {α : Type u_1} {M : Matroid α} {I J 
: Set α}, M.Indep I → ((M.contract I).Indep J ↔ Disjoint J I ∧ M.Indep (J ∪ I))
· 使用定理 `Matroid.Indep.subset`：∀ {α : Type u_1} {M : Matroid α} {I J : Set α}, M.
Indep J → I ⊆ J → M.Indep I
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Set.subset_sdiff`：subset_sdiff : s subseteq t \ u ↔ s subseteq t ∧ Disjo
int s u
-/
lemma Dep.of_contract (h : (M ／ C).Dep X) (hC : C ⊆ M.E := by aesop_mat) : M.Dep (C ∪ X) := by
  rw [Dep, and_iff_left (union_subset hC (h.subset_ground.trans sdiff_subset))]
  intro hi
  rw [Dep, (hi.subset subset_union_left).contract_indep_iff, union_comm,
    and_iff_left hi] at h
  exact h.1 (subset_sdiff.1 h.2).2

/-! ### Finiteness -/

/-
**Matroid.contract_finite** 是 Mathlib 中的一个实例，位于命名空间 `Matroid`。
形式化陈述：contract_finite [M.Finite] : (M ／ C).Finite
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Matroid.dual_delete_dual`：dual_delete_dual (M : Matroid α) (X : Set α) :
 (M✶ ＼ X)✶ = M ／ X

--- 原说明 ---
### Finiteness
-/
instance contract_finite [M.Finite] : (M ／ C).Finite := by
  rw [← dual_delete_dual]
  infer_instance
/-
**Matroid.contract_rankFinite** 是 Mathlib 中的一个实例，位于命名空间 `Matroid`。
形式化陈述：contract_rankFinite [RankFinite M] : RankFinite (M ／ C)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.exists_isBase`：∀ {α : Type u_1} (self : Matroid α), ∃ B, self.Is
Base B
· 使用定理 `Matroid.Indep.finite`：∀ {α : Type u_1} {M : Matroid α} {I : Set α} [M.Ra
nkFinite], M.Indep I → I.Finite
· 使用定理 `Matroid.Indep.of_contract`：∀ {α : Type u_1} {M : Matroid α} {I C : Set α
}, (M.contract C).Indep I → M.Indep I
· 使用定理 `Matroid.IsBase.indep`：∀ {α : Type u_1} {M : Matroid α} {B : Set α}, M.Is
Base B → M.Indep B
-/
instance contract_rankFinite [RankFinite M] : RankFinite (M ／ C) :=
  let ⟨B, hB⟩ := (M ／ C).exists_isBase
  ⟨B, hB, hB.indep.of_contract.finite⟩
/-
**Matroid.contract_finitary** 是 Mathlib 中的一个实例，位于命名空间 `Matroid`。
形式化陈述：contract_finitary [Finitary M] : Finitary (M ／ C)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.exists_isBasis'`：exists_isBasis' (M : Matroid α) (X : Set α) : e
xists I, M.IsBasis' I X
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Matroid.Indep.contract_indep_iff`：∀ {α : Type u_1} {M : Matroid α} {I J 
: Set α}, M.Indep I → ((M.contract I).Indep J ↔ Disjoint J I ∧ M.Indep (J ∪ I))
· 使用定理 `Matroid.IsBasis'.indep`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, 
M.IsBasis' I X → M.Indep I
· 使用定理 `Set.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s -> 
a ∉ t
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Matroid.Indep.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {I : Set α
}, M.Indep I → I ⊆ M.E
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Matroid.indep_of_forall_finite_subset_indep`：indep_of_forall_finite_subs
et_indep {M : Matroid α} [Finitary M] (I : Set α) (h : forall J, J subseteq I ->
 J.Finite -> M.Indep J) : M.Indep…
· 使用定理 `Matroid.Indep.subset`：∀ {α : Type u_1} {M : Matroid α} {I J : Set α}, M.
Indep J → I ⊆ J → M.Indep I
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `Set.Finite.inter_of_left`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ (t : 
Set α), (s ∩ t).Finite
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Decidable.not_or_of_imp`：∀ {a b : Prop} [Decidable a], (a → b) → ¬a ∨ b
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `Decidable.not_and_iff_not_or_not'`：∀ {b a : Prop} [Decidable b], ¬(a ∧ b
) ↔ ¬a ∨ ¬b
· 使用定理 `of_decide_eq_false`：∀ {p : Prop} [inst : Decidable p], decide p = false 
→ ¬p
· 使用定理 `Matroid.IsBasis'.contract_eq_contract_delete`：∀ {α : Type u_1} {M : Matr
oid α} {I X : Set α}, M.IsBasis' I X → M.contract X = (M.contract I).delete (X \
 I)
-/
instance contract_finitary [Finitary M] : Finitary (M ／ C) := by
  obtain ⟨J, hJ⟩ := M.exists_isBasis' C
  suffices (M ／ J).Finitary by
    rw [hJ.contract_eq_contract_delete]
    infer_instance
  exact ⟨fun I hI ↦ hJ.indep.contract_indep_iff.2  ⟨disjoint_left.2 fun e heI ↦
    ((hI {e} (by simpa) (by simp)).subset_ground rfl).2,
    indep_of_forall_finite_subset_indep _ fun K hK hKfin ↦
      (hJ.indep.contract_indep_iff.1 <| hI (K ∩ I)
      inter_subset_right (hKfin.inter_of_left _)).2.subset (by tauto_set)⟩⟩

/-! ### Loops and Coloops -/

/-
**Matroid.contract_eq_delete_of_subset_loops** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`
。
形式化陈述：contract_eq_delete_of_subset_loops (hX : X subseteq M.loops) : M ／ X = M ＼
 X
参数：hX : X subseteq M.loops。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.IsBasis.contract_eq_contract_delete`：∀ {α : Type u_1} {M : Matro
id α} {I X : Set α}, M.IsBasis I X → M.contract X = (M.contract I).delete (X \ I
)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Matroid.empty_isBasis_iff`：∀ {α : Type u_2} {M : Matroid α} {X : Set α},
 M.IsBasis ∅ X ↔ X ⊆ M.closure ∅
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Matroid.contract_empty`：∀ {α : Type u_1} (M : Matroid α), M.contract ∅ =
 M
· 使用定理 `Set.sdiff_empty`：sdiff_empty {s : Set α} : s \ ∅ = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
### Loops and Coloops
-/
lemma contract_eq_delete_of_subset_loops (hX : X ⊆ M.loops) : M ／ X = M ＼ X := by
  simp [(empty_isBasis_iff.2 hX).contract_eq_contract_delete]
/-
**Matroid.contract_eq_delete_of_subset_coloops** 是 Mathlib 中的一个引理，位于命名空间 `Matroi
d`。
形式化陈述：contract_eq_delete_of_subset_coloops (hX : X subseteq M.coloops) : M ／ X =
 M ＼ X
参数：hX : X subseteq M.coloops。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.dual_inj`：∀ {α : Type u_1} {M₁ M₂ : Matroid α}, M₁✶ = M₂✶ ↔ M₁ =
 M₂
· 使用引理 `Matroid.dual_delete`：dual_delete (M : Matroid α) (X : Set α) : (M ＼ X)✶ 
= M✶ ／ X
· 使用引理 `Matroid.contract_eq_delete_of_subset_loops`：contract_eq_delete_of_subset
_loops (hX : X subseteq M.loops) : M ／ X = M ＼ X
· 使用引理 `Matroid.dual_contract`：dual_contract (M : Matroid α) (X : Set α) : (M ／ 
X)✶ = M✶ ＼ X
-/
lemma contract_eq_delete_of_subset_coloops (hX : X ⊆ M.coloops) : M ／ X = M ＼ X := by
  rw [← dual_inj, dual_delete, contract_eq_delete_of_subset_loops hX, dual_contract]

@[simp]
/-
**Matroid.contract_isLoop_iff_mem_closure** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：contract_isLoop_iff_mem_closure : (M ／ C).IsLoop e ↔ e in M.closure C ∧ e 
∉ C
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.exists_isBasis'`：exists_isBasis' (M : Matroid α) (X : Set α) : e
xists I, M.IsBasis' I X
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.IsBasis'.contract_eq_contract_delete`：∀ {α : Type u_1} {M : Matr
oid α} {I X : Set α}, M.IsBasis' I X → M.contract X = (M.contract I).delete (X \
 I)
· 使用引理 `Matroid.delete_isLoop_iff`：delete_isLoop_iff : (M ＼ D).IsLoop e ↔ M.IsLo
op e ∧ e ∉ D
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Matroid.singleton_dep`：singleton_dep : M.Dep {e} ↔ M.IsLoop e
· 使用定理 `Matroid.Indep.contract_dep_iff`：∀ {α : Type u_1} {M : Matroid α} {I J : 
Set α}, M.Indep I → ((M.contract I).Dep J ↔ Disjoint J I ∧ M.Dep (J ∪ I))
· 使用定理 `Matroid.IsBasis'.indep`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, 
M.IsBasis' I X → M.Indep I
· 使用定理 `Set.singleton_union`：singleton_union : {a} union s = insert a s
· 使用定理 `Matroid.Indep.insert_dep_iff`：∀ {α : Type u_2} {M : Matroid α} {e : α} {
I : Set α}, M.Indep I → (M.Dep (insert e I) ↔ e ∈ M.closure I \ I)
· 使用定理 `Matroid.IsBasis'.closure_eq_closure`：∀ {α : Type u_2} {M : Matroid α} {X
 I : Set α}, M.IsBasis' I X → M.closure I = M.closure X
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Matroid.IsBasis'.subset`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α},
 M.IsBasis' I X → I ⊆ X
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
-/
lemma contract_isLoop_iff_mem_closure : (M ／ C).IsLoop e ↔ e ∈ M.closure C ∧ e ∉ C := by
  obtain ⟨I, hI⟩ := M.exists_isBasis' C
  rw [hI.contract_eq_contract_delete, delete_isLoop_iff, ← singleton_dep,
    hI.indep.contract_dep_iff, singleton_union, hI.indep.insert_dep_iff, hI.closure_eq_closure]
  by_cases heI : e ∈ I
  · simp [heI, hI.subset heI]
  simp [heI, and_comm]

@[simp]
/-
**Matroid.contract_loops_eq** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：contract_loops_eq (M : Matroid α) (C : Set α) : (M ／ C).loops = M.closure 
C \ C
参数：M : Matroid α；C : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma contract_loops_eq (M : Matroid α) (C : Set α) : (M ／ C).loops = M.closure C \ C := by
  simp [Set.ext_iff, ← isLoop_iff, contract_isLoop_iff_mem_closure]

@[simp]
/-
**Matroid.contract_coloops_eq** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：contract_coloops_eq (M : Matroid α) (C : Set α) : (M ／ C).coloops = M.colo
ops \ C
参数：M : Matroid α；C : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Matroid.dual_delete_dual`：dual_delete_dual (M : Matroid α) (X : Set α) :
 (M✶ ＼ X)✶ = M ／ X
· 使用引理 `Matroid.dual_coloops`：dual_coloops : M✶.coloops = M.loops
· 使用引理 `Matroid.delete_loops_eq`：delete_loops_eq (M : Matroid α) (D : Set α) : (
M ＼ D).loops = M.loops \ D
· 使用引理 `Matroid.dual_loops`：dual_loops : M✶.loops = M.coloops
-/
lemma contract_coloops_eq (M : Matroid α) (C : Set α) : (M ／ C).coloops = M.coloops \ C := by
  rw [← dual_delete_dual, dual_coloops, delete_loops_eq, dual_loops]

@[simp]
/-
**Matroid.contract_isColoop_iff** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：contract_isColoop_iff : (M ／ C).IsColoop e ↔ M.IsColoop e ∧ e ∉ C
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Matroid.contract_coloops_eq`：contract_coloops_eq (M : Matroid α) (C : Se
t α) : (M ／ C).coloops = M.coloops \ C
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma contract_isColoop_iff : (M ／ C).IsColoop e ↔ M.IsColoop e ∧ e ∉ C := by
  simp [isColoop_iff_mem_coloops]
/-
**Matroid.IsNonloop.of_contract** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsNonloop`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {e : α} {C : Set α}, (M.contract C).IsNon
loop e → M.IsNonloop e
参数：M.contract C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Matroid.indep_singleton`：indep_singleton : M.Indep {e} ↔ M.IsNonloop e
· 使用定理 `Matroid.Indep.of_contract`：∀ {α : Type u_1} {M : Matroid α} {I C : Set α
}, (M.contract C).Indep I → M.Indep I
-/
lemma IsNonloop.of_contract (h : (M ／ C).IsNonloop e) : M.IsNonloop e := by
  rw [← indep_singleton] at h ⊢
  exact h.of_contract

@[simp]
/-
**Matroid.contract_isNonloop_iff** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：contract_isNonloop_iff : (M ／ C).IsNonloop e ↔ e in M.E \ M.closure C
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matroid.isNonloop_iff_mem_compl_loops`：isNonloop_iff_mem_compl_loops : M
.IsNonloop e ↔ e in M.E \ M.loops
· 使用定理 `Matroid.contract_ground`：∀ {α : Type u_1} (M : Matroid α) (C : Set α), (
M.contract C).E = M.E \ C
· 使用引理 `Matroid.contract_loops_eq`：contract_loops_eq (M : Matroid α) (C : Set α)
 : (M ／ C).loops = M.closure C \ C
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.closure_inter_ground`：∀ {α : Type u_2} (M : Matroid α) (X : Set 
α), M.closure (X ∩ M.E) = M.closure X
· 使用引理 `Matroid.subset_closure`：subset_closure (M : Matroid α) (X : Set α) (hX :
 X subseteq M.E
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
lemma contract_isNonloop_iff : (M ／ C).IsNonloop e ↔ e ∈ M.E \ M.closure C := by
  rw [isNonloop_iff_mem_compl_loops, contract_ground, contract_loops_eq]
  refine ⟨fun ⟨he,heC⟩ ↦ ⟨he.1, fun h ↦ heC ⟨h, he.2⟩⟩,
    fun h ↦ ⟨⟨h.1, fun heC ↦ h.2 ?_⟩, fun h' ↦ h.2 h'.1⟩⟩
  rw [← closure_inter_ground]
  exact (M.subset_closure (C ∩ M.E)) ⟨heC, h.1⟩
/-
**Matroid.IsBasis.sdiff_subset_loops_contract** 是 Mathlib 中的一个定理，位于命名空间 `Matroid
.IsBasis`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, M.IsBasis I X → X \ I ⊆ (M
.contract I).loops
参数：M.contract I。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sdiff_subset_iff`：sdiff_subset_iff {s t u : Set α} : s \ t subseteq 
u ↔ s subseteq t union u
· 使用引理 `Matroid.contract_loops_eq`：contract_loops_eq (M : Matroid α) (C : Set α)
 : (M ／ C).loops = M.closure C \ C
· 使用定理 `Set.union_sdiff_self`：union_sdiff_self {s t : Set α} : s union t \ s = s
 union t
· 使用定理 `Set.union_eq_self_of_subset_left`：union_eq_self_of_subset_left {s t : Se
t α} (h : s subseteq t) : s union t = t
· 使用引理 `Matroid.subset_closure`：subset_closure (M : Matroid α) (X : Set α) (hX :
 X subseteq M.E
· 使用定理 `Matroid.IsBasis.left_subset_ground`：∀ {α : Type u_1} {M : Matroid α} {I 
X : Set α}, M.IsBasis I X → I ⊆ M.E
· 使用定理 `Matroid.IsBasis.subset_closure`：∀ {α : Type u_2} {M : Matroid α} {X I : 
Set α}, M.IsBasis I X → X ⊆ M.closure I
-/
lemma IsBasis.sdiff_subset_loops_contract (hIX : M.IsBasis I X) : X \ I ⊆ (M ／ I).loops := by
  rw [sdiff_subset_iff, contract_loops_eq, union_sdiff_self,
    union_eq_self_of_subset_left (M.subset_closure I)]
  exact hIX.subset_closure

@[deprecated (since := "2026-06-03")]
alias IsBasis.diff_subset_loops_contract := IsBasis.sdiff_subset_loops_contract

/-! ### Closure -/

/-- Contracting the closure of a set is the same as contracting the set,
and then deleting the rest of its elements. -/
/-
**Matroid.contract_closure_eq_contract_delete** 是 Mathlib 中的一个引理，位于命名空间 `Matroid
`。
形式化陈述：contract_closure_eq_contract_delete (M : Matroid α) (C : Set α) : M ／ M.cl
osure C = M ／ C ＼ (M.closure C \ C)
参数：M : Matroid α；C : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `Matroid.exists_isBasis`：exists_isBasis (M : Matroid α) (X : Set α) (hX :
 X subseteq M.E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.IsBasis.contract_eq_contract_delete`：∀ {α : Type u_1} {M : Matro
id α} {I X : Set α}, M.IsBasis I X → M.contract X = (M.contract I).delete (X \ I
)
· 使用定理 `Matroid.IsBasis.isBasis_closure_right`：∀ {α : Type u_2} {M : Matroid α} 
{X I : Set α}, M.IsBasis I X → M.IsBasis I (M.closure X)
· 使用引理 `Matroid.delete_delete`：delete_delete (M : Matroid α) (D₁ D₂ : Set α) : M
 ＼ D₁ ＼ D₂ = M ＼ (D₁ union D₂)
· 使用定理 `Set.union_comm`：union_comm (a b : Set α) : a union b = b union a
· 使用定理 `Set.sdiff_union_sdiff_cancel`：sdiff_union_sdiff_cancel (hts : t subseteq
 s) (hut : u subseteq t) : s \ t union t \ u = s \ u
· 使用引理 `Matroid.subset_closure`：subset_closure (M : Matroid α) (X : Set α) (hX :
 X subseteq M.E
· 使用定理 `Matroid.IsBasis.subset`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, 
M.IsBasis I X → I ⊆ X
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.contract_inter_ground_eq`：∀ {α : Type u_1} (M : Matroid α) (C : 
Set α), M.contract (C ∩ M.E) = M.contract C
· 使用定理 `Matroid.closure_inter_ground`：∀ {α : Type u_2} (M : Matroid α) (X : Set 
α), M.closure (X ∩ M.E) = M.closure X
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `Set.sdiff_inter`：sdiff_inter {s t u : Set α} : s \ (t inter u) = s \ t u
nion s \ u
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.sdiff_eq_empty`：sdiff_eq_empty {s t : Set α} : s \ t = ∅ ↔ s subsete
q t
· 使用引理 `Matroid.closure_subset_ground`：closure_subset_ground (M : Matroid α) (X 
: Set α) : M.closure X subseteq M.E
· 使用定理 `Set.union_empty`：union_empty (a : Set α) : a union ∅ = a

--- 原说明 ---
Contracting the closure of a set is the same as contracting the set,
and then deleting the rest of its elements.
-/
lemma contract_closure_eq_contract_delete (M : Matroid α) (C : Set α) :
    M ／ M.closure C = M ／ C ＼ (M.closure C \ C) := by
  wlog hCE : C ⊆ M.E with aux
  · rw [← M.contract_inter_ground_eq C, ← closure_inter_ground, aux _ _ inter_subset_right,
      sdiff_inter, sdiff_eq_empty.2 (M.closure_subset_ground _), union_empty]
  obtain ⟨I, hI⟩ := M.exists_isBasis C
  rw [hI.isBasis_closure_right.contract_eq_contract_delete, hI.contract_eq_contract_delete,
    delete_delete, union_comm, sdiff_union_sdiff_cancel (M.subset_closure C) hI.subset]

@[simp]
/-
**Matroid.contract_closure_eq** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：contract_closure_eq (M : Matroid α) (C X : Set α) : (M ／ C).closure X = M.
closure (X union C) \ C
参数：M : Matroid α；C X : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.sdiff_union_inter`：sdiff_union_inter (s t : Set α) : s \ t union s i
nter t = s
· 使用定理 `Set.sdiff_sdiff`：sdiff_sdiff {u : Set α} : (s \ t) \ u = s \ (t union u)
· 使用定理 `Set.union_comm`：union_comm (a b : Set α) : a union b = b union a
· 使用引理 `Matroid.contract_loops_eq`：contract_loops_eq (M : Matroid α) (C : Set α)
 : (M ／ C).loops = M.closure C \ C
· 使用引理 `Matroid.contract_contract`：contract_contract (M : Matroid α) (C₁ C₂ : Se
t α) : M ／ C₁ ／ C₂ = M ／ (C₁ union C₂)
· 使用定理 `subset_antisymm_iff`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst 
: PartialOrder α] {a b : α}, a = b ↔ a ⊆ b ∧ b ⊆ a
· 使用定理 `Set.union_subset_iff`：union_subset_iff {s t u : Set α} : s union t subse
teq u ↔ s subseteq u ∧ t subseteq u
· 使用定理 `and_iff_right`：∀ {a b : Prop}, a → (a ∧ b ↔ b)
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
· 使用定理 `Set.sdiff_subset_iff`：sdiff_subset_iff {s t u : Set α} : s \ t subseteq 
u ↔ s subseteq t union u
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.sdiff_sdiff_right_self`：sdiff_sdiff_right_self (s t : Set α) : s \ (
s \ t) = s inter t
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用引理 `Matroid.mem_closure_of_mem'`：mem_closure_of_mem' (M : Matroid α) (heX : 
e in X) (h : e in M.E
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `Matroid.mem_ground_of_mem_closure`：mem_ground_of_mem_closure (he : e in 
M.closure X) : e in M.E
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `Matroid.closure_subset_ground`：closure_subset_ground (M : Matroid α) (X 
: Set α) : M.closure X subseteq M.E
-/
lemma contract_closure_eq (M : Matroid α) (C X : Set α) :
    (M ／ C).closure X = M.closure (X ∪ C) \ C := by
  rw [← sdiff_union_inter (M.closure (X ∪ C) \ C) X, sdiff_sdiff, union_comm C, ← contract_loops_eq,
    union_comm X, ← contract_contract, contract_loops_eq, subset_antisymm_iff, union_subset_iff,
    and_iff_right sdiff_subset, ← sdiff_subset_iff]
  simp only [sdiff_sdiff_right_self, subset_inter_iff, inter_subset_right, and_true]
  refine ⟨fun e ⟨he, he'⟩ ↦ ⟨mem_closure_of_mem' _ (.inr he') (mem_ground_of_mem_closure he).1,
    (closure_subset_ground _ _ he).2⟩, fun e ⟨⟨he, heC⟩, he'⟩ ↦
    mem_closure_of_mem' _ he' ⟨M.closure_subset_ground _ he, heC⟩⟩
/-
**Matroid.contract_spanning_iff** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：contract_spanning_iff (hC : C subseteq M.E
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.spanning_iff`：∀ {α : Type u_2} (M : Matroid α) (S : Set α), M.Sp
anning S ↔ M.closure S = M.E ∧ S ⊆ M.E
· 使用引理 `Matroid.contract_closure_eq`：contract_closure_eq (M : Matroid α) (C X : 
Set α) : (M ／ C).closure X = M.closure (X union C) \ C
· 使用定理 `Matroid.contract_ground`：∀ {α : Type u_1} (M : Matroid α) (C : Set α), (
M.contract C).E = M.E \ C
· 使用定理 `Set.union_subset_iff`：union_subset_iff {s t u : Set α} : s union t subse
teq u ↔ s subseteq u ∧ t subseteq u
· 使用引理 `Set.subset_sdiff`：subset_sdiff : s subseteq t \ u ↔ s subseteq t ∧ Disjo
int s u
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `and_assoc`：∀ {a b c : Prop}, (a ∧ b) ∧ c ↔ a ∧ b ∧ c
· 使用定理 `and_congr_left_iff`：∀ {a c b : Prop}, (a ∧ c ↔ b ∧ c) ↔ c → (a ↔ b)
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
· 使用定理 `Set.union_sdiff_cancel`：union_sdiff_cancel {s t : Set α} (h : s subseteq
 t) : s union t \ s = t
· 使用引理 `Matroid.subset_closure_of_subset'`：subset_closure_of_subset' (M : Matroi
d α) (hXY : X subseteq Y) (hX : X subseteq M.E
· 使用定理 `Set.subset_union_right`：subset_union_right {s t : Set α} : t subseteq s 
union t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma contract_spanning_iff (hC : C ⊆ M.E := by aesop_mat) :
    (M ／ C).Spanning X ↔ M.Spanning (X ∪ C) ∧ Disjoint X C := by
  rw [spanning_iff, contract_closure_eq, contract_ground, spanning_iff, union_subset_iff,
    subset_sdiff, ← and_assoc, and_congr_left_iff, and_comm (a := X ⊆ _), ← and_assoc,
    and_congr_left_iff]
  refine fun hdj hX ↦ ⟨fun h ↦ ⟨?_, hC⟩, fun h ↦ by simp [h]⟩
  rwa [← union_sdiff_cancel (M.subset_closure_of_subset' subset_union_right hC), h,
    union_sdiff_cancel]

/-- A version of `Matroid.contract_spanning_iff` without the ground-set hypothesis. -/
/-
**Matroid.contract_spanning_iff'** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：contract_spanning_iff' : (M ／ C).Spanning X ↔ M.Spanning (X union (C inter
 M.E)) ∧ Disjoint X C
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.contract_inter_ground_eq`：∀ {α : Type u_1} (M : Matroid α) (C : 
Set α), M.contract (C ∩ M.E) = M.contract C
· 使用引理 `Matroid.contract_spanning_iff`：contract_spanning_iff (hC : C subseteq M.
E
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `and_congr_right_iff`：∀ {a b c : Prop}, (a ∧ b ↔ a ∧ c) ↔ a → (b ↔ c)
· 使用定理 `Set.sdiff_union_inter`：sdiff_union_inter (s t : Set α) : s \ t union s i
nter t = s
· 使用引理 `Set.disjoint_union_right`：disjoint_union_right : Disjoint s (t union u) 
↔ Disjoint s t ∧ Disjoint s u
· 使用定理 `and_iff_left`：∀ {b a : Prop}, b → (a ∧ b ↔ a)
· 使用定理 `Disjoint.mono_left`：Disjoint.mono_left (h : a <= b) : Disjoint b c -> Di
sjoint a c
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
· 使用定理 `Matroid.Spanning.subset_ground`：∀ {α : Type u_2} {M : Matroid α} {S : Se
t α}, M.Spanning S → S ⊆ M.E
· 使用引理 `Set.disjoint_sdiff_right`：disjoint_sdiff_right : Disjoint s (t \ s)
· 使用定理 `Disjoint.mono_right`：Disjoint.mono_right (h : b <= c) : Disjoint a c -> 
Disjoint a b
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s

--- 原说明 ---
A version of `Matroid.contract_spanning_iff` without the ground-set hypothesis.
-/
lemma contract_spanning_iff' : (M ／ C).Spanning X ↔ M.Spanning (X ∪ (C ∩ M.E)) ∧ Disjoint X C := by
  rw [← contract_inter_ground_eq, contract_spanning_iff, and_congr_right_iff]
  refine fun h ↦ ⟨fun hdj ↦ ?_, Disjoint.mono_right inter_subset_left⟩
  rw [← sdiff_union_inter C M.E, disjoint_union_right, and_iff_left hdj]
  exact disjoint_sdiff_right.mono_left (subset_union_left.trans h.subset_ground)
/-
**Matroid.Spanning.contract** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Spanning`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {X : Set α}, M.Spanning X → ∀ (C : Set α)
, (M.contract C).Spanning (X \ C)
参数：C : Set α；M.contract C；X \ C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.Spanning.subset_ground`：∀ {α : Type u_2} {M : Matroid α} {S : Se
t α}, M.Spanning S → S ⊆ M.E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matroid.contract_spanning_iff'`：contract_spanning_iff' : (M ／ C).Spannin
g X ↔ M.Spanning (X union (C inter M.E)) ∧ Disjoint X C
· 使用定理 `and_iff_left`：∀ {b a : Prop}, b → (a ∧ b ↔ a)
· 使用引理 `Set.disjoint_sdiff_left`：disjoint_sdiff_left : Disjoint (t \ s) s
· 使用定理 `Matroid.Spanning.superset`：∀ {α : Type u_2} {M : Matroid α} {S T : Set α
},   M.Spanning S → S ⊆ T → autoParam (T ⊆ M.E) Matroid.Spanning.superset._auto_
1 → M.Spanning …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Decidable.not_or_of_imp`：∀ {a b : Prop} [Decidable a], (a → b) → ¬a ∨ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Decidable.not_and_iff_not_or_not'`：∀ {b a : Prop} [Decidable b], ¬(a ∧ b
) ↔ ¬a ∨ ¬b
· 使用定理 `of_decide_eq_false`：∀ {p : Prop} [inst : Decidable p], decide p = false 
→ ¬p
· 使用定理 `Decidable.of_not_not`：∀ {p : Prop} [Decidable p], ¬¬p → p
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
lemma Spanning.contract (hX : M.Spanning X) (C : Set α) : (M ／ C).Spanning (X \ C) := by
  have hXE := hX.subset_ground
  rw [contract_spanning_iff', and_iff_left disjoint_sdiff_left]
  exact hX.superset (by tauto_set) (by tauto_set)
/-
**Matroid.Spanning.contract_eq_loopyOn** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Spanni
ng`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {X : Set α}, M.Spanning X → M.contract X 
= Matroid.loopyOn (M.E \ X)
参数：M.E \ X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matroid.eq_loopyOn_iff_loops_eq`：eq_loopyOn_iff_loops_eq {E : Set α} : M
 = loopyOn E ↔ M.loops = E ∧ M.E = E
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Matroid.contract_loops_eq`：contract_loops_eq (M : Matroid α) (C : Set α)
 : (M ／ C).loops = M.closure C \ C
· 使用定理 `Matroid.Spanning.closure_eq`：∀ {α : Type u_2} {M : Matroid α} {S : Set α
}, M.Spanning S → M.closure S = M.E
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
lemma Spanning.contract_eq_loopyOn (hX : M.Spanning X) : M ／ X = loopyOn (M.E \ X) := by
  rw [eq_loopyOn_iff_loops_eq]
  simp [hX.closure_eq]

/-! ### Circuits -/

/-
**Matroid.IsCircuit.contract_isCircuit** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsCirc
uit`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {K C : Set α}, M.IsCircuit K → C ⊂ K → (M
.contract C).IsCircuit (K \ C)
参数：M.contract C；K \ C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.Indep.subset`：∀ {α : Type u_1} {M : Matroid α} {I J : Set α}, M.
Indep J → I ⊆ J → M.Indep I
· 使用定理 `Matroid.IsCircuit.sdiff_singleton_indep`：∀ {α : Type u_1} {M : Matroid α
} {C : Set α} {e : α}, M.IsCircuit C → e ∈ C → M.Indep (C \ {e})
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用引理 `Set.subset_sdiff_singleton`：subset_sdiff_singleton (h : s subseteq t) (h
a : a ∉ s) : s subseteq t \ {a}
· 使用定理 `LT.lt.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preor
der α] {a b : α}, a ⊂ b → a ⊆ b
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Matroid.Indep.contract_indep_iff`：∀ {α : Type u_1} {M : Matroid α} {I J 
: Set α}, M.Indep I → ((M.contract I).Indep J ↔ Disjoint J I ∧ M.Indep (J ∪ I))
· 使用定理 `Matroid.IsCircuit.ssubset_indep`：∀ {α : Type u_1} {M : Matroid α} {C X :
 Set α}, M.IsCircuit C → X ⊂ C → M.Indep X
· 使用定理 `Set.sdiff_union_of_subset`：sdiff_union_of_subset {s t : Set α} (h : t su
bseteq s) : s \ t union t = s
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Matroid.IsCircuit.not_indep`：∀ {α : Type u_1} {M : Matroid α} {C : Set α
}, M.IsCircuit C → ¬M.Indep C
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Set.sdiff_subset_sdiff_left`：sdiff_subset_sdiff_left {s₁ s₂ t : Set α} (
h : s₁ subseteq s₂) : s₁ \ t subseteq s₂ \ t
· 使用定理 `Matroid.IsCircuit.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {C : S
et α}, M.IsCircuit C → C ⊆ M.E
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Set.sdiff_sdiff_comm`：sdiff_sdiff_comm {s t u : Set α} : (s \ t) \ u = (
s \ u) \ t
· 使用定理 `Set.sdiff_union_self`：sdiff_union_self {s t : Set α} : s \ t union t = s
 union t
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p

--- 原说明 ---
### Circuits
-/
lemma IsCircuit.contract_isCircuit (hK : M.IsCircuit K) (hC : C ⊂ K) :
    (M ／ C).IsCircuit (K \ C) := by
  suffices ∀ e ∈ K, e ∉ C → M.Indep (K \ {e} ∪ C) by
    simpa [isCircuit_iff_dep_forall_sdiff_singleton_indep, sdiff_sdiff_comm (s := K) (t := C),
    dep_iff, (hK.ssubset_indep hC).contract_indep_iff, sdiff_subset_sdiff_left hK.subset_ground,
    disjoint_sdiff_left, sdiff_union_of_subset hC.subset, hK.not_indep]
  exact fun e heK heC ↦ (hK.sdiff_singleton_indep heK).subset <| by
    simp [subset_sdiff_singleton hC.subset heC]
/-
**Matroid.IsCircuit.contractElem_isCircuit** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Is
Circuit`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {e : α} {C : Set α},   M.IsCircuit C → C.
Nontrivial → e ∈ C → (M.contract {e}).IsCircuit (C \ {e})
参数：M.contract {e}；C \ {e}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsCircuit.contract_isCircuit`：∀ {α : Type u_1} {M : Matroid α} {
K C : Set α}, M.IsCircuit K → C ⊂ K → (M.contract C).IsCircuit (K \ C)
· 使用定理 `ssubset_of_ne_of_subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [i
nst : PartialOrder α] {a b : α}, a ≠ b → a ⊆ b → a ⊂ b
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Set.Nontrivial.ne_singleton`：∀ {α : Type u} {s : Set α} {x : α}, s.Nontr
ivial → s ≠ {x}
-/
lemma IsCircuit.contractElem_isCircuit (hC : M.IsCircuit C) (hnt : C.Nontrivial) (heC : e ∈ C) :
    (M ／ {e}).IsCircuit (C \ {e}) :=
  hC.contract_isCircuit (ssubset_of_ne_of_subset hnt.ne_singleton.symm (by simpa))
/-
**Matroid.IsCircuit.contract_dep** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsCircuit`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {K C : Set α}, M.IsCircuit K → Disjoint C
 K → (M.contract C).Dep K
参数：M.contract C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.exists_isBasis`：exists_isBasis (M : Matroid α) (X : Set α) (hX :
 X subseteq M.E
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.contract_inter_ground_eq`：∀ {α : Type u_1} (M : Matroid α) (C : 
Set α), M.contract (C ∩ M.E) = M.contract C
· 使用定理 `Matroid.Dep.eq_1`：∀ {α : Type u_1} (M : Matroid α) (D : Set α), M.Dep D 
= (¬M.Indep D ∧ D ⊆ M.E)
· 使用定理 `Matroid.IsBasis.contract_indep_iff`：∀ {α : Type u_1} {M : Matroid α} {I 
J X : Set α},   M.IsBasis I X → ((M.contract X).Indep J ↔ M.Indep (J ∪ I) ∧ Disj
oint X J)
· 使用定理 `and_iff_left`：∀ {b a : Prop}, b → (a ∧ b ↔ a)
· 使用定理 `Disjoint.mono_left`：Disjoint.mono_left (h : a <= b) : Disjoint b c -> Di
sjoint a c
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Matroid.contract_ground`：∀ {α : Type u_1} (M : Matroid α) (C : Set α), (
M.contract C).E = M.E \ C
· 使用引理 `Set.subset_sdiff`：subset_sdiff : s subseteq t \ u ↔ s subseteq t ∧ Disjo
int s u
· 使用定理 `Disjoint.mono_right`：Disjoint.mono_right (h : b <= c) : Disjoint a c -> 
Disjoint a b
· 使用定理 `Disjoint.symm`：Disjoint.symm (x y : Finmap β) (h : Disjoint x y) : Disjo
int y x
· 使用定理 `Matroid.IsCircuit.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {C : S
et α}, M.IsCircuit C → C ⊆ M.E
· 使用定理 `Matroid.Dep.not_indep`：∀ {α : Type u_1} {M : Matroid α} {D : Set α}, M.D
ep D → ¬M.Indep D
· 使用定理 `Matroid.IsCircuit.dep`：∀ {α : Type u_1} {M : Matroid α} {C : Set α}, M.I
sCircuit C → M.Dep C
· 使用定理 `Matroid.Indep.subset`：∀ {α : Type u_1} {M : Matroid α} {I J : Set α}, M.
Indep J → I ⊆ J → M.Indep I
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
-/
lemma IsCircuit.contract_dep (hK : M.IsCircuit K) (hCK : Disjoint C K) : (M ／ C).Dep K := by
  obtain ⟨I, hI⟩ := M.exists_isBasis (C ∩ M.E)
  rw [← contract_inter_ground_eq, Dep, hI.contract_indep_iff,
    and_iff_left (hCK.mono_left inter_subset_left), contract_ground, subset_sdiff,
    and_iff_left (hCK.symm.mono_right inter_subset_left), and_iff_left hK.subset_ground]
  exact fun hi ↦ hK.dep.not_indep (hi.subset subset_union_left)
/-
**Matroid.IsCircuit.contract_dep_of_not_subset** 是 Mathlib 中的一个定理，位于命名空间 `Matroi
d.IsCircuit`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {K : Set α}, M.IsCircuit K → ∀ {C : Set α
}, ¬K ⊆ C → (M.contract C).Dep (K \ C)
参数：M.contract C；K \ C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsCircuit.contract_isCircuit`：∀ {α : Type u_1} {M : Matroid α} {
K C : Set α}, M.IsCircuit K → C ⊂ K → (M.contract C).IsCircuit (K \ C)
· 使用定理 `LE.le.ssubset_of_ne`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst 
: PartialOrder α] {a b : α}, a ⊆ b → a ≠ b → a ⊂ b
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.IsCircuit.contract_dep`：∀ {α : Type u_1} {M : Matroid α} {K C : 
Set α}, M.IsCircuit K → Disjoint C K → (M.contract C).Dep K
· 使用定理 `Set.sdiff_inter_self_eq_sdiff`：sdiff_inter_self_eq_sdiff {s t : Set α} :
 s \ (t inter s) = s \ t
· 使用定理 `disjoint_sdiff_sdiff`：disjoint_sdiff_sdiff : Disjoint (x \ y) (y \ x)
· 使用定理 `Set.inter_union_sdiff`：inter_union_sdiff (s t : Set α) : s inter t union
 s \ t = s
· 使用引理 `Matroid.contract_contract`：contract_contract (M : Matroid α) (C₁ C₂ : Se
t α) : M ／ C₁ ／ C₂ = M ／ (C₁ union C₂)
-/
lemma IsCircuit.contract_dep_of_not_subset (hK : M.IsCircuit K) {C : Set α} (hKC : ¬ K ⊆ C) :
    (M ／ C).Dep (K \ C) := by
  have h' := hK.contract_isCircuit (C := C ∩ K) (inter_subset_right.ssubset_of_ne (by simpa))
  simp only [sdiff_inter_self_eq_sdiff] at h'
  have hwin := h'.contract_dep (C := C \ K) disjoint_sdiff_sdiff
  rwa [contract_contract, inter_union_sdiff] at hwin
/-
**Matroid.IsCircuit.contract_sdiff_isCircuit** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.
IsCircuit`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {K C : Set α}, M.IsCircuit C → K.Nonempty
 → K ⊆ C → (M.contract (C \ K)).IsCircuit K
参数：M.contract (C \ K)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sdiff_sdiff_right_self`：sdiff_sdiff_right_self : x \ (x \ y) = x ⊓ y
· 使用定理 `Set.inter_eq_self_of_subset_right`：inter_eq_self_of_subset_right {s t : 
Set α} : t subseteq s -> s inter t = t
· 使用定理 `Matroid.IsCircuit.contract_isCircuit`：∀ {α : Type u_1} {M : Matroid α} {
K C : Set α}, M.IsCircuit K → C ⊂ K → (M.contract C).IsCircuit (K \ C)
· 使用引理 `Set.sdiff_ssubset_left_iff`：sdiff_ssubset_left_iff : s \ t ⊂ s ↔ (s inte
r t).Nonempty
-/
lemma IsCircuit.contract_sdiff_isCircuit (hC : M.IsCircuit C) (hK : K.Nonempty) (hKC : K ⊆ C) :
    (M ／ (C \ K)).IsCircuit K := by
  simpa [inter_eq_self_of_subset_right hKC] using hC.contract_isCircuit (C := C \ K) <|
    by rwa [sdiff_ssubset_left_iff, inter_eq_self_of_subset_right hKC]

@[deprecated (since := "2026-06-03")]
alias IsCircuit.contract_diff_isCircuit := IsCircuit.contract_sdiff_isCircuit

/-- If `C` is a circuit of `M ／ K`, then `M` has a circuit in the interval `[C, C ∪ K]`. -/
/-
**Matroid.IsCircuit.exists_subset_isCircuit_of_contract** 是 Mathlib 中的一个定理，位于命名空
间 `Matroid.IsCircuit`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {K C : Set α}, (M.contract K).IsCircuit C
 → ∃ C', M.IsCircuit C' ∧ C ⊆ C' ∧ C' ⊆ C ∪ K
参数：M.contract K。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Set.subset_sdiff`：subset_sdiff : s subseteq t \ u ↔ s subseteq t ∧ Disjo
int s u
· 使用定理 `Matroid.IsCircuit.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {C : S
et α}, M.IsCircuit C → C ⊆ M.E
· 使用定理 `Matroid.Dep.exists_isCircuit_subset`：∀ {α : Type u_1} {M : Matroid α} {X
 : Set α}, M.Dep X → ∃ C ⊆ X, M.IsCircuit C
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Matroid.Indep.contract_dep_iff`：∀ {α : Type u_1} {M : Matroid α} {I J : 
Set α}, M.Indep I → ((M.contract I).Dep J ↔ Disjoint J I ∧ M.Dep (J ∪ I))
· 使用定理 `Matroid.IsCircuit.dep`：∀ {α : Type u_1} {M : Matroid α} {C : Set α}, M.I
sCircuit C → M.Dep C
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_iff_right`：∀ {a b : Prop}, a → (a ∧ b ↔ b)
· 使用引理 `Set.disjoint_sdiff_left`：disjoint_sdiff_left : Disjoint (t \ s) s
· 使用定理 `Matroid.Dep.superset`：∀ {α : Type u_1} {M : Matroid α} {D X : Set α},   
M.Dep D → D ⊆ X → autoParam (X ⊆ M.E) Matroid.Dep.superset._auto_1 → M.Dep X
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.sdiff_union_self`：sdiff_union_self {s t : Set α} : s \ t union t = s
 union t
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matroid.Indep.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {I : Set α
}, M.Indep I → I ⊆ M.E
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.IsCircuit.eq_of_dep_subset`：∀ {α : Type u_1} {M : Matroid α} {C 
X : Set α}, M.IsCircuit C → M.Dep X → X ⊆ C → X = C
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.sdiff_subset_iff`：sdiff_subset_iff {s t u : Set α} : s \ t subseteq 
u ↔ s subseteq t union u
· 使用定理 `Set.union_comm`：union_comm (a b : Set α) : a union b = b union a
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
· 使用定理 `Matroid.exists_isBasis'`：exists_isBasis' (M : Matroid α) (X : Set α) : e
xists I, M.IsBasis' I X
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `Matroid.delete_isCircuit_iff`：delete_isCircuit_iff {C : Set α} : (M ＼ D)
.IsCircuit C ↔ M.IsCircuit C ∧ Disjoint C D
· 使用定理 `Matroid.IsBasis'.contract_eq_contract_delete`：∀ {α : Type u_1} {M : Matr
oid α} {I X : Set α}, M.IsBasis' I X → M.contract X = (M.contract I).delete (X \
 I)
· 使用定理 `Matroid.IsBasis'.indep`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, 
M.IsBasis' I X → M.Indep I
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.union_subset_union_right`：union_subset_union_right (s) {t₁ t₂ : Set 
α} (h : t₁ subseteq t₂) : s union t₁ subseteq s union t₂
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
If `C` is a circuit of `M ／ K`, then `M` has a circuit in the interval `[C, C ∪ 
K]`.
-/
lemma IsCircuit.exists_subset_isCircuit_of_contract (hC : (M ／ K).IsCircuit C) :
    ∃ C', M.IsCircuit C' ∧ C ⊆ C' ∧ C' ⊆ C ∪ K := by
  wlog hKi : M.Indep K generalizing K with aux
  · obtain ⟨I, hI⟩ := M.exists_isBasis' K
    rw [hI.contract_eq_contract_delete, delete_isCircuit_iff] at hC
    obtain ⟨C', hC', hCC', hC'ss⟩ := aux hC.1 hI.indep
    exact ⟨C', hC', hCC', hC'ss.trans (union_subset_union_right _ hI.subset)⟩
  obtain ⟨hCE : C ⊆ M.E, hCK : Disjoint C K⟩ := subset_sdiff.1 hC.subset_ground
  obtain ⟨C', hC'ss, hC'⟩ := (hKi.contract_dep_iff.1 hC.dep).2.exists_isCircuit_subset
  refine ⟨C', hC', ?_, hC'ss⟩
  have hdep2 : (M ／ K).Dep (C' \ K) := by
    rw [hKi.contract_dep_iff, and_iff_right disjoint_sdiff_left]
    refine hC'.dep.superset (by simp)
  rw [← (hC.eq_of_dep_subset hdep2 (sdiff_subset_iff.2 (union_comm _ _ ▸ hC'ss)))]
  exact sdiff_subset
/-
**Matroid.IsCocircuit.of_contract** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsCocircuit
`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {K C : Set α}, (M.contract C).IsCocircuit
 K → M.IsCocircuit K
参数：M.contract C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsCircuit.of_delete`：∀ {α : Type u_1} {M : Matroid α} {D C : Set
 α}, (M.delete D).IsCircuit C → M.IsCircuit C
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matroid.dual_contract`：dual_contract (M : Matroid α) (X : Set α) : (M ／ 
X)✶ = M✶ ＼ X
· 使用引理 `Matroid.isCocircuit_def`：isCocircuit_def : M.IsCocircuit K ↔ M✶.IsCircui
t K
-/
lemma IsCocircuit.of_contract (hK : (M ／ C).IsCocircuit K) : M.IsCocircuit K := by
  rw [isCocircuit_def, dual_contract] at hK
  exact hK.of_delete
/-
**Matroid.IsCocircuit.delete_isCocircuit** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsCo
circuit`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {K D : Set α}, M.IsCocircuit K → D ⊂ K → 
(M.delete D).IsCocircuit (K \ D)
参数：M.delete D；K \ D。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matroid.isCocircuit_def`：isCocircuit_def : M.IsCocircuit K ↔ M✶.IsCircui
t K
· 使用引理 `Matroid.dual_delete`：dual_delete (M : Matroid α) (X : Set α) : (M ＼ X)✶ 
= M✶ ／ X
· 使用定理 `Matroid.IsCircuit.contract_isCircuit`：∀ {α : Type u_1} {M : Matroid α} {
K C : Set α}, M.IsCircuit K → C ⊂ K → (M.contract C).IsCircuit (K \ C)
· 使用定理 `Matroid.IsCocircuit.isCircuit`：∀ {α : Type u_1} {M : Matroid α} {K : Set
 α}, M.IsCocircuit K → M✶.IsCircuit K
-/
lemma IsCocircuit.delete_isCocircuit {D : Set α} (hK : M.IsCocircuit K) (hD : D ⊂ K) :
    (M ＼ D).IsCocircuit (K \ D) := by
  rw [isCocircuit_def, dual_delete]
  exact hK.isCircuit.contract_isCircuit hD
/-
**Matroid.IsCocircuit.delete_sdiff_isCocircuit** 是 Mathlib 中的一个定理，位于命名空间 `Matroi
d.IsCocircuit`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {K X : Set α}, M.IsCocircuit K → X ⊆ K → 
X.Nonempty → (M.delete (K \ X)).IsCocircuit X
参数：M.delete (K \ X)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matroid.isCocircuit_def`：isCocircuit_def : M.IsCocircuit K ↔ M✶.IsCircui
t K
· 使用引理 `Matroid.dual_delete`：dual_delete (M : Matroid α) (X : Set α) : (M ＼ X)✶ 
= M✶ ／ X
· 使用定理 `Matroid.IsCircuit.contract_sdiff_isCircuit`：∀ {α : Type u_1} {M : Matroi
d α} {K C : Set α}, M.IsCircuit C → K.Nonempty → K ⊆ C → (M.contract (C \ K)).Is
Circuit K
· 使用定理 `Matroid.IsCocircuit.isCircuit`：∀ {α : Type u_1} {M : Matroid α} {K : Set
 α}, M.IsCocircuit K → M✶.IsCircuit K
-/
lemma IsCocircuit.delete_sdiff_isCocircuit {X : Set α} (hK : M.IsCocircuit K) (hXK : X ⊆ K)
    (hX : X.Nonempty) : (M ＼ (K \ X)).IsCocircuit X := by
  rw [isCocircuit_def, dual_delete]
  exact hK.isCircuit.contract_sdiff_isCircuit hX hXK

@[deprecated (since := "2026-06-03")]
alias IsCocircuit.delete_diff_isCocircuit := IsCocircuit.delete_sdiff_isCocircuit

/-! ### Commutativity -/

/-
**Matroid.contract_delete_sdiff** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：contract_delete_sdiff (M : Matroid α) (C D : Set α) : M ／ C ＼ D = M ／ C ＼ 
(D \ C)
参数：M : Matroid α；C D : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matroid.delete_eq_delete_iff`：delete_eq_delete_iff {D₁ D₂ : Set α} : M ＼
 D₁ = M ＼ D₂ ↔ D₁ inter M.E = D₂ inter M.E
· 使用定理 `Matroid.contract_ground`：∀ {α : Type u_1} (M : Matroid α) (C : Set α), (
M.contract C).E = M.E \ C
· 使用定理 `Set.sdiff_eq`：sdiff_eq (s t : Set α) : s \ t = s inter tᶜ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.inter_inter_distrib_right`：inter_inter_distrib_right (s t u : Set α)
 : s inter t inter u = s inter u inter (t inter u)
· 使用定理 `Set.inter_assoc`：inter_assoc (a b c : Set α) : a inter b inter c = a int
er (b inter c)

--- 原说明 ---
### Commutativity
-/
lemma contract_delete_sdiff (M : Matroid α) (C D : Set α) : M ／ C ＼ D = M ／ C ＼ (D \ C) := by
  rw [delete_eq_delete_iff, contract_ground, sdiff_eq, sdiff_eq, ← inter_inter_distrib_right,
    inter_assoc]

@[deprecated (since := "2026-06-03")] alias contract_delete_diff := contract_delete_sdiff
/-
**Matroid.contract_restrict_eq_restrict_contract** 是 Mathlib 中的一个引理，位于命名空间 `Matr
oid`。
形式化陈述：contract_restrict_eq_restrict_contract (M : Matroid α) (h : Disjoint C R) 
: (M ／ C) ↾ R = (M ↾ (R union C)) ／ C
参数：M : Matroid α；h : Disjoint C R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.ext_indep`：∀ {α : Type u_1} {M₁ M₂ : Matroid α}, M₁.E = M₂.E → (
∀ ⦃I : Set α⦄, I ⊆ M₁.E → (M₁.Indep I ↔ M₂.Indep I)) → M₁ = M₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.union_sdiff_right`：union_sdiff_right {s t : Set α} : (s union t) \ t
 = s \ t
· 使用定理 `Disjoint.sdiff_eq_right`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAl
gebra α] {a b : α}, Disjoint a b → b \ a = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Matroid.exists_isBasis'`：exists_isBasis' (M : Matroid α) (X : Set α) : e
xists I, M.IsBasis' I X
· 使用定理 `Set.inter_eq_self_of_subset_left`：inter_eq_self_of_subset_left {s t : Se
t α} : s subseteq t -> s inter t = s
· 使用定理 `Set.subset_union_right`：subset_union_right {s t : Set α} : t subseteq s 
union t
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Matroid.isBasis'_restrict_iff`：∀ {α : Type u_1} {M : Matroid α} {R I X :
 Set α}, (M.restrict R).IsBasis' I X ↔ M.IsBasis' I (X ∩ R) ∧ I ⊆ R
· 使用定理 `Matroid.restrict_indep_iff`：∀ {α : Type u_1} {M : Matroid α} {R I : Set 
α}, (M.restrict R).Indep I ↔ M.Indep I ∧ I ⊆ R
· 使用定理 `Matroid.IsBasis'.contract_indep_iff`：∀ {α : Type u_1} {M : Matroid α} {I
 J X : Set α},   M.IsBasis' I X → ((M.contract X).Indep J ↔ M.Indep (J ∪ I) ∧ Di
sjoint X J)
· 使用定理 `Matroid.IsBasis'.subset`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α},
 M.IsBasis' I X → I ⊆ X
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
-/
lemma contract_restrict_eq_restrict_contract (M : Matroid α) (h : Disjoint C R) :
    (M ／ C) ↾ R = (M ↾ (R ∪ C)) ／ C := by
  refine ext_indep (by simp [h.sdiff_eq_right]) fun I (hI : I ⊆ R) ↦ ?_
  obtain ⟨J, hJ⟩ := (M ↾ (R ∪ C)).exists_isBasis' C
  have hJ' : M.IsBasis' J C := by
    simpa [inter_eq_self_of_subset_left subset_union_right] using (isBasis'_restrict_iff.1 hJ).1
  rw [restrict_indep_iff, hJ.contract_indep_iff, hJ'.contract_indep_iff, restrict_indep_iff]
  have hJC := hJ'.subset
  tauto_set
/-
**Matroid.restrict_contract_eq_contract_restrict** 是 Mathlib 中的一个引理，位于命名空间 `Matr
oid`。
形式化陈述：restrict_contract_eq_contract_restrict (M : Matroid α) (hCR : C subseteq R
) : (M ↾ R) ／ C = (M ／ C) ↾ (R \ C)
参数：M : Matroid α；hCR : C subseteq R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matroid.contract_restrict_eq_restrict_contract`：contract_restrict_eq_res
trict_contract (M : Matroid α) (h : Disjoint C R) : (M ／ C) ↾ R = (M ↾ (R union 
C)) ／ C
· 使用引理 `Set.disjoint_sdiff_right`：disjoint_sdiff_right : Disjoint s (t \ s)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.sdiff_union_self`：sdiff_union_self {s t : Set α} : s \ t union t = s
 union t
· 使用定理 `Set.union_eq_self_of_subset_right`：union_eq_self_of_subset_right {s t : 
Set α} (h : t subseteq s) : s union t = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma restrict_contract_eq_contract_restrict (M : Matroid α) (hCR : C ⊆ R) :
    (M ↾ R) ／ C = (M ／ C) ↾ (R \ C) := by
  rw [contract_restrict_eq_restrict_contract _ disjoint_sdiff_right]
  simp [union_eq_self_of_subset_right hCR]

/-- Contraction and deletion commute for disjoint sets. -/
/-
**Matroid.contract_delete_comm** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：contract_delete_comm (M : Matroid α) (hCD : Disjoint C D) : M ／ C ＼ D = M 
＼ D ／ C
参数：M : Matroid α；hCD : Disjoint C D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matroid.delete_eq_restrict`：delete_eq_restrict (M : Matroid α) (D : Set 
α) : M ＼ D = M ↾ (M.E \ D)
· 使用定理 `Matroid.contract_ground`：∀ {α : Type u_1} (M : Matroid α) (C : Set α), (
M.contract C).E = M.E \ C
· 使用定理 `Set.sdiff_sdiff_comm`：sdiff_sdiff_comm {s t u : Set α} : (s \ t) \ u = (
s \ u) \ t
· 使用引理 `Matroid.restrict_contract_eq_contract_restrict`：restrict_contract_eq_con
tract_restrict (M : Matroid α) (hCR : C subseteq R) : (M ↾ R) ／ C = (M ／ C) ↾ (R
 \ C)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.contract_inter_ground_eq`：∀ {α : Type u_1} (M : Matroid α) (C : 
Set α), M.contract (C ∩ M.E) = M.contract C
· 使用定理 `Disjoint.mono_left`：Disjoint.mono_left (h : a <= b) : Disjoint b c -> Di
sjoint a c
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用引理 `Matroid.contract_eq_contract_iff`：contract_eq_contract_iff : M ／ C₁ = M 
／ C₂ ↔ C₁ inter M.E = C₂ inter M.E
· 使用定理 `Set.inter_assoc`：inter_assoc (a b c : Set α) : a inter b inter c = a int
er (b inter c)
· 使用引理 `Matroid.delete_ground`：delete_ground (M : Matroid α) (D : Set α) : (M ＼ 
D).E = M.E \ D
· 使用定理 `Set.inter_eq_self_of_subset_right`：inter_eq_self_of_subset_right {s t : 
Set α} : t subseteq s -> s inter t = t
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s

--- 原说明 ---
Contraction and deletion commute for disjoint sets.
-/
lemma contract_delete_comm (M : Matroid α) (hCD : Disjoint C D) : M ／ C ＼ D = M ＼ D ／ C := by
  wlog hCE : C ⊆ M.E generalizing C with aux
  · rw [← contract_inter_ground_eq, aux (hCD.mono_left inter_subset_left) inter_subset_right,
      contract_eq_contract_iff, inter_assoc, delete_ground,
      inter_eq_self_of_subset_right sdiff_subset]
  rw [delete_eq_restrict, delete_eq_restrict, contract_ground, sdiff_sdiff_comm,
    restrict_contract_eq_contract_restrict _ (by simpa [hCE, subset_sdiff])]

/-- A version of `contract_delete_comm` without the disjointness hypothesis,
and hence a less simple RHS. -/
/-
**Matroid.contract_delete_comm'** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：contract_delete_comm' (M : Matroid α) (C D : Set α) : M ／ C ＼ D = M ＼ (D \
 C) ／ C
参数：M : Matroid α；C D : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matroid.contract_delete_sdiff`：contract_delete_sdiff (M : Matroid α) (C 
D : Set α) : M ／ C ＼ D = M ／ C ＼ (D \ C)
· 使用引理 `Matroid.contract_delete_comm`：contract_delete_comm (M : Matroid α) (hCD 
: Disjoint C D) : M ／ C ＼ D = M ＼ D ／ C
· 使用引理 `Set.disjoint_sdiff_right`：disjoint_sdiff_right : Disjoint s (t \ s)

--- 原说明 ---
A version of `contract_delete_comm` without the disjointness hypothesis,
and hence a less simple RHS.
-/
lemma contract_delete_comm' (M : Matroid α) (C D : Set α) : M ／ C ＼ D = M ＼ (D \ C) ／ C := by
  rw [contract_delete_sdiff, contract_delete_comm _ disjoint_sdiff_right]
/-
**Matroid.delete_contract_eq_sdiff** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：delete_contract_eq_sdiff (M : Matroid α) (D C : Set α) : M ＼ D ／ C = M ＼ D
 ／ (C \ D)
参数：M : Matroid α；D C : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matroid.contract_eq_contract_iff`：contract_eq_contract_iff : M ／ C₁ = M 
／ C₂ ↔ C₁ inter M.E = C₂ inter M.E
· 使用引理 `Matroid.delete_ground`：delete_ground (M : Matroid α) (D : Set α) : (M ＼ 
D).E = M.E \ D
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.sdiff_inter_distrib_right`：sdiff_inter_distrib_right (s t r : Set α)
 : (t inter r) \ s = (t \ s) inter (r \ s)
· 使用定理 `Set.sdiff_eq`：sdiff_eq (s t : Set α) : s \ t = s inter tᶜ
· 使用定理 `Set.inter_assoc`：inter_assoc (a b c : Set α) : a inter b inter c = a int
er (b inter c)
-/
lemma delete_contract_eq_sdiff (M : Matroid α) (D C : Set α) : M ＼ D ／ C = M ＼ D ／ (C \ D) := by
  rw [contract_eq_contract_iff, delete_ground, ← sdiff_inter_distrib_right, sdiff_eq, sdiff_eq,
    inter_assoc]

@[deprecated (since := "2026-06-03")] alias delete_contract_eq_diff := delete_contract_eq_sdiff

/-- A version of `delete_contract_comm'` without the disjointness hypothesis,
and hence a less simple RHS. -/
/-
**Matroid.delete_contract_comm'** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：delete_contract_comm' (M : Matroid α) (D C : Set α) : M ＼ D ／ C = M ／ (C \
 D) ＼ D
参数：M : Matroid α；D C : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matroid.delete_contract_eq_sdiff`：delete_contract_eq_sdiff (M : Matroid 
α) (D C : Set α) : M ＼ D ／ C = M ＼ D ／ (C \ D)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Matroid.contract_delete_comm`：contract_delete_comm (M : Matroid α) (hCD 
: Disjoint C D) : M ／ C ＼ D = M ＼ D ／ C
· 使用引理 `Set.disjoint_sdiff_left`：disjoint_sdiff_left : Disjoint (t \ s) s

--- 原说明 ---
A version of `delete_contract_comm'` without the disjointness hypothesis,
and hence a less simple RHS.
-/
lemma delete_contract_comm' (M : Matroid α) (D C : Set α) : M ＼ D ／ C = M ／ (C \ D) ＼ D := by
  rw [delete_contract_eq_sdiff, ← contract_delete_comm _ disjoint_sdiff_left]

/-- A version of `contract_delete_contract` without the disjointness hypothesis,
and hence a less simple RHS. -/
/-
**Matroid.contract_delete_contract'** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：contract_delete_contract' (M : Matroid α) (C D C' : Set α) : M ／ C ＼ D ／ C
' = M ／ (C union C' \ D) ＼ D
参数：M : Matroid α；C D C' : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matroid.delete_contract_eq_sdiff`：delete_contract_eq_sdiff (M : Matroid 
α) (D C : Set α) : M ＼ D ／ C = M ＼ D ／ (C \ D)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Matroid.contract_delete_comm`：contract_delete_comm (M : Matroid α) (hCD 
: Disjoint C D) : M ／ C ＼ D = M ＼ D ／ C
· 使用引理 `Set.disjoint_sdiff_left`：disjoint_sdiff_left : Disjoint (t \ s) s
· 使用引理 `Matroid.contract_contract`：contract_contract (M : Matroid α) (C₁ C₂ : Se
t α) : M ／ C₁ ／ C₂ = M ／ (C₁ union C₂)

--- 原说明 ---
A version of `contract_delete_contract` without the disjointness hypothesis,
and hence a less simple RHS.
-/
lemma contract_delete_contract' (M : Matroid α) (C D C' : Set α) :
    M ／ C ＼ D ／ C' = M ／ (C ∪ C' \ D) ＼ D := by
  rw [delete_contract_eq_sdiff, ← contract_delete_comm _ disjoint_sdiff_left, contract_contract]
/-
**Matroid.contract_delete_contract** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：contract_delete_contract (M : Matroid α) (C D C' : Set α) (h : Disjoint C'
 D) : M ／ C ＼ D ／ C' = M ／ (C union C') ＼ D
参数：M : Matroid α；C D C' : Set α；h : Disjoint C' D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matroid.contract_delete_contract'`：contract_delete_contract' (M : Matroi
d α) (C D C' : Set α) : M ／ C ＼ D ／ C' = M ／ (C union C' \ D) ＼ D
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sdiff_eq_left`：∀ {α : Type u} {x y : α} [inst : GeneralizedBooleanAlgebr
a α], x \ y = x ↔ Disjoint x y
-/
lemma contract_delete_contract (M : Matroid α) (C D C' : Set α) (h : Disjoint C' D) :
    M ／ C ＼ D ／ C' = M ／ (C ∪ C') ＼ D := by rw [contract_delete_contract', sdiff_eq_left.mpr h]

/-- A version of `contract_delete_contract_delete` without the disjointness hypothesis,
and hence a less simple RHS. -/
/-
**Matroid.contract_delete_contract_delete'** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：contract_delete_contract_delete' (M : Matroid α) (C D C' D' : Set α) : M ／
 C ＼ D ／ C' ＼ D' = M ／ (C union C' \ D) ＼ (D union D')
参数：M : Matroid α；C D C' D' : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matroid.contract_delete_contract'`：contract_delete_contract' (M : Matroi
d α) (C D C' : Set α) : M ／ C ＼ D ／ C' = M ／ (C union C' \ D) ＼ D
· 使用引理 `Matroid.delete_delete`：delete_delete (M : Matroid α) (D₁ D₂ : Set α) : M
 ＼ D₁ ＼ D₂ = M ＼ (D₁ union D₂)

--- 原说明 ---
A version of `contract_delete_contract_delete` without the disjointness hypothes
is,
and hence a less simple RHS.
-/
lemma contract_delete_contract_delete' (M : Matroid α) (C D C' D' : Set α) :
    M ／ C ＼ D ／ C' ＼ D' = M ／ (C ∪ C' \ D) ＼ (D ∪ D') := by
  rw [contract_delete_contract', delete_delete]
/-
**Matroid.contract_delete_contract_delete** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：contract_delete_contract_delete (M : Matroid α) (C D C' D' : Set α) (h : D
isjoint C' D) : M ／ C ＼ D ／ C' ＼ D' = M ／ (C union C') ＼ (D union D')
参数：M : Matroid α；C D C' D' : Set α；h : Disjoint C' D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matroid.contract_delete_contract_delete'`：contract_delete_contract_delet
e' (M : Matroid α) (C D C' D' : Set α) : M ／ C ＼ D ／ C' ＼ D' = M ／ (C union C' \
 D) ＼ (D union D')
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sdiff_eq_left`：∀ {α : Type u} {x y : α} [inst : GeneralizedBooleanAlgebr
a α], x \ y = x ↔ Disjoint x y
-/
lemma contract_delete_contract_delete (M : Matroid α) (C D C' D' : Set α) (h : Disjoint C' D) :
    M ／ C ＼ D ／ C' ＼ D' = M ／ (C ∪ C') ＼ (D ∪ D') := by
  rw [contract_delete_contract_delete', sdiff_eq_left.mpr h]

/-- A version of `delete_contract_delete` without the disjointness hypothesis,
and hence a less simple RHS. -/
/-
**Matroid.delete_contract_delete'** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：delete_contract_delete' (M : Matroid α) (D C D' : Set α) : M ＼ D ／ C ＼ D' 
= M ／ (C \ D) ＼ (D union D')
参数：M : Matroid α；D C D' : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matroid.delete_contract_comm'`：delete_contract_comm' (M : Matroid α) (D 
C : Set α) : M ＼ D ／ C = M ／ (C \ D) ＼ D
· 使用引理 `Matroid.delete_delete`：delete_delete (M : Matroid α) (D₁ D₂ : Set α) : M
 ＼ D₁ ＼ D₂ = M ＼ (D₁ union D₂)

--- 原说明 ---
A version of `delete_contract_delete` without the disjointness hypothesis,
and hence a less simple RHS.
-/
lemma delete_contract_delete' (M : Matroid α) (D C D' : Set α) :
    M ＼ D ／ C ＼ D' = M ／ (C \ D) ＼ (D ∪ D') := by
  rw [delete_contract_comm', delete_delete]
/-
**Matroid.delete_contract_delete** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：delete_contract_delete (M : Matroid α) (D C D' : Set α) (h : Disjoint C D)
 : M ＼ D ／ C ＼ D' = M ／ C ＼ (D union D')
参数：M : Matroid α；D C D' : Set α；h : Disjoint C D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matroid.delete_contract_delete'`：delete_contract_delete' (M : Matroid α)
 (D C D' : Set α) : M ＼ D ／ C ＼ D' = M ／ (C \ D) ＼ (D union D')
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sdiff_eq_left`：∀ {α : Type u} {x y : α} [inst : GeneralizedBooleanAlgebr
a α], x \ y = x ↔ Disjoint x y
-/
lemma delete_contract_delete (M : Matroid α) (D C D' : Set α) (h : Disjoint C D) :
    M ＼ D ／ C ＼ D' = M ／ C ＼ (D ∪ D') := by
  rw [delete_contract_delete', sdiff_eq_left.mpr h]

end Contract

end Matroid

