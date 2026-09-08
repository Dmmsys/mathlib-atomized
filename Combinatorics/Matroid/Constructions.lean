/-
Copyright (c) 2024 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson
-/
module

public import Mathlib.Combinatorics.Matroid.Minor.Restrict

/-!
# Some constructions of matroids

This file defines some very elementary examples of matroids, namely those with at most one base.

## Main definitions

* `emptyOn α` is the matroid on `α` with empty ground set.

For `E : Set α`, ...

* `loopyOn E` is the matroid on `E` whose elements are all loops, or equivalently in which `∅`
  is the only base.
* `freeOn E` is the 'free matroid' whose ground set `E` is the only base.
* For `I ⊆ E`, `uniqueBaseOn I E` is the matroid with ground set `E` in which `I` is the only base.

## Implementation details

To avoid the tedious process of certifying the matroid axioms for each of these easy examples,
we bootstrap the definitions starting with `emptyOn α` (which `simp` can prove is a matroid)
and then construct the other examples using duality and restriction.

-/

@[expose] public section

assert_not_exists Field

variable {α : Type*} {M : Matroid α} {E B I X R J : Set α}

namespace Matroid

open Set

section EmptyOn

/-- The `Matroid α` with empty ground set. -/
/-
**Matroid.emptyOn** 是 Mathlib 中的一个定义，位于命名空间 `Matroid`。
形式化陈述：emptyOn (α : Type*) : Matroid α where E
参数：α : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `Matroid α` with empty ground set.
-/
def emptyOn (α : Type*) : Matroid α where
  E := ∅
  IsBase := (· = ∅)
  Indep := (· = ∅)
  indep_iff' := by simp [subset_empty_iff]
  exists_isBase := ⟨∅, rfl⟩
  isBase_exchange := by rintro _ _ rfl; simp
  maximality := by rintro _ _ _ rfl -; exact ⟨∅, by simp [Maximal]⟩
  subset_ground := by simp
/-
**Matroid.emptyOn_ground** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_1}, (Matroid.emptyOn α).E = ∅
参数：Matroid.emptyOn α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem emptyOn_ground : (emptyOn α).E = ∅ := rfl
/-
**Matroid.emptyOn_isBase_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_1} {B : Set α}, (Matroid.emptyOn α).IsBase B ↔ B = ∅
参数：Matroid.emptyOn α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] theorem emptyOn_isBase_iff : (emptyOn α).IsBase B ↔ B = ∅ := Iff.rfl
/-
**Matroid.emptyOn_indep_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_1} {I : Set α}, (Matroid.emptyOn α).Indep I ↔ I = ∅
参数：Matroid.emptyOn α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] theorem emptyOn_indep_iff : (emptyOn α).Indep I ↔ I = ∅ := Iff.rfl
/-
**Matroid.ground_eq_empty_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：ground_eq_empty_iff : (M.E = ∅) ↔ M = emptyOn α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem ground_eq_empty_iff : (M.E = ∅) ↔ M = emptyOn α := by
  simp only [emptyOn, ext_iff_indep, iff_self_and]
  exact fun h ↦ by simp [h, subset_empty_iff]
/-
**Matroid.emptyOn_dual_eq** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_1}, (Matroid.emptyOn α)✶ = Matroid.emptyOn α
参数：Matroid.emptyOn α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.ground_eq_empty_iff`：ground_eq_empty_iff : (M.E = ∅) ↔ M = empty
On α
-/
@[simp] theorem emptyOn_dual_eq : (emptyOn α)✶ = emptyOn α := by
  rw [← ground_eq_empty_iff]; rfl
/-
**Matroid.restrict_empty** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_1} (M : Matroid α), M.restrict ∅ = Matroid.emptyOn α
参数：M : Matroid α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem restrict_empty (M : Matroid α) : M ↾ (∅ : Set α) = emptyOn α := by
  simp [← ground_eq_empty_iff]
/-
**Matroid.eq_emptyOn_or_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：eq_emptyOn_or_nonempty (M : Matroid α) : M = emptyOn α ∨ Matroid.Nonempty 
M
参数：M : Matroid α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.ground_eq_empty_iff`：ground_eq_empty_iff : (M.E = ∅) ↔ M = empty
On α
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
-/
theorem eq_emptyOn_or_nonempty (M : Matroid α) : M = emptyOn α ∨ Matroid.Nonempty M := by
  rw [← ground_eq_empty_iff]
  exact M.E.eq_empty_or_nonempty.elim Or.inl (fun h ↦ Or.inr ⟨h⟩)
/-
**Matroid.eq_emptyOn** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：eq_emptyOn [IsEmpty α] (M : Matroid α) : M = emptyOn α
参数：M : Matroid α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.ground_eq_empty_iff`：ground_eq_empty_iff : (M.E = ∅) ↔ M = empty
On α
· 使用引理 `Set.eq_empty_of_isEmpty`：eq_empty_of_isEmpty (s : Set α) [IsEmpty s] : s
 = ∅
· 使用定理 `instIsEmptySubtype`：∀ {α : Sort u} [IsEmpty α] (p : α → Prop), IsEmpty (
Subtype p)
-/
theorem eq_emptyOn [IsEmpty α] (M : Matroid α) : M = emptyOn α := by
  rw [← ground_eq_empty_iff]
  exact M.E.eq_empty_of_isEmpty
/-
**Matroid.finite_emptyOn** 是 Mathlib 中的一个实例，位于命名空间 `Matroid`。
形式化陈述：finite_emptyOn (α : Type*) : (emptyOn α).Finite
参数：α : Type*。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.finite_empty`：finite_empty : (∅ : Set α).Finite
-/
instance finite_emptyOn (α : Type*) : (emptyOn α).Finite :=
  ⟨finite_empty⟩

end EmptyOn

section LoopyOn

/-- The `Matroid α` with ground set `E` whose only base is `∅`.
The elements are all 'loops' - see `Matroid.IsLoop` and `Matroid.loopyOn_isLoop_iff`. -/
/-
**Matroid.loopyOn** 是 Mathlib 中的一个定义，位于命名空间 `Matroid`。
形式化陈述：loopyOn (E : Set α) : Matroid α
参数：E : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `Matroid α` with ground set `E` whose only base is `∅`.
The elements are all 'loops' - see `Matroid.IsLoop` and `Matroid.loopyOn_isLoop_
iff`.
-/
def loopyOn (E : Set α) : Matroid α := emptyOn α ↾ E
/-
**Matroid.loopyOn_ground** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_1} (E : Set α), (Matroid.loopyOn E).E = E
参数：E : Set α；Matroid.loopyOn E。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem loopyOn_ground (E : Set α) : (loopyOn E).E = E := rfl
/-
**Matroid.loopyOn_empty** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ (α : Type u_2), Matroid.loopyOn ∅ = Matroid.emptyOn α
参数：α : Type u_2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.ground_eq_empty_iff`：ground_eq_empty_iff : (M.E = ∅) ↔ M = empty
On α
· 使用定理 `Matroid.loopyOn_ground`：∀ {α : Type u_1} (E : Set α), (Matroid.loopyOn E
).E = E
-/
@[simp] theorem loopyOn_empty (α : Type*) : loopyOn (∅ : Set α) = emptyOn α := by
  rw [← ground_eq_empty_iff, loopyOn_ground]
/-
**Matroid.loopyOn_indep_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_1} {E I : Set α}, (Matroid.loopyOn E).Indep I ↔ I = ∅
参数：Matroid.loopyOn E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.empty_subset`：empty_subset (s : Set α) : ∅ subseteq s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
@[simp] theorem loopyOn_indep_iff : (loopyOn E).Indep I ↔ I = ∅ := by
  simp only [loopyOn, restrict_indep_iff, emptyOn_indep_iff, and_iff_left_iff_imp]
  rintro rfl; apply empty_subset
/-
**Matroid.eq_loopyOn_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：eq_loopyOn_iff : M = loopyOn E ↔ M.E = E ∧ forall X subseteq M.E, M.Indep 
X -> X = ∅
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem eq_loopyOn_iff : M = loopyOn E ↔ M.E = E ∧ ∀ X ⊆ M.E, M.Indep X → X = ∅ := by
  simp only [ext_iff_indep, loopyOn_ground, loopyOn_indep_iff, and_congr_right_iff]
  rintro rfl
  refine ⟨fun h I hI ↦ (h hI).1, fun h I hIE ↦ ⟨h I hIE, by rintro rfl; simp⟩⟩
/-
**Matroid.loopyOn_isBase_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_1} {E B : Set α}, (Matroid.loopyOn E).IsBase B ↔ B = ∅
参数：Matroid.loopyOn E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] theorem loopyOn_isBase_iff : (loopyOn E).IsBase B ↔ B = ∅ := by
  simp [Maximal, isBase_iff_maximal_indep]
/-
**Matroid.loopyOn_isBasis_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_1} {E I X : Set α}, (Matroid.loopyOn E).IsBasis I X ↔ I = ∅ 
∧ X ⊆ E
参数：Matroid.loopyOn E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Matroid.loopyOn_indep_iff`：∀ {α : Type u_1} {E I : Set α}, (Matroid.loop
yOn E).Indep I ↔ I = ∅
· 使用定理 `Matroid.IsBasis.indep`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, M
.IsBasis I X → M.Indep I
· 使用定理 `Matroid.IsBasis.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {I X : S
et α}, M.IsBasis I X → X ⊆ M.E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.isBasis_iff`：isBasis_iff (hX : X subseteq M.E
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
@[simp] theorem loopyOn_isBasis_iff : (loopyOn E).IsBasis I X ↔ I = ∅ ∧ X ⊆ E :=
  ⟨fun h ↦ ⟨loopyOn_indep_iff.mp h.indep, h.subset_ground⟩,
    by rintro ⟨rfl, hX⟩; rw [isBasis_iff]; simp⟩
/-
**Matroid.loopyOn_rankFinite** 是 Mathlib 中的一个实例，位于命名空间 `Matroid`。
形式化陈述：loopyOn_rankFinite : RankFinite (loopyOn E)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
instance loopyOn_rankFinite : RankFinite (loopyOn E) :=
  ⟨∅, by simp⟩
/-
**Matroid.Finite.loopyOn_finite** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Finite`。
形式化陈述：∀ {α : Type u_1} {E : Set α}, E.Finite → (Matroid.loopyOn E).Finite
参数：Matroid.loopyOn E。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Finite.loopyOn_finite (hE : E.Finite) : Matroid.Finite (loopyOn E) :=
  ⟨hE⟩
/-
**Matroid.loopyOn_restrict** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_1} (E R : Set α), (Matroid.loopyOn E).restrict R = Matroid.l
oopyOn R
参数：E R : Set α；Matroid.loopyOn E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.ext_indep`：∀ {α : Type u_1} {M₁ M₂ : Matroid α}, M₁.E = M₂.E → (
∀ ⦃I : Set α⦄, I ⊆ M₁.E → (M₁.Indep I ↔ M₂.Indep I)) → M₁ = M₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
@[simp] theorem loopyOn_restrict (E R : Set α) : (loopyOn E) ↾ R = loopyOn R := by
  refine ext_indep rfl ?_
  simp only [restrict_ground_eq, restrict_indep_iff, loopyOn_indep_iff, and_iff_left_iff_imp]
  exact fun _ h _ ↦ h
/-
**Matroid.empty_isBase_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：empty_isBase_iff : M.IsBase ∅ ↔ M = loopyOn M.E
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `true_implies`：∀ (p : Prop), (True → p) = p
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Matroid.Indep.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {I : Set α
}, M.Indep I → I ⊆ M.E
-/
theorem empty_isBase_iff : M.IsBase ∅ ↔ M = loopyOn M.E := by
  simp only [isBase_iff_maximal_indep, Maximal, empty_indep, empty_subset,
    subset_empty_iff, true_implies, true_and, ext_iff_indep, loopyOn_ground,
    loopyOn_indep_iff]
  exact ⟨fun h I _ ↦ ⟨@h _, fun hI ↦ by simp [hI]⟩, fun h I hI ↦ (h hI.subset_ground).1 hI⟩
/-
**Matroid.eq_loopyOn_or_rankPos** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：eq_loopyOn_or_rankPos (M : Matroid α) : M = loopyOn M.E ∨ RankPos M
参数：M : Matroid α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.empty_isBase_iff`：empty_isBase_iff : M.IsBase ∅ ↔ M = loopyOn M.
E
· 使用定理 `Matroid.rankPos_iff`：∀ {α : Type u_1} (M : Matroid α), M.RankPos ↔ ¬M.Is
Base ∅
· 使用定理 `em`：∀ (p : Prop), p ∨ ¬p
-/
theorem eq_loopyOn_or_rankPos (M : Matroid α) : M = loopyOn M.E ∨ RankPos M := by
  rw [← empty_isBase_iff, rankPos_iff]; apply em
/-
**Matroid.not_rankPos_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：not_rankPos_iff : ¬RankPos M ↔ M = loopyOn M.E
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.rankPos_iff`：∀ {α : Type u_1} (M : Matroid α), M.RankPos ↔ ¬M.Is
Base ∅
· 使用定理 `not_iff_comm`：not_iff_comm : (¬a ↔ b) ↔ (¬b ↔ a)
· 使用定理 `Matroid.empty_isBase_iff`：empty_isBase_iff : M.IsBase ∅ ↔ M = loopyOn M.
E
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem not_rankPos_iff : ¬RankPos M ↔ M = loopyOn M.E := by
  rw [rankPos_iff, not_iff_comm, empty_isBase_iff]

end LoopyOn

section FreeOn

/-- The `Matroid α` with ground set `E` whose only base is `E`. -/
/-
**Matroid.freeOn** 是 Mathlib 中的一个定义，位于命名空间 `Matroid`。
形式化陈述：freeOn (E : Set α) : Matroid α
参数：E : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `Matroid α` with ground set `E` whose only base is `E`.
-/
def freeOn (E : Set α) : Matroid α := (loopyOn E)✶
/-
**Matroid.freeOn_ground** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_1} {E : Set α}, (Matroid.freeOn E).E = E
参数：Matroid.freeOn E。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem freeOn_ground : (freeOn E).E = E := rfl
/-
**Matroid.freeOn_dual_eq** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_1} {E : Set α}, (Matroid.freeOn E)✶ = Matroid.loopyOn E
参数：Matroid.freeOn E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.freeOn.eq_1`：∀ {α : Type u_1} (E : Set α), Matroid.freeOn E = (M
atroid.loopyOn E)✶
· 使用定理 `Matroid.dual_dual`：∀ {α : Type u_1} (M : Matroid α), M✶✶ = M
-/
@[simp] theorem freeOn_dual_eq : (freeOn E)✶ = loopyOn E := by
  rw [freeOn, dual_dual]
/-
**Matroid.loopyOn_dual_eq** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_1} {E : Set α}, (Matroid.loopyOn E)✶ = Matroid.freeOn E
参数：Matroid.loopyOn E。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem loopyOn_dual_eq : (loopyOn E)✶ = freeOn E := rfl
/-
**Matroid.freeOn_empty** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ (α : Type u_2), Matroid.freeOn ∅ = Matroid.emptyOn α
参数：α : Type u_2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.loopyOn_empty`：∀ (α : Type u_2), Matroid.loopyOn ∅ = Matroid.emp
tyOn α
· 使用定理 `Matroid.emptyOn_dual_eq`：∀ {α : Type u_1}, (Matroid.emptyOn α)✶ = Matroi
d.emptyOn α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem freeOn_empty (α : Type*) : freeOn (∅ : Set α) = emptyOn α := by
  simp [freeOn]
/-
**Matroid.freeOn_isBase_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_1} {E B : Set α}, (Matroid.freeOn E).IsBase B ↔ B = E
参数：Matroid.freeOn E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] theorem freeOn_isBase_iff : (freeOn E).IsBase B ↔ B = E := by
  simp only [freeOn, loopyOn_ground, dual_isBase_iff', loopyOn_isBase_iff, sdiff_eq_empty,
    ← subset_antisymm_iff, eq_comm (a := E)]
/-
**Matroid.freeOn_indep_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_1} {E I : Set α}, (Matroid.freeOn E).Indep I ↔ I ⊆ E
参数：Matroid.freeOn E。
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
@[simp] theorem freeOn_indep_iff : (freeOn E).Indep I ↔ I ⊆ E := by
  simp [indep_iff]
/-
**Matroid.freeOn_indep** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：freeOn_indep (hIE : I subseteq E) : (freeOn E).Indep I
参数：hIE : I subseteq E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Matroid.freeOn_indep_iff`：∀ {α : Type u_1} {E I : Set α}, (Matroid.freeO
n E).Indep I ↔ I ⊆ E
-/
theorem freeOn_indep (hIE : I ⊆ E) : (freeOn E).Indep I :=
  freeOn_indep_iff.2 hIE
/-
**Matroid.freeOn_isBasis_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_1} {E I X : Set α}, (Matroid.freeOn E).IsBasis I X ↔ I = X ∧
 X ⊆ E
参数：Matroid.freeOn E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.Indep.eq_of_isBasis`：∀ {α : Type u_1} {M : Matroid α} {I J : Set
 α}, M.Indep I → M.IsBasis J I → J = I
· 使用定理 `Matroid.freeOn_indep`：freeOn_indep (hIE : I subseteq E) : (freeOn E).Ind
ep I
· 使用定理 `Matroid.IsBasis.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {I X : S
et α}, M.IsBasis I X → X ⊆ M.E
· 使用定理 `Matroid.Indep.isBasis_self`：∀ {α : Type u_1} {M : Matroid α} {I : Set α}
, M.Indep I → M.IsBasis I I
-/
@[simp] theorem freeOn_isBasis_iff : (freeOn E).IsBasis I X ↔ I = X ∧ X ⊆ E := by
  use fun h ↦ ⟨(freeOn_indep h.subset_ground).eq_of_isBasis h, h.subset_ground⟩
  rintro ⟨rfl, hIE⟩
  exact (freeOn_indep hIE).isBasis_self
/-
**Matroid.freeOn_isBasis'_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_1} {E I X : Set α}, (Matroid.freeOn E).IsBasis' I X ↔ I = X 
∩ E
参数：Matroid.freeOn E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.isBasis'_iff_isBasis_inter_ground`：∀ {α : Type u_1} {M : Matroid
 α} {I X : Set α}, M.IsBasis' I X ↔ M.IsBasis I (X ∩ M.E)
· 使用定理 `Matroid.freeOn_isBasis_iff`：∀ {α : Type u_1} {E I X : Set α}, (Matroid.f
reeOn E).IsBasis I X ↔ I = X ∧ X ⊆ E
· 使用定理 `Matroid.freeOn_ground`：∀ {α : Type u_1} {E : Set α}, (Matroid.freeOn E).
E = E
· 使用定理 `and_iff_left`：∀ {b a : Prop}, b → (a ∧ b ↔ a)
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] theorem freeOn_isBasis'_iff : (freeOn E).IsBasis' I X ↔ I = X ∩ E := by
  rw [isBasis'_iff_isBasis_inter_ground, freeOn_isBasis_iff, freeOn_ground,
    and_iff_left inter_subset_right]
/-
**Matroid.eq_freeOn_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：eq_freeOn_iff : M = freeOn E ↔ M.E = E ∧ M.Indep E
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_of_true`：∀ {a b : Prop}, a → b → (a ↔ b)
· 使用定理 `Matroid.Indep.subset`：∀ {α : Type u_1} {M : Matroid α} {I J : Set α}, M.
Indep J → I ⊆ J → M.Indep I
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem eq_freeOn_iff : M = freeOn E ↔ M.E = E ∧ M.Indep E := by
  refine ⟨?_, fun h ↦ ?_⟩
  · rintro rfl; simp
  simp only [ext_iff_indep, freeOn_ground, freeOn_indep_iff, h.1, true_and]
  exact fun I hIX ↦ iff_of_true (h.2.subset hIX) hIX
/-
**Matroid.ground_indep_iff_eq_freeOn** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：ground_indep_iff_eq_freeOn : M.Indep M.E ↔ M = freeOn M.E
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem ground_indep_iff_eq_freeOn : M.Indep M.E ↔ M = freeOn M.E := by
  simp [eq_freeOn_iff]
/-
**Matroid.freeOn_restrict** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：freeOn_restrict (h : R subseteq E) : (freeOn E) ↾ R = freeOn R
参数：h : R subseteq E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem freeOn_restrict (h : R ⊆ E) : (freeOn E) ↾ R = freeOn R := by
  simp [h, eq_freeOn_iff]
/-
**Matroid.restrict_eq_freeOn_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：restrict_eq_freeOn_iff : M ↾ I = freeOn I ↔ M.Indep I
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.eq_freeOn_iff`：eq_freeOn_iff : M = freeOn E ↔ M.E = E ∧ M.Indep 
E
· 使用定理 `and_iff_right`：∀ {a b : Prop}, a → (a ∧ b ↔ b)
· 使用定理 `Matroid.restrict_ground_eq`：∀ {α : Type u_1} {M : Matroid α} {R : Set α}
, (M.restrict R).E = R
· 使用定理 `Matroid.restrict_indep_iff`：∀ {α : Type u_1} {M : Matroid α} {R I : Set 
α}, (M.restrict R).Indep I ↔ M.Indep I ∧ I ⊆ R
· 使用定理 `and_iff_left`：∀ {b a : Prop}, b → (a ∧ b ↔ a)
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem restrict_eq_freeOn_iff : M ↾ I = freeOn I ↔ M.Indep I := by
  rw [eq_freeOn_iff, and_iff_right M.restrict_ground_eq, restrict_indep_iff,
    and_iff_left Subset.rfl]
/-
**Matroid.Indep.restrict_eq_freeOn** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Indep`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I : Set α}, M.Indep I → M.restrict I = M
atroid.freeOn I
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.restrict_eq_freeOn_iff`：restrict_eq_freeOn_iff : M ↾ I = freeOn 
I ↔ M.Indep I
-/
theorem Indep.restrict_eq_freeOn (hI : M.Indep I) : M ↾ I = freeOn I := by
  rwa [restrict_eq_freeOn_iff]
/-
**Matroid.freeOn_finitary** 是 Mathlib 中的一个实例，位于命名空间 `Matroid`。
形式化陈述：freeOn_finitary : Finitary (freeOn E)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
instance freeOn_finitary : Finitary (freeOn E) := by
  simp only [finitary_iff, freeOn_indep_iff]
  exact fun I h e heI ↦ by simpa using h {e} (by simpa)
/-
**Matroid.freeOn_rankPos** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：freeOn_rankPos (hE : E.Nonempty) : RankPos (freeOn E)
参数：hE : E.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Set.Nonempty.ne_empty`：∀ {α : Type u} {s : Set α}, s.Nonempty → s ≠ ∅
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma freeOn_rankPos (hE : E.Nonempty) : RankPos (freeOn E) := by
  simp [rankPos_iff, hE.ne_empty.symm]

end FreeOn

section uniqueBaseOn

/-- The matroid on `E` whose unique base is the subset `I` of `E`.
Intended for use when `I ⊆ E`; if this is not the case, then the base is `I ∩ E`. -/
/-
**Matroid.uniqueBaseOn** 是 Mathlib 中的一个定义，位于命名空间 `Matroid`。
形式化陈述：uniqueBaseOn (I E : Set α) : Matroid α
参数：I E : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The matroid on `E` whose unique base is the subset `I` of `E`.
Intended for use when `I ⊆ E`; if this is not the case, then the base is `I ∩ E`
.
-/
def uniqueBaseOn (I E : Set α) : Matroid α := freeOn I ↾ E
/-
**Matroid.uniqueBaseOn_ground** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_1} {E I : Set α}, (Matroid.uniqueBaseOn I E).E = E
参数：Matroid.uniqueBaseOn I E。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem uniqueBaseOn_ground : (uniqueBaseOn I E).E = E :=
  rfl
/-
**Matroid.uniqueBaseOn_isBase_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：uniqueBaseOn_isBase_iff (hIE : I subseteq E) : (uniqueBaseOn I E).IsBase B
 ↔ B = I
参数：hIE : I subseteq E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.uniqueBaseOn.eq_1`：∀ {α : Type u_1} (I E : Set α), Matroid.uniqu
eBaseOn I E = (Matroid.freeOn I).restrict E
· 使用定理 `Matroid.isBase_restrict_iff'`：isBase_restrict_iff' : (M ↾ X).IsBase I ↔ 
M.IsBasis' I X
· 使用定理 `Matroid.freeOn_isBasis'_iff`：∀ {α : Type u_1} {E I X : Set α}, (Matroid.
freeOn E).IsBasis' I X ↔ I = X ∩ E
· 使用定理 `Set.inter_eq_self_of_subset_right`：inter_eq_self_of_subset_right {s t : 
Set α} : t subseteq s -> s inter t = t
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem uniqueBaseOn_isBase_iff (hIE : I ⊆ E) : (uniqueBaseOn I E).IsBase B ↔ B = I := by
  rw [uniqueBaseOn, isBase_restrict_iff', freeOn_isBasis'_iff, inter_eq_self_of_subset_right hIE]
/-
**Matroid.uniqueBaseOn_inter_ground_eq** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：uniqueBaseOn_inter_ground_eq (I E : Set α) : uniqueBaseOn (I inter E) E = 
uniqueBaseOn I E
参数：I E : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem uniqueBaseOn_inter_ground_eq (I E : Set α) :
    uniqueBaseOn (I ∩ E) E = uniqueBaseOn I E := by
  simp only [uniqueBaseOn, restrict_eq_restrict_iff, freeOn_indep_iff, subset_inter_iff]
  tauto
/-
**Matroid.uniqueBaseOn_indep_iff'** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_1} {E I J : Set α}, (Matroid.uniqueBaseOn I E).Indep J ↔ J ⊆
 I ∩ E
参数：Matroid.uniqueBaseOn I E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.uniqueBaseOn.eq_1`：∀ {α : Type u_1} (I E : Set α), Matroid.uniqu
eBaseOn I E = (Matroid.freeOn I).restrict E
· 使用定理 `Matroid.restrict_indep_iff`：∀ {α : Type u_1} {M : Matroid α} {R I : Set 
α}, (M.restrict R).Indep I ↔ M.Indep I ∧ I ⊆ R
· 使用定理 `Matroid.freeOn_indep_iff`：∀ {α : Type u_1} {E I : Set α}, (Matroid.freeO
n E).Indep I ↔ I ⊆ E
· 使用定理 `Set.subset_inter_iff`：subset_inter_iff {s t r : Set α} : r subseteq s in
ter t ↔ r subseteq s ∧ r subseteq t
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] theorem uniqueBaseOn_indep_iff' : (uniqueBaseOn I E).Indep J ↔ J ⊆ I ∩ E := by
  rw [uniqueBaseOn, restrict_indep_iff, freeOn_indep_iff, subset_inter_iff]
/-
**Matroid.uniqueBaseOn_indep_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：uniqueBaseOn_indep_iff (hIE : I subseteq E) : (uniqueBaseOn I E).Indep J ↔
 J subseteq I
参数：hIE : I subseteq E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.uniqueBaseOn.eq_1`：∀ {α : Type u_1} (I E : Set α), Matroid.uniqu
eBaseOn I E = (Matroid.freeOn I).restrict E
· 使用定理 `Matroid.restrict_indep_iff`：∀ {α : Type u_1} {M : Matroid α} {R I : Set 
α}, (M.restrict R).Indep I ↔ M.Indep I ∧ I ⊆ R
· 使用定理 `Matroid.freeOn_indep_iff`：∀ {α : Type u_1} {E I : Set α}, (Matroid.freeO
n E).Indep I ↔ I ⊆ E
· 使用定理 `and_iff_left_iff_imp`：∀ {a b : Prop}, (a ∧ b ↔ a) ↔ a → b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
theorem uniqueBaseOn_indep_iff (hIE : I ⊆ E) : (uniqueBaseOn I E).Indep J ↔ J ⊆ I := by
  rw [uniqueBaseOn, restrict_indep_iff, freeOn_indep_iff, and_iff_left_iff_imp]
  exact fun h ↦ h.trans hIE
/-
**Matroid.uniqueBaseOn_isBasis_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：uniqueBaseOn_isBasis_iff (hX : X subseteq E) : (uniqueBaseOn I E).IsBasis 
J X ↔ J = X inter I
参数：hX : X subseteq E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.isBasis_iff_maximal`：isBasis_iff_maximal (hX : X subseteq M.E
· 使用定理 `maximal_iff_eq`：∀ {α : Type u_2} {P : α → Prop} {x y : α} [inst : Partia
lOrder α],   P y → (∀ ⦃x : α⦄, P x → x ≤ y) → (Maximal P x ↔ x = y)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem uniqueBaseOn_isBasis_iff (hX : X ⊆ E) : (uniqueBaseOn I E).IsBasis J X ↔ J = X ∩ I := by
  rw [isBasis_iff_maximal]
  exact maximal_iff_eq (by simp [inter_subset_left.trans hX])
    (by simp +contextual)
/-
**Matroid.uniqueBaseOn_inter_isBasis** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：uniqueBaseOn_inter_isBasis (hX : X subseteq E) : (uniqueBaseOn I E).IsBasi
s (X inter I) X
参数：hX : X subseteq E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.uniqueBaseOn_isBasis_iff`：uniqueBaseOn_isBasis_iff (hX : X subse
teq E) : (uniqueBaseOn I E).IsBasis J X ↔ J = X inter I
-/
theorem uniqueBaseOn_inter_isBasis (hX : X ⊆ E) : (uniqueBaseOn I E).IsBasis (X ∩ I) X := by
  rw [uniqueBaseOn_isBasis_iff hX]
/-
**Matroid.uniqueBaseOn_dual_eq** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_1} (I E : Set α), (Matroid.uniqueBaseOn I E)✶ = Matroid.uniq
ueBaseOn (E \ I) E
参数：I E : Set α；Matroid.uniqueBaseOn I E；E \ I。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.uniqueBaseOn_inter_ground_eq`：uniqueBaseOn_inter_ground_eq (I E 
: Set α) : uniqueBaseOn (I inter E) E = uniqueBaseOn I E
· 使用定理 `Matroid.ext_isBase`：ext_isBase {M₁ M₂ : Matroid α} (hE : M₁.E = M₂.E) (h
 : forall ⦃B⦄, B subseteq M₁.E -> (M₁.IsBase B ↔ M₂.IsBase B)) : M₁ = M₂
· 使用定理 `Matroid.dual_isBase_iff`：∀ {α : Type u_1} {M : Matroid α} {B : Set α},  
 autoParam (B ⊆ M.E) Matroid.dual_isBase_iff._auto_1 → (M✶.IsBase B ↔ M.IsBase (
M.E \ B))
· 使用定理 `Matroid.uniqueBaseOn_isBase_iff`：uniqueBaseOn_isBase_iff (hIE : I subset
eq E) : (uniqueBaseOn I E).IsBase B ↔ B = I
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
· 使用定理 `Matroid.uniqueBaseOn_ground`：∀ {α : Type u_1} {E I : Set α}, (Matroid.un
iqueBaseOn I E).E = E
· 使用定理 `Set.sdiff_sdiff_cancel_left`：sdiff_sdiff_cancel_left {s t : Set α} (h : 
s subseteq t) : t \ (t \ s) = s
· 使用定理 `Set.sdiff_inter_self_eq_sdiff`：sdiff_inter_self_eq_sdiff {s t : Set α} :
 s \ (t inter s) = s \ t
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sdiff_sdiff_right_self`：sdiff_sdiff_right_self : x \ (x \ y) = x ⊓ y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem uniqueBaseOn_dual_eq (I E : Set α) :
    (uniqueBaseOn I E)✶ = uniqueBaseOn (E \ I) E := by
  rw [← uniqueBaseOn_inter_ground_eq]
  refine ext_isBase rfl (fun B (hB : B ⊆ E) ↦ ?_)
  rw [dual_isBase_iff, uniqueBaseOn_isBase_iff inter_subset_right,
    uniqueBaseOn_isBase_iff sdiff_subset, uniqueBaseOn_ground]
  exact ⟨fun h ↦ by rw [← sdiff_sdiff_cancel_left hB, h, sdiff_inter_self_eq_sdiff],
    fun h ↦ by rw [h, inter_comm I]; simp⟩
/-
**Matroid.uniqueBaseOn_self** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_1} (I : Set α), Matroid.uniqueBaseOn I I = Matroid.freeOn I
参数：I : Set α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.uniqueBaseOn.eq_1`：∀ {α : Type u_1} (I E : Set α), Matroid.uniqu
eBaseOn I E = (Matroid.freeOn I).restrict E
· 使用定理 `Matroid.freeOn_restrict`：freeOn_restrict (h : R subseteq E) : (freeOn E)
 ↾ R = freeOn R
· 使用定理 `Eq.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorder
 α] {a b : α}, a = b → a ⊆ b
-/
@[simp] theorem uniqueBaseOn_self (I : Set α) : uniqueBaseOn I I = freeOn I := by
  rw [uniqueBaseOn, freeOn_restrict rfl.subset]
/-
**Matroid.uniqueBaseOn_empty** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_1} (I : Set α), Matroid.uniqueBaseOn ∅ I = Matroid.loopyOn I
参数：I : Set α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.dual_inj`：∀ {α : Type u_1} {M₁ M₂ : Matroid α}, M₁✶ = M₂✶ ↔ M₁ =
 M₂
· 使用定理 `Matroid.uniqueBaseOn_dual_eq`：∀ {α : Type u_1} (I E : Set α), (Matroid.u
niqueBaseOn I E)✶ = Matroid.uniqueBaseOn (E \ I) E
· 使用定理 `Set.sdiff_empty`：sdiff_empty {s : Set α} : s \ ∅ = s
· 使用定理 `Matroid.uniqueBaseOn_self`：∀ {α : Type u_1} (I : Set α), Matroid.uniqueB
aseOn I I = Matroid.freeOn I
· 使用定理 `Matroid.loopyOn_dual_eq`：∀ {α : Type u_1} {E : Set α}, (Matroid.loopyOn 
E)✶ = Matroid.freeOn E
-/
@[simp] theorem uniqueBaseOn_empty (I : Set α) : uniqueBaseOn ∅ I = loopyOn I := by
  rw [← dual_inj, uniqueBaseOn_dual_eq, sdiff_empty, uniqueBaseOn_self, loopyOn_dual_eq]
/-
**Matroid.uniqueBaseOn_restrict'** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：uniqueBaseOn_restrict' (I E R : Set α) : (uniqueBaseOn I E) ↾ R = uniqueBa
seOn (I inter R inter E) R
参数：I E R : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
theorem uniqueBaseOn_restrict' (I E R : Set α) :
    (uniqueBaseOn I E) ↾ R = uniqueBaseOn (I ∩ R ∩ E) R := by
  simp_rw [ext_iff_indep, restrict_ground_eq, uniqueBaseOn_ground, true_and,
    restrict_indep_iff, uniqueBaseOn_indep_iff', subset_inter_iff]
  tauto
/-
**Matroid.uniqueBaseOn_restrict** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：uniqueBaseOn_restrict (h : I subseteq E) (R : Set α) : (uniqueBaseOn I E) 
↾ R = uniqueBaseOn (I inter R) R
参数：h : I subseteq E；R : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.uniqueBaseOn_restrict'`：uniqueBaseOn_restrict' (I E R : Set α) :
 (uniqueBaseOn I E) ↾ R = uniqueBaseOn (I inter R inter E) R
· 使用定理 `Set.inter_right_comm`：inter_right_comm (s₁ s₂ s₃ : Set α) : s₁ inter s₂ 
inter s₃ = s₁ inter s₃ inter s₂
· 使用定理 `Set.inter_eq_self_of_subset_left`：inter_eq_self_of_subset_left {s t : Se
t α} : s subseteq t -> s inter t = s
-/
theorem uniqueBaseOn_restrict (h : I ⊆ E) (R : Set α) :
    (uniqueBaseOn I E) ↾ R = uniqueBaseOn (I ∩ R) R := by
  rw [uniqueBaseOn_restrict', inter_right_comm, inter_eq_self_of_subset_left h]
/-
**Matroid.uniqueBaseOn_rankFinite** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：uniqueBaseOn_rankFinite (hI : I.Finite) : RankFinite (uniqueBaseOn I E)
参数：hI : I.Finite。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.uniqueBaseOn_inter_ground_eq`：uniqueBaseOn_inter_ground_eq (I E 
: Set α) : uniqueBaseOn (I inter E) E = uniqueBaseOn I E
· 使用定理 `Matroid.uniqueBaseOn_isBase_iff`：uniqueBaseOn_isBase_iff (hIE : I subset
eq E) : (uniqueBaseOn I E).IsBase B ↔ B = I
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `and_iff_right`：∀ {a b : Prop}, a → (a ∧ b ↔ b)
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
-/
lemma uniqueBaseOn_rankFinite (hI : I.Finite) : RankFinite (uniqueBaseOn I E) := by
  rw [← uniqueBaseOn_inter_ground_eq]
  refine ⟨I ∩ E, ?_⟩
  rw [uniqueBaseOn_isBase_iff inter_subset_right, and_iff_right rfl]
  exact hI.subset inter_subset_left
/-
**Matroid.uniqueBaseOn_finitary** 是 Mathlib 中的一个实例，位于命名空间 `Matroid`。
形式化陈述：uniqueBaseOn_finitary : Finitary (uniqueBaseOn I E)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
instance uniqueBaseOn_finitary : Finitary (uniqueBaseOn I E) := by
  refine ⟨fun K hK ↦ ?_⟩
  simp only [uniqueBaseOn_indep_iff'] at hK ⊢
  exact fun e heK ↦ singleton_subset_iff.1 <| hK _ (by simpa) (by simp)
/-
**Matroid.uniqueBaseOn_rankPos** 是 Mathlib 中的一个引理，位于命名空间 `Matroid`。
形式化陈述：uniqueBaseOn_rankPos (hIE : I subseteq E) (hI : I.Nonempty) : RankPos (uni
queBaseOn I E) where empty_not_isBase
参数：hIE : I subseteq E；hI : I.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.uniqueBaseOn_isBase_iff`：uniqueBaseOn_isBase_iff (hIE : I subset
eq E) : (uniqueBaseOn I E).IsBase B ↔ B = I
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Set.Nonempty.ne_empty`：∀ {α : Type u} {s : Set α}, s.Nonempty → s ≠ ∅
-/
lemma uniqueBaseOn_rankPos (hIE : I ⊆ E) (hI : I.Nonempty) : RankPos (uniqueBaseOn I E) where
  empty_not_isBase := by simpa [uniqueBaseOn_isBase_iff hIE] using Ne.symm <| hI.ne_empty

end uniqueBaseOn

end Matroid

