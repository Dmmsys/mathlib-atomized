/-
Copyright (c) 2023 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson
-/
module

public import Mathlib.Combinatorics.Matroid.IndepAxioms

/-!
# Matroid Duality

For a matroid `M` on ground set `E`, the collection of complements of the bases of `M` is the
collection of bases of another matroid on `E` called the 'dual' of `M`.
The map from `M` to its dual is an involution, interacts nicely with minors,
and preserves many important matroid properties such as representability and connectivity.

This file defines the dual matroid `M✶` of `M`, and gives associated API. The definition
is in terms of its independent sets, using `IndepMatroid.matroid`.

We also define 'Co-independence' (independence in the dual) of a set as a predicate `M.Coindep X`.
This is an abbreviation for `M✶.Indep X`, but has its own name for the sake of dot notation.

## Main Definitions

* `M.Dual`, written `M✶`, is the matroid on `M.E` which a set `B ⊆ M.E` is a base if and only if
  `M.E \ B` is a base for `M`.

* `M.Coindep X` means `M✶.Indep X`, or equivalently that `X` is contained in `M.E \ B` for some
  base `B` of `M`.
-/

@[expose] public section

assert_not_exists Field

open Set

namespace Matroid

variable {α : Type*} {M : Matroid α} {I B X : Set α}

section dual

/-- Given `M : Matroid α`, the `IndepMatroid α` whose independent sets are
  the subsets of `M.E` that are disjoint from some base of `M` -/
/-
**Matroid.dualIndepMatroid** 是 Mathlib 中的一个定义，位于命名空间 `Matroid`。
形式化陈述：{α : Type u_1} → Matroid α → IndepMatroid α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `M : Matroid α`, the `IndepMatroid α` whose independent sets are
  the subsets of `M.E` that are disjoint from some base of `M`
-/
@[simps] def dualIndepMatroid (M : Matroid α) : IndepMatroid α where
  E := M.E
  Indep I := I ⊆ M.E ∧ ∃ B, M.IsBase B ∧ Disjoint I B
  indep_empty := ⟨empty_subset M.E, M.exists_isBase.imp (fun _ hB ↦ ⟨hB, empty_disjoint _⟩)⟩
  indep_subset := by
    rintro I J ⟨hJE, B, hB, hJB⟩ hIJ
    exact ⟨hIJ.trans hJE, ⟨B, hB, disjoint_of_subset_left hIJ hJB⟩⟩
  indep_aug := by
    rintro I X ⟨hIE, B, hB, hIB⟩ hI_not_max hX_max
    have hXE := hX_max.1.1
    have hB' := (isBase_compl_iff_maximal_disjoint_isBase hXE).mpr hX_max
    set B' := M.E \ X with hX
    have hI := (not_iff_not.mpr (isBase_compl_iff_maximal_disjoint_isBase)).mpr hI_not_max
    obtain ⟨B'', hB'', hB''₁, hB''₂⟩ := (hB'.indep.sdiff I).exists_isBase_subset_union_isBase hB
    rw [← compl_subset_compl, ← hIB.sdiff_eq_right, ← union_sdiff_distrib, sdiff_eq, compl_inter,
      compl_compl, union_subset_iff, compl_subset_compl] at hB''₂
    have hssu := (subset_inter (hB''₂.2) hIE).ssubset_of_ne
      (by { rintro rfl; apply hI; convert! hB''; simp [hB''.subset_ground] })
    obtain ⟨e, ⟨(heB'' : e ∉ _), heE⟩, heI⟩ := exists_of_ssubset hssu
    use e
    simp_rw [mem_sdiff, insert_subset_iff, and_iff_left heI, and_iff_right heE, and_iff_right hIE]
    refine ⟨by_contra (fun heX ↦ heB'' (hB''₁ ⟨?_, heI⟩)), ⟨B'', hB'', ?_⟩⟩
    · rw [hX]; exact ⟨heE, heX⟩
    rw [← union_singleton, disjoint_union_left, disjoint_singleton_left, and_iff_left heB'']
    exact disjoint_of_subset_left hB''₂.2 disjoint_compl_left
  indep_maximal := by
    rintro X - I' ⟨hI'E, B, hB, hI'B⟩ hI'X
    obtain ⟨I, hI⟩ := M.exists_isBasis (M.E \ X)
    obtain ⟨B', hB', hIB', hB'IB⟩ := hI.indep.exists_isBase_subset_union_isBase hB
    obtain rfl : I = B' \ X := hI.eq_of_subset_indep (hB'.indep.sdiff _)
      (subset_sdiff.2 ⟨hIB', (subset_sdiff.1 hI.subset).2⟩)
      (sdiff_subset_sdiff_left hB'.subset_ground)
    simp_rw [maximal_subset_iff']
    refine ⟨(X \ B') ∩ M.E, ?_, ⟨⟨inter_subset_right, ?_⟩, ?_⟩, ?_⟩
    · rw [subset_inter_iff, and_iff_left hI'E, subset_sdiff, and_iff_right hI'X]
      exact Disjoint.mono_right hB'IB <| disjoint_union_right.2
        ⟨disjoint_sdiff_right.mono_left hI'X, hI'B⟩
    · exact ⟨B', hB', (disjoint_sdiff_left (t := X)).mono_left inter_subset_left⟩
    · exact inter_subset_left.trans sdiff_subset
    simp only [subset_inter_iff, subset_sdiff, and_imp, forall_exists_index]
    refine fun J hJE B'' hB'' hdj hJX hXJ ↦ ⟨⟨hJX, ?_⟩, hJE⟩
    have hI' : (B'' ∩ X) ∪ (B' \ X) ⊆ B' := by
      rw [union_subset_iff, and_iff_left sdiff_subset, ← union_sdiff_cancel hJX,
        inter_union_distrib_left, hdj.symm.inter_eq, empty_union, sdiff_eq, ← inter_assoc,
        ← sdiff_eq, sdiff_subset_comm, sdiff_eq, inter_assoc, ← sdiff_eq, inter_comm]
      exact subset_trans (inter_subset_inter_right _ hB''.subset_ground) hXJ
    obtain ⟨B₁, hB₁, hI'B₁, hB₁I⟩ := (hB'.indep.subset hI').exists_isBase_subset_union_isBase hB''
    rw [union_comm, ← union_assoc, union_eq_self_of_subset_right inter_subset_left] at hB₁I
    obtain rfl : B₁ = B' := by
      refine hB₁.eq_of_subset_indep hB'.indep (fun e he ↦ ?_)
      refine (hB₁I he).elim (fun heB'' ↦ ?_) (fun h ↦ h.1)
      refine (em (e ∈ X)).elim (fun heX ↦ hI' (Or.inl ⟨heB'', heX⟩)) (fun heX ↦ hIB' ?_)
      refine hI.mem_of_insert_indep ⟨hB₁.subset_ground he, heX⟩ ?_
      exact hB₁.indep.subset (insert_subset he (subset_union_right.trans hI'B₁))
    by_contra hdj'
    obtain ⟨e, heJ, heB'⟩ := not_disjoint_iff.mp hdj'
    obtain (heB'' | ⟨-, heX⟩) := hB₁I heB'
    · exact hdj.ne_of_mem heJ heB'' rfl
    exact heX (hJX heJ)
  subset_ground := by tauto

/-- The dual of a matroid; the bases are the complements (w.r.t. `M.E`) of the bases of `M`. -/
/-
**Matroid.dual** 是 Mathlib 中的一个定义，位于命名空间 `Matroid`。
形式化陈述：dual (M : Matroid α) : Matroid α
参数：M : Matroid α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The dual of a matroid; the bases are the complements (w.r.t. `M.E`) of the bases
 of `M`.
-/
def dual (M : Matroid α) : Matroid α := M.dualIndepMatroid.matroid

/-- The `✶` symbol, which denotes matroid duality.
  (This is distinct from the usual `*` symbol for multiplication, due to precedence issues.) -/
postfix:max "✶" => Matroid.dual

/-
**Matroid.dual_indep_iff_exists'** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：dual_indep_iff_exists' : (M✶.Indep I) ↔ I subseteq M.E ∧ (exists B, M.IsBa
se B ∧ Disjoint I B)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem dual_indep_iff_exists' : (M✶.Indep I) ↔ I ⊆ M.E ∧ (∃ B, M.IsBase B ∧ Disjoint I B) :=
  Iff.rfl
/-
**Matroid.dual_ground** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α}, M✶.E = M.E
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem dual_ground : M✶.E = M.E := rfl
/-
**Matroid.dual_indep_iff_exists** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：dual_indep_iff_exists (hI : I subseteq M.E
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.dual_indep_iff_exists'`：dual_indep_iff_exists' : (M✶.Indep I) ↔ 
I subseteq M.E ∧ (exists B, M.IsBase B ∧ Disjoint I B)
· 使用定理 `and_iff_right`：∀ {a b : Prop}, a → (a ∧ b ↔ b)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem dual_indep_iff_exists (hI : I ⊆ M.E := by aesop_mat) :
    M✶.Indep I ↔ (∃ B, M.IsBase B ∧ Disjoint I B) := by
  rw [dual_indep_iff_exists', and_iff_right hI]
/-
**Matroid.dual_dep_iff_forall** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：dual_dep_iff_forall : (M✶.Dep I) ↔ (forall B, M.IsBase B -> (I inter B).No
nempty) ∧ I subseteq M.E
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_true_intro`：∀ {a : Prop}, a → (a ↔ True)
-/
theorem dual_dep_iff_forall : (M✶.Dep I) ↔ (∀ B, M.IsBase B → (I ∩ B).Nonempty) ∧ I ⊆ M.E := by
  simp_rw [dep_iff, dual_indep_iff_exists', dual_ground, and_congr_left_iff, not_and,
    not_exists, not_and, not_disjoint_iff_nonempty_inter, Classical.imp_iff_right_iff,
    iff_true_intro Or.inl]
/-
**Matroid.dual_finite** 是 Mathlib 中的一个实例，位于命名空间 `Matroid`。
形式化陈述：dual_finite [M.Finite] : M✶.Finite
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.ground_finite`：ground_finite (M : Matroid α) [M.Finite] : M.E.Fi
nite
-/
instance dual_finite [M.Finite] : M✶.Finite :=
  ⟨M.ground_finite⟩
/-
**Matroid.dual_nonempty** 是 Mathlib 中的一个实例，位于命名空间 `Matroid`。
形式化陈述：dual_nonempty [M.Nonempty] : M✶.Nonempty
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.ground_nonempty`：ground_nonempty (M : Matroid α) [M.Nonempty] : 
M.E.Nonempty
-/
instance dual_nonempty [M.Nonempty] : M✶.Nonempty :=
  ⟨M.ground_nonempty⟩
/-
**Matroid.dual_isBase_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {B : Set α},   autoParam (B ⊆ M.E) Matroi
d.dual_isBase_iff._auto_1 → (M✶.IsBase B ↔ M.IsBase (M.E \ B))
参数：B ⊆ M.E；M✶.IsBase B ↔ M.IsBase (M.E \ B)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.isBase_compl_iff_maximal_disjoint_isBase`：isBase_compl_iff_maxim
al_disjoint_isBase (hB : B subseteq M.E
· 使用定理 `Matroid.isBase_iff_maximal_indep`：isBase_iff_maximal_indep : M.IsBase B 
↔ Maximal M.Indep B
· 使用定理 `maximal_subset_iff`：maximal_subset_iff : Maximal P s ↔ P s ∧ forall ⦃t⦄,
 P t -> s subseteq t -> s = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] theorem dual_isBase_iff (hB : B ⊆ M.E := by aesop_mat) :
    M✶.IsBase B ↔ M.IsBase (M.E \ B) := by
  rw [isBase_compl_iff_maximal_disjoint_isBase, isBase_iff_maximal_indep, maximal_subset_iff,
    maximal_subset_iff]
  simp [dual_indep_iff_exists', hB]
/-
**Matroid.dual_isBase_iff'** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：dual_isBase_iff' : M✶.IsBase B ↔ M.IsBase (M.E \ B) ∧ B subseteq M.E
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.dual_isBase_iff`：∀ {α : Type u_1} {M : Matroid α} {B : Set α},  
 autoParam (B ⊆ M.E) Matroid.dual_isBase_iff._auto_1 → (M✶.IsBase B ↔ M.IsBase (
M.E \ B))
· 使用定理 `and_iff_left`：∀ {b a : Prop}, b → (a ∧ b ↔ a)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `iff_of_false`：∀ {a b : Prop}, ¬a → ¬b → (a ↔ b)
· 使用定理 `Matroid.IsBase.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {B : Set 
α}, M.IsBase B → B ⊆ M.E
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem dual_isBase_iff' : M✶.IsBase B ↔ M.IsBase (M.E \ B) ∧ B ⊆ M.E :=
  (em (B ⊆ M.E)).elim (fun h ↦ by rw [dual_isBase_iff, and_iff_left h])
    (fun h ↦ iff_of_false (h ∘ (fun h' ↦ h'.subset_ground)) (h ∘ And.right))
/-
**Matroid.setOfPred_dual_isBase_eq** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：setOfPred_dual_isBase_eq : {B | M✶.IsBase B} = (fun X => M.E \ X) '' {B | 
M.IsBase B}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Set.sdiff_sdiff_cancel_left`：sdiff_sdiff_cancel_left {s t : Set α} (h : 
s subseteq t) : t \ (t \ s) = s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.IsBase.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {B : Set 
α}, M.IsBase B → B ⊆ M.E
· 使用定理 `Eq.trans_subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] {a b c : α
} [inst : LE α], a = b → b ⊆ c → a ⊆ c
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
-/
theorem setOfPred_dual_isBase_eq : {B | M✶.IsBase B} = (fun X ↦ M.E \ X) '' {B | M.IsBase B} := by
  ext B
  simp only [mem_ofPred_eq, mem_image, dual_isBase_iff']
  refine ⟨fun h ↦ ⟨_, h.1, sdiff_sdiff_cancel_left h.2⟩,
    fun ⟨B', hB', h⟩ ↦ ⟨?_,h.symm.trans_subset sdiff_subset⟩⟩
  rwa [← h, sdiff_sdiff_cancel_left hB'.subset_ground]

@[deprecated (since := "2026-07-09")] alias setOf_dual_isBase_eq := setOfPred_dual_isBase_eq
/-
**Matroid.dual_dual** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_1} (M : Matroid α), M✶✶ = M
参数：M : Matroid α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.ext_isBase`：ext_isBase {M₁ M₂ : Matroid α} (hE : M₁.E = M₂.E) (h
 : forall ⦃B⦄, B subseteq M₁.E -> (M₁.IsBase B ↔ M₂.IsBase B)) : M₁ = M₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.dual_isBase_iff`：∀ {α : Type u_1} {M : Matroid α} {B : Set α},  
 autoParam (B ⊆ M.E) Matroid.dual_isBase_iff._auto_1 → (M✶.IsBase B ↔ M.IsBase (
M.E \ B))
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Matroid.dual_ground`：∀ {α : Type u_1} {M : Matroid α}, M✶.E = M.E
· 使用定理 `Set.sdiff_sdiff_cancel_left`：sdiff_sdiff_cancel_left {s t : Set α} (h : 
s subseteq t) : t \ (t \ s) = s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] theorem dual_dual (M : Matroid α) : M✶✶ = M :=
  ext_isBase rfl (fun B (h : B ⊆ M.E) ↦
    by rw [dual_isBase_iff, dual_isBase_iff, dual_ground, sdiff_sdiff_cancel_left h])
/-
**Matroid.dual_involutive** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：dual_involutive : Function.Involutive (dual : Matroid α -> Matroid α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.dual_dual`：∀ {α : Type u_1} (M : Matroid α), M✶✶ = M
-/
theorem dual_involutive : Function.Involutive (dual : Matroid α → Matroid α) := dual_dual
/-
**Matroid.dual_injective** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：dual_injective : Function.Injective (dual : Matroid α -> Matroid α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Involutive.injective`：∀ {α : Sort u} {f : α → α}, Function.Invo
lutive f → Function.Injective f
· 使用定理 `Matroid.dual_involutive`：dual_involutive : Function.Involutive (dual : M
atroid α -> Matroid α)
-/
theorem dual_injective : Function.Injective (dual : Matroid α → Matroid α) :=
  dual_involutive.injective
/-
**Matroid.dual_inj** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_1} {M₁ M₂ : Matroid α}, M₁✶ = M₂✶ ↔ M₁ = M₂
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Matroid.dual_injective`：dual_injective : Function.Injective (dual : Matr
oid α -> Matroid α)
-/
@[simp] theorem dual_inj {M₁ M₂ : Matroid α} : M₁✶ = M₂✶ ↔ M₁ = M₂ :=
  dual_injective.eq_iff
/-
**Matroid.eq_dual_comm** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：eq_dual_comm {M₁ M₂ : Matroid α} : M₁ = M₂✶ ↔ M₂ = M₁✶
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.dual_inj`：∀ {α : Type u_1} {M₁ M₂ : Matroid α}, M₁✶ = M₂✶ ↔ M₁ =
 M₂
· 使用定理 `Matroid.dual_dual`：∀ {α : Type u_1} (M : Matroid α), M✶✶ = M
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem eq_dual_comm {M₁ M₂ : Matroid α} : M₁ = M₂✶ ↔ M₂ = M₁✶ := by
  rw [← dual_inj, dual_dual, eq_comm]
/-
**Matroid.eq_dual_iff_dual_eq** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：eq_dual_iff_dual_eq {M₁ M₂ : Matroid α} : M₁ = M₂✶ ↔ M₁✶ = M₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Function.Involutive.eq_iff`：∀ {α : Sort u} {f : α → α}, Function.Involut
ive f → ∀ {x y : α}, f x = y ↔ x = f y
· 使用定理 `Matroid.dual_involutive`：dual_involutive : Function.Involutive (dual : M
atroid α -> Matroid α)
-/
theorem eq_dual_iff_dual_eq {M₁ M₂ : Matroid α} : M₁ = M₂✶ ↔ M₁✶ = M₂ :=
  dual_involutive.eq_iff.symm
/-
**Matroid.IsBase.compl_isBase_of_dual** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBase`
。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {B : Set α}, M✶.IsBase B → M.IsBase (M.E 
\ B)
参数：M.E \ B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Matroid.dual_isBase_iff'`：dual_isBase_iff' : M✶.IsBase B ↔ M.IsBase (M.E
 \ B) ∧ B subseteq M.E
-/
theorem IsBase.compl_isBase_of_dual (h : M✶.IsBase B) : M.IsBase (M.E \ B) :=
  (dual_isBase_iff'.1 h).1
/-
**Matroid.IsBase.compl_isBase_dual** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBase`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {B : Set α}, M.IsBase B → M✶.IsBase (M.E 
\ B)
参数：M.E \ B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.dual_isBase_iff`：∀ {α : Type u_1} {M : Matroid α} {B : Set α},  
 autoParam (B ⊆ M.E) Matroid.dual_isBase_iff._auto_1 → (M✶.IsBase B ↔ M.IsBase (
M.E \ B))
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.sdiff_sdiff_cancel_left`：sdiff_sdiff_cancel_left {s t : Set α} (h : 
s subseteq t) : t \ (t \ s) = s
· 使用定理 `Matroid.IsBase.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {B : Set 
α}, M.IsBase B → B ⊆ M.E
-/
theorem IsBase.compl_isBase_dual (h : M.IsBase B) : M✶.IsBase (M.E \ B) := by
  rwa [dual_isBase_iff, sdiff_sdiff_cancel_left h.subset_ground]
/-
**Matroid.IsBase.compl_inter_isBasis_of_inter_isBasis** 是 Mathlib 中的一个定理，位于命名空间 
`Matroid.IsBase`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {B X : Set α},   M.IsBase B → M.IsBasis (
B ∩ X) X → M✶.IsBasis (M.E \ B ∩ (M.E \ X)) (M.E \ X)
参数：B ∩ X；M.E \ B ∩ (M.E \ X)；M.E \ X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.Indep.isBasis_of_forall_insert`：∀ {α : Type u_1} {M : Matroid α}
 {I X : Set α}, M.Indep I → I ⊆ X → (∀ e ∈ X \ I, M.Dep (insert e I)) → M.IsBasi
s I X
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.dual_indep_iff_exists`：dual_indep_iff_exists (hI : I subseteq M.
E
· 使用定理 `_private.Mathlib.Combinatorics.Matroid.Basic.0.Matroid.inter_right_subse
t_ground`：∀ {α : Type u_1} {M : Matroid α} {X Y : Set α}, X ⊆ M.E → X ∩ Y ⊆ M.E
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Set.disjoint_of_subset_left`：disjoint_of_subset_left (h : s subseteq u) 
(d : Disjoint u t) : Disjoint s t
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用引理 `Set.disjoint_sdiff_left`：disjoint_sdiff_left : Disjoint (t \ s) s
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `and_iff_right`：∀ {a b : Prop}, a → (a ∧ b ↔ b)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.sdiff_inter_self_eq_sdiff`：sdiff_inter_self_eq_sdiff {s t : Set α} :
 s \ (t inter s) = s \ t
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `imp_iff_right`：∀ {b a : Prop}, a → (a → b ↔ b)
· 使用定理 `and_iff_left`：∀ {b a : Prop}, b → (a ∧ b ↔ a)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
· 使用定理 `by_contra`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Matroid.IsBase.exchange`：∀ {α : Type u_1} {M : Matroid α} {B₁ B₂ : Set α
} {e : α},   M.IsBase B₁ → M.IsBase B₂ → e ∈ B₁ \ B₂ → ∃ y ∈ B₂ \ B₁, M.IsBase (
insert y (B₁ …
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.sdiff_eq_empty`：sdiff_eq_empty {s t : Set α} : s \ t = ∅ ↔ s subsete
q t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.sdiff_eq`：sdiff_eq (s t : Set α) : s \ t = s inter tᶜ
· 使用定理 `Set.inter_eq_self_of_subset_right`：inter_eq_self_of_subset_right {s t : 
Set α} : t subseteq s -> s inter t = t
· 使用定理 `Matroid.IsBase.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {B : Set 
α}, M.IsBase B → B ⊆ M.E
· 使用定理 `Set.inter_right_comm`：inter_right_comm (s₁ s₂ s₃ : Set α) : s₁ inter s₂ 
inter s₃ = s₁ inter s₃ inter s₂
· 使用定理 `Set.singleton_inter_eq_empty`：singleton_inter_eq_empty : {a} inter s = ∅
 ↔ a ∉ s
（共 43 条，此处仅展示前 30 条）
-/
theorem IsBase.compl_inter_isBasis_of_inter_isBasis (hB : M.IsBase B) (hBX : M.IsBasis (B ∩ X) X) :
    M✶.IsBasis ((M.E \ B) ∩ (M.E \ X)) (M.E \ X) := by
  refine Indep.isBasis_of_forall_insert ?_ inter_subset_right (fun e he ↦ ?_)
  · rw [dual_indep_iff_exists]
    exact ⟨B, hB, disjoint_of_subset_left inter_subset_left disjoint_sdiff_left⟩
  simp only [sdiff_inter_self_eq_sdiff, mem_sdiff, not_and, not_not, imp_iff_right he.1.1] at he
  simp_rw [dual_dep_iff_forall, insert_subset_iff, and_iff_right he.1.1,
    and_iff_left (inter_subset_left.trans sdiff_subset)]
  refine fun B' hB' ↦ by_contra (fun hem ↦ ?_)
  rw [nonempty_iff_ne_empty, not_ne_iff, ← union_singleton, sdiff_inter_sdiff,
    union_inter_distrib_right, union_empty_iff, singleton_inter_eq_empty, sdiff_eq,
    inter_right_comm, inter_eq_self_of_subset_right hB'.subset_ground, ← sdiff_eq,
    sdiff_eq_empty] at hem
  obtain ⟨f, hfb, hBf⟩ := hB.exchange hB' ⟨he.2, hem.2⟩
  have hi : M.Indep (insert f (B ∩ X)) := by
    refine hBf.indep.subset (insert_subset_insert ?_)
    simp_rw [subset_sdiff, and_iff_right inter_subset_left, disjoint_singleton_right,
      mem_inter_iff, iff_false_intro he.1.2, and_false, not_false_iff]
  exact hfb.2 (hBX.mem_of_insert_indep (Or.elim (hem.1 hfb.1) (False.elim ∘ hfb.2) id) hi).1
/-
**Matroid.IsBase.inter_isBasis_iff_compl_inter_isBasis_dual** 是 Mathlib 中的一个定理，位
于命名空间 `Matroid.IsBase`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {B X : Set α},   M.IsBase B →     autoPar
am (X ⊆ M.E) Matroid.IsBase.inter_isBasis_iff_compl_inter_isBasis_dual._auto_1 →
       (M.IsBasis (B ∩ X) X ↔ M✶.IsBasis (M.E \ B ∩ (M.E \ X)) (M.E \ X))
参数：X ⊆ M.E；M.IsBasis (B ∩ X) X ↔ M✶.IsBasis (M.E \ B ∩ (M.E \ X)) (M.E \ X)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsBase.compl_inter_isBasis_of_inter_isBasis`：∀ {α : Type u_1} {M
 : Matroid α} {B X : Set α},   M.IsBase B → M.IsBasis (B ∩ X) X → M✶.IsBasis (M.
E \ B ∩ (M.E \ X)) (M.E \ X)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.dual_dual`：∀ {α : Type u_1} (M : Matroid α), M✶✶ = M
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sdiff_sdiff_right_self`：sdiff_sdiff_right_self : x \ (x \ y) = x ⊓ y
· 使用定理 `Set.inter_eq_self_of_subset_right`：inter_eq_self_of_subset_right {s t : 
Set α} : t subseteq s -> s inter t = t
· 使用定理 `Matroid.IsBase.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {B : Set 
α}, M.IsBase B → B ⊆ M.E
· 使用定理 `Matroid.IsBase.compl_isBase_dual`：∀ {α : Type u_1} {M : Matroid α} {B : 
Set α}, M.IsBase B → M✶.IsBase (M.E \ B)
-/
theorem IsBase.inter_isBasis_iff_compl_inter_isBasis_dual (hB : M.IsBase B)
    (hX : X ⊆ M.E := by aesop_mat) :
    M.IsBasis (B ∩ X) X ↔ M✶.IsBasis ((M.E \ B) ∩ (M.E \ X)) (M.E \ X) := by
  refine ⟨hB.compl_inter_isBasis_of_inter_isBasis, fun h ↦ ?_⟩
  simpa [inter_eq_self_of_subset_right hX, inter_eq_self_of_subset_right hB.subset_ground] using
    hB.compl_isBase_dual.compl_inter_isBasis_of_inter_isBasis h
/-
**Matroid.base_iff_dual_isBase_compl** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：base_iff_dual_isBase_compl (hB : B subseteq M.E
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.dual_isBase_iff`：∀ {α : Type u_1} {M : Matroid α} {B : Set α},  
 autoParam (B ⊆ M.E) Matroid.dual_isBase_iff._auto_1 → (M✶.IsBase B ↔ M.IsBase (
M.E \ B))
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.sdiff_sdiff_cancel_left`：sdiff_sdiff_cancel_left {s t : Set α} (h : 
s subseteq t) : t \ (t \ s) = s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem base_iff_dual_isBase_compl (hB : B ⊆ M.E := by aesop_mat) :
    M.IsBase B ↔ M✶.IsBase (M.E \ B) := by
  rw [dual_isBase_iff, sdiff_sdiff_cancel_left hB]
/-
**Matroid.ground_not_isBase** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：ground_not_isBase (M : Matroid α) [h : RankPos M✶] : ¬M.IsBase M.E
参数：M : Matroid α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sdiff_empty`：sdiff_empty {s : Set α} : s \ ∅ = s
· 使用定理 `Matroid.dual_isBase_iff`：∀ {α : Type u_1} {M : Matroid α} {B : Set α},  
 autoParam (B ⊆ M.E) Matroid.dual_isBase_iff._auto_1 → (M✶.IsBase B ↔ M.IsBase (
M.E \ B))
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Matroid.rankPos_iff`：∀ {α : Type u_1} (M : Matroid α), M.RankPos ↔ ¬M.Is
Base ∅
-/
theorem ground_not_isBase (M : Matroid α) [h : RankPos M✶] : ¬M.IsBase M.E := by
  rwa [rankPos_iff, dual_isBase_iff, sdiff_empty] at h
/-
**Matroid.IsBase.ssubset_ground** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBase`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {B : Set α} [h : M✶.RankPos], M.IsBase B 
→ B ⊂ M.E
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.ssubset_of_ne`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst 
: PartialOrder α] {a b : α}, a ⊆ b → a ≠ b → a ⊂ b
· 使用定理 `Matroid.IsBase.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {B : Set 
α}, M.IsBase B → B ⊆ M.E
· 使用定理 `Matroid.ground_not_isBase`：ground_not_isBase (M : Matroid α) [h : RankPo
s M✶] : ¬M.IsBase M.E
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem IsBase.ssubset_ground [h : RankPos M✶] (hB : M.IsBase B) : B ⊂ M.E :=
  hB.subset_ground.ssubset_of_ne (by rintro rfl; exact M.ground_not_isBase hB)
/-
**Matroid.Indep.ssubset_ground** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Indep`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I : Set α} [h : M✶.RankPos], M.Indep I →
 I ⊂ M.E
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.Indep.exists_isBase_superset`：∀ {α : Type u_1} {M : Matroid α} {
I : Set α}, M.Indep I → ∃ B, M.IsBase B ∧ I ⊆ B
· 使用定理 `LE.le.trans_ssubset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst 
: Preorder α] {a b c : α}, a ⊆ b → b ⊂ c → a ⊂ c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Matroid.IsBase.ssubset_ground`：∀ {α : Type u_1} {M : Matroid α} {B : Set
 α} [h : M✶.RankPos], M.IsBase B → B ⊂ M.E
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem Indep.ssubset_ground [h : RankPos M✶] (hI : M.Indep I) : I ⊂ M.E := by
  obtain ⟨B, hB⟩ := hI.exists_isBase_superset; exact hB.2.trans_ssubset hB.1.ssubset_ground

/-- A coindependent set of `M` is an independent set of the dual of `M✶`. we give it a separate
  definition to enable dot notation. Which spelling is better depends on context. -/
/-
**Matroid.Coindep** 是 Mathlib 中的一个缩写定义，位于命名空间 `Matroid`。
形式化陈述：Coindep (M : Matroid α) (I : Set α) : Prop
参数：M : Matroid α；I : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A coindependent set of `M` is an independent set of the dual of `M✶`. we give it
 a separate
  definition to enable dot notation. Which spelling is better depends on context
.
-/
abbrev Coindep (M : Matroid α) (I : Set α) : Prop := M✶.Indep I
/-
**Matroid.coindep_def** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：coindep_def : M.Coindep X ↔ M✶.Indep X
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem coindep_def : M.Coindep X ↔ M✶.Indep X := Iff.rfl
/-
**Matroid.Coindep.indep** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Coindep`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {X : Set α}, M.Coindep X → M✶.Indep X
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Coindep.indep (hX : M.Coindep X) : M✶.Indep X :=
  hX
/-
**Matroid.dual_coindep_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {X : Set α}, M✶.Coindep X ↔ M.Indep X
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.Coindep.eq_1`：∀ {α : Type u_1} (M : Matroid α) (I : Set α), M.Co
indep I = M✶.Indep I
· 使用定理 `Matroid.dual_dual`：∀ {α : Type u_1} (M : Matroid α), M✶✶ = M
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] theorem dual_coindep_iff : M✶.Coindep X ↔ M.Indep X := by
  rw [Coindep, dual_dual]
/-
**Matroid.Indep.coindep** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Indep`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I : Set α}, M.Indep I → M✶.Coindep I
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Matroid.dual_coindep_iff`：∀ {α : Type u_1} {M : Matroid α} {X : Set α}, 
M✶.Coindep X ↔ M.Indep X
-/
theorem Indep.coindep (hI : M.Indep I) : M✶.Coindep I :=
  dual_coindep_iff.2 hI
/-
**Matroid.coindep_iff_exists'** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：coindep_iff_exists' : M.Coindep X ↔ (exists B, M.IsBase B ∧ B subseteq M.E
 \ X) ∧ X subseteq M.E
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Matroid.IsBase.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {B : Set 
α}, M.IsBase B → B ⊆ M.E
· 使用定理 `Disjoint.symm`：Disjoint.symm (x y : Finmap β) (h : Disjoint x y) : Disjo
int y x
-/
theorem coindep_iff_exists' : M.Coindep X ↔ (∃ B, M.IsBase B ∧ B ⊆ M.E \ X) ∧ X ⊆ M.E := by
  simp_rw [Coindep, dual_indep_iff_exists', and_comm (a := (_ : Set α) ⊆ _), and_congr_left_iff,
    subset_sdiff]
  exact fun _ ↦ ⟨fun ⟨B, hB, hXB⟩ ↦ ⟨B, hB, hB.subset_ground, hXB.symm⟩,
    fun ⟨B, hB, _, hBX⟩ ↦ ⟨B, hB, hBX.symm⟩⟩
/-
**Matroid.coindep_iff_exists** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：coindep_iff_exists (hX : X subseteq M.E
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.coindep_iff_exists'`：coindep_iff_exists' : M.Coindep X ↔ (exists
 B, M.IsBase B ∧ B subseteq M.E \ X) ∧ X subseteq M.E
· 使用定理 `and_iff_left`：∀ {b a : Prop}, b → (a ∧ b ↔ a)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem coindep_iff_exists (hX : X ⊆ M.E := by aesop_mat) :
    M.Coindep X ↔ ∃ B, M.IsBase B ∧ B ⊆ M.E \ X := by
  rw [coindep_iff_exists', and_iff_left hX]
/-
**Matroid.coindep_iff_subset_compl_isBase** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：coindep_iff_subset_compl_isBase : M.Coindep X ↔ exists B, M.IsBase B ∧ X s
ubseteq M.E \ B
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Disjoint.symm`：Disjoint.symm (x y : Finmap β) (h : Disjoint x y) : Disjo
int y x
· 使用定理 `Matroid.IsBase.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {B : Set 
α}, M.IsBase B → B ⊆ M.E
-/
theorem coindep_iff_subset_compl_isBase : M.Coindep X ↔ ∃ B, M.IsBase B ∧ X ⊆ M.E \ B := by
  simp_rw [coindep_iff_exists', subset_sdiff]
  exact ⟨fun ⟨⟨B, hB, _, hBX⟩, hX⟩ ↦ ⟨B, hB, hX, hBX.symm⟩,
    fun ⟨B, hB, hXE, hXB⟩ ↦ ⟨⟨B, hB, hB.subset_ground, hXB.symm⟩, hXE⟩⟩

@[aesop unsafe 10% (rule_sets := [Matroid])]
/-
**Matroid.Coindep.subset_ground** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Coindep`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {X : Set α}, M.Coindep X → X ⊆ M.E
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.Indep.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {I : Set α
}, M.Indep I → I ⊆ M.E
· 使用定理 `Matroid.Coindep.indep`：∀ {α : Type u_1} {M : Matroid α} {X : Set α}, M.C
oindep X → M✶.Indep X
-/
theorem Coindep.subset_ground (hX : M.Coindep X) : X ⊆ M.E :=
  hX.indep.subset_ground
/-
**Matroid.Coindep.exists_isBase_subset_compl** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.
Coindep`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {X : Set α}, M.Coindep X → ∃ B, M.IsBase 
B ∧ B ⊆ M.E \ X
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Matroid.coindep_iff_exists`：coindep_iff_exists (hX : X subseteq M.E
· 使用定理 `Matroid.Coindep.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {X : Set
 α}, M.Coindep X → X ⊆ M.E
-/
theorem Coindep.exists_isBase_subset_compl (h : M.Coindep X) : ∃ B, M.IsBase B ∧ B ⊆ M.E \ X :=
  (coindep_iff_exists h.subset_ground).1 h
/-
**Matroid.Coindep.exists_subset_compl_isBase** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.
Coindep`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {X : Set α}, M.Coindep X → ∃ B, M.IsBase 
B ∧ X ⊆ M.E \ B
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Matroid.coindep_iff_subset_compl_isBase`：coindep_iff_subset_compl_isBase
 : M.Coindep X ↔ exists B, M.IsBase B ∧ X subseteq M.E \ B
-/
theorem Coindep.exists_subset_compl_isBase (h : M.Coindep X) : ∃ B, M.IsBase B ∧ X ⊆ M.E \ B :=
  coindep_iff_subset_compl_isBase.1 h

end dual

end Matroid

