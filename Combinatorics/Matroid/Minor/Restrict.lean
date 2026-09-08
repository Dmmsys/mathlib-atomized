/-
Copyright (c) 2023 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson
-/
module

public import Mathlib.Combinatorics.Matroid.Dual

/-!
# Matroid Restriction

Given `M : Matroid α` and `R : Set α`, the independent sets of `M` that are contained in `R`
are the independent sets of another matroid `M ↾ R` with ground set `R`,
called the 'restriction' of `M` to `R`.
For `I ⊆ R ⊆ M.E`, `I` is a basis of `R` in `M` if and only if `I` is a base
of the restriction `M ↾ R`, so this construction relates `Matroid.IsBasis` to `Matroid.IsBase`.

If `N M : Matroid α` satisfy `N = M ↾ R` for some `R ⊆ M.E`,
then we call `N` a 'restriction of `M`', and write `N ≤r M`. This is a partial order.

This file proves that the restriction is a matroid and that the `≤r` order is a partial order,
and gives related API.
It also proves some `Matroid.IsBasis` analogues of `Matroid.IsBase` lemmas that,
while they could be stated in `Data.Matroid.Basic`,
are hard to prove without `Matroid.restrict` API.

## Main Definitions

* `M.restrict R`, written `M ↾ R`, is the restriction of `M : Matroid α` to `R : Set α`: i.e.
  the matroid with ground set `R` whose independent sets are the `M`-independent subsets of `R`.

* `Matroid.Restriction N M`, written `N ≤r M`, means that `N = M ↾ R` for some `R ⊆ M.E`.

* `Matroid.IsStrictRestriction N M`, written `N <r M`, means that `N = M ↾ R` for some `R ⊂ M.E`.

* `Matroidᵣ α` is a type synonym for `Matroid α`, equipped with the `PartialOrder` `≤r`.

## Implementation Notes

Since `R` and `M.E` are both terms in `Set α`, to define the restriction `M ↾ R`,
we need to either insist that `R ⊆ M.E`, or to say what happens when `R` contains the junk
outside `M.E`.

It turns out that `R ⊆ M.E` is just an unnecessary hypothesis; if we say the restriction
`M ↾ R` has ground set `R` and its independent sets are the `M`-independent subsets of `R`,
we always get a matroid, in which the elements of `R \ M.E` aren't in any independent sets.
We could instead define this matroid to always be 'smaller' than `M` by setting
`(M ↾ R).E := R ∩ M.E`, but this is worse definitionally, and more generally less convenient.

This makes it possible to actually restrict a matroid 'upwards'; for instance, if `M : Matroid α`
satisfies `M.E = ∅`, then `M ↾ Set.univ` is the matroid on `α` whose ground set is all of `α`,
where the empty set is the only independent set.
(In general, elements of `R \ M.E` are all 'loops' of the matroid `M ↾ R`;
see `Matroid.loops` and `Matroid.restrict_loops_eq'` for a precise version of this statement.)
This is mathematically strange, but is useful for API building.

The cost of allowing a restriction of `M` to be 'bigger' than `M` itself is that
the statement `M ↾ R ≤r M` is only true with the hypothesis `R ⊆ M.E`
(at least, if we want `≤r` to be a partial order).
But this isn't too inconvenient in practice. Indeed `(· ⊆ M.E)` proofs
can often be automatically provided by `aesop_mat`.

We define the restriction order `≤r` to give a `PartialOrder` instance on the type synonym
`Matroidᵣ α` rather than `Matroid α` itself, because the `PartialOrder (Matroid α)` instance is
reserved for the more mathematically important 'minor' order; see `Matroid.IsMinor`.
-/

@[expose] public section

assert_not_exists Field

open Set

namespace Matroid

variable {α : Type*} {M : Matroid α} {R I X Y : Set α}

section restrict

/-- The `IndepMatroid` whose independent sets are the independent subsets of `R`. -/
/-
**Matroid.restrictIndepMatroid** 是 Mathlib 中的一个定义，位于命名空间 `Matroid`。
形式化陈述：{α : Type u_1} → Matroid α → Set α → IndepMatroid α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `IndepMatroid` whose independent sets are the independent subsets of `R`.
-/
@[simps] def restrictIndepMatroid (M : Matroid α) (R : Set α) : IndepMatroid α where
  E := R
  Indep I := M.Indep I ∧ I ⊆ R
  indep_empty := ⟨M.empty_indep, empty_subset _⟩
  indep_subset := fun _ _ h hIJ ↦ ⟨h.1.subset hIJ, hIJ.trans h.2⟩
  indep_aug := by
    rintro I I' ⟨hI, hIY⟩ (hIn : ¬ M.IsBasis' I R) (hI' : M.IsBasis' I' R)
    rw [isBasis'_iff_isBasis_inter_ground] at hIn hI'
    obtain ⟨B', hB', rfl⟩ := hI'.exists_isBase
    obtain ⟨B, hB, hIB, hBIB'⟩ := hI.exists_isBase_subset_union_isBase hB'
    rw [hB'.inter_isBasis_iff_compl_inter_isBasis_dual, sdiff_inter_sdiff] at hI'
    have hss : M.E \ (B' ∪ (R ∩ M.E)) ⊆ M.E \ (B ∪ (R ∩ M.E)) := by
      apply sdiff_subset_sdiff_right
      rw [union_subset_iff, and_iff_left subset_union_right, union_comm]
      exact hBIB'.trans (union_subset_union_left _ (subset_inter hIY hI.subset_ground))
    have hi : M✶.Indep (M.E \ (B ∪ (R ∩ M.E))) := by
      rw [dual_indep_iff_exists]
      exact ⟨B, hB, disjoint_of_subset_right subset_union_left disjoint_sdiff_left⟩
    have h_eq := hI'.eq_of_subset_indep hi hss
      (sdiff_subset_sdiff_right subset_union_right)
    rw [h_eq, ← sdiff_inter_sdiff, ← hB.inter_isBasis_iff_compl_inter_isBasis_dual] at hI'
    obtain ⟨J, hJ, hIJ⟩ := hI.subset_isBasis_of_subset
      (subset_inter hIB (subset_inter hIY hI.subset_ground))
    obtain rfl := hI'.indep.eq_of_isBasis hJ
    have hIJ' : I ⊂ B ∩ (R ∩ M.E) := hIJ.ssubset_of_ne (fun he ↦ hIn (by rwa [he]))
    obtain ⟨e, he⟩ := exists_of_ssubset hIJ'
    exact ⟨e, ⟨⟨(hBIB' he.1.1).elim (fun h ↦ (he.2 h).elim) id,he.1.2⟩, he.2⟩,
      hI'.indep.subset (insert_subset he.1 hIJ), insert_subset he.1.2.1 hIY⟩
  indep_maximal := by
    rintro A hAR I ⟨hI, _⟩ hIA
    obtain ⟨J, hJ, hIJ⟩ := hI.subset_isBasis'_of_subset hIA
    use J
    simp only [hIJ, and_assoc, maximal_subset_iff, hJ.indep, hJ.subset, and_imp, true_and,
      hJ.subset.trans hAR]
    exact fun K hK _ hKA hJK ↦ hJ.eq_of_subset_indep hK hJK hKA
  subset_ground _ := And.right

/-- Change the ground set of a matroid to some `R : Set α`. The independent sets of the restriction
are the independent subsets of the new ground set. Most commonly used when `R ⊆ M.E`,
but it is convenient not to require this. The elements of `R \ M.E` become 'loops'. -/
/-
**Matroid.restrict** 是 Mathlib 中的一个定义，位于命名空间 `Matroid`。
形式化陈述：restrict (M : Matroid α) (R : Set α) : Matroid α
参数：M : Matroid α；R : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Change the ground set of a matroid to some `R : Set α`. The independent sets of 
the restriction
are the independent subsets of the new ground set. Most commonly used when `R ⊆ 
M.E`,
but it is convenient not to require this. The elements of `R \ M.E` become 'loop
s'.
-/
def restrict (M : Matroid α) (R : Set α) : Matroid α := (M.restrictIndepMatroid R).matroid

/-- `M ↾ R` means `M.restrict R`. -/
scoped infixl:65 " ↾ " => Matroid.restrict

/-
**Matroid.restrict_indep_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {R I : Set α}, (M.restrict R).Indep I ↔ M
.Indep I ∧ I ⊆ R
参数：M.restrict R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] theorem restrict_indep_iff : (M ↾ R).Indep I ↔ M.Indep I ∧ I ⊆ R := Iff.rfl
/-
**Matroid.Indep.indep_restrict_of_subset** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Inde
p`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {R I : Set α}, M.Indep I → I ⊆ R → (M.res
trict R).Indep I
参数：M.restrict R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Matroid.restrict_indep_iff`：∀ {α : Type u_1} {M : Matroid α} {R I : Set 
α}, (M.restrict R).Indep I ↔ M.Indep I ∧ I ⊆ R
-/
theorem Indep.indep_restrict_of_subset (h : M.Indep I) (hIR : I ⊆ R) : (M ↾ R).Indep I :=
  restrict_indep_iff.mpr ⟨h,hIR⟩
/-
**Matroid.Indep.of_restrict** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Indep`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {R I : Set α}, (M.restrict R).Indep I → M
.Indep I
参数：M.restrict R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Matroid.restrict_indep_iff`：∀ {α : Type u_1} {M : Matroid α} {R I : Set 
α}, (M.restrict R).Indep I ↔ M.Indep I ∧ I ⊆ R
-/
theorem Indep.of_restrict (hI : (M ↾ R).Indep I) : M.Indep I :=
  (restrict_indep_iff.1 hI).1
/-
**Matroid.restrict_ground_eq** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {R : Set α}, (M.restrict R).E = R
参数：M.restrict R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem restrict_ground_eq : (M ↾ R).E = R := rfl
/-
**Matroid.restrict_finite** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：restrict_finite {R : Set α} (hR : R.Finite) : (M ↾ R).Finite
参数：hR : R.Finite。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem restrict_finite {R : Set α} (hR : R.Finite) : (M ↾ R).Finite :=
  ⟨hR⟩
/-
**Matroid.restrict_dep_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {R X : Set α}, (M.restrict R).Dep X ↔ ¬M.
Indep X ∧ X ⊆ R
参数：M.restrict R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.Dep.eq_1`：∀ {α : Type u_1} (M : Matroid α) (D : Set α), M.Dep D 
= (¬M.Indep D ∧ D ⊆ M.E)
· 使用定理 `Matroid.restrict_indep_iff`：∀ {α : Type u_1} {M : Matroid α} {R I : Set 
α}, (M.restrict R).Indep I ↔ M.Indep I ∧ I ⊆ R
· 使用定理 `Matroid.restrict_ground_eq`：∀ {α : Type u_1} {M : Matroid α} {R : Set α}
, (M.restrict R).E = R
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Decidable.not_and_iff_not_or_not'`：∀ {b a : Prop} [Decidable b], ¬(a ∧ b
) ↔ ¬a ∨ ¬b
-/
@[simp] theorem restrict_dep_iff : (M ↾ R).Dep X ↔ ¬ M.Indep X ∧ X ⊆ R := by
  rw [Dep, restrict_indep_iff, restrict_ground_eq]; tauto
/-
**Matroid.restrict_ground_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_1} (M : Matroid α), M.restrict M.E = M
参数：M : Matroid α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.ext_indep`：∀ {α : Type u_1} {M₁ M₂ : Matroid α}, M₁.E = M₂.E → (
∀ ⦃I : Set α⦄, I ⊆ M₁.E → (M₁.Indep I ↔ M₂.Indep I)) → M₁ = M₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
@[simp] theorem restrict_ground_eq_self (M : Matroid α) : (M ↾ M.E) = M := by
  refine ext_indep rfl ?_; simp_all
/-
**Matroid.restrict_restrict_eq** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：restrict_restrict_eq {R₁ R₂ : Set α} (M : Matroid α) (hR : R₂ subseteq R₁)
 : (M ↾ R₁) ↾ R₂ = M ↾ R₂
参数：M : Matroid α；hR : R₂ subseteq R₁。
该定理/引理给出了一组等式。
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
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
theorem restrict_restrict_eq {R₁ R₂ : Set α} (M : Matroid α) (hR : R₂ ⊆ R₁) :
    (M ↾ R₁) ↾ R₂ = M ↾ R₂ := by
  refine ext_indep rfl ?_
  simp only [restrict_ground_eq, restrict_indep_iff, and_congr_left_iff, and_iff_left_iff_imp]
  exact fun _ h _ _ ↦ h.trans hR
/-
**Matroid.restrict_idem** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_1} (M : Matroid α) (R : Set α), (M.restrict R).restrict R = 
M.restrict R
参数：M : Matroid α；R : Set α；M.restrict R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.restrict_restrict_eq`：restrict_restrict_eq {R₁ R₂ : Set α} (M : 
Matroid α) (hR : R₂ subseteq R₁) : (M ↾ R₁) ↾ R₂ = M ↾ R₂
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
-/
@[simp] theorem restrict_idem (M : Matroid α) (R : Set α) : M ↾ R ↾ R = M ↾ R := by
  rw [M.restrict_restrict_eq Subset.rfl]
/-
**Matroid.isBase_restrict_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I X : Set α},   autoParam (X ⊆ M.E) Matr
oid.isBase_restrict_iff._auto_1 → ((M.restrict X).IsBase I ↔ M.IsBasis I X)
参数：X ⊆ M.E；(M.restrict X).IsBase I ↔ M.IsBasis I X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_iff_left`：∀ {b a : Prop}, b → (a ∧ b ↔ a)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] theorem isBase_restrict_iff (hX : X ⊆ M.E := by aesop_mat) :
    (M ↾ X).IsBase I ↔ M.IsBasis I X := by
  simp_rw [isBase_iff_maximal_indep, IsBasis, and_iff_left hX, maximal_iff, restrict_indep_iff]
/-
**Matroid.isBase_restrict_iff'** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：isBase_restrict_iff' : (M ↾ X).IsBase I ↔ M.IsBasis' I X
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isBase_restrict_iff' : (M ↾ X).IsBase I ↔ M.IsBasis' I X := by
  simp_rw [isBase_iff_maximal_indep, IsBasis', maximal_iff, restrict_indep_iff]
/-
**Matroid.IsBasis'.isBase_restrict** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBasis'`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, M.IsBasis' I X → (M.restri
ct X).IsBase I
参数：M.restrict X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Matroid.isBase_restrict_iff'`：isBase_restrict_iff' : (M ↾ X).IsBase I ↔ 
M.IsBasis' I X
-/
theorem IsBasis'.isBase_restrict (hI : M.IsBasis' I X) : (M ↾ X).IsBase I :=
  isBase_restrict_iff'.1 hI
/-
**Matroid.IsBasis.restrict_isBase** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBasis`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, M.IsBasis I X → (M.restric
t X).IsBase I
参数：M.restrict X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Matroid.isBase_restrict_iff`：∀ {α : Type u_1} {M : Matroid α} {I X : Set
 α},   autoParam (X ⊆ M.E) Matroid.isBase_restrict_iff._auto_1 → ((M.restrict X)
.IsBase I ↔ M.IsB…
· 使用定理 `Matroid.IsBasis.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {I X : S
et α}, M.IsBasis I X → X ⊆ M.E
-/
theorem IsBasis.restrict_isBase (h : M.IsBasis I X) : (M ↾ X).IsBase I :=
  (isBase_restrict_iff h.subset_ground).2 h
/-
**Matroid.restrict_rankFinite** 是 Mathlib 中的一个实例，位于命名空间 `Matroid`。
形式化陈述：restrict_rankFinite [M.RankFinite] (R : Set α) : (M ↾ R).RankFinite
参数：R : Set α。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.exists_isBase`：∀ {α : Type u_1} (self : Matroid α), ∃ B, self.Is
Base B
· 使用定理 `Matroid.IsBase.rankFinite_of_finite`：∀ {α : Type u_1} {M : Matroid α} {B
 : Set α}, M.IsBase B → B.Finite → M.RankFinite
· 使用定理 `Matroid.Indep.finite`：∀ {α : Type u_1} {M : Matroid α} {I : Set α} [M.Ra
nkFinite], M.Indep I → I.Finite
· 使用定理 `Matroid.Indep.of_restrict`：∀ {α : Type u_1} {M : Matroid α} {R I : Set α
}, (M.restrict R).Indep I → M.Indep I
· 使用定理 `Matroid.IsBase.indep`：∀ {α : Type u_1} {M : Matroid α} {B : Set α}, M.Is
Base B → M.Indep B
-/
instance restrict_rankFinite [M.RankFinite] (R : Set α) : (M ↾ R).RankFinite :=
  let ⟨_, hB⟩ := (M ↾ R).exists_isBase
  hB.rankFinite_of_finite (hB.indep.of_restrict.finite)
/-
**Matroid.restrict_finitary** 是 Mathlib 中的一个实例，位于命名空间 `Matroid`。
形式化陈述：restrict_finitary [Finitary M] (R : Set α) : Finitary (M ↾ R)
参数：R : Set α。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.indep_iff_forall_finite_subset_indep`：indep_iff_forall_finite_su
bset_indep {M : Matroid α} [Finitary M] : M.Indep I ↔ forall J, J subseteq I -> 
J.Finite -> M.Indep J
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
instance restrict_finitary [Finitary M] (R : Set α) : Finitary (M ↾ R) := by
  refine ⟨fun I hI ↦ ?_⟩
  simp only [restrict_indep_iff] at *
  rw [indep_iff_forall_finite_subset_indep]
  exact ⟨fun J hJ hJfin ↦ (hI J hJ hJfin).1,
    fun e heI ↦ singleton_subset_iff.1 (hI _ (by simpa) (toFinite _)).2⟩
/-
**Matroid.IsBasis.isBase_restrict** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBasis`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, M.IsBasis I X → (M.restric
t X).IsBase I
参数：M.restrict X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Matroid.isBase_restrict_iff`：∀ {α : Type u_1} {M : Matroid α} {I X : Set
 α},   autoParam (X ⊆ M.E) Matroid.isBase_restrict_iff._auto_1 → ((M.restrict X)
.IsBase I ↔ M.IsB…
· 使用定理 `Matroid.IsBasis.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {I X : S
et α}, M.IsBasis I X → X ⊆ M.E
-/
@[simp] theorem IsBasis.isBase_restrict (h : M.IsBasis I X) : (M ↾ X).IsBase I :=
  (isBase_restrict_iff h.subset_ground).mpr h
/-
**Matroid.IsBasis.isBasis_restrict_of_subset** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.
IsBasis`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I X Y : Set α}, M.IsBasis I X → X ⊆ Y → 
(M.restrict Y).IsBasis I X
参数：M.restrict Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.isBase_restrict_iff`：∀ {α : Type u_1} {M : Matroid α} {I X : Set
 α},   autoParam (X ⊆ M.E) Matroid.isBase_restrict_iff._auto_1 → ((M.restrict X)
.IsBase I ↔ M.IsB…
· 使用定理 `Matroid.restrict_restrict_eq`：restrict_restrict_eq {R₁ R₂ : Set α} (M : 
Matroid α) (hR : R₂ subseteq R₁) : (M ↾ R₁) ↾ R₂ = M ↾ R₂
· 使用定理 `Matroid.IsBasis.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {I X : S
et α}, M.IsBasis I X → X ⊆ M.E
-/
theorem IsBasis.isBasis_restrict_of_subset (hI : M.IsBasis I X) (hXY : X ⊆ Y) :
    (M ↾ Y).IsBasis I X := by
  rwa [← isBase_restrict_iff, M.restrict_restrict_eq hXY, isBase_restrict_iff]
/-
**Matroid.isBasis'_restrict_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {R I X : Set α}, (M.restrict R).IsBasis' 
I X ↔ M.IsBasis' I (X ∩ R) ∧ I ⊆ R
参数：M.restrict R；X ∩ R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
theorem isBasis'_restrict_iff : (M ↾ R).IsBasis' I X ↔ M.IsBasis' I (X ∩ R) ∧ I ⊆ R := by
  simp_rw [IsBasis', maximal_iff, restrict_indep_iff, subset_inter_iff, and_imp]
  tauto
/-
**Matroid.isBasis_restrict_iff'** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：isBasis_restrict_iff' : (M ↾ R).IsBasis I X ↔ M.IsBasis I (X inter M.E) ∧ 
X subseteq R
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.isBasis_iff_isBasis'_subset_ground`：∀ {α : Type u_1} {M : Matroi
d α} {I X : Set α}, M.IsBasis I X ↔ M.IsBasis' I X ∧ X ⊆ M.E
· 使用定理 `Matroid.isBasis'_restrict_iff`：∀ {α : Type u_1} {M : Matroid α} {R I X :
 Set α}, (M.restrict R).IsBasis' I X ↔ M.IsBasis' I (X ∩ R) ∧ I ⊆ R
· 使用定理 `Matroid.restrict_ground_eq`：∀ {α : Type u_1} {M : Matroid α} {R : Set α}
, (M.restrict R).E = R
· 使用定理 `and_congr_left_iff`：∀ {a c b : Prop}, (a ∧ c ↔ b ∧ c) ↔ c → (a ↔ b)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.isBasis'_iff_isBasis_inter_ground`：∀ {α : Type u_1} {M : Matroid
 α} {I X : Set α}, M.IsBasis' I X ↔ M.IsBasis I (X ∩ M.E)
· 使用定理 `Set.inter_eq_self_of_subset_left`：inter_eq_self_of_subset_left {s t : Se
t α} : s subseteq t -> s inter t = s
· 使用定理 `and_iff_left_iff_imp`：∀ {a b : Prop}, (a ∧ b ↔ a) ↔ a → b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Matroid.IsBasis'.subset`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α},
 M.IsBasis' I X → I ⊆ X
-/
theorem isBasis_restrict_iff' : (M ↾ R).IsBasis I X ↔ M.IsBasis I (X ∩ M.E) ∧ X ⊆ R := by
  rw [isBasis_iff_isBasis'_subset_ground, isBasis'_restrict_iff, restrict_ground_eq,
    and_congr_left_iff, ← isBasis'_iff_isBasis_inter_ground]
  intro hXR
  rw [inter_eq_self_of_subset_left hXR, and_iff_left_iff_imp]
  exact fun h ↦ h.subset.trans hXR
/-
**Matroid.isBasis_restrict_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：isBasis_restrict_iff (hR : R subseteq M.E
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.isBasis_restrict_iff'`：isBasis_restrict_iff' : (M ↾ R).IsBasis I
 X ↔ M.IsBasis I (X inter M.E) ∧ X subseteq R
· 使用定理 `and_congr_left_iff`：∀ {a c b : Prop}, (a ∧ c ↔ b ∧ c) ↔ c → (a ↔ b)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.isBasis'_iff_isBasis_inter_ground`：∀ {α : Type u_1} {M : Matroid
 α} {I X : Set α}, M.IsBasis' I X ↔ M.IsBasis I (X ∩ M.E)
· 使用定理 `Matroid.isBasis'_iff_isBasis`：∀ {α : Type u_1} {M : Matroid α} {I X : Se
t α},   autoParam (X ⊆ M.E) Matroid.isBasis'_iff_isBasis._auto_1 → (M.IsBasis' I
 X ↔ M.IsBasis I X…
· 使用定理 `_private.Mathlib.Combinatorics.Matroid.Basic.0.Matroid.subset_ground_of_
subset`：∀ {α : Type u_1} {M : Matroid α} {X Y : Set α}, X ⊆ Y → Y ⊆ M.E → X ⊆ M.
E
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isBasis_restrict_iff (hR : R ⊆ M.E := by aesop_mat) :
    (M ↾ R).IsBasis I X ↔ M.IsBasis I X ∧ X ⊆ R := by
  rw [isBasis_restrict_iff', and_congr_left_iff]
  intro hXR
  rw [← isBasis'_iff_isBasis_inter_ground, isBasis'_iff_isBasis]
/-
**Matroid.isBasis'_iff_isBasis_restrict_univ** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`
。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, M.IsBasis' I X ↔ (M.restri
ct Set.univ).IsBasis I X
参数：M.restrict Set.univ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.isBasis_restrict_iff'`：isBasis_restrict_iff' : (M ↾ R).IsBasis I
 X ↔ M.IsBasis I (X inter M.E) ∧ X subseteq R
· 使用定理 `Matroid.isBasis'_iff_isBasis_inter_ground`：∀ {α : Type u_1} {M : Matroid
 α} {I X : Set α}, M.IsBasis' I X ↔ M.IsBasis I (X ∩ M.E)
· 使用定理 `and_iff_left`：∀ {b a : Prop}, b → (a ∧ b ↔ a)
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isBasis'_iff_isBasis_restrict_univ : M.IsBasis' I X ↔ (M ↾ univ).IsBasis I X := by
  rw [isBasis_restrict_iff', isBasis'_iff_isBasis_inter_ground, and_iff_left (subset_univ _)]
/-
**Matroid.restrict_eq_restrict_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：restrict_eq_restrict_iff (M M' : Matroid α) (X : Set α) : M ↾ X = M' ↾ X ↔
 forall I, I subseteq X -> (M.Indep I ↔ M'.Indep I)
参数：M M' : Matroid α；X : Set α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `and_iff_left`：∀ {b a : Prop}, b → (a ∧ b ↔ a)
· 使用定理 `Matroid.restrict_indep_iff`：∀ {α : Type u_1} {M : Matroid α} {R I : Set 
α}, (M.restrict R).Indep I ↔ M.Indep I ∧ I ⊆ R
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Matroid.ext_indep`：∀ {α : Type u_1} {M₁ M₂ : Matroid α}, M₁.E = M₂.E → (
∀ ⦃I : Set α⦄, I ⊆ M₁.E → (M₁.Indep I ↔ M₂.Indep I)) → M₁ = M₂
-/
theorem restrict_eq_restrict_iff (M M' : Matroid α) (X : Set α) :
    M ↾ X = M' ↾ X ↔ ∀ I, I ⊆ X → (M.Indep I ↔ M'.Indep I) := by
  refine ⟨fun h I hIX ↦ ?_, fun h ↦ ext_indep rfl fun I (hI : I ⊆ X) ↦ ?_⟩
  · rw [← and_iff_left (a := (M.Indep I)) hIX, ← and_iff_left (a := (M'.Indep I)) hIX,
      ← restrict_indep_iff, h, restrict_indep_iff]
  rw [restrict_indep_iff, and_iff_left hI, restrict_indep_iff, and_iff_left hI, h _ hI]
/-
**Matroid.restrict_eq_self_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {R : Set α}, M.restrict R = M ↔ R = M.E
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matroid.restrict_ground_eq_self`：∀ {α : Type u_1} (M : Matroid α), M.res
trict M.E = M
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem restrict_eq_self_iff : M ↾ R = M ↔ R = M.E :=
  ⟨fun h ↦ by rw [← h]; rfl, fun h ↦ by simp [h]⟩

end restrict

section IsRestriction

variable {N : Matroid α}

/-- `Restriction N M` means that `N = M ↾ R` for some subset `R` of `M.E` -/
/-
**Matroid.IsRestriction** 是 Mathlib 中的一个定义，位于命名空间 `Matroid`。
形式化陈述：IsRestriction (N M : Matroid α) : Prop
参数：N M : Matroid α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Restriction N M` means that `N = M ↾ R` for some subset `R` of `M.E`
-/
def IsRestriction (N M : Matroid α) : Prop := ∃ R ⊆ M.E, N = M ↾ R

/-- `IsStrictRestriction N M` means that `N = M ↾ R` for some strict subset `R` of `M.E` -/
/-
**Matroid.IsStrictRestriction** 是 Mathlib 中的一个定义，位于命名空间 `Matroid`。
形式化陈述：IsStrictRestriction (N M : Matroid α) : Prop
参数：N M : Matroid α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`IsStrictRestriction N M` means that `N = M ↾ R` for some strict subset `R` of `
M.E`
-/
def IsStrictRestriction (N M : Matroid α) : Prop := IsRestriction N M ∧ ¬ IsRestriction M N

/-- `N ≤r M` means that `N` is a `Restriction` of `M`. -/
scoped infix:50 " ≤r " => IsRestriction

/-- `N <r M` means that `N` is a `IsStrictRestriction` of `M`. -/
scoped infix:50 " <r " => IsStrictRestriction

/-- A type synonym for matroids with the isRestriction order.
(The `PartialOrder` on `Matroid α` is reserved for the minor order) -/
/-
**Matroid.Matroid** 是 Mathlib 中的一个结构，位于命名空间 `Matroid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A type synonym for matroids with the isRestriction order.
(The `PartialOrder` on `Matroid α` is reserved for the minor order)
-/
@[ext] structure Matroidᵣ (α : Type*) where ofMatroid ::
  /-- The underlying `Matroid` -/
  toMatroid : Matroid α
/-
**Matroid.** 是 Mathlib 中的一个实例，位于命名空间 `Matroid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {α : Type*} : CoeOut (Matroidᵣ α) (Matroid α) where
  coe := Matroidᵣ.toMatroid
/-
**Matroid.Matroid** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem Matroidᵣ.coe_inj {M₁ M₂ : Matroidᵣ α} :
    (M₁ : Matroid α) = (M₂ : Matroid α) ↔ M₁ = M₂ := Matroidᵣ.ext_iff.symm
/-
**Matroid.** 是 Mathlib 中的一个实例，位于命名空间 `Matroid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {α : Type*} : PartialOrder (Matroidᵣ α) where
  le := (· ≤r ·)
  le_refl M := ⟨(M : Matroid α).E, Subset.rfl, (M : Matroid α).restrict_ground_eq_self.symm⟩
  le_trans M₁ M₂ M₃ := by
    rintro ⟨R, hR, h₁⟩ ⟨R', hR', h₂⟩
    rw [h₂] at h₁ hR
    rw [h₁, restrict_restrict_eq _ (show R ⊆ R' from hR)]
    exact ⟨R, hR.trans hR', rfl⟩
  le_antisymm M₁ M₂ := by
    rintro ⟨R, hR, h⟩ ⟨R', hR', h'⟩
    rw [h', restrict_ground_eq] at hR
    rw [h, restrict_ground_eq] at hR'
    rw [← Matroidᵣ.coe_inj, h, h', hR.antisymm hR', restrict_idem]
/-
**Matroid.Matroid** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] protected theorem Matroidᵣ.le_iff {M M' : Matroidᵣ α} :
    M ≤ M' ↔ (M : Matroid α) ≤r (M' : Matroid α) := Iff.rfl
/-
**Matroid.Matroid** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] protected theorem Matroidᵣ.lt_iff {M M' : Matroidᵣ α} :
    M < M' ↔ (M : Matroid α) <r (M' : Matroid α) := Iff.rfl
/-
**Matroid.ofMatroid_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：ofMatroid_le_iff {M M' : Matroid α} : Matroidᵣ.ofMatroid M <= Matroidᵣ.ofM
atroid M' ↔ M <=r M'
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
theorem ofMatroid_le_iff {M M' : Matroid α} :
    Matroidᵣ.ofMatroid M ≤ Matroidᵣ.ofMatroid M' ↔ M ≤r M' := by
  simp
/-
**Matroid.ofMatroid_lt_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：ofMatroid_lt_iff {M M' : Matroid α} : Matroidᵣ.ofMatroid M < Matroidᵣ.ofMa
troid M' ↔ M <r M'
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
theorem ofMatroid_lt_iff {M M' : Matroid α} :
    Matroidᵣ.ofMatroid M < Matroidᵣ.ofMatroid M' ↔ M <r M' := by
  simp
/-
**Matroid.IsRestriction.refl** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsRestriction`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α}, M.IsRestriction M
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem IsRestriction.refl : M ≤r M :=
  le_refl (Matroidᵣ.ofMatroid M)
/-
**Matroid.IsRestriction.antisymm** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsRestrictio
n`。
形式化陈述：∀ {α : Type u_1} {M M' : Matroid α}, M.IsRestriction M' → M'.IsRestriction
 M → M = M'
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.Matroidᵣ.ofMatroid.injEq`：∀ {α : Type u_2} (toMatroid toMatroid_
1 : Matroid α),   ({ toMatroid := toMatroid } = { toMatroid := toMatroid_1 }) = 
(toMatroid = toMatroid…
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Matroid.ofMatroid_le_iff`：ofMatroid_le_iff {M M' : Matroid α} : Matroidᵣ
.ofMatroid M <= Matroidᵣ.ofMatroid M' ↔ M <=r M'
-/
theorem IsRestriction.antisymm {M' : Matroid α} (h : M ≤r M') (h' : M' ≤r M) : M = M' := by
  simpa using (ofMatroid_le_iff.2 h).antisymm (ofMatroid_le_iff.2 h')
/-
**Matroid.IsRestriction.trans** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsRestriction`。
形式化陈述：∀ {α : Type u_1} {M₁ M₂ M₃ : Matroid α}, M₁.IsRestriction M₂ → M₂.IsRestri
ction M₃ → M₁.IsRestriction M₃
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
-/
theorem IsRestriction.trans {M₁ M₂ M₃ : Matroid α} (h : M₁ ≤r M₂) (h' : M₂ ≤r M₃) : M₁ ≤r M₃ :=
  le_trans (α := Matroidᵣ α) h h'
/-
**Matroid.restrict_isRestriction** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：restrict_isRestriction (M : Matroid α) (R : Set α) (hR : R subseteq M.E
参数：M : Matroid α；R : Set α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem restrict_isRestriction (M : Matroid α) (R : Set α) (hR : R ⊆ M.E := by aesop_mat) :
    M ↾ R ≤r M :=
  ⟨R, hR, rfl⟩
/-
**Matroid.IsRestriction.eq_restrict** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsRestric
tion`。
形式化陈述：∀ {α : Type u_1} {M N : Matroid α}, N.IsRestriction M → M.restrict N.E = N
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.restrict_ground_eq`：∀ {α : Type u_1} {M : Matroid α} {R : Set α}
, (M.restrict R).E = R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem IsRestriction.eq_restrict (h : N ≤r M) : M ↾ N.E = N := by
  obtain ⟨R, -, rfl⟩ := h; rw [restrict_ground_eq]
/-
**Matroid.IsRestriction.subset** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsRestriction`
。
形式化陈述：∀ {α : Type u_1} {M N : Matroid α}, N.IsRestriction M → N.E ⊆ M.E
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem IsRestriction.subset (h : N ≤r M) : N.E ⊆ M.E := by
  obtain ⟨R, hR, rfl⟩ := h; exact hR
/-
**Matroid.IsRestriction.exists_eq_restrict** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Is
Restriction`。
形式化陈述：∀ {α : Type u_1} {M N : Matroid α}, N.IsRestriction M → ∃ R ⊆ M.E, N = M.r
estrict R
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IsRestriction.exists_eq_restrict (h : N ≤r M) : ∃ R ⊆ M.E, N = M ↾ R :=
  h
/-
**Matroid.IsRestriction.of_subset** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsRestricti
on`。
形式化陈述：∀ {α : Type u_1} {R R' : Set α} (M : Matroid α), R ⊆ R' → (M.restrict R).I
sRestriction (M.restrict R')
参数：M : Matroid α；M.restrict R；M.restrict R'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.restrict_restrict_eq`：restrict_restrict_eq {R₁ R₂ : Set α} (M : 
Matroid α) (hR : R₂ subseteq R₁) : (M ↾ R₁) ↾ R₂ = M ↾ R₂
· 使用定理 `Matroid.restrict_isRestriction`：restrict_isRestriction (M : Matroid α) (
R : Set α) (hR : R subseteq M.E
-/
theorem IsRestriction.of_subset {R' : Set α} (M : Matroid α) (h : R ⊆ R') :
    (M ↾ R) ≤r (M ↾ R') := by
  rw [← restrict_restrict_eq M h]; exact restrict_isRestriction _ _ h
/-
**Matroid.isRestriction_iff_exists** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：isRestriction_iff_exists : (N <=r M) ↔ exists R, R subseteq M.E ∧ N = M ↾ 
R
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsRestriction.exists_eq_restrict`：∀ {α : Type u_1} {M N : Matroi
d α}, N.IsRestriction M → ∃ R ⊆ M.E, N = M.restrict R
· 使用定理 `Matroid.restrict_isRestriction`：restrict_isRestriction (M : Matroid α) (
R : Set α) (hR : R subseteq M.E
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem isRestriction_iff_exists : (N ≤r M) ↔ ∃ R, R ⊆ M.E ∧ N = M ↾ R := by
  use IsRestriction.exists_eq_restrict; rintro ⟨R, hR, rfl⟩; exact restrict_isRestriction M R hR
/-
**Matroid.IsStrictRestriction.isRestriction** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.I
sStrictRestriction`。
形式化陈述：∀ {α : Type u_1} {M N : Matroid α}, N.IsStrictRestriction M → N.IsRestrict
ion M
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem IsStrictRestriction.isRestriction (h : N <r M) : N ≤r M :=
  h.1
/-
**Matroid.IsStrictRestriction.ne** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsStrictRest
riction`。
形式化陈述：∀ {α : Type u_1} {M N : Matroid α}, N.IsStrictRestriction M → N ≠ M
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.ofMatroid_lt_iff`：ofMatroid_lt_iff {M M' : Matroid α} : Matroidᵣ
.ofMatroid M < Matroidᵣ.ofMatroid M' ↔ M <r M'
-/
theorem IsStrictRestriction.ne (h : N <r M) : N ≠ M := by
  rintro rfl; rw [← ofMatroid_lt_iff] at h; simp at h
/-
**Matroid.IsStrictRestriction.irrefl** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsStrict
Restriction`。
形式化陈述：∀ {α : Type u_1} (M : Matroid α), ¬M.IsStrictRestriction M
参数：M : Matroid α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsStrictRestriction.ne`：∀ {α : Type u_1} {M N : Matroid α}, N.Is
StrictRestriction M → N ≠ M
-/
theorem IsStrictRestriction.irrefl (M : Matroid α) : ¬ (M <r M) :=
  fun h ↦ h.ne rfl
/-
**Matroid.IsStrictRestriction.ssubset** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsStric
tRestriction`。
形式化陈述：∀ {α : Type u_1} {M N : Matroid α}, N.IsStrictRestriction M → N.E ⊂ M.E
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LE.le.ssubset_of_ne`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst 
: PartialOrder α] {a b : α}, a ⊆ b → a ≠ b → a ⊂ b
· 使用定理 `Matroid.IsRestriction.subset`：∀ {α : Type u_1} {M N : Matroid α}, N.IsRe
striction M → N.E ⊆ M.E
· 使用定理 `Matroid.IsStrictRestriction.isRestriction`：∀ {α : Type u_1} {M N : Matro
id α}, N.IsStrictRestriction M → N.IsRestriction M
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.restrict_idem`：∀ {α : Type u_1} (M : Matroid α) (R : Set α), (M.
restrict R).restrict R = M.restrict R
· 使用定理 `Matroid.restrict_ground_eq_self`：∀ {α : Type u_1} (M : Matroid α), M.res
trict M.E = M
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem IsStrictRestriction.ssubset (h : N <r M) : N.E ⊂ M.E := by
  obtain ⟨R, -, rfl⟩ := h.1
  refine h.isRestriction.subset.ssubset_of_ne (fun h' ↦ h.2 ⟨R, Subset.rfl, ?_⟩)
  rw [show R = M.E from h', restrict_idem, restrict_ground_eq_self]
/-
**Matroid.IsStrictRestriction.eq_restrict** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsS
trictRestriction`。
形式化陈述：∀ {α : Type u_1} {M N : Matroid α}, N.IsStrictRestriction M → M.restrict N
.E = N
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsRestriction.eq_restrict`：∀ {α : Type u_1} {M N : Matroid α}, N
.IsRestriction M → M.restrict N.E = N
· 使用定理 `Matroid.IsStrictRestriction.isRestriction`：∀ {α : Type u_1} {M N : Matro
id α}, N.IsStrictRestriction M → N.IsRestriction M
-/
theorem IsStrictRestriction.eq_restrict (h : N <r M) : M ↾ N.E = N :=
  h.isRestriction.eq_restrict
/-
**Matroid.IsStrictRestriction.exists_eq_restrict** 是 Mathlib 中的一个定理，位于命名空间 `Matr
oid.IsStrictRestriction`。
形式化陈述：∀ {α : Type u_1} {M N : Matroid α}, N.IsStrictRestriction M → ∃ R ⊂ M.E, N
 = M.restrict R
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsStrictRestriction.ssubset`：∀ {α : Type u_1} {M N : Matroid α},
 N.IsStrictRestriction M → N.E ⊂ M.E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.IsStrictRestriction.eq_restrict`：∀ {α : Type u_1} {M N : Matroid
 α}, N.IsStrictRestriction M → M.restrict N.E = N
-/
theorem IsStrictRestriction.exists_eq_restrict (h : N <r M) : ∃ R, R ⊂ M.E ∧ N = M ↾ R :=
  ⟨N.E, h.ssubset, by rw [h.eq_restrict]⟩
/-
**Matroid.IsRestriction.isStrictRestriction_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `Mat
roid.IsRestriction`。
形式化陈述：∀ {α : Type u_1} {M N : Matroid α}, N.IsRestriction M → N ≠ M → N.IsStrict
Restriction M
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsRestriction.antisymm`：∀ {α : Type u_1} {M M' : Matroid α}, M.I
sRestriction M' → M'.IsRestriction M → M = M'
-/
theorem IsRestriction.isStrictRestriction_of_ne (h : N ≤r M) (hne : N ≠ M) : N <r M :=
  ⟨h, fun h' ↦ hne <| h.antisymm h'⟩
/-
**Matroid.IsRestriction.eq_or_isStrictRestriction** 是 Mathlib 中的一个定理，位于命名空间 `Mat
roid.IsRestriction`。
形式化陈述：∀ {α : Type u_1} {M N : Matroid α}, N.IsRestriction M → N = M ∨ N.IsStrict
Restriction M
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.Matroidᵣ.ofMatroid.injEq`：∀ {α : Type u_2} (toMatroid toMatroid_
1 : Matroid α),   ({ toMatroid := toMatroid } = { toMatroid := toMatroid_1 }) = 
(toMatroid = toMatroid…
· 使用定理 `eq_or_lt_of_le`：eq_or_lt_of_le (h : a <= b) : a = b ∨ a < b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Matroid.ofMatroid_le_iff`：ofMatroid_le_iff {M M' : Matroid α} : Matroidᵣ
.ofMatroid M <= Matroidᵣ.ofMatroid M' ↔ M <=r M'
-/
theorem IsRestriction.eq_or_isStrictRestriction (h : N ≤r M) : N = M ∨ N <r M := by
  simpa using eq_or_lt_of_le (ofMatroid_le_iff.2 h)
/-
**Matroid.restrict_isStrictRestriction** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：restrict_isStrictRestriction {M : Matroid α} (hR : R ⊂ M.E) : M ↾ R <r M
参数：hR : R ⊂ M.E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsRestriction.isStrictRestriction_of_ne`：∀ {α : Type u_1} {M N :
 Matroid α}, N.IsRestriction M → N ≠ M → N.IsStrictRestriction M
· 使用定理 `Matroid.restrict_isRestriction`：restrict_isRestriction (M : Matroid α) (
R : Set α) (hR : R subseteq M.E
· 使用定理 `LT.lt.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preor
der α] {a b : α}, a ⊂ b → a ⊆ b
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.restrict_ground_eq`：∀ {α : Type u_1} {M : Matroid α} {R : Set α}
, (M.restrict R).E = R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem restrict_isStrictRestriction {M : Matroid α} (hR : R ⊂ M.E) : M ↾ R <r M := by
  refine (M.restrict_isRestriction R hR.subset).isStrictRestriction_of_ne (fun h ↦ ?_)
  rw [← h, restrict_ground_eq] at hR
  exact hR.ne rfl
/-
**Matroid.IsRestriction.isStrictRestriction_of_ground_ne** 是 Mathlib 中的一个定理，位于命名
空间 `Matroid.IsRestriction`。
形式化陈述：∀ {α : Type u_1} {M N : Matroid α}, N.IsRestriction M → N.E ≠ M.E → N.IsSt
rictRestriction M
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.IsRestriction.eq_restrict`：∀ {α : Type u_1} {M N : Matroid α}, N
.IsRestriction M → M.restrict N.E = N
· 使用定理 `Matroid.restrict_isStrictRestriction`：restrict_isStrictRestriction {M : 
Matroid α} (hR : R ⊂ M.E) : M ↾ R <r M
· 使用定理 `LE.le.ssubset_of_ne`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst 
: PartialOrder α] {a b : α}, a ⊆ b → a ≠ b → a ⊂ b
· 使用定理 `Matroid.IsRestriction.subset`：∀ {α : Type u_1} {M N : Matroid α}, N.IsRe
striction M → N.E ⊆ M.E
-/
theorem IsRestriction.isStrictRestriction_of_ground_ne (h : N ≤r M) (hne : N.E ≠ M.E) : N <r M := by
  rw [← h.eq_restrict]
  exact restrict_isStrictRestriction (h.subset.ssubset_of_ne hne)
/-
**Matroid.IsStrictRestriction.of_ssubset** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsSt
rictRestriction`。
形式化陈述：∀ {α : Type u_1} {R R' : Set α} (M : Matroid α), R ⊂ R' → (M.restrict R).I
sStrictRestriction (M.restrict R')
参数：M : Matroid α；M.restrict R；M.restrict R'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsRestriction.isStrictRestriction_of_ground_ne`：∀ {α : Type u_1}
 {M N : Matroid α}, N.IsRestriction M → N.E ≠ M.E → N.IsStrictRestriction M
· 使用定理 `Matroid.IsRestriction.of_subset`：∀ {α : Type u_1} {R R' : Set α} (M : Ma
troid α), R ⊆ R' → (M.restrict R).IsRestriction (M.restrict R')
· 使用定理 `LT.lt.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preor
der α] {a b : α}, a ⊂ b → a ⊆ b
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
-/
theorem IsStrictRestriction.of_ssubset {R' : Set α} (M : Matroid α) (h : R ⊂ R') :
    (M ↾ R) <r (M ↾ R') :=
  (IsRestriction.of_subset M h.subset).isStrictRestriction_of_ground_ne h.ne
/-
**Matroid.IsRestriction.finite** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsRestriction`
。
形式化陈述：∀ {α : Type u_1} {N M : Matroid α} [M.Finite], N.IsRestriction M → N.Finit
e
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.restrict_finite`：restrict_finite {R : Set α} (hR : R.Finite) : (
M ↾ R).Finite
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Matroid.ground_finite`：ground_finite (M : Matroid α) [M.Finite] : M.E.Fi
nite
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem IsRestriction.finite {M : Matroid α} [M.Finite] (h : N ≤r M) : N.Finite := by
  obtain ⟨R, hR, rfl⟩ := h
  exact restrict_finite <| M.ground_finite.subset hR
/-
**Matroid.IsRestriction.rankFinite** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsRestrict
ion`。
形式化陈述：∀ {α : Type u_1} {N M : Matroid α} [M.RankFinite], N.IsRestriction M → N.R
ankFinite
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem IsRestriction.rankFinite {M : Matroid α} [RankFinite M] (h : N ≤r M) : N.RankFinite := by
  obtain ⟨R, -, rfl⟩ := h
  infer_instance
/-
**Matroid.IsRestriction.finitary** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsRestrictio
n`。
形式化陈述：∀ {α : Type u_1} {N M : Matroid α} [M.Finitary], N.IsRestriction M → N.Fin
itary
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem IsRestriction.finitary {M : Matroid α} [Finitary M] (h : N ≤r M) : N.Finitary := by
  obtain ⟨R, -, rfl⟩ := h
  infer_instance
/-
**Matroid.finite_setOfPred_isRestriction** 是 Mathlib 中的一个定理，位于命名空间 `Matroid`。
形式化陈述：finite_setOfPred_isRestriction (M : Matroid α) [M.Finite] : {N | N <=r M}.
Finite
参数：M : Matroid α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Set.Finite.image`：∀ {α : Type u} {β : Type v} {s : Set α} (f : α → β), s
.Finite → (f '' s).Finite
· 使用定理 `Set.Finite.finite_subsets`：∀ {α : Type u} {a : Set α}, a.Finite → {b | b
 ⊆ a}.Finite
· 使用定理 `Matroid.ground_finite`：ground_finite (M : Matroid α) [M.Finite] : M.E.Fi
nite
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem finite_setOfPred_isRestriction (M : Matroid α) [M.Finite] : {N | N ≤r M}.Finite :=
  (M.ground_finite.finite_subsets.image (fun R ↦ M ↾ R)).subset <|
    by rintro _ ⟨R, hR, rfl⟩; exact ⟨_, hR, rfl⟩

@[deprecated (since := "2026-07-09")]
alias finite_setOf_isRestriction := finite_setOfPred_isRestriction
/-
**Matroid.Indep.of_isRestriction** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Indep`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I : Set α} {N : Matroid α}, N.Indep I → 
N.IsRestriction M → M.Indep I
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.Indep.of_restrict`：∀ {α : Type u_1} {M : Matroid α} {R I : Set α
}, (M.restrict R).Indep I → M.Indep I
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem Indep.of_isRestriction (hI : N.Indep I) (hNM : N ≤r M) : M.Indep I := by
  obtain ⟨R, -, rfl⟩ := hNM; exact hI.of_restrict
/-
**Matroid.Indep.indep_isRestriction** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Indep`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I : Set α} {N : Matroid α}, M.Indep I → 
N.IsRestriction M → I ⊆ N.E → N.Indep I
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem Indep.indep_isRestriction (hI : M.Indep I) (hNM : N ≤r M) (hIN : I ⊆ N.E) : N.Indep I := by
  obtain ⟨R, -, rfl⟩ := hNM; simpa [hI]
/-
**Matroid.IsRestriction.indep_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsRestricti
on`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I : Set α} {N : Matroid α}, N.IsRestrict
ion M → (N.Indep I ↔ M.Indep I ∧ I ⊆ N.E)
参数：N.Indep I ↔ M.Indep I ∧ I ⊆ N.E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.Indep.of_isRestriction`：∀ {α : Type u_1} {M : Matroid α} {I : Se
t α} {N : Matroid α}, N.Indep I → N.IsRestriction M → M.Indep I
· 使用定理 `Matroid.Indep.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {I : Set α
}, M.Indep I → I ⊆ M.E
· 使用定理 `Matroid.Indep.indep_isRestriction`：∀ {α : Type u_1} {M : Matroid α} {I :
 Set α} {N : Matroid α}, M.Indep I → N.IsRestriction M → I ⊆ N.E → N.Indep I
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem IsRestriction.indep_iff (hMN : N ≤r M) : N.Indep I ↔ M.Indep I ∧ I ⊆ N.E :=
  ⟨fun h ↦ ⟨h.of_isRestriction hMN, h.subset_ground⟩, fun h ↦ h.1.indep_isRestriction hMN h.2⟩
/-
**Matroid.IsBasis.isBasis_isRestriction** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBas
is`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I X : Set α} {N : Matroid α},   M.IsBasi
s I X → N.IsRestriction M → X ⊆ N.E → N.IsBasis I X
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.isBasis_restrict_iff`：isBasis_restrict_iff (hR : R subseteq M.E
· 使用定理 `and_iff_left`：∀ {b a : Prop}, b → (a ∧ b ↔ a)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem IsBasis.isBasis_isRestriction (hI : M.IsBasis I X) (hNM : N ≤r M) (hX : X ⊆ N.E) :
    N.IsBasis I X := by
  obtain ⟨R, hR, rfl⟩ := hNM; rwa [isBasis_restrict_iff, and_iff_left (show X ⊆ R from hX)]
/-
**Matroid.IsBasis.of_isRestriction** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBasis`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I X : Set α} {N : Matroid α}, N.IsBasis 
I X → N.IsRestriction M → M.IsBasis I X
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Matroid.isBasis_restrict_iff`：isBasis_restrict_iff (hR : R subseteq M.E
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem IsBasis.of_isRestriction (hI : N.IsBasis I X) (hNM : N ≤r M) : M.IsBasis I X := by
  obtain ⟨R, hR, rfl⟩ := hNM; exact ((isBasis_restrict_iff hR).1 hI).1
/-
**Matroid.IsBase.isBasis_of_isRestriction** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsB
ase`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I : Set α} {N : Matroid α}, N.IsBase I →
 N.IsRestriction M → M.IsBasis I N.E
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.isBase_restrict_iff`：∀ {α : Type u_1} {M : Matroid α} {I X : Set
 α},   autoParam (X ⊆ M.E) Matroid.isBase_restrict_iff._auto_1 → ((M.restrict X)
.IsBase I ↔ M.IsB…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem IsBase.isBasis_of_isRestriction (hI : N.IsBase I) (hNM : N ≤r M) : M.IsBasis I N.E := by
  obtain ⟨R, hR, rfl⟩ := hNM; rwa [isBase_restrict_iff] at hI
/-
**Matroid.IsRestriction.base_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsRestrictio
n`。
形式化陈述：∀ {α : Type u_1} {M N : Matroid α}, N.IsRestriction M → ∀ {B : Set α}, N.I
sBase B ↔ M.IsBasis B N.E
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsBase.isBasis_of_isRestriction`：∀ {α : Type u_1} {M : Matroid α
} {I : Set α} {N : Matroid α}, N.IsBase I → N.IsRestriction M → M.IsBasis I N.E
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.IsRestriction.eq_restrict`：∀ {α : Type u_1} {M N : Matroid α}, N
.IsRestriction M → M.restrict N.E = N
· 使用定理 `Matroid.IsBasis.restrict_isBase`：∀ {α : Type u_1} {M : Matroid α} {I X :
 Set α}, M.IsBasis I X → (M.restrict X).IsBase I
-/
theorem IsRestriction.base_iff (hMN : N ≤r M) {B : Set α} : N.IsBase B ↔ M.IsBasis B N.E :=
  ⟨fun h ↦ IsBase.isBasis_of_isRestriction h hMN,
    fun h ↦ by simpa [hMN.eq_restrict] using h.restrict_isBase⟩
/-
**Matroid.IsRestriction.isBasis_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsRestric
tion`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I X : Set α} {N : Matroid α},   N.IsRest
riction M → (N.IsBasis I X ↔ M.IsBasis I X ∧ X ⊆ N.E)
参数：N.IsBasis I X ↔ M.IsBasis I X ∧ X ⊆ N.E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsBasis.of_isRestriction`：∀ {α : Type u_1} {M : Matroid α} {I X 
: Set α} {N : Matroid α}, N.IsBasis I X → N.IsRestriction M → M.IsBasis I X
· 使用定理 `Matroid.IsBasis.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {I X : S
et α}, M.IsBasis I X → X ⊆ M.E
· 使用定理 `Matroid.IsBasis.isBasis_isRestriction`：∀ {α : Type u_1} {M : Matroid α} 
{I X : Set α} {N : Matroid α},   M.IsBasis I X → N.IsRestriction M → X ⊆ N.E → N
.IsBasis I X
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem IsRestriction.isBasis_iff (hMN : N ≤r M) : N.IsBasis I X ↔ M.IsBasis I X ∧ X ⊆ N.E :=
  ⟨fun h ↦ ⟨h.of_isRestriction hMN, h.subset_ground⟩, fun h ↦ h.1.isBasis_isRestriction hMN h.2⟩
/-
**Matroid.Dep.of_isRestriction** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Dep`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {X : Set α} {N : Matroid α}, N.Dep X → N.
IsRestriction M → M.Dep X
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.restrict_dep_iff`：∀ {α : Type u_1} {M : Matroid α} {R X : Set α}
, (M.restrict R).Dep X ↔ ¬M.Indep X ∧ X ⊆ R
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem Dep.of_isRestriction (hX : N.Dep X) (hNM : N ≤r M) : M.Dep X := by
  obtain ⟨R, hR, rfl⟩ := hNM
  rw [restrict_dep_iff] at hX
  exact ⟨hX.1, hX.2.trans hR⟩
/-
**Matroid.Dep.dep_isRestriction** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Dep`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {X : Set α} {N : Matroid α},   M.Dep X → 
N.IsRestriction M → autoParam (X ⊆ N.E) Matroid.Dep.dep_isRestriction._auto_1 → 
N.Dep X
参数：X ⊆ N.E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Matroid.Dep.not_indep`：∀ {α : Type u_1} {M : Matroid α} {D : Set α}, M.D
ep D → ¬M.Indep D
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem Dep.dep_isRestriction (hX : M.Dep X) (hNM : N ≤r M) (hXE : X ⊆ N.E := by aesop_mat) :
    N.Dep X := by
  obtain ⟨R, -, rfl⟩ := hNM; simpa [hX.not_indep]
/-
**Matroid.IsRestriction.dep_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsRestriction
`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {X : Set α} {N : Matroid α}, N.IsRestrict
ion M → (N.Dep X ↔ M.Dep X ∧ X ⊆ N.E)
参数：N.Dep X ↔ M.Dep X ∧ X ⊆ N.E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.Dep.of_isRestriction`：∀ {α : Type u_1} {M : Matroid α} {X : Set 
α} {N : Matroid α}, N.Dep X → N.IsRestriction M → M.Dep X
· 使用定理 `Matroid.Dep.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {D : Set α},
 M.Dep D → D ⊆ M.E
· 使用定理 `Matroid.Dep.dep_isRestriction`：∀ {α : Type u_1} {M : Matroid α} {X : Set
 α} {N : Matroid α},   M.Dep X → N.IsRestriction M → autoParam (X ⊆ N.E) Matroid
.Dep.dep_isRestrict…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem IsRestriction.dep_iff (hMN : N ≤r M) : N.Dep X ↔ M.Dep X ∧ X ⊆ N.E :=
  ⟨fun h ↦ ⟨h.of_isRestriction hMN, h.subset_ground⟩, fun h ↦ h.1.dep_isRestriction hMN h.2⟩

end IsRestriction

/-!
### `IsBasis` and `Base`
The lemmas below exploit the fact that `(M ↾ X).Base I ↔ M.IsBasis I X` to transfer facts about
`Matroid.Base` to facts about `Matroid.IsBasis`.
Their statements thematically belong in `Data.Matroid.Basic`, but they appear here because their
proofs depend on the API for `Matroid.restrict`,
-/

section IsBasis

variable {B J : Set α} {e : α}

/-
**Matroid.IsBasis.transfer** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBasis`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I X Y J : Set α},   M.IsBasis I X → M.Is
Basis J X → X ⊆ Y → M.IsBasis J Y → M.IsBasis I Y
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.isBase_restrict_iff`：∀ {α : Type u_1} {M : Matroid α} {I X : Set
 α},   autoParam (X ⊆ M.E) Matroid.isBase_restrict_iff._auto_1 → ((M.restrict X)
.IsBase I ↔ M.IsB…
· 使用定理 `Matroid.IsBasis.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {I X : S
et α}, M.IsBasis I X → X ⊆ M.E
· 使用定理 `Matroid.IsBase.isBase_of_isBasis_superset`：∀ {α : Type u_1} {M : Matroid
 α} {B I X : Set α}, M.IsBase B → B ⊆ X → M.IsBasis I X → M.IsBase I
· 使用定理 `Matroid.IsBasis.subset`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, 
M.IsBasis I X → I ⊆ X
· 使用定理 `Matroid.IsBasis.isBasis_restrict_of_subset`：∀ {α : Type u_1} {M : Matroi
d α} {I X Y : Set α}, M.IsBasis I X → X ⊆ Y → (M.restrict Y).IsBasis I X
-/
theorem IsBasis.transfer (hIX : M.IsBasis I X) (hJX : M.IsBasis J X) (hXY : X ⊆ Y)
    (hJY : M.IsBasis J Y) : M.IsBasis I Y := by
  rw [← isBase_restrict_iff]; rw [← isBase_restrict_iff] at hJY
  exact hJY.isBase_of_isBasis_superset hJX.subset (hIX.isBasis_restrict_of_subset hXY)
/-
**Matroid.IsBasis.isBasis_of_isBasis_of_subset_of_subset** 是 Mathlib 中的一个定理，位于命名
空间 `Matroid.IsBasis`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I X Y J : Set α}, M.IsBasis I X → M.IsBa
sis J Y → J ⊆ X → I ⊆ Y → M.IsBasis I Y
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsBasis.isBasis_subset`：∀ {α : Type u_1} {M : Matroid α} {I X Y 
: Set α}, M.IsBasis I X → I ⊆ Y → Y ⊆ X → M.IsBasis I Y
· 使用定理 `Set.subset_inter`：subset_inter {s t r : Set α} (rs : r subseteq s) (rt :
 r subseteq t) : r subseteq s inter t
· 使用定理 `Matroid.IsBasis.subset`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}, 
M.IsBasis I X → I ⊆ X
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `Matroid.IsBasis.transfer`：∀ {α : Type u_1} {M : Matroid α} {I X Y J : Se
t α},   M.IsBasis I X → M.IsBasis J X → X ⊆ Y → M.IsBasis J Y → M.IsBasis I Y
-/
theorem IsBasis.isBasis_of_isBasis_of_subset_of_subset (hI : M.IsBasis I X) (hJ : M.IsBasis J Y)
    (hJX : J ⊆ X) (hIY : I ⊆ Y) : M.IsBasis I Y := by
  have hI' := hI.isBasis_subset (subset_inter hI.subset hIY) inter_subset_left
  have hJ' := hJ.isBasis_subset (subset_inter hJX hJ.subset) inter_subset_right
  exact hI'.transfer hJ' inter_subset_right hJ
/-
**Matroid.Indep.exists_isBasis_subset_union_isBasis** 是 Mathlib 中的一个定理，位于命名空间 `M
atroid.Indep`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I X J : Set α},   M.Indep I → I ⊆ X → M.
IsBasis J X → ∃ I', M.IsBasis I' X ∧ I ⊆ I' ∧ I' ⊆ I ∪ J
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.Indep.exists_isBase_subset_union_isBase`：∀ {α : Type u_1} {M : M
atroid α} {B I : Set α}, M.Indep I → M.IsBase B → ∃ B', M.IsBase B' ∧ I ⊆ B' ∧ B
' ⊆ I ∪ B
· 使用定理 `Matroid.Indep.indep_restrict_of_subset`：∀ {α : Type u_1} {M : Matroid α}
 {R I : Set α}, M.Indep I → I ⊆ R → (M.restrict R).Indep I
· 使用定理 `Matroid.IsBasis.isBase_restrict`：∀ {α : Type u_1} {M : Matroid α} {I X :
 Set α}, M.IsBasis I X → (M.restrict X).IsBase I
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.isBase_restrict_iff`：∀ {α : Type u_1} {M : Matroid α} {I X : Set
 α},   autoParam (X ⊆ M.E) Matroid.isBase_restrict_iff._auto_1 → ((M.restrict X)
.IsBase I ↔ M.IsB…
· 使用定理 `Matroid.IsBasis.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {I X : S
et α}, M.IsBasis I X → X ⊆ M.E
-/
theorem Indep.exists_isBasis_subset_union_isBasis (hI : M.Indep I) (hIX : I ⊆ X)
    (hJ : M.IsBasis J X) : ∃ I', M.IsBasis I' X ∧ I ⊆ I' ∧ I' ⊆ I ∪ J := by
  obtain ⟨I', hI', hII', hI'IJ⟩ :=
    (hI.indep_restrict_of_subset hIX).exists_isBase_subset_union_isBase (IsBasis.isBase_restrict hJ)
  rw [isBase_restrict_iff] at hI'
  exact ⟨I', hI', hII', hI'IJ⟩
/-
**Matroid.Indep.exists_insert_of_not_isBasis** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.
Indep`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I X J : Set α},   M.Indep I → I ⊆ X → ¬M
.IsBasis I X → M.IsBasis J X → ∃ e ∈ J \ I, M.Indep (insert e I)
参数：insert e I。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.Indep.exists_insert_of_not_isBase`：∀ {α : Type u_1} {M : Matroid
 α} {B I : Set α}, M.Indep I → ¬M.IsBase I → M.IsBase B → ∃ e ∈ B \ I, M.Indep (
insert e I)
· 使用定理 `Matroid.Indep.indep_restrict_of_subset`：∀ {α : Type u_1} {M : Matroid α}
 {R I : Set α}, M.Indep I → I ⊆ R → (M.restrict R).Indep I
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.isBase_restrict_iff`：∀ {α : Type u_1} {M : Matroid α} {I X : Set
 α},   autoParam (X ⊆ M.E) Matroid.isBase_restrict_iff._auto_1 → ((M.restrict X)
.IsBase I ↔ M.IsB…
· 使用定理 `Matroid.IsBasis.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {I X : S
et α}, M.IsBasis I X → X ⊆ M.E
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Matroid.restrict_indep_iff`：∀ {α : Type u_1} {M : Matroid α} {R I : Set 
α}, (M.restrict R).Indep I ↔ M.Indep I ∧ I ⊆ R
-/
theorem Indep.exists_insert_of_not_isBasis (hI : M.Indep I) (hIX : I ⊆ X) (hI' : ¬M.IsBasis I X)
    (hJ : M.IsBasis J X) : ∃ e ∈ J \ I, M.Indep (insert e I) := by
  rw [← isBase_restrict_iff] at hI'; rw [← isBase_restrict_iff] at hJ
  obtain ⟨e, he, hi⟩ := (hI.indep_restrict_of_subset hIX).exists_insert_of_not_isBase hI' hJ
  exact ⟨e, he, (restrict_indep_iff.mp hi).1⟩
/-
**Matroid.IsBasis.isBase_of_isBase_subset** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsB
asis`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I X B : Set α}, M.IsBasis I X → M.IsBase
 B → B ⊆ X → M.IsBase I
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsBase.isBase_of_isBasis_superset`：∀ {α : Type u_1} {M : Matroid
 α} {B I X : Set α}, M.IsBase B → B ⊆ X → M.IsBasis I X → M.IsBase I
-/
theorem IsBasis.isBase_of_isBase_subset (hIX : M.IsBasis I X) (hB : M.IsBase B) (hBX : B ⊆ X) :
    M.IsBase I :=
  hB.isBase_of_isBasis_superset hBX hIX
/-
**Matroid.IsBasis.exchange** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBasis`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I X J : Set α} {e : α},   M.IsBasis I X 
→ M.IsBasis J X → e ∈ I \ J → ∃ f ∈ J \ I, M.IsBasis (insert f (I \ {e})) X
参数：insert f (I \ {e})。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsBase.exchange`：∀ {α : Type u_1} {M : Matroid α} {B₁ B₂ : Set α
} {e : α},   M.IsBase B₁ → M.IsBase B₂ → e ∈ B₁ \ B₂ → ∃ y ∈ B₂ \ B₁, M.IsBase (
insert y (B₁ …
· 使用定理 `Matroid.IsBasis.restrict_isBase`：∀ {α : Type u_1} {M : Matroid α} {I X :
 Set α}, M.IsBasis I X → (M.restrict X).IsBase I
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matroid.isBase_restrict_iff`：∀ {α : Type u_1} {M : Matroid α} {I X : Set
 α},   autoParam (X ⊆ M.E) Matroid.isBase_restrict_iff._auto_1 → ((M.restrict X)
.IsBase I ↔ M.IsB…
· 使用定理 `Matroid.IsBasis.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {I X : S
et α}, M.IsBasis I X → X ⊆ M.E
-/
theorem IsBasis.exchange (hIX : M.IsBasis I X) (hJX : M.IsBasis J X) (he : e ∈ I \ J) :
    ∃ f ∈ J \ I, M.IsBasis (insert f (I \ {e})) X := by
  obtain ⟨y, hy, h⟩ := hIX.restrict_isBase.exchange hJX.restrict_isBase he
  exact ⟨y, hy, by rwa [isBase_restrict_iff] at h⟩
/-
**Matroid.IsBasis.eq_exchange_of_sdiff_eq_singleton** 是 Mathlib 中的一个定理，位于命名空间 `M
atroid.IsBasis`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I X J : Set α} {e : α},   M.IsBasis I X 
→ M.IsBasis J X → I \ J = {e} → ∃ f ∈ J \ I, J = insert f I \ {e}
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsBase.eq_exchange_of_sdiff_eq_singleton`：∀ {α : Type u_1} {M : 
Matroid α} {B B' : Set α} {e : α},   M.IsBase B → M.IsBase B' → B \ B' = {e} → ∃
 f ∈ B' \ B, B' = insert f B \ {e}
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.isBase_restrict_iff`：∀ {α : Type u_1} {M : Matroid α} {I X : Set
 α},   autoParam (X ⊆ M.E) Matroid.isBase_restrict_iff._auto_1 → ((M.restrict X)
.IsBase I ↔ M.IsB…
· 使用定理 `Matroid.IsBasis.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {I X : S
et α}, M.IsBasis I X → X ⊆ M.E
-/
theorem IsBasis.eq_exchange_of_sdiff_eq_singleton (hI : M.IsBasis I X) (hJ : M.IsBasis J X)
    (hIJ : I \ J = {e}) : ∃ f ∈ J \ I, J = insert f I \ {e} := by
  rw [← isBase_restrict_iff] at hI hJ; exact hI.eq_exchange_of_sdiff_eq_singleton hJ hIJ

@[deprecated (since := "2026-06-03")]
alias IsBasis.eq_exchange_of_diff_eq_singleton := IsBasis.eq_exchange_of_sdiff_eq_singleton
/-
**Matroid.IsBasis'.encard_eq_encard** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBasis'`
。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I X J : Set α}, M.IsBasis' I X → M.IsBas
is' J X → I.encard = J.encard
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsBase.encard_eq_encard_of_isBase`：∀ {α : Type u_1} {M : Matroid
 α} {B₁ B₂ : Set α}, M.IsBase B₁ → M.IsBase B₂ → B₁.encard = B₂.encard
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.isBase_restrict_iff'`：isBase_restrict_iff' : (M ↾ X).IsBase I ↔ 
M.IsBasis' I X
-/
theorem IsBasis'.encard_eq_encard (hI : M.IsBasis' I X) (hJ : M.IsBasis' J X) :
    I.encard = J.encard := by
  rw [← isBase_restrict_iff'] at hI hJ; exact hI.encard_eq_encard_of_isBase hJ
/-
**Matroid.IsBasis.encard_eq_encard** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.IsBasis`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I X J : Set α}, M.IsBasis I X → M.IsBasi
s J X → I.encard = J.encard
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.IsBasis'.encard_eq_encard`：∀ {α : Type u_1} {M : Matroid α} {I X
 J : Set α}, M.IsBasis' I X → M.IsBasis' J X → I.encard = J.encard
· 使用定理 `Matroid.IsBasis.isBasis'`：∀ {α : Type u_1} {M : Matroid α} {I X : Set α}
, M.IsBasis I X → M.IsBasis' I X
-/
theorem IsBasis.encard_eq_encard (hI : M.IsBasis I X) (hJ : M.IsBasis J X) : I.encard = J.encard :=
  hI.isBasis'.encard_eq_encard hJ.isBasis'

/-- Any independent set can be extended into a larger independent set. -/
/-
**Matroid.Indep.augment** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Indep`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I J : Set α},   M.Indep I → M.Indep J → 
I.encard < J.encard → ∃ e ∈ J \ I, M.Indep (insert e I)
参数：insert e I。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Matroid.Indep.isBasis_iff_forall_insert_dep`：∀ {α : Type u_1} {M : Matro
id α} {I X : Set α}, M.Indep I → I ⊆ X → (M.IsBasis I X ↔ ∀ e ∈ X \ I, M.Dep (in
sert e I))
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.union_sdiff_left`：union_sdiff_left {s t : Set α} : (s union t) \ s =
 t \ s
· 使用定理 `and_iff_left`：∀ {b a : Prop}, b → (a ∧ b ↔ a)
· 使用定理 `Matroid.Indep.subset_ground`：∀ {α : Type u_1} {M : Matroid α} {I : Set α
}, M.Indep I → I ⊆ M.E
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `Matroid.Indep.subset_isBasis_of_subset`：∀ {α : Type u_1} {M : Matroid α}
 {I X : Set α},   M.Indep I → I ⊆ X → autoParam (X ⊆ M.E) Matroid.Indep.subset_i
sBasis_of_subset._auto_1 → ∃…
· 使用定理 `Set.subset_union_right`：subset_union_right {s t : Set α} : t subseteq s 
union t
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matroid.IsBasis.encard_eq_encard`：∀ {α : Type u_1} {M : Matroid α} {I X 
J : Set α}, M.IsBasis I X → M.IsBasis J X → I.encard = J.encard
· 使用定理 `Set.encard_mono`：encard_mono {α : Type*} : Monotone (encard : Set α -> N
at∞)

--- 原说明 ---
Any independent set can be extended into a larger independent set.
-/
theorem Indep.augment (hI : M.Indep I) (hJ : M.Indep J) (hIJ : I.encard < J.encard) :
    ∃ e ∈ J \ I, M.Indep (insert e I) := by
  by_contra! he
  have hb : M.IsBasis I (I ∪ J) := by
    simp_rw [hI.isBasis_iff_forall_insert_dep subset_union_left, union_sdiff_left, mem_sdiff,
      and_imp, dep_iff, insert_subset_iff, and_iff_left hI.subset_ground]
    exact fun e heJ heI ↦ ⟨he e ⟨heJ, heI⟩, hJ.subset_ground heJ⟩
  obtain ⟨J', hJ', hJJ'⟩ := hJ.subset_isBasis_of_subset I.subset_union_right
  rw [← hJ'.encard_eq_encard hb] at hIJ
  exact hIJ.not_ge (encard_mono hJJ')
/-
**Matroid.Indep.augment_finset** 是 Mathlib 中的一个定理，位于命名空间 `Matroid.Indep`。
形式化陈述：∀ {α : Type u_1} {M : Matroid α} {I J : Finset α},   M.Indep ↑I → M.Indep 
↑J → I.card < J.card → ∃ e ∈ J, e ∉ I ∧ M.Indep (insert e ↑I)
参数：insert e ↑I。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matroid.Indep.augment`：∀ {α : Type u_1} {M : Matroid α} {I J : Set α},  
 M.Indep I → M.Indep J → I.encard < J.encard → ∃ e ∈ J \ I, M.Indep (insert e I)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.encard_eq_coe_toFinset_card`：encard_eq_coe_toFinset_card (s : Set α)
 [Fintype s] : encard s = s.toFinset.card
· 使用定理 `Finset.toFinset_coe`：Finset.toFinset_coe (s : Finset α) [Fintype (s : Se
t α)] : (s : Set α).toFinset = s
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma Indep.augment_finset {I J : Finset α} (hI : M.Indep I) (hJ : M.Indep J)
    (hIJ : I.card < J.card) : ∃ e ∈ J, e ∉ I ∧ M.Indep (insert e I) := by
  obtain ⟨x, hx, hxI⟩ := hI.augment hJ (by simpa [encard_eq_coe_toFinset_card])
  simp only [mem_sdiff, Finset.mem_coe] at hx
  exact ⟨x, hx.1, hx.2, hxI⟩

end IsBasis

end Matroid

