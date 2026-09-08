/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kim Morrison
-/
module

public import Mathlib.Analysis.Convex.Combination
public import Mathlib.LinearAlgebra.AffineSpace.Independent
public import Mathlib.Tactic.FieldSimp

/-!
# Carathéodory's convexity theorem

Convex hull can be regarded as a refinement of affine span. Both are closure operators but whereas
convex hull takes values in the lattice of convex subsets, affine span takes values in the much
coarser sublattice of affine subspaces.

The cost of this refinement is that one no longer has bases. However Carathéodory's convexity
theorem offers some compensation. Given a set `s` together with a point `x` in its convex hull,
Carathéodory says that one may find an affine-independent family of elements `s` whose convex hull
contains `x`. Thus the difference from the case of affine span is that the affine-independent family
depends on `x`.

In particular, in finite dimensions Carathéodory's theorem implies that the convex hull of a set `s`
in `𝕜ᵈ` is the union of the convex hulls of the `(d + 1)`-tuples in `s`.

## Main results

* `convexHull_eq_union`: Carathéodory's convexity theorem

## Implementation details

This theorem was formalized as part of the Sphere Eversion project.

## Tags
convex hull, caratheodory

-/

@[expose] public section


open Set Finset

universe u

variable {𝕜 : Type*} {E : Type u} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup E] [Module 𝕜 E]

namespace Caratheodory

/-- If `x` is in the convex hull of some finset `t` whose elements are not affine-independent,
then it is in the convex hull of a strict subset of `t`. -/
/-
**Caratheodory.mem_convexHull_erase** 是 Mathlib 中的一个定理，位于命名空间 `Caratheodory`。
形式化陈述：mem_convexHull_erase [DecidableEq E] {t : Finset E} (h : ¬AffineIndependen
t 𝕜 ((↑) : t -> E)) {x : E} (m : x in convexHull 𝕜 (↑t : Set E)) : exists y : (↑
t : Set E), x in convexHull 𝕜 (↑(t.erase y) : Set E)
参数：h : ¬AffineIndependent 𝕜 ((↑) : t -> E)；m : x in convexHull 𝕜 (↑t : Set E)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.convexHull_eq`：Finset.convexHull_eq (s : Finset E) : convexHull R
 ↑s = { x : E | exists w : E -> R, (forall y in s, 0 <= w y) ∧ ∑ y in s, w y = 1
 ∧ s.cente…
· 使用定理 `exists_nontrivial_relation_sum_zero_of_not_affine_ind`：exists_nontrivial
_relation_sum_zero_of_not_affine_ind {t : Finset V} (h : ¬AffineIndependent k ((
↑) : t -> V)) : exists f : V -> k, ∑ e in t…
· 使用定理 `Finset.exists_pos_of_sum_zero_of_exists_nonzero`：∀ {ι : Type u_1} {M : T
ype u_4} [inst : AddCommMonoid M] [inst_1 : LinearOrder M] {s : Finset ι}   [IsO
rderedCancelAddMonoid M] (f : ι → M),…
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `Finset.exists_min_image`：exists_min_image (s : Finset β) (f : β -> α) (h
 : s.Nonempty) : exists x in s, forall x' in s, f x <= f x'
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Finset.filter_subset`：∀ {α : Type u_1} (p : α → Prop) [inst : DecidableP
red p] (s : Finset α), Finset.filter p s ⊆ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsUnit.div_mul_cancel`：∀ {α : Type u} [inst : DivisionMonoid α] {b : α},
 IsUnit b → ∀ (a : α), a / b * b = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.insert_erase`：∀ {α : Type u_1} [inst : DecidableEq α] {s : Finset
 α} {a : α}, a ∈ s → insert a (s.erase a) = s
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `Finset.notMem_erase`：notMem_erase (a : α) (s : Finset α) : a ∉ erase s a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Finset.sum_sub_distrib`：∀ {ι : Type u_1} {G : Type u_5} {s : Finset ι} [
inst : SubtractionCommMonoid G] (f g : ι → G),   ∑ x ∈ s, (f x - g x) = ∑ x ∈ s,
 f x - ∑ x ∈…
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
（共 60 条，此处仅展示前 30 条）

--- 原说明 ---
If `x` is in the convex hull of some finset `t` whose elements are not affine-in
dependent,
then it is in the convex hull of a strict subset of `t`.
-/
theorem mem_convexHull_erase [DecidableEq E] {t : Finset E} (h : ¬AffineIndependent 𝕜 ((↑) : t → E))
    {x : E} (m : x ∈ convexHull 𝕜 (↑t : Set E)) :
    ∃ y : (↑t : Set E), x ∈ convexHull 𝕜 (↑(t.erase y) : Set E) := by
  simp only [Finset.convexHull_eq, mem_ofPred_eq] at m ⊢
  obtain ⟨f, fpos, fsum, rfl⟩ := m
  obtain ⟨g, gcombo, gsum, gpos⟩ := exists_nontrivial_relation_sum_zero_of_not_affine_ind h
  replace gpos := exists_pos_of_sum_zero_of_exists_nonzero g gsum gpos
  clear h
  let s := {z ∈ t | 0 < g z}
  obtain ⟨i₀, mem, w⟩ : ∃ i₀ ∈ s, ∀ i ∈ s, f i₀ / g i₀ ≤ f i / g i := by
    apply s.exists_min_image fun z => f z / g z
    obtain ⟨x, hx, hgx⟩ : ∃ x ∈ t, 0 < g x := gpos
    exact ⟨x, mem_filter.mpr ⟨hx, hgx⟩⟩
  have hg : 0 < g i₀ := by
    rw [mem_filter] at mem
    exact mem.2
  have hi₀ : i₀ ∈ t := filter_subset _ _ mem
  let k : E → 𝕜 := fun z => f z - f i₀ / g i₀ * g z
  have hk : k i₀ = 0 := by simp [k, ne_of_gt hg]
  have ksum : ∑ e ∈ t.erase i₀, k e = 1 := by
    calc
      ∑ e ∈ t.erase i₀, k e = ∑ e ∈ t, k e := by
        conv_rhs => rw [← insert_erase hi₀, sum_insert (notMem_erase i₀ t), hk, zero_add]
      _ = ∑ e ∈ t, (f e - f i₀ / g i₀ * g e) := rfl
      _ = 1 := by rw [sum_sub_distrib, fsum, ← mul_sum, gsum, mul_zero, sub_zero]
  refine ⟨⟨i₀, hi₀⟩, k, ?_, by convert! ksum, ?_⟩
  · simp only [k, and_imp, sub_nonneg, mem_erase, Ne]
    intro e _ het
    by_cases hes : e ∈ s
    · have hge : 0 < g e := by
        rw [mem_filter] at hes
        exact hes.2
      rw [← le_div_iff₀ hge]
      exact w _ hes
    · calc
        _ ≤ 0 := by
          apply mul_nonpos_of_nonneg_of_nonpos
          · apply div_nonneg (fpos i₀ (mem_of_subset (filter_subset _ t) mem)) (le_of_lt hg)
          · simpa only [s, mem_filter, het, true_and, not_lt] using hes
        _ ≤ f e := fpos e het
  · rw [Subtype.coe_mk, centerMass_eq_of_sum_1 _ id ksum]
    calc
      ∑ e ∈ t.erase i₀, k e • e = ∑ e ∈ t, k e • e := sum_erase _ (by rw [hk, zero_smul])
      _ = ∑ e ∈ t, (f e - f i₀ / g i₀ * g e) • e := rfl
      _ = t.centerMass f id := by
        simp only [sub_smul, mul_smul, sum_sub_distrib, ← smul_sum, gcombo, smul_zero, sub_zero,
          centerMass, fsum, inv_one, one_smul, id]

variable {s : Set E} {x : E}

/-- Given a point `x` in the convex hull of a set `s`, this is a finite subset of `s` of minimum
cardinality, whose convex hull contains `x`. -/
/-
**Caratheodory.minCardFinsetOfMemConvexHull** 是 Mathlib 中的一个定义，位于命名空间 `Caratheod
ory`。
形式化陈述：minCardFinsetOfMemConvexHull (hx : x in convexHull 𝕜 s) : Finset E
参数：hx : x in convexHull 𝕜 s。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instWellFoundedLTNat`：WellFoundedLT ℕ

--- 原说明 ---
Given a point `x` in the convex hull of a set `s`, this is a finite subset of `s
` of minimum
cardinality, whose convex hull contains `x`.
-/
noncomputable def minCardFinsetOfMemConvexHull (hx : x ∈ convexHull 𝕜 s) : Finset E :=
  Function.argminOn Finset.card { t | ↑t ⊆ s ∧ x ∈ convexHull 𝕜 (t : Set E) } <| by
    simpa only [convexHull_eq_union_convexHull_finite_subsets s, exists_prop, mem_iUnion] using! hx

variable (hx : x ∈ convexHull 𝕜 s)
/-
**Caratheodory.minCardFinsetOfMemConvexHull_subseteq** 是 Mathlib 中的一个定理，位于命名空间 `
Caratheodory`。
形式化陈述：minCardFinsetOfMemConvexHull_subseteq : ↑(minCardFinsetOfMemConvexHull hx)
 subseteq s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `instWellFoundedLTNat`：WellFoundedLT ℕ
· 使用定理 `Function.argminOn_mem`：argminOn_mem (s : Set α) (hs : s.Nonempty) : argm
inOn f s hs in s
-/
theorem minCardFinsetOfMemConvexHull_subseteq : ↑(minCardFinsetOfMemConvexHull hx) ⊆ s :=
  (Function.argminOn_mem _ { t : Finset E | ↑t ⊆ s ∧ x ∈ convexHull 𝕜 (t : Set E) } _).1
/-
**Caratheodory.mem_minCardFinsetOfMemConvexHull** 是 Mathlib 中的一个定理，位于命名空间 `Carat
heodory`。
形式化陈述：mem_minCardFinsetOfMemConvexHull : x in convexHull 𝕜 (minCardFinsetOfMemCo
nvexHull hx : Set E)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `instWellFoundedLTNat`：WellFoundedLT ℕ
· 使用定理 `Function.argminOn_mem`：argminOn_mem (s : Set α) (hs : s.Nonempty) : argm
inOn f s hs in s
-/
theorem mem_minCardFinsetOfMemConvexHull :
    x ∈ convexHull 𝕜 (minCardFinsetOfMemConvexHull hx : Set E) :=
  (Function.argminOn_mem _ { t : Finset E | ↑t ⊆ s ∧ x ∈ convexHull 𝕜 (t : Set E) } _).2
/-
**Caratheodory.minCardFinsetOfMemConvexHull_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `
Caratheodory`。
形式化陈述：minCardFinsetOfMemConvexHull_nonempty : (minCardFinsetOfMemConvexHull hx).
Nonempty
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.coe_nonempty`：coe_nonempty {s : Finset α} : (s : Set α).Nonempty 
↔ s.Nonempty
· 使用定理 `convexHull_nonempty_iff`：convexHull_nonempty_iff : (convexHull 𝕜 s).None
mpty ↔ s.Nonempty
· 使用定理 `Caratheodory.mem_minCardFinsetOfMemConvexHull`：mem_minCardFinsetOfMemCon
vexHull : x in convexHull 𝕜 (minCardFinsetOfMemConvexHull hx : Set E)
-/
theorem minCardFinsetOfMemConvexHull_nonempty : (minCardFinsetOfMemConvexHull hx).Nonempty := by
  rw [← Finset.coe_nonempty, ← @convexHull_nonempty_iff 𝕜]
  exact ⟨x, mem_minCardFinsetOfMemConvexHull hx⟩
/-
**Caratheodory.minCardFinsetOfMemConvexHull_card_le_card** 是 Mathlib 中的一个定理，位于命名
空间 `Caratheodory`。
形式化陈述：minCardFinsetOfMemConvexHull_card_le_card {t : Finset E} (ht₁ : ↑t subsete
q s) (ht₂ : x in convexHull 𝕜 (t : Set E)) : #(minCardFinsetOfMemConvexHull hx) 
<= #t
参数：ht₁ : ↑t subseteq s；ht₂ : x in convexHull 𝕜 (t : Set E)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.argminOn_le`：argminOn_le (s : Set α) {a : α} (ha : a in s) : f 
(argminOn f s ⟨a, ha⟩) <= f a
· 使用定理 `instWellFoundedLTNat`：WellFoundedLT ℕ
-/
theorem minCardFinsetOfMemConvexHull_card_le_card {t : Finset E} (ht₁ : ↑t ⊆ s)
    (ht₂ : x ∈ convexHull 𝕜 (t : Set E)) : #(minCardFinsetOfMemConvexHull hx) ≤ #t :=
  Function.argminOn_le _ _ (by exact ⟨ht₁, ht₂⟩)
/-
**Caratheodory.affineIndependent_minCardFinsetOfMemConvexHull** 是 Mathlib 中的一个定理
，位于命名空间 `Caratheodory`。
形式化陈述：affineIndependent_minCardFinsetOfMemConvexHull : AffineIndependent 𝕜 ((↑) 
: minCardFinsetOfMemConvexHull hx -> E)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.succ_pred_eq_of_pos`：∀ {n : ℕ}, 0 < n → n.pred.succ = n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.card_pos`：∀ {α : Type u_1} {s : Finset α}, 0 < s.card ↔ s.Nonempt
y
· 使用定理 `Caratheodory.minCardFinsetOfMemConvexHull_nonempty`：minCardFinsetOfMemCo
nvexHull_nonempty : (minCardFinsetOfMemConvexHull hx).Nonempty
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Caratheodory.mem_convexHull_erase`：mem_convexHull_erase [DecidableEq E] 
{t : Finset E} (h : ¬AffineIndependent 𝕜 ((↑) : t -> E)) {x : E} (m : x in conve
xHull 𝕜 (↑t : Set E)) :…
· 使用定理 `Caratheodory.mem_minCardFinsetOfMemConvexHull`：mem_minCardFinsetOfMemCon
vexHull : x in convexHull 𝕜 (minCardFinsetOfMemConvexHull hx : Set E)
· 使用定理 `Caratheodory.minCardFinsetOfMemConvexHull_card_le_card`：minCardFinsetOfM
emConvexHull_card_le_card {t : Finset E} (ht₁ : ↑t subseteq s) (ht₂ : x in conve
xHull 𝕜 (t : Set E)) : #(minCardFinsetOfMemC…
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Finset.erase_subset`：erase_subset (a : α) (s : Finset α) : erase s a sub
seteq s
· 使用定理 `Caratheodory.minCardFinsetOfMemConvexHull_subseteq`：minCardFinsetOfMemCo
nvexHull_subseteq : ↑(minCardFinsetOfMemConvexHull hx) subseteq s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `Finset.card_erase_of_mem`：card_erase_of_mem : a in s -> #(s.erase a) = #
s - 1
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用引理 `lt_add_one`：lt_add_one [One α] [AddZeroClass α] [PartialOrder α] [ZeroLE
OneClass α] [NeZero (1 : α)] [AddLeftStrictMono α] (a : α) : a < a + 1
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
theorem affineIndependent_minCardFinsetOfMemConvexHull :
    AffineIndependent 𝕜 ((↑) : minCardFinsetOfMemConvexHull hx → E) := by
  let k := #(minCardFinsetOfMemConvexHull hx) - 1
  have hk : #(minCardFinsetOfMemConvexHull hx) = k + 1 :=
    (Nat.succ_pred_eq_of_pos (Finset.card_pos.mpr (minCardFinsetOfMemConvexHull_nonempty hx))).symm
  classical
  by_contra h
  obtain ⟨p, hp⟩ := mem_convexHull_erase h (mem_minCardFinsetOfMemConvexHull hx)
  have contra := minCardFinsetOfMemConvexHull_card_le_card hx (Set.Subset.trans
    (Finset.erase_subset (p : E) (minCardFinsetOfMemConvexHull hx))
    (minCardFinsetOfMemConvexHull_subseteq hx)) hp
  rw [← not_lt] at contra
  apply contra
  rw [card_erase_of_mem p.2, hk]
  exact lt_add_one _

end Caratheodory

variable {s : Set E}

/-- **Carathéodory's convexity theorem** -/
/-
**convexHull_eq_union** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：convexHull_eq_union : convexHull 𝕜 s = ⋃ (t : Finset E) (_ : ↑t subseteq s
) (_ : AffineIndependent 𝕜 ((↑) : t -> E)), convexHull 𝕜 ↑t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Caratheodory.minCardFinsetOfMemConvexHull_subseteq`：minCardFinsetOfMemCo
nvexHull_subseteq : ↑(minCardFinsetOfMemConvexHull hx) subseteq s
· 使用定理 `Caratheodory.affineIndependent_minCardFinsetOfMemConvexHull`：affineIndep
endent_minCardFinsetOfMemConvexHull : AffineIndependent 𝕜 ((↑) : minCardFinsetOf
MemConvexHull hx -> E)
· 使用定理 `Caratheodory.mem_minCardFinsetOfMemConvexHull`：mem_minCardFinsetOfMemCon
vexHull : x in convexHull 𝕜 (minCardFinsetOfMemConvexHull hx : Set E)
· 使用定理 `Set.iUnion_subset`：iUnion_subset {s : ι -> Set α} {t : Set α} (h : foral
l i, s i subseteq t) : ⋃ i, s i subseteq t
· 使用定理 `convexHull_mono`：convexHull_mono (hst : s subseteq t) : convexHull 𝕜 s s
ubseteq convexHull 𝕜 t

--- 原说明 ---
**Carathéodory's convexity theorem**
-/
theorem convexHull_eq_union : convexHull 𝕜 s =
    ⋃ (t : Finset E) (_ : ↑t ⊆ s) (_ : AffineIndependent 𝕜 ((↑) : t → E)), convexHull 𝕜 ↑t := by
  apply Set.Subset.antisymm
  · intro x hx
    simp only [exists_prop, Set.mem_iUnion]
    exact ⟨Caratheodory.minCardFinsetOfMemConvexHull hx,
      Caratheodory.minCardFinsetOfMemConvexHull_subseteq hx,
      Caratheodory.affineIndependent_minCardFinsetOfMemConvexHull hx,
      Caratheodory.mem_minCardFinsetOfMemConvexHull hx⟩
  · iterate 3 convert! Set.iUnion_subset _; intro
    exact convexHull_mono ‹_›

/-- A more explicit version of `convexHull_eq_union`. -/
/-
**eq_pos_convex_span_of_mem_convexHull** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_pos_convex_span_of_mem_convexHull {x : E} (hx : x in convexHull 𝕜 s) : 
exists (ι : Sort (u + 1)) (_ : Fintype ι), exists (z : ι -> E) (w : ι -> 𝕜), Set
.range z subseteq s ∧ AffineIndependent 𝕜 z ∧ (forall i, 0 < w i) ∧ ∑ i, w i = 1
 ∧ ∑ i, w i • z i = x
参数：hx : x in convexHull 𝕜 s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `convexHull_eq_union`：convexHull_eq_union : convexHull 𝕜 s = ⋃ (t : Finse
t E) (_ : ↑t subseteq s) (_ : AffineIndependent 𝕜 ((↑) : t -> E)), convexHull 𝕜 
↑t
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.convexHull_eq`：Finset.convexHull_eq (s : Finset E) : convexHull R
 ↑s = { x : E | exists w : E -> R, (forall y in s, 0 <= w y) ∧ ∑ y in s, w y = 1
 ∧ s.cente…
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Finset.filter_subset`：∀ {α : Type u_1} (p : α → Prop) [inst : DecidableP
red p] (s : Finset α), Finset.filter p s ⊆ s
· 使用定理 `AffineIndependent.comp_embedding`：AffineIndependent.comp_embedding {ι2 :
 Type*} (f : ι2 ↪ ι) {p : ι -> P} (ha : AffineIndependent k p) : AffineIndepende
nt k (p ∘ f)
· 使用定理 `Set.inclusion_injective`：inclusion_injective (h : s subseteq t) : (inclu
sion h).Injective
· 使用定理 `LE.le.lt_of_ne`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a ≠ b → a < b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Finset.sum_attach`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMonoid
 M] (s : Finset ι) (f : ι → M), ∑ x ∈ s.attach, f ↑x = ∑ x ∈ s, f x
· 使用定理 `Finset.sum_filter_ne_zero`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCo
mmMonoid M] {f : ι → M} (s : Finset ι)   [inst_1 : (x : ι) → Decidable (f x ≠ 0)
], ∑ x ∈ s with…
· 使用定理 `Finset.sum_filter_of_ne`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} 
[inst : AddCommMonoid M] {f : ι → M} {p : ι → Prop}   [inst_1 : DecidablePred p]
, (∀ x ∈ s, f…
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `Finset.centerMass_eq_of_sum_1`：Finset.centerMass_eq_of_sum_1 (hw : ∑ i i
n t, w i = 1) : t.centerMass w z = ∑ i in t, w i • z i

--- 原说明 ---
A more explicit version of `convexHull_eq_union`.
-/
theorem eq_pos_convex_span_of_mem_convexHull {x : E} (hx : x ∈ convexHull 𝕜 s) :
    ∃ (ι : Sort (u + 1)) (_ : Fintype ι),
      ∃ (z : ι → E) (w : ι → 𝕜), Set.range z ⊆ s ∧ AffineIndependent 𝕜 z ∧ (∀ i, 0 < w i) ∧
        ∑ i, w i = 1 ∧ ∑ i, w i • z i = x := by
  rw [convexHull_eq_union] at hx
  simp only [exists_prop, Set.mem_iUnion] at hx
  obtain ⟨t, ht₁, ht₂, ht₃⟩ := hx
  simp only [t.convexHull_eq, Set.mem_ofPred_eq] at ht₃
  obtain ⟨w, hw₁, hw₂, hw₃⟩ := ht₃
  let t' := {i ∈ t | w i ≠ 0}
  refine ⟨t', t'.fintypeCoeSort, ((↑) : t' → E), w ∘ ((↑) : t' → E), ?_, ?_, ?_, ?_, ?_⟩
  · rw [Subtype.range_coe_subtype]
    exact Subset.trans (Finset.filter_subset _ t) ht₁
  · exact ht₂.comp_embedding ⟨_, inclusion_injective (Finset.filter_subset (fun i => w i ≠ 0) t)⟩
  · exact fun i =>
      (hw₁ _ (Finset.mem_filter.mp i.2).1).lt_of_ne (Finset.mem_filter.mp i.property).2.symm
  · simp only [univ_eq_attach, Function.comp_apply]
    rw [Finset.sum_attach, Finset.sum_filter_ne_zero, hw₂]
  · change (∑ i ∈ t'.attach, (fun e => w e • e) ↑i) = x
    rw [Finset.sum_attach (f := fun e => w e • e), Finset.sum_filter_of_ne]
    · rw [t.centerMass_eq_of_sum_1 id hw₂] at hw₃
      exact hw₃
    · intro e _ hwe contra
      apply hwe
      rw [contra, zero_smul]
