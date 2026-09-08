/-
Copyright (c) 2025 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
module

public import Mathlib.Algebra.Order.Group.Basic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Cyclic linearly ordered groups

This file contains basic results about cyclic linearly ordered groups and cyclic subgroups of
linearly ordered groups.

The definitions `LinearOrderedCommGroup.Subgroup.genLTOne` (*resp.*
`LinearOrderedCommGroup.genLTOne`) yields a generator of a non-trivial subgroup of a linearly
ordered commutative group with (*resp.* of a non-trivial linearly ordered commutative group) that
is strictly less than `1`. The corresponding additive definitions are also provided.
-/

@[expose] public section

noncomputable section

namespace LinearOrderedCommGroup

open LinearOrderedCommGroup

variable {G : Type*} [CommGroup G] [LinearOrder G] [IsOrderedMonoid G]

namespace Subgroup

variable (H : Subgroup G) [Nontrivial H] [hH : IsCyclic H]

@[to_additive exists_neg_generator]
/-
**LinearOrderedCommGroup.Subgroup.exists_generator_lt_one** 是 Mathlib 中的一个引理，位于命
名空间 `LinearOrderedCommGroup.Subgroup`。
形式化陈述：exists_generator_lt_one : exists (a : G), a < 1 ∧ Subgroup.zpowers a = H
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subgroup.isCyclic_iff_exists_zpowers_eq_top`：∀ {α : Type u_1} [inst : Gr
oup α] (H : Subgroup α), IsCyclic ↥H ↔ ∃ g, Subgroup.zpowers g = H
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.zpowers_one_eq_bot`：zpowers_one_eq_bot : Subgroup.zpowers (1 : 
G) = ⊥
· 使用定理 `Subgroup.nontrivial_iff_ne_bot`：nontrivial_iff_ne_bot (H : Subgroup G) :
 Nontrivial H ↔ H != ⊥
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Left.inv_lt_one_iff`：Left.inv_lt_one_iff : a⁻¹ < 1 ↔ 1 < a
· 使用定理 `instIsLeftCancelMulOfMulLeftReflectLE`：∀ {α : Type u_1} [inst : Mul α] [
inst_1 : PartialOrder α] [MulLeftReflectLE α], IsLeftCancelMul α
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `Subgroup.zpowers_inv`：zpowers_inv : zpowers g⁻¹ = zpowers g
-/
lemma exists_generator_lt_one : ∃ (a : G), a < 1 ∧ Subgroup.zpowers a = H := by
  obtain ⟨a, ha⟩ := H.isCyclic_iff_exists_zpowers_eq_top.mp hH
  obtain ha1 | rfl | ha1 := lt_trichotomy a 1
  · exact ⟨a, ha1, ha⟩
  · rw [Subgroup.zpowers_one_eq_bot] at ha
    exact absurd ha.symm <| (H.nontrivial_iff_ne_bot).mp inferInstance
  · use a⁻¹, Left.inv_lt_one_iff.mpr ha1
    rw [Subgroup.zpowers_inv, ha]

/-- Given a subgroup of a cyclic linearly ordered commutative group, this is a generator of
the subgroup that is `< 1`. -/
@[to_additive negGen /-- Given an additive subgroup of an additive cyclic linearly ordered
commutative group, this is a negative generator of the subgroup. -/]
/-
**LinearOrderedCommGroup.Subgroup.genLTOne** 是 Mathlib 中的一个定义，位于命名空间 `LinearOrde
redCommGroup.Subgroup`。
形式化陈述：{G : Type u_1} →   [inst : CommGroup G] →     [inst_1 : LinearOrder G] → [
IsOrderedMonoid G] → (H : Subgroup G) → [Nontrivial ↥H] → [hH : IsCyclic ↥H] → G
参数：H : Subgroup G。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `LinearOrderedCommGroup.Subgroup.exists_generator_lt_one`：exists_generato
r_lt_one : exists (a : G), a < 1 ∧ Subgroup.zpowers a = H
-/
protected noncomputable def genLTOne : G := H.exists_generator_lt_one.choose

@[to_additive negGen_neg]
/-
**LinearOrderedCommGroup.Subgroup.genLTOne_lt_one** 是 Mathlib 中的一个引理，位于命名空间 `Lin
earOrderedCommGroup.Subgroup`。
形式化陈述：genLTOne_lt_one : H.genLTOne < 1
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `LinearOrderedCommGroup.Subgroup.exists_generator_lt_one`：exists_generato
r_lt_one : exists (a : G), a < 1 ∧ Subgroup.zpowers a = H
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
lemma genLTOne_lt_one : H.genLTOne < 1 :=
  H.exists_generator_lt_one.choose_spec.1

@[to_additive (attr := simp) negGen_zmultiples_eq_top]
/-
**LinearOrderedCommGroup.Subgroup.genLTOne_zpowers_eq_top** 是 Mathlib 中的一个引理，位于命
名空间 `LinearOrderedCommGroup.Subgroup`。
形式化陈述：genLTOne_zpowers_eq_top : Subgroup.zpowers H.genLTOne = H
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `LinearOrderedCommGroup.Subgroup.exists_generator_lt_one`：exists_generato
r_lt_one : exists (a : G), a < 1 ∧ Subgroup.zpowers a = H
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
lemma genLTOne_zpowers_eq_top : Subgroup.zpowers H.genLTOne = H :=
  H.exists_generator_lt_one.choose_spec.2
/-
**LinearOrderedCommGroup.Subgroup.genLTOne_mem** 是 Mathlib 中的一个引理，位于命名空间 `Linear
OrderedCommGroup.Subgroup`。
形式化陈述：genLTOne_mem : H.genLTOne in H
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `LinearOrderedCommGroup.Subgroup.genLTOne_zpowers_eq_top`：genLTOne_zpower
s_eq_top : Subgroup.zpowers H.genLTOne = H
· 使用定理 `Subgroup.mem_zpowers`：mem_zpowers (g : G) : g in zpowers g
-/
lemma genLTOne_mem : H.genLTOne ∈ H := by
  nth_rewrite 1 [← H.genLTOne_zpowers_eq_top]
  exact Subgroup.mem_zpowers (Subgroup.genLTOne H)
/-
**LinearOrderedCommGroup.Subgroup.genLTOne_unique** 是 Mathlib 中的一个引理，位于命名空间 `Lin
earOrderedCommGroup.Subgroup`。
形式化陈述：genLTOne_unique {g : G} (hg : g < 1) (hH : Subgroup.zpowers g = H) : g = H
.genLTOne
参数：hg : g < 1；hH : Subgroup.zpowers g = H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `not_isOfFinOrder_of_isMulTorsionFree`：not_isOfFinOrder_of_isMulTorsionFr
ee [IsMulTorsionFree G] (ha : a != 1) : ¬ IsOfFinOrder a
· 使用定理 `instIsMulTorsionFreeOfMulLeftStrictMonoOfMulRightStrictMono`：∀ {M : Type
 u_3} [inst : Monoid M] [inst_1 : LinearOrder M] [MulLeftStrictMono M] [MulRight
StrictMono M],   IsMulTorsionFree M
· 使用定理 `instIsLeftCancelMulOfMulLeftReflectLE`：∀ {α : Type u_1} [inst : Mul α] [
inst_1 : PartialOrder α] [MulLeftReflectLE α], IsLeftCancelMul α
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `instIsRightCancelMulOfMulRightReflectLE`：∀ {α : Type u_1} [inst : Mul α]
 [inst_1 : PartialOrder α] [MulRightReflectLE α], IsRightCancelMul α
· 使用定理 `LeftCancelSemigroup.toIsLeftCancelMul`：∀ {G : Type u} [self : LeftCancel
Semigroup G], IsLeftCancelMul G
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Subgroup.zpowers_eq_zpowers_iff`：Subgroup.zpowers_eq_zpowers_iff {x y : 
G} (hx : ¬IsOfFinOrder x) : zpowers x = zpowers y ↔ x = y ∨ x⁻¹ = y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `LinearOrderedCommGroup.Subgroup.genLTOne_zpowers_eq_top`：genLTOne_zpower
s_eq_top : Subgroup.zpowers H.genLTOne = H
· 使用定理 `not_lt_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 < a
· 使用定理 `one_lt_inv'`：∀ {α : Type u} [inst : Group α] [inst_1 : LT α] [MulLeftStr
ictMono α] {a : α}, 1 < a⁻¹ ↔ a < 1
· 使用引理 `LinearOrderedCommGroup.Subgroup.genLTOne_lt_one`：genLTOne_lt_one : H.gen
LTOne < 1
-/
lemma genLTOne_unique {g : G} (hg : g < 1) (hH : Subgroup.zpowers g = H) : g = H.genLTOne := by
  have hg' : ¬ IsOfFinOrder g := not_isOfFinOrder_of_isMulTorsionFree (ne_of_lt hg)
  rw [← H.genLTOne_zpowers_eq_top] at hH
  rcases (Subgroup.zpowers_eq_zpowers_iff hg').mp hH with _ | h
  · assumption
  rw [← one_lt_inv', h] at hg
  exact (not_lt_of_gt hg <| Subgroup.genLTOne_lt_one _).elim
/-
**LinearOrderedCommGroup.Subgroup.genLTOne_unique_of_zpowers_eq** 是 Mathlib 中的一个
引理，位于命名空间 `LinearOrderedCommGroup.Subgroup`。
形式化陈述：genLTOne_unique_of_zpowers_eq {g1 g2 : G} (hg1 : g1 < 1) (hg2 : g2 < 1) (h
 : Subgroup.zpowers g1 = Subgroup.zpowers g2) : g1 = g2
参数：hg1 : g1 < 1；hg2 : g2 < 1；h : Subgroup.zpowers g1 = Subgroup.zpowers g2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.bot_or_nontrivial`：bot_or_nontrivial (H : Subgroup G) : H = ⊥ ∨
 Nontrivial H
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Subgroup.isCyclic_iff_exists_zpowers_eq_top`：∀ {α : Type u_1} [inst : Gr
oup α] (H : Subgroup α), IsCyclic ↥H ↔ ∃ g, Subgroup.zpowers g = H
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `LinearOrderedCommGroup.Subgroup.genLTOne_unique`：genLTOne_unique {g : G}
 (hg : g < 1) (hH : Subgroup.zpowers g = H) : g = H.genLTOne
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearOrderedCommGroup.Subgroup.genLTOne.congr_simp`：∀ {G : Type u_1} [i
nst : CommGroup G] [inst_1 : LinearOrder G] [inst_2 : IsOrderedMonoid G] (H H_1 
: Subgroup G)   (e_H : H = H_1) [inst_3 :…
-/
lemma genLTOne_unique_of_zpowers_eq {g1 g2 : G} (hg1 : g1 < 1) (hg2 : g2 < 1)
    (h : Subgroup.zpowers g1 = Subgroup.zpowers g2) : g1 = g2 := by
  rcases (Subgroup.zpowers g2).bot_or_nontrivial with (h' | h')
  · rw [h'] at h
    simp_all only [Subgroup.zpowers_eq_bot]
  · have h1 : IsCyclic ↥(Subgroup.zpowers g2) := by
      rw [Subgroup.isCyclic_iff_exists_zpowers_eq_top]; use g2
    have h2 : Nontrivial ↥(Subgroup.zpowers g1) := by rw [h]; exact h'
    have h3 : IsCyclic ↥(Subgroup.zpowers g1) := by rw [h]; exact h1
    simp only [(Subgroup.zpowers g2).genLTOne_unique hg1 h]
    simp only [← h]
    simp only [(Subgroup.zpowers g1).genLTOne_unique hg2 h.symm]

end Subgroup

section IsCyclic

variable (G) [Nontrivial G] [IsCyclic G]

/-- Given a cyclic linearly ordered commutative group, this is a generator that is `< 1`. -/
@[to_additive negGen /-- Given an additive cyclic linearly ordered commutative group, this is a
negative generator of it. -/]
/-
**LinearOrderedCommGroup.genLTOne** 是 Mathlib 中的一个定义，位于命名空间 `LinearOrderedCommGr
oup`。
形式化陈述：genLTOne : G
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def genLTOne : G := (⊤ : Subgroup G).genLTOne

@[to_additive (attr := simp) negGen_eq_of_top]
/-
**LinearOrderedCommGroup.genLTOne_eq_of_top** 是 Mathlib 中的一个引理，位于命名空间 `LinearOrd
eredCommGroup`。
形式化陈述：genLTOne_eq_of_top : genLTOne G = (⊤ : Subgroup G).genLTOne
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma genLTOne_eq_of_top : genLTOne G = (⊤ : Subgroup G).genLTOne := rfl
/-
**LinearOrderedCommGroup.genLTOne_unique** 是 Mathlib 中的一个引理，位于命名空间 `LinearOrdere
dCommGroup`。
形式化陈述：genLTOne_unique {g : G} (hg : g < 1) (htop : Subgroup.zpowers g = ⊤) : g =
 genLTOne G
参数：hg : g < 1；htop : Subgroup.zpowers g = ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LinearOrderedCommGroup.Subgroup.genLTOne_unique`：genLTOne_unique {g : G}
 (hg : g < 1) (hH : Subgroup.zpowers g = H) : g = H.genLTOne
· 使用定理 `Subgroup.instNontrivialSubtypeMemTop`：∀ {G : Type u_1} [inst : Group G] 
[Nontrivial G], Nontrivial ↥⊤
-/
lemma genLTOne_unique {g : G} (hg : g < 1) (htop : Subgroup.zpowers g = ⊤) : g = genLTOne G :=
  (⊤ : Subgroup G).genLTOne_unique hg htop

end IsCyclic

end LinearOrderedCommGroup

