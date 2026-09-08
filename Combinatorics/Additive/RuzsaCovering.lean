/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.Action.Pointwise.Finset
public import Mathlib.Data.Real.Basic
public import Mathlib.Order.Preorder.Finite
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Tactic.Positivity.Finset

/-!
# Ruzsa's covering lemma

This file proves the Ruzsa covering lemma. This says that, for `A`, `B` finsets, we can cover `A`
with at most `#(A + B) / #B` copies of `B - B`.
-/

public section

open scoped Pointwise

variable {G : Type*} [Group G] {K : ℝ}

namespace Finset
variable [DecidableEq G] {A B : Finset G}

/-- **Ruzsa's covering lemma**. -/
@[to_additive /-- **Ruzsa's covering lemma** -/]
/-
**Finset.ruzsa_covering_mul** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：ruzsa_covering_mul (hB : B.Nonempty) (hK : #(A * B) <= K * #B) : exists F 
subseteq A, #F <= K ∧ A subseteq F * (B / B)
参数：hB : B.Nonempty；hK : #(A * B) <= K * #B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.exists_maximal`：exists_maximal (hs : s.Nonempty) : exists i, Maxi
mal (· in s) i
· 使用定理 `instIsTransLe`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x1 ≤ x2
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.filter_nonempty_iff`：∀ {α : Type u_1} {p : α → Prop} [inst : Deci
dablePred p] {s : Finset α}, (Finset.filter p s).Nonempty ↔ ∃ a ∈ s, p a
· 使用定理 `Finset.empty_mem_powerset`：empty_mem_powerset (s : Finset α) : ∅ in powe
rset s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_empty`：coe_empty : ((∅ : Finset α) : Set α) = ∅
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `le_of_mul_le_mul_right`：le_of_mul_le_mul_right [MulPosReflectLE α] (bc :
 b * a <= c * a) (a0 : 0 < a) : b <= c
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `Finset.card_mul_iff`：card_mul_iff : #(s * t) = #s * #t ↔ (s ×ˢ t : Set (
α × α)).InjOn fun p => p.1 * p.2
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.pairwiseDisjoint_smul_iff`：pairwiseDisjoint_smul_iff {s : Set α} 
{t : Finset β} : s.PairwiseDisjoint (· • t) ↔ (s ×ˢ t : Set (α × β)).InjOn fun p
 => p.1 • p.2
· 使用定理 `instIsLeftCancelSMul`：∀ (G : Type u_9) (P : Type u_10) [inst : Group G] 
[inst_1 : MulAction G P], IsLeftCancelSMul G P
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `Nat.mono_cast`：mono_cast : Monotone (Nat.cast : Nat -> α)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Finset.card_le_card`：card_le_card : s subseteq t -> #s <= #t
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `Finset.instMulLeftMono`：∀ {α : Type u_2} [inst : DecidableEq α] [inst_1 
: Mul α], MulLeftMono (Finset α)
· 使用定理 `Finset.instMulRightMono`：∀ {α : Type u_2} [inst : DecidableEq α] [inst_1
 : Mul α], MulRightMono (Finset α)
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Nat.cast_pos'`：cast_pos' {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `Finset.Nonempty.card_pos`：∀ {α : Type u_1} {s : Finset α}, s.Nonempty → 
0 < s.card
· 使用定理 `Finset.subset_mul_left`：subset_mul_left (s : Finset α) {t : Finset α} (h
t : (1 : α) in t) : s subseteq s * t
（共 44 条，此处仅展示前 30 条）

--- 原说明 ---
**Ruzsa's covering lemma**.
-/
theorem ruzsa_covering_mul (hB : B.Nonempty) (hK : #(A * B) ≤ K * #B) :
    ∃ F ⊆ A, #F ≤ K ∧ A ⊆ F * (B / B) := by
  have : ∀ F, Decidable ((F : Set G).PairwiseDisjoint (· • B)) := fun F ↦ Classical.dec _
  set C := {F ∈ A.powerset | (SetLike.coe F).PairwiseDisjoint (· • B)}
  obtain ⟨F, hFmax⟩ := C.exists_maximal <| filter_nonempty_iff.2
    ⟨∅, empty_mem_powerset _, by simp [coe_empty]⟩
  simp only [C, mem_filter, mem_powerset] at hFmax
  obtain ⟨hFA, hF⟩ := hFmax.1
  refine ⟨F, hFA, le_of_mul_le_mul_right ?_ (by positivity : (0 : ℝ) < #B), fun a ha ↦ ?_⟩
  · calc
      (#F * #B : ℝ) = #(F * B) := by
        rw [card_mul_iff.2 <| pairwiseDisjoint_smul_iff.1 hF, Nat.cast_mul]
      _ ≤ #(A * B) := by gcongr
      _ ≤ K * #B := hK
  by_cases hau : a ∈ F
  · exact subset_mul_left _ hB.one_mem_div hau
  by_cases! H : ∀ b ∈ F, Disjoint (a • B) (b • B)
  · refine (hFmax.not_gt ?_ <| ssubset_insert hau).elim
    rw [insert_subset_iff, coe_insert]
    exact ⟨⟨ha, hFA⟩, hF.insert fun _ hb _ ↦ H _ hb⟩
  simp_rw [not_disjoint_iff, ← inv_smul_mem_iff] at H
  obtain ⟨b, hb, c, hc₁, hc₂⟩ := H
  exact mem_mul.2 ⟨b, hb, b⁻¹ * a, mem_div.2 ⟨_, hc₂, _, hc₁, by simp⟩, by simp⟩

end Finset

namespace Set
variable {A B : Set G}

/-- **Ruzsa's covering lemma** for sets. See also `Finset.ruzsa_covering_mul`. -/
@[to_additive /-- **Ruzsa's covering lemma** for sets. See also `Finset.ruzsa_covering_add`. -/]
/-
**Set.ruzsa_covering_mul** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：ruzsa_covering_mul (hA : A.Finite) (hB : B.Finite) (hB₀ : B.Nonempty) (hK 
: Nat.card (A * B) <= K * Nat.card B) : exists F subseteq A, Nat.card F <= K ∧ A
 subseteq F * (B / B) ∧ F.Finite
参数：hA : A.Finite；hB : B.Finite；hB₀ : B.Nonempty；hK : Nat.card (A * B) <= K * Nat
.card B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `Set.instCanLiftFinsetCoeFinite`：∀ {α : Type u}, CanLift (Set α) (Finset 
α) SetLike.coe Set.Finite
· 使用定理 `Finset.ruzsa_covering_mul`：ruzsa_covering_mul (hB : B.Nonempty) (hK : #(
A * B) <= K * #B) : exists F subseteq A, #F <= K ∧ A subseteq F * (B / B)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `Fintype.card_coe`：Fintype.card_coe (s : Finset α) [Fintype s] : Fintype.
card s = #s
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p

--- 原说明 ---
**Ruzsa's covering lemma** for sets. See also `Finset.ruzsa_covering_mul`.
-/
lemma ruzsa_covering_mul (hA : A.Finite) (hB : B.Finite) (hB₀ : B.Nonempty)
    (hK : Nat.card (A * B) ≤ K * Nat.card B) :
    ∃ F ⊆ A, Nat.card F ≤ K ∧ A ⊆ F * (B / B) ∧ F.Finite := by
  lift A to Finset G using hA
  lift B to Finset G using hB
  classical
  obtain ⟨F, hFA, hF, hAF⟩ := Finset.ruzsa_covering_mul hB₀ (by simpa [← Finset.coe_mul] using hK)
  exact ⟨F, by norm_cast; simp [*]⟩

end Set

