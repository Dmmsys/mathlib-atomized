/-
Copyright (c) 2025 Jingting Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jingting Wang
-/
module

public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.KrullDimension.Zero

/-!
# The Krull dimension of a local ring

In this file, we proved some results about the Krull dimension of a local ring.
-/

public section

/-
**ringKrullDim_eq_one_iff_of_isLocalRing_isDomain** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ringKrullDim_eq_one_iff_of_isLocalRing_isDomain {R : Type*} [CommRing R] [
IsLocalRing R] [IsDomain R] : ringKrullDim R = 1 ↔ ¬ IsField R ∧ forall (x : R),
 x != 0 -> IsLocalRing.maximalIdeal R <= Ideal.radical (Ideal.span {x})
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `zero_ne_one`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 0 ≠ 1
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `ringKrullDim_eq_zero_of_isField`：ringKrullDim_eq_zero_of_isField {F : Ty
pe*} [CommRing F] (hF : IsField F) : ringKrullDim F = 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.radical_eq_sInf`：radical_eq_sInf (I : Ideal R) : radical I = sInf 
{ J : Ideal R | I <= J ∧ IsPrime J }
· 使用定理 `le_sInf`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, (∀ b ∈ s, a ≤ b) → a ≤ sInf s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Ring.krullDimLE_one_iff_of_noZeroDivisors`：Ring.krullDimLE_one_iff_of_no
ZeroDivisors [NoZeroDivisors R] : Ring.KrullDimLE 1 R ↔ forall I : Ideal R, I !=
 ⊥ -> I.IsPrime -> I.IsMaximal
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Ring.krullDimLE_iff`：Ring.krullDimLE_iff {n : Nat} : KrullDimLE n R ↔ ri
ngKrullDim R <= n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsLocalRing.eq_maximalIdeal`：eq_maximalIdeal {I : Ideal R} (hI : I.IsMax
imal) : I = maximalIdeal R
· 使用引理 `Ring.KrullDimLE.isField_of_isDomain`：Ring.KrullDimLE.isField_of_isDomain
 [IsDomain R] : IsField R
· 使用定理 `by_contradiction`：by_contradiction {p : Prop} : (¬p -> False) -> p
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Ideal.IsRadical.radical_le_iff`：∀ {R : Type u} [inst : CommSemiring R] {
I J : Ideal R}, J.IsRadical → (I.radical ≤ J ↔ I ≤ J)
（共 37 条，此处仅展示前 30 条）
-/
lemma ringKrullDim_eq_one_iff_of_isLocalRing_isDomain {R : Type*}
    [CommRing R] [IsLocalRing R] [IsDomain R] : ringKrullDim R = 1 ↔ ¬ IsField R ∧
    ∀ (x : R), x ≠ 0 → IsLocalRing.maximalIdeal R ≤ Ideal.radical (Ideal.span {x}) := by
  refine ⟨fun h ↦ ⟨fun h' ↦ ?_, ?_⟩, fun ⟨hn, h⟩ ↦ ?_⟩
  · exact zero_ne_one ((ringKrullDim_eq_zero_of_isField h') ▸ h)
  · intro x hx
    rw [Ideal.radical_eq_sInf]
    refine le_sInf (fun J ⟨hJ1, hJ2⟩ ↦ ?_)
    have : J.IsMaximal :=
      Ring.krullDimLE_one_iff_of_noZeroDivisors.mp (Ring.krullDimLE_iff.mpr (by simp [h]))
        J (fun hJ3 ↦ hx (by simp_all)) hJ2
    exact le_of_eq (IsLocalRing.eq_maximalIdeal this).symm
  · have : ¬ ringKrullDim R ≤ 0 := fun h ↦ by
      have : Ring.KrullDimLE 0 R := Ring.krullDimLE_iff.mpr h
      exact hn Ring.KrullDimLE.isField_of_isDomain
    suffices h : Ring.KrullDimLE 1 R by
      rw [Ring.krullDimLE_iff] at h
      exact le_antisymm h (Order.succ_le_of_lt (lt_of_not_ge this))
    refine Ring.krullDimLE_one_iff_of_noZeroDivisors.mpr fun I hI hI_prime ↦ ?_
    obtain ⟨x, hI, hx⟩ : ∃ (x : R), x ∈ I ∧ x ≠ 0 := by
      apply by_contradiction fun h ↦ (hI (le_antisymm (fun x ↦ ?_) bot_le))
      simp only [ne_eq, not_exists, not_and, not_not] at h
      exact fun hx ↦ h x hx
    have : IsLocalRing.maximalIdeal R ≤ I := le_trans (h x hx)
      ((Ideal.IsRadical.radical_le_iff hI_prime.isRadical).mpr
        ((Ideal.span_singleton_le_iff_mem I).mpr hI))
    have := Ideal.IsMaximal.eq_of_le (IsLocalRing.maximalIdeal.isMaximal R) hI_prime.ne_top this
    exact this ▸ (IsLocalRing.maximalIdeal.isMaximal R)
