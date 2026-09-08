/-
Copyright (c) 2023 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
module

public import Mathlib.Algebra.BigOperators.Expect
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Analysis.RCLike.Inner

/-!
# Orthogonality of characters of a finite abelian group

This file proves that characters of a finite abelian group are orthogonal, and in particular that
there are at most as many characters as there are elements of the group.
-/

public section

open Finset hiding card
open Fintype (card)
open Function RCLike
open scoped BigOperators ComplexConjugate DirectSum

variable {G H R : Type*}

namespace AddChar
section AddGroup
variable [AddGroup G]

section Semifield
variable [Fintype G] [Semifield R] [CharZero R] {ψ : AddChar G R}

/-
**AddChar.expect_eq_ite** 是 Mathlib 中的一个引理，位于命名空间 `AddChar`。
形式化陈述：expect_eq_ite (ψ : AddChar G R) : 𝔼 a, ψ a = if ψ = 0 then 1 else 0
参数：ψ : AddChar G R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fintype.expect_eq_sum_div_card`：∀ {ι : Type u_1} {K : Type u_3} [inst : 
Semifield K] [inst_1 : CharZero K] [inst_2 : Fintype ι] (f : ι → K),   (Finset.u
niv.expect fun i => …
· 使用引理 `AddChar.sum_eq_ite`：sum_eq_ite (ψ : AddChar A R) [Decidable (ψ = 0)] : ∑
 a, ψ a = if ψ = 0 then ↑(card A) else 0
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用引理 `ite_div`：ite_div (a b c : α) : (if P then a else b) / c = if P then a / 
c else b / c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `AddTorsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : A
ddGroup G} [self : AddTorsor G P], Nonempty P
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma expect_eq_ite (ψ : AddChar G R) : 𝔼 a, ψ a = if ψ = 0 then 1 else 0 := by
  simp [Fintype.expect_eq_sum_div_card, sum_eq_ite, ite_div]
/-
**AddChar.expect_eq_zero_iff_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `AddChar`。
形式化陈述：expect_eq_zero_iff_ne_zero : 𝔼 x, ψ x = 0 ↔ ψ != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AddChar.expect_eq_ite`：expect_eq_ite (ψ : AddChar G R) : 𝔼 a, ψ a = if ψ
 = 0 then 1 else 0
· 使用定理 `Ne.ite_eq_right_iff`：∀ {α : Sort u_1} {P : Prop} [inst : Decidable P] {a
 b : α}, a ≠ b → ((if P then a else b) = b ↔ ¬P)
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma expect_eq_zero_iff_ne_zero : 𝔼 x, ψ x = 0 ↔ ψ ≠ 0 := by
  rw [expect_eq_ite, one_ne_zero.ite_eq_right_iff]
/-
**AddChar.expect_ne_zero_iff_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `AddChar`。
形式化陈述：expect_ne_zero_iff_eq_zero : 𝔼 x, ψ x != 0 ↔ ψ = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not_left`：Iff.not_left (h : a ↔ ¬b) : ¬a ↔ b
· 使用引理 `AddChar.expect_eq_zero_iff_ne_zero`：expect_eq_zero_iff_ne_zero : 𝔼 x, ψ 
x = 0 ↔ ψ != 0
-/
lemma expect_ne_zero_iff_eq_zero : 𝔼 x, ψ x ≠ 0 ↔ ψ = 0 := expect_eq_zero_iff_ne_zero.not_left

end Semifield

section RCLike
variable [RCLike R] [Fintype G]

/-
**AddChar.wInner_cWeight_self** 是 Mathlib 中的一个引理，位于命名空间 `AddChar`。
形式化陈述：wInner_cWeight_self (ψ : AddChar G R) : ⟪(ψ : G -> R), ψ⟫ₙ_[R] = 1
参数：ψ : AddChar G R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RCLike.charZero_rclike`：∀ {K : Type u_1} [inst : RCLike K], CharZero K
· 使用引理 `RCLike.wInner_cWeight_eq_expect`：wInner_cWeight_eq_expect (f g : forall 
i, E i) : ⟪f, g⟫ₙ_[𝕜] = 𝔼 i, ⟪f i, g i⟫_𝕜
· 使用引理 `Finset.expect_congr`：expect_congr {t : Finset ι} (hst : s = t) (h : fora
ll i in t, f i = g i) : 𝔼 i in s, f i = 𝔼 i in t, g i
· 使用定理 `inner_self_eq_norm_sq_to_K`：inner_self_eq_norm_sq_to_K (x : E) : ⟪x, x⟫ 
= (‖x‖ : 𝕜) ^ 2
· 使用定理 `AddChar.norm_apply`：∀ {α : Type u_1} [inst : NormedRing α] [NormMulClass
 α] [NormOneClass α] {G : Type u_3} [inst_3 : AddLeftCancelMonoid G]   [Finite G
] (ψ : A…
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `Finset.expect_const`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMono
id M] [inst_1 : _root_.Module ℚ≥0 M] {s : Finset ι},   s.Nonempty → ∀ (a : M), (
s.expect …
· 使用定理 `AddTorsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : A
ddGroup G} [self : AddTorsor G P], Nonempty P
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma wInner_cWeight_self (ψ : AddChar G R) : ⟪(ψ : G → R), ψ⟫ₙ_[R] = 1 := by
  simp [wInner_cWeight_eq_expect, ψ.norm_apply]

end RCLike
end AddGroup

section AddCommGroup
variable [AddCommGroup G]

section RCLike
variable [RCLike R] {ψ₁ ψ₂ : AddChar G R}

/-
**AddChar.wInner_cWeight_eq_boole** 是 Mathlib 中的一个引理，位于命名空间 `AddChar`。
形式化陈述：wInner_cWeight_eq_boole [Fintype G] (ψ₁ ψ₂ : AddChar G R) : ⟪(ψ₁ : G -> R)
, ψ₂⟫ₙ_[R] = if ψ₁ = ψ₂ then 1 else 0
参数：ψ₁ ψ₂ : AddChar G R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用引理 `AddChar.wInner_cWeight_self`：wInner_cWeight_self (ψ : AddChar G R) : ⟪(ψ
 : G -> R), ψ⟫ₙ_[R] = 1
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `mul_inv_eq_one`：mul_inv_eq_one : a * b⁻¹ = 1 ↔ a = b
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `RCLike.charZero_rclike`：∀ {K : Type u_1} [inst : RCLike K], CharZero K
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `RCLike.wInner_cWeight_eq_expect`：wInner_cWeight_eq_expect (f g : forall 
i, E i) : ⟪f, g⟫ₙ_[𝕜] = 𝔼 i, ⟪f i, g i⟫_𝕜
· 使用引理 `Finset.expect_congr`：expect_congr {t : Finset ι} (hst : s = t) (h : fora
ll i in t, f i = g i) : 𝔼 i in s, f i = 𝔼 i in t, g i
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `AddChar.map_neg_eq_inv`：map_neg_eq_inv (ψ : AddChar A M) (a : A) : ψ (-a
) = (ψ a)⁻¹
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `AddChar.expect_eq_zero_iff_ne_zero`：expect_eq_zero_iff_ne_zero : 𝔼 x, ψ 
x = 0 ↔ ψ != 0
-/
lemma wInner_cWeight_eq_boole [Fintype G] (ψ₁ ψ₂ : AddChar G R) :
    ⟪(ψ₁ : G → R), ψ₂⟫ₙ_[R] = if ψ₁ = ψ₂ then 1 else 0 := by
  split_ifs with h
  · rw [h, wInner_cWeight_self]
  have : ψ₂ * ψ₁⁻¹ ≠ 1 := by rwa [Ne, mul_inv_eq_one, eq_comm]
  simp_rw [wInner_cWeight_eq_expect, RCLike.inner_apply, ← inv_apply_eq_conj]
  simpa [map_neg_eq_inv] using expect_eq_zero_iff_ne_zero.2 this
/-
**AddChar.wInner_cWeight_eq_zero_iff_ne** 是 Mathlib 中的一个引理，位于命名空间 `AddChar`。
形式化陈述：wInner_cWeight_eq_zero_iff_ne [Fintype G] : ⟪(ψ₁ : G -> R), ψ₂⟫ₙ_[R] = 0 ↔
 ψ₁ != ψ₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AddChar.wInner_cWeight_eq_boole`：wInner_cWeight_eq_boole [Fintype G] (ψ₁
 ψ₂ : AddChar G R) : ⟪(ψ₁ : G -> R), ψ₂⟫ₙ_[R] = if ψ₁ = ψ₂ then 1 else 0
· 使用定理 `Ne.ite_eq_right_iff`：∀ {α : Sort u_1} {P : Prop} [inst : Decidable P] {a
 b : α}, a ≠ b → ((if P then a else b) = b ↔ ¬P)
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `RCLike.charZero_rclike`：∀ {K : Type u_1} [inst : RCLike K], CharZero K
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma wInner_cWeight_eq_zero_iff_ne [Fintype G] : ⟪(ψ₁ : G → R), ψ₂⟫ₙ_[R] = 0 ↔ ψ₁ ≠ ψ₂ := by
  rw [wInner_cWeight_eq_boole, one_ne_zero.ite_eq_right_iff]
/-
**AddChar.wInner_cWeight_eq_one_iff_eq** 是 Mathlib 中的一个引理，位于命名空间 `AddChar`。
形式化陈述：wInner_cWeight_eq_one_iff_eq [Fintype G] : ⟪(ψ₁ : G -> R), ψ₂⟫ₙ_[R] = 1 ↔ 
ψ₁ = ψ₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AddChar.wInner_cWeight_eq_boole`：wInner_cWeight_eq_boole [Fintype G] (ψ₁
 ψ₂ : AddChar G R) : ⟪(ψ₁ : G -> R), ψ₂⟫ₙ_[R] = if ψ₁ = ψ₂ then 1 else 0
· 使用定理 `Ne.ite_eq_left_iff`：∀ {α : Sort u_1} {P : Prop} [inst : Decidable P] {a 
b : α}, a ≠ b → ((if P then a else b) = a ↔ P)
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `RCLike.charZero_rclike`：∀ {K : Type u_1} [inst : RCLike K], CharZero K
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma wInner_cWeight_eq_one_iff_eq [Fintype G] : ⟪(ψ₁ : G → R), ψ₂⟫ₙ_[R] = 1 ↔ ψ₁ = ψ₂ := by
  rw [wInner_cWeight_eq_boole, one_ne_zero.ite_eq_left_iff]

variable (G R)
/-
**AddChar.linearIndependent** 是 Mathlib 中的一个定理，位于命名空间 `AddChar`。
形式化陈述：∀ (G : Type u_1) (R : Type u_3) [inst : AddCommGroup G] [inst_1 : RCLike R
] [Finite G], LinearIndependent R DFunLike.coe
参数：G : Type u_1；R : Type u_3。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用引理 `RCLike.linearIndependent_of_ne_zero_of_wInner_cWeight_eq_zero`：linearInd
ependent_of_ne_zero_of_wInner_cWeight_eq_zero {f : κ -> ι -> 𝕜} (hf : forall k, 
f k != 0) (hinner : Pairwise fun k₁ k₂ => ⟪f k₁, f …
· 使用定理 `AddChar.coe_ne_zero`：∀ {A : Type u_1} {M₀ : Type u_2} [inst : AddGroup A
] [inst_1 : MonoidWithZero M₀] [Nontrivial M₀] (ψ : AddChar A M₀),   ⇑ψ ≠ 0
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `AddChar.wInner_cWeight_eq_zero_iff_ne`：wInner_cWeight_eq_zero_iff_ne [Fi
ntype G] : ⟪(ψ₁ : G -> R), ψ₂⟫ₙ_[R] = 0 ↔ ψ₁ != ψ₂
-/
protected lemma linearIndependent [Finite G] : LinearIndependent R ((⇑) : AddChar G R → G → R) := by
  cases nonempty_fintype G
  exact linearIndependent_of_ne_zero_of_wInner_cWeight_eq_zero coe_ne_zero
    fun ψ₁ ψ₂ ↦ wInner_cWeight_eq_zero_iff_ne.2
/-
**AddChar.instFintype** 是 Mathlib 中的一个实例，位于命名空间 `AddChar`。
形式化陈述：instFintype [Finite G] : Fintype (AddChar G R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance instFintype [Finite G] : Fintype (AddChar G R) :=
  @Fintype.ofFinite _ (AddChar.linearIndependent G R).finite
/-
**AddChar.card_addChar_le** 是 Mathlib 中的一个定理，位于命名空间 `AddChar`。
形式化陈述：∀ (G : Type u_1) (R : Type u_3) [inst : AddCommGroup G] [inst_1 : RCLike R
] [inst_2 : Fintype G],   Fintype.card (AddChar G R) ≤ Fintype.card G
参数：G : Type u_1；R : Type u_3；AddChar G R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.finrank_fintype_fun_eq_card`：Module.finrank_fintype_fun_eq_card :
 finrank R (η -> R) = Fintype.card η
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `LinearIndependent.fintype_card_le_finrank`：fintype_card_le_finrank [Modu
le.Finite R M] {ι : Type*} [Fintype ι] {b : ι -> M} (h : LinearIndependent R b) 
: Fintype.card ι <= finrank R M
· 使用定理 `AddChar.linearIndependent`：∀ (G : Type u_1) (R : Type u_3) [inst : AddCo
mmGroup G] [inst_1 : RCLike R] [Finite G], LinearIndependent R DFunLike.coe
-/
@[simp] lemma card_addChar_le [Fintype G] : card (AddChar G R) ≤ card G := by
  simpa only [Module.finrank_fintype_fun_eq_card] using
    (AddChar.linearIndependent G R).fintype_card_le_finrank

end RCLike
end AddCommGroup
end AddChar

