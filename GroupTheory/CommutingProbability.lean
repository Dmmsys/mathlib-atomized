/-
Copyright (c) 2022 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.GroupTheory.Abelianization.Finite
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Qify

/-!
# Commuting Probability

This file introduces the commuting probability of finite groups.

## Main definitions
* `commProb`: The commuting probability of a finite type with a multiplication operation.

## TODO
* Neumann's theorem.
-/

@[expose] public section

assert_not_exists Ideal TwoSidedIdeal

noncomputable section

open Fintype

variable (M : Type*) [Mul M]

/-- The commuting probability of a finite type with a multiplication operation. -/
/-
**commProb** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：commProb : Rat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The commuting probability of a finite type with a multiplication operation.
-/
def commProb : ℚ :=
  Nat.card { p : M × M // Commute p.1 p.2 } / (Nat.card M : ℚ) ^ 2
/-
**commProb_def** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：commProb_def : commProb M = Nat.card { p : M × M // Commute p.1 p.2 } / (N
at.card M : Rat) ^ 2
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem commProb_def :
    commProb M = Nat.card { p : M × M // Commute p.1 p.2 } / (Nat.card M : ℚ) ^ 2 :=
  rfl
/-
**commProb_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：commProb_prod (M' : Type*) [Mul M'] : commProb (M × M') = commProb M * com
mProb M'
参数：M' : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_mul_div_comm`：div_mul_div_comm : a / b * (c / d) = a * c / (b * d)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.card_prod`：card_prod (α β : Type*) : Nat.card (α × β) = Nat.card α *
 Nat.card β
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `mul_pow`：mul_pow {ea₁ b c₁ : Nat} {xa₁ : R} (_ : ea₁ * b = c₁) (_ : a₂ ^
 b = c₂) : (xa₁ ^ ea₁ * a₂ : R) ^ b = xa₁ ^ c₁ * c₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Nat.card_congr`：card_congr (f : α ≃ β) : Nat.card α = Nat.card β
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem commProb_prod (M' : Type*) [Mul M'] : commProb (M × M') = commProb M * commProb M' := by
  simp_rw [commProb_def, div_mul_div_comm, Nat.card_prod, Nat.cast_mul, mul_pow, ← Nat.cast_mul,
    ← Nat.card_prod, Commute, SemiconjBy, Prod.ext_iff]
  congr 2
  exact Nat.card_congr ⟨fun x => ⟨⟨⟨x.1.1.1, x.1.2.1⟩, x.2.1⟩, ⟨⟨x.1.1.2, x.1.2.2⟩, x.2.2⟩⟩,
    fun x => ⟨⟨⟨x.1.1.1, x.2.1.1⟩, ⟨x.1.1.2, x.2.1.2⟩⟩, ⟨x.1.2, x.2.2⟩⟩, fun x => rfl, fun x => rfl⟩
/-
**commProb_pi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：commProb_pi {α : Type*} (i : α -> Type*) [Fintype α] [forall a, Mul (i a)]
 : commProb (forall a, i a) = ∏ a, commProb (i a)
参数：i : α -> Type*；i a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_div_distrib`：prod_div_distrib (f g : ι -> G) : ∏ x in s, f x
 / g x = (∏ x in s, f x) / ∏ x in s, g x
· 使用定理 `Finset.prod_pow`：prod_pow (s : Finset ι) (n : Nat) (f : ι -> M) : ∏ x in
 s, f x ^ n = (∏ x in s, f x) ^ n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Nat.card_congr`：card_congr (f : α ≃ β) : Nat.card α = Nat.card β
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem commProb_pi {α : Type*} (i : α → Type*) [Fintype α] [∀ a, Mul (i a)] :
    commProb (∀ a, i a) = ∏ a, commProb (i a) := by
  simp_rw [commProb_def, Finset.prod_div_distrib, Finset.prod_pow, ← Nat.cast_prod,
    ← Nat.card_pi, Commute, SemiconjBy, funext_iff]
  congr 2
  exact Nat.card_congr ⟨fun x a => ⟨⟨x.1.1 a, x.1.2 a⟩, x.2 a⟩, fun x => ⟨⟨fun a => (x a).1.1,
    fun a => (x a).1.2⟩, fun a => (x a).2⟩, fun x => rfl, fun x => rfl⟩
/-
**commProb_function** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：commProb_function {α β : Type*} [Fintype α] [Mul β] : commProb (α -> β) = 
(commProb β) ^ Fintype.card α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `commProb_pi`：commProb_pi {α : Type*} (i : α -> Type*) [Fintype α] [foral
l a, Mul (i a)] : commProb (forall a, i a) = ∏ a, commProb (i a)
· 使用定理 `Finset.prod_const`：prod_const (b : M) : ∏ _x in s, b = b ^ #s
· 使用定理 `Finset.card_univ`：Finset.card_univ [Fintype α] : #(univ : Finset α) = Fi
ntype.card α
-/
theorem commProb_function {α β : Type*} [Fintype α] [Mul β] :
    commProb (α → β) = (commProb β) ^ Fintype.card α := by
  rw [commProb_pi, Finset.prod_const, Finset.card_univ]

@[simp]
/-
**commProb_eq_zero_of_infinite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：commProb_eq_zero_of_infinite [Infinite M] : commProb M = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `div_eq_zero_iff`：div_eq_zero_iff : a / b = 0 ↔ a = 0 ∨ b = 0
· 使用定理 `Nat.cast_eq_zero`：cast_eq_zero {n : Nat} : (n : R) = 0 ↔ n = 0
· 使用定理 `Nat.card_eq_zero_of_infinite`：∀ {α : Type u_1} [Infinite α], Nat.card α 
= 0
-/
theorem commProb_eq_zero_of_infinite [Infinite M] : commProb M = 0 :=
  div_eq_zero_iff.2 (Or.inl (Nat.cast_eq_zero.2 Nat.card_eq_zero_of_infinite))

variable [Finite M]
/-
**commProb_pos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：commProb_pos [h : Nonempty M] : 0 < commProb M
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nonempty.elim`：∀ {α : Sort u} {p : Prop}, Nonempty α → (∀ (a : α), p) → 
p
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_pos`：cast_pos {α} [Semiring α] [PartialOrder α] [IsOrderedRing 
α] [Nontrivial α] {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Finite.card_pos_iff`：Finite.card_pos_iff [Finite α] : 0 < Nat.card α ↔ N
onempty α
· 使用定理 `Finite.instProd`：∀ {α : Type u_1} {β : Type u_2} [Finite α] [Finite β], 
Finite (α × β)
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用定理 `Finite.card_pos`：Finite.card_pos [Finite α] [h : Nonempty α] : 0 < Nat.c
ard α
-/
theorem commProb_pos [h : Nonempty M] : 0 < commProb M :=
  h.elim fun x ↦
    div_pos (Nat.cast_pos.mpr (Finite.card_pos_iff.mpr ⟨⟨(x, x), rfl⟩⟩))
      (pow_pos (Nat.cast_pos.mpr Finite.card_pos) 2)
/-
**commProb_le_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：commProb_le_one : commProb M <= 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `div_le_one_of_le₀`：div_le_one_of_le₀ [ZeroLEOneClass G₀] (h : a <= b) (h
b : 0 <= b) : a / b <= 1
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Rat.instAddLeftMono`：AddLeftMono ℚ
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.card_prod`：card_prod (α β : Type*) : Nat.card (α × β) = Nat.card α *
 Nat.card β
· 使用定理 `Finite.card_subtype_le`：card_subtype_le [Finite α] (p : α -> Prop) : Nat
.card { x // p x } <= Nat.card α
· 使用定理 `Finite.instProd`：∀ {α : Type u_1} {β : Type u_2} [Finite α] [Finite β], 
Finite (α × β)
· 使用引理 `sq_nonneg`：sq_nonneg [ExistsAddOfLE R] [PosMulMono R] [AddLeftMono R] (a
 : R) : 0 <= a ^ 2
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
-/
theorem commProb_le_one : commProb M ≤ 1 := by
  refine div_le_one_of_le₀ ?_ (sq_nonneg (Nat.card M : ℚ))
  norm_cast
  rw [sq, ← Nat.card_prod]
  apply Finite.card_subtype_le

variable {M}
/-
**commProb_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：commProb_eq_one_iff [h : Nonempty M] : commProb M = 1 ↔ IsMulCommutative M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `commProb.eq_1`：∀ (M : Type u_1) [inst : Mul M], commProb M = ↑(Nat.card 
{ p // Commute p.1 p.2 }) / ↑(Nat.card M) ^ 2
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.coe_ofPred`：Set.coe_ofPred (p : α -> Prop) : ↥{ x | p x } = { x // p
 x }
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用引理 `div_eq_one_iff_eq`：div_eq_one_iff_eq (hb : b != 0) : a / b = 1 ↔ a = b
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_ne_zero`：cast_ne_zero {n : Nat} : (n : R) != 0 ↔ n != 0
· 使用定理 `Fintype.card_ne_zero`：card_ne_zero [Nonempty α] : card α != 0
· 使用定理 `Nat.cast_pow`：∀ {α : Type u_1} [inst : Semiring α] (m n : ℕ), ↑(m ^ n) =
 ↑m ^ n
· 使用定理 `Nat.cast_inj`：cast_inj {m n : Nat} : (m : R) = n ↔ m = n
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `Fintype.card_prod`：Fintype.card_prod (α β : Type*) [Fintype α] [Fintype 
β] : Fintype.card (α × β) = Fintype.card α * Fintype.card β
· 使用定理 `set_fintype_card_eq_univ_iff`：set_fintype_card_eq_univ_iff [Fintype α] (
s : Set α) [Fintype s] : Fintype.card s = Fintype.card α ↔ s = Set.univ
· 使用定理 `Set.eq_univ_iff_forall`：eq_univ_iff_forall {s : Set α} : s = univ ↔ fora
ll x, x in s
· 使用引理 `mul_comm'`：mul_comm' {M : Type*} [Mul M] [IsMulCommutative M] (a b : M) 
: a * b = b * a
-/
theorem commProb_eq_one_iff [h : Nonempty M] : commProb M = 1 ↔ IsMulCommutative M := by
  classical
  have := Fintype.ofFinite M
  rw [commProb, ← Set.coe_ofPred, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  rw [div_eq_one_iff_eq, ← Nat.cast_pow, Nat.cast_inj, sq, ← card_prod,
    set_fintype_card_eq_univ_iff, Set.eq_univ_iff_forall]
  · exact ⟨fun h ↦ ⟨⟨fun x y ↦ h (x, y)⟩⟩, fun h x ↦ mul_comm' ..⟩
  · exact pow_ne_zero 2 (Nat.cast_ne_zero.mpr card_ne_zero)

variable (G : Type*) [Group G]
/-
**commProb_def'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：commProb_def' : commProb G = Nat.card (ConjClasses G) / Nat.card G
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `commProb.eq_1`：∀ (M : Type u_1) [inst : Mul M], commProb M = ↑(Nat.card 
{ p // Commute p.1 p.2 }) / ↑(Nat.card M) ^ 2
· 使用定理 `card_comm_eq_card_conjClasses_mul_card`：card_comm_eq_card_conjClasses_mu
l_card (G : Type*) [Group G] : Nat.card { p : G × G // Commute p.1 p.2 } = Nat.c
ard (ConjClasses G) * Nat.ca…
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用引理 `mul_div_mul_right`：mul_div_mul_right (a b : G₀) (hc : c != 0) : a * c / 
(b * c) = a / b
-/
theorem commProb_def' : commProb G = Nat.card (ConjClasses G) / Nat.card G := by
  rw [commProb, card_comm_eq_card_conjClasses_mul_card, Nat.cast_mul, sq]
  by_cases h : (Nat.card G : ℚ) = 0
  · rw [h, zero_mul, div_zero, div_zero]
  · exact mul_div_mul_right _ _ h

variable {G}
variable [Finite G] (H : Subgroup G)
/-
**Subgroup.commProb_subgroup_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subgroup.commProb_subgroup_le : commProb H <= commProb G * (H.index : Rat)
 ^ 2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `commProb_def`：commProb_def : commProb M = Nat.card { p : M × M // Commut
e p.1 p.2 } / (Nat.card M : Rat) ^ 2
· 使用引理 `div_le_iff₀`：div_le_iff₀ (hc : 0 < c) : b / c <= a ↔ b <= a * c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_pos`：cast_pos {α} [Semiring α] [PartialOrder α] [IsOrderedRing 
α] [Nontrivial α] {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Finite.card_pos`：Finite.card_pos [Finite α] [h : Nonempty α] : 0 < Nat.c
ard α
· 使用定理 `Subgroup.instFiniteSubtypeMem`：∀ {G : Type u_1} [inst : Group G] (K : Su
bgroup G) [Finite G], Finite ↥K
· 使用定理 `One.instNonempty`：∀ {α : Type u} [One α], Nonempty α
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_pow`：mul_pow {ea₁ b c₁ : Nat} {xa₁ : R} (_ : ea₁ * b = c₁) (_ : a₂ ^
 b = c₂) : (xa₁ ^ ea₁ * a₂ : R) ^ b = xa₁ ^ c₁ * c₂
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Subgroup.card_mul_index`：card_mul_index : Nat.card H * H.index = Nat.car
d G
· 使用引理 `div_mul_cancel₀`：div_mul_cancel₀ (a : G₀) (h : b != 0) : a / b * b = a
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `Nat.cast_ne_zero`：cast_ne_zero {n : Nat} : (n : R) != 0 ↔ n != 0
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Nat.cast_le`：cast_le : (m : α) <= n ↔ m <= n
· 使用定理 `Rat.instAddLeftMono`：AddLeftMono ℚ
· 使用引理 `Nat.card_le_card_of_injective`：card_le_card_of_injective {α : Type u} {β
 : Type v} [Finite β] (f : α -> β) (hf : Injective f) : Nat.card α <= Nat.card β
（共 36 条，此处仅展示前 30 条）
-/
theorem Subgroup.commProb_subgroup_le : commProb H ≤ commProb G * (H.index : ℚ) ^ 2 := by
  /- After rewriting with `commProb_def`, we reduce to showing that `G` has at least as many
      commuting pairs as `H`. -/
  rw [commProb_def, commProb_def, div_le_iff₀, mul_assoc, ← mul_pow, ← Nat.cast_mul,
    mul_comm H.index, H.card_mul_index, div_mul_cancel₀, Nat.cast_le]
  · refine Nat.card_le_card_of_injective (fun p ↦ ⟨⟨p.1.1, p.1.2⟩, Subtype.ext_iff.mp p.2⟩) ?_
    exact fun p q h ↦ by simpa only [Subtype.ext_iff, Prod.ext_iff] using h
  · exact pow_ne_zero 2 (Nat.cast_ne_zero.mpr Finite.card_pos.ne')
  · exact pow_pos (Nat.cast_pos.mpr Finite.card_pos) 2
/-
**Subgroup.commProb_quotient_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subgroup.commProb_quotient_le [H.Normal] : commProb (G ⧸ H) <= commProb G 
* Nat.card H
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `commProb_def'`：commProb_def' : commProb G = Nat.card (ConjClasses G) / N
at.card G
· 使用引理 `div_le_iff₀`：div_le_iff₀ (hc : 0 < c) : b / c <= a ↔ b <= a * c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_pos`：cast_pos {α} [Semiring α] [PartialOrder α] [IsOrderedRing 
α] [Nontrivial α] {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Finite.card_pos`：Finite.card_pos [Finite α] [h : Nonempty α] : 0 < Nat.c
ard α
· 使用定理 `Subgroup.finiteIndex_of_finite`：∀ {G : Type u_1} [inst : Group G] {H : S
ubgroup G} [Finite G], H.FiniteIndex
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `Subgroup.index.eq_1`：∀ {G : Type u_1} [inst : Group G] (H : Subgroup G),
 H.index = Nat.card (G ⧸ H)
· 使用定理 `Subgroup.card_mul_index`：card_mul_index : Nat.card H * H.index = Nat.car
d G
· 使用引理 `div_mul_cancel₀`：div_mul_cancel₀ (a : G₀) (h : b != 0) : a / b * b = a
· 使用定理 `Nat.cast_ne_zero`：cast_ne_zero {n : Nat} : (n : R) != 0 ↔ n != 0
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `One.instNonempty`：∀ {α : Type u} [One α], Nonempty α
· 使用定理 `Nat.cast_le`：cast_le : (m : α) <= n ↔ m <= n
· 使用定理 `Rat.instAddLeftMono`：AddLeftMono ℚ
· 使用引理 `Nat.card_le_card_of_surjective`：card_le_card_of_surjective {α : Type u} 
{β : Type v} [Finite α] (f : α -> β) (hf : Surjective f) : Nat.card β <= Nat.car
d α
· 使用定理 `instFiniteConjClasses`：∀ {α : Type u_1} [inst : Monoid α] [Finite α], Fi
nite (ConjClasses α)
· 使用定理 `ConjClasses.map_surjective`：map_surjective {f : α ->* β} (hf : Function.
Surjective f) : Function.Surjective (ConjClasses.map f)
· 使用定理 `Quotient.mk''_surjective`：∀ {α : Sort u_1} {s₁ : Setoid α}, Function.Sur
jective Quotient.mk''
-/
theorem Subgroup.commProb_quotient_le [H.Normal] : commProb (G ⧸ H) ≤ commProb G * Nat.card H := by
  /- After rewriting with `commProb_def'`, we reduce to showing that `G` has at least as many
      conjugacy classes as `G ⧸ H`. -/
  rw [commProb_def', commProb_def', div_le_iff₀, mul_assoc, ← Nat.cast_mul, ← Subgroup.index,
    H.card_mul_index, div_mul_cancel₀, Nat.cast_le]
  · apply Nat.card_le_card_of_surjective (f := ConjClasses.map (QuotientGroup.mk' H))
    exact ConjClasses.map_surjective Quotient.mk''_surjective
  · exact Nat.cast_ne_zero.mpr Finite.card_pos.ne'
  · exact Nat.cast_pos.mpr Finite.card_pos

variable (G)
/-
**inv_card_commutator_le_commProb** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inv_card_commutator_le_commProb : (↑(Nat.card (commutator G)))⁻¹ <= commPr
ob G
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `inv_le_iff_one_le_mul₀`：inv_le_iff_one_le_mul₀ (ha : 0 < a) : a⁻¹ <= b ↔
 1 <= b * a
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `Nat.cast_pos`：cast_pos {α} [Semiring α] [PartialOrder α] [IsOrderedRing 
α] [Nontrivial α] {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Finite.card_pos`：Finite.card_pos [Finite α] [h : Nonempty α] : 0 < Nat.c
ard α
· 使用定理 `Subgroup.instFiniteSubtypeMem`：∀ {G : Type u_1} [inst : Group G] (K : Su
bgroup G) [Finite G], Finite ↥K
· 使用定理 `One.instNonempty`：∀ {α : Type u} [One α], Nonempty α
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `ge_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `commProb_eq_one_iff`：commProb_eq_one_iff [h : Nonempty M] : commProb M =
 1 ↔ IsMulCommutative M
· 使用定理 `instFiniteAbelianization`：∀ {G : Type u_1} [inst : Group G] [Finite G], 
Finite (Abelianization G)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Subgroup.commProb_quotient_le`：Subgroup.commProb_quotient_le [H.Normal] 
: commProb (G ⧸ H) <= commProb G * Nat.card H
· 使用定理 `instNormalCommutator`：∀ (G : Type u_1) [inst : Group G], (commutator G).
Normal
-/
theorem inv_card_commutator_le_commProb : (↑(Nat.card (commutator G)))⁻¹ ≤ commProb G :=
  (inv_le_iff_one_le_mul₀ (Nat.cast_pos.mpr Finite.card_pos)).mpr
    (le_trans (ge_of_eq (commProb_eq_one_iff.mpr (Abelianization.commGroup G).to_isCommutative))
      (commutator G).commProb_quotient_le)

-- Construction of group with commuting probability 1/n
namespace DihedralGroup

/-
**DihedralGroup.commProb_odd** 是 Mathlib 中的一个引理，位于命名空间 `DihedralGroup`。
形式化陈述：commProb_odd {n : Nat} (hn : Odd n) : commProb (DihedralGroup n) = (n + 3)
 / (4 * n)
参数：hn : Odd n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `commProb_def'`：commProb_def' : commProb G = Nat.card (ConjClasses G) / N
at.card G
· 使用引理 `DihedralGroup.card_conjClasses_odd`：card_conjClasses_odd (hn : Odd n) : 
Nat.card (ConjClasses (DihedralGroup n)) = (n + 3) / 2
· 使用定理 `DihedralGroup.nat_card`：nat_card : Nat.card (DihedralGroup n) = 2 * n
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Nat.cast_div_charZero`：cast_div_charZero (hnm : n ∣ m) : (↑(m / n) : K) 
= m / n
· 使用定理 `Nat.dvd_iff_mod_eq_zero`：∀ {m n : ℕ}, m ∣ n ↔ n % m = 0
· 使用定理 `Nat.add_mod`：∀ (a b n : ℕ), (a + b) % n = (a % n + b % n) % n
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Nat.odd_iff`：odd_iff : Odd n ↔ n % 2 = 1
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `div_div`：div_div : a / b / c = a / (b * c)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Mathlib.Meta.NormNum.isNat_eq_true`：∀ {α : Type u} [inst : AddMonoidWith
One α] {a b : α} {c : ℕ},   Mathlib.Meta.NormNum.IsNat a c → Mathlib.Meta.NormNu
m.IsNat b c → a = b
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
-/
lemma commProb_odd {n : ℕ} (hn : Odd n) :
    commProb (DihedralGroup n) = (n + 3) / (4 * n) := by
  rw [commProb_def', DihedralGroup.card_conjClasses_odd hn, nat_card]
  qify [show 2 ∣ n + 3 by rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.odd_iff.mp hn]]
  rw [div_div, ← mul_assoc]
  congr
  norm_num

/-- A list of Dihedral groups whose product will have commuting probability `1 / n`. -/
/-
**DihedralGroup.reciprocalFactors** 是 Mathlib 中的一个定义，位于命名空间 `DihedralGroup`。
形式化陈述：reciprocalFactors (n : Nat) : List Nat
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A list of Dihedral groups whose product will have commuting probability `1 / n`.
-/
def reciprocalFactors (n : ℕ) : List ℕ :=
  if _ : n = 0 then [0]
  else if _ : n = 1 then []
  else if Even n then
    3 :: reciprocalFactors (n / 2)
  else
    n % 4 * n :: reciprocalFactors (n / 4 + 1)
/-
**DihedralGroup.reciprocalFactors_zero** 是 Mathlib 中的一个定理，位于命名空间 `DihedralGroup`
。
形式化陈述：DihedralGroup.reciprocalFactors 0 = [0]
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DihedralGroup.reciprocalFactors.eq_def`：∀ (n : ℕ),   DihedralGroup.recip
rocalFactors n =     if x : n = 0 then [0]     else       if x : n = 1 then []  
     else         if Even n …
-/
@[simp] lemma reciprocalFactors_zero : reciprocalFactors 0 = [0] := by
  unfold reciprocalFactors; rfl
/-
**DihedralGroup.reciprocalFactors_one** 是 Mathlib 中的一个定理，位于命名空间 `DihedralGroup`。
形式化陈述：DihedralGroup.reciprocalFactors 1 = []
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DihedralGroup.reciprocalFactors.eq_def`：∀ (n : ℕ),   DihedralGroup.recip
rocalFactors n =     if x : n = 0 then [0]     else       if x : n = 1 then []  
     else         if Even n …
-/
@[simp] lemma reciprocalFactors_one : reciprocalFactors 1 = [] := by
  unfold reciprocalFactors; rfl
/-
**DihedralGroup.reciprocalFactors_even** 是 Mathlib 中的一个引理，位于命名空间 `DihedralGroup`
。
形式化陈述：reciprocalFactors_even {n : Nat} (h0 : n != 0) (h2 : Even n) : reciprocalF
actors n = 3 :: reciprocalFactors (n / 2)
参数：h0 : n != 0；h2 : Even n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false`：¬False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DihedralGroup.reciprocalFactors.eq_1`：∀ (n : ℕ),   DihedralGroup.recipro
calFactors n =     if x : n = 0 then [0]     else       if x : n = 1 then []    
   else         if Even n …
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
lemma reciprocalFactors_even {n : ℕ} (h0 : n ≠ 0) (h2 : Even n) :
    reciprocalFactors n = 3 :: reciprocalFactors (n / 2) := by
  have h1 : n ≠ 1 := by
    rintro rfl
    norm_num at h2
  rw [reciprocalFactors, dif_neg h0, dif_neg h1, if_pos h2]
/-
**DihedralGroup.reciprocalFactors_odd** 是 Mathlib 中的一个引理，位于命名空间 `DihedralGroup`。
形式化陈述：reciprocalFactors_odd {n : Nat} (h1 : n != 1) (h2 : Odd n) : reciprocalFac
tors n = n % 4 * n :: reciprocalFactors (n / 4 + 1)
参数：h1 : n != 1；h2 : Odd n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false`：¬False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `DihedralGroup.reciprocalFactors.eq_1`：∀ (n : ℕ),   DihedralGroup.recipro
calFactors n =     if x : n = 0 then [0]     else       if x : n = 1 then []    
   else         if Even n …
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.not_even_iff_odd`：∀ {n : ℕ}, ¬Even n ↔ Odd n
-/
lemma reciprocalFactors_odd {n : ℕ} (h1 : n ≠ 1) (h2 : Odd n) :
    reciprocalFactors n = n % 4 * n :: reciprocalFactors (n / 4 + 1) := by
  have h0 : n ≠ 0 := by
    rintro rfl
    norm_num [← Nat.not_even_iff_odd] at h2
  rw [reciprocalFactors, dif_neg h0, dif_neg h1, if_neg (Nat.not_even_iff_odd.2 h2)]

/-- A finite product of Dihedral groups. -/
/-
**DihedralGroup.Product** 是 Mathlib 中的一个缩写定义，位于命名空间 `DihedralGroup`。
形式化陈述：Product (l : List Nat) : Type
参数：l : List Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A finite product of Dihedral groups.
-/
abbrev Product (l : List ℕ) : Type :=
  ∀ i : Fin l.length, DihedralGroup l[i]
/-
**DihedralGroup.commProb_nil** 是 Mathlib 中的一个引理，位于命名空间 `DihedralGroup`。
形式化陈述：commProb_nil : commProb (Product []) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `commProb_pi`：commProb_pi {α : Type*} (i : α -> Type*) [Fintype α] [foral
l a, Mul (i a)] : commProb (forall a, i a) = ∏ a, commProb (i a)
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.univ_eq_empty`：univ_eq_empty [IsEmpty α] : (univ : Finset α) = ∅
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma commProb_nil : commProb (Product []) = 1 := by
  simp [Product, commProb_pi]

set_option backward.isDefEq.respectTransparency false in
/-
**DihedralGroup.commProb_cons** 是 Mathlib 中的一个引理，位于命名空间 `DihedralGroup`。
形式化陈述：commProb_cons (n : Nat) (l : List Nat) : commProb (Product (n :: l)) = com
mProb (DihedralGroup n) * commProb (Product l)
参数：n : Nat；l : List Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Nat.lt_of_succ_lt_succ`：∀ {n m : ℕ}, n.succ < m.succ → n < m
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `commProb_pi`：commProb_pi {α : Type*} (i : α -> Type*) [Fintype α] [foral
l a, Mul (i a)] : commProb (forall a, i a) = ∏ a, commProb (i a)
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Fin.prod_univ_succ`：prod_univ_succ (f : Fin (n + 1) -> M) : ∏ i, f i = f
 0 * ∏ i : Fin n, f i.succ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma commProb_cons (n : ℕ) (l : List ℕ) :
    commProb (Product (n :: l)) = commProb (DihedralGroup n) * commProb (Product l) := by
  simp only [commProb_pi, Fin.prod_univ_succ, Fin.getElem_fin, Fin.val_succ, Fin.val_zero,
    List.getElem_cons_zero, List.length_cons, List.getElem_cons_succ]

/-- Construction of a group with commuting probability `1 / n`. -/
/-
**DihedralGroup.commProb_reciprocal** 是 Mathlib 中的一个定理，位于命名空间 `DihedralGroup`。
形式化陈述：commProb_reciprocal (n : Nat) : commProb (Product (reciprocalFactors n)) =
 1 / n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DihedralGroup.reciprocalFactors_zero`：DihedralGroup.reciprocalFactors 0 
= [0]
· 使用引理 `DihedralGroup.commProb_cons`：commProb_cons (n : Nat) (l : List Nat) : co
mmProb (Product (n :: l)) = commProb (DihedralGroup n) * commProb (Product l)
· 使用引理 `DihedralGroup.commProb_nil`：commProb_nil : commProb (Product []) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `commProb_eq_zero_of_infinite`：commProb_eq_zero_of_infinite [Infinite M] 
: commProb M = 0
· 使用定理 `DihedralGroup.instInfiniteOfNatNat`：Infinite (DihedralGroup 0)
· 使用定理 `DihedralGroup.reciprocalFactors_one`：DihedralGroup.reciprocalFactors 1 =
 []
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用引理 `Nat.even_or_odd`：even_or_odd (n : Nat) : Even n ∨ Odd n
· 使用引理 `DihedralGroup.reciprocalFactors_even`：reciprocalFactors_even {n : Nat} (
h0 : n != 0) (h2 : Even n) : reciprocalFactors n = 3 :: reciprocalFactors (n / 2
)
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `Nat.lt_or_gt_of_ne`：∀ {a b : ℕ}, a ≠ b → a < b ∨ a > b
· 使用定理 `Lean.Omega.Constraint.not_sat'_of_isImpossible`：∀ {c : Omega.Constraint}
, c.isImpossible = true → ∀ {x y : Omega.Coeffs}, ¬c.sat' x y = true
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `Lean.Omega.tidy_sat`：∀ {s : Omega.Constraint} {x v : Omega.Coeffs},   s.
sat' x v = true → (Omega.tidyConstraint s x).sat' (Omega.tidyCoeffs s x) v = tru
e
· 使用定理 `Lean.Omega.combo_sat'`：∀ (s t : Omega.Constraint) (a : ℤ) (x : Omega.Coe
ffs) (b : ℤ) (y v : Omega.Coeffs),   s.sat' x v = true → t.sat' y v = true → (Om
ega.Constra…
· 使用定理 `Lean.Omega.Constraint.combine_sat'`：∀ {s t : Omega.Constraint} {x y : Om
ega.Coeffs}, s.sat' x y = true → t.sat' x y = true → (s.combine t).sat' x y = tr
ue
· 使用定理 `Lean.Omega.Constraint.addInequality_sat`：∀ {c : ℤ} {x y : Omega.Coeffs},
 c + x.dot y ≥ 0 → { lowerBound := some (-c), upperBound := none }.sat' x y = tr
ue
· 使用定理 `le_of_le_of_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `Int.sub_nonneg_of_le`：∀ {a b : ℤ}, b ≤ a → 0 ≤ a - b
· 使用定理 `Int.add_one_le_of_lt`：∀ {a b : ℤ}, a < b → a + 1 ≤ b
· 使用定理 `Lean.Omega.Int.ofNat_lt_of_lt`：∀ {x y : ℕ}, x < y → ↑x < ↑y
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Lean.Omega.Int.sub_congr`：∀ {a b c d : ℤ}, a = b → c = d → a - c = b - d
· 使用定理 `Lean.Omega.Int.add_congr`：∀ {a b c d : ℤ}, a = b → c = d → a + c = b + d
（共 111 条，此处仅展示前 30 条）

--- 原说明 ---
Construction of a group with commuting probability `1 / n`.
-/
theorem commProb_reciprocal (n : ℕ) :
    commProb (Product (reciprocalFactors n)) = 1 / n := by
  by_cases h0 : n = 0
  · rw [h0, reciprocalFactors_zero, commProb_cons, commProb_nil, mul_one, Nat.cast_zero, div_zero]
    apply commProb_eq_zero_of_infinite
  by_cases h1 : n = 1
  · rw [h1, reciprocalFactors_one, commProb_nil, Nat.cast_one, div_one]
  rcases Nat.even_or_odd n with h2 | h2
  · rw [reciprocalFactors_even h0 h2, commProb_cons, commProb_reciprocal (n / 2),
        commProb_odd (by decide)]
    simp [field, h2.two_dvd]
    norm_num
  · rw [reciprocalFactors_odd h1 h2, commProb_cons, commProb_reciprocal (n / 4 + 1)]
    have hn : Odd (n % 4) := by grind
    rw [commProb_odd (hn.mul h2), div_mul_div_comm, div_eq_div_iff] <;> norm_cast
    · grind [Nat.div_add_mod n 4, Odd]
    · positivity [hn.pos.ne']

end DihedralGroup

