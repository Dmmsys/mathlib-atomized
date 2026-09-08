/-
Copyright (c) 2014 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Notation.Support
public import Mathlib.Algebra.Ring.Units
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Logic.Embedding.Basic

/-!
# Characteristic zero rings
-/

@[expose] public section

assert_not_exists Field

open Function Set

variable {α R S : Type*} {n : ℕ}

section AddMonoidWithOne
variable [AddMonoidWithOne R] [CharZero R]

/-- `Nat.cast` as an embedding into monoids of characteristic `0`. -/
@[simps]
/-
**Nat.castEmbedding** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Nat.castEmbedding : Nat ↪ R
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.cast_injective`：cast_injective : Function.Injective (Nat.cast : Nat 
-> R)

--- 原说明 ---
`Nat.cast` as an embedding into monoids of characteristic `0`.
-/
def Nat.castEmbedding : ℕ ↪ R := ⟨Nat.cast, cast_injective⟩
/-
**CharZero.NeZero.two** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：CharZero.NeZero.two : NeZero (2 : R) where out
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_two`：cast_two [NatCast R] : ((2 : Nat) : R) = (2 : R)
· 使用定理 `Nat.cast_ne_zero`：cast_ne_zero {n : Nat} : (n : R) != 0 ↔ n != 0
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
-/
instance CharZero.NeZero.two : NeZero (2 : R) where
  out := by rw [← Nat.cast_two, Nat.cast_ne_zero]; decide

namespace Function

/-
**Function.support_natCast** 是 Mathlib 中的一个引理，位于命名空间 `Function`。
形式化陈述：support_natCast (hn : n != 0) : support (n : α -> R) = univ
参数：hn : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.support_const`：∀ {ι : Type u_1} {M : Type u_3} [inst : Zero M] 
{c : M}, c ≠ 0 → (Function.support fun x => c) = Set.univ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_ne_zero`：cast_ne_zero {n : Nat} : (n : R) != 0 ↔ n != 0
-/
lemma support_natCast (hn : n ≠ 0) : support (n : α → R) = univ :=
  support_const <| Nat.cast_ne_zero.2 hn
/-
**Function.mulSupport_natCast** 是 Mathlib 中的一个引理，位于命名空间 `Function`。
形式化陈述：mulSupport_natCast (hn : n != 1) : mulSupport (n : α -> R) = univ
参数：hn : n != 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Function.mulSupport_const`：mulSupport_const {c : M} (hc : c != 1) : (mul
Support fun _ : ι => c) = Set.univ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_ne_one`：cast_ne_one {n : Nat} : (n : R) != 1 ↔ n != 1
-/
lemma mulSupport_natCast (hn : n ≠ 1) : mulSupport (n : α → R) = univ :=
  mulSupport_const <| Nat.cast_ne_one.2 hn

end Function
end AddMonoidWithOne

section NonAssocSemiring
variable [NonAssocSemiring R] [NonAssocSemiring S]

namespace RingHom

/-
**RingHom.charZero** 是 Mathlib 中的一个引理，位于命名空间 `RingHom`。
形式化陈述：charZero (ϕ : R ->+* S) [CharZero S] : CharZero R where cast_injective a b
 h
参数：ϕ : R ->+* S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CharZero.cast_injective`：∀ {R : Type u_1} {inst : AddMonoidWithOne R} [s
elf : CharZero R], Function.Injective Nat.cast
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_natCast`：map_natCast [FunLike F R S] [RingHomClass F R S] (f : F) : 
forall n : Nat, f (n : R) = n
-/
lemma charZero (ϕ : R →+* S) [CharZero S] : CharZero R where
  cast_injective a b h := CharZero.cast_injective (R := S) <| by
    rw [← map_natCast ϕ, ← map_natCast ϕ, h]
/-
**RingHom.charZero_iff** 是 Mathlib 中的一个引理，位于命名空间 `RingHom`。
形式化陈述：charZero_iff {ϕ : R ->+* S} (hϕ : Injective ϕ) : CharZero R ↔ CharZero S
参数：hϕ : Injective ϕ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_inj`：cast_inj {m n : Nat} : (m : R) = n ↔ m = n
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `map_natCast`：map_natCast [FunLike F R S] [RingHomClass F R S] (f : F) : 
forall n : Nat, f (n : R) = n
· 使用引理 `RingHom.charZero`：charZero (ϕ : R ->+* S) [CharZero S] : CharZero R wher
e cast_injective a b h
-/
lemma charZero_iff {ϕ : R →+* S} (hϕ : Injective ϕ) : CharZero R ↔ CharZero S :=
  ⟨fun hR =>
    ⟨by intro a b h; rwa [← @Nat.cast_inj R, ← hϕ.eq_iff, map_natCast ϕ, map_natCast ϕ]⟩,
    fun _ => ϕ.charZero⟩
/-
**RingHom.injective_nat** 是 Mathlib 中的一个引理，位于命名空间 `RingHom`。
形式化陈述：injective_nat (f : Nat ->+* R) [CharZero R] : Injective f
参数：f : Nat ->+* R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.cast_injective`：cast_injective : Function.Injective (Nat.cast : Nat 
-> R)
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
-/
lemma injective_nat (f : ℕ →+* R) [CharZero R] : Injective f :=
  Subsingleton.elim (Nat.castRingHom _) f ▸ Nat.cast_injective

end RingHom

variable [NoZeroDivisors R] [CharZero R] {a : R}

@[simp]
/-
**add_self_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：add_self_eq_zero {a : R} : a + a = 0 ↔ a = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem add_self_eq_zero {a : R} : a + a = 0 ↔ a = 0 := by
  simp only [(two_mul a).symm, mul_eq_zero, two_ne_zero, false_or]

end NonAssocSemiring

section Semiring
variable [Semiring R] [CharZero R]

/-
**Nat.cast_pow_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {R : Type u_2} {n : ℕ} [inst : Semiring R] [CharZero R] {a : ℕ}, n ≠ 0 →
 (↑a ^ n = 1 ↔ a = 1)
参数：↑a ^ n = 1 ↔ a = 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma Nat.cast_pow_eq_one {a : ℕ} (hn : n ≠ 0) : (a : R) ^ n = 1 ↔ a = 1 := by
  simp [← cast_pow, cast_eq_one, hn]

variable [IsCancelMulZero R]

/-- A characteristic zero domain is torsion-free. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A characteristic zero domain is torsion-free.
-/
instance (priority := 100) IsAddTorsionFree.of_isCancelMulZero_charZero : IsAddTorsionFree R where
  nsmul_right_injective n hn a b hab := by simpa [hn] using hab

end Semiring

section NonAssocRing
variable [NonAssocRing R] [NoZeroDivisors R] [CharZero R]

-- `scoped` attribute here and below because the `simp` keys are weak
-- (see https://github.com/leanprover-community/mathlib4/pull/15631)
/-
**CharZero.neg_eq_self_iff** 是 Mathlib 中的一个定理，位于命名空间 `CharZero`。
形式化陈述：∀ {R : Type u_2} [inst : NonAssocRing R] [NoZeroDivisors R] [CharZero R] {
a : R}, -a = a ↔ a = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `neg_eq_iff_add_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, 
-a = b ↔ a + b = 0
· 使用定理 `add_self_eq_zero`：add_self_eq_zero {a : R} : a + a = 0 ↔ a = 0
-/
@[scoped simp] theorem CharZero.neg_eq_self_iff {a : R} : -a = a ↔ a = 0 :=
  neg_eq_iff_add_eq_zero.trans add_self_eq_zero
/-
**CharZero.eq_neg_self_iff** 是 Mathlib 中的一个定理，位于命名空间 `CharZero`。
形式化陈述：∀ {R : Type u_2} [inst : NonAssocRing R] [NoZeroDivisors R] [CharZero R] {
a : R}, a = -a ↔ a = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `eq_neg_iff_add_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, 
a = -b ↔ a + b = 0
· 使用定理 `add_self_eq_zero`：add_self_eq_zero {a : R} : a + a = 0 ↔ a = 0
-/
@[scoped simp] theorem CharZero.eq_neg_self_iff {a : R} : a = -a ↔ a = 0 :=
  eq_neg_iff_add_eq_zero.trans add_self_eq_zero
/-
**nat_mul_inj** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nat_mul_inj {n : Nat} {a b : R} (h : (n : R) * a = (n : R) * b) : n = 0 ∨ 
a = b
参数：h : (n : R) * a = (n : R) * b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `mul_eq_zero`：mul_eq_zero : a * b = 0 ↔ a = 0 ∨ b = 0
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
-/
theorem nat_mul_inj {n : ℕ} {a b : R} (h : (n : R) * a = (n : R) * b) : n = 0 ∨ a = b := by
  rw [← sub_eq_zero, ← mul_sub, mul_eq_zero, sub_eq_zero] at h
  exact mod_cast h
/-
**nat_mul_inj'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nat_mul_inj' {n : Nat} {a b : R} (h : (n : R) * a = (n : R) * b) (w : n !=
 0) : a = b
参数：h : (n : R) * a = (n : R) * b；w : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `nat_mul_inj`：nat_mul_inj {n : Nat} {a b : R} (h : (n : R) * a = (n : R) 
* b) : n = 0 ∨ a = b
-/
theorem nat_mul_inj' {n : ℕ} {a b : R} (h : (n : R) * a = (n : R) * b) (w : n ≠ 0) : a = b := by
  simpa [w] using nat_mul_inj h

end NonAssocRing

section Ring
variable [Ring R] [CharZero R]

@[simp]
/-
**units_ne_neg_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：units_ne_neg_self (u : Rˣ) : u != -u
参数：u : Rˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
theorem units_ne_neg_self (u : Rˣ) : u ≠ -u := by
  simp_rw [ne_eq, Units.ext_iff, Units.val_neg, eq_neg_iff_add_eq_zero, ← two_mul,
    Units.mul_left_eq_zero, two_ne_zero, not_false_iff]

@[simp]
/-
**neg_units_ne_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：neg_units_ne_self (u : Rˣ) : -u != u
参数：u : Rˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `units_ne_neg_self`：units_ne_neg_self (u : Rˣ) : u != -u
-/
theorem neg_units_ne_self (u : Rˣ) : -u ≠ u := (units_ne_neg_self u).symm

end Ring

