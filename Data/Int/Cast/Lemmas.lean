/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Algebra.Group.TypeTags.Hom
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Parity

/-!
# Cast of integers (additional theorems)

This file proves additional properties about the *canonical* homomorphism from
the integers into an additive group with a one (`Int.cast`),
particularly results involving algebraic homomorphisms or the order structure on `ℤ`
which were not available in the import dependencies of `Data.Int.Cast.Basic`.

## Main declarations

* `castAddHom`: `cast` bundled as an `AddMonoidHom`.
* `castRingHom`: `cast` bundled as a `RingHom`.
-/

@[expose] public section

assert_not_exists RelIso IsOrderedMonoid Field

open Additive Function Multiplicative Nat

variable {F ι α β : Type*}

namespace Int

/-- Coercion `ℕ → ℤ` as a `RingHom`. -/
/-
**Int.ofNatHom** 是 Mathlib 中的一个定义，位于命名空间 `Int`。
形式化陈述：ofNatHom : Nat ->+* Int
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Coercion `ℕ → ℤ` as a `RingHom`.
-/
def ofNatHom : ℕ →+* ℤ :=
  Nat.castRingHom ℤ

section cast

/-- `coe : ℤ → α` as an `AddMonoidHom`. -/
/-
**Int.castAddHom** 是 Mathlib 中的一个定义，位于命名空间 `Int`。
形式化陈述：castAddHom (α : Type*) [AddGroupWithOne α] : Int ->+ α where toFun
参数：α : Type*。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Int.cast_zero`：cast_zero : ((0 : Int) : R) = 0
· 使用定理 `Int.cast_add`：∀ {R : Type u} [inst : AddGroupWithOne R] (m n : ℤ), ↑(m +
 n) = ↑m + ↑n

--- 原说明 ---
`coe : ℤ → α` as an `AddMonoidHom`.
-/
def castAddHom (α : Type*) [AddGroupWithOne α] : ℤ →+ α where
  toFun := Int.cast
  map_zero' := cast_zero
  map_add' := cast_add

section AddGroupWithOne
variable [AddGroupWithOne α]

/-
**Int.coe_castAddHom** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：∀ {α : Type u_3} [inst : AddGroupWithOne α], ⇑(Int.castAddHom α) = fun x =
> ↑x
参数：Int.castAddHom α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_castAddHom : ⇑(castAddHom α) = fun x : ℤ => (x : α) := rfl
/-
**Int._root_.Even.intCast** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Even.intCast {n : ℤ} (h : Even n) : Even (n : α) := h.map (castAddHom α)

variable [CharZero α] {m n : ℤ}
/-
**Int.cast_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：∀ {α : Type u_3} [inst : AddGroupWithOne α] [CharZero α] {n : ℤ}, ↑n = 0 ↔
 n = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.cast_eq_zero`：cast_eq_zero {n : Nat} : (n : R) = 0 ↔ n = 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `Int.ofNat_eq_natCast`：∀ (n : ℕ), Int.ofNat n = ↑n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `neg_eq_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a =
 0 ↔ a = 0
· 使用定理 `Int.cast_negSucc`：cast_negSucc (n : Nat) : (-[n+1] : R) = -(n + 1 : Nat)
· 使用定理 `Int.cast_zero`：cast_zero : ((0 : Int) : R) = 0
-/
@[simp] lemma cast_eq_zero : (n : α) = 0 ↔ n = 0 where
  mp h := by
    cases n
    · rw [ofNat_eq_natCast, Int.cast_natCast] at h
      exact congr_arg _ (Nat.cast_eq_zero.1 h)
    · rw [cast_negSucc, neg_eq_zero, Nat.cast_eq_zero] at h
      contradiction
  mpr h := by rw [h, cast_zero]

@[simp, norm_cast]
/-
**Int.cast_inj** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：cast_inj : (m : α) = n ↔ m = n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `Int.cast_sub`：cast_sub (m n) : ((m - n : Int) : R) = m - n
· 使用定理 `Int.cast_eq_zero`：∀ {α : Type u_3} [inst : AddGroupWithOne α] [CharZero 
α] {n : ℤ}, ↑n = 0 ↔ n = 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma cast_inj : (m : α) = n ↔ m = n := by rw [← sub_eq_zero, ← cast_sub, cast_eq_zero, sub_eq_zero]
/-
**Int.cast_injective** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：cast_injective : Injective (Int.cast : Int -> α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Int.cast_inj`：cast_inj : (m : α) = n ↔ m = n
-/
lemma cast_injective : Injective (Int.cast : ℤ → α) := fun _ _ ↦ cast_inj.1
/-
**Int.cast_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：cast_ne_zero : (n : α) != 0 ↔ n != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_congr`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Int.cast_eq_zero`：∀ {α : Type u_3} [inst : AddGroupWithOne α] [CharZero 
α] {n : ℤ}, ↑n = 0 ↔ n = 0
-/
lemma cast_ne_zero : (n : α) ≠ 0 ↔ n ≠ 0 := not_congr cast_eq_zero
/-
**Int.cast_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：∀ {α : Type u_3} [inst : AddGroupWithOne α] [CharZero α] {n : ℤ}, ↑n = 1 ↔
 n = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用引理 `Int.cast_inj`：cast_inj : (m : α) = n ↔ m = n
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma cast_eq_one : (n : α) = 1 ↔ n = 1 := by rw [← cast_one, cast_inj]
/-
**Int.cast_ne_one** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：cast_ne_one : (n : α) != 1 ↔ n != 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Int.cast_eq_one`：∀ {α : Type u_3} [inst : AddGroupWithOne α] [CharZero α
] {n : ℤ}, ↑n = 1 ↔ n = 1
-/
lemma cast_ne_one : (n : α) ≠ 1 ↔ n ≠ 1 := cast_eq_one.not

end AddGroupWithOne

section NonAssocRing
variable [NonAssocRing α]

variable (α) in
/-- `coe : ℤ → α` as a `RingHom`. -/
@[instance_reducible]
/-
**Int.castRingHom** 是 Mathlib 中的一个定义，位于命名空间 `Int`。
形式化陈述：castRingHom : Int ->+* α where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Int.cast_mul`：cast_mul {α : Type*} [NonAssocRing α] : forall m n, ((m * 
n : Int) : α) = m * n

--- 原说明 ---
`coe : ℤ → α` as a `RingHom`.
-/
def castRingHom : ℤ →+* α where
  toFun := Int.cast
  map_zero' := cast_zero
  map_add' := cast_add
  map_one' := cast_one
  map_mul' := cast_mul
/-
**Int.coe_castRingHom** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：∀ {α : Type u_3} [inst : NonAssocRing α], ⇑(Int.castRingHom α) = fun x => 
↑x
参数：Int.castRingHom α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_castRingHom : ⇑(castRingHom α) = fun x : ℤ ↦ (x : α) := rfl
/-
**Int.cast_commute** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：∀ {α : Type u_3} [inst : NonAssocRing α] (n : ℤ) (a : α), Commute (↑n) a
参数：n : ℤ；a : α；↑n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `Nat.cast_commute`：cast_commute (n : Nat) (x : α) : Commute (n : α) x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Int.cast_negSucc`：cast_negSucc (n : Nat) : (-[n+1] : R) = -(n + 1 : Nat)
-/
lemma cast_commute : ∀ (n : ℤ) (a : α), Commute ↑n a
  | (n : ℕ), x => by simpa using n.cast_commute x
  | -[n+1], x => by
    simpa only [cast_negSucc, Commute.neg_left_iff, Commute.neg_right_iff] using
      (n + 1).cast_commute (-x)
/-
**Int.cast_comm** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：cast_comm (n : Int) (x : α) : n * x = x * n
参数：n : Int；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Commute.eq`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → a *
 b = b * a
· 使用定理 `Int.cast_commute`：∀ {α : Type u_3} [inst : NonAssocRing α] (n : ℤ) (a : 
α), Commute (↑n) a
-/
lemma cast_comm (n : ℤ) (x : α) : n * x = x * n := (cast_commute ..).eq
/-
**Int.commute_cast** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：commute_cast (a : α) (n : Int) : Commute a n
参数：a : α；n : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Commute.symm`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → C
ommute b a
· 使用定理 `Int.cast_commute`：∀ {α : Type u_3} [inst : NonAssocRing α] (n : ℤ) (a : 
α), Commute (↑n) a
-/
lemma commute_cast (a : α) (n : ℤ) : Commute a n := (cast_commute ..).symm
/-
**Int._root_.zsmul_eq_mul** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma _root_.zsmul_eq_mul (a : α) : ∀ n : ℤ, n • a = n * a
  | (n : ℕ) => by rw [natCast_zsmul, nsmul_eq_mul, Int.cast_natCast]
  | -[n+1] => by simp [Nat.cast_succ, neg_add_rev, Int.cast_negSucc, add_mul]
/-
**Int._root_.zsmul_eq_mul'** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.zsmul_eq_mul' (a : α) (n : ℤ) : n • a = a * n := by
  rw [zsmul_eq_mul, (n.cast_commute a).eq]

end NonAssocRing

section Ring
variable [Ring α] {n : ℤ}

/-
**Int._root_.Odd.intCast** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Odd.intCast (hn : Odd n) : Odd (n : α) := hn.map (castRingHom α)

end Ring

/-
**Int.cast_dvd_cast** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：cast_dvd_cast [Ring α] (m n : Int) (h : m ∣ n) : (m : α) ∣ (n : α)
参数：m n : Int；h : m ∣ n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_dvd`：∀ {M : Type u_1} {N : Type u_2} [inst : Semigroup M] [inst_1 : 
Semigroup N] {F : Type u_3} [inst_2 : FunLike F M N]   [MulHomClass F M N] (f…
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
-/
theorem cast_dvd_cast [Ring α] (m n : ℤ) (h : m ∣ n) : (m : α) ∣ (n : α) :=
  map_dvd (Int.castRingHom α) h

end cast

end Int

open Int

namespace SemiconjBy
variable [Ring α] {a x y : α}

/-
**SemiconjBy.intCast_mul_right** 是 Mathlib 中的一个定理，位于命名空间 `SemiconjBy`。
形式化陈述：∀ {α : Type u_3} [inst : Ring α] {a x y : α}, SemiconjBy a x y → ∀ (n : ℤ)
, SemiconjBy a (↑n * x) (↑n * y)
参数：n : ℤ；↑n * x；↑n * y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemiconjBy.mul_right`：mul_right (h : SemiconjBy a x y) (h' : SemiconjBy 
a x' y') : SemiconjBy a (x * x') (y * y')
· 使用引理 `Int.commute_cast`：commute_cast (a : α) (n : Int) : Commute a n
-/
@[simp] lemma intCast_mul_right (h : SemiconjBy a x y) (n : ℤ) : SemiconjBy a (n * x) (n * y) :=
  SemiconjBy.mul_right (Int.commute_cast _ _) h
/-
**SemiconjBy.intCast_mul_left** 是 Mathlib 中的一个定理，位于命名空间 `SemiconjBy`。
形式化陈述：∀ {α : Type u_3} [inst : Ring α] {a x y : α}, SemiconjBy a x y → ∀ (n : ℤ)
, SemiconjBy (↑n * a) x y
参数：n : ℤ；↑n * a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemiconjBy.mul_left`：mul_left (ha : SemiconjBy a y z) (hb : SemiconjBy b
 x y) : SemiconjBy (a * b) x z
· 使用定理 `Int.cast_commute`：∀ {α : Type u_3} [inst : NonAssocRing α] (n : ℤ) (a : 
α), Commute (↑n) a
-/
@[simp] lemma intCast_mul_left (h : SemiconjBy a x y) (n : ℤ) : SemiconjBy (n * a) x y :=
  SemiconjBy.mul_left (Int.cast_commute _ _) h
/-
**SemiconjBy.intCast_mul_intCast_mul** 是 Mathlib 中的一个引理，位于命名空间 `SemiconjBy`。
形式化陈述：intCast_mul_intCast_mul (h : SemiconjBy a x y) (m n : Int) : SemiconjBy (m
 * a) (n * x) (n * y)
参数：h : SemiconjBy a x y；m n : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
lemma intCast_mul_intCast_mul (h : SemiconjBy a x y) (m n : ℤ) :
    SemiconjBy (m * a) (n * x) (n * y) := by simp [h]

end SemiconjBy

namespace Commute
section NonAssocRing
variable [NonAssocRing α] {a : α} {n : ℤ}

/-
**Commute.intCast_left** 是 Mathlib 中的一个定理，位于命名空间 `Commute`。
形式化陈述：∀ {α : Type u_3} [inst : NonAssocRing α] {a : α} {n : ℤ}, Commute (↑n) a
参数：↑n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.cast_commute`：∀ {α : Type u_3} [inst : NonAssocRing α] (n : ℤ) (a : 
α), Commute (↑n) a
-/
@[simp] lemma intCast_left : Commute (n : α) a := Int.cast_commute _ _
/-
**Commute.intCast_right** 是 Mathlib 中的一个定理，位于命名空间 `Commute`。
形式化陈述：∀ {α : Type u_3} [inst : NonAssocRing α] {a : α} {n : ℤ}, Commute a ↑n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Int.commute_cast`：commute_cast (a : α) (n : Int) : Commute a n
-/
@[simp] lemma intCast_right : Commute a n := Int.commute_cast _ _

end NonAssocRing

section Ring
variable [Ring α] {a b : α}

/-
**Commute.intCast_mul_right** 是 Mathlib 中的一个引理，位于命名空间 `Commute`。
形式化陈述：intCast_mul_right (h : Commute a b) (m : Int) : Commute a (m * b)
参数：h : Commute a b；m : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
lemma intCast_mul_right (h : Commute a b) (m : ℤ) : Commute a (m * b) := by
  simp [h]
/-
**Commute.intCast_mul_left** 是 Mathlib 中的一个引理，位于命名空间 `Commute`。
形式化陈述：intCast_mul_left (h : Commute a b) (m : Int) : Commute (m * a) b
参数：h : Commute a b；m : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
lemma intCast_mul_left (h : Commute a b) (m : ℤ) : Commute (m * a) b := by
  simp [h]
/-
**Commute.intCast_mul_intCast_mul** 是 Mathlib 中的一个引理，位于命名空间 `Commute`。
形式化陈述：intCast_mul_intCast_mul (h : Commute a b) (m n : Int) : Commute (m * a) (n
 * b)
参数：h : Commute a b；m n : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SemiconjBy.intCast_mul_intCast_mul`：intCast_mul_intCast_mul (h : Semicon
jBy a x y) (m n : Int) : SemiconjBy (m * a) (n * x) (n * y)
-/
lemma intCast_mul_intCast_mul (h : Commute a b) (m n : ℤ) : Commute (m * a) (n * b) :=
  SemiconjBy.intCast_mul_intCast_mul h m n

variable (a) (m n : ℤ)
/-
**Commute.self_intCast_mul** 是 Mathlib 中的一个引理，位于命名空间 `Commute`。
形式化陈述：self_intCast_mul : Commute a (n * a : α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Commute.intCast_mul_right`：intCast_mul_right (h : Commute a b) (m : Int)
 : Commute a (m * b)
· 使用定理 `Commute.refl`：∀ {S : Type u_3} [inst : Mul S] (a : S), Commute a a
-/
lemma self_intCast_mul : Commute a (n * a : α) := (Commute.refl a).intCast_mul_right n
/-
**Commute.intCast_mul_self** 是 Mathlib 中的一个引理，位于命名空间 `Commute`。
形式化陈述：intCast_mul_self : Commute ((n : α) * a) a
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Commute.intCast_mul_left`：intCast_mul_left (h : Commute a b) (m : Int) :
 Commute (m * a) b
· 使用定理 `Commute.refl`：∀ {S : Type u_3} [inst : Mul S] (a : S), Commute a a
-/
lemma intCast_mul_self : Commute ((n : α) * a) a := (Commute.refl a).intCast_mul_left n
/-
**Commute.self_intCast_mul_intCast_mul** 是 Mathlib 中的一个引理，位于命名空间 `Commute`。
形式化陈述：self_intCast_mul_intCast_mul : Commute (m * a : α) (n * a : α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Commute.intCast_mul_intCast_mul`：intCast_mul_intCast_mul (h : Commute a 
b) (m n : Int) : Commute (m * a) (n * b)
· 使用定理 `Commute.refl`：∀ {S : Type u_3} [inst : Mul S] (a : S), Commute a a
-/
lemma self_intCast_mul_intCast_mul : Commute (m * a : α) (n * a : α) :=
  (Commute.refl a).intCast_mul_intCast_mul m n

end Ring
end Commute

namespace AddMonoidHom

variable {A : Type*}

/-- Two additive monoid homomorphisms `f`, `g` from `ℤ` to an additive monoid are equal
if `f 1 = g 1`. -/
@[ext high]
/-
**AddMonoidHom.ext_int** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoidHom`。
形式化陈述：ext_int [AddMonoid A] {f g : Int ->+ A} (h1 : f 1 = g 1) : f = g
参数：h1 : f 1 = g 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用引理 `ext_nat'`：ext_nat' [AddZeroClass A] [AddMonoidHomClass F Nat A] (f g : F
) (h : f 1 = g 1) : f = g
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `DFunLike.ext_iff`：ext_iff {f g : F} : f = g ↔ forall x, f x = g x
· 使用定理 `AddMonoidHom.ext`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZero M] [in
st_1 : AddZero N] ⦃f g : M →+ N⦄, (∀ (x : M), f x = g x) → f = g
· 使用定理 `eq_on_neg`：∀ {F : Type u_1} {G : Type u_2} {M : Type u_3} [inst : AddGro
up G] [inst_1 : AddMonoid M] [inst_2 : FunLike F G M]   [AddMonoidHomClass F G …

--- 原说明 ---
Two additive monoid homomorphisms `f`, `g` from `ℤ` to an additive monoid are eq
ual
if `f 1 = g 1`.
-/
theorem ext_int [AddMonoid A] {f g : ℤ →+ A} (h1 : f 1 = g 1) : f = g :=
  have : f.comp (Int.ofNatHom : ℕ →+ ℤ) = g.comp (Int.ofNatHom : ℕ →+ ℤ) := ext_nat' _ _ h1
  have this' : ∀ n : ℕ, f n = g n := DFunLike.ext_iff.1 this
  ext fun n => match n with
  | (n : ℕ) => this' n
  | .negSucc n => eq_on_neg _ _ (this' <| n + 1)

variable [AddGroupWithOne A]
/-
**AddMonoidHom.eq_intCastAddHom** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoidHom`。
形式化陈述：eq_intCastAddHom (f : Int ->+ A) (h1 : f 1 = 1) : f = Int.castAddHom A
参数：f : Int ->+ A；h1 : f 1 = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.ext_int`：ext_int [AddMonoid A] {f g : Int ->+ A} (h1 : f 1 
= g 1) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem eq_intCastAddHom (f : ℤ →+ A) (h1 : f 1 = 1) : f = Int.castAddHom A :=
  ext_int <| by simp [h1]

end AddMonoidHom

namespace AddEquiv
variable {A : Type*}

/-- Two additive monoid isomorphisms `f`, `g` from `ℤ` to an additive monoid are equal
if `f 1 = g 1`. -/
@[ext high]
/-
**AddEquiv.ext_int** 是 Mathlib 中的一个定理，位于命名空间 `AddEquiv`。
形式化陈述：ext_int [AddMonoid A] {f g : Int ≃+ A} (h1 : f 1 = g 1) : f = g
参数：h1 : f 1 = g 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddEquiv.toAddMonoidHom_injective`：∀ {M : Type u_4} {N : Type u_5} [inst
 : AddZeroClass M] [inst_1 : AddZeroClass N],   Function.Injective AddEquiv.toAd
dMonoidHom
· 使用定理 `AddMonoidHom.ext_int`：ext_int [AddMonoid A] {f g : Int ->+ A} (h1 : f 1 
= g 1) : f = g

--- 原说明 ---
Two additive monoid isomorphisms `f`, `g` from `ℤ` to an additive monoid are equ
al
if `f 1 = g 1`.
-/
theorem ext_int [AddMonoid A] {f g : ℤ ≃+ A} (h1 : f 1 = g 1) : f = g :=
  toAddMonoidHom_injective <| AddMonoidHom.ext_int h1

end AddEquiv

/-
**eq_intCast'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_intCast' [AddGroupWithOne α] [FunLike F Int α] [AddMonoidHomClass F Int
 α] (f : F) (h₁ : f 1 = 1) : forall n : Int, f n = n
参数：f : F；h₁ : f 1 = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `DFunLike.ext_iff`：ext_iff {f g : F} : f = g ↔ forall x, f x = g x
· 使用定理 `AddMonoidHom.eq_intCastAddHom`：eq_intCastAddHom (f : Int ->+ A) (h1 : f 
1 = 1) : f = Int.castAddHom A
-/
theorem eq_intCast' [AddGroupWithOne α] [FunLike F ℤ α] [AddMonoidHomClass F ℤ α]
    (f : F) (h₁ : f 1 = 1) :
    ∀ n : ℤ, f n = n :=
  DFunLike.ext_iff.1 <| (f : ℤ →+ α).eq_intCastAddHom h₁

/-- This version is primed so that the `RingHomClass` versions aren't. -/
/-
**map_intCast'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_intCast' [AddGroupWithOne α] [AddGroupWithOne β] [FunLike F α β] [AddM
onoidHomClass F α β] (f : F) (h₁ : f 1 = 1) : forall n : Int, f n = n
参数：f : F；h₁ : f 1 = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_intCast'`：eq_intCast' [AddGroupWithOne α] [FunLike F Int α] [AddMonoi
dHomClass F Int α] (f : F) (h₁ : f 1 = 1) : forall n : Int, f n = n
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1

--- 原说明 ---
This version is primed so that the `RingHomClass` versions aren't.
-/
theorem map_intCast' [AddGroupWithOne α] [AddGroupWithOne β] [FunLike F α β]
    [AddMonoidHomClass F α β] (f : F) (h₁ : f 1 = 1) : ∀ n : ℤ, f n = n :=
  eq_intCast' ((f : α →+ β).comp <| Int.castAddHom _) (by simpa)

@[simp]
/-
**Int.castAddHom_int** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Int.castAddHom_int : Int.castAddHom Int = AddMonoidHom.id Int
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AddMonoidHom.eq_intCastAddHom`：eq_intCastAddHom (f : Int ->+ A) (h1 : f 
1 = 1) : f = Int.castAddHom A
-/
theorem Int.castAddHom_int : Int.castAddHom ℤ = AddMonoidHom.id ℤ :=
  ((AddMonoidHom.id ℤ).eq_intCastAddHom rfl).symm

namespace MonoidHom

variable {M : Type*} [Monoid M]

@[ext]
/-
**MonoidHom.ext_mint** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：ext_mint {f g : Multiplicative Int ->* M} (h1 : f (ofAdd 1) = g (ofAdd 1))
 : f = g
参数：h1 : f (ofAdd 1) = g (ofAdd 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `AddMonoidHom.ext_int`：ext_int [AddMonoid A] {f g : Int ->+ A} (h1 : f 1 
= g 1) : f = g
-/
theorem ext_mint {f g : Multiplicative ℤ →* M} (h1 : f (ofAdd 1) = g (ofAdd 1)) : f = g :=
  MonoidHom.toAdditiveRight.injective <| AddMonoidHom.ext_int <| Additive.toMul.injective h1

/-- If two `MonoidHom`s agree on `-1` and the naturals then they are equal. -/
@[ext]
/-
**MonoidHom.ext_int** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：ext_int {f g : Int ->* M} (h_neg_one : f (-1) = g (-1)) (h_nat : f.comp In
t.ofNatHom.toMonoidHom = g.comp Int.ofNatHom.toMonoidHom) : f = g
参数：h_neg_one : f (-1) = g (-1)；h_nat : f.comp Int.ofNatHom.toMonoidHom = g.comp 
Int.ofNatHom.toMonoidHom。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.ext`：MonoidHom.ext [MulOne M] [MulOne N] ⦃f g : M ->* N⦄ (h : 
forall x, f x = g x) : f = g
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.negSucc_eq`：∀ (n : ℕ), Int.negSucc n = -(↑n + 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_one_mul`：neg_one_mul (a : α) : -1 * a = -a
· 使用定理 `MonoidHom.map_mul`：∀ {M : Type u_4} {N : Type u_5} [inst : MulOne M] [in
st_1 : MulOne N] (f : M →* N) (a b : M), f (a * b) = f a * f b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1

--- 原说明 ---
If two `MonoidHom`s agree on `-1` and the naturals then they are equal.
-/
theorem ext_int {f g : ℤ →* M} (h_neg_one : f (-1) = g (-1))
    (h_nat : f.comp Int.ofNatHom.toMonoidHom = g.comp Int.ofNatHom.toMonoidHom) : f = g := by
  ext (x | x)
  · exact (DFunLike.congr_fun h_nat x :)
  · rw [Int.negSucc_eq, ← neg_one_mul, f.map_mul, g.map_mul]
    congr 1
    exact mod_cast (DFunLike.congr_fun h_nat (x + 1) :)

end MonoidHom

namespace MonoidWithZeroHom

variable {M : Type*} [MonoidWithZero M]

/-- If two `MonoidWithZeroHom`s agree on `-1` and the naturals then they are equal. -/
@[ext]
/-
**MonoidWithZeroHom.ext_int** 是 Mathlib 中的一个定理，位于命名空间 `MonoidWithZeroHom`。
形式化陈述：ext_int {f g : Int ->*₀ M} (h_neg_one : f (-1) = g (-1)) (h_nat : f.comp I
nt.ofNatHom.toMonoidWithZeroHom = g.comp Int.ofNatHom.toMonoidWithZeroHom) : f =
 g
参数：h_neg_one : f (-1) = g (-1)；h_nat : f.comp Int.ofNatHom.toMonoidWithZeroHom =
 g.comp Int.ofNatHom.toMonoidWithZeroHom。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MonoidWithZeroHom.toMonoidHom_injective`：toMonoidHom_injective : Injecti
ve (toMonoidHom : (α ->*₀ β) -> α ->* β)
· 使用定理 `MonoidHom.ext_int`：ext_int {f g : Int ->* M} (h_neg_one : f (-1) = g (-1
)) (h_nat : f.comp Int.ofNatHom.toMonoidHom = g.comp Int.ofNatHom.toMonoidHom) :
 f = g
· 使用定理 `MonoidHom.ext`：MonoidHom.ext [MulOne M] [MulOne N] ⦃f g : M ->* N⦄ (h : 
forall x, f x = g x) : f = g
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x

--- 原说明 ---
If two `MonoidWithZeroHom`s agree on `-1` and the naturals then they are equal.
-/
theorem ext_int {f g : ℤ →*₀ M} (h_neg_one : f (-1) = g (-1))
    (h_nat : f.comp Int.ofNatHom.toMonoidWithZeroHom = g.comp Int.ofNatHom.toMonoidWithZeroHom) :
    f = g :=
  toMonoidHom_injective <| MonoidHom.ext_int h_neg_one <|
    MonoidHom.ext (DFunLike.congr_fun h_nat :)

end MonoidWithZeroHom

/-- If two `MonoidWithZeroHom`s agree on `-1` and the _positive_ naturals then they are equal. -/
/-
**ext_int'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ext_int' [MonoidWithZero α] [FunLike F Int α] [MonoidWithZeroHomClass F In
t α] {f g : F} (h_neg_one : f (-1) = g (-1)) (h_pos : forall n : Nat, 0 < n -> f
 n = g n) : f = g
参数：h_neg_one : f (-1) = g (-1)；h_pos : forall n : Nat, 0 < n -> f n = g n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用定理 `MonoidWithZeroHom.ext_int`：ext_int {f g : Int ->*₀ M} (h_neg_one : f (-1
) = g (-1)) (h_nat : f.comp Int.ofNatHom.toMonoidWithZeroHom = g.comp Int.ofNatH
om.toMonoidWith…
· 使用定理 `MonoidWithZeroHom.ext_nat`：MonoidWithZeroHom.ext_nat {f g : Nat ->*₀ A} 
: (forall {n : Nat}, 0 < n -> f n = g n) -> f = g

--- 原说明 ---
If two `MonoidWithZeroHom`s agree on `-1` and the _positive_ naturals then they 
are equal.
-/
theorem ext_int' [MonoidWithZero α] [FunLike F ℤ α] [MonoidWithZeroHomClass F ℤ α] {f g : F}
    (h_neg_one : f (-1) = g (-1)) (h_pos : ∀ n : ℕ, 0 < n → f n = g n) : f = g :=
  (DFunLike.ext _ _) fun n =>
    haveI :=
      DFunLike.congr_fun
        (@MonoidWithZeroHom.ext_int _ _ (.ofClass f) (.ofClass g) h_neg_one <|
          MonoidWithZeroHom.ext_nat (h_pos _))
        n
    this

section Group
variable (α) [Group α] (β) [AddGroup β]

/-- Additive homomorphisms from `ℤ` are defined by the image of `1`. -/
/-
**zmultiplesHom** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：zmultiplesHom : β ≃ (Int ->+ β) where toFun x
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `add_zsmul`：∀ {G : Type u_3} [inst : AddGroup G] (a : G) (m n : ℤ), (m + 
n) • a = m • a + n • a

--- 原说明 ---
Additive homomorphisms from `ℤ` are defined by the image of `1`.
-/
def zmultiplesHom : β ≃ (ℤ →+ β) where
  toFun x :=
  { toFun := fun n => n • x
    map_zero' := zero_zsmul x
    map_add' := fun _ _ => add_zsmul _ _ _ }
  invFun f := f 1
  left_inv := one_zsmul
  right_inv f := AddMonoidHom.ext_int <| one_zsmul (f 1)

/-- Monoid homomorphisms from `Multiplicative ℤ` are defined by the image
of `Multiplicative.ofAdd 1`. -/
/-
**zpowersHom** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：zpowersHom : α ≃ (Multiplicative Int ->* α)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
Monoid homomorphisms from `Multiplicative ℤ` are defined by the image
of `Multiplicative.ofAdd 1`.
-/
def zpowersHom : α ≃ (Multiplicative ℤ →* α) :=
  ofMul.trans <| (zmultiplesHom _).trans <| AddMonoidHom.toMultiplicativeLeft
/-
**zmultiplesHom_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ (β : Type u_4) [inst : AddGroup β] (x : β) (n : ℤ), ((zmultiplesHom β) x
) n = n • x
参数：β : Type u_4；x : β；n : ℤ；(zmultiplesHom β) x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma zmultiplesHom_apply (x : β) (n : ℤ) : zmultiplesHom β x n = n • x := rfl
/-
**zmultiplesHom_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ (β : Type u_4) [inst : AddGroup β] (f : ℤ →+ β), (zmultiplesHom β).symm 
f = f 1
参数：β : Type u_4；f : ℤ →+ β；zmultiplesHom β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
@[simp] lemma zmultiplesHom_symm_apply (f : ℤ →+ β) : (zmultiplesHom β).symm f = f 1 := rfl
/-
**zpowersHom_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ (α : Type u_3) [inst : Group α] (x : α) (n : Multiplicative ℤ), ((zpower
sHom α) x) n = x ^ Multiplicative.toAdd n
参数：α : Type u_3；x : α；n : Multiplicative ℤ；(zpowersHom α) x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma zpowersHom_apply (x : α) (n : Multiplicative ℤ) :
    zpowersHom α x n = x ^ n.toAdd := rfl
/-
**zpowersHom_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ (α : Type u_3) [inst : Group α] (f : Multiplicative ℤ →* α), (zpowersHom
 α).symm f = f (Multiplicative.ofAdd 1)
参数：α : Type u_3；f : Multiplicative ℤ →* α；zpowersHom α；Multiplicative.ofAdd 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
@[simp] lemma zpowersHom_symm_apply (f : Multiplicative ℤ →* α) :
    (zpowersHom α).symm f = f (ofAdd 1) := rfl
/-
**MonoidHom.apply_mint** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MonoidHom.apply_mint (f : Multiplicative Int ->* α) (n : Multiplicative In
t) : f n = f (ofAdd 1) ^ n.toAdd
参数：f : Multiplicative Int ->* α；n : Multiplicative Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zpowersHom_symm_apply`：∀ (α : Type u_3) [inst : Group α] (f : Multiplica
tive ℤ →* α), (zpowersHom α).symm f = f (Multiplicative.ofAdd 1)
· 使用定理 `zpowersHom_apply`：∀ (α : Type u_3) [inst : Group α] (x : α) (n : Multipl
icative ℤ), ((zpowersHom α) x) n = x ^ Multiplicative.toAdd n
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
-/
lemma MonoidHom.apply_mint (f : Multiplicative ℤ →* α) (n : Multiplicative ℤ) :
    f n = f (ofAdd 1) ^ n.toAdd := by
  rw [← zpowersHom_symm_apply, ← zpowersHom_apply, Equiv.apply_symm_apply]
/-
**AddMonoidHom.apply_int** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AddMonoidHom.apply_int (f : Int ->+ β) (n : Int) : f n = n • f 1
参数：f : Int ->+ β；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zmultiplesHom_symm_apply`：∀ (β : Type u_4) [inst : AddGroup β] (f : ℤ →+
 β), (zmultiplesHom β).symm f = f 1
· 使用定理 `zmultiplesHom_apply`：∀ (β : Type u_4) [inst : AddGroup β] (x : β) (n : ℤ
), ((zmultiplesHom β) x) n = n • x
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
-/
lemma AddMonoidHom.apply_int (f : ℤ →+ β) (n : ℤ) : f n = n • f 1 := by
  rw [← zmultiplesHom_symm_apply, ← zmultiplesHom_apply, Equiv.apply_symm_apply]

end Group

section CommGroup
variable (α) [CommGroup α] (β) [AddCommGroup β]

/-- If `α` is commutative, `zmultiplesHom` is an additive equivalence. -/
/-
**zmultiplesAddHom** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：zmultiplesAddHom : β ≃+ (Int ->+ β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `α` is commutative, `zmultiplesHom` is an additive equivalence.
-/
def zmultiplesAddHom : β ≃+ (ℤ →+ β) :=
  { zmultiplesHom β with map_add' := fun a b => AddMonoidHom.ext fun n => by simp [zsmul_add] }

/-- If `α` is commutative, `zpowersHom` is a multiplicative equivalence. -/
/-
**zpowersMulHom** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：zpowersMulHom : α ≃* (Multiplicative Int ->* α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `α` is commutative, `zpowersHom` is a multiplicative equivalence.
-/
def zpowersMulHom : α ≃* (Multiplicative ℤ →* α) :=
  { zpowersHom α with map_mul' := fun a b => MonoidHom.ext fun n => by simp [mul_zpow] }

variable {α}

@[simp]
/-
**zpowersMulHom_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：zpowersMulHom_apply (x : α) (n : Multiplicative Int) : zpowersMulHom α x n
 = x ^ n.toAdd
参数：x : α；n : Multiplicative Int。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma zpowersMulHom_apply (x : α) (n : Multiplicative ℤ) : zpowersMulHom α x n = x ^ n.toAdd := rfl

@[simp]
/-
**zpowersMulHom_symm_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：zpowersMulHom_symm_apply (f : Multiplicative Int ->* α) : (zpowersMulHom α
).symm f = f (ofAdd 1)
参数：f : Multiplicative Int ->* α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma zpowersMulHom_symm_apply (f : Multiplicative ℤ →* α) :
    (zpowersMulHom α).symm f = f (ofAdd 1) := rfl
/-
**zmultiplesAddHom_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ (β : Type u_4) [inst : AddCommGroup β] (x : β) (n : ℤ), ((zmultiplesAddH
om β) x) n = n • x
参数：β : Type u_4；x : β；n : ℤ；(zmultiplesAddHom β) x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma zmultiplesAddHom_apply (x : β) (n : ℤ) : zmultiplesAddHom β x n = n • x := rfl
/-
**zmultiplesAddHom_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ (β : Type u_4) [inst : AddCommGroup β] (f : ℤ →+ β), (zmultiplesAddHom β
).symm f = f 1
参数：β : Type u_4；f : ℤ →+ β；zmultiplesAddHom β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma zmultiplesAddHom_symm_apply (f : ℤ →+ β) : (zmultiplesAddHom β).symm f = f 1 := rfl

end CommGroup

section NonAssocRing

variable [NonAssocRing α] [NonAssocRing β]

@[simp]
/-
**eq_intCast** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_intCast [FunLike F Int α] [RingHomClass F Int α] (f : F) (n : Int) : f 
n = n
参数：f : F；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_intCast'`：eq_intCast' [AddGroupWithOne α] [FunLike F Int α] [AddMonoi
dHomClass F Int α] (f : F) (h₁ : f 1 = 1) : forall n : Int, f n = n
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
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
-/
theorem eq_intCast [FunLike F ℤ α] [RingHomClass F ℤ α] (f : F) (n : ℤ) : f n = n :=
  eq_intCast' f (map_one _) n

@[simp]
/-
**map_intCast** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_intCast [FunLike F α β] [RingHomClass F α β] (f : F) (n : Int) : f n =
 n
参数：f : F；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_intCast`：eq_intCast [FunLike F Int α] [RingHomClass F Int α] (f : F) 
(n : Int) : f n = n
-/
theorem map_intCast [FunLike F α β] [RingHomClass F α β] (f : F) (n : ℤ) : f n = n :=
  eq_intCast ((f : α →+* β).comp (Int.castRingHom α)) n

namespace RingHom

/-
**RingHom.eq_intCast'** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：eq_intCast' (f : Int ->+* α) : f = Int.castRingHom α
参数：f : Int ->+* α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `eq_intCast`：eq_intCast [FunLike F Int α] [RingHomClass F Int α] (f : F) 
(n : Int) : f n = n
-/
theorem eq_intCast' (f : ℤ →+* α) : f = Int.castRingHom α :=
  RingHom.ext <| eq_intCast f
/-
**RingHom.ext_int** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：ext_int {R : Type*} [NonAssocSemiring R] (f g : Int ->+* R) : f = g
参数：f g : Int ->+* R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.coe_addMonoidHom_injective`：coe_addMonoidHom_injective : Injecti
ve (fun f : α ->+* β => (f : α ->+ β))
· 使用定理 `AddMonoidHom.ext_int`：ext_int [AddMonoid A] {f g : Int ->+ A} (h1 : f 1 
= g 1) : f = g
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `RingHom.map_one`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring α
} {x_1 : NonAssocSemiring β} (f : α →+* β), f 1 = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem ext_int {R : Type*} [NonAssocSemiring R] (f g : ℤ →+* R) : f = g :=
  coe_addMonoidHom_injective <| AddMonoidHom.ext_int <| f.map_one.trans g.map_one.symm
/-
**RingHom.Int.subsingleton_ringHom** 是 Mathlib 中的一个定理，位于命名空间 `RingHom.Int`。
形式化陈述：∀ {R : Type u_5} [inst : NonAssocSemiring R], Subsingleton (ℤ →+* R)
参数：ℤ →+* R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext_int`：ext_int {R : Type*} [NonAssocSemiring R] (f g : Int ->+
* R) : f = g
-/
instance Int.subsingleton_ringHom {R : Type*} [NonAssocSemiring R] : Subsingleton (ℤ →+* R) :=
  ⟨RingHom.ext_int⟩

end RingHom

end NonAssocRing

@[simp]
/-
**Int.castRingHom_int** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Int.castRingHom_int : Int.castRingHom Int = RingHom.id Int
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHom.eq_intCast'`：eq_intCast' (f : Int ->+* α) : f = Int.castRingHom 
α
-/
theorem Int.castRingHom_int : Int.castRingHom ℤ = RingHom.id ℤ :=
  (RingHom.id ℤ).eq_intCast'.symm
