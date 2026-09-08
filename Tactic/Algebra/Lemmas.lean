/-
Copyright (c) 2025 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arend Mellendijk
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Tactic.Ring.RingNF

/-! # Lemmas for the `algebra` tactic.
-/

@[expose] public section

open Mathlib.Meta.NormNum

namespace Mathlib.Tactic.Algebra

section ring

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/- evalCast -/
/-
**Mathlib.Tactic.Algebra.isInt_negOfNat_eq** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Ta
ctic.Algebra`。
形式化陈述：isInt_negOfNat_eq {a : A} {lit : Nat} (h : IsInt a (Int.negOfNat lit)) : a
 = algebraMap R A (Int.rawCast (Int.negOfNat lit) + 0 : R) + 0
参数：h : IsInt a (Int.negOfNat lit)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Meta.NormNum.IsInt.out`：∀ {α : Type u} [inst : Ring α] {a : α} {
n : ℤ}, Mathlib.Meta.NormNum.IsInt a n → a = ↑n
· 使用定理 `Int.cast_negOfNat`：cast_negOfNat (n : Nat) : ((negOfNat n : Int) : R) = 
-n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `map_natCast`：map_natCast [FunLike F R S] [RingHomClass F R S] (f : F) : 
forall n : Nat, f (n : R) = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
evalCast
-/
theorem isInt_negOfNat_eq {a : A} {lit : ℕ} (h : IsInt a (Int.negOfNat lit)) :
    a = algebraMap R A (Int.rawCast (Int.negOfNat lit) + 0 : R) + 0 := by
  simp [h.out]

end ring

section semifield

variable {R A : Type*} [Semifield R] [Semifield A] [Algebra R A]

/- evalCast -/
/-
**Mathlib.Tactic.Algebra.isNNRat_eq_rawCast** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.T
actic.Algebra`。
形式化陈述：isNNRat_eq_rawCast {a : A} {n d : Nat} (h : IsNNRat a n d) : a = algebraMa
p R A (NNRat.rawCast n d + 0 : R) + 0
参数：h : IsNNRat a n d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.cast_nnrat`：∀ {n d : ℕ} {R : Type u_2} [inst : Divis
ionSemiring R] {a : R},   Mathlib.Meta.NormNum.IsNNRat a n d → a = NNRat.rawCast
 n d + 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_div₀`：map_div₀ : f (a / b) = f a / f b
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `map_natCast`：map_natCast [FunLike F R S] [RingHomClass F R S] (f : F) : 
forall n : Nat, f (n : R) = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
evalCast
-/
theorem isNNRat_eq_rawCast {a : A} {n d : ℕ} (h : IsNNRat a n d) :
    a = algebraMap R A (NNRat.rawCast n d + 0 : R) + 0 := by
  simp [Mathlib.Tactic.Ring.cast_nnrat h]

end semifield

section field

variable {R A : Type*} [Field R] [Field A] [Algebra R A]

/- evalCast -/
/-
**Mathlib.Tactic.Algebra.isRat_eq_rawCast** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tac
tic.Algebra`。
形式化陈述：isRat_eq_rawCast {a : A} {n d : Nat} (h : IsRat a (.negOfNat n) d) : a = a
lgebraMap R A (Rat.rawCast (.negOfNat n) d + 0 : R) + 0
参数：h : IsRat a (.negOfNat n) d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.cast_rat`：∀ {n : ℤ} {d : ℕ} {R : Type u_2} [inst : D
ivisionRing R] {a : R},   Mathlib.Meta.NormNum.IsRat a n d → a = Rat.rawCast n d
 + 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Int.cast_negOfNat`：cast_negOfNat (n : Nat) : ((negOfNat n : Int) : R) = 
-n
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `map_div₀`：map_div₀ : f (a / b) = f a / f b
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `map_natCast`：map_natCast [FunLike F R S] [RingHomClass F R S] (f : F) : 
forall n : Nat, f (n : R) = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
evalCast
-/
theorem isRat_eq_rawCast {a : A} {n d : ℕ} (h : IsRat a (.negOfNat n) d) :
    a = algebraMap R A (Rat.rawCast (.negOfNat n) d + 0 : R) + 0 := by
  simp [Mathlib.Tactic.Ring.cast_rat h]

end field

variable {R A : Type*} [sR : CommSemiring R] [sA : CommSemiring A] [sAlg : Algebra R A]

/- evalCast -/
/-
**Mathlib.Tactic.Algebra.isNat_zero_eq** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic
.Algebra`。
形式化陈述：isNat_zero_eq {a : A} (h : IsNat a 0) : a = 0
参数：h : IsNat a 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Meta.NormNum.IsNat.out`：∀ {α : Type u} [inst : AddMonoidWithOne 
α] {a : α} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = ↑n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
evalCast
-/
theorem isNat_zero_eq {a : A} (h : IsNat a 0) : a = 0 := by
  have := h.out
  simp [this]

/- evalCast -/
/-
**Mathlib.Tactic.Algebra.isNat_eq_rawCast** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tac
tic.Algebra`。
形式化陈述：isNat_eq_rawCast {a : A} {lit : Nat} (h : IsNat a lit) : a = algebraMap R 
A (lit + 0 : R) + 0
参数：h : IsNat a lit。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Meta.NormNum.IsNat.out`：∀ {α : Type u} [inst : AddMonoidWithOne 
α] {a : α} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = ↑n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `map_natCast`：map_natCast [FunLike F R S] [RingHomClass F R S] (f : F) : 
forall n : Nat, f (n : R) = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
evalCast
-/
theorem isNat_eq_rawCast {a : A} {lit : ℕ} (h : IsNat a lit) :
    a = algebraMap R A (lit + 0 : R) + 0 := by
  simp [h.out]

section cleanup

variable {n d : ℕ}

section cleanupSMul

/-
**Mathlib.Tactic.Algebra.add_assoc_rev** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic
.Algebra`。
形式化陈述：add_assoc_rev (a b c : R) : a + (b + c) = a + b + c
参数：a b c : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
-/
theorem add_assoc_rev (a b c : R) : a + (b + c) = a + b + c := (add_assoc ..).symm
/-
**Mathlib.Tactic.Algebra.mul_assoc_rev** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic
.Algebra`。
形式化陈述：mul_assoc_rev (a b c : R) : a * (b * c) = a * b * c
参数：a b c : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
-/
theorem mul_assoc_rev (a b c : R) : a * (b * c) = a * b * c := (mul_assoc ..).symm
/-
**Mathlib.Tactic.Algebra.mul_neg** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic.Algeb
ra`。
形式化陈述：mul_neg {R} [Ring R] (a b : R) : a * -b = -(a * b)
参数：a b : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mul_neg {R} [Ring R] (a b : R) : a * -b = -(a * b) := by simp
/-
**Mathlib.Tactic.Algebra.add_neg** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic.Algeb
ra`。
形式化陈述：add_neg {R} [Ring R] (a b : R) : a + -b = a - b
参数：a b : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
-/
theorem add_neg {R} [Ring R] (a b : R) : a + -b = a - b := (sub_eq_add_neg ..).symm
/-
**Mathlib.Tactic.Algebra.nat_rawCast_0** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic
.Algebra`。
形式化陈述：nat_rawCast_0 : (Nat.rawCast 0 : R) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem nat_rawCast_0 : (Nat.rawCast 0 : R) = 0 := by simp
/-
**Mathlib.Tactic.Algebra.nat_rawCast_1** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic
.Algebra`。
形式化陈述：nat_rawCast_1 : (Nat.rawCast 1 : R) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem nat_rawCast_1 : (Nat.rawCast 1 : R) = 1 := by simp
/-
**Mathlib.Tactic.Algebra.nat_rawCast_2** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic
.Algebra`。
形式化陈述：nat_rawCast_2 [Nat.AtLeastTwo n] : (Nat.rawCast n : R) = OfNat.ofNat n
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem nat_rawCast_2 [Nat.AtLeastTwo n] : (Nat.rawCast n : R) = OfNat.ofNat n := rfl
/-
**Mathlib.Tactic.Algebra.int_rawCast_neg** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tact
ic.Algebra`。
形式化陈述：int_rawCast_neg {R} [Ring R] : (Int.rawCast (.negOfNat n) : R) = -Nat.rawC
ast n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.cast_negOfNat`：cast_negOfNat (n : Nat) : ((negOfNat n : Int) : R) = 
-n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem int_rawCast_neg {R} [Ring R] : (Int.rawCast (.negOfNat n) : R) = -Nat.rawCast n := by simp
/-
**Mathlib.Tactic.Algebra.nnrat_rawCast** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic
.Algebra`。
形式化陈述：nnrat_rawCast {R} [DivisionSemiring R] : (NNRat.rawCast n d : R) = Nat.raw
Cast n / Nat.rawCast d
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem nnrat_rawCast {R} [DivisionSemiring R] :
    (NNRat.rawCast n d : R) = Nat.rawCast n / Nat.rawCast d := by simp
/-
**Mathlib.Tactic.Algebra.rat_rawCast_neg** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tact
ic.Algebra`。
形式化陈述：rat_rawCast_neg {R} [DivisionRing R] : (Rat.rawCast (.negOfNat n) d : R) =
 Int.rawCast (.negOfNat n) / Nat.rawCast d
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Int.cast_negOfNat`：cast_negOfNat (n : Nat) : ((negOfNat n : Int) : R) = 
-n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem rat_rawCast_neg {R} [DivisionRing R] :
    (Rat.rawCast (.negOfNat n) d : R) = Int.rawCast (.negOfNat n) / Nat.rawCast d := by simp

end cleanupSMul
section cleanupConsts

/-
**Mathlib.Tactic.Algebra.ofNat_smul** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic.Al
gebra`。
形式化陈述：ofNat_smul {R A} [CommSemiring R] [CommSemiring A] [Algebra R A] [n.AtLeas
tTwo] {a : A} : (ofNat(n) : R) • a = ofNat(n) * a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Nat.cast_smul_eq_nsmul`：Nat.cast_smul_eq_nsmul (n : Nat) (b : M) : (n : 
R) • b = n • b
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ofNat_smul {R A} [CommSemiring R] [CommSemiring A] [Algebra R A]
    [n.AtLeastTwo] {a : A} :
    (ofNat(n) : R) • a = ofNat(n) * a := by
  simp_rw [← nat_rawCast_2]
  simp [Nat.cast_smul_eq_nsmul]
/-
**Mathlib.Tactic.Algebra.neg_ofNat_smul** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tacti
c.Algebra`。
形式化陈述：neg_ofNat_smul {R A} [CommRing R] [CommRing A] [Algebra R A] {a : A} [n.At
LeastTwo] : (- ofNat(n) : R) • a = - (ofNat(n)) * a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `Mathlib.Tactic.Algebra.ofNat_smul`：ofNat_smul {R A} [CommSemiring R] [Co
mmSemiring A] [Algebra R A] [n.AtLeastTwo] {a : A} : (ofNat(n) : R) • a = ofNat(
n) * a
-/
theorem neg_ofNat_smul {R A} [CommRing R] [CommRing A] [Algebra R A] {a : A} [n.AtLeastTwo] :
    (- ofNat(n) : R) • a = - (ofNat(n)) * a := by
  simpa [← nat_rawCast_2] using! ofNat_smul
/-
**Mathlib.Tactic.Algebra.neg_1_smul** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic.Al
gebra`。
形式化陈述：neg_1_smul {R A} [CommRing R] [CommRing A] [Algebra R A] {a : A} : (-1 : R
) • a = - a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem neg_1_smul {R A} [CommRing R] [CommRing A] [Algebra R A] {a : A} :
    (-1 : R) • a = - a := by
  simp
/-
**Mathlib.Tactic.Algebra.nnRat_ofNat_smul_1** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.T
actic.Algebra`。
形式化陈述：nnRat_ofNat_smul_1 {R A} [Semifield R] [Semifield A] [Algebra R A] {a : A}
 [d.AtLeastTwo] : (1 / ofNat(d) : R) • a = (1 / ofNat(d)) * a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `map_inv₀`：map_inv₀ : f a⁻¹ = (f a)⁻¹
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `map_natCast`：map_natCast [FunLike F R S] [RingHomClass F R S] (f : F) : 
forall n : Nat, f (n : R) = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem nnRat_ofNat_smul_1 {R A} [Semifield R] [Semifield A] [Algebra R A] {a : A}
    [d.AtLeastTwo] :
    (1 / ofNat(d) : R) • a = (1 / ofNat(d)) * a := by
  simp [Algebra.smul_def, ← nat_rawCast_2]
/-
**Mathlib.Tactic.Algebra.nnRat_ofNat_smul_2** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.T
actic.Algebra`。
形式化陈述：nnRat_ofNat_smul_2 {R A} [Semifield R] [Semifield A] [Algebra R A] {a : A}
 [n.AtLeastTwo] [d.AtLeastTwo] : (ofNat(n) / ofNat(d) : R) • a = (ofNat(n) / ofN
at(d)) * a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `map_div₀`：map_div₀ : f (a / b) = f a / f b
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_natCast`：map_natCast [FunLike F R S] [RingHomClass F R S] (f : F) : 
forall n : Nat, f (n : R) = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem nnRat_ofNat_smul_2 {R A} [Semifield R] [Semifield A] [Algebra R A] {a : A}
    [n.AtLeastTwo] [d.AtLeastTwo] :
    (ofNat(n) / ofNat(d) : R) • a = (ofNat(n) / ofNat(d)) * a := by
  simp [Algebra.smul_def, ← nat_rawCast_2]
/-
**Mathlib.Tactic.Algebra.rat_ofNat_smul_1** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tac
tic.Algebra`。
形式化陈述：rat_ofNat_smul_1 {R A} [Field R] [Field A] [Algebra R A] {a : A} [d.AtLeas
tTwo] : ((- 1) / ofNat(d) : R) • a = ((- 1) / ofNat(d)) * a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `map_div₀`：map_div₀ : f (a / b) = f a / f b
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
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
· 使用定理 `map_natCast`：map_natCast [FunLike F R S] [RingHomClass F R S] (f : F) : 
forall n : Nat, f (n : R) = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem rat_ofNat_smul_1 {R A} [Field R] [Field A] [Algebra R A] {a : A}
    [d.AtLeastTwo] :
    ((- 1) / ofNat(d) : R) • a = ((- 1) / ofNat(d)) * a := by
  simp [Algebra.smul_def, ← nat_rawCast_2]
/-
**Mathlib.Tactic.Algebra.rat_ofNat_smul_2** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tac
tic.Algebra`。
形式化陈述：rat_ofNat_smul_2 {R A} [Field R] [Field A] [Algebra R A] {a : A} [n.AtLeas
tTwo] [d.AtLeastTwo] : ((- ofNat(n)) / ofNat(d) : R) • a = ((- ofNat(n)) / ofNat
(d)) * a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `map_div₀`：map_div₀ : f (a / b) = f a / f b
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `map_natCast`：map_natCast [FunLike F R S] [RingHomClass F R S] (f : F) : 
forall n : Nat, f (n : R) = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem rat_ofNat_smul_2 {R A} [Field R] [Field A] [Algebra R A] {a : A}
    [n.AtLeastTwo] [d.AtLeastTwo] :
    ((- ofNat(n)) / ofNat(d) : R) • a = ((- ofNat(n)) / ofNat(d)) * a := by
  simp [Algebra.smul_def, ← nat_rawCast_2]

end cleanupConsts

end cleanup

section equateScalars

/- ExProd.equateZero -/
/-
**Mathlib.Tactic.Algebra.smul_one_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tac
tic.Algebra`。
形式化陈述：smul_one_eq_zero {r : R} (h : r = 0) : r • (1 : A) = 0
参数：h : r = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
ExProd.equateZero
-/
theorem smul_one_eq_zero {r : R} (h : r = 0) :
    r • (1 : A) = 0 := by
  simp [h]

/- ExProd.equateZero -/
/-
**Mathlib.Tactic.Algebra.add_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic.A
lgebra`。
形式化陈述：add_eq_zero {a b : A} (ha : a = 0) (hb : b = 0) : a + b = 0
参数：ha : a = 0；hb : b = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
ExProd.equateZero
-/
theorem add_eq_zero {a b : A} (ha : a = 0) (hb : b = 0) :
    a + b = 0 := by
  simp [ha, hb]

/- ExProd.equateScalarsProd -/
/-
**Mathlib.Tactic.Algebra.smul_one_eq_smul_one'** 是 Mathlib 中的一个定理，位于命名空间 `Mathli
b.Tactic.Algebra`。
形式化陈述：smul_one_eq_smul_one' {r s : R} (h : r = s) : r • (1 : A) = s • 1
参数：h : r = s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
ExProd.equateScalarsProd
-/
theorem smul_one_eq_smul_one' {r s : R} (h : r = s) :
    r • (1 : A) = s • 1 := by
  simp [h]

/- equateScalarsSum -/
/-
**Mathlib.Tactic.Algebra.add_eq_of_zero_add** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.T
actic.Algebra`。
形式化陈述：add_eq_of_zero_add {a₁ a₂ b₁ b₂ : A} (ha₁ : a₁ = 0) (ha₂ : a₂ = b₁ + b₂) :
 a₁ + a₂ = b₁ + b₂
参数：ha₁ : a₁ = 0；ha₂ : a₂ = b₁ + b₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
equateScalarsSum
-/
theorem add_eq_of_zero_add {a₁ a₂ b₁ b₂ : A}
    (ha₁ : a₁ = 0) (ha₂ : a₂ = b₁ + b₂) :
    a₁ + a₂ = b₁ + b₂ := by
  subst_vars
  simp

/- equateScalarsSum -/
/-
**Mathlib.Tactic.Algebra.add_eq_of_add_zero** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.T
actic.Algebra`。
形式化陈述：add_eq_of_add_zero {a₁ a₂ b₁ b₂ : A} (hb₁ : b₁ = 0) (ha : a₁ + a₂ = b₂) : 
a₁ + a₂ = b₁ + b₂
参数：hb₁ : b₁ = 0；ha : a₁ + a₂ = b₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
equateScalarsSum
-/
theorem add_eq_of_add_zero {a₁ a₂ b₁ b₂ : A}
    (hb₁ : b₁ = 0) (ha : a₁ + a₂ = b₂) :
    a₁ + a₂ = b₁ + b₂ := by
  subst_vars
  simp

/- equateScalarsSum -/
/-
**Mathlib.Tactic.Algebra.add_eq_of_eq_eq** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tact
ic.Algebra`。
形式化陈述：add_eq_of_eq_eq {a₁ a₂ b₁ b₂ : A} (ha : a₁ = b₁) (hb : a₂ = b₂) : a₁ + a₂ 
= b₁ + b₂
参数：ha : a₁ = b₁；hb : a₂ = b₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
equateScalarsSum
-/
theorem add_eq_of_eq_eq {a₁ a₂ b₁ b₂ : A}
    (ha : a₁ = b₁) (hb : a₂ = b₂) :
    a₁ + a₂ = b₁ + b₂ := by
  subst_vars
  rfl

/- matchScalarsAux -/
omit sA in
/-
**Mathlib.Tactic.Algebra.eq_trans_trans** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tacti
c.Algebra`。
形式化陈述：eq_trans_trans {e₁ e₂ a b : A} (ha : e₁ = a) (hb : e₂ = b) (hab : a = b) :
 e₁ = e₂
参数：ha : e₁ = a；hb : e₂ = b；hab : a = b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem eq_trans_trans {e₁ e₂ a b : A}
    (ha : e₁ = a) (hb : e₂ = b) (hab : a = b) :
    e₁ = e₂ := by
  subst_vars
  rfl

/- ExProd.equateScalarsProd -/
/-
**Mathlib.Tactic.Algebra.mul_eq_mul_of_eq** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tac
tic.Algebra`。
形式化陈述：mul_eq_mul_of_eq {c a b : A} (h : a = b) : c * a = c * b
参数：h : a = b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
ExProd.equateScalarsProd
-/
theorem mul_eq_mul_of_eq {c a b : A}
    (h : a = b) :
    c * a = c * b := by
  simp [h]

end equateScalars

section RingCompute

/- RingCompute.add -/
/-
**Mathlib.Tactic.Algebra.add_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tacti
c.Algebra`。
形式化陈述：add_algebraMap {r s t : R} (h : r + s = t) : algebraMap R A r + algebraMap
 R A s = algebraMap R A t
参数：h : r + s = t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…

--- 原说明 ---
RingCompute.add
-/
theorem add_algebraMap {r s t : R} (h : r + s = t) :
    algebraMap R A r + algebraMap R A s = algebraMap R A t := by
  rw [← map_add, h]

/- RingCompute.add -/
/-
**Mathlib.Tactic.Algebra.add_algebraMap_isNat_zero** 是 Mathlib 中的一个定理，位于命名空间 `Ma
thlib.Tactic.Algebra`。
形式化陈述：add_algebraMap_isNat_zero {r s : R} (h : r + s = 0) : IsNat (algebraMap R 
A r + algebraMap R A s) 0
参数：h : r + s = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
RingCompute.add
-/
theorem add_algebraMap_isNat_zero {r s : R} (h : r + s = 0) :
    IsNat (algebraMap R A r + algebraMap R A s) 0 := by
  rw [← map_add, h, map_zero]
  exact ⟨by simp⟩

/- RingCompute.cast -/
/-
**Mathlib.Tactic.Algebra.cast_zero_smul_eq_zero_mul** 是 Mathlib 中的一个定理，位于命名空间 `M
athlib.Tactic.Algebra`。
形式化陈述：cast_zero_smul_eq_zero_mul {R' : Type*} [HSMul R' A A] {r' : R'} {r : R} (
hr : r = 0) (h_smul : forall (a : A), r • a = r' • a) (a : A) : r' • a = (0 : A)
 * a
参数：hr : r = 0；h_smul : forall (a : A), r • a = r' • a；a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
RingCompute.cast
-/
theorem cast_zero_smul_eq_zero_mul {R' : Type*} [HSMul R' A A] {r' : R'} {r : R}
    (hr : r = 0) (h_smul : ∀ (a : A), r • a = r' • a) (a : A) :
    r' • a = (0 : A) * a := by
  simp [← h_smul, hr]

/- RingCompute.cast -/
/-
**Mathlib.Tactic.Algebra.cast_smul_eq_mul** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tac
tic.Algebra`。
形式化陈述：cast_smul_eq_mul {R' : Type*} [HSMul R' A A] {r' : R'} {r r'' : R} (hr : r
 = r'') (h_smul : forall (a : A), r • a = r' • a) (a : A) : r' • a = (algebraMap
 R A r'' + 0) * a
参数：hr : r = r''；h_smul : forall (a : A), r • a = r' • a；a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
RingCompute.cast
-/
theorem cast_smul_eq_mul {R' : Type*} [HSMul R' A A] {r' : R'} {r r'' : R}
    (hr : r = r'') (h_smul : ∀ (a : A), r • a = r' • a) (a : A) :
    r' • a = (algebraMap R A r'' + 0) * a := by
  simp [← h_smul, ← hr, Algebra.smul_def r a]

/- RingCompute.neg -/
/-
**Mathlib.Tactic.Algebra.neg_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tacti
c.Algebra`。
形式化陈述：neg_algebraMap {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] {r t 
: R} (h : -r = t) : -(algebraMap R A r) = algebraMap R A t
参数：h : -r = t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…

--- 原说明 ---
RingCompute.neg
-/
theorem neg_algebraMap {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    {r t : R} (h : -r = t) :
    -(algebraMap R A r) = algebraMap R A t := by
  rw [← map_neg, h]

/- RingCompute.pow -/
/-
**Mathlib.Tactic.Algebra.pow_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tacti
c.Algebra`。
形式化陈述：pow_algebraMap {r s : R} {b : Nat} (h : r ^ b = s) : (algebraMap R A r) ^ 
b = algebraMap R A s
参数：h : r ^ b = s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…

--- 原说明 ---
RingCompute.pow
-/
theorem pow_algebraMap {r s : R} {b : ℕ} (h : r ^ b = s) :
    (algebraMap R A r) ^ b = algebraMap R A s := by
  rw [← map_pow, h]

/- RingCompute.inv -/
/-
**Mathlib.Tactic.Algebra.inv_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tacti
c.Algebra`。
形式化陈述：inv_algebraMap {R A : Type*} [Semifield R] [Semifield A] [Algebra R A] {r 
s : R} (h : r⁻¹ = s) : (algebraMap R A r)⁻¹ = algebraMap R A s
参数：h : r⁻¹ = s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_inv₀`：map_inv₀ : f a⁻¹ = (f a)⁻¹
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…

--- 原说明 ---
RingCompute.inv
-/
theorem inv_algebraMap {R A : Type*} [Semifield R] [Semifield A] [Algebra R A]
    {r s : R} (h : r⁻¹ = s) :
    (algebraMap R A r)⁻¹ = algebraMap R A s := by
  rw [← map_inv₀, h]

/- RingCompute.isOne -/
/-
**Mathlib.Tactic.Algebra.isOne_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tac
tic.Algebra`。
形式化陈述：isOne_algebraMap {r : R} (h : IsNat r 1) : IsNat (algebraMap R A (r + 0)) 
1
参数：h : IsNat r 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.out`：∀ {α : Type u} [inst : AddMonoidWithOne 
α] {a : α} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = ↑n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
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
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
RingCompute.isOne
-/
theorem isOne_algebraMap {r : R} (h : IsNat r 1) :
    IsNat (algebraMap R A (r + 0)) 1 := by
  simp only [h.out, Nat.cast_one, add_zero, map_one]
  exact ⟨by simp⟩

end RingCompute

end Mathlib.Tactic.Algebra

