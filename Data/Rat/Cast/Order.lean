/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Data.Rat.Cast.CharZero
public import Mathlib.Tactic.Positivity.Core

/-!
# Casts of rational numbers into linear ordered fields.
-/

@[expose] public section

variable {F ι α β : Type*}

namespace Rat
variable {p q : ℚ}

@[simp]
/-
**Rat.castHom_rat** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：castHom_rat : castHom Rat = RingHom.id Rat
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `Rat.cast_id`：∀ (n : ℚ), ↑n = n
-/
theorem castHom_rat : castHom ℚ = RingHom.id ℚ :=
  RingHom.ext cast_id

section LinearOrderedField

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-
**Rat.cast_pos_of_pos** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：cast_pos_of_pos (hq : 0 < q) : (0 : K) < q
参数：hq : 0 < q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Rat.cast_def`：cast_def (q : Rat) : (q : K) = q.num / q.den
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Int.cast_pos`：∀ {R : Type u_1} [inst : AddCommGroupWithOne R] [inst_1 : 
PartialOrder R] [AddLeftMono R] [ZeroLEOneClass R] [NeZero 1]   {n : ℤ}, 0 < ↑n 
↔ …
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `Rat.num_pos`：∀ {a : ℚ}, 0 < a.num ↔ 0 < a
· 使用定理 `Nat.cast_pos`：cast_pos {α} [Semiring α] [PartialOrder α] [IsOrderedRing 
α] [Nontrivial α] {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `instNontrivialOfCharZero`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [
CharZero α], Nontrivial α
· 使用定理 `Rat.pos`：pos (a : Rat) : 0 < a.den
-/
theorem cast_pos_of_pos (hq : 0 < q) : (0 : K) < q := by
  rw [Rat.cast_def]
  exact div_pos (Int.cast_pos.2 <| num_pos.2 hq) (Nat.cast_pos.2 q.pos)

@[gcongr, mono]
/-
**Rat.cast_strictMono** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：cast_strictMono : StrictMono ((↑) : Rat -> K)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `Rat.instAddLeftMono`：AddLeftMono ℚ
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Rat.cast_sub`：∀ {α : Type u_3} [inst : DivisionRing α] [CharZero α] (p q
 : ℚ), ↑(p - q) = ↑p - ↑q
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Rat.cast_pos_of_pos`：cast_pos_of_pos (hq : 0 < q) : (0 : K) < q
-/
theorem cast_strictMono : StrictMono ((↑) : ℚ → K) := fun p q => by
  simpa only [sub_pos, cast_sub] using cast_pos_of_pos (K := K) (q := q - p)

@[gcongr, mono]
/-
**Rat.cast_mono** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：cast_mono : Monotone ((↑) : Rat -> K)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.monotone`：∀ {α : Type u} {β : Type v} [inst : PartialOrder α]
 [inst_1 : Preorder β] {f : α → β}, StrictMono f → Monotone f
· 使用定理 `Rat.cast_strictMono`：cast_strictMono : StrictMono ((↑) : Rat -> K)
-/
theorem cast_mono : Monotone ((↑) : ℚ → K) :=
  cast_strictMono.monotone

/-- Coercion from `ℚ` as an order embedding. -/
@[simps!]
/-
**Rat.castOrderEmbedding** 是 Mathlib 中的一个定义，位于命名空间 `Rat`。
形式化陈述：castOrderEmbedding : Rat ↪o K
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Rat.cast_strictMono`：cast_strictMono : StrictMono ((↑) : Rat -> K)

--- 原说明 ---
Coercion from `ℚ` as an order embedding.
-/
def castOrderEmbedding : ℚ ↪o K :=
  OrderEmbedding.ofStrictMono (↑) cast_strictMono
/-
**Rat.cast_le** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：∀ {p q : ℚ} {K : Type u_5} [inst : Field K] [inst_1 : LinearOrder K] [IsSt
rictOrderedRing K], ↑p ≤ ↑q ↔ p ≤ q
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderEmbedding.le_iff_le`：le_iff_le {a b} : f a <= f b ↔ a <= b
-/
@[simp, norm_cast] lemma cast_le : (p : K) ≤ q ↔ p ≤ q := castOrderEmbedding.le_iff_le
/-
**Rat.cast_lt** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：∀ {p q : ℚ} {K : Type u_5} [inst : Field K] [inst_1 : LinearOrder K] [IsSt
rictOrderedRing K], ↑p < ↑q ↔ p < q
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.lt_iff_lt`：StrictMono.lt_iff_lt (hf : StrictMono f) {a b : α}
 : f a < f b ↔ a < b
· 使用定理 `Rat.cast_strictMono`：cast_strictMono : StrictMono ((↑) : Rat -> K)
-/
@[simp, norm_cast] lemma cast_lt : (p : K) < q ↔ p < q := cast_strictMono.lt_iff_lt
/-
**Rat.cast_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：∀ {q : ℚ} {K : Type u_5} [inst : Field K] [inst_1 : LinearOrder K] [IsStri
ctOrderedRing K], 0 ≤ ↑q ↔ 0 ≤ q
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Rat.cast_zero`：cast_zero : ((0 : Rat) : α) = 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma cast_nonneg : 0 ≤ (q : K) ↔ 0 ≤ q := by norm_cast
/-
**Rat.cast_nonpos** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：∀ {q : ℚ} {K : Type u_5} [inst : Field K] [inst_1 : LinearOrder K] [IsStri
ctOrderedRing K], ↑q ≤ 0 ↔ q ≤ 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Rat.cast_zero`：cast_zero : ((0 : Rat) : α) = 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma cast_nonpos : (q : K) ≤ 0 ↔ q ≤ 0 := by norm_cast
/-
**Rat.cast_pos** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：∀ {q : ℚ} {K : Type u_5} [inst : Field K] [inst_1 : LinearOrder K] [IsStri
ctOrderedRing K], 0 < ↑q ↔ 0 < q
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Rat.cast_zero`：cast_zero : ((0 : Rat) : α) = 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma cast_pos : (0 : K) < q ↔ 0 < q := by norm_cast
/-
**Rat.cast_lt_zero** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：∀ {q : ℚ} {K : Type u_5} [inst : Field K] [inst_1 : LinearOrder K] [IsStri
ctOrderedRing K], ↑q < 0 ↔ q < 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Rat.cast_zero`：cast_zero : ((0 : Rat) : α) = 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma cast_lt_zero : (q : K) < 0 ↔ q < 0 := by norm_cast

@[simp, norm_cast]
/-
**Rat.cast_le_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：cast_le_natCast {m : Rat} {n : Nat} : (m : K) <= n ↔ m <= (n : Rat)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Rat.cast_le`：∀ {p q : ℚ} {K : Type u_5} [inst : Field K] [inst_1 : Linea
rOrder K] [IsStrictOrderedRing K], ↑p ≤ ↑q ↔ p ≤ q
· 使用定理 `Rat.cast_natCast`：cast_natCast (n : Nat) : ((n : Rat) : α) = n
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem cast_le_natCast {m : ℚ} {n : ℕ} : (m : K) ≤ n ↔ m ≤ (n : ℚ) := by
  rw [← cast_le (K := K), cast_natCast]

@[simp, norm_cast]
/-
**Rat.natCast_le_cast** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：natCast_le_cast {m : Nat} {n : Rat} : (m : K) <= n ↔ (m : Rat) <= n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Rat.cast_le`：∀ {p q : ℚ} {K : Type u_5} [inst : Field K] [inst_1 : Linea
rOrder K] [IsStrictOrderedRing K], ↑p ≤ ↑q ↔ p ≤ q
· 使用定理 `Rat.cast_natCast`：cast_natCast (n : Nat) : ((n : Rat) : α) = n
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem natCast_le_cast {m : ℕ} {n : ℚ} : (m : K) ≤ n ↔ (m : ℚ) ≤ n := by
  rw [← cast_le (K := K), cast_natCast]

@[simp, norm_cast]
/-
**Rat.cast_le_intCast** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：cast_le_intCast {m : Rat} {n : Int} : (m : K) <= n ↔ m <= (n : Rat)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Rat.cast_le`：∀ {p q : ℚ} {K : Type u_5} [inst : Field K] [inst_1 : Linea
rOrder K] [IsStrictOrderedRing K], ↑p ≤ ↑q ↔ p ≤ q
· 使用定理 `Rat.cast_intCast`：cast_intCast (n : Int) : ((n : Rat) : α) = n
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem cast_le_intCast {m : ℚ} {n : ℤ} : (m : K) ≤ n ↔ m ≤ (n : ℚ) := by
  rw [← cast_le (K := K), cast_intCast]

@[simp, norm_cast]
/-
**Rat.intCast_le_cast** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：intCast_le_cast {m : Int} {n : Rat} : (m : K) <= n ↔ (m : Rat) <= n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Rat.cast_le`：∀ {p q : ℚ} {K : Type u_5} [inst : Field K] [inst_1 : Linea
rOrder K] [IsStrictOrderedRing K], ↑p ≤ ↑q ↔ p ≤ q
· 使用定理 `Rat.cast_intCast`：cast_intCast (n : Int) : ((n : Rat) : α) = n
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem intCast_le_cast {m : ℤ} {n : ℚ} : (m : K) ≤ n ↔ (m : ℚ) ≤ n := by
  rw [← cast_le (K := K), cast_intCast]

@[simp, norm_cast]
/-
**Rat.cast_lt_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：cast_lt_natCast {m : Rat} {n : Nat} : (m : K) < n ↔ m < (n : Rat)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Rat.cast_lt`：∀ {p q : ℚ} {K : Type u_5} [inst : Field K] [inst_1 : Linea
rOrder K] [IsStrictOrderedRing K], ↑p < ↑q ↔ p < q
· 使用定理 `Rat.cast_natCast`：cast_natCast (n : Nat) : ((n : Rat) : α) = n
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem cast_lt_natCast {m : ℚ} {n : ℕ} : (m : K) < n ↔ m < (n : ℚ) := by
  rw [← cast_lt (K := K), cast_natCast]

@[simp, norm_cast]
/-
**Rat.natCast_lt_cast** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：natCast_lt_cast {m : Nat} {n : Rat} : (m : K) < n ↔ (m : Rat) < n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Rat.cast_lt`：∀ {p q : ℚ} {K : Type u_5} [inst : Field K] [inst_1 : Linea
rOrder K] [IsStrictOrderedRing K], ↑p < ↑q ↔ p < q
· 使用定理 `Rat.cast_natCast`：cast_natCast (n : Nat) : ((n : Rat) : α) = n
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem natCast_lt_cast {m : ℕ} {n : ℚ} : (m : K) < n ↔ (m : ℚ) < n := by
  rw [← cast_lt (K := K), cast_natCast]

@[simp, norm_cast]
/-
**Rat.cast_lt_intCast** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：cast_lt_intCast {m : Rat} {n : Int} : (m : K) < n ↔ m < (n : Rat)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Rat.cast_lt`：∀ {p q : ℚ} {K : Type u_5} [inst : Field K] [inst_1 : Linea
rOrder K] [IsStrictOrderedRing K], ↑p < ↑q ↔ p < q
· 使用定理 `Rat.cast_intCast`：cast_intCast (n : Int) : ((n : Rat) : α) = n
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem cast_lt_intCast {m : ℚ} {n : ℤ} : (m : K) < n ↔ m < (n : ℚ) := by
  rw [← cast_lt (K := K), cast_intCast]

@[simp, norm_cast]
/-
**Rat.intCast_lt_cast** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：intCast_lt_cast {m : Int} {n : Rat} : (m : K) < n ↔ (m : Rat) < n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Rat.cast_lt`：∀ {p q : ℚ} {K : Type u_5} [inst : Field K] [inst_1 : Linea
rOrder K] [IsStrictOrderedRing K], ↑p < ↑q ↔ p < q
· 使用定理 `Rat.cast_intCast`：cast_intCast (n : Int) : ((n : Rat) : α) = n
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem intCast_lt_cast {m : ℤ} {n : ℚ} : (m : K) < n ↔ (m : ℚ) < n := by
  rw [← cast_lt (K := K), cast_intCast]

@[simp, norm_cast]
/-
**Rat.cast_min** 是 Mathlib 中的一个引理，位于命名空间 `Rat`。
形式化陈述：cast_min (p q : Rat) : (↑(min p q) : K) = min (p : K) (q : K)
参数：p q : Rat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.map_min`：∀ {α : Type u} {β : Type v} [inst : LinearOrder α] [in
st_1 : LinearOrder β] {f : α → β} {a b : α},   Monotone f → f (min a b) = min (f
 a) (f…
· 使用定理 `Rat.cast_mono`：cast_mono : Monotone ((↑) : Rat -> K)
-/
lemma cast_min (p q : ℚ) : (↑(min p q) : K) = min (p : K) (q : K) := (@cast_mono K _).map_min

@[simp, norm_cast]
/-
**Rat.cast_max** 是 Mathlib 中的一个引理，位于命名空间 `Rat`。
形式化陈述：cast_max (p q : Rat) : (↑(max p q) : K) = max (p : K) (q : K)
参数：p q : Rat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.map_max`：Monotone.map_max (hf : Monotone f) : f (max a b) = max
 (f a) (f b)
· 使用定理 `Rat.cast_mono`：cast_mono : Monotone ((↑) : Rat -> K)
-/
lemma cast_max (p q : ℚ) : (↑(max p q) : K) = max (p : K) (q : K) := (@cast_mono K _).map_max
/-
**Rat.cast_abs** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：∀ {K : Type u_5} [inst : Field K] [inst_1 : LinearOrder K] [IsStrictOrdere
dRing K] (q : ℚ), ↑|q| = |↑q|
参数：q : ℚ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Rat.cast_max`：cast_max (p q : Rat) : (↑(max p q) : K) = max (p : K) (q :
 K)
· 使用定理 `Rat.cast_neg`：∀ {α : Type u_3} [inst : DivisionRing α] (q : ℚ), ↑(-q) = 
-↑q
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp, norm_cast] lemma cast_abs (q : ℚ) : ((|q| : ℚ) : K) = |(q : K)| := by simp [abs_eq_max_neg]

open Set

@[simp]
/-
**Rat.preimage_cast_Icc** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：preimage_cast_Icc (p q : Rat) : (↑) ⁻¹' Icc (p : K) q = Icc p q
参数：p q : Rat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderEmbedding.preimage_Icc`：∀ {α : Type u_1} {β : Type u_2} [inst : Pre
order α] [inst_1 : Preorder β] (e : α ↪o β) (x y : α),   ⇑e ⁻¹' Set.Icc (e x) (e
 y) = Set.Icc x y
-/
theorem preimage_cast_Icc (p q : ℚ) : (↑) ⁻¹' Icc (p : K) q = Icc p q :=
  castOrderEmbedding.preimage_Icc ..

@[simp]
/-
**Rat.preimage_cast_Ico** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：preimage_cast_Ico (p q : Rat) : (↑) ⁻¹' Ico (p : K) q = Ico p q
参数：p q : Rat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderEmbedding.preimage_Ico`：∀ {α : Type u_1} {β : Type u_2} [inst : Pre
order α] [inst_1 : Preorder β] (e : α ↪o β) (x y : α),   ⇑e ⁻¹' Set.Ico (e x) (e
 y) = Set.Ico x y
-/
theorem preimage_cast_Ico (p q : ℚ) : (↑) ⁻¹' Ico (p : K) q = Ico p q :=
  castOrderEmbedding.preimage_Ico ..

@[simp]
/-
**Rat.preimage_cast_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：preimage_cast_Ioc (p q : Rat) : (↑) ⁻¹' Ioc (p : K) q = Ioc p q
参数：p q : Rat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderEmbedding.preimage_Ioc`：∀ {α : Type u_1} {β : Type u_2} [inst : Pre
order α] [inst_1 : Preorder β] (e : α ↪o β) (x y : α),   ⇑e ⁻¹' Set.Ioc (e x) (e
 y) = Set.Ioc x y
-/
theorem preimage_cast_Ioc (p q : ℚ) : (↑) ⁻¹' Ioc (p : K) q = Ioc p q :=
  castOrderEmbedding.preimage_Ioc p q

@[simp]
/-
**Rat.preimage_cast_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：preimage_cast_Ioo (p q : Rat) : (↑) ⁻¹' Ioo (p : K) q = Ioo p q
参数：p q : Rat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderEmbedding.preimage_Ioo`：∀ {α : Type u_1} {β : Type u_2} [inst : Pre
order α] [inst_1 : Preorder β] (e : α ↪o β) (x y : α),   ⇑e ⁻¹' Set.Ioo (e x) (e
 y) = Set.Ioo x y
-/
theorem preimage_cast_Ioo (p q : ℚ) : (↑) ⁻¹' Ioo (p : K) q = Ioo p q :=
  castOrderEmbedding.preimage_Ioo p q

@[simp]
/-
**Rat.preimage_cast_Ici** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：preimage_cast_Ici (q : Rat) : (↑) ⁻¹' Ici (q : K) = Ici q
参数：q : Rat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderEmbedding.preimage_Ici`：∀ {α : Type u_1} {β : Type u_2} [inst : Pre
order α] [inst_1 : Preorder β] (e : α ↪o β) (x : α),   ⇑e ⁻¹' Set.Ici (e x) = Se
t.Ici x
-/
theorem preimage_cast_Ici (q : ℚ) : (↑) ⁻¹' Ici (q : K) = Ici q :=
  castOrderEmbedding.preimage_Ici q

@[simp]
/-
**Rat.preimage_cast_Iic** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：preimage_cast_Iic (q : Rat) : (↑) ⁻¹' Iic (q : K) = Iic q
参数：q : Rat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderEmbedding.preimage_Iic`：∀ {α : Type u_1} {β : Type u_2} [inst : Pre
order α] [inst_1 : Preorder β] (e : α ↪o β) (x : α),   ⇑e ⁻¹' Set.Iic (e x) = Se
t.Iic x
-/
theorem preimage_cast_Iic (q : ℚ) : (↑) ⁻¹' Iic (q : K) = Iic q :=
  castOrderEmbedding.preimage_Iic q

@[simp]
/-
**Rat.preimage_cast_Ioi** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：preimage_cast_Ioi (q : Rat) : (↑) ⁻¹' Ioi (q : K) = Ioi q
参数：q : Rat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderEmbedding.preimage_Ioi`：∀ {α : Type u_1} {β : Type u_2} [inst : Pre
order α] [inst_1 : Preorder β] (e : α ↪o β) (x : α),   ⇑e ⁻¹' Set.Ioi (e x) = Se
t.Ioi x
-/
theorem preimage_cast_Ioi (q : ℚ) : (↑) ⁻¹' Ioi (q : K) = Ioi q :=
  castOrderEmbedding.preimage_Ioi q

@[simp]
/-
**Rat.preimage_cast_Iio** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：preimage_cast_Iio (q : Rat) : (↑) ⁻¹' Iio (q : K) = Iio q
参数：q : Rat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderEmbedding.preimage_Iio`：∀ {α : Type u_1} {β : Type u_2} [inst : Pre
order α] [inst_1 : Preorder β] (e : α ↪o β) (x : α),   ⇑e ⁻¹' Set.Iio (e x) = Se
t.Iio x
-/
theorem preimage_cast_Iio (q : ℚ) : (↑) ⁻¹' Iio (q : K) = Iio q :=
  castOrderEmbedding.preimage_Iio q

@[simp]
/-
**Rat.preimage_cast_uIcc** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：preimage_cast_uIcc (p q : Rat) : (↑) ⁻¹' uIcc (p : K) q = uIcc p q
参数：p q : Rat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderEmbedding.preimage_uIcc`：∀ {α : Type u_1} {β : Type u_2} [inst : Li
nearOrder α] [inst_1 : Lattice β] (e : α ↪o β) (x y : α),   ⇑e ⁻¹' Set.uIcc (e x
) (e y) = Set.uIcc…
-/
theorem preimage_cast_uIcc (p q : ℚ) : (↑) ⁻¹' uIcc (p : K) q = uIcc p q :=
  (castOrderEmbedding (K := K)).preimage_uIcc p q

@[simp]
/-
**Rat.preimage_cast_uIoc** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：preimage_cast_uIoc (p q : Rat) : (↑) ⁻¹' uIoc (p : K) q = uIoc p q
参数：p q : Rat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderEmbedding.preimage_uIoc`：∀ {α : Type u_1} {β : Type u_2} [inst : Li
nearOrder α] [inst_1 : LinearOrder β] (e : α ↪o β) (x y : α),   ⇑e ⁻¹' Set.uIoc 
(e x) (e y) = Set.…
-/
theorem preimage_cast_uIoc (p q : ℚ) : (↑) ⁻¹' uIoc (p : K) q = uIoc p q :=
  (castOrderEmbedding (K := K)).preimage_uIoc p q

end LinearOrderedField
end Rat

namespace NNRat

variable {K} [Semifield K] [LinearOrder K] [IsStrictOrderedRing K] {p q : ℚ≥0}

/-
**NNRat.cast_strictMono** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：cast_strictMono : StrictMono ((↑) : Rat>=0 -> K)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `NNRat.cast_def`：cast_def (q : Rat>=0) : (q : K) = q.num / q.den
· 使用引理 `div_lt_div_iff₀`：div_lt_div_iff₀ (hb : 0 < b) (hd : 0 < d) : a / b < c /
 d ↔ a * d < c * b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instNontrivialOfCharZero`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [
CharZero α], Nontrivial α
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `Nat.cast_lt`：cast_lt : (m : α) < n ↔ m < n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `NNRat.lt_def`：lt_def {p q : Rat>=0} : p < q ↔ p.num * q.den < q.num * p.
den
-/
theorem cast_strictMono : StrictMono ((↑) : ℚ≥0 → K) := fun p q h => by
  rwa [NNRat.cast_def, NNRat.cast_def, div_lt_div_iff₀, ← Nat.cast_mul, ← Nat.cast_mul,
    Nat.cast_lt (α := K), ← NNRat.lt_def]
  · simp
  · simp

@[gcongr, mono]
/-
**NNRat.cast_mono** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：cast_mono : Monotone ((↑) : Rat>=0 -> K)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.monotone`：∀ {α : Type u} {β : Type v} [inst : PartialOrder α]
 [inst_1 : Preorder β] {f : α → β}, StrictMono f → Monotone f
· 使用定理 `NNRat.cast_strictMono`：cast_strictMono : StrictMono ((↑) : Rat>=0 -> K)
-/
theorem cast_mono : Monotone ((↑) : ℚ≥0 → K) :=
  cast_strictMono.monotone

/-- Coercion from `ℚ` as an order embedding. -/
@[simps!]
/-
**NNRat.castOrderEmbedding** 是 Mathlib 中的一个定义，位于命名空间 `NNRat`。
形式化陈述：castOrderEmbedding : Rat>=0 ↪o K
该定义给出了一等式。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NNRat.cast_strictMono`：cast_strictMono : StrictMono ((↑) : Rat>=0 -> K)

--- 原说明 ---
Coercion from `ℚ` as an order embedding.
-/
def castOrderEmbedding : ℚ≥0 ↪o K :=
  OrderEmbedding.ofStrictMono (↑) cast_strictMono
/-
**NNRat.cast_le** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：∀ {K : Type u_5} [inst : Semifield K] [inst_1 : LinearOrder K] [IsStrictOr
deredRing K] {p q : ℚ≥0}, ↑p ≤ ↑q ↔ p ≤ q
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderEmbedding.le_iff_le`：le_iff_le {a b} : f a <= f b ↔ a <= b
-/
@[simp, norm_cast] lemma cast_le : (p : K) ≤ q ↔ p ≤ q := castOrderEmbedding.le_iff_le
/-
**NNRat.cast_lt** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：∀ {K : Type u_5} [inst : Semifield K] [inst_1 : LinearOrder K] [IsStrictOr
deredRing K] {p q : ℚ≥0}, ↑p < ↑q ↔ p < q
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.lt_iff_lt`：StrictMono.lt_iff_lt (hf : StrictMono f) {a b : α}
 : f a < f b ↔ a < b
· 使用定理 `NNRat.cast_strictMono`：cast_strictMono : StrictMono ((↑) : Rat>=0 -> K)
-/
@[simp, norm_cast] lemma cast_lt : (p : K) < q ↔ p < q := cast_strictMono.lt_iff_lt
/-
**NNRat.cast_nonpos** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：∀ {K : Type u_5} [inst : Semifield K] [inst_1 : LinearOrder K] [IsStrictOr
deredRing K] {q : ℚ≥0}, ↑q ≤ 0 ↔ q ≤ 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `NNRat.cast_zero`：∀ {α : Type u_3} [inst : DivisionSemiring α], ↑0 = 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma cast_nonpos : (q : K) ≤ 0 ↔ q ≤ 0 := by norm_cast
/-
**NNRat.cast_pos** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：∀ {K : Type u_5} [inst : Semifield K] [inst_1 : LinearOrder K] [IsStrictOr
deredRing K] {q : ℚ≥0}, 0 < ↑q ↔ 0 < q
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `NNRat.cast_zero`：∀ {α : Type u_3} [inst : DivisionSemiring α], ↑0 = 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma cast_pos : (0 : K) < q ↔ 0 < q := by norm_cast
/-
**NNRat.cast_lt_zero** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：∀ {K : Type u_5} [inst : Semifield K] [inst_1 : LinearOrder K] [IsStrictOr
deredRing K] {q : ℚ≥0}, ↑q < 0 ↔ q < 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `NNRat.cast_zero`：∀ {α : Type u_3} [inst : DivisionSemiring α], ↑0 = 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[norm_cast] lemma cast_lt_zero : (q : K) < 0 ↔ q < 0 := by norm_cast
/-
**NNRat.not_cast_lt_zero** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：∀ {K : Type u_5} [inst : Semifield K] [inst_1 : LinearOrder K] [IsStrictOr
deredRing K] {q : ℚ≥0}, ¬↑q < 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `NNRat.cast_zero`：∀ {α : Type u_3} [inst : DivisionSemiring α], ↑0 = 0
· 使用定理 `not_lt_zero`：∀ {α : Type u_1} {a : α} [inst : Preorder α] [inst_1 : Zero
 α] [IsBotZeroClass α], ¬a < 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
-/
@[simp] lemma not_cast_lt_zero : ¬(q : K) < 0 := mod_cast not_lt_zero
/-
**NNRat.cast_le_one** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：∀ {K : Type u_5} [inst : Semifield K] [inst_1 : LinearOrder K] [IsStrictOr
deredRing K] {p : ℚ≥0}, ↑p ≤ 1 ↔ p ≤ 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `NNRat.cast_one`：∀ {α : Type u_3} [inst : DivisionSemiring α], ↑1 = 1
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma cast_le_one : (p : K) ≤ 1 ↔ p ≤ 1 := by norm_cast
/-
**NNRat.one_le_cast** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：∀ {K : Type u_5} [inst : Semifield K] [inst_1 : LinearOrder K] [IsStrictOr
deredRing K] {p : ℚ≥0}, 1 ≤ ↑p ↔ 1 ≤ p
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `NNRat.cast_one`：∀ {α : Type u_3} [inst : DivisionSemiring α], ↑1 = 1
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma one_le_cast : 1 ≤ (p : K) ↔ 1 ≤ p := by norm_cast
/-
**NNRat.cast_lt_one** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：∀ {K : Type u_5} [inst : Semifield K] [inst_1 : LinearOrder K] [IsStrictOr
deredRing K] {p : ℚ≥0}, ↑p < 1 ↔ p < 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `NNRat.cast_one`：∀ {α : Type u_3} [inst : DivisionSemiring α], ↑1 = 1
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma cast_lt_one : (p : K) < 1 ↔ p < 1 := by norm_cast
/-
**NNRat.one_lt_cast** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：∀ {K : Type u_5} [inst : Semifield K] [inst_1 : LinearOrder K] [IsStrictOr
deredRing K] {p : ℚ≥0}, 1 < ↑p ↔ 1 < p
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `NNRat.cast_one`：∀ {α : Type u_3} [inst : DivisionSemiring α], ↑1 = 1
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma one_lt_cast : 1 < (p : K) ↔ 1 < p := by norm_cast

section ofNat
variable {n : ℕ} [n.AtLeastTwo]

/-
**NNRat.cast_le_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：∀ {K : Type u_5} [inst : Semifield K] [inst_1 : LinearOrder K] [IsStrictOr
deredRing K] {p : ℚ≥0} {n : ℕ}   [inst_3 : n.AtLeastTwo], ↑p ≤ OfNat.ofNat n ↔ p
 ≤ OfNat.ofNat n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNRat.cast_le`：∀ {K : Type u_5} [inst : Semifield K] [inst_1 : LinearOrd
er K] [IsStrictOrderedRing K] {p q : ℚ≥0}, ↑p ≤ ↑q ↔ p ≤ q
· 使用定理 `NNRat.cast_ofNat`：∀ {α : Type u_3} [inst : DivisionSemiring α] (n : ℕ) [
inst_1 : n.AtLeastTwo], ↑(OfNat.ofNat n) = OfNat.ofNat n
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma cast_le_ofNat : (p : K) ≤ ofNat(n) ↔ p ≤ OfNat.ofNat n := by
  simp [← cast_le (K := K)]
/-
**NNRat.ofNat_le_cast** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：∀ {K : Type u_5} [inst : Semifield K] [inst_1 : LinearOrder K] [IsStrictOr
deredRing K] {p : ℚ≥0} {n : ℕ}   [inst_3 : n.AtLeastTwo], OfNat.ofNat n ≤ ↑p ↔ O
fNat.ofNat n ≤ p
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNRat.cast_le`：∀ {K : Type u_5} [inst : Semifield K] [inst_1 : LinearOrd
er K] [IsStrictOrderedRing K] {p q : ℚ≥0}, ↑p ≤ ↑q ↔ p ≤ q
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `NNRat.cast_ofNat`：∀ {α : Type u_3} [inst : DivisionSemiring α] (n : ℕ) [
inst_1 : n.AtLeastTwo], ↑(OfNat.ofNat n) = OfNat.ofNat n
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma ofNat_le_cast : ofNat(n) ≤ (p : K) ↔ OfNat.ofNat n ≤ p := by
  simp [← cast_le (K := K)]
/-
**NNRat.cast_lt_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：∀ {K : Type u_5} [inst : Semifield K] [inst_1 : LinearOrder K] [IsStrictOr
deredRing K] {p : ℚ≥0} {n : ℕ}   [inst_3 : n.AtLeastTwo], ↑p < OfNat.ofNat n ↔ p
 < OfNat.ofNat n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNRat.cast_lt`：∀ {K : Type u_5} [inst : Semifield K] [inst_1 : LinearOrd
er K] [IsStrictOrderedRing K] {p q : ℚ≥0}, ↑p < ↑q ↔ p < q
· 使用定理 `NNRat.cast_ofNat`：∀ {α : Type u_3} [inst : DivisionSemiring α] (n : ℕ) [
inst_1 : n.AtLeastTwo], ↑(OfNat.ofNat n) = OfNat.ofNat n
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma cast_lt_ofNat : (p : K) < ofNat(n) ↔ p < OfNat.ofNat n := by
  simp [← cast_lt (K := K)]
/-
**NNRat.ofNat_lt_cast** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：∀ {K : Type u_5} [inst : Semifield K] [inst_1 : LinearOrder K] [IsStrictOr
deredRing K] {p : ℚ≥0} {n : ℕ}   [inst_3 : n.AtLeastTwo], OfNat.ofNat n < ↑p ↔ O
fNat.ofNat n < p
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNRat.cast_lt`：∀ {K : Type u_5} [inst : Semifield K] [inst_1 : LinearOrd
er K] [IsStrictOrderedRing K] {p q : ℚ≥0}, ↑p < ↑q ↔ p < q
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `NNRat.cast_ofNat`：∀ {α : Type u_3} [inst : DivisionSemiring α] (n : ℕ) [
inst_1 : n.AtLeastTwo], ↑(OfNat.ofNat n) = OfNat.ofNat n
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma ofNat_lt_cast : ofNat(n) < (p : K) ↔ OfNat.ofNat n < p := by
  simp [← cast_lt (K := K)]

end ofNat

@[simp, norm_cast]
/-
**NNRat.cast_le_natCast** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：cast_le_natCast {m : Rat>=0} {n : Nat} : (m : K) <= n ↔ m <= (n : Rat>=0)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNRat.cast_le`：∀ {K : Type u_5} [inst : Semifield K] [inst_1 : LinearOrd
er K] [IsStrictOrderedRing K] {p q : ℚ≥0}, ↑p ≤ ↑q ↔ p ≤ q
· 使用定理 `NNRat.cast_natCast`：∀ {α : Type u_3} [inst : DivisionSemiring α] (n : ℕ)
, ↑↑n = ↑n
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem cast_le_natCast {m : ℚ≥0} {n : ℕ} : (m : K) ≤ n ↔ m ≤ (n : ℚ≥0) := by
  rw [← cast_le (K := K), cast_natCast]

@[simp, norm_cast]
/-
**NNRat.natCast_le_cast** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：natCast_le_cast {m : Nat} {n : Rat>=0} : (m : K) <= n ↔ (m : Rat>=0) <= n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNRat.cast_le`：∀ {K : Type u_5} [inst : Semifield K] [inst_1 : LinearOrd
er K] [IsStrictOrderedRing K] {p q : ℚ≥0}, ↑p ≤ ↑q ↔ p ≤ q
· 使用定理 `NNRat.cast_natCast`：∀ {α : Type u_3} [inst : DivisionSemiring α] (n : ℕ)
, ↑↑n = ↑n
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem natCast_le_cast {m : ℕ} {n : ℚ≥0} : (m : K) ≤ n ↔ (m : ℚ≥0) ≤ n := by
  rw [← cast_le (K := K), cast_natCast]

@[simp, norm_cast]
/-
**NNRat.cast_lt_natCast** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：cast_lt_natCast {m : Rat>=0} {n : Nat} : (m : K) < n ↔ m < (n : Rat>=0)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNRat.cast_lt`：∀ {K : Type u_5} [inst : Semifield K] [inst_1 : LinearOrd
er K] [IsStrictOrderedRing K] {p q : ℚ≥0}, ↑p < ↑q ↔ p < q
· 使用定理 `NNRat.cast_natCast`：∀ {α : Type u_3} [inst : DivisionSemiring α] (n : ℕ)
, ↑↑n = ↑n
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem cast_lt_natCast {m : ℚ≥0} {n : ℕ} : (m : K) < n ↔ m < (n : ℚ≥0) := by
  rw [← cast_lt (K := K), cast_natCast]

@[simp, norm_cast]
/-
**NNRat.natCast_lt_cast** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：natCast_lt_cast {m : Nat} {n : Rat>=0} : (m : K) < n ↔ (m : Rat>=0) < n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNRat.cast_lt`：∀ {K : Type u_5} [inst : Semifield K] [inst_1 : LinearOrd
er K] [IsStrictOrderedRing K] {p q : ℚ≥0}, ↑p < ↑q ↔ p < q
· 使用定理 `NNRat.cast_natCast`：∀ {α : Type u_3} [inst : DivisionSemiring α] (n : ℕ)
, ↑↑n = ↑n
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem natCast_lt_cast {m : ℕ} {n : ℚ≥0} : (m : K) < n ↔ (m : ℚ≥0) < n := by
  rw [← cast_lt (K := K), cast_natCast]
/-
**NNRat.cast_min** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：∀ {K : Type u_5} [inst : Semifield K] [inst_1 : LinearOrder K] [IsStrictOr
deredRing K] (p q : ℚ≥0),   ↑(min p q) = min ↑p ↑q
参数：p q : ℚ≥0；min p q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.map_min`：∀ {α : Type u} {β : Type v} [inst : LinearOrder α] [in
st_1 : LinearOrder β] {f : α → β} {a b : α},   Monotone f → f (min a b) = min (f
 a) (f…
· 使用定理 `NNRat.cast_mono`：cast_mono : Monotone ((↑) : Rat>=0 -> K)
-/
@[simp, norm_cast] lemma cast_min (p q : ℚ≥0) : (↑(min p q) : K) = min (p : K) (q : K) :=
  (@cast_mono K _).map_min
/-
**NNRat.cast_max** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：∀ {K : Type u_5} [inst : Semifield K] [inst_1 : LinearOrder K] [IsStrictOr
deredRing K] (p q : ℚ≥0),   ↑(max p q) = max ↑p ↑q
参数：p q : ℚ≥0；max p q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.map_max`：Monotone.map_max (hf : Monotone f) : f (max a b) = max
 (f a) (f b)
· 使用定理 `NNRat.cast_mono`：cast_mono : Monotone ((↑) : Rat>=0 -> K)
-/
@[simp, norm_cast] lemma cast_max (p q : ℚ≥0) : (↑(max p q) : K) = max (p : K) (q : K) :=
  (@cast_mono K _).map_max

open Set

@[simp]
/-
**NNRat.preimage_cast_Icc** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：preimage_cast_Icc (p q : Rat>=0) : (↑) ⁻¹' Icc (p : K) q = Icc p q
参数：p q : Rat>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderEmbedding.preimage_Icc`：∀ {α : Type u_1} {β : Type u_2} [inst : Pre
order α] [inst_1 : Preorder β] (e : α ↪o β) (x y : α),   ⇑e ⁻¹' Set.Icc (e x) (e
 y) = Set.Icc x y
-/
theorem preimage_cast_Icc (p q : ℚ≥0) : (↑) ⁻¹' Icc (p : K) q = Icc p q :=
  castOrderEmbedding.preimage_Icc ..

@[simp]
/-
**NNRat.preimage_cast_Ico** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：preimage_cast_Ico (p q : Rat>=0) : (↑) ⁻¹' Ico (p : K) q = Ico p q
参数：p q : Rat>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderEmbedding.preimage_Ico`：∀ {α : Type u_1} {β : Type u_2} [inst : Pre
order α] [inst_1 : Preorder β] (e : α ↪o β) (x y : α),   ⇑e ⁻¹' Set.Ico (e x) (e
 y) = Set.Ico x y
-/
theorem preimage_cast_Ico (p q : ℚ≥0) : (↑) ⁻¹' Ico (p : K) q = Ico p q :=
  castOrderEmbedding.preimage_Ico ..

@[simp]
/-
**NNRat.preimage_cast_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：preimage_cast_Ioc (p q : Rat>=0) : (↑) ⁻¹' Ioc (p : K) q = Ioc p q
参数：p q : Rat>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderEmbedding.preimage_Ioc`：∀ {α : Type u_1} {β : Type u_2} [inst : Pre
order α] [inst_1 : Preorder β] (e : α ↪o β) (x y : α),   ⇑e ⁻¹' Set.Ioc (e x) (e
 y) = Set.Ioc x y
-/
theorem preimage_cast_Ioc (p q : ℚ≥0) : (↑) ⁻¹' Ioc (p : K) q = Ioc p q :=
  castOrderEmbedding.preimage_Ioc p q

@[simp]
/-
**NNRat.preimage_cast_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：preimage_cast_Ioo (p q : Rat>=0) : (↑) ⁻¹' Ioo (p : K) q = Ioo p q
参数：p q : Rat>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderEmbedding.preimage_Ioo`：∀ {α : Type u_1} {β : Type u_2} [inst : Pre
order α] [inst_1 : Preorder β] (e : α ↪o β) (x y : α),   ⇑e ⁻¹' Set.Ioo (e x) (e
 y) = Set.Ioo x y
-/
theorem preimage_cast_Ioo (p q : ℚ≥0) : (↑) ⁻¹' Ioo (p : K) q = Ioo p q :=
  castOrderEmbedding.preimage_Ioo p q

@[simp]
/-
**NNRat.preimage_cast_Ici** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：preimage_cast_Ici (p : Rat>=0) : (↑) ⁻¹' Ici (p : K) = Ici p
参数：p : Rat>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderEmbedding.preimage_Ici`：∀ {α : Type u_1} {β : Type u_2} [inst : Pre
order α] [inst_1 : Preorder β] (e : α ↪o β) (x : α),   ⇑e ⁻¹' Set.Ici (e x) = Se
t.Ici x
-/
theorem preimage_cast_Ici (p : ℚ≥0) : (↑) ⁻¹' Ici (p : K) = Ici p :=
  castOrderEmbedding.preimage_Ici p

@[simp]
/-
**NNRat.preimage_cast_Iic** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：preimage_cast_Iic (p : Rat>=0) : (↑) ⁻¹' Iic (p : K) = Iic p
参数：p : Rat>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderEmbedding.preimage_Iic`：∀ {α : Type u_1} {β : Type u_2} [inst : Pre
order α] [inst_1 : Preorder β] (e : α ↪o β) (x : α),   ⇑e ⁻¹' Set.Iic (e x) = Se
t.Iic x
-/
theorem preimage_cast_Iic (p : ℚ≥0) : (↑) ⁻¹' Iic (p : K) = Iic p :=
  castOrderEmbedding.preimage_Iic p

@[simp]
/-
**NNRat.preimage_cast_Ioi** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：preimage_cast_Ioi (p : Rat>=0) : (↑) ⁻¹' Ioi (p : K) = Ioi p
参数：p : Rat>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderEmbedding.preimage_Ioi`：∀ {α : Type u_1} {β : Type u_2} [inst : Pre
order α] [inst_1 : Preorder β] (e : α ↪o β) (x : α),   ⇑e ⁻¹' Set.Ioi (e x) = Se
t.Ioi x
-/
theorem preimage_cast_Ioi (p : ℚ≥0) : (↑) ⁻¹' Ioi (p : K) = Ioi p :=
  castOrderEmbedding.preimage_Ioi p

@[simp]
/-
**NNRat.preimage_cast_Iio** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：preimage_cast_Iio (p : Rat>=0) : (↑) ⁻¹' Iio (p : K) = Iio p
参数：p : Rat>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderEmbedding.preimage_Iio`：∀ {α : Type u_1} {β : Type u_2} [inst : Pre
order α] [inst_1 : Preorder β] (e : α ↪o β) (x : α),   ⇑e ⁻¹' Set.Iio (e x) = Se
t.Iio x
-/
theorem preimage_cast_Iio (p : ℚ≥0) : (↑) ⁻¹' Iio (p : K) = Iio p :=
  castOrderEmbedding.preimage_Iio p

@[simp]
/-
**NNRat.preimage_cast_uIcc** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：preimage_cast_uIcc (p q : Rat>=0) : (↑) ⁻¹' uIcc (p : K) q = uIcc p q
参数：p q : Rat>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderEmbedding.preimage_uIcc`：∀ {α : Type u_1} {β : Type u_2} [inst : Li
nearOrder α] [inst_1 : Lattice β] (e : α ↪o β) (x y : α),   ⇑e ⁻¹' Set.uIcc (e x
) (e y) = Set.uIcc…
-/
theorem preimage_cast_uIcc (p q : ℚ≥0) : (↑) ⁻¹' uIcc (p : K) q = uIcc p q :=
  (castOrderEmbedding (K := K)).preimage_uIcc p q

@[simp]
/-
**NNRat.preimage_cast_uIoc** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：preimage_cast_uIoc (p q : Rat>=0) : (↑) ⁻¹' uIoc (p : K) q = uIoc p q
参数：p q : Rat>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderEmbedding.preimage_uIoc`：∀ {α : Type u_1} {β : Type u_2} [inst : Li
nearOrder α] [inst_1 : LinearOrder β] (e : α ↪o β) (x y : α),   ⇑e ⁻¹' Set.uIoc 
(e x) (e y) = Set.…
-/
theorem preimage_cast_uIoc (p q : ℚ≥0) : (↑) ⁻¹' uIoc (p : K) q = uIoc p q :=
  (castOrderEmbedding (K := K)).preimage_uIoc p q

end NNRat

namespace Mathlib.Meta.Positivity
open Lean Meta Qq Function

/-- Extension for Rat.cast. -/
@[positivity Rat.cast _]
meta def evalRatCast : PositivityExt where eval {u α} _zα pα? e := do
  let ~q(@Rat.cast _ (_) ($a : ℚ)) := e | throwError "not Rat.cast"
  match ← core q(inferInstance) (some q(inferInstance)) a with
  | .positive pa => id <|
    match pα? with
    | none => do
      let _oα ← synthInstanceQ q(DivisionRing $α)
      let _cα ← synthInstanceQ q(CharZero $α)
      assumeInstancesCommute
      return .nonzero q((Rat.cast_ne_zero (α := $α)).mpr ($pa).ne')
    | some _ => do
      let _oα ← synthInstanceQ q(Field $α)
      let _oα ← synthInstanceQ q(LinearOrder $α)
      let _oα ← synthInstanceQ q(IsStrictOrderedRing $α)
      assumeInstancesCommute
      return .positive q((Rat.cast_pos (K := $α)).mpr $pa)
  | .nonnegative pa => id <|
    match pα? with | none => pure .none | some _ => do
    let _oα ← synthInstanceQ q(Field $α)
    let _oα ← synthInstanceQ q(LinearOrder $α)
    let _oα ← synthInstanceQ q(IsStrictOrderedRing $α)
    assumeInstancesCommute
    return .nonnegative q((Rat.cast_nonneg (K := $α)).mpr $pa)
  | .nonzero pa =>
    let _oα ← synthInstanceQ q(DivisionRing $α)
    let _cα ← synthInstanceQ q(CharZero $α)
    assumeInstancesCommute
    return .nonzero q((Rat.cast_ne_zero (α := $α)).mpr $pa)
  | .none => pure .none

/-- Extension for NNRat.cast. -/
@[positivity NNRat.cast _]
meta def evalNNRatCast : PositivityExt where eval {u α} _zα pα? e :=
  match pα? with | none => pure .none | some _ => do
  let ~q(@NNRat.cast _ (_) ($a : ℚ≥0)) := e | throwError "not NNRat.cast"
  match ← core q(inferInstance) (some q(inferInstance)) a with
  | .positive pa =>
    let _oα ← synthInstanceQ q(Semifield $α)
    let _oα ← synthInstanceQ q(LinearOrder $α)
    let _oα ← synthInstanceQ q(IsStrictOrderedRing $α)
    assumeInstancesCommute
    return .positive q((NNRat.cast_pos (K := $α)).mpr $pa)
  | _ =>
    let _oα ← synthInstanceQ q(Semifield $α)
    let _oα ← synthInstanceQ q(LinearOrder $α)
    let _oα ← synthInstanceQ q(IsStrictOrderedRing $α)
    assumeInstancesCommute
    return .nonnegative q(NNRat.cast_nonneg _)

end Mathlib.Meta.Positivity

