/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Data.ENat.Basic
public import Mathlib.Data.ENNReal.Basic

/-!
# Coercion from `ℕ∞` to `ℝ≥0∞`

In this file we define a coercion from `ℕ∞` to `ℝ≥0∞` and prove some basic lemmas about this map.
-/

@[expose] public section

assert_not_exists Finset

open NNReal ENNReal

noncomputable section

namespace ENat

variable {m n : ℕ∞}

/-- Coercion from `ℕ∞` to `ℝ≥0∞`. -/
/-
**ENat.toENNReal** 是 Mathlib 中的一个定义，位于命名空间 `ENat`。
形式化陈述：ℕ∞ → ENNReal
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Coercion from `ℕ∞` to `ℝ≥0∞`.
-/
@[coe] def toENNReal : ℕ∞ → ℝ≥0∞ := ENat.map Nat.cast
/-
**ENat.hasCoeENNReal** 是 Mathlib 中的一个实例，位于命名空间 `ENat`。
形式化陈述：hasCoeENNReal : CoeTC Nat∞ Real>=0∞
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Coercion from `ℕ∞` to `ℝ≥0∞`.
-/
instance hasCoeENNReal : CoeTC ℕ∞ ℝ≥0∞ := ⟨toENNReal⟩

@[simp]
/-
**ENat.map_coe_nnreal** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：map_coe_nnreal : ENat.map ((↑) : Nat -> Real>=0) = ((↑) : Nat∞ -> Real>=0∞
)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_coe_nnreal : ENat.map ((↑) : ℕ → ℝ≥0) = ((↑) : ℕ∞ → ℝ≥0∞) :=
  rfl

/-- Coercion `ℕ∞ → ℝ≥0∞` as an `OrderEmbedding`. -/
@[simps! -fullyApplied]
/-
**ENat.toENNRealOrderEmbedding** 是 Mathlib 中的一个定义，位于命名空间 `ENat`。
形式化陈述：toENNRealOrderEmbedding : Nat∞ ↪o Real>=0∞
该定义给出了一等式。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `NNReal.instIsStrictOrderedRing_1`：IsStrictOrderedRing NNReal
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R

--- 原说明 ---
Coercion `ℕ∞ → ℝ≥0∞` as an `OrderEmbedding`.
-/
def toENNRealOrderEmbedding : ℕ∞ ↪o ℝ≥0∞ :=
  Nat.castOrderEmbedding.withTopMap

/-- Coercion `ℕ∞ → ℝ≥0∞` as a ring homomorphism. -/
@[simps! -fullyApplied]
/-
**ENat.toENNRealRingHom** 是 Mathlib 中的一个定义，位于命名空间 `ENat`。
形式化陈述：toENNRealRingHom : Nat∞ ->+* Real>=0∞
该定义给出了一等式。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd NNReal
· 使用定理 `NNReal.instNontrivial`：Nontrivial NNReal

--- 原说明 ---
Coercion `ℕ∞ → ℝ≥0∞` as a ring homomorphism.
-/
def toENNRealRingHom : ℕ∞ →+* ℝ≥0∞ :=
  .ENatMap (Nat.castRingHom ℝ≥0) Nat.cast_injective

@[simp, norm_cast]
/-
**ENat.toENNReal_top** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：toENNReal_top : ((⊤ : Nat∞) : Real>=0∞) = ⊤
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toENNReal_top : ((⊤ : ℕ∞) : ℝ≥0∞) = ⊤ :=
  rfl

@[simp, norm_cast]
/-
**ENat.toENNReal_coe** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：toENNReal_coe (n : Nat) : ((n : Nat∞) : Real>=0∞) = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toENNReal_coe (n : ℕ) : ((n : ℕ∞) : ℝ≥0∞) = n :=
  rfl

@[simp, norm_cast]
/-
**ENat.toENNReal_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：toENNReal_ofNat (n : Nat) [n.AtLeastTwo] : ((ofNat(n) : Nat∞) : Real>=0∞) 
= ofNat(n)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toENNReal_ofNat (n : ℕ) [n.AtLeastTwo] : ((ofNat(n) : ℕ∞) : ℝ≥0∞) = ofNat(n) :=
  rfl

@[simp, norm_cast]
/-
**ENat.toENNReal_inj** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：toENNReal_inj : (m : Real>=0∞) = (n : Real>=0∞) ↔ m = n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderEmbedding.eq_iff_eq`：eq_iff_eq {a b} : f a = f b ↔ a = b
-/
theorem toENNReal_inj : (m : ℝ≥0∞) = (n : ℝ≥0∞) ↔ m = n :=
  toENNRealOrderEmbedding.eq_iff_eq
/-
**ENat.toENNReal_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：∀ {n : ℕ∞}, ↑n = ⊤ ↔ n = ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp, norm_cast] lemma toENNReal_eq_top : (n : ℝ≥0∞) = ∞ ↔ n = ⊤ := by simp [← toENNReal_inj]
/-
**ENat.toENNReal_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：∀ {n : ℕ∞}, ↑n ≠ ⊤ ↔ n ≠ ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[norm_cast] lemma toENNReal_ne_top : (n : ℝ≥0∞) ≠ ∞ ↔ n ≠ ⊤ := by simp

@[simp, norm_cast, gcongr]
/-
**ENat.toENNReal_le** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：toENNReal_le : (m : Real>=0∞) <= n ↔ m <= n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderEmbedding.le_iff_le`：le_iff_le {a b} : f a <= f b ↔ a <= b
-/
theorem toENNReal_le : (m : ℝ≥0∞) ≤ n ↔ m ≤ n :=
  toENNRealOrderEmbedding.le_iff_le

@[simp, norm_cast, gcongr]
/-
**ENat.toENNReal_lt** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：toENNReal_lt : (m : Real>=0∞) < n ↔ m < n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderEmbedding.lt_iff_lt`：lt_iff_lt {a b} : f a < f b ↔ a < b
-/
theorem toENNReal_lt : (m : ℝ≥0∞) < n ↔ m < n :=
  toENNRealOrderEmbedding.lt_iff_lt

@[simp, norm_cast]
/-
**ENat.toENNReal_lt_top** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：toENNReal_lt_top : (n : Real>=0∞) < ∞ ↔ n < ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma toENNReal_lt_top : (n : ℝ≥0∞) < ∞ ↔ n < ⊤ := by simp [← toENNReal_lt]

@[gcongr, mono]
/-
**ENat.toENNReal_mono** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：toENNReal_mono : Monotone ((↑) : Nat∞ -> Real>=0∞)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderEmbedding.monotone`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorde
r α] [inst_1 : Preorder β] (f : α ↪o β), Monotone ⇑f
-/
theorem toENNReal_mono : Monotone ((↑) : ℕ∞ → ℝ≥0∞) :=
  toENNRealOrderEmbedding.monotone

@[gcongr, mono]
/-
**ENat.toENNReal_strictMono** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：toENNReal_strictMono : StrictMono ((↑) : Nat∞ -> Real>=0∞)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderEmbedding.strictMono`：∀ {α : Type u_2} {β : Type u_3} [inst : Preor
der α] [inst_1 : Preorder β] (f : α ↪o β), StrictMono ⇑f
-/
theorem toENNReal_strictMono : StrictMono ((↑) : ℕ∞ → ℝ≥0∞) :=
  toENNRealOrderEmbedding.strictMono

@[simp, norm_cast]
/-
**ENat.toENNReal_zero** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：toENNReal_zero : ((0 : Nat∞) : Real>=0∞) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
theorem toENNReal_zero : ((0 : ℕ∞) : ℝ≥0∞) = 0 :=
  map_zero toENNRealRingHom
/-
**ENat.toENNReal_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：∀ {n : ℕ∞}, ↑n = 0 ↔ n = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENat.toENNReal_zero`：toENNReal_zero : ((0 : Nat∞) : Real>=0∞) = 0
· 使用定理 `ENat.toENNReal_inj`：toENNReal_inj : (m : Real>=0∞) = (n : Real>=0∞) ↔ m 
= n
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma toENNReal_eq_zero : toENNReal n = 0 ↔ n = 0 := by rw [← toENNReal_zero, toENNReal_inj]

@[simp, norm_cast]
/-
**ENat.toENNReal_add** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：toENNReal_add (m n : Nat∞) : ↑(m + n) = (m + n : Real>=0∞)
参数：m n : Nat∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
-/
theorem toENNReal_add (m n : ℕ∞) : ↑(m + n) = (m + n : ℝ≥0∞) :=
  map_add toENNRealRingHom m n

@[simp, norm_cast]
/-
**ENat.toENNReal_one** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：toENNReal_one : ((1 : Nat∞) : Real>=0∞) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
theorem toENNReal_one : ((1 : ℕ∞) : ℝ≥0∞) = 1 :=
  map_one toENNRealRingHom

@[simp, norm_cast]
/-
**ENat.toENNReal_mul** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：toENNReal_mul (m n : Nat∞) : ↑(m * n) = (m * n : Real>=0∞)
参数：m n : Nat∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
-/
theorem toENNReal_mul (m n : ℕ∞) : ↑(m * n) = (m * n : ℝ≥0∞) :=
  map_mul toENNRealRingHom m n

@[simp, norm_cast]
/-
**ENat.toENNReal_pow** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：toENNReal_pow (x : Nat∞) (n : Nat) : (x ^ n : Nat∞) = (x : Real>=0∞) ^ n
参数：x : Nat∞；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
theorem toENNReal_pow (x : ℕ∞) (n : ℕ) : (x ^ n : ℕ∞) = (x : ℝ≥0∞) ^ n :=
  map_pow toENNRealRingHom x n

@[simp, norm_cast]
/-
**ENat.toENNReal_min** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：toENNReal_min (m n : Nat∞) : ↑(min m n) = (min m n : Real>=0∞)
参数：m n : Nat∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.map_min`：∀ {α : Type u} {β : Type v} [inst : LinearOrder α] [in
st_1 : LinearOrder β] {f : α → β} {a b : α},   Monotone f → f (min a b) = min (f
 a) (f…
· 使用定理 `ENat.toENNReal_mono`：toENNReal_mono : Monotone ((↑) : Nat∞ -> Real>=0∞)
-/
theorem toENNReal_min (m n : ℕ∞) : ↑(min m n) = (min m n : ℝ≥0∞) :=
  toENNReal_mono.map_min

@[simp, norm_cast]
/-
**ENat.toENNReal_max** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：toENNReal_max (m n : Nat∞) : ↑(max m n) = (max m n : Real>=0∞)
参数：m n : Nat∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.map_max`：Monotone.map_max (hf : Monotone f) : f (max a b) = max
 (f a) (f b)
· 使用定理 `ENat.toENNReal_mono`：toENNReal_mono : Monotone ((↑) : Nat∞ -> Real>=0∞)
-/
theorem toENNReal_max (m n : ℕ∞) : ↑(max m n) = (max m n : ℝ≥0∞) :=
  toENNReal_mono.map_max

@[simp, norm_cast]
/-
**ENat.toENNReal_sub** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：toENNReal_sub (m n : Nat∞) : ↑(m - n) = (m - n : Real>=0∞)
参数：m n : Nat∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.map_sub`：∀ {α : Type u_1} {β : Type u_2} [inst : Sub α] [inst_1 
: Bot α] [inst_2 : Sub β] [inst_3 : Bot β] {f : α → β},   (∀ (x y : α), f (x - y
) = f…
· 使用定理 `Nat.cast_tsub`：cast_tsub [CommSemiring α] [PartialOrder α] [IsOrderedRin
g α] [CanonicallyOrderedAdd α] [Sub α] [OrderedSub α] [AddLeftReflectLE α] (m n 
: N…
· 使用定理 `NNReal.instIsOrderedRing_1`：IsOrderedRing NNReal
· 使用定理 `NNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd NNReal
· 使用定理 `NNReal.instOrderedSub`：OrderedSub NNReal
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
-/
theorem toENNReal_sub (m n : ℕ∞) : ↑(m - n) = (m - n : ℝ≥0∞) :=
  WithTop.map_sub Nat.cast_tsub Nat.cast_zero m n

end ENat

