/-
Copyright (c) 2024 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.NumberTheory.SiegelsLemma
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.NumberTheory.NumberField.EquivReindex

/-!
# House of an algebraic number

This file defines the house of an algebraic number `α`, which is
the largest of the modulus of its conjugates.

## References
* [D. Marcus, *Number Fields*][marcus1977number]
* [Hua, L.-K., *Introduction to number theory*][hua1982house]

## Tags
number field, algebraic number, house
-/

@[expose] public section

variable {K : Type*} [Field K] [NumberField K]

namespace NumberField

noncomputable section

open Module.Free Module canonicalEmbedding Matrix Finset

attribute [local instance] Matrix.seminormedAddCommGroup

/-- The house of an algebraic number as the norm of its image by the canonical embedding. -/
/-
**NumberField.house** 是 Mathlib 中的一个定义，位于命名空间 `NumberField`。
形式化陈述：house (α : K) : Real
参数：α : K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The house of an algebraic number as the norm of its image by the canonical embed
ding.
-/
def house (α : K) : ℝ := ‖canonicalEmbedding K α‖

/-- The house is the largest of the modulus of the conjugates of an algebraic number. -/
/-
**NumberField.house_eq_sup'** 是 Mathlib 中的一个定理，位于命名空间 `NumberField`。
形式化陈述：house_eq_sup' (α : K) : house α = univ.sup' univ_nonempty (fun φ : K ->+* 
Complex => ‖φ α‖₊)
参数：α : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `Finset.univ_nonempty`：univ_nonempty [Nonempty α] : (univ : Finset α).Non
empty
· 使用定理 `NumberField.Embeddings.instNonemptyRingHom`：∀ (K : Type u_1) [inst : Fie
ld K] (A : Type u_2) [inst_1 : Field A] [CharZero A] [NumberField K] [IsAlgClose
d A],   Nonempty (K →+* A)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.house.eq_1`：∀ {K : Type u_1} [inst : Field K] [inst_1 : Numb
erField K] (α : K),   NumberField.house α = ‖(NumberField.canonicalEmbedding K) 
α‖
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `coe_nnnorm`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ↑‖a‖
₊ = ‖a‖
· 使用定理 `NumberField.canonicalEmbedding.nnnorm_eq`：nnnorm_eq [NumberField K] (x :
 K) : ‖canonicalEmbedding K x‖₊ = Finset.univ.sup (fun φ : K ->+* Complex => ‖φ 
x‖₊)
· 使用定理 `Finset.sup'_eq_sup`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeS
up α] [inst_1 : OrderBot α] {s : Finset β} (H : s.Nonempty)   (f : β → α), s.sup
' H f = …

--- 原说明 ---
The house is the largest of the modulus of the conjugates of an algebraic number
.
-/
theorem house_eq_sup' (α : K) :
    house α = univ.sup' univ_nonempty (fun φ : K →+* ℂ ↦ ‖φ α‖₊) := by
  rw [house, ← coe_nnnorm, nnnorm_eq, ← sup'_eq_sup univ_nonempty]
/-
**NumberField.house_sum_le_sum_house** 是 Mathlib 中的一个定理，位于命名空间 `NumberField`。
形式化陈述：house_sum_le_sum_house {ι : Type*} (s : Finset ι) (α : ι -> K) : house (∑ 
i in s, α i) <= ∑ i in s, house (α i)
参数：s : Finset ι；α : ι -> K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `norm_sum_le_of_le`：∀ {ι : Type u_3} {E : Type u_5} [inst : SeminormedAdd
CommGroup E] (s : Finset ι) {f : ι → E} {n : ι → ℝ},   (∀ b ∈ s, ‖f b‖ ≤ n b) → 
‖∑ b ∈ …
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem house_sum_le_sum_house {ι : Type*} (s : Finset ι) (α : ι → K) :
    house (∑ i ∈ s, α i) ≤ ∑ i ∈ s, house (α i) := by
  simp only [house, map_sum]; apply norm_sum_le_of_le; intros; rfl
/-
**NumberField.house_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `NumberField`。
形式化陈述：house_nonneg (α : K) : 0 <= house α
参数：α : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
-/
theorem house_nonneg (α : K) : 0 ≤ house α := norm_nonneg _
/-
**NumberField.house_mul_le** 是 Mathlib 中的一个定理，位于命名空间 `NumberField`。
形式化陈述：house_mul_le (α β : K) : house (α * β) <= house α * house β
参数：α β : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `norm_mul_le`：norm_mul_le (a b : α) : ‖a * b‖ <= ‖a‖ * ‖b‖
-/
theorem house_mul_le (α β : K) : house (α * β) ≤ house α * house β := by
  simp only [house, map_mul]; apply norm_mul_le
/-
**NumberField.house_prod_le** 是 Mathlib 中的一个引理，位于命名空间 `NumberField`。
形式化陈述：house_prod_le (s : Finset K) : house (∏ x in s, x) <= ∏ x in s, house x
参数：s : Finset K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_prod`：map_prod [CommMonoid M] [CommMonoid N] {G : Type*} [FunLike G 
M N] [MonoidHomClass G M N] (g : G) (f : ι -> M) (s : Finset ι) : g (∏ x in s,…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Finset.norm_prod_le`：Finset.norm_prod_le {α : Type*} [NormedCommRing α] 
[NormOneClass α] (s : Finset ι) (f : ι -> α) : ‖∏ i in s, f i‖ <= ∏ i in s, ‖f i
‖
· 使用定理 `NumberField.Embeddings.instNonemptyRingHom`：∀ (K : Type u_1) [inst : Fie
ld K] (A : Type u_2) [inst_1 : Field A] [CharZero A] [NumberField K] [IsAlgClose
d A],   Nonempty (K →+* A)
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
-/
lemma house_prod_le (s : Finset K) : house (∏ x ∈ s, x) ≤ ∏ x ∈ s, house x := by
  simpa [house, map_prod] using Finset.norm_prod_le _ _
/-
**NumberField.house_add_le** 是 Mathlib 中的一个定理，位于命名空间 `NumberField`。
形式化陈述：house_add_le (α β : K) : house (α + β) <= house α + house β
参数：α β : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `norm_add_le`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a b : E), ‖
a + b‖ ≤ ‖a‖ + ‖b‖
-/
theorem house_add_le (α β : K) : house (α + β) ≤ house α + house β := by
  simp only [house, map_add]; apply norm_add_le
/-
**NumberField.house_pow_le** 是 Mathlib 中的一个定理，位于命名空间 `NumberField`。
形式化陈述：house_pow_le (α : K) (i : Nat) : house (α ^ i) <= house α ^ i
参数：α : K；i : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `norm_pow_le`：norm_pow_le [NormOneClass α] (a : α) (n : Nat) : ‖a ^ n‖ <=
 ‖a‖ ^ n
· 使用定理 `NumberField.Embeddings.instNonemptyRingHom`：∀ (K : Type u_1) [inst : Fie
ld K] (A : Type u_2) [inst_1 : Field A] [CharZero A] [NumberField K] [IsAlgClose
d A],   Nonempty (K →+* A)
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
-/
theorem house_pow_le (α : K) (i : ℕ) : house (α ^ i) ≤ house α ^ i := by
  simpa only [house, map_pow] using norm_pow_le ((canonicalEmbedding K) α) i
/-
**NumberField.house_nat_mul** 是 Mathlib 中的一个定理，位于命名空间 `NumberField`。
形式化陈述：house_nat_mul (α : K) (c : Nat) : house (c * α) = c * house α
参数：α : K；c : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `Finset.univ_nonempty`：univ_nonempty [Nonempty α] : (univ : Finset α).Non
empty
· 使用定理 `NumberField.Embeddings.instNonemptyRingHom`：∀ (K : Type u_1) [inst : Fie
ld K] (A : Type u_2) [inst_1 : Field A] [CharZero A] [NumberField K] [IsAlgClose
d A],   Nonempty (K →+* A)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.house_eq_sup'`：house_eq_sup' (α : K) : house α = univ.sup' u
niv_nonempty (fun φ : K ->+* Complex => ‖φ α‖₊)
· 使用定理 `Finset.sup'_eq_sup`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeS
up α] [inst_1 : OrderBot α] {s : Finset β} (H : s.Nonempty)   (f : β → α), s.sup
' H f = …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNReal.coe_natCast`：∀ (n : ℕ), ↑↑n = ↑n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_natCast`：map_natCast [FunLike F R S] [RingHomClass F R S] (f : F) : 
forall n : Nat, f (n : R) = n
· 使用定理 `nnnorm_mul`：∀ {α : Type u_2} [inst : SeminormedAddCommGroup α] [inst_1 :
 Mul α] [NormMulClass α] (a b : α), ‖a * b‖₊ = ‖a‖₊ * ‖b‖₊
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用引理 `Complex.nnnorm_natCast`：nnnorm_natCast (n : Nat) : ‖(n : Complex)‖₊ = n
· 使用定理 `NNReal.mul_finset_sup`：mul_finset_sup {α} (r : Real>=0) (s : Finset α) (
f : α -> Real>=0) : r * s.sup f = s.sup fun a => r * f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem house_nat_mul (α : K) (c : ℕ) : house (c * α) = c * house α := by
  rw [house_eq_sup', house_eq_sup', Finset.sup'_eq_sup, Finset.sup'_eq_sup]
  norm_cast
  simp [NNReal.mul_finset_sup]
/-
**NumberField.house_intCast** 是 Mathlib 中的一个定理，位于命名空间 `NumberField`。
形式化陈述：∀ {K : Type u_1} [inst : Field K] [inst_1 : NumberField K] (x : ℤ), Number
Field.house ↑x = ↑|x|
参数：x : ℤ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_intCast`：map_intCast [FunLike F α β] [RingHomClass F α β] (f : F) (n
 : Int) : f n = n
· 使用定理 `pi_norm_const`：∀ {ι : Type u_1} {E : Type u_2} [inst : Fintype ι] [inst_
1 : SeminormedAddGroup E] [Nonempty ι] (a : E),   ‖fun _i => a‖ = ‖a‖
· 使用定理 `NumberField.Embeddings.instNonemptyRingHom`：∀ (K : Type u_1) [inst : Fie
ld K] (A : Type u_2) [inst_1 : Field A] [CharZero A] [NumberField K] [IsAlgClose
d A],   Nonempty (K →+* A)
· 使用引理 `Complex.norm_intCast`：norm_intCast (n : Int) : ‖(n : Complex)‖ = |(n : R
eal)|
· 使用引理 `Int.cast_abs`：cast_abs : (↑|a| : R) = |(a : R)|
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem house_intCast (x : ℤ) : house (x : K) = |x| := by
  simp only [house, map_intCast, Pi.intCast_def, pi_norm_const, Complex.norm_intCast, Int.cast_abs]

/-- Let `α` be a non-zero algebraic integer. Then `α` has a conjugate `σ α` with `‖σ α‖ ≥ 1`. -/
/-
**NumberField.exists_conjugate_one_le_norm** 是 Mathlib 中的一个引理，位于命名空间 `NumberFiel
d`。
形式化陈述：exists_conjugate_one_le_norm {α : 𝓞 K} (hα0 : α != 0) : exists σ : K ->+* 
Complex, 1 <= ‖σ α‖
参数：hα0 : α != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `NumberField.instNonemptyInfinitePlaceOfRingHomComplex`：∀ (K : Type u_1) 
[inst : Field K] [Nonempty (K →+* ℂ)], Nonempty (NumberField.InfinitePlace K)
· 使用定理 `NumberField.Embeddings.instNonemptyRingHom`：∀ (K : Type u_1) [inst : Fie
ld K] (A : Type u_2) [inst_1 : Field A] [CharZero A] [NumberField K] [IsAlgClose
d A],   Nonempty (K →+* A)
· 使用定理 `NumberField.InfinitePlace.one_le_of_lt_one`：one_le_of_lt_one {w : Infini
tePlace K} {a : (𝓞 K)} (ha : a != 0) (h : forall ⦃z⦄, z != w -> z a < 1) : 1 <= 
w a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.InfinitePlace.norm_embedding_eq`：norm_embedding_eq (w : Infi
nitePlace K) (x : K) : ‖(embedding w) x‖ = w x

--- 原说明 ---
Let `α` be a non-zero algebraic integer. Then `α` has a conjugate `σ α` with `‖σ
 α‖ ≥ 1`.
-/
lemma exists_conjugate_one_le_norm {α : 𝓞 K} (hα0 : α ≠ 0) :
    ∃ σ : K →+* ℂ, 1 ≤ ‖σ α‖ := by
  obtain ⟨w, hw⟩ : ∃ w : InfinitePlace K, 1 ≤ w α := by
    by_contra! h_neg
    let w₀ := Classical.arbitrary (InfinitePlace K)
    have h_ge_one : 1 ≤ w₀ α := InfinitePlace.one_le_of_lt_one hα0 (fun z _ ↦ h_neg z)
    exact (h_neg w₀).not_ge h_ge_one
  use w.embedding
  rwa [InfinitePlace.norm_embedding_eq]
/-
**NumberField.norm_embedding_le_house** 是 Mathlib 中的一个引理，位于命名空间 `NumberField`。
形式化陈述：norm_embedding_le_house (α : K) (σ : K ->+* Complex) : ‖σ α‖ <= house α
参数：α : K；σ : K ->+* Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `Finset.univ_nonempty`：univ_nonempty [Nonempty α] : (univ : Finset α).Non
empty
· 使用定理 `NumberField.Embeddings.instNonemptyRingHom`：∀ (K : Type u_1) [inst : Fie
ld K] (A : Type u_2) [inst_1 : Field A] [CharZero A] [NumberField K] [IsAlgClose
d A],   Nonempty (K →+* A)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.house_eq_sup'`：house_eq_sup' (α : K) : house α = univ.sup' u
niv_nonempty (fun φ : K ->+* Complex => ‖φ α‖₊)
· 使用定理 `Finset.le_sup'`：le_sup' {b : β} (h : b in s) : f b <= s.sup' ⟨b, h⟩ f
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
-/
lemma norm_embedding_le_house (α : K) (σ : K →+* ℂ) : ‖σ α‖ ≤ house α := by
  rw [house_eq_sup']
  exact Finset.le_sup' (f := (‖· α‖₊)) (Finset.mem_univ σ)

set_option backward.isDefEq.respectTransparency.types false in
/-
**NumberField.one_le_house_of_isIntegral** 是 Mathlib 中的一个引理，位于命名空间 `NumberField`
。
形式化陈述：one_le_house_of_isIntegral {α : K} (hα : IsIntegral Int α) (hα0 : α != 0) 
: 1 <= house α
参数：hα : IsIntegral Int α；hα0 : α != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `NumberField.exists_conjugate_one_le_norm`：exists_conjugate_one_le_norm {
α : 𝓞 K} (hα0 : α != 0) : exists σ : K ->+* Complex, 1 <= ‖σ α‖
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `NumberField.norm_embedding_le_house`：norm_embedding_le_house (α : K) (σ 
: K ->+* Complex) : ‖σ α‖ <= house α
-/
lemma one_le_house_of_isIntegral {α : K} (hα : IsIntegral ℤ α) (hα0 : α ≠ 0) :
    1 ≤ house α := by
  have ⟨σ, hσ⟩ : ∃ σ : K →+* ℂ, 1 ≤ ‖σ α‖ := by
    apply exists_conjugate_one_le_norm (K := K) (α := ⟨α, hα⟩)
    simpa [RingOfIntegers.ext_iff]
  apply hσ.trans (norm_embedding_le_house α σ)
/-
**NumberField.norm_norm_le_norm_mul_house_pow** 是 Mathlib 中的一个引理，位于命名空间 `NumberF
ield`。
形式化陈述：norm_norm_le_norm_mul_house_pow (α : K) (σ : K ->+* Complex) : ‖Algebra.no
rm Rat α‖ <= ‖σ α‖ * house α ^ (Module.finrank Rat K - 1)
参数：α : K；σ : K ->+* Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `NumberField.to_finiteDimensional`：∀ {K : Type u_1} {inst : Field K} [sel
f : NumberField K], FiniteDimensional ℚ K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.norm_eq_prod_embeddings`：norm_eq_prod_embeddings [Algebra.IsSepa
rable K L] [IsAlgClosed E] (x : L) : algebraMap K E (norm K x) = ∏ σ : L ->ₐ[K] 
E, σ x
· 使用定理 `Rat.norm_cast_real`：norm_cast_real (r : Rat) : ‖(r : Real)‖ = ‖r‖
· 使用定理 `Real.norm_eq_abs`：norm_eq_abs (r : Real) : ‖r‖ = |r|
· 使用定理 `eq_ratCast`：∀ {F : Type u_1} {α : Type u_3} [inst : DivisionRing α] [ins
t_1 : FunLike F ℚ α] [RingHomClass F ℚ α] (f : F) (q : ℚ),   f q = ↑q
· 使用引理 `Complex.norm_ratCast`：norm_ratCast (q : Rat) : ‖(q : Complex)‖ = |(q : R
eal)|
· 使用定理 `Finset.mul_prod_erase`：mul_prod_erase [DecidableEq ι] (s : Finset ι) (f 
: ι -> M) {a : ι} (h : a in s) : (f a * ∏ x in s.erase a, f x) = ∏ x in s, f x
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `Complex.norm_mul`：∀ (z w : ℂ), ‖z * w‖ = ‖z‖ * ‖w‖
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `Finset.norm_prod_le`：Finset.norm_prod_le {α : Type*} [NormedCommRing α] 
[NormOneClass α] (s : Finset ι) (f : ι -> α) : ‖∏ i in s, f i‖ <= ∏ i in s, ‖f i
‖
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用引理 `Finset.prod_le_prod`：prod_le_prod (h0 : forall i in s, 0 <= f i) (h1 : f
orall i in s, f i <= g i) : ∏ i in s, f i <= ∏ i in s, g i
· 使用引理 `NumberField.norm_embedding_le_house`：norm_embedding_le_house (α : K) (σ 
: K ->+* Complex) : ‖σ α‖ <= house α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.prod_const`：prod_const (b : M) : ∏ _x in s, b = b ^ #s
· 使用定理 `Finset.card_erase_of_mem`：card_erase_of_mem : a in s -> #(s.erase a) = #
s - 1
· 使用定理 `AlgHom.card`：AlgHom.card (K : Type*) [Field K] [IsAlgClosed K] [Algebra 
F K] : Fintype.card (E ->ₐ[F] K) = finrank F E
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma norm_norm_le_norm_mul_house_pow (α : K) (σ : K →+* ℂ) :
    ‖Algebra.norm ℚ α‖ ≤ ‖σ α‖ * house α ^ (Module.finrank ℚ K - 1) := by
  classical
  set σ' := σ.toRatAlgHom
  calc _ = ‖∏ τ : K →ₐ[ℚ] ℂ, τ α‖ := ?_
       _ = ‖(σ' α) * ∏ τ ∈ univ.erase σ', τ α‖ := by rw [mul_prod_erase univ (· α) (mem_univ σ')]
       _ ≤ ‖σ' α‖ * ∏ τ ∈ univ.erase σ', ‖τ α‖ := ?_
       _ ≤ ‖σ' α‖ * ∏ τ ∈ univ.erase σ', house α := by gcongr; apply norm_embedding_le_house
       _ = ‖σ' α‖ * house α ^ (Module.finrank ℚ K - 1) := by simp
  · rw [← Algebra.norm_eq_prod_embeddings, ← Rat.norm_cast_real,
      Real.norm_eq_abs, eq_ratCast, Complex.norm_ratCast]
  · rw [Complex.norm_mul]
    gcongr
    exact norm_prod_le (univ.erase σ') (· α)

end

end NumberField

namespace NumberField.house

noncomputable section

variable (K)

open Module.Free Module canonicalEmbedding Matrix Finset

attribute [local instance] Matrix.seminormedAddCommGroup

section DecidableEq

variable [DecidableEq (K →+* ℂ)]

set_option backward.privateInPublic true in
/-- `c` is defined as the product of the maximum absolute
  value of the entries of the inverse of the matrix `basisMatrix` and  `finrank ℚ K`. -/
/-
**NumberField.house.c** 是 Mathlib 中的一个定义，位于命名空间 `NumberField.house`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`c` is defined as the product of the maximum absolute
  value of the entries of the inverse of the matrix `basisMatrix` and  `finrank 
ℚ K`.
-/
private def c := (finrank ℚ K) * ‖((basisMatrix K).transpose)⁻¹‖
/-
**NumberField.house.c_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.house`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem c_nonneg : 0 ≤ c K := by
  rw [c]
  positivity

set_option backward.isDefEq.respectTransparency false in
set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**NumberField.house.basis_repr_norm_le_const_mul_house** 是 Mathlib 中的一个定理，位于命名空间
 `NumberField.house`。
形式化陈述：basis_repr_norm_le_const_mul_house (α : 𝓞 K) (i : K ->+* Complex) : ‖(((in
tegralBasis K).reindex (equivReindex K).symm).repr α i : Complex)‖ <= (c K) * ho
use (algebraMap (𝓞 K) K α)
参数：α : 𝓞 K；i : K ->+* Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `NumberField.RingOfIntegers.instFreeInt`：∀ (K : Type u_1) [inst : Field K
] [NumberField K], Module.Free ℤ (NumberField.RingOfIntegers K)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NumberField.inverse_basisMatrix_mulVec_eq_repr`：inverse_basisMatrix_mulV
ec_eq_repr [DecidableEq (K ->+* Complex)] (α : 𝓞 K) : forall i, ((basisMatrix K)
.transpose)⁻¹.mulVec (fun j => canon…
· 使用定理 `norm_sum_le_of_le`：∀ {ι : Type u_3} {E : Type u_5} [inst : SeminormedAdd
CommGroup E] (s : Finset ι) {f : ι → E} {n : ι → ℝ},   (∀ b ∈ s, ‖f b‖ ≤ n b) → 
‖∑ b ∈ …
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `norm_mul`：∀ {α : Type u_2} [inst : Norm α] [inst_1 : Mul α] [NormMulClas
s α] (a b : α), ‖a * b‖ = ‖a‖ * ‖b‖
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Finset.sum_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f g : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈
 s, f i…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `Matrix.norm_entry_le_entrywise_sup_norm`：norm_entry_le_entrywise_sup_nor
m (A : Matrix m n α) {i : m} {j : n} : ‖A i j‖ <= ‖A‖
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `norm_le_pi_norm`：∀ {ι : Type u_1} {G : ι → Type u_4} [inst : Fintype ι] 
[inst_1 : (i : ι) → SeminormedAddGroup (G i)] (f : (i : ι) → G i)   (i : ι), ‖f 
i‖ ≤ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `NumberField.Embeddings.card`：card : Fintype.card (K ->+* A) = finrank Ra
t K
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem basis_repr_norm_le_const_mul_house (α : 𝓞 K) (i : K →+* ℂ) :
    ‖(((integralBasis K).reindex (equivReindex K).symm).repr α i : ℂ)‖ ≤
      (c K) * house (algebraMap (𝓞 K) K α) := by
  let σ := canonicalEmbedding K
  calc
    _ ≤ ∑ j, ‖(basisMatrix K)ᵀ⁻¹ i j‖ * ‖σ (algebraMap (𝓞 K) K α) j‖ := by
      rw [← inverse_basisMatrix_mulVec_eq_repr]
      exact norm_sum_le_of_le _ fun _ _ ↦ (norm_mul _ _).le
    _ ≤ ∑ j, ‖((basisMatrix K).transpose)⁻¹‖ * ‖σ (algebraMap (𝓞 K) K α) j‖ := by
      gcongr
      exact norm_entry_le_entrywise_sup_norm ((basisMatrix K).transpose)⁻¹
    _ ≤ ∑ _ : K →+* ℂ, ‖fun i j => ((basisMatrix K).transpose)⁻¹ i j‖
        * house (algebraMap (𝓞 K) K α) := by
      gcongr with j
      exact norm_le_pi_norm (σ ((algebraMap (𝓞 K) K) α)) j
    _ = ↑(finrank ℚ K) * ‖((basisMatrix K).transpose)⁻¹‖ * house (algebraMap (𝓞 K) K α) := by
      simp [Embeddings.card, mul_assoc]

/-- `newBasis K` defines a reindexed basis of the ring of integers of `K`,
  adjusted by the inverse of the equivalence `equivReindex`. -/
/-
**NumberField.house.newBasis** 是 Mathlib 中的一个定义，位于命名空间 `NumberField.house`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`newBasis K` defines a reindexed basis of the ring of integers of `K`,
  adjusted by the inverse of the equivalence `equivReindex`.
-/
private def newBasis := (RingOfIntegers.basis K).reindex (equivReindex K).symm

/-- `supOfBasis K` calculates the supremum of the absolute values of
  the elements in `newBasis K`. -/
/-
**NumberField.house.supOfBasis** 是 Mathlib 中的一个定义，位于命名空间 `NumberField.house`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`supOfBasis K` calculates the supremum of the absolute values of
  the elements in `newBasis K`.
-/
private def supOfBasis : ℝ := univ.sup' univ_nonempty
  fun r ↦ house (algebraMap (𝓞 K) K (newBasis K r))

end DecidableEq

/-
**NumberField.house.supOfBasis_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.hou
se`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem supOfBasis_nonneg : 0 ≤ supOfBasis K := by
  simp only [supOfBasis, le_sup'_iff, mem_univ, and_self,
    exists_const, house_nonneg]

variable {α : Type*} {β : Type*} (a : Matrix α β (𝓞 K))

/-- `a' K a` returns the integer coefficients of the basis vector in the
  expansion of the product of an algebraic integer and a basis vectors. -/
/-
**NumberField.house.a'** 是 Mathlib 中的一个定义，位于命名空间 `NumberField.house`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`a' K a` returns the integer coefficients of the basis vector in the
  expansion of the product of an algebraic integer and a basis vectors.
-/
private def a' : α → β → (K →+* ℂ) → (K →+* ℂ) → ℤ := fun k l r =>
  (newBasis K).repr (a k l * (newBasis K) r)

set_option backward.privateInPublic true in
/-- `asiegel K a` is the integer matrix of the coefficients of the
product of matrix elements and basis vectors. -/
/-
**NumberField.house.asiegel** 是 Mathlib 中的一个定义，位于命名空间 `NumberField.house`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`asiegel K a` is the integer matrix of the coefficients of the
product of matrix elements and basis vectors.
-/
private def asiegel : Matrix (α × (K →+* ℂ)) (β × (K →+* ℂ)) ℤ := fun k l => a' K a k.1 l.1 l.2 k.2

variable (ha : a ≠ 0)

set_option backward.isDefEq.respectTransparency false in
include ha in
/-
**NumberField.house.asiegel_ne_0** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.house`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem asiegel_ne_0 : asiegel K a ≠ 0 := by
  simp +unfoldPartialApp only [asiegel, a']
  simp only [ne_eq]
  rw [funext_iff]; intro hs
  simp only [Prod.forall] at hs
  apply ha
  rw [← Matrix.ext_iff]; intro k' l
  specialize hs k'
  let ⟨b⟩ := Fintype.card_pos_iff.1 (Fintype.card_pos (α := (K →+* ℂ)))
  have := ((newBasis K).repr.map_eq_zero_iff (x := (a k' l * (newBasis K) b))).1 <| by
    ext b'
    specialize hs b'
    rw [funext_iff] at hs
    simp only [Prod.forall] at hs
    apply hs
  simp only [mul_eq_zero] at this
  exact this.resolve_right (Basis.ne_zero (newBasis K) b)

variable {p q : ℕ} (h0p : 0 < p) (hpq : p < q) (x : β × (K →+* ℂ) → ℤ) (hxl : x ≠ 0)

/-- `ξ` is the product of `x (l, r)` and the `r`-th basis element of the newBasis of `K`. -/
/-
**NumberField.house.** 是 Mathlib 中的一个定义，位于命名空间 `NumberField.house`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ξ` is the product of `x (l, r)` and the `r`-th basis element of the newBasis of
 `K`.
-/
private def ξ : β → 𝓞 K := fun l => ∑ r : K →+* ℂ, x (l, r) * (newBasis K r)

set_option backward.privateInPublic true in
include hxl in
/-
**NumberField.house.** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.house`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem ξ_ne_0 : ξ K x ≠ 0 := by
  intro H
  apply hxl
  ext ⟨l, r⟩
  rw [funext_iff] at H
  have hblin := Basis.linearIndependent (newBasis K)
  simp only [zsmul_eq_mul, Fintype.linearIndependent_iff] at hblin
  exact hblin (fun r ↦ x (l, r)) (H _) r
/-
**NumberField.house.lin_1** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.house`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem lin_1 (l k r) : a k l * (newBasis K) r =
    ∑ u, (a' K a k l r u) * (newBasis K) u := by
  simp only [Basis.sum_repr (newBasis K) (a k l * (newBasis K) r), a', ← zsmul_eq_mul]

-- Variable declarations can only reference public items.
set_option backward.privateInPublic true
variable [Fintype β] (cardβ : Fintype.card β = q) (hmulvec0 : asiegel K a *ᵥ x = 0)

include hxl hmulvec0 in
/-
**NumberField.house.** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.house`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem ξ_mulVec_eq_0 : a *ᵥ ξ K x = 0 := by
  funext k; simp only [Pi.zero_apply]; rw [eq_comm]
  have lin_0 : ∀ u, ∑ r, ∑ l, (a' K a k l r u * x (l, r) : 𝓞 K) = 0 := by
    intro u
    have hξ := ξ_ne_0 K x hxl
    rw [Ne, funext_iff, not_forall] at hξ
    rcases hξ with ⟨l, hξ⟩
    rw [funext_iff] at hmulvec0
    specialize hmulvec0 ⟨k, u⟩
    simp only [Fintype.sum_prod_type, mulVec, dotProduct, asiegel] at hmulvec0
    rw [sum_comm] at hmulvec0
    exact mod_cast hmulvec0
  have : 0 = ∑ u, (∑ r, ∑ l, a' K a k l r u * x (l, r) : 𝓞 K) * (newBasis K) u := by
    simp only [lin_0, zero_mul, sum_const_zero]
  have : 0 = ∑ r, ∑ l, x (l, r) * ∑ u, a' K a k l r u * (newBasis K) u := by
    conv at this => enter [2, 2, u]; rw [sum_mul]
    rw [sum_comm] at this
    rw [this]; congr 1; ext1 r
    conv => enter [1, 2, l]; rw [sum_mul]
    rw [sum_comm]; congr 1; ext1 r
    rw [mul_sum]; congr 1; ext1 r
    ring
  rw [sum_comm] at this
  rw [this]; congr 1; ext1 l
  rw [ξ, mul_sum]; congr 1; ext1 l
  rw [← lin_1]; ring

variable {A : ℝ} (habs : ∀ k l, (house ((algebraMap (𝓞 K) K) (a k l))) ≤ A)

variable [DecidableEq (K →+* ℂ)]

/-- `c₂` is the product of the maximum of `1` and `c`, and `supOfBasis`. -/
/-
**NumberField.house.c** 是 Mathlib 中的一个缩写定义，位于命名空间 `NumberField.house`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`c₂` is the product of the maximum of `1` and `c`, and `supOfBasis`.
-/
private abbrev c₂ := max 1 (c K) * (supOfBasis K)
/-
**NumberField.house.c** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.house`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem c₂_nonneg : 0 ≤ c₂ K :=
  mul_nonneg (le_trans zero_le_one (le_max_left ..)) (supOfBasis_nonneg _)

variable [Fintype α] (cardα : Fintype.card α = p) (Apos : 0 ≤ A)
  (hxbound : ‖x‖ ≤ (q * finrank ℚ K * ‖asiegel K a‖) ^ ((p : ℝ) / (q - p)))

include habs Apos in
/-
**NumberField.house.asiegel_remark** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.house`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem asiegel_remark : ‖asiegel K a‖ ≤ c₂ K * A := by
  have := c_nonneg K
  rw [Matrix.norm_le_iff]
  · intro kr lu
    calc
      ‖asiegel K a kr lu‖ = |asiegel K a kr lu| := ?_
      _ ≤ c K * house ((algebraMap (𝓞 K) K) (a kr.1 lu.1 * ((newBasis K) lu.2))) := ?_
      _ ≤ c K * house ((algebraMap (𝓞 K) K) (a kr.1 lu.1)) *
        house ((algebraMap (𝓞 K) K) ((newBasis K) lu.2)) := ?_
      _ ≤ c K * A * house ((algebraMap (𝓞 K) K) ((newBasis K) lu.2)) := ?_
      _ ≤ c K * A * supOfBasis K := ?_
      _ ≤ c₂ K * A := ?_
    · simp only [Int.cast_abs, ← Real.norm_eq_abs (asiegel K a kr lu)]; rfl
    · have remark := basis_repr_norm_le_const_mul_house K
      simp only [Basis.repr_reindex, Finsupp.mapDomain_equiv_apply,
        integralBasis_repr_apply, eq_intCast, Rat.cast_intCast,
          Complex.norm_intCast] at remark
      exact mod_cast remark ((a kr.1 lu.1 * ((newBasis K) lu.2))) kr.2
    · simp only [house, map_mul, mul_assoc]
      gcongr
      apply norm_mul_le
    · rw [mul_assoc, mul_assoc]
      gcongr _ * (?_ * _)
      · apply house_nonneg
      · exact habs kr.1 lu.1
    · gcongr
      simp only [supOfBasis, le_sup'_iff, mem_univ]; use lu.2
    · rw [mul_right_comm, c₂]
      gcongr
      exacts [supOfBasis_nonneg _, le_max_right ..]
  · exact mul_nonneg (c₂_nonneg _) Apos

/-- `c₁ K` is the product of `finrank ℚ K` and  `c₂ K` and depends on `K`. -/
/-
**NumberField.house.c** 是 Mathlib 中的一个定义，位于命名空间 `NumberField.house`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`c₁ K` is the product of `finrank ℚ K` and  `c₂ K` and depends on `K`.
-/
private def c₁ := finrank ℚ K * c₂ K

include habs Apos hxbound hpq in
/-
**NumberField.house.house_le_bound** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.house`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem house_le_bound : ∀ l, house (ξ K x l).1 ≤ (c₁ K) *
    ((c₁ K * q * A) ^ ((p : ℝ) / (q - p))) := by
  let h := finrank ℚ K
  intro l
  have H₀ : 0 ≤ NumberField.house.supOfBasis K := supOfBasis_nonneg _
  have H₁ : 0 < (q - p : ℝ) := sub_pos.mpr <| mod_cast hpq
  calc _ = house (algebraMap (𝓞 K) K (∑ r, (x (l, r)) * ((newBasis K) r))) := rfl
       _ ≤ ∑ r, house (((algebraMap (𝓞 K) K) (x (l, r))) *
        ((algebraMap (𝓞 K) K) ((newBasis K) r))) := ?_
       _ ≤ ∑ r, ‖x (l, r)‖ * house ((algebraMap (𝓞 K) K) ((newBasis K) r)) := ?_
       _ ≤ ∑ r, ‖x (l, r)‖ * (supOfBasis K) := ?_
       _ ≤ ∑ _r : K →+* ℂ, ((↑q * h * ‖asiegel K a‖) ^ ((p : ℝ) / (q - p))) * supOfBasis K := ?_
       _ ≤ h * (c₂ K) * ((q * c₁ K * A) ^ ((p : ℝ) / (q - p))) := ?_
       _ ≤ c₁ K * ((c₁ K * ↑q * A) ^ ((p : ℝ) / (q - p))) := ?_
  · simp_rw [← map_mul, map_sum]; apply house_sum_le_sum_house
  · gcongr with r _; convert! house_mul_le ..
    simp only [map_intCast, house_intCast, Int.cast_abs, Int.norm_eq_abs]
  · unfold supOfBasis
    gcongr with r _
    simp only [le_sup'_iff, mem_univ, true_and]; use r
  · gcongr with r _
    exact le_trans (norm_le_pi_norm x ⟨l, r⟩) hxbound
  · simp only [sum_const, card_univ, nsmul_eq_mul]
    rw [Embeddings.card, mul_comm _ (supOfBasis K), c₂, c₁, ← mul_assoc,
      ← mul_assoc (q : ℝ), mul_assoc (q * _ : ℝ)]
    gcongr
    · exact le_mul_of_one_le_left (supOfBasis_nonneg K) (le_max_left ..)
    · exact asiegel_remark K a habs Apos
  · rw [mul_comm (q : ℝ) (c₁ K)]; rfl

set_option backward.privateInPublic.warn false in
include hpq h0p cardα cardβ ha habs in
/-- There exists a "small" non-zero algebraic integral solution of an
non-trivial underdetermined system of linear equations with algebraic integer coefficients. -/
/-
**NumberField.house.exists_ne_zero_int_vec_house_le** 是 Mathlib 中的一个定理，位于命名空间 `N
umberField.house`。
形式化陈述：exists_ne_zero_int_vec_house_le : exists (ξ : β -> 𝓞 K), ξ != 0 ∧ a *ᵥ ξ =
 0 ∧ forall l, house (ξ l).1 <= c₁ K * ((c₁ K * q * A) ^ ((p : Real) / (q - p)))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `mul_lt_mul_of_pos_right`：mul_lt_mul_of_pos_right [MulPosStrictMono α] (h
bc : b < c) (ha : 0 < a) : b * a < c * a
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `Module.finrank_pos`：Module.finrank_pos [IsDomain R] [IsTorsionFree R M] 
[h : Nontrivial M] : 0 < finrank R M
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `NumberField.to_finiteDimensional`：∀ {K : Type u_1} {inst : Field K} [sel
f : NumberField K], FiniteDimensional ℚ K
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_pos_iff`：mul_pos_iff [ExistsAddOfLE R] [PosMulStrictMono R] [MulPosS
trictMono R] [AddLeftStrictMono R] [AddLeftReflectLT R] : 0 < a * b ↔ 0 < a ∧ 0 
<…
· 使用定理 `StarOrderedRing.toExistsAddOfLE`：∀ {R : Type u_1} [inst : NonUnitalSemir
ing R] [inst_1 : PartialOrder R] [inst_2 : StarRing R] [StarOrderedRing R],   Ex
istsAddOfLE R
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Fintype.card_prod`：Fintype.card_prod (α β : Type*) [Fintype α] [Fintype 
β] : Fintype.card (α × β) = Fintype.card α * Fintype.card β
· 使用定理 `NumberField.Embeddings.card`：card : Fintype.card (K ->+* A) = finrank Ra
t K
· 使用定理 `Int.Matrix.exists_ne_zero_int_vec_norm_le'`：exists_ne_zero_int_vec_norm_
le' (hn : Fintype.card α < Fintype.card β) (hm : 0 < Fintype.card α) (hA : A != 
0) : exists t : β -> Int, t != 0…
· 使用定理 `_private.Mathlib.NumberTheory.NumberField.House.0.NumberField.house.asie
gel_ne_0`：∀ (K : Type u_1) [inst : Field K] [inst_1 : NumberField K] {α : Type u
_2} {β : Type u_3}   (a : Matrix α β (NumberField.RingOfIntegers K)), …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Fintype.card_pos_iff`：card_pos_iff : 0 < card α ↔ Nonempty α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `NumberField.house_nonneg`：house_nonneg (α : K) : 0 <= house α
· 使用定理 `_private.Mathlib.NumberTheory.NumberField.House.0.NumberField.house.ξ_ne
_0`：∀ (K : Type u_1) [inst : Field K] [inst_1 : NumberField K] {β : Type u_3} (x
 : β × (K →+* ℂ) → ℤ),   x ≠ 0 → NumberField.house.ξ✝ K x ≠ 0
· 使用定理 `_private.Mathlib.NumberTheory.NumberField.House.0.NumberField.house.ξ_mu
lVec_eq_0`：∀ (K : Type u_1) [inst : Field K] [inst_1 : NumberField K] {α : Type 
u_2} {β : Type u_3}   (a : Matrix α β (NumberField.RingOfIntegers K)) (…
（共 40 条，此处仅展示前 30 条）

--- 原说明 ---
There exists a "small" non-zero algebraic integral solution of an
non-trivial underdetermined system of linear equations with algebraic integer co
efficients.
-/
theorem exists_ne_zero_int_vec_house_le :
    ∃ (ξ : β → 𝓞 K), ξ ≠ 0 ∧ a *ᵥ ξ = 0 ∧
    ∀ l, house (ξ l).1 ≤ c₁ K * ((c₁ K * q * A) ^ ((p : ℝ) / (q - p))) := by
  let h := finrank ℚ K
  have hphqh : p * h < q * h := by gcongr; exact finrank_pos
  have h0ph : 0 < p * h := by rw [mul_pos_iff]; constructor; exact ⟨h0p, finrank_pos⟩
  have hfinp : Fintype.card (α × (K →+* ℂ)) = p * h := by
    rw [Fintype.card_prod, cardα, Embeddings.card]
  have hfinq : Fintype.card (β × (K →+* ℂ)) = q * h := by
    rw [Fintype.card_prod, cardβ, Embeddings.card]
  have ⟨x, hxl, hmulvec0, hxbound⟩ :=
    Int.Matrix.exists_ne_zero_int_vec_norm_le' (asiegel K a)
      (by rwa [hfinp, hfinq]) (by rwa [hfinp]) (asiegel_ne_0 K a ha)
  simp only [hfinp, hfinq, Nat.cast_mul] at hmulvec0 hxbound
  rw [← sub_mul, mul_div_mul_right _ _ (mod_cast finrank_pos.ne')] at hxbound
  have Apos : 0 ≤ A := by
    have ⟨k⟩ := Fintype.card_pos_iff.1 (cardα ▸ h0p)
    have ⟨l⟩ := Fintype.card_pos_iff.1 (cardβ ▸ h0p.trans hpq)
    exact le_trans (house_nonneg _) (habs k l)
  use ξ K x, ξ_ne_0 K x hxl, ξ_mulVec_eq_0 K a x hxl hmulvec0,
    house_le_bound K a hpq x habs Apos hxbound

end

end NumberField.house

