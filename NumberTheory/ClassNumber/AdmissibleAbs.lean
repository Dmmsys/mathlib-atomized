/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.NumberTheory.ClassNumber.AdmissibleAbsoluteValue

/-!
# Admissible absolute value on the integers

This file defines an admissible absolute value `AbsoluteValue.absIsAdmissible`
which we use to show the class number of the ring of integers of a number field
is finite.

## Main results

* `AbsoluteValue.absIsAdmissible` shows the "standard" absolute value on `ℤ`,
  mapping negative `x` to `-x`, is admissible.
-/

@[expose] public section


namespace AbsoluteValue

open Int

/-- We can partition a finite family into `partition_card ε` sets, such that the remainders
in each set are close together. -/
/-
**AbsoluteValue.exists_partition_int** 是 Mathlib 中的一个定理，位于命名空间 `AbsoluteValue`。
形式化陈述：exists_partition_int (n : Nat) {ε : Real} (hε : 0 < ε) {b : Int} (hb : b !
= 0) (A : Fin n -> Int) : exists t : Fin n -> Fin ⌈1 / ε⌉₊, forall i₀ i₁, t i₀ =
 t i₁ -> ↑(abs (A i₁ % b - A i₀ % b)) < abs b • ε
参数：n : Nat；hε : 0 < ε；hb : b != 0；A : Fin n -> Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Int.cast_pos`：∀ {R : Type u_1} [inst : AddCommGroupWithOne R] [inst_1 : 
PartialOrder R] [AddLeftMono R] [ZeroLEOneClass R] [NeZero 1]   {n : ℤ}, 0 < ↑n 
↔ …
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `abs_pos`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LinearOrder α] [
AddLeftMono α] {a : α}, 0 < |a| ↔ a ≠ 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Int.floor_nonneg`：floor_nonneg : 0 <= ⌊a⌋ ↔ 0 <= a
· 使用引理 `div_nonneg`：div_nonneg (ha : 0 <= a) (hb : 0 <= b) : 0 <= a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `Int.cast_nonneg`：∀ {R : Type u_1} [inst : AddCommGroupWithOne R] [inst_1
 : PartialOrder R] [AddLeftMono R] [ZeroLEOneClass R] {n : ℤ},   0 ≤ n → 0 ≤ ↑n
· 使用定理 `Int.emod_nonneg`：∀ (a : ℤ) {b : ℤ}, b ≠ 0 → 0 ≤ a % b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.ofNat_lt`：∀ {n m : ℕ}, ↑n < ↑m ↔ n < m
· 使用定理 `Int.natAbs_of_nonneg`：∀ {a : ℤ}, 0 ≤ a → ↑a.natAbs = a
· 使用定理 `Int.floor_lt`：floor_lt : ⌊a⌋ < z ↔ a < z
· 使用定理 `eq_intCast`：eq_intCast [FunLike F Int α] [RingHomClass F Int α] (f : F) 
(n : Int) : f n = n
· 使用定理 `div_div`：div_div : a / b / c = a / (b * c)
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用引理 `div_lt_div_of_pos_right`：div_lt_div_of_pos_right (h : a < b) (hc : 0 < c
) : a / c < b / c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `div_lt_one`：div_lt_one (hb : 0 < b) : a / b < 1 ↔ a < b
· 使用定理 `Int.cast_lt`：∀ {R : Type u_1} [inst : AddCommGroupWithOne R] [inst_1 : P
artialOrder R] [AddLeftMono R] [ZeroLEOneClass R] [NeZero 1]   {m n : ℤ}, ↑m < ↑
n…
· 使用定理 `Int.emod_lt_abs`：emod_lt_abs (a : Int) {b : Int} (H : b != 0) : a % b < 
|b|
（共 43 条，此处仅展示前 30 条）

--- 原说明 ---
We can partition a finite family into `partition_card ε` sets, such that the rem
ainders
in each set are close together.
-/
theorem exists_partition_int (n : ℕ) {ε : ℝ} (hε : 0 < ε) {b : ℤ} (hb : b ≠ 0) (A : Fin n → ℤ) :
    ∃ t : Fin n → Fin ⌈1 / ε⌉₊,
    ∀ i₀ i₁, t i₀ = t i₁ → ↑(abs (A i₁ % b - A i₀ % b)) < abs b • ε := by
  have hb' : (0 : ℝ) < ↑(abs b) := Int.cast_pos.mpr (abs_pos.mpr hb)
  have hbε : 0 < abs b • ε := by
    rw [Algebra.smul_def]
    exact mul_pos hb' hε
  have hfloor : ∀ i, 0 ≤ floor ((A i % b : ℤ) / abs b • ε : ℝ) :=
    fun _ ↦ floor_nonneg.mpr (div_nonneg (cast_nonneg (emod_nonneg _ hb)) hbε.le)
  refine ⟨fun i ↦ ⟨natAbs (floor ((A i % b : ℤ) / abs b • ε : ℝ)), ?_⟩, ?_⟩
  · rw [← ofNat_lt, natAbs_of_nonneg (hfloor i), floor_lt, Algebra.smul_def, eq_intCast, ← div_div]
    apply lt_of_lt_of_le _ (Nat.le_ceil _)
    gcongr
    rw [div_lt_one hb', cast_lt]
    exact Int.emod_lt_abs _ hb
  intro i₀ i₁ hi
  have hi : (⌊↑(A i₀ % b) / abs b • ε⌋.natAbs : ℤ) = ⌊↑(A i₁ % b) / abs b • ε⌋.natAbs :=
    congr_arg ((↑) : ℕ → ℤ) (Fin.mk_eq_mk.mp hi)
  rw [natAbs_of_nonneg (hfloor i₀), natAbs_of_nonneg (hfloor i₁)] at hi
  have hi := abs_sub_lt_one_of_floor_eq_floor hi
  rw [abs_sub_comm, ← sub_div, abs_div, abs_of_nonneg hbε.le, div_lt_iff₀ hbε, one_mul] at hi
  rwa [Int.cast_abs, Int.cast_sub]

/-- `abs : ℤ → ℤ` is an admissible absolute value. -/
/-
**AbsoluteValue.absIsAdmissible** 是 Mathlib 中的一个定义，位于命名空间 `AbsoluteValue`。
形式化陈述：absIsAdmissible : IsAdmissible AbsoluteValue.abs
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AbsoluteValue.abs_isEuclidean`：AbsoluteValue.abs.IsEuclidean
· 使用定理 `AbsoluteValue.exists_partition_int`：exists_partition_int (n : Nat) {ε : 
Real} (hε : 0 < ε) {b : Int} (hb : b != 0) (A : Fin n -> Int) : exists t : Fin n
 -> Fin ⌈1 / ε⌉₊, forall…

--- 原说明 ---
`abs : ℤ → ℤ` is an admissible absolute value.
-/
noncomputable def absIsAdmissible : IsAdmissible AbsoluteValue.abs :=
  { AbsoluteValue.abs_isEuclidean with
    card := fun ε ↦ ⌈1 / ε⌉₊
    exists_partition' := fun n _ hε _ hb ↦ exists_partition_int n hε hb }
/-
**AbsoluteValue.** 是 Mathlib 中的一个实例，位于命名空间 `AbsoluteValue`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : Inhabited (IsAdmissible AbsoluteValue.abs) :=
  ⟨absIsAdmissible⟩

end AbsoluteValue

