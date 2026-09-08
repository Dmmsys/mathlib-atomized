/-
Copyright (c) 2024 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
module

public import Mathlib.Data.Finsupp.WellFounded
public import Mathlib.RingTheory.MvPowerSeries.LexOrder
public import Mathlib.RingTheory.MvPowerSeries.Order

/-! # ZeroDivisors in a MvPowerSeries ring

- `mem_nonZeroDivisors_of_constantCoeff` proves that
  a multivariate power series whose constant coefficient is not a zero divisor
  is itself not a zero divisor


- `MvPowerSeries.order_mul` : multiplicativity of `MvPowerSeries.order`
  if the semiring `R` has no zero divisors

## Instance

If `R` has `NoZeroDivisors`, then so does `MvPowerSeries σ R`.


## TODO

* Transfer/adapt these results to `HahnSeries`.

## Remark

The analogue of `Polynomial.notMem_nonZeroDivisors_iff`
(McCoy theorem) holds for power series over a Noetherian ring,
but not in general. See [Fields1971]
-/

public section

noncomputable section

open Finset (antidiagonal mem_antidiagonal)

namespace MvPowerSeries

open Finsupp nonZeroDivisors

variable {σ R : Type*}

section Semiring

variable [Semiring R]

/-
**MvPowerSeries.mem_nonZeroDivisorsRight_of_constantCoeff** 是 Mathlib 中的一个定理，位于命
名空间 `MvPowerSeries`。
形式化陈述：mem_nonZeroDivisorsRight_of_constantCoeff {φ : MvPowerSeries σ R} (hφ : co
nstantCoeff φ in nonZeroDivisorsRight R) : φ in nonZeroDivisorsRight (MvPowerSer
ies σ R)
参数：hφ : constantCoeff φ in nonZeroDivisorsRight R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.ext`：ext {φ ψ : MvPowerSeries σ R} (h : forall n : σ ->₀ N
at, coeff n φ = coeff n ψ) : φ = ψ
· 使用定理 `WellFoundedLT.induction`：induction {motive : α -> Prop} (a : α) (ind : f
orall x, (forall y, y < x -> motive y) -> motive x) : motive a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `instWellFoundedLTNat`：WellFoundedLT ℕ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_right_mem_nonZeroDivisorsRight_eq_zero_iff`：mul_right_mem_nonZeroDiv
isorsRight_eq_zero_iff (hr : r in nonZeroDivisorsRight M₀) : x * r = 0 ↔ x = 0
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Finset.sum_eq_single`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] {s : Finset ι} {f : ι → M} (a : ι),   (∀ b ∈ s, b ≠ a → f b = 0) → (a ∉ s
 → f a = 0…
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.HasAntidiagonal.mem_antidiagonal`：∀ {A : Type u_1} {inst : AddMon
oid A} [self : Finset.HasAntidiagonal A] {n : A} {a : A × A},   a ∈ Finset.HasAn
tidiagonal.antidiagonal n ↔ a…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `Finsupp.instIsBotZeroClass`：∀ {ι : Type u_1} {α : Type u_3} [inst : AddC
ommMonoid α] [inst_1 : PartialOrder α] [IsBotZeroClass α],   IsBotZeroClass (ι →
₀ α)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `instIsEmptyFalse`：IsEmpty False
（共 32 条，此处仅展示前 30 条）
-/
theorem mem_nonZeroDivisorsRight_of_constantCoeff {φ : MvPowerSeries σ R}
    (hφ : constantCoeff φ ∈ nonZeroDivisorsRight R) :
    φ ∈ nonZeroDivisorsRight (MvPowerSeries σ R) := by
  classical
  intro x hx
  ext d
  apply WellFoundedLT.induction d
  intro e he
  rw [map_zero, ← mul_right_mem_nonZeroDivisorsRight_eq_zero_iff hφ,
    ← map_zero (f := coeff e), ← hx]
  convert! (coeff_mul e x φ).symm
  rw [Finset.sum_eq_single (e, 0), coeff_zero_eq_constantCoeff]
  · rintro ⟨u, _⟩ huv _
    suffices u < e by simp only [he u this, zero_mul, map_zero]
    apply lt_of_le_of_ne
    · simp only [← mem_antidiagonal.mp huv, le_add_iff_nonneg_right, zero_le]
    · rintro rfl
      simp_all
  · simp

-- TODO: derive from `mem_nonZeroDivisorsRight_of_constantCoeff` using `MulOpposite`
/-
**MvPowerSeries.mem_nonZeroDivisorsLeft_of_constantCoeff** 是 Mathlib 中的一个定理，位于命名
空间 `MvPowerSeries`。
形式化陈述：mem_nonZeroDivisorsLeft_of_constantCoeff {φ : MvPowerSeries σ R} (hφ : con
stantCoeff φ in nonZeroDivisorsLeft R) : φ in nonZeroDivisorsLeft (MvPowerSeries
 σ R)
参数：hφ : constantCoeff φ in nonZeroDivisorsLeft R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.ext`：ext {φ ψ : MvPowerSeries σ R} (h : forall n : σ ->₀ N
at, coeff n φ = coeff n ψ) : φ = ψ
· 使用定理 `WellFoundedLT.induction`：induction {motive : α -> Prop} (a : α) (ind : f
orall x, (forall y, y < x -> motive y) -> motive x) : motive a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `instWellFoundedLTNat`：WellFoundedLT ℕ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_left_mem_nonZeroDivisorsLeft_eq_zero_iff`：mul_left_mem_nonZeroDiviso
rsLeft_eq_zero_iff (hr : r in nonZeroDivisorsLeft M₀) : r * x = 0 ↔ x = 0
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Finset.sum_eq_single`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] {s : Finset ι} {f : ι → M} (a : ι),   (∀ b ∈ s, b ≠ a → f b = 0) → (a ∉ s
 → f a = 0…
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.HasAntidiagonal.mem_antidiagonal`：∀ {A : Type u_1} {inst : AddMon
oid A} [self : Finset.HasAntidiagonal A] {n : A} {a : A × A},   a ∈ Finset.HasAn
tidiagonal.antidiagonal n ↔ a…
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsRightCancelAdd.addRightReflectLE_of_addRightReflectLT`：∀ (N : Type u_2
) [inst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightReflect
LT N],   AddRightReflectLE N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLT`：∀ {α : Type u_1} [inst : Ad
dCommMonoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], AddLeftRe
flectLT α
· 使用定理 `Finsupp.instIsBotZeroClass`：∀ {ι : Type u_1} {α : Type u_3} [inst : AddC
ommMonoid α] [inst_1 : PartialOrder α] [IsBotZeroClass α],   IsBotZeroClass (ι →
₀ α)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
（共 37 条，此处仅展示前 30 条）
-/
theorem mem_nonZeroDivisorsLeft_of_constantCoeff {φ : MvPowerSeries σ R}
    (hφ : constantCoeff φ ∈ nonZeroDivisorsLeft R) :
    φ ∈ nonZeroDivisorsLeft (MvPowerSeries σ R) := by
  classical
  intro x hx
  ext d
  apply WellFoundedLT.induction d
  intro e he
  rw [map_zero, ← mul_left_mem_nonZeroDivisorsLeft_eq_zero_iff hφ,
    ← map_zero (f := coeff e), ← hx]
  convert! (coeff_mul e φ x).symm
  rw [Finset.sum_eq_single (0, e), coeff_zero_eq_constantCoeff]
  · rintro ⟨_, u⟩ huv _
    suffices u < e by simp only [he u this, mul_zero, map_zero]
    apply lt_of_le_of_ne
    · simp only [← mem_antidiagonal.mp huv, le_add_iff_nonneg_left, zero_le]
    · rintro rfl
      simp_all
  · simp only [mem_antidiagonal, zero_add, not_true_eq_false, coeff_zero_eq_constantCoeff,
      false_implies]

/-- A multivariate power series is not a zero divisor
  when its constant coefficient is not a zero divisor -/
/-
**MvPowerSeries.mem_nonZeroDivisors_of_constantCoeff** 是 Mathlib 中的一个定理，位于命名空间 `
MvPowerSeries`。
形式化陈述：mem_nonZeroDivisors_of_constantCoeff {φ : MvPowerSeries σ R} (hφ : constan
tCoeff φ in R⁰) : φ in (MvPowerSeries σ R)⁰
参数：hφ : constantCoeff φ in R⁰。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.mem_nonZeroDivisorsLeft_of_constantCoeff`：mem_nonZeroDivis
orsLeft_of_constantCoeff {φ : MvPowerSeries σ R} (hφ : constantCoeff φ in nonZer
oDivisorsLeft R) : φ in nonZeroDivisorsLeft …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `MvPowerSeries.mem_nonZeroDivisorsRight_of_constantCoeff`：mem_nonZeroDivi
sorsRight_of_constantCoeff {φ : MvPowerSeries σ R} (hφ : constantCoeff φ in nonZ
eroDivisorsRight R) : φ in nonZeroDivisorsRig…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
A multivariate power series is not a zero divisor
  when its constant coefficient is not a zero divisor
-/
theorem mem_nonZeroDivisors_of_constantCoeff {φ : MvPowerSeries σ R}
    (hφ : constantCoeff φ ∈ R⁰) :
    φ ∈ (MvPowerSeries σ R)⁰ :=
  ⟨mem_nonZeroDivisorsLeft_of_constantCoeff hφ.1, mem_nonZeroDivisorsRight_of_constantCoeff hφ.2⟩
/-
**MvPowerSeries.monomial_mem_nonzeroDivisorsLeft** 是 Mathlib 中的一个引理，位于命名空间 `MvPo
werSeries`。
形式化陈述：monomial_mem_nonzeroDivisorsLeft {n : σ ->₀ Nat} {r} : monomial n r in non
ZeroDivisorsLeft (MvPowerSeries σ R) ↔ r in nonZeroDivisorsLeft R
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPowerSeries.monomial_zero_eq_C`：monomial_zero_eq_C : ⇑(monomial (R
· 使用定理 `MvPowerSeries.monomial_mul_monomial`：monomial_mul_monomial (m n : σ ->₀ 
Nat) (a b : R) : monomial m a * monomial n b = monomial (m + n) (a * b)
· 使用定理 `MvPowerSeries.ext`：ext {φ ψ : MvPowerSeries σ R} (h : forall n : σ ->₀ N
at, coeff n φ = coeff n ψ) : φ = ψ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `add_tsub_cancel_right`：add_tsub_cancel_right (a b : α) : a + b - b = a
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `le_add_self`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [CanonicallyO
rderedAdd α] {a b : α}, a ≤ b + a
· 使用定理 `Finsupp.instCanonicallyOrderedAddOfAddLeftMono`：∀ {ι : Type u_1} {α : Ty
pe u_3} [inst : AddCommMonoid α] [inst_1 : PartialOrder α] [CanonicallyOrderedAd
d α]   [inst_3 : Sub α] [OrderedSub …
· 使用定理 `MvPowerSeries.coeff_monomial_mul`：coeff_monomial_mul (a : R) : coeff m (
monomial n a * φ) = if n <= m then a * coeff (m - n) φ else 0
-/
lemma monomial_mem_nonzeroDivisorsLeft {n : σ →₀ ℕ} {r} :
    monomial n r ∈ nonZeroDivisorsLeft (MvPowerSeries σ R) ↔ r ∈ nonZeroDivisorsLeft R := by
  constructor
  · intro H s hrs
    have := H (C s) (by rw [← monomial_zero_eq_C, monomial_mul_monomial]; ext; simp [hrs])
    simpa using congr(coeff 0 $(this))
  · intro H p hrp
    ext i
    have := congr(coeff (i + n) $hrp)
    rw [coeff_monomial_mul, if_pos le_add_self, add_tsub_cancel_right] at this
    simpa using H _ this

-- TODO: reduce duplication
/-
**MvPowerSeries.monomial_mem_nonzeroDivisorsRight** 是 Mathlib 中的一个引理，位于命名空间 `MvP
owerSeries`。
形式化陈述：monomial_mem_nonzeroDivisorsRight {n : σ ->₀ Nat} {r} : monomial n r in no
nZeroDivisorsRight (MvPowerSeries σ R) ↔ r in nonZeroDivisorsRight R
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPowerSeries.monomial_zero_eq_C`：monomial_zero_eq_C : ⇑(monomial (R
· 使用定理 `MvPowerSeries.monomial_mul_monomial`：monomial_mul_monomial (m n : σ ->₀ 
Nat) (a b : R) : monomial m a * monomial n b = monomial (m + n) (a * b)
· 使用定理 `MvPowerSeries.ext`：ext {φ ψ : MvPowerSeries σ R} (h : forall n : σ ->₀ N
at, coeff n φ = coeff n ψ) : φ = ψ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `add_tsub_cancel_right`：add_tsub_cancel_right (a b : α) : a + b - b = a
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `le_add_self`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [CanonicallyO
rderedAdd α] {a b : α}, a ≤ b + a
· 使用定理 `Finsupp.instCanonicallyOrderedAddOfAddLeftMono`：∀ {ι : Type u_1} {α : Ty
pe u_3} [inst : AddCommMonoid α] [inst_1 : PartialOrder α] [CanonicallyOrderedAd
d α]   [inst_3 : Sub α] [OrderedSub …
· 使用定理 `MvPowerSeries.coeff_mul_monomial`：coeff_mul_monomial (a : R) : coeff m (
φ * monomial n a) = if n <= m then coeff (m - n) φ * a else 0
-/
lemma monomial_mem_nonzeroDivisorsRight {n : σ →₀ ℕ} {r} :
    monomial n r ∈ nonZeroDivisorsRight (MvPowerSeries σ R) ↔ r ∈ nonZeroDivisorsRight R := by
  constructor
  · intro H s hrs
    have := H (C s) (by rw [← monomial_zero_eq_C, monomial_mul_monomial]; ext; simp [hrs])
    simpa using congr(coeff 0 $(this))
  · intro H p hrp
    ext i
    have := congr(coeff (i + n) $hrp)
    rw [coeff_mul_monomial, if_pos le_add_self, add_tsub_cancel_right] at this
    simpa using H _ this
/-
**MvPowerSeries.monomial_mem_nonzeroDivisors** 是 Mathlib 中的一个引理，位于命名空间 `MvPowerS
eries`。
形式化陈述：monomial_mem_nonzeroDivisors {n : σ ->₀ Nat} {r} : monomial n r in (MvPowe
rSeries σ R)⁰ ↔ r in R⁰
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.and`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∧ b ↔ c ∧ d)
· 使用引理 `MvPowerSeries.monomial_mem_nonzeroDivisorsLeft`：monomial_mem_nonzeroDivi
sorsLeft {n : σ ->₀ Nat} {r} : monomial n r in nonZeroDivisorsLeft (MvPowerSerie
s σ R) ↔ r in nonZeroDivisorsLeft R
· 使用引理 `MvPowerSeries.monomial_mem_nonzeroDivisorsRight`：monomial_mem_nonzeroDiv
isorsRight {n : σ ->₀ Nat} {r} : monomial n r in nonZeroDivisorsRight (MvPowerSe
ries σ R) ↔ r in nonZeroDivisorsRight…
-/
lemma monomial_mem_nonzeroDivisors {n : σ →₀ ℕ} {r} :
    monomial n r ∈ (MvPowerSeries σ R)⁰ ↔ r ∈ R⁰ :=
  monomial_mem_nonzeroDivisorsLeft.and monomial_mem_nonzeroDivisorsRight
/-
**MvPowerSeries.X_mem_nonzeroDivisors** 是 Mathlib 中的一个引理，位于命名空间 `MvPowerSeries`。
形式化陈述：X_mem_nonzeroDivisors {i : σ} : X i in (MvPowerSeries σ R)⁰
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.X.eq_1`：∀ {σ : Type u_1} {R : Type u_2} [inst : Semiring R
] (s : σ),   MvPowerSeries.X s = (MvPowerSeries.monomial fun₀ | s => 1) 1
· 使用引理 `MvPowerSeries.monomial_mem_nonzeroDivisors`：monomial_mem_nonzeroDivisors
 {n : σ ->₀ Nat} {r} : monomial n r in (MvPowerSeries σ R)⁰ ↔ r in R⁰
· 使用定理 `Submonoid.one_mem`：∀ {M : Type u_1} [inst : MulOneClass M] (S : Submonoi
d M), 1 ∈ S
-/
lemma X_mem_nonzeroDivisors {i : σ} :
    X i ∈ (MvPowerSeries σ R)⁰ := by
  rw [X, monomial_mem_nonzeroDivisors]
  exact Submonoid.one_mem R⁰

end Semiring

variable [Semiring R] [NoZeroDivisors R]

/-
**MvPowerSeries.** 是 Mathlib 中的一个实例，位于命名空间 `MvPowerSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : NoZeroDivisors (MvPowerSeries σ R) where
  eq_zero_or_eq_zero_of_mul_eq_zero {φ ψ} h := by
    rcases exists_wellFoundedGT σ
    simpa only [← lexOrder_eq_top_iff_eq_zero, lexOrder_mul, WithTop.add_eq_top] using h
/-
**MvPowerSeries.weightedOrder_mul** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：weightedOrder_mul (w : σ -> Nat) (f g : MvPowerSeries σ R) : (f * g).weigh
tedOrder w = f.weightedOrder w + g.weightedOrder w
参数：w : σ -> Nat；f g : MvPowerSeries σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.instNoZeroDivisors`：∀ {σ : Type u_1} {R : Type u_2} [inst 
: Semiring R] [NoZeroDivisors R], NoZeroDivisors (MvPowerSeries σ R)
· 使用定理 `MvPowerSeries.weightedHomogeneousComponent_of_weightedOrder`：weightedHom
ogeneousComponent_of_weightedOrder {f : MvPowerSeries σ R} {p : Nat} (hf : p = f
.weightedOrder w) : f.weightedHomogeneousComponen…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `MvPowerSeries.ne_zero_iff_weightedOrder_finite`：ne_zero_iff_weightedOrde
r_finite : f != 0 ↔ (f.weightedOrder w).toNat = f.weightedOrder w
· 使用定理 `ENat.natCast_toNat`：∀ {n : ℕ∞}, n ≠ ⊤ → ↑n.toNat = n
· 使用定理 `ne_top_of_lt`：ne_top_of_lt (h : a < b) : a != ⊤
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `MvPowerSeries.weightedHomogeneousComponent_mul_of_le_weightedOrder`：weig
htedHomogeneousComponent_mul_of_le_weightedOrder {f g : MvPowerSeries σ R} {p q 
: Nat} (hf : p <= f.weightedOrder w) (hg : q <= g.weight…
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `MvPowerSeries.weightedHomogeneousComponent_of_lt_weightedOrder_eq_zero`：
weightedHomogeneousComponent_of_lt_weightedOrder_eq_zero {f : MvPowerSeries σ R}
 {p : Nat} (hf : p < f.weightedOrder w) : f.weightedHomogene…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `not_lt_top_iff`：not_lt_top_iff : ¬a < ⊤ ↔ a = ⊤
· 使用定理 `add_top`：add_top (a : α) : a + ⊤ = ⊤
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `top_add`：top_add (a : α) : ⊤ + a = ⊤
· 使用定理 `MvPowerSeries.le_weightedOrder_mul`：le_weightedOrder_mul : f.weightedOrd
er w + g.weightedOrder w <= weightedOrder w (f * g)
-/
theorem weightedOrder_mul (w : σ → ℕ) (f g : MvPowerSeries σ R) :
    (f * g).weightedOrder w = f.weightedOrder w + g.weightedOrder w := by
  apply le_antisymm _ (le_weightedOrder_mul w)
  by_cases hf : f.weightedOrder w < ⊤
  · by_cases hg : g.weightedOrder w < ⊤
    · let p := (f.weightedOrder w).toNat
      have hp : p = f.weightedOrder w := by
        simpa only [p, ENat.natCast_toNat_eq_self, ← lt_top_iff_ne_top]
      let q := (g.weightedOrder w).toNat
      have hq : q = g.weightedOrder w := by
        simpa only [q, ENat.natCast_toNat_eq_self, ← lt_top_iff_ne_top]
      have : f.weightedHomogeneousComponent w p * g.weightedHomogeneousComponent w q ≠ 0 := by
        simp only [ne_eq, mul_eq_zero]
        intro H
        rcases H with H | H <;>
        · refine weightedHomogeneousComponent_of_weightedOrder ?_ H
          simp only [ENat.natCast_toNat_eq_self, ne_eq, weightedOrder_eq_top_iff, p, q]
          rw [← ne_eq, ne_zero_iff_weightedOrder_finite w]
          exact ENat.natCast_toNat (ne_top_of_lt (by simpa))
      rw [← weightedHomogeneousComponent_mul_of_le_weightedOrder
          (le_of_eq hp) (le_of_eq hq)] at this
      rw [← hp, ← hq, ← Nat.cast_add, ← not_lt]
      intro H
      apply this
      apply weightedHomogeneousComponent_of_lt_weightedOrder_eq_zero H
    · rw [not_lt_top_iff] at hg
      simp [hg]
  · rw [not_lt_top_iff] at hf
    simp [hf]
/-
**MvPowerSeries.weightedOrder_prod** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：weightedOrder_prod {R : Type*} [CommSemiring R] [NoZeroDivisors R] [Nontri
vial R] {ι : Type*} (w : σ -> Nat) (f : ι -> MvPowerSeries σ R) (s : Finset ι) :
 (∏ i in s, f i).weightedOrder w = ∑ i in s, (f i).weightedOrder w
参数：w : σ -> Nat；f : ι -> MvPowerSeries σ R；s : Finset ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.cons_induction`：∀ {α : Type u_3} {motive : Finset α → Prop},   mo
tive ∅ → (∀ (a : α) (s : Finset α) (h : a ∉ s), motive s → motive (Finset.cons a
 s h)) → ∀ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.weightedOrder_one`：weightedOrder_one [Nontrivial R] : (1 :
 MvPowerSeries σ R).weightedOrder w = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.sum_cons`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι} 
[inst : AddCommMonoid M] {f : ι → M} (h : a ∉ s),   ∑ x ∈ Finset.cons a s h, f x
 = f …
· 使用定理 `Finset.prod_cons`：prod_cons (h : a ∉ s) : ∏ x in cons a s h, f x = f a *
 ∏ x in s, f x
· 使用定理 `MvPowerSeries.weightedOrder_mul`：weightedOrder_mul (w : σ -> Nat) (f g :
 MvPowerSeries σ R) : (f * g).weightedOrder w = f.weightedOrder w + g.weightedOr
der w
-/
theorem weightedOrder_prod {R : Type*} [CommSemiring R] [NoZeroDivisors R] [Nontrivial R]
    {ι : Type*} (w : σ → ℕ) (f : ι → MvPowerSeries σ R) (s : Finset ι) :
    (∏ i ∈ s, f i).weightedOrder w = ∑ i ∈ s, (f i).weightedOrder w := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih => rw [Finset.sum_cons ha, Finset.prod_cons ha, weightedOrder_mul, ih]
/-
**MvPowerSeries.order_mul** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：order_mul (f g : MvPowerSeries σ R) : (f * g).order = f.order + g.order
参数：f g : MvPowerSeries σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.weightedOrder_mul`：weightedOrder_mul (w : σ -> Nat) (f g :
 MvPowerSeries σ R) : (f * g).weightedOrder w = f.weightedOrder w + g.weightedOr
der w
-/
theorem order_mul (f g : MvPowerSeries σ R) :
    (f * g).order = f.order + g.order :=
  weightedOrder_mul _ f g
/-
**MvPowerSeries.order_prod** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：order_prod {R : Type*} [CommSemiring R] [NoZeroDivisors R] [Nontrivial R] 
{ι : Type*} (f : ι -> MvPowerSeries σ R) (s : Finset ι) : (∏ i in s, f i).order 
= ∑ i in s, (f i).order
参数：f : ι -> MvPowerSeries σ R；s : Finset ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.weightedOrder_prod`：weightedOrder_prod {R : Type*} [CommSe
miring R] [NoZeroDivisors R] [Nontrivial R] {ι : Type*} (w : σ -> Nat) (f : ι ->
 MvPowerSeries σ R) (s…
-/
theorem order_prod {R : Type*} [CommSemiring R] [NoZeroDivisors R] [Nontrivial R]
    {ι : Type*} (f : ι → MvPowerSeries σ R) (s : Finset ι) :
    (∏ i ∈ s, f i).order = ∑ i ∈ s, (f i).order := weightedOrder_prod _ _ _

end MvPowerSeries

end

