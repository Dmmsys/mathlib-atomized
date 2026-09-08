/-
Copyright (c) 2026 Xavier Généreux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Généreux, María Inés de Frutos-Fernández
-/
module

public import Mathlib.RingTheory.Algebraic.Basic
public import Mathlib.RingTheory.Valuation.Basic


/-!
# Basic lemmas on valuations that are trivial over a base ring

This file contains additional results about `Valuation.IsTrivialOn` which is defined in
`Mathlib.RingTheory.Valuation.Basic`.

In what follows, we consider a `A`-algebra `B` and a valuation `v` over `B` which is trivial on `A`.

## Main results
* `valuation_aeval_eq_valuation_X_pow_natDegree_of_one_lt_valuation_X`: Let `p` be a polynomial
  over `A` evaluated at an element `w` of `B` for which `1 < v w`.
  We have the equality `v (p.aeval w) = v w ^ p.natDegree`.
* `Valuation.transcendental_of_ne_one`: If `y : B` is such that `y ≠ 0` and `v y ≠ 1`,
  then it is transcendental over `A`.
  Note that, in particular, this means that any non zero element of the
  maximal ideal of `v.valuationSubring` is transcendental over `A`.
-/

@[expose] public section

variable {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]

section Ring

variable {A : Type*} [CommSemiring A]
variable {B : Type*} [Ring B] [Algebra A B] {v : Valuation B Γ} [hv : v.IsTrivialOn A]

namespace Polynomial

/-
**Polynomial.valuation_aeval_monomial_eq_valuation_pow** 是 Mathlib 中的一个引理，位于命名空间
 `Polynomial`。
形式化陈述：valuation_aeval_monomial_eq_valuation_pow (w : B) (n : Nat) {a : A} (ha : 
a != 0) : v ((monomial n a).aeval w) = (v w) ^ n
参数：w : B；n : Nat；ha : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.aeval_C`：aeval_C (r : R) : aeval x (C r) = algebraMap R A r
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `Polynomial.aeval_X`：aeval_X : aeval x (X : R[X]) = x
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `Valuation.IsTrivialOn.eq_one`：∀ {Γ₀ : Type u_4} {inst : LinearOrderedCom
mMonoidWithZero Γ₀} {B : Type u_7} {A : Type u_8} {inst_1 : CommSemiring A}   {i
nst_2 : Ring B} {i…
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma valuation_aeval_monomial_eq_valuation_pow (w : B) (n : ℕ) {a : A} (ha : a ≠ 0) :
    v ((monomial n a).aeval w) = (v w) ^ n := by
  simp [← C_mul_X_pow_eq_monomial, map_mul, map_pow, one_mul, hv.eq_one a ha]
/-
**Polynomial.valuation_aeval_eq_valuation_X_pow_natDegree_of_one_lt_valuation_X*
* 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：valuation_aeval_eq_valuation_X_pow_natDegree_of_one_lt_valuation_X (w : B)
 (hpos : 1 < v w) {p : Polynomial A} (hp : p != 0) : v (p.aeval w) = v w ^ p.nat
Degree
参数：w : B；hpos : 1 < v w；hp : p != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Polynomial.valuation_aeval_monomial_eq_valuation_pow`：valuation_aeval_mo
nomial_eq_valuation_pow (w : B) (n : Nat) {a : A} (ha : a != 0) : v ((monomial n
 a).aeval w) = (v w) ^ n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.leadingCoeff_ne_zero`：leadingCoeff_ne_zero : leadingCoeff p !
= 0 ↔ p != 0
· 使用定理 `Polynomial.as_sum_range`：as_sum_range (p : R[X]) : p = ∑ i in range (p.n
atDegree + 1), monomial i (coeff p i)
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `Valuation.map_sum_eq_of_lt`：map_sum_eq_of_lt {ι : Type*} [DecidableEq ι]
 {s : Finset ι} {f : ι -> R} {j : ι} (hj : j in s) (hf : forall i in s \ {j}, v 
(f i) < v (f j))…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
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
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `Polynomial.aeval_C`：aeval_C (r : R) : aeval x (C r) = algebraMap R A r
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.aeval_X`：aeval_X : aeval x (X : R[X]) = x
（共 45 条，此处仅展示前 30 条）
-/
theorem valuation_aeval_eq_valuation_X_pow_natDegree_of_one_lt_valuation_X (w : B) (hpos : 1 < v w)
    {p : Polynomial A} (hp : p ≠ 0) : v (p.aeval w) = v w ^ p.natDegree := by
  rw [← valuation_aeval_monomial_eq_valuation_pow _ _ (leadingCoeff_ne_zero.mpr hp)]
  nth_rw 1 [as_sum_range p, map_sum]
  apply Valuation.map_sum_eq_of_lt _ (by simp)
  intro i hi
  simp only [Finset.mem_sdiff, Finset.mem_range, Nat.lt_add_one_iff, Finset.mem_singleton,
    ← lt_iff_le_and_ne] at hi
  simp only [← C_mul_X_pow_eq_monomial, map_mul, aeval_C, map_pow, aeval_X, coeff_natDegree]
  by_cases h0 : (p.coeff i) = 0
  · simp [hv.eq_one p.leadingCoeff (leadingCoeff_ne_zero.mpr hp),
      h0, pow_pos (lt_of_le_of_lt zero_le_one hpos) p.natDegree]
  · simp [hv.eq_one p.leadingCoeff (leadingCoeff_ne_zero.mpr hp),
      hv.eq_one _ h0, pow_lt_pow_right₀ hpos hi]

end Polynomial

end Ring

section Field

variable (A : Type*) [CommRing A]
variable {K : Type*} [Field K] [Algebra A K] {v : Valuation K Γ} [hv : v.IsTrivialOn A]

open Polynomial

/--
For an `A`-algebra `K` and a valuation `v` over `K` which is trivial on `A`.
If `y : K` is such that `y ≠ 0` and `v y ≠ 1`, then it is transcendental over `A`. -/
/-
**Valuation.transcendental_of_ne_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Valuation.transcendental_of_ne_one (y : K) (h0 : y != 0) (hy : v y != 1) :
 Transcendental A y
参数：y : K；h0 : y != 0；hy : v y != 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `IsAlgebraic.algebraMap`：∀ {R : Type u} {S : Type u_1} {A : Type v} [inst
 : CommRing R] [inst_1 : CommRing S] [inst_2 : Ring A]   [inst_3 : Algebra R A] 
[inst_4 : Al…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.valuation_aeval_eq_valuation_X_pow_natDegree_of_one_lt_valuat
ion_X`：valuation_aeval_eq_valuation_X_pow_natDegree_of_one_lt_valuation_X (w : B
) (hpos : 1 < v w) {p : Polynomial A} (hp : p != 0) : v (p.aeval w)…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `GroupWithZero.noZeroDivisors`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀
], NoZeroDivisors G₀
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `Transcendental.eq_1`：∀ (R : Type u) {A : Type v} [inst : CommRing R] [in
st_1 : Ring A] [inst_2 : Algebra R A] (x : A),   Transcendental R x = ¬IsAlgebra
ic R x
· 使用引理 `IsAlgebraic.inv_iff`：IsAlgebraic.inv_iff {K} [Field K] [Algebra R K] {x 
: K} : IsAlgebraic R (x⁻¹) ↔ IsAlgebraic R x
· 使用定理 `map_inv₀`：map_inv₀ : f a⁻¹ = (f a)⁻¹
· 使用定理 `Valuation.val_lt_one_iff`：val_lt_one_iff (v : Valuation K Γ₀) {x : K} (h
 : x != 0) : v x < 1 ↔ 1 < v x⁻¹
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b

--- 原说明 ---
For an `A`-algebra `K` and a valuation `v` over `K` which is trivial on `A`.
If `y : K` is such that `y ≠ 0` and `v y ≠ 1`, then it is transcendental over `A
`.
-/
theorem Valuation.transcendental_of_ne_one (y : K) (h0 : y ≠ 0) (hy : v y ≠ 1) :
    Transcendental A y := by
  wlog! hlt : 1 < v y generalizing y
  · rw [Transcendental, ← IsAlgebraic.inv_iff]
    apply this _ (by simpa) (by simpa)
    rw [← val_lt_one_iff _ h0]
    exact lt_of_le_of_ne hlt hy
  simp_all only [ne_eq, Transcendental]
  by_contra!
  replace ⟨p, hpnt, hp⟩ : IsAlgebraic A y := .algebraMap this
  suffices v y ^ p.natDegree = 0 by simp_all
  rw [← valuation_aeval_eq_valuation_X_pow_natDegree_of_one_lt_valuation_X _ hlt] <;> simp_all

end Field

