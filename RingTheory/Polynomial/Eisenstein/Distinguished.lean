/-
Copyright (c) 2024 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
public import Mathlib.RingTheory.PowerSeries.Order
/-!

# Distinguished polynomial

In this file we define the predicate `Polynomial.IsDistinguishedAt`
and develop the most basic lemmas about it.

-/

public section

open scoped Polynomial
open PowerSeries Ideal Quotient

variable {R : Type*} [CommRing R]

/--
Given an ideal `I` of a commutative ring `R`, we say that a polynomial `f : R[X]`
is *Distinguished at `I`* if `f` is monic and `IsWeaklyEisensteinAt I`.
i.e. `f` is of the form `xⁿ + a₁xⁿ⁻¹ + ⋯ + aₙ` with `aᵢ ∈ I` for all `i`.
-/
/-
**Polynomial.IsDistinguishedAt** 是 Mathlib 中的一个归纳类型，位于命名空间 `Polynomial`。
形式化陈述：{R : Type u_1} → [inst : CommRing R] → Polynomial R → Ideal R → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an ideal `I` of a commutative ring `R`, we say that a polynomial `f : R[X]
`
is *Distinguished at `I`* if `f` is monic and `IsWeaklyEisensteinAt I`.
i.e. `f` is of the form `xⁿ + a₁xⁿ⁻¹ + ⋯ + aₙ` with `aᵢ ∈ I` for all `i`.
-/
structure Polynomial.IsDistinguishedAt (f : R[X]) (I : Ideal R) : Prop
    extends f.IsWeaklyEisensteinAt I where
  monic : f.Monic

namespace Polynomial.IsDistinguishedAt

/-
**Polynomial.IsDistinguishedAt.mul** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial.IsDisti
nguishedAt`。
形式化陈述：mul {f f' : R[X]} {I : Ideal R} (hf : f.IsDistinguishedAt I) (hf' : f'.IsD
istinguishedAt I) : (f * f').IsDistinguishedAt I
参数：hf : f.IsDistinguishedAt I；hf' : f'.IsDistinguishedAt I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.IsWeaklyEisensteinAt.mul`：mul (hf : f.IsWeaklyEisensteinAt 𝓟)
 (hf' : f'.IsWeaklyEisensteinAt 𝓟) : (f * f').IsWeaklyEisensteinAt 𝓟
· 使用定理 `Polynomial.IsDistinguishedAt.toIsWeaklyEisensteinAt`：∀ {R : Type u_1} [i
nst : CommRing R] {f : Polynomial R} {I : Ideal R}, f.IsDistinguishedAt I → f.Is
WeaklyEisensteinAt I
· 使用定理 `Polynomial.Monic.mul`：∀ {R : Type u} [inst : Semiring R] {p q : Polynomi
al R}, p.Monic → q.Monic → (p * q).Monic
· 使用定理 `Polynomial.IsDistinguishedAt.monic`：∀ {R : Type u_1} [inst : CommRing R]
 {f : Polynomial R} {I : Ideal R}, f.IsDistinguishedAt I → f.Monic
-/
lemma mul {f f' : R[X]} {I : Ideal R} (hf : f.IsDistinguishedAt I) (hf' : f'.IsDistinguishedAt I) :
    (f * f').IsDistinguishedAt I :=
  ⟨hf.toIsWeaklyEisensteinAt.mul hf'.toIsWeaklyEisensteinAt, hf.monic.mul hf'.monic⟩
/-
**Polynomial.IsDistinguishedAt.map_eq_X_pow** 是 Mathlib 中的一个引理，位于命名空间 `Polynomia
l.IsDistinguishedAt`。
形式化陈述：map_eq_X_pow {f : R[X]} {I : Ideal R} (distinguish : f.IsDistinguishedAt I
) : f.map (Ideal.Quotient.mk I) = Polynomial.X ^ f.natDegree
参数：distinguish : f.IsDistinguishedAt I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.ext`：ext {p q : R[X]} : (forall n, coeff p n = coeff q n) -> 
p = q
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coeff_map`：coeff_map (n : Nat) : coeff (p.map f) n = f (coeff
 p n)
· 使用定理 `Polynomial.Monic.leadingCoeff`：∀ {R : Type u} [inst : Semiring R] {p : P
olynomial R}, p.Monic → p.leadingCoeff = 1
· 使用定理 `Polynomial.IsDistinguishedAt.monic`：∀ {R : Type u_1} [inst : CommRing R]
 {f : Polynomial R} {I : Ideal R}, f.IsDistinguishedAt I → f.Monic
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
· 使用定理 `Polynomial.coeff_X_pow`：coeff_X_pow (k n : Nat) : coeff (X ^ k : R[X]) n
 = if n = k then 1 else 0
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `lt_or_gt_of_ne`：lt_or_gt_of_ne (h : a != b) : a < b ∨ b < a
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Polynomial.IsWeaklyEisensteinAt.mem`：∀ {R : Type u} [inst : CommSemiring
 R] {f : Polynomial R} {𝓟 : Ideal R},   f.IsWeaklyEisensteinAt 𝓟 → ∀ {n : ℕ}, n 
< f.natDegree → f.coeff n…
· 使用定理 `Polynomial.IsDistinguishedAt.toIsWeaklyEisensteinAt`：∀ {R : Type u_1} [i
nst : CommRing R] {f : Polynomial R} {I : Ideal R}, f.IsDistinguishedAt I → f.Is
WeaklyEisensteinAt I
· 使用定理 `Polynomial.coeff_eq_zero_of_natDegree_lt`：coeff_eq_zero_of_natDegree_lt 
{p : R[X]} {n : Nat} (h : p.natDegree < n) : p.coeff n = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
-/
lemma map_eq_X_pow {f : R[X]} {I : Ideal R} (distinguish : f.IsDistinguishedAt I) :
    f.map (Ideal.Quotient.mk I) = Polynomial.X ^ f.natDegree := by
  ext i
  by_cases ne : i = f.natDegree
  · simp [ne, distinguish.monic]
  · rcases lt_or_gt_of_ne ne with lt | gt
    · simpa [ne, eq_zero_iff_mem] using (distinguish.mem lt)
    · simp [ne, Polynomial.coeff_eq_zero_of_natDegree_lt gt]

section degree_eq_order_map

variable {I : Ideal R} (f h : R⟦X⟧) {g : R[X]}

/-
**Polynomial.IsDistinguishedAt.map_ne_zero_of_eq_mul** 是 Mathlib 中的一个引理，位于命名空间 `
Polynomial.IsDistinguishedAt`。
形式化陈述：map_ne_zero_of_eq_mul (distinguish : g.IsDistinguishedAt I) (notMem : Powe
rSeries.constantCoeff h ∉ I) (eq : f = g * h) : f.map (Ideal.Quotient.mk I) != 0
参数：distinguish : g.IsDistinguishedAt I；notMem : PowerSeries.constantCoeff h ∉ I；
eq : f = g * h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
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
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Polynomial.IsDistinguishedAt.map_eq_X_pow`：map_eq_X_pow {f : R[X]} {I : 
Ideal R} (distinguish : f.IsDistinguishedAt I) : f.map (Ideal.Quotient.mk I) = P
olynomial.X ^ f.natDegree
· 使用引理 `Polynomial.polynomial_map_coe`：polynomial_map_coe {U V : Type*} [CommSem
iring U] [CommSemiring V] {φ : U ->+* V} {f : Polynomial U} : Polynomial.map φ f
 = PowerSeries.map …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.coe_pow`：coe_pow (n : Nat) : ((φ ^ n : R[X]) : PowerSeries R)
 = (φ : PowerSeries R) ^ n
· 使用定理 `Polynomial.coe_X`：coe_X : ((X : R[X]) : PowerSeries R) = PowerSeries.X
· 使用定理 `PowerSeries.coeff_X_pow_mul'`：coeff_X_pow_mul' (p : R⟦X⟧) (n d : Nat) : 
coeff d (X ^ n * p) = ite (n <= d) (coeff (d - n) p) 0
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `tsub_self`：tsub_self (a : α) : a - a = 0
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `PowerSeries.coeff_zero_eq_constantCoeff`：coeff_zero_eq_constantCoeff : ⇑
(coeff (R
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
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
lemma map_ne_zero_of_eq_mul (distinguish : g.IsDistinguishedAt I)
    (notMem : PowerSeries.constantCoeff h ∉ I) (eq : f = g * h) :
    f.map (Ideal.Quotient.mk I) ≠ 0 := fun H ↦ by
  have mapf : f.map (Ideal.Quotient.mk I) = (Polynomial.X ^ g.natDegree : (R ⧸ I)[X]) *
      h.map (Ideal.Quotient.mk I) := by
    simp [← map_eq_X_pow distinguish, eq]
  apply_fun PowerSeries.coeff g.natDegree at H
  simp [mapf, PowerSeries.coeff_X_pow_mul', eq_zero_iff_mem, notMem] at H
/-
**Polynomial.IsDistinguishedAt.degree_eq_coe_lift_order_map** 是 Mathlib 中的一个引理，位
于命名空间 `Polynomial.IsDistinguishedAt`。
形式化陈述：degree_eq_coe_lift_order_map (distinguish : g.IsDistinguishedAt I) (notMem
 : PowerSeries.constantCoeff h ∉ I) (eq : f = g * h) : g.degree = (f.map (Ideal.
Quotient.mk I)).order.lift (order_finite_iff_ne_zero.2 (distinguish.map_ne_zero_
of_eq_mul f h notMem eq))
参数：distinguish : g.IsDistinguishedAt I；notMem : PowerSeries.constantCoeff h ∉ I；
eq : f = g * h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `nontrivial_iff`：nontrivial_iff : Nontrivial α ↔ exists x y : α, x != y
· 使用定理 `ne_of_mem_of_not_mem`：∀ {α : Type u_1} {β : Type u_2} [inst : Membership
 α β] {s : β} {a b : α}, a ∈ s → b ∉ s → a ≠ b
· 使用定理 `Ideal.zero_mem`：∀ {α : Type u} [inst : Semiring α] (I : Ideal α), 0 ∈ I
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `PowerSeries.order_finite_iff_ne_zero`：order_finite_iff_ne_zero : (order 
φ < ⊤) ↔ φ != 0
· 使用引理 `Polynomial.IsDistinguishedAt.map_ne_zero_of_eq_mul`：map_ne_zero_of_eq_mu
l (distinguish : g.IsDistinguishedAt I) (notMem : PowerSeries.constantCoeff h ∉ 
I) (eq : f = g * h) : f.map (Ideal.Quoti…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.degree_eq_natDegree`：degree_eq_natDegree (hp : p != 0) : degr
ee p = (natDegree p : WithBot Nat)
· 使用定理 `Polynomial.Monic.ne_zero`：∀ {R : Type u} [inst : Semiring R] [Nontrivial
 R] {p : Polynomial R}, p.Monic → p ≠ 0
· 使用定理 `Polynomial.IsDistinguishedAt.monic`：∀ {R : Type u_1} [inst : CommRing R]
 {f : Polynomial R} {I : Ideal R}, f.IsDistinguishedAt I → f.Monic
· 使用定理 `Nat.cast_inj`：cast_inj {m n : Nat} : (m : R) = n ↔ m = n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENat.natCast_inj`：natCast_inj {a b : Nat} : (a : Nat∞) = b ↔ a = b
· 使用定理 `ENat.natCast_lift`：∀ (x : ℕ∞) (h : x < ⊤), ↑(x.lift h) = x
· 使用定理 `Eq.comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `PowerSeries.order_eq_nat`：order_eq_nat {φ : R⟦X⟧} {n : Nat} : order φ = 
n ↔ coeff n φ != 0 ∧ forall i, i < n -> coeff i φ = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
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
· 使用引理 `Polynomial.IsDistinguishedAt.map_eq_X_pow`：map_eq_X_pow {f : R[X]} {I : 
Ideal R} (distinguish : f.IsDistinguishedAt I) : f.map (Ideal.Quotient.mk I) = P
olynomial.X ^ f.natDegree
· 使用引理 `Polynomial.polynomial_map_coe`：polynomial_map_coe {U V : Type*} [CommSem
iring U] [CommSemiring V] {φ : U ->+* V} {f : Polynomial U} : Polynomial.map φ f
 = PowerSeries.map …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.coe_pow`：coe_pow (n : Nat) : ((φ ^ n : R[X]) : PowerSeries R)
 = (φ : PowerSeries R) ^ n
· 使用定理 `Polynomial.coe_X`：coe_X : ((X : R[X]) : PowerSeries R) = PowerSeries.X
· 使用定理 `PowerSeries.coeff_X_pow_mul'`：coeff_X_pow_mul' (p : R⟦X⟧) (n d : Nat) : 
coeff d (X ^ n * p) = ite (n <= d) (coeff (d - n) p) 0
（共 37 条，此处仅展示前 30 条）
-/
lemma degree_eq_coe_lift_order_map (distinguish : g.IsDistinguishedAt I)
    (notMem : PowerSeries.constantCoeff h ∉ I) (eq : f = g * h) :
    g.degree = (f.map (Ideal.Quotient.mk I)).order.lift
      (order_finite_iff_ne_zero.2 (distinguish.map_ne_zero_of_eq_mul f h notMem eq)) := by
  have : Nontrivial R := _root_.nontrivial_iff.mpr
    ⟨0, PowerSeries.constantCoeff h, ne_of_mem_of_not_mem I.zero_mem notMem⟩
  rw [Polynomial.degree_eq_natDegree distinguish.monic.ne_zero, Nat.cast_inj, ← ENat.natCast_inj,
    ENat.natCast_lift, Eq.comm, PowerSeries.order_eq_nat]
  have mapf : f.map (Ideal.Quotient.mk I) = (Polynomial.X ^ g.natDegree : (R ⧸ I)[X]) *
      h.map (Ideal.Quotient.mk I) := by
    simp [← map_eq_X_pow distinguish, eq]
  constructor
  · simp [mapf, PowerSeries.coeff_X_pow_mul', eq_zero_iff_mem, notMem]
  · intro i hi
    simp [mapf, PowerSeries.coeff_X_pow_mul', hi]
/-
**Polynomial.IsDistinguishedAt.coe_natDegree_eq_order_map** 是 Mathlib 中的一个引理，位于命
名空间 `Polynomial.IsDistinguishedAt`。
形式化陈述：coe_natDegree_eq_order_map (distinguish : g.IsDistinguishedAt I) (notMem :
 PowerSeries.constantCoeff h ∉ I) (eq : f = g * h) : g.natDegree = (f.map (Ideal
.Quotient.mk I)).order
参数：distinguish : g.IsDistinguishedAt I；notMem : PowerSeries.constantCoeff h ∉ I；
eq : f = g * h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.natDegree.eq_1`：∀ {R : Type u} [inst : Semiring R] (p : Polyn
omial R), p.natDegree = WithBot.unbotD 0 p.degree
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `PowerSeries.order_finite_iff_ne_zero`：order_finite_iff_ne_zero : (order 
φ < ⊤) ↔ φ != 0
· 使用引理 `Polynomial.IsDistinguishedAt.map_ne_zero_of_eq_mul`：map_ne_zero_of_eq_mu
l (distinguish : g.IsDistinguishedAt I) (notMem : PowerSeries.constantCoeff h ∉ 
I) (eq : f = g * h) : f.map (Ideal.Quoti…
· 使用引理 `Polynomial.IsDistinguishedAt.degree_eq_coe_lift_order_map`：degree_eq_coe
_lift_order_map (distinguish : g.IsDistinguishedAt I) (notMem : PowerSeries.cons
tantCoeff h ∉ I) (eq : f = g * h) : g.degree = …
· 使用定理 `ENat.natCast_lift`：∀ (x : ℕ∞) (h : x < ⊤), ↑(x.lift h) = x
-/
lemma coe_natDegree_eq_order_map (distinguish : g.IsDistinguishedAt I)
    (notMem : PowerSeries.constantCoeff h ∉ I) (eq : f = g * h) :
    g.natDegree = (f.map (Ideal.Quotient.mk I)).order := by
  rw [natDegree, distinguish.degree_eq_coe_lift_order_map f h notMem eq]
  exact ENat.natCast_lift _ <| order_finite_iff_ne_zero.2 <|
    distinguish.map_ne_zero_of_eq_mul f h notMem eq

end degree_eq_order_map

end Polynomial.IsDistinguishedAt

