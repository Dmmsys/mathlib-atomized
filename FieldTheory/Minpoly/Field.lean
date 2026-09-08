/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca, Johan Commelin
-/
module

public import Mathlib.FieldTheory.Minpoly.Basic
public import Mathlib.RingTheory.Algebraic.Integral

/-!
# Minimal polynomials on an algebra over a field

This file specializes the theory of minpoly to the setting of field extensions
and derives some well-known properties, amongst which the fact that minimal polynomials
are irreducible, and uniquely determined by their defining property.

-/

@[expose] public section


open Polynomial Set Function minpoly

namespace minpoly

variable {A B : Type*}
variable (A) [Field A]

section Ring

variable [Ring B] [Algebra A B] (x : B)

/-- If an element `x` is a root of a nonzero polynomial `p`, then the degree of `p` is at least the
degree of the minimal polynomial of `x`. See also `minpoly.IsIntegrallyClosed.degree_le_of_ne_zero`
which relaxes the assumptions on `A` in exchange for stronger assumptions on `B`. -/
/-
**minpoly.degree_le_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `minpoly`。
形式化陈述：degree_le_of_ne_zero {p : A[X]} (pnz : p != 0) (hp : Polynomial.aeval x p 
= 0) : degree (minpoly A x) <= degree p
参数：pnz : p != 0；hp : Polynomial.aeval x p = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `minpoly.min`：min {p : A[X]} (pmonic : p.Monic) (hp : Polynomial.aeval x 
p = 0) : degree (minpoly A x) <= degree p
· 使用定理 `Polynomial.monic_mul_leadingCoeff_inv`：monic_mul_leadingCoeff_inv {p : K
[X]} (h : p != 0) : Monic (p * C (leadingCoeff p)⁻¹)
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
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.degree_mul_leadingCoeff_inv`：degree_mul_leadingCoeff_inv (p :
 K[X]) {q : K[X]} (h : q != 0) : degree (p * C (leadingCoeff q)⁻¹) = degree p

--- 原说明 ---
If an element `x` is a root of a nonzero polynomial `p`, then the degree of `p` 
is at least the
degree of the minimal polynomial of `x`. See also `minpoly.IsIntegrallyClosed.de
gree_le_of_ne_zero`
which relaxes the assumptions on `A` in exchange for stronger assumptions on `B`
.
-/
theorem degree_le_of_ne_zero {p : A[X]} (pnz : p ≠ 0) (hp : Polynomial.aeval x p = 0) :
    degree (minpoly A x) ≤ degree p :=
  calc
    degree (minpoly A x) ≤ degree (p * C (leadingCoeff p)⁻¹) :=
      min A x (monic_mul_leadingCoeff_inv pnz) (by simp [hp])
    _ = degree p := degree_mul_leadingCoeff_inv p pnz
/-
**minpoly.ne_zero_of_finite** 是 Mathlib 中的一个定理，位于命名空间 `minpoly`。
形式化陈述：ne_zero_of_finite (e : B) [FiniteDimensional A B] : minpoly A e != 0
参数：e : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `minpoly.ne_zero`：ne_zero [Nontrivial A] (hx : IsIntegral A x) : minpoly 
A x != 0
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `IsIntegral.of_finite`：IsIntegral.of_finite [Module.Finite R B] (x : B) :
 IsIntegral R x
-/
theorem ne_zero_of_finite (e : B) [FiniteDimensional A B] : minpoly A e ≠ 0 :=
  minpoly.ne_zero <| .of_finite A _

/-- The minimal polynomial of an element `x` is uniquely characterized by its defining property:
if there is another monic polynomial of minimal degree that has `x` as a root, then this polynomial
is equal to the minimal polynomial of `x`. See also `minpoly.IsIntegrallyClosed.Minpoly.unique`
which relaxes the assumptions on `A` in exchange for stronger assumptions on `B`. -/
/-
**minpoly.unique** 是 Mathlib 中的一个定理，位于命名空间 `minpoly`。
形式化陈述：unique {p : A[X]} (pmonic : p.Monic) (hp : Polynomial.aeval x p = 0) (pmin
 : forall q : A[X], q.Monic -> Polynomial.aeval x q = 0 -> degree p <= degree q)
 : p = minpoly A x
参数：pmonic : p.Monic；hp : Polynomial.aeval x p = 0；pmin : forall q : A[X], q.Moni
c -> Polynomial.aeval x q = 0 -> degree p <= degree q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_sub_eq_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a b : 
α}, a - b = 0 → a = b
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `minpoly.degree_le_of_ne_zero`：degree_le_of_ne_zero {p : A[X]} (pnz : p !
= 0) (hp : Polynomial.aeval x p = 0) : degree (minpoly A x) <= degree p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.aeval_sub`：aeval_sub {p q : R[X]} [Ring A] [Algebra R A] (x :
 A) : aeval x (p - q) = aeval x p - aeval x q
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `minpoly.aeval`：aeval : aeval x (minpoly A x) = 0
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.degree_sub_lt_left`：degree_sub_lt_left (hd : degree p = degre
e q) (hp0 : p != 0) (hlc : leadingCoeff p = leadingCoeff q) : degree (p - q) < d
egree p
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `minpoly.min`：min {p : A[X]} (pmonic : p.Monic) (hp : Polynomial.aeval x 
p = 0) : degree (minpoly A x) <= degree p
· 使用定理 `minpoly.monic`：monic (hx : IsIntegral A x) : Monic (minpoly A x)
· 使用定理 `minpoly.ne_zero`：ne_zero [Nontrivial A] (hx : IsIntegral A x) : minpoly 
A x != 0
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `Polynomial.Monic.leadingCoeff`：∀ {R : Type u} [inst : Semiring R] {p : P
olynomial R}, p.Monic → p.leadingCoeff = 1

--- 原说明 ---
The minimal polynomial of an element `x` is uniquely characterized by its defini
ng property:
if there is another monic polynomial of minimal degree that has `x` as a root, t
hen this polynomial
is equal to the minimal polynomial of `x`. See also `minpoly.IsIntegrallyClosed.
Minpoly.unique`
which relaxes the assumptions on `A` in exchange for stronger assumptions on `B`
.
-/
theorem unique {p : A[X]} (pmonic : p.Monic) (hp : Polynomial.aeval x p = 0)
    (pmin : ∀ q : A[X], q.Monic → Polynomial.aeval x q = 0 → degree p ≤ degree q) :
    p = minpoly A x := by
  have hx : IsIntegral A x := ⟨p, pmonic, hp⟩
  symm; apply eq_of_sub_eq_zero
  by_contra hnz
  apply degree_le_of_ne_zero A x hnz (by simp [hp]) |>.not_gt
  apply degree_sub_lt_left _ (minpoly.ne_zero hx)
  · rw [(monic hx).leadingCoeff, pmonic.leadingCoeff]
  · exact le_antisymm (min A x pmonic hp) (pmin (minpoly A x) (monic hx) (aeval A x))
/-
**minpoly.unique_of_degree_le_degree_minpoly** 是 Mathlib 中的一个定理，位于命名空间 `minpoly`
。
形式化陈述：unique_of_degree_le_degree_minpoly {p : A[X]} (pmonic : p.Monic) (hp : p.a
eval x = 0) (pmin : p.degree <= (minpoly A x).degree) : p = minpoly A x
参数：pmonic : p.Monic；hp : p.aeval x = 0；pmin : p.degree <= (minpoly A x).degree。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `minpoly.unique`：unique {p : A[X]} (pmonic : p.Monic) (hp : Polynomial.ae
val x p = 0) (pmin : forall q : A[X], q.Monic -> Polynomial.aeval x q = 0 -> deg
ree …
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `minpoly.min`：min {p : A[X]} (pmonic : p.Monic) (hp : Polynomial.aeval x 
p = 0) : degree (minpoly A x) <= degree p
-/
theorem unique_of_degree_le_degree_minpoly {p : A[X]} (pmonic : p.Monic) (hp : p.aeval x = 0)
    (pmin : p.degree ≤ (minpoly A x).degree) : p = minpoly A x :=
  unique _ _ pmonic hp fun _ qm hq ↦ pmin.trans <| min _ _ qm hq

/-- If an element `x` is a root of a polynomial `p`, then the minimal polynomial of `x` divides `p`.
See also `minpoly.isIntegrallyClosed_dvd` which relaxes the assumptions on `A` in exchange for
stronger assumptions on `B`. -/
/-
**minpoly.dvd** 是 Mathlib 中的一个定理，位于命名空间 `minpoly`。
形式化陈述：dvd {p : A[X]} (hp : Polynomial.aeval x p = 0) : minpoly A x ∣ p
参数：hp : Polynomial.aeval x p = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsAlgebraic.isIntegral`：∀ {K : Type u} {A : Type v} [inst : Field K] [in
st_1 : Ring A] [inst_2 : Algebra K A] {x : A},   IsAlgebraic K x → IsIntegral K 
x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.modByMonic_eq_zero_iff_dvd`：modByMonic_eq_zero_iff_dvd (hq : 
Monic q) : p %ₘ q = 0 ↔ q ∣ p
· 使用定理 `minpoly.monic`：monic (hx : IsIntegral A x) : Monic (minpoly A x)
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `minpoly.degree_le_of_ne_zero`：degree_le_of_ne_zero {p : A[X]} (pnz : p !
= 0) (hp : Polynomial.aeval x p = 0) : degree (minpoly A x) <= degree p
· 使用定理 `Polynomial.aeval_modByMonic_eq_self_of_root`：aeval_modByMonic_eq_self_of
_root [Algebra R S] {p q : R[X]} {x : S} (hx : aeval x q = 0) : aeval x (p %ₘ q)
 = aeval x p
· 使用定理 `minpoly.aeval`：aeval : aeval x (minpoly A x) = 0
· 使用定理 `Polynomial.degree_modByMonic_lt`：degree_modByMonic_lt [Nontrivial R] : f
orall (p : R[X]) {q : R[X]} (_hq : Monic q), degree (p %ₘ q) < degree q | p, q, 
hq => letI
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R

--- 原说明 ---
If an element `x` is a root of a polynomial `p`, then the minimal polynomial of 
`x` divides `p`.
See also `minpoly.isIntegrallyClosed_dvd` which relaxes the assumptions on `A` i
n exchange for
stronger assumptions on `B`.
-/
theorem dvd {p : A[X]} (hp : Polynomial.aeval x p = 0) : minpoly A x ∣ p := by
  by_cases hp0 : p = 0
  · simp only [hp0, dvd_zero]
  have hx : IsIntegral A x := IsAlgebraic.isIntegral ⟨p, hp0, hp⟩
  rw [← modByMonic_eq_zero_iff_dvd (monic hx)]
  by_contra hnz
  apply degree_le_of_ne_zero A x hnz
    ((aeval_modByMonic_eq_self_of_root (aeval _ _)).trans hp) |>.not_gt
  exact degree_modByMonic_lt _ (monic hx)

variable {A x} in
/-
**minpoly.dvd_iff** 是 Mathlib 中的一个引理，位于命名空间 `minpoly`。
形式化陈述：dvd_iff {p : A[X]} : minpoly A x ∣ p ↔ Polynomial.aeval x p = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `minpoly.aeval`：aeval : aeval x (minpoly A x) = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `minpoly.dvd`：dvd {p : A[X]} (hp : Polynomial.aeval x p = 0) : minpoly A 
x ∣ p
-/
lemma dvd_iff {p : A[X]} : minpoly A x ∣ p ↔ Polynomial.aeval x p = 0 :=
  ⟨fun ⟨q, hq⟩ ↦ by rw [hq, map_mul, aeval, zero_mul], minpoly.dvd A x⟩
/-
**minpoly.isRadical** 是 Mathlib 中的一个定理，位于命名空间 `minpoly`。
形式化陈述：isRadical [IsReduced B] : IsRadical (minpoly A x)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `minpoly.dvd_iff`：dvd_iff {p : A[X]} : minpoly A x ∣ p ↔ Polynomial.aeval
 x p = 0
· 使用定理 `IsReduced.eq_zero`：∀ {R : Type u_5} {inst : Zero R} {inst_1 : Pow R ℕ} [
self : IsReduced R] (x : R), IsNilpotent x → x = 0
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
-/
theorem isRadical [IsReduced B] : IsRadical (minpoly A x) := fun n p dvd ↦ by
  rw [dvd_iff] at dvd ⊢; rw [map_pow] at dvd; exact IsReduced.eq_zero _ ⟨n, dvd⟩
/-
**minpoly.dvd_map_of_isScalarTower** 是 Mathlib 中的一个定理，位于命名空间 `minpoly`。
形式化陈述：dvd_map_of_isScalarTower (A K : Type*) {R : Type*} [CommRing A] [Field K] 
[Ring R] [Algebra A K] [Algebra A R] [Algebra K R] [IsScalarTower A K R] (x : R)
 : minpoly K x ∣ (minpoly A x).map (algebraMap A K)
参数：A K : Type*；x : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `minpoly.dvd`：dvd {p : A[X]} (hp : Polynomial.aeval x p = 0) : minpoly A 
x ∣ p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.aeval_map_algebraMap`：aeval_map_algebraMap (x : B) (p : R[X])
 : aeval x (map (algebraMap R A) p) = aeval x p
· 使用定理 `minpoly.aeval`：aeval : aeval x (minpoly A x) = 0
-/
theorem dvd_map_of_isScalarTower (A K : Type*) {R : Type*} [CommRing A] [Field K] [Ring R]
    [Algebra A K] [Algebra A R] [Algebra K R] [IsScalarTower A K R] (x : R) :
    minpoly K x ∣ (minpoly A x).map (algebraMap A K) := by
  refine minpoly.dvd K x ?_
  rw [aeval_map_algebraMap, minpoly.aeval]
/-
**minpoly.dvd_map_of_isScalarTower'** 是 Mathlib 中的一个定理，位于命名空间 `minpoly`。
形式化陈述：dvd_map_of_isScalarTower' (R : Type*) {S : Type*} (K L : Type*) [CommRing 
R] [CommRing S] [Field K] [Ring L] [Algebra R S] [Algebra R K] [Algebra S L] [Al
gebra K L] [Algebra R L] [IsScalarTower R K L] [IsScalarTower R S L] (s : S) : m
inpoly K (algebraMap S L s) ∣ map (algebraMap R K) (minpoly R s)
参数：R : Type*；K L : Type*；s : S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `minpoly.dvd`：dvd {p : A[X]} (hp : Polynomial.aeval x p = 0) : minpoly A 
x ∣ p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.map_aeval_eq_aeval_map`：map_aeval_eq_aeval_map {S T U : Type*
} [Semiring S] [CommSemiring T] [Semiring U] [Algebra R S] [Algebra T U] {φ : R 
->+* T} {ψ : S ->+* U} …
· 使用定理 `IsScalarTower.algebraMap_eq`：algebraMap_eq : algebraMap R A = (algebraMa
p S A).comp (algebraMap R S)
· 使用定理 `minpoly.aeval`：aeval : aeval x (minpoly A x) = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
theorem dvd_map_of_isScalarTower' (R : Type*) {S : Type*} (K L : Type*) [CommRing R]
    [CommRing S] [Field K] [Ring L] [Algebra R S] [Algebra R K] [Algebra S L] [Algebra K L]
    [Algebra R L] [IsScalarTower R K L] [IsScalarTower R S L] (s : S) :
    minpoly K (algebraMap S L s) ∣ map (algebraMap R K) (minpoly R s) := by
  apply minpoly.dvd K (algebraMap S L s)
  rw [← map_aeval_eq_aeval_map, minpoly.aeval, map_zero]
  rw [← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq]

/-- If `y` is a conjugate of `x` over a field `K`, then it is a conjugate over a subring `R`. -/
/-
**minpoly.aeval_of_isScalarTower** 是 Mathlib 中的一个定理，位于命名空间 `minpoly`。
形式化陈述：aeval_of_isScalarTower (R : Type*) {K T U : Type*} [CommRing R] [Field K] 
[CommRing T] [Algebra R K] [Algebra K T] [Algebra R T] [IsScalarTower R K T] [Co
mmSemiring U] [Algebra K U] [Algebra R U] [IsScalarTower R K U] (x : T) (y : U) 
(hy : Polynomial.aeval y (minpoly K x) = 0) : Polynomial.aeval y (minpoly R x) =
 0
参数：R : Type*；x : T；y : U；hy : Polynomial.aeval y (minpoly K x) = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.eval₂_eq_zero_of_dvd_of_eval₂_eq_zero`：eval₂_eq_zero_of_dvd_o
f_eval₂_eq_zero (h : p ∣ q) (h0 : eval₂ f x p = 0) : eval₂ f x q = 0
· 使用定理 `minpoly.dvd_map_of_isScalarTower`：dvd_map_of_isScalarTower (A K : Type*)
 {R : Type*} [CommRing A] [Field K] [Ring R] [Algebra A K] [Algebra A R] [Algebr
a K R] [IsScalarTower …
· 使用定理 `Polynomial.aeval_map_algebraMap`：aeval_map_algebraMap (x : B) (p : R[X])
 : aeval x (map (algebraMap R A) p) = aeval x p

--- 原说明 ---
If `y` is a conjugate of `x` over a field `K`, then it is a conjugate over a sub
ring `R`.
-/
theorem aeval_of_isScalarTower (R : Type*) {K T U : Type*} [CommRing R] [Field K] [CommRing T]
    [Algebra R K] [Algebra K T] [Algebra R T] [IsScalarTower R K T] [CommSemiring U] [Algebra K U]
    [Algebra R U] [IsScalarTower R K U] (x : T) (y : U)
    (hy : Polynomial.aeval y (minpoly K x) = 0) : Polynomial.aeval y (minpoly R x) = 0 :=
  aeval_map_algebraMap K y (minpoly R x) ▸
    eval₂_eq_zero_of_dvd_of_eval₂_eq_zero (algebraMap K U) y
      (minpoly.dvd_map_of_isScalarTower R K x) hy

/-- If a subfield `F` of `E` contains all the coefficients of `minpoly E a`, then
`minpoly F a` maps to `minpoly E a` via `algebraMap F E`. -/
/-
**minpoly.map_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `minpoly`。
形式化陈述：map_algebraMap {F E A : Type*} [Field F] [Field E] [CommRing A] [Algebra F
 E] [Algebra E A] [Algebra F A] [IsScalarTower F E A] {a : A} (ha : IsIntegral F
 a) (h : minpoly E a in lifts (algebraMap F E)) : (minpoly F a).map (algebraMap 
F E) = minpoly E a
参数：ha : IsIntegral F a；h : minpoly E a in lifts (algebraMap F E)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Polynomial.eq_of_monic_of_dvd_of_natDegree_le`：eq_of_monic_of_dvd_of_nat
Degree_le {p q : R[X]} (hp : p.Monic) (hq : q.Monic) (hdvd : p ∣ q) (hdeg : q.na
tDegree <= p.natDegree) : q = p
· 使用定理 `minpoly.monic`：monic (hx : IsIntegral A x) : Monic (minpoly A x)
· 使用定理 `IsIntegral.tower_top`：IsIntegral.tower_top [Algebra A B] [IsScalarTower 
R A B] {x : B} (hx : IsIntegral R x) : IsIntegral A x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Function.Injective.monic_map_iff`：∀ {R : Type u} {S : Type v} [inst : Se
miring R] [inst_1 : Semiring S] {f : R →+* S},   Function.Injective ⇑f → ∀ {p : 
Polynomial R}, p.Monic…
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `minpoly.dvd`：dvd {p : A[X]} (hp : Polynomial.aeval x p = 0) : minpoly A 
x ∣ p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.aeval_map_algebraMap`：aeval_map_algebraMap (x : B) (p : R[X])
 : aeval x (map (algebraMap R A) p) = aeval x p
· 使用定理 `minpoly.aeval`：aeval : aeval x (minpoly A x) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.lifts_and_natDegree_eq_and_monic`：lifts_and_natDegree_eq_and_
monic {p : S[X]} (hlifts : p in lifts f) (hp : p.Monic) : exists q : R[X], map f
 q = p ∧ q.natDegree = p.natDegre…
· 使用定理 `Polynomial.natDegree_map`：natDegree_map (f : R ->+* S) : (p.map f).natDe
gree = p.natDegree
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Polynomial.natDegree_le_of_dvd`：natDegree_le_of_dvd (h1 : p ∣ q) (h2 : q
 != 0) : p.natDegree <= q.natDegree
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsScalarTower.algebraMap_eq`：algebraMap_eq : algebraMap R A = (algebraMa
p S A).comp (algebraMap R S)
· 使用定理 `Polynomial.coe_mapRingHom`：coe_mapRingHom (f : R ->+* S) : ⇑(mapRingHom 
f) = map f
· 使用定理 `Polynomial.mapRingHom_comp`：mapRingHom_comp [Semiring T] (f : S ->+* T) 
(g : R ->+* S) : (mapRingHom f).comp (mapRingHom g) = mapRingHom (f.comp g)
· 使用定理 `RingHom.comp_apply`：comp_apply (hnp : β ->+* γ) (hmn : α ->+* β) (x : α)
 : (hnp.comp hmn : α -> γ) x = hnp (hmn x)
· 使用定理 `Polynomial.Monic.ne_zero`：∀ {R : Type u} [inst : Semiring R] [Nontrivial
 R] {p : Polynomial R}, p.Monic → p ≠ 0

--- 原说明 ---
If a subfield `F` of `E` contains all the coefficients of `minpoly E a`, then
`minpoly F a` maps to `minpoly E a` via `algebraMap F E`.
-/
theorem map_algebraMap {F E A : Type*} [Field F] [Field E] [CommRing A]
    [Algebra F E] [Algebra E A] [Algebra F A] [IsScalarTower F E A]
    {a : A} (ha : IsIntegral F a) (h : minpoly E a ∈ lifts (algebraMap F E)) :
    (minpoly F a).map (algebraMap F E) = minpoly E a := by
  refine eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic ha.tower_top)
    ((algebraMap F E).injective.monic_map_iff.mp <| minpoly.monic ha)
    (minpoly.dvd E a (by simp)) ?_
  obtain ⟨g, hg, hgdeg, hgmon⟩ := lifts_and_natDegree_eq_and_monic h (minpoly.monic ha.tower_top)
  rw [natDegree_map, ← hgdeg]
  refine natDegree_le_of_dvd (minpoly.dvd F a ?_) hgmon.ne_zero
  rw [← aeval_map_algebraMap A, IsScalarTower.algebraMap_eq F E A, ← coe_mapRingHom,
    ← mapRingHom_comp, RingHom.comp_apply, coe_mapRingHom, coe_mapRingHom, hg,
    aeval_map_algebraMap, minpoly.aeval]

/-- See also `minpoly.ker_eval` which relaxes the assumptions on `A` in exchange for
stronger assumptions on `B`. -/
@[simp]
/-
**minpoly.ker_aeval_eq_span_minpoly** 是 Mathlib 中的一个引理，位于命名空间 `minpoly`。
形式化陈述：ker_aeval_eq_span_minpoly : RingHom.ker (Polynomial.aeval x) = A[X] ∙ minp
oly A x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.ext`：ext {I J : Ideal α} (h : forall x, x in I ↔ x in J) : I = J
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
See also `minpoly.ker_eval` which relaxes the assumptions on `A` in exchange for
stronger assumptions on `B`.
-/
lemma ker_aeval_eq_span_minpoly :
    RingHom.ker (Polynomial.aeval x) = A[X] ∙ minpoly A x := by
  ext p
  simp_rw [RingHom.mem_ker, ← minpoly.dvd_iff, Submodule.mem_span_singleton,
    dvd_iff_exists_eq_mul_left, smul_eq_mul, eq_comm (a := p)]

variable {A x}
/-
**minpoly.eq_of_irreducible_of_monic** 是 Mathlib 中的一个定理，位于命名空间 `minpoly`。
形式化陈述：eq_of_irreducible_of_monic [Nontrivial B] {p : A[X]} (hp1 : Irreducible p)
 (hp2 : Polynomial.aeval x p = 0) (hp3 : p.Monic) : p = minpoly A x
参数：hp1 : Irreducible p；hp2 : Polynomial.aeval x p = 0；hp3 : p.Monic。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `minpoly.dvd`：dvd {p : A[X]} (hp : Polynomial.aeval x p = 0) : minpoly A 
x ∣ p
· 使用定理 `Polynomial.eq_of_monic_of_associated`：eq_of_monic_of_associated (hp : p.
Monic) (hq : q.Monic) (hpq : Associated p q) : p = q
· 使用定理 `minpoly.monic`：monic (hx : IsIntegral A x) : Monic (minpoly A x)
· 使用定理 `Associated.mul_left`：Associated.mul_left [Monoid M] (a : M) {b c : M} (h
 : b ~ᵤ c) : a * b ~ᵤ a * c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `associated_one_iff_isUnit`：associated_one_iff_isUnit [Monoid M] {a : M} 
: (a : M) ~ᵤ 1 ↔ IsUnit a
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Irreducible.isUnit_or_isUnit`：∀ {M : Type u_1} [inst : Monoid M] {p : M}
, Irreducible p → ∀ ⦃a b : M⦄, p = a * b → IsUnit a ∨ IsUnit b
· 使用定理 `minpoly.not_isUnit`：not_isUnit [Nontrivial B] : ¬IsUnit (minpoly A x)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem eq_of_irreducible_of_monic [Nontrivial B] {p : A[X]} (hp1 : Irreducible p)
    (hp2 : Polynomial.aeval x p = 0) (hp3 : p.Monic) : p = minpoly A x :=
  let ⟨_, hq⟩ := dvd A x hp2
  eq_of_monic_of_associated hp3 (monic ⟨p, ⟨hp3, hp2⟩⟩) <|
    mul_one (minpoly A x) ▸ hq.symm ▸ Associated.mul_left _
      (associated_one_iff_isUnit.2 <| (hp1.isUnit_or_isUnit hq).resolve_left <| not_isUnit A x)
/-
**minpoly.eq_iff_aeval_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `minpoly`。
形式化陈述：eq_iff_aeval_eq_zero [Nontrivial B] {p : A[X]} (irr : Irreducible p) (moni
c : p.Monic) : p = minpoly A x ↔ Polynomial.aeval x p = 0
参数：irr : Irreducible p；monic : p.Monic。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `minpoly.aeval`：aeval : aeval x (minpoly A x) = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `minpoly.eq_of_irreducible_of_monic`：eq_of_irreducible_of_monic [Nontrivi
al B] {p : A[X]} (hp1 : Irreducible p) (hp2 : Polynomial.aeval x p = 0) (hp3 : p
.Monic) : p = minpoly A …
-/
theorem eq_iff_aeval_eq_zero [Nontrivial B] {p : A[X]} (irr : Irreducible p) (monic : p.Monic) :
    p = minpoly A x ↔ Polynomial.aeval x p = 0 :=
  ⟨(· ▸ aeval A x), (eq_of_irreducible_of_monic irr · monic)⟩
/-
**minpoly.eq_iff_aeval_minpoly_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `minpoly`。
形式化陈述：eq_iff_aeval_minpoly_eq_zero [IsDomain B] {C} [Ring C] [Algebra A C] [Nont
rivial C] {b : B} (h : IsIntegral A b) {c : C} : minpoly A b = minpoly A c ↔ Pol
ynomial.aeval c (minpoly A b) = 0
参数：h : IsIntegral A b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `minpoly.eq_iff_aeval_eq_zero`：eq_iff_aeval_eq_zero [Nontrivial B] {p : A
[X]} (irr : Irreducible p) (monic : p.Monic) : p = minpoly A x ↔ Polynomial.aeva
l x p = 0
· 使用定理 `minpoly.irreducible`：irreducible (hx : IsIntegral A x) : Irreducible (mi
npoly A x)
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `minpoly.monic`：monic (hx : IsIntegral A x) : Monic (minpoly A x)
-/
theorem eq_iff_aeval_minpoly_eq_zero [IsDomain B] {C} [Ring C] [Algebra A C] [Nontrivial C]
    {b : B} (h : IsIntegral A b) {c : C} :
    minpoly A b = minpoly A c ↔ Polynomial.aeval c (minpoly A b) = 0 :=
  eq_iff_aeval_eq_zero (irreducible h) (monic h)
/-
**minpoly.eq_of_irreducible** 是 Mathlib 中的一个定理，位于命名空间 `minpoly`。
形式化陈述：eq_of_irreducible [Nontrivial B] {p : A[X]} (hp1 : Irreducible p) (hp2 : P
olynomial.aeval x p = 0) : p * C p.leadingCoeff⁻¹ = minpoly A x
参数：hp1 : Irreducible p；hp2 : Polynomial.aeval x p = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.leadingCoeff_ne_zero`：leadingCoeff_ne_zero : leadingCoeff p !
= 0 ↔ p != 0
· 使用定理 `Irreducible.ne_zero`：∀ {M : Type u_1} [inst : MonoidWithZero M] {p : M},
 Irreducible p → p ≠ 0
· 使用定理 `minpoly.eq_of_irreducible_of_monic`：eq_of_irreducible_of_monic [Nontrivi
al B] {p : A[X]} (hp1 : Irreducible p) (hp2 : Polynomial.aeval x p = 0) (hp3 : p
.Monic) : p = minpoly A …
· 使用定理 `Associated.irreducible`：∀ {M : Type u_1} [inst : Monoid M] {p q : M}, As
sociated p q → Irreducible p → Irreducible q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.C_mul`：C_mul : C (a * b) = C a * C b
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `Polynomial.C_1`：C_1 : C (1 : R) = 1
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用定理 `Polynomial.aeval_mul`：aeval_mul : aeval x (p * q) = aeval x p * aeval x 
q
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Polynomial.Monic.eq_1`：∀ {R : Type u} [inst : Semiring R] (p : Polynomia
l R), p.Monic = (p.leadingCoeff = 1)
· 使用引理 `Polynomial.leadingCoeff_mul`：leadingCoeff_mul (p q : R[X]) : leadingCoef
f (p * q) = leadingCoeff p * leadingCoeff q
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Polynomial.leadingCoeff_C`：leadingCoeff_C (a : R) : leadingCoeff (C a) =
 a
-/
theorem eq_of_irreducible [Nontrivial B] {p : A[X]} (hp1 : Irreducible p)
    (hp2 : Polynomial.aeval x p = 0) : p * C p.leadingCoeff⁻¹ = minpoly A x := by
  have : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp1.ne_zero
  apply eq_of_irreducible_of_monic
  · exact Associated.irreducible ⟨⟨C p.leadingCoeff⁻¹, C p.leadingCoeff,
      by rwa [← C_mul, inv_mul_cancel₀, C_1], by rwa [← C_mul, mul_inv_cancel₀, C_1]⟩, rfl⟩ hp1
  · rw [aeval_mul, hp2, zero_mul]
  · rwa [Polynomial.Monic, leadingCoeff_mul, leadingCoeff_C, mul_inv_cancel₀]
/-
**minpoly.Irreducible.eq_minpoly** 是 Mathlib 中的一个定理，位于命名空间 `minpoly.Irreducible`
。
形式化陈述：∀ {A : Type u_1} {B : Type u_2} [inst : Field A] [inst_1 : Ring B] [inst_2
 : Algebra A B] {x : B} [Nontrivial B]   {p : Polynomial A}, Irreducible p → (Po
lynomial.aeval x) p = 0 → p = Polynomial.C p.leadingCoeff * minpoly A x
参数：Polynomial.aeval x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `minpoly.eq_of_irreducible`：eq_of_irreducible [Nontrivial B] {p : A[X]} (
hp1 : Irreducible p) (hp2 : Polynomial.aeval x p = 0) : p * C p.leadingCoeff⁻¹ =
 minpoly A x
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Polynomial.C_mul`：C_mul : C (a * b) = C a * C b
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.leadingCoeff_ne_zero`：leadingCoeff_ne_zero : leadingCoeff p !
= 0 ↔ p != 0
· 使用定理 `Irreducible.ne_zero`：∀ {M : Type u_1} [inst : MonoidWithZero M] {p : M},
 Irreducible p → p ≠ 0
· 使用定理 `Polynomial.C_1`：C_1 : C (1 : R) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem Irreducible.eq_minpoly [Nontrivial B] {p : A[X]} (hi : Irreducible p)
    (hx : Polynomial.aeval x p = 0) : p = C p.leadingCoeff * minpoly A x := by
  rw [← minpoly.eq_of_irreducible hi hx, mul_comm, mul_assoc, ← C_mul,
    inv_mul_cancel₀ (leadingCoeff_ne_zero.mpr hi.ne_zero), C_1, mul_one]
/-
**minpoly._root_.Irreducible.dvd_iff_aeval_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `mi
npoly`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Irreducible.dvd_iff_aeval_eq_zero [Nontrivial B] {p q : A[X]} (hi : Irreducible p)
    {b : B} (hfa : p.aeval b = 0) : q.aeval b = 0 ↔ p ∣ q := by
  refine ⟨fun hga ↦ dvd_trans ?_ (minpoly.dvd A b hga), ?_⟩
  · rw [← minpoly.eq_of_irreducible hi hfa]
    exact dvd_mul_right _ _
  · rintro ⟨g, rfl⟩
    simp [hfa]
/-
**minpoly.add_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `minpoly`。
形式化陈述：add_algebraMap {B : Type*} [CommRing B] [Algebra A B] (x : B) (a : A) : mi
npoly A (x + algebraMap A B a) = (minpoly A x).comp (X - C a)
参数：x : B；a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `minpoly.unique`：unique {p : A[X]} (pmonic : p.Monic) (hp : Polynomial.ae
val x p = 0) (pmin : forall q : A[X], q.Monic -> Polynomial.aeval x q = 0 -> deg
ree …
· 使用定理 `Polynomial.Monic.comp_X_sub_C`：∀ {R : Type u} [inst : Ring R] {p : Polyn
omial R}, p.Monic → ∀ (r : R), (p.comp (Polynomial.X - Polynomial.C r)).Monic
· 使用定理 `minpoly.monic`：monic (hx : IsIntegral A x) : Monic (minpoly A x)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.aeval_comp`：aeval_comp {A : Type*} [Semiring A] [Algebra R A]
 (x : A) : aeval x (p.comp q) = aeval (aeval x q) p
· 使用定理 `Polynomial.aeval_sub`：aeval_sub {p q : R[X]} [Ring A] [Algebra R A] (x :
 A) : aeval x (p - q) = aeval x p - aeval x q
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.aeval_X`：aeval_X : aeval x (X : R[X]) = x
· 使用定理 `Polynomial.aeval_C`：aeval_C (r : R) : aeval x (C r) = algebraMap R A r
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a
· 使用定理 `minpoly.aeval`：aeval : aeval x (minpoly A x) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `minpoly.min`：min {p : A[X]} (pmonic : p.Monic) (hp : Polynomial.aeval x 
p = 0) : degree (minpoly A x) <= degree p
· 使用引理 `Polynomial.Monic.comp_X_add_C`：comp_X_add_C (hp : p.Monic) (r : R) : (p.
comp (X + C r)).Monic
· 使用定理 `Polynomial.degree_eq_natDegree`：degree_eq_natDegree (hp : p != 0) : degr
ee p = (natDegree p : WithBot Nat)
· 使用定理 `Polynomial.Monic.ne_zero`：∀ {R : Type u} [inst : Semiring R] [Nontrivial
 R] {p : Polynomial R}, p.Monic → p ≠ 0
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `Polynomial.natDegree_comp`：natDegree_comp : natDegree (p.comp q) = natDe
gree p * natDegree q
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Polynomial.natDegree_X_sub_C`：natDegree_X_sub_C (x : R) : (X - C x).natD
egree = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
（共 36 条，此处仅展示前 30 条）
-/
theorem add_algebraMap {B : Type*} [CommRing B] [Algebra A B] (x : B)
    (a : A) : minpoly A (x + algebraMap A B a) = (minpoly A x).comp (X - C a) := by
  by_cases hx : IsIntegral A x
  · refine (minpoly.unique _ _ ((minpoly.monic hx).comp_X_sub_C _) ?_ fun q qmo hq => ?_).symm
    · simp [aeval_comp]
    · have : (Polynomial.aeval x) (q.comp (X + C a)) = 0 := by simpa [aeval_comp] using hq
      have H := minpoly.min A x (qmo.comp_X_add_C _) this
      rw [degree_eq_natDegree qmo.ne_zero,
        degree_eq_natDegree ((minpoly.monic hx).comp_X_sub_C _).ne_zero, natDegree_comp,
        natDegree_X_sub_C, mul_one]
      rwa [degree_eq_natDegree (minpoly.ne_zero hx),
        degree_eq_natDegree (qmo.comp_X_add_C _).ne_zero, natDegree_comp,
        natDegree_X_add_C, mul_one] at H
  · rw [minpoly.eq_zero hx, minpoly.eq_zero, zero_comp]
    refine fun h ↦ hx ?_
    simpa only [add_sub_cancel_right] using IsIntegral.sub h (isIntegral_algebraMap (x := a))
/-
**minpoly.sub_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `minpoly`。
形式化陈述：sub_algebraMap {B : Type*} [CommRing B] [Algebra A B] (x : B) (a : A) : mi
npoly A (x - algebraMap A B a) = (minpoly A x).comp (X + C a)
参数：x : B；a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `minpoly.add_algebraMap`：add_algebraMap {B : Type*} [CommRing B] [Algebra
 A B] (x : B) (a : A) : minpoly A (x + algebraMap A B a) = (minpoly A x).comp (X
 - C a)
-/
theorem sub_algebraMap {B : Type*} [CommRing B] [Algebra A B] (x : B)
    (a : A) : minpoly A (x - algebraMap A B a) = (minpoly A x).comp (X + C a) := by
  simpa [sub_eq_add_neg] using add_algebraMap x (-a)
/-
**minpoly.neg** 是 Mathlib 中的一个定理，位于命名空间 `minpoly`。
形式化陈述：neg {B : Type*} [Ring B] [Algebra A B] (x : B) : minpoly A (-x) = (-1) ^ (
natDegree (minpoly A x)) * (minpoly A x).comp (-X)
参数：x : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `minpoly.unique`：unique {p : A[X]} (pmonic : p.Monic) (hp : Polynomial.ae
val x p = 0) (pmin : forall q : A[X], q.Monic -> Polynomial.aeval x q = 0 -> deg
ree …
· 使用定理 `Polynomial.Monic.neg_one_pow_natDegree_mul_comp_neg_X`：∀ {R : Type u} [i
nst : CommRing R] {p : Polynomial R}, p.Monic → ((-1) ^ p.natDegree * p.comp (-P
olynomial.X)).Monic
· 使用定理 `minpoly.monic`：monic (hx : IsIntegral A x) : Monic (minpoly A x)
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
· 使用定理 `Polynomial.aeval_neg`：aeval_neg {p : R[X]} [Ring A] [Algebra R A] (x : A
) : aeval x (-p) = -aeval x p
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `Polynomial.aeval_comp`：aeval_comp {A : Type*} [Semiring A] [Algebra R A]
 (x : A) : aeval x (p.comp q) = aeval (aeval x q) p
· 使用定理 `Polynomial.aeval_X`：aeval_X : aeval x (X : R[X]) = x
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `minpoly.aeval`：aeval : aeval x (minpoly A x) = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `minpoly.min`：min {p : A[X]} (pmonic : p.Monic) (hp : Polynomial.aeval x 
p = 0) : degree (minpoly A x) <= degree p
· 使用引理 `Polynomial.degree_mul`：degree_mul : degree (p * q) = degree p + degree q
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用引理 `Polynomial.degree_pow`：degree_pow [Nontrivial R] (p : R[X]) (n : Nat) : 
degree (p ^ n) = n • degree p
（共 43 条，此处仅展示前 30 条）
-/
theorem neg {B : Type*} [Ring B] [Algebra A B] (x : B) :
    minpoly A (-x) = (-1) ^ (natDegree (minpoly A x)) * (minpoly A x).comp (-X) := by
  by_cases hx : IsIntegral A x
  · refine (minpoly.unique _ _ ((minpoly.monic hx).neg_one_pow_natDegree_mul_comp_neg_X)
        ?_ fun q qmo hq => ?_).symm
    · simp [aeval_comp]
    · have : (Polynomial.aeval x) ((-1) ^ q.natDegree * q.comp (-X)) = 0 := by
        simpa [aeval_comp] using hq
      have H := minpoly.min A x qmo.neg_one_pow_natDegree_mul_comp_neg_X this
      simp_all
  · rw [minpoly.eq_zero hx, minpoly.eq_zero, zero_comp]
    · simp only [natDegree_zero, pow_zero, mul_zero]
    · exact IsIntegral.neg_iff.not.mpr hx
/-
**minpoly.map_eq_of_equiv_equiv** 是 Mathlib 中的一个定理，位于命名空间 `minpoly`。
形式化陈述：map_eq_of_equiv_equiv {R S T : Type*} [CommRing R] [IsDomain R] [Ring S] [
Ring T] [IsDomain S] [IsDomain T] [Algebra R S] [Algebra A T] [Algebra.IsIntegra
l R S] {f : R ≃+* A} {g : S ≃+* T} (hcomp : (algebraMap A T).comp f = (g : S ->+
* T).comp (algebraMap R S)) (x : S) : map f (minpoly R x) = minpoly A (g x)
参数：hcomp : (algebraMap A T).comp f = (g : S ->+* T).comp (algebraMap R S)；x : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `minpoly.eq_of_irreducible_of_monic`：eq_of_irreducible_of_monic [Nontrivi
al B] {p : A[X]} (hp1 : Irreducible p) (hp2 : Polynomial.aeval x p = 0) (hp3 : p
.Monic) : p = minpoly A …
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.mapEquiv_apply`：∀ {R : Type u} {S : Type v} [inst : Semiring 
R] [inst_1 : Semiring S] (e : R ≃+* S) (a : Polynomial R),   (Polynomial.mapEqui
v e) a = Polyno…
· 使用引理 `MulEquiv.irreducible_iff`：MulEquiv.irreducible_iff : Irreducible (f x) ↔
 Irreducible x
· 使用定理 `RingEquivClass.toMulEquivClass`：∀ {F : Type u_7} {R : Type u_8} {S : Typ
e u_9} {inst : Mul R} {inst_1 : Add R} {inst_2 : Mul S} {inst_3 : Add S}   {inst
_4 : EquivLike F R S…
· 使用定理 `minpoly.irreducible`：irreducible (hx : IsIntegral A x) : Irreducible (mi
npoly A x)
· 使用定理 `Algebra.IsIntegral.isIntegral`：∀ {R : Type u_1} {A : Type u_3} {inst : C
ommRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsIntegral
 R A] (x : A), IsIn…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `minpoly.aeval`：aeval : aeval x (minpoly A x) = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Polynomial.map_aeval_eq_aeval_map`：map_aeval_eq_aeval_map {S T U : Type*
} [Semiring S] [CommSemiring T] [Semiring U] [Algebra R S] [Algebra T U] {φ : R 
->+* T} {ψ : S ->+* U} …
· 使用定理 `Polynomial.Monic.map`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   p.Monic → (Polynomial.ma
p f p).Mon…
· 使用定理 `minpoly.monic`：monic (hx : IsIntegral A x) : Monic (minpoly A x)
-/
theorem map_eq_of_equiv_equiv {R S T : Type*} [CommRing R] [IsDomain R] [Ring S] [Ring T]
    [IsDomain S] [IsDomain T] [Algebra R S] [Algebra A T] [Algebra.IsIntegral R S]
    {f : R ≃+* A} {g : S ≃+* T}
    (hcomp : (algebraMap A T).comp f = (g : S →+* T).comp (algebraMap R S)) (x : S) :
    map f (minpoly R x) = minpoly A (g x) := by
  refine minpoly.eq_of_irreducible_of_monic ?_ ?_ ?_
  · rw [← mapEquiv_apply, MulEquiv.irreducible_iff]
    exact minpoly.irreducible (Algebra.IsIntegral.isIntegral x)
  · simpa using (map_aeval_eq_aeval_map hcomp (minpoly R x) x).symm
  · exact (monic (Algebra.IsIntegral.isIntegral x)).map _

section AlgHomFintype

open scoped Classical in
/-- A technical finiteness result. -/
@[instance_reducible]
/-
**minpoly.Fintype.subtypeProd** 是 Mathlib 中的一个定义，位于命名空间 `minpoly.Fintype`。
形式化陈述：{E : Type u_3} → {X : Set E} → X.Finite → {L : Type u_4} → (F : E → Multis
et L) → Fintype ((x : ↑X) → { l // l ∈ F ↑x })
参数：F : E → Multiset L；(x : ↑X) → { l // l ∈ F ↑x }。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A technical finiteness result.
-/
noncomputable def Fintype.subtypeProd {E : Type*} {X : Set E} (hX : X.Finite) {L : Type*}
    (F : E → Multiset L) : Fintype (∀ x : X, { l : L // l ∈ F x }) :=
  @Pi.instFintype _ _ _ (Finite.fintype hX) _

variable (F E K : Type*) [Field F] [Ring E] [CommRing K] [IsDomain K] [Algebra F E] [Algebra F K]
  [FiniteDimensional F E]

/-- Function from `Hom_K(E,L)` to pi type Π (x : basis), roots of min poly of x -/
/-
**minpoly.rootsOfMinPolyPiType** 是 Mathlib 中的一个定义，位于命名空间 `minpoly`。
形式化陈述：rootsOfMinPolyPiType (φ : E ->ₐ[F] K) (x : range (Module.finBasis F E : _ 
-> E)) : { l : K // l in (minpoly F x.1).aroots K }
参数：φ : E ->ₐ[F] K；x : range (Module.finBasis F E : _ -> E)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Function from `Hom_K(E,L)` to pi type Π (x : basis), roots of min poly of x
-/
def rootsOfMinPolyPiType (φ : E →ₐ[F] K)
    (x : range (Module.finBasis F E : _ → E)) :
    { l : K // l ∈ (minpoly F x.1).aroots K } :=
  ⟨φ x, by
    rw [mem_roots_map (minpoly.ne_zero_of_finite F x.val),
      ← aeval_def, aeval_algHom_apply, minpoly.aeval, map_zero]⟩
/-
**minpoly.aux_inj_roots_of_min_poly** 是 Mathlib 中的一个定理，位于命名空间 `minpoly`。
形式化陈述：aux_inj_roots_of_min_poly : Injective (rootsOfMinPolyPiType F E K)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `IsNoetherianRing.strongRankCondition`：∀ (R : Type u) [inst : Ring R] [No
ntrivial R] [IsNoetherianRing R], StrongRankCondition R
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `PrincipalIdealRing.isNoetherianRing`：∀ {R : Type u} [inst : Semiring R] 
[IsPrincipalIdealRing R], IsNoetherianRing R
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `LinearMap.ext_on`：ext_on {s : Set M} {f g : M ->ₛₗ[σ₁₂] M₂} (hv : span R
 s = ⊤) (h : Set.EqOn f g s) : f = g
· 使用定理 `Module.Basis.span_eq`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_5} [in
st : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] (b : 
Module.Bas…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext_iff`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g
 ↔ ∀ (x : α), f x = g x
· 使用定理 `DFunLike.ext'_iff`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [i
 : DFunLike F α β] {f g : F}, f = g ↔ ⇑f = ⇑g
-/
theorem aux_inj_roots_of_min_poly : Injective (rootsOfMinPolyPiType F E K) := by
  intro f g h
  -- needs explicit coercion on the RHS
  suffices (f : E →ₗ[F] K) = (g : E →ₗ[F] K) by rwa [DFunLike.ext'_iff] at this ⊢
  rw [funext_iff] at h
  exact LinearMap.ext_on (Module.finBasis F E).span_eq fun e he =>
    Subtype.ext_iff.mp (h ⟨e, he⟩)

/-- Given field extensions `E/F` and `K/F`, with `E/F` finite, there are finitely many `F`-algebra
  homomorphisms `E →ₐ[K] K`. -/
/-
**minpoly.AlgHom.fintype** 是 Mathlib 中的一个定义，位于命名空间 `minpoly.AlgHom`。
形式化陈述：(F : Type u_3) →   (E : Type u_4) →     (K : Type u_5) →       [inst : Fie
ld F] →         [inst_1 : Ring E] →           [inst_2 : CommRing K] →           
  [IsDomain K] →               [inst_4 : Algebra F E] → [inst_5 : Algebra F K] →
 [FiniteDimensional F E] → Fintype (E →ₐ[F] K)
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `minpoly.aux_inj_roots_of_min_poly`：aux_inj_roots_of_min_poly : Injective
 (rootsOfMinPolyPiType F E K)

--- 原说明 ---
Given field extensions `E/F` and `K/F`, with `E/F` finite, there are finitely ma
ny `F`-algebra
  homomorphisms `E →ₐ[K] K`.
-/
noncomputable instance AlgHom.fintype : Fintype (E →ₐ[F] K) :=
  @Fintype.ofInjective _ _
    (Fintype.subtypeProd (finite_range (Module.finBasis F E)) fun e =>
      (minpoly F e).aroots K)
    _ (aux_inj_roots_of_min_poly F E K)

end AlgHomFintype

variable (B) [Nontrivial B]

/-- If `B/K` is a nontrivial algebra over a field, and `x` is an element of `K`,
then the minimal polynomial of `algebraMap K B x` is `X - C x`. -/
/-
**minpoly.eq_X_sub_C** 是 Mathlib 中的一个定理，位于命名空间 `minpoly`。
形式化陈述：eq_X_sub_C (a : A) : minpoly A (algebraMap A B a) = X - C a
参数：a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `minpoly.eq_X_sub_C_of_algebraMap_inj`：eq_X_sub_C_of_algebraMap_inj (a : 
A) (hf : Function.Injective (algebraMap A B)) : minpoly A (algebraMap A B a) = X
 - C a
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A

--- 原说明 ---
If `B/K` is a nontrivial algebra over a field, and `x` is an element of `K`,
then the minimal polynomial of `algebraMap K B x` is `X - C x`.
-/
theorem eq_X_sub_C (a : A) : minpoly A (algebraMap A B a) = X - C a :=
  eq_X_sub_C_of_algebraMap_inj a (algebraMap A B).injective
/-
**minpoly.eq_X_sub_C'** 是 Mathlib 中的一个定理，位于命名空间 `minpoly`。
形式化陈述：eq_X_sub_C' (a : A) : minpoly A a = X - C a
参数：a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `minpoly.eq_X_sub_C`：eq_X_sub_C (a : A) : minpoly A (algebraMap A B a) = 
X - C a
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
-/
theorem eq_X_sub_C' (a : A) : minpoly A a = X - C a :=
  eq_X_sub_C A a

variable (A)

/-- The minimal polynomial of `0` is `X`. -/
@[simp]
/-
**minpoly.zero** 是 Mathlib 中的一个定理，位于命名空间 `minpoly`。
形式化陈述：zero : minpoly A (0 : B) = X
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `minpoly.eq_X_sub_C`：eq_X_sub_C (a : A) : minpoly A (algebraMap A B a) = 
X - C a

--- 原说明 ---
The minimal polynomial of `0` is `X`.
-/
theorem zero : minpoly A (0 : B) = X := by
  simpa only [add_zero, C_0, sub_eq_add_neg, neg_zero, map_zero] using eq_X_sub_C B (0 : A)

/-- The minimal polynomial of `1` is `X - 1`. -/
@[simp]
/-
**minpoly.one** 是 Mathlib 中的一个定理，位于命名空间 `minpoly`。
形式化陈述：one : minpoly A (1 : B) = X - 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
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
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `minpoly.eq_X_sub_C`：eq_X_sub_C (a : A) : minpoly A (algebraMap A B a) = 
X - C a

--- 原说明 ---
The minimal polynomial of `1` is `X - 1`.
-/
theorem one : minpoly A (1 : B) = X - 1 := by
  simpa only [map_one, C_1, sub_eq_add_neg] using eq_X_sub_C B (1 : A)

end Ring

section IsDomain

variable [Ring B] [IsDomain B] [Algebra A B]
variable {A} {x : B}

/-- A minimal polynomial is prime. -/
/-
**minpoly.prime** 是 Mathlib 中的一个定理，位于命名空间 `minpoly`。
形式化陈述：prime (hx : IsIntegral A x) : Prime (minpoly A x)
参数：hx : IsIntegral A x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `minpoly.ne_zero`：ne_zero [Nontrivial A] (hx : IsIntegral A x) : minpoly 
A x != 0
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `minpoly.not_isUnit`：not_isUnit [Nontrivial B] : ¬IsUnit (minpoly A x)
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
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
· 使用定理 `minpoly.aeval`：aeval : aeval x (minpoly A x) = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `minpoly.dvd`：dvd {p : A[X]} (hp : Polynomial.aeval x p = 0) : minpoly A 
x ∣ p

--- 原说明 ---
A minimal polynomial is prime.
-/
theorem prime (hx : IsIntegral A x) : Prime (minpoly A x) := by
  refine ⟨minpoly.ne_zero hx, not_isUnit A x, ?_⟩
  rintro p q ⟨d, h⟩
  have : Polynomial.aeval x (p * q) = 0 := by simp [h, aeval A x]
  replace : Polynomial.aeval x p = 0 ∨ Polynomial.aeval x q = 0 := by simpa
  exact Or.imp (dvd A x) (dvd A x) this

/-- If `L/K` is a field extension and an element `y` of `K` is a root of the minimal polynomial
of an element `x ∈ L`, then `y` maps to `x` under the field embedding. -/
/-
**minpoly.root** 是 Mathlib 中的一个定理，位于命名空间 `minpoly`。
形式化陈述：root {x : B} (hx : IsIntegral A x) {y : A} (h : IsRoot (minpoly A x) y) : 
algebraMap A B y = x
参数：hx : IsIntegral A x；h : IsRoot (minpoly A x) y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.eq_of_monic_of_associated`：eq_of_monic_of_associated (hp : p.
Monic) (hq : q.Monic) (hpq : Associated p q) : p = q
· 使用定理 `minpoly.monic`：monic (hx : IsIntegral A x) : Monic (minpoly A x)
· 使用定理 `Polynomial.monic_X_sub_C`：monic_X_sub_C (x : R) : Monic (X - C x)
· 使用定理 `associated_of_dvd_dvd`：associated_of_dvd_dvd [MonoidWithZero M] [IsLeftC
ancelMulZero M] {a b : M} (hab : a ∣ b) (hba : b ∣ a) : a ~ᵤ b
· 使用定理 `Polynomial.instIsLeftCancelMulZeroOfIsCancelAdd`：∀ {R : Type u} [inst : 
Semiring R] [IsCancelAdd R] [IsLeftCancelMulZero R], IsLeftCancelMulZero (Polyno
mial R)
· 使用定理 `AddCancelMonoid.toIsCancelAdd`：∀ (M : Type u) [inst : AddCancelMonoid M]
, IsCancelAdd M
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Irreducible.dvd_symm`：Irreducible.dvd_symm [Monoid M] {p q : M} (hp : Ir
reducible p) (hq : Irreducible q) : p ∣ q -> q ∣ p
· 使用定理 `Polynomial.irreducible_X_sub_C`：irreducible_X_sub_C (r : R) : Irreducibl
e (X - C r)
· 使用定理 `minpoly.irreducible`：irreducible (hx : IsIntegral A x) : Irreducible (mi
npoly A x)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.dvd_iff_isRoot`：dvd_iff_isRoot : X - C a ∣ p ↔ IsRoot p a
· 使用定理 `minpoly.aeval`：aeval : aeval x (minpoly A x) = 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `Polynomial.aeval_C`：aeval_C (r : R) : aeval x (C r) = algebraMap R A r
· 使用定理 `Polynomial.aeval_X`：aeval_X : aeval x (X : R[X]) = x
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …

--- 原说明 ---
If `L/K` is a field extension and an element `y` of `K` is a root of the minimal
 polynomial
of an element `x ∈ L`, then `y` maps to `x` under the field embedding.
-/
theorem root {x : B} (hx : IsIntegral A x) {y : A} (h : IsRoot (minpoly A x) y) :
    algebraMap A B y = x := by
  have key : minpoly A x = X - C y := eq_of_monic_of_associated (monic hx) (monic_X_sub_C y)
    (associated_of_dvd_dvd ((irreducible_X_sub_C y).dvd_symm (irreducible hx) (dvd_iff_isRoot.2 h))
      (dvd_iff_isRoot.2 h))
  have := aeval A x
  rwa [key, map_sub, aeval_X, aeval_C, sub_eq_zero, eq_comm] at this

/-- The constant coefficient of the minimal polynomial of `x` is `0` if and only if `x = 0`. -/
@[simp]
/-
**minpoly.coeff_zero_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `minpoly`。
形式化陈述：coeff_zero_eq_zero (hx : IsIntegral A x) : coeff (minpoly A x) 0 = 0 ↔ x =
 0
参数：hx : IsIntegral A x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.zero_isRoot_of_coeff_zero_eq_zero`：∀ {R : Type u} [inst : Sem
iring R] {p : Polynomial R}, p.coeff 0 = 0 → p.IsRoot 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `minpoly.root`：root {x : B} (hx : IsIntegral A x) {y : A} (h : IsRoot (mi
npoly A x) y) : algebraMap A B y = x
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
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `minpoly.zero`：zero : minpoly A (0 : B) = X
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `Polynomial.coeff_X_zero`：coeff_X_zero : coeff (X : R[X]) 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The constant coefficient of the minimal polynomial of `x` is `0` if and only if 
`x = 0`.
-/
theorem coeff_zero_eq_zero (hx : IsIntegral A x) : coeff (minpoly A x) 0 = 0 ↔ x = 0 := by
  constructor
  · intro h
    have zero_root := zero_isRoot_of_coeff_zero_eq_zero h
    rw [← root hx zero_root]
    exact map_zero _
  · rintro rfl
    simp

/-- The minimal polynomial of a nonzero element has nonzero constant coefficient. -/
/-
**minpoly.coeff_zero_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `minpoly`。
形式化陈述：coeff_zero_ne_zero (hx : IsIntegral A x) (h : x != 0) : coeff (minpoly A x
) 0 != 0
参数：hx : IsIntegral A x；h : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)

--- 原说明 ---
The minimal polynomial of a nonzero element has nonzero constant coefficient.
-/
theorem coeff_zero_ne_zero (hx : IsIntegral A x) (h : x ≠ 0) : coeff (minpoly A x) 0 ≠ 0 := by
  contrapose h
  simpa only [hx, coeff_zero_eq_zero] using h

end IsDomain

end minpoly

section AlgHom

variable {K L} [Field K] [CommRing L] [IsDomain L] [Algebra K L]

/-- The minimal polynomial (over `K`) of `σ : L ≃ₐ[K] L` is `X ^ (orderOf σ) - 1`. -/
/-
**minpoly_algEquiv_toLinearMap** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：minpoly_algEquiv_toLinearMap (σ : L ≃ₐ[K] L) (hσ : IsOfFinOrder σ) : minpo
ly K σ.toLinearMap = X ^ (orderOf σ) - C 1
参数：σ : L ≃ₐ[K] L；hσ : IsOfFinOrder σ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `minpoly.unique`：unique {p : A[X]} (pmonic : p.Monic) (hp : Polynomial.ae
val x p = 0) (pmin : forall q : A[X], q.Monic -> Polynomial.aeval x q = 0 -> deg
ree …
· 使用定理 `Polynomial.monic_X_pow_sub_C`：monic_X_pow_sub_C {R : Type u} [Ring R] (a
 : R) {n : Nat} (h : n != 0) : (X ^ n - C a).Monic
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `IsOfFinOrder.orderOf_pos`：∀ {G : Type u_1} [inst : Monoid G] {x : G}, Is
OfFinOrder x → 0 < orderOf x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
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
· 使用定理 `Polynomial.aeval_sub`：aeval_sub {p q : R[X]} [Ring A] [Algebra R A] (x :
 A) : aeval x (p - q) = aeval x p - aeval x q
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `Polynomial.aeval_X`：aeval_X : aeval x (X : R[X]) = x
· 使用定理 `pow_orderOf_eq_one`：pow_orderOf_eq_one (x : G) : x ^ orderOf x = 1
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.degree_eq_natDegree`：degree_eq_natDegree (hp : p != 0) : degr
ee p = (natDegree p : WithBot Nat)
· 使用定理 `Polynomial.Monic.ne_zero`：∀ {R : Type u} [inst : Semiring R] [Nontrivial
 R] {p : Polynomial R}, p.Monic → p ≠ 0
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `Polynomial.degree_X_pow_sub_C`：degree_X_pow_sub_C {n : Nat} (hn : 0 < n)
 (a : R) : degree ((X : R[X]) ^ n - C a) = n
· 使用定理 `Nat.cast_le`：cast_le : (m : α) <= n ↔ m <= n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
（共 43 条，此处仅展示前 30 条）

--- 原说明 ---
The minimal polynomial (over `K`) of `σ : L ≃ₐ[K] L` is `X ^ (orderOf σ) - 1`.
-/
lemma minpoly_algEquiv_toLinearMap (σ : L ≃ₐ[K] L) (hσ : IsOfFinOrder σ) :
    minpoly K σ.toLinearMap = X ^ (orderOf σ) - C 1 := by
  refine (minpoly.unique _ _ (monic_X_pow_sub_C _ hσ.orderOf_pos.ne.symm) ?_ ?_).symm
  · simp [← AlgEquiv.pow_toLinearMap, pow_orderOf_eq_one]
  · intro q hq hs
    rw [degree_eq_natDegree hq.ne_zero, degree_X_pow_sub_C hσ.orderOf_pos, Nat.cast_le, ← not_lt]
    intro H
    rw [aeval_eq_sum_range' H, ← Fin.sum_univ_eq_sum_range] at hs
    simp_rw [← AlgEquiv.pow_toLinearMap] at hs
    apply hq.ne_zero
    simpa using Fintype.linearIndependent_iff.mp
      (((linearIndependent_algHom_toLinearMap' K L L).comp _ AlgEquiv.coe_toAlgHom_injective).comp _
        (Subtype.val_injective.comp ((finEquivPowers hσ).injective)))
      (q.coeff ∘ (↑)) hs ⟨_, H⟩

/-- The minimal polynomial (over `K`) of `σ : Gal(L/K)` is `X ^ (orderOf σ) - 1`. -/
/-
**minpoly_algHom_toLinearMap** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：minpoly_algHom_toLinearMap (σ : L ->ₐ[K] L) (hσ : IsOfFinOrder σ) : minpol
y K σ.toLinearMap = X ^ (orderOf σ) - C 1
参数：σ : L ->ₐ[K] L；hσ : IsOfFinOrder σ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MonoidHom.coe_coe`：MonoidHom.coe_coe [MonoidHomClass F M N] (f : F) : ((
f : M ->* N) : M -> N) = f
· 使用定理 `orderOf_injective`：orderOf_injective {H : Type*} [Monoid H] (f : G ->* H
) (hf : Function.Injective f) (x : G) : orderOf (f x) = orderOf x
· 使用定理 `MulEquiv.injective`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul M] [inst
_1 : Mul N] (e : M ≃* N), Function.Injective ⇑e
· 使用定理 `orderOf_units`：orderOf_units {y : Gˣ} : orderOf (y : G) = orderOf y
· 使用定理 `IsOfFinOrder.val_unit`：∀ {M : Type u_6} [inst : Monoid M] {x : M} (hx : 
IsOfFinOrder x), ↑hx.unit = x
· 使用引理 `minpoly_algEquiv_toLinearMap`：minpoly_algEquiv_toLinearMap (σ : L ≃ₐ[K] 
L) (hσ : IsOfFinOrder σ) : minpoly K σ.toLinearMap = X ^ (orderOf σ) - C 1
· 使用定理 `orderOf_pos_iff`：orderOf_pos_iff : 0 < orderOf x ↔ IsOfFinOrder x
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgEquiv.algHomUnitsEquiv_apply_apply`：∀ (R : Type u_1) (S : Type u_2) [
inst : CommSemiring R] [inst_1 : Semiring S] [inst_2 : Algebra R S] (f : (S →ₐ[R
] S)ˣ)   (a : S), ((AlgEqui…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The minimal polynomial (over `K`) of `σ : Gal(L/K)` is `X ^ (orderOf σ) - 1`.
-/
lemma minpoly_algHom_toLinearMap (σ : L →ₐ[K] L) (hσ : IsOfFinOrder σ) :
    minpoly K σ.toLinearMap = X ^ (orderOf σ) - C 1 := by
  have : orderOf σ = orderOf (AlgEquiv.algHomUnitsEquiv _ _ hσ.unit) := by
    rw [← MonoidHom.coe_coe, orderOf_injective, ← orderOf_units, IsOfFinOrder.val_unit]
    exact (AlgEquiv.algHomUnitsEquiv K L).injective
  rw [this, ← minpoly_algEquiv_toLinearMap]
  · apply congr_arg
    ext
    simp
  · rwa [← orderOf_pos_iff, ← this, orderOf_pos_iff]

end AlgHom

