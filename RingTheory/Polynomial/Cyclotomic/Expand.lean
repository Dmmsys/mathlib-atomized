/-
Copyright (c) 2020 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
module

public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

/-!
# Cyclotomic polynomials and `expand`.

We gather results relating cyclotomic polynomials and `expand`.

## Main results

* `Polynomial.cyclotomic_expand_eq_cyclotomic_mul` : If `p` is a prime such that `¬ p ∣ n`, then
  `expand R p (cyclotomic n R) = (cyclotomic (n * p) R) * (cyclotomic n R)`.
* `Polynomial.cyclotomic_expand_eq_cyclotomic` : If `p` is a prime such that `p ∣ n`, then
  `expand R p (cyclotomic n R) = cyclotomic (p * n) R`.
* `Polynomial.cyclotomic_mul_prime_eq_pow_of_not_dvd` : If `R` is of characteristic `p` and
  `¬p ∣ n`, then `cyclotomic (n * p) R = (cyclotomic n R) ^ (p - 1)`.
* `Polynomial.cyclotomic_mul_prime_dvd_eq_pow` : If `R` is of characteristic `p` and `p ∣ n`, then
  `cyclotomic (n * p) R = (cyclotomic n R) ^ p`.
* `Polynomial.cyclotomic_mul_prime_pow_eq` : If `R` is of characteristic `p` and `¬p ∣ m`, then
  `cyclotomic (p ^ k * m) R = (cyclotomic m R) ^ (p ^ k - p ^ (k - 1))`.
-/

public section


namespace Polynomial

/-- If `p` is a prime such that `¬ p ∣ n`, then
`expand R p (cyclotomic n R) = (cyclotomic (n * p) R) * (cyclotomic n R)`. -/
@[simp]
/-
**Polynomial.cyclotomic_expand_eq_cyclotomic_mul** 是 Mathlib 中的一个定理，位于命名空间 `Poly
nomial`。
形式化陈述：cyclotomic_expand_eq_cyclotomic_mul {p n : Nat} (hp : Nat.Prime p) (hdiv :
 ¬p ∣ n) (R : Type*) [CommRing R] : expand R p (cyclotomic n R) = cyclotomic (n 
* p) R * cyclotomic n R
参数：hp : Nat.Prime p；hdiv : ¬p ∣ n；R : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.eq_zero_or_pos`：∀ (n : ℕ), n = 0 ∨ n > 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.cyclotomic_zero`：cyclotomic_zero (R : Type*) [Ring R] : cyclo
tomic 0 R = 1
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
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NeZero.of_pos`：of_pos [Preorder M] [Zero M] (h : 0 < x) : NeZero x
· 使用引理 `Polynomial.eq_of_monic_of_dvd_of_natDegree_le`：eq_of_monic_of_dvd_of_nat
Degree_le {p q : R[X]} (hp : p.Monic) (hq : q.Monic) (hdvd : p ∣ q) (hdeg : q.na
tDegree <= p.natDegree) : q = p
· 使用定理 `Polynomial.Monic.mul`：∀ {R : Type u} [inst : Semiring R] {p q : Polynomi
al R}, p.Monic → q.Monic → (p * q).Monic
· 使用定理 `Polynomial.cyclotomic.monic`：∀ (n : ℕ) (R : Type u_1) [inst : Ring R], (
Polynomial.cyclotomic n R).Monic
· 使用定理 `Polynomial.Monic.expand`：∀ {R : Type u} [inst : CommSemiring R] {p : ℕ} 
{f : Polynomial R}, 0 < p → f.Monic → ((Polynomial.expand R p) f).Monic
· 使用定理 `Nat.Prime.pos`：∀ {p : ℕ}, Nat.Prime p → 0 < p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast`：∀ (p q : Polyn
omial ℤ),   p.IsPrimitive → (p ∣ q ↔ Polynomial.map (Int.castRingHom ℚ) p ∣ Poly
nomial.map (Int.castRingHom ℚ) q)
· 使用定理 `Polynomial.IsPrimitive.mul`：∀ {R : Type u_1} [inst : CommRing R] [Normal
izedGCDMonoid R] {p q : Polynomial R},   p.IsPrimitive → q.IsPrimitive → (p * q)
.IsPrimitive
· 使用定理 `Polynomial.cyclotomic.isPrimitive`：∀ (n : ℕ) (R : Type u_1) [inst : Comm
Ring R], (Polynomial.cyclotomic n R).IsPrimitive
· 使用定理 `Polynomial.map_mul`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p q
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   Polynomial.map f (p * q)
 = Polyn…
· 使用定理 `Polynomial.map_cyclotomic_int`：map_cyclotomic_int (n : Nat) (R : Type*) 
[Ring R] : map (Int.castRingHom R) (cyclotomic n Int) = cyclotomic n R
· 使用定理 `Polynomial.map_expand`：map_expand {p : Nat} {f : R ->+* S} {q : R[X]} : 
map f (expand R p q) = expand S p (map f q)
· 使用定理 `IsCoprime.mul_dvd`：IsCoprime.mul_dvd (H : IsCoprime x y) (H1 : x ∣ z) (H
2 : y ∣ z) : x * y ∣ z
（共 68 条，此处仅展示前 30 条）

--- 原说明 ---
If `p` is a prime such that `¬ p ∣ n`, then
`expand R p (cyclotomic n R) = (cyclotomic (n * p) R) * (cyclotomic n R)`.
-/
theorem cyclotomic_expand_eq_cyclotomic_mul {p n : ℕ} (hp : Nat.Prime p) (hdiv : ¬p ∣ n)
    (R : Type*) [CommRing R] :
    expand R p (cyclotomic n R) = cyclotomic (n * p) R * cyclotomic n R := by
  rcases Nat.eq_zero_or_pos n with (rfl | hnpos)
  · simp
  have := NeZero.of_pos hnpos
  suffices expand ℤ p (cyclotomic n ℤ) = cyclotomic (n * p) ℤ * cyclotomic n ℤ by
    rw [← map_cyclotomic_int, ← map_expand, this, Polynomial.map_mul, map_cyclotomic_int,
      map_cyclotomic]
  refine eq_of_monic_of_dvd_of_natDegree_le ((cyclotomic.monic _ ℤ).mul (cyclotomic.monic _ ℤ))
    ((cyclotomic.monic n ℤ).expand hp.pos) ?_ ?_
  · refine (IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast _ _
      ((cyclotomic.isPrimitive (n * p) ℤ).mul (cyclotomic.isPrimitive n ℤ))).2 ?_
    rw [Polynomial.map_mul, map_cyclotomic_int, map_cyclotomic_int, map_expand, map_cyclotomic_int]
    refine IsCoprime.mul_dvd (cyclotomic.isCoprime_rat fun h => ?_) ?_ ?_
    · replace h : n * p = n * 1 := by simp [h]
      exact Nat.Prime.ne_one hp (mul_left_cancel₀ hnpos.ne' h)
    · have hpos : 0 < n * p := mul_pos hnpos hp.pos
      have hprim := Complex.isPrimitiveRoot_exp _ hpos.ne'
      rw [cyclotomic_eq_minpoly_rat hprim hpos]
      refine minpoly.dvd ℚ _ ?_
      rw [← eval_map_algebraMap, map_expand, map_cyclotomic, expand_eval, ← IsRoot.def,
        @isRoot_cyclotomic_iff]
      convert! IsPrimitiveRoot.pow_of_dvd hprim hp.ne_zero (dvd_mul_left p n)
      rw [Nat.mul_div_cancel _ (Nat.Prime.pos hp)]
    · have hprim := Complex.isPrimitiveRoot_exp _ hnpos.ne.symm
      rw [cyclotomic_eq_minpoly_rat hprim hnpos]
      refine minpoly.dvd ℚ _ ?_
      rw [← eval_map_algebraMap, map_expand, expand_eval, ← IsRoot.def, ←
        cyclotomic_eq_minpoly_rat hprim hnpos, map_cyclotomic, @isRoot_cyclotomic_iff]
      exact IsPrimitiveRoot.pow_of_prime hprim hp hdiv
  · rw [natDegree_expand, natDegree_cyclotomic,
      natDegree_mul (cyclotomic_ne_zero _ ℤ) (cyclotomic_ne_zero _ ℤ), natDegree_cyclotomic,
      natDegree_cyclotomic, mul_comm n,
      Nat.totient_mul ((Nat.Prime.coprime_iff_not_dvd hp).2 hdiv), Nat.totient_prime hp,
      mul_comm (p - 1), ← Nat.mul_succ, Nat.sub_one, Nat.succ_pred_eq_of_pos hp.pos]

@[simp]
/-
**Polynomial.cyclotomic_six** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：cyclotomic_six (R : Type*) [Ring R] : cyclotomic 6 R = X ^ 2 - X + 1
参数：R : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_right_cancel₀`：mul_right_cancel₀ (hb : b != 0) (h : a * b = c * b) :
 a = c
· 使用定理 `Polynomial.instIsRightCancelMulZeroOfIsCancelAdd`：∀ {R : Type u} [inst :
 Semiring R] [IsCancelAdd R] [IsRightCancelMulZero R], IsRightCancelMulZero (Pol
ynomial R)
· 使用定理 `IsOrderedCancelAddMonoid.toIsCancelAdd`：∀ {α : Type u_1} [inst : AddComm
Monoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], IsCancelAdd α
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `Int.instIsCancelMulZero`：IsCancelMulZero ℤ
· 使用定理 `Polynomial.cyclotomic_ne_zero`：cyclotomic_ne_zero (n : Nat) (R : Type*) 
[Ring R] [Nontrivial R] : cyclotomic n R != 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.cyclotomic_expand_eq_cyclotomic_mul`：cyclotomic_expand_eq_cyc
lotomic_mul {p n : Nat} (hp : Nat.Prime p) (hdiv : ¬p ∣ n) (R : Type*) [CommRing
 R] : expand R p (cyclotomic n R) = …
· 使用定理 `Nat.prime_three`：prime_three : Prime 3
· 使用定理 `Mathlib.Meta.NormNum.isNat_dvd_false`：∀ {a b a' b' c : ℕ}, Mathlib.Meta.
NormNum.IsNat a a' → Mathlib.Meta.NormNum.IsNat b b' → b'.mod a' = c.succ → ¬a ∣
 b
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.cyclotomic_two`：cyclotomic_two (R : Type*) [Ring R] : cycloto
mic 2 R = X + 1
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
· 使用定理 `Polynomial.expand_X`：expand_X : expand R p X = X ^ p
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
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
（共 76 条，此处仅展示前 30 条）
-/
lemma cyclotomic_six (R : Type*) [Ring R] : cyclotomic 6 R = X ^ 2 - X + 1 := by
  suffices cyclotomic 6 ℤ = X ^ 2 - X + 1 by
    rw [← map_cyclotomic_int, this]
    simp
  apply mul_right_cancel₀ (cyclotomic_ne_zero 2 ℤ)
  rw [show 6 = 2 * 3 by rfl, ← cyclotomic_expand_eq_cyclotomic_mul Nat.prime_three (by norm_num1)]
  simp; ring

/-- If `p` is a prime such that `p ∣ n`, then
`expand R p (cyclotomic n R) = cyclotomic (p * n) R`. -/
@[simp]
/-
**Polynomial.cyclotomic_expand_eq_cyclotomic** 是 Mathlib 中的一个定理，位于命名空间 `Polynomi
al`。
形式化陈述：cyclotomic_expand_eq_cyclotomic {p n : Nat} (hp : Nat.Prime p) (hdiv : p ∣
 n) (R : Type*) [CommRing R] : expand R p (cyclotomic n R) = cyclotomic (n * p) 
R
参数：hp : Nat.Prime p；hdiv : p ∣ n；R : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.eq_zero_or_pos`：∀ (n : ℕ), n = 0 ∨ n > 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.cyclotomic_zero`：cyclotomic_zero (R : Type*) [Ring R] : cyclo
tomic 0 R = 1
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
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NeZero.of_pos`：of_pos [Preorder M] [Zero M] (h : 0 < x) : NeZero x
· 使用引理 `Polynomial.eq_of_monic_of_dvd_of_natDegree_le`：eq_of_monic_of_dvd_of_nat
Degree_le {p q : R[X]} (hp : p.Monic) (hq : q.Monic) (hdvd : p ∣ q) (hdeg : q.na
tDegree <= p.natDegree) : q = p
· 使用定理 `Polynomial.cyclotomic.monic`：∀ (n : ℕ) (R : Type u_1) [inst : Ring R], (
Polynomial.cyclotomic n R).Monic
· 使用定理 `Polynomial.Monic.expand`：∀ {R : Type u} [inst : CommSemiring R] {p : ℕ} 
{f : Polynomial R}, 0 < p → f.Monic → ((Polynomial.expand R p) f).Monic
· 使用定理 `Nat.Prime.pos`：∀ {p : ℕ}, Nat.Prime p → 0 < p
· 使用定理 `Nat.mul_pos`：∀ {n m : ℕ}, 0 < n → 0 < m → 0 < n * m
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Complex.isPrimitiveRoot_exp`：isPrimitiveRoot_exp (n : Nat) (h0 : n != 0)
 : IsPrimitiveRoot (exp (2 * π * I / n)) n
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Polynomial.cyclotomic_eq_minpoly`：cyclotomic_eq_minpoly {n : Nat} {K : T
ype*} [Field K] {μ : K} (h : IsPrimitiveRoot μ n) (hpos : 0 < n) [CharZero K] : 
cyclotomic n Int = min…
· 使用定理 `minpoly.isIntegrallyClosed_dvd`：isIntegrallyClosed_dvd {s : S} (hs : IsI
ntegral R s) {p : R[X]} (hp : Polynomial.aeval s p = 0) : minpoly R s ∣ p
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `IsPrincipalIdealRing.isDedekindDomain`：∀ (A : Type u_2) [inst : CommRing
 A] [IsDomain A] [IsPrincipalIdealRing A], IsDedekindDomain A
（共 51 条，此处仅展示前 30 条）

--- 原说明 ---
If `p` is a prime such that `p ∣ n`, then
`expand R p (cyclotomic n R) = cyclotomic (p * n) R`.
-/
theorem cyclotomic_expand_eq_cyclotomic {p n : ℕ} (hp : Nat.Prime p) (hdiv : p ∣ n) (R : Type*)
    [CommRing R] : expand R p (cyclotomic n R) = cyclotomic (n * p) R := by
  rcases n.eq_zero_or_pos with (rfl | hzero)
  · simp
  have := NeZero.of_pos hzero
  suffices expand ℤ p (cyclotomic n ℤ) = cyclotomic (n * p) ℤ by
    rw [← map_cyclotomic_int, ← map_expand, this, map_cyclotomic_int]
  refine eq_of_monic_of_dvd_of_natDegree_le (cyclotomic.monic _ ℤ)
    ((cyclotomic.monic n ℤ).expand hp.pos) ?_ ?_
  · have hpos := Nat.mul_pos hzero hp.pos
    have hprim := Complex.isPrimitiveRoot_exp _ hpos.ne.symm
    rw [cyclotomic_eq_minpoly hprim hpos]
    refine minpoly.isIntegrallyClosed_dvd (hprim.isIntegral hpos) ?_
    rw [← eval_map_algebraMap, map_expand, map_cyclotomic, expand_eval, ← IsRoot.def,
      @isRoot_cyclotomic_iff]
    convert! IsPrimitiveRoot.pow_of_dvd hprim hp.ne_zero (dvd_mul_left p n)
    rw [Nat.mul_div_cancel _ hp.pos]
  · rw [natDegree_expand, natDegree_cyclotomic, natDegree_cyclotomic, mul_comm n,
      Nat.totient_mul_of_prime_of_dvd hp hdiv, mul_comm]

/-- If the `p ^ n`th cyclotomic polynomial is irreducible, so is the `p ^ m`th, for `m ≤ n`. -/
/-
**Polynomial.cyclotomic_irreducible_pow_of_irreducible_pow** 是 Mathlib 中的一个定理，位于
命名空间 `Polynomial`。
形式化陈述：cyclotomic_irreducible_pow_of_irreducible_pow {p : Nat} (hp : Nat.Prime p)
 {R} [CommRing R] [IsDomain R] {n m : Nat} (hmn : m <= n) (h : Irreducible (cycl
otomic (p ^ n) R)) : Irreducible (cyclotomic (p ^ m) R)
参数：hp : Nat.Prime p；hmn : m <= n；h : Irreducible (cyclotomic (p ^ n) R)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.eq_zero_or_pos`：∀ (n : ℕ), n = 0 ∨ n > 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Polynomial.cyclotomic_one`：cyclotomic_one (R : Type*) [Ring R] : cycloto
mic 1 R = X - 1
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
· 使用定理 `Polynomial.irreducible_X_sub_C`：irreducible_X_sub_C (r : R) : Irreducibl
e (X - C r)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.exists_eq_add_of_le`：∀ {m n : ℕ}, m ≤ n → ∃ k, n = m + k
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `add_pos_of_pos_of_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst
_1 : Preorder α] [AddLeftMono α] {a b : α}, 0 < a → 0 ≤ b → 0 < a + b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用定理 `Polynomial.of_irreducible_expand`：of_irreducible_expand {p : Nat} (hp : 
p != 0) {f : R[X]} (hf : Irreducible (expand R p f)) : Irreducible f
· 使用定理 `Nat.Prime.ne_zero`：∀ {n : ℕ}, Nat.Prime n → n ≠ 0
· 使用定理 `Polynomial.cyclotomic_expand_eq_cyclotomic`：cyclotomic_expand_eq_cycloto
mic {p n : Nat} (hp : Nat.Prime p) (hdiv : p ∣ n) (R : Type*) [CommRing R] : exp
and R p (cyclotomic n R) = cyclo…
· 使用引理 `dvd_pow_self`：dvd_pow_self (a : α) {n : Nat} (hn : n != 0) : a ∣ a ^ n
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `Nat.add_succ`：∀ (n m : ℕ), n + m.succ = (n + m).succ

--- 原说明 ---
If the `p ^ n`th cyclotomic polynomial is irreducible, so is the `p ^ m`th, for 
`m ≤ n`.
-/
theorem cyclotomic_irreducible_pow_of_irreducible_pow {p : ℕ} (hp : Nat.Prime p) {R} [CommRing R]
    [IsDomain R] {n m : ℕ} (hmn : m ≤ n) (h : Irreducible (cyclotomic (p ^ n) R)) :
    Irreducible (cyclotomic (p ^ m) R) := by
  rcases m.eq_zero_or_pos with (rfl | hm)
  · simpa using irreducible_X_sub_C (1 : R)
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  induction k with
  | zero => simpa using h
  | succ k hk =>
    have : m + k ≠ 0 := (add_pos_of_pos_of_nonneg hm k.zero_le).ne'
    rw [Nat.add_succ, pow_succ, ← cyclotomic_expand_eq_cyclotomic hp <| dvd_pow_self p this] at h
    exact hk (by lia) (of_irreducible_expand hp.ne_zero h)

/-- If `Irreducible (cyclotomic (p ^ n) R)` then `Irreducible (cyclotomic p R).` -/
/-
**Polynomial.cyclotomic_irreducible_of_irreducible_pow** 是 Mathlib 中的一个定理，位于命名空间
 `Polynomial`。
形式化陈述：cyclotomic_irreducible_of_irreducible_pow {p : Nat} (hp : Nat.Prime p) {R}
 [CommRing R] [IsDomain R] {n : Nat} (hn : n != 0) (h : Irreducible (cyclotomic 
(p ^ n) R)) : Irreducible (cyclotomic p R)
参数：hp : Nat.Prime p；hn : n != 0；h : Irreducible (cyclotomic (p ^ n) R)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.cyclotomic_irreducible_pow_of_irreducible_pow`：cyclotomic_irr
educible_pow_of_irreducible_pow {p : Nat} (hp : Nat.Prime p) {R} [CommRing R] [I
sDomain R] {n m : Nat} (hmn : m <= n) (h : Irr…
· 使用定理 `Ne.bot_lt`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α] 
{a : α}, a ≠ ⊥ → ⊥ < a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a

--- 原说明 ---
If `Irreducible (cyclotomic (p ^ n) R)` then `Irreducible (cyclotomic p R).`
-/
theorem cyclotomic_irreducible_of_irreducible_pow {p : ℕ} (hp : Nat.Prime p) {R} [CommRing R]
    [IsDomain R] {n : ℕ} (hn : n ≠ 0) (h : Irreducible (cyclotomic (p ^ n) R)) :
    Irreducible (cyclotomic p R) :=
  pow_one p ▸ cyclotomic_irreducible_pow_of_irreducible_pow hp hn.bot_lt h

section CharP

/-- If `R` is of characteristic `p` and `¬p ∣ n`, then
`cyclotomic (n * p) R = (cyclotomic n R) ^ (p - 1)`. -/
/-
**Polynomial.cyclotomic_mul_prime_eq_pow_of_not_dvd** 是 Mathlib 中的一个定理，位于命名空间 `P
olynomial`。
形式化陈述：cyclotomic_mul_prime_eq_pow_of_not_dvd (R : Type*) {p n : Nat} [hp : Fact 
(Nat.Prime p)] [Ring R] [CharP R p] (hn : ¬p ∣ n) : cyclotomic (n * p) R = cyclo
tomic n R ^ (p - 1)
参数：R : Type*；Nat.Prime p；hn : ¬p ∣ n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_right_injective₀`：mul_right_injective₀ (ha : a != 0) : Function.Inje
ctive (a * ·)
· 使用定理 `Polynomial.instIsLeftCancelMulZeroOfIsCancelAdd`：∀ {R : Type u} [inst : 
Semiring R] [IsCancelAdd R] [IsLeftCancelMulZero R], IsLeftCancelMulZero (Polyno
mial R)
· 使用定理 `AddCancelMonoid.toIsCancelAdd`：∀ (M : Type u) [inst : AddCancelMonoid M]
, IsCancelAdd M
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `ZMod.instIsDomain`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], IsDomain (ZMod p
)
· 使用定理 `Polynomial.cyclotomic_ne_zero`：cyclotomic_ne_zero (n : Nat) (R : Type*) 
[Ring R] [Nontrivial R] : cyclotomic n R != 0
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `tsub_add_cancel_of_le`：tsub_add_cancel_of_le (h : a <= b) : b - a + a = 
b
· 使用定理 `StarOrderedRing.toExistsAddOfLE`：∀ {R : Type u_1} [inst : NonUnitalSemir
ing R] [inst_1 : PartialOrder R] [inst_2 : StarRing R] [StarOrderedRing R],   Ex
istsAddOfLE R
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Nat.Prime.one_lt`：∀ {p : ℕ}, Nat.Prime p → 1 < p
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `ZMod.expand_card`：expand_card (f : Polynomial (ZMod p)) : expand (ZMod p
) p f = f ^ p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.map_cyclotomic_int`：map_cyclotomic_int (n : Nat) (R : Type*) 
[Ring R] : map (Int.castRingHom R) (cyclotomic n Int) = cyclotomic n R
· 使用定理 `Polynomial.map_expand`：map_expand {p : Nat} {f : R ->+* S} {q : R[X]} : 
map f (expand R p q) = expand S p (map f q)
· 使用定理 `Polynomial.cyclotomic_expand_eq_cyclotomic_mul`：cyclotomic_expand_eq_cyc
lotomic_mul {p n : Nat} (hp : Nat.Prime p) (hdiv : ¬p ∣ n) (R : Type*) [CommRing
 R] : expand R p (cyclotomic n R) = …
· 使用定理 `Polynomial.map_mul`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p q
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   Polynomial.map f (p * q)
 = Polyn…
· 使用定理 `Polynomial.map_cyclotomic`：map_cyclotomic (n : Nat) {R S : Type*} [Ring 
R] [Ring S] (f : R ->+* S) : map f (cyclotomic n R) = cyclotomic n S
· 使用定理 `Polynomial.map_pow`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p :
 Polynomial R} [inst_1 : Semiring S] (f : R →+* S) (n : ℕ),   Polynomial.map f (
p ^ n) =…

--- 原说明 ---
If `R` is of characteristic `p` and `¬p ∣ n`, then
`cyclotomic (n * p) R = (cyclotomic n R) ^ (p - 1)`.
-/
theorem cyclotomic_mul_prime_eq_pow_of_not_dvd (R : Type*) {p n : ℕ} [hp : Fact (Nat.Prime p)]
    [Ring R] [CharP R p] (hn : ¬p ∣ n) : cyclotomic (n * p) R = cyclotomic n R ^ (p - 1) := by
  let : Algebra (ZMod p) R := ZMod.algebra _ _
  suffices cyclotomic (n * p) (ZMod p) = cyclotomic n (ZMod p) ^ (p - 1) by
    rw [← map_cyclotomic _ (algebraMap (ZMod p) R), ← map_cyclotomic _ (algebraMap (ZMod p) R),
      this, Polynomial.map_pow]
  apply mul_right_injective₀ (cyclotomic_ne_zero n <| ZMod p); dsimp
  rw [← pow_succ', tsub_add_cancel_of_le hp.out.one_lt.le, mul_comm, ← ZMod.expand_card]
  conv_rhs => rw [← map_cyclotomic_int]
  rw [← map_expand, cyclotomic_expand_eq_cyclotomic_mul hp.out hn, Polynomial.map_mul,
    map_cyclotomic, map_cyclotomic]

/-- If `R` is of characteristic `p` and `p ∣ n`, then
`cyclotomic (n * p) R = (cyclotomic n R) ^ p`. -/
/-
**Polynomial.cyclotomic_mul_prime_dvd_eq_pow** 是 Mathlib 中的一个定理，位于命名空间 `Polynomi
al`。
形式化陈述：cyclotomic_mul_prime_dvd_eq_pow (R : Type*) {p n : Nat} [hp : Fact (Nat.Pr
ime p)] [Ring R] [CharP R p] (hn : p ∣ n) : cyclotomic (n * p) R = cyclotomic n 
R ^ p
参数：R : Type*；Nat.Prime p；hn : p ∣ n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ZMod.expand_card`：expand_card (f : Polynomial (ZMod p)) : expand (ZMod p
) p f = f ^ p
· 使用定理 `Polynomial.map_cyclotomic_int`：map_cyclotomic_int (n : Nat) (R : Type*) 
[Ring R] : map (Int.castRingHom R) (cyclotomic n Int) = cyclotomic n R
· 使用定理 `Polynomial.map_expand`：map_expand {p : Nat} {f : R ->+* S} {q : R[X]} : 
map f (expand R p q) = expand S p (map f q)
· 使用定理 `Polynomial.cyclotomic_expand_eq_cyclotomic`：cyclotomic_expand_eq_cycloto
mic {p n : Nat} (hp : Nat.Prime p) (hdiv : p ∣ n) (R : Type*) [CommRing R] : exp
and R p (cyclotomic n R) = cyclo…
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `Polynomial.map_cyclotomic`：map_cyclotomic (n : Nat) {R S : Type*} [Ring 
R] [Ring S] (f : R ->+* S) : map f (cyclotomic n R) = cyclotomic n S
· 使用定理 `Polynomial.map_pow`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p :
 Polynomial R} [inst_1 : Semiring S] (f : R →+* S) (n : ℕ),   Polynomial.map f (
p ^ n) =…

--- 原说明 ---
If `R` is of characteristic `p` and `p ∣ n`, then
`cyclotomic (n * p) R = (cyclotomic n R) ^ p`.
-/
theorem cyclotomic_mul_prime_dvd_eq_pow (R : Type*) {p n : ℕ} [hp : Fact (Nat.Prime p)] [Ring R]
    [CharP R p] (hn : p ∣ n) : cyclotomic (n * p) R = cyclotomic n R ^ p := by
  let : Algebra (ZMod p) R := ZMod.algebra _ _
  suffices cyclotomic (n * p) (ZMod p) = cyclotomic n (ZMod p) ^ p by
    rw [← map_cyclotomic _ (algebraMap (ZMod p) R), ← map_cyclotomic _ (algebraMap (ZMod p) R),
      this, Polynomial.map_pow]
  rw [← ZMod.expand_card, ← map_cyclotomic_int n, ← map_expand,
    cyclotomic_expand_eq_cyclotomic hp.out hn, map_cyclotomic]

/-- If `R` is of characteristic `p` and `¬p ∣ m`, then
`cyclotomic (p ^ k * m) R = (cyclotomic m R) ^ (p ^ k - p ^ (k - 1))`. -/
/-
**Polynomial.cyclotomic_mul_prime_pow_eq** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：cyclotomic_mul_prime_pow_eq (R : Type*) {p m : Nat} [Fact (Nat.Prime p)] [
Ring R] [CharP R p] (hm : ¬p ∣ m) : forall {k}, 0 < k -> cyclotomic (p ^ k * m) 
R = cyclotomic m R ^ (p ^ k - p ^ (k - 1)) | 1, _ => by rw [pow_one]; rw [Nat.su
b_self]; rw [pow_zero]; rw [mul_comm]; rw [cyclotomic_mul_prime_eq_pow_of_not_dv
d R hm] | a + 2, _ => by have hdiv : p ∣ p ^ a.succ * m
参数：R : Type*；Nat.Prime p；hm : ¬p ∣ m。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `R` is of characteristic `p` and `¬p ∣ m`, then
`cyclotomic (p ^ k * m) R = (cyclotomic m R) ^ (p ^ k - p ^ (k - 1))`.
-/
theorem cyclotomic_mul_prime_pow_eq (R : Type*) {p m : ℕ} [Fact (Nat.Prime p)] [Ring R] [CharP R p]
    (hm : ¬p ∣ m) : ∀ {k}, 0 < k → cyclotomic (p ^ k * m) R = cyclotomic m R ^ (p ^ k - p ^ (k - 1))
  | 1, _ => by
    rw [pow_one, Nat.sub_self, pow_zero, mul_comm, cyclotomic_mul_prime_eq_pow_of_not_dvd R hm]
  | a + 2, _ => by
    have hdiv : p ∣ p ^ a.succ * m := ⟨p ^ a * m, by rw [← mul_assoc, pow_succ']⟩
    rw [pow_succ', mul_assoc, mul_comm, cyclotomic_mul_prime_dvd_eq_pow R hdiv,
      cyclotomic_mul_prime_pow_eq _ _ a.succ_pos, ← pow_mul]
    · simp only [Nat.succ_sub_succ_eq_sub, Nat.sub_zero]
      rw [Nat.mul_sub_right_distrib, mul_comm, pow_succ]
    · assumption

/-- If `R` is of characteristic `p` and `¬p ∣ m`, then `ζ` is a root of `cyclotomic (p ^ k * m) R`
if and only if it is a primitive `m`-th root of unity. -/
/-
**Polynomial.isRoot_cyclotomic_prime_pow_mul_iff_of_charP** 是 Mathlib 中的一个定理，位于命
名空间 `Polynomial`。
形式化陈述：isRoot_cyclotomic_prime_pow_mul_iff_of_charP {m k p : Nat} {R : Type*} [Co
mmRing R] [IsDomain R] [hp : Fact (Nat.Prime p)] [hchar : CharP R p] {μ : R} [Ne
Zero (m : R)] : (Polynomial.cyclotomic (p ^ k * m) R).IsRoot μ ↔ IsPrimitiveRoot
 μ m
参数：Nat.Prime p；m : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.eq_zero_or_pos`：∀ (n : ℕ), n = 0 ∨ n > 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Polynomial.isRoot_cyclotomic_iff`：isRoot_cyclotomic_iff [NeZero (n : R)]
 {μ : R} : IsRoot (cyclotomic n R) μ ↔ IsPrimitiveRoot μ n
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_zero_of_pow_eq_zero`：eq_zero_of_pow_eq_zero [Zero R] [Pow R Nat] [IsR
educed R] {n : Nat} (h : x ^ n = 0) : x = 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Polynomial.eval_pow`：eval_pow (n : Nat) : (p ^ n).eval x = p.eval x ^ n
· 使用定理 `Polynomial.cyclotomic_mul_prime_pow_eq`：cyclotomic_mul_prime_pow_eq (R :
 Type*) {p m : Nat} [Fact (Nat.Prime p)] [Ring R] [CharP R p] (hm : ¬p ∣ m) : fo
rall {k}, 0 < k -> cyclotomi…
· 使用引理 `NeZero.not_char_dvd`：not_char_dvd (p : Nat) [CharP R p] (k : Nat) [h : N
eZero (k : R)] : ¬p ∣ k
· 使用定理 `Polynomial.IsRoot.def`：∀ {R : Type u} {a : R} [inst : Semiring R] {p : P
olynomial R}, p.IsRoot a ↔ Polynomial.eval a p = 0
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `Nat.sub_ne_zero_of_lt`：∀ {a b : ℕ}, a < b → b - a ≠ 0
· 使用引理 `pow_right_strictMono₀`：pow_right_strictMono₀ (h : 1 < a) : StrictMono (a
 ^ ·)
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `Nat.Prime.one_lt`：∀ {p : ℕ}, Nat.Prime p → 1 < p
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `Nat.pred_lt`：∀ {n : ℕ}, n ≠ 0 → n.pred < n
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b

--- 原说明 ---
If `R` is of characteristic `p` and `¬p ∣ m`, then `ζ` is a root of `cyclotomic 
(p ^ k * m) R`
if and only if it is a primitive `m`-th root of unity.
-/
theorem isRoot_cyclotomic_prime_pow_mul_iff_of_charP {m k p : ℕ} {R : Type*} [CommRing R]
    [IsDomain R] [hp : Fact (Nat.Prime p)] [hchar : CharP R p] {μ : R} [NeZero (m : R)] :
    (Polynomial.cyclotomic (p ^ k * m) R).IsRoot μ ↔ IsPrimitiveRoot μ m := by
  rcases k.eq_zero_or_pos with (rfl | hk)
  · rw [pow_zero, one_mul, isRoot_cyclotomic_iff]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [IsRoot.def, cyclotomic_mul_prime_pow_eq R (NeZero.not_char_dvd R p m) hk, eval_pow]
      at h
    replace h := eq_zero_of_pow_eq_zero h
    rwa [← IsRoot.def, isRoot_cyclotomic_iff] at h
  · rw [← isRoot_cyclotomic_iff, IsRoot.def] at h
    rw [cyclotomic_mul_prime_pow_eq R (NeZero.not_char_dvd R p m) hk, IsRoot.def, eval_pow,
      h, zero_pow]
    exact Nat.sub_ne_zero_of_lt <| pow_right_strictMono₀ hp.out.one_lt <| Nat.pred_lt hk.ne'

end CharP

end Polynomial

