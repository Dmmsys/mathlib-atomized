/-
Copyright (c) 2020 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Algebra.Polynomial.EraseLead

/-!
# Denominators of evaluation of polynomials at ratios

Let `i : R → K` be a homomorphism of semirings.  Assume that `K` is commutative.  If `a` and
`b` are elements of `R` such that `i b ∈ K` is invertible, then for any polynomial
`f ∈ R[X]` the "mathematical" expression `b ^ f.natDegree * f (a / b) ∈ K` is in
the image of the homomorphism `i`.
-/

@[expose] public section


open Polynomial Finset

open Polynomial

section DenomsClearable

variable {R K : Type*} [Semiring R] [CommSemiring K] {i : R →+* K}
variable {a b : R} {bi : K}

-- TODO: use hypothesis (ub : IsUnit (i b)) to work with localizations.
/-- `denomsClearable` formalizes the property that `b ^ N * f (a / b)`
does not have denominators, if the inequality `f.natDegree ≤ N` holds.

The definition asserts the existence of an element `D` of `R` and an
element `bi = 1 / i b` of `K` such that clearing the denominators of
the fraction equals `i D`.
-/
/-
**DenomsClearable** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：DenomsClearable (a b : R) (N : Nat) (f : R[X]) (i : R ->+* K) : Prop
参数：a b : R；N : Nat；f : R[X]；i : R ->+* K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`denomsClearable` formalizes the property that `b ^ N * f (a / b)`
does not have denominators, if the inequality `f.natDegree ≤ N` holds.

The definition asserts the existence of an element `D` of `R` and an
element `bi = 1 / i b` of `K` such that clearing the denominators of
the fraction equals `i D`.
-/
def DenomsClearable (a b : R) (N : ℕ) (f : R[X]) (i : R →+* K) : Prop :=
  ∃ (D : R) (bi : K), bi * i b = 1 ∧ i D = i b ^ N * eval (i a * bi) (f.map i)
/-
**denomsClearable_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：denomsClearable_zero (N : Nat) (a : R) (bu : bi * i b = 1) : DenomsClearab
le a b N 0 i
参数：N : Nat；a : R；bu : bi * i b = 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
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
· 使用定理 `Polynomial.map_zero`：∀ {R : Type u} {S : Type v} [inst : Semiring R] [in
st_1 : Semiring S] (f : R →+* S), Polynomial.map f 0 = 0
· 使用定理 `Polynomial.eval_zero`：eval_zero : (0 : R[X]).eval x = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem denomsClearable_zero (N : ℕ) (a : R) (bu : bi * i b = 1) : DenomsClearable a b N 0 i :=
  ⟨0, bi, bu, by
    simp only [eval_zero, map_zero, mul_zero, Polynomial.map_zero]⟩
/-
**denomsClearable_C_mul_X_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：denomsClearable_C_mul_X_pow {N : Nat} (a : R) (bu : bi * i b = 1) {n : Nat
} (r : R) (nN : n <= N) : DenomsClearable a b N (C r * X ^ n) i
参数：a : R；bu : bi * i b = 1；r : R；nN : n <= N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.C_mul_X_pow_eq_monomial`：∀ {R : Type u} {a : R} [inst : Semir
ing R] {n : ℕ}, Polynomial.C a * Polynomial.X ^ n = (Polynomial.monomial n) a
· 使用定理 `Polynomial.map_monomial`：map_monomial {n a} : (monomial n a).map f = mon
omial n (f a)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.eval_mul`：eval_mul : (p * q).eval x = p.eval x * q.eval x
· 使用定理 `Polynomial.eval_pow`：eval_pow (n : Nat) : (p ^ n).eval x = p.eval x ^ n
· 使用定理 `Polynomial.eval_C`：eval_C : (C a).eval x = a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Polynomial.eval_X`：eval_X : X.eval x = x
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `tsub_add_cancel_of_le`：tsub_add_cancel_of_le (h : a <= b) : b - a + a = 
b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `add_tsub_cancel_right`：add_tsub_cancel_right (a b : α) : a + b - b = a
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
· 使用定理 `mul_pow`：mul_pow {ea₁ b c₁ : Nat} {xa₁ : R} (_ : ea₁ * b = c₁) (_ : a₂ ^
 b = c₂) : (xa₁ ^ ea₁ * a₂ : R) ^ b = xa₁ ^ c₁ * c₂
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
（共 31 条，此处仅展示前 30 条）
-/
theorem denomsClearable_C_mul_X_pow {N : ℕ} (a : R) (bu : bi * i b = 1) {n : ℕ} (r : R)
    (nN : n ≤ N) : DenomsClearable a b N (C r * X ^ n) i := by
  refine ⟨r * a ^ n * b ^ (N - n), bi, bu, ?_⟩
  rw [C_mul_X_pow_eq_monomial, map_monomial, ← C_mul_X_pow_eq_monomial, eval_mul, eval_pow, eval_C]
  rw [map_mul, map_mul, map_pow, map_pow, eval_X, mul_comm]
  rw [← tsub_add_cancel_of_le nN]
  conv_lhs => rw [← mul_one (i a), ← bu]
  simp [mul_assoc, mul_comm, mul_left_comm, pow_add, mul_pow]
/-
**DenomsClearable.add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DenomsClearable.add {N : Nat} {f g : R[X]} : DenomsClearable a b N f i -> 
DenomsClearable a b N g i -> DenomsClearable a b N (f + g) i
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `Polynomial.map_add`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p q
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   Polynomial.map f (p + q)
 = Polyn…
· 使用定理 `Polynomial.eval_add`：eval_add : (p + q).eval x = p.eval x + q.eval x
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `inv_unique`：inv_unique (hy : x * y = 1) (hz : x * z = 1) : y = z
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem DenomsClearable.add {N : ℕ} {f g : R[X]} :
    DenomsClearable a b N f i → DenomsClearable a b N g i → DenomsClearable a b N (f + g) i :=
  fun ⟨Df, bf, bfu, Hf⟩ ⟨Dg, bg, bgu, Hg⟩ =>
  ⟨Df + Dg, bf, bfu, by
    rw [map_add, Polynomial.map_add, eval_add, mul_add, Hf, Hg]
    congr
    refine @inv_unique K _ (i b) bg bf ?_ ?_ <;> rwa [mul_comm]⟩
/-
**denomsClearable_of_natDegree_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：denomsClearable_of_natDegree_le (N : Nat) (a : R) (bu : bi * i b = 1) : fo
rall f : R[X], f.natDegree <= N -> DenomsClearable a b N f i
参数：N : Nat；a : R；bu : bi * i b = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.induction_with_natDegree_le`：induction_with_natDegree_le (mot
ive : R[X] -> Prop) (N : Nat) (zero : motive 0) (C_mul_pow : forall n : Nat, for
all r : R, r != 0 -> n <= N …
· 使用定理 `denomsClearable_zero`：denomsClearable_zero (N : Nat) (a : R) (bu : bi * 
i b = 1) : DenomsClearable a b N 0 i
· 使用定理 `denomsClearable_C_mul_X_pow`：denomsClearable_C_mul_X_pow {N : Nat} (a : 
R) (bu : bi * i b = 1) {n : Nat} (r : R) (nN : n <= N) : DenomsClearable a b N (
C r * X ^ n) i
· 使用定理 `DenomsClearable.add`：DenomsClearable.add {N : Nat} {f g : R[X]} : Denoms
Clearable a b N f i -> DenomsClearable a b N g i -> DenomsClearable a b N (f + g
) i
-/
theorem denomsClearable_of_natDegree_le (N : ℕ) (a : R) (bu : bi * i b = 1) :
    ∀ f : R[X], f.natDegree ≤ N → DenomsClearable a b N f i :=
  induction_with_natDegree_le _ N (denomsClearable_zero N a bu)
    (fun _ r _ => denomsClearable_C_mul_X_pow a bu r) fun _ _ _ _ df dg => df.add dg

/-- If `i : R → K` is a ring homomorphism, `f` is a polynomial with coefficients in `R`,
`a, b` are elements of `R`, with `i b` invertible, then there is a `D ∈ R` such that
`b ^ f.natDegree * f (a / b)` equals `i D`. -/
/-
**denomsClearable_natDegree** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：denomsClearable_natDegree (i : R ->+* K) (f : R[X]) (a : R) (bu : bi * i b
 = 1) : DenomsClearable a b f.natDegree f i
参数：i : R ->+* K；f : R[X]；a : R；bu : bi * i b = 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `denomsClearable_of_natDegree_le`：denomsClearable_of_natDegree_le (N : Na
t) (a : R) (bu : bi * i b = 1) : forall f : R[X], f.natDegree <= N -> DenomsClea
rable a b N f i
· 使用引理 `le_rfl`：le_rfl : a <= a

--- 原说明 ---
If `i : R → K` is a ring homomorphism, `f` is a polynomial with coefficients in 
`R`,
`a, b` are elements of `R`, with `i b` invertible, then there is a `D ∈ R` such 
that
`b ^ f.natDegree * f (a / b)` equals `i D`.
-/
theorem denomsClearable_natDegree (i : R →+* K) (f : R[X]) (a : R) (bu : bi * i b = 1) :
    DenomsClearable a b f.natDegree f i :=
  denomsClearable_of_natDegree_le f.natDegree a bu f le_rfl

end DenomsClearable

open RingHom

/-- Evaluating a polynomial with integer coefficients at a rational number and clearing
denominators, yields a number greater than or equal to one.  The target can be any
`LinearOrderedField K`.
The assumption on `K` could be weakened to `LinearOrderedCommRing` assuming that the
image of the denominator is invertible in `K`. -/
/-
**one_le_pow_mul_abs_eval_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：one_le_pow_mul_abs_eval_div {K : Type*} [Field K] [LinearOrder K] [IsStric
tOrderedRing K] {f : Int[X]} {a b : Int} (b0 : 0 < b) (fab : eval ((a : K) / b) 
(f.map (algebraMap Int K)) != 0) : (1 : K) <= (b : K) ^ f.natDegree * |eval ((a 
: K) / b) (f.map (algebraMap Int K))|
参数：b0 : 0 < b；fab : eval ((a : K) / b) (f.map (algebraMap Int K)) != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `denomsClearable_natDegree`：denomsClearable_natDegree (i : R ->+* K) (f :
 R[X]) (a : R) (bu : bi * i b = 1) : DenomsClearable a b f.natDegree f i
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_intCast`：eq_intCast [FunLike F Int α] [RingHomClass F Int α] (f : F) 
(n : Int) : f n = n
· 使用引理 `one_div_mul_cancel`：one_div_mul_cancel (h : a != 0) : 1 / a * a = 1
· 使用引理 `Int.cast_ne_zero`：cast_ne_zero : (n : α) != 0 ↔ n != 0
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `abs_of_pos`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] {a
 : α} [AddLeftMono α], 0 < a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Int.cast_pos`：∀ {R : Type u_1} [inst : AddCommGroupWithOne R] [inst_1 : 
PartialOrder R] [AddLeftMono R] [ZeroLEOneClass R] [NeZero 1]   {n : ℤ}, 0 < ↑n 
↔ …
· 使用引理 `abs_mul`：abs_mul (a b : α) : |a * b| = |a| * |b|
· 使用定理 `eq_one_div_of_mul_eq_one_left`：eq_one_div_of_mul_eq_one_left (h : b * a 
= 1) : b = 1 / a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用引理 `Int.cast_abs`：cast_abs : (↑|a| : R) = |(a : R)|
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `Int.cast_le`：∀ {R : Type u_1} [inst : AddCommGroupWithOne R] [inst_1 : P
artialOrder R] [AddLeftMono R] [ZeroLEOneClass R] [NeZero 1]   {m n : ℤ}, ↑m ≤ ↑
n…
· 使用定理 `Int.le_of_lt_add_one`：∀ {a b : ℤ}, a < b + 1 → a ≤ b
· 使用定理 `lt_add_iff_pos_left`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : 
LT α] [AddRightStrictMono α] [AddRightReflectLT α] (a : α) {b : α},   a < b + a 
↔ 0 < b
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
（共 46 条，此处仅展示前 30 条）

--- 原说明 ---
Evaluating a polynomial with integer coefficients at a rational number and clear
ing
denominators, yields a number greater than or equal to one.  The target can be a
ny
`LinearOrderedField K`.
The assumption on `K` could be weakened to `LinearOrderedCommRing` assuming that
 the
image of the denominator is invertible in `K`.
-/
theorem one_le_pow_mul_abs_eval_div {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {f : ℤ[X]} {a b : ℤ}
    (b0 : 0 < b) (fab : eval ((a : K) / b) (f.map (algebraMap ℤ K)) ≠ 0) :
    (1 : K) ≤ (b : K) ^ f.natDegree * |eval ((a : K) / b) (f.map (algebraMap ℤ K))| := by
  obtain ⟨ev, bi, bu, hF⟩ :=
    denomsClearable_natDegree (b := b) (algebraMap ℤ K) f a
      (by
        rw [eq_intCast, one_div_mul_cancel]
        rw [Int.cast_ne_zero]
        exact b0.ne.symm)
  obtain Fa := congr_arg abs hF
  rw [eq_one_div_of_mul_eq_one_left bu, eq_intCast, eq_intCast, abs_mul] at Fa
  rw [abs_of_pos (pow_pos (Int.cast_pos.mpr b0) _ : 0 < (b : K) ^ _), one_div, eq_intCast] at Fa
  rw [div_eq_mul_inv, ← Fa, ← Int.cast_abs, ← Int.cast_one, Int.cast_le]
  refine Int.le_of_lt_add_one ((lt_add_iff_pos_left 1).mpr (abs_pos.mpr fun F0 => fab ?_))
  rw [eq_one_div_of_mul_eq_one_left bu, F0, one_div, eq_intCast, Int.cast_zero, zero_eq_mul] at hF
  rcases hF with hF | hF
  · exact (not_le.mpr b0 (le_of_eq (Int.cast_eq_zero.mp (eq_zero_of_pow_eq_zero hF)))).elim
  · rwa [div_eq_mul_inv]
