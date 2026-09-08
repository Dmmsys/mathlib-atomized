/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.Data.Nat.Multiplicity
public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.WittVector.Basic
public import Mathlib.RingTheory.WittVector.IsPoly

/-!
## The Frobenius operator

If `R` has characteristic `p`, then there is a ring endomorphism `frobenius R p`
that raises `r : R` to the power `p`.
By applying `WittVector.map` to `frobenius R p`, we obtain a ring endomorphism `𝕎 R →+* 𝕎 R`.
It turns out that this endomorphism can be described by polynomials over `ℤ`
that do not depend on `R` or the fact that it has characteristic `p`.
In this way, we obtain a Frobenius endomorphism `WittVector.frobeniusFun : 𝕎 R → 𝕎 R`
for every commutative ring `R`.

Unfortunately, the aforementioned polynomials cannot be obtained using the machinery
of `wittStructureInt` that was developed in `StructurePolynomial.lean`.
We therefore have to define the polynomials by hand, and check that they have the required property.

In case `R` has characteristic `p`, we show in `frobenius_eq_map_frobenius`
that `WittVector.frobeniusFun` is equal to `WittVector.map (frobenius R p)`.

### Main definitions and results

* `frobeniusPoly`: the polynomials that describe the coefficients of `frobeniusFun`;
* `frobeniusFun`: the Frobenius endomorphism on Witt vectors;
* `frobeniusFun_isPoly`: the tautological assertion that Frobenius is a polynomial function;
* `frobenius_eq_map_frobenius`: the fact that in characteristic `p`, Frobenius is equal to
  `WittVector.map (frobenius R p)`.

TODO: Show that `WittVector.frobeniusFun` is a ring homomorphism,
and bundle it into `WittVector.frobenius`.

## References

* [Hazewinkel, *Witt Vectors*][Haze09]

* [Commelin and Lewis, *Formalizing the Ring of Witt Vectors*][CL21]
-/

@[expose] public section


namespace WittVector

variable {p : ℕ} {R : Type*} [hp : Fact p.Prime] [CommRing R]

local notation "𝕎" => WittVector p -- type as `\bbW`

noncomputable section

open MvPolynomial Finset

variable (p)

/-- The rational polynomials that give the coefficients of `frobenius x`,
in terms of the coefficients of `x`.
These polynomials actually have integral coefficients,
see `frobeniusPoly` and `map_frobeniusPoly`. -/
/-
**WittVector.frobeniusPolyRat** 是 Mathlib 中的一个定义，位于命名空间 `WittVector`。
形式化陈述：frobeniusPolyRat (n : Nat) : MvPolynomial Nat Rat
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The rational polynomials that give the coefficients of `frobenius x`,
in terms of the coefficients of `x`.
These polynomials actually have integral coefficients,
see `frobeniusPoly` and `map_frobeniusPoly`.
-/
def frobeniusPolyRat (n : ℕ) : MvPolynomial ℕ ℚ :=
  bind₁ (wittPolynomial p ℚ ∘ fun n => n + 1) (xInTermsOfW p ℚ n)
/-
**WittVector.bind** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bind₁_frobeniusPolyRat_wittPolynomial (n : ℕ) :
    bind₁ (frobeniusPolyRat p) (wittPolynomial p ℚ n) = wittPolynomial p ℚ (n + 1) := by
  delta frobeniusPolyRat
  rw [← bind₁_bind₁, bind₁_xInTermsOfW_wittPolynomial, bind₁_X_right, Function.comp_apply]

local notation "v" => multiplicity

/-- An auxiliary polynomial over the integers, that satisfies
`p * (frobeniusPolyAux p n) + X n ^ p = frobeniusPoly p n`.
This makes it easy to show that `frobeniusPoly p n` is congruent to `X n ^ p`
modulo `p`. -/
/-
**WittVector.frobeniusPolyAux** 是 Mathlib 中的一个定义，位于命名空间 `WittVector`。
形式化陈述：frobeniusPolyAux : Nat -> MvPolynomial Nat Int | n => X (n + 1) - ∑ i : Fi
n n, have _
该定义给出了一等式。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.is_lt`：∀ {n : ℕ} (a : Fin n), ↑a < n

--- 原说明 ---
An auxiliary polynomial over the integers, that satisfies
`p * (frobeniusPolyAux p n) + X n ^ p = frobeniusPoly p n`.
This makes it easy to show that `frobeniusPoly p n` is congruent to `X n ^ p`
modulo `p`.
-/
noncomputable def frobeniusPolyAux : ℕ → MvPolynomial ℕ ℤ
  | n => X (n + 1) - ∑ i : Fin n, have _ := i.is_lt
      ∑ j ∈ range (p ^ (n - i)),
        (((X (i : ℕ) ^ p) ^ (p ^ (n - (i : ℕ)) - (j + 1)) : MvPolynomial ℕ ℤ) *
        (frobeniusPolyAux i) ^ (j + 1)) *
        C (((p ^ (n - i)).choose (j + 1) / (p ^ (n - i - v p (j + 1)))
          * ↑p ^ (j - v p (j + 1)) : ℕ) : ℤ)

omit hp in
/-
**WittVector.frobeniusPolyAux_eq** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：frobeniusPolyAux_eq (n : Nat) : frobeniusPolyAux p n = X (n + 1) - ∑ i in 
range n, ∑ j in range (p ^ (n - i)), (X i ^ p) ^ (p ^ (n - i) - (j + 1)) * frobe
niusPolyAux p i ^ (j + 1) * C ↑((p ^ (n - i)).choose (j + 1) / p ^ (n - i - v p 
(j + 1)) * ↑p ^ (j - v p (j + 1)) : Nat)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.is_lt`：∀ {n : ℕ} (a : Fin n), ↑a < n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WittVector.frobeniusPolyAux.eq_1`：∀ (p x : ℕ),   WittVector.frobeniusPol
yAux p x =     MvPolynomial.X (x + 1) -       ∑ i,         have x_1 := ⋯;       
  ∑ j ∈ Finset.range (…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.sum_univ_eq_sum_range`：∀ {α : Type u_1} [inst : AddCommMonoid α] (f 
: ℕ → α) (n : ℕ), ∑ i, f ↑i = ∑ i ∈ Finset.range n, f i
-/
theorem frobeniusPolyAux_eq (n : ℕ) :
    frobeniusPolyAux p n =
      X (n + 1) - ∑ i ∈ range n,
          ∑ j ∈ range (p ^ (n - i)),
            (X i ^ p) ^ (p ^ (n - i) - (j + 1)) * frobeniusPolyAux p i ^ (j + 1) *
              C ↑((p ^ (n - i)).choose (j + 1) / p ^ (n - i - v p (j + 1)) *
                ↑p ^ (j - v p (j + 1)) : ℕ) := by
  rw [frobeniusPolyAux, ← Fin.sum_univ_eq_sum_range]

/-- The polynomials that give the coefficients of `frobenius x`,
in terms of the coefficients of `x`. -/
/-
**WittVector.frobeniusPoly** 是 Mathlib 中的一个定义，位于命名空间 `WittVector`。
形式化陈述：frobeniusPoly (n : Nat) : MvPolynomial Nat Int
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The polynomials that give the coefficients of `frobenius x`,
in terms of the coefficients of `x`.
-/
def frobeniusPoly (n : ℕ) : MvPolynomial ℕ ℤ :=
  X n ^ p + C (p : ℤ) * frobeniusPolyAux p n

/-
Our next goal is to prove
```
lemma map_frobeniusPoly (n : ℕ) :
    MvPolynomial.map (Int.castRingHom ℚ) (frobeniusPoly p n) = frobeniusPolyRat p n
```
This lemma has a rather long proof, but it mostly boils down to applying induction,
and then using the following two key facts at the right point.
-/
/-- A key divisibility fact for the proof of `WittVector.map_frobeniusPoly`. -/
/-
**WittVector.map_frobeniusPoly.key** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A key divisibility fact for the proof of `WittVector.map_frobeniusPoly`.
-/
theorem map_frobeniusPoly.key₁ (n j : ℕ) (hj : j < p ^ n) :
    p ^ (n - v p (j + 1)) ∣ (p ^ n).choose (j + 1) := by
  apply pow_dvd_of_le_emultiplicity
  rw [hp.out.emultiplicity_choose_prime_pow hj j.succ_ne_zero]

/-- A key numerical identity needed for the proof of `WittVector.map_frobeniusPoly`. -/
/-
**WittVector.map_frobeniusPoly.key** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A key numerical identity needed for the proof of `WittVector.map_frobeniusPoly`.
-/
theorem map_frobeniusPoly.key₂ {n i j : ℕ} (hi : i ≤ n) (hj : j < p ^ (n - i)) :
    j - v p (j + 1) + n = i + j + (n - i - v p (j + 1)) := by
  generalize h : v p (j + 1) = m
  rsuffices ⟨h₁, h₂⟩ : m ≤ n - i ∧ m ≤ j
  · rw [tsub_add_eq_add_tsub h₂, add_comm i j, add_tsub_assoc_of_le (h₁.trans (Nat.sub_le n i)),
      add_assoc, tsub_right_comm, add_comm i,
      tsub_add_cancel_of_le (le_tsub_of_add_le_right ((le_tsub_iff_left hi).mp h₁))]
  have hle : p ^ m ≤ j + 1 := h ▸ Nat.le_of_dvd j.succ_pos (pow_multiplicity_dvd _ _)
  exact ⟨(Nat.pow_le_pow_iff_right hp.1.one_lt).1 (hle.trans hj),
     Nat.le_of_lt_succ ((m.lt_pow_self hp.1.one_lt).trans_le hle)⟩
/-
**WittVector.map_frobeniusPoly** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：map_frobeniusPoly (n : Nat) : MvPolynomial.map (Int.castRingHom Rat) (frob
eniusPoly p n) = frobeniusPolyRat p n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WittVector.frobeniusPoly.eq_1`：∀ (p n : ℕ), WittVector.frobeniusPoly p n
 = MvPolynomial.X n ^ p + MvPolynomial.C ↑p * WittVector.frobeniusPolyAux p n
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
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
· 使用定理 `MvPolynomial.map_C`：map_C : forall a : R, map f (C a : MvPolynomial σ R)
 = C (f a)
· 使用定理 `MvPolynomial.map_X`：map_X (n : σ) : map f (X n : MvPolynomial σ R) = X n
· 使用定理 `eq_intCast`：eq_intCast [FunLike F Int α] [RingHomClass F Int α] (f : F) 
(n : Int) : f n = n
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `WittVector.frobeniusPolyRat.eq_1`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)] (n
 : ℕ),   WittVector.frobeniusPolyRat p n = (MvPolynomial.bind₁ (wittPolynomial p
 ℚ ∘ fun n => n + 1)) …
· 使用定理 `Nat.strong_induction_on`：∀ {p : ℕ → Prop} (n : ℕ), (∀ (n : ℕ), (∀ m < n,
 p m) → p n) → p n
· 使用定理 `xInTermsOfW_eq`：xInTermsOfW_eq [Invertible (p : R)] {n : Nat} : xInTerms
OfW p R n = (X n - ∑ i in range n, C ((p : R) ^ i) * xInTermsOfW p R i ^ p ^ (n 
- i)…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `MvPolynomial.bind₁_C_right`：bind₁_C_right (f : σ -> MvPolynomial τ R) (x
) : bind₁ f (C x) = C x
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
（共 181 条，此处仅展示前 30 条）
-/
theorem map_frobeniusPoly (n : ℕ) :
    MvPolynomial.map (Int.castRingHom ℚ) (frobeniusPoly p n) = frobeniusPolyRat p n := by
  rw [frobeniusPoly, map_add, map_mul, map_pow, map_C, map_X, eq_intCast, Int.cast_natCast,
    frobeniusPolyRat]
  refine Nat.strong_induction_on n ?_; clear n
  intro n IH
  rw [xInTermsOfW_eq]
  simp only [map_sum, map_sub, map_mul, map_pow (bind₁ _), bind₁_C_right]
  have h1 : (p : ℚ) ^ n * ⅟(p : ℚ) ^ n = 1 := by rw [← mul_pow, mul_invOf_self, one_pow]
  rw [bind₁_X_right, Function.comp_apply, wittPolynomial_eq_sum_C_mul_X_pow, sum_range_succ,
    sum_range_succ, tsub_self, add_tsub_cancel_left, pow_zero, pow_one, pow_one, sub_mul, add_mul,
    add_mul, mul_right_comm, mul_right_comm (C ((p : ℚ) ^ (n + 1))), ← C_mul, ← C_mul, pow_succ',
    mul_assoc (p : ℚ) ((p : ℚ) ^ n), h1, mul_one, C_1, one_mul, add_comm _ (X n ^ p), add_assoc,
    ← add_sub, add_right_inj, frobeniusPolyAux_eq, map_sub, map_X, mul_sub, sub_eq_add_neg,
    add_comm _ (C (p : ℚ) * X (n + 1)), ← add_sub,
    add_right_inj, neg_eq_iff_eq_neg, neg_sub, eq_comm]
  simp only [map_sum, mul_sum, sum_mul, ← sum_sub_distrib]
  apply sum_congr rfl
  intro i hi
  rw [mem_range] at hi
  rw [← IH i hi]
  clear IH
  rw [add_comm (X i ^ p), add_pow, sum_range_succ', pow_zero, tsub_zero, Nat.choose_zero_right,
    one_mul, Nat.cast_one, mul_one, mul_add, add_mul, Nat.succ_sub (le_of_lt hi),
    Nat.succ_eq_add_one (n - i), pow_succ', pow_mul, add_sub_cancel_right, mul_sum, sum_mul]
  apply sum_congr rfl
  intro j hj
  rw [mem_range] at hj
  rw [map_mul, map_mul, map_pow, map_pow, map_pow, map_pow, map_pow, map_C, map_X, mul_pow]
  rw [mul_comm (C (p : ℚ) ^ i), mul_comm _ ((X i ^ p) ^ _), mul_comm (C (p : ℚ) ^ (j + 1)),
    mul_comm (C (p : ℚ))]
  simp only [mul_assoc]
  apply congr_arg
  apply congr_arg
  rw [← C_eq_coe_nat]
  simp only [← map_pow, ← C_mul]
  rw [C_inj]
  simp only [invOf_eq_inv, eq_intCast, inv_pow, Int.cast_natCast, Nat.cast_mul, Int.cast_mul]
  rw [Rat.natCast_div _ _ (map_frobeniusPoly.key₁ p (n - i) j hj)]
  push_cast
  linear_combination (norm := skip) -p / p ^ n / p ^ (n - i - v p (j + 1))
    * (p ^ (n - i)).choose (j + 1) * congr((p : ℚ) ^ $(map_frobeniusPoly.key₂ p hi.le hj))
  field [hp.1.ne_zero]
/-
**WittVector.frobeniusPoly_zmod** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：frobeniusPoly_zmod (n : Nat) : MvPolynomial.map (Int.castRingHom (ZMod p))
 (frobeniusPoly p n) = X n ^ p
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WittVector.frobeniusPoly.eq_1`：∀ (p n : ℕ), WittVector.frobeniusPoly p n
 = MvPolynomial.X n ^ p + MvPolynomial.C ↑p * WittVector.frobeniusPolyAux p n
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `MvPolynomial.map_X`：map_X (n : σ) : map f (X n : MvPolynomial σ R) = X n
· 使用定理 `MvPolynomial.map_C`：map_C : forall a : R, map f (C a : MvPolynomial σ R)
 = C (f a)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_intCast`：eq_intCast [FunLike F Int α] [RingHomClass F Int α] (f : F) 
(n : Int) : f n = n
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `ZMod.natCast_self`：natCast_self (n : Nat) : (n : ZMod n) = 0
· 使用定理 `MvPolynomial.C_0`：C_0 : C 0 = (0 : MvPolynomial σ R)
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem frobeniusPoly_zmod (n : ℕ) :
    MvPolynomial.map (Int.castRingHom (ZMod p)) (frobeniusPoly p n) = X n ^ p := by
  rw [frobeniusPoly, map_add, map_pow, map_mul, map_X, map_C]
  simp only [Int.cast_natCast, add_zero, eq_intCast, ZMod.natCast_self, zero_mul, C_0]

@[simp]
/-
**WittVector.bind** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bind₁_frobeniusPoly_wittPolynomial (n : ℕ) :
    bind₁ (frobeniusPoly p) (wittPolynomial p ℤ n) = wittPolynomial p ℤ (n + 1) := by
  apply MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
  simp only [map_bind₁, map_frobeniusPoly, bind₁_frobeniusPolyRat_wittPolynomial,
    map_wittPolynomial]

variable {p}

/-- `frobeniusFun` is the function underlying the ring endomorphism
`frobenius : 𝕎 R →+* frobenius 𝕎 R`. -/
/-
**WittVector.frobeniusFun** 是 Mathlib 中的一个定义，位于命名空间 `WittVector`。
形式化陈述：frobeniusFun (x : 𝕎 R) : 𝕎 R
参数：x : 𝕎 R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`frobeniusFun` is the function underlying the ring endomorphism
`frobenius : 𝕎 R →+* frobenius 𝕎 R`.
-/
def frobeniusFun (x : 𝕎 R) : 𝕎 R :=
  mk p fun n => MvPolynomial.aeval x.coeff (frobeniusPoly p n)

omit hp in
/-
**WittVector.coeff_frobeniusFun** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：coeff_frobeniusFun (x : 𝕎 R) (n : Nat) : coeff (frobeniusFun x) n = MvPoly
nomial.aeval x.coeff (frobeniusPoly p n)
参数：x : 𝕎 R；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WittVector.frobeniusFun.eq_1`：∀ {p : ℕ} {R : Type u_1} [inst : CommRing 
R] (x : WittVector p R),   x.frobeniusFun = WittVector.mk p fun n => (MvPolynomi
al.aeval x.coeff) …
· 使用定理 `WittVector.coeff_mk`：coeff_mk (x : Nat -> R) : (mk p x).coeff = x
-/
theorem coeff_frobeniusFun (x : 𝕎 R) (n : ℕ) :
    coeff (frobeniusFun x) n = MvPolynomial.aeval x.coeff (frobeniusPoly p n) := by
  rw [frobeniusFun, coeff_mk]

variable (p) in
/-- `frobeniusFun` is tautologically a polynomial function.

See also `frobenius_isPoly`. -/
/-
**WittVector.frobeniusFun_isPoly** 是 Mathlib 中的一个实例，位于命名空间 `WittVector`。
形式化陈述：frobeniusFun_isPoly : IsPoly p fun R _ Rcr => @frobeniusFun p R _ Rcr
该定义给出了一等式。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `WittVector.coeff_frobeniusFun`：coeff_frobeniusFun (x : 𝕎 R) (n : Nat) : 
coeff (frobeniusFun x) n = MvPolynomial.aeval x.coeff (frobeniusPoly p n)

--- 原说明 ---
`frobeniusFun` is tautologically a polynomial function.

See also `frobenius_isPoly`.
-/
instance frobeniusFun_isPoly : IsPoly p fun R _ Rcr => @frobeniusFun p R _ Rcr :=
  ⟨⟨frobeniusPoly p, by intros; funext n; apply coeff_frobeniusFun⟩⟩

@[ghost_simps]
/-
**WittVector.ghostComponent_frobeniusFun** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：ghostComponent_frobeniusFun (n : Nat) (x : 𝕎 R) : ghostComponent n (froben
iusFun x) = ghostComponent (n + 1) x
参数：n : Nat；x : 𝕎 R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.aeval_bind₁`：aeval_bind₁ [Algebra R S] (f : τ -> S) (g : σ 
-> MvPolynomial τ R) (φ : MvPolynomial σ R) : aeval f (bind₁ g φ) = aeval (fun i
 => aeval f (g…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ghostComponent_frobeniusFun (n : ℕ) (x : 𝕎 R) :
    ghostComponent n (frobeniusFun x) = ghostComponent (n + 1) x := by
  simp only [ghostComponent_apply, frobeniusFun, coeff_mk, ← bind₁_frobeniusPoly_wittPolynomial,
    aeval_bind₁]

/-- If `R` has characteristic `p`, then there is a ring endomorphism
that raises `r : R` to the power `p`.
By applying `WittVector.map` to this endomorphism,
we obtain a ring endomorphism `frobenius R p : 𝕎 R →+* 𝕎 R`.

The underlying function of this morphism is `WittVector.frobeniusFun`.
-/
/-
**WittVector.frobenius** 是 Mathlib 中的一个定义，位于命名空间 `WittVector`。
形式化陈述：frobenius : 𝕎 R ->+* 𝕎 R where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `R` has characteristic `p`, then there is a ring endomorphism
that raises `r : R` to the power `p`.
By applying `WittVector.map` to this endomorphism,
we obtain a ring endomorphism `frobenius R p : 𝕎 R →+* 𝕎 R`.

The underlying function of this morphism is `WittVector.frobeniusFun`.
-/
def frobenius : 𝕎 R →+* 𝕎 R where
  toFun := frobeniusFun
  map_zero' := by
    refine IsPoly.ext (IsPoly.comp (hg := frobeniusFun_isPoly p) (hf := WittVector.zeroIsPoly))
      (IsPoly.comp (hg := WittVector.zeroIsPoly) (hf := frobeniusFun_isPoly p))
      ?_ _ 0
    simp only [Function.comp_apply, map_zero, forall_const]
    ghost_simp
  map_one' := by
    refine
      IsPoly.ext (IsPoly.comp (hg := frobeniusFun_isPoly p) (hf := WittVector.oneIsPoly))
        (IsPoly.comp (hg := WittVector.oneIsPoly) (hf := frobeniusFun_isPoly p)) ?_ _ 0
    simp only [Function.comp_apply, map_one, forall_const]
    ghost_simp
  map_add' := by ghost_calc _ _; ghost_simp
  map_mul' := by ghost_calc _ _; ghost_simp
/-
**WittVector.coeff_frobenius** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：coeff_frobenius (x : 𝕎 R) (n : Nat) : coeff (frobenius x) n = MvPolynomial
.aeval x.coeff (frobeniusPoly p n)
参数：x : 𝕎 R；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WittVector.coeff_frobeniusFun`：coeff_frobeniusFun (x : 𝕎 R) (n : Nat) : 
coeff (frobeniusFun x) n = MvPolynomial.aeval x.coeff (frobeniusPoly p n)
-/
theorem coeff_frobenius (x : 𝕎 R) (n : ℕ) :
    coeff (frobenius x) n = MvPolynomial.aeval x.coeff (frobeniusPoly p n) :=
  coeff_frobeniusFun _ _

@[ghost_simps]
/-
**WittVector.ghostComponent_frobenius** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：ghostComponent_frobenius (n : Nat) (x : 𝕎 R) : ghostComponent n (frobenius
 x) = ghostComponent (n + 1) x
参数：n : Nat；x : 𝕎 R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WittVector.ghostComponent_frobeniusFun`：ghostComponent_frobeniusFun (n :
 Nat) (x : 𝕎 R) : ghostComponent n (frobeniusFun x) = ghostComponent (n + 1) x
-/
theorem ghostComponent_frobenius (n : ℕ) (x : 𝕎 R) :
    ghostComponent n (frobenius x) = ghostComponent (n + 1) x :=
  ghostComponent_frobeniusFun _ _

variable (p)

/-- `frobenius` is tautologically a polynomial function. -/
/-
**WittVector.frobenius_isPoly** 是 Mathlib 中的一个实例，位于命名空间 `WittVector`。
形式化陈述：frobenius_isPoly : IsPoly p fun R _Rcr => @frobenius p R _ _Rcr
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`frobenius` is tautologically a polynomial function.
-/
instance frobenius_isPoly : IsPoly p fun R _Rcr => @frobenius p R _ _Rcr :=
  frobeniusFun_isPoly _

section CharP

variable [CharP R p]

@[simp]
/-
**WittVector.coeff_frobenius_charP** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：coeff_frobenius_charP (x : 𝕎 R) (n : Nat) : coeff (frobenius x) n = x.coef
f n ^ p
参数：x : 𝕎 R；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WittVector.coeff_frobenius`：coeff_frobenius (x : 𝕎 R) (n : Nat) : coeff 
(frobenius x) n = MvPolynomial.aeval x.coeff (frobeniusPoly p n)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MvPolynomial.aeval_eq_eval₂Hom`：aeval_eq_eval₂Hom (p : MvPolynomial σ R)
 : aeval f p = eval₂Hom (algebraMap R S₁) f p
· 使用定理 `MvPolynomial.eval₂Hom_map_hom`：eval₂Hom_map_hom [CommSemiring S₂] (f : R
 ->+* S₁) (g : σ -> S₂) (φ : S₁ ->+* S₂) (p : MvPolynomial σ R) : eval₂Hom φ g (
map f p) = eval₂Hom…
· 使用定理 `MvPolynomial.eval₂Hom_congr`：eval₂Hom_congr {f₁ f₂ : R ->+* S₁} {g₁ g₂ :
 σ -> S₁} {p₁ p₂ : MvPolynomial σ R} : f₁ = f₂ -> g₁ = g₂ -> p₁ = p₂ -> eval₂Hom
 f₁ g₁ p₁ = eval₂…
· 使用定理 `RingHom.ext_int`：ext_int {R : Type*} [NonAssocSemiring R] (f g : Int ->+
* R) : f = g
· 使用定理 `WittVector.frobeniusPoly_zmod`：frobeniusPoly_zmod (n : Nat) : MvPolynomi
al.map (Int.castRingHom (ZMod p)) (frobeniusPoly p n) = X n ^ p
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
· 使用定理 `MvPolynomial.aeval_X`：aeval_X (s : σ) : aeval f (X s : MvPolynomial σ R)
 = f s
-/
theorem coeff_frobenius_charP (x : 𝕎 R) (n : ℕ) : coeff (frobenius x) n = x.coeff n ^ p := by
  rw [coeff_frobenius]
  let : Algebra (ZMod p) R := ZMod.algebra _ _
  -- outline of the calculation, proofs follow below
  calc
    aeval (fun k => x.coeff k) (frobeniusPoly p n) =
        aeval (fun k => x.coeff k)
          (MvPolynomial.map (Int.castRingHom (ZMod p)) (frobeniusPoly p n)) := ?_
    _ = aeval (fun k => x.coeff k) (X n ^ p : MvPolynomial ℕ (ZMod p)) := ?_
    _ = x.coeff n ^ p := ?_
  · conv_rhs => rw [aeval_eq_eval₂Hom, eval₂Hom_map_hom]
    apply eval₂Hom_congr (RingHom.ext_int _ _) rfl rfl
  · rw [frobeniusPoly_zmod]
  · rw [map_pow, aeval_X]
/-
**WittVector.frobenius_eq_map_frobenius** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：frobenius_eq_map_frobenius : @frobenius p R _ _ = map (_root_.frobenius R 
p)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `WittVector.ext`：ext {x y : 𝕎 R} (h : forall n, x.coeff n = y.coeff n) : 
x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WittVector.coeff_frobenius_charP`：coeff_frobenius_charP (x : 𝕎 R) (n : N
at) : coeff (frobenius x) n = x.coeff n ^ p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem frobenius_eq_map_frobenius : @frobenius p R _ _ = map (_root_.frobenius R p) := by
  ext (x n)
  simp only [coeff_frobenius_charP, map_coeff, frobenius_def]

@[simp]
/-
**WittVector.frobenius_zmodp** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：frobenius_zmodp (x : 𝕎 (ZMod p)) : frobenius x = x
参数：x : 𝕎 (ZMod p)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WittVector.coeff_frobenius_charP`：coeff_frobenius_charP (x : 𝕎 R) (n : N
at) : coeff (frobenius x) n = x.coeff n ^ p
· 使用定理 `ZMod.pow_card`：pow_card (x : ZMod p) : x ^ p = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
theorem frobenius_zmodp (x : 𝕎 (ZMod p)) : frobenius x = x := by
  simp only [WittVector.ext_iff, coeff_frobenius_charP, ZMod.pow_card,
    forall_const]

variable (R)

/-- `WittVector.frobenius` as an equiv. -/
@[simps -fullyApplied]
/-
**WittVector.frobeniusEquiv** 是 Mathlib 中的一个定义，位于命名空间 `WittVector`。
形式化陈述：frobeniusEquiv [PerfectRing R p] : WittVector p R ≃+* WittVector p R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`WittVector.frobenius` as an equiv.
-/
def frobeniusEquiv [PerfectRing R p] : WittVector p R ≃+* WittVector p R :=
  { (WittVector.frobenius : WittVector p R →+* WittVector p R) with
    toFun := WittVector.frobenius
    invFun := map (_root_.frobeniusEquiv R p).symm
    left_inv := fun f => ext fun n => by
      rw [frobenius_eq_map_frobenius]
      exact frobeniusEquiv_symm_apply_frobenius R p _
    right_inv := fun f => ext fun n => by
      rw [frobenius_eq_map_frobenius]
      exact frobenius_apply_frobeniusEquiv_symm R p _ }
/-
**WittVector.frobenius_bijective** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：frobenius_bijective [PerfectRing R p] : Function.Bijective (@WittVector.fr
obenius p R _ _)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquiv.bijective`：∀ {R : Type u_4} {S : Type u_5} [inst : Mul R] [ins
t_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S] (e : R ≃+* S),   Function.Bijecti
ve ⇑e
-/
theorem frobenius_bijective [PerfectRing R p] :
    Function.Bijective (@WittVector.frobenius p R _ _) :=
  (frobeniusEquiv p R).bijective

end CharP

end

end WittVector

