/-
Copyright (c) 2020 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
module

public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Cyclotomic polynomials.

For `n : ℕ` and an integral domain `R`, we define a modified version of the `n`-th cyclotomic
polynomial with coefficients in `R`, denoted `cyclotomic' n R`, as `∏ (X - μ)`, where `μ` varies
over the primitive `n`th roots of unity. If there is a primitive `n`th root of unity in `R` then
this is the standard definition. We then define the standard cyclotomic polynomial `cyclotomic n R`
with coefficients in any ring `R`.

## Main definition

* `cyclotomic n R` : the `n`-th cyclotomic polynomial with coefficients in `R`.

## Main results

* `Polynomial.degree_cyclotomic` : The degree of `cyclotomic n` is `totient n`.
* `Polynomial.prod_cyclotomic_eq_X_pow_sub_one` : `X ^ n - 1 = ∏ (cyclotomic i)`, where `i`
  divides `n`.
* `Polynomial.cyclotomic_eq_prod_X_pow_sub_one_pow_moebius` : The Möbius inversion formula for
  `cyclotomic n R` over an abstract fraction field for `R[X]`.

## Implementation details

Our definition of `cyclotomic' n R` makes sense in any integral domain `R`, but the interesting
results hold if there is a primitive `n`-th root of unity in `R`. In particular, our definition is
not the standard one unless there is a primitive `n`th root of unity in `R`. For example,
`cyclotomic' 3 ℤ = 1`, since there are no primitive cube roots of unity in `ℤ`. The main example is
`R = ℂ`, we decided to work in general since the difficulties are essentially the same.
To get the standard cyclotomic polynomials, we use `unique_int_coeff_of_cycl`, with `R = ℂ`,
to get a polynomial with integer coefficients and then we map it to `R[X]`, for any ring `R`.
-/

@[expose] public section


open scoped Polynomial

noncomputable section

universe u

namespace Polynomial

section Cyclotomic'

section IsDomain

variable {R : Type*} [CommRing R] [IsDomain R]

/-- The modified `n`-th cyclotomic polynomial with coefficients in `R`, it is the usual cyclotomic
polynomial if there is a primitive `n`-th root of unity in `R`. -/
/-
**Polynomial.cyclotomic'** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：cyclotomic' (n : Nat) (R : Type*) [CommRing R] [IsDomain R] : R[X]
参数：n : Nat；R : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The modified `n`-th cyclotomic polynomial with coefficients in `R`, it is the us
ual cyclotomic
polynomial if there is a primitive `n`-th root of unity in `R`.
-/
def cyclotomic' (n : ℕ) (R : Type*) [CommRing R] [IsDomain R] : R[X] :=
  ∏ μ ∈ primitiveRoots n R, (X - C μ)

/-- The zeroth modified cyclotomic polynomial is `1`. -/
@[simp]
/-
**Polynomial.cyclotomic'_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ (R : Type u_2) [inst : CommRing R] [inst_1 : IsDomain R], Polynomial.cyc
lotomic' 0 R = 1
参数：R : Type u_2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `primitiveRoots_zero`：primitiveRoots_zero : primitiveRoots 0 R = ∅
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The zeroth modified cyclotomic polynomial is `1`.
-/
theorem cyclotomic'_zero (R : Type*) [CommRing R] [IsDomain R] : cyclotomic' 0 R = 1 := by
  simp only [cyclotomic', Finset.prod_empty, primitiveRoots_zero]

/-- The first modified cyclotomic polynomial is `X - 1`. -/
@[simp]
/-
**Polynomial.cyclotomic'_one** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ (R : Type u_2) [inst : CommRing R] [inst_1 : IsDomain R], Polynomial.cyc
lotomic' 1 R = Polynomial.X - 1
参数：R : Type u_2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `IsPrimitiveRoot.primitiveRoots_one`：primitiveRoots_one : primitiveRoots 
1 R = {(1 : R)}
· 使用定理 `Finset.prod_singleton`：prod_singleton (f : ι -> M) (a : ι) : ∏ x in sing
leton a, f x = f a
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
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The first modified cyclotomic polynomial is `X - 1`.
-/
theorem cyclotomic'_one (R : Type*) [CommRing R] [IsDomain R] : cyclotomic' 1 R = X - 1 := by
  simp only [cyclotomic', Finset.prod_singleton, map_one, IsPrimitiveRoot.primitiveRoots_one]

/-- The second modified cyclotomic polynomial is `X + 1` if the characteristic of `R` is not `2`. -/
-- Cannot be @[simp] because `p` cannot be inferred by `simp`.
/-
**Polynomial.cyclotomic'_two** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ (R : Type u_2) [inst : CommRing R] [inst_1 : IsDomain R] (p : ℕ) [CharP 
R p],   p ≠ 2 → Polynomial.cyclotomic' 2 R = Polynomial.X + 1
参数：R : Type u_2；p : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.cyclotomic'.eq_1`：∀ (n : ℕ) (R : Type u_2) [inst : CommRing R
] [inst_1 : IsDomain R],   Polynomial.cyclotomic' n R = ∏ μ ∈ primitiveRoots n R
, (Polynomial.X -…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mem_primitiveRoots`：mem_primitiveRoots {ζ : R} (h0 : 0 < k) : ζ in primi
tiveRoots k R ↔ IsPrimitiveRoot ζ k
· 使用定理 `two_pos`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : PartialO
rder α] [ZeroLEOneClass α] [NeZero 1] [AddLeftMono α],   0 < 2
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `IsPrimitiveRoot.neg_one`：neg_one (p : Nat) [Nontrivial R] [h : CharP R p
] (hp : p != 2) : IsPrimitiveRoot (-1 : R) 2
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsPrimitiveRoot.eq_neg_one_of_two_right`：eq_neg_one_of_two_right [NoZero
Divisors R] {ζ : R} (h : IsPrimitiveRoot ζ 2) : ζ = -1
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.prod_singleton`：prod_singleton (f : ι -> M) (a : ι) : ∏ x in sing
leton a, f x = f a
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
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
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem cyclotomic'_two (R : Type*) [CommRing R] [IsDomain R] (p : ℕ) [CharP R p] (hp : p ≠ 2) :
    cyclotomic' 2 R = X + 1 := by
  rw [cyclotomic']
  have prim_root_two : primitiveRoots 2 R = {(-1 : R)} := by
    simp only [Finset.eq_singleton_iff_unique_mem, mem_primitiveRoots two_pos]
    exact ⟨IsPrimitiveRoot.neg_one p hp, fun x => IsPrimitiveRoot.eq_neg_one_of_two_right⟩
  simp only [prim_root_two, Finset.prod_singleton, map_neg, map_one, sub_neg_eq_add]

/-- `cyclotomic' n R` is monic. -/
/-
**Polynomial.cyclotomic'.monic** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.cyclotomic'
`。
形式化陈述：∀ (n : ℕ) (R : Type u_2) [inst : CommRing R] [inst_1 : IsDomain R], (Polyn
omial.cyclotomic' n R).Monic
参数：n : ℕ；R : Type u_2；Polynomial.cyclotomic' n R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.monic_prod_of_monic`：monic_prod_of_monic (s : Finset ι) (f : 
ι -> R[X]) (hs : forall i in s, Monic (f i)) : Monic (∏ i in s, f i)
· 使用定理 `Polynomial.monic_X_sub_C`：monic_X_sub_C (x : R) : Monic (X - C x)

--- 原说明 ---
`cyclotomic' n R` is monic.
-/
theorem cyclotomic'.monic (n : ℕ) (R : Type*) [CommRing R] [IsDomain R] :
    (cyclotomic' n R).Monic :=
  monic_prod_of_monic _ _ fun _ _ => monic_X_sub_C _

/-- `cyclotomic' n R` is different from `0`. -/
/-
**Polynomial.cyclotomic'_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ (n : ℕ) (R : Type u_2) [inst : CommRing R] [inst_1 : IsDomain R], Polyno
mial.cyclotomic' n R ≠ 0
参数：n : ℕ；R : Type u_2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.Monic.ne_zero`：∀ {R : Type u} [inst : Semiring R] [Nontrivial
 R] {p : Polynomial R}, p.Monic → p ≠ 0
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `Polynomial.cyclotomic'.monic`：∀ (n : ℕ) (R : Type u_2) [inst : CommRing 
R] [inst_1 : IsDomain R], (Polynomial.cyclotomic' n R).Monic

--- 原说明 ---
`cyclotomic' n R` is different from `0`.
-/
theorem cyclotomic'_ne_zero (n : ℕ) (R : Type*) [CommRing R] [IsDomain R] : cyclotomic' n R ≠ 0 :=
  (cyclotomic'.monic n R).ne_zero

/-- The natural degree of `cyclotomic' n R` is `totient n` if there is a primitive root of
unity in `R`. -/
/-
**Polynomial.natDegree_cyclotomic'** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_cyclotomic' {ζ : R} {n : Nat} (h : IsPrimitiveRoot ζ n) : (cyclo
tomic' n R).natDegree = Nat.totient n
参数：h : IsPrimitiveRoot ζ n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.cyclotomic'.eq_1`：∀ (n : ℕ) (R : Type u_2) [inst : CommRing R
] [inst_1 : IsDomain R],   Polynomial.cyclotomic' n R = ∏ μ ∈ primitiveRoots n R
, (Polynomial.X -…
· 使用定理 `Polynomial.natDegree_prod`：natDegree_prod (h : forall i in s, f i != 0) 
: (∏ i in s, f i).natDegree = ∑ i in s, (f i).natDegree
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Polynomial.X_sub_C_ne_zero`：X_sub_C_ne_zero (r : R) : X - C r != 0
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Polynomial.natDegree_X_sub_C`：natDegree_X_sub_C (x : R) : (X - C x).natD
egree = 1
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `IsPrimitiveRoot.card_primitiveRoots`：card_primitiveRoots {ζ : R} {k : Na
t} (h : IsPrimitiveRoot ζ k) : #(primitiveRoots k R) = φ k
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The natural degree of `cyclotomic' n R` is `totient n` if there is a primitive r
oot of
unity in `R`.
-/
theorem natDegree_cyclotomic' {ζ : R} {n : ℕ} (h : IsPrimitiveRoot ζ n) :
    (cyclotomic' n R).natDegree = Nat.totient n := by
  rw [cyclotomic']
  rw [natDegree_prod (primitiveRoots n R) fun z : R => X - C z]
  · simp only [IsPrimitiveRoot.card_primitiveRoots h, mul_one, natDegree_X_sub_C, Nat.cast_id,
      Finset.sum_const, nsmul_eq_mul]
  intro z _
  exact X_sub_C_ne_zero z

/-- The degree of `cyclotomic' n R` is `totient n` if there is a primitive root of unity in `R`. -/
/-
**Polynomial.degree_cyclotomic'** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degree_cyclotomic' {ζ : R} {n : Nat} (h : IsPrimitiveRoot ζ n) : (cyclotom
ic' n R).degree = Nat.totient n
参数：h : IsPrimitiveRoot ζ n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.degree_eq_natDegree`：degree_eq_natDegree (hp : p != 0) : degr
ee p = (natDegree p : WithBot Nat)
· 使用定理 `Polynomial.cyclotomic'_ne_zero`：∀ (n : ℕ) (R : Type u_2) [inst : CommRin
g R] [inst_1 : IsDomain R], Polynomial.cyclotomic' n R ≠ 0
· 使用定理 `Polynomial.natDegree_cyclotomic'`：natDegree_cyclotomic' {ζ : R} {n : Nat
} (h : IsPrimitiveRoot ζ n) : (cyclotomic' n R).natDegree = Nat.totient n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The degree of `cyclotomic' n R` is `totient n` if there is a primitive root of u
nity in `R`.
-/
theorem degree_cyclotomic' {ζ : R} {n : ℕ} (h : IsPrimitiveRoot ζ n) :
    (cyclotomic' n R).degree = Nat.totient n := by
  simp only [degree_eq_natDegree (cyclotomic'_ne_zero n R), natDegree_cyclotomic' h]

/-- The roots of `cyclotomic' n R` are the primitive `n`-th roots of unity. -/
/-
**Polynomial.roots_of_cyclotomic** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：roots_of_cyclotomic (n : Nat) (R : Type*) [CommRing R] [IsDomain R] : (cyc
lotomic' n R).roots = (primitiveRoots n R).val
参数：n : Nat；R : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.cyclotomic'.eq_1`：∀ (n : ℕ) (R : Type u_2) [inst : CommRing R
] [inst_1 : IsDomain R],   Polynomial.cyclotomic' n R = ∏ μ ∈ primitiveRoots n R
, (Polynomial.X -…
· 使用定理 `Polynomial.roots_prod_X_sub_C`：roots_prod_X_sub_C (s : Finset R) : (s.pr
od fun a => X - C a).roots = s.val

--- 原说明 ---
The roots of `cyclotomic' n R` are the primitive `n`-th roots of unity.
-/
theorem roots_of_cyclotomic (n : ℕ) (R : Type*) [CommRing R] [IsDomain R] :
    (cyclotomic' n R).roots = (primitiveRoots n R).val := by
  rw [cyclotomic']; exact roots_prod_X_sub_C (primitiveRoots n R)

/-- If there is a primitive `n`th root of unity in `K`, then `X ^ n - 1 = ∏ (X - μ)`, where `μ`
varies over the `n`-th roots of unity. -/
/-
**Polynomial.X_pow_sub_one_eq_prod** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：X_pow_sub_one_eq_prod {ζ : R} {n : Nat} (hpos : 0 < n) (h : IsPrimitiveRoo
t ζ n) : X ^ n - 1 = ∏ ζ in nthRootsFinset n (1 : R), (X - C ζ)
参数：hpos : 0 < n；h : IsPrimitiveRoot ζ n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.nthRootsFinset.eq_1`：∀ (n : ℕ) {R : Type u_1} (a : R) [inst :
 CommRing R] [inst_1 : IsDomain R],   Polynomial.nthRootsFinset n a = (Polynomia
l.nthRoots n a).toFi…
· 使用定理 `IsPrimitiveRoot.nthRoots_one_nodup`：nthRoots_one_nodup {ζ : R} {n : Nat}
 (h : IsPrimitiveRoot ζ n) : (nthRoots n (1 : R)).Nodup
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.toFinset_eq`：toFinset_eq {s : Multiset α} (n : Nodup s) : Finse
t.mk s n = s.toFinset
· 使用定理 `Polynomial.nthRoots.eq_1`：∀ {R : Type u} [inst : CommRing R] [inst_1 : I
sDomain R] (n : ℕ) (a : R),   Polynomial.nthRoots n a = (Polynomial.X ^ n - Poly
nomial.C a).ro…
· 使用定理 `Polynomial.monic_X_pow_sub_C`：monic_X_pow_sub_C {R : Type u} [Ring R] (a
 : R) {n : Nat} (h : n != 0) : (X ^ n - C a).Monic
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用定理 `Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq`：prod_multise
t_X_sub_C_of_monic_of_roots_card_eq (hp : p.Monic) (hroots : Multiset.card p.roo
ts = p.natDegree) : (p.roots.map fun a => X - C …
· 使用定理 `Polynomial.natDegree_X_pow_sub_C`：natDegree_X_pow_sub_C {n : Nat} {r : R
} : (X ^ n - C r).natDegree = n
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsPrimitiveRoot.card_nthRoots_one`：card_nthRoots_one {ζ : R} {n : Nat} (
h : IsPrimitiveRoot ζ n) : Multiset.card (nthRoots n (1 : R)) = n

--- 原说明 ---
If there is a primitive `n`th root of unity in `K`, then `X ^ n - 1 = ∏ (X - μ)`
, where `μ`
varies over the `n`-th roots of unity.
-/
theorem X_pow_sub_one_eq_prod {ζ : R} {n : ℕ} (hpos : 0 < n) (h : IsPrimitiveRoot ζ n) :
    X ^ n - 1 = ∏ ζ ∈ nthRootsFinset n (1 : R), (X - C ζ) := by
  classical
  rw [nthRootsFinset, ← Multiset.toFinset_eq (IsPrimitiveRoot.nthRoots_one_nodup h)]
  simp only [Finset.prod_mk]
  rw [nthRoots]
  have hmonic : (X ^ n - C (1 : R)).Monic := monic_X_pow_sub_C (1 : R) (ne_of_lt hpos).symm
  symm
  apply prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmonic
  rw [@natDegree_X_pow_sub_C R _ _ n 1, ← nthRoots]
  exact IsPrimitiveRoot.card_nthRoots_one h

end IsDomain

section Field

variable {K : Type*} [Field K]

/-- `cyclotomic' n K` splits. -/
/-
**Polynomial.cyclotomic'_splits** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ {K : Type u_1} [inst : Field K] (n : ℕ), (Polynomial.cyclotomic' n K).Sp
lits
参数：n : ℕ；Polynomial.cyclotomic' n K。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.Splits.prod`：∀ {R : Type u_1} [inst : CommSemiring R] {ι : Ty
pe u_2} {f : ι → Polynomial R} {s : Finset ι},   (∀ i ∈ s, (f i).Splits) → (∏ i 
∈ s, f i).Sp…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p

--- 原说明 ---
`cyclotomic' n K` splits.
-/
theorem cyclotomic'_splits (n : ℕ) : Splits (cyclotomic' n K) := by
  apply Splits.prod
  intro z _
  simp only [Splits.X_sub_C]

/-- If there is a primitive `n`-th root of unity in `K`, then `X ^ n - 1` splits. -/
/-
**Polynomial.X_pow_sub_one_splits** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：X_pow_sub_one_splits {ζ : K} {n : Nat} (h : IsPrimitiveRoot ζ n) : Splits 
(X ^ n - C (1 : K))
参数：h : IsPrimitiveRoot ζ n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.splits_iff_card_roots`：splits_iff_card_roots : Splits f ↔ f.r
oots.card = f.natDegree
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.nthRoots.eq_1`：∀ {R : Type u} [inst : CommRing R] [inst_1 : I
sDomain R] (n : ℕ) (a : R),   Polynomial.nthRoots n a = (Polynomial.X ^ n - Poly
nomial.C a).ro…
· 使用定理 `IsPrimitiveRoot.card_nthRoots_one`：card_nthRoots_one {ζ : R} {n : Nat} (
h : IsPrimitiveRoot ζ n) : Multiset.card (nthRoots n (1 : R)) = n
· 使用定理 `Polynomial.natDegree_X_pow_sub_C`：natDegree_X_pow_sub_C {n : Nat} {r : R
} : (X ^ n - C r).natDegree = n
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K

--- 原说明 ---
If there is a primitive `n`-th root of unity in `K`, then `X ^ n - 1` splits.
-/
theorem X_pow_sub_one_splits {ζ : K} {n : ℕ} (h : IsPrimitiveRoot ζ n) :
    Splits (X ^ n - C (1 : K)) := by
  rw [splits_iff_card_roots, ← nthRoots, IsPrimitiveRoot.card_nthRoots_one h, natDegree_X_pow_sub_C]

/-- If there is a primitive `n`-th root of unity in `K`, then
`∏ i ∈ Nat.divisors n, cyclotomic' i K = X ^ n - 1`. -/
/-
**Polynomial.prod_cyclotomic'_eq_X_pow_sub_one** 是 Mathlib 中的一个定理，位于命名空间 `Polyno
mial`。
形式化陈述：∀ {K : Type u_2} [inst : CommRing K] [inst_1 : IsDomain K] {ζ : K} {n : ℕ}
,   0 < n → IsPrimitiveRoot ζ n → ∏ i ∈ n.divisors, Polynomial.cyclotomic' i K =
 Polynomial.X ^ n - 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPrimitiveRoot.disjoint`：disjoint {k l : Nat} (h : k != l) : Disjoint (
primitiveRoots k R) (primitiveRoots l R)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.prod_biUnion`：prod_biUnion [DecidableEq ι] {s : Finset κ} {t : κ 
-> Finset ι} (hs : Set.PairwiseDisjoint (↑s) t) : ∏ x in s.biUnion t, f x = ∏ x 
in s, ∏ i…
· 使用定理 `Polynomial.X_pow_sub_one_eq_prod`：X_pow_sub_one_eq_prod {ζ : R} {n : Nat
} (hpos : 0 < n) (h : IsPrimitiveRoot ζ n) : X ^ n - 1 = ∏ ζ in nthRootsFinset n
 (1 : R), (X - C ζ)
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `IsPrimitiveRoot.nthRoots_one_eq_biUnion_primitiveRoots`：nthRoots_one_eq_
biUnion_primitiveRoots [DecidableEq R] {n : Nat} : nthRootsFinset n (1 : R) = (N
at.divisors n).biUnion fun i => primitiveRoo…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If there is a primitive `n`-th root of unity in `K`, then
`∏ i ∈ Nat.divisors n, cyclotomic' i K = X ^ n - 1`.
-/
theorem prod_cyclotomic'_eq_X_pow_sub_one {K : Type*} [CommRing K] [IsDomain K] {ζ : K} {n : ℕ}
    (hpos : 0 < n) (h : IsPrimitiveRoot ζ n) :
    ∏ i ∈ Nat.divisors n, cyclotomic' i K = X ^ n - 1 := by
  classical
  have hd : (n.divisors : Set ℕ).PairwiseDisjoint fun k => primitiveRoots k K :=
    fun x _ y _ hne => IsPrimitiveRoot.disjoint hne
  simp only [X_pow_sub_one_eq_prod hpos h, cyclotomic', ← Finset.prod_biUnion hd,
    IsPrimitiveRoot.nthRoots_one_eq_biUnion_primitiveRoots]

/-- If there is a primitive `n`-th root of unity in `K`, then
`cyclotomic' n K = (X ^ k - 1) /ₘ (∏ i ∈ Nat.properDivisors k, cyclotomic' i K)`. -/
/-
**Polynomial.cyclotomic'_eq_X_pow_sub_one_div** 是 Mathlib 中的一个定理，位于命名空间 `Polynom
ial`。
形式化陈述：∀ {K : Type u_2} [inst : CommRing K] [inst_1 : IsDomain K] {ζ : K} {n : ℕ}
,   0 < n →     IsPrimitiveRoot ζ n →       Polynomial.cyclotomic' n K = (Polyno
mial.X ^ n - 1) /ₘ ∏ i ∈ n.properDivisors, Polynomial.cyclotomic' i K
参数：Polynomial.X ^ n - 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.prod_cyclotomic'_eq_X_pow_sub_one`：∀ {K : Type u_2} [inst : C
ommRing K] [inst_1 : IsDomain K] {ζ : K} {n : ℕ},   0 < n → IsPrimitiveRoot ζ n 
→ ∏ i ∈ n.divisors, Polynomial.cyc…
· 使用定理 `Nat.self_notMem_properDivisors`：self_notMem_properDivisors : n ∉ properD
ivisors n
· 使用定理 `Nat.cons_self_properDivisors`：cons_self_properDivisors (h : n != 0) : co
ns n (properDivisors n) self_notMem_properDivisors = divisors n
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Finset.prod_cons`：prod_cons (h : a ∉ s) : ∏ x in cons a s h, f x = f a *
 ∏ x in s, f x
· 使用定理 `Polynomial.monic_prod_of_monic`：monic_prod_of_monic (s : Finset ι) (f : 
ι -> R[X]) (hs : forall i in s, Monic (f i)) : Monic (∏ i in s, f i)
· 使用定理 `Polynomial.cyclotomic'.monic`：∀ (n : ℕ) (R : Type u_2) [inst : CommRing 
R] [inst_1 : IsDomain R], (Polynomial.cyclotomic' n R).Monic
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Polynomial.div_modByMonic_unique`：div_modByMonic_unique {f g} (q r : R[X
]) (hg : Monic g) (h : r + g * q = f ∧ degree r < degree g) : f /ₘ g = q ∧ f %ₘ 
g = r
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `bot_lt_iff_ne_bot`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : Orde
rBot α] {a : α}, ⊥ < a ↔ a ≠ ⊥
· 使用定理 `Polynomial.Monic.ne_zero`：∀ {R : Type u} [inst : Semiring R] [Nontrivial
 R] {p : Polynomial R}, p.Monic → p ≠ 0
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.degree_eq_bot`：degree_eq_bot : degree p = ⊥ ↔ p = 0

--- 原说明 ---
If there is a primitive `n`-th root of unity in `K`, then
`cyclotomic' n K = (X ^ k - 1) /ₘ (∏ i ∈ Nat.properDivisors k, cyclotomic' i K)`
.
-/
theorem cyclotomic'_eq_X_pow_sub_one_div {K : Type*} [CommRing K] [IsDomain K] {ζ : K} {n : ℕ}
    (hpos : 0 < n) (h : IsPrimitiveRoot ζ n) :
    cyclotomic' n K = (X ^ n - 1) /ₘ ∏ i ∈ Nat.properDivisors n, cyclotomic' i K := by
  rw [← prod_cyclotomic'_eq_X_pow_sub_one hpos h, ← Nat.cons_self_properDivisors hpos.ne',
    Finset.prod_cons]
  have prod_monic : (∏ i ∈ Nat.properDivisors n, cyclotomic' i K).Monic := by
    apply monic_prod_of_monic
    intro i _
    exact cyclotomic'.monic i K
  rw [(div_modByMonic_unique (cyclotomic' n K) 0 prod_monic _).1]
  simp only [degree_zero, zero_add]
  refine ⟨by rw [mul_comm], ?_⟩
  rw [bot_lt_iff_ne_bot]
  intro h
  exact Monic.ne_zero prod_monic (degree_eq_bot.1 h)

/-- If there is a primitive `n`-th root of unity in `K`, then `cyclotomic' n K` comes from a
monic polynomial with integer coefficients. -/
/-
**Polynomial.int_coeff_of_cyclotomic'** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：int_coeff_of_cyclotomic' {K : Type*} [CommRing K] [IsDomain K] {ζ : K} {n 
: Nat} (h : IsPrimitiveRoot ζ n) : exists P : Int[X], map (Int.castRingHom K) P 
= cyclotomic' n K ∧ P.degree = (cyclotomic' n K).degree ∧ P.Monic
参数：h : IsPrimitiveRoot ζ n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.lifts_and_degree_eq_and_monic`：lifts_and_degree_eq_and_monic 
[Nontrivial S] {p : S[X]} (hlifts : p in lifts f) (hp : p.Monic) : exists q : R[
X], map f q = p ∧ q.degree = p…
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `Nat.strong_induction_on`：∀ {p : ℕ → Prop} (n : ℕ), (∀ (n : ℕ), (∀ m < n,
 p m) → p n) → p n
· 使用定理 `Nat.eq_zero_or_pos`：∀ (n : ℕ), n = 0 ∨ n > 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.map_one`：∀ {R : Type u} {S : Type v} [inst : Semiring R] [ins
t_1 : Semiring S] (f : R →+* S), Polynomial.map f 1 = 1
· 使用定理 `Polynomial.cyclotomic'_zero`：∀ (R : Type u_2) [inst : CommRing R] [inst_
1 : IsDomain R], Polynomial.cyclotomic' 0 R = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.monic_prod_of_monic`：monic_prod_of_monic (s : Finset ι) (f : 
ι -> R[X]) (hs : forall i in s, Monic (f i)) : Monic (∏ i in s, f i)
· 使用定理 `Polynomial.cyclotomic'.monic`：∀ (n : ℕ) (R : Type u_2) [inst : CommRing 
R] [inst_1 : IsDomain R], (Polynomial.cyclotomic' n R).Monic
· 使用定理 `Subsemiring.prod_mem`：∀ {R : Type u_1} [inst : CommSemiring R] (s : Subs
emiring R) {ι : Type u_2} {t : Finset ι} {f : ι → R},   (∀ c ∈ t, f c ∈ s) → ∏ i
 ∈ t, f i …
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.mem_properDivisors`：mem_properDivisors {m : Nat} : n in properDiviso
rs m ↔ n ∣ m ∧ n < m
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `IsPrimitiveRoot.pow`：pow {n : Nat} {a b : Nat} (hn : 0 < n) (h : IsPrimi
tiveRoot ζ n) (hprod : n = a * b) : IsPrimitiveRoot (ζ ^ a) b
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Polynomial.prod_cyclotomic'_eq_X_pow_sub_one`：∀ {K : Type u_2} [inst : C
ommRing K] [inst_1 : IsDomain K] {ζ : K} {n : ℕ},   0 < n → IsPrimitiveRoot ζ n 
→ ∏ i ∈ n.divisors, Polynomial.cyc…
· 使用定理 `Nat.self_notMem_properDivisors`：self_notMem_properDivisors : n ∉ properD
ivisors n
· 使用定理 `Nat.cons_self_properDivisors`：cons_self_properDivisors (h : n != 0) : co
ns n (properDivisors n) self_notMem_properDivisors = divisors n
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Finset.prod_cons`：prod_cons (h : a ∉ s) : ∏ x in cons a s h, f x = f a *
 ∏ x in s, f x
· 使用定理 `Polynomial.Monic.ne_zero`：∀ {R : Type u} [inst : Semiring R] [Nontrivial
 R] {p : Polynomial R}, p.Monic → p ≠ 0
· 使用定理 `Polynomial.div_modByMonic_unique`：div_modByMonic_unique {f g} (q r : R[X
]) (hg : Monic g) (h : r + g * q = f ∧ degree r < degree g) : f /ₘ g = q ∧ f %ₘ 
g = r
· 使用定理 `Polynomial.coe_mapRingHom`：coe_mapRingHom (f : R ->+* S) : ⇑(mapRingHom 
f) = map f
（共 35 条，此处仅展示前 30 条）

--- 原说明 ---
If there is a primitive `n`-th root of unity in `K`, then `cyclotomic' n K` come
s from a
monic polynomial with integer coefficients.
-/
theorem int_coeff_of_cyclotomic' {K : Type*} [CommRing K] [IsDomain K] {ζ : K} {n : ℕ}
    (h : IsPrimitiveRoot ζ n) : ∃ P : ℤ[X], map (Int.castRingHom K) P =
      cyclotomic' n K ∧ P.degree = (cyclotomic' n K).degree ∧ P.Monic := by
  refine lifts_and_degree_eq_and_monic ?_ (cyclotomic'.monic n K)
  induction n using Nat.strong_induction_on generalizing ζ with | _ k ihk
  rcases k.eq_zero_or_pos with (rfl | hpos)
  · use 1
    simp only [cyclotomic'_zero, coe_mapRingHom, Polynomial.map_one]
  let B : K[X] := ∏ i ∈ Nat.properDivisors k, cyclotomic' i K
  have Bmo : B.Monic := by
    apply monic_prod_of_monic
    intro i _
    exact cyclotomic'.monic i K
  have Bint : B ∈ lifts (Int.castRingHom K) := by
    refine Subsemiring.prod_mem (lifts (Int.castRingHom K)) ?_
    intro x hx
    have xsmall := (Nat.mem_properDivisors.1 hx).2
    obtain ⟨d, hd⟩ := (Nat.mem_properDivisors.1 hx).1
    rw [mul_comm] at hd
    exact ihk x xsmall (h.pow hpos hd)
  replace Bint := lifts_and_degree_eq_and_monic Bint Bmo
  obtain ⟨B₁, hB₁, _, hB₁mo⟩ := Bint
  let Q₁ : ℤ[X] := (X ^ k - 1) /ₘ B₁
  have huniq : 0 + B * cyclotomic' k K = X ^ k - 1 ∧ (0 : K[X]).degree < B.degree := by
    constructor
    · rw [zero_add, mul_comm, ← prod_cyclotomic'_eq_X_pow_sub_one hpos h, ←
        Nat.cons_self_properDivisors hpos.ne', Finset.prod_cons]
    · simpa only [degree_zero, bot_lt_iff_ne_bot, Ne, degree_eq_bot] using Bmo.ne_zero
  replace huniq := div_modByMonic_unique (cyclotomic' k K) (0 : K[X]) Bmo huniq
  simp only [lifts, RingHom.mem_rangeS]
  use Q₁
  rw [coe_mapRingHom, map_divByMonic (Int.castRingHom K) hB₁mo, hB₁, ← huniq.1]
  simp

/-- If `K` is of characteristic `0` and there is a primitive `n`-th root of unity in `K`,
then `cyclotomic n K` comes from a unique polynomial with integer coefficients. -/
/-
**Polynomial.unique_int_coeff_of_cycl** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：unique_int_coeff_of_cycl {K : Type*} [CommRing K] [IsDomain K] [CharZero K
] {ζ : K} {n : Nat+} (h : IsPrimitiveRoot ζ n) : exists! P : Int[X], map (Int.ca
stRingHom K) P = cyclotomic' n K
参数：h : IsPrimitiveRoot ζ n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.int_coeff_of_cyclotomic'`：int_coeff_of_cyclotomic' {K : Type*
} [CommRing K] [IsDomain K] {ζ : K} {n : Nat} (h : IsPrimitiveRoot ζ n) : exists
 P : Int[X], map (Int.cas…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Polynomial.map_injective`：map_injective (hf : Function.Injective f) : Fu
nction.Injective (map f)
· 使用引理 `Int.cast_injective`：cast_injective : Injective (Int.cast : Int -> α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂

--- 原说明 ---
If `K` is of characteristic `0` and there is a primitive `n`-th root of unity in
 `K`,
then `cyclotomic n K` comes from a unique polynomial with integer coefficients.
-/
theorem unique_int_coeff_of_cycl {K : Type*} [CommRing K] [IsDomain K] [CharZero K] {ζ : K}
    {n : ℕ+} (h : IsPrimitiveRoot ζ n) :
    ∃! P : ℤ[X], map (Int.castRingHom K) P = cyclotomic' n K := by
  obtain ⟨P, hP⟩ := int_coeff_of_cyclotomic' h
  refine ⟨P, hP.1, fun Q hQ => ?_⟩
  apply map_injective (Int.castRingHom K) Int.cast_injective
  rw [hP.1, hQ]

end Field

end Cyclotomic'

section Cyclotomic

/-- The `n`-th cyclotomic polynomial with coefficients in `R`. -/
/-
**Polynomial.cyclotomic** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：cyclotomic (n : Nat) (R : Type*) [Ring R] : R[X]
参数：n : Nat；R : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `n`-th cyclotomic polynomial with coefficients in `R`.
-/
def cyclotomic (n : ℕ) (R : Type*) [Ring R] : R[X] :=
  if h : n = 0 then 1
  else map (Int.castRingHom R) (int_coeff_of_cyclotomic' (Complex.isPrimitiveRoot_exp n h)).choose
/-
**Polynomial.int_cyclotomic_rw** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：int_cyclotomic_rw {n : Nat} (h : n != 0) : cyclotomic n Int = (int_coeff_o
f_cyclotomic' (Complex.isPrimitiveRoot_exp n h)).choose
参数：h : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Polynomial.int_coeff_of_cyclotomic'`：int_coeff_of_cyclotomic' {K : Type*
} [CommRing K] [IsDomain K] {ζ : K} {n : Nat} (h : IsPrimitiveRoot ζ n) : exists
 P : Int[X], map (Int.cas…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Complex.isPrimitiveRoot_exp`：isPrimitiveRoot_exp (n : Nat) (h0 : n != 0)
 : IsPrimitiveRoot (exp (2 * π * I / n)) n
· 使用定理 `Eq.mpr_not`：∀ {p q : Prop}, p = q → ¬q → ¬p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Polynomial.ext`：ext {p q : R[X]} : (forall n, coeff p n = coeff q n) -> 
p = q
· 使用定理 `Polynomial.coeff_map`：coeff_map (n : Nat) : coeff (p.map f) n = f (coeff
 p n)
· 使用定理 `eq_intCast`：eq_intCast [FunLike F Int α] [RingHomClass F Int α] (f : F) 
(n : Int) : f n = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem int_cyclotomic_rw {n : ℕ} (h : n ≠ 0) :
    cyclotomic n ℤ = (int_coeff_of_cyclotomic' (Complex.isPrimitiveRoot_exp n h)).choose := by
  simp only [cyclotomic, h, dif_neg, not_false_iff]
  ext i
  simp only [coeff_map, Int.cast_id, eq_intCast]

/-- `cyclotomic n R` comes from `cyclotomic n ℤ`. -/
/-
**Polynomial.map_cyclotomic_int** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：map_cyclotomic_int (n : Nat) (R : Type*) [Ring R] : map (Int.castRingHom R
) (cyclotomic n Int) = cyclotomic n R
参数：n : Nat；R : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.mpr_not`：∀ {p q : Prop}, p = q → ¬q → ¬p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Polynomial.cyclotomic'.congr_simp`：∀ (n n_1 : ℕ),   n = n_1 →     ∀ (R :
 Type u_2) [inst : CommRing R] [inst_1 : IsDomain R],       Polynomial.cyclotomi
c' n R = Polynomial.cyc…
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `Exists.choose.congr_simp`：∀ {α : Sort u_1} {p p_1 : α → Prop} (e_p : p =
 p_1) (P : ∃ a, p a), P.choose = ⋯.choose
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Polynomial.map_one`：∀ {R : Type u} {S : Type v} [inst : Semiring R] [ins
t_1 : Semiring S] (f : R →+* S), Polynomial.map f 1 = 1
· 使用定理 `of_eq_false`：∀ {p : Prop}, p = False → ¬p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `Int.castRingHom_int`：Int.castRingHom_int : Int.castRingHom Int = RingHom
.id Int
· 使用定理 `Polynomial.map_id`：map_id : p.map (RingHom.id _) = p

--- 原说明 ---
`cyclotomic n R` comes from `cyclotomic n ℤ`.
-/
theorem map_cyclotomic_int (n : ℕ) (R : Type*) [Ring R] :
    map (Int.castRingHom R) (cyclotomic n ℤ) = cyclotomic n R := by
  by_cases hzero : n = 0
  · simp only [hzero, cyclotomic, dif_pos, Polynomial.map_one]
  simp [cyclotomic, hzero]
/-
**Polynomial.int_cyclotomic_spec** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：int_cyclotomic_spec (n : Nat) : map (Int.castRingHom Complex) (cyclotomic 
n Int) = cyclotomic' n Complex ∧ (cyclotomic n Int).degree = (cyclotomic' n Comp
lex).degree ∧ (cyclotomic n Int).Monic
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.mpr_not`：∀ {p q : Prop}, p = q → ¬q → ¬p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Polynomial.cyclotomic'.congr_simp`：∀ (n n_1 : ℕ),   n = n_1 →     ∀ (R :
 Type u_2) [inst : CommRing R] [inst_1 : IsDomain R],       Polynomial.cyclotomi
c' n R = Polynomial.cyc…
· 使用定理 `Polynomial.cyclotomic'_zero`：∀ (R : Type u_2) [inst : CommRing R] [inst_
1 : IsDomain R], Polynomial.cyclotomic' 0 R = 1
· 使用定理 `Polynomial.degree_one`：degree_one : degree (1 : R[X]) = (0 : WithBot Nat
)
· 使用定理 `Complex.instNontrivial`：Nontrivial ℂ
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `Exists.choose.congr_simp`：∀ {α : Sort u_1} {p p_1 : α → Prop} (e_p : p =
 p_1) (P : ∃ a, p a), P.choose = ⋯.choose
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Polynomial.map_one`：∀ {R : Type u} {S : Type v} [inst : Semiring R] [ins
t_1 : Semiring S] (f : R →+* S), Polynomial.map f 1 = 1
· 使用定理 `Polynomial.int_coeff_of_cyclotomic'`：int_coeff_of_cyclotomic' {K : Type*
} [CommRing K] [IsDomain K] {ζ : K} {n : Nat} (h : IsPrimitiveRoot ζ n) : exists
 P : Int[X], map (Int.cas…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Complex.isPrimitiveRoot_exp`：isPrimitiveRoot_exp (n : Nat) (h0 : n != 0)
 : IsPrimitiveRoot (exp (2 * π * I / n)) n
· 使用定理 `Polynomial.int_cyclotomic_rw`：int_cyclotomic_rw {n : Nat} (h : n != 0) :
 cyclotomic n Int = (int_coeff_of_cyclotomic' (Complex.isPrimitiveRoot_exp n h))
.choose
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
theorem int_cyclotomic_spec (n : ℕ) :
    map (Int.castRingHom ℂ) (cyclotomic n ℤ) = cyclotomic' n ℂ ∧
      (cyclotomic n ℤ).degree = (cyclotomic' n ℂ).degree ∧ (cyclotomic n ℤ).Monic := by
  by_cases hzero : n = 0
  · simp only [hzero, cyclotomic, degree_one, monic_one, cyclotomic'_zero, dif_pos,
      Polynomial.map_one, and_self_iff]
  rw [int_cyclotomic_rw hzero]
  exact (int_coeff_of_cyclotomic' (Complex.isPrimitiveRoot_exp n hzero)).choose_spec
/-
**Polynomial.int_cyclotomic_unique** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：int_cyclotomic_unique {n : Nat} {P : Int[X]} (h : map (Int.castRingHom Com
plex) P = cyclotomic' n Complex) : P = cyclotomic n Int
参数：h : map (Int.castRingHom Complex) P = cyclotomic' n Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Polynomial.map_injective`：map_injective (hf : Function.Injective f) : Fu
nction.Injective (map f)
· 使用引理 `Int.cast_injective`：cast_injective : Injective (Int.cast : Int -> α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Polynomial.int_cyclotomic_spec`：int_cyclotomic_spec (n : Nat) : map (Int
.castRingHom Complex) (cyclotomic n Int) = cyclotomic' n Complex ∧ (cyclotomic n
 Int).degree = (cycl…
-/
theorem int_cyclotomic_unique {n : ℕ} {P : ℤ[X]} (h : map (Int.castRingHom ℂ) P = cyclotomic' n ℂ) :
    P = cyclotomic n ℤ := by
  apply map_injective (Int.castRingHom ℂ) Int.cast_injective
  rw [h, (int_cyclotomic_spec n).1]

/-- The definition of `cyclotomic n R` commutes with any ring homomorphism. -/
@[simp]
/-
**Polynomial.map_cyclotomic** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：map_cyclotomic (n : Nat) {R S : Type*} [Ring R] [Ring S] (f : R ->+* S) : 
map f (cyclotomic n R) = cyclotomic n S
参数：n : Nat；f : R ->+* S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.map_cyclotomic_int`：map_cyclotomic_int (n : Nat) (R : Type*) 
[Ring R] : map (Int.castRingHom R) (cyclotomic n Int) = cyclotomic n R
· 使用定理 `Polynomial.map_map`：map_map [Semiring T] (g : S ->+* T) (p : R[X]) : (p.
map f).map g = p.map (g.comp f)
· 使用定理 `RingHom.Int.subsingleton_ringHom`：∀ {R : Type u_5} [inst : NonAssocSemir
ing R], Subsingleton (ℤ →+* R)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Lean.Meta.FastSubsingleton.elim`：∀ {α : Sort u} [h : Meta.FastSubsinglet
on α] (a b : α), a = b

--- 原说明 ---
The definition of `cyclotomic n R` commutes with any ring homomorphism.
-/
theorem map_cyclotomic (n : ℕ) {R S : Type*} [Ring R] [Ring S] (f : R →+* S) :
    map f (cyclotomic n R) = cyclotomic n S := by
  rw [← map_cyclotomic_int n R, ← map_cyclotomic_int n S, map_map]
  have : Subsingleton (ℤ →+* S) := inferInstance
  congr!
/-
**Polynomial.cyclotomic.eval_apply** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.cycloto
mic`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} (q : R) (n : ℕ) [inst : Ring R] [inst_1 : 
Ring S] (f : R →+* S),   Polynomial.eval (f q) (Polynomial.cyclotomic n S) = f (
Polynomial.eval q (Polynomial.cyclotomic n R))
参数：q : R；n : ℕ；f : R →+* S；f q；Polynomial.cyclotomic n S；Polynomial.eval q (Poly
nomial.cyclotomic n R)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.map_cyclotomic`：map_cyclotomic (n : Nat) {R S : Type*} [Ring 
R] [Ring S] (f : R ->+* S) : map f (cyclotomic n R) = cyclotomic n S
· 使用定理 `Polynomial.eval_map`：eval_map (x : S) : (p.map f).eval x = p.eval₂ f x
· 使用定理 `Polynomial.eval₂_at_apply`：eval₂_at_apply {S : Type*} [Semiring S] (f : 
R ->+* S) (r : R) : p.eval₂ f (f r) = f (p.eval r)
-/
theorem cyclotomic.eval_apply {R S : Type*} (q : R) (n : ℕ) [Ring R] [Ring S] (f : R →+* S) :
    eval (f q) (cyclotomic n S) = f (eval q (cyclotomic n R)) := by
  rw [← map_cyclotomic n f, eval_map, eval₂_at_apply]
/-
**Polynomial.cyclotomic.eval_apply_ofReal** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.
cyclotomic`。
形式化陈述：∀ (q : ℝ) (n : ℕ), Polynomial.eval (↑q) (Polynomial.cyclotomic n ℂ) = ↑(Po
lynomial.eval q (Polynomial.cyclotomic n ℝ))
参数：q : ℝ；n : ℕ；↑q；Polynomial.cyclotomic n ℂ；Polynomial.eval q (Polynomial.cyclot
omic n ℝ)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.cyclotomic.eval_apply`：∀ {R : Type u_1} {S : Type u_2} (q : R
) (n : ℕ) [inst : Ring R] [inst_1 : Ring S] (f : R →+* S),   Polynomial.eval (f 
q) (Polynomial.cycloto…
-/
@[simp] theorem cyclotomic.eval_apply_ofReal (q : ℝ) (n : ℕ) :
    eval (q : ℂ) (cyclotomic n ℂ) = (eval q (cyclotomic n ℝ)) :=
  cyclotomic.eval_apply q n (algebraMap ℝ ℂ)

/-- The zeroth cyclotomic polynomial is `1`. -/
@[simp]
/-
**Polynomial.cyclotomic_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：cyclotomic_zero (R : Type*) [Ring R] : cyclotomic 0 R = 1
参数：R : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.mpr_not`：∀ {p q : Prop}, p = q → ¬q → ¬p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc

--- 原说明 ---
The zeroth cyclotomic polynomial is `1`.
-/
theorem cyclotomic_zero (R : Type*) [Ring R] : cyclotomic 0 R = 1 := by
  simp only [cyclotomic, dif_pos]

/-- The first cyclotomic polynomial is `X - 1`. -/
@[simp]
/-
**Polynomial.cyclotomic_one** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：cyclotomic_one (R : Type*) [Ring R] : cyclotomic 1 R = X - 1
参数：R : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.map_sub`：∀ {R : Type u} [inst : Ring R] {p q : Polynomial R} 
{S : Type u_1} [inst_1 : Ring S] (f : R →+* S),   Polynomial.map f (p - q) = Pol
ynomial.…
· 使用定理 `Polynomial.map_X`：map_X : X.map f = X
· 使用定理 `Polynomial.map_one`：∀ {R : Type u} {S : Type v} [inst : Semiring R] [ins
t_1 : Semiring S] (f : R →+* S), Polynomial.map f 1 = 1
· 使用定理 `Polynomial.cyclotomic'_one`：∀ (R : Type u_2) [inst : CommRing R] [inst_1
 : IsDomain R], Polynomial.cyclotomic' 1 R = Polynomial.X - 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.map_cyclotomic_int`：map_cyclotomic_int (n : Nat) (R : Type*) 
[Ring R] : map (Int.castRingHom R) (cyclotomic n Int) = cyclotomic n R
· 使用定理 `Polynomial.int_cyclotomic_unique`：int_cyclotomic_unique {n : Nat} {P : I
nt[X]} (h : map (Int.castRingHom Complex) P = cyclotomic' n Complex) : P = cyclo
tomic n Int

--- 原说明 ---
The first cyclotomic polynomial is `X - 1`.
-/
theorem cyclotomic_one (R : Type*) [Ring R] : cyclotomic 1 R = X - 1 := by
  have hspec : map (Int.castRingHom ℂ) (X - 1) = cyclotomic' 1 ℂ := by
    simp only [cyclotomic'_one, map_X, Polynomial.map_one, Polynomial.map_sub]
  symm
  rw [← map_cyclotomic_int, ← int_cyclotomic_unique hspec]
  simp only [map_X, Polynomial.map_one, Polynomial.map_sub]

/-- `cyclotomic n` is monic. -/
/-
**Polynomial.cyclotomic.monic** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.cyclotomic`。
形式化陈述：∀ (n : ℕ) (R : Type u_1) [inst : Ring R], (Polynomial.cyclotomic n R).Moni
c
参数：n : ℕ；R : Type u_1；Polynomial.cyclotomic n R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.map_cyclotomic_int`：map_cyclotomic_int (n : Nat) (R : Type*) 
[Ring R] : map (Int.castRingHom R) (cyclotomic n Int) = cyclotomic n R
· 使用定理 `Polynomial.Monic.map`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   p.Monic → (Polynomial.ma
p f p).Mon…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Polynomial.int_cyclotomic_spec`：int_cyclotomic_spec (n : Nat) : map (Int
.castRingHom Complex) (cyclotomic n Int) = cyclotomic' n Complex ∧ (cyclotomic n
 Int).degree = (cycl…

--- 原说明 ---
`cyclotomic n` is monic.
-/
theorem cyclotomic.monic (n : ℕ) (R : Type*) [Ring R] : (cyclotomic n R).Monic := by
  rw [← map_cyclotomic_int]
  exact (int_cyclotomic_spec n).2.2.map _

/-- `cyclotomic n` is primitive. -/
/-
**Polynomial.cyclotomic.isPrimitive** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.cyclot
omic`。
形式化陈述：∀ (n : ℕ) (R : Type u_1) [inst : CommRing R], (Polynomial.cyclotomic n R).
IsPrimitive
参数：n : ℕ；R : Type u_1；Polynomial.cyclotomic n R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.Monic.isPrimitive`：∀ {R : Type u_1} [inst : CommSemiring R] {
p : Polynomial R}, p.Monic → p.IsPrimitive
· 使用定理 `Polynomial.cyclotomic.monic`：∀ (n : ℕ) (R : Type u_1) [inst : Ring R], (
Polynomial.cyclotomic n R).Monic

--- 原说明 ---
`cyclotomic n` is primitive.
-/
theorem cyclotomic.isPrimitive (n : ℕ) (R : Type*) [CommRing R] : (cyclotomic n R).IsPrimitive :=
  (cyclotomic.monic n R).isPrimitive

/-- `cyclotomic n R` is different from `0`. -/
/-
**Polynomial.cyclotomic_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：cyclotomic_ne_zero (n : Nat) (R : Type*) [Ring R] [Nontrivial R] : cycloto
mic n R != 0
参数：n : Nat；R : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.Monic.ne_zero`：∀ {R : Type u} [inst : Semiring R] [Nontrivial
 R] {p : Polynomial R}, p.Monic → p ≠ 0
· 使用定理 `Polynomial.cyclotomic.monic`：∀ (n : ℕ) (R : Type u_1) [inst : Ring R], (
Polynomial.cyclotomic n R).Monic

--- 原说明 ---
`cyclotomic n R` is different from `0`.
-/
theorem cyclotomic_ne_zero (n : ℕ) (R : Type*) [Ring R] [Nontrivial R] : cyclotomic n R ≠ 0 :=
  (cyclotomic.monic n R).ne_zero

/-- The degree of `cyclotomic n` is `totient n`. -/
/-
**Polynomial.degree_cyclotomic** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degree_cyclotomic (n : Nat) (R : Type*) [Ring R] [Nontrivial R] : (cycloto
mic n R).degree = Nat.totient n
参数：n : Nat；R : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.map_cyclotomic_int`：map_cyclotomic_int (n : Nat) (R : Type*) 
[Ring R] : map (Int.castRingHom R) (cyclotomic n Int) = cyclotomic n R
· 使用定理 `Polynomial.degree_map_eq_of_leadingCoeff_ne_zero`：degree_map_eq_of_leadi
ngCoeff_ne_zero (f : R ->+* S) (hf : f (leadingCoeff p) != 0) : degree (p.map f)
 = degree p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.Monic.leadingCoeff`：∀ {R : Type u} [inst : Semiring R] {p : P
olynomial R}, p.Monic → p.leadingCoeff = 1
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Polynomial.int_cyclotomic_spec`：int_cyclotomic_spec (n : Nat) : map (Int
.castRingHom Complex) (cyclotomic n Int) = cyclotomic' n Complex ∧ (cyclotomic n
 Int).degree = (cycl…
· 使用定理 `eq_intCast`：eq_intCast [FunLike F Int α] [RingHomClass F Int α] (f : F) 
(n : Int) : f n = n
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.mpr_not`：∀ {p q : Prop}, p = q → ¬q → ¬p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Polynomial.degree_one`：degree_one : degree (1 : R[X]) = (0 : WithBot Nat
)
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `Polynomial.degree_cyclotomic'`：degree_cyclotomic' {ζ : R} {n : Nat} (h :
 IsPrimitiveRoot ζ n) : (cyclotomic' n R).degree = Nat.totient n
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Complex.isPrimitiveRoot_exp`：isPrimitiveRoot_exp (n : Nat) (h0 : n != 0)
 : IsPrimitiveRoot (exp (2 * π * I / n)) n
· 使用定理 `Nat.succ_ne_zero`：∀ (n : ℕ), n.succ ≠ 0
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a

--- 原说明 ---
The degree of `cyclotomic n` is `totient n`.
-/
theorem degree_cyclotomic (n : ℕ) (R : Type*) [Ring R] [Nontrivial R] :
    (cyclotomic n R).degree = Nat.totient n := by
  rw [← map_cyclotomic_int]
  rw [degree_map_eq_of_leadingCoeff_ne_zero (Int.castRingHom R) _]
  · rcases n with - | k
    · simp only [cyclotomic, degree_one, dif_pos, Nat.totient_zero, CharP.cast_eq_zero]
    rw [← degree_cyclotomic' (Complex.isPrimitiveRoot_exp k.succ (Nat.succ_ne_zero k))]
    exact (int_cyclotomic_spec k.succ).2.1
  simp only [(int_cyclotomic_spec n).right.right, eq_intCast, Monic.leadingCoeff, Int.cast_one,
    Ne, not_false_iff, one_ne_zero]

/-- The natural degree of `cyclotomic n` is `totient n`. -/
/-
**Polynomial.natDegree_cyclotomic** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_cyclotomic (n : Nat) (R : Type*) [Ring R] [Nontrivial R] : (cycl
otomic n R).natDegree = Nat.totient n
参数：n : Nat；R : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.natDegree.eq_1`：∀ {R : Type u} [inst : Semiring R] (p : Polyn
omial R), p.natDegree = WithBot.unbotD 0 p.degree
· 使用定理 `Polynomial.degree_cyclotomic`：degree_cyclotomic (n : Nat) (R : Type*) [R
ing R] [Nontrivial R] : (cyclotomic n R).degree = Nat.totient n

--- 原说明 ---
The natural degree of `cyclotomic n` is `totient n`.
-/
theorem natDegree_cyclotomic (n : ℕ) (R : Type*) [Ring R] [Nontrivial R] :
    (cyclotomic n R).natDegree = Nat.totient n := by
  rw [natDegree, degree_cyclotomic]; norm_cast

/-- The natural degree of `cyclotomic n` is at most `totient n`.

If the base ring is nontrivial, then the degree is exactly `φ n`,
otherwise it's zero. -/
/-
**Polynomial.natDegree_cyclotomic_le** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_cyclotomic_le {R : Type*} [Ring R] {n : Nat} : natDegree (cyclot
omic n R) <= n.totient
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.natDegree_of_subsingleton`：natDegree_of_subsingleton [Subsing
leton R] : natDegree p = 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Polynomial.natDegree_cyclotomic`：natDegree_cyclotomic (n : Nat) (R : Typ
e*) [Ring R] [Nontrivial R] : (cyclotomic n R).natDegree = Nat.totient n
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a

--- 原说明 ---
The natural degree of `cyclotomic n` is at most `totient n`.

If the base ring is nontrivial, then the degree is exactly `φ n`,
otherwise it's zero.
-/
lemma natDegree_cyclotomic_le {R : Type*} [Ring R] {n : ℕ} :
    natDegree (cyclotomic n R) ≤ n.totient := by
  nontriviality R
  rw [natDegree_cyclotomic]

/-- The degree of `cyclotomic n R` is positive. -/
/-
**Polynomial.degree_cyclotomic_pos** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degree_cyclotomic_pos (n : Nat) (R : Type*) (hpos : 0 < n) [Ring R] [Nontr
ivial R] : 0 < (cyclotomic n R).degree
参数：n : Nat；R : Type*；hpos : 0 < n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.degree_cyclotomic`：degree_cyclotomic (n : Nat) (R : Type*) [R
ing R] [Nontrivial R] : (cyclotomic n R).degree = Nat.totient n
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `StarOrderedRing.toExistsAddOfLE`：∀ {R : Type u_1} [inst : NonUnitalSemir
ing R] [inst_1 : PartialOrder R] [inst_2 : StarRing R] [StarOrderedRing R],   Ex
istsAddOfLE R
· 使用定理 `Nat.cast_pos`：cast_pos {α} [Semiring α] [PartialOrder α] [IsOrderedRing 
α] [Nontrivial α] {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `WithBot.instIsOrderedRing`：∀ {α : Type u_1} [inst : DecidableEq α] [inst
_1 : CommSemiring α] [inst_2 : PartialOrder α] [IsOrderedRing α]   [inst_4 : Can
onicallyOrdered…
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Nat.totient_pos`：∀ {n : ℕ}, 0 < n.totient ↔ 0 < n

--- 原说明 ---
The degree of `cyclotomic n R` is positive.
-/
theorem degree_cyclotomic_pos (n : ℕ) (R : Type*) (hpos : 0 < n) [Ring R] [Nontrivial R] :
    0 < (cyclotomic n R).degree := by
  rwa [degree_cyclotomic n R, Nat.cast_pos, Nat.totient_pos]

open Finset

/-- `∏ i ∈ Nat.divisors n, cyclotomic i R = X ^ n - 1`. -/
/-
**Polynomial.prod_cyclotomic_eq_X_pow_sub_one** 是 Mathlib 中的一个定理，位于命名空间 `Polynom
ial`。
形式化陈述：prod_cyclotomic_eq_X_pow_sub_one {n : Nat} (hpos : 0 < n) (R : Type*) [Com
mRing R] : ∏ i in Nat.divisors n, cyclotomic i R = X ^ n - 1
参数：hpos : 0 < n；R : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.map_injective`：map_injective (hf : Function.Injective f) : Fu
nction.Injective (map f)
· 使用引理 `Int.cast_injective`：cast_injective : Injective (Int.cast : Int -> α)
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.map_prod`：∀ {R : Type u} {S : Type v} [inst : CommSemiring R]
 [inst_1 : CommSemiring S] (f : R →+* S) {ι : Type u_1}   (g : ι → Polynomial R)
 (s : Fin…
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Polynomial.map_sub`：∀ {R : Type u} [inst : Ring R] {p q : Polynomial R} 
{S : Type u_1} [inst_1 : Ring S] (f : R →+* S),   Polynomial.map f (p - q) = Pol
ynomial.…
· 使用定理 `Polynomial.map_pow`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p :
 Polynomial R} [inst_1 : Semiring S] (f : R →+* S) (n : ℕ),   Polynomial.map f (
p ^ n) =…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.map_X`：map_X : X.map f = X
· 使用定理 `Polynomial.map_one`：∀ {R : Type u} {S : Type v} [inst : Semiring R] [ins
t_1 : Semiring S] (f : R →+* S), Polynomial.map f 1 = 1
· 使用定理 `Polynomial.prod_cyclotomic'_eq_X_pow_sub_one`：∀ {K : Type u_2} [inst : C
ommRing K] [inst_1 : IsDomain K] {ζ : K} {n : ℕ},   0 < n → IsPrimitiveRoot ζ n 
→ ∏ i ∈ n.divisors, Polynomial.cyc…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Complex.isPrimitiveRoot_exp`：isPrimitiveRoot_exp (n : Nat) (h0 : n != 0)
 : IsPrimitiveRoot (exp (2 * π * I / n)) n
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Polynomial.map_cyclotomic_int`：map_cyclotomic_int (n : Nat) (R : Type*) 
[Ring R] : map (Int.castRingHom R) (cyclotomic n Int) = cyclotomic n R
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂

--- 原说明 ---
`∏ i ∈ Nat.divisors n, cyclotomic i R = X ^ n - 1`.
-/
theorem prod_cyclotomic_eq_X_pow_sub_one {n : ℕ} (hpos : 0 < n) (R : Type*) [CommRing R] :
    ∏ i ∈ Nat.divisors n, cyclotomic i R = X ^ n - 1 := by
  have integer : ∏ i ∈ Nat.divisors n, cyclotomic i ℤ = X ^ n - 1 := by
    apply map_injective (Int.castRingHom ℂ) Int.cast_injective
    simp only [Polynomial.map_prod, int_cyclotomic_spec, Polynomial.map_pow, map_X,
      Polynomial.map_one, Polynomial.map_sub]
    exact prod_cyclotomic'_eq_X_pow_sub_one hpos (Complex.isPrimitiveRoot_exp n hpos.ne')
  simpa only [Polynomial.map_prod, map_cyclotomic_int, Polynomial.map_sub, Polynomial.map_one,
    Polynomial.map_pow, Polynomial.map_X] using congr_arg (map (Int.castRingHom R)) integer
/-
**Polynomial.cyclotomic.dvd_X_pow_sub_one** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.
cyclotomic`。
形式化陈述：∀ (n : ℕ) (R : Type u_1) [inst : Ring R], Polynomial.cyclotomic n R ∣ Poly
nomial.X ^ n - 1
参数：n : ℕ；R : Type u_1。
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
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.prod_cyclotomic_eq_X_pow_sub_one`：prod_cyclotomic_eq_X_pow_su
b_one {n : Nat} (hpos : 0 < n) (R : Type*) [CommRing R] : ∏ i in Nat.divisors n,
 cyclotomic i R = X ^ n - 1
· 使用定理 `Finset.dvd_prod_of_mem`：dvd_prod_of_mem (f : ι -> M) {a : ι} {s : Finset
 ι} (ha : a in s) : f a ∣ ∏ i in s, f i
· 使用定理 `Nat.mem_divisors_self`：mem_divisors_self (n : Nat) (h : n != 0) : n in n
.divisors
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Polynomial.map_cyclotomic_int`：map_cyclotomic_int (n : Nat) (R : Type*) 
[Ring R] : map (Int.castRingHom R) (cyclotomic n Int) = cyclotomic n R
· 使用定理 `Polynomial.map_sub`：∀ {R : Type u} [inst : Ring R] {p q : Polynomial R} 
{S : Type u_1} [inst_1 : Ring S] (f : R →+* S),   Polynomial.map f (p - q) = Pol
ynomial.…
· 使用定理 `Polynomial.map_pow`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p :
 Polynomial R} [inst_1 : Semiring S] (f : R →+* S) (n : ℕ),   Polynomial.map f (
p ^ n) =…
· 使用定理 `Polynomial.map_X`：map_X : X.map f = X
· 使用定理 `Polynomial.map_one`：∀ {R : Type u} {S : Type v} [inst : Semiring R] [ins
t_1 : Semiring S] (f : R →+* S), Polynomial.map f 1 = 1
· 使用定理 `Polynomial.map_dvd`：map_dvd (f : R ->+* S) {x y : R[X]} : x ∣ y -> x.map
 f ∣ y.map f
-/
theorem cyclotomic.dvd_X_pow_sub_one (n : ℕ) (R : Type*) [Ring R] :
    cyclotomic n R ∣ X ^ n - 1 := by
  suffices cyclotomic n ℤ ∣ X ^ n - 1 by
    simpa only [map_cyclotomic_int, Polynomial.map_sub, Polynomial.map_one, Polynomial.map_pow,
      Polynomial.map_X] using Polynomial.map_dvd (Int.castRingHom R) this
  rcases n.eq_zero_or_pos with (rfl | hn)
  · simp
  rw [← prod_cyclotomic_eq_X_pow_sub_one hn]
  exact Finset.dvd_prod_of_mem _ (n.mem_divisors_self hn.ne')
/-
**Polynomial.prod_cyclotomic_eq_geom_sum** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：prod_cyclotomic_eq_geom_sum {n : Nat} (h : 0 < n) (R) [CommRing R] : ∏ i i
n n.divisors.erase 1, cyclotomic i R = ∑ i in Finset.range n, X ^ i
参数：h : 0 < n；R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `mul_left_inj'`：mul_left_inj' (hc : c != 0) : a * c = b * c ↔ a = b
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
· 使用定理 `Finset.prod_erase_mul`：prod_erase_mul [DecidableEq ι] (s : Finset ι) (f 
: ι -> M) {a : ι} (h : a in s) : (∏ x in s.erase a, f x) * f a = ∏ x in s, f x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.one_mem_divisors`：one_mem_divisors : 1 in divisors n ↔ n != 0
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Polynomial.cyclotomic_one`：cyclotomic_one (R : Type*) [Ring R] : cycloto
mic 1 R = X - 1
· 使用引理 `geom_sum_mul`：geom_sum_mul (x : R) (n : Nat) : (∑ i in range n, x ^ i) *
 (x - 1) = x ^ n - 1
· 使用定理 `Polynomial.prod_cyclotomic_eq_X_pow_sub_one`：prod_cyclotomic_eq_X_pow_su
b_one {n : Nat} (hpos : 0 < n) (R : Type*) [CommRing R] : ∏ i in Nat.divisors n,
 cyclotomic i R = X ^ n - 1
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.map_prod`：∀ {R : Type u} {S : Type v} [inst : CommSemiring R]
 [inst_1 : CommSemiring S] (f : R →+* S) {ι : Type u_1}   (g : ι → Polynomial R)
 (s : Fin…
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Polynomial.map_cyclotomic_int`：map_cyclotomic_int (n : Nat) (R : Type*) 
[Ring R] : map (Int.castRingHom R) (cyclotomic n Int) = cyclotomic n R
· 使用定理 `Polynomial.map_sum`：∀ {R : Type u} {S : Type v} [inst : Semiring R] [ins
t_1 : Semiring S] (f : R →+* S) {ι : Type u_1}   (g : ι → Polynomial R) (s : Fin
set ι), …
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Polynomial.map_pow`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p :
 Polynomial R} [inst_1 : Semiring S] (f : R →+* S) (n : ℕ),   Polynomial.map f (
p ^ n) =…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.map_X`：map_X : X.map f = X
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem prod_cyclotomic_eq_geom_sum {n : ℕ} (h : 0 < n) (R) [CommRing R] :
    ∏ i ∈ n.divisors.erase 1, cyclotomic i R = ∑ i ∈ Finset.range n, X ^ i := by
  suffices (∏ i ∈ n.divisors.erase 1, cyclotomic i ℤ) = ∑ i ∈ Finset.range n, X ^ i by
    simpa only [Polynomial.map_prod, map_cyclotomic_int, Polynomial.map_sum, Polynomial.map_pow,
      Polynomial.map_X] using congr_arg (map (Int.castRingHom R)) this
  rw [← mul_left_inj' (cyclotomic_ne_zero 1 ℤ), prod_erase_mul _ _ (Nat.one_mem_divisors.2 h.ne'),
    cyclotomic_one, geom_sum_mul, prod_cyclotomic_eq_X_pow_sub_one h]

/-- If `p` is prime, then `cyclotomic p R = ∑ i ∈ range p, X ^ i`. -/
/-
**Polynomial.cyclotomic_prime** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：cyclotomic_prime (R : Type*) [Ring R] (p : Nat) [hp : Fact p.Prime] : cycl
otomic p R = ∑ i in Finset.range p, X ^ i
参数：R : Type*；p : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.prod_cyclotomic_eq_geom_sum`：prod_cyclotomic_eq_geom_sum {n :
 Nat} (h : 0 < n) (R) [CommRing R] : ∏ i in n.divisors.erase 1, cyclotomic i R =
 ∑ i in Finset.range n, X ^ …
· 使用定理 `Nat.Prime.pos`：∀ {p : ℕ}, Nat.Prime p → 0 < p
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `Nat.Prime.divisors`：∀ {p : ℕ}, Nat.Prime p → p.divisors = {1, p}
· 使用定理 `Finset.erase_insert`：erase_insert {a : α} {s : Finset α} (h : a ∉ s) : (
insert a s).erase a = s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Finset.mem_singleton`：mem_singleton {a b : α} : b in ({a} : Finset α) ↔ 
b = a
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Nat.Prime.ne_one`：∀ {p : ℕ}, Nat.Prime p → p ≠ 1
· 使用定理 `Finset.prod_singleton`：prod_singleton (f : ι -> M) (a : ι) : ∏ x in sing
leton a, f x = f a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.map_cyclotomic_int`：map_cyclotomic_int (n : Nat) (R : Type*) 
[Ring R] : map (Int.castRingHom R) (cyclotomic n Int) = cyclotomic n R
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.map_sum`：∀ {R : Type u} {S : Type v} [inst : Semiring R] [ins
t_1 : Semiring S] (f : R →+* S) {ι : Type u_1}   (g : ι → Polynomial R) (s : Fin
set ι), …
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Polynomial.map_pow`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p :
 Polynomial R} [inst_1 : Semiring S] (f : R →+* S) (n : ℕ),   Polynomial.map f (
p ^ n) =…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.map_X`：map_X : X.map f = X
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂

--- 原说明 ---
If `p` is prime, then `cyclotomic p R = ∑ i ∈ range p, X ^ i`.
-/
theorem cyclotomic_prime (R : Type*) [Ring R] (p : ℕ) [hp : Fact p.Prime] :
    cyclotomic p R = ∑ i ∈ Finset.range p, X ^ i := by
  suffices cyclotomic p ℤ = ∑ i ∈ range p, X ^ i by
    simpa only [map_cyclotomic_int, Polynomial.map_sum, Polynomial.map_pow, Polynomial.map_X] using
      congr_arg (map (Int.castRingHom R)) this
  rw [← prod_cyclotomic_eq_geom_sum hp.out.pos, hp.out.divisors,
    erase_insert (mem_singleton.not.2 hp.out.ne_one.symm), prod_singleton]
/-
**Polynomial.cyclotomic_prime_mul_X_sub_one** 是 Mathlib 中的一个定理，位于命名空间 `Polynomia
l`。
形式化陈述：cyclotomic_prime_mul_X_sub_one (R : Type*) [Ring R] (p : Nat) [hn : Fact (
Nat.Prime p)] : cyclotomic p R * (X - 1) = X ^ p - 1
参数：R : Type*；p : Nat；Nat.Prime p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.cyclotomic_prime`：cyclotomic_prime (R : Type*) [Ring R] (p : 
Nat) [hp : Fact p.Prime] : cyclotomic p R = ∑ i in Finset.range p, X ^ i
· 使用引理 `geom_sum_mul`：geom_sum_mul (x : R) (n : Nat) : (∑ i in range n, x ^ i) *
 (x - 1) = x ^ n - 1
-/
theorem cyclotomic_prime_mul_X_sub_one (R : Type*) [Ring R] (p : ℕ) [hn : Fact (Nat.Prime p)] :
    cyclotomic p R * (X - 1) = X ^ p - 1 := by rw [cyclotomic_prime, geom_sum_mul]

@[simp]
/-
**Polynomial.cyclotomic_two** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：cyclotomic_two (R : Type*) [Ring R] : cyclotomic 2 R = X + 1
参数：R : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.cyclotomic_prime`：cyclotomic_prime (R : Type*) [Ring R] (p : 
Nat) [hp : Fact p.Prime] : cyclotomic p R = ∑ i in Finset.range p, X ^ i
· 使用引理 `geom_sum_two`：geom_sum_two {x : R} : ∑ i in range 2, x ^ i = x + 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem cyclotomic_two (R : Type*) [Ring R] : cyclotomic 2 R = X + 1 := by simp [cyclotomic_prime]

@[simp]
/-
**Polynomial.cyclotomic_three** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：cyclotomic_three (R : Type*) [Ring R] : cyclotomic 3 R = X ^ 2 + X + 1
参数：R : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.cyclotomic_prime`：cyclotomic_prime (R : Type*) [Ring R] (p : 
Nat) [hp : Fact p.Prime] : cyclotomic p R = ∑ i in Finset.range p, X ^ i
· 使用定理 `Finset.sum_range_succ'`：∀ {M : Type u_4} [inst : AddCommMonoid M] (f : ℕ
 → M) (n : ℕ),   ∑ k ∈ Finset.range (n + 1), f k = ∑ k ∈ Finset.range n, f (k + 
1) + f 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem cyclotomic_three (R : Type*) [Ring R] : cyclotomic 3 R = X ^ 2 + X + 1 := by
  simp [cyclotomic_prime, sum_range_succ']
/-
**Polynomial.cyclotomic_dvd_geom_sum_of_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Polynomia
l`。
形式化陈述：cyclotomic_dvd_geom_sum_of_dvd (R) [Ring R] {d n : Nat} (hdn : d ∣ n) (hd 
: d != 1) : cyclotomic d R ∣ ∑ i in Finset.range n, X ^ i
参数：R；hdn : d ∣ n；hd : d != 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.eq_zero_or_pos`：∀ (n : ℕ), n = 0 ∨ n > 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.prod_cyclotomic_eq_geom_sum`：prod_cyclotomic_eq_geom_sum {n :
 Nat} (h : 0 < n) (R) [CommRing R] : ∏ i in n.divisors.erase 1, cyclotomic i R =
 ∑ i in Finset.range n, X ^ …
· 使用定理 `Finset.dvd_prod_of_mem`：dvd_prod_of_mem (f : ι -> M) {a : ι} {s : Finset
 ι} (ha : a in s) : f a ∣ ∏ i in s, f i
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Polynomial.map_cyclotomic_int`：map_cyclotomic_int (n : Nat) (R : Type*) 
[Ring R] : map (Int.castRingHom R) (cyclotomic n Int) = cyclotomic n R
· 使用定理 `Polynomial.map_sum`：∀ {R : Type u} {S : Type v} [inst : Semiring R] [ins
t_1 : Semiring S] (f : R →+* S) {ι : Type u_1}   (g : ι → Polynomial R) (s : Fin
set ι), …
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Polynomial.map_pow`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p :
 Polynomial R} [inst_1 : Semiring S] (f : R →+* S) (n : ℕ),   Polynomial.map f (
p ^ n) =…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.map_X`：map_X : X.map f = X
· 使用定理 `Polynomial.map_dvd`：map_dvd (f : R ->+* S) {x y : R[X]} : x ∣ y -> x.map
 f ∣ y.map f
-/
theorem cyclotomic_dvd_geom_sum_of_dvd (R) [Ring R] {d n : ℕ} (hdn : d ∣ n) (hd : d ≠ 1) :
    cyclotomic d R ∣ ∑ i ∈ Finset.range n, X ^ i := by
  suffices cyclotomic d ℤ ∣ ∑ i ∈ Finset.range n, X ^ i by
    simpa only [map_cyclotomic_int, Polynomial.map_sum, Polynomial.map_pow, Polynomial.map_X] using
      map_dvd (Int.castRingHom R) this
  rcases n.eq_zero_or_pos with (rfl | hn)
  · simp
  rw [← prod_cyclotomic_eq_geom_sum hn]
  apply Finset.dvd_prod_of_mem
  simp [hd, hdn, hn.ne']
/-
**Polynomial.X_pow_sub_one_mul_prod_cyclotomic_eq_X_pow_sub_one_of_dvd** 是 Mathl
ib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：X_pow_sub_one_mul_prod_cyclotomic_eq_X_pow_sub_one_of_dvd (R) [CommRing R]
 {d n : Nat} (hdvd : d ∣ n) (hn : n != 0) : ((X ^ d - 1) * ∏ x in n.divisors \ d
.divisors, cyclotomic x R) = X ^ n - 1
参数：R；hdvd : d ∣ n；hn : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.pos_of_dvd_of_pos`：∀ {m n : ℕ}, m ∣ n → 0 < n → 0 < m
· 使用定理 `lt_of_le_of_ne'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≠ b → b < a
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.prod_cyclotomic_eq_X_pow_sub_one`：prod_cyclotomic_eq_X_pow_su
b_one {n : Nat} (hpos : 0 < n) (R : Type*) [CommRing R] : ∏ i in Nat.divisors n,
 cyclotomic i R = X ^ n - 1
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Finset.prod_sdiff`：prod_sdiff [DecidableEq ι] (h : s₁ subseteq s₂) : (∏ 
x in s₂ \ s₁, f x) * ∏ x in s₁, f x = ∏ x in s₂, f x
· 使用定理 `Nat.divisors_subset_of_dvd`：divisors_subset_of_dvd {m : Nat} (hzero : n 
!= 0) (h : m ∣ n) : divisors m subseteq divisors n
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
-/
theorem X_pow_sub_one_mul_prod_cyclotomic_eq_X_pow_sub_one_of_dvd (R) [CommRing R] {d n : ℕ}
    (hdvd : d ∣ n) (hn : n ≠ 0) :
    ((X ^ d - 1) * ∏ x ∈ n.divisors \ d.divisors, cyclotomic x R) = X ^ n - 1 := by
  have h0d : 0 < d := Nat.pos_of_dvd_of_pos hdvd (by positivity)
  rw [← prod_cyclotomic_eq_X_pow_sub_one h0d,
    ← prod_cyclotomic_eq_X_pow_sub_one (by positivity), mul_comm,
    Finset.prod_sdiff (by gcongr)]
/-
**Polynomial.X_pow_sub_one_mul_cyclotomic_dvd_X_pow_sub_one_of_dvd** 是 Mathlib 中
的一个定理，位于命名空间 `Polynomial`。
形式化陈述：X_pow_sub_one_mul_cyclotomic_dvd_X_pow_sub_one_of_dvd (R) [CommRing R] {d 
n : Nat} (h : d in n.properDivisors) : (X ^ d - 1) * cyclotomic n R ∣ X ^ n - 1
参数：R；h : d in n.properDivisors。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.X_pow_sub_one_mul_prod_cyclotomic_eq_X_pow_sub_one_of_dvd`：X_
pow_sub_one_mul_prod_cyclotomic_eq_X_pow_sub_one_of_dvd (R) [CommRing R] {d n : 
Nat} (hdvd : d ∣ n) (hn : n != 0) : ((X ^ d - 1) * ∏ x in …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Nat.mem_properDivisors`：mem_properDivisors {m : Nat} : n in properDiviso
rs m ↔ n ∣ m ∧ n < m
· 使用定理 `LT.lt.ne_bot`：∀ {α : Type u} [inst : Preorder α] [inst_1 : OrderBot α] {
a b : α}, b < a → a ≠ ⊥
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Nat.insert_self_properDivisors`：insert_self_properDivisors (h : n != 0) 
: insert n (properDivisors n) = divisors n
· 使用定理 `Finset.insert_sdiff_of_notMem`：insert_sdiff_of_notMem (s : Finset α) {t 
: Finset α} {x : α} (h : x ∉ t) : insert x s \ t = insert x (s \ t)
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `Nat.divisor_le`：divisor_le {m : Nat} : n in divisors m -> n <= m
· 使用定理 `Finset.prod_insert`：prod_insert [DecidableEq ι] : a ∉ s -> ∏ x in insert
 a s, f x = f a * ∏ x in s, f x
· 使用定理 `Finset.notMem_sdiff_of_notMem_left`：notMem_sdiff_of_notMem_left (h : a ∉
 s) : a ∉ s \ t
· 使用定理 `Nat.self_notMem_properDivisors`：self_notMem_properDivisors : n ∉ properD
ivisors n
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
-/
theorem X_pow_sub_one_mul_cyclotomic_dvd_X_pow_sub_one_of_dvd (R) [CommRing R] {d n : ℕ}
    (h : d ∈ n.properDivisors) : (X ^ d - 1) * cyclotomic n R ∣ X ^ n - 1 := by
  rw [Nat.mem_properDivisors] at h
  use ∏ x ∈ n.properDivisors \ d.divisors, cyclotomic x R
  rw [← X_pow_sub_one_mul_prod_cyclotomic_eq_X_pow_sub_one_of_dvd R h.1 h.2.ne_bot,
    ← Nat.insert_self_properDivisors, Finset.insert_sdiff_of_notMem,
    Finset.prod_insert, mul_assoc]
  · exact Finset.notMem_sdiff_of_notMem_left Nat.self_notMem_properDivisors
  · exact fun hk => h.2.not_ge <| Nat.divisor_le hk
  · exact h.2.ne_bot

section ArithmeticFunction

open ArithmeticFunction

-- access notation `μ`
open scoped ArithmeticFunction.Moebius

/-- `cyclotomic n R` can be expressed as a product in a fraction field of `R[X]`
  using Möbius inversion. -/
/-
**Polynomial.cyclotomic_eq_prod_X_pow_sub_one_pow_moebius** 是 Mathlib 中的一个定理，位于命
名空间 `Polynomial`。
形式化陈述：cyclotomic_eq_prod_X_pow_sub_one_pow_moebius {n : Nat} (R : Type*) [CommRi
ng R] [IsDomain R] : algebraMap _ (RatFunc R) (cyclotomic n R) = ∏ i in n.diviso
rsAntidiagonal, algebraMap R[X] _ (X ^ i.snd - 1) ^ μ i.fst
参数：R : Type*。
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
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Nat.divisorsAntidiagonal_zero`：divisorsAntidiagonal_zero : divisorsAntid
iagonal 0 = ∅
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.prod_cyclotomic_eq_X_pow_sub_one`：prod_cyclotomic_eq_X_pow_su
b_one {n : Nat} (hpos : 0 < n) (R : Type*) [CommRing R] : ∏ i in Nat.divisors n,
 cyclotomic i R = X ^ n - 1
· 使用定理 `map_prod`：map_prod [CommMonoid M] [CommMonoid N] {G : Type*} [FunLike G 
M N] [MonoidHomClass G M N] (g : G) (f : ι -> M) (s : Finset ι) : g (∏ x in s,…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ArithmeticFunction.prod_eq_iff_prod_pow_moebius_eq_of_nonzero`：prod_eq_i
ff_prod_pow_moebius_eq_of_nonzero [CommGroupWithZero R] {f g : Nat -> R} (hf : f
orall n : Nat, 0 < n -> f n != 0) (hg : forall n : …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `RatFunc.instIsFractionRingPolynomial`：∀ (K : Type u) [inst : CommRing K]
 [inst_1 : IsDomain K], IsFractionRing (Polynomial K) (RatFunc K)
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Polynomial.Monic.ne_zero`：∀ {R : Type u} [inst : Semiring R] [Nontrivial
 R] {p : Polynomial R}, p.Monic → p ≠ 0
· 使用定理 `Polynomial.monic_X_pow_sub_C`：monic_X_pow_sub_C {R : Type u} [Ring R] (a
 : R) {n : Nat} (h : n != 0) : (X ^ n - C a).Monic
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
`cyclotomic n R` can be expressed as a product in a fraction field of `R[X]`
  using Möbius inversion.
-/
theorem cyclotomic_eq_prod_X_pow_sub_one_pow_moebius {n : ℕ} (R : Type*) [CommRing R]
    [IsDomain R] : algebraMap _ (RatFunc R) (cyclotomic n R) =
      ∏ i ∈ n.divisorsAntidiagonal, algebraMap R[X] _ (X ^ i.snd - 1) ^ μ i.fst := by
  rcases n.eq_zero_or_pos with (rfl | hpos)
  · simp
  have h : ∀ n : ℕ, 0 < n → (∏ i ∈ Nat.divisors n, algebraMap _ (RatFunc R) (cyclotomic i R)) =
      algebraMap _ _ (X ^ n - 1 : R[X]) := by
    intro n hn
    rw [← prod_cyclotomic_eq_X_pow_sub_one hn R, map_prod]
  rw [(prod_eq_iff_prod_pow_moebius_eq_of_nonzero (fun n hn => _) fun n hn => _).1 h n hpos] <;>
    simp_rw [Ne, IsFractionRing.to_map_eq_zero_iff]
  · simp [cyclotomic_ne_zero]
  · intro n hn
    apply Monic.ne_zero
    apply monic_X_pow_sub_C _ (ne_of_gt hn)

end ArithmeticFunction

/-- We have
`cyclotomic n R = (X ^ k - 1) /ₘ (∏ i ∈ Nat.properDivisors k, cyclotomic i K)`. -/
/-
**Polynomial.cyclotomic_eq_X_pow_sub_one_div** 是 Mathlib 中的一个定理，位于命名空间 `Polynomi
al`。
形式化陈述：cyclotomic_eq_X_pow_sub_one_div {R : Type*} [CommRing R] {n : Nat} (hpos :
 0 < n) : cyclotomic n R = (X ^ n - 1) /ₘ ∏ i in Nat.properDivisors n, cyclotomi
c i R
参数：hpos : 0 < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.prod_cyclotomic_eq_X_pow_sub_one`：prod_cyclotomic_eq_X_pow_su
b_one {n : Nat} (hpos : 0 < n) (R : Type*) [CommRing R] : ∏ i in Nat.divisors n,
 cyclotomic i R = X ^ n - 1
· 使用定理 `Nat.self_notMem_properDivisors`：self_notMem_properDivisors : n ∉ properD
ivisors n
· 使用定理 `Nat.cons_self_properDivisors`：cons_self_properDivisors (h : n != 0) : co
ns n (properDivisors n) self_notMem_properDivisors = divisors n
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Finset.prod_cons`：prod_cons (h : a ∉ s) : ∏ x in cons a s h, f x = f a *
 ∏ x in s, f x
· 使用定理 `Polynomial.monic_prod_of_monic`：monic_prod_of_monic (s : Finset ι) (f : 
ι -> R[X]) (hs : forall i in s, Monic (f i)) : Monic (∏ i in s, f i)
· 使用定理 `Polynomial.cyclotomic.monic`：∀ (n : ℕ) (R : Type u_1) [inst : Ring R], (
Polynomial.cyclotomic n R).Monic
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Polynomial.div_modByMonic_unique`：div_modByMonic_unique {f g} (q r : R[X
]) (hg : Monic g) (h : r + g * q = f ∧ degree r < degree g) : f /ₘ g = q ∧ f %ₘ 
g = r
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `bot_lt_iff_ne_bot`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : Orde
rBot α] {a : α}, ⊥ < a ↔ a ≠ ⊥
· 使用定理 `Polynomial.Monic.ne_zero`：∀ {R : Type u} [inst : Semiring R] [Nontrivial
 R] {p : Polynomial R}, p.Monic → p ≠ 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.degree_eq_bot`：degree_eq_bot : degree p = ⊥ ↔ p = 0

--- 原说明 ---
We have
`cyclotomic n R = (X ^ k - 1) /ₘ (∏ i ∈ Nat.properDivisors k, cyclotomic i K)`.
-/
theorem cyclotomic_eq_X_pow_sub_one_div {R : Type*} [CommRing R] {n : ℕ} (hpos : 0 < n) :
    cyclotomic n R = (X ^ n - 1) /ₘ ∏ i ∈ Nat.properDivisors n, cyclotomic i R := by
  nontriviality R
  rw [← prod_cyclotomic_eq_X_pow_sub_one hpos, ← Nat.cons_self_properDivisors hpos.ne',
    Finset.prod_cons]
  have prod_monic : (∏ i ∈ Nat.properDivisors n, cyclotomic i R).Monic := by
    apply monic_prod_of_monic
    intro i _
    exact cyclotomic.monic i R
  rw [(div_modByMonic_unique (cyclotomic n R) 0 prod_monic _).1]
  simp only [degree_zero, zero_add]
  constructor
  · rw [mul_comm]
  rw [bot_lt_iff_ne_bot]
  intro h
  exact Monic.ne_zero prod_monic (degree_eq_bot.1 h)

/-- If `m` is a proper divisor of `n`, then `X ^ m - 1` divides
`∏ i ∈ Nat.properDivisors n, cyclotomic i R`. -/
/-
**Polynomial.X_pow_sub_one_dvd_prod_cyclotomic** 是 Mathlib 中的一个定理，位于命名空间 `Polyno
mial`。
形式化陈述：X_pow_sub_one_dvd_prod_cyclotomic (R : Type*) [CommRing R] {n m : Nat} (hp
os : 0 < n) (hm : m ∣ n) (hdiff : m != n) : X ^ m - 1 ∣ ∏ i in Nat.properDivisor
s n, cyclotomic i R
参数：R : Type*；hpos : 0 < n；hm : m ∣ n；hdiff : m != n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.mem_properDivisors`：mem_properDivisors {m : Nat} : n in properDiviso
rs m ↔ n ∣ m ∧ n < m
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `Nat.divisor_le`：divisor_le {m : Nat} : n in divisors m -> n <= m
· 使用定理 `Nat.mem_divisors`：mem_divisors {m : Nat} : n in divisors m ↔ n ∣ m ∧ m !
= 0
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sdiff_union_of_subset`：sdiff_union_of_subset {s₁ s₂ : Finset α} (
h : s₁ subseteq s₂) : s₂ \ s₁ union s₁ = s₂
· 使用定理 `Nat.divisors_subset_properDivisors`：divisors_subset_properDivisors {m : 
Nat} (hzero : n != 0) (h : m ∣ n) (hdiff : m != n) : divisors m subseteq properD
ivisors n
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Finset.prod_union`：prod_union [DecidableEq ι] (h : Disjoint s₁ s₂) : ∏ x
 in s₁ union s₂, f x = (∏ x in s₁, f x) * ∏ x in s₂, f x
· 使用定理 `Finset.sdiff_disjoint`：sdiff_disjoint : Disjoint (t \ s) s
· 使用定理 `Polynomial.prod_cyclotomic_eq_X_pow_sub_one`：prod_cyclotomic_eq_X_pow_su
b_one {n : Nat} (hpos : 0 < n) (R : Type*) [CommRing R] : ∏ i in Nat.divisors n,
 cyclotomic i R = X ^ n - 1
· 使用定理 `Nat.pos_of_mem_properDivisors`：pos_of_mem_properDivisors {m : Nat} (h : 
m in n.properDivisors) : 0 < m
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a

--- 原说明 ---
If `m` is a proper divisor of `n`, then `X ^ m - 1` divides
`∏ i ∈ Nat.properDivisors n, cyclotomic i R`.
-/
theorem X_pow_sub_one_dvd_prod_cyclotomic (R : Type*) [CommRing R] {n m : ℕ} (hpos : 0 < n)
    (hm : m ∣ n) (hdiff : m ≠ n) : X ^ m - 1 ∣ ∏ i ∈ Nat.properDivisors n, cyclotomic i R := by
  replace hm := Nat.mem_properDivisors.2
    ⟨hm, lt_of_le_of_ne (Nat.divisor_le (Nat.mem_divisors.2 ⟨hm, hpos.ne'⟩)) hdiff⟩
  rw [← Finset.sdiff_union_of_subset (Nat.divisors_subset_properDivisors (ne_of_lt hpos).symm
    (Nat.mem_properDivisors.1 hm).1 (ne_of_lt (Nat.mem_properDivisors.1 hm).2)),
    Finset.prod_union Finset.sdiff_disjoint,
    prod_cyclotomic_eq_X_pow_sub_one (Nat.pos_of_mem_properDivisors hm)]
  exact ⟨∏ x ∈ n.properDivisors \ m.divisors, cyclotomic x R, by rw [mul_comm]⟩

/-- If there is a primitive `n`-th root of unity in `K`, then
`cyclotomic n K = ∏ μ ∈ primitiveRoots n K, (X - C μ)`. ∈ particular,
`cyclotomic n K = cyclotomic' n K` -/
/-
**Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots** 是 Mathlib 中的一个定理，位于命名空间 `
Polynomial`。
形式化陈述：cyclotomic_eq_prod_X_sub_primitiveRoots {K : Type*} [CommRing K] [IsDomain
 K] {ζ : K} {n : Nat} (hz : IsPrimitiveRoot ζ n) : cyclotomic n K = ∏ μ in primi
tiveRoots n K, (X - C μ)
参数：hz : IsPrimitiveRoot ζ n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.cyclotomic'.eq_1`：∀ (n : ℕ) (R : Type u_2) [inst : CommRing R
] [inst_1 : IsDomain R],   Polynomial.cyclotomic' n R = ∏ μ ∈ primitiveRoots n R
, (Polynomial.X -…
· 使用定理 `Nat.strong_induction_on`：∀ {p : ℕ → Prop} (n : ℕ), (∀ (n : ℕ), (∀ m < n,
 p m) → p n) → p n
· 使用定理 `Nat.eq_zero_or_pos`：∀ (n : ℕ), n = 0 ∨ n > 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Polynomial.cyclotomic_zero`：cyclotomic_zero (R : Type*) [Ring R] : cyclo
tomic 0 R = 1
· 使用定理 `Polynomial.cyclotomic'.congr_simp`：∀ (n n_1 : ℕ),   n = n_1 →     ∀ (R :
 Type u_2) [inst : CommRing R] [inst_1 : IsDomain R],       Polynomial.cyclotomi
c' n R = Polynomial.cyc…
· 使用定理 `Polynomial.cyclotomic'_zero`：∀ (R : Type u_2) [inst : CommRing R] [inst_
1 : IsDomain R], Polynomial.cyclotomic' 0 R = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.mem_properDivisors`：mem_properDivisors {m : Nat} : n in properDiviso
rs m ↔ n ∣ m ∧ n < m
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `IsPrimitiveRoot.pow`：pow {n : Nat} {a b : Nat} (hn : 0 < n) (h : IsPrimi
tiveRoot ζ n) (hprod : n = a * b) : IsPrimitiveRoot (ζ ^ a) b
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Polynomial.cyclotomic_eq_X_pow_sub_one_div`：cyclotomic_eq_X_pow_sub_one_
div {R : Type*} [CommRing R] {n : Nat} (hpos : 0 < n) : cyclotomic n R = (X ^ n 
- 1) /ₘ ∏ i in Nat.properDivisor…
· 使用定理 `Polynomial.cyclotomic'_eq_X_pow_sub_one_div`：∀ {K : Type u_2} [inst : Co
mmRing K] [inst_1 : IsDomain K] {ζ : K} {n : ℕ},   0 < n →     IsPrimitiveRoot ζ
 n →       Polynomial.cyclotomic'…
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用引理 `refl`：refl [Std.Refl r] (a : α) : a ≺ a
· 使用定理 `IsPreorder.toRefl`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsPreorde
r α r], Std.Refl r
· 使用定理 `IsEquiv.toIsPreorder`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsEqui
v α r], IsPreorder α r

--- 原说明 ---
If there is a primitive `n`-th root of unity in `K`, then
`cyclotomic n K = ∏ μ ∈ primitiveRoots n K, (X - C μ)`. ∈ particular,
`cyclotomic n K = cyclotomic' n K`
-/
theorem cyclotomic_eq_prod_X_sub_primitiveRoots {K : Type*} [CommRing K] [IsDomain K] {ζ : K}
    {n : ℕ} (hz : IsPrimitiveRoot ζ n) : cyclotomic n K = ∏ μ ∈ primitiveRoots n K, (X - C μ) := by
  rw [← cyclotomic']
  induction n using Nat.strong_induction_on generalizing ζ with | _ k hk
  obtain hzero | hpos := k.eq_zero_or_pos
  · simp only [hzero, cyclotomic'_zero, cyclotomic_zero]
  have h : ∀ i ∈ k.properDivisors, cyclotomic i K = cyclotomic' i K := by
    intro i hi
    obtain ⟨d, hd⟩ := (Nat.mem_properDivisors.1 hi).1
    rw [mul_comm] at hd
    exact hk i (Nat.mem_properDivisors.1 hi).2 (IsPrimitiveRoot.pow hpos hz hd)
  rw [@cyclotomic_eq_X_pow_sub_one_div _ _ _ hpos, cyclotomic'_eq_X_pow_sub_one_div hpos hz,
    Finset.prod_congr (refl k.properDivisors) h]
/-
**Polynomial.eq_cyclotomic_iff** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：eq_cyclotomic_iff {R : Type*} [CommRing R] {n : Nat} (hpos : 0 < n) (P : R
[X]) : P = cyclotomic n R ↔ (P * ∏ i in Nat.properDivisors n, Polynomial.cycloto
mic i R) = X ^ n - 1
参数：hpos : 0 < n；P : R[X]。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.prod_cyclotomic_eq_X_pow_sub_one`：prod_cyclotomic_eq_X_pow_su
b_one {n : Nat} (hpos : 0 < n) (R : Type*) [CommRing R] : ∏ i in Nat.divisors n,
 cyclotomic i R = X ^ n - 1
· 使用定理 `Nat.self_notMem_properDivisors`：self_notMem_properDivisors : n ∉ properD
ivisors n
· 使用定理 `Nat.cons_self_properDivisors`：cons_self_properDivisors (h : n != 0) : co
ns n (properDivisors n) self_notMem_properDivisors = divisors n
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Finset.prod_cons`：prod_cons (h : a ∉ s) : ∏ x in cons a s h, f x = f a *
 ∏ x in s, f x
· 使用定理 `Polynomial.monic_prod_of_monic`：monic_prod_of_monic (s : Finset ι) (f : 
ι -> R[X]) (hs : forall i in s, Monic (f i)) : Monic (∏ i in s, f i)
· 使用定理 `Polynomial.cyclotomic.monic`：∀ (n : ℕ) (R : Type u_1) [inst : Ring R], (
Polynomial.cyclotomic n R).Monic
· 使用定理 `Polynomial.cyclotomic_eq_X_pow_sub_one_div`：cyclotomic_eq_X_pow_sub_one_
div {R : Type*} [CommRing R] {n : Nat} (hpos : 0 < n) : cyclotomic n R = (X ^ n 
- 1) /ₘ ∏ i in Nat.properDivisor…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Polynomial.div_modByMonic_unique`：div_modByMonic_unique {f g} (q r : R[X
]) (hg : Monic g) (h : r + g * q = f ∧ degree r < degree g) : f /ₘ g = q ∧ f %ₘ 
g = r
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Polynomial.degree_zero`：degree_zero : degree (0 : R[X]) = ⊥
· 使用定理 `bot_lt_iff_ne_bot`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : Orde
rBot α] {a : α}, ⊥ < a ↔ a ≠ ⊥
· 使用定理 `Polynomial.Monic.ne_zero`：∀ {R : Type u} [inst : Semiring R] [Nontrivial
 R] {p : Polynomial R}, p.Monic → p ≠ 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.degree_eq_bot`：degree_eq_bot : degree p = ⊥ ↔ p = 0
-/
theorem eq_cyclotomic_iff {R : Type*} [CommRing R] {n : ℕ} (hpos : 0 < n) (P : R[X]) :
    P = cyclotomic n R ↔
    (P * ∏ i ∈ Nat.properDivisors n, Polynomial.cyclotomic i R) = X ^ n - 1 := by
  nontriviality R
  refine ⟨fun hcycl => ?_, fun hP => ?_⟩
  · rw [hcycl, ← prod_cyclotomic_eq_X_pow_sub_one hpos R, ← Nat.cons_self_properDivisors hpos.ne',
      Finset.prod_cons]
  · have prod_monic : (∏ i ∈ Nat.properDivisors n, cyclotomic i R).Monic := by
      apply monic_prod_of_monic
      intro i _
      exact cyclotomic.monic i R
    rw [@cyclotomic_eq_X_pow_sub_one_div R _ _ hpos, (div_modByMonic_unique P 0 prod_monic _).1]
    refine ⟨by rwa [zero_add, mul_comm], ?_⟩
    rw [degree_zero, bot_lt_iff_ne_bot]
    intro h
    exact Monic.ne_zero prod_monic (degree_eq_bot.1 h)

/-- If `p ^ k` is a prime power, then
`cyclotomic (p ^ (n + 1)) R = ∑ i ∈ range p, (X ^ (p ^ n)) ^ i`. -/
/-
**Polynomial.cyclotomic_prime_pow_eq_geom_sum** 是 Mathlib 中的一个定理，位于命名空间 `Polynom
ial`。
形式化陈述：cyclotomic_prime_pow_eq_geom_sum {R : Type*} [CommRing R] {p n : Nat} (hp 
: p.Prime) : cyclotomic (p ^ (n + 1)) R = ∑ i in Finset.range p, (X ^ p ^ n) ^ i
参数：hp : p.Prime。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.eq_cyclotomic_iff`：eq_cyclotomic_iff {R : Type*} [CommRing R]
 {n : Nat} (hpos : 0 < n) (P : R[X]) : P = cyclotomic n R ↔ (P * ∏ i in Nat.prop
erDivisors n, Poly…
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `Nat.Prime.pos`：∀ {p : ℕ}, Nat.Prime p → 0 < p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Nat.prod_properDivisors_prime_pow`：prod_properDivisors_prime_pow {α : Ty
pe*} [CommMonoid α] {k p : Nat} {f : Nat -> α} (h : p.Prime) : (∏ x in (p ^ k).p
roperDivisors, f x) = ∏…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `Polynomial.cyclotomic_prime`：cyclotomic_prime (R : Type*) [Ring R] (p : 
Nat) [hp : Fact p.Prime] : cyclotomic p R = ∑ i in Finset.range p, X ^ i
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.prod_range_succ`：prod_range_succ (f : Nat -> M) (n : Nat) : (∏ x 
in range (n + 1), f x) = (∏ x in range n, f x) * f n
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用引理 `geom_sum_mul`：geom_sum_mul (x : R) (n : Nat) : (∑ i in range n, x ^ i) *
 (x - 1) = x ^ n - 1
· 使用定理 `sub_left_inj`：∀ {G : Type u_3} [inst : AddGroup G] {a b c : G}, b - a = 
c - a ↔ b = c
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d

--- 原说明 ---
If `p ^ k` is a prime power, then
`cyclotomic (p ^ (n + 1)) R = ∑ i ∈ range p, (X ^ (p ^ n)) ^ i`.
-/
theorem cyclotomic_prime_pow_eq_geom_sum {R : Type*} [CommRing R] {p n : ℕ} (hp : p.Prime) :
    cyclotomic (p ^ (n + 1)) R = ∑ i ∈ Finset.range p, (X ^ p ^ n) ^ i := by
  have : ∀ m, (cyclotomic (p ^ (m + 1)) R = ∑ i ∈ Finset.range p, (X ^ p ^ m) ^ i) ↔
      ((∑ i ∈ Finset.range p, (X ^ p ^ m) ^ i) *
        ∏ x ∈ Finset.range (m + 1), cyclotomic (p ^ x) R) = X ^ p ^ (m + 1) - 1 := by
    intro m
    have := eq_cyclotomic_iff (R := R) (P := ∑ i ∈ range p, (X ^ p ^ m) ^ i)
      (pow_pos hp.pos (m + 1))
    rw [eq_comm] at this
    rw [this, Nat.prod_properDivisors_prime_pow hp]
  induction n with
  | zero => have := Fact.mk hp; simp [cyclotomic_prime]
  | succ n_n n_ih =>
    rw [← (eq_cyclotomic_iff (pow_pos hp.pos (n_n + 1 + 1)) _).mpr ?_]
    rw [Nat.prod_properDivisors_prime_pow hp, Finset.prod_range_succ, n_ih]
    rw [this] at n_ih
    rw [mul_comm _ (∑ i ∈ _, _), n_ih, geom_sum_mul, sub_left_inj, ← pow_mul]
    simp only [pow_add, pow_one]
/-
**Polynomial.cyclotomic_prime_pow_mul_X_pow_sub_one** 是 Mathlib 中的一个定理，位于命名空间 `P
olynomial`。
形式化陈述：cyclotomic_prime_pow_mul_X_pow_sub_one (R : Type*) [CommRing R] (p k : Nat
) [hn : Fact (Nat.Prime p)] : cyclotomic (p ^ (k + 1)) R * (X ^ p ^ k - 1) = X ^
 p ^ (k + 1) - 1
参数：R : Type*；p k : Nat；Nat.Prime p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.cyclotomic_prime_pow_eq_geom_sum`：cyclotomic_prime_pow_eq_geo
m_sum {R : Type*} [CommRing R] {p n : Nat} (hp : p.Prime) : cyclotomic (p ^ (n +
 1)) R = ∑ i in Finset.range p, (…
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用引理 `geom_sum_mul`：geom_sum_mul (x : R) (n : Nat) : (∑ i in range n, x ^ i) *
 (x - 1) = x ^ n - 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem cyclotomic_prime_pow_mul_X_pow_sub_one (R : Type*) [CommRing R] (p k : ℕ)
    [hn : Fact (Nat.Prime p)] :
    cyclotomic (p ^ (k + 1)) R * (X ^ p ^ k - 1) = X ^ p ^ (k + 1) - 1 := by
  rw [cyclotomic_prime_pow_eq_geom_sum hn.out, geom_sum_mul, ← pow_mul, pow_succ, mul_comm]

/-- The constant term of `cyclotomic n R` is `1` if `2 ≤ n`. -/
/-
**Polynomial.cyclotomic_coeff_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：cyclotomic_coeff_zero (R : Type*) [CommRing R] {n : Nat} (hn : 1 < n) : (c
yclotomic n R).coeff 0 = 1
参数：R : Type*；hn : 1 < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.strong_induction_on`：∀ {p : ℕ → Prop} (n : ℕ), (∀ (n : ℕ), (∀ m < n,
 p m) → p n) → p n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.insert_erase`：∀ {α : Type u_1} [inst : DecidableEq α] {s : Finset
 α} {a : α}, a ∈ s → insert a (s.erase a) = s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.one_mem_properDivisors_iff_one_lt`：one_mem_properDivisors_iff_one_lt
 : 1 in n.properDivisors ↔ 1 < n
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `one_lt_two`：one_lt_two [AddLeftStrictMono α] : (1 : α) < 2
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
· 使用定理 `Finset.prod_insert`：prod_insert [DecidableEq ι] : a ∉ s -> ∏ x in insert
 a s, f x = f a * ∏ x in s, f x
· 使用定理 `Finset.notMem_erase`：notMem_erase (a : α) (s : Finset α) : a ∉ erase s a
· 使用定理 `Polynomial.cyclotomic_one`：cyclotomic_one (R : Type*) [Ring R] : cycloto
mic 1 R = X - 1
· 使用定理 `Nat.succ_le_of_lt`：∀ {n m : ℕ}, n < m → n.succ ≤ m
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ne.le_iff_lt`：Ne.le_iff_lt (h : a != b) : a <= b ↔ a < b
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Finset.mem_erase`：mem_erase {a b : α} {s : Finset α} : a in erase s b ↔ 
a != b ∧ a in s
· 使用定理 `Nat.pos_of_mem_properDivisors`：pos_of_mem_properDivisors {m : Nat} (h : 
m in n.properDivisors) : 0 < m
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Nat.mem_properDivisors`：mem_properDivisors {m : Nat} : n in properDiviso
rs m ↔ n ∣ m ∧ n < m
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用引理 `refl`：refl [Std.Refl r] (a : α) : a ≺ a
· 使用定理 `IsPreorder.toRefl`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsPreorde
r α r], Std.Refl r
· 使用定理 `IsEquiv.toIsPreorder`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsEqui
v α r], IsPreorder α r
（共 63 条，此处仅展示前 30 条）

--- 原说明 ---
The constant term of `cyclotomic n R` is `1` if `2 ≤ n`.
-/
theorem cyclotomic_coeff_zero (R : Type*) [CommRing R] {n : ℕ} (hn : 1 < n) :
    (cyclotomic n R).coeff 0 = 1 := by
  induction n using Nat.strong_induction_on with | _ n hi
  have hprod : (∏ i ∈ Nat.properDivisors n, (Polynomial.cyclotomic i R).coeff 0) = -1 := by
    rw [← Finset.insert_erase (Nat.one_mem_properDivisors_iff_one_lt.2
      (lt_of_lt_of_le one_lt_two hn)), Finset.prod_insert (Finset.notMem_erase 1 _),
      cyclotomic_one R]
    have hleq : ∀ j ∈ n.properDivisors.erase 1, 2 ≤ j := by
      intro j hj
      apply Nat.succ_le_of_lt
      exact (Ne.le_iff_lt (Finset.mem_erase.1 hj).1.symm).mp
        (Nat.succ_le_of_lt (Nat.pos_of_mem_properDivisors (Finset.mem_erase.1 hj).2))
    have hcongr : ∀ j ∈ n.properDivisors.erase 1, (cyclotomic j R).coeff 0 = 1 := by
      intro j hj
      exact hi j (Nat.mem_properDivisors.1 (Finset.mem_erase.1 hj).2).2 (hleq j hj)
    have hrw : (∏ x ∈ n.properDivisors.erase 1, (cyclotomic x R).coeff 0) = 1 := by
      rw [Finset.prod_congr (refl (n.properDivisors.erase 1)) hcongr]
      simp only [Finset.prod_const_one]
    simp only [hrw, mul_one, zero_sub, coeff_one_zero, coeff_X_zero, coeff_sub]
  have heq : (X ^ n - 1 : R[X]).coeff 0 = -(cyclotomic n R).coeff 0 := by
    rw [← prod_cyclotomic_eq_X_pow_sub_one (zero_le_one.trans_lt hn), ←
      Nat.cons_self_properDivisors hn.ne_bot, Finset.prod_cons, mul_coeff_zero, coeff_zero_prod,
      hprod, mul_neg, mul_one]
  have hzero : (X ^ n - 1 : R[X]).coeff 0 = (-1 : R) := by
    rw [coeff_zero_eq_eval_zero _]
    simp only [zero_pow (by positivity : n ≠ 0), eval_X, eval_one, zero_sub, eval_pow, eval_sub]
  rw [hzero] at heq
  exact neg_inj.mp (Eq.symm heq)

/-- If `(a : ℕ)` is a root of `cyclotomic n (ZMod p)`, where `p` is a prime, then `a` and `p` are
coprime. -/
/-
**Polynomial.coprime_of_root_cyclotomic** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：coprime_of_root_cyclotomic {n : Nat} (hpos : 0 < n) {p : Nat} [hprime : Fa
ct p.Prime] {a : Nat} (hroot : IsRoot (cyclotomic n (ZMod p)) (Nat.castRingHom (
ZMod p) a)) : a.Coprime p
参数：hpos : 0 < n；hroot : IsRoot (cyclotomic n (ZMod p)) (Nat.castRingHom (ZMod p)
 a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.Coprime.symm`：∀ {n m : ℕ}, n.Coprime m → m.Coprime n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.Prime.coprime_iff_not_dvd`：∀ {p n : ℕ}, Nat.Prime p → (p.Coprime n ↔
 ¬p ∣ n)
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ZMod.natCast_eq_zero_iff`：natCast_eq_zero_iff (a b : Nat) : (a : ZMod b)
 = 0 ↔ b ∣ a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Polynomial.cyclotomic_one`：cyclotomic_one (R : Type*) [Ring R] : cycloto
mic 1 R = X - 1
· 使用定理 `Polynomial.coeff_sub`：coeff_sub (p q : R[X]) (n : Nat) : coeff (p - q) n
 = coeff p n - coeff q n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.coeff_X_zero`：coeff_X_zero : coeff (X : R[X]) 0 = 0
· 使用定理 `Polynomial.coeff_one_zero`：coeff_one_zero : coeff (1 : R[X]) 0 = 1
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.coeff_zero_eq_eval_zero`：coeff_zero_eq_eval_zero (p : R[X]) :
 coeff p 0 = p.eval 0
· 使用定理 `eq_natCast`：eq_natCast [FunLike F Nat R] [RingHomClass F Nat R] (f : F) 
: forall n, f n = n
· 使用定理 `Polynomial.IsRoot.def`：∀ {R : Type u} {a : R} [inst : Semiring R] {p : P
olynomial R}, p.IsRoot a ↔ Polynomial.eval a p = 0
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `Polynomial.cyclotomic_coeff_zero`：cyclotomic_coeff_zero (R : Type*) [Com
mRing R] {n : Nat} (hn : 1 < n) : (cyclotomic n R).coeff 0 = 1
· 使用定理 `Nat.succ_le_of_lt`：∀ {n m : ℕ}, n < m → n.succ ≤ m
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a

--- 原说明 ---
If `(a : ℕ)` is a root of `cyclotomic n (ZMod p)`, where `p` is a prime, then `a
` and `p` are
coprime.
-/
theorem coprime_of_root_cyclotomic {n : ℕ} (hpos : 0 < n) {p : ℕ} [hprime : Fact p.Prime] {a : ℕ}
    (hroot : IsRoot (cyclotomic n (ZMod p)) (Nat.castRingHom (ZMod p) a)) : a.Coprime p := by
  apply Nat.Coprime.symm
  rw [hprime.1.coprime_iff_not_dvd]
  intro h
  replace h := (ZMod.natCast_eq_zero_iff a p).2 h
  rw [IsRoot.def, eq_natCast, h, ← coeff_zero_eq_eval_zero] at hroot
  by_cases hone : n = 1
  · simp only [hone, cyclotomic_one, zero_sub, coeff_one_zero, coeff_X_zero, neg_eq_zero,
      one_ne_zero, coeff_sub] at hroot
  rw [cyclotomic_coeff_zero (ZMod p) (Nat.succ_le_of_lt
    (lt_of_le_of_ne (Nat.succ_le_of_lt hpos) (Ne.symm hone)))] at hroot
  exact one_ne_zero hroot

end Cyclotomic

section Order

/-- If `(a : ℕ)` is a root of `cyclotomic n (ZMod p)`, then the multiplicative order of `a` modulo
`p` divides `n`. -/
/-
**Polynomial.orderOf_root_cyclotomic_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：orderOf_root_cyclotomic_dvd {n : Nat} (hpos : 0 < n) {p : Nat} [Fact p.Pri
me] {a : Nat} (hroot : IsRoot (cyclotomic n (ZMod p)) (Nat.castRingHom (ZMod p) 
a)) : orderOf (ZMod.unitOfCoprime a (coprime_of_root_cyclotomic hpos hroot)) ∣ n
参数：hpos : 0 < n；hroot : IsRoot (cyclotomic n (ZMod p)) (Nat.castRingHom (ZMod p)
 a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `orderOf_dvd_of_pow_eq_one`：orderOf_dvd_of_pow_eq_one (h : x ^ n = 1) : o
rderOf x ∣ n
· 使用定理 `Polynomial.coprime_of_root_cyclotomic`：coprime_of_root_cyclotomic {n : N
at} (hpos : 0 < n) {p : Nat} [hprime : Fact p.Prime] {a : Nat} (hroot : IsRoot (
cyclotomic n (ZMod p)) (Nat…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.prod_cyclotomic_eq_X_pow_sub_one`：prod_cyclotomic_eq_X_pow_su
b_one {n : Nat} (hpos : 0 < n) (R : Type*) [CommRing R] : ∏ i in Nat.divisors n,
 cyclotomic i R = X ^ n - 1
· 使用定理 `Nat.self_notMem_properDivisors`：self_notMem_properDivisors : n ∉ properD
ivisors n
· 使用定理 `Nat.cons_self_properDivisors`：cons_self_properDivisors (h : n != 0) : co
ns n (properDivisors n) self_notMem_properDivisors = divisors n
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Finset.prod_cons`：prod_cons (h : a ∉ s) : ∏ x in cons a s h, f x = f a *
 ∏ x in s, f x
· 使用定理 `Polynomial.eval_mul`：eval_mul : (p * q).eval x = p.eval x * q.eval x
· 使用定理 `Polynomial.IsRoot.def`：∀ {R : Type u} {a : R} [inst : Semiring R] {p : P
olynomial R}, p.IsRoot a ↔ Polynomial.eval a p = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Units.val_eq_one`：val_eq_one {a : αˣ} : (a : α) = 1 ↔ a = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `eq_natCast`：eq_natCast [FunLike F Nat R] [RingHomClass F Nat R] (f : F) 
: forall n, f n = n
· 使用定理 `Polynomial.eval_sub`：eval_sub (p q : R[X]) (x : R) : (p - q).eval x = p.
eval x - q.eval x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.eval_pow`：eval_pow (n : Nat) : (p ^ n).eval x = p.eval x ^ n
· 使用定理 `Polynomial.eval_X`：eval_X : X.eval x = x
· 使用定理 `Polynomial.eval_one`：eval_one : (1 : R[X]).eval x = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `(a : ℕ)` is a root of `cyclotomic n (ZMod p)`, then the multiplicative order
 of `a` modulo
`p` divides `n`.
-/
theorem orderOf_root_cyclotomic_dvd {n : ℕ} (hpos : 0 < n) {p : ℕ} [Fact p.Prime] {a : ℕ}
    (hroot : IsRoot (cyclotomic n (ZMod p)) (Nat.castRingHom (ZMod p) a)) :
    orderOf (ZMod.unitOfCoprime a (coprime_of_root_cyclotomic hpos hroot)) ∣ n := by
  apply orderOf_dvd_of_pow_eq_one
  suffices hpow : eval (Nat.castRingHom (ZMod p) a) (X ^ n - 1 : (ZMod p)[X]) = 0 by
    simp only [eval_X, eval_one, eval_pow, eval_sub, eq_natCast] at hpow
    apply Units.val_eq_one.1
    simp only [sub_eq_zero.mp hpow, ZMod.coe_unitOfCoprime, Units.val_pow_eq_pow_val]
  rw [IsRoot.def] at hroot
  rw [← prod_cyclotomic_eq_X_pow_sub_one hpos (ZMod p), ← Nat.cons_self_properDivisors hpos.ne',
    Finset.prod_cons, eval_mul, hroot, zero_mul]

end Order

section miscellaneous

open Finset

variable {R : Type*} [CommRing R] {ζ : R} {n : ℕ} (x y : R)

/-
**Polynomial.dvd_C_mul_X_sub_one_pow_add_one** 是 Mathlib 中的一个引理，位于命名空间 `Polynomi
al`。
形式化陈述：dvd_C_mul_X_sub_one_pow_add_one {p : Nat} (hpri : p.Prime) (hp : p != 2) (
a r : R) (h₁ : r ∣ a ^ p) (h₂ : r ∣ p * a) : C r ∣ (C a * X - 1) ^ p + 1
参数：hpri : p.Prime；hp : p != 2；a r : R；h₁ : r ∣ a ^ p；h₂ : r ∣ p * a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.Prime.dvd_add_pow_sub_pow_of_dvd`：Nat.Prime.dvd_add_pow_sub_pow_of_d
vd (hpri : p.Prime) {r : R} (h₁ : r ∣ x ^ p) (h₂ : r ∣ p * x) : r ∣ (x + y) ^ p 
- y ^ p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_pow`：mul_pow {ea₁ b c₁ : Nat} {xa₁ : R} (_ : ea₁ * b = c₁) (_ : a₂ ^
 b = c₂) : (xa₁ ^ ea₁ * a₂ : R) ^ b = xa₁ ^ c₁ * c₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Dvd.dvd.trans`：∀ {α : Type u_1} [inst : Semigroup α] {a b c : α}, a ∣ b 
→ b ∣ c → a ∣ c
· 使用定理 `map_dvd`：∀ {M : Type u_1} {N : Type u_2} [inst : Semigroup M] [inst_1 : 
Semigroup N] {F : Type u_3} [inst_2 : FunLike F M N]   [MulHomClass F M N] (f…
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `map_natCast`：map_natCast [FunLike F R S] [RingHomClass F R S] (f : F) : 
forall n : Nat, f (n : R) = n
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用引理 `Odd.neg_pow`：Odd.neg_pow : Odd n -> forall a : α, (-a) ^ n = -a ^ n
· 使用定理 `Nat.Prime.odd_of_ne_two`：∀ {p : ℕ}, Nat.Prime p → p ≠ 2 → Odd p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
-/
lemma dvd_C_mul_X_sub_one_pow_add_one {p : ℕ} (hpri : p.Prime)
    (hp : p ≠ 2) (a r : R) (h₁ : r ∣ a ^ p) (h₂ : r ∣ p * a) : C r ∣ (C a * X - 1) ^ p + 1 := by
  have := hpri.dvd_add_pow_sub_pow_of_dvd (C a * X) (-1) (r := C r) ?_ ?_
  · rwa [← sub_eq_add_neg, (hpri.odd_of_ne_two hp).neg_pow, one_pow, sub_neg_eq_add] at this
  · simp only [mul_pow, ← map_pow, dvd_mul_right, (_root_.map_dvd C h₁).trans]
  simp only [map_mul, map_natCast, ← mul_assoc, dvd_mul_right, (_root_.map_dvd C h₂).trans]
/-
**Polynomial._root_.IsPrimitiveRoot.pow_sub_pow_eq_prod_sub_mul_field** 是 Mathli
b 中的一个定理，位于命名空间 `Polynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem _root_.IsPrimitiveRoot.pow_sub_pow_eq_prod_sub_mul_field {K : Type*}
    [Field K] {ζ : K} (x y : K) (hpos : 0 < n) (h : IsPrimitiveRoot ζ n) :
    x ^ n - y ^ n = ∏ ζ ∈ nthRootsFinset n (1 : K), (x - ζ * y) := by
  by_cases hy : y = 0
  · simp only [hy, zero_pow (Nat.ne_zero_of_lt hpos), sub_zero, mul_zero, prod_const]
    congr
    rw [h.card_nthRootsFinset]
  convert!
    congr_arg (eval (x / y) · * y ^ card (nthRootsFinset n (1 : K))) <|
      X_pow_sub_one_eq_prod hpos h using 1
  · simp [sub_mul, div_pow, hy, h.card_nthRootsFinset]
  · simp [eval_prod, prod_mul_pow_card, sub_mul, hy]

variable [IsDomain R]

/-- If there is a primitive `n`th root of unity in `R`, then `X ^ n - Y ^ n = ∏ (X - μ Y)`,
where `μ` varies over the `n`-th roots of unity. -/
/-
**Polynomial._root_.IsPrimitiveRoot.pow_sub_pow_eq_prod_sub_mul** 是 Mathlib 中的一个
定理，位于命名空间 `Polynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If there is a primitive `n`th root of unity in `R`, then `X ^ n - Y ^ n = ∏ (X -
 μ Y)`,
where `μ` varies over the `n`-th roots of unity.
-/
theorem _root_.IsPrimitiveRoot.pow_sub_pow_eq_prod_sub_mul (hpos : 0 < n)
    (h : IsPrimitiveRoot ζ n) : x ^ n - y ^ n = ∏ ζ ∈ nthRootsFinset n (1 : R), (x - ζ * y) := by
  let K := FractionRing R
  apply FaithfulSMul.algebraMap_injective R K
  rw [map_sub, map_pow, map_pow, map_prod]
  simp_rw [map_sub, map_mul]
  have h' : IsPrimitiveRoot (algebraMap R K ζ) n :=
    h.map_of_injective <| FaithfulSMul.algebraMap_injective R K
  rw [h'.pow_sub_pow_eq_prod_sub_mul_field _ _ hpos]
  refine (prod_nbij (algebraMap R K) (fun a ha ↦ map_mem_nthRootsFinset_one ha _)
    (fun a _ b _ H ↦ FaithfulSMul.algebraMap_injective R K H) (fun a ha ↦ ?_) (fun _ _ ↦ rfl)).symm
  have := Set.surj_on_of_inj_on_of_ncard_le (s := nthRootsFinset n (1 : R))
    (t := nthRootsFinset n (1 : K)) _ (fun _ hr ↦ map_mem_nthRootsFinset_one hr _)
    (fun a _ b _ H ↦ FaithfulSMul.algebraMap_injective R K H)
    (by simp [h.card_nthRootsFinset, h'.card_nthRootsFinset])
  obtain ⟨x, hx, hx1⟩ := this _ ha
  exact ⟨x, hx, hx1.symm⟩

/-- If there is a primitive `n`th root of unity in `R` and `n` is odd, then
`X ^ n + Y ^ n = ∏ (X + μ Y)`, where `μ` varies over the `n`-th roots of unity. -/
/-
**Polynomial._root_.IsPrimitiveRoot.pow_add_pow_eq_prod_add_mul** 是 Mathlib 中的一个
定理，位于命名空间 `Polynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If there is a primitive `n`th root of unity in `R` and `n` is odd, then
`X ^ n + Y ^ n = ∏ (X + μ Y)`, where `μ` varies over the `n`-th roots of unity.
-/
theorem _root_.IsPrimitiveRoot.pow_add_pow_eq_prod_add_mul (hodd : Odd n)
    (h : IsPrimitiveRoot ζ n) : x ^ n + y ^ n = ∏ ζ ∈ nthRootsFinset n (1 : R), (x + ζ * y) := by
  simpa [hodd.neg_pow] using h.pow_sub_pow_eq_prod_sub_mul x (-y) hodd.pos
/-
**Polynomial.separable_cyclotomic** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：separable_cyclotomic (n : Nat) (K : Type*) [Field K] [NeZero (n : K)] : (c
yclotomic n K).Separable
参数：n : Nat；K : Type*；n : K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.Separable.of_dvd`：∀ {R : Type u} [inst : CommSemiring R] {f g
 : Polynomial R}, f.Separable → g ∣ f → g.Separable
· 使用定理 `Polynomial.separable_X_pow_sub_C`：separable_X_pow_sub_C {n : Nat} (a : F
) (hn : (n : F) != 0) (ha : a != 0) : Separable (X ^ n - C a)
· 使用定理 `NeZero.out`：∀ {R : Type u_1} {inst : Zero R} {n : R} [self : NeZero n], 
n ≠ 0
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Polynomial.cyclotomic.dvd_X_pow_sub_one`：∀ (n : ℕ) (R : Type u_1) [inst 
: Ring R], Polynomial.cyclotomic n R ∣ Polynomial.X ^ n - 1
-/
theorem separable_cyclotomic (n : ℕ) (K : Type*) [Field K] [NeZero (n : K)] :
    (cyclotomic n K).Separable :=
  .of_dvd (separable_X_pow_sub_C 1 NeZero.out one_ne_zero) (cyclotomic.dvd_X_pow_sub_one n K)
/-
**Polynomial.squarefree_cyclotomic** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：squarefree_cyclotomic (n : Nat) (K : Type*) [Field K] [NeZero (n : K)] : S
quarefree (cyclotomic n K)
参数：n : Nat；K : Type*；n : K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.Separable.squarefree`：∀ {R : Type u} [inst : CommSemiring R] 
{p : Polynomial R}, p.Separable → Squarefree p
· 使用定理 `Polynomial.separable_cyclotomic`：separable_cyclotomic (n : Nat) (K : Typ
e*) [Field K] [NeZero (n : K)] : (cyclotomic n K).Separable
-/
theorem squarefree_cyclotomic (n : ℕ) (K : Type*) [Field K] [NeZero (n : K)] :
    Squarefree (cyclotomic n K) :=
  (separable_cyclotomic n K).squarefree

end miscellaneous

end Polynomial

