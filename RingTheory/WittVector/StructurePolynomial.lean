/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Robert Y. Lewis
-/
module

public import Mathlib.FieldTheory.Finite.Polynomial
public import Mathlib.NumberTheory.Basic
public import Mathlib.RingTheory.WittVector.WittPolynomial

/-!
# Witt structure polynomials

In this file we prove the main theorem that makes the whole theory of Witt vectors work.
Briefly, consider a polynomial `Φ : MvPolynomial idx ℤ` over the integers,
with polynomials variables indexed by an arbitrary type `idx`.

Then there exists a unique family of polynomials `φ : ℕ → MvPolynomial (idx × ℕ) Φ`
such that for all `n : ℕ` we have (`wittStructureInt_existsUnique`)
```
bind₁ φ (wittPolynomial p ℤ n) = bind₁ (fun i ↦ (rename (prod.mk i) (wittPolynomial p ℤ n))) Φ
```
In other words: evaluating the `n`-th Witt polynomial on the family `φ`
is the same as evaluating `Φ` on the (appropriately renamed) `n`-th Witt polynomials.

N.b.: As far as we know, these polynomials do not have a name in the literature,
so we have decided to call them the “Witt structure polynomials”. See `wittStructureInt`.

## Special cases

With the main result of this file in place, we apply it to certain special polynomials.
For example, by taking `Φ = X tt + X ff` resp. `Φ = X tt * X ff`
we obtain families of polynomials `witt_add` resp. `witt_mul`
(with type `ℕ → MvPolynomial (Bool × ℕ) ℤ`) that will be used in later files to define the
addition and multiplication on the ring of Witt vectors.

## Outline of the proof

The proof of `wittStructureInt_existsUnique` is rather technical, and takes up most of this file.

We start by proving the analogous version for polynomials with rational coefficients,
instead of integer coefficients.
In this case, the solution is rather easy,
since the Witt polynomials form a faithful change of coordinates
in the polynomial ring `MvPolynomial ℕ ℚ`.
We therefore obtain a family of polynomials `wittStructureRat Φ`
for every `Φ : MvPolynomial idx ℚ`.

If `Φ` has integer coefficients, then the polynomials `wittStructureRat Φ n` do so as well.
Proving this claim is the essential core of this file, and culminates in
`map_wittStructureInt`, which proves that upon mapping the coefficients
of `wittStructureInt Φ n` from the integers to the rationals,
one obtains `wittStructureRat Φ n`.
Ultimately, the proof of `map_wittStructureInt` relies on
```
dvd_sub_pow_of_dvd_sub {R : Type*} [CommRing R] {p : ℕ} {a b : R} :
    (p : R) ∣ a - b → ∀ (k : ℕ), (p : R) ^ (k + 1) ∣ a ^ p ^ k - b ^ p ^ k
```

## Main results

* `wittStructureRat Φ`: the family of polynomials `ℕ → MvPolynomial (idx × ℕ) ℚ`
  associated with `Φ : MvPolynomial idx ℚ` and satisfying the property explained above.
* `wittStructureRat_prop`: the proof that `wittStructureRat` indeed satisfies the property.
* `wittStructureInt Φ`: the family of polynomials `ℕ → MvPolynomial (idx × ℕ) ℤ`
  associated with `Φ : MvPolynomial idx ℤ` and satisfying the property explained above.
* `map_wittStructureInt`: the proof that the integral polynomials `with_structure_int Φ`
  are equal to `wittStructureRat Φ` when mapped to polynomials with rational coefficients.
* `wittStructureInt_prop`: the proof that `wittStructureInt` indeed satisfies the property.
* Five families of polynomials that will be used to define the ring structure
  on the ring of Witt vectors:
  - `WittVector.wittZero`
  - `WittVector.wittOne`
  - `WittVector.wittAdd`
  - `WittVector.wittMul`
  - `WittVector.wittNeg`

  (We also define `WittVector.wittSub`, and later we will prove that it describes subtraction,
  which is defined as `fun a b ↦ a + -b`. See `WittVector.sub_coeff` for this proof.)

## References

* [Hazewinkel, *Witt Vectors*][Haze09]

* [Commelin and Lewis, *Formalizing the Ring of Witt Vectors*][CL21]
-/

@[expose] public section


open MvPolynomial Set

open Finset (range)

open Finsupp (single)

-- This lemma reduces a bundled morphism to a "mere" function,
-- and consequently the simplifier cannot use a lot of powerful simp-lemmas.
-- We disable this locally, and probably it should be disabled globally in mathlib.
attribute [-simp] coe_eval₂Hom

variable {p : ℕ} {R : Type*} {idx : Type*} [CommRing R]

open scoped Witt

section PPrime

variable (p)
variable [hp : Fact p.Prime]

-- Notation with ring of coefficients explicit
set_option quotPrecheck false in
@[inherit_doc]
scoped[Witt] notation "W_" => wittPolynomial p

-- Notation with ring of coefficients implicit
set_option quotPrecheck false in
@[inherit_doc]
scoped[Witt] notation "W" => wittPolynomial p _

/-- `wittStructureRat Φ` is a family of polynomials `ℕ → MvPolynomial (idx × ℕ) ℚ`
that are uniquely characterised by the property that
```
bind₁ (wittStructureRat p Φ) (wittPolynomial p ℚ n) =
bind₁ (fun i ↦ (rename (prod.mk i) (wittPolynomial p ℚ n))) Φ
```
In other words: evaluating the `n`-th Witt polynomial on the family `wittStructureRat Φ`
is the same as evaluating `Φ` on the (appropriately renamed) `n`-th Witt polynomials.

See `wittStructureRat_prop` for this property,
and `wittStructureRat_existsUnique` for the fact that `wittStructureRat`
gives the unique family of polynomials with this property.

These polynomials turn out to have integral coefficients,
but it requires some effort to show this.
See `wittStructureInt` for the version with integral coefficients,
and `map_wittStructureInt` for the fact that it is equal to `wittStructureRat`
when mapped to polynomials over the rationals. -/
/-
**wittStructureRat** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：wittStructureRat (Φ : MvPolynomial idx Rat) (n : Nat) : MvPolynomial (idx 
× Nat) Rat
参数：Φ : MvPolynomial idx Rat；n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`wittStructureRat Φ` is a family of polynomials `ℕ → MvPolynomial (idx × ℕ) ℚ`
that are uniquely characterised by the property that
```
bind₁ (wittStructureRat p Φ) (wittPolynomial p ℚ n) =
bind₁ (fun i ↦ (rename (prod.mk i) (wittPolynomial p ℚ n))) Φ
```
In other words: evaluating the `n`-th Witt polynomial on the family `wittStructu
reRat Φ`
is the same as evaluating `Φ` on the (appropriately renamed) `n`-th Witt polynom
ials.

See `wittStructureRat_prop` for this property,
and `wittStructureRat_existsUnique` for the fact that `wittStructureRat`
gives the unique family of polynomials with this property.

These polynomials turn out to have integral coefficients,
but it requires some effort to show this.
See `wittStructureInt` for the version with integral coefficients,
and `map_wittStructureInt` for the fact that it is equal to `wittStructureRat`
when mapped to polynomials over the rationals.
-/
noncomputable def wittStructureRat (Φ : MvPolynomial idx ℚ) (n : ℕ) : MvPolynomial (idx × ℕ) ℚ :=
  bind₁ (fun k => bind₁ (fun i => rename (Prod.mk i) (W_ ℚ k)) Φ) (xInTermsOfW p ℚ n)
/-
**wittStructureRat_prop** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：wittStructureRat_prop (Φ : MvPolynomial idx Rat) (n : Nat) : bind₁ (wittSt
ructureRat p Φ) (W_ Rat n) = bind₁ (fun i => rename (Prod.mk i) (W_ Rat n)) Φ
参数：Φ : MvPolynomial idx Rat；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.bind₁_bind₁`：bind₁_bind₁ {υ : Type*} (f : σ -> MvPolynomial
 τ R) (g : τ -> MvPolynomial υ R) (φ : MvPolynomial σ R) : (bind₁ g) (bind₁ f φ)
 = bind₁ (fun …
· 使用定理 `MvPolynomial.eval₂Hom_congr`：eval₂Hom_congr {f₁ f₂ : R ->+* S₁} {g₁ g₂ :
 σ -> S₁} {p₁ p₂ : MvPolynomial σ R} : f₁ = f₂ -> g₁ = g₂ -> p₁ = p₂ -> eval₂Hom
 f₁ g₁ p₁ = eval₂…
· 使用定理 `RingHom.ext_rat`：RingHom.ext_rat {R : Type*} [Semiring R] [FunLike F Rat
 R] [RingHomClass F Rat R] (f g : F) : f = g
· 使用定理 `bind₁_xInTermsOfW_wittPolynomial`：bind₁_xInTermsOfW_wittPolynomial [Inve
rtible (p : R)] (k : Nat) : bind₁ (xInTermsOfW p R) (W_ R k) = X k
· 使用定理 `MvPolynomial.bind₁_X_right`：bind₁_X_right (f : σ -> MvPolynomial τ R) (i
 : σ) : bind₁ f (X i) = f i
-/
theorem wittStructureRat_prop (Φ : MvPolynomial idx ℚ) (n : ℕ) :
    bind₁ (wittStructureRat p Φ) (W_ ℚ n) = bind₁ (fun i => rename (Prod.mk i) (W_ ℚ n)) Φ :=
  calc
    bind₁ (wittStructureRat p Φ) (W_ ℚ n) =
        bind₁ (fun k => bind₁ (fun i => (rename (Prod.mk i)) (W_ ℚ k)) Φ)
          (bind₁ (xInTermsOfW p ℚ) (W_ ℚ n)) := by
      rw [bind₁_bind₁]; exact eval₂Hom_congr (RingHom.ext_rat _ _) rfl rfl
    _ = bind₁ (fun i => rename (Prod.mk i) (W_ ℚ n)) Φ := by
      rw [bind₁_xInTermsOfW_wittPolynomial p _ n, bind₁_X_right]
/-
**wittStructureRat_existsUnique** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：wittStructureRat_existsUnique (Φ : MvPolynomial idx Rat) : exists! φ : Nat
 -> MvPolynomial (idx × Nat) Rat, forall n : Nat, bind₁ φ (W_ Rat n) = bind₁ (fu
n i => rename (Prod.mk i) (W_ Rat n)) Φ
参数：Φ : MvPolynomial idx Rat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `wittStructureRat_prop`：wittStructureRat_prop (Φ : MvPolynomial idx Rat) 
(n : Nat) : bind₁ (wittStructureRat p Φ) (W_ Rat n) = bind₁ (fun i => rename (Pr
od.mk i) (W…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `bind₁_wittPolynomial_xInTermsOfW`：bind₁_wittPolynomial_xInTermsOfW [Inve
rtible (p : R)] (n : Nat) : bind₁ (W_ R) (xInTermsOfW p R n) = X n
· 使用定理 `MvPolynomial.bind₁_X_right`：bind₁_X_right (f : σ -> MvPolynomial τ R) (i
 : σ) : bind₁ f (X i) = f i
· 使用定理 `MvPolynomial.bind₁_bind₁`：bind₁_bind₁ {υ : Type*} (f : σ -> MvPolynomial
 τ R) (g : τ -> MvPolynomial υ R) (φ : MvPolynomial σ R) : (bind₁ g) (bind₁ f φ)
 = bind₁ (fun …
· 使用定理 `MvPolynomial.eval₂Hom_congr`：eval₂Hom_congr {f₁ f₂ : R ->+* S₁} {g₁ g₂ :
 σ -> S₁} {p₁ p₂ : MvPolynomial σ R} : f₁ = f₂ -> g₁ = g₂ -> p₁ = p₂ -> eval₂Hom
 f₁ g₁ p₁ = eval₂…
· 使用定理 `RingHom.ext_rat`：RingHom.ext_rat {R : Type*} [Semiring R] [FunLike F Rat
 R] [RingHomClass F Rat R] (f g : F) : f = g
-/
theorem wittStructureRat_existsUnique (Φ : MvPolynomial idx ℚ) :
    ∃! φ : ℕ → MvPolynomial (idx × ℕ) ℚ,
      ∀ n : ℕ, bind₁ φ (W_ ℚ n) = bind₁ (fun i => rename (Prod.mk i) (W_ ℚ n)) Φ := by
  refine ⟨wittStructureRat p Φ, ?_, ?_⟩
  · intro n; apply wittStructureRat_prop
  · intro φ H
    funext n
    rw [show φ n = bind₁ φ (bind₁ (W_ ℚ) (xInTermsOfW p ℚ n)) by
        rw [bind₁_wittPolynomial_xInTermsOfW p, bind₁_X_right]]
    rw [bind₁_bind₁]
    exact eval₂Hom_congr (RingHom.ext_rat _ _) (funext H) rfl
/-
**wittStructureRat_rec_aux** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：wittStructureRat_rec_aux (Φ : MvPolynomial idx Rat) (n : Nat) : wittStruct
ureRat p Φ n * C ((p : Rat) ^ n) = bind₁ (fun b => rename (fun i => (b, i)) (W_ 
Rat n)) Φ - ∑ i in range n, C ((p : Rat) ^ i) * wittStructureRat p Φ i ^ p ^ (n 
- i)
参数：Φ : MvPolynomial idx Rat；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `xInTermsOfW_aux`：xInTermsOfW_aux [Invertible (p : R)] (n : Nat) : xInTer
msOfW p R n * C ((p : R) ^ n) = X n - ∑ i in range n, C ((p : R) ^ i) * xInTerms
OfW p…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `wittStructureRat.eq_1`：∀ (p : ℕ) {idx : Type u_2} [hp : Fact (Nat.Prime 
p)] (Φ : MvPolynomial idx ℚ) (n : ℕ),   wittStructureRat p Φ n =     (MvPolynomi
al.bind₁ fu…
· 使用定理 `MvPolynomial.bind₁_C_right`：bind₁_C_right (f : σ -> MvPolynomial τ R) (x
) : bind₁ f (C x) = C x
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MvPolynomial.bind₁_X_right`：bind₁_X_right (f : σ -> MvPolynomial τ R) (i
 : σ) : bind₁ f (X i) = f i
· 使用定理 `sub_right_inj`：∀ {G : Type u_3} [inst : AddGroup G] {a b c : G}, a - b =
 a - c ↔ b = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
-/
theorem wittStructureRat_rec_aux (Φ : MvPolynomial idx ℚ) (n : ℕ) :
    wittStructureRat p Φ n * C ((p : ℚ) ^ n) =
      bind₁ (fun b => rename (fun i => (b, i)) (W_ ℚ n)) Φ -
        ∑ i ∈ range n, C ((p : ℚ) ^ i) * wittStructureRat p Φ i ^ p ^ (n - i) := by
  have := xInTermsOfW_aux p ℚ n
  replace := congr_arg (bind₁ fun k : ℕ => bind₁ (fun i => rename (Prod.mk i) (W_ ℚ k)) Φ) this
  rw [map_mul, bind₁_C_right] at this
  rw [wittStructureRat, this]; clear this
  conv_lhs => simp only [map_sub, bind₁_X_right]
  rw [sub_right_inj]
  simp only [map_sum, map_mul, bind₁_C_right, map_pow]
  rfl

/-- Write `wittStructureRat p φ n` in terms of `wittStructureRat p φ i` for `i < n`. -/
/-
**wittStructureRat_rec** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：wittStructureRat_rec (Φ : MvPolynomial idx Rat) (n : Nat) : wittStructureR
at p Φ n = C (1 / (p : Rat) ^ n) * (bind₁ (fun b => rename (fun i => (b, i)) (W_
 Rat n)) Φ - ∑ i in range n, C ((p : Rat) ^ i) * wittStructureRat p Φ i ^ p ^ (n
 - i))
参数：Φ : MvPolynomial idx Rat；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPolynomial.C_mul`：C_mul : (C (a * a') : MvPolynomial σ R) = C a * C a'
· 使用引理 `div_mul_cancel₀`：div_mul_cancel₀ (a : G₀) (h : b != 0) : a / b * b = a
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_ne_zero`：cast_ne_zero {n : Nat} : (n : R) != 0 ↔ n != 0
· 使用定理 `Nat.Prime.ne_zero`：∀ {n : ℕ}, Nat.Prime n → n ≠ 0
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `MvPolynomial.C_1`：C_1 : C 1 = (1 : MvPolynomial σ R)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `wittStructureRat_rec_aux`：wittStructureRat_rec_aux (Φ : MvPolynomial idx
 Rat) (n : Nat) : wittStructureRat p Φ n * C ((p : Rat) ^ n) = bind₁ (fun b => r
ename (fun i =…

--- 原说明 ---
Write `wittStructureRat p φ n` in terms of `wittStructureRat p φ i` for `i < n`.
-/
theorem wittStructureRat_rec (Φ : MvPolynomial idx ℚ) (n : ℕ) :
    wittStructureRat p Φ n =
      C (1 / (p : ℚ) ^ n) *
        (bind₁ (fun b => rename (fun i => (b, i)) (W_ ℚ n)) Φ -
          ∑ i ∈ range n, C ((p : ℚ) ^ i) * wittStructureRat p Φ i ^ p ^ (n - i)) := by
  calc
    wittStructureRat p Φ n = C (1 / (p : ℚ) ^ n) * (wittStructureRat p Φ n * C ((p : ℚ) ^ n)) := ?_
    _ = _ := by rw [wittStructureRat_rec_aux]
  rw [mul_left_comm, ← C_mul, div_mul_cancel₀, C_1, mul_one]
  exact pow_ne_zero _ (Nat.cast_ne_zero.2 hp.1.ne_zero)

/-- `wittStructureInt Φ` is a family of polynomials `ℕ → MvPolynomial (idx × ℕ) ℤ`
that are uniquely characterised by the property that
```
bind₁ (wittStructureInt p Φ) (wittPolynomial p ℤ n) =
bind₁ (fun i ↦ (rename (prod.mk i) (wittPolynomial p ℤ n))) Φ
```
In other words: evaluating the `n`-th Witt polynomial on the family `wittStructureInt Φ`
is the same as evaluating `Φ` on the (appropriately renamed) `n`-th Witt polynomials.

See `wittStructureInt_prop` for this property,
and `wittStructureInt_existsUnique` for the fact that `wittStructureInt`
gives the unique family of polynomials with this property. -/
/-
**wittStructureInt** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：wittStructureInt (Φ : MvPolynomial idx Int) (n : Nat) : MvPolynomial (idx 
× Nat) Int
参数：Φ : MvPolynomial idx Int；n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`wittStructureInt Φ` is a family of polynomials `ℕ → MvPolynomial (idx × ℕ) ℤ`
that are uniquely characterised by the property that
```
bind₁ (wittStructureInt p Φ) (wittPolynomial p ℤ n) =
bind₁ (fun i ↦ (rename (prod.mk i) (wittPolynomial p ℤ n))) Φ
```
In other words: evaluating the `n`-th Witt polynomial on the family `wittStructu
reInt Φ`
is the same as evaluating `Φ` on the (appropriately renamed) `n`-th Witt polynom
ials.

See `wittStructureInt_prop` for this property,
and `wittStructureInt_existsUnique` for the fact that `wittStructureInt`
gives the unique family of polynomials with this property.
-/
noncomputable def wittStructureInt (Φ : MvPolynomial idx ℤ) (n : ℕ) : MvPolynomial (idx × ℕ) ℤ :=
  .ofCoeff <| .mapRange Rat.num (Rat.num_intCast 0) <| AddMonoidAlgebra.coeff <|
    wittStructureRat p (map (Int.castRingHom ℚ) Φ) n

variable {p}
/-
**bind** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bind₁_rename_expand_wittPolynomial (Φ : MvPolynomial idx ℤ) (n : ℕ)
    (IH :
      ∀ m : ℕ,
        m < n + 1 →
          map (Int.castRingHom ℚ) (wittStructureInt p Φ m) =
            wittStructureRat p (map (Int.castRingHom ℚ) Φ) m) :
    bind₁ (fun b => rename (fun i => (b, i)) (expand p (W_ ℤ n))) Φ =
      bind₁ (fun i => expand p (wittStructureInt p Φ i)) (W_ ℤ n) := by
  apply MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
  simp only [map_bind₁, map_rename, map_expand, rename_expand, map_wittPolynomial]
  have key := (wittStructureRat_prop p (map (Int.castRingHom ℚ) Φ) n).symm
  apply_fun expand p at key
  simp only [expand_bind₁] at key
  rw [key]; clear key
  apply eval₂Hom_congr' rfl _ rfl
  rintro i hi -
  rw [wittPolynomial_vars, Finset.mem_range] at hi
  simp only [IH i hi]
/-
**C_p_pow_dvd_bind** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem C_p_pow_dvd_bind₁_rename_wittPolynomial_sub_sum (Φ : MvPolynomial idx ℤ) (n : ℕ)
    (IH :
      ∀ m : ℕ,
        m < n →
          map (Int.castRingHom ℚ) (wittStructureInt p Φ m) =
            wittStructureRat p (map (Int.castRingHom ℚ) Φ) m) :
    (C ((p ^ n :) : ℤ) : MvPolynomial (idx × ℕ) ℤ) ∣
      bind₁ (fun b : idx => rename (fun i => (b, i)) (wittPolynomial p ℤ n)) Φ -
        ∑ i ∈ range n, C ((p : ℤ) ^ i) * wittStructureInt p Φ i ^ p ^ (n - i) := by
  rcases n with - | n
  · simp
  -- prepare a useful equation for rewriting
  have key := bind₁_rename_expand_wittPolynomial Φ n IH
  apply_fun map (Int.castRingHom (ZMod (p ^ (n + 1)))) at key
  conv_lhs at key => simp only [map_bind₁, map_rename, map_expand, map_wittPolynomial]
  -- clean up and massage
  rw [C_dvd_iff_zmod, map_sub, sub_eq_zero, map_bind₁]
  simp only [map_rename, map_wittPolynomial, wittPolynomial_zmod_self]
  rw [key]; clear key IH
  rw [bind₁, aeval_wittPolynomial, map_sum, map_sum, Finset.sum_congr rfl]
  intro k hk
  rw [Finset.mem_range, Nat.lt_succ_iff] at hk
  rw [← sub_eq_zero, ← map_sub, ← C_dvd_iff_zmod, C_eq_coe_nat, ← Nat.cast_pow,
    ← Nat.cast_pow, C_eq_coe_nat, ← mul_sub]
  have : p ^ (n + 1) = p ^ k * p ^ (n - k + 1) := by
    rw [← pow_add, ← add_assoc]; congr 2; rw [add_comm, ← tsub_eq_iff_eq_add_of_le hk]
  rw [this]
  rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_pow]
  apply mul_dvd_mul_left ((p : MvPolynomial (idx × ℕ) ℤ) ^ k)
  rw [show p ^ (n + 1 - k) = p * p ^ (n - k) by rw [← pow_succ', ← tsub_add_eq_add_tsub hk]]
  rw [pow_mul]
  -- the machine!
  apply dvd_sub_pow_of_dvd_sub
  rw [← C_eq_coe_nat, C_dvd_iff_zmod, map_sub, sub_eq_zero, map_expand, map_pow,
    MvPolynomial.expand_zmod]

variable (p)

@[simp]
/-
**map_wittStructureInt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_wittStructureInt (Φ : MvPolynomial idx Int) (n : Nat) : map (Int.castR
ingHom Rat) (wittStructureInt p Φ n) = wittStructureRat p (map (Int.castRingHom 
Rat) Φ) n
参数：Φ : MvPolynomial idx Int；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.strong_induction_on`：∀ {p : ℕ → Prop} (n : ℕ), (∀ (n : ℕ), (∀ m < n,
 p m) → p n) → p n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `wittStructureInt.eq_1`：∀ (p : ℕ) {idx : Type u_2} [hp : Fact (Nat.Prime 
p)] (Φ : MvPolynomial idx ℤ) (n : ℕ),   wittStructureInt p Φ n =     AddMonoidAl
gebra.ofCoe…
· 使用定理 `MvPolynomial.map_mapRange_eq_iff`：map_mapRange_eq_iff (f : R ->+* S₁) (g
 : S₁ -> R) (hg : g 0 = 0) (φ : MvPolynomial σ S₁) : map f (.ofCoeff <| Finsupp.
mapRange g hg <| AddMo…
· 使用定理 `Int.coe_castRingHom`：∀ {α : Type u_3} [inst : NonAssocRing α], ⇑(Int.cas
tRingHom α) = fun x => ↑x
· 使用定理 `wittStructureRat_rec`：wittStructureRat_rec (Φ : MvPolynomial idx Rat) (n
 : Nat) : wittStructureRat p Φ n = C (1 / (p : Rat) ^ n) * (bind₁ (fun b => rena
me (fun i …
· 使用定理 `MvPolynomial.coeff_C_mul`：coeff_C_mul (m) (a : R) (p : MvPolynomial σ R)
 : coeff m (C a * p) = a * coeff m p
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_div_assoc'`：mul_div_assoc' (a b c : G) : a * (b / c) = a * b / c
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
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
· 使用定理 `MvPolynomial.map_C`：map_C : forall a : R, map f (C a : MvPolynomial σ R)
 = C (f a)
· 使用定理 `Finset.mem_range`：mem_range : m in range n ↔ m < n
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_wittPolynomial`：map_wittPolynomial (f : R ->+* S) (n : Nat) : map f 
(W n) = W n
· 使用定理 `MvPolynomial.coeff_map`：coeff_map (p : MvPolynomial σ R) : forall m : σ 
->₀ Nat, coeff m (map f p) = f (coeff m p)
· 使用定理 `Nat.cast_pow`：∀ {α : Type u_1} [inst : Semiring α] (m n : ℕ), ↑(m ^ n) =
 ↑m ^ n
· 使用定理 `Int.cast_pow`：∀ {R : Type u_1} [inst : Ring R] (n : ℤ) (m : ℕ), ↑(n ^ m)
 = ↑n ^ m
（共 43 条，此处仅展示前 30 条）
-/
theorem map_wittStructureInt (Φ : MvPolynomial idx ℤ) (n : ℕ) :
    map (Int.castRingHom ℚ) (wittStructureInt p Φ n) =
      wittStructureRat p (map (Int.castRingHom ℚ) Φ) n := by
  induction n using Nat.strong_induction_on with | h n IH => ?_
  rw [wittStructureInt, map_mapRange_eq_iff, Int.coe_castRingHom]
  intro c
  rw [wittStructureRat_rec, coeff_C_mul, mul_comm, mul_div_assoc', mul_one]
  have sum_induction_steps :
      map (Int.castRingHom ℚ)
        (∑ i ∈ range n, C ((p : ℤ) ^ i) * wittStructureInt p Φ i ^ p ^ (n - i)) =
      ∑ i ∈ range n,
        C ((p : ℚ) ^ i) * wittStructureRat p (map (Int.castRingHom ℚ) Φ) i ^ p ^ (n - i) := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    simp only [IH i hi, map_mul, map_pow, map_C]
    rfl
  simp only [← sum_induction_steps, ← map_wittPolynomial p (Int.castRingHom ℚ), ← map_rename, ←
    map_bind₁, ← map_sub, coeff_map]
  rw [show (p : ℚ) ^ n = ((↑(p ^ n) : ℤ) : ℚ) by norm_cast]
  rw [← Rat.den_eq_one_iff, eq_intCast, Rat.den_div_intCast_eq_one_iff]
  swap; · exact mod_cast pow_ne_zero n hp.1.ne_zero
  revert c; rw [← C_dvd_iff_dvd_coeff]
  exact C_p_pow_dvd_bind₁_rename_wittPolynomial_sub_sum Φ n IH
/-
**wittStructureInt_prop** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：wittStructureInt_prop (Φ : MvPolynomial idx Int) (n) : bind₁ (wittStructur
eInt p Φ) (wittPolynomial p Int n) = bind₁ (fun i => rename (Prod.mk i) (W_ Int 
n)) Φ
参数：Φ : MvPolynomial idx Int；n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.map_injective`：map_injective (hf : Function.Injective f) : 
Function.Injective (map f : MvPolynomial σ R -> MvPolynomial σ S₁)
· 使用引理 `Int.cast_injective`：cast_injective : Injective (Int.cast : Int -> α)
· 使用定理 `wittStructureRat_prop`：wittStructureRat_prop (Φ : MvPolynomial idx Rat) 
(n : Nat) : bind₁ (wittStructureRat p Φ) (W_ Rat n) = bind₁ (fun i => rename (Pr
od.mk i) (W…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MvPolynomial.map_bind₁`：map_bind₁ (f : R ->+* S) (g : σ -> MvPolynomial 
τ R) (φ : MvPolynomial σ R) : map f (bind₁ g φ) = bind₁ (fun i : σ => (map f) (g
 i)) (map f …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `map_wittStructureInt`：map_wittStructureInt (Φ : MvPolynomial idx Int) (n
 : Nat) : map (Int.castRingHom Rat) (wittStructureInt p Φ n) = wittStructureRat 
p (map (In…
· 使用定理 `map_wittPolynomial`：map_wittPolynomial (f : R ->+* S) (n : Nat) : map f 
(W n) = W n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MvPolynomial.map_rename`：map_rename (f : R ->+* S) (g : σ -> τ) (p : MvP
olynomial σ R) : map f (rename g p) = rename g (map f p)
-/
theorem wittStructureInt_prop (Φ : MvPolynomial idx ℤ) (n) :
    bind₁ (wittStructureInt p Φ) (wittPolynomial p ℤ n) =
      bind₁ (fun i => rename (Prod.mk i) (W_ ℤ n)) Φ := by
  apply MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
  have := wittStructureRat_prop p (map (Int.castRingHom ℚ) Φ) n
  simpa only [map_bind₁, ← eval₂Hom_map_hom, eval₂Hom_C_left, map_rename, map_wittPolynomial,
    AlgHom.coe_toRingHom, map_wittStructureInt]
/-
**eq_wittStructureInt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_wittStructureInt (Φ : MvPolynomial idx Int) (φ : Nat -> MvPolynomial (i
dx × Nat) Int) (h : forall n, bind₁ φ (wittPolynomial p Int n) = bind₁ (fun i =>
 rename (Prod.mk i) (W_ Int n)) Φ) : φ = wittStructureInt p Φ
参数：Φ : MvPolynomial idx Int；φ : Nat -> MvPolynomial (idx × Nat) Int；h : forall n
, bind₁ φ (wittPolynomial p Int n) = bind₁ (fun i => rename (Prod.mk i) (W_ Int 
n)) Φ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MvPolynomial.map_injective`：map_injective (hf : Function.Injective f) : 
Function.Injective (map f : MvPolynomial σ R -> MvPolynomial σ S₁)
· 使用引理 `Int.cast_injective`：cast_injective : Injective (Int.cast : Int -> α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_wittStructureInt`：map_wittStructureInt (Φ : MvPolynomial idx Int) (n
 : Nat) : map (Int.castRingHom Rat) (wittStructureInt p Φ n) = wittStructureRat 
p (map (In…
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `ExistsUnique.unique`：ExistsUnique.unique {p : α -> Prop} (h : exists! x,
 p x) {y₁ y₂ : α} (py₁ : p y₁) (py₂ : p y₂) : y₁ = y₂
· 使用定理 `wittStructureRat_existsUnique`：wittStructureRat_existsUnique (Φ : MvPoly
nomial idx Rat) : exists! φ : Nat -> MvPolynomial (idx × Nat) Rat, forall n : Na
t, bind₁ φ (W_ Rat …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MvPolynomial.map_bind₁`：map_bind₁ (f : R ->+* S) (g : σ -> MvPolynomial 
τ R) (φ : MvPolynomial σ R) : map f (bind₁ g φ) = bind₁ (fun i : σ => (map f) (g
 i)) (map f …
· 使用定理 `map_wittPolynomial`：map_wittPolynomial (f : R ->+* S) (n : Nat) : map f 
(W n) = W n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MvPolynomial.map_rename`：map_rename (f : R ->+* S) (g : σ -> τ) (p : MvP
olynomial σ R) : map f (rename g p) = rename g (map f p)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `wittStructureRat_prop`：wittStructureRat_prop (Φ : MvPolynomial idx Rat) 
(n : Nat) : bind₁ (wittStructureRat p Φ) (W_ Rat n) = bind₁ (fun i => rename (Pr
od.mk i) (W…
-/
theorem eq_wittStructureInt (Φ : MvPolynomial idx ℤ) (φ : ℕ → MvPolynomial (idx × ℕ) ℤ)
    (h : ∀ n, bind₁ φ (wittPolynomial p ℤ n) = bind₁ (fun i => rename (Prod.mk i) (W_ ℤ n)) Φ) :
    φ = wittStructureInt p Φ := by
  funext k
  apply MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
  rw [map_wittStructureInt]
  -- Porting note: was `refine' congr_fun _ k`
  revert k
  refine congr_fun ?_
  apply ExistsUnique.unique (wittStructureRat_existsUnique p (map (Int.castRingHom ℚ) Φ))
  · intro n
    specialize h n
    apply_fun map (Int.castRingHom ℚ) at h
    simpa only [map_bind₁, ← eval₂Hom_map_hom, eval₂Hom_C_left, map_rename, map_wittPolynomial,
      AlgHom.coe_toRingHom] using h
  · intro n; apply wittStructureRat_prop
/-
**wittStructureInt_existsUnique** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：wittStructureInt_existsUnique (Φ : MvPolynomial idx Int) : exists! φ : Nat
 -> MvPolynomial (idx × Nat) Int, forall n : Nat, bind₁ φ (wittPolynomial p Int 
n) = bind₁ (fun i : idx => rename (Prod.mk i) (W_ Int n)) Φ
参数：Φ : MvPolynomial idx Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `wittStructureInt_prop`：wittStructureInt_prop (Φ : MvPolynomial idx Int) 
(n) : bind₁ (wittStructureInt p Φ) (wittPolynomial p Int n) = bind₁ (fun i => re
name (Prod.…
· 使用定理 `eq_wittStructureInt`：eq_wittStructureInt (Φ : MvPolynomial idx Int) (φ :
 Nat -> MvPolynomial (idx × Nat) Int) (h : forall n, bind₁ φ (wittPolynomial p I
nt n) = b…
-/
theorem wittStructureInt_existsUnique (Φ : MvPolynomial idx ℤ) :
    ∃! φ : ℕ → MvPolynomial (idx × ℕ) ℤ,
      ∀ n : ℕ,
        bind₁ φ (wittPolynomial p ℤ n) = bind₁ (fun i : idx => rename (Prod.mk i) (W_ ℤ n)) Φ :=
  ⟨wittStructureInt p Φ, wittStructureInt_prop _ _, eq_wittStructureInt _ _⟩
/-
**witt_structure_prop** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：witt_structure_prop (Φ : MvPolynomial idx Int) (n) : aeval (fun i => map (
Int.castRingHom R) (wittStructureInt p Φ i)) (wittPolynomial p Int n) = aeval (f
un i => rename (Prod.mk i) (W n)) Φ
参数：Φ : MvPolynomial idx Int；n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.hom_bind₁`：hom_bind₁ (f : MvPolynomial τ R ->+* S) (g : σ -
> MvPolynomial τ R) (φ : MvPolynomial σ R) : f (bind₁ g φ) = eval₂Hom (f.comp C)
 (fun i => f…
· 使用定理 `MvPolynomial.eval₂Hom_congr`：eval₂Hom_congr {f₁ f₂ : R ->+* S₁} {g₁ g₂ :
 σ -> S₁} {p₁ p₂ : MvPolynomial σ R} : f₁ = f₂ -> g₁ = g₂ -> p₁ = p₂ -> eval₂Hom
 f₁ g₁ p₁ = eval₂…
· 使用定理 `RingHom.ext_int`：ext_int {R : Type*} [NonAssocSemiring R] (f g : Int ->+
* R) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MvPolynomial.map_rename`：map_rename (f : R ->+* S) (g : σ -> τ) (p : MvP
olynomial σ R) : map f (rename g p) = rename g (map f p)
· 使用定理 `map_wittPolynomial`：map_wittPolynomial (f : R ->+* S) (n : Nat) : map f 
(W n) = W n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `wittStructureInt_prop`：wittStructureInt_prop (Φ : MvPolynomial idx Int) 
(n) : bind₁ (wittStructureInt p Φ) (wittPolynomial p Int n) = bind₁ (fun i => re
name (Prod.…
-/
theorem witt_structure_prop (Φ : MvPolynomial idx ℤ) (n) :
    aeval (fun i => map (Int.castRingHom R) (wittStructureInt p Φ i)) (wittPolynomial p ℤ n) =
      aeval (fun i => rename (Prod.mk i) (W n)) Φ := by
  convert! congr_arg (map (Int.castRingHom R)) (wittStructureInt_prop p Φ n) using 1 <;>
      rw [hom_bind₁] <;>
    apply eval₂Hom_congr (RingHom.ext_int _ _) _ rfl
  · rfl
  · simp only [map_rename, map_wittPolynomial]
/-
**wittStructureInt_rename** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：wittStructureInt_rename {σ : Type*} (Φ : MvPolynomial idx Int) (f : idx ->
 σ) (n : Nat) : wittStructureInt p (rename f Φ) n = rename (Prod.map f id) (witt
StructureInt p Φ n)
参数：Φ : MvPolynomial idx Int；f : idx -> σ；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.map_injective`：map_injective (hf : Function.Injective f) : 
Function.Injective (map f : MvPolynomial σ R -> MvPolynomial σ S₁)
· 使用引理 `Int.cast_injective`：cast_injective : Injective (Int.cast : Int -> α)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_wittStructureInt`：map_wittStructureInt (Φ : MvPolynomial idx Int) (n
 : Nat) : map (Int.castRingHom Rat) (wittStructureInt p Φ n) = wittStructureRat 
p (map (In…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MvPolynomial.map_rename`：map_rename (f : R ->+* S) (g : σ -> τ) (p : MvP
olynomial σ R) : map f (rename g p) = rename g (map f p)
· 使用定理 `MvPolynomial.bind₁_rename`：bind₁_rename {υ : Type*} (f : τ -> MvPolynomi
al υ R) (g : σ -> τ) (φ : MvPolynomial σ R) : bind₁ f (rename g φ) = bind₁ (f ∘ 
g) φ
· 使用定理 `MvPolynomial.rename_bind₁`：rename_bind₁ {υ : Type*} (f : σ -> MvPolynomi
al τ R) (g : τ -> υ) (φ : MvPolynomial σ R) : rename g (bind₁ f φ) = bind₁ (fun 
i => rename g <…
· 使用定理 `MvPolynomial.rename_rename`：rename_rename (f : σ -> τ) (g : τ -> α) (p :
 MvPolynomial σ R) : rename g (rename f p) = rename (g ∘ f) p
-/
theorem wittStructureInt_rename {σ : Type*} (Φ : MvPolynomial idx ℤ) (f : idx → σ) (n : ℕ) :
    wittStructureInt p (rename f Φ) n = rename (Prod.map f id) (wittStructureInt p Φ n) := by
  apply MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
  simp only [map_rename, map_wittStructureInt, wittStructureRat, rename_bind₁, rename_rename,
    bind₁_rename]
  rfl

@[simp]
/-
**constantCoeff_wittStructureRat_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：constantCoeff_wittStructureRat_zero (Φ : MvPolynomial idx Rat) : constantC
oeff (wittStructureRat p Φ 0) = constantCoeff Φ
参数：Φ : MvPolynomial idx Rat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `xInTermsOfW_zero`：xInTermsOfW_zero [Invertible (p : R)] : xInTermsOfW p 
R 0 = X 0
· 使用定理 `MvPolynomial.aeval_X`：aeval_X (s : σ) : aeval f (X s : MvPolynomial σ R)
 = f s
· 使用定理 `MvPolynomial.map_aeval`：map_aeval {B : Type*} [CommSemiring B] (g : σ ->
 S₁) (φ : S₁ ->+* B) (p : MvPolynomial σ R) : φ (aeval g p) = eval₂Hom (φ.comp (
algebraMap R…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MvPolynomial.constantCoeff_comp_algebraMap`：constantCoeff_comp_algebraMa
p : constantCoeff.comp (algebraMap R (MvPolynomial σ R)) = RingHom.id R
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MvPolynomial.constantCoeff_rename`：constantCoeff_rename {τ : Type*} (f :
 σ -> τ) (φ : MvPolynomial σ R) : constantCoeff (rename f φ) = constantCoeff φ
· 使用定理 `constantCoeff_wittPolynomial`：constantCoeff_wittPolynomial [hp : Fact p.
Prime] (n : Nat) : constantCoeff (wittPolynomial p R n) = 0
· 使用定理 `MvPolynomial.eval₂Hom_zero'_apply`：∀ {R : Type u} {S₂ : Type w} {σ : Typ
e u_1} [inst : CommSemiring R] [inst_1 : CommSemiring S₂] (f : R →+* S₂)   (p : 
MvPolynomial σ R), (MvP…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem constantCoeff_wittStructureRat_zero (Φ : MvPolynomial idx ℚ) :
    constantCoeff (wittStructureRat p Φ 0) = constantCoeff Φ := by
  simp only [wittStructureRat, bind₁, map_aeval, xInTermsOfW_zero, constantCoeff_rename,
    constantCoeff_wittPolynomial, aeval_X, constantCoeff_comp_algebraMap, eval₂Hom_zero'_apply,
    RingHom.id_apply]
/-
**constantCoeff_wittStructureRat** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：constantCoeff_wittStructureRat (Φ : MvPolynomial idx Rat) (h : constantCoe
ff Φ = 0) (n : Nat) : constantCoeff (wittStructureRat p Φ n) = 0
参数：Φ : MvPolynomial idx Rat；h : constantCoeff Φ = 0；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.map_aeval`：map_aeval {B : Type*} [CommSemiring B] (g : σ ->
 S₁) (φ : S₁ ->+* B) (p : MvPolynomial σ R) : φ (aeval g p) = eval₂Hom (φ.comp (
algebraMap R…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MvPolynomial.constantCoeff_comp_algebraMap`：constantCoeff_comp_algebraMa
p : constantCoeff.comp (algebraMap R (MvPolynomial σ R)) = RingHom.id R
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MvPolynomial.constantCoeff_rename`：constantCoeff_rename {τ : Type*} (f :
 σ -> τ) (φ : MvPolynomial σ R) : constantCoeff (rename f φ) = constantCoeff φ
· 使用定理 `constantCoeff_wittPolynomial`：constantCoeff_wittPolynomial [hp : Fact p.
Prime] (n : Nat) : constantCoeff (wittPolynomial p R n) = 0
· 使用定理 `MvPolynomial.eval₂Hom_zero'_apply`：∀ {R : Type u} {S₂ : Type w} {σ : Typ
e u_1} [inst : CommSemiring R] [inst_1 : CommSemiring S₂] (f : R →+* S₂)   (p : 
MvPolynomial σ R), (MvP…
· 使用定理 `constantCoeff_xInTermsOfW`：constantCoeff_xInTermsOfW [hp : Fact p.Prime]
 [Invertible (p : R)] (n : Nat) : constantCoeff (xInTermsOfW p R n) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem constantCoeff_wittStructureRat (Φ : MvPolynomial idx ℚ) (h : constantCoeff Φ = 0) (n : ℕ) :
    constantCoeff (wittStructureRat p Φ n) = 0 := by
  simp only [wittStructureRat, eval₂Hom_zero'_apply, h, bind₁, map_aeval, constantCoeff_rename,
    constantCoeff_wittPolynomial, constantCoeff_comp_algebraMap, RingHom.id_apply,
    constantCoeff_xInTermsOfW]

@[simp]
/-
**constantCoeff_wittStructureInt_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：constantCoeff_wittStructureInt_zero (Φ : MvPolynomial idx Int) : constantC
oeff (wittStructureInt p Φ 0) = constantCoeff Φ
参数：Φ : MvPolynomial idx Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Int.cast_inj`：cast_inj : (m : α) = n ↔ m = n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPolynomial.constantCoeff_map`：constantCoeff_map (f : R ->+* S₁) (φ : M
vPolynomial σ R) : constantCoeff (MvPolynomial.map f φ) = f (constantCoeff φ)
· 使用定理 `map_wittStructureInt`：map_wittStructureInt (Φ : MvPolynomial idx Int) (n
 : Nat) : map (Int.castRingHom Rat) (wittStructureInt p Φ n) = wittStructureRat 
p (map (In…
· 使用定理 `constantCoeff_wittStructureRat_zero`：constantCoeff_wittStructureRat_zero
 (Φ : MvPolynomial idx Rat) : constantCoeff (wittStructureRat p Φ 0) = constantC
oeff Φ
-/
theorem constantCoeff_wittStructureInt_zero (Φ : MvPolynomial idx ℤ) :
    constantCoeff (wittStructureInt p Φ 0) = constantCoeff Φ := by
  have inj : Function.Injective (Int.castRingHom ℚ) := by intro m n; exact Int.cast_inj.mp
  apply inj
  rw [← constantCoeff_map, map_wittStructureInt, constantCoeff_wittStructureRat_zero,
    constantCoeff_map]
/-
**constantCoeff_wittStructureInt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：constantCoeff_wittStructureInt (Φ : MvPolynomial idx Int) (h : constantCoe
ff Φ = 0) (n : Nat) : constantCoeff (wittStructureInt p Φ n) = 0
参数：Φ : MvPolynomial idx Int；h : constantCoeff Φ = 0；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Int.cast_inj`：cast_inj : (m : α) = n ↔ m = n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPolynomial.constantCoeff_map`：constantCoeff_map (f : R ->+* S₁) (φ : M
vPolynomial σ R) : constantCoeff (MvPolynomial.map f φ) = f (constantCoeff φ)
· 使用定理 `map_wittStructureInt`：map_wittStructureInt (Φ : MvPolynomial idx Int) (n
 : Nat) : map (Int.castRingHom Rat) (wittStructureInt p Φ n) = wittStructureRat 
p (map (In…
· 使用定理 `constantCoeff_wittStructureRat`：constantCoeff_wittStructureRat (Φ : MvPo
lynomial idx Rat) (h : constantCoeff Φ = 0) (n : Nat) : constantCoeff (wittStruc
tureRat p Φ n) = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
theorem constantCoeff_wittStructureInt (Φ : MvPolynomial idx ℤ) (h : constantCoeff Φ = 0) (n : ℕ) :
    constantCoeff (wittStructureInt p Φ n) = 0 := by
  have inj : Function.Injective (Int.castRingHom ℚ) := by intro m n; exact Int.cast_inj.mp
  apply inj
  rw [← constantCoeff_map, map_wittStructureInt, constantCoeff_wittStructureRat, map_zero]
  rw [constantCoeff_map, h, map_zero]

variable (R)

-- we could relax the fintype on `idx`, but then we need to cast from finset to set.
-- for our applications `idx` is always finite.
/-
**wittStructureRat_vars** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：wittStructureRat_vars [Fintype idx] (Φ : MvPolynomial idx Rat) (n : Nat) :
 (wittStructureRat p Φ n).vars subseteq Finset.univ ×ˢ Finset.range (n + 1)
参数：Φ : MvPolynomial idx Rat；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `wittStructureRat.eq_1`：∀ (p : ℕ) {idx : Type u_2} [hp : Fact (Nat.Prime 
p)] (Φ : MvPolynomial idx ℚ) (n : ℕ),   wittStructureRat p Φ n =     (MvPolynomi
al.bind₁ fu…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `MvPolynomial.mem_vars_bind₁`：mem_vars_bind₁ (f : σ -> MvPolynomial τ R) 
(φ : MvPolynomial σ R) {j : τ} (h : j in (bind₁ f φ).vars) : exists i : σ, i in 
φ.vars ∧ j in (f …
· 使用定理 `MvPolynomial.mem_vars_rename`：mem_vars_rename (f : σ -> τ) (φ : MvPolyno
mial σ R) {j : τ} (h : j in (rename f φ).vars) : exists i : σ, i in φ.vars ∧ f i
 = j
· 使用定理 `xInTermsOfW_vars_subset`：xInTermsOfW_vars_subset (n : Nat) : (xInTermsOf
W p Rat n).vars subseteq range (n + 1)
· 使用定理 `Finset.mem_range`：mem_range : m in range n ↔ m < n
· 使用定理 `wittPolynomial_vars`：wittPolynomial_vars [CharZero R] (n : Nat) : (wittP
olynomial p R n).vars = range (n + 1)
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
-/
theorem wittStructureRat_vars [Fintype idx] (Φ : MvPolynomial idx ℚ) (n : ℕ) :
    (wittStructureRat p Φ n).vars ⊆ Finset.univ ×ˢ Finset.range (n + 1) := by
  rw [wittStructureRat]
  intro x hx
  simp only [Finset.mem_product, true_and, Finset.mem_univ, Finset.mem_range]
  obtain ⟨k, hk, hx'⟩ := mem_vars_bind₁ _ _ hx
  obtain ⟨i, -, hx''⟩ := mem_vars_bind₁ _ _ hx'
  obtain ⟨j, hj, rfl⟩ := mem_vars_rename _ _ hx''
  rw [wittPolynomial_vars, Finset.mem_range] at hj
  replace hk := xInTermsOfW_vars_subset p _ hk
  grind

-- we could relax the fintype on `idx`, but then we need to cast from finset to set.
-- for our applications `idx` is always finite.
/-
**wittStructureInt_vars** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：wittStructureInt_vars [Fintype idx] (Φ : MvPolynomial idx Int) (n : Nat) :
 (wittStructureInt p Φ n).vars subseteq Finset.univ ×ˢ Finset.range (n + 1)
参数：Φ : MvPolynomial idx Int；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Int.cast_injective`：cast_injective : Injective (Int.cast : Int -> α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPolynomial.vars_map_of_injective`：vars_map_of_injective (hf : Injectiv
e f) : (map f p).vars = p.vars
· 使用定理 `map_wittStructureInt`：map_wittStructureInt (Φ : MvPolynomial idx Int) (n
 : Nat) : map (Int.castRingHom Rat) (wittStructureInt p Φ n) = wittStructureRat 
p (map (In…
· 使用定理 `wittStructureRat_vars`：wittStructureRat_vars [Fintype idx] (Φ : MvPolyno
mial idx Rat) (n : Nat) : (wittStructureRat p Φ n).vars subseteq Finset.univ ×ˢ 
Finset.rang…
-/
theorem wittStructureInt_vars [Fintype idx] (Φ : MvPolynomial idx ℤ) (n : ℕ) :
    (wittStructureInt p Φ n).vars ⊆ Finset.univ ×ˢ Finset.range (n + 1) := by
  have : Function.Injective (Int.castRingHom ℚ) := Int.cast_injective
  rw [← vars_map_of_injective _ this, map_wittStructureInt]
  apply wittStructureRat_vars

end PPrime

