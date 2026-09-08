/-
Copyright (c) 2023 Andrew Yang, Patrick Lutz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Minpoly
public import Mathlib.RingTheory.Norm.Basic

/-!
# Kummer Extensions

Let `K` be a field, `n` be an integer such that `K` contains a primitive `n`-th root of unity.
Kummer theory is about the classification of finite extensions of `L` whose Galois group is cyclic
of order `n`.

## Main result
- `isCyclic_tfae`:
  Suppose `L/K` is a finite extension of dimension `n`
  Then `L/K` is cyclic iff
  `L` is a splitting field of some irreducible polynomial of the form `Xⁿ - a : K[X]` iff
  `L = K[α]` for some `αⁿ ∈ K`.

- `autEquivRootsOfUnity`:
  Given an instance `IsSplittingField K L (X ^ n - C a)`
  (perhaps via `isSplittingField_X_pow_sub_C_of_root_adjoin_eq_top`),
  then the Galois group is isomorphic to `rootsOfUnity n K`, by sending
  `σ ↦ σ α / α` for `α ^ n = a`, and the inverse is given by `μ ↦ (α ↦ μ • α)`.

- `autEquivZmod`:
  Furthermore, given an explicit choice `ζ` of a primitive `n`-th root of unity, the Galois group is
  then isomorphic to `Multiplicative (ZMod n)` whose inverse is given by
  `i ↦ (α ↦ ζⁱ • α)`.

## Other results
Criteria for `X ^ n - C a` to be irreducible is given:
- `X_pow_sub_C_irreducible_iff_of_prime_pow`:
  For `n = p ^ k` an odd prime power, `X ^ n - C a` is irreducible iff `a` is not a `p`-th power.
- `X_pow_sub_C_irreducible_iff_forall_prime_of_odd`:
  For `n` odd, `X ^ n - C a` is irreducible iff `a` is not a `p`-th power for all prime `p ∣ n`.
- `X_pow_sub_C_irreducible_iff_of_odd`:
  For `n` odd, `X ^ n - C a` is irreducible iff `a` is not a `d`-th power for `d ∣ n` and `d ≠ 1`.

TODO: criteria for even `n`. See [serge_lang_algebra] VI,§9.

TODO: relate Kummer extensions of degree 2 with the class `Algebra.IsQuadraticExtension`.

TODO: treat the case where the characteristic `p` of the field divides `n`, so that `K` never
contains a primitive `n`-th root of unity.
For the Galois group part, this is Artin-Schreier theory;
it also holds that `X ^ p - C a` is irreducible iff `a` is not a `p`-th power in `K`.

-/

@[expose] public section
universe u

variable {K : Type u} [Field K]

open Polynomial IntermediateField AdjoinRoot

section Splits

/-
**X_pow_sub_C_splits_of_isPrimitiveRoot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：X_pow_sub_C_splits_of_isPrimitiveRoot {n : Nat} {ζ : K} (hζ : IsPrimitiveR
oot ζ n) {α a : K} (e : α ^ n = a) : (X ^ n - C a).Splits
参数：hζ : IsPrimitiveRoot ζ n；e : α ^ n = a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.eq_zero_or_pos`：∀ (n : ℕ), n = 0 ∨ n > 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHom.map_one`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring α
} {x_1 : NonAssocSemiring β} (f : α →+* β), f 1 = 1
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Polynomial.splits_iff_card_roots`：splits_iff_card_roots : Splits f ↔ f.r
oots.card = f.natDegree
· 使用定理 `Polynomial.nthRoots.eq_1`：∀ {R : Type u} [inst : CommRing R] [inst_1 : I
sDomain R] (n : ℕ) (a : R),   Polynomial.nthRoots n a = (Polynomial.X ^ n - Poly
nomial.C a).ro…
· 使用定理 `IsPrimitiveRoot.card_nthRoots`：card_nthRoots {n : Nat} {ζ : R} (hζ : IsP
rimitiveRoot ζ n) (a : R) : Multiset.card (nthRoots n a) = if exists α, α ^ n = 
a then n else 0
· 使用定理 `Polynomial.natDegree_X_pow_sub_C`：natDegree_X_pow_sub_C {n : Nat} {r : R
} : (X ^ n - C r).natDegree = n
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
theorem X_pow_sub_C_splits_of_isPrimitiveRoot
    {n : ℕ} {ζ : K} (hζ : IsPrimitiveRoot ζ n) {α a : K} (e : α ^ n = a) :
    (X ^ n - C a).Splits := by
  cases n.eq_zero_or_pos with
  | inl hn =>
    simp only [hn, pow_zero, ← C.map_one, ← map_sub, Splits.C]
  | inr hn =>
    rw [splits_iff_card_roots, ← nthRoots, hζ.card_nthRoots, natDegree_X_pow_sub_C, if_pos ⟨α, e⟩]

-- make this private, as we only use it to prove a strictly more general version
private
/-
**X_pow_sub_C_eq_prod'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：X_pow_sub_C_eq_prod' {n : Nat} {ζ : K} (hζ : IsPrimitiveRoot ζ n) {α a : K
} (hn : 0 < n) (e : α ^ n = a) : (X ^ n - C a) = ∏ i in Finset.range n, (X - C (
ζ ^ i * α))
参数：hζ : IsPrimitiveRoot ζ n；hn : 0 < n；e : α ^ n = a。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem X_pow_sub_C_eq_prod'
    {n : ℕ} {ζ : K} (hζ : IsPrimitiveRoot ζ n) {α a : K} (hn : 0 < n) (e : α ^ n = a) :
    (X ^ n - C a) = ∏ i ∈ Finset.range n, (X - C (ζ ^ i * α)) := by
  rw [(X_pow_sub_C_splits_of_isPrimitiveRoot hζ e).eq_prod_roots_of_monic
    (monic_X_pow_sub_C _ hn.ne'), ← nthRoots, hζ.nthRoots_eq e, Multiset.map_map]
  rfl
/-
**X_pow_sub_C_eq_prod** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：X_pow_sub_C_eq_prod {R : Type*} [CommRing R] [IsDomain R] {n : Nat} {ζ : R
} (hζ : IsPrimitiveRoot ζ n) {α a : R} (hn : 0 < n) (e : α ^ n = a) : (X ^ n - C
 a) = ∏ i in Finset.range n, (X - C (ζ ^ i * α))
参数：hζ : IsPrimitiveRoot ζ n；hn : 0 < n；e : α ^ n = a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `FractionRing.instFaithfulSMul`：∀ (R : Type u_1) [inst : CommRing R] (A :
 Type u_4) [inst_1 : CommRing A] [inst_2 : Algebra R A] [FaithfulSMul R A],   Fa
ithfulSMul R (Fract…
· 使用定理 `Module.Free.instFaithfulSMulOfNontrivial`：∀ (R : Type u) (M : Type v) [i
nst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Mod
ule.Free R M] [Nontrivial M], …
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `Polynomial.map_injective`：map_injective (hf : Function.Injective f) : Fu
nction.Injective (map f)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.map_sub`：∀ {R : Type u} [inst : Ring R] {p q : Polynomial R} 
{S : Type u_1} [inst_1 : Ring S] (f : R →+* S),   Polynomial.map f (p - q) = Pol
ynomial.…
· 使用定理 `Polynomial.map_pow`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p :
 Polynomial R} [inst_1 : Semiring S] (f : R →+* S) (n : ℕ),   Polynomial.map f (
p ^ n) =…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.map_X`：map_X : X.map f = X
· 使用定理 `Polynomial.map_C`：map_C : (C a).map f = C (f a)
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
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
· 使用定理 `Polynomial.map_prod`：∀ {R : Type u} {S : Type v} [inst : CommSemiring R]
 [inst_1 : CommSemiring S] (f : R →+* S) {ι : Type u_1}   (g : ι → Polynomial R)
 (s : Fin…
· 使用定理 `Polynomial.map_mul`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p q
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   Polynomial.map f (p * q)
 = Polyn…
· 使用定理 `_private.Mathlib.FieldTheory.KummerExtension.0.X_pow_sub_C_eq_prod'`：∀ {
K : Type u} [inst : Field K] {n : ℕ} {ζ : K},   IsPrimitiveRoot ζ n →     ∀ {α a
 : K},       0 < n →         α ^ n = a → Polynomial.X ^ n…
· 使用定理 `IsPrimitiveRoot.map_of_injective`：map_of_injective [MonoidHomClass F M N
] (h : IsPrimitiveRoot ζ k) (hf : Injective f) : IsPrimitiveRoot (f ζ) k where p
ow_eq_one
-/
lemma X_pow_sub_C_eq_prod {R : Type*} [CommRing R] [IsDomain R]
    {n : ℕ} {ζ : R} (hζ : IsPrimitiveRoot ζ n) {α a : R} (hn : 0 < n) (e : α ^ n = a) :
    (X ^ n - C a) = ∏ i ∈ Finset.range n, (X - C (ζ ^ i * α)) := by
  let K := FractionRing R
  let i := algebraMap R K
  have h := FaithfulSMul.algebraMap_injective R K
  apply_fun Polynomial.map i using map_injective i h
  simpa only [Polynomial.map_sub, Polynomial.map_pow, map_X, map_C, map_mul, map_pow,
    Polynomial.map_prod, Polynomial.map_mul]
    using X_pow_sub_C_eq_prod' (hζ.map_of_injective h) hn <| map_pow i α n ▸ congrArg i e

end Splits

section Irreducible

/-
**X_pow_mul_sub_C_irreducible** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：X_pow_mul_sub_C_irreducible {n m : Nat} {a : K} (hm : Irreducible (X ^ m -
 C a)) (hn : forall (E : Type u) [Field E] [Algebra K E] (x : E) (_ : minpoly K 
x = X ^ m - C a), Irreducible (X ^ n - C (AdjoinSimple.gen K x))) : Irreducible 
(X ^ (n * m) - C a)
参数：hm : Irreducible (X ^ m - C a)；hn : forall (E : Type u) [Field E] [Algebra K 
E] (x : E) (_ : minpoly K x = X ^ m - C a), Irreducible (X ^ n - C (AdjoinSimple
.gen K x))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.not_irreducible_C`：not_irreducible_C (x : R) : ¬Irreducible (
C x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `RingHom.map_one`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring α
} {x_1 : NonAssocSemiring β} (f : α →+* β), f 1 = 1
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.sub_comp`：sub_comp : (p - q).comp r = p.comp r - q.comp r
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.pow_comp`：pow_comp {R : Type*} [CommSemiring R] (p q : R[X]) 
(n : Nat) : (p ^ n).comp q = p.comp q ^ n
· 使用定理 `Polynomial.X_comp`：X_comp : X.comp p = p
· 使用定理 `Polynomial.C_comp`：C_comp : (C a).comp p = C a
· 使用定理 `Polynomial.irreducible_comp`：∀ {K : Type u} [inst : Field K] {f g : Poly
nomial K},   f.Monic →     g.Monic →       Irreducible f →         (∀ (E : Type 
u) [inst_1 : Fiel…
· 使用定理 `Polynomial.monic_X_pow_sub_C`：monic_X_pow_sub_C {R : Type u} [Ring R] (a
 : R) {n : Nat} (h : n != 0) : (X ^ n - C a).Monic
· 使用定理 `Polynomial.monic_X_pow`：monic_X_pow (n : Nat) : Monic (X ^ n : R[X])
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Polynomial.map_pow`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p :
 Polynomial R} [inst_1 : Semiring S] (f : R →+* S) (n : ℕ),   Polynomial.map f (
p ^ n) =…
· 使用定理 `Polynomial.map_X`：map_X : X.map f = X
-/
theorem X_pow_mul_sub_C_irreducible
    {n m : ℕ} {a : K} (hm : Irreducible (X ^ m - C a))
    (hn : ∀ (E : Type u) [Field E] [Algebra K E] (x : E) (_ : minpoly K x = X ^ m - C a),
      Irreducible (X ^ n - C (AdjoinSimple.gen K x))) :
    Irreducible (X ^ (n * m) - C a) := by
  have hm' : m ≠ 0 := by
    rintro rfl
    rw [pow_zero, ← C.map_one, ← map_sub] at hm
    exact not_irreducible_C _ hm
  simpa [pow_mul] using irreducible_comp (monic_X_pow_sub_C a hm') (monic_X_pow n) hm
    (by simpa only [Polynomial.map_pow, map_X] using hn)

-- TODO: generalize to even `n`
/-
**X_pow_sub_C_irreducible_of_odd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：X_pow_sub_C_irreducible_of_odd {n : Nat} (hn : Odd n) {a : K} (ha : forall
 p : Nat, p.Prime -> p ∣ n -> forall b : K, b ^ p != a) : Irreducible (X ^ n - C
 a)
参数：hn : Odd n；ha : forall p : Nat, p.Prime -> p ∣ n -> forall b : K, b ^ p != a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `induction_on_primes`：∀ {motive : ℕ → Prop},   motive 0 → motive 1 → (∀ (
p a : ℕ), Nat.Prime p → motive a → motive (p * a)) → ∀ (n : ℕ), motive n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `Polynomial.irreducible_X_sub_C`：irreducible_X_sub_C (r : R) : Irreducibl
e (X - C r)
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `X_pow_mul_sub_C_irreducible`：X_pow_mul_sub_C_irreducible {n m : Nat} {a 
: K} (hm : Irreducible (X ^ m - C a)) (hn : forall (E : Type u) [Field E] [Algeb
ra K E] (x : E) (…
· 使用定理 `X_pow_sub_C_irreducible_of_prime`：X_pow_sub_C_irreducible_of_prime {p : 
Nat} (hp : p.Prime) {a : K} (ha : forall b : K, b ^ p != a) : Irreducible (X ^ p
 - C a)
· 使用定理 `dvd_mul_right`：dvd_mul_right (a b : α) : a ∣ a * b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `Polynomial.degree_X_pow_sub_C`：degree_X_pow_sub_C {n : Nat} (hn : 0 < n)
 (a : R) : degree ((X : R[X]) ^ n - C a) = n
· 使用定理 `Nat.Prime.pos`：∀ {p : ℕ}, Nat.Prime p → 0 < p
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `Nat.odd_mul`：odd_mul : Odd (m * n) ↔ Odd m ∧ Odd n
· 使用定理 `dvd_mul_of_dvd_right`：dvd_mul_of_dvd_right (h : a ∣ b) (c : α) : a ∣ c *
 b
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `IntermediateField.adjoin.powerBasis_gen`：∀ {K : Type u} [inst : Field K]
 {L : Type u_3} [inst_1 : Field L] [inst_2 : Algebra K L] {x : L} (hx : IsIntegr
al K x),   (IntermediateField…
· 使用定理 `Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly`：∀ {R : Type u_1} {S :
 Type u_2} [inst : CommRing R] [inst_1 : Ring S] [inst_2 : Algebra R S] (pb : Po
werBasis R S),   (Algebra.norm R) pb.ge…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `IntermediateField.adjoin.powerBasis_dim`：∀ {K : Type u} [inst : Field K]
 {L : Type u_3} [inst_1 : Field L] [inst_2 : Algebra K L] {x : L} (hx : IsIntegr
al K x),   (IntermediateField…
（共 52 条，此处仅展示前 30 条）
-/
theorem X_pow_sub_C_irreducible_of_odd
    {n : ℕ} (hn : Odd n) {a : K} (ha : ∀ p : ℕ, p.Prime → p ∣ n → ∀ b : K, b ^ p ≠ a) :
    Irreducible (X ^ n - C a) := by
  induction n using induction_on_primes generalizing K a with
  | zero => simp [← Nat.not_even_iff_odd] at hn
  | one => simpa using irreducible_X_sub_C a
  | prime_mul p n hp IH =>
    rw [mul_comm]
    apply X_pow_mul_sub_C_irreducible
      (X_pow_sub_C_irreducible_of_prime hp (ha p hp (dvd_mul_right _ _)))
    intro E _ _ x hx
    have : IsIntegral K x := not_not.mp fun h ↦ by
      simpa only [degree_zero, degree_X_pow_sub_C hp.pos,
        WithBot.natCast_ne_bot] using congr_arg degree (hx.symm.trans (dif_neg h))
    apply IH (Nat.odd_mul.mp hn).2
    intro q hq hqn b hb
    apply ha q hq (dvd_mul_of_dvd_right hqn p) (Algebra.norm _ b)
    rw [← map_pow, hb, ← adjoin.powerBasis_gen this,
      Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly]
    simp [minpoly_gen, hx, hp.ne_zero.symm, (Nat.odd_mul.mp hn).1.neg_pow]
/-
**X_pow_sub_C_irreducible_iff_forall_prime_of_odd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：X_pow_sub_C_irreducible_iff_forall_prime_of_odd {n : Nat} (hn : Odd n) {a 
: K} : Irreducible (X ^ n - C a) ↔ (forall p : Nat, p.Prime -> p ∣ n -> forall b
 : K, b ^ p != a)
参数：hn : Odd n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `pow_ne_of_irreducible_X_pow_sub_C`：pow_ne_of_irreducible_X_pow_sub_C {n 
: Nat} {a : K} (H : Irreducible (X ^ n - C a)) {m : Nat} (hm : m ∣ n) (hm' : m !
= 1) (b : K) : b ^ m !=…
· 使用定理 `Nat.Prime.ne_one`：∀ {p : ℕ}, Nat.Prime p → p ≠ 1
· 使用定理 `X_pow_sub_C_irreducible_of_odd`：X_pow_sub_C_irreducible_of_odd {n : Nat}
 (hn : Odd n) {a : K} (ha : forall p : Nat, p.Prime -> p ∣ n -> forall b : K, b 
^ p != a) : Irreduci…
-/
theorem X_pow_sub_C_irreducible_iff_forall_prime_of_odd {n : ℕ} (hn : Odd n) {a : K} :
    Irreducible (X ^ n - C a) ↔ (∀ p : ℕ, p.Prime → p ∣ n → ∀ b : K, b ^ p ≠ a) :=
  ⟨fun e _ hp hpn ↦ pow_ne_of_irreducible_X_pow_sub_C e hpn hp.ne_one,
    X_pow_sub_C_irreducible_of_odd hn⟩
/-
**X_pow_sub_C_irreducible_iff_of_odd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：X_pow_sub_C_irreducible_iff_of_odd {n : Nat} (hn : Odd n) {a : K} : Irredu
cible (X ^ n - C a) ↔ (forall d, d ∣ n -> d != 1 -> forall b : K, b ^ d != a)
参数：hn : Odd n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `pow_ne_of_irreducible_X_pow_sub_C`：pow_ne_of_irreducible_X_pow_sub_C {n 
: Nat} {a : K} (H : Irreducible (X ^ n - C a)) {m : Nat} (hm : m ∣ n) (hm' : m !
= 1) (b : K) : b ^ m !=…
· 使用定理 `X_pow_sub_C_irreducible_of_odd`：X_pow_sub_C_irreducible_of_odd {n : Nat}
 (hn : Odd n) {a : K} (ha : forall p : Nat, p.Prime -> p ∣ n -> forall b : K, b 
^ p != a) : Irreduci…
· 使用定理 `Nat.Prime.ne_one`：∀ {p : ℕ}, Nat.Prime p → p ≠ 1
-/
theorem X_pow_sub_C_irreducible_iff_of_odd {n : ℕ} (hn : Odd n) {a : K} :
    Irreducible (X ^ n - C a) ↔ (∀ d, d ∣ n → d ≠ 1 → ∀ b : K, b ^ d ≠ a) :=
  ⟨fun e _ ↦ pow_ne_of_irreducible_X_pow_sub_C e,
    fun H ↦ X_pow_sub_C_irreducible_of_odd hn fun p hp hpn ↦ (H p hpn hp.ne_one)⟩

-- TODO: generalize to `p = 2`
/-
**X_pow_sub_C_irreducible_of_prime_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：X_pow_sub_C_irreducible_of_prime_pow {p : Nat} (hp : p.Prime) (hp' : p != 
2) (n : Nat) {a : K} (ha : forall b : K, b ^ p != a) : Irreducible (X ^ (p ^ n) 
- C a)
参数：hp : p.Prime；hp' : p != 2；n : Nat；ha : forall b : K, b ^ p != a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `X_pow_sub_C_irreducible_of_odd`：X_pow_sub_C_irreducible_of_odd {n : Nat}
 (hn : Odd n) {a : K} (ha : forall p : Nat, p.Prime -> p ∣ n -> forall b : K, b 
^ p != a) : Irreduci…
· 使用引理 `Odd.pow`：Odd.pow {n : Nat} (ha : Odd a) : Odd (a ^ n)
· 使用定理 `Nat.Prime.odd_of_ne_two`：∀ {p : ℕ}, Nat.Prime p → p ≠ 2 → Odd p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.prime_dvd_prime_iff_eq`：prime_dvd_prime_iff_eq {p q : Nat} (pp : p.P
rime) (qp : q.Prime) : p ∣ q ↔ p = q
· 使用定理 `Nat.Prime.dvd_of_dvd_pow`：∀ {p m n : ℕ}, Nat.Prime p → p ∣ m ^ n → p ∣ m
-/
theorem X_pow_sub_C_irreducible_of_prime_pow
    {p : ℕ} (hp : p.Prime) (hp' : p ≠ 2) (n : ℕ) {a : K} (ha : ∀ b : K, b ^ p ≠ a) :
    Irreducible (X ^ (p ^ n) - C a) := by
  apply X_pow_sub_C_irreducible_of_odd (hp.odd_of_ne_two hp').pow
  intro q hq hq'
  simpa [(Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow hq')] using ha
/-
**X_pow_sub_C_irreducible_iff_of_prime_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：X_pow_sub_C_irreducible_iff_of_prime_pow {p : Nat} (hp : p.Prime) (hp' : p
 != 2) {n} (hn : n != 0) {a : K} : Irreducible (X ^ p ^ n - C a) ↔ forall b, b ^
 p != a
参数：hp : p.Prime；hp' : p != 2；hn : n != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `pow_ne_of_irreducible_X_pow_sub_C`：pow_ne_of_irreducible_X_pow_sub_C {n 
: Nat} {a : K} (H : Irreducible (X ^ n - C a)) {m : Nat} (hm : m ∣ n) (hm' : m !
= 1) (b : K) : b ^ m !=…
· 使用引理 `dvd_pow`：dvd_pow (hab : a ∣ b) : forall {n : Nat} (_ : n != 0), a ∣ b ^ 
n | 0, hn => (hn rfl).elim | n + 1, _ => by rw [pow_succ']; exact hab.mul_rig…
· 使用定理 `dvd_rfl`：dvd_rfl : forall {a : α}, a ∣ a
· 使用定理 `Nat.Prime.ne_one`：∀ {p : ℕ}, Nat.Prime p → p ≠ 1
· 使用定理 `X_pow_sub_C_irreducible_of_prime_pow`：X_pow_sub_C_irreducible_of_prime_p
ow {p : Nat} (hp : p.Prime) (hp' : p != 2) (n : Nat) {a : K} (ha : forall b : K,
 b ^ p != a) : Irreducible…
-/
theorem X_pow_sub_C_irreducible_iff_of_prime_pow
    {p : ℕ} (hp : p.Prime) (hp' : p ≠ 2) {n} (hn : n ≠ 0) {a : K} :
    Irreducible (X ^ p ^ n - C a) ↔ ∀ b, b ^ p ≠ a :=
  ⟨(pow_ne_of_irreducible_X_pow_sub_C · (dvd_pow dvd_rfl hn) hp.ne_one),
    X_pow_sub_C_irreducible_of_prime_pow hp hp' n⟩

end Irreducible

/-!
### Galois Group of `K[n√a]`
We first develop the theory for a specific `K[n√a] := AdjoinRoot (X ^ n - C a)`.
The main result is the description of the Galois group: `autAdjoinRootXPowSubCEquiv`.
-/

variable {n : ℕ} (hζ : (primitiveRoots n K).Nonempty)
variable (a : K) (H : Irreducible (X ^ n - C a))

set_option quotPrecheck false in
scoped[KummerExtension] notation3 "K[" n "√" a "]" => AdjoinRoot (Polynomial.X ^ n - Polynomial.C a)

attribute [nolint docBlame] KummerExtension.«termK[_√_]»

open scoped KummerExtension

section AdjoinRoot

include hζ H in
/-- Also see `Polynomial.separable_X_pow_sub_C_unit` -/
/-
**Polynomial.separable_X_pow_sub_C_of_irreducible** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Polynomial.separable_X_pow_sub_C_of_irreducible : (X ^ n - C a).Separable
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.pos_iff_ne_zero`：∀ {n : ℕ}, 0 < n ↔ n ≠ 0
· 使用引理 `ne_zero_of_irreducible_X_pow_sub_C`：ne_zero_of_irreducible_X_pow_sub_C {
n : Nat} {a : K} (H : Irreducible (X ^ n - C a)) : n != 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `Polynomial.separable_X_sub_C`：separable_X_sub_C {x : R} : Separable (X -
 C x)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.separable_map`：separable_map {S} [CommRing S] [Nontrivial S] 
(f : F ->+* S) {p : F[X]} : (p.map f).Separable ↔ p.Separable
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Polynomial.map_sub`：∀ {R : Type u} [inst : Ring R] {p q : Polynomial R} 
{S : Type u_1} [inst_1 : Ring S] (f : R →+* S),   Polynomial.map f (p - q) = Pol
ynomial.…
· 使用定理 `Polynomial.map_pow`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p :
 Polynomial R} [inst_1 : Semiring S] (f : R →+* S) (n : ℕ),   Polynomial.map f (
p ^ n) =…
· 使用定理 `Polynomial.map_C`：map_C : (C a).map f = C (f a)
· 使用定理 `Polynomial.map_X`：map_X : X.map f = X
· 使用定理 `AdjoinRoot.algebraMap_eq`：algebraMap_eq : algebraMap R (AdjoinRoot f) = 
of f
· 使用引理 `X_pow_sub_C_eq_prod`：X_pow_sub_C_eq_prod {R : Type*} [CommRing R] [IsDom
ain R] {n : Nat} {ζ : R} (hζ : IsPrimitiveRoot ζ n) {α a : R} (hn : 0 < n) (e : 
α ^ n = a…
· 使用定理 `IsPrimitiveRoot.map_of_injective`：map_of_injective [MonoidHomClass F M N
] (h : IsPrimitiveRoot ζ k) (hf : Injective f) : IsPrimitiveRoot (f ζ) k where p
ow_eq_one
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `mem_primitiveRoots`：mem_primitiveRoots {ζ : R} (h0 : 0 < k) : ζ in primi
tiveRoots k R ↔ IsPrimitiveRoot ζ k
· 使用定理 `Nat.pos_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → 0 < n
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用引理 `root_X_pow_sub_C_pow`：root_X_pow_sub_C_pow (n : Nat) (a : K) : (AdjoinRo
ot.root (X ^ n - C a)) ^ n = AdjoinRoot.of _ a
· 使用定理 `Polynomial.separable_prod_X_sub_C_iff'`：separable_prod_X_sub_C_iff' {ι :
 Sort _} {f : ι -> F} {s : Finset ι} : (∏ i in s, (X - C (f i))).Separable ↔ for
all x in s, forall y in s, f…
· 使用引理 `IsPrimitiveRoot.injOn_pow_mul`：injOn_pow_mul {n : Nat} {ζ : M₀} (hζ : Is
PrimitiveRoot ζ n) {α : M₀} (hα : α != 0) : Set.InjOn (ζ ^ · * α) (Finset.range 
n)
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用引理 `root_X_pow_sub_C_ne_zero`：root_X_pow_sub_C_ne_zero {n : Nat} (hn : 1 < n
) (a : K) : (AdjoinRoot.root (X ^ n - C a)) != 0
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
Also see `Polynomial.separable_X_pow_sub_C_unit`
-/
theorem Polynomial.separable_X_pow_sub_C_of_irreducible : (X ^ n - C a).Separable := by
  let := Fact.mk H
  let : Algebra K K[n√a] := inferInstance
  have hn := Nat.pos_iff_ne_zero.mpr (ne_zero_of_irreducible_X_pow_sub_C H)
  by_cases hn' : n = 1
  · rw [hn', pow_one]; exact separable_X_sub_C
  have ⟨ζ, hζ⟩ := hζ
  rw [mem_primitiveRoots (Nat.pos_of_ne_zero <| ne_zero_of_irreducible_X_pow_sub_C H)] at hζ
  rw [← separable_map (algebraMap K K[n√a]), Polynomial.map_sub, Polynomial.map_pow, map_C, map_X,
    AdjoinRoot.algebraMap_eq,
    X_pow_sub_C_eq_prod (hζ.map_of_injective (algebraMap K _).injective) hn
    (root_X_pow_sub_C_pow n a), separable_prod_X_sub_C_iff']
  exact (hζ.map_of_injective (algebraMap K K[n√a]).injective).injOn_pow_mul
    (root_X_pow_sub_C_ne_zero (lt_of_le_of_ne (show 1 ≤ n from hn) (Ne.symm hn')) _)

variable (n)

/-- The natural embedding of the roots of unity of `K` into `Gal(K[ⁿ√a]/K)`, by sending
`η ↦ (ⁿ√a ↦ η • ⁿ√a)`. Also see `autAdjoinRootXPowSubC` for the `AlgEquiv` version. -/
noncomputable
/-
**autAdjoinRootXPowSubCHom** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：autAdjoinRootXPowSubCHom : rootsOfUnity n K ->* (K[n√a] ->ₐ[K] K[n√a]) whe
re toFun η
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def autAdjoinRootXPowSubCHom :
    rootsOfUnity n K →* (K[n√a] →ₐ[K] K[n√a]) where
  toFun η := liftAlgHom (X ^ n - C a) (Algebra.ofId _ _) (((η : Kˣ) : K) • (root _) : K[n√a]) <| by
    have := (mem_rootsOfUnity' _ _).mp η.prop
    change aeval _ _ = _
    rw [map_sub, map_pow, aeval_C, aeval_X, Algebra.smul_def, mul_pow, root_X_pow_sub_C_pow,
      AdjoinRoot.algebraMap_eq, ← map_pow, this, map_one, one_mul, sub_self]
  map_one' := algHom_ext <| by simp
  map_mul' := fun ε η ↦ algHom_ext <| by simp [mul_smul, smul_comm ((ε : Kˣ) : K)]

/-- The natural embedding of the roots of unity of `K` into `Gal(K[ⁿ√a]/K)`, by sending
`η ↦ (ⁿ√a ↦ η • ⁿ√a)`. This is an isomorphism when `K` contains a primitive root of unity.
See `autAdjoinRootXPowSubCEquiv`. -/
noncomputable
/-
**autAdjoinRootXPowSubC** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：autAdjoinRootXPowSubC : rootsOfUnity n K ->* (K[n√a] ≃ₐ[K] K[n√a])
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def autAdjoinRootXPowSubC :
    rootsOfUnity n K →* (K[n√a] ≃ₐ[K] K[n√a]) :=
  (AlgEquiv.algHomUnitsEquiv _ _).toMonoidHom.comp (autAdjoinRootXPowSubCHom n a).toHomUnits

variable {n}

set_option backward.isDefEq.respectTransparency.types false in
/-
**autAdjoinRootXPowSubC_root** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：autAdjoinRootXPowSubC_root (η) : autAdjoinRootXPowSubC n a η (root _) = ((
η : Kˣ) : K) • root _
参数：η。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `AdjoinRoot.liftAlgHom_root`：liftAlgHom_root (i : R ->ₐ[S] T) (x : T) (h)
 : liftAlgHom p i x h (root p) = x
-/
lemma autAdjoinRootXPowSubC_root (η) :
    autAdjoinRootXPowSubC n a η (root _) = ((η : Kˣ) : K) • root _ := by
  dsimp [autAdjoinRootXPowSubC, autAdjoinRootXPowSubCHom, AlgEquiv.algHomUnitsEquiv]
  exact liftAlgHom_root _ (Algebra.ofId _ _) ..

variable {a}

/-- The inverse function of `autAdjoinRootXPowSubC` if `K` has all roots of unity.
See `autAdjoinRootXPowSubCEquiv`. -/
noncomputable
/-
**AdjoinRootXPowSubCEquivToRootsOfUnity** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：AdjoinRootXPowSubCEquivToRootsOfUnity [NeZero n] (σ : K[n√a] ≃ₐ[K] K[n√a])
 : rootsOfUnity n K
参数：σ : K[n√a] ≃ₐ[K] K[n√a]。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def AdjoinRootXPowSubCEquivToRootsOfUnity [NeZero n] (σ : K[n√a] ≃ₐ[K] K[n√a]) :
    rootsOfUnity n K :=
  letI := Fact.mk H
  letI : IsDomain K[n√a] := inferInstance
  letI := Classical.decEq K
  (rootsOfUnityEquivOfPrimitiveRoots (n := n) (algebraMap K K[n√a]).injective hζ).symm
    (rootsOfUnity.mkOfPowEq (if a = 0 then 1 else σ (root _) / root _) (by
    -- The if is needed in case `n = 1` and `a = 0` and `K[n√a] = K`.
    split
    · exact one_pow _
    rw [div_pow, ← map_pow]
    simp only [root_X_pow_sub_C_pow, ← AdjoinRoot.algebraMap_eq, AlgEquiv.commutes]
    rw [div_self]
    rwa [Ne, map_eq_zero_iff _ (algebraMap K _).injective]))

/-- The equivalence between the roots of unity of `K` and `Gal(K[ⁿ√a]/K)`. -/
noncomputable
/-
**autAdjoinRootXPowSubCEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：autAdjoinRootXPowSubCEquiv [NeZero n] : rootsOfUnity n K ≃* (K[n√a] ≃ₐ[K] 
K[n√a]) where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def autAdjoinRootXPowSubCEquiv [NeZero n] :
    rootsOfUnity n K ≃* (K[n√a] ≃ₐ[K] K[n√a]) where
  __ := autAdjoinRootXPowSubC n a
  invFun := AdjoinRootXPowSubCEquivToRootsOfUnity hζ H
  left_inv := by
    intro η
    have := Fact.mk H
    have : IsDomain K[n√a] := inferInstance
    let : Algebra K K[n√a] := inferInstance
    apply (rootsOfUnityEquivOfPrimitiveRoots (algebraMap K K[n√a]).injective hζ).injective
    ext
    simp only [AdjoinRoot.algebraMap_eq, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
      autAdjoinRootXPowSubC_root, Algebra.smul_def, MulEquiv.apply_symm_apply,
      rootsOfUnity.val_mkOfPowEq_coe, val_rootsOfUnityEquivOfPrimitiveRoots_apply_coe,
      AdjoinRootXPowSubCEquivToRootsOfUnity]
    split_ifs with h
    · obtain rfl := not_imp_not.mp (fun hn ↦ ne_zero_of_irreducible_X_pow_sub_C' hn H) h
      have : (η : Kˣ) = 1 := (pow_one _).symm.trans η.prop
      simp only [this, Units.val_one, map_one]
    · exact mul_div_cancel_right₀ _ (root_X_pow_sub_C_ne_zero' (NeZero.pos n) h)
  right_inv := by
    intro e
    have := Fact.mk H
    let : Algebra K K[n√a] := inferInstance
    apply AlgEquiv.coe_toAlgHom_injective
    apply AdjoinRoot.algHom_ext
    simp only [AdjoinRootXPowSubCEquivToRootsOfUnity, AdjoinRoot.algebraMap_eq, OneHom.toFun_eq_coe,
      MonoidHom.toOneHom_coe, AlgEquiv.coe_toAlgHom, autAdjoinRootXPowSubC_root, Algebra.smul_def]
    rw [rootsOfUnityEquivOfPrimitiveRoots_symm_apply, rootsOfUnity.val_mkOfPowEq_coe]
    split_ifs with h
    · obtain rfl := not_imp_not.mp (fun hn ↦ ne_zero_of_irreducible_X_pow_sub_C' hn H) h
      rw [(pow_one _).symm.trans (root_X_pow_sub_C_pow 1 a), one_mul,
        ← AdjoinRoot.algebraMap_eq, AlgEquiv.commutes]
    · refine div_mul_cancel₀ _ (root_X_pow_sub_C_ne_zero' (NeZero.pos n) h)
/-
**autAdjoinRootXPowSubCEquiv_root** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：autAdjoinRootXPowSubCEquiv_root [NeZero n] (η) : autAdjoinRootXPowSubCEqui
v hζ H η (root _) = ((η : Kˣ) : K) • root _
参数：η。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用引理 `autAdjoinRootXPowSubC_root`：autAdjoinRootXPowSubC_root (η) : autAdjoinRo
otXPowSubC n a η (root _) = ((η : Kˣ) : K) • root _
-/
lemma autAdjoinRootXPowSubCEquiv_root [NeZero n] (η) :
    autAdjoinRootXPowSubCEquiv hζ H η (root _) = ((η : Kˣ) : K) • root _ :=
  autAdjoinRootXPowSubC_root a η
/-
**autAdjoinRootXPowSubCEquiv_symm_smul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：autAdjoinRootXPowSubCEquiv_symm_smul [NeZero n] (σ) : ((autAdjoinRootXPowS
ubCEquiv hζ H).symm σ : Kˣ) • (root _ : K[n√a]) = σ (root _)
参数：σ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `rootsOfUnityEquivOfPrimitiveRoots_symm_apply`：∀ {R : Type u_4} [inst : C
ommRing R] [inst_1 : IsDomain R] {S : Type u_7} {F : Type u_8} [inst_2 : CommRin
g S]   [inst_3 : IsDomain S] [inst…
· 使用定理 `Units.val_ofPowEqOne`：∀ {M : Type u_1} [inst : Monoid M] (a : M) (n : ℕ)
 (ha : a ^ n = 1) (hn : n ≠ 0), ↑(Units.ofPowEqOne a n ha hn) = a
· 使用引理 `ite_mul`：ite_mul (a b c : α) : (if P then a else b) * c = if P then a * 
c else b * c
· 使用定理 `ite.congr_simp`：∀ {α : Sort u} (c c_1 : Prop),   c = c_1 →     ∀ {h : De
cidable c} [h_1 : Decidable c_1] (t t_1 : α),       t = t_1 → ∀ (e e_1 : α), e =
 e_1…
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `root_X_pow_sub_C_eq_zero_iff`：root_X_pow_sub_C_eq_zero_iff {n : Nat} {a 
: K} (H : Irreducible (X ^ n - C a)) : (AdjoinRoot.root (X ^ n - C a)) = 0 ↔ a =
 0
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用引理 `div_mul_cancel₀`：div_mul_cancel₀ (a : G₀) (h : b != 0) : a / b * b = a
-/
lemma autAdjoinRootXPowSubCEquiv_symm_smul [NeZero n] (σ) :
    ((autAdjoinRootXPowSubCEquiv hζ H).symm σ : Kˣ) • (root _ : K[n√a]) = σ (root _) := by
  have := Fact.mk H
  simp only [autAdjoinRootXPowSubCEquiv, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
    MulEquiv.symm_mk, MulEquiv.coe_mk, Equiv.coe_fn_symm_mk, AdjoinRootXPowSubCEquivToRootsOfUnity,
    AdjoinRoot.algebraMap_eq, rootsOfUnity.mkOfPowEq, Units.smul_def, Algebra.smul_def,
    rootsOfUnityEquivOfPrimitiveRoots_symm_apply, Units.val_ofPowEqOne, ite_mul, one_mul]
  simp_rw [← root_X_pow_sub_C_eq_zero_iff H]
  split_ifs with h
  · rw [h, map_zero]
  · rw [div_mul_cancel₀ _ h]

end AdjoinRoot

/-! ### Galois Group of `IsSplittingField K L (X ^ n - C a)` -/

section IsSplittingField

variable {a}
variable {L : Type*} [Field L] [Algebra K L] [IsSplittingField K L (X ^ n - C a)]

include hζ in
/-
**isSplittingField_AdjoinRoot_X_pow_sub_C** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isSplittingField_AdjoinRoot_X_pow_sub_C : haveI
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.map_sub`：∀ {R : Type u} [inst : Ring R] {p q : Polynomial R} 
{S : Type u_1} [inst_1 : Ring S] (f : R →+* S),   Polynomial.map f (p - q) = Pol
ynomial.…
· 使用定理 `Polynomial.map_pow`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p :
 Polynomial R} [inst_1 : Semiring S] (f : R →+* S) (n : ℕ),   Polynomial.map f (
p ^ n) =…
· 使用定理 `Polynomial.map_C`：map_C : (C a).map f = C (f a)
· 使用定理 `Polynomial.map_X`：map_X : X.map f = X
· 使用定理 `X_pow_sub_C_splits_of_isPrimitiveRoot`：X_pow_sub_C_splits_of_isPrimitive
Root {n : Nat} {ζ : K} (hζ : IsPrimitiveRoot ζ n) {α a : K} (e : α ^ n = a) : (X
 ^ n - C a).Splits
· 使用定理 `IsPrimitiveRoot.map_of_injective`：map_of_injective [MonoidHomClass F M N
] (h : IsPrimitiveRoot ζ k) (hf : Injective f) : IsPrimitiveRoot (f ζ) k where p
ow_eq_one
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `mem_primitiveRoots`：mem_primitiveRoots {ζ : R} (h0 : 0 < k) : ζ in primi
tiveRoots k R ↔ IsPrimitiveRoot ζ k
· 使用定理 `Nat.pos_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → 0 < n
· 使用引理 `ne_zero_of_irreducible_X_pow_sub_C`：ne_zero_of_irreducible_X_pow_sub_C {
n : Nat} {a : K} (H : Irreducible (X ^ n - C a)) : n != 0
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用引理 `root_X_pow_sub_C_pow`：root_X_pow_sub_C_pow (n : Nat) (a : K) : (AdjoinRo
ot.root (X ^ n - C a)) ^ n = AdjoinRoot.of _ a
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AdjoinRoot.adjoinRoot_eq_top`：adjoinRoot_eq_top : Algebra.adjoin R ({roo
t f} : Set (AdjoinRoot f)) = ⊤
· 使用定理 `Algebra.adjoin_mono`：adjoin_mono (H : s subseteq t) : adjoin R s <= adjo
in R t
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
· 使用引理 `Polynomial.mem_rootSet_of_ne`：mem_rootSet_of_ne {p : T[X]} {S : Type*} [
IsDomain T] [CommRing S] [IsDomain S] [Algebra T S] [Module.IsTorsionFree T S] (
hp : p != 0) {a : …
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `Polynomial.X_pow_sub_C_ne_zero`：X_pow_sub_C_ne_zero {n : Nat} (hn : 0 < 
n) (a : R) : (X : R[X]) ^ n - C a != 0
· 使用定理 `Polynomial.aeval_def`：aeval_def (p : R[X]) : aeval x p = eval₂ (algebraM
ap R A) x p
· 使用定理 `AdjoinRoot.algebraMap_eq`：algebraMap_eq : algebraMap R (AdjoinRoot f) = 
of f
· 使用定理 `AdjoinRoot.eval₂_root`：eval₂_root (f : R[X]) : f.eval₂ (of f) (root f) =
 0
-/
lemma isSplittingField_AdjoinRoot_X_pow_sub_C :
    haveI := Fact.mk H
    letI : Algebra K K[n√a] := inferInstance
    IsSplittingField K K[n√a] (X ^ n - C a) := by
  have := Fact.mk H
  let : Algebra K K[n√a] := inferInstance
  constructor
  · rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_C,
      Polynomial.map_X]
    have ⟨_, hζ⟩ := hζ
    rw [mem_primitiveRoots (Nat.pos_of_ne_zero <| ne_zero_of_irreducible_X_pow_sub_C H)] at hζ
    exact X_pow_sub_C_splits_of_isPrimitiveRoot (hζ.map_of_injective (algebraMap K _).injective)
      (root_X_pow_sub_C_pow n a)
  · rw [eq_top_iff, ← AdjoinRoot.adjoinRoot_eq_top]
    apply Algebra.adjoin_mono
    have := ne_zero_of_irreducible_X_pow_sub_C H
    rw [Set.singleton_subset_iff, mem_rootSet_of_ne (X_pow_sub_C_ne_zero
      (Nat.pos_of_ne_zero this) a), aeval_def, AdjoinRoot.algebraMap_eq, AdjoinRoot.eval₂_root]

variable {α : L} (hα : α ^ n = algebraMap K L a)

/-- Suppose `L/K` is the splitting field of `Xⁿ - a`, then a choice of `ⁿ√a` gives an equivalence of
`L` with `K[n√a]`. -/
noncomputable
/-
**adjoinRootXPowSubCEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：adjoinRootXPowSubCEquiv (hζ : (primitiveRoots n K).Nonempty) (H : Irreduci
ble (X ^ n - C a)) (hα : α ^ n = algebraMap K L a) : K[n√a] ≃ₐ[K] L
参数：hζ : (primitiveRoots n K).Nonempty；H : Irreducible (X ^ n - C a)；hα : α ^ n =
 algebraMap K L a。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def adjoinRootXPowSubCEquiv (hζ : (primitiveRoots n K).Nonempty) (H : Irreducible (X ^ n - C a))
    (hα : α ^ n = algebraMap K L a) : K[n√a] ≃ₐ[K] L :=
  .ofBijective (AdjoinRoot.liftAlgHom (X ^ n - C a) (Algebra.ofId _ _) α (by simp [hα])) <| by
    have := Fact.mk H
    let := isSplittingField_AdjoinRoot_X_pow_sub_C hζ H
    refine ⟨(liftAlgHom (X ^ n - C a) _ α _).injective, ?_⟩
    rw [← AlgHom.range_eq_top, ← IsSplittingField.adjoin_rootSet _ (X ^ n - C a),
      eq_comm, Splits.adjoin_rootSet_eq_range, IsSplittingField.adjoin_rootSet]
    exact IsSplittingField.splits _ _
/-
**adjoinRootXPowSubCEquiv_root** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：adjoinRootXPowSubCEquiv_root : adjoinRootXPowSubCEquiv hζ H hα (root _) = 
α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `adjoinRootXPowSubCEquiv.eq_1`：∀ {K : Type u} [inst : Field K] {n : ℕ} {a
 : K} {L : Type u_1} [inst_1 : Field L] [inst_2 : Algebra K L]   [inst_3 : Polyn
omial.IsSplittingF…
· 使用引理 `AlgEquiv.coe_ofBijective`：coe_ofBijective (f : A₁ ->ₐ[R] A₂) (hf : Funct
ion.Bijective f) : (ofBijective f hf : A₁ -> A₂) = f
· 使用引理 `AdjoinRoot.liftAlgHom_root`：liftAlgHom_root (i : R ->ₐ[S] T) (x : T) (h)
 : liftAlgHom p i x h (root p) = x
-/
lemma adjoinRootXPowSubCEquiv_root :
    adjoinRootXPowSubCEquiv hζ H hα (root _) = α := by
  rw [adjoinRootXPowSubCEquiv, AlgEquiv.coe_ofBijective, liftAlgHom_root]
/-
**adjoinRootXPowSubCEquiv_symm_eq_root** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：adjoinRootXPowSubCEquiv_symm_eq_root : (adjoinRootXPowSubCEquiv hζ H hα).s
ymm α = root _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `AlgEquiv.injective`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [ins
t : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : Al
gebra R …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgEquiv.apply_symm_apply`：apply_symm_apply (e : A₁ ≃ₐ[R] A₂) : forall x
, e (e.symm x) = x
· 使用引理 `adjoinRootXPowSubCEquiv_root`：adjoinRootXPowSubCEquiv_root : adjoinRootX
PowSubCEquiv hζ H hα (root _) = α
-/
lemma adjoinRootXPowSubCEquiv_symm_eq_root :
    (adjoinRootXPowSubCEquiv hζ H hα).symm α = root _ := by
  apply (adjoinRootXPowSubCEquiv hζ H hα).injective
  rw [(adjoinRootXPowSubCEquiv hζ H hα).apply_symm_apply, adjoinRootXPowSubCEquiv_root]

include hζ H hα in
/-
**Algebra.adjoin_root_eq_top_of_isSplittingField** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Algebra.adjoin_root_eq_top_of_isSplittingField : Algebra.adjoin K {α} = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Subalgebra.map_injective`：map_injective {f : A ->ₐ[R] B} (hf : Function.
Injective f) : Function.Injective (map f)
· 使用定理 `AlgEquiv.injective`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [ins
t : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : Al
gebra R …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.map_top`：map_top (f : A ->ₐ[R] B) : (⊤ : Subalgebra R A).map f =
 f.range
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `AlgHom.range_eq_top`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : Co
mmSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_3 : Semiring 
B] [inst_…
· 使用定理 `AlgEquiv.surjective`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [in
st : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : A
lgebra R …
· 使用定理 `AlgHom.map_adjoin`：map_adjoin (φ : A ->ₐ[R] B) (s : Set A) : (adjoin R s
).map φ = adjoin R (φ '' s)
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
· 使用定理 `AlgEquiv.coe_toAlgHom`：coe_toAlgHom : DFunLike.coe e.toAlgHom = e
· 使用引理 `adjoinRootXPowSubCEquiv_symm_eq_root`：adjoinRootXPowSubCEquiv_symm_eq_ro
ot : (adjoinRootXPowSubCEquiv hζ H hα).symm α = root _
· 使用定理 `AdjoinRoot.adjoinRoot_eq_top`：adjoinRoot_eq_top : Algebra.adjoin R ({roo
t f} : Set (AdjoinRoot f)) = ⊤
-/
lemma Algebra.adjoin_root_eq_top_of_isSplittingField :
    Algebra.adjoin K {α} = ⊤ := by
  apply Subalgebra.map_injective (B := K[n√a]) (f := (adjoinRootXPowSubCEquiv hζ H hα).symm)
    (adjoinRootXPowSubCEquiv hζ H hα).symm.injective
  rw [Algebra.map_top, (AlgHom.range_eq_top _).mpr
    (adjoinRootXPowSubCEquiv hζ H hα).symm.surjective, AlgHom.map_adjoin,
    Set.image_singleton, AlgEquiv.coe_toAlgHom, adjoinRootXPowSubCEquiv_symm_eq_root,
      adjoinRoot_eq_top]

include hζ H hα in
/-
**IntermediateField.adjoin_root_eq_top_of_isSplittingField** 是 Mathlib 中的一个引理，位于
命名空间 ``。
形式化陈述：IntermediateField.adjoin_root_eq_top_of_isSplittingField : K⟮α⟯ = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IntermediateField.eq_adjoin_of_eq_algebra_adjoin`：eq_adjoin_of_eq_algebr
a_adjoin (K : IntermediateField F E) (h : K.toSubalgebra = Algebra.adjoin F S) :
 K = adjoin F S
· 使用引理 `Algebra.adjoin_root_eq_top_of_isSplittingField`：Algebra.adjoin_root_eq_t
op_of_isSplittingField : Algebra.adjoin K {α} = ⊤
-/
lemma IntermediateField.adjoin_root_eq_top_of_isSplittingField :
    K⟮α⟯ = ⊤ := by
  refine (IntermediateField.eq_adjoin_of_eq_algebra_adjoin _ _ _ ?_).symm
  exact (Algebra.adjoin_root_eq_top_of_isSplittingField hζ H hα).symm

variable (a) (L)

/-- An arbitrary choice of `ⁿ√a` in the splitting field of `Xⁿ - a`. -/
noncomputable
/-
**rootOfSplitsXPowSubC** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：rootOfSplitsXPowSubC (hn : 0 < n) (a : K) (L) [Field L] [Algebra K L] [IsS
plittingField K L (X ^ n - C a)] : L
参数：hn : 0 < n；a : K；L；X ^ n - C a。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
abbrev rootOfSplitsXPowSubC (hn : 0 < n) (a : K)
    (L) [Field L] [Algebra K L] [IsSplittingField K L (X ^ n - C a)] : L :=
  (rootOfSplits (IsSplittingField.splits L (X ^ n - C a))
      (by simpa [degree_X_pow_sub_C hn] using Nat.pos_iff_ne_zero.mp hn))
/-
**rootOfSplitsXPowSubC_pow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：rootOfSplitsXPowSubC_pow [NeZero n] : (rootOfSplitsXPowSubC (NeZero.pos n)
 a L) ^ n = algebraMap K L a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.IsSplittingField.splits`：splits (f : K[X]) [IsSplittingField 
K L f] : Splits (f.map (algebraMap K L))
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.map_sub`：∀ {R : Type u} [inst : Ring R] {p q : Polynomial R} 
{S : Type u_1} [inst_1 : Ring S] (f : R →+* S),   Polynomial.map f (p - q) = Pol
ynomial.…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.map_pow`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p :
 Polynomial R} [inst_1 : Semiring S] (f : R →+* S) (n : ℕ),   Polynomial.map f (
p ^ n) =…
· 使用定理 `Polynomial.map_X`：map_X : X.map f = X
· 使用定理 `Polynomial.map_C`：map_C : (C a).map f = C (f a)
· 使用定理 `Polynomial.degree_X_pow_sub_C`：degree_X_pow_sub_C {n : Nat} (hn : 0 < n)
 (a : R) : degree ((X : R[X]) ^ n - C a) = n
· 使用定理 `NeZero.pos`：pos [PartialOrder α] [IsBotZeroClass α] (a : α) [NeZero a] :
 0 < a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Polynomial.eval_rootOfSplits`：eval_rootOfSplits (hf : f.Splits) (hfd : f
.degree != 0) : f.eval (rootOfSplits hf hfd) = 0
· 使用定理 `Polynomial.eval_map`：eval_map (x : S) : (p.map f).eval x = p.eval₂ f x
· 使用定理 `Polynomial.eval₂_sub`：eval₂_sub {S} [Ring S] (f : R ->+* S) {x : S} : (p
 - q).eval₂ f x = p.eval₂ f x - q.eval₂ f x
· 使用定理 `Polynomial.eval₂_X_pow`：eval₂_X_pow {n : Nat} : (X ^ n).eval₂ f x = x ^ 
n
· 使用定理 `Polynomial.eval₂_C`：eval₂_C : (C a).eval₂ f x = f a
-/
lemma rootOfSplitsXPowSubC_pow [NeZero n] :
    (rootOfSplitsXPowSubC (NeZero.pos n) a L) ^ n = algebraMap K L a := by
  have := eval_rootOfSplits (IsSplittingField.splits L (X ^ n - C a))
    (by simp [degree_X_pow_sub_C (NeZero.pos n), NeZero.ne n])
  simpa only [eval_map, eval₂_sub, eval₂_X_pow, eval₂_C, sub_eq_zero] using this

variable {a}

/-- Suppose `L/K` is the splitting field of `Xⁿ - a`, then `Gal(L/K)` is isomorphic to the
roots of unity in `K` if `K` contains all of them.
Note that this does not depend on a choice of `ⁿ√a`. -/
noncomputable
/-
**autEquivRootsOfUnity** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：autEquivRootsOfUnity [NeZero n] : Gal(L/K) ≃* (rootsOfUnity n K)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `rootOfSplitsXPowSubC_pow`：rootOfSplitsXPowSubC_pow [NeZero n] : (rootOfS
plitsXPowSubC (NeZero.pos n) a L) ^ n = algebraMap K L a
-/
def autEquivRootsOfUnity [NeZero n] :
    Gal(L/K) ≃* (rootsOfUnity n K) :=
  (AlgEquiv.autCongr (adjoinRootXPowSubCEquiv hζ H (rootOfSplitsXPowSubC_pow a L)).symm).trans
    (autAdjoinRootXPowSubCEquiv hζ H).symm
/-
**autEquivRootsOfUnity_apply_rootOfSplit** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：autEquivRootsOfUnity_apply_rootOfSplit [NeZero n] (σ : Gal(L/K)) : σ (root
OfSplitsXPowSubC (NeZero.pos n) a L) = autEquivRootsOfUnity hζ H L σ • (rootOfSp
litsXPowSubC (NeZero.pos n) a L)
参数：σ : Gal(L/K)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `NeZero.pos`：pos [PartialOrder α] [IsBotZeroClass α] (a : α) [NeZero a] :
 0 < a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `MulEquiv.surjective`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul M] [ins
t_1 : Mul N] (e : M ≃* N), Function.Surjective ⇑e
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulEquiv.apply_symm_apply`：apply_symm_apply (e : M ≃* N) (y : N) : e (e.
symm y) = y
· 使用引理 `rootOfSplitsXPowSubC_pow`：rootOfSplitsXPowSubC_pow [NeZero n] : (rootOfS
plitsXPowSubC (NeZero.pos n) a L) ^ n = algebraMap K L a
· 使用定理 `autEquivRootsOfUnity.eq_1`：∀ {K : Type u} [inst : Field K] {n : ℕ} (hζ :
 (primitiveRoots n K).Nonempty) {a : K}   (H : Irreducible (Polynomial.X ^ n - P
olynomial.C a))…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AlgEquiv.autCongr_apply`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂}
 [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3
 : Algebra R …
· 使用引理 `adjoinRootXPowSubCEquiv_symm_eq_root`：adjoinRootXPowSubCEquiv_symm_eq_ro
ot : (adjoinRootXPowSubCEquiv hζ H hα).symm α = root _
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `autAdjoinRootXPowSubCEquiv_root`：autAdjoinRootXPowSubCEquiv_root [NeZero
 n] (η) : autAdjoinRootXPowSubCEquiv hζ H η (root _) = ((η : Kˣ) : K) • root _
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用引理 `adjoinRootXPowSubCEquiv_root`：adjoinRootXPowSubCEquiv_root : adjoinRootX
PowSubCEquiv hζ H hα (root _) = α
-/
lemma autEquivRootsOfUnity_apply_rootOfSplit [NeZero n] (σ : Gal(L/K)) :
    σ (rootOfSplitsXPowSubC (NeZero.pos n) a L) =
      autEquivRootsOfUnity hζ H L σ • (rootOfSplitsXPowSubC (NeZero.pos n) a L) := by
  obtain ⟨η, rfl⟩ := (autEquivRootsOfUnity hζ H L).symm.surjective σ
  rw [MulEquiv.apply_symm_apply, autEquivRootsOfUnity]
  simp only [MulEquiv.symm_trans_apply, AlgEquiv.autCongr_symm, AlgEquiv.symm_symm,
    MulEquiv.symm_symm, AlgEquiv.autCongr_apply, AlgEquiv.trans_apply,
    adjoinRootXPowSubCEquiv_symm_eq_root, autAdjoinRootXPowSubCEquiv_root, map_smul,
    adjoinRootXPowSubCEquiv_root]
  rfl

include hα in
/-
**autEquivRootsOfUnity_smul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：autEquivRootsOfUnity_smul [NeZero n] (σ : Gal(L/K)) : autEquivRootsOfUnity
 hζ H L σ • α = σ α
参数：σ : Gal(L/K)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `NeZero.pos`：pos [PartialOrder α] [IsBotZeroClass α] (a : α) [NeZero a] :
 0 < a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsPrimitiveRoot.nthRoots_eq`：nthRoots_eq {n : Nat} {ζ : R} (hζ : IsPrimi
tiveRoot ζ n) {α a : R} (e : α ^ n = a) : nthRoots n a = (Multiset.range n).map 
(ζ ^ · * α)
· 使用定理 `IsPrimitiveRoot.map_of_injective`：map_of_injective [MonoidHomClass F M N
] (h : IsPrimitiveRoot ζ k) (hf : Injective f) : IsPrimitiveRoot (f ζ) k where p
ow_eq_one
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `mem_primitiveRoots`：mem_primitiveRoots {ζ : R} (h0 : 0 < k) : ζ in primi
tiveRoots k R ↔ IsPrimitiveRoot ζ k
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用引理 `rootOfSplitsXPowSubC_pow`：rootOfSplitsXPowSubC_pow [NeZero n] : (rootOfS
plitsXPowSubC (NeZero.pos n) a L) ^ n = algebraMap K L a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.mem_nthRoots`：mem_nthRoots {n : Nat} (hn : 0 < n) {a x : R} :
 x in nthRoots n a ↔ x ^ n = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用引理 `autEquivRootsOfUnity_apply_rootOfSplit`：autEquivRootsOfUnity_apply_rootO
fSplit [NeZero n] (σ : Gal(L/K)) : σ (rootOfSplitsXPowSubC (NeZero.pos n) a L) =
 autEquivRootsOfUnity hζ H L…
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
-/
lemma autEquivRootsOfUnity_smul [NeZero n] (σ : Gal(L/K)) :
    autEquivRootsOfUnity hζ H L σ • α = σ α := by
  have ⟨ζ, hζ'⟩ := hζ
  have hn := NeZero.pos n
  rw [mem_primitiveRoots hn] at hζ'
  rw [← mem_nthRoots hn, (hζ'.map_of_injective (algebraMap K L).injective).nthRoots_eq
    (rootOfSplitsXPowSubC_pow a L)] at hα
  simp only [Multiset.mem_map, Multiset.mem_range] at hα
  obtain ⟨i, _, rfl⟩ := hα
  simp only [← map_pow, ← Algebra.smul_def, map_smul,
    autEquivRootsOfUnity_apply_rootOfSplit hζ H L]
  exact smul_comm _ _ _

/-- Suppose `L/K` is the splitting field of `Xⁿ - a`, and `ζ` is an `n`-th primitive root of unity
in `K`, then `Gal(L/K)` is isomorphic to `ZMod n`. -/
noncomputable
/-
**autEquivZmod** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：autEquivZmod [NeZero n] {ζ : K} (hζ : IsPrimitiveRoot ζ n) : Gal(L/K) ≃* M
ultiplicative (ZMod n)
参数：hζ : IsPrimitiveRoot ζ n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def autEquivZmod [NeZero n] {ζ : K} (hζ : IsPrimitiveRoot ζ n) :
    Gal(L/K) ≃* Multiplicative (ZMod n) :=
  haveI hn := ne_zero_of_irreducible_X_pow_sub_C H
  (autEquivRootsOfUnity ⟨ζ, (mem_primitiveRoots <| Nat.pos_of_ne_zero hn).mpr hζ⟩ H L).trans
    ((MulEquiv.subgroupCongr (IsPrimitiveRoot.zpowers_eq (hζ.isUnit_unit' hn)).symm).trans
        (hζ.isUnit_unit' hn).zmodEquivZPowers.symm.toMultiplicativeRight)

include hα in
/-
**autEquivZmod_symm_apply_intCast** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：autEquivZmod_symm_apply_intCast [NeZero n] {ζ : K} (hζ : IsPrimitiveRoot ζ
 n) (m : Int) : (autEquivZmod H L hζ).symm (Multiplicative.ofAdd (m : ZMod n)) α
 = ζ ^ m • α
参数：hζ : IsPrimitiveRoot ζ n；m : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.pos_iff_ne_zero`：∀ {n : ℕ}, 0 < n ↔ n ≠ 0
· 使用引理 `ne_zero_of_irreducible_X_pow_sub_C`：ne_zero_of_irreducible_X_pow_sub_C {
n : Nat} {a : K} (H : Irreducible (X ^ n - C a)) : n != 0
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `mem_primitiveRoots`：mem_primitiveRoots {ζ : R} (h0 : 0 < k) : ζ in primi
tiveRoots k R ↔ IsPrimitiveRoot ζ k
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `autEquivRootsOfUnity_smul`：autEquivRootsOfUnity_smul [NeZero n] (σ : Gal
(L/K)) : autEquivRootsOfUnity hζ H L σ • α = σ α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AddEquiv.toMultiplicativeRight_apply_symm_apply`：∀ {G : Type u_2} {H : T
ype u_3} [inst : MulOneClass G] [inst_1 : AddZeroClass H] (f : Additive G ≃+ H) 
  (a : Multiplicative H),   (AddEquiv…
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
· 使用定理 `AddMonoidHom.toMultiplicativeLeft_apply_apply`：∀ {α : Type u_3} {β : Typ
e u_4} [inst : AddZeroClass α] [inst_1 : MulOneClass β] (f : α →+ Additive β)   
(a : Multiplicative α), (AddMonoidH…
· 使用定理 `IsPrimitiveRoot.zmodEquivZPowers_apply_coe_int`：zmodEquivZPowers_apply_c
oe_int (i : Int) : h.zmodEquivZPowers i = Additive.ofMul (⟨ζ ^ i, i, rfl⟩ : Subg
roup.zpowers ζ)
· 使用定理 `MulEquiv.apply_symm_apply`：apply_symm_apply (e : M ≃* N) (y : N) : e (e.
symm y) = y
· 使用定理 `Units.val_zpow_eq_zpow_val`：val_zpow_eq_zpow_val : forall (u : αˣ) (n : 
Int), ((u ^ n : αˣ) : α) = (u : α) ^ n
· 使用定理 `IsUnit.val_unit'`：∀ {α : Type u} [inst : DivisionMonoid α] {a : α} (h : 
IsUnit a), ↑h.unit' = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma autEquivZmod_symm_apply_intCast [NeZero n] {ζ : K} (hζ : IsPrimitiveRoot ζ n) (m : ℤ) :
    (autEquivZmod H L hζ).symm (Multiplicative.ofAdd (m : ZMod n)) α = ζ ^ m • α := by
  have hn := Nat.pos_iff_ne_zero.mpr (ne_zero_of_irreducible_X_pow_sub_C H)
  rw [← autEquivRootsOfUnity_smul ⟨ζ, (mem_primitiveRoots hn).mpr hζ⟩ H L hα]
  simp [MulEquiv.subgroupCongr_symm_apply, Subgroup.smul_def, Units.smul_def, autEquivZmod]

include hα in
/-
**autEquivZmod_symm_apply_natCast** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：autEquivZmod_symm_apply_natCast [NeZero n] {ζ : K} (hζ : IsPrimitiveRoot ζ
 n) (m : Nat) : (autEquivZmod H L hζ).symm (Multiplicative.ofAdd (m : ZMod n)) α
 = ζ ^ m • α
参数：hζ : IsPrimitiveRoot ζ n；m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用引理 `autEquivZmod_symm_apply_intCast`：autEquivZmod_symm_apply_intCast [NeZero
 n] {ζ : K} (hζ : IsPrimitiveRoot ζ n) (m : Int) : (autEquivZmod H L hζ).symm (M
ultiplicative.ofAdd (…
-/
lemma autEquivZmod_symm_apply_natCast [NeZero n] {ζ : K} (hζ : IsPrimitiveRoot ζ n) (m : ℕ) :
    (autEquivZmod H L hζ).symm (Multiplicative.ofAdd (m : ZMod n)) α = ζ ^ m • α := by
  simpa only [Int.cast_natCast, zpow_natCast] using autEquivZmod_symm_apply_intCast H L hα hζ m

include hζ H in
/-
**isCyclic_of_isSplittingField_X_pow_sub_C** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isCyclic_of_isSplittingField_X_pow_sub_C [NeZero n] : IsCyclic Gal(L/K)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.pos_iff_ne_zero`：∀ {n : ℕ}, 0 < n ↔ n ≠ 0
· 使用引理 `ne_zero_of_irreducible_X_pow_sub_C`：ne_zero_of_irreducible_X_pow_sub_C {
n : Nat} {a : K} (H : Irreducible (X ^ n - C a)) : n != 0
· 使用定理 `isCyclic_of_surjective`：isCyclic_of_surjective {F : Type*} [hH : IsCycli
c G'] [FunLike F G' G] [MonoidHomClass F G' G] (f : F) (hf : Function.Surjective
 f) : IsCycl…
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_primitiveRoots`：mem_primitiveRoots {ζ : R} (h0 : 0 < k) : ζ in primi
tiveRoots k R ↔ IsPrimitiveRoot ζ k
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `MulEquiv.surjective`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul M] [ins
t_1 : Mul N] (e : M ≃* N), Function.Surjective ⇑e
-/
lemma isCyclic_of_isSplittingField_X_pow_sub_C [NeZero n] : IsCyclic Gal(L/K) :=
  have hn := Nat.pos_iff_ne_zero.mpr (ne_zero_of_irreducible_X_pow_sub_C H)
  isCyclic_of_surjective _
    (autEquivZmod H _ <| (mem_primitiveRoots hn).mp hζ.choose_spec).symm.surjective

include hζ H in
/-
**isGalois_of_isSplittingField_X_pow_sub_C** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isGalois_of_isSplittingField_X_pow_sub_C : IsGalois K L
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsGalois.of_separable_splitting_field`：of_separable_splitting_field [p.I
sSplittingField F E] (hp : p.Separable) : IsGalois F E
· 使用定理 `Polynomial.separable_X_pow_sub_C_of_irreducible`：Polynomial.separable_X_
pow_sub_C_of_irreducible : (X ^ n - C a).Separable
-/
lemma isGalois_of_isSplittingField_X_pow_sub_C : IsGalois K L :=
  IsGalois.of_separable_splitting_field (separable_X_pow_sub_C_of_irreducible hζ a H)

include hζ H in
/-
**finrank_of_isSplittingField_X_pow_sub_C** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：finrank_of_isSplittingField_X_pow_sub_C : Module.finrank K L = n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Polynomial.IsSplittingField.finiteDimensional`：finiteDimensional (f : K[
X]) [IsSplittingField K L f] : FiniteDimensional K L
· 使用引理 `isGalois_of_isSplittingField_X_pow_sub_C`：isGalois_of_isSplittingField_X
_pow_sub_C : IsGalois K L
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.pos_iff_ne_zero`：∀ {n : ℕ}, 0 < n ↔ n ≠ 0
· 使用引理 `ne_zero_of_irreducible_X_pow_sub_C`：ne_zero_of_irreducible_X_pow_sub_C {
n : Nat} {a : K} (H : Irreducible (X ^ n - C a)) : n != 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsGalois.card_aut_eq_finrank`：card_aut_eq_finrank [FiniteDimensional F E
] [IsGalois F E] : Nat.card Gal(E/F) = finrank F E
· 使用定理 `Nat.card_congr`：card_congr (f : α ≃ β) : Nat.card α = Nat.card β
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_primitiveRoots`：mem_primitiveRoots {ζ : R} (h0 : 0 < k) : ζ in primi
tiveRoots k R ↔ IsPrimitiveRoot ζ k
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `Nat.card_zmod`：card_zmod (n : Nat) : Nat.card (ZMod n) = n
-/
lemma finrank_of_isSplittingField_X_pow_sub_C : Module.finrank K L = n := by
  have := Polynomial.IsSplittingField.finiteDimensional L (X ^ n - C a)
  have := isGalois_of_isSplittingField_X_pow_sub_C hζ H L
  have hn := Nat.pos_iff_ne_zero.mpr (ne_zero_of_irreducible_X_pow_sub_C H)
  have : NeZero n := ⟨ne_zero_of_irreducible_X_pow_sub_C H⟩
  rw [← IsGalois.card_aut_eq_finrank, Nat.card_congr ((autEquivZmod H L <|
    (mem_primitiveRoots hn).mp hζ.choose_spec).toEquiv.trans Multiplicative.toAdd), Nat.card_zmod]

end IsSplittingField

/-! ### Cyclic extensions of order `n` when `K` has all `n`-th roots of unity. -/

section IsCyclic

variable {L} [Field L] [Algebra K L] [FiniteDimensional K L]
variable (hK : (primitiveRoots (Module.finrank K L) K).Nonempty)

open Module
variable (K L)

include hK in
/-- If `L/K` is a cyclic extension of degree `n`, and `K` contains all `n`-th roots of unity,
then `L = K[α]` for some `α ^ n ∈ K`. -/
/-
**exists_root_adjoin_eq_top_of_isCyclic** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：exists_root_adjoin_eq_top_of_isCyclic [IsGalois K L] [IsCyclic Gal(L/K)] :
 exists (α : L), α ^ (finrank K L) in Set.range (algebraMap K L) ∧ K⟮α⟯ = ⊤
参数：L/K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `orderOf_eq_card_of_forall_mem_zpowers`：orderOf_eq_card_of_forall_mem_zpo
wers {g : α} (hx : forall x, x in zpowers g) : orderOf g = Nat.card α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `minpoly_algEquiv_toLinearMap`：minpoly_algEquiv_toLinearMap (σ : L ≃ₐ[K] 
L) (hσ : IsOfFinOrder σ) : minpoly K σ.toLinearMap = X ^ (orderOf σ) - C 1
· 使用引理 `isOfFinOrder_of_finite`：isOfFinOrder_of_finite (x : G) : IsOfFinOrder x
· 使用定理 `Finite.algEquiv`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [inst :
 CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : Algeb
ra R …
· 使用定理 `instFiniteAlgHomOfFinite`：∀ (R : Type u_1) [inst : CommSemiring R] (K : 
Type u_2) [inst_1 : Field K] [inst_2 : Algebra R K] (S : Type u_3)   [inst_3 : S
emiring S] [in…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `IsGalois.card_aut_eq_finrank`：card_aut_eq_finrank [FiniteDimensional F E
] [IsGalois F E] : Nat.card Gal(E/F) = finrank F E
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
· 使用定理 `Polynomial.eval_sub`：eval_sub (p q : R[X]) (x : R) : (p - q).eval x = p.
eval x - q.eval x
· 使用定理 `Polynomial.eval_pow`：eval_pow (n : Nat) : (p ^ n).eval x = p.eval x ^ n
· 使用定理 `Polynomial.eval_X`：eval_X : X.eval x = x
· 使用定理 `Polynomial.eval_one`：eval_one : (1 : R[X]).eval x = 1
· 使用定理 `IsPrimitiveRoot.pow_eq_one`：∀ {M : Type u_1} [inst : CommMonoid M] {ζ : 
M} {k : ℕ}, IsPrimitiveRoot ζ k → ζ ^ k = 1
· 使用定理 `mem_primitiveRoots`：mem_primitiveRoots {ζ : R} (h0 : 0 < k) : ζ in primi
tiveRoots k R ↔ IsPrimitiveRoot ζ k
· 使用定理 `Module.finrank_pos`：Module.finrank_pos [IsDomain R] [IsTorsionFree R M] 
[h : Nontrivial M] : 0 < finrank R M
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `Module.End.HasEigenvalue.exists_hasEigenvector`：∀ {R : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]  
 {f : Module.End R M} {μ : R}, f.Has…
· 使用定理 `Module.End.hasEigenvalue_of_isRoot`：hasEigenvalue_of_isRoot (h : (minpol
y R f).IsRoot μ) : f.HasEigenvalue μ
· 使用定理 `Module.End.HasEigenvector.pow_apply`：∀ {R : Type v} {M : Type w} [inst :
 CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   {f : Modul
e.End R M} {μ : R} {v : M…
（共 64 条，此处仅展示前 30 条）

--- 原说明 ---
If `L/K` is a cyclic extension of degree `n`, and `K` contains all `n`-th roots 
of unity,
then `L = K[α]` for some `α ^ n ∈ K`.
-/
lemma exists_root_adjoin_eq_top_of_isCyclic [IsGalois K L] [IsCyclic Gal(L/K)] :
    ∃ (α : L), α ^ (finrank K L) ∈ Set.range (algebraMap K L) ∧ K⟮α⟯ = ⊤ := by
  -- Let `ζ` be an `n`-th root of unity, and `σ` be a generator of `Gal(L/K)`.
  have ⟨ζ, hζ⟩ := hK
  rw [mem_primitiveRoots finrank_pos] at hζ
  obtain ⟨σ, hσ⟩ := ‹IsCyclic Gal(L/K)›
  have hσ' := orderOf_eq_card_of_forall_mem_zpowers hσ
  -- Since the minimal polynomial of `σ` over `K` is `Xⁿ - 1`,
  -- `σ` has an eigenvector `v` with eigenvalue `ζ`.
  have : IsRoot (minpoly K σ.toLinearMap) ζ := by
    rw [IsGalois.card_aut_eq_finrank] at hσ'
    simpa [minpoly_algEquiv_toLinearMap σ (isOfFinOrder_of_finite σ), hσ',
      sub_eq_zero] using hζ.pow_eq_one
  obtain ⟨v, hv⟩ := (Module.End.hasEigenvalue_of_isRoot this).exists_hasEigenvector
  have hv' := hv.pow_apply
  simp_rw [← AlgEquiv.pow_toLinearMap, AlgEquiv.toLinearMap_apply] at hv'
  -- We claim that `v` is the desired root.
  refine ⟨v, ?_, ?_⟩
  · -- Since `v ^ n` is fixed by `σ` (`σ (v ^ n) = ζ ^ n • v ^ n = v ^ n`), it is in `K`.
    rw [← IntermediateField.mem_bot,
      ← OrderIso.map_bot IsGalois.intermediateFieldEquivSubgroup.symm]
    intro ⟨σ', hσ'⟩
    obtain ⟨n, rfl : σ ^ n = σ'⟩ := mem_powers_iff_mem_zpowers.mpr (hσ σ')
    rw [smul_pow', Submonoid.smul_def, AlgEquiv.smul_def, hv', smul_pow, ← pow_mul,
      mul_comm, pow_mul, hζ.pow_eq_one, one_pow, one_smul]
  · -- Since `σ` does not fix `K⟮α⟯`, `K⟮α⟯` is `L`.
    apply IsGalois.intermediateFieldEquivSubgroup.injective
    rw [map_top, eq_top_iff]
    intro σ' hσ'
    obtain ⟨n, rfl : σ ^ n = σ'⟩ := mem_powers_iff_mem_zpowers.mpr (hσ σ')
    have := hσ' ⟨v, IntermediateField.mem_adjoin_simple_self K v⟩
    simp only [AlgEquiv.smul_def, hv'] at this
    conv_rhs at this => rw [← one_smul K v]
    obtain ⟨k, rfl⟩ := hζ.dvd_of_pow_eq_one n (smul_left_injective K hv.2 this)
    rw [pow_mul, ← IsGalois.card_aut_eq_finrank, pow_card_eq_one', one_pow]
    exact one_mem _

variable {K L}
/-
**irreducible_X_pow_sub_C_of_root_adjoin_eq_top** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：irreducible_X_pow_sub_C_of_root_adjoin_eq_top {a : K} {α : L} (ha : α ^ (f
inrank K L) = algebraMap K L a) (hα : K⟮α⟯ = ⊤) : Irreducible (X ^ (finrank K L)
 - C a)
参数：ha : α ^ (finrank K L) = algebraMap K L a；hα : K⟮α⟯ = ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `minpoly.unique`：unique {p : A[X]} (pmonic : p.Monic) (hp : Polynomial.ae
val x p = 0) (pmin : forall q : A[X], q.Monic -> Polynomial.aeval x q = 0 -> deg
ree …
· 使用定理 `Polynomial.monic_X_pow_sub_C`：monic_X_pow_sub_C {R : Type u} [Ring R] (a
 : R) {n : Nat} (h : n != 0) : (X ^ n - C a).Monic
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Module.finrank_pos`：Module.finrank_pos [IsDomain R] [IsTorsionFree R M] 
[h : Nontrivial M] : 0 < finrank R M
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.eval₂_sub`：eval₂_sub {S} [Ring S] (f : R ->+* S) {x : S} : (p
 - q).eval₂ f x = p.eval₂ f x - q.eval₂ f x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.eval₂_X_pow`：eval₂_X_pow {n : Nat} : (X ^ n).eval₂ f x = x ^ 
n
· 使用定理 `Polynomial.eval₂_C`：eval₂_C : (C a).eval₂ f x = f a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Polynomial.degree_X_pow_sub_C`：degree_X_pow_sub_C {n : Nat} (hn : 0 < n)
 (a : R) : degree ((X : R[X]) ^ n - C a) = n
· 使用定理 `Polynomial.degree_eq_natDegree`：degree_eq_natDegree (hp : p != 0) : degr
ee p = (natDegree p : WithBot Nat)
· 使用定理 `minpoly.ne_zero`：ne_zero [Nontrivial A] (hx : IsIntegral A x) : minpoly 
A x != 0
· 使用定理 `IsIntegral.of_finite`：IsIntegral.of_finite [Module.Finite R B] (x : B) :
 IsIntegral R x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IntermediateField.adjoin.finrank`：∀ {K : Type u} [inst : Field K] {L : T
ype u_3} [inst_1 : Field L] [inst_2 : Algebra K L] {x : L},   IsIntegral K x → M
odule.finrank K ↥K⟮x⟯ …
· 使用定理 `Nat.cast_le`：cast_le : (m : α) <= n ↔ m <= n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
（共 37 条，此处仅展示前 30 条）
-/
lemma irreducible_X_pow_sub_C_of_root_adjoin_eq_top
    {a : K} {α : L} (ha : α ^ (finrank K L) = algebraMap K L a) (hα : K⟮α⟯ = ⊤) :
    Irreducible (X ^ (finrank K L) - C a) := by
  have : X ^ (finrank K L) - C a = minpoly K α := by
    refine minpoly.unique _ _ (monic_X_pow_sub_C _ finrank_pos.ne.symm) ?_ ?_
    · simp only [aeval_def, eval₂_sub, eval₂_X_pow, ha, eval₂_C, sub_self]
    · intro q hq hq'
      refine le_trans ?_ (degree_le_of_dvd (minpoly.dvd _ _ hq') hq.ne_zero)
      rw [degree_X_pow_sub_C finrank_pos,
        degree_eq_natDegree (minpoly.ne_zero (IsIntegral.of_finite K α)),
        ← IntermediateField.adjoin.finrank (IsIntegral.of_finite K α), hα, Nat.cast_le]
      exact (finrank_top K L).ge
  exact this ▸ minpoly.irreducible (IsIntegral.of_finite K α)

include hK in
/-
**isSplittingField_X_pow_sub_C_of_root_adjoin_eq_top** 是 Mathlib 中的一个引理，位于命名空间 `
`。
形式化陈述：isSplittingField_X_pow_sub_C_of_root_adjoin_eq_top {a : K} {α : L} (ha : α
 ^ (finrank K L) = algebraMap K L a) (hα : K⟮α⟯ = ⊤) : IsSplittingField K L (X ^
 (finrank K L) - C a)
参数：ha : α ^ (finrank K L) = algebraMap K L a；hα : K⟮α⟯ = ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.map_sub`：∀ {R : Type u} [inst : Ring R] {p q : Polynomial R} 
{S : Type u_1} [inst_1 : Ring S] (f : R →+* S),   Polynomial.map f (p - q) = Pol
ynomial.…
· 使用定理 `Polynomial.map_pow`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p :
 Polynomial R} [inst_1 : Semiring S] (f : R →+* S) (n : ℕ),   Polynomial.map f (
p ^ n) =…
· 使用定理 `Polynomial.map_C`：map_C : (C a).map f = C (f a)
· 使用定理 `Polynomial.map_X`：map_X : X.map f = X
· 使用定理 `X_pow_sub_C_splits_of_isPrimitiveRoot`：X_pow_sub_C_splits_of_isPrimitive
Root {n : Nat} {ζ : K} (hζ : IsPrimitiveRoot ζ n) {α a : K} (e : α ^ n = a) : (X
 ^ n - C a).Splits
· 使用定理 `IsPrimitiveRoot.map_of_injective`：map_of_injective [MonoidHomClass F M N
] (h : IsPrimitiveRoot ζ k) (hf : Injective f) : IsPrimitiveRoot (f ζ) k where p
ow_eq_one
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `mem_primitiveRoots`：mem_primitiveRoots {ζ : R} (h0 : 0 < k) : ζ in primi
tiveRoots k R ↔ IsPrimitiveRoot ζ k
· 使用定理 `Module.finrank_pos`：Module.finrank_pos [IsDomain R] [IsTorsionFree R M] 
[h : Nontrivial M] : 0 < finrank R M
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IntermediateField.top_toSubalgebra`：top_toSubalgebra : (⊤ : Intermediate
Field F E).toSubalgebra = ⊤
· 使用定理 `IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic`：adjoin_simp
le_toSubalgebra_of_isAlgebraic (hα : IsAlgebraic F α) : F⟮α⟯.toSubalgebra = F[α]
· 使用定理 `IsAlgebraic.of_finite`：IsAlgebraic.of_finite (e : A) [Module.Finite R A]
 : IsAlgebraic R e
· 使用定理 `Algebra.adjoin_mono`：adjoin_mono (H : s subseteq t) : adjoin R s <= adjo
in R t
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
· 使用引理 `Polynomial.mem_rootSet_of_ne`：mem_rootSet_of_ne {p : T[X]} {S : Type*} [
IsDomain T] [CommRing S] [IsDomain S] [Algebra T S] [Module.IsTorsionFree T S] (
hp : p != 0) {a : …
· 使用定理 `Polynomial.X_pow_sub_C_ne_zero`：X_pow_sub_C_ne_zero {n : Nat} (hn : 0 < 
n) (a : R) : (X : R[X]) ^ n - C a != 0
· 使用定理 `Polynomial.aeval_def`：aeval_def (p : R[X]) : aeval x p = eval₂ (algebraM
ap R A) x p
· 使用定理 `Polynomial.eval₂_sub`：eval₂_sub {S} [Ring S] (f : R ->+* S) {x : S} : (p
 - q).eval₂ f x = p.eval₂ f x - q.eval₂ f x
（共 33 条，此处仅展示前 30 条）
-/
lemma isSplittingField_X_pow_sub_C_of_root_adjoin_eq_top
    {a : K} {α : L} (ha : α ^ (finrank K L) = algebraMap K L a) (hα : K⟮α⟯ = ⊤) :
    IsSplittingField K L (X ^ (finrank K L) - C a) := by
  constructor
  · rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_C,
      Polynomial.map_X]
    have ⟨_, hζ⟩ := hK
    rw [mem_primitiveRoots finrank_pos] at hζ
    exact X_pow_sub_C_splits_of_isPrimitiveRoot (hζ.map_of_injective (algebraMap K _).injective) ha
  · rw [eq_top_iff, ← IntermediateField.top_toSubalgebra, ← hα,
      IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic (IsAlgebraic.of_finite K α)]
    apply Algebra.adjoin_mono
    rw [Set.singleton_subset_iff, mem_rootSet_of_ne (X_pow_sub_C_ne_zero finrank_pos a),
      aeval_def, eval₂_sub, eval₂_X_pow, eval₂_C, ha, sub_self]

end IsCyclic

open Module in
/--
Suppose `L/K` is a finite extension of dimension `n`,
and `K` contains a primitive`n`-th root of unity.
Then `L/K` is cyclic iff
`L` is a splitting field of some irreducible polynomial of the form `Xⁿ - a : K[X]` iff
`L = K[α]` for some `αⁿ ∈ K`.
-/
/-
**isCyclic_tfae** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isCyclic_tfae (K L) [Field K] [Field L] [Algebra K L] [FiniteDimensional K
 L] (hK : (primitiveRoots (Module.finrank K L) K).Nonempty) : List.TFAE [ IsGalo
is K L ∧ IsCyclic Gal(L/K), exists a : K, Irreducible (X ^ (finrank K L) - C a) 
∧ IsSplittingField K L (X ^ (finrank K L) - C a), exists (α : L), α ^ (finrank K
 L) in Set.range (algebraMap K L) ∧ K⟮α⟯ = ⊤]
参数：K L；hK : (primitiveRoots (Module.finrank K L) K).Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `NeZero.of_pos`：of_pos [Preorder M] [Zero M] (h : 0 < x) : NeZero x
· 使用定理 `Module.finrank_pos`：Module.finrank_pos [IsDomain R] [IsTorsionFree R M] 
[h : Nontrivial M] : 0 < finrank R M
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用引理 `exists_root_adjoin_eq_top_of_isCyclic`：exists_root_adjoin_eq_top_of_isCy
clic [IsGalois K L] [IsCyclic Gal(L/K)] : exists (α : L), α ^ (finrank K L) in S
et.range (algebraMap K L) ∧…
· 使用引理 `irreducible_X_pow_sub_C_of_root_adjoin_eq_top`：irreducible_X_pow_sub_C_o
f_root_adjoin_eq_top {a : K} {α : L} (ha : α ^ (finrank K L) = algebraMap K L a)
 (hα : K⟮α⟯ = ⊤) : Irreducible (X ^…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `isSplittingField_X_pow_sub_C_of_root_adjoin_eq_top`：isSplittingField_X_p
ow_sub_C_of_root_adjoin_eq_top {a : K} {α : L} (ha : α ^ (finrank K L) = algebra
Map K L a) (hα : K⟮α⟯ = ⊤) : IsSplitting…
· 使用引理 `isGalois_of_isSplittingField_X_pow_sub_C`：isGalois_of_isSplittingField_X
_pow_sub_C : IsGalois K L
· 使用引理 `isCyclic_of_isSplittingField_X_pow_sub_C`：isCyclic_of_isSplittingField_X
_pow_sub_C [NeZero n] : IsCyclic Gal(L/K)
· 使用定理 `List.tfae_of_cycle`：tfae_of_cycle {a b} {l : List Prop} (h_chain : List.
IsChain (· -> ·) (a :: b :: l)) (h_last : getLastD l b -> a) : TFAE (a :: b :: l
)

--- 原说明 ---
Suppose `L/K` is a finite extension of dimension `n`,
and `K` contains a primitive`n`-th root of unity.
Then `L/K` is cyclic iff
`L` is a splitting field of some irreducible polynomial of the form `Xⁿ - a : K[
X]` iff
`L = K[α]` for some `αⁿ ∈ K`.
-/
lemma isCyclic_tfae (K L) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (hK : (primitiveRoots (Module.finrank K L) K).Nonempty) :
    List.TFAE [
      IsGalois K L ∧ IsCyclic Gal(L/K),
      ∃ a : K, Irreducible (X ^ (finrank K L) - C a) ∧
        IsSplittingField K L (X ^ (finrank K L) - C a),
      ∃ (α : L), α ^ (finrank K L) ∈ Set.range (algebraMap K L) ∧ K⟮α⟯ = ⊤] := by
  have : NeZero (Module.finrank K L) := NeZero.of_pos finrank_pos
  tfae_have 1 → 3
  | ⟨inst₁, inst₂⟩ => exists_root_adjoin_eq_top_of_isCyclic K L hK
  tfae_have 3 → 2
  | ⟨α, ⟨a, ha⟩, hα⟩ => ⟨a, irreducible_X_pow_sub_C_of_root_adjoin_eq_top ha.symm hα,
      isSplittingField_X_pow_sub_C_of_root_adjoin_eq_top hK ha.symm hα⟩
  tfae_have 2 → 1
  | ⟨a, H, inst⟩ => ⟨isGalois_of_isSplittingField_X_pow_sub_C hK H L,
      isCyclic_of_isSplittingField_X_pow_sub_C hK H L⟩
  tfae_finish
