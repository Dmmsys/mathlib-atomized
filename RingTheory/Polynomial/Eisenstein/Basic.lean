/-
Copyright (c) 2022 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
module

public import Mathlib.RingTheory.Ideal.BigOperators
public import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
public import Mathlib.RingTheory.Polynomial.ScaleRoots

/-!
# Eisenstein polynomials

Given an ideal `𝓟` of a commutative semiring `R`, we say that a polynomial `f : R[X]` is
*Eisenstein at `𝓟`* if `f.leadingCoeff ∉ 𝓟`, `∀ n, n < f.natDegree → f.coeff n ∈ 𝓟` and
`f.coeff 0 ∉ 𝓟 ^ 2`. In this file we gather miscellaneous results about Eisenstein polynomials.

## Main definitions
* `Polynomial.IsEisensteinAt f 𝓟`: the property of being Eisenstein at `𝓟`.

## Main results
* `Polynomial.IsEisensteinAt.irreducible`: if a primitive `f` satisfies `f.IsEisensteinAt 𝓟`,
  where `𝓟.IsPrime`, then `f` is irreducible.

## Implementation details
We also define a notion `IsWeaklyEisensteinAt` requiring only that
`∀ n < f.natDegree → f.coeff n ∈ 𝓟`. This makes certain results slightly more general and it is
useful since it is sometimes better behaved (for example it is stable under `Polynomial.map`).

-/

public section


universe u v w z

variable {R : Type u}

open Ideal Algebra Finset

open Polynomial

namespace Polynomial

/-- Given an ideal `𝓟` of a commutative semiring `R`, we say that a polynomial `f : R[X]`
is *weakly Eisenstein at `𝓟`* if `∀ n, n < f.natDegree → f.coeff n ∈ 𝓟`. -/
@[mk_iff]
/-
**Polynomial.IsWeaklyEisensteinAt** 是 Mathlib 中的一个归纳类型，位于命名空间 `Polynomial`。
形式化陈述：{R : Type u} → [inst : CommSemiring R] → Polynomial R → Ideal R → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an ideal `𝓟` of a commutative semiring `R`, we say that a polynomial `f : 
R[X]`
is *weakly Eisenstein at `𝓟`* if `∀ n, n < f.natDegree → f.coeff n ∈ 𝓟`.
-/
structure IsWeaklyEisensteinAt [CommSemiring R] (f : R[X]) (𝓟 : Ideal R) : Prop where
  mem : ∀ {n}, n < f.natDegree → f.coeff n ∈ 𝓟

/-- Given an ideal `𝓟` of a commutative semiring `R`, we say that a polynomial `f : R[X]`
is *Eisenstein at `𝓟`* if `f.leadingCoeff ∉ 𝓟`, `∀ n, n < f.natDegree → f.coeff n ∈ 𝓟` and
`f.coeff 0 ∉ 𝓟 ^ 2`. -/
@[mk_iff]
/-
**Polynomial.IsEisensteinAt** 是 Mathlib 中的一个归纳类型，位于命名空间 `Polynomial`。
形式化陈述：{R : Type u} → [inst : CommSemiring R] → Polynomial R → Ideal R → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an ideal `𝓟` of a commutative semiring `R`, we say that a polynomial `f : 
R[X]`
is *Eisenstein at `𝓟`* if `f.leadingCoeff ∉ 𝓟`, `∀ n, n < f.natDegree → f.coeff 
n ∈ 𝓟` and
`f.coeff 0 ∉ 𝓟 ^ 2`.
-/
structure IsEisensteinAt [CommSemiring R] (f : R[X]) (𝓟 : Ideal R) : Prop where
  leading : f.leadingCoeff ∉ 𝓟
  mem : ∀ {n}, n < f.natDegree → f.coeff n ∈ 𝓟
  notMem : f.coeff 0 ∉ 𝓟 ^ 2

namespace IsWeaklyEisensteinAt

section CommSemiring

variable [CommSemiring R] {𝓟 : Ideal R} {f f' : R[X]}

/-
**Polynomial.IsWeaklyEisensteinAt.map** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.IsWe
aklyEisensteinAt`。
形式化陈述：map (hf : f.IsWeaklyEisensteinAt 𝓟) {A : Type v} [CommSemiring A] (φ : R -
>+* A) : (f.map φ).IsWeaklyEisensteinAt (𝓟.map φ)
参数：hf : f.IsWeaklyEisensteinAt 𝓟；φ : R ->+* A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.isWeaklyEisensteinAt_iff`：∀ {R : Type u} [inst : CommSemiring
 R] (f : Polynomial R) (𝓟 : Ideal R),   f.IsWeaklyEisensteinAt 𝓟 ↔ ∀ {n : ℕ}, n 
< f.natDegree → f.coeff n…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coeff_map`：coeff_map (n : Nat) : coeff (p.map f) n = f (coeff
 p n)
· 使用定理 `Ideal.mem_map_of_mem`：mem_map_of_mem (f : F) {I : Ideal R} {x : R} (h : 
x in I) : f x in map f I
· 使用定理 `Polynomial.IsWeaklyEisensteinAt.mem`：∀ {R : Type u} [inst : CommSemiring
 R] {f : Polynomial R} {𝓟 : Ideal R},   f.IsWeaklyEisensteinAt 𝓟 → ∀ {n : ℕ}, n 
< f.natDegree → f.coeff n…
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用引理 `Polynomial.natDegree_map_le`：natDegree_map_le : natDegree (p.map f) <= n
atDegree p
-/
theorem map (hf : f.IsWeaklyEisensteinAt 𝓟) {A : Type v} [CommSemiring A] (φ : R →+* A) :
    (f.map φ).IsWeaklyEisensteinAt (𝓟.map φ) := by
  refine (isWeaklyEisensteinAt_iff _ _).2 fun hn => ?_
  rw [coeff_map]
  exact mem_map_of_mem _ (hf.mem (lt_of_lt_of_le hn natDegree_map_le))
/-
**Polynomial.IsWeaklyEisensteinAt.mul** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.IsWe
aklyEisensteinAt`。
形式化陈述：mul (hf : f.IsWeaklyEisensteinAt 𝓟) (hf' : f'.IsWeaklyEisensteinAt 𝓟) : (f
 * f').IsWeaklyEisensteinAt 𝓟
参数：hf : f.IsWeaklyEisensteinAt 𝓟；hf' : f'.IsWeaklyEisensteinAt 𝓟。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.isWeaklyEisensteinAt_iff`：∀ {R : Type u} [inst : CommSemiring
 R] (f : Polynomial R) (𝓟 : Ideal R),   f.IsWeaklyEisensteinAt 𝓟 ↔ ∀ {n : ℕ}, n 
< f.natDegree → f.coeff n…
· 使用定理 `Polynomial.coeff_mul`：coeff_mul (p q : R[X]) (n : Nat) : coeff (p * q) n
 = ∑ x in antidiagonal n, coeff p x.1 * coeff q x.2
· 使用定理 `Ideal.sum_mem`：sum_mem (I : Ideal α) {ι : Type*} {t : Finset ι} {f : ι -
> α} : (forall c in t, f c in I) -> (∑ i in t, f i) in I
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `Ideal.mul_mem_right`：mul_mem_right {α} {a : α} (b : α) [Semiring α] (I :
 Ideal α) [I.IsTwoSided] (h : a in I) : a * b in I
· 使用定理 `Ideal.instIsTwoSided`：∀ {α : Type u} [inst : CommSemiring α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Polynomial.natDegree_mul_le`：natDegree_mul_le {p q : R[X]} : natDegree (
p * q) <= natDegree p + natDegree q
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
（共 51 条，此处仅展示前 30 条）
-/
theorem mul (hf : f.IsWeaklyEisensteinAt 𝓟) (hf' : f'.IsWeaklyEisensteinAt 𝓟) :
    (f * f').IsWeaklyEisensteinAt 𝓟 := by
  rw [isWeaklyEisensteinAt_iff] at hf hf' ⊢
  intro n hn
  rw [coeff_mul]
  refine sum_mem _ fun x hx ↦ ?_
  rcases lt_or_ge x.1 f.natDegree with hx1 | hx1
  · exact mul_mem_right _ _ (hf hx1)
  replace hx1 : x.2 < f'.natDegree := by
    by_contra!
    rw [HasAntidiagonal.mem_antidiagonal] at hx
    replace hn := hn.trans_le natDegree_mul_le
    linarith
  exact mul_mem_left _ _ (hf' hx1)

end CommSemiring

section CommRing

variable [CommRing R] {𝓟 : Ideal R} {f : R[X]}
variable {S : Type v} [CommRing S] [Algebra R S]

section Principal

variable {p : R}

/-
**Polynomial.IsWeaklyEisensteinAt.exists_mem_adjoin_mul_eq_pow_natDegree** 是 Mat
hlib 中的一个定理，位于命名空间 `Polynomial.IsWeaklyEisensteinAt`。
形式化陈述：exists_mem_adjoin_mul_eq_pow_natDegree {x : S} (hx : aeval x f = 0) (hmo :
 f.Monic) (hf : f.IsWeaklyEisensteinAt (Submodule.span R {p})) : exists y in adj
oin R ({x} : Set S), (algebraMap R S) p * y = x ^ (f.map (algebraMap R S)).natDe
gree
参数：hx : aeval x f = 0；hmo : f.Monic；hf : f.IsWeaklyEisensteinAt (Submodule.span 
R {p})。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_neg_of_add_eq_zero_left`：∀ {G : Type u_1} [inst : SubtractionMonoid G
] {a b : G}, a + b = 0 → a = -b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Polynomial.Monic.coeff_natDegree`：∀ {R : Type u} [inst : Semiring R] {p 
: Polynomial R}, p.Monic → p.coeff p.natDegree = 1
· 使用定理 `Polynomial.Monic.map`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   p.Monic → (Polynomial.ma
p f p).Mon…
· 使用定理 `Finset.sum_range`：∀ {M : Type u_2} [inst : AddCommMonoid M] {n : ℕ} (f :
 ℕ → M), ∑ i ∈ Finset.range n, f i = ∑ i, f ↑i
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `Finset.notMem_range_self`：notMem_range_self : n ∉ range n
· 使用定理 `Finset.range_add_one`：range_add_one : range (n + 1) = insert n (range n)
· 使用定理 `Polynomial.eval_eq_sum_range`：eval_eq_sum_range {p : R[X]} (x : R) : p.e
val x = ∑ i in Finset.range (p.natDegree + 1), p.coeff i * x ^ i
· 使用定理 `Polynomial.eval₂_eq_eval_map`：eval₂_eq_eval_map {x : S} : p.eval₂ f x = 
(p.map f).eval x
· 使用定理 `Polynomial.aeval_def`：aeval_def (p : R[X]) : aeval x p = eval₂ (algebraM
ap R A) x p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ideal.mem_span_singleton`：mem_span_singleton {x y : α} : x in span ({y} 
: Set α) ↔ y ∣ x
· 使用定理 `Polynomial.IsWeaklyEisensteinAt.mem`：∀ {R : Type u} [inst : CommSemiring
 R] {f : Polynomial R} {𝓟 : Ideal R},   f.IsWeaklyEisensteinAt 𝓟 → ∀ {n : ℕ}, n 
< f.natDegree → f.coeff n…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.coeff_map`：coeff_map (n : Nat) : coeff (p.map f) n = f (coeff
 p n)
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用引理 `Polynomial.natDegree_map_le`：natDegree_map_le : natDegree (p.map f) <= n
atDegree p
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用定理 `neg_eq_neg_one_mul`：neg_eq_neg_one_mul (a : α) : -a = -1 * a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Subalgebra.mul_mem`：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] 
[inst_1 : Semiring A] [inst_2 : Algebra R A] (S : Subalgebra R A)   {x y : A}, x
 ∈ S → y…
（共 40 条，此处仅展示前 30 条）
-/
theorem exists_mem_adjoin_mul_eq_pow_natDegree {x : S} (hx : aeval x f = 0) (hmo : f.Monic)
    (hf : f.IsWeaklyEisensteinAt (Submodule.span R {p})) : ∃ y ∈ adjoin R ({x} : Set S),
    (algebraMap R S) p * y = x ^ (f.map (algebraMap R S)).natDegree := by
  rw [aeval_def, Polynomial.eval₂_eq_eval_map, eval_eq_sum_range, range_add_one,
    sum_insert notMem_range_self, sum_range, (hmo.map (algebraMap R S)).coeff_natDegree,
    one_mul] at hx
  replace hx := eq_neg_of_add_eq_zero_left hx
  have : ∀ n < f.natDegree, p ∣ f.coeff n := by
    intro n hn
    exact mem_span_singleton.1 (by simpa using hf.mem hn)
  choose! φ hφ using this
  conv_rhs at hx =>
    congr
    congr
    · skip
    ext i
    rw [coeff_map, hφ i.1 (lt_of_lt_of_le i.2 natDegree_map_le), map_mul, mul_assoc]
  rw [hx, ← mul_sum, neg_eq_neg_one_mul, ← mul_assoc (-1 : S), mul_comm (-1 : S), mul_assoc]
  refine
    ⟨-1 * ∑ i : Fin (f.map (algebraMap R S)).natDegree, (algebraMap R S) (φ i.1) * x ^ i.1, ?_, rfl⟩
  exact
    Subalgebra.mul_mem _ (Subalgebra.neg_mem _ (Subalgebra.one_mem _))
      (Subalgebra.sum_mem _ fun i _ =>
        Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _)
          (Subalgebra.pow_mem _ (subset_adjoin (Set.mem_singleton x)) _))
/-
**Polynomial.IsWeaklyEisensteinAt.exists_mem_adjoin_mul_eq_pow_natDegree_le** 是 
Mathlib 中的一个定理，位于命名空间 `Polynomial.IsWeaklyEisensteinAt`。
形式化陈述：exists_mem_adjoin_mul_eq_pow_natDegree_le {x : S} (hx : aeval x f = 0) (hm
o : f.Monic) (hf : f.IsWeaklyEisensteinAt (Submodule.span R {p})) : forall i, (f
.map (algebraMap R S)).natDegree <= i -> exists y in adjoin R ({x} : Set S), (al
gebraMap R S) p * y = x ^ i
参数：hx : aeval x f = 0；hmo : f.Monic；hf : f.IsWeaklyEisensteinAt (Submodule.span 
R {p})。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ExistsAddOfLE.exists_add_of_le`：∀ {α : Type u} {inst : Add α} {inst_1 : 
LE α} [self : ExistsAddOfLE α] {a b : α}, a ≤ b → ∃ c, b = a + c
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `Polynomial.IsWeaklyEisensteinAt.exists_mem_adjoin_mul_eq_pow_natDegree`：
exists_mem_adjoin_mul_eq_pow_natDegree {x : S} (hx : aeval x f = 0) (hmo : f.Mon
ic) (hf : f.IsWeaklyEisensteinAt (Submodule.span R {p})) : e…
· 使用定理 `Subalgebra.mul_mem`：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] 
[inst_1 : Semiring A] [inst_2 : Algebra R A] (S : Subalgebra R A)   {x y : A}, x
 ∈ S → y…
· 使用定理 `Subalgebra.pow_mem`：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] 
[inst_1 : Semiring A] [inst_2 : Algebra R A] (S : Subalgebra R A)   {x : A}, x ∈
 S → ∀ (…
· 使用定理 `Algebra.subset_adjoin`：subset_adjoin : s subseteq adjoin R s
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
-/
theorem exists_mem_adjoin_mul_eq_pow_natDegree_le {x : S} (hx : aeval x f = 0) (hmo : f.Monic)
    (hf : f.IsWeaklyEisensteinAt (Submodule.span R {p})) :
    ∀ i, (f.map (algebraMap R S)).natDegree ≤ i →
        ∃ y ∈ adjoin R ({x} : Set S), (algebraMap R S) p * y = x ^ i := by
  intro i hi
  obtain ⟨k, hk⟩ := exists_add_of_le hi
  rw [hk, pow_add]
  obtain ⟨y, hy, H⟩ := exists_mem_adjoin_mul_eq_pow_natDegree hx hmo hf
  refine ⟨y * x ^ k, ?_, ?_⟩
  · exact Subalgebra.mul_mem _ hy (Subalgebra.pow_mem _ (subset_adjoin (Set.mem_singleton x)) _)
  · rw [← mul_assoc _ y, H]

end Principal

/-
**Polynomial.IsWeaklyEisensteinAt.pow_natDegree_le_of_root_of_monic_mem** 是 Math
lib 中的一个定理，位于命名空间 `Polynomial.IsWeaklyEisensteinAt`。
形式化陈述：pow_natDegree_le_of_root_of_monic_mem (hf : f.IsWeaklyEisensteinAt 𝓟) {x :
 R} (hroot : IsRoot f x) (hmo : f.Monic) : forall i, f.natDegree <= i -> x ^ i i
n 𝓟
参数：hf : f.IsWeaklyEisensteinAt 𝓟；hroot : IsRoot f x；hmo : f.Monic。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ExistsAddOfLE.exists_add_of_le`：∀ {α : Type u} {inst : Add α} {inst_1 : 
LE α} [self : ExistsAddOfLE α] {a b : α}, a ≤ b → ∃ c, b = a + c
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `eq_neg_of_add_eq_zero_left`：∀ {G : Type u_1} [inst : SubtractionMonoid G
] {a b : G}, a + b = 0 → a = -b
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Polynomial.Monic.coeff_natDegree`：∀ {R : Type u} [inst : Semiring R] {p 
: Polynomial R}, p.Monic → p.coeff p.natDegree = 1
· 使用定理 `Finset.sum_range`：∀ {M : Type u_2} [inst : AddCommMonoid M] {n : ℕ} (f :
 ℕ → M), ∑ i ∈ Finset.range n, f i = ∑ i, f ↑i
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `Finset.notMem_range_self`：notMem_range_self : n ∉ range n
· 使用定理 `Finset.range_add_one`：range_add_one : range (n + 1) = insert n (range n)
· 使用定理 `Polynomial.eval_eq_sum_range`：eval_eq_sum_range {p : R[X]} (x : R) : p.e
val x = ∑ i in Finset.range (p.natDegree + 1), p.coeff i * x ^ i
· 使用定理 `Polynomial.IsRoot.def`：∀ {R : Type u} {a : R} [inst : Semiring R] {p : P
olynomial R}, p.IsRoot a ↔ Polynomial.eval a p = 0
· 使用定理 `neg_mem_iff`：∀ {S : Type u_3} {G : Type u_4} [inst : InvolutiveNeg G] {x
 : SetLike S G} [NegMemClass S G] {H : S} {x_1 : G},   -x_1 ∈ H ↔ x_1 ∈ H
· 使用定理 `NonUnitalSubringClass.toNegMemClass`：∀ {S : Type u_1} {R : Type u} {inst
 : NonUnitalNonAssocRing R} {inst_1 : SetLike S R}   [self : NonUnitalSubringCla
ss S R], NegMemClass S R
· 使用定理 `instNonUnitalSubringClassIdeal`：∀ {R : Type u_1} [inst : Ring R], NonUni
talSubringClass (Ideal R) R
· 使用定理 `Submodule.sum_mem`：∀ {R : Type u} {M : Type v} {ι : Type w} [inst : Semi
ring R] [inst_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodu
le R M)…
· 使用定理 `Ideal.mul_mem_right`：mul_mem_right {α} {a : α} (b : α) [Semiring α] (I :
 Ideal α) [I.IsTwoSided] (h : a in I) : a * b in I
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Polynomial.IsWeaklyEisensteinAt.mem`：∀ {R : Type u} [inst : CommSemiring
 R] {f : Polynomial R} {𝓟 : Ideal R},   f.IsWeaklyEisensteinAt 𝓟 → ∀ {n : ℕ}, n 
< f.natDegree → f.coeff n…
· 使用定理 `Fin.is_lt`：∀ {n : ℕ} (a : Fin n), ↑a < n
-/
theorem pow_natDegree_le_of_root_of_monic_mem (hf : f.IsWeaklyEisensteinAt 𝓟)
    {x : R} (hroot : IsRoot f x) (hmo : f.Monic) :
    ∀ i, f.natDegree ≤ i → x ^ i ∈ 𝓟 := by
  intro i hi
  obtain ⟨k, hk⟩ := exists_add_of_le hi
  rw [hk, pow_add]
  suffices x ^ f.natDegree ∈ 𝓟 by exact mul_mem_right (x ^ k) 𝓟 this
  rw [IsRoot.def, eval_eq_sum_range, Finset.range_add_one,
    Finset.sum_insert Finset.notMem_range_self, Finset.sum_range, hmo.coeff_natDegree, one_mul] at
    *
  rw [eq_neg_of_add_eq_zero_left hroot, neg_mem_iff]
  exact Submodule.sum_mem _ fun i _ => mul_mem_right _ _ (hf.mem (Fin.is_lt i))
/-
**Polynomial.IsWeaklyEisensteinAt.pow_natDegree_le_of_aeval_zero_of_monic_mem_ma
p** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.IsWeaklyEisensteinAt`。
形式化陈述：pow_natDegree_le_of_aeval_zero_of_monic_mem_map (hf : f.IsWeaklyEisenstein
At 𝓟) {x : S} (hx : aeval x f = 0) (hmo : f.Monic) : forall i, (f.map (algebraMa
p R S)).natDegree <= i -> x ^ i in 𝓟.map (algebraMap R S)
参数：hf : f.IsWeaklyEisensteinAt 𝓟；hx : aeval x f = 0；hmo : f.Monic。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.IsWeaklyEisensteinAt.pow_natDegree_le_of_root_of_monic_mem`：p
ow_natDegree_le_of_root_of_monic_mem (hf : f.IsWeaklyEisensteinAt 𝓟) {x : R} (hr
oot : IsRoot f x) (hmo : f.Monic) : forall i, f.natDegree <…
· 使用定理 `Polynomial.IsWeaklyEisensteinAt.map`：map (hf : f.IsWeaklyEisensteinAt 𝓟)
 {A : Type v} [CommSemiring A] (φ : R ->+* A) : (f.map φ).IsWeaklyEisensteinAt (
𝓟.map φ)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.IsRoot.def`：∀ {R : Type u} {a : R} [inst : Semiring R] {p : P
olynomial R}, p.IsRoot a ↔ Polynomial.eval a p = 0
· 使用定理 `Polynomial.eval₂_eq_eval_map`：eval₂_eq_eval_map {x : S} : p.eval₂ f x = 
(p.map f).eval x
· 使用定理 `Polynomial.aeval_def`：aeval_def (p : R[X]) : aeval x p = eval₂ (algebraM
ap R A) x p
· 使用定理 `Polynomial.Monic.map`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   p.Monic → (Polynomial.ma
p f p).Mon…
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `ExistsAddOfLE.exists_add_of_le`：∀ {α : Type u} {inst : Add α} {inst_1 : 
LE α} [self : ExistsAddOfLE α] {a b : α}, a ≤ b → ∃ c, b = a + c
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `Ideal.mul_mem_right`：mul_mem_right {α} {a : α} (b : α) [Semiring α] (I :
 Ideal α) [I.IsTwoSided] (h : a in I) : a * b in I
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
-/
theorem pow_natDegree_le_of_aeval_zero_of_monic_mem_map (hf : f.IsWeaklyEisensteinAt 𝓟)
    {x : S} (hx : aeval x f = 0) (hmo : f.Monic) :
    ∀ i, (f.map (algebraMap R S)).natDegree ≤ i → x ^ i ∈ 𝓟.map (algebraMap R S) := by
  suffices x ^ (f.map (algebraMap R S)).natDegree ∈ 𝓟.map (algebraMap R S) by
    intro i hi
    obtain ⟨k, hk⟩ := exists_add_of_le hi
    rw [hk, pow_add]
    exact mul_mem_right _ _ this
  rw [aeval_def, eval₂_eq_eval_map, ← IsRoot.def] at hx
  exact pow_natDegree_le_of_root_of_monic_mem (hf.map _) hx (hmo.map _) _ rfl.le

end CommRing

end IsWeaklyEisensteinAt

section ScaleRoots

variable {A : Type*} [CommRing R] [CommRing A]

/-
**Polynomial.scaleRoots.isWeaklyEisensteinAt** 是 Mathlib 中的一个定理，位于命名空间 `Polynomi
al.scaleRoots`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] (p : Polynomial R) {x : R} {P : Ideal R
},   x ∈ P → (p.scaleRoots x).IsWeaklyEisensteinAt P
参数：p : Polynomial R；p.scaleRoots x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coeff_scaleRoots`：coeff_scaleRoots (p : R[X]) (s : R) (i : Na
t) : (scaleRoots p s).coeff i = coeff p i * s ^ (p.natDegree - i)
· 使用定理 `Ideal.mul_mem_left`：mul_mem_left : b in I -> a * b in I
· 使用定理 `Ideal.pow_mem_of_mem`：pow_mem_of_mem (ha : a in I) (n : Nat) (hn : 0 < n
) : a ^ n in I
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `tsub_pos_iff_lt`：tsub_pos_iff_lt : 0 < a - b ↔ b < a
· 使用定理 `Polynomial.natDegree_scaleRoots`：natDegree_scaleRoots (p : R[X]) (s : R)
 : natDegree (scaleRoots p s) = natDegree p
-/
theorem scaleRoots.isWeaklyEisensteinAt (p : R[X]) {x : R} {P : Ideal R} (hP : x ∈ P) :
    (scaleRoots p x).IsWeaklyEisensteinAt P := by
  refine ⟨fun i => ?_⟩
  rw [coeff_scaleRoots]
  rw [natDegree_scaleRoots, ← tsub_pos_iff_lt] at i
  exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem P hP _ i)
/-
**Polynomial.dvd_pow_natDegree_of_eval** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem dvd_pow_natDegree_of_eval₂_eq_zero {f : R →+* A} (hf : Function.Injective f) {p : R[X]}
    (hp : p.Monic) (x y : R) (z : A) (h : p.eval₂ f z = 0) (hz : f x * z = f y) :
    x ∣ y ^ p.natDegree := by
  rw [← natDegree_scaleRoots p x, ← Ideal.mem_span_singleton]
  refine
    (scaleRoots.isWeaklyEisensteinAt _
          (Ideal.mem_span_singleton.mpr <| dvd_refl x)).pow_natDegree_le_of_root_of_monic_mem
      ?_ ((monic_scaleRoots_iff x).mpr hp) _ le_rfl
  rw [injective_iff_map_eq_zero'] at hf
  have : eval₂ f _ (p.scaleRoots x) = 0 := scaleRoots_eval₂_eq_zero f h
  rwa [hz, Polynomial.eval₂_at_apply, hf] at this
/-
**Polynomial.dvd_pow_natDegree_of_aeval_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polyn
omial`。
形式化陈述：dvd_pow_natDegree_of_aeval_eq_zero [IsDomain R] [Algebra R A] [Nontrivial 
A] [Module.IsTorsionFree R A] {p : R[X]} (hp : p.Monic) (x y : R) (z : A) (h : p
.aeval z = 0) (hz : z * algebraMap R A x = algebraMap R A y) : x ∣ y ^ p.natDegr
ee
参数：hp : p.Monic；x y : R；z : A；h : p.aeval z = 0；hz : z * algebraMap R A x = alge
braMap R A y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.dvd_pow_natDegree_of_eval₂_eq_zero`：dvd_pow_natDegree_of_eval
₂_eq_zero {f : R ->+* A} (hf : Function.Injective f) {p : R[X]} (hp : p.Monic) (
x y : R) (z : A) (h : p.eval₂ f z =…
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `Module.IsTorsionFree.to_faithfulSMul`：∀ {R : Type u_1} {A : Type u_2} [i
nst : CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] [IsCancelMulZero R]  
 [Nontrivial A] [Module.Is…
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem dvd_pow_natDegree_of_aeval_eq_zero [IsDomain R] [Algebra R A] [Nontrivial A]
    [Module.IsTorsionFree R A] {p : R[X]} (hp : p.Monic) (x y : R) (z : A) (h : p.aeval z = 0)
    (hz : z * algebraMap R A x = algebraMap R A y) : x ∣ y ^ p.natDegree :=
  dvd_pow_natDegree_of_eval₂_eq_zero (FaithfulSMul.algebraMap_injective R A) hp x y z h
    ((mul_comm _ _).trans hz)

end ScaleRoots

namespace IsEisensteinAt

section CommSemiring

variable [CommSemiring R] {𝓟 : Ideal R} {f : R[X]}

/-
**Polynomial.IsEisensteinAt._root_.Polynomial.Monic.leadingCoeff_notMem** 是 Math
lib 中的一个定理，位于命名空间 `Polynomial.IsEisensteinAt`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Polynomial.Monic.leadingCoeff_notMem (hf : f.Monic) (h : 𝓟 ≠ ⊤) :
    f.leadingCoeff ∉ 𝓟 := hf.leadingCoeff.symm ▸ (Ideal.ne_top_iff_one _).1 h
/-
**Polynomial.IsEisensteinAt._root_.Polynomial.Monic.isEisensteinAt_of_mem_of_not
Mem** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.IsEisensteinAt`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Polynomial.Monic.isEisensteinAt_of_mem_of_notMem (hf : f.Monic) (h : 𝓟 ≠ ⊤)
    (hmem : ∀ {n}, n < f.natDegree → f.coeff n ∈ 𝓟) (hnotMem : f.coeff 0 ∉ 𝓟 ^ 2) :
    f.IsEisensteinAt 𝓟 :=
  { leading := Polynomial.Monic.leadingCoeff_notMem hf h
    mem := fun hn => hmem hn
    notMem := hnotMem }
/-
**Polynomial.IsEisensteinAt.isWeaklyEisensteinAt** 是 Mathlib 中的一个定理，位于命名空间 `Poly
nomial.IsEisensteinAt`。
形式化陈述：isWeaklyEisensteinAt (hf : f.IsEisensteinAt 𝓟) : IsWeaklyEisensteinAt f 𝓟
参数：hf : f.IsEisensteinAt 𝓟。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.IsEisensteinAt.mem`：∀ {R : Type u} [inst : CommSemiring R] {f
 : Polynomial R} {𝓟 : Ideal R},   f.IsEisensteinAt 𝓟 → ∀ {n : ℕ}, n < f.natDegre
e → f.coeff n ∈ 𝓟
-/
theorem isWeaklyEisensteinAt (hf : f.IsEisensteinAt 𝓟) : IsWeaklyEisensteinAt f 𝓟 :=
  ⟨fun h => hf.mem h⟩
/-
**Polynomial.IsEisensteinAt.coeff_mem** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.IsEi
sensteinAt`。
形式化陈述：coeff_mem (hf : f.IsEisensteinAt 𝓟) {n : Nat} (hn : n != f.natDegree) : f.
coeff n in 𝓟
参数：hf : f.IsEisensteinAt 𝓟；hn : n != f.natDegree。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `ne_iff_lt_or_gt`：ne_iff_lt_or_gt : a != b ↔ a < b ∨ b < a
· 使用定理 `Polynomial.IsEisensteinAt.mem`：∀ {R : Type u} [inst : CommSemiring R] {f
 : Polynomial R} {𝓟 : Ideal R},   f.IsEisensteinAt 𝓟 → ∀ {n : ℕ}, n < f.natDegre
e → f.coeff n ∈ 𝓟
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coeff_eq_zero_of_natDegree_lt`：coeff_eq_zero_of_natDegree_lt 
{p : R[X]} {n : Nat} (h : p.natDegree < n) : p.coeff n = 0
· 使用定理 `Ideal.zero_mem`：∀ {α : Type u} [inst : Semiring α] (I : Ideal α), 0 ∈ I
-/
theorem coeff_mem (hf : f.IsEisensteinAt 𝓟) {n : ℕ} (hn : n ≠ f.natDegree) : f.coeff n ∈ 𝓟 := by
  rcases ne_iff_lt_or_gt.1 hn with h₁ | h₂
  · exact hf.mem h₁
  · rw [coeff_eq_zero_of_natDegree_lt h₂]
    exact Ideal.zero_mem _

end CommSemiring

section IsDomain

variable [CommRing R] [IsDomain R] {𝓟 : Ideal R} {f : R[X]}

/-- If a primitive `f` satisfies `f.IsEisensteinAt 𝓟`, where `𝓟.IsPrime`,
then `f` is irreducible. -/
/-
**Polynomial.IsEisensteinAt.irreducible** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Is
EisensteinAt`。
形式化陈述：irreducible (hf : f.IsEisensteinAt 𝓟) (hprime : 𝓟.IsPrime) (hu : f.IsPrimi
tive) (hfd0 : 0 < f.natDegree) : Irreducible f
参数：hf : f.IsEisensteinAt 𝓟；hprime : 𝓟.IsPrime；hu : f.IsPrimitive；hfd0 : 0 < f.na
tDegree。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.irreducible_of_eisenstein_criterion`：irreducible_of_eisenstei
n_criterion {f : R[X]} {P : Ideal R} (hP : P.IsPrime) (hfl : f.leadingCoeff ∉ P)
 (hfP : forall n : Nat, ↑n < degree …
· 使用定理 `Polynomial.IsEisensteinAt.leading`：∀ {R : Type u} [inst : CommSemiring R
] {f : Polynomial R} {𝓟 : Ideal R}, f.IsEisensteinAt 𝓟 → f.leadingCoeff ∉ 𝓟
· 使用定理 `Polynomial.IsEisensteinAt.mem`：∀ {R : Type u} [inst : CommSemiring R] {f
 : Polynomial R} {𝓟 : Ideal R},   f.IsEisensteinAt 𝓟 → ∀ {n : ℕ}, n < f.natDegre
e → f.coeff n ∈ 𝓟
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.coe_lt_degree`：coe_lt_degree {p : R[X]} {n : Nat} : (n : With
Bot Nat) < degree p ↔ n < natDegree p
· 使用定理 `Polynomial.natDegree_pos_iff_degree_pos`：natDegree_pos_iff_degree_pos : 
0 < natDegree p ↔ 0 < degree p
· 使用定理 `Polynomial.IsEisensteinAt.notMem`：∀ {R : Type u} [inst : CommSemiring R]
 {f : Polynomial R} {𝓟 : Ideal R}, f.IsEisensteinAt 𝓟 → f.coeff 0 ∉ 𝓟 ^ 2

--- 原说明 ---
If a primitive `f` satisfies `f.IsEisensteinAt 𝓟`, where `𝓟.IsPrime`,
then `f` is irreducible.
-/
theorem irreducible (hf : f.IsEisensteinAt 𝓟) (hprime : 𝓟.IsPrime) (hu : f.IsPrimitive)
    (hfd0 : 0 < f.natDegree) : Irreducible f :=
  irreducible_of_eisenstein_criterion hprime hf.leading (fun _ hn => hf.mem (coe_lt_degree.1 hn))
    (natDegree_pos_iff_degree_pos.1 hfd0) hf.notMem hu

end IsDomain

end IsEisensteinAt

end Polynomial

