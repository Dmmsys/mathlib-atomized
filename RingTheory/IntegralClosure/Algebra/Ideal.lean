/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

/-!

# Integrality over ideals

## Main results
- `Polynomial.exists_monic_aeval_eq_zero_forall_mem_of_mem_map`:
  If `S` is an integral `R`-algebra, and `I` is an ideal of `R`,
  then any `x ∈ IS` is integral over `I`, i.e. it is a root
  of some monic polynomial in `R[X]` whose non-leading coefficients are in `I`.

## Note
We actually prove something stronger, namely that the `Xⁿ⁻ⁱ`-th coefficient lives in `Iⁿ`.
This is the definition that `x` is integral over `I` in https://stacks.math.columbia.edu/tag/00H2.

-/

public section

namespace Polynomial

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-
**Polynomial.coeff_mem_pow_of_mem_adjoin_C_mul_X** 是 Mathlib 中的一个引理，位于命名空间 `Poly
nomial`。
形式化陈述：coeff_mem_pow_of_mem_adjoin_C_mul_X {R : Type*} [CommRing R] {I : Ideal R}
 {P : R[X]} (hP : P in Algebra.adjoin R { C r * X | r in I }) (i : Nat) : P.coef
f i in I ^ i
参数：hP : P in Algebra.adjoin R { C r * X | r in I }；i : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.adjoin_induction`：adjoin_induction {p : (x : A) -> x in adjoin R
 s -> Prop} (mem : forall (x) (hx : x in s), p x (subset_adjoin hx)) (algebraMap
 : forall r, p…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coeff_C_mul`：coeff_C_mul (p : R[X]) : coeff (C a * p) n = a *
 coeff p n
· 使用定理 `Polynomial.coeff_X`：coeff_X : coeff (X : R[X]) n = if 1 = n then 1 else 
0
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `apply_ite`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [inst 
: Decidable P] (x y : α),   f (if P then x else y) = if P then f x else f y
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
· 使用定理 `Polynomial.coeff_C`：coeff_C : coeff (C a) n = ite (n = 0) a 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Ideal.one_eq_top`：one_eq_top : (1 : Ideal R) = ⊤
· 使用定理 `Polynomial.coeff_add`：coeff_add (p q : R[X]) (n : Nat) : coeff (p + q) n
 = coeff p n + coeff q n
· 使用定理 `AddMemClass.add_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Add M} {inst_1 : SetLike S M} [self : AddMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `AddSubmonoidClass.toAddMemClass`：∀ {S : Type u_3} {M : outParam (Type u_
4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass S
 M], AddMemClass S M
· 使用定理 `Polynomial.coeff_mul`：coeff_mul (p q : R[X]) (n : Nat) : coeff (p * q) n
 = ∑ x in antidiagonal n, coeff p x.1 * coeff q x.2
· 使用定理 `sum_mem`：∀ {B : Type u_3} {S : B} {M : Type u_4} [inst : AddCommMonoid M
] [inst_1 : SetLike B M] [AddSubmonoidClass B M]   {ι : Type u_5} {t : Finset…
· 使用定理 `Ideal.mul_mem_mul`：mul_mem_mul {r s} (hr : r in I) (hs : s in J) : r * s
 in I * J
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
-/
lemma coeff_mem_pow_of_mem_adjoin_C_mul_X {R : Type*} [CommRing R]
    {I : Ideal R} {P : R[X]} (hP : P ∈ Algebra.adjoin R { C r * X | r ∈ I }) (i : ℕ) :
    P.coeff i ∈ I ^ i := by
  induction hP using Algebra.adjoin_induction generalizing i with
  | mem x hx =>
    obtain ⟨r, hrI, rfl⟩ := hx
    simp +contextual [coeff_X, apply_ite, hrI, @eq_comm _ 1]
  | algebraMap r => simp +contextual [coeff_C, apply_ite]
  | add x y hx hy _ _ => aesop
  | mul x y _ _ hx hy =>
    rw [coeff_mul]
    refine sum_mem fun ⟨j₁, j₂⟩ hj ↦ ?_
    obtain rfl : j₁ + j₂ = i := by simpa using hj
    exact pow_add I j₁ j₂ ▸ Ideal.mul_mem_mul (hx _) (hy _)

attribute [local instance] Polynomial.algebra in
/-
**Polynomial.exists_monic_aeval_eq_zero_forall_mem_pow_of_isIntegral** 是 Mathlib
 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：exists_monic_aeval_eq_zero_forall_mem_pow_of_isIntegral {I : Ideal R} {x :
 S} (hx : IsIntegral (Algebra.adjoin R { C r * X | r in I }) (C x * X)) : exists
 p : R[X], p.Monic ∧ aeval x p = 0 ∧ forall i, p.coeff i in I ^ (p.natDegree - i
)
参数：hx : IsIntegral (Algebra.adjoin R { C r * X | r in I }) (C x * X)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
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
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `zero_tsub`：zero_tsub (a : α) : 0 - a = 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Ideal.one_eq_top`：one_eq_top : (1 : Ideal R) = ⊤
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Polynomial.natDegree_eq_of_le_of_coeff_ne_zero`：natDegree_eq_of_le_of_co
eff_ne_zero (pn : p.natDegree <= n) (p1 : p.coeff n != 0) : p.natDegree = n
· 使用引理 `Polynomial.natDegree_sum_le_of_forall_le`：natDegree_sum_le_of_forall_le 
{n : Nat} (f : ι -> S[X]) (h : forall i in s, natDegree (f i) <= n) : natDegree 
(∑ i in s, f i) <= n
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Polynomial.natDegree_C_mul_X_pow_le`：natDegree_C_mul_X_pow_le (a : R) (n
 : Nat) : natDegree (C a * X ^ n) <= n
· 使用定理 `Polynomial.finsetSum_coeff`：finsetSum_coeff {ι : Type*} (s : Finset ι) (
f : ι -> R[X]) (n : Nat) : coeff (∑ b in s, f b) n = ∑ b in s, coeff (f b) n
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Polynomial.coeff_C_mul`：coeff_C_mul (p : R[X]) : coeff (C a * p) n = a *
 coeff p n
· 使用定理 `Polynomial.coeff_X_pow`：coeff_X_pow (k n : Nat) : coeff (X ^ k : R[X]) n
 = if n = k then 1 else 0
· 使用引理 `mul_ite`：mul_ite (a b c : α) : (a * if P then b else c) = if P then a * 
b else a * c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
（共 67 条，此处仅展示前 30 条）
-/
lemma exists_monic_aeval_eq_zero_forall_mem_pow_of_isIntegral
    {I : Ideal R} {x : S}
    (hx : IsIntegral (Algebra.adjoin R { C r * X | r ∈ I }) (C x * X)) :
    ∃ p : R[X], p.Monic ∧ aeval x p = 0 ∧ ∀ i, p.coeff i ∈ I ^ (p.natDegree - i) := by
  cases subsingleton_or_nontrivial R
  · use 0; simp [Monic, Subsingleton.elim (α := R) 0 1]
  obtain ⟨p, hp, e⟩ := hx
  let q : R[X] := ∑ i ∈ Finset.range (p.natDegree + 1),
    C ((p.coeff i).1.coeff (p.natDegree - i)) * X ^ i
  have hq : q.natDegree = p.natDegree := by
    refine natDegree_eq_of_le_of_coeff_ne_zero (natDegree_sum_le_of_forall_le _ _ ?_) ?_
    · exact fun i hi ↦ (natDegree_C_mul_X_pow_le _ _).trans (by simpa [Nat.lt_succ_iff] using! hi)
    · simp [q, hp]
  refine ⟨q, ?_, ?_, ?_⟩
  · simpa [← hq] using! show q.coeff p.natDegree = 1 by simp [q, hp]
  · replace e := congr(($e).coeff p.natDegree)
    simp only [eval₂_eq_sum_range, finsetSum_coeff, coeff_zero] at e
    simp only [q, map_sum, map_mul, aeval_C, map_pow, aeval_X]
    refine (Finset.sum_congr rfl fun i hi ↦ ?_).trans e
    simp only [Finset.mem_range, Nat.lt_succ_iff] at hi
    rw [mul_pow, mul_left_comm, ← map_pow, coeff_C_mul, coeff_mul_X_pow', if_pos hi, mul_comm]
    simp [Subalgebra.algebraMap_def]
  · rw [hq]
    simp [q, apply_ite, coeff_mem_pow_of_mem_adjoin_C_mul_X (p.coeff _).2]
/-
**Polynomial.exists_monic_aeval_eq_zero_forall_mem_pow_of_mem_map** 是 Mathlib 中的
一个引理，位于命名空间 `Polynomial`。
形式化陈述：exists_monic_aeval_eq_zero_forall_mem_pow_of_mem_map [Algebra.IsIntegral R
 S] {I : Ideal R} {x : S} (hx : x in I.map (algebraMap R S)) : exists p : R[X], 
p.Monic ∧ aeval x p = 0 ∧ forall i, p.coeff i in I ^ (p.natDegree - i)
参数：hx : x in I.map (algebraMap R S)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Polynomial.exists_monic_aeval_eq_zero_forall_mem_pow_of_isIntegral`：exis
ts_monic_aeval_eq_zero_forall_mem_pow_of_isIntegral {I : Ideal R} {x : S} (hx : 
IsIntegral (Algebra.adjoin R { C r * X | r in I }) (C x …
· 使用定理 `Submodule.span_induction`：span_induction {p : (x : M) -> x in span R s -
> Prop} (mem : forall (x) (h : x in s), p x (subset_span h)) (zero : p 0 (Submod
ule.zero_mem _…
· 使用定理 `Algebra.subset_adjoin`：subset_adjoin : s subseteq adjoin R s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.map_mul`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p q
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   Polynomial.map f (p * q)
 = Polyn…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.map_C`：map_C : (C a).map f = C (f a)
· 使用定理 `Polynomial.map_X`：map_X : X.map f = X
· 使用定理 `isIntegral_algebraMap`：isIntegral_algebraMap {x : R} : IsIntegral R (alg
ebraMap R A x)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `IsIntegral.add`：∀ {R : Type u_1} {A : Type u_2} [inst : CommRing R] [ins
t_1 : CommRing A] [inst_2 : Algebra R A] {x y : A},   IsIntegral R x → IsIntegra
l R …
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `IsIntegral.mul`：∀ {R : Type u_1} {A : Type u_2} [inst : CommRing R] [ins
t_1 : CommRing A] [inst_2 : Algebra R A] {x y : A},   IsIntegral R x → IsIntegra
l R …
· 使用定理 `IsIntegral.tower_top`：IsIntegral.tower_top [Algebra A B] [IsScalarTower 
R A B] {x : B} (hx : IsIntegral R x) : IsIntegral A x
· 使用定理 `instIsScalarTowerPolynomial`：∀ (R : Type u_1) (S : Type u_2) (A : Type u
_3) [inst : CommSemiring R] [inst_1 : CommSemiring S] [inst_2 : Semiring A]   [i
nst_3 : Algebra R…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
（共 32 条，此处仅展示前 30 条）
-/
lemma exists_monic_aeval_eq_zero_forall_mem_pow_of_mem_map [Algebra.IsIntegral R S]
    {I : Ideal R} {x : S} (hx : x ∈ I.map (algebraMap R S)) :
    ∃ p : R[X], p.Monic ∧ aeval x p = 0 ∧ ∀ i, p.coeff i ∈ I ^ (p.natDegree - i) := by
  let A : Subalgebra R R[X] := Algebra.adjoin R { C r * X | r ∈ I }
  let := Polynomial.algebra R S
  refine exists_monic_aeval_eq_zero_forall_mem_pow_of_isIntegral ?_
  induction hx using Submodule.span_induction with
  | zero => simp [isIntegral_zero]
  | add x y _ _ hx hy => simpa [add_mul] using hx.add hy
  | mem x h =>
    obtain ⟨x, hx, rfl⟩ := h
    simpa using isIntegral_algebraMap (R := A) (A := S[X])
      (x := ⟨C x * X, Algebra.subset_adjoin ⟨x, hx, rfl⟩⟩)
  | smul a x _ hx =>
    simp only [smul_eq_mul, map_mul, mul_assoc]
    refine .mul ?_ hx
    exact ((Algebra.IsIntegral.isIntegral (R := R) a).map (IsScalarTower.toAlgHom R S _)).tower_top

@[stacks 00H5]
/-
**Polynomial.exists_monic_aeval_eq_zero_forall_mem_of_mem_map** 是 Mathlib 中的一个引理
，位于命名空间 `Polynomial`。
形式化陈述：exists_monic_aeval_eq_zero_forall_mem_of_mem_map [Algebra.IsIntegral R S] 
{I : Ideal R} {x : S} (hx : x in I.map (algebraMap R S)) : exists p : R[X], p.Mo
nic ∧ aeval x p = 0 ∧ forall i != p.natDegree, p.coeff i in I
参数：hx : x in I.map (algebraMap R S)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `Polynomial.exists_monic_aeval_eq_zero_forall_mem_pow_of_mem_map`：exists_
monic_aeval_eq_zero_forall_mem_pow_of_mem_map [Algebra.IsIntegral R S] {I : Idea
l R} {x : S} (hx : x in I.map (algebraMap R S)) : exi…
· 使用定理 `Ne.lt_or_gt`：Ne.lt_or_gt (h : a != b) : a < b ∨ b < a
· 使用定理 `Ideal.pow_le_self`：pow_le_self {n : Nat} (hn : n != 0) : I ^ n <= I
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coeff_eq_zero_of_natDegree_lt`：coeff_eq_zero_of_natDegree_lt 
{p : R[X]} {n : Nat} (h : p.natDegree < n) : p.coeff n = 0
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
-/
lemma exists_monic_aeval_eq_zero_forall_mem_of_mem_map [Algebra.IsIntegral R S]
    {I : Ideal R} {x : S} (hx : x ∈ I.map (algebraMap R S)) :
    ∃ p : R[X], p.Monic ∧ aeval x p = 0 ∧ ∀ i ≠ p.natDegree, p.coeff i ∈ I := by
  obtain ⟨p, hp, e, h⟩ := exists_monic_aeval_eq_zero_forall_mem_pow_of_mem_map hx
  refine ⟨p, hp, e, fun i hi ↦ ?_⟩
  obtain hi | hi := hi.lt_or_gt
  · exact Ideal.pow_le_self (by lia) (h _)
  · simp [coeff_eq_zero_of_natDegree_lt hi]

end Polynomial

