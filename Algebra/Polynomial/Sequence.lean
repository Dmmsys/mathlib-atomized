/-
Copyright (c) 2025 Julian Berman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Hill, Julian Berman, Austin Letson, Matej Penciak
-/
module

public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.RingTheory.Polynomial.Basic

/-!

# Polynomial sequences

We define polynomial sequences – sequences of polynomials `a₀, a₁, ...` such that the polynomial
`aᵢ` has degree `i`.

## Main definitions

* `Polynomial.Sequence R`: the type of polynomial sequences with coefficients in `R`

## Main statements

* `Polynomial.Sequence.basis`: a sequence is a basis for `R[X]`

## TODO

Generalize linear independence to:
  * `IsCancelAdd` semirings
  * just require coefficients are regular
  * arbitrary sets of polynomials which are pairwise different degree.
-/

@[expose] public section

open Module Submodule
open scoped Function

variable (R : Type*)

namespace Polynomial

/-- A sequence of polynomials such that the polynomial at index `i` has degree `i`. -/
/-
**Polynomial.Sequence** 是 Mathlib 中的一个归纳类型，位于命名空间 `Polynomial`。
形式化陈述：(R : Type u_1) → [Semiring R] → Type u_1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A sequence of polynomials such that the polynomial at index `i` has degree `i`.
-/
structure Sequence [Semiring R] where
  /-- The `i`-th element in the sequence. Use `S i` instead, defined via `CoeFun`. -/
  protected elems' : ℕ → R[X]
  /-- The `i`-th element in the sequence has degree `i`. Use `S.degree_eq` instead. -/
  protected degree_eq' (i : ℕ) : (elems' i).degree = i

attribute [coe] Sequence.elems'

namespace Sequence

variable {R}

/-- Make `S i` mean `S.elems' i`. -/
/-
**Polynomial.Sequence.coeFun** 是 Mathlib 中的一个实例，位于命名空间 `Polynomial.Sequence`。
形式化陈述：coeFun [Semiring R] : CoeFun (Sequence R) (fun _ => Nat -> R[X])
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Make `S i` mean `S.elems' i`.
-/
instance coeFun [Semiring R] : CoeFun (Sequence R) (fun _ ↦ ℕ → R[X]) := ⟨Sequence.elems'⟩

section Semiring

variable [Semiring R] (S : Sequence R)

/-- `S i` has degree `i`. -/
@[simp]
/-
**Polynomial.Sequence.degree_eq** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial.Sequence`。
形式化陈述：degree_eq (i : Nat) : (S i).degree = i
参数：i : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.Sequence.degree_eq'`：∀ {R : Type u_1} [inst : Semiring R] (se
lf : Polynomial.Sequence R) (i : ℕ), (↑self i).degree = ↑i

--- 原说明 ---
`S i` has degree `i`.
-/
lemma degree_eq (i : ℕ) : (S i).degree = i := S.degree_eq' i

/-- `S i` has `natDegree` `i`. -/
@[simp]
/-
**Polynomial.Sequence.natDegree_eq** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial.Sequenc
e`。
形式化陈述：natDegree_eq (i : Nat) : (S i).natDegree = i
参数：i : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.natDegree_eq_of_degree_eq_some`：natDegree_eq_of_degree_eq_som
e {p : R[X]} {n : Nat} (h : degree p = n) : natDegree p = n
· 使用引理 `Polynomial.Sequence.degree_eq`：degree_eq (i : Nat) : (S i).degree = i

--- 原说明 ---
`S i` has `natDegree` `i`.
-/
lemma natDegree_eq (i : ℕ) : (S i).natDegree = i := natDegree_eq_of_degree_eq_some <| S.degree_eq i

/-- No polynomial in the sequence is zero. -/
@[simp]
/-
**Polynomial.Sequence.ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial.Sequence`。
形式化陈述：ne_zero (i : Nat) : S i != 0
参数：i : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.degree_ne_bot`：degree_ne_bot : degree p != ⊥ ↔ p != 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Polynomial.Sequence.degree_eq`：degree_eq (i : Nat) : (S i).degree = i
· 使用定理 `not_false_eq_true`：(¬False) = True

--- 原说明 ---
No polynomial in the sequence is zero.
-/
lemma ne_zero (i : ℕ) : S i ≠ 0 := degree_ne_bot.mp <| by simp [S.degree_eq i]

/-- `S i` has strictly monotone degree. -/
/-
**Polynomial.Sequence.degree_strictMono** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial.Se
quence`。
形式化陈述：degree_strictMono : StrictMono degree ∘ S
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Polynomial.Sequence.degree_eq`：degree_eq (i : Nat) : (S i).degree = i
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α

--- 原说明 ---
`S i` has strictly monotone degree.
-/
lemma degree_strictMono : StrictMono <| degree ∘ S := fun _ _ ↦ by simp

/-- `S i` has strictly monotone natural degree. -/
/-
**Polynomial.Sequence.natDegree_strictMono** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial
.Sequence`。
形式化陈述：natDegree_strictMono : StrictMono natDegree ∘ S
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Polynomial.Sequence.natDegree_eq`：natDegree_eq (i : Nat) : (S i).natDegr
ee = i

--- 原说明 ---
`S i` has strictly monotone natural degree.
-/
lemma natDegree_strictMono : StrictMono <| natDegree ∘ S := fun _ _ ↦ by simp

end Semiring

section Ring

variable [Ring R] (S : Sequence R)

/-- The first `m` polynomials of a polynomial sequence span all polynomials of degree `< m` if their
    leading coefficients are units. -/
/-
**Polynomial.Sequence.span_degreeLT** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial.Sequen
ce`。
形式化陈述：span_degreeLT {m : Nat} (hCoeff : forall i < m, IsUnit (S i).leadingCoeff)
 : span R (S '' Set.Iio m) = degreeLT R m
参数：hCoeff : forall i < m, IsUnit (S i).leadingCoeff。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.span_eq_of_le`：span_eq_of_le (h₁ : s subseteq p) (h₂ : p <= sp
an R s) : span R s = p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_image`：mem_image (f : α -> β) (s : Set α) (y : β) : y in f '' s 
↔ exists x in s, f x = y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `Polynomial.mem_degreeLT`：mem_degreeLT {n : Nat} {f : R[X]} : f in degree
LT R n ↔ degree f < n
· 使用引理 `Polynomial.Sequence.degree_eq`：degree_eq (i : Nat) : (S i).degree = i
· 使用定理 `Nat.cast_lt`：cast_lt : (m : α) < n ↔ m < n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Set.mem_Iio`：∀ {α : Type u_1} [inst : Preorder α] {b x : α}, x ∈ Set.Iio
 b ↔ x < b
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Subsingleton.eq_zero`：∀ {α : Type u} [inst : Zero α] [Subsingleton α] (a
 : α), a = 0
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `Nat.strong_induction_on`：∀ {p : ℕ → Prop} (n : ℕ), (∀ (n : ℕ), (∀ m < n,
 p m) → p n) → p n
· 使用定理 `Polynomial.degree_eq_natDegree`：degree_eq_natDegree (hp : p != 0) : degr
ee p = (natDegree p : WithBot Nat)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `isUnit_iff_exists`：isUnit_iff_exists [Monoid M] {x : M} : IsUnit x ↔ exi
sts b, x * b = 1 ∧ b * x = 1
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用定理 `sub_eq_iff_eq_add`：∀ {G : Type u_3} [inst : AddGroup G] {a b c : G}, a -
 b = c ↔ a = c + b
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Submodule.sub_mem_iff_left`：sub_mem_iff_left (hy : y in p) : x - y in p 
↔ x in p
· 使用定理 `Polynomial.leadingCoeff_smul_of_smul_regular`：leadingCoeff_smul_of_smul_
regular {S : Type*} [SMulZeroClass S R] {k : S} (p : R[X]) (h : IsSMulRegular R 
k) : (k • p).leadingCoeff = k • p.…
· 使用定理 `IsSMulRegular.of_mul_eq_one`：of_mul_eq_one (h : a * b = 1) : IsSMulRegul
ar M b
· 使用定理 `IsRegular.right`：∀ {R : Type u_1} [inst : Mul R] {c : R}, IsRegular c → 
IsRightRegular c
（共 49 条，此处仅展示前 30 条）

--- 原说明 ---
The first `m` polynomials of a polynomial sequence span all polynomials of degre
e `< m` if their
    leading coefficients are units.
-/
lemma span_degreeLT {m : ℕ} (hCoeff : ∀ i < m, IsUnit (S i).leadingCoeff) :
    span R (S '' Set.Iio m) = degreeLT R m := by
  apply span_eq_of_le
  · intro P hP
    obtain ⟨i, hi, rfl⟩ := (Set.mem_image _ _ _).mp hP
    rw [SetLike.mem_coe, Polynomial.mem_degreeLT, S.degree_eq i, Nat.cast_lt]
    exact Set.mem_Iio.mp hi
  intro P hP
  -- we proceed via strong induction on the degree `n`, after getting the 0 polynomial done
  nontriviality R using Subsingleton.eq_zero P
  generalize hp : P.natDegree = n
  induction n using Nat.strong_induction_on generalizing P with
  | h n ih =>
    by_cases! p_ne_zero : P = 0
    · simp [p_ne_zero]
    have hn : n < m := by
      rw [Polynomial.mem_degreeLT] at hP
      have := Polynomial.degree_eq_natDegree p_ne_zero
      aesop
    -- let u be the inverse of `S n`'s leading coefficient
    obtain ⟨u, leftinv, rightinv⟩ := isUnit_iff_exists.mp <| hCoeff n hn
    -- We'll show `P` is the difference of two terms in the span:
    --   a polynomial whose leading term matches `P`'s and lower degree terms match `S n`'s
    let head := P.leadingCoeff • u • S n -- a polynomial whose leading term matches P's and whose
    --   and then an error correcting polynomial which gets us to `P`'s actual lower degree terms
    let tail := P - head
    -- `head` is in the span because it's a multiple of `S n`
    have head_mem_span : head ∈ span R (S '' Set.Iio m) := by
      have in_span : S n ∈ span R (S '' Set.Iio m) := subset_span ⟨n, by simp [hn], rfl⟩
      have smul_span := smul_mem (span R (S '' Set.Iio m)) (P.leadingCoeff • u) in_span
      rwa [smul_assoc] at smul_span
    -- to show the tail is in the span we really need consider only when we needed to "correct" for
    -- some lower degree terms in `P`
    by_cases tail_eq_zero : tail = 0
    · simp [head_mem_span, sub_eq_iff_eq_add.mp tail_eq_zero]
    -- we'll do so via the induction hypothesis,
    -- and once we show we can use it, `P` is a difference of two members of the span
    apply sub_mem_iff_left _ head_mem_span |>.mp
    -- so let's prove the tail has degree less than `n`
    suffices tail.degree < n by
      refine ih tail.natDegree ((natDegree_lt_iff_degree_lt tail_eq_zero).mpr this) ?_ rfl
      grw [(Nat.cast_lt (α := WithBot ℕ)).mpr hn] at this
      rwa [Polynomial.mem_degreeLT]
    -- first we want that `P` and `head` have the same degree
    have isRightRegular_smul_leadingCoeff : IsRightRegular (u • S n).leadingCoeff := by
      simpa [leadingCoeff_smul_of_smul_regular, IsSMulRegular.of_mul_eq_one leftinv, rightinv]
        using isRegular_one.right
    have u_degree_same := degree_smul_of_isRightRegular_leadingCoeff
      (left_ne_zero_of_mul_eq_one rightinv) (hCoeff n hn).isRegular.right
    have head_degree_eq := degree_smul_of_isRightRegular_leadingCoeff
      (leadingCoeff_ne_zero.mpr p_ne_zero) isRightRegular_smul_leadingCoeff
    rw [u_degree_same, S.degree_eq n, ← hp, eq_comm,
      ← degree_eq_natDegree p_ne_zero, hp] at head_degree_eq
    -- and that this degree is also their `natDegree`
    have head_degree_eq_natDegree : head.degree = head.natDegree := degree_eq_natDegree <| by
      grind [degree_eq_bot]
    -- and that they have matching leading coefficients
    have hPhead : P.leadingCoeff = head.leadingCoeff := by
      rw [degree_eq_natDegree p_ne_zero, head_degree_eq_natDegree] at head_degree_eq
      nth_rw 2 [← coeff_natDegree]
      rw_mod_cast [← head_degree_eq, hp]
      dsimp [head]
      nth_rw 2 [← S.natDegree_eq n]
      rw [coeff_smul, coeff_smul, coeff_natDegree, smul_eq_mul, smul_eq_mul, rightinv, mul_one]
    -- which we can now combine to show that `P - head` must have strictly lower degree,
    -- as its leading term has been cancelled, completing our proof.
    have tail_degree_lt := P.degree_sub_lt_left head_degree_eq p_ne_zero hPhead
    rwa [degree_eq_natDegree p_ne_zero, hp] at tail_degree_lt

/-- The first `m + 1` polynomials of a polynomial sequence span all polynomials of degree `≤ m` if
    their leading coefficients are units. -/
/-
**Polynomial.Sequence.span_degreeLE** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial.Sequen
ce`。
形式化陈述：span_degreeLE {m : Nat} (hCoeff : forall i <= m, IsUnit (S i).leadingCoeff
) : span R (S '' Set.Iic m) = degreeLE R m
参数：hCoeff : forall i <= m, IsUnit (S i).leadingCoeff。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Set.Iio_succ_eq_Iic`：Iio_succ_eq_Iic (b : α) : Iio (succ b) = Iic b
· 使用引理 `Polynomial.Sequence.span_degreeLT`：span_degreeLT {m : Nat} (hCoeff : for
all i < m, IsUnit (S i).leadingCoeff) : span R (S '' Set.Iio m) = degreeLT R m
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Order.lt_succ_iff`：lt_succ_iff : a < succ b ↔ a <= b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Order.succ_eq_add_one`：succ_eq_add_one (x : α) : succ x = x + 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The first `m + 1` polynomials of a polynomial sequence span all polynomials of d
egree `≤ m` if
    their leading coefficients are units.
-/
lemma span_degreeLE {m : ℕ} (hCoeff : ∀ i ≤ m, IsUnit (S i).leadingCoeff) :
    span R (S '' Set.Iic m) = degreeLE R m := by
  rw [← Set.Iio_succ_eq_Iic, span_degreeLT _ (fun i hi => hCoeff i (Order.lt_succ_iff.mp hi))]
  simp [← Polynomial.degreeLT_succ_eq_degreeLE]

/-- A polynomial sequence spans `R[X]` if all of its elements' leading coefficients are units. -/
/-
**Polynomial.Sequence.span** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Sequence`。
形式化陈述：∀ {R : Type u_1} [inst : Ring R] (S : Polynomial.Sequence R),   (∀ (i : ℕ)
, IsUnit (↑S i).leadingCoeff) → Submodule.span R (Set.range ↑S) = ⊤
参数：S : Polynomial.Sequence R；∀ (i : ℕ), IsUnit (↑S i).leadingCoeff；Set.range ↑S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.eq_top_iff'`：eq_top_iff' {p : Submodule R M} : p = ⊤ ↔ forall 
x, x in p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用引理 `Polynomial.Sequence.span_degreeLT`：span_degreeLT {m : Nat} (hCoeff : for
all i < m, IsUnit (S i).leadingCoeff) : span R (S '' Set.Iio m) = degreeLT R m
· 使用定理 `Polynomial.mem_degreeLT`：mem_degreeLT {n : Nat} {f : R[X]} : f in degree
LT R n ↔ degree f < n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.natDegree_lt_iff_degree_lt`：natDegree_lt_iff_degree_lt (hp : 
p != 0) : p.natDegree < n ↔ p.degree < ↑n
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
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Submodule.span_mono`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R]
 [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {s t : Set M}, s ⊆ t 
→ Submodu…
· 使用定理 `Set.preimage_range`：preimage_range (f : α -> β) : f ⁻¹' range f = univ

--- 原说明 ---
A polynomial sequence spans `R[X]` if all of its elements' leading coefficients 
are units.
-/
protected lemma span (hCoeff : ∀ i, IsUnit (S i).leadingCoeff) : span R (Set.range S) = ⊤ := by
  rw [eq_top_iff']
  intro P
  by_cases! p_ne_zero : P = 0
  · simp [p_ne_zero]
  suffices P ∈ span R (S '' Set.Iio (P.natDegree + 1)) from (span_mono (by simp)) this
  rw [span_degreeLT _ (by grind), Polynomial.mem_degreeLT, ← natDegree_lt_iff_degree_lt p_ne_zero]
  simp

section IsDomain

variable [IsDomain R]

/-- Polynomials in a polynomial sequence are linearly independent. -/
/-
**Polynomial.Sequence.linearIndependent** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial.Se
quence`。
形式化陈述：linearIndependent : LinearIndependent R S
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `linearIndependent_iff'`：linearIndependent_iff'ₛ : LinearIndependent R v 
↔ forall s : Finset ι, forall f g : ι -> R, ∑ i in s, f i • v i = ∑ i in s, g i 
• v i -> for…
· 使用定理 `Finset.le_sup`：le_sup {b : β} (hb : b in s) : f b <= s.sup f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `smul_eq_zero_iff_left`：smul_eq_zero_iff_left (hm : m != 0) : r • m = 0 ↔
 r = 0
· 使用定理 `Polynomial.instIsTorsionFree`：∀ {R : Type u} [inst : Semiring R] {S : Ty
pe u_1} [inst_1 : Semiring S] [inst_2 : _root_.Module S R]   [Module.IsTorsionFr
ee S R], Module.Is…
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `NoZeroDivisors.toNoZeroSMulDivisors`：∀ {R : Type u_1} [inst : Zero R] [i
nst_1 : Mul R] [NoZeroDivisors R], NoZeroSMulDivisors R R
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用引理 `Polynomial.Sequence.ne_zero`：ne_zero (i : Nat) : S i != 0
· 使用定理 `Polynomial.degree_eq_bot`：degree_eq_bot : degree p = ⊥ ↔ p = 0
· 使用定理 `eq_bot_mono`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α
] {a b : α}, b ≤ a → a = ⊥ → b = ⊥
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `smul_ne_zero_iff`：smul_ne_zero_iff : r • m != 0 ↔ r != 0 ∧ m != 0
· 使用定理 `IsRegular.right`：∀ {R : Type u_1} [inst : Mul R] {c : R}, IsRegular c → 
IsRightRegular c
· 使用定理 `IsRegular.of_ne_zero`：IsRegular.of_ne_zero (a0 : a != 0) : IsRegular a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.degree_smul_of_isRightRegular_leadingCoeff`：degree_smul_of_is
RightRegular_leadingCoeff (ha : a != 0) (hp : IsRightRegular p.leadingCoeff) : (
a • p).degree = p.degree
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用引理 `Polynomial.Sequence.degree_eq`：degree_eq (i : Nat) : (S i).degree = i
· 使用定理 `exists_eq'`：∀ {α : Sort u_1} {a' : α}, ∃ a, a' = a
· 使用定理 `Polynomial.degree_ne_bot`：degree_ne_bot : degree p != ⊥ ↔ p != 0
· 使用定理 `Polynomial.degree_sum_eq_of_disjoint`：degree_sum_eq_of_disjoint (f : S -
> R[X]) (s : Finset S) (h : Set.Pairwise { i | i in s ∧ f i != 0 } (Ne on degree
 ∘ f)) : degree (s.sum f) …
· 使用定理 `Eq.trans_ne`：∀ {α : Sort u_1} {a b c : α}, a = b → b ≠ c → a ≠ c
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
（共 32 条，此处仅展示前 30 条）

--- 原说明 ---
Polynomials in a polynomial sequence are linearly independent.
-/
lemma linearIndependent :
    LinearIndependent R S := linearIndependent_iff'.mpr <| fun s g eqzero i hi ↦ by
  by_cases hsupzero : s.sup (fun i ↦ (g i • S i).degree) = ⊥
  · have le_sup := Finset.le_sup hi (f := fun i ↦ (g i • S i).degree)
    exact (smul_eq_zero_iff_left (S.ne_zero i)).mp <| degree_eq_bot.mp (eq_bot_mono le_sup hsupzero)
  have hpairwise : {i | i ∈ s ∧ g i • S i ≠ 0}.Pairwise (Ne on fun i ↦ (g i • S i).degree) := by
    intro x ⟨_, hx⟩ y ⟨_, hy⟩ xney
    have zgx : g x ≠ 0 := (smul_ne_zero_iff.mp hx).1
    have zgy : g y ≠ 0 := (smul_ne_zero_iff.mp hy).1
    have rx : IsRightRegular (S x).leadingCoeff := IsRegular.of_ne_zero (by simp) |>.right
    have ry : IsRightRegular (S y).leadingCoeff := IsRegular.of_ne_zero (by simp) |>.right
    simp [degree_smul_of_isRightRegular_leadingCoeff, rx, ry, zgx, zgy, xney]
  obtain ⟨n, hn⟩ : ∃ n, (s.sup fun i ↦ (g i • S i).degree) = n := exists_eq'
  refine degree_ne_bot.mp ?_ eqzero |>.elim
  have hsum := degree_sum_eq_of_disjoint _ s hpairwise
  exact hsum.trans hn |>.trans_ne <| (ne_of_ne_of_eq (hsupzero ·.symm) hn).symm

variable (hCoeff : ∀ i, IsUnit (S i).leadingCoeff)

/-- Every polynomial sequence is a basis of `R[X]`. -/
/-
**Polynomial.Sequence.basis** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial.Sequence`。
形式化陈述：basis : Basis Nat R R[X]
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Polynomial.Sequence.linearIndependent`：linearIndependent : LinearIndepen
dent R S

--- 原说明 ---
Every polynomial sequence is a basis of `R[X]`.
-/
noncomputable def basis : Basis ℕ R R[X] :=
  Basis.mk S.linearIndependent <| eq_top_iff.mp <| S.span hCoeff

/-- The `i`-th basis vector is the `i`-th polynomial in the sequence. -/
@[simp]
/-
**Polynomial.Sequence.basis_eq_self** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial.Sequen
ce`。
形式化陈述：basis_eq_self (i : Nat) : S.basis hCoeff i = S i
参数：i : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.mk_apply`：mk_apply (i : ι) : Basis.mk hli hsp i = v i
· 使用引理 `Polynomial.Sequence.linearIndependent`：linearIndependent : LinearIndepen
dent R S

--- 原说明 ---
The `i`-th basis vector is the `i`-th polynomial in the sequence.
-/
lemma basis_eq_self (i : ℕ) : S.basis hCoeff i = S i := Basis.mk_apply _ _ _

/-- Basis elements have strictly monotone degree. -/
/-
**Polynomial.Sequence.basis_degree_strictMono** 是 Mathlib 中的一个引理，位于命名空间 `Polynom
ial.Sequence`。
形式化陈述：basis_degree_strictMono : StrictMono degree ∘ (S.basis hCoeff)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Polynomial.Sequence.basis_eq_self`：basis_eq_self (i : Nat) : S.basis hCo
eff i = S i
· 使用引理 `Polynomial.Sequence.degree_eq`：degree_eq (i : Nat) : (S i).degree = i
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α

--- 原说明 ---
Basis elements have strictly monotone degree.
-/
lemma basis_degree_strictMono : StrictMono <| degree ∘ (S.basis hCoeff) := fun _ _ ↦ by simp

/-- Basis elements have strictly monotone natural degree. -/
/-
**Polynomial.Sequence.basis_natDegree_strictMono** 是 Mathlib 中的一个引理，位于命名空间 `Poly
nomial.Sequence`。
形式化陈述：basis_natDegree_strictMono : StrictMono natDegree ∘ (S.basis hCoeff)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Polynomial.Sequence.basis_eq_self`：basis_eq_self (i : Nat) : S.basis hCo
eff i = S i
· 使用引理 `Polynomial.Sequence.natDegree_eq`：natDegree_eq (i : Nat) : (S i).natDegr
ee = i

--- 原说明 ---
Basis elements have strictly monotone natural degree.
-/
lemma basis_natDegree_strictMono : StrictMono <| natDegree ∘ (S.basis hCoeff) := fun _ _ ↦ by simp

end IsDomain

end Ring

end Sequence

end Polynomial

