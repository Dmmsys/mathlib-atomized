/-
Copyright (c) 2024 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.FieldTheory.KummerExtension

/-!
# More results on primitive roots of unity

(We put these in a separate file because of the `KummerExtension` import.)

Assume that `μ` is a primitive `n`th root of unity in an integral domain `R`. Then
$$ \prod_{k=1}^{n-1} (1 - \mu^k) = n \,; $$
see `IsPrimitiveRoot.prod_one_sub_pow_eq_order` and its variant
`IsPrimitiveRoot.prod_pow_sub_one_eq_order` in terms of `∏ (μ^k - 1)`.

We use this to deduce that `n` is divisible by `(μ - 1)^k` in `ℤ[μ] ⊆ R` when `k < n`.
-/

public section

variable {R : Type*} [CommRing R] [IsDomain R]

namespace IsPrimitiveRoot

open Finset Polynomial

/-- If `μ` is a primitive `n`th root of unity in `R`, then `∏(1≤k<n) (1-μ^k) = n`.
(Stated with `n+1` in place of `n` to avoid the condition `n ≠ 0`.) -/
/-
**IsPrimitiveRoot.prod_one_sub_pow_eq_order** 是 Mathlib 中的一个引理，位于命名空间 `IsPrimiti
veRoot`。
形式化陈述：prod_one_sub_pow_eq_order {n : Nat} {μ : R} (hμ : IsPrimitiveRoot μ (n + 1
)) : ∏ k in range n, (1 - μ ^ (k + 1)) = n + 1
参数：hμ : IsPrimitiveRoot μ (n + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `X_pow_sub_C_eq_prod`：X_pow_sub_C_eq_prod {R : Type*} [CommRing R] [IsDom
ain R] {n : Nat} {ζ : R} (hζ : IsPrimitiveRoot ζ n) {α a : R} (hn : 0 < n) (e : 
α ^ n = a…
· 使用定理 `Nat.zero_lt_succ`：∀ (n : ℕ), 0 < n.succ
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `mul_right_cancel₀`：mul_right_cancel₀ (hb : b != 0) (h : a * b = c * b) :
 a = c
· 使用定理 `Polynomial.instIsRightCancelMulZeroOfIsCancelAdd`：∀ {R : Type u} [inst :
 Semiring R] [IsCancelAdd R] [IsRightCancelMulZero R], IsRightCancelMulZero (Pol
ynomial R)
· 使用定理 `AddCancelMonoid.toIsCancelAdd`：∀ (M : Type u) [inst : AddCancelMonoid M]
, IsCancelAdd M
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `Polynomial.X_sub_C_ne_zero`：X_sub_C_ne_zero (r : R) : X - C r != 0
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Finset.prod_range_succ'`：∀ {M : Type u_4} [inst : CommMonoid M] (f : ℕ →
 M) (n : ℕ),   ∏ k ∈ Finset.range (n + 1), f k = (∏ k ∈ Finset.range n, f (k + 1
)) * f 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `mul_geom_sum`：mul_geom_sum (x : R) (n : Nat) : ((x - 1) * ∑ i in range n
, x ^ i) = x ^ n - 1
· 使用定理 `Polynomial.C_1`：C_1 : C (1 : R) = 1
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Polynomial.eval_prod`：eval_prod {ι : Type*} (s : Finset ι) (p : ι -> R[X
]) (x : R) : eval x (∏ j in s, p j) = ∏ j in s, eval x (p j)
· 使用定理 `Polynomial.eval_sub`：eval_sub (p q : R[X]) (x : R) : (p - q).eval x = p.
eval x - q.eval x
· 使用定理 `Polynomial.eval_X`：eval_X : X.eval x = x
· 使用定理 `Polynomial.eval_pow`：eval_pow (n : Nat) : (p ^ n).eval x = p.eval x ^ n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
（共 39 条，此处仅展示前 30 条）

--- 原说明 ---
If `μ` is a primitive `n`th root of unity in `R`, then `∏(1≤k<n) (1-μ^k) = n`.
(Stated with `n+1` in place of `n` to avoid the condition `n ≠ 0`.)
-/
lemma prod_one_sub_pow_eq_order {n : ℕ} {μ : R} (hμ : IsPrimitiveRoot μ (n + 1)) :
    ∏ k ∈ range n, (1 - μ ^ (k + 1)) = n + 1 := by
  have := X_pow_sub_C_eq_prod hμ n.zero_lt_succ (one_pow (n + 1))
  rw [C_1, ← mul_geom_sum, prod_range_succ', pow_zero, mul_one, mul_comm, eq_comm] at this
  replace this := mul_right_cancel₀ (Polynomial.X_sub_C_ne_zero 1) this
  apply_fun Polynomial.eval 1 at this
  simpa only [mul_one, map_pow, eval_prod, eval_sub, eval_X, eval_pow, eval_C, eval_geom_sum,
    one_pow, sum_const, card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one] using this

/-- If `μ` is a primitive `n`th root of unity in `R`, then `(-1)^(n-1) * ∏(1≤k<n) (μ^k-1) = n`.
(Stated with `n+1` in place of `n` to avoid the condition `n ≠ 0`.) -/
/-
**IsPrimitiveRoot.prod_pow_sub_one_eq_order** 是 Mathlib 中的一个引理，位于命名空间 `IsPrimiti
veRoot`。
形式化陈述：prod_pow_sub_one_eq_order {n : Nat} {μ : R} (hμ : IsPrimitiveRoot μ (n + 1
)) : (-1) ^ n * ∏ k in range n, (μ ^ (k + 1) - 1) = n + 1
参数：hμ : IsPrimitiveRoot μ (n + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_const`：prod_const (b : M) : ∏ _x in s, b = b ^ #s
· 使用定理 `Finset.card_range`：card_range (n : Nat) : #(range n) = n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `neg_one_mul`：neg_one_mul (a : α) : -1 * a = -a
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `IsPrimitiveRoot.prod_one_sub_pow_eq_order`：prod_one_sub_pow_eq_order {n 
: Nat} {μ : R} (hμ : IsPrimitiveRoot μ (n + 1)) : ∏ k in range n, (1 - μ ^ (k + 
1)) = n + 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `μ` is a primitive `n`th root of unity in `R`, then `(-1)^(n-1) * ∏(1≤k<n) (μ
^k-1) = n`.
(Stated with `n+1` in place of `n` to avoid the condition `n ≠ 0`.)
-/
lemma prod_pow_sub_one_eq_order {n : ℕ} {μ : R} (hμ : IsPrimitiveRoot μ (n + 1)) :
    (-1) ^ n * ∏ k ∈ range n, (μ ^ (k + 1) - 1) = n + 1 := by
  have : (-1 : R) ^ n = ∏ k ∈ range n, -1 := by rw [prod_const, card_range]
  simp only [this, ← prod_mul_distrib, neg_one_mul, neg_sub, ← prod_one_sub_pow_eq_order hμ]

open Algebra in
/-- If `μ` is a primitive `n`th root of unity in `R` and `k < n`, then `n` is divisible
by `(μ-1)^k` in `ℤ[μ] ⊆ R`. -/
/-
**IsPrimitiveRoot.self_sub_one_pow_dvd_order** 是 Mathlib 中的一个引理，位于命名空间 `IsPrimit
iveRoot`。
形式化陈述：self_sub_one_pow_dvd_order {k n : Nat} (hn : k < n) {μ : R} (hμ : IsPrimit
iveRoot μ n) : exists z in Int[μ], n = z * (μ - 1) ^ k
参数：hn : k < n；hμ : IsPrimitiveRoot μ n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.exists_eq_add_of_le'`：∀ {m n : ℕ}, m ≤ n → ∃ k, n = k + m
· 使用定理 `Nat.le_of_lt_succ`：∀ {m n : ℕ}, m < n.succ → m ≤ n
· 使用定理 `Subalgebra.sum_mem`：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] 
[inst_1 : Semiring A] [inst_2 : Algebra R A] (S : Subalgebra R A)   {ι : Type w}
 {t : Fi…
· 使用定理 `Subalgebra.pow_mem`：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] 
[inst_1 : Semiring A] [inst_2 : Algebra R A] (S : Subalgebra R A)   {x : A}, x ∈
 S → ∀ (…
· 使用定理 `Algebra.self_mem_adjoin_singleton`：self_mem_adjoin_singleton (x : A) : x
 in R[x]
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `geom_sum_mul`：geom_sum_mul (x : R) (n : Nat) : (∑ i in range n, x ^ i) *
 (x - 1) = x ^ n - 1
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `Subalgebra.mul_mem`：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] 
[inst_1 : Semiring A] [inst_2 : Algebra R A] (S : Subalgebra R A)   {x y : A}, x
 ∈ S → y…
· 使用定理 `Subalgebra.neg_mem`：∀ {R : Type u} {A : Type v} [inst : CommRing R] [ins
t_1 : Ring A] [inst_2 : Algebra R A] (S : Subalgebra R A) {x : A},   x ∈ S → -x 
∈ S
· 使用定理 `Subalgebra.one_mem`：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] 
[inst_1 : Semiring A] [inst_2 : Algebra R A] (S : Subalgebra R A),   1 ∈ S
· 使用定理 `Subalgebra.prod_mem`：∀ {R : Type u} {A : Type v} [inst : CommSemiring R]
 [inst_1 : CommSemiring A] [inst_2 : Algebra R A]   (S : Subalgebra R A) {ι : Ty
pe w} {t …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subalgebra.sub_mem`：∀ {R : Type u} {A : Type v} [inst : CommRing R] [ins
t_1 : Ring A] [inst_2 : Algebra R A] (S : Subalgebra R A) {x y : A},   x ∈ S → y
 ∈ S → x…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用引理 `IsPrimitiveRoot.prod_pow_sub_one_eq_order`：prod_pow_sub_one_eq_order {n 
: Nat} {μ : R} (hμ : IsPrimitiveRoot μ (n + 1)) : (-1) ^ n * ∏ k in range n, (μ 
^ (k + 1) - 1) = n + 1
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Finset.card_range`：card_range (n : Nat) : #(range n) = n
· 使用定理 `Finset.prod_range_mul_prod_Ico`：prod_range_mul_prod_Ico (f : Nat -> M) {
m n : Nat} (h : m <= n) : ((∏ k in range m, f k) * ∏ k in Ico m n, f k) = ∏ k in
 range n, f k
· 使用定理 `Nat.le_add_left`：∀ (n m : ℕ), n ≤ m + n
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Finset.prod_mul_pow_card`：prod_mul_pow_card {b : M} : (∏ a in s, f a) * 
b ^ #s = ∏ a in s, f a * b
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
If `μ` is a primitive `n`th root of unity in `R` and `k < n`, then `n` is divisi
ble
by `(μ-1)^k` in `ℤ[μ] ⊆ R`.
-/
lemma self_sub_one_pow_dvd_order {k n : ℕ} (hn : k < n) {μ : R} (hμ : IsPrimitiveRoot μ n) :
    ∃ z ∈ ℤ[μ], n = z * (μ - 1) ^ k := by
  let n' + 1 := n
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' (Nat.le_of_lt_succ hn)
  have hdvd k : ∃ z ∈ ℤ[μ], μ ^ k - 1 = z * (μ - 1) := by
    refine ⟨(Finset.range k).sum (μ ^ ·), ?_, (geom_sum_mul μ k).symm⟩
    exact Subalgebra.sum_mem _ fun m _ ↦ Subalgebra.pow_mem _ (self_mem_adjoin_singleton _ μ) _
  let Z k := Classical.choose <| hdvd k
  have Zdef k : Z k ∈ ℤ[μ] ∧ μ ^ k - 1 = Z k * (μ - 1) :=
    Classical.choose_spec <| hdvd k
  refine ⟨(-1) ^ (m + k) * (∏ j ∈ range k, Z (j + 1)) * ∏ j ∈ Ico k (m + k), (μ ^ (j + 1) - 1),
    ?_, ?_⟩
  · apply Subalgebra.mul_mem
    · apply Subalgebra.mul_mem
      · exact Subalgebra.pow_mem _ (Subalgebra.neg_mem _ <| Subalgebra.one_mem _) _
      · exact Subalgebra.prod_mem _ fun _ _ ↦ (Zdef _).1
    · refine Subalgebra.prod_mem _ fun _ _ ↦ ?_
      apply Subalgebra.sub_mem
      · exact Subalgebra.pow_mem _ (self_mem_adjoin_singleton ℤ μ) _
      · exact Subalgebra.one_mem _
  · push_cast
    have := Nat.cast_add (R := R) m k ▸ hμ.prod_pow_sub_one_eq_order
    rw [← this, mul_assoc, mul_assoc]
    congr 1
    conv => enter [2, 2, 2]; rw [← card_range k]
    rw [← prod_range_mul_prod_Ico _ (Nat.le_add_left k m), mul_comm _ (_ ^ #_), ← mul_assoc,
      prod_mul_pow_card]
    conv => enter [2, 1, 2, j]; rw [← (Zdef _).2]

end IsPrimitiveRoot

