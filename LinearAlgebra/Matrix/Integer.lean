/-
Copyright (c) 2025 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Algebra.GCDMonoid.Nat
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Rat.Cast.CharZero

/-!
# Lemmas on integer matrices

Here we collect some results about matrices over `ℚ` and `ℤ`.

## Main definitions and results

* `Matrix.num`, `Matrix.den`: express a rational matrix `A` as the quotient of an integer matrix
  by a (non-zero) natural.

## TODO

Consider generalizing these constructions to matrices over localizations of rings (or semirings).
-/

@[expose] public section

namespace Matrix

variable {m n : Type*} [Fintype m] [Fintype n]

/-!
## Casts

These results are useful shortcuts because the canonical casting maps out of `ℕ`, `ℤ`, and `ℚ` to
suitable types are bare functions, not ring homs, so we cannot apply `Matrix.map_mul` directly to
them.
-/

/-
**Matrix.map_mul_natCast** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：map_mul_natCast {α : Type*} [NonAssocSemiring α] (A B : Matrix n n Nat) : 
map (A * B) ((↑) : Nat -> α) = map A (↑) * map B (↑)
参数：A B : Matrix n n Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.map_mul`：∀ {m : Type u_2} {n : Type u_3} {o : Type u_4} {α : Type
 v} {β : Type w} [inst : NonUnitalNonAssocSemiring α]   [inst_1 : Fintype n] {L 
: Ma…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …

--- 原说明 ---
## Casts

These results are useful shortcuts because the canonical casting maps out of `ℕ`
, `ℤ`, and `ℚ` to
suitable types are bare functions, not ring homs, so we cannot apply `Matrix.map
_mul` directly to
them.
-/
lemma map_mul_natCast {α : Type*} [NonAssocSemiring α] (A B : Matrix n n ℕ) :
    map (A * B) ((↑) : ℕ → α) = map A (↑) * map B (↑) :=
  Matrix.map_mul (f := Nat.castRingHom α)
/-
**Matrix.map_mul_intCast** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：map_mul_intCast {α : Type*} [NonAssocRing α] (A B : Matrix n n Int) : map 
(A * B) ((↑) : Int -> α) = map A (↑) * map B (↑)
参数：A B : Matrix n n Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.map_mul`：∀ {m : Type u_2} {n : Type u_3} {o : Type u_4} {α : Type
 v} {β : Type w} [inst : NonUnitalNonAssocSemiring α]   [inst_1 : Fintype n] {L 
: Ma…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
-/
lemma map_mul_intCast {α : Type*} [NonAssocRing α] (A B : Matrix n n ℤ) :
    map (A * B) ((↑) : ℤ → α) = map A (↑) * map B (↑) :=
  Matrix.map_mul (f := Int.castRingHom α)
/-
**Matrix.map_mul_ratCast** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：map_mul_ratCast {α : Type*} [DivisionRing α] [CharZero α] (A B : Matrix n 
n Rat) : map (A * B) ((↑) : Rat -> α) = map A (↑) * map B (↑)
参数：A B : Matrix n n Rat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.map_mul`：∀ {m : Type u_2} {n : Type u_3} {o : Type u_4} {α : Type
 v} {β : Type w} [inst : NonUnitalNonAssocSemiring α]   [inst_1 : Fintype n] {L 
: Ma…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
-/
lemma map_mul_ratCast {α : Type*} [DivisionRing α] [CharZero α] (A B : Matrix n n ℚ) :
    map (A * B) ((↑) : ℚ → α) = map A (↑) * map B (↑) :=
  Matrix.map_mul (f := Rat.castHom α)

/-!
## Denominator of a rational matrix
-/

/-- The denominator of a matrix of rationals (as a `Nat`, defined as the LCM of the denominators of
the entries). -/
/-
**Matrix.den** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：{m : Type u_1} → {n : Type u_2} → [Fintype m] → [Fintype n] → Matrix m n ℚ
 → ℕ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The denominator of a matrix of rationals (as a `Nat`, defined as the LCM of the 
denominators of
the entries).
-/
protected def den (A : Matrix m n ℚ) : ℕ := Finset.univ.lcm (fun P : m × n ↦ (A P.1 P.2).den)

/-- The numerator of a matrix of rationals (a matrix of integers, defined so that
`A.num / A.den = A`). -/
/-
**Matrix.num** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：{m : Type u_1} → {n : Type u_2} → [Fintype m] → [Fintype n] → Matrix m n ℚ
 → Matrix m n ℤ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The numerator of a matrix of rationals (a matrix of integers, defined so that
`A.num / A.den = A`).
-/
protected def num (A : Matrix m n ℚ) : Matrix m n ℤ := ((A.den : ℚ) • A).map Rat.num
/-
**Matrix.den_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：den_ne_zero (A : Matrix m n Rat) : A.den != 0
参数：A : Matrix m n Rat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma den_ne_zero (A : Matrix m n ℚ) : A.den ≠ 0 := by
  simp [Matrix.den, Finset.lcm_eq_zero_iff]
/-
**Matrix.num_eq_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：num_eq_zero_iff (A : Matrix m n Rat) : A.num = 0 ↔ A = 0
参数：A : Matrix m n Rat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用引理 `Matrix.den_ne_zero`：den_ne_zero (A : Matrix m n Rat) : A.den != 0
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma num_eq_zero_iff (A : Matrix m n ℚ) : A.num = 0 ↔ A = 0 := by
  simp [Matrix.num, ← ext_iff, A.den_ne_zero]
/-
**Matrix.den_dvd_iff** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：den_dvd_iff {A : Matrix m n Rat} {r : Nat} : A.den ∣ r ↔ forall i j, (A i 
j).den ∣ r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma den_dvd_iff {A : Matrix m n ℚ} {r : ℕ} :
    A.den ∣ r ↔ ∀ i j, (A i j).den ∣ r := by
  simp [Matrix.den]
/-
**Matrix.num_div_den** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：num_div_den (A : Matrix m n Rat) (i : m) (j : n) : A.num i j / A.den = A i
 j
参数：A : Matrix m n Rat；i : m；j : n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Matrix.den_dvd_iff`：den_dvd_iff {A : Matrix m n Rat} {r : Nat} : A.den ∣
 r ↔ forall i j, (A i j).den ∣ r
· 使用定理 `dvd_refl`：dvd_refl (a : α) : a ∣ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.num.eq_1`：∀ {m : Type u_1} {n : Type u_2} [inst : Fintype m] [ins
t_1 : Fintype n] (A : Matrix m n ℚ),   A.num = (↑A.den • A).map Rat.num
· 使用定理 `Matrix.map_apply`：map_apply {M : Matrix m n α} {f : α -> β} {i : m} {j :
 n} : M.map f i j = f (M i j)
· 使用定理 `Matrix.smul_apply`：smul_apply [SMul β α] (r : β) (A : Matrix m n α) (i :
 m) (j : n) : (r • A) i j = r • (A i j)
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用引理 `div_eq_iff`：div_eq_iff (hb : b != 0) : a / b = c ↔ a = c * b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_ne_zero`：cast_ne_zero {n : Nat} : (n : R) != 0 ↔ n != 0
· 使用引理 `Matrix.den_ne_zero`：den_ne_zero (A : Matrix m n Rat) : A.den != 0
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Rat.mul_den_eq_num`：∀ (q : ℚ), q * ↑q.den = ↑q.num
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用引理 `Int.cast_mul`：cast_mul {α : Type*} [NonAssocRing α] : forall m n, ((m * 
n : Int) : α) = m * n
· 使用定理 `Rat.num_intCast`：∀ (a : ℤ), (↑a).num = a
-/
lemma num_div_den (A : Matrix m n ℚ) (i : m) (j : n) :
    A.num i j / A.den = A i j := by
  obtain ⟨k, hk⟩ := den_dvd_iff.mp (dvd_refl A.den) i j
  rw [Matrix.num, map_apply, smul_apply, smul_eq_mul, mul_comm,
    div_eq_iff <| Nat.cast_ne_zero.mpr A.den_ne_zero, hk, Nat.cast_mul, ← mul_assoc,
    Rat.mul_den_eq_num, ← Int.cast_natCast k, ← Int.cast_mul, Rat.num_intCast]
/-
**Matrix.inv_denom_smul_num** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：inv_denom_smul_num (A : Matrix m n Rat) : (A.den⁻¹ : Rat) • A.num.map (↑) 
= A
参数：A : Matrix m n Rat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Matrix.num_div_den`：num_div_den (A : Matrix m n Rat) (i : m) (j : n) : A
.num i j / A.den = A i j
· 使用定理 `div_eq_inv_mul`：div_eq_inv_mul : a / b = b⁻¹ * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma inv_denom_smul_num (A : Matrix m n ℚ) :
    (A.den⁻¹ : ℚ) • A.num.map (↑) = A := by
  ext
  simp [← Matrix.num_div_den A, div_eq_inv_mul]

@[simp]
/-
**Matrix.den_neg** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：den_neg (A : Matrix m n Rat) : (-A).den = A.den
参数：A : Matrix m n Rat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_forall_dvd`：eq_of_forall_dvd (h : forall c, a ∣ c ↔ b ∣ c) : a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma den_neg (A : Matrix m n ℚ) : (-A).den = A.den :=
  eq_of_forall_dvd <| by simp [den_dvd_iff]

@[simp]
/-
**Matrix.num_neg** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：num_neg (A : Matrix m n Rat) : (-A).num = -A.num
参数：A : Matrix m n Rat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matrix.den_neg`：den_neg (A : Matrix m n Rat) : (-A).den = A.den
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma num_neg (A : Matrix m n ℚ) : (-A).num = -A.num := by
  ext
  simp [Matrix.num]
/-
**Matrix.den_transpose** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {m : Type u_1} {n : Type u_2} [inst : Fintype m] [inst_1 : Fintype n] (A
 : Matrix m n ℚ), A.transpose.den = A.den
参数：A : Matrix m n ℚ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_forall_dvd`：eq_of_forall_dvd (h : forall c, a ∣ c ↔ b ∣ c) : a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b
-/
@[simp] lemma den_transpose (A : Matrix m n ℚ) : (Aᵀ).den = A.den :=
  eq_of_forall_dvd fun _ ↦ by simpa [den_dvd_iff] using forall_comm
/-
**Matrix.num_transpose** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {m : Type u_1} {n : Type u_2} [inst : Fintype m] [inst_1 : Fintype n] (A
 : Matrix m n ℚ),   A.transpose.num = A.num.transpose
参数：A : Matrix m n ℚ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.den_transpose`：∀ {m : Type u_1} {n : Type u_2} [inst : Fintype m]
 [inst_1 : Fintype n] (A : Matrix m n ℚ), A.transpose.den = A.den
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma num_transpose (A : Matrix m n ℚ) : (Aᵀ).num = (A.num)ᵀ := by
  ext; simp [Matrix.num]

/-!
### Compatibility with `map`
-/

@[simp]
/-
**Matrix.den_map_intCast** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：den_map_intCast (A : Matrix m n Int) : (A.map (↑)).den = 1
参数：A : Matrix m n Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
### Compatibility with `map`
-/
lemma den_map_intCast (A : Matrix m n ℤ) : (A.map (↑)).den = 1 := by
  simp [← Nat.dvd_one, Matrix.den_dvd_iff]

@[simp]
/-
**Matrix.num_map_intCast** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：num_map_intCast (A : Matrix m n Int) : (A.map (↑)).num = A
参数：A : Matrix m n Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matrix.den_map_intCast`：den_map_intCast (A : Matrix m n Int) : (A.map (↑
)).den = 1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Matrix.map_map`：map_map {M : Matrix m n α} {β γ : Type*} {f : α -> β} {g
 : β -> γ} : (M.map f).map g = M.map (g ∘ f)
· 使用定理 `Matrix.map_id'`：map_id' (M : Matrix m n α) : M.map (·) = M
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma num_map_intCast (A : Matrix m n ℤ) : (A.map (↑)).num = A := by
  simp [Matrix.num, Function.comp_def]

@[simp]
/-
**Matrix.den_map_natCast** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：den_map_natCast (A : Matrix m n Nat) : (A.map (↑)).den = 1
参数：A : Matrix m n Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma den_map_natCast (A : Matrix m n ℕ) : (A.map (↑)).den = 1 := by
  simp [← Nat.dvd_one, Matrix.den_dvd_iff]

@[simp]
/-
**Matrix.num_map_natCast** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：num_map_natCast (A : Matrix m n Nat) : (A.map (↑)).num = A.map (↑)
参数：A : Matrix m n Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matrix.den_map_natCast`：den_map_natCast (A : Matrix m n Nat) : (A.map (↑
)).den = 1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Matrix.map_map`：map_map {M : Matrix m n α} {β γ : Type*} {f : α -> β} {g
 : β -> γ} : (M.map f).map g = M.map (g ∘ f)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma num_map_natCast (A : Matrix m n ℕ) : (A.map (↑)).num = A.map (↑) := by
  simp [Matrix.num, Function.comp_def]

/-!
### Casts from scalar types
-/

@[simp]
/-
**Matrix.den_natCast** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：den_natCast [DecidableEq m] (a : Nat) : (a : Matrix m m Rat).den = 1
参数：a : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.diagonal_map`：diagonal_map [Zero α] [Zero β] {f : α -> β} (h : f 
0 = 0) {d : n -> α} : (diagonal d).map f = diagonal fun m => f (d m)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Matrix.den_map_natCast`：den_map_natCast (A : Matrix m n Nat) : (A.map (↑
)).den = 1

--- 原说明 ---
### Casts from scalar types
-/
lemma den_natCast [DecidableEq m] (a : ℕ) : (a : Matrix m m ℚ).den = 1 := by
  simpa [← diagonal_natCast] using den_map_natCast (a : Matrix m m ℕ)

@[simp]
/-
**Matrix.num_natCast** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：num_natCast [DecidableEq m] (a : Nat) : (a : Matrix m m Rat).num = a
参数：a : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.diagonal_map`：diagonal_map [Zero α] [Zero β] {f : α -> β} (h : f 
0 = 0) {d : n -> α} : (diagonal d).map f = diagonal fun m => f (d m)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Matrix.num_map_natCast`：num_map_natCast (A : Matrix m n Nat) : (A.map (↑
)).num = A.map (↑)
-/
lemma num_natCast [DecidableEq m] (a : ℕ) : (a : Matrix m m ℚ).num = a := by
  simpa [← diagonal_natCast] using num_map_natCast (a : Matrix m m ℕ)

@[simp]
/-
**Matrix.den_ofNat** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：den_ofNat [DecidableEq m] (a : Nat) [a.AtLeastTwo] : (ofNat(a) : Matrix m 
m Rat).den = 1
参数：a : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Matrix.den_natCast`：den_natCast [DecidableEq m] (a : Nat) : (a : Matrix 
m m Rat).den = 1
-/
lemma den_ofNat [DecidableEq m] (a : ℕ) [a.AtLeastTwo] :
    (ofNat(a) : Matrix m m ℚ).den = 1 :=
  den_natCast a

@[simp]
/-
**Matrix.num_ofNat** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：num_ofNat [DecidableEq m] (a : Nat) [a.AtLeastTwo] : (ofNat(a) : Matrix m 
m Rat).num = a
参数：a : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Matrix.num_natCast`：num_natCast [DecidableEq m] (a : Nat) : (a : Matrix 
m m Rat).num = a
-/
lemma num_ofNat [DecidableEq m] (a : ℕ) [a.AtLeastTwo] :
    (ofNat(a) : Matrix m m ℚ).num = a :=
  num_natCast a

@[simp]
/-
**Matrix.den_intCast** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：den_intCast [DecidableEq m] (a : Int) : (a : Matrix m m Rat).den = 1
参数：a : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.diagonal_map`：diagonal_map [Zero α] [Zero β] {f : α -> β} (h : f 
0 = 0) {d : n -> α} : (diagonal d).map f = diagonal fun m => f (d m)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Int.cast_zero`：cast_zero : ((0 : Int) : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Matrix.den_map_intCast`：den_map_intCast (A : Matrix m n Int) : (A.map (↑
)).den = 1
-/
lemma den_intCast [DecidableEq m] (a : ℤ) : (a : Matrix m m ℚ).den = 1 := by
  simpa [← diagonal_intCast] using den_map_intCast (a : Matrix m m ℤ)

@[simp]
/-
**Matrix.num_intCast** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：num_intCast [DecidableEq m] (a : Int) : (a : Matrix m m Rat).num = a
参数：a : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.diagonal_map`：diagonal_map [Zero α] [Zero β] {f : α -> β} (h : f 
0 = 0) {d : n -> α} : (diagonal d).map f = diagonal fun m => f (d m)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Int.cast_zero`：cast_zero : ((0 : Int) : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Matrix.num_map_intCast`：num_map_intCast (A : Matrix m n Int) : (A.map (↑
)).num = A
-/
lemma num_intCast [DecidableEq m] (a : ℤ) : (a : Matrix m m ℚ).num = a := by
  simpa [← diagonal_intCast] using num_map_intCast (a : Matrix m m ℤ)

@[simp]
/-
**Matrix.den_zero** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：den_zero : (0 : Matrix m n Rat).den = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Matrix.den_map_natCast`：den_map_natCast (A : Matrix m n Nat) : (A.map (↑
)).den = 1
-/
lemma den_zero : (0 : Matrix m n ℚ).den = 1 :=
  den_map_natCast 0

@[simp]
/-
**Matrix.num_zero** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：num_zero : (0 : Matrix m n Rat).num = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Matrix.num_map_natCast`：num_map_natCast (A : Matrix m n Nat) : (A.map (↑
)).num = A.map (↑)
-/
lemma num_zero : (0 : Matrix m n ℚ).num = 0 :=
  num_map_natCast 0

@[simp]
/-
**Matrix.den_one** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：den_one [DecidableEq m] : (1 : Matrix m m Rat).den = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Matrix.den_natCast`：den_natCast [DecidableEq m] (a : Nat) : (a : Matrix 
m m Rat).den = 1
-/
lemma den_one [DecidableEq m] : (1 : Matrix m m ℚ).den = 1 :=
  den_natCast 1

@[simp]
/-
**Matrix.num_one** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：num_one [DecidableEq m] : (1 : Matrix m m Rat).num = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Matrix.num_natCast`：num_natCast [DecidableEq m] (a : Nat) : (a : Matrix 
m m Rat).num = a
-/
lemma num_one [DecidableEq m] : (1 : Matrix m m ℚ).num = 1 :=
  num_natCast 1

end Matrix

