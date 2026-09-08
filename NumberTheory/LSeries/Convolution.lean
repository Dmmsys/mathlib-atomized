/-
Copyright (c) 2024 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.NumberTheory.ArithmeticFunction.Defs
public import Mathlib.NumberTheory.LSeries.Convergence

/-!
# Dirichlet convolution of sequences and products of L-series

We define the *Dirichlet convolution* `f ⍟ g` of two sequences `f g : ℕ → R` with values in a
semiring `R` by `(f ⍟ g) n = ∑ (k * m = n), f k * g m` when `n ≠ 0` and `(f ⍟ g) 0 = 0`.
Technically, this is done by transporting the existing definition for `ArithmeticFunction R`;
see `LSeries.convolution`. We show that these definitions agree (`LSeries.convolution_def`).

We then consider the case `R = ℂ` and show that `L (f ⍟ g) = L f * L g` on the common domain
of convergence of the L-series `L f`  and `L g` of `f` and `g`; see `LSeries_convolution`
and `LSeries_convolution'`.
-/

@[expose] public section

open scoped LSeries.notation

open Complex LSeries

/-!
### Dirichlet convolution of two functions
-/

open Nat

/-- We turn any function `ℕ → R` into an `ArithmeticFunction R` by setting its value at `0`
to be zero. -/
/-
**toArithmeticFunction** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：toArithmeticFunction {R : Type*} [Zero R] (f : Nat -> R) : ArithmeticFunct
ion R where toFun n
参数：f : Nat -> R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We turn any function `ℕ → R` into an `ArithmeticFunction R` by setting its value
 at `0`
to be zero.
-/
def toArithmeticFunction {R : Type*} [Zero R] (f : ℕ → R) : ArithmeticFunction R where
  toFun n := if n = 0 then 0 else f n
  map_zero' := rfl

set_option backward.isDefEq.respectTransparency false in
/-
**toArithmeticFunction_congr** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：toArithmeticFunction_congr {R : Type*} [Zero R] {f f' : Nat -> R} (h : for
all {n}, n != 0 -> f n = f' n) : toArithmeticFunction f = toArithmeticFunction f
'
参数：h : forall {n}, n != 0 -> f n = f' n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ArithmeticFunction.ext`：ext ⦃f g : ArithmeticFunction R⦄ (h : forall x, 
f x = g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `ZeroHom.mk.congr_simp`：∀ {M : Type u_10} {N : Type u_11} [inst : Zero M]
 [inst_1 : Zero N] (toFun toFun_1 : M → N) (e_toFun : toFun = toFun_1)   (map_ze
ro' : toFun…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma toArithmeticFunction_congr {R : Type*} [Zero R] {f f' : ℕ → R}
    (h : ∀ {n}, n ≠ 0 → f n = f' n) :
    toArithmeticFunction f = toArithmeticFunction f' := by
  ext
  simp_all [toArithmeticFunction]

set_option backward.isDefEq.respectTransparency false in
/-- If we consider an arithmetic function just as a function and turn it back into an
arithmetic function, it is the same as before. -/
@[simp]
/-
**ArithmeticFunction.toArithmeticFunction_eq_self** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ArithmeticFunction.toArithmeticFunction_eq_self {R : Type*} [Zero R] (f : 
ArithmeticFunction R) : toArithmeticFunction f = f
参数：f : ArithmeticFunction R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ArithmeticFunction.ext`：ext ⦃f g : ArithmeticFunction R⦄ (h : forall x, 
f x = g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ArithmeticFunction.map_zero`：map_zero {f : ArithmeticFunction R} : f 0 =
 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
If we consider an arithmetic function just as a function and turn it back into a
n
arithmetic function, it is the same as before.
-/
lemma ArithmeticFunction.toArithmeticFunction_eq_self {R : Type*} [Zero R]
    (f : ArithmeticFunction R) :
    toArithmeticFunction f = f := by
  ext n
  simp +contextual [toArithmeticFunction]

/-- Dirichlet convolution of two sequences.

We define this in terms of the already existing definition for arithmetic functions. -/
/-
**LSeries.convolution** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：LSeries.convolution {R : Type*} [Semiring R] (f g : Nat -> R) : Nat -> R
参数：f g : Nat -> R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Dirichlet convolution of two sequences.

We define this in terms of the already existing definition for arithmetic functi
ons.
-/
noncomputable def LSeries.convolution {R : Type*} [Semiring R] (f g : ℕ → R) : ℕ → R :=
  ⇑(toArithmeticFunction f * toArithmeticFunction g)

@[inherit_doc]
scoped[LSeries.notation] infixl:70 " ⍟ " => LSeries.convolution
/-
**LSeries.convolution_congr** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LSeries.convolution_congr {R : Type*} [Semiring R] {f f' g g' : Nat -> R} 
(hf : forall {n}, n != 0 -> f n = f' n) (hg : forall {n}, n != 0 -> g n = g' n) 
: f ⍟ g = f' ⍟ g'
参数：hf : forall {n}, n != 0 -> f n = f' n；hg : forall {n}, n != 0 -> g n = g' n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `toArithmeticFunction_congr`：toArithmeticFunction_congr {R : Type*} [Zero
 R] {f f' : Nat -> R} (h : forall {n}, n != 0 -> f n = f' n) : toArithmeticFunct
ion f = toArithm…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma LSeries.convolution_congr {R : Type*} [Semiring R] {f f' g g' : ℕ → R}
    (hf : ∀ {n}, n ≠ 0 → f n = f' n) (hg : ∀ {n}, n ≠ 0 → g n = g' n) :
    f ⍟ g = f' ⍟ g' := by
  simp [convolution, toArithmeticFunction_congr hf, toArithmeticFunction_congr hg]

/-- The product of two arithmetic functions defines the same function as the Dirichlet convolution
of the functions defined by them. -/
/-
**ArithmeticFunction.coe_mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ArithmeticFunction.coe_mul {R : Type*} [Semiring R] (f g : ArithmeticFunct
ion R) : f ⍟ g = ⇑(f * g)
参数：f g : ArithmeticFunction R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `ArithmeticFunction.toArithmeticFunction_eq_self`：ArithmeticFunction.toAr
ithmeticFunction_eq_self {R : Type*} [Zero R] (f : ArithmeticFunction R) : toAri
thmeticFunction f = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The product of two arithmetic functions defines the same function as the Dirichl
et convolution
of the functions defined by them.
-/
lemma ArithmeticFunction.coe_mul {R : Type*} [Semiring R] (f g : ArithmeticFunction R) :
    f ⍟ g = ⇑(f * g) := by
  simp [convolution]

namespace LSeries

set_option backward.isDefEq.respectTransparency false in
/-
**LSeries.convolution_def** 是 Mathlib 中的一个引理，位于命名空间 `LSeries`。
形式化陈述：convolution_def {R : Type*} [Semiring R] (f g : Nat -> R) : f ⍟ g = fun n 
=> ∑ p in n.divisorsAntidiagonal, f p.1 * g p.2
参数：f g : Nat -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `mul_ite`：mul_ite (a b c : α) : (a * if P then b else c) = if P then a * 
b else a * c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用引理 `ite_mul`：ite_mul (a b c : α) : (if P then a else b) * c = if P then a * 
c else b * c
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用引理 `Nat.ne_zero_of_mem_divisorsAntidiagonal`：ne_zero_of_mem_divisorsAntidiag
onal {p : Nat × Nat} (hp : p in n.divisorsAntidiagonal) : p.1 != 0 ∧ p.2 != 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma convolution_def {R : Type*} [Semiring R] (f g : ℕ → R) :
    f ⍟ g = fun n ↦ ∑ p ∈ n.divisorsAntidiagonal, f p.1 * g p.2 := by
  ext n
  simpa [convolution, toArithmeticFunction] using
    Finset.sum_congr rfl fun p hp ↦ by simp [ne_zero_of_mem_divisorsAntidiagonal hp]

@[simp]
/-
**LSeries.convolution_map_zero** 是 Mathlib 中的一个引理，位于命名空间 `LSeries`。
形式化陈述：convolution_map_zero {R : Type*} [Semiring R] (f g : Nat -> R) : (f ⍟ g) 0
 = 0
参数：f g : Nat -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `LSeries.convolution_def`：convolution_def {R : Type*} [Semiring R] (f g :
 Nat -> R) : f ⍟ g = fun n => ∑ p in n.divisorsAntidiagonal, f p.1 * g p.2
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Nat.divisorsAntidiagonal_zero`：divisorsAntidiagonal_zero : divisorsAntid
iagonal 0 = ∅
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma convolution_map_zero {R : Type*} [Semiring R] (f g : ℕ → R) : (f ⍟ g) 0 = 0 := by
  simp [convolution_def]


/-!
### Multiplication of L-series
-/

/-- We give an expression of the `LSeries.term` of the convolution of two functions
in terms of a sum over `Nat.divisorsAntidiagonal`. -/
/-
**LSeries.term_convolution** 是 Mathlib 中的一个引理，位于命名空间 `LSeries`。
形式化陈述：term_convolution (f g : Nat -> Complex) (s : Complex) (n : Nat) : term (f 
⍟ g) s n = ∑ p in n.divisorsAntidiagonal, term f s p.1 * term g s p.2
参数：f g : Nat -> Complex；s : Complex；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Nat.divisorsAntidiagonal_zero`：divisorsAntidiagonal_zero : divisorsAntid
iagonal 0 = ∅
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `LSeries.term_of_ne_zero`：term_of_ne_zero {n : Nat} (hn : n != 0) (f : Na
t -> Complex) (s : Complex) : term f s n = f n / n ^ s
· 使用引理 `LSeries.convolution_def`：convolution_def {R : Type*} [Semiring R] (f g :
 Nat -> R) : f ⍟ g = fun n => ∑ p in n.divisorsAntidiagonal, f p.1 * g p.2
· 使用引理 `Finset.sum_div`：Finset.sum_div (s : Finset ι) (f : ι -> K) (a : K) : (∑ 
i in s, f i) / a = ∑ i in s, f i / a
· 使用引理 `Nat.ne_zero_of_mem_divisorsAntidiagonal`：ne_zero_of_mem_divisorsAntidiag
onal {p : Nat × Nat} (hp : p in n.divisorsAntidiagonal) : p.1 != 0 ∧ p.2 != 0
· 使用定理 `mul_comm_div`：mul_comm_div : a / b * c = a * (c / b)
· 使用定理 `div_div`：div_div : a / b / c = a / (b * c)
· 使用定理 `mul_div_assoc`：mul_div_assoc (a b c : G) : a * b / c = a * (b / c)
· 使用引理 `Complex.natCast_mul_natCast_cpow`：natCast_mul_natCast_cpow (m n : Nat) (
s : Complex) : (m * n : Complex) ^ s = m ^ s * n ^ s
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.mem_divisorsAntidiagonal`：mem_divisorsAntidiagonal {x : Nat × Nat} :
 x in divisorsAntidiagonal n ↔ x.fst * x.snd = n ∧ n != 0

--- 原说明 ---
We give an expression of the `LSeries.term` of the convolution of two functions
in terms of a sum over `Nat.divisorsAntidiagonal`.
-/
lemma term_convolution (f g : ℕ → ℂ) (s : ℂ) (n : ℕ) :
    term (f ⍟ g) s n = ∑ p ∈ n.divisorsAntidiagonal, term f s p.1 * term g s p.2 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  -- now `n ≠ 0`
  rw [term_of_ne_zero hn, convolution_def, Finset.sum_div]
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  have ⟨hp₁, hp₂⟩ := ne_zero_of_mem_divisorsAntidiagonal hp
  rw [term_of_ne_zero hp₁, term_of_ne_zero hp₂, mul_comm_div, div_div, ← mul_div_assoc,
    ← natCast_mul_natCast_cpow, ← cast_mul, mul_comm p.2, (mem_divisorsAntidiagonal.mp hp).1]

open Set in
/-- We give an expression of the `LSeries.term` of the convolution of two functions
in terms of an a priori infinite sum over all pairs `(k, m)` with `k * m = n`
(the set we sum over is infinite when `n = 0`). This is the version needed for the
proof that `L (f ⍟ g) = L f * L g`. -/
/-
**LSeries.term_convolution'** 是 Mathlib 中的一个引理，位于命名空间 `LSeries`。
形式化陈述：term_convolution' (f g : Nat -> Complex) (s : Complex) : term (f ⍟ g) s = 
fun n => ∑' (b : (fun p : Nat × Nat => p.1 * p.2) ⁻¹' {n}), term f s b.val.1 * t
erm g s b.val.2
参数：f g : Nat -> Complex；s : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `LSeries.term_zero`：term_zero (f : Nat -> Complex) (s : Complex) : term f
 s 0 = 0
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `StarOrderedRing.toExistsAddOfLE`：∀ {R : Type u_1} [inst : NonUnitalSemir
ing R] [inst_1 : PartialOrder R] [inst_2 : StarRing R] [StarOrderedRing R],   Ex
istsAddOfLE R
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `tsum_zero`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [ins
t_1 : TopologicalSpace α] {L : SummationFilter β},   ∑'[L] (x : β), 0 = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Finset.tsum_subtype'`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMon
oid α] [inst_1 : TopologicalSpace α] (s : Finset β) (f : β → α),   ∑' (x : ↑↑s),
 f ↑x = ∑ …
· 使用引理 `LSeries.term_convolution`：term_convolution (f g : Nat -> Complex) (s : C
omplex) (n : Nat) : term (f ⍟ g) s n = ∑ p in n.divisorsAntidiagonal, term f s p
.1 * term g s …

--- 原说明 ---
We give an expression of the `LSeries.term` of the convolution of two functions
in terms of an a priori infinite sum over all pairs `(k, m)` with `k * m = n`
(the set we sum over is infinite when `n = 0`). This is the version needed for t
he
proof that `L (f ⍟ g) = L f * L g`.
-/
lemma term_convolution' (f g : ℕ → ℂ) (s : ℂ) :
    term (f ⍟ g) s = fun n ↦
      ∑' (b : (fun p : ℕ × ℕ ↦ p.1 * p.2) ⁻¹' {n}), term f s b.val.1 * term g s b.val.2 := by
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · -- show that both sides vanish when `n = 0`; this is the hardest part of the proof!
    refine (term_zero ..).trans ?_
    -- the right-hand sum is over the union below, but in each term, one factor is always zero
    have hS : (fun p ↦ p.1 * p.2) ⁻¹' {0} = {0} ×ˢ univ ∪ univ ×ˢ {0} := by
      ext
      simp
    have : ∀ p : (fun p : ℕ × ℕ ↦ p.1 * p.2) ⁻¹' {0}, term f s p.val.1 * term g s p.val.2 = 0 := by
      rintro ⟨⟨_, _⟩, hp⟩
      rcases hS ▸ hp with ⟨rfl, -⟩ | ⟨-, rfl⟩ <;> simp
    simp [this]
  -- now `n ≠ 0`
  rw [show (fun p : ℕ × ℕ ↦ p.1 * p.2) ⁻¹' {n} = n.divisorsAntidiagonal by ext; simp [hn],
    Finset.tsum_subtype' n.divisorsAntidiagonal fun p ↦ term f s p.1 * term g s p.2,
    term_convolution f g s n]

end LSeries

open Set in
/-- The L-series of the convolution product `f ⍟ g` of two sequences `f` and `g`
equals the product of their L-series, assuming both L-series converge. -/
/-
**LSeriesHasSum.convolution** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LSeriesHasSum.convolution {f g : Nat -> Complex} {s a b : Complex} (hf : L
SeriesHasSum f s a) (hg : LSeriesHasSum g s b) : LSeriesHasSum (f ⍟ g) s (a * b)
参数：hf : LSeriesHasSum f s a；hg : LSeriesHasSum g s b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `summable_mul_of_summable_norm`：summable_mul_of_summable_norm [CompleteSp
ace R] {f : ι -> R} {g : ι' -> R} (hf : Summable fun x => ‖f x‖) (hg : Summable 
fun x => ‖g x‖) : S…
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用定理 `Summable.norm`：∀ {α : Type u_1} {E : Type u_2} [inst : NormedAddCommGrou
p E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E]   {f : α → E}, Summable 
f →…
· 使用定理 `Complex.instFiniteDimensionalReal`：FiniteDimensional ℝ ℂ
· 使用定理 `HasSum.summable`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α}, H
asSum…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LSeries.term_convolution'`：term_convolution' (f g : Nat -> Complex) (s :
 Complex) : term (f ⍟ g) s = fun n => ∑' (b : (fun p : Nat × Nat => p.1 * p.2) ⁻
¹' {n}), term f…
· 使用定理 `HasSum.tsum_fiberwise`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [i
nst : AddCommGroup α] [inst_1 : UniformSpace α] [IsUniformAddGroup α]   [Complet
eSpace α] […
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `Complex.instT2Space`：T2Space ℂ
· 使用定理 `HasSum.mul`：HasSum.mul (hf : HasSum f s) (hg : HasSum g t) (hfg : Summab
le fun x : ι × κ => f x.1 * g x.2) : HasSum (fun x : ι × κ => f x.1 * g x.2) (s 
…
· 使用定理 `T4Space.t3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T4Space X
], T3Space X
· 使用定理 `instT4SpaceOfT1SpaceOfNormalSpace`：∀ {X : Type u_1} [inst : TopologicalS
pace X] [T1Space X] [NormalSpace X], T4Space X
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `CompletelyNormalSpace.toNormalSpace`：∀ {X : Type u_1} [inst : Topologica
lSpace X] [CompletelyNormalSpace X], NormalSpace X
· 使用定理 `UniformSpace.completelyNormalSpace_of_isCountablyGenerated_uniformity`：∀
 {α : Type u} [inst : UniformSpace α] [(uniformity α).IsCountablyGenerated], Com
pletelyNormalSpace α
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α

--- 原说明 ---
The L-series of the convolution product `f ⍟ g` of two sequences `f` and `g`
equals the product of their L-series, assuming both L-series converge.
-/
lemma LSeriesHasSum.convolution {f g : ℕ → ℂ} {s a b : ℂ} (hf : LSeriesHasSum f s a)
    (hg : LSeriesHasSum g s b) :
    LSeriesHasSum (f ⍟ g) s (a * b) := by
  have hsum := summable_mul_of_summable_norm hf.summable.norm hg.summable.norm
  -- NB: this `simpa` is quite slow if un-squeezed
  simpa only [LSeriesHasSum, term_convolution'] using (hf.mul hg hsum).tsum_fiberwise _

/-- The L-series of the convolution product `f ⍟ g` of two sequences `f` and `g`
equals the product of their L-series, assuming both L-series converge. -/
/-
**LSeries_convolution'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LSeries_convolution' {f g : Nat -> Complex} {s : Complex} (hf : LSeriesSum
mable f s) (hg : LSeriesSummable g s) : LSeries (f ⍟ g) s = LSeries f s * LSerie
s g s
参数：hf : LSeriesSummable f s；hg : LSeriesSummable g s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LSeriesHasSum.LSeries_eq`：LSeriesHasSum.LSeries_eq {f : Nat -> Complex} 
{s a : Complex} (h : LSeriesHasSum f s a) : LSeries f s = a
· 使用引理 `LSeriesHasSum.convolution`：LSeriesHasSum.convolution {f g : Nat -> Compl
ex} {s a b : Complex} (hf : LSeriesHasSum f s a) (hg : LSeriesHasSum g s b) : LS
eriesHasSum (f …
· 使用引理 `LSeriesSummable.LSeriesHasSum`：LSeriesSummable.LSeriesHasSum {f : Nat ->
 Complex} {s : Complex} (h : LSeriesSummable f s) : LSeriesHasSum f s (LSeries f
 s)

--- 原说明 ---
The L-series of the convolution product `f ⍟ g` of two sequences `f` and `g`
equals the product of their L-series, assuming both L-series converge.
-/
lemma LSeries_convolution' {f g : ℕ → ℂ} {s : ℂ} (hf : LSeriesSummable f s)
    (hg : LSeriesSummable g s) :
    LSeries (f ⍟ g) s = LSeries f s * LSeries g s :=
  (LSeriesHasSum.convolution hf.LSeriesHasSum hg.LSeriesHasSum).LSeries_eq

/-- The L-series of the convolution product `f ⍟ g` of two sequences `f` and `g`
equals the product of their L-series in their common half-plane of absolute convergence. -/
/-
**LSeries_convolution** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LSeries_convolution {f g : Nat -> Complex} {s : Complex} (hf : abscissaOfA
bsConv f < s.re) (hg : abscissaOfAbsConv g < s.re) : LSeries (f ⍟ g) s = LSeries
 f s * LSeries g s
参数：hf : abscissaOfAbsConv f < s.re；hg : abscissaOfAbsConv g < s.re。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LSeries_convolution'`：LSeries_convolution' {f g : Nat -> Complex} {s : C
omplex} (hf : LSeriesSummable f s) (hg : LSeriesSummable g s) : LSeries (f ⍟ g) 
s = LSerie…
· 使用引理 `LSeriesSummable_of_abscissaOfAbsConv_lt_re`：LSeriesSummable_of_abscissaO
fAbsConv_lt_re {f : Nat -> Complex} {s : Complex} (hs : abscissaOfAbsConv f < s.
re) : LSeriesSummable f s

--- 原说明 ---
The L-series of the convolution product `f ⍟ g` of two sequences `f` and `g`
equals the product of their L-series in their common half-plane of absolute conv
ergence.
-/
lemma LSeries_convolution {f g : ℕ → ℂ} {s : ℂ}
    (hf : abscissaOfAbsConv f < s.re) (hg : abscissaOfAbsConv g < s.re) :
    LSeries (f ⍟ g) s = LSeries f s * LSeries g s :=
  LSeries_convolution' (LSeriesSummable_of_abscissaOfAbsConv_lt_re hf)
    (LSeriesSummable_of_abscissaOfAbsConv_lt_re hg)

/-- The L-series of the convolution product `f ⍟ g` of two sequences `f` and `g`
is summable when both L-series are summable. -/
/-
**LSeriesSummable.convolution** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LSeriesSummable.convolution {f g : Nat -> Complex} {s : Complex} (hf : LSe
riesSummable f s) (hg : LSeriesSummable g s) : LSeriesSummable (f ⍟ g) s
参数：hf : LSeriesSummable f s；hg : LSeriesSummable g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LSeriesHasSum.LSeriesSummable`：LSeriesHasSum.LSeriesSummable {f : Nat ->
 Complex} {s a : Complex} (h : LSeriesHasSum f s a) : LSeriesSummable f s
· 使用引理 `LSeriesHasSum.convolution`：LSeriesHasSum.convolution {f g : Nat -> Compl
ex} {s a b : Complex} (hf : LSeriesHasSum f s a) (hg : LSeriesHasSum g s b) : LS
eriesHasSum (f …
· 使用引理 `LSeriesSummable.LSeriesHasSum`：LSeriesSummable.LSeriesHasSum {f : Nat ->
 Complex} {s : Complex} (h : LSeriesSummable f s) : LSeriesHasSum f s (LSeries f
 s)

--- 原说明 ---
The L-series of the convolution product `f ⍟ g` of two sequences `f` and `g`
is summable when both L-series are summable.
-/
lemma LSeriesSummable.convolution {f g : ℕ → ℂ} {s : ℂ} (hf : LSeriesSummable f s)
    (hg : LSeriesSummable g s) :
    LSeriesSummable (f ⍟ g) s :=
  (LSeriesHasSum.convolution hf.LSeriesHasSum hg.LSeriesHasSum).LSeriesSummable

/-- The abscissa of absolute convergence of `f ⍟ g` is at most the maximum of those
of `f` and `g`. -/
/-
**LSeries.abscissaOfAbsConv_convolution_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LSeries.abscissaOfAbsConv_convolution_le (f g : Nat -> Complex) : abscissa
OfAbsConv (f ⍟ g) <= max (abscissaOfAbsConv f) (abscissaOfAbsConv g)
参数：f g : Nat -> Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LSeries.abscissaOfAbsConv_binop_le`：LSeries.abscissaOfAbsConv_binop_le {
F : (Nat -> Complex) -> (Nat -> Complex) -> (Nat -> Complex)} (hF : forall {f g 
s}, LSeriesSummable f s …
· 使用引理 `LSeriesSummable.convolution`：LSeriesSummable.convolution {f g : Nat -> C
omplex} {s : Complex} (hf : LSeriesSummable f s) (hg : LSeriesSummable g s) : LS
eriesSummable (f …

--- 原说明 ---
The abscissa of absolute convergence of `f ⍟ g` is at most the maximum of those
of `f` and `g`.
-/
lemma LSeries.abscissaOfAbsConv_convolution_le (f g : ℕ → ℂ) :
    abscissaOfAbsConv (f ⍟ g) ≤ max (abscissaOfAbsConv f) (abscissaOfAbsConv g) :=
  abscissaOfAbsConv_binop_le LSeriesSummable.convolution f g

namespace ArithmeticFunction

/-!
### Versions for arithmetic functions
-/

/-- The L-series of the (convolution) product of two `ℂ`-valued arithmetic functions `f` and `g`
equals the product of their L-series, assuming both L-series converge. -/
/-
**ArithmeticFunction.LSeriesHasSum_mul** 是 Mathlib 中的一个引理，位于命名空间 `ArithmeticFunc
tion`。
形式化陈述：LSeriesHasSum_mul {f g : ArithmeticFunction Complex} {s a b : Complex} (hf
 : LSeriesHasSum ↗f s a) (hg : LSeriesHasSum ↗g s b) : LSeriesHasSum ↗(f * g) s 
(a * b)
参数：hf : LSeriesHasSum ↗f s a；hg : LSeriesHasSum ↗g s b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LSeriesHasSum.convolution`：LSeriesHasSum.convolution {f g : Nat -> Compl
ex} {s a b : Complex} (hf : LSeriesHasSum f s a) (hg : LSeriesHasSum g s b) : LS
eriesHasSum (f …
· 使用引理 `ArithmeticFunction.coe_mul`：ArithmeticFunction.coe_mul {R : Type*} [Semi
ring R] (f g : ArithmeticFunction R) : f ⍟ g = ⇑(f * g)

--- 原说明 ---
The L-series of the (convolution) product of two `ℂ`-valued arithmetic functions
 `f` and `g`
equals the product of their L-series, assuming both L-series converge.
-/
lemma LSeriesHasSum_mul {f g : ArithmeticFunction ℂ} {s a b : ℂ} (hf : LSeriesHasSum ↗f s a)
    (hg : LSeriesHasSum ↗g s b) :
    LSeriesHasSum ↗(f * g) s (a * b) :=
  coe_mul f g ▸ hf.convolution hg

/-- The L-series of the (convolution) product of two `ℂ`-valued arithmetic functions `f` and `g`
equals the product of their L-series, assuming both L-series converge. -/
/-
**ArithmeticFunction.LSeries_mul'** 是 Mathlib 中的一个引理，位于命名空间 `ArithmeticFunction`
。
形式化陈述：LSeries_mul' {f g : ArithmeticFunction Complex} {s : Complex} (hf : LSerie
sSummable ↗f s) (hg : LSeriesSummable ↗g s) : LSeries ↗(f * g) s = LSeries ↗f s 
* LSeries ↗g s
参数：hf : LSeriesSummable ↗f s；hg : LSeriesSummable ↗g s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LSeries_convolution'`：LSeries_convolution' {f g : Nat -> Complex} {s : C
omplex} (hf : LSeriesSummable f s) (hg : LSeriesSummable g s) : LSeries (f ⍟ g) 
s = LSerie…
· 使用引理 `ArithmeticFunction.coe_mul`：ArithmeticFunction.coe_mul {R : Type*} [Semi
ring R] (f g : ArithmeticFunction R) : f ⍟ g = ⇑(f * g)

--- 原说明 ---
The L-series of the (convolution) product of two `ℂ`-valued arithmetic functions
 `f` and `g`
equals the product of their L-series, assuming both L-series converge.
-/
lemma LSeries_mul' {f g : ArithmeticFunction ℂ} {s : ℂ} (hf : LSeriesSummable ↗f s)
    (hg : LSeriesSummable ↗g s) :
    LSeries ↗(f * g) s = LSeries ↗f s * LSeries ↗g s :=
  coe_mul f g ▸ LSeries_convolution' hf hg

/-- The L-series of the (convolution) product of two `ℂ`-valued arithmetic functions `f` and `g`
equals the product of their L-series in their common half-plane of absolute convergence. -/
/-
**ArithmeticFunction.LSeries_mul** 是 Mathlib 中的一个引理，位于命名空间 `ArithmeticFunction`。
形式化陈述：LSeries_mul {f g : ArithmeticFunction Complex} {s : Complex} (hf : absciss
aOfAbsConv ↗f < s.re) (hg : abscissaOfAbsConv ↗g < s.re) : LSeries ↗(f * g) s = 
LSeries ↗f s * LSeries ↗g s
参数：hf : abscissaOfAbsConv ↗f < s.re；hg : abscissaOfAbsConv ↗g < s.re。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LSeries_convolution`：LSeries_convolution {f g : Nat -> Complex} {s : Com
plex} (hf : abscissaOfAbsConv f < s.re) (hg : abscissaOfAbsConv g < s.re) : LSer
ies (f ⍟ …
· 使用引理 `ArithmeticFunction.coe_mul`：ArithmeticFunction.coe_mul {R : Type*} [Semi
ring R] (f g : ArithmeticFunction R) : f ⍟ g = ⇑(f * g)

--- 原说明 ---
The L-series of the (convolution) product of two `ℂ`-valued arithmetic functions
 `f` and `g`
equals the product of their L-series in their common half-plane of absolute conv
ergence.
-/
lemma LSeries_mul {f g : ArithmeticFunction ℂ} {s : ℂ}
    (hf : abscissaOfAbsConv ↗f < s.re) (hg : abscissaOfAbsConv ↗g < s.re) :
    LSeries ↗(f * g) s = LSeries ↗f s * LSeries ↗g s :=
  coe_mul f g ▸ LSeries_convolution hf hg

/-- The L-series of the (convolution) product of two `ℂ`-valued arithmetic functions `f` and `g`
is summable when both L-series are summable. -/
/-
**ArithmeticFunction.LSeriesSummable_mul** 是 Mathlib 中的一个引理，位于命名空间 `ArithmeticFu
nction`。
形式化陈述：LSeriesSummable_mul {f g : ArithmeticFunction Complex} {s : Complex} (hf :
 LSeriesSummable ↗f s) (hg : LSeriesSummable ↗g s) : LSeriesSummable ↗(f * g) s
参数：hf : LSeriesSummable ↗f s；hg : LSeriesSummable ↗g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LSeriesSummable.convolution`：LSeriesSummable.convolution {f g : Nat -> C
omplex} {s : Complex} (hf : LSeriesSummable f s) (hg : LSeriesSummable g s) : LS
eriesSummable (f …
· 使用引理 `ArithmeticFunction.coe_mul`：ArithmeticFunction.coe_mul {R : Type*} [Semi
ring R] (f g : ArithmeticFunction R) : f ⍟ g = ⇑(f * g)

--- 原说明 ---
The L-series of the (convolution) product of two `ℂ`-valued arithmetic functions
 `f` and `g`
is summable when both L-series are summable.
-/
lemma LSeriesSummable_mul {f g : ArithmeticFunction ℂ} {s : ℂ} (hf : LSeriesSummable ↗f s)
    (hg : LSeriesSummable ↗g s) :
    LSeriesSummable ↗(f * g) s :=
  coe_mul f g ▸ hf.convolution hg

end ArithmeticFunction

