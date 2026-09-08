/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.Polynomial.Eval.SMul
public import Mathlib.Algebra.Polynomial.HasseDeriv

/-!
# Taylor expansions of polynomials

## Main declarations

* `Polynomial.taylor`: the Taylor expansion of the polynomial `f` at `r`
* `Polynomial.taylor_coeff`: the `k`th coefficient of `taylor r f` is
  `(Polynomial.hasseDeriv k f).eval r`
* `Polynomial.eq_zero_of_hasseDeriv_eq_zero`:
  the identity principle: a polynomial is 0 iff all its Hasse derivatives are zero

-/

@[expose] public section


noncomputable section

namespace Polynomial

section Semiring

variable {R : Type*} [Semiring R] (r : R) (f : R[X])

/-- The Taylor expansion of a polynomial `f` at `r`. -/
/-
**Polynomial.taylor** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：taylor (r : R) : R[X] ->ₗ[R] R[X] where toFun f
参数：r : R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Taylor expansion of a polynomial `f` at `r`.
-/
def taylor (r : R) : R[X] →ₗ[R] R[X] where
  toFun f := f.comp (X + C r)
  map_add' _ _ := add_comp
  map_smul' c f := by simp only [smul_eq_C_mul, C_mul_comp, RingHom.id_apply]
/-
**Polynomial.taylor_apply** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：taylor_apply : taylor r f = f.comp (X + C r)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem taylor_apply : taylor r f = f.comp (X + C r) :=
  rfl

@[simp]
/-
**Polynomial.taylor_X** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：taylor_X : taylor r X = X + C r
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.X_comp`：X_comp : X.comp p = p
-/
theorem taylor_X : taylor r X = X + C r := X_comp

@[simp]
/-
**Polynomial.taylor_X_pow** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：taylor_X_pow (n : Nat) : taylor r (X ^ n) = (X + C r) ^ n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.X_pow_comp`：X_pow_comp {k : Nat} : (X ^ k).comp p = p ^ k
-/
theorem taylor_X_pow (n : ℕ) : taylor r (X ^ n) = (X + C r) ^ n := X_pow_comp

@[simp]
/-
**Polynomial.taylor_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：taylor_C (x : R) : taylor r (C x) = C x
参数：x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.C_comp`：C_comp : (C a).comp p = C a
-/
theorem taylor_C (x : R) : taylor r (C x) = C x := C_comp
/-
**Polynomial.taylor_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：taylor_zero (f : R[X]) : taylor 0 f = f
参数：f : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.taylor_apply`：taylor_apply : taylor r f = f.comp (X + C r)
· 使用定理 `Polynomial.C_0`：C_0 : C (0 : R) = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Polynomial.comp_X`：comp_X : p.comp X = p
-/
theorem taylor_zero (f : R[X]) : taylor 0 f = f := by rw [taylor_apply, C_0, add_zero, comp_X]

@[simp]
/-
**Polynomial.taylor_zero'** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：taylor_zero' : taylor (0 : R) = LinearMap.id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Polynomial.taylor_zero`：taylor_zero (f : R[X]) : taylor 0 f = f
-/
theorem taylor_zero' : taylor (0 : R) = LinearMap.id := LinearMap.ext taylor_zero

@[simp]
/-
**Polynomial.taylor_one** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：taylor_one : taylor r (1 : R[X]) = C 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.taylor_C`：taylor_C (x : R) : taylor r (C x) = C x
-/
theorem taylor_one : taylor r (1 : R[X]) = C 1 := taylor_C r 1

@[simp]
/-
**Polynomial.taylor_monomial** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：taylor_monomial (i : Nat) (k : R) : taylor r (monomial i k) = C k * (X + C
 r) ^ i
参数：i : Nat；k : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.monomial_comp`：monomial_comp (n : Nat) : (monomial n a).comp 
p = C a * p ^ n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem taylor_monomial (i : ℕ) (k : R) : taylor r (monomial i k) = C k * (X + C r) ^ i := by
  simp [taylor_apply]

/-- The `k`th coefficient of `Polynomial.taylor r f` is `(Polynomial.hasseDeriv k f).eval r`. -/
/-
**Polynomial.taylor_coeff** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：taylor_coeff (n : Nat) : (taylor r f).coeff n = (hasseDeriv n f).eval r
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.lhom_ext'`：lhom_ext' {M : Type*} [AddCommMonoid M] [Module R 
M] {f g : R[X] ->ₗ[R] M} (h : forall n, f.comp (monomial n) = g.comp (monomial n
)) : f = g
· 使用定理 `LinearMap.ext_ring`：ext_ring {f g : R ->ₛₗ[σ] M₃} (h : f 1 = g 1) : f = 
g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.monomial_comp`：monomial_comp (n : Nat) : (monomial n a).comp 
p = C a * p ^ n
· 使用定理 `Commute.add_pow`：add_pow (h : Commute x y) (n : Nat) : (x + y) ^ n = ∑ m
 in range (n + 1), x ^ m * y ^ (n - m) * n.choose m
· 使用定理 `Polynomial.commute_X`：commute_X (p : R[X]) : Commute X p
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `Polynomial.hasseDeriv_monomial`：hasseDeriv_monomial (n : Nat) (r : R) : 
hasseDeriv k (monomial n r) = monomial (n - k) (↑(n.choose k) * r)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Polynomial.leval_apply`：∀ {R : Type u_1} [inst : Semiring R] (r : R) (f 
: Polynomial R), (Polynomial.leval r) f = Polynomial.eval r f
· 使用定理 `Polynomial.eval_monomial`：eval_monomial {n a} : (monomial n a).eval x = 
a * x ^ n
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Polynomial.coeff_mul_C`：coeff_mul_C (p : R[X]) (n : Nat) (a : R) : coeff
 (p * C a) n = coeff p n * a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.coeff_X_pow`：coeff_X_pow (k n : Nat) : coeff (X ^ k : R[X]) n
 = if n = k then 1 else 0
· 使用定理 `boole_mul`：boole_mul {α} [MulZeroOneClass α] (P : Prop) [Decidable P] (a
 : α) : (if P then 1 else 0) * a = if P then a else 0
· 使用定理 `Finset.sum_ite_eq`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoid
 M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if 
a = x t…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Commute.eq`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → a *
 b = b * a
· 使用定理 `Nat.cast_commute`：cast_commute (n : Nat) (x : α) : Commute (n : α) x
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Nat.choose_eq_zero_of_lt`：choose_eq_zero_of_lt : forall {n k}, n < k -> 
choose n k = 0 | _, 0, hk => absurd hk (Nat.not_lt_zero _) | 0, _ + 1, _ => choo
se_zero_succ _…
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
The `k`th coefficient of `Polynomial.taylor r f` is `(Polynomial.hasseDeriv k f)
.eval r`.
-/
theorem taylor_coeff (n : ℕ) : (taylor r f).coeff n = (hasseDeriv n f).eval r :=
  show (lcoeff R n).comp (taylor r) f = (leval r).comp (hasseDeriv n) f by
    congr 1; clear! f; ext i
    simp only [leval_apply, mul_one, one_mul, eval_monomial, LinearMap.comp_apply, map_sum,
      hasseDeriv_monomial, taylor_apply, monomial_comp, C_1, (commute_X (C r)).add_pow i]
    simp only [lcoeff_apply, ← C_eq_natCast, mul_assoc, ← C_pow, ← C_mul, coeff_mul_C,
      (Nat.cast_commute _ _).eq, coeff_X_pow, boole_mul, Finset.sum_ite_eq, Finset.mem_range]
    split_ifs with h; · rfl
    push Not at h; rw [Nat.choose_eq_zero_of_lt h, Nat.cast_zero, mul_zero]

@[simp]
/-
**Polynomial.taylor_coeff_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：taylor_coeff_zero : (taylor r f).coeff 0 = f.eval r
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.taylor_coeff`：taylor_coeff (n : Nat) : (taylor r f).coeff n =
 (hasseDeriv n f).eval r
· 使用定理 `Polynomial.hasseDeriv_zero`：hasseDeriv_zero : @hasseDeriv R _ 0 = Linear
Map.id
· 使用定理 `LinearMap.id_apply`：id_apply (x : M) : @id R M _ _ _ x = x
-/
theorem taylor_coeff_zero : (taylor r f).coeff 0 = f.eval r := by
  rw [taylor_coeff, hasseDeriv_zero, LinearMap.id_apply]

@[simp]
/-
**Polynomial.taylor_coeff_one** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：taylor_coeff_one : (taylor r f).coeff 1 = f.derivative.eval r
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.taylor_coeff`：taylor_coeff (n : Nat) : (taylor r f).coeff n =
 (hasseDeriv n f).eval r
· 使用定理 `Polynomial.hasseDeriv_one`：hasseDeriv_one : @hasseDeriv R _ 1 = derivati
ve
-/
theorem taylor_coeff_one : (taylor r f).coeff 1 = f.derivative.eval r := by
  rw [taylor_coeff, hasseDeriv_one]

@[simp]
/-
**Polynomial.coeff_taylor_natDegree** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：coeff_taylor_natDegree : (taylor r f).coeff f.natDegree = f.leadingCoeff
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `Polynomial.coeff_natDegree`：coeff_natDegree : coeff p (natDegree p) = le
adingCoeff p
· 使用定理 `Polynomial.taylor_coeff`：taylor_coeff (n : Nat) : (taylor r f).coeff n =
 (hasseDeriv n f).eval r
· 使用定理 `Polynomial.hasseDeriv_natDegree_eq_C`：hasseDeriv_natDegree_eq_C : f.hass
eDeriv f.natDegree = C f.leadingCoeff
· 使用定理 `Polynomial.eval_C`：eval_C : (C a).eval x = a
-/
theorem coeff_taylor_natDegree : (taylor r f).coeff f.natDegree = f.leadingCoeff := by
  by_cases hf : f = 0
  · rw [hf, map_zero, coeff_natDegree]
  · rw [taylor_coeff, hasseDeriv_natDegree_eq_C, eval_C]

@[simp]
/-
**Polynomial.natDegree_taylor** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_taylor (p : R[X]) (r : R) : natDegree (taylor r p) = natDegree p
参数：p : R[X]；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.map_natDegree_eq_natDegree`：map_natDegree_eq_natDegree {S F :
 Type*} [Semiring S] [FunLike F R[X] S[X]] [AddMonoidHomClass F R[X] S[X]] {φ : 
F} (p) (φ_mon_nat : forall …
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.taylor_monomial`：taylor_monomial (i : Nat) (k : R) : taylor r
 (monomial i k) = C k * (X + C r) ^ i
· 使用定理 `Polynomial.natDegree_of_subsingleton`：natDegree_of_subsingleton [Subsing
leton R] : natDegree p = 0
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Polynomial.natDegree_C_mul_of_mul_ne_zero`：natDegree_C_mul_of_mul_ne_zer
o (h : a * p.leadingCoeff != 0) : (C a * p).natDegree = p.natDegree
· 使用定理 `Polynomial.leadingCoeff_pow_X_add_C`：leadingCoeff_pow_X_add_C (r : R) (i
 : Nat) : leadingCoeff ((X + C r) ^ i) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Polynomial.natDegree_pow_X_add_C`：natDegree_pow_X_add_C [Nontrivial R] (
n : Nat) (r : R) : ((X + C r) ^ n).natDegree = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem natDegree_taylor (p : R[X]) (r : R) : natDegree (taylor r p) = natDegree p := by
  refine map_natDegree_eq_natDegree _ ?_
  nontriviality R
  intro n c c0
  simp [taylor_monomial, natDegree_C_mul_of_mul_ne_zero, natDegree_pow_X_add_C, c0]

@[simp]
/-
**Polynomial.leadingCoeff_taylor** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：leadingCoeff_taylor : (taylor r f).leadingCoeff = f.leadingCoeff
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.leadingCoeff.eq_1`：∀ {R : Type u} [inst : Semiring R] (p : Po
lynomial R), p.leadingCoeff = p.coeff p.natDegree
· 使用定理 `Polynomial.natDegree_taylor`：natDegree_taylor (p : R[X]) (r : R) : natDe
gree (taylor r p) = natDegree p
· 使用定理 `Polynomial.coeff_taylor_natDegree`：coeff_taylor_natDegree : (taylor r f)
.coeff f.natDegree = f.leadingCoeff
-/
theorem leadingCoeff_taylor : (taylor r f).leadingCoeff = f.leadingCoeff := by
  rw [leadingCoeff, leadingCoeff, natDegree_taylor, coeff_taylor_natDegree, leadingCoeff]

@[simp]
/-
**Polynomial.taylor_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：taylor_eq_zero : taylor r f = 0 ↔ f = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.leadingCoeff_eq_zero`：leadingCoeff_eq_zero : leadingCoeff p =
 0 ↔ p = 0
· 使用定理 `Polynomial.leadingCoeff_taylor`：leadingCoeff_taylor : (taylor r f).leadi
ngCoeff = f.leadingCoeff
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem taylor_eq_zero : taylor r f = 0 ↔ f = 0 := by
  rw [← leadingCoeff_eq_zero, ← leadingCoeff_eq_zero, leadingCoeff_taylor]

@[simp]
/-
**Polynomial.degree_taylor** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degree_taylor (p : R[X]) (r : R) : degree (taylor r p) = degree p
参数：p : R[X]；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `Polynomial.degree_eq_natDegree`：degree_eq_natDegree (hp : p != 0) : degr
ee p = (natDegree p : WithBot Nat)
· 使用定理 `Polynomial.degree_eq_iff_natDegree_eq`：degree_eq_iff_natDegree_eq {p : R
[X]} {n : Nat} (hp : p != 0) : p.degree = n ↔ p.natDegree = n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Polynomial.taylor_eq_zero`：taylor_eq_zero : taylor r f = 0 ↔ f = 0
· 使用定理 `Polynomial.natDegree_taylor`：natDegree_taylor (p : R[X]) (r : R) : natDe
gree (taylor r p) = natDegree p
-/
theorem degree_taylor (p : R[X]) (r : R) : degree (taylor r p) = degree p := by
  by_cases hp : p = 0
  · rw [hp, map_zero]
  · rw [degree_eq_natDegree hp, degree_eq_iff_natDegree_eq ((taylor_eq_zero r p).not.2 hp),
      natDegree_taylor]
/-
**Polynomial.eq_zero_of_hasseDeriv_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial
`。
形式化陈述：eq_zero_of_hasseDeriv_eq_zero (f : R[X]) (r : R) (h : forall k, (hasseDeri
v k f).eval r = 0) : f = 0
参数：f : R[X]；r : R；h : forall k, (hasseDeriv k f).eval r = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.taylor_eq_zero`：taylor_eq_zero : taylor r f = 0 ↔ f = 0
· 使用定理 `Polynomial.ext`：ext {p q : R[X]} : (forall n, coeff p n = coeff q n) -> 
p = q
· 使用定理 `Polynomial.taylor_coeff`：taylor_coeff (n : Nat) : (taylor r f).coeff n =
 (hasseDeriv n f).eval r
· 使用定理 `Polynomial.coeff_zero`：coeff_zero (n : Nat) : coeff (0 : R[X]) n = 0
-/
theorem eq_zero_of_hasseDeriv_eq_zero (f : R[X]) (r : R)
    (h : ∀ k, (hasseDeriv k f).eval r = 0) : f = 0 := by
  rw [← taylor_eq_zero r]
  ext k
  rw [taylor_coeff, h, coeff_zero]
/-
**Polynomial.map_taylor** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ {R : Type u_2} {S : Type u_3} [inst : Semiring R] [inst_1 : Semiring S] 
(p : Polynomial R) (r : R) (f : R →+* S),   Polynomial.map f ((Polynomial.taylor
 r) p) = (Polynomial.taylor (f r)) (Polynomial.map f p)
参数：p : Polynomial R；r : R；f : R →+* S；(Polynomial.taylor r) p；Polynomial.taylor 
(f r)；Polynomial.map f p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.map_comp`：map_comp (p q : R[X]) : map f (p.comp q) = (map f p
).comp (map f q)
· 使用定理 `Polynomial.map_add`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p q
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   Polynomial.map f (p + q)
 = Polyn…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.map_X`：map_X : X.map f = X
· 使用定理 `Polynomial.map_C`：map_C : (C a).map f = C (f a)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma map_taylor {R S : Type*} [Semiring R] [Semiring S] (p : R[X]) (r : R) (f : R →+* S) :
    (p.taylor r).map f = (p.map f).taylor (f r) := by
  simp [taylor_apply, Polynomial.map_comp]

end Semiring

section Ring

variable {R : Type*} [Ring R]

/-
**Polynomial.taylor_injective** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：taylor_injective (r : R) : Function.Injective (taylor r)
参数：r : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `injective_iff_map_eq_zero'`：∀ {F : Type u_7} {G : Type u_8} {H : Type u_
9} [inst : AddGroup G] [inst_1 : AddZeroClass H] [inst_2 : FunLike F G H]   [Add
MonoidHomClass F…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `Polynomial.taylor_eq_zero`：taylor_eq_zero : taylor r f = 0 ↔ f = 0
-/
theorem taylor_injective (r : R) : Function.Injective (taylor r) :=
  (injective_iff_map_eq_zero' _).2 (taylor_eq_zero r)
/-
**Polynomial.taylor_inj** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ {R : Type u_1} [inst : Ring R] {r : R} {p q : Polynomial R}, (Polynomial
.taylor r) p = (Polynomial.taylor r) q ↔ p = q
参数：Polynomial.taylor r；Polynomial.taylor r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Polynomial.taylor_injective`：taylor_injective (r : R) : Function.Injecti
ve (taylor r)
-/
@[simp] lemma taylor_inj {r : R} {p q : R[X]} :
    taylor r p = taylor r q ↔ p = q := (taylor_injective r).eq_iff

end Ring

section CommSemiring

variable {R : Type*} [CommSemiring R] (r : R) (f : R[X])

@[simp]
/-
**Polynomial.taylor_mul** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：taylor_mul (p q : R[X]) : taylor r (p * q) = taylor r p * taylor r q
参数：p q : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.mul_comp`：mul_comp {R : Type*} [CommSemiring R] (p q r : R[X]
) : (p * q).comp r = p.comp r * q.comp r
-/
theorem taylor_mul (p q : R[X]) : taylor r (p * q) = taylor r p * taylor r q := mul_comp ..

/-- `Polynomial.taylor` as an `AlgHom` for commutative semirings -/
@[simps!]
/-
**Polynomial.taylorAlgHom** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：taylorAlgHom (r : R) : R[X] ->ₐ[R] R[X]
参数：r : R。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.taylor_mul`：taylor_mul (p q : R[X]) : taylor r (p * q) = tayl
or r p * taylor r q

--- 原说明 ---
`Polynomial.taylor` as an `AlgHom` for commutative semirings
-/
def taylorAlgHom (r : R) : R[X] →ₐ[R] R[X] :=
  AlgHom.ofLinearMap (taylor r) (taylor_one r) (taylor_mul r)

@[simp]
/-
**Polynomial.taylor_pow** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：taylor_pow (n : Nat) : taylor r (f ^ n) = taylor r f ^ n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.map_pow`：∀ {α : Type u_2} {β : Type u_3} [inst : Semiring α] [in
st_1 : Semiring β] (f : α →+* β) (a : α) (n : ℕ),   f (a ^ n) = f a ^ n
-/
theorem taylor_pow (n : ℕ) : taylor r (f ^ n) = taylor r f ^ n :=
  (taylorAlgHom r).map_pow ..
/-
**Polynomial.coe_taylorAlgHom** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] (r : R), ↑(Polynomial.taylorAlgHo
m r) = Polynomial.taylor r
参数：r : R；Polynomial.taylorAlgHom r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
-/
@[simp, norm_cast] lemma coe_taylorAlgHom : taylorAlgHom r = taylor r :=
  rfl
/-
**Polynomial.taylor_taylor** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：taylor_taylor (f : R[X]) (r s : R) : taylor r (taylor s f) = taylor (r + s
) f
参数：f : R[X]；r s : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.comp_assoc`：comp_assoc {R : Type*} [CommSemiring R] (φ ψ χ : 
R[X]) : (φ.comp ψ).comp χ = φ.comp (ψ.comp χ)
· 使用定理 `Polynomial.add_comp`：add_comp : (p + q).comp r = p.comp r + q.comp r
· 使用定理 `Polynomial.X_comp`：X_comp : X.comp p = p
· 使用定理 `Polynomial.C_comp`：C_comp : (C a).comp p = C a
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem taylor_taylor (f : R[X]) (r s : R) : taylor r (taylor s f) = taylor (r + s) f := by
  simp only [taylor_apply, comp_assoc, map_add, add_comp, X_comp, C_comp, add_assoc]
/-
**Polynomial.taylor_eval** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：taylor_eval (r : R) (f : R[X]) (s : R) : (taylor r f).eval s = f.eval (s +
 r)
参数：r : R；f : R[X]；s : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.eval_comp`：eval_comp : (p.comp q).eval x = p.eval (q.eval x)
· 使用定理 `Polynomial.eval_add`：eval_add : (p + q).eval x = p.eval x + q.eval x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.eval_X`：eval_X : X.eval x = x
· 使用定理 `Polynomial.eval_C`：eval_C : (C a).eval x = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem taylor_eval (r : R) (f : R[X]) (s : R) : (taylor r f).eval s = f.eval (s + r) := by
  simp only [taylor_apply, eval_comp, eval_C, eval_X, eval_add]
/-
**Polynomial.exists_mul_sq_add_linear_part_eq_eval_add** 是 Mathlib 中的一个定理，位于命名空间
 `Polynomial`。
形式化陈述：exists_mul_sq_add_linear_part_eq_eval_add (p : R[X]) (x y : R) : exists c 
: R, c * y ^ 2 + p.derivative.eval x * y + p.eval x = p.eval (x + y)
参数：p : R[X]；x y : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.eval_eq_sum_range'`：eval_eq_sum_range' {p : R[X]} {n : Nat} (
hn : p.natDegree < n) (x : R) : p.eval x = ∑ i in Finset.range n, p.coeff i * x 
^ i
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.taylor_eval`：taylor_eval (r : R) (f : R[X]) (s : R) : (taylor
 r f).eval s = f.eval (s + r)
· 使用定理 `Finset.sum_range_succ'`：∀ {M : Type u_4} [inst : AddCommMonoid M] (f : ℕ
 → M) (n : ℕ),   ∑ k ∈ Finset.range (n + 1), f k = ∑ k ∈ Finset.range n, f (k + 
1) + f 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用引理 `Finset.sum_mul`：sum_mul (s : Finset ι) (f : ι -> R) (a : R) : (∑ i in s,
 f i) * a = ∑ i in s, f i * a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Polynomial.natDegree_taylor`：natDegree_taylor (p : R[X]) (r : R) : natDe
gree (taylor r p) = natDegree p
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Polynomial.taylor_coeff_one`：taylor_coeff_one : (taylor r f).coeff 1 = f
.derivative.eval r
· 使用定理 `Polynomial.taylor_coeff_zero`：taylor_coeff_zero : (taylor r f).coeff 0 =
 f.eval r
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem exists_mul_sq_add_linear_part_eq_eval_add (p : R[X]) (x y : R) :
    ∃ c : R, c * y ^ 2 + p.derivative.eval x * y + p.eval x = p.eval (x + y) := by
  have this t :
      (taylor x p).eval t =
      ∑ i ∈ Finset.range ((taylor x p).natDegree + 2), (taylor x p).coeff i * t ^ i :=
    (taylor x p).eval_eq_sum_range' (n := (taylor x p).natDegree + 2) (by lia) t
  rw [add_comm, ← p.taylor_eval x y, this, Finset.sum_range_succ', Finset.sum_range_succ']
  use ∑ i ∈ Finset.range p.natDegree, (taylor x p).coeff (i + 2) * y ^ i
  simp [pow_succ, mul_assoc, Finset.sum_mul]
/-
**Polynomial.eval_add_of_sq_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：eval_add_of_sq_eq_zero (p : R[X]) (x y : R) (hy : y ^ 2 = 0) : p.eval (x +
 y) = p.eval x + p.derivative.eval x * y
参数：p : R[X]；x y : R；hy : y ^ 2 = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.exists_mul_sq_add_linear_part_eq_eval_add`：exists_mul_sq_add_
linear_part_eq_eval_add (p : R[X]) (x y : R) : exists c : R, c * y ^ 2 + p.deriv
ative.eval x * y + p.eval x = p.eval (x + …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
-/
theorem eval_add_of_sq_eq_zero (p : R[X]) (x y : R) (hy : y ^ 2 = 0) :
    p.eval (x + y) = p.eval x + p.derivative.eval x * y := by
  rcases exists_mul_sq_add_linear_part_eq_eval_add p x y with ⟨c, h⟩
  rw [← h, hy]; ring
/-
**Polynomial.aeval_add_of_sq_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：aeval_add_of_sq_eq_zero {S : Type*} [CommRing S] [Algebra R S] (p : R[X]) 
(x y : S) (hy : y ^ 2 = 0) : p.aeval (x + y) = p.aeval x + p.derivative.aeval x 
* y
参数：p : R[X]；x y : S；hy : y ^ 2 = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.eval_add_of_sq_eq_zero`：eval_add_of_sq_eq_zero (p : R[X]) (x 
y : R) (hy : y ^ 2 = 0) : p.eval (x + y) = p.eval x + p.derivative.eval x * y
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.derivative_map`：derivative_map [Semiring S] (p : R[X]) (f : R
 ->+* S) : derivative (p.map f) = p.derivative.map f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem aeval_add_of_sq_eq_zero {S : Type*} [CommRing S] [Algebra R S]
    (p : R[X]) (x y : S) (hy : y ^ 2 = 0) :
    p.aeval (x + y) = p.aeval x + p.derivative.aeval x * y := by
  simp only [← eval_map_algebraMap, Polynomial.eval_add_of_sq_eq_zero _ _ _ hy, derivative_map]

end CommSemiring

section CommRing

variable {R : Type*} [CommRing R] (r : R) (f : R[X])

set_option linter.style.whitespace false in -- manual alignment is not recognised
/-- `Polynomial.taylor` as an `AlgEquiv` for commutative rings. -/
/-
**Polynomial.taylorEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：taylorEquiv (r : R) : R[X] ≃ₐ[R] R[X] where invFun
参数：r : R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Polynomial.taylor` as an `AlgEquiv` for commutative rings.
-/
noncomputable def taylorEquiv (r : R) : R[X] ≃ₐ[R] R[X] where
  invFun      := taylorAlgHom (-r)
  left_inv P  := by simp [taylor, comp_assoc]
  right_inv P := by simp [taylor, comp_assoc]
  __ := taylorAlgHom r
/-
**Polynomial.toAlgHom_taylorEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] (r : R), ↑(Polynomial.taylorEquiv r) 
= Polynomial.taylorAlgHom r
参数：r : R；Polynomial.taylorEquiv r。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma toAlgHom_taylorEquiv : taylorEquiv r = taylorAlgHom r := rfl
/-
**Polynomial.coe_taylorEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] (r : R), ↑↑(Polynomial.taylorEquiv r)
 = Polynomial.taylor r
参数：r : R；Polynomial.taylorEquiv r。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_taylorEquiv : taylorEquiv r = taylor r := rfl
/-
**Polynomial.taylorEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] (r : R), (Polynomial.taylorEquiv r).s
ymm = Polynomial.taylorEquiv (-r)
参数：r : R；Polynomial.taylorEquiv r；-r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgEquiv.ext`：ext {f g : A₁ ≃ₐ[R] A₂} (h : forall a, f a = g a) : f = g
-/
@[simp] lemma taylorEquiv_symm : (taylorEquiv r).symm = taylorEquiv (-r) :=
  AlgEquiv.ext fun _ ↦ rfl
/-
**Polynomial.taylor_eval_sub** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：taylor_eval_sub (s : R) : (taylor r f).eval (s - r) = f.eval s
参数：s : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.taylor_eval`：taylor_eval (r : R) (f : R[X]) (s : R) : (taylor
 r f).eval s = f.eval (s + r)
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
-/
theorem taylor_eval_sub (s : R) :
    (taylor r f).eval (s - r) = f.eval s := by rw [taylor_eval, sub_add_cancel]

/-- Taylor's formula. -/
/-
**Polynomial.sum_taylor_eq** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：sum_taylor_eq (f : R[X]) (r : R) : ((taylor r f).sum fun i a => C a * (X -
 C r) ^ i) = f
参数：f : R[X]；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.comp_eq_sum_left`：comp_eq_sum_left : p.comp q = p.sum fun e a
 => C a * q ^ e
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Polynomial.C_neg`：C_neg : C (-a) = -C a
· 使用定理 `Polynomial.taylor_apply`：taylor_apply : taylor r f = f.comp (X + C r)
· 使用定理 `Polynomial.taylor_taylor`：taylor_taylor (f : R[X]) (r s : R) : taylor r 
(taylor s f) = taylor (r + s) f
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
· 使用定理 `Polynomial.taylor_zero`：taylor_zero (f : R[X]) : taylor 0 f = f

--- 原说明 ---
Taylor's formula.
-/
theorem sum_taylor_eq (f : R[X]) (r : R) :
    ((taylor r f).sum fun i a => C a * (X - C r) ^ i) = f := by
  rw [← comp_eq_sum_left, sub_eq_add_neg, ← C_neg, ← taylor_apply, taylor_taylor, neg_add_cancel,
    taylor_zero]

end CommRing

end Polynomial

