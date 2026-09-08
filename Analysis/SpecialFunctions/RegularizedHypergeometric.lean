/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
public import Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric

/-! # Generalized hypergeometric function

In this file we define the generalized hypergeometric function as well as the Gaussian
hypergeometric function.

The hypergeometric function is a function with parameters `a : Fin p → ℂ` and `b : Fin q → ℂ`.

Note that in this file, we use the *regularized* version of the hypergeometric function, that is
the coefficients are divides by `∏ i, Gamma (b i)`, giving in the case of the Gaussian
hypergeometric function the series representation
$$\sum_j \frac{(a)^n (b)^n}{\Gamma(c + n) n!} z^ n,$$
where `(a)^n` denotes the rising Pochhammer symbol.

This definition is valid for all values of `c`, whereas the usual hypergeometric function has a
pole for `c = -k` and `k : ℕ`. To our knowledge the regularized hypergeometric function only appears
in the literature only for the Gaussian case, it is implicit in the definition of the Bessel
function (`p = 0` and `q = 1`).
To recover the usual hypergeometric function, simply multiply by `∏ i, Gamma (b i)`.

## Definitions
For the general case we have
* `Complex.regularizedHGFunCoeff`: the coefficients
* `Complex.regularizedHGFunSeries`: the formal multilinear series
* `Complex.regularizedHGFun`: the function

For the Gaussian case (`p = 2` and `q = 1`), we define
* `Complex.regularizedGaussHGFunSeries`: the formal multilinear series
* `Complex.regularizedGaussHGFun`: the function

## Results

Convergence:
* `radius_regularizedHGFunSeries_eq_top_of_finite`: in the case that the series reduces to a
  polynomial, the radius of convergence is infinite.
* `radius_regularizedHGFunSeries_eq_top`: if `p < q + 1`, then the series has infinite convergence
  radius.
* `radius_regularizedHGFunSeries_eq_one`: if `p = q + 1`, then the series has convergence radius
  `1`.
* `Complex.radius_regularizedGaussHGFunSeries_eq_one`: the Gaussian hypergeometric series has
  convergence radius `1`.

-/

@[expose] public noncomputable section

namespace Complex

open scoped Nat Real
open Topology Filter

variable {p q : ℕ}

variable {a : Multiset ℂ} {b : Multiset ℂ} {n m : ℕ} {j k : ℂ}

/-- The coefficients of the regularized hypergeometric series. -/
/-
**Complex.regularizedHGFunCoeff** 是 Mathlib 中的一个定义，位于命名空间 `Complex`。
形式化陈述：regularizedHGFunCoeff (a : Multiset Complex) (b : Multiset Complex) (n : N
at) : Complex
参数：a : Multiset Complex；b : Multiset Complex；n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The coefficients of the regularized hypergeometric series.
-/
def regularizedHGFunCoeff (a : Multiset ℂ) (b : Multiset ℂ) (n : ℕ) : ℂ :=
  (a.map (ascPochhammer ℂ n).eval).prod / (n ! * (b.map (Gamma <| · + n)).prod)

attribute [grind .] Nat.factorial_ne_zero

@[grind =]
/-
**Complex.regularizedHGFunCoeff_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：regularizedHGFunCoeff_eq_zero_iff : regularizedHGFunCoeff a b n = 0 ↔ (exi
sts j in a, exists k < n, j = -k) ∨ exists j in b, exists (m : Nat), j + n = -m
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Complex.instNontrivial`：Nontrivial ℂ
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
-/
theorem regularizedHGFunCoeff_eq_zero_iff :
    regularizedHGFunCoeff a b n = 0 ↔
    (∃ j ∈ a, ∃ k < n, j = -k) ∨ ∃ j ∈ b, ∃ (m : ℕ), j + n = -m := by
  unfold regularizedHGFunCoeff
  simp
  grind

variable (a b n m) in
/-
**Complex.regularizedHGFunCoeff_eq_zero_right** 是 Mathlib 中的一个定理，位于命名空间 `Complex
`。
形式化陈述：regularizedHGFunCoeff_eq_zero_right (hb : -(n : Complex) - m in b
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem regularizedHGFunCoeff_eq_zero_right (hb : -(n : ℂ) - m ∈ b := by grind) :
    regularizedHGFunCoeff a b n = 0 := by grind

variable (a b n m) in
/-
**Complex.regularizedHGFunCoeff_eq_zero_left** 是 Mathlib 中的一个定理，位于命名空间 `Complex`
。
形式化陈述：regularizedHGFunCoeff_eq_zero_left (ha : -(m : Complex) in a
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem regularizedHGFunCoeff_eq_zero_left (ha : -(m : ℂ) ∈ a := by grind)
    (hm : m < n := by grind) :
  regularizedHGFunCoeff a b n = 0 := by grind

/-- Recursion formula for the coefficients of the hypergeometric series.

This is mainly used to calculate the convergence radius. -/
/-
**Complex.regularizedHGFunCoeff_add_one** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：regularizedHGFunCoeff_add_one (hb : forall k in b, k != -n) : regularizedH
GFunCoeff a b (n + 1) = regularizedHGFunCoeff a b n * ((a.map (· + (n : Complex)
)).prod / ((b.map (· + (n : Complex))).prod * (n + 1)))
参数：hb : forall k in b, k != -n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ascPochhammer_succ_right`：ascPochhammer_succ_right (n : Nat) : ascPochha
mmer S (n + 1) = ascPochhammer S n * (X + (n : S[X]))
· 使用定理 `Polynomial.eval_mul`：eval_mul : (p * q).eval x = p.eval x * q.eval x
· 使用定理 `Polynomial.eval_add`：eval_add : (p + q).eval x = p.eval x + q.eval x
· 使用定理 `Polynomial.eval_X`：eval_X : X.eval x = x
· 使用定理 `Polynomial.eval_natCast`：eval_natCast {n : Nat} : (n : R[X]).eval x = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.factorial_succ`：factorial_succ (n : Nat) : (n + 1)! = (n + 1) * n !
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `div_mul_div_comm`：div_mul_div_comm : a / b * (c / d) = a * c / (b * d)
· 使用定理 `Multiset.prod_map_mul`：prod_map_mul : (m.map fun i => f i * g i).prod = 
(m.map f).prod * (m.map g).prod
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.div_congr`：∀ {R : Type u_2} [inst : Semifield
 R] {a a' b b' c : R}, a = a' → b = b' → a' / b' = c → a / b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
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
（共 41 条，此处仅展示前 30 条）

--- 原说明 ---
Recursion formula for the coefficients of the hypergeometric series.

This is mainly used to calculate the convergence radius.
-/
theorem regularizedHGFunCoeff_add_one (hb : ∀ k ∈ b, k ≠ -n) :
    regularizedHGFunCoeff a b (n + 1) = regularizedHGFunCoeff a b n *
      ((a.map (· + (n : ℂ))).prod / ((b.map (· + (n : ℂ))).prod  * (n + 1))) := calc
  _ = (a.map fun i ↦ ((ascPochhammer ℂ n).eval i) * (i + n)).prod /
      (n ! * (n + 1) * (b.map fun j ↦ Gamma (j + n) * (j + n)).prod) := by
    unfold regularizedHGFunCoeff
    congrm ((a.map ?_).prod / (?_ * Multiset.prod ?_))
    · ext j
      simp [ascPochhammer_succ_right]
    · rw [Nat.factorial_succ]
      grind
    · refine Multiset.map_congr rfl (fun j hj ↦ ?_)
      simp only [Nat.cast_add, Nat.cast_one, ← add_assoc]
      grind
  _ = _ := by
    unfold regularizedHGFunCoeff
    simp_rw [div_mul_div_comm, Multiset.prod_map_mul]
    ring

/-- Recursion formula for the coefficients of the hypergeometric series.

This is mainly used to calculate the convergence radius. -/
/-
**Complex.regularizedHGFunCoeff_add_one_div_self** 是 Mathlib 中的一个定理，位于命名空间 `Comp
lex`。
形式化陈述：regularizedHGFunCoeff_add_one_div_self (h : regularizedHGFunCoeff a b n !=
 0) : regularizedHGFunCoeff a b (n + 1) / regularizedHGFunCoeff a b n = (a.map (
· + (n : Complex))).prod / ((b.map (· + (n : Complex))).prod * (n + 1))
参数：h : regularizedHGFunCoeff a b n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.regularizedHGFunCoeff_add_one`：regularizedHGFunCoeff_add_one (hb
 : forall k in b, k != -n) : regularizedHGFunCoeff a b (n + 1) = regularizedHGFu
nCoeff a b n * ((a.map (· +…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_eq_cancel_eq`：eq_eq_cancel_eq {M : Type*} [M
onoidWithZero M] [IsLeftCancelMulZero M] {e₁ e₂ f₁ f₂ L : M} (H₁ : e₁ = L * f₁) 
(H₂ : e₂ = L * f₂) (HL : L != …
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `instIsCancelMulZero`：∀ {G₀ : Type u_2} [inst : GroupWithZero G₀], IsCanc
elMulZero G₀
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_mul_of_eq_eq_eq_mul`：eq_mul_of_eq_eq_eq_mul 
{M : Type*} [Mul M] {a b c D e f : M} (h₁ : a = b) (h₂ : b = c) (h₃ : c = D * e)
 (h₄ : e = f) : a = D * f
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval`：div_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al / l₂.eval = l.eval) : x₁ /…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval`：mul_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al * l₂.eval = l.eval) : x₁ *…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.atom_eq_eval`：atom_eq_eval [GroupWithZero M]
 (x : M) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.FieldSimp.subst_add`：subst_add {M : Type*} [Semiring M] {
x₁ x₂ X₁ X₂ Y y a : M} (h₁ : x₁ = a * X₁) (h₂ : x₂ = a * X₂) (H_atom : X₁ + X₂ =
 Y) (hy : a * Y = y) : x…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_mul_eval_cons`：eval_mul_eval_cons [Comm
GroupWithZero M] (n : Int) (e : M) {L l l' : NF M} (h : L.eval * l.eval = l'.eva
l) : L.eval * ((n, e) ::ᵣ l).eval = …
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_div_of_eq_one_of_subst`：eq_div_of_eq_one_of_
subst {M : Type*} [DivInvOneMonoid M] {l l_n n : M} (h : l = l_n / 1) (hn : l_n 
= n) : l = n
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.cons_eq_div_of_eq_div`：cons_eq_div_of_eq_div
 [CommGroupWithZero M] (n : Int) (e : M) {t t_n t_d : NF M} (h : t.eval = t_n.ev
al / t_d.eval) : ((n, e) ::ᵣ t).eval = …
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons`：∀ {M : Type u_1} [inst : CommGrou
pWithZero M] (p : ℤ × M) (l : Mathlib.Tactic.FieldSimp.NF M),   (p ::ᵣ l).eval =
 l.eval * Mathlib.Tactic.Fi…
· 使用定理 `Mathlib.Tactic.FieldSimp.zpow'_one`：∀ {α : Type u_1} [inst : GroupWithZe
ro α] (a : α), Mathlib.Tactic.FieldSimp.zpow' a 1 = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.one_eq_eval`：one_eq_eval [GroupWithZero M] :
 (1:M) = NF.eval (M
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval₃`：mul_eq_eval₃ [CommGroupWithZer
o M] {a₁ : Int × M} (a₂ : Int × M) {l₁ l₂ l : NF M} (h : (a₁ ::ᵣ l₁).eval * l₂.e
val = l.eval) : (a₁ ::ᵣ l₁).ev…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval₃`：div_eq_eval₃ [CommGroupWithZer
o M] {a₁ : Int × M} (a₂ : Int × M) {l₁ l₂ l : NF M} (h : (a₁ ::ᵣ l₁).eval / l₂.e
val = l.eval) : (a₁ ::ᵣ l₁).ev…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval₁`：div_eq_eval₁ [CommGroupWithZer
o M] (a₁ : Int × M) {a₂ : Int × M} {l₁ l₂ l : NF M} (h : l₁.eval / (a₂ ::ᵣ l₂).e
val = l.eval) : (a₁ ::ᵣ l₁).ev…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval₂`：div_eq_eval₂ [CommGroupWithZer
o M] (r₁ r₂ : Int) (x : M) {l₁ l₂ l : NF M} (h : l₁.eval / l₂.eval = l.eval) : (
(r₁, x) ::ᵣ l₁).eval / ((r₂, x…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.one_div_eq_eval`：one_div_eq_eval [CommGroupW
ithZero M] (l : NF M) : 1 / l.eval = (l⁻¹).eval
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons_mul_eval`：eval_cons_mul_eval [Comm
GroupWithZero M] (n : Int) (e : M) {L l l' : NF M} (h : L.eval * l.eval = l'.eva
l) : ((n, e) ::ᵣ L).eval * l.eval = …
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_mul_eval_cons_zero`：eval_mul_eval_cons_
zero [CommGroupWithZero M] {e : M} {L l l' l₀ : NF M} (h : L.eval * l.eval = l'.
eval) (h' : ((0, e) ::ᵣ l).eval = l₀.eval…
（共 46 条，此处仅展示前 30 条）

--- 原说明 ---
Recursion formula for the coefficients of the hypergeometric series.

This is mainly used to calculate the convergence radius.
-/
theorem regularizedHGFunCoeff_add_one_div_self (h : regularizedHGFunCoeff a b n ≠ 0) :
    regularizedHGFunCoeff a b (n + 1) / regularizedHGFunCoeff a b n =
      (a.map (· + (n : ℂ))).prod / ((b.map (· + (n : ℂ))).prod * (n + 1)) := by
  by_cases! hb : ∀ k ∈ b, k ≠ -n
  · rw [regularizedHGFunCoeff_add_one hb]
    field_simp
  · obtain ⟨j, hj⟩ := hb
    have h₁ : (b.map (· + (n : ℂ))).prod = 0 := by
      grind [Multiset.prod_eq_zero, Multiset.mem_map]
    simp [regularizedHGFunCoeff_eq_zero_right a b n 0, h₁]
/-
**Complex.multiset_prod_eq_pow_mul_multiset_prod** 是 Mathlib 中的一个定理，位于命名空间 `Comp
lex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem multiset_prod_eq_pow_mul_multiset_prod (a : Multiset ℂ) (hn : n ≠ 0) :
    (a.map (· + (n : ℂ))).prod = n ^ a.card * (a.map (· / (n : ℂ) + 1)).prod := calc
  _ = (a.map (fun j ↦ n * (j / (n : ℂ) + 1))).prod := by
    congr; ext; field_simp
  _ = _ := by
    simp [Multiset.prod_map_mul]

private
/-
**Complex.multiset_prod_div_multiset_prod_mul** 是 Mathlib 中的一个定理，位于命名空间 `Complex
`。
形式化陈述：multiset_prod_div_multiset_prod_mul (a : Multiset Complex) (b : Multiset C
omplex) (hn : n != 0) : (a.map (· + (n : Complex))).prod / ((b.map (· + (n : Com
plex))).prod * (n + 1)) = n ^ (a.card - (b.card : Int) - 1) * (a.map (· / (n : C
omplex) + 1)).prod / ((b.map (· / (n : Complex) + 1)).prod * (1 + (n : Complex)⁻
¹))
参数：a : Multiset Complex；b : Multiset Complex；hn : n != 0。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem multiset_prod_div_multiset_prod_mul (a : Multiset ℂ) (b : Multiset ℂ) (hn : n ≠ 0) :
    (a.map (· + (n : ℂ))).prod / ((b.map (· + (n : ℂ))).prod * (n + 1)) =
      n ^ (a.card - (b.card : ℤ) - 1) * (a.map (· / (n : ℂ) + 1)).prod /
      ((b.map (· / (n : ℂ) + 1)).prod * (1 + (n : ℂ)⁻¹)) := by
  rw [multiset_prod_eq_pow_mul_multiset_prod a hn, multiset_prod_eq_pow_mul_multiset_prod b hn]
  field_simp
  congr 1
  calc
    _ = n * n ^ b.card * n ^ (a.card - b.card - (1 : ℤ)) *
        (a.map (fun x : ℂ ↦ (x + n) / n)).prod := by
      congr 1
      rw [← pow_succ', ← zpow_natCast, ← zpow_natCast, ← zpow_add' (by left; norm_cast)]
      grind
    _ = _ := by ring

variable (a b) in
/-- The regularized hypergeometric series. -/
/-
**Complex.regularizedHGFunSeries** 是 Mathlib 中的一个定义，位于命名空间 `Complex`。
形式化陈述：regularizedHGFunSeries : FormalMultilinearSeries Complex Complex Complex
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The regularized hypergeometric series.
-/
def regularizedHGFunSeries : FormalMultilinearSeries ℂ ℂ ℂ :=
  .ofScalars ℂ (regularizedHGFunCoeff a b)

@[simp]
/-
**Complex.regularizedHGFunSeries_coeff** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：regularizedHGFunSeries_coeff : (regularizedHGFunSeries a b).coeff = regula
rizedHGFunCoeff a b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `FormalMultilinearSeries.coeff_ofScalars`：coeff_ofScalars {𝕜 : Type*} [No
ntriviallyNormedField 𝕜] {p : Nat -> 𝕜} {n : Nat} : (FormalMultilinearSeries.ofS
calars 𝕜 p).coeff n = p n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem regularizedHGFunSeries_coeff :
    (regularizedHGFunSeries a b).coeff = regularizedHGFunCoeff a b := by
  unfold regularizedHGFunSeries
  ext; simp

@[simp, grind =]
/-
**Complex.regularizedHGFunSeries_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：regularizedHGFunSeries_eq_zero : regularizedHGFunSeries a b n = 0 ↔ regula
rizedHGFunCoeff a b n = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FormalMultilinearSeries.ofScalars_eq_zero`：ofScalars_eq_zero [Nontrivial
 E] (n : Nat) : ofScalars E c n = 0 ↔ c n = 0
· 使用定理 `Complex.instNontrivial`：Nontrivial ℂ
-/
theorem regularizedHGFunSeries_eq_zero :
    regularizedHGFunSeries a b n = 0 ↔ regularizedHGFunCoeff a b n = 0 := by
  apply FormalMultilinearSeries.ofScalars_eq_zero

variable (a b) in
/-- The regularized hypergeometric function. -/
/-
**Complex.regularizedHGFun** 是 Mathlib 中的一个定义，位于命名空间 `Complex`。
形式化陈述：regularizedHGFun (z : Complex) : Complex
参数：z : Complex。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The regularized hypergeometric function.
-/
def regularizedHGFun (z : ℂ) : ℂ := (regularizedHGFunSeries a b).sum z

/-- If there exists `j` and `k : ℕ`, such that `a j = -k`, then the hypergeometric series is finite
and has convergence radius `∞`. -/
/-
**Complex.radius_regularizedHGFunSeries_eq_top_of_finite** 是 Mathlib 中的一个定理，位于命名
空间 `Complex`。
形式化陈述：radius_regularizedHGFunSeries_eq_top_of_finite (ha : j in a) (hj : j = -n)
 : (regularizedHGFunSeries a b).radius = ⊤
参数：ha : j in a；hj : j = -n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FormalMultilinearSeries.radius_eq_top_of_eventually_eq_zero`：radius_eq_t
op_of_eventually_eq_zero (h : forallᶠ n in atTop, p n = 0) : p.radius = ∞
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Filter.eventually_atTop`：eventually_atTop : (forallᶠ x in atTop, p x) ↔ 
exists a, forall b, a <= b -> p b
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α

--- 原说明 ---
If there exists `j` and `k : ℕ`, such that `a j = -k`, then the hypergeometric s
eries is finite
and has convergence radius `∞`.
-/
theorem radius_regularizedHGFunSeries_eq_top_of_finite (ha : j ∈ a) (hj : j = -n) :
    (regularizedHGFunSeries a b).radius = ⊤ := by
  apply FormalMultilinearSeries.radius_eq_top_of_eventually_eq_zero
  apply eventually_atTop.mpr
  use n + 1
  grind

variable (b) in
/-- If for all `j` and `k : ℕ`, `a j ≠ -k`, then the coefficients of the hypergeometric series
are eventually non-vanishing. -/
/-
**Complex.eventually_atTop_regularizedHGFunCoeff_ne_zero** 是 Mathlib 中的一个定理，位于命名
空间 `Complex`。
形式化陈述：eventually_atTop_regularizedHGFunCoeff_ne_zero (h : forall j in a, forall 
(k : Nat), j != -↑k) : forallᶠ (n : Nat) in atTop, regularizedHGFunCoeff a b n !
= 0
参数：h : forall j in a, forall (k : Nat), j != -↑k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Filter.eventually_atTop`：eventually_atTop : (forallᶠ x in atTop, p x) ↔ 
exists a, forall b, a <= b -> p b
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Complex.regularizedHGFunCoeff_eq_zero_iff`：regularizedHGFunCoeff_eq_zero
_iff : regularizedHGFunCoeff a b n = 0 ↔ (exists j in a, exists k < n, j = -k) ∨
 exists j in b, exists (m : Nat…
· 使用定理 `Nat.le_ceil`：le_ceil (a : R) : a <= ⌈a⌉₊
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Finset.le_sup`：le_sup {b : β} (hb : b in s) : f b <= s.sup f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N

--- 原说明 ---
If for all `j` and `k : ℕ`, `a j ≠ -k`, then the coefficients of the hypergeomet
ric series
are eventually non-vanishing.
-/
theorem eventually_atTop_regularizedHGFunCoeff_ne_zero (h : ∀ j ∈ a, ∀ (k : ℕ), j ≠ -↑k) :
    ∀ᶠ (n : ℕ) in atTop, regularizedHGFunCoeff a b n ≠ 0 := by
  rw [Filter.eventually_atTop]
  use b.toFinset.sup (⌈-re ·⌉₊) + 1
  intro n hn h'
  rw [regularizedHGFunCoeff_eq_zero_iff] at h'
  rcases h' with (h' | ⟨j, hj, m, h'⟩)
  · grind
  · suffices (m : ℝ) < 0 by grind
    suffices -j.re < n by
      have h : j = -m - n := by grind
      simpa [h] using this
    calc
      -j.re ≤ ⌈-j.re⌉₊ := Nat.le_ceil (-j.re)
      _ ≤ b.toFinset.sup (⌈-re ·⌉₊) := mod_cast Finset.le_sup (by grind) (f := (⌈-re ·⌉₊))
      _ < n := by norm_cast

variable (a) in
/-
**Complex.tendsto_multiset_prod_div_add_one** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem tendsto_multiset_prod_div_add_one :
    Tendsto (fun n : ℕ ↦ (a.map (· / (n : ℂ) + 1)).prod) atTop (𝓝 1) := by
  suffices ∀ i ∈ a, Tendsto (fun n : ℕ ↦ (i / n + 1)) atTop (𝓝 <| (fun _ : _ ↦ 1) i) by
    simpa using tendsto_multiset_prod _ this
  intro i hi
  simpa using (tendsto_const_div_atTop_nhds_zero_nat i).add_const 1

variable (a b) in
/-
**Complex.tendsto_multiset_prod_div_multiset_prod_mul** 是 Mathlib 中的一个定理，位于命名空间 
`Complex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem tendsto_multiset_prod_div_multiset_prod_mul :
    Tendsto (fun n : ℕ ↦ (a.map (· / (n : ℂ) + 1)).prod /
      ((b.map (· / (n : ℂ) + 1)).prod * (1 + (n : ℂ)⁻¹))) atTop (𝓝 1) := by
  have h : Tendsto (fun n : ℕ ↦ (n : ℂ)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_nhds_zero_nat
  have := (tendsto_multiset_prod_div_add_one a).div
    ((tendsto_multiset_prod_div_add_one b).mul <| h.const_add 1) (by simp)
  simp only [add_zero, mul_one, ne_eq, one_ne_zero, not_false_eq_true, div_self] at this
  apply this.congr
  simp

/-- If `a.card ≤ b.card`, then the hypergeometric series has infinite convergence radius. -/
@[grind =]
/-
**Complex.radius_regularizedHGFunSeries_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `Comple
x`。
形式化陈述：radius_regularizedHGFunSeries_eq_top (h : a.card <= b.card) : (regularized
HGFunSeries a b).radius = ⊤
参数：h : a.card <= b.card。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.radius_regularizedHGFunSeries_eq_top_of_finite`：radius_regulariz
edHGFunSeries_eq_top_of_finite (ha : j in a) (hj : j = -n) : (regularizedHGFunSe
ries a b).radius = ⊤
· 使用定理 `FormalMultilinearSeries.ofScalars_radius_eq_top_of_tendsto`：ofScalars_ra
dius_eq_top_of_tendsto (hc : forallᶠ n in atTop, c n != 0) (hc' : Tendsto (fun n
 => ‖c n.succ‖ / ‖c n‖) atTop (𝓝 0)) : (ofScalar…
· 使用定理 `Complex.eventually_atTop_regularizedHGFunCoeff_ne_zero`：eventually_atTop
_regularizedHGFunCoeff_ne_zero (h : forall j in a, forall (k : Nat), j != -↑k) :
 forallᶠ (n : Nat) in atTop, regularizedHGFu…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Filter.Tendsto.pow`：Filter.Tendsto.pow {l : Filter α} {f : α -> M} {x : 
M} (hf : Tendsto f l (𝓝 x)) (n : Nat) : Tendsto (fun x => f x ^ n) l (𝓝 (x ^ n))
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `tendsto_one_div_atTop_nhds_zero_nat`：tendsto_one_div_atTop_nhds_zero_nat
 {𝕜 : Type*} [DivisionSemiring 𝕜] [CharZero 𝕜] [TopologicalSpace 𝕜] [ContinuousS
Mul Rat>=0 𝕜] : Tendsto (…
· 使用定理 `NNRat.instContinuousSMulOfIsScalarTowerOfRat`：∀ {R : Type u_1} [inst : T
opologicalSpace R] [inst_1 : MulAction ℚ R] [inst_2 : MulAction ℚ≥0 R] [IsScalar
Tower ℚ≥0 ℚ R]   [ContinuousSMul ℚ…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Filter.Tendsto.congr`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {l
₁ : Filter α} {l₂ : Filter β},   (∀ (x : α), f₁ x = f₂ x) → Filter.Tendsto f₁ l₁
 l₂ → Filt…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `inv_pow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℕ), a⁻¹
 ^ n = (a ^ n)⁻¹
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用定理 `Int.ofNat_sub`：∀ {m n : ℕ}, m ≤ n → ↑(n - m) = ↑n - ↑m
· 使用定理 `Int.natCast_add_one`：∀ (n : ℕ), ↑(n + 1) = ↑n + 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf'`：∀ {R : Type u_1} [inst : CommSemiri
ng R] {a a' b : R},   a = a' → ∀ {e : ℕ}, Nat.rawCast 1 = e → a' ^ e * Nat.rawCa
st 1 = b → a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
（共 72 条，此处仅展示前 30 条）

--- 原说明 ---
If `a.card ≤ b.card`, then the hypergeometric series has infinite convergence ra
dius.
-/
theorem radius_regularizedHGFunSeries_eq_top (h : a.card ≤ b.card) :
    (regularizedHGFunSeries a b).radius = ⊤ := by
  by_cases! ha : ∃ j ∈ a, ∃ k : ℕ, j = -k
  · obtain ⟨j, hj, k, ha⟩ := ha
    apply radius_regularizedHGFunSeries_eq_top_of_finite hj ha
  apply FormalMultilinearSeries.ofScalars_radius_eq_top_of_tendsto
  · apply eventually_atTop_regularizedHGFunCoeff_ne_zero b ha
  · simp only [Nat.succ_eq_add_one]
    have h₁ : Tendsto (fun (n : ℕ) ↦ (n : ℂ) ^ (a.card - (b.card : ℤ) - 1)) atTop (𝓝 0) := by
      have := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℂ)).pow (b.card + 1 - a.card)
      rw [zero_pow (by grind)] at this
      apply this.congr
      intro n
      rw [one_div, inv_pow, ← zpow_natCast, ← zpow_neg, Int.ofNat_sub (by grind),
        Int.natCast_add_one]
      ring_nf
    have := (h₁.mul (tendsto_multiset_prod_div_multiset_prod_mul a b)).norm
    simp only [mul_one, norm_zero] at this
    apply this.congr'
    have h_ne := eventually_atTop_regularizedHGFunCoeff_ne_zero b ha
    filter_upwards [h_ne, Filter.eventually_ne_atTop 0] with n hn₁ hn₂
    rw [← Complex.norm_div, regularizedHGFunCoeff_add_one_div_self hn₁,
      multiset_prod_div_multiset_prod_mul a b hn₂, mul_div]

/-- If `a.card = b.card + 1`, then the hypergeometric series has convergence radius `1`, unless it
is a polynomial. -/
@[grind =]
/-
**Complex.radius_regularizedHGFunSeries_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Comple
x`。
形式化陈述：radius_regularizedHGFunSeries_eq_one (h : a.card = b.card + 1) (h' : foral
l j in a, forall k : Nat, j != -k) : (regularizedHGFunSeries a b).radius = 1
参数：h : a.card = b.card + 1；h' : forall j in a, forall k : Nat, j != -k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.norm`：∀ {α : Type u_1} {E : Type u_4} [inst : SeminormedA
ddGroup E] {a : E} {l : Filter α} {f : α → E},   Filter.Tendsto f l (nhds a) → F
ilter.Ten…
· 使用定理 `_private.Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric.0.C
omplex.tendsto_multiset_prod_div_multiset_prod_mul`：∀ (a b : Multiset ℂ),   Filt
er.Tendsto     (fun n =>       (Multiset.map (fun x => x / ↑n + 1) a).prod / ((M
ultiset.map (fun x => x / ↑n + 1…
· 使用定理 `Filter.Tendsto.congr'`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {
l₁ : Filter α} {l₂ : Filter β},   f₁ =ᶠ[l₁] f₂ → Filter.Tendsto f₁ l₁ l₂ → Filte
r.Tendsto f…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `Complex.eventually_atTop_regularizedHGFunCoeff_ne_zero`：eventually_atTop
_regularizedHGFunCoeff_ne_zero (h : forall j in a, forall (k : Nat), j != -↑k) :
 forallᶠ (n : Nat) in atTop, regularizedHGFu…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.eventually_ne_atTop`：eventually_ne_atTop [Preorder α] [NoTopOrder
 α] (a : α) : forallᶠ x in atTop, x != a
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `norm_div`：norm_div (a b : α) : ‖a / b‖ = ‖a‖ / ‖b‖
· 使用定理 `Complex.norm_mul`：∀ (z w : ℂ), ‖z * w‖ = ‖z‖ * ‖w‖
· 使用定理 `Complex.regularizedHGFunCoeff_add_one_div_self`：regularizedHGFunCoeff_ad
d_one_div_self (h : regularizedHGFunCoeff a b n != 0) : regularizedHGFunCoeff a 
b (n + 1) / regularizedHGFunCoeff a …
· 使用定理 `_private.Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric.0.C
omplex.multiset_prod_div_multiset_prod_mul`：∀ {n : ℕ} (a b : Multiset ℂ),   n ≠ 
0 →     (Multiset.map (fun x => x + ↑n) a).prod / ((Multiset.map (fun x => x + ↑
n) b).prod * (↑n + 1)) =…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用引理 `zpow_ofNat`：zpow_ofNat (a : G) (n : Nat) : a ^ (ofNat(n) : Int) = a ^ Of
Nat.ofNat n
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `FormalMultilinearSeries.ofScalars_radius_eq_inv_of_tendsto`：ofScalars_ra
dius_eq_inv_of_tendsto [NormOneClass E] {r : Real>=0} (hr : r != 0) (hc : Tendst
o (fun n => ‖c n.succ‖ / ‖c n‖) atTop (𝓝 r)) : (…
· 使用定理 `NNReal.instNontrivial`：Nontrivial NNReal
（共 32 条，此处仅展示前 30 条）

--- 原说明 ---
If `a.card = b.card + 1`, then the hypergeometric series has convergence radius 
`1`, unless it
is a polynomial.
-/
theorem radius_regularizedHGFunSeries_eq_one (h : a.card = b.card + 1)
    (h' : ∀ j ∈ a, ∀ k : ℕ, j ≠ -k) :
    (regularizedHGFunSeries a b).radius = 1 := by
  have : Tendsto (fun n ↦ ‖regularizedHGFunCoeff a b n.succ‖ / ‖regularizedHGFunCoeff a b n‖) atTop
      (𝓝 1) := by
    have := (tendsto_multiset_prod_div_multiset_prod_mul a b).norm
    simp only [norm_one] at this
    apply this.congr'
    have h_ne := eventually_atTop_regularizedHGFunCoeff_ne_zero b h'
    filter_upwards [h_ne, Filter.eventually_ne_atTop 0] with n hn₁ hn₂
    simp [Nat.succ_eq_add_one, ← Complex.norm_div, regularizedHGFunCoeff_add_one_div_self hn₁,
      multiset_prod_div_multiset_prod_mul a b hn₂, h]
  have := FormalMultilinearSeries.ofScalars_radius_eq_inv_of_tendsto (r := 1) ℂ _ (by simp) this
  simpa

/-- If `a.card = b.card + 1`, then the hypergeometric series has convergence radius greater or equal
to `1`. -/
/-
**Complex.radius_regularizedHGFunSeries_ge_one** 是 Mathlib 中的一个定理，位于命名空间 `Comple
x`。
形式化陈述：radius_regularizedHGFunSeries_ge_one (h : a.card = b.card + 1) : 1 <= (reg
ularizedHGFunSeries a b).radius
参数：h : a.card = b.card + 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Complex.radius_regularizedHGFunSeries_eq_top_of_finite`：radius_regulariz
edHGFunSeries_eq_top_of_finite (ha : j in a) (hj : j = -n) : (regularizedHGFunSe
ries a b).radius = ⊤
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p

--- 原说明 ---
If `a.card = b.card + 1`, then the hypergeometric series has convergence radius 
greater or equal
to `1`.
-/
theorem radius_regularizedHGFunSeries_ge_one (h : a.card = b.card + 1) :
    1 ≤ (regularizedHGFunSeries a b).radius := by
  by_cases! h' : ∀ j ∈ a, ∀ k : ℕ, j ≠ -k
  · grind
  · obtain ⟨j, hj, k, h'⟩ := h'
    rw [radius_regularizedHGFunSeries_eq_top_of_finite hj h']
    simp

section ZeroZero

/-- The regularized hypergeometric series with `a = b = 0` is exponential series. -/
@[simp, grind =]
/-
**Complex.regularizedHGFunSeries_zero_zero** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：regularizedHGFunSeries_zero_zero : regularizedHGFunSeries 0 0 = NormedSpac
e.expSeries Complex Complex
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FormalMultilinearSeries.ext`：∀ {𝕜 : Type u} {E : Type v} {F : Type w} [i
nst : Semiring 𝕜] [inst_1 : AddCommMonoid E] [inst_2 : _root_.Module 𝕜 E]   [ins
t_3 : Topological…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `ContinuousMultilinearMap.ext_ring`：ext_ring [Finite ι] [TopologicalSpace
 R] ⦃f g : ContinuousMultilinearMap R (fun _ : ι => R) M₂⦄ (h : f (fun _ => 1) =
 g (fun _ => 1)) : f = …
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FormalMultilinearSeries.apply_eq_prod_smul_coeff`：apply_eq_prod_smul_coe
ff : p n y = (∏ i, y i) • p.coeff n
· 使用定理 `Finset.prod_const_one`：prod_const_one : (∏ _x in s, (1 : M)) = 1
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Complex.regularizedHGFunSeries_coeff`：regularizedHGFunSeries_coeff : (re
gularizedHGFunSeries a b).coeff = regularizedHGFunCoeff a b
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `ContinuousMultilinearMap.instIsSMulApplyForall`：∀ {ι : Type v} {M₁ : ι →
 Type w₁} {M₂ : Type w₂} [inst : (i : ι) → AddCommMonoid (M₁ i)] [inst_1 : AddCo
mmMonoid M₂]   [inst_2 : (i : ι) → T…
· 使用定理 `List.ofFn_const`：∀ {α : Type u} (n : ℕ) (c : α), (List.ofFn fun x => c) 
= List.replicate n c
· 使用定理 `List.prod_replicate`：prod_replicate (n : Nat) (a : M) : (replicate n a).
prod = a ^ n
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The regularized hypergeometric series with `a = b = 0` is exponential series.
-/
theorem regularizedHGFunSeries_zero_zero :
    regularizedHGFunSeries 0 0 = NormedSpace.expSeries ℂ ℂ := by
  ext n
  simp [regularizedHGFunCoeff, NormedSpace.expSeries]

/-- The regularized hypergeometric function `₀F₀` is the complex exponential. -/
@[simp, grind =]
/-
**Complex.regularizedHGFun_zero_zero** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：regularizedHGFun_zero_zero : regularizedHGFun 0 0 = exp
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.exp_eq_exp_ℂ`：Complex.exp = NormedSpace.exp
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `SMulCommClass.continuousConstSMul`：∀ {R : Type u_6} {A : Type u_7} [inst
 : Monoid A] [inst_1 : SMul R A] [SMulCommClass R A A]   [inst_3 : TopologicalSp
ace A] [SeparatelyConti…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `NormedSpace.exp_eq_expSeries_sum`：exp_eq_expSeries_sum [CharZero 𝕂] : ex
p = (expSeries 𝕂 𝔸).sum
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Complex.regularizedHGFunSeries_zero_zero`：regularizedHGFunSeries_zero_ze
ro : regularizedHGFunSeries 0 0 = NormedSpace.expSeries Complex Complex
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The regularized hypergeometric function `₀F₀` is the complex exponential.
-/
theorem regularizedHGFun_zero_zero : regularizedHGFun 0 0 = exp := by
  rw [exp_eq_exp_ℂ, NormedSpace.exp_eq_expSeries_sum (𝕂 := ℂ)]
  unfold regularizedHGFun
  simp

end ZeroZero

section Gaussian

/-- The regularized Gaussian hypergeometric function. -/
/-
**Complex.regularizedGaussHGFunSeries** 是 Mathlib 中的一个定义，位于命名空间 `Complex`。
形式化陈述：regularizedGaussHGFunSeries (a b c : Complex) : FormalMultilinearSeries Co
mplex Complex Complex
参数：a b c : Complex。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The regularized Gaussian hypergeometric function.
-/
def regularizedGaussHGFunSeries (a b c : ℂ) : FormalMultilinearSeries ℂ ℂ ℂ :=
  regularizedHGFunSeries {a, b} {c}

/-- The regularized Gaussian hypergeometric function. -/
/-
**Complex.regularizedGaussHGFun** 是 Mathlib 中的一个定义，位于命名空间 `Complex`。
形式化陈述：regularizedGaussHGFun (a b c z : Complex) : Complex
参数：a b c z : Complex。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The regularized Gaussian hypergeometric function.
-/
def regularizedGaussHGFun (a b c z : ℂ) : ℂ :=
  (regularizedGaussHGFunSeries a b c).sum z

variable {a b c z : ℂ}

variable (a b c) in
/-
**Complex.regularizedGaussHGFunSeries_symm** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：regularizedGaussHGFunSeries_symm : regularizedGaussHGFunSeries a b c = reg
ularizedGaussHGFunSeries b a c
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.pair_comm`：pair_comm (x y : α) : ({x, y} : Multiset α) = {y, x}
-/
theorem regularizedGaussHGFunSeries_symm :
    regularizedGaussHGFunSeries a b c = regularizedGaussHGFunSeries b a c := by
  unfold regularizedGaussHGFunSeries
  rw [Multiset.pair_comm]

variable (a b c) in
/-
**Complex.regularizedGaussHGFun_symm** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：regularizedGaussHGFun_symm : regularizedGaussHGFun a b c = regularizedGaus
sHGFun b a c
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `Complex.regularizedGaussHGFunSeries_symm`：regularizedGaussHGFunSeries_sy
mm : regularizedGaussHGFunSeries a b c = regularizedGaussHGFunSeries b a c
-/
theorem regularizedGaussHGFun_symm :
    regularizedGaussHGFun a b c = regularizedGaussHGFun b a c := by
  unfold regularizedGaussHGFun
  rw [regularizedGaussHGFunSeries_symm]
/-
**Complex.coeff_regularizedGaussHGFunSeries** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：coeff_regularizedGaussHGFunSeries : (a.regularizedGaussHGFunSeries b c).co
eff n = ((ascPochhammer Complex n).eval a * (ascPochhammer Complex n).eval b) / 
(n ! * Gamma (c + n))
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
· 使用定理 `Complex.regularizedHGFunSeries_coeff`：regularizedHGFunSeries_coeff : (re
gularizedHGFunSeries a b).coeff = regularizedHGFunCoeff a b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Multiset.map_cons`：map_cons (f : α -> β) (a s) : map f (a ::ₘ s) = f a :
:ₘ map f s
· 使用定理 `Multiset.prod_cons`：prod_cons (a : M) (s) : prod (a ::ₘ s) = a * prod s
· 使用定理 `Multiset.prod_singleton`：prod_singleton (a : M) : prod {a} = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coeff_regularizedGaussHGFunSeries :
    (a.regularizedGaussHGFunSeries b c).coeff n =
    ((ascPochhammer ℂ n).eval a * (ascPochhammer ℂ n).eval b) / (n ! * Gamma (c + n)) := by
  simp [regularizedGaussHGFunSeries, regularizedHGFunCoeff]
/-
**Complex.Gamma_inv_mul_ordinaryHypergeometricSeries_eq** 是 Mathlib 中的一个定理，位于命名空
间 `Complex`。
形式化陈述：Gamma_inv_mul_ordinaryHypergeometricSeries_eq (hc : forall k : Nat, c != -
k) {n : Nat} : (Gamma c)⁻¹ * (ordinaryHypergeometricSeries Complex a b c).coeff 
n = (a.regularizedGaussHGFunSeries b c).coeff n
参数：hc : forall k : Nat, c != -k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.coeff_regularizedGaussHGFunSeries`：coeff_regularizedGaussHGFunSe
ries : (a.regularizedGaussHGFunSeries b c).coeff n = ((ascPochhammer Complex n).
eval a * (ascPochhammer Complex…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `SMulCommClass.continuousConstSMul`：∀ {R : Type u_6} {A : Type u_7} [inst
 : Monoid A] [inst_1 : SMul R A] [SMulCommClass R A A]   [inst_3 : TopologicalSp
ace A] [SeparatelyConti…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `ordinaryHypergeometricSeries.eq_1`：∀ {𝕂 : Type u_1} (𝔸 : Type u_2) [inst
 : Field 𝕂] [inst_1 : Ring 𝔸] [inst_2 : Algebra 𝕂 𝔸] [inst_3 : TopologicalSpace 
𝔸]   [inst_4 : IsTopolo…
· 使用引理 `FormalMultilinearSeries.coeff_ofScalars`：coeff_ofScalars {𝕜 : Type*} [No
ntriviallyNormedField 𝕜] {p : Nat -> 𝕜} {n : Nat} : (FormalMultilinearSeries.ofS
calars 𝕜 p).coeff n = p n
· 使用定理 `ordinaryHypergeometricCoefficient.eq_1`：∀ {𝕂 : Type u_1} [inst : Field 𝕂
] (a b c : 𝕂) (n : ℕ),   ordinaryHypergeometricCoefficient a b c n =     (↑n.fac
torial)⁻¹ * Polynomial.eval …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.Gamma_add_nat_div_Gamma_eq`：Gamma_add_nat_div_Gamma_eq {n : Nat}
 (z : Complex) (hz : forall k : Nat, z != -k) : Gamma (z + n) / Gamma z = (ascPo
chhammer Complex n).eval…
-/
theorem Gamma_inv_mul_ordinaryHypergeometricSeries_eq (hc : ∀ k : ℕ, c ≠ -k) {n : ℕ} :
    (Gamma c)⁻¹ * (ordinaryHypergeometricSeries ℂ a b c).coeff n =
      (a.regularizedGaussHGFunSeries b c).coeff n := by
  rw [coeff_regularizedGaussHGFunSeries, ordinaryHypergeometricSeries,
    FormalMultilinearSeries.coeff_ofScalars, ordinaryHypergeometricCoefficient,
    ← Gamma_add_nat_div_Gamma_eq c hc]
  grind
/-
**Complex.ordinaryHypergeometric_div_Gamma_eq** 是 Mathlib 中的一个定理，位于命名空间 `Complex
`。
形式化陈述：ordinaryHypergeometric_div_Gamma_eq (hc : forall k : Nat, c != -k) : ordin
aryHypergeometric a b c z / Gamma c = regularizedGaussHGFun a b c z
参数：hc : forall k : Nat, c != -k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.regularizedGaussHGFun.eq_1`：∀ (a b c z : ℂ), a.regularizedGaussH
GFun b c z = (a.regularizedGaussHGFunSeries b c).sum z
· 使用定理 `ordinaryHypergeometric.eq_1`：∀ {𝕂 : Type u_1} {𝔸 : Type u_2} [inst : Fie
ld 𝕂] [inst_1 : Ring 𝔸] [inst_2 : Algebra 𝕂 𝔸] [inst_3 : TopologicalSpace 𝔸]   [
inst_4 : IsTopolo…
· 使用定理 `div_eq_inv_mul`：div_eq_inv_mul : a / b = b⁻¹ * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `FormalMultilinearSeries.const_smul_sum_apply`：const_smul_sum_apply [T2Sp
ace F] (a : 𝕜') (f : FormalMultilinearSeries 𝕜 E F) (z : E) : a • f.sum z = (a •
 f).sum z
· 使用定理 `Complex.instT2Space`：T2Space ℂ
· 使用定理 `FormalMultilinearSeries.ext`：∀ {𝕜 : Type u} {E : Type v} {F : Type w} [i
nst : Semiring 𝕜] [inst_1 : AddCommMonoid E] [inst_2 : _root_.Module 𝕜 E]   [ins
t_3 : Topological…
· 使用定理 `ContinuousMultilinearMap.ext_ring`：ext_ring [Finite ι] [TopologicalSpace
 R] ⦃f g : ContinuousMultilinearMap R (fun _ : ι => R) M₂⦄ (h : f (fun _ => 1) =
 g (fun _ => 1)) : f = …
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `ContinuousMultilinearMap.instIsSMulApplyForall`：∀ {ι : Type v} {M₁ : ι →
 Type w₁} {M₂ : Type w₂} [inst : (i : ι) → AddCommMonoid (M₁ i)] [inst_1 : AddCo
mmMonoid M₂]   [inst_2 : (i : ι) → T…
· 使用定理 `FormalMultilinearSeries.apply_eq_prod_smul_coeff`：apply_eq_prod_smul_coe
ff : p n y = (∏ i, y i) • p.coeff n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.prod_const_one`：prod_const_one : (∏ _x in s, (1 : M)) = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Complex.Gamma_inv_mul_ordinaryHypergeometricSeries_eq`：Gamma_inv_mul_ord
inaryHypergeometricSeries_eq (hc : forall k : Nat, c != -k) {n : Nat} : (Gamma c
)⁻¹ * (ordinaryHypergeometricSeries Complex…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ordinaryHypergeometric_div_Gamma_eq (hc : ∀ k : ℕ, c ≠ -k) :
    ordinaryHypergeometric a b c z / Gamma c = regularizedGaussHGFun a b c z := by
  rw [regularizedGaussHGFun, ordinaryHypergeometric, div_eq_inv_mul, ← smul_eq_mul,
    FormalMultilinearSeries.const_smul_sum_apply]
  congr
  ext n
  simp [Gamma_inv_mul_ordinaryHypergeometricSeries_eq hc]

variable (b c) in
@[simp]
/-
**Complex.radius_regularizedGaussHGFunSeries_eq_top_of_left** 是 Mathlib 中的一个定理，位
于命名空间 `Complex`。
形式化陈述：radius_regularizedGaussHGFunSeries_eq_top_of_left (k : Nat) : (regularized
GaussHGFunSeries (-k) b c).radius = ⊤
参数：k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.radius_regularizedHGFunSeries_eq_top_of_finite`：radius_regulariz
edHGFunSeries_eq_top_of_finite (ha : j in a) (hj : j = -n) : (regularizedHGFunSe
ries a b).radius = ⊤
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
-/
theorem radius_regularizedGaussHGFunSeries_eq_top_of_left (k : ℕ) :
    (regularizedGaussHGFunSeries (-k) b c).radius = ⊤ :=
  radius_regularizedHGFunSeries_eq_top_of_finite (j := -(k : ℂ)) (by simp) rfl

variable (a c) in
@[simp]
/-
**Complex.radius_regularizedGaussHGFunSeries_eq_top_of_right** 是 Mathlib 中的一个定理，
位于命名空间 `Complex`。
形式化陈述：radius_regularizedGaussHGFunSeries_eq_top_of_right (k : Nat) : (regularize
dGaussHGFunSeries a (-k) c).radius = ⊤
参数：k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.radius_regularizedHGFunSeries_eq_top_of_finite`：radius_regulariz
edHGFunSeries_eq_top_of_finite (ha : j in a) (hj : j = -n) : (regularizedHGFunSe
ries a b).radius = ⊤
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
-/
theorem radius_regularizedGaussHGFunSeries_eq_top_of_right (k : ℕ) :
    (regularizedGaussHGFunSeries a (-k) c).radius = ⊤ :=
  radius_regularizedHGFunSeries_eq_top_of_finite (j := -(k : ℂ)) (by simp) rfl

variable (c) in
@[grind =]
/-
**Complex.radius_regularizedGaussHGFunSeries_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `C
omplex`。
形式化陈述：radius_regularizedGaussHGFunSeries_eq_one (h : forall k : Nat, a != -k ∧ b
 != -k) : (regularizedGaussHGFunSeries a b c).radius = 1
参数：h : forall k : Nat, a != -k ∧ b != -k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.radius_regularizedHGFunSeries_eq_one`：radius_regularizedHGFunSer
ies_eq_one (h : a.card = b.card + 1) (h' : forall j in a, forall k : Nat, j != -
k) : (regularizedHGFunSeries a b).…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem radius_regularizedGaussHGFunSeries_eq_one (h : ∀ k : ℕ, a ≠ -k ∧ b ≠ -k) :
    (regularizedGaussHGFunSeries a b c).radius = 1 :=
  radius_regularizedHGFunSeries_eq_one rfl (by simp; grind)

variable (a b c) in
/-
**Complex.radius_regularizedGaussHGFunSeries_ge_one** 是 Mathlib 中的一个定理，位于命名空间 `C
omplex`。
形式化陈述：radius_regularizedGaussHGFunSeries_ge_one : 1 <= (regularizedGaussHGFunSer
ies a b c).radius
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.radius_regularizedHGFunSeries_ge_one`：radius_regularizedHGFunSer
ies_ge_one (h : a.card = b.card + 1) : 1 <= (regularizedHGFunSeries a b).radius
-/
theorem radius_regularizedGaussHGFunSeries_ge_one :
    1 ≤ (regularizedGaussHGFunSeries a b c).radius :=
  radius_regularizedHGFunSeries_ge_one rfl

end Gaussian

end Complex

