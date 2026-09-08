/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Analysis.Convex.Gauge
public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.RingTheory.Polynomial.Bernstein
public import Mathlib.Topology.Algebra.Module.LocallyConvex
public import Mathlib.Topology.ContinuousMap.Polynomial

/-!
# Bernstein approximations and Weierstrass' theorem

We prove that the Bernstein approximations
```
∑ k : Fin (n+1), (n.choose k * x^k * (1-x)^(n-k)) • f (k/n : ℝ)
```
for a continuous function `f : C([0,1], E)` taking values in a locally convex vector space
converge uniformly to `f` as `n` tends to infinity.
This statement directly applies to the cases when the codomain is a (semi)normed space
or, more generally, has a topology defined by a family of seminorms.

Our proof follows [Richard Beals' *Analysis, an introduction*][beals-analysis], §7D.
The original proof, due to [Bernstein](bernstein1912) in 1912, is probabilistic,
and relies on Bernoulli's theorem,
which gives bounds for how quickly the observed frequencies in a
Bernoulli trial approach the underlying probability.

The proof here does not directly rely on Bernoulli's theorem,
but can also be given a probabilistic account.
* Consider a weighted coin which with probability `x` produces heads,
  and with probability `1-x` produces tails.
* The value of `bernstein n k x` is the probability that
  such a coin gives exactly `k` heads in a sequence of `n` tosses.
* If such an appearance of `k` heads results in a payoff of `f(k / n)`,
  the `n`-th Bernstein approximation for `f` evaluated at `x` is the expected payoff.
* The main estimate in the proof bounds the probability that
  the observed frequency of heads differs from `x` by more than some `δ`,
  obtaining a bound of `(4 * n * δ^2)⁻¹`, irrespective of `x`.
* This ensures that for `n` large, the Bernstein approximation is (uniformly) close to the
  payoff function `f`.

(You don't need to think in these terms to follow the proof below: it's a giant `calc` block!)

This result proves Weierstrass' theorem that polynomials are dense in `C([0,1], ℝ)`,
although we defer an abstract statement of this until later.
-/

@[expose] public section

noncomputable section

open Filter
open scoped unitInterval Topology Uniformity

/-- The Bernstein polynomials, as continuous functions on `[0,1]`.
-/
/-
**bernstein** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：bernstein (n ν : Nat) : C(I, Real)
参数：n ν : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Bernstein polynomials, as continuous functions on `[0,1]`.
-/
def bernstein (n ν : ℕ) : C(I, ℝ) :=
  (bernsteinPolynomial ℝ n ν).toContinuousMapOn I
/-
**bernstein_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：bernstein_apply (n ν : Nat) (x : I) : bernstein n ν x = (n.choose ν : Real
) * (x : Real) ^ ν * (1 - (x : Real)) ^ (n - ν)
参数：n ν : Nat；x : I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Polynomial.eval_mul`：eval_mul : (p * q).eval x = p.eval x * q.eval x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.eval_natCast`：eval_natCast {n : Nat} : (n : R[X]).eval x = n
· 使用定理 `Polynomial.eval_pow`：eval_pow (n : Nat) : (p ^ n).eval x = p.eval x ^ n
· 使用定理 `Polynomial.eval_X`：eval_X : X.eval x = x
· 使用定理 `Polynomial.eval_sub`：eval_sub (p q : R[X]) (x : R) : (p - q).eval x = p.
eval x - q.eval x
· 使用定理 `Polynomial.eval_one`：eval_one : (1 : R[X]).eval x = 1
· 使用定理 `ContinuousMap.mk.congr_simp`：∀ {X : Type u_1} {Y : Type u_2} [inst : Top
ologicalSpace X] [inst_1 : TopologicalSpace Y] (toFun toFun_1 : X → Y)   (e_toFu
n : toFun = toFun…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem bernstein_apply (n ν : ℕ) (x : I) :
    bernstein n ν x = (n.choose ν : ℝ) * (x : ℝ) ^ ν * (1 - (x : ℝ)) ^ (n - ν) := by
  dsimp [bernstein, Polynomial.toContinuousMapOn, Polynomial.toContinuousMap, bernsteinPolynomial]
  simp

@[simp]
/-
**bernstein_nonneg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：bernstein_nonneg {n ν : Nat} {x : I} : 0 <= bernstein n ν x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `bernstein_apply`：bernstein_apply (n ν : Nat) (x : I) : bernstein n ν x =
 (n.choose ν : Real) * (x : Real) ^ ν * (1 - (x : Real)) ^ (n - ν)
· 使用定理 `unitInterval.nonneg`：nonneg (x : I) : 0 <= (x : Real)
· 使用定理 `unitInterval.one_minus_nonneg`：one_minus_nonneg (x : I) : 0 <= 1 - (x : 
Real)
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `Nat.cast_nonneg'`：cast_nonneg' (n : Nat) : 0 <= (n : α)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `pow_nonneg`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : Preor
der M₀] {a : M₀} [ZeroLEOneClass M₀] [PosMulMono M₀],   0 ≤ a → ∀ (n : ℕ), 0 ≤ a
…
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
-/
theorem bernstein_nonneg {n ν : ℕ} {x : I} : 0 ≤ bernstein n ν x := by
  simp only [bernstein_apply]
  have h₁ : (0 : ℝ) ≤ x := by unit_interval
  have h₂ : (0 : ℝ) ≤ 1 - x := by unit_interval
  positivity

namespace Mathlib.Meta.Positivity

open Lean Meta Qq Function

/-- Extension of the `positivity` tactic for Bernstein polynomials: they are always non-negative. -/
@[positivity DFunLike.coe (bernstein _ _) _]
meta def evalBernstein : PositivityExt where eval {_ _} _zα pα? e :=
  match pα? with | none => pure .none | some _ => do
  let .app (.app _coe (.app (.app _ n) ν)) x ← whnfR e | throwError "not bernstein polynomial"
  let p ← mkAppOptM ``bernstein_nonneg #[n, ν, x]
  pure (.nonnegative p)

end Mathlib.Meta.Positivity

/-!
We now give a slight reformulation of `bernsteinPolynomial.variance`.
-/


namespace bernstein

/-- Send `k : Fin (n+1)` to the equally spaced points `k/n` in the unit interval.
-/
/-
**bernstein.z** 是 Mathlib 中的一个定义，位于命名空间 `bernstein`。
形式化陈述：z {n : Nat} (k : Fin (n + 1)) : I
参数：k : Fin (n + 1)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Send `k : Fin (n+1)` to the equally spaced points `k/n` in the unit interval.
-/
def z {n : ℕ} (k : Fin (n + 1)) : I :=
  ⟨(k : ℝ) / n, by simp [div_nonneg, div_le_one_of_le₀, k.is_le]⟩

local postfix:90 "/ₙ" => z
/-
**bernstein.z_zero** 是 Mathlib 中的一个定理，位于命名空间 `bernstein`。
形式化陈述：∀ {n : ℕ}, bernstein.z 0 = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma z_zero {n : ℕ} : (0 : Fin (n + 1))/ₙ = 0 := by simp [z]
/-
**bernstein.z_last** 是 Mathlib 中的一个定理，位于命名空间 `bernstein`。
形式化陈述：∀ {n : ℕ}, n ≠ 0 → bernstein.z (Fin.last n) = 1
参数：Fin.last n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma z_last {n : ℕ} (hn : n ≠ 0) : .last n/ₙ = 1 := by simp [z, hn]

@[simp]
/-
**bernstein.probability** 是 Mathlib 中的一个定理，位于命名空间 `bernstein`。
形式化陈述：probability (n : Nat) (x : I) : (∑ k : Fin (n + 1), bernstein n k x) = 1
参数：n : Nat；x : I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `bernsteinPolynomial.sum`：sum (n : Nat) : (∑ ν in Finset.range (n + 1), b
ernsteinPolynomial R n ν) = 1
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_range`：∀ {M : Type u_2} [inst : AddCommMonoid M] {n : ℕ} (f :
 ℕ → M), ∑ i ∈ Finset.range n, f i = ∑ i, f ↑i
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `Polynomial.eval_one`：eval_one : (1 : R[X]).eval x = 1
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem probability (n : ℕ) (x : I) : (∑ k : Fin (n + 1), bernstein n k x) = 1 := by
  have := bernsteinPolynomial.sum ℝ n
  apply_fun fun p => Polynomial.aeval (x : ℝ) p at this
  simpa [Finset.sum_range]
/-
**bernstein.variance** 是 Mathlib 中的一个定理，位于命名空间 `bernstein`。
形式化陈述：variance {n : Nat} (hn : n != 0) (x : I) : (∑ k : Fin (n + 1), (x - k/ₙ : 
Real) ^ 2 * bernstein n k x) = (x : Real) * (1 - x) / n
参数：hn : n != 0；x : I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `bernstein_apply`：bernstein_apply (n ν : Nat) (x : I) : bernstein n ν x =
 (n.choose ν : Real) * (x : Real) ^ ν * (1 - (x : Real)) ^ (n - ν)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `Finset.sum_range`：∀ {M : Type u_2} [inst : AddCommMonoid M] {n : ℕ} (f :
 ℕ → M), ∑ i ∈ Finset.range n, f i = ∑ i, f ↑i
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `Polynomial.eval_mul`：eval_mul : (p * q).eval x = p.eval x * q.eval x
· 使用定理 `Polynomial.eval_pow`：eval_pow (n : Nat) : (p ^ n).eval x = p.eval x ^ n
· 使用定理 `Polynomial.eval_sub`：eval_sub (p q : R[X]) (x : R) : (p - q).eval x = p.
eval x - q.eval x
· 使用定理 `Polynomial.eval_natCast`：eval_natCast {n : Nat} : (n : R[X]).eval x = n
· 使用定理 `Polynomial.eval_X`：eval_X : X.eval x = x
· 使用定理 `Polynomial.eval_one`：eval_one : (1 : R[X]).eval x = 1
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
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval`：mul_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al * l₂.eval = l.eval) : x₁ *…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.pow_eq_eval`：pow_eq_eval [CommGroupWithZero 
M] {l : NF M} {r : Nat} (hr : r != 0) {x : M} (hx : x = l.eval) : x ^ r = (l ^ r
).eval
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
（共 99 条，此处仅展示前 30 条）
-/
theorem variance {n : ℕ} (hn : n ≠ 0) (x : I) :
    (∑ k : Fin (n + 1), (x - k/ₙ : ℝ) ^ 2 * bernstein n k x) = (x : ℝ) * (1 - x) / n := by
  convert! congr(Polynomial.aeval (x : ℝ) $(bernsteinPolynomial.variance ℝ n) / n ^ 2) using 1
  · simp only [z, bernstein_apply, nsmul_eq_mul, bernsteinPolynomial, Finset.sum_range, map_sum,
      Polynomial.coe_aeval_eq_eval, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub,
      Polynomial.eval_natCast, Polynomial.eval_X, Polynomial.eval_one]
    field_simp
    rw [← Finset.sum_div]
    field
  · simp
    field

end bernstein

open bernstein

local postfix:1024 "/ₙ" => z

variable {E : Type*} [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [Module ℝ E] [ContinuousSMul ℝ E]

/-- The `n`-th approximation of a continuous function on `[0,1]` by Bernstein polynomials,
given by `∑ k, bernstein n k x • f (k/n)`.
-/
/-
**bernsteinApproximation** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：bernsteinApproximation (n : Nat) (f : C(I, E)) : C(I, E)
参数：n : Nat；f : C(I, E)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `n`-th approximation of a continuous function on `[0,1]` by Bernstein polyno
mials,
given by `∑ k, bernstein n k x • f (k/n)`.
-/
def bernsteinApproximation (n : ℕ) (f : C(I, E)) : C(I, E) :=
  ∑ k : Fin (n + 1), bernstein n k • .const _ (f k/ₙ)

/-!
We now set up some of the basic machinery of the proof that the Bernstein approximations
converge uniformly.

A key player is the set `S f ε h n x`,
for some function `f : C(I, E)`, `h : 0 < ε`, `n : ℕ` and `x : I`.

This is the set of points `k` in `Fin (n+1)` such that
`k/n` is within `δ` of `x`, where `δ` is the modulus of uniform continuity for `f`,
chosen so `‖f x - f y‖ < ε/2` when `|x - y| < δ`.

We show that if `k ∉ S`, then `1 ≤ δ^-2 * (x - k/n)^2`.
-/

namespace bernsteinApproximation

/-
**bernsteinApproximation.apply** 是 Mathlib 中的一个定理，位于命名空间 `bernsteinApproximation
`。
形式化陈述：apply (n : Nat) (f : C(I, E)) (x : I) : bernsteinApproximation n f x = ∑ k
 : Fin (n + 1), bernstein n k x • f k/ₙ
参数：n : Nat；f : C(I, E)；x : I。
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
· 使用定理 `ContinuousMap.coe_sum`：∀ {α : Type u_1} {β : Type u_2} [inst : Topologic
alSpace α] [inst_1 : TopologicalSpace β] [inst_2 : AddCommMonoid β]   [inst_3 : 
ContinuousA…
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem apply (n : ℕ) (f : C(I, E)) (x : I) :
    bernsteinApproximation n f x = ∑ k : Fin (n + 1), bernstein n k x • f k/ₙ := by
  simp [bernsteinApproximation]

@[simp]
/-
**bernsteinApproximation.apply_zero** 是 Mathlib 中的一个定理，位于命名空间 `bernsteinApproxim
ation`。
形式化陈述：apply_zero (n : Nat) (f : C(I, E)) : bernsteinApproximation n f 0 = f 0
参数：n : Nat；f : C(I, E)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `bernsteinApproximation.apply`：apply (n : Nat) (f : C(I, E)) (x : I) : be
rnsteinApproximation n f x = ∑ k : Fin (n + 1), bernstein n k x • f k/ₙ
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `bernstein_apply`：bernstein_apply (n ν : Nat) (x : I) : bernstein n ν x =
 (n.choose ν : Real) * (x : Real) ^ ν * (1 - (x : Real)) ^ (n - ν)
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Fin.sum_univ_succ`：∀ {M : Type u_2} [inst : AddCommMonoid M] {n : ℕ} (f 
: Fin (n + 1) → M), ∑ i, f i = f 0 + ∑ i, f i.succ
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.choose_zero_right`：choose_zero_right (n : Nat) : choose n 0 = 1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
（共 32 条，此处仅展示前 30 条）
-/
theorem apply_zero (n : ℕ) (f : C(I, E)) : bernsteinApproximation n f 0 = f 0 := by
  simp [apply, Fin.sum_univ_succ, bernstein_apply, z]

@[simp]
/-
**bernsteinApproximation.apply_one** 是 Mathlib 中的一个定理，位于命名空间 `bernsteinApproxima
tion`。
形式化陈述：apply_one {n : Nat} (hn : n != 0) (f : C(I, E)) : bernsteinApproximation n
 f 1 = f 1
参数：hn : n != 0；f : C(I, E)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `bernsteinApproximation.apply`：apply (n : Nat) (f : C(I, E)) (x : I) : be
rnsteinApproximation n f x = ∑ k : Fin (n + 1), bernstein n k x • f k/ₙ
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `bernstein_apply`：bernstein_apply (n ν : Nat) (x : I) : bernstein n ν x =
 (n.choose ν : Real) * (x : Real) ^ ν * (1 - (x : Real)) ^ (n - ν)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `Fin.sum_univ_castSucc`：∀ {M : Type u_2} [inst : AddCommMonoid M] {n : ℕ}
 (f : Fin (n + 1) → M), ∑ i, f i = ∑ i, f i.castSucc + f (Fin.last n)
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `Nat.choose_self`：choose_self (n : Nat) : choose n n = 1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `tsub_self`：tsub_self (a : α) : a - a = 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `bernstein.z_last`：∀ {n : ℕ}, n ≠ 0 → bernstein.z (Fin.last n) = 1
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem apply_one {n : ℕ} (hn : n ≠ 0) (f : C(I, E)) : bernsteinApproximation n f 1 = f 1 := by
  simp [apply, Fin.sum_univ_castSucc, bernstein_apply, hn, Nat.sub_eq_zero_iff_le]

end bernsteinApproximation

open bernsteinApproximation

/-- The Bernstein approximations
```
∑ k : Fin (n+1), f (k/n : ℝ) * n.choose k * x^k * (1-x)^(n-k)
```
for a continuous function `f : C([0,1], ℝ)` converge uniformly to `f` as `n` tends to infinity.

This is the proof given in [Richard Beals' *Analysis, an introduction*][beals-analysis], §7D,
and reproduced on wikipedia.
-/
/-
**bernsteinApproximation_uniform** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：bernsteinApproximation_uniform [LocallyConvexSpace Real E] (f : C(I, E)) :
 Tendsto (fun n : Nat => bernsteinApproximation n f) atTop (𝓝 f)
参数：f : C(I, E)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isUniformAddGroup_of_addCommGroup`：∀ {G : Type u_1} [inst : AddCommGroup
 G] [inst_1 : TopologicalSpace G] [inst_2 : IsTopologicalAddGroup G],   IsUnifor
mAddGroup G
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `continuous_gauge`：continuous_gauge (hc : Convex Real s) (hs₀ : s in 𝓝 0)
 : Continuous (gauge s)
· 使用定理 `Continuous.fun_sub`：∀ {G : Type u_1} {X : Type u_3} [inst : TopologicalS
pace X] [inst_1 : TopologicalSpace G] [inst_2 : Sub G]   [ContinuousSub G] {f g 
: X → G}…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `ContinuousMapClass.map_continuous`：∀ {F : Type u_1} {X : outParam (Type 
u_2)} {Y : outParam (Type u_3)} {inst : TopologicalSpace X}   {inst_1 : Topologi
calSpace Y} {inst_2 : F…
· 使用定理 `Continuous.fst`：Continuous.fst {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).1
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `Continuous.snd`：Continuous.snd {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).2
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsCompact.bddAbove`：IsCompact.bddAbove [ClosedIciTopology α] [Nonempty α
] {s : Set α} (hs : IsCompact s) : BddAbove s
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `isCompact_range`：isCompact_range [CompactSpace X] {f : X -> Y} (hf : Con
tinuous f) : IsCompact (range f)
· 使用定理 `instCompactSpaceProd`：∀ {X : Type u} {Y : Type v} [inst : TopologicalSpa
ce X] [inst_1 : TopologicalSpace Y] [CompactSpace X] [CompactSpace Y],   Compact
Space (X ×…
· 使用定理 `ConditionallyCompleteLinearOrder.toCompactIccSpace`：∀ (α : Type u_2) [in
st : ConditionallyCompleteLinearOrder α] [inst_1 : TopologicalSpace α] [OrderTop
ology α],   CompactIccSpace α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `gauge_nonneg`：gauge_nonneg (x : E) : 0 <= gauge s x
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `CompactSpace.uniformContinuous_of_continuous`：CompactSpace.uniformContin
uous_of_continuous [CompactSpace α] {f : α -> β} (h : Continuous f) : UniformCon
tinuous f
· 使用定理 `Filter.HasBasis.uniformContinuous_iff`：Filter.HasBasis.uniformContinuous
_iff {ι'} {p : ι -> Prop} {s : ι -> SetRel α α} (ha : (𝓤 α).HasBasis p s) {q : ι
' -> Prop} {t : ι' -> Set (…
· 使用定理 `Metric.uniformity_basis_dist`：uniformity_basis_dist : (𝓤 α).HasBasis (fu
n ε : Real => 0 < ε) fun ε => { p : α × α | dist p.1 p.2 < ε }
· 使用定理 `Filter.HasBasis.uniformity_of_nhds_zero_swapped`：∀ {α : Type u_1} [inst 
: UniformSpace α] [inst_1 : AddGroup α] [IsUniformAddGroup α] {ι : Sort u_3} {p 
: ι → Prop}   {U : ι → Set α}, (nhds …
· 使用定理 `Filter.basis_sets`：basis_sets (l : Filter α) : l.HasBasis (fun s : Set α
 => s in l) id
（共 166 条，此处仅展示前 30 条）

--- 原说明 ---
The Bernstein approximations
```
∑ k : Fin (n+1), f (k/n : ℝ) * n.choose k * x^k * (1-x)^(n-k)
```
for a continuous function `f : C([0,1], ℝ)` converge uniformly to `f` as `n` ten
ds to infinity.

This is the proof given in [Richard Beals' *Analysis, an introduction*][beals-an
alysis], §7D,
and reproduced on wikipedia.
-/
theorem bernsteinApproximation_uniform [LocallyConvexSpace ℝ E] (f : C(I, E)) :
    Tendsto (fun n : ℕ => bernsteinApproximation n f) atTop (𝓝 f) := by
  let : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  have : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  /- Topology on a locally convex TVS is given by a family of seminorms `‖x‖_U = gauge U x`,
  where the open symmetric convex sets `U` form a basis of neighborhoods in this topology,
  and are the open unit balls for the corresponding seminorms.
  For technical reasons, we neither assume `U`s to be open, nor symmetric. -/
  suffices ∀ U ∈ 𝓝 (0 : E), Convex ℝ U →
      ∀ᶠ n in atTop, ∀ x : I, gauge U (bernsteinApproximation n f x - f x) < 1 by
    rw [(LocallyConvexSpace.convex_basis_zero ℝ E).uniformity_of_nhds_zero_swapped
      |>.compactConvergenceUniformity_of_compact |> nhds_basis_uniformity |>.tendsto_right_iff]
    rintro U ⟨hU₀, hcU⟩
    filter_upwards [this U hU₀ hcU] with n hn x
    exact setOfPred_gauge_lt_one_subset_self hcU (mem_of_mem_nhds hU₀) (absorbent_nhds_zero hU₀)
      (hn x)
  intro U hU₀ hUc
  /- Choose a constant `C` such that `‖f x - f y‖_U ≤ C` for all `x`, `y`.
  For a normed space, this would be twice the norm of `f`. -/
  obtain ⟨C, hC⟩ : ∃ C, ∀ x y, gauge U (f x - f y) ≤ C := by
    have : Continuous fun (x, y) ↦ gauge U (f x - f y) := by fun_prop
    simpa only [BddAbove, Set.Nonempty, mem_upperBounds, Set.forall_mem_range, Prod.forall]
      using isCompact_range this |>.bddAbove
  have hC₀ : 0 ≤ C := le_trans (gauge_nonneg _) (hC 0 0)
  /- Use uniform continuity of `f` to choose `δ > 0` such that `‖f x - f y‖_U < 1 / 2`
  whenever `dist x y < δ`. -/
  obtain ⟨δ, hδ₀, hδ⟩ : ∃ δ > 0, ∀ x y : I, dist x y < δ → gauge U (f x - f y) < 1 / 2 := by
    have := CompactSpace.uniformContinuous_of_continuous (map_continuous f)
    rw [Metric.uniformity_basis_dist.uniformContinuous_iff
      (basis_sets _).uniformity_of_nhds_zero_swapped] at this
    exact this {z | gauge U z < 1 / 2} <| tendsto_gauge_nhds_zero hU₀
      |>.eventually_lt_const <| by positivity
  -- Take `n ≠ 0` such that `C / δ ^ 2 / n < 1 / 2`.
  have nhds_zero := tendsto_const_div_atTop_nhds_zero_nat (C / δ ^ 2)
  filter_upwards [nhds_zero.eventually_lt_const (half_pos one_pos), eventually_ne_atTop 0]
    with n nh hn₀ x
  -- The idea is to split up the sum over `k` into two sets,
  -- `S`, where `x - k/n < δ`, and its complement.
  set S : Finset (Fin (n + 1)) := {k : Fin (n + 1) | dist k/ₙ x < δ}
  calc
    gauge U (bernsteinApproximation n f x - f x)
      = gauge U (∑ k : Fin (n + 1), bernstein n k x • (f k/ₙ - f x)) := by
      simp [bernsteinApproximation.apply, smul_sub, ← Finset.sum_smul]
    _ ≤ ∑ k : Fin (n + 1), gauge U (bernstein n k x • (f k/ₙ - f x)) :=
      gauge_sum_le hUc (absorbent_nhds_zero hU₀) _ _
    _ = ∑ k : Fin (n + 1), bernstein n k x * gauge U (f k/ₙ - f x) := by
      simp only [gauge_smul_of_nonneg, bernstein_nonneg, smul_eq_mul]
    _ = (∑ k ∈ S, bernstein n k x * gauge U (f k/ₙ - f x)) +
          ∑ k ∈ Sᶜ, bernstein n k x * gauge U (f k/ₙ - f x) :=
      (S.sum_add_sum_compl _).symm
    -- We'll now deal with the terms in `S` and the terms in `Sᶜ` in separate calc blocks.
    _ < 1 / 2 + 1 / 2 := add_lt_add_of_le_of_lt ?_ ?_
    _ = 1 := add_halves 1
  · -- We now work on the terms in `S`: uniform continuity and `bernstein.probability`
    -- quickly give us a bound.
    calc
      ∑ k ∈ S, bernstein n k x * gauge U (f k/ₙ - f x) ≤ ∑ k ∈ S, bernstein n k x * (1 / 2) := by
        gcongr with k hk
        refine (hδ _ _ ?_).le
        simpa [S] using hk
      _ = 1 / 2 * ∑ k ∈ S, bernstein n k x := by rw [mul_comm, Finset.sum_mul]
      -- In this step we increase the sum over `S` back to a sum over all of `Fin (n+1)`,
      -- so that we can use `bernstein.probability`.
      _ ≤ 1 / 2 * ∑ k : Fin (n + 1), bernstein n k x := by gcongr; exact S.subset_univ
      _ = 1 / 2 := by rw [bernstein.probability, mul_one]
  · -- We now turn to working on `Sᶜ`: we control the difference term just using `C`,
    -- and then insert a `(x - k/n)^2 / δ^2` factor
    -- (which is at least one because we are not in `S`).
    calc
      ∑ k ∈ Sᶜ, bernstein n k x * gauge U (f k/ₙ - f x) ≤ ∑ k ∈ Sᶜ, C * bernstein n k x := by
        simp only [mul_comm (bernstein n _ x)]
        gcongr
        apply hC
      _ = C * ∑ k ∈ Sᶜ, bernstein n k x := by rw [Finset.mul_sum]
      _ ≤ C * ∑ k ∈ Sᶜ, ((x : ℝ) - k/ₙ) ^ 2 / δ ^ 2 * bernstein n k x := by
        gcongr with k hk
        conv_lhs => rw [← one_mul (bernstein _ _ _)]
        gcongr
        simpa [one_le_div₀, hδ₀, sq_le_sq, S, abs_of_pos, ← Real.dist_eq, dist_comm (x : ℝ)]
          using! hk
      -- Again enlarging the sum from `Sᶜ` to all of `Fin (n+1)`
      _ ≤ C * ∑ k : Fin (n + 1), ((x : ℝ) - k/ₙ) ^ 2 / δ ^ 2 * bernstein n k x := by
        gcongr; exact Sᶜ.subset_univ
      _ = C * (∑ k : Fin (n + 1), ((x : ℝ) - k/ₙ) ^ 2 * bernstein n k x) / δ ^ 2 := by
        simp only [← mul_div_right_comm, ← mul_div_assoc, ← Finset.sum_div]
      -- `bernstein.variance` and `x ∈ [0,1]` gives the uniform bound
      _ = C / δ ^ 2 * x * (1 - x) / n := by rw [variance hn₀]; ring
      _ ≤ C / δ ^ 2 * 1 * 1 / n := by gcongr <;> unit_interval
      _ < 1 / 2 := by simpa only [mul_one]
