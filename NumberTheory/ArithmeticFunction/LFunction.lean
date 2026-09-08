/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.NumberTheory.ArithmeticFunction.Defs
public import Mathlib.Order.Northcott
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.PiTopology
public import Mathlib.RingTheory.PowerSeries.Substitution

/-!
# Construction of L-functions

This file constructs L-functions as formal Dirichlet series.

## Main definitions

* `ArithmeticFunction.ofPowerSeries q f`: L-function `f(q⁻ˢ)` obtained from a power series `f(T)`.
* `ArithmeticFunction.eulerProduct f`: the Euler product of a family `f i` of Dirichlet series.

## Implementation notes

We take the following route from polynomials to L-functions:
* Starting from a polynomial in `T`, `PowerSeries.invOfUnit` gives the reciporical power series.
* `ofPowerSeries` gives the local Euler factor as a formal Dirichlet series on powers of `q`.
* `eulerProduct` gives the L-function as the formal product of these local Euler factors.
* `LSeries` gives the L-function as an analytic function on the right half-plane of convergence.

For example, the Riemann zeta function `ζ(s)` corresponds to taking `1 - T` at each prime `p`.

For context, here is a diagram of the possible routes from polynomials to L-functions:
```
                   T=q⁻ˢ                     s ∈ ℂ
[polynomials in T] ----> [polynomials in q⁻ˢ] ----> [analytic function in s]
          |                           |                           |
          | (reciprocal)              | (reciprocal)              | (reciprocal)
          v         T=q⁻ˢ             V          s ∈ ℂ            V
[power series in T] ----> [power series in q⁻ˢ] ----> [analytic function in s] (the Euler factor)
          |                           |                           |
          | (product)                 | (product)                 | (product)
          v                 T=q⁻ˢ     V               s ∈ ℂ       V
[multivariate power series] ----> [Dirichlet series] ----> [L-function in s] (the Euler product)
```
-/

@[expose] public section

namespace ArithmeticFunction

section PowerSeries

variable {R : Type*}

section CommSemiring

variable [CommSemiring R]

set_option backward.isDefEq.respectTransparency.types false in
/-- The arithmetic function corresponding to the Dirichlet series `f(q⁻ˢ)`.
For example, if `f = 1 + X + X² + ...` and `q = p`, then `f(q⁻ˢ) = 1 + p⁻ˢ + p⁻²ˢ + ...`.

If `q ≤ 1` then `k ↦ q ^ k` is not injective, so we use the junk value `f.constantCoeff`. -/
/-
**ArithmeticFunction.ofPowerSeries** 是 Mathlib 中的一个定义，位于命名空间 `ArithmeticFunction
`。
形式化陈述：ofPowerSeries (q : Nat) : PowerSeries R ->ₐ[R] ArithmeticFunction R where 
toFun f
参数：q : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The arithmetic function corresponding to the Dirichlet series `f(q⁻ˢ)`.
For example, if `f = 1 + X + X² + ...` and `q = p`, then `f(q⁻ˢ) = 1 + p⁻ˢ + p⁻²
ˢ + ...`.

If `q ≤ 1` then `k ↦ q ^ k` is not injective, so we use the junk value `f.consta
ntCoeff`.
-/
noncomputable def ofPowerSeries (q : ℕ) : PowerSeries R →ₐ[R] ArithmeticFunction R where
  toFun f := if hq : 1 < q then
    ⟨Function.extend (q ^ ·) (f.coeff ·) 0, by simp [Nat.ne_zero_of_lt hq]⟩ else
      algebraMap R (ArithmeticFunction R) f.constantCoeff
  map_zero' := by ext; split_ifs <;> simp [Function.extend]
  -- note that `ofPowerSeries.map_one'` relies on the junk value `f.constantCoeff`.
  map_one' := by
    ext n
    split_ifs with hq
    · by_cases hn : ∃ k, q ^ k = n
      · obtain ⟨a, rfl⟩ := hn
        simp [(Nat.pow_right_injective hq).extend_apply, one_apply, hq.ne']
      · simp [hn, one_apply_ne (fun H ↦ hn ⟨0, H.symm⟩)]
    · simp
  map_add' f g := by
    ext n
    split_ifs with hq
    · by_cases h : ∃ a, q ^ a = n
      · obtain ⟨a, rfl⟩ := h
        simp [(Nat.pow_right_injective hq).extend_apply]
      · simp [h]
    · by_cases hn : n = 1 <;> simp [hn]
  map_mul' f g := by
    ext n
    split_ifs with hq
    · simp_rw [mul_apply, coe_mk]
      by_cases hn : ∃ a, q ^ a = n
      · obtain ⟨k, rfl⟩ := hn
        rw [(Nat.pow_right_injective hq).extend_apply]
        have hs : (Finset.antidiagonal k).map (.prodMap ⟨fun k ↦ q ^ k, Nat.pow_right_injective hq⟩
            ⟨fun k ↦ q ^ k, Nat.pow_right_injective hq⟩) ⊆ (q ^ k).divisorsAntidiagonal :=
          Nat.antidiagonal_map_subset_divisorsAntidiagonal_pow hq k
        rw [PowerSeries.coeff_mul k f g, ← Finset.sum_subset hs]
        · simp [(Nat.pow_right_injective hq).extend_apply]
        · intro (a, b) hab h
          by_cases ha : ∃ i, q ^ i = a
          · by_cases hb : ∃ j, q ^ j = b
            · obtain ⟨i, rfl⟩ := ha
              obtain ⟨j, rfl⟩ := hb
              rw [Nat.mem_divisorsAntidiagonal, ← pow_add, Nat.pow_right_inj hq] at hab
              simp_rw [Finset.mem_map, not_exists, not_and, Finset.mem_antidiagonal] at h
              simpa using h (i, j) hab.1
            · rwa [mul_comm, Function.extend_apply', Pi.zero_apply, zero_mul]
          · rwa [Function.extend_apply', Pi.zero_apply, zero_mul]
      · rw [Function.extend_apply' _ _ _ hn, Pi.zero_apply, Finset.sum_eq_zero]
        intro (a, b) hk
        obtain ⟨hab, -⟩ := Nat.mem_divisorsAntidiagonal.mp hk
        by_cases ha : ∃ i, q ^ i = a
        · by_cases hb : ∃ j, q ^ j = b
          · obtain ⟨i, rfl⟩ := ha
            obtain ⟨j, rfl⟩ := hb
            rw [← pow_add] at hab
            exact (hn ⟨i + j, hab⟩).elim
          · rwa [mul_comm, Function.extend_apply', Pi.zero_apply, zero_mul]
        · rwa [Function.extend_apply', Pi.zero_apply, zero_mul]
    · simp
  commutes' x := by
    ext n
    split_ifs with hq
    · simp only [Algebra.algebraMap_eq_smul_one, coe_mk]
      by_cases hn : ∃ k, q ^ k = n
      · obtain ⟨k, rfl⟩ := hn
        simp [(Nat.pow_right_injective hq).extend_apply, one_apply, hq.ne']
      · rw [Function.extend_apply' _ _ _ hn, Pi.zero_apply, smul_map, one_apply_ne, smul_zero]
        contrapose hn
        exact ⟨0, by simp [hn]⟩
    · simp

set_option backward.isDefEq.respectTransparency.types false in
/-
**ArithmeticFunction.ofPowerSeries_apply** 是 Mathlib 中的一个定理，位于命名空间 `ArithmeticFu
nction`。
形式化陈述：ofPowerSeries_apply {q : Nat} (hq : 1 < q) (f : PowerSeries R) (n : Nat) :
 ofPowerSeries q f n = Function.extend (q ^ ·) (f.coeff ·) 0 n
参数：hq : 1 < q；f : PowerSeries R；n : Nat。
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
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `OneHom.mk.congr_simp`：∀ {M : Type u_10} {N : Type u_11} [inst : One M] [
inst_1 : One N] (toFun toFun_1 : M → N) (e_toFun : toFun = toFun_1)   (map_one' 
: toFun 1 …
· 使用定理 `MonoidHom.mk.congr_simp`：∀ {M : Type u_10} {N : Type u_11} [inst : MulOn
e M] [inst_1 : MulOne N] (toOneHom toOneHom_1 : OneHom M N)   (e_toOneHom : toOn
eHom = toOneH…
· 使用定理 `RingHom.mk.congr_simp`：∀ {α : Type u_5} {β : Type u_6} [inst : NonAssocS
emiring α] [inst_1 : NonAssocSemiring β]   (toMonoidHom toMonoidHom_1 : α →* β) 
(e_toMonoid…
· 使用定理 `AlgHom.mk.congr_simp`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : C
ommSemiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 : Algebra R
 A] [inst_…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ofPowerSeries_apply {q : ℕ} (hq : 1 < q) (f : PowerSeries R) (n : ℕ) :
    ofPowerSeries q f n = Function.extend (q ^ ·) (f.coeff ·) 0 n := by
  simp [ofPowerSeries, dif_pos hq]
/-
**ArithmeticFunction.ofPowerSeries_apply_pow** 是 Mathlib 中的一个定理，位于命名空间 `Arithmet
icFunction`。
形式化陈述：ofPowerSeries_apply_pow {q : Nat} (hq : 1 < q) (f : PowerSeries R) (k : Na
t) : ofPowerSeries q f (q ^ k) = f.coeff k
参数：hq : 1 < q；f : PowerSeries R；k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ArithmeticFunction.ofPowerSeries_apply`：ofPowerSeries_apply {q : Nat} (h
q : 1 < q) (f : PowerSeries R) (n : Nat) : ofPowerSeries q f n = Function.extend
 (q ^ ·) (f.coeff ·) 0 n
· 使用定理 `Function.Injective.extend_apply`：∀ {α : Sort u_1} {β : Sort u_2} {γ : So
rt u_3} {f : α → β},   Function.Injective f → ∀ (g : α → γ) (e' : β → γ) (a : α)
, Function.extend f g…
· 使用定理 `Nat.pow_right_injective`：∀ {a : ℕ}, 2 ≤ a → Function.Injective fun x => 
a ^ x
-/
theorem ofPowerSeries_apply_pow {q : ℕ} (hq : 1 < q) (f : PowerSeries R) (k : ℕ) :
    ofPowerSeries q f (q ^ k) = f.coeff k := by
  rw [ofPowerSeries_apply hq, (Nat.pow_right_injective hq).extend_apply]
/-
**ArithmeticFunction.ofPowerSeries_apply_zero** 是 Mathlib 中的一个定理，位于命名空间 `Arithme
ticFunction`。
形式化陈述：ofPowerSeries_apply_zero (q : Nat) (f : PowerSeries R) : ofPowerSeries q f
 0 = 0
参数：q : Nat；f : PowerSeries R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ArithmeticFunction.map_zero`：map_zero {f : ArithmeticFunction R} : f 0 =
 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ofPowerSeries_apply_zero (q : ℕ) (f : PowerSeries R) : ofPowerSeries q f 0 = 0 := by
  simp

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
-- note that `ofPowerSeries_apply_one` relies on the junk value `f.constantCoeff`.
/-
**ArithmeticFunction.ofPowerSeries_apply_one** 是 Mathlib 中的一个定理，位于命名空间 `Arithmet
icFunction`。
形式化陈述：ofPowerSeries_apply_one (q : Nat) (f : PowerSeries R) : ofPowerSeries q f 
1 = f.constantCoeff
参数：q : Nat；f : PowerSeries R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `ArithmeticFunction.ofPowerSeries_apply_pow`：ofPowerSeries_apply_pow {q :
 Nat} (hq : 1 < q) (f : PowerSeries R) (k : Nat) : ofPowerSeries q f (q ^ k) = f
.coeff k
· 使用定理 `PowerSeries.coeff_zero_eq_constantCoeff`：coeff_zero_eq_constantCoeff : ⇑
(coeff (R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `OneHom.mk.congr_simp`：∀ {M : Type u_10} {N : Type u_11} [inst : One M] [
inst_1 : One N] (toFun toFun_1 : M → N) (e_toFun : toFun = toFun_1)   (map_one' 
: toFun 1 …
· 使用定理 `MonoidHom.mk.congr_simp`：∀ {M : Type u_10} {N : Type u_11} [inst : MulOn
e M] [inst_1 : MulOne N] (toOneHom toOneHom_1 : OneHom M N)   (e_toOneHom : toOn
eHom = toOneH…
· 使用定理 `RingHom.mk.congr_simp`：∀ {α : Type u_5} {β : Type u_6} [inst : NonAssocS
emiring α] [inst_1 : NonAssocSemiring β]   (toMonoidHom toMonoidHom_1 : α →* β) 
(e_toMonoid…
· 使用定理 `AlgHom.mk.congr_simp`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : C
ommSemiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 : Algebra R
 A] [inst_…
· 使用定理 `ArithmeticFunction.algebraMap_apply_one`：algebraMap_apply_one {S : Type*
} [CommSemiring R] [Semiring S] [Algebra R S] (x : R) : algebraMap R (Arithmetic
Function S) x 1 = algebraMap …
· 使用定理 `RingHomCompTriple.comp_apply`：comp_apply [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]
 {x : R₁} : σ₂₃ (σ₁₂ x) = σ₁₃ x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ofPowerSeries_apply_one (q : ℕ) (f : PowerSeries R) :
    ofPowerSeries q f 1 = f.constantCoeff := by
  by_cases hq : 1 < q
  · rw [← pow_zero q, ofPowerSeries_apply_pow hq, PowerSeries.coeff_zero_eq_constantCoeff]
  · simp [ofPowerSeries, dif_neg hq]

end CommSemiring

section CommRing

variable [CommRing R]

/-- In `ArithmeticFunction.ofPowerSeries`, replacing the base `q` with a power `q ^ k` corresponds
to substituting `X` with `X ^ k` in the original power series. -/
/-
**ArithmeticFunction.ofPowerSeries_pow** 是 Mathlib 中的一个定理，位于命名空间 `ArithmeticFunc
tion`。
形式化陈述：ofPowerSeries_pow (q : Nat) {k : Nat} (hk : k != 0) (f : PowerSeries R) : 
ofPowerSeries (q ^ k) f = ofPowerSeries q (f.subst (PowerSeries.X ^ k))
参数：q : Nat；hk : k != 0；f : PowerSeries R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ArithmeticFunction.ext`：ext ⦃f g : ArithmeticFunction R⦄ (h : forall x, 
f x = g x) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ArithmeticFunction.ofPowerSeries_apply_pow`：ofPowerSeries_apply_pow {q :
 Nat} (hq : 1 < q) (f : PowerSeries R) (k : Nat) : ofPowerSeries q f (q ^ k) = f
.coeff k
· 使用定理 `PowerSeries.coeff_subst_X_pow`：coeff_subst_X_pow {k : Nat} (hk : k != 0)
 (f : PowerSeries R) (n : Nat) : coeff n (subst (X ^ k) f) = ite (k ∣ n) (algebr
aMap R S (coeff (n …
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用定理 `one_lt_pow'`：one_lt_pow' (ha : 1 < a) {k : Nat} (hk : k != 0) : 1 < a ^ 
k
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_div_cancel_left₀`：∀ {M₀ : Type u_1} [inst : CommMonoidWithZero M₀] [
inst_1 : Div M₀] [MulDivCancelClass M₀] (b : M₀) {a : M₀},   a ≠ 0 → a * b / a =
 b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `ArithmeticFunction.ofPowerSeries_apply`：ofPowerSeries_apply {q : Nat} (h
q : 1 < q) (f : PowerSeries R) (n : Nat) : ofPowerSeries q f n = Function.extend
 (q ^ ·) (f.coeff ·) 0 n
· 使用定理 `Function.extend_apply'`：extend_apply' (g : α -> γ) (e' : β -> γ) (b : β)
 (hb : ¬exists a, f a = b) : extend f g e' b = e' b
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Nat.pow_right_inj`：∀ {a m n : ℕ}, 1 < a → (a ^ m = a ^ n ↔ m = n)
· 使用定理 `Pi.zero_apply`：∀ {ι : Type u_1} {M : ι → Type u_5} [inst : (i : ι) → Zer
o (M i)] (i : ι), 0 i = 0
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `OneHom.mk.congr_simp`：∀ {M : Type u_10} {N : Type u_11} [inst : One M] [
inst_1 : One N] (toFun toFun_1 : M → N) (e_toFun : toFun = toFun_1)   (map_one' 
: toFun 1 …
· 使用定理 `MonoidHom.mk.congr_simp`：∀ {M : Type u_10} {N : Type u_11} [inst : MulOn
e M] [inst_1 : MulOne N] (toOneHom toOneHom_1 : OneHom M N)   (e_toOneHom : toOn
eHom = toOneH…
· 使用定理 `RingHom.mk.congr_simp`：∀ {α : Type u_5} {β : Type u_6} [inst : NonAssocS
emiring α] [inst_1 : NonAssocSemiring β]   (toMonoidHom toMonoidHom_1 : α →* β) 
(e_toMonoid…
· 使用定理 `AlgHom.mk.congr_simp`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : C
ommSemiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 : Algebra R
 A] [inst_…
· 使用定理 `PowerSeries.constantCoeff_subst_X_pow`：constantCoeff_subst_X_pow {k : Na
t} (hk : k != 0) (f : PowerSeries R) : constantCoeff (subst (X ^ k) f) = algebra
Map R S f.constantCoeff
· 使用定理 `RingHomCompTriple.comp_apply`：comp_apply [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]
 {x : R₁} : σ₂₃ (σ₁₂ x) = σ₁₃ x

--- 原说明 ---
In `ArithmeticFunction.ofPowerSeries`, replacing the base `q` with a power `q ^ 
k` corresponds
to substituting `X` with `X ^ k` in the original power series.
-/
theorem ofPowerSeries_pow (q : ℕ) {k : ℕ} (hk : k ≠ 0) (f : PowerSeries R) :
    ofPowerSeries (q ^ k) f = ofPowerSeries q (f.subst (PowerSeries.X ^ k)) := by
  by_cases hq : 1 < q
  · ext n
    by_cases hn : ∃ i, q ^ i = n
    · obtain ⟨i, rfl⟩ := hn
      rw [ofPowerSeries_apply_pow hq, PowerSeries.coeff_subst_X_pow hk]
      split_ifs with hn
      · obtain ⟨j, rfl⟩ := hn
        rw [pow_mul, ofPowerSeries_apply_pow (one_lt_pow' hq hk)]
        simp [hk]
      · rw [ofPowerSeries_apply (one_lt_pow' hq hk), Function.extend_apply', Pi.zero_apply]
        simp_rw [← pow_mul, Nat.pow_right_inj hq, eq_comm, ← dvd_def]
        exact hn
    · rwa [ofPowerSeries_apply hq, ofPowerSeries_apply (one_lt_pow' hq hk),
        Function.extend_apply', Function.extend_apply']
      contrapose! hn
      obtain ⟨i, rfl⟩ := hn
      exact ⟨k * i, pow_mul q k i⟩
  · simp [ofPowerSeries, hq, hk]

-- todo: generalize to `CommSemiring`
/-- `ArithmeticFunction.ofPowerSeries` produces multiplicative power series. -/
/-
**ArithmeticFunction.isMultiplicative_ofPowerSeries_of_isPrimePow** 是 Mathlib 中的
一个定理，位于命名空间 `ArithmeticFunction`。
形式化陈述：isMultiplicative_ofPowerSeries_of_isPrimePow (q : Nat) (hq : IsPrimePow q)
 (f : PowerSeries R) (hf : f.constantCoeff = 1) : IsMultiplicative (ofPowerSerie
s q f)
参数：q : Nat；hq : IsPrimePow q；f : PowerSeries R；hf : f.constantCoeff = 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ArithmeticFunction.ofPowerSeries_apply_one`：ofPowerSeries_apply_one (q :
 Nat) (f : PowerSeries R) : ofPowerSeries q f 1 = f.constantCoeff
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ArithmeticFunction.ofPowerSeries_pow`：ofPowerSeries_pow (q : Nat) {k : N
at} (hk : k != 0) (f : PowerSeries R) : ofPowerSeries (q ^ k) f = ofPowerSeries 
q (f.subst (PowerSeries.X …
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `PowerSeries.constantCoeff_subst_X_pow`：constantCoeff_subst_X_pow {k : Na
t} (hk : k != 0) (f : PowerSeries R) : constantCoeff (subst (X ^ k) f) = algebra
Map R S f.constantCoeff
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.Prime.ne_one`：∀ {p : ℕ}, Nat.Prime p → p ≠ 1
· 使用定理 `Nat.prime_iff`：prime_iff {p : Nat} : p.Prime ↔ _root_.Prime p
· 使用定理 `ArithmeticFunction.ofPowerSeries_apply`：ofPowerSeries_apply {q : Nat} (h
q : 1 < q) (f : PowerSeries R) (n : Nat) : ofPowerSeries q f n = Function.extend
 (q ^ ·) (f.coeff ·) 0 n
· 使用定理 `Nat.Prime.one_lt`：∀ {p : ℕ}, Nat.Prime p → 1 < p
· 使用定理 `Function.extend_apply'`：extend_apply' (g : α -> γ) (e' : β -> γ) (b : β)
 (hb : ¬exists a, f a = b) : extend f g e' b = e' b
（共 37 条，此处仅展示前 30 条）

--- 原说明 ---
`ArithmeticFunction.ofPowerSeries` produces multiplicative power series.
-/
theorem isMultiplicative_ofPowerSeries_of_isPrimePow
    (q : ℕ) (hq : IsPrimePow q) (f : PowerSeries R) (hf : f.constantCoeff = 1) :
    IsMultiplicative (ofPowerSeries q f) := by
  refine ⟨(ofPowerSeries_apply_one q f).trans hf, fun {m n} hmn ↦ ?_⟩
  obtain ⟨p, k, hp, hk, rfl⟩ := hq
  rw [← Nat.prime_iff] at hp
  rw [ofPowerSeries_pow p hk.ne']
  by_cases hm : ∃ i, p ^ i = m
  · obtain ⟨i, rfl⟩ := hm
    by_cases hn : ∃ j, p ^ j = n
    · obtain ⟨j, rfl⟩ := hn
      cases i
      · simp [hk.ne', hf]
      · cases j
        · simp [hk.ne', hf]
        · simp [hp.ne_one] at hmn
    · simp_rw [ofPowerSeries_apply hp.one_lt]
      rw [Function.extend_apply', Function.extend_apply' _ _ _ hn,
        Pi.zero_apply, Pi.zero_apply, mul_zero]
      contrapose! hn
      obtain ⟨j, hj⟩ := hn
      obtain ⟨v, -, rfl⟩ := (Nat.dvd_prime_pow hp).mp (Dvd.intro_left _ hj.symm)
      exact ⟨v, rfl⟩
  · simp_rw [ofPowerSeries_apply hp.one_lt]
    rw [Function.extend_apply', Function.extend_apply' _ _ _ hm,
      Pi.zero_apply, Pi.zero_apply, zero_mul]
    contrapose! hm
    obtain ⟨i, hi⟩ := hm
    obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow hp).mp ⟨n, hi⟩
    exact ⟨j, rfl⟩

end CommRing

end PowerSeries

section EulerProduct

open Filter

variable {ι R : Type*} [CommSemiring R]

/-- A private uniform space instance on `ArithmeticFunction R` in order to define `eulerProduct` as
a `tprod`. If `R` is viewed as having the discrete topology, then the resulting topology on
`ArithmeticFunction R` is the topology of pointwise convergence (see `tendsto_iff`).

See `tendsTo_eulerProduct_of_tendsTo` for the outward facing `eulerProduct` API. -/
local instance uniformSpace : UniformSpace (ArithmeticFunction R) :=
  letI : UniformSpace R := ⊥
  .comap ((↑) : ArithmeticFunction R → (ℕ → R)) inferInstance

/-- A family `f i : ArithmeticFunction R` tends to `g` if and only if for each `n`, the `n`th
coefficient of `f i` is eventually equal to the `n`th coefficient of `g`. If `R` is viewed as
having the discrete topology, then this is the topology of pointwise convergence.

See `tendsTo_eulerProduct_of_tendsTo` for the outward facing `eulerProduct` API. -/
/-
**ArithmeticFunction.tendsto_iff** 是 Mathlib 中的一个定理，位于命名空间 `ArithmeticFunction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A family `f i : ArithmeticFunction R` tends to `g` if and only if for each `n`, 
the `n`th
coefficient of `f i` is eventually equal to the `n`th coefficient of `g`. If `R`
 is viewed as
having the discrete topology, then this is the topology of pointwise convergence
.

See `tendsTo_eulerProduct_of_tendsTo` for the outward facing `eulerProduct` API.
-/
private theorem tendsto_iff
    {f : ι → ArithmeticFunction R} {F : Filter ι} {g : ArithmeticFunction R} :
    Tendsto f F (nhds g) ↔ ∀ n, ∀ᶠ i in F, f i n = g n := by
  let : UniformSpace R := ⊥
  have : Topology.IsInducing ((↑) : ArithmeticFunction R → (ℕ → R)) := ⟨rfl⟩
  simp [this.tendsto_nhds_iff, tendsto_pi_nhds]

/-- The uniform space structure on arithmetic functions is complete.
See `tendsTo_eulerProduct_of_tendsTo` for the outward facing `eulerProduct` API. -/
local instance : CompleteSpace (ArithmeticFunction R) := by
  let : UniformSpace R := ⊥
  apply IsUniformInducing.completeSpace ⟨rfl⟩
  apply IsClosed.isComplete
  have : Set.range ((↑) : ArithmeticFunction R → (ℕ → R)) = {f | f 0 = 0} := by
    ext f
    exact ⟨by rintro ⟨f, rfl⟩; simp, fun hf ↦ ⟨⟨f, hf⟩, rfl⟩⟩
  rw [ArithmeticFunction.range_coe]
  apply isClosed_setOfPred_map_zero

/-- The Euler product of a family of arithmetic functions. Defined as a `tprod`, but see
`tendsTo_eulerProduct_of_tendsTo` for the outward facing `eulerProduct` API. -/
/-
**ArithmeticFunction.eulerProduct** 是 Mathlib 中的一个定义，位于命名空间 `ArithmeticFunction`
。
形式化陈述：eulerProduct (f : ι -> ArithmeticFunction R) : ArithmeticFunction R
参数：f : ι -> ArithmeticFunction R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Euler product of a family of arithmetic functions. Defined as a `tprod`, but
 see
`tendsTo_eulerProduct_of_tendsTo` for the outward facing `eulerProduct` API.
-/
noncomputable def eulerProduct (f : ι → ArithmeticFunction R) : ArithmeticFunction R :=
  ∏' i, f i

/-- If arithmetic functions `f i` converges to `1` pointwise, then the partial products
`∏ i ∈ s, f i` converge to `eulerProduct f` pointwise. -/
/-
**ArithmeticFunction.tendsTo_eulerProduct_of_tendsTo** 是 Mathlib 中的一个定理，位于命名空间 `
ArithmeticFunction`。
形式化陈述：tendsTo_eulerProduct_of_tendsTo (f : ι -> ArithmeticFunction R) (hf : fora
ll n, forallᶠ i in cofinite, f i n = (1 : ArithmeticFunction R) n) : forall n, f
orallᶠ s in atTop, (∏ i in s, f i) n = eulerProduct f n
参数：f : ι -> ArithmeticFunction R；hf : forall n, forallᶠ i in cofinite, f i n = (
1 : ArithmeticFunction R) n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ArithmeticFunction.instCompleteSpace`：∀ {R : Type u_2} [inst : CommSemir
ing R], CompleteSpace (ArithmeticFunction R)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsUniformInducing.cauchy_map_iff`：IsUniformInducing.cauchy_map_iff {f : 
α -> β} (hf : IsUniformInducing f) {F : Filter α} : Cauchy (map f F) ↔ Cauchy F
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.map_map`：map_map : Filter.map m' (Filter.map m f) = Filter.map (m
' ∘ m) f
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Pi.uniformity`：Pi.uniformity : 𝓤 (forall i, α i) = ⨅ i : ι, (Filter.coma
p fun a => (a.1 i, a.2 i)) (𝓤 (α i))
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `DiscreteUniformity.eq_principal_setRelId`：eq_principal_setRelId : unifor
mity X = 𝓟 SetRel.id
· 使用定理 `DiscreteUniformity.inst`：∀ (X : Type u_1), DiscreteUniformity X
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Filter.prod_atTop_atTop_eq`：prod_atTop_atTop_eq [Preorder α] [Preorder β
] : (atTop : Filter α) ×ˢ (atTop : Filter β) = (atTop : Filter (α × β))
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Filter.eventually_iff_exists_mem`：eventually_iff_exists_mem {p : α -> Pr
op} {f : Filter α} : (forallᶠ x in f, p x) ↔ exists v in f, forall y in v, p y
· 使用定理 `Filter.eventually_all_finite`：eventually_all_finite {ι} {I : Set ι} (hI 
: I.Finite) {l} {p : ι -> α -> Prop} : (forallᶠ x in l, forall i in I, p i x) ↔ 
forall i in I, for…
· 使用定理 `Set.finite_Iic`：∀ {α : Type u_1} [inst : Preorder α] [LocallyFiniteOrder
Bot α] (a : α), (Set.Iic a).Finite
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.mem_cofinite`：mem_cofinite {s : Set α} : s in @cofinite α ↔ sᶜ.Fi
nite
· 使用定理 `Finset.prod_sdiff`：prod_sdiff [DecidableEq ι] (h : s₁ subseteq s₂) : (∏ 
x in s₂ \ s₁, f x) * ∏ x in s₁, f x = ∏ x in s₂, f x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.notMem_compl_iff`：notMem_compl_iff {x : α} : x ∉ sᶜ ↔ x in s
· 使用定理 `Set.Finite.mem_toFinset`：∀ {α : Type u} {s : Set α} {a : α} (hs : s.Fini
te), a ∈ hs.toFinset ↔ a ∈ s
· 使用定理 `Finset.mem_sdiff`：mem_sdiff : a in s \ t ↔ a in s ∧ a ∉ t
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Finset.prod_insert`：prod_insert [DecidableEq ι] : a ∉ s -> ∏ x in insert
 a s, f x = f a * ∏ x in s, f x
（共 40 条，此处仅展示前 30 条）

--- 原说明 ---
If arithmetic functions `f i` converges to `1` pointwise, then the partial produ
cts
`∏ i ∈ s, f i` converge to `eulerProduct f` pointwise.
-/
theorem tendsTo_eulerProduct_of_tendsTo (f : ι → ArithmeticFunction R)
    (hf : ∀ n, ∀ᶠ i in cofinite, f i n = (1 : ArithmeticFunction R) n) :
    ∀ n, ∀ᶠ s in atTop, (∏ i ∈ s, f i) n = eulerProduct f n := by
  let : UniformSpace R := ⊥
  have : IsUniformInducing ((↑) : ArithmeticFunction R → (ℕ → R)) := ⟨rfl⟩
  classical
  suffices Multipliable f from tendsto_iff.mp this.hasProd
  simp_rw [multipliable_iff_cauchySeq_finset, CauchySeq, ← this.cauchy_map_iff,
    Filter.map_map, cauchy_map_iff', Pi.uniformity, DiscreteUniformity.eq_principal_setRelId,
    tendsto_iInf, tendsto_comap_iff, tendsto_principal, Function.comp_apply, prod_atTop_atTop_eq,
    eventually_atTop_prod_self, SetRel.mem_id]
  intro n
  replace hf : ∀ k ∈ Set.Iic n, ∀ᶠ (x : ι) in cofinite, (f x) k = (1 : ArithmeticFunction R) k :=
    fun k hk ↦ hf k
  rw [← eventually_all_finite (Set.finite_Iic n), eventually_iff_exists_mem] at hf
  obtain ⟨s, hs, hs'⟩ := hf
  let t := (mem_cofinite.mp hs).toFinset
  refine ⟨t, fun u v hu hv ↦ ?_⟩
  rw [← Finset.prod_sdiff hu, ← Finset.prod_sdiff hv]
  replace hu : ∀ i ∈ u \ t, i ∈ s := by
    intro i hi
    rw [Finset.mem_sdiff, Set.Finite.mem_toFinset, Set.notMem_compl_iff] at hi
    exact hi.2
  replace hv : ∀ i ∈ v \ t, i ∈ s := by
    intro i hi
    rw [Finset.mem_sdiff, Set.Finite.mem_toFinset, Set.notMem_compl_iff] at hi
    exact hi.2
  suffices ∀ k ≤ n, (∏ x ∈ u \ t, f x) k = (∏ x ∈ v \ t, f x) k by
    rw [mul_apply, mul_apply]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    rw [this k.1 (Nat.divisor_le (Nat.fst_mem_divisors_of_mem_antidiagonal hk))]
  suffices ∀ w, (∀ i ∈ w, i ∈ s) → ∀ k ≤ n, (∏ x ∈ w, f x) k = (1 : ArithmeticFunction R) k by
    intro k hk
    rw [this (u \ t) hu k hk, this (v \ t) hv k hk]
  intro w hw
  induction w using Finset.induction_on
  case empty => simp
  case insert i w hi hw' =>
    intro k hk
    rw [← one_mul (1 : ArithmeticFunction R), Finset.prod_insert hi, mul_apply, mul_apply]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    have h1 := hs' i (hw i (Finset.mem_insert_self i w)) j.1
      ((Nat.divisor_le (Nat.fst_mem_divisors_of_mem_antidiagonal hj)).trans hk)
    have h2 := hw' (fun i hi ↦ hw i (Finset.mem_insert_of_mem hi)) j.2
      ((Nat.divisor_le (Nat.snd_mem_divisors_of_mem_antidiagonal hj)).trans hk)
    rw [h1, h2]
/-
**ArithmeticFunction.isMultiplicative_eulerProduct** 是 Mathlib 中的一个定理，位于命名空间 `Ar
ithmeticFunction`。
形式化陈述：isMultiplicative_eulerProduct (f : ι -> ArithmeticFunction R) (hf : forall
 i, IsMultiplicative (f i)) : IsMultiplicative (eulerProduct f)
参数：f : ι -> ArithmeticFunction R；hf : forall i, IsMultiplicative (f i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ArithmeticFunction.isMultiplicative_finsetProd`：isMultiplicative_finsetP
rod [CommSemiring R] {ι : Type*} (f : ι -> ArithmeticFunction R) (s : Finset ι) 
(hf : forall i in s, IsMultiplicativ…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `_private.Mathlib.NumberTheory.ArithmeticFunction.LFunction.0.ArithmeticF
unction.tendsto_iff`：∀ {ι : Type u_1} {R : Type u_2} [inst : CommSemiring R] {f 
: ι → ArithmeticFunction R} {F : Filter ι}   {g : ArithmeticFunction R}, Filter.
T…
· 使用定理 `Multipliable.hasProd`：Multipliable.hasProd (ha : Multipliable f L) : Has
Prod f (∏'[L] b, f b) L
· 使用定理 `And.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∧ b → c ∧ d
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Filter.eventually_const`：eventually_const {f : Filter α} [t : NeBot f] {
p : Prop} : (forallᶠ _ in f, p) ↔ p
· 使用定理 `SummationFilter.instNeBotFinsetFilterOfNeBot`：∀ {β : Type u_2} (L : Summ
ationFilter β) [L.NeBot], L.filter.NeBot
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.EventuallyEq.trans`：∀ {α : Type u} {β : Type v} {l : Filter α} {f
 g h : α → β}, f =ᶠ[l] g → g =ᶠ[l] h → f =ᶠ[l] h
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `Filter.EventuallyEq.mul`：∀ {α : Type u} {β : Type v} [inst : Mul β] {f f
' g g' : α → β} {l : Filter α},   f =ᶠ[l] g → f' =ᶠ[l] g' → f * f' =ᶠ[l] g * g'
· 使用定理 `forall_and`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (x : α), p x ∧ q x) ↔ 
(∀ (x : α), p x) ∧ ∀ (x : α), q x
· 使用定理 `ArithmeticFunction.eulerProduct.eq_1`：∀ {ι : Type u_1} {R : Type u_2} [i
nst : CommSemiring R] (f : ι → ArithmeticFunction R),   ArithmeticFunction.euler
Product f = ∏' (i : ι), f …
· 使用定理 `tprod_eq_one_of_not_multipliable`：tprod_eq_one_of_not_multipliable (h : 
¬Multipliable f L) : ∏'[L] b, f b = 1
· 使用定理 `ArithmeticFunction.isMultiplicative_one`：isMultiplicative_one [MonoidWit
hZero R] : IsMultiplicative (1 : ArithmeticFunction R)
-/
theorem isMultiplicative_eulerProduct (f : ι → ArithmeticFunction R)
    (hf : ∀ i, IsMultiplicative (f i)) : IsMultiplicative (eulerProduct f) := by
  by_cases hf' : Multipliable f
  · have h (s : Finset ι) : (∏ b ∈ s, f b).IsMultiplicative :=
      isMultiplicative_finsetProd f s fun i a ↦ hf i
    have key := tendsto_iff.mp hf'.hasProd
    refine (forall_and.mp h).imp (fun h ↦ ?_) fun h m n hmn ↦ ?_
    · specialize key 1
      simp_rw [h] at key
      rwa [eventually_const, eq_comm] at key
    · replace h s : (∏ b ∈ s, f b) (m * n) = (∏ b ∈ s, f b) m * (∏ b ∈ s, f b) n := h s hmn
      have h2 := key (m * n)
      simp_rw [h] at h2
      exact eventually_const.mp (EventuallyEq.trans (.symm h2) (.mul (key m) (key n)))
  · rw [eulerProduct, tprod_eq_one_of_not_multipliable hf']
    exact isMultiplicative_one

/-- Given arithmetic functions `f(q⁻ˢ)` with `q → ∞`, the partial products `∏ i ∈ s, f i` converge
to the Euler product pointwise. -/
/-
**ArithmeticFunction.tendsTo_eulerProduct_ofPowerSeries** 是 Mathlib 中的一个定理，位于命名空
间 `ArithmeticFunction`。
形式化陈述：tendsTo_eulerProduct_ofPowerSeries (q : ι -> Nat) [hq : Northcott q] (f : 
ι -> PowerSeries R) (hf : forall i, (f i).constantCoeff = 1) (n : Nat) : forallᶠ
 s in atTop, (∏ i in s, ofPowerSeries (q i) (f i)) n = eulerProduct (fun i => of
PowerSeries (q i) (f i)) n
参数：q : ι -> Nat；f : ι -> PowerSeries R；hf : forall i, (f i).constantCoeff = 1；n 
: Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ArithmeticFunction.tendsTo_eulerProduct_of_tendsTo`：tendsTo_eulerProduct
_of_tendsTo (f : ι -> ArithmeticFunction R) (hf : forall n, forallᶠ i in cofinit
e, f i n = (1 : ArithmeticFunction R) n)…
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.tendsto_atTop`：tendsto_atTop [Preorder β] {m : α -> β} {f : Filte
r α} : Tendsto m f atTop ↔ forall b, forallᶠ a in f, b <= m a
· 使用定理 `northcott_iff_tendsto`：northcott_iff_tendsto [LinearOrder β] [NoMaxOrder
 β] : Northcott h ↔ Tendsto h cofinite atTop
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ArithmeticFunction.map_zero`：map_zero {f : ArithmeticFunction R} : f 0 =
 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `ArithmeticFunction.ofPowerSeries_apply_one`：ofPowerSeries_apply_one (q :
 Nat) (f : PowerSeries R) : ofPowerSeries q f 1 = f.constantCoeff
· 使用定理 `ArithmeticFunction.IsMultiplicative.map_one`：map_one {f : ArithmeticFunc
tion R} (h : f.IsMultiplicative) : f 1 = 1
· 使用定理 `ArithmeticFunction.ofPowerSeries_apply`：ofPowerSeries_apply {q : Nat} (h
q : 1 < q) (f : PowerSeries R) (n : Nat) : ofPowerSeries q f n = Function.extend
 (q ^ ·) (f.coeff ·) 0 n
· 使用定理 `Function.extend_apply'`：extend_apply' (g : α -> γ) (e' : β -> γ) (b : β)
 (hb : ¬exists a, f a = b) : extend f g e' b = e' b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `Pi.zero_apply`：∀ {ι : Type u_1} {M : ι → Type u_5} [inst : (i : ι) → Zer
o (M i)] (i : ι), 0 i = 0
· 使用定理 `ArithmeticFunction.one_apply_ne`：one_apply_ne {x : Nat} (h : x != 1) : (
1 : ArithmeticFunction R) x = 0

--- 原说明 ---
Given arithmetic functions `f(q⁻ˢ)` with `q → ∞`, the partial products `∏ i ∈ s,
 f i` converge
to the Euler product pointwise.
-/
theorem tendsTo_eulerProduct_ofPowerSeries (q : ι → ℕ) [hq : Northcott q]
    (f : ι → PowerSeries R) (hf : ∀ i, (f i).constantCoeff = 1) (n : ℕ) :
    ∀ᶠ s in atTop, (∏ i ∈ s, ofPowerSeries (q i) (f i)) n =
      eulerProduct (fun i ↦ ofPowerSeries (q i) (f i)) n := by
  apply tendsTo_eulerProduct_of_tendsTo
  refine fun n ↦ (tendsto_atTop.mp ((northcott_iff_tendsto q).mp hq) (n + 1)).mono fun i hi ↦ ?_
  rcases n with rfl | rfl | n
  · simp
  · simp [hf]
  · have hqi : 1 < q i := by lia
    rw [ofPowerSeries_apply hqi, Function.extend_apply', Pi.zero_apply, one_apply_ne (by lia)]
    rintro ⟨k, hk⟩
    have h : k ≠ 0 := fun h ↦ by simp_all
    grind [Nat.le_pow h.pos (a := q i)]

end EulerProduct

end ArithmeticFunction

