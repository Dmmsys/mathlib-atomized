/-
Copyright (c) 2023 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
module

public import Mathlib.Computability.AkraBazzi.SumTransform
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Divide-and-conquer recurrences and the Akra-Bazzi theorem

A divide-and-conquer recurrence is a function `T : ℕ → ℝ` that satisfies a recurrence relation of
the form `T(n) = ∑_{i=0}^{k-1} a_i T(r_i(n)) + g(n)` for sufficiently large `n`, where `r_i(n)` is
a function such that `‖r_i(n) - b_i n‖ ∈ o(n / (log n)^2)` for every `i`, the coefficients `a_i`
are positive, and the coefficients `b_i` are real numbers in `(0, 1)`. (This assumption can be
relaxed to `O(n / (log n)^(1+ε))`, for some `ε > 0`; we leave this as future work.) These
recurrences arise mainly in the analysis of divide-and-conquer algorithms such as mergesort or
Strassen's algorithm for matrix multiplication. This class of algorithms works by dividing an
instance of the problem of size `n`, into `k` smaller instances, where the `i`-th instance is of
size roughly `b_i n`, and calling itself recursively on those smaller instances. `T(n)` then
represents the running time of the algorithm, and `g(n)` represents the running time required to
divide the instance and process the answers produced by the recursive calls. Since virtually all
such algorithms produce instances that are only approximately of size `b_i n` (they must round up
or down, at the very least), we allow the instance sizes to be given by a function `r_i(n)` that
approximates `b_i n`.

The Akra-Bazzi theorem gives the asymptotic order of such a recurrence: it states that
`T(n) ∈ Θ(n^p (1 + ∑_{u=0}^{n-1} g(n) / u^{p+1}))`,
where `p` is the unique real number such that `∑ a_i b_i^p = 1`.

## Main definitions and results

* `isTheta_asympBound`: The main result stating that
  `T(n) ∈ Θ(n^p (1 + ∑_{u=0}^{n-1} g(n) / u^{p+1}))`

## Implementation

Note that the original version of the Akra–Bazzi theorem uses an integral rather than the sum in
the above expression, and first considers the `T : ℝ → ℝ` case before moving on to `ℕ → ℝ`. We
prove the version with a sum here, as it is simpler and more relevant for algorithms.

## TODO

* Relax the assumption described in the introduction from `o(n / (log n)^2)` to
  `O(n / (log n)^(1+ε))`, for some `ε > 0`.
* Specialize this theorem to the very common case where the recurrence is of the form
  `T(n) = ℓT(r_i(n)) + g(n)`
  where `g(n) ∈ Θ(n^t)` for some `t`. (This is often called the "master theorem" in the literature.)
* Add the original version of the theorem with an integral instead of a sum.

## References

* Mohamad Akra and Louay Bazzi, On the solution of linear recurrence equations
* Tom Leighton, Notes on better master theorems for divide-and-conquer recurrences
* Manuel Eberl, Asymptotic reasoning in a proof assistant

-/

@[expose] public section

open Finset Real Filter Asymptotics
open scoped Topology

namespace AkraBazziRecurrence

variable {α : Type*} [Fintype α] {T : ℕ → ℝ} {g : ℝ → ℝ} {a b : α → ℝ} {r : α → ℕ → ℕ}
variable [Nonempty α] (R : AkraBazziRecurrence T g a b r)


local notation "ε" => smoothingFn


/-!
### Technical lemmas

The next several lemmas are technical results leading up to `rpow_p_mul_one_sub_smoothingFn_le` and
`rpow_p_mul_one_add_smoothingFn_ge`, which are key steps in the main proof.
-/

/-
**AkraBazziRecurrence.eventually_deriv_rpow_p_mul_one_sub_smoothingFn** 是 Mathli
b 中的一个引理，位于命名空间 `AkraBazziRecurrence`。
形式化陈述：eventually_deriv_rpow_p_mul_one_sub_smoothingFn (p : Real) : deriv (fun z 
=> z ^ p * (1 - ε z)) =ᶠ[atTop] fun z => p * z ^ (p - 1) * (1 - ε z) + z ^ (p - 
1) / (log z ^ 2)
参数：p : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.eventually_gt_atTop`：eventually_gt_atTop [Preorder α] [NoTopOrder
 α] (a : α) : forallᶠ x in atTop, a < x
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `deriv_fun_mul`：deriv_fun_mul (hc : DifferentiableAt 𝕜 c x) (hd : Differe
ntiableAt 𝕜 d x) : deriv (fun y => c y * d y) x = deriv c x * d x + c x * deriv 
d x
· 使用引理 `Real.differentiableAt_rpow_const_of_ne`：differentiableAt_rpow_const_of_n
e (p : Real) {x : Real} (hx : x != 0) : DifferentiableAt Real (fun x => x ^ p) x
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `lt_trans`：lt_trans : a < b -> b < c -> a < c
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用引理 `AkraBazziRecurrence.differentiableAt_one_sub_smoothingFn`：differentiable
At_one_sub_smoothingFn {x : Real} (hx : 1 < x) : DifferentiableAt Real (fun z =>
 1 - ε z) x
· 使用引理 `AkraBazziRecurrence.eventually_deriv_one_sub_smoothingFn`：eventually_der
iv_one_sub_smoothingFn : deriv (fun x => 1 - ε x) =ᶠ[atTop] fun x => x⁻¹ / (log 
x ^ 2)
· 使用定理 `Real.deriv_rpow_const`：deriv_rpow_const (x p : Real) : deriv (fun x => x
 ^ p) x = p * x ^ (p - 1)
· 使用定理 `mul_div`：mul_div (a b c : G) : a * (b / c) = a * b / c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.rpow_neg_one`：rpow_neg_one (x : Real) : x ^ (-1 : Real) = x⁻¹
· 使用定理 `Real.rpow_add`：rpow_add (hx : 0 < x) (y z : Real) : x ^ (y + z) = x ^ y 
* x ^ z
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b

--- 原说明 ---
### Technical lemmas

The next several lemmas are technical results leading up to `rpow_p_mul_one_sub_
smoothingFn_le` and
`rpow_p_mul_one_add_smoothingFn_ge`, which are key steps in the main proof.
-/
lemma eventually_deriv_rpow_p_mul_one_sub_smoothingFn (p : ℝ) :
    deriv (fun z => z ^ p * (1 - ε z))
      =ᶠ[atTop] fun z => p * z ^ (p - 1) * (1 - ε z) + z ^ (p - 1) / (log z ^ 2) :=
  calc deriv (fun z => z ^ p * (1 - ε z))
  _ =ᶠ[atTop] fun x => deriv (· ^ p) x * (1 - ε x) + x ^ p * deriv (1 - ε ·) x := by
    filter_upwards [eventually_gt_atTop 1] with x hx
    rw [deriv_fun_mul]
    · exact differentiableAt_rpow_const_of_ne _ (by positivity)
    · exact differentiableAt_one_sub_smoothingFn hx
  _ =ᶠ[atTop] fun x => p * x ^ (p - 1) * (1 - ε x) + x ^ p * (x⁻¹ / (log x ^ 2)) := by
    filter_upwards [eventually_gt_atTop 1, eventually_deriv_one_sub_smoothingFn]
      with x hx hderiv
    rw [hderiv, Real.deriv_rpow_const]
  _ =ᶠ[atTop] fun x => p * x ^ (p - 1) * (1 - ε x) + x ^ (p - 1) / (log x ^ 2) := by
    filter_upwards [eventually_gt_atTop 0] with x hx
    rw [mul_div, ← Real.rpow_neg_one, ← Real.rpow_add (by positivity), sub_eq_add_neg]
/-
**AkraBazziRecurrence.eventually_deriv_rpow_p_mul_one_add_smoothingFn** 是 Mathli
b 中的一个引理，位于命名空间 `AkraBazziRecurrence`。
形式化陈述：eventually_deriv_rpow_p_mul_one_add_smoothingFn (p : Real) : deriv (fun z 
=> z ^ p * (1 + ε z)) =ᶠ[atTop] fun z => p * z ^ (p - 1) * (1 + ε z) - z ^ (p - 
1) / (log z ^ 2)
参数：p : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.eventually_gt_atTop`：eventually_gt_atTop [Preorder α] [NoTopOrder
 α] (a : α) : forallᶠ x in atTop, a < x
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `deriv_fun_mul`：deriv_fun_mul (hc : DifferentiableAt 𝕜 c x) (hd : Differe
ntiableAt 𝕜 d x) : deriv (fun y => c y * d y) x = deriv c x * d x + c x * deriv 
d x
· 使用引理 `Real.differentiableAt_rpow_const_of_ne`：differentiableAt_rpow_const_of_n
e (p : Real) {x : Real} (hx : x != 0) : DifferentiableAt Real (fun x => x ^ p) x
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `lt_trans`：lt_trans : a < b -> b < c -> a < c
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用引理 `AkraBazziRecurrence.differentiableAt_one_add_smoothingFn`：differentiable
At_one_add_smoothingFn {x : Real} (hx : 1 < x) : DifferentiableAt Real (fun z =>
 1 + ε z) x
· 使用引理 `AkraBazziRecurrence.eventually_deriv_one_add_smoothingFn`：eventually_der
iv_one_add_smoothingFn : deriv (fun x => 1 + ε x) =ᶠ[atTop] fun x => -x⁻¹ / (log
 x ^ 2)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Real.deriv_rpow_const`：deriv_rpow_const (x p : Real) : deriv (fun x => x
 ^ p) x = p * x ^ (p - 1)
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用引理 `neg_div`：neg_div (a b : R) : -b / a = -(b / a)
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `mul_div`：mul_div (a b c : G) : a * (b / c) = a * b / c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.rpow_add`：rpow_add (hx : 0 < x) (y z : Real) : x ^ (y + z) = x ^ y 
* x ^ z
-/
lemma eventually_deriv_rpow_p_mul_one_add_smoothingFn (p : ℝ) :
    deriv (fun z => z ^ p * (1 + ε z))
      =ᶠ[atTop] fun z => p * z ^ (p - 1) * (1 + ε z) - z ^ (p - 1) / (log z ^ 2) :=
  calc deriv (fun x => x ^ p * (1 + ε x))
    _ =ᶠ[atTop] fun x => deriv (· ^ p) x * (1 + ε x) + x ^ p * deriv (1 + ε ·) x := by
      filter_upwards [eventually_gt_atTop 1] with x hx
      rw [deriv_fun_mul]
      · exact differentiableAt_rpow_const_of_ne _ (by positivity)
      · exact differentiableAt_one_add_smoothingFn hx
    _ =ᶠ[atTop] fun x => p * x ^ (p - 1) * (1 + ε x) - x ^ p * (x⁻¹ / (log x ^ 2)) := by
      filter_upwards [eventually_gt_atTop 1, eventually_deriv_one_add_smoothingFn]
        with x hx hderiv
      simp [hderiv, Real.deriv_rpow_const, neg_div, sub_eq_add_neg]
    _ =ᶠ[atTop] fun x => p * x ^ (p - 1) * (1 + ε x) - x ^ (p - 1) / (log x ^ 2) := by
      filter_upwards [eventually_gt_atTop 0] with x hx
      simp [mul_div, ← Real.rpow_neg_one, ← Real.rpow_add (by positivity), sub_eq_add_neg]
/-
**AkraBazziRecurrence.isEquivalent_deriv_rpow_p_mul_one_sub_smoothingFn** 是 Math
lib 中的一个引理，位于命名空间 `AkraBazziRecurrence`。
形式化陈述：isEquivalent_deriv_rpow_p_mul_one_sub_smoothingFn {p : Real} (hp : p != 0)
 : deriv (fun z => z ^ p * (1 - ε z)) ~[atTop] fun z => p * z ^ (p - 1)
参数：hp : p != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AkraBazziRecurrence.eventually_deriv_rpow_p_mul_one_sub_smoothingFn`：eve
ntually_deriv_rpow_p_mul_one_sub_smoothingFn (p : Real) : deriv (fun z => z ^ p 
* (1 - ε z)) =ᶠ[atTop] fun z => p * z ^ (p - 1) * (1 - ε …
· 使用定理 `Asymptotics.IsEquivalent.add_isLittleO`：∀ {α : Type u_1} {β : Type u_2} 
[inst : NormedAddCommGroup β] {u v w : α → β} {l : Filter α},   Asymptotics.IsEq
uivalent l u v → w =o[l] v →…
· 使用定理 `Asymptotics.IsEquivalent.mul`：∀ {α : Type u_1} {β : Type u_3} [inst : No
rmedField β] {t u v w : α → β} {l : Filter α},   Asymptotics.IsEquivalent l t u 
→ Asymptotics.IsEq…
· 使用定理 `Asymptotics.IsEquivalent.refl`：∀ {α : Type u_1} {β : Type u_2} [inst : N
ormedAddCommGroup β] {u : α → β} {l : Filter α}, Asymptotics.IsEquivalent l u u
· 使用引理 `AkraBazziRecurrence.isEquivalent_one_sub_smoothingFn_one`：isEquivalent_o
ne_sub_smoothingFn_one : (fun x => 1 - ε x) ~[atTop] (fun _ => (1 : Real))
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
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
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Asymptotics.IsBigO.mul_isLittleO`：∀ {α : Type u_1} {R : Type u_13} [inst
 : SeminormedRing R] {S : Type u_17} [inst_1 : NormedRing S] [NormMulClass S]   
{l : Filter α} {f₁ f₂ …
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Asymptotics.isBigO_refl`：isBigO_refl (f : α -> E) (l : Filter α) : f =O[
l] f
· 使用定理 `Asymptotics.IsLittleO.inv_rev`：∀ {α : Type u_1} {𝕜 : Type u_15} {𝕜' : Ty
pe u_16} [inst : NormedDivisionRing 𝕜] [inst_1 : NormedDivisionRing 𝕜']   {l : F
ilter α} {f : α → 𝕜…
（共 54 条，此处仅展示前 30 条）
-/
lemma isEquivalent_deriv_rpow_p_mul_one_sub_smoothingFn {p : ℝ} (hp : p ≠ 0) :
    deriv (fun z => z ^ p * (1 - ε z)) ~[atTop] fun z => p * z ^ (p - 1) :=
  calc deriv (fun z => z ^ p * (1 - ε z))
    _ =ᶠ[atTop] fun z => p * z ^ (p - 1) * (1 - ε z) + z ^ (p - 1) / (log z ^ 2) :=
      eventually_deriv_rpow_p_mul_one_sub_smoothingFn p
    _ ~[atTop] fun z => p * z ^ (p - 1) := by
      refine IsEquivalent.add_isLittleO ?one ?two
      case one => calc
        (fun z => p * z ^ (p - 1) * (1 - ε z)) ~[atTop] fun z => p * z ^ (p - 1) * 1 :=
              IsEquivalent.mul IsEquivalent.refl isEquivalent_one_sub_smoothingFn_one
        _ = fun z => p * z ^ (p - 1) := by ext; ring
      case two => calc
        (fun z => z ^ (p - 1) / (log z ^ 2)) =o[atTop] fun z => z ^ (p - 1) / 1 := by
          simp_rw [div_eq_mul_inv]
          refine IsBigO.mul_isLittleO (isBigO_refl _ _)
            (IsLittleO.inv_rev ?_ (by simp))
          rw [isLittleO_const_left]
          refine Or.inr <| Tendsto.comp tendsto_norm_atTop_atTop ?_
          exact Tendsto.comp (g := fun z => z ^ 2)
            (tendsto_pow_atTop (by norm_num)) tendsto_log_atTop
        _ = fun z => z ^ (p - 1) := by ext; simp
        _ =Θ[atTop] fun z => p * z ^ (p - 1) := IsTheta.const_mul_right hp <| isTheta_refl _ _
/-
**AkraBazziRecurrence.isEquivalent_deriv_rpow_p_mul_one_add_smoothingFn** 是 Math
lib 中的一个引理，位于命名空间 `AkraBazziRecurrence`。
形式化陈述：isEquivalent_deriv_rpow_p_mul_one_add_smoothingFn {p : Real} (hp : p != 0)
 : deriv (fun z => z ^ p * (1 + ε z)) ~[atTop] fun z => p * z ^ (p - 1)
参数：hp : p != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AkraBazziRecurrence.eventually_deriv_rpow_p_mul_one_add_smoothingFn`：eve
ntually_deriv_rpow_p_mul_one_add_smoothingFn (p : Real) : deriv (fun z => z ^ p 
* (1 + ε z)) =ᶠ[atTop] fun z => p * z ^ (p - 1) * (1 + ε …
· 使用定理 `Asymptotics.IsEquivalent.add_isLittleO`：∀ {α : Type u_1} {β : Type u_2} 
[inst : NormedAddCommGroup β] {u v w : α → β} {l : Filter α},   Asymptotics.IsEq
uivalent l u v → w =o[l] v →…
· 使用定理 `Asymptotics.IsEquivalent.mul`：∀ {α : Type u_1} {β : Type u_3} [inst : No
rmedField β] {t u v w : α → β} {l : Filter α},   Asymptotics.IsEquivalent l t u 
→ Asymptotics.IsEq…
· 使用定理 `Asymptotics.IsEquivalent.refl`：∀ {α : Type u_1} {β : Type u_2} [inst : N
ormedAddCommGroup β] {u : α → β} {l : Filter α}, Asymptotics.IsEquivalent l u u
· 使用引理 `AkraBazziRecurrence.isEquivalent_one_add_smoothingFn_one`：isEquivalent_o
ne_add_smoothingFn_one : (fun x => 1 + ε x) ~[atTop] (fun _ => (1 : Real))
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
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
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Asymptotics.IsBigO.mul_isLittleO`：∀ {α : Type u_1} {R : Type u_13} [inst
 : SeminormedRing R] {S : Type u_17} [inst_1 : NormedRing S] [NormMulClass S]   
{l : Filter α} {f₁ f₂ …
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Asymptotics.isBigO_refl`：isBigO_refl (f : α -> E) (l : Filter α) : f =O[
l] f
· 使用定理 `Asymptotics.IsLittleO.inv_rev`：∀ {α : Type u_1} {𝕜 : Type u_15} {𝕜' : Ty
pe u_16} [inst : NormedDivisionRing 𝕜] [inst_1 : NormedDivisionRing 𝕜']   {l : F
ilter α} {f : α → 𝕜…
（共 54 条，此处仅展示前 30 条）
-/
lemma isEquivalent_deriv_rpow_p_mul_one_add_smoothingFn {p : ℝ} (hp : p ≠ 0) :
    deriv (fun z => z ^ p * (1 + ε z)) ~[atTop] fun z => p * z ^ (p - 1) :=
  calc deriv (fun z => z ^ p * (1 + ε z))
    _ =ᶠ[atTop] fun z => p * z ^ (p - 1) * (1 + ε z) - z ^ (p - 1) / (log z ^ 2) :=
      eventually_deriv_rpow_p_mul_one_add_smoothingFn p
    _ ~[atTop] fun z => p * z ^ (p - 1) := by
      refine IsEquivalent.add_isLittleO ?one ?two
      case one => calc
        (fun z => p * z ^ (p - 1) * (1 + ε z)) ~[atTop] fun z => p * z ^ (p - 1) * 1 :=
              IsEquivalent.mul IsEquivalent.refl isEquivalent_one_add_smoothingFn_one
        _ = fun z => p * z ^ (p - 1) := by ext; ring
      case two => calc
        (fun z => -(z ^ (p - 1) / (log z ^ 2))) =o[atTop] fun z => z ^ (p - 1) / 1 := by
            simp_rw [isLittleO_neg_left, div_eq_mul_inv]
            refine IsBigO.mul_isLittleO (isBigO_refl _ _)
              (IsLittleO.inv_rev ?_ (by simp))
            rw [isLittleO_const_left]
            refine Or.inr <| Tendsto.comp tendsto_norm_atTop_atTop ?_
            exact Tendsto.comp (g := fun z => z ^ 2)
              (tendsto_pow_atTop (by norm_num)) tendsto_log_atTop
        _ = fun z => z ^ (p - 1) := by ext; simp
        _ =Θ[atTop] fun z => p * z ^ (p - 1) := IsTheta.const_mul_right hp <| isTheta_refl _ _
/-
**AkraBazziRecurrence.isTheta_deriv_rpow_p_mul_one_sub_smoothingFn** 是 Mathlib 中
的一个引理，位于命名空间 `AkraBazziRecurrence`。
形式化陈述：isTheta_deriv_rpow_p_mul_one_sub_smoothingFn {p : Real} (hp : p != 0) : (f
un x => ‖deriv (fun z => z ^ p * (1 - ε z)) x‖) =Θ[atTop] fun z => z ^ (p - 1)
参数：hp : p != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsTheta.norm_left`：∀ {α : Type u_1} {F : Type u_4} {E' : Typ
e u_6} [inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {g : α → F}   {f' : 
α → E'} {l : Filter…
· 使用定理 `Asymptotics.IsEquivalent.isTheta`：∀ {α : Type u_1} {β : Type u_2} [inst 
: NormedAddCommGroup β] {u v : α → β} {l : Filter α},   Asymptotics.IsEquivalent
 l u v → u =Θ[l] v
· 使用引理 `AkraBazziRecurrence.isEquivalent_deriv_rpow_p_mul_one_sub_smoothingFn`：i
sEquivalent_deriv_rpow_p_mul_one_sub_smoothingFn {p : Real} (hp : p != 0) : deri
v (fun z => z ^ p * (1 - ε z)) ~[atTop] fun z => p * z ^ (p…
· 使用定理 `Asymptotics.IsTheta.const_mul_left`：∀ {α : Type u_1} {F : Type u_4} {𝕜 :
 Type u_14} [inst : Norm F] [inst_1 : NormedField 𝕜] {g : α → F} {l : Filter α} 
  {c : 𝕜} {f : α → 𝕜}, c…
· 使用定理 `Asymptotics.isTheta_refl`：isTheta_refl (f : α -> E) (l : Filter α) : f =
Θ[l] f
-/
lemma isTheta_deriv_rpow_p_mul_one_sub_smoothingFn {p : ℝ} (hp : p ≠ 0) :
    (fun x => ‖deriv (fun z => z ^ p * (1 - ε z)) x‖) =Θ[atTop] fun z => z ^ (p - 1) := by
  refine IsTheta.norm_left ?_
  calc (fun x => deriv (fun z => z ^ p * (1 - ε z)) x) =Θ[atTop] fun z => p * z ^ (p - 1) :=
        (isEquivalent_deriv_rpow_p_mul_one_sub_smoothingFn hp).isTheta
    _ =Θ[atTop] fun z => z ^ (p - 1) := IsTheta.const_mul_left hp <| isTheta_refl _ _
/-
**AkraBazziRecurrence.isTheta_deriv_rpow_p_mul_one_add_smoothingFn** 是 Mathlib 中
的一个引理，位于命名空间 `AkraBazziRecurrence`。
形式化陈述：isTheta_deriv_rpow_p_mul_one_add_smoothingFn {p : Real} (hp : p != 0) : (f
un x => ‖deriv (fun z => z ^ p * (1 + ε z)) x‖) =Θ[atTop] fun z => z ^ (p - 1)
参数：hp : p != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsTheta.norm_left`：∀ {α : Type u_1} {F : Type u_4} {E' : Typ
e u_6} [inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {g : α → F}   {f' : 
α → E'} {l : Filter…
· 使用定理 `Asymptotics.IsEquivalent.isTheta`：∀ {α : Type u_1} {β : Type u_2} [inst 
: NormedAddCommGroup β] {u v : α → β} {l : Filter α},   Asymptotics.IsEquivalent
 l u v → u =Θ[l] v
· 使用引理 `AkraBazziRecurrence.isEquivalent_deriv_rpow_p_mul_one_add_smoothingFn`：i
sEquivalent_deriv_rpow_p_mul_one_add_smoothingFn {p : Real} (hp : p != 0) : deri
v (fun z => z ^ p * (1 + ε z)) ~[atTop] fun z => p * z ^ (p…
· 使用定理 `Asymptotics.IsTheta.const_mul_left`：∀ {α : Type u_1} {F : Type u_4} {𝕜 :
 Type u_14} [inst : Norm F] [inst_1 : NormedField 𝕜] {g : α → F} {l : Filter α} 
  {c : 𝕜} {f : α → 𝕜}, c…
· 使用定理 `Asymptotics.isTheta_refl`：isTheta_refl (f : α -> E) (l : Filter α) : f =
Θ[l] f
-/
lemma isTheta_deriv_rpow_p_mul_one_add_smoothingFn {p : ℝ} (hp : p ≠ 0) :
    (fun x => ‖deriv (fun z => z ^ p * (1 + ε z)) x‖) =Θ[atTop] fun z => z ^ (p - 1) := by
  refine IsTheta.norm_left ?_
  calc (fun x => deriv (fun z => z ^ p * (1 + ε z)) x) =Θ[atTop] fun z => p * z ^ (p - 1) :=
      (isEquivalent_deriv_rpow_p_mul_one_add_smoothingFn hp).isTheta
    _ =Θ[atTop] fun z => z ^ (p - 1) := IsTheta.const_mul_left hp <| isTheta_refl _ _
/-
**AkraBazziRecurrence.growsPolynomially_deriv_rpow_p_mul_one_sub_smoothingFn** 是
 Mathlib 中的一个引理，位于命名空间 `AkraBazziRecurrence`。
形式化陈述：growsPolynomially_deriv_rpow_p_mul_one_sub_smoothingFn (p : Real) : GrowsP
olynomially fun x => ‖deriv (fun z => z ^ p * (1 - ε z)) x‖
参数：p : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.eventually_gt_atTop`：eventually_gt_atTop [Preorder α] [NoTopOrder
 α] (a : α) : forallᶠ x in atTop, a < x
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用引理 `AkraBazziRecurrence.eventually_deriv_one_sub_smoothingFn`：eventually_der
iv_one_sub_smoothingFn : deriv (fun x => 1 - ε x) =ᶠ[atTop] fun x => x⁻¹ / (log 
x ^ 2)
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用引理 `Mathlib.Meta.Positivity.div_nonneg_of_pos_of_nonneg`：div_nonneg_of_pos_o
f_nonneg [PosMulReflectLT α] (ha : 0 < a) (hb : 0 <= b) : 0 <= a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `inv_pos_of_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : Pa
rtialOrder G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a → 0 < a⁻¹
· 使用引理 `lt_trans`：lt_trans : a < b -> b < c -> a < c
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Even.pow_nonneg`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : LinearOr
der R] [IsOrderedRing R] [ExistsAddOfLE R] {n : ℕ},   Even n → ∀ (a : R), 0 ≤ a 
^ n
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `even_two_mul`：even_two_mul (a : α) : Even (2 * a)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Real.rpow_zero`：rpow_zero (x : Real) : x ^ (0 : Real) = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Real.norm_of_nonneg`：norm_of_nonneg (hr : 0 <= r) : ‖r‖ = r
（共 43 条，此处仅展示前 30 条）
-/
lemma growsPolynomially_deriv_rpow_p_mul_one_sub_smoothingFn (p : ℝ) :
    GrowsPolynomially fun x => ‖deriv (fun z => z ^ p * (1 - ε z)) x‖ := by
  cases eq_or_ne p 0 with
  | inl hp => -- p = 0
    have h₁ : (fun x => ‖deriv (fun z => z ^ p * (1 - ε z)) x‖)
        =ᶠ[atTop] fun z => z⁻¹ / (log z ^ 2) := by
      filter_upwards [eventually_deriv_one_sub_smoothingFn, eventually_gt_atTop 1] with x hx hx_pos
      have : 0 ≤ x⁻¹ / (log x ^ 2) := by positivity
      simp only [hp, Real.rpow_zero, one_mul, hx, Real.norm_of_nonneg this]
    refine GrowsPolynomially.congr_of_eventuallyEq h₁ ?_
    refine GrowsPolynomially.div (GrowsPolynomially.inv growsPolynomially_id)
      (GrowsPolynomially.pow 2 growsPolynomially_log ?_)
    filter_upwards [eventually_ge_atTop 1] with _ hx using log_nonneg hx
  | inr hp => -- p ≠ 0
    refine GrowsPolynomially.of_isTheta (growsPolynomially_rpow (p - 1))
      (isTheta_deriv_rpow_p_mul_one_sub_smoothingFn hp) ?_
    filter_upwards [eventually_gt_atTop 0] with _ _
    positivity
/-
**AkraBazziRecurrence.growsPolynomially_deriv_rpow_p_mul_one_add_smoothingFn** 是
 Mathlib 中的一个引理，位于命名空间 `AkraBazziRecurrence`。
形式化陈述：growsPolynomially_deriv_rpow_p_mul_one_add_smoothingFn (p : Real) : GrowsP
olynomially fun x => ‖deriv (fun z => z ^ p * (1 + ε z)) x‖
参数：p : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.eventually_gt_atTop`：eventually_gt_atTop [Preorder α] [NoTopOrder
 α] (a : α) : forallᶠ x in atTop, a < x
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用引理 `AkraBazziRecurrence.eventually_deriv_one_add_smoothingFn`：eventually_der
iv_one_add_smoothingFn : deriv (fun x => 1 + ε x) =ᶠ[atTop] fun x => -x⁻¹ / (log
 x ^ 2)
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用引理 `Mathlib.Meta.Positivity.div_nonneg_of_pos_of_nonneg`：div_nonneg_of_pos_o
f_nonneg [PosMulReflectLT α] (ha : 0 < a) (hb : 0 <= b) : 0 <= a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `inv_pos_of_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : Pa
rtialOrder G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a → 0 < a⁻¹
· 使用引理 `lt_trans`：lt_trans : a < b -> b < c -> a < c
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Even.pow_nonneg`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : LinearOr
der R] [IsOrderedRing R] [ExistsAddOfLE R] {n : ℕ},   Even n → ∀ (a : R), 0 ≤ a 
^ n
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `even_two_mul`：even_two_mul (a : α) : Even (2 * a)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Real.rpow_zero`：rpow_zero (x : Real) : x ^ (0 : Real) = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用引理 `neg_div`：neg_div (a b : R) : -b / a = -(b / a)
（共 45 条，此处仅展示前 30 条）
-/
lemma growsPolynomially_deriv_rpow_p_mul_one_add_smoothingFn (p : ℝ) :
    GrowsPolynomially fun x => ‖deriv (fun z => z ^ p * (1 + ε z)) x‖ := by
  cases eq_or_ne p 0 with
  | inl hp => -- p = 0
    have h₁ : (fun x => ‖deriv (fun z => z ^ p * (1 + ε z)) x‖)
        =ᶠ[atTop] fun z => z⁻¹ / (log z ^ 2) := by
      filter_upwards [eventually_deriv_one_add_smoothingFn, eventually_gt_atTop 1] with x hx hx_pos
      have : 0 ≤ x⁻¹ / (log x ^ 2) := by positivity
      simp only [neg_div, norm_neg, hp, Real.rpow_zero,
        one_mul, hx, Real.norm_of_nonneg this]
    refine GrowsPolynomially.congr_of_eventuallyEq h₁ ?_
    refine GrowsPolynomially.div (GrowsPolynomially.inv growsPolynomially_id)
      (GrowsPolynomially.pow 2 growsPolynomially_log ?_)
    filter_upwards [eventually_ge_atTop 1] with x hx using log_nonneg hx
  | inr hp => -- p ≠ 0
    refine GrowsPolynomially.of_isTheta (growsPolynomially_rpow (p - 1))
      (isTheta_deriv_rpow_p_mul_one_add_smoothingFn hp) ?_
    filter_upwards [eventually_gt_atTop 0] with _ _
    positivity

include R
/-
**AkraBazziRecurrence.isBigO_apply_r_sub_b** 是 Mathlib 中的一个引理，位于命名空间 `AkraBazziR
ecurrence`。
形式化陈述：isBigO_apply_r_sub_b (q : Real -> Real) (hq_diff : DifferentiableOn Real q
 (Set.Ioi 1)) (hq_poly : GrowsPolynomially fun x => ‖deriv q x‖) (i : α) : (fun 
n => q (r i n) - q (b i * n)) =O[atTop] fun n => (deriv q n) * (r i n - b i * n)
参数：q : Real -> Real；hq_diff : DifferentiableOn Real q (Set.Ioi 1)；hq_poly : Grow
sPolynomially fun x => ‖deriv q x‖；i : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `AkraBazziRecurrence.b_pos`：∀ {α : Type u_1} [inst : Fintype α] [inst_1 :
 Nonempty α] {T : ℕ → ℝ} {g : ℝ → ℝ} {a b : α → ℝ} {r : α → ℕ → ℕ}   (self : Akr
aBazziRecurrenc…
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `div_two_lt_of_pos`：∀ {α : Type u_2} [inst : Semifield α] [inst_1 : Parti
alOrder α] [PosMulReflectLT α] {a : α} [IsStrictOrderedRing α],   0 < a → a / 2 
< a
· 使用定理 `AkraBazziRecurrence.b_lt_one`：∀ {α : Type u_1} [inst : Fintype α] [inst_
1 : Nonempty α] {T : ℕ → ℝ} {g : ℝ → ℝ} {a b : α → ℝ} {r : α → ℕ → ℕ}   (self : 
AkraBazziRecurrenc…
· 使用引理 `div_le_div_of_nonneg_right`：div_le_div_of_nonneg_right (hab : a <= b) (h
c : 0 <= c) : a / c <= b / c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用引理 `AkraBazziRecurrence.min_bi_le`：min_bi_le {b : α -> Real} (i : α) : b (mi
n_bi b) <= b i
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Asymptotics.isBigO_iff`：isBigO_iff : f =O[l] g ↔ exists c : Real, forall
ᶠ x in l, ‖f x‖ <= c * ‖g x‖
· 使用定理 `Filter.Tendsto.const_mul_atTop`：∀ {α : Type u_1} {β : Type u_2} [inst : 
Semifield α] [inst_1 : LinearOrder α] [IsStrictOrderedRing α] {l : Filter β}   {
f : β → α} {r : α}, …
· 使用定理 `Filter.tendsto_id`：tendsto_id {x : Filter α} : Tendsto id x x
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.Eventually.natCast_atTop`：Filter.Eventually.natCast_atTop [Semiri
ng R] [PartialOrder R] [IsOrderedRing R] [Archimedean R] {p : R -> Prop} (h : fo
rallᶠ (x : R) in atTo…
· 使用定理 `Filter.Tendsto.eventually_gt_atTop`：∀ {α : Type u_3} {β : Type u_4} [ins
t : Preorder β] [NoTopOrder β] {f : α → β} {l : Filter α},   Filter.Tendsto f l 
Filter.atTop → ∀ (c : β)…
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `Filter.eventually_gt_atTop`：eventually_gt_atTop [Preorder α] [NoTopOrder
 α] (a : α) : forallᶠ x in atTop, a < x
· 使用定理 `Filter.eventually_ge_atTop`：eventually_ge_atTop [Preorder α] (a : α) : f
orallᶠ x in atTop, a <= x
（共 60 条，此处仅展示前 30 条）
-/
lemma isBigO_apply_r_sub_b (q : ℝ → ℝ) (hq_diff : DifferentiableOn ℝ q (Set.Ioi 1))
    (hq_poly : GrowsPolynomially fun x => ‖deriv q x‖) (i : α) :
    (fun n => q (r i n) - q (b i * n)) =O[atTop] fun n => (deriv q n) * (r i n - b i * n) := by
  let b' := b (min_bi b) / 2
  have hb_pos : 0 < b' := by have := R.b_pos (min_bi b); positivity
  have hb_lt_one : b' < 1 := calc b (min_bi b) / 2
    _ < b (min_bi b) := div_two_lt_of_pos (R.b_pos (min_bi b))
    _ < 1 := R.b_lt_one (min_bi b)
  have hb : b' ∈ Set.Ioo 0 1 := ⟨hb_pos, hb_lt_one⟩
  have hb' (i) : b' ≤ b i := calc b (min_bi b) / 2
    _ ≤ b i / 2 := by gcongr; aesop
    _ ≤ b i := le_of_lt <| div_two_lt_of_pos (R.b_pos i)
  obtain ⟨c₁, _, c₂, _, hq_poly⟩ := hq_poly b' hb
  rw [isBigO_iff]
  refine ⟨c₂, ?_⟩
  have h_tendsto : Tendsto (fun x => b' * x) atTop atTop :=
    Tendsto.const_mul_atTop hb_pos tendsto_id
  filter_upwards [hq_poly.natCast_atTop, R.eventually_bi_mul_le_r, eventually_ge_atTop R.n₀,
                  eventually_gt_atTop 0, (h_tendsto.eventually_gt_atTop 1).natCast_atTop] with
    n hn h_bi_le_r h_ge_n₀ h_n_pos h_bn
  rw [norm_mul, ← mul_assoc]
  refine Convex.norm_image_sub_le_of_norm_deriv_le
    (s := Set.Icc (b' * n) n) (fun z hz => ?diff) (fun z hz => (hn z hz).2)
    (convex_Icc _ _) ?mem_Icc <| ⟨h_bi_le_r i, by exact_mod_cast (le_of_lt (R.r_lt_n i n h_ge_n₀))⟩
  case diff =>
    refine hq_diff.differentiableAt (Ioi_mem_nhds ?_)
    calc 1 < b' * n := h_bn
         _ ≤ z := hz.1
  case mem_Icc =>
    refine ⟨by gcongr; exact hb' i, ?_⟩
    calc b i * n ≤ 1 * n := by gcongr; exact le_of_lt <| R.b_lt_one i
                 _ = n := by simp
/-
**AkraBazziRecurrence.rpow_p_mul_one_sub_smoothingFn_le** 是 Mathlib 中的一个引理，位于命名空
间 `AkraBazziRecurrence`。
形式化陈述：rpow_p_mul_one_sub_smoothingFn_le : forallᶠ (n : Nat) in atTop, forall i, 
(r i n) ^ (p a b) * (1 - ε (r i n)) <= (b i) ^ (p a b) * n ^ (p a b) * (1 - ε n)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.eventually_all`：eventually_all {ι : Sort*} [Finite ι] {l} {p : ι 
-> α -> Prop} : (forallᶠ x in l, forall i, p i x) ↔ forall i, forallᶠ x in l, p 
i x
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `DifferentiableOn.mul`：DifferentiableOn.mul (ha : DifferentiableOn 𝕜 a s)
 (hb : DifferentiableOn 𝕜 b s) : DifferentiableOn 𝕜 (a * b) s
· 使用定理 `DifferentiableOn.mono`：DifferentiableOn.mono (h : DifferentiableOn 𝕜 f t
) (st : s subseteq t) : DifferentiableOn 𝕜 f s
· 使用引理 `Real.differentiableOn_rpow_const`：differentiableOn_rpow_const (p : Real)
 : DifferentiableOn Real (fun x => (x : Real) ^ p) {0}ᶜ
· 使用引理 `Set.mem_compl_singleton_iff`：mem_compl_singleton_iff : a in ({b} : Set α
)ᶜ ↔ a != b
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Set.mem_Ioi`：∀ {α : Type u_1} [inst : Preorder α] {b x : α}, x ∈ Set.Ioi
 b ↔ b < x
· 使用引理 `AkraBazziRecurrence.differentiableOn_one_sub_smoothingFn`：differentiable
On_one_sub_smoothingFn : DifferentiableOn Real (fun z => 1 - ε z) (Set.Ioi 1)
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.eventually_gt_atTop`：eventually_gt_atTop [Preorder α] [NoTopOrder
 α] (a : α) : forallᶠ x in atTop, a < x
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `Filter.eventually_ne_atTop`：eventually_ne_atTop [Preorder α] [NoTopOrder
 α] (a : α) : forallᶠ x in atTop, x != a
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `deriv_fun_mul`：deriv_fun_mul (hc : DifferentiableAt 𝕜 c x) (hd : Differe
ntiableAt 𝕜 d x) : deriv (fun y => c y * d y) x = deriv c x * d x + c x * deriv 
d x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用引理 `AkraBazziRecurrence.differentiableAt_smoothingFn`：differentiableAt_smoot
hingFn {x : Real} (hx : 1 < x) : DifferentiableAt Real ε x
· 使用定理 `Asymptotics.IsBigO.add`：∀ {α : Type u_1} {F : Type u_4} {E' : Type u_6} 
[inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {g : α → F}   {l : Filter α
} {f₁ f₂ : α…
· 使用定理 `Asymptotics.IsBigO.mul`：∀ {α : Type u_1} {R : Type u_13} [inst : Seminor
medRing R] {S : Type u_17} [inst_1 : NormedRing S] [NormMulClass S]   {l : Filte
r α} {f₁ f₂ …
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
（共 126 条，此处仅展示前 30 条）
-/
lemma rpow_p_mul_one_sub_smoothingFn_le :
    ∀ᶠ (n : ℕ) in atTop, ∀ i, (r i n) ^ (p a b) * (1 - ε (r i n))
      ≤ (b i) ^ (p a b) * n ^ (p a b) * (1 - ε n) := by
  rw [Filter.eventually_all]
  intro i
  let q : ℝ → ℝ := fun x => x ^ (p a b) * (1 - ε x)
  have h_diff_q : DifferentiableOn ℝ q (Set.Ioi 1) := by
    refine DifferentiableOn.mul
      (DifferentiableOn.mono (differentiableOn_rpow_const _) fun z hz => ?_)
        differentiableOn_one_sub_smoothingFn
    rw [Set.mem_compl_singleton_iff]
    rw [Set.mem_Ioi] at hz
    exact ne_of_gt <| zero_lt_one.trans hz
  have h_deriv_q : deriv q =O[atTop] fun x => x ^ ((p a b) - 1) := calc deriv q
    _ = deriv fun x => (fun z => z ^ (p a b)) x * (fun z => 1 - ε z) x := by rfl
    _ =ᶠ[atTop] fun x => deriv (fun z => z ^ (p a b)) x * (1 - ε x) +
          x ^ (p a b) * deriv (fun z => 1 - ε z) x := by
      filter_upwards [eventually_ne_atTop 0, eventually_gt_atTop 1] with x hx hx'
      rw [deriv_fun_mul] <;> aesop
    _ =O[atTop] fun x => x ^ ((p a b) - 1) := by
      refine IsBigO.add ?left ?right
      case left => calc (fun x => deriv (fun z => z ^ (p a b)) x * (1 - ε x))
        _ =O[atTop] fun x => x ^ ((p a b) - 1) * (1 - ε x) :=
          IsBigO.mul (isBigO_deriv_rpow_const_atTop (p a b)) (isBigO_refl _ _)
        _ =O[atTop] fun x => x ^ ((p a b) - 1) * 1 :=
          IsBigO.mul (isBigO_refl _ _) isEquivalent_one_sub_smoothingFn_one.isBigO
        _ = fun x => x ^ ((p a b) - 1) := by ext; rw [mul_one]
      case right => calc (fun x => x ^ (p a b) * deriv (fun z => 1 - ε z) x)
        _ =O[atTop] (fun x => x ^ (p a b) * x⁻¹) :=
          IsBigO.mul (isBigO_refl _ _) isLittleO_deriv_one_sub_smoothingFn.isBigO
        _ =ᶠ[atTop] fun x => x ^ ((p a b) - 1) := by
          filter_upwards [eventually_gt_atTop 0] with x hx
          rw [← Real.rpow_neg_one, ← Real.rpow_add hx, ← sub_eq_add_neg]
  have h_main_norm : (fun (n : ℕ) => ‖q (r i n) - q (b i * n)‖)
      ≤ᶠ[atTop] fun (n : ℕ) => ‖(b i) ^ (p a b) * n ^ (p a b) * (ε (b i * n) - ε n)‖ := by
    refine IsLittleO.eventuallyLE ?_
    calc (fun (n : ℕ) => q (r i n) - q (b i * n))
      _ =O[atTop] fun n => (deriv q n) * (r i n - b i * n) :=
        R.isBigO_apply_r_sub_b q h_diff_q
          (growsPolynomially_deriv_rpow_p_mul_one_sub_smoothingFn (p a b)) i
      _ =o[atTop] fun n => (deriv q n) * (n / log n ^ 2) :=
        IsBigO.mul_isLittleO (isBigO_refl _ _) (R.dist_r_b i)
      _ =O[atTop] fun n => n ^ ((p a b) - 1) * (n / log n ^ 2) :=
        IsBigO.mul (IsBigO.natCast_atTop h_deriv_q) (isBigO_refl _ _)
      _ =ᶠ[atTop] fun n => n ^ (p a b) / (log n) ^ 2 := by
        filter_upwards [eventually_ne_atTop 0] with n hn
        have hn' : (n : ℝ) ≠ 0 := by positivity
        simp [← mul_div_assoc, ← Real.rpow_add_one hn']
      _ = fun (n : ℕ) => (n : ℝ) ^ (p a b) * (1 / (log n) ^ 2) := by
        simp_rw [mul_div, mul_one]
      _ =Θ[atTop] fun (n : ℕ) => (b i) ^ (p a b) * n ^ (p a b) * (1 / (log n) ^ 2) := by
        refine IsTheta.symm ?_
        simp_rw [mul_assoc]
        refine IsTheta.const_mul_left ?_ (isTheta_refl _ _)
        have := R.b_pos i; positivity
      _ =Θ[atTop] fun (n : ℕ) => (b i) ^ (p a b) * n ^ (p a b) * (ε (b i * n) - ε n) :=
        IsTheta.symm <| IsTheta.mul (isTheta_refl _ _) <| R.isTheta_smoothingFn_sub_self i
  have h_main : (fun (n : ℕ) => q (r i n) - q (b i * n))
      ≤ᶠ[atTop] fun (n : ℕ) => (b i) ^ (p a b) * n ^ (p a b) * (ε (b i * n) - ε n) := by
    calc (fun (n : ℕ) => q (r i n) - q (b i * n))
      _ ≤ᶠ[atTop] fun (n : ℕ) => ‖q (r i n) - q (b i * n)‖ := by
        filter_upwards with _ using le_norm_self _
      _ ≤ᶠ[atTop] fun (n : ℕ) => ‖(b i) ^ (p a b) * n ^ (p a b) * (ε (b i * n) - ε n)‖ :=
        h_main_norm
      _ =ᶠ[atTop] fun (n : ℕ) => (b i) ^ (p a b) * n ^ (p a b) * (ε (b i * n) - ε n) := by
        filter_upwards [eventually_gt_atTop ⌈(b i)⁻¹⌉₊, eventually_gt_atTop 1] with n hn hn'
        refine norm_of_nonneg ?_
        have h₁ := R.b_pos i
        have h₂ : 0 ≤ ε (b i * n) - ε n := by
          refine sub_nonneg_of_le <|
            (strictAntiOn_smoothingFn.le_iff_ge ?n_gt_one ?bn_gt_one).mpr ?le
          case n_gt_one => rwa [Set.mem_Ioi, Nat.one_lt_cast]
          case bn_gt_one =>
            calc 1 = b i * (b i)⁻¹ := by rw [mul_inv_cancel₀ (by positivity)]
              _ ≤ b i * ⌈(b i)⁻¹⌉₊ := by gcongr; exact Nat.le_ceil _
              _ < b i * n := by gcongr
          case le => calc b i * n
            _ ≤ 1 * n := by have := R.b_lt_one i; gcongr
            _ = n := by rw [one_mul]
        positivity
  filter_upwards [h_main] with n hn
  have h₁ : q (b i * n) + (b i) ^ (p a b) * n ^ (p a b) * (ε (b i * n) - ε n)
      = (b i) ^ (p a b) * n ^ (p a b) * (1 - ε n) := by
    have := R.b_pos i
    simp only [q, mul_rpow (by positivity : (0 : ℝ) ≤ b i) (by positivity : (0 : ℝ) ≤ n)]
    ring
  change q (r i n) ≤ (b i) ^ (p a b) * n ^ (p a b) * (1 - ε n)
  rw [← h₁, ← sub_le_iff_le_add']
  exact hn
/-
**AkraBazziRecurrence.rpow_p_mul_one_add_smoothingFn_ge** 是 Mathlib 中的一个引理，位于命名空
间 `AkraBazziRecurrence`。
形式化陈述：rpow_p_mul_one_add_smoothingFn_ge : forallᶠ (n : Nat) in atTop, forall i, 
(b i) ^ (p a b) * n ^ (p a b) * (1 + ε n) <= (r i n) ^ (p a b) * (1 + ε (r i n))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.eventually_all`：eventually_all {ι : Sort*} [Finite ι] {l} {p : ι 
-> α -> Prop} : (forallᶠ x in l, forall i, p i x) ↔ forall i, forallᶠ x in l, p 
i x
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `DifferentiableOn.mul`：DifferentiableOn.mul (ha : DifferentiableOn 𝕜 a s)
 (hb : DifferentiableOn 𝕜 b s) : DifferentiableOn 𝕜 (a * b) s
· 使用定理 `DifferentiableOn.mono`：DifferentiableOn.mono (h : DifferentiableOn 𝕜 f t
) (st : s subseteq t) : DifferentiableOn 𝕜 f s
· 使用引理 `Real.differentiableOn_rpow_const`：differentiableOn_rpow_const (p : Real)
 : DifferentiableOn Real (fun x => (x : Real) ^ p) {0}ᶜ
· 使用引理 `Set.mem_compl_singleton_iff`：mem_compl_singleton_iff : a in ({b} : Set α
)ᶜ ↔ a != b
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Set.mem_Ioi`：∀ {α : Type u_1} [inst : Preorder α] {b x : α}, x ∈ Set.Ioi
 b ↔ b < x
· 使用引理 `AkraBazziRecurrence.differentiableOn_one_add_smoothingFn`：differentiable
On_one_add_smoothingFn : DifferentiableOn Real (fun z => 1 + ε z) (Set.Ioi 1)
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.eventually_gt_atTop`：eventually_gt_atTop [Preorder α] [NoTopOrder
 α] (a : α) : forallᶠ x in atTop, a < x
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `Filter.eventually_ne_atTop`：eventually_ne_atTop [Preorder α] [NoTopOrder
 α] (a : α) : forallᶠ x in atTop, x != a
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `deriv_fun_mul`：deriv_fun_mul (hc : DifferentiableAt 𝕜 c x) (hd : Differe
ntiableAt 𝕜 d x) : deriv (fun y => c y * d y) x = deriv c x * d x + c x * deriv 
d x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用引理 `AkraBazziRecurrence.differentiableAt_smoothingFn`：differentiableAt_smoot
hingFn {x : Real} (hx : 1 < x) : DifferentiableAt Real ε x
· 使用定理 `Asymptotics.IsBigO.add`：∀ {α : Type u_1} {F : Type u_4} {E' : Type u_6} 
[inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {g : α → F}   {l : Filter α
} {f₁ f₂ : α…
· 使用定理 `Asymptotics.IsBigO.mul`：∀ {α : Type u_1} {R : Type u_13} [inst : Seminor
medRing R] {S : Type u_17} [inst_1 : NormedRing S] [NormMulClass S]   {l : Filte
r α} {f₁ f₂ …
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
（共 128 条，此处仅展示前 30 条）
-/
lemma rpow_p_mul_one_add_smoothingFn_ge :
    ∀ᶠ (n : ℕ) in atTop, ∀ i, (b i) ^ (p a b) * n ^ (p a b) * (1 + ε n)
      ≤ (r i n) ^ (p a b) * (1 + ε (r i n)) := by
  rw [Filter.eventually_all]
  intro i
  let q : ℝ → ℝ := fun x => x ^ (p a b) * (1 + ε x)
  have h_diff_q : DifferentiableOn ℝ q (Set.Ioi 1) := by
    refine DifferentiableOn.mul
        (DifferentiableOn.mono (differentiableOn_rpow_const _) fun z hz => ?_)
        differentiableOn_one_add_smoothingFn
    rw [Set.mem_compl_singleton_iff]
    rw [Set.mem_Ioi] at hz
    exact ne_of_gt <| zero_lt_one.trans hz
  have h_deriv_q : deriv q =O[atTop] fun x => x ^ ((p a b) - 1) :=
    calc deriv q
      _ = deriv fun x => (fun z => z ^ (p a b)) x * (fun z => 1 + ε z) x := by rfl
      _ =ᶠ[atTop] fun x => deriv (fun z => z ^ (p a b)) x * (1 + ε x)
          + x ^ (p a b) * deriv (fun z => 1 + ε z) x := by
        filter_upwards [eventually_ne_atTop 0, eventually_gt_atTop 1] with x hx hx'
        rw [deriv_fun_mul] <;> aesop
      _ =O[atTop] fun x => x ^ ((p a b) - 1) := by
        refine IsBigO.add ?left ?right
        case left =>
          calc (fun x => deriv (fun z => z ^ (p a b)) x * (1 + ε x))
            _ =O[atTop] fun x => x ^ ((p a b) - 1) * (1 + ε x) :=
              IsBigO.mul (isBigO_deriv_rpow_const_atTop (p a b)) (isBigO_refl _ _)
            _ =O[atTop] fun x => x ^ ((p a b) - 1) * 1 :=
              IsBigO.mul (isBigO_refl _ _) isEquivalent_one_add_smoothingFn_one.isBigO
            _ = fun x => x ^ ((p a b) - 1) := by ext; rw [mul_one]
        case right =>
          calc (fun x => x ^ (p a b) * deriv (fun z => 1 + ε z) x)
            _ =O[atTop] (fun x => x ^ (p a b) * x⁻¹) :=
              IsBigO.mul (isBigO_refl _ _) isLittleO_deriv_one_add_smoothingFn.isBigO
            _ =ᶠ[atTop] fun x => x ^ ((p a b) - 1) := by
              filter_upwards [eventually_gt_atTop 0] with x hx
              rw [← Real.rpow_neg_one, ← Real.rpow_add hx, ← sub_eq_add_neg]
  have h_main_norm : (fun (n : ℕ) => ‖q (r i n) - q (b i * n)‖)
      ≤ᶠ[atTop] fun (n : ℕ) => ‖(b i) ^ (p a b) * n ^ (p a b) * (ε (b i * n) - ε n)‖ := by
    refine IsLittleO.eventuallyLE ?_
    calc
      (fun (n : ℕ) => q (r i n) - q (b i * n))
          =O[atTop] fun n => (deriv q n) * (r i n - b i * n) := by
            exact R.isBigO_apply_r_sub_b q h_diff_q
              (growsPolynomially_deriv_rpow_p_mul_one_add_smoothingFn (p a b)) i
        _ =o[atTop] fun n => (deriv q n) * (n / log n ^ 2) :=
          IsBigO.mul_isLittleO (isBigO_refl _ _) (R.dist_r_b i)
        _ =O[atTop] fun n => n ^ ((p a b) - 1) * (n / log n ^ 2) :=
          IsBigO.mul (IsBigO.natCast_atTop h_deriv_q) (isBigO_refl _ _)
        _ =ᶠ[atTop] fun n => n ^ (p a b) / (log n) ^ 2 := by
          filter_upwards [eventually_ne_atTop 0] with n hn
          have hn' : (n : ℝ) ≠ 0 := by positivity
          simp [← mul_div_assoc, ← Real.rpow_add_one hn']
        _ = fun (n : ℕ) => (n : ℝ) ^ (p a b) * (1 / (log n) ^ 2) := by simp_rw [mul_div, mul_one]
        _ =Θ[atTop] fun (n : ℕ) => (b i) ^ (p a b) * n ^ (p a b) * (1 / (log n) ^ 2) := by
          refine IsTheta.symm ?_
          simp_rw [mul_assoc]
          refine IsTheta.const_mul_left ?_ (isTheta_refl _ _)
          have := R.b_pos i; positivity
        _ =Θ[atTop] fun (n : ℕ) => (b i) ^ (p a b) * n ^ (p a b) * (ε (b i * n) - ε n) :=
          IsTheta.symm <| IsTheta.mul (isTheta_refl _ _) <| R.isTheta_smoothingFn_sub_self i
  have h_main : (fun (n : ℕ) => q (b i * n) - q (r i n))
      ≤ᶠ[atTop] fun (n : ℕ) => (b i) ^ (p a b) * n ^ (p a b) * (ε (b i * n) - ε n) := by
    calc (fun (n : ℕ) => q (b i * n) - q (r i n))
      _ ≤ᶠ[atTop] fun (n : ℕ) => ‖q (r i n) - q (b i * n)‖ := by
        filter_upwards with _; rw [norm_sub_rev]; exact le_norm_self _
      _ ≤ᶠ[atTop] fun (n : ℕ) => ‖(b i) ^ (p a b) * n ^ (p a b) * (ε (b i * n) - ε n)‖ :=
        h_main_norm
      _ =ᶠ[atTop] fun (n : ℕ) => (b i) ^ (p a b) * n ^ (p a b) * (ε (b i * n) - ε n) := by
        filter_upwards [eventually_gt_atTop ⌈(b i)⁻¹⌉₊, eventually_gt_atTop 1] with n hn hn'
        refine norm_of_nonneg ?_
        have h₁ := R.b_pos i
        have h₂ : 0 ≤ ε (b i * n) - ε n := by
          refine sub_nonneg_of_le <|
            (strictAntiOn_smoothingFn.le_iff_ge ?n_gt_one ?bn_gt_one).mpr ?le
          case n_gt_one =>
            change 1 < (n : ℝ)
            rw [Nat.one_lt_cast]
            exact hn'
          case bn_gt_one =>
            calc 1 = b i * (b i)⁻¹ := by rw [mul_inv_cancel₀ (by positivity)]
                _ ≤ b i * ⌈(b i)⁻¹⌉₊ := by gcongr; exact Nat.le_ceil _
                _ < b i * n := by gcongr
          case le => calc b i * n
            _ ≤ 1 * n := by have := R.b_lt_one i; gcongr
            _ = n := by rw [one_mul]
        positivity
  filter_upwards [h_main] with n hn
  have h₁ : q (b i * n) - (b i) ^ (p a b) * n ^ (p a b) * (ε (b i * n) - ε n)
      = (b i) ^ (p a b) * n ^ (p a b) * (1 + ε n) := by
    have := R.b_pos i
    simp only [q, mul_rpow (by positivity : (0 : ℝ) ≤ b i) (by positivity : (0 : ℝ) ≤ n)]
    ring
  change (b i) ^ (p a b) * n ^ (p a b) * (1 + ε n) ≤ q (r i n)
  rw [← h₁, sub_le_iff_le_add', ← sub_le_iff_le_add]
  exact hn

/-!
### Main proof

This final section proves the Akra-Bazzi theorem.
-/

/-- The main proof of the upper-bound part of the Akra-Bazzi theorem. The factor `1 - ε n` does not
change the asymptotic order, but it is needed for the induction step to go through. -/
/-
**AkraBazziRecurrence.T_isBigO_smoothingFn_mul_asympBound** 是 Mathlib 中的一个引理，位于命
名空间 `AkraBazziRecurrence`。
形式化陈述：T_isBigO_smoothingFn_mul_asympBound : T =O[atTop] (fun n => (1 - ε n) * as
ympBound g a b n)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Asymptotics.isBigO_nat_atTop_induction_of_eventually_pos`：isBigO_nat_atT
op_induction_of_eventually_pos {f g : Nat -> Real} (hf : forallᶠ n in atTop, 0 <
= f n) (hg : forallᶠ n in atTop, 0 < g n) (hre…
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用引理 `AkraBazziRecurrence.T_nonneg`：T_nonneg (n : Nat) : 0 <= T n
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用引理 `AkraBazziRecurrence.eventually_one_sub_smoothingFn_pos`：eventually_one_s
ub_smoothingFn_pos : forallᶠ (n : Nat) in atTop, 0 < 1 - ε n
· 使用引理 `AkraBazziRecurrence.eventually_asympBound_pos`：eventually_asympBound_pos
 : forallᶠ (n : Nat) in atTop, 0 < asympBound g a b n
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `AkraBazziRecurrence.bi_min_div_two_pos`：bi_min_div_two_pos : 0 < b (min_
bi b) / 2
· 使用引理 `AkraBazziRecurrence.eventually_atTop_sumTransform_ge`：eventually_atTop_s
umTransform_ge : exists c > 0, forallᶠ (n : Nat) in atTop, forall i, c * g n <= 
sumTransform (p a b) g (r i n) n
· 使用定理 `Filter.eventually_ge_atTop`：eventually_ge_atTop [Preorder α] (a : α) : f
orallᶠ x in atTop, a <= x
· 使用引理 `AkraBazziRecurrence.eventually_bi_mul_le_r`：eventually_bi_mul_le_r : for
allᶠ (n : Nat) in atTop, forall i, (b (min_bi b) / 2) * n <= r i n
· 使用引理 `AkraBazziRecurrence.eventually_one_sub_smoothingFn_gt_const`：eventually_
one_sub_smoothingFn_gt_const (c : Real) (hc : c < 1) : forallᶠ (n : Nat) in atTo
p, c < 1 - ε n
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_lt_true`：isNNRat_lt_true [Semiring α] [Line
arOrder α] [IsStrictOrderedRing α] : {a b : α} -> {na nb : Nat} -> {da db : Nat}
 -> IsNNRat a na da -> IsN…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_div`：∀ {α : Type u} [inst : DivisionSemirin
g α] {a b : α} {cn cd : ℕ},   Mathlib.Meta.NormNum.IsNNRat (a * b⁻¹) cn cd → Mat
hlib.Meta.NormNum.IsNN…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_mul`：isNNRat_mul {α} [Semiring α] {f : α ->
 α -> α} {a b : α} {na nb nc : Nat} {da db dc k : Nat} : f = HMul.hMul -> IsNNRa
t a na da -> IsNNRat b…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isNNRat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsN
NRat a n 1
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_inv_pos`：isNNRat_inv_pos {α} [DivisionSemir
ing α] [CharZero α] {a : α} {n d : Nat} : IsNNRat a (Nat.succ n) d -> IsNNRat a⁻
¹ d (Nat.succ n)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用引理 `AkraBazziRecurrence.rpow_p_mul_one_sub_smoothingFn_le`：rpow_p_mul_one_su
b_smoothingFn_le : forallᶠ (n : Nat) in atTop, forall i, (r i n) ^ (p a b) * (1 
- ε (r i n)) <= (b i) ^ (p a b) * n ^ (p a …
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Nat.le_ceil`：le_ceil (a : R) : a <= ⌈a⌉₊
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
（共 124 条，此处仅展示前 30 条）

--- 原说明 ---
The main proof of the upper-bound part of the Akra-Bazzi theorem. The factor `1 
- ε n` does not
change the asymptotic order, but it is needed for the induction step to go throu
gh.
-/
lemma T_isBigO_smoothingFn_mul_asympBound :
    T =O[atTop] (fun n => (1 - ε n) * asympBound g a b n) := by
  refine isBigO_nat_atTop_induction_of_eventually_pos ?_ ?_ ?_
  · exact Eventually.of_forall fun h => R.T_nonneg _
  · filter_upwards [R.eventually_asympBound_pos, eventually_one_sub_smoothingFn_pos] with n hn hn₂
    positivity
  let b' := b (min_bi b) / 2
  have hb_pos : 0 < b' := R.bi_min_div_two_pos
  obtain ⟨c₁, hc₁, h_sumTransform_aux⟩ := R.eventually_atTop_sumTransform_ge
  filter_upwards [eventually_ge_atTop R.n₀] with n₀ n₀_ge_Rn₀
  refine ⟨2 * c₁⁻¹, ?_⟩
  filter_upwards [
    eventually_ge_atTop n₀,
    -- bound1
    R.rpow_p_mul_one_sub_smoothingFn_le,
    -- h_smoothing_pos
    eventually_one_sub_smoothingFn_pos,
    -- h_sumTransform
    h_sumTransform_aux,
    -- h_smoothing_gt_half
    eventually_one_sub_smoothingFn_gt_const (1 / 2) (by norm_num),
    -- h_bi_le_r
    R.eventually_bi_mul_le_r,
    -- n₀_div_le_n
    eventually_ge_atTop ⌈n₀ / b'⌉₊]
      with n hn bound1 h_smoothing_pos h_sumTransform h_smoothing_gt_half h_bi_le_r n₀_div_le_n
  --have n₀_le_bn : n₀ ≤ b' * n := by
  --  sorry
  have n₀_le_r : ∀ i, n₀ ≤ r i n := by
    intro i
    exact_mod_cast
      calc n₀ ≤ b' * n := by
                have : (n₀ : ℝ) / b' ≤ n := by
                  exact_mod_cast calc
                    (n₀ : ℝ) / b' ≤ ⌈n₀ / b'⌉₊ := Nat.le_ceil (↑n₀ / b')
                    _ ≤ n := by exact_mod_cast n₀_div_le_n
                rwa [div_le_iff₀, mul_comm] at this
                grind only
        _ ≤ r i n := by grind
  have r_le_n : ∀ i, r i n < n := by grind [AkraBazziRecurrence]
  intro C hC h_ind
  have C_pos : 0 ≤ C := by grind [inv_pos]
  have g_pos : 0 ≤ g n := R.g_nonneg n (by positivity)
  calc T n
    _ = (∑ i, a i * T (r i n)) + g n := R.h_rec n (by grind)
    _ ≤ (∑ i, a i * (C * ((1 - ε (r i n)) * asympBound g a b (r i n)))) + g n := by
      -- Apply the induction hypothesis
      gcongr (∑ i, a i * ?_) + g n with i _
      · exact le_of_lt <| R.a_pos _
      · exact h_ind (r i n) (by grind)
    _ = (∑ i, a i * (C * ((1 - ε (r i n)) * ((r i n) ^ (p a b)
              * (1 + (∑ u ∈ range (r i n), g u / u ^ ((p a b) + 1))))))) + g n := by
      simp_rw [asympBound_def']
    _ = (∑ i, C * a i * ((r i n) ^ (p a b) * (1 - ε (r i n))
              * ((1 + (∑ u ∈ range (r i n), g u / u ^ ((p a b) + 1)))))) + g n := by
      congr; ext; ring
    _ ≤ (∑ i, C * a i * ((b i) ^ (p a b) * n ^ (p a b) * (1 - ε n)
              * ((1 + (∑ u ∈ range (r i n), g u / u ^ ((p a b) + 1)))))) + g n := by
      gcongr (∑ i, C * a i * (?_
          * ((1 + (∑ u ∈ range (r i n), g u / u ^ ((p a b) + 1)))))) + g n with i
      · positivity [R.a_pos i]
      · refine add_nonneg zero_le_one <| Finset.sum_nonneg fun j _ => ?_
        rw [div_nonneg_iff]
        exact Or.inl ⟨R.g_nonneg j (by positivity), by positivity⟩
      · grind
    _ = (∑ i, C * a i * ((b i) ^ (p a b) * n ^ (p a b) * (1 - ε n)
              * ((1 + ((∑ u ∈ range n, g u / u ^ ((p a b) + 1))
              - (∑ u ∈ Finset.Ico (r i n) n, g u / u ^ ((p a b) + 1))))))) + g n := by
      congr; ext i; congr
      refine eq_sub_of_add_eq ?_
      rw [add_comm]
      exact add_eq_of_eq_sub <| Finset.sum_Ico_eq_sub _
        <| le_of_lt <| R.r_lt_n i n <| n₀_ge_Rn₀.trans hn
    _ = (∑ i, C * a i * ((b i) ^ (p a b) * (1 - ε n) * ((n ^ (p a b)
              * (1 + (∑ u ∈ range n, g u / u ^ ((p a b) + 1)))
              - n ^ (p a b) * (∑ u ∈ Finset.Ico (r i n) n, g u / u ^ ((p a b) + 1))))))
              + g n := by
      congr; ext; ring
    _ = (∑ i, C * a i * ((b i) ^ (p a b) * (1 - ε n)
              * ((asympBound g a b n - sumTransform (p a b) g (r i n) n)))) + g n := by
      simp_rw [asympBound_def', sumTransform_def]
    _ ≤ (∑ i, C * a i * ((b i) ^ (p a b) * (1 - ε n)
              * ((asympBound g a b n - c₁ * g n)))) + g n := by
      gcongr with i
      · positivity [R.a_pos i]
      · positivity [R.b_pos i]
      · exact h_sumTransform i
    _ = (∑ i, C * (1 - ε n) * ((asympBound g a b n - c₁ * g n))
              * (a i * (b i) ^ (p a b))) + g n := by
      congr; ext; ring
    _ = C * (1 - ε n) * (asympBound g a b n - c₁ * g n) + g n := by
      rw [← Finset.mul_sum, R.sumCoeffsExp_p_eq_one, mul_one]
    _ = C * (1 - ε n) * asympBound g a b n + (1 - C * c₁ * (1 - ε n)) * g n := by ring
    _ ≤ C * (1 - ε n) * asympBound g a b n + 0 := by
      gcongr
      refine mul_nonpos_of_nonpos_of_nonneg ?_ g_pos
      rw [sub_nonpos]
      calc 1
        _ ≤ 2 * (c₁⁻¹ * c₁) * (1 / 2) := by
          rw [inv_mul_cancel₀ (by positivity : c₁ ≠ 0)]; norm_num
        _ = (2 * c₁⁻¹) * c₁ * (1 / 2) := by ring
        _ ≤ C * c₁ * (1 - ε n) := by gcongr
    _ = C * ((1 - ε n) * asympBound g a b n) := by ring

/-- The main proof of the lower-bound part of the Akra-Bazzi theorem. The factor `1 + ε n` does not
change the asymptotic order, but it is needed for the induction step to go through. -/
/-
**AkraBazziRecurrence.smoothingFn_mul_asympBound_isBigO_T** 是 Mathlib 中的一个引理，位于命
名空间 `AkraBazziRecurrence`。
形式化陈述：smoothingFn_mul_asympBound_isBigO_T : (fun (n : Nat) => (1 + ε n) * asympB
ound g a b n) =O[atTop] T
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Asymptotics.isBigO_nat_atTop_induction_of_eventually_pos`：isBigO_nat_atT
op_induction_of_eventually_pos {f g : Nat -> Real} (hf : forallᶠ n in atTop, 0 <
= f n) (hg : forallᶠ n in atTop, 0 < g n) (hre…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用引理 `AkraBazziRecurrence.eventually_one_add_smoothingFn_pos`：eventually_one_a
dd_smoothingFn_pos : forallᶠ (n : Nat) in atTop, 0 < 1 + ε n
· 使用引理 `AkraBazziRecurrence.eventually_asympBound_pos`：eventually_asympBound_pos
 : forallᶠ (n : Nat) in atTop, 0 < asympBound g a b n
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `AkraBazziRecurrence.T_pos`：∀ {α : Type u_1} [inst : Fintype α] {T : ℕ → 
ℝ} {g : ℝ → ℝ} {a b : α → ℝ} {r : α → ℕ → ℕ} [inst_1 : Nonempty α]   (R : AkraBa
zziRecurrence T…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `AkraBazziRecurrence.bi_min_div_two_pos`：bi_min_div_two_pos : 0 < b (min_
bi b) / 2
· 使用引理 `AkraBazziRecurrence.eventually_atTop_sumTransform_le`：eventually_atTop_s
umTransform_le : exists c > 0, forallᶠ (n : Nat) in atTop, forall i, sumTransfor
m (p a b) g (r i n) n <= c * g n
· 使用定理 `Filter.eventually_ge_atTop`：eventually_ge_atTop [Preorder α] (a : α) : f
orallᶠ x in atTop, a <= x
· 使用引理 `AkraBazziRecurrence.eventually_bi_mul_le_r`：eventually_bi_mul_le_r : for
allᶠ (n : Nat) in atTop, forall i, (b (min_bi b) / 2) * n <= r i n
· 使用引理 `AkraBazziRecurrence.eventually_one_sub_smoothingFn_gt_const`：eventually_
one_sub_smoothingFn_gt_const (c : Real) (hc : c < 1) : forallᶠ (n : Nat) in atTo
p, c < 1 - ε n
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_lt_true`：isNNRat_lt_true [Semiring α] [Line
arOrder α] [IsStrictOrderedRing α] : {a b : α} -> {na nb : Nat} -> {da db : Nat}
 -> IsNNRat a na da -> IsN…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_div`：∀ {α : Type u} [inst : DivisionSemirin
g α] {a b : α} {cn cd : ℕ},   Mathlib.Meta.NormNum.IsNNRat (a * b⁻¹) cn cd → Mat
hlib.Meta.NormNum.IsNN…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_mul`：isNNRat_mul {α} [Semiring α] {f : α ->
 α -> α} {a b : α} {na nb nc : Nat} {da db dc k : Nat} : f = HMul.hMul -> IsNNRa
t a na da -> IsNNRat b…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isNNRat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsN
NRat a n 1
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_inv_pos`：isNNRat_inv_pos {α} [DivisionSemir
ing α] [CharZero α] {a : α} {n d : Nat} : IsNNRat a (Nat.succ n) d -> IsNNRat a⁻
¹ d (Nat.succ n)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用引理 `AkraBazziRecurrence.rpow_p_mul_one_add_smoothingFn_ge`：rpow_p_mul_one_ad
d_smoothingFn_ge : forallᶠ (n : Nat) in atTop, forall i, (b i) ^ (p a b) * n ^ (
p a b) * (1 + ε n) <= (r i n) ^ (p a b) * (…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Nat.le_ceil`：le_ceil (a : R) : a <= ⌈a⌉₊
（共 107 条，此处仅展示前 30 条）

--- 原说明 ---
The main proof of the lower-bound part of the Akra-Bazzi theorem. The factor `1 
+ ε n` does not
change the asymptotic order, but it is needed for the induction step to go throu
gh.
-/
lemma smoothingFn_mul_asympBound_isBigO_T :
    (fun (n : ℕ) => (1 + ε n) * asympBound g a b n) =O[atTop] T := by
  refine isBigO_nat_atTop_induction_of_eventually_pos ?_ ?_ ?_
  · filter_upwards [R.eventually_asympBound_pos, eventually_one_add_smoothingFn_pos] with n hn hn₂
    positivity
  · exact Eventually.of_forall fun h => R.T_pos _
  let b' := b (min_bi b) / 2
  have hb_pos : 0 < b' := R.bi_min_div_two_pos
  obtain ⟨c₁, hc₁, h_sumTransform_aux⟩ := R.eventually_atTop_sumTransform_le
  filter_upwards [eventually_ge_atTop R.n₀] with n₀ n₀_ge_Rn₀
  refine ⟨2 * c₁, ?_⟩
  filter_upwards [
    eventually_ge_atTop n₀,
    -- bound2
    R.rpow_p_mul_one_add_smoothingFn_ge,
    -- h_smoothing_pos
    eventually_one_add_smoothingFn_pos,
    -- h_sumTransform
    h_sumTransform_aux,
    -- h_smoothing_gt_half
    eventually_one_sub_smoothingFn_gt_const (1 / 2) (by norm_num),
    -- h_bi_le_r
    R.eventually_bi_mul_le_r,
    -- n₀_div_le_n
    eventually_ge_atTop ⌈n₀ / b'⌉₊,
    -- h_exp
    eventually_ge_atTop ⌈exp 1⌉₊]
      with n hn bound2 h_smoothing_pos h_sumTransform h_smoothing_gt_half h_bi_le_r n₀_div_le_n
        h_exp
  have n₀_le_r : ∀ i, n₀ ≤ r i n := by
    intro i
    exact_mod_cast
      calc n₀ ≤ b' * n := by
                have : (n₀ : ℝ) / b' ≤ n := by
                  exact_mod_cast calc
                    (n₀ : ℝ) / b' ≤ ⌈n₀ / b'⌉₊ := Nat.le_ceil (↑n₀ / b')
                    _ ≤ n := by exact_mod_cast n₀_div_le_n
                rwa [div_le_iff₀, mul_comm] at this
                grind only
        _ ≤ r i n := by grind
  have r_le_n : ∀ i, r i n < n := by grind [AkraBazziRecurrence]
  intro C hC h_ind
  have C_pos : 0 ≤ C := by grind [inv_pos]
  have g_pos : 0 ≤ g n := R.g_nonneg n (by positivity)
  calc C * T n
    _ = C * ((∑ i, a i * T (r i n)) + g n) := by grind [AkraBazziRecurrence]
    _ = (∑ i, a i * (C * T (r i n))) + C * g n := by rw [mul_add, mul_sum]; grind
    _ ≥ (∑ i, a i * ((1 + ε (r i n)) * asympBound g a b (r i n))) + C * g n := by
      gcongr (∑ i, a i * ?_) + C * g n with i _
      · exact le_of_lt <| R.a_pos _
      · exact h_ind (r i n) (by grind)
    _ = (∑ i, a i * ((1 + ε (r i n)) * ((r i n) ^ (p a b)
          * (1 + (∑ u ∈ range (r i n), g u / u ^ ((p a b) + 1)))))) + C * g n := by
      simp_rw [asympBound_def']
    _ = (∑ i, a i * ((r i n) ^ (p a b) * (1 + ε (r i n))
              * ((1 + (∑ u ∈ range (r i n), g u / u ^ ((p a b) + 1)))))) + C * g n := by
      congr; ext; ring
    _ ≥ (∑ i, a i * ((b i) ^ (p a b) * n ^ (p a b) * (1 + ε n)
              * ((1 + (∑ u ∈ range (r i n), g u / u ^ ((p a b) + 1)))))) + C * g n := by
      gcongr (∑ i, a i * (?_ *
          ((1 + (∑ u ∈ range (r i n), g u / u ^ ((p a b) + 1)))))) + C * g n with i
      · positivity [R.a_pos i]
      · refine add_nonneg zero_le_one <| Finset.sum_nonneg fun j _ => ?_
        rw [div_nonneg_iff]
        exact Or.inl ⟨R.g_nonneg j (by positivity), by positivity⟩
      · exact bound2 i
    _ = (∑ i, a i * ((b i) ^ (p a b) * n ^ (p a b) * (1 + ε n)
              * ((1 + ((∑ u ∈ range n, g u / u ^ ((p a b) + 1))
              - (∑ u ∈ Finset.Ico (r i n) n, g u / u ^ ((p a b) + 1))))))) + C * g n := by
      congr; ext i; congr
      refine eq_sub_of_add_eq ?_
      rw [add_comm]
      exact add_eq_of_eq_sub <| Finset.sum_Ico_eq_sub _
        <| le_of_lt <| R.r_lt_n i n <| n₀_ge_Rn₀.trans hn
    _ = (∑ i, a i * ((b i) ^ (p a b) * (1 + ε n)
              * ((n ^ (p a b) * (1 + (∑ u ∈ range n, g u / u ^ ((p a b) + 1)))
              - n ^ (p a b) * (∑ u ∈ Finset.Ico (r i n) n, g u / u ^ ((p a b) + 1))))))
              + C * g n := by
      congr; ext; ring
    _ = (∑ i, a i * ((b i) ^ (p a b) * (1 + ε n)
              * ((asympBound g a b n - sumTransform (p a b) g (r i n) n)))) + C * g n := by
      simp_rw [asympBound_def', sumTransform_def]
    _ ≥ (∑ i, a i * ((b i) ^ (p a b) * (1 + ε n)
              * ((asympBound g a b n - c₁ * g n)))) + C * g n := by
      gcongr with i
      · positivity [R.a_pos i]
      · positivity [R.b_pos i]
      · exact h_sumTransform i
    _ = (∑ i, (1 + ε n) * ((asympBound g a b n - c₁ * g n))
              * (a i * (b i) ^ (p a b))) + C * g n := by grind only
    _ = (1 + ε n) * (asympBound g a b n - c₁ * g n) + C * g n := by
          rw [← Finset.mul_sum, R.sumCoeffsExp_p_eq_one, mul_one]
    _ = (1 + ε n) * asympBound g a b n + (C - c₁ * (1 + ε n)) * g n := by ring
    _ ≥ (1 + ε n) * asympBound g a b n + 0 := by
      gcongr
      #adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
      (replacing grind's canonicalizer with a type-directed normalizer), `grind` closed this
      goal. It is not yet clear whether this is due to defeq abuse in Mathlib or a problem in
      the new canonicalizer; a minimization would help. The original proof was:
      `exact mul_nonneg (by grind +splitIndPred) g_pos` -/
      have : 1 + ε ↑n < 2 := by grind
      exact mul_nonneg (by grw [sub_nonneg, this, mul_comm, hC]) g_pos
    _ = ((1 + ε n) * asympBound g a b n) := by ring

/-- The **Akra-Bazzi theorem**: `T ∈ O(n^p (1 + ∑_u^n g(u) / u^{p+1}))` -/
/-
**AkraBazziRecurrence.isBigO_asympBound** 是 Mathlib 中的一个定理，位于命名空间 `AkraBazziRecu
rrence`。
形式化陈述：isBigO_asympBound : T =O[atTop] asympBound g a b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AkraBazziRecurrence.T_isBigO_smoothingFn_mul_asympBound`：T_isBigO_smooth
ingFn_mul_asympBound : T =O[atTop] (fun n => (1 - ε n) * asympBound g a b n)
· 使用定理 `Asymptotics.IsBigO.mul`：∀ {α : Type u_1} {R : Type u_13} [inst : Seminor
medRing R] {S : Type u_17} [inst_1 : NormedRing S] [NormMulClass S]   {l : Filte
r α} {f₁ f₂ …
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Asymptotics.isBigO_const_of_tendsto`：isBigO_const_of_tendsto {y : E''} (
h : Tendsto f'' l (𝓝 y)) {c : F''} (hc : c != 0) : f'' =O[l] fun _x => c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.comp_def`：∀ {α : Sort u_1} {β : Sort u_2} {δ : Sort u_3} (f : β
 → δ) (g : α → β), f ∘ g = fun x => f (g x)
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Asymptotics.IsEquivalent.tendsto_const`：∀ {α : Type u_1} {β : Type u_2} 
[inst : NormedAddCommGroup β] {u : α → β} {l : Filter α} {c : β},   Asymptotics.
IsEquivalent l u (Function.c…
· 使用引理 `AkraBazziRecurrence.isEquivalent_one_sub_smoothingFn_one`：isEquivalent_o
ne_sub_smoothingFn_one : (fun x => 1 - ε x) ~[atTop] (fun _ => (1 : Real))
· 使用定理 `tendsto_natCast_atTop_atTop`：tendsto_natCast_atTop_atTop [Semiring R] [P
artialOrder R] [IsOrderedRing R] [Archimedean R] : Tendsto ((↑) : Nat -> R) atTo
p atTop
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Asymptotics.isBigO_refl`：isBigO_refl (f : α -> E) (l : Filter α) : f =O[
l] f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The **Akra-Bazzi theorem**: `T ∈ O(n^p (1 + ∑_u^n g(u) / u^{p+1}))`
-/
theorem isBigO_asympBound : T =O[atTop] asympBound g a b := by
  calc T
    _ =O[atTop] (fun n => (1 - ε n) * asympBound g a b n) := by
      exact R.T_isBigO_smoothingFn_mul_asympBound
    _ =O[atTop] (fun n => 1 * asympBound g a b n) := by
      refine IsBigO.mul (isBigO_const_of_tendsto (y := 1) ?_ one_ne_zero) (isBigO_refl _ _)
      rw [← Function.comp_def (fun n => 1 - ε n) Nat.cast]
      exact Tendsto.comp isEquivalent_one_sub_smoothingFn_one.tendsto_const
        tendsto_natCast_atTop_atTop
    _ = asympBound g a b := by simp

/-- The **Akra-Bazzi theorem**: `T ∈ Ω(n^p (1 + ∑_u^n g(u) / u^{p+1}))` -/
/-
**AkraBazziRecurrence.isBigO_symm_asympBound** 是 Mathlib 中的一个定理，位于命名空间 `AkraBazz
iRecurrence`。
形式化陈述：isBigO_symm_asympBound : asympBound g a b =O[atTop] T
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Asymptotics.IsEquivalent.mul`：∀ {α : Type u_1} {β : Type u_3} [inst : No
rmedField β] {t u v w : α → β} {l : Filter α},   Asymptotics.IsEquivalent l t u 
→ Asymptotics.IsEq…
· 使用定理 `Asymptotics.IsEquivalent.symm`：∀ {α : Type u_1} {β : Type u_2} [inst : N
ormedAddCommGroup β] {u v : α → β} {l : Filter α},   Asymptotics.IsEquivalent l 
u v → Asymptotics.I…
· 使用定理 `Function.const_def`：const_def {y : β} : (fun _ : α => y) = const α y
· 使用定理 `Asymptotics.isEquivalent_const_iff_tendsto`：isEquivalent_const_iff_tends
to {c : β} (h : c != 0) : u ~[l] const _ c ↔ Tendsto u l (𝓝 c)
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.comp_def`：∀ {α : Sort u_1} {β : Sort u_2} {δ : Sort u_3} (f : β
 → δ) (g : α → β), f ∘ g = fun x => f (g x)
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Asymptotics.IsEquivalent.tendsto_const`：∀ {α : Type u_1} {β : Type u_2} 
[inst : NormedAddCommGroup β] {u : α → β} {l : Filter α} {c : β},   Asymptotics.
IsEquivalent l u (Function.c…
· 使用引理 `AkraBazziRecurrence.isEquivalent_one_add_smoothingFn_one`：isEquivalent_o
ne_add_smoothingFn_one : (fun x => 1 + ε x) ~[atTop] (fun _ => (1 : Real))
· 使用定理 `tendsto_natCast_atTop_atTop`：tendsto_natCast_atTop_atTop [Semiring R] [P
artialOrder R] [IsOrderedRing R] [Archimedean R] : Tendsto ((↑) : Nat -> R) atTo
p atTop
· 使用定理 `Asymptotics.IsEquivalent.refl`：∀ {α : Type u_1} {β : Type u_2} [inst : N
ormedAddCommGroup β] {u : α → β} {l : Filter α}, Asymptotics.IsEquivalent l u u
· 使用引理 `AkraBazziRecurrence.smoothingFn_mul_asympBound_isBigO_T`：smoothingFn_mul
_asympBound_isBigO_T : (fun (n : Nat) => (1 + ε n) * asympBound g a b n) =O[atTo
p] T

--- 原说明 ---
The **Akra-Bazzi theorem**: `T ∈ Ω(n^p (1 + ∑_u^n g(u) / u^{p+1}))`
-/
theorem isBigO_symm_asympBound : asympBound g a b =O[atTop] T := by
  calc asympBound g a b
    _ = (fun n => 1 * asympBound g a b n) := by simp
    _ ~[atTop] (fun n => (1 + ε n) * asympBound g a b n) := by
      refine IsEquivalent.mul (IsEquivalent.symm ?_) IsEquivalent.refl
      rw [Function.const_def, isEquivalent_const_iff_tendsto one_ne_zero,
        ← Function.comp_def (fun n => 1 + ε n) Nat.cast]
      exact Tendsto.comp isEquivalent_one_add_smoothingFn_one.tendsto_const
        tendsto_natCast_atTop_atTop
    _ =O[atTop] T := R.smoothingFn_mul_asympBound_isBigO_T

/-- The **Akra-Bazzi theorem**: `T ∈ Θ(n^p (1 + ∑_u^n g(u) / u^{p+1}))` -/
/-
**AkraBazziRecurrence.isTheta_asympBound** 是 Mathlib 中的一个定理，位于命名空间 `AkraBazziRec
urrence`。
形式化陈述：isTheta_asympBound : T =Θ[atTop] asympBound g a b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AkraBazziRecurrence.isBigO_asympBound`：isBigO_asympBound : T =O[atTop] a
sympBound g a b
· 使用定理 `AkraBazziRecurrence.isBigO_symm_asympBound`：isBigO_symm_asympBound : asy
mpBound g a b =O[atTop] T

--- 原说明 ---
The **Akra-Bazzi theorem**: `T ∈ Θ(n^p (1 + ∑_u^n g(u) / u^{p+1}))`
-/
theorem isTheta_asympBound : T =Θ[atTop] asympBound g a b :=
  ⟨R.isBigO_asympBound, R.isBigO_symm_asympBound⟩

end AkraBazziRecurrence

