/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg, Snir Broshi
-/
module

public import Mathlib.Analysis.Complex.IsIntegral
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.RingTheory.Polynomial.RationalRoot
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Tactic.Peel
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Qify

/-! # Niven's Theorem

This file proves Niven's theorem, stating that the only rational angles _in degrees_ which
also have rational cosines, are 0, 30 degrees, and 90 degrees - up to reflection and shifts
by π. Equivalently, the only rational numbers that occur as `cos(π * p / q)` are the five
values `{-1, -1/2, 0, 1/2, 1}`.
-/

public section

namespace IsIntegral

variable {α R : Type*} [DivisionRing α] [CharZero α] {q : ℚ} {x : α}

@[simp]
/-
**IsIntegral.ratCast_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsIntegral`。
形式化陈述：ratCast_iff : IsIntegral Int (q : α) ↔ IsIntegral Int q
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isIntegral_algebraMap_iff`：isIntegral_algebraMap_iff [Algebra A B] [IsSc
alarTower R A B] {x : A} (hAB : Function.Injective (algebraMap A B)) : IsIntegra
l R (algebraMap…
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `instFaithfulSMul_1`：∀ (R : Type u_1) (A : Type u_2) [inst : CommRing R] 
[inst_1 : Semiring A] [inst_2 : Algebra R A] [IsSimpleRing R]   [Nontrivial A], 
Faithful…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `instNontrivialOfCharZero`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [
CharZero α], Nontrivial α
-/
theorem ratCast_iff : IsIntegral ℤ (q : α) ↔ IsIntegral ℤ q :=
  isIntegral_algebraMap_iff (FaithfulSMul.algebraMap_injective ℚ α)
/-
**IsIntegral.exists_int_iff_exists_rat** 是 Mathlib 中的一个定理，位于命名空间 `IsIntegral`。
形式化陈述：exists_int_iff_exists_rat (h₁ : IsIntegral Int x) : (exists q : Rat, x = q
) ↔ exists k : Int, x = k
参数：h₁ : IsIntegral Int x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_intCast`：eq_intCast [FunLike F Int α] [RingHomClass F Int α] (f : F) 
(n : Int) : f n = n
· 使用定理 `Rat.cast_intCast`：cast_intCast (n : Int) : ((n : Rat) : α) = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IsIntegrallyClosed.algebraMap_eq_of_integral`：algebraMap_eq_of_integral 
[IsIntegrallyClosed R] {x : K} : IsIntegral R x -> exists y : R, algebraMap R K 
y = x
· 使用定理 `IsIntegralClosure.of_isIntegrallyClosed`：∀ (R : Type u_1) (S : Type u_2)
 [inst : CommRing R] [inst_1 : CommRing S] (K : Type u_3) [inst_2 : CommRing K] 
  [inst_3 : Algebra R K] [ifr…
· 使用定理 `UniqueFactorizationMonoid.instIsIntegrallyClosed`：∀ {A : Type u_1} [inst
 : CommRing A] [IsDomain A] [UniqueFactorizationMonoid A], IsIntegrallyClosed A
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `PrincipalIdealRing.to_uniqueFactorizationMonoid`：∀ {R : Type u} [inst : 
CommRing R] [IsDomain R] [IsPrincipalIdealRing R], UniqueFactorizationMonoid R
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `AddMonoid.fg_of_addGroup_fg`：∀ {G : Type u_3} [inst : AddGroup G] [AddGr
oup.FG G], AddMonoid.FG G
· 使用定理 `AddGroup.instFGInt`：AddGroup.FG ℤ
· 使用定理 `IsIntegral.ratCast_iff`：ratCast_iff : IsIntegral Int (q : α) ↔ IsIntegra
l Int q
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
-/
theorem exists_int_iff_exists_rat (h₁ : IsIntegral ℤ x) : (∃ q : ℚ, x = q) ↔ ∃ k : ℤ, x = k := by
  refine ⟨?_, fun ⟨w, h⟩ ↦ ⟨w, by simp [h]⟩⟩
  rintro ⟨q, rfl⟩
  rw [ratCast_iff] at h₁
  peel IsIntegrallyClosed.algebraMap_eq_of_integral h₁ with h
  simp [← h]

end IsIntegral

variable {θ : ℝ}

open Real

section IsIntegral

namespace Complex

/-
**Complex.exp_rat_mul_pi_mul_I_pow_two_mul_den** 是 Mathlib 中的一个引理，位于命名空间 `Comple
x`。
形式化陈述：exp_rat_mul_pi_mul_I_pow_two_mul_den (q : Rat) : exp (q * π * I) ^ (2 * q.
den) = 1
参数：q : Rat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Rat.num_div_den`：num_div_den (r : Rat) : (r.num : Rat) / (r.den : Rat) =
 r
· 使用定理 `Complex.exp_nat_mul`：∀ (x : ℂ) (n : ℕ), Complex.exp (↑n * x) = Complex.e
xp x ^ n
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Rat.cast_div`：∀ {α : Type u_3} [inst : DivisionRing α] [CharZero α] (p q
 : ℚ), ↑(p / q) = ↑p / ↑q
· 使用定理 `Rat.cast_intCast`：cast_intCast (n : Int) : ((n : Rat) : α) = n
· 使用定理 `Rat.cast_natCast`：cast_natCast (n : Nat) : ((n : Rat) : α) = n
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
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval`：mul_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al * l₂.eval = l.eval) : x₁ *…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.atom_eq_eval`：atom_eq_eval [GroupWithZero M]
 (x : M) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval₃`：mul_eq_eval₃ [CommGroupWithZer
o M] {a₁ : Int × M} (a₂ : Int × M) {l₁ l₂ l : NF M} (h : (a₁ ::ᵣ l₁).eval * l₂.e
val = l.eval) : (a₁ ::ᵣ l₁).ev…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval`：div_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al / l₂.eval = l.eval) : x₁ /…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval₁`：div_eq_eval₁ [CommGroupWithZer
o M] (a₁ : Int × M) {a₂ : Int × M} {l₁ l₂ l : NF M} (h : l₁.eval / (a₂ ::ᵣ l₂).e
val = l.eval) : (a₁ ::ᵣ l₁).ev…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.one_div_eq_eval`：one_div_eq_eval [CommGroupW
ithZero M] (l : NF M) : 1 / l.eval = (l⁻¹).eval
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval₂`：mul_eq_eval₂ [CommGroupWithZer
o M] (r₁ r₂ : Int) (x : M) {l₁ l₂ l : NF M} (h : l₁.eval * l₂.eval = l.eval) : (
(r₁, x) ::ᵣ l₁).eval * ((r₂, x…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons_mul_eval`：eval_cons_mul_eval [Comm
GroupWithZero M] (n : Int) (e : M) {L l l' : NF M} (h : L.eval * l.eval = l'.eva
l) : ((n, e) ::ᵣ L).eval * l.eval = …
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_mul_eval_cons`：eval_mul_eval_cons [Comm
GroupWithZero M] (n : Int) (e : M) {L l l' : NF M} (h : L.eval * l.eval = l'.eva
l) : L.eval * ((n, e) ::ᵣ l).eval = …
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_mul_eval_cons_zero`：eval_mul_eval_cons_
zero [CommGroupWithZero M] {e : M} {L l l' l₀ : NF M} (h : L.eval * l.eval = l'.
eval) (h' : ((0, e) ::ᵣ l).eval = l₀.eval…
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
（共 50 条，此处仅展示前 30 条）
-/
lemma exp_rat_mul_pi_mul_I_pow_two_mul_den (q : ℚ) : exp (q * π * I) ^ (2 * q.den) = 1 := by
  nth_rw 1 [← q.num_div_den, ← exp_nat_mul]
  push_cast
  rw [show 2 * q.den * (q.num / q.den * π * I) = q.num * (2 * π * I) by field,
    exp_int_mul_two_pi_mul_I]

/-- `exp(q * π * I)` for `q : ℚ` is integral over `ℤ`. -/
/-
**Complex.isIntegral_exp_rat_mul_pi_mul_I** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：isIntegral_exp_rat_mul_pi_mul_I (q : Rat) : IsIntegral Int exp q * π * I
参数：q : Rat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsIntegral.of_pow`：IsIntegral.of_pow [Algebra R B] {x : B} {n : Nat} (hn
 : 0 < n) (hx : IsIntegral R <| x ^ n) : IsIntegral R x
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Nat.mul_pos`：∀ {n m : ℕ}, 0 < n → 0 < m → 0 < n * m
· 使用定理 `zero_lt_two`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : Part
ialOrder α] [ZeroLEOneClass α] [NeZero 1] [AddLeftMono α],   0 < 2
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Rat.den_pos`：∀ (self : ℚ), 0 < self.den
· 使用定理 `isIntegral_one`：isIntegral_one [Algebra R B] : IsIntegral R (1 : B)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Complex.exp_rat_mul_pi_mul_I_pow_two_mul_den`：exp_rat_mul_pi_mul_I_pow_t
wo_mul_den (q : Rat) : exp (q * π * I) ^ (2 * q.den) = 1

--- 原说明 ---
`exp(q * π * I)` for `q : ℚ` is integral over `ℤ`.
-/
theorem isIntegral_exp_rat_mul_pi_mul_I (q : ℚ) : IsIntegral ℤ <| exp <| q * π * I := by
  refine .of_pow (Nat.mul_pos zero_lt_two q.den_pos) ?_
  exact exp_rat_mul_pi_mul_I_pow_two_mul_den _ ▸ isIntegral_one

/-- `exp(-(q * π) * I)` for `q : ℚ` is integral over `ℤ`. -/
/-
**Complex.isIntegral_exp_neg_rat_mul_pi_mul_I** 是 Mathlib 中的一个定理，位于命名空间 `Complex
`。
形式化陈述：isIntegral_exp_neg_rat_mul_pi_mul_I (q : Rat) : IsIntegral Int exp -(q * π
) * I
参数：q : Rat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Rat.cast_neg`：∀ {α : Type u_3} [inst : DivisionRing α] (q : ℚ), ↑(-q) = 
-↑q
· 使用定理 `Complex.isIntegral_exp_rat_mul_pi_mul_I`：isIntegral_exp_rat_mul_pi_mul_I
 (q : Rat) : IsIntegral Int exp q * π * I

--- 原说明 ---
`exp(-(q * π) * I)` for `q : ℚ` is integral over `ℤ`.
-/
theorem isIntegral_exp_neg_rat_mul_pi_mul_I (q : ℚ) :
    IsIntegral ℤ <| exp <| -(q * π) * I := by
  simpa using isIntegral_exp_rat_mul_pi_mul_I (-q)

/-- `2 sin(q * π)` for `q : ℚ` is integral over `ℤ`, using the complex `sin` function. -/
/-
**Complex.isIntegral_two_mul_sin_rat_mul_pi** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：isIntegral_two_mul_sin_rat_mul_pi (q : Rat) : IsIntegral Int 2 * sin (q * 
π)
参数：q : Rat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.sin.eq_1`：∀ (z : ℂ), Complex.sin z = (Complex.exp (-z * Complex.
I) - Complex.exp (z * Complex.I)) * Complex.I / 2
· 使用引理 `mul_div_cancel₀`：mul_div_cancel₀ (a : G₀) (hb : b != 0) : b * (a / b) = 
a
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `IsIntegral.mul`：∀ {R : Type u_1} {A : Type u_2} [inst : CommRing R] [ins
t_1 : CommRing A] [inst_2 : Algebra R A] {x y : A},   IsIntegral R x → IsIntegra
l R …
· 使用定理 `IsIntegral.sub`：∀ {R : Type u_1} {A : Type u_2} [inst : CommRing R] [ins
t_1 : CommRing A] [inst_2 : Algebra R A] {x y : A},   IsIntegral R x → IsIntegra
l R …
· 使用定理 `Complex.isIntegral_exp_neg_rat_mul_pi_mul_I`：isIntegral_exp_neg_rat_mul_
pi_mul_I (q : Rat) : IsIntegral Int exp -(q * π) * I
· 使用定理 `Complex.isIntegral_exp_rat_mul_pi_mul_I`：isIntegral_exp_rat_mul_pi_mul_I
 (q : Rat) : IsIntegral Int exp q * π * I
· 使用定理 `Complex.isIntegral_int_I`：isIntegral_int_I : IsIntegral Int I

--- 原说明 ---
`2 sin(q * π)` for `q : ℚ` is integral over `ℤ`, using the complex `sin` functio
n.
-/
theorem isIntegral_two_mul_sin_rat_mul_pi (q : ℚ) : IsIntegral ℤ <| 2 * sin (q * π) := by
  rw [sin.eq_1, mul_div_cancel₀ _ two_ne_zero]
  exact (isIntegral_exp_neg_rat_mul_pi_mul_I q).sub (isIntegral_exp_rat_mul_pi_mul_I q)
    |>.mul isIntegral_int_I

/-- `2 cos(q * π)` for `q : ℚ` is integral over `ℤ`, using the complex `cos` function. -/
/-
**Complex.isIntegral_two_mul_cos_rat_mul_pi** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：isIntegral_two_mul_cos_rat_mul_pi (q : Rat) : IsIntegral Int 2 * cos (q * 
π)
参数：q : Rat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.cos.eq_1`：∀ (z : ℂ), Complex.cos z = (Complex.exp (z * Complex.I
) + Complex.exp (-z * Complex.I)) / 2
· 使用引理 `mul_div_cancel₀`：mul_div_cancel₀ (a : G₀) (hb : b != 0) : b * (a / b) = 
a
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `IsIntegral.add`：∀ {R : Type u_1} {A : Type u_2} [inst : CommRing R] [ins
t_1 : CommRing A] [inst_2 : Algebra R A] {x y : A},   IsIntegral R x → IsIntegra
l R …
· 使用定理 `Complex.isIntegral_exp_rat_mul_pi_mul_I`：isIntegral_exp_rat_mul_pi_mul_I
 (q : Rat) : IsIntegral Int exp q * π * I
· 使用定理 `Complex.isIntegral_exp_neg_rat_mul_pi_mul_I`：isIntegral_exp_neg_rat_mul_
pi_mul_I (q : Rat) : IsIntegral Int exp -(q * π) * I

--- 原说明 ---
`2 cos(q * π)` for `q : ℚ` is integral over `ℤ`, using the complex `cos` functio
n.
-/
theorem isIntegral_two_mul_cos_rat_mul_pi (q : ℚ) : IsIntegral ℤ <| 2 * cos (q * π) := by
  rw [cos.eq_1, mul_div_cancel₀ _ two_ne_zero]
  exact (isIntegral_exp_rat_mul_pi_mul_I q).add (isIntegral_exp_neg_rat_mul_pi_mul_I q)

/-- `sin(q * π)` for `q : ℚ` is algebraic over `ℤ`, using the complex `sin` function. -/
/-
**Complex.isAlgebraic_sin_rat_mul_pi** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：isAlgebraic_sin_rat_mul_pi (q : Rat) : IsAlgebraic Int sin q * π
参数：q : Rat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAlgebraic.of_mul`：IsAlgebraic.of_mul [NoZeroDivisors R] {y z : S} (hy 
: y in nonZeroDivisors S) (alg_y : IsAlgebraic R y) (alg_yz : IsAlgebraic R (y *
 z)) : I…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_intCast`：eq_intCast [FunLike F Int α] [RingHomClass F Int α] (f : F) 
(n : Int) : f n = n
· 使用定理 `Int.cast_ofNat`：cast_ofNat (n : Nat) [n.AtLeastTwo] : ((ofNat(n) : Int) 
: R) = ofNat(n)
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Complex.instNontrivial`：Nontrivial ℂ
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `isAlgebraic_algebraMap`：isAlgebraic_algebraMap [Nontrivial R] (x : R) : 
IsAlgebraic R (algebraMap R A x)
· 使用定理 `IsIntegral.isAlgebraic`：IsIntegral.isAlgebraic [Nontrivial R] {x : A} : 
IsIntegral R x -> IsAlgebraic R x
· 使用定理 `Complex.isIntegral_two_mul_sin_rat_mul_pi`：isIntegral_two_mul_sin_rat_mu
l_pi (q : Rat) : IsIntegral Int 2 * sin (q * π)

--- 原说明 ---
`sin(q * π)` for `q : ℚ` is algebraic over `ℤ`, using the complex `sin` function
.
-/
theorem isAlgebraic_sin_rat_mul_pi (q : ℚ) : IsAlgebraic ℤ <| sin <| q * π :=
  .of_mul (by simp) (isAlgebraic_algebraMap _) (isIntegral_two_mul_sin_rat_mul_pi q).isAlgebraic

/-- `cos(q * π)` for `q : ℚ` is algebraic over `ℤ`, using the complex `cos` function. -/
/-
**Complex.isAlgebraic_cos_rat_mul_pi** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：isAlgebraic_cos_rat_mul_pi (q : Rat) : IsAlgebraic Int cos q * π
参数：q : Rat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAlgebraic.of_mul`：IsAlgebraic.of_mul [NoZeroDivisors R] {y z : S} (hy 
: y in nonZeroDivisors S) (alg_y : IsAlgebraic R y) (alg_yz : IsAlgebraic R (y *
 z)) : I…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_intCast`：eq_intCast [FunLike F Int α] [RingHomClass F Int α] (f : F) 
(n : Int) : f n = n
· 使用定理 `Int.cast_ofNat`：cast_ofNat (n : Nat) [n.AtLeastTwo] : ((ofNat(n) : Int) 
: R) = ofNat(n)
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Complex.instNontrivial`：Nontrivial ℂ
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `isAlgebraic_algebraMap`：isAlgebraic_algebraMap [Nontrivial R] (x : R) : 
IsAlgebraic R (algebraMap R A x)
· 使用定理 `IsIntegral.isAlgebraic`：IsIntegral.isAlgebraic [Nontrivial R] {x : A} : 
IsIntegral R x -> IsAlgebraic R x
· 使用定理 `Complex.isIntegral_two_mul_cos_rat_mul_pi`：isIntegral_two_mul_cos_rat_mu
l_pi (q : Rat) : IsIntegral Int 2 * cos (q * π)

--- 原说明 ---
`cos(q * π)` for `q : ℚ` is algebraic over `ℤ`, using the complex `cos` function
.
-/
theorem isAlgebraic_cos_rat_mul_pi (q : ℚ) : IsAlgebraic ℤ <| cos <| q * π :=
  .of_mul (by simp) (isAlgebraic_algebraMap _) (isIntegral_two_mul_cos_rat_mul_pi q).isAlgebraic

/-- `tan(q * π)` for `q : ℚ` is algebraic over `ℤ`, using the complex `tan` function. -/
/-
**Complex.isAlgebraic_tan_rat_mul_pi** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：isAlgebraic_tan_rat_mul_pi (q : Rat) : IsAlgebraic Int tan q * π
参数：q : Rat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAlgebraic.mul`：∀ {R : Type u_1} {S : Type u_2} [inst : CommRing R] [in
st_1 : CommRing S] [inst_2 : Algebra R S] [NoZeroDivisors R]   {a b : S}, IsAlge
braic…
· 使用定理 `Complex.isAlgebraic_sin_rat_mul_pi`：isAlgebraic_sin_rat_mul_pi (q : Rat)
 : IsAlgebraic Int sin q * π
· 使用定理 `IsAlgebraic.inv`：∀ {R : Type u} [inst : CommRing R] {K : Type u_2} [inst
_1 : Field K] [inst_2 : Algebra R K] {x : K},   IsAlgebraic R x → IsAlgebraic R 
x⁻¹
· 使用定理 `Complex.isAlgebraic_cos_rat_mul_pi`：isAlgebraic_cos_rat_mul_pi (q : Rat)
 : IsAlgebraic Int cos q * π

--- 原说明 ---
`tan(q * π)` for `q : ℚ` is algebraic over `ℤ`, using the complex `tan` function
.
-/
theorem isAlgebraic_tan_rat_mul_pi (q : ℚ) : IsAlgebraic ℤ <| tan <| q * π :=
  (isAlgebraic_sin_rat_mul_pi q).mul (isAlgebraic_cos_rat_mul_pi q).inv

end Complex

namespace Real

/-- `2 sin(q * π)` for `q : ℚ` is integral over `ℤ`, using the real `sin` function. -/
/-
**Real.isIntegral_two_mul_sin_rat_mul_pi** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：isIntegral_two_mul_sin_rat_mul_pi (q : Rat) : IsIntegral Int 2 * sin (q * 
π)
参数：q : Rat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `isIntegral_algebraMap_iff`：isIntegral_algebraMap_iff [Algebra A B] [IsSc
alarTower R A B] {x : A} (hAB : Function.Injective (algebraMap A B)) : IsIntegra
l R (algebraMap…
· 使用定理 `RCLike.ofReal_injective`：ofReal_injective : Function.Injective ((↑) : Re
al -> K)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.ofReal_mul`：ofReal_mul (r s : Real) : ((r * s : Real) : Complex)
 = r * s
· 使用定理 `Complex.ofReal_sin`：ofReal_sin (x : Real) : (Real.sin x : Complex) = sin
 x

--- 原说明 ---
`2 sin(q * π)` for `q : ℚ` is integral over `ℤ`, using the real `sin` function.
-/
theorem isIntegral_two_mul_sin_rat_mul_pi (q : ℚ) : IsIntegral ℤ <| 2 * sin (q * π) :=
  isIntegral_algebraMap_iff (B := ℂ) RCLike.ofReal_injective |>.mp <| by
    simp [Complex.isIntegral_two_mul_sin_rat_mul_pi]

/-- `2 cos(q * π)` for `q : ℚ` is integral over `ℤ`, using the real `cos` function. -/
/-
**Real.isIntegral_two_mul_cos_rat_mul_pi** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：isIntegral_two_mul_cos_rat_mul_pi (q : Rat) : IsIntegral Int 2 * cos (q * 
π)
参数：q : Rat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `isIntegral_algebraMap_iff`：isIntegral_algebraMap_iff [Algebra A B] [IsSc
alarTower R A B] {x : A} (hAB : Function.Injective (algebraMap A B)) : IsIntegra
l R (algebraMap…
· 使用定理 `RCLike.ofReal_injective`：ofReal_injective : Function.Injective ((↑) : Re
al -> K)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.ofReal_mul`：ofReal_mul (r s : Real) : ((r * s : Real) : Complex)
 = r * s
· 使用定理 `Complex.ofReal_cos`：ofReal_cos (x : Real) : (Real.cos x : Complex) = cos
 x

--- 原说明 ---
`2 cos(q * π)` for `q : ℚ` is integral over `ℤ`, using the real `cos` function.
-/
theorem isIntegral_two_mul_cos_rat_mul_pi (q : ℚ) : IsIntegral ℤ <| 2 * cos (q * π) :=
  isIntegral_algebraMap_iff (B := ℂ) RCLike.ofReal_injective |>.mp <| by
    simp [Complex.isIntegral_two_mul_cos_rat_mul_pi]

/-- `sin(q * π)` for `q : ℚ` is algebraic over `ℤ`, using the real `sin` function. -/
/-
**Real.isAlgebraic_sin_rat_mul_pi** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：isAlgebraic_sin_rat_mul_pi (q : Rat) : IsAlgebraic Int sin q * π
参数：q : Rat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAlgebraic.of_mul`：IsAlgebraic.of_mul [NoZeroDivisors R] {y z : S} (hy 
: y in nonZeroDivisors S) (alg_y : IsAlgebraic R y) (alg_yz : IsAlgebraic R (y *
 z)) : I…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_intCast`：eq_intCast [FunLike F Int α] [RingHomClass F Int α] (f : F) 
(n : Int) : f n = n
· 使用定理 `Int.cast_ofNat`：cast_ofNat (n : Nat) [n.AtLeastTwo] : ((ofNat(n) : Int) 
: R) = ofNat(n)
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `isAlgebraic_algebraMap`：isAlgebraic_algebraMap [Nontrivial R] (x : R) : 
IsAlgebraic R (algebraMap R A x)
· 使用定理 `IsIntegral.isAlgebraic`：IsIntegral.isAlgebraic [Nontrivial R] {x : A} : 
IsIntegral R x -> IsAlgebraic R x
· 使用定理 `Real.isIntegral_two_mul_sin_rat_mul_pi`：isIntegral_two_mul_sin_rat_mul_p
i (q : Rat) : IsIntegral Int 2 * sin (q * π)

--- 原说明 ---
`sin(q * π)` for `q : ℚ` is algebraic over `ℤ`, using the real `sin` function.
-/
theorem isAlgebraic_sin_rat_mul_pi (q : ℚ) : IsAlgebraic ℤ <| sin <| q * π :=
  .of_mul (by simp) (isAlgebraic_algebraMap _) (isIntegral_two_mul_sin_rat_mul_pi q).isAlgebraic

/-- `cos(q * π)` for `q : ℚ` is algebraic over `ℤ`, using the real `cos` function. -/
/-
**Real.isAlgebraic_cos_rat_mul_pi** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：isAlgebraic_cos_rat_mul_pi (q : Rat) : IsAlgebraic Int cos q * π
参数：q : Rat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAlgebraic.of_mul`：IsAlgebraic.of_mul [NoZeroDivisors R] {y z : S} (hy 
: y in nonZeroDivisors S) (alg_y : IsAlgebraic R y) (alg_yz : IsAlgebraic R (y *
 z)) : I…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_intCast`：eq_intCast [FunLike F Int α] [RingHomClass F Int α] (f : F) 
(n : Int) : f n = n
· 使用定理 `Int.cast_ofNat`：cast_ofNat (n : Nat) [n.AtLeastTwo] : ((ofNat(n) : Int) 
: R) = ofNat(n)
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `isAlgebraic_algebraMap`：isAlgebraic_algebraMap [Nontrivial R] (x : R) : 
IsAlgebraic R (algebraMap R A x)
· 使用定理 `IsIntegral.isAlgebraic`：IsIntegral.isAlgebraic [Nontrivial R] {x : A} : 
IsIntegral R x -> IsAlgebraic R x
· 使用定理 `Real.isIntegral_two_mul_cos_rat_mul_pi`：isIntegral_two_mul_cos_rat_mul_p
i (q : Rat) : IsIntegral Int 2 * cos (q * π)

--- 原说明 ---
`cos(q * π)` for `q : ℚ` is algebraic over `ℤ`, using the real `cos` function.
-/
theorem isAlgebraic_cos_rat_mul_pi (q : ℚ) : IsAlgebraic ℤ <| cos <| q * π :=
  .of_mul (by simp) (isAlgebraic_algebraMap _) (isIntegral_two_mul_cos_rat_mul_pi q).isAlgebraic

/-- `tan(q * π)` for `q : ℚ` is algebraic over `ℤ`, using the real `tan` function. -/
/-
**Real.isAlgebraic_tan_rat_mul_pi** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：isAlgebraic_tan_rat_mul_pi (q : Rat) : IsAlgebraic Int tan q * π
参数：q : Rat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isAlgebraic_algebraMap_iff`：isAlgebraic_algebraMap_iff {a : S} (h : Func
tion.Injective (algebraMap S A)) : IsAlgebraic R (algebraMap S A a) ↔ IsAlgebrai
c R a
· 使用定理 `RCLike.ofReal_injective`：ofReal_injective : Function.Injective ((↑) : Re
al -> K)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.ofReal_tan`：ofReal_tan (x : Real) : (Real.tan x : Complex) = tan
 x
· 使用定理 `Complex.ofReal_mul`：ofReal_mul (r s : Real) : ((r * s : Real) : Complex)
 = r * s

--- 原说明 ---
`tan(q * π)` for `q : ℚ` is algebraic over `ℤ`, using the real `tan` function.
-/
theorem isAlgebraic_tan_rat_mul_pi (q : ℚ) : IsAlgebraic ℤ <| tan <| q * π :=
  isAlgebraic_algebraMap_iff (A := ℂ) RCLike.ofReal_injective |>.mp <| by
    simp [Complex.isAlgebraic_tan_rat_mul_pi]

end Real

end IsIntegral

/-- **Niven's theorem**: The only rational values of `cos` that occur at rational multiples of π
are `{-1, -1/2, 0, 1/2, 1}`. -/
/-
**niven** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：niven (hθ : exists r : Rat, θ = r * π) (hcos : exists q : Rat, cos θ = q) 
: cos θ in ({-1, -1 / 2, 0, 1 / 2, 1} : Set Real)
参数：hθ : exists r : Rat, θ = r * π；hcos : exists q : Rat, cos θ = q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsIntegral.exists_int_iff_exists_rat`：exists_int_iff_exists_rat (h₁ : Is
Integral Int x) : (exists q : Rat, x = q) ↔ exists k : Int, x = k
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Real.isIntegral_two_mul_cos_rat_mul_pi`：isIntegral_two_mul_cos_rat_mul_p
i (q : Rat) : IsIntegral Int 2 * cos (q * π)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Rat.cast_mul`：∀ {α : Type u_3} [inst : DivisionRing α] [CharZero α] (p q
 : ℚ), ↑(p * q) = ↑p * ↑q
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Rat.cast_ofNat`：∀ {α : Type u_3} [inst : DivisionRing α] (n : ℕ) [inst_1
 : n.AtLeastTwo], ↑(OfNat.ofNat n) = OfNat.ofNat n
· 使用引理 `Mathlib.Tactic.Linarith.eq_of_not_lt_of_not_gt`：eq_of_not_lt_of_not_gt {
α} [LinearOrder α] (a b : α) (h1 : ¬ a < b) (h2 : ¬ b < a) : a = b
· 使用定理 `Not.intro`：∀ {a : Prop}, (a → False) → ¬a
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
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
（共 95 条，此处仅展示前 30 条）

--- 原说明 ---
**Niven's theorem**: The only rational values of `cos` that occur at rational mu
ltiples of π
are `{-1, -1/2, 0, 1/2, 1}`.
-/
theorem niven (hθ : ∃ r : ℚ, θ = r * π) (hcos : ∃ q : ℚ, cos θ = q) :
    cos θ ∈ ({-1, -1 / 2, 0, 1 / 2, 1} : Set ℝ) := by
  -- Since `2 cos θ ` is an algebraic integer and rational, it must be an integer.
  -- Hence, `2 cos θ ∈ {-2, -1, 0, 1, 2}`.
  obtain ⟨r, rfl⟩ := hθ
  obtain ⟨k, hk⟩ : ∃ k : ℤ, 2 * cos (r * π) = k := by
    rw [← (Real.isIntegral_two_mul_cos_rat_mul_pi r).exists_int_iff_exists_rat]
    exact ⟨2 * hcos.choose, by push_cast; linarith [hcos.choose_spec]⟩
  -- Since k is an integer and `2 * cos (w * pi) = k`, we have $k ∈ {-2, -1, 0, 1, 2}$.
  have hk_values : k ∈ Finset.Icc (-2 : ℤ) 2 := by
    rw [Finset.mem_Icc]
    rify
    constructor <;> linarith [hk, (r * π).neg_one_le_cos, (r * π).cos_le_one]
  rw [show cos (r * π) = k / 2 by grind]
  fin_cases hk_values <;> simp

/-- Niven's theorem, but stated for `sin` instead of `cos`. -/
/-
**niven_sin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：niven_sin (hθ : exists r : Rat, θ = r * π) (hcos : exists q : Rat, sin θ =
 q) : sin θ in ({-1, -1 / 2, 0, 1 / 2, 1} : Set Real)
参数：hθ : exists r : Rat, θ = r * π；hcos : exists q : Rat, sin θ = q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.cos_sub_pi_div_two`：cos_sub_pi_div_two (x : Real) : cos (x - π / 2)
 = sin x
· 使用定理 `niven`：niven (hθ : exists r : Rat, θ = r * π) (hcos : exists q : Rat, co
s θ = q) : cos θ in ({-1, -1 / 2, 0, 1 / 2, 1} : Set Real)
· 使用定理 `Exists.imp'`：∀ {α : Sort u_2} {p : α → Prop} {β : Sort u_1} {q : β → Pro
p} (f : α → β),   (∀ (a : α), p a → q (f a)) → (∃ a, p a) → ∃ b, q b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Rat.cast_sub`：∀ {α : Type u_3} [inst : DivisionRing α] [CharZero α] (p q
 : ℚ), ↑(p - q) = ↑p - ↑q
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Rat.cast_div`：∀ {α : Type u_3} [inst : DivisionRing α] [CharZero α] (p q
 : ℚ), ↑(p / q) = ↑p / ↑q
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Rat.cast_one`：cast_one : ((1 : Rat) : α) = 1
· 使用定理 `Rat.cast_ofNat`：∀ {α : Type u_3} [inst : DivisionRing α] (n : ℕ) [inst_1
 : n.AtLeastTwo], ↑(OfNat.ofNat n) = OfNat.ofNat n
· 使用引理 `Mathlib.Tactic.Linarith.eq_of_not_lt_of_not_gt`：eq_of_not_lt_of_not_gt {
α} [LinearOrder α] (a b : α) (h1 : ¬ a < b) (h2 : ¬ b < a) : a = b
· 使用定理 `Not.intro`：∀ {a : Prop}, (a → False) → ¬a
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
（共 78 条，此处仅展示前 30 条）

--- 原说明 ---
Niven's theorem, but stated for `sin` instead of `cos`.
-/
theorem niven_sin (hθ : ∃ r : ℚ, θ = r * π) (hcos : ∃ q : ℚ, sin θ = q) :
    sin θ ∈ ({-1, -1 / 2, 0, 1 / 2, 1} : Set ℝ) := by
  convert! ← niven (θ := θ - π / 2) ?_ ?_ using 1
  · exact cos_sub_pi_div_two θ
  · exact hθ.imp' (· - 1 / 2) (by intros; push_cast; linarith)
  · simpa [cos_sub_pi_div_two]

/-- Niven's theorem, giving the possible angles for `θ` in the range `0 .. π`. -/
/-
**niven_angle_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：niven_angle_eq (hθ : exists r : Rat, θ = r * π) (hcos : exists q : Rat, co
s θ = q) (h_bnd : θ in Set.Icc 0 π) : θ in ({0, π / 3, π / 2, π * (2 / 3), π} : 
Set Real)
参数：hθ : exists r : Rat, θ = r * π；hcos : exists q : Rat, cos θ = q；h_bnd : θ in 
Set.Icc 0 π。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `niven`：niven (hθ : exists r : Rat, θ = r * π) (hcos : exists q : Rat, co
s θ = q) : cos θ in ({-1, -1 / 2, 0, 1 / 2, 1} : Set Real)
· 使用定理 `Real.cos_pi`：cos_pi : cos π = -1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.injOn_cos`：injOn_cos : InjOn cos (Icc 0 π)
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Real.pi_pos`：pi_pos : 0 < π
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero`：∀ {R : Type u_1} [in
st : CommSemiring R] {a₁ a₂ b₁ b₂ c : R},   Mathlib.Meta.NormNum.IsNat (a₁ + b₁)
 0 → a₂ + b₂ = c → a₁ + a₂ + (b₁ + b₂) =…
· 使用定理 `Mathlib.Tactic.Ring.Common.add_overlap_pf_zero`：∀ {R : Type u_1} [inst :
 CommSemiring R] {a b : R} (x : R) (e : ℕ),   Mathlib.Meta.NormNum.IsNat (a + b)
 0 → Mathlib.Meta.NormNum.IsNat (x ^…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isInt_add`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HAdd.hAdd →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
（共 92 条，此处仅展示前 30 条）

--- 原说明 ---
Niven's theorem, giving the possible angles for `θ` in the range `0 .. π`.
-/
theorem niven_angle_eq (hθ : ∃ r : ℚ, θ = r * π) (hcos : ∃ q : ℚ, cos θ = q)
    (h_bnd : θ ∈ Set.Icc 0 π) : θ ∈ ({0, π / 3, π / 2, π * (2 / 3), π} : Set ℝ) := by
  rcases niven hθ hcos with h | h | h | h | h <;>
  -- define `h₂` appropriately for each proof branch
  [have h₂ := cos_pi;
    have h₂ : cos (π * (2 / 3)) = -1 / 2 := by
      have := cos_pi_sub (π / 3)
      have := cos_pi_div_three
      grind;;
    have h₂ := cos_pi_div_two;
    have h₂ := cos_pi_div_three;
    have h₂ := cos_zero] <;>
  simp [injOn_cos h_bnd ⟨by positivity, by linarith [pi_nonneg]⟩ (h₂ ▸ h)]
/-
**niven_angle_div_pi_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：niven_angle_div_pi_eq {r : Rat} (hcos : exists q : Rat, cos (r * π) = q) (
h_bnd : r in Set.Icc 0 1) : r in ({0, 1 / 3, 1 / 2, 2 / 3, 1} : Set Rat)
参数：hcos : exists q : Rat, cos (r * π) = q；h_bnd : r in Set.Icc 0 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Function.Injective.mem_set_image`：∀ {α : Type u_1} {β : Type u_2} {f : α
 → β}, Function.Injective f → ∀ {s : Set α} {a : α}, f a ∈ f '' s ↔ a ∈ s
· 使用引理 `smul_left_injective`：smul_left_injective (hm : m != 0) : ((· • m) : R ->
 M).Injective
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `Real.pi_ne_zero`：pi_ne_zero : π != 0
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Real.pi_pos`：pi_pos : 0 < π
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `niven_angle_eq`：niven_angle_eq (hθ : exists r : Rat, θ = r * π) (hcos : 
exists q : Rat, cos θ = q) (h_bnd : θ in Set.Icc 0 π) : θ in ({0, π / 3, π / 2, 
π * …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Rat.smul_def`：smul_def (a : Rat) (x : K) : a • x = ↑a * x
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Rat.cast_zero`：cast_zero : ((0 : Rat) : α) = 0
· 使用定理 `Rat.cast_inv`：∀ {α : Type u_3} [inst : DivisionRing α] [CharZero α] (p :
 ℚ), ↑p⁻¹ = (↑p)⁻¹
（共 38 条，此处仅展示前 30 条）
-/
theorem niven_angle_div_pi_eq {r : ℚ} (hcos : ∃ q : ℚ, cos (r * π) = q)
    (h_bnd : r ∈ Set.Icc 0 1) : r ∈ ({0, 1 / 3, 1 / 2, 2 / 3, 1} : Set ℚ) := by
  apply smul_left_injective ℚ pi_ne_zero |>.mem_set_image.mp
  replace h_bnd : (r : ℝ) * π ∈ Set.Icc (0 * π) (1 * π) := by
    obtain ⟨hr, hr'⟩ := h_bnd; constructor <;> gcongr <;> norm_cast
  generalize h : (r : ℝ) * π = θ at *
  have := niven_angle_eq ⟨r, h.symm⟩ hcos (by simpa using h_bnd)
  simp_all [Rat.smul_def]
  grind
/-
**niven_fract_angle_div_pi_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：niven_fract_angle_div_pi_eq {r : Rat} (hcos : exists q : Rat, cos (r * π) 
= q) : Int.fract r in ({0, 1 / 3, 1 / 2, 2 / 3} : Set Rat)
参数：hcos : exists q : Rat, cos (r * π) = q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `niven_angle_div_pi_eq`：niven_angle_div_pi_eq {r : Rat} (hcos : exists q 
: Rat, cos (r * π) = q) (h_bnd : r in Set.Icc 0 1) : r in ({0, 1 / 3, 1 / 2, 2 /
 3, 1} : Se…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.fract.eq_1`：∀ {α : Type u_2} [inst : Ring α] [inst_1 : LinearOrder α
] [inst_2 : FloorRing α] (a : α), Int.fract a = a - ↑⌊a⌋
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Rat.cast_sub`：∀ {α : Type u_3} [inst : DivisionRing α] [CharZero α] (p q
 : ℚ), ↑(p - q) = ↑p - ↑q
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Rat.cast_intCast`：cast_intCast (n : Int) : ((n : Rat) : α) = n
· 使用定理 `Rat.cast_mul`：∀ {α : Type u_3} [inst : DivisionRing α] [CharZero α] (p q
 : ℚ), ↑(p * q) = ↑p * ↑q
· 使用引理 `Rat.cast_zpow`：cast_zpow (p : Rat) (n : Int) : ↑(p ^ n) = (p ^ n : α)
· 使用定理 `Rat.cast_neg`：∀ {α : Type u_3} [inst : DivisionRing α] (q : ℚ), ↑(-q) = 
-↑q
· 使用定理 `Rat.cast_one`：cast_one : ((1 : Rat) : α) = 1
· 使用定理 `sub_mul`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), (a
 - b) * c = a * c - b * c
· 使用定理 `Real.cos_sub_int_mul_pi`：cos_sub_int_mul_pi (x : Real) (n : Int) : cos (
x - n * π) = (-1) ^ n * cos x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Int.fract_lt_one`：fract_lt_one (a : R) : fract a < 1
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem niven_fract_angle_div_pi_eq {r : ℚ} (hcos : ∃ q : ℚ, cos (r * π) = q) :
    Int.fract r ∈ ({0, 1 / 3, 1 / 2, 2 / 3} : Set ℚ) := by
  suffices Int.fract r ∈ ({0, 1 / 3, 1 / 2, 2 / 3, 1} : Set ℚ) by
    grind [ne_of_lt (Int.fract_lt_one r)]
  refine niven_angle_div_pi_eq (r := Int.fract r) ?_ (by simp [le_of_lt <| Int.fract_lt_one r])
  obtain ⟨q, hq⟩ := hcos
  exact ⟨(-1) ^ ⌊r⌋ * q, by rw [Int.fract]; push_cast; rw [sub_mul, cos_sub_int_mul_pi, hq]⟩
/-
**irrational_cos_rat_mul_pi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：irrational_cos_rat_mul_pi {r : Rat} (hr : 3 < r.den) : Irrational (cos (r 
* π))
参数：hr : 3 < r.den。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `niven_fract_angle_div_pi_eq`：niven_fract_angle_div_pi_eq {r : Rat} (hcos
 : exists q : Rat, cos (r * π) = q) : Int.fract r in ({0, 1 / 3, 1 / 2, 2 / 3} :
 Set Rat)
· 使用定理 `exists_rat_of_not_irrational`：exists_rat_of_not_irrational {x : Real} (h
x : ¬ Irrational x) : exists (q : Rat), x = q
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Mathlib.Meta.NormNum.isNat_lt_false`：isNat_lt_false [Semiring α] [Partia
lOrder α] [IsOrderedRing α] {a b : α} {a' b' : Nat} (ha : IsNat a a') (hb : IsNa
t b b') (h : Nat.ble b' a…
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isNat_ratDen`：isNat_ratDen : forall {q : Rat} {n : 
Int} {n' : Nat} {d : Nat}, IsRat q n d -> n.natAbs = n' -> n'.gcd d = 1 -> IsNat
 q.den d | _, n, _, d, …
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_isRat`：∀ {α : Type u_1} [inst : Ring α] 
{a : α} {n d : ℕ},   Mathlib.Meta.NormNum.IsNNRat a n d → Mathlib.Meta.NormNum.I
sRat a (Int.ofNat n) d
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isNNRat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsN
NRat a n 1
· 使用定理 `Int.natAbs_natCast`：∀ (n : ℕ), (↑n).natAbs = n
· 使用定理 `Nat.gcd_zero_left`：∀ (y : ℕ), Nat.gcd 0 y = y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Rat.den_intFract`：den_intFract (x : Rat) : (fract x).den = x.den
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_div`：∀ {α : Type u} [inst : DivisionSemirin
g α] {a b : α} {cn cd : ℕ},   Mathlib.Meta.NormNum.IsNNRat (a * b⁻¹) cn cd → Mat
hlib.Meta.NormNum.IsNN…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_mul`：isNNRat_mul {α} [Semiring α] {f : α ->
 α -> α} {a b : α} {na nb nc : Nat} {da db dc k : Nat} : f = HMul.hMul -> IsNNRa
t a na da -> IsNNRat b…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_inv_pos`：isNNRat_inv_pos {α} [DivisionSemir
ing α] [CharZero α] {a : α} {n d : Nat} : IsNNRat a (Nat.succ n) d -> IsNNRat a⁻
¹ d (Nat.succ n)
· 使用定理 `Nat.gcd_one_left`：∀ (n : ℕ), Nat.gcd 1 n = 1
· 使用定理 `Mathlib.Meta.NormNum.nat_gcd_helper_1'`：nat_gcd_helper_1' (x y a b : Nat
) (h : y * b = x * a + 1) : Nat.gcd x y = 1
· 使用定理 `Set.mem_singleton_iff`：mem_singleton_iff {a b : α} : a in ({b} : Set α) 
↔ a = b
-/
theorem irrational_cos_rat_mul_pi {r : ℚ} (hr : 3 < r.den) :
    Irrational (cos (r * π)) := by
  rw [← Rat.den_intFract] at hr
  by_contra! hnz
  rcases niven_fract_angle_div_pi_eq (exists_rat_of_not_irrational hnz) with (hr' | hr' | hr' | hr')
  all_goals (try rw [Set.mem_singleton_iff] at hr'); rw [hr'] at hr; norm_num at hr
