/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.RingTheory.WittVector.Basic
public import Mathlib.RingTheory.WittVector.IsPoly

/-!
## The Verschiebung operator

## References

* [Hazewinkel, *Witt Vectors*][Haze09]

* [Commelin and Lewis, *Formalizing the Ring of Witt Vectors*][CL21]
-/

@[expose] public section


namespace WittVector

open MvPolynomial

variable {p : ℕ} {R S : Type*} [CommRing R] [CommRing S]

local notation "𝕎" => WittVector p -- type as `\bbW`

noncomputable section

/-- `verschiebungFun x` shifts the coefficients of `x` up by one,
by inserting 0 as the 0th coefficient.
`x.coeff i` then becomes `(verschiebungFun x).coeff (i + 1)`.

`verschiebungFun` is the underlying function of the additive monoid hom `WittVector.verschiebung`.
-/
/-
**WittVector.verschiebungFun** 是 Mathlib 中的一个定义，位于命名空间 `WittVector`。
形式化陈述：verschiebungFun (x : 𝕎 R) : 𝕎 R
参数：x : 𝕎 R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`verschiebungFun x` shifts the coefficients of `x` up by one,
by inserting 0 as the 0th coefficient.
`x.coeff i` then becomes `(verschiebungFun x).coeff (i + 1)`.

`verschiebungFun` is the underlying function of the additive monoid hom `WittVec
tor.verschiebung`.
-/
def verschiebungFun (x : 𝕎 R) : 𝕎 R :=
  @mk' p _ fun n => if n = 0 then 0 else x.coeff (n - 1)
/-
**WittVector.verschiebungFun_coeff** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：verschiebungFun_coeff (x : 𝕎 R) (n : Nat) : (verschiebungFun x).coeff n = 
if n = 0 then 0 else x.coeff (n - 1)
参数：x : 𝕎 R；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem verschiebungFun_coeff (x : 𝕎 R) (n : ℕ) :
    (verschiebungFun x).coeff n = if n = 0 then 0 else x.coeff (n - 1) := by
  simp only [verschiebungFun]
/-
**WittVector.verschiebungFun_coeff_zero** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：verschiebungFun_coeff_zero (x : 𝕎 R) : (verschiebungFun x).coeff 0 = 0
参数：x : 𝕎 R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WittVector.verschiebungFun_coeff`：verschiebungFun_coeff (x : 𝕎 R) (n : N
at) : (verschiebungFun x).coeff n = if n = 0 then 0 else x.coeff (n - 1)
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
theorem verschiebungFun_coeff_zero (x : 𝕎 R) : (verschiebungFun x).coeff 0 = 0 := by
  rw [verschiebungFun_coeff, if_pos rfl]

@[simp]
/-
**WittVector.verschiebungFun_coeff_succ** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：verschiebungFun_coeff_succ (x : 𝕎 R) (n : Nat) : (verschiebungFun x).coeff
 n.succ = x.coeff n
参数：x : 𝕎 R；n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem verschiebungFun_coeff_succ (x : 𝕎 R) (n : ℕ) :
    (verschiebungFun x).coeff n.succ = x.coeff n :=
  rfl

@[ghost_simps]
/-
**WittVector.ghostComponent_zero_verschiebungFun** 是 Mathlib 中的一个定理，位于命名空间 `Witt
Vector`。
形式化陈述：ghostComponent_zero_verschiebungFun [hp : Fact p.Prime] (x : 𝕎 R) : ghostC
omponent 0 (verschiebungFun x) = 0
参数：x : 𝕎 R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WittVector.ghostComponent_apply`：ghostComponent_apply (n : Nat) (x : 𝕎 R
) : ghostComponent n x = aeval x.coeff (W_ Int n)
· 使用定理 `aeval_wittPolynomial`：aeval_wittPolynomial {A : Type*} [CommRing A] [Alg
ebra R A] (f : Nat -> A) (n : Nat) : aeval f (W_ R n) = ∑ i in range (n + 1), (p
 : A) ^ i …
· 使用定理 `Finset.range_one`：range_one : range 1 = {0}
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `WittVector.verschiebungFun_coeff_zero`：verschiebungFun_coeff_zero (x : 𝕎
 R) : (verschiebungFun x).coeff 0 = 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem ghostComponent_zero_verschiebungFun [hp : Fact p.Prime] (x : 𝕎 R) :
    ghostComponent 0 (verschiebungFun x) = 0 := by
  rw [ghostComponent_apply, aeval_wittPolynomial, Finset.range_one, Finset.sum_singleton,
    verschiebungFun_coeff_zero, pow_zero, pow_zero, pow_one, one_mul]

@[ghost_simps]
/-
**WittVector.ghostComponent_verschiebungFun** 是 Mathlib 中的一个定理，位于命名空间 `WittVecto
r`。
形式化陈述：ghostComponent_verschiebungFun [hp : Fact p.Prime] (x : 𝕎 R) (n : Nat) : g
hostComponent (n + 1) (verschiebungFun x) = p * ghostComponent n x
参数：x : 𝕎 R；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `aeval_wittPolynomial`：aeval_wittPolynomial {A : Type*} [CommRing A] [Alg
ebra R A] (f : Nat -> A) (n : Nat) : aeval f (W_ R n) = ∑ i in range (n + 1), (p
 : A) ^ i …
· 使用定理 `Finset.sum_range_succ'`：∀ {M : Type u_4} [inst : AddCommMonoid M] (f : ℕ
 → M) (n : ℕ),   ∑ k ∈ Finset.range (n + 1), f k = ∑ k ∈ Finset.range n, f (k + 
1) + f 0
· 使用定理 `WittVector.verschiebungFun_coeff`：verschiebungFun_coeff (x : 𝕎 R) (n : N
at) : (verschiebungFun x).coeff n = if n = 0 then 0 else x.coeff (n - 1)
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `Nat.Prime.ne_zero`：∀ {n : ℕ}, Nat.Prime n → n ≠ 0
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `Nat.succ_sub_succ_eq_sub`：∀ (n m : ℕ), n.succ - m.succ = n - m
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ghostComponent_verschiebungFun [hp : Fact p.Prime] (x : 𝕎 R) (n : ℕ) :
    ghostComponent (n + 1) (verschiebungFun x) = p * ghostComponent n x := by
  simp only [ghostComponent_apply, aeval_wittPolynomial]
  rw [Finset.sum_range_succ', verschiebungFun_coeff, if_pos rfl,
    zero_pow (pow_ne_zero _ hp.1.ne_zero), mul_zero, add_zero, Finset.mul_sum, Finset.sum_congr rfl]
  rintro i -
  simp only [pow_succ', verschiebungFun_coeff_succ, Nat.succ_sub_succ_eq_sub, mul_assoc]

/-- The 0th Verschiebung polynomial is 0. For `n > 0`, the `n`th Verschiebung polynomial is the
variable `X (n-1)`.
-/
/-
**WittVector.verschiebungPoly** 是 Mathlib 中的一个定义，位于命名空间 `WittVector`。
形式化陈述：verschiebungPoly (n : Nat) : MvPolynomial Nat Int
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The 0th Verschiebung polynomial is 0. For `n > 0`, the `n`th Verschiebung polyno
mial is the
variable `X (n-1)`.
-/
def verschiebungPoly (n : ℕ) : MvPolynomial ℕ ℤ :=
  if n = 0 then 0 else X (n - 1)

@[simp]
/-
**WittVector.verschiebungPoly_zero** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：verschiebungPoly_zero : verschiebungPoly 0 = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem verschiebungPoly_zero : verschiebungPoly 0 = 0 :=
  rfl
/-
**WittVector.aeval_verschiebung_poly'** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：aeval_verschiebung_poly' (x : 𝕎 R) (n : Nat) : aeval x.coeff (verschiebung
Poly n) = (verschiebungFun x).coeff n
参数：x : 𝕎 R；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `WittVector.verschiebungFun_coeff_zero`：verschiebungFun_coeff_zero (x : 𝕎
 R) : (verschiebungFun x).coeff 0 = 0
· 使用定理 `WittVector.verschiebungPoly.eq_1`：∀ (n : ℕ), WittVector.verschiebungPoly
 n = if n = 0 then 0 else MvPolynomial.X (n - 1)
· 使用定理 `WittVector.verschiebungFun_coeff_succ`：verschiebungFun_coeff_succ (x : 𝕎
 R) (n : Nat) : (verschiebungFun x).coeff n.succ = x.coeff n
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Nat.succ_ne_zero`：∀ (n : ℕ), n.succ ≠ 0
· 使用定理 `MvPolynomial.aeval_X`：aeval_X (s : σ) : aeval f (X s : MvPolynomial σ R)
 = f s
· 使用定理 `add_tsub_cancel_right`：add_tsub_cancel_right (a b : α) : a + b - b = a
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
theorem aeval_verschiebung_poly' (x : 𝕎 R) (n : ℕ) :
    aeval x.coeff (verschiebungPoly n) = (verschiebungFun x).coeff n := by
  rcases n with - | n
  · simp only [verschiebungPoly, ite_true, map_zero, verschiebungFun_coeff_zero]
  · rw [verschiebungPoly, verschiebungFun_coeff_succ, if_neg n.succ_ne_zero, aeval_X,
      add_tsub_cancel_right]

variable (p)

/-- `WittVector.verschiebung` has polynomial structure given by `WittVector.verschiebungPoly`.
-/
/-
**WittVector.verschiebungFun_isPoly** 是 Mathlib 中的一个实例，位于命名空间 `WittVector`。
形式化陈述：verschiebungFun_isPoly : IsPoly p fun R _Rcr => @verschiebungFun p R _Rcr
该定义给出了一等式。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `WittVector.aeval_verschiebung_poly'`：aeval_verschiebung_poly' (x : 𝕎 R) 
(n : Nat) : aeval x.coeff (verschiebungPoly n) = (verschiebungFun x).coeff n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
`WittVector.verschiebung` has polynomial structure given by `WittVector.verschie
bungPoly`.
-/
instance verschiebungFun_isPoly : IsPoly p fun R _Rcr => @verschiebungFun p R _Rcr := by
  use verschiebungPoly
  simp only [aeval_verschiebung_poly', forall₃_true_iff]

-- We add this example as a verification that Lean 4's instance resolution can handle the `IsPoly`
-- typeclass, whereas Lean 3 needed a bespoke `@[is_poly]` attribute.
/-
**WittVector.** 是 Mathlib 中的一个示例，位于命名空间 `WittVector`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example (p : ℕ) (f : ⦃R : Type _⦄ → [CommRing R] → WittVector p R → WittVector p R) [IsPoly p f] :
    IsPoly p (fun (R : Type*) (I : CommRing R) ↦ verschiebungFun ∘ (@f R I)) :=
  inferInstance

variable {p}
variable [hp : Fact p.Prime]

/--
`verschiebung x` shifts the coefficients of `x` up by one, by inserting 0 as the 0th coefficient.
`x.coeff i` then becomes `(verschiebung x).coeff (i + 1)`.

This is an additive monoid hom with underlying function `verschiebung_fun`.
-/
/-
**WittVector.verschiebung** 是 Mathlib 中的一个定义，位于命名空间 `WittVector`。
形式化陈述：verschiebung : 𝕎 R ->+ 𝕎 R where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`verschiebung x` shifts the coefficients of `x` up by one, by inserting 0 as the
 0th coefficient.
`x.coeff i` then becomes `(verschiebung x).coeff (i + 1)`.

This is an additive monoid hom with underlying function `verschiebung_fun`.
-/
noncomputable def verschiebung : 𝕎 R →+ 𝕎 R where
  toFun := verschiebungFun
  map_zero' := by
    ext ⟨⟩ <;> rw [verschiebungFun_coeff] <;>
      simp only [zero_coeff, ite_self]
  map_add' := by
    ghost_calc _ _
    rintro ⟨⟩ <;> ghost_simp

/-- `WittVector.verschiebung` is a polynomial function. -/
@[is_poly]
/-
**WittVector.verschiebung_isPoly** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：verschiebung_isPoly : IsPoly p fun _ _ => verschiebung (p
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`WittVector.verschiebung` is a polynomial function.
-/
theorem verschiebung_isPoly : IsPoly p fun _ _ => verschiebung (p := p) :=
  verschiebungFun_isPoly p

/-- verschiebung is a natural transformation -/
@[simp]
/-
**WittVector.map_verschiebung** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：map_verschiebung (f : R ->+* S) (x : 𝕎 R) : map f (verschiebung x) = versc
hiebung (map f x)
参数：f : R ->+* S；x : 𝕎 R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WittVector.ext`：ext {x y : 𝕎 R} (h : forall n, x.coeff n = y.coeff n) : 
x = y
· 使用定理 `RingHom.map_zero`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring 
α} {x_1 : NonAssocSemiring β} (f : α →+* β), f 0 = 0

--- 原说明 ---
verschiebung is a natural transformation
-/
theorem map_verschiebung (f : R →+* S) (x : 𝕎 R) :
    map f (verschiebung x) = verschiebung (map f x) := by
  ext ⟨-, -⟩
  · exact f.map_zero
  · rfl

@[ghost_simps]
/-
**WittVector.ghostComponent_zero_verschiebung** 是 Mathlib 中的一个定理，位于命名空间 `WittVec
tor`。
形式化陈述：ghostComponent_zero_verschiebung (x : 𝕎 R) : ghostComponent 0 (verschiebun
g x) = 0
参数：x : 𝕎 R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WittVector.ghostComponent_zero_verschiebungFun`：ghostComponent_zero_vers
chiebungFun [hp : Fact p.Prime] (x : 𝕎 R) : ghostComponent 0 (verschiebungFun x)
 = 0
-/
theorem ghostComponent_zero_verschiebung (x : 𝕎 R) : ghostComponent 0 (verschiebung x) = 0 :=
  ghostComponent_zero_verschiebungFun _

@[ghost_simps]
/-
**WittVector.ghostComponent_verschiebung** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：ghostComponent_verschiebung (x : 𝕎 R) (n : Nat) : ghostComponent (n + 1) (
verschiebung x) = p * ghostComponent n x
参数：x : 𝕎 R；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WittVector.ghostComponent_verschiebungFun`：ghostComponent_verschiebungFu
n [hp : Fact p.Prime] (x : 𝕎 R) (n : Nat) : ghostComponent (n + 1) (verschiebung
Fun x) = p * ghostComponent n x
-/
theorem ghostComponent_verschiebung (x : 𝕎 R) (n : ℕ) :
    ghostComponent (n + 1) (verschiebung x) = p * ghostComponent n x :=
  ghostComponent_verschiebungFun _ _

@[simp]
/-
**WittVector.verschiebung_coeff_zero** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：verschiebung_coeff_zero (x : 𝕎 R) : (verschiebung x).coeff 0 = 0
参数：x : 𝕎 R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem verschiebung_coeff_zero (x : 𝕎 R) : (verschiebung x).coeff 0 = 0 :=
  rfl

-- simp_nf complains if this is simp
/-
**WittVector.verschiebung_coeff_add_one** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：verschiebung_coeff_add_one (x : 𝕎 R) (n : Nat) : (verschiebung x).coeff (n
 + 1) = x.coeff n
参数：x : 𝕎 R；n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem verschiebung_coeff_add_one (x : 𝕎 R) (n : ℕ) :
    (verschiebung x).coeff (n + 1) = x.coeff n :=
  rfl

@[simp]
/-
**WittVector.verschiebung_coeff_succ** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：verschiebung_coeff_succ (x : 𝕎 R) (n : Nat) : (verschiebung x).coeff n.suc
c = x.coeff n
参数：x : 𝕎 R；n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem verschiebung_coeff_succ (x : 𝕎 R) (n : ℕ) : (verschiebung x).coeff n.succ = x.coeff n :=
  rfl

variable (p R) in
/-
**WittVector.verschiebung_injective** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：verschiebung_injective : Function.Injective (verschiebung : 𝕎 R -> 𝕎 R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `injective_iff_map_eq_zero`：∀ {F : Type u_7} {G : Type u_8} {H : Type u_9
} [inst : AddGroup G] [inst_1 : AddZeroClass H] [inst_2 : FunLike F G H]   [AddM
onoidHomClass F…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `WittVector.ext`：ext {x y : 𝕎 R} (h : forall n, x.coeff n = y.coeff n) : 
x = y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WittVector.verschiebung_coeff_succ`：verschiebung_coeff_succ (x : 𝕎 R) (n
 : Nat) : (verschiebung x).coeff n.succ = x.coeff n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `WittVector.zero_coeff`：zero_coeff (n : Nat) : (0 : 𝕎 R).coeff n = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem verschiebung_injective : Function.Injective (verschiebung : 𝕎 R → 𝕎 R) := by
  rw [injective_iff_map_eq_zero]
  intro w h
  ext n
  rw [← verschiebung_coeff_succ, h]
  simp only [zero_coeff]
/-
**WittVector.aeval_verschiebungPoly** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：aeval_verschiebungPoly (x : 𝕎 R) (n : Nat) : aeval x.coeff (verschiebungPo
ly n) = (verschiebung x).coeff n
参数：x : 𝕎 R；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WittVector.aeval_verschiebung_poly'`：aeval_verschiebung_poly' (x : 𝕎 R) 
(n : Nat) : aeval x.coeff (verschiebungPoly n) = (verschiebungFun x).coeff n
-/
theorem aeval_verschiebungPoly (x : 𝕎 R) (n : ℕ) :
    aeval x.coeff (verschiebungPoly n) = (verschiebung x).coeff n :=
  aeval_verschiebung_poly' x n

@[simp]
/-
**WittVector.bind** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bind₁_verschiebungPoly_wittPolynomial (n : ℕ) :
    bind₁ verschiebungPoly (wittPolynomial p ℤ n) =
      if n = 0 then 0 else p * wittPolynomial p ℤ (n - 1) := by
  apply MvPolynomial.funext
  intro x
  split_ifs with hn
  · simp only [hn, wittPolynomial_zero, bind₁_X_right, verschiebungPoly_zero, map_zero]
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    rw [Nat.succ_eq_add_one, add_tsub_cancel_right]
    simp only [map_mul]
    rw [map_natCast, hom_bind₁]
    calc
      _ = ghostComponent (n + 1) (verschiebung <| mk p x) := by
       apply eval₂Hom_congr (RingHom.ext_int _ _) _ rfl
       funext k
       simp only [← aeval_verschiebungPoly]
       exact eval₂Hom_congr (RingHom.ext_int _ _) rfl rfl
      _ = _ := by rw [ghostComponent_verschiebung]; rfl

end

end WittVector

