/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.RingTheory.WittVector.Frobenius
public import Mathlib.RingTheory.WittVector.Verschiebung
public import Mathlib.RingTheory.WittVector.MulP

/-!
## Identities between operations on the ring of Witt vectors

In this file we derive common identities between the Frobenius and Verschiebung operators.

## Main declarations

* `frobenius_verschiebung`: the composition of Frobenius and Verschiebung is multiplication by `p`
* `verschiebung_mul_frobenius`: the “projection formula”: `V(x * F y) = V x * y`
* `iterate_verschiebung_mul_coeff`: an identity from [Haze09] 6.2

## References

* [Hazewinkel, *Witt Vectors*][Haze09]

* [Commelin and Lewis, *Formalizing the Ring of Witt Vectors*][CL21]
-/

public section


namespace WittVector

variable {p : ℕ} {R : Type*} [hp : Fact p.Prime] [CommRing R]

-- type as `\bbW`
local notation "𝕎" => WittVector p

noncomputable section

-- Porting note: `ghost_calc` failure: the manual instances had to be added.
/-- The composition of Frobenius and Verschiebung is multiplication by `p`. -/
/-
**WittVector.frobenius_verschiebung** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：frobenius_verschiebung (x : 𝕎 R) : frobenius (verschiebung x) = x * p
参数：x : 𝕎 R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WittVector.verschiebung_isPoly`：verschiebung_isPoly : IsPoly p fun _ _ =
> verschiebung (p
· 使用定理 `WittVector.mulN_isPoly`：mulN_isPoly (n : Nat) : IsPoly p fun _ _Rcr x =>
 x * n
· 使用定理 `WittVector.IsPoly.ext`：ext [Fact p.Prime] {f g} (hf : IsPoly p f) (hg : 
IsPoly p g) (h : forall (R : Type u) [_Rcr : CommRing R] (x : 𝕎 R) (n : Nat), gh
ostComponen…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WittVector.ghostComponent_frobenius`：ghostComponent_frobenius (n : Nat) 
(x : 𝕎 R) : ghostComponent n (frobenius x) = ghostComponent (n + 1) x
· 使用定理 `WittVector.ghostComponent_verschiebung`：ghostComponent_verschiebung (x :
 𝕎 R) (n : Nat) : ghostComponent (n + 1) (verschiebung x) = p * ghostComponent n
 x
· 使用定理 `RingHom.map_mul`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring α
} {x_1 : NonAssocSemiring β} (f : α →+* β) (a b : α),   f (a * b) = f a * f b
· 使用定理 `map_natCast`：map_natCast [FunLike F R S] [RingHomClass F R S] (f : F) : 
forall n : Nat, f (n : R) = n
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The composition of Frobenius and Verschiebung is multiplication by `p`.
-/
theorem frobenius_verschiebung (x : 𝕎 R) : frobenius (verschiebung x) = x * p := by
  have : IsPoly p fun {R} [CommRing R] x ↦ frobenius (verschiebung x) :=
    IsPoly.comp (hg := frobenius_isPoly p) (hf := verschiebung_isPoly)
  have : IsPoly p fun {R} [CommRing R] x ↦ x * p := mulN_isPoly p p
  ghost_calc x
  ghost_simp [mul_comm]

/-- Verschiebung is the same as multiplication by `p` on the ring of Witt vectors of `ZMod p`. -/
/-
**WittVector.verschiebung_zmod** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：verschiebung_zmod (x : 𝕎 (ZMod p)) : verschiebung x = x * p
参数：x : 𝕎 (ZMod p)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WittVector.frobenius_verschiebung`：frobenius_verschiebung (x : 𝕎 R) : fr
obenius (verschiebung x) = x * p
· 使用定理 `WittVector.frobenius_zmodp`：frobenius_zmodp (x : 𝕎 (ZMod p)) : frobenius
 x = x

--- 原说明 ---
Verschiebung is the same as multiplication by `p` on the ring of Witt vectors of
 `ZMod p`.
-/
theorem verschiebung_zmod (x : 𝕎 (ZMod p)) : verschiebung x = x * p := by
  rw [← frobenius_verschiebung, frobenius_zmodp]

variable (p R)
/-
**WittVector.coeff_p_pow** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：coeff_p_pow [CharP R p] (i : Nat) : ((p : 𝕎 R) ^ i).coeff i = 1
参数：i : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `WittVector.one_coeff_zero`：one_coeff_zero : (1 : 𝕎 R).coeff 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WittVector.frobenius_verschiebung`：frobenius_verschiebung (x : 𝕎 R) : fr
obenius (verschiebung x) = x * p
· 使用定理 `WittVector.coeff_frobenius_charP`：coeff_frobenius_charP (x : 𝕎 R) (n : N
at) : coeff (frobenius x) n = x.coeff n ^ p
· 使用定理 `WittVector.verschiebung_coeff_succ`：verschiebung_coeff_succ (x : 𝕎 R) (n
 : Nat) : (verschiebung x).coeff n.succ = x.coeff n
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
-/
theorem coeff_p_pow [CharP R p] (i : ℕ) : ((p : 𝕎 R) ^ i).coeff i = 1 := by
  induction i with
  | zero => simp only [one_coeff_zero, pow_zero]
  | succ i h =>
    rw [pow_succ, ← frobenius_verschiebung, coeff_frobenius_charP,
      verschiebung_coeff_succ, h, one_pow]
/-
**WittVector.coeff_p_pow_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：coeff_p_pow_eq_zero [CharP R p] {i j : Nat} (hj : j != i) : ((p : 𝕎 R) ^ i
).coeff j = 0
参数：hj : j != i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `WittVector.one_coeff_eq_of_pos`：one_coeff_eq_of_pos (n : Nat) (hn : 0 < 
n) : coeff (1 : 𝕎 R) n = 0
· 使用定理 `Nat.pos_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → 0 < n
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WittVector.frobenius_verschiebung`：frobenius_verschiebung (x : 𝕎 R) : fr
obenius (verschiebung x) = x * p
· 使用定理 `WittVector.coeff_frobenius_charP`：coeff_frobenius_charP (x : 𝕎 R) (n : N
at) : coeff (frobenius x) n = x.coeff n ^ p
· 使用定理 `WittVector.verschiebung_coeff_zero`：verschiebung_coeff_zero (x : 𝕎 R) : 
(verschiebung x).coeff 0 = 0
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `Nat.Prime.ne_zero`：∀ {n : ℕ}, Nat.Prime n → n ≠ 0
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `WittVector.verschiebung_coeff_succ`：verschiebung_coeff_succ (x : 𝕎 R) (n
 : Nat) : (verschiebung x).coeff n.succ = x.coeff n
· 使用定理 `ne_of_apply_ne`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) {x y : α}, f
 x ≠ f y → x ≠ y
-/
theorem coeff_p_pow_eq_zero [CharP R p] {i j : ℕ} (hj : j ≠ i) : ((p : 𝕎 R) ^ i).coeff j = 0 := by
  induction i generalizing j with
  | zero =>
    rw [pow_zero, one_coeff_eq_of_pos]
    exact Nat.pos_of_ne_zero hj
  | succ i hi =>
    rw [pow_succ, ← frobenius_verschiebung, coeff_frobenius_charP]
    cases j
    · rw [verschiebung_coeff_zero, zero_pow hp.out.ne_zero]
    · rw [verschiebung_coeff_succ, hi (ne_of_apply_ne _ hj), zero_pow hp.out.ne_zero]
/-
**WittVector.coeff_p** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：coeff_p [CharP R p] (i : Nat) : (p : 𝕎 R).coeff i = if i = 1 then 1 else 0
参数：i : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `WittVector.coeff_p_pow`：coeff_p_pow [CharP R p] (i : Nat) : ((p : 𝕎 R) ^
 i).coeff i = 1
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `WittVector.coeff_p_pow_eq_zero`：coeff_p_pow_eq_zero [CharP R p] {i j : N
at} (hj : j != i) : ((p : 𝕎 R) ^ i).coeff j = 0
-/
theorem coeff_p [CharP R p] (i : ℕ) : (p : 𝕎 R).coeff i = if i = 1 then 1 else 0 := by
  split_ifs with hi
  · simpa only [hi, pow_one] using coeff_p_pow p R 1
  · simpa only [pow_one] using coeff_p_pow_eq_zero p R hi

@[simp]
/-
**WittVector.coeff_p_zero** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：coeff_p_zero [CharP R p] : (p : 𝕎 R).coeff 0 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WittVector.coeff_p`：coeff_p [CharP R p] (i : Nat) : (p : 𝕎 R).coeff i = 
if i = 1 then 1 else 0
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `zero_ne_one`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 0 ≠ 1
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
theorem coeff_p_zero [CharP R p] : (p : 𝕎 R).coeff 0 = 0 := by
  rw [coeff_p, if_neg]
  exact zero_ne_one

@[simp]
/-
**WittVector.coeff_p_one** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：coeff_p_one [CharP R p] : (p : 𝕎 R).coeff 1 = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WittVector.coeff_p`：coeff_p [CharP R p] (i : Nat) : (p : 𝕎 R).coeff i = 
if i = 1 then 1 else 0
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
theorem coeff_p_one [CharP R p] : (p : 𝕎 R).coeff 1 = 1 := by rw [coeff_p, if_pos rfl]
/-
**WittVector.p_nonzero** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：p_nonzero [Nontrivial R] [CharP R p] : (p : 𝕎 R) != 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WittVector.zero_coeff`：zero_coeff (n : Nat) : (0 : 𝕎 R).coeff n = 0
· 使用定理 `WittVector.coeff_p_one`：coeff_p_one [CharP R p] : (p : 𝕎 R).coeff 1 = 1
-/
theorem p_nonzero [Nontrivial R] [CharP R p] : (p : 𝕎 R) ≠ 0 := by
  intro h
  simpa only [h, zero_coeff, zero_ne_one] using coeff_p_one p R
/-
**WittVector.FractionRing.p_nonzero** 是 Mathlib 中的一个定理，位于命名空间 `WittVector.Fracti
onRing`。
形式化陈述：∀ (p : ℕ) (R : Type u_1) [hp : Fact (Nat.Prime p)] [inst : CommRing R] [No
ntrivial R] [CharP R p], ↑p ≠ 0
参数：p : ℕ；R : Type u_1；Nat.Prime p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_natCast`：map_natCast [FunLike F R S] [RingHomClass F R S] (f : F) : 
forall n : Nat, f (n : R) = n
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Function.Injective.ne`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Func
tion.Injective f → ∀ {a₁ a₂ : α}, a₁ ≠ a₂ → f a₁ ≠ f a₂
· 使用定理 `IsFractionRing.injective`：∀ (R : Type u_1) [inst : CommRing R] (K : Type
 u_5) [inst_1 : CommRing K] [inst_2 : Algebra R K] [IsFractionRing R K],   Funct
ion.Injective …
· 使用定理 `WittVector.p_nonzero`：p_nonzero [Nontrivial R] [CharP R p] : (p : 𝕎 R) !
= 0
-/
theorem FractionRing.p_nonzero [Nontrivial R] [CharP R p] : (p : FractionRing (𝕎 R)) ≠ 0 := by
  simpa using (IsFractionRing.injective (𝕎 R) (FractionRing (𝕎 R))).ne (WittVector.p_nonzero _ _)

variable {p R}

-- Porting note: `ghost_calc` failure: the manual instances had to be added.
/-- The “projection formula” for Frobenius and Verschiebung. -/
/-
**WittVector.verschiebung_mul_frobenius** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：verschiebung_mul_frobenius (x y : 𝕎 R) : verschiebung (x * frobenius y) = 
verschiebung x * y
参数：x y : 𝕎 R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WittVector.IsPoly.comp₂`：∀ {p : ℕ} {g : ⦃R : Type u_2⦄ → [CommRing R] → 
WittVector p R → WittVector p R}   {f : ⦃R : Type u_2⦄ → [CommRing R] → WittVect
or p R → Witt…
· 使用定理 `WittVector.verschiebung_isPoly`：verschiebung_isPoly : IsPoly p fun _ _ =
> verschiebung (p
· 使用定理 `WittVector.IsPoly₂.comp`：∀ {p : ℕ} {h : ⦃R : Type u_2⦄ → [CommRing R] → 
WittVector p R → WittVector p R → WittVector p R}   {f g : ⦃R : Type u_2⦄ → [Com
mRing R] → Wi…
· 使用定理 `WittVector.IsPoly₂.ext`：ext [Fact p.Prime] {f g} (hf : IsPoly₂ p f) (hg 
: IsPoly₂ p g) (h : forall (R : Type u) [_Rcr : CommRing R] (x y : 𝕎 R) (n : Nat
), ghostComp…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WittVector.ghostComponent_zero_verschiebung`：ghostComponent_zero_verschi
ebung (x : 𝕎 R) : ghostComponent 0 (verschiebung x) = 0
· 使用定理 `RingHom.map_mul`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring α
} {x_1 : NonAssocSemiring β} (f : α →+* β) (a b : α),   f (a * b) = f a * f b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `WittVector.ghostComponent_verschiebung`：ghostComponent_verschiebung (x :
 𝕎 R) (n : Nat) : ghostComponent (n + 1) (verschiebung x) = p * ghostComponent n
 x
· 使用定理 `WittVector.ghostComponent_frobenius`：ghostComponent_frobenius (n : Nat) 
(x : 𝕎 R) : ghostComponent n (frobenius x) = ghostComponent (n + 1) x
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)

--- 原说明 ---
The “projection formula” for Frobenius and Verschiebung.
-/
theorem verschiebung_mul_frobenius (x y : 𝕎 R) :
    verschiebung (x * frobenius y) = verschiebung x * y := by
  have : IsPoly₂ p fun {R} [Rcr : CommRing R] x y ↦ verschiebung (x * frobenius y) :=
    IsPoly.comp₂ (hg := verschiebung_isPoly)
      (hf := IsPoly₂.comp (hh := mulIsPoly₂) (hf := idIsPolyI' p) (hg := frobenius_isPoly p))
  have : IsPoly₂ p fun {R} [CommRing R] x y ↦ verschiebung x * y :=
    IsPoly₂.comp (hh := mulIsPoly₂) (hf := verschiebung_isPoly) (hg := idIsPolyI' p)
  ghost_calc x y
  rintro ⟨⟩ <;> ghost_simp [mul_assoc]
/-
**WittVector.mul_charP_coeff_zero** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：mul_charP_coeff_zero [CharP R p] (x : 𝕎 R) : (x * p).coeff 0 = 0
参数：x : 𝕎 R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WittVector.frobenius_verschiebung`：frobenius_verschiebung (x : 𝕎 R) : fr
obenius (verschiebung x) = x * p
· 使用定理 `WittVector.coeff_frobenius_charP`：coeff_frobenius_charP (x : 𝕎 R) (n : N
at) : coeff (frobenius x) n = x.coeff n ^ p
· 使用定理 `WittVector.verschiebung_coeff_zero`：verschiebung_coeff_zero (x : 𝕎 R) : 
(verschiebung x).coeff 0 = 0
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `Nat.Prime.ne_zero`：∀ {n : ℕ}, Nat.Prime n → n ≠ 0
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
-/
theorem mul_charP_coeff_zero [CharP R p] (x : 𝕎 R) : (x * p).coeff 0 = 0 := by
  rw [← frobenius_verschiebung, coeff_frobenius_charP, verschiebung_coeff_zero,
    zero_pow hp.out.ne_zero]
/-
**WittVector.mul_charP_coeff_succ** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：mul_charP_coeff_succ [CharP R p] (x : 𝕎 R) (i : Nat) : (x * p).coeff (i + 
1) = x.coeff i ^ p
参数：x : 𝕎 R；i : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WittVector.frobenius_verschiebung`：frobenius_verschiebung (x : 𝕎 R) : fr
obenius (verschiebung x) = x * p
· 使用定理 `WittVector.coeff_frobenius_charP`：coeff_frobenius_charP (x : 𝕎 R) (n : N
at) : coeff (frobenius x) n = x.coeff n ^ p
· 使用定理 `WittVector.verschiebung_coeff_succ`：verschiebung_coeff_succ (x : 𝕎 R) (n
 : Nat) : (verschiebung x).coeff n.succ = x.coeff n
-/
theorem mul_charP_coeff_succ [CharP R p] (x : 𝕎 R) (i : ℕ) :
    (x * p).coeff (i + 1) = x.coeff i ^ p := by
  rw [← frobenius_verschiebung, coeff_frobenius_charP, verschiebung_coeff_succ]
/-
**WittVector.mul_pow_charP_coeff_zero** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：mul_pow_charP_coeff_zero [CharP R p] (x : 𝕎 R) {m n : Nat} (h : m < n) : (
x * p ^ n).coeff m = 0
参数：x : 𝕎 R；h : m < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `WittVector.mul_charP_coeff_zero`：mul_charP_coeff_zero [CharP R p] (x : 𝕎
 R) : (x * p).coeff 0 = 0
· 使用定理 `WittVector.mul_charP_coeff_succ`：mul_charP_coeff_succ [CharP R p] (x : 𝕎
 R) (i : Nat) : (x * p).coeff (i + 1) = x.coeff i ^ p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `Nat.Prime.ne_zero`：∀ {n : ℕ}, Nat.Prime n → n ≠ 0
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
-/
theorem mul_pow_charP_coeff_zero [CharP R p] (x : 𝕎 R) {m n : ℕ} (h : m < n) :
    (x * p ^ n).coeff m = 0 := by
  induction n generalizing m with
  | zero => contradiction
  | succ n ih =>
    rw [pow_succ, ← mul_assoc]
    cases m with
    | zero => exact mul_charP_coeff_zero _
    | succ m' =>
      rw [mul_charP_coeff_succ, ih, zero_pow hp.out.ne_zero]
      simpa using h
/-
**WittVector.mul_pow_charP_coeff_succ** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：mul_pow_charP_coeff_succ [CharP R p] (x : 𝕎 R) {m n : Nat} : (x * p ^ n).c
oeff (m + n) = x.coeff m ^ (p ^ n)
参数：x : 𝕎 R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `WittVector.mul_charP_coeff_succ`：mul_charP_coeff_succ [CharP R p] (x : 𝕎
 R) (i : Nat) : (x * p).coeff (i + 1) = x.coeff i ^ p
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
-/
theorem mul_pow_charP_coeff_succ [CharP R p] (x : 𝕎 R) {m n : ℕ} :
    (x * p ^ n).coeff (m + n) = x.coeff m ^ (p ^ n) := by
  induction n generalizing m with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ← mul_assoc, ← add_assoc, mul_charP_coeff_succ, pow_succ, pow_mul]
    congr
    exact ih
/-
**WittVector.verschiebung_frobenius** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：verschiebung_frobenius [CharP R p] (x : 𝕎 R) : verschiebung (frobenius x) 
= x * p
参数：x : 𝕎 R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WittVector.ext`：ext {x y : 𝕎 R} (h : forall n, x.coeff n = y.coeff n) : 
x = y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WittVector.mul_charP_coeff_zero`：mul_charP_coeff_zero [CharP R p] (x : 𝕎
 R) : (x * p).coeff 0 = 0
· 使用定理 `WittVector.verschiebung_coeff_zero`：verschiebung_coeff_zero (x : 𝕎 R) : 
(verschiebung x).coeff 0 = 0
· 使用定理 `WittVector.mul_charP_coeff_succ`：mul_charP_coeff_succ [CharP R p] (x : 𝕎
 R) (i : Nat) : (x * p).coeff (i + 1) = x.coeff i ^ p
· 使用定理 `WittVector.verschiebung_coeff_succ`：verschiebung_coeff_succ (x : 𝕎 R) (n
 : Nat) : (verschiebung x).coeff n.succ = x.coeff n
· 使用定理 `WittVector.coeff_frobenius_charP`：coeff_frobenius_charP (x : 𝕎 R) (n : N
at) : coeff (frobenius x) n = x.coeff n ^ p
-/
theorem verschiebung_frobenius [CharP R p] (x : 𝕎 R) : verschiebung (frobenius x) = x * p := by
  ext ⟨i⟩
  · rw [mul_charP_coeff_zero, verschiebung_coeff_zero]
  · rw [mul_charP_coeff_succ, verschiebung_coeff_succ, coeff_frobenius_charP]
/-
**WittVector.verschiebung_frobenius_comm** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：verschiebung_frobenius_comm [CharP R p] : Function.Commute (verschiebung :
 𝕎 R -> 𝕎 R) frobenius
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WittVector.verschiebung_frobenius`：verschiebung_frobenius [CharP R p] (x
 : 𝕎 R) : verschiebung (frobenius x) = x * p
· 使用定理 `WittVector.frobenius_verschiebung`：frobenius_verschiebung (x : 𝕎 R) : fr
obenius (verschiebung x) = x * p
-/
theorem verschiebung_frobenius_comm [CharP R p] :
    Function.Commute (verschiebung : 𝕎 R → 𝕎 R) frobenius := fun x => by
  rw [verschiebung_frobenius, frobenius_verschiebung]

/-!
## Iteration lemmas
-/


open Function

/-
**WittVector.iterate_verschiebung_coeff_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `WittV
ector`。
形式化陈述：iterate_verschiebung_coeff_eq_zero (x : 𝕎 R) {n : Nat} {m : Nat} (h : m < 
n) : (verschiebung^[n] x).coeff m = 0
参数：x : 𝕎 R；h : m < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.iterate_succ_apply'`：iterate_succ_apply' (n : Nat) (x : α) : f^
[n.succ] x = f (f^[n] x)
· 使用定理 `WittVector.verschiebung_coeff_zero`：verschiebung_coeff_zero (x : 𝕎 R) : 
(verschiebung x).coeff 0 = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WittVector.verschiebung_coeff_succ`：verschiebung_coeff_succ (x : 𝕎 R) (n
 : Nat) : (verschiebung x).coeff n.succ = x.coeff n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
theorem iterate_verschiebung_coeff_eq_zero (x : 𝕎 R) {n : ℕ} {m : ℕ} (h : m < n) :
    (verschiebung^[n] x).coeff m = 0 := by
  induction n generalizing m with
  | zero => contradiction
  | succ n ih =>
    rw [iterate_succ_apply']
    cases m with
    | zero => exact verschiebung_coeff_zero _
    | succ m' =>
      rw [verschiebung_coeff_succ, ih]
      simpa using h
/-
**WittVector.iterate_verschiebung_coeff** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：iterate_verschiebung_coeff (x : 𝕎 R) (n k : Nat) : (verschiebung^[n] x).co
eff (k + n) = x.coeff k
参数：x : 𝕎 R；n k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Function.iterate_succ_apply'`：iterate_succ_apply' (n : Nat) (x : α) : f^
[n.succ] x = f (f^[n] x)
· 使用定理 `Nat.add_succ`：∀ (n m : ℕ), n + m.succ = (n + m).succ
· 使用定理 `WittVector.verschiebung_coeff_succ`：verschiebung_coeff_succ (x : 𝕎 R) (n
 : Nat) : (verschiebung x).coeff n.succ = x.coeff n
-/
theorem iterate_verschiebung_coeff (x : 𝕎 R) (n k : ℕ) :
    (verschiebung^[n] x).coeff (k + n) = x.coeff k := by
  induction n with
  | zero => simp
  | succ k ih => rw [iterate_succ_apply', Nat.add_succ, verschiebung_coeff_succ]; exact ih
/-
**WittVector.iterate_verschiebung_mul_left** 是 Mathlib 中的一个定理，位于命名空间 `WittVector
`。
形式化陈述：iterate_verschiebung_mul_left (x y : 𝕎 R) (i : Nat) : verschiebung^[i] x *
 y = verschiebung^[i] (x * frobenius^[i] y)
参数：x y : 𝕎 R；i : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.iterate_succ_apply'`：iterate_succ_apply' (n : Nat) (x : α) : f^
[n.succ] x = f (f^[n] x)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WittVector.verschiebung_mul_frobenius`：verschiebung_mul_frobenius (x y :
 𝕎 R) : verschiebung (x * frobenius y) = verschiebung x * y
· 使用定理 `Function.iterate_succ_apply`：iterate_succ_apply (n : Nat) (x : α) : f^[n
.succ] x = f^[n] (f x)
-/
theorem iterate_verschiebung_mul_left (x y : 𝕎 R) (i : ℕ) :
    verschiebung^[i] x * y = verschiebung^[i] (x * frobenius^[i] y) := by
  induction i generalizing y with
  | zero => simp
  | succ i ih =>
    rw [iterate_succ_apply', ← verschiebung_mul_frobenius, ih, iterate_succ_apply',
      iterate_succ_apply]

section CharP

variable [CharP R p]

/-
**WittVector.iterate_verschiebung_mul** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：iterate_verschiebung_mul (x y : 𝕎 R) (i j : Nat) : verschiebung^[i] x * ve
rschiebung^[j] y = verschiebung^[i + j] (frobenius^[j] x * frobenius^[i] y)
参数：x y : 𝕎 R；i j : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WittVector.iterate_verschiebung_mul_left`：iterate_verschiebung_mul_left 
(x y : 𝕎 R) (i : Nat) : verschiebung^[i] x * y = verschiebung^[i] (x * frobenius
^[i] y)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Commute.iterate_iterate`：iterate_iterate (h : Commute f g) (m n
 : Nat) : Commute f^[m] g^[n]
· 使用定理 `WittVector.verschiebung_frobenius_comm`：verschiebung_frobenius_comm [Cha
rP R p] : Function.Commute (verschiebung : 𝕎 R -> 𝕎 R) frobenius
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Function.iterate_add_apply`：iterate_add_apply (m n : Nat) (x : α) : f^[m
 + n] x = f^[m] (f^[n] x)
-/
theorem iterate_verschiebung_mul (x y : 𝕎 R) (i j : ℕ) :
    verschiebung^[i] x * verschiebung^[j] y =
      verschiebung^[i + j] (frobenius^[j] x * frobenius^[i] y) := by
  calc
    _ = verschiebung^[i] (x * frobenius^[i] (verschiebung^[j] y)) := ?_
    _ = verschiebung^[i] (x * verschiebung^[j] (frobenius^[i] y)) := ?_
    _ = verschiebung^[i] (verschiebung^[j] (frobenius^[i] y) * x) := ?_
    _ = verschiebung^[i] (verschiebung^[j] (frobenius^[i] y * frobenius^[j] x)) := ?_
    _ = verschiebung^[i + j] (frobenius^[i] y * frobenius^[j] x) := ?_
    _ = _ := ?_
  · apply iterate_verschiebung_mul_left
  · rw [verschiebung_frobenius_comm.iterate_iterate]
  · rw [mul_comm]
  · rw [iterate_verschiebung_mul_left]
  · rw [iterate_add_apply]
  · rw [mul_comm]
/-
**WittVector.iterate_frobenius_coeff** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：iterate_frobenius_coeff (x : 𝕎 R) (i k : Nat) : (frobenius^[i] x).coeff k 
= x.coeff k ^ p ^ i
参数：x : 𝕎 R；i k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Function.iterate_succ_apply'`：iterate_succ_apply' (n : Nat) (x : α) : f^
[n.succ] x = f (f^[n] x)
· 使用定理 `WittVector.coeff_frobenius_charP`：coeff_frobenius_charP (x : 𝕎 R) (n : N
at) : coeff (frobenius x) n = x.coeff n ^ p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a c₁ c₂ : R} {b₁ b₂ : ℕ} {d : R},   a ^ b₁ = c₁ → a ^ b₂ = c₂ → c₁ * c₂ = 
d → a ^ (b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.single_pow`：∀ {R : Type u_1} [inst : CommSemi
ring R] {a c : R} {b : ℕ}, a ^ b = c → (a + 0) ^ b = c + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pow_mul`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₂ c₂ : R} {ea₁ b c₁ : ℕ} {xa₁ c₃ d : R},   ea₁ * b = c₁ → a₂ ^ b = c₂
 → xa₁ ^ c₁ * Nat.rawCast 1 …
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
· 使用定理 `Mathlib.Tactic.Ring.Common.one_pow`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a : R} (b : ℕ), Mathlib.Meta.NormNum.IsNat a 1 → a ^ b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R) {e : R}, Nat.rawCast 1 = e → a ^ 0 = e + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Mathlib.Tactic.RingNF.mul_assoc_rev`：mul_assoc_rev (a b c : R) : a * (b 
* c) = a * b * c
· 使用定理 `Mathlib.Tactic.RingNF.nat_rawCast_1`：nat_rawCast_1 : (Nat.rawCast 1 : R)
 = 1
（共 37 条，此处仅展示前 30 条）
-/
theorem iterate_frobenius_coeff (x : 𝕎 R) (i k : ℕ) :
    (frobenius^[i] x).coeff k = x.coeff k ^ p ^ i := by
  induction i with
  | zero => simp
  | succ i ih => rw [iterate_succ_apply', coeff_frobenius_charP, ih]; ring_nf

/-- This is a slightly specialized form of [Hazewinkel, *Witt Vectors*][Haze09] 6.2 equation 5. -/
/-
**WittVector.iterate_verschiebung_mul_coeff** 是 Mathlib 中的一个定理，位于命名空间 `WittVecto
r`。
形式化陈述：iterate_verschiebung_mul_coeff (x y : 𝕎 R) (i j : Nat) : (verschiebung^[i]
 x * verschiebung^[j] y).coeff (i + j) = x.coeff 0 ^ p ^ j * y.coeff 0 ^ p ^ i
参数：x y : 𝕎 R；i j : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WittVector.iterate_verschiebung_mul`：iterate_verschiebung_mul (x y : 𝕎 R
) (i j : Nat) : verschiebung^[i] x * verschiebung^[j] y = verschiebung^[i + j] (
frobenius^[j] x * frobeni…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `WittVector.iterate_verschiebung_coeff`：iterate_verschiebung_coeff (x : 𝕎
 R) (n k : Nat) : (verschiebung^[n] x).coeff (k + n) = x.coeff k
· 使用定理 `WittVector.mul_coeff_zero`：mul_coeff_zero (x y : 𝕎 R) : (x * y).coeff 0 
= x.coeff 0 * y.coeff 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `WittVector.iterate_frobenius_coeff`：iterate_frobenius_coeff (x : 𝕎 R) (i
 k : Nat) : (frobenius^[i] x).coeff k = x.coeff k ^ p ^ i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
This is a slightly specialized form of [Hazewinkel, *Witt Vectors*][Haze09] 6.2 
equation 5.
-/
theorem iterate_verschiebung_mul_coeff (x y : 𝕎 R) (i j : ℕ) :
    (verschiebung^[i] x * verschiebung^[j] y).coeff (i + j) =
      x.coeff 0 ^ p ^ j * y.coeff 0 ^ p ^ i := by
  calc
    _ = (verschiebung^[i + j] (frobenius^[j] x * frobenius^[i] y)).coeff (i + j) := ?_
    _ = (frobenius^[j] x * frobenius^[i] y).coeff 0 := ?_
    _ = (frobenius^[j] x).coeff 0 * (frobenius^[i] y).coeff 0 := ?_
    _ = _ := ?_
  · rw [iterate_verschiebung_mul]
  · convert! iterate_verschiebung_coeff (p := p) (R := R) _ _ _ using 2
    rw [zero_add]
  · apply mul_coeff_zero
  · simp only [iterate_frobenius_coeff]
/-
**WittVector.iterate_verschiebung_iterate_frobenius** 是 Mathlib 中的一个定理，位于命名空间 `W
ittVector`。
形式化陈述：iterate_verschiebung_iterate_frobenius (x : 𝕎 R) (n : Nat) : verschiebung^
[n] (frobenius^[n] x) = x * (p ^ n)
参数：x : 𝕎 R；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `Function.Commute.comp_iterate`：comp_iterate (h : Commute f g) (n : Nat) 
: (f ∘ g)^[n] = f^[n] ∘ g^[n]
· 使用定理 `WittVector.verschiebung_frobenius_comm`：verschiebung_frobenius_comm [Cha
rP R p] : Function.Commute (verschiebung : 𝕎 R -> 𝕎 R) frobenius
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Function.iterate_succ_apply'`：iterate_succ_apply' (n : Nat) (x : α) : f^
[n.succ] x = f (f^[n] x)
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `WittVector.verschiebung_frobenius`：verschiebung_frobenius [CharP R p] (x
 : 𝕎 R) : verschiebung (frobenius x) = x * p
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
-/
theorem iterate_verschiebung_iterate_frobenius (x : 𝕎 R) (n : ℕ) :
    verschiebung^[n] (frobenius^[n] x) = x * (p ^ n) := by
  rw [← comp_apply (f := verschiebung^[n]),
      ← Function.Commute.comp_iterate verschiebung_frobenius_comm]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iterate_succ_apply', ih, pow_succ, comp_apply, verschiebung_frobenius, mul_assoc]

end CharP

end

end WittVector

