/-
Copyright (c) 2021 Jon Eugster. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Eugster, Eric Wieser
-/
module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.FreeAlgebra
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.SimpleRing.Basic

/-!
# Characteristics of algebras

In this file we describe the characteristic of `R`-algebras.

In particular we are interested in the characteristic of free algebras over `R`
and the fraction field `FractionRing R`.


## Main results

- `charP_of_injective_algebraMap` If `R →+* A` is an injective algebra map
  then `A` has the same characteristic as `R`.

Instances constructed from this result:
- Any `FreeAlgebra R X` has the same characteristic as `R`.
- The `FractionRing R` of an integral domain `R` has the same characteristic as `R`.

-/

public section

variable {R A : Type*}

/-- Given `R →+* A`, then `char A ∣ char R`. -/
/-
**CharP.dvd_of_ringHom** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CharP.dvd_of_ringHom [NonAssocSemiring R] [NonAssocSemiring A] (f : R ->+*
 A) (p q : Nat) [CharP R p] [CharP A q] : q ∣ p
参数：f : R ->+* A；p q : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CharP.cast_eq_zero_iff`：∀ (R : Type u_2) {inst : AddMonoidWithOne R} (p 
: outParam ℕ) [self : CharP R p] (x : ℕ), ↑x = 0 ↔ p ∣ x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_natCast`：map_natCast [FunLike F R S] [RingHomClass F R S] (f : F) : 
forall n : Nat, f (n : R) = n
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…

--- 原说明 ---
Given `R →+* A`, then `char A ∣ char R`.
-/
theorem CharP.dvd_of_ringHom [NonAssocSemiring R] [NonAssocSemiring A]
    (f : R →+* A) (p q : ℕ) [CharP R p] [CharP A q] : q ∣ p := by
  refine (CharP.cast_eq_zero_iff A q p).mp ?_
  rw [← map_natCast f p, CharP.cast_eq_zero, map_zero]

/-- Given `R →+* A`, where `R` is a domain with `char R > 0`, then `char A = char R`. -/
/-
**CharP.of_ringHom_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CharP.of_ringHom_of_ne_zero [NonAssocSemiring R] [NoZeroDivisors R] [NonAs
socSemiring A] [Nontrivial A] (f : R ->+* A) (p : Nat) (hp : p != 0) [CharP R p]
 : CharP A p
参数：f : R ->+* A；p : Nat；hp : p != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.domain_nontrivial`：domain_nontrivial [Nontrivial β] : Nontrivial
 α
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用引理 `CharP.char_is_prime_or_zero`：char_is_prime_or_zero (p : Nat) [hc : CharP
 R p] : Nat.Prime p ∨ p = 0
· 使用定理 `CharP.exists`：∀ (R : Type u_1) [inst : NonAssocSemiring R], ∃ p, CharP R
 p
· 使用定理 `CharP.dvd_of_ringHom`：CharP.dvd_of_ringHom [NonAssocSemiring R] [NonAsso
cSemiring A] (f : R ->+* A) (p q : Nat) [CharP R p] [CharP A q] : q ∣ p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.isUnit_iff`：∀ {n : ℕ}, IsUnit n ↔ n = 1
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Irreducible.isUnit_or_isUnit`：∀ {M : Type u_1} [inst : Monoid M] {p : M}
, Irreducible p → ∀ ⦃a b : M⦄, p = a * b → IsUnit a ∨ IsUnit b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用引理 `CharP.char_ne_one`：char_ne_one [Nontrivial R] (p : Nat) [hc : CharP R p]
 : p != 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a

--- 原说明 ---
Given `R →+* A`, where `R` is a domain with `char R > 0`, then `char A = char R`
.
-/
theorem CharP.of_ringHom_of_ne_zero [NonAssocSemiring R] [NoZeroDivisors R]
    [NonAssocSemiring A] [Nontrivial A]
    (f : R →+* A) (p : ℕ) (hp : p ≠ 0) [CharP R p] : CharP A p := by
  have := f.domain_nontrivial
  have H := (CharP.char_is_prime_or_zero R p).resolve_right hp
  obtain ⟨q, hq⟩ := CharP.exists A
  obtain ⟨k, e⟩ := dvd_of_ringHom f p q
  have := Nat.isUnit_iff.mp ((H.2 e).resolve_left (Nat.isUnit_iff.not.mpr (char_ne_one A q)))
  rw [this, mul_one] at e
  exact e ▸ hq

/-- If a ring homomorphism `R →+* A` is injective then `A` has the same characteristic as `R`. -/
/-
**charP_of_injective_ringHom** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：charP_of_injective_ringHom [NonAssocSemiring R] [NonAssocSemiring A] {f : 
R ->+* A} (h : Function.Injective f) (p : Nat) [CharP R p] : CharP A p where cas
t_eq_zero_iff x
参数：h : Function.Injective f；p : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CharP.cast_eq_zero_iff`：∀ (R : Type u_2) {inst : AddMonoidWithOne R} (p 
: outParam ℕ) [self : CharP R p] (x : ℕ), ↑x = 0 ↔ p ∣ x
· 使用定理 `map_natCast`：map_natCast [FunLike F R S] [RingHomClass F R S] (f : F) : 
forall n : Nat, f (n : R) = n
· 使用定理 `map_eq_zero_iff`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : 
Zero M] [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F
), Fu…
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
If a ring homomorphism `R →+* A` is injective then `A` has the same characterist
ic as `R`.
-/
theorem charP_of_injective_ringHom [NonAssocSemiring R] [NonAssocSemiring A]
    {f : R →+* A} (h : Function.Injective f) (p : ℕ) [CharP R p] : CharP A p where
  cast_eq_zero_iff x := by
    rw [← CharP.cast_eq_zero_iff R p x, ← map_natCast f x, map_eq_zero_iff f h]

/-- If the algebra map `R →+* A` is injective then `A` has the same characteristic as `R`. -/
/-
**charP_of_injective_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：charP_of_injective_algebraMap [CommSemiring R] [Semiring A] [Algebra R A] 
(h : Function.Injective (algebraMap R A)) (p : Nat) [CharP R p] : CharP A p
参数：h : Function.Injective (algebraMap R A)；p : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `charP_of_injective_ringHom`：charP_of_injective_ringHom [NonAssocSemiring
 R] [NonAssocSemiring A] {f : R ->+* A} (h : Function.Injective f) (p : Nat) [Ch
arP R p] : CharP…

--- 原说明 ---
If the algebra map `R →+* A` is injective then `A` has the same characteristic a
s `R`.
-/
theorem charP_of_injective_algebraMap [CommSemiring R] [Semiring A] [Algebra R A]
    (h : Function.Injective (algebraMap R A)) (p : ℕ) [CharP R p] : CharP A p :=
  charP_of_injective_ringHom h p
/-
**charP_of_injective_algebraMap'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：charP_of_injective_algebraMap' (R : Type*) [CommRing R] [Semiring A] [Alge
bra R A] [FaithfulSMul R A] (p : Nat) [CharP R p] : CharP A p
参数：R : Type*；p : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `charP_of_injective_ringHom`：charP_of_injective_ringHom [NonAssocSemiring
 R] [NonAssocSemiring A] {f : R ->+* A} (h : Function.Injective f) (p : Nat) [Ch
arP R p] : CharP…
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
-/
theorem charP_of_injective_algebraMap' (R : Type*) [CommRing R] [Semiring A]
    [Algebra R A] [FaithfulSMul R A] (p : ℕ) [CharP R p] : CharP A p :=
  charP_of_injective_ringHom (FaithfulSMul.algebraMap_injective R A) p

/-- If a ring homomorphism `R →+* A` is injective and `R` has characteristic zero
then so does `A`. -/
/-
**charZero_of_injective_ringHom** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：charZero_of_injective_ringHom [NonAssocSemiring R] [NonAssocSemiring A] {f
 : R ->+* A} (h : Function.Injective f) [CharZero R] : CharZero A where cast_inj
ective _ _ _
参数：h : Function.Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CharZero.cast_injective`：∀ {R : Type u_1} {inst : AddMonoidWithOne R} [s
elf : CharZero R], Function.Injective Nat.cast
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_natCast`：map_natCast [FunLike F R S] [RingHomClass F R S] (f : F) : 
forall n : Nat, f (n : R) = n

--- 原说明 ---
If a ring homomorphism `R →+* A` is injective and `R` has characteristic zero
then so does `A`.
-/
theorem charZero_of_injective_ringHom [NonAssocSemiring R] [NonAssocSemiring A]
    {f : R →+* A} (h : Function.Injective f) [CharZero R] : CharZero A where
  cast_injective _ _ _ := CharZero.cast_injective <| h <| by simpa only [map_natCast f]

/-- If the algebra map `R →+* A` is injective and `R` has characteristic zero then so does `A`. -/
/-
**charZero_of_injective_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：charZero_of_injective_algebraMap [CommSemiring R] [Semiring A] [Algebra R 
A] (h : Function.Injective (algebraMap R A)) [CharZero R] : CharZero A
参数：h : Function.Injective (algebraMap R A)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `charZero_of_injective_ringHom`：charZero_of_injective_ringHom [NonAssocSe
miring R] [NonAssocSemiring A] {f : R ->+* A} (h : Function.Injective f) [CharZe
ro R] : CharZero A …

--- 原说明 ---
If the algebra map `R →+* A` is injective and `R` has characteristic zero then s
o does `A`.
-/
theorem charZero_of_injective_algebraMap [CommSemiring R] [Semiring A] [Algebra R A]
    (h : Function.Injective (algebraMap R A)) [CharZero R] : CharZero A :=
  charZero_of_injective_ringHom h

/-- If `R →+* A` is injective, and `A` is of characteristic `p`, then `R` is also of
characteristic `p`. Similar to `RingHom.charZero`. -/
/-
**RingHom.charP** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：RingHom.charP [NonAssocSemiring R] [NonAssocSemiring A] (f : R ->+* A) (H 
: Function.Injective f) (p : Nat) [CharP A p] : CharP R p
参数：f : R ->+* A；H : Function.Injective f；p : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CharP.exists`：∀ (R : Type u_1) [inst : NonAssocSemiring R], ∃ p, CharP R
 p
· 使用引理 `CharP.eq`：eq {p q : Nat} (hp : CharP R p) (hq : CharP R q) : p = q
· 使用定理 `charP_of_injective_ringHom`：charP_of_injective_ringHom [NonAssocSemiring
 R] [NonAssocSemiring A] {f : R ->+* A} (h : Function.Injective f) (p : Nat) [Ch
arP R p] : CharP…

--- 原说明 ---
If `R →+* A` is injective, and `A` is of characteristic `p`, then `R` is also of
characteristic `p`. Similar to `RingHom.charZero`.
-/
theorem RingHom.charP [NonAssocSemiring R] [NonAssocSemiring A] (f : R →+* A)
    (H : Function.Injective f) (p : ℕ) [CharP A p] : CharP R p := by
  obtain ⟨q, h⟩ := CharP.exists R
  exact CharP.eq _ (charP_of_injective_ringHom H q) ‹CharP A p› ▸ h

/-- If `R →+* A` is injective, then `R` is of characteristic `p` if and only if `A` is also of
characteristic `p`. Similar to `RingHom.charZero_iff`. -/
/-
**RingHom.charP_iff** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：∀ {R : Type u_1} {A : Type u_2} [inst : NonAssocSemiring R] [inst_1 : NonA
ssocSemiring A] (f : R →+* A),   Function.Injective ⇑f → ∀ (p : ℕ), CharP R p ↔ 
CharP A p
参数：f : R →+* A；p : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `charP_of_injective_ringHom`：charP_of_injective_ringHom [NonAssocSemiring
 R] [NonAssocSemiring A] {f : R ->+* A} (h : Function.Injective f) (p : Nat) [Ch
arP R p] : CharP…
· 使用定理 `RingHom.charP`：RingHom.charP [NonAssocSemiring R] [NonAssocSemiring A] (
f : R ->+* A) (H : Function.Injective f) (p : Nat) [CharP A p] : CharP R p

--- 原说明 ---
If `R →+* A` is injective, then `R` is of characteristic `p` if and only if `A` 
is also of
characteristic `p`. Similar to `RingHom.charZero_iff`.
-/
protected theorem RingHom.charP_iff [NonAssocSemiring R] [NonAssocSemiring A]
    (f : R →+* A) (H : Function.Injective f) (p : ℕ) : CharP R p ↔ CharP A p :=
  ⟨fun _ ↦ charP_of_injective_ringHom H p, fun _ ↦ f.charP H p⟩

/-- If a ring homomorphism `R →+* A` is injective then `A` has the same exponential characteristic
as `R`. -/
/-
**expChar_of_injective_ringHom** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：expChar_of_injective_ringHom [NonAssocSemiring R] [NonAssocSemiring A] {f 
: R ->+* A} (h : Function.Injective f) (q : Nat) [hR : ExpChar R q] : ExpChar A 
q
参数：h : Function.Injective f；q : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `charZero_of_injective_ringHom`：charZero_of_injective_ringHom [NonAssocSe
miring R] [NonAssocSemiring A] {f : R ->+* A} (h : Function.Injective f) [CharZe
ro R] : CharZero A …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `charP_of_injective_ringHom`：charP_of_injective_ringHom [NonAssocSemiring
 R] [NonAssocSemiring A] {f : R ->+* A} (h : Function.Injective f) (p : Nat) [Ch
arP R p] : CharP…

--- 原说明 ---
If a ring homomorphism `R →+* A` is injective then `A` has the same exponential 
characteristic
as `R`.
-/
lemma expChar_of_injective_ringHom
    [NonAssocSemiring R] [NonAssocSemiring A] {f : R →+* A} (h : Function.Injective f)
    (q : ℕ) [hR : ExpChar R q] : ExpChar A q := by
  rcases hR with _ | hprime
  · have := charZero_of_injective_ringHom h; exact .zero
  have := charP_of_injective_ringHom h q; exact .prime hprime

/-- If `R →+* A` is injective, and `A` is of exponential characteristic `p`, then `R` is also of
exponential characteristic `p`. Similar to `RingHom.charZero`. -/
/-
**RingHom.expChar** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：RingHom.expChar [NonAssocSemiring R] [NonAssocSemiring A] (f : R ->+* A) (
H : Function.Injective f) (p : Nat) [ExpChar A p] : ExpChar R p
参数：f : R ->+* A；H : Function.Injective f；p : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RingHom.charZero`：charZero (ϕ : R ->+* S) [CharZero S] : CharZero R wher
e cast_injective a b h
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHom.charP`：RingHom.charP [NonAssocSemiring R] [NonAssocSemiring A] (
f : R ->+* A) (H : Function.Injective f) (p : Nat) [CharP A p] : CharP R p

--- 原说明 ---
If `R →+* A` is injective, and `A` is of exponential characteristic `p`, then `R
` is also of
exponential characteristic `p`. Similar to `RingHom.charZero`.
-/
lemma RingHom.expChar [NonAssocSemiring R] [NonAssocSemiring A] (f : R →+* A)
    (H : Function.Injective f) (p : ℕ) [ExpChar A p] : ExpChar R p := by
  cases ‹ExpChar A p› with
  | zero => have := f.charZero; exact .zero
  | prime hp => have := f.charP H p; exact .prime hp

/-- If `R →+* A` is injective, then `R` is of exponential characteristic `p` if and only if `A` is
also of exponential characteristic `p`. Similar to `RingHom.charZero_iff`. -/
/-
**RingHom.expChar_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：RingHom.expChar_iff [NonAssocSemiring R] [NonAssocSemiring A] (f : R ->+* 
A) (H : Function.Injective f) (p : Nat) : ExpChar R p ↔ ExpChar A p
参数：f : R ->+* A；H : Function.Injective f；p : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `expChar_of_injective_ringHom`：expChar_of_injective_ringHom [NonAssocSemi
ring R] [NonAssocSemiring A] {f : R ->+* A} (h : Function.Injective f) (q : Nat)
 [hR : ExpChar R q…
· 使用引理 `RingHom.expChar`：RingHom.expChar [NonAssocSemiring R] [NonAssocSemiring 
A] (f : R ->+* A) (H : Function.Injective f) (p : Nat) [ExpChar A p] : ExpChar R
 p

--- 原说明 ---
If `R →+* A` is injective, then `R` is of exponential characteristic `p` if and 
only if `A` is
also of exponential characteristic `p`. Similar to `RingHom.charZero_iff`.
-/
lemma RingHom.expChar_iff [NonAssocSemiring R] [NonAssocSemiring A] (f : R →+* A)
    (H : Function.Injective f) (p : ℕ) : ExpChar R p ↔ ExpChar A p :=
  ⟨fun _ ↦ expChar_of_injective_ringHom H p, fun _ ↦ f.expChar H p⟩

/-- If the algebra map `R →+* A` is injective then `A` has the same exponential characteristic
as `R`. -/
/-
**expChar_of_injective_algebraMap** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：expChar_of_injective_algebraMap [CommSemiring R] [Semiring A] [Algebra R A
] (h : Function.Injective (algebraMap R A)) (q : Nat) [ExpChar R q] : ExpChar A 
q
参数：h : Function.Injective (algebraMap R A)；q : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `expChar_of_injective_ringHom`：expChar_of_injective_ringHom [NonAssocSemi
ring R] [NonAssocSemiring A] {f : R ->+* A} (h : Function.Injective f) (q : Nat)
 [hR : ExpChar R q…

--- 原说明 ---
If the algebra map `R →+* A` is injective then `A` has the same exponential char
acteristic
as `R`.
-/
lemma expChar_of_injective_algebraMap [CommSemiring R] [Semiring A] [Algebra R A]
    (h : Function.Injective (algebraMap R A)) (q : ℕ) [ExpChar R q] : ExpChar A q :=
  expChar_of_injective_ringHom h q

variable (R) in
/-
**ExpChar.of_injective_algebraMap'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ExpChar.of_injective_algebraMap' [CommRing R] [CommRing A] [Algebra R A] [
FaithfulSMul R A] (q : Nat) [ExpChar R q] : ExpChar A q
参数：q : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `expChar_of_injective_ringHom`：expChar_of_injective_ringHom [NonAssocSemi
ring R] [NonAssocSemiring A] {f : R ->+* A} (h : Function.Injective f) (q : Nat)
 [hR : ExpChar R q…
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
-/
theorem ExpChar.of_injective_algebraMap' [CommRing R] [CommRing A]
    [Algebra R A] [FaithfulSMul R A] (q : ℕ) [ExpChar R q] : ExpChar A q :=
  expChar_of_injective_ringHom (FaithfulSMul.algebraMap_injective R A) q

namespace Subfield

variable [DivisionRing R] (L : Subfield R) (p : ℕ)

/-
**Subfield.charP** 是 Mathlib 中的一个实例，位于命名空间 `Subfield`。
形式化陈述：charP [CharP R p] : CharP L p
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.charP`：RingHom.charP [NonAssocSemiring R] [NonAssocSemiring A] (
f : R ->+* A) (H : Function.Injective f) (p : Nat) [CharP A p] : CharP R p
· 使用引理 `Subfield.subtype_injective`：subtype_injective (s : Subfield K) : Functio
n.Injective s.subtype
-/
instance charP [CharP R p] : CharP L p := L.subtype.charP L.subtype_injective p
/-
**Subfield.expChar** 是 Mathlib 中的一个实例，位于命名空间 `Subfield`。
形式化陈述：expChar [ExpChar R p] : ExpChar L p
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `RingHom.expChar`：RingHom.expChar [NonAssocSemiring R] [NonAssocSemiring 
A] (f : R ->+* A) (H : Function.Injective f) (p : Nat) [ExpChar A p] : ExpChar R
 p
· 使用引理 `Subfield.subtype_injective`：subtype_injective (s : Subfield K) : Functio
n.Injective s.subtype
-/
instance expChar [ExpChar R p] : ExpChar L p := L.subtype.expChar L.subtype_injective p

end Subfield

/-!
As an application, a `ℚ`-algebra has characteristic zero.
-/

-- `CharP.charP_to_charZero A _ (charP_of_injective_algebraMap h 0)` does not work
-- here as it would require `Ring A`.
section QAlgebra

variable (R : Type*) [Nontrivial R]

/-- A nontrivial `ℚ`-algebra has `CharP` equal to zero.

This cannot be a (local) instance because it would immediately form a loop with the
instance `DivisionRing.toRatAlgebra`. It's probably easier to go the other way: prove `CharZero R`
and automatically receive an `Algebra ℚ R` instance.
-/
/-
**algebraRat.charP_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：algebraRat.charP_zero [Semiring R] [Algebra Rat R] : CharP R 0
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `charP_of_injective_algebraMap`：charP_of_injective_algebraMap [CommSemiri
ng R] [Semiring A] [Algebra R A] (h : Function.Injective (algebraMap R A)) (p : 
Nat) [CharP R p] : …
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A

--- 原说明 ---
A nontrivial `ℚ`-algebra has `CharP` equal to zero.

This cannot be a (local) instance because it would immediately form a loop with 
the
instance `DivisionRing.toRatAlgebra`. It's probably easier to go the other way: 
prove `CharZero R`
and automatically receive an `Algebra ℚ R` instance.
-/
theorem algebraRat.charP_zero [Semiring R] [Algebra ℚ R] : CharP R 0 :=
  charP_of_injective_algebraMap (algebraMap ℚ R).injective 0

/-- A nontrivial `ℚ`-algebra has characteristic zero.

This cannot be a (local) instance because it would immediately form a loop with the
instance `DivisionRing.toRatAlgebra`. It's probably easier to go the other way: prove `CharZero R`
and automatically receive an `Algebra ℚ R` instance.
-/
/-
**algebraRat.charZero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：algebraRat.charZero [Ring R] [Algebra Rat R] : CharZero R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CharP.charP_to_charZero`：charP_to_charZero [CharP R 0] : CharZero R
· 使用定理 `algebraRat.charP_zero`：algebraRat.charP_zero [Semiring R] [Algebra Rat R
] : CharP R 0

--- 原说明 ---
A nontrivial `ℚ`-algebra has characteristic zero.

This cannot be a (local) instance because it would immediately form a loop with 
the
instance `DivisionRing.toRatAlgebra`. It's probably easier to go the other way: 
prove `CharZero R`
and automatically receive an `Algebra ℚ R` instance.
-/
theorem algebraRat.charZero [Ring R] [Algebra ℚ R] : CharZero R :=
  @CharP.charP_to_charZero R _ (algebraRat.charP_zero R)

end QAlgebra

/-!
An algebra over a field has the same characteristic as the field.
-/

/-
**RingHom.charP_iff_charP** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：RingHom.charP_iff_charP {K L : Type*} [DivisionRing K] [NonAssocSemiring L
] [Nontrivial L] (f : K ->+* L) (p : Nat) : CharP K p ↔ CharP L p
参数：f : K ->+* L；p : Nat。
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
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
An algebra over a field has the same characteristic as the field.
-/
lemma RingHom.charP_iff_charP {K L : Type*} [DivisionRing K] [NonAssocSemiring L] [Nontrivial L]
    (f : K →+* L) (p : ℕ) : CharP K p ↔ CharP L p := by
  simp only [charP_iff, ← f.injective.eq_iff, map_natCast f, map_zero f]

section

variable (K L : Type*) [Field K] [CommSemiring L] [Nontrivial L] [Algebra K L]

/-
**Algebra.charP_iff** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：∀ (K : Type u_3) (L : Type u_4) [inst : Field K] [inst_1 : CommSemiring L]
 [Nontrivial L] [Algebra K L] (p : ℕ),   CharP K p ↔ CharP L p
参数：K : Type u_3；L : Type u_4；p : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RingHom.charP_iff_charP`：RingHom.charP_iff_charP {K L : Type*} [Division
Ring K] [NonAssocSemiring L] [Nontrivial L] (f : K ->+* L) (p : Nat) : CharP K p
 ↔ CharP L p
-/
protected theorem Algebra.charP_iff (p : ℕ) : CharP K p ↔ CharP L p :=
  (algebraMap K L).charP_iff_charP p
/-
**Algebra.ringChar_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Algebra.ringChar_eq : ringChar K = ringChar L
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ringChar.eq_iff`：eq_iff {p : Nat} : ringChar R = p ↔ CharP R p
· 使用定理 `Algebra.charP_iff`：∀ (K : Type u_3) (L : Type u_4) [inst : Field K] [ins
t_1 : CommSemiring L] [Nontrivial L] [Algebra K L] (p : ℕ),   CharP K p ↔ CharP 
L p
· 使用定理 `ringChar.charP`：∀ (R : Type u_1) [inst : NonAssocSemiring R], CharP R (r
ingChar R)
-/
theorem Algebra.ringChar_eq : ringChar K = ringChar L := by
  rw [ringChar.eq_iff, Algebra.charP_iff K L]
  apply ringChar.charP

end

namespace FreeAlgebra

variable {R X : Type*} [CommSemiring R] (p : ℕ)

/-- If `R` has characteristic `p`, then so does `FreeAlgebra R X`. -/
/-
**FreeAlgebra.charP** 是 Mathlib 中的一个实例，位于命名空间 `FreeAlgebra`。
形式化陈述：charP [CharP R p] : CharP (FreeAlgebra R X) p
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `charP_of_injective_algebraMap`：charP_of_injective_algebraMap [CommSemiri
ng R] [Semiring A] [Algebra R A] (h : Function.Injective (algebraMap R A)) (p : 
Nat) [CharP R p] : …
· 使用定理 `Function.LeftInverse.injective`：∀ {α : Sort u_1} {β : Sort u_2} {g : β →
 α} {f : α → β}, Function.LeftInverse g f → Function.Injective f
· 使用定理 `FreeAlgebra.algebraMap_leftInverse`：algebraMap_leftInverse : Function.Le
ftInverse algebraMapInv (algebraMap R <| FreeAlgebra R X)

--- 原说明 ---
If `R` has characteristic `p`, then so does `FreeAlgebra R X`.
-/
instance charP [CharP R p] : CharP (FreeAlgebra R X) p :=
  charP_of_injective_algebraMap FreeAlgebra.algebraMap_leftInverse.injective p

/-- If `R` has characteristic `0`, then so does `FreeAlgebra R X`. -/
/-
**FreeAlgebra.charZero** 是 Mathlib 中的一个实例，位于命名空间 `FreeAlgebra`。
形式化陈述：charZero [CharZero R] : CharZero (FreeAlgebra R X)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `charZero_of_injective_algebraMap`：charZero_of_injective_algebraMap [Comm
Semiring R] [Semiring A] [Algebra R A] (h : Function.Injective (algebraMap R A))
 [CharZero R] : CharZe…
· 使用定理 `Function.LeftInverse.injective`：∀ {α : Sort u_1} {β : Sort u_2} {g : β →
 α} {f : α → β}, Function.LeftInverse g f → Function.Injective f
· 使用定理 `FreeAlgebra.algebraMap_leftInverse`：algebraMap_leftInverse : Function.Le
ftInverse algebraMapInv (algebraMap R <| FreeAlgebra R X)

--- 原说明 ---
If `R` has characteristic `0`, then so does `FreeAlgebra R X`.
-/
instance charZero [CharZero R] : CharZero (FreeAlgebra R X) :=
  charZero_of_injective_algebraMap FreeAlgebra.algebraMap_leftInverse.injective

end FreeAlgebra

namespace IsFractionRing

variable (R : Type*) {K : Type*} [CommRing R] [Field K] [Algebra R K] [IsFractionRing R K]
variable (p : ℕ)

/-- If `R` has characteristic `p`, then so does Frac(R). -/
/-
**IsFractionRing.charP_of_isFractionRing** 是 Mathlib 中的一个定理，位于命名空间 `IsFractionRi
ng`。
形式化陈述：charP_of_isFractionRing [CharP R p] : CharP K p
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `charP_of_injective_algebraMap`：charP_of_injective_algebraMap [CommSemiri
ng R] [Semiring A] [Algebra R A] (h : Function.Injective (algebraMap R A)) (p : 
Nat) [CharP R p] : …
· 使用定理 `IsFractionRing.injective`：∀ (R : Type u_1) [inst : CommRing R] (K : Type
 u_5) [inst_1 : CommRing K] [inst_2 : Algebra R K] [IsFractionRing R K],   Funct
ion.Injective …

--- 原说明 ---
If `R` has characteristic `p`, then so does Frac(R).
-/
theorem charP_of_isFractionRing [CharP R p] : CharP K p :=
  charP_of_injective_algebraMap (IsFractionRing.injective R K) p

/-- If `R` has characteristic `0`, then so does Frac(R). -/
/-
**IsFractionRing.charZero_of_isFractionRing** 是 Mathlib 中的一个定理，位于命名空间 `IsFractio
nRing`。
形式化陈述：charZero_of_isFractionRing [CharZero R] : CharZero K
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CharP.charP_to_charZero`：charP_to_charZero [CharP R 0] : CharZero R
· 使用定理 `IsFractionRing.charP_of_isFractionRing`：charP_of_isFractionRing [CharP R
 p] : CharP K p

--- 原说明 ---
If `R` has characteristic `0`, then so does Frac(R).
-/
theorem charZero_of_isFractionRing [CharZero R] : CharZero K :=
  @CharP.charP_to_charZero K _ (charP_of_isFractionRing R 0)

variable [IsDomain R]

/-- If `R` has characteristic `p`, then so does `FractionRing R`. -/
/-
**IsFractionRing.charP** 是 Mathlib 中的一个实例，位于命名空间 `IsFractionRing`。
形式化陈述：charP [CharP R p] : CharP (FractionRing R) p
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsFractionRing.charP_of_isFractionRing`：charP_of_isFractionRing [CharP R
 p] : CharP K p

--- 原说明 ---
If `R` has characteristic `p`, then so does `FractionRing R`.
-/
instance charP [CharP R p] : CharP (FractionRing R) p :=
  charP_of_isFractionRing R p

/-- If `R` has characteristic `0`, then so does `FractionRing R`. -/
/-
**IsFractionRing.charZero** 是 Mathlib 中的一个实例，位于命名空间 `IsFractionRing`。
形式化陈述：charZero [CharZero R] : CharZero (FractionRing R)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsFractionRing.charZero_of_isFractionRing`：charZero_of_isFractionRing [C
harZero R] : CharZero K

--- 原说明 ---
If `R` has characteristic `0`, then so does `FractionRing R`.
-/
instance charZero [CharZero R] : CharZero (FractionRing R) :=
  charZero_of_isFractionRing R

end IsFractionRing

