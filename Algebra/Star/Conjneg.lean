/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Star.Pi
public import Mathlib.Algebra.Group.Pointwise.Set.Basic

/-!
# Conjugation-negation operator

This file defines the conjugation-negation operator, useful in Fourier analysis.

The way this operator enters the picture is that the adjoint of convolution with a function `f` is
convolution with `conjneg f`.
-/

@[expose] public section

open Function
open scoped ComplexConjugate

variable {ι G R : Type*} [AddGroup G]

section CommSemiring
variable [CommSemiring R] [StarRing R] {f g : G → R}

/-- Conjugation-negation. Sends `f` to `fun x ↦ conj (f (-x))`. -/
/-
**conjneg** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：conjneg (f : G -> R) : G -> R
参数：f : G -> R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Conjugation-negation. Sends `f` to `fun x ↦ conj (f (-x))`.
-/
def conjneg (f : G → R) : G → R := conj fun x ↦ f (-x)
/-
**conjneg_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {G : Type u_2} {R : Type u_3} [inst : AddGroup G] [inst_1 : CommSemiring
 R] [inst_2 : StarRing R] (f : G → R) (x : G),   conjneg f x = (starRingEnd R) (
f (-x))
参数：f : G → R；x : G；starRingEnd R；f (-x)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma conjneg_apply (f : G → R) (x : G) : conjneg f x = conj (f (-x)) := rfl
/-
**conjneg_conjneg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {G : Type u_2} {R : Type u_3} [inst : AddGroup G] [inst_1 : CommSemiring
 R] [inst_2 : StarRing R] (f : G → R),   conjneg (conjneg f) = f
参数：f : G → R；conjneg f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `RingHomCompTriple.comp_apply`：comp_apply [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]
 {x : R₁} : σ₂₃ (σ₁₂ x) = σ₁₃ x
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma conjneg_conjneg (f : G → R) : conjneg (conjneg f) = f := by ext; simp
/-
**conjneg_involutive** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：conjneg_involutive : Involutive (conjneg : (G -> R) -> G -> R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `conjneg_conjneg`：∀ {G : Type u_2} {R : Type u_3} [inst : AddGroup G] [in
st_1 : CommSemiring R] [inst_2 : StarRing R] (f : G → R),   conjneg (conjneg f) 
= f
-/
lemma conjneg_involutive : Involutive (conjneg : (G → R) → G → R) := conjneg_conjneg
/-
**conjneg_bijective** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：conjneg_bijective : Bijective (conjneg : (G -> R) -> G -> R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Involutive.bijective`：∀ {α : Sort u} {f : α → α}, Function.Invo
lutive f → Function.Bijective f
· 使用引理 `conjneg_involutive`：conjneg_involutive : Involutive (conjneg : (G -> R) 
-> G -> R)
-/
lemma conjneg_bijective : Bijective (conjneg : (G → R) → G → R) := conjneg_involutive.bijective
/-
**conjneg_injective** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：conjneg_injective : Injective (conjneg : (G -> R) -> G -> R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Involutive.injective`：∀ {α : Sort u} {f : α → α}, Function.Invo
lutive f → Function.Injective f
· 使用引理 `conjneg_involutive`：conjneg_involutive : Involutive (conjneg : (G -> R) 
-> G -> R)
-/
lemma conjneg_injective : Injective (conjneg : (G → R) → G → R) := conjneg_involutive.injective
/-
**conjneg_surjective** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：conjneg_surjective : Surjective (conjneg : (G -> R) -> G -> R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Involutive.surjective`：∀ {α : Sort u} {f : α → α}, Function.Inv
olutive f → Function.Surjective f
· 使用引理 `conjneg_involutive`：conjneg_involutive : Involutive (conjneg : (G -> R) 
-> G -> R)
-/
lemma conjneg_surjective : Surjective (conjneg : (G → R) → G → R) := conjneg_involutive.surjective
/-
**conjneg_inj** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {G : Type u_2} {R : Type u_3} [inst : AddGroup G] [inst_1 : CommSemiring
 R] [inst_2 : StarRing R] {f g : G → R},   conjneg f = conjneg g ↔ f = g
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用引理 `conjneg_injective`：conjneg_injective : Injective (conjneg : (G -> R) -> 
G -> R)
-/
@[simp] lemma conjneg_inj : conjneg f = conjneg g ↔ f = g := conjneg_injective.eq_iff
/-
**conjneg_ne_conjneg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：conjneg_ne_conjneg : conjneg f != conjneg g ↔ f != g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.ne_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {x y : α}, f x ≠ f y ↔ x ≠ y
· 使用引理 `conjneg_injective`：conjneg_injective : Injective (conjneg : (G -> R) -> 
G -> R)
-/
lemma conjneg_ne_conjneg : conjneg f ≠ conjneg g ↔ f ≠ g := conjneg_injective.ne_iff
/-
**conjneg_conj** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {G : Type u_2} {R : Type u_3} [inst : AddGroup G] [inst_1 : CommSemiring
 R] [inst_2 : StarRing R] (f : G → R),   conjneg ((starRingEnd (G → R)) f) = (st
arRingEnd (G → R)) (conjneg f)
参数：f : G → R；(starRingEnd (G → R)) f；starRingEnd (G → R)；conjneg f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma conjneg_conj (f : G → R) : conjneg (conj f) = conj (conjneg f) := rfl
/-
**conjneg_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {G : Type u_2} {R : Type u_3} [inst : AddGroup G] [inst_1 : CommSemiring
 R] [inst_2 : StarRing R], conjneg 0 = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma conjneg_zero : conjneg (0 : G → R) = 0 := by ext; simp
/-
**conjneg_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {G : Type u_2} {R : Type u_3} [inst : AddGroup G] [inst_1 : CommSemiring
 R] [inst_2 : StarRing R], conjneg 1 = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma conjneg_one : conjneg (1 : G → R) = 1 := by ext; simp
/-
**conjneg_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {G : Type u_2} {R : Type u_3} [inst : AddGroup G] [inst_1 : CommSemiring
 R] [inst_2 : StarRing R] (f g : G → R),   conjneg (f + g) = conjneg f + conjneg
 g
参数：f g : G → R；f + g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
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
@[simp] lemma conjneg_add (f g : G → R) : conjneg (f + g) = conjneg f + conjneg g := by ext; simp
/-
**conjneg_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {G : Type u_2} {R : Type u_3} [inst : AddGroup G] [inst_1 : CommSemiring
 R] [inst_2 : StarRing R] (f g : G → R),   conjneg (f * g) = conjneg f * conjneg
 g
参数：f g : G → R；f * g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma conjneg_mul (f g : G → R) : conjneg (f * g) = conjneg f * conjneg g := by ext; simp
/-
**conjneg_sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {ι : Type u_1} {G : Type u_2} {R : Type u_3} [inst : AddGroup G] [inst_1
 : CommSemiring R] [inst_2 : StarRing R]   (s : Finset ι) (f : ι → G → R), conjn
eg (∑ i ∈ s, f i) = ∑ i ∈ s, conjneg (f i)
参数：s : Finset ι；f : ι → G → R；∑ i ∈ s, f i；f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma conjneg_sum (s : Finset ι) (f : ι → G → R) :
    conjneg (∑ i ∈ s, f i) = ∑ i ∈ s, conjneg (f i) := by ext; simp
/-
**conjneg_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {ι : Type u_1} {G : Type u_2} {R : Type u_3} [inst : AddGroup G] [inst_1
 : CommSemiring R] [inst_2 : StarRing R]   (s : Finset ι) (f : ι → G → R), conjn
eg (∏ i ∈ s, f i) = ∏ i ∈ s, conjneg (f i)
参数：s : Finset ι；f : ι → G → R；∏ i ∈ s, f i；f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_apply`：Finset.prod_apply {α : Type*} {M : α -> Type*} [foral
l a, CommMonoid (M a)] (a : α) (s : Finset ι) (g : ι -> forall a, M a) : (∏ c in
 s, g c…
· 使用定理 `map_prod`：map_prod [CommMonoid M] [CommMonoid N] {G : Type*} [FunLike G 
M N] [MonoidHomClass G M N] (g : G) (f : ι -> M) (s : Finset ι) : g (∏ x in s,…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma conjneg_prod (s : Finset ι) (f : ι → G → R) :
    conjneg (∏ i ∈ s, f i) = ∏ i ∈ s, conjneg (f i) := by ext; simp
/-
**conjneg_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {G : Type u_2} {R : Type u_3} [inst : AddGroup G] [inst_1 : CommSemiring
 R] [inst_2 : StarRing R] {f : G → R},   conjneg f = 0 ↔ f = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `conjneg_inj`：∀ {G : Type u_2} {R : Type u_3} [inst : AddGroup G] [inst_1
 : CommSemiring R] [inst_2 : StarRing R] {f g : G → R},   conjneg f = conjneg g 
↔…
· 使用定理 `conjneg_conjneg`：∀ {G : Type u_2} {R : Type u_3} [inst : AddGroup G] [in
st_1 : CommSemiring R] [inst_2 : StarRing R] (f : G → R),   conjneg (conjneg f) 
= f
· 使用定理 `conjneg_zero`：∀ {G : Type u_2} {R : Type u_3} [inst : AddGroup G] [inst_
1 : CommSemiring R] [inst_2 : StarRing R], conjneg 0 = 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma conjneg_eq_zero : conjneg f = 0 ↔ f = 0 := by
  rw [← conjneg_inj, conjneg_conjneg, conjneg_zero]
/-
**conjneg_eq_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {G : Type u_2} {R : Type u_3} [inst : AddGroup G] [inst_1 : CommSemiring
 R] [inst_2 : StarRing R] {f : G → R},   conjneg f = 1 ↔ f = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `conjneg_inj`：∀ {G : Type u_2} {R : Type u_3} [inst : AddGroup G] [inst_1
 : CommSemiring R] [inst_2 : StarRing R] {f g : G → R},   conjneg f = conjneg g 
↔…
· 使用定理 `conjneg_conjneg`：∀ {G : Type u_2} {R : Type u_3} [inst : AddGroup G] [in
st_1 : CommSemiring R] [inst_2 : StarRing R] (f : G → R),   conjneg (conjneg f) 
= f
· 使用定理 `conjneg_one`：∀ {G : Type u_2} {R : Type u_3} [inst : AddGroup G] [inst_1
 : CommSemiring R] [inst_2 : StarRing R], conjneg 1 = 1
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma conjneg_eq_one : conjneg f = 1 ↔ f = 1 := by
  rw [← conjneg_inj, conjneg_conjneg, conjneg_one]
/-
**conjneg_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：conjneg_ne_zero : conjneg f != 0 ↔ f != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `conjneg_eq_zero`：∀ {G : Type u_2} {R : Type u_3} [inst : AddGroup G] [in
st_1 : CommSemiring R] [inst_2 : StarRing R] {f : G → R},   conjneg f = 0 ↔ f = 
0
-/
lemma conjneg_ne_zero : conjneg f ≠ 0 ↔ f ≠ 0 := conjneg_eq_zero.not
/-
**conjneg_ne_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：conjneg_ne_one : conjneg f != 1 ↔ f != 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `conjneg_eq_one`：∀ {G : Type u_2} {R : Type u_3} [inst : AddGroup G] [ins
t_1 : CommSemiring R] [inst_2 : StarRing R] {f : G → R},   conjneg f = 1 ↔ f = 1
-/
lemma conjneg_ne_one : conjneg f ≠ 1 ↔ f ≠ 1 := conjneg_eq_one.not
/-
**sum_conjneg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：sum_conjneg [Fintype G] (f : G -> R) : ∑ a, conjneg f a = ∑ a, conj (f a)
参数：f : G -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fintype.sum_equiv`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst 
: Fintype ι] [inst_1 : Fintype κ] [inst_2 : AddCommMonoid M]   (e : ι ≃ κ) (f : 
ι → M) …
-/
lemma sum_conjneg [Fintype G] (f : G → R) : ∑ a, conjneg f a = ∑ a, conj (f a) :=
  Fintype.sum_equiv (Equiv.neg _) _ _ fun _ ↦ rfl
/-
**support_conjneg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {G : Type u_2} {R : Type u_3} [inst : AddGroup G] [inst_1 : CommSemiring
 R] [inst_2 : StarRing R] (f : G → R),   Function.support (conjneg f) = -Functio
n.support f
参数：f : G → R；conjneg f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma support_conjneg (f : G → R) : support (conjneg f) = -support f := by
  ext; simp [starRingEnd_apply]

/-- `conjneg` bundled as a ring homomorphism. -/
/-
**conjnegRingHom** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：{G : Type u_2} → {R : Type u_3} → [AddGroup G] → [inst : CommSemiring R] →
 [StarRing R] → (G → R) →+* G → R
参数：G → R。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `conjneg_one`：∀ {G : Type u_2} {R : Type u_3} [inst : AddGroup G] [inst_1
 : CommSemiring R] [inst_2 : StarRing R], conjneg 1 = 1
· 使用定理 `conjneg_mul`：∀ {G : Type u_2} {R : Type u_3} [inst : AddGroup G] [inst_1
 : CommSemiring R] [inst_2 : StarRing R] (f g : G → R),   conjneg (f * g) = conj
n…
· 使用定理 `conjneg_zero`：∀ {G : Type u_2} {R : Type u_3} [inst : AddGroup G] [inst_
1 : CommSemiring R] [inst_2 : StarRing R], conjneg 0 = 0
· 使用定理 `conjneg_add`：∀ {G : Type u_2} {R : Type u_3} [inst : AddGroup G] [inst_1
 : CommSemiring R] [inst_2 : StarRing R] (f g : G → R),   conjneg (f + g) = conj
n…

--- 原说明 ---
`conjneg` bundled as a ring homomorphism.
-/
@[simps] def conjnegRingHom : (G → R) →+* (G → R) where
  toFun := conjneg
  map_zero' := conjneg_zero
  map_one' := conjneg_one
  map_add' := conjneg_add
  map_mul' := conjneg_mul

end CommSemiring

section CommRing
variable [CommRing R] [StarRing R]

/-
**conjneg_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {G : Type u_2} {R : Type u_3} [inst : AddGroup G] [inst_1 : CommRing R] 
[inst_2 : StarRing R] (f g : G → R),   conjneg (f - g) = conjneg f - conjneg g
参数：f g : G → R；f - g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma conjneg_sub (f g : G → R) : conjneg (f - g) = conjneg f - conjneg g := by ext; simp
/-
**conjneg_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {G : Type u_2} {R : Type u_3} [inst : AddGroup G] [inst_1 : CommRing R] 
[inst_2 : StarRing R] (f : G → R),   conjneg (-f) = -conjneg f
参数：f : G → R；-f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma conjneg_neg (f : G → R) : conjneg (-f) = -conjneg f := by ext; simp

end CommRing

