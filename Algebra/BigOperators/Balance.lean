/-
Copyright (c) 2023 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
module

public import Mathlib.Algebra.BigOperators.Expect

/-!
# Balancing a function

This file defines the balancing of a function `f`, defined as `f` minus its average.

This is the unique function `g` such that `f a - f b = g a - g b` for all `a` and `b`, and
`∑ a, g a = 0`. This is particularly useful in Fourier analysis as `f` and `g` then have the same
Fourier transform, except in the `0`-th frequency where the Fourier transform of `g` vanishes.
-/

@[expose] public section

open Finset Function
open scoped BigOperators

variable {ι H F G : Type*}

namespace Fintype

section AddCommGroup
variable [Fintype ι] [AddCommGroup G] [Module ℚ≥0 G] [AddCommGroup H] [Module ℚ≥0 H]

/-- The balancing of a function, namely the function minus its average. -/
/-
**Fintype.balance** 是 Mathlib 中的一个定义，位于命名空间 `Fintype`。
形式化陈述：balance (f : ι -> G) : ι -> G
参数：f : ι -> G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The balancing of a function, namely the function minus its average.
-/
def balance (f : ι → G) : ι → G := f - Function.const _ (𝔼 y, f y)
/-
**Fintype.balance_apply** 是 Mathlib 中的一个引理，位于命名空间 `Fintype`。
形式化陈述：balance_apply (f : ι -> G) (x : ι) : balance f x = f x - 𝔼 y, f y
参数：f : ι -> G；x : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma balance_apply (f : ι → G) (x : ι) : balance f x = f x - 𝔼 y, f y := rfl
/-
**Fintype.balance_zero** 是 Mathlib 中的一个定理，位于命名空间 `Fintype`。
形式化陈述：∀ {ι : Type u_1} {G : Type u_4} [inst : Fintype ι] [inst_1 : AddCommGroup 
G] [inst_2 : _root_.Module ℚ≥0 G],   Fintype.balance 0 = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.expect_congr`：expect_congr {t : Finset ι} (hst : s = t) (h : fora
ll i in t, f i = g i) : 𝔼 i in s, f i = 𝔼 i in t, g i
· 使用定理 `Finset.expect_const_zero`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCom
mMonoid M] [inst_1 : _root_.Module ℚ≥0 M] (s : Finset ι),   (s.expect fun _i => 
0) = 0
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma balance_zero : balance (0 : ι → G) = 0 := by simp [balance]
/-
**Fintype.balance_add** 是 Mathlib 中的一个定理，位于命名空间 `Fintype`。
形式化陈述：∀ {ι : Type u_1} {G : Type u_4} [inst : Fintype ι] [inst_1 : AddCommGroup 
G] [inst_2 : _root_.Module ℚ≥0 G]   (f g : ι → G), Fintype.balance (f + g) = Fin
type.balance f + Fintype.balance g
参数：f g : ι → G；f + g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.expect_congr`：expect_congr {t : Finset ι} (hst : s = t) (h : fora
ll i in t, f i = g i) : 𝔼 i in s, f i = 𝔼 i in t, g i
· 使用引理 `Finset.expect_add_distrib`：expect_add_distrib (s : Finset ι) (f g : ι ->
 M) : 𝔼 i in s, (f i + g i) = 𝔼 i in s, f i + 𝔼 i in s, g i
· 使用定理 `add_sub_add_comm`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b
 c d : α), a + b - (c + d) = a - c + (b - d)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma balance_add (f g : ι → G) : balance (f + g) = balance f + balance g := by
  simp only [balance, expect_add_distrib, ← const_add, add_sub_add_comm, Pi.add_apply]
/-
**Fintype.balance_sub** 是 Mathlib 中的一个定理，位于命名空间 `Fintype`。
形式化陈述：∀ {ι : Type u_1} {G : Type u_4} [inst : Fintype ι] [inst_1 : AddCommGroup 
G] [inst_2 : _root_.Module ℚ≥0 G]   (f g : ι → G), Fintype.balance (f - g) = Fin
type.balance f - Fintype.balance g
参数：f g : ι → G；f - g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.expect_congr`：expect_congr {t : Finset ι} (hst : s = t) (h : fora
ll i in t, f i = g i) : 𝔼 i in s, f i = 𝔼 i in t, g i
· 使用引理 `Finset.expect_sub_distrib`：expect_sub_distrib (s : Finset ι) (f g : ι ->
 M) : 𝔼 i in s, (f i - g i) = 𝔼 i in s, f i - 𝔼 i in s, g i
· 使用定理 `sub_sub_sub_comm`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b
 c d : α), a - b - (c - d) = a - c - (b - d)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma balance_sub (f g : ι → G) : balance (f - g) = balance f - balance g := by
  simp only [balance, expect_sub_distrib, const_sub, sub_sub_sub_comm, Pi.sub_apply]
/-
**Fintype.balance_neg** 是 Mathlib 中的一个定理，位于命名空间 `Fintype`。
形式化陈述：∀ {ι : Type u_1} {G : Type u_4} [inst : Fintype ι] [inst_1 : AddCommGroup 
G] [inst_2 : _root_.Module ℚ≥0 G] (f : ι → G),   Fintype.balance (-f) = -Fintype
.balance f
参数：f : ι → G；-f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.expect_congr`：expect_congr {t : Finset ι} (hst : s = t) (h : fora
ll i in t, f i = g i) : 𝔼 i in s, f i = 𝔼 i in t, g i
· 使用引理 `Finset.expect_neg_distrib`：expect_neg_distrib (s : Finset ι) (f : ι -> M
) : 𝔼 i in s, -f i = -𝔼 i in s, f i
· 使用定理 `neg_sub'`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b : α), -
(a - b) = -a - -b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma balance_neg (f : ι → G) : balance (-f) = -balance f := by
  simp only [balance, expect_neg_distrib, const_neg, neg_sub', Pi.neg_apply]
/-
**Fintype.sum_balance** 是 Mathlib 中的一个定理，位于命名空间 `Fintype`。
形式化陈述：∀ {ι : Type u_1} {G : Type u_4} [inst : Fintype ι] [inst_1 : AddCommGroup 
G] [inst_2 : _root_.Module ℚ≥0 G] (f : ι → G),   ∑ x, Fintype.balance f x = 0
参数：f : ι → G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.univ_eq_empty`：univ_eq_empty [IsEmpty α] : (univ : Finset α) = ∅
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Finset.expect_congr`：expect_congr {t : Finset ι} (hst : s = t) (h : fora
ll i in t, f i = g i) : 𝔼 i in s, f i = 𝔼 i in t, g i
· 使用定理 `Finset.expect_empty`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMono
id M] [inst_1 : _root_.Module ℚ≥0 M] (f : ι → M),   (∅.expect fun i => f i) = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.sum_sub_distrib`：∀ {ι : Type u_1} {G : Type u_5} {s : Finset ι} [
inst : SubtractionCommMonoid G] (f g : ι → G),   ∑ x ∈ s, (f x - g x) = ∑ x ∈ s,
 f x - ∑ x ∈…
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `Fintype.card_smul_expect`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCom
mMonoid M] [inst_1 : _root_.Module ℚ≥0 M] [inst_2 : Fintype ι]   (f : ι → M), (F
intype.card ι …
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
-/
@[simp] lemma sum_balance (f : ι → G) : ∑ x, balance f x = 0 := by
  cases isEmpty_or_nonempty ι <;> simp [balance_apply]
/-
**Fintype.expect_balance** 是 Mathlib 中的一个定理，位于命名空间 `Fintype`。
形式化陈述：∀ {ι : Type u_1} {G : Type u_4} [inst : Fintype ι] [inst_1 : AddCommGroup 
G] [inst_2 : _root_.Module ℚ≥0 G] (f : ι → G),   (Finset.univ.expect fun x => Fi
ntype.balance f x) = 0
参数：f : ι → G；Finset.univ.expect fun x => Fintype.balance f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Fintype.sum_balance`：∀ {ι : Type u_1} {G : Type u_4} [inst : Fintype ι] 
[inst_1 : AddCommGroup G] [inst_2 : _root_.Module ℚ≥0 G] (f : ι → G),   ∑ x, Fin
type.bala…
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma expect_balance (f : ι → G) : 𝔼 x, balance f x = 0 := by simp [expect]
/-
**Fintype.balance_idem** 是 Mathlib 中的一个定理，位于命名空间 `Fintype`。
形式化陈述：∀ {ι : Type u_1} {G : Type u_4} [inst : Fintype ι] [inst_1 : AddCommGroup 
G] [inst_2 : _root_.Module ℚ≥0 G] (f : ι → G),   Fintype.balance (Fintype.balanc
e f) = Fintype.balance f
参数：f : ι → G；Fintype.balance f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Finset.expect_congr`：expect_congr {t : Finset ι} (hst : s = t) (h : fora
ll i in t, f i = g i) : 𝔼 i in s, f i = 𝔼 i in t, g i
· 使用定理 `Finset.univ_eq_empty`：univ_eq_empty [IsEmpty α] : (univ : Finset α) = ∅
· 使用定理 `Finset.expect_empty`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMono
id M] [inst_1 : _root_.Module ℚ≥0 M] (f : ι → M),   (∅.expect fun i => f i) = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Finset.expect_sub_distrib`：expect_sub_distrib (s : Finset ι) (f g : ι ->
 M) : 𝔼 i in s, (f i - g i) = 𝔼 i in s, f i - 𝔼 i in s, g i
· 使用定理 `Finset.expect_const`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMono
id M] [inst_1 : _root_.Module ℚ≥0 M] {s : Finset ι},   s.Nonempty → ∀ (a : M), (
s.expect …
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
-/
@[simp] lemma balance_idem (f : ι → G) : balance (balance f) = balance f := by
  cases isEmpty_or_nonempty ι <;> ext x <;> simp [balance, expect_sub_distrib, univ_nonempty]
/-
**Fintype.map_balance** 是 Mathlib 中的一个定理，位于命名空间 `Fintype`。
形式化陈述：∀ {ι : Type u_1} {H : Type u_2} {F : Type u_3} {G : Type u_4} [inst : Fint
ype ι] [inst_1 : AddCommGroup G]   [inst_2 : _root_.Module ℚ≥0 G] [inst_3 : AddC
ommGroup H] [inst_4 : _root_.Module ℚ≥0 H] [inst_5 : FunLike F G H]   [LinearMap
Class F ℚ≥0 G H] (g : F) (f : ι → G) (a : ι), g (Fintype.balance f a) = Fintype.
balance (⇑g ∘ f) a
参数：g : F；f : ι → G；a : ι；Fintype.balance f a；⇑g ∘ f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `map_expect`：∀ {ι : Type u_1} {M : Type u_4} {N : Type u_5} [inst : AddCo
mmMonoid M] [inst_1 : _root_.Module ℚ≥0 M]   [inst_2 : AddCommMonoid N] [inst_3 
…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Finset.expect_congr`：expect_congr {t : Finset ι} (hst : s = t) (h : fora
ll i in t, f i = g i) : 𝔼 i in s, f i = 𝔼 i in t, g i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma map_balance [FunLike F G H] [LinearMapClass F ℚ≥0 G H] (g : F) (f : ι → G) (a : ι) :
    g (balance f a) = balance (g ∘ f) a := by simp [balance, map_expect]

end AddCommGroup
end Fintype

