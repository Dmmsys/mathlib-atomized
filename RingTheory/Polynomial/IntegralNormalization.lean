/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Kim Morrison, Jens Wagemaker, Andrew Yang, Yuyang Zhao
-/
module

public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.RingTheory.Polynomial.ScaleRoots

/-!
# Theory of monic polynomials

We define `integralNormalization`, which relate arbitrary polynomials to monic ones.
-/

@[expose] public section


open Polynomial

namespace Polynomial

universe u v y

variable {R : Type u} {S : Type v} {a b : R} {m n : ℕ} {ι : Type y}

section IntegralNormalization

section Semiring

variable [Semiring R]

/-- If `p : R[X]` is a nonzero polynomial with root `z`, `integralNormalization p` is
a monic polynomial with root `leadingCoeff f * z`.

Moreover, `integralNormalization 0 = 0`.
-/
/-
**Polynomial.integralNormalization** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：integralNormalization (p : R[X]) : R[X]
参数：p : R[X]。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `p : R[X]` is a nonzero polynomial with root `z`, `integralNormalization p` i
s
a monic polynomial with root `leadingCoeff f * z`.

Moreover, `integralNormalization 0 = 0`.
-/
noncomputable def integralNormalization (p : R[X]) : R[X] :=
  p.sum fun i a ↦
    monomial i (if p.degree = i then 1 else a * p.leadingCoeff ^ (p.natDegree - 1 - i))

@[simp]
/-
**Polynomial.integralNormalization_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：integralNormalization_zero : integralNormalization (0 : R[X]) = 0
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
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `zero_tsub`：zero_tsub (a : α) : 0 - a = 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Polynomial.sum_zero_index`：sum_zero_index {S : Type*} [AddCommMonoid S] 
(f : Nat -> R -> S) : (0 : R[X]).sum f = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem integralNormalization_zero : integralNormalization (0 : R[X]) = 0 := by
  simp [integralNormalization]

@[simp]
/-
**Polynomial.integralNormalization_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：integralNormalization_C {x : R} (hx : x != 0) : integralNormalization (C x
) = 1
参数：hx : x != 0。
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
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Polynomial.degree_C`：degree_C (ha : a != 0) : degree (C a) = (0 : WithBo
t Nat)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.leadingCoeff_C`：leadingCoeff_C (a : R) : leadingCoeff (C a) =
 a
· 使用定理 `Polynomial.natDegree_C`：natDegree_C (a : R) : natDegree (C a) = 0
· 使用定理 `zero_tsub`：zero_tsub (a : α) : 0 - a = 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Polynomial.support_C`：support_C {a : R} (h : a != 0) : (C a).support = s
ingleton 0
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
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
-/
theorem integralNormalization_C {x : R} (hx : x ≠ 0) : integralNormalization (C x) = 1 := by
  simp [integralNormalization, sum_def, support_C hx, degree_C hx]

variable {p : R[X]}
/-
**Polynomial.integralNormalization_coeff** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：integralNormalization_coeff {i : Nat} : (integralNormalization p).coeff i 
= if p.degree = i then 1 else coeff p i * p.leadingCoeff ^ (p.natDegree - 1 - i)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.coeff_ne_zero_of_eq_degree`：coeff_ne_zero_of_eq_degree (hn : 
degree p = n) : coeff p n != 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.finsetSum_coeff`：finsetSum_coeff {ι : Type*} (s : Finset ι) (
f : ι -> R[X]) (n : Nat) : coeff (∑ b in s, f b) n = ∑ b in s, coeff (f b) n
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Polynomial.coeff_monomial`：coeff_monomial : coeff (monomial n a) m = if 
n = m then a else 0
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_ite_eq'`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoi
d M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if
 x = a t…
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem integralNormalization_coeff {i : ℕ} :
    (integralNormalization p).coeff i =
      if p.degree = i then 1 else coeff p i * p.leadingCoeff ^ (p.natDegree - 1 - i) := by
  have : p.coeff i = 0 → p.degree ≠ i := fun hc hd => coeff_ne_zero_of_eq_degree hd hc
  simp +contextual [sum_def, integralNormalization, coeff_monomial, this,
    mem_support_iff]
/-
**Polynomial.support_integralNormalization_subset** 是 Mathlib 中的一个定理，位于命名空间 `Pol
ynomial`。
形式化陈述：support_integralNormalization_subset : (integralNormalization p).support s
ubseteq p.support
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.finsetSum_coeff`：finsetSum_coeff {ι : Type*} (s : Finset ι) (
f : ι -> R[X]) (n : Nat) : coeff (∑ b in s, f b) n = ∑ b in s, coeff (f b) n
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Polynomial.coeff_monomial`：coeff_monomial : coeff (monomial n a) m = if 
n = m then a else 0
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_ite_eq'`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoi
d M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if
 x = a t…
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem support_integralNormalization_subset :
    (integralNormalization p).support ⊆ p.support := by
  intro
  simp +contextual [sum_def, integralNormalization, coeff_monomial, mem_support_iff]
/-
**Polynomial.integralNormalization_coeff_degree** 是 Mathlib 中的一个定理，位于命名空间 `Polyn
omial`。
形式化陈述：integralNormalization_coeff_degree {i : Nat} (hi : p.degree = i) : (integr
alNormalization p).coeff i = 1
参数：hi : p.degree = i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.integralNormalization_coeff`：integralNormalization_coeff {i :
 Nat} : (integralNormalization p).coeff i = if p.degree = i then 1 else coeff p 
i * p.leadingCoeff ^ (p.natD…
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
theorem integralNormalization_coeff_degree {i : ℕ} (hi : p.degree = i) :
    (integralNormalization p).coeff i = 1 := by rw [integralNormalization_coeff, if_pos hi]
/-
**Polynomial.integralNormalization_coeff_natDegree** 是 Mathlib 中的一个定理，位于命名空间 `Po
lynomial`。
形式化陈述：integralNormalization_coeff_natDegree (hp : p != 0) : (integralNormalizati
on p).coeff (natDegree p) = 1
参数：hp : p != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.integralNormalization_coeff_degree`：integralNormalization_coe
ff_degree {i : Nat} (hi : p.degree = i) : (integralNormalization p).coeff i = 1
· 使用定理 `Polynomial.degree_eq_natDegree`：degree_eq_natDegree (hp : p != 0) : degr
ee p = (natDegree p : WithBot Nat)
-/
theorem integralNormalization_coeff_natDegree (hp : p ≠ 0) :
    (integralNormalization p).coeff (natDegree p) = 1 :=
  integralNormalization_coeff_degree (degree_eq_natDegree hp)
/-
**Polynomial.integralNormalization_coeff_degree_ne** 是 Mathlib 中的一个定理，位于命名空间 `Po
lynomial`。
形式化陈述：integralNormalization_coeff_degree_ne {i : Nat} (hi : p.degree != i) : coe
ff (integralNormalization p) i = coeff p i * p.leadingCoeff ^ (p.natDegree - 1 -
 i)
参数：hi : p.degree != i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.integralNormalization_coeff`：integralNormalization_coeff {i :
 Nat} : (integralNormalization p).coeff i = if p.degree = i then 1 else coeff p 
i * p.leadingCoeff ^ (p.natD…
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem integralNormalization_coeff_degree_ne {i : ℕ} (hi : p.degree ≠ i) :
    coeff (integralNormalization p) i = coeff p i * p.leadingCoeff ^ (p.natDegree - 1 - i) := by
  rw [integralNormalization_coeff, if_neg hi]
/-
**Polynomial.integralNormalization_coeff_ne_natDegree** 是 Mathlib 中的一个定理，位于命名空间 
`Polynomial`。
形式化陈述：integralNormalization_coeff_ne_natDegree {i : Nat} (hi : i != natDegree p)
 : coeff (integralNormalization p) i = coeff p i * p.leadingCoeff ^ (p.natDegree
 - 1 - i)
参数：hi : i != natDegree p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.integralNormalization_coeff_degree_ne`：integralNormalization_
coeff_degree_ne {i : Nat} (hi : p.degree != i) : coeff (integralNormalization p)
 i = coeff p i * p.leadingCoeff ^ (p.n…
· 使用定理 `Polynomial.degree_ne_of_natDegree_ne`：degree_ne_of_natDegree_ne {n : Nat
} : p.natDegree != n -> degree p != n
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
-/
theorem integralNormalization_coeff_ne_natDegree {i : ℕ} (hi : i ≠ natDegree p) :
    coeff (integralNormalization p) i = coeff p i * p.leadingCoeff ^ (p.natDegree - 1 - i) :=
  integralNormalization_coeff_degree_ne (degree_ne_of_natDegree_ne hi.symm)

@[simp]
/-
**Polynomial.degree_integralNormalization** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`
。
形式化陈述：degree_integralNormalization : p.integralNormalization.degree = p.degree
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.degree_of_subsingleton`：degree_of_subsingleton [Subsingleton 
R] : degree p = ⊥
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.integralNormalization_zero`：integralNormalization_zero : inte
gralNormalization (0 : R[X]) = 0
· 使用定理 `Polynomial.degree_eq_natDegree`：degree_eq_natDegree (hp : p != 0) : degr
ee p = (natDegree p : WithBot Nat)
· 使用定理 `Polynomial.degree_eq_of_le_of_coeff_ne_zero`：degree_eq_of_le_of_coeff_ne
_zero (pn : p.degree <= n) (p1 : p.coeff n != 0) : p.degree = n
· 使用定理 `Finset.sup_le`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSup α]
 [inst_1 : OrderBot α] {s : Finset β} {f : β → α} {a : α},   (∀ b ∈ s, f b ≤ a) 
→ s…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `WithBot.coe_le_coe`：coe_le_coe : (a : WithBot α) <= b ↔ a <= b
· 使用定理 `Polynomial.le_natDegree_of_mem_supp`：le_natDegree_of_mem_supp (a : Nat) 
: a in p.support -> a <= natDegree p
· 使用定理 `Polynomial.support_integralNormalization_subset`：support_integralNormali
zation_subset : (integralNormalization p).support subseteq p.support
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.integralNormalization_coeff_natDegree`：integralNormalization_
coeff_natDegree (hp : p != 0) : (integralNormalization p).coeff (natDegree p) = 
1
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma degree_integralNormalization : p.integralNormalization.degree = p.degree := by
  nontriviality R
  by_cases hp : p = 0; · simp [hp]
  rw [degree_eq_natDegree hp]
  refine degree_eq_of_le_of_coeff_ne_zero ?_ (by simp [integralNormalization_coeff_natDegree, *])
  exact (Finset.sup_le fun i h =>
      WithBot.coe_le_coe.2 <| le_natDegree_of_mem_supp i <| support_integralNormalization_subset h)

@[simp]
/-
**Polynomial.natDegree_integralNormalization** 是 Mathlib 中的一个引理，位于命名空间 `Polynomi
al`。
形式化陈述：natDegree_integralNormalization : p.integralNormalization.natDegree = p.na
tDegree
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.natDegree_of_subsingleton`：natDegree_of_subsingleton [Subsing
leton R] : natDegree p = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.integralNormalization_zero`：integralNormalization_zero : inte
gralNormalization (0 : R[X]) = 0
· 使用定理 `Polynomial.natDegree_eq_of_degree_eq`：natDegree_eq_of_degree_eq [Semirin
g S] {q : S[X]} (h : degree p = degree q) : natDegree p = natDegree q
· 使用引理 `Polynomial.degree_integralNormalization`：degree_integralNormalization : 
p.integralNormalization.degree = p.degree
-/
lemma natDegree_integralNormalization : p.integralNormalization.natDegree = p.natDegree := by
  nontriviality R
  by_cases hp : p = 0; · simp [hp]
  exact natDegree_eq_of_degree_eq p.degree_integralNormalization
/-
**Polynomial.monic_integralNormalization** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：monic_integralNormalization (hp : p != 0) : Monic (integralNormalization p
)
参数：hp : p != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.monic_of_degree_le`：monic_of_degree_le (n : Nat) (pn : p.degr
ee <= n) (p1 : p.coeff n = 1) : Monic p
· 使用定理 `Finset.sup_le`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSup α]
 [inst_1 : OrderBot α] {s : Finset β} {f : β → α} {a : α},   (∀ b ∈ s, f b ≤ a) 
→ s…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `WithBot.coe_le_coe`：coe_le_coe : (a : WithBot α) <= b ↔ a <= b
· 使用定理 `Polynomial.le_natDegree_of_mem_supp`：le_natDegree_of_mem_supp (a : Nat) 
: a in p.support -> a <= natDegree p
· 使用定理 `Polynomial.support_integralNormalization_subset`：support_integralNormali
zation_subset : (integralNormalization p).support subseteq p.support
· 使用定理 `Polynomial.integralNormalization_coeff_natDegree`：integralNormalization_
coeff_natDegree (hp : p != 0) : (integralNormalization p).coeff (natDegree p) = 
1
-/
theorem monic_integralNormalization (hp : p ≠ 0) : Monic (integralNormalization p) :=
  monic_of_degree_le p.natDegree
    (Finset.sup_le fun i h =>
      WithBot.coe_le_coe.2 <| le_natDegree_of_mem_supp i <| support_integralNormalization_subset h)
    (integralNormalization_coeff_natDegree hp)
/-
**Polynomial.integralNormalization_coeff_mul_leadingCoeff_pow** 是 Mathlib 中的一个定理
，位于命名空间 `Polynomial`。
形式化陈述：integralNormalization_coeff_mul_leadingCoeff_pow (i : Nat) (hp : 1 <= natD
egree p) : (integralNormalization p).coeff i * p.leadingCoeff ^ i = p.coeff i * 
p.leadingCoeff ^ (p.natDegree - 1)
参数：i : Nat；hp : 1 <= natDegree p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.integralNormalization_coeff`：integralNormalization_coeff {i :
 Nat} : (integralNormalization p).coeff i = if p.degree = i then 1 else coeff p 
i * p.leadingCoeff ^ (p.natD…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.natDegree_eq_of_degree_eq_some`：natDegree_eq_of_degree_eq_som
e {p : R[X]} {n : Nat} (h : degree p = n) : natDegree p = n
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `tsub_add_cancel_of_le`：tsub_add_cancel_of_le (h : a <= b) : b - a + a = 
b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `le_tsub_iff_right`：le_tsub_iff_right (h : a <= c) : b <= c - a ↔ b + a <
= c
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `Nat.succ_le_iff`：∀ {m n : ℕ}, m.succ ≤ n ↔ m < n
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.coe_lt_degree`：coe_lt_degree {p : R[X]} {n : Nat} : (n : With
Bot Nat) < degree p ↔ n < natDegree p
· 使用定理 `Polynomial.coeff_eq_zero_of_degree_lt`：coeff_eq_zero_of_degree_lt (h : d
egree p < n) : coeff p n = 0
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
-/
theorem integralNormalization_coeff_mul_leadingCoeff_pow (i : ℕ) (hp : 1 ≤ natDegree p) :
    (integralNormalization p).coeff i * p.leadingCoeff ^ i =
      p.coeff i * p.leadingCoeff ^ (p.natDegree - 1) := by
  rw [integralNormalization_coeff]
  split_ifs with h
  · simp [natDegree_eq_of_degree_eq_some h, leadingCoeff,
      ← pow_succ', tsub_add_cancel_of_le (natDegree_eq_of_degree_eq_some h ▸ hp)]
  · simp only [mul_assoc, ← pow_add]
    by_cases h' : i < p.degree
    · rw [tsub_add_cancel_of_le]
      rw [le_tsub_iff_right hp, Nat.succ_le_iff]
      exact coe_lt_degree.mp h'
    · simp [coeff_eq_zero_of_degree_lt (lt_of_le_of_ne (le_of_not_gt h') h)]
/-
**Polynomial.integralNormalization_mul_C_leadingCoeff** 是 Mathlib 中的一个定理，位于命名空间 
`Polynomial`。
形式化陈述：integralNormalization_mul_C_leadingCoeff (p : R[X]) : integralNormalizatio
n p * C p.leadingCoeff = scaleRoots p p.leadingCoeff
参数：p : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.ext`：ext {p q : R[X]} : (forall n, coeff p n = coeff q n) -> 
p = q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coeff_mul_C`：coeff_mul_C (p : R[X]) (n : Nat) (a : R) : coeff
 (p * C a) n = coeff p n * a
· 使用定理 `Polynomial.integralNormalization_coeff`：integralNormalization_coeff {i :
 Nat} : (integralNormalization p).coeff i = if p.degree = i then 1 else coeff p 
i * p.leadingCoeff ^ (p.natD…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.natDegree_eq_of_degree_eq_some`：natDegree_eq_of_degree_eq_som
e {p : R[X]} {n : Nat} (h : degree p = n) : natDegree p = n
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Polynomial.coeff_scaleRoots`：coeff_scaleRoots (p : R[X]) (s : R) (i : Na
t) : (scaleRoots p s).coeff i = coeff p i * s ^ (p.natDegree - i)
· 使用定理 `tsub_self`：tsub_self (a : α) : a - a = 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `tsub_right_comm`：tsub_right_comm : a - b - c = a - c - b
· 使用定理 `tsub_add_cancel_of_le`：tsub_add_cancel_of_le (h : a <= b) : b - a + a = 
b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `le_tsub_iff_left`：le_tsub_iff_left (h : a <= c) : b <= c - a ↔ a + b <= 
c
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.coe_lt_degree`：coe_lt_degree {p : R[X]} {n : Nat} : (n : With
Bot Nat) < degree p ↔ n < natDegree p
（共 35 条，此处仅展示前 30 条）
-/
theorem integralNormalization_mul_C_leadingCoeff (p : R[X]) :
    integralNormalization p * C p.leadingCoeff = scaleRoots p p.leadingCoeff := by
  ext i
  rw [coeff_mul_C, integralNormalization_coeff]
  split_ifs with h
  · simp [natDegree_eq_of_degree_eq_some h, leadingCoeff]
  · simp only [coeff_scaleRoots]
    by_cases h' : i < p.degree
    · rw [mul_assoc, ← pow_succ, tsub_right_comm, tsub_add_cancel_of_le]
      rw [le_tsub_iff_left (coe_lt_degree.mp h').le, Nat.succ_le_iff]
      exact coe_lt_degree.mp h'
    · simp [coeff_eq_zero_of_degree_lt (lt_of_le_of_ne (le_of_not_gt h') h)]

variable {A : Type*} [CommSemiring S] [Semiring A]
/-
**Polynomial.leadingCoeff_smul_integralNormalization** 是 Mathlib 中的一个定理，位于命名空间 `
Polynomial`。
形式化陈述：leadingCoeff_smul_integralNormalization (p : S[X]) : p.leadingCoeff • inte
gralNormalization p = scaleRoots p p.leadingCoeff
参数：p : S[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `Polynomial.algebraMap_eq`：algebraMap_eq : algebraMap R R[X] = C
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Polynomial.integralNormalization_mul_C_leadingCoeff`：integralNormalizati
on_mul_C_leadingCoeff (p : R[X]) : integralNormalization p * C p.leadingCoeff = 
scaleRoots p p.leadingCoeff
-/
theorem leadingCoeff_smul_integralNormalization (p : S[X]) :
    p.leadingCoeff • integralNormalization p = scaleRoots p p.leadingCoeff := by
  rw [Algebra.smul_def, algebraMap_eq, mul_comm, integralNormalization_mul_C_leadingCoeff]
/-
**Polynomial.integralNormalization_eval** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem integralNormalization_eval₂_leadingCoeff_mul_of_commute (h : 1 ≤ p.natDegree) (f : R →+* A)
    (x : A) (h₁ : Commute (f p.leadingCoeff) x) (h₂ : ∀ {r r'}, Commute (f r) (f r')) :
    (integralNormalization p).eval₂ f (f p.leadingCoeff * x) =
      f p.leadingCoeff ^ (p.natDegree - 1) * p.eval₂ f x := by
  rw [eval₂_eq_sum_range, eval₂_eq_sum_range, Finset.mul_sum]
  apply Finset.sum_congr
  · rw [natDegree_eq_of_degree_eq p.degree_integralNormalization]
  intro n _hn
  rw [h₁.mul_pow, ← mul_assoc, ← f.map_pow, ← f.map_mul,
    integralNormalization_coeff_mul_leadingCoeff_pow _ h, f.map_mul, h₂.eq, f.map_pow, mul_assoc]
/-
**Polynomial.integralNormalization_eval** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem integralNormalization_eval₂_leadingCoeff_mul (h : 1 ≤ p.natDegree) (f : R →+* S) (x : S) :
    (integralNormalization p).eval₂ f (f p.leadingCoeff * x) =
      f p.leadingCoeff ^ (p.natDegree - 1) * p.eval₂ f x :=
  integralNormalization_eval₂_leadingCoeff_mul_of_commute h _ _ (.all _ _) (.all _ _)
/-
**Polynomial.integralNormalization_eval** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem integralNormalization_eval₂_eq_zero_of_commute {p : R[X]} (f : R →+* A) {z : A}
    (hz : eval₂ f z p = 0) (h₁ : Commute (f p.leadingCoeff) z) (h₂ : ∀ {r r'}, Commute (f r) (f r'))
    (inj : ∀ x : R, f x = 0 → x = 0) :
    eval₂ f (f p.leadingCoeff * z) (integralNormalization p) = 0 := by
  obtain (h | h) := p.natDegree.eq_zero_or_pos
  · by_cases h0 : coeff p 0 = 0
    · rw [eq_C_of_natDegree_eq_zero h]
      simp [h0]
    · rw [eq_C_of_natDegree_eq_zero h, eval₂_C] at hz
      exact absurd (inj _ hz) h0
  · rw [integralNormalization_eval₂_leadingCoeff_mul_of_commute h _ _ h₁ h₂, hz, mul_zero]
/-
**Polynomial.integralNormalization_eval** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem integralNormalization_eval₂_eq_zero {p : R[X]} (f : R →+* S) {z : S} (hz : eval₂ f z p = 0)
    (inj : ∀ x : R, f x = 0 → x = 0) :
    eval₂ f (f p.leadingCoeff * z) (integralNormalization p) = 0 :=
  integralNormalization_eval₂_eq_zero_of_commute _ hz (.all _ _) (.all _ _) inj
/-
**Polynomial.integralNormalization_aeval_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Poly
nomial`。
形式化陈述：integralNormalization_aeval_eq_zero [Algebra S A] {f : S[X]} {z : A} (hz :
 aeval z f = 0) (inj : forall x : S, algebraMap S A x = 0 -> x = 0) : aeval (alg
ebraMap S A f.leadingCoeff * z) (integralNormalization f) = 0
参数：hz : aeval z f = 0；inj : forall x : S, algebraMap S A x = 0 -> x = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.integralNormalization_eval₂_eq_zero_of_commute`：integralNorma
lization_eval₂_eq_zero_of_commute {p : R[X]} (f : R ->+* A) {z : A} (hz : eval₂ 
f z p = 0) (h₁ : Commute (f p.leadingCoeff) z) …
· 使用引理 `Algebra.commute_algebraMap_left`：commute_algebraMap_left (r : R) (x : A)
 : Commute (algebraMap R A r) x
· 使用定理 `Commute.map`：∀ {F : Type u_1} {M : Type u_2} {N : Type u_3} [inst : Mul 
M] [inst_1 : Mul N] {x y : M} [inst_2 : FunLike F M N]   [MulHomClass F M N], Co
m…
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `Commute.all`：∀ {S : Type u_3} [inst : CommMagma S] (a b : S), Commute a 
b
-/
theorem integralNormalization_aeval_eq_zero [Algebra S A] {f : S[X]} {z : A} (hz : aeval z f = 0)
    (inj : ∀ x : S, algebraMap S A x = 0 → x = 0) :
    aeval (algebraMap S A f.leadingCoeff * z) (integralNormalization f) = 0 :=
  integralNormalization_eval₂_eq_zero_of_commute (algebraMap S A) hz
    (Algebra.commute_algebraMap_left _ _) (.map (.all _ _) _) inj
/-
**Polynomial.integralNormalization_map** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：integralNormalization_map (f : R ->+* A) (p : R[X]) (H : f p.leadingCoeff 
!= 0) : (p.map f).integralNormalization = p.integralNormalization.map f
参数：f : R ->+* A；p : R[X]；H : f p.leadingCoeff != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.ext`：ext {p q : R[X]} : (forall n, coeff p n = coeff q n) -> 
p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.integralNormalization_coeff`：integralNormalization_coeff {i :
 Nat} : (integralNormalization p).coeff i = if p.degree = i then 1 else coeff p 
i * p.leadingCoeff ^ (p.natD…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.degree_map_eq_of_leadingCoeff_ne_zero`：degree_map_eq_of_leadi
ngCoeff_ne_zero (f : R ->+* S) (hf : f (leadingCoeff p) != 0) : degree (p.map f)
 = degree p
· 使用定理 `Polynomial.coeff_map`：coeff_map (n : Nat) : coeff (p.map f) n = f (coeff
 p n)
· 使用定理 `Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero`：leadingCoeff_map_of
_leadingCoeff_ne_zero (f : R ->+* S) (hf : f (leadingCoeff p) != 0) : leadingCoe
ff (p.map f) = f (leadingCoeff p)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.natDegree_map_eq_iff`：natDegree_map_eq_iff {f : R ->+* S} {p 
: Polynomial R} : natDegree (map f p) = natDegree p ↔ f (p.leadingCoeff) != 0 ∨ 
natDegree p = 0
· 使用定理 `apply_ite`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [inst 
: Decidable P] (x y : α),   f (if P then x else y) = if P then f x else f y
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
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma integralNormalization_map (f : R →+* A) (p : R[X]) (H : f p.leadingCoeff ≠ 0) :
    (p.map f).integralNormalization = p.integralNormalization.map f := by
  ext i
  simp [integralNormalization_coeff, degree_map_eq_of_leadingCoeff_ne_zero _ H, apply_ite f,
    leadingCoeff_map_of_leadingCoeff_ne_zero _ H, natDegree_map_eq_iff.mpr (.inl H)]

end Semiring

section IsCancelMulZero

variable [Semiring R] [IsCancelMulZero R]

@[simp]
/-
**Polynomial.support_integralNormalization** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial
`。
形式化陈述：support_integralNormalization {f : R[X]} : (integralNormalization f).suppo
rt = f.support
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subsingleton.eq_zero`：∀ {α : Type u} [inst : Zero α] [Subsingleton α] (a
 : α), a = 0
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.integralNormalization_zero`：integralNormalization_zero : inte
gralNormalization (0 : R[X]) = 0
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `Polynomial.support_integralNormalization_subset`：support_integralNormali
zation_subset : (integralNormalization p).support subseteq p.support
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.integralNormalization_coeff`：integralNormalization_coeff {i :
 Nat} : (integralNormalization p).coeff i = if p.degree = i then 1 else coeff p 
i * p.leadingCoeff ^ (p.natD…
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
-/
theorem support_integralNormalization {f : R[X]} :
    (integralNormalization f).support = f.support := by
  nontriviality R using Subsingleton.eq_zero (α := R[X])
  have : IsDomain R := {}
  by_cases hf : f = 0; · simp [hf]
  ext i
  refine ⟨fun h => support_integralNormalization_subset h, ?_⟩
  simp only [integralNormalization_coeff, mem_support_iff]
  intro hfi
  split_ifs with hi <;> simp [hf, hfi]

end IsCancelMulZero

end IntegralNormalization

end Polynomial

