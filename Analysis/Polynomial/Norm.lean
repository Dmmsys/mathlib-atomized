/-
Copyright (c) 2025 Kevin H. Wilson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin H. Wilson
-/
module

public import Mathlib.RingTheory.Polynomial.GaussNorm
public import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
public import Mathlib.Algebra.Order.Hom.Basic


/-!
# Sup Norm of Polynomials

In this file we define the sup norm on `Polynomial`s based on their coefficients as well as several
basic results about this norm. We note that this is often called the _(naive) height_ of the
polynomial in the literature.

The sup norm is related to the Mahler measure of the polynomial. See
`Mathlib/Analysis/Polynomial/MahlerMeasure.lean`.

## Main definitions

- `Polynomial.supNorm p`: the sup norm of the coefficients of the polynomial, equal to the
  maximum of the norm of its coefficients (or zero for the zero polynomial)

## A Note on Naming

In the literature, the sup norm is often called the _(naive) height_ of a polynomial and the
`l^1` norm is often called the _length_ of the polynomial. Unfortunately, these terms are
extremely overloaded and Mathlib defines _height_ differently.

### TODOs

All other `l^p` norms can be defined on Polynomials as well. In the literature, the `l^1` norm is
sometimes called the polynomial's _length_. The `l^2` norm sometimes arises due to Parseval's
theorem implying that the squared `l^2` norm of a complex polynomial is the integral of the norm of
the polynomial's value on the unit circle.
-/


@[expose] public section supnorm_seminorm

variable {A : Type*} [SeminormedRing A] (p : Polynomial A)

namespace Polynomial

/-- The sup norm of a polynomial on a semi-normed ring, defined as the maximum of its coefficients.
Often called the _(naive) height_ of the polynomial.

This is defined in terms of `Polynomial.gaussNorm`. -/
/-
**Polynomial.supNorm** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：supNorm : Real
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The sup norm of a polynomial on a semi-normed ring, defined as the maximum of it
s coefficients.
Often called the _(naive) height_ of the polynomial.

This is defined in terms of `Polynomial.gaussNorm`.
-/
noncomputable def supNorm : ℝ := p.gaussNorm (SeminormedRing.toRingSeminorm A) 1

/-- The direct definition of the supNorm -/
/-
**Polynomial.supNorm_def'** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：supNorm_def' : p.supNorm = if hp : p.support.Nonempty then p.support.sup' 
hp (norm ∘ p.coeff) else 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `Finset.sup'_congr`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSu
p α] {s : Finset β} (H : s.Nonempty) {t : Finset β} {f g : β → α}   (h₁ : s = t)
, (∀ x …
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The direct definition of the supNorm
-/
lemma supNorm_def' : p.supNorm =
    if hp : p.support.Nonempty then p.support.sup' hp (norm ∘ p.coeff) else 0 := by
  split_ifs with h
  · simp only [supNorm, gaussNorm, h, ↓reduceDIte, one_pow, mul_one, Function.comp_apply]
    congr
  · simp [supNorm, gaussNorm, h]

@[simp]
/-
**Polynomial.supNorm_zero** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：supNorm_zero : (0 : A[X]).supNorm = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Polynomial.gaussNorm_zero`：gaussNorm_zero : gaussNorm v c 0 = 0
-/
lemma supNorm_zero : (0 : A[X]).supNorm = 0 := gaussNorm_zero ..
/-
**Polynomial.supNorm_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：supNorm_nonneg : 0 <= p.supNorm
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.gaussNorm_nonneg`：gaussNorm_nonneg (hc : 0 <= c) : 0 <= p.gau
ssNorm v c
· 使用定理 `RingSeminormClass.toNonnegHomClass`：∀ {F : Type u_2} {α : Type u_3} {β :
 Type u_4} [inst : FunLike F α β] [inst_1 : NonUnitalNonAssocRing α]   [inst_2 :
 Semiring β] [inst_3 : L…
· 使用定理 `Mathlib.Meta.NormNum.isNat_le_true`：∀ {α : Type u_1} [inst : Semiring α]
 [inst_1 : PartialOrder α] [IsOrderedRing α] {a b : α} {a' b' : ℕ},   Mathlib.Me
ta.NormNum.IsNat a a' → …
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
-/
lemma supNorm_nonneg : 0 ≤ p.supNorm := by
  apply gaussNorm_nonneg
  norm_num

@[simp]
/-
**Polynomial.supNorm_C** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：supNorm_C {a : A} : (C a).supNorm = ‖a‖
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Polynomial.gaussNorm_C`：gaussNorm_C (r : R) : (C r).gaussNorm v c = v r
· 使用定理 `AddGroupSeminormClass.toZeroHomClass`：∀ {F : Type u_2} {α : Type u_3} {β
 : Type u_4} [inst : FunLike F α β] [inst_1 : AddGroup α] [inst_2 : AddCommMonoi
d β]   [inst_3 : PartialOr…
· 使用定理 `RingSeminormClass.toAddGroupSeminormClass`：∀ {F : Type u_7} {α : outPara
m (Type u_8)} {β : outParam (Type u_9)} {inst : NonUnitalNonAssocRing α}   {inst
_1 : Semiring β} {inst_2 : Part…
-/
lemma supNorm_C {a : A} : (C a).supNorm = ‖a‖ := gaussNorm_C ..

@[simp]
/-
**Polynomial.supNorm_monomial** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：supNorm_monomial (n : Nat) {a : A} : (monomial n a).supNorm = ‖a‖
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.monomial_zero_right`：monomial_zero_right (n : Nat) : monomial
 n (0 : R) = 0
· 使用引理 `Polynomial.supNorm_zero`：supNorm_zero : (0 : A[X]).supNorm = 0
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `Polynomial.support_monomial`：support_monomial (n) {a : R} (h : a != 0) :
 (monomial n a).support = singleton n
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `Finset.sup'.congr_simp`：∀ {α : Type u_2} {β : Type u_3} [inst : Semilatt
iceSup α] (s s_1 : Finset β) (e_s : s = s_1) (H : s.Nonempty)   (f f_1 : β → α),
 f = f_1 → s…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Polynomial.coeff_monomial_same`：coeff_monomial_same (n : Nat) (c : R) : 
(monomial n c).coeff n = c
-/
lemma supNorm_monomial (n : ℕ) {a : A} : (monomial n a).supNorm = ‖a‖ := by
  by_cases ha : a = 0
  · simp [ha]
  · simp [supNorm, gaussNorm, support_monomial n ha]

@[simp]
/-
**Polynomial.supNorm_X** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：supNorm_X [NormOneClass A] : (X : A[X]).supNorm = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.monomial_one_one_eq_X`：monomial_one_one_eq_X : monomial 1 (1 
: R) = X
· 使用引理 `Polynomial.supNorm_monomial`：supNorm_monomial (n : Nat) {a : A} : (monom
ial n a).supNorm = ‖a‖
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1
-/
lemma supNorm_X [NormOneClass A] : (X : A[X]).supNorm = 1 := by
  rw [← monomial_one_one_eq_X, supNorm_monomial, norm_one]
/-
**Polynomial.le_supNorm** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：le_supNorm (i : Nat) : ‖p.coeff i‖ <= p.supNorm
参数：i : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用引理 `Polynomial.le_gaussNorm`：le_gaussNorm (hc : 0 <= c) (i : Nat) : v (p.coe
ff i) * c ^ i <= p.gaussNorm v c
· 使用定理 `AddGroupSeminormClass.toZeroHomClass`：∀ {F : Type u_2} {α : Type u_3} {β
 : Type u_4} [inst : FunLike F α β] [inst_1 : AddGroup α] [inst_2 : AddCommMonoi
d β]   [inst_3 : PartialOr…
· 使用定理 `RingSeminormClass.toAddGroupSeminormClass`：∀ {F : Type u_7} {α : outPara
m (Type u_8)} {β : outParam (Type u_9)} {inst : NonUnitalNonAssocRing α}   {inst
_1 : Semiring β} {inst_2 : Part…
· 使用定理 `RingSeminormClass.toNonnegHomClass`：∀ {F : Type u_2} {α : Type u_3} {β :
 Type u_4} [inst : FunLike F α β] [inst_1 : NonUnitalNonAssocRing α]   [inst_2 :
 Semiring β] [inst_3 : L…
· 使用定理 `Mathlib.Meta.NormNum.isNat_le_true`：∀ {α : Type u_1} [inst : Semiring α]
 [inst_1 : PartialOrder α] [IsOrderedRing α] {a b : α} {a' b' : ℕ},   Mathlib.Me
ta.NormNum.IsNat a a' → …
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
-/
lemma le_supNorm (i : ℕ) : ‖p.coeff i‖ ≤ p.supNorm := by
  simpa using! le_gaussNorm (SeminormedRing.toRingSeminorm A) p (by norm_num : (0 : ℝ) ≤ 1) i
/-
**Polynomial.exists_eq_supNorm** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：exists_eq_supNorm : exists i : Nat, p.supNorm = ‖p.coeff i‖
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Polynomial.exists_eq_gaussNorm`：exists_eq_gaussNorm : exists i, p.gaussN
orm v c = v (p.coeff i) * c ^ i
· 使用定理 `AddGroupSeminormClass.toZeroHomClass`：∀ {F : Type u_2} {α : Type u_3} {β
 : Type u_4} [inst : FunLike F α β] [inst_1 : AddGroup α] [inst_2 : AddCommMonoi
d β]   [inst_3 : PartialOr…
· 使用定理 `RingSeminormClass.toAddGroupSeminormClass`：∀ {F : Type u_7} {α : outPara
m (Type u_8)} {β : outParam (Type u_9)} {inst : NonUnitalNonAssocRing α}   {inst
_1 : Semiring β} {inst_2 : Part…
-/
lemma exists_eq_supNorm : ∃ i : ℕ, p.supNorm = ‖p.coeff i‖ := by
  simpa using! p.exists_eq_gaussNorm (SeminormedRing.toRingSeminorm A) 1
/-
**Polynomial.isGreatest_supNorm** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：isGreatest_supNorm : IsGreatest (Set.range (‖p.coeff ·‖)) p.supNorm
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Polynomial.exists_eq_supNorm`：exists_eq_supNorm : exists i : Nat, p.supN
orm = ‖p.coeff i‖
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `Polynomial.le_supNorm`：le_supNorm (i : Nat) : ‖p.coeff i‖ <= p.supNorm
-/
lemma isGreatest_supNorm : IsGreatest (Set.range (‖p.coeff ·‖)) p.supNorm :=
  ⟨by simpa [eq_comm] using exists_eq_supNorm p, by simpa [mem_upperBounds] using le_supNorm p⟩

/-- The supNorm can also be defined with an iSup. Note that this uses the fact that `norm` is both
a `ZeroHom` and `NonnegHom` so is not _a priori_ true from the `gaussNorm` definition. -/
/-
**Polynomial.supNorm_eq_iSup** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：supNorm_eq_iSup : p.supNorm = ⨆ i, ‖p.coeff i‖
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsGreatest.csSup_eq`：IsGreatest.csSup_eq (H : IsGreatest s a) : sSup s =
 a
· 使用引理 `Polynomial.isGreatest_supNorm`：isGreatest_supNorm : IsGreatest (Set.rang
e (‖p.coeff ·‖)) p.supNorm

--- 原说明 ---
The supNorm can also be defined with an iSup. Note that this uses the fact that 
`norm` is both
a `ZeroHom` and `NonnegHom` so is not _a priori_ true from the `gaussNorm` defin
ition.
-/
lemma supNorm_eq_iSup : p.supNorm = ⨆ i, ‖p.coeff i‖ := p.isGreatest_supNorm.csSup_eq.symm

end Polynomial
end supnorm_seminorm

@[expose] public section supnorm_norm

namespace Polynomial

variable {A : Type*} [NormedRing A] (p : Polynomial A)

/-
**Polynomial.supNorm_eq_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：supNorm_eq_zero_iff : p.supNorm = 0 ↔ p = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.gaussNorm_eq_zero_iff`：gaussNorm_eq_zero_iff (h_eq_zero : for
all x : R, v x = 0 -> x = 0) (hc : 0 < c) : p.gaussNorm v c = 0 ↔ p = 0
· 使用定理 `AddGroupSeminormClass.toZeroHomClass`：∀ {F : Type u_2} {α : Type u_3} {β
 : Type u_4} [inst : FunLike F α β] [inst_1 : AddGroup α] [inst_2 : AddCommMonoi
d β]   [inst_3 : PartialOr…
· 使用定理 `RingSeminormClass.toAddGroupSeminormClass`：∀ {F : Type u_7} {α : outPara
m (Type u_8)} {β : outParam (Type u_9)} {inst : NonUnitalNonAssocRing α}   {inst
_1 : Semiring β} {inst_2 : Part…
· 使用定理 `RingSeminormClass.toNonnegHomClass`：∀ {F : Type u_2} {α : Type u_3} {β :
 Type u_4} [inst : FunLike F α β] [inst_1 : NonUnitalNonAssocRing α]   [inst_2 :
 Semiring β] [inst_3 : L…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
-/
lemma supNorm_eq_zero_iff : p.supNorm = 0 ↔ p = 0 := gaussNorm_eq_zero_iff _ _ (by simp) (by simp)

end Polynomial

end supnorm_norm

