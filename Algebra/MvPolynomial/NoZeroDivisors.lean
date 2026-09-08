/-
Copyright (c) 2025 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, Bolton Bailey
-/
module

public import Mathlib.Algebra.MvPolynomial.Variables
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.RingTheory.MvPolynomial.MonomialOrder.DegLex
public import Mathlib.Algebra.MvPolynomial.Division

/-!
# Multivariate polynomials over integral domains

This file proves results about multivariate polynomials
that hold when the coefficient (semi)ring has no zero divisors.

-/

public section

open Finset Equiv

variable {R : Type*}

namespace MvPolynomial

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

section CommSemiring

variable [CommSemiring R]

variable {p q : MvPolynomial σ R}

section NoZeroDivisors

variable [NoZeroDivisors R]

section DegreeOf

/-
**MvPolynomial.degreeOf_mul_eq** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：degreeOf_mul_eq (hp : p != 0) (hq : q != 0) : degreeOf n (p * q) = degreeO
f n p + degreeOf n q
参数：hp : p != 0；hq : q != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MvPolynomial.degreeOf_eq_natDegree`：degreeOf_eq_natDegree [DecidableEq σ
] (a : σ) (p : MvPolynomial σ R) : degreeOf a p = (optionEquivLeft R {b // b != 
a} (rename (Equiv.option…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用引理 `Polynomial.natDegree_mul`：natDegree_mul (hp : p != 0) (hq : q != 0) : (p
 * q).natDegree = p.natDegree + q.natDegree
· 使用定理 `MvPolynomial.instNoZeroDivisors`：∀ {R : Type u} {σ : Type u_1} [inst : C
ommSemiring R] [NoZeroDivisors R], NoZeroDivisors (MvPolynomial σ R)
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
-/
lemma degreeOf_mul_eq (hp : p ≠ 0) (hq : q ≠ 0) :
    degreeOf n (p * q) = degreeOf n p + degreeOf n q := by
  classical
  simp_rw [degreeOf_eq_natDegree, map_mul, ← renameEquiv_apply]
  rw [Polynomial.natDegree_mul] <;> simpa [-renameEquiv_apply, EmbeddingLike.map_eq_zero_iff]
/-
**MvPolynomial.degreeOf_prod_eq** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：degreeOf_prod_eq {ι : Type*} (s : Finset ι) (f : ι -> MvPolynomial σ R) (h
 : forall i in s, f i != 0) : degreeOf n (∏ i in s, f i) = ∑ i in s, degreeOf n 
(f i)
参数：s : Finset ι；f : ι -> MvPolynomial σ R；h : forall i in s, f i != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Subsingleton.eq_zero`：∀ {α : Type u} [inst : Zero α] [Subsingleton α] (a
 : α), a = 0
· 使用定理 `MvPolynomial.degreeOf_zero`：degreeOf_zero (n : σ) : degreeOf n (0 : MvPo
lynomial σ R) = 0
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MvPolynomial.degreeOf_one`：degreeOf_one (n : σ) : degreeOf n (1 : MvPoly
nomial σ R) = 0
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Finset.prod_insert`：prod_insert [DecidableEq ι] : a ∉ s -> ∏ x in insert
 a s, f x = f a * ∏ x in s, f x
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `MvPolynomial.degreeOf_mul_eq`：degreeOf_mul_eq (hp : p != 0) (hq : q != 0
) : degreeOf n (p * q) = degreeOf n p + degreeOf n q
· 使用引理 `Finset.prod_ne_zero_iff`：prod_ne_zero_iff : ∏ x in s, f x != 0 ↔ forall 
a in s, f a != 0
· 使用定理 `MvPolynomial.instNoZeroDivisors`：∀ {R : Type u} {σ : Type u_1} [inst : C
ommSemiring R] [NoZeroDivisors R], NoZeroDivisors (MvPolynomial σ R)
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
-/
lemma degreeOf_prod_eq {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ R)
    (h : ∀ i ∈ s, f i ≠ 0) :
    degreeOf n (∏ i ∈ s, f i) = ∑ i ∈ s, degreeOf n (f i) := by
  rcases subsingleton_or_nontrivial (MvPolynomial σ R) with nontrivial | nontrivial
  · simp [Subsingleton.eq_zero (α := MvPolynomial σ R)]
  · classical
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s a_not_mem ih =>
      simp only [mem_insert, ne_eq, forall_eq_or_imp] at h
      obtain ⟨ha, hs⟩ := h
      simp [a_not_mem, not_false_eq_true, prod_insert, sum_insert, degreeOf_mul_eq ha
        (by rw [prod_ne_zero_iff]; exact hs), ih hs]
/-
**MvPolynomial.degreeOf_pow_eq** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：degreeOf_pow_eq (i : σ) (p : MvPolynomial σ R) (n : Nat) (hp : p != 0) : d
egreeOf i (p ^ n) = n * degreeOf i p
参数：i : σ；p : MvPolynomial σ R；n : Nat；hp : p != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.pow_eq_prod_const`：pow_eq_prod_const (b : M) : forall n, b ^ n = 
∏ _k in range n, b
· 使用引理 `MvPolynomial.degreeOf_prod_eq`：degreeOf_prod_eq {ι : Type*} (s : Finset 
ι) (f : ι -> MvPolynomial σ R) (h : forall i in s, f i != 0) : degreeOf n (∏ i i
n s, f i) = ∑ i in …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `Finset.card_range`：card_range (n : Nat) : #(range n) = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem degreeOf_pow_eq (i : σ) (p : MvPolynomial σ R) (n : ℕ) (hp : p ≠ 0) :
    degreeOf i (p ^ n) = n * degreeOf i p := by
  rw [pow_eq_prod_const, degreeOf_prod_eq (range n) (fun _ ↦ p) (fun _ _ ↦ hp)]
  simp

end DegreeOf

section Degrees

/-
**MvPolynomial.degrees_mul_eq** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：degrees_mul_eq (hp : p != 0) (hq : q != 0) : degrees (p * q) = degrees p +
 degrees q
参数：hp : p != 0；hq : q != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.ext'`：ext' {s t : Multiset α} : (forall a, count a s = count a 
t) -> s = t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.count_add`：count_add (a : α) : forall s t, count a (s + t) = co
unt a s + count a t
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `MvPolynomial.degreeOf_mul_eq`：degreeOf_mul_eq (hp : p != 0) (hq : q != 0
) : degreeOf n (p * q) = degreeOf n p + degreeOf n q
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma degrees_mul_eq (hp : p ≠ 0) (hq : q ≠ 0) :
    degrees (p * q) = degrees p + degrees q := by
  classical
  ext s
  simp_rw [Multiset.count_add, ← degreeOf_def, degreeOf_mul_eq hp hq]

end Degrees

/-
**MvPolynomial.totalDegree_mul_of_isDomain** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomi
al`。
形式化陈述：totalDegree_mul_of_isDomain {f g : MvPolynomial σ R} (hf : f != 0) (hg : g
 != 0) : totalDegree (f * g) = totalDegree f + totalDegree g
参数：hf : f != 0；hg : g != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `exists_wellFoundedGT`：exists_wellFoundedGT : exists (_ : LinearOrder α),
 WellFoundedGT α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonomialOrder.degree_mul`：degree_mul [NoZeroDivisors R] {f g : MvPolynom
ial σ R} (hf : f != 0) (hg : g != 0) : m.degree (f * g) = m.degree f + m.degree 
g
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem totalDegree_mul_of_isDomain {f g : MvPolynomial σ R}
    (hf : f ≠ 0) (hg : g ≠ 0) :
    totalDegree (f * g) = totalDegree f + totalDegree g := by
  cases exists_wellFoundedGT σ
  simp [← degree_degLexDegree, MonomialOrder.degree_mul hf hg]
/-
**MvPolynomial.totalDegree_le_of_dvd_of_isDomain** 是 Mathlib 中的一个定理，位于命名空间 `MvPo
lynomial`。
形式化陈述：totalDegree_le_of_dvd_of_isDomain {f g : MvPolynomial σ R} (h : f ∣ g) (hg
 : g != 0) : f.totalDegree <= g.totalDegree
参数：h : f ∣ g；hg : g != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.totalDegree_mul_of_isDomain`：totalDegree_mul_of_isDomain {f
 g : MvPolynomial σ R} (hf : f != 0) (hg : g != 0) : totalDegree (f * g) = total
Degree f + totalDegree g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `MvPolynomial.instNoZeroDivisors`：∀ {R : Type u} {σ : Type u_1} [inst : C
ommSemiring R] [NoZeroDivisors R], NoZeroDivisors (MvPolynomial σ R)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem totalDegree_le_of_dvd_of_isDomain {f g : MvPolynomial σ R}
    (h : f ∣ g) (hg : g ≠ 0) :
    f.totalDegree ≤ g.totalDegree := by
  obtain ⟨r, rfl⟩ := h
  rw [totalDegree_mul_of_isDomain (by aesop) (by aesop)]
  lia
/-
**MvPolynomial.dvd_C_iff_exists** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：dvd_C_iff_exists {f : MvPolynomial σ R} {a : R} (ha : a != 0) : f ∣ C a ↔ 
exists b, b ∣ a ∧ f = C b
参数：ha : a != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.eq_zero_of_le_zero`：∀ {n : ℕ}, n ≤ 0 → n = 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.totalDegree_C`：totalDegree_C (a : R) : (C a : MvPolynomial 
σ R).totalDegree = 0
· 使用定理 `MvPolynomial.totalDegree_le_of_dvd_of_isDomain`：totalDegree_le_of_dvd_of
_isDomain {f g : MvPolynomial σ R} (h : f ∣ g) (hg : g != 0) : f.totalDegree <= 
g.totalDegree
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `MvPolynomial.coeff_zero_C`：coeff_zero_C (a) : coeff 0 (C a : MvPolynomia
l σ R) = a
· 使用定理 `MvPolynomial.C_dvd_iff_dvd_coeff`：C_dvd_iff_dvd_coeff (r : R) (φ : MvPol
ynomial σ R) : C r ∣ φ ↔ forall i, r ∣ φ.coeff i
· 使用定理 `MvPolynomial.totalDegree_eq_zero_iff_eq_C`：totalDegree_eq_zero_iff_eq_C 
{p : MvPolynomial σ R} : p.totalDegree = 0 ↔ p = C (p.coeff 0)
· 使用定理 `map_dvd`：∀ {M : Type u_1} {N : Type u_2} [inst : Semigroup M] [inst_1 : 
Semigroup N] {F : Type u_3} [inst_2 : FunLike F M N]   [MulHomClass F M N] (f…
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem dvd_C_iff_exists {f : MvPolynomial σ R} {a : R} (ha : a ≠ 0) :
    f ∣ C a ↔ ∃ b, b ∣ a ∧ f = C b := by
  constructor
  · intro hf
    use coeff 0 f
    suffices f.totalDegree = 0 by
      rw [totalDegree_eq_zero_iff_eq_C] at this
      refine ⟨?_, this⟩
      rw [this, C_dvd_iff_dvd_coeff] at hf
      simpa using hf 0
    apply Nat.eq_zero_of_le_zero
    simpa using totalDegree_le_of_dvd_of_isDomain hf (by simp [ha])
  · rintro ⟨b, hab, rfl⟩
    exact map_dvd C hab

end NoZeroDivisors

section nonZeroDivisors

open nonZeroDivisors

/-
**MvPolynomial.degreeOf_C_mul** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：degreeOf_C_mul (j : σ) (c : R) (hc : c in R⁰) : degreeOf j (C c * p) = deg
reeOf j p
参数：j : σ；c : R；hc : c in R⁰。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `MvPolynomial.degreeOf_zero`：degreeOf_zero (n : σ) : degreeOf n (0 : MvPo
lynomial σ R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用引理 `MvPolynomial.degreeOf_eq_natDegree`：degreeOf_eq_natDegree [DecidableEq σ
] (a : σ) (p : MvPolynomial σ R) : degreeOf a p = (optionEquivLeft R {b // b != 
a} (rename (Equiv.option…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用定理 `Polynomial.natDegree_mul'`：natDegree_mul' (h : leadingCoeff p * leadingC
oeff q != 0) : natDegree (p * q) = natDegree p + natDegree q
· 使用定理 `MvPolynomial.rename_injective`：rename_injective (f : σ -> τ) (hf : Funct
ion.Injective f) : Function.Injective (rename f : MvPolynomial σ R -> MvPolynomi
al τ R)
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `MvPolynomial.renameEquiv_apply`：∀ {σ : Type u_1} {τ : Type u_2} (R : Typ
e u_4) [inst : CommSemiring R] (f : σ ≃ τ) (a : MvPolynomial σ R),   (MvPolynomi
al.renameEquiv R f) …
· 使用定理 `MvPolynomial.algHom_C`：algHom_C {A : Type*} [Semiring A] [Algebra R A] (
f : MvPolynomial σ R ->ₐ[R] A) (r : R) : f (C r) = algebraMap R A r
· 使用引理 `MvPolynomial.optionEquivLeft_C`：optionEquivLeft_C (r : R) : optionEquivL
eft R S₁ (C r) = Polynomial.C (C r)
· 使用定理 `Polynomial.leadingCoeff_C`：leadingCoeff_C (a : R) : leadingCoeff (C a) =
 a
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `MvPolynomial.ext`：ext (p q : MvPolynomial σ R) : (forall m, coeff m p = 
coeff m q) -> p = q
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `MvPolynomial.coeff_C_mul`：coeff_C_mul (m) (a : R) (p : MvPolynomial σ R)
 : coeff m (C a * p) = a * coeff m p
（共 34 条，此处仅展示前 30 条）
-/
theorem degreeOf_C_mul (j : σ) (c : R) (hc : c ∈ R⁰) : degreeOf j (C c * p) = degreeOf j p := by
  by_cases hp : p = 0
  · simp [hp]
  classical
  simp_rw [degreeOf_eq_natDegree, map_mul, ← renameEquiv_apply]
  rw [Polynomial.natDegree_mul']
  · simp
  · have hp' : (optionEquivLeft R _ ((rename (optionSubtypeNe j).symm) p)).leadingCoeff ≠ 0 := by
      intro h
      exact hp (rename_injective _ (Equiv.injective _) (by simpa using h))
    simp_rw [ne_eq, renameEquiv_apply, algHom_C, algebraMap_eq, optionEquivLeft_C,
      Polynomial.leadingCoeff_C]
    contrapose hp'
    ext m
    apply hc.1
    simpa using congr_arg (coeff m) hp'

end nonZeroDivisors

end CommSemiring

section CommRing

variable [CommRing R] [NoZeroDivisors R] {p q r : MvPolynomial σ R}

/-
**MvPolynomial.dvd_monomial_iff_exists** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：dvd_monomial_iff_exists {n : σ ->₀ Nat} {a : R} (ha : a != 0) : p ∣ monomi
al n a ↔ exists m b, m <= n ∧ b ∣ a ∧ p = monomial m b
参数：ha : a != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `MvPolynomial.C_mul_monomial`：C_mul_monomial : C a * monomial s a' = mono
mial s (a * a')
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MvPolynomial.dvd_monomial_mul_iff_exists`：dvd_monomial_mul_iff_exists [I
sCancelMulZero R] {n : σ ->₀ Nat} : p ∣ monomial n 1 * q ↔ exists m r, m <= n ∧ 
r ∣ q ∧ p = monomial m 1 * r
· 使用定理 `NoZeroDivisors.to_isCancelMulZero`：∀ (R : Type u_3) [inst : NonUnitalNon
AssocRing R] [NoZeroDivisors R], IsCancelMulZero R
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `MvPolynomial.dvd_C_iff_exists`：dvd_C_iff_exists {f : MvPolynomial σ R} {
a : R} (ha : a != 0) : f ∣ C a ↔ exists b, b ∣ a ∧ f = C b
· 使用定理 `map_dvd`：∀ {M : Type u_1} {N : Type u_2} [inst : Semigroup M] [inst_1 : 
Semigroup N] {F : Type u_3} [inst_2 : FunLike F M N]   [MulHomClass F M N] (f…
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
-/
theorem dvd_monomial_iff_exists {n : σ →₀ ℕ} {a : R} (ha : a ≠ 0) :
    p ∣ monomial n a ↔ ∃ m b, m ≤ n ∧ b ∣ a ∧ p = monomial m b := by
  rw [show monomial n a = monomial n 1 * C a by rw [mul_comm, C_mul_monomial, mul_one],
    dvd_monomial_mul_iff_exists]
  apply exists_congr
  intro m
  constructor
  · rintro ⟨r, hmn, hr, h⟩
    rw [dvd_C_iff_exists ha] at hr
    obtain ⟨b, hb, hr⟩ := hr
    use b, hmn, hb
    rw [h, mul_comm, hr, C_mul_monomial, mul_one]
  · rintro ⟨b, hmn, hb, h⟩
    use C b, hmn, map_dvd C hb
    rwa [mul_comm, C_mul_monomial, mul_one]
/-
**MvPolynomial.dvd_monomial_one_iff_exists** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomi
al`。
形式化陈述：dvd_monomial_one_iff_exists {n : σ ->₀ Nat} : p ∣ monomial n 1 ↔ exists m 
u, m <= n ∧ IsUnit u ∧ p = monomial m u
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `true_iff`：∀ (p : Prop), (True ↔ p) = p
· 使用定理 `MvPolynomial.dvd_monomial_iff_exists`：dvd_monomial_iff_exists {n : σ ->₀
 Nat} {a : R} (ha : a != 0) : p ∣ monomial n a ↔ exists m b, m <= n ∧ b ∣ a ∧ p 
= monomial m b
· 使用引理 `one_ne_zero'`：one_ne_zero' [One α] [NeZero (1 : α)] : (1 : α) != 0
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem dvd_monomial_one_iff_exists {n : σ →₀ ℕ} :
    p ∣ monomial n 1 ↔ ∃ m u, m ≤ n ∧ IsUnit u ∧ p = monomial m u := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · suffices ∃ m, m ≤ n by simpa [Subsingleton.elim _ p]
    use n
  rw [dvd_monomial_iff_exists (one_ne_zero' R)]
  apply exists_congr
  intro m
  simp_rw [isUnit_iff_dvd_one]
/-
**MvPolynomial.dvd_smul_X_iff_exists** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：dvd_smul_X_iff_exists {i : σ} {r : R} (hr : r != 0) : p ∣ r • X i ↔ exists
 s, s ∣ r ∧ (p = C s ∨ p = s • X i)
参数：hr : r != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.X.eq_1`：∀ {R : Type u} {σ : Type u_1} [inst : CommSemiring 
R] (n : σ),   MvPolynomial.X n = (MvPolynomial.monomial fun₀ | n => 1) 1
· 使用定理 `MvPolynomial.smul_monomial`：smul_monomial {S₁ : Type*} [SMulZeroClass S₁
 R] (r : S₁) : r • monomial s a = monomial s (r • a)
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MvPolynomial.dvd_monomial_iff_exists`：dvd_monomial_iff_exists {n : σ ->₀
 Nat} {a : R} (ha : a != 0) : p ∣ monomial n a ↔ exists m b, m <= n ∧ b ∣ a ∧ p 
= monomial m b
· 使用定理 `exists_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∃ a b,
 p a b) ↔ ∃ b a, p a b
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Finsupp.single_eq_of_ne`：single_eq_of_ne (h : a' != a) : (single a b : α
 ->₀ M) a' = 0
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Finsupp.instIsBotZeroClass`：∀ {ι : Type u_1} {α : Type u_3} [inst : AddC
ommMonoid α] [inst_1 : PartialOrder α] [IsBotZeroClass α],   IsBotZeroClass (ι →
₀ α)
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem dvd_smul_X_iff_exists {i : σ} {r : R} (hr : r ≠ 0) :
    p ∣ r • X i ↔ ∃ s, s ∣ r ∧ (p = C s ∨ p = s • X i) := by
  rw [X, smul_monomial, smul_eq_mul, mul_one, dvd_monomial_iff_exists hr, exists_comm]
  apply exists_congr
  intro b
  constructor
  · rintro ⟨m, hmn, hb, rfl⟩
    simp only [hb, true_and]
    suffices m = 0 ∨ m = Finsupp.single i 1 by
      apply this.imp <;> simp +contextual [smul_monomial, smul_eq_mul, mul_one]
    by_cases hm : m i = 0
    · left
      ext j
      simp only [Finsupp.coe_zero, Pi.zero_apply, ← Nat.le_zero]
      by_cases hj : j = i
      · rw [← hm, hj]
      · exact (hmn j).trans (Finsupp.single_eq_of_ne hj).le
    · right
      ext j
      apply le_antisymm (hmn j)
      by_cases hj : j = i
      · simpa [hj, Nat.one_le_iff_ne_zero]
      · simp [Finsupp.single_eq_of_ne hj]
  · rintro ⟨hb, hp | hp⟩
    · use 0; simp [hb, hp]
    · use Finsupp.single i 1, le_rfl, hb
      simp [hp, smul_monomial]
/-
**MvPolynomial.dvd_X_iff_exists** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：dvd_X_iff_exists {i : σ} : p ∣ X i ↔ exists r, IsUnit r ∧ (p = C r ∨ p = r
 • X i)
该定理/引理刻画了左右两侧的等价关系。
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
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Zero.instNonempty`：∀ {α : Type u} [Zero α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `MvPolynomial.dvd_smul_X_iff_exists`：dvd_smul_X_iff_exists {i : σ} {r : R
} (hr : r != 0) : p ∣ r • X i ↔ exists s, s ∣ r ∧ (p = C s ∨ p = s • X i)
· 使用引理 `one_ne_zero'`：one_ne_zero' [One α] [NeZero (1 : α)] : (1 : α) != 0
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `isUnit_iff_dvd_one`：isUnit_iff_dvd_one {x : α} : IsUnit x ↔ x ∣ 1
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem dvd_X_iff_exists {i : σ} :
    p ∣ X i ↔ ∃ r, IsUnit r ∧ (p = C r ∨ p = r • X i) := by
  nontriviality R
  rw [← one_smul R (X i), dvd_smul_X_iff_exists (one_ne_zero' R)]
  apply exists_congr
  intro r
  rw [isUnit_iff_dvd_one, one_smul]

end CommRing

end MvPolynomial

