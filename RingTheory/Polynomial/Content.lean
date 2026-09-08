/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
module

public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Algebra.Polynomial.CancelLeads
public import Mathlib.Algebra.Polynomial.EraseLead
public import Mathlib.Algebra.Polynomial.FieldDivision

/-!
# GCD structures on polynomials

Definitions and basic results about polynomials over GCD domains, particularly their contents
and primitive polynomials.

## Main Definitions
Let `p : R[X]`.
- `p.content` is the `gcd` of the coefficients of `p`.
- `p.IsPrimitive` indicates that `p.content = 1`.

## Main Results
- `Polynomial.content_mul`: if `p q : R[X]`, then `(p * q).content = p.content * q.content`.
- `Polynomial.NormalizedGcdMonoid`: the polynomial ring of a GCD domain is itself a GCD domain.

## Note

This has nothing to do with minimal polynomials of primitive elements in finite fields.

-/

@[expose] public section


namespace Polynomial

section Primitive

variable {R : Type*} [CommSemiring R]

/-- A polynomial is primitive when the only constant polynomials dividing it are units.
Note: This has nothing to do with minimal polynomials of primitive elements in finite fields. -/
/-
**Polynomial.IsPrimitive** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：IsPrimitive (p : R[X]) : Prop
参数：p : R[X]。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A polynomial is primitive when the only constant polynomials dividing it are uni
ts.
Note: This has nothing to do with minimal polynomials of primitive elements in f
inite fields.
-/
def IsPrimitive (p : R[X]) : Prop :=
  ∀ r : R, C r ∣ p → IsUnit r
/-
**Polynomial.isPrimitive_iff_isUnit_of_C_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Polynomi
al`。
形式化陈述：isPrimitive_iff_isUnit_of_C_dvd {p : R[X]} : p.IsPrimitive ↔ forall r : R,
 C r ∣ p -> IsUnit r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isPrimitive_iff_isUnit_of_C_dvd {p : R[X]} : p.IsPrimitive ↔ ∀ r : R, C r ∣ p → IsUnit r :=
  Iff.rfl

@[simp]
/-
**Polynomial.isPrimitive_one** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：isPrimitive_one : IsPrimitive (1 : R[X])
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.isUnit_C`：isUnit_C {x : R} : IsUnit (C x) ↔ IsUnit x
· 使用定理 `isUnit_of_dvd_one`：isUnit_of_dvd_one {a : α} (h : a ∣ 1) : IsUnit (a : α
)
-/
theorem isPrimitive_one : IsPrimitive (1 : R[X]) := fun _ h =>
  isUnit_C.mp (isUnit_of_dvd_one h)
/-
**Polynomial.Monic.isPrimitive** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Monic`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {p : Polynomial R}, p.Monic → p.I
sPrimitive
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUnit.of_mul_eq_one`：IsUnit.of_mul_eq_one [Monoid M] [IsDedekindFiniteM
onoid M] {a : M} (b : M) (h : a * b = 1) : IsUnit a
· 使用定理 `instIsDedekindFiniteMonoid`：∀ (M : Type u_2) [inst : CommMonoid M], IsDe
dekindFiniteMonoid M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.coeff_C_mul`：coeff_C_mul (p : R[X]) : coeff (C a * p) n = a *
 coeff p n
-/
theorem Monic.isPrimitive {p : R[X]} (hp : p.Monic) : p.IsPrimitive := by
  rintro r ⟨q, h⟩
  exact .of_mul_eq_one (q.coeff p.natDegree) (by rwa [← coeff_C_mul, ← h])
/-
**Polynomial.IsPrimitive.ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.IsPrimiti
ve`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] [Nontrivial R] {p : Polynomial R}
, p.IsPrimitive → p ≠ 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUnit.ne_zero`：ne_zero [Nontrivial M₀] {a : M₀} (ha : IsUnit a) : a != 
0
· 使用定理 `dvd_zero`：dvd_zero (a : α) : a ∣ 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem IsPrimitive.ne_zero [Nontrivial R] {p : R[X]} (hp : p.IsPrimitive) : p ≠ 0 := by
  rintro rfl
  exact (hp 0 (dvd_zero (C 0))).ne_zero rfl
/-
**Polynomial.isPrimitive_of_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：isPrimitive_of_dvd {p q : R[X]} (hp : IsPrimitive p) (hq : q ∣ p) : IsPrim
itive q
参数：hp : IsPrimitive p；hq : q ∣ p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.isPrimitive_iff_isUnit_of_C_dvd`：isPrimitive_iff_isUnit_of_C_
dvd {p : R[X]} : p.IsPrimitive ↔ forall r : R, C r ∣ p -> IsUnit r
· 使用定理 `dvd_trans`：dvd_trans : a ∣ b -> b ∣ c -> a ∣ c | ⟨d, h₁⟩, ⟨e, h₂⟩ => ⟨d 
* e, h₁ ▸ h₂.trans mul_assoc a d e⟩  alias Dvd.dvd.trans
-/
theorem isPrimitive_of_dvd {p q : R[X]} (hp : IsPrimitive p) (hq : q ∣ p) : IsPrimitive q :=
  fun a ha => isPrimitive_iff_isUnit_of_C_dvd.mp hp a (dvd_trans ha hq)

/-- An irreducible nonconstant polynomial over a domain is primitive. -/
/-
**Polynomial._root_.Irreducible.isPrimitive** 是 Mathlib 中的一个定理，位于命名空间 `Polynomia
l`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An irreducible nonconstant polynomial over a domain is primitive.
-/
theorem _root_.Irreducible.isPrimitive [NoZeroDivisors R]
    {p : Polynomial R} (hp : Irreducible p) (hp' : p.natDegree ≠ 0) : p.IsPrimitive := by
  rintro r ⟨q, hq⟩
  suffices ¬IsUnit q by simpa using ((hp.2 hq).resolve_right this).map Polynomial.constantCoeff
  intro H
  have hr : r ≠ 0 := by rintro rfl; simp_all
  obtain ⟨s, hs, rfl⟩ := Polynomial.isUnit_iff.mp H
  simp [hq, Polynomial.natDegree_C_mul hr] at hp'

/-- In a field, the notion of primitive polynomials is degenerate. -/
@[simp]
/-
**Polynomial.isPrimitive_iff_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：isPrimitive_iff_ne_zero {F : Type*} [Field F] (p : F[X]) : p.IsPrimitive ↔
 p != 0
参数：p : F[X]。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.IsPrimitive.ne_zero`：∀ {R : Type u_1} [inst : CommSemiring R]
 [Nontrivial R] {p : Polynomial R}, p.IsPrimitive → p ≠ 0
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `IsUnit.mk0`：IsUnit.mk0 (x : G₀) (hx : x != 0) : IsUnit x
· 使用定理 `ne_zero_of_dvd_ne_zero`：ne_zero_of_dvd_ne_zero {p q : α} (h₁ : q != 0) (
h₂ : p ∣ q) : p != 0
· 使用定理 `Polynomial.C_0`：C_0 : C (0 : R) = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
In a field, the notion of primitive polynomials is degenerate.
-/
theorem isPrimitive_iff_ne_zero {F : Type*} [Field F] (p : F[X]) : p.IsPrimitive ↔ p ≠ 0 :=
  ⟨IsPrimitive.ne_zero, fun h _ hrp ↦ .mk0 _ fun hr ↦ ne_zero_of_dvd_ne_zero h hrp <| hr ▸ C_0⟩

end Primitive

variable {R : Type*} [CommRing R]

section NormalizedGCDMonoid

variable [NormalizedGCDMonoid R]

/-- `p.content` is the `gcd` of the coefficients of `p`. -/
/-
**Polynomial.content** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：content (p : R[X]) : R
参数：p : R[X]。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`p.content` is the `gcd` of the coefficients of `p`.
-/
def content (p : R[X]) : R :=
  p.support.gcd p.coeff
/-
**Polynomial.content_dvd_coeff** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：content_dvd_coeff {p : R[X]} (n : Nat) : p.content ∣ p.coeff n
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.gcd_dvd`：gcd_dvd {b : β} (hb : b in s) : s.gcd f ∣ f b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `Polynomial.mem_support_iff`：mem_support_iff : n in p.support ↔ p.coeff n
 != 0
· 使用定理 `dvd_zero`：dvd_zero (a : α) : a ∣ 0
-/
theorem content_dvd_coeff {p : R[X]} (n : ℕ) : p.content ∣ p.coeff n := by
  by_cases h : n ∈ p.support
  · apply Finset.gcd_dvd h
  rw [mem_support_iff, Classical.not_not] at h
  rw [h]
  apply dvd_zero

@[simp]
/-
**Polynomial.content_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：content_C {r : R} : (C r).content = normalize r
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.content.eq_1`：∀ {R : Type u_1} [inst : CommRing R] [inst_1 : 
NormalizedGCDMonoid R] (p : Polynomial R),   p.content = p.support.gcd p.coeff
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `normalize_zero`：∀ {α : Type u_1} [inst : MonoidWithZero α] [inst_1 : Nor
malizationMonoid α], normalize 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.support_monomial`：support_monomial (n) {a : R} (h : a != 0) :
 (monomial n a).support = singleton n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.gcd_singleton`：gcd_singleton {b : β} : ({b} : Finset β).gcd f = n
ormalize (f b)
· 使用定理 `Polynomial.coeff_C_zero`：coeff_C_zero : coeff (C a) 0 = a
-/
theorem content_C {r : R} : (C r).content = normalize r := by
  rw [content]
  by_cases h0 : r = 0
  · simp [h0]
  have h : (C r).support = {0} := support_monomial _ h0
  simp [h]

@[simp]
/-
**Polynomial.content_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：content_zero : content (0 : R[X]) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.C_0`：C_0 : C (0 : R) = 0
· 使用定理 `Polynomial.content_C`：content_C {r : R} : (C r).content = normalize r
· 使用定理 `normalize_zero`：∀ {α : Type u_1} [inst : MonoidWithZero α] [inst_1 : Nor
malizationMonoid α], normalize 0 = 0
-/
theorem content_zero : content (0 : R[X]) = 0 := by rw [← C_0, content_C, normalize_zero]

@[simp]
/-
**Polynomial.content_one** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：content_one : content (1 : R[X]) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.C_1`：C_1 : C (1 : R) = 1
· 使用定理 `Polynomial.content_C`：content_C {r : R} : (C r).content = normalize r
· 使用定理 `normalize_one`：∀ {α : Type u_1} [inst : MonoidWithZero α] [inst_1 : Norm
alizationMonoid α], normalize 1 = 1
-/
theorem content_one : content (1 : R[X]) = 1 := by rw [← C_1, content_C, normalize_one]
/-
**Polynomial.content_X_mul** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：content_X_mul {p : R[X]} : content (X * p) = content p
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.content.eq_1`：∀ {R : Type u_1} [inst : CommRing R] [inst_1 : 
NormalizedGCDMonoid R] (p : Polynomial R),   p.content = p.support.gcd p.coeff
· 使用定理 `Finset.gcd_def`：gcd_def : s.gcd f = (s.1.map f).gcd
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Nat.succ_injective`：succ_injective : Injective Nat.succ
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Polynomial.mul_coeff_zero`：mul_coeff_zero (p q : R[X]) : coeff (p * q) 0
 = coeff p 0 * coeff q 0
· 使用定理 `Polynomial.coeff_X_zero`：coeff_X_zero : coeff (X : R[X]) 0 = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Polynomial.coeff_mul_X`：coeff_mul_X (p : R[X]) (n : Nat) : coeff (p * X)
 (n + 1) = coeff p n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
· 使用定理 `Polynomial.coeff_X_mul`：coeff_X_mul (p : R[X]) (n : Nat) : coeff (X * p)
 (n + 1) = coeff p n
-/
theorem content_X_mul {p : R[X]} : content (X * p) = content p := by
  rw [content, content, Finset.gcd_def, Finset.gcd_def]
  refine congr rfl ?_
  have h : (X * p).support = p.support.map ⟨Nat.succ, Nat.succ_injective⟩ := by
    ext a
    simp only [Finset.mem_map, Function.Embedding.coeFn_mk, Ne, mem_support_iff]
    rcases a with - | a
    · simp
    rw [mul_comm, coeff_mul_X]
    constructor
    · intro h
      use a
    · rintro ⟨b, ⟨h1, h2⟩⟩
      rw [← Nat.succ_injective h2]
      apply h1
  rw [h]
  simp

@[simp]
/-
**Polynomial.content_X_pow** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：content_X_pow {k : Nat} : content ((X : R[X]) ^ k) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Polynomial.content_one`：content_one : content (1 : R[X]) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `Polynomial.content_X_mul`：content_X_mul {p : R[X]} : content (X * p) = c
ontent p
-/
theorem content_X_pow {k : ℕ} : content ((X : R[X]) ^ k) = 1 := by
  induction k with
  | zero => simp
  | succ k hi => rw [pow_succ', content_X_mul, hi]

@[simp]
/-
**Polynomial.content_X** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：content_X : content (X : R[X]) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Polynomial.content_X_mul`：content_X_mul {p : R[X]} : content (X * p) = c
ontent p
· 使用定理 `Polynomial.content_one`：content_one : content (1 : R[X]) = 1
-/
theorem content_X : content (X : R[X]) = 1 := by rw [← mul_one X, content_X_mul, content_one]
/-
**Polynomial.content_C_mul** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：content_C_mul {R} [CommRing R] [StrongNormalizedGCDMonoid R] (r : R) (p : 
R[X]) : (C r * p).content = normalize r * p.content
参数：r : R；p : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Polynomial.content_zero`：content_zero : content (0 : R[X]) = 0
· 使用定理 `normalize_zero`：∀ {α : Type u_1} [inst : MonoidWithZero α] [inst_1 : Nor
malizationMonoid α], normalize 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.content.eq_1`：∀ {R : Type u_1} [inst : CommRing R] [inst_1 : 
NormalizedGCDMonoid R] (p : Polynomial R),   p.content = p.support.gcd p.coeff
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.gcd_mul_left`：∀ {β : Type u_3} {α : Type u_5} [inst : CommMonoidW
ithZero α] [inst_1 : StrongNormalizedGCDMonoid α] {s : Finset β}   {f : β → α} {
a : α}, (…
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `Polynomial.coeff_C_mul`：coeff_C_mul (p : R[X]) : coeff (C a * p) n = a *
 coeff p n
· 使用定理 `IsRightCancelMulZero.to_noZeroDivisors`：∀ (M₀ : Type u_1) [inst : MulZer
oClass M₀] [IsRightCancelMulZero M₀], NoZeroDivisors M₀
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `GCDMonoid.toIsCancelMulZero`：∀ {α : Type u_2} {inst : CommMonoidWithZero
 α} [self : GCDMonoid α], IsCancelMulZero α
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem content_C_mul {R} [CommRing R] [StrongNormalizedGCDMonoid R] (r : R) (p : R[X]) :
    (C r * p).content = normalize r * p.content := by
  by_cases h0 : r = 0; · simp [h0]
  rw [content, content, ← Finset.gcd_mul_left]
  refine congr (congr rfl ?_) ?_ <;> ext <;> simp [h0, mem_support_iff]
/-
**Polynomial.associated_content_C_mul** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：associated_content_C_mul (r : R) (p : R[X]) : Associated (C r * p).content
 (r * p.content)
参数：r : R；p : R[X]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Polynomial.content_zero`：content_zero : content (0 : R[X]) = 0
· 使用定理 `Associated.trans`：∀ {M : Type u_1} [inst : Monoid M] {x y z : M}, Associ
ated x y → Associated y z → Associated x z
· 使用定理 `Associated.of_eq`：Associated.of_eq [Monoid M] {a b : M} (h : a = b) : a 
~ᵤ b
· 使用定理 `Polynomial.content.eq_1`：∀ {R : Type u_1} [inst : CommRing R] [inst_1 : 
NormalizedGCDMonoid R] (p : Polynomial R),   p.content = p.support.gcd p.coeff
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `Polynomial.coeff_C_mul`：coeff_C_mul (p : R[X]) : coeff (C a * p) n = a *
 coeff p n
· 使用定理 `IsRightCancelMulZero.to_noZeroDivisors`：∀ (M₀ : Type u_1) [inst : MulZer
oClass M₀] [IsRightCancelMulZero M₀], NoZeroDivisors M₀
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `GCDMonoid.toIsCancelMulZero`：∀ {α : Type u_2} {inst : CommMonoidWithZero
 α} [self : GCDMonoid α], IsCancelMulZero α
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.gcd_mul_left'`：∀ {α : Type u_2} {β : Type u_3} [inst : CommMonoid
WithZero α] [inst_1 : NormalizedGCDMonoid α] (s : Finset β)   (f : β → α) (a : α
), Associa…
-/
theorem associated_content_C_mul (r : R) (p : R[X]) :
    Associated (C r * p).content (r * p.content) := by
  by_cases h0 : r = 0; · simp [h0]
  refine .trans (.of_eq ?_) (Finset.gcd_mul_left' _ _ _)
  rw [content]; refine congr (congr rfl ?_) ?_ <;> ext <;> simp [h0, mem_support_iff]

-- `simp`-normal form is `normUnit_content`
/-
**Polynomial.normalize_content** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：normalize_content {p : R[X]} : normalize p.content = p.content
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.normalize_gcd`：normalize_gcd : normalize (s.gcd f) = s.gcd f
-/
theorem normalize_content {p : R[X]} : normalize p.content = p.content :=
  Finset.normalize_gcd

@[simp]
/-
**Polynomial.content_monomial** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：content_monomial {r : R} {k : Nat} : content (monomial k r) = normalize r
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.C_mul_X_pow_eq_monomial`：∀ {R : Type u} {a : R} [inst : Semir
ing R] {n : ℕ}, Polynomial.C a * Polynomial.X ^ n = (Polynomial.monomial n) a
· 使用定理 `Polynomial.normalize_content`：normalize_content {p : R[X]} : normalize p
.content = p.content
· 使用定理 `normalize_eq_normalize_iff_associated`：normalize_eq_normalize_iff_associ
ated {a b : α} : normalize a = normalize b ↔ Associated a b where mp h
· 使用引理 `Mathlib.Tactic.GCongr.rel_imp_rel`：rel_imp_rel (h₁ : r c a) (h₂ : r b d)
 : r a b -> r c d
· 使用定理 `Associated.instIsTrans`：∀ {M : Type u_1} [inst : Monoid M], IsTrans M As
sociated
· 使用定理 `Polynomial.associated_content_C_mul`：associated_content_C_mul (r : R) (p
 : R[X]) : Associated (C r * p).content (r * p.content)
· 使用定理 `Associated.refl`：∀ {M : Type u_1} [inst : Monoid M] (x : M), Associated 
x x
· 使用定理 `Polynomial.content_X_pow`：content_X_pow {k : Nat} : content ((X : R[X]) 
^ k) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Associated.rfl`：∀ {M : Type u_1} [inst : Monoid M] {x : M}, Associated x
 x
-/
theorem content_monomial {r : R} {k : ℕ} : content (monomial k r) = normalize r := by
  rw [← C_mul_X_pow_eq_monomial, ← normalize_content, normalize_eq_normalize_iff_associated]
  grw [associated_content_C_mul, content_X_pow, mul_one]
  exact Associated.rfl
/-
**Polynomial.content_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：content_eq_zero_iff {p : R[X]} : content p = 0 ↔ p = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.content.eq_1`：∀ {R : Type u_1} [inst : CommRing R] [inst_1 : 
NormalizedGCDMonoid R] (p : Polynomial R),   p.content = p.support.gcd p.coeff
· 使用定理 `Finset.gcd_eq_zero_iff`：gcd_eq_zero_iff : s.gcd f = 0 ↔ forall x in s, f
 x = 0
· 使用定理 `Polynomial.ext`：ext {p q : R[X]} : (forall n, coeff p n = coeff q n) -> 
p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem content_eq_zero_iff {p : R[X]} : content p = 0 ↔ p = 0 := by
  rw [content, Finset.gcd_eq_zero_iff]
  constructor <;> intro h
  · ext n
    simp_all
  · intro x
    simp [h]

@[simp]
/-
**Polynomial.normUnit_content** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：normUnit_content {p : R[X]} : normUnit (content p) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NormalizationMonoid.normUnit_zero`：∀ {α : Type u_2} {inst : MonoidWithZe
ro α} [self : NormalizationMonoid α], normUnit 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Units.ext`：ext {u v : αˣ} (huv : u.val = v.val) : u = v
· 使用定理 `mul_left_cancel₀`：mul_left_cancel₀ (ha : a != 0) (h : a * b = a * c) : b
 = c
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `GCDMonoid.toIsCancelMulZero`：∀ {α : Type u_2} {inst : CommMonoidWithZero
 α} [self : GCDMonoid α], IsCancelMulZero α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `normalize_apply`：normalize_apply (x : α) : normalize x = x * normUnit x
· 使用定理 `Polynomial.normalize_content`：normalize_content {p : R[X]} : normalize p
.content = p.content
· 使用定理 `Units.val_one`：val_one : ((1 : αˣ) : α) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem normUnit_content {p : R[X]} : normUnit (content p) = 1 := by
  by_cases hp0 : p.content = 0
  · simp [hp0]
  · ext
    apply mul_left_cancel₀ hp0
    rw [← normalize_apply, normalize_content, Units.val_one, mul_one]
/-
**Polynomial.content_eq_gcd_range_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：content_eq_gcd_range_of_lt (p : R[X]) (n : Nat) (h : p.natDegree < n) : p.
content = (Finset.range n).gcd p.coeff
参数：p : R[X]；n : Nat；h : p.natDegree < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dvd_antisymm_of_normalize_eq`：dvd_antisymm_of_normalize_eq {a b : α} (ha
 : normalize a = a) (hb : normalize b = b) (hab : a ∣ b) (hba : b ∣ a) : a = b
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `GCDMonoid.toIsCancelMulZero`：∀ {α : Type u_2} {inst : CommMonoidWithZero
 α} [self : GCDMonoid α], IsCancelMulZero α
· 使用定理 `Polynomial.normalize_content`：normalize_content {p : R[X]} : normalize p
.content = p.content
· 使用定理 `Finset.normalize_gcd`：normalize_gcd : normalize (s.gcd f) = s.gcd f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.dvd_gcd_iff`：dvd_gcd_iff {a : α} : a ∣ s.gcd f ↔ forall b in s, a
 ∣ f b
· 使用定理 `Polynomial.content_dvd_coeff`：content_dvd_coeff {p : R[X]} (n : Nat) : p
.content ∣ p.coeff n
· 使用定理 `Finset.gcd_mono`：gcd_mono (h : s₁ subseteq s₂) : s₂.gcd f ∣ s₁.gcd f
· 使用定理 `Polynomial.supp_subset_range`：supp_subset_range (h : natDegree p < m) : 
p.support subseteq Finset.range m
-/
theorem content_eq_gcd_range_of_lt (p : R[X]) (n : ℕ) (h : p.natDegree < n) :
    p.content = (Finset.range n).gcd p.coeff := by
  apply dvd_antisymm_of_normalize_eq normalize_content Finset.normalize_gcd
  · rw [Finset.dvd_gcd_iff]
    intro i _
    apply content_dvd_coeff _
  · exact Finset.gcd_mono (supp_subset_range h)
/-
**Polynomial.content_eq_gcd_range_succ** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：content_eq_gcd_range_succ (p : R[X]) : p.content = (Finset.range p.natDegr
ee.succ).gcd p.coeff
参数：p : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.content_eq_gcd_range_of_lt`：content_eq_gcd_range_of_lt (p : R
[X]) (n : Nat) (h : p.natDegree < n) : p.content = (Finset.range n).gcd p.coeff
· 使用定理 `Nat.lt_succ_self`：∀ (n : ℕ), n < n.succ
-/
theorem content_eq_gcd_range_succ (p : R[X]) :
    p.content = (Finset.range p.natDegree.succ).gcd p.coeff :=
  content_eq_gcd_range_of_lt _ _ (Nat.lt_succ_self _)
/-
**Polynomial.content_eq_gcd_leadingCoeff_content_eraseLead** 是 Mathlib 中的一个定理，位于
命名空间 `Polynomial`。
形式化陈述：content_eq_gcd_leadingCoeff_content_eraseLead (p : R[X]) : p.content = gcd
 p.leadingCoeff (eraseLead p).content
参数：p : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.content_zero`：content_zero : content (0 : R[X]) = 0
· 使用定理 `Polynomial.eraseLead_zero`：eraseLead_zero : eraseLead (0 : R[X]) = 0
· 使用定理 `gcd_same`：gcd_same [NormalizedGCDMonoid α] (a : α) : gcd a a = normalize
 a
· 使用定理 `normalize_zero`：∀ {α : Type u_1} [inst : MonoidWithZero α] [inst_1 : Nor
malizationMonoid α], normalize 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.content.eq_1`：∀ {R : Type u_1} [inst : CommRing R] [inst_1 : 
NormalizedGCDMonoid R] (p : Polynomial R),   p.content = p.support.gcd p.coeff
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.insert_erase`：∀ {α : Type u_1} [inst : DecidableEq α] {s : Finset
 α} {a : α}, a ∈ s → insert a (s.erase a) = s
· 使用定理 `Polynomial.mem_support_iff`：mem_support_iff : n in p.support ↔ p.coeff n
 != 0
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Polynomial.leadingCoeff.eq_1`：∀ {R : Type u} [inst : Semiring R] (p : Po
lynomial R), p.leadingCoeff = p.coeff p.natDegree
· 使用定理 `Polynomial.leadingCoeff_eq_zero`：leadingCoeff_eq_zero : leadingCoeff p =
 0 ↔ p = 0
· 使用定理 `Finset.gcd_insert`：gcd_insert [DecidableEq β] {b : β} : (insert b s : Fi
nset β).gcd f = GCDMonoid.gcd (f b) (s.gcd f)
· 使用定理 `Polynomial.eraseLead_support`：eraseLead_support (f : R[X]) : f.eraseLead
.support = f.support.erase f.natDegree
· 使用定理 `Finset.gcd_congr`：gcd_congr {f g : β -> α} (hs : s₁ = s₂) (hfg : forall 
a in s₂, f a = g a) : s₁.gcd f = s₂.gcd g
· 使用定理 `Polynomial.eraseLead_coeff`：eraseLead_coeff (i : Nat) : f.eraseLead.coef
f i = if i = f.natDegree then 0 else f.coeff i
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Finset.mem_erase`：mem_erase {a b : α} {s : Finset α} : a in erase s b ↔ 
a != b ∧ a in s
-/
theorem content_eq_gcd_leadingCoeff_content_eraseLead (p : R[X]) :
    p.content = gcd p.leadingCoeff (eraseLead p).content := by
  by_cases h : p = 0
  · simp [h]
  rw [← leadingCoeff_eq_zero, leadingCoeff, ← Ne, ← mem_support_iff] at h
  rw [content, ← Finset.insert_erase h, Finset.gcd_insert, leadingCoeff, content,
    eraseLead_support]
  refine congr rfl (Finset.gcd_congr rfl fun i hi => ?_)
  rw [Finset.mem_erase] at hi
  rw [eraseLead_coeff, if_neg hi.1]
/-
**Polynomial.dvd_content_iff_C_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：dvd_content_iff_C_dvd {p : R[X]} {r : R} : r ∣ p.content ↔ C r ∣ p
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.C_dvd_iff_dvd_coeff`：C_dvd_iff_dvd_coeff (r : R) (φ : R[X]) :
 C r ∣ φ ↔ forall i, r ∣ φ.coeff i
· 使用定理 `Dvd.dvd.trans`：∀ {α : Type u_1} [inst : Semigroup α] {a b c : α}, a ∣ b 
→ b ∣ c → a ∣ c
· 使用定理 `Polynomial.content_dvd_coeff`：content_dvd_coeff {p : R[X]} (n : Nat) : p
.content ∣ p.coeff n
· 使用定理 `Polynomial.content.eq_1`：∀ {R : Type u_1} [inst : CommRing R] [inst_1 : 
NormalizedGCDMonoid R] (p : Polynomial R),   p.content = p.support.gcd p.coeff
· 使用定理 `Finset.dvd_gcd_iff`：dvd_gcd_iff {a : α} : a ∣ s.gcd f ↔ forall b in s, a
 ∣ f b
-/
theorem dvd_content_iff_C_dvd {p : R[X]} {r : R} : r ∣ p.content ↔ C r ∣ p := by
  rw [C_dvd_iff_dvd_coeff]
  constructor
  · intro h i
    apply h.trans (content_dvd_coeff _)
  · intro h
    rw [content, Finset.dvd_gcd_iff]
    intro i _
    apply h i
/-
**Polynomial.C_content_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：C_content_dvd (p : R[X]) : C p.content ∣ p
参数：p : R[X]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.dvd_content_iff_C_dvd`：dvd_content_iff_C_dvd {p : R[X]} {r : 
R} : r ∣ p.content ↔ C r ∣ p
· 使用定理 `dvd_rfl`：dvd_rfl : forall {a : α}, a ∣ a
-/
theorem C_content_dvd (p : R[X]) : C p.content ∣ p :=
  dvd_content_iff_C_dvd.1 dvd_rfl
/-
**Polynomial.isPrimitive_iff_content_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Polynomia
l`。
形式化陈述：isPrimitive_iff_content_eq_one {p : R[X]} : p.IsPrimitive ↔ p.content = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.normalize_content`：normalize_content {p : R[X]} : normalize p
.content = p.content
· 使用定理 `normalize_eq_one`：normalize_eq_one {x : α} : normalize x = 1 ↔ IsUnit x 
where mp hx
· 使用定理 `Polynomial.IsPrimitive.eq_1`：∀ {R : Type u_1} [inst : CommSemiring R] (p
 : Polynomial R), p.IsPrimitive = ∀ (r : R), Polynomial.C r ∣ p → IsUnit r
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `dvd_refl`：dvd_refl (a : α) : a ∣ a
· 使用定理 `isUnit_of_dvd_unit`：isUnit_of_dvd_unit {x y : α} (xy : x ∣ y) (hu : IsUn
it y) : IsUnit x
-/
theorem isPrimitive_iff_content_eq_one {p : R[X]} : p.IsPrimitive ↔ p.content = 1 := by
  rw [← normalize_content, normalize_eq_one, IsPrimitive]
  simp_rw [← dvd_content_iff_C_dvd]
  exact ⟨fun h => h p.content (dvd_refl p.content), fun h r hdvd => isUnit_of_dvd_unit hdvd h⟩
/-
**Polynomial.IsPrimitive.content_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Is
Primitive`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] [inst_1 : NormalizedGCDMonoid R] {p :
 Polynomial R}, p.IsPrimitive → p.content = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.isPrimitive_iff_content_eq_one`：isPrimitive_iff_content_eq_on
e {p : R[X]} : p.IsPrimitive ↔ p.content = 1
-/
theorem IsPrimitive.content_eq_one {p : R[X]} (hp : p.IsPrimitive) : p.content = 1 :=
  isPrimitive_iff_content_eq_one.mp hp

section PrimPart

/-- The primitive part of a polynomial `p` is the primitive polynomial gained by dividing `p` by
  `p.content`. If `p = 0`, then `p.primPart = 1`. -/
/-
**Polynomial.primPart** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：primPart (p : R[X]) : R[X]
参数：p : R[X]。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.C_content_dvd`：C_content_dvd (p : R[X]) : C p.content ∣ p

--- 原说明 ---
The primitive part of a polynomial `p` is the primitive polynomial gained by div
iding `p` by
  `p.content`. If `p = 0`, then `p.primPart = 1`.
-/
noncomputable def primPart (p : R[X]) : R[X] :=
  letI := Classical.decEq R
  if p = 0 then 1 else Classical.choose (C_content_dvd p)
/-
**Polynomial.eq_C_content_mul_primPart** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：eq_C_content_mul_primPart (p : R[X]) : p = C p.content * p.primPart
参数：p : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.content_zero`：content_zero : content (0 : R[X]) = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.C_content_dvd`：C_content_dvd (p : R[X]) : C p.content ∣ p
· 使用定理 `Polynomial.primPart.eq_1`：∀ {R : Type u_1} [inst : CommRing R] [inst_1 :
 NormalizedGCDMonoid R] (p : Polynomial R),   p.primPart = if p = 0 then 1 else 
Classical.choo…
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem eq_C_content_mul_primPart (p : R[X]) : p = C p.content * p.primPart := by
  by_cases h : p = 0; · simp [h]
  rw [primPart, if_neg h, ← Classical.choose_spec (C_content_dvd p)]

@[simp]
/-
**Polynomial.primPart_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：primPart_zero : primPart (0 : R[X]) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Polynomial.C_content_dvd`：C_content_dvd (p : R[X]) : C p.content ∣ p
-/
theorem primPart_zero : primPart (0 : R[X]) = 1 :=
  if_pos rfl
/-
**Polynomial.isPrimitive_primPart** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：isPrimitive_primPart (p : R[X]) : p.primPart.IsPrimitive
参数：p : R[X]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.primPart_zero`：primPart_zero : primPart (0 : R[X]) = 1
· 使用定理 `Polynomial.isPrimitive_iff_content_eq_one`：isPrimitive_iff_content_eq_on
e {p : R[X]} : p.IsPrimitive ↔ p.content = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.normalize_content`：normalize_content {p : R[X]} : normalize p
.content = p.content
· 使用定理 `normalize_eq_one`：normalize_eq_one {x : α} : normalize x = 1 ↔ IsUnit x 
where mp hx
· 使用定理 `isUnit_of_associated_mul`：isUnit_of_associated_mul [CommMonoidWithZero M
] [IsCancelMulZero M] {p b : M} (h : Associated (p * b) p) (hp : p != 0) : IsUni
t b
· 使用定理 `GCDMonoid.toIsCancelMulZero`：∀ {α : Type u_2} {inst : CommMonoidWithZero
 α} [self : GCDMonoid α], IsCancelMulZero α
· 使用定理 `Associated.symm`：∀ {M : Type u_1} [inst : Monoid M] {x y : M}, Associate
d x y → Associated y x
· 使用定理 `Polynomial.eq_C_content_mul_primPart`：eq_C_content_mul_primPart (p : R[X
]) : p = C p.content * p.primPart
· 使用定理 `Polynomial.associated_content_C_mul`：associated_content_C_mul (r : R) (p
 : R[X]) : Associated (C r * p).content (r * p.content)
· 使用定理 `Polynomial.content_eq_zero_iff`：content_eq_zero_iff {p : R[X]} : content
 p = 0 ↔ p = 0
-/
theorem isPrimitive_primPart (p : R[X]) : p.primPart.IsPrimitive := by
  by_cases h : p = 0; · simp [h]
  rw [← content_eq_zero_iff] at h
  rw [isPrimitive_iff_content_eq_one, ← normalize_content, normalize_eq_one]
  refine isUnit_of_associated_mul (.symm ?_) h
  conv_lhs => rw [p.eq_C_content_mul_primPart]
  apply associated_content_C_mul
/-
**Polynomial.content_primPart** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：content_primPart (p : R[X]) : p.primPart.content = 1
参数：p : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.IsPrimitive.content_eq_one`：∀ {R : Type u_1} [inst : CommRing
 R] [inst_1 : NormalizedGCDMonoid R] {p : Polynomial R}, p.IsPrimitive → p.conte
nt = 1
· 使用定理 `Polynomial.isPrimitive_primPart`：isPrimitive_primPart (p : R[X]) : p.pri
mPart.IsPrimitive
-/
theorem content_primPart (p : R[X]) : p.primPart.content = 1 :=
  p.isPrimitive_primPart.content_eq_one
/-
**Polynomial.primPart_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：primPart_ne_zero [Nontrivial R] (p : R[X]) : p.primPart != 0
参数：p : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.IsPrimitive.ne_zero`：∀ {R : Type u_1} [inst : CommSemiring R]
 [Nontrivial R] {p : Polynomial R}, p.IsPrimitive → p ≠ 0
· 使用定理 `Polynomial.isPrimitive_primPart`：isPrimitive_primPart (p : R[X]) : p.pri
mPart.IsPrimitive
-/
theorem primPart_ne_zero [Nontrivial R] (p : R[X]) : p.primPart ≠ 0 :=
  p.isPrimitive_primPart.ne_zero
/-
**Polynomial.natDegree_primPart** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_primPart (p : R[X]) : p.primPart.natDegree = p.natDegree
参数：p : R[X]。
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
· 使用定理 `Polynomial.content_eq_zero_iff`：content_eq_zero_iff {p : R[X]} : content
 p = 0 ↔ p = 0
· 使用定理 `Polynomial.C_eq_zero`：C_eq_zero : C a = 0 ↔ a = 0
· 使用定理 `Polynomial.primPart_zero`：primPart_zero : primPart (0 : R[X]) = 1
· 使用定理 `Polynomial.natDegree_one`：natDegree_one : natDegree (1 : R[X]) = 0
· 使用定理 `Polynomial.eq_C_content_mul_primPart`：eq_C_content_mul_primPart (p : R[X
]) : p = C p.content * p.primPart
· 使用引理 `Polynomial.natDegree_mul`：natDegree_mul (hp : p != 0) (hq : q != 0) : (p
 * q).natDegree = p.natDegree + q.natDegree
· 使用定理 `IsRightCancelMulZero.to_noZeroDivisors`：∀ (M₀ : Type u_1) [inst : MulZer
oClass M₀] [IsRightCancelMulZero M₀], NoZeroDivisors M₀
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `GCDMonoid.toIsCancelMulZero`：∀ {α : Type u_2} {inst : CommMonoidWithZero
 α} [self : GCDMonoid α], IsCancelMulZero α
· 使用定理 `Polynomial.primPart_ne_zero`：primPart_ne_zero [Nontrivial R] (p : R[X]) 
: p.primPart != 0
· 使用定理 `Polynomial.natDegree_C`：natDegree_C (a : R) : natDegree (C a) = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
theorem natDegree_primPart (p : R[X]) : p.primPart.natDegree = p.natDegree := by
  nontriviality R
  by_cases h : C p.content = 0
  · rw [C_eq_zero, content_eq_zero_iff] at h
    simp [h]
  conv_rhs =>
    rw [p.eq_C_content_mul_primPart, natDegree_mul h p.primPart_ne_zero, natDegree_C, zero_add]

@[simp]
/-
**Polynomial.IsPrimitive.primPart_eq** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.IsPri
mitive`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] [inst_1 : NormalizedGCDMonoid R] {p :
 Polynomial R}, p.IsPrimitive → p.primPart = p
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Polynomial.C_1`：C_1 : C (1 : R) = 1
· 使用定理 `Polynomial.IsPrimitive.content_eq_one`：∀ {R : Type u_1} [inst : CommRing
 R] [inst_1 : NormalizedGCDMonoid R] {p : Polynomial R}, p.IsPrimitive → p.conte
nt = 1
· 使用定理 `Polynomial.eq_C_content_mul_primPart`：eq_C_content_mul_primPart (p : R[X
]) : p = C p.content * p.primPart
-/
theorem IsPrimitive.primPart_eq {p : R[X]} (hp : p.IsPrimitive) : p.primPart = p := by
  rw [← one_mul p.primPart, ← C_1, ← hp.content_eq_one, ← p.eq_C_content_mul_primPart]
/-
**Polynomial.isUnit_primPart_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：isUnit_primPart_C (r : R) : IsUnit (C r).primPart
参数：r : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
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
· 使用定理 `Polynomial.primPart_zero`：primPart_zero : primPart (0 : R[X]) = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `Units.inv_mul`：inv_mul : (↑a⁻¹ * a : α) = 1
· 使用定理 `Polynomial.C_1`：C_1 : C (1 : R) = 1
· 使用定理 `Units.mul_inv`：mul_inv : (a * ↑a⁻¹ : α) = 1
· 使用定理 `mul_left_cancel₀`：mul_left_cancel₀ (ha : a != 0) (h : a * b = a * c) : b
 = c
· 使用定理 `Polynomial.instIsLeftCancelMulZeroOfIsCancelAdd`：∀ {R : Type u} [inst : 
Semiring R] [IsCancelAdd R] [IsLeftCancelMulZero R], IsLeftCancelMulZero (Polyno
mial R)
· 使用定理 `AddCancelMonoid.toIsCancelAdd`：∀ (M : Type u) [inst : AddCancelMonoid M]
, IsCancelAdd M
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `GCDMonoid.toIsCancelMulZero`：∀ {α : Type u_2} {inst : CommMonoidWithZero
 α} [self : GCDMonoid α], IsCancelMulZero α
· 使用定理 `Polynomial.C_eq_zero`：C_eq_zero : C a = 0 ↔ a = 0
· 使用定理 `normalize_eq_zero`：normalize_eq_zero {x : α} : normalize x = 0 ↔ x = 0
· 使用定理 `Polynomial.content_C`：content_C {r : R} : (C r).content = normalize r
· 使用定理 `Polynomial.eq_C_content_mul_primPart`：eq_C_content_mul_primPart (p : R[X
]) : p = C p.content * p.primPart
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem isUnit_primPart_C (r : R) : IsUnit (C r).primPart := by
  by_cases h0 : r = 0
  · simp [h0]
  unfold IsUnit
  refine
    ⟨⟨C ↑(normUnit r)⁻¹, C ↑(normUnit r), by rw [← map_mul, Units.inv_mul, C_1], by
        rw [← map_mul, Units.mul_inv, C_1]⟩,
      ?_⟩
  rw [← normalize_eq_zero, ← C_eq_zero] at h0
  apply mul_left_cancel₀ h0
  conv_rhs => rw [← content_C, ← (C r).eq_C_content_mul_primPart]
  simp only [normalize_apply, map_mul]
  rw [mul_assoc, ← map_mul, Units.mul_inv, C_1, mul_one]
/-
**Polynomial.primPart_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：primPart_dvd (p : R[X]) : p.primPart ∣ p
参数：p : R[X]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Dvd.intro_left`：Dvd.intro_left (c : α) (h : c * a = b) : a ∣ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.eq_C_content_mul_primPart`：eq_C_content_mul_primPart (p : R[X
]) : p = C p.content * p.primPart
-/
theorem primPart_dvd (p : R[X]) : p.primPart ∣ p :=
  Dvd.intro_left (C p.content) p.eq_C_content_mul_primPart.symm
/-
**Polynomial.aeval_primPart_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：aeval_primPart_eq_zero {S : Type*} [Ring S] [IsDomain S] [Algebra R S] [Mo
dule.IsTorsionFree R S] {p : R[X]} {s : S} (hpzero : p != 0) (hp : aeval s p = 0
) : aeval s p.primPart = 0
参数：hpzero : p != 0；hp : aeval s p = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_zero_of_ne_zero_of_mul_left_eq_zero`：eq_zero_of_ne_zero_of_mul_left_e
q_zero (hx : x != 0) (hxy : x * y = 0) : y = 0
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Module.nontrivial`：∀ (R : Type u_5) (M : Type u_6) [inst : MonoidWithZer
o R] [Nontrivial M] [inst_2 : Zero M] [MulActionWithZero R M],   Nontrivial R
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `GCDMonoid.toIsCancelMulZero`：∀ {α : Type u_2} {inst : CommMonoidWithZero
 α} [self : GCDMonoid α], IsCancelMulZero α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Injective.ne_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Injective f → ∀ {x y : α} {z : β}, f y = z → (f x ≠ z ↔ x ≠ y)
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `Module.IsTorsionFree.to_faithfulSMul`：∀ {R : Type u_1} {A : Type u_2} [i
nst : CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] [IsCancelMulZero R]  
 [Nontrivial A] [Module.Is…
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Polynomial.content_eq_zero_iff`：content_eq_zero_iff {p : R[X]} : content
 p = 0 ↔ p = 0
· 使用定理 `Polynomial.aeval_C`：aeval_C (r : R) : aeval x (C r) = algebraMap R A r
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `Polynomial.eq_C_content_mul_primPart`：eq_C_content_mul_primPart (p : R[X
]) : p = C p.content * p.primPart
-/
theorem aeval_primPart_eq_zero {S : Type*} [Ring S] [IsDomain S] [Algebra R S]
    [Module.IsTorsionFree R S] {p : R[X]} {s : S} (hpzero : p ≠ 0) (hp : aeval s p = 0) :
    aeval s p.primPart = 0 := by
  nontriviality S
  rw [eq_C_content_mul_primPart p, map_mul, aeval_C] at hp
  refine eq_zero_of_ne_zero_of_mul_left_eq_zero ?_ hp
  have : IsDomain R := { Module.nontrivial R S with }
  rwa [(FaithfulSMul.algebraMap_injective R S).ne_iff' (map_zero _), Ne, content_eq_zero_iff]
/-
**Polynomial.eval** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：eval (x : R) (p : R[X]) : R
参数：x : R；p : R[X]。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval₂_primPart_eq_zero {S : Type*} [CommSemiring S] [IsDomain S] {f : R →+* S}
    (hinj : Function.Injective f) {p : R[X]} {s : S} (hpzero : p ≠ 0) (hp : eval₂ f s p = 0) :
    eval₂ f s p.primPart = 0 := by
  rw [eq_C_content_mul_primPart p, eval₂_mul, eval₂_C] at hp
  refine eq_zero_of_ne_zero_of_mul_left_eq_zero ?_ hp
  rwa [hinj.ne_iff' (map_zero _), Ne, content_eq_zero_iff]

end PrimPart

/-
**Polynomial.gcd_content_eq_of_dvd_sub** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：gcd_content_eq_of_dvd_sub {a : R} {p q : R[X]} (h : C a ∣ p - q) : gcd a p
.content = gcd a q.content
参数：h : C a ∣ p - q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.content_eq_gcd_range_of_lt`：content_eq_gcd_range_of_lt (p : R
[X]) (n : Nat) (h : p.natDegree < n) : p.content = (Finset.range n).gcd p.coeff
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用定理 `Nat.lt_succ_self`：∀ (n : ℕ), n < n.succ
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
· 使用定理 `Finset.gcd_eq_of_dvd_sub`：gcd_eq_of_dvd_sub {s : Finset β} {f g : β -> α
} {a : α} (h : forall x : β, x in s -> a ∣ f x - g x) : GCDMonoid.gcd a (s.gcd f
) = GCDMonoid.…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.coeff_sub`：coeff_sub (p q : R[X]) (n : Nat) : coeff (p - q) n
 = coeff p n - coeff q n
· 使用定理 `Polynomial.coeff_C_mul`：coeff_C_mul (p : R[X]) : coeff (C a * p) n = a *
 coeff p n
-/
theorem gcd_content_eq_of_dvd_sub {a : R} {p q : R[X]} (h : C a ∣ p - q) :
    gcd a p.content = gcd a q.content := by
  rw [content_eq_gcd_range_of_lt p (max p.natDegree q.natDegree).succ
      (lt_of_le_of_lt (le_max_left _ _) (Nat.lt_succ_self _))]
  rw [content_eq_gcd_range_of_lt q (max p.natDegree q.natDegree).succ
      (lt_of_le_of_lt (le_max_right _ _) (Nat.lt_succ_self _))]
  apply Finset.gcd_eq_of_dvd_sub
  intro x _
  obtain ⟨w, hw⟩ := h
  use w.coeff x
  rw [← coeff_sub, hw, coeff_C_mul]
/-
**Polynomial.content_mul_aux** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：content_mul_aux {p q : R[X]} : gcd (p * q).eraseLead.content p.leadingCoef
f = gcd (p.eraseLead * q).content p.leadingCoeff
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `gcd_comm`：gcd_comm [NormalizedGCDMonoid α] (a b : α) : gcd a b = gcd b a
· 使用定理 `Polynomial.gcd_content_eq_of_dvd_sub`：gcd_content_eq_of_dvd_sub {a : R} 
{p q : R[X]} (h : C a ∣ p - q) : gcd a p.content = gcd a q.content
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.self_sub_C_mul_X_pow`：self_sub_C_mul_X_pow {R : Type*} [Ring 
R] (f : R[X]) : f - C f.leadingCoeff * X ^ f.natDegree = f.eraseLead
· 使用定理 `sub_mul`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), (a
 - b) * c = a * c - b * c
· 使用定理 `sub_sub`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b c : α), 
a - b - c = a - (b + c)
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `sub_add`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b c : α), 
a - b + c = a - (b - c)
· 使用定理 `sub_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a - 
(a - b) = b
· 使用引理 `Polynomial.leadingCoeff_mul`：leadingCoeff_mul (p q : R[X]) : leadingCoef
f (p * q) = leadingCoeff p * leadingCoeff q
· 使用定理 `IsRightCancelMulZero.to_noZeroDivisors`：∀ (M₀ : Type u_1) [inst : MulZer
oClass M₀] [IsRightCancelMulZero M₀], NoZeroDivisors M₀
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `GCDMonoid.toIsCancelMulZero`：∀ {α : Type u_2} {inst : CommMonoidWithZero
 α} [self : GCDMonoid α], IsCancelMulZero α
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `dvd_sub`：dvd_sub (h₁ : a ∣ b) (h₂ : a ∣ c) : a ∣ b - c
· 使用定理 `Dvd.intro`：Dvd.intro (c : α) (h : a * c = b) : a ∣ b
-/
theorem content_mul_aux {p q : R[X]} :
    gcd (p * q).eraseLead.content p.leadingCoeff =
      gcd (p.eraseLead * q).content p.leadingCoeff := by
  rw [gcd_comm (content _) _, gcd_comm (content _) _]
  apply gcd_content_eq_of_dvd_sub
  rw [← self_sub_C_mul_X_pow, ← self_sub_C_mul_X_pow, sub_mul, sub_sub, add_comm, sub_add,
    sub_sub_cancel, leadingCoeff_mul, map_mul, mul_assoc, mul_assoc]
  apply dvd_sub (Dvd.intro _ rfl) (Dvd.intro _ rfl)
/-
**Polynomial.associated_content_mul** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：associated_content_mul (p q : R[X]) : Associated ((p * q).content) (p.cont
ent * q.content)
参数：p q : R[X]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_eq_zero`：mul_eq_zero : a * b = 0 ↔ a = 0 ∨ b = 0
· 使用定理 `Polynomial.instNoZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [NoZer
oDivisors R], NoZeroDivisors (Polynomial R)
· 使用定理 `IsRightCancelMulZero.to_noZeroDivisors`：∀ (M₀ : Type u_1) [inst : MulZer
oClass M₀] [IsRightCancelMulZero M₀], NoZeroDivisors M₀
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `GCDMonoid.toIsCancelMulZero`：∀ {α : Type u_2} {inst : CommMonoidWithZero
 α} [self : GCDMonoid α], IsCancelMulZero α
· 使用定理 `Polynomial.degree_eq_bot`：degree_eq_bot : degree p = ⊥ ↔ p = 0
· 使用定理 `Nat.WithBot.lt_zero_iff`：lt_zero_iff {n : WithBot Nat} : n < 0 ↔ n = ⊥
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Polynomial.content_zero`：content_zero : content (0 : R[X]) = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用引理 `Polynomial.natDegree_mul`：natDegree_mul (hp : p != 0) (hq : q != 0) : (p
 * q).natDegree = p.natDegree + q.natDegree
· 使用定理 `Polynomial.degree_eq_natDegree`：degree_eq_natDegree (hp : p != 0) : degr
ee p = (natDegree p : WithBot Nat)
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `Nat.cast_lt`：cast_lt : (m : α) < n ↔ m < n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Nat.lt_succ_iff_lt_or_eq`：∀ {m n : ℕ}, m < n.succ ↔ m < n ∨ m = n
· 使用定理 `Polynomial.eq_C_content_mul_primPart`：eq_C_content_mul_primPart (p : R[X
]) : p = C p.content * p.primPart
· 使用定理 `Polynomial.normalize_content`：normalize_content {p : R[X]} : normalize p
.content = p.content
· 使用定理 `normalize_eq_one`：normalize_eq_one {x : α} : normalize x = 1 ↔ IsUnit x 
where mp hx
· 使用定理 `isUnit_iff_dvd_one`：isUnit_iff_dvd_one {x : α} : IsUnit x ↔ x ∣ 1
· 使用定理 `Polynomial.content_eq_gcd_leadingCoeff_content_eraseLead`：content_eq_gcd
_leadingCoeff_content_eraseLead (p : R[X]) : p.content = gcd p.leadingCoeff (era
seLead p).content
· 使用引理 `Polynomial.leadingCoeff_mul`：leadingCoeff_mul (p q : R[X]) : leadingCoef
f (p * q) = leadingCoeff p * leadingCoeff q
（共 72 条，此处仅展示前 30 条）
-/
theorem associated_content_mul (p q : R[X]) :
    Associated ((p * q).content) (p.content * q.content) := by
  nontriviality R
  classical
    suffices h : ∀ (n : ℕ) (p q : R[X]),
        (p * q).degree < n → Associated ((p * q).content) (p.content * q.content) by
      apply h
      apply lt_of_le_of_lt degree_le_natDegree (WithBot.coe_lt_coe.2 (Nat.lt_succ_self _))
    intro n p q hpq
    induction n generalizing p q with
    | zero =>
      rw [Nat.cast_zero, Nat.WithBot.lt_zero_iff, degree_eq_bot, mul_eq_zero] at hpq
      rcases hpq with (rfl | rfl) <;> simp
    | succ n ih => ?_
    by_cases p0 : p = 0
    · simp [p0]
    by_cases q0 : q = 0
    · simp [q0]
    rw [degree_eq_natDegree (mul_ne_zero p0 q0), Nat.cast_lt,
      Nat.lt_succ_iff_lt_or_eq, ← Nat.cast_lt (α := WithBot ℕ),
      ← degree_eq_natDegree (mul_ne_zero p0 q0), natDegree_mul p0 q0] at hpq
    rcases hpq with (hlt | heq)
    · apply ih _ _ hlt
    rw [← p.natDegree_primPart, ← q.natDegree_primPart, ← Nat.cast_inj (R := WithBot ℕ),
      Nat.cast_add, ← degree_eq_natDegree p.primPart_ne_zero,
      ← degree_eq_natDegree q.primPart_ne_zero] at heq
    rw [p.eq_C_content_mul_primPart, q.eq_C_content_mul_primPart]
    suffices h : (q.primPart * p.primPart).content = 1 by
      grw [mul_assoc, associated_content_C_mul, associated_content_C_mul, mul_comm p.primPart,
        mul_assoc, associated_content_C_mul, associated_content_C_mul, h, mul_one,
        content_primPart, content_primPart, mul_one, mul_one]
    rw [← normalize_content, normalize_eq_one, isUnit_iff_dvd_one,
      content_eq_gcd_leadingCoeff_content_eraseLead, leadingCoeff_mul, gcd_comm]
    apply (gcd_mul_dvd_mul_gcd _ _ _).trans
    rw [content_mul_aux, (ih ..).gcd_eq_left, content_primPart, mul_one, gcd_comm, ←
      content_eq_gcd_leadingCoeff_content_eraseLead, content_primPart, one_mul,
      mul_comm q.primPart, content_mul_aux, (ih ..).gcd_eq_left, content_primPart, mul_one,
      gcd_comm, ← content_eq_gcd_leadingCoeff_content_eraseLead, content_primPart]
    · rw [← heq, degree_mul, WithBot.add_lt_add_iff_right]
      · apply degree_erase_lt p.primPart_ne_zero
      · rw [Ne, degree_eq_bot]
        apply q.primPart_ne_zero
    · rw [mul_comm, ← heq, degree_mul, WithBot.add_lt_add_iff_left]
      · apply degree_erase_lt q.primPart_ne_zero
      · rw [Ne, degree_eq_bot]
        apply p.primPart_ne_zero

@[simp]
/-
**Polynomial.content_mul** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：content_mul {R} [CommRing R] [StrongNormalizedGCDMonoid R] {p q : R[X]} : 
(p * q).content = p.content * q.content
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Associated.eq_of_normalized`：Associated.eq_of_normalized {a b : α} (h : 
Associated a b) (ha : normalize a = a) (hb : normalize b = b) : a = b
· 使用定理 `Polynomial.associated_content_mul`：associated_content_mul (p q : R[X]) :
 Associated ((p * q).content) (p.content * q.content)
· 使用定理 `Polynomial.normalize_content`：normalize_content {p : R[X]} : normalize p
.content = p.content
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `normalize_mul`：∀ {α : Type u_1} [inst : CommMonoidWithZero α] [inst_1 : 
StrongNormalizationMonoid α] (x y : α),   normalize (x * y) = normalize x * norm
ali…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem content_mul {R} [CommRing R] [StrongNormalizedGCDMonoid R] {p q : R[X]} :
    (p * q).content = p.content * q.content :=
  (associated_content_mul ..).eq_of_normalized normalize_content <| by simp [normalize_content]
/-
**Polynomial.IsPrimitive.mul** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.IsPrimitive`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] [NormalizedGCDMonoid R] {p q : Polyno
mial R},   p.IsPrimitive → q.IsPrimitive → (p * q).IsPrimitive
参数：p * q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.isPrimitive_iff_content_eq_one`：isPrimitive_iff_content_eq_on
e {p : R[X]} : p.IsPrimitive ↔ p.content = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.normalize_content`：normalize_content {p : R[X]} : normalize p
.content = p.content
· 使用定理 `normalize_eq_one`：normalize_eq_one {x : α} : normalize x = 1 ↔ IsUnit x 
where mp hx
· 使用定理 `Associated.isUnit`：∀ {M : Type u_1} [inst : Monoid M] {a b : M}, Associa
ted a b → IsUnit a → IsUnit b
· 使用定理 `Associated.symm`：∀ {M : Type u_1} [inst : Monoid M] {x y : M}, Associate
d x y → Associated y x
· 使用定理 `Polynomial.associated_content_mul`：associated_content_mul (p q : R[X]) :
 Associated ((p * q).content) (p.content * q.content)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.IsPrimitive.content_eq_one`：∀ {R : Type u_1} [inst : CommRing
 R] [inst_1 : NormalizedGCDMonoid R] {p : Polynomial R}, p.IsPrimitive → p.conte
nt = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
theorem IsPrimitive.mul {p q : R[X]} (hp : p.IsPrimitive) (hq : q.IsPrimitive) :
    (p * q).IsPrimitive := by
  rw [isPrimitive_iff_content_eq_one, ← normalize_content, normalize_eq_one]
  refine (associated_content_mul p q).symm.isUnit ?_
  simp_rw [hp.content_eq_one, hq.content_eq_one, mul_one, isUnit_one]
/-
**Polynomial.associated_primPart_mul** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：associated_primPart_mul {p q : R[X]} (h0 : p * q != 0) : Associated (p * q
).primPart (p.primPart * q.primPart)
参数：h0 : p * q != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Associated.of_mul_left`：Associated.of_mul_left [CommMonoidWithZero M] [I
sCancelMulZero M] {a b c d : M} (h : a * b ~ᵤ c * d) (h₁ : a ~ᵤ c) (ha : a != 0)
 : b ~ᵤ d
· 使用定理 `Polynomial.instIsCancelMulZeroOfIsCancelAdd`：∀ {R : Type u} [inst : Semi
ring R] [IsCancelAdd R] [IsCancelMulZero R], IsCancelMulZero (Polynomial R)
· 使用定理 `AddCancelMonoid.toIsCancelAdd`：∀ (M : Type u) [inst : AddCancelMonoid M]
, IsCancelAdd M
· 使用定理 `GCDMonoid.toIsCancelMulZero`：∀ {α : Type u_2} {inst : CommMonoidWithZero
 α} [self : GCDMonoid α], IsCancelMulZero α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.eq_C_content_mul_primPart`：eq_C_content_mul_primPart (p : R[X
]) : p = C p.content * p.primPart
· 使用定理 `mul_mul_mul_comm`：mul_mul_mul_comm (a b c d : G) : a * b * (c * d) = a *
 c * (b * d)
· 使用定理 `Polynomial.C_mul`：C_mul : C (a * b) = C a * C b
· 使用定理 `Associated.mul_right`：Associated.mul_right [CommMonoid M] {a b : M} (h :
 a ~ᵤ b) (c : M) : a * c ~ᵤ b * c
· 使用定理 `Associated.map`：map {M N : Type*} [Monoid M] [Monoid N] {F : Type*} [Fun
Like F M N] [MonoidHomClass F M N] (f : F) {x y : M} (ha : Associated x y) : Ass
ocia…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Associated.symm`：∀ {M : Type u_1} [inst : Monoid M] {x y : M}, Associate
d x y → Associated y x
· 使用定理 `Polynomial.associated_content_mul`：associated_content_mul (p q : R[X]) :
 Associated ((p * q).content) (p.content * q.content)
· 使用定理 `Associated.rfl`：∀ {M : Type u_1} [inst : Monoid M] {x : M}, Associated x
 x
· 使用定理 `Polynomial.C_eq_zero`：C_eq_zero : C a = 0 ↔ a = 0
· 使用定理 `Polynomial.content_eq_zero_iff`：content_eq_zero_iff {p : R[X]} : content
 p = 0 ↔ p = 0
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
-/
theorem associated_primPart_mul {p q : R[X]} (h0 : p * q ≠ 0) :
    Associated (p * q).primPart (p.primPart * q.primPart) := by
  rw [Ne, ← content_eq_zero_iff, ← C_eq_zero] at h0
  refine .of_mul_left ?_ .rfl h0
  conv_lhs => rw [← (p * q).eq_C_content_mul_primPart,
    p.eq_C_content_mul_primPart, q.eq_C_content_mul_primPart, mul_mul_mul_comm, ← C_mul]
  gcongr
  exact (associated_content_mul ..).symm.map _

@[simp]
/-
**Polynomial.primPart_mul** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：primPart_mul {R} [CommRing R] [StrongNormalizedGCDMonoid R] {p q : R[X]} (
h0 : p * q != 0) : (p * q).primPart = p.primPart * q.primPart
参数：h0 : p * q != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_left_cancel₀`：mul_left_cancel₀ (ha : a != 0) (h : a * b = a * c) : b
 = c
· 使用定理 `Polynomial.instIsLeftCancelMulZeroOfIsCancelAdd`：∀ {R : Type u} [inst : 
Semiring R] [IsCancelAdd R] [IsLeftCancelMulZero R], IsLeftCancelMulZero (Polyno
mial R)
· 使用定理 `AddCancelMonoid.toIsCancelAdd`：∀ (M : Type u) [inst : AddCancelMonoid M]
, IsCancelAdd M
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `GCDMonoid.toIsCancelMulZero`：∀ {α : Type u_2} {inst : CommMonoidWithZero
 α} [self : GCDMonoid α], IsCancelMulZero α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.C_eq_zero`：C_eq_zero : C a = 0 ↔ a = 0
· 使用定理 `Polynomial.content_eq_zero_iff`：content_eq_zero_iff {p : R[X]} : content
 p = 0 ↔ p = 0
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.eq_C_content_mul_primPart`：eq_C_content_mul_primPart (p : R[X
]) : p = C p.content * p.primPart
· 使用定理 `Polynomial.content_mul`：content_mul {R} [CommRing R] [StrongNormalizedGC
DMonoid R] {p q : R[X]} : (p * q).content = p.content * q.content
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
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
-/
theorem primPart_mul {R} [CommRing R] [StrongNormalizedGCDMonoid R] {p q : R[X]} (h0 : p * q ≠ 0) :
    (p * q).primPart = p.primPart * q.primPart := by
  rw [Ne, ← content_eq_zero_iff, ← C_eq_zero] at h0
  apply mul_left_cancel₀ h0
  conv_lhs =>
    rw [← (p * q).eq_C_content_mul_primPart, p.eq_C_content_mul_primPart,
      q.eq_C_content_mul_primPart]
  rw [content_mul, map_mul]
  ring
/-
**Polynomial.IsPrimitive.dvd_primPart_iff_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Polynom
ial.IsPrimitive`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] [inst_1 : NormalizedGCDMonoid R] {p q
 : Polynomial R},   p.IsPrimitive → q ≠ 0 → (p ∣ q.primPart ↔ p ∣ q)
参数：p ∣ q.primPart ↔ p ∣ q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Dvd.dvd.trans`：∀ {α : Type u_1} [inst : Semigroup α] {a b c : α}, a ∣ b 
→ b ∣ c → a ∣ c
· 使用定理 `Dvd.intro_left`：Dvd.intro_left (c : α) (h : c * a = b) : a ∣ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.eq_C_content_mul_primPart`：eq_C_content_mul_primPart (p : R[X
]) : p = C p.content * p.primPart
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.IsPrimitive.primPart_eq`：∀ {R : Type u_1} [inst : CommRing R]
 [inst_1 : NormalizedGCDMonoid R] {p : Polynomial R}, p.IsPrimitive → p.primPart
 = p
· 使用定理 `Associated.dvd`：∀ {M : Type u_1} [inst : Monoid M] {a b : M}, Associated
 a b → a ∣ b
· 使用定理 `Associated.symm`：∀ {M : Type u_1} [inst : Monoid M] {x y : M}, Associate
d x y → Associated y x
· 使用定理 `Polynomial.associated_primPart_mul`：associated_primPart_mul {p q : R[X]}
 (h0 : p * q != 0) : Associated (p * q).primPart (p.primPart * q.primPart)
-/
theorem IsPrimitive.dvd_primPart_iff_dvd {p q : R[X]} (hp : p.IsPrimitive) (hq : q ≠ 0) :
    p ∣ q.primPart ↔ p ∣ q := by
  refine ⟨fun h => h.trans (Dvd.intro_left _ q.eq_C_content_mul_primPart.symm), fun h => ?_⟩
  rcases h with ⟨r, rfl⟩
  exact .trans (by simp [hp.primPart_eq]) (associated_primPart_mul hq).symm.dvd
/-
**Polynomial.exists_primitive_lcm_of_isPrimitive** 是 Mathlib 中的一个定理，位于命名空间 `Poly
nomial`。
形式化陈述：exists_primitive_lcm_of_isPrimitive {p q : R[X]} (hp : p.IsPrimitive) (hq 
: q.IsPrimitive) : exists r : R[X], r.IsPrimitive ∧ forall s : R[X], p ∣ s ∧ q ∣
 s ↔ r ∣ s
参数：hp : p.IsPrimitive；hq : q.IsPrimitive。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.IsPrimitive.mul`：∀ {R : Type u_1} [inst : CommRing R] [Normal
izedGCDMonoid R] {p q : Polynomial R},   p.IsPrimitive → q.IsPrimitive → (p * q)
.IsPrimitive
· 使用定理 `dvd_mul_right`：dvd_mul_right (a b : α) : a ∣ a * b
· 使用定理 `dvd_mul_left`：dvd_mul_left (a b : α) : a ∣ b * a
· 使用定理 `Nat.find_spec`：∀ {p : ℕ → Prop} [inst : DecidablePred p] (H : ∃ n, p n),
 p (Nat.find H)
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.find_min'`：∀ {p : ℕ → Prop} [inst : DecidablePred p] (H : ∃ n, p n) 
{m : ℕ}, p m → Nat.find H ≤ m
· 使用定理 `Polynomial.natDegree_primPart`：natDegree_primPart (p : R[X]) : p.primPar
t.natDegree = p.natDegree
· 使用定理 `Polynomial.isPrimitive_primPart`：isPrimitive_primPart (p : R[X]) : p.pri
mPart.IsPrimitive
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.IsPrimitive.dvd_primPart_iff_dvd`：∀ {R : Type u_1} [inst : Co
mmRing R] [inst_1 : NormalizedGCDMonoid R] {p q : Polynomial R},   p.IsPrimitive
 → q ≠ 0 → (p ∣ q.primPart ↔ p ∣ …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.dvd_content_iff_C_dvd`：dvd_content_iff_C_dvd {p : R[X]} {r : 
R} : r ∣ p.content ↔ C r ∣ p
· 使用定理 `Polynomial.eq_C_of_natDegree_le_zero`：eq_C_of_natDegree_le_zero (h : nat
Degree p <= 0) : p = C (coeff p 0)
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `IsUnit.dvd`：dvd (hu : IsUnit u) : u ∣ a
· 使用定理 `normalize_eq_one`：normalize_eq_one {x : α} : normalize x = 1 ↔ IsUnit x 
where mp hx
· 使用定理 `Polynomial.content_C`：content_C {r : R} : (C r).content = normalize r
· 使用定理 `Polynomial.isPrimitive_iff_content_eq_one`：isPrimitive_iff_content_eq_on
e {p : R[X]} : p.IsPrimitive ↔ p.content = 1
· 使用定理 `Polynomial.natDegree_cancelLeads_lt_of_natDegree_le_natDegree`：natDegree
_cancelLeads_lt_of_natDegree_le_natDegree (h : p.natDegree <= q.natDegree) (hq :
 0 < q.natDegree) : (p.cancelLeads q).natDegree < q…
· 使用定理 `Nat.find_min`：∀ {p : ℕ → Prop} [inst : DecidablePred p] (H : ∃ n, p n) {
m : ℕ}, m < Nat.find H → ¬p m
· 使用定理 `Polynomial.dvd_cancelLeads_of_dvd_of_dvd`：dvd_cancelLeads_of_dvd_of_dvd 
{r : R[X]} (pq : p ∣ q) (pr : p ∣ r) : p ∣ q.cancelLeads r
· 使用定理 `dvd_add`：dvd_add [LeftDistribClass α] {a b c : α} (h₁ : a ∣ b) (h₂ : a ∣
 c) : a ∣ b + c
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
（共 54 条，此处仅展示前 30 条）
-/
theorem exists_primitive_lcm_of_isPrimitive {p q : R[X]} (hp : p.IsPrimitive) (hq : q.IsPrimitive) :
    ∃ r : R[X], r.IsPrimitive ∧ ∀ s : R[X], p ∣ s ∧ q ∣ s ↔ r ∣ s := by
  classical
    have h : ∃ (n : ℕ) (r : R[X]), r.natDegree = n ∧ r.IsPrimitive ∧ p ∣ r ∧ q ∣ r :=
      ⟨(p * q).natDegree, p * q, rfl, hp.mul hq, dvd_mul_right _ _, dvd_mul_left _ _⟩
    rcases Nat.find_spec h with ⟨r, rdeg, rprim, pr, qr⟩
    refine ⟨r, rprim, fun s => ⟨?_, fun rs => ⟨pr.trans rs, qr.trans rs⟩⟩⟩
    suffices hs : ∀ (n : ℕ) (s : R[X]), s.natDegree = n → p ∣ s ∧ q ∣ s → r ∣ s from
      hs s.natDegree s rfl
    clear s
    by_contra! con
    rcases Nat.find_spec con with ⟨s, sdeg, ⟨ps, qs⟩, rs⟩
    have s0 : s ≠ 0 := by
      contrapose rs
      simp [rs]
    have hs :=
      Nat.find_min' h
        ⟨_, s.natDegree_primPart, s.isPrimitive_primPart, (hp.dvd_primPart_iff_dvd s0).2 ps,
          (hq.dvd_primPart_iff_dvd s0).2 qs⟩
    rw [← rdeg] at hs
    by_cases! sC : s.natDegree ≤ 0
    · rw [eq_C_of_natDegree_le_zero (le_trans hs sC), isPrimitive_iff_content_eq_one, content_C,
        normalize_eq_one] at rprim
      rw [eq_C_of_natDegree_le_zero (le_trans hs sC), ← dvd_content_iff_C_dvd] at rs
      apply rs rprim.dvd
    have hcancel := natDegree_cancelLeads_lt_of_natDegree_le_natDegree hs sC
    rw [sdeg] at hcancel
    apply Nat.find_min con hcancel
    refine
      ⟨_, rfl, ⟨dvd_cancelLeads_of_dvd_of_dvd pr ps, dvd_cancelLeads_of_dvd_of_dvd qr qs⟩,
        fun rcs => rs ?_⟩
    rw [← rprim.dvd_primPart_iff_dvd s0]
    rw [cancelLeads, tsub_eq_zero_iff_le.mpr hs, pow_zero, mul_one] at rcs
    have h :=
      dvd_add rcs (Dvd.intro_left (C (leadingCoeff s) * X ^ (natDegree s - natDegree r)) rfl)
    nontriviality R
    have hC0 := rprim.ne_zero
    rw [Ne, ← leadingCoeff_eq_zero, ← C_eq_zero] at hC0
    rw [sub_add_cancel, ← rprim.dvd_primPart_iff_dvd (mul_ne_zero hC0 s0)] at h
    refine h.trans (Associated.dvd ?_)
    grw [associated_primPart_mul (mul_ne_zero hC0 s0)]
    exact associated_unit_mul_left _ _ (isUnit_primPart_C _)
/-
**Polynomial.dvd_iff_content_dvd_content_and_primPart_dvd_primPart** 是 Mathlib 中
的一个定理，位于命名空间 `Polynomial`。
形式化陈述：dvd_iff_content_dvd_content_and_primPart_dvd_primPart {p q : R[X]} (hq : q
 != 0) : p ∣ q ↔ p.content ∣ q.content ∧ p.primPart ∣ q.primPart
参数：hq : q != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Associated.dvd_iff_dvd_right`：Associated.dvd_iff_dvd_right [Monoid M] {a
 b c : M} (h : b ~ᵤ c) : a ∣ b ↔ a ∣ c
· 使用定理 `Polynomial.associated_content_mul`：associated_content_mul (p q : R[X]) :
 Associated ((p * q).content) (p.content * q.content)
· 使用定理 `Polynomial.IsPrimitive.dvd_primPart_iff_dvd`：∀ {R : Type u_1} [inst : Co
mmRing R] [inst_1 : NormalizedGCDMonoid R] {p q : Polynomial R},   p.IsPrimitive
 → q ≠ 0 → (p ∣ q.primPart ↔ p ∣ …
· 使用定理 `Polynomial.isPrimitive_primPart`：isPrimitive_primPart (p : R[X]) : p.pri
mPart.IsPrimitive
· 使用定理 `dvd_mul_right`：dvd_mul_right (a b : α) : a ∣ a * b
· 使用定理 `dvd_mul_of_dvd_left`：dvd_mul_of_dvd_left (h : a ∣ b) (c : α) : a ∣ b * c
· 使用定理 `Polynomial.primPart_dvd`：primPart_dvd (p : R[X]) : p.primPart ∣ p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.eq_C_content_mul_primPart`：eq_C_content_mul_primPart (p : R[X
]) : p = C p.content * p.primPart
· 使用定理 `mul_dvd_mul`：∀ {α : Type u_1} [inst : CommSemigroup α] {a b c d : α}, a 
∣ b → c ∣ d → a * c ∣ b * d
· 使用定理 `map_dvd`：∀ {M : Type u_1} {N : Type u_2} [inst : Semigroup M] [inst_1 : 
Semigroup N] {F : Type u_3} [inst_2 : FunLike F M N]   [MulHomClass F M N] (f…
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
-/
theorem dvd_iff_content_dvd_content_and_primPart_dvd_primPart {p q : R[X]} (hq : q ≠ 0) :
    p ∣ q ↔ p.content ∣ q.content ∧ p.primPart ∣ q.primPart := by
  constructor
  · rintro ⟨r, rfl⟩
    rw [(associated_content_mul ..).dvd_iff_dvd_right,
      p.isPrimitive_primPart.dvd_primPart_iff_dvd hq]
    exact ⟨dvd_mul_right .., dvd_mul_of_dvd_left p.primPart_dvd _⟩
  · rintro ⟨h₁, h₂⟩
    rw [p.eq_C_content_mul_primPart, q.eq_C_content_mul_primPart]
    gcongr
/-
**Polynomial.normalizedGcdMonoid** 是 Mathlib 中的一个实例，位于命名空间 `Polynomial`。
形式化陈述：normalizedGcdMonoid : NormalizedGCDMonoid R[X]
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance normalizedGcdMonoid : NormalizedGCDMonoid R[X] :=
  letI := Classical.decEq R
  normalizedGCDMonoidOfExistsLCM fun p q => by
    rcases exists_primitive_lcm_of_isPrimitive p.isPrimitive_primPart
        q.isPrimitive_primPart with
      ⟨r, rprim, hr⟩
    refine ⟨C (lcm p.content q.content) * r, fun s => ?_⟩
    by_cases hs : s = 0
    · simp [hs]
    by_cases hpq : C (lcm p.content q.content) = 0
    · rw [C_eq_zero, lcm_eq_zero_iff, content_eq_zero_iff, content_eq_zero_iff] at hpq
      rcases hpq with (hpq | hpq) <;> simp [hpq, hs]
    iterate 3 rw [dvd_iff_content_dvd_content_and_primPart_dvd_primPart hs]
    nontriviality R
    rw [(associated_content_mul ..).dvd_iff_dvd_left, rprim.content_eq_one, mul_one, content_C,
      (associated_primPart_mul (mul_ne_zero hpq rprim.ne_zero)).dvd_iff_dvd_left, rprim.primPart_eq,
      normalize_lcm, lcm_dvd_iff,
      (isUnit_primPart_C (lcm p.content q.content)).mul_left_dvd, ← hr s.primPart]
    tauto
/-
**Polynomial.degree_gcd_le_left** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degree_gcd_le_left {p : R[X]} (hp : p != 0) (q) : (gcd p q).degree <= p.de
gree
参数：hp : p != 0；q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.natDegree_le_iff_degree_le`：natDegree_le_iff_degree_le {n : N
at} : natDegree p <= n ↔ degree p <= n
· 使用引理 `Polynomial.natDegree_le_of_dvd`：natDegree_le_of_dvd (h1 : p ∣ q) (h2 : q
 != 0) : p.natDegree <= q.natDegree
· 使用定理 `IsRightCancelMulZero.to_noZeroDivisors`：∀ (M₀ : Type u_1) [inst : MulZer
oClass M₀] [IsRightCancelMulZero M₀], NoZeroDivisors M₀
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `GCDMonoid.toIsCancelMulZero`：∀ {α : Type u_2} {inst : CommMonoidWithZero
 α} [self : GCDMonoid α], IsCancelMulZero α
· 使用定理 `GCDMonoid.gcd_dvd_left`：∀ {α : Type u_2} {inst : CommMonoidWithZero α} [
self : GCDMonoid α] (a b : α), gcd a b ∣ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.degree_eq_natDegree`：degree_eq_natDegree (hp : p != 0) : degr
ee p = (natDegree p : WithBot Nat)
-/
theorem degree_gcd_le_left {p : R[X]} (hp : p ≠ 0) (q) : (gcd p q).degree ≤ p.degree := by
  have := natDegree_le_iff_degree_le.mp (natDegree_le_of_dvd (gcd_dvd_left p q) hp)
  rwa [degree_eq_natDegree hp]
/-
**Polynomial.degree_gcd_le_right** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degree_gcd_le_right (p) {q : R[X]} (hq : q != 0) : (gcd p q).degree <= q.d
egree
参数：p；hq : q != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `gcd_comm`：gcd_comm [NormalizedGCDMonoid α] (a b : α) : gcd a b = gcd b a
· 使用定理 `Polynomial.degree_gcd_le_left`：degree_gcd_le_left {p : R[X]} (hp : p != 
0) (q) : (gcd p q).degree <= p.degree
-/
theorem degree_gcd_le_right (p) {q : R[X]} (hq : q ≠ 0) : (gcd p q).degree ≤ q.degree := by
  rw [gcd_comm]
  exact degree_gcd_le_left hq p

end NormalizedGCDMonoid

/-
**Polynomial.** 是 Mathlib 中的一个实例，位于命名空间 `Polynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance [StrongNormalizedGCDMonoid R] : StrongNormalizedGCDMonoid R[X] where
  __ : NormalizedGCDMonoid R[X] := inferInstance
  __ : StrongNormalizationMonoid R[X] := inferInstance

-- We do not add a `GCDMonoid R[X]` instance due to diamond
/-
**Polynomial.** 是 Mathlib 中的一个实例，位于命名空间 `Polynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsGCDMonoid R] : IsGCDMonoid R[X] :=
  have := Classical.arbitrary (NormalizedGCDMonoid R); inferInstance

end Polynomial

