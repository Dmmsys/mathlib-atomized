/-
Copyright (c) 2025 Michal Staromiejski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Staromiejski
-/
module

public import Mathlib.FieldTheory.PurelyInseparable.Basic

/-!

# The exponent of purely inseparable extensions

This file defines the exponent of a purely inseparable extension (if one exists) and
some related results.

Most results are stated using `ringExpChar K` rather than using `[ExpChar K p]` parameter because
it gives cleaner API. To use the results in a context with `[ExpChar K p]`, consider using
`ringExpChar.eq K p` for substitution.

## Main definitions

- `IsPurelyInseparable.HasExponent`: typeclass to assert a purely inseparable field extension
  `L / K` has an exponent, that is a smallest natural number `e` such that
  `a ^ ringExpChar K ^ e ∈ K` for all `a ∈ L`.
- `IsPurelyInseparable.exponent`: the exponent of a purely inseparable field extension.
- `IsPurelyInseparable.elemExponent`: the exponent of an element of a purely inseparable
  field extension, that is the smallest natural number `e` such that `a ^ ringExpChar K ^ e ∈ K`.
- `IsPurelyInseparable.iterateFrobenius`: the iterated Frobenius map (ring homomorphism) `L →+* K`
  for purely inseparable field extension `L / K` with exponent; for `n ≥ exponent K L`, it acts like
  `x ↦ x ^ p ^ n` but the codomain is the base field `K`.
- `IsPurelyInseparable.iterateFrobeniusₛₗ`: version of `iterateFrobenius` as a semilinear map over
  a subfield `F` of `K`, w.r.t. the iterated Frobenius homomorphism on `F`.

## Tags

purely inseparable

-/

@[expose] public section

namespace IsPurelyInseparable

variable (F K L : Type*)

section Ring

variable [CommRing K] [Ring L] [Algebra K L]

/-- A predicate class on a ring extension saying that there is a natural number `e`
such that `a ^ ringExpChar K ^ e ∈ K` for all `a ∈ L`. -/
@[mk_iff]
/-
**IsPurelyInseparable.HasExponent** 是 Mathlib 中的一个归纳类型，位于命名空间 `IsPurelyInseparab
le`。
形式化陈述：(K : Type u_2) → (L : Type u_3) → [inst : CommRing K] → [inst_1 : Ring L] 
→ [Algebra K L] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A predicate class on a ring extension saying that there is a natural number `e`
such that `a ^ ringExpChar K ^ e ∈ K` for all `a ∈ L`.
-/
class HasExponent : Prop where
  has_exponent : ∃ e, ∀ a, a ^ ringExpChar K ^ e ∈ (algebraMap K L).range

/-- Version of `hasExponent_iff` using `ExpChar`. -/
/-
**IsPurelyInseparable.hasExponent_iff'** 是 Mathlib 中的一个定理，位于命名空间 `IsPurelyInsepa
rable`。
形式化陈述：hasExponent_iff' (p : Nat) [ExpChar K p] : HasExponent K L ↔ exists e, for
all (a : L), a ^ p ^ e in (algebraMap K L).range
参数：p : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPurelyInseparable.hasExponent_iff`：∀ (K : Type u_2) (L : Type u_3) [in
st : CommRing K] [inst_1 : Ring L] [inst_2 : Algebra K L],   IsPurelyInseparable
.HasExponent K L ↔ ∃ e, ∀…
· 使用引理 `ringExpChar.eq`：ringExpChar.eq (q : Nat) [h : ExpChar R q] : ringExpChar
 R = q

--- 原说明 ---
Version of `hasExponent_iff` using `ExpChar`.
-/
theorem hasExponent_iff' (p : ℕ) [ExpChar K p] :
    HasExponent K L ↔ ∃ e, ∀ (a : L), a ^ p ^ e ∈ (algebraMap K L).range :=
  ringExpChar.eq K p ▸ hasExponent_iff K L

open scoped Classical in
/-- The *exponent* of a purely inseparable extension is the smallest
natural number `e` such that `a ^ ringExpChar K ^ e ∈ K` for all `a ∈ L`. -/
/-
**IsPurelyInseparable.exponent** 是 Mathlib 中的一个定义，位于命名空间 `IsPurelyInseparable`。
形式化陈述：exponent [HasExponent K L] : Nat
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsPurelyInseparable.HasExponent.has_exponent`：∀ {K : Type u_2} {L : Type
 u_3} {inst : CommRing K} {inst_1 : Ring L} {inst_2 : Algebra K L}   [self : IsP
urelyInseparable.HasExponent K L],…

--- 原说明 ---
The *exponent* of a purely inseparable extension is the smallest
natural number `e` such that `a ^ ringExpChar K ^ e ∈ K` for all `a ∈ L`.
-/
noncomputable def exponent [HasExponent K L] : ℕ :=
  Nat.find ‹HasExponent K L›.has_exponent

variable {L}
/-
**IsPurelyInseparable.exponent_def** 是 Mathlib 中的一个定理，位于命名空间 `IsPurelyInseparabl
e`。
形式化陈述：exponent_def [HasExponent K L] (a : L) : a ^ ringExpChar K ^ exponent K L 
in (algebraMap K L).range
参数：a : L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.find_spec`：∀ {p : ℕ → Prop} [inst : DecidablePred p] (H : ∃ n, p n),
 p (Nat.find H)
· 使用定理 `IsPurelyInseparable.HasExponent.has_exponent`：∀ {K : Type u_2} {L : Type
 u_3} {inst : CommRing K} {inst_1 : Ring L} {inst_2 : Algebra K L}   [self : IsP
urelyInseparable.HasExponent K L],…
-/
theorem exponent_def [HasExponent K L] (a : L) :
    a ^ ringExpChar K ^ exponent K L ∈ (algebraMap K L).range := by
  classical
  exact Nat.find_spec ‹HasExponent K L›.has_exponent a

/-- Version of `exponent_def` using `ExpChar`. -/
/-
**IsPurelyInseparable.exponent_def'** 是 Mathlib 中的一个定理，位于命名空间 `IsPurelyInseparab
le`。
形式化陈述：exponent_def' [HasExponent K L] (p : Nat) [ExpChar K p] (a : L) : a ^ p ^ 
exponent K L in (algebraMap K L).range
参数：p : Nat；a : L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPurelyInseparable.exponent_def`：exponent_def [HasExponent K L] (a : L)
 : a ^ ringExpChar K ^ exponent K L in (algebraMap K L).range
· 使用引理 `ringExpChar.eq`：ringExpChar.eq (q : Nat) [h : ExpChar R q] : ringExpChar
 R = q

--- 原说明 ---
Version of `exponent_def` using `ExpChar`.
-/
theorem exponent_def' [HasExponent K L] (p : ℕ) [ExpChar K p] (a : L) :
    a ^ p ^ exponent K L ∈ (algebraMap K L).range :=
  ringExpChar.eq K p ▸ exponent_def K a

variable {K}
/-
**IsPurelyInseparable.exponent_min** 是 Mathlib 中的一个定理，位于命名空间 `IsPurelyInseparabl
e`。
形式化陈述：exponent_min [HasExponent K L] {e : Nat} (h : e < exponent K L) : exists a
, a ^ ringExpChar K ^ e ∉ (algebraMap K L).range
参数：h : e < exponent K L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Classical.not_forall`：∀ {α : Sort u_1} {p : α → Prop}, (¬∀ (x : α), p x)
 ↔ ∃ x, ¬p x
· 使用定理 `Nat.find_min`：∀ {p : ℕ → Prop} [inst : DecidablePred p] (H : ∃ n, p n) {
m : ℕ}, m < Nat.find H → ¬p m
· 使用定理 `IsPurelyInseparable.HasExponent.has_exponent`：∀ {K : Type u_2} {L : Type
 u_3} {inst : CommRing K} {inst_1 : Ring L} {inst_2 : Algebra K L}   [self : IsP
urelyInseparable.HasExponent K L],…
-/
theorem exponent_min [HasExponent K L] {e : ℕ} (h : e < exponent K L) :
    ∃ a, a ^ ringExpChar K ^ e ∉ (algebraMap K L).range := by
  classical
  exact not_forall.mp <| Nat.find_min ‹HasExponent K L›.has_exponent h

/-- Version of `exponent_min` using `ExpChar`. -/
/-
**IsPurelyInseparable.exponent_min'** 是 Mathlib 中的一个定理，位于命名空间 `IsPurelyInseparab
le`。
形式化陈述：exponent_min' [HasExponent K L] (p : Nat) [ExpChar K p] {e : Nat} (h : e <
 exponent K L) : exists a, a ^ p ^ e ∉ (algebraMap K L).range
参数：p : Nat；h : e < exponent K L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPurelyInseparable.exponent_min`：exponent_min [HasExponent K L] {e : Na
t} (h : e < exponent K L) : exists a, a ^ ringExpChar K ^ e ∉ (algebraMap K L).r
ange
· 使用引理 `ringExpChar.eq`：ringExpChar.eq (q : Nat) [h : ExpChar R q] : ringExpChar
 R = q

--- 原说明 ---
Version of `exponent_min` using `ExpChar`.
-/
theorem exponent_min' [HasExponent K L] (p : ℕ) [ExpChar K p] {e : ℕ} (h : e < exponent K L) :
    ∃ a, a ^ p ^ e ∉ (algebraMap K L).range :=
  ringExpChar.eq K p ▸ exponent_min h

end Ring

section IsDomain

variable [Field K] [Ring L] [IsDomain L] [Algebra K L]

/-
**IsPurelyInseparable.** 是 Mathlib 中的一个实例，位于命名空间 `IsPurelyInseparable`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasExponent K L] : IsPurelyInseparable K L :=
  let ⟨n, h⟩ := ‹HasExponent K L›.has_exponent
  (isPurelyInseparable_iff_pow_mem K (ringExpChar K)).mpr fun x ↦ ⟨n, h x⟩

end IsDomain

section Field

open Polynomial

variable [Field K] [Field L] [Algebra K L] [IsPurelyInseparable K L]
variable {L}

open scoped Classical in
/-- The exponent of an element `a ∈ L` of a purely inseparable field extension `L / K`
is the smallest natural number `e` such that `a ^ ringExpChar K ^ e ∈ K`. -/
/-
**IsPurelyInseparable.elemExponent** 是 Mathlib 中的一个定义，位于命名空间 `IsPurelyInseparabl
e`。
形式化陈述：elemExponent (a : L) : Nat
参数：a : L。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The exponent of an element `a ∈ L` of a purely inseparable field extension `L / 
K`
is the smallest natural number `e` such that `a ^ ringExpChar K ^ e ∈ K`.
-/
noncomputable def elemExponent (a : L) : ℕ :=
  Nat.find <| minpoly_eq_X_pow_sub_C K (ringExpChar K) a

variable {K} in
/-
**IsPurelyInseparable.elemExponent_eq_zero_of_mem_range** 是 Mathlib 中的一个定理，位于命名空
间 `IsPurelyInseparable`。
形式化陈述：elemExponent_eq_zero_of_mem_range {a : L} (h : a in (algebraMap K L).range
) : elemExponent K a = 0
参数：h : a in (algebraMap K L).range。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.find_eq_zero`：∀ {p : ℕ → Prop} [inst : DecidablePred p] (h : ∃ n, p 
n), Nat.find h = 0 ↔ p 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `minpoly.eq_X_sub_C`：eq_X_sub_C (a : A) : minpoly A (algebraMap A B a) = 
X - C a
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
-/
theorem elemExponent_eq_zero_of_mem_range {a : L} (h : a ∈ (algebraMap K L).range) :
    elemExponent K a = 0 := by
  classical
  apply (Nat.find_eq_zero _).mpr
  rw [pow_zero, pow_one]
  obtain ⟨y, hy⟩ := h
  exact ⟨y, hy ▸ minpoly.eq_X_sub_C L y⟩
/-
**IsPurelyInseparable.elemExponent_eq_zero_of_charZero** 是 Mathlib 中的一个定理，位于命名空间
 `IsPurelyInseparable`。
形式化陈述：elemExponent_eq_zero_of_charZero (a : L) [CharZero K] : elemExponent K a =
 0
参数：a : L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPurelyInseparable.elemExponent_eq_zero_of_mem_range`：elemExponent_eq_z
ero_of_mem_range {a : L} (h : a in (algebraMap K L).range) : elemExponent K a = 
0
· 使用定理 `IsPurelyInseparable.surjective_algebraMap_of_isSeparable`：IsPurelyInsepa
rable.surjective_algebraMap_of_isSeparable [IsPurelyInseparable F E] [Algebra.Is
Separable F E] : Function.Surjective (algebraM…
· 使用定理 `Normal.toIsAlgebraic`：∀ {F : Type u_1} {K : Type u_2} {inst : Field F} {
inst_1 : Field K} {inst_2 : Algebra F K} [self : Normal F K],   Algebra.IsAlgebr
aic F K
-/
theorem elemExponent_eq_zero_of_charZero (a : L) [CharZero K] :
    elemExponent K a = 0 :=
  elemExponent_eq_zero_of_mem_range <| surjective_algebraMap_of_isSeparable K L a

open scoped Classical in
/-- The element `y` of the base field `K` such that
`a ^ ringExpChar K ^ elemExponent K a = algebraMap K L y`.
See `IsPurelyInseparable.algebraMap_elemReduct_eq`. -/
/-
**IsPurelyInseparable.elemReduct** 是 Mathlib 中的一个定义，位于命名空间 `IsPurelyInseparable`
。
形式化陈述：elemReduct (a : L) : K
参数：a : L。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The element `y` of the base field `K` such that
`a ^ ringExpChar K ^ elemExponent K a = algebraMap K L y`.
See `IsPurelyInseparable.algebraMap_elemReduct_eq`.
-/
noncomputable def elemReduct (a : L) : K :=
  Classical.choose <| Nat.find_spec <| minpoly_eq_X_pow_sub_C K (ringExpChar K) a
/-
**IsPurelyInseparable.minpoly_eq** 是 Mathlib 中的一个定理，位于命名空间 `IsPurelyInseparable`
。
形式化陈述：minpoly_eq (a : L) : minpoly K a = X ^ ringExpChar K ^ elemExponent K a - 
C (elemReduct K a)
参数：a : L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `IsPurelyInseparable.minpoly_eq_X_pow_sub_C`：IsPurelyInseparable.minpoly_
eq_X_pow_sub_C (q : Nat) [ExpChar F q] [IsPurelyInseparable F E] (x : E) : exist
s (n : Nat) (y : F), minpoly F x…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Nat.find_spec`：∀ {p : ℕ → Prop} [inst : DecidablePred p] (H : ∃ n, p n),
 p (Nat.find H)
-/
theorem minpoly_eq (a : L) :
    minpoly K a = X ^ ringExpChar K ^ elemExponent K a - C (elemReduct K a) := by
  classical
  exact Classical.choose_spec <| Nat.find_spec <| minpoly_eq_X_pow_sub_C K (ringExpChar K) a

/-- Version of `minpoly_eq` using `ExpChar`. -/
/-
**IsPurelyInseparable.minpoly_eq'** 是 Mathlib 中的一个定理，位于命名空间 `IsPurelyInseparable
`。
形式化陈述：minpoly_eq' (p : Nat) [ExpChar K p] (a : L) : minpoly K a = X ^ p ^ elemEx
ponent K a - C (elemReduct K a)
参数：p : Nat；a : L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPurelyInseparable.minpoly_eq`：minpoly_eq (a : L) : minpoly K a = X ^ r
ingExpChar K ^ elemExponent K a - C (elemReduct K a)
· 使用引理 `ringExpChar.eq`：ringExpChar.eq (q : Nat) [h : ExpChar R q] : ringExpChar
 R = q

--- 原说明 ---
Version of `minpoly_eq` using `ExpChar`.
-/
theorem minpoly_eq' (p : ℕ) [ExpChar K p] (a : L) :
    minpoly K a = X ^ p ^ elemExponent K a - C (elemReduct K a) :=
  ringExpChar.eq K p ▸ minpoly_eq K a

/-- The degree of the minimal polynomial of an element `a ∈ L` equals
`ringExpChar K ^ elemExponent K a`. -/
/-
**IsPurelyInseparable.minpoly_natDegree_eq** 是 Mathlib 中的一个定理，位于命名空间 `IsPurelyIn
separable`。
形式化陈述：minpoly_natDegree_eq (a : L) : (minpoly K a).natDegree = ringExpChar K ^ e
lemExponent K a
参数：a : L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsPurelyInseparable.minpoly_eq`：minpoly_eq (a : L) : minpoly K a = X ^ r
ingExpChar K ^ elemExponent K a - C (elemReduct K a)
· 使用定理 `Polynomial.natDegree_sub_C`：natDegree_sub_C {a : R} : natDegree (p - C a
) = natDegree p
· 使用引理 `Polynomial.natDegree_pow`：natDegree_pow (p : R[X]) (n : Nat) : natDegree
 (p ^ n) = n * natDegree p
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Polynomial.natDegree_X`：natDegree_X : (X : R[X]).natDegree = 1
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a

--- 原说明 ---
The degree of the minimal polynomial of an element `a ∈ L` equals
`ringExpChar K ^ elemExponent K a`.
-/
theorem minpoly_natDegree_eq (a : L) :
    (minpoly K a).natDegree = ringExpChar K ^ elemExponent K a := by
  rw [minpoly_eq K a, natDegree_sub_C, natDegree_pow, natDegree_X, mul_one]

/-- Version of `minpoly_natDegree_eq` using `ExpChar`. -/
/-
**IsPurelyInseparable.minpoly_natDegree_eq'** 是 Mathlib 中的一个定理，位于命名空间 `IsPurelyI
nseparable`。
形式化陈述：minpoly_natDegree_eq' (p : Nat) [ExpChar K p] (a : L) : (minpoly K a).natD
egree = p ^ elemExponent K a
参数：p : Nat；a : L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPurelyInseparable.minpoly_natDegree_eq`：minpoly_natDegree_eq (a : L) :
 (minpoly K a).natDegree = ringExpChar K ^ elemExponent K a
· 使用引理 `ringExpChar.eq`：ringExpChar.eq (q : Nat) [h : ExpChar R q] : ringExpChar
 R = q

--- 原说明 ---
Version of `minpoly_natDegree_eq` using `ExpChar`.
-/
theorem minpoly_natDegree_eq' (p : ℕ) [ExpChar K p] (a : L) :
    (minpoly K a).natDegree = p ^ elemExponent K a :=
  ringExpChar.eq K p ▸ minpoly_natDegree_eq K a
/-
**IsPurelyInseparable.algebraMap_elemReduct_eq** 是 Mathlib 中的一个定理，位于命名空间 `IsPure
lyInseparable`。
形式化陈述：algebraMap_elemReduct_eq (a : L) : algebraMap K L (elemReduct K a) = a ^ r
ingExpChar K ^ elemExponent K a
参数：a : L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `minpoly.aeval`：aeval : aeval x (minpoly A x) = 0
· 使用定理 `IsPurelyInseparable.minpoly_eq`：minpoly_eq (a : L) : minpoly K a = X ^ r
ingExpChar K ^ elemExponent K a - C (elemReduct K a)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `Polynomial.aeval_X`：aeval_X : aeval x (X : R[X]) = x
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `Polynomial.aeval_C`：aeval_C (r : R) : aeval x (C r) = algebraMap R A r
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
-/
theorem algebraMap_elemReduct_eq (a : L) :
    algebraMap K L (elemReduct K a) = a ^ ringExpChar K ^ elemExponent K a := by
  have := minpoly_eq K a ▸ minpoly.aeval K a
  rwa [map_sub, aeval_C, map_pow, aeval_X, sub_eq_zero, eq_comm] at this

/-- Version of `algebraMap_elemReduct_eq` using `ExpChar`. -/
/-
**IsPurelyInseparable.algebraMap_elemReduct_eq'** 是 Mathlib 中的一个定理，位于命名空间 `IsPur
elyInseparable`。
形式化陈述：algebraMap_elemReduct_eq' (p : Nat) [ExpChar K p] (a : L) : algebraMap K L
 (elemReduct K a) = a ^ p ^ elemExponent K a
参数：p : Nat；a : L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPurelyInseparable.algebraMap_elemReduct_eq`：algebraMap_elemReduct_eq (
a : L) : algebraMap K L (elemReduct K a) = a ^ ringExpChar K ^ elemExponent K a
· 使用引理 `ringExpChar.eq`：ringExpChar.eq (q : Nat) [h : ExpChar R q] : ringExpChar
 R = q

--- 原说明 ---
Version of `algebraMap_elemReduct_eq` using `ExpChar`.
-/
theorem algebraMap_elemReduct_eq' (p : ℕ) [ExpChar K p] (a : L) :
    algebraMap K L (elemReduct K a) = a ^ p ^ elemExponent K a :=
  ringExpChar.eq K p ▸ algebraMap_elemReduct_eq K a
/-
**IsPurelyInseparable.elemExponent_def** 是 Mathlib 中的一个定理，位于命名空间 `IsPurelyInsepa
rable`。
形式化陈述：elemExponent_def (a : L) : a ^ ringExpChar K ^ elemExponent K a in (algebr
aMap K L).range
参数：a : L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `RingHom.mem_range`：mem_range {f : R ->+* S} {y : S} : y in f.range ↔ exi
sts x, f x = y
· 使用定理 `IsPurelyInseparable.algebraMap_elemReduct_eq`：algebraMap_elemReduct_eq (
a : L) : algebraMap K L (elemReduct K a) = a ^ ringExpChar K ^ elemExponent K a
-/
theorem elemExponent_def (a : L) :
    a ^ ringExpChar K ^ elemExponent K a ∈ (algebraMap K L).range :=
  RingHom.mem_range.mpr <| ⟨_, algebraMap_elemReduct_eq K a⟩

/-- Version of `elemExponent_def` using `ExpChar`. -/
/-
**IsPurelyInseparable.elemExponent_def'** 是 Mathlib 中的一个定理，位于命名空间 `IsPurelyInsep
arable`。
形式化陈述：elemExponent_def' (p : Nat) [ExpChar K p] (a : L) : a ^ p ^ elemExponent K
 a in (algebraMap K L).range
参数：p : Nat；a : L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPurelyInseparable.elemExponent_def`：elemExponent_def (a : L) : a ^ rin
gExpChar K ^ elemExponent K a in (algebraMap K L).range
· 使用引理 `ringExpChar.eq`：ringExpChar.eq (q : Nat) [h : ExpChar R q] : ringExpChar
 R = q

--- 原说明 ---
Version of `elemExponent_def` using `ExpChar`.
-/
theorem elemExponent_def' (p : ℕ) [ExpChar K p] (a : L) :
    a ^ p ^ elemExponent K a ∈ (algebraMap K L).range :=
  ringExpChar.eq K p ▸ elemExponent_def K a

variable {K} in
/-
**IsPurelyInseparable.elemExponent_le_of_pow_mem** 是 Mathlib 中的一个定理，位于命名空间 `IsPu
relyInseparable`。
形式化陈述：elemExponent_le_of_pow_mem {a : L} {n : Nat} (h : a ^ ringExpChar K ^ n in
 (algebraMap K L).range) : elemExponent K a <= n
参数：h : a ^ ringExpChar K ^ n in (algebraMap K L).range。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ExpChar.exists`：ExpChar.exists [Ring R] [IsDomain R] : exists q, ExpChar
 R q
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsPurelyInseparable.elemExponent_eq_zero_of_charZero`：elemExponent_eq_ze
ro_of_charZero (a : L) [CharZero K] : elemExponent K a = 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `RingHom.mem_range`：mem_range {f : R ->+* S} {y : S} : y in f.range ↔ exi
sts x, f x = y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `Polynomial.aeval_C`：aeval_C (r : R) : aeval x (C r) = algebraMap R A r
· 使用定理 `Polynomial.aeval_X_pow`：aeval_X_pow {n : Nat} : aeval x ((X : R[X]) ^ n)
 = x ^ n
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Polynomial.monic_X_pow_sub_C`：monic_X_pow_sub_C {R : Type u} [Ring R] (a
 : R) {n : Nat} (h : n != 0) : (X ^ n - C a).Monic
· 使用定理 `Nat.pos_iff_ne_zero`：∀ {n : ℕ}, 0 < n ↔ n ≠ 0
· 使用引理 `expChar_pow_pos`：expChar_pow_pos (q : Nat) [ExpChar R q] (n : Nat) : 0 <
 q ^ n
· 使用定理 `Polynomial.natDegree_sub_C`：natDegree_sub_C {a : R} : natDegree (p - C a
) = natDegree p
· 使用引理 `Polynomial.natDegree_pow`：natDegree_pow (p : R[X]) (n : Nat) : natDegree
 (p ^ n) = n * natDegree p
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Polynomial.natDegree_X`：natDegree_X : (X : R[X]).natDegree = 1
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Nat.pow_le_pow_iff_right`：∀ {a n m : ℕ}, 1 < a → (a ^ n ≤ a ^ m ↔ n ≤ m)
· 使用定理 `Nat.Prime.one_lt`：∀ {p : ℕ}, Nat.Prime p → 1 < p
· 使用定理 `Polynomial.natDegree_le_natDegree`：natDegree_le_natDegree [Semiring S] {
q : S[X]} (hpq : p.degree <= q.degree) : p.natDegree <= q.natDegree
· 使用定理 `minpoly.min`：min {p : A[X]} (pmonic : p.Monic) (hp : Polynomial.aeval x 
p = 0) : degree (minpoly A x) <= degree p
· 使用定理 `IsPurelyInseparable.minpoly_natDegree_eq`：minpoly_natDegree_eq (a : L) :
 (minpoly K a).natDegree = ringExpChar K ^ elemExponent K a
（共 31 条，此处仅展示前 30 条）
-/
theorem elemExponent_le_of_pow_mem {a : L} {n : ℕ}
    (h : a ^ ringExpChar K ^ n ∈ (algebraMap K L).range) : elemExponent K a ≤ n := by
  let ⟨p, _⟩ := ExpChar.exists K
  rcases ‹ExpChar K p› with _ | ⟨hp⟩
  · exact elemExponent_eq_zero_of_charZero K a ▸ Nat.zero_le _
  · obtain ⟨y, hy⟩ := RingHom.mem_range.mp <| h
    let f := X ^ ringExpChar K ^ n - C y
    have hf₁ : f.aeval a = 0 := by rwa [map_sub, aeval_C, aeval_X_pow, sub_eq_zero, eq_comm]
    have hf₂ : f.Monic := monic_X_pow_sub_C y <| Nat.pos_iff_ne_zero.mp <| expChar_pow_pos K _ _
    have hf₃ : f.natDegree = ringExpChar K ^ n := by
      rw [natDegree_sub_C, natDegree_pow, natDegree_X, mul_one]
    exact (Nat.pow_le_pow_iff_right <| Nat.Prime.one_lt hp).mp <|
      ringExpChar.eq K p ▸ hf₃ ▸ minpoly_natDegree_eq K a ▸
      natDegree_le_natDegree (minpoly.min K a hf₂ hf₁)

variable {K} in
/-- Version of `elemExponent_le_of_pow_mem` using `ExpChar`. -/
/-
**IsPurelyInseparable.elemExponent_le_of_pow_mem'** 是 Mathlib 中的一个定理，位于命名空间 `IsP
urelyInseparable`。
形式化陈述：elemExponent_le_of_pow_mem' (p : Nat) [ExpChar K p] {a : L} {n : Nat} (h :
 a ^ p ^ n in (algebraMap K L).range) : elemExponent K a <= n
参数：p : Nat；h : a ^ p ^ n in (algebraMap K L).range。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPurelyInseparable.elemExponent_le_of_pow_mem`：elemExponent_le_of_pow_m
em {a : L} {n : Nat} (h : a ^ ringExpChar K ^ n in (algebraMap K L).range) : ele
mExponent K a <= n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ringExpChar.eq`：ringExpChar.eq (q : Nat) [h : ExpChar R q] : ringExpChar
 R = q

--- 原说明 ---
Version of `elemExponent_le_of_pow_mem` using `ExpChar`.
-/
theorem elemExponent_le_of_pow_mem' (p : ℕ) [ExpChar K p] {a : L} {n : ℕ}
    (h : a ^ p ^ n ∈ (algebraMap K L).range) : elemExponent K a ≤ n :=
  elemExponent_le_of_pow_mem (ringExpChar.eq K p ▸ h)

variable {K} in
/-
**IsPurelyInseparable.elemExponent_min** 是 Mathlib 中的一个定理，位于命名空间 `IsPurelyInsepa
rable`。
形式化陈述：elemExponent_min {a : L} {n : Nat} (h : n < elemExponent K a) : a ^ ringEx
pChar K ^ n ∉ (algebraMap K L).range
参数：h : n < elemExponent K a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.not_lt_of_ge`：∀ {a b : ℕ}, b ≥ a → ¬b < a
· 使用定理 `IsPurelyInseparable.elemExponent_le_of_pow_mem`：elemExponent_le_of_pow_m
em {a : L} {n : Nat} (h : a ^ ringExpChar K ^ n in (algebraMap K L).range) : ele
mExponent K a <= n
-/
theorem elemExponent_min {a : L} {n : ℕ} (h : n < elemExponent K a) :
    a ^ ringExpChar K ^ n ∉ (algebraMap K L).range :=
  fun hn ↦ (Nat.not_lt_of_ge <| elemExponent_le_of_pow_mem hn) h

/-- Version of `elemExponent_min` using `ExpChar`. -/
/-
**IsPurelyInseparable.elemExponent_min'** 是 Mathlib 中的一个定理，位于命名空间 `IsPurelyInsep
arable`。
形式化陈述：elemExponent_min' (p : Nat) [ExpChar K p] {a : L} {n : Nat} (h : n < elemE
xponent K a) : a ^ p ^ n ∉ (algebraMap K L).range
参数：p : Nat；h : n < elemExponent K a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPurelyInseparable.elemExponent_min`：elemExponent_min {a : L} {n : Nat}
 (h : n < elemExponent K a) : a ^ ringExpChar K ^ n ∉ (algebraMap K L).range
· 使用引理 `ringExpChar.eq`：ringExpChar.eq (q : Nat) [h : ExpChar R q] : ringExpChar
 R = q

--- 原说明 ---
Version of `elemExponent_min` using `ExpChar`.
-/
theorem elemExponent_min' (p : ℕ) [ExpChar K p] {a : L} {n : ℕ} (h : n < elemExponent K a) :
    a ^ p ^ n ∉ (algebraMap K L).range :=
  ringExpChar.eq K p ▸ elemExponent_min h

/-- An exponent of an element is less or equal than exponent of the extension. -/
/-
**IsPurelyInseparable.elemExponent_le_exponent** 是 Mathlib 中的一个定理，位于命名空间 `IsPure
lyInseparable`。
形式化陈述：elemExponent_le_exponent [HasExponent K L] (a : L) : elemExponent K a <= e
xponent K L
参数：a : L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPurelyInseparable.elemExponent_le_of_pow_mem`：elemExponent_le_of_pow_m
em {a : L} {n : Nat} (h : a ^ ringExpChar K ^ n in (algebraMap K L).range) : ele
mExponent K a <= n
· 使用定理 `IsPurelyInseparable.exponent_def`：exponent_def [HasExponent K L] (a : L)
 : a ^ ringExpChar K ^ exponent K L in (algebraMap K L).range

--- 原说明 ---
An exponent of an element is less or equal than exponent of the extension.
-/
theorem elemExponent_le_exponent [HasExponent K L] (a : L) :
    elemExponent K a ≤ exponent K L :=
  elemExponent_le_of_pow_mem <| exponent_def K a

variable {K} in
/-
**IsPurelyInseparable.hasExponent_of_finiteDimensional** 是 Mathlib 中的一个实例，位于命名空间
 `IsPurelyInseparable`。
形式化陈述：hasExponent_of_finiteDimensional [FiniteDimensional K L] : HasExponent K L
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `ExpChar.exists`：ExpChar.exists [Ring R] [IsDomain R] : exists q, ExpChar
 R q
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsPurelyInseparable.surjective_algebraMap_of_isSeparable`：IsPurelyInsepa
rable.surjective_algebraMap_of_isSeparable [IsPurelyInseparable F E] [Algebra.Is
Separable F E] : Function.Surjective (algebraM…
· 使用定理 `Normal.toIsAlgebraic`：∀ {F : Type u_1} {K : Type u_2} {inst : Field F} {
inst_1 : Field K} {inst_2 : Algebra F K} [self : Normal F K],   Algebra.IsAlgebr
aic F K
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.le_log_of_pow_le`：le_log_of_pow_le {b x y : Nat} (hb : 1 < b) (h : b
 ^ x <= y) : x <= log b y
· 使用定理 `Nat.Prime.one_lt`：∀ {p : ℕ}, Nat.Prime p → 1 < p
· 使用引理 `ringExpChar.eq`：ringExpChar.eq (q : Nat) [h : ExpChar R q] : ringExpChar
 R = q
· 使用定理 `minpoly.natDegree_le`：natDegree_le [Module.Free A B] : (minpoly A x).nat
Degree <= Module.finrank A B
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `IsPurelyInseparable.minpoly_natDegree_eq`：minpoly_natDegree_eq (a : L) :
 (minpoly K a).natDegree = ringExpChar K ^ elemExponent K a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `IsPurelyInseparable.algebraMap_elemReduct_eq`：algebraMap_elemReduct_eq (
a : L) : algebraMap K L (elemReduct K a) = a ^ ringExpChar K ^ elemExponent K a
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `Nat.add_sub_cancel'`：∀ {n m : ℕ}, m ≤ n → m + (n - m) = n
-/
instance hasExponent_of_finiteDimensional [FiniteDimensional K L] :
    HasExponent K L := by
  let ⟨p, _⟩ := ExpChar.exists K
  rcases ‹ExpChar K p› with _ | ⟨hp⟩
  · exact ⟨0, fun a ↦ surjective_algebraMap_of_isSeparable K L _⟩
  · let e := Nat.log (ringExpChar K) (Module.finrank K L)
    refine ⟨e, fun a ↦ ⟨elemReduct K a ^ ringExpChar K ^ (e - elemExponent K a), ?_⟩⟩
    have h_elemexp_bound (a : L) : elemExponent K a ≤ e :=
      Nat.le_log_of_pow_le (Nat.Prime.one_lt <| ringExpChar.eq K p ▸ hp)
        (minpoly_natDegree_eq K a ▸ minpoly.natDegree_le a)
    rw [map_pow, algebraMap_elemReduct_eq, ← pow_mul, ← pow_add,
      Nat.add_sub_cancel' (h_elemexp_bound a)]

end Field

section Frobenius

/-
This section defines the iterated Frobenius map `x ↦ x ^ p ^ n` for a purely inseparable
field extension `L / K` with exponent, with the base field `K` as a codomain, when
`n ≥ exponent K L`.
We define it both as a ring homomorphism and a semilinear map over a subfield `F` of `K`.

Implementation note: the API exposes arguments `{n : ℕ} (hn : exponent K L ≤ n)` to define the
action `x ↦ x ^ p ^ n` instead of just `(n : ℕ)` with action `x ↦ x ^ p ^ (exponent K L + n)`
to avoid problems with definitional equality when using the semilinear map version.
-/

variable [Field K] [Field L] [Algebra K L] [HasExponent K L]
variable (p : ℕ) [ExpChar K p]

set_option backward.privateInPublic true in
/-
**IsPurelyInseparable.iterateFrobeniusAux** 是 Mathlib 中的一个定义，位于命名空间 `IsPurelyIns
eparable`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private noncomputable def iterateFrobeniusAux (n : ℕ) : L → K :=
  fun a ↦ elemReduct K a ^ p ^ (n - elemExponent K a)

variable {L} in
/-- Action of `iterateFrobeniusAux` on the top field. -/
/-
**IsPurelyInseparable.algebraMap_iterateFrobeniusAux** 是 Mathlib 中的一个定理，位于命名空间 `
IsPurelyInseparable`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Action of `iterateFrobeniusAux` on the top field.
-/
private theorem algebraMap_iterateFrobeniusAux {n : ℕ} (hn : exponent K L ≤ n) (a : L) :
    algebraMap K L (iterateFrobeniusAux K L p n a) = a ^ p ^ n := by
  rw [iterateFrobeniusAux, map_pow, algebraMap_elemReduct_eq' K p, ← pow_mul, ← pow_add,
    Nat.add_sub_cancel' <| (elemExponent_le_exponent K a).trans hn]

section RingHom

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- Iterated Frobenius map (ring homomorphism) for purely inseparable field extension with exponent.
If `n ≥ exponent K L`, it acts like `x ↦ x ^ p ^ n` but the codomain is the base field `K`. -/
/-
**IsPurelyInseparable.iterateFrobenius** 是 Mathlib 中的一个定义，位于命名空间 `IsPurelyInsepa
rable`。
形式化陈述：iterateFrobenius {n : Nat} (hn : exponent K L <= n) : L ->+* K where toFun
参数：hn : exponent K L <= n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Iterated Frobenius map (ring homomorphism) for purely inseparable field extensio
n with exponent.
If `n ≥ exponent K L`, it acts like `x ↦ x ^ p ^ n` but the codomain is the base
 field `K`.
-/
noncomputable def iterateFrobenius {n : ℕ} (hn : exponent K L ≤ n) : L →+* K where
  toFun := iterateFrobeniusAux K L p n
  map_zero' := by
    apply (algebraMap K L).injective
    rw [(algebraMap K L).map_zero,
      algebraMap_iterateFrobeniusAux K p hn 0,
      zero_pow]
    exact Nat.pos_iff_ne_zero.mp <| expChar_pow_pos K p n
  map_add' a b := by
    have inj := (algebraMap K L).injective
    have : ExpChar L p := expChar_of_injective_ringHom inj p
    apply inj
    rw [(algebraMap K L).map_add,
      algebraMap_iterateFrobeniusAux K p hn a,
      algebraMap_iterateFrobeniusAux K p hn b,
      algebraMap_iterateFrobeniusAux K p hn (a + b),
      add_pow_expChar_pow a b]
  map_one' := by
    apply (algebraMap K L).injective
    rw [(algebraMap K L).map_one,
      algebraMap_iterateFrobeniusAux K p hn 1,
      one_pow]
  map_mul' a b := by
    apply (algebraMap K L).injective
    rw [(algebraMap K L).map_mul,
      algebraMap_iterateFrobeniusAux K p hn a,
      algebraMap_iterateFrobeniusAux K p hn b,
      algebraMap_iterateFrobeniusAux K p hn (a * b),
      mul_pow]

variable {L} in
/-- Action of `iterateFrobenius` on the top field. -/
/-
**IsPurelyInseparable.algebraMap_iterateFrobenius** 是 Mathlib 中的一个定理，位于命名空间 `IsP
urelyInseparable`。
形式化陈述：algebraMap_iterateFrobenius {n : Nat} (hn : exponent K L <= n) (a : L) : a
lgebraMap K L (iterateFrobenius K L p hn a) = a ^ p ^ n
参数：hn : exponent K L <= n；a : L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.FieldTheory.PurelyInseparable.Exponent.0.IsPurelyInsepa
rable.algebraMap_iterateFrobeniusAux`：∀ (K : Type u_2) {L : Type u_3} [inst : Fi
eld K] [inst_1 : Field L] [inst_2 : Algebra K L]   [inst_3 : IsPurelyInseparable
.HasExponent K L] …

--- 原说明 ---
Action of `iterateFrobenius` on the top field.
-/
theorem algebraMap_iterateFrobenius {n : ℕ} (hn : exponent K L ≤ n) (a : L) :
    algebraMap K L (iterateFrobenius K L p hn a) = a ^ p ^ n :=
  algebraMap_iterateFrobeniusAux K p hn a

variable {K} in
/-- Action of `iterateFrobenius` on the bottom field. -/
/-
**IsPurelyInseparable.iterateFrobenius_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `IsP
urelyInseparable`。
形式化陈述：iterateFrobenius_algebraMap {n : Nat} (hn : exponent K L <= n) (a : K) : i
terateFrobenius K L p hn (algebraMap K L a) = a ^ p ^ n
参数：hn : exponent K L <= n；a : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `IsPurelyInseparable.algebraMap_iterateFrobenius`：algebraMap_iterateFrobe
nius {n : Nat} (hn : exponent K L <= n) (a : L) : algebraMap K L (iterateFrobeni
us K L p hn a) = a ^ p ^ n

--- 原说明 ---
Action of `iterateFrobenius` on the bottom field.
-/
theorem iterateFrobenius_algebraMap {n : ℕ} (hn : exponent K L ≤ n) (a : K) :
    iterateFrobenius K L p hn (algebraMap K L a) = a ^ p ^ n := by
  apply (algebraMap K L).injective
  rw [map_pow, algebraMap_iterateFrobenius K p hn]

end RingHom

section Semilinear

variable [Field F] [Algebra F K] [Algebra F L] [IsScalarTower F K L]
variable [ExpChar F p]

/-- Version of `iterateFrobenius` as a semilinear map over a subfield `F` of `K`, w.r.t. the
iterated Frobenius homomorphism on `F`. -/
/-
**IsPurelyInseparable.iterateFrobenius** 是 Mathlib 中的一个定义，位于命名空间 `IsPurelyInsepa
rable`。
形式化陈述：iterateFrobenius {n : Nat} (hn : exponent K L <= n) : L ->+* K where toFun
参数：hn : exponent K L <= n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Version of `iterateFrobenius` as a semilinear map over a subfield `F` of `K`, w.
r.t. the
iterated Frobenius homomorphism on `F`.
-/
noncomputable def iterateFrobeniusₛₗ {n : ℕ} (hn : exponent K L ≤ n) :
    L →ₛₗ[_root_.iterateFrobenius F p n] K where
  __ := iterateFrobenius K L p hn
  map_smul' r a := by
    dsimp [iterateFrobenius]
    rw [Algebra.smul_def _ (iterateFrobeniusAux K L p n a)]
    apply (algebraMap K L).injective
    rw [(algebraMap K L).map_mul,
      ← IsScalarTower.algebraMap_apply,
      algebraMap_iterateFrobeniusAux K p hn a,
      algebraMap_iterateFrobeniusAux K p hn (r • a),
      iterateFrobenius_def,
      map_pow,
      Algebra.smul_def,
      mul_pow]

/-- Action of `iterateFrobeniusₛₗ` on the top field. -/
/-
**IsPurelyInseparable.algebraMap_iterateFrobenius** 是 Mathlib 中的一个定理，位于命名空间 `IsP
urelyInseparable`。
形式化陈述：algebraMap_iterateFrobenius {n : Nat} (hn : exponent K L <= n) (a : L) : a
lgebraMap K L (iterateFrobenius K L p hn a) = a ^ p ^ n
参数：hn : exponent K L <= n；a : L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.FieldTheory.PurelyInseparable.Exponent.0.IsPurelyInsepa
rable.algebraMap_iterateFrobeniusAux`：∀ (K : Type u_2) {L : Type u_3} [inst : Fi
eld K] [inst_1 : Field L] [inst_2 : Algebra K L]   [inst_3 : IsPurelyInseparable
.HasExponent K L] …

--- 原说明 ---
Action of `iterateFrobeniusₛₗ` on the top field.
-/
theorem algebraMap_iterateFrobeniusₛₗ {n : ℕ} (hn : exponent K L ≤ n) (a : L) :
    algebraMap K L (iterateFrobeniusₛₗ F K L p hn a) = a ^ p ^ n :=
  algebraMap_iterateFrobenius K p hn a

/-- Action of `iterateFrobeniusₛₗ` on the bottom field. -/
/-
**IsPurelyInseparable.iterateFrobenius** 是 Mathlib 中的一个定义，位于命名空间 `IsPurelyInsepa
rable`。
形式化陈述：iterateFrobenius {n : Nat} (hn : exponent K L <= n) : L ->+* K where toFun
参数：hn : exponent K L <= n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Action of `iterateFrobeniusₛₗ` on the bottom field.
-/
theorem iterateFrobeniusₛₗ_algebraMap {n : ℕ} (hn : exponent K L ≤ n) (a : K) :
    iterateFrobeniusₛₗ F K L p hn (algebraMap K L a) = a ^ p ^ n :=
  iterateFrobenius_algebraMap L p hn a

/-- Action of `iterateFrobeniusₛₗ` on the base field. -/
/-
**IsPurelyInseparable.iterateFrobenius** 是 Mathlib 中的一个定义，位于命名空间 `IsPurelyInsepa
rable`。
形式化陈述：iterateFrobenius {n : Nat} (hn : exponent K L <= n) : L ->+* K where toFun
参数：hn : exponent K L <= n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Action of `iterateFrobeniusₛₗ` on the base field.
-/
theorem iterateFrobeniusₛₗ_algebraMap_base {n : ℕ} (hn : exponent K L ≤ n) (a : F) :
    iterateFrobeniusₛₗ F K L p hn (algebraMap F L a) = (algebraMap F K a) ^ p ^ n := by
  apply (algebraMap K L).injective
  rw [← map_pow, ← IsScalarTower.algebraMap_apply, map_pow,
    algebraMap_iterateFrobeniusₛₗ F K L p hn]

end Semilinear

end Frobenius

end IsPurelyInseparable

