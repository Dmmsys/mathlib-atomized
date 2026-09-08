/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro, Johan Commelin, Amelia Livingston, Anne Baanen
-/
module

public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.Integer
public import Mathlib.RingTheory.UniqueFactorizationDomain.GCDMonoid

/-!
# Numerator and denominator in a localization

## Implementation notes

See `Mathlib/RingTheory/Localization/Basic.lean` for a design overview.

## Tags
localization, ring localization, commutative ring localization, characteristic predicate,
commutative ring, field of fractions
-/

@[expose] public section


namespace IsFractionRing

open IsLocalization

section NumDen

variable (A : Type*) [CommRing A] [IsDomain A] [UniqueFactorizationMonoid A]
variable {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]

/-
**IsFractionRing.exists_reduced_fraction** 是 Mathlib 中的一个定理，位于命名空间 `IsFractionRi
ng`。
形式化陈述：exists_reduced_fraction (x : K) : exists (a : A) (b : nonZeroDivisors A), 
IsRelPrime a b ∧ mk' K a b = x
参数：x : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `IsLocalization.exists_integer_multiple`：exists_integer_multiple (a : S) 
: exists b : M, IsInteger R ((b : R) • a)
· 使用定理 `UniqueFactorizationMonoid.exists_reduced_factors'`：exists_reduced_factor
s' (a b : R) (hb : b != 0) : exists a' b' c', IsRelPrime a' b' ∧ c' * a' = a ∧ c
' * b' = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_nonZeroDivisors_iff_ne_zero`：∀ {M₀ : Type u_2} [inst : MonoidWithZer
o M₀] {x : M₀} [NoZeroDivisors M₀] [Nontrivial M₀],   x ∈ nonZeroDivisors M₀ ↔ x
 ≠ 0
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用引理 `mul_mem_nonZeroDivisors`：mul_mem_nonZeroDivisors : a * b in M₀⁰ ↔ a in M
₀⁰ ∧ b in M₀⁰ where mp h
· 使用定理 `mul_left_cancel₀`：mul_left_cancel₀ (ha : a != 0) (h : a * b = a * c) : b
 = c
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors`：∀ {R : Type u_1} [
inst : CommRing R] {K : Type u_5} [inst_1 : CommRing K] [inst_2 : Algebra R K] [
IsFractionRing R K]   [Nontrivial R] {x : …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `IsLocalization.mk'_spec'`：∀ {R : Type u_1} [inst : CommSemiring R] {M : 
Submonoid R} (S : Type u_2) [inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [
inst_3 : IsLoc…
-/
theorem exists_reduced_fraction (x : K) :
    ∃ (a : A) (b : nonZeroDivisors A), IsRelPrime a b ∧ mk' K a b = x := by
  obtain ⟨⟨b, b_nonzero⟩, a, hab⟩ := exists_integer_multiple (nonZeroDivisors A) x
  obtain ⟨a', b', c', no_factor, rfl, rfl⟩ :=
    UniqueFactorizationMonoid.exists_reduced_factors' a b
      (mem_nonZeroDivisors_iff_ne_zero.mp b_nonzero)
  obtain ⟨_, b'_nonzero⟩ := mul_mem_nonZeroDivisors.mp b_nonzero
  refine ⟨a', ⟨b', b'_nonzero⟩, no_factor, ?_⟩
  refine mul_left_cancel₀ (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b_nonzero) ?_
  simp only [map_mul, Algebra.smul_def] at *
  rw [← hab, mul_assoc, mk'_spec' _ a' ⟨b', b'_nonzero⟩]

/-- `f.num x` is the numerator of `x : f.codomain` as a reduced fraction. -/
/-
**IsFractionRing.num** 是 Mathlib 中的一个定义，位于命名空间 `IsFractionRing`。
形式化陈述：num (x : K) : A
参数：x : K。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `IsFractionRing.exists_reduced_fraction`：exists_reduced_fraction (x : K) 
: exists (a : A) (b : nonZeroDivisors A), IsRelPrime a b ∧ mk' K a b = x

--- 原说明 ---
`f.num x` is the numerator of `x : f.codomain` as a reduced fraction.
-/
noncomputable def num (x : K) : A :=
  Classical.choose (exists_reduced_fraction A x)

/-- `f.den x` is the denominator of `x : f.codomain` as a reduced fraction. -/
/-
**IsFractionRing.den** 是 Mathlib 中的一个定义，位于命名空间 `IsFractionRing`。
形式化陈述：den (x : K) : nonZeroDivisors A
参数：x : K。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `IsFractionRing.exists_reduced_fraction`：exists_reduced_fraction (x : K) 
: exists (a : A) (b : nonZeroDivisors A), IsRelPrime a b ∧ mk' K a b = x

--- 原说明 ---
`f.den x` is the denominator of `x : f.codomain` as a reduced fraction.
-/
noncomputable def den (x : K) : nonZeroDivisors A :=
  Classical.choose (Classical.choose_spec (exists_reduced_fraction A x))
/-
**IsFractionRing.num_den_reduced** 是 Mathlib 中的一个定理，位于命名空间 `IsFractionRing`。
形式化陈述：num_den_reduced (x : K) : IsRelPrime (num A x) (den A x)
参数：x : K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `IsFractionRing.exists_reduced_fraction`：exists_reduced_fraction (x : K) 
: exists (a : A) (b : nonZeroDivisors A), IsRelPrime a b ∧ mk' K a b = x
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem num_den_reduced (x : K) : IsRelPrime (num A x) (den A x) :=
  (Classical.choose_spec (Classical.choose_spec (exists_reduced_fraction A x))).1

-- `@[simp]` normal form is called `mk'_num_den'`.
/-
**IsFractionRing.mk'_num_den** 是 Mathlib 中的一个定理，位于命名空间 `IsFractionRing`。
形式化陈述：∀ (A : Type u_1) [inst : CommRing A] [inst_1 : IsDomain A] [inst_2 : Uniqu
eFactorizationMonoid A] {K : Type u_2}   [inst_3 : Field K] [inst_4 : Algebra A 
K] [inst_5 : IsFractionRing A K] (x : K),   IsLocalization.mk' K (IsFractionRing
.num A x) (IsFractionRing.den A x) = x
参数：A : Type u_1；x : K；IsFractionRing.num A x；IsFractionRing.den A x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `IsFractionRing.exists_reduced_fraction`：exists_reduced_fraction (x : K) 
: exists (a : A) (b : nonZeroDivisors A), IsRelPrime a b ∧ mk' K a b = x
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem mk'_num_den (x : K) : mk' K (num A x) (den A x) = x :=
  (Classical.choose_spec (Classical.choose_spec (exists_reduced_fraction A x))).2

@[simp]
/-
**IsFractionRing.mk'_num_den'** 是 Mathlib 中的一个定理，位于命名空间 `IsFractionRing`。
形式化陈述：∀ (A : Type u_1) [inst : CommRing A] [inst_1 : IsDomain A] [inst_2 : Uniqu
eFactorizationMonoid A] {K : Type u_2}   [inst_3 : Field K] [inst_4 : Algebra A 
K] [inst_5 : IsFractionRing A K] (x : K),   (algebraMap A K) (IsFractionRing.num
 A x) / (algebraMap A K) ↑(IsFractionRing.den A x) = x
参数：A : Type u_1；x : K；algebraMap A K；IsFractionRing.num A x；algebraMap A K；IsFra
ctionRing.den A x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsFractionRing.mk'_eq_div`：∀ {A : Type u_4} [inst : CommRing A] {K : Typ
e u_5} [inst_1 : Field K] [inst_2 : Algebra A K]   [inst_3 : IsFractionRing A K]
 {r : A} (s : ↥…
· 使用定理 `IsFractionRing.mk'_num_den`：∀ (A : Type u_1) [inst : CommRing A] [inst_1
 : IsDomain A] [inst_2 : UniqueFactorizationMonoid A] {K : Type u_2}   [inst_3 :
 Field K] [inst_…
-/
theorem mk'_num_den' (x : K) : algebraMap A K (num A x) / algebraMap A K (den A x) = x := by
  rw [← mk'_eq_div]
  apply mk'_num_den

variable {A}
/-
**IsFractionRing.num_mul_den_eq_num_iff_eq** 是 Mathlib 中的一个定理，位于命名空间 `IsFraction
Ring`。
形式化陈述：num_mul_den_eq_num_iff_eq {x y : K} : x * algebraMap A K (den A y) = algeb
raMap A K (num A y) ↔ x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsFractionRing.mk'_num_den`：∀ (A : Type u_1) [inst : CommRing A] [inst_1
 : IsDomain A] [inst_2 : UniqueFactorizationMonoid A] {K : Type u_2}   [inst_3 :
 Field K] [inst_…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsLocalization.eq_mk'_iff_mul_eq`：∀ {R : Type u_1} [inst : CommSemiring 
R] {M : Submonoid R} {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebr
a R S] [inst_3 : IsLoc…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
theorem num_mul_den_eq_num_iff_eq {x y : K} :
    x * algebraMap A K (den A y) = algebraMap A K (num A y) ↔ x = y :=
  ⟨fun h => by simpa only [mk'_num_den] using eq_mk'_iff_mul_eq.mpr h, fun h ↦
    eq_mk'_iff_mul_eq.mp (by rw [h, mk'_num_den])⟩
/-
**IsFractionRing.num_mul_den_eq_num_iff_eq'** 是 Mathlib 中的一个定理，位于命名空间 `IsFractio
nRing`。
形式化陈述：num_mul_den_eq_num_iff_eq' {x y : K} : y * algebraMap A K (den A x) = alge
braMap A K (num A x) ↔ x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsFractionRing.mk'_num_den`：∀ (A : Type u_1) [inst : CommRing A] [inst_1
 : IsDomain A] [inst_2 : UniqueFactorizationMonoid A] {K : Type u_2}   [inst_3 :
 Field K] [inst_…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsLocalization.eq_mk'_iff_mul_eq`：∀ {R : Type u_1} [inst : CommSemiring 
R] {M : Submonoid R} {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebr
a R S] [inst_3 : IsLoc…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
theorem num_mul_den_eq_num_iff_eq' {x y : K} :
    y * algebraMap A K (den A x) = algebraMap A K (num A x) ↔ x = y :=
  ⟨fun h ↦ by simpa only [eq_comm, mk'_num_den] using eq_mk'_iff_mul_eq.mpr h, fun h ↦
    eq_mk'_iff_mul_eq.mp (by rw [h, mk'_num_den])⟩
/-
**IsFractionRing.num_mul_den_eq_num_mul_den_iff_eq** 是 Mathlib 中的一个定理，位于命名空间 `Is
FractionRing`。
形式化陈述：num_mul_den_eq_num_mul_den_iff_eq {x y : K} : num A y * den A x = num A x 
* den A y ↔ x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsFractionRing.mk'_num_den`：∀ (A : Type u_1) [inst : CommRing A] [inst_1
 : IsDomain A] [inst_2 : UniqueFactorizationMonoid A] {K : Type u_2}   [inst_3 :
 Field K] [inst_…
· 使用定理 `IsLocalization.mk'_eq_of_eq'`：∀ {R : Type u_1} [inst : CommSemiring R] {
M : Submonoid R} {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebra R 
S] [inst_3 : IsLoc…
-/
theorem num_mul_den_eq_num_mul_den_iff_eq {x y : K} :
    num A y * den A x = num A x * den A y ↔ x = y :=
  ⟨fun h ↦ by simpa only [mk'_num_den] using mk'_eq_of_eq' (S := K) h, fun h ↦ by rw [h]⟩
/-
**IsFractionRing.eq_zero_of_num_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `IsFractionRin
g`。
形式化陈述：eq_zero_of_num_eq_zero {x : K} (h : num A x = 0) : x = 0
参数：h : num A x = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsFractionRing.num_mul_den_eq_num_iff_eq'`：num_mul_den_eq_num_iff_eq' {x
 y : K} : y * algebraMap A K (den A x) = algebraMap A K (num A x) ↔ x = y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
theorem eq_zero_of_num_eq_zero {x : K} (h : num A x = 0) : x = 0 :=
  (num_mul_den_eq_num_iff_eq' (A := A)).mp (by rw [zero_mul, h, map_zero])

@[simp]
/-
**IsFractionRing.num_zero** 是 Mathlib 中的一个引理，位于命名空间 `IsFractionRing`。
形式化陈述：num_zero : IsFractionRing.num A (0 : K) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsFractionRing.mk'_num_den'`：∀ (A : Type u_1) [inst : CommRing A] [inst_
1 : IsDomain A] [inst_2 : UniqueFactorizationMonoid A] {K : Type u_2}   [inst_3 
: Field K] [inst_…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `IsFractionRing.instFaithfulSMul`：∀ (R : Type u_1) [inst : CommRing R] (K
 : Type u_5) [inst_1 : CommRing K] [inst_2 : Algebra R K] [IsFractionRing R K], 
  FaithfulSMul R K
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma num_zero : IsFractionRing.num A (0 : K) = 0 := by
  have := mk'_num_den' A (0 : K)
  simp only [div_eq_zero_iff] at this
  simp_all

@[simp]
/-
**IsFractionRing.num_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `IsFractionRing`。
形式化陈述：num_eq_zero (x : K) : IsFractionRing.num A x = 0 ↔ x = 0
参数：x : K。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsFractionRing.eq_zero_of_num_eq_zero`：eq_zero_of_num_eq_zero {x : K} (h
 : num A x = 0) : x = 0
· 使用引理 `IsFractionRing.num_zero`：num_zero : IsFractionRing.num A (0 : K) = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma num_eq_zero (x : K) : IsFractionRing.num A x = 0 ↔ x = 0 :=
  ⟨eq_zero_of_num_eq_zero, fun h ↦ h ▸ num_zero⟩
/-
**IsFractionRing.isInteger_of_isUnit_den** 是 Mathlib 中的一个定理，位于命名空间 `IsFractionRi
ng`。
形式化陈述：isInteger_of_isUnit_den {x : K} (h : IsUnit (den A x : A)) : IsInteger A x
参数：h : IsUnit (den A x : A)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors`：∀ {R : Type u_1} [
inst : CommRing R] {K : Type u_5} [inst_1 : CommRing K] [inst_2 : Algebra R K] [
IsFractionRing R K]   [Nontrivial R] {x : …
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用引理 `trans`：trans [IsTrans α r] : a ≺ b -> b ≺ c -> a ≺ c
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `IsPreorder.toIsTrans`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsPreo
rder α r], IsTrans α r
· 使用定理 `IsEquiv.toIsPreorder`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsEqui
v α r], IsPreorder α r
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
· 使用定理 `map_units_inv`：∀ {M : Type u} [inst : Monoid M] {α : Type u_1} [inst_1 :
 DivisionMonoid α] {F : Type u_2} [inst_2 : FunLike F M α]   [MonoidHomClass F M
 α]…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `mul_left_cancel₀`：mul_left_cancel₀ (ha : a != 0) (h : a * b = a * c) : b
 = c
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `IsLocalization.mk'_spec'`：∀ {R : Type u_1} [inst : CommSemiring R] {M : 
Submonoid R} (S : Type u_2) [inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [
inst_3 : IsLoc…
· 使用定理 `IsFractionRing.mk'_num_den`：∀ (A : Type u_1) [inst : CommRing A] [inst_1
 : IsDomain A] [inst_2 : UniqueFactorizationMonoid A] {K : Type u_2}   [inst_3 :
 Field K] [inst_…
-/
theorem isInteger_of_isUnit_den {x : K} (h : IsUnit (den A x : A)) : IsInteger A x := by
  obtain ⟨d, hd⟩ := h
  have d_ne_zero : algebraMap A K (den A x) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (den A x).2
  use ↑d⁻¹ * num A x
  refine _root_.trans ?_ (mk'_num_den A x)
  rw [map_mul, map_units_inv, hd]
  apply mul_left_cancel₀ d_ne_zero
  rw [← mul_assoc, mul_inv_cancel₀ d_ne_zero, one_mul, mk'_spec']
/-
**IsFractionRing.isUnit_den_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsFractionRing`。
形式化陈述：isUnit_den_iff (x : K) : IsUnit (den A x : A) ↔ IsLocalization.IsInteger A
 x where mp
参数：x : K。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsFractionRing.isInteger_of_isUnit_den`：isInteger_of_isUnit_den {x : K} 
(h : IsUnit (den A x : A)) : IsInteger A x
· 使用定理 `IsRelPrime.isUnit_of_dvd`：IsRelPrime.isUnit_of_dvd (H : IsRelPrime x y) 
(d : x ∣ y) : IsUnit x
· 使用定理 `IsRelPrime.symm`：∀ {α : Type u_1} [inst : CommMonoid α] {x y : α}, IsRel
Prime x y → IsRelPrime y x
· 使用定理 `IsFractionRing.num_den_reduced`：num_den_reduced (x : K) : IsRelPrime (nu
m A x) (den A x)
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `IsFractionRing.instFaithfulSMul`：∀ (R : Type u_1) [inst : CommRing R] (K
 : Type u_5) [inst_1 : CommRing K] [inst_2 : Algebra R K] [IsFractionRing R K], 
  FaithfulSMul R K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `div_eq_iff`：div_eq_iff (hb : b != 0) : a / b = c ↔ a = c * b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsFractionRing.mk'_num_den'`：∀ (A : Type u_1) [inst : CommRing A] [inst_
1 : IsDomain A] [inst_2 : UniqueFactorizationMonoid A] {K : Type u_2}   [inst_3 
: Field K] [inst_…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem isUnit_den_iff (x : K) : IsUnit (den A x : A) ↔ IsLocalization.IsInteger A x where
  mp := isInteger_of_isUnit_den
  mpr h := by
    have ⟨v, h⟩ := h
    apply IsRelPrime.isUnit_of_dvd (num_den_reduced A x).symm
    use v
    apply_fun algebraMap A K
    · simp only [map_mul, h]
      rw [mul_comm, ← div_eq_iff]
      · simp only [mk'_num_den']
      simp
    exact FaithfulSMul.algebraMap_injective A K
/-
**IsFractionRing.isUnit_den_zero** 是 Mathlib 中的一个定理，位于命名空间 `IsFractionRing`。
形式化陈述：isUnit_den_zero : IsUnit (den A (0 : K) : A)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
theorem isUnit_den_zero : IsUnit (den A (0 : K) : A) := by
  simp [isUnit_den_iff, IsLocalization.isInteger_zero]
/-
**IsFractionRing.associated_den_num_inv** 是 Mathlib 中的一个引理，位于命名空间 `IsFractionRin
g`。
形式化陈述：associated_den_num_inv (x : K) (hx : x != 0) : Associated (den A x : A) (n
um A x⁻¹)
参数：x : K；hx : x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `associated_of_dvd_dvd`：associated_of_dvd_dvd [MonoidWithZero M] [IsLeftC
ancelMulZero M] {a b : M} (hab : a ∣ b) (hba : b ∣ a) : a ~ᵤ b
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `IsRelPrime.dvd_of_dvd_mul_right`：IsRelPrime.dvd_of_dvd_mul_right (H1 : I
sRelPrime x z) (H2 : x ∣ y * z) : x ∣ y
· 使用定理 `instDecompositionMonoidOfIsGCDMonoid`：∀ {α : Type u_1} [inst : CommMonoi
dWithZero α] [h : IsGCDMonoid α], DecompositionMonoid α
· 使用定理 `instIsGCDMonoidOfUniqueFactorizationMonoid`：∀ (α : Type u_2) [inst : Com
mMonoidWithZero α] [UniqueFactorizationMonoid α], IsGCDMonoid α
· 使用定理 `IsRelPrime.symm`：∀ {α : Type u_1} [inst : CommMonoid α] {x y : α}, IsRel
Prime x y → IsRelPrime y x
· 使用定理 `IsFractionRing.num_den_reduced`：num_den_reduced (x : K) : IsRelPrime (nu
m A x) (den A x)
· 使用定理 `dvd_of_mul_left_dvd`：dvd_of_mul_left_dvd (h : a * b ∣ c) : b ∣ c
· 使用定理 `dvd_of_eq`：dvd_of_eq (h : a = b) : a ∣ b
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `IsFractionRing.instFaithfulSMul`：∀ (R : Type u_1) [inst : CommRing R] (K
 : Type u_5) [inst_1 : CommRing K] [inst_2 : Algebra R K] [IsFractionRing R K], 
  FaithfulSMul R K
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_div_eq_one`：eq_of_div_eq_one (h : a / b = 1) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `mul_div_mul_comm`：mul_div_mul_comm : a * b / (c * d) = a / c * (b / d)
· 使用定理 `IsFractionRing.mk'_num_den'`：∀ (A : Type u_1) [inst : CommRing A] [inst_
1 : IsDomain A] [inst_2 : UniqueFactorizationMonoid A] {K : Type u_2}   [inst_3 
: Field K] [inst_…
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
-/
lemma associated_den_num_inv (x : K) (hx : x ≠ 0) : Associated (den A x : A) (num A x⁻¹) :=
  associated_of_dvd_dvd
    (IsRelPrime.dvd_of_dvd_mul_right (IsFractionRing.num_den_reduced A x).symm <|
      dvd_of_mul_left_dvd (a := (den A x⁻¹ : A)) <| dvd_of_eq <|
      FaithfulSMul.algebraMap_injective A K <| Eq.symm <| eq_of_div_eq_one
      (by simp [mul_div_mul_comm, hx]))
    (IsRelPrime.dvd_of_dvd_mul_right (IsFractionRing.num_den_reduced A x⁻¹) <|
      dvd_of_mul_left_dvd (a := (num A x : A)) <| dvd_of_eq <|
      FaithfulSMul.algebraMap_injective A K <| eq_of_div_eq_one
      (by simp [mul_div_mul_comm, hx]))
/-
**IsFractionRing.associated_num_den_inv** 是 Mathlib 中的一个引理，位于命名空间 `IsFractionRin
g`。
形式化陈述：associated_num_den_inv (x : K) (hx : x != 0) : Associated (num A x : A) (d
en A x⁻¹)
参数：x : K；hx : x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Associated.symm`：∀ {M : Type u_1} [inst : Monoid M] {x y : M}, Associate
d x y → Associated y x
· 使用引理 `IsFractionRing.associated_den_num_inv`：associated_den_num_inv (x : K) (h
x : x != 0) : Associated (den A x : A) (num A x⁻¹)
· 使用定理 `inv_ne_zero`：inv_ne_zero (h : a != 0) : a⁻¹ != 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
-/
lemma associated_num_den_inv (x : K) (hx : x ≠ 0) : Associated (num A x : A) (den A x⁻¹) := by
  have : Associated (num A x⁻¹⁻¹ : A) (den A x⁻¹) :=
    (associated_den_num_inv x⁻¹ (inv_ne_zero hx)).symm
  rw [inv_inv] at this
  exact this

variable (A) in
/-
**IsFractionRing.num_den_unique** 是 Mathlib 中的一个定理，位于命名空间 `IsFractionRing`。
形式化陈述：num_den_unique (x : K) (n : A) (d : nonZeroDivisors A) (pr : IsRelPrime n 
d) (h : IsLocalization.mk' K n d = x) : Associated (num A x) n ∧ Associated (den
 A x : A) d
参数：x : K；n : A；d : nonZeroDivisors A；pr : IsRelPrime n d；h : IsLocalization.mk' 
K n d = x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `associated_of_dvd_dvd`：associated_of_dvd_dvd [MonoidWithZero M] [IsLeftC
ancelMulZero M] {a b : M} (hab : a ∣ b) (hba : b ∣ a) : a ~ᵤ b
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `IsRelPrime.dvd_of_dvd_mul_right`：IsRelPrime.dvd_of_dvd_mul_right (H1 : I
sRelPrime x z) (H2 : x ∣ y * z) : x ∣ y
· 使用定理 `instDecompositionMonoidOfIsGCDMonoid`：∀ {α : Type u_1} [inst : CommMonoi
dWithZero α] [h : IsGCDMonoid α], DecompositionMonoid α
· 使用定理 `instIsGCDMonoidOfUniqueFactorizationMonoid`：∀ (α : Type u_2) [inst : Com
mMonoidWithZero α] [UniqueFactorizationMonoid α], IsGCDMonoid α
· 使用定理 `IsFractionRing.num_den_reduced`：num_den_reduced (x : K) : IsRelPrime (nu
m A x) (den A x)
· 使用定理 `dvd_mul_right`：dvd_mul_right (a b : α) : a ∣ a * b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `Module.IsTorsionFree.to_faithfulSMul`：∀ {R : Type u_1} {A : Type u_2} [i
nst : CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] [IsCancelMulZero R]  
 [Nontrivial A] [Module.Is…
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `FaithfulSMul.to_isTorsionFree`：∀ (R : Type u_1) (A : Type u_3) [inst : C
ommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A] [FaithfulSMul R A]  
 [Nontrivial R] [Is…
· 使用定理 `IsFractionRing.instFaithfulSMul`：∀ (R : Type u_1) [inst : CommRing R] (K
 : Type u_5) [inst_1 : CommRing K] [inst_2 : Algebra R K] [IsFractionRing R K], 
  FaithfulSMul R K
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsLocalization.mk'_eq_iff_eq'`：∀ {R : Type u_1} [inst : CommSemiring R] 
{M : Submonoid R} {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebra R
 S] [inst_3 : IsLoc…
· 使用定理 `IsFractionRing.mk'_num_den`：∀ (A : Type u_1) [inst : CommRing A] [inst_1
 : IsDomain A] [inst_2 : UniqueFactorizationMonoid A] {K : Type u_2}   [inst_3 :
 Field K] [inst_…
· 使用定理 `IsRelPrime.dvd_of_dvd_mul_left`：IsRelPrime.dvd_of_dvd_mul_left (H1 : IsR
elPrime x y) (H2 : x ∣ y * z) : x ∣ z
· 使用定理 `IsRelPrime.symm`：∀ {α : Type u_1} [inst : CommMonoid α] {x y : α}, IsRel
Prime x y → IsRelPrime y x
· 使用定理 `dvd_mul_left`：dvd_mul_left (a b : α) : a ∣ b * a
-/
theorem num_den_unique (x : K) (n : A) (d : nonZeroDivisors A) (pr : IsRelPrime n d)
    (h : IsLocalization.mk' K n d = x) :
    Associated (num A x) n ∧ Associated (den A x : A) d := by
  rw [← IsFractionRing.mk'_num_den A x, IsLocalization.mk'_eq_iff_eq',
    (FaithfulSMul.algebraMap_injective _ _).eq_iff] at h
  refine ⟨associated_of_dvd_dvd
      ((num_den_reduced A x).dvd_of_dvd_mul_right <| h ▸ dvd_mul_right _ _)
      (pr.dvd_of_dvd_mul_right <| h ▸ dvd_mul_right _ _),
    associated_of_dvd_dvd
      ((num_den_reduced A x).symm.dvd_of_dvd_mul_left <| h ▸ dvd_mul_left _ _)
      (pr.symm.dvd_of_dvd_mul_left <| h ▸ dvd_mul_left _ _)⟩


end NumDen

end IsFractionRing

