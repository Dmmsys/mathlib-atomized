/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro, Johan Commelin, Amelia Livingston, Anne Baanen
-/
module

public import Mathlib.Algebra.Group.Pointwise.Set.Scalar
public import Mathlib.Algebra.Ring.Subsemiring.Basic
public import Mathlib.RingTheory.Localization.Defs

/-!
# Integer elements of a localization

## Main definitions

* `IsLocalization.IsInteger` is a predicate stating that `x : S` is in the image of `R`

## Implementation notes

See `Mathlib/RingTheory/Localization/Basic.lean` for a design overview.

## Tags
localization, ring localization, commutative ring localization, characteristic predicate,
commutative ring, field of fractions
-/

@[expose] public section


variable {R : Type*} [CommSemiring R] {M : Submonoid R} {S : Type*} [CommSemiring S]
variable [Algebra R S] {P : Type*} [CommSemiring P]

open Function

namespace IsLocalization

section

variable (R)

-- TODO: define a subalgebra of `IsInteger`s
/-- Given `a : S`, `S` a localization of `R`, `IsInteger R a` iff `a` is in the image of
the localization map from `R` to `S`. -/
/-
**IsLocalization.IsInteger** 是 Mathlib 中的一个定义，位于命名空间 `IsLocalization`。
形式化陈述：IsInteger (a : S) : Prop
参数：a : S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `a : S`, `S` a localization of `R`, `IsInteger R a` iff `a` is in the imag
e of
the localization map from `R` to `S`.
-/
def IsInteger (a : S) : Prop :=
  a ∈ (algebraMap R S).rangeS

end

/-
**IsLocalization.isInteger_zero** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：isInteger_zero : IsInteger R (0 : S)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsemiring.zero_mem`：∀ {R : Type u} [inst : NonAssocSemiring R] (s : Su
bsemiring R), 0 ∈ s
-/
theorem isInteger_zero : IsInteger R (0 : S) :=
  Subsemiring.zero_mem _
/-
**IsLocalization.isInteger_one** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：isInteger_one : IsInteger R (1 : S)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsemiring.one_mem`：∀ {R : Type u} [inst : NonAssocSemiring R] (s : Sub
semiring R), 1 ∈ s
-/
theorem isInteger_one : IsInteger R (1 : S) :=
  Subsemiring.one_mem _
/-
**IsLocalization.isInteger_add** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：isInteger_add {a b : S} (ha : IsInteger R a) (hb : IsInteger R b) : IsInte
ger R (a + b)
参数：ha : IsInteger R a；hb : IsInteger R b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsemiring.add_mem`：∀ {R : Type u} [inst : NonAssocSemiring R] (s : Sub
semiring R) {x y : R}, x ∈ s → y ∈ s → x + y ∈ s
-/
theorem isInteger_add {a b : S} (ha : IsInteger R a) (hb : IsInteger R b) : IsInteger R (a + b) :=
  Subsemiring.add_mem _ ha hb
/-
**IsLocalization.isInteger_mul** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：isInteger_mul {a b : S} (ha : IsInteger R a) (hb : IsInteger R b) : IsInte
ger R (a * b)
参数：ha : IsInteger R a；hb : IsInteger R b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsemiring.mul_mem`：∀ {R : Type u} [inst : NonAssocSemiring R] (s : Sub
semiring R) {x y : R}, x ∈ s → y ∈ s → x * y ∈ s
-/
theorem isInteger_mul {a b : S} (ha : IsInteger R a) (hb : IsInteger R b) : IsInteger R (a * b) :=
  Subsemiring.mul_mem _ ha hb
/-
**IsLocalization.isInteger_smul** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：isInteger_smul {a : R} {b : S} (hb : IsInteger R b) : IsInteger R (a • b)
参数：hb : IsInteger R b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHom.map_mul`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring α
} {x_1 : NonAssocSemiring β} (f : α →+* β) (a b : α),   f (a * b) = f a * f b
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
-/
theorem isInteger_smul {a : R} {b : S} (hb : IsInteger R b) : IsInteger R (a • b) := by
  rcases hb with ⟨b', hb⟩
  use a * b'
  rw [← hb, (algebraMap R S).map_mul, Algebra.smul_def]

variable (M)
variable [IsLocalization M S]

/-- Each element `a : S` has an `M`-multiple which is an integer.

This version multiplies `a` on the right, matching the argument order in `LocalizationMap.surj`.
-/
/-
**IsLocalization.exists_integer_multiple'** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalizat
ion`。
形式化陈述：exists_integer_multiple' (a : S) : exists b : M, IsInteger R (a * algebraM
ap R S b)
参数：a : S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalization.surj`：surj : forall z : S, exists x : R × M, z * algebraM
ap R S x.2 = algebraMap R S x.1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_range`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} {x : α}, x ∈ Se
t.range f ↔ ∃ y, f y = x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
Each element `a : S` has an `M`-multiple which is an integer.

This version multiplies `a` on the right, matching the argument order in `Locali
zationMap.surj`.
-/
theorem exists_integer_multiple' (a : S) : ∃ b : M, IsInteger R (a * algebraMap R S b) :=
  let ⟨⟨Num, denom⟩, h⟩ := IsLocalization.surj _ a
  ⟨denom, Set.mem_range.mpr ⟨Num, h.symm⟩⟩

/-- Each element `a : S` has an `M`-multiple which is an integer.

This version multiplies `a` on the left, matching the argument order in the `SMul` instance.
-/
/-
**IsLocalization.exists_integer_multiple** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalizati
on`。
形式化陈述：exists_integer_multiple (a : S) : exists b : M, IsInteger R ((b : R) • a)
参数：a : S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `IsLocalization.exists_integer_multiple'`：exists_integer_multiple' (a : S
) : exists b : M, IsInteger R (a * algebraMap R S b)

--- 原说明 ---
Each element `a : S` has an `M`-multiple which is an integer.

This version multiplies `a` on the left, matching the argument order in the `SMu
l` instance.
-/
theorem exists_integer_multiple (a : S) : ∃ b : M, IsInteger R ((b : R) • a) := by
  simp_rw [Algebra.smul_def, mul_comm _ a]
  apply exists_integer_multiple'

/-- We can clear the denominators of a `Finset`-indexed family of fractions. -/
/-
**IsLocalization.exist_integer_multiples** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalizati
on`。
形式化陈述：exist_integer_multiples {ι : Type*} (s : Finset ι) (f : ι -> S) : exists b
 : M, forall i in s, IsLocalization.IsInteger R ((b : R) • f i)
参数：s : Finset ι；f : ι -> S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `IsLocalization.sec_spec'`：sec_spec' (z : S) : algebraMap R S (IsLocaliza
tion.sec M z).1 = algebraMap R S (IsLocalization.sec M z).2 * z
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `RingHom.map_mul`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring α
} {x_1 : NonAssocSemiring β} (f : α →+* β) (a b : α),   f (a * b) = f a * f b
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用引理 `trans`：trans [IsTrans α r] : a ≺ b -> b ≺ c -> a ≺ c
· 使用定理 `IsPreorder.toIsTrans`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsPreo
rder α r], IsTrans α r
· 使用定理 `IsEquiv.toIsPreorder`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsEqui
v α r], IsPreorder α r
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Submonoid.coe_finsetProd`：coe_finsetProd {ι M} [CommMonoid M] (S : Submo
noid M) (f : ι -> S) (s : Finset ι) : ↑(∏ i in s, f i) = (∏ i in s, f i : M)
· 使用定理 `Finset.prod_insert`：prod_insert [DecidableEq ι] : a ∉ s -> ∏ x in insert
 a s, f x = f a * ∏ x in s, f x
· 使用定理 `Finset.notMem_erase`：notMem_erase (a : α) (s : Finset α) : a ∉ erase s a
· 使用定理 `Finset.insert_erase`：∀ {α : Type u_1} [inst : DecidableEq α] {s : Finset
 α} {a : α}, a ∈ s → insert a (s.erase a) = s
· 使用定理 `map_prod`：map_prod [CommMonoid M] [CommMonoid N] {G : Type*} [FunLike G 
M N] [MonoidHomClass G M N] (g : G) (f : ι -> M) (s : Finset ι) : g (∏ x in s,…

--- 原说明 ---
We can clear the denominators of a `Finset`-indexed family of fractions.
-/
theorem exist_integer_multiples {ι : Type*} (s : Finset ι) (f : ι → S) :
    ∃ b : M, ∀ i ∈ s, IsLocalization.IsInteger R ((b : R) • f i) := by
  have := Classical.propDecidable
  refine ⟨∏ i ∈ s, (sec M (f i)).2, fun i hi => ⟨?_, ?_⟩⟩
  · exact (∏ j ∈ s.erase i, (sec M (f j)).2) * (sec M (f i)).1
  rw [map_mul, sec_spec', ← mul_assoc, ← (algebraMap R S).map_mul, ← Algebra.smul_def]
  congr 2
  refine _root_.trans ?_ (map_prod (Submonoid.subtype M) _ _).symm
  rw [mul_comm, Submonoid.coe_finsetProd,
    -- Porting note: explicitly supplied `f`
    ← Finset.prod_insert (f := fun i => ((sec M (f i)).snd : R)) (s.notMem_erase i),
    Finset.insert_erase hi]
  rfl

/-- We can clear the denominators of a finite indexed family of fractions. -/
/-
**IsLocalization.exist_integer_multiples_of_finite** 是 Mathlib 中的一个定理，位于命名空间 `Is
Localization`。
形式化陈述：exist_integer_multiples_of_finite {ι : Type*} [Finite ι] (f : ι -> S) : ex
ists b : M, forall i, IsLocalization.IsInteger R ((b : R) • f i)
参数：f : ι -> S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `IsLocalization.exist_integer_multiples`：exist_integer_multiples {ι : Typ
e*} (s : Finset ι) (f : ι -> S) : exists b : M, forall i in s, IsLocalization.Is
Integer R ((b : R) • f i)
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)

--- 原说明 ---
We can clear the denominators of a finite indexed family of fractions.
-/
theorem exist_integer_multiples_of_finite {ι : Type*} [Finite ι] (f : ι → S) :
    ∃ b : M, ∀ i, IsLocalization.IsInteger R ((b : R) • f i) := by
  cases nonempty_fintype ι
  obtain ⟨b, hb⟩ := exist_integer_multiples M Finset.univ f
  exact ⟨b, fun i => hb i (Finset.mem_univ _)⟩

/-- We can clear the denominators of a finite set of fractions. -/
/-
**IsLocalization.exist_integer_multiples_of_finset** 是 Mathlib 中的一个定理，位于命名空间 `Is
Localization`。
形式化陈述：exist_integer_multiples_of_finset (s : Finset S) : exists b : M, forall a 
in s, IsInteger R ((b : R) • a)
参数：s : Finset S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalization.exist_integer_multiples`：exist_integer_multiples {ι : Typ
e*} (s : Finset ι) (f : ι -> S) : exists b : M, forall i in s, IsLocalization.Is
Integer R ((b : R) • f i)

--- 原说明 ---
We can clear the denominators of a finite set of fractions.
-/
theorem exist_integer_multiples_of_finset (s : Finset S) :
    ∃ b : M, ∀ a ∈ s, IsInteger R ((b : R) • a) :=
  exist_integer_multiples M s id

/-- A choice of a common multiple of the denominators of a `Finset`-indexed family of fractions. -/
/-
**IsLocalization.commonDenom** 是 Mathlib 中的一个定义，位于命名空间 `IsLocalization`。
形式化陈述：commonDenom {ι : Type*} (s : Finset ι) (f : ι -> S) : M
参数：s : Finset ι；f : ι -> S。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalization.exist_integer_multiples`：exist_integer_multiples {ι : Typ
e*} (s : Finset ι) (f : ι -> S) : exists b : M, forall i in s, IsLocalization.Is
Integer R ((b : R) • f i)

--- 原说明 ---
A choice of a common multiple of the denominators of a `Finset`-indexed family o
f fractions.
-/
noncomputable def commonDenom {ι : Type*} (s : Finset ι) (f : ι → S) : M :=
  (exist_integer_multiples M s f).choose

/-- The numerator of a fraction after clearing the denominators
of a `Finset`-indexed family of fractions. -/
/-
**IsLocalization.integerMultiple** 是 Mathlib 中的一个定义，位于命名空间 `IsLocalization`。
形式化陈述：integerMultiple {ι : Type*} (s : Finset ι) (f : ι -> S) (i : s) : R
参数：s : Finset ι；f : ι -> S；i : s。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalization.exist_integer_multiples`：exist_integer_multiples {ι : Typ
e*} (s : Finset ι) (f : ι -> S) : exists b : M, forall i in s, IsLocalization.Is
Integer R ((b : R) • f i)

--- 原说明 ---
The numerator of a fraction after clearing the denominators
of a `Finset`-indexed family of fractions.
-/
noncomputable def integerMultiple {ι : Type*} (s : Finset ι) (f : ι → S) (i : s) : R :=
  ((exist_integer_multiples M s f).choose_spec i i.prop).choose

@[simp]
/-
**IsLocalization.map_integerMultiple** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：map_integerMultiple {ι : Type*} (s : Finset ι) (f : ι -> S) (i : s) : alge
braMap R S (integerMultiple M s f i) = commonDenom M s f • f i
参数：s : Finset ι；f : ι -> S；i : s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `IsLocalization.exist_integer_multiples`：exist_integer_multiples {ι : Typ
e*} (s : Finset ι) (f : ι -> S) : exists b : M, forall i in s, IsLocalization.Is
Integer R ((b : R) • f i)
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
-/
theorem map_integerMultiple {ι : Type*} (s : Finset ι) (f : ι → S) (i : s) :
    algebraMap R S (integerMultiple M s f i) = commonDenom M s f • f i :=
  ((exist_integer_multiples M s f).choose_spec _ i.prop).choose_spec
/-
**IsLocalization.integerMultiple_injective** 是 Mathlib 中的一个定理，位于命名空间 `IsLocaliza
tion`。
形式化陈述：integerMultiple_injective {ι : Type*} (s : Finset ι) (f : ι -> S) (hf : Fu
nction.Injective f) : Function.Injective (integerMultiple M s f)
参数：s : Finset ι；f : ι -> S；hf : Function.Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SetLike.coe_eq_coe`：coe_eq_coe {x y : p} : (x : B) = y ↔ x = y
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Function.Bijective.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β
}, Function.Bijective f → Function.Injective f
· 使用定理 `IsLocalization.smul_bijective`：smul_bijective (m : M) : Bijective fun s 
: S => m • s
· 使用定理 `IsLocalization.map_integerMultiple`：map_integerMultiple {ι : Type*} (s :
 Finset ι) (f : ι -> S) (i : s) : algebraMap R S (integerMultiple M s f i) = com
monDenom M s f • f i
-/
theorem integerMultiple_injective {ι : Type*} (s : Finset ι) (f : ι → S)
    (hf : Function.Injective f) : Function.Injective (integerMultiple M s f) := by
  intro i j h
  rw [← SetLike.coe_eq_coe, ← hf.eq_iff,
    ← (IsLocalization.smul_bijective S (commonDenom M s f)).injective.eq_iff,
    ← map_integerMultiple M s f i, ← map_integerMultiple M s f j, h]

@[deprecated (since := "2026-07-18")] alias integerMultipleMultiple_injective :=
  integerMultiple_injective

/-- A choice of a common multiple of the denominators of a finite set of fractions. -/
/-
**IsLocalization.commonDenomOfFinset** 是 Mathlib 中的一个定义，位于命名空间 `IsLocalization`。
形式化陈述：commonDenomOfFinset (s : Finset S) : M
参数：s : Finset S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A choice of a common multiple of the denominators of a finite set of fractions.
-/
noncomputable def commonDenomOfFinset (s : Finset S) : M :=
  commonDenom M s id

/-- The finset of numerators after clearing the denominators of a finite set of fractions. -/
/-
**IsLocalization.finsetIntegerMultiple** 是 Mathlib 中的一个定义，位于命名空间 `IsLocalization
`。
形式化陈述：finsetIntegerMultiple [DecidableEq R] (s : Finset S) : Finset R
参数：s : Finset S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The finset of numerators after clearing the denominators of a finite set of frac
tions.
-/
noncomputable def finsetIntegerMultiple [DecidableEq R] (s : Finset S) : Finset R :=
  s.attach.image fun t => integerMultiple M s id t

open scoped Pointwise
/-
**IsLocalization.finsetIntegerMultiple_image** 是 Mathlib 中的一个定理，位于命名空间 `IsLocali
zation`。
形式化陈述：finsetIntegerMultiple_image [DecidableEq R] (s : Finset S) : algebraMap R 
S '' finsetIntegerMultiple M s = commonDenomOfFinset M s • (s : Set S)
参数：s : Finset S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `IsLocalization.map_integerMultiple`：map_integerMultiple {ι : Type*} (s :
 Finset ι) (f : ι -> S) (i : s) : algebraMap R S (integerMultiple M s f i) = com
monDenom M s f • f i
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `Finset.mem_attach`：mem_attach (s : Finset α) : forall x, x in s.attach
-/
theorem finsetIntegerMultiple_image [DecidableEq R] (s : Finset S) :
    algebraMap R S '' finsetIntegerMultiple M s = commonDenomOfFinset M s • (s : Set S) := by
  delta finsetIntegerMultiple commonDenom
  rw [Finset.coe_image]
  ext
  constructor
  · rintro ⟨_, ⟨x, -, rfl⟩, rfl⟩
    rw [map_integerMultiple]
    exact Set.mem_image_of_mem _ x.prop
  · rintro ⟨x, hx, rfl⟩
    exact ⟨_, ⟨⟨x, hx⟩, s.mem_attach _, rfl⟩, map_integerMultiple M s id _⟩

@[simp]
/-
**IsLocalization.card_finsetIntegerMultiple** 是 Mathlib 中的一个定理，位于命名空间 `IsLocaliz
ation`。
形式化陈述：card_finsetIntegerMultiple [DecidableEq R] (s : Finset S) : (finsetInteger
Multiple M s).card = s.card
参数：s : Finset S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.card_image_of_injective`：card_image_of_injective [DecidableEq β] 
(s : Finset α) (H : Injective f) : #(s.image f) = #s
· 使用定理 `IsLocalization.integerMultiple_injective`：integerMultiple_injective {ι :
 Type*} (s : Finset ι) (f : ι -> S) (hf : Function.Injective f) : Function.Injec
tive (integerMultiple M s f)
· 使用定理 `Function.injective_id`：∀ {α : Sort u_1}, Function.Injective id
· 使用定理 `Finset.card_attach`：card_attach : #s.attach = #s
-/
theorem card_finsetIntegerMultiple [DecidableEq R] (s : Finset S) :
    (finsetIntegerMultiple M s).card = s.card :=
  (Finset.card_image_of_injective _ (integerMultiple_injective M s id injective_id)).trans
    Finset.card_attach

end IsLocalization

