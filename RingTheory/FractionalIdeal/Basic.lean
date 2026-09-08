/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Filippo A. E. Nuccio
-/
module

public import Mathlib.RingTheory.Localization.Integer
public import Mathlib.RingTheory.Localization.Submodule

/-!
# Fractional ideals

This file defines fractional ideals of an integral domain and proves basic facts about them.

## Main definitions
Let `S` be a submonoid of an integral domain `R` and `P` the localization of `R` at `S`.
* `IsFractional` defines which `R`-submodules of `P` are fractional ideals
* `FractionalIdeal S P` is the type of fractional ideals in `P`
* a coercion `coeIdeal : Ideal R → FractionalIdeal S P`
* `CommSemiring (FractionalIdeal S P)` instance:
  the typical ideal operations generalized to fractional ideals
* `Lattice (FractionalIdeal S P)` instance

## Main statements

  * the `MulLeftMono` and `MulRightMono` instances state that ideal multiplication is monotone
  * `mul_div_self_cancel_iff` states that `1 / I` is the inverse of `I` if one exists

## Implementation notes

Fractional ideals are considered equal when they contain the same elements,
independent of the denominator `a : R` such that `a I ⊆ R`.
Thus, we define `FractionalIdeal` to be the subtype of the predicate `IsFractional`,
instead of having `FractionalIdeal` be a structure of which `a` is a field.

Most definitions in this file specialize operations from submodules to fractional ideals,
proving that the result of this operation is fractional if the input is fractional.
Exceptions to this rule are defining `(+) := (⊔)` and `⊥ := 0`,
in order to reuse their respective proof terms.
We can still use `simp` to show `↑I + ↑J = ↑(I + J)` and `↑⊥ = ↑0`.

Many results in fact do not need that `P` is a localization, only that `P` is an
`R`-algebra. We omit the `IsLocalization` parameter whenever this is practical.
Similarly, we don't assume that the localization is a field until we need it to
define ideal quotients. When this assumption is needed, we replace `S` with `R⁰`,
making the localization a field.

## References

  * https://en.wikipedia.org/wiki/Fractional_ideal

## Tags

fractional ideal, fractional ideals, invertible ideal
-/

@[expose] public section


open IsLocalization Pointwise nonZeroDivisors

section Defs

variable {R : Type*} [CommRing R] {S : Submonoid R} {P : Type*} [CommRing P]
variable [Algebra R P]
variable (S)

/-- A submodule `I` is a fractional ideal with respect to a submonoid `S`
if `a I ⊆ R` for some `a ∈ S`. -/
/-
**IsFractional** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsFractional (I : Submodule R P)
参数：I : Submodule R P。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A submodule `I` is a fractional ideal with respect to a submonoid `S`
if `a I ⊆ R` for some `a ∈ S`.
-/
def IsFractional (I : Submodule R P) :=
  ∃ a ∈ S, ∀ b ∈ I, IsInteger R (a • b)

variable (P)

/-- The fractional ideals of a domain `R` are ideals of `R` divided by some `a ∈ R`.

More precisely, let `P` be a localization of `R` at some submonoid `S`,
then a fractional ideal `I ⊆ P` is an `R`-submodule of `P`,
such that there is an `a ∈ S` with `a I ⊆ R`.
-/
@[wikidata Q1497184]
/-
**FractionalIdeal** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：FractionalIdeal
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The fractional ideals of a domain `R` are ideals of `R` divided by some `a ∈ R`.

More precisely, let `P` be a localization of `R` at some submonoid `S`,
then a fractional ideal `I ⊆ P` is an `R`-submodule of `P`,
such that there is an `a ∈ S` with `a I ⊆ R`.
-/
def FractionalIdeal :=
  { I : Submodule R P // IsFractional S I }

end Defs

namespace FractionalIdeal

open Set Submodule

variable {R : Type*} [CommRing R] {S : Submonoid R} {P : Type*} [CommRing P]
variable [Algebra R P]

/-- Map a fractional ideal `I` to a submodule by forgetting that `∃ a, a I ⊆ R`.

This implements the coercion `FractionalIdeal S P → Submodule R P`.
-/
@[coe]
/-
**FractionalIdeal.coeToSubmodule** 是 Mathlib 中的一个定义，位于命名空间 `FractionalIdeal`。
形式化陈述：coeToSubmodule (I : FractionalIdeal S P) : Submodule R P
参数：I : FractionalIdeal S P。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Map a fractional ideal `I` to a submodule by forgetting that `∃ a, a I ⊆ R`.

This implements the coercion `FractionalIdeal S P → Submodule R P`.
-/
def coeToSubmodule (I : FractionalIdeal S P) : Submodule R P :=
  I.val

/-- Map a fractional ideal `I` to a submodule by forgetting that `∃ a, a I ⊆ R`.

This coercion is typically called `coeToSubmodule` in lemma names
(or `coe` when the coercion is clear from the context),
not to be confused with `IsLocalization.coeSubmodule : Ideal R → Submodule R P`
(which we use to define `coe : Ideal R → FractionalIdeal S P`).
-/
/-
**FractionalIdeal.** 是 Mathlib 中的一个实例，位于命名空间 `FractionalIdeal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Map a fractional ideal `I` to a submodule by forgetting that `∃ a, a I ⊆ R`.

This coercion is typically called `coeToSubmodule` in lemma names
(or `coe` when the coercion is clear from the context),
not to be confused with `IsLocalization.coeSubmodule : Ideal R → Submodule R P`
(which we use to define `coe : Ideal R → FractionalIdeal S P`).
-/
instance : CoeOut (FractionalIdeal S P) (Submodule R P) :=
  ⟨coeToSubmodule⟩
/-
**FractionalIdeal.isFractional** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {S : Submonoid R} {P : Type u_2} [ins
t_1 : CommRing P] [inst_2 : Algebra R P]   (I : FractionalIdeal S P), IsFraction
al S ↑I
参数：I : FractionalIdeal S P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
-/
protected theorem isFractional (I : FractionalIdeal S P) : IsFractional S (I : Submodule R P) :=
  I.prop

/-- An element of `S` such that `I.den • I = I.num`, see `FractionalIdeal.num` and
`FractionalIdeal.den_mul_self_eq_num`. -/
/-
**FractionalIdeal.den** 是 Mathlib 中的一个定义，位于命名空间 `FractionalIdeal`。
形式化陈述：den (I : FractionalIdeal S P) : S
参数：I : FractionalIdeal S P。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An element of `S` such that `I.den • I = I.num`, see `FractionalIdeal.num` and
`FractionalIdeal.den_mul_self_eq_num`.
-/
noncomputable def den (I : FractionalIdeal S P) : S :=
  ⟨I.2.choose, I.2.choose_spec.1⟩

/-- An ideal of `R` such that `I.den • I = I.num`, see `FractionalIdeal.den` and
`FractionalIdeal.den_mul_self_eq_num`. -/
/-
**FractionalIdeal.num** 是 Mathlib 中的一个定义，位于命名空间 `FractionalIdeal`。
形式化陈述：num (I : FractionalIdeal S P) : Ideal R
参数：I : FractionalIdeal S P。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An ideal of `R` such that `I.den • I = I.num`, see `FractionalIdeal.den` and
`FractionalIdeal.den_mul_self_eq_num`.
-/
noncomputable def num (I : FractionalIdeal S P) : Ideal R :=
  (I.den • (I : Submodule R P)).comap (Algebra.linearMap R P)
/-
**FractionalIdeal.den_mul_self_eq_num** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal
`。
形式化陈述：den_mul_self_eq_num (I : FractionalIdeal S P) : I.den • (I : Submodule R P
) = Submodule.map (Algebra.linearMap R P) I.num
参数：I : FractionalIdeal S P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FractionalIdeal.den.eq_1`：∀ {R : Type u_1} [inst : CommRing R] {S : Subm
onoid R} {P : Type u_2} [inst_1 : CommRing P] [inst_2 : Algebra R P]   (I : Frac
tionalIdeal S …
· 使用定理 `FractionalIdeal.num.eq_1`：∀ {R : Type u_1} [inst : CommRing R] {S : Subm
onoid R} {P : Type u_2} [inst_1 : CommRing P] [inst_2 : Algebra R P]   (I : Frac
tionalIdeal S …
· 使用定理 `Submodule.map_comap_eq`：∀ {R : Type u_1} {R₂ : Type u_2} {M : Type u_5} 
{M₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddCommMo
noid M] [ins…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inf_of_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, b ≤
 a → a ⊓ b = b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
theorem den_mul_self_eq_num (I : FractionalIdeal S P) :
    I.den • (I : Submodule R P) = Submodule.map (Algebra.linearMap R P) I.num := by
  rw [den, num, Submodule.map_comap_eq]
  refine (inf_of_le_right ?_).symm
  rintro _ ⟨a, ha, rfl⟩
  exact I.2.choose_spec.2 a ha

/-- The linear equivalence between the fractional ideal `I` and the integral ideal `I.num`
defined by mapping `x` to `I.den • x`, assuming scalar multiplication by `I.den` is injective. -/
/-
**FractionalIdeal.equivNumOfIsSMulRegular** 是 Mathlib 中的一个缩写定义，位于命名空间 `Fractiona
lIdeal`。
形式化陈述：equivNumOfIsSMulRegular [FaithfulSMul R P] {I : FractionalIdeal S P} (reg 
: IsSMulRegular P I.den) : I ≃ₗ[R] I.num
参数：reg : IsSMulRegular P I.den。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The linear equivalence between the fractional ideal `I` and the integral ideal `
I.num`
defined by mapping `x` to `I.den • x`, assuming scalar multiplication by `I.den`
 is injective.
-/
noncomputable abbrev equivNumOfIsSMulRegular [FaithfulSMul R P] {I : FractionalIdeal S P}
    (reg : IsSMulRegular P I.den) : I ≃ₗ[R] I.num := by
  refine LinearEquiv.trans
    (LinearEquiv.ofBijective ((DistribSMul.toLinearMap R P I.den).restrict fun _ hx ↦ ?_)
      ⟨fun _ _ hxy ↦ ?_, fun ⟨y, hy⟩ ↦ ?_⟩)
    (Submodule.equivMapOfInjective (Algebra.linearMap R P)
      (FaithfulSMul.algebraMap_injective R P) (num I)).symm
  · rw [← den_mul_self_eq_num]
    exact Submodule.smul_mem_pointwise_smul _ _ _ hx
  · simpa [LinearMap.restrict_apply, reg.eq_iff] using hxy
  · rw [← den_mul_self_eq_num] at hy
    obtain ⟨x, hx, hxy⟩ := hy
    exact ⟨⟨x, hx⟩, by simp_rw [LinearMap.restrict_apply, Subtype.ext_iff, ← hxy]; rfl⟩

/-- The linear equivalence between the fractional ideal `I` and the integral ideal `I.num`
defined by mapping `x` to `I.den • x`. -/
/-
**FractionalIdeal.equivNum** 是 Mathlib 中的一个定义，位于命名空间 `FractionalIdeal`。
形式化陈述：equivNum [IsDomain R] [Module.IsTorsionFree R P] [Nontrivial P] {I : Fract
ionalIdeal S P} (h_nz : (I.den : R) != 0) : I ≃ₗ[R] I.num
参数：h_nz : (I.den : R) != 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The linear equivalence between the fractional ideal `I` and the integral ideal `
I.num`
defined by mapping `x` to `I.den • x`.
-/
noncomputable def equivNum [IsDomain R] [Module.IsTorsionFree R P] [Nontrivial P]
    {I : FractionalIdeal S P} (h_nz : (I.den : R) ≠ 0) : I ≃ₗ[R] I.num :=
  equivNumOfIsSMulRegular (smul_right_injective P h_nz)

/-- The linear equivalence between the fractional ideal `I` in a faithful localization
and the integral ideal `I.num`. -/
/-
**FractionalIdeal.equivNumOfIsLocalization** 是 Mathlib 中的一个定义，位于命名空间 `Fractional
Ideal`。
形式化陈述：equivNumOfIsLocalization [FaithfulSMul R P] [IsLocalization S P] (I : Frac
tionalIdeal S P) : I ≃ₗ[R] I.num
参数：I : FractionalIdeal S P。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The linear equivalence between the fractional ideal `I` in a faithful localizati
on
and the integral ideal `I.num`.
-/
noncomputable def equivNumOfIsLocalization [FaithfulSMul R P] [IsLocalization S P]
    (I : FractionalIdeal S P) : I ≃ₗ[R] I.num :=
  equivNumOfIsSMulRegular (smul_bijective ..).1

section SetLike

/-
**FractionalIdeal.** 是 Mathlib 中的一个实例，位于命名空间 `FractionalIdeal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SetLike (FractionalIdeal S P) P where
  coe I := ↑(I : Submodule R P)
  coe_injective := SetLike.coe_injective.comp Subtype.coe_injective
/-
**FractionalIdeal.** 是 Mathlib 中的一个实例，位于命名空间 `FractionalIdeal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PartialOrder (FractionalIdeal S P) := .ofSetLike (FractionalIdeal S P) P

@[simp]
/-
**FractionalIdeal.mem_coe** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：mem_coe {I : FractionalIdeal S P} {x : P} : x in (I : Submodule R P) ↔ x i
n I
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_coe {I : FractionalIdeal S P} {x : P} : x ∈ (I : Submodule R P) ↔ x ∈ I :=
  Iff.rfl

/-- Partially-applied version of `FractionalIdeal.ext`. -/
/-
**FractionalIdeal.coe_ext** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：coe_ext {I J : FractionalIdeal S P} : (I : Submodule R P) = (J : Submodule
 R P) -> I = J
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2

--- 原说明 ---
Partially-applied version of `FractionalIdeal.ext`.
-/
theorem coe_ext {I J : FractionalIdeal S P} : (I : Submodule R P) = (J : Submodule R P) → I = J :=
  Subtype.ext

/-- Partially-applied version of `FractionalIdeal.ext_iff`. -/
/-
**FractionalIdeal.coe_ext_iff** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：coe_ext_iff {I J : FractionalIdeal S P} : I = J ↔ (I : Submodule R P) = (J
 : Submodule R P)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2

--- 原说明 ---
Partially-applied version of `FractionalIdeal.ext_iff`.
-/
theorem coe_ext_iff {I J : FractionalIdeal S P} :
    I = J ↔ (I : Submodule R P) = (J : Submodule R P) :=
  Subtype.ext_iff

@[ext]
/-
**FractionalIdeal.ext** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：ext {I J : FractionalIdeal S P} : (forall x, x in I ↔ x in J) -> I = J
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
-/
theorem ext {I J : FractionalIdeal S P} : (∀ x, x ∈ I ↔ x ∈ J) → I = J :=
  SetLike.ext

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**FractionalIdeal.equivNum_apply** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：equivNum_apply [IsDomain R] [Module.IsTorsionFree R P] [Nontrivial P] {I :
 FractionalIdeal S P} (h_nz : (I.den : R) != 0) (x : I) : algebraMap R P (equivN
um h_nz x) = I.den • x
参数：h_nz : (I.den : R) != 0；x : I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FractionalIdeal.equivNum.eq_1`：∀ {R : Type u_1} [inst : CommRing R] {S :
 Submonoid R} {P : Type u_2} [inst_1 : CommRing P] [inst_2 : Algebra R P]   [ins
t_3 : IsDomain R] […
· 使用定理 `LinearEquiv.trans_apply`：trans_apply (c : M₁) : (e₁₂.trans e₂₃ : M₁ ≃ₛₗ[
σ₁₃] M₃) c = e₂₃ (e₁₂ c)
· 使用定理 `LinearEquiv.ofBijective_apply`：ofBijective_apply [RingHomInvPair σ₁₂ σ₂₁
] [RingHomInvPair σ₂₁ σ₁₂] {hf} (x : M) : ofBijective f hf x = f x
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `LinearMap.restrict_apply`：restrict_apply {f : M ->ₛₗ[σ₁₂] M₂} {p : Submo
dule R M} {q : Submodule R₂ M₂} (hf : forall x in p, f x in q) (x : p) : f.restr
ict hf x = ⟨f …
· 使用定理 `RingHomSurjective.invPair`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Sem
iring R₁] [inst_1 : Semiring R₂] {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁}   [RingHomInv
Pair σ₁ σ₂], Ri…
· 使用定理 `Submodule.map_equivMapOfInjective_symm_apply`：map_equivMapOfInjective_sy
mm_apply (f : M ->ₛₗ[σ₁₂] M₂) (i : Injective f) (p : Submodule R M) (x : p.map f
) : f ((equivMapOfInjective f i p)…
· 使用定理 `Subtype.coe_mk`：coe_mk (a h) : (@mk α p a h : α) = a
· 使用定理 `DistribSMul.toLinearMap_apply`：∀ (R : Type u_1) {S : Type u_3} (M : Type
 u_4) [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R
 M] [inst_3 : Distr…
-/
theorem equivNum_apply [IsDomain R] [Module.IsTorsionFree R P] [Nontrivial P]
    {I : FractionalIdeal S P} (h_nz : (I.den : R) ≠ 0) (x : I) :
    algebraMap R P (equivNum h_nz x) = I.den • x := by
  change Algebra.linearMap R P _ = _
  rw [equivNum, LinearEquiv.trans_apply, LinearEquiv.ofBijective_apply, LinearMap.restrict_apply,
    Submodule.map_equivMapOfInjective_symm_apply, Subtype.coe_mk,
    DistribSMul.toLinearMap_apply]

/-- Copy of a `FractionalIdeal` with a new underlying set equal to the old one.
Useful to fix definitional equalities. -/
/-
**FractionalIdeal.copy** 是 Mathlib 中的一个定义，位于命名空间 `FractionalIdeal`。
形式化陈述：{R : Type u_1} →   [inst : CommRing R] →     {S : Submonoid R} →       {P 
: Type u_2} →         [inst_1 : CommRing P] →           [inst_2 : Algebra R P] →
 (p : FractionalIdeal S P) → (s : Set P) → s = ↑p → FractionalIdeal S P
参数：p : FractionalIdeal S P；s : Set P。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Copy of a `FractionalIdeal` with a new underlying set equal to the old one.
Useful to fix definitional equalities.
-/
protected def copy (p : FractionalIdeal S P) (s : Set P) (hs : s = ↑p) : FractionalIdeal S P :=
  ⟨Submodule.copy p s hs, by
    convert! p.isFractional
    ext
    simp only [hs]
    rfl⟩

@[simp]
/-
**FractionalIdeal.coe_copy** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：coe_copy (p : FractionalIdeal S P) (s : Set P) (hs : s = ↑p) : ↑(p.copy s 
hs) = s
参数：p : FractionalIdeal S P；s : Set P；hs : s = ↑p。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_copy (p : FractionalIdeal S P) (s : Set P) (hs : s = ↑p) : ↑(p.copy s hs) = s :=
  rfl
/-
**FractionalIdeal.coe_eq** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：coe_eq (p : FractionalIdeal S P) (s : Set P) (hs : s = ↑p) : p.copy s hs =
 p
参数：p : FractionalIdeal S P；s : Set P；hs : s = ↑p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
-/
theorem coe_eq (p : FractionalIdeal S P) (s : Set P) (hs : s = ↑p) : p.copy s hs = p :=
  SetLike.coe_injective hs

end SetLike

/-
**FractionalIdeal.zero_mem** 是 Mathlib 中的一个引理，位于命名空间 `FractionalIdeal`。
形式化陈述：zero_mem (I : FractionalIdeal S P) : 0 in I
参数：I : FractionalIdeal S P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.zero_mem`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [ins
t_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodule R M), 0 ∈
 p
-/
lemma zero_mem (I : FractionalIdeal S P) : 0 ∈ I := I.coeToSubmodule.zero_mem

@[simp]
/-
**FractionalIdeal.val_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：val_eq_coe (I : FractionalIdeal S P) : I.val = I
参数：I : FractionalIdeal S P。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem val_eq_coe (I : FractionalIdeal S P) : I.val = I :=
  rfl

@[simp, norm_cast]
/-
**FractionalIdeal.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：coe_mk (I : Submodule R P) (hI : IsFractional S I) : coeToSubmodule ⟨I, hI
⟩ = I
参数：I : Submodule R P；hI : IsFractional S I。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mk (I : Submodule R P) (hI : IsFractional S I) :
    coeToSubmodule ⟨I, hI⟩ = I :=
  rfl
/-
**FractionalIdeal.coeToSet_coeToSubmodule** 是 Mathlib 中的一个定理，位于命名空间 `FractionalI
deal`。
形式化陈述：coeToSet_coeToSubmodule (I : FractionalIdeal S P) : ((I : Submodule R P) :
 Set P) = I
参数：I : FractionalIdeal S P。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coeToSet_coeToSubmodule (I : FractionalIdeal S P) :
    ((I : Submodule R P) : Set P) = I :=
  rfl

/-! Transfer instances from `Submodule R P` to `FractionalIdeal S P`. -/

/-
**FractionalIdeal.** 是 Mathlib 中的一个实例，位于命名空间 `FractionalIdeal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Transfer instances from `Submodule R P` to `FractionalIdeal S P`.
-/
instance (I : FractionalIdeal S P) : Module R I :=
  Submodule.module (I : Submodule R P)
/-
**FractionalIdeal.coeToSubmodule_injective** 是 Mathlib 中的一个定理，位于命名空间 `Fractional
Ideal`。
形式化陈述：coeToSubmodule_injective : Function.Injective (fun (I : FractionalIdeal S 
P) => (I : Submodule R P))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
-/
theorem coeToSubmodule_injective :
    Function.Injective (fun (I : FractionalIdeal S P) ↦ (I : Submodule R P)) :=
  Subtype.coe_injective
/-
**FractionalIdeal.coeToSubmodule_inj** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`
。
形式化陈述：coeToSubmodule_inj {I J : FractionalIdeal S P} : (I : Submodule R P) = J ↔
 I = J
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `FractionalIdeal.coeToSubmodule_injective`：coeToSubmodule_injective : Fun
ction.Injective (fun (I : FractionalIdeal S P) => (I : Submodule R P))
-/
theorem coeToSubmodule_inj {I J : FractionalIdeal S P} : (I : Submodule R P) = J ↔ I = J :=
  coeToSubmodule_injective.eq_iff
/-
**FractionalIdeal.isFractional_of_le_one** 是 Mathlib 中的一个定理，位于命名空间 `FractionalId
eal`。
形式化陈述：isFractional_of_le_one (I : Submodule R P) (h : I <= 1) : IsFractional S I
参数：I : Submodule R P；h : I <= 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.one_mem`：∀ {M : Type u_1} [inst : MulOneClass M] (S : Submonoi
d M), 1 ∈ S
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.mem_one`：mem_one {x : A} : x in (1 : Submodule R A) ↔ exists y
, algebraMap R A y = x
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem isFractional_of_le_one (I : Submodule R P) (h : I ≤ 1) : IsFractional S I := by
  use 1, S.one_mem
  intro b hb
  rw [one_smul]
  obtain ⟨b', b'_mem, rfl⟩ := mem_one.mp (h hb)
  exact Set.mem_range_self b'
/-
**FractionalIdeal.isFractional_of_le** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`
。
形式化陈述：isFractional_of_le {I : Submodule R P} {J : FractionalIdeal S P} (hIJ : I 
<= J) : IsFractional S I
参数：hIJ : I <= J。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FractionalIdeal.isFractional`：∀ {R : Type u_1} [inst : CommRing R] {S : 
Submonoid R} {P : Type u_2} [inst_1 : CommRing P] [inst_2 : Algebra R P]   (I : 
FractionalIdeal S …
-/
theorem isFractional_of_le {I : Submodule R P} {J : FractionalIdeal S P} (hIJ : I ≤ J) :
    IsFractional S I := by
  obtain ⟨a, a_mem, ha⟩ := J.isFractional
  use a, a_mem
  intro b b_mem
  exact ha b (hIJ b_mem)

/-- Map an ideal `I` to a fractional ideal by forgetting `I` is integral.

This is the function that implements the coercion `Ideal R → FractionalIdeal S P`. -/
@[coe]
/-
**FractionalIdeal.coeIdeal** 是 Mathlib 中的一个定义，位于命名空间 `FractionalIdeal`。
形式化陈述：coeIdeal (I : Ideal R) : FractionalIdeal S P
参数：I : Ideal R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Map an ideal `I` to a fractional ideal by forgetting `I` is integral.

This is the function that implements the coercion `Ideal R → FractionalIdeal S P
`.
-/
def coeIdeal (I : Ideal R) : FractionalIdeal S P :=
  ⟨coeSubmodule P I,
   isFractional_of_le_one _ <| by simpa using coeSubmodule_mono P (le_top : I ≤ ⊤)⟩

-- Is a `CoeTC` rather than `Coe` to speed up failing inference, see library note [use has_coe_t]
/-- Map an ideal `I` to a fractional ideal by forgetting `I` is integral.

This is a bundled version of `IsLocalization.coeSubmodule : Ideal R → Submodule R P`,
which is not to be confused with the `coe : FractionalIdeal S P → Submodule R P`,
also called `coeToSubmodule` in theorem names.

This map is available as a ring hom, called `FractionalIdeal.coeIdealHom`.
-/
/-
**FractionalIdeal.** 是 Mathlib 中的一个实例，位于命名空间 `FractionalIdeal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Map an ideal `I` to a fractional ideal by forgetting `I` is integral.

This is a bundled version of `IsLocalization.coeSubmodule : Ideal R → Submodule 
R P`,
which is not to be confused with the `coe : FractionalIdeal S P → Submodule R P`
,
also called `coeToSubmodule` in theorem names.

This map is available as a ring hom, called `FractionalIdeal.coeIdealHom`.
-/
instance : CoeTC (Ideal R) (FractionalIdeal S P) :=
  ⟨fun I => coeIdeal I⟩

@[simp, norm_cast]
/-
**FractionalIdeal.coe_coeIdeal** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：coe_coeIdeal (I : Ideal R) : ((I : FractionalIdeal S P) : Submodule R P) =
 coeSubmodule P I
参数：I : Ideal R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_coeIdeal (I : Ideal R) :
    ((I : FractionalIdeal S P) : Submodule R P) = coeSubmodule P I :=
  rfl

variable (S)

@[simp]
/-
**FractionalIdeal.mem_coeIdeal** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：mem_coeIdeal {x : P} {I : Ideal R} : x in (I : FractionalIdeal S P) ↔ exis
ts x', x' in I ∧ algebraMap R P x' = x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalization.mem_coeSubmodule`：mem_coeSubmodule (I : Ideal R) {x : S} 
: x in coeSubmodule S I ↔ exists y : R, y in I ∧ algebraMap R S y = x
-/
theorem mem_coeIdeal {x : P} {I : Ideal R} :
    x ∈ (I : FractionalIdeal S P) ↔ ∃ x', x' ∈ I ∧ algebraMap R P x' = x :=
  mem_coeSubmodule _ _

@[simp] -- Ensure `simp` is confluent for `x ∈ ((I : Ideal R) : FractionalIdeal S P)`.
/-
**FractionalIdeal.mem_coeSubmodule** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：mem_coeSubmodule {x : P} {I : Ideal R} : x in coeSubmodule P I ↔ exists x'
, x' in I ∧ algebraMap R P x' = x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_coeSubmodule {x : P} {I : Ideal R} :
    x ∈ coeSubmodule P I ↔ ∃ x', x' ∈ I ∧ algebraMap R P x' = x :=
  Iff.rfl
/-
**FractionalIdeal.mem_coeIdeal_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal
`。
形式化陈述：mem_coeIdeal_of_mem {x : R} {I : Ideal R} (hx : x in I) : algebraMap R P x
 in (I : FractionalIdeal S P)
参数：hx : x in I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `FractionalIdeal.mem_coeIdeal`：mem_coeIdeal {x : P} {I : Ideal R} : x in 
(I : FractionalIdeal S P) ↔ exists x', x' in I ∧ algebraMap R P x' = x
-/
theorem mem_coeIdeal_of_mem {x : R} {I : Ideal R} (hx : x ∈ I) :
    algebraMap R P x ∈ (I : FractionalIdeal S P) :=
  (mem_coeIdeal S).mpr ⟨x, hx, rfl⟩
/-
**FractionalIdeal.coeIdeal_le_coeIdeal'** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIde
al`。
形式化陈述：coeIdeal_le_coeIdeal' [IsLocalization S P] (h : S <= nonZeroDivisors R) {I
 J : Ideal R} : (I : FractionalIdeal S P) <= J ↔ I <= J
参数：h : S <= nonZeroDivisors R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalization.coeSubmodule_le_coeSubmodule`：coeSubmodule_le_coeSubmodul
e (h : M <= nonZeroDivisors R) {I J : Ideal R} : coeSubmodule S I <= coeSubmodul
e S J ↔ I <= J
-/
theorem coeIdeal_le_coeIdeal' [IsLocalization S P] (h : S ≤ nonZeroDivisors R) {I J : Ideal R} :
    (I : FractionalIdeal S P) ≤ J ↔ I ≤ J :=
  coeSubmodule_le_coeSubmodule h

@[simp, gcongr]
/-
**FractionalIdeal.coeIdeal_le_coeIdeal** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdea
l`。
形式化陈述：coeIdeal_le_coeIdeal (K : Type*) [CommRing K] [Algebra R K] [IsFractionRin
g R K] {I J : Ideal R} : (I : FractionalIdeal R⁰ K) <= J ↔ I <= J
参数：K : Type*。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsFractionRing.coeSubmodule_le_coeSubmodule`：coeSubmodule_le_coeSubmodul
e {I J : Ideal R} : coeSubmodule K I <= coeSubmodule K J ↔ I <= J
-/
theorem coeIdeal_le_coeIdeal (K : Type*) [CommRing K] [Algebra R K] [IsFractionRing R K]
    {I J : Ideal R} : (I : FractionalIdeal R⁰ K) ≤ J ↔ I ≤ J :=
  IsFractionRing.coeSubmodule_le_coeSubmodule
/-
**FractionalIdeal.** 是 Mathlib 中的一个实例，位于命名空间 `FractionalIdeal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Zero (FractionalIdeal S P) :=
  ⟨(0 : Ideal R)⟩

@[simp]
/-
**FractionalIdeal.mem_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：mem_zero_iff {x : P} : x in (0 : FractionalIdeal S P) ↔ x = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
-/
theorem mem_zero_iff {x : P} : x ∈ (0 : FractionalIdeal S P) ↔ x = 0 :=
  ⟨fun ⟨x', x'_mem_zero, x'_eq_x⟩ => by
    have x'_eq_zero : x' = 0 := x'_mem_zero
    simp [x'_eq_x.symm, x'_eq_zero], fun hx => ⟨0, rfl, by simp [hx]⟩⟩

variable {S}

@[simp, norm_cast]
/-
**FractionalIdeal.coe_zero** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：coe_zero : ↑(0 : FractionalIdeal S P) = (⊥ : Submodule R P)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `FractionalIdeal.mem_zero_iff`：mem_zero_iff {x : P} : x in (0 : Fractiona
lIdeal S P) ↔ x = 0
-/
theorem coe_zero : ↑(0 : FractionalIdeal S P) = (⊥ : Submodule R P) :=
  Submodule.ext fun _ => mem_zero_iff S

@[simp, norm_cast]
/-
**FractionalIdeal.coeIdeal_bot** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：coeIdeal_bot : ((⊥ : Ideal R) : FractionalIdeal S P) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coeIdeal_bot : ((⊥ : Ideal R) : FractionalIdeal S P) = 0 :=
  rfl

section
variable [loc : IsLocalization S P]

variable (P) in
-- Cannot be @[simp] because `S` cannot be inferred by `simp`.
/-
**FractionalIdeal.exists_mem_algebraMap_eq** 是 Mathlib 中的一个定理，位于命名空间 `Fractional
Ideal`。
形式化陈述：exists_mem_algebraMap_eq {x : R} {I : Ideal R} (h : S <= nonZeroDivisors R
) : (exists x', x' in I ∧ algebraMap R P x' = algebraMap R P x) ↔ x in I
参数：h : S <= nonZeroDivisors R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalization.injective`：∀ {R : Type u_1} [inst : CommRing R] {M : Subm
onoid R} (S : Type u_2) [inst_1 : CommRing S] [inst_2 : Algebra R S]   [IsLocali
zation M S], M…
-/
theorem exists_mem_algebraMap_eq {x : R} {I : Ideal R} (h : S ≤ nonZeroDivisors R) :
    (∃ x', x' ∈ I ∧ algebraMap R P x' = algebraMap R P x) ↔ x ∈ I :=
  ⟨fun ⟨_, hx', Eq⟩ => IsLocalization.injective _ h Eq ▸ hx', fun h => ⟨x, h, rfl⟩⟩
/-
**FractionalIdeal.coeIdeal_injective'** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal
`。
形式化陈述：coeIdeal_injective' (h : S <= nonZeroDivisors R) : Function.Injective (fun
 (I : Ideal R) => (I : FractionalIdeal S P))
参数：h : S <= nonZeroDivisors R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `FractionalIdeal.coeIdeal_le_coeIdeal'`：coeIdeal_le_coeIdeal' [IsLocaliza
tion S P] (h : S <= nonZeroDivisors R) {I J : Ideal R} : (I : FractionalIdeal S 
P) <= J ↔ I <= J
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
-/
theorem coeIdeal_injective' (h : S ≤ nonZeroDivisors R) :
    Function.Injective (fun (I : Ideal R) ↦ (I : FractionalIdeal S P)) := fun _ _ h' =>
  ((coeIdeal_le_coeIdeal' S h).mp h'.le).antisymm ((coeIdeal_le_coeIdeal' S h).mp
    h'.ge)
/-
**FractionalIdeal.coeIdeal_inj'** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：coeIdeal_inj' (h : S <= nonZeroDivisors R) {I J : Ideal R} : (I : Fraction
alIdeal S P) = J ↔ I = J
参数：h : S <= nonZeroDivisors R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `FractionalIdeal.coeIdeal_injective'`：coeIdeal_injective' (h : S <= nonZe
roDivisors R) : Function.Injective (fun (I : Ideal R) => (I : FractionalIdeal S 
P))
-/
theorem coeIdeal_inj' (h : S ≤ nonZeroDivisors R) {I J : Ideal R} :
    (I : FractionalIdeal S P) = J ↔ I = J :=
  (coeIdeal_injective' h).eq_iff

-- Not `@[simp]` because `coeIdeal_eq_zero` (in `Operations.lean`) will prove this.
/-
**FractionalIdeal.coeIdeal_eq_zero'** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：coeIdeal_eq_zero' {I : Ideal R} (h : S <= nonZeroDivisors R) : (I : Fracti
onalIdeal S P) = 0 ↔ I = (⊥ : Ideal R)
参数：h : S <= nonZeroDivisors R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FractionalIdeal.coeIdeal_inj'`：coeIdeal_inj' (h : S <= nonZeroDivisors R
) {I J : Ideal R} : (I : FractionalIdeal S P) = J ↔ I = J
-/
theorem coeIdeal_eq_zero' {I : Ideal R} (h : S ≤ nonZeroDivisors R) :
    (I : FractionalIdeal S P) = 0 ↔ I = (⊥ : Ideal R) :=
  coeIdeal_inj' h
/-
**FractionalIdeal.coeIdeal_ne_zero'** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：coeIdeal_ne_zero' {I : Ideal R} (h : S <= nonZeroDivisors R) : (I : Fracti
onalIdeal S P) != 0 ↔ I != (⊥ : Ideal R)
参数：h : S <= nonZeroDivisors R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `FractionalIdeal.coeIdeal_eq_zero'`：coeIdeal_eq_zero' {I : Ideal R} (h : 
S <= nonZeroDivisors R) : (I : FractionalIdeal S P) = 0 ↔ I = (⊥ : Ideal R)
-/
theorem coeIdeal_ne_zero' {I : Ideal R} (h : S ≤ nonZeroDivisors R) :
    (I : FractionalIdeal S P) ≠ 0 ↔ I ≠ (⊥ : Ideal R) :=
  not_iff_not.mpr <| coeIdeal_eq_zero' h

end

/-
**FractionalIdeal.coeToSubmodule_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIde
al`。
形式化陈述：coeToSubmodule_eq_bot {I : FractionalIdeal S P} : (I : Submodule R P) = ⊥ 
↔ I = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FractionalIdeal.coeToSubmodule_injective`：coeToSubmodule_injective : Fun
ction.Injective (fun (I : FractionalIdeal S P) => (I : Submodule R P))
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FractionalIdeal.coe_zero`：coe_zero : ↑(0 : FractionalIdeal S P) = (⊥ : S
ubmodule R P)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
theorem coeToSubmodule_eq_bot {I : FractionalIdeal S P} : (I : Submodule R P) = ⊥ ↔ I = 0 :=
  ⟨fun h => coeToSubmodule_injective (by simp [h]), fun h => by simp [h]⟩
/-
**FractionalIdeal.coeToSubmodule_ne_bot** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIde
al`。
形式化陈述：coeToSubmodule_ne_bot {I : FractionalIdeal S P} : ↑I != (⊥ : Submodule R P
) ↔ I != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `FractionalIdeal.coeToSubmodule_eq_bot`：coeToSubmodule_eq_bot {I : Fracti
onalIdeal S P} : (I : Submodule R P) = ⊥ ↔ I = 0
-/
theorem coeToSubmodule_ne_bot {I : FractionalIdeal S P} : ↑I ≠ (⊥ : Submodule R P) ↔ I ≠ 0 :=
  not_iff_not.mpr coeToSubmodule_eq_bot
/-
**FractionalIdeal.** 是 Mathlib 中的一个实例，位于命名空间 `FractionalIdeal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (FractionalIdeal S P) :=
  ⟨0⟩
/-
**FractionalIdeal.** 是 Mathlib 中的一个实例，位于命名空间 `FractionalIdeal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : One (FractionalIdeal S P) :=
  ⟨(⊤ : Ideal R)⟩
/-
**FractionalIdeal.zero_of_num_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`
。
形式化陈述：zero_of_num_eq_bot [IsDomain R] [Module.IsTorsionFree R P] (hS : 0 ∉ S) {I
 : FractionalIdeal S P} (hI : I.num = ⊥) : I = 0
参数：hS : 0 ∉ S；hI : I.num = ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FractionalIdeal.coeToSubmodule_eq_bot`：coeToSubmodule_eq_bot {I : Fracti
onalIdeal S P} : (I : Submodule R P) = ⊥ ↔ I = 0
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
· 使用定理 `FractionalIdeal.den_mul_self_eq_num`：den_mul_self_eq_num (I : Fractional
Ideal S P) : I.den • (I : Submodule R P) = Submodule.map (Algebra.linearMap R P)
 I.num
· 使用定理 `Submodule.map_bot`：map_bot (f : M ->ₛₗ[σ₁₂] M₂) : map f ⊥ = ⊥
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.eq_bot_iff`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R
] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (p : Submodule R M),
 p = ⊥ ↔ ∀…
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `smul_eq_zero`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R] [inst_
1 : AddCommMonoid M] [inst_2 : _root_.Module R M] {r : R}   {m : M} [Module.IsTo
rs…
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `ne_of_mem_of_not_mem`：∀ {α : Type u_1} {β : Type u_2} [inst : Membership
 α β] {s : β} {a b : α}, a ∈ s → b ∉ s → a ≠ b
· 使用定理 `SetLike.coe_mem`：coe_mem (x : p) : (x : B) in p
-/
theorem zero_of_num_eq_bot [IsDomain R] [Module.IsTorsionFree R P] (hS : 0 ∉ S)
    {I : FractionalIdeal S P} (hI : I.num = ⊥) : I = 0 := by
  rw [← coeToSubmodule_eq_bot, eq_bot_iff]
  intro x hx
  suffices (den I : R) • x = 0 from
    (smul_eq_zero.mp this).resolve_left (ne_of_mem_of_not_mem (SetLike.coe_mem _) hS)
  have h_eq : I.den • (I : Submodule R P) = ⊥ := by rw [den_mul_self_eq_num, hI, Submodule.map_bot]
  exact (Submodule.eq_bot_iff _).mp h_eq (den I • x) ⟨x, hx, rfl⟩

set_option backward.isDefEq.respectTransparency false in
/-
**FractionalIdeal.num_zero_eq** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：num_zero_eq (h_inj : Function.Injective (algebraMap R P)) : num (0 : Fract
ionalIdeal S P) = 0
参数：h_inj : Function.Injective (algebraMap R P)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FractionalIdeal.coe_zero`：coe_zero : ↑(0 : FractionalIdeal S P) = (⊥ : S
ubmodule R P)
· 使用定理 `Submodule.smul_bot'`：smul_bot' (a : α) : a • (⊥ : Submodule R M) = ⊥
-/
theorem num_zero_eq (h_inj : Function.Injective (algebraMap R P)) :
    num (0 : FractionalIdeal S P) = 0 := by
  simpa [num, LinearMap.ker_eq_bot] using! h_inj

variable (S)

@[simp, norm_cast]
/-
**FractionalIdeal.coeIdeal_top** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：coeIdeal_top : ((⊤ : Ideal R) : FractionalIdeal S P) = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coeIdeal_top : ((⊤ : Ideal R) : FractionalIdeal S P) = 1 :=
  rfl

@[simp]
/-
**FractionalIdeal.mem_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：mem_one_iff {x : P} : x in (1 : FractionalIdeal S P) ↔ exists x' : R, alge
braMap R P x' = x
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mem_one_iff {x : P} : x ∈ (1 : FractionalIdeal S P) ↔ ∃ x' : R, algebraMap R P x' = x :=
  Iff.intro (fun ⟨x', _, h⟩ => ⟨x', h⟩) fun ⟨x', h⟩ => ⟨x', ⟨⟩, h⟩
/-
**FractionalIdeal.coe_mem_one** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：coe_mem_one (x : R) : algebraMap R P x in (1 : FractionalIdeal S P)
参数：x : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
theorem coe_mem_one (x : R) : algebraMap R P x ∈ (1 : FractionalIdeal S P) := by simp
/-
**FractionalIdeal.one_mem_one** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：one_mem_one : (1 : P) in (1 : FractionalIdeal S P)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `FractionalIdeal.mem_one_iff`：mem_one_iff {x : P} : x in (1 : FractionalI
deal S P) ↔ exists x' : R, algebraMap R P x' = x
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
theorem one_mem_one : (1 : P) ∈ (1 : FractionalIdeal S P) :=
  (mem_one_iff S).mpr ⟨1, map_one _⟩

variable {S}

/-- `(1 : FractionalIdeal S P)` is defined as the R-submodule `f(R) ≤ P`.

However, this is not definitionally equal to `1 : Submodule R P`,
which is proved in the actual `simp` lemma `coe_one`. -/
/-
**FractionalIdeal.coe_one_eq_coeSubmodule_top** 是 Mathlib 中的一个定理，位于命名空间 `Fractio
nalIdeal`。
形式化陈述：coe_one_eq_coeSubmodule_top : ↑(1 : FractionalIdeal S P) = coeSubmodule P 
(⊤ : Ideal R)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`(1 : FractionalIdeal S P)` is defined as the R-submodule `f(R) ≤ P`.

However, this is not definitionally equal to `1 : Submodule R P`,
which is proved in the actual `simp` lemma `coe_one`.
-/
theorem coe_one_eq_coeSubmodule_top : ↑(1 : FractionalIdeal S P) = coeSubmodule P (⊤ : Ideal R) :=
  rfl

@[simp, norm_cast]
/-
**FractionalIdeal.coe_one** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：coe_one : (↑(1 : FractionalIdeal S P) : Submodule R P) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FractionalIdeal.coe_one_eq_coeSubmodule_top`：coe_one_eq_coeSubmodule_top
 : ↑(1 : FractionalIdeal S P) = coeSubmodule P (⊤ : Ideal R)
· 使用定理 `IsLocalization.coeSubmodule_top`：coeSubmodule_top : coeSubmodule S (⊤ : 
Ideal R) = 1
-/
theorem coe_one : (↑(1 : FractionalIdeal S P) : Submodule R P) = 1 := by
  rw [coe_one_eq_coeSubmodule_top, coeSubmodule_top]

section Lattice

/-!
### `Lattice` section

Defines the order on fractional ideals as inclusion of their underlying sets,
and ports the lattice structure on submodules to fractional ideals.
-/


@[simp]
/-
**FractionalIdeal.coe_le_coe** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：coe_le_coe {I J : FractionalIdeal S P} : (I : Submodule R P) <= (J : Submo
dule R P) ↔ I <= J
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
### `Lattice` section

Defines the order on fractional ideals as inclusion of their underlying sets,
and ports the lattice structure on submodules to fractional ideals.
-/
theorem coe_le_coe {I J : FractionalIdeal S P} :
    (I : Submodule R P) ≤ (J : Submodule R P) ↔ I ≤ J :=
  Iff.rfl
/-
**FractionalIdeal.zero_le** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：zero_le (I : FractionalIdeal S P) : 0 <= I
参数：I : FractionalIdeal S P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `FractionalIdeal.mem_zero_iff`：mem_zero_iff {x : P} : x in (0 : Fractiona
lIdeal S P) ↔ x = 0
· 使用引理 `FractionalIdeal.zero_mem`：zero_mem (I : FractionalIdeal S P) : 0 in I
-/
theorem zero_le (I : FractionalIdeal S P) : 0 ≤ I := by
  intro x hx
  convert! zero_mem I
  rw [(mem_zero_iff _).mp hx]
/-
**FractionalIdeal.orderBot** 是 Mathlib 中的一个实例，位于命名空间 `FractionalIdeal`。
形式化陈述：orderBot : OrderBot (FractionalIdeal S P) where bot
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `FractionalIdeal.zero_le`：zero_le (I : FractionalIdeal S P) : 0 <= I
-/
instance orderBot : OrderBot (FractionalIdeal S P) where
  bot := 0
  bot_le := zero_le

@[simp]
/-
**FractionalIdeal.bot_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：bot_eq_zero : (⊥ : FractionalIdeal S P) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bot_eq_zero : (⊥ : FractionalIdeal S P) = 0 :=
  rfl
/-
**FractionalIdeal.le_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：le_zero_iff {I : FractionalIdeal S P} : I <= 0 ↔ I = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ ↔ a = ⊥
-/
theorem le_zero_iff {I : FractionalIdeal S P} : I ≤ 0 ↔ I = 0 :=
  le_bot_iff
/-
**FractionalIdeal.eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：eq_zero_iff {I : FractionalIdeal S P} : I = 0 ↔ forall x in I, x = (0 : P)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `le_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ ↔ a = ⊥
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `FractionalIdeal.mem_zero_iff`：mem_zero_iff {x : P} : x in (0 : Fractiona
lIdeal S P) ↔ x = 0
-/
theorem eq_zero_iff {I : FractionalIdeal S P} : I = 0 ↔ ∀ x ∈ I, x = (0 : P) :=
  ⟨fun h x hx => by simpa [h, mem_zero_iff] using hx, fun h =>
    le_bot_iff.mp fun x hx => (mem_zero_iff S).mpr (h x hx)⟩
/-
**FractionalIdeal._root_.IsFractional.sup** 是 Mathlib 中的一个定理，位于命名空间 `FractionalI
deal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.IsFractional.sup {I J : Submodule R P} :
    IsFractional S I → IsFractional S J → IsFractional S (I ⊔ J)
  | ⟨aI, haI, hI⟩, ⟨aJ, haJ, hJ⟩ =>
    ⟨aI * aJ, S.mul_mem haI haJ, fun b hb => by
      rcases mem_sup.mp hb with ⟨bI, hbI, bJ, hbJ, rfl⟩
      rw [smul_add]
      apply isInteger_add
      · rw [mul_smul, smul_comm]
        exact isInteger_smul (hI bI hbI)
      · rw [mul_smul]
        exact isInteger_smul (hJ bJ hbJ)⟩
/-
**FractionalIdeal._root_.IsFractional.inf_right** 是 Mathlib 中的一个定理，位于命名空间 `Fract
ionalIdeal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.IsFractional.inf_right {I : Submodule R P} :
    IsFractional S I → ∀ J, IsFractional S (I ⊓ J)
  | ⟨aI, haI, hI⟩, J =>
    ⟨aI, haI, fun b hb => by
      rcases mem_inf.mp hb with ⟨hbI, _⟩
      exact hI b hbI⟩
/-
**FractionalIdeal.** 是 Mathlib 中的一个实例，位于命名空间 `FractionalIdeal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Min (FractionalIdeal S P) :=
  ⟨fun I J => ⟨I ⊓ J, I.isFractional.inf_right J⟩⟩

@[simp, norm_cast]
/-
**FractionalIdeal.coe_inf** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：coe_inf (I J : FractionalIdeal S P) : ↑(I ⊓ J) = (I ⊓ J : Submodule R P)
参数：I J : FractionalIdeal S P。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_inf (I J : FractionalIdeal S P) : ↑(I ⊓ J) = (I ⊓ J : Submodule R P) :=
  rfl
/-
**FractionalIdeal.** 是 Mathlib 中的一个实例，位于命名空间 `FractionalIdeal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Max (FractionalIdeal S P) :=
  ⟨fun I J => ⟨I ⊔ J, I.isFractional.sup J.isFractional⟩⟩

@[norm_cast]
/-
**FractionalIdeal.coe_sup** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：coe_sup (I J : FractionalIdeal S P) : ↑(I ⊔ J) = (I ⊔ J : Submodule R P)
参数：I J : FractionalIdeal S P。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_sup (I J : FractionalIdeal S P) : ↑(I ⊔ J) = (I ⊔ J : Submodule R P) :=
  rfl
/-
**FractionalIdeal.lattice** 是 Mathlib 中的一个实例，位于命名空间 `FractionalIdeal`。
形式化陈述：lattice : Lattice (FractionalIdeal S P)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `FractionalIdeal.coe_sup`：coe_sup (I J : FractionalIdeal S P) : ↑(I ⊔ J) 
= (I ⊔ J : Submodule R P)
· 使用定理 `FractionalIdeal.coe_inf`：coe_inf (I J : FractionalIdeal S P) : ↑(I ⊓ J) 
= (I ⊓ J : Submodule R P)
-/
instance lattice : Lattice (FractionalIdeal S P) :=
  Function.Injective.lattice _ Subtype.coe_injective .rfl .rfl coe_sup coe_inf

end Lattice

section Semiring

/-
**FractionalIdeal.** 是 Mathlib 中的一个实例，位于命名空间 `FractionalIdeal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Add (FractionalIdeal S P) :=
  ⟨(· ⊔ ·)⟩

@[simp]
/-
**FractionalIdeal.sup_eq_add** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：sup_eq_add (I J : FractionalIdeal S P) : I ⊔ J = I + J
参数：I J : FractionalIdeal S P。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sup_eq_add (I J : FractionalIdeal S P) : I ⊔ J = I + J :=
  rfl

@[simp, norm_cast]
/-
**FractionalIdeal.coe_add** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：coe_add (I J : FractionalIdeal S P) : (↑(I + J) : Submodule R P) = I + J
参数：I J : FractionalIdeal S P。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_add (I J : FractionalIdeal S P) : (↑(I + J) : Submodule R P) = I + J :=
  rfl
/-
**FractionalIdeal.mem_add** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：mem_add (I J : FractionalIdeal S P) (x : P) : x in I + J ↔ exists i in I, 
exists j in J, i + j = x
参数：I J : FractionalIdeal S P；x : P。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FractionalIdeal.mem_coe`：mem_coe {I : FractionalIdeal S P} {x : P} : x i
n (I : Submodule R P) ↔ x in I
· 使用定理 `FractionalIdeal.coe_add`：coe_add (I J : FractionalIdeal S P) : (↑(I + J)
 : Submodule R P) = I + J
· 使用定理 `Submodule.add_eq_sup`：add_eq_sup (p q : Submodule R M) : p + q = p ⊔ q
· 使用定理 `Submodule.mem_sup`：mem_sup : x in p ⊔ p' ↔ exists y in p, exists z in p'
, y + z = x
-/
theorem mem_add (I J : FractionalIdeal S P) (x : P) :
    x ∈ I + J ↔ ∃ i ∈ I, ∃ j ∈ J, i + j = x := by
  rw [← mem_coe, coe_add, Submodule.add_eq_sup]; exact Submodule.mem_sup

@[simp, norm_cast]
/-
**FractionalIdeal.coeIdeal_inf** 是 Mathlib 中的一个引理，位于命名空间 `FractionalIdeal`。
形式化陈述：coeIdeal_inf [FaithfulSMul R P] (I J : Ideal R) : (↑(I ⊓ J) : FractionalId
eal S P) = ↑I ⊓ ↑J
参数：I J : Ideal R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FractionalIdeal.coeToSubmodule_injective`：coeToSubmodule_injective : Fun
ction.Injective (fun (I : FractionalIdeal S P) => (I : Submodule R P))
· 使用定理 `Submodule.map_inf`：map_inf (f : M ->ₛₗ[σ₁₂] M₂) {p q : Submodule R M} (h
f : Injective f) : (p ⊓ q).map f = p.map f ⊓ q.map f
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
-/
lemma coeIdeal_inf [FaithfulSMul R P] (I J : Ideal R) :
    (↑(I ⊓ J) : FractionalIdeal S P) = ↑I ⊓ ↑J := by
  apply coeToSubmodule_injective
  exact Submodule.map_inf (Algebra.linearMap R P) (FaithfulSMul.algebraMap_injective R P)

@[simp, norm_cast]
/-
**FractionalIdeal.coeIdeal_sup** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：coeIdeal_sup (I J : Ideal R) : ↑(I ⊔ J) = (I + J : FractionalIdeal S P)
参数：I J : Ideal R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FractionalIdeal.coeToSubmodule_injective`：coeToSubmodule_injective : Fun
ction.Injective (fun (I : FractionalIdeal S P) => (I : Submodule R P))
· 使用定理 `IsLocalization.coeSubmodule_sup`：coeSubmodule_sup (I J : Ideal R) : coeS
ubmodule S (I ⊔ J) = coeSubmodule S I ⊔ coeSubmodule S J
-/
theorem coeIdeal_sup (I J : Ideal R) : ↑(I ⊔ J) = (I + J : FractionalIdeal S P) :=
  coeToSubmodule_injective <| coeSubmodule_sup _ _ _
/-
**FractionalIdeal._root_.IsFractional.nsmul** 是 Mathlib 中的一个定理，位于命名空间 `Fractiona
lIdeal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.IsFractional.nsmul {I : Submodule R P} :
    ∀ n : ℕ, IsFractional S I → IsFractional S (n • I : Submodule R P)
  | 0, _ => by
    rw [zero_smul]
    convert! ((0 : Ideal R) : FractionalIdeal S P).isFractional
    simp
  | n + 1, h => by
    rw [succ_nsmul]
    exact (IsFractional.nsmul n h).sup h
/-
**FractionalIdeal.** 是 Mathlib 中的一个实例，位于命名空间 `FractionalIdeal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMul ℕ (FractionalIdeal S P) where smul n I := ⟨n • ↑I, I.isFractional.nsmul n⟩

@[norm_cast]
/-
**FractionalIdeal.coe_nsmul** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：coe_nsmul (n : Nat) (I : FractionalIdeal S P) : (↑(n • I) : Submodule R P)
 = n • (I : Submodule R P)
参数：n : Nat；I : FractionalIdeal S P。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_nsmul (n : ℕ) (I : FractionalIdeal S P) :
    (↑(n • I) : Submodule R P) = n • (I : Submodule R P) :=
  rfl
/-
**FractionalIdeal._root_.IsFractional.mul** 是 Mathlib 中的一个定理，位于命名空间 `FractionalI
deal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.IsFractional.mul {I J : Submodule R P} :
    IsFractional S I → IsFractional S J → IsFractional S (I * J : Submodule R P)
  | ⟨aI, haI, hI⟩, ⟨aJ, haJ, hJ⟩ =>
    ⟨aI * aJ, S.mul_mem haI haJ, fun b hb => by
      refine Submodule.mul_induction_on hb ?_ ?_
      · intro m hm n hn
        obtain ⟨n', hn'⟩ := hJ n hn
        rw [mul_smul, mul_comm m, ← smul_mul_assoc, ← hn', ← Algebra.smul_def]
        apply hI
        exact Submodule.smul_mem _ _ hm
      · intro x y hx hy
        rw [smul_add]
        apply isInteger_add hx hy⟩
/-
**FractionalIdeal._root_.IsFractional.pow** 是 Mathlib 中的一个定理，位于命名空间 `FractionalI
deal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.IsFractional.pow {I : Submodule R P} (h : IsFractional S I) :
    ∀ n : ℕ, IsFractional S (I ^ n : Submodule R P)
  | 0 => isFractional_of_le_one _ (pow_zero _).le
  | n + 1 => (pow_succ I n).symm ▸ (IsFractional.pow h n).mul h

/-- `FractionalIdeal.mul` is the product of two fractional ideals,
used to define the `Mul` instance.

This is only an auxiliary definition: the preferred way of writing `I.mul J` is `I * J`.

Elaborated terms involving `FractionalIdeal` tend to grow quite large,
so by making definitions irreducible, we hope to avoid deep unfolds.
-/
irreducible_def mul (lemma := mul_def') (I J : FractionalIdeal S P) : FractionalIdeal S P :=
  ⟨I * J, I.isFractional.mul J.isFractional⟩

-- local attribute [semireducible] mul
/-
**FractionalIdeal.** 是 Mathlib 中的一个实例，位于命名空间 `FractionalIdeal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Mul (FractionalIdeal S P) :=
  ⟨fun I J => mul I J⟩

@[simp]
/-
**FractionalIdeal.mul_eq_mul** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：mul_eq_mul (I J : FractionalIdeal S P) : mul I J = I * J
参数：I J : FractionalIdeal S P。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mul_eq_mul (I J : FractionalIdeal S P) : mul I J = I * J :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-
**FractionalIdeal.mul_def** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：mul_def (I J : FractionalIdeal S P) : I * J = ⟨I * J, I.isFractional.mul J
.isFractional⟩
参数：I J : FractionalIdeal S P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsFractional.mul`：∀ {R : Type u_1} [inst : CommRing R] {S : Submonoid R}
 {P : Type u_2} [inst_1 : CommRing P] [inst_2 : Algebra R P]   {I J : Submodule 
R P}, …
· 使用定理 `FractionalIdeal.isFractional`：∀ {R : Type u_1} [inst : CommRing R] {S : 
Submonoid R} {P : Type u_2} [inst_1 : CommRing P] [inst_2 : Algebra R P]   (I : 
FractionalIdeal S …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FractionalIdeal.mul_def'`：∀ {R : Type u_3} [inst : CommRing R] {S : Subm
onoid R} {P : Type u_4} [inst_1 : CommRing P] [inst_2 : Algebra R P]   (I J : Fr
actionalIdeal …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mul_def (I J : FractionalIdeal S P) :
    I * J = ⟨I * J, I.isFractional.mul J.isFractional⟩ := by simp only [← mul_eq_mul, mul_def']

@[simp, norm_cast]
/-
**FractionalIdeal.coe_mul** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：coe_mul (I J : FractionalIdeal S P) : (↑(I * J) : Submodule R P) = I * J
参数：I J : FractionalIdeal S P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsFractional.mul`：∀ {R : Type u_1} [inst : CommRing R] {S : Submonoid R}
 {P : Type u_2} [inst_1 : CommRing P] [inst_2 : Algebra R P]   {I J : Submodule 
R P}, …
· 使用定理 `FractionalIdeal.isFractional`：∀ {R : Type u_1} [inst : CommRing R] {S : 
Submonoid R} {P : Type u_2} [inst_1 : CommRing P] [inst_2 : Algebra R P]   (I : 
FractionalIdeal S …
· 使用定理 `FractionalIdeal.mul_def`：mul_def (I J : FractionalIdeal S P) : I * J = ⟨
I * J, I.isFractional.mul J.isFractional⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coe_mul (I J : FractionalIdeal S P) : (↑(I * J) : Submodule R P) = I * J := by
  simp only [mul_def, coe_mk]

@[simp, norm_cast]
/-
**FractionalIdeal.coeIdeal_mul** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：coeIdeal_mul (I J : Ideal R) : (↑(I * J) : FractionalIdeal S P) = I * J
参数：I J : Ideal R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsFractional.mul`：∀ {R : Type u_1} [inst : CommRing R] {S : Submonoid R}
 {P : Type u_2} [inst_1 : CommRing P] [inst_2 : Algebra R P]   {I J : Submodule 
R P}, …
· 使用定理 `FractionalIdeal.isFractional`：∀ {R : Type u_1} [inst : CommRing R] {S : 
Submonoid R} {P : Type u_2} [inst_1 : CommRing P] [inst_2 : Algebra R P]   (I : 
FractionalIdeal S …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FractionalIdeal.mul_def`：mul_def (I J : FractionalIdeal S P) : I * J = ⟨
I * J, I.isFractional.mul J.isFractional⟩
· 使用定理 `FractionalIdeal.coeToSubmodule_injective`：coeToSubmodule_injective : Fun
ction.Injective (fun (I : FractionalIdeal S P) => (I : Submodule R P))
· 使用定理 `IsLocalization.coeSubmodule_mul`：coeSubmodule_mul (I J : Ideal R) : coeS
ubmodule S (I * J) = coeSubmodule S I * coeSubmodule S J
-/
theorem coeIdeal_mul (I J : Ideal R) : (↑(I * J) : FractionalIdeal S P) = I * J := by
  simp only [mul_def]
  exact coeToSubmodule_injective (coeSubmodule_mul _ _ _)
/-
**FractionalIdeal.** 是 Mathlib 中的一个实例，位于命名空间 `FractionalIdeal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MulLeftMono (FractionalIdeal S P) where
  elim I J J' h := by simpa only [mul_def] using! mul_le.mpr fun x hx y hy => mul_mem_mul hx (h hy)
/-
**FractionalIdeal.** 是 Mathlib 中的一个实例，位于命名空间 `FractionalIdeal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MulRightMono (FractionalIdeal S P) where
  elim I J J' h := by simpa only [mul_def] using! mul_le.mpr fun x hx y hy => mul_mem_mul (h hx) hy
/-
**FractionalIdeal.mul_mem_mul** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：mul_mem_mul {I J : FractionalIdeal S P} {i j : P} (hi : i in I) (hj : j in
 J) : i * j in I * J
参数：hi : i in I；hj : j in J。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsFractional.mul`：∀ {R : Type u_1} [inst : CommRing R] {S : Submonoid R}
 {P : Type u_2} [inst_1 : CommRing P] [inst_2 : Algebra R P]   {I J : Submodule 
R P}, …
· 使用定理 `FractionalIdeal.isFractional`：∀ {R : Type u_1} [inst : CommRing R] {S : 
Submonoid R} {P : Type u_2} [inst_1 : CommRing P] [inst_2 : Algebra R P]   (I : 
FractionalIdeal S …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FractionalIdeal.mul_def`：mul_def (I J : FractionalIdeal S P) : I * J = ⟨
I * J, I.isFractional.mul J.isFractional⟩
· 使用定理 `Submodule.mul_mem_mul`：mul_mem_mul (hm : m in M) (hn : n in N) : m * n i
n M * N
-/
theorem mul_mem_mul {I J : FractionalIdeal S P} {i j : P} (hi : i ∈ I) (hj : j ∈ J) :
    i * j ∈ I * J := by
  simp only [mul_def]
  exact Submodule.mul_mem_mul hi hj
/-
**FractionalIdeal.mul_le** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：mul_le {I J K : FractionalIdeal S P} : I * J <= K ↔ forall i in I, forall 
j in J, i * j in K
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsFractional.mul`：∀ {R : Type u_1} [inst : CommRing R] {S : Submonoid R}
 {P : Type u_2} [inst_1 : CommRing P] [inst_2 : Algebra R P]   {I J : Submodule 
R P}, …
· 使用定理 `FractionalIdeal.isFractional`：∀ {R : Type u_1} [inst : CommRing R] {S : 
Submonoid R} {P : Type u_2} [inst_1 : CommRing P] [inst_2 : Algebra R P]   (I : 
FractionalIdeal S …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FractionalIdeal.mul_def`：mul_def (I J : FractionalIdeal S P) : I * J = ⟨
I * J, I.isFractional.mul J.isFractional⟩
· 使用定理 `Submodule.mul_le`：mul_le : M * N <= P ↔ forall m in M, forall n in N, m 
* n in P
-/
theorem mul_le {I J K : FractionalIdeal S P} : I * J ≤ K ↔ ∀ i ∈ I, ∀ j ∈ J, i * j ∈ K := by
  simp only [mul_def]
  exact Submodule.mul_le
/-
**FractionalIdeal.** 是 Mathlib 中的一个实例，位于命名空间 `FractionalIdeal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Pow (FractionalIdeal S P) ℕ :=
  ⟨fun I n => ⟨(I : Submodule R P) ^ n, I.isFractional.pow n⟩⟩

@[simp, norm_cast]
/-
**FractionalIdeal.coe_pow** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：coe_pow (I : FractionalIdeal S P) (n : Nat) : ↑(I ^ n) = (I : Submodule R 
P) ^ n
参数：I : FractionalIdeal S P；n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_pow (I : FractionalIdeal S P) (n : ℕ) : ↑(I ^ n) = (I : Submodule R P) ^ n :=
  rfl

@[elab_as_elim]
/-
**FractionalIdeal.mul_induction_on** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {S : Submonoid R} {P : Type u_2} [ins
t_1 : CommRing P] [inst_2 : Algebra R P]   {I J : FractionalIdeal S P} {C : P → 
Prop} {r : P},   r ∈ I * J → (∀ i ∈ I, ∀ j ∈ J, C (i * j)) → (∀ (x y : P), C x →
 C y → C (x + y)) → C r
参数：∀ i ∈ I, ∀ j ∈ J, C (i * j)；∀ (x y : P), C x → C y → C (x + y)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.mul_induction_on`：∀ {R : Type u} [inst : Semiring R] {A : Type
 v} [inst_1 : Semiring A] [inst_2 : _root_.Module R A]   [inst_3 : IsScalarTower
 R A A] {M N : S…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsFractional.mul`：∀ {R : Type u_1} [inst : CommRing R] {S : Submonoid R}
 {P : Type u_2} [inst_1 : CommRing P] [inst_2 : Algebra R P]   {I J : Submodule 
R P}, …
· 使用定理 `FractionalIdeal.isFractional`：∀ {R : Type u_1} [inst : CommRing R] {S : 
Submonoid R} {P : Type u_2} [inst_1 : CommRing P] [inst_2 : Algebra R P]   (I : 
FractionalIdeal S …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FractionalIdeal.mul_def`：mul_def (I J : FractionalIdeal S P) : I * J = ⟨
I * J, I.isFractional.mul J.isFractional⟩
-/
protected theorem mul_induction_on {I J : FractionalIdeal S P} {C : P → Prop} {r : P}
    (hr : r ∈ I * J) (hm : ∀ i ∈ I, ∀ j ∈ J, C (i * j)) (ha : ∀ x y, C x → C y → C (x + y)) :
    C r := by
  simp only [mul_def] at hr
  exact Submodule.mul_induction_on hr hm ha
/-
**FractionalIdeal.** 是 Mathlib 中的一个实例，位于命名空间 `FractionalIdeal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : NatCast (FractionalIdeal S P) :=
  ⟨Nat.unaryCast⟩
/-
**FractionalIdeal.coe_natCast** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：coe_natCast (n : Nat) : ((n : FractionalIdeal S P) : Submodule R P) = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FractionalIdeal.coe_zero`：coe_zero : ↑(0 : FractionalIdeal S P) = (⊥ : S
ubmodule R P)
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `FractionalIdeal.coe_one`：coe_one : (↑(1 : FractionalIdeal S P) : Submodu
le R P) = 1
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
-/
theorem coe_natCast (n : ℕ) : ((n : FractionalIdeal S P) : Submodule R P) = n :=
  show ((n.unaryCast : FractionalIdeal S P) : Submodule R P) = n
  by induction n <;> simp [*, Nat.unaryCast]
/-
**FractionalIdeal.commSemiring** 是 Mathlib 中的一个实例，位于命名空间 `FractionalIdeal`。
形式化陈述：commSemiring : CommSemiring (FractionalIdeal S P)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `FractionalIdeal.coe_zero`：coe_zero : ↑(0 : FractionalIdeal S P) = (⊥ : S
ubmodule R P)
· 使用定理 `FractionalIdeal.coe_one`：coe_one : (↑(1 : FractionalIdeal S P) : Submodu
le R P) = 1
· 使用定理 `FractionalIdeal.coe_add`：coe_add (I J : FractionalIdeal S P) : (↑(I + J)
 : Submodule R P) = I + J
· 使用定理 `FractionalIdeal.coe_mul`：coe_mul (I J : FractionalIdeal S P) : (↑(I * J)
 : Submodule R P) = I * J
· 使用定理 `FractionalIdeal.coe_nsmul`：coe_nsmul (n : Nat) (I : FractionalIdeal S P)
 : (↑(n • I) : Submodule R P) = n • (I : Submodule R P)
· 使用定理 `FractionalIdeal.coe_pow`：coe_pow (I : FractionalIdeal S P) (n : Nat) : ↑
(I ^ n) = (I : Submodule R P) ^ n
· 使用定理 `FractionalIdeal.coe_natCast`：coe_natCast (n : Nat) : ((n : FractionalIde
al S P) : Submodule R P) = n
-/
instance commSemiring : CommSemiring (FractionalIdeal S P) :=
  Function.Injective.commSemiring _ Subtype.coe_injective coe_zero coe_one coe_add coe_mul
    (fun _ _ => coe_nsmul _ _) coe_pow coe_natCast
/-
**FractionalIdeal.** 是 Mathlib 中的一个实例，位于命名空间 `FractionalIdeal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CanonicallyOrderedAdd (FractionalIdeal S P) where
  exists_add_of_le h := ⟨_, (sup_eq_right.mpr h).symm⟩
  le_add_self _ _ := le_sup_right
  le_self_add _ _ := le_sup_left
/-
**FractionalIdeal.** 是 Mathlib 中的一个实例，位于命名空间 `FractionalIdeal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsOrderedRing (FractionalIdeal S P) :=
  CanonicallyOrderedAdd.toIsOrderedRing

end Semiring

variable (S P)

/-- `FractionalIdeal.coeToSubmodule` as a bundled `RingHom`. -/
@[simps]
/-
**FractionalIdeal.coeSubmoduleHom** 是 Mathlib 中的一个定义，位于命名空间 `FractionalIdeal`。
形式化陈述：coeSubmoduleHom : FractionalIdeal S P ->+* Submodule R P where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `FractionalIdeal.coe_one`：coe_one : (↑(1 : FractionalIdeal S P) : Submodu
le R P) = 1
· 使用定理 `FractionalIdeal.coe_mul`：coe_mul (I J : FractionalIdeal S P) : (↑(I * J)
 : Submodule R P) = I * J
· 使用定理 `FractionalIdeal.coe_zero`：coe_zero : ↑(0 : FractionalIdeal S P) = (⊥ : S
ubmodule R P)
· 使用定理 `FractionalIdeal.coe_add`：coe_add (I J : FractionalIdeal S P) : (↑(I + J)
 : Submodule R P) = I + J

--- 原说明 ---
`FractionalIdeal.coeToSubmodule` as a bundled `RingHom`.
-/
def coeSubmoduleHom : FractionalIdeal S P →+* Submodule R P where
  toFun := coeToSubmodule
  map_one' := coe_one
  map_mul' := coe_mul
  map_zero' := coe_zero (S := S)
  map_add' := coe_add

variable {S P}

section Order

/-
**FractionalIdeal.coeIdeal_le_one** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：coeIdeal_le_one {I : Ideal R} : (I : FractionalIdeal S P) <= 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `FractionalIdeal.mem_coeIdeal`：mem_coeIdeal {x : P} {I : Ideal R} : x in 
(I : FractionalIdeal S P) ↔ exists x', x' in I ∧ algebraMap R P x' = x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `FractionalIdeal.mem_one_iff`：mem_one_iff {x : P} : x in (1 : FractionalI
deal S P) ↔ exists x' : R, algebraMap R P x' = x
-/
theorem coeIdeal_le_one {I : Ideal R} : (I : FractionalIdeal S P) ≤ 1 := fun _ hx =>
  let ⟨y, _, hy⟩ := (mem_coeIdeal S).mp hx
  (mem_one_iff S).mpr ⟨y, hy⟩
/-
**FractionalIdeal.le_one_iff_exists_coeIdeal** 是 Mathlib 中的一个定理，位于命名空间 `Fraction
alIdeal`。
形式化陈述：le_one_iff_exists_coeIdeal {J : FractionalIdeal S P} : J <= (1 : Fractiona
lIdeal S P) ↔ exists I : Ideal R, ↑I = J
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_ofPred`：mem_ofPred {a : α} {p : α -> Prop} : a in { x | p x } ↔ 
p a
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `Submodule.add_mem`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [inst
_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodule R M) {x y 
: M}, x…
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用引理 `FractionalIdeal.zero_mem`：zero_mem (I : FractionalIdeal S P) : 0 in I
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
· 使用定理 `FractionalIdeal.ext`：ext {I J : FractionalIdeal S P} : (forall x, x in I
 ↔ x in J) -> I = J
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `FractionalIdeal.mem_one_iff`：mem_one_iff {x : P} : x in (1 : FractionalI
deal S P) ↔ exists x' : R, algebraMap R P x' = x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `FractionalIdeal.coeIdeal_le_one`：coeIdeal_le_one {I : Ideal R} : (I : Fr
actionalIdeal S P) <= 1
-/
theorem le_one_iff_exists_coeIdeal {J : FractionalIdeal S P} :
    J ≤ (1 : FractionalIdeal S P) ↔ ∃ I : Ideal R, ↑I = J := by
  constructor
  · intro hJ
    refine ⟨⟨⟨⟨{ x : R | algebraMap R P x ∈ J }, ?_⟩, ?_⟩, ?_⟩, ?_⟩
    · intro a b ha hb
      rw [mem_ofPred, map_add]
      exact J.val.add_mem ha hb
    · rw [mem_ofPred, map_zero]
      exact J.zero_mem
    · intro c x hx
      rw [smul_eq_mul, mem_ofPred, map_mul, ← Algebra.smul_def]
      exact J.val.smul_mem c hx
    · ext x
      constructor
      · rintro ⟨y, hy, eq_y⟩
        rwa [← eq_y]
      · intro hx
        obtain ⟨y, rfl⟩ := (mem_one_iff S).mp (hJ hx)
        exact mem_ofPred.mpr ⟨y, hx, rfl⟩
  · rintro ⟨I, hI⟩
    rw [← hI]
    apply coeIdeal_le_one

@[simp]
/-
**FractionalIdeal.one_le** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：one_le {I : FractionalIdeal S P} : 1 <= I ↔ (1 : P) in I
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FractionalIdeal.coe_le_coe`：coe_le_coe {I J : FractionalIdeal S P} : (I 
: Submodule R P) <= (J : Submodule R P) ↔ I <= J
· 使用定理 `FractionalIdeal.coe_one`：coe_one : (↑(1 : FractionalIdeal S P) : Submodu
le R P) = 1
· 使用定理 `Submodule.one_le`：one_le {P : Submodule R A} : (1 : Submodule R A) <= P 
↔ (1 : A) in P
· 使用定理 `FractionalIdeal.mem_coe`：mem_coe {I : FractionalIdeal S P} {x : P} : x i
n (I : Submodule R P) ↔ x in I
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem one_le {I : FractionalIdeal S P} : 1 ≤ I ↔ (1 : P) ∈ I := by
  rw [← coe_le_coe, coe_one, Submodule.one_le, mem_coe]

variable (S P)

/-- `coeIdealHom (S : Submonoid R) P` is `(↑) : Ideal R → FractionalIdeal S P` as a ring hom -/
@[simps]
/-
**FractionalIdeal.coeIdealHom** 是 Mathlib 中的一个定义，位于命名空间 `FractionalIdeal`。
形式化陈述：coeIdealHom : Ideal R ->+* FractionalIdeal S P where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `FractionalIdeal.coeIdeal_mul`：coeIdeal_mul (I J : Ideal R) : (↑(I * J) :
 FractionalIdeal S P) = I * J
· 使用定理 `FractionalIdeal.coeIdeal_bot`：coeIdeal_bot : ((⊥ : Ideal R) : Fractional
Ideal S P) = 0
· 使用定理 `FractionalIdeal.coeIdeal_sup`：coeIdeal_sup (I J : Ideal R) : ↑(I ⊔ J) = 
(I + J : FractionalIdeal S P)

--- 原说明 ---
`coeIdealHom (S : Submonoid R) P` is `(↑) : Ideal R → FractionalIdeal S P` as a 
ring hom
-/
def coeIdealHom : Ideal R →+* FractionalIdeal S P where
  toFun := coeIdeal
  map_add' := coeIdeal_sup
  map_mul' := coeIdeal_mul
  map_one' := by rw [Ideal.one_eq_top, coeIdeal_top]
  map_zero' := coeIdeal_bot
/-
**FractionalIdeal.coeIdeal_pow** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：coeIdeal_pow (I : Ideal R) (n : Nat) : ↑(I ^ n) = (I : FractionalIdeal S P
) ^ n
参数：I : Ideal R；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.map_pow`：∀ {α : Type u_2} {β : Type u_3} [inst : Semiring α] [in
st_1 : Semiring β] (f : α →+* β) (a : α) (n : ℕ),   f (a ^ n) = f a ^ n
-/
theorem coeIdeal_pow (I : Ideal R) (n : ℕ) : ↑(I ^ n) = (I : FractionalIdeal S P) ^ n :=
  (coeIdealHom S P).map_pow _ n
/-
**FractionalIdeal.coeIdeal_finprod** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：coeIdeal_finprod [IsLocalization S P] {α : Sort*} {f : α -> Ideal R} (hS :
 S <= nonZeroDivisors R) : ((∏ᶠ a : α, f a : Ideal R) : FractionalIdeal S P) = ∏
ᶠ a : α, (f a : FractionalIdeal S P)
参数：hS : S <= nonZeroDivisors R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.map_finprod_of_injective`：MonoidHom.map_finprod_of_injective (
g : M ->* N) (hg : Injective g) (f : α -> M) : g (∏ᶠ i, f i) = ∏ᶠ i, g (f i)
· 使用定理 `FractionalIdeal.coeIdeal_injective'`：coeIdeal_injective' (h : S <= nonZe
roDivisors R) : Function.Injective (fun (I : Ideal R) => (I : FractionalIdeal S 
P))
-/
theorem coeIdeal_finprod [IsLocalization S P] {α : Sort*} {f : α → Ideal R}
    (hS : S ≤ nonZeroDivisors R) :
    ((∏ᶠ a : α, f a : Ideal R) : FractionalIdeal S P) = ∏ᶠ a : α, (f a : FractionalIdeal S P) :=
  MonoidHom.map_finprod_of_injective (coeIdealHom S P).toMonoidHom (coeIdeal_injective' hS) f

end Order

section FG

variable {R : Type*} [CommRing R] [IsDomain R] {S : Submonoid R}
variable {P : Type*} [Nontrivial P] [CommRing P] [Algebra R P] [Module.IsTorsionFree R P]

/-- The fractional ideals of a Noetherian ring are finitely generated. -/
/-
**FractionalIdeal.fg_of_isNoetherianRing** 是 Mathlib 中的一个引理，位于命名空间 `FractionalId
eal`。
形式化陈述：fg_of_isNoetherianRing [hR : IsNoetherianRing R] (hS : S <= R⁰) (I : Fract
ionalIdeal S P) : FG I.coeToSubmodule
参数：hS : S <= R⁰；I : FractionalIdeal S P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsNoetherian.noetherian`：∀ {R : Type u_1} {M : Type u_2} {inst : Semirin
g R} {inst_1 : AddCommMonoid M} {inst_2 : _root_.Module R M}   [self : IsNoether
ian R M] (s :…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.Finite.iff_fg`：iff_fg {N : Submodule R M} : Module.Finite R N ↔ N
.FG
· 使用定理 `Module.Finite.equiv`：equiv [Module.Finite R M] (e : M ≃ₗ[R] N) : Module.
Finite R N
· 使用定理 `nonZeroDivisors.coe_ne_zero`：nonZeroDivisors.coe_ne_zero (x : M₀⁰) : (x 
: M₀) != 0
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `SetLike.coe_mem`：coe_mem (x : p) : (x : B) in p

--- 原说明 ---
The fractional ideals of a Noetherian ring are finitely generated.
-/
lemma fg_of_isNoetherianRing [hR : IsNoetherianRing R] (hS : S ≤ R⁰) (I : FractionalIdeal S P) :
    FG I.coeToSubmodule := by
  have := hR.noetherian I.num
  rw [← Module.Finite.iff_fg] at this ⊢
  exact .equiv (I.equivNum <| coe_ne_zero ⟨(I.den : R), hS (SetLike.coe_mem I.den)⟩).symm

end FG

end FractionalIdeal

