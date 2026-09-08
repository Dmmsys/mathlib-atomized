/-
Copyright (c) 2024 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.FractionalIdeal.Norm
public import Mathlib.RingTheory.FractionalIdeal.Operations

/-!

# Fractional ideals of number fields

Prove some results on the fractional ideals of number fields.

## Main definitions and results

* `NumberField.basisOfFractionalIdeal`: A `ℚ`-basis of `K` that spans `I` over `ℤ` where `I` is
  a fractional ideal of a number field `K`.
* `NumberField.det_basisOfFractionalIdeal_eq_absNorm`: for `I` a fractional ideal of a number
  field `K`, the absolute value of the determinant of the base change from `integralBasis` to
  `basisOfFractionalIdeal I` is equal to the norm of `I`.
-/

@[expose] public section

variable (K : Type*) [Field K] [NumberField K]

namespace NumberField

open scoped nonZeroDivisors

section Basis

open Module

/-
**NumberField.** 是 Mathlib 中的一个实例，位于命名空间 `NumberField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (I : FractionalIdeal (𝓞 K)⁰ K) : Module.Free ℤ I := by
  refine Free.of_equiv (LinearEquiv.restrictScalars ℤ (I.equivNum ?_)).symm
  exact nonZeroDivisors.coe_ne_zero I.den
/-
**NumberField.** 是 Mathlib 中的一个实例，位于命名空间 `NumberField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (I : FractionalIdeal (𝓞 K)⁰ K) : Module.Finite ℤ I := by
  refine Module.Finite.of_surjective
    (LinearEquiv.restrictScalars ℤ (I.equivNum ?_)).symm.toLinearMap (LinearEquiv.surjective _)
  exact nonZeroDivisors.coe_ne_zero I.den
/-
**NumberField.** 是 Mathlib 中的一个实例，位于命名空间 `NumberField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    IsLocalizedModule ℤ⁰ ((Submodule.subtype (I : Submodule (𝓞 K) K)).restrictScalars ℤ) where
  map_units x := by
    rw [← (Algebra.lmul _ _).commutes, Algebra.lmul_isUnit_iff, isUnit_iff_ne_zero, eq_intCast,
      Int.cast_ne_zero]
    exact nonZeroDivisors.coe_ne_zero x
  surj x := by
    obtain ⟨⟨a, _, d, hd, rfl⟩, h⟩ := IsLocalization.surj (Algebra.algebraMapSubmonoid (𝓞 K) ℤ⁰) x
    refine ⟨⟨⟨Ideal.absNorm I.1.num * (algebraMap _ K a), I.1.num_le ?_⟩, d * Ideal.absNorm I.1.num,
      ?_⟩, ?_⟩
    · refine (IsLocalization.mem_coeSubmodule _ _).mpr ⟨Ideal.absNorm I.1.num * a, ?_, ?_⟩
      · exact Ideal.mul_mem_right _ _ I.1.num.absNorm_mem
      · rw [map_mul, map_natCast]
    · refine Submonoid.mul_mem _ hd (mem_nonZeroDivisors_of_ne_zero ?_)
      rw [Nat.cast_ne_zero, ne_eq, Ideal.absNorm_eq_zero_iff]
      exact FractionalIdeal.num_eq_zero_iff.not.mpr <| Units.ne_zero I
    · simp_rw [LinearMap.coe_restrictScalars, Submodule.coe_subtype] at h ⊢
      rw [← h]
      simp only [Submonoid.mk_smul, zsmul_eq_mul, Int.cast_mul, Int.cast_natCast, algebraMap_int_eq,
        eq_intCast, map_intCast]
      ring
  exists_of_eq h :=
    ⟨1, by rwa [one_smul, one_smul, ← (Submodule.injective_subtype I.1.coeToSubmodule).eq_iff]⟩

/-- A `ℤ`-basis of a fractional ideal. -/
/-
**NumberField.fractionalIdealBasis** 是 Mathlib 中的一个定义，位于命名空间 `NumberField`。
形式化陈述：fractionalIdealBasis (I : FractionalIdeal (𝓞 K)⁰ K) : Basis (Free.ChooseBa
sisIndex Int I) Int I
参数：I : FractionalIdeal (𝓞 K)⁰ K。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.instFreeIntSubtypeMemSubmoduleRingOfIntegersCoeToSubmodule`：
∀ (K : Type u_1) [inst : Field K] [NumberField K]   (I : FractionalIdeal (nonZer
oDivisors (NumberField.RingOfIntegers K)) K), Module.Free ℤ …

--- 原说明 ---
A `ℤ`-basis of a fractional ideal.
-/
noncomputable def fractionalIdealBasis (I : FractionalIdeal (𝓞 K)⁰ K) :
    Basis (Free.ChooseBasisIndex ℤ I) ℤ I := Free.chooseBasis ℤ I

/-- A `ℚ`-basis of `K` that spans `I` over `ℤ`, see `mem_span_basisOfFractionalIdeal` below. -/
/-
**NumberField.basisOfFractionalIdeal** 是 Mathlib 中的一个定义，位于命名空间 `NumberField`。
形式化陈述：basisOfFractionalIdeal (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : Basis (Free.Cho
oseBasisIndex Int I) Rat K
参数：I : (FractionalIdeal (𝓞 K)⁰ K)ˣ。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.RingOfIntegers.instIsDedekindDomain`：∀ (K : Type u_1) [inst 
: Field K] [NumberField K], IsDedekindDomain (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.RingOfIntegers.instIsFractionRing`：∀ {K : Type u_1} [inst : 
Field K] [NumberField K], IsFractionRing (NumberField.RingOfIntegers K) K
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `NumberField.instIsLocalizedModuleIntSubtypeMemSubmoduleRingOfIntegersCoe
ToSubmoduleValFractionalIdealNonZeroDivisorsRestrictScalarsSubtype`：∀ (K : Type 
u_1) [inst : Field K] [inst_1 : NumberField K]   (I : (FractionalIdeal (nonZeroD
ivisors (NumberField.RingOfIntegers K)) K)ˣ),   …

--- 原说明 ---
A `ℚ`-basis of `K` that spans `I` over `ℤ`, see `mem_span_basisOfFractionalIdeal
` below.
-/
noncomputable def basisOfFractionalIdeal (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Basis (Free.ChooseBasisIndex ℤ I) ℚ K :=
  (fractionalIdealBasis K I.1).ofIsLocalizedModule ℚ ℤ⁰
    ((Submodule.subtype (I : Submodule (𝓞 K) K)).restrictScalars ℤ)
/-
**NumberField.basisOfFractionalIdeal_apply** 是 Mathlib 中的一个定理，位于命名空间 `NumberFiel
d`。
形式化陈述：basisOfFractionalIdeal_apply (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (i : Free.C
hooseBasisIndex Int I) : basisOfFractionalIdeal K I i = fractionalIdealBasis K I
.1 i
参数：I : (FractionalIdeal (𝓞 K)⁰ K)ˣ；i : Free.ChooseBasisIndex Int I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.RingOfIntegers.instIsDedekindDomain`：∀ (K : Type u_1) [inst 
: Field K] [NumberField K], IsDedekindDomain (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.RingOfIntegers.instIsFractionRing`：∀ {K : Type u_1} [inst : 
Field K] [NumberField K], IsFractionRing (NumberField.RingOfIntegers K) K
· 使用定理 `NumberField.instFreeIntSubtypeMemSubmoduleRingOfIntegersCoeToSubmodule`：
∀ (K : Type u_1) [inst : Field K] [NumberField K]   (I : FractionalIdeal (nonZer
oDivisors (NumberField.RingOfIntegers K)) K), Module.Free ℤ …
· 使用定理 `Module.Basis.ofIsLocalizedModule_apply`：ofIsLocalizedModule_apply (i : ι
) : b.ofIsLocalizedModule Rₛ S f i = f (b i)
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `NumberField.instIsLocalizedModuleIntSubtypeMemSubmoduleRingOfIntegersCoe
ToSubmoduleValFractionalIdealNonZeroDivisorsRestrictScalarsSubtype`：∀ (K : Type 
u_1) [inst : Field K] [inst_1 : NumberField K]   (I : (FractionalIdeal (nonZeroD
ivisors (NumberField.RingOfIntegers K)) K)ˣ),   …
-/
theorem basisOfFractionalIdeal_apply (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (i : Free.ChooseBasisIndex ℤ I) :
    basisOfFractionalIdeal K I i = fractionalIdealBasis K I.1 i :=
  (fractionalIdealBasis K I.1).ofIsLocalizedModule_apply ℚ ℤ⁰ _ i
/-
**NumberField.mem_span_basisOfFractionalIdeal** 是 Mathlib 中的一个定理，位于命名空间 `NumberF
ield`。
形式化陈述：mem_span_basisOfFractionalIdeal {I : (FractionalIdeal (𝓞 K)⁰ K)ˣ} {x : K} 
: x in Submodule.span Int (Set.range (basisOfFractionalIdeal K I)) ↔ x in (I : S
et K)
参数：FractionalIdeal (𝓞 K)⁰ K。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.RingOfIntegers.instIsDedekindDomain`：∀ (K : Type u_1) [inst 
: Field K] [NumberField K], IsDedekindDomain (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.RingOfIntegers.instIsFractionRing`：∀ {K : Type u_1} [inst : 
Field K] [NumberField K], IsFractionRing (NumberField.RingOfIntegers K) K
· 使用定理 `NumberField.instFreeIntSubtypeMemSubmoduleRingOfIntegersCoeToSubmodule`：
∀ (K : Type u_1) [inst : Field K] [NumberField K]   (I : FractionalIdeal (nonZer
oDivisors (NumberField.RingOfIntegers K)) K), Module.Free ℤ …
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `NumberField.instIsLocalizedModuleIntSubtypeMemSubmoduleRingOfIntegersCoe
ToSubmoduleValFractionalIdealNonZeroDivisorsRestrictScalarsSubtype`：∀ (K : Type 
u_1) [inst : Field K] [inst_1 : NumberField K]   (I : (FractionalIdeal (nonZeroD
ivisors (NumberField.RingOfIntegers K)) K)ˣ),   …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.basisOfFractionalIdeal.eq_1`：∀ (K : Type u_1) [inst : Field 
K] [inst_1 : NumberField K]   (I : (FractionalIdeal (nonZeroDivisors (NumberFiel
d.RingOfIntegers K)) K)ˣ),   …
· 使用定理 `Module.Basis.ofIsLocalizedModule_span`：ofIsLocalizedModule_span : span R
 (Set.range (b.ofIsLocalizedModule Rₛ S f)) = LinearMap.range f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_span_basisOfFractionalIdeal {I : (FractionalIdeal (𝓞 K)⁰ K)ˣ} {x : K} :
    x ∈ Submodule.span ℤ (Set.range (basisOfFractionalIdeal K I)) ↔ x ∈ (I : Set K) := by
  rw [basisOfFractionalIdeal, (fractionalIdealBasis K I.1).ofIsLocalizedModule_span ℚ ℤ⁰ _]
  simp

open Module in
/-
**NumberField.fractionalIdeal_rank** 是 Mathlib 中的一个定理，位于命名空间 `NumberField`。
形式化陈述：fractionalIdeal_rank (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : finrank Int I = f
inrank Int (𝓞 K)
参数：I : (FractionalIdeal (𝓞 K)⁰ K)ˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.RingOfIntegers.instIsDedekindDomain`：∀ (K : Type u_1) [inst 
: Field K] [NumberField K], IsDedekindDomain (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.RingOfIntegers.instIsFractionRing`：∀ {K : Type u_1} [inst : 
Field K] [NumberField K], IsFractionRing (NumberField.RingOfIntegers K) K
· 使用定理 `NumberField.instFreeIntSubtypeMemSubmoduleRingOfIntegersCoeToSubmodule`：
∀ (K : Type u_1) [inst : Field K] [NumberField K]   (I : FractionalIdeal (nonZer
oDivisors (NumberField.RingOfIntegers K)) K), Module.Free ℤ …
· 使用定理 `NumberField.instFiniteIntSubtypeMemSubmoduleRingOfIntegersCoeToSubmodule
`：∀ (K : Type u_1) [inst : Field K] [NumberField K]   (I : FractionalIdeal (nonZ
eroDivisors (NumberField.RingOfIntegers K)) K), Module.Finite …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.finrank_eq_card_chooseBasisIndex`：∀ (R : Type u) (M : Type v) [in
st : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [inst
_3 : Module.Free R M] [Strong…
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `NumberField.RingOfIntegers.rank`：∀ (K : Type u_1) [inst : Field K] [inst
_1 : NumberField K],   Module.finrank ℤ (NumberField.RingOfIntegers K) = Module.
finrank ℚ K
· 使用定理 `Module.finrank_eq_card_basis`：finrank_eq_card_basis {ι : Type w} [Fintyp
e ι] (h : Basis ι R M) : finrank R M = Fintype.card ι
-/
theorem fractionalIdeal_rank (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    finrank ℤ I = finrank ℤ (𝓞 K) := by
  rw [finrank_eq_card_chooseBasisIndex, RingOfIntegers.rank,
    finrank_eq_card_basis (basisOfFractionalIdeal K I)]

end Basis

section Norm

open Module

/-- The absolute value of the determinant of the base change from `integralBasis` to
`basisOfFractionalIdeal I` is equal to the norm of `I`. -/
/-
**NumberField.det_basisOfFractionalIdeal_eq_absNorm** 是 Mathlib 中的一个定理，位于命名空间 `N
umberField`。
形式化陈述：det_basisOfFractionalIdeal_eq_absNorm (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (e
 : (Free.ChooseBasisIndex Int (𝓞 K)) ≃ (Free.ChooseBasisIndex Int I)) : |(integr
alBasis K).det ((basisOfFractionalIdeal K I).reindex e.symm)| = FractionalIdeal.
absNorm I.1
参数：I : (FractionalIdeal (𝓞 K)⁰ K)ˣ；e : (Free.ChooseBasisIndex Int (𝓞 K)) ≃ (Free
.ChooseBasisIndex Int I)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.RingOfIntegers.instIsDedekindDomain`：∀ (K : Type u_1) [inst 
: Field K] [NumberField K], IsDedekindDomain (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.RingOfIntegers.instIsFractionRing`：∀ {K : Type u_1} [inst : 
Field K] [NumberField K], IsFractionRing (NumberField.RingOfIntegers K) K
· 使用定理 `NumberField.RingOfIntegers.instFreeInt`：∀ (K : Type u_1) [inst : Field K
] [NumberField K], Module.Free ℤ (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.instFreeIntSubtypeMemSubmoduleRingOfIntegersCoeToSubmodule`：
∀ (K : Type u_1) [inst : Field K] [NumberField K]   (I : FractionalIdeal (nonZer
oDivisors (NumberField.RingOfIntegers K)) K), Module.Free ℤ …
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `AddMonoid.fg_of_addGroup_fg`：∀ {G : Type u_3} [inst : AddGroup G] [AddGr
oup.FG G], AddMonoid.FG G
· 使用定理 `NumberField.RingOfIntegers.instFG`：∀ (K : Type u_1) [inst : Field K] [Nu
mberField K], AddGroup.FG (NumberField.RingOfIntegers K)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `NumberField.RingOfIntegers.instIsLocalizationAlgebraMapSubmonoidIntNonZe
roDivisors`：∀ (K : Type u_1) [inst : Field K] [NumberField K],   IsLocalization 
(Algebra.algebraMapSubmonoid (NumberField.RingOfIntegers K) (nonZeroDivi…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FractionalIdeal.abs_det_basis_change`：abs_det_basis_change [IsDomain K] 
{ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι Int R) (I : FractionalIdeal
 R⁰ K) (bI : Basis ι Int I…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Module.Basis.coe_reindex`：coe_reindex : (b.reindex e : ι' -> M) = b ∘ e.
symm
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `NumberField.basisOfFractionalIdeal_apply`：basisOfFractionalIdeal_apply (
I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (i : Free.ChooseBasisIndex Int I) : basisOfFrac
tionalIdeal K I i = fractional…

--- 原说明 ---
The absolute value of the determinant of the base change from `integralBasis` to
`basisOfFractionalIdeal I` is equal to the norm of `I`.
-/
theorem det_basisOfFractionalIdeal_eq_absNorm (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (e : (Free.ChooseBasisIndex ℤ (𝓞 K)) ≃ (Free.ChooseBasisIndex ℤ I)) :
    |(integralBasis K).det ((basisOfFractionalIdeal K I).reindex e.symm)| =
      FractionalIdeal.absNorm I.1 := by
  rw [← FractionalIdeal.abs_det_basis_change (RingOfIntegers.basis K) I.1
    ((fractionalIdealBasis K I.1).reindex e.symm)]
  congr
  ext
  simpa using basisOfFractionalIdeal_apply K I _

end Norm

end NumberField

