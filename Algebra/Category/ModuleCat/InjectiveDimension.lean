/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Ext.DimensionShifting
public import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
public import Mathlib.Algebra.Category.ModuleCat.Injective
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Abelian.Injective.Dimension

/-!

# Injective Dimension in ModuleCat

This file deals with preservation of `injectiveDimension` in (semi) linear equivalences.
Previously we only know this for linear equivalence within same universe level, now it works with
all universe level where the ring `R` is small.

## Main Results

* `ModuleCat.hasInjectiveDimensionLE_iff_of_linearEquiv`: `HasInjectiveDimensionLE` is preserved
  under arbitrary linear equivalence.

* `ModuleCat.hasInjectiveDimensionLE_iff_of_semiLinearEquiv`: `HasInjectiveDimensionLE` is preserved
  under arbitrary semi-linear equivalence.

* `ModuleCat.injectiveDimension_eq_of_semiLinearEquiv`: `injectiveDimension` is preserved
  under arbitrary semi-linear equivalence.

* `ModuleCat.injectiveDimension_eq_of_linearEquiv`: `injectiveDimension` is preserved
  under arbitrary linear equivalence.

-/

public section

universe v v' u u'

variable {R : Type u} [Ring R]

open CategoryTheory Abelian

namespace ModuleCat

/-
**ModuleCat.hasInjectiveDimensionLE_iff_of_linearEquiv_aux** 是 Mathlib 中的一个引理，位于
命名空间 `ModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma hasInjectiveDimensionLE_iff_of_linearEquiv_aux [Small.{v} R]
    {M : ModuleCat.{v} R} {N : ModuleCat.{max v v'} R}
    (e : M ≃ₗ[R] N) (n : ℕ) : HasInjectiveDimensionLE M n ↔ HasInjectiveDimensionLE N n := by
  have : Small.{max v v'} R := small_lift R
  induction n generalizing M N with
  | zero =>
    simp [HasInjectiveDimensionLE, ← injective_iff_hasInjectiveDimensionLT_one,
      ← Module.injective_iff_injective_object R M, ← Module.injective_iff_injective_object R N,
      ← Module.Baer.iff_injective, Module.Baer.congr e]
  | succ n ih =>
    let ⟨I, _, f, _⟩ := EnoughInjectives.presentation M
    have injf : Function.Injective f.hom := (mono_iff_injective f).mp ‹_›
    let S : ShortComplex (ModuleCat.{v} R) :=
      ModuleCat.shortComplexOfCompEqZero _ _ f.hom.exact_map_mkQ_range.linearMap_comp_eq_zero
    have exactS := ModuleCat.shortComplex_shortExact S
      f.hom.exact_map_mkQ_range injf (Submodule.mkQ_surjective _)
    let I' := ModuleCat.of R (ULift.{v'} I)
    let f' : N →ₗ[R] I' := ULift.moduleEquiv.symm.toLinearMap.comp (f.hom.comp e.symm.toLinearMap)
    have injf' : Function.Injective f' := by simpa [f']
    let S' : ShortComplex (ModuleCat.{max v v'} R) :=
      ModuleCat.shortComplexOfCompEqZero _ _ f'.exact_map_mkQ_range.linearMap_comp_eq_zero
    have exactS' := ModuleCat.shortComplex_shortExact S'
      f'.exact_map_mkQ_range injf' (Submodule.mkQ_surjective _)
    let eCoker : ModuleCat.of R (I ⧸ f.hom.range) ≃ₗ[R] ModuleCat.of R (I' ⧸ f'.range) :=
      Submodule.Quotient.equiv _ _ ULift.moduleEquiv.symm (by simp [f', LinearMap.range_comp])
    exact (exactS.hasInjectiveDimensionLT_X₃_iff n inferInstance).symm.trans
      ((ih eCoker).trans (exactS'.hasInjectiveDimensionLT_X₃_iff n inferInstance))
/-
**ModuleCat.hasInjectiveDimensionLE_iff_of_linearEquiv** 是 Mathlib 中的一个引理，位于命名空间
 `ModuleCat`。
形式化陈述：hasInjectiveDimensionLE_iff_of_linearEquiv [Small.{v} R] [Small.{v'} R] {M
 : ModuleCat.{v} R} {N : ModuleCat.{v'} R} (e : M ≃ₗ[R] N) (n : Nat) : HasInject
iveDimensionLE M n ↔ HasInjectiveDimensionLE N n
参数：e : M ≃ₗ[R] N；n : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.Algebra.Category.ModuleCat.InjectiveDimension.0.ModuleC
at.hasInjectiveDimensionLE_iff_of_linearEquiv_aux`：∀ {R : Type u} [inst : Ring R
] [Small.{v, u} R] {M : ModuleCat R} {N : ModuleCat R} (e : ↑M ≃ₗ[R] ↑N) (n : ℕ)
,   CategoryTheory.HasInjective…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma hasInjectiveDimensionLE_iff_of_linearEquiv [Small.{v} R] [Small.{v'} R]
    {M : ModuleCat.{v} R} {N : ModuleCat.{v'} R}
    (e : M ≃ₗ[R] N) (n : ℕ) : HasInjectiveDimensionLE M n ↔ HasInjectiveDimensionLE N n := by
  let eM : M ≃ₗ[R] ModuleCat.of R (ULift.{v'} M) := ULift.moduleEquiv.symm
  rw [hasInjectiveDimensionLE_iff_of_linearEquiv_aux eM,
    ← hasInjectiveDimensionLE_iff_of_linearEquiv_aux (e.symm.trans eM)]

section SemiLinear

variable [Small.{v} R] {R' : Type u'} [Ring R'] (eR : R ≃+* R')

attribute [local instance] RingHomInvPair.of_ringEquiv

set_option backward.isDefEq.respectTransparency.types false in
/-
**ModuleCat.hasInjectiveDimensionLE_iff_of_semiLinearEquiv_aux** 是 Mathlib 中的一个引
理，位于命名空间 `ModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma hasInjectiveDimensionLE_iff_of_semiLinearEquiv_aux [Small.{v} R']
    {M : ModuleCat.{v} R} {N : ModuleCat.{v} R'} (e : M ≃ₛₗ[RingHomClass.toRingHom eR] N)
    (n : ℕ) : HasInjectiveDimensionLE M n ↔ HasInjectiveDimensionLE N n := by
  induction n generalizing M N with
  | zero =>
    simp only [HasInjectiveDimensionLE, zero_add, ← injective_iff_hasInjectiveDimensionLT_one,
      ← Module.injective_iff_injective_object R M, ← Module.injective_iff_injective_object R' N]
    exact ⟨fun _ ↦ Module.Injective.of_ringEquiv eR e,
      fun _ ↦ Module.Injective.of_ringEquiv eR.symm e.symm⟩
  | succ n ih =>
    let ⟨I', _, f', _⟩ := EnoughInjectives.presentation N
    have : Module.Injective R' I' := Module.injective_module_of_injective_object R' I'
    have injf' : Function.Injective f'.hom := (mono_iff_injective f').mp ‹_›
    let S' : ShortComplex (ModuleCat.{v} R') :=
      ModuleCat.shortComplexOfCompEqZero _ _ f'.hom.exact_map_mkQ_range.linearMap_comp_eq_zero
    have exactS' := ModuleCat.shortComplex_shortExact S'
      f'.hom.exact_map_mkQ_range injf' (Submodule.mkQ_surjective _)
    let I : ModuleCat.{v} R :=
      let := Module.compHom I' eR.toRingHom
      ModuleCat.of R I'
    let eI : I ≃ₛₗ[RingHomClass.toRingHom eR] I' := {
      __ := AddEquiv.refl I
      map_smul' r i := rfl }
    have : Injective (ModuleCat.of R I) := by
      rw [← Module.injective_iff_injective_object]
      exact Module.Injective.of_ringEquiv eR.symm eI.symm
    let f : M →ₗ[R] I := eI.symm.toLinearMap.comp (f'.hom.comp e.toLinearMap)
    have injf : Function.Injective f := by simpa [f]
    let S : ShortComplex (ModuleCat.{v} R) :=
      ModuleCat.shortComplexOfCompEqZero _ _ f.exact_map_mkQ_range.linearMap_comp_eq_zero
    have exactS := ModuleCat.shortComplex_shortExact S
      f.exact_map_mkQ_range injf (Submodule.mkQ_surjective _)
    let eCoker : ModuleCat.of R (I ⧸ f.range) ≃ₛₗ[RingHomClass.toRingHom eR]
      ModuleCat.of R' (I' ⧸ f'.hom.range) :=
      Submodule.Quotient.equiv _ _ eI
        (by simp [f, ← Submodule.map_symm_eq_iff eI, LinearMap.range_comp])
    exact (exactS.hasInjectiveDimensionLT_X₃_iff n inferInstance).symm.trans
      ((ih eCoker).trans (exactS'.hasInjectiveDimensionLT_X₃_iff n inferInstance))

set_option backward.isDefEq.respectTransparency.types false in
attribute [local instance] small_lift in
/-
**ModuleCat.hasInjectiveDimensionLE_iff_of_semiLinearEquiv** 是 Mathlib 中的一个引理，位于
命名空间 `ModuleCat`。
形式化陈述：hasInjectiveDimensionLE_iff_of_semiLinearEquiv [Small.{v'} R'] {M : Module
Cat.{v} R} {N : ModuleCat.{v'} R'} (e : M ≃ₛₗ[RingHomClass.toRingHom eR] N) (n :
 Nat) : HasInjectiveDimensionLE M n ↔ HasInjectiveDimensionLE N n
参数：e : M ≃ₛₗ[RingHomClass.toRingHom eR] N；n : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用引理 `RingHomInvPair.of_ringEquiv`：of_ringEquiv (e : R₁ ≃+* R₂) : RingHomInvPa
ir (↑e : R₁ ->+* R₂) ↑e.symm
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.Algebra.Category.ModuleCat.InjectiveDimension.0.ModuleC
at.hasInjectiveDimensionLE_iff_of_linearEquiv_aux`：∀ {R : Type u} [inst : Ring R
] [Small.{v, u} R] {M : ModuleCat R} {N : ModuleCat R} (e : ↑M ≃ₗ[R] ↑N) (n : ℕ)
,   CategoryTheory.HasInjective…
· 使用定理 `_private.Mathlib.Algebra.Category.ModuleCat.InjectiveDimension.0.ModuleC
at.hasInjectiveDimensionLE_iff_of_semiLinearEquiv_aux`：∀ {R : Type u} [inst : Ri
ng R] [Small.{v, u} R] {R' : Type u'} [inst_2 : Ring R'] (eR : R ≃+* R') [Small.
{v, u'} R']   {M : ModuleCat R} {N …
· 使用定理 `small_lift`：small_lift (α : Type u) [hα : Small.{v} α] : Small.{max v w}
 α
-/
lemma hasInjectiveDimensionLE_iff_of_semiLinearEquiv [Small.{v'} R']
    {M : ModuleCat.{v} R} {N : ModuleCat.{v'} R'} (e : M ≃ₛₗ[RingHomClass.toRingHom eR] N)
    (n : ℕ) : HasInjectiveDimensionLE M n ↔ HasInjectiveDimensionLE N n := by
  let eM : M ≃ₗ[R] ModuleCat.of R (ULift.{v'} M) := ULift.moduleEquiv.symm
  let eN : N ≃ₗ[R'] ModuleCat.of R' (ULift.{v} N) := ULift.moduleEquiv.symm
  rw [hasInjectiveDimensionLE_iff_of_linearEquiv_aux eM,
    hasInjectiveDimensionLE_iff_of_linearEquiv_aux eN]
  exact hasInjectiveDimensionLE_iff_of_semiLinearEquiv_aux eR ((eM.symm.trans e).trans eN) n
/-
**ModuleCat.injectiveDimension_eq_of_semiLinearEquiv** 是 Mathlib 中的一个引理，位于命名空间 `
ModuleCat`。
形式化陈述：injectiveDimension_eq_of_semiLinearEquiv [Small.{v'} R'] {M : ModuleCat.{v
} R} {N : ModuleCat.{v'} R'} (e : M ≃ₛₗ[RingHomClass.toRingHom eR] N) : injectiv
eDimension M = injectiveDimension N
参数：e : M ≃ₛₗ[RingHomClass.toRingHom eR] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用引理 `RingHomInvPair.of_ringEquiv`：of_ringEquiv (e : R₁ ≃+* R₂) : RingHomInvPa
ir (↑e : R₁ ->+* R₂) ↑e.symm
· 使用定理 `eq_of_forall_ge_iff`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α},
 (∀ (c : α), a ≤ c ↔ b ≤ c) → a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Equiv.subsingleton_congr`：subsingleton_congr (e : α ≃ β) : Subsingleton 
α ↔ Subsingleton β
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用引理 `ModuleCat.hasInjectiveDimensionLE_iff_of_semiLinearEquiv`：hasInjectiveDi
mensionLE_iff_of_semiLinearEquiv [Small.{v'} R'] {M : ModuleCat.{v} R} {N : Modu
leCat.{v'} R'} (e : M ≃ₛₗ[RingHomClass.toRingH…
-/
lemma injectiveDimension_eq_of_semiLinearEquiv [Small.{v'} R']
    {M : ModuleCat.{v} R} {N : ModuleCat.{v'} R'} (e : M ≃ₛₗ[RingHomClass.toRingHom eR] N) :
    injectiveDimension M = injectiveDimension N := by
  refine eq_of_forall_ge_iff (fun N ↦ ?_)
  induction N with
  | bot => simpa [injectiveDimension_eq_bot_iff, ModuleCat.isZero_iff_subsingleton] using
      e.subsingleton_congr
  | coe n =>
    induction n with
    | top => simp
    | coe n =>
      simp [injectiveDimension_le_iff, hasInjectiveDimensionLE_iff_of_semiLinearEquiv eR e n]

end SemiLinear

variable [Small.{v} R] [Small.{v'} R] {M : ModuleCat.{v} R} {N : ModuleCat.{v'} R}

/-
**ModuleCat.injectiveDimension_eq_of_linearEquiv** 是 Mathlib 中的一个引理，位于命名空间 `Modu
leCat`。
形式化陈述：injectiveDimension_eq_of_linearEquiv (e : M ≃ₗ[R] N) : injectiveDimension 
M = injectiveDimension N
参数：e : M ≃ₗ[R] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ModuleCat.injectiveDimension_eq_of_semiLinearEquiv`：injectiveDimension_e
q_of_semiLinearEquiv [Small.{v'} R'] {M : ModuleCat.{v} R} {N : ModuleCat.{v'} R
'} (e : M ≃ₛₗ[RingHomClass.toRingHom eR]…
-/
lemma injectiveDimension_eq_of_linearEquiv (e : M ≃ₗ[R] N) :
    injectiveDimension M = injectiveDimension N :=
  injectiveDimension_eq_of_semiLinearEquiv.{v, v'} (M := M) (N := N) (RingEquiv.refl R) e

end ModuleCat

