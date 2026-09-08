/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Localization
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Abelian.Projective.Dimension
public import Mathlib.CategoryTheory.Preadditive.Projective.Preserves
public import Mathlib.RingTheory.LocalProperties.Projective

/-!
# The Projective Dimension Equal to Supremum over Localizations

In this file, we proved that projective dimension equal to supremum over localizations

## Main definition and results

-/

public section

universe v u

variable {R : Type u} [CommRing R]

namespace ModuleCat

open CategoryTheory

set_option backward.isDefEq.respectTransparency false in
/-
**ModuleCat.** 是 Mathlib 中的一个实例，位于命名空间 `ModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Small.{v} R] (S : Submonoid R) :
    (ModuleCat.localizedModuleFunctor.{v} S).PreservesProjectiveObjects where
  projective_obj X {proj} := by
    have : Small.{v} (Localization S) := small_of_surjective Localization.mkHom_surjective
    rw [← IsProjective.iff_projective] at proj ⊢
    simpa [ModuleCat.localizedModuleFunctor] using
      Module.projective_of_isLocalizedModule S (X.localizedModuleMkLinearMap S)

open Limits in
/-
**ModuleCat.localizedModule_hasProjectiveDimensionLE** 是 Mathlib 中的一个引理，位于命名空间 `
ModuleCat`。
形式化陈述：localizedModule_hasProjectiveDimensionLE [Small.{v, u} R] (n : Nat) (S : S
ubmonoid R) (M : ModuleCat.{v} R) [HasProjectiveDimensionLE M n] : HasProjective
DimensionLE (M.localizedModule S) n
参数：n : Nat；S : Submonoid R；M : ModuleCat.{v} R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `small_of_surjective`：small_of_surjective {α : Type v} {β : Type w} [Smal
l.{u} α] {f : α -> β} (hf : Function.Surjective f) : Small.{u} β
· 使用引理 `Localization.mkHom_surjective`：mkHom_surjective : Surjective (mkHom (S
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.projective_iff_hasProjectiveDimensionLT_one`：projective_i
ff_hasProjectiveDimensionLT_one : Projective X ↔ HasProjectiveDimensionLT X 1
· 使用定理 `IsProjective.iff_projective`：IsProjective.iff_projective [Small.{v} R] (
P : Type v) [AddCommGroup P] [Module R P] : Module.Projective R P ↔ Projective (
of R P)
· 使用定理 `Module.projective_of_isLocalizedModule`：Module.projective_of_isLocalized
Module {Rₛ Mₛ} [AddCommGroup Mₛ] [Module R Mₛ] [CommRing Rₛ] [Algebra R Rₛ] [Mod
ule Rₛ Mₛ] [IsScalarTower R …
· 使用定理 `ModuleCat.instIsScalarTowerLocalizationCarrierLocalizedModule`：∀ {R : Ty
pe u} [inst : CommRing R] [inst_1 : Small.{v, u} R] (M : ModuleCat R) (S : Submo
noid R),   IsScalarTower R (Localization S) ↑(M.loc…
· 使用定理 `CategoryTheory.EnoughProjectives.presentation`：∀ {C : Type u} {inst : Ca
tegoryTheory.Category.{v, u} C} [self : CategoryTheory.EnoughProjectives C] (X :
 C),   Nonempty (CategoryTheory.Pro…
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `CategoryTheory.Limits.kernel.condition`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X 
Y : C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `CategoryTheory.ShortComplex.exact_kernel`：exact_kernel {X Y : C} (f : X 
⟶ Y) : (ShortComplex.mk (kernel.ι f) f (by simp)).Exact
· 使用定理 `CategoryTheory.Limits.equalizer.ι_mono`：∀ {C : Type u} {X Y : C} [inst :
 CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y}   [inst_1 : CategoryTheory.Limi
ts.HasEqualizer f g], Catego…
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `ModuleCat.instAdditiveLocalizationLocalizedModuleFunctor`：∀ {R : Type u}
 [inst : CommRing R] [inst_1 : Small.{v, u} R] (S : Submonoid R),   (ModuleCat.l
ocalizedModuleFunctor S).Additive
· 使用定理 `CategoryTheory.ShortComplex.ShortExact.map_of_exact`：∀ {C : Type u_1} {D
 : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryT
heory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `ModuleCat.instPreservesFiniteLimitsLocalizationLocalizedModuleFunctor`：∀
 {R : Type u} [inst : CommRing R] [inst_1 : Small.{v, u} R] (S : Submonoid R),  
 CategoryTheory.Limits.PreservesFiniteLimits (ModuleCat.loc…
· 使用定理 `ModuleCat.instPreservesFiniteColimitsLocalizationLocalizedModuleFunctor`
：∀ {R : Type u} [inst : CommRing R] [inst_1 : Small.{v, u} R] (S : Submonoid R),
   CategoryTheory.Limits.PreservesFiniteColimits (ModuleCat.l…
· 使用定理 `CategoryTheory.Functor.projective_obj`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, 
u₂} D]   (F : CategoryTheor…
· 使用定理 `ModuleCat.instPreservesProjectiveObjectsLocalizationLocalizedModuleFunct
or`：∀ {R : Type u} [inst : CommRing R] [inst_1 : Small.{v, u} R] (S : Submonoid 
R),   (ModuleCat.localizedModuleFunctor S).PreservesProjectiveOb…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `CategoryTheory.ShortComplex.ShortExact.hasProjectiveDimensionLT_X₃_iff`：
hasProjectiveDimensionLT_X₃_iff (n : Nat) (h₂ : Projective S.X₂) : HasProjective
DimensionLT S.X₃ (n + 2) ↔ HasProjectiveDimensionLT S.X₁ (n …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
lemma localizedModule_hasProjectiveDimensionLE [Small.{v, u} R] (n : ℕ) (S : Submonoid R)
    (M : ModuleCat.{v} R) [HasProjectiveDimensionLE M n] :
    HasProjectiveDimensionLE (M.localizedModule S) n := by
  have : Small.{v} (Localization S) := small_of_surjective Localization.mkHom_surjective
  induction n generalizing M with
  | zero =>
    have projle : HasProjectiveDimensionLE M 0 := ‹_›
    simp only [HasProjectiveDimensionLE, zero_add] at projle ⊢
    rw [← projective_iff_hasProjectiveDimensionLT_one, ← IsProjective.iff_projective] at projle ⊢
    exact Module.projective_of_isLocalizedModule S (M.localizedModuleMkLinearMap S)
  | succ n ih =>
    rcases ModuleCat.enoughProjectives.1 M with ⟨⟨P, f⟩⟩
    let T := ShortComplex.mk (kernel.ι f) f (kernel.condition f)
    have T_exact : T.ShortExact := { exact := ShortComplex.exact_kernel f }
    let TS := T.map (ModuleCat.localizedModuleFunctor S)
    have TS_exact : TS.ShortExact := T_exact.map_of_exact (ModuleCat.localizedModuleFunctor S)
    have : Projective TS.X₂ := (ModuleCat.localizedModuleFunctor.{v} S).projective_obj _
    have := (T_exact.hasProjectiveDimensionLT_X₃_iff n ‹_›).mp ‹_›
    exact (TS_exact.hasProjectiveDimensionLT_X₃_iff n ‹_›).mpr (ih (kernel f))
/-
**ModuleCat.projectiveDimension_le_projectiveDimension_of_isLocalizedModule** 是 
Mathlib 中的一个引理，位于命名空间 `ModuleCat`。
形式化陈述：projectiveDimension_le_projectiveDimension_of_isLocalizedModule [Small.{v,
 u} R] (S : Submonoid R) (M : ModuleCat.{v} R) : projectiveDimension (M.localize
dModule S) <= projectiveDimension M
参数：S : Submonoid R；M : ModuleCat.{v} R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `ModuleCat.localizedModule_hasProjectiveDimensionLE`：localizedModule_hasP
rojectiveDimensionLE [Small.{v, u} R] (n : Nat) (S : Submonoid R) (M : ModuleCat
.{v} R) [HasProjectiveDimensionLE M n] :…
· 使用定理 `le_of_forall_ge`：∀ {α : Type u_2} [inst : Preorder α] {a b : α}, (∀ (c :
 α), a ≤ c → b ≤ c) → b ≤ a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.subsingleton_congr`：subsingleton_congr (e : α ≃ β) : Subsingleton 
α ↔ Subsingleton β
· 使用定理 `LocalizedModule.instSubsingleton`：∀ {R : Type u_1} {M : Type u_2} [inst 
: CommRing R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Subsing
leton M] (S : Submonoi…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
lemma projectiveDimension_le_projectiveDimension_of_isLocalizedModule [Small.{v, u} R]
    (S : Submonoid R) (M : ModuleCat.{v} R) :
    projectiveDimension (M.localizedModule S) ≤ projectiveDimension M := by
  have aux (n : ℕ) : projectiveDimension M ≤ n → projectiveDimension (M.localizedModule S) ≤ n := by
    simp only [projectiveDimension_le_iff]
    intro h
    exact ModuleCat.localizedModule_hasProjectiveDimensionLE n S M
  refine le_of_forall_ge (fun N ↦ ?_)
  induction N with
  | bot =>
    simp only [le_bot_iff, projectiveDimension_eq_bot_iff, ModuleCat.isZero_iff_subsingleton,
      ModuleCat.localizedModule, ← Equiv.subsingleton_congr (equivShrink _)]
    intro _
    apply LocalizedModule.instSubsingleton _
  | coe N =>
    induction N with
    | top => simp
    | coe n => simpa using aux n
/-
**ModuleCat.hasProjectiveDimensionLE_iff_forall_maximalSpectrum** 是 Mathlib 中的一个
引理，位于命名空间 `ModuleCat`。
形式化陈述：hasProjectiveDimensionLE_iff_forall_maximalSpectrum (n : Nat) [Small.{v} R
] [IsNoetherianRing R] (M : ModuleCat.{v} R) [Module.Finite R M] : HasProjective
DimensionLE M n ↔ forall (m : MaximalSpectrum R), HasProjectiveDimensionLE (M.lo
calizedModule m.1.primeCompl) n
参数：n : Nat；M : ModuleCat.{v} R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `MaximalSpectrum.isMaximal`：∀ {R : Type u_1} [inst : CommSemiring R] (sel
f : MaximalSpectrum R), self.asIdeal.IsMaximal
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `small_of_surjective`：small_of_surjective {α : Type v} {β : Type w} [Smal
l.{u} α] {f : α -> β} (hf : Function.Surjective f) : Small.{u} β
· 使用引理 `Localization.mkHom_surjective`：mkHom_surjective : Surjective (mkHom (S
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsProjective.iff_projective`：IsProjective.iff_projective [Small.{v} R] (
P : Type v) [AddCommGroup P] [Module R P] : Module.Projective R P ↔ Projective (
of R P)
· 使用定理 `Module.projective_of_isLocalizedModule`：Module.projective_of_isLocalized
Module {Rₛ Mₛ} [AddCommGroup Mₛ] [Module R Mₛ] [CommRing Rₛ] [Algebra R Rₛ] [Mod
ule Rₛ Mₛ] [IsScalarTower R …
· 使用定理 `ModuleCat.instIsScalarTowerLocalizationCarrierLocalizedModule`：∀ {R : Ty
pe u} [inst : CommRing R] [inst_1 : Small.{v, u} R] (M : ModuleCat R) (S : Submo
noid R),   IsScalarTower R (Localization S) ↑(M.loc…
· 使用引理 `Module.finitePresentation_of_finite`：Module.finitePresentation_of_finite
 [IsNoetherianRing R] [h : Module.Finite R M] : Module.FinitePresentation R M
· 使用定理 `Module.projective_of_localization_maximal`：Module.projective_of_localiza
tion_maximal (H : forall (I : Ideal R) (_ : I.IsMaximal), Module.Projective (Loc
alization.AtPrime I) (Localized…
· 使用定理 `Module.Projective.of_equiv`：∀ {R : Type u_8} {S : Type u_9} [inst : Semi
ring R] [inst_1 : Semiring S] {M : Type u_10} {N : Type u_11}   [inst_2 : AddCom
mMonoid M] [inst…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `OreLocalization.instIsScalarTower_1`：∀ {R : Type u_1} {M : Type u_3} {X 
: Type u_4} [inst : Monoid M] {S : Submonoid M} [inst_1 : OreLocalization.OreSet
 S]   [inst_2 : MulAction…
· 使用定理 `Module.exists_finite_presentation`：Module.exists_finite_presentation [Sm
all.{v} R] (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] : exis
ts (P : Type v) (_ : Ad…
· 使用定理 `LinearMap.shortExact_shortComplexKer`：LinearMap.shortExact_shortComplexK
er {f : M ->ₗ[R] N} (h : Function.Surjective f) : f.shortComplexKer.ShortExact w
here exact
· 使用定理 `Module.Projective.of_free`：∀ {R : Type u_1} [inst : Semiring R] {P : Typ
e u_2} [inst_1 : AddCommMonoid P] [inst_2 : _root_.Module R P]   [Module.Free R 
P], Module.Proj…
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `ModuleCat.instAdditiveLocalizationLocalizedModuleFunctor`：∀ {R : Type u}
 [inst : CommRing R] [inst_1 : Small.{v, u} R] (S : Submonoid R),   (ModuleCat.l
ocalizedModuleFunctor S).Additive
· 使用定理 `CategoryTheory.ShortComplex.ShortExact.map_of_exact`：∀ {C : Type u_1} {D
 : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryT
heory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `ModuleCat.instPreservesFiniteLimitsLocalizationLocalizedModuleFunctor`：∀
 {R : Type u} [inst : CommRing R] [inst_1 : Small.{v, u} R] (S : Submonoid R),  
 CategoryTheory.Limits.PreservesFiniteLimits (ModuleCat.loc…
· 使用定理 `ModuleCat.instPreservesFiniteColimitsLocalizationLocalizedModuleFunctor`
：∀ {R : Type u} [inst : CommRing R] [inst_1 : Small.{v, u} R] (S : Submonoid R),
   CategoryTheory.Limits.PreservesFiniteColimits (ModuleCat.l…
· 使用定理 `CategoryTheory.Functor.projective_obj_of_projective`：∀ {C : Type u₁} [in
st : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.
Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `ModuleCat.instPreservesProjectiveObjectsLocalizationLocalizedModuleFunct
or`：∀ {R : Type u} [inst : CommRing R] [inst_1 : Small.{v, u} R] (S : Submonoid 
R),   (ModuleCat.localizedModuleFunctor S).PreservesProjectiveOb…
· 使用引理 `CategoryTheory.ShortComplex.ShortExact.hasProjectiveDimensionLT_X₃_iff`：
hasProjectiveDimensionLT_X₃_iff (n : Nat) (h₂ : Projective S.X₂) : HasProjective
DimensionLT S.X₃ (n + 2) ↔ HasProjectiveDimensionLT S.X₁ (n …
· 使用定理 `Module.IsNoetherian.finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semi
ring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [IsNoetherian 
R M], Module.Fin…
（共 32 条，此处仅展示前 30 条）
-/
lemma hasProjectiveDimensionLE_iff_forall_maximalSpectrum (n : ℕ) [Small.{v} R]
    [IsNoetherianRing R] (M : ModuleCat.{v} R) [Module.Finite R M] : HasProjectiveDimensionLE M n ↔
    ∀ (m : MaximalSpectrum R), HasProjectiveDimensionLE (M.localizedModule m.1.primeCompl) n := by
  induction n generalizing M with
  | zero =>
    simp only [HasProjectiveDimensionLE, zero_add, ← projective_iff_hasProjectiveDimensionLT_one]
    refine ⟨fun h p ↦ ?_, fun h ↦ ?_⟩
    · let : Small.{v} (Localization p.asIdeal.primeCompl) :=
        small_of_surjective Localization.mkHom_surjective
      rw [← IsProjective.iff_projective]
      exact Module.projective_of_isLocalizedModule p.1.primeCompl
        (M.localizedModuleMkLinearMap p.1.primeCompl)
    · rw [← IsProjective.iff_projective]
      have : Module.FinitePresentation R M := Module.finitePresentation_of_finite R M
      apply Module.projective_of_localization_maximal (fun p hp ↦ ?_)
      have : Module.Projective (Localization.AtPrime p) (M.localizedModule p.primeCompl) := by
        let : Small.{v} (Localization.AtPrime p) :=
          small_of_surjective Localization.mkHom_surjective
        simpa [IsProjective.iff_projective] using h ⟨p, hp⟩
      exact Module.Projective.of_equiv (LinearEquiv.extendScalarsOfIsLocalization p.primeCompl
        (Localization.AtPrime p) (IsLocalizedModule.linearEquiv p.primeCompl
        (M.localizedModuleMkLinearMap p.primeCompl)
        (LocalizedModule.mkLinearMap p.primeCompl M)))
  | succ n ih =>
    rcases Module.exists_finite_presentation R M with ⟨P, _, _, _, _, f, surjf⟩
    let S := f.shortComplexKer
    have S_exact := LinearMap.shortExact_shortComplexKer surjf
    have proj := ModuleCat.projective_of_categoryTheory_projective S.X₂
    let Sp (p : MaximalSpectrum R) := S.map (ModuleCat.localizedModuleFunctor p.1.primeCompl)
    have Sp_exact (p : MaximalSpectrum R) : (Sp p).ShortExact :=
      S_exact.map_of_exact (ModuleCat.localizedModuleFunctor p.asIdeal.primeCompl)
    specialize ih (ModuleCat.of R (LinearMap.ker f))
    have projp (p : MaximalSpectrum R) : Projective (Sp p).X₂ :=
      (ModuleCat.localizedModuleFunctor.{v} p.1.primeCompl).projective_obj_of_projective proj
    simp only [HasProjectiveDimensionLE] at ih ⊢
    rw [S_exact.hasProjectiveDimensionLT_X₃_iff n proj, ih]
    exact (forall_congr' (fun p ↦ (Sp_exact p).hasProjectiveDimensionLT_X₃_iff n (projp p))).symm
/-
**ModuleCat.hasProjectiveDimensionLE_iff_forall_primeSpectrum** 是 Mathlib 中的一个引理
，位于命名空间 `ModuleCat`。
形式化陈述：hasProjectiveDimensionLE_iff_forall_primeSpectrum (n : Nat) [Small.{v} R] 
[IsNoetherianRing R] (M : ModuleCat.{v} R) [Module.Finite R M] : HasProjectiveDi
mensionLE M n ↔ forall (p : PrimeSpectrum R), HasProjectiveDimensionLE (M.locali
zedModule p.1.primeCompl) n
参数：n : Nat；M : ModuleCat.{v} R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用引理 `ModuleCat.localizedModule_hasProjectiveDimensionLE`：localizedModule_hasP
rojectiveDimensionLE [Small.{v, u} R] (n : Nat) (S : Submonoid R) (M : ModuleCat
.{v} R) [HasProjectiveDimensionLE M n] :…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `MaximalSpectrum.isMaximal`：∀ {R : Type u_1} [inst : CommSemiring R] (sel
f : MaximalSpectrum R), self.asIdeal.IsMaximal
· 使用引理 `ModuleCat.hasProjectiveDimensionLE_iff_forall_maximalSpectrum`：hasProjec
tiveDimensionLE_iff_forall_maximalSpectrum (n : Nat) [Small.{v} R] [IsNoetherian
Ring R] (M : ModuleCat.{v} R) [Module.Finite R M] :…
-/
lemma hasProjectiveDimensionLE_iff_forall_primeSpectrum (n : ℕ) [Small.{v} R]
    [IsNoetherianRing R] (M : ModuleCat.{v} R) [Module.Finite R M] : HasProjectiveDimensionLE M n ↔
    ∀ (p : PrimeSpectrum R), HasProjectiveDimensionLE (M.localizedModule p.1.primeCompl) n :=
  ⟨fun _ p ↦ M.localizedModule_hasProjectiveDimensionLE n p.1.primeCompl,
    fun h ↦ (M.hasProjectiveDimensionLE_iff_forall_maximalSpectrum n).mpr
    fun m ↦ h ⟨m.1, Ideal.IsMaximal.isPrime' m.1⟩⟩
/-
**ModuleCat.projectiveDimension_eq_iSup_localizedModule_prime** 是 Mathlib 中的一个引理
，位于命名空间 `ModuleCat`。
形式化陈述：projectiveDimension_eq_iSup_localizedModule_prime [Small.{v} R] [IsNoether
ianRing R] (M : ModuleCat.{v} R) [Module.Finite R M] : projectiveDimension M = ⨆
 (p : PrimeSpectrum R), projectiveDimension (M.localizedModule p.1.primeCompl)
参数：M : ModuleCat.{v} R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用引理 `ModuleCat.hasProjectiveDimensionLE_iff_forall_primeSpectrum`：hasProjecti
veDimensionLE_iff_forall_primeSpectrum (n : Nat) [Small.{v} R] [IsNoetherianRing
 R] (M : ModuleCat.{v} R) [Module.Finite R M] : H…
· 使用定理 `eq_of_forall_ge_iff`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α},
 (∀ (c : α), a ≤ c ↔ b ≤ c) → a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.subsingleton_congr`：subsingleton_congr (e : α ≃ β) : Subsingleton 
α ↔ Subsingleton β
· 使用定理 `LocalizedModule.instSubsingleton`：∀ {R : Type u_1} {M : Type u_2} [inst 
: CommRing R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Subsing
leton M] (S : Submonoi…
· 使用定理 `Module.subsingleton_of_localization_maximal`：Module.subsingleton_of_loca
lization_maximal (h : forall (P : Ideal R) [P.IsMaximal], Subsingleton (Mₚ P)) :
 Subsingleton M
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.IsMaximal.isPrime`：∀ {α : Type u} [inst : CommSemiring α] {I : Ide
al α}, I.IsMaximal → I.IsPrime
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma projectiveDimension_eq_iSup_localizedModule_prime [Small.{v} R]
    [IsNoetherianRing R] (M : ModuleCat.{v} R) [Module.Finite R M] : projectiveDimension M =
    ⨆ (p : PrimeSpectrum R), projectiveDimension (M.localizedModule p.1.primeCompl) := by
  have aux (n : ℕ) : projectiveDimension M ≤ n ↔ ⨆ (p : PrimeSpectrum R), projectiveDimension
    (M.localizedModule p.1.primeCompl) ≤ n := by
    simp only [projectiveDimension_le_iff, iSup_le_iff]
    exact M.hasProjectiveDimensionLE_iff_forall_primeSpectrum n
  refine eq_of_forall_ge_iff (fun N ↦ ?_)
  induction N with
  | bot =>
    simp only [le_bot_iff, projectiveDimension_eq_bot_iff, ModuleCat.isZero_iff_subsingleton,
      iSup_eq_bot, ModuleCat.localizedModule, ← Equiv.subsingleton_congr (equivShrink _)]
    refine ⟨fun h p ↦ LocalizedModule.instSubsingleton _, fun h ↦ ?_⟩
    apply Module.subsingleton_of_localization_maximal (R := R)
      (fun p ↦ LocalizedModule p.primeCompl M) (fun p ↦ LocalizedModule.mkLinearMap p.primeCompl M)
    intro p hp
    exact h ⟨p, hp.isPrime⟩
  | coe N =>
    induction N with
    | top => simp
    | coe n => simpa using aux n
/-
**ModuleCat.projectiveDimension_eq_iSup_localizedModule_maximal** 是 Mathlib 中的一个
引理，位于命名空间 `ModuleCat`。
形式化陈述：projectiveDimension_eq_iSup_localizedModule_maximal [Small.{v} R] [IsNoeth
erianRing R] (M : ModuleCat.{v} R) [Module.Finite R M] : projectiveDimension M =
 ⨆ (p : MaximalSpectrum R), projectiveDimension (M.localizedModule p.1.primeComp
l)
参数：M : ModuleCat.{v} R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `MaximalSpectrum.isMaximal`：∀ {R : Type u_1} [inst : CommSemiring R] (sel
f : MaximalSpectrum R), self.asIdeal.IsMaximal
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用引理 `ModuleCat.hasProjectiveDimensionLE_iff_forall_maximalSpectrum`：hasProjec
tiveDimensionLE_iff_forall_maximalSpectrum (n : Nat) [Small.{v} R] [IsNoetherian
Ring R] (M : ModuleCat.{v} R) [Module.Finite R M] :…
· 使用定理 `eq_of_forall_ge_iff`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α},
 (∀ (c : α), a ≤ c ↔ b ≤ c) → a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.subsingleton_congr`：subsingleton_congr (e : α ≃ β) : Subsingleton 
α ↔ Subsingleton β
· 使用定理 `LocalizedModule.instSubsingleton`：∀ {R : Type u_1} {M : Type u_2} [inst 
: CommRing R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Subsing
leton M] (S : Submonoi…
· 使用定理 `Module.subsingleton_of_localization_maximal`：Module.subsingleton_of_loca
lization_maximal (h : forall (P : Ideal R) [P.IsMaximal], Subsingleton (Mₚ P)) :
 Subsingleton M
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma projectiveDimension_eq_iSup_localizedModule_maximal [Small.{v} R]
    [IsNoetherianRing R] (M : ModuleCat.{v} R) [Module.Finite R M] : projectiveDimension M =
    ⨆ (p : MaximalSpectrum R), projectiveDimension (M.localizedModule p.1.primeCompl) := by
  have aux (n : ℕ) : projectiveDimension M ≤ n ↔ ⨆ (p : MaximalSpectrum R), projectiveDimension
    (M.localizedModule p.1.primeCompl) ≤ n := by
    simp only [projectiveDimension_le_iff, iSup_le_iff]
    exact M.hasProjectiveDimensionLE_iff_forall_maximalSpectrum n
  refine eq_of_forall_ge_iff (fun N ↦ ?_)
  induction N with
  | bot =>
    simp only [le_bot_iff, projectiveDimension_eq_bot_iff, ModuleCat.isZero_iff_subsingleton,
      iSup_eq_bot, ModuleCat.localizedModule, ← Equiv.subsingleton_congr (equivShrink _)]
    refine ⟨fun h p ↦ LocalizedModule.instSubsingleton _, fun h ↦ ?_⟩
    apply Module.subsingleton_of_localization_maximal (R := R)
      (fun p ↦ LocalizedModule p.primeCompl M) (fun p ↦ LocalizedModule.mkLinearMap p.primeCompl M)
    intro p hp
    exact h ⟨p, hp⟩
  | coe N =>
    induction N with
    | top => simp
    | coe n => simpa using aux n

end ModuleCat

