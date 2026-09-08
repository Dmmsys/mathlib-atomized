/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
public import Mathlib.Algebra.Category.ModuleCat.Localization
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Module.LocalizedModule.Exact
public import Mathlib.CategoryTheory.Abelian.Injective.Dimension
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.RingTheory.LocalProperties.Injective

/-!

# Relation of Injective Dimension with Localizations

-/

public section

universe v u

namespace ModuleCat

variable {R : Type u} [CommRing R]

open CategoryTheory Limits

set_option backward.isDefEq.respectTransparency false in
/-
**ModuleCat.** 是 Mathlib 中的一个实例，位于命名空间 `ModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Small.{v} R] [IsNoetherianRing R] (S : Submonoid R) :
    (ModuleCat.localizedModuleFunctor.{v} S).PreservesInjectiveObjects where
  injective_obj X {inj} := by
    let _ : Small.{v, u} (Localization S) := small_of_surjective Localization.mkHom_surjective
    rw [← Module.injective_iff_injective_object] at inj ⊢
    simpa [ModuleCat.localizedModuleFunctor] using
      Module.injective_of_isLocalizedModule S (X.localizedModuleMkLinearMap S)
/-
**ModuleCat.localizedModule_hasInjectiveDimensionLE** 是 Mathlib 中的一个引理，位于命名空间 `M
oduleCat`。
形式化陈述：localizedModule_hasInjectiveDimensionLE [Small.{v, u} R] [IsNoetherianRing
 R] (n : Nat) (S : Submonoid R) (M : ModuleCat.{v} R) [HasInjectiveDimensionLE M
 n] : HasInjectiveDimensionLE (M.localizedModule S) n
参数：n : Nat；S : Submonoid R；M : ModuleCat.{v} R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `small_of_surjective`：small_of_surjective {α : Type v} {β : Type w} [Smal
l.{u} α] {f : α -> β} (hf : Function.Surjective f) : Small.{u} β
· 使用引理 `Localization.mkHom_surjective`：mkHom_surjective : Surjective (mkHom (S
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.injective_iff_injective_object`：injective_iff_injective_object : 
Module.Injective R M ↔ CategoryTheory.Injective (ModuleCat.of R M)
· 使用定理 `Module.injective_of_isLocalizedModule`：Module.injective_of_isLocalizedMo
dule [Small.{v} R] [IsNoetherianRing R] {Rₛ : Type u'} [Small.{v'} Rₛ] [CommRing
 Rₛ] [Algebra R Rₛ] {Mₛ : T…
· 使用定理 `ModuleCat.instIsScalarTowerLocalizationCarrierLocalizedModule`：∀ {R : Ty
pe u} [inst : CommRing R] [inst_1 : Small.{v, u} R] (M : ModuleCat R) (S : Submo
noid R),   IsScalarTower R (Localization S) ↑(M.loc…
· 使用定理 `instEnoughInjectivesModuleCatOfSmall`：∀ (R : Type u) [inst : Ring R] [Sm
all.{v, u} R], CategoryTheory.EnoughInjectives (ModuleCat R)
· 使用定理 `CategoryTheory.EnoughInjectives.presentation`：∀ {C : Type u₁} {inst : Ca
tegoryTheory.Category.{v₁, u₁} C} [self : CategoryTheory.EnoughInjectives C] (X 
: C),   Nonempty (CategoryTheory.I…
· 使用定理 `ModuleCat.HasColimit.instHasColimit`：∀ {R : Type w} [inst : Ring R] {J :
 Type u} [inst_1 : CategoryTheory.Category.{v, u} J]   (F : CategoryTheory.Funct
or J (ModuleCat R))   [Ca…
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `CategoryTheory.Limits.cokernel.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {
X Y : C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `CategoryTheory.ShortComplex.exact_cokernel`：exact_cokernel {X Y : C} (f 
: X ⟶ Y) : (ShortComplex.mk f (cokernel.π f) (by simp)).Exact
· 使用定理 `CategoryTheory.Limits.coequalizer.π_epi`：∀ {C : Type u} {X Y : C} [inst 
: CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y}   [inst_1 : CategoryTheory.Lim
its.HasCoequalizer f g], Cate…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exac
t`：∀ {R : Type u} [inst : Ring R] (S : CategoryTheory.ShortComplex (ModuleCat R)
),   S.Exact ↔ Function.Exact ⇑(CategoryTheory.ConcreteCategory…
· 使用定理 `CategoryTheory.ShortComplex.ShortExact.exact`：∀ {C : Type u_1} [inst : C
ategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorp
hisms C]   {S : CategoryTheory.Sho…
· 使用定理 `IsLocalizedModule.map_exact`：IsLocalizedModule.map_exact (g : M₀ ->ₗ[R] 
M₁) (h : M₁ ->ₗ[R] M₂) (ex : Function.Exact g h) : Function.Exact (map S f₀ f₁ g
) (map S f₁ f₂ h)
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
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `CategoryTheory.ShortComplex.ShortExact.hasInjectiveDimensionLT_X₃_iff`：h
asInjectiveDimensionLT_X₃_iff (n : Nat) (h₂ : Injective S.X₂) : HasInjectiveDime
nsionLT S.X₃ (n + 1) ↔ HasInjectiveDimensionLT S.X₁ (n + 2)
· 使用定理 `CategoryTheory.Functor.injective_obj`：∀ {C : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u
₂} D]   (F : CategoryTheor…
· 使用定理 `ModuleCat.instPreservesInjectiveObjectsLocalizationLocalizedModuleFuncto
rOfIsNoetherianRing`：∀ {R : Type u} [inst : CommRing R] [inst_1 : Small.{v, u} R
] [IsNoetherianRing R] (S : Submonoid R),   (ModuleCat.localizedModuleFunctor S)
.…
-/
lemma localizedModule_hasInjectiveDimensionLE [Small.{v, u} R] [IsNoetherianRing R] (n : ℕ)
    (S : Submonoid R) (M : ModuleCat.{v} R) [HasInjectiveDimensionLE M n] :
    HasInjectiveDimensionLE (M.localizedModule S) n := by
  have : Small.{v} (Localization S) := small_of_surjective Localization.mkHom_surjective
  induction n generalizing M with
  | zero =>
    have injle : HasInjectiveDimensionLE M 0 := ‹_›
    simp only [HasInjectiveDimensionLE, zero_add, ← injective_iff_hasInjectiveDimensionLT_one]
      at injle ⊢
    rw [← Module.injective_iff_injective_object] at injle ⊢
    exact Module.injective_of_isLocalizedModule S (M.localizedModuleMkLinearMap S)
  | succ n ih =>
    have ei : EnoughInjectives (ModuleCat.{v} R) := inferInstance
    rcases ei.1 M with ⟨I, inj, f, monof⟩
    let T := ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
    have T_exact : T.ShortExact := { exact := ShortComplex.exact_cokernel f }
    have T_exact' : Function.Exact (ConcreteCategory.hom T.f) (ConcreteCategory.hom T.g) :=
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp T_exact.1
    have TS_exact' := IsLocalizedModule.map_exact S (T.X₁.localizedModuleMkLinearMap S)
      (T.X₂.localizedModuleMkLinearMap S) (T.X₃.localizedModuleMkLinearMap S) _ _ T_exact'
    let TS := T.map (ModuleCat.localizedModuleFunctor S)
    have TS_exact : TS.ShortExact := T_exact.map_of_exact (ModuleCat.localizedModuleFunctor S)
    let _ := (T_exact.hasInjectiveDimensionLT_X₃_iff n ‹_›).mpr ‹_›
    let _ : Injective TS.X₂ := (ModuleCat.localizedModuleFunctor.{v} S).injective_obj _
    exact (TS_exact.hasInjectiveDimensionLT_X₃_iff n ‹_›).mp (ih T.X₃)

open Limits in
/-
**ModuleCat.injectiveDimension_le_injectiveDimension_of_isLocalizedModule** 是 Ma
thlib 中的一个引理，位于命名空间 `ModuleCat`。
形式化陈述：injectiveDimension_le_injectiveDimension_of_isLocalizedModule [Small.{v, u
} R] [IsNoetherianRing R] (S : Submonoid R) (M : ModuleCat.{v} R) : injectiveDim
ension (M.localizedModule S) <= injectiveDimension M
参数：S : Submonoid R；M : ModuleCat.{v} R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `ModuleCat.localizedModule_hasInjectiveDimensionLE`：localizedModule_hasIn
jectiveDimensionLE [Small.{v, u} R] [IsNoetherianRing R] (n : Nat) (S : Submonoi
d R) (M : ModuleCat.{v} R) [HasInjectiv…
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
lemma injectiveDimension_le_injectiveDimension_of_isLocalizedModule [Small.{v, u} R]
    [IsNoetherianRing R] (S : Submonoid R) (M : ModuleCat.{v} R) :
    injectiveDimension (M.localizedModule S) ≤ injectiveDimension M := by
  have aux (n : ℕ) : injectiveDimension M ≤ n → injectiveDimension (M.localizedModule S) ≤ n := by
    simp only [injectiveDimension_le_iff]
    intro h
    exact M.localizedModule_hasInjectiveDimensionLE n S
  refine le_of_forall_ge (fun N ↦ ?_)
  induction N with
  | bot =>
    simp only [le_bot_iff, injectiveDimension_eq_bot_iff, ModuleCat.isZero_iff_subsingleton,
      ModuleCat.localizedModule, ← Equiv.subsingleton_congr (equivShrink _)]
    intro _
    apply LocalizedModule.instSubsingleton _
  | coe N =>
    induction N with
    | top => simp
    | coe n => simpa using aux n
/-
**ModuleCat.hasInjectiveDimensionLE_iff_forall_maximalSpectrum** 是 Mathlib 中的一个引
理，位于命名空间 `ModuleCat`。
形式化陈述：hasInjectiveDimensionLE_iff_forall_maximalSpectrum [Small.{v, u} R] [IsNoe
therianRing R] (n : Nat) (M : ModuleCat.{v} R) : HasInjectiveDimensionLE M n ↔ f
orall (m : MaximalSpectrum R), HasInjectiveDimensionLE (M.localizedModule m.1.pr
imeCompl) n
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
· 使用定理 `Module.injective_module_of_injective_object`：injective_module_of_injecti
ve_object [inj : CategoryTheory.Injective <| ModuleCat.of R M] : Module.Injectiv
e R M where out X Y _ _ _ _ f hf …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.injective_iff_injective_object`：injective_iff_injective_object : 
Module.Injective R M ↔ CategoryTheory.Injective (ModuleCat.of R M)
· 使用定理 `Module.injective_of_isLocalizedModule`：Module.injective_of_isLocalizedMo
dule [Small.{v} R] [IsNoetherianRing R] {Rₛ : Type u'} [Small.{v'} Rₛ] [CommRing
 Rₛ] [Algebra R Rₛ] {Mₛ : T…
· 使用定理 `ModuleCat.instIsScalarTowerLocalizationCarrierLocalizedModule`：∀ {R : Ty
pe u} [inst : CommRing R] [inst_1 : Small.{v, u} R] (M : ModuleCat R) (S : Submo
noid R),   IsScalarTower R (Localization S) ↑(M.loc…
· 使用定理 `Module.injective_of_localization_maximal`：Module.injective_of_localizati
on_maximal [Small.{v} R] [IsNoetherianRing R] (H : forall (I : Ideal R) (_ : I.I
sMaximal), Module.Injective (L…
· 使用定理 `Module.Baer.iff_injective`：∀ {R : Type u} [inst : Ring R] {Q : Type v} [
inst_1 : AddCommGroup Q] [inst_2 : _root_.Module R Q] [Small.{v, u} R],   Module
.Baer R Q ↔ Mod…
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用引理 `Module.Baer.of_equiv`：of_equiv (e : Q ≃ₗ[R] M) (h : Module.Baer R Q) : M
odule.Baer R M
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `OreLocalization.instIsScalarTower_1`：∀ {R : Type u_1} {M : Type u_3} {X 
: Type u_4} [inst : Monoid M] {S : Submonoid M} [inst_1 : OreLocalization.OreSet
 S]   [inst_2 : MulAction…
· 使用定理 `instEnoughInjectivesModuleCatOfSmall`：∀ (R : Type u) [inst : Ring R] [Sm
all.{v, u} R], CategoryTheory.EnoughInjectives (ModuleCat R)
· 使用定理 `CategoryTheory.EnoughInjectives.presentation`：∀ {C : Type u₁} {inst : Ca
tegoryTheory.Category.{v₁, u₁} C} [self : CategoryTheory.EnoughInjectives C] (X 
: C),   Nonempty (CategoryTheory.I…
· 使用定理 `ModuleCat.HasColimit.instHasColimit`：∀ {R : Type w} [inst : Ring R] {J :
 Type u} [inst_1 : CategoryTheory.Category.{v, u} J]   (F : CategoryTheory.Funct
or J (ModuleCat R))   [Ca…
· 使用定理 `CategoryTheory.Limits.cokernel.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {
X Y : C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `CategoryTheory.ShortComplex.exact_cokernel`：exact_cokernel {X Y : C} (f 
: X ⟶ Y) : (ShortComplex.mk f (cokernel.π f) (by simp)).Exact
· 使用定理 `CategoryTheory.Limits.coequalizer.π_epi`：∀ {C : Type u} {X Y : C} [inst 
: CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y}   [inst_1 : CategoryTheory.Lim
its.HasCoequalizer f g], Cate…
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
（共 35 条，此处仅展示前 30 条）
-/
lemma hasInjectiveDimensionLE_iff_forall_maximalSpectrum [Small.{v, u} R] [IsNoetherianRing R]
    (n : ℕ) (M : ModuleCat.{v} R) : HasInjectiveDimensionLE M n ↔
    ∀ (m : MaximalSpectrum R), HasInjectiveDimensionLE (M.localizedModule m.1.primeCompl) n := by
  induction n generalizing M with
  | zero =>
    simp only [HasInjectiveDimensionLE, zero_add, ← injective_iff_hasInjectiveDimensionLT_one]
    refine ⟨fun h m ↦ ?_, fun h ↦ ?_⟩
    · let _ : Small.{v} (Localization m.1.primeCompl) :=
        small_of_surjective Localization.mkHom_surjective
      let _ : Module.Injective R M := Module.injective_module_of_injective_object R M
      rw [← Module.injective_iff_injective_object]
      exact Module.injective_of_isLocalizedModule m.1.primeCompl
        (M.localizedModuleMkLinearMap m.1.primeCompl)
    · rw [← Module.injective_iff_injective_object]
      apply Module.injective_of_localization_maximal (fun p hp ↦ ?_)
      let : Small.{v} (Localization.AtPrime p) := small_of_surjective Localization.mkHom_surjective
      have : Module.Injective (Localization.AtPrime p) (M.localizedModule p.primeCompl) := by
        simpa [Module.injective_iff_injective_object] using h ⟨p, hp⟩
      rw [← Module.Baer.iff_injective] at this ⊢
      exact Module.Baer.of_equiv (LinearEquiv.extendScalarsOfIsLocalization p.primeCompl
        (Localization.AtPrime p) (IsLocalizedModule.linearEquiv p.primeCompl
        (M.localizedModuleMkLinearMap p.primeCompl)
        (LocalizedModule.mkLinearMap p.primeCompl M))) this
  | succ n ih =>
    have ei : EnoughInjectives (ModuleCat.{v} R) := inferInstance
    rcases ei.1 M with ⟨I, inj, f, monof⟩
    let S := ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
    have S_exact : S.ShortExact := { exact := ShortComplex.exact_cokernel f }
    let Sp (m : MaximalSpectrum R) := S.map (ModuleCat.localizedModuleFunctor m.1.primeCompl)
    have Sp_exact (m : MaximalSpectrum R) : (Sp m).ShortExact :=
      S_exact.map_of_exact (ModuleCat.localizedModuleFunctor m.1.primeCompl)
    have ih' := ih S.X₃
    simp only [HasInjectiveDimensionLE] at ih' ⊢
    rw [← S_exact.hasInjectiveDimensionLT_X₃_iff n inj, ih']
    have injp (m : MaximalSpectrum R) : Injective (Sp m).X₂ :=
      (ModuleCat.localizedModuleFunctor.{v} m.1.primeCompl).injective_obj _
    exact (forall_congr' (fun p ↦ (Sp_exact p).hasInjectiveDimensionLT_X₃_iff n (injp p)))
/-
**ModuleCat.hasInjectiveDimensionLE_iff_forall_primeSpectrum** 是 Mathlib 中的一个引理，
位于命名空间 `ModuleCat`。
形式化陈述：hasInjectiveDimensionLE_iff_forall_primeSpectrum [Small.{v, u} R] [IsNoeth
erianRing R] (n : Nat) (M : ModuleCat.{v} R) : HasInjectiveDimensionLE M n ↔ for
all (p : PrimeSpectrum R), HasInjectiveDimensionLE (M.localizedModule p.1.primeC
ompl) n
参数：n : Nat；M : ModuleCat.{v} R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用引理 `ModuleCat.localizedModule_hasInjectiveDimensionLE`：localizedModule_hasIn
jectiveDimensionLE [Small.{v, u} R] [IsNoetherianRing R] (n : Nat) (S : Submonoi
d R) (M : ModuleCat.{v} R) [HasInjectiv…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `MaximalSpectrum.isMaximal`：∀ {R : Type u_1} [inst : CommSemiring R] (sel
f : MaximalSpectrum R), self.asIdeal.IsMaximal
· 使用引理 `ModuleCat.hasInjectiveDimensionLE_iff_forall_maximalSpectrum`：hasInjecti
veDimensionLE_iff_forall_maximalSpectrum [Small.{v, u} R] [IsNoetherianRing R] (
n : Nat) (M : ModuleCat.{v} R) : HasInjectiveDimen…
-/
lemma hasInjectiveDimensionLE_iff_forall_primeSpectrum [Small.{v, u} R] [IsNoetherianRing R]
    (n : ℕ) (M : ModuleCat.{v} R) : HasInjectiveDimensionLE M n ↔
    ∀ (p : PrimeSpectrum R), HasInjectiveDimensionLE (M.localizedModule p.1.primeCompl) n :=
  ⟨fun _ p ↦ M.localizedModule_hasInjectiveDimensionLE n p.1.primeCompl,
    fun h ↦ (M.hasInjectiveDimensionLE_iff_forall_maximalSpectrum n).mpr
    fun m ↦ h ⟨m.1, Ideal.IsMaximal.isPrime' m.1⟩⟩
/-
**ModuleCat.injectiveDimension_eq_iSup_localizedModule_prime** 是 Mathlib 中的一个引理，
位于命名空间 `ModuleCat`。
形式化陈述：injectiveDimension_eq_iSup_localizedModule_prime [Small.{v, u} R] [IsNoeth
erianRing R] (M : ModuleCat.{v} R) : injectiveDimension M = ⨆ (p : PrimeSpectrum
 R), injectiveDimension (M.localizedModule p.1.primeCompl)
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
· 使用引理 `ModuleCat.hasInjectiveDimensionLE_iff_forall_primeSpectrum`：hasInjective
DimensionLE_iff_forall_primeSpectrum [Small.{v, u} R] [IsNoetherianRing R] (n : 
Nat) (M : ModuleCat.{v} R) : HasInjectiveDimensi…
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
lemma injectiveDimension_eq_iSup_localizedModule_prime [Small.{v, u} R] [IsNoetherianRing R]
    (M : ModuleCat.{v} R) : injectiveDimension M =
    ⨆ (p : PrimeSpectrum R), injectiveDimension (M.localizedModule p.1.primeCompl) := by
  have aux (n : ℕ) : injectiveDimension M ≤ n ↔ ⨆ (p : PrimeSpectrum R), injectiveDimension
    (M.localizedModule p.1.primeCompl) ≤ n := by
    simp only [injectiveDimension_le_iff, iSup_le_iff]
    exact M.hasInjectiveDimensionLE_iff_forall_primeSpectrum n
  refine eq_of_forall_ge_iff (fun N ↦ ?_)
  induction N with
  | bot =>
    simp only [le_bot_iff, injectiveDimension_eq_bot_iff, ModuleCat.isZero_iff_subsingleton,
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
**ModuleCat.injectiveDimension_eq_iSup_localizedModule_maximal** 是 Mathlib 中的一个引
理，位于命名空间 `ModuleCat`。
形式化陈述：injectiveDimension_eq_iSup_localizedModule_maximal [Small.{v, u} R] [IsNoe
therianRing R] (M : ModuleCat.{v} R) : injectiveDimension M = ⨆ (p : MaximalSpec
trum R), injectiveDimension (M.localizedModule p.1.primeCompl)
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
· 使用引理 `ModuleCat.hasInjectiveDimensionLE_iff_forall_maximalSpectrum`：hasInjecti
veDimensionLE_iff_forall_maximalSpectrum [Small.{v, u} R] [IsNoetherianRing R] (
n : Nat) (M : ModuleCat.{v} R) : HasInjectiveDimen…
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
lemma injectiveDimension_eq_iSup_localizedModule_maximal [Small.{v, u} R] [IsNoetherianRing R]
    (M : ModuleCat.{v} R) : injectiveDimension M =
    ⨆ (p : MaximalSpectrum R), injectiveDimension (M.localizedModule p.1.primeCompl) := by
  have aux (n : ℕ) : injectiveDimension M ≤ n ↔ ⨆ (m : MaximalSpectrum R), injectiveDimension
    (M.localizedModule m.1.primeCompl) ≤ n := by
    simp only [injectiveDimension_le_iff, iSup_le_iff]
    exact M.hasInjectiveDimensionLE_iff_forall_maximalSpectrum n
  refine eq_of_forall_ge_iff (fun N ↦ ?_)
  induction N with
  | bot =>
    simp only [le_bot_iff, injectiveDimension_eq_bot_iff, ModuleCat.isZero_iff_subsingleton,
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

