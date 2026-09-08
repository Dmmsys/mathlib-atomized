/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!
# Ring-theoretic results in terms of categorical language
-/

public section

universe u

open CategoryTheory

/-
**localization_unit_isIso** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：localization_unit_isIso (R : CommRingCat) : IsIso (CommRingCat.ofHom <| al
gebraMap R (Localization.Away (1 : R)))
参数：R : CommRingCat。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
-/
instance localization_unit_isIso (R : CommRingCat) :
    IsIso (CommRingCat.ofHom <| algebraMap R (Localization.Away (1 : R))) :=
  Iso.isIso_hom (IsLocalization.atOne R (Localization.Away (1 : R))).toRingEquiv.toCommRingCatIso
/-
**localization_unit_isIso'** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：localization_unit_isIso' (R : CommRingCat) : @IsIso CommRingCat _ R _ (Com
mRingCat.ofHom <| algebraMap R (Localization.Away (1 : R)))
参数：R : CommRingCat。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
instance localization_unit_isIso' (R : CommRingCat) :
    @IsIso CommRingCat _ R _ (CommRingCat.ofHom <| algebraMap R (Localization.Away (1 : R))) := by
  cases R
  exact localization_unit_isIso _
/-
**IsLocalization.epi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLocalization.epi {R : Type*} [CommRing R] (M : Submonoid R) (S : Type _)
 [CommRing S] [Algebra R S] [IsLocalization M S] : Epi (CommRingCat.ofHom <| alg
ebraMap R S)
参数：M : Submonoid R；S : Type _。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CommRingCat.hom_ext`：hom_ext {R S : CommRingCat} {f g : R ⟶ S} (hf : f.h
om = g.hom) : f = g
· 使用定理 `IsLocalization.ringHom_ext`：ringHom_ext {P : Type*} [Semiring P] ⦃j k : 
S ->+* P⦄ (h : j.comp (algebraMap R S) = k.comp (algebraMap R S)) : j = k
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem IsLocalization.epi {R : Type*} [CommRing R] (M : Submonoid R) (S : Type _) [CommRing S]
    [Algebra R S] [IsLocalization M S] : Epi (CommRingCat.ofHom <| algebraMap R S) :=
  ⟨fun _ _ h => CommRingCat.hom_ext <| ringHom_ext M congr(($h).hom)⟩
/-
**Localization.epi** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Localization.epi {R : Type*} [CommRing R] (M : Submonoid R) : Epi (CommRin
gCat.ofHom <| algebraMap R <| Localization M)
参数：M : Submonoid R。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalization.epi`：IsLocalization.epi {R : Type*} [CommRing R] (M : Sub
monoid R) (S : Type _) [CommRing S] [Algebra R S] [IsLocalization M S] : Epi (Co
mmRingCa…
-/
instance Localization.epi {R : Type*} [CommRing R] (M : Submonoid R) :
    Epi (CommRingCat.ofHom <| algebraMap R <| Localization M) :=
  IsLocalization.epi M _
/-
**Localization.epi'** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Localization.epi' {R : CommRingCat} (M : Submonoid R) : @Epi CommRingCat _
 R _ (CommRingCat.ofHom <| algebraMap R <| Localization M :)
参数：M : Submonoid R。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalization.epi`：IsLocalization.epi {R : Type*} [CommRing R] (M : Sub
monoid R) (S : Type _) [CommRing S] [Algebra R S] [IsLocalization M S] : Epi (Co
mmRingCa…
-/
instance Localization.epi' {R : CommRingCat} (M : Submonoid R) :
    @Epi CommRingCat _ R _ (CommRingCat.ofHom <| algebraMap R <| Localization M :) := by
  rcases R with ⟨α, str⟩
  exact IsLocalization.epi M _

@[instance]
/-
**CommRingCat.isLocalHom_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CommRingCat.isLocalHom_comp {R S T : CommRingCat} (f : R ⟶ S) (g : S ⟶ T) 
[IsLocalHom g.hom] [IsLocalHom f.hom] : IsLocalHom (f ≫ g).hom
参数：f : R ⟶ S；g : S ⟶ T。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.isLocalHom_comp`：RingHom.isLocalHom_comp (g : S ->+* T) (f : R -
>+* S) [IsLocalHom g] [IsLocalHom f] : IsLocalHom (g.comp f) where map_nonunit a
-/
theorem CommRingCat.isLocalHom_comp {R S T : CommRingCat} (f : R ⟶ S) (g : S ⟶ T)
    [IsLocalHom g.hom] [IsLocalHom f.hom] : IsLocalHom (f ≫ g).hom :=
  RingHom.isLocalHom_comp _ _
/-
**isLocalHom_of_iso** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLocalHom_of_iso {R S : CommRingCat} (f : R ≅ S) : IsLocalHom f.hom.hom
参数：f : R ≅ S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.hom_inv_id_apply`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {F : C → C → Type uF}   {carrier 
: C → Type w} {instFunLik…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `RingHom.isUnit_map`：isUnit_map (f : α ->+* β) {a : α} : IsUnit a -> IsUn
it (f a)
-/
theorem isLocalHom_of_iso {R S : CommRingCat} (f : R ≅ S) : IsLocalHom f.hom.hom :=
  { map_nonunit := fun a ha => by
      convert! f.inv.hom.isUnit_map ha
      simp }

-- see Note [lower instance priority]
@[instance 100]
/-
**isLocalHom_of_isIso** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLocalHom_of_isIso {R S : CommRingCat} (f : R ⟶ S) [IsIso f] : IsLocalHom
 f.hom
参数：f : R ⟶ S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isLocalHom_of_iso`：isLocalHom_of_iso {R S : CommRingCat} (f : R ≅ S) : I
sLocalHom f.hom.hom
-/
theorem isLocalHom_of_isIso {R S : CommRingCat} (f : R ⟶ S) [IsIso f] :
    IsLocalHom f.hom :=
  isLocalHom_of_iso (asIso f)
