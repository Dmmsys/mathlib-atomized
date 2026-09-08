/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
public import Mathlib.RingTheory.RingHom.Surjective
public import Mathlib.RingTheory.Spectrum.Prime.TensorProduct
public import Mathlib.Topology.LocalAtTarget

/-!
# Morphisms surjective on stalks

We define the class of morphisms between schemes that are surjective on stalks.
We show that this class is stable under composition and base change.

We also show that (`AlgebraicGeometry.SurjectiveOnStalks.isEmbedding_pullback`)
if `Y ⟶ S` is surjective on stalks, then for every `X ⟶ S`, `X ×ₛ Y` is a subset of
`X × Y` (Cartesian product as topological spaces) with the induced topology.
-/

public section

open CategoryTheory CategoryTheory.Limits Topology

namespace AlgebraicGeometry

universe u

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- The class of morphisms `f : X ⟶ Y` between schemes such that
`𝒪_{Y, f x} ⟶ 𝒪_{X, x}` is surjective for all `x : X`. -/
@[mk_iff]
/-
**AlgebraicGeometry.SurjectiveOnStalks** 是 Mathlib 中的一个类，位于命名空间 `AlgebraicGeomet
ry`。
形式化陈述：SurjectiveOnStalks (f : X ⟶ Y) : Prop where stalkMap_surjective (f) : fora
ll x, Function.Surjective (f.stalkMap x)  alias Scheme.Hom.stalkMap_surjective
参数：f : X ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The class of morphisms `f : X ⟶ Y` between schemes such that
`𝒪_{Y, f x} ⟶ 𝒪_{X, x}` is surjective for all `x : X`.
-/
class SurjectiveOnStalks (f : X ⟶ Y) : Prop where
  stalkMap_surjective (f) : ∀ x, Function.Surjective (f.stalkMap x)

alias Scheme.Hom.stalkMap_surjective := SurjectiveOnStalks.stalkMap_surjective

@[deprecated (since := "2026-01-20")]
alias SurjectiveOnStalks.surj_on_stalks := Scheme.Hom.stalkMap_surjective

namespace SurjectiveOnStalks

/-
**AlgebraicGeometry.SurjectiveOnStalks.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeom
etry.SurjectiveOnStalks`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 900) [IsOpenImmersion f] : SurjectiveOnStalks f :=
  ⟨fun _ ↦ (ConcreteCategory.bijective_of_isIso _).2⟩
/-
**AlgebraicGeometry.SurjectiveOnStalks.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeom
etry.SurjectiveOnStalks`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MorphismProperty.IsMultiplicative @SurjectiveOnStalks where
  id_mem _ := inferInstance
  comp_mem {X Y Z} f g hf hg := by
    refine ⟨fun x ↦ ?_⟩
    rw [Scheme.Hom.stalkMap_comp]
    exact (f.stalkMap_surjective x).comp (g.stalkMap_surjective (f x))

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.SurjectiveOnStalks.comp** 是 Mathlib 中的一个实例，位于命名空间 `Algebraic
Geometry.SurjectiveOnStalks`。
形式化陈述：comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [SurjectiveOnStalks f] [Surj
ectiveOnStalks g] : SurjectiveOnStalks (f ≫ g)
参数：f : X ⟶ Y；g : Y ⟶ Z。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsStableUnderComposition.comp_mem`：∀ {C 
: Type u} {inst : CategoryTheory.Category.{v, u} C} {P : CategoryTheory.Morphism
Property C}   [self : P.IsStableUnderComposition] {X Y …
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.toIsStableUnderComposit
ion`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheor
y.MorphismProperty C}   [self : W.IsMultiplicative], W.IsStableUn…
· 使用定理 `AlgebraicGeometry.SurjectiveOnStalks.instIsMultiplicativeScheme`：Categor
yTheory.MorphismProperty.IsMultiplicative @AlgebraicGeometry.SurjectiveOnStalks
-/
instance comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [SurjectiveOnStalks f]
    [SurjectiveOnStalks g] : SurjectiveOnStalks (f ≫ g) :=
  MorphismProperty.IsStableUnderComposition.comp_mem f g inferInstance inferInstance
/-
**AlgebraicGeometry.SurjectiveOnStalks.eq_stalkwise** 是 Mathlib 中的一个引理，位于命名空间 `A
lgebraicGeometry.SurjectiveOnStalks`。
形式化陈述：eq_stalkwise : @SurjectiveOnStalks = stalkwise (Function.Surjective ·)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `AlgebraicGeometry.surjectiveOnStalks_iff`：∀ {X Y : AlgebraicGeometry.Sch
eme} (f : X ⟶ Y),   AlgebraicGeometry.SurjectiveOnStalks f ↔     ∀ (x : ↥X), Fun
ction.Surjective ⇑(CategoryThe…
-/
lemma eq_stalkwise :
    @SurjectiveOnStalks = stalkwise (Function.Surjective ·) := by
  ext; exact surjectiveOnStalks_iff _
/-
**AlgebraicGeometry.SurjectiveOnStalks.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeom
etry.SurjectiveOnStalks`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsZariskiLocalAtTarget @SurjectiveOnStalks :=
  eq_stalkwise ▸ stalkwiseIsZariskiLocalAtTarget_of_respectsIso RingHom.surjective_respectsIso
/-
**AlgebraicGeometry.SurjectiveOnStalks.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeom
etry.SurjectiveOnStalks`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsZariskiLocalAtSource @SurjectiveOnStalks :=
  eq_stalkwise ▸ stalkwise_isZariskiLocalAtSource_of_respectsIso RingHom.surjective_respectsIso
/-
**AlgebraicGeometry.SurjectiveOnStalks.Spec_iff** 是 Mathlib 中的一个引理，位于命名空间 `Algeb
raicGeometry.SurjectiveOnStalks`。
形式化陈述：Spec_iff {R S : CommRingCat.{u}} {φ : R ⟶ S} : SurjectiveOnStalks (Spec.ma
p φ) ↔ RingHom.SurjectiveOnStalks φ.hom
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.SurjectiveOnStalks.eq_stalkwise`：eq_stalkwise : @Surje
ctiveOnStalks = stalkwise (Function.Surjective ·)
· 使用定理 `Ideal.IsPrime.comap`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst : 
Semiring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S] (f : F)   {K : Ideal 
S} [inst_…
· 使用引理 `AlgebraicGeometry.stalkwise_SpecMap_iff`：stalkwise_SpecMap_iff (hP : Rin
gHom.RespectsIso P) {R S : CommRingCat} (φ : R ⟶ S) : stalkwise P (Spec.map φ) ↔
 forall (p : Ideal S) (_ : p.…
· 使用定理 `RingHom.surjective_respectsIso`：surjective_respectsIso : RespectsIso sur
jective
· 使用定理 `RingHom.SurjectiveOnStalks.eq_1`：∀ {R : Type u_1} [inst : CommRing R] {S
 : Type u_2} [inst_1 : CommRing S] (f : R →+* S),   f.SurjectiveOnStalks =     ∀
 (P : Ideal S) (x : P…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma Spec_iff {R S : CommRingCat.{u}} {φ : R ⟶ S} :
    SurjectiveOnStalks (Spec.map φ) ↔ RingHom.SurjectiveOnStalks φ.hom := by
  rw [eq_stalkwise, stalkwise_SpecMap_iff RingHom.surjective_respectsIso,
    RingHom.SurjectiveOnStalks]
/-
**AlgebraicGeometry.SurjectiveOnStalks.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeom
etry.SurjectiveOnStalks`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasRingHomProperty @SurjectiveOnStalks RingHom.SurjectiveOnStalks :=
  eq_stalkwise ▸ .stalkwise RingHom.surjective_respectsIso

set_option backward.isDefEq.respectTransparency false in
variable {f} in
/-
**AlgebraicGeometry.SurjectiveOnStalks.iff_of_isAffine** 是 Mathlib 中的一个引理，位于命名空间
 `AlgebraicGeometry.SurjectiveOnStalks`。
形式化陈述：iff_of_isAffine [IsAffine X] [IsAffine Y] : SurjectiveOnStalks f ↔ RingHom
.SurjectiveOnStalks (f.app ⊤).hom
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `AlgebraicGeometry.SurjectiveOnStalks.Spec_iff`：Spec_iff {R S : CommRingC
at.{u}} {φ : R ⟶ S} : SurjectiveOnStalks (Spec.map φ) ↔ RingHom.SurjectiveOnStal
ks φ.hom
· 使用定理 `CategoryTheory.MorphismProperty.arrow_mk_iso_iff`：arrow_mk_iso_iff (P : 
MorphismProperty C) [RespectsIso P] {W X Y Z : C} {f : W ⟶ X} {g : Y ⟶ Z} (e : A
rrow.mk f ≅ Arrow.mk g) : P f ↔ P g
· 使用定理 `CategoryTheory.MorphismProperty.IsLocalAtSource.toRespects`：∀ {C : Type 
u} {inst : CategoryTheory.Category.{v, u} C} {P : CategoryTheory.MorphismPropert
y C}   (K : CategoryTheory.Precoverage C) [self …
· 使用定理 `AlgebraicGeometry.SurjectiveOnStalks.instIsZariskiLocalAtSource`：Algebra
icGeometry.IsZariskiLocalAtSource @AlgebraicGeometry.SurjectiveOnStalks
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma iff_of_isAffine [IsAffine X] [IsAffine Y] :
    SurjectiveOnStalks f ↔ RingHom.SurjectiveOnStalks (f.app ⊤).hom := by
  rw [← Spec_iff, MorphismProperty.arrow_mk_iso_iff @SurjectiveOnStalks (arrowIsoSpecΓOfIsAffine f)]
/-
**AlgebraicGeometry.SurjectiveOnStalks.of_comp** 是 Mathlib 中的一个定理，位于命名空间 `Algebr
aicGeometry.SurjectiveOnStalks`。
形式化陈述：of_comp [SurjectiveOnStalks (f ≫ g)] : SurjectiveOnStalks f
参数：f ≫ g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Hom.stalkMap_surjective`：∀ {X Y : AlgebraicGeom
etry.Scheme} (f : X ⟶ Y) [self : AlgebraicGeometry.SurjectiveOnStalks f] (x : ↥X
),   Function.Surjective ⇑(CategoryThe…
· 使用定理 `Function.Surjective.of_comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u
_3} {f : α → β} {g : γ → α},   Function.Surjective (f ∘ g) → Function.Surjective
 f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.Scheme.Hom.stalkMap_comp`：stalkMap_comp {X Y Z : Schem
e.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) : (f ≫ g : X ⟶ Z).stalkMap x = g.stalkMap
 (f x) ≫ f.stalkMap x
-/
theorem of_comp [SurjectiveOnStalks (f ≫ g)] : SurjectiveOnStalks f := by
  refine ⟨fun x ↦ ?_⟩
  have := (f ≫ g).stalkMap_surjective x
  rw [Scheme.Hom.stalkMap_comp] at this
  exact Function.Surjective.of_comp this
/-
**AlgebraicGeometry.SurjectiveOnStalks.stableUnderBaseChange** 是 Mathlib 中的一个实例，
位于命名空间 `AlgebraicGeometry.SurjectiveOnStalks`。
形式化陈述：stableUnderBaseChange : MorphismProperty.IsStableUnderBaseChange @Surjecti
veOnStalks
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.HasRingHomProperty.isStableUnderBaseChange`：isStableUn
derBaseChange (hP : RingHom.IsStableUnderBaseChange Q) : P.IsStableUnderBaseChan
ge
· 使用定理 `AlgebraicGeometry.SurjectiveOnStalks.instHasRingHomPropertySurjectiveOnS
talks`：AlgebraicGeometry.HasRingHomProperty @AlgebraicGeometry.SurjectiveOnStalk
s fun {R S} [CommRing R] [CommRing S] =>   RingHom.SurjectiveOnStal…
· 使用定理 `RingHom.IsStableUnderBaseChange.mk`：∀ {P : {R S : Type u} → [inst : Comm
Ring R] → [inst_1 : CommRing S] → (R →+* S) → Prop},   RingHom.RespectsIso P →  
   (∀ ⦃R S T : Type u⦄ […
· 使用定理 `RingHom.PropertyIsLocal.respectsIso`：RingHom.PropertyIsLocal.respectsIso
 (hP : RingHom.PropertyIsLocal @P) : RingHom.RespectsIso @P
· 使用定理 `AlgebraicGeometry.HasRingHomProperty.isLocal_ringHomProperty`：∀ (P : Cat
egoryTheory.MorphismProperty AlgebraicGeometry.Scheme)   {Q : outParam ({R S : T
ype u} → [inst : CommRing R] → [inst_1 : CommRing …
· 使用定理 `RingHom.SurjectiveOnStalks.baseChange`：∀ {R : Type u_1} [inst : CommRing
 R] {S : Type u_2} [inst_1 : CommRing S] {T : Type u_3} [inst_2 : CommRing T]   
[inst_3 : Algebra R T] [ins…
-/
instance stableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange @SurjectiveOnStalks := by
  apply HasRingHomProperty.isStableUnderBaseChange
  apply RingHom.IsStableUnderBaseChange.mk
  · exact (HasRingHomProperty.isLocal_ringHomProperty @SurjectiveOnStalks).respectsIso
  intro R S T _ _ _ _ _ H
  exact H.baseChange

variable {f} in
/-
**AlgebraicGeometry.SurjectiveOnStalks.mono_of_injective** 是 Mathlib 中的一个引理，位于命名
空间 `AlgebraicGeometry.SurjectiveOnStalks`。
形式化陈述：mono_of_injective [SurjectiveOnStalks f] (hf : Function.Injective f) : Mon
o f
参数：hf : Function.Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.mono_of_mono_map`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.reflectsMonomorphisms_of_reflectsLimitsOfShape`：∀ {C : Ty
pe u₁} {D : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Categ
oryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.ReflectsFiniteLimits.reflects`：∀ {C : Type u₁} {in
st : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.
Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.instReflectsFiniteLimitsOfReflectsLimits`：∀ {C : T
ype u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Cate
goryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `AlgebraicGeometry.Scheme.instFullLocallyRingedSpaceForgetToLocallyRinged
Space`：AlgebraicGeometry.Scheme.forgetToLocallyRingedSpace.Full
· 使用定理 `AlgebraicGeometry.Scheme.instFaithfulLocallyRingedSpaceForgetToLocallyRi
ngedSpace`：AlgebraicGeometry.Scheme.forgetToLocallyRingedSpace.Faithful
· 使用定理 `CategoryTheory.Functor.reflectsMonomorphisms_of_faithful`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTh
eory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `AlgebraicGeometry.LocallyRingedSpace.instFaithfulSheafedSpaceCommRingCat
ForgetToSheafedSpace`：AlgebraicGeometry.LocallyRingedSpace.forgetToSheafedSpace.
Faithful
· 使用引理 `AlgebraicGeometry.SheafedSpace.mono_of_base_injective_of_stalk_epi`：mono
_of_base_injective_of_stalk_epi {X Y : SheafedSpace C} (f : X ⟶ Y) (h₁ : Functio
n.Injective f.hom.base) (h₂ : forall x, Epi (f.hom.stalk…
· 使用定理 `CategoryTheory.ConcreteCategory.epi_of_surjective`：epi_of_surjective {X 
Y : C} (f : X ⟶ Y) (s : Function.Surjective f) : Epi f
· 使用定理 `AlgebraicGeometry.Scheme.Hom.stalkMap_surjective`：∀ {X Y : AlgebraicGeom
etry.Scheme} (f : X ⟶ Y) [self : AlgebraicGeometry.SurjectiveOnStalks f] (x : ↥X
),   Function.Surjective ⇑(CategoryThe…
-/
lemma mono_of_injective [SurjectiveOnStalks f] (hf : Function.Injective f) : Mono f := by
  refine (Scheme.forgetToLocallyRingedSpace ⋙
    LocallyRingedSpace.forgetToSheafedSpace).mono_of_mono_map ?_
  apply SheafedSpace.mono_of_base_injective_of_stalk_epi
  · exact hf
  · exact fun x ↦ ConcreteCategory.epi_of_surjective _ (f.stalkMap_surjective x)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- If `Y ⟶ S` is surjective on stalks, then for every `X ⟶ S`, `X ×ₛ Y` is a subset of
`X × Y` (Cartesian product as topological spaces) with the induced topology. -/
/-
**AlgebraicGeometry.SurjectiveOnStalks.isEmbedding_pullback** 是 Mathlib 中的一个引理，位
于命名空间 `AlgebraicGeometry.SurjectiveOnStalks`。
形式化陈述：isEmbedding_pullback {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) [Surject
iveOnStalks g] : IsEmbedding fun x => (pullback.fst f g x, pullback.snd f g x)
参数：f : X ⟶ S；g : Y ⟶ S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `AlgebraicGeometry.SurjectiveOnStalks.instOfIsOpenImmersion`：∀ {X Y : Alg
ebraicGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.IsOpenImmersion f],   Alge
braicGeometry.SurjectiveOnStalks f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.SurjectiveOnStalks.of_comp`：of_comp [SurjectiveOnStalk
s (f ≫ g)] : SurjectiveOnStalks f
· 使用定理 `AlgebraicGeometry.Spec.map_preimage`：∀ {R S : CommRingCat} (f : Algebrai
cGeometry.Spec S ⟶ AlgebraicGeometry.Spec R),   AlgebraicGeometry.Spec.map (Alge
braicGeometry.Spec.preima…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Homeomorph.surjective`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologic
alSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y),   Function.Surjective ⇑h
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.pullback.lift_fst`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Cate
goryTheory.Limits.HasPullback…
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `AlgebraicGeometry.Scheme.Hom.comp_apply`：comp_apply {X Y Z : Scheme} (f 
: X ⟶ Y) (g : Y ⟶ Z) (x : X) : (f ≫ g) x = g (f x)
· 使用定理 `AlgebraicGeometry.pullbackSpecIso_inv_fst_assoc`：∀ (R S T : Type u) [ins
t : CommRing R] [inst_1 : CommRing S] [inst_2 : CommRing T] [inst_3 : Algebra R 
S]   [inst_4 : Algebra R T] {Z : Alge…
· 使用定理 `CategoryTheory.Limits.pullback.lift_snd`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Cate
goryTheory.Limits.HasPullback…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgebraicGeometry.pullbackSpecIso_inv_snd_assoc`：∀ (R S T : Type u) [ins
t : CommRing R] [inst_1 : CommRing S] [inst_2 : CommRing T] [inst_3 : Algebra R 
S]   [inst_4 : Algebra R T] {Z : Alge…
· 使用定理 `Topology.IsEmbedding.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3
} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : TopologicalSpa
ce Y] [inst_2 :…
· 使用定理 `Topology.IsOpenEmbedding.isEmbedding`：∀ {X : Type u_1} {Y : Type u_2} {f
 : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.
IsOpenEmbedding f → Topolo…
· 使用定理 `Topology.IsOpenEmbedding.prodMap`：∀ {X : Type u} {Y : Type v} {W : Type 
u_1} {Z : Type u_2} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   
[inst_2 : TopologicalS…
· 使用定理 `AlgebraicGeometry.Scheme.Hom.isOpenEmbedding`：isOpenEmbedding : IsOpenEm
bedding f
· 使用引理 `PrimeSpectrum.isEmbedding_tensorProductTo_of_surjectiveOnStalks`：PrimeSp
ectrum.isEmbedding_tensorProductTo_of_surjectiveOnStalks : IsEmbedding (tensorPr
oductTo R S T)
· 使用定理 `AlgebraicGeometry.HasRingHomProperty.Spec_iff`：Spec_iff {R S : CommRingC
at.{u}} {φ : R ⟶ S} : P (Spec.map φ) ↔ Q φ.hom
· 使用定理 `AlgebraicGeometry.SurjectiveOnStalks.instHasRingHomPropertySurjectiveOnS
talks`：AlgebraicGeometry.HasRingHomProperty @AlgebraicGeometry.SurjectiveOnStalk
s fun {R S} [CommRing R] [CommRing S] =>   RingHom.SurjectiveOnStal…
· 使用定理 `Homeomorph.isEmbedding`：isEmbedding (h : X ≃ₜ Y) : IsEmbedding h
· 使用定理 `AlgebraicGeometry.Scheme.instIsStableUnderBaseChangePrecoverageOfIsJoint
lySurjectivePreservingOfIsStableUnderBaseChange`：∀ (P : CategoryTheory.MorphismP
roperty AlgebraicGeometry.Scheme)   [AlgebraicGeometry.Scheme.IsJointlySurjectiv
ePreserving P] [P.IsStableUnd…
（共 58 条，此处仅展示前 30 条）

--- 原说明 ---
If `Y ⟶ S` is surjective on stalks, then for every `X ⟶ S`, `X ×ₛ Y` is a subset
 of
`X × Y` (Cartesian product as topological spaces) with the induced topology.
-/
lemma isEmbedding_pullback {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) [SurjectiveOnStalks g] :
    IsEmbedding fun x ↦ (pullback.fst f g x, pullback.snd f g x) := by
  let L := (fun x ↦ (pullback.fst f g x, pullback.snd f g x))
  have H : ∀ R A B (f' : Spec A ⟶ Spec R) (g' : Spec B ⟶ Spec R) (iX : Spec A ⟶ X)
      (iY : Spec B ⟶ Y) (iS : Spec R ⟶ S) (e₁ e₂), IsOpenImmersion iX → IsOpenImmersion iY →
      IsOpenImmersion iS → IsEmbedding (L ∘ pullback.map f' g' f g iX iY iS e₁ e₂) := by
    intro R A B f' g' iX iY iS e₁ e₂ _ _ _
    have H : SurjectiveOnStalks g' :=
      have : SurjectiveOnStalks (g' ≫ iS) := e₂ ▸ inferInstance
      .of_comp _ iS
    obtain ⟨φ, rfl⟩ : ∃ φ, Spec.map φ = f' := ⟨_, Spec.map_preimage _⟩
    obtain ⟨ψ, rfl⟩ : ∃ ψ, Spec.map ψ = g' := ⟨_, Spec.map_preimage _⟩
    algebraize [φ.hom, ψ.hom]
    rw [HasRingHomProperty.Spec_iff (P := @SurjectiveOnStalks)] at H
    convert!
      ((iX.isOpenEmbedding.prodMap iY.isOpenEmbedding).isEmbedding.comp
            (PrimeSpectrum.isEmbedding_tensorProductTo_of_surjectiveOnStalks R A B H)).comp
        (Scheme.homeoOfIso (pullbackSpecIso R A B)).isEmbedding
    ext1 x
    obtain ⟨x, rfl⟩ := (Scheme.homeoOfIso (pullbackSpecIso R A B).symm).surjective x
    simp only [Scheme.homeoOfIso_apply, Function.comp_apply]
    ext
    · simp only [L, ← Scheme.Hom.comp_apply, pullback.lift_fst, Iso.symm_hom,
        Iso.inv_hom_id]
      erw [← Scheme.Hom.comp_apply, pullbackSpecIso_inv_fst_assoc]
      rfl
    · simp only [L, ← Scheme.Hom.comp_apply, pullback.lift_snd, Iso.symm_hom,
        Iso.inv_hom_id]
      erw [← Scheme.Hom.comp_apply, pullbackSpecIso_inv_snd_assoc]
      rfl
  let 𝒰 := S.affineOpenCover.openCover
  let 𝒱 (i) := ((𝒰.pullback₁ f).X i).affineOpenCover.openCover
  let 𝒲 (i) := ((𝒰.pullback₁ g).X i).affineOpenCover.openCover
  let U (ijk : Σ i, (𝒱 i).I₀ × (𝒲 i).I₀) : TopologicalSpace.Opens (X.carrier × Y) :=
    ⟨{ P | P.1 ∈ ((𝒱 ijk.1).f ijk.2.1 ≫ (𝒰.pullback₁ f).f ijk.1).opensRange ∧
          P.2 ∈ ((𝒲 ijk.1).f ijk.2.2 ≫ (𝒰.pullback₁ g).f ijk.1).opensRange },
      (continuous_fst.1 _ ((𝒱 ijk.1).f ijk.2.1 ≫
      (𝒰.pullback₁ f).f ijk.1).opensRange.2).inter (continuous_snd.1 _
      ((𝒲 ijk.1).f ijk.2.2 ≫ (𝒰.pullback₁ g).f ijk.1).opensRange.2)⟩
  have : Set.range L ⊆ (iSup U :) := by
    simp only [Precoverage.ZeroHypercover.pullback₁_toPreZeroHypercover,
      PreZeroHypercover.pullback₁_I₀, PreZeroHypercover.pullback₁_X, Set.range_subset_iff]
    intro z
    simp only [SetLike.mem_coe, TopologicalSpace.Opens.mem_iSup, Sigma.exists, Prod.exists]
    obtain ⟨is, s, hsx⟩ := 𝒰.exists_eq (f (pullback.fst f g z))
    have hsy : 𝒰.f is s = g (pullback.snd f g z) := by
      rwa [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply]
    obtain ⟨x : (𝒰.pullback₁ f).X is, hx⟩ :=
      Scheme.IsJointlySurjectivePreserving.exists_preimage_fst_triplet_of_prop
        (P := @IsOpenImmersion) inferInstance _ _ hsx.symm
    obtain ⟨y : (𝒰.pullback₁ g).X is, hy⟩ :=
      Scheme.IsJointlySurjectivePreserving.exists_preimage_fst_triplet_of_prop
        (P := @IsOpenImmersion) inferInstance _ _ hsy.symm
    obtain ⟨ix, x, rfl⟩ := (𝒱 is).exists_eq x
    obtain ⟨iy, y, rfl⟩ := (𝒲 is).exists_eq y
    refine ⟨is, ix, iy, ⟨x, hx⟩, ⟨y, hy⟩⟩
  let 𝓤 := (Scheme.Pullback.openCoverOfBase 𝒰 f g).bind
    (fun i ↦ Scheme.Pullback.openCoverOfLeftRight (𝒱 i) (𝒲 i) _ _)
  refine isEmbedding_of_iSup_eq_top_of_preimage_subset_range _ ?_ U this _ (𝓤.f ·)
    (fun i ↦ (𝓤.f i).continuous) ?_ ?_
  · fun_prop
  · rintro i x ⟨⟨x₁, hx₁⟩, ⟨x₂, hx₂⟩⟩
    obtain ⟨x₁', hx₁'⟩ :=
      Scheme.IsJointlySurjectivePreserving.exists_preimage_fst_triplet_of_prop
        (P := @IsOpenImmersion) inferInstance _ _ hx₁.symm
    obtain ⟨x₂', hx₂'⟩ :=
      Scheme.IsJointlySurjectivePreserving.exists_preimage_fst_triplet_of_prop
        (P := @IsOpenImmersion) inferInstance _ _ hx₂.symm
    obtain ⟨z, hz⟩ :=
      Scheme.IsJointlySurjectivePreserving.exists_preimage_fst_triplet_of_prop
        (P := @IsOpenImmersion) inferInstance _ _ (hx₁'.trans hx₂'.symm)
    refine ⟨(pullbackFstFstIso _ _ _ _ _ _ (𝒰.f i.1) ?_ ?_).hom z, ?_⟩
    · simp [pullback.condition]
    · simp [pullback.condition]
    · dsimp only
      rw [← hx₁', ← hz, ← Scheme.Hom.comp_apply]
      erw [← Scheme.Hom.comp_apply]
      congr 5
      apply pullback.hom_ext <;> simp [𝓤, ← pullback.condition, ← pullback.condition_assoc]
  · intro i
    have := H (S.affineOpenCover.X i.1) (((𝒰.pullback₁ f).X i.1).affineOpenCover.X i.2.1)
        (((𝒰.pullback₁ g).X i.1).affineOpenCover.X i.2.2)
        ((𝒱 i.1).f i.2.1 ≫ 𝒰.pullbackHom f i.1)
        ((𝒲 i.1).f i.2.2 ≫ 𝒰.pullbackHom g i.1)
        ((𝒱 i.1).f i.2.1 ≫ (𝒰.pullback₁ f).f i.1)
        ((𝒲 i.1).f i.2.2 ≫ (𝒰.pullback₁ g).f i.1)
        (𝒰.f i.1) (by simp [pullback.condition]) (by simp [pullback.condition])
        inferInstance inferInstance inferInstance
    convert! this using 7
    apply pullback.hom_ext <;>
      simp [𝓤, Scheme.Cover.pullbackHom]

end SurjectiveOnStalks

end AlgebraicGeometry

