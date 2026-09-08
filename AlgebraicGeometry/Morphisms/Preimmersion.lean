/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Morphisms.SurjectiveOnStalks

/-!

# Preimmersions of schemes

A morphism of schemes `f : X ⟶ Y` is a preimmersion if the underlying map of topological spaces
is an embedding and the induced morphisms of stalks are all surjective. This is not a concept seen
in the literature but it is useful for generalizing results on immersions to other maps including
`Spec 𝒪_{X, x} ⟶ X` and inclusions of fibers `κ(x) ×ₓ Y ⟶ Y`.

-/

public section

universe v u

open CategoryTheory Topology

namespace AlgebraicGeometry

/-- A morphism of schemes `f : X ⟶ Y` is a preimmersion if the underlying map of
topological spaces is an embedding and the induced morphisms of stalks are all surjective. -/
@[mk_iff]
/-
**AlgebraicGeometry.IsPreimmersion** 是 Mathlib 中的一个类，位于命名空间 `AlgebraicGeometry`。
形式化陈述：IsPreimmersion {X Y : Scheme} (f : X ⟶ Y) : Prop extends SurjectiveOnStalk
s f where isEmbedding (f) : IsEmbedding f  alias Scheme.Hom.isEmbedding
参数：f : X ⟶ Y。
继承自：SurjectiveOnStalks f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism of schemes `f : X ⟶ Y` is a preimmersion if the underlying map of
topological spaces is an embedding and the induced morphisms of stalks are all s
urjective.
-/
class IsPreimmersion {X Y : Scheme} (f : X ⟶ Y) : Prop extends SurjectiveOnStalks f where
  isEmbedding (f) : IsEmbedding f

alias Scheme.Hom.isEmbedding := IsPreimmersion.isEmbedding

@[deprecated (since := "2026-01-20")] alias IsPreimmersion.base_embedding := Scheme.Hom.isEmbedding
/-
**AlgebraicGeometry.isPreimmersion_eq_inf** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGe
ometry`。
形式化陈述：isPreimmersion_eq_inf : @IsPreimmersion = (@SurjectiveOnStalks ⊓ topologic
ally IsEmbedding : MorphismProperty _)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.isPreimmersion_iff`：∀ {X Y : AlgebraicGeometry.Scheme}
 (f : X ⟶ Y),   AlgebraicGeometry.IsPreimmersion f ↔ AlgebraicGeometry.Surjectiv
eOnStalks f ∧ Topology.IsE…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isPreimmersion_eq_inf :
    @IsPreimmersion = (@SurjectiveOnStalks ⊓ topologically IsEmbedding : MorphismProperty _) := by
  ext
  rw [isPreimmersion_iff]
  rfl

namespace IsPreimmersion

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.IsPreimmersion.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry
.IsPreimmersion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsZariskiLocalAtTarget @IsPreimmersion :=
  isPreimmersion_eq_inf ▸ inferInstance
/-
**AlgebraicGeometry.IsPreimmersion.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry
.IsPreimmersion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 900) {X Y : Scheme} (f : X ⟶ Y) [IsOpenImmersion f] : IsPreimmersion f where
  isEmbedding := f.isOpenEmbedding.isEmbedding
  stalkMap_surjective _ := (ConcreteCategory.bijective_of_isIso _).2
/-
**AlgebraicGeometry.IsPreimmersion.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry
.IsPreimmersion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MorphismProperty.IsMultiplicative @IsPreimmersion where
  id_mem _ := inferInstance
  comp_mem f g _ _ := ⟨g.isEmbedding.comp f.isEmbedding⟩

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.IsPreimmersion.comp** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeom
etry.IsPreimmersion`。
形式化陈述：comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [IsPreimmersion f] [IsPreimm
ersion g] : IsPreimmersion (f ≫ g)
参数：f : X ⟶ Y；g : Y ⟶ Z。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsStableUnderComposition.comp_mem`：∀ {C 
: Type u} {inst : CategoryTheory.Category.{v, u} C} {P : CategoryTheory.Morphism
Property C}   [self : P.IsStableUnderComposition] {X Y …
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.toIsStableUnderComposit
ion`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheor
y.MorphismProperty C}   [self : W.IsMultiplicative], W.IsStableUn…
· 使用定理 `AlgebraicGeometry.IsPreimmersion.instIsMultiplicativeScheme`：CategoryThe
ory.MorphismProperty.IsMultiplicative @AlgebraicGeometry.IsPreimmersion
-/
instance comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [IsPreimmersion f]
    [IsPreimmersion g] : IsPreimmersion (f ≫ g) :=
  MorphismProperty.IsStableUnderComposition.comp_mem f g inferInstance inferInstance
/-
**AlgebraicGeometry.IsPreimmersion.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry
.IsPreimmersion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 900) {X Y} (f : X ⟶ Y) [IsPreimmersion f] : Mono f :=
  SurjectiveOnStalks.mono_of_injective f.isEmbedding.injective
/-
**AlgebraicGeometry.IsPreimmersion.of_comp** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicG
eometry.IsPreimmersion`。
形式化陈述：of_comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [IsPreimmersion g] [IsPre
immersion (f ≫ g)] : IsPreimmersion f where isEmbedding
参数：f : X ⟶ Y；g : Y ⟶ Z；f ≫ g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Hom.stalkMap_surjective`：∀ {X Y : AlgebraicGeom
etry.Scheme} (f : X ⟶ Y) [self : AlgebraicGeometry.SurjectiveOnStalks f] (x : ↥X
),   Function.Surjective ⇑(CategoryThe…
· 使用定理 `AlgebraicGeometry.IsPreimmersion.toSurjectiveOnStalks`：∀ {X Y : Algebrai
cGeometry.Scheme} {f : X ⟶ Y} [self : AlgebraicGeometry.IsPreimmersion f],   Alg
ebraicGeometry.SurjectiveOnStalks f
· 使用定理 `Function.Surjective.of_comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u
_3} {f : α → β} {g : γ → α},   Function.Surjective (f ∘ g) → Function.Surjective
 f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.Scheme.Hom.stalkMap_comp`：stalkMap_comp {X Y Z : Schem
e.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) : (f ≫ g : X ⟶ Z).stalkMap x = g.stalkMap
 (f x) ≫ f.stalkMap x
· 使用定理 `AlgebraicGeometry.Scheme.Hom.isEmbedding`：∀ {X Y : AlgebraicGeometry.Sch
eme} (f : X ⟶ Y) [self : AlgebraicGeometry.IsPreimmersion f], Topology.IsEmbeddi
ng ⇑f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Topology.IsEmbedding.of_comp_iff`：∀ {X : Type u_1} {Y : Type u_2} {Z : T
ype u_3} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : Topolog
icalSpace Y] [inst_2 :…
-/
theorem of_comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [IsPreimmersion g]
    [IsPreimmersion (f ≫ g)] : IsPreimmersion f where
  isEmbedding := by
    have h := (f ≫ g).isEmbedding
    rwa [← g.isEmbedding.of_comp_iff]
  stalkMap_surjective x := by
    have h := (f ≫ g).stalkMap_surjective x
    rw [Scheme.Hom.stalkMap_comp] at h
    exact Function.Surjective.of_comp h
/-
**AlgebraicGeometry.IsPreimmersion.comp_iff** 是 Mathlib 中的一个定理，位于命名空间 `Algebraic
Geometry.IsPreimmersion`。
形式化陈述：comp_iff {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [IsPreimmersion g] : IsP
reimmersion (f ≫ g) ↔ IsPreimmersion f
参数：f : X ⟶ Y；g : Y ⟶ Z。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.IsPreimmersion.of_comp`：of_comp {X Y Z : Scheme} (f : 
X ⟶ Y) (g : Y ⟶ Z) [IsPreimmersion g] [IsPreimmersion (f ≫ g)] : IsPreimmersion 
f where isEmbedding
-/
theorem comp_iff {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [IsPreimmersion g] :
    IsPreimmersion (f ≫ g) ↔ IsPreimmersion f :=
  ⟨fun _ ↦ of_comp f g, fun _ ↦ inferInstance⟩
/-
**AlgebraicGeometry.IsPreimmersion.SpecMap_iff** 是 Mathlib 中的一个引理，位于命名空间 `Algebr
aicGeometry.IsPreimmersion`。
形式化陈述：SpecMap_iff {R S : CommRingCat.{u}} (f : R ⟶ S) : IsPreimmersion (Spec.map
 f) ↔ IsEmbedding (PrimeSpectrum.comap f.hom) ∧ f.hom.SurjectiveOnStalks
参数：f : R ⟶ S。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.HasRingHomProperty.Spec_iff`：Spec_iff {R S : CommRingC
at.{u}} {φ : R ⟶ S} : P (Spec.map φ) ↔ Q φ.hom
· 使用定理 `AlgebraicGeometry.SurjectiveOnStalks.instHasRingHomPropertySurjectiveOnS
talks`：AlgebraicGeometry.HasRingHomProperty @AlgebraicGeometry.SurjectiveOnStalk
s fun {R S} [CommRing R] [CommRing S] =>   RingHom.SurjectiveOnStal…
· 使用定理 `AlgebraicGeometry.isPreimmersion_iff`：∀ {X Y : AlgebraicGeometry.Scheme}
 (f : X ⟶ Y),   AlgebraicGeometry.IsPreimmersion f ↔ AlgebraicGeometry.Surjectiv
eOnStalks f ∧ Topology.IsE…
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma SpecMap_iff {R S : CommRingCat.{u}} (f : R ⟶ S) :
    IsPreimmersion (Spec.map f) ↔ IsEmbedding (PrimeSpectrum.comap f.hom) ∧
      f.hom.SurjectiveOnStalks := by
  rw [← HasRingHomProperty.Spec_iff (P := @SurjectiveOnStalks), isPreimmersion_iff, and_comm]
  rfl
/-
**AlgebraicGeometry.IsPreimmersion.mk_SpecMap** 是 Mathlib 中的一个引理，位于命名空间 `Algebra
icGeometry.IsPreimmersion`。
形式化陈述：mk_SpecMap {R S : CommRingCat.{u}} {f : R ⟶ S} (h₁ : IsEmbedding (PrimeSpe
ctrum.comap f.hom)) (h₂ : f.hom.SurjectiveOnStalks) : IsPreimmersion (Spec.map f
)
参数：h₁ : IsEmbedding (PrimeSpectrum.comap f.hom)；h₂ : f.hom.SurjectiveOnStalks。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `AlgebraicGeometry.IsPreimmersion.SpecMap_iff`：SpecMap_iff {R S : CommRin
gCat.{u}} (f : R ⟶ S) : IsPreimmersion (Spec.map f) ↔ IsEmbedding (PrimeSpectrum
.comap f.hom) ∧ f.hom.SurjectiveOn…
-/
lemma mk_SpecMap {R S : CommRingCat.{u}} {f : R ⟶ S}
    (h₁ : IsEmbedding (PrimeSpectrum.comap f.hom)) (h₂ : f.hom.SurjectiveOnStalks) :
    IsPreimmersion (Spec.map f) :=
  (SpecMap_iff f).mpr ⟨h₁, h₂⟩
/-
**AlgebraicGeometry.IsPreimmersion.of_isLocalization** 是 Mathlib 中的一个引理，位于命名空间 `
AlgebraicGeometry.IsPreimmersion`。
形式化陈述：of_isLocalization {R S : Type u} [CommRing R] (M : Submonoid R) [CommRing 
S] [Algebra R S] [IsLocalization M S] : IsPreimmersion (Spec.map (CommRingCat.of
Hom <| algebraMap R S))
参数：M : Submonoid R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.IsPreimmersion.mk_SpecMap`：mk_SpecMap {R S : CommRingC
at.{u}} {f : R ⟶ S} (h₁ : IsEmbedding (PrimeSpectrum.comap f.hom)) (h₂ : f.hom.S
urjectiveOnStalks) : IsPreimmersi…
· 使用定理 `PrimeSpectrum.localization_comap_isEmbedding`：localization_comap_isEmbed
ding [Algebra R S] (M : Submonoid R) [IsLocalization M S] : IsEmbedding (comap (
algebraMap R S))
· 使用引理 `RingHom.surjectiveOnStalks_of_isLocalization`：surjectiveOnStalks_of_isLo
calization [Algebra R S] [IsLocalization M S] : SurjectiveOnStalks (algebraMap R
 S)
-/
lemma of_isLocalization {R S : Type u} [CommRing R] (M : Submonoid R) [CommRing S]
    [Algebra R S] [IsLocalization M S] :
    IsPreimmersion (Spec.map (CommRingCat.ofHom <| algebraMap R S)) :=
  IsPreimmersion.mk_SpecMap
    (PrimeSpectrum.localization_comap_isEmbedding (R := R) S M)
    (RingHom.surjectiveOnStalks_of_isLocalization (M := M) S)

set_option backward.isDefEq.respectTransparency.types false in
open Limits MorphismProperty in
/-
**AlgebraicGeometry.IsPreimmersion.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry
.IsPreimmersion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsStableUnderBaseChange @IsPreimmersion := by
  refine .mk' fun X Y Z f g _ _ ↦ ?_
  have := pullback_fst (P := @SurjectiveOnStalks) f g inferInstance
  constructor
  let L (x : (pullback f g :)) : { x : X × Y | f x.1 = g x.2 } :=
    ⟨⟨pullback.fst f g x, pullback.snd f g x⟩,
    by simp only [Set.mem_ofPred, ← Scheme.Hom.comp_apply, pullback.condition]⟩
  have : IsEmbedding L := IsEmbedding.of_comp (by fun_prop) continuous_subtype_val
    (SurjectiveOnStalks.isEmbedding_pullback f g)
  exact IsEmbedding.subtypeVal.comp ((TopCat.pullbackHomeoPreimage _ f.continuous _
    g.isEmbedding).isEmbedding.comp this)

variable {X Y Z : Scheme} (f : X ⟶ Z) (g : Y ⟶ Z)

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.IsPreimmersion.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry
.IsPreimmersion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsPreimmersion g] : IsPreimmersion (Limits.pullback.fst f g) :=
  MorphismProperty.pullback_fst f g inferInstance

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.IsPreimmersion.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry
.IsPreimmersion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsPreimmersion f] : IsPreimmersion (Limits.pullback.snd f g) :=
  MorphismProperty.pullback_snd f g inferInstance
/-
**AlgebraicGeometry.IsPreimmersion.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry
.IsPreimmersion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (f : X ⟶ Y) (V : Y.Opens) [IsPreimmersion f] : IsPreimmersion (f ∣_ V) :=
  IsZariskiLocalAtTarget.restrict ‹_› V

end IsPreimmersion

end AlgebraicGeometry

