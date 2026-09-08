/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.Artinian
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Mathlib.RingTheory.RingHom.QuasiFinite
public import Mathlib.RingTheory.ZariskisMainTheorem

/-!
# Quasi-finite morphisms

We say that a morphism `f : X ⟶ Y` is locally quasi finite if `Γ(Y, U) ⟶ Γ(X, V)` is
quasi-finite (in the mathlib sense) for every pair of affine opens that `f` maps one into the other.

This is equivalent to all the fibers `f⁻¹(x)` having an open cover of `κ(x)`-finite schemes.
Note that this does not require `f` to be quasi-compact nor locally of finite type.

We prove that this is stable under composition and base change, and is right cancellative.

## Main results
- `AlgebraicGeometry.LocallyQuasiFinite` : The class of locally quasi-finite morphisms.
- `AlgebraicGeometry.Scheme.Hom.isDiscrete_preimage_singleton`:
  Locally quasi-finite morphisms have discrete fibers.
- `AlgebraicGeometry.Scheme.Hom.finite_preimage_singleton`:
  Quasi-finite, quasi-compact morphisms have finite fibers.
- `AlgebraicGeometry.locallyQuasiFinite_iff_isFinite_fiber`: If `f` is quasi-compact,
  then `f` is locally quasi-finite iff all the fibers `f⁻¹(x)` are `κ(x)`-finite.
- `AlgebraicGeometry.locallyQuasiFinite_iff_isDiscrete_preimage_singleton`:
  If `f` is locally of finite type, then `f` is locally quasi-finite iff `f` has discrete fibers.
- `AlgebraicGeometry.locallyQuasiFinite_iff_finite_preimage_singleton`:
  If `f` is of finite type, then `f` is locally quasi-finite iff `f` has finite fibers.
-/

@[expose] public section

open CategoryTheory hiding IsDiscrete
open Limits

namespace AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

open Scheme

/--
We say that a morphism `f : X ⟶ Y` is locally quasi finite if `Γ(Y, U) ⟶ Γ(X, V)` is
quasi-finite (in the mathlib sense) for every pair of affine opens that `f` maps one into the other.

Note that this does not require `f` to be quasi-compact nor locally of finite type.

Being locally quasi-finite implies that `f` has discrete fibers
(via `f.isDiscrete_preimage_singleton`).
The converse holds under various scenarios:

- `locallyQuasiFinite_iff_isDiscrete_preimage_singleton`:
  If `f` is quasi-compact, this is equivalent to `f ⁻¹ {x}` being `κ(x)`-finite for all `x`.
- `locallyQuasiFinite_iff_isDiscrete_preimage_singleton`:
  If `f` is locally of finite type, this is equivalent to `f` having discrete fibers.
- `locallyQuasiFinite_iff_finite_preimage_singleton`:
  If `f` is of finite type, this is equivalent to `f` having finite fibers.
-/
@[mk_iff]
/-
**AlgebraicGeometry.LocallyQuasiFinite** 是 Mathlib 中的一个归纳类型，位于命名空间 `AlgebraicGeo
metry`。
形式化陈述：{X Y : AlgebraicGeometry.Scheme} → (X ⟶ Y) → Prop
参数：X ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say that a morphism `f : X ⟶ Y` is locally quasi finite if `Γ(Y, U) ⟶ Γ(X, V)
` is
quasi-finite (in the mathlib sense) for every pair of affine opens that `f` maps
 one into the other.

Note that this does not require `f` to be quasi-compact nor locally of finite ty
pe.

Being locally quasi-finite implies that `f` has discrete fibers
(via `f.isDiscrete_preimage_singleton`).
The converse holds under various scenarios:

- `locallyQuasiFinite_iff_isDiscrete_preimage_singleton`:
  If `f` is quasi-compact, this is equivalent to `f ⁻¹ {x}` being `κ(x)`-finite 
for all `x`.
- `locallyQuasiFinite_iff_isDiscrete_preimage_singleton`:
  If `f` is locally of finite type, this is equivalent to `f` having discrete fi
bers.
- `locallyQuasiFinite_iff_finite_preimage_singleton`:
  If `f` is of finite type, this is equivalent to `f` having finite fibers.
-/
class LocallyQuasiFinite : Prop where
  quasiFinite_appLE :
    ∀ {U : Y.Opens} (_ : IsAffineOpen U) {V : X.Opens} (_ : IsAffineOpen V) (e : V ≤ f ⁻¹ᵁ U),
      (f.appLE U V e).hom.QuasiFinite
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasRingHomProperty @LocallyQuasiFinite RingHom.QuasiFinite where
  isLocal_ringHomProperty := RingHom.QuasiFinite.propertyIsLocal
  eq_affineLocally' := by
    ext X Y f
    simp [locallyQuasiFinite_iff, affineLocally_iff_affineOpens_le, affineOpens]
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MorphismProperty.IsStableUnderComposition @LocallyQuasiFinite :=
  HasRingHomProperty.stableUnderComposition RingHom.QuasiFinite.stableUnderComposition
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    [LocallyQuasiFinite f] [LocallyQuasiFinite g] : LocallyQuasiFinite (f ≫ g) :=
  MorphismProperty.comp_mem _ f g ‹_› ‹_›

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := low) [IsFinite f] : LocallyQuasiFinite f := by
  rw [HasAffineProperty.eq_targetAffineLocally @IsFinite] at ‹IsFinite f›
  rw [HasRingHomProperty.eq_affineLocally @LocallyQuasiFinite]
  refine ((targetAffineLocally_affineAnd_eq_affineLocally
    RingHom.QuasiFinite.propertyIsLocal).le f ?_).2
  exact targetAffineLocally_affineAnd_le (fun hf ↦ .of_finite hf) f ‹_›
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := low) [IsImmersion f] : LocallyQuasiFinite f := by
  rw [← f.liftCoborder_ι]
  have := HasRingHomProperty.of_isOpenImmersion (P := @LocallyQuasiFinite)
    RingHom.QuasiFinite.holdsForLocalizationAway.containsIdentities (f := f.coborderRange.ι)
  infer_instance
/-
**AlgebraicGeometry.LocallyQuasiFinite.of_comp** 是 Mathlib 中的一个定理，位于命名空间 `Algebr
aicGeometry.LocallyQuasiFinite`。
形式化陈述：∀ {X Y Z : AlgebraicGeometry.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)   [AlgebraicG
eometry.LocallyQuasiFinite (CategoryTheory.CategoryStruct.comp f g)],   Algebrai
cGeometry.LocallyQuasiFinite f
参数：f : X ⟶ Y；g : Y ⟶ Z；CategoryTheory.CategoryStruct.comp f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.HasRingHomProperty.of_comp`：of_comp (H : forall {R S T
 : Type u} [CommRing R] [CommRing S] [CommRing T], forall (f : R ->+* S) (g : S 
->+* T), Q (g.comp f) -> Q g) {X Y…
· 使用定理 `AlgebraicGeometry.instHasRingHomPropertyLocallyQuasiFiniteQuasiFinite`：A
lgebraicGeometry.HasRingHomProperty @AlgebraicGeometry.LocallyQuasiFinite fun {R
 S} [CommRing R] [CommRing S] =>   RingHom.QuasiFinite
· 使用定理 `RingHom.QuasiFinite.of_comp`：∀ {T : Type u_3} [inst : CommRing T] {R : T
ype u_4} {S : Type u_5} [inst_1 : CommRing R] [inst_2 : CommRing S]   {f : S →+*
 T} {g : R →+* S}…
-/
theorem LocallyQuasiFinite.of_comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    [LocallyQuasiFinite (f ≫ g)] : LocallyQuasiFinite f :=
  HasRingHomProperty.of_comp (fun _ _ ↦ RingHom.QuasiFinite.of_comp) ‹_›
/-
**AlgebraicGeometry.LocallyQuasiFinite.comp_iff** 是 Mathlib 中的一个定理，位于命名空间 `Algeb
raicGeometry.LocallyQuasiFinite`。
形式化陈述：∀ {X Y Z : AlgebraicGeometry.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [AlgebraicGeo
metry.LocallyQuasiFinite g],   AlgebraicGeometry.LocallyQuasiFinite (CategoryThe
ory.CategoryStruct.comp f g) ↔ AlgebraicGeometry.LocallyQuasiFinite f
参数：f : X ⟶ Y；g : Y ⟶ Z；CategoryTheory.CategoryStruct.comp f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.LocallyQuasiFinite.of_comp`：∀ {X Y Z : AlgebraicGeomet
ry.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)   [AlgebraicGeometry.LocallyQuasiFinite (Cate
goryTheory.CategoryStruct.comp f g…
· 使用定理 `AlgebraicGeometry.instLocallyQuasiFiniteCompScheme`：∀ {X Y Z : Algebraic
Geometry.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [AlgebraicGeometry.LocallyQuasiFinite f
]   [AlgebraicGeometry.LocallyQuasiFinit…
-/
theorem LocallyQuasiFinite.comp_iff {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    [LocallyQuasiFinite g] :
    LocallyQuasiFinite (f ≫ g) ↔ LocallyQuasiFinite f :=
  ⟨fun _ ↦ .of_comp f g, fun _ ↦ inferInstance⟩
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MorphismProperty.IsMultiplicative @LocallyQuasiFinite where
  id_mem _ := inferInstance
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MorphismProperty.IsStableUnderBaseChange @LocallyQuasiFinite :=
  HasRingHomProperty.isStableUnderBaseChange RingHom.QuasiFinite.isStableUnderBaseChange

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) [LocallyQuasiFinite g] :
    LocallyQuasiFinite (pullback.fst f g) :=
  MorphismProperty.pullback_fst f g inferInstance

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) [LocallyQuasiFinite f] :
    LocallyQuasiFinite (pullback.snd f g) :=
  MorphismProperty.pullback_snd f g inferInstance

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (V : Y.Opens) [LocallyQuasiFinite f] : LocallyQuasiFinite (f ∣_ V) :=
  IsZariskiLocalAtTarget.restrict ‹_› V
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (U : X.Opens) (V : Y.Opens) (e) [LocallyQuasiFinite f] :
    LocallyQuasiFinite (f.resLE V U e) := by
  delta Scheme.Hom.resLE; infer_instance
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MorphismProperty.Respects @LocallyQuasiFinite @IsOpenImmersion :=
  HasRingHomProperty.respects_isOpenImmersion
  (RingHom.QuasiFinite.stableUnderComposition.stableUnderCompositionWithLocalizationAway
    RingHom.QuasiFinite.holdsForLocalizationAway).1

set_option backward.isDefEq.respectTransparency false in
nonrec lemma IsLocallyArtinian.of_locallyQuasiFinite [LocallyQuasiFinite f]
    [IsLocallyArtinian Y] : IsLocallyArtinian X := by
  change id _ -- avoid typeclass synthesis from getting stuck on the wlog hypothesis.
  wlog hY : ∃ R, Y = Spec R
  · exact (isLocallyArtinian_iff_openCover (Y.affineCover.pullback₁ f)).mpr fun i ↦
      this (pullback.snd _ _) ⟨_, rfl⟩
  wlog hX : ∃ S, X = Spec S
  · exact (isLocallyArtinian_iff_openCover X.affineCover).mpr fun i ↦
      this (X.affineCover.f i ≫ f) hY ⟨_, rfl⟩
  obtain ⟨R, rfl⟩ := hY
  obtain ⟨S, rfl⟩ := hX
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  simp only [isLocallyArtinianScheme_Spec, HasRingHomProperty.Spec_iff, id_eq] at *
  algebraize [φ.hom]
  have : Module.Finite R S := .of_quasiFinite
  exact .of_finite R S

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [LocallyQuasiFinite f] (y : Y) : IsLocallyArtinian (f.fiber y) :=
  .of_locallyQuasiFinite (pullback.snd _ _)
/-
**AlgebraicGeometry.Scheme.Hom.isDiscrete_preimage_singleton** 是 Mathlib 中的一个定理，
位于命名空间 `AlgebraicGeometry.Scheme.Hom`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.LocallyQ
uasiFinite f] (y : ↥Y),   IsDiscrete (⇑f ⁻¹' {y})
参数：f : X ⟶ Y；y : ↥Y；⇑f ⁻¹' {y}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `AlgebraicGeometry.Scheme.Hom.range_fiberι`：∀ {X Y : AlgebraicGeometry.Sc
heme} (f : X ⟶ Y) (y : ↥Y),   Set.range ⇑(AlgebraicGeometry.Scheme.Hom.fiberι f 
y) = ⇑f ⁻¹' {y}
· 使用引理 `IsDiscrete.image`：IsDiscrete.image (hs : IsDiscrete s) (hf : IsInducing 
f) : IsDiscrete (f '' s)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `isDiscrete_univ_iff`：isDiscrete_univ_iff : IsDiscrete (Set.univ : Set X)
 ↔ DiscreteTopology X
· 使用定理 `AlgebraicGeometry.IsLocallyArtinian.discreteTopology`：∀ {X : AlgebraicGe
ometry.Scheme} [AlgebraicGeometry.IsLocallyArtinian X], DiscreteTopology ↥X
· 使用定理 `AlgebraicGeometry.instIsLocallyArtinianFiberOfLocallyQuasiFinite`：∀ {X Y
 : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.LocallyQuasiFinite f
] (y : ↥Y),   AlgebraicGeometry.IsLocallyArtinian (Alg…
· 使用定理 `Topology.IsEmbedding.toIsInducing`：∀ {X : Type u_1} {Y : Type u_2} [tX :
 TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbeddi
ng f → Topology.IsInduc…
· 使用定理 `AlgebraicGeometry.Scheme.Hom.isEmbedding`：∀ {X Y : AlgebraicGeometry.Sch
eme} (f : X ⟶ Y) [self : AlgebraicGeometry.IsPreimmersion f], Topology.IsEmbeddi
ng ⇑f
· 使用定理 `AlgebraicGeometry.instIsPreimmersionFiberι`：∀ {X Y : AlgebraicGeometry.S
cheme} (f : X ⟶ Y) (y : ↥Y),   AlgebraicGeometry.IsPreimmersion (AlgebraicGeomet
ry.Scheme.Hom.fiberι f y)
-/
lemma Scheme.Hom.isDiscrete_preimage_singleton [LocallyQuasiFinite f] (y : Y) :
    IsDiscrete (f ⁻¹' {y}) := by
  simpa [Scheme.Hom.range_fiberι] using
    (isDiscrete_univ_iff.mpr inferInstance).image (f.fiberι y).isEmbedding.toIsInducing
/-
**AlgebraicGeometry.Scheme.Hom.isDiscrete_preimage** 是 Mathlib 中的一个定理，位于命名空间 `Al
gebraicGeometry.Scheme.Hom`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.LocallyQ
uasiFinite f] {s : Set ↥Y},   IsDiscrete s → IsDiscrete (⇑f ⁻¹' s)
参数：f : X ⟶ Y；⇑f ⁻¹' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsDiscrete.preimage'`：IsDiscrete.preimage' {s : Set Y} (hs : IsDiscrete 
s) (hf : ContinuousOn f (f ⁻¹' s)) (H : forall x, IsDiscrete (f ⁻¹' {x})) : IsDi
screte (f …
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `AlgebraicGeometry.Scheme.Hom.continuous`：∀ {X Y : AlgebraicGeometry.Sche
me} (f : X ⟶ Y), Continuous ⇑f
· 使用定理 `AlgebraicGeometry.Scheme.Hom.isDiscrete_preimage_singleton`：∀ {X Y : Alg
ebraicGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.LocallyQuasiFinite f] (y :
 ↥Y),   IsDiscrete (⇑f ⁻¹' {y})
-/
lemma Scheme.Hom.isDiscrete_preimage [LocallyQuasiFinite f] {s : Set Y} (hs : IsDiscrete s) :
    IsDiscrete (f ⁻¹' s) :=
  hs.preimage' f.continuous.continuousOn f.isDiscrete_preimage_singleton
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [LocallyQuasiFinite f] [QuasiCompact f] (y : Y) : IsArtinianScheme (f.fiber y) where
/-
**AlgebraicGeometry.Scheme.Hom.finite_preimage_singleton** 是 Mathlib 中的一个定理，位于命名
空间 `AlgebraicGeometry.Scheme.Hom`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.LocallyQ
uasiFinite f]   [AlgebraicGeometry.QuasiCompact f] (y : ↥Y), (⇑f ⁻¹' {y}).Finite
参数：f : X ⟶ Y；y : ↥Y；⇑f ⁻¹' {y}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `AlgebraicGeometry.Scheme.Hom.range_fiberι`：∀ {X Y : AlgebraicGeometry.Sc
heme} (f : X ⟶ Y) (y : ↥Y),   Set.range ⇑(AlgebraicGeometry.Scheme.Hom.fiberι f 
y) = ⇑f ⁻¹' {y}
· 使用定理 `Set.Finite.image`：∀ {α : Type u} {β : Type v} {s : Set α} (f : α → β), s
.Finite → (f '' s).Finite
· 使用定理 `Set.finite_univ`：∀ {α : Type u} [Finite α], Set.univ.Finite
· 使用定理 `AlgebraicGeometry.IsArtinianScheme.finite`：∀ {X : AlgebraicGeometry.Sche
me} [AlgebraicGeometry.IsArtinianScheme X], Finite ↥X
· 使用定理 `AlgebraicGeometry.instIsArtinianSchemeFiberOfLocallyQuasiFiniteOfQuasiCo
mpact`：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.Locally
QuasiFinite f]   [AlgebraicGeometry.QuasiCompact f] (y : ↥Y),   Alg…
-/
lemma Scheme.Hom.finite_preimage_singleton [LocallyQuasiFinite f] [QuasiCompact f] (y : Y) :
    (f ⁻¹' {y}).Finite := by
  simpa [Scheme.Hom.range_fiberι] using Set.finite_univ.image (f.fiberι y)

@[deprecated (since := "2026-02-05")]
alias IsFinite.finite_preimage_singleton := Scheme.Hom.finite_preimage_singleton
/-
**AlgebraicGeometry.Scheme.Hom.finite_preimage** 是 Mathlib 中的一个定理，位于命名空间 `Algebr
aicGeometry.Scheme.Hom`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.LocallyQ
uasiFinite f]   [AlgebraicGeometry.QuasiCompact f] {s : Set ↥Y}, s.Finite → (⇑f 
⁻¹' s).Finite
参数：f : X ⟶ Y；⇑f ⁻¹' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.preimage'`：∀ {α : Type u} {β : Type v} {f : α → β} {s : Set β
}, s.Finite → (∀ b ∈ s, (f ⁻¹' {b}).Finite) → (f ⁻¹' s).Finite
· 使用定理 `AlgebraicGeometry.Scheme.Hom.finite_preimage_singleton`：∀ {X Y : Algebra
icGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.LocallyQuasiFinite f]   [Algeb
raicGeometry.QuasiCompact f] (y : ↥Y), (⇑f ⁻…
-/
lemma Scheme.Hom.finite_preimage [LocallyQuasiFinite f] [QuasiCompact f]
    {s : Set Y} (hs : s.Finite) : (f ⁻¹' s).Finite :=
  hs.preimage' fun _ _ ↦ f.finite_preimage_singleton _
/-
**AlgebraicGeometry.Scheme.Hom.tendsto_cofinite_cofinite** 是 Mathlib 中的一个定理，位于命名
空间 `AlgebraicGeometry.Scheme.Hom`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.LocallyQ
uasiFinite f]   [AlgebraicGeometry.QuasiCompact f], Filter.Tendsto (⇑f) Filter.c
ofinite Filter.cofinite
参数：f : X ⟶ Y；⇑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.cofinite_of_finite_preimage_singleton`：Filter.Tendsto.cof
inite_of_finite_preimage_singleton {f : α -> β} (hf : forall b, Finite (f ⁻¹' {b
})) : Tendsto f cofinite cofinite
· 使用定理 `AlgebraicGeometry.Scheme.Hom.finite_preimage_singleton`：∀ {X Y : Algebra
icGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.LocallyQuasiFinite f]   [Algeb
raicGeometry.QuasiCompact f] (y : ↥Y), (⇑f ⁻…
-/
lemma Scheme.Hom.tendsto_cofinite_cofinite [LocallyQuasiFinite f] [QuasiCompact f] :
    Filter.Tendsto f .cofinite .cofinite :=
  .cofinite_of_finite_preimage_singleton f.finite_preimage_singleton

set_option backward.isDefEq.respectTransparency.types false in
nonrec lemma IsFinite.of_locallyQuasiFinite (f : X ⟶ Y) [LocallyQuasiFinite f]
    [QuasiCompact f] [IsLocallyArtinian Y] : IsFinite f := by
  change id _ -- avoid typeclass synthesis from getting stuck on the wlog hypothesis.
  wlog hY : ∃ R, Y = Spec R
  · exact (IsZariskiLocalAtTarget.iff_of_openCover Y.affineCover).mpr fun i ↦
      this (pullback.snd _ _) ⟨_, rfl⟩
  obtain ⟨R, rfl⟩ := hY
  wlog hX : ∃ S, X = Spec S
  · have inst : IsArtinianScheme X :=
      { toIsLocallyArtinian := .of_locallyQuasiFinite f,
        toCompactSpace := QuasiCompact.compactSpace_of_compactSpace f }
    exact (MorphismProperty.cancel_left_of_respectsIso _ _ _).mp
      (this _ ((Scheme.isoSpec X).inv ≫ f) ⟨_, rfl⟩)
  obtain ⟨S, rfl⟩ := hX
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  simp only [isLocallyArtinianScheme_Spec, HasRingHomProperty.Spec_iff, id_eq,
    IsFinite.SpecMap_iff] at *
  algebraize [φ.hom]
  exact .of_quasiFinite
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (f : X ⟶ Y) [LocallyQuasiFinite f] [QuasiCompact f] (x : Y) :
    IsFinite (f.fiberToSpecResidueField x) :=
  .of_locallyQuasiFinite (pullback.snd _ _)

set_option backward.isDefEq.respectTransparency false in
nonrec lemma LocallyQuasiFinite.of_fiberToSpecResidueField
    (hf : ∀ x, LocallyQuasiFinite (f.fiberToSpecResidueField x)) : LocallyQuasiFinite f := by
  change id _ -- avoid typeclass synthesis from getting stuck on the wlog hypothesis.
  wlog hY : ∃ R, Y = Spec R
  · refine (IsZariskiLocalAtTarget.iff_of_openCover Y.affineCover).mpr fun i ↦
      this (f := pullback.snd _ _) (fun x ↦ ?_) ⟨_, rfl⟩
    have (x : Y) : IsLocallyArtinian (f.fiber x) :=
      .of_locallyQuasiFinite (f.fiberToSpecResidueField x)
    refine (MorphismProperty.cancel_right_of_respectsIso @LocallyQuasiFinite _
      (Spec.map ((Y.affineCover.f i).residueFieldMap _))).mp ?_
    let g : (pullback.snd f (Y.affineCover.f i)).fiber x ⟶ f.fiber (Y.affineCover.f i x) :=
      pullback.map _ _ _ _ (pullback.fst _ _) (Spec.map ((Y.affineCover.f i).residueFieldMap _))
        (Y.affineCover.f i) (by simp [pullback.condition]) (by simp)
    have : IsClosedImmersion g := .of_isPreimmersion _ (isClosed_discrete _)
    convert! (inferInstance : LocallyQuasiFinite <| g ≫ f.fiberToSpecResidueField _) using 1
    simp [g, Hom.fiberToSpecResidueField]
  obtain ⟨R, rfl⟩ := hY
  wlog hX : ∃ S, X = Spec S
  · refine (IsZariskiLocalAtSource.iff_of_openCover X.affineCover).mpr fun i ↦
      this _ _ (fun x ↦ ?_) ⟨_, rfl⟩
    have (x : _) : IsLocallyArtinian (f.fiber x) :=
      .of_locallyQuasiFinite (f.fiberToSpecResidueField x)
    let g : (X.affineCover.f i ≫ f).fiber x ⟶ f.fiber x :=
      pullback.map _ _ _ _ (X.affineCover.f i) (𝟙 _) (𝟙 _) (by simp) (by simp)
    have : IsClosedImmersion g := .of_isPreimmersion _ (isClosed_discrete _)
    convert (inferInstance : LocallyQuasiFinite <| g ≫ f.fiberToSpecResidueField _)
    simp [g, Hom.fiberToSpecResidueField]
  obtain ⟨S, rfl⟩ := hX
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  algebraize [φ.hom]
  simp only [HasRingHomProperty.Spec_iff, id_eq]
  refine ⟨fun P hP ↦ ?_⟩
  suffices LocallyQuasiFinite (Spec.map <|
      CommRingCat.ofHom <| algebraMap P.ResidueField (P.Fiber S)) by
    simp only [HasRingHomProperty.Spec_iff (P := @LocallyQuasiFinite), CommRingCat.hom_ofHom,
      RingHom.quasiFinite_algebraMap] at this
    exact .of_quasiFinite
  obtain ⟨x, rfl⟩ : ∃ x : Spec R, P = x.asIdeal := ⟨⟨P, hP⟩, rfl⟩
  refine (MorphismProperty.arrow_mk_iso_iff _ (Arrow.isoMk ?_ ?_ ?_)).mp (hf x)
  · refine asIso (pullback.map _ _ _ _ (𝟙 _) (Spec.map (Spec.residueFieldIso _ x).inv) (𝟙 _)
      ?_ ?_) ≪≫ pullbackSymmetry _ _ ≪≫ pullbackSpecIso ..
    · simp; rfl
    · simp [← Spec.map_comp, fromSpecResidueField, Spec.fromSpecStalk_eq]
  · exact asIso (Spec.map (Spec.residueFieldIso _ x).inv)
  · simp [Hom.fiberToSpecResidueField]

@[deprecated (since := "2026-02-15")]
alias LocallyQuasiFinite.of_isFinite_fiberToSpecResidueField :=
  LocallyQuasiFinite.of_fiberToSpecResidueField
/-
**AlgebraicGeometry.locallyQuasiFinite_iff_isFinite_fiber** 是 Mathlib 中的一个引理，位于命
名空间 `AlgebraicGeometry`。
形式化陈述：locallyQuasiFinite_iff_isFinite_fiber {f : X ⟶ Y} [QuasiCompact f] : Local
lyQuasiFinite f ↔ forall x, IsFinite (f.fiberToSpecResidueField x)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.instIsFiniteFiberToSpecResidueFieldOfLocallyQuasiFinit
eOfQuasiCompact`：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeomet
ry.LocallyQuasiFinite f]   [AlgebraicGeometry.QuasiCompact f] (x : ↥Y),   Alg…
· 使用定理 `AlgebraicGeometry.LocallyQuasiFinite.of_fiberToSpecResidueField`：∀ {X Y 
: AlgebraicGeometry.Scheme} (f : X ⟶ Y),   (∀ (x : ↥Y), AlgebraicGeometry.Locall
yQuasiFinite (AlgebraicGeometry.Scheme.Hom.fiberToSpe…
· 使用定理 `AlgebraicGeometry.instLocallyQuasiFiniteOfIsFinite`：∀ {X Y : AlgebraicGe
ometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.IsFinite f], AlgebraicGeometry.Loc
allyQuasiFinite f
-/
lemma locallyQuasiFinite_iff_isFinite_fiber {f : X ⟶ Y} [QuasiCompact f] :
    LocallyQuasiFinite f ↔ ∀ x, IsFinite (f.fiberToSpecResidueField x) :=
  ⟨fun _ ↦ inferInstance, fun _ ↦ .of_fiberToSpecResidueField f fun _ ↦ inferInstance⟩
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := low) [IsPreimmersion f] : LocallyQuasiFinite f := by
  refine .of_fiberToSpecResidueField _ fun x ↦ ?_
  have : IsClosedImmersion (f.fiberToSpecResidueField x) :=
    .of_isPreimmersion (pullback.snd _ _) (isClosed_discrete _)
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
nonrec lemma locallyQuasiFinite_iff_isDiscrete_preimage_singleton
    {f : X ⟶ Y} [LocallyOfFiniteType f] :
    LocallyQuasiFinite f ↔ ∀ x, IsDiscrete (f ⁻¹' {x}) := by
  refine ⟨fun _ ↦ f.isDiscrete_preimage_singleton, fun H ↦ ?_⟩
  change id _ -- avoid typeclass synthesis from getting stuck on the wlog hypothesis.
  wlog hY : ∃ R, Y = Spec R
  · refine (IsZariskiLocalAtTarget.iff_of_openCover Y.affineCover).mpr fun i ↦
      this (f := pullback.snd _ _) (fun x ↦ ?_) ⟨_, rfl⟩
    convert!
      (H (Y.affineCover.f i x)).preimage ((pullback.fst f _).continuous.continuousOn)
        (pullback.fst f (Y.affineCover.f i)).isOpenEmbedding.injective
    ext
    simp [← (Y.affineCover.f i).isOpenEmbedding.injective.eq_iff, ← Scheme.Hom.comp_apply,
      -Hom.comp_base, pullback.condition]
  obtain ⟨R, rfl⟩ := hY
  wlog hX : ∃ S, X = Spec S
  · exact (IsZariskiLocalAtSource.iff_of_openCover X.affineCover).mpr fun i ↦
      this _ (fun x ↦ (H x).preimage (X.affineCover.f _).continuous.continuousOn
      (X.affineCover.f _).isOpenEmbedding.injective) ⟨_, rfl⟩
  obtain ⟨S, rfl⟩ := hX
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  simp only [HasRingHomProperty.Spec_iff, id_eq] at *
  algebraize [φ.hom]
  exact (Algebra.QuasiFinite.iff_finite_comap_preimage_singleton).mpr fun x ↦
    ((Spec.map φ).isCompact_preimage_singleton _).finite (H _)

set_option backward.isDefEq.respectTransparency.types false in
nonrec lemma LocallyQuasiFinite.of_finite_preimage_singleton
    [LocallyOfFiniteType f] (hf : ∀ x, (f ⁻¹' {x}).Finite) : LocallyQuasiFinite f := by
  change id _ -- avoid typeclass synthesis from getting stuck on the wlog hypothesis.
  wlog hY : ∃ R, Y = Spec R
  · refine (IsZariskiLocalAtTarget.iff_of_openCover Y.affineCover).mpr fun i ↦
      this (f := pullback.snd _ _) (fun x ↦ ?_) ⟨_, rfl⟩
    convert!
      (hf (Y.affineCover.f i x)).preimage
        (pullback.fst f (Y.affineCover.f i)).isOpenEmbedding.injective.injOn
    ext
    simp [← (Y.affineCover.f i).isOpenEmbedding.injective.eq_iff, ← Scheme.Hom.comp_apply,
      -Hom.comp_base, pullback.condition]
  obtain ⟨R, rfl⟩ := hY
  wlog hX : ∃ S, X = Spec S
  · exact (IsZariskiLocalAtSource.iff_of_openCover X.affineCover).mpr fun i ↦ this _ _
      (fun x ↦ ((hf x).preimage (X.affineCover.f _).isOpenEmbedding.injective.injOn :)) ⟨_, rfl⟩
  obtain ⟨S, rfl⟩ := hX
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  simp only [HasRingHomProperty.Spec_iff, id_eq] at *
  algebraize [φ.hom]
  exact (Algebra.QuasiFinite.iff_finite_comap_preimage_singleton).mpr hf
/-
**AlgebraicGeometry.locallyQuasiFinite_iff_finite_preimage_singleton** 是 Mathlib
 中的一个引理，位于命名空间 `AlgebraicGeometry`。
形式化陈述：locallyQuasiFinite_iff_finite_preimage_singleton {f : X ⟶ Y} [LocallyOfFin
iteType f] [QuasiCompact f] : LocallyQuasiFinite f ↔ forall x, (f ⁻¹' {x}).Finit
e
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Hom.finite_preimage_singleton`：∀ {X Y : Algebra
icGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.LocallyQuasiFinite f]   [Algeb
raicGeometry.QuasiCompact f] (y : ↥Y), (⇑f ⁻…
· 使用定理 `AlgebraicGeometry.LocallyQuasiFinite.of_finite_preimage_singleton`：∀ {X 
Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.LocallyOfFiniteType
 f],   (∀ (x : ↥Y), (⇑f ⁻¹' {x}).Finite) → AlgebraicGeo…
-/
lemma locallyQuasiFinite_iff_finite_preimage_singleton
    {f : X ⟶ Y} [LocallyOfFiniteType f] [QuasiCompact f] :
    LocallyQuasiFinite f ↔ ∀ x, (f ⁻¹' {x}).Finite :=
  ⟨fun _ ↦ f.finite_preimage_singleton, .of_finite_preimage_singleton f⟩
/-
**AlgebraicGeometry.LocallyQuasiFinite.of_injective** 是 Mathlib 中的一个定理，位于命名空间 `A
lgebraicGeometry.LocallyQuasiFinite`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} {f : X ⟶ Y} [AlgebraicGeometry.LocallyO
fFiniteType f],   Function.Injective ⇑f → AlgebraicGeometry.LocallyQuasiFinite f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.LocallyQuasiFinite.of_finite_preimage_singleton`：∀ {X 
Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.LocallyOfFiniteType
 f],   (∀ (x : ↥Y), (⇑f ⁻¹' {x}).Finite) → AlgebraicGeo…
· 使用定理 `Set.Subsingleton.finite`：∀ {α : Type u} {s : Set α}, s.Subsingleton → s.
Finite
· 使用定理 `Set.Subsingleton.preimage`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
s : Set β}, s.Subsingleton → Function.Injective f → (f ⁻¹' s).Subsingleton
· 使用定理 `Set.subsingleton_singleton`：subsingleton_singleton {a} : ({a} : Set α).S
ubsingleton
-/
lemma LocallyQuasiFinite.of_injective {f : X ⟶ Y} [LocallyOfFiniteType f]
    (hf : Function.Injective f) : LocallyQuasiFinite f :=
  .of_finite_preimage_singleton _ fun _ ↦ (Set.subsingleton_singleton.preimage hf).finite
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := low) {f : X ⟶ Y} [LocallyOfFiniteType f]
    [UniversallyInjective f] : LocallyQuasiFinite f := .of_injective f.injective

/-- A morphism `f : X ⟶ Y` is quasi-finite at `x : X`
if the stalk map `𝒪_{X, x} ⟶ 𝒪_{Y, f x}` is quasi-finite. -/
/-
**AlgebraicGeometry.Scheme.Hom.QuasiFiniteAt** 是 Mathlib 中的一个定义，位于命名空间 `Algebrai
cGeometry.Scheme.Hom`。
形式化陈述：{X Y : AlgebraicGeometry.Scheme} → (X ⟶ Y) → ↥X → Prop
参数：X ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism `f : X ⟶ Y` is quasi-finite at `x : X`
if the stalk map `𝒪_{X, x} ⟶ 𝒪_{Y, f x}` is quasi-finite.
-/
def Scheme.Hom.QuasiFiniteAt (x : X) : Prop := (f.stalkMap x).hom.QuasiFinite

variable {f} in
set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.Scheme.Hom.QuasiFiniteAt.quasiFiniteAt** 是 Mathlib 中的一个定理，位于
命名空间 `AlgebraicGeometry.Scheme.Hom.QuasiFiniteAt`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} {f : X ⟶ Y} {x : ↥X},   AlgebraicGeomet
ry.Scheme.Hom.QuasiFiniteAt f x →     ∀ {V : X.Opens} (hV : AlgebraicGeometry.Is
AffineOpen V) {U : Y.Opens},       AlgebraicGeometry.IsAffineOpen U →         ∀ 
(hVU : V ≤ (TopologicalSpace.Opens.map f.base).obj U) (hxV : x ∈ V.carrier),    
       (CommRingCat.Hom.hom (AlgebraicGeometry.Scheme.Hom.appLE f U V hVU)).Quas
iFiniteAt             (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
参数：hV : AlgebraicGeometry.IsAffineOpen V；hVU : V ≤ (TopologicalSpace.Opens.map f
.base).obj U；hxV : x ∈ V.carrier；CommRingCat.Hom.hom (AlgebraicGeometry.Scheme.H
om.appLE f U V hVU)；hV.primeIdealOf ⟨x, hxV⟩。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `AlgebraicGeometry.IsAffineOpen.isLocalization_stalk`：isLocalization_stal
k (x : U) : IsLocalization.AtPrime (X.presheaf.stalk x) (hU.primeIdealOf x).asId
eal
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHom.algebraMap_toAlgebra`：RingHom.algebraMap_toAlgebra {R S} [CommSe
miring R] [CommSemiring S] (i : R ->+* S) : @algebraMap R S _ _ i.toAlgebra = i
· 使用引理 `RingHom.quasiFinite_algebraMap`：quasiFinite_algebraMap [Algebra R S] : (
algebraMap R S).QuasiFinite ↔ Algebra.QuasiFinite R S
· 使用引理 `Algebra.QuasiFinite.of_isLocalization`：of_isLocalization (M : Submonoid 
S) [IsLocalization M T] [QuasiFinite R S] : QuasiFinite R T
· 使用定理 `Algebra.QuasiFinite.instOfFinite`：∀ {R : Type u_1} {S : Type u_2} [inst 
: CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] [Module.Finite R S], 
  Algebra.QuasiFinite …
· 使用定理 `RingHom.QuasiFiniteAt.eq_1`：∀ {R : Type u_6} {S : Type u_7} [inst : Comm
Ring R] [inst_1 : CommRing S] (f : R →+* S) (p : Ideal S)   [inst_2 : p.IsPrime]
, f.QuasiFiniteA…
· 使用定理 `Algebra.QuasiFiniteAt.eq_1`：∀ (R : Type u_1) {S : Type u_2} [inst : Comm
Ring R] [inst_1 : CommRing S] [inst_2 : Algebra R S] (p : Ideal S)   [inst_3 : p
.IsPrime], Algeb…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用引理 `CommRingCat.hom_comp`：hom_comp {R S T : CommRingCat} (f : R ⟶ S) (g : S 
⟶ T) : (f ≫ g).hom = g.hom.comp f.hom
· 使用引理 `AlgebraicGeometry.Scheme.Hom.germ_stalkMap`：germ_stalkMap (U : Y.Opens) 
(x : X) (hx : f x in U) : Y.presheaf.germ U (f x) hx ≫ f.stalkMap x = f.app U ≫ 
X.presheaf.germ (f ⁻¹ᵁ U) x hx
· 使用定理 `TopCat.Presheaf.germ_res`：germ_res (F : X.Presheaf C) {U V : Opens X} (i
 : U ⟶ V) (x : X) (hx : x in U) : F.map i.op ≫ F.germ U x hx = F.germ V x (i.le 
hx)
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用引理 `AlgebraicGeometry.Scheme.Hom.app_eq_appLE`：app_eq_appLE {U : Y.Opens} : 
f.app U = f.appLE U _ le_rfl
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `AlgebraicGeometry.Scheme.Hom.appLE_map_assoc`：∀ {X Y : AlgebraicGeometry
.Scheme} (f : X ⟶ Y) {U : Y.Opens} {V V' : X.Opens}   (e : V ≤ (TopologicalSpace
.Opens.map f.base).obj U) (i : Opp…
· 使用定理 `RingHom.comp_assoc`：comp_assoc {δ} {_ : NonAssocSemiring δ} (f : α ->+* 
β) (g : β ->+* γ) (h : γ ->+* δ) : (h.comp g).comp f = h.comp (g.comp f)
· 使用定理 `IsScalarTower.algebraMap_eq`：algebraMap_eq : algebraMap R A = (algebraMa
p S A).comp (algebraMap R S)
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgHom.comp_algebraMap`：comp_algebraMap : (φ : A ->+* B).comp (algebraMa
p R A) = algebraMap R B
· 使用定理 `RingHom.QuasiFinite.comp`：∀ {T : Type u_3} [inst : CommRing T] {R : Type
 u_4} {S : Type u_5} [inst_1 : CommRing R] [inst_2 : CommRing S]   {f : S →+* T}
 {g : R →+* S}…
· 使用定理 `RingHom.QuasiFinite.of_finite`：∀ {T : Type u_3} [inst : CommRing T] {S :
 Type u_5} [inst_1 : CommRing S] {f : S →+* T}, f.Finite → f.QuasiFinite
· 使用定理 `RingEquiv.finite`：∀ {A : Type u_1} {B : Type u_2} [inst : CommRing A] [i
nst_1 : CommRing B] (e : A ≃+* B), e.toRingHom.Finite
-/
lemma Scheme.Hom.QuasiFiniteAt.quasiFiniteAt
    {x : X} (hx : f.QuasiFiniteAt x) {V : X.Opens} (hV : IsAffineOpen V) {U : Y.Opens}
    (hU : IsAffineOpen U) (hVU : V ≤ f ⁻¹ᵁ U) (hxV : x ∈ V.1) :
    (f.appLE U V hVU).hom.QuasiFiniteAt (hV.primeIdealOf ⟨x, hxV⟩).asIdeal := by
  algebraize [(f.appLE U V hVU).hom]
  have H : (Y.presheaf.germ U _ (hVU hxV)).hom.QuasiFinite := by
    algebraize [(Y.presheaf.germ U _ (hVU hxV)).hom]
    have := hU.isLocalization_stalk ⟨f x, (hVU hxV)⟩
    rw [← (Y.presheaf.germ U _ (hVU hxV)).hom.algebraMap_toAlgebra,
      RingHom.quasiFinite_algebraMap]
    exact .of_isLocalization (hU.primeIdealOf ⟨_, hVU hxV⟩).asIdeal.primeCompl
  algebraize [(X.presheaf.germ V x hxV).hom]
  have := hV.isLocalization_stalk ⟨x, hxV⟩
  let e := IsLocalization.algEquiv (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl
    (X.presheaf.stalk (⟨x, hxV⟩ : V.1)) (Localization.AtPrime (hV.primeIdealOf ⟨x, hxV⟩).asIdeal)
  rw [RingHom.QuasiFiniteAt, Algebra.QuasiFiniteAt, ← RingHom.quasiFinite_algebraMap]
  convert! (RingHom.QuasiFinite.of_finite e.finite).comp (hx.comp H)
  rw [← CommRingCat.hom_comp, f.germ_stalkMap, ← X.presheaf.germ_res (homOfLE hVU) _ hxV,
    Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map_assoc, CommRingCat.hom_comp, ← RingHom.comp_assoc,
    IsScalarTower.algebraMap_eq Γ(Y, U) Γ(X, V), e.toAlgHom.comp_algebraMap.symm]
  rfl
/-
**AlgebraicGeometry.Scheme.Hom.quasiFiniteAt** 是 Mathlib 中的一个定理，位于命名空间 `Algebrai
cGeometry.Scheme.Hom`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.LocallyQ
uasiFinite f] (x : ↥X),   AlgebraicGeometry.Scheme.Hom.QuasiFiniteAt f x
参数：f : X ⟶ Y；x : ↥X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.HasRingHomProperty.stalkMap`：stalkMap (hQ : forall {R 
S : Type u} [CommRing R] [CommRing S] (f : R ->+* S) (_ : Q f) (J : Ideal S) (_ 
: J.IsPrime), Q (Localization.local…
· 使用定理 `AlgebraicGeometry.instHasRingHomPropertyLocallyQuasiFiniteQuasiFinite`：A
lgebraicGeometry.HasRingHomProperty @AlgebraicGeometry.LocallyQuasiFinite fun {R
 S} [CommRing R] [CommRing S] =>   RingHom.QuasiFinite
· 使用定理 `RingHom.QuasiFinite.of_comp`：∀ {T : Type u_3} [inst : CommRing T] {R : T
ype u_4} {S : Type u_5} [inst_1 : CommRing R] [inst_2 : CommRing S]   {f : S →+*
 T} {g : R →+* S}…
· 使用定理 `Ideal.IsPrime.comap`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst : 
Semiring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S] (f : F)   {K : Ideal 
S} [inst_…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Localization.localRingHom_to_map`：localRingHom_to_map (J : Ideal P) [J.I
sPrime] (f : R ->+* P) (hIJ : I = J.comap f) (x : R) : localRingHom I J f hIJ (a
lgebraMap _ _ x) = alg…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `RingHom.quasiFinite_algebraMap`：quasiFinite_algebraMap [Algebra R S] : (
algebraMap R S).QuasiFinite ↔ Algebra.QuasiFinite R S
· 使用定理 `Algebra.QuasiFinite.instLocalization`：∀ {R : Type u_1} {S : Type u_2} [i
nst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] (M : Submonoid S)
   [Algebra.QuasiFinite R …
· 使用定理 `RingHom.QuasiFinite.toAlgebra`：∀ {R : Type u_1} {S : Type u_2} [inst : C
ommRing R] [inst_1 : CommRing S] {f : R →+* S},   f.QuasiFinite → Algebra.QuasiF
inite R S
-/
lemma Scheme.Hom.quasiFiniteAt [LocallyQuasiFinite f] (x : X) :
    f.QuasiFiniteAt x := by
  refine HasRingHomProperty.stalkMap ?_ ‹_› x
  introv hf
  algebraize [f]
  refine .of_comp (g := algebraMap R _) ?_
  convert!
    RingHom.quasiFinite_algebraMap.mpr
      (inferInstance : Algebra.QuasiFinite R (Localization.AtPrime J))
  ext; simp; rfl

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.Scheme.Hom.quasiFiniteAt_comp_iff_of_isOpenImmersion** 是 Mat
hlib 中的一个定理，位于命名空间 `AlgebraicGeometry.Scheme.Hom`。
形式化陈述：∀ {X Y Z : AlgebraicGeometry.Scheme} {f : X ⟶ Y} {g : Y ⟶ Z} {x : ↥X} [Alg
ebraicGeometry.IsOpenImmersion f],   AlgebraicGeometry.Scheme.Hom.QuasiFiniteAt 
(CategoryTheory.CategoryStruct.comp f g) x ↔     AlgebraicGeometry.Scheme.Hom.Qu
asiFiniteAt g (f x)
参数：CategoryTheory.CategoryStruct.comp f g；f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.Scheme.Hom.stalkMap_comp`：stalkMap_comp {X Y Z : Schem
e.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) : (f ≫ g : X ⟶ Z).stalkMap x = g.stalkMap
 (f x) ≫ f.stalkMap x
· 使用定理 `RingHom.RespectsIso.cancel_right_isIso`：∀ {P : {R S : Type u} → [inst : 
CommRing R] → [inst_1 : CommRing S] → (R →+* S) → Prop},   RingHom.RespectsIso P
 →     ∀ {R S T : CommRingCa…
· 使用定理 `RingHom.QuasiFinite.respectsIso`：RingHom.RespectsIso fun {R S} [CommRing
 R] [CommRing S] => RingHom.QuasiFinite
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.instIsIsoCommRingCatStalkMap`：∀ {X Y :
 AlgebraicGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.IsOpenImmersion f] (x 
: ↥X),   CategoryTheory.IsIso (AlgebraicGeometry.Sch…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma Scheme.Hom.quasiFiniteAt_comp_iff_of_isOpenImmersion
    {Z : Scheme} {f : X ⟶ Y} {g : Y ⟶ Z} {x : X} [IsOpenImmersion f] :
    (f ≫ g).QuasiFiniteAt x ↔ g.QuasiFiniteAt (f x) := by
  simp only [QuasiFiniteAt, stalkMap_comp, CommRingCat.hom_comp,
    RingHom.QuasiFinite.respectsIso.cancel_right_isIso]
/-
**AlgebraicGeometry.Scheme.Hom.quasiFiniteAt_comp_iff** 是 Mathlib 中的一个定理，位于命名空间 
`AlgebraicGeometry.Scheme.Hom`。
形式化陈述：∀ {X Y Z : AlgebraicGeometry.Scheme} {f : X ⟶ Y} {g : Y ⟶ Z} {x : ↥X} [Alg
ebraicGeometry.LocallyQuasiFinite g],   AlgebraicGeometry.Scheme.Hom.QuasiFinite
At (CategoryTheory.CategoryStruct.comp f g) x ↔     AlgebraicGeometry.Scheme.Hom
.QuasiFiniteAt f x
参数：CategoryTheory.CategoryStruct.comp f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.Scheme.Hom.stalkMap_comp`：stalkMap_comp {X Y Z : Schem
e.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) : (f ≫ g : X ⟶ Z).stalkMap x = g.stalkMap
 (f x) ≫ f.stalkMap x
· 使用定理 `RingHom.QuasiFinite.comp_iff`：∀ {T : Type u_3} [inst : CommRing T] {R : 
Type u_4} {S : Type u_5} [inst_1 : CommRing R] [inst_2 : CommRing S]   {f : S →+
* T} {g : R →+* S}…
· 使用定理 `AlgebraicGeometry.Scheme.Hom.quasiFiniteAt`：∀ {X Y : AlgebraicGeometry.S
cheme} (f : X ⟶ Y) [AlgebraicGeometry.LocallyQuasiFinite f] (x : ↥X),   Algebrai
cGeometry.Scheme.Hom.QuasiFinite…
-/
lemma Scheme.Hom.quasiFiniteAt_comp_iff {Z : Scheme} {f : X ⟶ Y} {g : Y ⟶ Z} {x : X}
    [LocallyQuasiFinite g] :
    (f ≫ g).QuasiFiniteAt x ↔ f.QuasiFiniteAt x := by
  simp only [QuasiFiniteAt, stalkMap_comp]
  exact RingHom.QuasiFinite.comp_iff (g.quasiFiniteAt _)
/-
**AlgebraicGeometry.Scheme.Hom.quasiFiniteAt_iff** 是 Mathlib 中的一个定理，位于命名空间 `Alge
braicGeometry.Scheme.Hom`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} {f : X ⟶ Y} {x : ↥X},   AlgebraicGeomet
ry.Scheme.Hom.QuasiFiniteAt f x ↔     AlgebraicGeometry.LocallyQuasiFinite (Cate
goryTheory.CategoryStruct.comp (X.fromSpecStalk x) f)
参数：CategoryTheory.CategoryStruct.comp (X.fromSpecStalk x) f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `AlgebraicGeometry.Scheme.SpecMap_stalkMap_fromSpecStalk`：SpecMap_stalkMa
p_fromSpecStalk {x} : Spec.map (f.stalkMap x) ≫ Y.fromSpecStalk _ = X.fromSpecSt
alk x ≫ f
· 使用定理 `AlgebraicGeometry.LocallyQuasiFinite.comp_iff`：∀ {X Y Z : AlgebraicGeome
try.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [AlgebraicGeometry.LocallyQuasiFinite g],   
AlgebraicGeometry.LocallyQuasiFinit…
· 使用定理 `AlgebraicGeometry.instLocallyQuasiFiniteOfIsPreimmersion`：∀ {X Y : Algeb
raicGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.IsPreimmersion f],   Algebra
icGeometry.LocallyQuasiFinite f
· 使用定理 `AlgebraicGeometry.instIsPreimmersionFromSpecStalk`：∀ {X : AlgebraicGeome
try.Scheme} (x : ↥X), AlgebraicGeometry.IsPreimmersion (X.fromSpecStalk x)
· 使用定理 `AlgebraicGeometry.HasRingHomProperty.Spec_iff`：Spec_iff {R S : CommRingC
at.{u}} {φ : R ⟶ S} : P (Spec.map φ) ↔ Q φ.hom
· 使用定理 `AlgebraicGeometry.instHasRingHomPropertyLocallyQuasiFiniteQuasiFinite`：A
lgebraicGeometry.HasRingHomProperty @AlgebraicGeometry.LocallyQuasiFinite fun {R
 S} [CommRing R] [CommRing S] =>   RingHom.QuasiFinite
· 使用定理 `AlgebraicGeometry.Scheme.Hom.QuasiFiniteAt.eq_1`：∀ {X Y : AlgebraicGeome
try.Scheme} (f : X ⟶ Y) (x : ↥X),   AlgebraicGeometry.Scheme.Hom.QuasiFiniteAt f
 x =     (CommRingCat.Hom.hom (Algebr…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma Scheme.Hom.quasiFiniteAt_iff {f : X ⟶ Y} {x : X} :
    f.QuasiFiniteAt x ↔ LocallyQuasiFinite (X.fromSpecStalk x ≫ f) := by
  rw [← SpecMap_stalkMap_fromSpecStalk, LocallyQuasiFinite.comp_iff,
    HasRingHomProperty.Spec_iff (P := @LocallyQuasiFinite), QuasiFiniteAt]

set_option backward.isDefEq.respectTransparency false in
nonrec lemma Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber
    {f : X ⟶ Y} [LocallyOfFiniteType f] {x : X} :
    f.QuasiFiniteAt x ↔ IsOpen {f.asFiber x} := by
  rw [← (f.fiberHomeo (f x)).isOpen_image]
  simp only [Set.image_singleton, asFiber, Homeomorph.apply_symm_apply]
  wlog hY : ∃ R, Y = Spec R
  · obtain ⟨i, y, hy⟩ := Y.affineCover.exists_eq (f x)
    obtain ⟨x, rfl, rfl⟩ := Scheme.Pullback.exists_preimage_pullback _ _ hy.symm
    let ι := Y.affineCover.f i
    convert! this (f := pullback.snd f ι) (x := x) ⟨_, rfl⟩ using 1
    · exact (RingHom.QuasiFinite.respectsIso.arrow_mk_iso_iff
        (Scheme.stalkMapIsoOfIsPullback (.of_hasPullback f ι) x))
    have H : pullback.snd f ι ⁻¹' {pullback.snd f ι x} =
        pullback.fst f ι ⁻¹' f ⁻¹' {f (pullback.fst f ι x)} := by
      rw [← Set.preimage_comp, ← TopCat.coe_comp, ← Scheme.Hom.comp_base, ← Scheme.Hom.comp_apply,
        pullback.condition]
      simp [← Set.image_singleton, Set.preimage_comp, Set.preimage_image_eq _ ι.injective]
    let f' : pullback.snd f ι ⁻¹' {pullback.snd f ι x} → f ⁻¹' {f (pullback.fst f ι x)} :=
      Set.MapsTo.restrict (pullback.fst f ι) _ _ fun a ha ↦ H.le ha
    have : Topology.IsOpenEmbedding f' := by
      convert!
        (f ⁻¹' {f (pullback.fst f ι x)}).restrictPreimage_isOpenEmbedding
          (pullback.fst f ι).isOpenEmbedding using 0
      dsimp [f', Set.restrictPreimage]
      congr!
    rw [this.isOpen_iff_image_isOpen, Set.image_singleton]; rfl
  obtain ⟨R, rfl⟩ := hY
  wlog hX : ∃ S, X = Spec S
  · obtain ⟨i, x, rfl⟩ := X.affineCover.exists_eq x
    let ι := X.affineCover.f i
    convert! this (x := x) _ (f := ι ≫ f) ⟨_, rfl⟩ using 1
    · exact quasiFiniteAt_comp_iff_of_isOpenImmersion.symm
    rw [((f ⁻¹' {f (ι x)}).restrictPreimage_isOpenEmbedding
      ι.isOpenEmbedding).isOpen_iff_image_isOpen, Set.image_singleton]; rfl
  obtain ⟨S, rfl⟩ := hX
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at ‹LocallyOfFiniteType (Spec.map φ)›
  algebraize [φ.hom]
  rw [← Algebra.quasiFiniteAt_iff_isOpen_singleton_fiber]
  let := Localization.AtPrime.algebraOfLiesOver (x.asIdeal.under R) x.asIdeal
  trans Algebra.QuasiFinite (Localization.AtPrime (x.asIdeal.under R))
    (Localization.AtPrime x.asIdeal)
  · rw [← RingHom.quasiFinite_algebraMap]
    exact RingHom.QuasiFinite.respectsIso.arrow_mk_iso_iff (Scheme.arrowStalkMapSpecIso ..)
  exact ⟨fun _ ↦ .trans _ (Localization.AtPrime (x.asIdeal.under R)) _,
    fun _ ↦ .of_restrictScalars R _ _⟩

nonrec lemma Scheme.Hom.QuasiFiniteAt.isClopen_singleton_asFiber
    [LocallyOfFiniteType f] {x : X} (hx : f.QuasiFiniteAt x) : IsClopen {f.asFiber x} := by
  have := Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber.mp ‹_›
  exact ⟨isClosed_singleton_of_isLocallyClosed_singleton this.isLocallyClosed, this⟩

end AlgebraicGeometry

