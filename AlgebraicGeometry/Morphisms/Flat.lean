/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten, Andrew Yang
-/
module

public import Mathlib.Algebra.Category.Ring.Under.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.RingTheory.RingHom.FaithfullyFlat

/-!
# Flat morphisms

A morphism of schemes `f : X ⟶ Y` is flat if for each affine `U ⊆ Y` and
`V ⊆ f ⁻¹' U`, the induced map `Γ(Y, U) ⟶ Γ(X, V)` is flat. This is equivalent to
asking that all stalk maps are flat (see `AlgebraicGeometry.Flat.iff_flat_stalkMap`).

We show that this property is local, and are stable under compositions and base change.

-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe v u

namespace AlgebraicGeometry

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y)

/-- A morphism of schemes `f : X ⟶ Y` is flat if for each affine `U ⊆ Y` and
`V ⊆ f ⁻¹' U`, the induced map `Γ(Y, U) ⟶ Γ(X, V)` is flat. This is equivalent to
asking that all stalk maps are flat (see `AlgebraicGeometry.Flat.iff_flat_stalkMap`).
-/
@[mk_iff]
/-
**AlgebraicGeometry.Flat** 是 Mathlib 中的一个类，位于命名空间 `AlgebraicGeometry`。
形式化陈述：Flat (f : X ⟶ Y) : Prop where flat_appLE (f) : forall {U : Y.Opens} (_ : I
sAffineOpen U) {V : X.Opens} (_ : IsAffineOpen V) (e : V <= f ⁻¹ᵁ U), (f.appLE U
 V e).hom.Flat  alias Scheme.Hom.flat_appLE
参数：f : X ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism of schemes `f : X ⟶ Y` is flat if for each affine `U ⊆ Y` and
`V ⊆ f ⁻¹' U`, the induced map `Γ(Y, U) ⟶ Γ(X, V)` is flat. This is equivalent t
o
asking that all stalk maps are flat (see `AlgebraicGeometry.Flat.iff_flat_stalkM
ap`).
-/
class Flat (f : X ⟶ Y) : Prop where
  flat_appLE (f) :
    ∀ {U : Y.Opens} (_ : IsAffineOpen U) {V : X.Opens} (_ : IsAffineOpen V) (e : V ≤ f ⁻¹ᵁ U),
      (f.appLE U V e).hom.Flat

alias Scheme.Hom.flat_appLE := Flat.flat_appLE

@[deprecated (since := "2026-01-20")] alias Flat.flat_of_affine_subset := Scheme.Hom.flat_appLE

namespace Flat

/-
**AlgebraicGeometry.Flat.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Flat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasRingHomProperty @Flat RingHom.Flat where
  isLocal_ringHomProperty := RingHom.Flat.propertyIsLocal
  eq_affineLocally' := by
    ext X Y f
    rw [flat_iff, affineLocally_iff_forall_isAffineOpen]
/-
**AlgebraicGeometry.Flat.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Flat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 900) [IsOpenImmersion f] : Flat f :=
  HasRingHomProperty.of_isOpenImmersion
    RingHom.Flat.containsIdentities
/-
**AlgebraicGeometry.Flat.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Flat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MorphismProperty.IsStableUnderComposition @Flat :=
  HasRingHomProperty.stableUnderComposition RingHom.Flat.stableUnderComposition

@[simp]
/-
**AlgebraicGeometry.Flat.SpecMap_iff** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometr
y.Flat`。
形式化陈述：SpecMap_iff {R S : CommRingCat.{u}} {f : R ⟶ S} : Flat (Spec.map f) ↔ f.ho
m.Flat
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.HasRingHomProperty.Spec_iff`：Spec_iff {R S : CommRingC
at.{u}} {φ : R ⟶ S} : P (Spec.map φ) ↔ Q φ.hom
· 使用定理 `AlgebraicGeometry.Flat.instHasRingHomPropertyFlat`：AlgebraicGeometry.Has
RingHomProperty @AlgebraicGeometry.Flat fun {R S} [CommRing R] [CommRing S] => R
ingHom.Flat
-/
lemma SpecMap_iff {R S : CommRingCat.{u}} {f : R ⟶ S} : Flat (Spec.map f) ↔ f.hom.Flat :=
  HasRingHomProperty.Spec_iff
/-
**AlgebraicGeometry.Flat.comp** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Flat`
。
形式化陈述：comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [hf : Flat f] [hg : Flat g] 
: Flat (f ≫ g)
参数：f : X ⟶ Y；g : Y ⟶ Z。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.comp_mem`：comp_mem (W : MorphismProperty
 C) [W.IsStableUnderComposition] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : W f) 
(hg : W g) : W (f ≫ g)
· 使用定理 `AlgebraicGeometry.Flat.instIsStableUnderCompositionScheme`：CategoryTheor
y.MorphismProperty.IsStableUnderComposition @AlgebraicGeometry.Flat
-/
instance comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    [hf : Flat f] [hg : Flat g] : Flat (f ≫ g) :=
  MorphismProperty.comp_mem _ f g hf hg

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.Flat.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Flat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MorphismProperty.Respects @Flat @IsOpenImmersion where
  postcomp _ _ _ _ := inferInstance
/-
**AlgebraicGeometry.Flat.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Flat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MorphismProperty.IsMultiplicative @Flat where
  id_mem _ := inferInstance
/-
**AlgebraicGeometry.Flat.isStableUnderBaseChange** 是 Mathlib 中的一个实例，位于命名空间 `Alge
braicGeometry.Flat`。
形式化陈述：isStableUnderBaseChange : MorphismProperty.IsStableUnderBaseChange @Flat
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.HasRingHomProperty.isStableUnderBaseChange`：isStableUn
derBaseChange (hP : RingHom.IsStableUnderBaseChange Q) : P.IsStableUnderBaseChan
ge
· 使用定理 `AlgebraicGeometry.Flat.instHasRingHomPropertyFlat`：AlgebraicGeometry.Has
RingHomProperty @AlgebraicGeometry.Flat fun {R S} [CommRing R] [CommRing S] => R
ingHom.Flat
· 使用引理 `RingHom.Flat.isStableUnderBaseChange`：isStableUnderBaseChange : IsStable
UnderBaseChange Flat
-/
instance isStableUnderBaseChange : MorphismProperty.IsStableUnderBaseChange @Flat :=
  HasRingHomProperty.isStableUnderBaseChange RingHom.Flat.isStableUnderBaseChange

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.Flat.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Flat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (f : X ⟶ Z) (g : Y ⟶ Z) [Flat g] : Flat (pullback.fst f g) :=
  MorphismProperty.pullback_fst _ _ inferInstance

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.Flat.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Flat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (f : X ⟶ Z) (g : Y ⟶ Z) [Flat f] : Flat (pullback.snd f g) :=
  MorphismProperty.pullback_snd _ _ inferInstance

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.Flat.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Flat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (f : X ⟶ Y) (V : Y.Opens) [Flat f] : Flat (f ∣_ V) :=
  IsZariskiLocalAtTarget.restrict ‹_› V
/-
**AlgebraicGeometry.Flat.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Flat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (f : X ⟶ Y) (U : X.Opens) (V : Y.Opens) (e) [Flat f] : Flat (f.resLE V U e) := by
  delta Scheme.Hom.resLE; infer_instance
/-
**AlgebraicGeometry.Flat.of_stalkMap** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometr
y.Flat`。
形式化陈述：of_stalkMap (H : forall x, (f.stalkMap x).hom.Flat) : Flat f
参数：H : forall x, (f.stalkMap x).hom.Flat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.HasRingHomProperty.of_stalkMap`：of_stalkMap (hQ : OfLo
calizationPrime Q) (H : forall x, Q (f.stalkMap x).hom) : P f
· 使用定理 `AlgebraicGeometry.Flat.instHasRingHomPropertyFlat`：AlgebraicGeometry.Has
RingHomProperty @AlgebraicGeometry.Flat fun {R S} [CommRing R] [CommRing S] => R
ingHom.Flat
· 使用引理 `RingHom.Flat.ofLocalizationPrime`：ofLocalizationPrime : OfLocalizationPr
ime Flat
-/
lemma of_stalkMap (H : ∀ x, (f.stalkMap x).hom.Flat) : Flat f :=
  HasRingHomProperty.of_stalkMap RingHom.Flat.ofLocalizationPrime H
/-
**AlgebraicGeometry.Flat.stalkMap** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry.F
lat`。
形式化陈述：stalkMap [Flat f] (x : X) : (f.stalkMap x).hom.Flat
参数：x : X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.HasRingHomProperty.stalkMap`：stalkMap (hQ : forall {R 
S : Type u} [CommRing R] [CommRing S] (f : R ->+* S) (_ : Q f) (J : Ideal S) (_ 
: J.IsPrime), Q (Localization.local…
· 使用定理 `AlgebraicGeometry.Flat.instHasRingHomPropertyFlat`：AlgebraicGeometry.Has
RingHomProperty @AlgebraicGeometry.Flat fun {R S} [CommRing R] [CommRing S] => R
ingHom.Flat
· 使用引理 `RingHom.Flat.localRingHom`：localRingHom {f : R ->+* S} (hf : f.Flat) (P 
: Ideal S) [P.IsPrime] (Q : Ideal R) [Q.IsPrime] (hQP : Q = Ideal.comap f P) : (
Localization.lo…
· 使用定理 `Ideal.IsPrime.comap`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst : 
Semiring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S] (f : F)   {K : Ideal 
S} [inst_…
-/
lemma stalkMap [Flat f] (x : X) : (f.stalkMap x).hom.Flat :=
  HasRingHomProperty.stalkMap (P := @Flat)
    (fun f hf J hJ ↦ hf.localRingHom J (J.comap f) rfl) ‹_› x
/-
**AlgebraicGeometry.Flat.iff_flat_stalkMap** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicG
eometry.Flat`。
形式化陈述：iff_flat_stalkMap : Flat f ↔ forall x, (f.stalkMap x).hom.Flat
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.Flat.stalkMap`：stalkMap [Flat f] (x : X) : (f.stalkMap
 x).hom.Flat
· 使用引理 `AlgebraicGeometry.Flat.of_stalkMap`：of_stalkMap (H : forall x, (f.stalkM
ap x).hom.Flat) : Flat f
-/
lemma iff_flat_stalkMap : Flat f ↔ ∀ x, (f.stalkMap x).hom.Flat :=
  ⟨fun _ ↦ stalkMap f, fun H ↦ of_stalkMap f H⟩

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.Flat.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Flat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X : Scheme.{u}} {ι : Type v} [Small.{u} ι] {Y : ι → Scheme.{u}} {f : ∀ i, Y i ⟶ X}
    [∀ i, Flat (f i)] : Flat (Sigma.desc f) :=
  IsZariskiLocalAtSource.sigmaDesc (fun _ ↦ inferInstance)

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.Flat.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Flat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := low) [Subsingleton Y] [IsIntegral Y] : Flat f := by
  refine (MorphismProperty.cancel_right_of_respectsIso @Flat _ Y.isoSpec.hom).mp ?_
  refine (IsZariskiLocalAtSource.iff_of_openCover X.affineCover).mpr fun i ↦ ?_
  rw [← Spec.map_preimage (X.affineCover.f i ≫ f ≫ Y.isoSpec.hom),
    HasRingHomProperty.Spec_iff (P := @Flat)]
  exact .of_isField (isField_of_isIntegral_of_subsingleton _) _

/-- A surjective, quasi-compact, flat morphism is a quotient map. -/
@[stacks 02JY]
/-
**AlgebraicGeometry.Flat.isQuotientMap_of_surjective** 是 Mathlib 中的一个引理，位于命名空间 `
AlgebraicGeometry.Flat`。
形式化陈述：isQuotientMap_of_surjective {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [Quasi
Compact f] [Surjective f] : Topology.IsQuotientMap f
参数：f : X ⟶ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Topology.isQuotientMap_iff`：∀ {X : Type u_3} {Y : Type u_4} [inst : Topo
logicalSpace X] [inst_1 : TopologicalSpace Y] (f : X → Y),   Topology.IsQuotient
Map f ↔ Topology…
· 使用定理 `Topology.IsCoinducing.of_isOpen_preimage_iff_isOpen`：∀ {X : Type u_1} {Y
 : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace 
Y],   (∀ (s : Set Y), IsOpen (f ⁻¹' s) ↔ …
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `AlgebraicGeometry.Spec.map_surjective`：∀ {R S : CommRingCat}, Function.S
urjective AlgebraicGeometry.Spec.map
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Topology.IsCoinducing.isOpen_preimage`：∀ {X : Type u_1} {Y : Type u_2} {
f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology
.IsCoinducing f → ∀ {s : Se…
· 使用定理 `Topology.IsQuotientMap.isCoinducing`：∀ {X : Type u_3} {Y : Type u_4} [in
st : TopologicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   Topology.I
sQuotientMap f → Topology…
· 使用引理 `PrimeSpectrum.isQuotientMap_of_generalizingMap`：isQuotientMap_of_general
izingMap (h₂ : GeneralizingMap (comap f)) : Topology.IsQuotientMap (comap f)
· 使用定理 `AlgebraicGeometry.surjective_iff`：∀ {X Y : AlgebraicGeometry.Scheme} (f 
: X ⟶ Y), AlgebraicGeometry.Surjective f ↔ Function.Surjective ⇑f
· 使用引理 `RingHom.Flat.generalizingMap_comap`：generalizingMap_comap {f : R ->+* S}
 (hf : f.Flat) : GeneralizingMap (comap f)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.HasRingHomProperty.Spec_iff`：Spec_iff {R S : CommRingC
at.{u}} {φ : R ⟶ S} : P (Spec.map φ) ↔ Q φ.hom
· 使用定理 `AlgebraicGeometry.Flat.instHasRingHomPropertyFlat`：AlgebraicGeometry.Has
RingHomProperty @AlgebraicGeometry.Flat fun {R S} [CommRing R] [CommRing S] => R
ingHom.Flat
· 使用定理 `AlgebraicGeometry.QuasiCompact.compactSpace_of_compactSpace`：∀ {X Y : Al
gebraicGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.QuasiCompact f] [CompactS
pace ↥Y], CompactSpace ↥X
· 使用定理 `AlgebraicGeometry.Scheme.compactSpace_of_isAffine`：∀ (X : AlgebraicGeome
try.Scheme) [AlgebraicGeometry.IsAffine X], CompactSpace ↥X
· 使用定理 `AlgebraicGeometry.Scheme.IsLocallyDirected.instHasColimit`：∀ {J : Type w
} [inst : CategoryTheory.Category.{v, w} J] (F : CategoryTheory.Functor J Algebr
aicGeometry.Scheme)   [∀ {i j : J} (f : i ⟶ j),…
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.of_isIso`：∀ {Y Z : AlgebraicGeometry.S
cheme} (g : Y ⟶ Z) [CategoryTheory.IsIso g], AlgebraicGeometry.IsOpenImmersion g
· 使用定理 `CategoryTheory.Discrete.instIsIso`：∀ {I : Type u₁} {i j : CategoryTheory
.Discrete I} (f : i ⟶ j), CategoryTheory.IsIso f
· 使用定理 `CategoryTheory.instIsLocallyDirectedDiscrete`：∀ {J : Type u_1} (F : Cate
goryTheory.Functor (CategoryTheory.Discrete J) (Type u_2)), F.IsLocallyDirected
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `AlgebraicGeometry.instIsAffineSigmaObjScheme`：∀ {σ : Type v} (g : σ → Al
gebraicGeometry.Scheme) [inst : Finite σ] [∀ (i : σ), AlgebraicGeometry.IsAffine
 (g i)],   AlgebraicGeometry.IsAff…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `AlgebraicGeometry.instIsAffineXSchemeFiniteSubcover`：∀ (X : AlgebraicGeo
metry.Scheme) [inst : CompactSpace ↥X] (𝒰 : X.OpenCover)   [∀ (i : 𝒰.I₀), Algebr
aicGeometry.IsAffine (𝒰.X i)] (i : 𝒰.fini…
· 使用定理 `AlgebraicGeometry.Scheme.isAffine_affineCover`：∀ (X : AlgebraicGeometry.
Scheme) (i : X.affineCover.I₀), AlgebraicGeometry.IsAffine (X.affineCover.X i)
· 使用定理 `AlgebraicGeometry.Flat.instOfIsOpenImmersion`：∀ {X Y : AlgebraicGeometry
.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.IsOpenImmersion f], AlgebraicGeometry.Fl
at f
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `AlgebraicGeometry.Flat.instDescScheme`：∀ {X : AlgebraicGeometry.Scheme} 
{ι : Type v} [inst : Small.{u, v} ι] {Y : ι → AlgebraicGeometry.Scheme}   {f : (
i : ι) → Y i ⟶ X} [∀ (i : ι…
· 使用定理 `AlgebraicGeometry.Scheme.instIsOpenImmersionF`：∀ {X : AlgebraicGeometry.
Scheme} (𝒰 : X.OpenCover) (i : 𝒰.I₀), AlgebraicGeometry.IsOpenImmersion (𝒰.f i)
（共 55 条，此处仅展示前 30 条）

--- 原说明 ---
A surjective, quasi-compact, flat morphism is a quotient map.
-/
lemma isQuotientMap_of_surjective {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [QuasiCompact f]
    [Surjective f] : Topology.IsQuotientMap f := by
  rw [Topology.isQuotientMap_iff]
  refine ⟨.of_isOpen_preimage_iff_isOpen fun s ↦
    ⟨fun hs ↦ ?_, fun hs ↦ hs.preimage f.continuous⟩, f.surjective⟩
  wlog hY : ∃ R, Y = Spec R
  · let 𝒰 := Y.affineCover
    rw [𝒰.isOpenCover_opensRange.isOpen_iff_inter]
    intro i
    rw [Scheme.Hom.coe_opensRange, ← Set.image_preimage_eq_inter_range]
    apply (𝒰.f i).isOpenEmbedding.isOpenMap
    refine this (f := pullback.fst (𝒰.f i) f) _ ?_ ⟨_, rfl⟩
    rw [← Set.preimage_comp, ← TopCat.coe_comp, ← Scheme.Hom.comp_base, pullback.condition,
      Scheme.Hom.comp_base, TopCat.coe_comp, Set.preimage_comp]
    exact hs.preimage (Scheme.Hom.continuous _)
  obtain ⟨R, rfl⟩ := hY
  wlog hX : ∃ S, X = Spec S
  · have _ : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
    let 𝒰 := X.affineCover.finiteSubcover
    let p : ∐ (fun i : 𝒰.I₀ ↦ 𝒰.X i) ⟶ X := Sigma.desc (fun i ↦ 𝒰.f i)
    refine this (f := (∐ (fun i : 𝒰.I₀ ↦ 𝒰.X i)).isoSpec.inv ≫ p ≫ f) _ _ ?_ ⟨_, rfl⟩
    rw [← Category.assoc, Scheme.Hom.comp_base, TopCat.coe_comp, Set.preimage_comp]
    exact hs.preimage (_ ≫ p).continuous
  obtain ⟨S, rfl⟩ := hX
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  refine ((PrimeSpectrum.isQuotientMap_of_generalizingMap ?_ ?_).isOpen_preimage).mp hs
  · exact (surjective_iff (Spec.map φ)).mp inferInstance
  · apply RingHom.Flat.generalizingMap_comap
    rwa [← HasRingHomProperty.Spec_iff (P := @Flat)]

set_option backward.isDefEq.respectTransparency.types false in
/-- A flat surjective morphism of schemes is an epimorphism in the category of schemes. -/
@[stacks 02VW]
/-
**AlgebraicGeometry.Flat.epi_of_flat_of_surjective** 是 Mathlib 中的一个引理，位于命名空间 `Al
gebraicGeometry.Flat`。
形式化陈述：epi_of_flat_of_surjective (f : X ⟶ Y) [Flat f] [Surjective f] : Epi f
参数：f : X ⟶ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.epi_of_epi_map`：epi_of_epi_map (F : C ⥤ D) [Refle
ctsEpimorphisms F] {X Y : C} {f : X ⟶ Y} (h : Epi (F.map f)) : Epi f
· 使用定理 `CategoryTheory.reflectsEpimorphisms_of_reflectsColimitsOfShape`：∀ {C : T
ype u₁} {D : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.ReflectsFiniteColimits.reflects`：∀ {C : Type u₁} {
inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheor
y.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.instReflectsFiniteColimitsOfReflectsColimits`：∀ {C
 : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : 
CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `AlgebraicGeometry.Scheme.instFullLocallyRingedSpaceForgetToLocallyRinged
Space`：AlgebraicGeometry.Scheme.forgetToLocallyRingedSpace.Full
· 使用定理 `AlgebraicGeometry.Scheme.instFaithfulLocallyRingedSpaceForgetToLocallyRi
ngedSpace`：AlgebraicGeometry.Scheme.forgetToLocallyRingedSpace.Faithful
· 使用定理 `AlgebraicGeometry.LocallyRingedSpace.instReflectsIsomorphismsSheafedSpac
eCommRingCatForgetToSheafedSpace`：AlgebraicGeometry.LocallyRingedSpace.forgetToS
heafedSpace.ReflectsIsomorphisms
· 使用定理 `CategoryTheory.Limits.hasFiniteColimits_of_hasColimits`：∀ (C : Type u) [
inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasColimits C], 
  CategoryTheory.Limits.HasFiniteColimits C
· 使用定理 `AlgebraicGeometry.LocallyRingedSpace.instHasColimits`：CategoryTheory.Lim
its.HasColimits AlgebraicGeometry.LocallyRingedSpace
· 使用定理 `CategoryTheory.Limits.PreservesColimits.preservesFiniteColimits`：∀ {C : 
Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用引理 `AlgebraicGeometry.SheafedSpace.epi_of_base_surjective_of_stalk_mono`：epi
_of_base_surjective_of_stalk_mono {X Y : SheafedSpace C} (f : X ⟶ Y) (h₁ : Funct
ion.Surjective f.hom.base) (h₂ : forall x, Mono (f.hom.st…
· 使用定理 `AlgebraicGeometry.Surjective.surj`：∀ {X Y : AlgebraicGeometry.Scheme} {f
 : X ⟶ Y} [self : AlgebraicGeometry.Surjective f], Function.Surjective ⇑f
· 使用定理 `CategoryTheory.ConcreteCategory.mono_of_injective`：mono_of_injective {X 
Y : C} (f : X ⟶ Y) (i : Function.Injective f) : Mono f
· 使用引理 `Module.FaithfullyFlat.of_flat_of_isLocalHom`：Module.FaithfullyFlat.of_fl
at_of_isLocalHom [IsLocalRing A] [IsLocalRing B] [Flat A B] [IsLocalHom (algebra
Map A B)] : Module.FaithfullyFlat…
· 使用定理 `AlgebraicGeometry.LocallyRingedSpace.instIsLocalRingCarrierStalkCommRing
CatPresheaf`：∀ (X : AlgebraicGeometry.LocallyRingedSpace) (x : ↑X.toTopCat), IsL
ocalRing ↑(X.presheaf.stalk x)
· 使用引理 `AlgebraicGeometry.Flat.stalkMap`：stalkMap [Flat f] (x : X) : (f.stalkMap
 x).hom.Flat
· 使用定理 `AlgebraicGeometry.LocallyRingedSpace.Hom.prop`：∀ {X Y : AlgebraicGeometr
y.LocallyRingedSpace} (self : X.Hom Y) (x : ↑↑X.toPresheafedSpace),   IsLocalHom
 (CommRingCat.Hom.hom (self.stalkMa…
· 使用引理 `RingHom.FaithfullyFlat.injective`：injective (hf : f.FaithfullyFlat) : Fu
nction.Injective ⇑f

--- 原说明 ---
A flat surjective morphism of schemes is an epimorphism in the category of schem
es.
-/
lemma epi_of_flat_of_surjective (f : X ⟶ Y) [Flat f] [Surjective f] : Epi f := by
  apply CategoryTheory.Functor.epi_of_epi_map (Scheme.forgetToLocallyRingedSpace)
  apply CategoryTheory.Functor.epi_of_epi_map (LocallyRingedSpace.forgetToSheafedSpace)
  apply SheafedSpace.epi_of_base_surjective_of_stalk_mono _ ‹Surjective f›.surj
  intro x
  apply ConcreteCategory.mono_of_injective
  algebraize [(f.stalkMap x).hom]
  have : Module.FaithfullyFlat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _
      (Flat.stalkMap f x) (f.toLRSHom.prop x)
  exact ‹RingHom.FaithfullyFlat _›.injective

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine** 是 
Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry.Flat`。
形式化陈述：flat_and_surjective_iff_faithfullyFlat_of_isAffine [IsAffine X] [IsAffine 
Y] : Flat f ∧ Surjective f ↔ f.appTop.hom.FaithfullyFlat
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RingHom.FaithfullyFlat.iff_flat_and_comap_surjective`：iff_flat_and_comap
_surjective : f.FaithfullyFlat ↔ f.Flat ∧ Function.Surjective (PrimeSpectrum.com
ap f)
· 使用定理 `CategoryTheory.MorphismProperty.arrow_mk_iso_iff`：arrow_mk_iso_iff (P : 
MorphismProperty C) [RespectsIso P] {W X Y Z : C} {f : W ⟶ X} {g : Y ⟶ Z} (e : A
rrow.mk f ≅ Arrow.mk g) : P f ↔ P g
· 使用定理 `AlgebraicGeometry.instRespectsIsoSchemeSurjective`：CategoryTheory.Morphi
smProperty.RespectsIso @AlgebraicGeometry.Surjective
· 使用定理 `CategoryTheory.MorphismProperty.IsLocalAtSource.toRespects`：∀ {C : Type 
u} {inst : CategoryTheory.Category.{v, u} C} {P : CategoryTheory.MorphismPropert
y C}   (K : CategoryTheory.Precoverage C) [self …
· 使用定理 `AlgebraicGeometry.HasRingHomProperty.instIsZariskiLocalAtSource`：∀ {P : 
CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme}   {Q : {R S : Type u} 
→ [inst : CommRing R] → [inst_1 : CommRing S] → (R →+…
· 使用定理 `AlgebraicGeometry.Flat.instHasRingHomPropertyFlat`：AlgebraicGeometry.Has
RingHomProperty @AlgebraicGeometry.Flat fun {R S} [CommRing R] [CommRing S] => R
ingHom.Flat
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.HasRingHomProperty.Spec_iff`：Spec_iff {R S : CommRingC
at.{u}} {φ : R ⟶ S} : P (Spec.map φ) ↔ Q φ.hom
· 使用定理 `AlgebraicGeometry.surjective_iff`：∀ {X Y : AlgebraicGeometry.Scheme} (f 
: X ⟶ Y), AlgebraicGeometry.Surjective f ↔ Function.Surjective ⇑f
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma flat_and_surjective_iff_faithfullyFlat_of_isAffine [IsAffine X] [IsAffine Y] :
    Flat f ∧ Surjective f ↔ f.appTop.hom.FaithfullyFlat := by
  rw [RingHom.FaithfullyFlat.iff_flat_and_comap_surjective,
    MorphismProperty.arrow_mk_iso_iff @Surjective (arrowIsoSpecΓOfIsAffine f),
    MorphismProperty.arrow_mk_iso_iff @Flat (arrowIsoSpecΓOfIsAffine f),
    ← HasRingHomProperty.Spec_iff (P := @Flat), surjective_iff]
  rfl

end Flat

/-
**AlgebraicGeometry.Scheme.Hom.flat_appTop** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicG
eometry.Scheme.Hom`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.IsAffine
 X] [AlgebraicGeometry.IsAffine Y]   [AlgebraicGeometry.Flat f], (CommRingCat.Ho
m.hom (AlgebraicGeometry.Scheme.Hom.appTop f)).Flat
参数：f : X ⟶ Y；CommRingCat.Hom.hom (AlgebraicGeometry.Scheme.Hom.appTop f)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.HasRingHomProperty.appTop`：appTop (H : P f) [IsAffine 
X] [IsAffine Y] : Q f.appTop.hom
· 使用定理 `AlgebraicGeometry.Flat.instHasRingHomPropertyFlat`：AlgebraicGeometry.Has
RingHomProperty @AlgebraicGeometry.Flat fun {R S} [CommRing R] [CommRing S] => R
ingHom.Flat
-/
lemma Scheme.Hom.flat_appTop [IsAffine X] [IsAffine Y] [Flat f] :
    f.appTop.hom.Flat :=
  HasRingHomProperty.appTop (P := @Flat) _ inferInstance
/-
**AlgebraicGeometry.flat_and_surjective_SpecMap_iff** 是 Mathlib 中的一个引理，位于命名空间 `A
lgebraicGeometry`。
形式化陈述：flat_and_surjective_SpecMap_iff {R S : CommRingCat.{u}} (f : R ⟶ S) : Flat
 (Spec.map f) ∧ Surjective (Spec.map f) ↔ f.hom.FaithfullyFlat
参数：f : R ⟶ S。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.HasRingHomProperty.Spec_iff`：Spec_iff {R S : CommRingC
at.{u}} {φ : R ⟶ S} : P (Spec.map φ) ↔ Q φ.hom
· 使用定理 `AlgebraicGeometry.Flat.instHasRingHomPropertyFlat`：AlgebraicGeometry.Has
RingHomProperty @AlgebraicGeometry.Flat fun {R S} [CommRing R] [CommRing S] => R
ingHom.Flat
· 使用引理 `RingHom.FaithfullyFlat.iff_flat_and_comap_surjective`：iff_flat_and_comap
_surjective : f.FaithfullyFlat ↔ f.Flat ∧ Function.Surjective (PrimeSpectrum.com
ap f)
· 使用定理 `AlgebraicGeometry.surjective_iff`：∀ {X Y : AlgebraicGeometry.Scheme} (f 
: X ⟶ Y), AlgebraicGeometry.Surjective f ↔ Function.Surjective ⇑f
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma flat_and_surjective_SpecMap_iff {R S : CommRingCat.{u}} (f : R ⟶ S) :
    Flat (Spec.map f) ∧ Surjective (Spec.map f) ↔ f.hom.FaithfullyFlat := by
  rw [HasRingHomProperty.Spec_iff (P := @Flat),
    RingHom.FaithfullyFlat.iff_flat_and_comap_surjective, surjective_iff]
  rfl

section sections

/-!
## Sections of fibered products

Suppose we are given the following cartesian square:
```
Y --g-→ X
|       |
iY      iX
↓       |
T --f-→ S
```
Let `Uₛ` be an open of `S`, `Uₓ` and `Uₜ` be opens of `X` and `T` mapping into `Uₛ`.
There is a canonical map `Γ(X, Uₓ) ⊗[Γ(S, Uₛ)] Γ(T, Uₜ) ⟶ Γ(X ×ₛ T, pr₁ ⁻¹ Uₓ ∩ pr₂ ⁻¹ Uₜ)`.

We show that this map is
1. `isIso_pushoutSection_of_isAffineOpen`:
  bijective when `Uₛ`, `Uₜ`, and `Uₓ` are all affine.
2. `mono_pushoutSection_of_isCompact_of_flat_right`:
  injective when `Uₛ`, `Uₜ` are affine, `Uₓ` is compact, and `f` is flat.
3. `isIso_pushoutSection_of_isQuasiSeparated_of_flat_right`:
  bijective when `Uₛ`, `Uₜ` are affine, `Uₓ` is qcqs, and `f` is flat.
4. `mono_pushoutSection_of_isCompact_of_flat_right_of_ringHomFlat`:
  injective when `Uₛ` is affine, `Uₜ` is compact, `Uₓ` is qcqs, `f` is flat,
  and `Γ(T, Uₜ)` is flat over `Γ(S, Uₛ)` (typically true when `S = Spec k`.)
5. `isIso_pushoutSection_of_isCompact_of_flat_right_of_ringHomFlat`:
  bijective when `Uₛ` is affine, `Uₜ` and `Uₓ` are qcqs, `f` is flat,
  and `Γ(T, Uₜ)` is flat over `Γ(S, Uₛ)` (typically true when `S = Spec k`.)

-/

variable {X Y S T : Scheme.{u}} {f : T ⟶ S} {g : Y ⟶ X} {iX : X ⟶ S} {iY : Y ⟶ T}
  (H : IsPullback g iY iX f)
  {US : S.Opens} {UT : T.Opens}
  {UX : X.Opens} (hUST : UT ≤ f ⁻¹ᵁ US) (hUSX : UX ≤ iX ⁻¹ᵁ US)
  {UY : Y.Opens} (hUY : UY = g ⁻¹ᵁ UX ⊓ iY ⁻¹ᵁ UT)

/-- The canonical map `Γ(X, Uₓ) ⊗[Γ(S, Uₛ)] Γ(T, Uₜ) ⟶ Γ(X ×ₛ T, pr₁ ⁻¹ Uₓ ∩ pr₂ ⁻¹ Uₜ)`.
This is an isomorphism under various circumstances. -/
/-
**AlgebraicGeometry.pushoutSection** 是 Mathlib 中的一个缩写定义，位于命名空间 `AlgebraicGeometr
y`。
形式化陈述：pushoutSection : pushout (iX.appLE US UX hUSX) (f.appLE US UT hUST) ⟶ Γ(Y,
 UY)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical map `Γ(X, Uₓ) ⊗[Γ(S, Uₛ)] Γ(T, Uₜ) ⟶ Γ(X ×ₛ T, pr₁ ⁻¹ Uₓ ∩ pr₂ ⁻¹ 
Uₜ)`.
This is an isomorphism under various circumstances.
-/
abbrev pushoutSection : pushout (iX.appLE US UX hUSX) (f.appLE US UT hUST) ⟶ Γ(Y, UY) :=
  pushout.desc (g.appLE UX UY (by simp [*])) (iY.appLE UT UY (by simp [*]))
    (by simp only [Scheme.Hom.appLE_comp_appLE, H.w])

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.isIso_pushoutSection_iff** 是 Mathlib 中的一个引理，位于命名空间 `Algebrai
cGeometry`。
形式化陈述：isIso_pushoutSection_iff : IsIso (pushoutSection H hUST hUSX hUY) ↔ IsPush
out (iX.appLE US UX hUSX) (f.appLE US UT hUST) (g.appLE UX UY (by simp [*])) (iY
.appLE UT UY (by simp [*]))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePushouts_of_has_finite_limits`：∀ (C :
 Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFin
iteColimits C],   CategoryTheory.Limits.HasFiniteWideP…
· 使用定理 `CategoryTheory.Limits.hasFiniteColimits_of_hasColimits`：∀ (C : Type u) [
inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasColimits C], 
  CategoryTheory.Limits.HasFiniteColimits C
· 使用引理 `CategoryTheory.IsPushout.of_iso`：of_iso (h : IsPushout f g inl inr) {Z' 
X' Y' P' : C} {f' : Z' ⟶ X'} {g' : Z' ⟶ Y'} {inl' : X' ⟶ P'} {inr' : Y' ⟶ P'} (e
₁ : Z ≅ Z') (e₂ : X ≅…
· 使用定理 `CategoryTheory.IsPushout.of_hasPushout`：of_hasPushout (f : Z ⟶ X) (g : Z
 ⟶ Y) [HasPushout f g] : IsPushout f g (pushout.inl f g) (pushout.inr f g)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PushoutCocone.mk_ι_app`：∀ {C : Type u} [inst : Cat
egoryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} {W : C} (inl 
: Y ⟶ W)   (inr : Z ⟶ W) (eq : Cat…
-/
lemma isIso_pushoutSection_iff :
    IsIso (pushoutSection H hUST hUSX hUY) ↔ IsPushout (iX.appLE US UX hUSX) (f.appLE US UT hUST)
      (g.appLE UX UY (by simp [*])) (iY.appLE UT UY (by simp [*])) :=
  ⟨fun _ ↦ .of_iso (.of_hasPushout _ _) (.refl _) (.refl _) (.refl _)
    (asIso (pushoutSection H hUST hUSX hUY)) (by simp) (by simp) (by simp) (by simp),
    fun h ↦ inferInstanceAs (IsIso h.isoPushout.inv)⟩

set_option backward.defeqAttrib.useBackward true in
attribute [local simp] IsAffineOpen.isoSpec_hom in
attribute [local simp← ] Scheme.Hom.resLE_eq_morphismRestrict in
/-
**AlgebraicGeometry.isIso_pushoutSection_of_isAffineOpen** 是 Mathlib 中的一个引理，位于命名
空间 `AlgebraicGeometry`。
形式化陈述：isIso_pushoutSection_of_isAffineOpen (hUS : IsAffineOpen US) (hUT : IsAffi
neOpen UT) (hUX : IsAffineOpen UX) : IsIso (pushoutSection H hUST hUSX hUY)
参数：hUS : IsAffineOpen US；hUT : IsAffineOpen UT；hUX : IsAffineOpen UX。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePushouts_of_has_finite_limits`：∀ (C :
 Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFin
iteColimits C],   CategoryTheory.Limits.HasFiniteWideP…
· 使用定理 `CategoryTheory.Limits.hasFiniteColimits_of_hasColimits`：∀ (C : Type u) [
inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasColimits C], 
  CategoryTheory.Limits.HasFiniteColimits C
· 使用引理 `AlgebraicGeometry.isIso_pushoutSection_iff`：isIso_pushoutSection_iff : I
sIso (pushoutSection H hUST hUSX hUY) ↔ IsPushout (iX.appLE US UX hUSX) (f.appLE
 US UT hUST) (g.appLE UX UY (by …
· 使用定理 `CategoryTheory.IsPullback.unop`：unop {P X Y Z : Cᵒᵖ} {fst : P ⟶ X} {snd 
: P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback fst snd f g) : IsPushout g.unop
 f.unop snd.unop fst…
· 使用定理 `CategoryTheory.IsPullback.of_map_of_faithful`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Categor
y.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.reflectsLimit_of_reflectsLimitsOfShape`：∀ {C : Typ
e u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Catego
ryTheory.Category.{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `CategoryTheory.Limits.ReflectsFiniteLimits.reflects`：∀ {C : Type u₁} {in
st : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.
Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.reflectsIsomorphisms_of_full_and_faithful`：∀ {C : Type u_
1} [inst : CategoryTheory.Category.{v_1, u_1} C] {D : Type u_2}   [inst_1 : Cate
goryTheory.Category.{v_2, u_2} D] (F : Categor…
· 使用定理 `AlgebraicGeometry.Spec.full`：AlgebraicGeometry.Scheme.Spec.Full
· 使用定理 `AlgebraicGeometry.Spec.faithful`：AlgebraicGeometry.Scheme.Spec.Faithful
· 使用定理 `CategoryTheory.Limits.PreservesLimits.preservesFiniteLimits`：∀ {C : Type
 u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Categor
yTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.instPreservesLimitsOfSizeOfIsRightAdjoint`：∀ {C :
 Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_2, u_2} C]   [inst_
1 : CategoryTheory.Category.{v_3, u_3} D] (F : Categor…
· 使用定理 `CategoryTheory.instIsRightAdjointOfMonadicRightAdjoint`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} D]   (R : CategoryTheor…
· 使用定理 `AlgebraicGeometry.IsAffine.of_isIso`：∀ {X Y : AlgebraicGeometry.Scheme} 
(f : X ⟶ Y) [CategoryTheory.IsIso f] [h : AlgebraicGeometry.IsAffine Y],   Algeb
raicGeometry.IsAffine X
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `AlgebraicGeometry.Scheme.Hom.isPullback_resLE`：∀ {X Y S T : AlgebraicGeo
metry.Scheme} {f : T ⟶ S} {g : Y ⟶ X} {iX : X ⟶ S} {iY : Y ⟶ T},   CategoryTheor
y.IsPullback g iY iX f →     ∀ {US …
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `AlgebraicGeometry.instIsAffinePullbackSchemeOfIsAffineHom_1`：∀ {X Y S : 
AlgebraicGeometry.Scheme} (f : X ⟶ S) (g : Y ⟶ S) [AlgebraicGeometry.IsAffineHom
 g]   [AlgebraicGeometry.IsAffine X], AlgebraicGe…
· 使用定理 `AlgebraicGeometry.isAffineHom_of_isAffine`：∀ {X Y : AlgebraicGeometry.Sc
heme} (f : X ⟶ Y) [AlgebraicGeometry.IsAffine X] [AlgebraicGeometry.IsAffine Y],
   AlgebraicGeometry.IsAffineHo…
· 使用引理 `CategoryTheory.IsPullback.of_iso`：of_iso (h : IsPullback fst snd f g) {P
' X' Y' Z' : C} {fst' : P' ⟶ X'} {snd' : P' ⟶ Y'} {f' : X' ⟶ Z'} {g' : Y' ⟶ Z'} 
(e₁ : P ≅ P') (e₂ : X …
· 使用定理 `CategoryTheory.IsPullback.flip`：flip (h : IsPullback fst snd f g) : IsPu
llback snd fst g f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Spec.map_comp`：∀ {R S T : CommRingCat} (f : R ⟶ S) (g 
: S ⟶ T),   AlgebraicGeometry.Spec.map (CategoryTheory.CategoryStruct.comp f g) 
=     CategoryTheory.…
（共 35 条，此处仅展示前 30 条）
-/
lemma isIso_pushoutSection_of_isAffineOpen (hUS : IsAffineOpen US) (hUT : IsAffineOpen UT)
    (hUX : IsAffineOpen UX) : IsIso (pushoutSection H hUST hUSX hUY) := by
  refine (isIso_pushoutSection_iff ..).mpr (IsPullback.of_map_of_faithful Scheme.Spec ?_).unop
  have : IsAffine _ := hUS
  have : IsAffine _ := hUT
  have : IsAffine _ := hUX
  have hUY' : IsAffineOpen UY :=
    .of_isIso (Scheme.Hom.isPullback_resLE H hUST hUSX hUY).isoPullback.hom
  exact .of_iso (Scheme.Hom.isPullback_resLE H hUST hUSX hUY).flip hUY'.isoSpec hUT.isoSpec
    hUX.isoSpec hUS.isoSpec (by simp) (by simp) (by simp) (by simp)

set_option backward.isDefEq.respectTransparency false in
open TensorProduct in
/-
**AlgebraicGeometry.mono_pushoutSection_of_iSup_eq** 是 Mathlib 中的一个引理，位于命名空间 `Al
gebraicGeometry`。
形式化陈述：mono_pushoutSection_of_iSup_eq {ι : Type*} [Finite ι] (VX : ι -> X.Opens) 
(hVU : iSup VX = UX) (hV : forall i, Mono (pushoutSection H hUST (show VX i <= _
 by aesop) rfl)) (hT : (f.appLE US UT hUST).hom.Flat) : Mono (pushoutSection H h
UST hUSX hUY)
参数：VX : ι -> X.Opens；hVU : iSup VX = UX；hV : forall i, Mono (pushoutSection H hU
ST (show VX i <= _ by aesop) rfl)；hT : (f.appLE US UT hUST).hom.Flat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePushouts_of_has_finite_limits`：∀ (C :
 Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFin
iteColimits C],   CategoryTheory.Limits.HasFiniteWideP…
· 使用定理 `CategoryTheory.Limits.hasFiniteColimits_of_hasColimits`：∀ (C : Type u) [
inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasColimits C], 
  CategoryTheory.Limits.HasFiniteColimits C
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `inf_le_inf`：∀ {α : Type u} [inst : SemilatticeInf α] {a b c d : α}, b ≤ 
a → d ≤ c → b ⊓ d ≤ a ⊓ c
· 使用引理 `AlgebraicGeometry.Scheme.Hom.preimage_mono`：preimage_mono {U U' : Y.Open
s} (hUU' : U <= U') : f ⁻¹ᵁ U <= f ⁻¹ᵁ U'
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.Scheme.Hom.appLE_map`：appLE_map (e : V <= f ⁻¹ᵁ U) (i 
: op V ⟶ op V') : f.appLE U V e ≫ X.presheaf.map i = f.appLE U V' (i.unop.le.tra
ns e)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `TopCat.Presheaf.IsSheaf.section_ext`：∀ {X : TopCat} {A : Type u_1} [inst
 : CategoryTheory.Category.{u, u_1} A] {FC : A → A → Type u_2} {CC : A → Type u}
   [inst_1 : (X Y : A) → …
· 使用定理 `AlgebraicGeometry.SheafedSpace.IsSheaf`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] (self : AlgebraicGeometry.SheafedSpace C),   self.presh
eaf.IsSheaf
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Module.Flat.lTensor_preserves_injective_linearMap`：lTensor_preserves_inj
ective_linearMap [Flat R M] (f : N ->ₗ[R] P) (hf : Function.Injective f) : Funct
ion.Injective (f.lTensor M)
· 使用定理 `CategoryTheory.Functor.instPreservesLimitsOfShapeOfIsRightAdjoint`：∀ {J 
: Type u_1} {C : Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_1, 
u_1} J]   [inst_1 : CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `CommRingCat.instIsRightAdjointForgetRingHomCarrier`：(CategoryTheory.forg
et CommRingCat).IsRightAdjoint
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `CategoryTheory.IsPushout.flip`：flip (h : IsPushout f g inl inr) : IsPush
out g f inr inl
· 使用引理 `CommRingCat.isPushout_tensorProduct`：isPushout_tensorProduct (R A B : Ty
pe u) [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] : IsPus
hout (ofHom <| algebraMap…
（共 53 条，此处仅展示前 30 条）
-/
lemma mono_pushoutSection_of_iSup_eq {ι : Type*} [Finite ι] (VX : ι → X.Opens) (hVU : iSup VX = UX)
    (hV : ∀ i, Mono (pushoutSection H hUST (show VX i ≤ _ by aesop) rfl))
    (hT : (f.appLE US UT hUST).hom.Flat) :
    Mono (pushoutSection H hUST hUSX hUY) := by
  /-
  We shall show that `Γ(T, Uₜ) ⊗[Γ(S, Uₛ)] Γ(X, U) ⟶ Γ(X ×ₛ T, pr₁ ⁻¹ U ∩ pr₂ ⁻¹ Uₜ)` is
  injective using the following diagram
  ```
  Γ(T, Uₜ) ⊗ Γ(X, U) ------→ Γ(T, Uₜ) ⊗ ∏ᵢ Γ(X, Vᵢ)
           |                          |
           ↓                          ↓
  Γ(X ×ₛ T, U ∩ Uₜ)  ------→ ∏ᵢ Γ(X ×ₛ T, Vᵢ ∩ Uₜ)
  ```
  -/
  have (i : _) : VX i ≤ iX ⁻¹ᵁ US := by clear hV; aesop
  classical
  algebraize [(iX.appLE US UX hUSX).hom, (f.appLE US UT hUST).hom]
  let (i : _) := (iX.appLE US (VX i) (by aesop)).hom.toAlgebra
  -- This is the map `Γ(X ×ₛ T, U ∩ Uₜ) ⟶ ∏ᵢ Γ(X ×ₛ T, Vᵢ ∩ Uₜ)` on the bottom.
  let ψY : Γ(Y, UY) →+* Π i, Γ(Y, g ⁻¹ᵁ VX i ⊓ iY ⁻¹ᵁ UT) := RingHom.pi fun i ↦
      (Y.presheaf.map (homOfLE (by subst hUY hVU; gcongr; exact le_iSup _ _)).op).hom
  -- The map `Γ(X, U) ⟶ ∏ᵢ Γ(X, Vᵢ)`
  let ψ : Γ(X, UX) →ₐ[Γ(S, US)] Π i, Γ(X, VX i) := AlgHom.pi fun i ↦
    ⟨(X.presheaf.map (homOfLE (hVU ▸ le_iSup VX i)).op).hom, fun r ↦ by
      dsimp [RingHom.algebraMap_toAlgebra]
      simp only [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]⟩
  -- ... is injective by the sheaf axiom,
  have hψ : Function.Injective ψ := by
    intro s t est
    apply X.IsSheaf.section_ext fun x hx ↦ ?_
    simp only [← hVU, Opens.mem_iSup] at hx
    obtain ⟨i, hxi⟩ := hx
    exact ⟨_, _, hxi, congr($est i)⟩
  -- ... and remains injective after tensoring with `Γ(T, Uₜ)` by the flatness assumption.
  have hψ' : Function.Injective (Algebra.TensorProduct.map (AlgHom.id Γ(T, UT) Γ(T, UT)) ψ) :=
    Module.Flat.lTensor_preserves_injective_linearMap ψ.toLinearMap hψ
  simp_rw [@ConcreteCategory.mono_iff_injective_of_preservesPullback] at hV ⊢
  cases nonempty_fintype ι
  -- And the map at the right
  let φ : (Γ(T, UT) ⊗[Γ(S, US)] Π i, Γ(X, VX i)) →+* Π i, Γ(Y, g ⁻¹ᵁ VX i ⊓ iY ⁻¹ᵁ UT) :=
    (RingHom.pi fun i ↦ (pushoutSection H hUST (show VX i ≤ _ by aesop) rfl).hom.comp
      ((CommRingCat.isPushout_tensorProduct _ _ _).flip.isoPushout.hom.hom.comp
      (by exact Pi.evalRingHom _ _))).comp (Algebra.TensorProduct.piRight _ Γ(S, US) _ _).toRingHom
  -- ... is also injective by our hypotheses on `Vᵢ`.
  have hφ : Function.Injective φ := by
    dsimp [φ]
    refine .comp ?_ (Algebra.TensorProduct.piRight _ Γ(S, US) _ _).injective
    exact .piMap fun i ↦ (hV _).comp <| CommRingCat.isPushout_tensorProduct _ _ _
      |>.flip.isoPushout.commRingCatIsoToRingEquiv.injective
  let e : pushout (iX.appLE US UX hUSX) (f.appLE US UT hUST) ≅
      .of (Γ(T, UT) ⊗[Γ(S, US)] Γ(X, UX)) :=
    (CommRingCat.isPushout_tensorProduct _ _ _).flip.isoPushout.symm
  -- It remains to check that the square indeed commutes, and we may conclude that the map
  -- at the left is also injective.
  suffices (ψY.comp (pushoutSection H hUST hUSX hUY).hom).comp e.inv.hom = φ.comp
      (Algebra.TensorProduct.map (AlgHom.id Γ(T, UT) Γ(T, UT)) ψ).toRingHom by
    refine .of_comp (f := ψY) ?_
    convert (hφ.comp hψ').comp e.commRingCatIsoToRingEquiv.injective
    ext1 x; simpa using! congr($this (e.hom x))
  ext1
  · have H₁ : e.inv.hom.comp Algebra.TensorProduct.includeLeftRingHom =
        (pushout.inr (C := CommRingCat) _ _).hom :=
      congr($((CommRingCat.isPushout_tensorProduct _ _ _).flip.inr_isoPushout_hom).hom)
    have H₂ (x j) : φ (x ⊗ₜ[↑Γ(S, US)] 1) j = pushoutSection H hUST (UX := VX j) (by simp_all) rfl
        (pushout.inr (C := CommRingCat) _ _ x) := congr(pushoutSection H hUST (UX := VX j) _ rfl
        ($((CommRingCat.isPushout_tensorProduct ↑Γ(S, US)
          ↑Γ(T, UT) ↑Γ(X, VX j)).flip.inr_isoPushout_hom) x))
    simp only [RingHom.comp_assoc, H₁]
    ext x j
    simp [ψY, H₂, ← CategoryTheory.comp_apply, pushoutSection]
  · have H₁ : e.inv.hom.comp Algebra.TensorProduct.includeRight.toRingHom =
        (pushout.inl (C := CommRingCat) _ _).hom :=
      congr($((CommRingCat.isPushout_tensorProduct _ _ _).flip.inl_isoPushout_hom).hom)
    have H₂ (x j) : φ (1 ⊗ₜ[↑Γ(S, US)] x) j = pushoutSection H hUST (UX := VX j) (by simp_all) rfl
        (pushout.inl (C := CommRingCat) _ _ (x j)) := congr(pushoutSection H hUST (UX := VX j) _ rfl
        ($((CommRingCat.isPushout_tensorProduct ↑Γ(S, US)
          ↑Γ(T, UT) ↑Γ(X, VX j)).flip.inl_isoPushout_hom) (x j)))
    simp only [RingHom.comp_assoc, H₁]
    ext x j
    simp [ψY, H₂, -CommRingCat.hom_comp, ← CategoryTheory.comp_apply, pushoutSection, ψ]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.isIso_pushoutSection_of_iSup_eq** 是 Mathlib 中的一个引理，位于命名空间 `A
lgebraicGeometry`。
形式化陈述：isIso_pushoutSection_of_iSup_eq {ι : Type u} [Finite ι] (VX : ι -> X.Opens
) (hVU : iSup VX = UX) (hV : forall i, IsIso (pushoutSection H hUST (show VX i <
= _ by aesop) rfl)) (hV' : forall i j, Mono (pushoutSection H hUST (show VX i ⊓ 
VX j <= _ from inf_le_left.trans (by clear hV; aesop)) rfl)) (hT : (f.appLE US U
T hUST).hom.Flat) : IsIso (pushoutSection H hUST hUSX hUY)
参数：VX : ι -> X.Opens；hVU : iSup VX = UX；hV : forall i, IsIso (pushoutSection H h
UST (show VX i <= _ by aesop) rfl)；hV' : forall i j, Mono (pushoutSection H hUST
 (show VX i ⊓ VX j <= _ from inf_le_left.trans (by clear hV; aesop)) rfl)；hT : (
f.appLE US UT hUST).hom.Flat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePushouts_of_has_finite_limits`：∀ (C :
 Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFin
iteColimits C],   CategoryTheory.Limits.HasFiniteWideP…
· 使用定理 `CategoryTheory.Limits.hasFiniteColimits_of_hasColimits`：∀ (C : Type u) [
inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasColimits C], 
  CategoryTheory.Limits.HasFiniteColimits C
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `iSup_le_iff`：iSup_le_iff : iSup f <= a ↔ forall i, f i <= a
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
· 使用定理 `CategoryTheory.Limits.instHasColimitsOfShapeOfHasColimitsOfSize`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : Catego
ryTheory.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.CompleteLattice.hasColimits_of_completeLattice`：∀ 
{α : Type u} [inst : CompleteLattice α], CategoryTheory.Limits.HasColimitsOfSize
.{w, w', u, u} α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.CompleteLattice.colimit_eq_iSup`：colimit_eq_iSup (
F : J ⥤ α) : colimit F = iSup F.obj
· 使用定理 `inf_le_inf`：∀ {α : Type u} [inst : SemilatticeInf α] {a b c d : α}, b ≤ 
a → d ≤ c → b ⊓ d ≤ a ⊓ c
· 使用引理 `AlgebraicGeometry.Scheme.Hom.preimage_mono`：preimage_mono {U U' : Y.Open
s} (hUU' : U <= U') : f ⁻¹ᵁ U <= f ⁻¹ᵁ U'
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `AlgebraicGeometry.Scheme.Hom.appLE_map`：appLE_map (e : V <= f ⁻¹ᵁ U) (i 
: op V ⟶ op V') : f.appLE U V e ≫ X.presheaf.map i = f.appLE U V' (i.unop.le.tra
ns e)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.pushout.hom_ext`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}   [inst_1 : Category
Theory.Limits.HasPushout f …
· 使用引理 `CommRingCat.hom_ext`：hom_ext {R S : CommRingCat} {f g : R ⟶ S} (hf : f.h
om = g.hom) : f = g
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc_assoc`：∀ {J : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{
v, u} C]   {F : CategoryTheory.F…
（共 77 条，此处仅展示前 30 条）
-/
lemma isIso_pushoutSection_of_iSup_eq
    {ι : Type u} [Finite ι] (VX : ι → X.Opens) (hVU : iSup VX = UX)
    (hV : ∀ i, IsIso (pushoutSection H hUST (show VX i ≤ _ by aesop) rfl))
    (hV' : ∀ i j, Mono (pushoutSection H hUST
      (show VX i ⊓ VX j ≤ _ from inf_le_left.trans (by clear hV; aesop)) rfl))
    (hT : (f.appLE US UT hUST).hom.Flat) :
    IsIso (pushoutSection H hUST hUSX hUY) := by
  classical
  /-
  We shall show that `Γ(T, Uₜ) ⊗[Γ(S, Uₛ)] Γ(X, U) ⟶ Γ(X ×ₛ T, pr₁ ⁻¹ U ∩ pr₂ ⁻¹ Uₜ)` is
  injective using the following diagram
  ```
  0 → Γ(T, Uₜ) ⊗ Γ(X, U) ------→ Γ(T, Uₜ) ⊗ ∏ᵢ Γ(X, Vᵢ) ---→ Γ(T, Uₜ) ⊗ ∏ᵢⱼ Γ(X, Vᵢ ∩ Vⱼ)
           |                              |                           |
           ↓                              ↓                           ↓
  0 → Γ(X ×ₛ T, U ∩ Uₜ)  ------→ ∏ᵢ Γ(X ×ₛ T, Vᵢ ∩ Uₜ)  ---→ ∏ᵢ Γ(X ×ₛ T, Vᵢ ∩ Vⱼ ∩ Uₜ)
  ```
  The two rows are exact because of the sheaf axiom (and additionally the flatness assumption for
  the top row). The vertical arrow in the middle is an isomorphism by assumption, and the one
  one the right is monomorphic by assumption. Hence the left arrow is also an isomorphism.

  In the actual proof we use `Pairwise`-indexed diagrams instead of nested limits because it works
  better with the existing API.
  -/
  -- The diagram consisting of `Γ(X, Vᵢ) ⟶ Γ(X, Vᵢ ∩ Vⱼ)`.
  let D := Pairwise.diagram VX
  have h : iSup D.obj = UX := by
    refine le_antisymm (iSup_le_iff.mpr ?_) ?_
    · subst hVU; rintro (i | ⟨i, j⟩); exacts [le_iSup VX _, inf_le_left.trans (le_iSup VX _)]
    · subst hVU; exact iSup_le_iff.mpr fun i ↦ le_iSup D.obj (.single i)
  let c₀ : Cocone D := (colimit.cocone _).extend
    (eqToIso (Y := UX) (by simpa [CompleteLattice.colimit_eq_iSup])).hom
  -- The diagram consisting of `Γ(T, Uₜ) ⊗ Γ(X, Vᵢ) ⟶ Γ(T, Uₜ) ⊗ Γ(X, Vᵢ ∩ Vⱼ)`.
  let F := Under.lift _ ((Functor.const _).map (iX.appLE US UX hUSX) ≫
    ((X.presheaf.mapCone c₀.op).π)) ⋙ Under.pushout (f.appLE US UT hUST) ⋙ Under.forget _
  let G : X.Opens ⥤ Y.Opens :=
    { obj U := g ⁻¹ᵁ U ⊓ iY ⁻¹ᵁ UT, map h := homOfLE (by gcongr; exact h.le) }
  -- The natural transformation between the diagrams at the top and bottom.
  let αF : F ⟶ D.op ⋙ G.op ⋙ Y.presheaf :=
  { app i := (pushout.congrHom (by simp) rfl).hom ≫
      pushoutSection H hUST (by grw [← hUSX, ← h]; exact le_iSup D.obj i.unop) rfl }
  -- `Γ(T, Uₜ) ⊗ Γ(X, U)` as a (limit) cone over the top diagram.
  let c : Cone F := (Under.pushout (f.appLE US UT hUST) ⋙ Under.forget _).mapCone
    (Under.liftCone (X.presheaf.mapCone c₀.op) _)
  have := CommRingCat.Under.preservesFiniteLimits_of_flat _ hT
  cases nonempty_fintype ι
  let hc : IsLimit c :=
    haveI HX := ((TopCat.Presheaf.isSheaf_iff_isSheafPreservesLimitPairwiseIntersections
      _).mp X.IsSheaf VX).preserves (c := c₀.op)
    haveI HX := (HX (IsColimit.extendIso _ (colimit.isColimit _)).op).some
    isLimitOfPreserves (Under.pushout _ ⋙ Under.forget _) (Under.isLimitLiftCone _ _ HX)
  let c'₀ : Cocone (D ⋙ G) := (colimit.cocone _).extend
    (eqToIso (Y := UY) (by
      simp only [colimit.cocone_x, CompleteLattice.colimit_eq_iSup]
      eta_expand
      dsimp [G]
      rw [← iSup_inf_eq, ← Scheme.Hom.preimage_iSup, h, hUY])).hom
  -- `Γ(X ×ₛ T, U ∩ Uₜ)` as a (limit) cone over the bottom diagram.
  let c' : Cone (D.op ⋙ G.op ⋙ Y.presheaf) := Y.presheaf.mapCone c'₀.op
  let hc' : IsLimit c' := by
    letI e : D ⋙ G ≅ Pairwise.diagram fun i ↦ g ⁻¹ᵁ VX i ⊓ iY ⁻¹ᵁ UT :=
      NatIso.ofComponents (fun | .single i => .refl _ | .pair i j => eqToIso (by
        dsimp [D, G]; rw [Scheme.Hom.preimage_inf, inf_inf_distrib_right]))
    haveI HX := ((TopCat.Presheaf.isSheaf_iff_isSheafPreservesLimitPairwiseIntersections _).mp
      Y.IsSheaf (fun i ↦ g ⁻¹ᵁ VX i ⊓ iY ⁻¹ᵁ UT)).preserves
        (c := ((Cocone.precompose e.inv).obj c'₀).op)
    exact (IsLimit.postcomposeHomEquiv (Functor.isoWhiskerRight (NatIso.op e.symm) Y.presheaf) _)
      ((HX ((IsColimit.precomposeInvEquiv e _).symm
        (IsColimit.extendIso _ (colimit.isColimit _))).op).some.ofIsoLimit (Cone.ext (.refl _)))
  have HαF₂ (i j : _) : Mono (αF.app (.op <| .pair i j)) := by infer_instance
  -- We construct the morphisms between the cone points,
  let f₁ : c.pt ⟶ c'.pt := hc'.lift ((Cone.postcompose αF).obj c)
  let f₂ : c'.pt ⟶ c.pt := hc.lift ⟨c'.pt, ⟨fun
    | .op (.single i) => c'.π.app _ ≫ inv (αF.app (.op <| .single i))
    | .op (.pair i j) => c'.π.app (.op (.single i)) ≫ inv (αF.app (.op <| .single i)) ≫
        F.map (Quiver.Hom.op <| Pairwise.Hom.left i j), by
    rintro ⟨i⟩ ⟨j⟩ f
    obtain ⟨i | ⟨i, j⟩ | ⟨i, j⟩ | ⟨i, j⟩, rfl⟩ :=
      (show Function.Surjective Quiver.Hom.op from Quiver.Hom.opEquiv.surjective) f
    · simp [show Pairwise.Hom.id_single i = 𝟙 (Pairwise.single i) from rfl]
    · simp [show Pairwise.Hom.id_pair i j = 𝟙 (Pairwise.pair i j) from rfl]
    · simp
    · rw [← cancel_mono (αF.app _)]
      simpa using (c'.w (Quiver.Hom.op <| Pairwise.Hom.left i j)).trans
        (c'.w (Quiver.Hom.op <| Pairwise.Hom.right i j)).symm⟩⟩
  -- and prove that they form an isomorphism.
  let e : c.pt ≅ c'.pt := by
    refine ⟨f₁, f₂, hc.hom_ext ?_, hc'.hom_ext ?_⟩
    · rintro ⟨i | ⟨i, j⟩⟩ <;> simp [f₁, f₂]
    · rintro ⟨i | ⟨i, j⟩⟩
      · simp [f₁, f₂]
      · simpa [f₁, f₂] using c'.w (Quiver.Hom.op <| Pairwise.Hom.left i j)
  convert! e.isIso_hom using 1
  · refine hc'.hom_ext fun i ↦ ?_
    rw [hc'.fac]
    ext1
    · simp [αF, c, Under.liftCone, c', c₀]
    · simp [αF, c, c']
/-
**AlgebraicGeometry.mono_pushoutSection_of_isCompact_of_flat_right** 是 Mathlib 中
的一个引理，位于命名空间 `AlgebraicGeometry`。
形式化陈述：mono_pushoutSection_of_isCompact_of_flat_right [Flat f] (hUS : IsAffineOpe
n US) (hUT : IsAffineOpen UT) (hUX : IsCompact (X
参数：hUS : IsAffineOpen US；hUT : IsAffineOpen UT。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePushouts_of_has_finite_limits`：∀ (C :
 Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFin
iteColimits C],   CategoryTheory.Limits.HasFiniteWideP…
· 使用定理 `CategoryTheory.Limits.hasFiniteColimits_of_hasColimits`：∀ (C : Type u) [
inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasColimits C], 
  CategoryTheory.Limits.HasFiniteColimits C
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AlgebraicGeometry.isCompact_iff_finite_and_eq_biUnion_affineOpens`：isCom
pact_iff_finite_and_eq_biUnion_affineOpens {U : X.Opens} : IsCompact (X
· 使用定理 `Set.Finite.to_subtype`：∀ {α : Type u} {s : Set α}, s.Finite → Finite ↑s
· 使用引理 `AlgebraicGeometry.mono_pushoutSection_of_iSup_eq`：mono_pushoutSection_of
_iSup_eq {ι : Type*} [Finite ι] (VX : ι -> X.Opens) (hVU : iSup VX = UX) (hV : f
orall i, Mono (pushoutSection H hUST (…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iSup_subtype`：iSup_subtype {p : ι -> Prop} {f : Subtype p -> α} : iSup f
 = ⨆ (i) (h : p i), f ⟨i, h⟩
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用引理 `AlgebraicGeometry.isIso_pushoutSection_of_isAffineOpen`：isIso_pushoutSec
tion_of_isAffineOpen (hUS : IsAffineOpen US) (hUT : IsAffineOpen UT) (hUX : IsAf
fineOpen UX) : IsIso (pushoutSection H hUST …
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.instStrongMonoOfIsRegularMono`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsRegula
rMono f],   CategoryTheory.StrongM…
· 使用定理 `CategoryTheory.instIsRegularMonoOfIsSplitMono`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsSplit
Mono f],   CategoryTheory.IsRegular…
· 使用定理 `CategoryTheory.IsSplitMono.of_iso`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {X Y : C} (f : Y ⟶ X) [CategoryTheory.IsIso f],   Categor
yTheory.IsSplitMono f
· 使用定理 `AlgebraicGeometry.Scheme.Hom.flat_appLE`：∀ {X Y : AlgebraicGeometry.Sche
me} (f : X ⟶ Y) [self : AlgebraicGeometry.Flat f] {U : Y.Opens},   AlgebraicGeom
etry.IsAffineOpen U →     ∀ {…
-/
lemma mono_pushoutSection_of_isCompact_of_flat_right [Flat f]
    (hUS : IsAffineOpen US) (hUT : IsAffineOpen UT) (hUX : IsCompact (X := X) UX) :
    Mono (pushoutSection H hUST hUSX hUY) := by
  obtain ⟨I, hI, e⟩ := isCompact_iff_finite_and_eq_biUnion_affineOpens.mp hUX
  have := hI.to_subtype
  exact mono_pushoutSection_of_iSup_eq (ι := I) H hUST hUSX hUY (·) (by rwa [iSup_subtype, eq_comm])
    (fun i ↦ have := isIso_pushoutSection_of_isAffineOpen H hUST _ rfl hUS hUT i.1.2; inferInstance)
    (f.flat_appLE hUS hUT _)

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.mono_pushoutSection_of_isCompact_of_flat_left** 是 Mathlib 中的
一个引理，位于命名空间 `AlgebraicGeometry`。
形式化陈述：mono_pushoutSection_of_isCompact_of_flat_left [Flat iX] (hUS : IsAffineOpe
n US) (hUX : IsAffineOpen UX) (hUT : IsCompact (X
参数：hUS : IsAffineOpen US；hUX : IsAffineOpen UX。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePushouts_of_has_finite_limits`：∀ (C :
 Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFin
iteColimits C],   CategoryTheory.Limits.HasFiniteWideP…
· 使用定理 `CategoryTheory.Limits.hasFiniteColimits_of_hasColimits`：∀ (C : Type u) [
inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasColimits C], 
  CategoryTheory.Limits.HasFiniteColimits C
· 使用定理 `CategoryTheory.IsPullback.flip`：flip (h : IsPullback fst snd f g) : IsPu
llback snd fst g f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α), a ⊓ b = b 
⊓ a
· 使用引理 `AlgebraicGeometry.mono_pushoutSection_of_isCompact_of_flat_right`：mono_p
ushoutSection_of_isCompact_of_flat_right [Flat f] (hUS : IsAffineOpen US) (hUT :
 IsAffineOpen UT) (hUX : IsCompact (X
· 使用定理 `CategoryTheory.Limits.hasPushout_symmetry`：hasPushout_symmetry [HasPusho
ut f g] : HasPushout g f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.mono_comp_iff_of_isIso`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} C] {X Y Z : C} (g : Z ⟶ Y) [CategoryTheory.IsIso g]   (f
 : Y ⟶ X), CategoryTheory.M…
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `CategoryTheory.Limits.pushout.hom_ext`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}   [inst_1 : Category
Theory.Limits.HasPushout f …
· 使用引理 `CommRingCat.hom_ext`：hom_ext {R S : CommRingCat} {f g : R ⟶ S} (hf : f.h
om = g.hom) : f = g
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.inl_comp_pushoutSymmetry_hom_assoc`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z)  
 [inst_1 : CategoryTheory.Limits.HasPushout f …
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PushoutCocone.mk_ι_app`：∀ {C : Type u} [inst : Cat
egoryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} {W : C} (inl 
: Y ⟶ W)   (inr : Z ⟶ W) (eq : Cat…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.inr_comp_pushoutSymmetry_hom_assoc`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z)  
 [inst_1 : CategoryTheory.Limits.HasPushout f …
-/
lemma mono_pushoutSection_of_isCompact_of_flat_left [Flat iX]
    (hUS : IsAffineOpen US) (hUX : IsAffineOpen UX) (hUT : IsCompact (X := T) UT) :
    Mono (pushoutSection H hUST hUSX hUY) := by
  suffices Mono (pushoutSection H.flip hUSX hUST (hUY.trans (inf_comm _ _))) by
    rw [← mono_comp_iff_of_isIso (pushoutSymmetry _ _).hom]; convert! this; cat_disch
  exact mono_pushoutSection_of_isCompact_of_flat_right _ _ _ _ hUS hUX hUT
/-
**AlgebraicGeometry.isIso_pushoutSection_of_isQuasiSeparated_of_flat_right** 是 M
athlib 中的一个引理，位于命名空间 `AlgebraicGeometry`。
形式化陈述：isIso_pushoutSection_of_isQuasiSeparated_of_flat_right [Flat f] (hUS : IsA
ffineOpen US) (hUT : IsAffineOpen UT) (hUX : IsCompact (X
参数：hUS : IsAffineOpen US；hUT : IsAffineOpen UT。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePushouts_of_has_finite_limits`：∀ (C :
 Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFin
iteColimits C],   CategoryTheory.Limits.HasFiniteWideP…
· 使用定理 `CategoryTheory.Limits.hasFiniteColimits_of_hasColimits`：∀ (C : Type u) [
inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasColimits C], 
  CategoryTheory.Limits.HasFiniteColimits C
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AlgebraicGeometry.isCompact_iff_finite_and_eq_biUnion_affineOpens`：isCom
pact_iff_finite_and_eq_biUnion_affineOpens {U : X.Opens} : IsCompact (X
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `isOpen_iUnion`：isOpen_iUnion {f : ι -> Set X} (h : forall i, IsOpen (f i
)) : IsOpen (⋃ i, f i)
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Set.iUnion_coe_set`：iUnion_coe_set {α β : Type*} (s : Set α) (f : s -> S
et β) : ⋃ i, f i = ⋃ i in s, f ⟨i, ‹i in s›⟩
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `TopologicalSpace.Opens.iSup_mk`：iSup_mk {ι} (s : ι -> Set α) (h : forall
 i, IsOpen (s i)) : (⨆ i, ⟨s i, h i⟩ : Opens α) = ⟨⋃ i, s i, isOpen_iUnion h⟩
· 使用定理 `TopologicalSpace.Opens.mk.congr_simp`：∀ {α : Type u_2} [inst : Topologic
alSpace α] (carrier carrier_1 : Set α) (e_carrier : carrier = carrier_1)   (is_o
pen' : IsOpen carrier), { …
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Finite.to_subtype`：∀ {α : Type u} {s : Set α}, s.Finite → Finite ↑s
· 使用引理 `AlgebraicGeometry.isIso_pushoutSection_of_iSup_eq`：isIso_pushoutSection_
of_iSup_eq {ι : Type u} [Finite ι] (VX : ι -> X.Opens) (hVU : iSup VX = UX) (hV 
: forall i, IsIso (pushoutSection H hUS…
· 使用定理 `iSup_subtype`：iSup_subtype {p : ι -> Prop} {f : Subtype p -> α} : iSup f
 = ⨆ (i) (h : p i), f ⟨i, h⟩
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用引理 `AlgebraicGeometry.isIso_pushoutSection_of_isAffineOpen`：isIso_pushoutSec
tion_of_isAffineOpen (hUS : IsAffineOpen US) (hUT : IsAffineOpen UT) (hUX : IsAf
fineOpen UX) : IsIso (pushoutSection H hUST …
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用引理 `AlgebraicGeometry.mono_pushoutSection_of_isCompact_of_flat_right`：mono_p
ushoutSection_of_isCompact_of_flat_right [Flat f] (hUS : IsAffineOpen US) (hUT :
 IsAffineOpen UT) (hUX : IsCompact (X
（共 34 条，此处仅展示前 30 条）
-/
lemma isIso_pushoutSection_of_isQuasiSeparated_of_flat_right [Flat f]
    (hUS : IsAffineOpen US) (hUT : IsAffineOpen UT)
    (hUX : IsCompact (X := X) UX) (hUX' : IsQuasiSeparated (α := X) UX) :
    IsIso (pushoutSection H hUST hUSX hUY) := by
  obtain ⟨I, hI, e⟩ := isCompact_iff_finite_and_eq_biUnion_affineOpens.mp hUX
  have hIUX (i : I) : i.1 ≤ UX := by rw [e]; intro i; aesop
  have := hI.to_subtype
  exact isIso_pushoutSection_of_iSup_eq H hUST hUSX hUY (fun i : I ↦ i) (by rwa [iSup_subtype,
    eq_comm]) (fun i ↦ isIso_pushoutSection_of_isAffineOpen _ _ _ _ hUS hUT i.1.2) (fun i j ↦
    mono_pushoutSection_of_isCompact_of_flat_right _ _ _ _ hUS hUT (hUX' _ _ (hIUX _) i.1.1.2
    i.1.2.isCompact (hIUX _) j.1.1.2 j.1.2.isCompact))
    (f.flat_appLE hUS hUT _)

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.isIso_pushoutSection_of_isQuasiSeparated_of_flat_left** 是 Ma
thlib 中的一个引理，位于命名空间 `AlgebraicGeometry`。
形式化陈述：isIso_pushoutSection_of_isQuasiSeparated_of_flat_left [Flat iX] (hUS : IsA
ffineOpen US) (hUX : IsAffineOpen UX) (hUT : IsCompact (X
参数：hUS : IsAffineOpen US；hUX : IsAffineOpen UX。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePushouts_of_has_finite_limits`：∀ (C :
 Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFin
iteColimits C],   CategoryTheory.Limits.HasFiniteWideP…
· 使用定理 `CategoryTheory.Limits.hasFiniteColimits_of_hasColimits`：∀ (C : Type u) [
inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasColimits C], 
  CategoryTheory.Limits.HasFiniteColimits C
· 使用定理 `CategoryTheory.IsPullback.flip`：flip (h : IsPullback fst snd f g) : IsPu
llback snd fst g f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α), a ⊓ b = b 
⊓ a
· 使用引理 `AlgebraicGeometry.isIso_pushoutSection_of_isQuasiSeparated_of_flat_right
`：isIso_pushoutSection_of_isQuasiSeparated_of_flat_right [Flat f] (hUS : IsAffin
eOpen US) (hUT : IsAffineOpen UT) (hUX : IsCompact (X
· 使用定理 `CategoryTheory.Limits.hasPushout_symmetry`：hasPushout_symmetry [HasPusho
ut f g] : HasPushout g f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.isIso_comp_left_iff`：isIso_comp_left_iff {X Y Z : C} (f :
 X ⟶ Y) (g : Y ⟶ Z) [IsIso f] : IsIso (f ≫ g) ↔ IsIso g
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `CategoryTheory.Limits.pushout.hom_ext`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}   [inst_1 : Category
Theory.Limits.HasPushout f …
· 使用引理 `CommRingCat.hom_ext`：hom_ext {R S : CommRingCat} {f g : R ⟶ S} (hf : f.h
om = g.hom) : f = g
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.inl_comp_pushoutSymmetry_hom_assoc`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z)  
 [inst_1 : CategoryTheory.Limits.HasPushout f …
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PushoutCocone.mk_ι_app`：∀ {C : Type u} [inst : Cat
egoryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} {W : C} (inl 
: Y ⟶ W)   (inr : Z ⟶ W) (eq : Cat…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.inr_comp_pushoutSymmetry_hom_assoc`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z)  
 [inst_1 : CategoryTheory.Limits.HasPushout f …
-/
lemma isIso_pushoutSection_of_isQuasiSeparated_of_flat_left [Flat iX]
    (hUS : IsAffineOpen US) (hUX : IsAffineOpen UX)
    (hUT : IsCompact (X := T) UT) (hUT' : IsQuasiSeparated (α := T) UT) :
    IsIso (pushoutSection H hUST hUSX hUY) := by
  suffices IsIso (pushoutSection H.flip hUSX hUST (hUY.trans (inf_comm _ _))) by
    rw [← isIso_comp_left_iff (pushoutSymmetry _ _).hom]; convert! this; cat_disch
  exact isIso_pushoutSection_of_isQuasiSeparated_of_flat_right _ _ _ _ hUS hUX hUT hUT'
/-
**AlgebraicGeometry.mono_pushoutSection_of_isCompact_of_flat_left_of_ringHomFlat
** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry`。
形式化陈述：mono_pushoutSection_of_isCompact_of_flat_left_of_ringHomFlat [Flat iX] (hU
S : IsAffineOpen US) (hUT : IsCompact (X
参数：hUS : IsAffineOpen US。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePushouts_of_has_finite_limits`：∀ (C :
 Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFin
iteColimits C],   CategoryTheory.Limits.HasFiniteWideP…
· 使用定理 `CategoryTheory.Limits.hasFiniteColimits_of_hasColimits`：∀ (C : Type u) [
inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasColimits C], 
  CategoryTheory.Limits.HasFiniteColimits C
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AlgebraicGeometry.isCompact_iff_finite_and_eq_biUnion_affineOpens`：isCom
pact_iff_finite_and_eq_biUnion_affineOpens {U : X.Opens} : IsCompact (X
· 使用定理 `Set.Finite.to_subtype`：∀ {α : Type u} {s : Set α}, s.Finite → Finite ↑s
· 使用引理 `AlgebraicGeometry.mono_pushoutSection_of_iSup_eq`：mono_pushoutSection_of
_iSup_eq {ι : Type*} [Finite ι] (VX : ι -> X.Opens) (hVU : iSup VX = UX) (hV : f
orall i, Mono (pushoutSection H hUST (…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iSup_subtype`：iSup_subtype {p : ι -> Prop} {f : Subtype p -> α} : iSup f
 = ⨆ (i) (h : p i), f ⟨i, h⟩
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用引理 `AlgebraicGeometry.mono_pushoutSection_of_isCompact_of_flat_left`：mono_pu
shoutSection_of_isCompact_of_flat_left [Flat iX] (hUS : IsAffineOpen US) (hUX : 
IsAffineOpen UX) (hUT : IsCompact (X
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
lemma mono_pushoutSection_of_isCompact_of_flat_left_of_ringHomFlat [Flat iX]
    (hUS : IsAffineOpen US) (hUT : IsCompact (X := T) UT)
    (hUX : IsCompact (X := X) UX) (hf : (f.appLE US UT hUST).hom.Flat) :
    Mono (pushoutSection H hUST hUSX hUY) := by
  obtain ⟨I, hI, e⟩ := isCompact_iff_finite_and_eq_biUnion_affineOpens.mp hUX
  have := hI.to_subtype
  exact mono_pushoutSection_of_iSup_eq _ _ _ _ (fun i : I ↦ i) (by rwa [iSup_subtype, eq_comm])
    (fun i ↦ mono_pushoutSection_of_isCompact_of_flat_left _ _ _ _ hUS i.1.2 hUT) hf

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.mono_pushoutSection_of_isCompact_of_flat_right_of_ringHomFla
t** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry`。
形式化陈述：mono_pushoutSection_of_isCompact_of_flat_right_of_ringHomFlat [Flat f] (hU
S : IsAffineOpen US) (hUT : IsCompact (X
参数：hUS : IsAffineOpen US。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePushouts_of_has_finite_limits`：∀ (C :
 Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFin
iteColimits C],   CategoryTheory.Limits.HasFiniteWideP…
· 使用定理 `CategoryTheory.Limits.hasFiniteColimits_of_hasColimits`：∀ (C : Type u) [
inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasColimits C], 
  CategoryTheory.Limits.HasFiniteColimits C
· 使用定理 `CategoryTheory.IsPullback.flip`：flip (h : IsPullback fst snd f g) : IsPu
llback snd fst g f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α), a ⊓ b = b 
⊓ a
· 使用引理 `AlgebraicGeometry.mono_pushoutSection_of_isCompact_of_flat_left_of_ringH
omFlat`：mono_pushoutSection_of_isCompact_of_flat_left_of_ringHomFlat [Flat iX] (
hUS : IsAffineOpen US) (hUT : IsCompact (X
· 使用定理 `CategoryTheory.Limits.hasPushout_symmetry`：hasPushout_symmetry [HasPusho
ut f g] : HasPushout g f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.mono_comp_iff_of_isIso`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} C] {X Y Z : C} (g : Z ⟶ Y) [CategoryTheory.IsIso g]   (f
 : Y ⟶ X), CategoryTheory.M…
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `CategoryTheory.Limits.pushout.hom_ext`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}   [inst_1 : Category
Theory.Limits.HasPushout f …
· 使用引理 `CommRingCat.hom_ext`：hom_ext {R S : CommRingCat} {f g : R ⟶ S} (hf : f.h
om = g.hom) : f = g
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.inl_comp_pushoutSymmetry_hom_assoc`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z)  
 [inst_1 : CategoryTheory.Limits.HasPushout f …
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PushoutCocone.mk_ι_app`：∀ {C : Type u} [inst : Cat
egoryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} {W : C} (inl 
: Y ⟶ W)   (inr : Z ⟶ W) (eq : Cat…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.inr_comp_pushoutSymmetry_hom_assoc`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z)  
 [inst_1 : CategoryTheory.Limits.HasPushout f …
-/
lemma mono_pushoutSection_of_isCompact_of_flat_right_of_ringHomFlat [Flat f]
    (hUS : IsAffineOpen US) (hUT : IsCompact (X := T) UT)
    (hUX : IsCompact (X := X) UX) (hiX : (iX.appLE US UX hUSX).hom.Flat) :
    Mono (pushoutSection H hUST hUSX hUY) := by
  suffices Mono (pushoutSection H.flip hUSX hUST (hUY.trans (inf_comm _ _))) by
    rw [← mono_comp_iff_of_isIso (pushoutSymmetry _ _).hom]; convert! this; cat_disch
  exact mono_pushoutSection_of_isCompact_of_flat_left_of_ringHomFlat _ _ _ _ hUS hUX hUT hiX

set_option backward.isDefEq.respectTransparency false in
include H in
/-
**AlgebraicGeometry.isIso_pushoutSection_of_isCompact_of_flat_right_of_ringHomFl
at** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry`。
形式化陈述：isIso_pushoutSection_of_isCompact_of_flat_right_of_ringHomFlat [Flat f] (h
US : IsAffineOpen US) (hUT : IsCompact (X
参数：hUS : IsAffineOpen US。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePushouts_of_has_finite_limits`：∀ (C :
 Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFin
iteColimits C],   CategoryTheory.Limits.HasFiniteWideP…
· 使用定理 `CategoryTheory.Limits.hasFiniteColimits_of_hasColimits`：∀ (C : Type u) [
inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasColimits C], 
  CategoryTheory.Limits.HasFiniteColimits C
· 使用定理 `CategoryTheory.IsPullback.flip`：flip (h : IsPullback fst snd f g) : IsPu
llback snd fst g f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α), a ⊓ b = b 
⊓ a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AlgebraicGeometry.isCompact_iff_finite_and_eq_biUnion_affineOpens`：isCom
pact_iff_finite_and_eq_biUnion_affineOpens {U : X.Opens} : IsCompact (X
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `isOpen_iUnion`：isOpen_iUnion {f : ι -> Set X} (h : forall i, IsOpen (f i
)) : IsOpen (⋃ i, f i)
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Set.iUnion_coe_set`：iUnion_coe_set {α β : Type*} (s : Set α) (f : s -> S
et β) : ⋃ i, f i = ⋃ i in s, f ⟨i, ‹i in s›⟩
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `TopologicalSpace.Opens.iSup_mk`：iSup_mk {ι} (s : ι -> Set α) (h : forall
 i, IsOpen (s i)) : (⨆ i, ⟨s i, h i⟩ : Opens α) = ⟨⋃ i, s i, isOpen_iUnion h⟩
· 使用定理 `TopologicalSpace.Opens.mk.congr_simp`：∀ {α : Type u_2} [inst : Topologic
alSpace α] (carrier carrier_1 : Set α) (e_carrier : carrier = carrier_1)   (is_o
pen' : IsOpen carrier), { …
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Finite.to_subtype`：∀ {α : Type u} {s : Set α}, s.Finite → Finite ↑s
· 使用引理 `AlgebraicGeometry.isIso_pushoutSection_of_iSup_eq`：isIso_pushoutSection_
of_iSup_eq {ι : Type u} [Finite ι] (VX : ι -> X.Opens) (hVU : iSup VX = UX) (hV 
: forall i, IsIso (pushoutSection H hUS…
· 使用定理 `iSup_subtype`：iSup_subtype {p : ι -> Prop} {f : Subtype p -> α} : iSup f
 = ⨆ (i) (h : p i), f ⟨i, h⟩
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用引理 `AlgebraicGeometry.isIso_pushoutSection_of_isQuasiSeparated_of_flat_left`
：isIso_pushoutSection_of_isQuasiSeparated_of_flat_left [Flat iX] (hUS : IsAffine
Open US) (hUX : IsAffineOpen UX) (hUT : IsCompact (X
（共 48 条，此处仅展示前 30 条）
-/
lemma isIso_pushoutSection_of_isCompact_of_flat_right_of_ringHomFlat [Flat f]
    (hUS : IsAffineOpen US) (hUT : IsCompact (X := T) UT) (hUT' : IsQuasiSeparated (α := T) UT)
    (hUX : IsCompact (X := X) UX) (hUX' : IsQuasiSeparated (α := X) UX)
    (hiX : (iX.appLE US UX hUSX).hom.Flat) :
    IsIso (pushoutSection H hUST hUSX hUY) := by
  suffices IsIso (pushoutSection H.flip hUSX hUST (hUY.trans (inf_comm _ _))) by
    rw [← isIso_comp_left_iff (pushoutSymmetry _ _).hom]; convert! this; cat_disch
  obtain ⟨I, hI, e⟩ := isCompact_iff_finite_and_eq_biUnion_affineOpens.mp hUT
  have hIUT (i : I) : i.1 ≤ UT := by rw [e]; intro i; aesop
  have := hI.to_subtype
  exact isIso_pushoutSection_of_iSup_eq _ _ _ _ (fun i : I ↦ i) (by rwa [iSup_subtype, eq_comm])
    (fun i ↦ isIso_pushoutSection_of_isQuasiSeparated_of_flat_left _ _ _ _ hUS i.1.2 hUX hUX')
    (fun i j ↦ mono_pushoutSection_of_isCompact_of_flat_left_of_ringHomFlat _ _ _ _ hUS hUX
    (hUT' _ _ (hIUT _) i.1.1.2 i.1.2.isCompact (hIUT _) j.1.1.2 j.1.2.isCompact) hiX) hiX

end sections

end AlgebraicGeometry

