/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.RingTheory.Ideal.IdempotentFG
public import Mathlib.RingTheory.RingHom.Unramified
public import Mathlib.RingTheory.Unramified.LocalRing

/-!
# Formally unramified morphisms

A morphism of schemes `f : X ⟶ Y` is formally unramified if for each affine `U ⊆ Y` and
`V ⊆ f ⁻¹' U`, the induced map `Γ(Y, U) ⟶ Γ(X, V)` is formally unramified.

We show that these properties are local, and are stable under compositions and base change.

-/

public section


noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe v u

open AlgebraicGeometry

/-- If `S` is a formally unramified `R`-algebra, essentially of finite type, the diagonal is an
open immersion. -/
/-
**Algebra.FormallyUnramified.isOpenImmersion_SpecMap_lmul** 是 Mathlib 中的一个实例，位于命
名空间 ``。
形式化陈述：Algebra.FormallyUnramified.isOpenImmersion_SpecMap_lmul {R S : Type u} [Co
mmRing R] [CommRing S] [Algebra R S] [Algebra.FormallyUnramified R S] [Algebra.E
ssFiniteType R S] : IsOpenImmersion (Spec.map (CommRingCat.ofHom (TensorProduct.
lmul' R (S
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.isOpenImmersion_SpecMap_iff_of_surjective`：isOpenImmer
sion_SpecMap_iff_of_surjective {R S : CommRingCat} (f : R ⟶ S) (hf : Function.Su
rjective f.hom) : IsOpenImmersion (Spec.map f) ↔ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `CategoryTheory.ConcreteCategory.hom_ofHom`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (C
 → Type w)}   {inst_1 : outPara…
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.isIdempotentElem_iff_of_fg`：isIdempotentElem_iff_of_fg {R : Type*}
 [CommRing R] (I : Ideal R) (h : I.FG) : IsIdempotentElem I ↔ exists e : R, IsId
empotentElem e ∧ I = R…
· 使用定理 `KaehlerDifferential.ideal_fg`：KaehlerDifferential.ideal_fg [EssFiniteTyp
e R S] : (KaehlerDifferential.ideal R S).FG
· 使用定理 `Ideal.cotangent_subsingleton_iff`：cotangent_subsingleton_iff : Subsingle
ton I.Cotangent ↔ IsIdempotentElem I

--- 原说明 ---
If `S` is a formally unramified `R`-algebra, essentially of finite type, the dia
gonal is an
open immersion.
-/
instance Algebra.FormallyUnramified.isOpenImmersion_SpecMap_lmul {R S : Type u} [CommRing R]
    [CommRing S] [Algebra R S] [Algebra.FormallyUnramified R S] [Algebra.EssFiniteType R S] :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (TensorProduct.lmul' R (S := S)).toRingHom)) := by
  rw [isOpenImmersion_SpecMap_iff_of_surjective _ (fun x ↦ ⟨1 ⊗ₜ x, by simp⟩)]
  apply (Ideal.isIdempotentElem_iff_of_fg _ (KaehlerDifferential.ideal_fg R S)).mp
  apply (Ideal.cotangent_subsingleton_iff _).mp
  exact inferInstanceAs <| Subsingleton Ω[S⁄R]

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- A morphism of schemes `f : X ⟶ Y` is formally unramified if for each affine `U ⊆ Y` and
`V ⊆ f ⁻¹' U`, The induced map `Γ(Y, U) ⟶ Γ(X, V)` is formally unramified.

See `FormallyUnramified.hom_ext` and `FormallyUnramified.of_hom_ext`
for the infinitesimal lifting criterion. -/
@[mk_iff]
/-
**AlgebraicGeometry.FormallyUnramified** 是 Mathlib 中的一个类，位于命名空间 `AlgebraicGeomet
ry`。
形式化陈述：FormallyUnramified (f : X ⟶ Y) : Prop where formallyUnramified_appLE (f) :
 forall {U : Y.Opens} (_ : IsAffineOpen U) {V : X.Opens} (_ : IsAffineOpen V) (e
 : V <= f ⁻¹ᵁ U), (f.appLE U V e).hom.FormallyUnramified  alias Scheme.Hom.forma
llyUnramified_appLE
参数：f : X ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism of schemes `f : X ⟶ Y` is formally unramified if for each affine `U ⊆
 Y` and
`V ⊆ f ⁻¹' U`, The induced map `Γ(Y, U) ⟶ Γ(X, V)` is formally unramified.

See `FormallyUnramified.hom_ext` and `FormallyUnramified.of_hom_ext`
for the infinitesimal lifting criterion.
-/
class FormallyUnramified (f : X ⟶ Y) : Prop where
  formallyUnramified_appLE (f) :
    ∀ {U : Y.Opens} (_ : IsAffineOpen U) {V : X.Opens} (_ : IsAffineOpen V) (e : V ≤ f ⁻¹ᵁ U),
      (f.appLE U V e).hom.FormallyUnramified

alias Scheme.Hom.formallyUnramified_appLE := FormallyUnramified.formallyUnramified_appLE

@[deprecated (since := "2026-01-20")]
alias FormallyUnramified.formallyUnramified_of_affine_subset := Scheme.Hom.formallyUnramified_appLE

namespace FormallyUnramified

/-
**AlgebraicGeometry.FormallyUnramified.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeom
etry.FormallyUnramified`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasRingHomProperty @FormallyUnramified RingHom.FormallyUnramified where
  isLocal_ringHomProperty := RingHom.FormallyUnramified.propertyIsLocal
  eq_affineLocally' := by
    ext X Y f
    rw [formallyUnramified_iff, affineLocally_iff_forall_isAffineOpen]
/-
**AlgebraicGeometry.FormallyUnramified.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeom
etry.FormallyUnramified`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MorphismProperty.IsStableUnderComposition @FormallyUnramified :=
  HasRingHomProperty.stableUnderComposition RingHom.FormallyUnramified.stableUnderComposition

set_option backward.isDefEq.respectTransparency.types false in
/-- `f : X ⟶ S` is formally unramified if `X ⟶ X ×ₛ X` is an open immersion.
In particular, monomorphisms (e.g. immersions) are formally unramified.
The converse is true if `f` is locally of finite type. -/
/-
**AlgebraicGeometry.FormallyUnramified.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeom
etry.FormallyUnramified`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`f : X ⟶ S` is formally unramified if `X ⟶ X ×ₛ X` is an open immersion.
In particular, monomorphisms (e.g. immersions) are formally unramified.
The converse is true if `f` is locally of finite type.
-/
instance (priority := 900) [IsOpenImmersion (pullback.diagonal f)] : FormallyUnramified f := by
  wlog hY : ∃ R, Y = Spec R
  · rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @FormallyUnramified) Y.affineCover]
    intro i
    have inst : IsOpenImmersion (pullback.diagonal (pullback.snd f (Y.affineCover.f i))) :=
      MorphismProperty.pullback_snd (P := .diagonal @IsOpenImmersion) _ _ ‹_›
    exact this (pullback.snd _ _) ⟨_, rfl⟩
  obtain ⟨R, rfl⟩ := hY
  wlog hX : ∃ S, X = Spec S generalizing X
  · rw [IsZariskiLocalAtSource.iff_of_openCover (P := @FormallyUnramified) X.affineCover]
    intro i
    have inst : IsOpenImmersion (pullback.diagonal (X.affineCover.f i ≫ f)) :=
      MorphismProperty.comp_mem (.diagonal @IsOpenImmersion) _ _
        (inferInstanceAs (IsOpenImmersion _)) ‹_›
    exact this (_ ≫ _) ⟨_, rfl⟩
  obtain ⟨S, rfl⟩ := hX
  obtain ⟨φ, rfl : Spec.map φ = f⟩ := Spec.homEquiv.symm.surjective f
  rw [HasRingHomProperty.Spec_iff (P := @FormallyUnramified)]
  algebraize [φ.hom]
  let F := (Algebra.TensorProduct.lmul' R (S := S)).toRingHom
  have hF : Function.Surjective F := fun x ↦ ⟨.mk _ _ _ x 1, by simp [F]⟩
  have : IsOpenImmersion (Spec.map (CommRingCat.ofHom F)) := by
    rwa [← MorphismProperty.cancel_right_of_respectsIso (P := @IsOpenImmersion) _
      (pullbackSpecIso R S S).inv, ← AlgebraicGeometry.diagonal_SpecMap R S]
  obtain ⟨e, he, he'⟩ := (isOpenImmersion_SpecMap_iff_of_surjective _ hF).mp this
  refine ⟨subsingleton_of_forall_eq 0 fun x ↦ ?_⟩
  obtain ⟨⟨x, hx⟩, rfl⟩ := Ideal.toCotangent_surjective _ x
  obtain ⟨x, rfl⟩ := Ideal.mem_span_singleton.mp (he'.le hx)
  refine (Ideal.toCotangent_eq_zero _ _).mpr ?_
  rw [pow_two, Subtype.coe_mk, ← he, mul_assoc]
  exact Ideal.mul_mem_mul (he'.ge (Ideal.mem_span_singleton_self e)) hx
/-
**AlgebraicGeometry.FormallyUnramified.of_comp** 是 Mathlib 中的一个定理，位于命名空间 `Algebr
aicGeometry.FormallyUnramified`。
形式化陈述：of_comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [FormallyUnramified (f ≫ 
g)] : FormallyUnramified f
参数：f : X ⟶ Y；g : Y ⟶ Z；f ≫ g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.HasRingHomProperty.of_comp`：of_comp (H : forall {R S T
 : Type u} [CommRing R] [CommRing S] [CommRing T], forall (f : R ->+* S) (g : S 
->+* T), Q (g.comp f) -> Q g) {X Y…
· 使用定理 `AlgebraicGeometry.FormallyUnramified.instHasRingHomPropertyFormallyUnram
ified`：AlgebraicGeometry.HasRingHomProperty @AlgebraicGeometry.FormallyUnramifie
d fun {R S} [CommRing R] [CommRing S] =>   RingHom.FormallyUnramifi…
· 使用定理 `IsScalarTower.of_algebraMap_eq'`：of_algebraMap_eq' [Algebra R A] (h : al
gebraMap R A = (algebraMap S A).comp (algebraMap R S)) : IsScalarTower R S A
· 使用定理 `Algebra.FormallyUnramified.of_restrictScalars`：of_restrictScalars [Forma
llyUnramified R B] : FormallyUnramified A B
-/
theorem of_comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    [FormallyUnramified (f ≫ g)] : FormallyUnramified f :=
  HasRingHomProperty.of_comp (fun {R S T _ _ _} f g H ↦ by
    algebraize [f, g, g.comp f]
    exact Algebra.FormallyUnramified.of_restrictScalars R S T) ‹_›
/-
**AlgebraicGeometry.FormallyUnramified.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeom
etry.FormallyUnramified`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MorphismProperty.IsMultiplicative @FormallyUnramified where
  id_mem _ := inferInstance
/-
**AlgebraicGeometry.FormallyUnramified.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeom
etry.FormallyUnramified`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MorphismProperty.IsStableUnderBaseChange @FormallyUnramified :=
  HasRingHomProperty.isStableUnderBaseChange RingHom.FormallyUnramified.isStableUnderBaseChange

set_option backward.isDefEq.respectTransparency.types false in
open MorphismProperty in
/-- The diagonal of a formally unramified morphism of finite type is an open immersion. -/
/-
**AlgebraicGeometry.FormallyUnramified.isOpenImmersion_diagonal** 是 Mathlib 中的一个
实例，位于命名空间 `AlgebraicGeometry.FormallyUnramified`。
形式化陈述：isOpenImmersion_diagonal [FormallyUnramified f] [LocallyOfFiniteType f] : 
IsOpenImmersion (pullback.diagonal f)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `AlgebraicGeometry.Spec.map_surjective`：∀ {R S : CommRingCat}, Function.S
urjective AlgebraicGeometry.Spec.map
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.diagonal_SpecMap`：diagonal_SpecMap : pullback.diagonal
 (Spec.map (CommRingCat.ofHom (algebraMap R S))) = Spec.map (CommRingCat.ofHom (
Algebra.TensorProduct.lm…
· 使用定理 `CategoryTheory.MorphismProperty.cancel_right_of_respectsIso`：cancel_righ
t_of_respectsIso (P : MorphismProperty C) [hP : RespectsIso P] {X Y Z : C} (f : 
X ⟶ Y) (g : Y ⟶ Z) [IsIso g] : P (f ≫ g) ↔ P f
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `AlgebraicGeometry.HasRingHomProperty.Spec_iff`：Spec_iff {R S : CommRingC
at.{u}} {φ : R ⟶ S} : P (Spec.map φ) ↔ Q φ.hom
· 使用定理 `AlgebraicGeometry.FormallyUnramified.instHasRingHomPropertyFormallyUnram
ified`：AlgebraicGeometry.HasRingHomProperty @AlgebraicGeometry.FormallyUnramifie
d fun {R S} [CommRing R] [CommRing S] =>   RingHom.FormallyUnramifi…
· 使用定理 `Algebra.EssFiniteType.of_finiteType`：∀ (R : Type u_1) (S : Type u_2) [in
st : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   [Algebra.FiniteT
ype R S], Algebra.EssFini…
· 使用定理 `AlgebraicGeometry.instHasRingHomPropertyLocallyOfFiniteTypeFiniteType`：A
lgebraicGeometry.HasRingHomProperty @AlgebraicGeometry.LocallyOfFiniteType fun {
R S} [CommRing R] [CommRing S] =>   RingHom.FiniteType
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.Scheme.instIsStableUnderBaseChangePrecoverageOfIsJoint
lySurjectivePreservingOfIsStableUnderBaseChange`：∀ (P : CategoryTheory.MorphismP
roperty AlgebraicGeometry.Scheme)   [AlgebraicGeometry.Scheme.IsJointlySurjectiv
ePreserving P] [P.IsStableUnd…
· 使用定理 `AlgebraicGeometry.Scheme.instIsJointlySurjectivePreservingIsOpenImmersio
n`：AlgebraicGeometry.Scheme.IsJointlySurjectivePreserving AlgebraicGeometry.IsOp
enImmersion
· 使用引理 `AlgebraicGeometry.IsZariskiLocalAtTarget.of_range_subset_iSup`：of_range_
subset_iSup [P.RespectsRight @IsOpenImmersion] {ι : Type*} (U : ι -> Y.Opens) (H
 : Set.range f subseteq (⨆ i, U i : Y.Opens)) (hf :…
· 使用定理 `CategoryTheory.MorphismProperty.Respects.toRespectsRight`：∀ {C : Type u}
 {inst : CategoryTheory.CategoryStruct.{v, u} C} {P Q : CategoryTheory.MorphismP
roperty C}   [self : P.Respects Q], P.Respects…
· 使用定理 `CategoryTheory.MorphismProperty.instRespectsOfIsStableUnderComposition`：
∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (W : CategoryTheory.Mor
phismProperty C)   [W.IsStableUnderComposition], W.Respects …
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.range_diagonal_subset_diagonalCoverDia
gonalRange`：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) (𝒰 : Y.OpenCover)   (
𝒱 : (i : 𝒰.I₀) → (CategoryTheory.Limits.pullback f (𝒰.f i)).OpenCover), …
· 使用定理 `AlgebraicGeometry.Scheme.instIsOpenImmersionF`：∀ {X : AlgebraicGeometry.
Scheme} (𝒰 : X.OpenCover) (i : 𝒰.I₀), AlgebraicGeometry.IsOpenImmersion (𝒰.f i)
· 使用定理 `CategoryTheory.MorphismProperty.arrow_mk_iso_iff`：arrow_mk_iso_iff (P : 
MorphismProperty C) [RespectsIso P] {W X Y Z : C} {f : W ⟶ X} {g : Y ⟶ Z} (e : A
rrow.mk f ≅ Arrow.mk g) : P f ↔ P g
· 使用引理 `CategoryTheory.MorphismProperty.comp_mem`：comp_mem (W : MorphismProperty
 C) [W.IsStableUnderComposition] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : W f) 
(hg : W g) : W (f ≫ g)
· 使用定理 `AlgebraicGeometry.FormallyUnramified.instIsStableUnderCompositionScheme`
：CategoryTheory.MorphismProperty.IsStableUnderComposition @AlgebraicGeometry.For
mallyUnramified
· 使用定理 `AlgebraicGeometry.FormallyUnramified.instOfIsOpenImmersionDiagonalScheme
`：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y)   [AlgebraicGeometry.IsOpenImme
rsion (CategoryTheory.Limits.pullback.diagonal f)],   Algebrai…
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.of_isIso`：∀ {Y Z : AlgebraicGeometry.S
cheme} (g : Y ⟶ Z) [CategoryTheory.IsIso g], AlgebraicGeometry.IsOpenImmersion g
· 使用定理 `CategoryTheory.Limits.pullback.instIsIsoDiagonalOfMono`：∀ {C : Type u_1}
 [inst : CategoryTheory.Category.{v_1, u_1} C] {X Y : C} (f : X ⟶ Y)   [inst_1 :
 CategoryTheory.Limits.HasPullback f f] [Cat…
· 使用定理 `CategoryTheory.MorphismProperty.pullback_snd`：pullback_snd {X Y S : C} (
f : X ⟶ S) (g : Y ⟶ S) [HasPullback f g] [P.IsStableUnderBaseChangeAlong g] (H :
 P f) : P (pullback.snd f g)
· 使用定理 `CategoryTheory.MorphismProperty.instIsStableUnderBaseChangeAlongOfIsStab
leUnderBaseChange`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (P :
 CategoryTheory.MorphismProperty C)   [P.IsStableUnderBaseChange] {X Y : C} (f …
· 使用定理 `AlgebraicGeometry.FormallyUnramified.instIsStableUnderBaseChangeScheme`：
CategoryTheory.MorphismProperty.IsStableUnderBaseChange @AlgebraicGeometry.Forma
llyUnramified
· 使用定理 `AlgebraicGeometry.instIsStableUnderCompositionSchemeLocallyOfFiniteType`
：CategoryTheory.MorphismProperty.IsStableUnderComposition @AlgebraicGeometry.Loc
allyOfFiniteType
· 使用定理 `AlgebraicGeometry.locallyOfFiniteType_of_isOpenImmersion`：∀ {X Y : Algeb
raicGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.IsOpenImmersion f],   Algebr
aicGeometry.LocallyOfFiniteType f
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
The diagonal of a formally unramified morphism of finite type is an open immersi
on.
-/
instance isOpenImmersion_diagonal [FormallyUnramified f] [LocallyOfFiniteType f] :
    IsOpenImmersion (pullback.diagonal f) := by
  wlog hX : (∃ S, X = Spec S) ∧ ∃ R, Y = Spec R
  · let 𝒰Y := Y.affineCover
    let 𝒰X (j : (Y.affineCover.pullback₁ f).I₀) :
        ((Y.affineCover.pullback₁ f).X j).OpenCover := Scheme.affineCover _
    apply IsZariskiLocalAtTarget.of_range_subset_iSup _
      (Scheme.Pullback.range_diagonal_subset_diagonalCoverDiagonalRange f 𝒰Y 𝒰X)
    intro ⟨i, j⟩
    rw [arrow_mk_iso_iff (P := @IsOpenImmersion)
      (Scheme.Pullback.diagonalRestrictIsoDiagonal f 𝒰Y 𝒰X i j)]
    have hu : FormallyUnramified ((𝒰X i).f j ≫ pullback.snd f (𝒰Y.f i)) :=
      comp_mem _ _ _ inferInstance (pullback_snd _ _ inferInstance)
    have hfin : LocallyOfFiniteType ((𝒰X i).f j ≫ pullback.snd f (𝒰Y.f i)) :=
      comp_mem _ _ _ inferInstance (pullback_snd _ _ inferInstance)
    exact this _ ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩
  obtain ⟨⟨S, rfl⟩, R, rfl⟩ := hX
  obtain ⟨f, rfl⟩ := Spec.map_surjective f
  rw [HasRingHomProperty.Spec_iff (P := @FormallyUnramified),
    HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at *
  algebraize [f.hom]
  rw [show f = CommRingCat.ofHom (algebraMap R S) from rfl, diagonal_SpecMap R S,
    cancel_right_of_respectsIso (P := @IsOpenImmersion)]
  infer_instance
/-
**AlgebraicGeometry.FormallyUnramified.stalkMap** 是 Mathlib 中的一个引理，位于命名空间 `Algeb
raicGeometry.FormallyUnramified`。
形式化陈述：stalkMap [FormallyUnramified f] (x : X) : (f.stalkMap x).hom.FormallyUnram
ified
参数：x : X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.HasRingHomProperty.stalkMap`：stalkMap (hQ : forall {R 
S : Type u} [CommRing R] [CommRing S] (f : R ->+* S) (_ : Q f) (J : Ideal S) (_ 
: J.IsPrime), Q (Localization.local…
· 使用定理 `AlgebraicGeometry.FormallyUnramified.instHasRingHomPropertyFormallyUnram
ified`：AlgebraicGeometry.HasRingHomProperty @AlgebraicGeometry.FormallyUnramifie
d fun {R S} [CommRing R] [CommRing S] =>   RingHom.FormallyUnramifi…
· 使用引理 `RingHom.HoldsForLocalization.localRingHom`：RingHom.HoldsForLocalization.
localRingHom (hPc : StableUnderComposition P) (hPp : LocalizationPreserves P) (h
Pl : HoldsForLocalization P) {R…
· 使用引理 `RingHom.FormallyUnramified.stableUnderComposition`：stableUnderCompositio
n : StableUnderComposition FormallyUnramified
· 使用引理 `RingHom.IsStableUnderBaseChange.localizationPreserves`：RingHom.IsStableU
nderBaseChange.localizationPreserves : LocalizationPreserves P
· 使用引理 `RingHom.FormallyUnramified.isStableUnderBaseChange`：isStableUnderBaseCha
nge : IsStableUnderBaseChange FormallyUnramified
· 使用引理 `RingHom.FormallyUnramified.holdsForLocalization`：holdsForLocalization : 
HoldsForLocalization FormallyUnramified
· 使用定理 `Ideal.IsPrime.comap`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst : 
Semiring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S] (f : F)   {K : Ideal 
S} [inst_…
-/
lemma stalkMap [FormallyUnramified f] (x : X) : (f.stalkMap x).hom.FormallyUnramified :=
  HasRingHomProperty.stalkMap
    (fun f hf p q ↦
      RingHom.FormallyUnramified.holdsForLocalization.localRingHom
        RingHom.FormallyUnramified.stableUnderComposition
        RingHom.FormallyUnramified.isStableUnderBaseChange.localizationPreserves _ hf) ‹_› x
/-
**AlgebraicGeometry.FormallyUnramified.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeom
etry.FormallyUnramified`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [FormallyUnramified f] [LocallyOfFiniteType f] (x : X) :
    letI : Algebra (Y.residueField (f.base x)) (X.residueField x) :=
      (f.residueFieldMap x).hom.toAlgebra
    Algebra.IsSeparable (Y.residueField (f.base x)) (X.residueField x) := by
  algebraize [(f.stalkMap x).hom]
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
    inferInstanceAs <| IsLocalHom (f.stalkMap x).hom
  suffices h : Algebra.IsSeparable
      (IsLocalRing.ResidueField <| Y.presheaf.stalk (f x))
      (IsLocalRing.ResidueField <| X.presheaf.stalk x) by
    convert! h
    refine Algebra.algebra_ext _ _ fun x ↦ ?_
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective x
    rfl
  have : Algebra.EssFiniteType (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := by
    rw [← RingHom.essFiniteType_algebraMap, RingHom.algebraMap_toAlgebra]
    exact LocallyOfFiniteType.stalkMap f x
  have : Algebra.FormallyUnramified (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := by
    rw [← RingHom.formallyUnramified_algebraMap, RingHom.algebraMap_toAlgebra]
    exact stalkMap f x
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
/--
Given any commuting diagram
```
Z' --→ X
|      |
↓      ↓
Z  --→ Y
```
With `X ⟶ Y` formally unramified and `Z' ⟶ Z` an infinitesimal thickening, there exists at most
one arrow `Z ⟶ X` making the diagram commute.
-/
@[stacks 04F1]
/-
**AlgebraicGeometry.FormallyUnramified.hom_ext** 是 Mathlib 中的一个定理，位于命名空间 `Algebr
aicGeometry.FormallyUnramified`。
形式化陈述：∀ {X Y Z' Z : AlgebraicGeometry.Scheme} (i : Z' ⟶ Z),   IsNilpotent (Algeb
raicGeometry.Scheme.Hom.ker i) →     ∀ [AlgebraicGeometry.IsClosedImmersion i] (
f : X ⟶ Y) [AlgebraicGeometry.FormallyUnramified f] {g₁ g₂ : Z ⟶ X},       Categ
oryTheory.CategoryStruct.comp i g₁ = CategoryTheory.CategoryStruct.comp i g₂ →  
       CategoryTheory.CategoryStruct.comp g₁ f = CategoryTheory.CategoryStruct.c
omp g₂ f → g₁ = g₂
参数：i : Z' ⟶ Z；AlgebraicGeometry.Scheme.Hom.ker i；f : X ⟶ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.isDominant_iff`：∀ {X Y : AlgebraicGeometry.Scheme} (f 
: X ⟶ Y), AlgebraicGeometry.IsDominant f ↔ DenseRange ⇑f
· 使用定理 `denseRange_iff_closure_range`：denseRange_iff_closure_range : DenseRange 
f ↔ closure (range f) = univ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.Scheme.Hom.support_ker`：∀ {X Y : AlgebraicGeometry.Sch
eme} (f : X ⟶ Y) [AlgebraicGeometry.QuasiCompact f],   ↑(AlgebraicGeometry.Schem
e.Hom.ker f).support = closure…
· 使用定理 `AlgebraicGeometry.instQuasiCompactOfUniversallyClosed`：∀ {X Y : Algebrai
cGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.UniversallyClosed f], Algebraic
Geometry.QuasiCompact f
· 使用定理 `AlgebraicGeometry.IsProper.toUniversallyClosed`：∀ {X Y : AlgebraicGeomet
ry.Scheme} {f : X ⟶ Y} [self : AlgebraicGeometry.IsProper f],   AlgebraicGeometr
y.UniversallyClosed f
· 使用定理 `AlgebraicGeometry.IsProper.instOfIsFinite`：∀ {X Y : AlgebraicGeometry.Sc
heme} (f : X ⟶ Y) [AlgebraicGeometry.IsFinite f], AlgebraicGeometry.IsProper f
· 使用定理 `AlgebraicGeometry.IsFinite.instOfIsClosedImmersion`：∀ {X Y : AlgebraicGe
ometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.IsClosedImmersion f], AlgebraicGeo
metry.IsFinite f
· 使用引理 `AlgebraicGeometry.Scheme.IdealSheafData.support_pow`：support_pow (n : Na
t) (hn : n != 0) : (I ^ n).support = I.support
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AlgebraicGeometry.Scheme.IdealSheafData.bot_mul`：∀ {X : AlgebraicGeometr
y.Scheme} (I : X.IdealSheafData), ⊥ * I = ⊥
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `AlgebraicGeometry.Scheme.hom_ext_of_forall`：hom_ext_of_forall {X Y : Sch
eme} (f g : X ⟶ Y) (H : forall x : X, exists U : X.Opens, x in U ∧ U.ι ≫ f = U.ι
 ≫ g) : f = g
· 使用定理 `TopologicalSpace.IsTopologicalBasis.exists_subset_of_mem_open`：∀ {α : Ty
pe u} [t : TopologicalSpace α] {b : Set (Set α)},   TopologicalSpace.IsTopologic
alBasis b → ∀ {a : α} {u : Set α}, a ∈ u → IsOpen u…
· 使用定理 `AlgebraicGeometry.Scheme.isBasis_affineOpens`：∀ (X : AlgebraicGeometry.S
cheme), TopologicalSpace.Opens.IsBasis X.affineOpens
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `isOpen_univ`：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen Set.univ
· 使用定理 `TopologicalSpace.Opens.isOpen`：∀ {α : Type u_2} [inst : TopologicalSpace
 α] (U : TopologicalSpace.Opens α), IsOpen ↑U
· 使用引理 `TopCat.ext`：ext {X Y : TopCat.{u}} {f g : X ⟶ Y} (w : forall x : X, f x 
= g x) : f = g
· 使用定理 `AlgebraicGeometry.Scheme.Hom.surjective`：∀ {X Y : AlgebraicGeometry.Sche
me} (f : X ⟶ Y) [AlgebraicGeometry.Surjective f], Function.Surjective ⇑f
· 使用定理 `AlgebraicGeometry.Surjective.of_universallyClosed_of_isDominant`：∀ {X Y 
: AlgebraicGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.UniversallyClosed f] 
[AlgebraicGeometry.IsDominant f],   AlgebraicGeometry…
· 使用定理 `AlgebraicGeometry.Scheme.Hom.formallyUnramified_appLE`：∀ {X Y : Algebrai
cGeometry.Scheme} (f : X ⟶ Y) [self : AlgebraicGeometry.FormallyUnramified f] {U
 : Y.Opens},   AlgebraicGeometry.IsAffineOp…
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
（共 50 条，此处仅展示前 30 条）

--- 原说明 ---
Given any commuting diagram
```
Z' --→ X
|      |
↓      ↓
Z  --→ Y
```
With `X ⟶ Y` formally unramified and `Z' ⟶ Z` an infinitesimal thickening, there
 exists at most
one arrow `Z ⟶ X` making the diagram commute.
-/
protected lemma hom_ext {Z' Z : Scheme} (i : Z' ⟶ Z) (hi : IsNilpotent i.ker) [IsClosedImmersion i]
    (f : X ⟶ Y) [FormallyUnramified f]
    {g₁ g₂ : Z ⟶ X} (hig : i ≫ g₁ = i ≫ g₂) (hgf : g₁ ≫ f = g₂ ≫ f) : g₁ = g₂ := by
  have : IsDominant i := by
    obtain ⟨n, hn⟩ := hi
    rw [isDominant_iff, denseRange_iff_closure_range, ← i.support_ker,
      ← i.ker.support_pow (n + 1) (by simp), pow_succ, hn]
    simp
  refine Scheme.hom_ext_of_forall _ _ fun x ↦ ?_
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f (g₁ x))) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU : V ≤ f ⁻¹ᵁ U⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxU (f ⁻¹ᵁ U).isOpen
  have : g₁.base = g₂.base := by ext x; obtain ⟨x, rfl⟩ := i.surjective x; exact congr($hig x)
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWV : W ≤ _⟩ := Z.isBasis_affineOpens.exists_subset_of_mem_open
    (And.intro hxV (by simpa [← this])) (g₁ ⁻¹ᵁ V ⊓ g₂ ⁻¹ᵁ V).isOpen
  refine ⟨W, hxW, ?_⟩
  have := f.formallyUnramified_appLE hU hV hVU
  algebraize [(f.appLE U V hVU).hom,
    ((g₁ ≫ f).appLE U W (by grw [hWV, inf_le_left, hVU]; rfl)).hom]
  let ψ₁ : Γ(X, V) →ₐ[Γ(Y, U)] Γ(Z, W) := ⟨(g₁.appLE _ _ (hWV.trans inf_le_left)).hom, fun r ↦ by
    simp [RingHom.algebraMap_toAlgebra, ← CategoryTheory.comp_apply, -CommRingCat.hom_comp,
      Scheme.Hom.appLE_comp_appLE]⟩
  let ψ₂ : Γ(X, V) →ₐ[Γ(Y, U)] Γ(Z, W) := ⟨(g₂.appLE _ _ (hWV.trans inf_le_right)).hom, fun r ↦ by
    simp [RingHom.algebraMap_toAlgebra, ← CategoryTheory.comp_apply, -CommRingCat.hom_comp,
      Scheme.Hom.appLE_comp_appLE, hgf, -Scheme.Hom.comp_appLE]⟩
  suffices ψ₁ = ψ₂ by
    simpa [ψ₁, ψ₂, -Iso.cancel_iso_hom_left, IsAffineOpen.isoSpec_hom] using
      congr(hW.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom ($this).toRingHom) ≫ hV.fromSpec)
  refine Algebra.FormallyUnramified.ext' (i.app W).hom ?_ ψ₁ ψ₂ ?_
  · obtain ⟨n, hn⟩ := hi
    exact ⟨n, by simpa using congr(($hn).ideal ⟨W, hW⟩)⟩
  · simp [ψ₁, ψ₂, ← CategoryTheory.comp_apply, -CommRingCat.hom_comp, hig,
      Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE, -Scheme.Hom.comp_appLE]

/--
To show that `f : X ⟶ Y` is formally unramified,
it suffices to check for that every following commuting diagram
```
Spec R --→ X
  |        |
  ↓        ↓
Spec S --→ Y
```
with `S = R/I` for some `I² = 0`, there exists at most one arrow `Spec S ⟶ X` making
the diagram commute.
-/
/-
**AlgebraicGeometry.FormallyUnramified.of_hom_ext** 是 Mathlib 中的一个定理，位于命名空间 `Alg
ebraicGeometry.FormallyUnramified`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y),   (∀ (R S : CommRingCat) (
φ : R ⟶ S),       Function.Surjective ⇑(CategoryTheory.ConcreteCategory.hom φ) →
         RingHom.ker (CommRingCat.Hom.hom φ) ^ 2 = ⊥ →           ∀ (g₁ g₂ : Alge
braicGeometry.Spec R ⟶ X),             CategoryTheory.CategoryStruct.comp (Algeb
raicGeometry.Spec.map φ) g₁ =                 CategoryTheory.CategoryStruct.comp
 (AlgebraicGeometry.Spec.map φ) g₂ →               CategoryTheory.CategoryStruct
.comp g₁ f = CategoryTheory.CategoryStruct.comp g₂ f → g₁ = g₂) →     AlgebraicG
eometry.FormallyUnramified f
参数：f : X ⟶ Y；∀ (R S : CommRingCat) (φ : R ⟶ S),       Function.Surjective ⇑(Cate
goryTheory.ConcreteCategory.hom φ) →         RingHom.ker (CommRingCat.Hom.hom φ)
 ^ 2 = ⊥ →           ∀ (g₁ g₂ : AlgebraicGeometry.Spec R ⟶ X),             Categ
oryTheory.CategoryStruct.comp (AlgebraicGeometry.Spec.map φ) g₁ =               
  CategoryTheory.CategoryStruct.comp (AlgebraicGeometry.Spec.map φ) g₂ →        
       CategoryTheory.CategoryStruct.comp g₁ f = CategoryTheory.CategoryStruct.c
omp g₂ f → g₁ = g₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Algebra.FormallyUnramified.iff_comp_injective`：iff_comp_injective : Form
allyUnramified R A ↔ forall ⦃B : Type u⦄ [CommRing B], forall [Algebra R B] (I :
 Ideal B) (_ : I ^ 2 = ⊥), Function…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用引理 `CommRingCat.hom_ext`：hom_ext {R S : CommRingCat} {f g : R ⟶ S} (hf : f.h
om = g.hom) : f = g
· 使用定理 `AlgHom.comp_algebraMap`：comp_algebraMap : (φ : A ->+* B).comp (algebraMa
p R A) = algebraMap R B
· 使用定理 `Ideal.Quotient.mk_surjective`：mk_surjective : Function.Surjective (mk I)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `RingHom.ker.congr_simp`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst
 : Semiring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S]   [rcf : RingHomCl
ass F R S] (…
· 使用定理 `CategoryTheory.ConcreteCategory.hom_ofHom`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (C
 → Type w)}   {inst_1 : outPara…
· 使用定理 `Ideal.Quotient.mkₐ_ker`：∀ (R₁ : Type u_1) {A : Type u_3} [inst : CommSem
iring R₁] [inst_1 : Ring A] [inst_2 : Algebra R₁ A] (I : Ideal A)   [inst_3 : I.
IsTwoSided],…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `RingHomClass.toRingHom.congr_simp`：∀ {F : Type u_1} {α : Type u_2} {β : 
Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSemir
ing β} [inst_1 : RingHo…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `AlgebraicGeometry.IsAffineOpen.SpecMap_appLE_fromSpec`：SpecMap_appLE_fro
mSpec (f : X ⟶ Y) {V : X.Opens} {U : Y.Opens} (hU : IsAffineOpen U) (hV : IsAffi
neOpen V) (i : V <= f ⁻¹ᵁ U) : Spec.map (f.…
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用定理 `AlgebraicGeometry.Spec.map_inj`：∀ {R S : CommRingCat} {φ ψ : R ⟶ S}, Alg
ebraicGeometry.Spec.map φ = AlgebraicGeometry.Spec.map ψ ↔ φ = ψ
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…

--- 原说明 ---
To show that `f : X ⟶ Y` is formally unramified,
it suffices to check for that every following commuting diagram
```
Spec R --→ X
  |        |
  ↓        ↓
Spec S --→ Y
```
with `S = R/I` for some `I² = 0`, there exists at most one arrow `Spec S ⟶ X` ma
king
the diagram commute.
-/
protected lemma of_hom_ext (f : X ⟶ Y)
    (H : ∀ (R S : CommRingCat) (φ : R ⟶ S) (_ : Function.Surjective φ)
      (_ : RingHom.ker φ.hom ^ 2 = ⊥) (g₁ g₂ : Spec R ⟶ X)
      (_ : Spec.map φ ≫ g₁ = Spec.map φ ≫ g₂) (_ : g₁ ≫ f = g₂ ≫ f), g₁ = g₂) :
    FormallyUnramified f := by
  refine ⟨fun {U hU V hV hVU} ↦ ?_⟩
  let := (f.appLE U V hVU).hom.toAlgebra
  refine Algebra.FormallyUnramified.iff_comp_injective.mpr fun R _ _ I hI g₁ g₂ hg₁g₂ ↦ ?_
  have hg₁ : f.appLE U V hVU ≫ CommRingCat.ofHom g₁ = CommRingCat.ofHom (algebraMap _ R) :=
    CommRingCat.hom_ext g₁.comp_algebraMap
  have hg₂ : f.appLE U V hVU ≫ CommRingCat.ofHom g₂ = CommRingCat.ofHom (algebraMap _ R) :=
    CommRingCat.hom_ext g₂.comp_algebraMap
  have := H (.of R) (.of (R ⧸ I)) (CommRingCat.ofHom (Ideal.Quotient.mkₐ Γ(Y, U) I))
    Ideal.Quotient.mk_surjective (by simpa)
    (Spec.map (CommRingCat.ofHom g₁) ≫ hV.fromSpec) (Spec.map (CommRingCat.ofHom g₂) ≫ hV.fromSpec)
    (by simp only [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, ← AlgHom.comp_toRingHom, *])
    (by simp only [Category.assoc, ← hU.SpecMap_appLE_fromSpec f hV hVU, ← Spec.map_comp_assoc, *])
  rw [cancel_mono, Spec.map_inj] at this
  exact AlgHom.ext fun x ↦ congr($this x)

end FormallyUnramified

end AlgebraicGeometry

