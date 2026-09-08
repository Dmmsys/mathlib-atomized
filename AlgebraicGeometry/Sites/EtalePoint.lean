/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten, Joël Riou
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.CategoryTheory.Functor.TypeValuedFlat
public import Mathlib.CategoryTheory.Limits.Elements
public import Mathlib.CategoryTheory.Sites.Point.Conservative
public import Mathlib.FieldTheory.SeparableClosure

/-!

# Points of the étale site

In this file, we show that a morphism `Spec (.of Ω) ⟶ S` where `Ω` is
a separably closed field defines a point on the small étale site of `S`.
We show that these points form a conservative family.

-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

variable {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (s : Spec (.of Ω) ⟶ S)

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.Scheme.exists_fac_of_etale_of_isSepClosed** 是 Mathlib 中的一个引理
，位于命名空间 `AlgebraicGeometry.Scheme`。
形式化陈述：exists_fac_of_etale_of_isSepClosed {X S : Scheme.{u}} (f : X ⟶ S) [Etale f
] {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ S) (x : X) (hx : f 
x = s default) : exists (l : Spec (.of Ω) ⟶ X), l ≫ f = s ∧ l default = x
参数：f : X ⟶ S；s : Spec (.of Ω) ⟶ S；x : X；hx : f x = s default。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
· 使用定理 `AlgebraicGeometry.FormallyUnramified.instIsSeparableCarrierResidueFieldC
oeContinuousMapCarrierCarrierCommRingCatHomTopCatBaseOfLocallyOfFiniteType`：∀ {X
 Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.FormallyUnramified
 f]   [AlgebraicGeometry.LocallyOfFiniteType f] (x : ↥X)…
· 使用定理 `AlgebraicGeometry.Etale.instFormallyUnramified`：∀ {X Y : AlgebraicGeomet
ry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.Etale f], AlgebraicGeometry.FormallyUn
ramified f
· 使用定理 `AlgebraicGeometry.instLocallyOfFiniteTypeOfLocallyOfFinitePresentation`：
∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [hf : AlgebraicGeometry.LocallyOf
FinitePresentation f],   AlgebraicGeometry.LocallyOfFiniteTy…
· 使用定理 `AlgebraicGeometry.instLocallyOfFinitePresentationOfSmooth`：∀ {X Y : Alge
braicGeometry.Scheme} (f : X ⟶ Y) [hf : AlgebraicGeometry.Smooth f],   Algebraic
Geometry.LocallyOfFinitePresentation f
· 使用定理 `AlgebraicGeometry.Etale.instSmooth`：∀ {X Y : AlgebraicGeometry.Scheme} (
f : X ⟶ Y) [AlgebraicGeometry.Etale f], AlgebraicGeometry.Smooth f
· 使用引理 `CommRingCat.hom_ext`：hom_ext {R S : CommRingCat} {f g : R ⟶ S} (hf : f.h
om = g.hom) : f = g
· 使用定理 `AlgHom.comp_algebraMap`：comp_algebraMap : (φ : A ->+* B).comp (algebraMa
p R A) = algebraMap R B
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `AlgebraicGeometry.Scheme.descResidueField_stalkClosedPointTo_fromSpecRes
idueField`：descResidueField_stalkClosedPointTo_fromSpecResidueField (K : Type u)
 [Field K] (X : Scheme.{u}) (f : Spec (.of K) ⟶ X) : Spec.map (descResi…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AlgebraicGeometry.Spec.map_comp`：∀ {R S T : CommRingCat} (f : R ⟶ S) (g 
: S ⟶ T),   AlgebraicGeometry.Spec.map (CategoryTheory.CategoryStruct.comp f g) 
=     CategoryTheory.…
· 使用定理 `AlgebraicGeometry.Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueFiel
d`：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) (x : ↥X),   CategoryTheory.Cat
egoryStruct.comp (AlgebraicGeometry.Spec.map (AlgebraicGeometry…
· 使用引理 `AlgebraicGeometry.Scheme.fromSpecResidueField_apply`：fromSpecResidueFiel
d_apply (x : X.carrier) (s : Spec (X.residueField x)) : X.fromSpecResidueField x
 s = x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma exists_fac_of_etale_of_isSepClosed {X S : Scheme.{u}} (f : X ⟶ S) [Etale f]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (x : X) (hx : f x = s default) :
    ∃ (l : Spec (.of Ω) ⟶ X), l ≫ f = s ∧ l default = x := by
  obtain ⟨⟨s, a⟩, rfl⟩ := (SpecToEquivOfField Ω S).symm.surjective s
  obtain rfl : f x = s := by simp [hx, SpecToEquivOfField]
  let m := (f.residueFieldMap x).hom
  dsimp at m
  algebraize [m, a.hom]
  let b : X.residueField x →ₐ[S.residueField (f x)] Ω :=
    IsSepClosed.lift
  have : f.residueFieldMap x ≫ CommRingCat.ofHom b.toRingHom = a := by
    ext1; exact b.comp_algebraMap
  refine ⟨Spec.map (CommRingCat.ofHom b.toRingHom) ≫ X.fromSpecResidueField x, ?_, ?_⟩
  · simp [SpecToEquivOfField, ← this]
    rfl
  · dsimp
    apply fromSpecResidueField_apply
/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsCofiltered (Etale.forget S ⋙ coyoneda.obj (op (Over.mk s))).Elements :=
  Functor.isCofiltered_elements _

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A morphism `s : Spec (.of Ω) ⟶ S` where `Ω` is a separably closed field
defines a point for the small étale site of `S`. -/
@[simps]
/-
**AlgebraicGeometry.Scheme.pointSmallEtale** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicG
eometry.Scheme`。
形式化陈述：pointSmallEtale : (smallEtaleTopology S).Point where fiber
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism `s : Spec (.of Ω) ⟶ S` where `Ω` is a separably closed field
defines a point for the small étale site of `S`.
-/
noncomputable def pointSmallEtale : (smallEtaleTopology S).Point where
  fiber := Etale.forget S ⋙ coyoneda.obj (op (Over.mk s))
  initiallySmall :=
    initiallySmall_of_essentiallySmall_weakly_initial_objectProperty
      (Functor.Elements.precomp (AffineEtale.Spec S)
        (Etale.forget S ⋙ coyoneda.obj (op (Over.mk s)))).essImage (by
      rintro ⟨X, x⟩
      cases X with | _ Y f
      obtain ⟨y, hy, rfl⟩ := Over.homMk_surjective x
      dsimp at y hy
      obtain ⟨R, j, _, y', rfl⟩ : ∃ (R : CommRingCat) (j : Spec (.of R) ⟶ Y)
          (_ : IsOpenImmersion j) (y' : _ ⟶ _), y' ≫ j = y := by
        obtain ⟨R, j, _, hj, _⟩ := exists_affine_mem_range_and_range_subset
          (x := y.base default) (U := ⊤) (by simp)
        refine ⟨R, j, inferInstance, _, IsOpenImmersion.lift_fac j y ?_⟩
        rintro _ ⟨a, rfl⟩
        rwa [Subsingleton.elim a default]
      exact ⟨_,
        ⟨Functor.elementsMk _ (AffineEtale.mk (j ≫ f)) (Over.homMk y'), ⟨Iso.refl _⟩⟩,
        ⟨⟨MorphismProperty.Over.homMk j rfl (by simp), by cat_disch⟩⟩⟩)
  jointly_surjective {X} R hR φ := by
    cases X with | _ X f
    obtain ⟨φ : Spec (.of Ω) ⟶ X, rfl : φ ≫ f = s, rfl⟩ := Over.homMk_surjective φ
    obtain ⟨𝒰, h, _, le⟩ := (mem_smallGrothendieckTopology _ _).1 hR
    obtain ⟨i, y, hy⟩ := 𝒰.exists_eq (φ default)
    obtain ⟨l, hl₁, hl₂⟩ := exists_fac_of_etale_of_isSepClosed (𝒰.f i) φ _ hy
    have : 𝒰.f i ≫ f = 𝒰.X i ↘ S := HomIsOver.comp_over (f := 𝒰.f i) (S := S)
    exact ⟨(𝒰.X i).asOverProp S inferInstance,
      MorphismProperty.Over.homMk (𝒰.f i), le _ _ ⟨i⟩, Over.homMk l, by cat_disch⟩

variable {s₀ : S} (hs₀ : s default = s₀)

/-- Given a morphism `s : Spec (.of Ω) ⟶ S` with image `s₀ : S` where `Ω` is a
separably closed field, this is the canonical map
`(pointSmallEtale s).fiber.obj X ⟶ X.hom ⁻¹' {s₀}` for `X : S.Etale`. -/
@[simps]
/-
**AlgebraicGeometry.Scheme.pointSmallEtaleFiberObjToPreimage** 是 Mathlib 中的一个定义，
位于命名空间 `AlgebraicGeometry.Scheme`。
形式化陈述：pointSmallEtaleFiberObjToPreimage {X : S.Etale} (t : (pointSmallEtale s).f
iber.obj X) : X.hom ⁻¹' {s₀}
参数：t : (pointSmallEtale s).fiber.obj X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a morphism `s : Spec (.of Ω) ⟶ S` with image `s₀ : S` where `Ω` is a
separably closed field, this is the canonical map
`(pointSmallEtale s).fiber.obj X ⟶ X.hom ⁻¹' {s₀}` for `X : S.Etale`.
-/
noncomputable def pointSmallEtaleFiberObjToPreimage {X : S.Etale}
    (t : (pointSmallEtale s).fiber.obj X) :
    X.hom ⁻¹' {s₀} :=
  ⟨t.left (default : Spec (.of Ω)), by
    have := (Over.w t).symm
    cat_disch⟩

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {Y X : Scheme.{u}} (f : Y ⟶ X) [Etale f] (x : X) :
    Etale (f.fiberToSpecResidueField x) := by
  dsimp [Hom.fiberToSpecResidueField]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.Scheme.pointSmallEtaleFiberObjToPreimage_surjective** 是 Math
lib 中的一个引理，位于命名空间 `AlgebraicGeometry.Scheme`。
形式化陈述：pointSmallEtaleFiberObjToPreimage_surjective (X : S.Etale) : Function.Surj
ective (pointSmallEtaleFiberObjToPreimage s hs₀ (X
参数：X : S.Etale。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.surjective`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologic
alSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y),   Function.Surjective ⇑h
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
· 使用引理 `AlgebraicGeometry.Scheme.exists_fac_of_etale_of_isSepClosed`：exists_fac_
of_etale_of_isSepClosed {X S : Scheme.{u}} (f : X ⟶ S) [Etale f] {Ω : Type u} [F
ield Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ S) (x…
· 使用定理 `AlgebraicGeometry.Scheme.instEtaleFiberToSpecResidueField`：∀ {Y X : Alge
braicGeometry.Scheme} (f : Y ⟶ X) [AlgebraicGeometry.Etale f] (x : ↥X),   Algebr
aicGeometry.Etale (AlgebraicGeometry.Scheme.Hom…
· 使用定理 `AlgebraicGeometry.Scheme.instEtaleHomDiscretePUnit`：∀ (X : AlgebraicGeom
etry.Scheme) (Y : X.Etale), AlgebraicGeometry.Etale Y.hom
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `AlgebraicGeometry.Scheme.Hom.fiber_fac`：∀ {X Y : AlgebraicGeometry.Schem
e} (f : X ⟶ Y) (y : ↥Y),   CategoryTheory.CategoryStruct.comp (AlgebraicGeometry
.Scheme.Hom.fiberι f y) f = …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Mathlib.Tactic.Reassoc.eq_whisker'`：eq_whisker' {C : Type*} [Category* C
] {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) : f ≫ h = g ≫ h
· 使用定理 `AlgebraicGeometry.Scheme.SpecToEquivOfField_symm_apply`：∀ (K : Type u) [
inst : Field K] (X : AlgebraicGeometry.Scheme) (xf : (x : ↥X) × (X.residueField 
x ⟶ CommRingCat.of K)),   (AlgebraicGeometry…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `AlgebraicGeometry.Scheme.fromSpecResidueField_apply`：fromSpecResidueFiel
d_apply (x : X.carrier) (s : Spec (X.residueField x)) : X.fromSpecResidueField x
 s = x
-/
lemma pointSmallEtaleFiberObjToPreimage_surjective (X : S.Etale) :
    Function.Surjective (pointSmallEtaleFiberObjToPreimage s hs₀ (X := X)) := by
  intro y
  obtain ⟨y, rfl⟩ := (X.hom.fiberHomeo s₀).surjective y
  obtain ⟨⟨t, a⟩, rfl⟩ := (Scheme.SpecToEquivOfField Ω _).symm.surjective s
  obtain rfl : t = s₀ := by simp [SpecToEquivOfField, ← hs₀]
  obtain ⟨l, hl, rfl⟩ := exists_fac_of_etale_of_isSepClosed
    (X.hom.fiberToSpecResidueField _) (Spec.map a) y (by subsingleton)
  refine ⟨Over.homMk (l ≫ X.hom.fiberι t) ?_, rfl⟩
  simp [X.hom.fiber_fac, reassoc_of% hl]

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.Scheme.isConservative_pointSmallEtale** 是 Mathlib 中的一个引理，位于命
名空间 `AlgebraicGeometry.Scheme`。
形式化陈述：isConservative_pointSmallEtale {ι : Type*} {S : Scheme.{u}} {Ω : ι -> Type
 u} [forall i, Field (Ω i)] [forall i, IsSepClosed (Ω i)] (s : forall i, Spec (.
of (Ω i)) ⟶ S) (hs : ⋃ i, Set.range (s i) = .univ) : (ObjectProperty.ofObj (fun 
i => pointSmallEtale (s i))).IsConservativeFamilyOfPoints
参数：Ω i；Ω i；s : forall i, Spec (.of (Ω i)) ⟶ S；hs : ⋃ i, Set.range (s i) = .univ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints.mk'`：mk' [Has
Sheafify J (Type w)] (hP : forall ⦃X : C⦄ (S : Sieve X) (_ : forall (Φ : P.FullS
ubcategory) (x : Φ.obj.fiber.obj X), exists (Y : C) …
· 使用定理 `CategoryTheory.locallySmall_of_univLE`：∀ (C : Type u) [inst : CategoryTh
eory.Category.{v, u} C] [UnivLE.{v, w}], CategoryTheory.LocallySmall.{w, v, u} C
· 使用定理 `AlgebraicGeometry.Scheme.instHasSheafifyEtaleSmallEtaleTopology`：∀ {S : 
AlgebraicGeometry.Scheme} {A : Type u'} [inst : CategoryTheory.Category.{u, u'} 
A] {FA : A → A → Type u_1}   {CD : A → Type u} [inst_…
· 使用定理 `CategoryTheory.Types.instPreservesLimitsOfSizeForgetTypeFun`：CategoryThe
ory.Limits.PreservesLimitsOfSize.{u_1, u_2, u, u, u + 1, u + 1} (CategoryTheory.
forget (Type u))
· 使用定理 `CategoryTheory.Limits.Types.hasColimitsOfSize`：∀ [UnivLE.{v, u}], Catego
ryTheory.Limits.HasColimitsOfSize.{w, v, u, u + 1} (Type u)
· 使用定理 `CategoryTheory.Limits.Types.hasLimitsOfSize`：∀ [UnivLE.{v, u}], Category
Theory.Limits.HasLimitsOfSize.{w, v, u, u + 1} (Type u)
· 使用定理 `CategoryTheory.instReflectsIsomorphismsForgetTypeFun`：(CategoryTheory.fo
rget (Type u_1)).ReflectsIsomorphisms
· 使用定理 `CategoryTheory.Limits.PreservesColimits.preservesFilteredColimits`：∀ {C 
: Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : C
ategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Types.instPreservesColimitsOfSizeForgetTypeFun`：CategoryT
heory.Limits.PreservesColimitsOfSize.{u_1, u_2, u, u, u + 1, u + 1} (CategoryThe
ory.forget (Type u))
· 使用引理 `CategoryTheory.Sieve.exists_eq_ofArrows`：exists_eq_ofArrows (R : Sieve X
) : exists (I : Type max u₁ v₁) (Y : I -> C) (f : forall i, Y i ⟶ X), R = Sieve.
ofArrows _ f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.Scheme.ofArrows_mem_smallEtaleTopology_iff`：ofArrows_m
em_smallEtaleTopology_iff {X : Scheme.{u}} {W : X.Etale} {ι : Type*} {Z : ι -> X
.Etale} (f : forall i, Z i ⟶ W) : Sieve.ofArrows _…
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `AlgebraicGeometry.Scheme.pointSmallEtaleFiberObjToPreimage_surjective`：p
ointSmallEtaleFiberObjToPreimage_surjective (X : S.Etale) : Function.Surjective 
(pointSmallEtaleFiberObjToPreimage s hs₀ (X
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `AlgebraicGeometry.Scheme.pointSmallEtaleFiberObjToPreimage_coe`：∀ {S : A
lgebraicGeometry.Scheme} {Ω : Type u} [inst : Field Ω] [inst_1 : IsSepClosed Ω] 
  (s : AlgebraicGeometry.Spec (CommRingCat.of Ω) ⟶ S…
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
-/
lemma isConservative_pointSmallEtale
    {ι : Type*} {S : Scheme.{u}}
    {Ω : ι → Type u} [∀ i, Field (Ω i)] [∀ i, IsSepClosed (Ω i)]
    (s : ∀ i, Spec (.of (Ω i)) ⟶ S)
    (hs : ⋃ i, Set.range (s i) = .univ) :
    (ObjectProperty.ofObj (fun i ↦ pointSmallEtale (s i))).IsConservativeFamilyOfPoints :=
  .mk' (fun X R hR ↦ by
    obtain ⟨α, T, f, rfl⟩ := R.exists_eq_ofArrows
    rw [ofArrows_mem_smallEtaleTopology_iff]
    ext x
    simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
    obtain ⟨i, hi⟩ : ∃ i, s i default = X.hom x := by
      have := Set.mem_univ (X.hom x)
      simp only [← hs, Functor.id_obj, Set.mem_iUnion, Set.mem_range] at this
      obtain ⟨i, y, hy⟩ := this
      obtain rfl := Subsingleton.elim y default
      exact ⟨i, hy⟩
    obtain ⟨x', hx'⟩ := pointSmallEtaleFiberObjToPreimage_surjective (s i) hi X ⟨x, by simp⟩
    rw [Subtype.ext_iff] at hx'
    simp only [Functor.id_obj, pointSmallEtaleFiberObjToPreimage_coe, Etale.forget_obj_left] at hx'
    subst hx'
    obtain ⟨W, g, ⟨Z, p, _, ⟨a⟩, rfl⟩, y, rfl⟩ := hR ⟨_, ⟨i⟩⟩ x'
    exact ⟨a, (pointSmallEtaleFiberObjToPreimage (s i) hi (y ≫ p.hom)).1, rfl⟩)
/-
**AlgebraicGeometry.Scheme.isConservativeFamilyOfPoints_pointSmallEtale'** 是 Mat
hlib 中的一个引理，位于命名空间 `AlgebraicGeometry.Scheme`。
形式化陈述：isConservativeFamilyOfPoints_pointSmallEtale' (S : Scheme.{u}) : (ObjectPr
operty.ofObj (fun (s : S) => pointSmallEtale ((SpecToEquivOfField (SeparableClos
ure (S.residueField s)) _).2 ⟨s, CommRingCat.ofHom (algebraMap (S.residueField s
) _)⟩))).IsConservativeFamilyOfPoints
参数：S : Scheme.{u}。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.Scheme.isConservative_pointSmallEtale`：isConservative_
pointSmallEtale {ι : Type*} {S : Scheme.{u}} {Ω : ι -> Type u} [forall i, Field 
(Ω i)] [forall i, IsSepClosed (Ω i)] (s : for…
· 使用定理 `AlgebraicClosure.instIsScalarTower`：∀ (k : Type u) [inst : Field k] {R :
 Type u_1} {S : Type u_2} [inst_1 : CommSemiring R] [inst_2 : CommSemiring S]   
[inst_3 : Algebra R S] […
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `AlgebraicGeometry.Scheme.fromSpecResidueField_apply`：fromSpecResidueFiel
d_apply (x : X.carrier) (s : Spec (X.residueField x)) : X.fromSpecResidueField x
 s = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma isConservativeFamilyOfPoints_pointSmallEtale' (S : Scheme.{u}) :
    (ObjectProperty.ofObj (fun (s : S) ↦ pointSmallEtale
      ((SpecToEquivOfField (SeparableClosure (S.residueField s)) _).2
        ⟨s, CommRingCat.ofHom
          (algebraMap (S.residueField s) _)⟩))).IsConservativeFamilyOfPoints :=
  isConservative_pointSmallEtale _ (by
    ext s
    simp only [Equiv.invFun_as_coe, Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
    exact ⟨s, default, by simp [SpecToEquivOfField]⟩)
/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : GrothendieckTopology.HasEnoughPoints.{u} (smallEtaleTopology S) where
  exists_objectProperty :=
    ⟨_, inferInstance, isConservativeFamilyOfPoints_pointSmallEtale' S⟩

end AlgebraicGeometry.Scheme

