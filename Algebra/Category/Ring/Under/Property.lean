/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Category.Ring.Under.Limits
public import Mathlib.CategoryTheory.Limits.MorphismProperty
public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

/-!
# Properties of `P.Under ⊤ R` for `R : CommRingCat`

In this file we translate ring theoretic properties of a property of ring homomorphisms
`P` in properties of the category `P.Under ⊤ R`.

## Main results

- `CommRingCat.Under.hasFiniteLimits`: If `P` is stable under finite products and equalizers,
  `P.Under ⊤ R` has finite limits.
- `RingHom.HasStableEqualizers.preservesFiniteLimits_pushout`: If `P` has stable equalizers,
  base change along arbitrary morphisms preserve finite limits.
-/

@[expose] public section

universe u

open CategoryTheory Limits

variable {Q : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop}

open MorphismProperty

set_option backward.isDefEq.respectTransparency.types false in
/-
**RingHom.HasFiniteProducts.isClosedUnderLimitsOfShape** 是 Mathlib 中的一个引理，位于命名空间
 ``。
形式化陈述：RingHom.HasFiniteProducts.isClosedUnderLimitsOfShape (hQi : RespectsIso Q)
 (hQp : HasFiniteProducts Q) (R : CommRingCat.{u}) : (toMorphismProperty Q).unde
rObj (X
参数：hQi : RespectsIso Q；hQp : HasFiniteProducts Q；R : CommRingCat.{u}。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ObjectProperty.IsClosedUnderFiniteProducts.of_isClosedUnd
erLimitsOfShape`：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] 
{P : CategoryTheory.ObjectProperty C},   (∀ (J : Type w) [Finite J], P.IsClos…
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `RingHom.toMorphismProperty_respectsIso_iff`：toMorphismProperty_respectsI
so_iff : RespectsIso P ↔ (toMorphismProperty P).RespectsIso
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MorphismProperty.underObj_iff`：∀ {T : Type u_3} [inst : C
ategoryTheory.Category.{v_3, u_3} T] {W : CategoryTheory.MorphismProperty T} {X 
: T}   (Y : CategoryTheory.Under X…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Under.w`：w : f.hom ≫ φ.right = g.hom
· 使用定理 `CategoryTheory.MorphismProperty.cancel_right_of_respectsIso`：cancel_righ
t_of_respectsIso (P : MorphismProperty C) [hP : RespectsIso P] {X Y Z : C} (f : 
X ⟶ Y) (g : Y ⟶ Z) [IsIso g] : P (f ≫ g) ↔ P f
· 使用定理 `CategoryTheory.Comma.instIsIsoRight`：∀ {B : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} B] {A : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} A]   {T : Type u₃} [ins…
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
-/
lemma RingHom.HasFiniteProducts.isClosedUnderLimitsOfShape (hQi : RespectsIso Q)
    (hQp : HasFiniteProducts Q) (R : CommRingCat.{u}) :
    (toMorphismProperty Q).underObj (X := R).IsClosedUnderFiniteProducts := by
  refine .of_isClosedUnderLimitsOfShape fun (J : Type u) _ ↦ ⟨fun A ⟨pres, hpres⟩ ↦ ?_⟩
  let e : A ≅ CommRingCat.mkUnder R (Π i, pres.diag.obj ⟨i⟩) :=
    (limit.isoLimitCone ⟨_, pres.isLimit⟩).symm ≪≫
      HasLimit.isoOfNatIso (Discrete.natIso fun i ↦ eqToIso <| by simp) ≪≫
      limit.isoLimitCone ⟨CommRingCat.Under.piFan <| fun i ↦ (pres.diag.obj ⟨i⟩),
        CommRingCat.Under.piFanIsLimit <| fun i ↦ (pres.diag.obj ⟨i⟩)⟩
  have : (toMorphismProperty Q).RespectsIso := toMorphismProperty_respectsIso_iff.mp hQi
  rw [underObj_iff, ← Under.w e.inv, (toMorphismProperty Q).cancel_right_of_respectsIso]
  exact hQp _ fun i ↦ hpres _

set_option backward.isDefEq.respectTransparency.types false in
/-
**RingHom.HasEqualizers.isClosedUnderLimitsOfShape** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：RingHom.HasEqualizers.isClosedUnderLimitsOfShape (hQi : RespectsIso Q) (hQ
e : HasEqualizers Q) (R : CommRingCat.{u}) : (toMorphismProperty Q).underObj (X
参数：hQi : RespectsIso Q；hQe : HasEqualizers Q；R : CommRingCat.{u}。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `RingHom.toMorphismProperty_respectsIso_iff`：toMorphismProperty_respectsI
so_iff : RespectsIso P ↔ (toMorphismProperty P).RespectsIso
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MorphismProperty.underObj_iff`：∀ {T : Type u_3} [inst : C
ategoryTheory.Category.{v_3, u_3} T] {W : CategoryTheory.MorphismProperty T} {X 
: T}   (Y : CategoryTheory.Under X…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Under.w`：w : f.hom ≫ φ.right = g.hom
· 使用定理 `CategoryTheory.MorphismProperty.cancel_right_of_respectsIso`：cancel_righ
t_of_respectsIso (P : MorphismProperty C) [hP : RespectsIso P] {X Y Z : C} (f : 
X ⟶ Y) (g : Y ⟶ Z) [IsIso g] : P (f ≫ g) ↔ P f
· 使用定理 `CategoryTheory.Comma.instIsIsoRight`：∀ {B : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} B] {A : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} A]   {T : Type u₃} [ins…
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
-/
lemma RingHom.HasEqualizers.isClosedUnderLimitsOfShape (hQi : RespectsIso Q)
    (hQe : HasEqualizers Q) (R : CommRingCat.{u}) :
    (toMorphismProperty Q).underObj (X := R).IsClosedUnderLimitsOfShape WalkingParallelPair := by
  refine ⟨fun A ⟨pres, hpres⟩ ↦ ?_⟩
  let e : A ≅
      CommRingCat.mkUnder R
        (AlgHom.equalizer (R := R)
          (CommRingCat.toAlgHom (pres.diag.map .left))
          (CommRingCat.toAlgHom (pres.diag.map .right))) :=
    (limit.isoLimitCone ⟨_, pres.isLimit⟩).symm ≪≫
      HasLimit.isoOfNatIso (diagramIsoParallelPair _) ≪≫ limit.isoLimitCone
        ⟨CommRingCat.Under.equalizerFork (pres.diag.map .left) (pres.diag.map .right),
          CommRingCat.Under.equalizerForkIsLimit
            (pres.diag.map .left) (pres.diag.map .right)⟩
  have : (toMorphismProperty Q).RespectsIso := toMorphismProperty_respectsIso_iff.mp hQi
  rw [underObj_iff, ← Under.w e.inv, (toMorphismProperty Q).cancel_right_of_respectsIso]
  exact hQe _ _ (hpres .zero) (hpres .one)

/-- If `Q` is stable under finite products, the inclusion from the subcategory of `Under R` defined
by `Q` creates finite products. -/
@[instance_reducible]
/-
**RingHom.HasFiniteProducts.createsFiniteProductsForget** 是 Mathlib 中的一个定义，位于命名空
间 ``。
形式化陈述：RingHom.HasFiniteProducts.createsFiniteProductsForget (hQi : RespectsIso Q
) (hQp : HasFiniteProducts Q) (R : CommRingCat.{u}) : CreatesFiniteProducts (Mor
phismProperty.Under.forget (toMorphismProperty Q) ⊤ R)
参数：hQi : RespectsIso Q；hQp : HasFiniteProducts Q；R : CommRingCat.{u}。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.instTop`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C], ⊤.IsMultiplicative

--- 原说明 ---
If `Q` is stable under finite products, the inclusion from the subcategory of `U
nder R` defined
by `Q` creates finite products.
-/
noncomputable def RingHom.HasFiniteProducts.createsFiniteProductsForget
    (hQi : RespectsIso Q) (hQp : HasFiniteProducts Q) (R : CommRingCat.{u}) :
    CreatesFiniteProducts (MorphismProperty.Under.forget (toMorphismProperty Q) ⊤ R) := by
  refine .mk' _ fun (J : Type u) _ ↦ ?_
  apply +allowSynthFailures Comma.forgetCreatesLimitsOfShapeOfClosed
  have := hQp.isClosedUnderLimitsOfShape hQi R
  exact inferInstanceAs <| (toMorphismProperty Q).underObj.IsClosedUnderLimitsOfShape _
/-
**RingHom.HasFiniteProducts.hasFiniteProducts** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：RingHom.HasFiniteProducts.hasFiniteProducts (hQi : RespectsIso Q) (hQp : H
asFiniteProducts Q) (R : CommRingCat.{u}) : Limits.HasFiniteProducts ((RingHom.t
oMorphismProperty Q).Under ⊤ R)
参数：hQi : RespectsIso Q；hQp : HasFiniteProducts Q；R : CommRingCat.{u}。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.instTop`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C], ⊤.IsMultiplicative
· 使用定理 `CategoryTheory.hasLimit_of_created`：hasLimit_of_created (K : J ⥤ C) (F :
 C ⥤ D) [HasLimit (K ⋙ F)] [CreatesLimit K F] : HasLimit K
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
-/
lemma RingHom.HasFiniteProducts.hasFiniteProducts (hQi : RespectsIso Q) (hQp : HasFiniteProducts Q)
    (R : CommRingCat.{u}) :
    Limits.HasFiniteProducts ((RingHom.toMorphismProperty Q).Under ⊤ R) := by
  refine ⟨fun n ↦ ⟨fun D ↦ ?_⟩⟩
  have := hQp.createsFiniteProductsForget hQi R
  exact CategoryTheory.hasLimit_of_created D (Under.forget _ _ R)
/-
**RingHom.HasFiniteProducts.preservesFiniteProducts_pushout** 是 Mathlib 中的一个引理，位
于命名空间 ``。
形式化陈述：RingHom.HasFiniteProducts.preservesFiniteProducts_pushout (hQi : RingHom.R
espectsIso Q) (hQp : RingHom.HasFiniteProducts Q) [(toMorphismProperty Q).IsStab
leUnderCobaseChange] {R S : CommRingCat.{u}} (f : R ⟶ S) : PreservesFiniteProduc
ts (Under.pushout (toMorphismProperty Q) ⊤ f)
参数：hQi : RingHom.RespectsIso Q；hQp : RingHom.HasFiniteProducts Q；toMorphismPrope
rty Q；f : R ⟶ S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.instTop`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C], ⊤.IsMultiplicative
· 使用定理 `CategoryTheory.MorphismProperty.instHasPushoutsAlongOfHasPushouts`：∀ {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C] (P : CategoryTheory.Morphism
Property C) [P.HasPushouts]   {X Y : C} {f : X ⟶ Y}, P.…
· 使用定理 `CategoryTheory.MorphismProperty.instHasPushoutsOfHasPushouts`：∀ {C : Typ
e u} [inst : CategoryTheory.Category.{v, u} C] (P : CategoryTheory.MorphismPrope
rty C)   [CategoryTheory.Limits.HasPushouts C], P.…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePushouts_of_has_finite_limits`：∀ (C :
 Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFin
iteColimits C],   CategoryTheory.Limits.HasFiniteWideP…
· 使用定理 `CategoryTheory.Limits.hasFiniteColimits_of_hasColimits`：∀ (C : Type u) [
inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasColimits C], 
  CategoryTheory.Limits.HasFiniteColimits C
· 使用定理 `CategoryTheory.MorphismProperty.instIsStableUnderCobaseChangeAlongOfIsSt
ableUnderCobaseChange`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] 
(P : CategoryTheory.MorphismProperty C)   [P.IsStableUnderCobaseChange] {X Y : C
} (…
· 使用定理 `CategoryTheory.MorphismProperty.instIsStableUnderCobaseChangeTop`：∀ {C :
 Type u} [inst : CategoryTheory.Category.{v, u} C], ⊤.IsStableUnderCobaseChange
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MorphismProperty.instHasPushoutsAlongOfHasPushoutsAlong`：
∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (P : CategoryTheory.Mor
phismProperty C) {X Y : C} (f : X ⟶ Y)   [CategoryTheory.Lim…
· 使用引理 `CategoryTheory.Limits.preservesLimit_iff_of_natIso`：preservesLimit_iff_o
f_natIso (K : J ⥤ C) {F G : C ⥤ D} (h : F ≅ G) : PreservesLimit K F ↔ PreservesL
imit K G
· 使用定理 `CategoryTheory.preservesLimit_of_createsLimit_and_hasLimit`：∀ {C : Type 
u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Category
Theory.Category.{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Limits.instPreservesLimitsOfShapeDiscreteOfFiniteOfPreser
vesFiniteProducts`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {
D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CommRingCat.Under.instPreservesFiniteProductsUnderPushout`：∀ {R S : Comm
RingCat} (f : R ⟶ S), CategoryTheory.Limits.PreservesFiniteProducts (CategoryThe
ory.Under.pushout f)
· 使用引理 `CategoryTheory.Limits.preservesLimit_of_reflects_of_preserves`：preserves
Limit_of_reflects_of_preserves [PreservesLimit K (F ⋙ G)] [ReflectsLimit (K ⋙ F)
 G] : PreservesLimit K F
· 使用定理 `CategoryTheory.Limits.reflectsLimit_of_reflectsLimitsOfShape`：∀ {C : Typ
e u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Catego
ryTheory.Category.{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `CategoryTheory.Limits.ReflectsFiniteLimits.reflects`：∀ {C : Type u₁} {in
st : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.
Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.instReflectsFiniteLimitsOfReflectsLimits`：∀ {C : T
ype u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Cate
goryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.MorphismProperty.instFullUnderTopUnderForget`：∀ {T : Type
 u_1} [inst : CategoryTheory.Category.{v_1, u_1} T] (P : CategoryTheory.Morphism
Property T) (X : T),   (CategoryTheory.MorphismPr…
· 使用定理 `CategoryTheory.MorphismProperty.instFaithfulUnderUnderForget`：∀ {T : Typ
e u_1} [inst : CategoryTheory.Category.{v_1, u_1} T] (P Q : CategoryTheory.Morph
ismProperty T) (X : T)   [inst_1 : Q.IsMultiplicat…
-/
lemma RingHom.HasFiniteProducts.preservesFiniteProducts_pushout (hQi : RingHom.RespectsIso Q)
    (hQp : RingHom.HasFiniteProducts Q) [(toMorphismProperty Q).IsStableUnderCobaseChange]
    {R S : CommRingCat.{u}} (f : R ⟶ S) :
    PreservesFiniteProducts (Under.pushout (toMorphismProperty Q) ⊤ f) := by
  have := hQp.createsFiniteProductsForget hQi R
  refine ⟨fun n ↦ ⟨fun {K} ↦ ?_⟩⟩
  have : PreservesLimit K (Under.pushout (toMorphismProperty Q) ⊤ f ⋙
        Under.forget (toMorphismProperty Q) ⊤ S) := by
    rw [preservesLimit_iff_of_natIso _ (Under.pushoutCompForgetIso _)]
    infer_instance
  exact preservesLimit_of_reflects_of_preserves _ (MorphismProperty.Under.forget _ ⊤ S)

/-- If `Q` is stable under equalizers, the inclusion from the subcategory of `Under R` defined
by `Q` creates equalizers. -/
@[instance_reducible]
/-
**RingHom.HasEqualizers.createsLimitsWalkingParallelPair** 是 Mathlib 中的一个定义，位于命名
空间 ``。
形式化陈述：RingHom.HasEqualizers.createsLimitsWalkingParallelPair (hQi : RespectsIso 
Q) (hQe : HasEqualizers Q) (R : CommRingCat.{u}) : CreatesLimitsOfShape WalkingP
arallelPair (MorphismProperty.Under.forget (toMorphismProperty Q) ⊤ R)
参数：hQi : RespectsIso Q；hQe : HasEqualizers Q；R : CommRingCat.{u}。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `RingHom.HasEqualizers.isClosedUnderLimitsOfShape`：RingHom.HasEqualizers.
isClosedUnderLimitsOfShape (hQi : RespectsIso Q) (hQe : HasEqualizers Q) (R : Co
mmRingCat.{u}) : (toMorphismProperty Q…

--- 原说明 ---
If `Q` is stable under equalizers, the inclusion from the subcategory of `Under 
R` defined
by `Q` creates equalizers.
-/
noncomputable def RingHom.HasEqualizers.createsLimitsWalkingParallelPair (hQi : RespectsIso Q)
    (hQe : HasEqualizers Q) (R : CommRingCat.{u}) :
    CreatesLimitsOfShape WalkingParallelPair
      (MorphismProperty.Under.forget (toMorphismProperty Q) ⊤ R) := by
  apply +allowSynthFailures Comma.forgetCreatesLimitsOfShapeOfClosed
  exact hQe.isClosedUnderLimitsOfShape hQi _
/-
**RingHom.HasEqualizers.hasEqualizers** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：RingHom.HasEqualizers.hasEqualizers (hQi : RespectsIso Q) (hQe : HasEquali
zers Q) (R : CommRingCat.{u}) : Limits.HasEqualizers ((toMorphismProperty Q).Und
er ⊤ R)
参数：hQi : RespectsIso Q；hQe : HasEqualizers Q；R : CommRingCat.{u}。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.instTop`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C], ⊤.IsMultiplicative
· 使用定理 `CategoryTheory.hasLimit_of_created`：hasLimit_of_created (K : J ⥤ C) (F :
 C ⥤ D) [HasLimit (K ⋙ F)] [CreatesLimit K F] : HasLimit K
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
-/
lemma RingHom.HasEqualizers.hasEqualizers (hQi : RespectsIso Q) (hQe : HasEqualizers Q)
    (R : CommRingCat.{u}) :
    Limits.HasEqualizers ((toMorphismProperty Q).Under ⊤ R) := by
  refine ⟨fun D ↦ ?_⟩
  have := hQe.createsLimitsWalkingParallelPair hQi R
  exact hasLimit_of_created D (Under.forget _ _ R)

namespace CommRingCat

/-- If `Q` is stable under finite products and equalizers, the inclusion from the subcategory of
`Under R` defined by `Q` creates finite limits. -/
@[instance_reducible]
/-
**CommRingCat.Under.createsFiniteLimitsForget** 是 Mathlib 中的一个定义，位于命名空间 `CommRin
gCat.Under`。
形式化陈述：{Q : {R S : Type u} → [inst : CommRing R] → [inst_1 : CommRing S] → (R →+*
 S) → Prop} →   (RingHom.RespectsIso fun {R S} [CommRing R] [CommRing S] => Q) →
     (RingHom.HasFiniteProducts fun {R S} [CommRing R] [CommRing S] => Q) →     
  (RingHom.HasEqualizers fun {R S} [CommRing R] [CommRing S] => Q) →         (R 
: CommRingCat) →           CategoryTheory.Limits.CreatesFiniteLimits            
 (CategoryTheory.MorphismProperty.Under.forget               (RingHom.toMorphism
Property fun {R S} [CommRing R] [CommRing S] => Q) ⊤ R)
参数：R →+* S；RingHom.RespectsIso fun {R S} [CommRing R] [CommRing S] => Q；RingHom.
HasFiniteProducts fun {R S} [CommRing R] [CommRing S] => Q；RingHom.HasEqualizers
 fun {R S} [CommRing R] [CommRing S] => Q；R : CommRingCat；CategoryTheory.Morphis
mProperty.Under.forget               (RingHom.toMorphismProperty fun {R S} [Comm
Ring R] [CommRing S] => Q) ⊤ R。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.instTop`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C], ⊤.IsMultiplicative

--- 原说明 ---
If `Q` is stable under finite products and equalizers, the inclusion from the su
bcategory of
`Under R` defined by `Q` creates finite limits.
-/
noncomputable def Under.createsFiniteLimitsForget (hQi : RingHom.RespectsIso Q)
    (hQp : RingHom.HasFiniteProducts Q) (hQe : RingHom.HasEqualizers Q) (R : CommRingCat.{u}) :
    CreatesFiniteLimits (Under.forget (RingHom.toMorphismProperty Q) ⊤ R) :=
  letI := hQp.createsFiniteProductsForget hQi
  letI := hQe.createsLimitsWalkingParallelPair hQi
  createsFiniteLimitsOfCreatesEqualizersAndFiniteProducts _
/-
**CommRingCat.Under.hasFiniteLimits** 是 Mathlib 中的一个定理，位于命名空间 `CommRingCat.Under
`。
形式化陈述：∀ {Q : {R S : Type u} → [inst : CommRing R] → [inst_1 : CommRing S] → (R →
+* S) → Prop},   (RingHom.RespectsIso fun {R S} [CommRing R] [CommRing S] => Q) 
→     (RingHom.HasFiniteProducts fun {R S} [CommRing R] [CommRing S] => Q) →    
   (RingHom.HasEqualizers fun {R S} [CommRing R] [CommRing S] => Q) →         ∀ 
(R : CommRingCat),           CategoryTheory.Limits.HasFiniteLimits             (
(RingHom.toMorphismProperty fun {R S} [CommRing R] [CommRing S] => Q).Under ⊤ R)
参数：R →+* S；RingHom.RespectsIso fun {R S} [CommRing R] [CommRing S] => Q；RingHom.
HasFiniteProducts fun {R S} [CommRing R] [CommRing S] => Q；RingHom.HasEqualizers
 fun {R S} [CommRing R] [CommRing S] => Q；R : CommRingCat；(RingHom.toMorphismPro
perty fun {R S} [CommRing R] [CommRing S] => Q).Under ⊤ R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.instTop`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C], ⊤.IsMultiplicative
· 使用引理 `RingHom.HasFiniteProducts.hasFiniteProducts`：RingHom.HasFiniteProducts.h
asFiniteProducts (hQi : RespectsIso Q) (hQp : HasFiniteProducts Q) (R : CommRing
Cat.{u}) : Limits.HasFiniteProduc…
· 使用引理 `RingHom.HasEqualizers.hasEqualizers`：RingHom.HasEqualizers.hasEqualizers
 (hQi : RespectsIso Q) (hQe : HasEqualizers Q) (R : CommRingCat.{u}) : Limits.Ha
sEqualizers ((toMorphismP…
· 使用定理 `CategoryTheory.Limits.hasFiniteLimits_of_hasEqualizers_and_finite_produc
ts`：hasFiniteLimits_of_hasEqualizers_and_finite_products [HasFiniteProducts C] [
HasEqualizers C] : HasFiniteLimits C where out _
-/
lemma Under.hasFiniteLimits (hQi : RingHom.RespectsIso Q)
    (hQp : RingHom.HasFiniteProducts Q) (hQe : RingHom.HasEqualizers Q) (R : CommRingCat.{u}) :
    HasFiniteLimits ((RingHom.toMorphismProperty Q).Under ⊤ R) :=
  have := hQp.hasFiniteProducts hQi
  have := hQe.hasEqualizers hQi
  hasFiniteLimits_of_hasEqualizers_and_finite_products

end CommRingCat

variable (P : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop)

open RingHom

variable {P}

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CommRingCat.preservesLimit_parallelPair_tensorProd_iff_tensorEqualizer_bijecti
ve** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：CommRingCat.preservesLimit_parallelPair_tensorProd_iff_tensorEqualizer_bij
ective {R S : CommRingCat.{u}} [Algebra R S] {A B : Under R} {f g : A ⟶ B} : Pre
servesLimit (parallelPair f g) (tensorProd R S) ↔ Function.Bijective ((toAlgHom 
f).tensorEqualizer R S (toAlgHom g))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用引理 `CommRingCat.Under.equalizer_comp`：equalizer_comp {A B : Under R} (f g : 
A ⟶ B) : (AlgHom.equalizer (toAlgHom f) (toAlgHom g)).val.toUnder ≫ f = (AlgHom.
equalizer (toAlgHom f)…
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用引理 `CategoryTheory.Limits.preservesLimit_iff_isLimit_mapCone`：preservesLimit
_iff_isLimit_mapCone {F : C ⥤ D} {t : Cone K} (h : IsLimit t) : PreservesLimit K
 F ↔ Nonempty (IsLimit (F.mapCone t))
· 使用定理 `Equiv.nonempty_congr`：nonempty_congr (e : α ≃ β) : Nonempty α ↔ Nonempty
 β
· 使用引理 `CategoryTheory.Limits.IsLimit.nonempty_isLimit_iff_isIso_lift`：nonempty_
isLimit_iff_isIso_lift {s t : Cone F} (hs : IsLimit s) : Nonempty (IsLimit t) ↔ 
IsIso (hs.lift t)
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `CategoryTheory.Limits.Fork.IsLimit.hom_ext`：∀ {C : Type u} {X Y : C} [in
st : CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y} {s : CategoryTheory.Limits.
Fork f g}   (hs : CategoryTheory…
· 使用定理 `CategoryTheory.Limits.Fork.IsLimit.lift_ι`：∀ {C : Type u} {X Y : C} [ins
t : CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y} {s t : CategoryTheory.Limits
.Fork f g}   (hs : CategoryTheo…
· 使用定理 `CategoryTheory.Under.UnderMorphism.ext`：∀ {T : Type u₁} [inst : Category
Theory.Category.{v₁, u₁} T] {X : T} {U V : CategoryTheory.Under X} {f g : U ⟶ V}
,   CategoryTheory.Under.Hom…
· 使用引理 `CommRingCat.hom_ext`：hom_ext {R S : CommRingCat} {f g : R ⟶ S} (hf : f.h
om = g.hom) : f = g
· 使用引理 `Algebra.TensorProduct.ringHom_ext`：ringHom_ext {C : Type*} [Semiring C] 
{f g : A otimes[R] B ->+* C} (h₁ : f.comp includeLeftRingHom = g.comp includeLef
tRingHom) (h₂ : f.comp …
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.isIso_iff_of_reflects_iso`：isIso_iff_of_reflects_iso {A B
 : C} (f : A ⟶ B) (F : C ⥤ D) [F.ReflectsIsomorphisms] : IsIso (F.map f) ↔ IsIso
 f
· 使用定理 `CategoryTheory.ConcreteCategory.isIso_iff_bijective`：isIso_iff_bijective
 [(forget C).ReflectsIsomorphisms] {X Y : C} (f : X ⟶ Y) : IsIso f ↔ Function.Bi
jective f
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma CommRingCat.preservesLimit_parallelPair_tensorProd_iff_tensorEqualizer_bijective
    {R S : CommRingCat.{u}} [Algebra R S] {A B : Under R} {f g : A ⟶ B} :
    PreservesLimit (parallelPair f g) (tensorProd R S) ↔
      Function.Bijective ((toAlgHom f).tensorEqualizer R S (toAlgHom g)) := by
  let c : Fork f g := Under.equalizerFork f g
  let hc : IsLimit c := Under.equalizerForkIsLimit f g
  let ι : R.mkUnder (AlgHom.equalizer (toAlgHom f) (toAlgHom g)) ⟶ A :=
    (AlgHom.equalizer (toAlgHom f) (toAlgHom g)).val.toUnder
  let h' := (R.tensorProd S).map ι
  have w' : h' ≫ (tensorProd R S).map f = h' ≫ (tensorProd R S).map g := by
    simpa using! congr((R.tensorProd S).map $(CommRingCat.Under.equalizer_comp f g))
  let e : IsLimit ((R.tensorProd S).mapCone c) ≃ IsLimit (Fork.ofι h' w') :=
    isLimitMapConeForkEquiv (tensorProd R S) (Under.equalizer_comp f g)
  rw [preservesLimit_iff_isLimit_mapCone hc, e.nonempty_congr,
    (Under.equalizerForkIsLimit _ _).nonempty_isLimit_iff_isIso_lift]
  have heq : (Under.equalizerForkIsLimit _ _).lift (Fork.ofι h' w') =
      (AlgHom.tensorEqualizer S S (toAlgHom f) (toAlgHom g)).toUnder ≫
        Under.homMk (CommRingCat.ofHom (.id _)) := by
    refine Fork.IsLimit.hom_ext (Under.equalizerForkIsLimit _ _) ?_
    rw [Fork.IsLimit.lift_ι]
    ext : 2
    dsimp
    ext x <;> rfl
  rw [heq, ← isIso_iff_of_reflects_iso _ (CategoryTheory.Under.forget S),
    ConcreteCategory.isIso_iff_bijective]
  rfl
/-
**RingHom.HasStableEqualizers.preservesLimit_parallelPair_tensorProd** 是 Mathlib
 中的一个引理，位于命名空间 ``。
形式化陈述：RingHom.HasStableEqualizers.preservesLimit_parallelPair_tensorProd (hPse :
 HasStableEqualizers P) {R S : CommRingCat.{u}} [Algebra R S] {A B : Under R} (f
 g : A ⟶ B) (hA : P A.hom.hom) (hB : P B.hom.hom) : PreservesLimit (parallelPair
 f g) (CommRingCat.tensorProd R S)
参数：hPse : HasStableEqualizers P；f g : A ⟶ B；hA : P A.hom.hom；hB : P B.hom.hom。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CommRingCat.preservesLimit_parallelPair_tensorProd_iff_tensorEqualizer_b
ijective`：CommRingCat.preservesLimit_parallelPair_tensorProd_iff_tensorEqualizer
_bijective {R S : CommRingCat.{u}} [Algebra R S] {A B : Under R} {f g …
-/
lemma RingHom.HasStableEqualizers.preservesLimit_parallelPair_tensorProd
    (hPse : HasStableEqualizers P) {R S : CommRingCat.{u}} [Algebra R S]
    {A B : Under R} (f g : A ⟶ B) (hA : P A.hom.hom) (hB : P B.hom.hom) :
    PreservesLimit (parallelPair f g) (CommRingCat.tensorProd R S) := by
  rw [CommRingCat.preservesLimit_parallelPair_tensorProd_iff_tensorEqualizer_bijective]
  exact hPse _ _ hA hB
/-
**RingHom.HasStableEqualizers.preservesEqualizers_pushout** 是 Mathlib 中的一个引理，位于命
名空间 ``。
形式化陈述：RingHom.HasStableEqualizers.preservesEqualizers_pushout (hPi : RespectsIso
 P) (hPe : HasEqualizers P) (hPse : HasStableEqualizers P) [(toMorphismProperty 
P).IsStableUnderCobaseChange] {R S : CommRingCat.{u}} (f : R ⟶ S) : PreservesLim
itsOfShape WalkingParallelPair (Under.pushout (toMorphismProperty P) ⊤ f)
参数：hPi : RespectsIso P；hPe : HasEqualizers P；hPse : HasStableEqualizers P；toMorp
hismProperty P；f : R ⟶ S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.instTop`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C], ⊤.IsMultiplicative
· 使用定理 `CategoryTheory.MorphismProperty.instHasPushoutsAlongOfHasPushouts`：∀ {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C] (P : CategoryTheory.Morphism
Property C) [P.HasPushouts]   {X Y : C} {f : X ⟶ Y}, P.…
· 使用定理 `CategoryTheory.MorphismProperty.instHasPushoutsOfHasPushouts`：∀ {C : Typ
e u} [inst : CategoryTheory.Category.{v, u} C] (P : CategoryTheory.MorphismPrope
rty C)   [CategoryTheory.Limits.HasPushouts C], P.…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePushouts_of_has_finite_limits`：∀ (C :
 Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFin
iteColimits C],   CategoryTheory.Limits.HasFiniteWideP…
· 使用定理 `CategoryTheory.Limits.hasFiniteColimits_of_hasColimits`：∀ (C : Type u) [
inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasColimits C], 
  CategoryTheory.Limits.HasFiniteColimits C
· 使用定理 `CategoryTheory.MorphismProperty.instIsStableUnderCobaseChangeAlongOfIsSt
ableUnderCobaseChange`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] 
(P : CategoryTheory.MorphismProperty C)   [P.IsStableUnderCobaseChange] {X Y : C
} (…
· 使用定理 `CategoryTheory.MorphismProperty.instIsStableUnderCobaseChangeTop`：∀ {C :
 Type u} [inst : CategoryTheory.Category.{v, u} C], ⊤.IsStableUnderCobaseChange
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CommRingCat.ofHom_hom`：ofHom_hom {R S : CommRingCat} (f : R ⟶ S) : ofHom
 (Hom.hom f) = f
· 使用引理 `CategoryTheory.Limits.preservesLimit_iff_of_natIso`：preservesLimit_iff_o
f_natIso (K : J ⥤ C) {F G : C ⥤ D} (h : F ≅ G) : PreservesLimit K F ↔ PreservesL
imit K G
· 使用引理 `CategoryTheory.Limits.preservesLimit_iff_of_iso_diagram`：preservesLimit_
iff_of_iso_diagram {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂) : PreservesLimit K₁
 F ↔ PreservesLimit K₂ F
· 使用引理 `RingHom.HasStableEqualizers.preservesLimit_parallelPair_tensorProd`：Ring
Hom.HasStableEqualizers.preservesLimit_parallelPair_tensorProd (hPse : HasStable
Equalizers P) {R S : CommRingCat.{u}} [Algebra R S] {A B…
· 使用定理 `CategoryTheory.MorphismProperty.Comma.prop`：∀ {A : Type u_1} [inst : Cat
egoryTheory.Category.{v_1, u_1} A] {B : Type u_2}   [inst_1 : CategoryTheory.Cat
egory.{v_2, u_2} B] {T : Type u_…
· 使用定理 `CategoryTheory.MorphismProperty.instHasPushoutsAlongOfHasPushoutsAlong`：
∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (P : CategoryTheory.Mor
phismProperty C) {X Y : C} (f : X ⟶ Y)   [CategoryTheory.Lim…
· 使用定理 `CategoryTheory.preservesLimit_of_createsLimit_and_hasLimit`：∀ {C : Type 
u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Category
Theory.Category.{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用引理 `CategoryTheory.Limits.preservesLimit_of_reflects_of_preserves`：preserves
Limit_of_reflects_of_preserves [PreservesLimit K (F ⋙ G)] [ReflectsLimit (K ⋙ F)
 G] : PreservesLimit K F
· 使用定理 `CategoryTheory.Limits.reflectsLimit_of_reflectsLimitsOfShape`：∀ {C : Typ
e u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Catego
ryTheory.Category.{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `CategoryTheory.Limits.ReflectsFiniteLimits.reflects`：∀ {C : Type u₁} {in
st : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.
Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.instReflectsFiniteLimitsOfReflectsLimits`：∀ {C : T
ype u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Cate
goryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.MorphismProperty.instFullUnderTopUnderForget`：∀ {T : Type
 u_1} [inst : CategoryTheory.Category.{v_1, u_1} T] (P : CategoryTheory.Morphism
Property T) (X : T),   (CategoryTheory.MorphismPr…
· 使用定理 `CategoryTheory.MorphismProperty.instFaithfulUnderUnderForget`：∀ {T : Typ
e u_1} [inst : CategoryTheory.Category.{v_1, u_1} T] (P Q : CategoryTheory.Morph
ismProperty T) (X : T)   [inst_1 : Q.IsMultiplicat…
-/
lemma RingHom.HasStableEqualizers.preservesEqualizers_pushout (hPi : RespectsIso P)
    (hPe : HasEqualizers P) (hPse : HasStableEqualizers P)
    [(toMorphismProperty P).IsStableUnderCobaseChange] {R S : CommRingCat.{u}} (f : R ⟶ S) :
    PreservesLimitsOfShape WalkingParallelPair (Under.pushout (toMorphismProperty P) ⊤ f) := by
  refine ⟨fun {K} ↦ ?_⟩
  have := hPe.createsLimitsWalkingParallelPair hPi R
  algebraize [f.hom]
  have : PreservesLimit (K ⋙ Under.forget (toMorphismProperty P) ⊤ R)
      (CategoryTheory.Under.pushout f) := by
    rw [← CommRingCat.ofHom_hom f,
      ← preservesLimit_iff_of_natIso _ (CommRingCat.tensorProdIsoPushout R S),
      ← preservesLimit_iff_of_iso_diagram _ (diagramIsoParallelPair _).symm]
    exact hPse.preservesLimit_parallelPair_tensorProd _ _ ((K.obj _).prop) ((K.obj _).prop)
  have : PreservesLimit K (Under.pushout (toMorphismProperty P) ⊤ f ⋙
        Under.forget (toMorphismProperty P) ⊤ S) := by
    rw [preservesLimit_iff_of_natIso _ (Under.pushoutCompForgetIso _)]
    infer_instance
  exact preservesLimit_of_reflects_of_preserves _ (Under.forget _ ⊤ S)

/-- If `P` is a property of ring homs that is stable under finite products and
equalizers, and the latter are preserved by arbitrary base change,
pushout along any ring homomorphism preserves finite limits. -/
/-
**RingHom.HasStableEqualizers.preservesFiniteLimits_pushout** 是 Mathlib 中的一个引理，位
于命名空间 ``。
形式化陈述：RingHom.HasStableEqualizers.preservesFiniteLimits_pushout (hPi : RingHom.R
espectsIso P) (hPp : HasFiniteProducts P) (hPe : HasEqualizers P) (hPse : HasSta
bleEqualizers P) [(toMorphismProperty P).IsStableUnderCobaseChange] {R S : CommR
ingCat.{u}} (f : R ⟶ S) : PreservesFiniteLimits (Under.pushout (toMorphismProper
ty P) ⊤ f)
参数：hPi : RingHom.RespectsIso P；hPp : HasFiniteProducts P；hPe : HasEqualizers P；h
Pse : HasStableEqualizers P；toMorphismProperty P；f : R ⟶ S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.instTop`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C], ⊤.IsMultiplicative
· 使用定理 `CategoryTheory.MorphismProperty.instHasPushoutsAlongOfHasPushouts`：∀ {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C] (P : CategoryTheory.Morphism
Property C) [P.HasPushouts]   {X Y : C} {f : X ⟶ Y}, P.…
· 使用定理 `CategoryTheory.MorphismProperty.instHasPushoutsOfHasPushouts`：∀ {C : Typ
e u} [inst : CategoryTheory.Category.{v, u} C] (P : CategoryTheory.MorphismPrope
rty C)   [CategoryTheory.Limits.HasPushouts C], P.…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePushouts_of_has_finite_limits`：∀ (C :
 Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFin
iteColimits C],   CategoryTheory.Limits.HasFiniteWideP…
· 使用定理 `CategoryTheory.Limits.hasFiniteColimits_of_hasColimits`：∀ (C : Type u) [
inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasColimits C], 
  CategoryTheory.Limits.HasFiniteColimits C
· 使用定理 `CategoryTheory.MorphismProperty.instIsStableUnderCobaseChangeAlongOfIsSt
ableUnderCobaseChange`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] 
(P : CategoryTheory.MorphismProperty C)   [P.IsStableUnderCobaseChange] {X Y : C
} (…
· 使用定理 `CategoryTheory.MorphismProperty.instIsStableUnderCobaseChangeTop`：∀ {C :
 Type u} [inst : CategoryTheory.Category.{v, u} C], ⊤.IsStableUnderCobaseChange
· 使用引理 `RingHom.HasFiniteProducts.preservesFiniteProducts_pushout`：RingHom.HasFi
niteProducts.preservesFiniteProducts_pushout (hQi : RingHom.RespectsIso Q) (hQp 
: RingHom.HasFiniteProducts Q) [(toMorphismProp…
· 使用引理 `RingHom.HasStableEqualizers.preservesEqualizers_pushout`：RingHom.HasStab
leEqualizers.preservesEqualizers_pushout (hPi : RespectsIso P) (hPe : HasEqualiz
ers P) (hPse : HasStableEqualizers P) [(toMor…
· 使用定理 `CommRingCat.Under.hasFiniteLimits`：∀ {Q : {R S : Type u} → [inst : CommR
ing R] → [inst_1 : CommRing S] → (R →+* S) → Prop},   (RingHom.RespectsIso fun {
R S} [CommRing R] [Comm…
· 使用引理 `CategoryTheory.Limits.preservesFiniteLimits_of_preservesEqualizers_and_f
initeProducts`：preservesFiniteLimits_of_preservesEqualizers_and_finiteProducts [
HasEqualizers C] [HasFiniteProducts C] (G : C ⥤ D) [PreservesLimitsOfShape …
· 使用定理 `CategoryTheory.Limits.hasLimitsOfShape_of_hasFiniteLimits`：∀ (C : Type u
) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFiniteLimi
ts C] (J : Type w)   [inst_2 : CategoryTheory.S…
· 使用定理 `CategoryTheory.Limits.hasFiniteProducts_of_hasFiniteLimits`：∀ (C : Type 
u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFiniteLim
its C],   CategoryTheory.Limits.HasFiniteProduct…

--- 原说明 ---
If `P` is a property of ring homs that is stable under finite products and
equalizers, and the latter are preserved by arbitrary base change,
pushout along any ring homomorphism preserves finite limits.
-/
lemma RingHom.HasStableEqualizers.preservesFiniteLimits_pushout (hPi : RingHom.RespectsIso P)
    (hPp : HasFiniteProducts P) (hPe : HasEqualizers P) (hPse : HasStableEqualizers P)
    [(toMorphismProperty P).IsStableUnderCobaseChange] {R S : CommRingCat.{u}} (f : R ⟶ S) :
    PreservesFiniteLimits (Under.pushout (toMorphismProperty P) ⊤ f) :=
  have := hPp.preservesFiniteProducts_pushout hPi f
  have := hPse.preservesEqualizers_pushout hPi hPe f
  have := CommRingCat.Under.hasFiniteLimits hPi hPp hPe
  preservesFiniteLimits_of_preservesEqualizers_and_finiteProducts _
