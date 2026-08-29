/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.RegularMono
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.Limits.Preserves.Basic

/-!
# Definitions and basic properties of normal monomorphisms and epimorphisms.

A normal monomorphism is a morphism that is the kernel of some other morphism.

We give the construction `NormalMono → RegularMono` (`CategoryTheory.NormalMono.regularMono`)
as well as the dual construction for normal epimorphisms. We show equivalences reflect normal
monomorphisms (`CategoryTheory.equivalenceReflectsNormalMono`), and that the pullback of a
normal monomorphism is normal (`CategoryTheory.normalOfIsPullbackSndOfNormal`).

We also define classes `IsNormalMonoCategory` and `IsNormalEpiCategory` for categories in which
every monomorphism or epimorphism is normal, and deduce that these categories are
`RegularMonoCategory`s resp. `RegularEpiCategory`s.

-/

@[expose] public section


noncomputable section

namespace CategoryTheory

open CategoryTheory.Limits

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C]
variable {X Y : C}

section

variable [HasZeroMorphisms C]

/--
Definition of `NormalMono` / `NormalMono` 的定义

English:
class NormalMono
  parameters: (f : X ⟶ Y)
  axioms and operations (4):
    - Z : C
    - g : Y ⟶ Z
    - w : f ≫ g = 0
    - isLimit : IsLimit (KernelFork.ofι f w)

中文:
类 正规单态射
  参数: (f : X ⟶ Y)
  公理与运算 (4 个):
    - Z : C
    - g : Y ⟶ Z
    - w : f ≫ g = 0
    - isLimit : 是极限 (核叉.ofι f w)
-/
class NormalMono (f : X ⟶ Y) where
  Z : C
  g : Y ⟶ Z
  w : f ≫ g = 0
  isLimit : IsLimit (KernelFork.ofι f w)

attribute [inherit_doc NormalMono] NormalMono.Z NormalMono.g NormalMono.w NormalMono.isLimit

section

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- If `F` is an equivalence and `F.map f` is a normal mono, then `f` is a normal mono. -/
@[instance_reducible]
/--
Definition of `equivalenceReflectsNormalMono` / `equivalenceReflectsNormalMono` 的定义

English:
definition equivalenceReflectsNormalMono
  signature: {D : Type u₂} [Category.{v₁} D] [HasZeroMorphisms D] (F : C ⥤ D)
  body: F.objPreimage hf.Z
  g := F.preimage (hf.g ≫ (F.objObjPreimageIso hf.Z).inv)
w := F.map_injective by
    have reassoc' {W : D} (h : hf.Z ⟶ W) : F.map f ≫ hf.g ≫ h = 0 ≫ h := by
      rw [← Category.assoc]; rw [eq_whisker hf.w]
    simp [reassoc']
isLimit := isLimitOfReflects F
IsLimit.ofConeEquiv (C

中文:
定义 equivalenceReflectsNormalMono
  签名: {D : 类型u₂} [范畴.{v₁} D] [有ZeroMorphisms D] (F : C ⥤ D)
  定义体: F.objPreimage hf.Z
  g := F.preimage (hf.g ≫ (F.objObjPreimageIso hf.Z).inv)
w := F.map_injective by
    have reassoc' {W : D} (h : hf.Z ⟶ W) : F.map f ≫ hf.g ≫ h = 0 ≫ h := by
      rw [← Category.assoc]; rw [eq_whisker hf.w]
    simp [reassoc']
isLimit := isLimitOfReflects F
IsLimit.ofConeEquiv (C

Depends on / 依赖: F.objPreimage, hf.Z, objPreimage
-/
def equivalenceReflectsNormalMono {D : Type u₂} [Category.{v₁} D] [HasZeroMorphisms D] (F : C ⥤ D)
    [F.IsEquivalence] {X Y : C} {f : X ⟶ Y} (hf : NormalMono (F.map f)) : NormalMono f where
  Z := F.objPreimage hf.Z
  g := F.preimage (hf.g ≫ (F.objObjPreimageIso hf.Z).inv)
w := F.map_injective by
    have reassoc' {W : D} (h : hf.Z ⟶ W) : F.map f ≫ hf.g ≫ h = 0 ≫ h := by
      rw [← Category.assoc]; rw [eq_whisker hf.w]
    simp [reassoc']
isLimit := isLimitOfReflects F
IsLimit.ofConeEquiv (Cone.postcomposeEquivalence (compNatIso F))
      (IsLimit.ofIsoLimit (IsKernel.ofCompIso _ _ (F.objObjPreimageIso hf.Z) (by
        simp only [Functor.map_preimage, Category.assoc, Iso.inv_hom_id, Category.comp_id])
        hf.isLimit)) (Fork.ext (Iso.refl _) (by simp [compNatIso, Fork.ι]))

end

/--
Definition of `NormalMono.regularMono` / `NormalMono.regularMono` 的定义

English:
definition NormalMono.regularMono
  signature: (f : X ⟶ Y) [I : NormalMono f]
  body: { I with
    left := I.g
    right := 0
    w := by simpa using I.w }

中文:
定义 正规单态射.regularMono
  签名: (f : X ⟶ Y) [I : 正规单态射 f]
  定义体: { I with
    left := I.g
    right := 0
    w := by simpa using I.w }
-/
def NormalMono.regularMono (f : X ⟶ Y) [I : NormalMono f] : RegularMono f :=
  { I with
    left := I.g
    right := 0
    w := by simpa using I.w }

instance (priority := 100) (f : X ⟶ Y) [I : NormalMono f] : IsRegularMono f := ⟨⟨I.regularMono⟩⟩

/--
Definition of `NormalMono.lift'` / `NormalMono.lift'` 的定义

English:
definition NormalMono.lift'
  signature: {W : C} (f : X ⟶ Y) [hf : NormalMono f] (k : W ⟶ Y) (h : k ≫ hf.g = 0)
  body: KernelFork.IsLimit.lift' NormalMono.isLimit _ h

中文:
定义 正规单态射.lift'
  签名: {W : C} (f : X ⟶ Y) [hf : 正规单态射 f] (k : W ⟶ Y) (h : k ≫ hf.g = 0)
  定义体: KernelFork.IsLimit.lift' NormalMono.isLimit _ h

Depends on / 依赖: IsLimit, KernelFork, KernelFork.IsLimit.lift, NormalMono, NormalMono.isLimit, isLimit
-/
def NormalMono.lift' {W : C} (f : X ⟶ Y) [hf : NormalMono f] (k : W ⟶ Y) (h : k ≫ hf.g = 0) :
    { l : W ⟶ X // l ≫ f = k } :=
  KernelFork.IsLimit.lift' NormalMono.isLimit _ h

/-- The second leg of a pullback cone is a normal monomorphism if the right component is too.

See also `pullback.sndOfMono` for the basic monomorphism version, and
`normalOfIsPullbackFstOfNormal` for the flipped version.
-/
@[instance_reducible]
/--
Definition of `normalOfIsPullbackSndOfNormal` / `normalOfIsPullbackSndOfNormal` 的定义

English:
definition normalOfIsPullbackSndOfNormal
  signature: {P Q R S : C} {f : P ⟶ Q} {g : P ⟶ R} {h : Q ⟶ S} {k : R ⟶ S}
  body: hn.Z
  g := k ≫ hn.g
  w := by
    have reassoc' {W : C} (h' : S ⟶ W) : f ≫ h ≫ h' = g ≫ k ≫ h' := by
      simp only [← Category.assoc, eq_whisker comm]
    rw [← reassoc']; rw [hn.w]; rw [HasZeroMorphisms.comp_zero]
  isLimit := by
    letI gr := regularOfIsPullbackSndOfRegular hn.regularMono comm

中文:
定义 normalOfIsPullbackSndOfNormal
  签名: {P Q R S : C} {f : P ⟶ Q} {g : P ⟶ R} {h : Q ⟶ S} {k : R ⟶ S}
  定义体: hn.Z
  g := k ≫ hn.g
  w := by
    have reassoc' {W : C} (h' : S ⟶ W) : f ≫ h ≫ h' = g ≫ k ≫ h' := by
      simp only [← Category.assoc, eq_whisker comm]
    rw [← reassoc']; rw [hn.w]; rw [HasZeroMorphisms.comp_zero]
  isLimit := by
    letI gr := regularOfIsPullbackSndOfRegular hn.regularMono comm

Depends on / 依赖: hn.Z
-/
def normalOfIsPullbackSndOfNormal {P Q R S : C} {f : P ⟶ Q} {g : P ⟶ R} {h : Q ⟶ S} {k : R ⟶ S}
    [hn : NormalMono h] (comm : f ≫ h = g ≫ k) (t : IsLimit (PullbackCone.mk _ _ comm)) :
    NormalMono g where
  Z := hn.Z
  g := k ≫ hn.g
  w := by
    have reassoc' {W : C} (h' : S ⟶ W) : f ≫ h ≫ h' = g ≫ k ≫ h' := by
      simp only [← Category.assoc, eq_whisker comm]
    rw [← reassoc']; rw [hn.w]; rw [HasZeroMorphisms.comp_zero]
  isLimit := by
    letI gr := regularOfIsPullbackSndOfRegular hn.regularMono comm t
    have q := (HasZeroMorphisms.comp_zero k hn.Z).symm
    convert! gr.isLimit

/-- The first leg of a pullback cone is a normal monomorphism if the left component is too.

See also `pullback.fstOfMono` for the basic monomorphism version, and
`normalOfIsPullbackSndOfNormal` for the flipped version.
-/
@[instance_reducible]
/--
Definition of `normalOfIsPullbackFstOfNormal` / `normalOfIsPullbackFstOfNormal` 的定义

English:
definition normalOfIsPullbackFstOfNormal
  signature: {P Q R S : C} {f : P ⟶ Q} {g : P ⟶ R} {h : Q ⟶ S} {k : R ⟶ S}
  body: normalOfIsPullbackSndOfNormal comm.symm (PullbackCone.flipIsLimit t)

中文:
定义 normalOfIsPullbackFstOfNormal
  签名: {P Q R S : C} {f : P ⟶ Q} {g : P ⟶ R} {h : Q ⟶ S} {k : R ⟶ S}
  定义体: normalOfIsPullbackSndOfNormal comm.symm (PullbackCone.flipIsLimit t)

Depends on / 依赖: Discrete, Discrete.instSubsingletonDiscreteHom, PullbackCone, PullbackCone.flipIsLimit, comm.symm, flipIsLimit, instSubsingletonDiscreteHom, normalOfIsPullbackSndOfNormal
-/
def normalOfIsPullbackFstOfNormal {P Q R S : C} {f : P ⟶ Q} {g : P ⟶ R} {h : Q ⟶ S} {k : R ⟶ S}
    [NormalMono k] (comm : f ≫ h = g ≫ k) (t : IsLimit (PullbackCone.mk _ _ comm)) :
    NormalMono f :=
  normalOfIsPullbackSndOfNormal comm.symm (PullbackCone.flipIsLimit t)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Transport a `NormalMono` structure via an isomorphism of arrows. -/
@[instance_reducible]
/--
Definition of `NormalMono.ofArrowIso` / `NormalMono.ofArrowIso` 的定义

English:
definition NormalMono.ofArrowIso
  signature: {X Y : C} {f : X ⟶ Y}
  body: hf.Z
  g := e.inv.right ≫ hf.g
  w := by
    have := Arrow.w e.inv
    dsimp at this
    rw [← reassoc_of% this]; rw [hf.w]; rw [comp_zero]
  isLimit := by
    refine (IsLimit.equivOfNatIsoOfIso ?_ _ _ ?_).1 hf.isLimit
    · exact parallelPair.ext (Arrow.rightFunc.mapIso e) (Iso.refl _)
    · exact 

中文:
定义 正规单态射.ofArrowIso
  签名: {X Y : C} {f : X ⟶ Y}
  定义体: hf.Z
  g := e.inv.right ≫ hf.g
  w := by
    have := Arrow.w e.inv
    dsimp at this
    rw [← reassoc_of% this]; rw [hf.w]; rw [comp_zero]
  isLimit := by
    refine (IsLimit.equivOfNatIsoOfIso ?_ _ _ ?_).1 hf.isLimit
    · exact parallelPair.ext (Arrow.rightFunc.mapIso e) (Iso.refl _)
    · exact 

Depends on / 依赖: hf.Z
-/
def NormalMono.ofArrowIso {X Y : C} {f : X ⟶ Y}
    (hf : NormalMono f) {X' Y' : C} {f' : X' ⟶ Y'} (e : Arrow.mk f ≅ Arrow.mk f') :
    NormalMono f' where
  Z := hf.Z
  g := e.inv.right ≫ hf.g
  w := by
    have := Arrow.w e.inv
    dsimp at this
    rw [← reassoc_of% this]; rw [hf.w]; rw [comp_zero]
  isLimit := by
    refine (IsLimit.equivOfNatIsoOfIso ?_ _ _ ?_).1 hf.isLimit
    · exact parallelPair.ext (Arrow.rightFunc.mapIso e) (Iso.refl _)
    · exact Fork.ext (Arrow.leftFunc.mapIso e)

section

variable (C)

/--
Definition of `IsNormalMonoCategory` / `IsNormalMonoCategory` 的定义

English:
class IsNormalMonoCategory
  parameters: : Prop where
  axioms and operations (1):
    - normalMonoOfMono : forall {X Y : C} (f : X ⟶ Y) [Mono f], Nonempty (NormalMono f)

中文:
类 是正规单态射范畴
  参数: : 命题 where
  公理与运算 (1 个):
    - normalMonoOfMono : 对任意 {X Y : C} (f : X ⟶ Y) [单态射 f], 非空 (正规单态射 f)
-/
class IsNormalMonoCategory : Prop where
  normalMonoOfMono : forall {X Y : C} (f : X ⟶ Y) [Mono f], Nonempty (NormalMono f)

attribute [inherit_doc IsNormalMonoCategory] IsNormalMonoCategory.normalMonoOfMono

end

/-- In a category in which every monomorphism is normal, we can express every monomorphism as
a kernel. This is not an instance because it would create an instance loop. -/
@[instance_reducible]
/--
Definition of `normalMonoOfMono` / `normalMonoOfMono` 的定义

English:
definition normalMonoOfMono
  signature: [IsNormalMonoCategory C] (f : X ⟶ Y) [Mono f]
  body: (IsNormalMonoCategory.normalMonoOfMono _).some

中文:
定义 normalMonoOfMono
  签名: [是正规单态射范畴 C] (f : X ⟶ Y) [单态射 f]
  定义体: (IsNormalMonoCategory.normalMonoOfMono _).some

Depends on / 依赖: IsNormalMonoCategory, IsNormalMonoCategory.normalMonoOfMono, normalMonoOfMono
-/
def normalMonoOfMono [IsNormalMonoCategory C] (f : X ⟶ Y) [Mono f] : NormalMono f :=
  (IsNormalMonoCategory.normalMonoOfMono _).some

instance (priority := 100) regularMonoCategoryOfNormalMonoCategory [IsNormalMonoCategory C] :
    IsRegularMonoCategory C where
  regularMonoOfMono f _ := by
    have := normalMonoOfMono f
    infer_instance

end

section

variable [HasZeroMorphisms C]

/--
Definition of `NormalEpi` / `NormalEpi` 的定义

English:
class NormalEpi
  parameters: (f : X ⟶ Y)
  axioms and operations (4):
    - W : C
    - g : W ⟶ X
    - w : g ≫ f = 0
    - isColimit : IsColimit (CokernelCofork.ofπ f w)

中文:
类 正规满态射
  参数: (f : X ⟶ Y)
  公理与运算 (4 个):
    - W : C
    - g : W ⟶ X
    - w : g ≫ f = 0
    - isColimit : 是余极限 (余核余叉.ofπ f w)
-/
class NormalEpi (f : X ⟶ Y) where
  W : C
  g : W ⟶ X
  w : g ≫ f = 0
  isColimit : IsColimit (CokernelCofork.ofπ f w)

attribute [inherit_doc NormalEpi] NormalEpi.W NormalEpi.g NormalEpi.w NormalEpi.isColimit

section

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- If `F` is an equivalence and `F.map f` is a normal epi, then `f` is a normal epi. -/
@[instance_reducible]
/--
Definition of `equivalenceReflectsNormalEpi` / `equivalenceReflectsNormalEpi` 的定义

English:
definition equivalenceReflectsNormalEpi
  signature: {D : Type u₂} [Category.{v₁} D] [HasZeroMorphisms D] (F : C ⥤ D)
  body: F.objPreimage hf.W
  g := F.preimage ((F.objObjPreimageIso hf.W).hom ≫ hf.g)
w := F.map_injective by simp [hf.w]
isColimit := isColimitOfReflects F
IsColimit.ofCoconeEquiv (Cocone.precomposeEquivalence (compNatIso F))
      (IsColimit.ofIsoColimit
        (IsCokernel.ofIsoComp _ _ (F.objObjPreimageI

中文:
定义 equivalenceReflectsNormalEpi
  签名: {D : 类型u₂} [范畴.{v₁} D] [有ZeroMorphisms D] (F : C ⥤ D)
  定义体: F.objPreimage hf.W
  g := F.preimage ((F.objObjPreimageIso hf.W).hom ≫ hf.g)
w := F.map_injective by simp [hf.w]
isColimit := isColimitOfReflects F
IsColimit.ofCoconeEquiv (Cocone.precomposeEquivalence (compNatIso F))
      (IsColimit.ofIsoColimit
        (IsCokernel.ofIsoComp _ _ (F.objObjPreimageI

Depends on / 依赖: F.objPreimage, hf.W, objPreimage
-/
def equivalenceReflectsNormalEpi {D : Type u₂} [Category.{v₁} D] [HasZeroMorphisms D] (F : C ⥤ D)
    [F.IsEquivalence] {X Y : C} {f : X ⟶ Y} (hf : NormalEpi (F.map f)) : NormalEpi f where
  W := F.objPreimage hf.W
  g := F.preimage ((F.objObjPreimageIso hf.W).hom ≫ hf.g)
w := F.map_injective by simp [hf.w]
isColimit := isColimitOfReflects F
IsColimit.ofCoconeEquiv (Cocone.precomposeEquivalence (compNatIso F))
      (IsColimit.ofIsoColimit
        (IsCokernel.ofIsoComp _ _ (F.objObjPreimageIso hf.W).symm (by simp) hf.isColimit)
          (Cofork.ext (Iso.refl _) (by simp [compNatIso, Cofork.π])))

end

/--
Definition of `NormalEpi.regularEpi` / `NormalEpi.regularEpi` 的定义

English:
definition NormalEpi.regularEpi
  signature: (f : X ⟶ Y) [I : NormalEpi f]
  body: { I with
    left := I.g
    right := 0
    w := by simpa using I.w }

中文:
定义 正规满态射.regularEpi
  签名: (f : X ⟶ Y) [I : 正规满态射 f]
  定义体: { I with
    left := I.g
    right := 0
    w := by simpa using I.w }
-/
def NormalEpi.regularEpi (f : X ⟶ Y) [I : NormalEpi f] : RegularEpi f :=
  { I with
    left := I.g
    right := 0
    w := by simpa using I.w }

instance (priority := 100) (f : X ⟶ Y) [I : NormalEpi f] : IsRegularEpi f := ⟨⟨I.regularEpi⟩⟩

/--
Definition of `NormalEpi.desc'` / `NormalEpi.desc'` 的定义

English:
definition NormalEpi.desc'
  signature: {W : C} (f : X ⟶ Y) [nef : NormalEpi f] (k : X ⟶ W) (h : nef.g ≫ k = 0)
  body: CokernelCofork.IsColimit.desc' NormalEpi.isColimit _ h

中文:
定义 正规满态射.desc'
  签名: {W : C} (f : X ⟶ Y) [nef : 正规满态射 f] (k : X ⟶ W) (h : nef.g ≫ k = 0)
  定义体: CokernelCofork.IsColimit.desc' NormalEpi.isColimit _ h

Depends on / 依赖: CokernelCofork, CokernelCofork.IsColimit.desc, IsColimit, NormalEpi, NormalEpi.isColimit, isColimit
-/
def NormalEpi.desc' {W : C} (f : X ⟶ Y) [nef : NormalEpi f] (k : X ⟶ W) (h : nef.g ≫ k = 0) :
    { l : Y ⟶ W // f ≫ l = k } :=
  CokernelCofork.IsColimit.desc' NormalEpi.isColimit _ h

/-- The second leg of a pushout cocone is a normal epimorphism if the right component is too.

See also `pushout.sndOfEpi` for the basic epimorphism version, and
`normalOfIsPushoutFstOfNormal` for the flipped version.
-/
@[instance_reducible]
/--
Definition of `normalOfIsPushoutSndOfNormal` / `normalOfIsPushoutSndOfNormal` 的定义

English:
definition normalOfIsPushoutSndOfNormal
  signature: {P Q R S : C} {f : P ⟶ Q} {g : P ⟶ R} {h : Q ⟶ S} {k : R ⟶ S}
  body: gn.W
  g := gn.g ≫ f
  w := by
    have reassoc' {W : C} (h' : R ⟶ W) : gn.g ≫ g ≫ h' = 0 ≫ h' := by
      rw [← Category.assoc]; rw [eq_whisker gn.w]
    rw [Category.assoc]; rw [comm]; rw [reassoc']; rw [zero_comp]
  isColimit := by
    letI hn := regularOfIsPushoutSndOfRegular gn.regularEpi comm 

中文:
定义 normalOfIsPushoutSndOfNormal
  签名: {P Q R S : C} {f : P ⟶ Q} {g : P ⟶ R} {h : Q ⟶ S} {k : R ⟶ S}
  定义体: gn.W
  g := gn.g ≫ f
  w := by
    have reassoc' {W : C} (h' : R ⟶ W) : gn.g ≫ g ≫ h' = 0 ≫ h' := by
      rw [← Category.assoc]; rw [eq_whisker gn.w]
    rw [Category.assoc]; rw [comm]; rw [reassoc']; rw [zero_comp]
  isColimit := by
    letI hn := regularOfIsPushoutSndOfRegular gn.regularEpi comm 

Depends on / 依赖: gn.W
-/
def normalOfIsPushoutSndOfNormal {P Q R S : C} {f : P ⟶ Q} {g : P ⟶ R} {h : Q ⟶ S} {k : R ⟶ S}
    [gn : NormalEpi g] (comm : f ≫ h = g ≫ k) (t : IsColimit (PushoutCocone.mk _ _ comm)) :
    NormalEpi h where
  W := gn.W
  g := gn.g ≫ f
  w := by
    have reassoc' {W : C} (h' : R ⟶ W) : gn.g ≫ g ≫ h' = 0 ≫ h' := by
      rw [← Category.assoc]; rw [eq_whisker gn.w]
    rw [Category.assoc]; rw [comm]; rw [reassoc']; rw [zero_comp]
  isColimit := by
    letI hn := regularOfIsPushoutSndOfRegular gn.regularEpi comm t
    have q := (@zero_comp _ _ _ gn.W _ _ f).symm
    convert! hn.isColimit

/-- The first leg of a pushout cocone is a normal epimorphism if the left component is too.

See also `pushout.fstOfEpi` for the basic epimorphism version, and
`normalOfIsPushoutSndOfNormal` for the flipped version.
-/
@[instance_reducible]
/--
Definition of `normalOfIsPushoutFstOfNormal` / `normalOfIsPushoutFstOfNormal` 的定义

English:
definition normalOfIsPushoutFstOfNormal
  signature: {P Q R S : C} {f : P ⟶ Q} {g : P ⟶ R} {h : Q ⟶ S} {k : R ⟶ S}
  body: normalOfIsPushoutSndOfNormal comm.symm (PushoutCocone.flipIsColimit t)

中文:
定义 normalOfIsPushoutFstOfNormal
  签名: {P Q R S : C} {f : P ⟶ Q} {g : P ⟶ R} {h : Q ⟶ S} {k : R ⟶ S}
  定义体: normalOfIsPushoutSndOfNormal comm.symm (PushoutCocone.flipIsColimit t)

Depends on / 依赖: PushoutCocone, PushoutCocone.flipIsColimit, comm.symm, flipIsColimit, normalOfIsPushoutSndOfNormal
-/
def normalOfIsPushoutFstOfNormal {P Q R S : C} {f : P ⟶ Q} {g : P ⟶ R} {h : Q ⟶ S} {k : R ⟶ S}
    [NormalEpi f] (comm : f ≫ h = g ≫ k) (t : IsColimit (PushoutCocone.mk _ _ comm)) :
    NormalEpi k :=
  normalOfIsPushoutSndOfNormal comm.symm (PushoutCocone.flipIsColimit t)

end

open Opposite

variable [HasZeroMorphisms C]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Transport a `NormalEpi` structure via an isomorphism of arrows. -/
@[instance_reducible]
/--
Definition of `NormalEpi.ofArrowIso` / `NormalEpi.ofArrowIso` 的定义

English:
definition NormalEpi.ofArrowIso
  signature: {X Y : C} {f : X ⟶ Y}
  body: hf.W
  g := hf.g ≫ e.hom.left
  w := by
    have := Arrow.w e.hom
    dsimp at this
    rw [Category.assoc]; rw [this]; rw [reassoc_of% hf.w]; rw [zero_comp]
  isColimit := by
    refine (IsColimit.equivOfNatIsoOfIso ?_ _ _ ?_).1 hf.isColimit
    · exact parallelPair.ext (Iso.refl _) (Arrow.leftFunc

中文:
定义 正规满态射.ofArrowIso
  签名: {X Y : C} {f : X ⟶ Y}
  定义体: hf.W
  g := hf.g ≫ e.hom.left
  w := by
    have := Arrow.w e.hom
    dsimp at this
    rw [Category.assoc]; rw [this]; rw [reassoc_of% hf.w]; rw [zero_comp]
  isColimit := by
    refine (IsColimit.equivOfNatIsoOfIso ?_ _ _ ?_).1 hf.isColimit
    · exact parallelPair.ext (Iso.refl _) (Arrow.leftFunc

Depends on / 依赖: hf.W
-/
def NormalEpi.ofArrowIso {X Y : C} {f : X ⟶ Y}
    (hf : NormalEpi f) {X' Y' : C} {f' : X' ⟶ Y'} (e : Arrow.mk f ≅ Arrow.mk f') :
    NormalEpi f' where
  W := hf.W
  g := hf.g ≫ e.hom.left
  w := by
    have := Arrow.w e.hom
    dsimp at this
    rw [Category.assoc]; rw [this]; rw [reassoc_of% hf.w]; rw [zero_comp]
  isColimit := by
    refine (IsColimit.equivOfNatIsoOfIso ?_ _ _ ?_).1 hf.isColimit
    · exact parallelPair.ext (Iso.refl _) (Arrow.leftFunc.mapIso e)
    · exact Cofork.ext (Arrow.rightFunc.mapIso e) (by simp [Cofork.π])


set_option backward.defeqAttrib.useBackward true in
/-- A normal mono becomes a normal epi in the opposite category. -/
@[instance_reducible]
/--
Definition of `normalEpiOfNormalMonoUnop` / `normalEpiOfNormalMonoUnop` 的定义

English:
definition normalEpiOfNormalMonoUnop
  signature: {X Y : Cᵒᵖ} (f : X ⟶ Y) (m : NormalMono f.unop)
  body: op m.Z
  g := m.g.op
  w := congrArg Quiver.Hom.op m.w
  isColimit :=
    CokernelCofork.IsColimit.ofπ _ _
      (fun g' w' =>
        (KernelFork.IsLimit.lift' m.isLimit g'.unop (congrArg Quiver.Hom.unop w')).1.op)
      (fun g' w' =>
        congrArg Quiver.Hom.op
          (KernelFork.IsLimit.lif

中文:
定义 normalEpiOfNormalMonoUnop
  签名: {X Y : Cᵒᵖ} (f : X ⟶ Y) (m : 正规单态射 f.unop)
  定义体: op m.Z
  g := m.g.op
  w := congrArg Quiver.Hom.op m.w
  isColimit :=
    CokernelCofork.IsColimit.ofπ _ _
      (fun g' w' =>
        (KernelFork.IsLimit.lift' m.isLimit g'.unop (congrArg Quiver.Hom.unop w')).1.op)
      (fun g' w' =>
        congrArg Quiver.Hom.op
          (KernelFork.IsLimit.lif
-/
def normalEpiOfNormalMonoUnop {X Y : Cᵒᵖ} (f : X ⟶ Y) (m : NormalMono f.unop) : NormalEpi f where
  W := op m.Z
  g := m.g.op
  w := congrArg Quiver.Hom.op m.w
  isColimit :=
    CokernelCofork.IsColimit.ofπ _ _
      (fun g' w' =>
        (KernelFork.IsLimit.lift' m.isLimit g'.unop (congrArg Quiver.Hom.unop w')).1.op)
      (fun g' w' =>
        congrArg Quiver.Hom.op
          (KernelFork.IsLimit.lift' m.isLimit g'.unop (congrArg Quiver.Hom.unop w')).2)
      (by
        rintro Z' g' w' m' rfl
        apply Quiver.Hom.unop_inj
        apply m.isLimit.uniq (KernelFork.ofι (m'.unop ≫ f.unop) _) m'.unop
        rintro (⟨⟩ | ⟨⟩) <;> simp)

set_option backward.defeqAttrib.useBackward true in
/-- A normal epi becomes a normal mono in the opposite category. -/
@[instance_reducible]
/--
Definition of `normalMonoOfNormalEpiUnop` / `normalMonoOfNormalEpiUnop` 的定义

English:
definition normalMonoOfNormalEpiUnop
  signature: {X Y : Cᵒᵖ} (f : X ⟶ Y) (m : NormalEpi f.unop)
  body: op m.W
  g := m.g.op
  w := congrArg Quiver.Hom.op m.w
  isLimit :=
    KernelFork.IsLimit.ofι _ _
      (fun g' w' =>
        (CokernelCofork.IsColimit.desc' m.isColimit g'.unop (congrArg Quiver.Hom.unop w')).1.op)
      (fun g' w' =>
        congrArg Quiver.Hom.op
          (CokernelCofork.IsColim

中文:
定义 normalMonoOfNormalEpiUnop
  签名: {X Y : Cᵒᵖ} (f : X ⟶ Y) (m : 正规满态射 f.unop)
  定义体: op m.W
  g := m.g.op
  w := congrArg Quiver.Hom.op m.w
  isLimit :=
    KernelFork.IsLimit.ofι _ _
      (fun g' w' =>
        (CokernelCofork.IsColimit.desc' m.isColimit g'.unop (congrArg Quiver.Hom.unop w')).1.op)
      (fun g' w' =>
        congrArg Quiver.Hom.op
          (CokernelCofork.IsColim
-/
def normalMonoOfNormalEpiUnop {X Y : Cᵒᵖ} (f : X ⟶ Y) (m : NormalEpi f.unop) : NormalMono f where
  Z := op m.W
  g := m.g.op
  w := congrArg Quiver.Hom.op m.w
  isLimit :=
    KernelFork.IsLimit.ofι _ _
      (fun g' w' =>
        (CokernelCofork.IsColimit.desc' m.isColimit g'.unop (congrArg Quiver.Hom.unop w')).1.op)
      (fun g' w' =>
        congrArg Quiver.Hom.op
          (CokernelCofork.IsColimit.desc' m.isColimit g'.unop (congrArg Quiver.Hom.unop w')).2)
      (by
        rintro Z' g' w' m' rfl
        apply Quiver.Hom.unop_inj
        apply m.isColimit.uniq (CokernelCofork.ofπ (f.unop ≫ m'.unop) _) m'.unop
        rintro (⟨⟩ | ⟨⟩) <;> simp)

section

variable (C)

/--
Definition of `IsNormalEpiCategory` / `IsNormalEpiCategory` 的定义

English:
class IsNormalEpiCategory
  parameters: : Prop where
  axioms and operations (1):
    - normalEpiOfEpi : forall {X Y : C} (f : X ⟶ Y) [Epi f], Nonempty (NormalEpi f)

中文:
类 是正规满态射范畴
  参数: : 命题 where
  公理与运算 (1 个):
    - normalEpiOfEpi : 对任意 {X Y : C} (f : X ⟶ Y) [满态射 f], 非空 (正规满态射 f)
-/
class IsNormalEpiCategory : Prop where
  normalEpiOfEpi : forall {X Y : C} (f : X ⟶ Y) [Epi f], Nonempty (NormalEpi f)

attribute [inherit_doc IsNormalEpiCategory] IsNormalEpiCategory.normalEpiOfEpi

end

/-- In a category in which every epimorphism is normal, we can express every epimorphism as
a kernel. This is not an instance because it would create an instance loop. -/
@[instance_reducible]
/--
Definition of `normalEpiOfEpi` / `normalEpiOfEpi` 的定义

English:
definition normalEpiOfEpi
  signature: [IsNormalEpiCategory C] (f : X ⟶ Y) [Epi f]
  body: (IsNormalEpiCategory.normalEpiOfEpi _).some

中文:
定义 normalEpiOfEpi
  签名: [是正规满态射范畴 C] (f : X ⟶ Y) [满态射 f]
  定义体: (IsNormalEpiCategory.normalEpiOfEpi _).some

Depends on / 依赖: IsNormalEpiCategory, IsNormalEpiCategory.normalEpiOfEpi, normalEpiOfEpi
-/
def normalEpiOfEpi [IsNormalEpiCategory C] (f : X ⟶ Y) [Epi f] : NormalEpi f :=
  (IsNormalEpiCategory.normalEpiOfEpi _).some

instance (priority := 100) regularEpiCategoryOfNormalEpiCategory [IsNormalEpiCategory C] :
    IsRegularEpiCategory C where
  regularEpiOfEpi f _ := by
    have := normalEpiOfEpi f
    infer_instance

end CategoryTheory
