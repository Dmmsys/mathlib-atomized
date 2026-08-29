/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero

/-!
# Preservation of biproducts

We define the image of a (binary) bicone under a functor that preserves zero morphisms and define
classes `PreservesBiproduct` and `PreservesBinaryBiproduct`. We then

* show that a functor that preserves biproducts of a two-element type preserves binary biproducts,
* construct the comparison morphisms between the image of a biproduct and the biproduct of the
  images and show that the biproduct is preserved if one of them is an isomorphism,
* give the canonical isomorphism between the image of a biproduct and the biproduct of the images
  in case that the biproduct is preserved.

-/

@[expose] public section


universe w₁ w₂ v₁ v₂ u₁ u₂

noncomputable section

open CategoryTheory

open CategoryTheory.Limits

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

section HasZeroMorphisms

variable [HasZeroMorphisms C] [HasZeroMorphisms D]

namespace Functor

section Map

variable (F : C ⥤ D) [PreservesZeroMorphisms F]

section Bicone

variable {J : Type w₁}

set_option backward.isDefEq.respectTransparency false in
/-- The image of a bicone under a functor. -/
@[simps]
/--
Definition of `mapBicone` / `mapBicone` 的定义

English:
definition mapBicone
  signature: {f : J -> C} (b : Bicone f)
  body: F.obj b.pt
  π j := F.map (b.π j)
  ι j := F.map (b.ι j)
  ι_π j j' := by
    rw [← F.map_comp]
    split_ifs with h
    · subst h
      simp only [bicone_ι_π_self, CategoryTheory.Functor.map_id, eqToHom_refl]; dsimp
    · rw [bicone_ι_π_ne _ h, F.map_zero]

中文:
定义 mapBicone
  签名: {f : J -> C} (b : Bicone f)
  定义体: F.obj b.pt
  π j := F.map (b.π j)
  ι j := F.map (b.ι j)
  ι_π j j' := by
    rw [← F.map_comp]
    split_ifs with h
    · subst h
      simp only [bicone_ι_π_self, CategoryTheory.Functor.map_id, eqToHom_refl]; dsimp
    · rw [bicone_ι_π_ne _ h, F.map_zero]

Depends on / 依赖: F.obj, b.pt
-/
def mapBicone {f : J -> C} (b : Bicone f) : Bicone (F.obj ∘ f) where
  pt := F.obj b.pt
  π j := F.map (b.π j)
  ι j := F.map (b.ι j)
  ι_π j j' := by
    rw [← F.map_comp]
    split_ifs with h
    · subst h
      simp only [bicone_ι_π_self, CategoryTheory.Functor.map_id, eqToHom_refl]; dsimp
    · rw [bicone_ι_π_ne _ h, F.map_zero]

/--
theorem `mapBicone_whisker` / 定理 `mapBicone_whisker`

English:
theorem mapBicone_whisker
  given: {K : Type w₂} {g : K ≃ J} {f : J -> C} (c : Bicone f)
  proof: rfl

中文:
定理 mapBicone_whisker
  条件: {K : 类型 w₂} {g : K ≃ J} {f : J -> C} (c : Bicone f)
  证明: rfl
-/
theorem mapBicone_whisker {K : Type w₂} {g : K ≃ J} {f : J -> C} (c : Bicone f) :
    F.mapBicone (c.whisker g) = (F.mapBicone c).whisker g :=
  rfl

end Bicone

/-- The image of a binary bicone under a functor. -/
@[simps!]
/--
Definition of `mapBinaryBicone` / `mapBinaryBicone` 的定义

English:
definition mapBinaryBicone
  signature: {X Y : C} (b : BinaryBicone X Y)
  body: (BinaryBicones.functoriality _ _ F).obj b

中文:
定义 mapBinaryBicone
  签名: {X Y : C} (b : BinaryBicone X Y)
  定义体: (BinaryBicones.functoriality _ _ F).obj b

Depends on / 依赖: BinaryBicones, BinaryBicones.functoriality, functoriality
-/
def mapBinaryBicone {X Y : C} (b : BinaryBicone X Y) : BinaryBicone (F.obj X) (F.obj Y) :=
  (BinaryBicones.functoriality _ _ F).obj b

end Map

end Functor

open CategoryTheory.Functor

namespace Limits

section Bicone

variable {J : Type w₁} {K : Type w₂}

/--
Definition of `PreservesBiproduct` / `PreservesBiproduct` 的定义

English:
class PreservesBiproduct
  parameters: (f : J -> C) (F : C ⥤ D) [PreservesZeroMorphisms F]
  axioms and operations (1):
    - preserves : forall {b : Bicone f}, b.IsBilimit -> Nonempty (F.mapBicone b).IsBilimit

中文:
类 保持Biproduct
  参数: (f : J -> C) (F : C ⥤ D) [保持ZeroMorphisms F]
  公理与运算 (1 个):
    - preserves : 对任意 {b : Bicone f}, b.是Bilimit -> 非空 (F.mapBicone b).是Bilimit
-/
class PreservesBiproduct (f : J -> C) (F : C ⥤ D) [PreservesZeroMorphisms F] : Prop where
  preserves : forall {b : Bicone f}, b.IsBilimit -> Nonempty (F.mapBicone b).IsBilimit

attribute [inherit_doc PreservesBiproduct] PreservesBiproduct.preserves

/--
Definition of `isBilimitOfPreserves` / `isBilimitOfPreserves` 的定义

English:
definition isBilimitOfPreserves
  signature: {f : J -> C} (F : C ⥤ D) [PreservesZeroMorphisms F] [PreservesBiproduct f F]
  body: (PreservesBiproduct.preserves hb).some

中文:
定义 isBilimitOfPreserves
  签名: {f : J -> C} (F : C ⥤ D) [保持ZeroMorphisms F] [保持Biproduct f F]
  定义体: (PreservesBiproduct.preserves hb).some

Depends on / 依赖: PreservesBiproduct, PreservesBiproduct.preserves, preserves
-/
def isBilimitOfPreserves {f : J -> C} (F : C ⥤ D) [PreservesZeroMorphisms F] [PreservesBiproduct f F]
    {b : Bicone f} (hb : b.IsBilimit) : (F.mapBicone b).IsBilimit :=
  (PreservesBiproduct.preserves hb).some

variable (J)

/--
Definition of `PreservesBiproductsOfShape` / `PreservesBiproductsOfShape` 的定义

English:
class PreservesBiproductsOfShape
  parameters: (F : C ⥤ D) [PreservesZeroMorphisms F]
  axioms and operations (1):
    - preserves : forall {f : J -> C}, PreservesBiproduct f F

中文:
类 保持BiproductsOfShape
  参数: (F : C ⥤ D) [保持ZeroMorphisms F]
  公理与运算 (1 个):
    - preserves : 对任意 {f : J -> C}, 保持Biproduct f F
-/
class PreservesBiproductsOfShape (F : C ⥤ D) [PreservesZeroMorphisms F] : Prop where
  preserves : forall {f : J -> C}, PreservesBiproduct f F

attribute [inherit_doc PreservesBiproductsOfShape] PreservesBiproductsOfShape.preserves

attribute [instance 100] PreservesBiproductsOfShape.preserves

end Bicone

/--
Definition of `PreservesFiniteBiproducts` / `PreservesFiniteBiproducts` 的定义

English:
class PreservesFiniteBiproducts
  parameters: (F : C ⥤ D) [PreservesZeroMorphisms F]
  axioms and operations (1):
    - preserves : forall {J : Type} [Finite J], PreservesBiproductsOfShape J F

中文:
类 保持FiniteBiproducts
  参数: (F : C ⥤ D) [保持ZeroMorphisms F]
  公理与运算 (1 个):
    - preserves : 对任意 {J : 类型} [有限 J], 保持BiproductsOfShape J F
-/
class PreservesFiniteBiproducts (F : C ⥤ D) [PreservesZeroMorphisms F] : Prop where
  preserves : forall {J : Type} [Finite J], PreservesBiproductsOfShape J F

attribute [inherit_doc PreservesFiniteBiproducts] PreservesFiniteBiproducts.preserves
attribute [instance 100] PreservesFiniteBiproducts.preserves

/--
Definition of `PreservesBiproducts` / `PreservesBiproducts` 的定义

English:
class PreservesBiproducts
  parameters: (F : C ⥤ D) [PreservesZeroMorphisms F]
  axioms and operations (1):
    - preserves : forall {J : Type w₁}, PreservesBiproductsOfShape J F

中文:
类 保持Biproducts
  参数: (F : C ⥤ D) [保持ZeroMorphisms F]
  公理与运算 (1 个):
    - preserves : 对任意 {J : 类型 w₁}, 保持BiproductsOfShape J F
-/
class PreservesBiproducts (F : C ⥤ D) [PreservesZeroMorphisms F] : Prop where
  preserves : forall {J : Type w₁}, PreservesBiproductsOfShape J F

attribute [inherit_doc PreservesBiproducts] PreservesBiproducts.preserves

attribute [instance 100] PreservesBiproducts.preserves

/--
lemma `preservesBiproducts_shrink` / 引理 `preservesBiproducts_shrink`

English:
lemma preservesBiproducts_shrink
  statement: (F : C ⥤ D) [PreservesZeroMorphisms F]
  proof: ⟨fun {_} =>
    ⟨fun {_} =>
      ⟨fun {b} ib =>
        ⟨((F.mapBicone b).whiskerIsBilimitIff _).toFun
          (isBilimitOfPreserves F ((b.whiskerIsBilimitIff Equiv.ulift.{w₂}).invFun ib))⟩⟩⟩⟩

中文:
引理 preservesBiproducts_shrink
  结论: (F : C ⥤ D) [保持ZeroMorphisms F]
  证明: ⟨fun {_} =>
    ⟨fun {_} =>
      ⟨fun {b} ib =>
        ⟨((F.mapBicone b).whiskerIsBilimitIff _).toFun
          (isBilimitOfPreserves F ((b.whiskerIsBilimitIff Equiv.ulift.{w₂}).invFun ib))⟩⟩⟩⟩

Depends on / 依赖: Equiv.ulift, F.mapBicone, b.whiskerIsBilimitIff, invFun, isBilimitOfPreserves, mapBicone, whiskerIsBilimitIff
-/
lemma preservesBiproducts_shrink (F : C ⥤ D) [PreservesZeroMorphisms F]
    [PreservesBiproducts.{max w₁ w₂} F] : PreservesBiproducts.{w₁} F :=
  ⟨fun {_} =>
    ⟨fun {_} =>
      ⟨fun {b} ib =>
        ⟨((F.mapBicone b).whiskerIsBilimitIff _).toFun
          (isBilimitOfPreserves F ((b.whiskerIsBilimitIff Equiv.ulift.{w₂}).invFun ib))⟩⟩⟩⟩

instance (priority := 100) preservesFiniteBiproductsOfPreservesBiproducts (F : C ⥤ D)
    [PreservesZeroMorphisms F] [PreservesBiproducts.{w₁} F] : PreservesFiniteBiproducts F where
  preserves {J} _ := by let := preservesBiproducts_shrink.{0} F; infer_instance

/--
Definition of `PreservesBinaryBiproduct` / `PreservesBinaryBiproduct` 的定义

English:
class PreservesBinaryBiproduct
  parameters: (X Y : C) (F : C ⥤ D) [PreservesZeroMorphisms F]
  axioms and operations (1):
    - preserves : forall {b : BinaryBicone X Y}, b.IsBilimit -> Nonempty ((F.mapBinaryBicone b).IsBilimit)

中文:
类 保持BinaryBiproduct
  参数: (X Y : C) (F : C ⥤ D) [保持ZeroMorphisms F]
  公理与运算 (1 个):
    - preserves : 对任意 {b : BinaryBicone X Y}, b.是Bilimit -> 非空 ((F.mapBinaryBicone b).是Bilimit)
-/
class PreservesBinaryBiproduct (X Y : C) (F : C ⥤ D) [PreservesZeroMorphisms F] : Prop where
  preserves : forall {b : BinaryBicone X Y}, b.IsBilimit -> Nonempty ((F.mapBinaryBicone b).IsBilimit)

attribute [inherit_doc PreservesBinaryBiproduct] PreservesBinaryBiproduct.preserves

/--
Definition of `isBinaryBilimitOfPreserves` / `isBinaryBilimitOfPreserves` 的定义

English:
definition isBinaryBilimitOfPreserves
  signature: {X Y : C} (F : C ⥤ D) [PreservesZeroMorphisms F]
  body: (PreservesBinaryBiproduct.preserves hb).some

中文:
定义 isBinaryBilimitOfPreserves
  签名: {X Y : C} (F : C ⥤ D) [保持ZeroMorphisms F]
  定义体: (PreservesBinaryBiproduct.preserves hb).some

Depends on / 依赖: PreservesBinaryBiproduct, PreservesBinaryBiproduct.preserves, preserves
-/
def isBinaryBilimitOfPreserves {X Y : C} (F : C ⥤ D) [PreservesZeroMorphisms F]
    [PreservesBinaryBiproduct X Y F] {b : BinaryBicone X Y} (hb : b.IsBilimit) :
    (F.mapBinaryBicone b).IsBilimit :=
  (PreservesBinaryBiproduct.preserves hb).some

/--
Definition of `PreservesBinaryBiproducts` / `PreservesBinaryBiproducts` 的定义

English:
class PreservesBinaryBiproducts
  parameters: (F : C ⥤ D) [PreservesZeroMorphisms F]
  axioms and operations (1):
    - preserves : forall {X Y : C}, PreservesBinaryBiproduct X Y F  [default: by infer_instance]

中文:
类 保持BinaryBiproducts
  参数: (F : C ⥤ D) [保持ZeroMorphisms F]
  公理与运算 (1 个):
    - preserves : 对任意 {X Y : C}, 保持BinaryBiproduct X Y F  [默认: by infer_instance]

Depends on / 依赖: infer_instance
-/
class PreservesBinaryBiproducts (F : C ⥤ D) [PreservesZeroMorphisms F] : Prop where
  preserves : forall {X Y : C}, PreservesBinaryBiproduct X Y F := by infer_instance

attribute [inherit_doc PreservesBinaryBiproducts] PreservesBinaryBiproducts.preserves

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `preservesBinaryBiproduct_of_preservesBiproduct` / 引理 `preservesBinaryBiproduct_of_preservesBiproduct`

English:
lemma preservesBinaryBiproduct_of_preservesBiproduct
  statement: (F : C ⥤ D)
  proof: ⟨{
      isLimit :=
        IsLimit.ofIsoLimit
            ((IsLimit.postcomposeHomEquiv (diagramIsoPair _) _).symm
              (isBilimitOfPreserves F (b.toBiconeIsBilimit.symm hb)).isLimit) <|
          Cone.ext (Iso.refl _) fun j => by
            rcases j with ⟨⟨⟩⟩ <;> simp
      isColimit :=


中文:
引理 preservesBinaryBiproduct_of_preservesBiproduct
  结论: (F : C ⥤ D)
  证明: ⟨{
      isLimit :=
        IsLimit.ofIsoLimit
            ((IsLimit.postcomposeHomEquiv (diagramIsoPair _) _).symm
              (isBilimitOfPreserves F (b.toBiconeIsBilimit.symm hb)).isLimit) <|
          Cone.ext (Iso.refl _) fun j => by
            rcases j with ⟨⟨⟩⟩ <;> simp
      isColimit :=

-/
lemma preservesBinaryBiproduct_of_preservesBiproduct (F : C ⥤ D)
    [PreservesZeroMorphisms F] (X Y : C) [PreservesBiproduct (pairFunction X Y) F] :
    PreservesBinaryBiproduct X Y F where
  preserves {b} hb := ⟨{
      isLimit :=
        IsLimit.ofIsoLimit
            ((IsLimit.postcomposeHomEquiv (diagramIsoPair _) _).symm
              (isBilimitOfPreserves F (b.toBiconeIsBilimit.symm hb)).isLimit) <|
          Cone.ext (Iso.refl _) fun j => by
            rcases j with ⟨⟨⟩⟩ <;> simp
      isColimit :=
        IsColimit.ofIsoColimit
            ((IsColimit.precomposeInvEquiv (diagramIsoPair _) _).symm
              (isBilimitOfPreserves F (b.toBiconeIsBilimit.symm hb)).isColimit) <|
          Cocone.ext (Iso.refl _) fun j => by
            rcases j with ⟨⟨⟩⟩ <;> simp }⟩

/--
lemma `preservesBinaryBiproducts_of_preservesBiproducts` / 引理 `preservesBinaryBiproducts_of_preservesBiproducts`

English:
lemma preservesBinaryBiproducts_of_preservesBiproducts
  statement: (F : C ⥤ D) [PreservesZeroMorphisms F]
  proof: preservesBinaryBiproduct_of_preservesBiproduct F X Y

中文:
引理 preservesBinaryBiproducts_of_preservesBiproducts
  结论: (F : C ⥤ D) [保持ZeroMorphisms F]
  证明: preservesBinaryBiproduct_of_preservesBiproduct F X Y

Depends on / 依赖: preservesBinaryBiproduct_of_preservesBiproduct
-/
lemma preservesBinaryBiproducts_of_preservesBiproducts (F : C ⥤ D) [PreservesZeroMorphisms F]
    [PreservesBiproductsOfShape WalkingPair F] : PreservesBinaryBiproducts F where
  preserves {X} Y := preservesBinaryBiproduct_of_preservesBiproduct F X Y

attribute [instance 100] PreservesBinaryBiproducts.preserves

end Limits

open CategoryTheory.Limits

namespace Functor

section Bicone

variable {J : Type w₁} (F : C ⥤ D) (f : J -> C) [HasBiproduct f]

section

variable [HasBiproduct (F.obj ∘ f)]

/--
Definition of `biproductComparison` / `biproductComparison` 的定义

English:
definition biproductComparison
  signature: : F.obj (⨁ f) ⟶ ⨁ F.obj ∘ f
  body: biproduct.lift fun j => F.map (biproduct.π f j)

@[reassoc (attr := simp)]

中文:
定义 biproductComparison
  签名: : F.obj (⨁ f) ⟶ ⨁ F.obj ∘ f
  定义体: biproduct.lift fun j => F.map (biproduct.π f j)

@[reassoc (attr := simp)]

Depends on / 依赖: F.map, biproduct, biproduct.lift
-/
def biproductComparison : F.obj (⨁ f) ⟶ ⨁ F.obj ∘ f :=
  biproduct.lift fun j => F.map (biproduct.π f j)

@[reassoc (attr := simp)]
/--
theorem `biproductComparison_π` / 定理 `biproductComparison_π`

English:
theorem biproductComparison_π
  given: (j : J)
  proof: biproduct.lift_π _ _

中文:
定理 biproductComparison_π
  条件: (j : J)
  证明: biproduct.lift_π _ _

Depends on / 依赖: biproduct, biproduct.lift_
-/
theorem biproductComparison_π (j : J) :
    biproductComparison F f ≫ biproduct.π _ j = F.map (biproduct.π f j) :=
  biproduct.lift_π _ _

/--
Definition of `biproductComparison'` / `biproductComparison'` 的定义

English:
definition biproductComparison'
  signature: : ⨁ F.obj ∘ f ⟶ F.obj (⨁ f)
  body: biproduct.desc fun j => F.map (biproduct.ι f j)

@[reassoc (attr := simp)]

中文:
定义 biproductComparison'
  签名: : ⨁ F.obj ∘ f ⟶ F.obj (⨁ f)
  定义体: biproduct.desc fun j => F.map (biproduct.ι f j)

@[reassoc (attr := simp)]

Depends on / 依赖: F.map, biproduct, biproduct.desc
-/
def biproductComparison' : ⨁ F.obj ∘ f ⟶ F.obj (⨁ f) :=
  biproduct.desc fun j => F.map (biproduct.ι f j)

@[reassoc (attr := simp)]
/--
theorem `ι_biproductComparison'` / 定理 `ι_biproductComparison'`

English:
theorem ι_biproductComparison'
  given: (j : J)
  proof: biproduct.ι_desc _ _

中文:
定理 ι_biproductComparison'
  条件: (j : J)
  证明: biproduct.ι_desc _ _

Depends on / 依赖: biproduct
-/
theorem ι_biproductComparison' (j : J) :
    biproduct.ι _ j ≫ biproductComparison' F f = F.map (biproduct.ι f j) :=
  biproduct.ι_desc _ _

variable [PreservesZeroMorphisms F]

set_option backward.isDefEq.respectTransparency false in
/-- The composition in the opposite direction is equal to the identity if and only if `F` preserves
the biproduct, see `preservesBiproduct_of_monoBiproductComparison`. -/
@[reassoc (attr := simp)]
/--
theorem `biproductComparison'_comp_biproductComparison` / 定理 `biproductComparison'_comp_biproductComparison`

English:
theorem biproductComparison'_comp_biproductComparison
  proof: by
  classical
    ext
    simp [biproduct.ι_π, ← Functor.map_comp, eqToHom_map]

中文:
定理 biproductComparison'_comp_biproductComparison
  证明: by
  classical
    ext
    simp [biproduct.ι_π, ← Functor.map_comp, eqToHom_map]
-/
theorem biproductComparison'_comp_biproductComparison :
    biproductComparison' F f ≫ biproductComparison F f = 𝟙 (⨁ F.obj ∘ f) := by
  classical
    ext
    simp [biproduct.ι_π, ← Functor.map_comp, eqToHom_map]

/-- `biproduct_comparison F f` is a split epimorphism. -/
@[simps]
/--
Definition of `splitEpiBiproductComparison` / `splitEpiBiproductComparison` 的定义

English:
definition splitEpiBiproductComparison
  signature: : SplitEpi (biproductComparison F f) where
  body: biproductComparison' F f
  id := by simp

中文:
定义 splitEpiBiproductComparison
  签名: : 分裂满态射 (biproductComparison F f) where
  定义体: biproductComparison' F f
  id := by simp
-/
def splitEpiBiproductComparison : SplitEpi (biproductComparison F f) where
  section_ := biproductComparison' F f
  id := by simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsSplitEpi (biproductComparison F f)
  body: IsSplitEpi.mk' (splitEpiBiproductComparison F f)

中文:
实例 :
  签名: 是分裂满态射 (biproductComparison F f)
  定义体: IsSplitEpi.mk' (splitEpiBiproductComparison F f)

Depends on / 依赖: IsSplitEpi, IsSplitEpi.mk, splitEpiBiproductComparison
-/
instance : IsSplitEpi (biproductComparison F f) :=
  IsSplitEpi.mk' (splitEpiBiproductComparison F f)

/-- `biproduct_comparison' F f` is a split monomorphism. -/
@[simps]
/--
Definition of `splitMonoBiproductComparison'` / `splitMonoBiproductComparison'` 的定义

English:
definition splitMonoBiproductComparison'
  signature: : SplitMono (biproductComparison' F f) where
  body: biproductComparison F f
  id := by simp

中文:
定义 splitMonoBiproductComparison'
  签名: : 分裂单态射 (biproductComparison' F f) where
  定义体: biproductComparison F f
  id := by simp

Depends on / 依赖: biproductComparison
-/
def splitMonoBiproductComparison' : SplitMono (biproductComparison' F f) where
  retraction := biproductComparison F f
  id := by simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsSplitMono (biproductComparison' F f)
  body: IsSplitMono.mk' (splitMonoBiproductComparison' F f)

中文:
实例 :
  签名: 是分裂单态射 (biproductComparison' F f)
  定义体: IsSplitMono.mk' (splitMonoBiproductComparison' F f)

Depends on / 依赖: IsSplitMono, IsSplitMono.mk, splitMonoBiproductComparison
-/
instance : IsSplitMono (biproductComparison' F f) :=
  IsSplitMono.mk' (splitMonoBiproductComparison' F f)

end

variable [PreservesZeroMorphisms F] [PreservesBiproduct f F]

/--
Instance `hasBiproduct_of_preserves` / 实例 `hasBiproduct_of_preserves`

English:
instance hasBiproduct_of_preserves
  signature: : HasBiproduct (F.obj ∘ f)
  body: HasBiproduct.mk
    { bicone := F.mapBicone (biproduct.bicone f)
      isBilimit := isBilimitOfPreserves _ (biproduct.isBilimit _) }

中文:
实例 hasBiproduct_of_preserves
  签名: : 有Biproduct (F.obj ∘ f)
  定义体: HasBiproduct.mk
    { bicone := F.mapBicone (biproduct.bicone f)
      isBilimit := isBilimitOfPreserves _ (biproduct.isBilimit _) }

Depends on / 依赖: F.mapBicone, HasBiproduct, HasBiproduct.mk, bicone, biproduct, biproduct.bicone, biproduct.isBilimit, isBilimit, isBilimitOfPreserves, mapBicone
-/
instance hasBiproduct_of_preserves : HasBiproduct (F.obj ∘ f) :=
  HasBiproduct.mk
    { bicone := F.mapBicone (biproduct.bicone f)
      isBilimit := isBilimitOfPreserves _ (biproduct.isBilimit _) }

/-- This instance applies more often than `hasBiproduct_of_preserves`, but the discrimination
tree key matches a lot more (since it does not look through lambdas). -/
instance (priority := low) hasBiproduct_of_preserves' : HasBiproduct fun i => F.obj (f i) :=
  HasBiproduct.mk
    { bicone := F.mapBicone (biproduct.bicone f)
      isBilimit := isBilimitOfPreserves _ (biproduct.isBilimit _) }

/--
Definition of `mapBiproduct` / `mapBiproduct` 的定义

English:
abbreviation mapBiproduct
  signature: : F.obj (⨁ f) ≅ ⨁ F.obj ∘ f
  body: biproduct.uniqueUpToIso _ (isBilimitOfPreserves _ (biproduct.isBilimit _))

中文:
缩写 mapBiproduct
  签名: : F.obj (⨁ f) ≅ ⨁ F.obj ∘ f
  定义体: biproduct.uniqueUpToIso _ (isBilimitOfPreserves _ (biproduct.isBilimit _))

Depends on / 依赖: biproduct, biproduct.isBilimit, biproduct.uniqueUpToIso, isBilimit, isBilimitOfPreserves, uniqueUpToIso
-/
abbrev mapBiproduct : F.obj (⨁ f) ≅ ⨁ F.obj ∘ f :=
  biproduct.uniqueUpToIso _ (isBilimitOfPreserves _ (biproduct.isBilimit _))

/--
theorem `mapBiproduct_hom` / 定理 `mapBiproduct_hom`

English:
theorem mapBiproduct_hom
  proof: rfl

中文:
定理 mapBiproduct_hom
  证明: rfl
-/
theorem mapBiproduct_hom :
    (mapBiproduct F f).hom = biproduct.lift fun j => F.map (biproduct.π f j) := rfl

/--
theorem `mapBiproduct_inv` / 定理 `mapBiproduct_inv`

English:
theorem mapBiproduct_inv
  proof: rfl

中文:
定理 mapBiproduct_inv
  证明: rfl
-/
theorem mapBiproduct_inv :
    (mapBiproduct F f).inv = biproduct.desc fun j => F.map (biproduct.ι f j) := rfl

end Bicone

variable (F : C ⥤ D) (X Y : C) [HasBinaryBiproduct X Y]

section

variable [HasBinaryBiproduct (F.obj X) (F.obj Y)]

/--
Definition of `biprodComparison` / `biprodComparison` 的定义

English:
definition biprodComparison
  signature: : F.obj (X ⊞ Y) ⟶ F.obj X ⊞ F.obj Y
  body: biprod.lift (F.map biprod.fst) (F.map biprod.snd)

@[reassoc (attr := simp)]

中文:
定义 biprodComparison
  签名: : F.obj (X ⊞ Y) ⟶ F.obj X ⊞ F.obj Y
  定义体: biprod.lift (F.map biprod.fst) (F.map biprod.snd)

@[reassoc (attr := simp)]

Depends on / 依赖: F.map, biprod, biprod.fst, biprod.lift, biprod.snd
-/
def biprodComparison : F.obj (X ⊞ Y) ⟶ F.obj X ⊞ F.obj Y :=
  biprod.lift (F.map biprod.fst) (F.map biprod.snd)

@[reassoc (attr := simp)]
/--
theorem `biprodComparison_fst` / 定理 `biprodComparison_fst`

English:
theorem biprodComparison_fst
  statement: biprodComparison F X Y ≫ biprod.fst = F.map biprod.fst
  proof: biprod.lift_fst _ _

@[reassoc (attr := simp)]

中文:
定理 biprodComparison_fst
  结论: biprodComparison F X Y ≫ biprod.fst = F.map biprod.fst
  证明: biprod.lift_fst _ _

@[reassoc (attr := simp)]

Depends on / 依赖: biprod, biprod.lift_fst, lift_fst
-/
theorem biprodComparison_fst : biprodComparison F X Y ≫ biprod.fst = F.map biprod.fst :=
  biprod.lift_fst _ _

@[reassoc (attr := simp)]
/--
theorem `biprodComparison_snd` / 定理 `biprodComparison_snd`

English:
theorem biprodComparison_snd
  statement: biprodComparison F X Y ≫ biprod.snd = F.map biprod.snd
  proof: biprod.lift_snd _ _

中文:
定理 biprodComparison_snd
  结论: biprodComparison F X Y ≫ biprod.snd = F.map biprod.snd
  证明: biprod.lift_snd _ _

Depends on / 依赖: biprod, biprod.lift_snd, lift_snd
-/
theorem biprodComparison_snd : biprodComparison F X Y ≫ biprod.snd = F.map biprod.snd :=
  biprod.lift_snd _ _

/--
Definition of `biprodComparison'` / `biprodComparison'` 的定义

English:
definition biprodComparison'
  signature: : F.obj X ⊞ F.obj Y ⟶ F.obj (X ⊞ Y)
  body: biprod.desc (F.map biprod.inl) (F.map biprod.inr)

@[reassoc (attr := simp)]

中文:
定义 biprodComparison'
  签名: : F.obj X ⊞ F.obj Y ⟶ F.obj (X ⊞ Y)
  定义体: biprod.desc (F.map biprod.inl) (F.map biprod.inr)

@[reassoc (attr := simp)]

Depends on / 依赖: F.map, biprod, biprod.desc, biprod.inl, biprod.inr
-/
def biprodComparison' : F.obj X ⊞ F.obj Y ⟶ F.obj (X ⊞ Y) :=
  biprod.desc (F.map biprod.inl) (F.map biprod.inr)

@[reassoc (attr := simp)]
/--
theorem `inl_biprodComparison'` / 定理 `inl_biprodComparison'`

English:
theorem inl_biprodComparison'
  statement: biprod.inl ≫ biprodComparison' F X Y = F.map biprod.inl
  proof: biprod.inl_desc _ _

@[reassoc (attr := simp)]

中文:
定理 inl_biprodComparison'
  结论: biprod.inl ≫ biprodComparison' F X Y = F.map biprod.inl
  证明: biprod.inl_desc _ _

@[reassoc (attr := simp)]

Depends on / 依赖: biprod, biprod.inl_desc, inl_desc
-/
theorem inl_biprodComparison' : biprod.inl ≫ biprodComparison' F X Y = F.map biprod.inl :=
  biprod.inl_desc _ _

@[reassoc (attr := simp)]
/--
theorem `inr_biprodComparison'` / 定理 `inr_biprodComparison'`

English:
theorem inr_biprodComparison'
  statement: biprod.inr ≫ biprodComparison' F X Y = F.map biprod.inr
  proof: biprod.inr_desc _ _

中文:
定理 inr_biprodComparison'
  结论: biprod.inr ≫ biprodComparison' F X Y = F.map biprod.inr
  证明: biprod.inr_desc _ _

Depends on / 依赖: biprod, biprod.inr_desc, inr_desc
-/
theorem inr_biprodComparison' : biprod.inr ≫ biprodComparison' F X Y = F.map biprod.inr :=
  biprod.inr_desc _ _

variable [PreservesZeroMorphisms F]

/-- The composition in the opposite direction is equal to the identity if and only if `F` preserves
the biproduct, see `preservesBinaryBiproduct_of_monoBiprodComparison`. -/
@[reassoc (attr := simp)]
/--
theorem `biprodComparison'_comp_biprodComparison` / 定理 `biprodComparison'_comp_biprodComparison`

English:
theorem biprodComparison'_comp_biprodComparison
  proof: by
  ext <;> simp [← Functor.map_comp]

中文:
定理 biprodComparison'_comp_biprodComparison
  证明: by
  ext <;> simp [← Functor.map_comp]
-/
theorem biprodComparison'_comp_biprodComparison :
    biprodComparison' F X Y ≫ biprodComparison F X Y = 𝟙 (F.obj X ⊞ F.obj Y) := by
  ext <;> simp [← Functor.map_comp]

/-- `biprodComparison F X Y` is a split epi. -/
@[simps]
/--
Definition of `splitEpiBiprodComparison` / `splitEpiBiprodComparison` 的定义

English:
definition splitEpiBiprodComparison
  signature: : SplitEpi (biprodComparison F X Y) where
  body: biprodComparison' F X Y
  id := by simp

中文:
定义 splitEpiBiprodComparison
  签名: : 分裂满态射 (biprodComparison F X Y) where
  定义体: biprodComparison' F X Y
  id := by simp
-/
def splitEpiBiprodComparison : SplitEpi (biprodComparison F X Y) where
  section_ := biprodComparison' F X Y
  id := by simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsSplitEpi (biprodComparison F X Y)
  body: IsSplitEpi.mk' (splitEpiBiprodComparison F X Y)

中文:
实例 :
  签名: 是分裂满态射 (biprodComparison F X Y)
  定义体: IsSplitEpi.mk' (splitEpiBiprodComparison F X Y)

Depends on / 依赖: IsSplitEpi, IsSplitEpi.mk, splitEpiBiprodComparison
-/
instance : IsSplitEpi (biprodComparison F X Y) :=
  IsSplitEpi.mk' (splitEpiBiprodComparison F X Y)

/-- `biprodComparison' F X Y` is a split mono. -/
@[simps]
/--
Definition of `splitMonoBiprodComparison'` / `splitMonoBiprodComparison'` 的定义

English:
definition splitMonoBiprodComparison'
  signature: : SplitMono (biprodComparison' F X Y) where
  body: biprodComparison F X Y
  id := by simp

中文:
定义 splitMonoBiprodComparison'
  签名: : 分裂单态射 (biprodComparison' F X Y) where
  定义体: biprodComparison F X Y
  id := by simp

Depends on / 依赖: biprodComparison
-/
def splitMonoBiprodComparison' : SplitMono (biprodComparison' F X Y) where
  retraction := biprodComparison F X Y
  id := by simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsSplitMono (biprodComparison' F X Y)
  body: IsSplitMono.mk' (splitMonoBiprodComparison' F X Y)

中文:
实例 :
  签名: 是分裂单态射 (biprodComparison' F X Y)
  定义体: IsSplitMono.mk' (splitMonoBiprodComparison' F X Y)

Depends on / 依赖: IsSplitMono, IsSplitMono.mk, splitMonoBiprodComparison
-/
instance : IsSplitMono (biprodComparison' F X Y) :=
  IsSplitMono.mk' (splitMonoBiprodComparison' F X Y)

end

variable [PreservesZeroMorphisms F] [PreservesBinaryBiproduct X Y F]

/--
Instance `hasBinaryBiproduct_of_preserves` / 实例 `hasBinaryBiproduct_of_preserves`

English:
instance hasBinaryBiproduct_of_preserves
  signature: : HasBinaryBiproduct (F.obj X) (F.obj Y)
  body: HasBinaryBiproduct.mk
    { bicone := F.mapBinaryBicone (BinaryBiproduct.bicone X Y)
      isBilimit := isBinaryBilimitOfPreserves F (BinaryBiproduct.isBilimit _ _) }

中文:
实例 hasBinaryBiproduct_of_preserves
  签名: : 有BinaryBiproduct (F.obj X) (F.obj Y)
  定义体: HasBinaryBiproduct.mk
    { bicone := F.mapBinaryBicone (BinaryBiproduct.bicone X Y)
      isBilimit := isBinaryBilimitOfPreserves F (BinaryBiproduct.isBilimit _ _) }

Depends on / 依赖: BinaryBiproduct, BinaryBiproduct.bicone, BinaryBiproduct.isBilimit, Category, Category.assoc, Comon.tensorObj_comul, F.mapBinaryBicone, HasBinaryBiproduct, HasBinaryBiproduct.mk, SymmetricCategory, SymmetricCategory.tensor, bicone, isBilimit, isBinaryBilimitOfPreserves, mapBinaryBicone, tensorObj_comul
-/
instance hasBinaryBiproduct_of_preserves : HasBinaryBiproduct (F.obj X) (F.obj Y) :=
  HasBinaryBiproduct.mk
    { bicone := F.mapBinaryBicone (BinaryBiproduct.bicone X Y)
      isBilimit := isBinaryBilimitOfPreserves F (BinaryBiproduct.isBilimit _ _) }

/--
Definition of `mapBiprod` / `mapBiprod` 的定义

English:
abbreviation mapBiprod
  signature: : F.obj (X ⊞ Y) ≅ F.obj X ⊞ F.obj Y
  body: biprod.uniqueUpToIso _ _ (isBinaryBilimitOfPreserves F (BinaryBiproduct.isBilimit _ _))

中文:
缩写 mapBiprod
  签名: : F.obj (X ⊞ Y) ≅ F.obj X ⊞ F.obj Y
  定义体: biprod.uniqueUpToIso _ _ (isBinaryBilimitOfPreserves F (BinaryBiproduct.isBilimit _ _))

Depends on / 依赖: BinaryBiproduct, BinaryBiproduct.isBilimit, biprod, biprod.uniqueUpToIso, isBilimit, isBinaryBilimitOfPreserves, uniqueUpToIso
-/
abbrev mapBiprod : F.obj (X ⊞ Y) ≅ F.obj X ⊞ F.obj Y :=
  biprod.uniqueUpToIso _ _ (isBinaryBilimitOfPreserves F (BinaryBiproduct.isBilimit _ _))

/--
theorem `mapBiprod_hom` / 定理 `mapBiprod_hom`

English:
theorem mapBiprod_hom
  statement: (mapBiprod F X Y).hom = biprod.lift (F.map biprod.fst) (F.map biprod.snd)
  proof: rfl

中文:
定理 mapBiprod_hom
  结论: (mapBiprod F X Y).hom = biprod.lift (F.map biprod.fst) (F.map biprod.snd)
  证明: rfl
-/
theorem mapBiprod_hom : (mapBiprod F X Y).hom = biprod.lift (F.map biprod.fst) (F.map biprod.snd) :=
  rfl

/--
theorem `mapBiprod_inv` / 定理 `mapBiprod_inv`

English:
theorem mapBiprod_inv
  statement: (mapBiprod F X Y).inv = biprod.desc (F.map biprod.inl) (F.map biprod.inr)
  proof: rfl

中文:
定理 mapBiprod_inv
  结论: (mapBiprod F X Y).inv = biprod.desc (F.map biprod.inl) (F.map biprod.inr)
  证明: rfl
-/
theorem mapBiprod_inv : (mapBiprod F X Y).inv = biprod.desc (F.map biprod.inl) (F.map biprod.inr) :=
  rfl

end Functor

namespace Limits

variable (F : C ⥤ D) [PreservesZeroMorphisms F]

section Bicone

variable {J : Type w₁} (f : J -> C) [HasBiproduct f] [PreservesBiproduct f F] {W : C}

/--
theorem `biproduct.map_lift_mapBiprod` / 定理 `biproduct.map_lift_mapBiprod`

English:
theorem biproduct.map_lift_mapBiprod
  given: (g : forall j, W ⟶ f j)
  proof: by
  ext j
  dsimp only [Function.comp_def]
  simp only [mapBiproduct_hom, Category.assoc, biproduct.lift_π, ← F.map_comp]

中文:
定理 biproduct.map_lift_mapBiprod
  条件: (g : 对任意 j, W ⟶ f j)
  证明: by
  ext j
  dsimp only [Function.comp_def]
  simp only [mapBiproduct_hom, Category.assoc, biproduct.lift_π, ← F.map_comp]

Depends on / 依赖: Category, Category.assoc, F.map_comp, Function, Function.comp_def, biproduct, biproduct.lift_, comp_def, mapBiproduct_hom, map_comp
-/
theorem biproduct.map_lift_mapBiprod (g : forall j, W ⟶ f j) :
    F.map (biproduct.lift g) ≫ (F.mapBiproduct f).hom = biproduct.lift fun j => F.map (g j) := by
  ext j
  dsimp only [Function.comp_def]
  simp only [mapBiproduct_hom, Category.assoc, biproduct.lift_π, ← F.map_comp]

/--
theorem `biproduct.mapBiproduct_inv_map_desc` / 定理 `biproduct.mapBiproduct_inv_map_desc`

English:
theorem biproduct.mapBiproduct_inv_map_desc
  given: (g : forall j, f j ⟶ W)
  proof: by
  ext j
  dsimp only [Function.comp_def]
  simp only [mapBiproduct_inv, ← Category.assoc, biproduct.ι_desc, ← F.map_comp]

中文:
定理 biproduct.mapBiproduct_inv_map_desc
  条件: (g : 对任意 j, f j ⟶ W)
  证明: by
  ext j
  dsimp only [Function.comp_def]
  simp only [mapBiproduct_inv, ← Category.assoc, biproduct.ι_desc, ← F.map_comp]

Depends on / 依赖: Category, Category.assoc, F.map_comp, Function, Function.comp_def, biproduct, comp_def, mapBiproduct_inv, map_comp
-/
theorem biproduct.mapBiproduct_inv_map_desc (g : forall j, f j ⟶ W) :
    (F.mapBiproduct f).inv ≫ F.map (biproduct.desc g) = biproduct.desc fun j => F.map (g j) := by
  ext j
  dsimp only [Function.comp_def]
  simp only [mapBiproduct_inv, ← Category.assoc, biproduct.ι_desc, ← F.map_comp]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `biproduct.mapBiproduct_hom_desc` / 定理 `biproduct.mapBiproduct_hom_desc`

English:
theorem biproduct.mapBiproduct_hom_desc
  given: (g : forall j, f j ⟶ W)
  proof: by
  rw [← biproduct.mapBiproduct_inv_map_desc]; rw [Iso.hom_inv_id_assoc]

中文:
定理 biproduct.mapBiproduct_hom_desc
  条件: (g : 对任意 j, f j ⟶ W)
  证明: by
  rw [← biproduct.mapBiproduct_inv_map_desc]; rw [Iso.hom_inv_id_assoc]

Depends on / 依赖: Iso.hom_inv_id_assoc, biproduct, biproduct.mapBiproduct_inv_map_desc, hom_inv_id_assoc, mapBiproduct_inv_map_desc
-/
theorem biproduct.mapBiproduct_hom_desc (g : forall j, f j ⟶ W) :
    ((F.mapBiproduct f).hom ≫ biproduct.desc fun j => F.map (g j)) = F.map (biproduct.desc g) := by
  rw [← biproduct.mapBiproduct_inv_map_desc]; rw [Iso.hom_inv_id_assoc]

end Bicone

section BinaryBicone

variable (X Y : C) [HasBinaryBiproduct X Y] [PreservesBinaryBiproduct X Y F] {W : C}

set_option backward.defeqAttrib.useBackward true in
/--
theorem `biprod.map_lift_mapBiprod` / 定理 `biprod.map_lift_mapBiprod`

English:
theorem biprod.map_lift_mapBiprod
  given: (f : W ⟶ X) (g : W ⟶ Y)
  proof: by
  ext <;> simp [mapBiprod, ← F.map_comp]

中文:
定理 biprod.map_lift_mapBiprod
  条件: (f : W ⟶ X) (g : W ⟶ Y)
  证明: by
  ext <;> simp [mapBiprod, ← F.map_comp]

Depends on / 依赖: F.map_comp, mapBiprod, map_comp
-/
theorem biprod.map_lift_mapBiprod (f : W ⟶ X) (g : W ⟶ Y) :
    F.map (biprod.lift f g) ≫ (F.mapBiprod X Y).hom = biprod.lift (F.map f) (F.map g) := by
  ext <;> simp [mapBiprod, ← F.map_comp]

/--
theorem `biprod.lift_mapBiprod` / 定理 `biprod.lift_mapBiprod`

English:
theorem biprod.lift_mapBiprod
  given: (f : W ⟶ X) (g : W ⟶ Y)
  proof: by
  rw [← biprod.map_lift_mapBiprod]; rw [Category.assoc]; rw [Iso.hom_inv_id]; rw [Category.comp_id]

中文:
定理 biprod.lift_mapBiprod
  条件: (f : W ⟶ X) (g : W ⟶ Y)
  证明: by
  rw [← biprod.map_lift_mapBiprod]; rw [Category.assoc]; rw [Iso.hom_inv_id]; rw [Category.comp_id]

Depends on / 依赖: Category, Category.assoc, Category.comp_id, Iso.hom_inv_id, biprod, biprod.map_lift_mapBiprod, comp_id, hom_inv_id, map_lift_mapBiprod
-/
theorem biprod.lift_mapBiprod (f : W ⟶ X) (g : W ⟶ Y) :
    biprod.lift (F.map f) (F.map g) ≫ (F.mapBiprod X Y).inv = F.map (biprod.lift f g) := by
  rw [← biprod.map_lift_mapBiprod]; rw [Category.assoc]; rw [Iso.hom_inv_id]; rw [Category.comp_id]

set_option backward.defeqAttrib.useBackward true in
/--
theorem `biprod.mapBiprod_inv_map_desc` / 定理 `biprod.mapBiprod_inv_map_desc`

English:
theorem biprod.mapBiprod_inv_map_desc
  given: (f : X ⟶ W) (g : Y ⟶ W)
  proof: by
  ext <;> simp [mapBiprod, ← F.map_comp]

中文:
定理 biprod.mapBiprod_inv_map_desc
  条件: (f : X ⟶ W) (g : Y ⟶ W)
  证明: by
  ext <;> simp [mapBiprod, ← F.map_comp]

Depends on / 依赖: F.map_comp, mapBiprod, map_comp
-/
theorem biprod.mapBiprod_inv_map_desc (f : X ⟶ W) (g : Y ⟶ W) :
    (F.mapBiprod X Y).inv ≫ F.map (biprod.desc f g) = biprod.desc (F.map f) (F.map g) := by
  ext <;> simp [mapBiprod, ← F.map_comp]

/--
theorem `biprod.mapBiprod_hom_desc` / 定理 `biprod.mapBiprod_hom_desc`

English:
theorem biprod.mapBiprod_hom_desc
  given: (f : X ⟶ W) (g : Y ⟶ W)
  proof: by
  rw [← biprod.mapBiprod_inv_map_desc]; rw [Iso.hom_inv_id_assoc]

中文:
定理 biprod.mapBiprod_hom_desc
  条件: (f : X ⟶ W) (g : Y ⟶ W)
  证明: by
  rw [← biprod.mapBiprod_inv_map_desc]; rw [Iso.hom_inv_id_assoc]

Depends on / 依赖: Iso.hom_inv_id_assoc, biprod, biprod.mapBiprod_inv_map_desc, hom_inv_id_assoc, mapBiprod_inv_map_desc
-/
theorem biprod.mapBiprod_hom_desc (f : X ⟶ W) (g : Y ⟶ W) :
    (F.mapBiprod X Y).hom ≫ biprod.desc (F.map f) (F.map g) = F.map (biprod.desc f g) := by
  rw [← biprod.mapBiprod_inv_map_desc]; rw [Iso.hom_inv_id_assoc]

end BinaryBicone

end Limits

end HasZeroMorphisms

end CategoryTheory
