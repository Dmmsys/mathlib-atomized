/-
Copyright (c) 2025 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module

public import Mathlib.CategoryTheory.Bicategory.LocallyDiscrete
public import Mathlib.CategoryTheory.Bicategory.FunctorBicategory.Oplax
public import Mathlib.CategoryTheory.Bicategory.End
public import Mathlib.CategoryTheory.Monoidal.Comon_

/-!
# Comonads in a bicategory

We define comonads in a bicategory `B` as comonoid objects in an endomorphism monoidal category.
We show that this is equivalent to oplax functors from the trivial bicategory to `B`. From this,
we show that comonads in `B` form a bicategory.

## TODO

We can also define monads in a bicategory. This is not yet done as we don't have the bicategory
structure on the set of lax functors at this point, which is needed to show that monads form a
bicategory.
-/

@[expose] public section

namespace CategoryTheory

namespace Bicategory

universe w v u

variable {B : Type u} [Bicategory.{w, v} B]

/--
Definition of `Comonad` / `Comonad` 的定义

English:
abbreviation Comonad
  signature: {a : B} (t : a ⟶ a)
  body: ComonObj t

中文:
缩写 余单子
  签名: {a : B} (t : a ⟶ a)
  定义体: ComonObj t

Depends on / 依赖: ComonObj
-/
abbrev Comonad {a : B} (t : a ⟶ a) := ComonObj t

/--
Definition of `Comonad.counit` / `Comonad.counit` 的定义

English:
abbreviation Comonad.counit
  signature: {a : B} {t : a ⟶ a} [Comonad t]
  body: ComonObj.counit

中文:
缩写 余单子.counit
  签名: {a : B} {t : a ⟶ a} [余单子 t]
  定义体: ComonObj.counit

Depends on / 依赖: ComonObj, ComonObj.counit, counit
-/
abbrev Comonad.counit {a : B} {t : a ⟶ a} [Comonad t] : t ⟶ 𝟙 a := ComonObj.counit

/--
Definition of `Comonad.comul` / `Comonad.comul` 的定义

English:
abbreviation Comonad.comul
  signature: {a : B} {t : a ⟶ a} [Comonad t]
  body: ComonObj.comul

@[inherit_doc] scoped notation "ε" => Comonad.counit
@[inherit_doc] scoped notation "ε[" x "]" => Comonad.counit (t := x)
@[inherit_doc] scoped notation "Δ" => Comonad.comul
@[inherit_doc] scoped notation "Δ[" x "]" => Comonad.comul (t := x)

中文:
缩写 余单子.comul
  签名: {a : B} {t : a ⟶ a} [余单子 t]
  定义体: ComonObj.comul

@[inherit_doc] scoped notation "ε" => Comonad.counit
@[inherit_doc] scoped notation "ε[" x "]" => Comonad.counit (t := x)
@[inherit_doc] scoped notation "Δ" => Comonad.comul
@[inherit_doc] scoped notation "Δ[" x "]" => Comonad.comul (t := x)

Depends on / 依赖: ComonObj, ComonObj.comul
-/
abbrev Comonad.comul {a : B} {t : a ⟶ a} [Comonad t] : t ⟶ t ≫ t := ComonObj.comul

@[inherit_doc] scoped notation "ε" => Comonad.counit
@[inherit_doc] scoped notation "ε[" x "]" => Comonad.counit (t := x)
@[inherit_doc] scoped notation "Δ" => Comonad.comul
@[inherit_doc] scoped notation "Δ[" x "]" => Comonad.comul (t := x)

namespace Comonad

variable {a : B}

/- Comonad laws -/
section

variable (t : a ⟶ a) [Comonad t]

@[reassoc (attr := simp)]
/--
theorem `counit_comul` / 定理 `counit_comul`

English:
theorem counit_comul
  statement: Δ ≫ ε ▷ t = (fun_ t).inv
  proof: ComonObj.counit_comul t

@[reassoc (attr := simp)]

中文:
定理 counit_comul
  结论: Δ ≫ ε ▷ t = (fun_ t).inv
  证明: ComonObj.counit_comul t

@[reassoc (attr := simp)]

Depends on / 依赖: ComonObj, ComonObj.counit_comul, counit_comul
-/
theorem counit_comul : Δ ≫ ε ▷ t = (fun_ t).inv := ComonObj.counit_comul t

@[reassoc (attr := simp)]
/--
theorem `comul_counit` / 定理 `comul_counit`

English:
theorem comul_counit
  statement: Δ ≫ t ◁ ε = (ρ_ t).inv
  proof: ComonObj.comul_counit t

@[reassoc (attr := simp)]

中文:
定理 comul_counit
  结论: Δ ≫ t ◁ ε = (ρ_ t).inv
  证明: ComonObj.comul_counit t

@[reassoc (attr := simp)]

Depends on / 依赖: ComonObj, ComonObj.comul_counit, comul_counit
-/
theorem comul_counit : Δ ≫ t ◁ ε = (ρ_ t).inv := ComonObj.comul_counit t

@[reassoc (attr := simp)]
/--
theorem `comul_assoc` / 定理 `comul_assoc`

English:
theorem comul_assoc
  statement: Δ ≫ t ◁ Δ = Δ ≫ Δ ▷ t ≫ (α_ t t t).hom
  proof: ComonObj.comul_assoc t

@[reassoc]

中文:
定理 comul_assoc
  结论: Δ ≫ t ◁ Δ = Δ ≫ Δ ▷ t ≫ (α_ t t t).hom
  证明: ComonObj.comul_assoc t

@[reassoc]

Depends on / 依赖: ComonObj, ComonObj.comul_assoc, comul_assoc
-/
theorem comul_assoc : Δ ≫ t ◁ Δ = Δ ≫ Δ ▷ t ≫ (α_ t t t).hom := ComonObj.comul_assoc t

@[reassoc]
/--
theorem `comul_assoc_flip` / 定理 `comul_assoc_flip`

English:
theorem comul_assoc_flip
  statement: Δ ≫ Δ ▷ t = Δ ≫ t ◁ Δ ≫ (α_ t t t).inv
  proof: ComonObj.comul_assoc_flip t

中文:
定理 comul_assoc_flip
  结论: Δ ≫ Δ ▷ t = Δ ≫ t ◁ Δ ≫ (α_ t t t).inv
  证明: ComonObj.comul_assoc_flip t

Depends on / 依赖: ComonObj, ComonObj.comul_assoc_flip, comul_assoc_flip
-/
theorem comul_assoc_flip : Δ ≫ Δ ▷ t = Δ ≫ t ◁ Δ ≫ (α_ t t t).inv := ComonObj.comul_assoc_flip t

end

@[simps! counit]
instance {a : B} : Comonad (𝟙 a) :=
  ComonObj.instTensorUnit (a ⟶ a)

/-- An oplax functor from the trivial bicategory to `B` defines a comonad in `B`. -/
@[instance_reducible]
/--
Definition of `ofOplaxFromUnit` / `ofOplaxFromUnit` 的定义

English:
definition ofOplaxFromUnit
  signature: (F : LocallyDiscrete (Discrete Unit) ⥤ᵒᵖᴸ B)
  body: F.map₂ (ρ_ _).inv ≫ F.mapComp _ _
  counit := F.mapId _
  comul_assoc := by
    simp only [tensorObj_def, MonoidalCategory.whiskerLeft_comp, whiskerLeft_def, Category.assoc,
      MonoidalCategory.comp_whiskerRight, whiskerRight_def, associator_def]
    rw [← F.mapComp_naturality_left_assoc]; rw [← 

中文:
定义 ofOplaxFromUnit
  签名: (F : LocallyDiscrete (离散 单元) ⥤ᵒᵖᴸ B)
  定义体: F.map₂ (ρ_ _).inv ≫ F.mapComp _ _
  counit := F.mapId _
  comul_assoc := by
    simp only [tensorObj_def, MonoidalCategory.whiskerLeft_comp, whiskerLeft_def, Category.assoc,
      MonoidalCategory.comp_whiskerRight, whiskerRight_def, associator_def]
    rw [← F.mapComp_naturality_left_assoc]; rw [← 

Depends on / 依赖: F.map, F.mapComp, mapComp
-/
def ofOplaxFromUnit (F : LocallyDiscrete (Discrete Unit) ⥤ᵒᵖᴸ B) :
    Comonad (F.map (𝟙 ⟨⟨Unit.unit⟩⟩)) where
  comul := F.map₂ (ρ_ _).inv ≫ F.mapComp _ _
  counit := F.mapId _
  comul_assoc := by
    simp only [tensorObj_def, MonoidalCategory.whiskerLeft_comp, whiskerLeft_def, Category.assoc,
      MonoidalCategory.comp_whiskerRight, whiskerRight_def, associator_def]
    rw [← F.mapComp_naturality_left_assoc]; rw [← F.mapComp_naturality_right_assoc]
    simp only [whiskerLeft_rightUnitor_inv, PrelaxFunctor.map₂_comp, Category.assoc,
      OplaxFunctor.map₂_associator, whiskerRight_id, Iso.hom_inv_id_assoc]
  counit_comul := by
    simp only [tensorUnit_def, tensorObj_def, whiskerRight_def, Category.assoc, leftUnitor_def]
    rw [F.mapComp_id_left]; rw [unitors_equal]; rw [F.map₂_inv_hom_assoc]
  comul_counit := by
    simp only [tensorUnit_def, tensorObj_def, whiskerLeft_def, rightUnitor_def]
    rw [Category.assoc]; rw [F.mapComp_id_right]; rw [F.map₂_inv_hom_assoc]

/--
Definition of `toOplax` / `toOplax` 的定义

English:
definition toOplax
  signature: {a : B} (t : a ⟶ a) [Comonad t]
  body: a
  map _ := t
  map₂ _ := 𝟙 _
  mapId _ := ε
  mapComp _ _ := Δ
  map₂_associator _ _ _ := by
    rw [Category.id_comp]
    apply Comonad.comul_assoc

中文:
定义 toOplax
  签名: {a : B} (t : a ⟶ a) [余单子 t]
  定义体: a
  map _ := t
  map₂ _ := 𝟙 _
  mapId _ := ε
  mapComp _ _ := Δ
  map₂_associator _ _ _ := by
    rw [Category.id_comp]
    apply Comonad.comul_assoc
-/
def toOplax {a : B} (t : a ⟶ a) [Comonad t] : LocallyDiscrete (Discrete Unit) ⥤ᵒᵖᴸ B where
  obj _ := a
  map _ := t
  map₂ _ := 𝟙 _
  mapId _ := ε
  mapComp _ _ := Δ
  map₂_associator _ _ _ := by
    rw [Category.id_comp]
    apply Comonad.comul_assoc

end Comonad

/- In this section, we define bicategory structure on comonads by using the bicategory structure on
oplax functors. We may use oplax, lax, or pseudonatural transformations to provide the bicategory
structure, and the namespace below indicates that we use oplax transformations here. The
constructions for the other two cases would be given in the corresponding namespaces. -/
namespace OplaxTrans

/--
Definition of `ComonadBicat` / `ComonadBicat` 的定义

English:
definition ComonadBicat
  signature: (B : Type u) [Bicategory.{w, v} B]
  body: LocallyDiscrete (Discrete Unit) ⥤ᵒᵖᴸ B

中文:
定义 ComonadBicat
  签名: (B : 类型u) [双范畴.{w, v} B]
  定义体: LocallyDiscrete (Discrete Unit) ⥤ᵒᵖᴸ B

Depends on / 依赖: Discrete, LocallyDiscrete
-/
def ComonadBicat (B : Type u) [Bicategory.{w, v} B] :=
  LocallyDiscrete (Discrete Unit) ⥤ᵒᵖᴸ B

namespace ComonadBicat

open scoped Oplax.OplaxTrans.OplaxFunctor in
/-- The bicategory of comonads in `B`. -/
scoped instance : Bicategory (ComonadBicat B) :=
inferInstanceAs Bicategory (LocallyDiscrete (Discrete PUnit) ⥤ᵒᵖᴸ B)

/--
Definition of `toOplax` / `toOplax` 的定义

English:
definition toOplax
  signature: (m : ComonadBicat B)
  body: m

中文:
定义 toOplax
  签名: (m : ComonadBicat B)
  定义体: m
-/
def toOplax (m : ComonadBicat B) : LocallyDiscrete (Discrete PUnit) ⥤ᵒᵖᴸ B :=
  m

/--
Definition of `obj` / `obj` 的定义

English:
definition obj
  signature: (m : ComonadBicat B)
  body: m.toOplax.obj ⟨⟨PUnit.unit⟩⟩

中文:
定义 obj
  签名: (m : ComonadBicat B)
  定义体: m.toOplax.obj ⟨⟨PUnit.unit⟩⟩

Depends on / 依赖: PUnit.unit, m.toOplax.obj, toOplax
-/
def obj (m : ComonadBicat B) :=
  m.toOplax.obj ⟨⟨PUnit.unit⟩⟩

/--
Definition of `hom` / `hom` 的定义

English:
definition hom
  signature: (m : ComonadBicat B)
  body: m.toOplax.map (𝟙 (⟨⟨PUnit.unit⟩⟩ : LocallyDiscrete (Discrete PUnit)))

中文:
定义 hom
  签名: (m : ComonadBicat B)
  定义体: m.toOplax.map (𝟙 (⟨⟨PUnit.unit⟩⟩ : LocallyDiscrete (Discrete PUnit)))

Depends on / 依赖: Discrete, LocallyDiscrete, PUnit.unit, m.toOplax.map, toOplax
-/
def hom (m : ComonadBicat B) : m.obj ⟶ m.obj :=
  m.toOplax.map (𝟙 (⟨⟨PUnit.unit⟩⟩ : LocallyDiscrete (Discrete PUnit)))

instance (m : ComonadBicat B) : Comonad m.hom :=
Comonad.ofOplaxFromUnit m.toOplax

/--
Definition of `mkOfComonad` / `mkOfComonad` 的定义

English:
definition mkOfComonad
  signature: {a : B} (t : a ⟶ a) [Comonad t]
  body: Comonad.toOplax t

中文:
定义 mkOfComonad
  签名: {a : B} (t : a ⟶ a) [余单子 t]
  定义体: Comonad.toOplax t

Depends on / 依赖: Comonad, Comonad.toOplax, toOplax
-/
def mkOfComonad {a : B} (t : a ⟶ a) [Comonad t] : ComonadBicat B :=
  Comonad.toOplax t

open Comonad

section

variable {a : B} (t : a ⟶ a) [Comonad t]

/--
theorem `mkOfComonad_hom` / 定理 `mkOfComonad_hom`

English:
theorem mkOfComonad_hom
  statement: (mkOfComonad t).hom = t
  proof: rfl

中文:
定理 mkOfComonad_hom
  结论: (mkOfComonad t).hom = t
  证明: rfl

Depends on / 依赖: IsConnected, IsConnected.is_nonempty, is_nonempty
-/
theorem mkOfComonad_hom : (mkOfComonad t).hom = t := rfl

/--
theorem `mkOfComonad_counit` / 定理 `mkOfComonad_counit`

English:
theorem mkOfComonad_counit
  statement: ε[(mkOfComonad t).hom] = ε[t]
  proof: rfl

中文:
定理 mkOfComonad_counit
  结论: ε[(mkOfComonad t).hom] = ε[t]
  证明: rfl
-/
theorem mkOfComonad_counit : ε[(mkOfComonad t).hom] = ε[t] := rfl

/--
theorem `mkOfComonad_comul` / 定理 `mkOfComonad_comul`

English:
theorem mkOfComonad_comul
  statement: Δ[(mkOfComonad t).hom] = Δ[t]
  proof: by
  change 𝟙 t ≫ Δ = Δ
  apply Category.id_comp

中文:
定理 mkOfComonad_comul
  结论: Δ[(mkOfComonad t).hom] = Δ[t]
  证明: by
  change 𝟙 t ≫ Δ = Δ
  apply Category.id_comp

Depends on / 依赖: Category, Category.id_comp, id_comp
-/
theorem mkOfComonad_comul : Δ[(mkOfComonad t).hom] = Δ[t] := by
  change 𝟙 t ≫ Δ = Δ
  apply Category.id_comp

end

end ComonadBicat

end OplaxTrans

end Bicategory

end CategoryTheory
