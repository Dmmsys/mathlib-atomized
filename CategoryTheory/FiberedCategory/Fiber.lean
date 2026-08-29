/-
Copyright (c) 2024 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne, Paul Lezeau
-/
module

public import Mathlib.CategoryTheory.FiberedCategory.HomLift
public import Mathlib.CategoryTheory.Functor.Const

/-!

# Fibers of functors

In this file we define, for a functor `p : 𝒳 ⥤ 𝒴`, the fiber categories `Fiber p S` for every
`S : 𝒮` as follows
- An object in `Fiber p S` is a pair `(a, ha)` where `a : 𝒳` and `ha : p.obj a = S`.
- A morphism in `Fiber p S` is a morphism `φ : a ⟶ b` in 𝒳 such that `p.map φ = 𝟙 S`.

For any category `C` equipped with a functor `F : C ⥤ 𝒳` such that `F ⋙ p` is constant at `S`,
we define a functor `inducedFunctor : C ⥤ Fiber p S` that `F` factors through.
-/

@[expose] public section

universe v₁ u₁ v₂ u₂ v₃ u₃

namespace CategoryTheory

open IsHomLift

namespace Functor

variable {𝒮 : Type u₁} {𝒳 : Type u₂} [Category.{v₁} 𝒮] [Category.{v₂} 𝒳]

/--
Definition of `Fiber` / `Fiber` 的定义

English:
definition Fiber
  signature: (p : 𝒳 ⥤ 𝒮) (S : 𝒮)
  body: { a : 𝒳 // p.obj a = S }

中文:
定义 Fiber
  签名: (p : 𝒳 ⥤ 𝒮) (S : 𝒮)
  定义体: { a : 𝒳 // p.obj a = S }

Depends on / 依赖: p.obj
-/
def Fiber (p : 𝒳 ⥤ 𝒮) (S : 𝒮) := { a : 𝒳 // p.obj a = S }

namespace Fiber

variable {p : 𝒳 ⥤ 𝒮} {S : 𝒮}

/--
Instance `fiberCategory` / 实例 `fiberCategory`

English:
instance fiberCategory
  signature: : Category (Fiber p S) where
  body: {φ : a.1 ⟶ b.1 // IsHomLift p (𝟙 S) φ}
  id a := ⟨𝟙 a.1, IsHomLift.id a.2⟩
  comp φ ψ := ⟨φ.val ≫ ψ.val, by have := φ.2; have := ψ.2; infer_instance⟩

中文:
实例 fiberCategory
  签名: : 范畴 (Fiber p S) where
  定义体: {φ : a.1 ⟶ b.1 // IsHomLift p (𝟙 S) φ}
  id a := ⟨𝟙 a.1, IsHomLift.id a.2⟩
  comp φ ψ := ⟨φ.val ≫ ψ.val, by have := φ.2; have := ψ.2; infer_instance⟩

Depends on / 依赖: IsHomLift
-/
instance fiberCategory : Category (Fiber p S) where
  Hom a b := {φ : a.1 ⟶ b.1 // IsHomLift p (𝟙 S) φ}
  id a := ⟨𝟙 a.1, IsHomLift.id a.2⟩
  comp φ ψ := ⟨φ.val ≫ ψ.val, by have := φ.2; have := ψ.2; infer_instance⟩

/--
Definition of `fiberInclusion` / `fiberInclusion` 的定义

English:
definition fiberInclusion
  signature: : Fiber p S ⥤ 𝒳 where
  body: a.1
  map φ := φ.1

中文:
定义 fiberInclusion
  签名: : Fiber p S ⥤ 𝒳 where
  定义体: a.1
  map φ := φ.1
-/
def fiberInclusion : Fiber p S ⥤ 𝒳 where
  obj a := a.1
  map φ := φ.1

instance {a b : Fiber p S} (φ : a ⟶ b) : IsHomLift p (𝟙 S) (fiberInclusion.map φ) := φ.2

@[ext]
/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  statement: {a b : Fiber p S} {φ ψ : a ⟶ b}
  proof: Subtype.ext h

中文:
引理 hom_ext
  结论: {a b : Fiber p S} {φ ψ : a ⟶ b}
  证明: Subtype.ext h

Depends on / 依赖: Subtype, Subtype.ext
-/
lemma hom_ext {a b : Fiber p S} {φ ψ : a ⟶ b}
    (h : fiberInclusion.map φ = fiberInclusion.map ψ) : φ = ψ :=
  Subtype.ext h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (fiberInclusion : Fiber p S ⥤ _).Faithful

中文:
实例 :
  签名: (fiberInclusion : Fiber p S ⥤ _).忠实
-/
instance : (fiberInclusion : Fiber p S ⥤ _).Faithful where

/--
lemma `fiberInclusion_obj_inj` / 引理 `fiberInclusion_obj_inj`

English:
lemma fiberInclusion_obj_inj
  statement: (fiberInclusion : Fiber p S ⥤ _).obj.Injective
  proof: fun _ _ f => Subtype.val_inj.1 f

中文:
引理 fiberInclusion_obj_inj
  结论: (fiberInclusion : Fiber p S ⥤ _).obj.单射
  证明: fun _ _ f => Subtype.val_inj.1 f

Depends on / 依赖: Subtype, Subtype.val_inj, val_inj
-/
lemma fiberInclusion_obj_inj : (fiberInclusion : Fiber p S ⥤ _).obj.Injective :=
  fun _ _ f => Subtype.val_inj.1 f

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- For fixed `S : 𝒮` this is the natural isomorphism between `fiberInclusion ⋙ p` and the constant
function valued at `S`. -/
@[simps!]
/--
Definition of `fiberInclusionCompIsoConst` / `fiberInclusionCompIsoConst` 的定义

English:
definition fiberInclusionCompIsoConst
  signature: : fiberInclusion ⋙ p ≅ (const (Fiber p S)).obj S
  body: NatIso.ofComponents (fun X => eqToIso X.2)
    (fun φ => by simp [IsHomLift.fac' p (𝟙 S) (fiberInclusion.map φ)])

中文:
定义 fiberInclusionCompIsoConst
  签名: : fiberInclusion ⋙ p ≅ (const (Fiber p S)).obj S
  定义体: NatIso.ofComponents (fun X => eqToIso X.2)
    (fun φ => by simp [IsHomLift.fac' p (𝟙 S) (fiberInclusion.map φ)])

Depends on / 依赖: IsHomLift, IsHomLift.fac, NatIso, NatIso.ofComponents, eqToIso, fiberInclusion, fiberInclusion.map, ofComponents
-/
def fiberInclusionCompIsoConst : fiberInclusion ⋙ p ≅ (const (Fiber p S)).obj S :=
  NatIso.ofComponents (fun X => eqToIso X.2)
    (fun φ => by simp [IsHomLift.fac' p (𝟙 S) (fiberInclusion.map φ)])

/--
lemma `fiberInclusion_comp_eq_const` / 引理 `fiberInclusion_comp_eq_const`

English:
lemma fiberInclusion_comp_eq_const
  statement: fiberInclusion ⋙ p = (const (Fiber p S)).obj S
  proof: Functor.ext_of_iso fiberInclusionCompIsoConst (fun x => x.2)

中文:
引理 fiberInclusion_comp_eq_const
  结论: fiberInclusion ⋙ p = (const (Fiber p S)).obj S
  证明: Functor.ext_of_iso fiberInclusionCompIsoConst (fun x => x.2)

Depends on / 依赖: Functor, Functor.ext_of_iso, ext_of_iso, fiberInclusionCompIsoConst
-/
lemma fiberInclusion_comp_eq_const : fiberInclusion ⋙ p = (const (Fiber p S)).obj S :=
  Functor.ext_of_iso fiberInclusionCompIsoConst (fun x => x.2)

/--
Definition of `mk` / `mk` 的定义

English:
definition mk
  signature: {p : 𝒳 ⥤ 𝒮} {S : 𝒮} {a : 𝒳} (ha : p.obj a = S)
  body: ⟨a, ha⟩

@[simp]

中文:
定义 mk
  签名: {p : 𝒳 ⥤ 𝒮} {S : 𝒮} {a : 𝒳} (ha : p.obj a = S)
  定义体: ⟨a, ha⟩

@[simp]
-/
def mk {p : 𝒳 ⥤ 𝒮} {S : 𝒮} {a : 𝒳} (ha : p.obj a = S) : Fiber p S := ⟨a, ha⟩

@[simp]
/--
lemma `fiberInclusion_mk` / 引理 `fiberInclusion_mk`

English:
lemma fiberInclusion_mk
  given: {p : 𝒳 ⥤ 𝒮} {S : 𝒮} {a : 𝒳} (ha : p.obj a = S)
  proof: rfl

中文:
引理 fiberInclusion_mk
  条件: {p : 𝒳 ⥤ 𝒮} {S : 𝒮} {a : 𝒳} (ha : p.obj a = S)
  证明: rfl
-/
lemma fiberInclusion_mk {p : 𝒳 ⥤ 𝒮} {S : 𝒮} {a : 𝒳} (ha : p.obj a = S) :
    fiberInclusion.obj (mk ha) = a :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `homMk` / `homMk` 的定义

English:
definition homMk
  signature: (p : 𝒳 ⥤ 𝒮) (S : 𝒮) {a b : 𝒳} (φ : a ⟶ b) [IsHomLift p (𝟙 S) φ]
  body: ⟨φ, inferInstance⟩

@[simp]

中文:
定义 homMk
  签名: (p : 𝒳 ⥤ 𝒮) (S : 𝒮) {a b : 𝒳} (φ : a ⟶ b) [IsHomLift p (𝟙 S) φ]
  定义体: ⟨φ, inferInstance⟩

@[simp]
-/
def homMk (p : 𝒳 ⥤ 𝒮) (S : 𝒮) {a b : 𝒳} (φ : a ⟶ b) [IsHomLift p (𝟙 S) φ] :
    mk (domain_eq p (𝟙 S) φ) ⟶ mk (codomain_eq p (𝟙 S) φ) :=
  ⟨φ, inferInstance⟩

@[simp]
/--
lemma `fiberInclusion_homMk` / 引理 `fiberInclusion_homMk`

English:
lemma fiberInclusion_homMk
  given: (p : 𝒳 ⥤ 𝒮) (S : 𝒮) {a b : 𝒳} (φ : a ⟶ b) [IsHomLift p (𝟙 S) φ]
  proof: rfl

@[simp]

中文:
引理 fiberInclusion_homMk
  条件: (p : 𝒳 ⥤ 𝒮) (S : 𝒮) {a b : 𝒳} (φ : a ⟶ b) [IsHomLift p (𝟙 S) φ]
  证明: rfl

@[simp]
-/
lemma fiberInclusion_homMk (p : 𝒳 ⥤ 𝒮) (S : 𝒮) {a b : 𝒳} (φ : a ⟶ b) [IsHomLift p (𝟙 S) φ] :
    fiberInclusion.map (homMk p S φ) = φ :=
  rfl

@[simp]
/--
lemma `homMk_id` / 引理 `homMk_id`

English:
lemma homMk_id
  given: (p : 𝒳 ⥤ 𝒮) (S : 𝒮) (a : 𝒳) [IsHomLift p (𝟙 S) (𝟙 a)]
  proof: rfl

@[simp]

中文:
引理 homMk_id
  条件: (p : 𝒳 ⥤ 𝒮) (S : 𝒮) (a : 𝒳) [IsHomLift p (𝟙 S) (𝟙 a)]
  证明: rfl

@[simp]
-/
lemma homMk_id (p : 𝒳 ⥤ 𝒮) (S : 𝒮) (a : 𝒳) [IsHomLift p (𝟙 S) (𝟙 a)] :
    homMk p S (𝟙 a) = 𝟙 (mk (domain_eq p (𝟙 S) (𝟙 a))) :=
  rfl

@[simp]
/--
lemma `homMk_comp` / 引理 `homMk_comp`

English:
lemma homMk_comp
  statement: {a b c : 𝒳} (φ : a ⟶ b) (ψ : b ⟶ c) [IsHomLift p (𝟙 S) φ]
  proof: rfl

中文:
引理 homMk_comp
  结论: {a b c : 𝒳} (φ : a ⟶ b) (ψ : b ⟶ c) [IsHomLift p (𝟙 S) φ]
  证明: rfl
-/
lemma homMk_comp {a b c : 𝒳} (φ : a ⟶ b) (ψ : b ⟶ c) [IsHomLift p (𝟙 S) φ]
    [IsHomLift p (𝟙 S) ψ] : homMk p S φ ≫ homMk p S ψ = homMk p S (φ ≫ ψ) :=
  rfl

section

variable {p : 𝒳 ⥤ 𝒮} {S : 𝒮} {C : Type u₃} [Category.{v₃} C] {F : C ⥤ 𝒳}
  (hF : F ⋙ p = (const C).obj S)

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `inducedFunctor` / `inducedFunctor` 的定义

English:
definition inducedFunctor
  signature: : C ⥤ Fiber p S where
  body: ⟨F.obj x, by simp only [← comp_obj, hF, const_obj_obj]⟩
map φ := ⟨F.map φ, of_commsq _ _ _ (congr_obj hF _) (congr_obj hF _)
    by simpa using (eqToIso hF).hom.naturality φ⟩

中文:
定义 inducedFunctor
  签名: : C ⥤ Fiber p S where
  定义体: ⟨F.obj x, by simp only [← comp_obj, hF, const_obj_obj]⟩
map φ := ⟨F.map φ, of_commsq _ _ _ (congr_obj hF _) (congr_obj hF _)
    by simpa using (eqToIso hF).hom.naturality φ⟩

Depends on / 依赖: F.obj, comp_obj, const_obj_obj
-/
def inducedFunctor : C ⥤ Fiber p S where
  obj x := ⟨F.obj x, by simp only [← comp_obj, hF, const_obj_obj]⟩
map φ := ⟨F.map φ, of_commsq _ _ _ (congr_obj hF _) (congr_obj hF _)
    by simpa using (eqToIso hF).hom.naturality φ⟩

/-- Given a functor `F : C ⥤ 𝒳` such that `F ⋙ p` is constant at some `S : 𝒮`, then
we get a natural isomorphism between `inducedFunctor _ ⋙ fiberInclusion` and `F`. -/
@[simps!]
/--
Definition of `inducedFunctorCompIsoSelf` / `inducedFunctorCompIsoSelf` 的定义

English:
definition inducedFunctorCompIsoSelf
  signature: : (inducedFunctor hF) ⋙ fiberInclusion ≅ F
  body: .refl _

中文:
定义 inducedFunctorCompIsoSelf
  签名: : (inducedFunctor hF) ⋙ fiberInclusion ≅ F
  定义体: .refl _

Depends on / 依赖: B.retract, instIsSplitMonoI, retract
-/
def inducedFunctorCompIsoSelf : (inducedFunctor hF) ⋙ fiberInclusion ≅ F := .refl _

/--
lemma `inducedFunctor_comp` / 引理 `inducedFunctor_comp`

English:
lemma inducedFunctor_comp
  statement: (inducedFunctor hF) ⋙ fiberInclusion = F
  proof: rfl

@[simp]

中文:
引理 inducedFunctor_comp
  结论: (inducedFunctor hF) ⋙ fiberInclusion = F
  证明: rfl

@[simp]

Depends on / 依赖: B.retract, instIsSplitEpiR, retract
-/
lemma inducedFunctor_comp : (inducedFunctor hF) ⋙ fiberInclusion = F := rfl

@[simp]
/--
lemma `inducedFunctor_comp_obj` / 引理 `inducedFunctor_comp_obj`

English:
lemma inducedFunctor_comp_obj
  given: (X : C)
  proof: rfl

@[simp]

中文:
引理 inducedFunctor_comp_obj
  条件: (X : C)
  证明: rfl

@[simp]
-/
lemma inducedFunctor_comp_obj (X : C) :
    fiberInclusion.obj ((inducedFunctor hF).obj X) = F.obj X := rfl

@[simp]
/--
lemma `inducedFunctor_comp_map` / 引理 `inducedFunctor_comp_map`

English:
lemma inducedFunctor_comp_map
  given: {X Y : C} (f : X ⟶ Y)
  proof: rfl

中文:
引理 inducedFunctor_comp_map
  条件: {X Y : C} (f : X ⟶ Y)
  证明: rfl
-/
lemma inducedFunctor_comp_map {X Y : C} (f : X ⟶ Y) :
    fiberInclusion.map ((inducedFunctor hF).map f) = F.map f := rfl

end

end Fiber

end Functor

end CategoryTheory
