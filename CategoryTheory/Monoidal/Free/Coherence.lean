/-
Copyright (c) 2021 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Monoidal.Free.Basic

/-!
# The monoidal coherence theorem

In this file, we prove the monoidal coherence theorem, stated in the following form: the free
monoidal category over any type `C` is thin.

We follow a proof described by Ilya Beylin and Peter Dybjer, which has been previously formalized
in the proof assistant ALF. The idea is to declare a normal form (with regard to association and
adding units) on objects of the free monoidal category and consider the discrete subcategory of
objects that are in normal form. A normalization procedure is then just a functor
`fullNormalize : FreeMonoidalCategory C ⥤ Discrete (NormalMonoidalObject C)`, where
functoriality says that two objects which are related by associators and unitors have the
same normal form. Another desirable property of a normalization procedure is that an object is
isomorphic (i.e., related via associators and unitors) to its normal form. In the case of the
specific normalization procedure we use we not only get these isomorphisms, but also that they
assemble into a natural isomorphism `𝟭 (FreeMonoidalCategory C) ≅ fullNormalize ⋙ inclusion`.
But this means that any two parallel morphisms in the free monoidal category factor through a
discrete category in the same way, so they must be equal, and hence the free monoidal category
is thin.

## References

* [Ilya Beylin and Peter Dybjer, Extracting a proof of coherence for monoidal categories from a
  proof of normalization for monoids][beylin1996]

-/

@[expose] public section


universe u

namespace CategoryTheory

open MonoidalCategory CategoryTheory.Functor

namespace FreeMonoidalCategory

variable {C : Type u}

section

variable (C)

/--
Inductive type `NormalMonoidalObject` / 归纳类型 `NormalMonoidalObject`

English:
inductive NormalMonoidalObject
  parameters: : Type u
  constructors (2):
    - unit: NormalMonoidalObject
    - tensor: NormalMonoidalObject -> C -> NormalMonoidalObject

中文:
归纳类型 NormalMonoidalObject
  参数: : 类型u
  构造子 (2 个):
    - unit: NormalMonoidalObject
    - tensor: NormalMonoidalObject -> C -> NormalMonoidalObject
-/
inductive NormalMonoidalObject : Type u
  | unit : NormalMonoidalObject
  | tensor : NormalMonoidalObject -> C -> NormalMonoidalObject

end

local notation "F" => FreeMonoidalCategory

local notation "N" => Discrete ∘ NormalMonoidalObject

local infixr:10 " ⟶ᵐ " => Hom

instance (x y : N C) : Subsingleton (x ⟶ y) := Discrete.instSubsingletonDiscreteHom _ _

/-- Auxiliary definition for `inclusion`. -/
@[simp]
/--
Definition of `inclusionObj` / `inclusionObj` 的定义

English:
definition inclusionObj
  signature: : NormalMonoidalObject C -> F C

中文:
定义 inclusionObj
  签名: : NormalMonoidalObject C -> F C
-/
def inclusionObj : NormalMonoidalObject C -> F C
  | NormalMonoidalObject.unit => unit
  | NormalMonoidalObject.tensor n a => tensor (inclusionObj n) (of a)

/--
Definition of `inclusion` / `inclusion` 的定义

English:
definition inclusion
  signature: : N C ⥤ F C
  body: Discrete.functor inclusionObj

@[simp]

中文:
定义 inclusion
  签名: : N C ⥤ F C
  定义体: Discrete.functor inclusionObj

@[simp]

Depends on / 依赖: Discrete, Discrete.functor, functor, inclusionObj
-/
def inclusion : N C ⥤ F C :=
  Discrete.functor inclusionObj

@[simp]
/--
theorem `inclusion_obj` / 定理 `inclusion_obj`

English:
theorem inclusion_obj
  given: (X : N C)
  proof: rfl

@[simp]

中文:
定理 inclusion_obj
  条件: (X : N C)
  证明: rfl

@[simp]
-/
theorem inclusion_obj (X : N C) :
    inclusion.obj X = inclusionObj X.as :=
  rfl

@[simp]
/--
theorem `inclusion_map` / 定理 `inclusion_map`

English:
theorem inclusion_map
  given: {X Y : N C} (f : X ⟶ Y)
  proof: rfl

中文:
定理 inclusion_map
  条件: {X Y : N C} (f : X ⟶ Y)
  证明: rfl
-/
theorem inclusion_map {X Y : N C} (f : X ⟶ Y) :
    inclusion.map f = eqToHom (congr_arg _ (Discrete.ext (Discrete.eq_of_hom f))) := rfl

/--
Definition of `normalizeObj` / `normalizeObj` 的定义

English:
definition normalizeObj
  signature: : F C -> NormalMonoidalObject C -> NormalMonoidalObject C

中文:
定义 normalizeObj
  签名: : F C -> NormalMonoidalObject C -> NormalMonoidalObject C
-/
def normalizeObj : F C -> NormalMonoidalObject C -> NormalMonoidalObject C
  | unit, n => n
  | of X, n => NormalMonoidalObject.tensor n X
  | tensor X Y, n => normalizeObj Y (normalizeObj X n)

@[simp]
/--
theorem `normalizeObj_unitor` / 定理 `normalizeObj_unitor`

English:
theorem normalizeObj_unitor
  given: (n : NormalMonoidalObject C)
  statement: normalizeObj (𝟙_ (F C)) n = n
  proof: rfl

@[simp]

中文:
定理 normalizeObj_unitor
  条件: (n : NormalMonoidalObject C)
  结论: normalizeObj (𝟙_ (F C)) n = n
  证明: rfl

@[simp]
-/
theorem normalizeObj_unitor (n : NormalMonoidalObject C) : normalizeObj (𝟙_ (F C)) n = n :=
  rfl

@[simp]
/--
theorem `normalizeObj_tensor` / 定理 `normalizeObj_tensor`

English:
theorem normalizeObj_tensor
  given: (X Y : F C) (n : NormalMonoidalObject C)
  proof: rfl

中文:
定理 normalizeObj_tensor
  条件: (X Y : F C) (n : NormalMonoidalObject C)
  证明: rfl
-/
theorem normalizeObj_tensor (X Y : F C) (n : NormalMonoidalObject C) :
    normalizeObj (X otimes Y) n = normalizeObj Y (normalizeObj X n) :=
  rfl

/--
Definition of `normalizeObj'` / `normalizeObj'` 的定义

English:
definition normalizeObj'
  signature: (X : F C)
  body: Discrete.functor fun n => ⟨normalizeObj X n⟩

@[simp]

中文:
定义 normalizeObj'
  签名: (X : F C)
  定义体: Discrete.functor fun n => ⟨normalizeObj X n⟩

@[simp]

Depends on / 依赖: Discrete, Discrete.functor, functor, normalizeObj
-/
def normalizeObj' (X : F C) : N C ⥤ N C := Discrete.functor fun n => ⟨normalizeObj X n⟩

@[simp]
/--
theorem `as_obj_normalizeObj'` / 定理 `as_obj_normalizeObj'`

English:
theorem as_obj_normalizeObj'
  given: (X : F C) (n : N C)
  proof: rfl

中文:
定理 as_obj_normalizeObj'
  条件: (X : F C) (n : N C)
  证明: rfl
-/
theorem as_obj_normalizeObj' (X : F C) (n : N C) :
    ((normalizeObj' X).obj n).as = normalizeObj X n.as := rfl

section

open Hom

/-- Auxiliary definition for `normalize`. Here we prove that objects that are related by
associators and unitors map to the same normal form. -/
@[simp]
/--
Definition of `normalizeMapAux` / `normalizeMapAux` 的定义

English:
definition normalizeMapAux
  signature: : forall {X Y : F C}, (X ⟶ᵐ Y) -> (normalizeObj' X ⟶ normalizeObj' Y)

中文:
定义 normalizeMapAux
  签名: : 对任意 {X Y : F C}, (X ⟶ᵐ Y) -> (normalizeObj' X ⟶ normalizeObj' Y)
-/
def normalizeMapAux : forall {X Y : F C}, (X ⟶ᵐ Y) -> (normalizeObj' X ⟶ normalizeObj' Y)
  | _, _, Hom.id _ => 𝟙 _
  | _, _, α_hom X Y Z => by dsimp; exact Discrete.natTrans (fun _ => 𝟙 _)
  | _, _, α_inv _ _ _ => by dsimp; exact Discrete.natTrans (fun _ => 𝟙 _)
  | _, _, l_hom _ => by dsimp; exact Discrete.natTrans (fun _ => 𝟙 _)
  | _, _, l_inv _ => by dsimp; exact Discrete.natTrans (fun _ => 𝟙 _)
  | _, _, ρ_hom _ => by dsimp; exact Discrete.natTrans (fun _ => 𝟙 _)
  | _, _, ρ_inv _ => by dsimp; exact Discrete.natTrans (fun _ => 𝟙 _)
  | _, _, (@Hom.comp _ _ _ _ f g) => normalizeMapAux f ≫ normalizeMapAux g
  | _, _, (@Hom.tensor _ T _ _ W f g) =>
Discrete.natTrans fun ⟨X⟩ => (normalizeMapAux g).app ⟨normalizeObj T X⟩ ≫
      (normalizeObj' W).map ((normalizeMapAux f).app ⟨X⟩)
  | _, _, (@Hom.whiskerLeft _ T _ W f) =>
Discrete.natTrans fun ⟨X⟩ => (normalizeMapAux f).app ⟨normalizeObj T X⟩
  | _, _, (@Hom.whiskerRight _ T _ f W) =>
Discrete.natTrans fun X => (normalizeObj' W).map (normalizeMapAux f).app X

end

section

variable (C)

set_option backward.isDefEq.respectTransparency false in
/-- Our normalization procedure works by first defining a functor `F C ⥤ (N C ⥤ N C)` (which turns
out to be very easy), and then obtain a functor `F C ⥤ N C` by plugging in the normal object
`𝟙_ C`. -/
@[simp]
/--
Definition of `normalize` / `normalize` 的定义

English:
definition normalize
  signature: : F C ⥤ N C ⥤ N C where
  body: normalizeObj' X
  map {X Y} := Quotient.lift normalizeMapAux (by cat_disch)

中文:
定义 normalize
  签名: : F C ⥤ N C ⥤ N C where
  定义体: normalizeObj' X
  map {X Y} := Quotient.lift normalizeMapAux (by cat_disch)

Depends on / 依赖: normalizeObj
-/
def normalize : F C ⥤ N C ⥤ N C where
  obj X := normalizeObj' X
  map {X Y} := Quotient.lift normalizeMapAux (by cat_disch)

/-- A variant of the normalization functor where we consider the result as an object in the free
monoidal category (rather than an object of the discrete subcategory of objects in normal form). -/
@[simp]
/--
Definition of `normalize'` / `normalize'` 的定义

English:
definition normalize'
  signature: : F C ⥤ N C ⥤ F C
  body: normalize C ⋙ (whiskeringRight _ _ _).obj inclusion

中文:
定义 normalize'
  签名: : F C ⥤ N C ⥤ F C
  定义体: normalize C ⋙ (whiskeringRight _ _ _).obj inclusion

Depends on / 依赖: inclusion, normalize, whiskeringRight
-/
def normalize' : F C ⥤ N C ⥤ F C :=
  normalize C ⋙ (whiskeringRight _ _ _).obj inclusion

/--
Definition of `fullNormalize` / `fullNormalize` 的定义

English:
definition fullNormalize
  signature: : F C ⥤ N C where
  body: ((normalize C).obj X).obj ⟨NormalMonoidalObject.unit⟩
  map f := ((normalize C).map f).app ⟨NormalMonoidalObject.unit⟩

中文:
定义 fullNormalize
  签名: : F C ⥤ N C where
  定义体: ((normalize C).obj X).obj ⟨NormalMonoidalObject.unit⟩
  map f := ((normalize C).map f).app ⟨NormalMonoidalObject.unit⟩

Depends on / 依赖: NormalMonoidalObject, NormalMonoidalObject.unit, normalize
-/
def fullNormalize : F C ⥤ N C where
  obj X := ((normalize C).obj X).obj ⟨NormalMonoidalObject.unit⟩
  map f := ((normalize C).map f).app ⟨NormalMonoidalObject.unit⟩

/-- Given an object `X` of the free monoidal category and an object `n` in normal form, taking
the tensor product `n ⊗ X` in the free monoidal category is functorial in both `X` and `n`. -/
@[simp]
/--
Definition of `tensorFunc` / `tensorFunc` 的定义

English:
definition tensorFunc
  signature: : F C ⥤ N C ⥤ F C where
  body: Discrete.functor fun n => inclusion.obj ⟨n⟩ otimes X
  map f := Discrete.natTrans (fun _ => _ ◁ f)

中文:
定义 tensorFunc
  签名: : F C ⥤ N C ⥤ F C where
  定义体: Discrete.functor fun n => inclusion.obj ⟨n⟩ otimes X
  map f := Discrete.natTrans (fun _ => _ ◁ f)

Depends on / 依赖: Category, Category.comp_id, Discrete, Discrete.functor, Iso.refl_inv, PreZeroHypercover, PreZeroHypercover.Hom.ext, comp_id, congrIndexOneOfEqIso_refl, eqToHom_refl, functor, heq_eq_eq, implies_true, inclusion, inclusion.obj, mk.injEq, otimes, refl_inv, toHomf, toHomg
-/
def tensorFunc : F C ⥤ N C ⥤ F C where
  obj X := Discrete.functor fun n => inclusion.obj ⟨n⟩ otimes X
  map f := Discrete.natTrans (fun _ => _ ◁ f)

/--
theorem `tensorFunc_map_app` / 定理 `tensorFunc_map_app`

English:
theorem tensorFunc_map_app
  given: {X Y : F C} (f : X ⟶ Y) (n)
  statement: ((tensorFunc C).map f).app n = _ ◁ f
  proof: rfl

中文:
定理 tensorFunc_map_app
  条件: {X Y : F C} (f : X ⟶ Y) (n)
  结论: ((tensorFunc C).map f).app n = _ ◁ f
  证明: rfl

Depends on / 依赖: Hom.ext, congrIndexOneOfEq
-/
theorem tensorFunc_map_app {X Y : F C} (f : X ⟶ Y) (n) : ((tensorFunc C).map f).app n = _ ◁ f :=
  rfl

/--
theorem `tensorFunc_obj_map` / 定理 `tensorFunc_obj_map`

English:
theorem tensorFunc_obj_map
  given: (Z : F C) {n n' : N C} (f : n ⟶ n')
  proof: by
  cases n
  cases n'
  rcases f with ⟨⟨h⟩⟩
  dsimp at h
  subst h
  simp

中文:
定理 tensorFunc_obj_map
  条件: (Z : F C) {n n' : N C} (f : n ⟶ n')
  证明: by
  cases n
  cases n'
  rcases f with ⟨⟨h⟩⟩
  dsimp at h
  subst h
  simp
-/
theorem tensorFunc_obj_map (Z : F C) {n n' : N C} (f : n ⟶ n') :
    ((tensorFunc C).obj Z).map f = inclusion.map f ▷ Z := by
  cases n
  cases n'
  rcases f with ⟨⟨h⟩⟩
  dsimp at h
  subst h
  simp

/-- Auxiliary definition for `normalizeIso`. Here we construct the isomorphism between
`n ⊗ X` and `normalize X n`. -/
@[simp]
/--
Definition of `normalizeIsoApp` / `normalizeIsoApp` 的定义

English:
definition normalizeIsoApp
  signature: :

中文:
定义 normalizeIsoApp
  签名: :
-/
def normalizeIsoApp :
    forall (X : F C) (n : N C), ((tensorFunc C).obj X).obj n ≅ ((normalize' C).obj X).obj n
  | of _, _ => Iso.refl _
  | unit, _ => ρ_ _
  | tensor X a, n =>
    (α_ _ _ _).symm ≪≫ whiskerRightIso (normalizeIsoApp X n) a ≪≫ normalizeIsoApp _ _

/--
Definition of `normalizeIsoApp'` / `normalizeIsoApp'` 的定义

English:
definition normalizeIsoApp'
  signature: :

中文:
定义 normalizeIsoApp'
  签名: :
-/
def normalizeIsoApp' :
    forall (X : F C) (n : NormalMonoidalObject C), inclusionObj n otimes X ≅ inclusionObj (normalizeObj X n)
  | of _, _ => Iso.refl _
  | unit, _ => ρ_ _
  | tensor X Y, n =>
    (α_ _ _ _).symm ≪≫ whiskerRightIso (normalizeIsoApp' X n) Y ≪≫ normalizeIsoApp' _ _

/--
theorem `normalizeIsoApp'_tensor` / 定理 `normalizeIsoApp'_tensor`

English:
theorem normalizeIsoApp'_tensor
  given: (X Y : F C) (n : NormalMonoidalObject C)
  proof: rfl

中文:
定理 normalizeIsoApp'_tensor
  条件: (X Y : F C) (n : NormalMonoidalObject C)
  证明: rfl
-/
@[simp] theorem normalizeIsoApp'_tensor (X Y : F C) (n : NormalMonoidalObject C) :
    normalizeIsoApp' C (X otimes Y) n =
      (α_ _ _ _).symm ≪≫ whiskerRightIso (normalizeIsoApp' C X n) Y ≪≫
        normalizeIsoApp' C Y _ := rfl

/--
theorem `normalizeIsoApp'_unit` / 定理 `normalizeIsoApp'_unit`

English:
theorem normalizeIsoApp'_unit
  given: (n : NormalMonoidalObject C)
  proof: rfl

中文:
定理 normalizeIsoApp'_unit
  条件: (n : NormalMonoidalObject C)
  证明: rfl
-/
@[simp] theorem normalizeIsoApp'_unit (n : NormalMonoidalObject C) :
    normalizeIsoApp' C (𝟙_ (F C)) n = ρ_ _ := rfl

set_option backward.defeqAttrib.useBackward true in
/--
theorem `normalizeIsoApp_eq` / 定理 `normalizeIsoApp_eq`

English:
theorem normalizeIsoApp_eq

中文:
定理 normalizeIsoApp_eq
-/
theorem normalizeIsoApp_eq :
    forall (X : F C) (n : N C), normalizeIsoApp C X n = normalizeIsoApp' C X n.as
  | of _, _ => rfl
  | unit, _ => rfl
  | tensor X Y, n => by
      rw [normalizeIsoApp]; rw [normalizeIsoApp']
      rw [normalizeIsoApp_eq X n]
      rw [normalizeIsoApp_eq Y ⟨normalizeObj X n.as⟩]
      simp

@[simp]
/--
theorem `normalizeIsoApp_tensor` / 定理 `normalizeIsoApp_tensor`

English:
theorem normalizeIsoApp_tensor
  given: (X Y : F C) (n : N C)
  proof: rfl

@[simp]

中文:
定理 normalizeIsoApp_tensor
  条件: (X Y : F C) (n : N C)
  证明: rfl

@[simp]
-/
theorem normalizeIsoApp_tensor (X Y : F C) (n : N C) :
    normalizeIsoApp C (X otimes Y) n =
      (α_ _ _ _).symm ≪≫ whiskerRightIso (normalizeIsoApp C X n) Y ≪≫ normalizeIsoApp _ _ _ :=
  rfl

@[simp]
/--
theorem `normalizeIsoApp_unitor` / 定理 `normalizeIsoApp_unitor`

English:
theorem normalizeIsoApp_unitor
  given: (n : N C)
  statement: normalizeIsoApp C (𝟙_ (F C)) n = ρ_ _
  proof: rfl

中文:
定理 normalizeIsoApp_unitor
  条件: (n : N C)
  结论: normalizeIsoApp C (𝟙_ (F C)) n = ρ_ _
  证明: rfl
-/
theorem normalizeIsoApp_unitor (n : N C) : normalizeIsoApp C (𝟙_ (F C)) n = ρ_ _ :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- Auxiliary definition for `normalizeIso`. -/
@[simps!]
/--
Definition of `normalizeIsoAux` / `normalizeIsoAux` 的定义

English:
definition normalizeIsoAux
  signature: (X : F C)
  body: NatIso.ofComponents (normalizeIsoApp C X)
    (by
      rintro ⟨X⟩ ⟨Y⟩ ⟨⟨f⟩⟩
      dsimp at f
      subst f
      dsimp
      simp)

中文:
定义 normalizeIsoAux
  签名: (X : F C)
  定义体: NatIso.ofComponents (normalizeIsoApp C X)
    (by
      rintro ⟨X⟩ ⟨Y⟩ ⟨⟨f⟩⟩
      dsimp at f
      subst f
      dsimp
      simp)

Depends on / 依赖: NatIso, NatIso.ofComponents, normalizeIsoApp, ofComponents
-/
def normalizeIsoAux (X : F C) : (tensorFunc C).obj X ≅ (normalize' C).obj X :=
  NatIso.ofComponents (normalizeIsoApp C X)
    (by
      rintro ⟨X⟩ ⟨Y⟩ ⟨⟨f⟩⟩
      dsimp at f
      subst f
      dsimp
      simp)


section

variable {C}

/--
theorem `normalizeObj_congr` / 定理 `normalizeObj_congr`

English:
theorem normalizeObj_congr
  given: (n : NormalMonoidalObject C) {X Y : F C} (f : X ⟶ Y)
  proof: by
  rcases f with ⟨f'⟩
  apply @congr_fun _ _ fun n => normalizeObj X n
  clear n f
  induction f' with
  | comp _ _ _ _ => apply Eq.trans <;> assumption
  | whiskerLeft _ _ ih => funext; apply congr_fun ih
  | whiskerRight _ _ ih => funext; apply congr_arg₂ _ rfl (congr_fun ih _)
  | @tensor W X Y Z _ _ ih₁ ih₂ =>
      funext n
      simp [congr_fun ih₁ n, congr_fun ih₂ (normalizeObj Y n)]
  | _ => funext; rfl

中文:
定理 normalizeObj_congr
  条件: (n : NormalMonoidalObject C) {X Y : F C} (f : X ⟶ Y)
  证明: by
  rcases f with ⟨f'⟩
  apply @congr_fun _ _ fun n => normalizeObj X n
  clear n f
  induction f' with
  | comp _ _ _ _ => apply Eq.trans <;> assumption
  | whiskerLeft _ _ ih => funext; apply congr_fun ih
  | whiskerRight _ _ ih => funext; apply congr_arg₂ _ rfl (congr_fun ih _)
  | @tensor W X Y Z _ _ ih₁ ih₂ =>
      funext n
      simp [congr_fun ih₁ n, congr_fun ih₂ (normalizeObj Y n)]
  | _ => funext; rfl

Depends on / 依赖: Eq.trans, congr_fun, normalizeObj, tensor, whiskerLeft, whiskerRight
-/
theorem normalizeObj_congr (n : NormalMonoidalObject C) {X Y : F C} (f : X ⟶ Y) :
    normalizeObj X n = normalizeObj Y n := by
  rcases f with ⟨f'⟩
  apply @congr_fun _ _ fun n => normalizeObj X n
  clear n f
  induction f' with
  | comp _ _ _ _ => apply Eq.trans <;> assumption
  | whiskerLeft _ _ ih => funext; apply congr_fun ih
  | whiskerRight _ _ ih => funext; apply congr_arg₂ _ rfl (congr_fun ih _)
  | @tensor W X Y Z _ _ ih₁ ih₂ =>
      funext n
      simp [congr_fun ih₁ n, congr_fun ih₂ (normalizeObj Y n)]
  | _ => funext; rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
theorem `normalize_naturality` / 定理 `normalize_naturality`

English:
theorem normalize_naturality
  given: (n : NormalMonoidalObject C) {X Y : F C} (f : X ⟶ Y)
  proof: by
  revert n
  induction f using Hom.inductionOn
  case comp f g ihf ihg => simp [ihg, reassoc_of% (ihf _)]
  case whiskerLeft X' X Y f ih =>
    intro n
    dsimp only [normalizeObj_tensor, normalizeIsoApp'_tensor, Iso.trans_hom,
      Iso.symm_hom, whiskerRightIso_hom, Function.comp_apply, inclusion_obj]
    rw [associator_inv_naturality_right_assoc]; rw [whisker_exchange_assoc]; rw [ih]
    simp
  case whiskerRight X Y h η' ih =>
    intro n
    dsimp only [normalizeObj_tensor, normalizeIsoApp'_tensor, Iso.trans_hom,
      Iso.symm_hom, whiskerRightIso_hom, Function.comp_apply, inclusion_obj]
    rw [associator_inv_naturality_middle_assoc]; rw [← comp_whiskerRight_assoc]; rw [ih]
    have := dcongr_arg (fun x => (normalizeIsoApp' C η' x).hom) (normalizeObj_congr n h)
    simp [this]
  all_goals simp

中文:
定理 normalize_naturality
  条件: (n : NormalMonoidalObject C) {X Y : F C} (f : X ⟶ Y)
  证明: by
  revert n
  induction f using Hom.inductionOn
  case comp f g ihf ihg => simp [ihg, reassoc_of% (ihf _)]
  case whiskerLeft X' X Y f ih =>
    intro n
    dsimp only [normalizeObj_tensor, normalizeIsoApp'_tensor, Iso.trans_hom,
      Iso.symm_hom, whiskerRightIso_hom, Function.comp_apply, inclusion_obj]
    rw [associator_inv_naturality_right_assoc]; rw [whisker_exchange_assoc]; rw [ih]
    simp
  case whiskerRight X Y h η' ih =>
    intro n
    dsimp only [normalizeObj_tensor, normalizeIsoApp'_tensor, Iso.trans_hom,
      Iso.symm_hom, whiskerRightIso_hom, Function.comp_apply, inclusion_obj]
    rw [associator_inv_naturality_middle_assoc]; rw [← comp_whiskerRight_assoc]; rw [ih]
    have := dcongr_arg (fun x => (normalizeIsoApp' C η' x).hom) (normalizeObj_congr n h)
    simp [this]
  all_goals simp

Depends on / 依赖: Function, Function.comp_apply, Hom.inductionOn, Iso.symm_hom, Iso.trans_hom, _tensor, associator_inv_naturality_right_assoc, comp_apply, inclusion_obj, inductionOn, normalizeIsoApp, normalizeObj_tensor, reassoc_of, revert, symm_hom, trans_hom, whiskerLeft, whiskerRight, whiskerRightIso_hom, whisker_exchange_assoc
-/
theorem normalize_naturality (n : NormalMonoidalObject C) {X Y : F C} (f : X ⟶ Y) :
    inclusionObj n ◁ f ≫ (normalizeIsoApp' C Y n).hom =
      (normalizeIsoApp' C X n).hom ≫
        inclusion.map (eqToHom (Discrete.ext (normalizeObj_congr n f))) := by
  revert n
  induction f using Hom.inductionOn
  case comp f g ihf ihg => simp [ihg, reassoc_of% (ihf _)]
  case whiskerLeft X' X Y f ih =>
    intro n
    dsimp only [normalizeObj_tensor, normalizeIsoApp'_tensor, Iso.trans_hom,
      Iso.symm_hom, whiskerRightIso_hom, Function.comp_apply, inclusion_obj]
    rw [associator_inv_naturality_right_assoc]; rw [whisker_exchange_assoc]; rw [ih]
    simp
  case whiskerRight X Y h η' ih =>
    intro n
    dsimp only [normalizeObj_tensor, normalizeIsoApp'_tensor, Iso.trans_hom,
      Iso.symm_hom, whiskerRightIso_hom, Function.comp_apply, inclusion_obj]
    rw [associator_inv_naturality_middle_assoc]; rw [← comp_whiskerRight_assoc]; rw [ih]
    have := dcongr_arg (fun x => (normalizeIsoApp' C η' x).hom) (normalizeObj_congr n h)
    simp [this]
  all_goals simp

end

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `normalizeIso` / `normalizeIso` 的定义

English:
definition normalizeIso
  signature: : tensorFunc C ≅ normalize' C
  body: NatIso.ofComponents (normalizeIsoAux C) by
    intro X Y f
    ext ⟨n⟩
    convert! normalize_naturality n f using 1
    any_goals dsimp; rw [normalizeIsoApp_eq]

中文:
定义 normalizeIso
  签名: : tensorFunc C ≅ normalize' C
  定义体: NatIso.ofComponents (normalizeIsoAux C) by
    intro X Y f
    ext ⟨n⟩
    convert! normalize_naturality n f using 1
    any_goals dsimp; rw [normalizeIsoApp_eq]

Depends on / 依赖: Category, Category.assoc, NatIso, NatIso.ofComponents, PreOneHypercover, PreOneHypercover.hom_inv_h, PreOneHypercover.inv_hom_h, any_goals, convert, e.hom.s, e.inv.h, eqToHom, eqToHom_naturality, eqToHom_refl, eqToHom_trans, normalizeIsoApp_eq, normalizeIsoAux, normalize_naturality, ofComponents
-/
def normalizeIso : tensorFunc C ≅ normalize' C :=
NatIso.ofComponents (normalizeIsoAux C) by
    intro X Y f
    ext ⟨n⟩
    convert! normalize_naturality n f using 1
    any_goals dsimp; rw [normalizeIsoApp_eq]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `fullNormalizeIso` / `fullNormalizeIso` 的定义

English:
definition fullNormalizeIso
  signature: : 𝟭 (F C) ≅ fullNormalize C ⋙ inclusion
  body: NatIso.ofComponents
  (fun X => (fun_ X).symm ≪≫ ((normalizeIso C).app X).app ⟨NormalMonoidalObject.unit⟩)
    (by
      intro X Y f
      dsimp
      rw [leftUnitor_inv_naturality_assoc]; rw [Category.assoc]; rw [Iso.cancel_iso_inv_left]
      exact
        congr_arg (fun f => NatTrans.app f (Discrete.mk NormalMonoidalObject.unit))
          ((normalizeIso.{u} C).hom.naturality f))

中文:
定义 fullNormalizeIso
  签名: : 𝟭 (F C) ≅ fullNormalize C ⋙ inclusion
  定义体: NatIso.ofComponents
  (fun X => (fun_ X).symm ≪≫ ((normalizeIso C).app X).app ⟨NormalMonoidalObject.unit⟩)
    (by
      intro X Y f
      dsimp
      rw [leftUnitor_inv_naturality_assoc]; rw [Category.assoc]; rw [Iso.cancel_iso_inv_left]
      exact
        congr_arg (fun f => NatTrans.app f (Discrete.mk NormalMonoidalObject.unit))
          ((normalizeIso.{u} C).hom.naturality f))

Depends on / 依赖: Category, Category.assoc, Discrete, Discrete.mk, Iso.cancel_iso_inv_left, NatIso, NatIso.ofComponents, NatTrans, NatTrans.app, NormalMonoidalObject, NormalMonoidalObject.unit, PreOneHypercover, PreOneHypercover.inv_hom_h, cancel_iso_inv_left, congr_arg, fun_, hom.naturality, leftUnitor_inv_naturality_assoc, naturality, normalizeIso
-/
def fullNormalizeIso : 𝟭 (F C) ≅ fullNormalize C ⋙ inclusion :=
  NatIso.ofComponents
  (fun X => (fun_ X).symm ≪≫ ((normalizeIso C).app X).app ⟨NormalMonoidalObject.unit⟩)
    (by
      intro X Y f
      dsimp
      rw [leftUnitor_inv_naturality_assoc]; rw [Category.assoc]; rw [Iso.cancel_iso_inv_left]
      exact
        congr_arg (fun f => NatTrans.app f (Discrete.mk NormalMonoidalObject.unit))
          ((normalizeIso.{u} C).hom.naturality f))

end

/--
Instance `subsingleton_hom` / 实例 `subsingleton_hom`

English:
instance subsingleton_hom
  signature: : Quiver.IsThin (F C)
  body: fun X Y =>
  ⟨fun f g => by
    have hfg : (fullNormalize C).map f = (fullNormalize C).map g := Subsingleton.elim _ _
    have hf := NatIso.naturality_2 (fullNormalizeIso.{u} C) f
    have hg := NatIso.naturality_2 (fullNormalizeIso.{u} C) g
    exact hf.symm.trans (Eq.trans (by simp only [Functor.comp_map, hfg]) hg)⟩

中文:
实例 subsingleton_hom
  签名: : 箭图.IsThin (F C)
  定义体: fun X Y =>
  ⟨fun f g => by
    have hfg : (fullNormalize C).map f = (fullNormalize C).map g := Subsingleton.elim _ _
    have hf := NatIso.naturality_2 (fullNormalizeIso.{u} C) f
    have hg := NatIso.naturality_2 (fullNormalizeIso.{u} C) g
    exact hf.symm.trans (Eq.trans (by simp only [Functor.comp_map, hfg]) hg)⟩

Depends on / 依赖: Category, Category.assoc, Category.id_comp, E.congrIndexOneOfEqIso, Iso.inv_hom_id, PreOneHypercover, PreOneHypercover.congrIndexOneOfEqIso_hom_naturality, PreOneHypercover.hom_inv_h, congrIndexOneOfEqIso, congrIndexOneOfEqIso_hom_naturality, e.inv.h, eqToHom, eqToHom_naturality_assoc, eqToHom_refl, eqToHom_trans_assoc, id_comp, inv_hom_id, true_and
-/
instance subsingleton_hom : Quiver.IsThin (F C) := fun X Y =>
  ⟨fun f g => by
    have hfg : (fullNormalize C).map f = (fullNormalize C).map g := Subsingleton.elim _ _
    have hf := NatIso.naturality_2 (fullNormalizeIso.{u} C) f
    have hg := NatIso.naturality_2 (fullNormalizeIso.{u} C) g
    exact hf.symm.trans (Eq.trans (by simp only [Functor.comp_map, hfg]) hg)⟩

section Groupoid

section

open Hom

/--
Definition of `inverseAux` / `inverseAux` 的定义

English:
definition inverseAux
  signature: : forall {X Y : F C}, (X ⟶ᵐ Y) -> (Y ⟶ᵐ X)

中文:
定义 inverseAux
  签名: : 对任意 {X Y : F C}, (X ⟶ᵐ Y) -> (Y ⟶ᵐ X)

Depends on / 依赖: PreOneHypercover, PreOneHypercover.inv_hom_h, of_isIso_fac_right
-/
def inverseAux : forall {X Y : F C}, (X ⟶ᵐ Y) -> (Y ⟶ᵐ X)
  | _, _, Hom.id X => id X
  | _, _, α_hom _ _ _ => α_inv _ _ _
  | _, _, α_inv _ _ _ => α_hom _ _ _
  | _, _, ρ_hom _ => ρ_inv _
  | _, _, ρ_inv _ => ρ_hom _
  | _, _, l_hom _ => l_inv _
  | _, _, l_inv _ => l_hom _
  | _, _, Hom.comp f g => (inverseAux g).comp (inverseAux f)
  | _, _, Hom.whiskerLeft X f => (inverseAux f).whiskerLeft X
  | _, _, Hom.whiskerRight f X => (inverseAux f).whiskerRight X
  | _, _, Hom.tensor f g => (inverseAux f).tensor (inverseAux g)

end

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Groupoid.{u} (F C)
  body: { (inferInstance : Category (F C)) with
    inv := Quotient.lift (fun f => ⟦inverseAux f⟧) (by cat_disch) }

中文:
实例 :
  签名: 群胚.{u} (F C)
  定义体: { (inferInstance : Category (F C)) with
    inv := Quotient.lift (fun f => ⟦inverseAux f⟧) (by cat_disch) }

Depends on / 依赖: Category, Quotient, Quotient.lift, cat_disch, inverseAux
-/
instance : Groupoid.{u} (F C) :=
  { (inferInstance : Category (F C)) with
    inv := Quotient.lift (fun f => ⟦inverseAux f⟧) (by cat_disch) }

end Groupoid

end FreeMonoidalCategory

end CategoryTheory
