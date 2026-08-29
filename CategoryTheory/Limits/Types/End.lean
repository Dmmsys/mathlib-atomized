/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Limits.Chosen.End

/-!
# Ends and coends in `Type`

This file constructs explicit ends and coends in `Type` and provides
`ChosenEnds` and `ChosenCoends` instances using these constructions.
-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Opposite TypeCat ConcreteCategory

namespace Limits.Types

variable {J : Type u} [Category.{v} J] (F : Jᵒᵖ ⥤ J ⥤ Type max w u)

/--
Inductive type `coendRel` / 归纳类型 `coendRel`

English:
inductive coendRel
  parameters: : (j : J) × (F.obj (op j)).obj j -> (j : J) × (F.obj (op j)).obj j -> Prop where
  constructors (1):
    - mk: {j j' : J} (f : j ⟶ j') (x : (F.obj (op j')).obj j) : coendRel ⟨j, TypeCat.Hom.hom ((F.map f.op).app _) x⟩ ⟨j', TypeCat.Hom.hom ((F.obj _).map f) x⟩

中文:
归纳类型 coendRel
  参数: : (j : J) × (F.obj (op j)).obj j -> (j : J) × (F.obj (op j)).obj j -> 命题 where
  构造子 (1 个):
    - mk: {j j' : J} (f : j ⟶ j') (x : (F.obj (op j')).obj j) : coendRel ⟨j, TypeCat.Hom.hom ((F.map f.op).app _) x⟩ ⟨j', TypeCat.Hom.hom ((F.obj _).map f) x⟩
-/
inductive coendRel : (j : J) × (F.obj (op j)).obj j -> (j : J) × (F.obj (op j)).obj j -> Prop where
  | mk {j j' : J} (f : j ⟶ j') (x : (F.obj (op j')).obj j) :
    coendRel ⟨j, TypeCat.Hom.hom ((F.map f.op).app _) x⟩
      ⟨j', TypeCat.Hom.hom ((F.obj _).map f) x⟩

/--
lemma `coendRel_iff` / 引理 `coendRel_iff`

English:
lemma coendRel_iff
  given: (j j' : J) (x : (F.obj (op j)).obj j) (x' : (F.obj (op j')).obj j')
  proof: by
  constructor
  · rintro ⟨f, x⟩
    exact ⟨f, x, by simp⟩
  · rintro ⟨f, y, rfl, rfl⟩
    exact coendRel.mk f y

中文:
引理 coendRel_iff
  条件: (j j' : J) (x : (F.obj (op j)).obj j) (x' : (F.obj (op j')).obj j')
  证明: by
  constructor
  · rintro ⟨f, x⟩
    exact ⟨f, x, by simp⟩
  · rintro ⟨f, y, rfl, rfl⟩
    exact coendRel.mk f y

Depends on / 依赖: coendRel, coendRel.mk
-/
lemma coendRel_iff (j j' : J) (x : (F.obj (op j)).obj j) (x' : (F.obj (op j')).obj j') :
    coendRel F ⟨j, x⟩ ⟨j', x'⟩ ↔
      exists (f : j ⟶ j') (y : (F.obj (op j')).obj j),
        (F.map f.op).app _ y = x ∧ (F.obj _).map f y = x' := by
  constructor
  · rintro ⟨f, x⟩
    exact ⟨f, x, by simp⟩
  · rintro ⟨f, y, rfl, rfl⟩
    exact coendRel.mk f y

/--
Definition of `coend` / `coend` 的定义

English:
abbreviation coend
  signature: : Type max w u
  body: Quot (coendRel F)

中文:
缩写 coend
  签名: : Type max w u
  定义体: Quot (coendRel F)

Depends on / 依赖: coendRel
-/
abbrev coend : Type max w u := Quot (coendRel F)

/--
Definition of `coend.ι` / `coend.ι` 的定义

English:
definition coend.ι
  signature: (j : J)
  body: ↾fun x => Quot.mk _ ⟨j, x⟩

中文:
定义 coend.ι
  签名: (j : J)
  定义体: ↾fun x => Quot.mk _ ⟨j, x⟩
-/
def coend.ι (j : J) : (F.obj (op j)).obj j ⟶ coend F := ↾fun x => Quot.mk _ ⟨j, x⟩

variable {F}

@[reassoc]
/--
lemma `coend.condition` / 引理 `coend.condition`

English:
lemma coend.condition
  given: {j j' : J} (f : j ⟶ j')
  proof: by
  ext
  apply Quot.sound
  apply coendRel.mk

中文:
引理 coend.condition
  条件: {j j' : J} (f : j ⟶ j')
  证明: by
  ext
  apply Quot.sound
  apply coendRel.mk
-/
lemma coend.condition {j j' : J} (f : j ⟶ j') :
    (F.map f.op).app _ ≫ coend.ι F j = (F.obj _).map f ≫ coend.ι F j' := by
  ext
  apply Quot.sound
  apply coendRel.mk

variable (F)

/--
Definition of `cowedge` / `cowedge` 的定义

English:
definition cowedge
  signature: : Cowedge F
  body: Cowedge.mk (coend F) (coend.ι F) (by intros; apply coend.condition)

中文:
定义 cowedge
  签名: : Cowedge F
  定义体: Cowedge.mk (coend F) (coend.ι F) (by intros; apply coend.condition)

Depends on / 依赖: Cowedge, Cowedge.mk, coend.condition, condition, intros
-/
def cowedge : Cowedge F := Cowedge.mk (coend F) (coend.ι F) (by intros; apply coend.condition)

/--
Definition of `cowedgeIsColimit` / `cowedgeIsColimit` 的定义

English:
definition cowedgeIsColimit
  signature: : IsColimit (cowedge F) where
  body: TypeCat.ofHom Quot.lift (fun x => Multicofork.π s x.fst x.snd) fun _ _ h => by
    cases h with | mk f x => exact ConcreteCategory.congr_hom (Cowedge.condition s f) _
  fac s := by rintro (_ | _) <;> cat_disch
  uniq s m h := by ext ⟨j⟩; exact ConcreteCategory.congr_hom (h (.right j.fst)) j.snd

中文:
定义 cowedgeIsColimit
  签名: : IsColimit (cowedge F) where
  定义体: TypeCat.ofHom Quot.lift (fun x => Multicofork.π s x.fst x.snd) fun _ _ h => by
    cases h with | mk f x => exact ConcreteCategory.congr_hom (Cowedge.condition s f) _
  fac s := by rintro (_ | _) <;> cat_disch
  uniq s m h := by ext ⟨j⟩; exact ConcreteCategory.congr_hom (h (.right j.fst)) j.snd

Depends on / 依赖: ConcreteCategory, ConcreteCategory.congr_hom, Cowedge, Cowedge.condition, Multicofork, Quot.lift, TypeCat, TypeCat.ofHom, cat_disch, condition, congr_hom, j.fst, j.snd, x.fst, x.snd
-/
def cowedgeIsColimit : IsColimit (cowedge F) where
desc s := TypeCat.ofHom Quot.lift (fun x => Multicofork.π s x.fst x.snd) fun _ _ h => by
    cases h with | mk f x => exact ConcreteCategory.congr_hom (Cowedge.condition s f) _
  fac s := by rintro (_ | _) <;> cat_disch
  uniq s m h := by ext ⟨j⟩; exact ConcreteCategory.congr_hom (h (.right j.fst)) j.snd

end Types

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ChosenCoends.{v, u} (Type max w u)
  body: Types.cowedge
  isCoend := Types.cowedgeIsColimit

中文:
实例 :
  签名: ChosenCoends.{v, u} (Type max w u)
  定义体: Types.cowedge
  isCoend := Types.cowedgeIsColimit

Depends on / 依赖: Types.cowedge, cowedge
-/
instance : ChosenCoends.{v, u} (Type max w u) where
  cowedge := Types.cowedge
  isCoend := Types.cowedgeIsColimit

variable {J : Type u} [Category.{v} J] {F : Jᵒᵖ ⥤ J ⥤ Type max w u}

/--
lemma `Types.chosenCoend_def` / 引理 `Types.chosenCoend_def`

English:
lemma Types.chosenCoend_def
  statement: chosenCoend F = Quot (coendRel F)
  proof: rfl

中文:
引理 Types.chosenCoend_def
  结论: chosenCoend F = Quot (coendRel F)
  证明: rfl
-/
lemma Types.chosenCoend_def : chosenCoend F = Quot (coendRel F) := rfl

attribute [local simp] Types.chosenCoend_def

/--
lemma `chosenCoend.ι_apply` / 引理 `chosenCoend.ι_apply`

English:
lemma chosenCoend.ι_apply
  given: (j : J) (x : (F.obj (op j)).obj j)
  proof: rfl

中文:
引理 chosenCoend.ι_apply
  条件: (j : J) (x : (F.obj (op j)).obj j)
  证明: rfl
-/
lemma chosenCoend.ι_apply (j : J) (x : (F.obj (op j)).obj j) :
    dsimp% chosenCoend.ι F j x = Quot.mk _ ⟨j, x⟩ :=
  rfl

/--
lemma `chosenCoend.desc_apply` / 引理 `chosenCoend.desc_apply`

English:
lemma chosenCoend.desc_apply
  statement: {X : Type max w u} (f : forall j, (F.obj (op j)).obj j ⟶ X)
  proof: rfl

中文:
引理 chosenCoend.desc_apply
  结论: {X : Type max w u} (f : 对任意 j, (F.obj (op j)).obj j ⟶ X)
  证明: rfl

Depends on / 依赖: F.hasBiproduct_of_preserves, hasBiproduct_of_preserves
-/
lemma chosenCoend.desc_apply {X : Type max w u} (f : forall j, (F.obj (op j)).obj j ⟶ X)
    (hf : forall ⦃i j : J⦄ (g : i ⟶ j), (F.map g.op).app i ≫ f i = (F.obj (op j)).map g ≫ f j)
    (x : chosenCoend F) : dsimp% chosenCoend.desc f hf x =
      Quot.lift (fun j => f j.fst j.snd) (fun _ _ h => by
        cases h with | mk f x => exact ConcreteCategory.congr_hom (hf f) _) x :=
  rfl

/--
lemma `chosenCoend.map_apply` / 引理 `chosenCoend.map_apply`

English:
lemma chosenCoend.map_apply
  given: {G : Jᵒᵖ ⥤ J ⥤ Type max w u} (f : F ⟶ G) (x : chosenCoend F)
  proof: rfl

中文:
引理 chosenCoend.map_apply
  条件: {G : Jᵒᵖ ⥤ J ⥤ Type max w u} (f : F ⟶ G) (x : chosenCoend F)
  证明: rfl
-/
lemma chosenCoend.map_apply {G : Jᵒᵖ ⥤ J ⥤ Type max w u} (f : F ⟶ G) (x : chosenCoend F) :
    dsimp% chosenCoend.map f x =
      Quot.lift (fun ⟨j, y⟩ => Quot.mk _ ⟨j, (f.app _).app _ y⟩) (fun _ _ => by
        rintro ⟨g, y⟩
        apply Quot.sound
        rw [Types.coendRel_iff]
        refine ⟨g, (f.app _).app _ y, ?_, ?_⟩
        · simp only [← NatTrans.comp_app_apply, f.naturality]
        · simp [← NatTrans.naturality_apply]) x :=
  rfl

namespace Types

variable {J : Type u} [Category.{v} J] (F : Jᵒᵖ ⥤ J ⥤ Type max w u)

/--
Definition of `end_` / `end_` 的定义

English:
abbreviation end_
  signature: : Type max w u
  body: { x : forall j, (F.obj (op j)).obj j // forall ⦃i j : J⦄ (f : i ⟶ j),
      TypeCat.Hom.hom ((F.obj (op i)).map f) (x i) =
        TypeCat.Hom.hom ((F.map f.op).app j) (x j) }

中文:
缩写 end_
  签名: : Type max w u
  定义体: { x : forall j, (F.obj (op j)).obj j // forall ⦃i j : J⦄ (f : i ⟶ j),
      TypeCat.Hom.hom ((F.obj (op i)).map f) (x i) =
        TypeCat.Hom.hom ((F.map f.op).app j) (x j) }

Depends on / 依赖: F.map, F.obj, TypeCat, TypeCat.Hom.hom, f.op
-/
abbrev end_ : Type max w u :=
  { x : forall j, (F.obj (op j)).obj j // forall ⦃i j : J⦄ (f : i ⟶ j),
      TypeCat.Hom.hom ((F.obj (op i)).map f) (x i) =
        TypeCat.Hom.hom ((F.map f.op).app j) (x j) }

/--
Definition of `end_.π` / `end_.π` 的定义

English:
definition end_.π
  signature: (j : J)
  body: ↾fun x => x.1 j

中文:
定义 end_.π
  签名: (j : J)
  定义体: ↾fun x => x.1 j
-/
def end_.π (j : J) : end_ F ⟶ (F.obj (op j)).obj j := ↾fun x => x.1 j

variable {F}

@[reassoc]
/--
lemma `end_.condition` / 引理 `end_.condition`

English:
lemma end_.condition
  given: {i j : J} (f : i ⟶ j)
  proof: by
  ext x
  exact x.2 f

中文:
引理 end_.condition
  条件: {i j : J} (f : i ⟶ j)
  证明: by
  ext x
  exact x.2 f
-/
lemma end_.condition {i j : J} (f : i ⟶ j) :
    end_.π F i ≫ (F.obj (op i)).map f = end_.π F j ≫ (F.map f.op).app j := by
  ext x
  exact x.2 f

variable (F)

/--
Definition of `wedge` / `wedge` 的定义

English:
definition wedge
  signature: : Wedge F
  body: Wedge.mk (end_ F) (end_.π F) (by intros; apply end_.condition)

中文:
定义 wedge
  签名: : Wedge F
  定义体: Wedge.mk (end_ F) (end_.π F) (by intros; apply end_.condition)

Depends on / 依赖: Wedge.mk, condition, end_, end_.condition, intros
-/
def wedge : Wedge F := Wedge.mk (end_ F) (end_.π F) (by intros; apply end_.condition)

/--
Definition of `wedgeIsLimit` / `wedgeIsLimit` 的定义

English:
definition wedgeIsLimit
  signature: : IsLimit (wedge F) where
  body: TypeCat.ofHom fun x =>
    (⟨fun j : J => Multifork.ι s j x, fun _ _ f => by
      exact ConcreteCategory.congr_hom (Wedge.condition s f) x⟩ : end_ F)
  fac s := by rintro (_ | _) <;> cat_disch
  uniq s m h := by
    ext x
    apply Subtype.ext
    funext j
    exact ConcreteCategory.congr_hom (h (.

中文:
定义 wedgeIsLimit
  签名: : IsLimit (wedge F) where
  定义体: TypeCat.ofHom fun x =>
    (⟨fun j : J => Multifork.ι s j x, fun _ _ f => by
      exact ConcreteCategory.congr_hom (Wedge.condition s f) x⟩ : end_ F)
  fac s := by rintro (_ | _) <;> cat_disch
  uniq s m h := by
    ext x
    apply Subtype.ext
    funext j
    exact ConcreteCategory.congr_hom (h (.

Depends on / 依赖: TypeCat, TypeCat.ofHom
-/
def wedgeIsLimit : IsLimit (wedge F) where
lift s := TypeCat.ofHom fun x =>
    (⟨fun j : J => Multifork.ι s j x, fun _ _ f => by
      exact ConcreteCategory.congr_hom (Wedge.condition s f) x⟩ : end_ F)
  fac s := by rintro (_ | _) <;> cat_disch
  uniq s m h := by
    ext x
    apply Subtype.ext
    funext j
    exact ConcreteCategory.congr_hom (h (.left j)) x

end Types

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ChosenEnds.{v, u} (Type max w u)
  body: Types.wedge
  isEnd := Types.wedgeIsLimit

中文:
实例 :
  签名: ChosenEnds.{v, u} (Type max w u)
  定义体: Types.wedge
  isEnd := Types.wedgeIsLimit

Depends on / 依赖: Types.wedge
-/
instance : ChosenEnds.{v, u} (Type max w u) where
  wedge := Types.wedge
  isEnd := Types.wedgeIsLimit

variable {J : Type u} [Category.{v} J] {F : Jᵒᵖ ⥤ J ⥤ Type max w u}

/--
lemma `Types.chosenEnd_def` / 引理 `Types.chosenEnd_def`

English:
lemma Types.chosenEnd_def
  statement: chosenEnd F = Types.end_ F
  proof: rfl

中文:
引理 Types.chosenEnd_def
  结论: chosenEnd F = Types.end_ F
  证明: rfl
-/
lemma Types.chosenEnd_def : chosenEnd F = Types.end_ F := rfl

attribute [local simp] Types.chosenEnd_def

/--
lemma `chosenEnd.π_apply` / 引理 `chosenEnd.π_apply`

English:
lemma chosenEnd.π_apply
  given: (j : J) (x : Types.end_ F)
  proof: rfl

中文:
引理 chosenEnd.π_apply
  条件: (j : J) (x : Types.end_ F)
  证明: rfl
-/
lemma chosenEnd.π_apply (j : J) (x : Types.end_ F) :
    dsimp% chosenEnd.π (C := Type max w u) F j x = x.1 j :=
  rfl

/--
lemma `chosenEnd.lift_apply` / 引理 `chosenEnd.lift_apply`

English:
lemma chosenEnd.lift_apply
  statement: {X : Type max w u} (f : forall j, X ⟶ (F.obj (op j)).obj j)
  proof: rfl

中文:
引理 chosenEnd.lift_apply
  结论: {X : Type max w u} (f : 对任意 j, X ⟶ (F.obj (op j)).obj j)
  证明: rfl
-/
lemma chosenEnd.lift_apply {X : Type max w u} (f : forall j, X ⟶ (F.obj (op j)).obj j)
    (hf : forall ⦃i j : J⦄ (g : i ⟶ j), f i ≫ (F.obj (op i)).map g = f j ≫ (F.map g.op).app j)
    (x : X) : dsimp% chosenEnd.lift (C := Type max w u) (F := F) f hf x =
      (⟨fun j => f j x, fun _ _ g => ConcreteCategory.congr_hom (hf g) x⟩ : Types.end_ F) :=
  rfl

/--
lemma `chosenEnd.map_apply` / 引理 `chosenEnd.map_apply`

English:
lemma chosenEnd.map_apply
  statement: {G : Jᵒᵖ ⥤ J ⥤ Type max w u} (f : F ⟶ G)
  proof: rfl

中文:
引理 chosenEnd.map_apply
  结论: {G : Jᵒᵖ ⥤ J ⥤ Type max w u} (f : F ⟶ G)
  证明: rfl
-/
lemma chosenEnd.map_apply {G : Jᵒᵖ ⥤ J ⥤ Type max w u} (f : F ⟶ G)
    (x : Types.end_ F) :
    dsimp% chosenEnd.map (C := Type max w u) f x =
      ⟨fun j => (f.app (op j)).app j (x.1 j), by
        intro i j g
        rw [← (f.app (op i)).naturality_apply]
        simp [x.2 g, ← comp_apply, -types_comp_apply]⟩ :=
  rfl

end CategoryTheory.Limits
