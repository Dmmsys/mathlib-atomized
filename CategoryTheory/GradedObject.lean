/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Joël Riou
-/
module

public import Mathlib.CategoryTheory.Shift.Basic
public import Mathlib.Data.Set.Subsingleton
public import Mathlib.Algebra.Group.Int.Defs

/-!
# The category of graded objects

For any type `β`, a `β`-graded object over some category `C` is just
a function `β → C` into the objects of `C`.
We put the "pointwise" category structure on these, as the non-dependent specialization of
`CategoryTheory.Pi`.

We describe the `comap` functors obtained by precomposing with functions `β → γ`.

As a consequence a fixed element (e.g. `1`) in an additive group `β` provides a shift
functor on `β`-graded objects

When `C` has coproducts we construct the `total` functor `GradedObject β C ⥤ C`,
show that it is faithful, and deduce that when `C` is concrete so is `GradedObject β C`.

A covariant functoriality of `GradedObject β C` with respect to the index set `β` is also
introduced: if `p : I → J` is a map such that `C` has coproducts indexed by `p ⁻¹' {j}`, we
have a functor `map : GradedObject I C ⥤ GradedObject J C`.

-/

@[expose] public section

namespace CategoryTheory

open Category Limits

universe w v u

/-- A type synonym for `β → C`, used for `β`-graded objects in a category `C`. -/
@[implicit_reducible]
/--
Definition of `GradedObject` / `GradedObject` 的定义

English:
definition GradedObject
  signature: (β : Type w) (C : Type u)
  body: β -> C

中文:
定义 GradedObject
  签名: (β : 类型 w) (C : 类型u)
  定义体: β -> C
-/
def GradedObject (β : Type w) (C : Type u) : Type max w u :=
  β -> C

-- Satisfying the inhabited linter...
/--
Instance `inhabitedGradedObject` / 实例 `inhabitedGradedObject`

English:
instance inhabitedGradedObject
  signature: (β : Type w) (C : Type u) [Inhabited C]
  body: ⟨fun _ => Inhabited.default⟩

中文:
实例 inhabitedGradedObject
  签名: (β : 类型 w) (C : 类型u) [可居 C]
  定义体: ⟨fun _ => Inhabited.default⟩

Depends on / 依赖: Inhabited, Inhabited.default
-/
instance inhabitedGradedObject (β : Type w) (C : Type u) [Inhabited C] :
    Inhabited (GradedObject β C) :=
  ⟨fun _ => Inhabited.default⟩

-- `s` is here to distinguish type synonyms asking for different shifts
/-- A type synonym for `β → C`, used for `β`-graded objects in a category `C`
with a shift functor given by translation by `s`.
-/
@[nolint unusedArguments]
/--
Definition of `GradedObjectWithShift` / `GradedObjectWithShift` 的定义

English:
abbreviation GradedObjectWithShift
  signature: {β : Type w} [AddCommGroup β] (_ : β) (C : Type u)
  body: GradedObject β C

中文:
缩写 GradedObjectWithShift
  签名: {β : 类型 w} [加法交换群 β] (_ : β) (C : 类型u)
  定义体: GradedObject β C

Depends on / 依赖: GradedObject
-/
abbrev GradedObjectWithShift {β : Type w} [AddCommGroup β] (_ : β) (C : Type u) : Type max w u :=
  GradedObject β C

namespace GradedObject

variable {C : Type u} [Category.{v} C]

@[simps!]
/--
Instance `categoryOfGradedObjects` / 实例 `categoryOfGradedObjects`

English:
instance categoryOfGradedObjects
  signature: (β : Type w)
  body: CategoryTheory.pi fun _ => C

@[ext]

中文:
实例 categoryOfGradedObjects
  签名: (β : 类型 w)
  定义体: CategoryTheory.pi fun _ => C

@[ext]

Depends on / 依赖: CategoryTheory, CategoryTheory.pi
-/
instance categoryOfGradedObjects (β : Type w) : Category.{max w v} (GradedObject β C) :=
  CategoryTheory.pi fun _ => C

@[ext]
/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  given: {β : Type*} {X Y : GradedObject β C} (f g : X ⟶ Y) (h : forall x, f x = g x)
  statement: f = g
  proof: by
  funext
  apply h

中文:
引理 hom_ext
  条件: {β : 类型} {X Y : GradedObject β C} (f g : X ⟶ Y) (h : 对任意 x, f x = g x)
  结论: f = g
  证明: by
  funext
  apply h
-/
lemma hom_ext {β : Type*} {X Y : GradedObject β C} (f g : X ⟶ Y) (h : forall x, f x = g x) : f = g := by
  funext
  apply h

/-- The projection of a graded object to its `i`-th component. -/
@[simps]
/--
Definition of `eval` / `eval` 的定义

English:
definition eval
  signature: {β : Type w} (b : β)
  body: X b
  map f := f b

中文:
定义 eval
  签名: {β : 类型 w} (b : β)
  定义体: X b
  map f := f b
-/
def eval {β : Type w} (b : β) : GradedObject β C ⥤ C where
  obj X := X b
  map f := f b

section

variable {β : Type*} (X Y : GradedObject β C)

set_option backward.isDefEq.respectTransparency.types false in
/-- Constructor for isomorphisms in `GradedObject` -/
@[simps]
/--
Definition of `isoMk` / `isoMk` 的定义

English:
definition isoMk
  signature: (e : forall i, X i ≅ Y i)
  body: (e i).hom
  inv i := (e i).inv

中文:
定义 isoMk
  签名: (e : 对任意 i, X i ≅ Y i)
  定义体: (e i).hom
  inv i := (e i).inv
-/
def isoMk (e : forall i, X i ≅ Y i) : X ≅ Y where
  hom i := (e i).hom
  inv i := (e i).inv

variable {X Y}

-- this lemma is not an instance as it may create a loop with `isIso_apply_of_isIso`
set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `isIso_of_isIso_apply` / 引理 `isIso_of_isIso_apply`

English:
lemma isIso_of_isIso_apply
  given: (f : X ⟶ Y) [hf : forall i, IsIso (f i)]
  proof: by
  change IsIso (isoMk X Y (fun i => asIso (f i))).hom
  infer_instance

中文:
引理 isIso_of_isIso_apply
  条件: (f : X ⟶ Y) [hf : 对任意 i, 是同构 (f i)]
  证明: by
  change IsIso (isoMk X Y (fun i => asIso (f i))).hom
  infer_instance

Depends on / 依赖: infer_instance
-/
lemma isIso_of_isIso_apply (f : X ⟶ Y) [hf : forall i, IsIso (f i)] :
    IsIso f := by
  change IsIso (isoMk X Y (fun i => asIso (f i))).hom
  infer_instance

/--
Instance `isIso_apply_of_isIso` / 实例 `isIso_apply_of_isIso`

English:
instance isIso_apply_of_isIso
  signature: (f : X ⟶ Y) [IsIso f] (i : β)
  body: by
  change IsIso ((eval i).map f)
  infer_instance

中文:
实例 isIso_apply_of_isIso
  签名: (f : X ⟶ Y) [是同构 f] (i : β)
  定义体: by
  change IsIso ((eval i).map f)
  infer_instance

Depends on / 依赖: infer_instance
-/
instance isIso_apply_of_isIso (f : X ⟶ Y) [IsIso f] (i : β) : IsIso (f i) := by
  change IsIso ((eval i).map f)
  infer_instance

end

end GradedObject

namespace Iso

variable {C D E J : Type*} [Category* C] [Category* D] [Category* E]
  {X Y : GradedObject J C}

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/--
lemma `hom_inv_id_eval` / 引理 `hom_inv_id_eval`

English:
lemma hom_inv_id_eval
  given: (e : X ≅ Y) (j : J)
  proof: by
  rw [← GradedObject.categoryOfGradedObjects_comp]; rw [e.hom_inv_id]; rw [GradedObject.categoryOfGradedObjects_id]

中文:
引理 hom_inv_id_eval
  条件: (e : X ≅ Y) (j : J)
  证明: by
  rw [← GradedObject.categoryOfGradedObjects_comp]; rw [e.hom_inv_id]; rw [GradedObject.categoryOfGradedObjects_id]

Depends on / 依赖: GradedObject, GradedObject.categoryOfGradedObjects_comp, GradedObject.categoryOfGradedObjects_id, categoryOfGradedObjects_comp, categoryOfGradedObjects_id, e.hom_inv_id, hom_ext, hom_inv_id, hs.hom_ext
-/
lemma hom_inv_id_eval (e : X ≅ Y) (j : J) :
    e.hom j ≫ e.inv j = 𝟙 _ := by
  rw [← GradedObject.categoryOfGradedObjects_comp]; rw [e.hom_inv_id]; rw [GradedObject.categoryOfGradedObjects_id]

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/--
lemma `inv_hom_id_eval` / 引理 `inv_hom_id_eval`

English:
lemma inv_hom_id_eval
  given: (e : X ≅ Y) (j : J)
  proof: by
  rw [← GradedObject.categoryOfGradedObjects_comp]; rw [e.inv_hom_id]; rw [GradedObject.categoryOfGradedObjects_id]

中文:
引理 inv_hom_id_eval
  条件: (e : X ≅ Y) (j : J)
  证明: by
  rw [← GradedObject.categoryOfGradedObjects_comp]; rw [e.inv_hom_id]; rw [GradedObject.categoryOfGradedObjects_id]

Depends on / 依赖: GradedObject, GradedObject.categoryOfGradedObjects_comp, GradedObject.categoryOfGradedObjects_id, WidePullbackCone, WidePullbackCone.mk, categoryOfGradedObjects_comp, categoryOfGradedObjects_id, e.inv_hom_id, hs.lift, inv_hom_id
-/
lemma inv_hom_id_eval (e : X ≅ Y) (j : J) :
    e.inv j ≫ e.hom j = 𝟙 _ := by
  rw [← GradedObject.categoryOfGradedObjects_comp]; rw [e.inv_hom_id]; rw [GradedObject.categoryOfGradedObjects_id]

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/--
lemma `map_hom_inv_id_eval` / 引理 `map_hom_inv_id_eval`

English:
lemma map_hom_inv_id_eval
  given: (e : X ≅ Y) (F : C ⥤ D) (j : J)
  proof: by
  rw [← F.map_comp]; rw [← GradedObject.categoryOfGradedObjects_comp]; rw [e.hom_inv_id]; rw [GradedObject.categoryOfGradedObjects_id]; rw [Functor.map_id]

中文:
引理 map_hom_inv_id_eval
  条件: (e : X ≅ Y) (F : C ⥤ D) (j : J)
  证明: by
  rw [← F.map_comp]; rw [← GradedObject.categoryOfGradedObjects_comp]; rw [e.hom_inv_id]; rw [GradedObject.categoryOfGradedObjects_id]; rw [Functor.map_id]

Depends on / 依赖: F.map_comp, Functor, Functor.map_id, GradedObject, GradedObject.categoryOfGradedObjects_comp, GradedObject.categoryOfGradedObjects_id, categoryOfGradedObjects_comp, categoryOfGradedObjects_id, e.hom_inv_id, hom_inv_id, map_comp, map_id
-/
lemma map_hom_inv_id_eval (e : X ≅ Y) (F : C ⥤ D) (j : J) :
    F.map (e.hom j) ≫ F.map (e.inv j) = 𝟙 _ := by
  rw [← F.map_comp]; rw [← GradedObject.categoryOfGradedObjects_comp]; rw [e.hom_inv_id]; rw [GradedObject.categoryOfGradedObjects_id]; rw [Functor.map_id]

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/--
lemma `map_inv_hom_id_eval` / 引理 `map_inv_hom_id_eval`

English:
lemma map_inv_hom_id_eval
  given: (e : X ≅ Y) (F : C ⥤ D) (j : J)
  proof: by
  rw [← F.map_comp]; rw [← GradedObject.categoryOfGradedObjects_comp]; rw [e.inv_hom_id]; rw [GradedObject.categoryOfGradedObjects_id]; rw [Functor.map_id]

@[reassoc (attr := simp)]

中文:
引理 map_inv_hom_id_eval
  条件: (e : X ≅ Y) (F : C ⥤ D) (j : J)
  证明: by
  rw [← F.map_comp]; rw [← GradedObject.categoryOfGradedObjects_comp]; rw [e.inv_hom_id]; rw [GradedObject.categoryOfGradedObjects_id]; rw [Functor.map_id]

@[reassoc (attr := simp)]

Depends on / 依赖: F.map_comp, Functor, Functor.map_id, GradedObject, GradedObject.categoryOfGradedObjects_comp, GradedObject.categoryOfGradedObjects_id, categoryOfGradedObjects_comp, categoryOfGradedObjects_id, e.inv_hom_id, inv_hom_id, map_comp, map_id
-/
lemma map_inv_hom_id_eval (e : X ≅ Y) (F : C ⥤ D) (j : J) :
    F.map (e.inv j) ≫ F.map (e.hom j) = 𝟙 _ := by
  rw [← F.map_comp]; rw [← GradedObject.categoryOfGradedObjects_comp]; rw [e.inv_hom_id]; rw [GradedObject.categoryOfGradedObjects_id]; rw [Functor.map_id]

@[reassoc (attr := simp)]
/--
lemma `map_hom_inv_id_eval_app` / 引理 `map_hom_inv_id_eval_app`

English:
lemma map_hom_inv_id_eval_app
  given: (e : X ≅ Y) (F : C ⥤ D ⥤ E) (j : J) (Y : D)
  proof: by
  rw [← NatTrans.comp_app]; rw [← F.map_comp]; rw [hom_inv_id_eval]; rw [Functor.map_id]; rw [NatTrans.id_app]

@[reassoc (attr := simp)]

中文:
引理 map_hom_inv_id_eval_app
  条件: (e : X ≅ Y) (F : C ⥤ D ⥤ E) (j : J) (Y : D)
  证明: by
  rw [← NatTrans.comp_app]; rw [← F.map_comp]; rw [hom_inv_id_eval]; rw [Functor.map_id]; rw [NatTrans.id_app]

@[reassoc (attr := simp)]

Depends on / 依赖: F.map_comp, Functor, Functor.map_id, NatTrans, NatTrans.comp_app, NatTrans.id_app, comp_app, hom_inv_id_eval, id_app, map_comp, map_id
-/
lemma map_hom_inv_id_eval_app (e : X ≅ Y) (F : C ⥤ D ⥤ E) (j : J) (Y : D) :
    (F.map (e.hom j)).app Y ≫ (F.map (e.inv j)).app Y = 𝟙 _ := by
  rw [← NatTrans.comp_app]; rw [← F.map_comp]; rw [hom_inv_id_eval]; rw [Functor.map_id]; rw [NatTrans.id_app]

@[reassoc (attr := simp)]
/--
lemma `map_inv_hom_id_eval_app` / 引理 `map_inv_hom_id_eval_app`

English:
lemma map_inv_hom_id_eval_app
  given: (e : X ≅ Y) (F : C ⥤ D ⥤ E) (j : J) (Y : D)
  proof: by
  rw [← NatTrans.comp_app]; rw [← F.map_comp]; rw [inv_hom_id_eval]; rw [Functor.map_id]; rw [NatTrans.id_app]

中文:
引理 map_inv_hom_id_eval_app
  条件: (e : X ≅ Y) (F : C ⥤ D ⥤ E) (j : J) (Y : D)
  证明: by
  rw [← NatTrans.comp_app]; rw [← F.map_comp]; rw [inv_hom_id_eval]; rw [Functor.map_id]; rw [NatTrans.id_app]

Depends on / 依赖: F.map_comp, Functor, Functor.map_id, NatTrans, NatTrans.comp_app, NatTrans.id_app, comp_app, id_app, inv_hom_id_eval, map_comp, map_id
-/
lemma map_inv_hom_id_eval_app (e : X ≅ Y) (F : C ⥤ D ⥤ E) (j : J) (Y : D) :
    (F.map (e.inv j)).app Y ≫ (F.map (e.hom j)).app Y = 𝟙 _ := by
  rw [← NatTrans.comp_app]; rw [← F.map_comp]; rw [inv_hom_id_eval]; rw [Functor.map_id]; rw [NatTrans.id_app]

end Iso

namespace GradedObject

variable {C : Type u} [Category.{v} C]

section

variable (C)

/--
Definition of `comap` / `comap` 的定义

English:
abbreviation comap
  signature: {I J : Type*} (h : J -> I)
  body: Pi.comap (fun _ => C) h

@[simp]

中文:
缩写 comap
  签名: {I J : 类型} (h : J -> I)
  定义体: Pi.comap (fun _ => C) h

@[simp]

Depends on / 依赖: Pi.comap
-/
abbrev comap {I J : Type*} (h : J -> I) : GradedObject I C ⥤ GradedObject J C :=
  Pi.comap (fun _ => C) h

@[simp]
/--
theorem `eqToHom_proj` / 定理 `eqToHom_proj`

English:
theorem eqToHom_proj
  given: {I : Type*} {x x' : GradedObject I C} (h : x = x') (i : I)
  proof: by
  subst h
  rfl

中文:
定理 eqToHom_proj
  条件: {I : 类型} {x x' : GradedObject I C} (h : x = x') (i : I)
  证明: by
  subst h
  rfl
-/
theorem eqToHom_proj {I : Type*} {x x' : GradedObject I C} (h : x = x') (i : I) :
    (eqToHom h : x ⟶ x') i = eqToHom (funext_iff.mp h i) := by
  subst h
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- The natural isomorphism comparing between
pulling back along two propositionally equal functions.
-/
@[simps]
/--
Definition of `comapEq` / `comapEq` 的定义

English:
definition comapEq
  signature: {β γ : Type w} {f g : β -> γ} (h : f = g)
  body: { app := fun X b => eqToHom (by dsimp; simp only [h]) }
  inv := { app := fun X b => eqToHom (by dsimp; simp only [h]) }

中文:
定义 comapEq
  签名: {β γ : 类型 w} {f g : β -> γ} (h : f = g)
  定义体: { app := fun X b => eqToHom (by dsimp; simp only [h]) }
  inv := { app := fun X b => eqToHom (by dsimp; simp only [h]) }

Depends on / 依赖: eqToHom
-/
def comapEq {β γ : Type w} {f g : β -> γ} (h : f = g) : comap C f ≅ comap C g where
  hom := { app := fun X b => eqToHom (by dsimp; simp only [h]) }
  inv := { app := fun X b => eqToHom (by dsimp; simp only [h]) }

/--
theorem `comapEq_symm` / 定理 `comapEq_symm`

English:
theorem comapEq_symm
  given: {β γ : Type w} {f g : β -> γ} (h : f = g)
  proof: by cat_disch

中文:
定理 comapEq_symm
  条件: {β γ : 类型 w} {f g : β -> γ} (h : f = g)
  证明: by cat_disch

Depends on / 依赖: cat_disch
-/
theorem comapEq_symm {β γ : Type w} {f g : β -> γ} (h : f = g) :
    comapEq C h.symm = (comapEq C h).symm := by cat_disch

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `comapEq_trans` / 定理 `comapEq_trans`

English:
theorem comapEq_trans
  given: {β γ : Type w} {f g h : β -> γ} (k : f = g) (l : g = h)
  proof: by cat_disch

中文:
定理 comapEq_trans
  条件: {β γ : 类型 w} {f g h : β -> γ} (k : f = g) (l : g = h)
  证明: by cat_disch

Depends on / 依赖: cat_disch
-/
theorem comapEq_trans {β γ : Type w} {f g h : β -> γ} (k : f = g) (l : g = h) :
    comapEq C (k.trans l) = comapEq C k ≪≫ comapEq C l := by cat_disch

/--
theorem `eqToHom_apply` / 定理 `eqToHom_apply`

English:
theorem eqToHom_apply
  given: {β : Type w} {X Y : β -> C} (h : X = Y) (b : β)
  proof: by
  subst h
  rfl

中文:
定理 eqToHom_apply
  条件: {β : 类型 w} {X Y : β -> C} (h : X = Y) (b : β)
  证明: by
  subst h
  rfl
-/
theorem eqToHom_apply {β : Type w} {X Y : β -> C} (h : X = Y) (b : β) :
    (eqToHom h : X ⟶ Y) b = eqToHom (by rw [h]) := by
  subst h
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The equivalence between β-graded objects and γ-graded objects,
given an equivalence between β and γ.
-/
@[simps]
/--
Definition of `comapEquiv` / `comapEquiv` 的定义

English:
definition comapEquiv
  signature: {β γ : Type w} (e : β ≃ γ)
  body: comap C (e.symm : γ -> β)
  inverse := comap C (e : β -> γ)
  counitIso :=
    (Pi.comapComp (fun _ => C) _ _).trans (comapEq C (by ext; simp))
  unitIso :=
    (comapEq C (by ext; simp)).trans (Pi.comapComp _ _ _).symm

中文:
定义 comapEquiv
  签名: {β γ : 类型 w} (e : β ≃ γ)
  定义体: comap C (e.symm : γ -> β)
  inverse := comap C (e : β -> γ)
  counitIso :=
    (Pi.comapComp (fun _ => C) _ _).trans (comapEq C (by ext; simp))
  unitIso :=
    (comapEq C (by ext; simp)).trans (Pi.comapComp _ _ _).symm

Depends on / 依赖: e.symm
-/
def comapEquiv {β γ : Type w} (e : β ≃ γ) : GradedObject β C ≌ GradedObject γ C where
  functor := comap C (e.symm : γ -> β)
  inverse := comap C (e : β -> γ)
  counitIso :=
    (Pi.comapComp (fun _ => C) _ _).trans (comapEq C (by ext; simp))
  unitIso :=
    (comapEq C (by ext; simp)).trans (Pi.comapComp _ _ _).symm

end

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Instance `hasShift` / 实例 `hasShift`

English:
instance hasShift
  signature: {β : Type*} [AddCommGroup β] (s : β)
  body: hasShiftMk _ _
    { F := fun n => comap C fun b : β => b + n • s
      zero := comapEq C (by cat_disch) ≪≫ Pi.comapId β fun _ => C
      add := fun m n => comapEq C (by ext; dsimp; rw [add_comm m n, add_zsmul, add_assoc]) ≪≫
          (Pi.comapComp _ _ _).symm }

中文:
实例 hasShift
  签名: {β : 类型} [加法交换群 β] (s : β)
  定义体: hasShiftMk _ _
    { F := fun n => comap C fun b : β => b + n • s
      zero := comapEq C (by cat_disch) ≪≫ Pi.comapId β fun _ => C
      add := fun m n => comapEq C (by ext; dsimp; rw [add_comm m n, add_zsmul, add_assoc]) ≪≫
          (Pi.comapComp _ _ _).symm }

Depends on / 依赖: Pi.comapComp, Pi.comapId, add_assoc, add_comm, add_zsmul, cat_disch, comapComp, comapEq, comapId, hasShiftMk
-/
instance hasShift {β : Type*} [AddCommGroup β] (s : β) : HasShift (GradedObjectWithShift s C) Int :=
  hasShiftMk _ _
    { F := fun n => comap C fun b : β => b + n • s
      zero := comapEq C (by cat_disch) ≪≫ Pi.comapId β fun _ => C
      add := fun m n => comapEq C (by ext; dsimp; rw [add_comm m n, add_zsmul, add_assoc]) ≪≫
          (Pi.comapComp _ _ _).symm }

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `shiftFunctor_obj_apply` / 定理 `shiftFunctor_obj_apply`

English:
theorem shiftFunctor_obj_apply
  given: {β : Type*} [AddCommGroup β] (s : β) (X : β -> C) (t : β) (n : Int)
  proof: rfl

中文:
定理 shiftFunctor_obj_apply
  条件: {β : 类型} [加法交换群 β] (s : β) (X : β -> C) (t : β) (n : 整数)
  证明: rfl
-/
theorem shiftFunctor_obj_apply {β : Type*} [AddCommGroup β] (s : β) (X : β -> C) (t : β) (n : Int) :
    (shiftFunctor (GradedObjectWithShift s C) n).obj X t = X (t + n • s) :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `shiftFunctor_map_apply` / 定理 `shiftFunctor_map_apply`

English:
theorem shiftFunctor_map_apply
  statement: {β : Type*} [AddCommGroup β] (s : β)
  proof: rfl

中文:
定理 shiftFunctor_map_apply
  结论: {β : 类型} [加法交换群 β] (s : β)
  证明: rfl
-/
theorem shiftFunctor_map_apply {β : Type*} [AddCommGroup β] (s : β)
    {X Y : GradedObjectWithShift s C} (f : X ⟶ Y) (t : β) (n : Int) :
    (shiftFunctor (GradedObjectWithShift s C) n).map f t = f (t + n • s) :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasZeroMorphisms
  signature: C] (β
  body: ⟨fun _ => 0⟩

@[simp]

中文:
实例 [有ZeroMorphisms
  签名: C] (β
  定义体: ⟨fun _ => 0⟩

@[simp]
-/
instance [HasZeroMorphisms C] (β : Type w) (X Y : GradedObject β C) : Zero (X ⟶ Y) :=
  ⟨fun _ => 0⟩

@[simp]
/--
theorem `zero_apply` / 定理 `zero_apply`

English:
theorem zero_apply
  given: [HasZeroMorphisms C] (β : Type w) (X Y : GradedObject β C) (b : β)
  proof: rfl

中文:
定理 zero_apply
  条件: [有ZeroMorphisms C] (β : 类型 w) (X Y : GradedObject β C) (b : β)
  证明: rfl
-/
theorem zero_apply [HasZeroMorphisms C] (β : Type w) (X Y : GradedObject β C) (b : β) :
    (0 : X ⟶ Y) b = 0 :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `hasZeroMorphisms` / 实例 `hasZeroMorphisms`

English:
instance hasZeroMorphisms
  signature: [HasZeroMorphisms C] (β : Type w)

中文:
实例 hasZeroMorphisms
  签名: [有ZeroMorphisms C] (β : 类型 w)
-/
instance hasZeroMorphisms [HasZeroMorphisms C] (β : Type w) :
    HasZeroMorphisms.{max w v} (GradedObject β C) where

section

open ZeroObject

/--
Instance `hasZeroObject` / 实例 `hasZeroObject`

English:
instance hasZeroObject
  signature: [HasZeroObject C] [HasZeroMorphisms C] (β : Type w)
  body: by
  refine ⟨⟨fun _ => 0, fun X => ⟨⟨⟨fun b => 0⟩, fun f => ?_⟩⟩, fun X =>
    ⟨⟨⟨fun b => 0⟩, fun f => ?_⟩⟩⟩⟩ <;> cat_disch

中文:
实例 hasZeroObject
  签名: [有ZeroObject C] [有ZeroMorphisms C] (β : 类型 w)
  定义体: by
  refine ⟨⟨fun _ => 0, fun X => ⟨⟨⟨fun b => 0⟩, fun f => ?_⟩⟩, fun X =>
    ⟨⟨⟨fun b => 0⟩, fun f => ?_⟩⟩⟩⟩ <;> cat_disch

Depends on / 依赖: cat_disch
-/
instance hasZeroObject [HasZeroObject C] [HasZeroMorphisms C] (β : Type w) :
    HasZeroObject.{max w v} (GradedObject β C) := by
  refine ⟨⟨fun _ => 0, fun X => ⟨⟨⟨fun b => 0⟩, fun f => ?_⟩⟩, fun X =>
    ⟨⟨⟨fun b => 0⟩, fun f => ?_⟩⟩⟩⟩ <;> cat_disch

end

end GradedObject

namespace GradedObject

-- The universes get a little hairy here, so we restrict the universe level for the grading to 0.
-- Since we're typically interested in grading by ℤ or a finite group, this should be okay.
-- If you're grading by things in higher universes, have fun!
variable (β : Type)
variable (C : Type u) [Category.{v} C]
variable [HasCoproducts.{0} C]

section

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `total` / `total` 的定义

English:
definition total
  signature: : GradedObject β C ⥤ C where
  body: ∐ fun i : β => X i
  map f := Limits.Sigma.map fun i => f i

中文:
定义 total
  签名: : GradedObject β C ⥤ C where
  定义体: ∐ fun i : β => X i
  map f := Limits.Sigma.map fun i => f i
-/
noncomputable def total : GradedObject β C ⥤ C where
  obj X := ∐ fun i : β => X i
  map f := Limits.Sigma.map fun i => f i

end

variable [HasZeroMorphisms C]

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (total β C).Faithful
  body: by
    ext i
    replace w := Sigma.ι (fun i : β => X i) i ≫= w
    erw [colimit.ι_map, colimit.ι_map] at w
    replace w : f i ≫ colimit.ι (Discrete.functor Y) ⟨i⟩ =
      g i ≫ colimit.ι (Discrete.functor Y) ⟨i⟩ := by simpa
    exact Mono.right_cancellation _ _ w

中文:
实例 :
  签名: (total β C).忠实
  定义体: by
    ext i
    replace w := Sigma.ι (fun i : β => X i) i ≫= w
    erw [colimit.ι_map, colimit.ι_map] at w
    replace w : f i ≫ colimit.ι (Discrete.functor Y) ⟨i⟩ =
      g i ≫ colimit.ι (Discrete.functor Y) ⟨i⟩ := by simpa
    exact Mono.right_cancellation _ _ w

Depends on / 依赖: Discrete, Discrete.functor, Mono.right_cancellation, colimit, functor, replace, right_cancellation
-/
instance : (total β C).Faithful where
  map_injective {X Y} f g w := by
    ext i
    replace w := Sigma.ι (fun i : β => X i) i ≫= w
    erw [colimit.ι_map, colimit.ι_map] at w
    replace w : f i ≫ colimit.ι (Discrete.functor Y) ⟨i⟩ =
      g i ≫ colimit.ι (Discrete.functor Y) ⟨i⟩ := by simpa
    exact Mono.right_cancellation _ _ w

end GradedObject

namespace GradedObject

variable {I J K : Type*} {C : Type*} [Category* C]
  (X Y Z : GradedObject I C) (φ : X ⟶ Y) (e : X ≅ Y) (ψ : Y ⟶ Z) (p : I -> J)

/--
Definition of `mapObjFun` / `mapObjFun` 的定义

English:
abbreviation mapObjFun
  signature: (j : J) (i : p ⁻¹' {j})
  body: X i

中文:
缩写 mapObjFun
  签名: (j : J) (i : p ⁻¹' {j})
  定义体: X i
-/
abbrev mapObjFun (j : J) (i : p ⁻¹' {j}) : C := X i

variable (j : J)

/--
Definition of `HasMap` / `HasMap` 的定义

English:
abbreviation HasMap
  signature: : Prop
  body: forall (j : J), HasCoproduct (X.mapObjFun p j)

中文:
缩写 HasMap
  签名: : 命题
  定义体: forall (j : J), HasCoproduct (X.mapObjFun p j)

Depends on / 依赖: HasCoproduct, X.mapObjFun, mapObjFun
-/
abbrev HasMap : Prop := forall (j : J), HasCoproduct (X.mapObjFun p j)

variable {X Y} in
/--
lemma `hasMap_of_iso` / 引理 `hasMap_of_iso`

English:
lemma hasMap_of_iso
  given: (e : X ≅ Y) (p : I -> J) [HasMap X p]
  statement: HasMap Y p
  proof: fun j => by
  have α : Discrete.functor (X.mapObjFun p j) ≅ Discrete.functor (Y.mapObjFun p j) :=
    Discrete.natIso (fun ⟨i, _⟩ => (GradedObject.eval i).mapIso e)
  exact hasColimit_of_iso α.symm

中文:
引理 hasMap_of_iso
  条件: (e : X ≅ Y) (p : I -> J) [HasMap X p]
  结论: HasMap Y p
  证明: fun j => by
  have α : Discrete.functor (X.mapObjFun p j) ≅ Discrete.functor (Y.mapObjFun p j) :=
    Discrete.natIso (fun ⟨i, _⟩ => (GradedObject.eval i).mapIso e)
  exact hasColimit_of_iso α.symm

Depends on / 依赖: Discrete, Discrete.functor, Discrete.natIso, GradedObject, GradedObject.eval, X.mapObjFun, Y.mapObjFun, functor, hasColimit_of_iso, mapIso, mapObjFun, natIso
-/
lemma hasMap_of_iso (e : X ≅ Y) (p : I -> J) [HasMap X p] : HasMap Y p := fun j => by
  have α : Discrete.functor (X.mapObjFun p j) ≅ Discrete.functor (Y.mapObjFun p j) :=
    Discrete.natIso (fun ⟨i, _⟩ => (GradedObject.eval i).mapIso e)
  exact hasColimit_of_iso α.symm

section
variable [X.HasMap p] [Y.HasMap p]

/--
Definition of `mapObj` / `mapObj` 的定义

English:
definition mapObj
  signature: : GradedObject J C
  body: fun j => ∐ (X.mapObjFun p j)

中文:
定义 mapObj
  签名: : GradedObject J C
  定义体: fun j => ∐ (X.mapObjFun p j)

Depends on / 依赖: X.mapObjFun, mapObjFun
-/
noncomputable def mapObj : GradedObject J C := fun j => ∐ (X.mapObjFun p j)

/--
Definition of `ιMapObj` / `ιMapObj` 的定义

English:
definition ιMapObj
  signature: (i : I) (j : J) (hij : p i = j)
  body: Sigma.ι (X.mapObjFun p j) ⟨i, hij⟩

中文:
定义 ιMapObj
  签名: (i : I) (j : J) (hij : p i = j)
  定义体: Sigma.ι (X.mapObjFun p j) ⟨i, hij⟩

Depends on / 依赖: X.mapObjFun, mapObjFun
-/
noncomputable def ιMapObj (i : I) (j : J) (hij : p i = j) : X i ⟶ X.mapObj p j :=
  Sigma.ι (X.mapObjFun p j) ⟨i, hij⟩

/--
Definition of `CofanMapObjFun` / `CofanMapObjFun` 的定义

English:
abbreviation CofanMapObjFun
  signature: (j : J)
  body: Cofan (X.mapObjFun p j)

中文:
缩写 CofanMapObjFun
  签名: (j : J)
  定义体: Cofan (X.mapObjFun p j)

Depends on / 依赖: X.mapObjFun, mapObjFun
-/
abbrev CofanMapObjFun (j : J) : Type _ := Cofan (X.mapObjFun p j)

-- in order to use the cofan API, some definitions below
-- have a `simp` attribute rather than `simps`
/-- Constructor for `CofanMapObjFun X p j`. -/
@[simp]
/--
Definition of `CofanMapObjFun.mk` / `CofanMapObjFun.mk` 的定义

English:
definition CofanMapObjFun.mk
  signature: (j : J) (pt : C) (ι' : forall (i : I) (_ : p i = j), X i ⟶ pt)
  body: Cofan.mk pt (fun ⟨i, hi⟩ => ι' i hi)

中文:
定义 CofanMapObjFun.mk
  签名: (j : J) (pt : C) (ι' : 对任意 (i : I) (_ : p i = j), X i ⟶ pt)
  定义体: Cofan.mk pt (fun ⟨i, hi⟩ => ι' i hi)

Depends on / 依赖: Cofan.mk
-/
def CofanMapObjFun.mk (j : J) (pt : C) (ι' : forall (i : I) (_ : p i = j), X i ⟶ pt) :
    CofanMapObjFun X p j :=
  Cofan.mk pt (fun ⟨i, hi⟩ => ι' i hi)

/-- The tautological cofan corresponding to the coproduct decomposition of `X.mapObj p j`. -/
@[simp]
/--
Definition of `cofanMapObj` / `cofanMapObj` 的定义

English:
definition cofanMapObj
  signature: (j : J)
  body: CofanMapObjFun.mk X p j (X.mapObj p j) (fun i hi => X.ιMapObj p i j hi)

中文:
定义 cofanMapObj
  签名: (j : J)
  定义体: CofanMapObjFun.mk X p j (X.mapObj p j) (fun i hi => X.ιMapObj p i j hi)

Depends on / 依赖: CofanMapObjFun, CofanMapObjFun.mk, X.mapObj, mapObj
-/
noncomputable def cofanMapObj (j : J) : CofanMapObjFun X p j :=
  CofanMapObjFun.mk X p j (X.mapObj p j) (fun i hi => X.ιMapObj p i j hi)

/--
Definition of `isColimitCofanMapObj` / `isColimitCofanMapObj` 的定义

English:
definition isColimitCofanMapObj
  signature: (j : J)
  body: colimit.isColimit _

@[ext]

中文:
定义 isColimitCofanMapObj
  签名: (j : J)
  定义体: colimit.isColimit _

@[ext]

Depends on / 依赖: colimit, colimit.isColimit, isColimit
-/
noncomputable def isColimitCofanMapObj (j : J) : IsColimit (X.cofanMapObj p j) :=
  colimit.isColimit _

@[ext]
/--
lemma `mapObj_ext` / 引理 `mapObj_ext`

English:
lemma mapObj_ext
  statement: {A : C} {j : J} (f g : X.mapObj p j ⟶ A)
  proof: Cofan.IsColimit.hom_ext (X.isColimitCofanMapObj p j) _ _ (fun ⟨i, hij⟩ => hfg i hij)

中文:
引理 mapObj_ext
  结论: {A : C} {j : J} (f g : X.mapObj p j ⟶ A)
  证明: Cofan.IsColimit.hom_ext (X.isColimitCofanMapObj p j) _ _ (fun ⟨i, hij⟩ => hfg i hij)

Depends on / 依赖: Cofan.IsColimit.hom_ext, IsColimit, X.isColimitCofanMapObj, hom_ext, isColimitCofanMapObj
-/
lemma mapObj_ext {A : C} {j : J} (f g : X.mapObj p j ⟶ A)
    (hfg : forall (i : I) (hij : p i = j), X.ιMapObj p i j hij ≫ f = X.ιMapObj p i j hij ≫ g) :
    f = g :=
  Cofan.IsColimit.hom_ext (X.isColimitCofanMapObj p j) _ _ (fun ⟨i, hij⟩ => hfg i hij)

/--
Definition of `descMapObj` / `descMapObj` 的定义

English:
definition descMapObj
  signature: {A : C} {j : J} (φ : forall (i : I) (_ : p i = j), X i ⟶ A)
  body: Cofan.IsColimit.desc (X.isColimitCofanMapObj p j) (fun ⟨i, hi⟩ => φ i hi)

@[reassoc (attr := simp)]

中文:
定义 descMapObj
  签名: {A : C} {j : J} (φ : 对任意 (i : I) (_ : p i = j), X i ⟶ A)
  定义体: Cofan.IsColimit.desc (X.isColimitCofanMapObj p j) (fun ⟨i, hi⟩ => φ i hi)

@[reassoc (attr := simp)]

Depends on / 依赖: Cofan.IsColimit.desc, IsColimit, X.isColimitCofanMapObj, isColimitCofanMapObj
-/
noncomputable def descMapObj {A : C} {j : J} (φ : forall (i : I) (_ : p i = j), X i ⟶ A) :
    X.mapObj p j ⟶ A :=
  Cofan.IsColimit.desc (X.isColimitCofanMapObj p j) (fun ⟨i, hi⟩ => φ i hi)

@[reassoc (attr := simp)]
/--
lemma `ι_descMapObj` / 引理 `ι_descMapObj`

English:
lemma ι_descMapObj
  statement: {A : C} {j : J}
  proof: by
  apply Cofan.IsColimit.fac

中文:
引理 ι_descMapObj
  结论: {A : C} {j : J}
  证明: by
  apply Cofan.IsColimit.fac

Depends on / 依赖: Cofan.IsColimit.fac, IsColimit
-/
lemma ι_descMapObj {A : C} {j : J}
    (φ : forall (i : I) (_ : p i = j), X i ⟶ A) (i : I) (hi : p i = j) :
    X.ιMapObj p i j hi ≫ X.descMapObj p φ = φ i hi := by
  apply Cofan.IsColimit.fac

end
namespace CofanMapObjFun

/--
lemma `hasMap` / 引理 `hasMap`

English:
lemma hasMap
  given: (c : forall j, CofanMapObjFun X p j) (hc : forall j, IsColimit (c j))
  proof: fun j => ⟨_, hc j⟩

中文:
引理 hasMap
  条件: (c : 对任意 j, CofanMapObjFun X p j) (hc : 对任意 j, 是余极限 (c j))
  证明: fun j => ⟨_, hc j⟩
-/
lemma hasMap (c : forall j, CofanMapObjFun X p j) (hc : forall j, IsColimit (c j)) :
    X.HasMap p := fun j => ⟨_, hc j⟩

variable {j X p}
variable [X.HasMap p]
variable {c : CofanMapObjFun X p j} (hc : IsColimit c)

/--
Definition of `iso` / `iso` 的定义

English:
definition iso
  signature: : c.pt ≅ X.mapObj p j
  body: IsColimit.coconePointUniqueUpToIso hc (X.isColimitCofanMapObj p j)

@[reassoc (attr := simp)]

中文:
定义 iso
  签名: : c.pt ≅ X.mapObj p j
  定义体: IsColimit.coconePointUniqueUpToIso hc (X.isColimitCofanMapObj p j)

@[reassoc (attr := simp)]

Depends on / 依赖: IsColimit, IsColimit.coconePointUniqueUpToIso, X.isColimitCofanMapObj, coconePointUniqueUpToIso, isColimitCofanMapObj
-/
noncomputable def iso : c.pt ≅ X.mapObj p j :=
  IsColimit.coconePointUniqueUpToIso hc (X.isColimitCofanMapObj p j)

@[reassoc (attr := simp)]
/--
lemma `inj_iso_hom` / 引理 `inj_iso_hom`

English:
lemma inj_iso_hom
  given: (i : I) (hi : p i = j)
  proof: by
  apply IsColimit.comp_coconePointUniqueUpToIso_hom

@[reassoc (attr := simp)]

中文:
引理 inj_iso_hom
  条件: (i : I) (hi : p i = j)
  证明: by
  apply IsColimit.comp_coconePointUniqueUpToIso_hom

@[reassoc (attr := simp)]

Depends on / 依赖: IsColimit, IsColimit.comp_coconePointUniqueUpToIso_hom, comp_coconePointUniqueUpToIso_hom
-/
lemma inj_iso_hom (i : I) (hi : p i = j) :
    c.inj ⟨i, hi⟩ ≫ (c.iso hc).hom = X.ιMapObj p i j hi := by
  apply IsColimit.comp_coconePointUniqueUpToIso_hom

@[reassoc (attr := simp)]
/--
lemma `ιMapObj_iso_inv` / 引理 `ιMapObj_iso_inv`

English:
lemma ιMapObj_iso_inv
  given: (i : I) (hi : p i = j)
  proof: by
  apply IsColimit.comp_coconePointUniqueUpToIso_inv

中文:
引理 ιMapObj_iso_inv
  条件: (i : I) (hi : p i = j)
  证明: by
  apply IsColimit.comp_coconePointUniqueUpToIso_inv

Depends on / 依赖: IsColimit, IsColimit.comp_coconePointUniqueUpToIso_inv, comp_coconePointUniqueUpToIso_inv
-/
lemma ιMapObj_iso_inv (i : I) (hi : p i = j) :
    X.ιMapObj p i j hi ≫ (c.iso hc).inv = c.inj ⟨i, hi⟩ := by
  apply IsColimit.comp_coconePointUniqueUpToIso_inv

end CofanMapObjFun

variable {X Y}
variable [X.HasMap p] [Y.HasMap p]

/--
Definition of `mapMap` / `mapMap` 的定义

English:
definition mapMap
  signature: : X.mapObj p ⟶ Y.mapObj p
  body: fun j =>
  X.descMapObj p (fun i hi => φ i ≫ Y.ιMapObj p i j hi)

@[reassoc (attr := simp)]

中文:
定义 mapMap
  签名: : X.mapObj p ⟶ Y.mapObj p
  定义体: fun j =>
  X.descMapObj p (fun i hi => φ i ≫ Y.ιMapObj p i j hi)

@[reassoc (attr := simp)]
-/
noncomputable def mapMap : X.mapObj p ⟶ Y.mapObj p := fun j =>
  X.descMapObj p (fun i hi => φ i ≫ Y.ιMapObj p i j hi)

@[reassoc (attr := simp)]
/--
lemma `ι_mapMap` / 引理 `ι_mapMap`

English:
lemma ι_mapMap
  given: (i : I) (j : J) (hij : p i = j)
  proof: by
  simp only [mapMap, ι_descMapObj]

中文:
引理 ι_mapMap
  条件: (i : I) (j : J) (hij : p i = j)
  证明: by
  simp only [mapMap, ι_descMapObj]

Depends on / 依赖: mapMap
-/
lemma ι_mapMap (i : I) (j : J) (hij : p i = j) :
    X.ιMapObj p i j hij ≫ mapMap φ p j = φ i ≫ Y.ιMapObj p i j hij := by
  simp only [mapMap, ι_descMapObj]

/--
lemma `congr_mapMap` / 引理 `congr_mapMap`

English:
lemma congr_mapMap
  given: (φ₁ φ₂ : X ⟶ Y) (h : φ₁ = φ₂)
  statement: mapMap φ₁ p = mapMap φ₂ p
  proof: by
  subst h
  rfl

中文:
引理 congr_mapMap
  条件: (φ₁ φ₂ : X ⟶ Y) (h : φ₁ = φ₂)
  结论: mapMap φ₁ p = mapMap φ₂ p
  证明: by
  subst h
  rfl
-/
lemma congr_mapMap (φ₁ φ₂ : X ⟶ Y) (h : φ₁ = φ₂) : mapMap φ₁ p = mapMap φ₂ p := by
  subst h
  rfl

variable (X)

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `mapMap_id` / 引理 `mapMap_id`

English:
lemma mapMap_id
  statement: mapMap (𝟙 X) p = 𝟙 _
  proof: by cat_disch

中文:
引理 mapMap_id
  结论: mapMap (𝟙 X) p = 𝟙 _
  证明: by cat_disch

Depends on / 依赖: cat_disch
-/
lemma mapMap_id : mapMap (𝟙 X) p = 𝟙 _ := by cat_disch

variable {X Z}

set_option backward.isDefEq.respectTransparency.types false in
@[simp, reassoc]
/--
lemma `mapMap_comp` / 引理 `mapMap_comp`

English:
lemma mapMap_comp
  given: [Z.HasMap p]
  statement: mapMap (φ ≫ ψ) p = mapMap φ p ≫ mapMap ψ p
  proof: by cat_disch

中文:
引理 mapMap_comp
  条件: [Z.HasMap p]
  结论: mapMap (φ ≫ ψ) p = mapMap φ p ≫ mapMap ψ p
  证明: by cat_disch

Depends on / 依赖: cat_disch
-/
lemma mapMap_comp [Z.HasMap p] : mapMap (φ ≫ ψ) p = mapMap φ p ≫ mapMap ψ p := by cat_disch

set_option backward.isDefEq.respectTransparency.types false in
/-- The isomorphism of `J`-graded objects `X.mapObj p ≅ Y.mapObj p` induced by an
isomorphism `X ≅ Y` of graded objects and a map `p : I → J`. -/
@[simps]
/--
Definition of `mapIso` / `mapIso` 的定义

English:
definition mapIso
  signature: : X.mapObj p ≅ Y.mapObj p where
  body: mapMap e.hom p
  inv := mapMap e.inv p

中文:
定义 mapIso
  签名: : X.mapObj p ≅ Y.mapObj p where
  定义体: mapMap e.hom p
  inv := mapMap e.inv p

Depends on / 依赖: e.hom, mapMap
-/
noncomputable def mapIso : X.mapObj p ≅ Y.mapObj p where
  hom := mapMap e.hom p
  inv := mapMap e.inv p

variable (C)

/-- Given a map `p : I → J`, this is the functor `GradedObject I C ⥤ GradedObject J C` which
sends an `I`-object `X` to the graded object `X.mapObj p` which in degree `j : J` is given
by the coproduct of those `X i` such that `p i = j`. -/
@[simps]
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: [forall (j : J), HasColimitsOfShape (Discrete (p ⁻¹' {j})) C]
  body: X.mapObj p
  map φ := mapMap φ p

中文:
定义 map
  签名: [对任意 (j : J), 有形状余极限 (离散 (p ⁻¹' {j})) C]
  定义体: X.mapObj p
  map φ := mapMap φ p

Depends on / 依赖: X.mapObj, mapObj
-/
noncomputable def map [forall (j : J), HasColimitsOfShape (Discrete (p ⁻¹' {j})) C] :
    GradedObject I C ⥤ GradedObject J C where
  obj X := X.mapObj p
  map φ := mapMap φ p

variable {C} (X Y)
variable (q : J -> K) (r : I -> K) (hpqr : forall i, q (p i) = r i)

section

variable (k : K) (c : forall (j : J), q j = k -> X.CofanMapObjFun p j)
  (hc : forall j hj, IsColimit (c j hj))
  (c' : Cofan (fun (j : q ⁻¹' {k}) => (c j.1 j.2).pt)) (hc' : IsColimit c')

/-- Given maps `p : I → J`, `q : J → K` and `r : I → K` such that `q.comp p = r`,
`X : GradedObject I C`, `k : K`, the datum of cofans `X.CofanMapObjFun p j` for all
`j : J` and of a cofan for all the points of these cofans, this is a cofan of
type `X.CofanMapObjFun r k`, which is a colimit (see `isColimitCofanMapObjComp`) if the
given cofans are. -/
@[simp]
/--
Definition of `cofanMapObjComp` / `cofanMapObjComp` 的定义

English:
definition cofanMapObjComp
  signature: : X.CofanMapObjFun r k
  body: CofanMapObjFun.mk _ _ _ c'.pt (fun i hi =>
    (c (p i) (by rw [hpqr, hi])).inj ⟨i, rfl⟩ ≫ c'.inj (⟨p i, by
      rw [Set.mem_preimage]; rw [Set.mem_singleton_iff]; rw [hpqr]; rw [hi]⟩))

中文:
定义 cofanMapObjComp
  签名: : X.CofanMapObjFun r k
  定义体: CofanMapObjFun.mk _ _ _ c'.pt (fun i hi =>
    (c (p i) (by rw [hpqr, hi])).inj ⟨i, rfl⟩ ≫ c'.inj (⟨p i, by
      rw [Set.mem_preimage]; rw [Set.mem_singleton_iff]; rw [hpqr]; rw [hi]⟩))

Depends on / 依赖: CofanMapObjFun, CofanMapObjFun.mk, Set.mem_preimage, Set.mem_singleton_iff, mem_preimage, mem_singleton_iff
-/
def cofanMapObjComp : X.CofanMapObjFun r k :=
  CofanMapObjFun.mk _ _ _ c'.pt (fun i hi =>
    (c (p i) (by rw [hpqr, hi])).inj ⟨i, rfl⟩ ≫ c'.inj (⟨p i, by
      rw [Set.mem_preimage]; rw [Set.mem_singleton_iff]; rw [hpqr]; rw [hi]⟩))

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Given maps `p : I → J`, `q : J → K` and `r : I → K` such that `q.comp p = r`,
`X : GradedObject I C`, `k : K`, the cofan constructed by `cofanMapObjComp` is a colimit.
In other words, if we have, for all `j : J` such that `hj : q j = k`,
a colimit cofan `c j hj` which computes the coproduct of the `X i` such that `p i = j`,
and also a colimit cofan which computes the coproduct of the points of these `c j hj`, then
the point of this latter cofan computes the coproduct of the `X i` such that `r i = k`. -/
@[simp]
/--
Definition of `isColimitCofanMapObjComp` / `isColimitCofanMapObjComp` 的定义

English:
definition isColimitCofanMapObjComp
  signature: :
  body: Cofan.IsColimit.mk _
    (fun s => Cofan.IsColimit.desc hc'
      (fun ⟨j, (hj : q j = k)⟩ => Cofan.IsColimit.desc (hc j hj)
        (fun ⟨i, (hi : p i = j)⟩ => s.inj ⟨i, by
          simp only [Set.mem_preimage, Set.mem_singleton_iff, ← hpqr, hi, hj]⟩)))
    (fun s ⟨i, (hi : r i = k)⟩ => by simp)
    (fun s m hm => by
      apply Cofan.IsColimit.hom_ext hc'
      rintro ⟨j, rfl : q j = k⟩
      apply Cofan.IsColimit.hom_ext (hc j rfl)
      rintro ⟨i, rfl : p i = j⟩
      dsimp
      rw [Cofan.IsColimit.fac]; rw [Cofan.IsColimit.fac]; rw [← hm]
      dsimp
      rw [assoc])

include hpqr in

中文:
定义 isColimitCofanMapObjComp
  签名: :
  定义体: Cofan.IsColimit.mk _
    (fun s => Cofan.IsColimit.desc hc'
      (fun ⟨j, (hj : q j = k)⟩ => Cofan.IsColimit.desc (hc j hj)
        (fun ⟨i, (hi : p i = j)⟩ => s.inj ⟨i, by
          simp only [Set.mem_preimage, Set.mem_singleton_iff, ← hpqr, hi, hj]⟩)))
    (fun s ⟨i, (hi : r i = k)⟩ => by simp)
    (fun s m hm => by
      apply Cofan.IsColimit.hom_ext hc'
      rintro ⟨j, rfl : q j = k⟩
      apply Cofan.IsColimit.hom_ext (hc j rfl)
      rintro ⟨i, rfl : p i = j⟩
      dsimp
      rw [Cofan.IsColimit.fac]; rw [Cofan.IsColimit.fac]; rw [← hm]
      dsimp
      rw [assoc])

include hpqr in

Depends on / 依赖: Cofan.IsColimit.desc, Cofan.IsColimit.fac, Cofan.IsColimit.hom_ext, Cofan.IsColimit.mk, IsColimit, Set.mem_preimage, Set.mem_singleton_iff, hom_ext, mem_preimage, mem_singleton_iff, s.inj
-/
def isColimitCofanMapObjComp :
    IsColimit (cofanMapObjComp X p q r hpqr k c c') :=
  Cofan.IsColimit.mk _
    (fun s => Cofan.IsColimit.desc hc'
      (fun ⟨j, (hj : q j = k)⟩ => Cofan.IsColimit.desc (hc j hj)
        (fun ⟨i, (hi : p i = j)⟩ => s.inj ⟨i, by
          simp only [Set.mem_preimage, Set.mem_singleton_iff, ← hpqr, hi, hj]⟩)))
    (fun s ⟨i, (hi : r i = k)⟩ => by simp)
    (fun s m hm => by
      apply Cofan.IsColimit.hom_ext hc'
      rintro ⟨j, rfl : q j = k⟩
      apply Cofan.IsColimit.hom_ext (hc j rfl)
      rintro ⟨i, rfl : p i = j⟩
      dsimp
      rw [Cofan.IsColimit.fac]; rw [Cofan.IsColimit.fac]; rw [← hm]
      dsimp
      rw [assoc])

include hpqr in
/--
lemma `hasMap_comp` / 引理 `hasMap_comp`

English:
lemma hasMap_comp
  given: [(X.mapObj p).HasMap q]
  statement: X.HasMap r
  proof: fun k => ⟨_, isColimitCofanMapObjComp X p q r hpqr k _
    (fun j _ => X.isColimitCofanMapObj p j) _ ((X.mapObj p).isColimitCofanMapObj q k)⟩

中文:
引理 hasMap_comp
  条件: [(X.mapObj p).HasMap q]
  结论: X.HasMap r
  证明: fun k => ⟨_, isColimitCofanMapObjComp X p q r hpqr k _
    (fun j _ => X.isColimitCofanMapObj p j) _ ((X.mapObj p).isColimitCofanMapObj q k)⟩

Depends on / 依赖: X.isColimitCofanMapObj, X.mapObj, isColimitCofanMapObj, isColimitCofanMapObjComp, mapObj
-/
lemma hasMap_comp [(X.mapObj p).HasMap q] : X.HasMap r :=
  fun k => ⟨_, isColimitCofanMapObjComp X p q r hpqr k _
    (fun j _ => X.isColimitCofanMapObj p j) _ ((X.mapObj p).isColimitCofanMapObj q k)⟩

end

variable [HasZeroMorphisms C] [DecidableEq J] (i : I) (j : J)

/--
Definition of `ιMapObjOrZero` / `ιMapObjOrZero` 的定义

English:
definition ιMapObjOrZero
  signature: : X i ⟶ X.mapObj p j
  body: if h : p i = j
    then X.ιMapObj p i j h
    else 0

中文:
定义 ιMapObjOrZero
  签名: : X i ⟶ X.mapObj p j
  定义体: if h : p i = j
    then X.ιMapObj p i j h
    else 0
-/
noncomputable def ιMapObjOrZero : X i ⟶ X.mapObj p j :=
  if h : p i = j
    then X.ιMapObj p i j h
    else 0

/--
lemma `ιMapObjOrZero_eq` / 引理 `ιMapObjOrZero_eq`

English:
lemma ιMapObjOrZero_eq
  given: (h : p i = j)
  statement: X.ιMapObjOrZero p i j = X.ιMapObj p i j h
  proof: dif_pos h

中文:
引理 ιMapObjOrZero_eq
  条件: (h : p i = j)
  结论: X.ιMapObjOrZero p i j = X.ιMapObj p i j h
  证明: dif_pos h

Depends on / 依赖: dif_pos
-/
lemma ιMapObjOrZero_eq (h : p i = j) : X.ιMapObjOrZero p i j = X.ιMapObj p i j h := dif_pos h

/--
lemma `ιMapObjOrZero_eq_zero` / 引理 `ιMapObjOrZero_eq_zero`

English:
lemma ιMapObjOrZero_eq_zero
  given: (h : p i != j)
  statement: X.ιMapObjOrZero p i j = 0
  proof: dif_neg h

中文:
引理 ιMapObjOrZero_eq_zero
  条件: (h : p i != j)
  结论: X.ιMapObjOrZero p i j = 0
  证明: dif_neg h

Depends on / 依赖: dif_neg
-/
lemma ιMapObjOrZero_eq_zero (h : p i != j) : X.ιMapObjOrZero p i j = 0 := dif_neg h

variable {X Y} in
@[reassoc (attr := simp)]
/--
lemma `ιMapObjOrZero_mapMap` / 引理 `ιMapObjOrZero_mapMap`

English:
lemma ιMapObjOrZero_mapMap
  proof: by
  by_cases h : p i = j
  · simp only [ιMapObjOrZero_eq _ _ _ _ h, ι_mapMap]
  · simp only [ιMapObjOrZero_eq_zero _ _ _ _ h, zero_comp, comp_zero]

中文:
引理 ιMapObjOrZero_mapMap
  证明: by
  by_cases h : p i = j
  · simp only [ιMapObjOrZero_eq _ _ _ _ h, ι_mapMap]
  · simp only [ιMapObjOrZero_eq_zero _ _ _ _ h, zero_comp, comp_zero]

Depends on / 依赖: comp_zero, zero_comp
-/
lemma ιMapObjOrZero_mapMap :
    X.ιMapObjOrZero p i j ≫ mapMap φ p j = φ i ≫ Y.ιMapObjOrZero p i j := by
  by_cases h : p i = j
  · simp only [ιMapObjOrZero_eq _ _ _ _ h, ι_mapMap]
  · simp only [ιMapObjOrZero_eq_zero _ _ _ _ h, zero_comp, comp_zero]

end GradedObject

end CategoryTheory
