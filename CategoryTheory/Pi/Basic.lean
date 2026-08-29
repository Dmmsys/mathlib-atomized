/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Kim Morrison
-/
module

public import Mathlib.CategoryTheory.EqToHom
public import Mathlib.CategoryTheory.NatIso
public import Mathlib.CategoryTheory.Products.Basic

/-!
# Categories of indexed families of objects.

We define the pointwise category structure on indexed families of objects in a category
(and also the dependent generalization).

-/

@[expose] public section

namespace CategoryTheory

open CategoryTheory.Functor

universe w₀ w₁ w₂ v₁ v₂ v₃ u₁ u₂ u₃

variable {I : Type w₀} {J : Type w₁} (C : I -> Type u₁) [forall i, Category.{v₁} (C i)]


/--
Instance `pi` / 实例 `pi`

English:
instance pi
  signature: : Category.{max w₀ v₁} (forall i, C i) where
  body: forall i, X i ⟶ Y i
  id X i := 𝟙 (X i)
  comp f g i := f i ≫ g i

中文:
实例 pi
  签名: : 范畴.{最大值 w₀ v₁} (对任意 i, C i) where
  定义体: forall i, X i ⟶ Y i
  id X i := 𝟙 (X i)
  comp f g i := f i ≫ g i
-/
instance pi : Category.{max w₀ v₁} (forall i, C i) where
  Hom X Y := forall i, X i ⟶ Y i
  id X i := 𝟙 (X i)
  comp f g i := f i ≫ g i

namespace Pi

@[simp]
/--
theorem `id_apply` / 定理 `id_apply`

English:
theorem id_apply
  given: (X : forall i, C i) (i)
  statement: (𝟙 X : forall i, X i ⟶ X i) i = 𝟙 (X i)
  proof: rfl

@[simp]

中文:
定理 id_apply
  条件: (X : 对任意 i, C i) (i)
  结论: (𝟙 X : 对任意 i, X i ⟶ X i) i = 𝟙 (X i)
  证明: rfl

@[simp]
-/
theorem id_apply (X : forall i, C i) (i) : (𝟙 X : forall i, X i ⟶ X i) i = 𝟙 (X i) :=
  rfl

@[simp]
/--
theorem `comp_apply` / 定理 `comp_apply`

English:
theorem comp_apply
  given: {X Y Z : forall i, C i} (f : X ⟶ Y) (g : Y ⟶ Z) (i)
  proof: rfl

@[ext]

中文:
定理 comp_apply
  条件: {X Y Z : 对任意 i, C i} (f : X ⟶ Y) (g : Y ⟶ Z) (i)
  证明: rfl

@[ext]
-/
theorem comp_apply {X Y Z : forall i, C i} (f : X ⟶ Y) (g : Y ⟶ Z) (i) :
    (f ≫ g : forall i, X i ⟶ Z i) i = f i ≫ g i :=
  rfl

@[ext]
/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  given: {X Y : forall i, C i} {f g : X ⟶ Y} (w : forall i, f i = g i)
  statement: f = g
  proof: funext (w ·)

中文:
引理 ext
  条件: {X Y : 对任意 i, C i} {f g : X ⟶ Y} (w : 对任意 i, f i = g i)
  结论: f = g
  证明: funext (w ·)
-/
lemma ext {X Y : forall i, C i} {f g : X ⟶ Y} (w : forall i, f i = g i) : f = g :=
  funext (w ·)

/--
The evaluation functor at `i : I`, sending an `I`-indexed family of objects to the object over `i`.
-/
@[simps]
/--
Definition of `eval` / `eval` 的定义

English:
definition eval
  signature: (i : I)
  body: f i
  map α := α i

中文:
定义 eval
  签名: (i : I)
  定义体: f i
  map α := α i
-/
def eval (i : I) : (forall i, C i) ⥤ C i where
  obj f := f i
  map α := α i

section

variable {J : Type w₁}

instance (f : J -> I) : (j : J) -> Category ((C ∘ f) j) :=
inferInstanceAs (j : J) -> Category (C (f j))

/-- Pull back an `I`-indexed family of objects to a `J`-indexed family, along a function `J → I`.
-/
@[simps, implicit_reducible]
/--
Definition of `comap` / `comap` 的定义

English:
definition comap
  signature: (h : J -> I)
  body: f (h i)
  map α i := α (h i)

中文:
定义 comap
  签名: (h : J -> I)
  定义体: f (h i)
  map α i := α (h i)
-/
def comap (h : J -> I) : (forall i, C i) ⥤ (forall j, C (h j)) where
  obj f i := f (h i)
  map α i := α (h i)

variable (I)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The natural isomorphism between
pulling back a grading along the identity function,
and the identity functor. -/
@[simps]
/--
Definition of `comapId` / `comapId` 的定义

English:
definition comapId
  signature: : comap C (id : I -> I) ≅ 𝟭 (forall i, C i) where
  body: { app := fun X => 𝟙 X }
  inv := { app := fun X => 𝟙 X }

example (g : J -> I) : (j : J) -> Category (C (g j)) := by infer_instance

中文:
定义 comapId
  签名: : comap C (id : I -> I) ≅ 𝟭 (对任意 i, C i) where
  定义体: { app := fun X => 𝟙 X }
  inv := { app := fun X => 𝟙 X }

example (g : J -> I) : (j : J) -> Category (C (g j)) := by infer_instance
-/
def comapId : comap C (id : I -> I) ≅ 𝟭 (forall i, C i) where
  hom := { app := fun X => 𝟙 X }
  inv := { app := fun X => 𝟙 X }

example (g : J -> I) : (j : J) -> Category (C (g j)) := by infer_instance

variable {I}
variable {K : Type w₂}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The natural isomorphism comparing between
pulling back along two successive functions, and
pulling back along their composition
-/
@[simps!]
/--
Definition of `comapComp` / `comapComp` 的定义

English:
definition comapComp
  signature: (f : K -> J) (g : J -> I)
  body: { app := fun X b => 𝟙 (X (g (f b)))
    naturality := fun X Y f' => by simp only [comap, Function.comp]; funext; simp }
  inv :=
  { app := fun X b => 𝟙 (X (g (f b)))
    naturality := fun X Y f' => by simp only [comap, Function.comp]; funext; simp }

中文:
定义 comapComp
  签名: (f : K -> J) (g : J -> I)
  定义体: { app := fun X b => 𝟙 (X (g (f b)))
    naturality := fun X Y f' => by simp only [comap, Function.comp]; funext; simp }
  inv :=
  { app := fun X b => 𝟙 (X (g (f b)))
    naturality := fun X Y f' => by simp only [comap, Function.comp]; funext; simp }

Depends on / 依赖: Function, Function.comp, naturality
-/
def comapComp (f : K -> J) (g : J -> I) : comap C g ⋙ comap (C ∘ g) f ≅ comap C (g ∘ f) where
  hom :=
  { app := fun X b => 𝟙 (X (g (f b)))
    naturality := fun X Y f' => by simp only [comap, Function.comp]; funext; simp }
  inv :=
  { app := fun X b => 𝟙 (X (g (f b)))
    naturality := fun X Y f' => by simp only [comap, Function.comp]; funext; simp }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The natural isomorphism between pulling back then evaluating, and just evaluating. -/
@[simps!]
/--
Definition of `comapEvalIsoEval` / `comapEvalIsoEval` 的定义

English:
definition comapEvalIsoEval
  signature: (h : J -> I) (j : J)
  body: NatIso.ofComponents (fun _ => Iso.refl _) (by simp)

中文:
定义 comapEvalIsoEval
  签名: (h : J -> I) (j : J)
  定义体: NatIso.ofComponents (fun _ => Iso.refl _) (by simp)

Depends on / 依赖: Iso.refl, NatIso, NatIso.ofComponents, ofComponents
-/
def comapEvalIsoEval (h : J -> I) (j : J) : comap C h ⋙ eval (C ∘ h) j ≅ eval C (h j) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by simp)

end

section

variable {J : Type w₀} {D : J -> Type u₁} [forall j, Category.{v₁} (D j)]

/--
Instance `sumElimCategory` / 实例 `sumElimCategory`

English:
instance sumElimCategory
  signature: : forall s : I oplus J, Category.{v₁} (Sum.elim C D s)

中文:
实例 sumElimCategory
  签名: : 对任意 s : I oplus J, 范畴.{v₁} (和.elim C D s)
-/
instance sumElimCategory : forall s : I oplus J, Category.{v₁} (Sum.elim C D s)
| Sum.inl i => inferInstanceAs Category (C i)
| Sum.inr j => inferInstanceAs Category (D j)

set_option backward.isDefEq.respectTransparency false in
/-- The bifunctor combining an `I`-indexed family of objects with a `J`-indexed family of objects
to obtain an `I ⊕ J`-indexed family of objects.
-/
@[simps]
/--
Definition of `sum` / `sum` 的定义

English:
definition sum
  signature: : (forall i, C i) ⥤ (forall j, D j) ⥤ forall s : I oplus J, Sum.elim C D s where
  body: { obj := fun Y s =>
        match s with
        | .inl i => X i
        | .inr j => Y j
      map := fun {_} {_} f s =>
        match s with
        | .inl i => 𝟙 (X i)
        | .inr j => f j }
  map {X} {X'} f :=
    { app := fun Y s =>
        match s with
        | .inl i => f i
        | .inr 

中文:
定义 求和
  签名: : (对任意 i, C i) ⥤ (对任意 j, D j) ⥤ 对任意 s : I oplus J, 和.elim C D s where
  定义体: { obj := fun Y s =>
        match s with
        | .inl i => X i
        | .inr j => Y j
      map := fun {_} {_} f s =>
        match s with
        | .inl i => 𝟙 (X i)
        | .inr j => f j }
  map {X} {X'} f :=
    { app := fun Y s =>
        match s with
        | .inl i => f i
        | .inr 
-/
def sum : (forall i, C i) ⥤ (forall j, D j) ⥤ forall s : I oplus J, Sum.elim C D s where
  obj X :=
    { obj := fun Y s =>
        match s with
        | .inl i => X i
        | .inr j => Y j
      map := fun {_} {_} f s =>
        match s with
        | .inl i => 𝟙 (X i)
        | .inr j => f j }
  map {X} {X'} f :=
    { app := fun Y s =>
        match s with
        | .inl i => f i
        | .inr j => 𝟙 (Y j) }

end

variable {C}

/-- A family of isomorphisms gives rise to an isomorphism of families. -/
@[simps]
/--
Definition of `isoMk` / `isoMk` 的定义

English:
definition isoMk
  signature: {X Y : forall i, C i} (iso : forall i, X i ≅ Y i)
  body: fun i => (iso i).hom
  inv := fun i => (iso i).inv

中文:
定义 isoMk
  签名: {X Y : 对任意 i, C i} (iso : 对任意 i, X i ≅ Y i)
  定义体: fun i => (iso i).hom
  inv := fun i => (iso i).inv
-/
def isoMk {X Y : forall i, C i} (iso : forall i, X i ≅ Y i) :
    X ≅ Y where
  hom := fun i => (iso i).hom
  inv := fun i => (iso i).inv

/-- An isomorphism between `I`-indexed objects gives an isomorphism between each
pair of corresponding components. -/
@[simps]
/--
Definition of `isoApp` / `isoApp` 的定义

English:
definition isoApp
  signature: {X Y : forall i, C i} (f : X ≅ Y) (i : I)
  body: ⟨f.hom i, f.inv i,
    by rw [← comp_apply, Iso.hom_inv_id, id_apply], by rw [← comp_apply, Iso.inv_hom_id, id_apply]⟩

@[simp]

中文:
定义 isoApp
  签名: {X Y : 对任意 i, C i} (f : X ≅ Y) (i : I)
  定义体: ⟨f.hom i, f.inv i,
    by rw [← comp_apply, Iso.hom_inv_id, id_apply], by rw [← comp_apply, Iso.inv_hom_id, id_apply]⟩

@[simp]

Depends on / 依赖: Iso.hom_inv_id, Iso.inv_hom_id, comp_apply, f.hom, f.inv, hom_inv_id, id_apply, inv_hom_id
-/
def isoApp {X Y : forall i, C i} (f : X ≅ Y) (i : I) : X i ≅ Y i :=
  ⟨f.hom i, f.inv i,
    by rw [← comp_apply, Iso.hom_inv_id, id_apply], by rw [← comp_apply, Iso.inv_hom_id, id_apply]⟩

@[simp]
/--
theorem `isoApp_refl` / 定理 `isoApp_refl`

English:
theorem isoApp_refl
  given: (X : forall i, C i) (i : I)
  statement: isoApp (Iso.refl X) i = Iso.refl (X i)
  proof: rfl

@[simp]

中文:
定理 isoApp_refl
  条件: (X : 对任意 i, C i) (i : I)
  结论: isoApp (同构.refl X) i = 同构.refl (X i)
  证明: rfl

@[simp]
-/
theorem isoApp_refl (X : forall i, C i) (i : I) : isoApp (Iso.refl X) i = Iso.refl (X i) :=
  rfl

@[simp]
/--
theorem `isoApp_symm` / 定理 `isoApp_symm`

English:
theorem isoApp_symm
  given: {X Y : forall i, C i} (f : X ≅ Y) (i : I)
  statement: isoApp f.symm i = (isoApp f i).symm
  proof: rfl

@[simp]

中文:
定理 isoApp_symm
  条件: {X Y : 对任意 i, C i} (f : X ≅ Y) (i : I)
  结论: isoApp f.symm i = (isoApp f i).symm
  证明: rfl

@[simp]
-/
theorem isoApp_symm {X Y : forall i, C i} (f : X ≅ Y) (i : I) : isoApp f.symm i = (isoApp f i).symm :=
  rfl

@[simp]
/--
theorem `isoApp_trans` / 定理 `isoApp_trans`

English:
theorem isoApp_trans
  given: {X Y Z : forall i, C i} (f : X ≅ Y) (g : Y ≅ Z) (i : I)
  proof: rfl

中文:
定理 isoApp_trans
  条件: {X Y Z : 对任意 i, C i} (f : X ≅ Y) (g : Y ≅ Z) (i : I)
  证明: rfl
-/
theorem isoApp_trans {X Y Z : forall i, C i} (f : X ≅ Y) (g : Y ≅ Z) (i : I) :
    isoApp (f ≪≫ g) i = isoApp f i ≪≫ isoApp g i :=
  rfl

end Pi

namespace Functor

variable {C}
variable {D : I -> Type u₂} [forall i, Category.{v₂} (D i)] {A : Type u₃} [Category.{v₃} A]

/-- Assemble an `I`-indexed family of functors into a functor between the pi types.
-/
@[simps]
/--
Definition of `pi` / `pi` 的定义

English:
definition pi
  signature: (F : forall i, C i ⥤ D i)
  body: (F i).obj (f i)
  map α i := (F i).map (α i)

中文:
定义 pi
  签名: (F : 对任意 i, C i ⥤ D i)
  定义体: (F i).obj (f i)
  map α i := (F i).map (α i)
-/
def pi (F : forall i, C i ⥤ D i) : (forall i, C i) ⥤ forall i, D i where
  obj f i := (F i).obj (f i)
  map α i := (F i).map (α i)

/-- Similar to `pi`, but all functors come from the same category `A`
-/
@[simps]
/--
Definition of `pi'` / `pi'` 的定义

English:
definition pi'
  signature: (f : forall i, A ⥤ C i)
  body: (f i).obj a
  map h i := (f i).map h

中文:
定义 pi'
  签名: (f : 对任意 i, A ⥤ C i)
  定义体: (f i).obj a
  map h i := (f i).map h
-/
def pi' (f : forall i, A ⥤ C i) : A ⥤ forall i, C i where
  obj a i := (f i).obj a
  map h i := (f i).map h

/-- The projections of `Functor.pi' F` are isomorphic to the functors of the family `F` -/
@[simps!]
/--
Definition of `pi'CompEval` / `pi'CompEval` 的定义

English:
definition pi'CompEval
  signature: {A : Type*} [Category* A] (F : forall i, A ⥤ C i) (i : I)
  body: Iso.refl _

中文:
定义 pi'CompEval
  签名: {A : 类型} [范畴* A] (F : 对任意 i, A ⥤ C i) (i : I)
  定义体: Iso.refl _
-/
def pi'CompEval {A : Type*} [Category* A] (F : forall i, A ⥤ C i) (i : I) :
    pi' F ⋙ Pi.eval C i ≅ F i :=
  Iso.refl _

section EqToHom

@[simp]
/--
theorem `eqToHom_proj` / 定理 `eqToHom_proj`

English:
theorem eqToHom_proj
  given: {x x' : forall i, C i} (h : x = x') (i : I)
  proof: by
  subst h
  rfl

中文:
定理 eqToHom_proj
  条件: {x x' : 对任意 i, C i} (h : x = x') (i : I)
  证明: by
  subst h
  rfl
-/
theorem eqToHom_proj {x x' : forall i, C i} (h : x = x') (i : I) :
    (eqToHom h : x ⟶ x') i = eqToHom (funext_iff.mp h i) := by
  subst h
  rfl

end EqToHom

-- One could add some natural isomorphisms showing
-- how `Functor.pi` commutes with `Pi.eval` and `Pi.comap`.
@[simp]
/--
theorem `pi'_eval` / 定理 `pi'_eval`

English:
theorem pi'_eval
  given: (f : forall i, A ⥤ C i) (i : I)
  statement: pi' f ⋙ Pi.eval C i = f i
  proof: rfl

中文:
定理 pi'_eval
  条件: (f : 对任意 i, A ⥤ C i) (i : I)
  结论: pi' f ⋙ 依赖函数类型.eval C i = f i
  证明: rfl
-/
theorem pi'_eval (f : forall i, A ⥤ C i) (i : I) : pi' f ⋙ Pi.eval C i = f i :=
  rfl

/--
theorem `pi_ext` / 定理 `pi_ext`

English:
theorem pi_ext
  given: (f f' : A ⥤ forall i, C i) (h : forall i, f ⋙ (Pi.eval C i) = f' ⋙ (Pi.eval C i))
  proof: by
  apply Functor.ext; rotate_left
  · intro X
    ext i
    specialize h i
    have := congr_obj h X
    simpa
  · intro X Y g
    funext i
    specialize h i
    have := congr_hom h g
    simpa

中文:
定理 pi_ext
  条件: (f f' : A ⥤ 对任意 i, C i) (h : 对任意 i, f ⋙ (依赖函数类型.eval C i) = f' ⋙ (依赖函数类型.eval C i))
  证明: by
  apply Functor.ext; rotate_left
  · intro X
    ext i
    specialize h i
    have := congr_obj h X
    simpa
  · intro X Y g
    funext i
    specialize h i
    have := congr_hom h g
    simpa

Depends on / 依赖: Functor, Functor.ext, congr_hom, congr_obj, rotate_left, specialize
-/
theorem pi_ext (f f' : A ⥤ forall i, C i) (h : forall i, f ⋙ (Pi.eval C i) = f' ⋙ (Pi.eval C i)) :
    f = f' := by
  apply Functor.ext; rotate_left
  · intro X
    ext i
    specialize h i
    have := congr_obj h X
    simpa
  · intro X Y g
    funext i
    specialize h i
    have := congr_hom h g
    simpa

end Functor

namespace NatTrans

variable {C}
variable {D : I -> Type u₂} [forall i, Category.{v₂} (D i)]
variable {F G : forall i, C i ⥤ D i}

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Assemble an `I`-indexed family of natural transformations into a single natural transformation.
-/
@[simps!]
/--
Definition of `pi` / `pi` 的定义

English:
definition pi
  signature: (α : forall i, F i ⟶ G i)
  body: (α i).app (f i)

中文:
定义 pi
  签名: (α : 对任意 i, F i ⟶ G i)
  定义体: (α i).app (f i)
-/
def pi (α : forall i, F i ⟶ G i) : Functor.pi F ⟶ Functor.pi G where
  app f i := (α i).app (f i)

/-- Assemble an `I`-indexed family of natural transformations into a single natural transformation.
-/
@[simps]
/--
Definition of `pi'` / `pi'` 的定义

English:
definition pi'
  signature: {E : Type*} [Category* E] {F G : E ⥤ forall i, C i}
  body: fun X i => (τ i).app X
  naturality _ _ f := by
    ext i
    exact (τ i).naturality f

中文:
定义 pi'
  签名: {E : 类型} [范畴* E] {F G : E ⥤ 对任意 i, C i}
  定义体: fun X i => (τ i).app X
  naturality _ _ f := by
    ext i
    exact (τ i).naturality f
-/
def pi' {E : Type*} [Category* E] {F G : E ⥤ forall i, C i}
    (τ : forall i, F ⋙ Pi.eval C i ⟶ G ⋙ Pi.eval C i) : F ⟶ G where
  app := fun X i => (τ i).app X
  naturality _ _ f := by
    ext i
    exact (τ i).naturality f

end NatTrans

namespace NatIso

variable {C}
variable {D : I -> Type u₂} [forall i, Category.{v₂} (D i)]
variable {F G : forall i, C i ⥤ D i}

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Assemble an `I`-indexed family of natural isomorphisms into a single natural isomorphism.
-/
@[simps]
/--
Definition of `pi` / `pi` 的定义

English:
definition pi
  signature: (e : forall i, F i ≅ G i)
  body: NatTrans.pi (fun i => (e i).hom)
  inv := NatTrans.pi (fun i => (e i).inv)

中文:
定义 pi
  签名: (e : 对任意 i, F i ≅ G i)
  定义体: NatTrans.pi (fun i => (e i).hom)
  inv := NatTrans.pi (fun i => (e i).inv)

Depends on / 依赖: NatTrans, NatTrans.pi
-/
def pi (e : forall i, F i ≅ G i) : Functor.pi F ≅ Functor.pi G where
  hom := NatTrans.pi (fun i => (e i).hom)
  inv := NatTrans.pi (fun i => (e i).inv)

set_option backward.isDefEq.respectTransparency false in
/-- Assemble an `I`-indexed family of natural isomorphisms into a single natural isomorphism.
-/
@[simps]
/--
Definition of `pi'` / `pi'` 的定义

English:
definition pi'
  signature: {E : Type*} [Category* E] {F G : E ⥤ forall i, C i}
  body: NatTrans.pi' (fun i => (e i).hom)
  inv := NatTrans.pi' (fun i => (e i).inv)

中文:
定义 pi'
  签名: {E : 类型} [范畴* E] {F G : E ⥤ 对任意 i, C i}
  定义体: NatTrans.pi' (fun i => (e i).hom)
  inv := NatTrans.pi' (fun i => (e i).inv)

Depends on / 依赖: NatTrans, NatTrans.pi
-/
def pi' {E : Type*} [Category* E] {F G : E ⥤ forall i, C i}
    (e : forall i, F ⋙ Pi.eval C i ≅ G ⋙ Pi.eval C i) : F ≅ G where
  hom := NatTrans.pi' (fun i => (e i).hom)
  inv := NatTrans.pi' (fun i => (e i).inv)

end NatIso

variable {C}

/--
lemma `isIso_pi_iff` / 引理 `isIso_pi_iff`

English:
lemma isIso_pi_iff
  given: {X Y : forall i, C i} (f : X ⟶ Y)
  proof: by
  constructor
  · intro _ i
    exact (Pi.isoApp (asIso f) i).isIso_hom
  · intro
    exact ⟨fun i => inv (f i), by cat_disch, by cat_disch⟩

中文:
引理 isIso_pi_iff
  条件: {X Y : 对任意 i, C i} (f : X ⟶ Y)
  证明: by
  constructor
  · intro _ i
    exact (Pi.isoApp (asIso f) i).isIso_hom
  · intro
    exact ⟨fun i => inv (f i), by cat_disch, by cat_disch⟩

Depends on / 依赖: Pi.isoApp, cat_disch, isIso_hom, isoApp
-/
lemma isIso_pi_iff {X Y : forall i, C i} (f : X ⟶ Y) :
    IsIso f ↔ forall i, IsIso (f i) := by
  constructor
  · intro _ i
    exact (Pi.isoApp (asIso f) i).isIso_hom
  · intro
    exact ⟨fun i => inv (f i), by cat_disch, by cat_disch⟩

variable (C)

/--
Definition of `Pi.eqToEquivalence` / `Pi.eqToEquivalence` 的定义

English:
definition Pi.eqToEquivalence
  signature: {i j : I} (h : i = j)
  body: by subst h; rfl

中文:
定义 依赖函数类型.eqToEquivalence
  签名: {i j : I} (h : i = j)
  定义体: by subst h; rfl
-/
def Pi.eqToEquivalence {i j : I} (h : i = j) : C i ≌ C j := by subst h; rfl

/-- When `i = j`, projections `Pi.eval C i` and `Pi.eval C j` are related by the equivalence
`Pi.eqToEquivalence C h : C i ≌ C j`. -/
@[simps!]
/--
Definition of `Pi.evalCompEqToEquivalenceFunctor` / `Pi.evalCompEqToEquivalenceFunctor` 的定义

English:
definition Pi.evalCompEqToEquivalenceFunctor
  signature: {i j : I} (h : i = j)
  body: eqToIso (by subst h; rfl)

中文:
定义 依赖函数类型.evalCompEqToEquivalenceFunctor
  签名: {i j : I} (h : i = j)
  定义体: eqToIso (by subst h; rfl)

Depends on / 依赖: eqToIso
-/
def Pi.evalCompEqToEquivalenceFunctor {i j : I} (h : i = j) :
    Pi.eval C i ⋙ (Pi.eqToEquivalence C h).functor ≅
      Pi.eval C j :=
  eqToIso (by subst h; rfl)

/-- The equivalences given by `Pi.eqToEquivalence` are compatible with reindexing. -/
@[simps!]
/--
Definition of `Pi.eqToEquivalenceFunctorIso` / `Pi.eqToEquivalenceFunctorIso` 的定义

English:
definition Pi.eqToEquivalenceFunctorIso
  signature: (f : J -> I) {i' j' : J} (h : i' = j')
  body: eqToIso (by subst h; rfl)

中文:
定义 依赖函数类型.eqToEquivalenceFunctorIso
  签名: (f : J -> I) {i' j' : J} (h : i' = j')
  定义体: eqToIso (by subst h; rfl)

Depends on / 依赖: eqToIso
-/
def Pi.eqToEquivalenceFunctorIso (f : J -> I) {i' j' : J} (h : i' = j') :
    (Pi.eqToEquivalence C (congr_arg f h)).functor ≅
      (Pi.eqToEquivalence (fun i' => C (f i')) h).functor :=
  eqToIso (by subst h; rfl)

attribute [local simp] eqToHom_map

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Reindexing a family of categories gives equivalent `Pi` categories. -/
@[simps]
/--
Definition of `Pi.equivalenceOfEquiv` / `Pi.equivalenceOfEquiv` 的定义

English:
definition Pi.equivalenceOfEquiv
  signature: (e : J ≃ I)
  body: pi' (fun i => Pi.eval _ (e.symm i) ⋙
    (Pi.eqToEquivalence C (by simp)).functor)
  inverse := Functor.pi' (fun i' => Pi.eval _ (e i'))
  unitIso := NatIso.pi' (fun i' => leftUnitor _ ≪≫
    (Pi.evalCompEqToEquivalenceFunctor (fun j => C (e j)) (e.symm_apply_apply i')).symm ≪≫
    isoWhiskerLeft _ 

中文:
定义 依赖函数类型.equivalenceOfEquiv
  签名: (e : J ≃ I)
  定义体: pi' (fun i => Pi.eval _ (e.symm i) ⋙
    (Pi.eqToEquivalence C (by simp)).functor)
  inverse := Functor.pi' (fun i' => Pi.eval _ (e i'))
  unitIso := NatIso.pi' (fun i' => leftUnitor _ ≪≫
    (Pi.evalCompEqToEquivalenceFunctor (fun j => C (e j)) (e.symm_apply_apply i')).symm ≪≫
    isoWhiskerLeft _ 

Depends on / 依赖: Pi.eval, e.symm
-/
noncomputable def Pi.equivalenceOfEquiv (e : J ≃ I) :
    (forall j, C (e j)) ≌ (forall i, C i) where
  functor := pi' (fun i => Pi.eval _ (e.symm i) ⋙
    (Pi.eqToEquivalence C (by simp)).functor)
  inverse := Functor.pi' (fun i' => Pi.eval _ (e i'))
  unitIso := NatIso.pi' (fun i' => leftUnitor _ ≪≫
    (Pi.evalCompEqToEquivalenceFunctor (fun j => C (e j)) (e.symm_apply_apply i')).symm ≪≫
    isoWhiskerLeft _ ((Pi.eqToEquivalenceFunctorIso C e (e.symm_apply_apply i')).symm) ≪≫
    (pi'CompEval _ _).symm ≪≫ isoWhiskerLeft _ (pi'CompEval _ _).symm ≪≫
    (associator _ _ _).symm)
  counitIso := NatIso.pi' (fun i => (associator _ _ _).symm ≪≫
    isoWhiskerRight (pi'CompEval _ _) _ ≪≫
    Pi.evalCompEqToEquivalenceFunctor C (e.apply_symm_apply i) ≪≫
    (leftUnitor _).symm)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A product of categories indexed by `Option J` identifies to a binary product. -/
@[simps]
/--
Definition of `Pi.optionEquivalence` / `Pi.optionEquivalence` 的定义

English:
definition Pi.optionEquivalence
  signature: (C' : Option J -> Type u₁) [forall i, Category.{v₁} (C' i)]
  body: Functor.prod' (Pi.eval C' none)
    (Functor.pi' (fun i => (Pi.eval _ (some i))))
  inverse := Functor.pi' (fun i => match i with
    | none => Prod.fst _ _
    | some i => Prod.snd _ _ ⋙ (Pi.eval _ i))
  unitIso := NatIso.pi' (fun i => match i with
    | none => Iso.refl _
    | some _ => Iso.refl 

中文:
定义 依赖函数类型.optionEquivalence
  签名: (C' : 选项类型 J -> 类型u₁) [对任意 i, 范畴.{v₁} (C' i)]
  定义体: Functor.prod' (Pi.eval C' none)
    (Functor.pi' (fun i => (Pi.eval _ (some i))))
  inverse := Functor.pi' (fun i => match i with
    | none => Prod.fst _ _
    | some i => Prod.snd _ _ ⋙ (Pi.eval _ i))
  unitIso := NatIso.pi' (fun i => match i with
    | none => Iso.refl _
    | some _ => Iso.refl 

Depends on / 依赖: Functor, Functor.prod, Pi.eval
-/
def Pi.optionEquivalence (C' : Option J -> Type u₁) [forall i, Category.{v₁} (C' i)] :
    (forall i, C' i) ≌ C' none × (forall (j : J), C' (some j)) where
  functor := Functor.prod' (Pi.eval C' none)
    (Functor.pi' (fun i => (Pi.eval _ (some i))))
  inverse := Functor.pi' (fun i => match i with
    | none => Prod.fst _ _
    | some i => Prod.snd _ _ ⋙ (Pi.eval _ i))
  unitIso := NatIso.pi' (fun i => match i with
    | none => Iso.refl _
    | some _ => Iso.refl _)
  counitIso := by exact Iso.refl _

namespace Equivalence

variable {C}
variable {D : I -> Type u₂} [forall i, Category.{v₂} (D i)]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Assemble an `I`-indexed family of equivalences of categories
into a single equivalence. -/
@[simps]
/--
Definition of `pi` / `pi` 的定义

English:
definition pi
  signature: (E : forall i, C i ≌ D i)
  body: Functor.pi (fun i => (E i).functor)
  inverse := Functor.pi (fun i => (E i).inverse)
  unitIso := NatIso.pi (fun i => (E i).unitIso)
  counitIso := NatIso.pi (fun i => (E i).counitIso)

中文:
定义 pi
  签名: (E : 对任意 i, C i ≌ D i)
  定义体: Functor.pi (fun i => (E i).functor)
  inverse := Functor.pi (fun i => (E i).inverse)
  unitIso := NatIso.pi (fun i => (E i).unitIso)
  counitIso := NatIso.pi (fun i => (E i).counitIso)

Depends on / 依赖: Functor, Functor.pi, functor
-/
def pi (E : forall i, C i ≌ D i) : (forall i, C i) ≌ (forall i, D i) where
  functor := Functor.pi (fun i => (E i).functor)
  inverse := Functor.pi (fun i => (E i).inverse)
  unitIso := NatIso.pi (fun i => (E i).unitIso)
  counitIso := NatIso.pi (fun i => (E i).counitIso)

instance (F : forall i, C i ⥤ D i) [forall i, (F i).IsEquivalence] :
    (Functor.pi F).IsEquivalence :=
  (pi (fun i => (F i).asEquivalence)).isEquivalence_functor

end Equivalence

end CategoryTheory
