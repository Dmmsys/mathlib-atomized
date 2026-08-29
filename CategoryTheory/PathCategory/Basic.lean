/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Robin Carlier
-/
module

public import Mathlib.CategoryTheory.Quotient

/-!
# The category paths on a quiver.

When `C` is a quiver, `paths C` is the category of paths.

## When the quiver is itself a category
We provide `path_composition : paths C ⥤ C`.

We check that the quotient of the path category of a category by the canonical relation
(paths are related if they compose to the same path) is equivalent to the original category.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

section

/--
Definition of `Paths` / `Paths` 的定义

English:
definition Paths
  signature: (V : Type u₁)
  body: V

中文:
定义 Paths
  签名: (V : 类型u₁)
  定义体: V
-/
def Paths (V : Type u₁) : Type u₁ := V

instance (V : Type u₁) [Inhabited V] : Inhabited (Paths V) := ⟨(default : V)⟩
instance (V : Type u₁) [Unique V] : Unique (Paths V) where
  uniq _ := Subsingleton.elim (α := V) _ _

variable (V : Type u₁) [Quiver.{v₁} V]

namespace Paths

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `categoryPaths` / 实例 `categoryPaths`

English:
instance categoryPaths
  signature: : Category.{max u₁ v₁} (Paths V) where
  body: fun X Y : V => Quiver.Path X Y
  id _ := Quiver.Path.nil
  comp f g := Quiver.Path.comp f g

中文:
实例 categoryPaths
  签名: : 范畴.{最大值 u₁ v₁} (Paths V) where
  定义体: fun X Y : V => Quiver.Path X Y
  id _ := Quiver.Path.nil
  comp f g := Quiver.Path.comp f g

Depends on / 依赖: Quiver, Quiver.Path
-/
instance categoryPaths : Category.{max u₁ v₁} (Paths V) where
  Hom := fun X Y : V => Quiver.Path X Y
  id _ := Quiver.Path.nil
  comp f g := Quiver.Path.comp f g

set_option backward.isDefEq.respectTransparency.types false in
/-- The inclusion of a quiver `V` into its path category, as a prefunctor.
-/
@[simps]
/--
Definition of `of` / `of` 的定义

English:
definition of
  signature: : V ⥤q Paths V where
  body: X
  map f := f.toPath

中文:
定义 of
  签名: : V ⥤q Paths V where
  定义体: X
  map f := f.toPath
-/
def of : V ⥤q Paths V where
  obj X := X
  map f := f.toPath

variable {V}

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `induction_fixed_source` / 引理 `induction_fixed_source`

English:
lemma induction_fixed_source
  statement: {a : Paths V} (P : forall {b : Paths V}, (a ⟶ b) -> Prop)
  proof: by
  intro _ f
  induction f with
  | nil => exact id
  | cons _ w h => exact comp _ w h

中文:
引理 induction_fixed_source
  结论: {a : Paths V} (P : 对任意 {b : Paths V}, (a ⟶ b) -> 命题)
  证明: by
  intro _ f
  induction f with
  | nil => exact id
  | cons _ w h => exact comp _ w h
-/
lemma induction_fixed_source {a : Paths V} (P : forall {b : Paths V}, (a ⟶ b) -> Prop)
    (id : P (𝟙 a))
    (comp : forall {u v : V} (p : a ⟶ (of V).obj u) (q : u ⟶ v), P p -> P (p ≫ (of V).map q)) :
    forall {b : Paths V} (f : a ⟶ b), P f := by
  intro _ f
  induction f with
  | nil => exact id
  | cons _ w h => exact comp _ w h

set_option backward.isDefEq.respectTransparency false in
/--
lemma `induction_fixed_target` / 引理 `induction_fixed_target`

English:
lemma induction_fixed_target
  statement: {b : Paths V} (P : forall {a : Paths V}, (a ⟶ b) -> Prop)
  proof: by
  intro a f
  generalize h : f.length = k
  induction k generalizing f a with
  | zero => cases f with
    | nil => exact id
    | cons _ _ => simp at h
  | succ k h' =>
    obtain ⟨c, f, q, hq, rfl⟩ := f.eq_toPath_comp_of_length_eq_succ h
    exact comp _ _ (h' _ hq)

中文:
引理 induction_fixed_target
  结论: {b : Paths V} (P : 对任意 {a : Paths V}, (a ⟶ b) -> 命题)
  证明: by
  intro a f
  generalize h : f.length = k
  induction k generalizing f a with
  | zero => cases f with
    | nil => exact id
    | cons _ _ => simp at h
  | succ k h' =>
    obtain ⟨c, f, q, hq, rfl⟩ := f.eq_toPath_comp_of_length_eq_succ h
    exact comp _ _ (h' _ hq)

Depends on / 依赖: eq_toPath_comp_of_length_eq_succ, f.eq_toPath_comp_of_length_eq_succ, f.length, generalize, generalizing, length
-/
lemma induction_fixed_target {b : Paths V} (P : forall {a : Paths V}, (a ⟶ b) -> Prop)
    (id : P (𝟙 b))
    (comp : forall {u v : V} (p : (of V).obj v ⟶ b) (q : u ⟶ v), P p -> P ((of V).map q ≫ p)) :
    forall {a : Paths V} (f : a ⟶ b), P f := by
  intro a f
  generalize h : f.length = k
  induction k generalizing f a with
  | zero => cases f with
    | nil => exact id
    | cons _ _ => simp at h
  | succ k h' =>
    obtain ⟨c, f, q, hq, rfl⟩ := f.eq_toPath_comp_of_length_eq_succ h
    exact comp _ _ (h' _ hq)

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `induction` / 引理 `induction`

English:
lemma induction
  statement: (P : forall {a b : Paths V}, (a ⟶ b) -> Prop)
  proof: fun {_} => induction_fixed_source _ id comp

中文:
引理 induction
  结论: (P : 对任意 {a b : Paths V}, (a ⟶ b) -> 命题)
  证明: fun {_} => induction_fixed_source _ id comp

Depends on / 依赖: induction_fixed_source
-/
lemma induction (P : forall {a b : Paths V}, (a ⟶ b) -> Prop)
    (id : forall {v : V}, P (𝟙 ((of V).obj v)))
    (comp : forall {u v w : V}
      (p : (of V).obj u ⟶ (of V).obj v) (q : v ⟶ w), P p -> P (p ≫ (of V).map q)) :
    forall {a b : Paths V} (f : a ⟶ b), P f :=
  fun {_} => induction_fixed_source _ id comp

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `induction'` / 引理 `induction'`

English:
lemma induction'
  statement: (P : forall {a b : Paths V}, (a ⟶ b) -> Prop)
  proof: by
  intro a b
  revert a
  exact induction_fixed_target (P := fun f => P f) id (fun _ _ => comp _ _)

中文:
引理 induction'
  结论: (P : 对任意 {a b : Paths V}, (a ⟶ b) -> 命题)
  证明: by
  intro a b
  revert a
  exact induction_fixed_target (P := fun f => P f) id (fun _ _ => comp _ _)

Depends on / 依赖: induction_fixed_target, revert
-/
lemma induction' (P : forall {a b : Paths V}, (a ⟶ b) -> Prop)
    (id : forall {v : V}, P (𝟙 ((of V).obj v)))
    (comp : forall {u v w : V} (p : u ⟶ v)
      (q : (of V).obj v ⟶ (of V).obj w), P q -> P ((of V).map p ≫ q)) :
    forall {a b : Paths V} (f : a ⟶ b), P f := by
  intro a b
  revert a
  exact induction_fixed_target (P := fun f => P f) id (fun _ _ => comp _ _)

attribute [local ext (iff := false)] Functor.ext

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: {C} [Category* C] (φ : V ⥤q C)
  body: φ.obj
  map {X} {Y} f :=
    @Quiver.Path.rec V _ X (fun Y _ => φ.obj X ⟶ φ.obj Y) (𝟙 <| φ.obj X)
      (fun _ f ihp => ihp ≫ φ.map f) Y f
  map_id _ := rfl
  map_comp f g := by
    induction g with
    | nil =>
      rw [Category.comp_id]
      rfl
    | cons g' p ih =>
      have : f ≫ Quiver.Path

中文:
定义 lift
  签名: {C} [范畴* C] (φ : V ⥤q C)
  定义体: φ.obj
  map {X} {Y} f :=
    @Quiver.Path.rec V _ X (fun Y _ => φ.obj X ⟶ φ.obj Y) (𝟙 <| φ.obj X)
      (fun _ f ihp => ihp ≫ φ.map f) Y f
  map_id _ := rfl
  map_comp f g := by
    induction g with
    | nil =>
      rw [Category.comp_id]
      rfl
    | cons g' p ih =>
      have : f ≫ Quiver.Path
-/
def lift {C} [Category* C] (φ : V ⥤q C) : Paths V ⥤ C where
  obj := φ.obj
  map {X} {Y} f :=
    @Quiver.Path.rec V _ X (fun Y _ => φ.obj X ⟶ φ.obj Y) (𝟙 <| φ.obj X)
      (fun _ f ihp => ihp ≫ φ.map f) Y f
  map_id _ := rfl
  map_comp f g := by
    induction g with
    | nil =>
      rw [Category.comp_id]
      rfl
    | cons g' p ih =>
      have : f ≫ Quiver.Path.cons g' p = (f ≫ g').cons p := by apply Quiver.Path.comp_cons
      rw [this]
      simp only at ih ⊢
      rw [ih]; rw [Category.assoc]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `lift_nil` / 定理 `lift_nil`

English:
theorem lift_nil
  given: {C} [Category* C] (φ : V ⥤q C) (X : V)
  proof: rfl

中文:
定理 lift_nil
  条件: {C} [范畴* C] (φ : V ⥤q C) (X : V)
  证明: rfl
-/
theorem lift_nil {C} [Category* C] (φ : V ⥤q C) (X : V) :
    (lift φ).map Quiver.Path.nil = 𝟙 (φ.obj X) := rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `lift_cons` / 定理 `lift_cons`

English:
theorem lift_cons
  given: {C} [Category* C] (φ : V ⥤q C) {X Y Z : V} (p : Quiver.Path X Y) (f : Y ⟶ Z)
  proof: rfl

中文:
定理 lift_cons
  条件: {C} [范畴* C] (φ : V ⥤q C) {X Y Z : V} (p : 箭图.道路 X Y) (f : Y ⟶ Z)
  证明: rfl
-/
theorem lift_cons {C} [Category* C] (φ : V ⥤q C) {X Y Z : V} (p : Quiver.Path X Y) (f : Y ⟶ Z) :
    (lift φ).map (p.cons f) = (lift φ).map p ≫ φ.map f := rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `lift_toPath` / 定理 `lift_toPath`

English:
theorem lift_toPath
  given: {C} [Category* C] (φ : V ⥤q C) {X Y : V} (f : X ⟶ Y)
  proof: by
  dsimp [Quiver.Hom.toPath, lift]
  simp

中文:
定理 lift_toPath
  条件: {C} [范畴* C] (φ : V ⥤q C) {X Y : V} (f : X ⟶ Y)
  证明: by
  dsimp [Quiver.Hom.toPath, lift]
  simp

Depends on / 依赖: Quiver, Quiver.Hom.toPath, toPath
-/
theorem lift_toPath {C} [Category* C] (φ : V ⥤q C) {X Y : V} (f : X ⟶ Y) :
    (lift φ).map f.toPath = φ.map f := by
  dsimp [Quiver.Hom.toPath, lift]
  simp

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
theorem `lift_spec` / 定理 `lift_spec`

English:
theorem lift_spec
  given: {C} [Category* C] (φ : V ⥤q C)
  statement: of V ⋙q (lift φ).toPrefunctor = φ
  proof: by
  fapply Prefunctor.ext
  · rintro X
    rfl
  · rintro X Y f
    rcases φ with ⟨φo, φm⟩
    dsimp [lift, Quiver.Hom.toPath]
    simp

中文:
定理 lift_spec
  条件: {C} [范畴* C] (φ : V ⥤q C)
  结论: of V ⋙q (lift φ).toPrefunctor = φ
  证明: by
  fapply Prefunctor.ext
  · rintro X
    rfl
  · rintro X Y f
    rcases φ with ⟨φo, φm⟩
    dsimp [lift, Quiver.Hom.toPath]
    simp

Depends on / 依赖: Prefunctor, Prefunctor.ext, Quiver, Quiver.Hom.toPath, fapply, toPath
-/
theorem lift_spec {C} [Category* C] (φ : V ⥤q C) : of V ⋙q (lift φ).toPrefunctor = φ := by
  fapply Prefunctor.ext
  · rintro X
    rfl
  · rintro X Y f
    rcases φ with ⟨φo, φm⟩
    dsimp [lift, Quiver.Hom.toPath]
    simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `lift_unique` / 定理 `lift_unique`

English:
theorem lift_unique
  statement: {C} [Category* C] (φ : V ⥤q C) (Φ : Paths V ⥤ C)
  proof: by
  subst_vars
  fapply Functor.ext
  · rintro X
    rfl
  · rintro X Y f
    dsimp [lift]
    induction f with
    | nil =>
      simp only [Category.comp_id]
      apply Functor.map_id
    | cons p f' ih =>
      simp only [Category.comp_id, Category.id_comp] at ih ⊢
      -- Porting note: Had to

中文:
定理 lift_unique
  结论: {C} [范畴* C] (φ : V ⥤q C) (Φ : Paths V ⥤ C)
  证明: by
  subst_vars
  fapply Functor.ext
  · rintro X
    rfl
  · rintro X Y f
    dsimp [lift]
    induction f with
    | nil =>
      simp only [Category.comp_id]
      apply Functor.map_id
    | cons p f' ih =>
      simp only [Category.comp_id, Category.id_comp] at ih ⊢
      -- Porting note: Had to

Depends on / 依赖: Category, Category.comp_id, Category.id_comp, Functor, Functor.ext, Functor.map_id, comp_id, fapply, id_comp, map_id
-/
theorem lift_unique {C} [Category* C] (φ : V ⥤q C) (Φ : Paths V ⥤ C)
    (hΦ : of V ⋙q Φ.toPrefunctor = φ) : Φ = lift φ := by
  subst_vars
  fapply Functor.ext
  · rintro X
    rfl
  · rintro X Y f
    dsimp [lift]
    induction f with
    | nil =>
      simp only [Category.comp_id]
      apply Functor.map_id
    | cons p f' ih =>
      simp only [Category.comp_id, Category.id_comp] at ih ⊢
      -- Porting note: Had to do substitute `p.cons f'` and `f'.toPath` by their fully qualified
      -- versions in this `have` clause (elsewhere too).
      have : Φ.map (Quiver.Path.cons p f') = Φ.map p ≫ Φ.map (Quiver.Hom.toPath f') := by
        convert! Functor.map_comp Φ p (Quiver.Hom.toPath f')
      rw [this]; rw [ih]

set_option backward.isDefEq.respectTransparency.types false in
/-- Two functors out of a path category are equal when they agree on singleton paths. -/
@[ext (iff := false)]
/--
theorem `ext_functor` / 定理 `ext_functor`

English:
theorem ext_functor
  statement: {C} [Category* C] {F G : Paths V ⥤ C} (h_obj : F.obj = G.obj)
  proof: by
  fapply Functor.ext
  · intro X
    rw [h_obj]
  · intro X Y f
    induction f with
    | nil => erw [F.map_id, G.map_id, Category.id_comp, eqToHom_trans, eqToHom_refl]
    | cons g e ih =>
      erw [F.map_comp g (Quiver.Hom.toPath e), G.map_comp g (Quiver.Hom.toPath e), ih, h]
      simp only 

中文:
定理 ext_functor
  结论: {C} [范畴* C] {F G : Paths V ⥤ C} (h_obj : F.obj = G.obj)
  证明: by
  fapply Functor.ext
  · intro X
    rw [h_obj]
  · intro X Y f
    induction f with
    | nil => erw [F.map_id, G.map_id, Category.id_comp, eqToHom_trans, eqToHom_refl]
    | cons g e ih =>
      erw [F.map_comp g (Quiver.Hom.toPath e), G.map_comp g (Quiver.Hom.toPath e), ih, h]
      simp only 

Depends on / 依赖: Category, Category.assoc, Category.id_comp, F.map_comp, F.map_id, Functor, Functor.ext, G.map_comp, G.map_id, Quiver, Quiver.Hom.toPath, eqToHom_refl, eqToHom_trans, eqToHom_trans_assoc, fapply, h_obj, id_comp, map_comp, map_id, toPath
-/
theorem ext_functor {C} [Category* C] {F G : Paths V ⥤ C} (h_obj : F.obj = G.obj)
    (h : forall (a b : V) (e : a ⟶ b), F.map e.toPath =
        eqToHom (congr_fun h_obj a) ≫ G.map e.toPath ≫ eqToHom (congr_fun h_obj.symm b)) :
    F = G := by
  fapply Functor.ext
  · intro X
    rw [h_obj]
  · intro X Y f
    induction f with
    | nil => erw [F.map_id, G.map_id, Category.id_comp, eqToHom_trans, eqToHom_refl]
    | cons g e ih =>
      erw [F.map_comp g (Quiver.Hom.toPath e), G.map_comp g (Quiver.Hom.toPath e), ih, h]
      simp only [Category.id_comp, eqToHom_refl, eqToHom_trans_assoc, Category.assoc]

end Paths

variable (W : Type u₂) [Quiver.{v₂} W]

-- A restatement of `Prefunctor.mapPath_comp` using `f ≫ g` instead of `f.comp g`.
set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `Prefunctor.mapPath_comp'` / 定理 `Prefunctor.mapPath_comp'`

English:
theorem Prefunctor.mapPath_comp'
  given: (F : V ⥤q W) {X Y Z : Paths V} (f : X ⟶ Y) (g : Y ⟶ Z)
  proof: Prefunctor.mapPath_comp _ _ _

中文:
定理 预函子.mapPath_comp'
  条件: (F : V ⥤q W) {X Y Z : Paths V} (f : X ⟶ Y) (g : Y ⟶ Z)
  证明: Prefunctor.mapPath_comp _ _ _

Depends on / 依赖: Prefunctor, Prefunctor.mapPath_comp, mapPath_comp
-/
theorem Prefunctor.mapPath_comp' (F : V ⥤q W) {X Y Z : Paths V} (f : X ⟶ Y) (g : Y ⟶ Z) :
    F.mapPath (f ≫ g) = (F.mapPath f).comp (F.mapPath g) :=
  Prefunctor.mapPath_comp _ _ _

end

section

variable {C : Type u₁} [Category.{v₁} C]

open Quiver

/-- A path in a category can be composed to a single morphism. -/
@[simp]
/--
Definition of `composePath` / `composePath` 的定义

English:
definition composePath
  signature: {X : C}

中文:
定义 composePath
  签名: {X : C}
-/
def composePath {X : C} : forall {Y : C} (_ : Path X Y), X ⟶ Y
  | _, .nil => 𝟙 X
  | _, .cons p e => composePath p ≫ e

-- This lemma was marked as `@[simp]` but it is generated by `@[simp]` on `composePath`.
/--
lemma `composePath_nil` / 引理 `composePath_nil`

English:
lemma composePath_nil
  given: {X : C}
  statement: composePath (Path.nil : Path X X) = 𝟙 X
  proof: rfl

中文:
引理 composePath_nil
  条件: {X : C}
  结论: composePath (道路.nil : 道路 X X) = 𝟙 X
  证明: rfl
-/
lemma composePath_nil {X : C} : composePath (Path.nil : Path X X) = 𝟙 X := rfl

-- This lemma was marked as `@[simp]` but it is generated by `@[simp]` on `composePath`.
/--
lemma `composePath_cons` / 引理 `composePath_cons`

English:
lemma composePath_cons
  given: {X Y Z : C} (p : Path X Y) (e : Y ⟶ Z)
  proof: rfl

@[simp]

中文:
引理 composePath_cons
  条件: {X Y Z : C} (p : 道路 X Y) (e : Y ⟶ Z)
  证明: rfl

@[simp]
-/
lemma composePath_cons {X Y Z : C} (p : Path X Y) (e : Y ⟶ Z) :
    composePath (p.cons e) = composePath p ≫ e := rfl

@[simp]
/--
theorem `composePath_toPath` / 定理 `composePath_toPath`

English:
theorem composePath_toPath
  given: {X Y : C} (f : X ⟶ Y)
  statement: composePath f.toPath = f
  proof: Category.id_comp _

@[simp]

中文:
定理 composePath_toPath
  条件: {X Y : C} (f : X ⟶ Y)
  结论: composePath f.toPath = f
  证明: Category.id_comp _

@[simp]

Depends on / 依赖: Category, Category.id_comp, id_comp
-/
theorem composePath_toPath {X Y : C} (f : X ⟶ Y) : composePath f.toPath = f := Category.id_comp _

@[simp]
/--
theorem `composePath_comp` / 定理 `composePath_comp`

English:
theorem composePath_comp
  given: {X Y Z : C} (f : Path X Y) (g : Path Y Z)
  proof: by
  induction g with
  | nil => simp
  | cons g e ih => simp [ih]

中文:
定理 composePath_comp
  条件: {X Y Z : C} (f : 道路 X Y) (g : 道路 Y Z)
  证明: by
  induction g with
  | nil => simp
  | cons g e ih => simp [ih]
-/
theorem composePath_comp {X Y Z : C} (f : Path X Y) (g : Path Y Z) :
    composePath (f.comp g) = composePath f ≫ composePath g := by
  induction g with
  | nil => simp
  | cons g e ih => simp [ih]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
-- TODO get rid of `(id X : C)` somehow?
/--
theorem `composePath_id` / 定理 `composePath_id`

English:
theorem composePath_id
  given: {X : Paths C}
  statement: composePath (𝟙 X) = 𝟙 (show C from X)
  proof: rfl

中文:
定理 composePath_id
  条件: {X : Paths C}
  结论: composePath (𝟙 X) = 𝟙 (show C from X)
  证明: rfl
-/
theorem composePath_id {X : Paths C} : composePath (𝟙 X) = 𝟙 (show C from X) := rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `composePath_comp'` / 定理 `composePath_comp'`

English:
theorem composePath_comp'
  given: {X Y Z : Paths C} (f : X ⟶ Y) (g : Y ⟶ Z)
  proof: composePath_comp f g

中文:
定理 composePath_comp'
  条件: {X Y Z : Paths C} (f : X ⟶ Y) (g : Y ⟶ Z)
  证明: composePath_comp f g

Depends on / 依赖: composePath_comp
-/
theorem composePath_comp' {X Y Z : Paths C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    composePath (f ≫ g) = composePath f ≫ composePath g :=
  composePath_comp f g

variable (C)

set_option backward.isDefEq.respectTransparency.types false in
/-- Composition of paths as functor from the path category of a category to the category. -/
@[simps]
/--
Definition of `pathComposition` / `pathComposition` 的定义

English:
definition pathComposition
  signature: : Paths C ⥤ C where
  body: X
  map f := composePath f

中文:
定义 pathComposition
  签名: : Paths C ⥤ C where
  定义体: X
  map f := composePath f
-/
def pathComposition : Paths C ⥤ C where
  obj X := X
  map f := composePath f

-- TODO: This, and what follows, should be generalized to
-- the `HomRel` for the kernel of any functor.
-- Indeed, this should be part of an equivalence between congruence relations on a category `C`
-- and full, essentially surjective functors out of `C`.
/-- The canonical relation on the path category of a category:
two paths are related if they compose to the same morphism. -/
@[simp]
/--
Definition of `pathsHomRel` / `pathsHomRel` 的定义

English:
definition pathsHomRel
  signature: : HomRel (Paths C)
  body: fun _ _ p q =>
  (pathComposition C).map p = (pathComposition C).map q

#adaptation_note /-- As of nightly-2026-04-29, the simpNF linter is failing here.
Assistance investigating this would be appreciated. -/

中文:
定义 pathsHomRel
  签名: : HomRel (Paths C)
  定义体: fun _ _ p q =>
  (pathComposition C).map p = (pathComposition C).map q

#adaptation_note /-- As of nightly-2026-04-29, the simpNF linter is failing here.
Assistance investigating this would be appreciated. -/
-/
def pathsHomRel : HomRel (Paths C) := fun _ _ p q =>
  (pathComposition C).map p = (pathComposition C).map q

#adaptation_note /-- As of nightly-2026-04-29, the simpNF linter is failing here.
Assistance investigating this would be appreciated. -/
attribute [nolint simpNF] pathsHomRel.eq_1

set_option backward.isDefEq.respectTransparency.types false in
/-- The functor from a category to the canonical quotient of its path category. -/
@[simps]
/--
Definition of `toQuotientPaths` / `toQuotientPaths` 的定义

English:
definition toQuotientPaths
  signature: : C ⥤ Quotient (pathsHomRel C) where
  body: Quotient.mk X
  map f := Quot.mk _ f.toPath
  map_id X := Quot.sound (HomRel.CompClosure.of (by simp))
  map_comp f g := Quot.sound (HomRel.CompClosure.of (by simp))

中文:
定义 toQuotientPaths
  签名: : C ⥤ 商 (pathsHomRel C) where
  定义体: Quotient.mk X
  map f := Quot.mk _ f.toPath
  map_id X := Quot.sound (HomRel.CompClosure.of (by simp))
  map_comp f g := Quot.sound (HomRel.CompClosure.of (by simp))

Depends on / 依赖: Quotient, Quotient.mk
-/
def toQuotientPaths : C ⥤ Quotient (pathsHomRel C) where
  obj X := Quotient.mk X
  map f := Quot.mk _ f.toPath
  map_id X := Quot.sound (HomRel.CompClosure.of (by simp))
  map_comp f g := Quot.sound (HomRel.CompClosure.of (by simp))

set_option backward.isDefEq.respectTransparency.types false in
/-- The functor from the canonical quotient of a path category of a category
to the original category. -/
@[simps!]
/--
Definition of `quotientPathsTo` / `quotientPathsTo` 的定义

English:
definition quotientPathsTo
  signature: : Quotient (pathsHomRel C) ⥤ C
  body: Quotient.lift _ (pathComposition C) fun _ _ _ _ w => w

中文:
定义 quotientPathsTo
  签名: : 商 (pathsHomRel C) ⥤ C
  定义体: Quotient.lift _ (pathComposition C) fun _ _ _ _ w => w

Depends on / 依赖: Quotient, Quotient.lift, pathComposition
-/
def quotientPathsTo : Quotient (pathsHomRel C) ⥤ C :=
  Quotient.lift _ (pathComposition C) fun _ _ _ _ w => w

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `quotientPathsEquiv` / `quotientPathsEquiv` 的定义

English:
definition quotientPathsEquiv
  signature: : Quotient (pathsHomRel C) ≌ C where
  body: quotientPathsTo C
  inverse := toQuotientPaths C
  unitIso :=
    NatIso.ofComponents
      (fun X => by cases X; rfl)
      (Quot.ind fun f => by exact Quot.sound (HomRel.CompClosure.of (by simp)))
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _) (fun f => by simp)
  functor_unitIso_comp X 

中文:
定义 quotientPathsEquiv
  签名: : 商 (pathsHomRel C) ≌ C where
  定义体: quotientPathsTo C
  inverse := toQuotientPaths C
  unitIso :=
    NatIso.ofComponents
      (fun X => by cases X; rfl)
      (Quot.ind fun f => by exact Quot.sound (HomRel.CompClosure.of (by simp)))
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _) (fun f => by simp)
  functor_unitIso_comp X 

Depends on / 依赖: quotientPathsTo
-/
def quotientPathsEquiv : Quotient (pathsHomRel C) ≌ C where
  functor := quotientPathsTo C
  inverse := toQuotientPaths C
  unitIso :=
    NatIso.ofComponents
      (fun X => by cases X; rfl)
      (Quot.ind fun f => by exact Quot.sound (HomRel.CompClosure.of (by simp)))
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _) (fun f => by simp)
  functor_unitIso_comp X := by
    cases X
    simp only [Functor.id_obj,
               quotientPathsTo_obj, Functor.comp_obj, toQuotientPaths_obj_as,
               NatIso.ofComponents_hom_app, Iso.refl_hom, quotientPathsTo_map, Category.comp_id]
    rfl

end

end CategoryTheory
