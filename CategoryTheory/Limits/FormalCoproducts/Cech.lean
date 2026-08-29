/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.CategoryTheory.Limits.FormalCoproducts.Basic

/-!
# The Cech object for formal coproducts

Let `C` be a category that has finite products. In this file, we define a
functor `cechFunctor : FormalCoproduct C ⥤ SimplicialObject (FormalCoproduct C)`
which sends a formal coproduct of objects `U j` (for `j : ι`) to the simplicial object
which sends `⦋n⦌` to the formal coproduct, indexed by `i : Fin (n + 1) → ι`,
of the products of the objects `U (i a)` for all `a : Fin (n + 1)`.

-/

@[expose] public section

universe w t v u

namespace CategoryTheory.Limits.FormalCoproduct

variable {C : Type u} [Category.{v} C]

/-- Given `U : FormalCoproduct C` and a type `α`, this is the formal coproduct
indexed by all `i : α → U.I` of the products of the objects `U.obj (i a)`
for all `a : α`. -/
@[simps]
/--
Definition of `power` / `power` 的定义

English:
definition power
  signature: (U : FormalCoproduct.{w} C) (α : Type t)
  body: α -> U.I
  obj i := ∏ᶜ (U.obj ∘ i)

中文:
定义 power
  签名: (U : 形式余积.{w} C) (α : 类型 t)
  定义体: α -> U.I
  obj i := ∏ᶜ (U.obj ∘ i)
-/
noncomputable def power (U : FormalCoproduct.{w} C) (α : Type t)
    [HasProductsOfShape α C] : FormalCoproduct.{max w t} C where
  I := α -> U.I
  obj i := ∏ᶜ (U.obj ∘ i)

section

variable (U : FormalCoproduct.{w} C) (α : Type) [HasProductsOfShape α C]

variable {α} in
/-- The projection `U.power α ⟶ U` for each `a : α`. -/
@[simps]
/--
Definition of `powerπ` / `powerπ` 的定义

English:
definition powerπ
  signature: (a : α)
  body: i a
  φ _ := Pi.π _ a

中文:
定义 powerπ
  签名: (a : α)
  定义体: i a
  φ _ := Pi.π _ a
-/
noncomputable def powerπ (a : α) : U.power α ⟶ U where
  f i := i a
  φ _ := Pi.π _ a

/--
Definition of `powerFan` / `powerFan` 的定义

English:
abbreviation powerFan
  signature: :
  body: Fan.mk (U.power α) U.powerπ

中文:
缩写 powerFan
  签名: :
  定义体: Fan.mk (U.power α) U.powerπ

Depends on / 依赖: Fan.mk, U.power
-/
noncomputable abbrev powerFan :
    Fan (fun (_ : α) => U) :=
  Fan.mk (U.power α) U.powerπ

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `isLimitPowerFan` / `isLimitPowerFan` 的定义

English:
definition isLimitPowerFan
  signature: : IsLimit (U.powerFan α)
  body: Fan.IsLimit.mk _
    (fun s =>
      { f i a := (s.proj a).f i
        φ i := Pi.lift (fun a => (s.proj a).φ i) })
    (fun _ _ => by ext <;> simp)
    (fun s m hm => by
      obtain ⟨f, φ⟩ := m
      obtain rfl : f = fun i a => (s.proj a).f i := by
        ext i
        dsimp
        ext a
        

中文:
定义 isLimitPowerFan
  签名: : 是极限 (U.powerFan α)
  定义体: Fan.IsLimit.mk _
    (fun s =>
      { f i a := (s.proj a).f i
        φ i := Pi.lift (fun a => (s.proj a).φ i) })
    (fun _ _ => by ext <;> simp)
    (fun s m hm => by
      obtain ⟨f, φ⟩ := m
      obtain rfl : f = fun i a => (s.proj a).f i := by
        ext i
        dsimp
        ext a
        

Depends on / 依赖: Fan.IsLimit.mk, FormalCoproduct, FormalCoproduct.Hom.f, IsLimit, Pi.lift, congr_arg, congr_fun, hom_ext_iff, s.proj, specialize
-/
noncomputable def isLimitPowerFan : IsLimit (U.powerFan α) :=
  Fan.IsLimit.mk _
    (fun s =>
      { f i a := (s.proj a).f i
        φ i := Pi.lift (fun a => (s.proj a).φ i) })
    (fun _ _ => by ext <;> simp)
    (fun s m hm => by
      obtain ⟨f, φ⟩ := m
      obtain rfl : f = fun i a => (s.proj a).f i := by
        ext i
        dsimp
        ext a
        exact congr_fun (congr_arg FormalCoproduct.Hom.f (hm a)) i
      ext i
      · rfl
      · dsimp
        ext a
        specialize hm a
        rw [hom_ext_iff] at hm
        obtain ⟨_, hm⟩ := hm
        simpa using hm i)

end

/-- For any morphism `f : U ⟶ V` in `FormalCoproduct C` and a type `α`,
this is the induced map `U.power α ⟶ V.power α`. -/
@[simps -fullyApplied]
/--
Definition of `powerMap` / `powerMap` 的定义

English:
definition powerMap
  signature: {U V : FormalCoproduct.{w} C} (f : U ⟶ V) (α : Type t)
  body: f.f ∘ i
  φ i := Pi.map (fun a => f.φ (i a))

中文:
定义 powerMap
  签名: {U V : 形式余积.{w} C} (f : U ⟶ V) (α : 类型 t)
  定义体: f.f ∘ i
  φ i := Pi.map (fun a => f.φ (i a))
-/
noncomputable def powerMap {U V : FormalCoproduct.{w} C} (f : U ⟶ V) (α : Type t)
    [HasProductsOfShape α C] :
    U.power α ⟶ V.power α where
  f i := f.f ∘ i
  φ i := Pi.map (fun a => f.φ (i a))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `powerMap_id` / 引理 `powerMap_id`

English:
lemma powerMap_id
  given: (U : FormalCoproduct.{w} C) (α : Type t) [HasProductsOfShape α C]
  proof: by
  cat_disch

中文:
引理 powerMap_id
  条件: (U : 形式余积.{w} C) (α : 类型 t) [HasProductsOfShape α C]
  证明: by
  cat_disch

Depends on / 依赖: cat_disch
-/
lemma powerMap_id (U : FormalCoproduct.{w} C) (α : Type t) [HasProductsOfShape α C] :
    powerMap (𝟙 U) α = 𝟙 _ := by
  cat_disch

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `powerMap_comp` / 引理 `powerMap_comp`

English:
lemma powerMap_comp
  statement: {U V W : FormalCoproduct.{w} C} (f : U ⟶ V) (g : V ⟶ W) (α : Type t)
  proof: by
  ext
  · cat_disch
  · dsimp
    ext
    simp only [Category.comp_id, Category.assoc, Pi.map_π, Function.comp_apply,
      Pi.map_π_assoc]
    apply Pi.map_π

中文:
引理 powerMap_comp
  结论: {U V W : 形式余积.{w} C} (f : U ⟶ V) (g : V ⟶ W) (α : 类型 t)
  证明: by
  ext
  · cat_disch
  · dsimp
    ext
    simp only [Category.comp_id, Category.assoc, Pi.map_π, Function.comp_apply,
      Pi.map_π_assoc]
    apply Pi.map_π

Depends on / 依赖: Category, Category.assoc, Category.comp_id, Function, Function.comp_apply, Pi.map_, cat_disch, comp_apply, comp_id
-/
lemma powerMap_comp {U V W : FormalCoproduct.{w} C} (f : U ⟶ V) (g : V ⟶ W) (α : Type t)
    [HasProductsOfShape α C] :
    powerMap (f ≫ g) α = powerMap f α ≫ powerMap g α := by
  ext
  · cat_disch
  · dsimp
    ext
    simp only [Category.comp_id, Category.assoc, Pi.map_π, Function.comp_apply,
      Pi.map_π_assoc]
    apply Pi.map_π

attribute [local simp] powerMap_comp

/-- Given a type `α`, this is the functor `FormalCoproduct C ⥤ FormalCoproduct C`
which sends `U` to `U.power α`. -/
@[simps]
/--
Definition of `powerFunctor` / `powerFunctor` 的定义

English:
definition powerFunctor
  signature: (α : Type t) [HasProductsOfShape α C]
  body: U.power α
  map f := powerMap f α

中文:
定义 powerFunctor
  签名: (α : 类型 t) [HasProductsOfShape α C]
  定义体: U.power α
  map f := powerMap f α

Depends on / 依赖: U.power
-/
noncomputable def powerFunctor (α : Type t) [HasProductsOfShape α C] :
    FormalCoproduct.{w} C ⥤ FormalCoproduct.{max w t} C where
  obj U := U.power α
  map f := powerMap f α

/-- The functoriality of `FormalCoproduct.power` with respect to the index type. -/
@[simps -fullyApplied]
/--
Definition of `mapPower` / `mapPower` 的定义

English:
definition mapPower
  signature: (U : FormalCoproduct.{w} C) {α β : Type t}
  body: i ∘ f
  φ _ := Pi.lift (fun _ => Pi.π _ _)

中文:
定义 mapPower
  签名: (U : 形式余积.{w} C) {α β : 类型 t}
  定义体: i ∘ f
  φ _ := Pi.lift (fun _ => Pi.π _ _)
-/
noncomputable def mapPower (U : FormalCoproduct.{w} C) {α β : Type t}
    [HasProductsOfShape α C] [HasProductsOfShape β C] (f : α -> β) :
    U.power β ⟶ U.power α where
  f i := i ∘ f
  φ _ := Pi.lift (fun _ => Pi.π _ _)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `mapPower_id` / 引理 `mapPower_id`

English:
lemma mapPower_id
  statement: (U : FormalCoproduct.{w} C) (α : Type t)
  proof: by
  cat_disch

中文:
引理 mapPower_id
  结论: (U : 形式余积.{w} C) (α : 类型 t)
  证明: by
  cat_disch

Depends on / 依赖: cat_disch
-/
lemma mapPower_id (U : FormalCoproduct.{w} C) (α : Type t)
    [HasProductsOfShape α C] :
    U.mapPower (id : α -> α) = 𝟙 _ := by
  cat_disch

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `mapPower_comp` / 引理 `mapPower_comp`

English:
lemma mapPower_comp
  statement: (U : FormalCoproduct.{w} C) {α β γ : Type t}
  proof: by
  ext
  · cat_disch
  · dsimp
    ext
    simp [Function.comp_def]

中文:
引理 mapPower_comp
  结论: (U : 形式余积.{w} C) {α β γ : 类型 t}
  证明: by
  ext
  · cat_disch
  · dsimp
    ext
    simp [Function.comp_def]

Depends on / 依赖: Function, Function.comp_def, cat_disch, comp_def
-/
lemma mapPower_comp (U : FormalCoproduct.{w} C) {α β γ : Type t}
    [HasProductsOfShape α C] [HasProductsOfShape β C] [HasProductsOfShape γ C]
    (f : α -> β) (g : β -> γ) :
    U.mapPower (g ∘ f) = U.mapPower g ≫ U.mapPower f := by
  ext
  · cat_disch
  · dsimp
    ext
    simp [Function.comp_def]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `mapPower_powerMap` / 引理 `mapPower_powerMap`

English:
lemma mapPower_powerMap
  statement: {U V : FormalCoproduct.{w} C} (f : U ⟶ V)
  proof: by
  ext
  · cat_disch
  · dsimp
    ext
    simp [Function.comp_def]

中文:
引理 mapPower_powerMap
  结论: {U V : 形式余积.{w} C} (f : U ⟶ V)
  证明: by
  ext
  · cat_disch
  · dsimp
    ext
    simp [Function.comp_def]

Depends on / 依赖: Function, Function.comp_def, cat_disch, comp_def
-/
lemma mapPower_powerMap {U V : FormalCoproduct.{w} C} (f : U ⟶ V)
    {α β : Type t} [HasProductsOfShape α C] [HasProductsOfShape β C] (g : α -> β) :
    U.mapPower g ≫ powerMap f α = powerMap f β ≫ V.mapPower g := by
  ext
  · cat_disch
  · dsimp
    ext
    simp [Function.comp_def]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `mapPower_π` / 引理 `mapPower_π`

English:
lemma mapPower_π
  statement: (U : FormalCoproduct.{w} C) {α β : Type}
  proof: by
  ext <;> simp

中文:
引理 mapPower_π
  结论: (U : 形式余积.{w} C) {α β : 类型}
  证明: by
  ext <;> simp
-/
lemma mapPower_π (U : FormalCoproduct.{w} C) {α β : Type}
    [HasProductsOfShape α C] [HasProductsOfShape β C] (f : α -> β) (a : α) :
    mapPower U f ≫ U.powerπ a = U.powerπ (f a) := by
  ext <;> simp

attribute [local simp] mapPower_comp mapPower_powerMap

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The functor `(Type t)ᵒᵖ ⥤ FormalCoproduct.{w} C ⥤ FormalCoproduct.{max w t} C`
which sends a type `α` and `U : FormalCoproduct C` to `U.power α`. -/
@[simps]
/--
Definition of `powerBifunctor` / `powerBifunctor` 的定义

English:
definition powerBifunctor
  signature: [HasProducts.{t} C]
  body: powerFunctor α.unop
  map f := { app _ := mapPower _ f.unop }
  map_comp _ _ := by ext : 2; simp [types_comp]

中文:
定义 powerBifunctor
  签名: [HasProducts.{t} C]
  定义体: powerFunctor α.unop
  map f := { app _ := mapPower _ f.unop }
  map_comp _ _ := by ext : 2; simp [types_comp]

Depends on / 依赖: powerFunctor
-/
noncomputable def powerBifunctor [HasProducts.{t} C] :
    Type tᵒᵖ ⥤ FormalCoproduct.{w} C ⥤ FormalCoproduct.{max w t} C where
  obj α := powerFunctor α.unop
  map f := { app _ := mapPower _ f.unop }
  map_comp _ _ := by ext : 2; simp [types_comp]

variable [HasFiniteProducts C]

/-- Given `U : FormalCoproduct C`, this is the simplicial object
in `FormalCoproduct C` which sends `⦋n⦌` to `U.power (Fin (n + 1))`. -/
@[simps]
/--
Definition of `cech` / `cech` 的定义

English:
definition cech
  signature: (U : FormalCoproduct.{w} C)
  body: U.power (ToType n.unop)
  map f := U.mapPower f.unop.toOrderHom.toFun

中文:
定义 cech
  签名: (U : 形式余积.{w} C)
  定义体: U.power (ToType n.unop)
  map f := U.mapPower f.unop.toOrderHom.toFun

Depends on / 依赖: SuccOrder, SuccOrder.limitRecOn, ToType, U.power, WellOrderInductionData, cancel_epi, eq_bot, hf.F.isColimitOfIsWellOrderContinuous, hf.F.op, hf.isColimit.hom_ext, hf.isoBot.inv, hf.map_mem, hj.eq_bot, hom_ext, isColimit, isColimitOfIsWellOrderContinuous, isSuccLimit, isoBot, limitRecOn, map_mem
-/
noncomputable def cech (U : FormalCoproduct.{w} C) :
    SimplicialObject (FormalCoproduct.{w} C) where
  obj n := U.power (ToType n.unop)
  map f := U.mapPower f.unop.toOrderHom.toFun

set_option backward.defeqAttrib.useBackward true in
/-- The functor `FormalCoproduct C ⥤ SimplicialObject (FormalCoproduct C)`
which sends a formal coproduct to its Cech object. -/
@[simps]
/--
Definition of `cechFunctor` / `cechFunctor` 的定义

English:
definition cechFunctor
  signature: :
  body: U.cech
  map f := { app _ := powerMap f _ }
  map_comp _ _ := by ext : 1; simp

中文:
定义 cechFunctor
  签名: :
  定义体: U.cech
  map f := { app _ := powerMap f _ }
  map_comp _ _ := by ext : 1; simp

Depends on / 依赖: U.cech
-/
noncomputable def cechFunctor :
    FormalCoproduct.{w} C ⥤ SimplicialObject (FormalCoproduct.{w} C) where
  obj U := U.cech
  map f := { app _ := powerMap f _ }
  map_comp _ _ := by ext : 1; simp

end CategoryTheory.Limits.FormalCoproduct
