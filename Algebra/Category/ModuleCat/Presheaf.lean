/-
Copyright (c) 2023 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Joël Riou
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.Ring.Basic

/-!
# Presheaves of modules over a presheaf of rings.

Given a presheaf of rings `R : Cᵒᵖ ⥤ RingCat`, we define the category `PresheafOfModules R`.
An object `M : PresheafOfModules R` consists of a family of modules
`M.obj X : ModuleCat (R.obj X)` for all `X : Cᵒᵖ`, together with the data, for all `f : X ⟶ Y`,
of a functorial linear map `M.map f` from `M.obj X` to the restriction
of scalars of `M.obj Y` via `R.map f`.


## Future work

* Compare this to the definition as a presheaf of pairs `(R, M)` with specified first part.
* Compare this to the definition as a module object of the presheaf of rings
  thought of as a monoid object.
* Presheaves of modules over a presheaf of commutative rings form a monoidal category.
* Pushforward and pullback.
-/

@[expose] public section

universe v v₁ u₁ u

open CategoryTheory LinearMap Opposite

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{u}}

variable (R) in
/-- A presheaf of modules over `R : Cᵒᵖ ⥤ RingCat` consists of family of
objects `obj X : ModuleCat (R.obj X)` for all `X : Cᵒᵖ` together with
functorial maps `obj X ⟶ (ModuleCat.restrictScalars (R.map f)).obj (obj Y)`
for all `f : X ⟶ Y` in `Cᵒᵖ`. -/
/-
**PresheafOfModules** 是 Mathlib 中的一个结构，位于命名空间 ``。
形式化陈述：PresheafOfModules where /-- a family of modules over `R.obj X` for all `X`
 -/ obj (X : Cᵒᵖ) : ModuleCat.{v} (R.obj X) /-- the restriction maps of a preshe
af of modules -/ map {X Y : Cᵒᵖ} (f : X ⟶ Y) : obj X ⟶ (ModuleCat.restrictScalar
s (R.map f).hom).obj (obj Y) map_id (X : Cᵒᵖ) : map (𝟙 X) = (ModuleCat.restrictS
calarsId' (R.map (𝟙 X)).hom (congrArg RingCat.Hom.hom (R.map_id X))).inv.app _
参数：X : Cᵒᵖ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A presheaf of modules over `R : Cᵒᵖ ⥤ RingCat` consists of family of
objects `obj X : ModuleCat (R.obj X)` for all `X : Cᵒᵖ` together with
functorial maps `obj X ⟶ (ModuleCat.restrictScalars (R.map f)).obj (obj Y)`
for all `f : X ⟶ Y` in `Cᵒᵖ`.
-/
structure PresheafOfModules where
  /-- a family of modules over `R.obj X` for all `X` -/
  obj (X : Cᵒᵖ) : ModuleCat.{v} (R.obj X)
  /-- the restriction maps of a presheaf of modules -/
  map {X Y : Cᵒᵖ} (f : X ⟶ Y) : obj X ⟶ (ModuleCat.restrictScalars (R.map f).hom).obj (obj Y)
  map_id (X : Cᵒᵖ) :
    map (𝟙 X) = (ModuleCat.restrictScalarsId' (R.map (𝟙 X)).hom
      (congrArg RingCat.Hom.hom (R.map_id X))).inv.app _ := by
        cat_disch
  map_comp {X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) :
    map (f ≫ g) = map f ≫ (ModuleCat.restrictScalars _).map (map g) ≫
      (ModuleCat.restrictScalarsComp' (R.map f).hom (R.map g).hom (R.map (f ≫ g)).hom
        (congrArg RingCat.Hom.hom <| R.map_comp f g)).inv.app _ := by cat_disch

namespace PresheafOfModules

attribute [simp] map_id map_comp
attribute [reassoc] map_comp

#adaptation_note /-- https://github.com/leanprover/lean4/pull/12564
This is required for `Algebra.Category.ModuleCat.Differentials.Presheaf` -/
/-
**PresheafOfModules.** 是 Mathlib 中的一个实例，位于命名空间 `PresheafOfModules`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
https://github.com/leanprover/lean4/pull/12564
This is required for `Algebra.Category.ModuleCat.Differentials.Presheaf`
-/
instance {R : Cᵒᵖ ⥤ CommRingCat.{u}} (X : Cᵒᵖ) (M : PresheafOfModules.{v} (R ⋙ forget₂ _ _)) :
    Module (R.obj X) (M.obj X) := (M.obj X).isModule

variable (M M₁ M₂ : PresheafOfModules.{v} R)

set_option backward.isDefEq.respectTransparency false in
/-
**PresheafOfModules.map_smul** 是 Mathlib 中的一个定理，位于命名空间 `PresheafOfModules`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {R : CategoryT
heory.Functor Cᵒᵖ RingCat}   (M : PresheafOfModules R) {X Y : Cᵒᵖ} (f : X ⟶ Y) (
r : ↑(R.obj X)) (m : ↑(M.obj X)),   (CategoryTheory.ConcreteCategory.hom (M.map 
f)) (r • m) =     (CategoryTheory.ConcreteCategory.hom (R.map f)) r • (CategoryT
heory.ConcreteCategory.hom (M.map f)) m
参数：M : PresheafOfModules R；f : X ⟶ Y；r : ↑(R.obj X)；m : ↑(M.obj X)；CategoryTheor
y.ConcreteCategory.hom (M.map f)；r • m；CategoryTheory.ConcreteCategory.hom (R.ma
p f)；CategoryTheory.ConcreteCategory.hom (M.map f)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected lemma map_smul {X Y : Cᵒᵖ} (f : X ⟶ Y) (r : R.obj X) (m : M.obj X) :
    M.map f (r • m) = R.map f r • M.map f m := by simp
/-
**PresheafOfModules.congr_map_apply** 是 Mathlib 中的一个引理，位于命名空间 `PresheafOfModules
`。
形式化陈述：congr_map_apply {X Y : Cᵒᵖ} {f g : X ⟶ Y} (h : f = g) (m : M.obj X) : M.ma
p f m = M.map g m
参数：h : f = g；m : M.obj X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
lemma congr_map_apply {X Y : Cᵒᵖ} {f g : X ⟶ Y} (h : f = g) (m : M.obj X) :
    M.map f m = M.map g m := by rw [h]
/-
**PresheafOfModules.map_comp_apply** 是 Mathlib 中的一个引理，位于命名空间 `PresheafOfModules`
。
形式化陈述：map_comp_apply {U V W : Cᵒᵖ} (i : U ⟶ V) (j : V ⟶ W) (x) : M.map (i ≫ j) x
 = M.map j (M.map i x)
参数：i : U ⟶ V；j : V ⟶ W；x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `PresheafOfModules.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.Categ
ory.{v₁, u₁} C] {R : CategoryTheory.Functor Cᵒᵖ RingCat}   (self : PresheafOfMod
ules R) {X Y Z :…
-/
lemma map_comp_apply {U V W : Cᵒᵖ} (i : U ⟶ V) (j : V ⟶ W) (x) :
    M.map (i ≫ j) x = M.map j (M.map i x) := by
  rw [M.map_comp]; rfl

set_option backward.isDefEq.respectTransparency false in
/-- The restriction map `M.map f` of a presheaf of modules `M`, bundled as a semilinear map
along the ring map `R.map f`. -/
/-
**PresheafOfModules.restrict** 是 Mathlib 中的一个定义，位于命名空间 `PresheafOfModules`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The restriction map `M.map f` of a presheaf of modules `M`, bundled as a semilin
ear map
along the ring map `R.map f`.
-/
noncomputable def restrictₛₗ {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    M.obj X →ₛₗ[(R.map f).hom] M.obj Y where
  toFun m := M.map f m
  map_add' := map_add (M.map f).hom
  map_smul' r m := M.map_smul f r m

@[simp]
/-
**PresheafOfModules.restrict** 是 Mathlib 中的一个引理，位于命名空间 `PresheafOfModules`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma restrictₛₗ_apply {X Y : Cᵒᵖ} (f : X ⟶ Y) (m : M.obj X) :
    M.restrictₛₗ f m = M.map f m := rfl

/-- A morphism of presheaves of modules consists of a family of linear maps which
satisfy the naturality condition. -/
@[ext]
/-
**PresheafOfModules.Hom** 是 Mathlib 中的一个结构，位于命名空间 `PresheafOfModules`。
形式化陈述：Hom where /-- a family of linear maps `M₁.obj X ⟶ M₂.obj X` for all `X`. -
/ app (X : Cᵒᵖ) : M₁.obj X ⟶ M₂.obj X naturality {X Y : Cᵒᵖ} (f : X ⟶ Y) : M₁.ma
p f ≫ (ModuleCat.restrictScalars (R.map f).hom).map (app Y) = app X ≫ M₂.map f
参数：X : Cᵒᵖ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism of presheaves of modules consists of a family of linear maps which
satisfy the naturality condition.
-/
structure Hom where
  /-- a family of linear maps `M₁.obj X ⟶ M₂.obj X` for all `X`. -/
  app (X : Cᵒᵖ) : M₁.obj X ⟶ M₂.obj X
  naturality {X Y : Cᵒᵖ} (f : X ⟶ Y) :
      M₁.map f ≫ (ModuleCat.restrictScalars (R.map f).hom).map (app Y) =
        app X ≫ M₂.map f := by cat_disch

attribute [reassoc (attr := simp)] Hom.naturality
/-
**PresheafOfModules.** 是 Mathlib 中的一个实例，位于命名空间 `PresheafOfModules`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Category (PresheafOfModules.{v} R) where
  Hom := Hom
  id _ := { app := fun _ ↦ 𝟙 _ }
  comp f g := { app := fun _ ↦ f.app _ ≫ g.app _ }

variable {M₁ M₂}

@[ext]
/-
**PresheafOfModules.hom_ext** 是 Mathlib 中的一个引理，位于命名空间 `PresheafOfModules`。
形式化陈述：hom_ext {f g : M₁ ⟶ M₂} (h : forall (X : Cᵒᵖ), f.app X = g.app X) : f = g
参数：h : forall (X : Cᵒᵖ), f.app X = g.app X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PresheafOfModules.Hom.ext`：∀ {C : Type u₁} {inst : CategoryTheory.Catego
ry.{v₁, u₁} C} {R : CategoryTheory.Functor Cᵒᵖ RingCat}   {M₁ M₂ : PresheafOfMod
ules R} {x y : …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
lemma hom_ext {f g : M₁ ⟶ M₂} (h : ∀ (X : Cᵒᵖ), f.app X = g.app X) :
    f = g := Hom.ext (by ext1; apply h)

@[simp]
/-
**PresheafOfModules.id_app** 是 Mathlib 中的一个引理，位于命名空间 `PresheafOfModules`。
形式化陈述：id_app (M : PresheafOfModules R) (X : Cᵒᵖ) : Hom.app (𝟙 M) X = 𝟙 _
参数：M : PresheafOfModules R；X : Cᵒᵖ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma id_app (M : PresheafOfModules R) (X : Cᵒᵖ) : Hom.app (𝟙 M) X = 𝟙 _ := by
  rfl

@[simp]
/-
**PresheafOfModules.comp_app** 是 Mathlib 中的一个引理，位于命名空间 `PresheafOfModules`。
形式化陈述：comp_app {M₁ M₂ M₃ : PresheafOfModules R} (f : M₁ ⟶ M₂) (g : M₂ ⟶ M₃) (X :
 Cᵒᵖ) : (f ≫ g).app X = f.app X ≫ g.app X
参数：f : M₁ ⟶ M₂；g : M₂ ⟶ M₃；X : Cᵒᵖ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma comp_app {M₁ M₂ M₃ : PresheafOfModules R} (f : M₁ ⟶ M₂) (g : M₂ ⟶ M₃) (X : Cᵒᵖ) :
    (f ≫ g).app X = f.app X ≫ g.app X := by
  rfl
/-
**PresheafOfModules.naturality_apply** 是 Mathlib 中的一个引理，位于命名空间 `PresheafOfModule
s`。
形式化陈述：naturality_apply (f : M₁ ⟶ M₂) {X Y : Cᵒᵖ} (g : X ⟶ Y) (x : M₁.obj X) : Ho
m.app f Y (M₁.map g x) = M₂.map g (Hom.app f X x)
参数：f : M₁ ⟶ M₂；g : X ⟶ Y；x : M₁.obj X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.congr_fun`：∀ {C : Type u_1} [inst : CategoryTheory.Catego
ry.{v_1, u_1} C] {FC : outParam (C → C → Type u_2)}   {CC : outParam (C → Type w
)} [inst_1 : o…
· 使用定理 `PresheafOfModules.Hom.naturality`：∀ {C : Type u₁} [inst : CategoryTheory
.Category.{v₁, u₁} C] {R : CategoryTheory.Functor Cᵒᵖ RingCat}   {M₁ M₂ : Preshe
afOfModules R} (self :…
-/
lemma naturality_apply (f : M₁ ⟶ M₂) {X Y : Cᵒᵖ} (g : X ⟶ Y) (x : M₁.obj X) :
    Hom.app f Y (M₁.map g x) = M₂.map g (Hom.app f X x) :=
  CategoryTheory.congr_fun (Hom.naturality f g) x

/-- Constructor for isomorphisms in the category of presheaves of modules. -/
@[simps!]
/-
**PresheafOfModules.isoMk** 是 Mathlib 中的一个定义，位于命名空间 `PresheafOfModules`。
形式化陈述：isoMk (app : forall (X : Cᵒᵖ), M₁.obj X ≅ M₂.obj X) (naturality : forall ⦃
X Y : Cᵒᵖ⦄ (f : X ⟶ Y), M₁.map f ≫ (ModuleCat.restrictScalars (R.map f).hom).map
 (app Y).hom = (app X).hom ≫ M₂.map f
参数：app : forall (X : Cᵒᵖ), M₁.obj X ≅ M₂.obj X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for isomorphisms in the category of presheaves of modules.
-/
def isoMk (app : ∀ (X : Cᵒᵖ), M₁.obj X ≅ M₂.obj X)
    (naturality : ∀ ⦃X Y : Cᵒᵖ⦄ (f : X ⟶ Y),
      M₁.map f ≫ (ModuleCat.restrictScalars (R.map f).hom).map (app Y).hom =
        (app X).hom ≫ M₂.map f := by cat_disch) : M₁ ≅ M₂ where
  hom := { app := fun X ↦ (app X).hom }
  inv :=
    { app := fun X ↦ (app X).inv
      naturality := fun {X Y} f ↦ by
        rw [← cancel_epi (app X).hom, ← reassoc_of% (naturality f), Iso.map_hom_inv_id,
          Category.comp_id, Iso.hom_inv_id_assoc] }

set_option backward.isDefEq.respectTransparency false in
/-- The underlying presheaf of abelian groups of a presheaf of modules. -/
/-
**PresheafOfModules.presheaf** 是 Mathlib 中的一个定义，位于命名空间 `PresheafOfModules`。
形式化陈述：presheaf : Cᵒᵖ ⥤ Ab where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The underlying presheaf of abelian groups of a presheaf of modules.
-/
noncomputable def presheaf : Cᵒᵖ ⥤ Ab where
  obj X := (forget₂ _ _).obj (M.obj X)
  map f := AddCommGrpCat.ofHom <| AddMonoidHom.mk' (M.map f) (by simp)

@[simp]
/-
**PresheafOfModules.presheaf_obj_coe** 是 Mathlib 中的一个引理，位于命名空间 `PresheafOfModule
s`。
形式化陈述：presheaf_obj_coe (X : Cᵒᵖ) : (M.presheaf.obj X : Type _) = M.obj X
参数：X : Cᵒᵖ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma presheaf_obj_coe (X : Cᵒᵖ) :
    (M.presheaf.obj X : Type _) = M.obj X := rfl

@[simp]
/-
**PresheafOfModules.presheaf_map_apply_coe** 是 Mathlib 中的一个引理，位于命名空间 `PresheafOf
Modules`。
形式化陈述：presheaf_map_apply_coe {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : M.obj X) : DFunLike.co
e (α
参数：f : X ⟶ Y；x : M.obj X。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma presheaf_map_apply_coe {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : M.obj X) :
    DFunLike.coe (α := M.obj X) (β := fun _ ↦ M.obj Y) (M.presheaf.map f).hom x = M.map f x := rfl

@[reassoc]
/-
**PresheafOfModules.smul_map** 是 Mathlib 中的一个引理，位于命名空间 `PresheafOfModules`。
形式化陈述：smul_map {U V : Cᵒᵖ} (f : U ⟶ V) (r : R.obj U) : dsimp% ModuleCat.smul _ r
 ≫ M.presheaf.map f = M.presheaf.map f ≫ ModuleCat.smul _ (R.map f r)
参数：f : U ⟶ V；r : R.obj U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddCommGrpCat.hom_ext`：∀ {X Y : AddCommGrpCat} {f g : X ⟶ Y}, AddCommGrp
Cat.Hom.hom f = AddCommGrpCat.Hom.hom g → f = g
· 使用定理 `AddMonoidHom.ext`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZero M] [in
st_1 : AddZero N] ⦃f g : M →+ N⦄, (∀ (x : M), f x = g x) → f = g
· 使用定理 `LinearMap.map_smul`：∀ {R : Type u_1} {M : Type u_8} {M₂ : Type u_10} [in
st : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid M₂] [inst_
3 : _roo…
-/
lemma smul_map {U V : Cᵒᵖ} (f : U ⟶ V) (r : R.obj U) :
    dsimp% ModuleCat.smul _ r ≫ M.presheaf.map f =
      M.presheaf.map f ≫ ModuleCat.smul _ (R.map f r) := by
  ext x
  exact (M.map f).hom.map_smul r x
/-
**PresheafOfModules.** 是 Mathlib 中的一个实例，位于命名空间 `PresheafOfModules`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (M : PresheafOfModules R) (X : Cᵒᵖ) :
    Module (R.obj X) (M.presheaf.obj X) :=
  inferInstanceAs (Module (R.obj X) (M.obj X))

variable (R) in
/-- The forgetful functor `PresheafOfModules R ⥤ Cᵒᵖ ⥤ Ab`. -/
/-
**PresheafOfModules.toPresheaf** 是 Mathlib 中的一个定义，位于命名空间 `PresheafOfModules`。
形式化陈述：toPresheaf : PresheafOfModules.{v} R ⥤ Cᵒᵖ ⥤ Ab where obj M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful functor `PresheafOfModules R ⥤ Cᵒᵖ ⥤ Ab`.
-/
noncomputable def toPresheaf : PresheafOfModules.{v} R ⥤ Cᵒᵖ ⥤ Ab where
  obj M := M.presheaf
  map f :=
    { app := fun X ↦ AddCommGrpCat.ofHom <| AddMonoidHom.mk' (Hom.app f X) (by simp)
      naturality := fun X Y g ↦ by ext x; exact naturality_apply f g x }

@[simp]
/-
**PresheafOfModules.toPresheaf_obj_coe** 是 Mathlib 中的一个引理，位于命名空间 `PresheafOfModu
les`。
形式化陈述：toPresheaf_obj_coe (X : Cᵒᵖ) : (((toPresheaf R).obj M).obj X : Type _) = M
.obj X
参数：X : Cᵒᵖ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toPresheaf_obj_coe (X : Cᵒᵖ) :
    (((toPresheaf R).obj M).obj X : Type _) = M.obj X := rfl

@[simp]
/-
**PresheafOfModules.toPresheaf_map_app_apply** 是 Mathlib 中的一个引理，位于命名空间 `Presheaf
OfModules`。
形式化陈述：toPresheaf_map_app_apply (f : M₁ ⟶ M₂) (X : Cᵒᵖ) (x : M₁.obj X) : DFunLike
.coe (α
参数：f : M₁ ⟶ M₂；X : Cᵒᵖ；x : M₁.obj X。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toPresheaf_map_app_apply (f : M₁ ⟶ M₂) (X : Cᵒᵖ) (x : M₁.obj X) :
    DFunLike.coe (α := M₁.obj X) (β := fun _ ↦ M₂.obj X)
      (((toPresheaf R).map f).app X).hom x = f.app X x := rfl
/-
**PresheafOfModules.** 是 Mathlib 中的一个实例，位于命名空间 `PresheafOfModules`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (toPresheaf R).Faithful where
  map_injective {_ _ f g} h := by
    ext X x
    exact ConcreteCategory.congr_hom (((evaluation _ _).obj X ⋙ forget Ab).congr_map h) x

section

variable (M : Cᵒᵖ ⥤ Ab.{v}) [∀ X, Module (R.obj X) (M.obj X)]
  (map_smul : ∀ ⦃X Y : Cᵒᵖ⦄ (f : X ⟶ Y) (r : R.obj X) (m : M.obj X),
    M.map f (r • m) = R.map f r • M.map f m)

set_option backward.isDefEq.respectTransparency false in
/-- The object in `PresheafOfModules R` that is obtained from `M : Cᵒᵖ ⥤ Ab.{v}` such
that for all `X : Cᵒᵖ`, `M.obj X` is a `R.obj X` module, in such a way that the
restriction maps are semilinear. (This constructor should be used only in cases
when the preferred constructor `PresheafOfModules.mk` is not as convenient as this one.) -/
@[simps]
/-
**PresheafOfModules.ofPresheaf** 是 Mathlib 中的一个定义，位于命名空间 `PresheafOfModules`。
形式化陈述：ofPresheaf : PresheafOfModules.{v} R where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The object in `PresheafOfModules R` that is obtained from `M : Cᵒᵖ ⥤ Ab.{v}` suc
h
that for all `X : Cᵒᵖ`, `M.obj X` is a `R.obj X` module, in such a way that the
restriction maps are semilinear. (This constructor should be used only in cases
when the preferred constructor `PresheafOfModules.mk` is not as convenient as th
is one.)
-/
noncomputable def ofPresheaf : PresheafOfModules.{v} R where
  obj X := ModuleCat.of _ (M.obj X)
  -- TODO: after https://github.com/leanprover-community/mathlib4/pull/19511 we need to hint `(Y := ...)`.
  -- This suggests `restrictScalars` needs to be redesigned.
  map {X Y} f := ModuleCat.ofHom
      (Y := (ModuleCat.restrictScalars (R.map f).hom).obj (ModuleCat.of _ (M.obj Y)))
    { toFun := fun x ↦ M.map f x
      map_add' := by simp
      map_smul' := fun r m ↦ map_smul f r m }

@[simp]
/-
**PresheafOfModules.ofPresheaf_presheaf** 是 Mathlib 中的一个引理，位于命名空间 `PresheafOfMod
ules`。
形式化陈述：ofPresheaf_presheaf : (ofPresheaf M map_smul).presheaf = M
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofPresheaf_presheaf : (ofPresheaf M map_smul).presheaf = M := rfl

end

set_option backward.isDefEq.respectTransparency.types false in
/-- The morphism of presheaves of modules `M₁ ⟶ M₂` given by a morphism
of abelian presheaves `M₁.presheaf ⟶ M₂.presheaf`
which satisfy a suitable linearity condition. -/
@[simps]
/-
**PresheafOfModules.homMk** 是 Mathlib 中的一个定义，位于命名空间 `PresheafOfModules`。
形式化陈述：homMk (φ : M₁.presheaf ⟶ M₂.presheaf) (hφ : forall (X : Cᵒᵖ) (r : R.obj X)
 (m : M₁.obj X), φ.app X (r • m) = r • φ.app X m) : M₁ ⟶ M₂ where app X
参数：φ : M₁.presheaf ⟶ M₂.presheaf；hφ : forall (X : Cᵒᵖ) (r : R.obj X) (m : M₁.obj
 X), φ.app X (r • m) = r • φ.app X m。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism of presheaves of modules `M₁ ⟶ M₂` given by a morphism
of abelian presheaves `M₁.presheaf ⟶ M₂.presheaf`
which satisfy a suitable linearity condition.
-/
noncomputable def homMk (φ : M₁.presheaf ⟶ M₂.presheaf)
    (hφ : ∀ (X : Cᵒᵖ) (r : R.obj X) (m : M₁.obj X), φ.app X (r • m) = r • φ.app X m) :
    M₁ ⟶ M₂ where
  app X := ModuleCat.ofHom
    { toFun := φ.app X
      map_add' := by simp +instances
      map_smul' := hφ X }
  naturality := fun f ↦ by
    ext x
    exact CategoryTheory.congr_fun (φ.naturality f) x
/-
**PresheafOfModules.** 是 Mathlib 中的一个实例，位于命名空间 `PresheafOfModules`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Zero (M₁ ⟶ M₂) where
  zero := { app := fun _ ↦ 0 }

variable (M₁ M₂) in
/-
**PresheafOfModules.zero_app** 是 Mathlib 中的一个定理，位于命名空间 `PresheafOfModules`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {R : CategoryT
heory.Functor Cᵒᵖ RingCat}   (M₁ M₂ : PresheafOfModules R) (X : Cᵒᵖ), PresheafOf
Modules.Hom.app 0 X = 0
参数：M₁ M₂ : PresheafOfModules R；X : Cᵒᵖ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma zero_app (X : Cᵒᵖ) : (0 : M₁ ⟶ M₂).app X = 0 := rfl
/-
**PresheafOfModules.** 是 Mathlib 中的一个实例，位于命名空间 `PresheafOfModules`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Neg (M₁ ⟶ M₂) where
  neg f :=
    { app := fun X ↦ -f.app X
      naturality := fun {X Y} h ↦ by
        ext x
        simp [← naturality_apply] }
/-
**PresheafOfModules.** 是 Mathlib 中的一个实例，位于命名空间 `PresheafOfModules`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Add (M₁ ⟶ M₂) where
  add f g :=
    { app := fun X ↦ f.app X + g.app X
      naturality := fun {X Y} h ↦ by
        ext x
        simp [← naturality_apply] }
/-
**PresheafOfModules.** 是 Mathlib 中的一个实例，位于命名空间 `PresheafOfModules`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Sub (M₁ ⟶ M₂) where
  sub f g :=
    { app := fun X ↦ f.app X - g.app X
      naturality := fun {X Y} h ↦ by
        ext x
        simp [← naturality_apply] }
/-
**PresheafOfModules.neg_app** 是 Mathlib 中的一个定理，位于命名空间 `PresheafOfModules`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {R : CategoryT
heory.Functor Cᵒᵖ RingCat}   {M₁ M₂ : PresheafOfModules R} (f : M₁ ⟶ M₂) (X : Cᵒ
ᵖ), (-f).app X = -f.app X
参数：f : M₁ ⟶ M₂；X : Cᵒᵖ；-f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma neg_app (f : M₁ ⟶ M₂) (X : Cᵒᵖ) : (-f).app X = -f.app X := rfl
/-
**PresheafOfModules.add_app** 是 Mathlib 中的一个定理，位于命名空间 `PresheafOfModules`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {R : CategoryT
heory.Functor Cᵒᵖ RingCat}   {M₁ M₂ : PresheafOfModules R} (f g : M₁ ⟶ M₂) (X : 
Cᵒᵖ), (f + g).app X = f.app X + g.app X
参数：f g : M₁ ⟶ M₂；X : Cᵒᵖ；f + g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma add_app (f g : M₁ ⟶ M₂) (X : Cᵒᵖ) : (f + g).app X = f.app X + g.app X := rfl
/-
**PresheafOfModules.sub_app** 是 Mathlib 中的一个定理，位于命名空间 `PresheafOfModules`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {R : CategoryT
heory.Functor Cᵒᵖ RingCat}   {M₁ M₂ : PresheafOfModules R} (f g : M₁ ⟶ M₂) (X : 
Cᵒᵖ), (f - g).app X = f.app X - g.app X
参数：f g : M₁ ⟶ M₂；X : Cᵒᵖ；f - g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma sub_app (f g : M₁ ⟶ M₂) (X : Cᵒᵖ) : (f - g).app X = f.app X - g.app X := rfl
/-
**PresheafOfModules.** 是 Mathlib 中的一个实例，位于命名空间 `PresheafOfModules`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddCommGroup (M₁ ⟶ M₂) where
  add_assoc := by intros; ext1; simp only [add_app, add_assoc]
  zero_add := by intros; ext1; simp only [add_app, zero_app, zero_add]
  neg_add_cancel := by intros; ext1; simp only [add_app, neg_app, neg_add_cancel, zero_app]
  add_zero := by intros; ext1; simp only [add_app, zero_app, add_zero]
  add_comm := by intros; ext1; simp only [add_app]; apply add_comm
  sub_eq_add_neg := by intros; ext1; simp only [add_app, sub_app, neg_app, sub_eq_add_neg]
  nsmul := nsmulRec
  zsmul := zsmulRec
/-
**PresheafOfModules.** 是 Mathlib 中的一个实例，位于命名空间 `PresheafOfModules`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Preadditive (PresheafOfModules R) where
/-
**PresheafOfModules.** 是 Mathlib 中的一个实例，位于命名空间 `PresheafOfModules`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (toPresheaf R).Additive where
/-
**PresheafOfModules.zsmul_app** 是 Mathlib 中的一个引理，位于命名空间 `PresheafOfModules`。
形式化陈述：zsmul_app (n : Int) (f : M₁ ⟶ M₂) (X : Cᵒᵖ) : (n • f).app X = n • f.app X
参数：n : Int；f : M₁ ⟶ M₂；X : Cᵒᵖ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ModuleCat.hom_ext`：hom_ext {M N : ModuleCat.{v} R} {f g : M ⟶ N} (hf : f
.hom = g.hom) : f = g
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_zsmul`：map_zsmul {X Y : C} {f : X ⟶ Y} {r : I
nt} : F.map (r • f) = r • F.map f
· 使用定理 `CategoryTheory.Functor.instAdditiveComp`：∀ {C : Type u_1} {D : Type u_2}
 [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.Catego
ry.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `PresheafOfModules.instAdditiveFunctorOppositeAbToPresheaf`：∀ {C : Type u
₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {R : CategoryTheory.Functor Cᵒᵖ R
ingCat},   (PresheafOfModules.toPresheaf R).Add…
· 使用定理 `CategoryTheory.Functor.instAdditiveObjEvaluation`：∀ {C : Type u_1} [inst
 : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C]
 {J : Type u_4}   [inst_2 : CategoryTh…
-/
lemma zsmul_app (n : ℤ) (f : M₁ ⟶ M₂) (X : Cᵒᵖ) : (n • f).app X = n • f.app X := by
  ext x
  change (toPresheaf R ⋙ (evaluation _ _).obj X).map (n • f) x = _
  rw [Functor.map_zsmul]
  rfl

variable (R)

/-- Evaluation on an object `X` gives a functor
`PresheafOfModules R ⥤ ModuleCat (R.obj X)`. -/
@[simps]
/-
**PresheafOfModules.evaluation** 是 Mathlib 中的一个定义，位于命名空间 `PresheafOfModules`。
形式化陈述：evaluation (X : Cᵒᵖ) : PresheafOfModules.{v} R ⥤ ModuleCat (R.obj X) where
 obj M
参数：X : Cᵒᵖ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Evaluation on an object `X` gives a functor
`PresheafOfModules R ⥤ ModuleCat (R.obj X)`.
-/
def evaluation (X : Cᵒᵖ) : PresheafOfModules.{v} R ⥤ ModuleCat (R.obj X) where
  obj M := M.obj X
  map f := f.app X
/-
**PresheafOfModules.** 是 Mathlib 中的一个实例，位于命名空间 `PresheafOfModules`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : Cᵒᵖ) : (evaluation.{v} R X).Additive where

set_option backward.defeqAttrib.useBackward true in
/-- The restriction natural transformation on presheaves of modules, considered as linear maps
to restriction of scalars. -/
@[simps]
/-
**PresheafOfModules.restriction** 是 Mathlib 中的一个定义，位于命名空间 `PresheafOfModules`。
形式化陈述：restriction {X Y : Cᵒᵖ} (f : X ⟶ Y) : evaluation R X ⟶ evaluation R Y ⋙ Mo
duleCat.restrictScalars (R.map f).hom where app M
参数：f : X ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The restriction natural transformation on presheaves of modules, considered as l
inear maps
to restriction of scalars.
-/
noncomputable def restriction {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    evaluation R X ⟶ evaluation R Y ⋙ ModuleCat.restrictScalars (R.map f).hom where
  app M := M.map f

set_option backward.isDefEq.respectTransparency false in
/-- The obvious free presheaf of modules of rank `1`. -/
/-
**PresheafOfModules.unit** 是 Mathlib 中的一个定义，位于命名空间 `PresheafOfModules`。
形式化陈述：unit : PresheafOfModules R where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The obvious free presheaf of modules of rank `1`.
-/
noncomputable def unit : PresheafOfModules R where
  obj X := ModuleCat.of _ (R.obj X)
  -- TODO: after https://github.com/leanprover-community/mathlib4/pull/19511 we need to hint `(Y := ...)`.
  -- This suggests `restrictScalars` needs to be redesigned.
  map {X Y} f := ModuleCat.ofHom
      (Y := (ModuleCat.restrictScalars (R.map f).hom).obj (ModuleCat.of (R.obj Y) (R.obj Y)))
    { toFun := fun x ↦ R.map f x
      map_add' := by simp
      map_smul' := by cat_disch }
/-
**PresheafOfModules.unit_map_one** 是 Mathlib 中的一个引理，位于命名空间 `PresheafOfModules`。
形式化陈述：unit_map_one {X Y : Cᵒᵖ} (f : X ⟶ Y) : (unit R).map f (1 : R.obj X) = (1 :
 R.obj Y)
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.map_one`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring α
} {x_1 : NonAssocSemiring β} (f : α →+* β), f 1 = 1
-/
lemma unit_map_one {X Y : Cᵒᵖ} (f : X ⟶ Y) : (unit R).map f (1 : R.obj X) = (1 : R.obj Y) :=
  (R.map f).hom.map_one

variable {R}

/-- The type of sections of a presheaf of modules. -/
/-
**PresheafOfModules.sections** 是 Mathlib 中的一个定义，位于命名空间 `PresheafOfModules`。
形式化陈述：sections (M : PresheafOfModules.{v} R) : Type _
参数：M : PresheafOfModules.{v} R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of sections of a presheaf of modules.
-/
def sections (M : PresheafOfModules.{v} R) : Type _ := (M.presheaf ⋙ forget _).sections

/-- Given a presheaf of modules `M`, `s : M.sections` and `X : Cᵒᵖ`, this is the induced
element in `M.obj X`. -/
/-
**PresheafOfModules.sections.eval** 是 Mathlib 中的一个定义，位于命名空间 `PresheafOfModules.s
ections`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {R : C
ategoryTheory.Functor Cᵒᵖ RingCat} → {M : PresheafOfModules R} → M.sections → (X
 : Cᵒᵖ) → ↑(M.obj X)
参数：X : Cᵒᵖ；M.obj X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a presheaf of modules `M`, `s : M.sections` and `X : Cᵒᵖ`, this is the ind
uced
element in `M.obj X`.
-/
abbrev sections.eval {M : PresheafOfModules.{v} R} (s : M.sections) (X : Cᵒᵖ) : M.obj X := s.1 X

@[simp]
/-
**PresheafOfModules.sections_property** 是 Mathlib 中的一个引理，位于命名空间 `PresheafOfModul
es`。
形式化陈述：sections_property {M : PresheafOfModules.{v} R} (s : M.sections) {X Y : Cᵒ
ᵖ} (f : X ⟶ Y) : M.map f (s.1 X) = s.1 Y
参数：s : M.sections；f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
lemma sections_property {M : PresheafOfModules.{v} R} (s : M.sections)
    {X Y : Cᵒᵖ} (f : X ⟶ Y) : M.map f (s.1 X) = s.1 Y := s.2 f

/-- Constructor for sections of a presheaf of modules. -/
@[simps]
/-
**PresheafOfModules.sectionsMk** 是 Mathlib 中的一个定义，位于命名空间 `PresheafOfModules`。
形式化陈述：sectionsMk {M : PresheafOfModules.{v} R} (s : forall X, M.obj X) (hs : for
all ⦃X Y : Cᵒᵖ⦄ (f : X ⟶ Y), M.map f (s X) = s Y) : M.sections where val
参数：s : forall X, M.obj X；hs : forall ⦃X Y : Cᵒᵖ⦄ (f : X ⟶ Y), M.map f (s X) = s 
Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for sections of a presheaf of modules.
-/
def sectionsMk {M : PresheafOfModules.{v} R} (s : ∀ X, M.obj X)
    (hs : ∀ ⦃X Y : Cᵒᵖ⦄ (f : X ⟶ Y), M.map f (s X) = s Y) : M.sections where
  val := s
  property f := hs f

@[ext]
/-
**PresheafOfModules.sections_ext** 是 Mathlib 中的一个引理，位于命名空间 `PresheafOfModules`。
形式化陈述：sections_ext {M : PresheafOfModules.{v} R} (s t : M.sections) (h : forall 
(X : Cᵒᵖ), s.val X = t.val X) : s = t
参数：s t : M.sections；h : forall (X : Cᵒᵖ), s.val X = t.val X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
lemma sections_ext {M : PresheafOfModules.{v} R} (s t : M.sections)
    (h : ∀ (X : Cᵒᵖ), s.val X = t.val X) : s = t :=
  Subtype.ext (by ext; apply h)

set_option backward.isDefEq.respectTransparency.types false in
/-- The map `M.sections → N.sections` induced by a morphisms `M ⟶ N` of presheaves of modules. -/
@[simps!]
/-
**PresheafOfModules.sectionsMap** 是 Mathlib 中的一个定义，位于命名空间 `PresheafOfModules`。
形式化陈述：sectionsMap {M N : PresheafOfModules.{v} R} (f : M ⟶ N) (s : M.sections) :
 N.sections
参数：f : M ⟶ N；s : M.sections。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map `M.sections → N.sections` induced by a morphisms `M ⟶ N` of presheaves o
f modules.
-/
def sectionsMap {M N : PresheafOfModules.{v} R} (f : M ⟶ N) (s : M.sections) : N.sections :=
  N.sectionsMk (fun X ↦ f.app X (s.1 _))
    (fun X Y g ↦ by rw [← naturality_apply, sections_property])

@[simp]
/-
**PresheafOfModules.sectionsMap_comp** 是 Mathlib 中的一个定理，位于命名空间 `PresheafOfModule
s`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {R : CategoryT
heory.Functor Cᵒᵖ RingCat}   {M N P : PresheafOfModules R} (f : M ⟶ N) (g : N ⟶ 
P) (s : M.sections),   PresheafOfModules.sectionsMap (CategoryTheory.CategoryStr
uct.comp f g) s =     PresheafOfModules.sectionsMap g (PresheafOfModules.section
sMap f s)
参数：f : M ⟶ N；g : N ⟶ P；s : M.sections；CategoryTheory.CategoryStruct.comp f g；Pre
sheafOfModules.sectionsMap f s。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma sectionsMap_comp {M N P : PresheafOfModules.{v} R} (f : M ⟶ N) (g : N ⟶ P) (s : M.sections) :
    sectionsMap (f ≫ g) s = sectionsMap g (sectionsMap f s) := rfl

@[simp]
/-
**PresheafOfModules.sectionsMap_id** 是 Mathlib 中的一个定理，位于命名空间 `PresheafOfModules`
。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {R : CategoryT
heory.Functor Cᵒᵖ RingCat}   {M : PresheafOfModules R} (s : M.sections), Preshea
fOfModules.sectionsMap (CategoryTheory.CategoryStruct.id M) s = s
参数：s : M.sections；CategoryTheory.CategoryStruct.id M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma sectionsMap_id {M : PresheafOfModules.{v} R} (s : M.sections) :
    sectionsMap (𝟙 M) s = s := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The bijection `(unit R ⟶ M) ≃ M.sections` for `M : PresheafOfModules R`. -/
@[simps! apply_coe]
/-
**PresheafOfModules.unitHomEquiv** 是 Mathlib 中的一个定义，位于命名空间 `PresheafOfModules`。
形式化陈述：unitHomEquiv (M : PresheafOfModules R) : (unit R ⟶ M) ≃ M.sections where t
oFun f
参数：M : PresheafOfModules R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The bijection `(unit R ⟶ M) ≃ M.sections` for `M : PresheafOfModules R`.
-/
noncomputable def unitHomEquiv (M : PresheafOfModules R) :
    (unit R ⟶ M) ≃ M.sections where
  toFun f := sectionsMk (fun X ↦ Hom.app f X (1 : R.obj X))
    (by intros; rw [← naturality_apply, unit_map_one])
  invFun s :=
    { app := fun X ↦ ModuleCat.ofHom
        ((LinearMap.ringLmapEquivSelf (R.obj X) ℤ (M.obj X)).symm (s.val X))
      naturality := fun {X Y} f ↦ by
        ext
        dsimp
        change R.map f 1 • s.eval Y = M.map f (1 • s.eval X)
        simp }
  left_inv f := by
    ext X : 2
    exact (LinearMap.ringLmapEquivSelf (R.obj X) ℤ (M.obj X)).symm_apply_apply (f.app X).hom
  right_inv s := by
    ext X
    exact (LinearMap.ringLmapEquivSelf (R.obj X) ℤ (M.obj X)).apply_symm_apply (s.val X)

section module_over_initial

variable (X : Cᵒᵖ) (hX : Limits.IsInitial X)

/-!
## `PresheafOfModules R ⥤ Cᵒᵖ ⥤ ModuleCat (R.obj X)` when `X` is initial

When `X` is initial, we have `Module (R.obj X) (M.obj c)` for any `c : Cᵒᵖ`.

-/

section

variable (M : PresheafOfModules.{v} R)

/-- Auxiliary definition for `forgetToPresheafModuleCatObj`. -/
/-
**PresheafOfModules.forgetToPresheafModuleCatObjObj** 是 Mathlib 中的一个缩写定义，位于命名空间 
`PresheafOfModules`。
形式化陈述：forgetToPresheafModuleCatObjObj (Y : Cᵒᵖ) : ModuleCat (R.obj X)
参数：Y : Cᵒᵖ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `forgetToPresheafModuleCatObj`.
-/
noncomputable abbrev forgetToPresheafModuleCatObjObj (Y : Cᵒᵖ) : ModuleCat (R.obj X) :=
  (ModuleCat.restrictScalars (R.map (hX.to Y)).hom).obj (M.obj Y)

-- This should not be a `simp` lemma because `M.obj Y` is missing the `Module (R.obj X)` instance,
-- so `simp`ing breaks downstream proofs.
/-
**PresheafOfModules.forgetToPresheafModuleCatObjObj_coe** 是 Mathlib 中的一个引理，位于命名空
间 `PresheafOfModules`。
形式化陈述：forgetToPresheafModuleCatObjObj_coe (Y : Cᵒᵖ) : (forgetToPresheafModuleCat
ObjObj X hX M Y : Type _) = M.obj Y
参数：Y : Cᵒᵖ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma forgetToPresheafModuleCatObjObj_coe (Y : Cᵒᵖ) :
    (forgetToPresheafModuleCatObjObj X hX M Y : Type _) = M.obj Y := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary definition for `forgetToPresheafModuleCatObj`. -/
/-
**PresheafOfModules.forgetToPresheafModuleCatObjMap** 是 Mathlib 中的一个定义，位于命名空间 `P
resheafOfModules`。
形式化陈述：forgetToPresheafModuleCatObjMap {Y Z : Cᵒᵖ} (f : Y ⟶ Z) : forgetToPresheaf
ModuleCatObjObj X hX M Y ⟶ forgetToPresheafModuleCatObjObj X hX M Z
参数：f : Y ⟶ Z。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `forgetToPresheafModuleCatObj`.
-/
noncomputable def forgetToPresheafModuleCatObjMap {Y Z : Cᵒᵖ} (f : Y ⟶ Z) :
    forgetToPresheafModuleCatObjObj X hX M Y ⟶
      forgetToPresheafModuleCatObjObj X hX M Z :=
  ModuleCat.ofHom
    (X := forgetToPresheafModuleCatObjObj X hX M Y) (Y := forgetToPresheafModuleCatObjObj X hX M Z)
  { toFun := fun x => M.map f x
    map_add' := by simp
    map_smul' := fun r x => by
      simp only [ModuleCat.restrictScalars.smul_def (R := R.obj X), RingHom.id_apply, M.map_smul]
      rw [← RingCat.comp_apply, ← R.map_comp]
      congr
      apply hX.hom_ext }

@[simp]
/-
**PresheafOfModules.forgetToPresheafModuleCatObjMap_apply** 是 Mathlib 中的一个引理，位于命
名空间 `PresheafOfModules`。
形式化陈述：forgetToPresheafModuleCatObjMap_apply {Y Z : Cᵒᵖ} (f : Y ⟶ Z) (m : M.obj Y
) : (forgetToPresheafModuleCatObjMap X hX M f).hom m = M.map f m
参数：f : Y ⟶ Z；m : M.obj Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma forgetToPresheafModuleCatObjMap_apply {Y Z : Cᵒᵖ} (f : Y ⟶ Z) (m : M.obj Y) :
    (forgetToPresheafModuleCatObjMap X hX M f).hom m = M.map f m := rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
Implementation of the functor `PresheafOfModules R ⥤ Cᵒᵖ ⥤ ModuleCat (R.obj X)`
when `X` is initial.

The functor is implemented as, on object level `M ↦ (c ↦ M(c))` where the `R(X)`-module structure
on `M(c)` is given by restriction of scalars along the unique morphism `R(c) ⟶ R(X)`; and on
morphism level `(f : M ⟶ N) ↦ (c ↦ f(c))`.
-/
@[simps]
/-
**PresheafOfModules.forgetToPresheafModuleCatObj** 是 Mathlib 中的一个定义，位于命名空间 `Pres
heafOfModules`。
形式化陈述：forgetToPresheafModuleCatObj (X : Cᵒᵖ) (hX : Limits.IsInitial X) (M : Pres
heafOfModules.{v} R) : Cᵒᵖ ⥤ ModuleCat (R.obj X) where obj Y
参数：X : Cᵒᵖ；hX : Limits.IsInitial X；M : PresheafOfModules.{v} R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Implementation of the functor `PresheafOfModules R ⥤ Cᵒᵖ ⥤ ModuleCat (R.obj X)`
when `X` is initial.

The functor is implemented as, on object level `M ↦ (c ↦ M(c))` where the `R(X)`
-module structure
on `M(c)` is given by restriction of scalars along the unique morphism `R(c) ⟶ R
(X)`; and on
morphism level `(f : M ⟶ N) ↦ (c ↦ f(c))`.
-/
noncomputable def forgetToPresheafModuleCatObj
    (X : Cᵒᵖ) (hX : Limits.IsInitial X) (M : PresheafOfModules.{v} R) :
    Cᵒᵖ ⥤ ModuleCat (R.obj X) where
  obj Y := forgetToPresheafModuleCatObjObj X hX M Y
  map f := forgetToPresheafModuleCatObjMap X hX M f

end

set_option backward.isDefEq.respectTransparency false in
/--
Implementation of the functor `PresheafOfModules R ⥤ Cᵒᵖ ⥤ ModuleCat (R.obj X)`
when `X` is initial.

The functor is implemented as, on object level `M ↦ (c ↦ M(c))` where the `R(X)`-module structure
on `M(c)` is given by restriction of scalars along the unique morphism `R(c) ⟶ R(X)`; and on
morphism level `(f : M ⟶ N) ↦ (c ↦ f(c))`.
-/
/-
**PresheafOfModules.forgetToPresheafModuleCatMap** 是 Mathlib 中的一个定义，位于命名空间 `Pres
heafOfModules`。
形式化陈述：forgetToPresheafModuleCatMap (X : Cᵒᵖ) (hX : Limits.IsInitial X) {M N : Pr
esheafOfModules.{v} R} (f : M ⟶ N) : forgetToPresheafModuleCatObj X hX M ⟶ forge
tToPresheafModuleCatObj X hX N where app Y
参数：X : Cᵒᵖ；hX : Limits.IsInitial X；f : M ⟶ N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Implementation of the functor `PresheafOfModules R ⥤ Cᵒᵖ ⥤ ModuleCat (R.obj X)`
when `X` is initial.

The functor is implemented as, on object level `M ↦ (c ↦ M(c))` where the `R(X)`
-module structure
on `M(c)` is given by restriction of scalars along the unique morphism `R(c) ⟶ R
(X)`; and on
morphism level `(f : M ⟶ N) ↦ (c ↦ f(c))`.
-/
noncomputable def forgetToPresheafModuleCatMap
    (X : Cᵒᵖ) (hX : Limits.IsInitial X) {M N : PresheafOfModules.{v} R} (f : M ⟶ N) :
    forgetToPresheafModuleCatObj X hX M ⟶ forgetToPresheafModuleCatObj X hX N where
  app Y := ModuleCat.ofHom
      (X := (forgetToPresheafModuleCatObj X hX M).obj Y)
      (Y := (forgetToPresheafModuleCatObj X hX N).obj Y)
    { toFun := f.app Y
      map_add' := by simp
      map_smul' := fun r ↦ (f.app Y).hom.map_smul (R.map (hX.to Y) _) }
  naturality Y Z g := by
    ext x
    exact naturality_apply f g x

set_option backward.isDefEq.respectTransparency.types false in
/--
The forgetful functor from presheaves of modules over a presheaf of rings `R` to presheaves of
`R(X)`-modules where `X` is an initial object.

The functor is implemented as, on object level `M ↦ (c ↦ M(c))` where the `R(X)`-module structure
on `M(c)` is given by restriction of scalars along the unique morphism `R(c) ⟶ R(X)`; and on
morphism level `(f : M ⟶ N) ↦ (c ↦ f(c))`.
-/
@[simps]
/-
**PresheafOfModules.forgetToPresheafModuleCat** 是 Mathlib 中的一个定义，位于命名空间 `Preshea
fOfModules`。
形式化陈述：forgetToPresheafModuleCat (X : Cᵒᵖ) (hX : Limits.IsInitial X) : PresheafOf
Modules.{v} R ⥤ Cᵒᵖ ⥤ ModuleCat (R.obj X) where obj M
参数：X : Cᵒᵖ；hX : Limits.IsInitial X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful functor from presheaves of modules over a presheaf of rings `R` to
 presheaves of
`R(X)`-modules where `X` is an initial object.

The functor is implemented as, on object level `M ↦ (c ↦ M(c))` where the `R(X)`
-module structure
on `M(c)` is given by restriction of scalars along the unique morphism `R(c) ⟶ R
(X)`; and on
morphism level `(f : M ⟶ N) ↦ (c ↦ f(c))`.
-/
noncomputable def forgetToPresheafModuleCat (X : Cᵒᵖ) (hX : Limits.IsInitial X) :
    PresheafOfModules.{v} R ⥤ Cᵒᵖ ⥤ ModuleCat (R.obj X) where
  obj M := forgetToPresheafModuleCatObj X hX M
  map f := forgetToPresheafModuleCatMap X hX f

end module_over_initial

end PresheafOfModules

