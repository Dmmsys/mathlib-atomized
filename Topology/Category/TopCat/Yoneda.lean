/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Types.Products
public import Mathlib.Topology.Category.TopCat.Limits.Products

/-!

# Yoneda presheaves on topologically concrete categories

This file develops some API for "topologically concrete" categories, defining universe polymorphic
"Yoneda presheaves" on such categories.
-/

@[expose] public section

universe w w' v u

open CategoryTheory Opposite Limits

variable {C : Type u} [Category.{v} C] (F : C ⥤ TopCat.{w}) (Y : Type w') [TopologicalSpace Y]

namespace ContinuousMap

/--
A universe polymorphic "Yoneda presheaf" on `C` given by continuous maps into a topological space
`Y`.
-/
@[simps]
/-
**ContinuousMap.yonedaPresheaf** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMap`。
形式化陈述：yonedaPresheaf : Cᵒᵖ ⥤ Type (max w w') where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A universe polymorphic "Yoneda presheaf" on `C` given by continuous maps into a 
topological space
`Y`.
-/
def yonedaPresheaf : Cᵒᵖ ⥤ Type (max w w') where
  obj X := C(F.obj (unop X), Y)
  map f := ↾fun g ↦ ContinuousMap.comp g (F.map f.unop).hom

/--
A universe polymorphic Yoneda presheaf on `TopCat` given by continuous maps into a topological
space `Y`.
-/
@[simps]
/-
**ContinuousMap.yonedaPresheaf'** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMap`。
形式化陈述：yonedaPresheaf' : TopCat.{w}ᵒᵖ ⥤ Type (max w w') where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A universe polymorphic Yoneda presheaf on `TopCat` given by continuous maps into
 a topological
space `Y`.
-/
def yonedaPresheaf' : TopCat.{w}ᵒᵖ ⥤ Type (max w w') where
  obj X := C((unop X).1, Y)
  map f := ↾fun g ↦ ContinuousMap.comp g
    (ConcreteCategory.hom f.unop)
/-
**ContinuousMap.comp_yonedaPresheaf'** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：comp_yonedaPresheaf' : yonedaPresheaf F Y = F.op ⋙ yonedaPresheaf' Y
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_yonedaPresheaf' : yonedaPresheaf F Y = F.op ⋙ yonedaPresheaf' Y := rfl

set_option backward.isDefEq.respectTransparency false in
/-
**ContinuousMap.piComparison_fac** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：piComparison_fac {α : Type} (X : α -> TopCat) : piComparison (yonedaPreshe
af'.{w, w'} Y) (fun x => op (X x)) = (yonedaPresheaf' Y).map ((opCoproductIsoPro
duct X).inv ≫ (TopCat.sigmaIsoSigma X).inv.op) ≫ (equivEquivIso (sigmaEquiv Y (f
un x => (X x).1))).inv ≫ (Types.productIso _).inv
参数：X : α -> TopCat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasProductOppositeOp`：∀ {C : Type u₁} [inst : 
CategoryTheory.Category.{v₁, u₁} C] {α : Type u_1} {Z : α → C}   [CategoryTheory
.Limits.HasCoproduct Z], CategoryThe…
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.eq_comp_inv`：eq_comp_inv (α : X ≅ Y) {f : Z ⟶ Y} {g :
 Z ⟶ X} : g = f ≫ α.inv ↔ g ≫ α.hom = f
· 使用定理 `CategoryTheory.ConcreteCategory.ext`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y
 : C) → FunLike (FC X Y) …
· 使用定理 `TypeCat.Fun.ext`：∀ {X : Type u_1} {Y : Type u_2} {x y : TypeCat.Fun X Y}
, x.toFun = y.toFun → x = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ContinuousMap.ext`：ext {f g : C(X, Y)} (h : forall a, f a = g a) : f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
· 使用定理 `CategoryTheory.Limits.Types.productIso_hom_comp_eval_apply`：∀ {J : Type 
v} (F : J → Type (max v u)) (j : J) (x : ∏ᶜ F),   (CategoryTheory.ConcreteCatego
ry.hom (CategoryTheory.Limits.Types.productIso F…
· 使用定理 `CategoryTheory.Limits.Types.pi_lift_π_apply`：pi_lift_π_apply {β : Type v
} [Small.{u} β] (f : β -> Type u) {P : Type u} (s : forall b, P ⟶ f b) (b : β) (
x : P) : (Pi.π f b) (@Pi.lift β _…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.toIso_inv_hom_apply`：∀ {X Y : Type u} (e : X ≃ Y) (x : Y), (Catego
ryTheory.ConcreteCategory.hom e.toIso.inv) x = e.symm x
· 使用定理 `ContinuousMap.sigmaEquiv_symm_apply`：∀ {I : Type u_5} (A : Type u_6) (X 
: I → Type u_7) [inst : TopologicalSpace A]   [inst_1 : (i : I) → TopologicalSpa
ce (X i)] (f : C((i : I) …
· 使用定理 `ContinuousMap.sigmaMk_apply`：∀ {I : Type u_5} {X : I → Type u_7} [inst :
 (i : I) → TopologicalSpace (X i)] (i : I) (snd : X i),   (ContinuousMap.sigmaMk
 i) snd = ⟨i, snd…
-/
theorem piComparison_fac {α : Type} (X : α → TopCat) :
    piComparison (yonedaPresheaf'.{w, w'} Y) (fun x ↦ op (X x)) =
    (yonedaPresheaf' Y).map ((opCoproductIsoProduct X).inv ≫ (TopCat.sigmaIsoSigma X).inv.op) ≫
    (equivEquivIso (sigmaEquiv Y (fun x ↦ (X x).1))).inv ≫ (Types.productIso _).inv := by
  rw [← Category.assoc, Iso.eq_comp_inv]
  ext
  simp [yonedaPresheaf', piComparison, ← opCoproductIsoProduct_inv_comp_ι]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The universe polymorphic Yoneda presheaf on `TopCat` preserves finite products. -/
/-
**ContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The universe polymorphic Yoneda presheaf on `TopCat` preserves finite products.
-/
noncomputable instance : PreservesFiniteProducts (yonedaPresheaf'.{w, w'} Y) where
  preserves _ :=
    { preservesLimit := fun {K} =>
      have : ∀ {α : Type} (X : α → TopCat), PreservesLimit (Discrete.functor (fun x ↦ op (X x)))
          (yonedaPresheaf'.{w, w'} Y) := fun X => @PreservesProduct.of_iso_comparison _ _ _ _
          (yonedaPresheaf' Y) _ (fun x ↦ op (X x)) _ _ (by rw [piComparison_fac]; infer_instance)
      let i : K ≅ Discrete.functor (fun i ↦ op (unop (K.obj ⟨i⟩))) := Discrete.natIsoFunctor
      preservesLimit_of_iso_diagram _ i.symm }

end ContinuousMap

