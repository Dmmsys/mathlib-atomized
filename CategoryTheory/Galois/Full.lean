/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Galois.Action

/-!

# Fiber functors are (faithfully) full

Any (fiber) functor `F : C ⥤ FintypeCat` factors via the forgetful functor
from finite `Aut F`-sets to finite sets. The induced functor
`H : C ⥤ Action FintypeCat (Aut F)` is faithfully full. The faithfulness
follows easily from the faithfulness of `F`. In this file we show that `H` is also full.

## Main results

- `PreGaloisCategory.exists_lift_of_mono`: If `Y` is a sub-`Aut F`-set of `F.obj X`, there exists
  a sub-object `Z` of `X` such that `F.obj Z ≅ Y` as `Aut F`-sets.
- `PreGaloisCategory.functorToAction_full`: The induced functor `H` from above is full.

The main input for this is that the induced functor `H : C ⥤ Action FintypeCat (Aut F)`
preserves connectedness, which translates to the fact that `Aut F` acts transitively on
the fibers of connected objects.

-/

public section

universe u

namespace CategoryTheory

namespace PreGaloisCategory

open Limits CategoryTheory.Functor

variable {C : Type*} [Category* C] (F : C ⥤ FintypeCat.{u}) [GaloisCategory C] [FiberFunctor F]

/--
Let `X` be an object of a Galois category with fiber functor `F` and `Y` a sub-`Aut F`-set
of `F.obj X`, on which `Aut F` acts transitively (i.e. which is connected in the Galois category
of finite `Aut F`-sets). Then there exists a connected sub-object `Z` of `X` and an isomorphism
`Y ≅ F.obj X` as `Aut F`-sets such that the obvious triangle commutes.

For a version without the connectedness assumption, see `exists_lift_of_mono`.
-/
/-
**CategoryTheory.PreGaloisCategory.exists_lift_of_mono_of_isConnected** 是 Mathli
b 中的一个引理，位于命名空间 `CategoryTheory.PreGaloisCategory`。
形式化陈述：exists_lift_of_mono_of_isConnected (X : C) (Y : Action FintypeCat.{u} (Aut
 F)) (i : Y ⟶ (functorToAction F).obj X) [Mono i] [IsConnected Y] : exists (Z : 
C) (f : Z ⟶ X) (u : Y ≅ (functorToAction F).obj Z), IsConnected Z ∧ Mono f ∧ i =
 u.hom ≫ (functorToAction F).map f
参数：X : C；Y : Action FintypeCat.{u} (Aut F)；i : Y ⟶ (functorToAction F).obj X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GaloisCategory.toPreGaloisCategory`：∀ {C : Type u₁} {inst
 : CategoryTheory.Category.{u₂, u₁} C} [self : CategoryTheory.GaloisCategory C],
   CategoryTheory.PreGaloisCategory C
· 使用定理 `CategoryTheory.FintypeCat.instPreGaloisCategoryActionFintypeCat`：∀ (G : 
Type u) [inst : Group G], CategoryTheory.PreGaloisCategory (Action FintypeCat G)
· 使用定理 `CategoryTheory.FintypeCat.instFiberFunctorActionFintypeCatForget₂HomSubt
ypeFunObjFiniteV`：∀ (G : Type u) [inst : Group G],   CategoryTheory.PreGaloisCat
egory.FiberFunctor (CategoryTheory.forget₂ (Action FintypeCat G) FintypeCat)
· 使用引理 `CategoryTheory.PreGaloisCategory.fiber_in_connected_component`：fiber_in_
connected_component (X : C) (x : F.obj X) : exists (Y : C) (i : Y ⟶ X) (y : F.ob
j Y), F.map i y = x ∧ IsConnected Y ∧ Mono i
· 使用定理 `CategoryTheory.PreGaloisCategory.PreservesIsConnected.preserves`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{u₂, u₁} C} {D : Type v₁} {inst_1 : Cat
egoryTheory.Category.{v₂, v₁} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.PreGaloisCategory.instPreservesIsConnectedActionFintypeCa
tAutFunctorFunctorToAction`：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_
1, u_1} C] (F : CategoryTheory.Functor C FintypeCat)   [inst_1 : CategoryTheory.
GaloisCa…
· 使用引理 `CategoryTheory.PreGaloisCategory.connected_component_unique`：connected_c
omponent_unique {X A B : C} [IsConnected A] [IsConnected B] (a : F.obj A) (b : F
.obj B) (i : A ⟶ X) (j : B ⟶ X) (h : F.map i a = …
· 使用定理 `CategoryTheory.FintypeCat.instGaloisCategoryActionFintypeCat`：∀ (G : Typ
e u) [inst : Group G], CategoryTheory.GaloisCategory (Action FintypeCat G)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_mono`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (F : CategoryTheor…
· 使用定理 `CategoryTheory.PreGaloisCategory.instPreservesMonomorphismsActionFintype
CatAutFunctorFunctorToAction`：∀ {C : Type u_1} [inst : CategoryTheory.Category.{
v_1, u_1} C] (F : CategoryTheory.Functor C FintypeCat)   [inst_1 : CategoryTheor
y.GaloisCa…
· 使用引理 `CategoryTheory.PreGaloisCategory.evaluation_injective_of_isConnected`：ev
aluation_injective_of_isConnected (A X : C) [IsConnected A] (a : F.obj A) : Func
tion.Injective (fun (f : A ⟶ X) => F.map f a)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …

--- 原说明 ---
Let `X` be an object of a Galois category with fiber functor `F` and `Y` a sub-`
Aut F`-set
of `F.obj X`, on which `Aut F` acts transitively (i.e. which is connected in the
 Galois category
of finite `Aut F`-sets). Then there exists a connected sub-object `Z` of `X` and
 an isomorphism
`Y ≅ F.obj X` as `Aut F`-sets such that the obvious triangle commutes.

For a version without the connectedness assumption, see `exists_lift_of_mono`.
-/
lemma exists_lift_of_mono_of_isConnected (X : C) (Y : Action FintypeCat.{u} (Aut F))
    (i : Y ⟶ (functorToAction F).obj X) [Mono i] [IsConnected Y] : ∃ (Z : C) (f : Z ⟶ X)
    (u : Y ≅ (functorToAction F).obj Z),
    IsConnected Z ∧ Mono f ∧ i = u.hom ≫ (functorToAction F).map f := by
  obtain ⟨y⟩ := nonempty_fiber_of_isConnected (forget₂ _ FintypeCat) Y
  obtain ⟨Z, f, z, hz, hc, hm⟩ := fiber_in_connected_component F X (i.hom y)
  have : IsConnected ((functorToAction F).obj Z) := PreservesIsConnected.preserves
  obtain ⟨u, hu⟩ := connected_component_unique
    (forget₂ (Action FintypeCat (Aut F)) FintypeCat) (B := (functorToAction F).obj Z)
    y z i ((functorToAction F).map f) hz.symm
  refine ⟨Z, f, u, hc, hm, ?_⟩
  apply evaluation_injective_of_isConnected
    (forget₂ (Action FintypeCat (Aut F)) FintypeCat) Y ((functorToAction F).obj X) y
  suffices h : i.hom y = F.map f z by simpa [hu]
  exact hz.symm

set_option backward.isDefEq.respectTransparency false in
/--
Let `X` be an object of a Galois category with fiber functor `F` and `Y` a sub-`Aut F`-set
of `F.obj X`. Then there exists a sub-object `Z` of `X` and an isomorphism
`Y ≅ F.obj X` as `Aut F`-sets such that the obvious triangle commutes.
-/
/-
**CategoryTheory.PreGaloisCategory.exists_lift_of_mono** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.PreGaloisCategory`。
形式化陈述：exists_lift_of_mono (X : C) (Y : Action FintypeCat.{u} (Aut F)) (i : Y ⟶ (
functorToAction F).obj X) [Mono i] : exists (Z : C) (f : Z ⟶ X) (u : Y ≅ (functo
rToAction F).obj Z), Mono f ∧ u.hom ≫ (functorToAction F).map f = i
参数：X : C；Y : Action FintypeCat.{u} (Aut F)；i : Y ⟶ (functorToAction F).obj X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GaloisCategory.toPreGaloisCategory`：∀ {C : Type u₁} {inst
 : CategoryTheory.Category.{u₂, u₁} C} [self : CategoryTheory.GaloisCategory C],
   CategoryTheory.PreGaloisCategory C
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.PreGaloisCategory.hasFiniteCoproducts`：∀ {C : Type u₁} {i
nst : CategoryTheory.Category.{u₂, u₁} C} [self : CategoryTheory.PreGaloisCatego
ry C],   CategoryTheory.Limits.HasFiniteCo…
· 使用定理 `CategoryTheory.FintypeCat.instGaloisCategoryActionFintypeCat`：∀ (G : Typ
e u) [inst : Group G], CategoryTheory.GaloisCategory (Action FintypeCat G)
· 使用定理 `CategoryTheory.PreGaloisCategory.has_decomp_connected_components'`：has_d
ecomp_connected_components' (X : C) : exists (ι : Type) (_ : Finite ι) (f : ι ->
 C) (_ : ∐ f ≅ X), forall i, IsConnected (f i)
· 使用定理 `Action.instHasFiniteCoproducts`：∀ {V : Type u_1} [inst : CategoryTheory.
Category.{v_1, u_1} V] {G : Type u_2} [inst_1 : Monoid G]   [CategoryTheory.Limi
ts.HasFiniteCoproduc…
· 使用定理 `CategoryTheory.Limits.hasFiniteCoproducts_of_hasFiniteColimits`：∀ (C : T
ype u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFinit
eColimits C],   CategoryTheory.Limits.HasFiniteCopro…
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Limits.instPreservesColimitsOfShapeDiscreteOfFiniteOfPres
ervesFiniteCoproducts`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} 
C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTh
eor…
· 使用定理 `CategoryTheory.PreGaloisCategory.instPreservesFiniteCoproductsActionFint
ypeCatAutFunctorFunctorToAction`：∀ {C : Type u_1} [inst : CategoryTheory.Categor
y.{v_1, u_1} C] (F : CategoryTheory.Functor C FintypeCat)   [inst_1 : CategoryTh
eory.GaloisCa…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Iso.inv_comp_eq`：inv_comp_eq (α : X ≅ Y) {f : X ⟶ Z} {g :
 Y ⟶ Z} : α.inv ≫ f = g ↔ f = α.hom ≫ g
· 使用定理 `CategoryTheory.Limits.Sigma.hom_ext`：∀ {β : Type w} {C : Type u} [inst :
 CategoryTheory.Category.{v, u} C] {f : β → C}   [inst_1 : CategoryTheory.Limits
.HasCoproduct f] {X : C} …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Limits.sigmaComparison_map_desc`：sigmaComparison_map_desc
 [HasCoproduct f] [HasCoproduct fun b => G.obj (f b)] (P : C) (g : forall j, f j
 ⟶ P) : sigmaComparison G f ≫ G.map …
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.Sigma.ι_mapIso_inv_assoc`：∀ {β : Type w} {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C] {f g : β → C}   [inst_1 : Category
Theory.Limits.HasCoproductsOfShape β…
· 使用定理 `CategoryTheory.Functor.mono_of_mono_map`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.PreGaloisCategory.instReflectsMonomorphismsActionFintypeC
atAutFunctorFunctorToAction`：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v
_1, u_1} C] (F : CategoryTheory.Functor C FintypeCat)   [inst_1 : CategoryTheory
.GaloisCa…
· 使用定理 `CategoryTheory.mono_comp`：∀ {C : Type u} [inst : CategoryTheory.Category
.{v, u} C] {X Y Z : C} (g : Z ⟶ Y) [CategoryTheory.Mono g] (f : Y ⟶ X)   [Catego
ryTheory.Mono …
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.instStrongMonoOfIsRegularMono`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsRegula
rMono f],   CategoryTheory.StrongM…
（共 38 条，此处仅展示前 30 条）

--- 原说明 ---
Let `X` be an object of a Galois category with fiber functor `F` and `Y` a sub-`
Aut F`-set
of `F.obj X`. Then there exists a sub-object `Z` of `X` and an isomorphism
`Y ≅ F.obj X` as `Aut F`-sets such that the obvious triangle commutes.
-/
lemma exists_lift_of_mono (X : C) (Y : Action FintypeCat.{u} (Aut F))
    (i : Y ⟶ (functorToAction F).obj X) [Mono i] : ∃ (Z : C) (f : Z ⟶ X)
    (u : Y ≅ (functorToAction F).obj Z), Mono f ∧ u.hom ≫ (functorToAction F).map f = i := by
  obtain ⟨ι, hf, f, t, hc⟩ := has_decomp_connected_components' Y
  let i' (j : ι) : f j ⟶ (functorToAction F).obj X := Sigma.ι f j ≫ t.hom ≫ i
  choose gZ gf gu _ _ h using fun i ↦ exists_lift_of_mono_of_isConnected F X (f i) (i' i)
  let is2 : (functorToAction F).obj (∐ gZ) ≅ ∐ fun i => (functorToAction F).obj (gZ i) :=
    PreservesCoproduct.iso (functorToAction F) gZ
  let u' : ∐ f ≅ ∐ fun i => (functorToAction F).obj (gZ i) := Sigma.mapIso gu
  have heq : (functorToAction F).map (Sigma.desc gf) = (t.symm ≪≫ u' ≪≫ is2.symm).inv ≫ i := by
    simp only [Iso.trans_inv, Iso.symm_inv, Category.assoc]
    rw [← Iso.inv_comp_eq]
    refine Sigma.hom_ext _ _ (fun j ↦ ?_)
    suffices (functorToAction F).map (gf j) = (gu j).inv ≫ i' j by
      simpa [is2, u']
    simp only [h, Iso.inv_hom_id_assoc]
  refine ⟨∐ gZ, Sigma.desc gf, t.symm ≪≫ u' ≪≫ is2.symm, ?_, by simp [heq]⟩
  · exact mono_of_mono_map (functorToAction F) (heq ▸ mono_comp _ _)

set_option backward.isDefEq.respectTransparency false in
/-- The by a fiber functor `F : C ⥤ FintypeCat` induced functor `functorToAction F` to
finite `Aut F`-sets is full. -/
/-
**CategoryTheory.PreGaloisCategory.functorToAction_full** 是 Mathlib 中的一个实例，位于命名空
间 `CategoryTheory.PreGaloisCategory`。
形式化陈述：functorToAction_full : Functor.Full (functorToAction F) where map_surjecti
ve {X Y} f
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GaloisCategory.toPreGaloisCategory`：∀ {C : Type u₁} {inst
 : CategoryTheory.Category.{u₂, u₁} C} [self : CategoryTheory.GaloisCategory C],
   CategoryTheory.PreGaloisCategory C
· 使用定理 `CategoryTheory.Limits.instHasBinaryProductObjOfPreservesLimitDiscreteWal
kingPairPair`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : T
ype u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (G : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.PreGaloisCategory.instHasBinaryProducts`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{u₂, u₁} C] [CategoryTheory.PreGaloisCategory C]
,   CategoryTheory.Limits.HasBinaryProducts …
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Limits.instPreservesLimitsOfShapeDiscreteOfFiniteOfPreser
vesFiniteProducts`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {
D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.PreGaloisCategory.instPreservesFiniteProductsActionFintyp
eCatAutFunctorFunctorToAction`：∀ {C : Type u_1} [inst : CategoryTheory.Category.
{v_1, u_1} C] (F : CategoryTheory.Functor C FintypeCat)   [inst_1 : CategoryTheo
ry.GaloisCa…
· 使用定理 `CategoryTheory.instMonoId`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] (X : C),   CategoryTheory.Mono (CategoryTheory.CategoryStruct.id X)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.prod.lift_fst`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinaryPro
duct X Y] (f : W ⟶ X) (g …
· 使用定理 `CategoryTheory.mono_of_mono`：∀ {C : Type u} [inst : CategoryTheory.Categ
ory.{v, u} C] {X Y Z : C} (g : Z ⟶ Y) (f : Y ⟶ X)   [CategoryTheory.Mono (Catego
ryTheory.Category…
· 使用定理 `CategoryTheory.mono_comp`：∀ {C : Type u} [inst : CategoryTheory.Category
.{v, u} C] {X Y Z : C} (g : Z ⟶ Y) [CategoryTheory.Mono g] (f : Y ⟶ X)   [Catego
ryTheory.Mono …
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.instStrongMonoOfIsRegularMono`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsRegula
rMono f],   CategoryTheory.StrongM…
· 使用定理 `CategoryTheory.instIsRegularMonoOfIsSplitMono`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsSplit
Mono f],   CategoryTheory.IsRegular…
· 使用定理 `CategoryTheory.IsSplitMono.of_iso`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {X Y : C} (f : Y ⟶ X) [CategoryTheory.IsIso f],   Categor
yTheory.IsSplitMono f
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用引理 `CategoryTheory.PreGaloisCategory.exists_lift_of_mono`：exists_lift_of_mon
o (X : C) (Y : Action FintypeCat.{u} (Aut F)) (i : Y ⟶ (functorToAction F).obj X
) [Mono i] : exists (Z : C) (f : Z ⟶ X) (u…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.PreservesLimitPair.iso_inv_fst`：∀ {C : Type u₁} [i
nst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory
.Category.{v₂, u₂} D]   (G : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.isIso_of_reflects_iso`：isIso_of_reflects_iso {A B : C} (f
 : A ⟶ B) (F : C ⥤ D) [IsIso (F.map f)] [F.ReflectsIsomorphisms] : IsIso f
（共 42 条，此处仅展示前 30 条）

--- 原说明 ---
The by a fiber functor `F : C ⥤ FintypeCat` induced functor `functorToAction F` 
to
finite `Aut F`-sets is full.
-/
instance functorToAction_full : Functor.Full (functorToAction F) where
  map_surjective {X Y} f := by
    let u : (functorToAction F).obj X ⟶ (functorToAction F).obj X ⨯ (functorToAction F).obj Y :=
      prod.lift (𝟙 _) f
    let i : (functorToAction F).obj X ⟶ (functorToAction F).obj (X ⨯ Y) :=
      u ≫ (PreservesLimitPair.iso (functorToAction F) X Y).inv
    have : Mono i := by
      have : Mono (u ≫ prod.fst) := prod.lift_fst (𝟙 _) f ▸ inferInstance
      have : Mono u := mono_of_mono u prod.fst
      apply mono_comp u _
    obtain ⟨Z, g, v, _, hvgi⟩ := exists_lift_of_mono F (Limits.prod X Y)
      ((functorToAction F).obj X) i
    let ψ : Z ⟶ X := g ≫ prod.fst
    have hgvi : (functorToAction F).map g = v.inv ≫ i := by simp [← hvgi]
    have : IsIso ((functorToAction F).map ψ) := by
      simp only [map_comp, hgvi, Category.assoc, ψ]
      have : IsIso (i ≫ (functorToAction F).map prod.fst) := by
        suffices h : IsIso (𝟙 ((functorToAction F).obj X)) by simpa [i, u]
        infer_instance
      apply IsIso.comp_isIso
    have : IsIso ψ := isIso_of_reflects_iso ψ (functorToAction F)
    use inv ψ ≫ g ≫ prod.snd
    rw [← cancel_epi ((functorToAction F).map ψ)]
    ext (z : F.obj Z)
    simp [-FintypeCat.comp_apply, -Action.comp_hom, i, u, ψ, hgvi]

end PreGaloisCategory

end CategoryTheory

