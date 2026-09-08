/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products
public import Mathlib.Topology.Category.CompHausLike.Limits
/-!

# The sigma-comparison map

This file defines the map `CompHausLike.sigmaComparison` associated to a presheaf `X` on
`CompHausLike P`, and a finite family `S₁,...,Sₙ` of spaces in `CompHausLike P`, where `P` is
stable under taking finite disjoint unions.

The map `sigmaComparison` is the canonical map `X(S₁ ⊔ ... ⊔ Sₙ) ⟶ X(S₁) × ... × X(Sₙ)` induced by
the inclusion maps `Sᵢ ⟶ S₁ ⊔ ... ⊔ Sₙ`, and it is an isomorphism when `X` preserves finite
products.
-/

@[expose] public section

universe u w

open CategoryTheory Limits

namespace CompHausLike

variable {P : TopCat.{u} → Prop} [HasExplicitFiniteCoproducts.{u} P]
  (X : (CompHausLike.{u} P)ᵒᵖ ⥤ Type (max u w)) [PreservesFiniteProducts X]
  {α : Type u} [Finite α] (σ : α → Type u)
  [∀ a, TopologicalSpace (σ a)] [∀ a, CompactSpace (σ a)] [∀ a, T2Space (σ a)]
  [∀ a, HasProp P (σ a)]

/-
**CompHausLike.** 是 Mathlib 中的一个实例，位于命名空间 `CompHausLike`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasProp P (Σ (a : α), (σ a)) := HasExplicitFiniteCoproducts.hasProp (fun a ↦ of P (σ a))

/--
The comparison map from the value of a condensed set on a finite coproduct to the product of the
values on the components.
-/
/-
**CompHausLike.sigmaComparison** 是 Mathlib 中的一个定义，位于命名空间 `CompHausLike`。
形式化陈述：sigmaComparison : X.obj ⟨(of P ((a : α) × σ a))⟩ ⟶ ((a : α) -> X.obj ⟨of P
 (σ a)⟩)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instCompactSpaceSigmaOfFinite`：∀ {ι : Type u_1} {X : ι → Type u_2} [Fini
te ι] [inst : (i : ι) → TopologicalSpace (X i)]   [∀ (i : ι), CompactSpace (X i)
], CompactSpace ((i…
· 使用定理 `CompHausLike.instHasPropSigma`：∀ {P : TopCat → Prop} [CompHausLike.HasEx
plicitFiniteCoproducts P] {α : Type u} [Finite α] (σ : α → Type u)   [inst : (a 
: α) → TopologicalS…
· 使用定理 `continuous_sigmaMk`：continuous_sigmaMk {i : ι} : Continuous (@Sigma.mk ι
 σ i)

--- 原说明 ---
The comparison map from the value of a condensed set on a finite coproduct to th
e product of the
values on the components.
-/
def sigmaComparison : X.obj ⟨(of P ((a : α) × σ a))⟩ ⟶ ((a : α) → X.obj ⟨of P (σ a)⟩) :=
  ↾fun x a ↦ X.map (ofHom _ ⟨Sigma.mk a, continuous_sigmaMk⟩).op x

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CompHausLike.sigmaComparison_eq_comp_isos** 是 Mathlib 中的一个定理，位于命名空间 `CompHausL
ike`。
形式化陈述：sigmaComparison_eq_comp_isos : sigmaComparison X σ = (X.mapIso (opCoproduc
tIsoProduct' (finiteCoproduct.isColimit.{u, u} (fun a => of P (σ a))) (productIs
Product fun x => Opposite.op (of P (σ x))))).hom ≫ (PreservesProduct.iso X fun a
 => ⟨of P (σ a)⟩).hom ≫ (Types.productIso.{u, max u w} fun a => X.obj ⟨of P (σ a
)⟩).hom
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ConcreteCategory.ext`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y
 : C) → FunLike (FC X Y) …
· 使用定理 `instCompactSpaceSigmaOfFinite`：∀ {ι : Type u_1} {X : ι → Type u_2} [Fini
te ι] [inst : (i : ι) → TopologicalSpace (X i)]   [∀ (i : ι), CompactSpace (X i)
], CompactSpace ((i…
· 使用定理 `CompHausLike.instHasPropSigma`：∀ {P : TopCat → Prop} [CompHausLike.HasEx
plicitFiniteCoproducts P] {α : Type u} [Finite α] (σ : α → Type u)   [inst : (a 
: α) → TopologicalS…
· 使用定理 `CompHausLike.HasExplicitFiniteCoproducts.hasProp`：∀ {P : TopCat → Prop} 
[self : CompHausLike.HasExplicitFiniteCoproducts P] {α : Type w} [Finite α]   (X
 : α → CompHausLike P), CompHausLike.H…
· 使用定理 `CategoryTheory.Limits.instHasProductOppositeOp`：∀ {C : Type u₁} [inst : 
CategoryTheory.Category.{v₁, u₁} C] {α : Type u_1} {Z : α → C}   [CategoryTheory
.Limits.HasCoproduct Z], CategoryThe…
· 使用定理 `CompHausLike.instHasCoproduct`：∀ {P : TopCat → Prop} {α : Type w} [Finit
e α] (X : α → CompHausLike P) [CompHausLike.HasExplicitFiniteCoproduct X],   Cat
egoryTheory.Limits.…
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Limits.instPreservesLimitsOfShapeDiscreteOfFiniteOfPreser
vesFiniteProducts`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {
D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `TypeCat.Fun.ext`：∀ {X : Type u_1} {Y : Type u_2} {x y : TypeCat.Fun X Y}
, x.toFun = y.toFun → x = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
· 使用定理 `CategoryTheory.Limits.Types.productIso_hom_comp_eval_apply`：∀ {J : Type 
v} (F : J → Type (max v u)) (j : J) (x : ∏ᶜ F),   (CategoryTheory.ConcreteCatego
ry.hom (CategoryTheory.Limits.Types.productIso F…
· 使用定理 `CategoryTheory.ConcreteCategory.congr_hom`：congr_hom {X Y : C} {f g : X 
⟶ Y} (h : f = g) (x : ToType X) : f x = g x
· 使用定理 `CategoryTheory.Limits.piComparison_comp_π`：piComparison_comp_π [HasProdu
ct f] [HasProduct fun b => G.obj (f b)] (b : β) : piComparison G f ≫ Pi.π _ b = 
G.map (Pi.π f b)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `continuous_sigmaMk`：continuous_sigmaMk {i : ι} : Continuous (@Sigma.mk ι
 σ i)
· 使用定理 `CategoryTheory.ConcreteCategory.hom_ofHom`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (C
 → Type w)}   {inst_1 : outPara…
· 使用定理 `CategoryTheory.Limits.opCoproductIsoProduct_inv_comp_ι`：opCoproductIsoPr
oduct_inv_comp_ι [HasCoproduct Z] (b : α) : (opCoproductIsoProduct Z).inv ≫ (Sig
ma.ι Z b).op = Pi.π (op <| Z ·) b
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.opCoproductIsoProduct'_comp_self`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {α : Type u_1} {Z : α → C}   {c c' :
 CategoryTheory.Limits.Cofan Z} {f : Categor…
· 使用定理 `CategoryTheory.Limits.IsColimit.fac`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃
} C]   {F : CategoryTheor…
-/
theorem sigmaComparison_eq_comp_isos : sigmaComparison X σ =
    (X.mapIso (opCoproductIsoProduct'
      (finiteCoproduct.isColimit.{u, u} (fun a ↦ of P (σ a)))
      (productIsProduct fun x ↦ Opposite.op (of P (σ x))))).hom ≫
    (PreservesProduct.iso X fun a ↦ ⟨of P (σ a)⟩).hom ≫
    (Types.productIso.{u, max u w} fun a ↦ X.obj ⟨of P (σ a)⟩).hom := by
  ext x a
  simp only [TypeCat.Fun.toFun_apply, Cofan.mk_pt, Fan.mk_pt, Functor.mapIso_hom,
    PreservesProduct.iso_hom, comp_apply, Types.productIso_hom_comp_eval_apply]
  have := ConcreteCategory.congr_hom (piComparison_comp_π X (fun a ↦ ⟨of P (σ a)⟩) a)
  simp only [comp_apply] at this
  rw [this, ← comp_apply, ← Functor.map_comp]
  simp only [sigmaComparison, ConcreteCategory.hom_ofHom, TypeCat.Fun.coe_mk]
  apply ConcreteCategory.congr_hom
  congr 2
  rw [← opCoproductIsoProduct_inv_comp_ι]
  simp only [Opposite.unop_op, unop_comp, Quiver.Hom.unop_op, Category.assoc]
  simp only [opCoproductIsoProduct, ← unop_comp, opCoproductIsoProduct'_comp_self]
  erw [IsColimit.fac]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-
**CompHausLike.isIsoSigmaComparison** 是 Mathlib 中的一个实例，位于命名空间 `CompHausLike`。
形式化陈述：isIsoSigmaComparison : IsIso sigmaComparison X σ
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `instCompactSpaceSigmaOfFinite`：∀ {ι : Type u_1} {X : ι → Type u_2} [Fini
te ι] [inst : (i : ι) → TopologicalSpace (X i)]   [∀ (i : ι), CompactSpace (X i)
], CompactSpace ((i…
· 使用定理 `CompHausLike.instHasPropSigma`：∀ {P : TopCat → Prop} [CompHausLike.HasEx
plicitFiniteCoproducts P] {α : Type u} [Finite α] (σ : α → Type u)   [inst : (a 
: α) → TopologicalS…
· 使用定理 `CompHausLike.HasExplicitFiniteCoproducts.hasProp`：∀ {P : TopCat → Prop} 
[self : CompHausLike.HasExplicitFiniteCoproducts P] {α : Type w} [Finite α]   (X
 : α → CompHausLike P), CompHausLike.H…
· 使用定理 `CategoryTheory.Limits.instHasProductOppositeOp`：∀ {C : Type u₁} [inst : 
CategoryTheory.Category.{v₁, u₁} C] {α : Type u_1} {Z : α → C}   [CategoryTheory
.Limits.HasCoproduct Z], CategoryThe…
· 使用定理 `CompHausLike.instHasCoproduct`：∀ {P : TopCat → Prop} {α : Type w} [Finit
e α] (X : α → CompHausLike P) [CompHausLike.HasExplicitFiniteCoproduct X],   Cat
egoryTheory.Limits.…
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Limits.instPreservesLimitsOfShapeDiscreteOfFiniteOfPreser
vesFiniteProducts`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {
D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CompHausLike.sigmaComparison_eq_comp_isos`：sigmaComparison_eq_comp_isos 
: sigmaComparison X σ = (X.mapIso (opCoproductIsoProduct' (finiteCoproduct.isCol
imit.{u, u} (fun a => of P (σ a…
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
-/
instance isIsoSigmaComparison : IsIso <| sigmaComparison X σ := by
  rw [sigmaComparison_eq_comp_isos]
  infer_instance

end CompHausLike

