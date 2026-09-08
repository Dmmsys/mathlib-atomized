/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.CategoryTheory.Filtered.Connected
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.Limits.ConeCategory
public import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
public import Mathlib.CategoryTheory.Limits.Preserves.Filtered
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Limits.Bicones
public import Mathlib.CategoryTheory.Limits.Comma
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Limits.Preserves.Opposites
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
/-!
# Representably flat functors

We define representably flat functors as functors such that the category of structured arrows
over `X` is cofiltered for each `X`. This concept is also known as flat functors as in [Elephant]
Remark C2.3.7, and this name is suggested by Mike Shulman in
https://golem.ph.utexas.edu/category/2011/06/flat_functors_and_morphisms_of.html to avoid
confusion with other notions of flatness (e.g. see the notion of flat type-valued
functor in the file `Mathlib/CategoryTheory/Functor/TypeValuedFlat.lean`).

This definition is equivalent to left exact functors (functors that preserves finite limits) when
`C` has all finite limits.

## Main results

* `flat_of_preservesFiniteLimits`: If `F : C ⥤ D` preserves finite limits and `C` has all finite
  limits, then `F` is flat.
* `preservesFiniteLimits_of_flat`: If `F : C ⥤ D` is flat, then it preserves all finite limits.
* `preservesFiniteLimits_iff_flat`: If `C` has all finite limits,
  then `F` is flat iff `F` is left exact.
* `lan_preservesFiniteLimits_of_flat`: If `F : C ⥤ D` is a flat functor between small categories,
  then the functor `Lan F.op` between presheaves of sets preserves all finite limits.
* `flat_iff_lan_flat`: If `C`, `D` are small and `C` has all finite limits, then `F` is flat iff
  `Lan F.op : (Cᵒᵖ ⥤ Type*) ⥤ (Dᵒᵖ ⥤ Type*)` is flat.
* `preservesFiniteLimits_iff_lanPreservesFiniteLimits`: If `C`, `D` are small and `C` has all
  finite limits, then `F` preserves finite limits iff `Lan F.op : (Cᵒᵖ ⥤ Type*) ⥤ (Dᵒᵖ ⥤ Type*)`
  does.

-/

@[expose] public section


universe w v₁ v₂ v₃ u₁ u₂ u₃

open CategoryTheory

open CategoryTheory.Limits

open Opposite

namespace CategoryTheory

section RepresentablyFlat

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
variable {E : Type u₃} [Category.{v₃} E]

/-- A functor `F : C ⥤ D` is representably flat if the comma category `(X/F)` is cofiltered for
each `X : D`.
-/
/-
**CategoryTheory.RepresentablyFlat** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} → [inst_1 : CategoryTheory.Category.{v₂, u₂} D] → CategoryTheory.Functor
 C D → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor `F : C ⥤ D` is representably flat if the comma category `(X/F)` is cof
iltered for
each `X : D`.
-/
class RepresentablyFlat (F : C ⥤ D) : Prop where
  cofiltered : ∀ X : D, IsCofiltered (StructuredArrow X F)

/-- A functor `F : C ⥤ D` is representably coflat if the comma category `(F/X)` is filtered for
each `X : D`. -/
/-
**CategoryTheory.RepresentablyCoflat** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory
`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} → [inst_1 : CategoryTheory.Category.{v₂, u₂} D] → CategoryTheory.Functor
 C D → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor `F : C ⥤ D` is representably coflat if the comma category `(F/X)` is f
iltered for
each `X : D`.
-/
class RepresentablyCoflat (F : C ⥤ D) : Prop where
  filtered : ∀ X : D, IsFiltered (CostructuredArrow F X)

attribute [instance] RepresentablyFlat.cofiltered RepresentablyCoflat.filtered

variable (F : C ⥤ D)
/-
**CategoryTheory.RepresentablyFlat.of_isRightAdjoint** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.RepresentablyFlat`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheory.Functor C D)
 [F.IsRightAdjoint], CategoryTheory.RepresentablyFlat F
参数：F : CategoryTheory.Functor C D。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsCofiltered.of_isInitial`：of_isInitial {X : C} (h : IsIn
itial X) : IsCofiltered C
-/
instance RepresentablyFlat.of_isRightAdjoint [F.IsRightAdjoint] : RepresentablyFlat F where
  cofiltered _ := IsCofiltered.of_isInitial _ (mkInitialOfLeftAdjoint _ (.ofIsRightAdjoint F) _)
/-
**CategoryTheory.RepresentablyCoflat.of_isLeftAdjoint** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.RepresentablyCoflat`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheory.Functor C D)
 [F.IsLeftAdjoint], CategoryTheory.RepresentablyCoflat F
参数：F : CategoryTheory.Functor C D。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsFiltered.of_isTerminal`：of_isTerminal {X : C} (h : IsTe
rminal X) : IsFiltered C
-/
instance RepresentablyCoflat.of_isLeftAdjoint [F.IsLeftAdjoint] : RepresentablyCoflat F where
  filtered _ := IsFiltered.of_isTerminal _ (mkTerminalOfRightAdjoint _ (.ofIsLeftAdjoint F) _)
/-
**CategoryTheory.RepresentablyFlat.id** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
RepresentablyFlat`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C],   CategoryThe
ory.RepresentablyFlat (CategoryTheory.Functor.id C)
参数：CategoryTheory.Functor.id C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.RepresentablyFlat.of_isRightAdjoint`：∀ {C : Type u₁} [ins
t : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.C
ategory.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.isRightAdjoint_of_isEquivalence`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} D]   {F : CategoryTheor…
-/
theorem RepresentablyFlat.id : RepresentablyFlat (𝟭 C) := inferInstance
/-
**CategoryTheory.RepresentablyCoflat.id** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.RepresentablyCoflat`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C],   CategoryThe
ory.RepresentablyCoflat (CategoryTheory.Functor.id C)
参数：CategoryTheory.Functor.id C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.RepresentablyCoflat.of_isLeftAdjoint`：∀ {C : Type u₁} [in
st : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.
Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.isLeftAdjoint_of_isEquivalence`：∀ {C : Type u₁} [
inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheor
y.Category.{v₂, u₂} D]   {F : CategoryTheor…
-/
theorem RepresentablyCoflat.id : RepresentablyCoflat (𝟭 C) := inferInstance

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.RepresentablyFlat.comp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.RepresentablyFlat`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {E : Type u₃} [inst_2 : Category
Theory.Category.{v₃, u₃} E] (F : CategoryTheory.Functor C D)   (G : CategoryTheo
ry.Functor D E) [CategoryTheory.RepresentablyFlat F] [CategoryTheory.Representab
lyFlat G],   CategoryTheory.RepresentablyFlat (F.comp G)
参数：F : CategoryTheory.Functor C D；G : CategoryTheory.Functor D E；F.comp G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsCofiltered.of_cone_nonempty`：of_cone_nonempty (h : fora
ll {J : Type w} [SmallCategory J] [FinCategory J] (F : J ⥤ C), Nonempty (Cone F)
) : IsCofiltered C
· 使用定理 `CategoryTheory.IsCofiltered.cone_nonempty`：cone_nonempty (F : J ⥤ C) : N
onempty (Cone F)
· 使用定理 `CategoryTheory.RepresentablyFlat.cofiltered`：∀ {C : Type u₁} {inst : Cat
egoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Category
.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.Cone.w`：∀ {J : Type u₁} [inst : CategoryTheory.Cat
egory.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃} C]   
{F : CategoryTheor…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.StructuredArrow.homMk.congr_simp`：∀ {C : Type u₁} [inst :
 CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cate
gory.{v₂, u₂} D]   {S : D} {T : Categ…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.StructuredArrow.w`：w : X.hom ≫ T.map f.right = Y.hom
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
-/
instance RepresentablyFlat.comp (G : D ⥤ E) [RepresentablyFlat F]
    [RepresentablyFlat G] : RepresentablyFlat (F ⋙ G) := by
  refine ⟨fun X => IsCofiltered.of_cone_nonempty.{0} _ (fun {J} _ _ H => ?_)⟩
  obtain ⟨c₁⟩ := IsCofiltered.cone_nonempty (H ⋙ StructuredArrow.pre X F G)
  let H₂ : J ⥤ StructuredArrow c₁.pt.right F :=
    { obj := fun j => StructuredArrow.mk (c₁.π.app j).right
      map := fun {j j'} f =>
        StructuredArrow.homMk (H.map f).right (congrArg CommaMorphism.right (c₁.w f)) }
  obtain ⟨c₂⟩ := IsCofiltered.cone_nonempty H₂
  simp only [H₂] at c₂
  exact ⟨⟨StructuredArrow.mk (c₁.pt.hom ≫ G.map c₂.pt.hom),
    ⟨fun j => StructuredArrow.homMk (c₂.π.app j).right (by simp [← G.map_comp]),
     fun j j' f => by simpa using (c₂.w f).symm⟩⟩⟩

section

variable {F}

/-- Being a representably flat functor is closed under natural isomorphisms. -/
/-
**CategoryTheory.RepresentablyFlat.of_iso** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.RepresentablyFlat`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {F : CategoryTheory.Functor C D}
 [CategoryTheory.RepresentablyFlat F] {G : CategoryTheory.Functor C D} (α : F ≅ 
G),   CategoryTheory.RepresentablyFlat G
参数：α : F ≅ G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsCofiltered.of_equivalence`：of_equivalence (h : C ≌ D) :
 IsCofiltered D
· 使用定理 `CategoryTheory.RepresentablyFlat.cofiltered`：∀ {C : Type u₁} {inst : Cat
egoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Category
.{v₂, u₂} D}   {F : CategoryTheor…

--- 原说明 ---
Being a representably flat functor is closed under natural isomorphisms.
-/
theorem RepresentablyFlat.of_iso [RepresentablyFlat F] {G : C ⥤ D} (α : F ≅ G) :
    RepresentablyFlat G where
  cofiltered _ := IsCofiltered.of_equivalence (StructuredArrow.mapNatIso α)
/-
**CategoryTheory.RepresentablyCoflat.of_iso** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.RepresentablyCoflat`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {F : CategoryTheory.Functor C D}
 [CategoryTheory.RepresentablyCoflat F] {G : CategoryTheory.Functor C D} (α : F 
≅ G),   CategoryTheory.RepresentablyCoflat G
参数：α : F ≅ G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsFiltered.of_equivalence`：of_equivalence (h : C ≌ D) : I
sFiltered D
· 使用定理 `CategoryTheory.RepresentablyCoflat.filtered`：∀ {C : Type u₁} {inst : Cat
egoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Category
.{v₂, u₂} D}   {F : CategoryTheor…
-/
theorem RepresentablyCoflat.of_iso [RepresentablyCoflat F] {G : C ⥤ D} (α : F ≅ G) :
    RepresentablyCoflat G where
  filtered _ := IsFiltered.of_equivalence (CostructuredArrow.mapNatIso α)

end

/-
**CategoryTheory.representablyCoflat_op_iff** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory`。
形式化陈述：representablyCoflat_op_iff : RepresentablyCoflat F.op ↔ RepresentablyFlat 
F
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsFiltered.of_equivalence`：of_equivalence (h : C ≌ D) : I
sFiltered D
· 使用定理 `CategoryTheory.RepresentablyCoflat.filtered`：∀ {C : Type u₁} {inst : Cat
egoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Category
.{v₂, u₂} D}   {F : CategoryTheor…
· 使用引理 `CategoryTheory.isCofiltered_of_isFiltered_op`：isCofiltered_of_isFiltered
_op [IsFiltered Cᵒᵖ] : IsCofiltered C
· 使用定理 `CategoryTheory.IsCofiltered.of_equivalence`：of_equivalence (h : C ≌ D) :
 IsCofiltered D
· 使用定理 `CategoryTheory.RepresentablyFlat.cofiltered`：∀ {C : Type u₁} {inst : Cat
egoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Category
.{v₂, u₂} D}   {F : CategoryTheor…
· 使用引理 `CategoryTheory.isFiltered_of_isCofiltered_op`：isFiltered_of_isCofiltered
_op [IsCofiltered Cᵒᵖ] : IsFiltered C
-/
theorem representablyCoflat_op_iff : RepresentablyCoflat F.op ↔ RepresentablyFlat F := by
  refine ⟨fun _ => ⟨fun X => ?_⟩, fun _ => ⟨fun ⟨X⟩ => ?_⟩⟩
  · suffices IsFiltered (StructuredArrow X F)ᵒᵖ from isCofiltered_of_isFiltered_op _
    apply IsFiltered.of_equivalence (structuredArrowOpEquivalence _ _).symm
  · suffices IsCofiltered (CostructuredArrow F.op (op X))ᵒᵖ from isFiltered_of_isCofiltered_op _
    suffices IsCofiltered (StructuredArrow X F)ᵒᵖᵒᵖ from
      IsCofiltered.of_equivalence (structuredArrowOpEquivalence _ _).op
    apply IsCofiltered.of_equivalence (opOpEquivalence _)
/-
**CategoryTheory.representablyFlat_op_iff** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory`。
形式化陈述：representablyFlat_op_iff : RepresentablyFlat F.op ↔ RepresentablyCoflat F
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsCofiltered.of_equivalence`：of_equivalence (h : C ≌ D) :
 IsCofiltered D
· 使用定理 `CategoryTheory.RepresentablyFlat.cofiltered`：∀ {C : Type u₁} {inst : Cat
egoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Category
.{v₂, u₂} D}   {F : CategoryTheor…
· 使用引理 `CategoryTheory.isFiltered_of_isCofiltered_op`：isFiltered_of_isCofiltered
_op [IsCofiltered Cᵒᵖ] : IsFiltered C
· 使用定理 `CategoryTheory.IsFiltered.of_equivalence`：of_equivalence (h : C ≌ D) : I
sFiltered D
· 使用定理 `CategoryTheory.RepresentablyCoflat.filtered`：∀ {C : Type u₁} {inst : Cat
egoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Category
.{v₂, u₂} D}   {F : CategoryTheor…
· 使用引理 `CategoryTheory.isCofiltered_of_isFiltered_op`：isCofiltered_of_isFiltered
_op [IsFiltered Cᵒᵖ] : IsCofiltered C
-/
theorem representablyFlat_op_iff : RepresentablyFlat F.op ↔ RepresentablyCoflat F := by
  refine ⟨fun _ => ⟨fun X => ?_⟩, fun _ => ⟨fun ⟨X⟩ => ?_⟩⟩
  · suffices IsCofiltered (CostructuredArrow F X)ᵒᵖ from isFiltered_of_isCofiltered_op _
    apply IsCofiltered.of_equivalence (costructuredArrowOpEquivalence _ _).symm
  · suffices IsFiltered (StructuredArrow (op X) F.op)ᵒᵖ from isCofiltered_of_isFiltered_op _
    suffices IsFiltered (CostructuredArrow F X)ᵒᵖᵒᵖ from
      IsFiltered.of_equivalence (costructuredArrowOpEquivalence _ _).op
    apply IsFiltered.of_equivalence (opOpEquivalence _)
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [RepresentablyFlat F] : RepresentablyCoflat F.op :=
  (representablyCoflat_op_iff F).2 inferInstance
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [RepresentablyCoflat F] : RepresentablyFlat F.op :=
  (representablyFlat_op_iff F).2 inferInstance
/-
**CategoryTheory.RepresentablyCoflat.comp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.RepresentablyCoflat`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {E : Type u₃} [inst_2 : Category
Theory.Category.{v₃, u₃} E] (F : CategoryTheory.Functor C D)   (G : CategoryTheo
ry.Functor D E) [CategoryTheory.RepresentablyCoflat F] [CategoryTheory.Represent
ablyCoflat G],   CategoryTheory.RepresentablyCoflat (F.comp G)
参数：F : CategoryTheory.Functor C D；G : CategoryTheory.Functor D E；F.comp G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.representablyFlat_op_iff`：representablyFlat_op_iff : Repr
esentablyFlat F.op ↔ RepresentablyCoflat F
-/
instance RepresentablyCoflat.comp (G : D ⥤ E) [RepresentablyCoflat F] [RepresentablyCoflat G] :
    RepresentablyCoflat (F ⋙ G) :=
  (representablyFlat_op_iff _).1 <| inferInstanceAs <| RepresentablyFlat (F.op ⋙ G.op)
/-
**CategoryTheory.final_of_representablyFlat** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory`。
形式化陈述：final_of_representablyFlat [h : RepresentablyFlat F] : F.Final where out _
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsCofiltered.isConnected`：∀ (C : Type u) [inst : Category
Theory.Category.{v, u} C] [CategoryTheory.IsCofiltered C], CategoryTheory.IsConn
ected C
· 使用定理 `CategoryTheory.RepresentablyFlat.cofiltered`：∀ {C : Type u₁} {inst : Cat
egoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Category
.{v₂, u₂} D}   {F : CategoryTheor…
-/
lemma final_of_representablyFlat [h : RepresentablyFlat F] : F.Final where
  out _ := IsCofiltered.isConnected _
/-
**CategoryTheory.initial_of_representablyCoflat** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory`。
形式化陈述：initial_of_representablyCoflat [h : RepresentablyCoflat F] : F.Initial whe
re out _
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsFiltered.isConnected`：∀ (C : Type u) [inst : CategoryTh
eory.Category.{v, u} C] [CategoryTheory.IsFiltered C], CategoryTheory.IsConnecte
d C
· 使用定理 `CategoryTheory.RepresentablyCoflat.filtered`：∀ {C : Type u₁} {inst : Cat
egoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Category
.{v₂, u₂} D}   {F : CategoryTheor…
-/
lemma initial_of_representablyCoflat [h : RepresentablyCoflat F] : F.Initial where
  out _ := IsFiltered.isConnected _

end RepresentablyFlat

section HasLimit

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-
**CategoryTheory.flat_of_preservesFiniteLimits** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory`。
形式化陈述：flat_of_preservesFiniteLimits [HasFiniteLimits C] (F : C ⥤ D) [PreservesFi
niteLimits F] : RepresentablyFlat F
参数：F : C ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsCofiltered.of_hasFiniteLimits`：of_hasFiniteLimits [HasF
initeLimits C] : IsCofiltered C
· 使用定理 `CategoryTheory.Limits.hasFiniteLimits_of_hasFiniteLimits_of_size`：hasFin
iteLimits_of_hasFiniteLimits_of_size (h : forall (J : Type w) {𝒥 : SmallCategory
 J} (_ : @FinCategory J 𝒥), HasLimitsOfShape J C) : Ha…
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.hasLimitsOfShape_of_hasFiniteLimits`：∀ (C : Type u
) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFiniteLimi
ts C] (J : Type w)   [inst_2 : CategoryTheory.S…
· 使用定理 `CategoryTheory.Limits.preservesLimitsOfShapeOfPreservesFiniteLimits`：∀ {
C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 :
 CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Limits.comp_preservesLimitsOfShape`：∀ {C : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Ca
tegory.{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `CategoryTheory.Limits.preservesFiniteLimits_of_createsFiniteLimits_and_h
asFiniteLimits`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D :
 Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
-/
theorem flat_of_preservesFiniteLimits [HasFiniteLimits C] (F : C ⥤ D) [PreservesFiniteLimits F] :
    RepresentablyFlat F :=
  ⟨fun X =>
    haveI : HasFiniteLimits (StructuredArrow X F) := by
      apply hasFiniteLimits_of_hasFiniteLimits_of_size.{v₁} (StructuredArrow X F)
      exact fun _ _ _ => HasLimitsOfShape.mk
    IsCofiltered.of_hasFiniteLimits _⟩
/-
**CategoryTheory.coflat_of_preservesFiniteColimits** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory`。
形式化陈述：coflat_of_preservesFiniteColimits [HasFiniteColimits C] (F : C ⥤ D) [Prese
rvesFiniteColimits F] : RepresentablyCoflat F
参数：F : C ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesFiniteLimits_op`：preservesFiniteLimits_op
 (F : C ⥤ D) [PreservesFiniteColimits F] : PreservesFiniteLimits F.op where pres
ervesFiniteLimits J _ _
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.representablyFlat_op_iff`：representablyFlat_op_iff : Repr
esentablyFlat F.op ↔ RepresentablyCoflat F
· 使用定理 `CategoryTheory.flat_of_preservesFiniteLimits`：flat_of_preservesFiniteLim
its [HasFiniteLimits C] (F : C ⥤ D) [PreservesFiniteLimits F] : RepresentablyFla
t F
-/
theorem coflat_of_preservesFiniteColimits [HasFiniteColimits C] (F : C ⥤ D)
    [PreservesFiniteColimits F] : RepresentablyCoflat F :=
  let _ := preservesFiniteLimits_op F
  (representablyFlat_op_iff _).1 (flat_of_preservesFiniteLimits _)

namespace PreservesFiniteLimitsOfFlat

open StructuredArrow

variable {J : Type v₁} [SmallCategory J] [FinCategory J] {K : J ⥤ C}
variable (F : C ⥤ D) [RepresentablyFlat F] {c : Cone K} (hc : IsLimit c) (s : Cone (K ⋙ F))

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- (Implementation).
Given a limit cone `c : cone K` and a cone `s : cone (K ⋙ F)` with `F` representably flat,
`s` can factor through `F.mapCone c`.
-/
/-
**CategoryTheory.PreservesFiniteLimitsOfFlat.lift** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.PreservesFiniteLimitsOfFlat`。
形式化陈述：lift : s.pt ⟶ F.obj c.pt
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(Implementation).
Given a limit cone `c : cone K` and a cone `s : cone (K ⋙ F)` with `F` represent
ably flat,
`s` can factor through `F.mapCone c`.
-/
noncomputable def lift : s.pt ⟶ F.obj c.pt :=
  let s' := IsCofiltered.cone (s.toStructuredArrow ⋙ StructuredArrow.pre _ K F)
  s'.pt.hom ≫
    (F.map <|
      hc.lift <|
        (Cone.postcompose
              ({ app := fun _ => 𝟙 _ } :
                (s.toStructuredArrow ⋙ pre s.pt K F) ⋙ proj s.pt F ⟶ K)).obj <|
          (StructuredArrow.proj s.pt F).mapCone s')

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.PreservesFiniteLimitsOfFlat.fac** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.PreservesFiniteLimitsOfFlat`。
形式化陈述：fac (x : J) : lift F hc s ≫ (F.mapCone c).π.app x = s.π.app x
参数：x : J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.IsLimit.fac`：∀ {J : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃} 
C]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.StructuredArrow.w`：w : X.hom ≫ T.map f.right = Y.hom
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem fac (x : J) : lift F hc s ≫ (F.mapCone c).π.app x = s.π.app x := by
  simp [lift, ← Functor.map_comp]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.PreservesFiniteLimitsOfFlat.uniq** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.PreservesFiniteLimitsOfFlat`。
形式化陈述：uniq {K : J ⥤ C} {c : Cone K} (hc : IsLimit c) (s : Cone (K ⋙ F)) (f₁ f₂ :
 s.pt ⟶ F.obj c.pt) (h₁ : forall j : J, f₁ ≫ (F.mapCone c).π.app j = s.π.app j) 
(h₂ : forall j : J, f₂ ≫ (F.mapCone c).π.app j = s.π.app j) : f₁ = f₂
参数：hc : IsLimit c；s : Cone (K ⋙ F)；f₁ f₂ : s.pt ⟶ F.obj c.pt；h₁ : forall j : J, 
f₁ ≫ (F.mapCone c).π.app j = s.π.app j；h₂ : forall j : J, f₂ ≫ (F.mapCone c).π.a
pp j = s.π.app j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.StructuredArrow.eqToHom_right`：eqToHom_right {X Y : Struc
turedArrow S T} (h : X = Y) : (eqToHom h).right = eqToHom (by rw [h])
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.RepresentablyFlat.cofiltered`：∀ {C : Type u₁} {inst : Cat
egoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Category
.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `CategoryTheory.Limits.Cone.w`：∀ {J : Type u₁} [inst : CategoryTheory.Cat
egory.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃} C]   
{F : CategoryTheor…
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.Limits.IsLimit.uniq`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃}
 C]   {F : CategoryTheor…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `CategoryTheory.StructuredArrow.Hom.w`：∀ {C : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u
₂} D]   {S : D} {T : Categ…
-/
theorem uniq {K : J ⥤ C} {c : Cone K} (hc : IsLimit c) (s : Cone (K ⋙ F))
    (f₁ f₂ : s.pt ⟶ F.obj c.pt) (h₁ : ∀ j : J, f₁ ≫ (F.mapCone c).π.app j = s.π.app j)
    (h₂ : ∀ j : J, f₂ ≫ (F.mapCone c).π.app j = s.π.app j) : f₁ = f₂ := by
  -- We can make two cones over the diagram of `s` via `f₁` and `f₂`.
  let α₁ : (F.mapCone c).toStructuredArrow ⋙ map f₁ ⟶ s.toStructuredArrow :=
    { app := fun X => eqToHom (by simp [← h₁]) }
  let α₂ : (F.mapCone c).toStructuredArrow ⋙ map f₂ ⟶ s.toStructuredArrow :=
    { app := fun X => eqToHom (by simp [← h₂]) }
  let c₁ : Cone (s.toStructuredArrow ⋙ pre s.pt K F) :=
    (Cone.postcompose (Functor.whiskerRight α₁ (pre s.pt K F) :)).obj
      (c.toStructuredArrowCone F f₁)
  let c₂ : Cone (s.toStructuredArrow ⋙ pre s.pt K F) :=
    (Cone.postcompose (Functor.whiskerRight α₂ (pre s.pt K F) :)).obj
      (c.toStructuredArrowCone F f₂)
  -- The two cones can then be combined and we may obtain a cone over the two cones since
  -- `StructuredArrow s.pt F` is cofiltered.
  let c₀ := IsCofiltered.cone (biconeMk _ c₁ c₂)
  let g₁ : c₀.pt ⟶ c₁.pt := c₀.π.app Bicone.left
  let g₂ : c₀.pt ⟶ c₂.pt := c₀.π.app Bicone.right
  -- Then `g₁.right` and `g₂.right` are two maps from the same cone into the `c`.
  have : ∀ j : J, g₁.right ≫ c.π.app j = g₂.right ≫ c.π.app j := by
    intro j
    injection c₀.π.naturality (BiconeHom.left j) with _ e₁
    injection c₀.π.naturality (BiconeHom.right j) with _ e₂
    convert! e₁.symm.trans e₂ <;> simp [c₁, c₂]
  have : c.extend g₁.right = c.extend g₂.right := by
    unfold Cone.extend
    congr 1
    ext x
    apply this
  -- And thus they are equal as `c` is the limit.
  have : g₁.right = g₂.right := calc
    g₁.right = hc.lift (c.extend g₁.right) := by
      apply hc.uniq (c.extend _)
      simp
    _ = hc.lift (c.extend g₂.right) := by
      congr
    _ = g₂.right := by
      symm
      apply hc.uniq (c.extend _)
      simp
  -- Finally, since `fᵢ` factors through `F(gᵢ)`, the result follows.
  calc
    f₁ = c₀.pt.hom ≫ F.map g₁.right := g₁.w.symm
    _ = c₀.pt.hom ≫ F.map g₂.right := by rw [this]
    _ = f₂ := g₂.w

end PreservesFiniteLimitsOfFlat

/-- Representably flat functors preserve finite limits. -/
/-
**CategoryTheory.preservesFiniteLimits_of_flat** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory`。
形式化陈述：preservesFiniteLimits_of_flat (F : C ⥤ D) [RepresentablyFlat F] : Preserve
sFiniteLimits F
参数：F : C ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesFiniteLimits_of_preservesFiniteLimitsOfSi
ze`：preservesFiniteLimits_of_preservesFiniteLimitsOfSize (F : C ⥤ D) (h : forall
 (J : Type w) {𝒥 : SmallCategory J} (_ : @FinCategory J 𝒥), Pres…
· 使用定理 `CategoryTheory.PreservesFiniteLimitsOfFlat.fac`：fac (x : J) : lift F hc 
s ≫ (F.mapCone c).π.app x = s.π.app x
· 使用定理 `CategoryTheory.PreservesFiniteLimitsOfFlat.uniq`：uniq {K : J ⥤ C} {c : C
one K} (hc : IsLimit c) (s : Cone (K ⋙ F)) (f₁ f₂ : s.pt ⟶ F.obj c.pt) (h₁ : for
all j : J, f₁ ≫ (F.mapCone c).π.app j…

--- 原说明 ---
Representably flat functors preserve finite limits.
-/
lemma preservesFiniteLimits_of_flat (F : C ⥤ D) [RepresentablyFlat F] :
    PreservesFiniteLimits F := by
  apply preservesFiniteLimits_of_preservesFiniteLimitsOfSize
  intro J _ _; constructor
  intro K; constructor
  intro c hc
  constructor
  exact
    { lift := PreservesFiniteLimitsOfFlat.lift F hc
      fac := PreservesFiniteLimitsOfFlat.fac F hc
      uniq := fun s m h => by
        apply PreservesFiniteLimitsOfFlat.uniq F hc
        · exact h
        · exact PreservesFiniteLimitsOfFlat.fac F hc s }

/-- Representably coflat functors preserve finite colimits. -/
/-
**CategoryTheory.preservesFiniteColimits_of_coflat** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory`。
形式化陈述：preservesFiniteColimits_of_coflat (F : C ⥤ D) [RepresentablyCoflat F] : Pr
eservesFiniteColimits F
参数：F : C ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesFiniteColimits_of_op`：preservesFiniteColi
mits_of_op (F : C ⥤ D) [PreservesFiniteLimits F.op] : PreservesFiniteColimits F 
where preservesFiniteColimits J _ _
· 使用引理 `CategoryTheory.preservesFiniteLimits_of_flat`：preservesFiniteLimits_of_f
lat (F : C ⥤ D) [RepresentablyFlat F] : PreservesFiniteLimits F
· 使用定理 `CategoryTheory.instRepresentablyFlatOppositeOpOfRepresentablyCoflat`：∀ {
C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 :
 CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…

--- 原说明 ---
Representably coflat functors preserve finite colimits.
-/
lemma preservesFiniteColimits_of_coflat (F : C ⥤ D) [RepresentablyCoflat F] :
    PreservesFiniteColimits F :=
  letI _ := preservesFiniteLimits_of_flat F.op
  preservesFiniteColimits_of_op _

/-- If `C` is finitely complete, then `F : C ⥤ D` is representably flat iff it preserves
finite limits.
-/
/-
**CategoryTheory.preservesFiniteLimits_iff_flat** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory`。
形式化陈述：preservesFiniteLimits_iff_flat [HasFiniteLimits C] (F : C ⥤ D) : Represent
ablyFlat F ↔ PreservesFiniteLimits F
参数：F : C ⥤ D。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.preservesFiniteLimits_of_flat`：preservesFiniteLimits_of_f
lat (F : C ⥤ D) [RepresentablyFlat F] : PreservesFiniteLimits F
· 使用定理 `CategoryTheory.flat_of_preservesFiniteLimits`：flat_of_preservesFiniteLim
its [HasFiniteLimits C] (F : C ⥤ D) [PreservesFiniteLimits F] : RepresentablyFla
t F

--- 原说明 ---
If `C` is finitely complete, then `F : C ⥤ D` is representably flat iff it prese
rves
finite limits.
-/
lemma preservesFiniteLimits_iff_flat [HasFiniteLimits C] (F : C ⥤ D) :
    RepresentablyFlat F ↔ PreservesFiniteLimits F :=
  ⟨fun _ ↦ preservesFiniteLimits_of_flat F, fun _ ↦ flat_of_preservesFiniteLimits F⟩

/-- If `C` is finitely cocomplete, then `F : C ⥤ D` is representably coflat iff it preserves
finite colimits. -/
/-
**CategoryTheory.preservesFiniteColimits_iff_coflat** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory`。
形式化陈述：preservesFiniteColimits_iff_coflat [HasFiniteColimits C] (F : C ⥤ D) : Rep
resentablyCoflat F ↔ PreservesFiniteColimits F
参数：F : C ⥤ D。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.preservesFiniteColimits_of_coflat`：preservesFiniteColimit
s_of_coflat (F : C ⥤ D) [RepresentablyCoflat F] : PreservesFiniteColimits F
· 使用定理 `CategoryTheory.coflat_of_preservesFiniteColimits`：coflat_of_preservesFin
iteColimits [HasFiniteColimits C] (F : C ⥤ D) [PreservesFiniteColimits F] : Repr
esentablyCoflat F

--- 原说明 ---
If `C` is finitely cocomplete, then `F : C ⥤ D` is representably coflat iff it p
reserves
finite colimits.
-/
lemma preservesFiniteColimits_iff_coflat [HasFiniteColimits C] (F : C ⥤ D) :
    RepresentablyCoflat F ↔ PreservesFiniteColimits F :=
  ⟨fun _ => preservesFiniteColimits_of_coflat F, fun _ => coflat_of_preservesFiniteColimits F⟩

end HasLimit

section SmallCategory

variable {C D : Type u₁} [SmallCategory C] [SmallCategory D] (E : Type u₂) [Category.{u₁} E]


set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- (Implementation)
The evaluation of `F.lan` at `X` is the colimit over the costructured arrows over `X`.
-/
/-
**CategoryTheory.lanEvaluationIsoColim** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
`。
形式化陈述：lanEvaluationIsoColim (F : C ⥤ D) (X : D) [forall X : D, HasColimitsOfShap
e (CostructuredArrow F X) E] : F.lan ⋙ (evaluation D E).obj X ≅ (Functor.whisker
ingLeft _ _ E).obj (CostructuredArrow.proj F X) ⋙ colim
参数：F : C ⥤ D；X : D；CostructuredArrow F X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(Implementation)
The evaluation of `F.lan` at `X` is the colimit over the costructured arrows ove
r `X`.
-/
noncomputable def lanEvaluationIsoColim (F : C ⥤ D) (X : D)
    [∀ X : D, HasColimitsOfShape (CostructuredArrow F X) E] :
    F.lan ⋙ (evaluation D E).obj X ≅
      (Functor.whiskeringLeft _ _ E).obj (CostructuredArrow.proj F X) ⋙ colim :=
  NatIso.ofComponents (fun G =>
    IsColimit.coconePointUniqueUpToIso
    (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit F G X)
    (colimit.isColimit _)) (fun {G₁ G₂} φ => by
      apply (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit F G₁ X).hom_ext
      intro T
      have h₁ := fun (G : C ⥤ E) => IsColimit.comp_coconePointUniqueUpToIso_hom
        (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit F G X) (colimit.isColimit _) T
      have h₂ := congr_app (F.lanUnit.naturality φ) T.left
      dsimp at h₁ h₂ ⊢
      simp only [Category.assoc] at h₁ ⊢
      simp only [Functor.lan, Functor.lanUnit] at h₂ ⊢
      rw [reassoc_of% h₁, NatTrans.naturality_assoc, ← reassoc_of% h₂, h₁,
        ι_colimMap, Functor.whiskerLeft_app]
      rfl)

variable {FE : E → E → Type*} {CE : E → Type u₁} [∀ X Y, FunLike (FE X Y) (CE X) (CE Y)]
    [ConcreteCategory E FE] [HasLimits E] [HasColimits E]
variable [ReflectsLimits (forget E)] [PreservesFilteredColimits (forget E)]
variable [PreservesLimits (forget E)]

/-- If `F : C ⥤ D` is a representably flat functor between small categories, then the functor
`Lan F.op` that takes presheaves over `C` to presheaves over `D` preserves finite limits.
-/
/-
**CategoryTheory.lan_preservesFiniteLimits_of_flat** 是 Mathlib 中的一个实例，位于命名空间 `Ca
tegoryTheory`。
形式化陈述：lan_preservesFiniteLimits_of_flat (F : C ⥤ D) [RepresentablyFlat F] : Pres
ervesFiniteLimits (F.op.lan : _ ⥤ Dᵒᵖ ⥤ E)
参数：F : C ⥤ D。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesFiniteLimits_of_preservesFiniteLimitsOfSi
ze`：preservesFiniteLimits_of_preservesFiniteLimitsOfSize (F : C ⥤ D) (h : forall
 (J : Type w) {𝒥 : SmallCategory J} (_ : @FinCategory J 𝒥), Pres…
· 使用定理 `CategoryTheory.Functor.instHasLeftKanExtension`：∀ {C : Type u_1} {D : Ty
pe u_2} {H : Type u_4} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 :
 CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.instHasColimitsOfShapeOfHasColimitsOfSize`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : Catego
ryTheory.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用引理 `CategoryTheory.Limits.preservesLimitsOfShape_of_evaluation`：preservesLim
itsOfShape_of_evaluation (F : D ⥤ K ⥤ C) (J : Type*) [Category* J] (_ : forall k
 : K, PreservesLimitsOfShape J (F ⋙ (evaluation …
· 使用定理 `CategoryTheory.IsFiltered.of_equivalence`：of_equivalence (h : C ≌ D) : I
sFiltered D
· 使用定理 `CategoryTheory.RepresentablyFlat.cofiltered`：∀ {C : Type u₁} {inst : Cat
egoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Category
.{v₂, u₂} D}   {F : CategoryTheor…
· 使用引理 `CategoryTheory.Limits.preservesLimitsOfShape_of_natIso`：preservesLimitsO
fShape_of_natIso {F G : C ⥤ D} (h : F ≅ G) [PreservesLimitsOfShape J F] : Preser
vesLimitsOfShape J G where preservesLimit {K…
· 使用定理 `CategoryTheory.Limits.comp_preservesLimitsOfShape`：∀ {C : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Ca
tegory.{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `CategoryTheory.Limits.hasLimitsOfShape_of_hasFiniteLimits`：∀ (C : Type u
) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFiniteLimi
ts C] (J : Type w)   [inst_2 : CategoryTheory.S…
· 使用定理 `CategoryTheory.Limits.hasFiniteLimits_of_hasLimits`：∀ (C : Type u) [inst
 : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasLimits C],   Cate
goryTheory.Limits.HasFiniteLimits C
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `CategoryTheory.Limits.reflectsLimitsOfShape_of_reflectsLimits`：∀ {C : Ty
pe u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Categ
oryTheory.Category.{v₂, u₂} D]   (J : Type w) [inst…
· 使用定理 `CategoryTheory.Limits.PreservesFilteredColimitsOfSize.preserves_filtered
_colimits`：∀ {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type
 u₂} {inst_1 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.preservesLimitsOfShapeOfPreservesFiniteLimits`：∀ {
C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 :
 CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.PreservesLimits.preservesFiniteLimits`：∀ {C : Type
 u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Categor
yTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…

--- 原说明 ---
If `F : C ⥤ D` is a representably flat functor between small categories, then th
e functor
`Lan F.op` that takes presheaves over `C` to presheaves over `D` preserves finit
e limits.
-/
noncomputable instance lan_preservesFiniteLimits_of_flat (F : C ⥤ D) [RepresentablyFlat F] :
    PreservesFiniteLimits (F.op.lan : _ ⥤ Dᵒᵖ ⥤ E) := by
  apply preservesFiniteLimits_of_preservesFiniteLimitsOfSize.{u₁}
  intro J _ _
  apply preservesLimitsOfShape_of_evaluation (F.op.lan : (Cᵒᵖ ⥤ E) ⥤ Dᵒᵖ ⥤ E) J
  intro K
  have : IsFiltered (CostructuredArrow F.op K) :=
    IsFiltered.of_equivalence (structuredArrowOpEquivalence F (unop K))
  exact preservesLimitsOfShape_of_natIso (lanEvaluationIsoColim _ _ _).symm
/-
**CategoryTheory.lan_flat_of_flat** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
形式化陈述：lan_flat_of_flat (F : C ⥤ D) [RepresentablyFlat F] : RepresentablyFlat (F.
op.lan : _ ⥤ Dᵒᵖ ⥤ E)
参数：F : C ⥤ D。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.flat_of_preservesFiniteLimits`：flat_of_preservesFiniteLim
its [HasFiniteLimits C] (F : C ⥤ D) [PreservesFiniteLimits F] : RepresentablyFla
t F
· 使用定理 `CategoryTheory.Limits.hasFiniteLimits_of_hasLimits`：∀ (C : Type u) [inst
 : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasLimits C],   Cate
goryTheory.Limits.HasFiniteLimits C
· 使用定理 `CategoryTheory.Functor.instHasLeftKanExtension`：∀ {C : Type u_1} {D : Ty
pe u_2} {H : Type u_4} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 :
 CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.instHasColimitsOfShapeOfHasColimitsOfSize`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : Catego
ryTheory.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
-/
instance lan_flat_of_flat (F : C ⥤ D) [RepresentablyFlat F] :
    RepresentablyFlat (F.op.lan : _ ⥤ Dᵒᵖ ⥤ E) :=
  flat_of_preservesFiniteLimits _

variable [HasFiniteLimits C]
/-
**CategoryTheory.lan_preservesFiniteLimits_of_preservesFiniteLimits** 是 Mathlib 
中的一个实例，位于命名空间 `CategoryTheory`。
形式化陈述：lan_preservesFiniteLimits_of_preservesFiniteLimits (F : C ⥤ D) [PreservesF
initeLimits F] : PreservesFiniteLimits (F.op.lan : _ ⥤ Dᵒᵖ ⥤ E)
参数：F : C ⥤ D。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.flat_of_preservesFiniteLimits`：flat_of_preservesFiniteLim
its [HasFiniteLimits C] (F : C ⥤ D) [PreservesFiniteLimits F] : RepresentablyFla
t F
· 使用定理 `CategoryTheory.Functor.instHasLeftKanExtension`：∀ {C : Type u_1} {D : Ty
pe u_2} {H : Type u_4} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 :
 CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.instHasColimitsOfShapeOfHasColimitsOfSize`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : Catego
ryTheory.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
-/
instance lan_preservesFiniteLimits_of_preservesFiniteLimits (F : C ⥤ D)
    [PreservesFiniteLimits F] : PreservesFiniteLimits (F.op.lan : _ ⥤ Dᵒᵖ ⥤ E) := by
  have := flat_of_preservesFiniteLimits F
  infer_instance
/-
**CategoryTheory.flat_iff_lan_flat** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：flat_iff_lan_flat (F : C ⥤ D) : RepresentablyFlat F ↔ RepresentablyFlat (F
.op.lan : _ ⥤ Dᵒᵖ ⥤ Type u₁)
参数：F : C ⥤ D。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.instHasLeftKanExtension`：∀ {C : Type u_1} {D : Ty
pe u_2} {H : Type u_4} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 :
 CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `CategoryTheory.Limits.Types.hasLimitsOfSize`：∀ [UnivLE.{v, u}], Category
Theory.Limits.HasLimitsOfSize.{w, v, u, u + 1} (Type u)
· 使用定理 `CategoryTheory.Limits.Types.hasColimitsOfSize`：∀ [UnivLE.{v, u}], Catego
ryTheory.Limits.HasColimitsOfSize.{w, v, u, u + 1} (Type u)
· 使用定理 `CategoryTheory.Types.instReflectsLimitsOfSizeForgetTypeFun`：CategoryTheo
ry.Limits.ReflectsLimitsOfSize.{u_1, u_2, u, u, u + 1, u + 1} (CategoryTheory.fo
rget (Type u))
· 使用定理 `CategoryTheory.Limits.PreservesColimits.preservesFilteredColimits`：∀ {C 
: Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : C
ategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Types.instPreservesColimitsOfSizeForgetTypeFun`：CategoryT
heory.Limits.PreservesColimitsOfSize.{u_1, u_2, u, u, u + 1, u + 1} (CategoryThe
ory.forget (Type u))
· 使用定理 `CategoryTheory.Types.instPreservesLimitsOfSizeForgetTypeFun`：CategoryThe
ory.Limits.PreservesLimitsOfSize.{u_1, u_2, u, u, u + 1, u + 1} (CategoryTheory.
forget (Type u))
· 使用引理 `CategoryTheory.preservesFiniteLimits_of_flat`：preservesFiniteLimits_of_f
lat (F : C ⥤ D) [RepresentablyFlat F] : PreservesFiniteLimits F
· 使用引理 `CategoryTheory.Limits.preservesFiniteLimits_of_preservesFiniteLimitsOfSi
ze`：preservesFiniteLimits_of_preservesFiniteLimitsOfSize (F : C ⥤ D) (h : forall
 (J : Type w) {𝒥 : SmallCategory J} (_ : @FinCategory J 𝒥), Pres…
· 使用引理 `CategoryTheory.preservesLimit_of_lan_preservesLimit`：preservesLimit_of_l
an_preservesLimit {C D : Type u} [SmallCategory C] [SmallCategory D] (F : C ⥤ D)
 (J : Type u) [SmallCategory J] [Preserve…
· 使用定理 `CategoryTheory.Limits.preservesLimitsOfShapeOfPreservesFiniteLimits`：∀ {
C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 :
 CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.flat_of_preservesFiniteLimits`：flat_of_preservesFiniteLim
its [HasFiniteLimits C] (F : C ⥤ D) [PreservesFiniteLimits F] : RepresentablyFla
t F
-/
theorem flat_iff_lan_flat (F : C ⥤ D) :
    RepresentablyFlat F ↔ RepresentablyFlat (F.op.lan : _ ⥤ Dᵒᵖ ⥤ Type u₁) :=
  ⟨fun _ => inferInstance, fun H => by
    have := preservesFiniteLimits_of_flat (F.op.lan : _ ⥤ Dᵒᵖ ⥤ Type u₁)
    have : PreservesFiniteLimits F := by
      apply preservesFiniteLimits_of_preservesFiniteLimitsOfSize.{u₁}
      intros; apply preservesLimit_of_lan_preservesLimit
    apply flat_of_preservesFiniteLimits⟩

/-- If `C` is finitely complete, then `F : C ⥤ D` preserves finite limits iff
`Lan F.op : (Cᵒᵖ ⥤ Type*) ⥤ (Dᵒᵖ ⥤ Type*)` preserves finite limits.
-/
/-
**CategoryTheory.preservesFiniteLimits_iff_lan_preservesFiniteLimits** 是 Mathlib
 中的一个引理，位于命名空间 `CategoryTheory`。
形式化陈述：preservesFiniteLimits_iff_lan_preservesFiniteLimits (F : C ⥤ D) : Preserve
sFiniteLimits F ↔ PreservesFiniteLimits (F.op.lan : _ ⥤ Dᵒᵖ ⥤ Type u₁)
参数：F : C ⥤ D。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.instHasLeftKanExtension`：∀ {C : Type u_1} {D : Ty
pe u_2} {H : Type u_4} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 :
 CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `CategoryTheory.Limits.Types.hasLimitsOfSize`：∀ [UnivLE.{v, u}], Category
Theory.Limits.HasLimitsOfSize.{w, v, u, u + 1} (Type u)
· 使用定理 `CategoryTheory.Limits.Types.hasColimitsOfSize`：∀ [UnivLE.{v, u}], Catego
ryTheory.Limits.HasColimitsOfSize.{w, v, u, u + 1} (Type u)
· 使用定理 `CategoryTheory.Types.instReflectsLimitsOfSizeForgetTypeFun`：CategoryTheo
ry.Limits.ReflectsLimitsOfSize.{u_1, u_2, u, u, u + 1, u + 1} (CategoryTheory.fo
rget (Type u))
· 使用定理 `CategoryTheory.Limits.PreservesColimits.preservesFilteredColimits`：∀ {C 
: Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : C
ategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Types.instPreservesColimitsOfSizeForgetTypeFun`：CategoryT
heory.Limits.PreservesColimitsOfSize.{u_1, u_2, u, u, u + 1, u + 1} (CategoryThe
ory.forget (Type u))
· 使用定理 `CategoryTheory.Types.instPreservesLimitsOfSizeForgetTypeFun`：CategoryThe
ory.Limits.PreservesLimitsOfSize.{u_1, u_2, u, u, u + 1, u + 1} (CategoryTheory.
forget (Type u))
· 使用引理 `CategoryTheory.Limits.preservesFiniteLimits_of_preservesFiniteLimitsOfSi
ze`：preservesFiniteLimits_of_preservesFiniteLimitsOfSize (F : C ⥤ D) (h : forall
 (J : Type w) {𝒥 : SmallCategory J} (_ : @FinCategory J 𝒥), Pres…
· 使用引理 `CategoryTheory.preservesLimit_of_lan_preservesLimit`：preservesLimit_of_l
an_preservesLimit {C D : Type u} [SmallCategory C] [SmallCategory D] (F : C ⥤ D)
 (J : Type u) [SmallCategory J] [Preserve…
· 使用定理 `CategoryTheory.Limits.preservesLimitsOfShapeOfPreservesFiniteLimits`：∀ {
C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 :
 CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…

--- 原说明 ---
If `C` is finitely complete, then `F : C ⥤ D` preserves finite limits iff
`Lan F.op : (Cᵒᵖ ⥤ Type*) ⥤ (Dᵒᵖ ⥤ Type*)` preserves finite limits.
-/
lemma preservesFiniteLimits_iff_lan_preservesFiniteLimits (F : C ⥤ D) :
    PreservesFiniteLimits F ↔ PreservesFiniteLimits (F.op.lan : _ ⥤ Dᵒᵖ ⥤ Type u₁) :=
  ⟨fun _ ↦ inferInstance,
    fun _ ↦ preservesFiniteLimits_of_preservesFiniteLimitsOfSize.{u₁} _
      (fun _ _ _ ↦ preservesLimit_of_lan_preservesLimit _ _)⟩

end SmallCategory

section

variable {C D E : Type*} [Category* C] [Category* D] [Category* E] (F : C ⥤ D) (G : D ⥤ E)

attribute [local instance] IsCofiltered.isConnected IsFiltered.isConnected

/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : E) [RepresentablyFlat F] : (StructuredArrow.pre X F G).Final :=
  ⟨fun _ ↦ isConnected_of_equivalent (StructuredArrow.preEquivalence _ _).symm⟩
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : E) [RepresentablyCoflat F] : (CostructuredArrow.pre F G X).Initial :=
  ⟨fun _ ↦ isConnected_of_equivalent (CostructuredArrow.preEquivalence _ _).symm⟩

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : E) [RepresentablyFlat F] [IsCofiltered (StructuredArrow X G)] :
    IsCofiltered (StructuredArrow X (F ⋙ G)) := by
  let T := StructuredArrow.pre X F G
  obtain ⟨Y⟩ := IsCofiltered.nonempty (C := StructuredArrow X G)
  obtain ⟨A⟩ := IsCofiltered.nonempty (C := StructuredArrow Y.right F)
  have : Nonempty (StructuredArrow X (F ⋙ G)) := ⟨.mk (Y.hom ≫ G.map A.hom)⟩
  suffices IsCofilteredOrEmpty (StructuredArrow X (F ⋙ G)) by constructor
  refine ⟨fun A B ↦ ?_, fun A B f g ↦ ?_⟩
  · let U := IsCofiltered.min (T.obj A) (T.obj B)
    let A' : StructuredArrow U.right F := .mk (IsCofiltered.minToLeft (T.obj A) (T.obj B)).right
    let B' : StructuredArrow U.right F := .mk (IsCofiltered.minToRight (T.obj A) (T.obj B)).right
    refine ⟨.mk <| U.hom ≫ G.map (IsCofiltered.min A' B').hom,
      StructuredArrow.homMk (IsCofiltered.minToLeft A' B').right ?_,
      StructuredArrow.homMk (IsCofiltered.minToRight A' B').right ?_, trivial⟩
    · simp [← Functor.map_comp, A', T]
    · simp [← Functor.map_comp, B', T]
  · let U := IsCofiltered.eq (T.map f) (T.map g)
    let A' : StructuredArrow _ F := .mk (IsCofiltered.eqHom (T.map f) (T.map g)).right
    let B' : StructuredArrow _ F := .mk (IsCofiltered.eqHom (T.map f) (T.map g) ≫ T.map f).right
    let f' : A' ⟶ B' := StructuredArrow.homMk f.right rfl
    let g' : A' ⟶ B' := StructuredArrow.homMk g.right
      congr($(IsCofiltered.eq_condition (T.map f) (T.map g)).right).symm
    refine ⟨.mk <| U.hom ≫ G.map (IsCofiltered.eq f' g').hom,
      StructuredArrow.homMk (IsCofiltered.eqHom f' g').right ?_, ?_⟩
    · simp [← Functor.map_comp, A', T]
    · ext
      exact congr($(IsCofiltered.eq_condition f' g').right)
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : E) [RepresentablyCoflat F] [h : IsFiltered (CostructuredArrow G X)] :
    IsFiltered (CostructuredArrow (F ⋙ G) X) := by
  rw [← isCofiltered_op_iff_isFiltered, IsCofiltered.iff_of_equivalence
    (costructuredArrowOpEquivalence _ _)] at h ⊢
  exact inferInstanceAs <| IsCofiltered (StructuredArrow (op X) (F.op ⋙ G.op))
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (G : D ⥤ Type*) [RepresentablyFlat F] [IsCofiltered G.Elements] :
    IsCofiltered (F ⋙ G).Elements := by
  suffices h : IsCofiltered (StructuredArrow PUnit (F ⋙ G)) from
    .of_equivalence (CategoryOfElements.structuredArrowEquivalence _).symm
  have : IsCofiltered (StructuredArrow PUnit G) :=
    .of_equivalence (CategoryOfElements.structuredArrowEquivalence _)
  infer_instance

end

end CategoryTheory

