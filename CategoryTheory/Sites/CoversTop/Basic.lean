/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Sites.Sheaf

/-! # Objects which cover the terminal object

In this file, given a site `(C, J)`, we introduce the notion of a family
of objects `Y : I → C` which "cover the final object": this means
that for all `X : C`, the sieve `Sieve.ofObjects Y X` is covering for `J`.
When there is a terminal object `X : C`, then `J.CoversTop Y`
holds iff `Sieve.ofObjects Y X` is covering for `J`.

We introduce a notion of compatible family of elements on objects `Y`
and obtain `Presheaf.FamilyOfElementsOnObjects.IsCompatible.existsUnique_section`
which asserts that if a presheaf of types is a sheaf, then any compatible
family of elements on objects `Y` which cover the final object extends to
a section of this presheaf.

-/

@[expose] public section

universe w v' v u' u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {A : Type u'} [Category.{v'} A]

namespace GrothendieckTopology

/-- A family of objects `Y : I → C` "covers the final object"
if for all `X : C`, the sieve `ofObjects Y X` is a covering sieve. -/
/-
**CategoryTheory.GrothendieckTopology.CoversTop** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.GrothendieckTopology`。
形式化陈述：CoversTop {I : Type*} (Y : I -> C) : Prop
参数：Y : I -> C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A family of objects `Y : I → C` "covers the final object"
if for all `X : C`, the sieve `ofObjects Y X` is a covering sieve.
-/
def CoversTop {I : Type*} (Y : I → C) : Prop :=
  ∀ (X : C), Sieve.ofObjects Y X ∈ J X
/-
**CategoryTheory.GrothendieckTopology.coversTop_iff_of_isTerminal** 是 Mathlib 中的
一个引理，位于命名空间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：coversTop_iff_of_isTerminal (X : C) (hX : IsTerminal X) {I : Type*} (Y : I
 -> C) : J.CoversTop Y ↔ Sieve.ofObjects Y X in J X
参数：X : C；hX : IsTerminal X；Y : I -> C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrothendieckTopology.superset_covering`：superset_covering
 (Hss : S <= R) (sjx : S in J X) : R in J X
· 使用定理 `CategoryTheory.GrothendieckTopology.pullback_stable`：pullback_stable (f 
: Y ⟶ X) (hS : S in J X) : S.pullback f in J Y
-/
lemma coversTop_iff_of_isTerminal (X : C) (hX : IsTerminal X)
    {I : Type*} (Y : I → C) :
    J.CoversTop Y ↔ Sieve.ofObjects Y X ∈ J X := by
  constructor
  · tauto
  · intro h W
    apply J.superset_covering _ (J.pullback_stable (hX.from W) h)
    rintro T a ⟨i, ⟨b⟩⟩
    exact ⟨i, ⟨b⟩⟩

namespace CoversTop

variable {J}
variable {I : Type*} {Y : I → C} (hY : J.CoversTop Y)
include hY

/-- The cover of any object `W : C` attached to a family of objects `Y` that satisfy
`J.CoversTop Y` -/
/-
**CategoryTheory.GrothendieckTopology.CoversTop.cover** 是 Mathlib 中的一个缩写定义，位于命名空
间 `CategoryTheory.GrothendieckTopology.CoversTop`。
形式化陈述：cover (W : C) : Cover J W
参数：W : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cover of any object `W : C` attached to a family of objects `Y` that satisfy
`J.CoversTop Y`
-/
abbrev cover (W : C) : Cover J W := ⟨Sieve.ofObjects Y W, hY W⟩
/-
**CategoryTheory.GrothendieckTopology.CoversTop.ext** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.GrothendieckTopology.CoversTop`。
形式化陈述：ext (F : Sheaf J A) {c : Cone F.1} (hc : IsLimit c) {X : A} {f g : X ⟶ c.p
t} (h : forall (i : I), f ≫ c.π.app (Opposite.op (Y i)) = g ≫ c.π.app (Opposite.
op (Y i))) : f = g
参数：F : Sheaf J A；hc : IsLimit c；h : forall (i : I), f ≫ c.π.app (Opposite.op (Y 
i)) = g ≫ c.π.app (Opposite.op (Y i))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsLimit.hom_ext`：hom_ext (h : IsLimit t) {W : C} {
f f' : W ⟶ t.pt} (w : forall j, f ≫ t.π.app j = f' ≫ t.π.app j) : f = f'
· 使用定理 `CategoryTheory.Presheaf.IsSheaf.hom_ext`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {J : CategoryTheory.GrothendieckTopology C} {A : Ty
pe u₂}   [inst_1 : CategoryTh…
· 使用定理 `CategoryTheory.ObjectProperty.FullSubcategory.property`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.ObjectProperty C}  
 (self : P.FullSubcategory), P self.obj
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.Cone.w`：∀ {J : Type u₁} [inst : CategoryTheory.Cat
egory.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃} C]   
{F : CategoryTheor…
· 使用定理 `CategoryTheory.eq_whisker`：eq_whisker {f g : X ⟶ Y} (w : f = g) (h : Y ⟶
 Z) : f ≫ h = g ≫ h
-/
lemma ext (F : Sheaf J A) {c : Cone F.1} (hc : IsLimit c) {X : A} {f g : X ⟶ c.pt}
    (h : ∀ (i : I), f ≫ c.π.app (Opposite.op (Y i)) =
      g ≫ c.π.app (Opposite.op (Y i))) :
    f = g := by
  refine hc.hom_ext (fun Z => F.2.hom_ext (hY.cover Z.unop) _ _ ?_)
  rintro ⟨W, a, ⟨i, ⟨b⟩⟩⟩
  simpa using h i =≫ F.1.map b.op
/-
**CategoryTheory.GrothendieckTopology.CoversTop.sections_ext** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.GrothendieckTopology.CoversTop`。
形式化陈述：sections_ext (F : Sheaf J Type*) {x y : F.1.sections} (h : forall (i : I),
 x.1 (Opposite.op (Y i)) = y.1 (Opposite.op (Y i))) : x = y
参数：F : Sheaf J Type*；h : forall (i : I), x.1 (Opposite.op (Y i)) = y.1 (Opposite
.op (Y i))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.Presieve.IsSeparatedFor.ext`：∀ {C : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} C] {P : CategoryTheory.Functor Cᵒᵖ (Type w)} {X : C
}   {R : CategoryTheory.Presieve…
· 使用定理 `CategoryTheory.Presieve.IsSheaf.isSeparated`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {J : CategoryTheory.GrothendieckTopology C}   {P :
 CategoryTheory.Functor Cᵒᵖ (Type…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.isSheaf_iff_isSheaf_of_type`：isSheaf_iff_isSheaf_of_type 
(P : Cᵒᵖ ⥤ Type w) : Presheaf.IsSheaf J P ↔ Presieve.IsSheaf J P
· 使用定理 `CategoryTheory.ObjectProperty.FullSubcategory.property`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.ObjectProperty C}  
 (self : P.FullSubcategory), P self.obj
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Functor.sections_property`：sections_property {F : J ⥤ Typ
e w} (s : F.sections) {j j' : J} (f : j ⟶ j') : F.map f (s.val j) = s.val j'
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
lemma sections_ext (F : Sheaf J Type*) {x y : F.1.sections}
    (h : ∀ (i : I), x.1 (Opposite.op (Y i)) = y.1 (Opposite.op (Y i))) :
    x = y := by
  ext W
  apply (((isSheaf_iff_isSheaf_of_type _ _).1 F.2).isSeparated _ (hY W.unop)).ext
  rintro T a ⟨i, ⟨b⟩⟩
  simpa using congr_arg (F.1.map b.op) (h i)

end CoversTop

end GrothendieckTopology

namespace Presheaf

variable (F : Cᵒᵖ ⥤ Type w) {I : Type*} (Y : I → C)

/-- A family of elements of a presheaf of types `F` indexed by a family of objects
`Y : I → C` consists of the data of an element in `F.obj (Opposite.op (Y i))` for all `i`. -/
/-
**CategoryTheory.Presheaf.FamilyOfElementsOnObjects** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Presheaf`。
形式化陈述：FamilyOfElementsOnObjects
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A family of elements of a presheaf of types `F` indexed by a family of objects
`Y : I → C` consists of the data of an element in `F.obj (Opposite.op (Y i))` fo
r all `i`.
-/
def FamilyOfElementsOnObjects := ∀ (i : I), F.obj (Opposite.op (Y i))

namespace FamilyOfElementsOnObjects

variable {F Y}
variable (x : FamilyOfElementsOnObjects F Y)

/-- `x : FamilyOfElementsOnObjects F Y` is compatible if for any object `Z` such that
there exists a morphism `f : Z → Y i`, then the pullback of `x i` by `f` is independent
of `f` and `i`. -/
/-
**CategoryTheory.Presheaf.FamilyOfElementsOnObjects.IsCompatible** 是 Mathlib 中的一
个定义，位于命名空间 `CategoryTheory.Presheaf.FamilyOfElementsOnObjects`。
形式化陈述：IsCompatible (x : FamilyOfElementsOnObjects F Y) : Prop
参数：x : FamilyOfElementsOnObjects F Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`x : FamilyOfElementsOnObjects F Y` is compatible if for any object `Z` such tha
t
there exists a morphism `f : Z → Y i`, then the pullback of `x i` by `f` is inde
pendent
of `f` and `i`.
-/
def IsCompatible (x : FamilyOfElementsOnObjects F Y) : Prop :=
  ∀ (Z : C) (i j : I) (f : Z ⟶ Y i) (g : Z ⟶ Y j),
    F.map f.op (x i) = F.map g.op (x j)

/-- A family of elements indexed by `Sieve.ofObjects Y X` that is induced by
`x : FamilyOfElementsOnObjects F Y`. See the equational lemma
`IsCompatible.familyOfElements_apply` which holds under the assumption `x.IsCompatible`. -/
/-
**CategoryTheory.Presheaf.FamilyOfElementsOnObjects.familyOfElements** 是 Mathlib
 中的一个定义，位于命名空间 `CategoryTheory.Presheaf.FamilyOfElementsOnObjects`。
形式化陈述：familyOfElements (X : C) : Presieve.FamilyOfElements F (Sieve.ofObjects Y 
X).arrows
参数：X : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A family of elements indexed by `Sieve.ofObjects Y X` that is induced by
`x : FamilyOfElementsOnObjects F Y`. See the equational lemma
`IsCompatible.familyOfElements_apply` which holds under the assumption `x.IsComp
atible`.
-/
noncomputable def familyOfElements (X : C) :
    Presieve.FamilyOfElements F (Sieve.ofObjects Y X).arrows :=
  fun _ _ hf => F.map hf.choose_spec.some.op (x _)

namespace IsCompatible

variable {x}

/-
**CategoryTheory.Presheaf.FamilyOfElementsOnObjects.IsCompatible.familyOfElement
s_apply** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Presheaf.FamilyOfElementsOnObj
ects.IsCompatible`。
形式化陈述：familyOfElements_apply (hx : x.IsCompatible) {X Z : C} (f : Z ⟶ X) (i : I)
 (φ : Z ⟶ Y i) : familyOfElements x X f ⟨i, ⟨φ⟩⟩ = F.map φ.op (x i)
参数：hx : x.IsCompatible；f : Z ⟶ X；i : I；φ : Z ⟶ Y i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma familyOfElements_apply (hx : x.IsCompatible) {X Z : C} (f : Z ⟶ X) (i : I) (φ : Z ⟶ Y i) :
    familyOfElements x X f ⟨i, ⟨φ⟩⟩ = F.map φ.op (x i) := by
  apply hx
/-
**CategoryTheory.Presheaf.FamilyOfElementsOnObjects.IsCompatible.familyOfElement
s_isCompatible** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Presheaf.FamilyOfElemen
tsOnObjects.IsCompatible`。
形式化陈述：familyOfElements_isCompatible (hx : x.IsCompatible) (X : C) : (familyOfEle
ments x X).Compatible
参数：hx : x.IsCompatible；X : C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Presheaf.FamilyOfElementsOnObjects.IsCompatible.familyOfE
lements_apply`：familyOfElements_apply (hx : x.IsCompatible) {X Z : C} (f : Z ⟶ X
) (i : I) (φ : Z ⟶ Y i) : familyOfElements x X f ⟨i, ⟨φ⟩⟩ = F.map φ.op (x i…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `CategoryTheory.types_congr_hom`：types_congr_hom {X Y : Type u} {f g : X 
⟶ Y} (h : f = g) (x : X) : f x = g x
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
-/
lemma familyOfElements_isCompatible (hx : x.IsCompatible) (X : C) :
    (familyOfElements x X).Compatible := by
  intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ ⟨i₁, ⟨φ₁⟩⟩ ⟨i₂, ⟨φ₂⟩⟩ _
  simpa [hx.familyOfElements_apply f₁ i₁ φ₁,
    hx.familyOfElements_apply f₂ i₂ φ₂] using hx Z i₁ i₂ (g₁ ≫ φ₁) (g₂ ≫ φ₂)

variable {J}
/-
**CategoryTheory.Presheaf.FamilyOfElementsOnObjects.IsCompatible.existsUnique_se
ction** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Presheaf.FamilyOfElementsOnObjec
ts.IsCompatible`。
形式化陈述：existsUnique_section (hx : x.IsCompatible) (hY : J.CoversTop Y) (hF : IsSh
eaf J F) : exists! (s : F.sections), forall (i : I), s.1 (Opposite.op (Y i)) = x
 i
参数：hx : x.IsCompatible；hY : J.CoversTop Y；hF : IsSheaf J F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.isSheaf_iff_isSheaf_of_type`：isSheaf_iff_isSheaf_of_type 
(P : Cᵒᵖ ⥤ Type w) : Presheaf.IsSheaf J P ↔ Presieve.IsSheaf J P
· 使用定理 `existsUnique_of_exists_of_unique`：existsUnique_of_exists_of_unique {p : 
α -> Prop} (hex : exists x, p x) (hunique : forall y₁ y₂, p y₁ -> p y₂ -> y₁ = y
₂) : exists! x, p x
· 使用引理 `CategoryTheory.Presheaf.FamilyOfElementsOnObjects.IsCompatible.familyOfE
lements_isCompatible`：familyOfElements_isCompatible (hx : x.IsCompatible) (X : C
) : (familyOfElements x X).Compatible
· 使用定理 `CategoryTheory.Presieve.IsSheafFor.valid_glue`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {P : CategoryTheory.Functor Cᵒᵖ (Type w)} {X 
Y : C}   {R : CategoryTheory.Presie…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.types_congr_hom`：types_congr_hom {X Y : Type u} {f g : X 
⟶ Y} (h : f = g) (x : X) : f x = g x
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用引理 `CategoryTheory.Presheaf.FamilyOfElementsOnObjects.IsCompatible.familyOfE
lements_apply`：familyOfElements_apply (hx : x.IsCompatible) {X Z : C} (f : Z ⟶ X
) (i : I) (φ : Z ⟶ Y i) : familyOfElements x X f ⟨i, ⟨φ⟩⟩ = F.map φ.op (x i…
· 使用定理 `CategoryTheory.Presieve.IsSeparatedFor.ext`：∀ {C : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} C] {P : CategoryTheory.Functor Cᵒᵖ (Type w)} {X : C
}   {R : CategoryTheory.Presieve…
· 使用定理 `CategoryTheory.Presieve.IsSheaf.isSeparated`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {J : CategoryTheory.GrothendieckTopology C}   {P :
 CategoryTheory.Functor Cᵒᵖ (Type…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.op_comp`：op_comp {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} : (f
 ≫ g).op = g.op ≫ f.op
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.id_apply`：∀ {C : Type u} [inst : CategoryTheory.Category.
{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → FunL
ike (FC X Y) …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CategoryTheory.GrothendieckTopology.CoversTop.sections_ext`：sections_ext
 (F : Sheaf J Type*) {x y : F.1.sections} (h : forall (i : I), x.1 (Opposite.op 
(Y i)) = y.1 (Opposite.op (Y i))) : x = y
-/
lemma existsUnique_section (hx : x.IsCompatible) (hY : J.CoversTop Y) (hF : IsSheaf J F) :
    ∃! (s : F.sections), ∀ (i : I), s.1 (Opposite.op (Y i)) = x i := by
  have H := (isSheaf_iff_isSheaf_of_type _ _).1 hF
  apply existsUnique_of_exists_of_unique
  · let s := fun (X : C) => (H _ (hY X)).amalgamate _
      (hx.familyOfElements_isCompatible X)
    have hs : ∀ {X : C} (i : I) (f : X ⟶ Y i), s X = F.map f.op (x i) := fun {X} i f => by
      have h := Presieve.IsSheafFor.valid_glue (H _ (hY X))
          (hx.familyOfElements_isCompatible _) (𝟙 _) ⟨i, ⟨f⟩⟩
      simp only [op_id, F.map_id, types_id_apply] at h
      exact h.trans (hx.familyOfElements_apply _ _ _)
    have hs' : ∀ {W X : C} (a : W ⟶ X) (i : I) (_ : W ⟶ Y i), F.map a.op (s X) = s W := by
      intro W X a i b
      rw [hs i b]
      exact (Presieve.IsSheafFor.valid_glue (H _ (hY X))
        (hx.familyOfElements_isCompatible _) a ⟨i, ⟨b⟩⟩).trans (familyOfElements_apply hx _ _ _)
    refine ⟨⟨fun X => s X.unop, ?_⟩, fun i => (hs i (𝟙 (Y i))).trans (by simp)⟩
    rintro ⟨Y₁⟩ ⟨Y₂⟩ ⟨f : Y₂ ⟶ Y₁⟩
    change F.map f.op (s Y₁) = s Y₂
    apply (H.isSeparated _ (hY Y₂)).ext
    rintro Z φ ⟨i, ⟨g⟩⟩
    rw [hs' φ i g, ← hs' (φ ≫ f) i g, op_comp, F.map_comp]
    rfl
  · intro y₁ y₂ hy₁ hy₂
    exact hY.sections_ext ⟨F, hF⟩ (fun i => by rw [hy₁, hy₂])

variable (hx : x.IsCompatible) (hY : J.CoversTop Y) (hF : IsSheaf J F)

/-- The section of a sheaf of types which lifts a compatible family of elements indexed
by objects which cover the terminal object. -/
/-
**CategoryTheory.Presheaf.FamilyOfElementsOnObjects.IsCompatible.section_** 是 Ma
thlib 中的一个定义，位于命名空间 `CategoryTheory.Presheaf.FamilyOfElementsOnObjects.IsCompati
ble`。
形式化陈述：section_ : F.sections
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Presheaf.FamilyOfElementsOnObjects.IsCompatible.existsUni
que_section`：existsUnique_section (hx : x.IsCompatible) (hY : J.CoversTop Y) (hF
 : IsSheaf J F) : exists! (s : F.sections), forall (i : I), s.1 (Opposite…

--- 原说明 ---
The section of a sheaf of types which lifts a compatible family of elements inde
xed
by objects which cover the terminal object.
-/
noncomputable def section_ : F.sections := (hx.existsUnique_section hY hF).choose

@[simp]
/-
**CategoryTheory.Presheaf.FamilyOfElementsOnObjects.IsCompatible.section_apply**
 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Presheaf.FamilyOfElementsOnObjects.IsCo
mpatible`。
形式化陈述：section_apply (i : I) : (hx.section_ hY hF).1 (Opposite.op (Y i)) = x i
参数：i : I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `CategoryTheory.Presheaf.FamilyOfElementsOnObjects.IsCompatible.existsUni
que_section`：existsUnique_section (hx : x.IsCompatible) (hY : J.CoversTop Y) (hF
 : IsSheaf J F) : exists! (s : F.sections), forall (i : I), s.1 (Opposite…
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
lemma section_apply (i : I) : (hx.section_ hY hF).1 (Opposite.op (Y i)) = x i :=
  (hx.existsUnique_section hY hF).choose_spec.1 i

end IsCompatible

end FamilyOfElementsOnObjects

end Presheaf

end CategoryTheory

