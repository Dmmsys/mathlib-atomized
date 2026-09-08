/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Christian Merten
-/
module

public import Mathlib.CategoryTheory.Bicategory.Adjunction.Cat
public import Mathlib.CategoryTheory.Bicategory.LocallyDiscrete
public import Mathlib.CategoryTheory.Monad.Adjunction

/-!
# Descent data as coalgebras

Let `F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Adj Cat` be a pseudofunctor
to the bicategory of adjunctions in `Cat`. In particular,
for any morphism `g : X ⟶ Y` in `C`, we have an
adjunction `(g^*, g_*)` between a pullback functor and a
pushforward functor.

In this file, given a family of morphisms `f i : X i ⟶ S` indexed
by a type `ι` in `C`, we introduce a category `F.DescentDataAsCoalgebra f`
of descent data relative to the morphisms `f i`, where the objects are
described as a family of objects `obj i` over `X i`, and the
morphisms relating them are described as morphisms
`obj i₁ ⟶ (f i₁)^* (f i₂)_* (obj i₂)`, similarly as
Eilenberg-Moore coalgebras. Indeed, when the index type `ι`
contains a unique element, we show that
`F.DescentDataAsCoalgebra (fun (i : ι) ↦ f`
identifies to the category of coalgebras for the comonad attached
to the adjunction `(F.map f.op.toLoc).adj`.

## TODO (@joelriou, @chrisflav)
* Compare `DescentDataAsCoalgebra` with `DescentData` when suitable
  pullbacks exist and certain base change morphisms are isomorphisms

-/

@[expose] public section

universe t v' v u' u

namespace CategoryTheory

open Bicategory Opposite

namespace Pseudofunctor

variable {C : Type u} [Category.{v} C]
  {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Adj Cat.{v', u'}}

variable (F) in
/-- Given a pseudofunctor `F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Adj Cat` and a family
of morphisms `f i : X i ⟶ S` in `C`, this is the category of descent data for `F`
relative to the morphisms `f i` where the objects are defined as coalgebras:
the morphisms relating the various objects `obj i` over `X i` are of the
form `obj i₁ ⟶ (f i₁)^* (f i₂)_* (obj i₂)`. This category can be compared
to the corresponding category `DescentData` when suitable pullbacks exist
and certain base change morphisms are isomorphisms (TODO). -/
/-
**CategoryTheory.Pseudofunctor.DescentDataAsCoalgebra** 是 Mathlib 中的一个结构，位于命名空间 
`CategoryTheory.Pseudofunctor`。
形式化陈述：DescentDataAsCoalgebra {ι : Type t} {S : C} {X : ι -> C} (f : forall i, X 
i ⟶ S) where /-- The objects over `X i` for all `i` -/ obj (i : ι) : (F.obj (.mk
 (op (X i)))).obj /-- The compatibility morphisms. -/ hom (i₁ i₂ : ι) : obj i₁ ⟶
 (F.map (f i₁).op.toLoc).l.toFunctor.obj ((F.map (f i₂).op.toLoc).r.toFunctor.ob
j (obj i₂)) counit (i : ι) : hom i i ≫ (F.map (f i).op.toLoc).adj.counit.toNatTr
ans.app _ = 𝟙 _
参数：f : forall i, X i ⟶ S；i : ι。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a pseudofunctor `F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Adj Cat` and a family
of morphisms `f i : X i ⟶ S` in `C`, this is the category of descent data for `F
`
relative to the morphisms `f i` where the objects are defined as coalgebras:
the morphisms relating the various objects `obj i` over `X i` are of the
form `obj i₁ ⟶ (f i₁)^* (f i₂)_* (obj i₂)`. This category can be compared
to the corresponding category `DescentData` when suitable pullbacks exist
and certain base change morphisms are isomorphisms (TODO).
-/
structure DescentDataAsCoalgebra
    {ι : Type t} {S : C} {X : ι → C} (f : ∀ i, X i ⟶ S) where
  /-- The objects over `X i` for all `i` -/
  obj (i : ι) : (F.obj (.mk (op (X i)))).obj
  /-- The compatibility morphisms. -/
  hom (i₁ i₂ : ι) : obj i₁ ⟶
    (F.map (f i₁).op.toLoc).l.toFunctor.obj
      ((F.map (f i₂).op.toLoc).r.toFunctor.obj (obj i₂))
  counit (i : ι) : hom i i ≫ (F.map (f i).op.toLoc).adj.counit.toNatTrans.app _ = 𝟙 _ := by
    cat_disch
  coassoc (i₁ i₂ i₃ : ι) :
    hom i₁ i₂ ≫ (F.map (f i₁).op.toLoc).l.toFunctor.map
      ((F.map (f i₂).op.toLoc).r.toFunctor.map (hom i₂ i₃)) =
    hom i₁ i₃ ≫
      (F.map (f i₁).op.toLoc).l.toFunctor.map
        ((F.map (f i₂).op.toLoc).adj.unit.toNatTrans.app _) := by cat_disch

namespace DescentDataAsCoalgebra

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
attribute [reassoc (attr := simp)] counit coassoc

section

variable {ι : Type t} {S : C} {X : ι → C} {f : ∀ i, X i ⟶ S}

/-- The type of morphisms in `DescentDataAsCoalgebra`. -/
@[ext]
/-
**CategoryTheory.Pseudofunctor.DescentDataAsCoalgebra.Hom** 是 Mathlib 中的一个结构，位于命
名空间 `CategoryTheory.Pseudofunctor.DescentDataAsCoalgebra`。
形式化陈述：Hom (D₁ D₂ : F.DescentDataAsCoalgebra f) where /-- The morphisms between t
he `obj` fields of descent data. -/ hom (i : ι) : D₁.obj i ⟶ D₂.obj i comm (i₁ i
₂ : ι) : D₁.hom i₁ i₂ ≫ (F.map (f i₁).op.toLoc).l.toFunctor.map ((F.map (f i₂).o
p.toLoc).r.toFunctor.map (hom i₂)) = hom i₁ ≫ D₂.hom i₁ i₂
参数：D₁ D₂ : F.DescentDataAsCoalgebra f；i : ι。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of morphisms in `DescentDataAsCoalgebra`.
-/
structure Hom (D₁ D₂ : F.DescentDataAsCoalgebra f) where
  /-- The morphisms between the `obj` fields of descent data. -/
  hom (i : ι) : D₁.obj i ⟶ D₂.obj i
  comm (i₁ i₂ : ι) :
    D₁.hom i₁ i₂ ≫
      (F.map (f i₁).op.toLoc).l.toFunctor.map
        ((F.map (f i₂).op.toLoc).r.toFunctor.map (hom i₂)) =
    hom i₁ ≫ D₂.hom i₁ i₂ := by cat_disch

attribute [reassoc (attr := simp)] Hom.comm
/-
**CategoryTheory.Pseudofunctor.DescentDataAsCoalgebra.** 是 Mathlib 中的一个实例，位于命名空间
 `CategoryTheory.Pseudofunctor.DescentDataAsCoalgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Category (F.DescentDataAsCoalgebra f) where
  Hom := Hom
  id _ := { hom _ := 𝟙 _ }
  comp f g := { hom i := f.hom i ≫ g.hom i }

@[ext]
/-
**CategoryTheory.Pseudofunctor.DescentDataAsCoalgebra.hom_ext** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory.Pseudofunctor.DescentDataAsCoalgebra`。
形式化陈述：hom_ext {D₁ D₂ : F.DescentDataAsCoalgebra f} {φ φ' : D₁ ⟶ D₂} (h : forall 
i, φ.hom i = φ'.hom i) : φ = φ'
参数：h : forall i, φ.hom i = φ'.hom i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Pseudofunctor.DescentDataAsCoalgebra.Hom.ext`：∀ {C : Type
 u} {inst : CategoryTheory.Category.{v, u} C}   {F :     CategoryTheory.Pseudofu
nctor (CategoryTheory.LocallyDiscrete Cᵒᵖ)       …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
lemma hom_ext {D₁ D₂ : F.DescentDataAsCoalgebra f} {φ φ' : D₁ ⟶ D₂}
    (h : ∀ i, φ.hom i = φ'.hom i) : φ = φ' :=
  Hom.ext (funext h)

@[simp]
/-
**CategoryTheory.Pseudofunctor.DescentDataAsCoalgebra.id_hom** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.Pseudofunctor.DescentDataAsCoalgebra`。
形式化陈述：id_hom (D : F.DescentDataAsCoalgebra f) (i : ι) : Hom.hom (𝟙 D) i = 𝟙 _
参数：D : F.DescentDataAsCoalgebra f；i : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma id_hom (D : F.DescentDataAsCoalgebra f) (i : ι) :
    Hom.hom (𝟙 D) i = 𝟙 _ := rfl

@[reassoc, simp]
/-
**CategoryTheory.Pseudofunctor.DescentDataAsCoalgebra.comp_hom** 是 Mathlib 中的一个引
理，位于命名空间 `CategoryTheory.Pseudofunctor.DescentDataAsCoalgebra`。
形式化陈述：comp_hom {D₁ D₂ D₃ : F.DescentDataAsCoalgebra f} (φ : D₁ ⟶ D₂) (φ' : D₂ ⟶ 
D₃) (i : ι) : (φ ≫ φ').hom i = φ.hom i ≫ φ'.hom i
参数：φ : D₁ ⟶ D₂；φ' : D₂ ⟶ D₃；i : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma comp_hom {D₁ D₂ D₃ : F.DescentDataAsCoalgebra f} (φ : D₁ ⟶ D₂) (φ' : D₂ ⟶ D₃) (i : ι) :
    (φ ≫ φ').hom i = φ.hom i ≫ φ'.hom i := rfl

/-- Constructor for isomorphisms in `DescentDataAsCoalgebra`. -/
@[simps]
/-
**CategoryTheory.Pseudofunctor.DescentDataAsCoalgebra.isoMk** 是 Mathlib 中的一个定义，位
于命名空间 `CategoryTheory.Pseudofunctor.DescentDataAsCoalgebra`。
形式化陈述：isoMk {D₁ D₂ : F.DescentDataAsCoalgebra f} (e : forall (i : ι), D₁.obj i ≅
 D₂.obj i) (comm : forall (i₁ i₂ : ι), D₁.hom i₁ i₂ ≫ (F.map (f i₁).op.toLoc).l.
toFunctor.map ((F.map (f i₂).op.toLoc).r.toFunctor.map (e i₂).hom) = (e i₁).hom 
≫ D₂.hom i₁ i₂
参数：e : forall (i : ι), D₁.obj i ≅ D₂.obj i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for isomorphisms in `DescentDataAsCoalgebra`.
-/
def isoMk {D₁ D₂ : F.DescentDataAsCoalgebra f} (e : ∀ (i : ι), D₁.obj i ≅ D₂.obj i)
    (comm : ∀ (i₁ i₂ : ι), D₁.hom i₁ i₂ ≫
      (F.map (f i₁).op.toLoc).l.toFunctor.map ((F.map (f i₂).op.toLoc).r.toFunctor.map (e i₂).hom) =
      (e i₁).hom ≫ D₂.hom i₁ i₂ := by cat_disch) :
    D₁ ≅ D₂ where
  hom.hom i := (e i).hom
  hom.comm := comm
  inv.hom i := (e i).inv
  inv.comm i₁ i₂ := by
    rw [← cancel_epi (e i₁).hom, ← reassoc_of% (comm i₁ i₂), ← Functor.map_comp, ← Functor.map_comp]
    simp

end

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
variable (F) in
/-- When the index type `ι` contains a unique element, the category
`DescentDataAsCoalgebra` identifies to the category of coalgebras
over the comonad corresponding to the adjunction
`(F.map f.op.toLoc).adj`. -/
@[simps! functor_obj_A functor_obj_a functor_map_f inverse_obj_obj inverse_obj_hom
  inverse_map_hom counitIso_hom_app_f counitIso_inv_app_f,
  simps! -isSimp unitIso_hom_app_hom unitIso_inv_app_hom]
/-
**CategoryTheory.Pseudofunctor.DescentDataAsCoalgebra.coalgebraEquivalence** 是 M
athlib 中的一个定义，位于命名空间 `CategoryTheory.Pseudofunctor.DescentDataAsCoalgebra`。
形式化陈述：coalgebraEquivalence (ι : Type*) [Unique ι] {X S : C} (f : X ⟶ S) : F.Desc
entDataAsCoalgebra (fun (_ : ι) => f) ≌ (Adjunction.ofCat (F.map f.op.toLoc).adj
).toComonad.Coalgebra where functor.obj D
参数：ι : Type*；f : X ⟶ S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def coalgebraEquivalence (ι : Type*) [Unique ι] {X S : C} (f : X ⟶ S) :
    F.DescentDataAsCoalgebra (fun (_ : ι) ↦ f) ≌
    (Adjunction.ofCat (F.map f.op.toLoc).adj).toComonad.Coalgebra where
  functor.obj D :=
    { A := D.obj default
      a := D.hom default default }
  functor.map φ := { f := φ.hom default }
  inverse.obj A :=
    { obj _ := A.A
      hom _ _ := A.a
      counit _ := A.counit
      coassoc _ _ _ := A.coassoc.symm }
  inverse.map φ :=
    { hom i := φ.f
      comm _ _ := φ.h }
  unitIso :=
    NatIso.ofComponents
      (fun D ↦ isoMk (fun i ↦ eqToIso (congr_arg D.obj (by subsingleton)))
        (fun i₁ i₂ ↦ by
          obtain rfl := Subsingleton.elim i₁ default
          obtain rfl := Subsingleton.elim i₂ default
          simp)) (fun {D₁ D₂} α ↦ by
      ext i
      obtain rfl := Subsingleton.elim i default
      simp)
  counitIso := Iso.refl _

end DescentDataAsCoalgebra

set_option backward.isDefEq.respectTransparency false in
variable (F) in
/-- The functor `(F.obj (.mk (op S))).obj ⥤ F.DescentDataAsCoalgebra f`
when `f i : X i ⟶ S` is a family of morphisms. -/
@[simps]
/-
**CategoryTheory.Pseudofunctor.toDescentDataAsCoalgebra** 是 Mathlib 中的一个定义，位于命名空
间 `CategoryTheory.Pseudofunctor`。
形式化陈述：toDescentDataAsCoalgebra {ι : Type t} {S : C} {X : ι -> C} (f : forall i, 
X i ⟶ S) : (F.obj (.mk (op S))).obj ⥤ F.DescentDataAsCoalgebra f where obj M
参数：f : forall i, X i ⟶ S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `(F.obj (.mk (op S))).obj ⥤ F.DescentDataAsCoalgebra f`
when `f i : X i ⟶ S` is a family of morphisms.
-/
def toDescentDataAsCoalgebra
    {ι : Type t} {S : C} {X : ι → C} (f : ∀ i, X i ⟶ S) :
    (F.obj (.mk (op S))).obj ⥤ F.DescentDataAsCoalgebra f where
  obj M :=
    { obj i := (F.map (f i).op.toLoc).l.toFunctor.obj M
      hom i₁ i₂ :=
        (F.map (f i₁).op.toLoc).l.toFunctor.map
          ((F.map (f i₂).op.toLoc).adj.unit.toNatTrans.app _)
      coassoc i₁ i₂ i₃ := by
        rw [← Functor.map_comp, ← Functor.map_comp, Adj.unit_naturality] }
  map g :=
    { hom i := (F.map (f i).op.toLoc).l.toFunctor.map g
      comm i₁ i₂ := by simp [← Functor.map_comp] }

section

variable (ι : Type*) [Unique ι] {X S : C} (f : X ⟶ S)

/-- When `ι` contains a unique element and `f : X ⟶ S` is a morphism,
the composition of `F.toDescentDataAsCoalgebra (fun (_ : ι) ↦ f)`
and the functor of the equivalence
`DescentDataAsCoalgebra.coalgebraEquivalence F ι f` identifies to
`Comonad.comparison` applied to the adjunction corresponding to
`F.map f.op.toLoc`. -/
@[simps!]
/-
**CategoryTheory.Pseudofunctor.toDescentDataAsCoalgebraCompCoalgebraEquivalenceF
unctorIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Pseudofunctor`。
形式化陈述：toDescentDataAsCoalgebraCompCoalgebraEquivalenceFunctorIso (ι : Type*) [Un
ique ι] {X S : C} (f : X ⟶ S) : F.toDescentDataAsCoalgebra (fun (_ : ι) => f) ⋙ 
(DescentDataAsCoalgebra.coalgebraEquivalence F ι f).functor ≅ Comonad.comparison
 (Adjunction.ofCat (F.map f.op.toLoc).adj)
参数：ι : Type*；f : X ⟶ S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `ι` contains a unique element and `f : X ⟶ S` is a morphism,
the composition of `F.toDescentDataAsCoalgebra (fun (_ : ι) ↦ f)`
and the functor of the equivalence
`DescentDataAsCoalgebra.coalgebraEquivalence F ι f` identifies to
`Comonad.comparison` applied to the adjunction corresponding to
`F.map f.op.toLoc`.
-/
def toDescentDataAsCoalgebraCompCoalgebraEquivalenceFunctorIso
    (ι : Type*) [Unique ι] {X S : C} (f : X ⟶ S) :
    F.toDescentDataAsCoalgebra (fun (_ : ι) ↦ f) ⋙
      (DescentDataAsCoalgebra.coalgebraEquivalence F ι f).functor ≅
    Comonad.comparison (Adjunction.ofCat (F.map f.op.toLoc).adj) :=
  Iso.refl _
/-
**CategoryTheory.Pseudofunctor.isEquivalence_toDescentDataAsCoalgebra_iff_isEqui
valence_comonadComparison** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Pseudofuncto
r`。
形式化陈述：isEquivalence_toDescentDataAsCoalgebra_iff_isEquivalence_comonadComparison
 : (F.toDescentDataAsCoalgebra (fun (_ : ι) => f)).IsEquivalence ↔ (Comonad.comp
arison (Adjunction.ofCat (F.map f.op.toLoc).adj)).IsEquivalence
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.Functor.isEquivalence_iff_of_iso`：isEquivalence_iff_of_is
o {F G : C ⥤ D} (e : F ≅ G) : F.IsEquivalence ↔ G.IsEquivalence
· 使用定理 `CategoryTheory.Functor.isEquivalence_trans`：∀ {C : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.
{v₂, u₂} D]   {E : Type u₃} [ins…
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_functor`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.fun…
· 使用引理 `CategoryTheory.Functor.isEquivalence_of_comp_right`：isEquivalence_of_com
p_right {E : Type*} [Category* E] (F : C ⥤ D) (G : D ⥤ E) [IsEquivalence G] [IsE
quivalence (F ⋙ G)] : IsEquivalence F
-/
lemma isEquivalence_toDescentDataAsCoalgebra_iff_isEquivalence_comonadComparison :
    (F.toDescentDataAsCoalgebra (fun (_ : ι) ↦ f)).IsEquivalence ↔
    (Comonad.comparison (Adjunction.ofCat (F.map f.op.toLoc).adj)).IsEquivalence := by
  rw [← Functor.isEquivalence_iff_of_iso
    (F.toDescentDataAsCoalgebraCompCoalgebraEquivalenceFunctorIso ι f)]
  exact ⟨fun _ ↦ inferInstance, fun _ ↦
    Functor.isEquivalence_of_comp_right _
      ((DescentDataAsCoalgebra.coalgebraEquivalence F ι f).functor)⟩

end

end Pseudofunctor

end CategoryTheory

