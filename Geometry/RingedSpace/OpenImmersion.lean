/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Topology.Category.TopCat.Limits.Pullbacks
public import Mathlib.Geometry.RingedSpace.LocallyRingedSpace

/-!
# Open immersions of structured spaces

We say that a morphism of presheafed spaces `f : X ⟶ Y` is an open immersion if
the underlying map of spaces is an open embedding `f : X ⟶ U ⊆ Y`,
and the sheaf map `Y(V) ⟶ f _* X(V)` is an iso for each `V ⊆ U`.

Abbreviations are also provided for `SheafedSpace`, `LocallyRingedSpace` and `Scheme`.

## Main definitions

* `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion`: the `Prop`-valued typeclass asserting
  that a PresheafedSpace hom `f` is an open immersion.
* `AlgebraicGeometry.IsOpenImmersion`: the `Prop`-valued typeclass asserting
  that a Scheme morphism `f` is an open immersion.
* `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.isoRestrict`: The source of an
  open immersion is isomorphic to the restriction of the target onto the image.
* `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.lift`: Any morphism whose range is
  contained in an open immersion factors through the open immersion.
* `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.toSheafedSpace`: If `f : X ⟶ Y` is an
  open immersion of presheafed spaces, and `Y` is a sheafed space, then `X` is also a sheafed
  space. The morphism as morphisms of sheafed spaces is given by `toSheafedSpaceHom`.
* `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.toLocallyRingedSpace`: If `f : X ⟶ Y` is
  an open immersion of presheafed spaces, and `Y` is a locally ringed space, then `X` is also a
  locally ringed space. The morphism as morphisms of locally ringed spaces is given by
  `toLocallyRingedSpaceHom`.

## Main results

* `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.comp`: The composition of two open
  immersions is an open immersion.
* `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.ofIso`: An iso is an open immersion.
* `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.to_iso`:
  A surjective open immersion is an isomorphism.
* `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.stalk_iso`: An open immersion induces
  an isomorphism on stalks.
* `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.hasPullback_of_left`: If `f` is an open
  immersion, then the pullback `(f, g)` exists (and the forgetful functor to `TopCat` preserves it).
* `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.pullbackSndOfLeft`: Open immersions
  are stable under pullbacks.
* `AlgebraicGeometry.SheafedSpace.IsOpenImmersion.of_stalk_iso`: A (topological) open embedding
  between two sheafed spaces is an open immersion if all the stalk maps are isomorphisms.

-/

@[expose] public section


open TopologicalSpace CategoryTheory Opposite Topology

open CategoryTheory.Limits

namespace AlgebraicGeometry

universe w v v₁ v₂ u

variable {C : Type u} [Category.{v} C]

/-- An open immersion of PresheafedSpaces is an open embedding `f : X ⟶ U ⊆ Y` of the underlying
spaces, such that the sheaf map `Y(V) ⟶ f _* X(V)` is an iso for each `V ⊆ U`.
-/
/-
**AlgebraicGeometry.PresheafedSpace.IsOpenImmersion** 是 Mathlib 中的一个归纳类型，位于命名空间 
`AlgebraicGeometry.PresheafedSpace`。
形式化陈述：{C : Type u} → [inst : CategoryTheory.Category.{v, u} C] → {X Y : Algebrai
cGeometry.PresheafedSpace C} → (X ⟶ Y) → Prop
参数：X ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An open immersion of PresheafedSpaces is an open embedding `f : X ⟶ U ⊆ Y` of th
e underlying
spaces, such that the sheaf map `Y(V) ⟶ f _* X(V)` is an iso for each `V ⊆ U`.
-/
class PresheafedSpace.IsOpenImmersion {X Y : PresheafedSpace C} (f : X ⟶ Y) : Prop where
  /-- the underlying continuous map of underlying spaces from the source to an open subset of the
  target. -/
  base_open : IsOpenEmbedding f.base
  /-- the underlying sheaf morphism is an isomorphism on each open subset -/
  c_iso : ∀ U : Opens X, IsIso (f.c.app (op (base_open.functor.obj U)))

/-- A morphism of SheafedSpaces is an open immersion if it is an open immersion as a morphism
of PresheafedSpaces
-/
/-
**AlgebraicGeometry.SheafedSpace.IsOpenImmersion** 是 Mathlib 中的一个定义，位于命名空间 `Alge
braicGeometry.SheafedSpace`。
形式化陈述：{C : Type u} → [inst : CategoryTheory.Category.{v, u} C] → {X Y : Algebrai
cGeometry.SheafedSpace C} → (X ⟶ Y) → Prop
参数：X ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism of SheafedSpaces is an open immersion if it is an open immersion as a
 morphism
of PresheafedSpaces
-/
abbrev SheafedSpace.IsOpenImmersion {X Y : SheafedSpace C} (f : X ⟶ Y) : Prop :=
  PresheafedSpace.IsOpenImmersion f.hom
/-
**AlgebraicGeometry.SheafedSpace.isOpenImmersion_iff_hom** 是 Mathlib 中的一个定理，位于命名
空间 `AlgebraicGeometry.SheafedSpace`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : AlgebraicG
eometry.SheafedSpace C} (f : X ⟶ Y),   AlgebraicGeometry.SheafedSpace.IsOpenImme
rsion f ↔ AlgebraicGeometry.PresheafedSpace.IsOpenImmersion f.hom
参数：f : X ⟶ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma SheafedSpace.isOpenImmersion_iff_hom {X Y : SheafedSpace C} (f : X ⟶ Y) :
    SheafedSpace.IsOpenImmersion f ↔ PresheafedSpace.IsOpenImmersion f.hom := Iff.rfl

/-- A morphism of LocallyRingedSpaces is an open immersion if it is an open immersion as a morphism
of SheafedSpaces
-/
/-
**AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion** 是 Mathlib 中的一个定义，位于命名空间
 `AlgebraicGeometry.LocallyRingedSpace`。
形式化陈述：{X Y : AlgebraicGeometry.LocallyRingedSpace} → (X ⟶ Y) → Prop
参数：X ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism of LocallyRingedSpaces is an open immersion if it is an open immersio
n as a morphism
of SheafedSpaces
-/
abbrev LocallyRingedSpace.IsOpenImmersion {X Y : LocallyRingedSpace} (f : X ⟶ Y) : Prop :=
  SheafedSpace.IsOpenImmersion f.toShHom
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y : LocallyRingedSpace} (f : X ⟶ Y) [LocallyRingedSpace.IsOpenImmersion f] :
    PresheafedSpace.IsOpenImmersion f.toHom := by assumption

namespace PresheafedSpace.IsOpenImmersion

open PresheafedSpace

local notation "IsOpenImmersion" => PresheafedSpace.IsOpenImmersion

attribute [instance] IsOpenImmersion.c_iso

section

variable {X Y : PresheafedSpace C} (f : X ⟶ Y) [H : IsOpenImmersion f]

/-- The functor `Opens X ⥤ Opens Y` associated with an open immersion `f : X ⟶ Y`. -/
/-
**AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.opensFunctor** 是 Mathlib 中的一
个缩写定义，位于命名空间 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion`。
形式化陈述：opensFunctor
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.base_open`：∀ {C : Type
 u} {inst : CategoryTheory.Category.{v, u} C} {X Y : AlgebraicGeometry.Presheafe
dSpace C} {f : X ⟶ Y}   [self : AlgebraicGeometry…

--- 原说明 ---
The functor `Opens X ⥤ Opens Y` associated with an open immersion `f : X ⟶ Y`.
-/
abbrev opensFunctor :=
  H.base_open.functor

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- An open immersion `f : X ⟶ Y` induces an isomorphism `X ≅ Y|_{f(X)}`. -/
@[simps! hom_c_app]
/-
**AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.isoRestrict** 是 Mathlib 中的一个
定义，位于命名空间 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion`。
形式化陈述：isoRestrict : X ≅ Y.restrict H.base_open
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.base_open`：∀ {C : Type
 u} {inst : CategoryTheory.Category.{v, u} C} {X Y : AlgebraicGeometry.Presheafe
dSpace C} {f : X ⟶ Y}   [self : AlgebraicGeometry…

--- 原说明 ---
An open immersion `f : X ⟶ Y` induces an isomorphism `X ≅ Y|_{f(X)}`.
-/
noncomputable def isoRestrict : X ≅ Y.restrict H.base_open :=
  PresheafedSpace.isoOfComponents (Iso.refl _) <| by
    symm
    fapply NatIso.ofComponents
    · intro U
      refine asIso (f.c.app (op (opensFunctor f |>.obj (unop U)))) ≪≫ X.presheaf.mapIso (eqToIso ?_)
      induction U with | op U => ?_
      cases U
      dsimp only [IsOpenMap.functor, Functor.op, Opens.map_def]
      congr 2
      erw [Set.preimage_image_eq _ H.base_open.injective]
      rfl
    · intro U V i
      dsimp
      simp only [NatTrans.naturality_assoc, TopCat.Presheaf.pushforward_obj_obj,
        TopCat.Presheaf.pushforward_obj_map, Quiver.Hom.unop_op, Category.assoc]
      rw [← X.presheaf.map_comp, ← X.presheaf.map_comp]
      congr 1

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.isoRestrict_hom_ofRestrict**
 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion`。
形式化陈述：isoRestrict_hom_ofRestrict : (isoRestrict f).hom ≫ Y.ofRestrict _ = f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.PresheafedSpace.Hom.ext`：∀ {C : Type u_1} [inst : Cate
goryTheory.Category.{v_1, u_1} C] {X Y : AlgebraicGeometry.PresheafedSpace C}   
(α β : X.Hom Y) (w : α.base = β…
· 使用定理 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.base_open`：∀ {C : Type
 u} {inst : CategoryTheory.Category.{v, u} C} {X Y : AlgebraicGeometry.Presheafe
dSpace C} {f : X ⟶ Y}   [self : AlgebraicGeometry…
· 使用定理 `CategoryTheory.NatTrans.ext`：∀ {C : Type u₁} {inst : CategoryTheory.Cate
gory.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Category.{v₂, u₂} D}   {
F G : CategoryThe…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Functor.whiskerRight_id'`：whiskerRight_id' {G : C ⥤ D} (F
 : D ⥤ E) : whiskerRight (𝟙 G) F = 𝟙 (G.comp F)
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `AlgebraicGeometry.PresheafedSpace.comp_c_app`：comp_c_app {X Y Z : Preshe
afedSpace C} (α : X ⟶ Y) (β : Y ⟶ Z) (U) : (α ≫ β).c.app U = β.c.app U ≫ α.c.app
 (op ((Opens.map β.base).obj (unop…
· 使用定理 `CategoryTheory.NatTrans.naturality_assoc`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem isoRestrict_hom_ofRestrict : (isoRestrict f).hom ≫ Y.ofRestrict _ = f := by
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): `ext` did not pick up `NatTrans.ext`
  refine PresheafedSpace.Hom.ext _ _ rfl <| NatTrans.ext <| funext fun x => ?_
  simp only [eqToHom_refl,
    Functor.whiskerRight_id']
  erw [Category.comp_id, comp_c_app, f.c.naturality_assoc, ← X.presheaf.map_comp]
  trans f.c.app x ≫ X.presheaf.map (𝟙 _)
  · congr 1
  · simp

@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.isoRestrict_inv_ofRestrict**
 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion`。
形式化陈述：isoRestrict_inv_ofRestrict : (isoRestrict f).inv ≫ f = Y.ofRestrict _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.base_open`：∀ {C : Type
 u} {inst : CategoryTheory.Category.{v, u} C} {X Y : AlgebraicGeometry.Presheafe
dSpace C} {f : X ⟶ Y}   [self : AlgebraicGeometry…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.inv_comp_eq`：inv_comp_eq (α : X ≅ Y) {f : X ⟶ Z} {g :
 Y ⟶ Z} : α.inv ≫ f = g ↔ f = α.hom ≫ g
· 使用定理 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.isoRestrict_hom_ofRest
rict`：isoRestrict_hom_ofRestrict : (isoRestrict f).hom ≫ Y.ofRestrict _ = f
-/
theorem isoRestrict_inv_ofRestrict : (isoRestrict f).inv ≫ f = Y.ofRestrict _ := by
  rw [Iso.inv_comp_eq, isoRestrict_hom_ofRestrict]
/-
**AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.mono** 是 Mathlib 中的一个实例，位于命名
空间 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion`。
形式化陈述：mono : Mono f
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.base_open`：∀ {C : Type
 u} {inst : CategoryTheory.Category.{v, u} C} {X Y : AlgebraicGeometry.Presheafe
dSpace C} {f : X ⟶ Y}   [self : AlgebraicGeometry…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.isoRestrict_hom_ofRest
rict`：isoRestrict_hom_ofRestrict : (isoRestrict f).hom ≫ Y.ofRestrict _ = f
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
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
-/
instance mono : Mono f := by
  rw [← H.isoRestrict_hom_ofRestrict]; apply mono_comp
/-
**AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.c_iso'** 是 Mathlib 中的一个引理，位于
命名空间 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion`。
形式化陈述：c_iso' {V : Opens Y} (U : Opens X) (h : V = (opensFunctor f).obj U) : IsIs
o (f.c.app (Opposite.op V))
参数：U : Opens X；h : V = (opensFunctor f).obj U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.c_iso`：∀ {C : Type u} 
{inst : CategoryTheory.Category.{v, u} C} {X Y : AlgebraicGeometry.PresheafedSpa
ce C} {f : X ⟶ Y}   [self : AlgebraicGeometry…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma c_iso' {V : Opens Y} (U : Opens X) (h : V = (opensFunctor f).obj U) :
    IsIso (f.c.app (Opposite.op V)) := by
  subst h
  infer_instance

set_option backward.defeqAttrib.useBackward true in
/-- The composition of two open immersions is an open immersion. -/
/-
**AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.comp** 是 Mathlib 中的一个实例，位于命名
空间 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion`。
形式化陈述：comp {Z : PresheafedSpace C} (g : Y ⟶ Z) [hg : IsOpenImmersion g] : IsOpen
Immersion (f ≫ g) where base_open
参数：g : Y ⟶ Z。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsOpenEmbedding.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type
 u_3} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : Topologica
lSpace Y] [inst_2 :…
· 使用定理 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.base_open`：∀ {C : Type
 u} {inst : CategoryTheory.Category.{v, u} C} {X Y : AlgebraicGeometry.Presheafe
dSpace C} {f : X ⟶ Y}   [self : AlgebraicGeometry…
· 使用引理 `CategoryTheory.IsIso.comp_isIso'`：comp_isIso' (_ : IsIso f) (_ : IsIso h
) : IsIso (f ≫ h)
· 使用引理 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.c_iso'`：c_iso' {V : Op
ens Y} (U : Opens X) (h : V = (opensFunctor f).obj U) : IsIso (f.c.app (Opposite
.op V))
· 使用定理 `TopologicalSpace.Opens.ext`：ext {U V : Opens α} (h : (U : Set α) = V) : 
U = V
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Set.image_comp`：image_comp (f : β -> γ) (g : α -> β) (a : Set α) : f ∘ g
 '' a = f '' g '' a
· 使用定理 `Set.preimage_image_eq`：preimage_image_eq {f : α -> β} (s : Set α) (h : I
njective f) : f ⁻¹' f '' s = s
· 使用定理 `Topology.IsEmbedding.injective`：∀ {X : Type u_1} {Y : Type u_2} [tX : To
pologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbedding 
f → Function.Injecti…
· 使用定理 `Topology.IsOpenEmbedding.toIsEmbedding`：∀ {X : Type u_1} {Y : Type u_2} 
[tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsOp
enEmbedding f → Topology.IsE…

--- 原说明 ---
The composition of two open immersions is an open immersion.
-/
instance comp {Z : PresheafedSpace C} (g : Y ⟶ Z) [hg : IsOpenImmersion g] :
    IsOpenImmersion (f ≫ g) where
  base_open := hg.base_open.comp H.base_open
  c_iso U := by
    generalize_proofs h
    dsimp only [AlgebraicGeometry.PresheafedSpace.comp_c_app, unop_op, Functor.op, comp_base,
      Opens.map_comp_obj]
    apply IsIso.comp_isIso'
    · exact c_iso' g ((opensFunctor f).obj U) (by ext; simp)
    · apply c_iso' f U
      ext1
      dsimp only [Opens.map_coe, IsOpenMap.coe_functor_obj, comp_base, TopCat.coe_comp]
      rw [Set.image_comp, Set.preimage_image_eq _ hg.base_open.injective]

set_option backward.isDefEq.respectTransparency false in
/-- For an open immersion `f : X ⟶ Y` and an open set `U ⊆ X`, we have the map `X(U) ⟶ Y(U)`. -/
/-
**AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.invApp** 是 Mathlib 中的一个定义，位于
命名空间 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion`。
形式化陈述：invApp (U : Opens X) : X.presheaf.obj (op U) ⟶ Y.presheaf.obj (op (opensFu
nctor f |>.obj U))
参数：U : Opens X。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.c_iso`：∀ {C : Type u} 
{inst : CategoryTheory.Category.{v, u} C} {X Y : AlgebraicGeometry.PresheafedSpa
ce C} {f : X ⟶ Y}   [self : AlgebraicGeometry…

--- 原说明 ---
For an open immersion `f : X ⟶ Y` and an open set `U ⊆ X`, we have the map `X(U)
 ⟶ Y(U)`.
-/
noncomputable def invApp (U : Opens X) :
    X.presheaf.obj (op U) ⟶ Y.presheaf.obj (op (opensFunctor f |>.obj U)) :=
  X.presheaf.map (eqToHom (by simp [Opens.map_def, Set.preimage_image_eq _ H.base_open.injective]))
    ≫ inv (f.c.app (op (opensFunctor f |>.obj U)))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp, reassoc]
/-
**AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.inv_naturality** 是 Mathlib 中
的一个定理，位于命名空间 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion`。
形式化陈述：inv_naturality {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) : X.presheaf.map i ≫ H.invA
pp _ (unop V) = invApp f (unop U) ≫ Y.presheaf.map (opensFunctor f |>.op.map i)
参数：Opens X；i : U ⟶ V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.c_iso`：∀ {C : Type u} 
{inst : CategoryTheory.Category.{v, u} C} {X Y : AlgebraicGeometry.PresheafedSpa
ce C} {f : X ⟶ Y}   [self : AlgebraicGeometry…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsIso.comp_inv_eq`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {X Y Z : C} (α : Y ⟶ X) [inst_1 : CategoryTheory.IsIso α]   {
f : Z ⟶ X} {g : Z ⟶ Y}…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.IsIso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y) [I : CategoryTheory.IsIso f] {Z : 
C}   (h : Y ⟶ Z), CategoryT…
-/
theorem inv_naturality {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) :
    X.presheaf.map i ≫ H.invApp _ (unop V) =
      invApp f (unop U) ≫ Y.presheaf.map (opensFunctor f |>.op.map i) := by
  simp only [invApp, ← Category.assoc]
  rw [IsIso.comp_inv_eq]
  simp only [Functor.op_obj, op_unop, ← X.presheaf.map_comp, Functor.op_map, Category.assoc,
    NatTrans.naturality, Quiver.Hom.unop_op, IsIso.inv_hom_id_assoc,
    TopCat.Presheaf.pushforward_obj_map]
  congr 1

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.** 是 Mathlib 中的一个实例，位于命名空间 `
AlgebraicGeometry.PresheafedSpace.IsOpenImmersion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (U : Opens X) : IsIso (invApp f U) := by delta invApp; infer_instance

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.inv_invApp** 是 Mathlib 中的一个定
理，位于命名空间 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion`。
形式化陈述：inv_invApp (U : Opens X) : inv (H.invApp _ U) = f.c.app (op (opensFunctor 
f |>.obj U)) ≫ X.presheaf.map (eqToHom (by simp [Opens.map_def, Set.preimage_ima
ge_eq _ H.base_open.injective]))
参数：U : Opens X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.instIsIsoInvApp`：∀ {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : AlgebraicGeometry.Pre
sheafedSpace C} (f : X ⟶ Y)   [H : AlgebraicGeometry.Pr…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.instEffectiveEpiOfIsIso`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],  
 CategoryTheory.EffectiveEpi…
· 使用定理 `CategoryTheory.IsIso.hom_inv_id`：hom_inv_id (f : X ⟶ Y) [I : IsIso f] : 
f ≫ inv f = 𝟙 X
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.c_iso`：∀ {C : Type u} 
{inst : CategoryTheory.Category.{v, u} C} {X Y : AlgebraicGeometry.PresheafedSpa
ce C} {f : X ⟶ Y}   [self : AlgebraicGeometry…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.IsIso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y) [I : CategoryTheory.IsIso f] {Z : 
C}   (h : Y ⟶ Z), CategoryT…
· 使用定理 `CategoryTheory.eqToHom_trans`：eqToHom_trans {X Y Z : C} (p : X = Y) (q :
 Y = Z) : eqToHom p ≫ eqToHom q = eqToHom (p.trans q)
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inv_invApp (U : Opens X) :
    inv (H.invApp _ U) =
      f.c.app (op (opensFunctor f |>.obj U)) ≫
        X.presheaf.map
          (eqToHom (by simp [Opens.map_def, Set.preimage_image_eq _ H.base_open.injective])) := by
  rw [← cancel_epi (H.invApp _ U), IsIso.hom_inv_id]
  delta invApp
  simp [← Functor.map_comp]

set_option backward.isDefEq.respectTransparency false in
@[simp, reassoc, elementwise]
/-
**AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.invApp_app** 是 Mathlib 中的一个定
理，位于命名空间 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion`。
形式化陈述：invApp_app (U : Opens X) : invApp f U ≫ f.c.app (op (opensFunctor f |>.obj
 U)) = X.presheaf.map (eqToHom (by simp [Opens.map_def, Set.preimage_image_eq _ 
H.base_open.injective]))
参数：U : Opens X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.c_iso`：∀ {C : Type u} 
{inst : CategoryTheory.Category.{v, u} C} {X Y : AlgebraicGeometry.PresheafedSpa
ce C} {f : X ⟶ Y}   [self : AlgebraicGeometry…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.invApp.eq_1`：∀ {C : Ty
pe u} [inst : CategoryTheory.Category.{v, u} C] {X Y : AlgebraicGeometry.Preshea
fedSpace C} (f : X ⟶ Y)   [H : AlgebraicGeometry.Pr…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.IsIso.inv_hom_id`：inv_hom_id (f : X ⟶ Y) [I : IsIso f] : 
inv f ≫ f = 𝟙 Y
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
theorem invApp_app (U : Opens X) :
    invApp f U ≫ f.c.app (op (opensFunctor f |>.obj U)) = X.presheaf.map
      (eqToHom (by simp [Opens.map_def, Set.preimage_image_eq _ H.base_open.injective])) := by
  rw [invApp, Category.assoc, IsIso.inv_hom_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
@[simp, reassoc]
/-
**AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.app_invApp** 是 Mathlib 中的一个定
理，位于命名空间 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion`。
形式化陈述：app_invApp (U : Opens Y) : f.c.app (op U) ≫ H.invApp _ ((Opens.map f.base)
.obj U) = Y.presheaf.map ((homOfLE (Set.image_preimage_subset f.base U.1)).op : 
op U ⟶ op (opensFunctor f |>.obj ((Opens.map f.base).obj U)))
参数：U : Opens Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_preimage_subset`：image_preimage_subset (f : α -> β) (s : Set β
) : f '' f ⁻¹' s subseteq s
· 使用定理 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.c_iso`：∀ {C : Type u} 
{inst : CategoryTheory.Category.{v, u} C} {X Y : AlgebraicGeometry.PresheafedSpa
ce C} {f : X ⟶ Y}   [self : AlgebraicGeometry…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.invApp.eq_1`：∀ {C : Ty
pe u} [inst : CategoryTheory.Category.{v, u} C] {X Y : AlgebraicGeometry.Preshea
fedSpace C} (f : X ⟶ Y)   [H : AlgebraicGeometry.Pr…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.IsIso.comp_inv_eq`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {X Y Z : C} (α : Y ⟶ X) [inst_1 : CategoryTheory.IsIso α]   {
f : Z ⟶ X} {g : Z ⟶ Y}…
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
-/
theorem app_invApp (U : Opens Y) :
    f.c.app (op U) ≫ H.invApp _ ((Opens.map f.base).obj U) =
      Y.presheaf.map
        ((homOfLE (Set.image_preimage_subset f.base U.1)).op :
          op U ⟶ op (opensFunctor f |>.obj ((Opens.map f.base).obj U))) := by
  rw [invApp, ← Category.assoc, IsIso.comp_inv_eq, f.c.naturality]
  congr

/-- A variant of `app_inv_app` that gives an `eqToHom` instead of `homOfLe`. -/
@[reassoc]
/-
**AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.app_inv_app'** 是 Mathlib 中的一
个定理，位于命名空间 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion`。
形式化陈述：app_inv_app' (U : Opens Y) (hU : (U : Set Y) subseteq Set.range f.base) : 
f.c.app (op U) ≫ invApp f ((Opens.map f.base).obj U) = Y.presheaf.map (eqToHom (
le_antisymm (Set.image_preimage_subset f.base U.1) <| (Set.image_preimage_eq_int
er_range (f
参数：U : Opens Y；hU : (U : Set Y) subseteq Set.range f.base。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Set.image_preimage_subset`：image_preimage_subset (f : α -> β) (s : Set β
) : f '' f ⁻¹' s subseteq s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.subset_inter_iff`：subset_inter_iff {s t r : Set α} : r subseteq s in
ter t ↔ r subseteq s ∧ r subseteq t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_preimage_eq_inter_range`：image_preimage_eq_inter_range {f : α 
-> β} {t : Set β} : f '' f ⁻¹' t = t inter range f
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.app_invApp`：app_invApp
 (U : Opens Y) : f.c.app (op U) ≫ H.invApp _ ((Opens.map f.base).obj U) = Y.pres
heaf.map ((homOfLE (Set.image_preimage_subset f.ba…
· 使用定理 `CategoryTheory.eqToHom_op`：eqToHom_op {X Y : C} (h : X = Y) : (eqToHom h
).op = eqToHom (congr_arg op h.symm)

--- 原说明 ---
A variant of `app_inv_app` that gives an `eqToHom` instead of `homOfLe`.
-/
theorem app_inv_app' (U : Opens Y) (hU : (U : Set Y) ⊆ Set.range f.base) :
    f.c.app (op U) ≫ invApp f ((Opens.map f.base).obj U) =
      Y.presheaf.map
        (eqToHom
            (le_antisymm (Set.image_preimage_subset f.base U.1) <|
              (Set.image_preimage_eq_inter_range (f := f.base) (t := U.1)).symm ▸
                Set.subset_inter_iff.mpr ⟨fun _ h => h, hU⟩)).op := by
  simp only [app_invApp, Opens.carrier_eq_coe,
    homOfLE_leOfHom, eqToHom_op]
  tauto

set_option backward.isDefEq.respectTransparency false in
/-- An isomorphism is an open immersion. -/
/-
**AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.ofIso** 是 Mathlib 中的一个实例，位于命
名空间 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion`。
形式化陈述：ofIso {X Y : PresheafedSpace C} (H : X ≅ Y) : IsOpenImmersion H.hom where 
base_open
参数：H : X ≅ Y。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.isOpenEmbedding`：isOpenEmbedding (h : X ≃ₜ Y) : IsOpenEmbeddi
ng h
· 使用定理 `CategoryTheory.NatIso.isIso_app_of_isIso`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom

--- 原说明 ---
An isomorphism is an open immersion.
-/
instance ofIso {X Y : PresheafedSpace C} (H : X ≅ Y) : IsOpenImmersion H.hom where
  base_open := (TopCat.homeoOfIso ((forget C).mapIso H)).isOpenEmbedding
  -- Porting note: `inferInstance` will fail if Lean is not told that `H.hom.c` is iso
  c_iso _ := letI : IsIso H.hom.c := inferInstance;
    inferInstance
/-
**AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.** 是 Mathlib 中的一个实例，位于命名空间 `
AlgebraicGeometry.PresheafedSpace.IsOpenImmersion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) ofIsIso {X Y : PresheafedSpace C} (f : X ⟶ Y) [IsIso f] :
    IsOpenImmersion f :=
  AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.ofIso (asIso f)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.ofRestrict** 是 Mathlib 中的一个实
例，位于命名空间 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion`。
形式化陈述：ofRestrict {X : TopCat} (Y : PresheafedSpace C) {f : X ⟶ Y.carrier} (hf : 
IsOpenEmbedding f) : IsOpenImmersion (Y.ofRestrict hf) where base_open
参数：Y : PresheafedSpace C；hf : IsOpenEmbedding f。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.Opens.ext`：ext {U V : Opens α} (h : (U : Set α) = V) : 
U = V
· 使用定理 `Set.preimage_image_eq`：preimage_image_eq {f : α -> β} (s : Set α) (h : I
njective f) : f ⁻¹' f '' s = s
· 使用定理 `Topology.IsEmbedding.injective`：∀ {X : Type u_1} {Y : Type u_2} [tX : To
pologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbedding 
f → Function.Injecti…
· 使用定理 `Topology.IsOpenEmbedding.toIsEmbedding`：∀ {X : Type u_1} {Y : Type u_2} 
[tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsOp
enEmbedding f → Topology.IsE…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Subsingleton.helim`：∀ {α β : Sort u} [h₁ : Subsingleton α], α = β → ∀ (a
 : α) (b : β), a ≍ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
instance ofRestrict {X : TopCat} (Y : PresheafedSpace C) {f : X ⟶ Y.carrier}
    (hf : IsOpenEmbedding f) : IsOpenImmersion (Y.ofRestrict hf) where
  base_open := hf
  c_iso U := by
    dsimp
    have : (Opens.map f).obj (hf.functor.obj U) = U := by
      ext1
      exact Set.preimage_image_eq _ hf.injective
    convert_to IsIso (Y.presheaf.map (𝟙 _))
    · congr
    · -- Porting note: was `apply Subsingleton.helim; rw [this]`
      -- See https://github.com/leanprover/lean4/issues/2273
      congr
      · simp only
        congr
      apply Subsingleton.helim
      rw [this]
    · infer_instance

set_option backward.isDefEq.respectTransparency false in
@[elementwise, simp]
/-
**AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.ofRestrict_invApp** 是 Mathli
b 中的一个定理，位于命名空间 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion`。
形式化陈述：ofRestrict_invApp {C : Type*} [Category* C] (X : PresheafedSpace C) {Y : T
opCat.{w}} {f : Y ⟶ TopCat.of X.carrier} (h : IsOpenEmbedding f) (U : Opens (X.r
estrict h).carrier) : (PresheafedSpace.IsOpenImmersion.ofRestrict X h).invApp _ 
U = 𝟙 _
参数：X : PresheafedSpace C；h : IsOpenEmbedding f；U : Opens (X.restrict h).carrier。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.c_iso`：∀ {C : Type u} 
{inst : CategoryTheory.Category.{v, u} C} {X Y : AlgebraicGeometry.PresheafedSpa
ce C} {f : X ⟶ Y}   [self : AlgebraicGeometry…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsIso.comp_inv_eq`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {X Y Z : C} (α : Y ⟶ X) [inst_1 : CategoryTheory.IsIso α]   {
f : Z ⟶ X} {g : Z ⟶ Y}…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
-/
theorem ofRestrict_invApp {C : Type*} [Category* C] (X : PresheafedSpace C) {Y : TopCat.{w}}
    {f : Y ⟶ TopCat.of X.carrier} (h : IsOpenEmbedding f) (U : Opens (X.restrict h).carrier) :
    (PresheafedSpace.IsOpenImmersion.ofRestrict X h).invApp _ U = 𝟙 _ := by
  delta invApp
  rw [IsIso.comp_inv_eq, Category.id_comp]
  change X.presheaf.map _ = X.presheaf.map _
  congr 1

/-- An open immersion is an iso if the underlying continuous map is epi. -/
/-
**AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.to_iso** 是 Mathlib 中的一个定理，位于
命名空间 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion`。
形式化陈述：to_iso [h' : Epi f.base] : IsIso f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_preimage_eq`：image_preimage_eq {f : α -> β} (s : Set β) (h : S
urjective f) : f '' f ⁻¹' s = s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `TopCat.epi_iff_surjective`：epi_iff_surjective {X Y : TopCat.{u}} (f : X 
⟶ Y) : Epi f ↔ Function.Surjective f
· 使用定理 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.base_open`：∀ {C : Type
 u} {inst : CategoryTheory.Category.{v, u} C} {X Y : AlgebraicGeometry.Presheafe
dSpace C} {f : X ⟶ Y}   [self : AlgebraicGeometry…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.c_iso`：∀ {C : Type u} 
{inst : CategoryTheory.Category.{v, u} C} {X Y : AlgebraicGeometry.PresheafedSpa
ce C} {f : X ⟶ Y}   [self : AlgebraicGeometry…
· 使用定理 `CategoryTheory.NatIso.isIso_of_isIso_app`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `AlgebraicGeometry.PresheafedSpace.isIso_of_components`：isIso_of_componen
ts (f : X ⟶ Y) [IsIso f.base] [IsIso f.c] : IsIso f
· 使用定理 `Topology.IsOpenEmbedding.isEmbedding`：∀ {X : Type u_1} {Y : Type u_2} {f
 : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.
IsOpenEmbedding f → Topolo…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.range_eq_univ`：range_eq_univ : range f = univ ↔ Surjective f
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
· 使用定理 `Continuous.subtype_mk`：Continuous.subtype_mk {f : Y -> X} (h : Continuou
s f) (hp : forall x, p (f x)) : Continuous fun x => (⟨f x, hp x⟩ : Subtype p)
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom

--- 原说明 ---
An open immersion is an iso if the underlying continuous map is epi.
-/
theorem to_iso [h' : Epi f.base] : IsIso f := by
  have : ∀ (U : (Opens Y)ᵒᵖ), IsIso (f.c.app U) := by
    intro U
    have : U = op (opensFunctor f |>.obj ((Opens.map f.base).obj (unop U))) := by
      induction U with | op U => ?_
      cases U
      dsimp only [Functor.op, Opens.map]
      congr
      exact (Set.image_preimage_eq _ ((TopCat.epi_iff_surjective _).mp h')).symm
    convert! H.c_iso (Opens.map f.base |>.obj <| unop U)
  have : IsIso f.c := NatIso.isIso_of_isIso_app _
  apply +allowSynthFailures isIso_of_components
  let t : X ≃ₜ Y := H.base_open.isEmbedding.toHomeomorph.trans
    { toFun := Subtype.val
      invFun := fun x =>
        ⟨x, by rw [Set.range_eq_univ.mpr ((TopCat.epi_iff_surjective _).mp h')]; trivial⟩ }
  exact (TopCat.isoOfHomeo t).isIso_hom

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.stalk_iso** 是 Mathlib 中的一个实例
，位于命名空间 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion`。
形式化陈述：stalk_iso [HasColimits C] (x : X) : IsIso (f.stalkMap x)
参数：x : X。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.base_open`：∀ {C : Type
 u} {inst : CategoryTheory.Category.{v, u} C} {X Y : AlgebraicGeometry.Presheafe
dSpace C} {f : X ⟶ Y}   [self : AlgebraicGeometry…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.isoRestrict_hom_ofRest
rict`：isoRestrict_hom_ofRestrict : (isoRestrict f).hom ≫ Y.ofRestrict _ = f
· 使用定理 `AlgebraicGeometry.PresheafedSpace.stalkMap.comp`：comp {X Y Z : Presheafe
dSpace.{_, _, v} C} (α : X ⟶ Y) (β : Y ⟶ Z) (x : X) : (α ≫ β).stalkMap x = (β.st
alkMap (α.base x) : Z.presheaf.stalk …
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
-/
instance stalk_iso [HasColimits C] (x : X) : IsIso (f.stalkMap x) := by
  rw [← H.isoRestrict_hom_ofRestrict, PresheafedSpace.stalkMap.comp]
  infer_instance

end

noncomputable section Pullback

variable {X Y Z : PresheafedSpace C} (f : X ⟶ Z) [hf : IsOpenImmersion f] (g : Y ⟶ Z)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- (Implementation.) The projection map when constructing the pullback along an open immersion.
-/
/-
**AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.pullbackConeOfLeftFst** 是 Ma
thlib 中的一个定义，位于命名空间 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion`。
形式化陈述：pullbackConeOfLeftFst : Y.restrict (TopCat.snd_isOpenEmbedding_of_left hf.
base_open g.base) ⟶ X where base
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.base_open`：∀ {C : Type
 u} {inst : CategoryTheory.Category.{v, u} C} {X Y : AlgebraicGeometry.Presheafe
dSpace C} {f : X ⟶ Y}   [self : AlgebraicGeometry…

--- 原说明 ---
(Implementation.) The projection map when constructing the pullback along an ope
n immersion.
-/
def pullbackConeOfLeftFst :
    Y.restrict (TopCat.snd_isOpenEmbedding_of_left hf.base_open g.base) ⟶ X where
  base := pullback.fst _ _
  c :=
    { app := fun U =>
        hf.invApp _ (unop U) ≫
          g.c.app (op (hf.base_open.functor.obj (unop U))) ≫
            Y.presheaf.map
              (eqToHom
                (by
                  simp only [IsOpenMap.functor, op_inj_iff, Opens.map,
                    Functor.op_obj]
                  apply LE.le.antisymm
                  · rintro _ ⟨_, h₁, h₂⟩
                    use (TopCat.pullbackIsoProdSubtype _ _).inv ⟨⟨_, _⟩, h₂⟩
                    simpa [(TopCat.pullbackIsoProdSubtype_inv_fst_apply),
                      (TopCat.pullbackIsoProdSubtype_inv_snd_apply)]
                  · rintro _ ⟨x, h₁, rfl⟩
                    exact ⟨_, h₁, CategoryTheory.congr_fun pullback.condition x⟩))
      naturality := by
        intro U V i
        induction U
        induction V
        simp only [(inv_naturality_assoc), restrict_carrier, restrict_presheaf,
          TopCat.Presheaf.pushforward_obj_obj, Functor.comp_obj, Functor.op_obj,
          TopCat.Presheaf.pushforward_obj_map, Functor.comp_map, Functor.op_map, Quiver.Hom.unop_op,
          NatTrans.naturality_assoc, TopCat.Presheaf.pushforward_obj_map, Quiver.Hom.unop_op,
          ← Functor.map_comp, Category.assoc]
        rfl }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.pullback_cone_of_left_condit
ion** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion
`。
形式化陈述：pullback_cone_of_left_condition : pullbackConeOfLeftFst f g ≫ f = Y.ofRest
rict _ ≫ g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.PresheafedSpace.Hom.ext`：∀ {C : Type u_1} [inst : Cate
goryTheory.Category.{v_1, u_1} C] {X Y : AlgebraicGeometry.PresheafedSpace C}   
(α β : X.Hom Y) (w : α.base = β…
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePullbacks_of_hasFiniteLimits`：∀ (C : 
Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFini
teLimits C],   CategoryTheory.Limits.HasFiniteWidePul…
· 使用定理 `CategoryTheory.Limits.hasFiniteLimits_of_hasLimits`：∀ (C : Type u) [inst
 : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasLimits C],   Cate
goryTheory.Limits.HasFiniteLimits C
· 使用定理 `TopCat.snd_isOpenEmbedding_of_left`：snd_isOpenEmbedding_of_left {X Y S :
 TopCat.{u}} {f : X ⟶ S} (H : IsOpenEmbedding f) (g : Y ⟶ S) : IsOpenEmbedding ⇑
(pullback.snd f g)
· 使用定理 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.base_open`：∀ {C : Type
 u} {inst : CategoryTheory.Category.{v, u} C} {X Y : AlgebraicGeometry.Presheafe
dSpace C} {f : X ⟶ Y}   [self : AlgebraicGeometry…
· 使用定理 `CategoryTheory.Limits.pullback.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPullback f…
· 使用定理 `CategoryTheory.NatTrans.ext`：∀ {C : Type u₁} {inst : CategoryTheory.Cate
gory.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Category.{v₂, u₂} D}   {
F G : CategoryThe…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.image_preimage_subset`：image_preimage_subset (f : α -> β) (s : Set β
) : f '' f ⁻¹' s subseteq s
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.congr_obj`：congr_obj {F G : C ⥤ D} (h : F = G) (X
) : F.obj X = G.obj X
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.NatTrans.comp_app`：comp_app {F G H : C ⥤ D} (α : F ⟶ G) (
β : G ⟶ H) (X : C) : (α ≫ β).app X = α.app X ≫ β.app X
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.app_invApp_assoc`：∀ {C
 : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : AlgebraicGeometry.Pr
esheafedSpace C} (f : X ⟶ Y)   [H : AlgebraicGeometry.Pr…
· 使用定理 `CategoryTheory.NatTrans.naturality_assoc`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.eqToHom_app`：eqToHom_app {F G : C ⥤ D} (h : F = G) (X : C
) : (eqToHom h : F ⟶ G).app X = eqToHom (Functor.congr_obj h X)
· 使用定理 `CategoryTheory.eqToHom_unop`：eqToHom_unop {X Y : Cᵒᵖ} (h : X = Y) : (eqT
oHom h).unop = eqToHom (congr_arg unop h.symm)
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
-/
theorem pullback_cone_of_left_condition : pullbackConeOfLeftFst f g ≫ f = Y.ofRestrict _ ≫ g := by
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): `ext` did not pick up `NatTrans.ext`
  refine PresheafedSpace.Hom.ext _ _ ?_ <| NatTrans.ext <| funext fun U => ?_
  · simpa using! pullback.condition
  · induction U
    simp only [(NatTrans.comp_app), comp_c_app, unop_op, Functor.whiskerRight_app,
      pullbackConeOfLeftFst, app_invApp_assoc, eqToHom_app, Category.assoc,
      NatTrans.naturality_assoc, restrict_carrier, comp_base, ofRestrict_base, restrict_presheaf,
      Functor.comp_obj, Functor.op_obj, Opens.map_comp_obj, TopCat.Presheaf.pushforward_obj_obj,
      Opens.carrier_eq_coe, homOfLE_leOfHom, TopCat.Presheaf.pushforward_obj_map, Functor.comp_map,
      Functor.op_map, eqToHom_unop, ofRestrict_c_app, Functor.id_obj]
    rw [← Y.presheaf.map_comp, ← Y.presheaf.map_comp]
    congr 1

/-- We construct the pullback along an open immersion via restricting along the pullback of the
maps of underlying spaces (which is also an open embedding).
-/
/-
**AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.pullbackConeOfLeft** 是 Mathl
ib 中的一个定义，位于命名空间 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion`。
形式化陈述：pullbackConeOfLeft : PullbackCone f g
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.pullback_cone_of_left_
condition`：pullback_cone_of_left_condition : pullbackConeOfLeftFst f g ≫ f = Y.o
fRestrict _ ≫ g

--- 原说明 ---
We construct the pullback along an open immersion via restricting along the pull
back of the
maps of underlying spaces (which is also an open embedding).
-/
def pullbackConeOfLeft : PullbackCone f g :=
  PullbackCone.mk (pullbackConeOfLeftFst f g) (Y.ofRestrict _)
    (pullback_cone_of_left_condition f g)

variable (s : PullbackCone f g)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- (Implementation.) Any cone over `cospan f g` indeed factors through the constructed cone.
-/
/-
**AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.pullbackConeOfLeftLift** 是 M
athlib 中的一个定义，位于命名空间 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion`。
形式化陈述：pullbackConeOfLeftLift : s.pt ⟶ (pullbackConeOfLeft f g).pt where base
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(Implementation.) Any cone over `cospan f g` indeed factors through the construc
ted cone.
-/
def pullbackConeOfLeftLift : s.pt ⟶ (pullbackConeOfLeft f g).pt where
  base :=
    pullback.lift s.fst.base s.snd.base
      (congr_arg (fun x => PresheafedSpace.Hom.base x) s.condition)
  c :=
    { app := fun U =>
        s.snd.c.app _ ≫
          s.pt.presheaf.map
            (eqToHom
              (by
                dsimp only [Opens.map_def, IsOpenMap.functor, Functor.op]
                congr 2
                let s' : PullbackCone f.base g.base :=
                  PullbackCone.mk s.fst.base s.snd.base (congr_arg Hom.base s.condition)
                have : _ = s.snd.base := limit.lift_π s' WalkingCospan.right
                conv_lhs =>
                  rw [← this]
                  dsimp [s']
                  rw [Function.comp_def, ← Set.preimage_preimage]
                rw [Set.preimage_image_eq _
                    (TopCat.snd_isOpenEmbedding_of_left hf.base_open g.base).injective]
                rfl))
      naturality := fun U V i => by
        erw [s.snd.c.naturality_assoc]
        rw [Category.assoc]
        erw [← s.pt.presheaf.map_comp, ← s.pt.presheaf.map_comp]
        congr 1 }

set_option backward.isDefEq.respectTransparency false in
-- this lemma is not a `simp` lemma, because it is an implementation detail
/-
**AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.pullbackConeOfLeftLift_fst**
 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion`。
形式化陈述：pullbackConeOfLeftLift_fst : pullbackConeOfLeftLift f g s ≫ (pullbackConeO
fLeft f g).fst = s.fst
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.PresheafedSpace.Hom.ext`：∀ {C : Type u_1} [inst : Cate
goryTheory.Category.{v_1, u_1} C] {X Y : AlgebraicGeometry.PresheafedSpace C}   
(α β : X.Hom Y) (w : α.base = β…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PullbackCone.mk_π_app`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {W : C} (fst :
 W ⟶ X)   (snd : W ⟶ Y)   (eq :  …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.NatTrans.ext`：∀ {C : Type u₁} {inst : CategoryTheory.Cate
gory.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Category.{v₂, u₂} D}   {
F G : CategoryThe…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.base_open`：∀ {C : Type
 u} {inst : CategoryTheory.Category.{v, u} C} {X Y : AlgebraicGeometry.Presheafe
dSpace C} {f : X ⟶ Y}   [self : AlgebraicGeometry…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.NatTrans.naturality_assoc`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Limits.PullbackCone.condition`：condition (t : PullbackCon
e f g) : fst t ≫ f = snd t ≫ g
· 使用定理 `AlgebraicGeometry.PresheafedSpace.congr_app`：congr_app {X Y : Presheafed
Space C} {α β : X ⟶ Y} (h : α = β) (U) : α.c.app U = β.c.app U ≫ X.presheaf.map 
(eqToHom (by subst h; rfl))
· 使用定理 `CategoryTheory.instIsIsoEqToHom`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {X Y : C} (h : X = Y),   CategoryTheory.IsIso (CategoryTheo
ry.eqToHom h)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Mathlib.Tactic.Reassoc.eq_whisker'`：eq_whisker' {C : Type*} [Category* C
] {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) : f ≫ h = g ≫ h
· 使用定理 `CategoryTheory.IsIso.comp_inv_eq`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {X Y Z : C} (α : Y ⟶ X) [inst_1 : CategoryTheory.IsIso α]   {
f : Z ⟶ X} {g : Z ⟶ Y}…
· 使用定理 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.invApp_app_assoc`：∀ {C
 : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : AlgebraicGeometry.Pr
esheafedSpace C} (f : X ⟶ Y)   [H : AlgebraicGeometry.Pr…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.congr_obj`：congr_obj {F G : C ⥤ D} (h : F = G) (X
) : F.obj X = G.obj X
· 使用定理 `CategoryTheory.eqToHom_unop`：eqToHom_unop {X Y : Cᵒᵖ} (h : X = Y) : (eqT
oHom h).unop = eqToHom (congr_arg unop h.symm)
· 使用定理 `CategoryTheory.eqToHom_map`：eqToHom_map (F : C ⥤ D) {X Y : C} (p : X = Y
) : F.map (eqToHom p) = eqToHom (congr_arg F.obj p)
· 使用定理 `CategoryTheory.eqToHom_op`：eqToHom_op {X Y : C} (h : X = Y) : (eqToHom h
).op = eqToHom (congr_arg op h.symm)
· 使用定理 `CategoryTheory.inv.congr_simp`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (f f_1 : X ⟶ Y) (e_f : f = f_1)   [I : CategoryTheory.
IsIso f], CategoryT…
· 使用定理 `CategoryTheory.inv_eqToHom`：inv_eqToHom {X Y : C} (h : X = Y) : inv (eqT
oHom h) = eqToHom h.symm
（共 33 条，此处仅展示前 30 条）
-/
theorem pullbackConeOfLeftLift_fst :
    pullbackConeOfLeftLift f g s ≫ (pullbackConeOfLeft f g).fst = s.fst := by
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): `ext` did not pick up `NatTrans.ext`
  refine PresheafedSpace.Hom.ext _ _ ?_ <| NatTrans.ext <| funext fun x => ?_
  · change pullback.lift _ _ _ ≫ pullback.fst _ _ = _
    simp
  · induction x with | op x => ?_
    change ((_ ≫ _) ≫ _ ≫ _) ≫ _ = _
    simp_rw [Category.assoc]
    erw [← s.pt.presheaf.map_comp]
    erw [s.snd.c.naturality_assoc]
    have := congr_app s.condition (op (opensFunctor f |>.obj x))
    dsimp only [comp_c_app, unop_op] at this
    rw [← IsIso.comp_inv_eq] at this
    replace this := reassoc_of% this
    erw [← this, hf.invApp_app_assoc, s.fst.c.naturality_assoc]
    simp [eqToHom_map]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
-- this lemma is not a `simp` lemma, because it is an implementation detail
/-
**AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.pullbackConeOfLeftLift_snd**
 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion`。
形式化陈述：pullbackConeOfLeftLift_snd : pullbackConeOfLeftLift f g s ≫ (pullbackConeO
fLeft f g).snd = s.snd
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.PresheafedSpace.Hom.ext`：∀ {C : Type u_1} [inst : Cate
goryTheory.Category.{v_1, u_1} C] {X Y : AlgebraicGeometry.PresheafedSpace C}   
(α β : X.Hom Y) (w : α.base = β…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.NatTrans.ext`：∀ {C : Type u₁} {inst : CategoryTheory.Cate
gory.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Category.{v₂, u₂} D}   {
F G : CategoryThe…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.NatTrans.naturality_assoc`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
theorem pullbackConeOfLeftLift_snd :
    pullbackConeOfLeftLift f g s ≫ (pullbackConeOfLeft f g).snd = s.snd := by
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): `ext` did not pick up `NatTrans.ext`
  refine PresheafedSpace.Hom.ext _ _ ?_ <| NatTrans.ext <| funext fun x => ?_
  · change pullback.lift _ _ _ ≫ pullback.snd _ _ = _
    simp
  · change (_ ≫ _ ≫ _) ≫ _ = _
    simp_rw [Category.assoc]
    erw [s.snd.c.naturality_assoc]
    erw [← s.pt.presheaf.map_comp, ← s.pt.presheaf.map_comp]
    trans s.snd.c.app x ≫ s.pt.presheaf.map (𝟙 _)
    · congr 1
    · simp

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.pullbackConeSndIsOpenImmersi
on** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion`
。
形式化陈述：pullbackConeSndIsOpenImmersion : IsOpenImmersion (pullbackConeOfLeft f g).
snd
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.pullback_cone_of_left_
condition`：pullback_cone_of_left_condition : pullbackConeOfLeftFst f g ≫ f = Y.o
fRestrict _ ≫ g
· 使用定理 `CategoryTheory.Limits.PullbackCone.mk_snd`：mk_snd {W : C} (fst : W ⟶ X) 
(snd : W ⟶ Y) (eq : fst ≫ f = snd ≫ g) : (mk fst snd eq).snd = snd
-/
instance pullbackConeSndIsOpenImmersion : IsOpenImmersion (pullbackConeOfLeft f g).snd := by
  erw [CategoryTheory.Limits.PullbackCone.mk_snd]
  infer_instance

/-- The constructed pullback cone is indeed the pullback. -/
/-
**AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.pullbackConeOfLeftIsLimit** 
是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion`。
形式化陈述：pullbackConeOfLeftIsLimit : IsLimit (pullbackConeOfLeft f g)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The constructed pullback cone is indeed the pullback.
-/
def pullbackConeOfLeftIsLimit : IsLimit (pullbackConeOfLeft f g) := by
  apply PullbackCone.isLimitAux'
  intro s
  use pullbackConeOfLeftLift f g s
  use pullbackConeOfLeftLift_fst f g s
  use pullbackConeOfLeftLift_snd f g s
  intro m _ h₂
  rw [← cancel_mono (pullbackConeOfLeft f g).snd]
  exact h₂.trans (pullbackConeOfLeftLift_snd f g s).symm
/-
**AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.hasPullback_of_left** 是 Math
lib 中的一个实例，位于命名空间 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion`。
形式化陈述：hasPullback_of_left : HasPullback f g
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasPullback_of_left : HasPullback f g :=
  ⟨⟨⟨_, pullbackConeOfLeftIsLimit f g⟩⟩⟩
/-
**AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.hasPullback_of_right** 是 Mat
hlib 中的一个实例，位于命名空间 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion`。
形式化陈述：hasPullback_of_right : HasPullback g f
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasPullback_symmetry`：hasPullback_symmetry [HasPul
lback f g] : HasPullback g f
-/
instance hasPullback_of_right : HasPullback g f :=
  hasPullback_symmetry f g

set_option backward.isDefEq.respectTransparency false in
/-- Open immersions are stable under base-change. -/
/-
**AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.pullbackSndOfLeft** 是 Mathli
b 中的一个实例，位于命名空间 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion`。
形式化陈述：pullbackSndOfLeft : IsOpenImmersion (pullback.snd f g)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.limit.isoLimitCone_hom_π`：∀ {J : Type u₁} [inst : 
CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Catego
ry.{v, u} C]   {F : CategoryTheory.F…

--- 原说明 ---
Open immersions are stable under base-change.
-/
instance pullbackSndOfLeft : IsOpenImmersion (pullback.snd f g) := by
  delta pullback.snd
  rw [← limit.isoLimitCone_hom_π ⟨_, pullbackConeOfLeftIsLimit f g⟩ WalkingCospan.right]
  infer_instance

/-- Open immersions are stable under base-change. -/
/-
**AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.pullbackFstOfRight** 是 Mathl
ib 中的一个实例，位于命名空间 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion`。
形式化陈述：pullbackFstOfRight : IsOpenImmersion (pullback.fst g f)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasPullback_symmetry`：hasPullback_symmetry [HasPul
lback f g] : HasPullback g f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.pullbackSymmetry_hom_comp_snd`：pullbackSymmetry_ho
m_comp_snd [HasPullback f g] : (pullbackSymmetry f g).hom ≫ pullback.snd g f = p
ullback.fst f g

--- 原说明 ---
Open immersions are stable under base-change.
-/
instance pullbackFstOfRight : IsOpenImmersion (pullback.fst g f) := by
  rw [← pullbackSymmetry_hom_comp_snd]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.pullbackToBaseIsOpenImmersio
n** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion`。
形式化陈述：pullbackToBaseIsOpenImmersion [IsOpenImmersion g] : IsOpenImmersion (limit
.π (cospan f g) WalkingCospan.one)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.limit.w`：∀ {J : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]   (F
 : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.cospan_map_inl`：cospan_map_inl {X Y Z : C} (f : X 
⟶ Z) (g : Y ⟶ Z) : (cospan f g).map WalkingCospan.Hom.inl = f
-/
instance pullbackToBaseIsOpenImmersion [IsOpenImmersion g] :
    IsOpenImmersion (limit.π (cospan f g) WalkingCospan.one) := by
  rw [← limit.w (cospan f g) WalkingCospan.Hom.inl, cospan_map_inl]
  infer_instance
/-
**AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.forget_preservesLimitsOfLeft
** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion`。
形式化陈述：forget_preservesLimitsOfLeft : PreservesLimit (cospan f g) (forget C)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesLimit_of_preserves_limit_cone`：preservesL
imit_of_preserves_limit_cone {F : C ⥤ D} {t : Cone K} (h : IsLimit t) (hF : IsLi
mit (F.mapCone t)) : PreservesLimit K F where pres…
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePullbacks_of_hasFiniteLimits`：∀ (C : 
Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFini
teLimits C],   CategoryTheory.Limits.HasFiniteWidePul…
· 使用定理 `CategoryTheory.Limits.hasFiniteLimits_of_hasLimits`：∀ (C : Type u) [inst
 : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasLimits C],   Cate
goryTheory.Limits.HasFiniteLimits C
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.PullbackCone.condition_one`：condition_one (t : Pul
lbackCone f g) : t.π.app WalkingCospan.one = t.fst ≫ f
· 使用定理 `AlgebraicGeometry.PresheafedSpace.forget_map`：∀ (C : Type u_1) [inst : C
ategoryTheory.Category.{v_1, u_1} C] {X Y : AlgebraicGeometry.PresheafedSpace C}
 (f : X ⟶ Y),   (AlgebraicGeometry…
· 使用定理 `CategoryTheory.Limits.diagramIsoCospan_hom_app`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C]   (F : CategoryTheory.Functor CategoryTheory.Li
mits.WalkingCospan C) (X : CategoryT…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
instance forget_preservesLimitsOfLeft : PreservesLimit (cospan f g) (forget C) :=
  preservesLimit_of_preserves_limit_cone (pullbackConeOfLeftIsLimit f g)
    (by
      apply (IsLimit.postcomposeHomEquiv (diagramIsoCospan _) _).toFun
      refine (IsLimit.equivIsoLimit ?_).toFun (limit.isLimit (cospan f.base g.base))
      fapply Cone.ext
      · exact Iso.refl _
      change ∀ j, _ = 𝟙 _ ≫ _ ≫ _
      simp_rw [Category.id_comp]
      rintro (_ | _ | _) <;> symm
      · simp only [limit.cone_x, cospan_one, Functor.mapCone_π_app, PullbackCone.condition_one,
        forget_map,
          comp_base, cospan_left, cospan_right, Functor.comp_map, cospan_map_inl, cospan_map_inr,
          diagramIsoCospan_hom_app, PullbackCone.fst_limit_cone]
        tauto
      · exact Category.comp_id _
      · exact Category.comp_id _)
/-
**AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.forget_preservesLimitsOfRigh
t** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion`。
形式化陈述：forget_preservesLimitsOfRight : PreservesLimit (cospan g f) (forget C)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesPullback_symmetry`：preservesPullback_symm
etry : PreservesLimit (cospan g f) G where preserves {c} hc
-/
instance forget_preservesLimitsOfRight : PreservesLimit (cospan g f) (forget C) :=
  preservesPullback_symmetry (forget C) f g

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.pullback_snd_isIso_of_range_
subset** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry.PresheafedSpace.IsOpenImmers
ion`。
形式化陈述：pullback_snd_isIso_of_range_subset (H : Set.range g.base subseteq Set.rang
e f.base) : IsIso (pullback.snd f g)
参数：H : Set.range g.base subseteq Set.range f.base。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePullbacks_of_hasFiniteLimits`：∀ (C : 
Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFini
teLimits C],   CategoryTheory.Limits.HasFiniteWidePul…
· 使用定理 `CategoryTheory.Limits.hasFiniteLimits_of_hasLimits`：∀ (C : Type u) [inst
 : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasLimits C],   Cate
goryTheory.Limits.HasFiniteLimits C
· 使用定理 `TopCat.snd_iso_of_left_embedding_range_subset`：snd_iso_of_left_embedding
_range_subset {X Y S : TopCat.{u}} {f : X ⟶ S} (hf : IsEmbedding f) (g : Y ⟶ S) 
(H : Set.range g subseteq Set.range…
· 使用定理 `Topology.IsOpenEmbedding.isEmbedding`：∀ {X : Type u_1} {Y : Type u_2} {f
 : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.
IsOpenEmbedding f → Topolo…
· 使用定理 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.base_open`：∀ {C : Type
 u} {inst : CategoryTheory.Category.{v, u} C} {X Y : AlgebraicGeometry.Presheafe
dSpace C} {f : X ⟶ Y}   [self : AlgebraicGeometry…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.limit.isoLimitCone_hom_π`：∀ {J : Type u₁} [inst : 
CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Catego
ry.{v, u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.to_iso`：to_iso [h' : E
pi f.base] : IsIso f
· 使用定理 `CategoryTheory.instEffectiveEpiOfIsIso`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],  
 CategoryTheory.EffectiveEpi…
-/
theorem pullback_snd_isIso_of_range_subset (H : Set.range g.base ⊆ Set.range f.base) :
    IsIso (pullback.snd f g) := by
  have := TopCat.snd_iso_of_left_embedding_range_subset hf.base_open.isEmbedding g.base H
  have : IsIso (pullback.snd f g).base := by
    delta pullback.snd
    rw [← limit.isoLimitCone_hom_π ⟨_, pullbackConeOfLeftIsLimit f g⟩ WalkingCospan.right]
    change IsIso (_ ≫ pullback.snd _ _)
    infer_instance
  apply to_iso

/-- The universal property of open immersions:
For an open immersion `f : X ⟶ Z`, given any morphism of schemes `g : Y ⟶ Z` whose topological
image is contained in the image of `f`, we can lift this morphism to a unique `Y ⟶ X` that
commutes with these maps.
-/
/-
**AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.lift** 是 Mathlib 中的一个定义，位于命名
空间 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion`。
形式化陈述：lift (H : Set.range g.base subseteq Set.range f.base) : Y ⟶ X
参数：H : Set.range g.base subseteq Set.range f.base。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.pullback_snd_isIso_of_
range_subset`：pullback_snd_isIso_of_range_subset (H : Set.range g.base subseteq 
Set.range f.base) : IsIso (pullback.snd f g)

--- 原说明 ---
The universal property of open immersions:
For an open immersion `f : X ⟶ Z`, given any morphism of schemes `g : Y ⟶ Z` who
se topological
image is contained in the image of `f`, we can lift this morphism to a unique `Y
 ⟶ X` that
commutes with these maps.
-/
def lift (H : Set.range g.base ⊆ Set.range f.base) : Y ⟶ X :=
  haveI := pullback_snd_isIso_of_range_subset f g H
  inv (pullback.snd f g) ≫ pullback.fst _ _

@[simp, reassoc]
/-
**AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.lift_fac** 是 Mathlib 中的一个定理，
位于命名空间 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion`。
形式化陈述：lift_fac (H : Set.range g.base subseteq Set.range f.base) : lift f g H ≫ f
 = g
参数：H : Set.range g.base subseteq Set.range f.base。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.pullback_snd_isIso_of_
range_subset`：pullback_snd_isIso_of_range_subset (H : Set.range g.base subseteq 
Set.range f.base) : IsIso (pullback.snd f g)
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.pullback.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPullback f…
· 使用定理 `CategoryTheory.IsIso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y) [I : CategoryTheory.IsIso f] {Z : 
C}   (h : Y ⟶ Z), CategoryT…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lift_fac (H : Set.range g.base ⊆ Set.range f.base) : lift f g H ≫ f = g := by
  simp [AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.lift,
    CategoryTheory.Limits.pullback.condition]
/-
**AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.lift_uniq** 是 Mathlib 中的一个定理
，位于命名空间 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion`。
形式化陈述：lift_uniq (H : Set.range g.base subseteq Set.range f.base) (l : Y ⟶ X) (hl
 : l ≫ f = g) : l = lift f g H
参数：H : Set.range g.base subseteq Set.range f.base；l : Y ⟶ X；hl : l ≫ f = g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.lift_fac`：lift_fac (H 
: Set.range g.base subseteq Set.range f.base) : lift f g H ≫ f = g
-/
theorem lift_uniq (H : Set.range g.base ⊆ Set.range f.base) (l : Y ⟶ X) (hl : l ≫ f = g) :
    l = lift f g H := by rw [← cancel_mono f, hl, lift_fac]

/-- Two open immersions with equal range is isomorphic. -/
@[simps]
/-
**AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.isoOfRangeEq** 是 Mathlib 中的一
个定义，位于命名空间 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion`。
形式化陈述：isoOfRangeEq [IsOpenImmersion g] (e : Set.range f.base = Set.range g.base)
 : X ≅ Y where hom
参数：e : Set.range f.base = Set.range g.base。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Two open immersions with equal range is isomorphic.
-/
def isoOfRangeEq [IsOpenImmersion g] (e : Set.range f.base = Set.range g.base) : X ≅ Y where
  hom := lift g f (le_of_eq e)
  inv := lift f g (le_of_eq e.symm)
  hom_inv_id := by rw [← cancel_mono f]; simp
  inv_hom_id := by rw [← cancel_mono g]; simp

end Pullback

open CategoryTheory.Limits.WalkingCospan

section ToSheafedSpace

variable {X : PresheafedSpace C} (Y : SheafedSpace C)

/-- If `X ⟶ Y` is an open immersion, and `Y` is a SheafedSpace, then so is `X`. -/
/-
**AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.toSheafedSpace** 是 Mathlib 中
的一个定义，位于命名空间 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion`。
形式化陈述：toSheafedSpace (f : X ⟶ Y.toPresheafedSpace) [H : IsOpenImmersion f] : She
afedSpace C where IsSheaf
参数：f : X ⟶ Y.toPresheafedSpace。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `X ⟶ Y` is an open immersion, and `Y` is a SheafedSpace, then so is `X`.
-/
def toSheafedSpace (f : X ⟶ Y.toPresheafedSpace) [H : IsOpenImmersion f] : SheafedSpace C where
  IsSheaf := by
    apply TopCat.Presheaf.isSheaf_of_iso (sheafIsoOfIso (isoRestrict f).symm).symm
    apply TopCat.Sheaf.pushforward_sheaf_of_sheaf
    exact (Y.restrict H.base_open).IsSheaf
  toPresheafedSpace := X

variable (f : X ⟶ Y.toPresheafedSpace) [H : IsOpenImmersion f]

@[simp]
/-
**AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.toSheafedSpace_toPresheafedS
pace** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersio
n`。
形式化陈述：toSheafedSpace_toPresheafedSpace : (toSheafedSpace Y f).toPresheafedSpace 
= X
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toSheafedSpace_toPresheafedSpace : (toSheafedSpace Y f).toPresheafedSpace = X :=
  rfl

/-- If `X ⟶ Y` is an open immersion of PresheafedSpaces, and `Y` is a SheafedSpace, we can
upgrade it into a morphism of SheafedSpaces.
-/
/-
**AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.toSheafedSpaceHom** 是 Mathli
b 中的一个定义，位于命名空间 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion`。
形式化陈述：toSheafedSpaceHom : toSheafedSpace Y f ⟶ Y
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `X ⟶ Y` is an open immersion of PresheafedSpaces, and `Y` is a SheafedSpace, 
we can
upgrade it into a morphism of SheafedSpaces.
-/
def toSheafedSpaceHom : toSheafedSpace Y f ⟶ Y :=
  InducedCategory.homMk f

@[simp]
/-
**AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.toSheafedSpaceHom_hom_base**
 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion`。
形式化陈述：toSheafedSpaceHom_hom_base : (toSheafedSpaceHom Y f).hom.base = f.base
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toSheafedSpaceHom_hom_base : (toSheafedSpaceHom Y f).hom.base = f.base :=
  rfl

@[simp]
/-
**AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.toSheafedSpaceHom_hom_c** 是 
Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion`。
形式化陈述：toSheafedSpaceHom_hom_c : (toSheafedSpaceHom Y f).hom.c = f.c
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toSheafedSpaceHom_hom_c : (toSheafedSpaceHom Y f).hom.c = f.c :=
  rfl
/-
**AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.toSheafedSpace_isOpenImmersi
on** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion`
。
形式化陈述：toSheafedSpace_isOpenImmersion : SheafedSpace.IsOpenImmersion (toSheafedSp
aceHom Y f)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance toSheafedSpace_isOpenImmersion : SheafedSpace.IsOpenImmersion (toSheafedSpaceHom Y f) :=
  H

@[simp]
/-
**AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.sheafedSpace_toSheafedSpace*
* 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion`。
形式化陈述：sheafedSpace_toSheafedSpace {X Y : SheafedSpace C} (f : X ⟶ Y) [SheafedSpa
ce.IsOpenImmersion f] : toSheafedSpace Y f.hom = X
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem sheafedSpace_toSheafedSpace {X Y : SheafedSpace C} (f : X ⟶ Y)
    [SheafedSpace.IsOpenImmersion f] :
    toSheafedSpace Y f.hom = X := by cases X; rfl

end ToSheafedSpace

section ToLocallyRingedSpace

variable {X : PresheafedSpace CommRingCat} (Y : LocallyRingedSpace)
variable (f : X ⟶ Y.toPresheafedSpace) [H : IsOpenImmersion f]

set_option backward.isDefEq.respectTransparency.types false in
/-- If `X ⟶ Y` is an open immersion, and `Y` is a LocallyRingedSpace, then so is `X`. -/
/-
**AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.toLocallyRingedSpace** 是 Mat
hlib 中的一个定义，位于命名空间 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion`。
形式化陈述：toLocallyRingedSpace : LocallyRingedSpace where toSheafedSpace
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `X ⟶ Y` is an open immersion, and `Y` is a LocallyRingedSpace, then so is `X`
.
-/
def toLocallyRingedSpace : LocallyRingedSpace where
  toSheafedSpace := toSheafedSpace Y.toSheafedSpace f
  isLocalRing x :=
    haveI : IsLocalRing (Y.presheaf.stalk (f.base x)) := Y.isLocalRing _
    (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv.isLocalRing

@[simp]
/-
**AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.toLocallyRingedSpace_toSheaf
edSpace** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry.PresheafedSpace.IsOpenImmer
sion`。
形式化陈述：toLocallyRingedSpace_toSheafedSpace : (toLocallyRingedSpace Y f).toSheafed
Space = toSheafedSpace Y.1 f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toLocallyRingedSpace_toSheafedSpace :
    (toLocallyRingedSpace Y f).toSheafedSpace = toSheafedSpace Y.1 f :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- If `X ⟶ Y` is an open immersion of PresheafedSpaces, and `Y` is a LocallyRingedSpace, we can
upgrade it into a morphism of LocallyRingedSpace.
-/
/-
**AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.toLocallyRingedSpaceHom** 是 
Mathlib 中的一个定义，位于命名空间 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion`。
形式化陈述：toLocallyRingedSpaceHom : toLocallyRingedSpace Y f ⟶ Y
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `X ⟶ Y` is an open immersion of PresheafedSpaces, and `Y` is a LocallyRingedS
pace, we can
upgrade it into a morphism of LocallyRingedSpace.
-/
def toLocallyRingedSpaceHom : toLocallyRingedSpace Y f ⟶ Y :=
  ⟨f, fun _ => inferInstance⟩

@[simp]
/-
**AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.toLocallyRingedSpaceHom_val*
* 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion`。
形式化陈述：toLocallyRingedSpaceHom_val : (toLocallyRingedSpaceHom Y f).toShHom = Indu
cedCategory.homMk f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toLocallyRingedSpaceHom_val :
    (toLocallyRingedSpaceHom Y f).toShHom = InducedCategory.homMk f :=
  rfl
/-
**AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.toLocallyRingedSpace_isOpenI
mmersion** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.PresheafedSpace.IsOpenImme
rsion`。
形式化陈述：toLocallyRingedSpace_isOpenImmersion : LocallyRingedSpace.IsOpenImmersion 
(toLocallyRingedSpaceHom Y f)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance toLocallyRingedSpace_isOpenImmersion :
    LocallyRingedSpace.IsOpenImmersion (toLocallyRingedSpaceHom Y f) :=
  H

@[simp]
/-
**AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.locallyRingedSpace_toLocally
RingedSpace** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry.PresheafedSpace.IsOpenI
mmersion`。
形式化陈述：locallyRingedSpace_toLocallyRingedSpace {X Y : LocallyRingedSpace} (f : X 
⟶ Y) [LocallyRingedSpace.IsOpenImmersion f] : toLocallyRingedSpace Y f.toHom = X
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.instIsOpenImmersionCommRingCatOfIsOpenImmersion`：∀ {X 
Y : AlgebraicGeometry.LocallyRingedSpace} (f : X ⟶ Y) [AlgebraicGeometry.Locally
RingedSpace.IsOpenImmersion f],   AlgebraicGeometry.Pre…
-/
theorem locallyRingedSpace_toLocallyRingedSpace {X Y : LocallyRingedSpace} (f : X ⟶ Y)
    [LocallyRingedSpace.IsOpenImmersion f] : toLocallyRingedSpace Y f.toHom = X :=
  rfl

end ToLocallyRingedSpace

/-
**AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.isIso_of_subset** 是 Mathlib 
中的一个定理，位于命名空间 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion`。
形式化陈述：isIso_of_subset {X Y : PresheafedSpace C} (f : X ⟶ Y) [H : PresheafedSpace
.IsOpenImmersion f] (U : Opens Y.carrier) (hU : (U : Set Y.carrier) subseteq Set
.range f.base) : IsIso (f.c.app <| op U)
参数：f : X ⟶ Y；U : Opens Y.carrier；hU : (U : Set Y.carrier) subseteq Set.range f.b
ase。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.base_open`：∀ {C : Type
 u} {inst : CategoryTheory.Category.{v, u} C} {X Y : AlgebraicGeometry.Presheafe
dSpace C} {f : X ⟶ Y}   [self : AlgebraicGeometry…
· 使用定理 `TopologicalSpace.Opens.ext`：ext {U V : Opens α} (h : (U : Set α) = V) : 
U = V
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.inter_eq_left`：∀ {α : Type u} {s t : Set α}, s ∩ t = s ↔ s ⊆ t
· 使用定理 `Set.image_preimage_eq_inter_range`：image_preimage_eq_inter_range {f : α 
-> β} {t : Set β} : f '' f ⁻¹' t = t inter range f
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.c_iso`：∀ {C : Type u} 
{inst : CategoryTheory.Category.{v, u} C} {X Y : AlgebraicGeometry.PresheafedSpa
ce C} {f : X ⟶ Y}   [self : AlgebraicGeometry…
-/
theorem isIso_of_subset {X Y : PresheafedSpace C} (f : X ⟶ Y)
    [H : PresheafedSpace.IsOpenImmersion f] (U : Opens Y.carrier)
    (hU : (U : Set Y.carrier) ⊆ Set.range f.base) : IsIso (f.c.app <| op U) := by
  have : U = H.base_open.functor.obj ((Opens.map f.base).obj U) := by
    ext1
    exact (Set.inter_eq_left.mpr hU).symm.trans Set.image_preimage_eq_inter_range.symm
  convert! H.c_iso ((Opens.map f.base).obj U)

end PresheafedSpace.IsOpenImmersion

namespace SheafedSpace.IsOpenImmersion

/-
**AlgebraicGeometry.SheafedSpace.IsOpenImmersion.** 是 Mathlib 中的一个实例，位于命名空间 `Alg
ebraicGeometry.SheafedSpace.IsOpenImmersion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) of_isIso {X Y : SheafedSpace C} (f : X ⟶ Y) [IsIso f] :
    SheafedSpace.IsOpenImmersion f :=
  @PresheafedSpace.IsOpenImmersion.ofIsIso _ _ _ _ f.hom
    (SheafedSpace.forgetToPresheafedSpace.map_isIso _)
/-
**AlgebraicGeometry.SheafedSpace.IsOpenImmersion.comp** 是 Mathlib 中的一个实例，位于命名空间 
`AlgebraicGeometry.SheafedSpace.IsOpenImmersion`。
形式化陈述：comp {X Y Z : SheafedSpace C} (f : X ⟶ Y) (g : Y ⟶ Z) [SheafedSpace.IsOpen
Immersion f] [SheafedSpace.IsOpenImmersion g] : SheafedSpace.IsOpenImmersion (f 
≫ g)
参数：f : X ⟶ Y；g : Y ⟶ Z。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance comp {X Y Z : SheafedSpace C} (f : X ⟶ Y) (g : Y ⟶ Z) [SheafedSpace.IsOpenImmersion f]
    [SheafedSpace.IsOpenImmersion g] : SheafedSpace.IsOpenImmersion (f ≫ g) :=
  PresheafedSpace.IsOpenImmersion.comp f.hom g.hom

noncomputable section Pullback

variable {X Y Z : SheafedSpace C} (f : X ⟶ Z) (g : Y ⟶ Z)
variable [H : SheafedSpace.IsOpenImmersion f]

/-- This is often wrapped in parentheses to distinguish with the forgetful functor. -/
local notation "forget" => SheafedSpace.forgetToPresheafedSpace

open CategoryTheory.Limits.WalkingCospan

/-
**AlgebraicGeometry.SheafedSpace.IsOpenImmersion.** 是 Mathlib 中的一个实例，位于命名空间 `Alg
ebraicGeometry.SheafedSpace.IsOpenImmersion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Mono f :=
  (forget).mono_of_mono_map (show @Mono (PresheafedSpace C) _ _ _ f.hom by infer_instance)
/-
**AlgebraicGeometry.SheafedSpace.IsOpenImmersion.forgetMapIsOpenImmersion** 是 Ma
thlib 中的一个实例，位于命名空间 `AlgebraicGeometry.SheafedSpace.IsOpenImmersion`。
形式化陈述：forgetMapIsOpenImmersion : PresheafedSpace.IsOpenImmersion ((forget).map f
)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.base_open`：∀ {C : Type
 u} {inst : CategoryTheory.Category.{v, u} C} {X Y : AlgebraicGeometry.Presheafe
dSpace C} {f : X ⟶ Y}   [self : AlgebraicGeometry…
· 使用定理 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.c_iso`：∀ {C : Type u} 
{inst : CategoryTheory.Category.{v, u} C} {X Y : AlgebraicGeometry.PresheafedSpa
ce C} {f : X ⟶ Y}   [self : AlgebraicGeometry…
-/
instance forgetMapIsOpenImmersion : PresheafedSpace.IsOpenImmersion ((forget).map f) :=
  ⟨H.base_open, H.c_iso⟩
/-
**AlgebraicGeometry.SheafedSpace.IsOpenImmersion.hasLimit_cospan_forget_of_left*
* 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.SheafedSpace.IsOpenImmersion`。
形式化陈述：hasLimit_cospan_forget_of_left : HasLimit (cospan f g ⋙ forget)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasLimit_of_iso`：hasLimit_of_iso {F G : J ⥤ C} [Ha
sLimit F] (α : F ≅ G) : HasLimit G
-/
instance hasLimit_cospan_forget_of_left : HasLimit (cospan f g ⋙ forget) := by
  have : HasLimit (cospan ((cospan f g ⋙ forget).map Hom.inl)
      ((cospan f g ⋙ forget).map Hom.inr)) := by
    change HasLimit (cospan ((forget).map f) ((forget).map g))
    infer_instance
  apply hasLimit_of_iso (diagramIsoCospan _).symm
/-
**AlgebraicGeometry.SheafedSpace.IsOpenImmersion.hasLimit_cospan_forget_of_left'
** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.SheafedSpace.IsOpenImmersion`。
形式化陈述：hasLimit_cospan_forget_of_left' : HasLimit (cospan ((cospan f g ⋙ forget).
map Hom.inl) ((cospan f g ⋙ forget).map Hom.inr))
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasLimit_cospan_forget_of_left' :
    HasLimit (cospan ((cospan f g ⋙ forget).map Hom.inl) ((cospan f g ⋙ forget).map Hom.inr)) :=
  show HasLimit (cospan ((forget).map f) ((forget).map g)) from inferInstance
/-
**AlgebraicGeometry.SheafedSpace.IsOpenImmersion.hasLimit_cospan_forget_of_right
** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.SheafedSpace.IsOpenImmersion`。
形式化陈述：hasLimit_cospan_forget_of_right : HasLimit (cospan g f ⋙ forget)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasLimit_of_iso`：hasLimit_of_iso {F G : J ⥤ C} [Ha
sLimit F] (α : F ≅ G) : HasLimit G
-/
instance hasLimit_cospan_forget_of_right : HasLimit (cospan g f ⋙ forget) := by
  have : HasLimit (cospan ((cospan g f ⋙ forget).map Hom.inl)
      ((cospan g f ⋙ forget).map Hom.inr)) := by
    change HasLimit (cospan ((forget).map g) ((forget).map f))
    infer_instance
  apply hasLimit_of_iso (diagramIsoCospan _).symm
/-
**AlgebraicGeometry.SheafedSpace.IsOpenImmersion.hasLimit_cospan_forget_of_right
'** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.SheafedSpace.IsOpenImmersion`。
形式化陈述：hasLimit_cospan_forget_of_right' : HasLimit (cospan ((cospan g f ⋙ forget)
.map Hom.inl) ((cospan g f ⋙ forget).map Hom.inr))
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasLimit_cospan_forget_of_right' :
    HasLimit (cospan ((cospan g f ⋙ forget).map Hom.inl) ((cospan g f ⋙ forget).map Hom.inr)) :=
  show HasLimit (cospan ((forget).map g) ((forget).map f)) from inferInstance
/-
**AlgebraicGeometry.SheafedSpace.IsOpenImmersion.forgetCreatesPullbackOfLeft** 是
 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.SheafedSpace.IsOpenImmersion`。
形式化陈述：forgetCreatesPullbackOfLeft : CreatesLimit (cospan f g) forget
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance forgetCreatesPullbackOfLeft : CreatesLimit (cospan f g) forget :=
  createsLimitOfFullyFaithfulOfIso
    (PresheafedSpace.IsOpenImmersion.toSheafedSpace Y
      (@pullback.snd (PresheafedSpace C) _ _ _ _ f.hom g.hom _))
    (eqToIso (show pullback _ _ = pullback _ _ by congr) ≪≫
      HasLimit.isoOfNatIso (diagramIsoCospan _).symm)
/-
**AlgebraicGeometry.SheafedSpace.IsOpenImmersion.forgetCreatesPullbackOfRight** 
是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.SheafedSpace.IsOpenImmersion`。
形式化陈述：forgetCreatesPullbackOfRight : CreatesLimit (cospan g f) forget
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance forgetCreatesPullbackOfRight : CreatesLimit (cospan g f) forget :=
  createsLimitOfFullyFaithfulOfIso
    (PresheafedSpace.IsOpenImmersion.toSheafedSpace Y
      (@pullback.fst (PresheafedSpace C) _ _ _ _ g.hom f.hom _))
    (eqToIso (show pullback _ _ = pullback _ _ by congr) ≪≫
      HasLimit.isoOfNatIso (diagramIsoCospan _).symm)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**AlgebraicGeometry.SheafedSpace.IsOpenImmersion.sheafedSpace_forgetPreserves_of
_left** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.SheafedSpace.IsOpenImmersion`
。
形式化陈述：sheafedSpace_forgetPreserves_of_left : PreservesLimit (cospan f g) (Sheafe
dSpace.forget C)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.preservesLimit_of_createsLimit_and_hasLimit`：∀ {C : Type 
u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Category
Theory.Category.{v₂, u₂} D]   {J : Type w} [inst…
· 使用引理 `CategoryTheory.Limits.preservesLimit_of_iso_diagram`：preservesLimit_of_i
so_diagram {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂) [PreservesLimit K₁ F] : Pre
servesLimit K₂ F where preserves {c} t
-/
instance sheafedSpace_forgetPreserves_of_left :
    PreservesLimit (cospan f g) (SheafedSpace.forget C) :=
  @Limits.comp_preservesLimit _ _ _ _ _ _ (cospan f g) _ _ forget (PresheafedSpace.forget C)
    inferInstance <| by
      have : PreservesLimit
        (cospan ((cospan f g ⋙ forget).map Hom.inl)
          ((cospan f g ⋙ forget).map Hom.inr)) (PresheafedSpace.forget C) := by
        dsimp
        infer_instance
      apply preservesLimit_of_iso_diagram _ (diagramIsoCospan _).symm
/-
**AlgebraicGeometry.SheafedSpace.IsOpenImmersion.sheafedSpace_forgetPreserves_of
_right** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.SheafedSpace.IsOpenImmersion
`。
形式化陈述：sheafedSpace_forgetPreserves_of_right : PreservesLimit (cospan g f) (Sheaf
edSpace.forget C)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesPullback_symmetry`：preservesPullback_symm
etry : PreservesLimit (cospan g f) G where preserves {c} hc
-/
instance sheafedSpace_forgetPreserves_of_right :
    PreservesLimit (cospan g f) (SheafedSpace.forget C) :=
  preservesPullback_symmetry _ _ _
/-
**AlgebraicGeometry.SheafedSpace.IsOpenImmersion.sheafedSpace_hasPullback_of_lef
t** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.SheafedSpace.IsOpenImmersion`。
形式化陈述：sheafedSpace_hasPullback_of_left : HasPullback f g
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.hasLimit_of_created`：hasLimit_of_created (K : J ⥤ C) (F :
 C ⥤ D) [HasLimit (K ⋙ F)] [CreatesLimit K F] : HasLimit K
-/
instance sheafedSpace_hasPullback_of_left : HasPullback f g :=
  hasLimit_of_created (cospan f g) forget
/-
**AlgebraicGeometry.SheafedSpace.IsOpenImmersion.sheafedSpace_hasPullback_of_rig
ht** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.SheafedSpace.IsOpenImmersion`。
形式化陈述：sheafedSpace_hasPullback_of_right : HasPullback g f
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.hasLimit_of_created`：hasLimit_of_created (K : J ⥤ C) (F :
 C ⥤ D) [HasLimit (K ⋙ F)] [CreatesLimit K F] : HasLimit K
-/
instance sheafedSpace_hasPullback_of_right : HasPullback g f :=
  hasLimit_of_created (cospan g f) forget

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Open immersions are stable under base-change. -/
/-
**AlgebraicGeometry.SheafedSpace.IsOpenImmersion.sheafedSpace_pullback_snd_of_le
ft** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.SheafedSpace.IsOpenImmersion`。
形式化陈述：sheafedSpace_pullback_snd_of_left : SheafedSpace.IsOpenImmersion (pullback
.snd f g)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.SheafedSpace.isOpenImmersion_iff_hom`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {X Y : AlgebraicGeometry.SheafedSpace C
} (f : X ⟶ Y),   AlgebraicGeometry.SheafedSp…
· 使用定理 `CategoryTheory.Limits.instHasLimitCompOfPreservesLimit`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `CategoryTheory.preservesLimit_of_createsLimit_and_hasLimit`：∀ {C : Type 
u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Category
Theory.Category.{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `CategoryTheory.preservesLimitIso_hom_π`：preservesLimitIso_hom_π (j) : (p
reservesLimitIso G F).hom ≫ limit.π _ j = G.map (limit.π F j)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.HasLimit.isoOfNatIso_hom_π`：∀ {J : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Cate
gory.{v, u} C]   {F G : CategoryTheory…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…

--- 原说明 ---
Open immersions are stable under base-change.
-/
instance sheafedSpace_pullback_snd_of_left :
    SheafedSpace.IsOpenImmersion (pullback.snd f g) := by
  rw [SheafedSpace.isOpenImmersion_iff_hom]
  have : _ = (pullback.snd f g).hom := preservesLimitIso_hom_π forget (cospan f g) right
  rw [← this]
  have := HasLimit.isoOfNatIso_hom_π (diagramIsoCospan (cospan f g ⋙ forget)) right
  dsimp at this
  rw [Category.comp_id] at this
  rw [← this]
  infer_instance

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.SheafedSpace.IsOpenImmersion.sheafedSpace_pullback_fst_of_ri
ght** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.SheafedSpace.IsOpenImmersion`。
形式化陈述：sheafedSpace_pullback_fst_of_right : SheafedSpace.IsOpenImmersion (pullbac
k.fst g f)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.SheafedSpace.isOpenImmersion_iff_hom`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {X Y : AlgebraicGeometry.SheafedSpace C
} (f : X ⟶ Y),   AlgebraicGeometry.SheafedSp…
· 使用定理 `CategoryTheory.Limits.instHasLimitCompOfPreservesLimit`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `CategoryTheory.preservesLimit_of_createsLimit_and_hasLimit`：∀ {C : Type 
u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Category
Theory.Category.{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `CategoryTheory.preservesLimitIso_hom_π`：preservesLimitIso_hom_π (j) : (p
reservesLimitIso G F).hom ≫ limit.π _ j = G.map (limit.π F j)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.HasLimit.isoOfNatIso_hom_π`：∀ {J : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Cate
gory.{v, u} C]   {F G : CategoryTheory…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
instance sheafedSpace_pullback_fst_of_right :
    SheafedSpace.IsOpenImmersion (pullback.fst g f) := by
  rw [SheafedSpace.isOpenImmersion_iff_hom]
  have : _ = (pullback.fst g f).hom := preservesLimitIso_hom_π forget (cospan g f) left
  rw [← this]
  have := HasLimit.isoOfNatIso_hom_π (diagramIsoCospan (cospan g f ⋙ forget)) left
  dsimp at this
  rw [Category.comp_id] at this
  rw [← this]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.SheafedSpace.IsOpenImmersion.sheafedSpace_pullback_to_base_i
sOpenImmersion** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.SheafedSpace.IsOpenI
mmersion`。
形式化陈述：sheafedSpace_pullback_to_base_isOpenImmersion [SheafedSpace.IsOpenImmersio
n g] : SheafedSpace.IsOpenImmersion (limit.π (cospan f g) one : pullback f g ⟶ Z
)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.limit.w`：∀ {J : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]   (F
 : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.cospan_map_inl`：cospan_map_inl {X Y Z : C} (f : X 
⟶ Z) (g : Y ⟶ Z) : (cospan f g).map WalkingCospan.Hom.inl = f
-/
instance sheafedSpace_pullback_to_base_isOpenImmersion [SheafedSpace.IsOpenImmersion g] :
    SheafedSpace.IsOpenImmersion (limit.π (cospan f g) one : pullback f g ⟶ Z) := by
  rw [← limit.w (cospan f g) Hom.inl, cospan_map_inl]
  infer_instance

end Pullback

section OfStalkIso

variable [HasLimits C] [HasColimits C] {FC : C → C → Type*} {CC : C → Type v}
variable [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [instCC : ConcreteCategory.{v} C FC]
variable [(CategoryTheory.forget C).ReflectsIsomorphisms]
  [PreservesLimits (CategoryTheory.forget C)]

variable [PreservesFilteredColimits (CategoryTheory.forget C)]

set_option backward.isDefEq.respectTransparency false in
include instCC in
/-- Suppose `X Y : SheafedSpace C`, where `C` is a concrete category,
whose forgetful functor reflects isomorphisms, preserves limits and filtered colimits.
Then a morphism `X ⟶ Y` that is a topological open embedding
is an open immersion iff every stalk map is an iso.
-/
/-
**AlgebraicGeometry.SheafedSpace.IsOpenImmersion.of_stalk_iso** 是 Mathlib 中的一个定理
，位于命名空间 `AlgebraicGeometry.SheafedSpace.IsOpenImmersion`。
形式化陈述：of_stalk_iso {X Y : SheafedSpace C} (f : X ⟶ Y) (hf : IsOpenEmbedding f.ho
m.base) [H : forall x : X.1, IsIso (f.hom.stalkMap x)] : SheafedSpace.IsOpenImme
rsion f
参数：f : X ⟶ Y；hf : IsOpenEmbedding f.hom.base；f.hom.stalkMap x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopCat.Presheaf.app_isIso_of_stalkFunctor_map_iso`：app_isIso_of_stalkFun
ctor_map_iso {F G : Sheaf C X} (f : F ⟶ G) (U : Opens X) [forall x : U, IsIso ((
stalkFunctor C x.val).map f.1)] : IsIso…
· 使用定理 `TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing`：sta
lkPushforward_iso_of_isInducing {f : X ⟶ Y} (hf : IsInducing f) (F : X.Presheaf 
C) (x : X) : IsIso (F.stalkPushforward _ f x)
· 使用定理 `Topology.IsEmbedding.toIsInducing`：∀ {X : Type u_1} {Y : Type u_2} [tX :
 TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbeddi
ng f → Topology.IsInduc…
· 使用定理 `Topology.IsOpenEmbedding.toIsEmbedding`：∀ {X : Type u_1} {Y : Type u_2} 
[tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsOp
enEmbedding f → Topology.IsE…
· 使用引理 `CategoryTheory.IsIso.comp_isIso'`：comp_isIso' (_ : IsIso f) (_ : IsIso h
) : IsIso (f ≫ h)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.IsIso.hom_inv_id`：hom_inv_id (f : X ⟶ Y) [I : IsIso f] : 
f ≫ inv f = 𝟙 X
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…

--- 原说明 ---
Suppose `X Y : SheafedSpace C`, where `C` is a concrete category,
whose forgetful functor reflects isomorphisms, preserves limits and filtered col
imits.
Then a morphism `X ⟶ Y` that is a topological open embedding
is an open immersion iff every stalk map is an iso.
-/
theorem of_stalk_iso {X Y : SheafedSpace C} (f : X ⟶ Y) (hf : IsOpenEmbedding f.hom.base)
    [H : ∀ x : X.1, IsIso (f.hom.stalkMap x)] : SheafedSpace.IsOpenImmersion f :=
  { base_open := hf
    c_iso := fun U => by
      apply +allowSynthFailures TopCat.Presheaf.app_isIso_of_stalkFunctor_map_iso
          (show Y.sheaf ⟶ (TopCat.Sheaf.pushforward _ f.hom.base).obj X.sheaf from ⟨f.hom.c⟩)
      rintro ⟨_, y, hy, rfl⟩
      specialize H y
      delta PresheafedSpace.Hom.stalkMap at H
      have H' := TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing C
        hf.toIsInducing X.presheaf y
      have := IsIso.comp_isIso' H (@IsIso.inv_isIso _ _ _ _ _ H')
      rwa [Category.assoc, IsIso.hom_inv_id, Category.comp_id] at this }

end OfStalkIso

section

variable {X Y : SheafedSpace C} (f : X ⟶ Y) [H : IsOpenImmersion f]

/-- The functor `Opens X ⥤ Opens Y` associated with an open immersion `f : X ⟶ Y`. -/
/-
**AlgebraicGeometry.SheafedSpace.IsOpenImmersion.opensFunctor** 是 Mathlib 中的一个缩写
定义，位于命名空间 `AlgebraicGeometry.SheafedSpace.IsOpenImmersion`。
形式化陈述：opensFunctor : Opens X ⥤ Opens Y
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `Opens X ⥤ Opens Y` associated with an open immersion `f : X ⟶ Y`.
-/
abbrev opensFunctor : Opens X ⥤ Opens Y :=
  H.base_open.functor

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- An open immersion `f : X ⟶ Y` induces an isomorphism `X ≅ Y|_{f(X)}`. -/
@[simps! hom_hom_c_app]
/-
**AlgebraicGeometry.SheafedSpace.IsOpenImmersion.isoRestrict** 是 Mathlib 中的一个定义，
位于命名空间 `AlgebraicGeometry.SheafedSpace.IsOpenImmersion`。
形式化陈述：isoRestrict : X ≅ Y.restrict H.base_open
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An open immersion `f : X ⟶ Y` induces an isomorphism `X ≅ Y|_{f(X)}`.
-/
noncomputable def isoRestrict : X ≅ Y.restrict H.base_open :=
  SheafedSpace.isoMk <| PresheafedSpace.IsOpenImmersion.isoRestrict f.hom

@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.SheafedSpace.IsOpenImmersion.isoRestrict_hom_ofRestrict** 是 
Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry.SheafedSpace.IsOpenImmersion`。
形式化陈述：isoRestrict_hom_ofRestrict : (isoRestrict f).hom ≫ Y.ofRestrict _ = f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.InducedCategory.hom_ext`：hom_ext {X Y : InducedCategory D
 F} {f g : X ⟶ Y} (h : f.hom = g.hom) : f = g
· 使用定理 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.base_open`：∀ {C : Type
 u} {inst : CategoryTheory.Category.{v, u} C} {X Y : AlgebraicGeometry.Presheafe
dSpace C} {f : X ⟶ Y}   [self : AlgebraicGeometry…
· 使用定理 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.isoRestrict_hom_ofRest
rict`：isoRestrict_hom_ofRestrict : (isoRestrict f).hom ≫ Y.ofRestrict _ = f
-/
theorem isoRestrict_hom_ofRestrict : (isoRestrict f).hom ≫ Y.ofRestrict _ = f :=
  InducedCategory.hom_ext
    (PresheafedSpace.IsOpenImmersion.isoRestrict_hom_ofRestrict f.hom)

@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.SheafedSpace.IsOpenImmersion.isoRestrict_inv_ofRestrict** 是 
Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry.SheafedSpace.IsOpenImmersion`。
形式化陈述：isoRestrict_inv_ofRestrict : (isoRestrict f).inv ≫ f = Y.ofRestrict _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.InducedCategory.hom_ext`：hom_ext {X Y : InducedCategory D
 F} {f g : X ⟶ Y} (h : f.hom = g.hom) : f = g
· 使用定理 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.base_open`：∀ {C : Type
 u} {inst : CategoryTheory.Category.{v, u} C} {X Y : AlgebraicGeometry.Presheafe
dSpace C} {f : X ⟶ Y}   [self : AlgebraicGeometry…
· 使用定理 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.isoRestrict_inv_ofRest
rict`：isoRestrict_inv_ofRestrict : (isoRestrict f).inv ≫ f = Y.ofRestrict _
-/
theorem isoRestrict_inv_ofRestrict : (isoRestrict f).inv ≫ f = Y.ofRestrict _ :=
  InducedCategory.hom_ext
    (PresheafedSpace.IsOpenImmersion.isoRestrict_inv_ofRestrict f.hom)

/-- For an open immersion `f : X ⟶ Y` and an open set `U ⊆ X`, we have the map `X(U) ⟶ Y(U)`. -/
/-
**AlgebraicGeometry.SheafedSpace.IsOpenImmersion.invApp** 是 Mathlib 中的一个定义，位于命名空
间 `AlgebraicGeometry.SheafedSpace.IsOpenImmersion`。
形式化陈述：invApp (U : Opens X) : X.presheaf.obj (op U) ⟶ Y.presheaf.obj (op (opensFu
nctor f |>.obj U))
参数：U : Opens X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For an open immersion `f : X ⟶ Y` and an open set `U ⊆ X`, we have the map `X(U)
 ⟶ Y(U)`.
-/
noncomputable def invApp (U : Opens X) :
    X.presheaf.obj (op U) ⟶ Y.presheaf.obj (op (opensFunctor f |>.obj U)) :=
  PresheafedSpace.IsOpenImmersion.invApp f.hom U

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.SheafedSpace.IsOpenImmersion.inv_naturality** 是 Mathlib 中的一个
定理，位于命名空间 `AlgebraicGeometry.SheafedSpace.IsOpenImmersion`。
形式化陈述：inv_naturality {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) : X.presheaf.map i ≫ H.invA
pp _ (unop V) = H.invApp _ (unop U) ≫ Y.presheaf.map (opensFunctor f |>.op.map i
)
参数：Opens X；i : U ⟶ V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.inv_naturality`：inv_na
turality {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) : X.presheaf.map i ≫ H.invApp _ (unop V
) = invApp f (unop U) ≫ Y.presheaf.map (opensFunctor f…

--- 原说明 ---
`respectTransparency.types true` changes the auto-generated lemmas' signature
-/
theorem inv_naturality {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) :
    X.presheaf.map i ≫ H.invApp _ (unop V) =
      H.invApp _ (unop U) ≫ Y.presheaf.map (opensFunctor f |>.op.map i) :=
  PresheafedSpace.IsOpenImmersion.inv_naturality f.hom i
/-
**AlgebraicGeometry.SheafedSpace.IsOpenImmersion.** 是 Mathlib 中的一个实例，位于命名空间 `Alg
ebraicGeometry.SheafedSpace.IsOpenImmersion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (U : Opens X) : IsIso (H.invApp _ U) := by delta invApp; infer_instance
/-
**AlgebraicGeometry.SheafedSpace.IsOpenImmersion.inv_invApp** 是 Mathlib 中的一个定理，位
于命名空间 `AlgebraicGeometry.SheafedSpace.IsOpenImmersion`。
形式化陈述：inv_invApp (U : Opens X) : inv (H.invApp _ U) = f.hom.c.app (op (opensFunc
tor f |>.obj U)) ≫ X.presheaf.map (eqToHom (by simp [Opens.map_def, Set.preimage
_image_eq _ H.base_open.injective]))
参数：U : Opens X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.inv_invApp`：inv_invApp
 (U : Opens X) : inv (H.invApp _ U) = f.c.app (op (opensFunctor f |>.obj U)) ≫ X
.presheaf.map (eqToHom (by simp [Opens.map_def, Se…
-/
theorem inv_invApp (U : Opens X) :
    inv (H.invApp _ U) =
      f.hom.c.app (op (opensFunctor f |>.obj U)) ≫ X.presheaf.map
        (eqToHom (by simp [Opens.map_def, Set.preimage_image_eq _ H.base_open.injective])) :=
  PresheafedSpace.IsOpenImmersion.inv_invApp f.hom U

@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.SheafedSpace.IsOpenImmersion.invApp_app** 是 Mathlib 中的一个定理，位
于命名空间 `AlgebraicGeometry.SheafedSpace.IsOpenImmersion`。
形式化陈述：invApp_app (U : Opens X) : H.invApp _ U ≫ f.hom.c.app (op (opensFunctor f 
|>.obj U)) = X.presheaf.map (eqToHom (by simp [Opens.map_def, Set.preimage_image
_eq _ H.base_open.injective]))
参数：U : Opens X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.invApp_app`：invApp_app
 (U : Opens X) : invApp f U ≫ f.c.app (op (opensFunctor f |>.obj U)) = X.preshea
f.map (eqToHom (by simp [Opens.map_def, Set.preima…
-/
theorem invApp_app (U : Opens X) :
    H.invApp _ U ≫ f.hom.c.app (op (opensFunctor f |>.obj U)) = X.presheaf.map
      (eqToHom (by simp [Opens.map_def, Set.preimage_image_eq _ H.base_open.injective])) :=
  PresheafedSpace.IsOpenImmersion.invApp_app f.hom U

attribute [elementwise] invApp_app

@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.SheafedSpace.IsOpenImmersion.app_invApp** 是 Mathlib 中的一个定理，位
于命名空间 `AlgebraicGeometry.SheafedSpace.IsOpenImmersion`。
形式化陈述：app_invApp (U : Opens Y) : f.hom.c.app (op U) ≫ H.invApp _ ((Opens.map f.h
om.base).obj U) = Y.presheaf.map ((homOfLE (Set.image_preimage_subset f.hom.base
 U.1)).op : op U ⟶ op (opensFunctor f |>.obj ((Opens.map f.hom.base).obj U)))
参数：U : Opens Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.app_invApp`：app_invApp
 (U : Opens Y) : f.c.app (op U) ≫ H.invApp _ ((Opens.map f.base).obj U) = Y.pres
heaf.map ((homOfLE (Set.image_preimage_subset f.ba…
-/
theorem app_invApp (U : Opens Y) :
    f.hom.c.app (op U) ≫ H.invApp _ ((Opens.map f.hom.base).obj U) =
      Y.presheaf.map
        ((homOfLE (Set.image_preimage_subset f.hom.base U.1)).op :
          op U ⟶ op (opensFunctor f |>.obj ((Opens.map f.hom.base).obj U))) :=
  PresheafedSpace.IsOpenImmersion.app_invApp f.hom U

/-- A variant of `app_inv_app` that gives an `eqToHom` instead of `homOfLe`. -/
@[reassoc]
/-
**AlgebraicGeometry.SheafedSpace.IsOpenImmersion.app_inv_app'** 是 Mathlib 中的一个定理
，位于命名空间 `AlgebraicGeometry.SheafedSpace.IsOpenImmersion`。
形式化陈述：app_inv_app' (U : Opens Y) (hU : (U : Set Y) subseteq Set.range f.hom.base
) : f.hom.c.app (op U) ≫ invApp f ((Opens.map f.hom.base).obj U) = Y.presheaf.ma
p (eqToHom <| le_antisymm (Set.image_preimage_subset f.hom.base U.1) (Set.image_
preimage_eq_inter_range (f
参数：U : Opens Y；hU : (U : Set Y) subseteq Set.range f.hom.base。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.app_invApp`：app_invApp
 (U : Opens Y) : f.c.app (op U) ≫ H.invApp _ ((Opens.map f.base).obj U) = Y.pres
heaf.map ((homOfLE (Set.image_preimage_subset f.ba…

--- 原说明 ---
A variant of `app_inv_app` that gives an `eqToHom` instead of `homOfLe`.
-/
theorem app_inv_app' (U : Opens Y) (hU : (U : Set Y) ⊆ Set.range f.hom.base) :
    f.hom.c.app (op U) ≫ invApp f ((Opens.map f.hom.base).obj U) =
      Y.presheaf.map
        (eqToHom <|
            le_antisymm (Set.image_preimage_subset f.hom.base U.1) <|
              (Set.image_preimage_eq_inter_range (f := f.hom.base) (t := U.1)).symm ▸
                Set.subset_inter_iff.mpr ⟨fun _ h => h, hU⟩).op :=
  PresheafedSpace.IsOpenImmersion.app_invApp f.hom U
/-
**AlgebraicGeometry.SheafedSpace.IsOpenImmersion.ofRestrict** 是 Mathlib 中的一个实例，位
于命名空间 `AlgebraicGeometry.SheafedSpace.IsOpenImmersion`。
形式化陈述：ofRestrict {X : TopCat.{w}} (Y : SheafedSpace C) {f : X ⟶ Y.carrier} (hf :
 IsOpenEmbedding f) : IsOpenImmersion (Y.ofRestrict hf)
参数：Y : SheafedSpace C；hf : IsOpenEmbedding f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance ofRestrict {X : TopCat.{w}} (Y : SheafedSpace C) {f : X ⟶ Y.carrier}
    (hf : IsOpenEmbedding f) : IsOpenImmersion (Y.ofRestrict hf) :=
  PresheafedSpace.IsOpenImmersion.ofRestrict _ hf

@[elementwise, simp]
/-
**AlgebraicGeometry.SheafedSpace.IsOpenImmersion.ofRestrict_invApp** 是 Mathlib 中
的一个定理，位于命名空间 `AlgebraicGeometry.SheafedSpace.IsOpenImmersion`。
形式化陈述：ofRestrict_invApp {C : Type*} [Category* C] (X : SheafedSpace C) {Y : TopC
at.{w}} {f : Y ⟶ TopCat.of X.carrier} (h : IsOpenEmbedding f) (U : Opens (X.rest
rict h).carrier) : (SheafedSpace.IsOpenImmersion.ofRestrict X h).invApp _ U = 𝟙 
_
参数：X : SheafedSpace C；h : IsOpenEmbedding f；U : Opens (X.restrict h).carrier。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.ofRestrict_invApp`：ofR
estrict_invApp {C : Type*} [Category* C] (X : PresheafedSpace C) {Y : TopCat.{w}
} {f : Y ⟶ TopCat.of X.carrier} (h : IsOpenEmbedding f) (…
-/
theorem ofRestrict_invApp {C : Type*} [Category* C] (X : SheafedSpace C) {Y : TopCat.{w}}
    {f : Y ⟶ TopCat.of X.carrier} (h : IsOpenEmbedding f) (U : Opens (X.restrict h).carrier) :
    (SheafedSpace.IsOpenImmersion.ofRestrict X h).invApp _ U = 𝟙 _ :=
  PresheafedSpace.IsOpenImmersion.ofRestrict_invApp _ h U

/-- An open immersion is an iso if the underlying continuous map is epi. -/
/-
**AlgebraicGeometry.SheafedSpace.IsOpenImmersion.to_iso** 是 Mathlib 中的一个定理，位于命名空
间 `AlgebraicGeometry.SheafedSpace.IsOpenImmersion`。
形式化陈述：to_iso [h' : Epi f.hom.base] : IsIso f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.to_iso`：to_iso [h' : E
pi f.base] : IsIso f
· 使用定理 `CategoryTheory.isIso_of_reflects_iso`：isIso_of_reflects_iso {A B : C} (f
 : A ⟶ B) (F : C ⥤ D) [IsIso (F.map f)] [F.ReflectsIsomorphisms] : IsIso f
· 使用定理 `CategoryTheory.reflectsIsomorphisms_of_full_and_faithful`：∀ {C : Type u_
1} [inst : CategoryTheory.Category.{v_1, u_1} C] {D : Type u_2}   [inst_1 : Cate
goryTheory.Category.{v_2, u_2} D] (F : Categor…

--- 原说明 ---
An open immersion is an iso if the underlying continuous map is epi.
-/
theorem to_iso [h' : Epi f.hom.base] : IsIso f := by
  have : IsIso (forgetToPresheafedSpace.map f) := PresheafedSpace.IsOpenImmersion.to_iso f.hom
  apply isIso_of_reflects_iso _ (SheafedSpace.forgetToPresheafedSpace)
/-
**AlgebraicGeometry.SheafedSpace.IsOpenImmersion.stalk_iso** 是 Mathlib 中的一个实例，位于
命名空间 `AlgebraicGeometry.SheafedSpace.IsOpenImmersion`。
形式化陈述：stalk_iso [HasColimits C] (x : X) : IsIso (f.hom.stalkMap x)
参数：x : X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance stalk_iso [HasColimits C] (x : X) :
    IsIso (f.hom.stalkMap x) :=
  PresheafedSpace.IsOpenImmersion.stalk_iso f.hom x

end

section Prod

-- here `ι` should have same universe level as morphism of `C`, so needs explicit universe level
variable [HasLimits C] {ι : Type v} (F : Discrete ι ⥤ SheafedSpace.{_, v, v} C) [HasColimit F]
  (i : Discrete ι)

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.SheafedSpace.IsOpenImmersion.sigma_** 是 Mathlib 中的一个定理，位于命名空
间 `AlgebraicGeometry.SheafedSpace.IsOpenImmersion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sigma_ι_isOpenEmbedding : IsOpenEmbedding (colimit.ι F i).hom.base := by
  rw [← show _ = (colimit.ι F i).hom.base from
    ι_preservesColimitIso_inv (SheafedSpace.forget C) F i]
  have : _ = _ ≫ colimit.ι (Discrete.functor ((F ⋙ SheafedSpace.forget C).obj ∘ Discrete.mk)) i :=
    HasColimit.isoOfNatIso_ι_hom Discrete.natIsoFunctor i
  rw [← Iso.eq_comp_inv] at this
  rw [this]
  have : colimit.ι _ _ ≫ _ = _ :=
    TopCat.sigmaIsoSigma_hom_ι.{v, v} ((F ⋙ SheafedSpace.forget C).obj ∘ Discrete.mk) i.as
  rw [← Iso.eq_comp_inv] at this
  cases i
  rw [this, ← Category.assoc]
  simp_rw [TopCat.isOpenEmbedding_iff_comp_isIso, (TopCat.isOpenEmbedding_iff_isIso_comp)]
  exact .sigmaMk

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.SheafedSpace.IsOpenImmersion.image_preimage_is_empty** 是 Mat
hlib 中的一个定理，位于命名空间 `AlgebraicGeometry.SheafedSpace.IsOpenImmersion`。
形式化陈述：image_preimage_is_empty (j : Discrete ι) (h : i != j) (U : Opens (F.obj i)
) : (Opens.map (colimit.ι (F ⋙ SheafedSpace.forgetToPresheafedSpace) j).base).ob
j ((Opens.map (preservesColimitIso SheafedSpace.forgetToPresheafedSpace F).inv.b
ase).obj ((sigma_ι_isOpenEmbedding F i).functor.obj U)) = ⊥
参数：j : Discrete ι；h : i != j；U : Opens (F.obj i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.Opens.ext`：ext {U V : Opens α} (h : (U : Set α) = V) : 
U = V
· 使用定理 `CategoryTheory.Limits.instHasColimitCompOfPreservesColimit`：∀ {C : Type 
u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Category
Theory.Category.{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.preservesColimitOfShape_of_createsColimitsOfShape_and_has
ColimitsOfShape`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D 
: Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `CategoryTheory.Limits.instHasLimitsOfShapeOfHasLimitsOfSize`：∀ {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTh
eory.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `AlgebraicGeometry.PresheafedSpace.instHasColimitsOfShape`：∀ {J : Type u'
} [inst : CategoryTheory.Category.{v', u'} J] {C : Type u} [inst_1 : CategoryThe
ory.Category.{v, u} C]   [CategoryTheory.Limit…
· 使用定理 `TopCat.instHasLimitsOfShapePresheaf`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {J : Type w} [inst_1 : CategoryTheory.Category.{v_1, w} J]
   [CategoryTheory.Limits…
· 使用定理 `CategoryTheory.preservesColimit_of_createsColimit_and_hasColimit`：∀ {C :
 Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Ca
tegoryTheory.Category.{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `AlgebraicGeometry.SheafedSpace.IsOpenImmersion.sigma_ι_isOpenEmbedding`：
sigma_ι_isOpenEmbedding : IsOpenEmbedding (colimit.ι F i).hom.base
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `iff_false_intro`：∀ {a : Prop}, ¬a → (a ↔ False)
· 使用定理 `AlgebraicGeometry.SheafedSpace.instPreservesColimitsOfShapeTopCatForgetO
fSmallOfHasLimitsOfShapeOpposite`：∀ {C : Type u} [inst : CategoryTheory.Category
.{v, u} C] (J : Type w) [inst_1 : CategoryTheory.Category.{w', w} J]   [Small.{v
, w} J] [Categ…
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.ConcreteCategory.congr_arg`：congr_arg {X Y : C} (f : X ⟶ 
Y) {x x' : ToType X} (h : x = x') : f x = f x'
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TopCat.sigmaIsoSigma_hom_ι`：sigmaIsoSigma_hom_ι {ι : Type v} (α : ι -> T
opCat.{max v u}) (i : ι) : Sigma.ι α i ≫ (sigmaIsoSigma α).hom = sigmaι α i
· 使用定理 `CategoryTheory.Limits.HasColimit.isoOfNatIso_ι_hom_assoc`：∀ {J : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryThe
ory.Category.{v, u} C]   {F G : CategoryTheory…
· 使用定理 `CategoryTheory.ι_preservesColimitIso_hom_assoc`：∀ {C : Type u₁} [inst : 
CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Categ
ory.{v₂, u₂} D]   (G : CategoryTheor…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.ι_preservesColimitIso_inv`：ι_preservesColimitIso_inv (j :
 J) : colimit.ι _ j ≫ (preservesColimitIso G F).inv = G.map (colimit.ι F j)
-/
theorem image_preimage_is_empty (j : Discrete ι) (h : i ≠ j) (U : Opens (F.obj i)) :
    (Opens.map (colimit.ι (F ⋙ SheafedSpace.forgetToPresheafedSpace) j).base).obj
        ((Opens.map (preservesColimitIso SheafedSpace.forgetToPresheafedSpace F).inv.base).obj
          ((sigma_ι_isOpenEmbedding F i).functor.obj U)) =
      ⊥ := by
  ext x
  apply iff_false_intro
  rintro ⟨y, hy, eq⟩
  replace eq := ConcreteCategory.congr_arg (preservesColimitIso (SheafedSpace.forget C) F ≪≫
    HasColimit.isoOfNatIso Discrete.natIsoFunctor ≪≫ TopCat.sigmaIsoSigma.{v, v} _).hom eq
  simp_rw [CategoryTheory.Iso.trans_hom, ← TopCat.comp_app, ← PresheafedSpace.comp_base] at eq
  rw [ι_preservesColimitIso_inv] at eq
  change
    ((SheafedSpace.forget C).map (colimit.ι F i) ≫ (preservesColimitIso (forget C) F).hom ≫
          (HasColimit.isoOfNatIso Discrete.natIsoFunctor).hom ≫
            (TopCat.sigmaIsoSigma ((F ⋙ forget C).obj ∘ Discrete.mk)).hom) y =
      ((SheafedSpace.forget C).map (colimit.ι F j) ≫ (preservesColimitIso (forget C) F).hom ≫
          (HasColimit.isoOfNatIso Discrete.natIsoFunctor).hom ≫
            (TopCat.sigmaIsoSigma ((F ⋙ forget C).obj ∘ Discrete.mk)).hom) x at eq
  cases i; cases j
  rw [ι_preservesColimitIso_hom_assoc, ι_preservesColimitIso_hom_assoc,
    HasColimit.isoOfNatIso_ι_hom_assoc, HasColimit.isoOfNatIso_ι_hom_assoc,
    TopCat.sigmaIsoSigma_hom_ι, TopCat.sigmaIsoSigma_hom_ι] at eq
  convert! h (congr_arg Discrete.mk (congr_arg Sigma.fst eq))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.SheafedSpace.IsOpenImmersion.sigma_** 是 Mathlib 中的一个实例，位于命名空
间 `AlgebraicGeometry.SheafedSpace.IsOpenImmersion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance sigma_ι_isOpenImmersion_aux [HasStrictTerminalObjects C] :
    SheafedSpace.IsOpenImmersion (colimit.ι F i) where
  base_open := sigma_ι_isOpenEmbedding F i
  c_iso U := by
    have h₁ := ι_preservesColimitIso_inv SheafedSpace.forgetToPresheafedSpace F i
    have h₂ : colimit.ι F i =
      { hom := (colimit.ι (F ⋙ forgetToPresheafedSpace) i ≫
        (preservesColimitIso _ F).inv) } :=
      InducedCategory.hom_ext h₁.symm
    have H :
      IsOpenEmbedding
        (colimit.ι (F ⋙ SheafedSpace.forgetToPresheafedSpace) i ≫
            (preservesColimitIso SheafedSpace.forgetToPresheafedSpace F).inv).base := by
      have := h₁.symm
      convert! sigma_ι_isOpenEmbedding F i
    suffices IsIso <| (colimit.ι (F ⋙ SheafedSpace.forgetToPresheafedSpace) i ≫
        (preservesColimitIso SheafedSpace.forgetToPresheafedSpace F).inv).c.app <|
      op (H.functor.obj U) by
      convert! this
    rw [PresheafedSpace.comp_c_app,
      ← PresheafedSpace.colimitPresheafObjIsoComponentwiseLimit_hom_π]
    -- Porting note: this instance created manually to make the `inferInstance` below work
    have : IsIso (preservesColimitIso forgetToPresheafedSpace F).inv.c := inferInstance
    suffices IsIso (limit.π (PresheafedSpace.componentwiseDiagram
      (F ⋙ SheafedSpace.forgetToPresheafedSpace) ((Opens.map
        (preservesColimitIso SheafedSpace.forgetToPresheafedSpace F).inv.base).obj
          (H.functor.obj U))) (op i)) from inferInstance
    apply limit_π_isIso_of_is_strict_terminal
    rintro ⟨j⟩ hj
    dsimp
    convert! (F.obj j).sheaf.isTerminalOfEmpty using 3
    convert! image_preimage_is_empty F i j (fun h => hj (congr_arg op h.symm)) U using 6
    exact congr_arg PresheafedSpace.Hom.base h₁

set_option backward.defeqAttrib.useBackward true in
/-
**AlgebraicGeometry.SheafedSpace.IsOpenImmersion.sigma_** 是 Mathlib 中的一个实例，位于命名空
间 `AlgebraicGeometry.SheafedSpace.IsOpenImmersion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance sigma_ι_isOpenImmersion {ι : Type w} [Small.{v} ι]
    (F : Discrete ι ⥤ SheafedSpace.{_, v, v} C) [HasColimit F] (i : Discrete ι)
    [HasStrictTerminalObjects C] :
    SheafedSpace.IsOpenImmersion (colimit.ι F i) := by
  obtain ⟨ι', ⟨e⟩⟩ := Small.equiv_small (α := ι)
  let f : Discrete ι' ≌ Discrete ι := Discrete.equivalence e.symm
  have : colimit.ι F i = (colimit.ι F i ≫ (HasColimit.isoOfEquivalence f (Iso.refl _)).inv) ≫
      (HasColimit.isoOfEquivalence f (Iso.refl _)).hom := by
    simp
  rw [this, HasColimit.ι_isoOfEquivalence_inv]
  infer_instance

end Prod

end SheafedSpace.IsOpenImmersion

namespace LocallyRingedSpace.IsOpenImmersion

/-
**AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.** 是 Mathlib 中的一个实例，位于命名空
间 `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : LocallyRingedSpace) {U : TopCat.{w}} (f : U ⟶ X.toTopCat) (hf : IsOpenEmbedding f) :
    LocallyRingedSpace.IsOpenImmersion (X.ofRestrict hf) :=
  PresheafedSpace.IsOpenImmersion.ofRestrict X.toPresheafedSpace hf

noncomputable section Pullback

variable {X Y Z : LocallyRingedSpace} (f : X ⟶ Z) (g : Y ⟶ Z)
variable [H : LocallyRingedSpace.IsOpenImmersion f]
/-
**AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.** 是 Mathlib 中的一个实例，位于命名空
间 `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) of_isIso [IsIso g] : LocallyRingedSpace.IsOpenImmersion g := by
  infer_instance
/-
**AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.comp** 是 Mathlib 中的一个实例，位
于命名空间 `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion`。
形式化陈述：comp (g : Z ⟶ Y) [LocallyRingedSpace.IsOpenImmersion g] : LocallyRingedSpa
ce.IsOpenImmersion (f ≫ g)
参数：g : Z ⟶ Y。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.instIsOpenImmersionCommRingCatOfIsOpenImmersion`：∀ {X 
Y : AlgebraicGeometry.LocallyRingedSpace} (f : X ⟶ Y) [AlgebraicGeometry.Locally
RingedSpace.IsOpenImmersion f],   AlgebraicGeometry.Pre…
-/
instance comp (g : Z ⟶ Y) [LocallyRingedSpace.IsOpenImmersion g] :
    LocallyRingedSpace.IsOpenImmersion (f ≫ g) :=
  PresheafedSpace.IsOpenImmersion.comp f.1 g.1
/-
**AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.mono** 是 Mathlib 中的一个实例，位
于命名空间 `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion`。
形式化陈述：mono : Mono f
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.mono_of_mono_map`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.reflectsMonomorphisms_of_faithful`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTh
eory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `AlgebraicGeometry.LocallyRingedSpace.instFaithfulSheafedSpaceCommRingCat
ForgetToSheafedSpace`：AlgebraicGeometry.LocallyRingedSpace.forgetToSheafedSpace.
Faithful
· 使用定理 `AlgebraicGeometry.SheafedSpace.IsOpenImmersion.instMono`：∀ {C : Type u} 
[inst : CategoryTheory.Category.{v, u} C] {X Z : AlgebraicGeometry.SheafedSpace 
C} (f : X ⟶ Z)   [H : AlgebraicGeometry.Sheaf…
-/
instance mono : Mono f :=
  LocallyRingedSpace.forgetToSheafedSpace.mono_of_mono_map (show Mono f.toShHom by infer_instance)
/-
**AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.** 是 Mathlib 中的一个实例，位于命名空
间 `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SheafedSpace.IsOpenImmersion (LocallyRingedSpace.forgetToSheafedSpace.map f) :=
  H

set_option backward.isDefEq.respectTransparency false in
/-- An explicit pullback cone over `cospan f g` if `f` is an open immersion. -/
/-
**AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.pullbackConeOfLeft** 是 Ma
thlib 中的一个定义，位于命名空间 `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion`。
形式化陈述：pullbackConeOfLeft : PullbackCone f g
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.instIsOpenImmersionCommRingCatOfIsOpenImmersion`：∀ {X 
Y : AlgebraicGeometry.LocallyRingedSpace} (f : X ⟶ Y) [AlgebraicGeometry.Locally
RingedSpace.IsOpenImmersion f],   AlgebraicGeometry.Pre…

--- 原说明 ---
An explicit pullback cone over `cospan f g` if `f` is an open immersion.
-/
def pullbackConeOfLeft : PullbackCone f g := by
  refine PullbackCone.mk ?_
      (Y.ofRestrict (TopCat.snd_isOpenEmbedding_of_left H.base_open g.base)) ?_
  · use PresheafedSpace.IsOpenImmersion.pullbackConeOfLeftFst f.1 g.1
    intro x
    have := PresheafedSpace.stalkMap.congr_hom _ _
        (PresheafedSpace.IsOpenImmersion.pullback_cone_of_left_condition f.1 g.1) x
    rw [PresheafedSpace.stalkMap.comp, PresheafedSpace.stalkMap.comp] at this
    rw [← IsIso.eq_inv_comp] at this
    rw [this]
    dsimp
    apply RingHom.isLocalHom_comp
  · exact LocallyRingedSpace.Hom.ext'
        (PresheafedSpace.IsOpenImmersion.pullback_cone_of_left_condition _ _)
/-
**AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.** 是 Mathlib 中的一个实例，位于命名空
间 `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LocallyRingedSpace.IsOpenImmersion (pullbackConeOfLeft f g).snd :=
  show PresheafedSpace.IsOpenImmersion (Y.toPresheafedSpace.ofRestrict _) by infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- The constructed `pullbackConeOfLeft` is indeed limiting. -/
/-
**AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.pullbackConeOfLeftIsLimit
** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion
`。
形式化陈述：pullbackConeOfLeftIsLimit : IsLimit (pullbackConeOfLeft f g)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.instIsOpenImmersionCommRingCatOfIsOpenImmersion`：∀ {X 
Y : AlgebraicGeometry.LocallyRingedSpace} (f : X ⟶ Y) [AlgebraicGeometry.Locally
RingedSpace.IsOpenImmersion f],   AlgebraicGeometry.Pre…

--- 原说明 ---
The constructed `pullbackConeOfLeft` is indeed limiting.
-/
def pullbackConeOfLeftIsLimit : IsLimit (pullbackConeOfLeft f g) :=
  PullbackCone.isLimitAux' _ fun s => by
    refine ⟨LocallyRingedSpace.Hom.mk (PresheafedSpace.IsOpenImmersion.pullbackConeOfLeftLift
        f.1 g.1 (PullbackCone.mk _ _ (congr_arg LocallyRingedSpace.Hom.toHom s.condition))) ?_,
      LocallyRingedSpace.Hom.ext'
        (PresheafedSpace.IsOpenImmersion.pullbackConeOfLeftLift_fst f.1 g.1 _),
      LocallyRingedSpace.Hom.ext'
          (PresheafedSpace.IsOpenImmersion.pullbackConeOfLeftLift_snd f.1 g.1 _), ?_⟩
    · intro x
      have :=
        PresheafedSpace.stalkMap.congr_hom _ _
          (PresheafedSpace.IsOpenImmersion.pullbackConeOfLeftLift_snd f.1 g.1
            (PullbackCone.mk s.fst.1 s.snd.1
              (congr_arg LocallyRingedSpace.Hom.toHom s.condition)))
          x
      change _ = _ ≫ s.snd.1.stalkMap x at this
      rw [PresheafedSpace.stalkMap.comp, ← IsIso.eq_inv_comp] at this
      rw [this]
      infer_instance
    · intro m _ h₂
      rw [← cancel_mono (pullbackConeOfLeft f g).snd]
      exact h₂.trans <| LocallyRingedSpace.Hom.ext'
        (PresheafedSpace.IsOpenImmersion.pullbackConeOfLeftLift_snd f.1 g.1 <|
          PullbackCone.mk s.fst.1 s.snd.1 <| congr_arg
            LocallyRingedSpace.Hom.toHom s.condition).symm
/-
**AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.hasPullback_of_left** 是 M
athlib 中的一个实例，位于命名空间 `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion`。
形式化陈述：hasPullback_of_left : HasPullback f g
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasPullback_of_left : HasPullback f g :=
  ⟨⟨⟨_, pullbackConeOfLeftIsLimit f g⟩⟩⟩
/-
**AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.hasPullback_of_right** 是 
Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion`。
形式化陈述：hasPullback_of_right : HasPullback g f
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasPullback_symmetry`：hasPullback_symmetry [HasPul
lback f g] : HasPullback g f
-/
instance hasPullback_of_right : HasPullback g f :=
  hasPullback_symmetry f g

set_option backward.isDefEq.respectTransparency false in
/-- Open immersions are stable under base-change. -/
/-
**AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.pullback_snd_of_left** 是 
Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion`。
形式化陈述：pullback_snd_of_left : LocallyRingedSpace.IsOpenImmersion (pullback.snd f 
g)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.limit.isoLimitCone_hom_π`：∀ {J : Type u₁} [inst : 
CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Catego
ry.{v, u} C]   {F : CategoryTheory.F…
· 使用定理 `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.of_isIso`：∀ {Y Z : 
AlgebraicGeometry.LocallyRingedSpace} (g : Y ⟶ Z) [CategoryTheory.IsIso g],   Al
gebraicGeometry.LocallyRingedSpace.IsOpenImmersion …
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.instSndPullbackCone
OfLeft`：∀ {X Y Z : AlgebraicGeometry.LocallyRingedSpace} (f : X ⟶ Z) (g : Y ⟶ Z)
   [H : AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion f],   A…

--- 原说明 ---
Open immersions are stable under base-change.
-/
instance pullback_snd_of_left :
    LocallyRingedSpace.IsOpenImmersion (pullback.snd f g) := by
  delta pullback.snd
  rw [← limit.isoLimitCone_hom_π ⟨_, pullbackConeOfLeftIsLimit f g⟩ WalkingCospan.right]
  infer_instance

/-- Open immersions are stable under base-change. -/
/-
**AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.pullback_fst_of_right** 是
 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion`。
形式化陈述：pullback_fst_of_right : LocallyRingedSpace.IsOpenImmersion (pullback.fst g
 f)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasPullback_symmetry`：hasPullback_symmetry [HasPul
lback f g] : HasPullback g f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.pullbackSymmetry_hom_comp_snd`：pullbackSymmetry_ho
m_comp_snd [HasPullback f g] : (pullbackSymmetry f g).hom ≫ pullback.snd g f = p
ullback.fst f g
· 使用定理 `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.of_isIso`：∀ {Y Z : 
AlgebraicGeometry.LocallyRingedSpace} (g : Y ⟶ Z) [CategoryTheory.IsIso g],   Al
gebraicGeometry.LocallyRingedSpace.IsOpenImmersion …
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom

--- 原说明 ---
Open immersions are stable under base-change.
-/
instance pullback_fst_of_right :
    LocallyRingedSpace.IsOpenImmersion (pullback.fst g f) := by
  rw [← pullbackSymmetry_hom_comp_snd]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.pullback_to_base_isOpenIm
mersion** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.LocallyRingedSpace.IsOpenIm
mersion`。
形式化陈述：pullback_to_base_isOpenImmersion [LocallyRingedSpace.IsOpenImmersion g] : 
LocallyRingedSpace.IsOpenImmersion (limit.π (cospan f g) WalkingCospan.one)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.limit.w`：∀ {J : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]   (F
 : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.cospan_map_inl`：cospan_map_inl {X Y Z : C} (f : X 
⟶ Z) (g : Y ⟶ Z) : (cospan f g).map WalkingCospan.Hom.inl = f
-/
instance pullback_to_base_isOpenImmersion [LocallyRingedSpace.IsOpenImmersion g] :
    LocallyRingedSpace.IsOpenImmersion (limit.π (cospan f g) WalkingCospan.one) := by
  rw [← limit.w (cospan f g) WalkingCospan.Hom.inl, cospan_map_inl]
  infer_instance
/-
**AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.forget_preservesPullbackO
fLeft** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.LocallyRingedSpace.IsOpenImme
rsion`。
形式化陈述：forget_preservesPullbackOfLeft : PreservesLimit (cospan f g) LocallyRinged
Space.forgetToSheafedSpace
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesLimit_of_preserves_limit_cone`：preservesL
imit_of_preserves_limit_cone {F : C ⥤ D} {t : Cone K} (h : IsLimit t) (hF : IsLi
mit (F.mapCone t)) : PreservesLimit K F where pres…
· 使用定理 `AlgebraicGeometry.instIsOpenImmersionCommRingCatOfIsOpenImmersion`：∀ {X 
Y : AlgebraicGeometry.LocallyRingedSpace} (f : X ⟶ Y) [AlgebraicGeometry.Locally
RingedSpace.IsOpenImmersion f],   AlgebraicGeometry.Pre…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `CategoryTheory.CreatesLimit.toReflectsLimit`：∀ {C : Type u₁} {inst : Cat
egoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Category
.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.instIsOpenImmersion
CommRingCatMapSheafedSpaceForgetToSheafedSpace`：∀ {X Z : AlgebraicGeometry.Local
lyRingedSpace} (f : X ⟶ Z) [H : AlgebraicGeometry.LocallyRingedSpace.IsOpenImmer
sion f],   AlgebraicGeometry…
-/
instance forget_preservesPullbackOfLeft :
    PreservesLimit (cospan f g) LocallyRingedSpace.forgetToSheafedSpace :=
  preservesLimit_of_preserves_limit_cone (pullbackConeOfLeftIsLimit f g) <| by
    apply (isLimitMapConePullbackConeEquiv _ _).symm.toFun
    apply isLimitOfIsLimitPullbackConeMap SheafedSpace.forgetToPresheafedSpace
    exact PresheafedSpace.IsOpenImmersion.pullbackConeOfLeftIsLimit f.1 g.1
/-
**AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.forgetToPresheafedSpace_p
reservesPullback_of_left** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.LocallyRin
gedSpace.IsOpenImmersion`。
形式化陈述：forgetToPresheafedSpace_preservesPullback_of_left : PreservesLimit (cospan
 f g) (LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forgetToPresheafed
Space)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesLimit_of_preserves_limit_cone`：preservesL
imit_of_preserves_limit_cone {F : C ⥤ D} {t : Cone K} (h : IsLimit t) (hF : IsLi
mit (F.mapCone t)) : PreservesLimit K F where pres…
· 使用定理 `AlgebraicGeometry.instIsOpenImmersionCommRingCatOfIsOpenImmersion`：∀ {X 
Y : AlgebraicGeometry.LocallyRingedSpace} (f : X ⟶ Y) [AlgebraicGeometry.Locally
RingedSpace.IsOpenImmersion f],   AlgebraicGeometry.Pre…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
instance forgetToPresheafedSpace_preservesPullback_of_left :
    PreservesLimit (cospan f g)
      (LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forgetToPresheafedSpace) :=
  preservesLimit_of_preserves_limit_cone (pullbackConeOfLeftIsLimit f g) <| by
    apply (isLimitMapConePullbackConeEquiv _ _).symm.toFun
    exact PresheafedSpace.IsOpenImmersion.pullbackConeOfLeftIsLimit f.1 g.1
/-
**AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.forgetToPresheafedSpacePr
eservesOpenImmersion** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.LocallyRingedS
pace.IsOpenImmersion`。
形式化陈述：forgetToPresheafedSpacePreservesOpenImmersion : PresheafedSpace.IsOpenImme
rsion ((LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forgetToPresheafe
dSpace).map f)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance forgetToPresheafedSpacePreservesOpenImmersion :
    PresheafedSpace.IsOpenImmersion
      ((LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forgetToPresheafedSpace).map f) :=
  H

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.forgetToTop_preservesPull
back_of_left** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.LocallyRingedSpace.IsO
penImmersion`。
形式化陈述：forgetToTop_preservesPullback_of_left : PreservesLimit (cospan f g) (Local
lyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forget _)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesLimit_of_iso_diagram`：preservesLimit_of_i
so_diagram {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂) [PreservesLimit K₁ F] : Pre
servesLimit K₂ F where preserves {c} t
· 使用定理 `AlgebraicGeometry.instIsOpenImmersionCommRingCatOfIsOpenImmersion`：∀ {X 
Y : AlgebraicGeometry.LocallyRingedSpace} (f : X ⟶ Y) [AlgebraicGeometry.Locally
RingedSpace.IsOpenImmersion f],   AlgebraicGeometry.Pre…
-/
instance forgetToTop_preservesPullback_of_left :
    PreservesLimit (cospan f g)
      (LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forget _) := by
  change PreservesLimit _ <|
    (LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forgetToPresheafedSpace) ⋙
    PresheafedSpace.forget _
  apply +allowSynthFailures Limits.comp_preservesLimit
  apply +allowSynthFailures preservesLimit_of_iso_diagram
  · exact (diagramIsoCospan _).symm
  dsimp
  infer_instance
/-
**AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.forget_reflectsPullback_o
f_left** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.LocallyRingedSpace.IsOpenImm
ersion`。
形式化陈述：forget_reflectsPullback_of_left : ReflectsLimit (cospan f g) LocallyRinged
Space.forgetToSheafedSpace
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.reflectsLimit_of_reflectsIsomorphisms`：reflectsLim
it_of_reflectsIsomorphisms (F : J ⥤ C) (G : C ⥤ D) [G.ReflectsIsomorphisms] [Has
Limit F] [PreservesLimit F G] : ReflectsLimit F G…
· 使用定理 `AlgebraicGeometry.LocallyRingedSpace.instReflectsIsomorphismsSheafedSpac
eCommRingCatForgetToSheafedSpace`：AlgebraicGeometry.LocallyRingedSpace.forgetToS
heafedSpace.ReflectsIsomorphisms
-/
instance forget_reflectsPullback_of_left :
    ReflectsLimit (cospan f g) LocallyRingedSpace.forgetToSheafedSpace :=
  reflectsLimit_of_reflectsIsomorphisms _ _
/-
**AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.forget_preservesPullback_
of_right** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.LocallyRingedSpace.IsOpenI
mmersion`。
形式化陈述：forget_preservesPullback_of_right : PreservesLimit (cospan g f) LocallyRin
gedSpace.forgetToSheafedSpace
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesPullback_symmetry`：preservesPullback_symm
etry : PreservesLimit (cospan g f) G where preserves {c} hc
-/
instance forget_preservesPullback_of_right :
    PreservesLimit (cospan g f) LocallyRingedSpace.forgetToSheafedSpace :=
  preservesPullback_symmetry _ _ _
/-
**AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.forgetToPresheafedSpace_p
reservesPullback_of_right** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.LocallyRi
ngedSpace.IsOpenImmersion`。
形式化陈述：forgetToPresheafedSpace_preservesPullback_of_right : PreservesLimit (cospa
n g f) (LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forgetToPresheafe
dSpace)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesPullback_symmetry`：preservesPullback_symm
etry : PreservesLimit (cospan g f) G where preserves {c} hc
-/
instance forgetToPresheafedSpace_preservesPullback_of_right :
    PreservesLimit (cospan g f)
      (LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forgetToPresheafedSpace) :=
  preservesPullback_symmetry _ _ _
/-
**AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.forget_reflectsPullback_o
f_right** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.LocallyRingedSpace.IsOpenIm
mersion`。
形式化陈述：forget_reflectsPullback_of_right : ReflectsLimit (cospan g f) LocallyRinge
dSpace.forgetToSheafedSpace
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.reflectsLimit_of_reflectsIsomorphisms`：reflectsLim
it_of_reflectsIsomorphisms (F : J ⥤ C) (G : C ⥤ D) [G.ReflectsIsomorphisms] [Has
Limit F] [PreservesLimit F G] : ReflectsLimit F G…
· 使用定理 `AlgebraicGeometry.LocallyRingedSpace.instReflectsIsomorphismsSheafedSpac
eCommRingCatForgetToSheafedSpace`：AlgebraicGeometry.LocallyRingedSpace.forgetToS
heafedSpace.ReflectsIsomorphisms
-/
instance forget_reflectsPullback_of_right :
    ReflectsLimit (cospan g f) LocallyRingedSpace.forgetToSheafedSpace :=
  reflectsLimit_of_reflectsIsomorphisms _ _
/-
**AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.forgetToPresheafedSpace_r
eflectsPullback_of_left** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.LocallyRing
edSpace.IsOpenImmersion`。
形式化陈述：forgetToPresheafedSpace_reflectsPullback_of_left : ReflectsLimit (cospan f
 g) (LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forgetToPresheafedSp
ace)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.reflectsLimit_of_reflectsIsomorphisms`：reflectsLim
it_of_reflectsIsomorphisms (F : J ⥤ C) (G : C ⥤ D) [G.ReflectsIsomorphisms] [Has
Limit F] [PreservesLimit F G] : ReflectsLimit F G…
· 使用定理 `AlgebraicGeometry.LocallyRingedSpace.instReflectsIsomorphismsSheafedSpac
eCommRingCatForgetToSheafedSpace`：AlgebraicGeometry.LocallyRingedSpace.forgetToS
heafedSpace.ReflectsIsomorphisms
· 使用定理 `CategoryTheory.reflectsIsomorphisms_of_full_and_faithful`：∀ {C : Type u_
1} [inst : CategoryTheory.Category.{v_1, u_1} C] {D : Type u_2}   [inst_1 : Cate
goryTheory.Category.{v_2, u_2} D] (F : Categor…
-/
instance forgetToPresheafedSpace_reflectsPullback_of_left :
    ReflectsLimit (cospan f g)
      (LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forgetToPresheafedSpace) :=
  reflectsLimit_of_reflectsIsomorphisms _ _
/-
**AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.forgetToPresheafedSpace_r
eflectsPullback_of_right** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.LocallyRin
gedSpace.IsOpenImmersion`。
形式化陈述：forgetToPresheafedSpace_reflectsPullback_of_right : ReflectsLimit (cospan 
g f) (LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forgetToPresheafedS
pace)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.reflectsLimit_of_reflectsIsomorphisms`：reflectsLim
it_of_reflectsIsomorphisms (F : J ⥤ C) (G : C ⥤ D) [G.ReflectsIsomorphisms] [Has
Limit F] [PreservesLimit F G] : ReflectsLimit F G…
· 使用定理 `AlgebraicGeometry.LocallyRingedSpace.instReflectsIsomorphismsSheafedSpac
eCommRingCatForgetToSheafedSpace`：AlgebraicGeometry.LocallyRingedSpace.forgetToS
heafedSpace.ReflectsIsomorphisms
· 使用定理 `CategoryTheory.reflectsIsomorphisms_of_full_and_faithful`：∀ {C : Type u_
1} [inst : CategoryTheory.Category.{v_1, u_1} C] {D : Type u_2}   [inst_1 : Cate
goryTheory.Category.{v_2, u_2} D] (F : Categor…
-/
instance forgetToPresheafedSpace_reflectsPullback_of_right :
    ReflectsLimit (cospan g f)
      (LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forgetToPresheafedSpace) :=
  reflectsLimit_of_reflectsIsomorphisms _ _
/-
**AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.pullback_snd_isIso_of_ran
ge_subset** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry.LocallyRingedSpace.IsOpen
Immersion`。
形式化陈述：pullback_snd_isIso_of_range_subset (H' : Set.range g.base subseteq Set.ran
ge f.base) : IsIso (pullback.snd f g)
参数：H' : Set.range g.base subseteq Set.range f.base。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.ReflectsIsomorphisms.reflects`：∀ {C : Type u_1} {
inst : CategoryTheory.Category.{v_1, u_1} C} {D : Type u_2}   {inst_1 : Category
Theory.Category.{v_2, u_2} D} (F : Categor…
· 使用定理 `AlgebraicGeometry.LocallyRingedSpace.instReflectsIsomorphismsSheafedSpac
eCommRingCatForgetToSheafedSpace`：AlgebraicGeometry.LocallyRingedSpace.forgetToS
heafedSpace.ReflectsIsomorphisms
· 使用定理 `CategoryTheory.reflectsIsomorphisms_of_full_and_faithful`：∀ {C : Type u_
1} [inst : CategoryTheory.Category.{v_1, u_1} C] {D : Type u_2}   [inst_1 : Cate
goryTheory.Category.{v_2, u_2} D] (F : Categor…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.PreservesPullback.iso_hom_snd`：∀ {C : Type u₁} [in
st : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.
Category.{v₂, u₂} D]   (G : CategoryTheor…
· 使用引理 `CategoryTheory.IsIso.comp_isIso'`：comp_isIso' (_ : IsIso f) (_ : IsIso h
) : IsIso (f ≫ h)
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.pullback_snd_isIso_of_
range_subset`：pullback_snd_isIso_of_range_subset (H : Set.range g.base subseteq 
Set.range f.base) : IsIso (pullback.snd f g)
-/
theorem pullback_snd_isIso_of_range_subset (H' : Set.range g.base ⊆ Set.range f.base) :
    IsIso (pullback.snd f g) := by
  apply +allowSynthFailures Functor.ReflectsIsomorphisms.reflects
    (F := LocallyRingedSpace.forgetToSheafedSpace)
  apply +allowSynthFailures Functor.ReflectsIsomorphisms.reflects
    (F := SheafedSpace.forgetToPresheafedSpace)
  erw [← PreservesPullback.iso_hom_snd
      (LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forgetToPresheafedSpace) f g]
  -- Porting note: was `inferInstance`
  exact IsIso.comp_isIso' inferInstance <|
    PresheafedSpace.IsOpenImmersion.pullback_snd_isIso_of_range_subset _ _ H'

/-- The universal property of open immersions:
For an open immersion `f : X ⟶ Z`, given any morphism of schemes `g : Y ⟶ Z` whose topological
image is contained in the image of `f`, we can lift this morphism to a unique `Y ⟶ X` that
commutes with these maps.
-/
/-
**AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.lift** 是 Mathlib 中的一个定义，位
于命名空间 `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion`。
形式化陈述：lift (H' : Set.range g.base subseteq Set.range f.base) : Y ⟶ X
参数：H' : Set.range g.base subseteq Set.range f.base。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.pullback_snd_isIso_
of_range_subset`：pullback_snd_isIso_of_range_subset (H' : Set.range g.base subse
teq Set.range f.base) : IsIso (pullback.snd f g)

--- 原说明 ---
The universal property of open immersions:
For an open immersion `f : X ⟶ Z`, given any morphism of schemes `g : Y ⟶ Z` who
se topological
image is contained in the image of `f`, we can lift this morphism to a unique `Y
 ⟶ X` that
commutes with these maps.
-/
def lift (H' : Set.range g.base ⊆ Set.range f.base) : Y ⟶ X :=
  have := pullback_snd_isIso_of_range_subset f g H'
  inv (pullback.snd f g) ≫ pullback.fst _ _

@[simp, reassoc]
/-
**AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.lift_fac** 是 Mathlib 中的一个
定理，位于命名空间 `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion`。
形式化陈述：lift_fac (H' : Set.range g.base subseteq Set.range f.base) : lift f g H' ≫
 f = g
参数：H' : Set.range g.base subseteq Set.range f.base。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.pullback_snd_isIso_
of_range_subset`：pullback_snd_isIso_of_range_subset (H' : Set.range g.base subse
teq Set.range f.base) : IsIso (pullback.snd f g)
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.pullback.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPullback f…
· 使用定理 `CategoryTheory.IsIso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y) [I : CategoryTheory.IsIso f] {Z : 
C}   (h : Y ⟶ Z), CategoryT…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lift_fac (H' : Set.range g.base ⊆ Set.range f.base) : lift f g H' ≫ f = g := by
  simp [lift, pullback.condition]
/-
**AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.lift_uniq** 是 Mathlib 中的一
个定理，位于命名空间 `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion`。
形式化陈述：lift_uniq (H' : Set.range g.base subseteq Set.range f.base) (l : Y ⟶ X) (h
l : l ≫ f = g) : l = lift f g H'
参数：H' : Set.range g.base subseteq Set.range f.base；l : Y ⟶ X；hl : l ≫ f = g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.lift_fac`：lift_fac 
(H' : Set.range g.base subseteq Set.range f.base) : lift f g H' ≫ f = g
-/
theorem lift_uniq (H' : Set.range g.base ⊆ Set.range f.base) (l : Y ⟶ X) (hl : l ≫ f = g) :
    l = lift f g H' := by rw [← cancel_mono f, hl, lift_fac]

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.lift_range** 是 Mathlib 中的
一个定理，位于命名空间 `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion`。
形式化陈述：lift_range (H' : Set.range g.base subseteq Set.range f.base) : Set.range (
lift f g H').base = f.base ⁻¹' Set.range g.base
参数：H' : Set.range g.base subseteq Set.range f.base。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.pullback_snd_isIso_
of_range_subset`：pullback_snd_isIso_of_range_subset (H' : Set.range g.base subse
teq Set.range f.base) : IsIso (pullback.snd f g)
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePullbacks_of_hasFiniteLimits`：∀ (C : 
Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFini
teLimits C],   CategoryTheory.Limits.HasFiniteWidePul…
· 使用定理 `CategoryTheory.Limits.hasFiniteLimits_of_hasLimits`：∀ (C : Type u) [inst
 : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasLimits C],   Cate
goryTheory.Limits.HasFiniteLimits C
· 使用定理 `CategoryTheory.Limits.PreservesPullback.iso_hom_fst`：∀ {C : Type u₁} [in
st : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.
Category.{v₂, u₂} D]   (G : CategoryTheor…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.LocallyRingedSpace.comp_base`：comp_base {X Y Z : Local
lyRingedSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).base = f.base ≫ g.base
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `TopCat.coe_comp`：∀ {X Y Z : TopCat} (f : X ⟶ Y) (g : Y ⟶ Z),   ⇑(Categor
yTheory.ConcreteCategory.hom (CategoryTheory.CategoryStruct.comp f g)) =     ⇑(C
atego…
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.range_eq_univ`：range_eq_univ : range f = univ ↔ Surjective f
· 使用定理 `TopCat.epi_iff_surjective`：epi_iff_surjective {X Y : TopCat.{u}} (f : X 
⟶ Y) : Epi f ↔ Function.Surjective f
· 使用定理 `CategoryTheory.Functor.map_inv`：map_inv (F : C ⥤ D) {X Y : C} (f : X ⟶ Y
) [IsIso f] : F.map (inv f) = inv (F.map f)
· 使用定理 `CategoryTheory.instEffectiveEpiOfIsIso`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],  
 CategoryTheory.EffectiveEpi…
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `TopCat.pullback_fst_range`：pullback_fst_range {X Y S : TopCat.{u}} (f : 
X ⟶ S) (g : Y ⟶ S) : Set.range (pullback.fst f g) = { x : X | exists y : Y, f x 
= g y }
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
-/
theorem lift_range (H' : Set.range g.base ⊆ Set.range f.base) :
    Set.range (lift f g H').base = f.base ⁻¹' Set.range g.base := by
  have := pullback_snd_isIso_of_range_subset f g H'
  dsimp only [lift]
  have : _ = (pullback.fst f g).base :=
    PreservesPullback.iso_hom_fst
      (LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forget _) f g
  rw [LocallyRingedSpace.comp_base, ← this, ← Category.assoc, TopCat.coe_comp, Set.range_comp,
      Set.range_eq_univ.mpr, Set.image_univ]
  · rw [TopCat.pullback_fst_range]
    ext
    constructor
    · rintro ⟨y, eq⟩; exact ⟨y, eq.symm⟩
    · rintro ⟨y, eq⟩; exact ⟨y, eq.symm⟩
  · rw [← TopCat.epi_iff_surjective, show (inv (pullback.snd f g)).base = _ from
        (LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forget _).map_inv _]
    infer_instance

end Pullback

/-- An open immersion is isomorphic to the induced open subscheme on its image. -/
/-
**AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.isoRestrict** 是 Mathlib 中
的一个定义，位于命名空间 `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion`。
形式化陈述：isoRestrict {X Y : LocallyRingedSpace} (f : X ⟶ Y) [H : LocallyRingedSpace
.IsOpenImmersion f] : X ≅ Y.restrict H.base_open
参数：f : X ⟶ Y。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.instIsOpenImmersionCommRingCatOfIsOpenImmersion`：∀ {X 
Y : AlgebraicGeometry.LocallyRingedSpace} (f : X ⟶ Y) [AlgebraicGeometry.Locally
RingedSpace.IsOpenImmersion f],   AlgebraicGeometry.Pre…

--- 原说明 ---
An open immersion is isomorphic to the induced open subscheme on its image.
-/
noncomputable def isoRestrict {X Y : LocallyRingedSpace} (f : X ⟶ Y)
    [H : LocallyRingedSpace.IsOpenImmersion f] :
    X ≅ Y.restrict H.base_open :=
  LocallyRingedSpace.isoOfSheafedSpaceIso <|
    SheafedSpace.fullyFaithfulForgetToPresheafedSpace.preimageIso
      (PresheafedSpace.IsOpenImmersion.isoRestrict f.1)

/-- The functor `Opens X ⥤ Opens Y` associated with an open immersion `f : X ⟶ Y`. -/
/-
**AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.opensFunctor** 是 Mathlib 
中的一个缩写定义，位于命名空间 `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion`。
形式化陈述：opensFunctor {X Y : LocallyRingedSpace} (f : X ⟶ Y) [H : LocallyRingedSpac
e.IsOpenImmersion f] : Opens X ⥤ Opens Y
参数：f : X ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `Opens X ⥤ Opens Y` associated with an open immersion `f : X ⟶ Y`.
-/
abbrev opensFunctor {X Y : LocallyRingedSpace} (f : X ⟶ Y)
    [H : LocallyRingedSpace.IsOpenImmersion f] : Opens X ⥤ Opens Y :=
  H.base_open.functor

section OfStalkIso

/-- Suppose `X Y : SheafedSpace C`, where `C` is a concrete category,
whose forgetful functor reflects isomorphisms, preserves limits and filtered colimits.
Then a morphism `X ⟶ Y` that is a topological open embedding
is an open immersion iff every stalk map is an iso.
-/
/-
**AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.of_stalk_iso** 是 Mathlib 
中的一个定理，位于命名空间 `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion`。
形式化陈述：of_stalk_iso {X Y : LocallyRingedSpace} (f : X ⟶ Y) (hf : IsOpenEmbedding 
f.base) [stalk_iso : forall x : X.1, IsIso (f.stalkMap x)] : LocallyRingedSpace.
IsOpenImmersion f
参数：f : X ⟶ Y；hf : IsOpenEmbedding f.base；f.stalkMap x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.SheafedSpace.IsOpenImmersion.of_stalk_iso`：of_stalk_is
o {X Y : SheafedSpace C} (f : X ⟶ Y) (hf : IsOpenEmbedding f.hom.base) [H : fora
ll x : X.1, IsIso (f.hom.stalkMap x)] : SheafedSp…

--- 原说明 ---
Suppose `X Y : SheafedSpace C`, where `C` is a concrete category,
whose forgetful functor reflects isomorphisms, preserves limits and filtered col
imits.
Then a morphism `X ⟶ Y` that is a topological open embedding
is an open immersion iff every stalk map is an iso.
-/
theorem of_stalk_iso {X Y : LocallyRingedSpace} (f : X ⟶ Y) (hf : IsOpenEmbedding f.base)
    [stalk_iso : ∀ x : X.1, IsIso (f.stalkMap x)] :
    LocallyRingedSpace.IsOpenImmersion f :=
  SheafedSpace.IsOpenImmersion.of_stalk_iso _ hf (H := stalk_iso)

end OfStalkIso

section

variable {X Y : LocallyRingedSpace} (f : X ⟶ Y) [H : IsOpenImmersion f]

@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.isoRestrict_hom_ofRestric
t** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersio
n`。
形式化陈述：isoRestrict_hom_ofRestrict : (isoRestrict f).hom ≫ Y.ofRestrict _ = f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.map_injective`：map_injective (F : C ⥤ D) [Faithfu
l F] : Function.Injective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
· 使用定理 `AlgebraicGeometry.LocallyRingedSpace.instFaithfulSheafedSpaceCommRingCat
ForgetToSheafedSpace`：AlgebraicGeometry.LocallyRingedSpace.forgetToSheafedSpace.
Faithful
· 使用定理 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.base_open`：∀ {C : Type
 u} {inst : CategoryTheory.Category.{v, u} C} {X Y : AlgebraicGeometry.Presheafe
dSpace C} {f : X ⟶ Y}   [self : AlgebraicGeometry…
· 使用定理 `AlgebraicGeometry.SheafedSpace.IsOpenImmersion.isoRestrict_hom_ofRestric
t`：isoRestrict_hom_ofRestrict : (isoRestrict f).hom ≫ Y.ofRestrict _ = f
-/
theorem isoRestrict_hom_ofRestrict : (isoRestrict f).hom ≫ Y.ofRestrict _ = f := by
  apply LocallyRingedSpace.forgetToSheafedSpace.map_injective
  exact SheafedSpace.IsOpenImmersion.isoRestrict_hom_ofRestrict f.toShHom

@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.isoRestrict_inv_ofRestric
t** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersio
n`。
形式化陈述：isoRestrict_inv_ofRestrict : (isoRestrict f).inv ≫ f = Y.ofRestrict _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.base_open`：∀ {C : Type
 u} {inst : CategoryTheory.Category.{v, u} C} {X Y : AlgebraicGeometry.Presheafe
dSpace C} {f : X ⟶ Y}   [self : AlgebraicGeometry…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.isoRestrict_hom_ofR
estrict`：isoRestrict_hom_ofRestrict : (isoRestrict f).hom ≫ Y.ofRestrict _ = f
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem isoRestrict_inv_ofRestrict : (isoRestrict f).inv ≫ f = Y.ofRestrict _ := by
  simp only [← isoRestrict_hom_ofRestrict f, Iso.inv_hom_id_assoc]
/-- For an open immersion `f : X ⟶ Y` and an open set `U ⊆ X`, we have the map `X(U) ⟶ Y(U)`. -/
/-
**AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.invApp** 是 Mathlib 中的一个定义
，位于命名空间 `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion`。
形式化陈述：invApp (U : Opens X) : X.presheaf.obj (op U) ⟶ Y.presheaf.obj (op (opensFu
nctor f |>.obj U))
参数：U : Opens X。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.instIsOpenImmersionCommRingCatOfIsOpenImmersion`：∀ {X 
Y : AlgebraicGeometry.LocallyRingedSpace} (f : X ⟶ Y) [AlgebraicGeometry.Locally
RingedSpace.IsOpenImmersion f],   AlgebraicGeometry.Pre…

--- 原说明 ---
For an open immersion `f : X ⟶ Y` and an open set `U ⊆ X`, we have the map `X(U)
 ⟶ Y(U)`.
-/
noncomputable def invApp (U : Opens X) :
    X.presheaf.obj (op U) ⟶ Y.presheaf.obj (op (opensFunctor f |>.obj U)) :=
  PresheafedSpace.IsOpenImmersion.invApp f.1 U

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.inv_naturality** 是 Mathli
b 中的一个定理，位于命名空间 `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion`。
形式化陈述：inv_naturality {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) : X.presheaf.map i ≫ H.invA
pp _ (unop V) = H.invApp _ (unop U) ≫ Y.presheaf.map (opensFunctor f |>.op.map i
)
参数：Opens X；i : U ⟶ V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.inv_naturality`：inv_na
turality {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) : X.presheaf.map i ≫ H.invApp _ (unop V
) = invApp f (unop U) ≫ Y.presheaf.map (opensFunctor f…
· 使用定理 `AlgebraicGeometry.instIsOpenImmersionCommRingCatOfIsOpenImmersion`：∀ {X 
Y : AlgebraicGeometry.LocallyRingedSpace} (f : X ⟶ Y) [AlgebraicGeometry.Locally
RingedSpace.IsOpenImmersion f],   AlgebraicGeometry.Pre…

--- 原说明 ---
`respectTransparency.types true` changes the auto-generated lemmas' signature
-/
theorem inv_naturality {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) :
    X.presheaf.map i ≫ H.invApp _ (unop V) =
      H.invApp _ (unop U) ≫ Y.presheaf.map (opensFunctor f |>.op.map i) :=
  PresheafedSpace.IsOpenImmersion.inv_naturality f.1 i

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.** 是 Mathlib 中的一个实例，位于命名空
间 `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (U : Opens X) : IsIso (H.invApp _ U) := by delta invApp; infer_instance

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.inv_invApp** 是 Mathlib 中的
一个定理，位于命名空间 `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion`。
形式化陈述：inv_invApp (U : Opens X) : inv (H.invApp _ U) = f.c.app (op (opensFunctor 
f |>.obj U)) ≫ X.presheaf.map (eqToHom (by have
参数：U : Opens X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.inv_invApp`：inv_invApp
 (U : Opens X) : inv (H.invApp _ U) = f.c.app (op (opensFunctor f |>.obj U)) ≫ X
.presheaf.map (eqToHom (by simp [Opens.map_def, Se…
· 使用定理 `AlgebraicGeometry.instIsOpenImmersionCommRingCatOfIsOpenImmersion`：∀ {X 
Y : AlgebraicGeometry.LocallyRingedSpace} (f : X ⟶ Y) [AlgebraicGeometry.Locally
RingedSpace.IsOpenImmersion f],   AlgebraicGeometry.Pre…
-/
theorem inv_invApp (U : Opens X) :
    inv (H.invApp _ U) =
      f.c.app (op (opensFunctor f |>.obj U)) ≫ X.presheaf.map
        (eqToHom (by
          have := Set.preimage_image_eq U.1 H.base_open.injective
          dsimp at this
          simp [Opens.map_def, this])) :=
  PresheafedSpace.IsOpenImmersion.inv_invApp f.1 U

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.invApp_app** 是 Mathlib 中的
一个定理，位于命名空间 `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion`。
形式化陈述：invApp_app (U : Opens X) : H.invApp _ U ≫ f.c.app (op (opensFunctor f |>.o
bj U)) = X.presheaf.map (eqToHom (by have
参数：U : Opens X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.invApp_app`：invApp_app
 (U : Opens X) : invApp f U ≫ f.c.app (op (opensFunctor f |>.obj U)) = X.preshea
f.map (eqToHom (by simp [Opens.map_def, Set.preima…
· 使用定理 `AlgebraicGeometry.instIsOpenImmersionCommRingCatOfIsOpenImmersion`：∀ {X 
Y : AlgebraicGeometry.LocallyRingedSpace} (f : X ⟶ Y) [AlgebraicGeometry.Locally
RingedSpace.IsOpenImmersion f],   AlgebraicGeometry.Pre…
-/
theorem invApp_app (U : Opens X) :
    H.invApp _ U ≫ f.c.app (op (opensFunctor f |>.obj U)) = X.presheaf.map
      (eqToHom (by
        have := Set.preimage_image_eq U.1 H.base_open.injective
        dsimp at this
        simp [Opens.map_def, this])) :=
  PresheafedSpace.IsOpenImmersion.invApp_app f.1 U

attribute [elementwise nosimp] invApp_app

@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.app_invApp** 是 Mathlib 中的
一个定理，位于命名空间 `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion`。
形式化陈述：app_invApp (U : Opens Y) : f.c.app (op U) ≫ H.invApp _ ((Opens.map f.base)
.obj U) = Y.presheaf.map ((homOfLE (Set.image_preimage_subset f.base U.1)).op : 
op U ⟶ op (opensFunctor f |>.obj ((Opens.map f.base).obj U)))
参数：U : Opens Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.app_invApp`：app_invApp
 (U : Opens Y) : f.c.app (op U) ≫ H.invApp _ ((Opens.map f.base).obj U) = Y.pres
heaf.map ((homOfLE (Set.image_preimage_subset f.ba…
· 使用定理 `AlgebraicGeometry.instIsOpenImmersionCommRingCatOfIsOpenImmersion`：∀ {X 
Y : AlgebraicGeometry.LocallyRingedSpace} (f : X ⟶ Y) [AlgebraicGeometry.Locally
RingedSpace.IsOpenImmersion f],   AlgebraicGeometry.Pre…
-/
theorem app_invApp (U : Opens Y) :
    f.c.app (op U) ≫ H.invApp _ ((Opens.map f.base).obj U) =
      Y.presheaf.map
        ((homOfLE (Set.image_preimage_subset f.base U.1)).op :
          op U ⟶ op (opensFunctor f |>.obj ((Opens.map f.base).obj U))) :=
  PresheafedSpace.IsOpenImmersion.app_invApp f.1 U

/-- A variant of `app_inv_app` that gives an `eqToHom` instead of `homOfLe`. -/
@[reassoc]
/-
**AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.app_inv_app'** 是 Mathlib 
中的一个定理，位于命名空间 `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion`。
形式化陈述：app_inv_app' (U : Opens Y) (hU : (U : Set Y) subseteq Set.range f.base) : 
f.c.app (op U) ≫ H.invApp _ ((Opens.map f.base).obj U) = Y.presheaf.map (eqToHom
 <| le_antisymm (Set.image_preimage_subset f.base U.1) (Set.image_preimage_eq_in
ter_range (f
参数：U : Opens Y；hU : (U : Set Y) subseteq Set.range f.base。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.app_invApp`：app_invApp
 (U : Opens Y) : f.c.app (op U) ≫ H.invApp _ ((Opens.map f.base).obj U) = Y.pres
heaf.map ((homOfLE (Set.image_preimage_subset f.ba…
· 使用定理 `AlgebraicGeometry.instIsOpenImmersionCommRingCatOfIsOpenImmersion`：∀ {X 
Y : AlgebraicGeometry.LocallyRingedSpace} (f : X ⟶ Y) [AlgebraicGeometry.Locally
RingedSpace.IsOpenImmersion f],   AlgebraicGeometry.Pre…

--- 原说明 ---
A variant of `app_inv_app` that gives an `eqToHom` instead of `homOfLe`.
-/
theorem app_inv_app' (U : Opens Y) (hU : (U : Set Y) ⊆ Set.range f.base) :
    f.c.app (op U) ≫ H.invApp _ ((Opens.map f.base).obj U) =
      Y.presheaf.map
        (eqToHom <|
            le_antisymm (Set.image_preimage_subset f.base U.1) <|
              (Set.image_preimage_eq_inter_range (f := f.base) (t := U.1)).symm ▸
                Set.subset_inter_iff.mpr ⟨fun _ h => h, hU⟩).op :=
  PresheafedSpace.IsOpenImmersion.app_invApp f.1 U
/-
**AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.ofRestrict** 是 Mathlib 中的
一个实例，位于命名空间 `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion`。
形式化陈述：ofRestrict {X : TopCat.{w}} (Y : LocallyRingedSpace) {f : X ⟶ Y.carrier} (
hf : IsOpenEmbedding f) : IsOpenImmersion (Y.ofRestrict hf)
参数：Y : LocallyRingedSpace；hf : IsOpenEmbedding f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance ofRestrict {X : TopCat.{w}} (Y : LocallyRingedSpace) {f : X ⟶ Y.carrier}
    (hf : IsOpenEmbedding f) : IsOpenImmersion (Y.ofRestrict hf) :=
  PresheafedSpace.IsOpenImmersion.ofRestrict _ hf

@[elementwise, simp]
/-
**AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.ofRestrict_invApp** 是 Mat
hlib 中的一个定理，位于命名空间 `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion`。
形式化陈述：ofRestrict_invApp (X : LocallyRingedSpace) {Y : TopCat.{w}} {f : Y ⟶ TopCa
t.of X.carrier} (h : IsOpenEmbedding f) (U : Opens (X.restrict h).carrier) : (Lo
callyRingedSpace.IsOpenImmersion.ofRestrict X h).invApp _ U = 𝟙 _
参数：X : LocallyRingedSpace；h : IsOpenEmbedding f；U : Opens (X.restrict h).carrier
。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.ofRestrict_invApp`：ofR
estrict_invApp {C : Type*} [Category* C] (X : PresheafedSpace C) {Y : TopCat.{w}
} {f : Y ⟶ TopCat.of X.carrier} (h : IsOpenEmbedding f) (…
-/
theorem ofRestrict_invApp (X : LocallyRingedSpace) {Y : TopCat.{w}}
    {f : Y ⟶ TopCat.of X.carrier} (h : IsOpenEmbedding f) (U : Opens (X.restrict h).carrier) :
    (LocallyRingedSpace.IsOpenImmersion.ofRestrict X h).invApp _ U = 𝟙 _ :=
  PresheafedSpace.IsOpenImmersion.ofRestrict_invApp _ h U
/-
**AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.stalk_iso** 是 Mathlib 中的一
个实例，位于命名空间 `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion`。
形式化陈述：stalk_iso (x : X) : IsIso (f.stalkMap x)
参数：x : X。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.instIsOpenImmersionCommRingCatOfIsOpenImmersion`：∀ {X 
Y : AlgebraicGeometry.LocallyRingedSpace} (f : X ⟶ Y) [AlgebraicGeometry.Locally
RingedSpace.IsOpenImmersion f],   AlgebraicGeometry.Pre…
-/
instance stalk_iso (x : X) : IsIso (f.stalkMap x) :=
  PresheafedSpace.IsOpenImmersion.stalk_iso f.1 x
/-
**AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.to_iso** 是 Mathlib 中的一个定理
，位于命名空间 `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion`。
形式化陈述：to_iso [Epi f.base] : IsIso f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.isIso_iff_of_reflects_iso`：isIso_iff_of_reflects_iso {A B
 : C} (f : A ⟶ B) (F : C ⥤ D) [F.ReflectsIsomorphisms] : IsIso (F.map f) ↔ IsIso
 f
· 使用定理 `AlgebraicGeometry.LocallyRingedSpace.instReflectsIsomorphismsSheafedSpac
eCommRingCatForgetToSheafedSpace`：AlgebraicGeometry.LocallyRingedSpace.forgetToS
heafedSpace.ReflectsIsomorphisms
· 使用定理 `AlgebraicGeometry.SheafedSpace.IsOpenImmersion.to_iso`：to_iso [h' : Epi 
f.hom.base] : IsIso f
· 使用定理 `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.instIsOpenImmersion
CommRingCatMapSheafedSpaceForgetToSheafedSpace`：∀ {X Z : AlgebraicGeometry.Local
lyRingedSpace} (f : X ⟶ Z) [H : AlgebraicGeometry.LocallyRingedSpace.IsOpenImmer
sion f],   AlgebraicGeometry…
-/
theorem to_iso [Epi f.base] : IsIso f := by
  rw [← isIso_iff_of_reflects_iso _ LocallyRingedSpace.forgetToSheafedSpace]
  have : Epi (forgetToSheafedSpace.map f).hom.base := by assumption
  apply SheafedSpace.IsOpenImmersion.to_iso

end

end LocallyRingedSpace.IsOpenImmersion

end AlgebraicGeometry

