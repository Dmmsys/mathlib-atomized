/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Presentable.IsCardinalFiltered
public import Mathlib.CategoryTheory.Subobject.Lattice

/-!
# Subobjects in Grothendieck abelian categories

We study the complete lattice of subobjects of `X : C`
when `C` is a Grothendieck abelian category. In particular,
for a functor `F : J ⥤ MonoOver X` from a filtered category,
we relate the colimit of `F` (computed in `C`) and the
supremum of the subobjects corresponding to the objects
in the image of `F`.

-/

@[expose] public section

universe w v' v u' u

namespace CategoryTheory

open Limits

namespace IsGrothendieckAbelian

attribute [local instance] IsFiltered.isConnected

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  {X : C} {J : Type w} [SmallCategory J] (F : J ⥤ MonoOver X)

section

variable [IsFiltered J] {c : Cocone (F ⋙ MonoOver.forget _ ⋙ Over.forget _)}
  (hc : IsColimit c) (f : c.pt ⟶ X) (hf : ∀ (j : J), c.ι.app j ≫ f = (F.obj j).obj.hom)

include hc hf

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- If `C` is a Grothendieck abelian category, `X : C`, if `F : J ⥤ MonoOver X` is a
functor from a filtered category `J`, `c` is a colimit cocone for the corresponding
functor `J ⥤ C`, and `f : c.pt ⟶ X` is induced by the inclusions,
then `f` is a monomorphism. -/
/-
**CategoryTheory.IsGrothendieckAbelian.mono_of_isColimit_monoOver** 是 Mathlib 中的
一个引理，位于命名空间 `CategoryTheory.IsGrothendieckAbelian`。
形式化陈述：mono_of_isColimit_monoOver : Mono f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Over.w`：w : φ.left ≫ g.hom = f.hom
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.NatTrans.mono_of_mono_app`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Limits.colim.map_mono'`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {J : Type u'} [inst_1 : CategoryTheory.Category.{v', u'}
 J]   [inst_2 : CategoryThe…
· 使用定理 `CategoryTheory.Limits.hasColimitsOfShape_of_has_filtered_colimits`：∀ {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C]   [CategoryTheory.Limits.Has
FilteredColimitsOfSize.{w', w, v, u} C] (I : Type w)   …
· 使用定理 `CategoryTheory.IsGrothendieckAbelian.hasFilteredColimitsOfSize`：∀ {C : T
ype u} {inst : CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Abelia
n C}   [self : CategoryTheory.IsGrothendieckAbelian.…
· 使用定理 `CategoryTheory.Functor.instPreservesMonomorphisms`：∀ {C : Type u_1} {D :
 Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryThe
ory.Category.{v_2, u_2} D] (F : Categor…
· 使用定理 `CategoryTheory.Limits.HasZeroObject.instFunctor`：∀ {C : Type u} [inst : 
CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasZeroObject C] {B : T
ype u_1}   [inst_2 : CategoryTheory.C…
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_preserves_terminal_obje
ct`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [i
nst_1 : CategoryTheory.Category.{v₂, u₂} D]   [CategoryTheory.Li…
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Limits.PreservesFiniteLimits.preservesFiniteLimits`：∀ {C 
: Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : C
ategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.HasExactColimitsOfShape.preservesFiniteLimits`：∀ {J : Typ
e u'} {inst : CategoryTheory.Category.{v', u'} J} {C : Type u} {inst_1 : Categor
yTheory.Category.{v, u} C}   {inst_2 : CategoryThe…
· 使用定理 `CategoryTheory.AB5OfSize.ofShape`：∀ {C : Type u} {inst : CategoryTheory.
Category.{v, u} C}   {inst_1 : CategoryTheory.Limits.HasFilteredColimitsOfSize.{
w, w', v, u} C}   [sel…
· 使用定理 `CategoryTheory.IsGrothendieckAbelian.ab5OfSize`：∀ {C : Type u} {inst : C
ategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Abelian C}   [self : C
ategoryTheory.IsGrothendieckAbelian.…
· 使用定理 `CategoryTheory.Functor.preservesHomologyOfExact`：∀ {C : Type u_1} {D : T
ype u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheor
y.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Limits.PreservesColimits.preservesFiniteColimits`：∀ {C : 
Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.IsFiltered.isConnected`：∀ (C : Type u) [inst : CategoryTh
eory.Category.{v, u} C] [CategoryTheory.IsFiltered C], CategoryTheory.IsConnecte
d C
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a

--- 原说明 ---
If `C` is a Grothendieck abelian category, `X : C`, if `F : J ⥤ MonoOver X` is a
functor from a filtered category `J`, `c` is a colimit cocone for the correspond
ing
functor `J ⥤ C`, and `f : c.pt ⟶ X` is induced by the inclusions,
then `f` is a monomorphism.
-/
lemma mono_of_isColimit_monoOver : Mono f := by
  let α : F ⋙ MonoOver.forget _ ⋙ Over.forget _ ⟶ (Functor.const _).obj X :=
    { app j := (F.obj j).obj.hom }
  have := NatTrans.mono_of_mono_app α
  exact colim.map_mono' α hc (isColimitConstCocone J X) f (by simpa using hf)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- If `C` is a Grothendieck abelian category, `X : C`, if `F : J ⥤ MonoOver X` is a
functor from a filtered category `J`, the colimit of `F` (computed in `C`) gives
a subobject of `F` which is a supremum of the subobjects corresponding to
the objects in the image of the functor `F`. -/
/-
**CategoryTheory.IsGrothendieckAbelian.subobjectMk_of_isColimit_eq_iSup** 是 Math
lib 中的一个引理，位于命名空间 `CategoryTheory.IsGrothendieckAbelian`。
形式化陈述：subobjectMk_of_isColimit_eq_iSup : haveI
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.IsGrothendieckAbelian.mono_of_isColimit_monoOver`：mono_of
_isColimit_monoOver : Mono f
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `CategoryTheory.IsGrothendieckAbelian.locallySmall`：∀ {C : Type u} {inst 
: CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Abelian C}   [self 
: CategoryTheory.IsGrothendieckAbelian.…
· 使用定理 `CategoryTheory.IsGrothendieckAbelian.wellPowered`：∀ (C : Type u) [inst :
 CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2
 : CategoryTheory.IsGrothendieckAbelia…
· 使用定理 `CategoryTheory.Limits.instHasLimitsOfShapeOfHasLimitsOfSize`：∀ {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTh
eory.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.IsGrothendieckAbelian.hasLimits`：∀ (C : Type u) [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [Category
Theory.IsGrothendieckAbelian.{w, v, …
· 使用定理 `CategoryTheory.Limits.hasImages_of_hasStrongEpiMonoFactorisations`：∀ {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasSt
rongEpiMonoFactorisations C],   CategoryTheory.Limits.H…
· 使用定理 `CategoryTheory.Abelian.instHasStrongEpiMonoFactorisations`：∀ {C : Type u
} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Abelian C],   Catego
ryTheory.Limits.HasStrongEpiMonoFactorisations …
· 使用定理 `CategoryTheory.Limits.instHasColimitsOfShapeOfHasColimitsOfSize`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : Catego
ryTheory.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.IsGrothendieckAbelian.hasColimits`：∀ (C : Type u) [inst :
 CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [Catego
ryTheory.IsGrothendieckAbelian.{w, v, …
· 使用定理 `CategoryTheory.Limits.HasZeroObject.initialMonoClass`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasZeroObject C], 
  CategoryTheory.Limits.InitialMonoClass C
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `le_iSup_iff`：le_iSup_iff {s : ι -> α} : a <= iSup s ↔ forall b, (forall 
i, s i <= b) -> a <= b
· 使用定理 `CategoryTheory.Subobject.ind`：∀ {C : Type u₁} [inst : CategoryTheory.Cat
egory.{v₁, u₁} C] {X : C} (p : CategoryTheory.Subobject X → Prop),   (∀ ⦃A : C⦄ 
(f : A ⟶ X) [inst_…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Subobject.ofMkLEMk_comp`：ofMkLEMk_comp {B A₁ A₂ : C} {f :
 A₁ ⟶ B} {g : A₂ ⟶ B} [Mono f] [Mono g] (h : mk f <= mk g) : ofMkLEMk f g h ≫ g 
= f
· 使用定理 `CategoryTheory.MonoOver.w`：w {f g : MonoOver X} (k : f ⟶ g) : k.hom.left
 ≫ g.arrow = f.arrow
· 使用定理 `CategoryTheory.Subobject.mk_le_mk_of_comm`：mk_le_mk_of_comm {B A₁ A₂ : C
} {f₁ : A₁ ⟶ B} {f₂ : A₂ ⟶ B} [Mono f₁] [Mono f₂] (g : A₁ ⟶ A₂) (w : g ≫ f₂ = f₁
) : mk f₁ <= mk f₂
· 使用定理 `CategoryTheory.Limits.IsColimit.hom_ext`：∀ {J : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃
, u₃} C]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.IsColimit.fac_assoc`：∀ {J : Type u₁} [inst : Categ
oryTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{
v₃, u₃} C]   {F : CategoryTheor…
· 使用定理 `iSup_le_iff`：iSup_le_iff : iSup f <= a ↔ forall i, f i <= a

--- 原说明 ---
If `C` is a Grothendieck abelian category, `X : C`, if `F : J ⥤ MonoOver X` is a
functor from a filtered category `J`, the colimit of `F` (computed in `C`) gives
a subobject of `F` which is a supremum of the subobjects corresponding to
the objects in the image of the functor `F`.
-/
lemma subobjectMk_of_isColimit_eq_iSup :
    haveI := mono_of_isColimit_monoOver F hc f hf
    Subobject.mk f = ⨆ j, Subobject.mk (F.obj j).obj.hom := by
  have := mono_of_isColimit_monoOver F hc f hf
  apply le_antisymm
  · rw [le_iSup_iff]
    intro s H
    induction s using Subobject.ind with | _ g
    let c' : Cocone (F ⋙ MonoOver.forget _ ⋙ Over.forget _) := Cocone.mk _
      { app j := Subobject.ofMkLEMk _ _ (H j)
        naturality j j' f := by
          dsimp
          simpa only [← cancel_mono g, Category.assoc, Subobject.ofMkLEMk_comp,
            Category.comp_id] using MonoOver.w (F.map f) }
    exact Subobject.mk_le_mk_of_comm (hc.desc c')
      (hc.hom_ext (fun j ↦ by rw [hc.fac_assoc c' j, hf, Subobject.ofMkLEMk_comp]))
  · rw [iSup_le_iff]
    intro j
    exact Subobject.mk_le_mk_of_comm (c.ι.app j) (hf j)

end

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Let `X : C` be an object in a Grothendieck abelian category,
`F : J ⥤ MonoOver X` a functor from a filtered category, `c` a cocone for
the composition `F ⋙ MonoOver.forget _ : J ⥤ Over X`. We assume
that `c.pt.hom : c.pt.left ⟶ X` is a monomorphism and that the corresponding
subobject of `X` is the supremum of the subobjects given by `(F.obj j).obj.hom`,
then `c` becomes a colimit cocone after the application of
the forget functor `Over X ⥤ C`. (See also `subobjectMk_of_isColimit_eq_iSup`.) -/
/-
**CategoryTheory.IsGrothendieckAbelian.isColimitMapCoconeOfSubobjectMkEqISup** 是
 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.IsGrothendieckAbelian`。
形式化陈述：isColimitMapCoconeOfSubobjectMkEqISup [IsFiltered J] (c : Cocone (F ⋙ Mono
Over.forget _)) [Mono c.pt.hom] (h : Subobject.mk c.pt.hom = ⨆ j, Subobject.mk (
F.obj j).obj.hom) : IsColimit ((Over.forget _).mapCocone c)
参数：c : Cocone (F ⋙ MonoOver.forget _)；h : Subobject.mk c.pt.hom = ⨆ j, Subobject
.mk (F.obj j).obj.hom。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsGrothendieckAbelian.locallySmall`：∀ {C : Type u} {inst 
: CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Abelian C}   [self 
: CategoryTheory.IsGrothendieckAbelian.…
· 使用定理 `CategoryTheory.IsGrothendieckAbelian.wellPowered`：∀ (C : Type u) [inst :
 CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2
 : CategoryTheory.IsGrothendieckAbelia…

--- 原说明 ---
Let `X : C` be an object in a Grothendieck abelian category,
`F : J ⥤ MonoOver X` a functor from a filtered category, `c` a cocone for
the composition `F ⋙ MonoOver.forget _ : J ⥤ Over X`. We assume
that `c.pt.hom : c.pt.left ⟶ X` is a monomorphism and that the corresponding
subobject of `X` is the supremum of the subobjects given by `(F.obj j).obj.hom`,
then `c` becomes a colimit cocone after the application of
the forget functor `Over X ⥤ C`. (See also `subobjectMk_of_isColimit_eq_iSup`.)
-/
noncomputable def isColimitMapCoconeOfSubobjectMkEqISup
    [IsFiltered J] (c : Cocone (F ⋙ MonoOver.forget _)) [Mono c.pt.hom]
    (h : Subobject.mk c.pt.hom = ⨆ j, Subobject.mk (F.obj j).obj.hom) :
    IsColimit ((Over.forget _).mapCocone c) := by
  let f : colimit (F ⋙ MonoOver.forget X ⋙ Over.forget X) ⟶ X :=
    colimit.desc _ (Cocone.mk X
      { app j := (F.obj j).obj.hom
        naturality {j j'} g := by simp [MonoOver.forget] })
  haveI := mono_of_isColimit_monoOver F (colimit.isColimit _) f (by simp [f])
  have := subobjectMk_of_isColimit_eq_iSup F (colimit.isColimit _) f (by simp [f])
  rw [← h] at this
  refine IsColimit.ofIsoColimit (colimit.isColimit _)
    (Cocone.ext (Subobject.isoOfMkEqMk _ _ this) (fun j ↦ ?_))
  rw [← cancel_mono (c.pt.hom)]
  dsimp
  rw [Category.assoc, Subobject.ofMkLEMk_comp, Over.w]
  apply colimit.ι_desc

/-- If `C` is a Grothendieck abelian category, `X : C`, if `F : J ⥤ MonoOver X` is a
functor from a `κ`-filtered category `J` with `κ` a regular cardinal such
that `HasCardinalLT (Subobject X) κ`, and if the colimit of `F` (computed in `C`)
maps epimorphically onto `X`, then there exists `j : J` such that `(F.obj j).obj.hom`
is an isomorphism. -/
/-
**CategoryTheory.IsGrothendieckAbelian.exists_isIso_of_functor_from_monoOver** 是
 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.IsGrothendieckAbelian`。
形式化陈述：exists_isIso_of_functor_from_monoOver {κ : Cardinal.{w}} [hκ : Fact κ.IsRe
gular] [IsCardinalFiltered J κ] (hXκ : HasCardinalLT (Subobject X) κ) (c : Cocon
e (F ⋙ MonoOver.forget _ ⋙ Over.forget _)) (hc : IsColimit c) (f : c.pt ⟶ X) (hf
 : forall (j : J), c.ι.app j ≫ f = (F.obj j).obj.hom) (h : Epi f) : exists (j : 
J), IsIso (F.obj j).obj.hom
参数：hXκ : HasCardinalLT (Subobject X) κ；c : Cocone (F ⋙ MonoOver.forget _ ⋙ Over.
forget _)；hc : IsColimit c；f : c.pt ⟶ X；hf : forall (j : J), c.ι.app j ≫ f = (F.
obj j).obj.hom；h : Epi f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.isFiltered_of_isCardinalFiltered`：isFiltered_of_isCardina
lFiltered (J : Type u) [Category.{v} J] (κ : Cardinal.{w}) [hκ : Fact κ.IsRegula
r] [IsCardinalFiltered J κ] : IsFilte…
· 使用引理 `CategoryTheory.IsGrothendieckAbelian.mono_of_isColimit_monoOver`：mono_of
_isColimit_monoOver : Mono f
· 使用定理 `Function.Surjective.hasRightInverse`：∀ {α : Sort u} {β : Sort v} {f : α 
→ β}, Function.Surjective f → Function.HasRightInverse f
· 使用引理 `HasCardinalLT.of_injective`：of_injective (f : Y -> X) (hf : Function.Inj
ective f) : HasCardinalLT Y κ
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Subobject.isIso_iff_mk_eq_top`：isIso_iff_mk_eq_top {X Y :
 C} (f : X ⟶ Y) [Mono f] : IsIso f ↔ mk f = ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `top_le_iff`：top_le_iff : ⊤ <= a ↔ a = ⊤
· 使用定理 `CategoryTheory.IsGrothendieckAbelian.locallySmall`：∀ {C : Type u} {inst 
: CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Abelian C}   [self 
: CategoryTheory.IsGrothendieckAbelian.…
· 使用定理 `CategoryTheory.IsGrothendieckAbelian.wellPowered`：∀ (C : Type u) [inst :
 CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2
 : CategoryTheory.IsGrothendieckAbelia…
· 使用定理 `CategoryTheory.Limits.instHasLimitsOfShapeOfHasLimitsOfSize`：∀ {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTh
eory.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.IsGrothendieckAbelian.hasLimits`：∀ (C : Type u) [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [Category
Theory.IsGrothendieckAbelian.{w, v, …
· 使用定理 `CategoryTheory.Limits.hasImages_of_hasStrongEpiMonoFactorisations`：∀ {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasSt
rongEpiMonoFactorisations C],   CategoryTheory.Limits.H…
· 使用定理 `CategoryTheory.Abelian.instHasStrongEpiMonoFactorisations`：∀ {C : Type u
} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Abelian C],   Catego
ryTheory.Limits.HasStrongEpiMonoFactorisations …
· 使用定理 `CategoryTheory.Limits.instHasColimitsOfShapeOfHasColimitsOfSize`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : Catego
ryTheory.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.IsGrothendieckAbelian.hasColimits`：∀ (C : Type u) [inst :
 CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [Catego
ryTheory.IsGrothendieckAbelian.{w, v, …
· 使用定理 `CategoryTheory.Limits.HasZeroObject.initialMonoClass`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasZeroObject C], 
  CategoryTheory.Limits.InitialMonoClass C
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用引理 `CategoryTheory.IsGrothendieckAbelian.subobjectMk_of_isColimit_eq_iSup`：s
ubobjectMk_of_isColimit_eq_iSup : haveI
· 使用引理 `CategoryTheory.Subobject.epi_iff_mk_eq_top`：epi_iff_mk_eq_top [Balanced 
C] (f : X ⟶ Y) [Mono f] : Epi f ↔ Subobject.mk f = ⊤
· 使用定理 `CategoryTheory.balanced_of_strongMonoCategory`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] [CategoryTheory.StrongMonoCategory C],   Categor
yTheory.Balanced C
· 使用定理 `CategoryTheory.strongMonoCategory_of_regularMonoCategory`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] [CategoryTheory.IsRegularMonoCateg
ory C],   CategoryTheory.StrongMonoCategory C
· 使用定理 `CategoryTheory.regularMonoCategoryOfNormalMonoCategory`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Limits.HasZ
eroMorphisms C]   [CategoryTheory.IsNormalMo…
· 使用定理 `CategoryTheory.Abelian.toIsNormalMonoCategory`：∀ {C : Type u} {inst : Ca
tegoryTheory.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryThe
ory.IsNormalMonoCategory C
· 使用定理 `iSup_le_iff`：iSup_le_iff : iSup f <= a ↔ forall i, f i <= a
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用引理 `CategoryTheory.MonoOver.subobjectMk_le_mk_of_hom`：subobjectMk_le_mk_of_h
om : Subobject.mk P.obj.hom <= Subobject.mk Q.obj.hom

--- 原说明 ---
If `C` is a Grothendieck abelian category, `X : C`, if `F : J ⥤ MonoOver X` is a
functor from a `κ`-filtered category `J` with `κ` a regular cardinal such
that `HasCardinalLT (Subobject X) κ`, and if the colimit of `F` (computed in `C`
)
maps epimorphically onto `X`, then there exists `j : J` such that `(F.obj j).obj
.hom`
is an isomorphism.
-/
lemma exists_isIso_of_functor_from_monoOver
    {κ : Cardinal.{w}} [hκ : Fact κ.IsRegular] [IsCardinalFiltered J κ]
    (hXκ : HasCardinalLT (Subobject X) κ)
    (c : Cocone (F ⋙ MonoOver.forget _ ⋙ Over.forget _)) (hc : IsColimit c)
    (f : c.pt ⟶ X) (hf : ∀ (j : J), c.ι.app j ≫ f = (F.obj j).obj.hom) (h : Epi f) :
    ∃ (j : J), IsIso (F.obj j).obj.hom := by
  have := isFiltered_of_isCardinalFiltered J κ
  have := mono_of_isColimit_monoOver F hc f hf
  rw [Subobject.epi_iff_mk_eq_top f,
    subobjectMk_of_isColimit_eq_iSup F hc f hf] at h
  let s (j : J) : Subobject X := Subobject.mk (F.obj j).obj.hom
  have h' : Function.Surjective (fun (j : J) ↦ (⟨s j, _, rfl⟩ : Set.range s)) := by
    rintro ⟨_, j, rfl⟩
    exact ⟨j, rfl⟩
  obtain ⟨σ, hσ⟩ := h'.hasRightInverse
  have hs : HasCardinalLT (Set.range s) κ :=
    hXκ.of_injective (f := Subtype.val) Subtype.val_injective
  refine ⟨IsCardinalFiltered.max σ hs, ?_⟩
  rw [Subobject.isIso_iff_mk_eq_top, ← top_le_iff, ← h, iSup_le_iff]
  intro j
  let t : Set.range s := ⟨_, j, rfl⟩
  trans Subobject.mk (F.obj (σ t)).obj.hom
  · exact (hσ t).symm.le
  · exact MonoOver.subobjectMk_le_mk_of_hom
      (F.map (IsCardinalFiltered.toMax σ hs t))

end IsGrothendieckAbelian

end CategoryTheory

