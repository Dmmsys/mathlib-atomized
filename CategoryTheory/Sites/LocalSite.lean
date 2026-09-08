/-
Copyright (c) 2025 Ben Eltschig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Eltschig
-/
module

public import Mathlib.CategoryTheory.Adjunction.Triple
public import Mathlib.CategoryTheory.Limits.Elements
public import Mathlib.CategoryTheory.Sites.GlobalSections
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper

/-!
# Local sites

A site is called local if it has a terminal object whose only covering sieve is trivial -
this makes it possible to define coconstant sheaves on it, giving its sheaf topos the structure
of a local topos. This is one of the conditions of cohesive sites.

Sheaves of types on any local site form a local topos (i.e. a topos whose global sections functor
has a fully faithful right adjoint), and a subcanonical site is local if and only if its topos of
sheaves of types is (see TODOs).

## Main definitions / results

* `J.IsLocalSite`: typeclass stating that `J` makes the category it is defined on into a local site.
* `IsLocalSite.point J`: the canonical point of any local site, whose fibre functor is given by
  the coyoneda embedding of the terminal object and extends to the global sections functors on
  presheaves and sheaves.
* `coconstantSheaf J A`: the coconstant sheaf functor `A ⥤ Sheaf J A` for any local site and
  sufficiently nice target category `A`, defined as the skyscraper sheaf functor of the canonical
  point.
* `ΓCoconstantSheafAdj J A`: the adjunction between the global sections functor `Γ J A` and
  `coconstantSheaf J A`.
* `fullyFaithfulCoconstantSheaf`: `coconstantSheaf` is fully faithful.
* `fullyFaithfulConstantSheaf`: on local sites, the constant sheaf functor is fully faithful.

## References

* https://ncatlab.org/nlab/show/local+site

## TODO

* Define local topoi and prove that sheaves on any local site form a local topos
* Show that a subcanonical site is local if and only if its global sections functor has a fully
  faithful right adjoint
-/

universe w u v u' v'

@[expose] public section

open CategoryTheory Limits Sheaf Opposite GrothendieckTopology

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- A local site is a site that has a terminal object with only a single covering sieve. -/
/-
**CategoryTheory.GrothendieckTopology.IsLocalSite** 是 Mathlib 中的一个归纳类型，位于命名空间 `C
ategoryTheory.GrothendieckTopology`。
形式化陈述：{C : Type u} → [inst : CategoryTheory.Category.{v, u} C] → CategoryTheory.
GrothendieckTopology C → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A local site is a site that has a terminal object with only a single covering si
eve.
-/
class GrothendieckTopology.IsLocalSite extends HasTerminal C where
  /-- The only covering sieve of the terminal object is the trivial sieve. -/
  eq_top_of_mem : ∀ S ∈ J (⊤_ C), S = ⊤

namespace GrothendieckTopology.IsLocalSite

/-- On a local site, every covering sieve contains every morphism from the terminal object. -/
/-
**CategoryTheory.GrothendieckTopology.IsLocalSite.from_terminal_mem_of_mem** 是 M
athlib 中的一个引理，位于命名空间 `CategoryTheory.GrothendieckTopology.IsLocalSite`。
形式化陈述：from_terminal_mem_of_mem [J.IsLocalSite] {X : C} (f : ⊤_ C ⟶ X) {S : Sieve
 X} (hS : S in J X) : S.arrows f
参数：f : ⊤_ C ⟶ X；hS : S in J X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrothendieckTopology.IsLocalSite.toHasLimitsOfShape`：∀ {C
 : Type u} {inst : CategoryTheory.Category.{v, u} C} (J : CategoryTheory.Grothen
dieckTopology C)   [self : J.IsLocalSite], CategoryTheor…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.Sieve.mem_iff_pullback_eq_top`：mem_iff_pullback_eq_top (f
 : Y ⟶ X) : S f ↔ S.pullback f = ⊤
· 使用定理 `CategoryTheory.GrothendieckTopology.IsLocalSite.eq_top_of_mem`：∀ {C : Ty
pe u} {inst : CategoryTheory.Category.{v, u} C} {J : CategoryTheory.Grothendieck
Topology C}   [self : J.IsLocalSite], ∀ S ∈ J (⊤_ C…
· 使用定理 `CategoryTheory.GrothendieckTopology.pullback_stable`：pullback_stable (f 
: Y ⟶ X) (hS : S in J X) : S.pullback f in J Y

--- 原说明 ---
On a local site, every covering sieve contains every morphism from the terminal 
object.
-/
lemma from_terminal_mem_of_mem [J.IsLocalSite] {X : C} (f : ⊤_ C ⟶ X) {S : Sieve X}
    (hS : S ∈ J X) : S.arrows f :=
  (S.mem_iff_pullback_eq_top f).mpr <| eq_top_of_mem _ <| J.pullback_stable f hS

/-- Every category with a terminal object becomes a local site with the trivial topology. -/
/-
**CategoryTheory.GrothendieckTopology.IsLocalSite.** 是 Mathlib 中的一个实例，位于命名空间 `Ca
tegoryTheory.GrothendieckTopology.IsLocalSite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Every category with a terminal object becomes a local site with the trivial topo
logy.
-/
instance {C : Type u} [Category.{v} C] [HasTerminal C] : (trivial C).IsLocalSite where
  eq_top_of_mem _ := trivial_covering.mp

/-- Every local site has a canonical point, given as a fibre functor by the coyoneda embedding of
the terminal object `⊤_ C`. -/
/-
**CategoryTheory.GrothendieckTopology.IsLocalSite.point** 是 Mathlib 中的一个定义，位于命名空
间 `CategoryTheory.GrothendieckTopology.IsLocalSite`。
形式化陈述：point [LocallySmall.{w} C] [J.IsLocalSite] : Point.{w} J where fiber
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrothendieckTopology.IsLocalSite.toHasLimitsOfShape`：∀ {C
 : Type u} {inst : CategoryTheory.Category.{v, u} C} (J : CategoryTheory.Grothen
dieckTopology C)   [self : J.IsLocalSite], CategoryTheor…

--- 原说明 ---
Every local site has a canonical point, given as a fibre functor by the coyoneda
 embedding of
the terminal object `⊤_ C`.
-/
noncomputable def point [LocallySmall.{w} C] [J.IsLocalSite] : Point.{w} J where
  fiber := shrinkCoyoneda.obj (op (⊤_ C))
  jointly_surjective R hR x :=
    ⟨(⊤_ C), shrinkCoyonedaObjObjEquiv x,
      (from_terminal_mem_of_mem J (shrinkCoyonedaObjObjEquiv x) hR),
          shrinkCoyonedaObjObjEquiv.symm (𝟙 _), by
        rw [shrinkCoyoneda_obj_map_shrinkCoyonedaObjObjEquiv_symm]
        simp⟩

variable [LocallySmall.{w} C] [J.IsLocalSite] (A : Type u') [Category.{v'} A]

/-- The right adjoint to the global sections functor that exists over any local site. This is
implemented as the skyscraper functor associated to `point.{w} J`, but can be thought of
as taking any object `X : A` to the sheaf that sends each `Y : C` to the product over copies of `A`
indexed by the points `⊤_ C ⟶ Y` of `Y`.

Note this takes in an extra universe parameter `w` that does not appear in the output type
`A ⥤ Sheaf J A` but is required for the construction; it should always be given explicitly when
referring to this functor, as in e.g. `coconstantSheaf.{w} J A`. -/
/-
**CategoryTheory.GrothendieckTopology.IsLocalSite.coconstantSheaf** 是 Mathlib 中的
一个定义，位于命名空间 `CategoryTheory.GrothendieckTopology.IsLocalSite`。
形式化陈述：coconstantSheaf [HasProducts.{w} A] : A ⥤ Sheaf J A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The right adjoint to the global sections functor that exists over any local site
. This is
implemented as the skyscraper functor associated to `point.{w} J`, but can be th
ought of
as taking any object `X : A` to the sheaf that sends each `Y : C` to the product
 over copies of `A`
indexed by the points `⊤_ C ⟶ Y` of `Y`.

Note this takes in an extra universe parameter `w` that does not appear in the o
utput type
`A ⥤ Sheaf J A` but is required for the construction; it should always be given 
explicitly when
referring to this functor, as in e.g. `coconstantSheaf.{w} J A`.
-/
noncomputable def coconstantSheaf [HasProducts.{w} A] : A ⥤ Sheaf J A :=
  (point.{w} J).skyscraperSheafFunctor

variable [HasColimitsOfSize.{w, w} A]

set_option backward.isDefEq.respectTransparency.types false in
variable {A} in
/-- The fibre of any presheaf `P : Cᵒᵖ ⥤ A` at `point J` is just `P` evaluated at
the terminal object. -/
/-
**CategoryTheory.GrothendieckTopology.IsLocalSite.pointPresheafFiberIso** 是 Math
lib 中的一个定义，位于命名空间 `CategoryTheory.GrothendieckTopology.IsLocalSite`。
形式化陈述：pointPresheafFiberIso (P : Cᵒᵖ ⥤ A) : (point J).presheafFiber.obj P ≅ P.ob
j (op (⊤_ C))
参数：P : Cᵒᵖ ⥤ A。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrothendieckTopology.IsLocalSite.toHasLimitsOfShape`：∀ {C
 : Type u} {inst : CategoryTheory.Category.{v, u} C} (J : CategoryTheory.Grothen
dieckTopology C)   [self : J.IsLocalSite], CategoryTheor…

--- 原说明 ---
The fibre of any presheaf `P : Cᵒᵖ ⥤ A` at `point J` is just `P` evaluated at
the terminal object.
-/
noncomputable def pointPresheafFiberIso (P : Cᵒᵖ ⥤ A) :
    (point J).presheafFiber.obj P ≅ P.obj (op (⊤_ C)) :=
  (colimit.isColimit _).coconePointUniqueUpToIso
    (colimitOfDiagramTerminal (Functor.Elements.isInitialOfCorepresentableBy
      <| shrinkCoyonedaCorepresentableBy <| op (⊤_ C)).op _)

variable {A} in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/-
**CategoryTheory.GrothendieckTopology.IsLocalSite.toPresheafFiber_pointPresheafF
iberIso_hom** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.GrothendieckTopology.IsLoc
alSite`。
形式化陈述：toPresheafFiber_pointPresheafFiberIso_hom {P : Cᵒᵖ ⥤ A} (X : C) (x : (poin
t J).fiber.obj X) : (point J).toPresheafFiber _ x _ ≫ (pointPresheafFiberIso J P
).hom = P.map (.op <| shrinkCoyonedaObjObjEquiv x)
参数：X : C；x : (point J).fiber.obj X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrothendieckTopology.IsLocalSite.toHasLimitsOfShape`：∀ {C
 : Type u} {inst : CategoryTheory.Category.{v, u} C} (J : CategoryTheory.Grothen
dieckTopology C)   [self : J.IsLocalSite], CategoryTheor…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.colimit.comp_coconePointUniqueUpToIso_hom`：∀ {J : 
Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : Cate
goryTheory.Category.{v, u} C]   {F : CategoryTheory.F…
-/
lemma toPresheafFiber_pointPresheafFiberIso_hom {P : Cᵒᵖ ⥤ A} (X : C) (x : (point J).fiber.obj X) :
    (point J).toPresheafFiber  _ x _ ≫ (pointPresheafFiberIso J P).hom =
      P.map (.op <| shrinkCoyonedaObjObjEquiv x) := by
  simp [Point.toPresheafFiber, pointPresheafFiberIso]
  rfl

variable {A} in
@[reassoc (attr := simp)]
/-
**CategoryTheory.GrothendieckTopology.IsLocalSite.pointPresheafFiberIso_naturali
ty** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.GrothendieckTopology.IsLocalSite`。
形式化陈述：pointPresheafFiberIso_naturality {P P' : Cᵒᵖ ⥤ A} (F : P ⟶ P') : (point J)
.presheafFiber.map F ≫ (pointPresheafFiberIso J P').hom = (pointPresheafFiberIso
 J P).hom ≫ F.app (op (⊤_ C))
参数：F : P ⟶ P'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.GrothendieckTopology.Point.presheafFiber_hom_ext`：preshea
fFiber_hom_ext {P : Cᵒᵖ ⥤ A} {T : A} {f g : Φ.presheafFiber.obj P ⟶ T} (h : fora
ll (X : C) (x : Φ.fiber.obj X), Φ.toPresheafFiber X x…
· 使用定理 `CategoryTheory.GrothendieckTopology.IsLocalSite.toHasLimitsOfShape`：∀ {C
 : Type u} {inst : CategoryTheory.Category.{v, u} C} (J : CategoryTheory.Grothen
dieckTopology C)   [self : J.IsLocalSite], CategoryTheor…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.GrothendieckTopology.Point.toPresheafFiber_naturality_ass
oc`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {J : CategoryTheory
.GrothendieckTopology C} (Φ : J.Point)   {A : Type u'} [inst_1 :…
· 使用引理 `CategoryTheory.GrothendieckTopology.IsLocalSite.toPresheafFiber_pointPre
sheafFiberIso_hom`：toPresheafFiber_pointPresheafFiberIso_hom {P : Cᵒᵖ ⥤ A} (X : 
C) (x : (point J).fiber.obj X) : (point J).toPresheafFiber _ x _ ≫ (pointPreshe…
· 使用定理 `CategoryTheory.GrothendieckTopology.IsLocalSite.toPresheafFiber_pointPre
sheafFiberIso_hom_assoc`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C
] (J : CategoryTheory.GrothendieckTopology C)   [inst_1 : CategoryTheory.Locally
Small…
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma pointPresheafFiberIso_naturality {P P' : Cᵒᵖ ⥤ A} (F : P ⟶ P') :
    (point J).presheafFiber.map F ≫ (pointPresheafFiberIso J P').hom =
      (pointPresheafFiberIso J P).hom ≫ F.app (op (⊤_ C)) := by
  cat_disch

/-- The presheaf fibre functor of `point J` is given by evaluation at the terminal
object. -/
/-
**CategoryTheory.GrothendieckTopology.IsLocalSite.pointPresheafFiberNatIso** 是 M
athlib 中的一个定义，位于命名空间 `CategoryTheory.GrothendieckTopology.IsLocalSite`。
形式化陈述：pointPresheafFiberNatIso : ((point J).presheafFiber : _ ⥤ A) ≅ (evaluation
 _ _).obj (op (⊤_ C))
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrothendieckTopology.IsLocalSite.toHasLimitsOfShape`：∀ {C
 : Type u} {inst : CategoryTheory.Category.{v, u} C} (J : CategoryTheory.Grothen
dieckTopology C)   [self : J.IsLocalSite], CategoryTheor…
· 使用引理 `CategoryTheory.GrothendieckTopology.IsLocalSite.pointPresheafFiberIso_na
turality`：pointPresheafFiberIso_naturality {P P' : Cᵒᵖ ⥤ A} (F : P ⟶ P') : (poin
t J).presheafFiber.map F ≫ (pointPresheafFiberIso J P').hom = (pointPr…

--- 原说明 ---
The presheaf fibre functor of `point J` is given by evaluation at the terminal
object.
-/
noncomputable def pointPresheafFiberNatIso :
    ((point J).presheafFiber : _ ⥤ A) ≅ (evaluation _ _).obj (op (⊤_ C)) :=
  NatIso.ofComponents (pointPresheafFiberIso J) fun F ↦ pointPresheafFiberIso_naturality J F

/-- The sheaf fibre functor of `point J` is the global sections functor. -/
/-
**CategoryTheory.GrothendieckTopology.IsLocalSite.pointSheafFiberIso** 是 Mathlib
 中的一个定义，位于命名空间 `CategoryTheory.GrothendieckTopology.IsLocalSite`。
形式化陈述：pointSheafFiberIso [HasWeakSheafify J A] : (point J).sheafFiber ≅ Γ J A
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrothendieckTopology.IsLocalSite.toHasLimitsOfShape`：∀ {C
 : Type u} {inst : CategoryTheory.Category.{v, u} C} (J : CategoryTheory.Grothen
dieckTopology C)   [self : J.IsLocalSite], CategoryTheor…

--- 原说明 ---
The sheaf fibre functor of `point J` is the global sections functor.
-/
noncomputable def pointSheafFiberIso
    [HasWeakSheafify J A] : (point J).sheafFiber ≅ Γ J A :=
  ((sheafToPresheaf J A).isoWhiskerLeft (pointPresheafFiberNatIso J A)).trans
    (ΓNatIsoSheafSections J A terminalIsTerminal).symm

variable [HasProducts.{w} A] [HasWeakSheafify J A]

/-- On local sites, the global sections functor `Γ` is left-adjoint to the coconstant functor. -/
/-
**CategoryTheory.GrothendieckTopology.IsLocalSite.** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.GrothendieckTopology.IsLocalSite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
On local sites, the global sections functor `Γ` is left-adjoint to the coconstan
t functor.
-/
noncomputable def ΓCoconstantSheafAdj : Γ J A ⊣ coconstantSheaf.{w} J A :=
  (point.{w} J).skyscraperSheafAdjunction.ofNatIsoLeft (pointSheafFiberIso J A)

/-- On any locally `w`-small local site, the global sections functor to any category with colimits
and products of size `w` is a left adjoint. A variant of this without the universe parameter `w`
is registered as an instance. -/
/-
**CategoryTheory.GrothendieckTopology.IsLocalSite.** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.GrothendieckTopology.IsLocalSite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
On any locally `w`-small local site, the global sections functor to any category
 with colimits
and products of size `w` is a left adjoint. A variant of this without the univer
se parameter `w`
is registered as an instance.
-/
lemma Γ_isLeftAdjoint : (Γ J A).IsLeftAdjoint :=
  ⟨coconstantSheaf.{w} J A, ⟨ΓCoconstantSheafAdj J A⟩⟩

/-- On any local site with morphism types in `Type v`, the global sections functor to any category
with colimits and products of size `v` is a left adjoint. See `ΓIsLeftAdjoint` for a
version for `w`-locally small sites that can't be registered as an instance because of the extra
universe parameter `w`. -/
/-
**CategoryTheory.GrothendieckTopology.IsLocalSite.** 是 Mathlib 中的一个实例，位于命名空间 `Ca
tegoryTheory.GrothendieckTopology.IsLocalSite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
On any local site with morphism types in `Type v`, the global sections functor t
o any category
with colimits and products of size `v` is a left adjoint. See `ΓIsLeftAdjoint` f
or a
version for `w`-locally small sites that can't be registered as an instance beca
use of the extra
universe parameter `w`.
-/
instance (A : Type u') [Category.{v'} A] [HasColimitsOfSize.{v, v} A]
    [HasProducts.{v} A] [HasWeakSheafify J A] : (Γ J A).IsLeftAdjoint :=
  Γ_isLeftAdjoint.{v} J A
/-
**CategoryTheory.GrothendieckTopology.IsLocalSite.** 是 Mathlib 中的一个实例，位于命名空间 `Ca
tegoryTheory.GrothendieckTopology.IsLocalSite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (coconstantSheaf.{w} J A).IsRightAdjoint :=
  ⟨Γ J A, ⟨ΓCoconstantSheafAdj J A⟩⟩

set_option backward.defeqAttrib.useBackward true in
/-- The global sections of the coconstant sheaf on a type are naturally isomorphic to that type. -/
/-
**CategoryTheory.GrothendieckTopology.IsLocalSite.coconstantSheaf** 是 Mathlib 中的
一个定义，位于命名空间 `CategoryTheory.GrothendieckTopology.IsLocalSite`。
形式化陈述：coconstantSheaf [HasProducts.{w} A] : A ⥤ Sheaf J A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The global sections of the coconstant sheaf on a type are naturally isomorphic t
o that type.
-/
noncomputable def coconstantSheafΓNatIsoId :
    IsLocalSite.coconstantSheaf.{w} J A ⋙ Γ J A ≅ 𝟭 A :=
  letI : Unique (unop ((IsLocalSite.point J).fiber.op.obj (op (⊤_ C)))) :=
    (equivShrink (⊤_ C ⟶ ⊤_ C)).symm.unique
  (Functor.isoWhiskerLeft _ (ΓNatIsoSheafSections J _ terminalIsTerminal)) ≪≫
    NatIso.ofComponents (fun X ↦ productUniqueIso _) (by simp [IsLocalSite.coconstantSheaf])

/-- `coconstantSheaf` is fully faithful. -/
/-
**CategoryTheory.GrothendieckTopology.IsLocalSite.fullyFaithfulCoconstantSheaf**
 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.GrothendieckTopology.IsLocalSite`。
形式化陈述：fullyFaithfulCoconstantSheaf : (coconstantSheaf.{w} J A).FullyFaithful
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`coconstantSheaf` is fully faithful.
-/
noncomputable def fullyFaithfulCoconstantSheaf :
    (coconstantSheaf.{w} J A).FullyFaithful :=
  (ΓCoconstantSheafAdj J A).fullyFaithfulROfCompIsoId (coconstantSheafΓNatIsoId J A)
/-
**CategoryTheory.GrothendieckTopology.IsLocalSite.** 是 Mathlib 中的一个实例，位于命名空间 `Ca
tegoryTheory.GrothendieckTopology.IsLocalSite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (coconstantSheaf.{w} J A).Full :=
  (fullyFaithfulCoconstantSheaf J A).full
/-
**CategoryTheory.GrothendieckTopology.IsLocalSite.** 是 Mathlib 中的一个实例，位于命名空间 `Ca
tegoryTheory.GrothendieckTopology.IsLocalSite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (coconstantSheaf.{w} J A).Faithful :=
  (fullyFaithfulCoconstantSheaf J A).faithful

/-- The adjoint triple `constantSheaf J A ⊣ Γ J A ⊣ coconstantSheaf J A` on any local site. -/
/-
**CategoryTheory.GrothendieckTopology.IsLocalSite.constant** 是 Mathlib 中的一个缩写定义，
位于命名空间 `CategoryTheory.GrothendieckTopology.IsLocalSite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The adjoint triple `constantSheaf J A ⊣ Γ J A ⊣ coconstantSheaf J A` on any loca
l site.
-/
noncomputable abbrev constantΓCoconstantTriple :
    Adjunction.Triple (constantSheaf J A) (Γ J A) (coconstantSheaf.{w} J A) where
  adj₁ := constantSheafΓAdj J A
  adj₂ := ΓCoconstantSheafAdj J A

/-- On local sites, the constant sheaf functor is fully faithful. -/
/-
**CategoryTheory.GrothendieckTopology.IsLocalSite.fullyFaithfulConstantSheaf** 是
 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.GrothendieckTopology.IsLocalSite`。
形式化陈述：fullyFaithfulConstantSheaf : (constantSheaf J A).FullyFaithful
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
On local sites, the constant sheaf functor is fully faithful.
-/
noncomputable def fullyFaithfulConstantSheaf : (constantSheaf J A).FullyFaithful :=
  (constantΓCoconstantTriple J A).fullyFaithfulEquiv.symm <|
    fullyFaithfulCoconstantSheaf.{w} J A
/-
**CategoryTheory.GrothendieckTopology.IsLocalSite.full_constantSheaf** 是 Mathlib
 中的一个引理，位于命名空间 `CategoryTheory.GrothendieckTopology.IsLocalSite`。
形式化陈述：full_constantSheaf : (constantSheaf J A).Full
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.FullyFaithful.full`：full : F.Full where map_surje
ctive
-/
lemma full_constantSheaf : (constantSheaf J A).Full :=
  (fullyFaithfulConstantSheaf.{w} J A).full
/-
**CategoryTheory.GrothendieckTopology.IsLocalSite.faithful_constantSheaf** 是 Mat
hlib 中的一个引理，位于命名空间 `CategoryTheory.GrothendieckTopology.IsLocalSite`。
形式化陈述：faithful_constantSheaf : (constantSheaf J A).Faithful
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.FullyFaithful.faithful`：faithful : F.Faithful whe
re map_injective
-/
lemma faithful_constantSheaf : (constantSheaf J A).Faithful :=
  (fullyFaithfulConstantSheaf.{w} J A).faithful

/-- See `IsLocalSite.full_constantSheaf` for a version for `w`-locally small sites. -/
/-
**CategoryTheory.GrothendieckTopology.IsLocalSite.** 是 Mathlib 中的一个实例，位于命名空间 `Ca
tegoryTheory.GrothendieckTopology.IsLocalSite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See `IsLocalSite.full_constantSheaf` for a version for `w`-locally small sites.
-/
instance {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) [J.IsLocalSite]
    (A : Type u') [Category.{v'} A] [HasColimitsOfSize.{v, v} A]
    [HasProducts.{v} A] [HasWeakSheafify J A] : (constantSheaf J A).Full :=
  full_constantSheaf.{v} J A

/-- See `IsLocalSite.faithful_constantSheaf` for a version for `w`-locally small sites. -/
/-
**CategoryTheory.GrothendieckTopology.IsLocalSite.** 是 Mathlib 中的一个实例，位于命名空间 `Ca
tegoryTheory.GrothendieckTopology.IsLocalSite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See `IsLocalSite.faithful_constantSheaf` for a version for `w`-locally small sit
es.
-/
instance {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) [J.IsLocalSite]
    (A : Type u') [Category.{v'} A] [HasColimitsOfSize.{v, v} A]
    [HasProducts.{v} A] [HasWeakSheafify J A] : (constantSheaf J A).Faithful :=
  faithful_constantSheaf.{v} J A

end GrothendieckTopology.IsLocalSite

end CategoryTheory

