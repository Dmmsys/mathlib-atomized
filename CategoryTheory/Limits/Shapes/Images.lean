/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Mono
public import Mathlib.CategoryTheory.Limits.Shapes.StrongEpi
public import Mathlib.CategoryTheory.MorphismProperty.Factorization

/-!
# Categorical images

We define the categorical image of `f` as a factorisation `f = e ≫ m` through a monomorphism `m`,
so that `m` factors through the `m'` in any other such factorisation.

## Main definitions

* A `MonoFactorisation` is a factorisation `f = e ≫ m`, where `m` is a monomorphism
* `IsImage F` means that a given mono factorisation `F` has the universal property of the image.
* `HasImage f` means that there is some image factorization for the morphism `f : X ⟶ Y`.
  * In this case, `image f` is some image object (selected with choice), `image.ι f : image f ⟶ Y`
    is the monomorphism `m` of the factorisation and `factorThruImage f : X ⟶ image f` is the
    morphism `e`.
* `HasImages C` means that every morphism in `C` has an image.
* Let `f : X ⟶ Y` and `g : P ⟶ Q` be morphisms in `C`, which we will represent as objects of the
  arrow category `Arrow C`. Then `sq : f ⟶ g` is a commutative square in `C`. If `f` and `g` have
  images, then `HasImageMap sq` represents the fact that there is a morphism
  `i : image f ⟶ image g` making the diagram

  X ----→ image f ----→ Y
  |         |           |
  |         |           |
  ↓         ↓           ↓
  P ----→ image g ----→ Q

  commute, where the top row is the image factorisation of `f`, the bottom row is the image
  factorisation of `g`, and the outer rectangle is the commutative square `sq`.
* If a category `HasImages`, then `HasImageMaps` means that every commutative square admits an
  image map.
* If a category `HasImages`, then `HasStrongEpiImages` means that the morphism to the image is
  always a strong epimorphism.

## Main statements

* When `C` has equalizers, the morphism `e` appearing in an image factorisation is an epimorphism.
* When `C` has strong epi images, then these images admit image maps.

## Future work
* TODO: coimages, and abelian categories.
* TODO: connect this with existing work in the group theory and ring theory libraries.

-/

@[expose] public section


noncomputable section

universe w v u

open CategoryTheory

open CategoryTheory.Limits.WalkingParallelPair

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]
variable {X Y : C} (f : X ⟶ Y)

/-- A factorisation of a morphism `f = e ≫ m`, with `m` monic. -/
/-
**CategoryTheory.Limits.MonoFactorisation** 是 Mathlib 中的一个结构，位于命名空间 `CategoryThe
ory.Limits`。
形式化陈述：MonoFactorisation (f : X ⟶ Y) where I : C m : I ⟶ Y [m_mono : Mono m] e : 
X ⟶ I fac : e ≫ m = f
参数：f : X ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A factorisation of a morphism `f = e ≫ m`, with `m` monic.
-/
structure MonoFactorisation (f : X ⟶ Y) where
  I : C
  m : I ⟶ Y
  [m_mono : Mono m]
  e : X ⟶ I
  fac : e ≫ m = f := by cat_disch

attribute [inherit_doc MonoFactorisation] MonoFactorisation.I MonoFactorisation.m
  MonoFactorisation.m_mono MonoFactorisation.e MonoFactorisation.fac

attribute [reassoc (attr := simp)] MonoFactorisation.fac

attribute [instance] MonoFactorisation.m_mono

namespace MonoFactorisation

/-- The obvious factorisation of a monomorphism through itself. -/
/-
**CategoryTheory.Limits.MonoFactorisation.self** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Limits.MonoFactorisation`。
形式化陈述：self [Mono f] : MonoFactorisation f where I
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The obvious factorisation of a monomorphism through itself.
-/
def self [Mono f] : MonoFactorisation f where
  I := X
  m := f
  e := 𝟙 X

-- I'm not sure we really need this, but the linter says that an inhabited instance
-- ought to exist...
/-
**CategoryTheory.Limits.MonoFactorisation.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTh
eory.Limits.MonoFactorisation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Mono f] : Inhabited (MonoFactorisation f) := ⟨self f⟩

variable {f}

/-- The morphism `m` in a factorisation `f = e ≫ m` through a monomorphism is uniquely
determined. -/
@[ext (iff := false)]
/-
**CategoryTheory.Limits.MonoFactorisation.ext** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Limits.MonoFactorisation`。
形式化陈述：ext {F F' : MonoFactorisation f} (hI : F.I = F'.I) (hm : F.m = eqToHom hI 
≫ F'.m) : F = F'
参数：hI : F.I = F'.I；hm : F.m = eqToHom hI ≫ F'.m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'

--- 原说明 ---
The morphism `m` in a factorisation `f = e ≫ m` through a monomorphism is unique
ly
determined.
-/
theorem ext {F F' : MonoFactorisation f} (hI : F.I = F'.I)
    (hm : F.m = eqToHom hI ≫ F'.m) : F = F' := by
  obtain ⟨_, Fm, _, Ffac⟩ := F; obtain ⟨_, Fm', _, Ffac'⟩ := F'
  cases hI
  replace hm : Fm = Fm' := by simpa using hm
  congr
  apply (cancel_mono Fm).1
  rw [Ffac, hm, Ffac']

/-- Any mono factorisation of `f` gives a mono factorisation of `f ≫ g` when `g` is a mono. -/
@[simps]
/-
**CategoryTheory.Limits.MonoFactorisation.compMono** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Limits.MonoFactorisation`。
形式化陈述：compMono (F : MonoFactorisation f) {Y' : C} (g : Y ⟶ Y') [Mono g] : MonoFa
ctorisation (f ≫ g) where I
参数：F : MonoFactorisation f；g : Y ⟶ Y'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any mono factorisation of `f` gives a mono factorisation of `f ≫ g` when `g` is 
a mono.
-/
def compMono (F : MonoFactorisation f) {Y' : C} (g : Y ⟶ Y') [Mono g] :
    MonoFactorisation (f ≫ g) where
  I := F.I
  m := F.m ≫ g
  m_mono := mono_comp _ _
  e := F.e

/-- A mono factorisation of `f ≫ g`, where `g` is an isomorphism,
gives a mono factorisation of `f`. -/
@[simps]
/-
**CategoryTheory.Limits.MonoFactorisation.ofCompIso** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Limits.MonoFactorisation`。
形式化陈述：ofCompIso {Y' : C} {g : Y ⟶ Y'} [IsIso g] (F : MonoFactorisation (f ≫ g)) 
: MonoFactorisation f where I
参数：F : MonoFactorisation (f ≫ g)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A mono factorisation of `f ≫ g`, where `g` is an isomorphism,
gives a mono factorisation of `f`.
-/
def ofCompIso {Y' : C} {g : Y ⟶ Y'} [IsIso g] (F : MonoFactorisation (f ≫ g)) :
    MonoFactorisation f where
  I := F.I
  m := F.m ≫ inv g
  m_mono := mono_comp _ _
  e := F.e

/-- Any mono factorisation of `f` gives a mono factorisation of `g ≫ f`. -/
@[simps]
/-
**CategoryTheory.Limits.MonoFactorisation.isoComp** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Limits.MonoFactorisation`。
形式化陈述：isoComp (F : MonoFactorisation f) {X' : C} (g : X' ⟶ X) : MonoFactorisatio
n (g ≫ f) where I
参数：F : MonoFactorisation f；g : X' ⟶ X。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.MonoFactorisation.m_mono`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] {X Y : C} {f : X ⟶ Y}   (self : CategoryTheory.
Limits.MonoFactorisation f), Categor…

--- 原说明 ---
Any mono factorisation of `f` gives a mono factorisation of `g ≫ f`.
-/
def isoComp (F : MonoFactorisation f) {X' : C} (g : X' ⟶ X) : MonoFactorisation (g ≫ f) where
  I := F.I
  m := F.m
  e := g ≫ F.e

/-- A mono factorisation of `g ≫ f`, where `g` is an isomorphism,
gives a mono factorisation of `f`. -/
@[simps]
/-
**CategoryTheory.Limits.MonoFactorisation.ofIsoComp** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Limits.MonoFactorisation`。
形式化陈述：ofIsoComp {X' : C} (g : X' ⟶ X) [IsIso g] (F : MonoFactorisation (g ≫ f)) 
: MonoFactorisation f where I
参数：g : X' ⟶ X；F : MonoFactorisation (g ≫ f)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A mono factorisation of `g ≫ f`, where `g` is an isomorphism,
gives a mono factorisation of `f`.
-/
def ofIsoComp {X' : C} (g : X' ⟶ X) [IsIso g] (F : MonoFactorisation (g ≫ f)) :
    MonoFactorisation f where
  I := F.I
  m := F.m
  e := inv g ≫ F.e

/-- If `f` and `g` are isomorphic arrows, then a mono factorisation of `f`
gives a mono factorisation of `g` -/
@[simps]
/-
**CategoryTheory.Limits.MonoFactorisation.ofArrowIso** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Limits.MonoFactorisation`。
形式化陈述：ofArrowIso {f g : Arrow C} (F : MonoFactorisation f.hom) (sq : f ⟶ g) [IsI
so sq] : MonoFactorisation g.hom where I
参数：F : MonoFactorisation f.hom；sq : f ⟶ g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f` and `g` are isomorphic arrows, then a mono factorisation of `f`
gives a mono factorisation of `g`
-/
def ofArrowIso {f g : Arrow C} (F : MonoFactorisation f.hom) (sq : f ⟶ g) [IsIso sq] :
    MonoFactorisation g.hom where
  I := F.I
  m := F.m ≫ sq.right
  e := inv sq.left ≫ F.e
  m_mono := mono_comp _ _
  fac := by simp only [fac_assoc, Arrow.w, IsIso.inv_comp_eq, Category.assoc]

/--
Given a mono factorisation `X ⟶ I ⟶ Y` of an arrow `f`, an isomorphism `I ≅ I'` gives a new mono
factorisation `X ⟶ I' ⟶ Y` of `f`.
-/
@[simps]
/-
**CategoryTheory.Limits.MonoFactorisation.ofIsoI** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Limits.MonoFactorisation`。
形式化陈述：ofIsoI (F : MonoFactorisation f) {I'} (e : F.I ≅ I') : MonoFactorisation f
 where I
参数：F : MonoFactorisation f；e : F.I ≅ I'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a mono factorisation `X ⟶ I ⟶ Y` of an arrow `f`, an isomorphism `I ≅ I'` 
gives a new mono
factorisation `X ⟶ I' ⟶ Y` of `f`.
-/
def ofIsoI (F : MonoFactorisation f) {I'} (e : F.I ≅ I') :
    MonoFactorisation f where
  I := I'
  m := e.inv ≫ F.m
  e := F.e ≫ e.hom

/--
Copying a mono factorisation to another mono factorisation with propositionally equal
`m` and `e` fields.
-/
@[simps]
/-
**CategoryTheory.Limits.MonoFactorisation.copy** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Limits.MonoFactorisation`。
形式化陈述：copy (F : MonoFactorisation f) (m : F.I ⟶ Y) (e : X ⟶ F.I) (hm : m = F.m
参数：F : MonoFactorisation f；m : F.I ⟶ Y；e : X ⟶ F.I。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Copying a mono factorisation to another mono factorisation with propositionally 
equal
`m` and `e` fields.
-/
def copy (F : MonoFactorisation f) (m : F.I ⟶ Y) (e : X ⟶ F.I)
    (hm : m = F.m := by cat_disch) (he : e = F.e := by cat_disch) :
    MonoFactorisation f where
  I := F.I
  m := m
  e := e
  m_mono := by rw [hm]; infer_instance

@[simp]
/-
**CategoryTheory.Limits.MonoFactorisation.fac_apply** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.Limits.MonoFactorisation`。
形式化陈述：fac_apply {F G : C ⥤ Type w} {f : F ⟶ G} {X : C} (H : MonoFactorisation f)
 (x : F.obj X) : H.m.app X (H.e.app X x) = f.app X x
参数：H : MonoFactorisation f；x : F.obj X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Limits.MonoFactorisation.fac`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y : C} {f : X ⟶ Y}   (self : CategoryTheory.Lim
its.MonoFactorisation f), Categor…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma fac_apply {F G : C ⥤ Type w} {f : F ⟶ G} {X : C}
    (H : MonoFactorisation f) (x : F.obj X) : H.m.app X (H.e.app X x) = f.app X x := by
  simp [← comp_apply, ← NatTrans.comp_app]

end MonoFactorisation

variable {f}

/-- Data exhibiting that a given factorisation through a mono is initial. -/
/-
**CategoryTheory.Limits.IsImage** 是 Mathlib 中的一个结构，位于命名空间 `CategoryTheory.Limits
`。
形式化陈述：IsImage (F : MonoFactorisation f) where lift : forall F' : MonoFactorisati
on f, F.I ⟶ F'.I lift_fac : forall F' : MonoFactorisation f, lift F' ≫ F'.m = F.
m
参数：F : MonoFactorisation f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Data exhibiting that a given factorisation through a mono is initial.
-/
structure IsImage (F : MonoFactorisation f) where
  lift : ∀ F' : MonoFactorisation f, F.I ⟶ F'.I
  lift_fac : ∀ F' : MonoFactorisation f, lift F' ≫ F'.m = F.m := by cat_disch

attribute [inherit_doc IsImage] IsImage.lift IsImage.lift_fac

attribute [reassoc (attr := simp)] IsImage.lift_fac

namespace IsImage

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.IsImage.fac_lift** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Limits.IsImage`。
形式化陈述：fac_lift {F : MonoFactorisation f} (hF : IsImage F) (F' : MonoFactorisatio
n f) : F.e ≫ hF.lift F' = F'.e
参数：hF : IsImage F；F' : MonoFactorisation f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.Limits.MonoFactorisation.m_mono`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] {X Y : C} {f : X ⟶ Y}   (self : CategoryTheory.
Limits.MonoFactorisation f), Categor…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.IsImage.lift_fac`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {X Y : C} {f : X ⟶ Y}   {F : CategoryTheory.Limits.Mono
Factorisation f} (self : Cat…
· 使用定理 `CategoryTheory.Limits.MonoFactorisation.fac`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y : C} {f : X ⟶ Y}   (self : CategoryTheory.Lim
its.MonoFactorisation f), Categor…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem fac_lift {F : MonoFactorisation f} (hF : IsImage F) (F' : MonoFactorisation f) :
    F.e ≫ hF.lift F' = F'.e :=
  (cancel_mono F'.m).1 <| by simp

variable (f)

set_option backward.isDefEq.respectTransparency.types false in
/-- The trivial factorisation of a monomorphism satisfies the universal property. -/
@[simps]
/-
**CategoryTheory.Limits.IsImage.self** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.L
imits.IsImage`。
形式化陈述：self [Mono f] : IsImage (MonoFactorisation.self f) where lift F'
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The trivial factorisation of a monomorphism satisfies the universal property.
-/
def self [Mono f] : IsImage (MonoFactorisation.self f) where lift F' := F'.e
/-
**CategoryTheory.Limits.IsImage.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limit
s.IsImage`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Mono f] : Inhabited (IsImage (MonoFactorisation.self f)) :=
  ⟨self f⟩

variable {f}

-- TODO this is another good candidate for a future `UniqueUpToCanonicalIso`.
/-- Two factorisations through monomorphisms satisfying the universal property
must factor through isomorphic objects. -/
@[simps]
/-
**CategoryTheory.Limits.IsImage.isoExt** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Limits.IsImage`。
形式化陈述：isoExt {F F' : MonoFactorisation f} (hF : IsImage F) (hF' : IsImage F') : 
F.I ≅ F'.I where hom
参数：hF : IsImage F；hF' : IsImage F'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Two factorisations through monomorphisms satisfying the universal property
must factor through isomorphic objects.
-/
def isoExt {F F' : MonoFactorisation f} (hF : IsImage F) (hF' : IsImage F') :
    F.I ≅ F'.I where
  hom := hF.lift F'
  inv := hF'.lift F
  hom_inv_id := (cancel_mono F.m).1 (by simp)
  inv_hom_id := (cancel_mono F'.m).1 (by simp)

variable {F F' : MonoFactorisation f} (hF : IsImage F) (hF' : IsImage F')
/-
**CategoryTheory.Limits.IsImage.isoExt_hom_m** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Limits.IsImage`。
形式化陈述：isoExt_hom_m : (isoExt hF hF').hom ≫ F'.m = F.m
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.IsImage.isoExt_hom`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y : C} {f : X ⟶ Y}   {F F' : CategoryTheory.Limits
.MonoFactorisation f} (hF : Ca…
· 使用定理 `CategoryTheory.Limits.IsImage.lift_fac`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {X Y : C} {f : X ⟶ Y}   {F : CategoryTheory.Limits.Mono
Factorisation f} (self : Cat…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem isoExt_hom_m : (isoExt hF hF').hom ≫ F'.m = F.m := by simp
/-
**CategoryTheory.Limits.IsImage.isoExt_inv_m** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Limits.IsImage`。
形式化陈述：isoExt_inv_m : (isoExt hF hF').inv ≫ F.m = F'.m
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.IsImage.isoExt_inv`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y : C} {f : X ⟶ Y}   {F F' : CategoryTheory.Limits
.MonoFactorisation f} (hF : Ca…
· 使用定理 `CategoryTheory.Limits.IsImage.lift_fac`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {X Y : C} {f : X ⟶ Y}   {F : CategoryTheory.Limits.Mono
Factorisation f} (self : Cat…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem isoExt_inv_m : (isoExt hF hF').inv ≫ F.m = F'.m := by simp
/-
**CategoryTheory.Limits.IsImage.e_isoExt_hom** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Limits.IsImage`。
形式化陈述：e_isoExt_hom : F.e ≫ (isoExt hF hF').hom = F'.e
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.IsImage.isoExt_hom`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y : C} {f : X ⟶ Y}   {F F' : CategoryTheory.Limits
.MonoFactorisation f} (hF : Ca…
· 使用定理 `CategoryTheory.Limits.IsImage.fac_lift`：fac_lift {F : MonoFactorisation 
f} (hF : IsImage F) (F' : MonoFactorisation f) : F.e ≫ hF.lift F' = F'.e
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem e_isoExt_hom : F.e ≫ (isoExt hF hF').hom = F'.e := by simp
/-
**CategoryTheory.Limits.IsImage.e_isoExt_inv** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Limits.IsImage`。
形式化陈述：e_isoExt_inv : F'.e ≫ (isoExt hF hF').inv = F.e
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.IsImage.isoExt_inv`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y : C} {f : X ⟶ Y}   {F F' : CategoryTheory.Limits
.MonoFactorisation f} (hF : Ca…
· 使用定理 `CategoryTheory.Limits.IsImage.fac_lift`：fac_lift {F : MonoFactorisation 
f} (hF : IsImage F) (F' : MonoFactorisation f) : F.e ≫ hF.lift F' = F'.e
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem e_isoExt_inv : F'.e ≫ (isoExt hF hF').inv = F.e := by simp

set_option backward.isDefEq.respectTransparency false in
/-- If `f` and `g` are isomorphic arrows, then a mono factorisation of `f` that is an image
gives a mono factorisation of `g` that is an image -/
@[simps]
/-
**CategoryTheory.Limits.IsImage.ofArrowIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Limits.IsImage`。
形式化陈述：ofArrowIso {f g : Arrow C} {F : MonoFactorisation f.hom} (hF : IsImage F) 
(sq : f ⟶ g) [IsIso sq] : IsImage (F.ofArrowIso sq) where lift F'
参数：hF : IsImage F；sq : f ⟶ g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f` and `g` are isomorphic arrows, then a mono factorisation of `f` that is a
n image
gives a mono factorisation of `g` that is an image
-/
def ofArrowIso {f g : Arrow C} {F : MonoFactorisation f.hom} (hF : IsImage F) (sq : f ⟶ g)
    [IsIso sq] : IsImage (F.ofArrowIso sq) where
  lift F' := hF.lift (F'.ofArrowIso (inv sq))
  lift_fac F' := by
    simpa only [MonoFactorisation.ofArrowIso_m, Arrow.inv_right, ← Category.assoc,
      IsIso.comp_inv_eq] using hF.lift_fac (F'.ofArrowIso (inv sq))

set_option backward.isDefEq.respectTransparency.types false in
/--
Given a mono factorisation `X ⟶ I ⟶ Y` of an arrow `f` that is an image and an isomorphism `I ≅ I'`,
the induced mono factorisation by the isomorphism is also an image.
-/
@[simps]
/-
**CategoryTheory.Limits.IsImage.ofIsoI** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Limits.IsImage`。
形式化陈述：ofIsoI {F : MonoFactorisation f} (hF : IsImage F) {I' : C} (e : F.I ≅ I') 
: IsImage (F.ofIsoI e) where lift F'
参数：hF : IsImage F；e : F.I ≅ I'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a mono factorisation `X ⟶ I ⟶ Y` of an arrow `f` that is an image and an i
somorphism `I ≅ I'`,
the induced mono factorisation by the isomorphism is also an image.
-/
def ofIsoI {F : MonoFactorisation f} (hF : IsImage F) {I' : C} (e : F.I ≅ I') :
    IsImage (F.ofIsoI e) where
  lift F' := e.inv ≫ hF.lift F'

set_option backward.defeqAttrib.useBackward true in
/--
Copying a mono factorisation to another mono factorisation with propositionally equal fields
preserves the property of being an image.
This is useful when one needs precise control of the `m` and `e` fields.
-/
@[simps]
/-
**CategoryTheory.Limits.IsImage.copy** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.L
imits.IsImage`。
形式化陈述：copy {F : MonoFactorisation f} (hF : IsImage F) (m : F.I ⟶ Y) (e : X ⟶ F.I
) (hm : m = F.m
参数：hF : IsImage F；m : F.I ⟶ Y；e : X ⟶ F.I。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Copying a mono factorisation to another mono factorisation with propositionally 
equal fields
preserves the property of being an image.
This is useful when one needs precise control of the `m` and `e` fields.
-/
def copy {F : MonoFactorisation f} (hF : IsImage F) (m : F.I ⟶ Y) (e : X ⟶ F.I)
    (hm : m = F.m := by cat_disch) (he : e = F.e := by cat_disch) :
    IsImage (F.copy m e) where
  lift := hF.lift

end IsImage

variable (f)

/-- Data exhibiting that a morphism `f` has an image. -/
/-
**CategoryTheory.Limits.ImageFactorisation** 是 Mathlib 中的一个归纳类型，位于命名空间 `Category
Theory.Limits`。
形式化陈述：{C : Type u} → [inst : CategoryTheory.Category.{v, u} C] → {X Y : C} → (X 
⟶ Y) → Type (max u v)
参数：X ⟶ Y；max u v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Data exhibiting that a morphism `f` has an image.
-/
structure ImageFactorisation (f : X ⟶ Y) where
  F : MonoFactorisation f
  isImage : IsImage F

attribute [inherit_doc ImageFactorisation] ImageFactorisation.F ImageFactorisation.isImage

namespace ImageFactorisation

/-
**CategoryTheory.Limits.ImageFactorisation.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryT
heory.Limits.ImageFactorisation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Mono f] : Inhabited (ImageFactorisation f) :=
  ⟨⟨_, IsImage.self f⟩⟩

/-- If `f` and `g` are isomorphic arrows, then an image factorisation of `f`
gives an image factorisation of `g` -/
@[simps]
/-
**CategoryTheory.Limits.ImageFactorisation.ofArrowIso** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.Limits.ImageFactorisation`。
形式化陈述：ofArrowIso {f g : Arrow C} (F : ImageFactorisation f.hom) (sq : f ⟶ g) [Is
Iso sq] : ImageFactorisation g.hom where F
参数：F : ImageFactorisation f.hom；sq : f ⟶ g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f` and `g` are isomorphic arrows, then an image factorisation of `f`
gives an image factorisation of `g`
-/
def ofArrowIso {f g : Arrow C} (F : ImageFactorisation f.hom) (sq : f ⟶ g) [IsIso sq] :
    ImageFactorisation g.hom where
  F := F.F.ofArrowIso sq
  isImage := F.isImage.ofArrowIso sq

/--
Given an image factorisation `X ⟶ I ⟶ Y` of an arrow `f`, an isomorphism `I ≅ I'` induces a new
image factorisation `X ⟶ I' ⟶ Y` of `f`.
-/
@[simps]
/-
**CategoryTheory.Limits.ImageFactorisation.ofIsoI** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Limits.ImageFactorisation`。
形式化陈述：ofIsoI {f : X ⟶ Y} (F : ImageFactorisation f) {I' : C} (e : F.F.I ≅ I') : 
ImageFactorisation f where F
参数：F : ImageFactorisation f；e : F.F.I ≅ I'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an image factorisation `X ⟶ I ⟶ Y` of an arrow `f`, an isomorphism `I ≅ I'
` induces a new
image factorisation `X ⟶ I' ⟶ Y` of `f`.
-/
def ofIsoI {f : X ⟶ Y} (F : ImageFactorisation f) {I' : C} (e : F.F.I ≅ I') :
    ImageFactorisation f where
  F := F.F.ofIsoI e
  isImage := F.isImage.ofIsoI e

/--
Copying an image factorisation to another image factorisation with propositionally equal
`m` and `e` fields.
-/
@[simps]
/-
**CategoryTheory.Limits.ImageFactorisation.copy** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Limits.ImageFactorisation`。
形式化陈述：copy {f : X ⟶ Y} (F : ImageFactorisation f) (m : F.F.I ⟶ Y) (e : X ⟶ F.F.I
) (hm : m = F.F.m
参数：F : ImageFactorisation f；m : F.F.I ⟶ Y；e : X ⟶ F.F.I。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Copying an image factorisation to another image factorisation with propositional
ly equal
`m` and `e` fields.
-/
def copy {f : X ⟶ Y} (F : ImageFactorisation f) (m : F.F.I ⟶ Y) (e : X ⟶ F.F.I)
    (hm : m = F.F.m := by cat_disch) (he : e = F.F.e := by cat_disch) :
    ImageFactorisation f where
  F := F.F.copy m e
  isImage := F.isImage.copy m e

end ImageFactorisation

/-- `HasImage f` means that there exists an image factorisation of `f`. -/
/-
**CategoryTheory.Limits.HasImage** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory.Lim
its`。
形式化陈述：{C : Type u} → [inst : CategoryTheory.Category.{v, u} C] → {X Y : C} → (X 
⟶ Y) → Prop
参数：X ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`HasImage f` means that there exists an image factorisation of `f`.
-/
class HasImage (f : X ⟶ Y) : Prop where mk' ::
  exists_image : Nonempty (ImageFactorisation f)

attribute [inherit_doc HasImage] HasImage.exists_image
/-
**CategoryTheory.Limits.HasImage.mk** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Li
mits.HasImage`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} {f : X 
⟶ Y}   (F : CategoryTheory.Limits.ImageFactorisation f), CategoryTheory.Limits.H
asImage f
参数：F : CategoryTheory.Limits.ImageFactorisation f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem HasImage.mk {f : X ⟶ Y} (F : ImageFactorisation f) : HasImage f :=
  ⟨Nonempty.intro F⟩
/-
**CategoryTheory.Limits.HasImage.of_arrow_iso** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Limits.HasImage`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {f g : CategoryTh
eory.Arrow C}   [h : CategoryTheory.Limits.HasImage f.hom] (sq : f ⟶ g) [Categor
yTheory.IsIso sq],   CategoryTheory.Limits.HasImage g.hom
参数：sq : f ⟶ g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasImage.exists_image`：∀ {C : Type u} {inst : Cate
goryTheory.Category.{v, u} C} {X Y : C} {f : X ⟶ Y}   [self : CategoryTheory.Lim
its.HasImage f], Nonempty (Catego…
-/
theorem HasImage.of_arrow_iso {f g : Arrow C} [h : HasImage f.hom] (sq : f ⟶ g) [IsIso sq] :
    HasImage g.hom :=
  ⟨⟨h.exists_image.some.ofArrowIso sq⟩⟩
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) mono_hasImage (f : X ⟶ Y) [Mono f] : HasImage f :=
  HasImage.mk ⟨_, IsImage.self f⟩

section

variable [HasImage f]

/-- Some image factorisation of `f` through a monomorphism (selected with choice). -/
/-
**CategoryTheory.Limits.Image.imageFactorisation** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Limits.Image`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {X Y : C}
 → (f : X ⟶ Y) → [CategoryTheory.Limits.HasImage f] → CategoryTheory.Limits.Imag
eFactorisation f
参数：f : X ⟶ Y。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasImage.exists_image`：∀ {C : Type u} {inst : Cate
goryTheory.Category.{v, u} C} {X Y : C} {f : X ⟶ Y}   [self : CategoryTheory.Lim
its.HasImage f], Nonempty (Catego…

--- 原说明 ---
Some image factorisation of `f` through a monomorphism (selected with choice).
-/
def Image.imageFactorisation : ImageFactorisation f :=
  Classical.choice HasImage.exists_image

/-- Some factorisation of `f` through a monomorphism (selected with choice). -/
/-
**CategoryTheory.Limits.Image.monoFactorisation** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Limits.Image`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {X Y : C}
 → (f : X ⟶ Y) → [CategoryTheory.Limits.HasImage f] → CategoryTheory.Limits.Mono
Factorisation f
参数：f : X ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Some factorisation of `f` through a monomorphism (selected with choice).
-/
def Image.monoFactorisation : MonoFactorisation f :=
  (Image.imageFactorisation f).F

/-- The witness of the universal property for the chosen factorisation of `f` through
a monomorphism. -/
/-
**CategoryTheory.Limits.Image.isImage** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Limits.Image`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {X Y : C}
 →       (f : X ⟶ Y) →         [inst_1 : CategoryTheory.Limits.HasImage f] →    
       CategoryTheory.Limits.IsImage (CategoryTheory.Limits.Image.monoFactorisat
ion f)
参数：f : X ⟶ Y；CategoryTheory.Limits.Image.monoFactorisation f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The witness of the universal property for the chosen factorisation of `f` throug
h
a monomorphism.
-/
def Image.isImage : IsImage (Image.monoFactorisation f) :=
  (Image.imageFactorisation f).isImage

/-- The categorical image of a morphism. -/
@[implicit_reducible]
/-
**CategoryTheory.Limits.image** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：image : C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The categorical image of a morphism.
-/
def image : C :=
  (Image.monoFactorisation f).I

/-- The inclusion of the image of a morphism into the target. -/
/-
**CategoryTheory.Limits.image.** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limits`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion of the image of a morphism into the target.
-/
def image.ι : image f ⟶ Y :=
  (Image.monoFactorisation f).m

@[simp]
/-
**CategoryTheory.Limits.image.as_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Limi
ts`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem image.as_ι : (Image.monoFactorisation f).m = image.ι f := rfl
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Mono (image.ι f) :=
  (Image.monoFactorisation f).m_mono

/-- The map from the source to the image of a morphism. -/
/-
**CategoryTheory.Limits.factorThruImage** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Limits`。
形式化陈述：factorThruImage : X ⟶ image f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map from the source to the image of a morphism.
-/
def factorThruImage : X ⟶ image f :=
  (Image.monoFactorisation f).e

/-- Rewrite in terms of the `factorThruImage` interface. -/
@[simp]
/-
**CategoryTheory.Limits.as_factorThruImage** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Limits`。
形式化陈述：as_factorThruImage : (Image.monoFactorisation f).e = factorThruImage f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Rewrite in terms of the `factorThruImage` interface.
-/
theorem as_factorThruImage : (Image.monoFactorisation f).e = factorThruImage f :=
  rfl

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.image.fac** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Limi
ts.image`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} (f : X 
⟶ Y)   [inst_1 : CategoryTheory.Limits.HasImage f],   CategoryTheory.CategoryStr
uct.comp (CategoryTheory.Limits.factorThruImage f) (CategoryTheory.Limits.image.
ι f) = f
参数：f : X ⟶ Y；CategoryTheory.Limits.factorThruImage f；CategoryTheory.Limits.image
.ι f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.MonoFactorisation.fac`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y : C} {f : X ⟶ Y}   (self : CategoryTheory.Lim
its.MonoFactorisation f), Categor…
-/
theorem image.fac : factorThruImage f ≫ image.ι f = f :=
  (Image.monoFactorisation f).fac

variable {f}

/-- Any other factorisation of the morphism `f` through a monomorphism receives a map from the
image. -/
/-
**CategoryTheory.Limits.image.lift** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Lim
its.image`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {X Y : C}
 →       {f : X ⟶ Y} →         [inst_1 : CategoryTheory.Limits.HasImage f] →    
       (F' : CategoryTheory.Limits.MonoFactorisation f) → CategoryTheory.Limits.
image f ⟶ F'.I
参数：F' : CategoryTheory.Limits.MonoFactorisation f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any other factorisation of the morphism `f` through a monomorphism receives a ma
p from the
image.
-/
def image.lift (F' : MonoFactorisation f) : image f ⟶ F'.I :=
  (Image.isImage f).lift F'

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.image.lift_fac** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Limits.image`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} {f : X 
⟶ Y}   [inst_1 : CategoryTheory.Limits.HasImage f] (F' : CategoryTheory.Limits.M
onoFactorisation f),   CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits
.image.lift F') F'.m = CategoryTheory.Limits.image.ι f
参数：F' : CategoryTheory.Limits.MonoFactorisation f；CategoryTheory.Limits.image.li
ft F'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsImage.lift_fac`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {X Y : C} {f : X ⟶ Y}   {F : CategoryTheory.Limits.Mono
Factorisation f} (self : Cat…
-/
theorem image.lift_fac (F' : MonoFactorisation f) : image.lift F' ≫ F'.m = image.ι f :=
  (Image.isImage f).lift_fac F'

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.image.fac_lift** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Limits.image`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} {f : X 
⟶ Y}   [inst_1 : CategoryTheory.Limits.HasImage f] (F' : CategoryTheory.Limits.M
onoFactorisation f),   CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits
.factorThruImage f) (CategoryTheory.Limits.image.lift F') =     F'.e
参数：F' : CategoryTheory.Limits.MonoFactorisation f；CategoryTheory.Limits.factorTh
ruImage f；CategoryTheory.Limits.image.lift F'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsImage.fac_lift`：fac_lift {F : MonoFactorisation 
f} (hF : IsImage F) (F' : MonoFactorisation f) : F.e ≫ hF.lift F' = F'.e
-/
theorem image.fac_lift (F' : MonoFactorisation f) : factorThruImage f ≫ image.lift F' = F'.e :=
  (Image.isImage f).fac_lift F'

@[simp]
/-
**CategoryTheory.Limits.image.isImage_lift** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Limits.image`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} {f : X 
⟶ Y}   [inst_1 : CategoryTheory.Limits.HasImage f] (F : CategoryTheory.Limits.Mo
noFactorisation f),   (CategoryTheory.Limits.Image.isImage f).lift F = CategoryT
heory.Limits.image.lift F
参数：F : CategoryTheory.Limits.MonoFactorisation f；CategoryTheory.Limits.Image.isI
mage f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem image.isImage_lift (F : MonoFactorisation f) : (Image.isImage f).lift F = image.lift F :=
  rfl

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.IsImage.lift_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IsImage.lift_ι {F : MonoFactorisation f} (hF : IsImage F) :
    hF.lift (Image.monoFactorisation f) ≫ image.ι f = F.m :=
  hF.lift_fac _

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.image.lift_mk_factorThruImage** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.Limits.image`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} {f : X 
⟶ Y}   [inst_1 : CategoryTheory.Limits.HasImage f],   CategoryTheory.CategoryStr
uct.comp       (CategoryTheory.Limits.image.lift         { I := CategoryTheory.L
imits.image f, m := CategoryTheory.Limits.image.ι f, m_mono := ⋯,           e :=
 CategoryTheory.Limits.factorThruImage f, fac := ⋯ })       (CategoryTheory.Limi
ts.image.ι f) =     CategoryTheory.Limits.image.ι f
参数：CategoryTheory.Limits.image.lift         { I := CategoryTheory.Limits.image f
, m := CategoryTheory.Limits.image.ι f, m_mono := ⋯,           e := CategoryTheo
ry.Limits.factorThruImage f, fac := ⋯ }；CategoryTheory.Limits.image.ι f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsImage.lift_fac`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {X Y : C} {f : X ⟶ Y}   {F : CategoryTheory.Limits.Mono
Factorisation f} (self : Cat…
· 使用定理 `CategoryTheory.Limits.instMonoι`：∀ {C : Type u} [inst : CategoryTheory.C
ategory.{v, u} C] {X Y : C} (f : X ⟶ Y)   [inst_1 : CategoryTheory.Limits.HasIma
ge f], CategoryTheory…
-/
theorem image.lift_mk_factorThruImage :
    image.lift { I := image f, m := ι f, e := factorThruImage f } ≫ image.ι f = image.ι f :=
  (Image.isImage f).lift_fac _

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.image.lift_mk_comp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Limits.image`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y Z : C} (f : 
X ⟶ Y) (g : Y ⟶ Z)   [inst_1 : CategoryTheory.Limits.HasImage g]   [inst_2 : Cat
egoryTheory.Limits.HasImage (CategoryTheory.CategoryStruct.comp f g)]   (h : Y ⟶
 CategoryTheory.Limits.image g)   (H :     CategoryTheory.CategoryStruct.comp (C
ategoryTheory.CategoryStruct.comp f h) (CategoryTheory.Limits.image.ι g) =      
 CategoryTheory.CategoryStruct.comp f g),   CategoryTheory.CategoryStruct.comp  
     (CategoryTheory.Limits.image.lift         { I := CategoryTheory.Limits.imag
e g, m := CategoryTheory.Limits.image.ι g, m_mono := ⋯,           e := CategoryT
heory.CategoryStruct.comp f h, fac := ⋯ })       (CategoryTheory.Limits.image.ι 
g) =     CategoryTheory.Limits.image.ι (CategoryTheory.CategoryStruct.comp f g)
参数：f : X ⟶ Y；g : Y ⟶ Z；CategoryTheory.CategoryStruct.comp f g；h : Y ⟶ CategoryTh
eory.Limits.image g；H :     CategoryTheory.CategoryStruct.comp (CategoryTheory.C
ategoryStruct.comp f h) (CategoryTheory.Limits.image.ι g) =       CategoryTheory
.CategoryStruct.comp f g；CategoryTheory.Limits.image.lift         { I := Categor
yTheory.Limits.image g, m := CategoryTheory.Limits.image.ι g, m_mono := ⋯,      
     e := CategoryTheory.CategoryStruct.comp f h, fac := ⋯ }；CategoryTheory.Limi
ts.image.ι g；CategoryTheory.CategoryStruct.comp f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.image.lift_fac`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {X Y : C} {f : X ⟶ Y}   [inst_1 : CategoryTheory.Limits.H
asImage f] (F' : CategoryT…
· 使用定理 `CategoryTheory.Limits.instMonoι`：∀ {C : Type u} [inst : CategoryTheory.C
ategory.{v, u} C] {X Y : C} (f : X ⟶ Y)   [inst_1 : CategoryTheory.Limits.HasIma
ge f], CategoryTheory…
-/
theorem image.lift_mk_comp {C : Type u} [Category.{v} C] {X Y Z : C}
    (f : X ⟶ Y) (g : Y ⟶ Z) [HasImage g] [HasImage (f ≫ g)]
    (h : Y ⟶ image g) (H : (f ≫ h) ≫ image.ι g = f ≫ g) :
    image.lift { I := image g, m := ι g, e := (f ≫ h) } ≫ image.ι g = image.ι (f ≫ g) :=
  image.lift_fac _

-- TODO we could put a category structure on `MonoFactorisation f`,
-- with the morphisms being `g : I ⟶ I'` commuting with the `m`s
-- (they then automatically commute with the `e`s)
-- and show that an `imageOf f` gives an initial object there
-- (uniqueness of the lift comes for free).
/-
**CategoryTheory.Limits.image.lift_mono** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Limits.image`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} {f : X 
⟶ Y}   [inst_1 : CategoryTheory.Limits.HasImage f] (F' : CategoryTheory.Limits.M
onoFactorisation f),   CategoryTheory.Mono (CategoryTheory.Limits.image.lift F')
参数：F' : CategoryTheory.Limits.MonoFactorisation f；CategoryTheory.Limits.image.li
ft F'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.mono_of_mono`：∀ {C : Type u} [inst : CategoryTheory.Categ
ory.{v, u} C] {X Y Z : C} (g : Z ⟶ Y) (f : Y ⟶ X)   [CategoryTheory.Mono (Catego
ryTheory.Category…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.image.lift_fac`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {X Y : C} {f : X ⟶ Y}   [inst_1 : CategoryTheory.Limits.H
asImage f] (F' : CategoryT…
· 使用定理 `CategoryTheory.Limits.MonoFactorisation.m_mono`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] {X Y : C} {f : X ⟶ Y}   (self : CategoryTheory.
Limits.MonoFactorisation f), Categor…
-/
instance image.lift_mono (F' : MonoFactorisation f) : Mono (image.lift F') := by
  refine @mono_of_mono _ _ _ _ _ _ F'.m ?_
  simpa using! MonoFactorisation.m_mono _
/-
**CategoryTheory.Limits.HasImage.uniq** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
Limits.HasImage`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} {f : X 
⟶ Y}   [inst_1 : CategoryTheory.Limits.HasImage f] (F' : CategoryTheory.Limits.M
onoFactorisation f)   (l : CategoryTheory.Limits.image f ⟶ F'.I),   CategoryTheo
ry.CategoryStruct.comp l F'.m = CategoryTheory.Limits.image.ι f → l = CategoryTh
eory.Limits.image.lift F'
参数：F' : CategoryTheory.Limits.MonoFactorisation f；l : CategoryTheory.Limits.imag
e f ⟶ F'.I。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.Limits.MonoFactorisation.m_mono`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] {X Y : C} {f : X ⟶ Y}   (self : CategoryTheory.
Limits.MonoFactorisation f), Categor…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.image.lift_fac`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {X Y : C} {f : X ⟶ Y}   [inst_1 : CategoryTheory.Limits.H
asImage f] (F' : CategoryT…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem HasImage.uniq (F' : MonoFactorisation f) (l : image f ⟶ F'.I) (w : l ≫ F'.m = image.ι f) :
    l = image.lift F' :=
  (cancel_mono F'.m).1 (by simp [w])

/-- If `has_image g`, then `has_image (f ≫ g)` when `f` is an isomorphism. -/
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `has_image g`, then `has_image (f ≫ g)` when `f` is an isomorphism.
-/
instance {X Y Z : C} (f : X ⟶ Y) [IsIso f] (g : Y ⟶ Z) [HasImage g] : HasImage (f ≫ g) where
  exists_image :=
    ⟨{  F :=
          { I := image g
            m := image.ι g
            e := f ≫ factorThruImage g }
        isImage :=
          { lift := fun F' => image.lift
                { I := F'.I
                  m := F'.m
                  e := inv f ≫ F'.e } } }⟩

end

section

variable (C)

/-- `HasImages` asserts that every morphism has an image. -/
/-
**CategoryTheory.Limits.HasImages** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory.Li
mits`。
形式化陈述：(C : Type u) → [CategoryTheory.Category.{v, u} C] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`HasImages` asserts that every morphism has an image.
-/
class HasImages : Prop where
  has_image : ∀ {X Y : C} (f : X ⟶ Y), HasImage f

attribute [inherit_doc HasImages] HasImages.has_image

attribute [instance 100] HasImages.has_image

end

section

/-- The image of a monomorphism is isomorphic to the source. -/
/-
**CategoryTheory.Limits.imageMonoIsoSource** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Limits`。
形式化陈述：imageMonoIsoSource [Mono f] : image f ≅ X
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.mono_hasImage`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.Mono f],   CategoryT
heory.Limits.HasImage f

--- 原说明 ---
The image of a monomorphism is isomorphic to the source.
-/
def imageMonoIsoSource [Mono f] : image f ≅ X :=
  IsImage.isoExt (Image.isImage f) (IsImage.self f)

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.imageMonoIsoSource_inv_** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem imageMonoIsoSource_inv_ι [Mono f] : (imageMonoIsoSource f).inv ≫ image.ι f = f := by
  simp [imageMonoIsoSource]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.imageMonoIsoSource_hom_self** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.Limits`。
形式化陈述：imageMonoIsoSource_hom_self [Mono f] : (imageMonoIsoSource f).hom ≫ f = im
age.ι f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.mono_hasImage`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.Mono f],   CategoryT
heory.Limits.HasImage f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.imageMonoIsoSource_inv_ι`：imageMonoIsoSource_inv_ι
 [Mono f] : (imageMonoIsoSource f).inv ≫ image.ι f = f
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
-/
theorem imageMonoIsoSource_hom_self [Mono f] : (imageMonoIsoSource f).hom ≫ f = image.ι f := by
  simp only [← imageMonoIsoSource_inv_ι f]
  rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
-- This is the proof that `factorThruImage f` is an epimorphism
-- from https://en.wikipedia.org/wiki/Image_%28category_theory%29, which is in turn taken from:
-- Mitchell, Barry (1965), Theory of categories, MR 0202787, p.12, Proposition 10.1
@[ext (iff := false)]
/-
**CategoryTheory.Limits.image.ext** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Limi
ts.image`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} (f : X 
⟶ Y)   [inst_1 : CategoryTheory.Limits.HasImage f] {W : C} {g h : CategoryTheory
.Limits.image f ⟶ W}   [CategoryTheory.Limits.HasLimit (CategoryTheory.Limits.pa
rallelPair g h)],   CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.fa
ctorThruImage f) g =       CategoryTheory.CategoryStruct.comp (CategoryTheory.Li
mits.factorThruImage f) h →     g = h
参数：f : X ⟶ Y；CategoryTheory.Limits.parallelPair g h；CategoryTheory.Limits.factor
ThruImage f；CategoryTheory.Limits.factorThruImage f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.mono_comp`：∀ {C : Type u} [inst : CategoryTheory.Category
.{v, u} C] {X Y Z : C} (g : Z ⟶ Y) [CategoryTheory.Mono g] (f : Y ⟶ X)   [Catego
ryTheory.Mono …
· 使用定理 `CategoryTheory.Limits.equalizer.ι_mono`：∀ {C : Type u} {X Y : C} [inst :
 CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y}   [inst_1 : CategoryTheory.Limi
ts.HasEqualizer f g], Catego…
· 使用定理 `CategoryTheory.Limits.instMonoι`：∀ {C : Type u} [inst : CategoryTheory.C
ategory.{v, u} C] {X Y : C} (f : X ⟶ Y)   [inst_1 : CategoryTheory.Limits.HasIma
ge f], CategoryTheory…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.limit.lift_π_assoc`：∀ {J : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v,
 u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.image.fac`：∀ {C : Type u} [inst : CategoryTheory.C
ategory.{v, u} C] {X Y : C} (f : X ⟶ Y)   [inst_1 : CategoryTheory.Limits.HasIma
ge f],   CategoryTheo…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.image.lift_fac`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {X Y : C} {f : X ⟶ Y}   [inst_1 : CategoryTheory.Limits.H
asImage f] (F' : CategoryT…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.cancel_mono_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {h : Y ⟶ Y},   Cat
egoryTheory.Categor…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Limits.equalizer.condition`：∀ {C : Type u} {X Y : C} [ins
t : CategoryTheory.Category.{v, u} C] (f g : X ⟶ Y)   [inst_1 : CategoryTheory.L
imits.HasEqualizer f g],   Cate…
-/
theorem image.ext [HasImage f] {W : C} {g h : image f ⟶ W} [HasLimit (parallelPair g h)]
    (w : factorThruImage f ≫ g = factorThruImage f ≫ h) : g = h := by
  let q := equalizer.ι g h
  let e' := equalizer.lift _ w
  let F' : MonoFactorisation f :=
    { I := equalizer g h
      m := q ≫ image.ι f
      m_mono := mono_comp _ _
      e := e' }
  let v := image.lift F'
  have t₀ : v ≫ q ≫ image.ι f = image.ι f := image.lift_fac F'
  have t : v ≫ q = 𝟙 (image f) :=
    (cancel_mono_id (image.ι f)).1
      (by
        convert! t₀ using 1
        rw [Category.assoc])
  -- The proof from wikipedia next proves `q ≫ v = 𝟙 _`,
  -- and concludes that `equalizer g h ≅ image f`,
  -- but this isn't necessary.
  calc
    g = 𝟙 (image f) ≫ g := by rw [Category.id_comp]
    _ = v ≫ q ≫ g := by rw [← t, Category.assoc]
    _ = v ≫ q ≫ h := by rw [equalizer.condition g h]
    _ = 𝟙 (image f) ≫ h := by rw [← Category.assoc, t]
    _ = h := by rw [Category.id_comp]
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasImage f] [∀ {Z : C} (g h : image f ⟶ Z), HasLimit (parallelPair g h)] :
    Epi (factorThruImage f) :=
  ⟨fun _ _ w => image.ext f w⟩
/-
**CategoryTheory.Limits.epi_image_of_epi** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Limits`。
形式化陈述：epi_image_of_epi {X Y : C} (f : X ⟶ Y) [HasImage f] [E : Epi f] : Epi (ima
ge.ι f)
参数：f : X ⟶ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.epi_of_epi`：epi_of_epi (f : X ⟶ Y) (g : Y ⟶ Z) [Epi (f ≫ 
g)] : Epi g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.image.fac`：∀ {C : Type u} [inst : CategoryTheory.C
ategory.{v, u} C] {X Y : C} (f : X ⟶ Y)   [inst_1 : CategoryTheory.Limits.HasIma
ge f],   CategoryTheo…
-/
theorem epi_image_of_epi {X Y : C} (f : X ⟶ Y) [HasImage f] [E : Epi f] : Epi (image.ι f) := by
  rw [← image.fac f] at E
  exact epi_of_epi (factorThruImage f) (image.ι f)
/-
**CategoryTheory.Limits.epi_of_epi_image** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Limits`。
形式化陈述：epi_of_epi_image {X Y : C} (f : X ⟶ Y) [HasImage f] [Epi (image.ι f)] [Epi
 (factorThruImage f)] : Epi f
参数：f : X ⟶ Y；image.ι f；factorThruImage f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.image.fac`：∀ {C : Type u} [inst : CategoryTheory.C
ategory.{v, u} C] {X Y : C} (f : X ⟶ Y)   [inst_1 : CategoryTheory.Limits.HasIma
ge f],   CategoryTheo…
-/
theorem epi_of_epi_image {X Y : C} (f : X ⟶ Y) [HasImage f] [Epi (image.ι f)]
    [Epi (factorThruImage f)] : Epi f := by
  rw [← image.fac f]
  apply epi_comp

end

section

variable {f}
variable {f' : X ⟶ Y} [HasImage f] [HasImage f']

/-- An equation between morphisms gives a comparison map between the images
(which momentarily we prove is an iso).
-/
/-
**CategoryTheory.Limits.image.eqToHom** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Limits.image`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {X Y : C}
 →       {f f' : X ⟶ Y} →         [inst_1 : CategoryTheory.Limits.HasImage f] → 
          [inst_2 : CategoryTheory.Limits.HasImage f'] →             f = f' → (C
ategoryTheory.Limits.image f ⟶ CategoryTheory.Limits.image f')
参数：CategoryTheory.Limits.image f ⟶ CategoryTheory.Limits.image f'。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instMonoι`：∀ {C : Type u} [inst : CategoryTheory.C
ategory.{v, u} C] {X Y : C} (f : X ⟶ Y)   [inst_1 : CategoryTheory.Limits.HasIma
ge f], CategoryTheory…

--- 原说明 ---
An equation between morphisms gives a comparison map between the images
(which momentarily we prove is an iso).
-/
def image.eqToHom (h : f = f') : image f ⟶ image f' :=
  image.lift
    { I := image f'
      m := image.ι f'
      e := factorThruImage f'
      fac := by rw [h]; simp only [image.fac] }
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (h : f = f') : IsIso (image.eqToHom h) :=
  ⟨⟨image.eqToHom h.symm,
      ⟨(cancel_mono (image.ι f)).1 (by
          subst h
          simp [image.eqToHom, Category.assoc, Category.id_comp]),
        (cancel_mono (image.ι f')).1 (by
          subst h
          simp [image.eqToHom])⟩⟩⟩

/-- An equation between morphisms gives an isomorphism between the images. -/
/-
**CategoryTheory.Limits.image.eqToIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Limits.image`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {X Y : C}
 →       {f f' : X ⟶ Y} →         [inst_1 : CategoryTheory.Limits.HasImage f] → 
          [inst_2 : CategoryTheory.Limits.HasImage f'] →             f = f' → (C
ategoryTheory.Limits.image f ≅ CategoryTheory.Limits.image f')
参数：CategoryTheory.Limits.image f ≅ CategoryTheory.Limits.image f'。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instIsIsoEqToHom`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {X Y : C} {f f' : X ⟶ Y}   [inst_1 : CategoryTheory.Lim
its.HasImage f] [inst_2 : Ca…

--- 原说明 ---
An equation between morphisms gives an isomorphism between the images.
-/
def image.eqToIso (h : f = f') : image f ≅ image f' :=
  asIso (image.eqToHom h)

/-- As long as the category has equalizers,
the image inclusion maps commute with `image.eqToIso`.
-/
/-
**CategoryTheory.Limits.image.eq_fac** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.L
imits.image`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} {f f' :
 X ⟶ Y}   [inst_1 : CategoryTheory.Limits.HasImage f] [inst_2 : CategoryTheory.L
imits.HasImage f']   [CategoryTheory.Limits.HasEqualizers C] (h : f = f'),   Cat
egoryTheory.Limits.image.ι f =     CategoryTheory.CategoryStruct.comp (CategoryT
heory.Limits.image.eqToIso h).hom (CategoryTheory.Limits.image.ι f')
参数：h : f = f'；CategoryTheory.Limits.image.eqToIso h；CategoryTheory.Limits.image.
ι f'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.image.ext`：∀ {C : Type u} [inst : CategoryTheory.C
ategory.{v, u} C] {X Y : C} (f : X ⟶ Y)   [inst_1 : CategoryTheory.Limits.HasIma
ge f] {W : C} {g h : …
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.image.fac`：∀ {C : Type u} [inst : CategoryTheory.C
ategory.{v, u} C] {X Y : C} (f : X ⟶ Y)   [inst_1 : CategoryTheory.Limits.HasIma
ge f],   CategoryTheo…
· 使用定理 `CategoryTheory.Limits.image.lift_mk_factorThruImage`：∀ {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C] {X Y : C} {f : X ⟶ Y}   [inst_1 : Category
Theory.Limits.HasImage f],   CategoryTheo…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
As long as the category has equalizers,
the image inclusion maps commute with `image.eqToIso`.
-/
theorem image.eq_fac [HasEqualizers C] (h : f = f') :
    image.ι f = (image.eqToIso h).hom ≫ image.ι f' := by
  apply image.ext
  subst h
  simp [asIso, image.eqToIso, image.eqToHom]

end

section

variable {Z : C} (g : Y ⟶ Z)

/-- The comparison map `image (f ≫ g) ⟶ image g`. -/
/-
**CategoryTheory.Limits.image.preComp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Limits.image`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {X Y : C}
 →       (f : X ⟶ Y) →         {Z : C} →           (g : Y ⟶ Z) →             [in
st_1 : CategoryTheory.Limits.HasImage g] →               [inst_2 : CategoryTheor
y.Limits.HasImage (CategoryTheory.CategoryStruct.comp f g)] →                 Ca
tegoryTheory.Limits.image (CategoryTheory.CategoryStruct.comp f g) ⟶ CategoryThe
ory.Limits.image g
参数：f : X ⟶ Y；g : Y ⟶ Z；CategoryTheory.CategoryStruct.comp f g；CategoryTheory.Cat
egoryStruct.comp f g。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instMonoι`：∀ {C : Type u} [inst : CategoryTheory.C
ategory.{v, u} C] {X Y : C} (f : X ⟶ Y)   [inst_1 : CategoryTheory.Limits.HasIma
ge f], CategoryTheory…

--- 原说明 ---
The comparison map `image (f ≫ g) ⟶ image g`.
-/
def image.preComp [HasImage g] [HasImage (f ≫ g)] : image (f ≫ g) ⟶ image g :=
  image.lift
    { I := image g
      m := image.ι g
      e := f ≫ factorThruImage g }

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.image.preComp_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem image.preComp_ι [HasImage g] [HasImage (f ≫ g)] :
    image.preComp f g ≫ image.ι g = image.ι (f ≫ g) := by
      simp [image.preComp]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.image.factorThruImage_preComp** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.Limits.image`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} (f : X 
⟶ Y) {Z : C} (g : Y ⟶ Z)   [inst_1 : CategoryTheory.Limits.HasImage g]   [inst_2
 : CategoryTheory.Limits.HasImage (CategoryTheory.CategoryStruct.comp f g)],   C
ategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.factorThruImage (Catego
ryTheory.CategoryStruct.comp f g))       (CategoryTheory.Limits.image.preComp f 
g) =     CategoryTheory.CategoryStruct.comp f (CategoryTheory.Limits.factorThruI
mage g)
参数：f : X ⟶ Y；g : Y ⟶ Z；CategoryTheory.CategoryStruct.comp f g；CategoryTheory.Lim
its.factorThruImage (CategoryTheory.CategoryStruct.comp f g)；CategoryTheory.Limi
ts.image.preComp f g；CategoryTheory.Limits.factorThruImage g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.image.fac_lift`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {X Y : C} {f : X ⟶ Y}   [inst_1 : CategoryTheory.Limits.H
asImage f] (F' : CategoryT…
· 使用定理 `CategoryTheory.Limits.instMonoι`：∀ {C : Type u} [inst : CategoryTheory.C
ategory.{v, u} C] {X Y : C} (f : X ⟶ Y)   [inst_1 : CategoryTheory.Limits.HasIma
ge f], CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem image.factorThruImage_preComp [HasImage g] [HasImage (f ≫ g)] :
    factorThruImage (f ≫ g) ≫ image.preComp f g = f ≫ factorThruImage g := by simp [image.preComp]

/-- `image.preComp f g` is a monomorphism.
-/
/-
**CategoryTheory.Limits.image.preComp_mono** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Limits.image`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} (f : X 
⟶ Y) {Z : C} (g : Y ⟶ Z)   [inst_1 : CategoryTheory.Limits.HasImage g]   [inst_2
 : CategoryTheory.Limits.HasImage (CategoryTheory.CategoryStruct.comp f g)],   C
ategoryTheory.Mono (CategoryTheory.Limits.image.preComp f g)
参数：f : X ⟶ Y；g : Y ⟶ Z；CategoryTheory.CategoryStruct.comp f g；CategoryTheory.Lim
its.image.preComp f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.mono_of_mono`：∀ {C : Type u} [inst : CategoryTheory.Categ
ory.{v, u} C] {X Y Z : C} (g : Z ⟶ Y) (f : Y ⟶ X)   [CategoryTheory.Mono (Catego
ryTheory.Category…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.image.preComp_ι`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y) {Z : C} (g : Y ⟶ Z)   [inst_1 : Ca
tegoryTheory.Limits.HasImag…
· 使用定理 `CategoryTheory.Limits.instMonoι`：∀ {C : Type u} [inst : CategoryTheory.C
ategory.{v, u} C] {X Y : C} (f : X ⟶ Y)   [inst_1 : CategoryTheory.Limits.HasIma
ge f], CategoryTheory…

--- 原说明 ---
`image.preComp f g` is a monomorphism.
-/
instance image.preComp_mono [HasImage g] [HasImage (f ≫ g)] : Mono (image.preComp f g) := by
  refine @mono_of_mono _ _ _ _ _ _ (image.ι g) ?_
  simp only [image.preComp_ι]
  infer_instance

/-- The two step comparison map
  `image (f ≫ (g ≫ h)) ⟶ image (g ≫ h) ⟶ image h`
agrees with the one step comparison map
  `image (f ≫ (g ≫ h)) ≅ image ((f ≫ g) ≫ h) ⟶ image h`.
-/
/-
**CategoryTheory.Limits.image.preComp_comp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Limits.image`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} (f : X 
⟶ Y) {Z : C} (g : Y ⟶ Z) {W : C} (h : Z ⟶ W)   [inst_1 : CategoryTheory.Limits.H
asImage (CategoryTheory.CategoryStruct.comp g h)]   [inst_2 :     CategoryTheory
.Limits.HasImage (CategoryTheory.CategoryStruct.comp f (CategoryTheory.CategoryS
truct.comp g h))]   [inst_3 : CategoryTheory.Limits.HasImage h]   [inst_4 :     
CategoryTheory.Limits.HasImage (CategoryTheory.CategoryStruct.comp (CategoryTheo
ry.CategoryStruct.comp f g) h)],   CategoryTheory.CategoryStruct.comp (CategoryT
heory.Limits.image.preComp f (CategoryTheory.CategoryStruct.comp g h))       (Ca
tegoryTheory.Limits.image.preComp g h) =     CategoryTheory.CategoryStruct.comp 
(CategoryTheory.Limits.image.eqToHom ⋯)       (CategoryTheory.Limits.image.preCo
mp (CategoryTheory.CategoryStruct.comp f g) h)
参数：f : X ⟶ Y；g : Y ⟶ Z；h : Z ⟶ W；CategoryTheory.CategoryStruct.comp g h；Category
Theory.CategoryStruct.comp f (CategoryTheory.CategoryStruct.comp g h)；CategoryTh
eory.CategoryStruct.comp (CategoryTheory.CategoryStruct.comp f g) h；CategoryTheo
ry.Limits.image.preComp f (CategoryTheory.CategoryStruct.comp g h)；CategoryTheor
y.Limits.image.preComp g h；CategoryTheory.Limits.image.eqToHom ⋯；CategoryTheory.
Limits.image.preComp (CategoryTheory.CategoryStruct.comp f g) h。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.Limits.instMonoι`：∀ {C : Type u} [inst : CategoryTheory.C
ategory.{v, u} C] {X Y : C} (f : X ⟶ Y)   [inst_1 : CategoryTheory.Limits.HasIma
ge f], CategoryTheory…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.image.lift_mk_comp`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)   [inst_1 : Categ
oryTheory.Limits.HasImage g]  …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.image.fac`：∀ {C : Type u} [inst : CategoryTheory.C
ategory.{v, u} C] {X Y : C} (f : X ⟶ Y)   [inst_1 : CategoryTheory.Limits.HasIma
ge f],   CategoryTheo…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.image.lift_fac`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {X Y : C} {f : X ⟶ Y}   [inst_1 : CategoryTheory.Limits.H
asImage f] (F' : CategoryT…

--- 原说明 ---
The two step comparison map
  `image (f ≫ (g ≫ h)) ⟶ image (g ≫ h) ⟶ image h`
agrees with the one step comparison map
  `image (f ≫ (g ≫ h)) ≅ image ((f ≫ g) ≫ h) ⟶ image h`.
-/
theorem image.preComp_comp {W : C} (h : Z ⟶ W) [HasImage (g ≫ h)] [HasImage (f ≫ g ≫ h)]
    [HasImage h] [HasImage ((f ≫ g) ≫ h)] :
    image.preComp f (g ≫ h) ≫ image.preComp g h =
      image.eqToHom (Category.assoc f g h).symm ≫ image.preComp (f ≫ g) h := by
  apply (cancel_mono (image.ι h)).1
  simp only [preComp, Category.assoc, fac, lift_mk_comp, eqToHom]
  rw [image.lift_fac]

variable [HasEqualizers C]

/-- `image.preComp f g` is an epimorphism when `f` is an epimorphism
(we need `C` to have equalizers to prove this).
-/
/-
**CategoryTheory.Limits.image.preComp_epi_of_epi** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Limits.image`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} (f : X 
⟶ Y) {Z : C} (g : Y ⟶ Z)   [CategoryTheory.Limits.HasEqualizers C] [inst_2 : Cat
egoryTheory.Limits.HasImage g]   [inst_3 : CategoryTheory.Limits.HasImage (Categ
oryTheory.CategoryStruct.comp f g)] [CategoryTheory.Epi f],   CategoryTheory.Epi
 (CategoryTheory.Limits.image.preComp f g)
参数：f : X ⟶ Y；g : Y ⟶ Z；CategoryTheory.CategoryStruct.comp f g；CategoryTheory.Lim
its.image.preComp f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.epi_of_epi_fac`：epi_of_epi_fac {f : X ⟶ Y} {g : Y ⟶ Z} {h
 : X ⟶ Z} [Epi h] (w : f ≫ g = h) : Epi g
· 使用定理 `CategoryTheory.Limits.instEpiFactorThruImageOfHasLimitWalkingParallelPai
rParallelPair`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C
} (f : X ⟶ Y)   [inst_1 : CategoryTheory.Limits.HasImage f]   [∀ {Z : C} (g…
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.image.factorThruImage_preComp`：∀ {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y) {Z : C} (g : Y ⟶ Z) 
  [inst_1 : CategoryTheory.Limits.HasImag…

--- 原说明 ---
`image.preComp f g` is an epimorphism when `f` is an epimorphism
(we need `C` to have equalizers to prove this).
-/
instance image.preComp_epi_of_epi [HasImage g] [HasImage (f ≫ g)] [Epi f] :
    Epi (image.preComp f g) := by
  apply @epi_of_epi_fac _ _ _ _ _ _ _ _ ?_ (image.factorThruImage_preComp _ _)
  exact epi_comp _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Limits.hasImage_iso_comp** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory.Limits`。
形式化陈述：hasImage_iso_comp [IsIso f] [HasImage g] : HasImage (f ≫ g)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasImage.mk`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] {X Y : C} {f : X ⟶ Y}   (F : CategoryTheory.Limits.ImageFact
orisation f), CategoryT…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.image.lift_fac`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {X Y : C} {f : X ⟶ Y}   [inst_1 : CategoryTheory.Limits.H
asImage f] (F' : CategoryT…
-/
instance hasImage_iso_comp [IsIso f] [HasImage g] : HasImage (f ≫ g) :=
  HasImage.mk
    { F := (Image.monoFactorisation g).isoComp f
      isImage := { lift := fun F' => image.lift (F'.ofIsoComp f)
                   lift_fac := fun F' => by
                    dsimp
                    have : (MonoFactorisation.ofIsoComp f F').m = F'.m := rfl
                    rw [← this, image.lift_fac (MonoFactorisation.ofIsoComp f F')] } }

/-- `image.preComp f g` is an isomorphism when `f` is an isomorphism
(we need `C` to have equalizers to prove this).
-/
/-
**CategoryTheory.Limits.image.isIso_precomp_iso** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Limits.image`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y Z : C} (g : 
Y ⟶ Z) [CategoryTheory.Limits.HasEqualizers C]   (f : X ⟶ Y) [inst_2 : CategoryT
heory.IsIso f] [inst_3 : CategoryTheory.Limits.HasImage g],   CategoryTheory.IsI
so (CategoryTheory.Limits.image.preComp f g)
参数：g : Y ⟶ Z；f : X ⟶ Y；CategoryTheory.Limits.image.preComp f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instMonoι`：∀ {C : Type u} [inst : CategoryTheory.C
ategory.{v, u} C] {X Y : C} (f : X ⟶ Y)   [inst_1 : CategoryTheory.Limits.HasIma
ge f], CategoryTheory…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.image.fac`：∀ {C : Type u} [inst : CategoryTheory.C
ategory.{v, u} C] {X Y : C} (f : X ⟶ Y)   [inst_1 : CategoryTheory.Limits.HasIma
ge f],   CategoryTheo…
· 使用定理 `CategoryTheory.IsIso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y) [I : CategoryTheory.IsIso f] {Z : 
C}   (h : Y ⟶ Z), CategoryT…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.image.ext`：∀ {C : Type u} [inst : CategoryTheory.C
ategory.{v, u} C] {X Y : C} (f : X ⟶ Y)   [inst_1 : CategoryTheory.Limits.HasIma
ge f] {W : C} {g h : …
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Limits.image.fac_lift_assoc`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] {X Y : C} {f : X ⟶ Y}   [inst_1 : CategoryTheory.Li
mits.HasImage f] (F' : CategoryT…
· 使用定理 `CategoryTheory.Limits.image.fac_lift`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {X Y : C} {f : X ⟶ Y}   [inst_1 : CategoryTheory.Limits.H
asImage f] (F' : CategoryT…
· 使用定理 `CategoryTheory.IsIso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y) [I : CategoryTheory.IsIso f] {Z : 
C}   (h : X ⟶ Z), CategoryT…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…

--- 原说明 ---
`image.preComp f g` is an isomorphism when `f` is an isomorphism
(we need `C` to have equalizers to prove this).
-/
instance image.isIso_precomp_iso (f : X ⟶ Y) [IsIso f] [HasImage g] : IsIso (image.preComp f g) :=
  ⟨⟨image.lift
        { I := image (f ≫ g)
          m := image.ι (f ≫ g)
          e := inv f ≫ factorThruImage (f ≫ g) },
      ⟨by
        ext
        simp [image.preComp], by
        ext
        simp [image.preComp]⟩⟩⟩

set_option backward.isDefEq.respectTransparency false in
-- Note that in general we don't have the other comparison map you might expect
-- `image f ⟶ image (f ≫ g)`.
/-
**CategoryTheory.Limits.hasImage_comp_iso** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory.Limits`。
形式化陈述：hasImage_comp_iso [HasImage f] [IsIso g] : HasImage (f ≫ g)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasImage.mk`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] {X Y : C} {f : X ⟶ Y}   (F : CategoryTheory.Limits.ImageFact
orisation f), CategoryT…
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.strongMono_of_isIso`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {P Q : C} (f : Q ⟶ P) [CategoryTheory.IsIso f],   CategoryT
heory.StrongMono f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.IsIso.inv_hom_id`：inv_hom_id (f : X ⟶ Y) [I : IsIso f] : 
inv f ≫ f = 𝟙 Y
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Limits.MonoFactorisation.ofCompIso_m`：∀ {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C] {X Y : C} {f : X ⟶ Y} {Y' : C} {g : Y ⟶ Y'
}   [inst_1 : CategoryTheory.IsIso g]   (…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.image.lift_fac`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {X Y : C} {f : X ⟶ Y}   [inst_1 : CategoryTheory.Limits.H
asImage f] (F' : CategoryT…
· 使用定理 `CategoryTheory.Limits.image.as_ι`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {X Y : C} (f : X ⟶ Y)   [inst_1 : CategoryTheory.Limits.HasIm
age f],   (CategoryThe…
-/
instance hasImage_comp_iso [HasImage f] [IsIso g] : HasImage (f ≫ g) :=
  HasImage.mk
    { F := (Image.monoFactorisation f).compMono g
      isImage :=
      { lift := fun F' => image.lift F'.ofCompIso
        lift_fac := fun F' => by
          rw [← Category.comp_id (image.lift (MonoFactorisation.ofCompIso F') ≫ F'.m),
            ← IsIso.inv_hom_id g, ← Category.assoc]
          refine congrArg (· ≫ g) ?_
          have : (image.lift (MonoFactorisation.ofCompIso F') ≫ F'.m) ≫ inv g =
            image.lift (MonoFactorisation.ofCompIso F') ≫
            ((MonoFactorisation.ofCompIso F').m) := by
              simp only [Category.assoc,
                MonoFactorisation.ofCompIso_m]
          rw [this, image.lift_fac (MonoFactorisation.ofCompIso F'), image.as_ι] } }

set_option backward.isDefEq.respectTransparency false in
/-- Postcomposing by an isomorphism induces an isomorphism on the image. -/
/-
**CategoryTheory.Limits.image.compIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Limits.image`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {X Y : C}
 →       (f : X ⟶ Y) →         {Z : C} →           (g : Y ⟶ Z) →             [Ca
tegoryTheory.Limits.HasEqualizers C] →               [inst_2 : CategoryTheory.Li
mits.HasImage f] →                 [inst_3 : CategoryTheory.IsIso g] →          
         CategoryTheory.Limits.image f ≅ CategoryTheory.Limits.image (CategoryTh
eory.CategoryStruct.comp f g)
参数：f : X ⟶ Y；g : Y ⟶ Z；CategoryTheory.CategoryStruct.comp f g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Postcomposing by an isomorphism induces an isomorphism on the image.
-/
def image.compIso [HasImage f] [IsIso g] : image f ≅ image (f ≫ g) where
  hom := image.lift (Image.monoFactorisation (f ≫ g)).ofCompIso
  inv := image.lift ((Image.monoFactorisation f).compMono g)

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.image.compIso_hom_comp_image_** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem image.compIso_hom_comp_image_ι [HasImage f] [IsIso g] :
    (image.compIso f g).hom ≫ image.ι (f ≫ g) = image.ι f ≫ g := by
  ext
  simp [image.compIso]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.image.compIso_inv_comp_image_** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem image.compIso_inv_comp_image_ι [HasImage f] [IsIso g] :
    (image.compIso f g).inv ≫ image.ι f = image.ι (f ≫ g) ≫ inv g := by
  ext
  simp [image.compIso]

end

end CategoryTheory.Limits

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]

section

/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y : C} (f : X ⟶ Y) [HasImage f] : HasImage (Arrow.mk f).hom :=
  inferInstanceAs <| HasImage f

end

section HasImageMap

/-- An image map is a morphism `image f → image g` fitting into a commutative square and satisfying
the obvious commutativity conditions. -/
/-
**CategoryTheory.Limits.ImageMap** 是 Mathlib 中的一个结构，位于命名空间 `CategoryTheory.Limit
s`。
形式化陈述：ImageMap {f g : Arrow C} [HasImage f.hom] [HasImage g.hom] (sq : f ⟶ g) wh
ere map : image f.hom ⟶ image g.hom map_ι : map ≫ image.ι g.hom = image.ι f.hom 
≫ sq.right
参数：sq : f ⟶ g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An image map is a morphism `image f → image g` fitting into a commutative square
 and satisfying
the obvious commutativity conditions.
-/
structure ImageMap {f g : Arrow C} [HasImage f.hom] [HasImage g.hom] (sq : f ⟶ g) where
  map : image f.hom ⟶ image g.hom
  map_ι : map ≫ image.ι g.hom = image.ι f.hom ≫ sq.right := by aesop

attribute [inherit_doc ImageMap] ImageMap.map ImageMap.map_ι
/-
**CategoryTheory.Limits.inhabitedImageMap** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory.Limits`。
形式化陈述：inhabitedImageMap {f : Arrow C} [HasImage f.hom] : Inhabited (ImageMap (𝟙 
f))
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance inhabitedImageMap {f : Arrow C} [HasImage f.hom] : Inhabited (ImageMap (𝟙 f)) :=
  ⟨⟨𝟙 _, by simp⟩⟩

attribute [reassoc (attr := simp)] ImageMap.map_ι

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.ImageMap.factor_map** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Limits.ImageMap`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {f g : CategoryTh
eory.Arrow C}   [inst_1 : CategoryTheory.Limits.HasImage f.hom] [inst_2 : Catego
ryTheory.Limits.HasImage g.hom] (sq : f ⟶ g)   (m : CategoryTheory.Limits.ImageM
ap sq),   CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.factorThruIm
age f.hom) m.map =     CategoryTheory.CategoryStruct.comp (CategoryTheory.Arrow.
Hom.left sq) (CategoryTheory.Limits.factorThruImage g.hom)
参数：sq : f ⟶ g；m : CategoryTheory.Limits.ImageMap sq；CategoryTheory.Limits.factor
ThruImage f.hom；CategoryTheory.Arrow.Hom.left sq；CategoryTheory.Limits.factorThr
uImage g.hom。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.Limits.instMonoι`：∀ {C : Type u} [inst : CategoryTheory.C
ategory.{v, u} C] {X Y : C} (f : X ⟶ Y)   [inst_1 : CategoryTheory.Limits.HasIma
ge f], CategoryTheory…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.ImageMap.map_ι`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {f g : CategoryTheory.Arrow C}   [inst_1 : CategoryTheory
.Limits.HasImage f.hom] [i…
· 使用定理 `CategoryTheory.Limits.image.fac_assoc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y)   [inst_1 : CategoryTheory.Limits.
HasImage f] {Z : C} (h : Y …
· 使用定理 `CategoryTheory.Limits.image.fac`：∀ {C : Type u} [inst : CategoryTheory.C
ategory.{v, u} C] {X Y : C} (f : X ⟶ Y)   [inst_1 : CategoryTheory.Limits.HasIma
ge f],   CategoryTheo…
· 使用定理 `CategoryTheory.Arrow.w`：w {f g : Arrow T} (sq : f ⟶ g) : sq.left ≫ g.hom
 = f.hom ≫ sq.right
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ImageMap.factor_map {f g : Arrow C} [HasImage f.hom] [HasImage g.hom] (sq : f ⟶ g)
    (m : ImageMap sq) : factorThruImage f.hom ≫ m.map = sq.left ≫ factorThruImage g.hom :=
  (cancel_mono (image.ι g.hom)).1 <| by simp

set_option backward.isDefEq.respectTransparency false in
/-- To give an image map for a commutative square with `f` at the top and `g` at the bottom, it
suffices to give a map between any mono factorisation of `f` and any image factorisation of `g`. -/
/-
**CategoryTheory.Limits.ImageMap.transport** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Limits.ImageMap`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {f g : Ca
tegoryTheory.Arrow C} →       [inst_1 : CategoryTheory.Limits.HasImage f.hom] → 
        [inst_2 : CategoryTheory.Limits.HasImage g.hom] →           (sq : f ⟶ g)
 →             (F : CategoryTheory.Limits.MonoFactorisation f.hom) →            
   {F' : CategoryTheory.Limits.MonoFactorisation g.hom} →                 Catego
ryTheory.Limits.IsImage F' →                   {map : F.I ⟶ F'.I} →             
        CategoryTheory.CategoryStruct.comp map F'.m =                         Ca
tegoryTheory.CategoryStruct.comp F.m (CategoryTheory.Arrow.Hom.right sq) →      
                 CategoryTheory.Limits.ImageMap sq
参数：sq : f ⟶ g；F : CategoryTheory.Limits.MonoFactorisation f.hom；CategoryTheory.A
rrow.Hom.right sq。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
To give an image map for a commutative square with `f` at the top and `g` at the
 bottom, it
suffices to give a map between any mono factorisation of `f` and any image facto
risation of `g`.
-/
def ImageMap.transport {f g : Arrow C} [HasImage f.hom] [HasImage g.hom] (sq : f ⟶ g)
    (F : MonoFactorisation f.hom) {F' : MonoFactorisation g.hom} (hF' : IsImage F')
    {map : F.I ⟶ F'.I} (map_ι : map ≫ F'.m = F.m ≫ sq.right) : ImageMap sq where
  map := image.lift F ≫ map ≫ hF'.lift (Image.monoFactorisation g.hom)
  map_ι := by simp [map_ι]

/-- `HasImageMap sq` means that there is an `ImageMap` for the square `sq`. -/
/-
**CategoryTheory.Limits.HasImageMap** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory.
Limits`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {f g : Ca
tegoryTheory.Arrow C} →       [CategoryTheory.Limits.HasImage f.hom] → [Category
Theory.Limits.HasImage g.hom] → (f ⟶ g) → Prop
参数：f ⟶ g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`HasImageMap sq` means that there is an `ImageMap` for the square `sq`.
-/
class HasImageMap {f g : Arrow C} [HasImage f.hom] [HasImage g.hom] (sq : f ⟶ g) : Prop where
mk' ::
  has_image_map : Nonempty (ImageMap sq)

attribute [inherit_doc HasImageMap] HasImageMap.has_image_map
/-
**CategoryTheory.Limits.HasImageMap.mk** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Limits.HasImageMap`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {f g : CategoryTh
eory.Arrow C}   [inst_1 : CategoryTheory.Limits.HasImage f.hom] [inst_2 : Catego
ryTheory.Limits.HasImage g.hom] {sq : f ⟶ g}   (m : CategoryTheory.Limits.ImageM
ap sq), CategoryTheory.Limits.HasImageMap sq
参数：m : CategoryTheory.Limits.ImageMap sq。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem HasImageMap.mk {f g : Arrow C} [HasImage f.hom] [HasImage g.hom] {sq : f ⟶ g}
    (m : ImageMap sq) : HasImageMap sq :=
  ⟨Nonempty.intro m⟩
/-
**CategoryTheory.Limits.HasImageMap.transport** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Limits.HasImageMap`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {f g : CategoryTh
eory.Arrow C}   [inst_1 : CategoryTheory.Limits.HasImage f.hom] [inst_2 : Catego
ryTheory.Limits.HasImage g.hom] (sq : f ⟶ g)   (F : CategoryTheory.Limits.MonoFa
ctorisation f.hom) {F' : CategoryTheory.Limits.MonoFactorisation g.hom}   (hF' :
 CategoryTheory.Limits.IsImage F') (map : F.I ⟶ F'.I),   CategoryTheory.Category
Struct.comp map F'.m =       CategoryTheory.CategoryStruct.comp F.m (CategoryThe
ory.Arrow.Hom.right sq) →     CategoryTheory.Limits.HasImageMap sq
参数：sq : f ⟶ g；F : CategoryTheory.Limits.MonoFactorisation f.hom；hF' : CategoryTh
eory.Limits.IsImage F'；map : F.I ⟶ F'.I；CategoryTheory.Arrow.Hom.right sq。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasImageMap.mk`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {f g : CategoryTheory.Arrow C}   [inst_1 : CategoryTheory
.Limits.HasImage f.hom] [i…
-/
theorem HasImageMap.transport {f g : Arrow C} [HasImage f.hom] [HasImage g.hom] (sq : f ⟶ g)
    (F : MonoFactorisation f.hom) {F' : MonoFactorisation g.hom} (hF' : IsImage F')
    (map : F.I ⟶ F'.I) (map_ι : map ≫ F'.m = F.m ≫ sq.right) : HasImageMap sq :=
  HasImageMap.mk <| ImageMap.transport sq F hF' map_ι

/-- Obtain an `ImageMap` from a `HasImageMap` instance. -/
/-
**CategoryTheory.Limits.HasImageMap.imageMap** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Limits.HasImageMap`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {f g : Ca
tegoryTheory.Arrow C} →       [inst_1 : CategoryTheory.Limits.HasImage f.hom] → 
        [inst_2 : CategoryTheory.Limits.HasImage g.hom] →           (sq : f ⟶ g)
 → [CategoryTheory.Limits.HasImageMap sq] → CategoryTheory.Limits.ImageMap sq
参数：sq : f ⟶ g。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasImageMap.has_image_map`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {f g : CategoryTheory.Arrow C}   {inst_1 : Cat
egoryTheory.Limits.HasImage f.hom} {i…

--- 原说明 ---
Obtain an `ImageMap` from a `HasImageMap` instance.
-/
def HasImageMap.imageMap {f g : Arrow C} [HasImage f.hom] [HasImage g.hom] (sq : f ⟶ g)
    [HasImageMap sq] : ImageMap sq :=
  Classical.choice <| @HasImageMap.has_image_map _ _ _ _ _ _ sq _

-- see Note [lower instance priority]
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) hasImageMapOfIsIso {f g : Arrow C} [HasImage f.hom] [HasImage g.hom]
    (sq : f ⟶ g) [IsIso sq] : HasImageMap sq :=
  HasImageMap.mk
    { map := image.lift ((Image.monoFactorisation g.hom).ofArrowIso (inv sq))
      map_ι := by
        erw [← cancel_mono (inv sq).right, Category.assoc, ← MonoFactorisation.ofArrowIso_m,
          image.lift_fac, Category.assoc, ← Comma.comp_right, IsIso.hom_inv_id, Comma.id_right,
          Category.comp_id] }
/-
**CategoryTheory.Limits.HasImageMap.comp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Limits.HasImageMap`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {f g h : Category
Theory.Arrow C}   [inst_1 : CategoryTheory.Limits.HasImage f.hom] [inst_2 : Cate
goryTheory.Limits.HasImage g.hom]   [inst_3 : CategoryTheory.Limits.HasImage h.h
om] (sq1 : f ⟶ g) (sq2 : g ⟶ h) [CategoryTheory.Limits.HasImageMap sq1]   [Categ
oryTheory.Limits.HasImageMap sq2],   CategoryTheory.Limits.HasImageMap (Category
Theory.CategoryStruct.comp sq1 sq2)
参数：sq1 : f ⟶ g；sq2 : g ⟶ h；CategoryTheory.CategoryStruct.comp sq1 sq2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasImageMap.mk`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {f g : CategoryTheory.Arrow C}   [inst_1 : CategoryTheory
.Limits.HasImage f.hom] [i…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.ImageMap.map_ι`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {f g : CategoryTheory.Arrow C}   [inst_1 : CategoryTheory
.Limits.HasImage f.hom] [i…
· 使用定理 `CategoryTheory.Limits.ImageMap.map_ι_assoc`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] {f g : CategoryTheory.Arrow C}   [inst_1 : Category
Theory.Limits.HasImage f.hom] [i…
· 使用定理 `CategoryTheory.Arrow.comp_right`：∀ {T : Type u} [inst : CategoryTheory.C
ategory.{v, u} T] {X Y Z : CategoryTheory.Arrow T} (g : Z ⟶ Y) (f : Y ⟶ X),   Ca
tegoryTheory.Arrow.Ho…
-/
instance HasImageMap.comp {f g h : Arrow C} [HasImage f.hom] [HasImage g.hom] [HasImage h.hom]
    (sq1 : f ⟶ g) (sq2 : g ⟶ h) [HasImageMap sq1] [HasImageMap sq2] : HasImageMap (sq1 ≫ sq2) :=
  HasImageMap.mk
    { map := (HasImageMap.imageMap sq1).map ≫ (HasImageMap.imageMap sq2).map
      map_ι := by
        rw [Category.assoc, ImageMap.map_ι, ImageMap.map_ι_assoc, Arrow.comp_right] }

variable {f g : Arrow C} [HasImage f.hom] [HasImage g.hom] (sq : f ⟶ g)

section

attribute [local ext] ImageMap

/-
**CategoryTheory.Limits.ImageMap.map_uniq_aux** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Limits.ImageMap`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {f g : CategoryTh
eory.Arrow C}   [inst_1 : CategoryTheory.Limits.HasImage f.hom] [inst_2 : Catego
ryTheory.Limits.HasImage g.hom] {sq : f ⟶ g}   (map : CategoryTheory.Limits.imag
e f.hom ⟶ CategoryTheory.Limits.image g.hom),   autoParam       (CategoryTheory.
CategoryStruct.comp map (CategoryTheory.Limits.image.ι g.hom) =         Category
Theory.CategoryStruct.comp (CategoryTheory.Limits.image.ι f.hom) (CategoryTheory
.Arrow.Hom.right sq))       CategoryTheory.Limits.ImageMap.map_uniq_aux._auto_1 
→     ∀ (map' : CategoryTheory.Limits.image f.hom ⟶ CategoryTheory.Limits.image 
g.hom),       CategoryTheory.CategoryStruct.comp map' (CategoryTheory.Limits.ima
ge.ι g.hom) =           CategoryTheory.CategoryStruct.comp (CategoryTheory.Limit
s.image.ι f.hom) (CategoryTheory.Arrow.Hom.right sq) →         map = map'
参数：map : CategoryTheory.Limits.image f.hom ⟶ CategoryTheory.Limits.image g.hom；C
ategoryTheory.CategoryStruct.comp map (CategoryTheory.Limits.image.ι g.hom) =   
      CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.image.ι f.hom) (
CategoryTheory.Arrow.Hom.right sq)；map' : CategoryTheory.Limits.image f.hom ⟶ Ca
tegoryTheory.Limits.image g.hom；CategoryTheory.Limits.image.ι g.hom；CategoryTheo
ry.Limits.image.ι f.hom；CategoryTheory.Arrow.Hom.right sq。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.Limits.instMonoι`：∀ {C : Type u} [inst : CategoryTheory.C
ategory.{v, u} C] {X Y : C} (f : X ⟶ Y)   [inst_1 : CategoryTheory.Limits.HasIma
ge f], CategoryTheory…
-/
theorem ImageMap.map_uniq_aux {f g : Arrow C} [HasImage f.hom] [HasImage g.hom] {sq : f ⟶ g}
    (map : image f.hom ⟶ image g.hom)
    (map_ι : map ≫ image.ι g.hom = image.ι f.hom ≫ sq.right := by cat_disch)
    (map' : image f.hom ⟶ image g.hom)
    (map_ι' : map' ≫ image.ι g.hom = image.ι f.hom ≫ sq.right) : (map = map') := by
  have : map ≫ image.ι g.hom = map' ≫ image.ι g.hom := by rw [map_ι, map_ι']
  apply (cancel_mono (image.ι g.hom)).1 this
/-
**CategoryTheory.Limits.ImageMap.map_uniq** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Limits.ImageMap`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {f g : CategoryTh
eory.Arrow C}   [inst_1 : CategoryTheory.Limits.HasImage f.hom] [inst_2 : Catego
ryTheory.Limits.HasImage g.hom] {sq : f ⟶ g}   (F G : CategoryTheory.Limits.Imag
eMap sq), F.map = G.map
参数：F G : CategoryTheory.Limits.ImageMap sq。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.ImageMap.map_uniq_aux`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {f g : CategoryTheory.Arrow C}   [inst_1 : Categor
yTheory.Limits.HasImage f.hom] [i…
· 使用定理 `CategoryTheory.Limits.ImageMap.map_ι`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {f g : CategoryTheory.Arrow C}   [inst_1 : CategoryTheory
.Limits.HasImage f.hom] [i…
-/
theorem ImageMap.map_uniq {f g : Arrow C} [HasImage f.hom] [HasImage g.hom]
    {sq : f ⟶ g} (F G : ImageMap sq) : F.map = G.map := by
  apply ImageMap.map_uniq_aux _ F.map_ι _ G.map_ι

@[deprecated (since := "2026-04-08")]
alias ImageMap.mk.injEq' := ImageMap.mk.injEq
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Subsingleton (ImageMap sq) :=
  Subsingleton.intro fun a b =>
    ImageMap.ext <| ImageMap.map_uniq a b

end

variable [HasImageMap sq]

/-- The map on images induced by a commutative square. -/
/-
**CategoryTheory.Limits.image.map** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limi
ts.image`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {f g : Ca
tegoryTheory.Arrow C} →       [inst_1 : CategoryTheory.Limits.HasImage f.hom] → 
        [inst_2 : CategoryTheory.Limits.HasImage g.hom] →           (sq : f ⟶ g)
 →             [CategoryTheory.Limits.HasImageMap sq] →               CategoryTh
eory.Limits.image f.hom ⟶ CategoryTheory.Limits.image g.hom
参数：sq : f ⟶ g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map on images induced by a commutative square.
-/
abbrev image.map : image f.hom ⟶ image g.hom :=
  (HasImageMap.imageMap sq).map
/-
**CategoryTheory.Limits.image.factor_map** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Limits.image`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {f g : CategoryTh
eory.Arrow C}   [inst_1 : CategoryTheory.Limits.HasImage f.hom] [inst_2 : Catego
ryTheory.Limits.HasImage g.hom] (sq : f ⟶ g)   [inst_3 : CategoryTheory.Limits.H
asImageMap sq],   CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.fact
orThruImage f.hom)       (CategoryTheory.Limits.image.map sq) =     CategoryTheo
ry.CategoryStruct.comp (CategoryTheory.Arrow.Hom.left sq) (CategoryTheory.Limits
.factorThruImage g.hom)
参数：sq : f ⟶ g；CategoryTheory.Limits.factorThruImage f.hom；CategoryTheory.Limits.
image.map sq；CategoryTheory.Arrow.Hom.left sq；CategoryTheory.Limits.factorThruIm
age g.hom。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.ImageMap.factor_map`：∀ {C : Type u} [inst : Catego
ryTheory.Category.{v, u} C] {f g : CategoryTheory.Arrow C}   [inst_1 : CategoryT
heory.Limits.HasImage f.hom] [i…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem image.factor_map :
    factorThruImage f.hom ≫ image.map sq = sq.left ≫ factorThruImage g.hom := by simp
/-
**CategoryTheory.Limits.image.map_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Lim
its`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem image.map_ι : image.map sq ≫ image.ι g.hom = image.ι f.hom ≫ sq.right := by simp
/-
**CategoryTheory.Limits.image.map_homMk'_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem image.map_homMk'_ι {X Y P Q : C} {k : X ⟶ Y} [HasImage k] {l : P ⟶ Q} [HasImage l]
    {m : X ⟶ P} {n : Y ⟶ Q} (w : m ≫ l = k ≫ n) [HasImageMap (Arrow.homMk' _ _ w)] :
    image.map (Arrow.homMk' _ _ w) ≫ image.ι l = image.ι k ≫ n :=
  image.map_ι _

section

variable {h : Arrow C} [HasImage h.hom] (sq' : g ⟶ h)
variable [HasImageMap sq']

/-- Image maps for composable commutative squares induce an image map in the composite square. -/
/-
**CategoryTheory.Limits.imageMapComp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.L
imits`。
形式化陈述：imageMapComp : ImageMap (sq ≫ sq') where map
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Image maps for composable commutative squares induce an image map in the composi
te square.
-/
def imageMapComp : ImageMap (sq ≫ sq') where map := image.map sq ≫ image.map sq'

@[simp]
/-
**CategoryTheory.Limits.image.map_comp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Limits.image`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {f g : CategoryTh
eory.Arrow C}   [inst_1 : CategoryTheory.Limits.HasImage f.hom] [inst_2 : Catego
ryTheory.Limits.HasImage g.hom] (sq : f ⟶ g)   [inst_3 : CategoryTheory.Limits.H
asImageMap sq] {h : CategoryTheory.Arrow C}   [inst_4 : CategoryTheory.Limits.Ha
sImage h.hom] (sq' : g ⟶ h) [inst_5 : CategoryTheory.Limits.HasImageMap sq']   [
inst_6 : CategoryTheory.Limits.HasImageMap (CategoryTheory.CategoryStruct.comp s
q sq')],   CategoryTheory.Limits.image.map (CategoryTheory.CategoryStruct.comp s
q sq') =     CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.image.map
 sq) (CategoryTheory.Limits.image.map sq')
参数：sq : f ⟶ g；sq' : g ⟶ h；CategoryTheory.CategoryStruct.comp sq sq'；CategoryTheo
ry.CategoryStruct.comp sq sq'；CategoryTheory.Limits.image.map sq；CategoryTheory.
Limits.image.map sq'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Limits.instSubsingletonImageMap`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] {f g : CategoryTheory.Arrow C}   [inst_1 : Cate
goryTheory.Limits.HasImage f.hom] [i…
-/
theorem image.map_comp [HasImageMap (sq ≫ sq')] :
    image.map (sq ≫ sq') = image.map sq ≫ image.map sq' :=
  show (HasImageMap.imageMap (sq ≫ sq')).map = (imageMapComp sq sq').map by
    congr; simp only [eq_iff_true_of_subsingleton]

end

section

variable (f)

/-- The identity `image f ⟶ image f` fits into the commutative square represented by the identity
morphism `𝟙 f` in the arrow category. -/
/-
**CategoryTheory.Limits.imageMapId** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Lim
its`。
形式化陈述：imageMapId : ImageMap (𝟙 f) where map
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity `image f ⟶ image f` fits into the commutative square represented by
 the identity
morphism `𝟙 f` in the arrow category.
-/
def imageMapId : ImageMap (𝟙 f) where map := 𝟙 (image f.hom)

@[simp]
/-
**CategoryTheory.Limits.image.map_id** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.L
imits.image`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (f : CategoryTheo
ry.Arrow C)   [inst_1 : CategoryTheory.Limits.HasImage f.hom]   [inst_2 : Catego
ryTheory.Limits.HasImageMap (CategoryTheory.CategoryStruct.id f)],   CategoryThe
ory.Limits.image.map (CategoryTheory.CategoryStruct.id f) =     CategoryTheory.C
ategoryStruct.id (CategoryTheory.Limits.image f.hom)
参数：f : CategoryTheory.Arrow C；CategoryTheory.CategoryStruct.id f；CategoryTheory.
CategoryStruct.id f；CategoryTheory.Limits.image f.hom。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Limits.instSubsingletonImageMap`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] {f g : CategoryTheory.Arrow C}   [inst_1 : Cate
goryTheory.Limits.HasImage f.hom] [i…
-/
theorem image.map_id [HasImageMap (𝟙 f)] : image.map (𝟙 f) = 𝟙 (image f.hom) :=
  show (HasImageMap.imageMap (𝟙 f)).map = (imageMapId f).map by
    congr; simp only [eq_iff_true_of_subsingleton]

end

end HasImageMap

section

variable (C) [HasImages C]

/-- If a category `HasImageMaps`, then all commutative squares induce morphisms on images. -/
/-
**CategoryTheory.Limits.HasImageMaps** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory
.Limits`。
形式化陈述：(C : Type u) → [inst : CategoryTheory.Category.{v, u} C] → [CategoryTheory
.Limits.HasImages C] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a category `HasImageMaps`, then all commutative squares induce morphisms on i
mages.
-/
class HasImageMaps : Prop where
  has_image_map : ∀ {f g : Arrow C} (st : f ⟶ g), HasImageMap st

attribute [instance 100] HasImageMaps.has_image_map

end

section HasImageMaps

variable [HasImages C] [HasImageMaps C]

/-- The functor from the arrow category of `C` to `C` itself that maps a morphism to its image
and a commutative square to the induced morphism on images. -/
@[simps]
/-
**CategoryTheory.Limits.im** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：im : Arrow C ⥤ C where obj f
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasImageMaps.has_image_map`：∀ {C : Type u} {inst :
 CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasImages C} 
  [self : CategoryTheory.Limits.HasIma…

--- 原说明 ---
The functor from the arrow category of `C` to `C` itself that maps a morphism to
 its image
and a commutative square to the induced morphism on images.
-/
def im : Arrow C ⥤ C where
  obj f := image f.hom
  map st := image.map st

end HasImageMaps

section StrongEpiMonoFactorisation

/-- A strong epi-mono factorisation is a decomposition `f = e ≫ m` with `e` a strong epimorphism
and `m` a monomorphism. -/
/-
**CategoryTheory.Limits.StrongEpiMonoFactorisation** 是 Mathlib 中的一个归纳类型，位于命名空间 `
CategoryTheory.Limits`。
形式化陈述：{C : Type u} → [inst : CategoryTheory.Category.{v, u} C] → {X Y : C} → (X 
⟶ Y) → Type (max u v)
参数：X ⟶ Y；max u v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A strong epi-mono factorisation is a decomposition `f = e ≫ m` with `e` a strong
 epimorphism
and `m` a monomorphism.
-/
structure StrongEpiMonoFactorisation {X Y : C} (f : X ⟶ Y) extends MonoFactorisation f where
  [e_strong_epi : StrongEpi e]

attribute [inherit_doc StrongEpiMonoFactorisation] StrongEpiMonoFactorisation.e_strong_epi

attribute [instance] StrongEpiMonoFactorisation.e_strong_epi

/-- Satisfying the inhabited linter -/
/-
**CategoryTheory.Limits.strongEpiMonoFactorisationInhabited** 是 Mathlib 中的一个实例，位
于命名空间 `CategoryTheory.Limits`。
形式化陈述：strongEpiMonoFactorisationInhabited {X Y : C} (f : X ⟶ Y) [StrongEpi f] : 
Inhabited (StrongEpiMonoFactorisation f)
参数：f : X ⟶ Y。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.instMonoId`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] (X : C),   CategoryTheory.Mono (CategoryTheory.CategoryStruct.id X)

--- 原说明 ---
Satisfying the inhabited linter
-/
instance strongEpiMonoFactorisationInhabited {X Y : C} (f : X ⟶ Y) [StrongEpi f] :
    Inhabited (StrongEpiMonoFactorisation f) :=
  ⟨⟨⟨Y, 𝟙 Y, f, by simp⟩⟩⟩

/-- A mono factorisation coming from a strong epi-mono factorisation always has the universal
property of the image. -/
/-
**CategoryTheory.Limits.StrongEpiMonoFactorisation.toMonoIsImage** 是 Mathlib 中的一
个定义，位于命名空间 `CategoryTheory.Limits.StrongEpiMonoFactorisation`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {X Y : C}
 →       {f : X ⟶ Y} →         (F : CategoryTheory.Limits.StrongEpiMonoFactorisa
tion f) → CategoryTheory.Limits.IsImage F.toMonoFactorisation
参数：F : CategoryTheory.Limits.StrongEpiMonoFactorisation f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A mono factorisation coming from a strong epi-mono factorisation always has the 
universal
property of the image.
-/
def StrongEpiMonoFactorisation.toMonoIsImage {X Y : C} {f : X ⟶ Y}
    (F : StrongEpiMonoFactorisation f) : IsImage F.toMonoFactorisation where
  lift G :=
    (CommSq.mk (show G.e ≫ G.m = F.e ≫ F.m by rw [F.toMonoFactorisation.fac, G.fac])).lift

variable (C)

/-- A category has strong epi-mono factorisations if every morphism admits a strong epi-mono
factorisation. -/
/-
**CategoryTheory.Limits.HasStrongEpiMonoFactorisations** 是 Mathlib 中的一个归纳类型，位于命名
空间 `CategoryTheory.Limits`。
形式化陈述：(C : Type u) → [CategoryTheory.Category.{v, u} C] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A category has strong epi-mono factorisations if every morphism admits a strong 
epi-mono
factorisation.
-/
class HasStrongEpiMonoFactorisations : Prop where mk' ::
  has_fac : ∀ {X Y : C} (f : X ⟶ Y), Nonempty (StrongEpiMonoFactorisation f)

attribute [inherit_doc HasStrongEpiMonoFactorisations] HasStrongEpiMonoFactorisations.has_fac

variable {C}
/-
**CategoryTheory.Limits.HasStrongEpiMonoFactorisations.mk** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.Limits.HasStrongEpiMonoFactorisations`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C]   (d : {X Y : C} 
→ (f : X ⟶ Y) → CategoryTheory.Limits.StrongEpiMonoFactorisation f),   CategoryT
heory.Limits.HasStrongEpiMonoFactorisations C
参数：d : {X Y : C} → (f : X ⟶ Y) → CategoryTheory.Limits.StrongEpiMonoFactorisatio
n f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem HasStrongEpiMonoFactorisations.mk
    (d : ∀ {X Y : C} (f : X ⟶ Y), StrongEpiMonoFactorisation f) :
    HasStrongEpiMonoFactorisations C :=
  ⟨fun f => Nonempty.intro <| d f⟩
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) hasImages_of_hasStrongEpiMonoFactorisations
    [HasStrongEpiMonoFactorisations C] : HasImages C where
  has_image f :=
    let F' := Classical.choice (HasStrongEpiMonoFactorisations.has_fac f)
    HasImage.mk
      { F := F'.toMonoFactorisation
        isImage := F'.toMonoIsImage }

end StrongEpiMonoFactorisation

section HasStrongEpiImages

variable (C) [HasImages C]

/-- A category has strong epi images if it has all images and `factorThruImage f` is a strong
epimorphism for all `f`. -/
/-
**CategoryTheory.Limits.HasStrongEpiImages** 是 Mathlib 中的一个归纳类型，位于命名空间 `Category
Theory.Limits`。
形式化陈述：(C : Type u) → [inst : CategoryTheory.Category.{v, u} C] → [CategoryTheory
.Limits.HasImages C] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A category has strong epi images if it has all images and `factorThruImage f` is
 a strong
epimorphism for all `f`.
-/
class HasStrongEpiImages : Prop where
  strong_factorThruImage : ∀ {X Y : C} (f : X ⟶ Y), StrongEpi (factorThruImage f)

attribute [instance] HasStrongEpiImages.strong_factorThruImage

end HasStrongEpiImages

section HasStrongEpiImages

/-- If there is a single strong epi-mono factorisation of `f`, then every image factorisation is a
strong epi-mono factorisation. -/
/-
**CategoryTheory.Limits.strongEpi_of_strongEpiMonoFactorisation** 是 Mathlib 中的一个
定理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：strongEpi_of_strongEpiMonoFactorisation {X Y : C} {f : X ⟶ Y} (F : StrongE
piMonoFactorisation f) {F' : MonoFactorisation f} (hF' : IsImage F') : StrongEpi
 F'.e
参数：F : StrongEpiMonoFactorisation f；hF' : IsImage F'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.IsImage.e_isoExt_hom`：e_isoExt_hom : F.e ≫ (isoExt
 hF hF').hom = F'.e
· 使用定理 `CategoryTheory.Limits.StrongEpiMonoFactorisation.e_strong_epi`：∀ {C : Ty
pe u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} {f : X ⟶ Y}   (self : 
CategoryTheory.Limits.StrongEpiMonoFactorisation f)…
· 使用定理 `CategoryTheory.strongEpi_of_isIso`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] {P Q : C} (f : P ⟶ Q) [CategoryTheory.IsIso f],   CategoryTh
eory.StrongEpi f
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom

--- 原说明 ---
If there is a single strong epi-mono factorisation of `f`, then every image fact
orisation is a
strong epi-mono factorisation.
-/
theorem strongEpi_of_strongEpiMonoFactorisation {X Y : C} {f : X ⟶ Y}
    (F : StrongEpiMonoFactorisation f) {F' : MonoFactorisation f} (hF' : IsImage F') :
    StrongEpi F'.e := by
  rw [← IsImage.e_isoExt_hom F.toMonoIsImage hF']
  apply strongEpi_comp
/-
**CategoryTheory.Limits.strongEpi_factorThruImage_of_strongEpiMonoFactorisation*
* 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：strongEpi_factorThruImage_of_strongEpiMonoFactorisation {X Y : C} {f : X ⟶
 Y} [HasImage f] (F : StrongEpiMonoFactorisation f) : StrongEpi (factorThruImage
 f)
参数：F : StrongEpiMonoFactorisation f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.strongEpi_of_strongEpiMonoFactorisation`：strongEpi
_of_strongEpiMonoFactorisation {X Y : C} {f : X ⟶ Y} (F : StrongEpiMonoFactorisa
tion f) {F' : MonoFactorisation f} (hF' : IsImage F…
-/
theorem strongEpi_factorThruImage_of_strongEpiMonoFactorisation {X Y : C} {f : X ⟶ Y} [HasImage f]
    (F : StrongEpiMonoFactorisation f) : StrongEpi (factorThruImage f) :=
  strongEpi_of_strongEpiMonoFactorisation F <| Image.isImage f

/-- If we constructed our images from strong epi-mono factorisations, then these images are
strong epi images. -/
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If we constructed our images from strong epi-mono factorisations, then these ima
ges are
strong epi images.
-/
instance (priority := 100) hasStrongEpiImages_of_hasStrongEpiMonoFactorisations
    [HasStrongEpiMonoFactorisations C] : HasStrongEpiImages C where
  strong_factorThruImage f :=
    strongEpi_factorThruImage_of_strongEpiMonoFactorisation <|
      Classical.choice <| HasStrongEpiMonoFactorisations.has_fac f

end HasStrongEpiImages

section HasStrongEpiImages

variable [HasImages C]

/-- A category with strong epi images has image maps. -/
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A category with strong epi images has image maps.
-/
instance (priority := 100) hasImageMapsOfHasStrongEpiImages [HasStrongEpiImages C] :
    HasImageMaps C where
  has_image_map {f} {g} st :=
    HasImageMap.mk
      { map :=
          (CommSq.mk
              (show
                (st.left ≫ factorThruImage g.hom) ≫ image.ι g.hom =
                  factorThruImage f.hom ≫ image.ι f.hom ≫ st.right
                by simp)).lift }

set_option backward.isDefEq.respectTransparency false in
/-- If a category has images, equalizers and pullbacks, then images are automatically strong epi
images. -/
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a category has images, equalizers and pullbacks, then images are automaticall
y strong epi
images.
-/
instance (priority := 100) hasStrongEpiImages_of_hasPullbacks_of_hasEqualizers [HasPullbacks C]
    [HasEqualizers C] : HasStrongEpiImages C where
  strong_factorThruImage f :=
    StrongEpi.mk' fun {A} {B} h h_mono x y sq =>
      CommSq.HasLift.mk'
        { l :=
            image.lift
                { I := pullback h y
                  m := pullback.snd h y ≫ image.ι f
                  m_mono := mono_comp _ _
                  e := pullback.lift _ _ sq.w } ≫
              pullback.fst h y
          fac_left := by simp only [image.fac_lift_assoc, pullback.lift_fst]
          fac_right := by
            apply image.ext
            simp only [sq.w, Category.assoc, image.fac_lift_assoc, pullback.lift_fst_assoc] }

end HasStrongEpiImages

variable [HasStrongEpiMonoFactorisations C]
variable {X Y : C} {f : X ⟶ Y}

/--
If `C` has strong epi mono factorisations, then the image is unique up to isomorphism, in that if
`f` factors as a strong epi followed by a mono, this factorisation is essentially the image
factorisation.
-/
/-
**CategoryTheory.Limits.image.isoStrongEpiMono** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Limits.image`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Limits.HasStrongEpiMonoFactorisations C] →       {X Y : C} →    
     {f : X ⟶ Y} →           {I' : C} →             (e : X ⟶ I') →              
 (m : I' ⟶ Y) →                 CategoryTheory.CategoryStruct.comp e m = f →    
               [CategoryTheory.StrongEpi e] → [CategoryTheory.Mono m] → I' ≅ Cat
egoryTheory.Limits.image f
参数：e : X ⟶ I'；m : I' ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `C` has strong epi mono factorisations, then the image is unique up to isomor
phism, in that if
`f` factors as a strong epi followed by a mono, this factorisation is essentiall
y the image
factorisation.
-/
def image.isoStrongEpiMono {I' : C} (e : X ⟶ I') (m : I' ⟶ Y) (comm : e ≫ m = f) [StrongEpi e]
    [Mono m] : I' ≅ image f :=
  let F : StrongEpiMonoFactorisation f := { I := I', m := m, e := e }
  IsImage.isoExt F.toMonoIsImage <| Image.isImage f

set_option backward.defeqAttrib.useBackward true in
@[simp]
/-
**CategoryTheory.Limits.image.isoStrongEpiMono_hom_comp_** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem image.isoStrongEpiMono_hom_comp_ι {I' : C} (e : X ⟶ I') (m : I' ⟶ Y) (comm : e ≫ m = f)
    [StrongEpi e] [Mono m] : (image.isoStrongEpiMono e m comm).hom ≫ image.ι f = m := by
  dsimp [isoStrongEpiMono]
  apply IsImage.lift_fac

@[simp]
/-
**CategoryTheory.Limits.image.isoStrongEpiMono_inv_comp_mono** 是 Mathlib 中的一个定理，
位于命名空间 `CategoryTheory.Limits.image`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C]   [inst_1 : Categ
oryTheory.Limits.HasStrongEpiMonoFactorisations C] {X Y : C} {f : X ⟶ Y} {I' : C
} (e : X ⟶ I')   (m : I' ⟶ Y) (comm : CategoryTheory.CategoryStruct.comp e m = f
) [inst_2 : CategoryTheory.StrongEpi e]   [inst_3 : CategoryTheory.Mono m],   Ca
tegoryTheory.CategoryStruct.comp (CategoryTheory.Limits.image.isoStrongEpiMono e
 m comm).inv m =     CategoryTheory.Limits.image.ι f
参数：e : X ⟶ I'；m : I' ⟶ Y；comm : CategoryTheory.CategoryStruct.comp e m = f；Categ
oryTheory.Limits.image.isoStrongEpiMono e m comm。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.image.lift_fac`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {X Y : C} {f : X ⟶ Y}   [inst_1 : CategoryTheory.Limits.H
asImage f] (F' : CategoryT…
-/
theorem image.isoStrongEpiMono_inv_comp_mono {I' : C} (e : X ⟶ I') (m : I' ⟶ Y) (comm : e ≫ m = f)
    [StrongEpi e] [Mono m] : (image.isoStrongEpiMono e m comm).inv ≫ m = image.ι f :=
  image.lift_fac _

open MorphismProperty

variable (C)

set_option backward.isDefEq.respectTransparency false in
/-- A category with strong epi mono factorisations admits functorial epi/mono factorizations. -/
/-
**CategoryTheory.Limits.functorialEpiMonoFactorizationData** 是 Mathlib 中的一个定义，位于
命名空间 `CategoryTheory.Limits`。
形式化陈述：functorialEpiMonoFactorizationData : FunctorialFactorizationData (epimorph
isms C) (monomorphisms C) where Z
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasImages_of_hasStrongEpiMonoFactorisations`：∀ {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasSt
rongEpiMonoFactorisations C],   CategoryTheory.Limits.H…

--- 原说明 ---
A category with strong epi mono factorisations admits functorial epi/mono factor
izations.
-/
noncomputable def functorialEpiMonoFactorizationData :
    FunctorialFactorizationData (epimorphisms C) (monomorphisms C) where
  Z := im
  i := { app := fun f => factorThruImage f.hom }
  p := { app := fun f => image.ι f.hom }
  hi _ := epimorphisms.infer_property _
  hp _ := monomorphisms.infer_property _

end CategoryTheory.Limits

namespace CategoryTheory.Functor

open CategoryTheory.Limits

variable {C D : Type*} [Category* C] [Category* D]

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Functor.hasStrongEpiMonoFactorisations_imp_of_isEquivalence** 是
 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：hasStrongEpiMonoFactorisations_imp_of_isEquivalence (F : C ⥤ D) [IsEquival
ence F] [h : HasStrongEpiMonoFactorisations C] : HasStrongEpiMonoFactorisations 
D
参数：F : C ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasStrongEpiMonoFactorisations.has_fac`：∀ {C : Typ
e u} {inst : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.Limits.Has
StrongEpiMonoFactorisations C]   {X Y : C} (f : X …
· 使用定理 `CategoryTheory.mono_comp`：∀ {C : Type u} [inst : CategoryTheory.Category
.{v, u} C] {X Y Z : C} (g : Z ⟶ Y) [CategoryTheory.Mono g] (f : Y ⟶ X)   [Catego
ryTheory.Mono …
· 使用定理 `CategoryTheory.Functor.map_mono`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.preservesMonomorphisms_of_isRightAdjoint`：∀ {C : 
Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.isRightAdjoint_of_isEquivalence`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.MonoFactorisation.m_mono`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] {X Y : C} {f : X ⟶ Y}   (self : CategoryTheory.
Limits.MonoFactorisation f), Categor…
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.strongMono_of_isIso`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {P Q : C} (f : Q ⟶ P) [CategoryTheory.IsIso f],   CategoryT
heory.StrongMono f
· 使用定理 `CategoryTheory.NatIso.hom_app_isIso`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.strongEpi_of_isIso`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] {P Q : C} (f : P ⟶ Q) [CategoryTheory.IsIso f],   CategoryTh
eory.StrongEpi f
· 使用定理 `CategoryTheory.NatIso.inv_app_isIso`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Limits.StrongEpiMonoFactorisation.e_strong_epi`：∀ {C : Ty
pe u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} {f : X ⟶ Y}   (self : 
CategoryTheory.Limits.StrongEpiMonoFactorisation f)…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp_assoc`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v_1, u₁} C] {D : Type u₂}   [inst_1 : CategoryTheory.Category.{v
_2, u₂} D] (F : CategoryThe…
· 使用定理 `CategoryTheory.Limits.MonoFactorisation.fac`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y : C} {f : X ⟶ Y}   (self : CategoryTheory.Lim
its.MonoFactorisation f), Categor…
· 使用定理 `CategoryTheory.Functor.fun_inv_map`：fun_inv_map (F : C ⥤ D) [IsEquivalen
ce F] (X Y : D) (f : X ⟶ Y) : F.map (F.inv.map f) = F.asEquivalence.counit.app X
 ≫ f ≫ F.asEquivalence.c…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_app`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} 
D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_app_assoc`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F G : CategoryThe…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem hasStrongEpiMonoFactorisations_imp_of_isEquivalence (F : C ⥤ D) [IsEquivalence F]
    [h : HasStrongEpiMonoFactorisations C] : HasStrongEpiMonoFactorisations D :=
  ⟨fun {X} {Y} f => by
    let em : StrongEpiMonoFactorisation (F.inv.map f) :=
      (HasStrongEpiMonoFactorisations.has_fac (F.inv.map f)).some
    have : Mono (F.map em.m ≫ F.asEquivalence.counitIso.hom.app Y) := mono_comp _ _
    have : StrongEpi (F.asEquivalence.counitIso.inv.app X ≫ F.map em.e) := strongEpi_comp _ _
    exact
      Nonempty.intro
        { I := F.obj em.I
          e := F.asEquivalence.counitIso.inv.app X ≫ F.map em.e
          m := F.map em.m ≫ F.asEquivalence.counitIso.hom.app Y
          fac := by
            simp only [Category.assoc, ← F.map_comp_assoc,
              MonoFactorisation.fac, fun_inv_map, id_obj, Iso.inv_hom_id_app, Category.comp_id,
              Iso.inv_hom_id_app_assoc] }⟩

end CategoryTheory.Functor

