/-
Copyright (c) 2022 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno, Junyan Xu
-/
module

public import Mathlib.CategoryTheory.PathCategory.Basic
public import Mathlib.CategoryTheory.Functor.FullyFaithful
public import Mathlib.CategoryTheory.Bicategory.Free
public import Mathlib.CategoryTheory.Bicategory.LocallyDiscrete

/-!
# The coherence theorem for bicategories

In this file, we prove the coherence theorem for bicategories, stated in the following form: the
free bicategory over any quiver is locally thin.

The proof is almost the same as the proof of the coherence theorem for monoidal categories that
has been previously formalized in mathlib, which is based on the proof described by Ilya Beylin
and Peter Dybjer. The idea is to view a path on a quiver as a normal form of a 1-morphism in the
free bicategory on the same quiver. A normalization procedure is then described by
`normalize : FreeBicategory B ⥤ᵖ (LocallyDiscrete (Paths B))`, which is a
pseudofunctor from the free bicategory to the locally discrete bicategory on the path category.
It turns out that this pseudofunctor is locally an equivalence of categories, and the coherence
theorem follows immediately from this fact.

## Main statements

* `locally_thin` : the free bicategory is locally thin, that is, there is at most one
  2-morphism between two fixed 1-morphisms.

## References

* [Ilya Beylin and Peter Dybjer, Extracting a proof of coherence for monoidal categories from a
  proof of normalization for monoids][beylin1996]
-/

@[expose] public section


open Quiver (Path)

open Quiver.Path

namespace CategoryTheory

open Bicategory Category

universe v u

namespace FreeBicategory

variable {B : Type u} [Quiver.{v} B]

/-- Auxiliary definition for `inclusionPath`. -/
@[simp]
/-
**CategoryTheory.FreeBicategory.inclusionPathAux** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.FreeBicategory`。
形式化陈述：inclusionPathAux {a : B} : forall {b : B}, Path a b -> Hom a b | _, nil =>
 Hom.id a | _, cons p f => (inclusionPathAux p).comp (Hom.of f)  /-- Category st
ructure on `Hom a b`. In this file, we will use `Hom a b` for `a b : B` (precise
ly, `FreeBicategory.Hom a b`) instead of the definitionally equal expression `a 
⟶ b` for `a b : FreeBicategory B`. The main reason is that we have to annoyingly
 write `@Quiver.Hom (FreeBicategory B) _ a b` to get the latter expression when 
given `a b : B`. -/ local 
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `inclusionPath`.
-/
def inclusionPathAux {a : B} : ∀ {b : B}, Path a b → Hom a b
  | _, nil => Hom.id a
  | _, cons p f => (inclusionPathAux p).comp (Hom.of f)

/-- Category structure on `Hom a b`. In this file, we will use `Hom a b` for `a b : B`
(precisely, `FreeBicategory.Hom a b`) instead of the definitionally equal expression
`a ⟶ b` for `a b : FreeBicategory B`. The main reason is that we have to annoyingly write
`@Quiver.Hom (FreeBicategory B) _ a b` to get the latter expression when given `a b : B`. -/
local instance homCategory' (a b : B) : Category (Hom a b) :=
  homCategory a b

/-- The discrete category on the paths includes into the category of 1-morphisms in the free
bicategory.
-/
/-
**CategoryTheory.FreeBicategory.inclusionPath** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.FreeBicategory`。
形式化陈述：inclusionPath (a b : B) : Discrete (Path.{v} a b) ⥤ Hom a b
参数：a b : B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The discrete category on the paths includes into the category of 1-morphisms in 
the free
bicategory.
-/
def inclusionPath (a b : B) : Discrete (Path.{v} a b) ⥤ Hom a b :=
  Discrete.functor inclusionPathAux

set_option backward.isDefEq.respectTransparency.types false in
/-- The inclusion from the locally discrete bicategory on the path category into the free bicategory
as a prelax functor. This will be promoted to a pseudofunctor after proving the coherence theorem.
See `inclusion`.
-/
/-
**CategoryTheory.FreeBicategory.preinclusion** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.FreeBicategory`。
形式化陈述：preinclusion (B : Type u) [Quiver.{v} B] : PrelaxFunctor (LocallyDiscrete 
(Paths B)) (FreeBicategory B) where obj a
参数：B : Type u。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion from the locally discrete bicategory on the path category into the
 free bicategory
as a prelax functor. This will be promoted to a pseudofunctor after proving the 
coherence theorem.
See `inclusion`.
-/
def preinclusion (B : Type u) [Quiver.{v} B] :
    PrelaxFunctor (LocallyDiscrete (Paths B)) (FreeBicategory B) where
  obj a := a.as
  map {a b} f := (@inclusionPath B _ a.as b.as).obj f
  map₂ η := (inclusionPath _ _).map η

@[simp]
/-
**CategoryTheory.FreeBicategory.preinclusion_obj** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.FreeBicategory`。
形式化陈述：preinclusion_obj (a : B) : (preinclusion B).obj ⟨a⟩ = a
参数：a : B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem preinclusion_obj (a : B) : (preinclusion B).obj ⟨a⟩ = a :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**CategoryTheory.FreeBicategory.preinclusion_map** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.FreeBicategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem preinclusion_map₂ {a b : B} (f g : Discrete (Path.{v} a b)) (η : f ⟶ g) :
    (preinclusion B).map₂ η = eqToHom (congr_arg _ (Discrete.ext (Discrete.eq_of_hom η))) :=
  rfl

/-- The normalization of the composition of `p : Path a b` and `f : Hom b c`.
`p` will eventually be taken to be `nil` and we then get the normalization
of `f` alone, but the auxiliary `p` is necessary for Lean to accept the definition of
`normalizeIso` and the `whisker_left` case of `normalizeAux_congr` and `normalize_naturality`.
-/
@[simp]
/-
**CategoryTheory.FreeBicategory.normalizeAux** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.FreeBicategory`。
形式化陈述：{B : Type u} →   [inst : Quiver B] → {a b c : B} → Quiver.Path a b → Categ
oryTheory.FreeBicategory.Hom b c → Quiver.Path a c
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The normalization of the composition of `p : Path a b` and `f : Hom b c`.
`p` will eventually be taken to be `nil` and we then get the normalization
of `f` alone, but the auxiliary `p` is necessary for Lean to accept the definiti
on of
`normalizeIso` and the `whisker_left` case of `normalizeAux_congr` and `normaliz
e_naturality`.
-/
def normalizeAux {a : B} : ∀ {b c : B}, Path a b → Hom b c → Path a c
  | _, _, p, Hom.of f => p.cons f
  | _, _, p, Hom.id _ => p
  | _, _, p, Hom.comp f g => normalizeAux (normalizeAux p f) g

/-
We may define
```
def normalizeAux' : ∀ {a b : B}, Hom a b → Path a b
  | _, _, (Hom.of f) => f.toPath
  | _, _, (Hom.id b) => nil
  | _, _, (Hom.comp f g) => (normalizeAux' f).comp (normalizeAux' g)
```
and define `normalizeAux p f` to be `p.comp (normalizeAux' f)` and this will be
equal to the above definition, but the equality proof requires `comp_assoc`, and it
thus lacks the correct definitional property to make the definition of `normalizeIso`
typecheck.
```
example {a b c : B} (p : Path a b) (f : Hom b c) :
    normalizeAux p f = p.comp (normalizeAux' f) := by
  induction f; rfl; rfl;
  case comp _ _ _ _ _ ihf ihg => rw [normalizeAux, ihf, ihg]; apply comp_assoc
```
-/
set_option backward.isDefEq.respectTransparency.types false in
/-- A 2-isomorphism between a partially-normalized 1-morphism in the free bicategory to the
fully-normalized 1-morphism.
-/
@[simp]
/-
**CategoryTheory.FreeBicategory.normalizeIso** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.FreeBicategory`。
形式化陈述：{B : Type u} →   [inst : Quiver B] →     {a b c : B} →       (p : Quiver.P
ath a b) →         (f : CategoryTheory.FreeBicategory.Hom b c) →           Categ
oryTheory.CategoryStruct.comp ((CategoryTheory.FreeBicategory.preinclusion B).ma
p { as := p }) f ≅             (CategoryTheory.FreeBicategory.preinclusion B).ma
p { as := CategoryTheory.FreeBicategory.normalizeAux p f }
参数：p : Quiver.Path a b；f : CategoryTheory.FreeBicategory.Hom b c；(CategoryTheory
.FreeBicategory.preinclusion B).map { as := p }；CategoryTheory.FreeBicategory.pr
einclusion B。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A 2-isomorphism between a partially-normalized 1-morphism in the free bicategory
 to the
fully-normalized 1-morphism.
-/
def normalizeIso {a : B} :
    ∀ {b c : B} (p : Path a b) (f : Hom b c),
      (preinclusion B).map ⟨p⟩ ≫ f ≅ (preinclusion B).map ⟨normalizeAux p f⟩
  | _, _, _, Hom.of _ => Iso.refl _
  | _, _, _, Hom.id b => ρ_ _
  | _, _, p, Hom.comp f g =>
    (α_ _ _ _).symm ≪≫ whiskerRightIso (normalizeIso p f) g ≪≫ normalizeIso (normalizeAux p f) g

-- Equation lemmas for `normalizeIso`/`normalizeAux` matching `≫`/`𝟙`
-- (i.e., `CategoryStruct.comp`/`CategoryStruct.id` for `FreeBicategory`) instead of
-- `Hom.comp`/`Hom.id`. Needed because after leanprover/lean4#13363, `canUnfoldAtMatcher`
-- no longer unfolds class projections in match discriminants.
/-
**CategoryTheory.FreeBicategory.normalizeAux_comp** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.FreeBicategory`。
形式化陈述：∀ {B : Type u} [inst : Quiver B] {a : B} {b c d : CategoryTheory.FreeBicat
egory B} (p : Quiver.Path a b) (f : b ⟶ c)   (g : c ⟶ d),   CategoryTheory.FreeB
icategory.normalizeAux p (CategoryTheory.CategoryStruct.comp f g) =     Category
Theory.FreeBicategory.normalizeAux (CategoryTheory.FreeBicategory.normalizeAux p
 f) g
参数：p : Quiver.Path a b；f : b ⟶ c；g : c ⟶ d；CategoryTheory.CategoryStruct.comp f 
g；CategoryTheory.FreeBicategory.normalizeAux p f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem normalizeAux_comp {a : B} {b c d : FreeBicategory B}
    (p : Path a b) (f : b ⟶ c) (g : c ⟶ d) :
    normalizeAux p (f ≫ g) = normalizeAux (normalizeAux p f) g := rfl
/-
**CategoryTheory.FreeBicategory.normalizeAux_id** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.FreeBicategory`。
形式化陈述：∀ {B : Type u} [inst : Quiver B] {a : B} {b : CategoryTheory.FreeBicategor
y B} (p : Quiver.Path a b),   CategoryTheory.FreeBicategory.normalizeAux p (Cate
goryTheory.CategoryStruct.id b) = p
参数：p : Quiver.Path a b；CategoryTheory.CategoryStruct.id b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem normalizeAux_id {a : B} {b : FreeBicategory B} (p : Path a b) :
    normalizeAux p (𝟙 b) = p := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.FreeBicategory.normalizeIso_comp** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.FreeBicategory`。
形式化陈述：∀ {B : Type u} [inst : Quiver B] {a : B} {b c d : CategoryTheory.FreeBicat
egory B} (p : Quiver.Path a b) (f : b ⟶ c)   (g : c ⟶ d),   CategoryTheory.FreeB
icategory.normalizeIso p (CategoryTheory.CategoryStruct.comp f g) =     (Categor
yTheory.Bicategory.associator ((CategoryTheory.FreeBicategory.preinclusion B).ma
p { as := p }) f g).symm ≪≫       CategoryTheory.Bicategory.whiskerRightIso (Cat
egoryTheory.FreeBicategory.normalizeIso p f) g ≪≫         CategoryTheory.FreeBic
ategory.normalizeIso (CategoryTheory.FreeBicategory.normalizeAux p f) g
参数：p : Quiver.Path a b；f : b ⟶ c；g : c ⟶ d；CategoryTheory.CategoryStruct.comp f 
g；CategoryTheory.Bicategory.associator ((CategoryTheory.FreeBicategory.preinclus
ion B).map { as := p }) f g；CategoryTheory.FreeBicategory.normalizeIso p f；Categ
oryTheory.FreeBicategory.normalizeAux p f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem normalizeIso_comp {a : B} {b c d : FreeBicategory B}
    (p : Path a b) (f : b ⟶ c) (g : c ⟶ d) :
    normalizeIso p (f ≫ g) =
      (α_ _ _ _).symm ≪≫ whiskerRightIso (normalizeIso p f) g ≪≫
        normalizeIso (normalizeAux p f) g := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.FreeBicategory.normalizeIso_id** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.FreeBicategory`。
形式化陈述：∀ {B : Type u} [inst : Quiver B] {a : B} {b : CategoryTheory.FreeBicategor
y B} (p : Quiver.Path a b),   CategoryTheory.FreeBicategory.normalizeIso p (Cate
goryTheory.CategoryStruct.id b) =     CategoryTheory.Bicategory.rightUnitor ((Ca
tegoryTheory.FreeBicategory.preinclusion B).map { as := p })
参数：p : Quiver.Path a b；CategoryTheory.CategoryStruct.id b；(CategoryTheory.FreeBi
category.preinclusion B).map { as := p }。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem normalizeIso_id {a : B} {b : FreeBicategory B} (p : Path a b) :
    normalizeIso p (𝟙 b) = ρ_ _ := rfl
/-
**CategoryTheory.FreeBicategory.quot_whisker_left** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.FreeBicategory`。
形式化陈述：∀ {B : Type u} [inst : Quiver B] {a b c : CategoryTheory.FreeBicategory B}
 (f : a ⟶ b) {g h : b ⟶ c}   (η : CategoryTheory.FreeBicategory.Hom₂ g h),   Quo
t.mk CategoryTheory.FreeBicategory.Rel (CategoryTheory.FreeBicategory.Hom₂.whisk
er_left f η) =     CategoryTheory.Bicategory.whiskerLeft f (Quot.mk CategoryTheo
ry.FreeBicategory.Rel η)
参数：f : a ⟶ b；η : CategoryTheory.FreeBicategory.Hom₂ g h；CategoryTheory.FreeBicat
egory.Hom₂.whisker_left f η；Quot.mk CategoryTheory.FreeBicategory.Rel η。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem quot_whisker_left {a b c : FreeBicategory B} (f : a ⟶ b) {g h : b ⟶ c}
    (η : Hom₂ g h) : Quot.mk Rel (Hom₂.whisker_left f η) = f ◁ (Quot.mk Rel η) := rfl

/-- Given a 2-morphism between `f` and `g` in the free bicategory, we have the equality
`normalizeAux p f = normalizeAux p g`.
-/
/-
**CategoryTheory.FreeBicategory.normalizeAux_congr** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.FreeBicategory`。
形式化陈述：normalizeAux_congr {a b c : B} (p : Path a b) {f g : Hom b c} (η : f ⟶ g) 
: normalizeAux p f = normalizeAux p g
参数：p : Path a b；η : f ⟶ g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'

--- 原说明 ---
Given a 2-morphism between `f` and `g` in the free bicategory, we have the equal
ity
`normalizeAux p f = normalizeAux p g`.
-/
theorem normalizeAux_congr {a b c : B} (p : Path a b) {f g : Hom b c} (η : f ⟶ g) :
    normalizeAux p f = normalizeAux p g := by
  rcases η with ⟨η'⟩
  apply @congr_fun _ _ fun p => normalizeAux p f
  clear p η
  induction η' with
  | vcomp _ _ _ _ => apply Eq.trans <;> assumption
  | whisker_left _ _ ih => funext; apply congr_fun ih
  | whisker_right _ _ ih => funext; apply congr_arg₂ _ (congr_fun ih _) rfl
  | _ => funext; rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The 2-isomorphism `normalizeIso p f` is natural in `f`. -/
/-
**CategoryTheory.FreeBicategory.normalize_naturality** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.FreeBicategory`。
形式化陈述：normalize_naturality {a b c : B} (p : Path a b) {f g : Hom b c} (η : f ⟶ g
) : (preinclusion B).map ⟨p⟩ ◁ η ≫ (normalizeIso p g).hom = (normalizeIso p f).h
om ≫ (preinclusion B).map₂ (eqToHom (Discrete.ext (normalizeAux_congr p η)))
参数：p : Path a b；η : f ⟶ g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Discrete.ext`：∀ {α : Type u₁} {x y : CategoryTheory.Discr
ete α}, x.as = y.as → x = y
· 使用定理 `CategoryTheory.FreeBicategory.normalizeAux_congr`：normalizeAux_congr {a 
b c : B} (p : Path a b) {f g : Hom b c} (η : f ⟶ g) : normalizeAux p f = normali
zeAux p g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Bicategory.whiskerLeft_id`：∀ {B : Type u} [self : Categor
yTheory.Bicategory B] {a b c : B} (f : a ⟶ b) (g : b ⟶ c),   CategoryTheory.Bica
tegory.whiskerLeft f (Category…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Bicategory.whiskerLeft_comp`：∀ {B : Type u} [self : Categ
oryTheory.Bicategory B] {a b c : B} (f : a ⟶ b) {g h i : b ⟶ c} (η : g ⟶ h) (θ :
 h ⟶ i),   CategoryTheory.Bicate…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `CategoryTheory.Discrete.eq_of_hom`：eq_of_hom {X Y : Discrete α} (i : X ⟶
 Y) : X.as = Y.as
· 使用定理 `CategoryTheory.eqToHom_trans`：eqToHom_trans {X Y Z : C} (p : X = Y) (q :
 Y = Z) : eqToHom p ≫ eqToHom q = eqToHom (p.trans q)
· 使用定理 `CategoryTheory.Bicategory.associator_inv_naturality_right_assoc`：∀ {B : 
Type u} [inst : CategoryTheory.Bicategory B] {a b c d : B} (f : a ⟶ b) (g : b ⟶ 
c) {h h' : c ⟶ d} (η : h ⟶ h')   {Z : a ⟶ d} (h_1 : C…
· 使用定理 `CategoryTheory.Bicategory.whisker_exchange_assoc`：∀ {B : Type u} [self :
 CategoryTheory.Bicategory B] {a b c : B} {f g : a ⟶ b} {h i : b ⟶ c} (η : f ⟶ g
) (θ : h ⟶ i)   {Z : a ⟶ c} (h_1 : Cat…
· 使用定理 `CategoryTheory.Bicategory.associator_inv_naturality_middle_assoc`：∀ {B :
 Type u} [inst : CategoryTheory.Bicategory B] {a b c d : B} (f : a ⟶ b) {g g' : 
b ⟶ c} (η : g ⟶ g') (h : c ⟶ d)   {Z : a ⟶ d} (h_1 : C…
· 使用定理 `CategoryTheory.Bicategory.comp_whiskerRight_assoc`：∀ {B : Type u} [self 
: CategoryTheory.Bicategory B] {a b c : B} {f g h : a ⟶ b} (η : f ⟶ g) (θ : g ⟶ 
h) (i : b ⟶ c)   {Z : a ⟶ c} (h_1 : Cat…
· 使用定理 `CategoryTheory.Bicategory.comp_whiskerRight`：∀ {B : Type u} [self : Cate
goryTheory.Bicategory B] {a b c : B} {f g h : a ⟶ b} (η : f ⟶ g) (θ : g ⟶ h) (i 
: b ⟶ c),   CategoryTheory.Bicate…
· 使用定理 `CategoryTheory.dcongr_arg`：dcongr_arg {ι : Type*} {F G : ι -> C} (α : fo
rall i, F i ⟶ G i) {i j : ι} (h : i = j) : α i = eqToHom (congr_arg F h) ≫ α j ≫
 eqToHom (congr…
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `CategoryTheory.Bicategory.eqToHom_whiskerRight`：eqToHom_whiskerRight {a 
b c : B} {f g : a ⟶ b} (η : f = g) (h : b ⟶ c) : eqToHom η ▷ h = eqToHom (congr_
arg₂ (· ≫ ·) η rfl)
· 使用定理 `CategoryTheory.Bicategory.whiskerRight_comp`：∀ {B : Type u} [self : Cate
goryTheory.Bicategory B] {a b c d : B} {f f' : a ⟶ b} (η : f ⟶ f') (g : b ⟶ c) (
h : c ⟶ d),   CategoryTheory.Bica…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `CategoryTheory.Bicategory.pentagon_hom_inv_inv_inv_inv_assoc`：∀ {B : Typ
e u} [inst : CategoryTheory.Bicategory B] {a b c d e : B} (f : a ⟶ b) (g : b ⟶ c
) (h : c ⟶ d) (i : d ⟶ e)   {Z : a ⟶ e}   (h_1 :  …
· 使用定理 `CategoryTheory.Bicategory.pentagon_inv_assoc`：∀ {B : Type u} [inst : Cat
egoryTheory.Bicategory B] {a b c d e : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i
 : d ⟶ e)   {Z : a ⟶ e}   (h_1 :  …
· 使用定理 `CategoryTheory.Bicategory.whiskerLeft_rightUnitor`：whiskerLeft_rightUnit
or (f : a ⟶ b) (g : b ⟶ c) : f ◁ (ρ_ g).hom = (α_ f g (𝟙 c)).inv ≫ (ρ_ (f ≫ g)).
hom
（共 36 条，此处仅展示前 30 条）

--- 原说明 ---
The 2-isomorphism `normalizeIso p f` is natural in `f`.
-/
theorem normalize_naturality {a b c : B} (p : Path a b) {f g : Hom b c} (η : f ⟶ g) :
    (preinclusion B).map ⟨p⟩ ◁ η ≫ (normalizeIso p g).hom =
      (normalizeIso p f).hom ≫
        (preinclusion B).map₂ (eqToHom (Discrete.ext (normalizeAux_congr p η))) := by
  rcases η with ⟨η'⟩; clear η
  induction η' with
  | id => simp
  | vcomp η θ ihf ihg =>
    simp only [mk_vcomp, whiskerLeft_comp]
    slice_lhs 2 3 => rw [ihg]
    slice_lhs 1 2 => rw [ihf]
    simp
  -- p ≠ nil required! See the docstring of `normalizeAux`.
  | whisker_left _ _ ih =>
    dsimp
    rw [associator_inv_naturality_right_assoc, whisker_exchange_assoc, ih]
    simp
  | whisker_right h η' ih =>
    dsimp
    rw [associator_inv_naturality_middle_assoc, ← comp_whiskerRight_assoc, ih, comp_whiskerRight]
    have := dcongr_arg (fun x => (normalizeIso x h).hom) (normalizeAux_congr p (Quot.mk _ η'))
    dsimp at this; simp [this]
  | _ => simp

-- Not `@[simp]` because it is not in `simp`-normal form.
/-
**CategoryTheory.FreeBicategory.normalizeAux_nil_comp** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.FreeBicategory`。
形式化陈述：normalizeAux_nil_comp {a b c : B} (f : Hom a b) (g : Hom b c) : normalizeA
ux nil (f.comp g) = (normalizeAux nil f).comp (normalizeAux nil g)
参数：f : Hom a b；g : Hom b c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Quiver.Path.comp_assoc`：∀ {V : Type u} [inst : Quiver V] {a b c d : V} (
p : Quiver.Path a b) (q : Quiver.Path b c) (r : Quiver.Path c d),   (p.comp q).c
omp r = p.co…
-/
theorem normalizeAux_nil_comp {a b c : B} (f : Hom a b) (g : Hom b c) :
    normalizeAux nil (f.comp g) = (normalizeAux nil f).comp (normalizeAux nil g) := by
  induction g generalizing a with
  | id => rfl
  | of => rfl
  | comp g _ ihf ihg => erw [ihg (f.comp g), ihf f, ihg g, comp_assoc]

/-- The normalization pseudofunctor for the free bicategory on a quiver `B`. -/
/-
**CategoryTheory.FreeBicategory.normalize** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.FreeBicategory`。
形式化陈述：normalize (B : Type u) [Quiver.{v} B] : FreeBicategory B ⥤ᵖ (LocallyDiscre
te (Paths B)) where obj a
参数：B : Type u。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The normalization pseudofunctor for the free bicategory on a quiver `B`.
-/
def normalize (B : Type u) [Quiver.{v} B] :
    FreeBicategory B ⥤ᵖ (LocallyDiscrete (Paths B)) where
  obj a := ⟨a⟩
  map f := ⟨normalizeAux nil f⟩
  map₂ η := eqToHom <| Discrete.ext <| normalizeAux_congr nil η
  mapId _ := eqToIso <| Discrete.ext rfl
  mapComp f g := eqToIso <| Discrete.ext <| normalizeAux_nil_comp f g

set_option backward.isDefEq.respectTransparency.types false in
/-- Auxiliary definition for `normalizeEquiv`. -/
/-
**CategoryTheory.FreeBicategory.normalizeUnitIso** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.FreeBicategory`。
形式化陈述：normalizeUnitIso (a b : FreeBicategory B) : 𝟭 (a ⟶ b) ≅ (normalize B).mapF
unctor a b ⋙ @inclusionPath B _ a b
参数：a b : FreeBicategory B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `normalizeEquiv`.
-/
def normalizeUnitIso (a b : FreeBicategory B) :
    𝟭 (a ⟶ b) ≅ (normalize B).mapFunctor a b ⋙ @inclusionPath B _ a b :=
  NatIso.ofComponents (fun f => (λ_ f).symm ≪≫ normalizeIso nil f)
    (by
      intro f g η
      erw [leftUnitor_inv_naturality_assoc, assoc]
      congr 1
      exact normalize_naturality nil η)

set_option backward.isDefEq.respectTransparency.types false in
/-- Normalization as an equivalence of categories. -/
/-
**CategoryTheory.FreeBicategory.normalizeEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.FreeBicategory`。
形式化陈述：normalizeEquiv (a b : B) : Hom a b ≌ Discrete (Path.{v} a b)
参数：a b : B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Normalization as an equivalence of categories.
-/
def normalizeEquiv (a b : B) : Hom a b ≌ Discrete (Path.{v} a b) :=
  Equivalence.mk ((normalize _).mapFunctor a b) (inclusionPath a b) (normalizeUnitIso a b)
    (Discrete.natIso fun f => eqToIso (by
      obtain ⟨f⟩ := f
      induction f with
      | nil => rfl
      | cons _ _ ih =>
        ext1 -- Porting note: `tidy` closes the goal in mathlib3 but `aesop` doesn't here.
        injection ih with ih
        conv_rhs => rw [← ih]
        rfl))

set_option backward.isDefEq.respectTransparency.types false in
/-- The coherence theorem for bicategories. -/
/-
**CategoryTheory.FreeBicategory.locally_thin** 是 Mathlib 中的一个实例，位于命名空间 `Category
Theory.FreeBicategory`。
形式化陈述：locally_thin {a b : FreeBicategory B} : Quiver.IsThin (a ⟶ b)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.map_injective`：map_injective (F : C ⥤ D) [Faithfu
l F] : Function.Injective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b

--- 原说明 ---
The coherence theorem for bicategories.
-/
instance locally_thin {a b : FreeBicategory B} : Quiver.IsThin (a ⟶ b) := fun _ _ =>
  ⟨fun _ _ =>
    (@normalizeEquiv B _ a b).functor.map_injective (Subsingleton.elim _ _)⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- Auxiliary definition for `inclusion`. -/
/-
**CategoryTheory.FreeBicategory.inclusionMapCompAux** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.FreeBicategory`。
形式化陈述：{B : Type u} →   [inst : Quiver B] →     {a b c : B} →       (f : Quiver.P
ath a b) →         (g : Quiver.Path b c) →           (CategoryTheory.FreeBicateg
ory.preinclusion B).map               (CategoryTheory.CategoryStruct.comp { as :
= f } { as := g }) ≅             CategoryTheory.CategoryStruct.comp ((CategoryTh
eory.FreeBicategory.preinclusion B).map { as := f })               ((CategoryThe
ory.FreeBicategory.preinclusion B).map { as := g })
参数：f : Quiver.Path a b；g : Quiver.Path b c；CategoryTheory.FreeBicategory.preincl
usion B；CategoryTheory.CategoryStruct.comp { as := f } { as := g }；(CategoryTheo
ry.FreeBicategory.preinclusion B).map { as := f }；(CategoryTheory.FreeBicategory
.preinclusion B).map { as := g }。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `inclusion`.
-/
def inclusionMapCompAux {a b : B} :
    ∀ {c : B} (f : Path a b) (g : Path b c),
      (preinclusion _).map (⟨f⟩ ≫ ⟨g⟩) ≅ (preinclusion _).map ⟨f⟩ ≫ (preinclusion _).map ⟨g⟩
  | _, f, nil => (ρ_ ((preinclusion _).map ⟨f⟩)).symm
  | _, f, cons g₁ g₂ => whiskerRightIso (inclusionMapCompAux f g₁) (Hom.of g₂) ≪≫ α_ _ _ _

set_option backward.isDefEq.respectTransparency.types false in
/-- The inclusion pseudofunctor from the locally discrete bicategory on the path category into the
free bicategory.
-/
/-
**CategoryTheory.FreeBicategory.inclusion** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.FreeBicategory`。
形式化陈述：inclusion (B : Type u) [Quiver.{v} B] : LocallyDiscrete (Paths B) ⥤ᵖ (Free
Bicategory B)
参数：B : Type u。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion pseudofunctor from the locally discrete bicategory on the path cat
egory into the
free bicategory.
-/
def inclusion (B : Type u) [Quiver.{v} B] :
    LocallyDiscrete (Paths B) ⥤ᵖ (FreeBicategory B) :=
  { -- All the conditions for 2-morphisms are trivial thanks to the coherence theorem!
    preinclusion B with
    mapId := fun _ => Iso.refl _
    mapComp := fun f g => inclusionMapCompAux f.as g.as }

end FreeBicategory

end CategoryTheory

