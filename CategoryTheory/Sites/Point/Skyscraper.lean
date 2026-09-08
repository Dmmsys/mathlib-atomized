/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Brian Nugent
-/
module

public import Mathlib.CategoryTheory.Sites.Point.Basic

/-!
# Skyscraper sheaves

Let `Φ` be a point of a site `(C, J)`. In this file, we construct the
skyscraper sheaf functor `skyscraperSheafFunctor : A ⥤ Sheaf J A` and
show that it is a right adjoint to `Φ.sheafFiber : Sheaf J A ⥤ A`.

-/

@[expose] public section

universe w v' v u' u

namespace CategoryTheory.GrothendieckTopology.Point

open Limits Opposite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (Φ : Point.{w} J) {A : Type u'} [Category.{v'} A]
  [HasProducts.{w} A]

/-- Given a point `Φ` on a site `(C, J)`, this is the skyscraper presheaf functor
`A ⥤ Cᵒᵖ ⥤ A`. -/
@[simps!]
/-
**CategoryTheory.GrothendieckTopology.Point.skyscraperPresheafFunctor** 是 Mathli
b 中的一个定义，位于命名空间 `CategoryTheory.GrothendieckTopology.Point`。
形式化陈述：skyscraperPresheafFunctor : A ⥤ Cᵒᵖ ⥤ A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a point `Φ` on a site `(C, J)`, this is the skyscraper presheaf functor
`A ⥤ Cᵒᵖ ⥤ A`.
-/
noncomputable def skyscraperPresheafFunctor : A ⥤ Cᵒᵖ ⥤ A :=
  Functor.flip (Φ.fiber.op ⋙ piFunctor.{w}.flip)

/-- Given a point `Φ` on a site `(C, J)`, and an object `M` of a category `A`,
this is the skyscraper presheaf with value `M`: it sends `X : C` to the
product of copies of `M` indexed by `Φ.fiber.obj X`. -/
/-
**CategoryTheory.GrothendieckTopology.Point.skyscraperPresheaf** 是 Mathlib 中的一个缩
写定义，位于命名空间 `CategoryTheory.GrothendieckTopology.Point`。
形式化陈述：skyscraperPresheaf (M : A) : Cᵒᵖ ⥤ A
参数：M : A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a point `Φ` on a site `(C, J)`, and an object `M` of a category `A`,
this is the skyscraper presheaf with value `M`: it sends `X : C` to the
product of copies of `M` indexed by `Φ.fiber.obj X`.
-/
noncomputable abbrev skyscraperPresheaf (M : A) :
    Cᵒᵖ ⥤ A :=
  Φ.skyscraperPresheafFunctor.obj M

section

variable {P Q : Cᵒᵖ ⥤ A} {M N : A} [HasColimitsOfSize.{w, w} A]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- If `Φ` is a point of a site `(C, J)`, `P : Cᵒᵖ ⥤ A` and `M : A`, this is
the bijection `(Φ.presheafFiber.obj P ⟶ M) ≃ (P ⟶ Φ.skyscraperPresheaf M)`
that is part of the adjunction `skyscraperPresheafAdjunction`. -/
@[simps -isSimp apply_app symm_apply]
/-
**CategoryTheory.GrothendieckTopology.Point.skyscraperPresheafHomEquiv** 是 Mathl
ib 中的一个定义，位于命名空间 `CategoryTheory.GrothendieckTopology.Point`。
形式化陈述：skyscraperPresheafHomEquiv : (Φ.presheafFiber.obj P ⟶ M) ≃ (P ⟶ Φ.skyscrap
erPresheaf M) where toFun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `Φ` is a point of a site `(C, J)`, `P : Cᵒᵖ ⥤ A` and `M : A`, this is
the bijection `(Φ.presheafFiber.obj P ⟶ M) ≃ (P ⟶ Φ.skyscraperPresheaf M)`
that is part of the adjunction `skyscraperPresheafAdjunction`.
-/
noncomputable def skyscraperPresheafHomEquiv :
    (Φ.presheafFiber.obj P ⟶ M) ≃ (P ⟶ Φ.skyscraperPresheaf M) where
  toFun f :=
    { app X := Pi.lift (fun x ↦ Φ.toPresheafFiber X.unop x P ≫ f)
      naturality {X Y} g := by
        dsimp
        ext y
        have := Φ.toPresheafFiber_w g.unop y P
        dsimp at this
        simp [reassoc_of% this] }
  invFun g := Φ.presheafFiberDesc (fun X x ↦ g.app (op X) ≫ Pi.π _ x) (by simp)
  left_inv f := by cat_disch
  right_inv g := by cat_disch

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.GrothendieckTopology.Point.toPresheafFiber_skyscraperPresheafHo
mEquiv_symm** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.GrothendieckTopology.Point
`。
形式化陈述：toPresheafFiber_skyscraperPresheafHomEquiv_symm (g : P ⟶ Φ.skyscraperPresh
eaf M) (X : C) (x : Φ.fiber.obj X) : Φ.toPresheafFiber X x P ≫ Φ.skyscraperPresh
eafHomEquiv.symm g = g.app (op X) ≫ Pi.π _ x
参数：g : P ⟶ Φ.skyscraperPresheaf M；X : C；x : Φ.fiber.obj X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.GrothendieckTopology.Point.skyscraperPresheafHomEquiv_sym
m_apply`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {J : CategoryT
heory.GrothendieckTopology C} (Φ : J.Point)   {A : Type u'} [inst_1 :…
· 使用引理 `CategoryTheory.GrothendieckTopology.Point.toPresheafFiber_presheafFiberD
esc`：toPresheafFiber_presheafFiberDesc (X : C) (x : Φ.fiber.obj X) : Φ.toPreshea
fFiber X x P ≫ Φ.presheafFiberDesc φ hφ = φ X x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
`respectTransparency.types true` changes the auto-generated lemmas' signature
-/
lemma toPresheafFiber_skyscraperPresheafHomEquiv_symm
    (g : P ⟶ Φ.skyscraperPresheaf M) (X : C) (x : Φ.fiber.obj X) :
    Φ.toPresheafFiber X x P ≫ Φ.skyscraperPresheafHomEquiv.symm g =
      g.app (op X) ≫ Pi.π _ x := by
  simp [skyscraperPresheafHomEquiv_symm_apply]

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
/-
**CategoryTheory.GrothendieckTopology.Point.skyscraperPresheafHomEquiv_naturalit
y_left_symm** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.GrothendieckTopology.Point
`。
形式化陈述：skyscraperPresheafHomEquiv_naturality_left_symm (f : P ⟶ Q) (g : Q ⟶ Φ.sky
scraperPresheaf M) : Φ.skyscraperPresheafHomEquiv.symm (f ≫ g) = Φ.presheafFiber
.map f ≫ Φ.skyscraperPresheafHomEquiv.symm g
参数：f : P ⟶ Q；g : Q ⟶ Φ.skyscraperPresheaf M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.GrothendieckTopology.Point.presheafFiber_hom_ext`：preshea
fFiber_hom_ext {P : Cᵒᵖ ⥤ A} {T : A} {f g : Φ.presheafFiber.obj P ⟶ T} (h : fora
ll (X : C) (x : Φ.fiber.obj X), Φ.toPresheafFiber X x…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.GrothendieckTopology.Point.toPresheafFiber_skyscraperPres
heafHomEquiv_symm`：toPresheafFiber_skyscraperPresheafHomEquiv_symm (g : P ⟶ Φ.sk
yscraperPresheaf M) (X : C) (x : Φ.fiber.obj X) : Φ.toPresheafFiber X x P ≫ Φ.s…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.GrothendieckTopology.Point.toPresheafFiber_naturality_ass
oc`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {J : CategoryTheory
.GrothendieckTopology C} (Φ : J.Point)   {A : Type u'} [inst_1 :…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma skyscraperPresheafHomEquiv_naturality_left_symm
    (f : P ⟶ Q) (g : Q ⟶ Φ.skyscraperPresheaf M) :
    Φ.skyscraperPresheafHomEquiv.symm (f ≫ g) =
      Φ.presheafFiber.map f ≫ Φ.skyscraperPresheafHomEquiv.symm g := by
  cat_disch

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.GrothendieckTopology.Point.skyscraperPresheafHomEquiv_app_** 是 
Mathlib 中的一个引理，位于命名空间 `CategoryTheory.GrothendieckTopology.Point`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma skyscraperPresheafHomEquiv_app_π
    (f : Φ.presheafFiber.obj P ⟶ M) (X : C) (x : Φ.fiber.obj X) :
    (Φ.skyscraperPresheafHomEquiv f).app (op X) ≫ Pi.π (fun (_ : Φ.fiber.obj X) ↦ M) x =
      Φ.toPresheafFiber X x P ≫ f := by
  simp [skyscraperPresheafHomEquiv_apply_app]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**CategoryTheory.GrothendieckTopology.Point.skyscraperPresheafHomEquiv_naturalit
y_right** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.GrothendieckTopology.Point`。
形式化陈述：skyscraperPresheafHomEquiv_naturality_right (f : Φ.presheafFiber.obj P ⟶ M
) (g : M ⟶ N) : Φ.skyscraperPresheafHomEquiv (f ≫ g) = Φ.skyscraperPresheafHomEq
uiv f ≫ Φ.skyscraperPresheafFunctor.map g
参数：f : Φ.presheafFiber.obj P ⟶ M；g : M ⟶ N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.Limits.Pi.hom_ext`：∀ {β : Type w} {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] {f : β → C}   [inst_1 : CategoryTheory.Limits.Ha
sProduct f] {X : C} (g…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用引理 `CategoryTheory.GrothendieckTopology.Point.skyscraperPresheafHomEquiv_app
_π`：skyscraperPresheafHomEquiv_app_π (f : Φ.presheafFiber.obj P ⟶ M) (X : C) (x 
: Φ.fiber.obj X) : (Φ.skyscraperPresheafHomEquiv f).app (op X) ≫…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.Pi.map_π`：∀ {β : Type w} {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {f g : β → C}   [inst_1 : CategoryTheory.Limits.Ha
sProduct f] [inst_2 …
· 使用定理 `CategoryTheory.GrothendieckTopology.Point.skyscraperPresheafHomEquiv_app
_π_assoc`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {J : Category
Theory.GrothendieckTopology C} (Φ : J.Point)   {A : Type u'} [inst_1 :…
-/
lemma skyscraperPresheafHomEquiv_naturality_right
    (f : Φ.presheafFiber.obj P ⟶ M) (g : M ⟶ N) :
    Φ.skyscraperPresheafHomEquiv (f ≫ g) =
      Φ.skyscraperPresheafHomEquiv f ≫ Φ.skyscraperPresheafFunctor.map g := by
  ext
  dsimp
  ext
  dsimp
  rw [skyscraperPresheafHomEquiv_app_π]
  dsimp
  rw [Category.assoc, Pi.map_π, skyscraperPresheafHomEquiv_app_π_assoc]

@[reassoc]
/-
**CategoryTheory.GrothendieckTopology.Point.skyscraperPresheafHomEquiv_naturalit
y_left** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.GrothendieckTopology.Point`。
形式化陈述：skyscraperPresheafHomEquiv_naturality_left (f : P ⟶ Q) (g : Φ.presheafFibe
r.obj Q ⟶ M) : Φ.skyscraperPresheafHomEquiv (Φ.presheafFiber.map f ≫ g) = f ≫ Φ.
skyscraperPresheafHomEquiv g
参数：f : P ⟶ Q；g : Φ.presheafFiber.obj Q ⟶ M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用引理 `CategoryTheory.GrothendieckTopology.Point.skyscraperPresheafHomEquiv_nat
urality_left_symm`：skyscraperPresheafHomEquiv_naturality_left_symm (f : P ⟶ Q) (
g : Q ⟶ Φ.skyscraperPresheaf M) : Φ.skyscraperPresheafHomEquiv.symm (f ≫ g) = Φ…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma skyscraperPresheafHomEquiv_naturality_left
    (f : P ⟶ Q) (g : Φ.presheafFiber.obj Q ⟶ M) :
    Φ.skyscraperPresheafHomEquiv (Φ.presheafFiber.map f ≫ g) =
      f ≫ Φ.skyscraperPresheafHomEquiv g :=
  Φ.skyscraperPresheafHomEquiv.symm.injective
    (by simp [Φ.skyscraperPresheafHomEquiv_naturality_left_symm])

end

section

variable [HasColimitsOfSize.{w, w} A]

/-- Given a point of a site, the skyscraper presheaf functor is right adjoint
to the fiber functor on presheaves. -/
/-
**CategoryTheory.GrothendieckTopology.Point.skyscraperPresheafAdjunction** 是 Mat
hlib 中的一个定义，位于命名空间 `CategoryTheory.GrothendieckTopology.Point`。
形式化陈述：skyscraperPresheafAdjunction : Φ.presheafFiber (A
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.GrothendieckTopology.Point.skyscraperPresheafHomEquiv_nat
urality_left_symm`：skyscraperPresheafHomEquiv_naturality_left_symm (f : P ⟶ Q) (
g : Q ⟶ Φ.skyscraperPresheaf M) : Φ.skyscraperPresheafHomEquiv.symm (f ≫ g) = Φ…
· 使用引理 `CategoryTheory.GrothendieckTopology.Point.skyscraperPresheafHomEquiv_nat
urality_right`：skyscraperPresheafHomEquiv_naturality_right (f : Φ.presheafFiber.
obj P ⟶ M) (g : M ⟶ N) : Φ.skyscraperPresheafHomEquiv (f ≫ g) = Φ.skyscrape…

--- 原说明 ---
Given a point of a site, the skyscraper presheaf functor is right adjoint
to the fiber functor on presheaves.
-/
noncomputable def skyscraperPresheafAdjunction :
    Φ.presheafFiber (A := A) ⊣ Φ.skyscraperPresheafFunctor :=
  Adjunction.mkOfHomEquiv
    { homEquiv _ _ := Φ.skyscraperPresheafHomEquiv
      homEquiv_naturality_left_symm _ _ := Φ.skyscraperPresheafHomEquiv_naturality_left_symm _ _
      homEquiv_naturality_right _ _ := Φ.skyscraperPresheafHomEquiv_naturality_right _ _ }

@[simp]
/-
**CategoryTheory.GrothendieckTopology.Point.skyscraperPresheafAdjunction_homEqui
v_apply** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.GrothendieckTopology.Point`。
形式化陈述：skyscraperPresheafAdjunction_homEquiv_apply {P : Cᵒᵖ ⥤ A} {M : A} (f : Φ.p
resheafFiber.obj P ⟶ M) : Φ.skyscraperPresheafAdjunction.homEquiv _ _ f = Φ.skys
craperPresheafHomEquiv f
参数：f : Φ.presheafFiber.obj P ⟶ M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.GrothendieckTopology.Point.skyscraperPresheafHomEquiv_nat
urality_left_symm`：skyscraperPresheafHomEquiv_naturality_left_symm (f : P ⟶ Q) (
g : Q ⟶ Φ.skyscraperPresheaf M) : Φ.skyscraperPresheafHomEquiv.symm (f ≫ g) = Φ…
· 使用引理 `CategoryTheory.GrothendieckTopology.Point.skyscraperPresheafHomEquiv_nat
urality_right`：skyscraperPresheafHomEquiv_naturality_right (f : Φ.presheafFiber.
obj P ⟶ M) (g : M ⟶ N) : Φ.skyscraperPresheafHomEquiv (f ≫ g) = Φ.skyscrape…
· 使用引理 `CategoryTheory.Adjunction.mkOfHomEquiv_homEquiv`：mkOfHomEquiv_homEquiv (
adj : CoreHomEquiv F G) : (mkOfHomEquiv adj).homEquiv = adj.homEquiv
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma skyscraperPresheafAdjunction_homEquiv_apply {P : Cᵒᵖ ⥤ A} {M : A}
    (f : Φ.presheafFiber.obj P ⟶ M) :
    Φ.skyscraperPresheafAdjunction.homEquiv _ _ f =
      Φ.skyscraperPresheafHomEquiv f := by
  simp [skyscraperPresheafAdjunction]

@[simp]
/-
**CategoryTheory.GrothendieckTopology.Point.skyscraperPresheafAdjunction_homEqui
v_symm_apply** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.GrothendieckTopology.Poin
t`。
形式化陈述：skyscraperPresheafAdjunction_homEquiv_symm_apply {P : Cᵒᵖ ⥤ A} {M : A} (f 
: P ⟶ Φ.skyscraperPresheaf M) : (Φ.skyscraperPresheafAdjunction.homEquiv _ _).sy
mm f = Φ.skyscraperPresheafHomEquiv.symm f
参数：f : P ⟶ Φ.skyscraperPresheaf M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.GrothendieckTopology.Point.skyscraperPresheafHomEquiv_nat
urality_left_symm`：skyscraperPresheafHomEquiv_naturality_left_symm (f : P ⟶ Q) (
g : Q ⟶ Φ.skyscraperPresheaf M) : Φ.skyscraperPresheafHomEquiv.symm (f ≫ g) = Φ…
· 使用引理 `CategoryTheory.GrothendieckTopology.Point.skyscraperPresheafHomEquiv_nat
urality_right`：skyscraperPresheafHomEquiv_naturality_right (f : Φ.presheafFiber.
obj P ⟶ M) (g : M ⟶ N) : Φ.skyscraperPresheafHomEquiv (f ≫ g) = Φ.skyscrape…
· 使用引理 `CategoryTheory.Adjunction.mkOfHomEquiv_homEquiv`：mkOfHomEquiv_homEquiv (
adj : CoreHomEquiv F G) : (mkOfHomEquiv adj).homEquiv = adj.homEquiv
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma skyscraperPresheafAdjunction_homEquiv_symm_apply {P : Cᵒᵖ ⥤ A} {M : A}
    (f : P ⟶ Φ.skyscraperPresheaf M) :
    (Φ.skyscraperPresheafAdjunction.homEquiv _ _).symm f =
      Φ.skyscraperPresheafHomEquiv.symm f := by
  simp [skyscraperPresheafAdjunction]

end

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
variable {Φ} in
/-
**CategoryTheory.GrothendieckTopology.Point.isSheaf_skyscraperPresheaf_aux** 是 M
athlib 中的一个引理，位于命名空间 `CategoryTheory.GrothendieckTopology.Point`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma isSheaf_skyscraperPresheaf_aux
    {M : A} {X : C} (R : Sieve X) (hR : R ∈ J X)
    (s : Cone (R.arrows.diagram.op ⋙ Φ.skyscraperPresheaf M)) :
    ∃ (l : s.pt ⟶ ∏ᶜ fun (_ : Φ.fiber.obj X) ↦ M),
      ∀ (j : R.arrows.category) (y : Φ.fiber.obj j.obj.left),
        l ≫ Pi.π _ (Φ.fiber.map j.obj.hom y) = s.π.app (op j) ≫ Pi.π _ y := by
  suffices ∀ (x : Φ.fiber.obj X), ∃ (l : s.pt ⟶ M),
      ∀ ⦃Y : C⦄ (g : Y ⟶ X) (hg : R g) (y : Φ.fiber.obj Y) (hy : Φ.fiber.map g y = x),
        s.π.app (op (Presieve.categoryMk _ _ hg)) ≫ Pi.π _ y = l by
    choose l hl using this
    exact ⟨Pi.lift l, fun j y ↦ by simpa using! (hl _ j.obj.hom  j.property y rfl).symm⟩
  intro x
  obtain ⟨Y₁, f₁, hf₁, y₁, hy₁⟩ := Φ.jointly_surjective _ hR x
  refine ⟨s.π.app (op (Presieve.categoryMk _ _ hf₁)) ≫ Pi.π _ y₁,
    fun Y₂ f₂ hf₂ y₂ hy₂ ↦ ?_⟩
  obtain ⟨Z, p₁, p₂, z, fac, hz₁, hz₂⟩ :
      ∃ (Z : C) (p₁ : Z ⟶ Y₁) (p₂ : Z ⟶ Y₂) (z : Φ.fiber.obj Z), p₁ ≫ f₁ = p₂ ≫ f₂ ∧
        Φ.fiber.map p₁ z = y₁ ∧ Φ.fiber.map p₂ z = y₂ := by
    let α₁ : Φ.fiber.elementsMk _ y₁ ⟶ Φ.fiber.elementsMk _ x := ⟨f₁, hy₁⟩
    let α₂ : Φ.fiber.elementsMk _ y₂ ⟶ Φ.fiber.elementsMk _ x := ⟨f₂, hy₂⟩
    obtain ⟨z, q₁, q₂, fac⟩ := IsCofiltered.cospan α₁ α₂
    rw [Subtype.ext_iff] at fac
    refine ⟨z.1, q₁.1, q₂.1, z.2, fac, ?_, ?_⟩
    all_goals rw [CategoryOfElements.map_snd] -- was `simp`
  let φ₁ : Presieve.categoryMk _ _ (R.downward_closed hf₁ p₁) ⟶
      Presieve.categoryMk _ _ hf₁ :=
    ObjectProperty.homMk (Over.homMk p₁)
  let φ₂ : Presieve.categoryMk _ _ (R.downward_closed hf₁ p₁) ⟶
      Presieve.categoryMk _ _ hf₂ :=
    ObjectProperty.homMk (Over.homMk p₂)
  simpa [hz₁, hz₂, φ₁, φ₂] using!
    (Cone.w s φ₂.op =≫ Pi.π _ z).trans (Cone.w s φ₁.op =≫ Pi.π _ z).symm

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.GrothendieckTopology.Point.isSheaf_skyscraperPresheaf** 是 Mathl
ib 中的一个引理，位于命名空间 `CategoryTheory.GrothendieckTopology.Point`。
形式化陈述：isSheaf_skyscraperPresheaf (M : A) : Presheaf.IsSheaf J (Φ.skyscraperPresh
eaf M)
参数：M : A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Presheaf.isSheaf_iff_isLimit`：isSheaf_iff_isLimit : IsShe
af J P ↔ forall ⦃X : C⦄ (S : Sieve X), S in J X -> Nonempty (IsLimit (P.mapCone 
S.arrows.cocone.op))
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `_private.Mathlib.CategoryTheory.Sites.Point.Skyscraper.0.CategoryTheory.
GrothendieckTopology.Point.isSheaf_skyscraperPresheaf_aux`：∀ {C : Type u} [inst 
: CategoryTheory.Category.{v, u} C] {J : CategoryTheory.GrothendieckTopology C} 
{Φ : J.Point}   {A : Type u'} [inst_1 :…
· 使用定理 `CategoryTheory.Limits.Pi.hom_ext`：∀ {β : Type w} {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] {f : β → C}   [inst_1 : CategoryTheory.Limits.Ha
sProduct f] {X : C} (g…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.Pi.map'_comp_π`：∀ {β : Type w} {α : Type w₂} {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] {f : α → C} {g : β → C}   [ins
t_1 : CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `CategoryTheory.GrothendieckTopology.Point.jointly_surjective`：∀ {C : Typ
e u} [inst : CategoryTheory.Category.{v, u} C] {J : CategoryTheory.GrothendieckT
opology C} (self : J.Point)   {X : C},   ∀ R ∈ J X…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma isSheaf_skyscraperPresheaf (M : A) :
    Presheaf.IsSheaf J (Φ.skyscraperPresheaf M) := by
  rw [Presheaf.isSheaf_iff_isLimit]
  intro X R hR
  exact ⟨{
    lift s := (isSheaf_skyscraperPresheaf_aux R hR s).choose
    fac s j := by
      dsimp
      ext y
      simpa using! (isSheaf_skyscraperPresheaf_aux R hR s).choose_spec _ y
    uniq s m hm := by
      dsimp at hm ⊢
      ext x
      obtain ⟨Y, g, hg, y, rfl⟩ := Φ.jointly_surjective _ hR x
      simpa [← hm (op (Presieve.categoryMk _ _ hg))] using!
        ((isSheaf_skyscraperPresheaf_aux R hR s).choose_spec (Presieve.categoryMk _ _ hg) y).symm }⟩

/-- Given a point `Φ` of a site `(C, J)`, this is the skyscraper sheaf functor
`A ⥤ Sheaf J A`. -/
@[simps]
/-
**CategoryTheory.GrothendieckTopology.Point.skyscraperSheafFunctor** 是 Mathlib 中
的一个定义，位于命名空间 `CategoryTheory.GrothendieckTopology.Point`。
形式化陈述：skyscraperSheafFunctor : A ⥤ Sheaf J A where obj M
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.GrothendieckTopology.Point.isSheaf_skyscraperPresheaf`：is
Sheaf_skyscraperPresheaf (M : A) : Presheaf.IsSheaf J (Φ.skyscraperPresheaf M)

--- 原说明 ---
Given a point `Φ` of a site `(C, J)`, this is the skyscraper sheaf functor
`A ⥤ Sheaf J A`.
-/
noncomputable def skyscraperSheafFunctor : A ⥤ Sheaf J A where
  obj M := ⟨Φ.skyscraperPresheaf M, Φ.isSheaf_skyscraperPresheaf M⟩
  map f := ⟨Φ.skyscraperPresheafFunctor.map f⟩

/-- Given a point `Φ` on a site `(C, J)`, and an object `M` of a category `A`,
this is the skyscraper sheaf with value `M`: it sends `X : C` to the
product of copies of `M` indexed by `Φ.fiber.obj X`. -/
/-
**CategoryTheory.GrothendieckTopology.Point.skyscraperSheaf** 是 Mathlib 中的一个缩写定义
，位于命名空间 `CategoryTheory.GrothendieckTopology.Point`。
形式化陈述：skyscraperSheaf (M : A) : Sheaf J A
参数：M : A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a point `Φ` on a site `(C, J)`, and an object `M` of a category `A`,
this is the skyscraper sheaf with value `M`: it sends `X : C` to the
product of copies of `M` indexed by `Φ.fiber.obj X`.
-/
noncomputable abbrev skyscraperSheaf (M : A) :
    Sheaf J A :=
  Φ.skyscraperSheafFunctor.obj M

variable [HasColimitsOfSize.{w, w} A]

/-- Given a point of a site, the skyscraper sheaf functor is right adjoint
to the fiber functor on sheaves. -/
/-
**CategoryTheory.GrothendieckTopology.Point.skyscraperSheafAdjunction** 是 Mathli
b 中的一个定义，位于命名空间 `CategoryTheory.GrothendieckTopology.Point`。
形式化陈述：skyscraperSheafAdjunction : Φ.sheafFiber (A
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Given a point of a site, the skyscraper sheaf functor is right adjoint
to the fiber functor on sheaves.
-/
noncomputable def skyscraperSheafAdjunction :
    Φ.sheafFiber (A := A) ⊣ Φ.skyscraperSheafFunctor :=
  Adjunction.mkOfHomEquiv
    { homEquiv F M :=
        Φ.skyscraperPresheafHomEquiv.trans
          ((fullyFaithfulSheafToPresheaf J A).homEquiv (Y := Φ.skyscraperSheaf M)).symm
      homEquiv_naturality_left_symm f g :=
        Φ.skyscraperPresheafHomEquiv_naturality_left_symm f.hom g.hom
      homEquiv_naturality_right f g := by
        ext : 1
        exact Φ.skyscraperPresheafHomEquiv_naturality_right f g }
/-
**CategoryTheory.GrothendieckTopology.Point.** 是 Mathlib 中的一个实例，位于命名空间 `Category
Theory.GrothendieckTopology.Point`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (Φ.sheafFiber (A := A)).IsLeftAdjoint :=
  Φ.skyscraperSheafAdjunction.isLeftAdjoint
/-
**CategoryTheory.GrothendieckTopology.Point.** 是 Mathlib 中的一个实例，位于命名空间 `Category
Theory.GrothendieckTopology.Point`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (Φ.skyscraperSheafFunctor (A := A)).IsRightAdjoint :=
  Φ.skyscraperSheafAdjunction.isRightAdjoint

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simp]
/-
**CategoryTheory.GrothendieckTopology.Point.skyscraperSheafAdjunction_homEquiv_a
pply_hom** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.GrothendieckTopology.Point`。
形式化陈述：skyscraperSheafAdjunction_homEquiv_apply_hom {F : Sheaf J A} {M : A} (f : 
Φ.presheafFiber.obj F.obj ⟶ M) : letI e : (Φ.presheafFiber.obj F.obj ⟶ M) ≃ _
参数：f : Φ.presheafFiber.obj F.obj ⟶ M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用引理 `CategoryTheory.Adjunction.mkOfHomEquiv_homEquiv`：mkOfHomEquiv_homEquiv (
adj : CoreHomEquiv F G) : (mkOfHomEquiv adj).homEquiv = adj.homEquiv
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma skyscraperSheafAdjunction_homEquiv_apply_hom {F : Sheaf J A} {M : A}
    (f : Φ.presheafFiber.obj F.obj ⟶ M) :
    letI e : (Φ.presheafFiber.obj F.obj ⟶ M) ≃ _ := Φ.skyscraperSheafAdjunction.homEquiv F M
    letI a : F.obj ⟶ Φ.skyscraperPresheaf M := (e f).hom
    a = Φ.skyscraperPresheafHomEquiv f := by
  simp [skyscraperSheafAdjunction, Functor.FullyFaithful.homEquiv]

@[deprecated (since := "2026-03-05")]
alias skyscraperSheafAdjunction_homEquiv_apply_val :=
  skyscraperSheafAdjunction_homEquiv_apply_hom

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simp]
/-
**CategoryTheory.GrothendieckTopology.Point.skyscraperSheafAdjunction_homEquiv_s
ymm_apply** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.GrothendieckTopology.Point`。
形式化陈述：skyscraperSheafAdjunction_homEquiv_symm_apply {F : Sheaf J A} {M : A} (f :
 F ⟶ Φ.skyscraperSheaf M) : letI e : (Φ.presheafFiber.obj F.obj ⟶ M) ≃ _
参数：f : F ⟶ Φ.skyscraperSheaf M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用引理 `CategoryTheory.Adjunction.mkOfHomEquiv_homEquiv`：mkOfHomEquiv_homEquiv (
adj : CoreHomEquiv F G) : (mkOfHomEquiv adj).homEquiv = adj.homEquiv
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma skyscraperSheafAdjunction_homEquiv_symm_apply {F : Sheaf J A} {M : A}
    (f : F ⟶ Φ.skyscraperSheaf M) :
    letI e : (Φ.presheafFiber.obj F.obj ⟶ M) ≃ _ := Φ.skyscraperSheafAdjunction.homEquiv F M
    e.symm f = Φ.skyscraperPresheafHomEquiv.symm f.hom := by
  simp [skyscraperSheafAdjunction, Functor.FullyFaithful.homEquiv]
/-
**CategoryTheory.GrothendieckTopology.Point.W_isInvertedBy_presheafFiber** 是 Mat
hlib 中的一个引理，位于命名空间 `CategoryTheory.GrothendieckTopology.Point`。
形式化陈述：W_isInvertedBy_presheafFiber : J.W.IsInvertedBy (Φ.presheafFiber (A
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.isIso_iff_coyoneda_map_bijective`：isIso_iff_coyoneda_map_
bijective {X Y : C} (f : X ⟶ Y) : IsIso f ↔ (forall (T : C), Function.Bijective 
(fun (x : Y ⟶ T) => f ≫ x))
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Bijective.of_comp_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {γ : So
rt u_3} {f : α → β},   Function.Bijective f → ∀ (g : γ → α), Function.Bijective 
(f ∘ g) ↔ Function.Bi…
· 使用定理 `Equiv.bijective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Bijec
tive ⇑e
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `CategoryTheory.GrothendieckTopology.Point.skyscraperPresheafHomEquiv_nat
urality_left`：skyscraperPresheafHomEquiv_naturality_left (f : P ⟶ Q) (g : Φ.pres
heafFiber.obj Q ⟶ M) : Φ.skyscraperPresheafHomEquiv (Φ.presheafFiber.map f…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Function.Bijective.comp`：∀ {α : Sort u₁} {β : Sort u₂} {φ : Sort u₃} {g 
: β → φ} {f : α → β},   Function.Bijective g → Function.Bijective f → Function.B
ijective (g ∘…
· 使用引理 `CategoryTheory.GrothendieckTopology.Point.isSheaf_skyscraperPresheaf`：is
Sheaf_skyscraperPresheaf (M : A) : Presheaf.IsSheaf J (Φ.skyscraperPresheaf M)
-/
lemma W_isInvertedBy_presheafFiber :
    J.W.IsInvertedBy (Φ.presheafFiber (A := A)) := by
  intro P₁ P₂ f hf
  rw [isIso_iff_coyoneda_map_bijective]
  intro M
  rw [← Function.Bijective.of_comp_iff' Φ.skyscraperPresheafHomEquiv.bijective]
  convert! (hf _ (Φ.isSheaf_skyscraperPresheaf M)).comp Φ.skyscraperPresheafHomEquiv.bijective
  ext g : 1
  simp [skyscraperPresheafHomEquiv_naturality_left]
/-
**CategoryTheory.GrothendieckTopology.Point.** 是 Mathlib 中的一个实例，位于命名空间 `Category
Theory.GrothendieckTopology.Point`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (P : Cᵒᵖ ⥤ A) [HasWeakSheafify J A] :
    IsIso (Φ.presheafFiber.map (CategoryTheory.toSheafify J P)) :=
  W_isInvertedBy_presheafFiber _ _ (W_toSheafify J P)

set_option backward.isDefEq.respectTransparency false in
variable (A) in
/-- The fiber functor on sheaves is obtained from the fiber functor on presheaves
by localization with respect to the class of morphisms `J.W`. -/
/-
**CategoryTheory.GrothendieckTopology.Point.presheafToSheafCompSheafFiberIso** 是
 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.GrothendieckTopology.Point`。
形式化陈述：presheafToSheafCompSheafFiberIso [HasWeakSheafify J A] : presheafToSheaf J
 A ⋙ Φ.sheafFiber ≅ Φ.presheafFiber
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrothendieckTopology.Point.instIsIsoMapFunctorOppositePre
sheafFiberToSheafify`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {
J : CategoryTheory.GrothendieckTopology C} (Φ : J.Point)   {A : Type u'} [inst_1
 :…

--- 原说明 ---
The fiber functor on sheaves is obtained from the fiber functor on presheaves
by localization with respect to the class of morphisms `J.W`.
-/
noncomputable def presheafToSheafCompSheafFiberIso [HasWeakSheafify J A] :
    presheafToSheaf J A ⋙ Φ.sheafFiber ≅ Φ.presheafFiber :=
  (NatIso.ofComponents
    (fun P ↦ asIso ((Φ.presheafFiber (A := A)).map (CategoryTheory.toSheafify J P) :))
      (by simp [sheafFiber, ← Functor.map_comp])).symm

@[deprecated (since := "2026-03-08")]
alias presheafToSheafCompSheafFiber := presheafToSheafCompSheafFiberIso
/-
**CategoryTheory.GrothendieckTopology.Point.** 是 Mathlib 中的一个实例，位于命名空间 `Category
Theory.GrothendieckTopology.Point`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance [HasWeakSheafify J A] :
    Localization.Lifting (presheafToSheaf J A) J.W
      Φ.presheafFiber Φ.sheafFiber where
  iso := Φ.presheafToSheafCompSheafFiberIso A
/-
**CategoryTheory.GrothendieckTopology.Point.** 是 Mathlib 中的一个实例，位于命名空间 `Category
Theory.GrothendieckTopology.Point`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PreservesFiniteColimits (Φ.sheafFiber (A := A)) :=
  have : PreservesColimitsOfSize.{w, w} (Φ.sheafFiber (A := A)) := inferInstance
  PreservesColimitsOfSize.preservesFiniteColimits _

end CategoryTheory.GrothendieckTopology.Point

