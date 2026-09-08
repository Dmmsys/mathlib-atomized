/-
Copyright (c) 2018 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Johannes Hölzl, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.PUnit

/-!
# Category instances for `Semiring`, `Ring`, `CommSemiring`, and `CommRing`.

We introduce the bundled categories:
* `SemiRingCat`
* `RingCat`
* `CommSemiRingCat`
* `CommRingCat`

along with the relevant forgetful functors between them.
-/

@[expose] public section

universe u v

open CategoryTheory

/-- The category of semirings. -/
/-
**SemiRingCat** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type (u + 1)
参数：u + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of semirings.
-/
structure SemiRingCat where
  /-- The object in the category of semirings associated to a type equipped with the appropriate
  typeclasses. -/
  of ::
  /-- The underlying type. -/
  carrier : Type u
  [semiring : Semiring carrier]

section Notation

open Lean.PrettyPrinter.Delaborator

/-- This prevents `SemiRingCat.of R` being printed as `{ carrier := R, semiring := ... }` by
`delabStructureInstance`. -/
@[app_delab SemiRingCat.of]
meta def SemiRingCat.delabOf : Delab := delabApp

end Notation

attribute [instance] SemiRingCat.semiring

initialize_simps_projections SemiRingCat (-semiring)

namespace SemiRingCat

/-
**SemiRingCat.** 是 Mathlib 中的一个实例，位于命名空间 `SemiRingCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeSort SemiRingCat (Type u) :=
  ⟨SemiRingCat.carrier⟩

attribute [coe] SemiRingCat.carrier
/-
**SemiRingCat.coe_of** 是 Mathlib 中的一个引理，位于命名空间 `SemiRingCat`。
形式化陈述：coe_of (R : Type u) [Semiring R] : (of R : Type u) = R
参数：R : Type u。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_of (R : Type u) [Semiring R] : (of R : Type u) = R :=
  rfl
/-
**SemiRingCat.of_carrier** 是 Mathlib 中的一个引理，位于命名空间 `SemiRingCat`。
形式化陈述：of_carrier (R : SemiRingCat.{u}) : of R = R
参数：R : SemiRingCat.{u}。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma of_carrier (R : SemiRingCat.{u}) : of R = R := rfl

variable {R} in
/-- The type of morphisms in `SemiRingCat`. -/
@[ext]
/-
**SemiRingCat.Hom** 是 Mathlib 中的一个归纳类型，位于命名空间 `SemiRingCat`。
形式化陈述：SemiRingCat → SemiRingCat → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of morphisms in `SemiRingCat`.
-/
structure Hom (R S : SemiRingCat.{u}) where
  private mk ::
  /-- The underlying ring hom. -/
  hom' : R →+* S

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**SemiRingCat.** 是 Mathlib 中的一个实例，位于命名空间 `SemiRingCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Category SemiRingCat where
  Hom R S := Hom R S
  id R := ⟨RingHom.id R⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**SemiRingCat.** 是 Mathlib 中的一个实例，位于命名空间 `SemiRingCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ConcreteCategory.{u} SemiRingCat (fun R S => R →+* S) where
  hom := Hom.hom'
  ofHom f := ⟨f⟩

/-- Turn a morphism in `SemiRingCat` back into a `RingHom`. -/
/-
**SemiRingCat.Hom.hom** 是 Mathlib 中的一个定义，位于命名空间 `SemiRingCat.Hom`。
形式化陈述：{R S : SemiRingCat} → R.Hom S → ↑R →+* ↑S
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turn a morphism in `SemiRingCat` back into a `RingHom`.
-/
abbrev Hom.hom {R S : SemiRingCat.{u}} (f : Hom R S) :=
  ConcreteCategory.hom (C := SemiRingCat) f

/-- Typecheck a `RingHom` as a morphism in `SemiRingCat`. -/
/-
**SemiRingCat.ofHom** 是 Mathlib 中的一个缩写定义，位于命名空间 `SemiRingCat`。
形式化陈述：ofHom {R S : Type u} [Semiring R] [Semiring S] (f : R ->+* S) : of R ⟶ of 
S
参数：f : R ->+* S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typecheck a `RingHom` as a morphism in `SemiRingCat`.
-/
abbrev ofHom {R S : Type u} [Semiring R] [Semiring S] (f : R →+* S) : of R ⟶ of S :=
  ConcreteCategory.ofHom (C := SemiRingCat) f

/-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/
/-
**SemiRingCat.Hom.Simps.hom** 是 Mathlib 中的一个定义，位于命名空间 `SemiRingCat.Hom.Simps`。
形式化陈述：(R S : SemiRingCat) → R.Hom S → ↑R →+* ↑S
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas.
-/
def Hom.Simps.hom (R S : SemiRingCat) (f : Hom R S) :=
  f.hom

initialize_simps_projections Hom (hom' → hom)

/-!
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep them for `dsimp`.
-/

@[simp]
/-
**SemiRingCat.hom_id** 是 Mathlib 中的一个引理，位于命名空间 `SemiRingCat`。
形式化陈述：hom_id {R : SemiRingCat} : (𝟙 R : R ⟶ R).hom = RingHom.id R
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep 
them for `dsimp`.
-/
lemma hom_id {R : SemiRingCat} : (𝟙 R : R ⟶ R).hom = RingHom.id R := rfl

/- Provided for rewriting. -/
/-
**SemiRingCat.id_apply** 是 Mathlib 中的一个引理，位于命名空间 `SemiRingCat`。
形式化陈述：id_apply (R : SemiRingCat) (r : R) : (𝟙 R : R ⟶ R) r = r
参数：R : SemiRingCat；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Provided for rewriting.
-/
lemma id_apply (R : SemiRingCat) (r : R) :
    (𝟙 R : R ⟶ R) r = r := by simp

@[simp]
/-
**SemiRingCat.hom_comp** 是 Mathlib 中的一个引理，位于命名空间 `SemiRingCat`。
形式化陈述：hom_comp {R S T : SemiRingCat} (f : R ⟶ S) (g : S ⟶ T) : (f ≫ g).hom = g.h
om.comp f.hom
参数：f : R ⟶ S；g : S ⟶ T。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_comp {R S T : SemiRingCat} (f : R ⟶ S) (g : S ⟶ T) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

/- Provided for rewriting. -/
/-
**SemiRingCat.comp_apply** 是 Mathlib 中的一个引理，位于命名空间 `SemiRingCat`。
形式化陈述：comp_apply {R S T : SemiRingCat} (f : R ⟶ S) (g : S ⟶ T) (r : R) : (f ≫ g)
 r = g (f r)
参数：f : R ⟶ S；g : S ⟶ T；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Provided for rewriting.
-/
lemma comp_apply {R S T : SemiRingCat} (f : R ⟶ S) (g : S ⟶ T) (r : R) :
    (f ≫ g) r = g (f r) := by simp

@[ext]
/-
**SemiRingCat.hom_ext** 是 Mathlib 中的一个引理，位于命名空间 `SemiRingCat`。
形式化陈述：hom_ext {R S : SemiRingCat} {f g : R ⟶ S} (hf : f.hom = g.hom) : f = g
参数：hf : f.hom = g.hom。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemiRingCat.Hom.ext`：∀ {R S : SemiRingCat} {x y : R.Hom S}, x.hom' = y.h
om' → x = y
-/
lemma hom_ext {R S : SemiRingCat} {f g : R ⟶ S} (hf : f.hom = g.hom) : f = g :=
  Hom.ext hf

@[simp]
/-
**SemiRingCat.hom_ofHom** 是 Mathlib 中的一个引理，位于命名空间 `SemiRingCat`。
形式化陈述：hom_ofHom {R S : Type u} [Semiring R] [Semiring S] (f : R ->+* S) : (ofHom
 f).hom = f
参数：f : R ->+* S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_ofHom {R S : Type u} [Semiring R] [Semiring S] (f : R →+* S) : (ofHom f).hom = f := rfl

@[simp]
/-
**SemiRingCat.ofHom_hom** 是 Mathlib 中的一个引理，位于命名空间 `SemiRingCat`。
形式化陈述：ofHom_hom {R S : SemiRingCat} (f : R ⟶ S) : ofHom (Hom.hom f) = f
参数：f : R ⟶ S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_hom {R S : SemiRingCat} (f : R ⟶ S) :
    ofHom (Hom.hom f) = f := rfl

@[simp]
/-
**SemiRingCat.ofHom_id** 是 Mathlib 中的一个引理，位于命名空间 `SemiRingCat`。
形式化陈述：ofHom_id {R : Type u} [Semiring R] : ofHom (RingHom.id R) = 𝟙 (of R)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_id {R : Type u} [Semiring R] : ofHom (RingHom.id R) = 𝟙 (of R) := rfl

@[simp]
/-
**SemiRingCat.ofHom_comp** 是 Mathlib 中的一个引理，位于命名空间 `SemiRingCat`。
形式化陈述：ofHom_comp {R S T : Type u} [Semiring R] [Semiring S] [Semiring T] (f : R 
->+* S) (g : S ->+* T) : ofHom (g.comp f) = ofHom f ≫ ofHom g
参数：f : R ->+* S；g : S ->+* T。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_comp {R S T : Type u} [Semiring R] [Semiring S] [Semiring T]
    (f : R →+* S) (g : S →+* T) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g :=
  rfl
/-
**SemiRingCat.ofHom_apply** 是 Mathlib 中的一个引理，位于命名空间 `SemiRingCat`。
形式化陈述：ofHom_apply {R S : Type u} [Semiring R] [Semiring S] (f : R ->+* S) (r : R
) : ofHom f r = f r
参数：f : R ->+* S；r : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_apply {R S : Type u} [Semiring R] [Semiring S]
    (f : R →+* S) (r : R) : ofHom f r = f r := rfl
/-
**SemiRingCat.inv_hom_apply** 是 Mathlib 中的一个引理，位于命名空间 `SemiRingCat`。
形式化陈述：inv_hom_apply {R S : SemiRingCat} (e : R ≅ S) (r : R) : e.inv (e.hom r) = 
r
参数：e : R ≅ S；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.hom_inv_id_apply`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {F : C → C → Type uF}   {carrier 
: C → Type w} {instFunLik…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma inv_hom_apply {R S : SemiRingCat} (e : R ≅ S) (r : R) : e.inv (e.hom r) = r := by
  simp
/-
**SemiRingCat.hom_inv_apply** 是 Mathlib 中的一个引理，位于命名空间 `SemiRingCat`。
形式化陈述：hom_inv_apply {R S : SemiRingCat} (e : R ≅ S) (s : S) : e.hom (e.inv s) = 
s
参数：e : R ≅ S；s : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.inv_hom_id_apply`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {F : C → C → Type uF}   {carrier 
: C → Type w} {instFunLik…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma hom_inv_apply {R S : SemiRingCat} (e : R ≅ S) (s : S) : e.hom (e.inv s) = s := by
  simp
/-
**SemiRingCat.** 是 Mathlib 中的一个实例，位于命名空间 `SemiRingCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited SemiRingCat :=
  ⟨of PUnit⟩

/-- This unification hint helps with problems of the form `(forget ?C).obj R =?= carrier R'`. -/
unif_hint forget_obj_eq_coe (R R' : SemiRingCat) where
  R ≟ R' ⊢
  (forget SemiRingCat).obj R ≟ SemiRingCat.carrier R'

@[deprecated (since := "2026-02-16")] alias forget_obj := CategoryTheory.forget_obj
@[deprecated (since := "2026-02-16")] alias forget_map := ConcreteCategory.forget_map_eq_ofHom

/-
**SemiRingCat.** 是 Mathlib 中的一个实例，位于命名空间 `SemiRingCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R : SemiRingCat} : Semiring ((forget SemiRingCat).obj R) :=
  inferInstanceAs <| Semiring R.carrier
/-
**SemiRingCat.hasForgetToMonCat** 是 Mathlib 中的一个实例，位于命名空间 `SemiRingCat`。
形式化陈述：hasForgetToMonCat : HasForget₂ SemiRingCat MonCat where forget₂
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasForgetToMonCat : HasForget₂ SemiRingCat MonCat where
  forget₂ :=
    { obj := fun R ↦ MonCat.of R
      map := fun f ↦ MonCat.ofHom f.hom.toMonoidHom }
/-
**SemiRingCat.hasForgetToAddCommMonCat** 是 Mathlib 中的一个实例，位于命名空间 `SemiRingCat`。
形式化陈述：hasForgetToAddCommMonCat : HasForget₂ SemiRingCat AddCommMonCat where forg
et₂
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasForgetToAddCommMonCat : HasForget₂ SemiRingCat AddCommMonCat where
  forget₂ :=
    { obj := fun R ↦ AddCommMonCat.of R
      map := fun f ↦ AddCommMonCat.ofHom f.hom.toAddMonoidHom }
/-
**SemiRingCat.forget** 是 Mathlib 中的一个引理，位于命名空间 `SemiRingCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma forget₂_monCat_map {R S : SemiRingCat} (f : R ⟶ S) (x) :
    (forget₂ SemiRingCat MonCat).map f x = f x := rfl
/-
**SemiRingCat.forget** 是 Mathlib 中的一个引理，位于命名空间 `SemiRingCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma forget₂_addCommMonCat_map {R S : SemiRingCat} (f : R ⟶ S) (x) :
    (forget₂ SemiRingCat AddCommMonCat).map f x = f x := rfl

/-- Ring equivalences are isomorphisms in category of semirings -/
@[simps]
/-
**SemiRingCat._root_.RingEquiv.toSemiRingCatIso** 是 Mathlib 中的一个定义，位于命名空间 `SemiR
ingCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Ring equivalences are isomorphisms in category of semirings
-/
def _root_.RingEquiv.toSemiRingCatIso {R S : Type u} [Semiring R] [Semiring S] (e : R ≃+* S) :
    of R ≅ of S where
  hom := ofHom e
  inv := ofHom e.symm
/-
**SemiRingCat.forgetReflectIsos** 是 Mathlib 中的一个实例，位于命名空间 `SemiRingCat`。
形式化陈述：forgetReflectIsos : (forget SemiRingCat).ReflectsIsomorphisms where reflec
ts {X Y} f _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.left_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Function
.LeftInverse self.invFun self.toFun
· 使用定理 `Equiv.right_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Functio
n.RightInverse self.invFun self.toFun
· 使用定理 `MonoidHom.map_mul'`：∀ {M : Type u_10} {N : Type u_11} [inst : MulOne M] 
[inst_1 : MulOne N] (self : M →* N) (x y : M),   (↑self).toFun (x * y) = (↑self)
.toFun x…
· 使用定理 `RingHom.map_add'`：∀ {α : Type u_5} {β : Type u_6} [inst : NonAssocSemiri
ng α] [inst_1 : NonAssocSemiring β] (self : α →+* β) (x y : α),   (↑↑self).toFun
 (x + …
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
-/
instance forgetReflectIsos : (forget SemiRingCat).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    let i := asIso ((forget SemiRingCat).map f)
    let ff : X →+* Y := f.hom
    let e : X ≃+* Y := { ff, i.toEquiv with }
    exact e.toSemiRingCatIso.isIso_hom

end SemiRingCat

/-- The category of rings. -/
/-
**RingCat** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type (u + 1)
参数：u + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of rings.
-/
structure RingCat where
  /-- The object in the category of rings associated to a type equipped with the appropriate
  typeclasses. -/
  of ::
  /-- The underlying type. -/
  carrier : Type u
  [ring : Ring carrier]

section Notation

open Lean.PrettyPrinter.Delaborator

/-- This prevents `RingCat.of R` being printed as `{ carrier := R, ring := ... }` by
`delabStructureInstance`. -/
@[app_delab RingCat.of]
meta def RingCat.delabOf : Delab := delabApp

end Notation

attribute [instance] RingCat.ring

initialize_simps_projections RingCat (-ring)

namespace RingCat

/-
**RingCat.** 是 Mathlib 中的一个实例，位于命名空间 `RingCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeSort RingCat (Type u) :=
  ⟨RingCat.carrier⟩

attribute [coe] RingCat.carrier
/-
**RingCat.coe_of** 是 Mathlib 中的一个引理，位于命名空间 `RingCat`。
形式化陈述：coe_of (R : Type u) [Ring R] : (of R : Type u) = R
参数：R : Type u。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_of (R : Type u) [Ring R] : (of R : Type u) = R :=
  rfl
/-
**RingCat.of_carrier** 是 Mathlib 中的一个引理，位于命名空间 `RingCat`。
形式化陈述：of_carrier (R : RingCat.{u}) : of R = R
参数：R : RingCat.{u}。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma of_carrier (R : RingCat.{u}) : of R = R := rfl

variable {R} in
/-- The type of morphisms in `RingCat`. -/
@[ext]
/-
**RingCat.Hom** 是 Mathlib 中的一个归纳类型，位于命名空间 `RingCat`。
形式化陈述：RingCat → RingCat → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of morphisms in `RingCat`.
-/
structure Hom (R S : RingCat.{u}) where
  private mk ::
  /-- The underlying ring hom. -/
  hom' : R →+* S

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**RingCat.** 是 Mathlib 中的一个实例，位于命名空间 `RingCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Category RingCat where
  Hom R S := Hom R S
  id R := ⟨RingHom.id R⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**RingCat.** 是 Mathlib 中的一个实例，位于命名空间 `RingCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ConcreteCategory.{u} RingCat (fun R S => R →+* S) where
  hom := Hom.hom'
  ofHom f := ⟨f⟩

/-- Turn a morphism in `RingCat` back into a `RingHom`. -/
/-
**RingCat.Hom.hom** 是 Mathlib 中的一个定义，位于命名空间 `RingCat.Hom`。
形式化陈述：{R S : RingCat} → R.Hom S → ↑R →+* ↑S
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turn a morphism in `RingCat` back into a `RingHom`.
-/
abbrev Hom.hom {R S : RingCat.{u}} (f : Hom R S) :=
  ConcreteCategory.hom (C := RingCat) f

/-- Typecheck a `RingHom` as a morphism in `RingCat`. -/
/-
**RingCat.ofHom** 是 Mathlib 中的一个缩写定义，位于命名空间 `RingCat`。
形式化陈述：ofHom {R S : Type u} [Ring R] [Ring S] (f : R ->+* S) : of R ⟶ of S
参数：f : R ->+* S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typecheck a `RingHom` as a morphism in `RingCat`.
-/
abbrev ofHom {R S : Type u} [Ring R] [Ring S] (f : R →+* S) : of R ⟶ of S :=
  ConcreteCategory.ofHom (C := RingCat) f

/-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/
/-
**RingCat.Hom.Simps.hom** 是 Mathlib 中的一个定义，位于命名空间 `RingCat.Hom.Simps`。
形式化陈述：(R S : RingCat) → R.Hom S → ↑R →+* ↑S
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas.
-/
def Hom.Simps.hom (R S : RingCat) (f : Hom R S) :=
  f.hom

initialize_simps_projections Hom (hom' → hom)

/-!
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep them for `dsimp`.
-/

@[simp]
/-
**RingCat.hom_id** 是 Mathlib 中的一个引理，位于命名空间 `RingCat`。
形式化陈述：hom_id {R : RingCat} : (𝟙 R : R ⟶ R).hom = RingHom.id R
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep 
them for `dsimp`.
-/
lemma hom_id {R : RingCat} : (𝟙 R : R ⟶ R).hom = RingHom.id R := rfl

/- Provided for rewriting. -/
/-
**RingCat.id_apply** 是 Mathlib 中的一个引理，位于命名空间 `RingCat`。
形式化陈述：id_apply (R : RingCat) (r : R) : (𝟙 R : R ⟶ R) r = r
参数：R : RingCat；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Provided for rewriting.
-/
lemma id_apply (R : RingCat) (r : R) :
    (𝟙 R : R ⟶ R) r = r := by simp

@[simp]
/-
**RingCat.hom_comp** 是 Mathlib 中的一个引理，位于命名空间 `RingCat`。
形式化陈述：hom_comp {R S T : RingCat} (f : R ⟶ S) (g : S ⟶ T) : (f ≫ g).hom = g.hom.c
omp f.hom
参数：f : R ⟶ S；g : S ⟶ T。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_comp {R S T : RingCat} (f : R ⟶ S) (g : S ⟶ T) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

/- Provided for rewriting. -/
/-
**RingCat.comp_apply** 是 Mathlib 中的一个引理，位于命名空间 `RingCat`。
形式化陈述：comp_apply {R S T : RingCat} (f : R ⟶ S) (g : S ⟶ T) (r : R) : (f ≫ g) r =
 g (f r)
参数：f : R ⟶ S；g : S ⟶ T；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Provided for rewriting.
-/
lemma comp_apply {R S T : RingCat} (f : R ⟶ S) (g : S ⟶ T) (r : R) :
    (f ≫ g) r = g (f r) := by simp

@[ext]
/-
**RingCat.hom_ext** 是 Mathlib 中的一个引理，位于命名空间 `RingCat`。
形式化陈述：hom_ext {R S : RingCat} {f g : R ⟶ S} (hf : f.hom = g.hom) : f = g
参数：hf : f.hom = g.hom。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingCat.Hom.ext`：∀ {R S : RingCat} {x y : R.Hom S}, x.hom' = y.hom' → x 
= y
-/
lemma hom_ext {R S : RingCat} {f g : R ⟶ S} (hf : f.hom = g.hom) : f = g :=
  Hom.ext hf

@[simp]
/-
**RingCat.hom_ofHom** 是 Mathlib 中的一个引理，位于命名空间 `RingCat`。
形式化陈述：hom_ofHom {R S : Type u} [Ring R] [Ring S] (f : R ->+* S) : (ofHom f).hom 
= f
参数：f : R ->+* S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_ofHom {R S : Type u} [Ring R] [Ring S] (f : R →+* S) : (ofHom f).hom = f := rfl

@[simp]
/-
**RingCat.ofHom_hom** 是 Mathlib 中的一个引理，位于命名空间 `RingCat`。
形式化陈述：ofHom_hom {R S : RingCat} (f : R ⟶ S) : ofHom (Hom.hom f) = f
参数：f : R ⟶ S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_hom {R S : RingCat} (f : R ⟶ S) :
    ofHom (Hom.hom f) = f := rfl

@[simp]
/-
**RingCat.ofHom_id** 是 Mathlib 中的一个引理，位于命名空间 `RingCat`。
形式化陈述：ofHom_id {R : Type u} [Ring R] : ofHom (RingHom.id R) = 𝟙 (of R)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_id {R : Type u} [Ring R] : ofHom (RingHom.id R) = 𝟙 (of R) := rfl

@[simp]
/-
**RingCat.ofHom_comp** 是 Mathlib 中的一个引理，位于命名空间 `RingCat`。
形式化陈述：ofHom_comp {R S T : Type u} [Ring R] [Ring S] [Ring T] (f : R ->+* S) (g :
 S ->+* T) : ofHom (g.comp f) = ofHom f ≫ ofHom g
参数：f : R ->+* S；g : S ->+* T。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_comp {R S T : Type u} [Ring R] [Ring S] [Ring T]
    (f : R →+* S) (g : S →+* T) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g :=
  rfl
/-
**RingCat.ofHom_apply** 是 Mathlib 中的一个引理，位于命名空间 `RingCat`。
形式化陈述：ofHom_apply {R S : Type u} [Ring R] [Ring S] (f : R ->+* S) (r : R) : ofHo
m f r = f r
参数：f : R ->+* S；r : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_apply {R S : Type u} [Ring R] [Ring S]
    (f : R →+* S) (r : R) : ofHom f r = f r := rfl
/-
**RingCat.inv_hom_apply** 是 Mathlib 中的一个引理，位于命名空间 `RingCat`。
形式化陈述：inv_hom_apply {R S : RingCat} (e : R ≅ S) (r : R) : e.inv (e.hom r) = r
参数：e : R ≅ S；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.hom_inv_id_apply`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {F : C → C → Type uF}   {carrier 
: C → Type w} {instFunLik…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma inv_hom_apply {R S : RingCat} (e : R ≅ S) (r : R) : e.inv (e.hom r) = r := by
  simp
/-
**RingCat.hom_inv_apply** 是 Mathlib 中的一个引理，位于命名空间 `RingCat`。
形式化陈述：hom_inv_apply {R S : RingCat} (e : R ≅ S) (s : S) : e.hom (e.inv s) = s
参数：e : R ≅ S；s : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.inv_hom_id_apply`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {F : C → C → Type uF}   {carrier 
: C → Type w} {instFunLik…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma hom_inv_apply {R S : RingCat} (e : R ≅ S) (s : S) : e.hom (e.inv s) = s := by
  simp
/-
**RingCat.** 是 Mathlib 中的一个实例，位于命名空间 `RingCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited RingCat :=
  ⟨of PUnit⟩

/-- This unification hint helps with problems of the form `(forget ?C).obj R =?= carrier R'`.

An example where this is needed is in applying
`PresheafOfModules.Sheafify.app_eq_of_isLocallyInjective`.
-/
unif_hint forget_obj_eq_coe (R R' : RingCat) where
  R ≟ R' ⊢
  (forget RingCat).obj R ≟ RingCat.carrier R'

@[deprecated (since := "2026-02-16")] alias forget_obj := CategoryTheory.forget_obj
@[deprecated (since := "2026-02-16")] alias forget_map := ConcreteCategory.forget_map_eq_ofHom

/-
**RingCat.** 是 Mathlib 中的一个实例，位于命名空间 `RingCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R : RingCat} : Ring ((forget RingCat).obj R) :=
  inferInstanceAs <| Ring R.carrier
/-
**RingCat.hasForgetToSemiRingCat** 是 Mathlib 中的一个实例，位于命名空间 `RingCat`。
形式化陈述：hasForgetToSemiRingCat : HasForget₂ RingCat SemiRingCat where forget₂
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasForgetToSemiRingCat : HasForget₂ RingCat SemiRingCat where
  forget₂ :=
    { obj := fun R ↦ SemiRingCat.of R
      map := fun f ↦ SemiRingCat.ofHom f.hom }
/-
**RingCat.forget** 是 Mathlib 中的一个引理，位于命名空间 `RingCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma forget₂_map {R S : RingCat} (f : R ⟶ S) (x) :
    (forget₂ RingCat SemiRingCat).map f x = f x := rfl

/-- The forgetful functor from `RingCat` to `SemiRingCat` is fully faithful. -/
/-
**RingCat.fullyFaithfulForget** 是 Mathlib 中的一个定义，位于命名空间 `RingCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful functor from `RingCat` to `SemiRingCat` is fully faithful.
-/
def fullyFaithfulForget₂ToSemiRingCat :
    (forget₂ RingCat SemiRingCat).FullyFaithful where
  preimage f := ofHom f.hom
/-
**RingCat.** 是 Mathlib 中的一个实例，位于命名空间 `RingCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (forget₂ RingCat SemiRingCat).Full :=
  fullyFaithfulForget₂ToSemiRingCat.full
/-
**RingCat.hasForgetToAddCommGrp** 是 Mathlib 中的一个实例，位于命名空间 `RingCat`。
形式化陈述：hasForgetToAddCommGrp : HasForget₂ RingCat AddCommGrpCat where forget₂
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasForgetToAddCommGrp : HasForget₂ RingCat AddCommGrpCat where
  forget₂ :=
    { obj := fun R ↦ AddCommGrpCat.of R
      map := fun f ↦ AddCommGrpCat.ofHom f.hom.toAddMonoidHom }

/-- Ring equivalences are isomorphisms in category of rings -/
@[simps]
/-
**RingCat._root_.RingEquiv.toRingCatIso** 是 Mathlib 中的一个定义，位于命名空间 `RingCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Ring equivalences are isomorphisms in category of rings
-/
def _root_.RingEquiv.toRingCatIso {R S : Type u} [Ring R] [Ring S] (e : R ≃+* S) :
    of R ≅ of S where
  hom := ofHom e
  inv := ofHom e.symm
/-
**RingCat.forgetReflectIsos** 是 Mathlib 中的一个实例，位于命名空间 `RingCat`。
形式化陈述：forgetReflectIsos : (forget RingCat).ReflectsIsomorphisms where reflects {
X Y} f _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.left_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Function
.LeftInverse self.invFun self.toFun
· 使用定理 `Equiv.right_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Functio
n.RightInverse self.invFun self.toFun
· 使用定理 `MonoidHom.map_mul'`：∀ {M : Type u_10} {N : Type u_11} [inst : MulOne M] 
[inst_1 : MulOne N] (self : M →* N) (x y : M),   (↑self).toFun (x * y) = (↑self)
.toFun x…
· 使用定理 `RingHom.map_add'`：∀ {α : Type u_5} {β : Type u_6} [inst : NonAssocSemiri
ng α] [inst_1 : NonAssocSemiring β] (self : α →+* β) (x y : α),   (↑↑self).toFun
 (x + …
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
-/
instance forgetReflectIsos : (forget RingCat).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    let i := asIso ((forget RingCat).map f)
    let ff : X →+* Y := f.hom
    let e : X ≃+* Y := { ff, i.toEquiv with }
    exact e.toRingCatIso.isIso_hom

end RingCat

/-- The category of commutative semirings. -/
/-
**CommSemiRingCat** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type (u + 1)
参数：u + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of commutative semirings.
-/
structure CommSemiRingCat where
  /-- The object in the category of commutative semirings associated to a type equipped with the
  appropriate typeclasses. -/
  of ::
  /-- The underlying type. -/
  carrier : Type u
  [commSemiring : CommSemiring carrier]

section Notation

open Lean.PrettyPrinter.Delaborator

/-- This prevents `CommSemiRingCat.of R` being printed as `{ carrier := R, commSemiring := ... }` by
`delabStructureInstance`. -/
@[app_delab CommSemiRingCat.of]
meta def CommSemiRingCat.delabOf : Delab := delabApp

end Notation

attribute [instance] CommSemiRingCat.commSemiring

initialize_simps_projections CommSemiRingCat (-commSemiring)

namespace CommSemiRingCat

/-
**CommSemiRingCat.** 是 Mathlib 中的一个实例，位于命名空间 `CommSemiRingCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeSort (CommSemiRingCat) (Type u) :=
  ⟨CommSemiRingCat.carrier⟩

attribute [coe] CommSemiRingCat.carrier
/-
**CommSemiRingCat.coe_of** 是 Mathlib 中的一个引理，位于命名空间 `CommSemiRingCat`。
形式化陈述：coe_of (R : Type u) [CommSemiring R] : (of R : Type u) = R
参数：R : Type u。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_of (R : Type u) [CommSemiring R] : (of R : Type u) = R :=
  rfl
/-
**CommSemiRingCat.of_carrier** 是 Mathlib 中的一个引理，位于命名空间 `CommSemiRingCat`。
形式化陈述：of_carrier (R : CommSemiRingCat.{u}) : of R = R
参数：R : CommSemiRingCat.{u}。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma of_carrier (R : CommSemiRingCat.{u}) : of R = R := rfl

variable {R} in
/-- The type of morphisms in `CommSemiRingCat`. -/
@[ext]
/-
**CommSemiRingCat.Hom** 是 Mathlib 中的一个归纳类型，位于命名空间 `CommSemiRingCat`。
形式化陈述：CommSemiRingCat → CommSemiRingCat → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of morphisms in `CommSemiRingCat`.
-/
structure Hom (R S : CommSemiRingCat.{u}) where
  private mk ::
  /-- The underlying ring hom. -/
  hom' : R →+* S

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**CommSemiRingCat.** 是 Mathlib 中的一个实例，位于命名空间 `CommSemiRingCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Category CommSemiRingCat where
  Hom R S := Hom R S
  id R := ⟨RingHom.id R⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**CommSemiRingCat.** 是 Mathlib 中的一个实例，位于命名空间 `CommSemiRingCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ConcreteCategory.{u} CommSemiRingCat (fun R S => R →+* S) where
  hom := Hom.hom'
  ofHom f := ⟨f⟩

/-- Turn a morphism in `CommSemiRingCat` back into a `RingHom`. -/
/-
**CommSemiRingCat.Hom.hom** 是 Mathlib 中的一个定义，位于命名空间 `CommSemiRingCat.Hom`。
形式化陈述：{R S : CommSemiRingCat} → R.Hom S → ↑R →+* ↑S
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turn a morphism in `CommSemiRingCat` back into a `RingHom`.
-/
abbrev Hom.hom {R S : CommSemiRingCat.{u}} (f : Hom R S) :=
  ConcreteCategory.hom (C := CommSemiRingCat) f

/-- Typecheck a `RingHom` as a morphism in `CommSemiRingCat`. -/
/-
**CommSemiRingCat.ofHom** 是 Mathlib 中的一个缩写定义，位于命名空间 `CommSemiRingCat`。
形式化陈述：ofHom {R S : Type u} [CommSemiring R] [CommSemiring S] (f : R ->+* S) : of
 R ⟶ of S
参数：f : R ->+* S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typecheck a `RingHom` as a morphism in `CommSemiRingCat`.
-/
abbrev ofHom {R S : Type u} [CommSemiring R] [CommSemiring S] (f : R →+* S) : of R ⟶ of S :=
  ConcreteCategory.ofHom (C := CommSemiRingCat) f

/-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/
/-
**CommSemiRingCat.Hom.Simps.hom** 是 Mathlib 中的一个定义，位于命名空间 `CommSemiRingCat.Hom.S
imps`。
形式化陈述：(R S : CommSemiRingCat) → R.Hom S → ↑R →+* ↑S
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas.
-/
def Hom.Simps.hom (R S : CommSemiRingCat) (f : Hom R S) :=
  f.hom

initialize_simps_projections Hom (hom' → hom)

/-!
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep them for `dsimp`.
-/

@[simp]
/-
**CommSemiRingCat.hom_id** 是 Mathlib 中的一个引理，位于命名空间 `CommSemiRingCat`。
形式化陈述：hom_id {R : CommSemiRingCat} : (𝟙 R : R ⟶ R).hom = RingHom.id R
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep 
them for `dsimp`.
-/
lemma hom_id {R : CommSemiRingCat} : (𝟙 R : R ⟶ R).hom = RingHom.id R := rfl

/- Provided for rewriting. -/
/-
**CommSemiRingCat.id_apply** 是 Mathlib 中的一个引理，位于命名空间 `CommSemiRingCat`。
形式化陈述：id_apply (R : CommSemiRingCat) (r : R) : (𝟙 R : R ⟶ R) r = r
参数：R : CommSemiRingCat；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Provided for rewriting.
-/
lemma id_apply (R : CommSemiRingCat) (r : R) :
    (𝟙 R : R ⟶ R) r = r := by simp

@[simp]
/-
**CommSemiRingCat.hom_comp** 是 Mathlib 中的一个引理，位于命名空间 `CommSemiRingCat`。
形式化陈述：hom_comp {R S T : CommSemiRingCat} (f : R ⟶ S) (g : S ⟶ T) : (f ≫ g).hom =
 g.hom.comp f.hom
参数：f : R ⟶ S；g : S ⟶ T。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_comp {R S T : CommSemiRingCat} (f : R ⟶ S) (g : S ⟶ T) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

/- Provided for rewriting. -/
/-
**CommSemiRingCat.comp_apply** 是 Mathlib 中的一个引理，位于命名空间 `CommSemiRingCat`。
形式化陈述：comp_apply {R S T : CommSemiRingCat} (f : R ⟶ S) (g : S ⟶ T) (r : R) : (f 
≫ g) r = g (f r)
参数：f : R ⟶ S；g : S ⟶ T；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Provided for rewriting.
-/
lemma comp_apply {R S T : CommSemiRingCat} (f : R ⟶ S) (g : S ⟶ T) (r : R) :
    (f ≫ g) r = g (f r) := by simp

@[ext]
/-
**CommSemiRingCat.hom_ext** 是 Mathlib 中的一个引理，位于命名空间 `CommSemiRingCat`。
形式化陈述：hom_ext {R S : CommSemiRingCat} {f g : R ⟶ S} (hf : f.hom = g.hom) : f = g
参数：hf : f.hom = g.hom。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CommSemiRingCat.Hom.ext`：∀ {R S : CommSemiRingCat} {x y : R.Hom S}, x.ho
m' = y.hom' → x = y
-/
lemma hom_ext {R S : CommSemiRingCat} {f g : R ⟶ S} (hf : f.hom = g.hom) : f = g :=
  Hom.ext hf

@[simp]
/-
**CommSemiRingCat.hom_ofHom** 是 Mathlib 中的一个引理，位于命名空间 `CommSemiRingCat`。
形式化陈述：hom_ofHom {R S : Type u} [CommSemiring R] [CommSemiring S] (f : R ->+* S) 
: (ofHom f).hom = f
参数：f : R ->+* S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_ofHom {R S : Type u} [CommSemiring R] [CommSemiring S] (f : R →+* S) :
    (ofHom f).hom = f := rfl

@[simp]
/-
**CommSemiRingCat.ofHom_hom** 是 Mathlib 中的一个引理，位于命名空间 `CommSemiRingCat`。
形式化陈述：ofHom_hom {R S : CommSemiRingCat} (f : R ⟶ S) : ofHom (Hom.hom f) = f
参数：f : R ⟶ S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_hom {R S : CommSemiRingCat} (f : R ⟶ S) :
    ofHom (Hom.hom f) = f := rfl

@[simp]
/-
**CommSemiRingCat.ofHom_id** 是 Mathlib 中的一个引理，位于命名空间 `CommSemiRingCat`。
形式化陈述：ofHom_id {R : Type u} [CommSemiring R] : ofHom (RingHom.id R) = 𝟙 (of R)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_id {R : Type u} [CommSemiring R] : ofHom (RingHom.id R) = 𝟙 (of R) := rfl

@[simp]
/-
**CommSemiRingCat.ofHom_comp** 是 Mathlib 中的一个引理，位于命名空间 `CommSemiRingCat`。
形式化陈述：ofHom_comp {R S T : Type u} [CommSemiring R] [CommSemiring S] [CommSemirin
g T] (f : R ->+* S) (g : S ->+* T) : ofHom (g.comp f) = ofHom f ≫ ofHom g
参数：f : R ->+* S；g : S ->+* T。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_comp {R S T : Type u} [CommSemiring R] [CommSemiring S] [CommSemiring T]
    (f : R →+* S) (g : S →+* T) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g :=
  rfl
/-
**CommSemiRingCat.ofHom_apply** 是 Mathlib 中的一个引理，位于命名空间 `CommSemiRingCat`。
形式化陈述：ofHom_apply {R S : Type u} [CommSemiring R] [CommSemiring S] (f : R ->+* S
) (r : R) : ofHom f r = f r
参数：f : R ->+* S；r : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_apply {R S : Type u} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (r : R) : ofHom f r = f r := rfl
/-
**CommSemiRingCat.inv_hom_apply** 是 Mathlib 中的一个引理，位于命名空间 `CommSemiRingCat`。
形式化陈述：inv_hom_apply {R S : CommSemiRingCat} (e : R ≅ S) (r : R) : e.inv (e.hom r
) = r
参数：e : R ≅ S；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.hom_inv_id_apply`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {F : C → C → Type uF}   {carrier 
: C → Type w} {instFunLik…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma inv_hom_apply {R S : CommSemiRingCat} (e : R ≅ S) (r : R) : e.inv (e.hom r) = r := by
  simp
/-
**CommSemiRingCat.hom_inv_apply** 是 Mathlib 中的一个引理，位于命名空间 `CommSemiRingCat`。
形式化陈述：hom_inv_apply {R S : CommSemiRingCat} (e : R ≅ S) (s : S) : e.hom (e.inv s
) = s
参数：e : R ≅ S；s : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.inv_hom_id_apply`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {F : C → C → Type uF}   {carrier 
: C → Type w} {instFunLik…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma hom_inv_apply {R S : CommSemiRingCat} (e : R ≅ S) (s : S) : e.hom (e.inv s) = s := by
  simp
/-
**CommSemiRingCat.** 是 Mathlib 中的一个实例，位于命名空间 `CommSemiRingCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited CommSemiRingCat :=
  ⟨of PUnit⟩

/-- This unification hint helps with problems of the form `(forget ?C).obj R =?= carrier R'`. -/
unif_hint forget_obj_eq_coe (R R' : CommSemiRingCat) where
  R ≟ R' ⊢
  (forget CommSemiRingCat).obj R ≟ CommSemiRingCat.carrier R'

@[deprecated (since := "2026-02-16")] alias forget_obj := CategoryTheory.forget_obj
@[deprecated (since := "2026-02-16")] alias forget_map := ConcreteCategory.forget_map_eq_ofHom

/-
**CommSemiRingCat.** 是 Mathlib 中的一个实例，位于命名空间 `CommSemiRingCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R : CommSemiRingCat} : CommSemiring ((forget CommSemiRingCat).obj R) :=
  inferInstanceAs <| CommSemiring R.carrier

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**CommSemiRingCat.hasForgetToSemiRingCat** 是 Mathlib 中的一个实例，位于命名空间 `CommSemiRing
Cat`。
形式化陈述：hasForgetToSemiRingCat : HasForget₂ CommSemiRingCat SemiRingCat where forg
et₂
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasForgetToSemiRingCat : HasForget₂ CommSemiRingCat SemiRingCat where
  forget₂ :=
    { obj := fun R ↦ ⟨R⟩
      map := fun f ↦ ⟨f.hom⟩ }

/-- The forgetful functor from `CommSemiRingCat` to `SemiRingCat` is fully faithful. -/
/-
**CommSemiRingCat.fullyFaithfulForget** 是 Mathlib 中的一个定义，位于命名空间 `CommSemiRingCat
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful functor from `CommSemiRingCat` to `SemiRingCat` is fully faithful.
-/
def fullyFaithfulForget₂ToSemiRingCat :
    (forget₂ CommSemiRingCat SemiRingCat).FullyFaithful where
  preimage f := ofHom f.hom
/-
**CommSemiRingCat.** 是 Mathlib 中的一个实例，位于命名空间 `CommSemiRingCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (forget₂ CommSemiRingCat SemiRingCat).Full :=
  fullyFaithfulForget₂ToSemiRingCat.full

/-- The forgetful functor from commutative rings to (multiplicative) commutative monoids. -/
/-
**CommSemiRingCat.hasForgetToCommMonCat** 是 Mathlib 中的一个实例，位于命名空间 `CommSemiRingC
at`。
形式化陈述：hasForgetToCommMonCat : HasForget₂ CommSemiRingCat CommMonCat where forget
₂
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful functor from commutative rings to (multiplicative) commutative mon
oids.
-/
instance hasForgetToCommMonCat : HasForget₂ CommSemiRingCat CommMonCat where
  forget₂ :=
    { obj := fun R ↦ CommMonCat.of R
      map := fun f ↦ CommMonCat.ofHom f.hom.toMonoidHom }

/-- Ring equivalences are isomorphisms in category of commutative semirings -/
@[simps]
/-
**CommSemiRingCat._root_.RingEquiv.toCommSemiRingCatIso** 是 Mathlib 中的一个定义，位于命名空
间 `CommSemiRingCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Ring equivalences are isomorphisms in category of commutative semirings
-/
def _root_.RingEquiv.toCommSemiRingCatIso
    {R S : Type u} [CommSemiring R] [CommSemiring S] (e : R ≃+* S) :
    of R ≅ of S where
  hom := ofHom e
  inv := ofHom e.symm
/-
**CommSemiRingCat.forgetReflectIsos** 是 Mathlib 中的一个实例，位于命名空间 `CommSemiRingCat`。
形式化陈述：forgetReflectIsos : (forget CommSemiRingCat).ReflectsIsomorphisms where re
flects {X Y} f _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.left_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Function
.LeftInverse self.invFun self.toFun
· 使用定理 `Equiv.right_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Functio
n.RightInverse self.invFun self.toFun
· 使用定理 `MonoidHom.map_mul'`：∀ {M : Type u_10} {N : Type u_11} [inst : MulOne M] 
[inst_1 : MulOne N] (self : M →* N) (x y : M),   (↑self).toFun (x * y) = (↑self)
.toFun x…
· 使用定理 `RingHom.map_add'`：∀ {α : Type u_5} {β : Type u_6} [inst : NonAssocSemiri
ng α] [inst_1 : NonAssocSemiring β] (self : α →+* β) (x y : α),   (↑↑self).toFun
 (x + …
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
-/
instance forgetReflectIsos : (forget CommSemiRingCat).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    let i := asIso ((forget CommSemiRingCat).map f)
    let ff : X →+* Y := f.hom
    let e : X ≃+* Y := { ff, i.toEquiv with }
    exact e.toCommSemiRingCatIso.isIso_hom

end CommSemiRingCat

/-- The category of commutative rings. -/
/-
**CommRingCat** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type (u + 1)
参数：u + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of commutative rings.
-/
structure CommRingCat where
  /-- The object in the category of commutative rings associated to a type equipped with the
  appropriate typeclasses. -/
  of ::
  /-- The underlying type. -/
  carrier : Type u
  [commRing : CommRing carrier]

section Notation

open Lean.PrettyPrinter.Delaborator

/-- This prevents `CommRingCat.of R` being printed as `{ carrier := R, commRing := ... }` by
`delabStructureInstance`. -/
@[app_delab CommRingCat.of]
meta def CommRingCat.delabOf : Delab := delabApp

end Notation

attribute [instance] CommRingCat.commRing

initialize_simps_projections CommRingCat (-commRing)

namespace CommRingCat

/-
**CommRingCat.** 是 Mathlib 中的一个实例，位于命名空间 `CommRingCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeSort CommRingCat (Type u) :=
  ⟨CommRingCat.carrier⟩

attribute [coe] CommRingCat.carrier
/-
**CommRingCat.coe_of** 是 Mathlib 中的一个引理，位于命名空间 `CommRingCat`。
形式化陈述：coe_of (R : Type u) [CommRing R] : (of R : Type u) = R
参数：R : Type u。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_of (R : Type u) [CommRing R] : (of R : Type u) = R :=
  rfl
/-
**CommRingCat.of_carrier** 是 Mathlib 中的一个引理，位于命名空间 `CommRingCat`。
形式化陈述：of_carrier (R : CommRingCat.{u}) : of R = R
参数：R : CommRingCat.{u}。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma of_carrier (R : CommRingCat.{u}) : of R = R := rfl

variable {R} in
/-- The type of morphisms in `CommRingCat`. -/
@[ext]
/-
**CommRingCat.Hom** 是 Mathlib 中的一个归纳类型，位于命名空间 `CommRingCat`。
形式化陈述：CommRingCat → CommRingCat → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of morphisms in `CommRingCat`.
-/
structure Hom (R S : CommRingCat.{u}) where
  private mk ::
  /-- The underlying ring hom. -/
  hom' : R →+* S

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**CommRingCat.** 是 Mathlib 中的一个实例，位于命名空间 `CommRingCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Category CommRingCat where
  Hom R S := Hom R S
  id R := ⟨RingHom.id R⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**CommRingCat.** 是 Mathlib 中的一个实例，位于命名空间 `CommRingCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ConcreteCategory.{u} CommRingCat (fun R S => R →+* S) where
  hom := Hom.hom'
  ofHom f := ⟨f⟩

/-- The underlying ring hom. -/
/-
**CommRingCat.Hom.hom** 是 Mathlib 中的一个定义，位于命名空间 `CommRingCat.Hom`。
形式化陈述：{R S : CommRingCat} → R.Hom S → ↑R →+* ↑S
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The underlying ring hom.
-/
abbrev Hom.hom {R S : CommRingCat.{u}} (f : Hom R S) :=
  ConcreteCategory.hom (C := CommRingCat) f

/-- Typecheck a `RingHom` as a morphism in `CommRingCat`. -/
/-
**CommRingCat.ofHom** 是 Mathlib 中的一个缩写定义，位于命名空间 `CommRingCat`。
形式化陈述：ofHom {R S : Type u} [CommRing R] [CommRing S] (f : R ->+* S) : of R ⟶ of 
S
参数：f : R ->+* S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typecheck a `RingHom` as a morphism in `CommRingCat`.
-/
abbrev ofHom {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) : of R ⟶ of S :=
  ConcreteCategory.ofHom (C := CommRingCat) f

/-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/
/-
**CommRingCat.Hom.Simps.hom** 是 Mathlib 中的一个定义，位于命名空间 `CommRingCat.Hom.Simps`。
形式化陈述：(R S : CommRingCat) → R.Hom S → ↑R →+* ↑S
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas.
-/
def Hom.Simps.hom (R S : CommRingCat) (f : Hom R S) :=
  f.hom

initialize_simps_projections Hom (hom' → hom)

/-!
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep them for `dsimp`.
-/

@[simp]
/-
**CommRingCat.hom_id** 是 Mathlib 中的一个引理，位于命名空间 `CommRingCat`。
形式化陈述：hom_id {R : CommRingCat} : (𝟙 R : R ⟶ R).hom = RingHom.id R
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep 
them for `dsimp`.
-/
lemma hom_id {R : CommRingCat} : (𝟙 R : R ⟶ R).hom = RingHom.id R := rfl

/- Provided for rewriting. -/
/-
**CommRingCat.id_apply** 是 Mathlib 中的一个引理，位于命名空间 `CommRingCat`。
形式化陈述：id_apply (R : CommRingCat) (r : R) : (𝟙 R : R ⟶ R) r = r
参数：R : CommRingCat；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Provided for rewriting.
-/
lemma id_apply (R : CommRingCat) (r : R) :
    (𝟙 R : R ⟶ R) r = r := by simp

@[simp]
/-
**CommRingCat.hom_comp** 是 Mathlib 中的一个引理，位于命名空间 `CommRingCat`。
形式化陈述：hom_comp {R S T : CommRingCat} (f : R ⟶ S) (g : S ⟶ T) : (f ≫ g).hom = g.h
om.comp f.hom
参数：f : R ⟶ S；g : S ⟶ T。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_comp {R S T : CommRingCat} (f : R ⟶ S) (g : S ⟶ T) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

/- Provided for rewriting. -/
/-
**CommRingCat.comp_apply** 是 Mathlib 中的一个引理，位于命名空间 `CommRingCat`。
形式化陈述：comp_apply {R S T : CommRingCat} (f : R ⟶ S) (g : S ⟶ T) (r : R) : (f ≫ g)
 r = g (f r)
参数：f : R ⟶ S；g : S ⟶ T；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Provided for rewriting.
-/
lemma comp_apply {R S T : CommRingCat} (f : R ⟶ S) (g : S ⟶ T) (r : R) :
    (f ≫ g) r = g (f r) := by simp

@[ext]
/-
**CommRingCat.hom_ext** 是 Mathlib 中的一个引理，位于命名空间 `CommRingCat`。
形式化陈述：hom_ext {R S : CommRingCat} {f g : R ⟶ S} (hf : f.hom = g.hom) : f = g
参数：hf : f.hom = g.hom。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CommRingCat.Hom.ext`：∀ {R S : CommRingCat} {x y : R.Hom S}, x.hom' = y.h
om' → x = y
-/
lemma hom_ext {R S : CommRingCat} {f g : R ⟶ S} (hf : f.hom = g.hom) : f = g :=
  Hom.ext hf

@[simp]
/-
**CommRingCat.hom_ofHom** 是 Mathlib 中的一个引理，位于命名空间 `CommRingCat`。
形式化陈述：hom_ofHom {R S : Type u} [CommRing R] [CommRing S] (f : R ->+* S) : (ofHom
 f).hom = f
参数：f : R ->+* S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_ofHom {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) : (ofHom f).hom = f := rfl

@[simp]
/-
**CommRingCat.ofHom_hom** 是 Mathlib 中的一个引理，位于命名空间 `CommRingCat`。
形式化陈述：ofHom_hom {R S : CommRingCat} (f : R ⟶ S) : ofHom (Hom.hom f) = f
参数：f : R ⟶ S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_hom {R S : CommRingCat} (f : R ⟶ S) :
    ofHom (Hom.hom f) = f := rfl

@[simp]
/-
**CommRingCat.ofHom_id** 是 Mathlib 中的一个引理，位于命名空间 `CommRingCat`。
形式化陈述：ofHom_id {R : Type u} [CommRing R] : ofHom (RingHom.id R) = 𝟙 (of R)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_id {R : Type u} [CommRing R] : ofHom (RingHom.id R) = 𝟙 (of R) := rfl

@[simp]
/-
**CommRingCat.ofHom_comp** 是 Mathlib 中的一个引理，位于命名空间 `CommRingCat`。
形式化陈述：ofHom_comp {R S T : Type u} [CommRing R] [CommRing S] [CommRing T] (f : R 
->+* S) (g : S ->+* T) : ofHom (g.comp f) = ofHom f ≫ ofHom g
参数：f : R ->+* S；g : S ->+* T。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_comp {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g :=
  rfl
/-
**CommRingCat.ofHom_apply** 是 Mathlib 中的一个引理，位于命名空间 `CommRingCat`。
形式化陈述：ofHom_apply {R S : Type u} [CommRing R] [CommRing S] (f : R ->+* S) (r : R
) : ofHom f r = f r
参数：f : R ->+* S；r : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_apply {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (r : R) : ofHom f r = f r := rfl
/-
**CommRingCat.inv_hom_apply** 是 Mathlib 中的一个引理，位于命名空间 `CommRingCat`。
形式化陈述：inv_hom_apply {R S : CommRingCat} (e : R ≅ S) (r : R) : e.inv (e.hom r) = 
r
参数：e : R ≅ S；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.hom_inv_id_apply`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {F : C → C → Type uF}   {carrier 
: C → Type w} {instFunLik…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma inv_hom_apply {R S : CommRingCat} (e : R ≅ S) (r : R) : e.inv (e.hom r) = r := by
  simp
/-
**CommRingCat.hom_inv_apply** 是 Mathlib 中的一个引理，位于命名空间 `CommRingCat`。
形式化陈述：hom_inv_apply {R S : CommRingCat} (e : R ≅ S) (s : S) : e.hom (e.inv s) = 
s
参数：e : R ≅ S；s : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.inv_hom_id_apply`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {F : C → C → Type uF}   {carrier 
: C → Type w} {instFunLik…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma hom_inv_apply {R S : CommRingCat} (e : R ≅ S) (s : S) : e.hom (e.inv s) = s := by
  simp
/-
**CommRingCat.** 是 Mathlib 中的一个实例，位于命名空间 `CommRingCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited CommRingCat :=
  ⟨of PUnit⟩

@[deprecated (since := "2026-02-16")] alias forget_obj := CategoryTheory.forget_obj
@[deprecated (since := "2026-02-16")] alias forget_map := ConcreteCategory.forget_map_eq_ofHom

/-- This unification hint helps with problems of the form `(forget ?C).obj R =?= carrier R'`.

An example where this is needed is in applying `TopCat.Presheaf.restrictOpen` to commutative rings.
-/
unif_hint forget_obj_eq_coe (R R' : CommRingCat) where
  R ≟ R' ⊢
  (forget CommRingCat).obj R ≟ CommRingCat.carrier R'

/-
**CommRingCat.** 是 Mathlib 中的一个实例，位于命名空间 `CommRingCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R : CommRingCat} : CommRing ((forget CommRingCat).obj R) :=
  inferInstanceAs <| CommRing R.carrier
/-
**CommRingCat.hasForgetToRingCat** 是 Mathlib 中的一个实例，位于命名空间 `CommRingCat`。
形式化陈述：hasForgetToRingCat : HasForget₂ CommRingCat RingCat where forget₂
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasForgetToRingCat : HasForget₂ CommRingCat RingCat where
  forget₂ :=
    { obj := fun R ↦ RingCat.of R
      map := fun f ↦ RingCat.ofHom f.hom }

/-- The forgetful functor from `CommRingCat` to `RingCat` is fully faithful. -/
/-
**CommRingCat.fullyFaithfulForget** 是 Mathlib 中的一个定义，位于命名空间 `CommRingCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful functor from `CommRingCat` to `RingCat` is fully faithful.
-/
def fullyFaithfulForget₂ToRingCat :
    (forget₂ CommRingCat RingCat).FullyFaithful where
  preimage f := ofHom f.hom
/-
**CommRingCat.** 是 Mathlib 中的一个实例，位于命名空间 `CommRingCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (forget₂ CommRingCat RingCat).Full :=
  fullyFaithfulForget₂ToRingCat.full
/-
**CommRingCat.forgetToRingCat_map_hom** 是 Mathlib 中的一个定理，位于命名空间 `CommRingCat`。
形式化陈述：∀ {R S : CommRingCat} (f : R ⟶ S),   RingCat.Hom.hom ((CategoryTheory.forg
et₂ CommRingCat RingCat).map f) = CommRingCat.Hom.hom f
参数：f : R ⟶ S；(CategoryTheory.forget₂ CommRingCat RingCat).map f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma forgetToRingCat_map_hom {R S : CommRingCat} (f : R ⟶ S) :
    ((forget₂ CommRingCat RingCat).map f).hom = f.hom :=
  rfl
/-
**CommRingCat.forgetToRingCat_obj** 是 Mathlib 中的一个定理，位于命名空间 `CommRingCat`。
形式化陈述：∀ {R : CommRingCat}, ↑((CategoryTheory.forget₂ CommRingCat RingCat).obj R)
 = ↑R
参数：(CategoryTheory.forget₂ CommRingCat RingCat).obj R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma forgetToRingCat_obj {R : CommRingCat} :
    (((forget₂ CommRingCat RingCat).obj R) : Type u) = R :=
  rfl
/-
**CommRingCat.hasForgetToAddCommMonCat** 是 Mathlib 中的一个实例，位于命名空间 `CommRingCat`。
形式化陈述：hasForgetToAddCommMonCat : HasForget₂ CommRingCat CommSemiRingCat where fo
rget₂
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasForgetToAddCommMonCat : HasForget₂ CommRingCat CommSemiRingCat where
  forget₂ :=
    { obj := fun R ↦ CommSemiRingCat.of R
      map := fun f ↦ CommSemiRingCat.ofHom f.hom }

@[simps (nameStem := "commMon")]
/-
**CommRingCat.** 是 Mathlib 中的一个实例，位于命名空间 `CommRingCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasForget₂ CommRingCat CommMonCat where
  forget₂ := { obj M := .of M, map f := CommMonCat.ofHom f.hom }
  forget_comp := rfl

/-- Ring equivalences are isomorphisms in category of commutative rings -/
@[simps]
/-
**CommRingCat._root_.RingEquiv.toCommRingCatIso** 是 Mathlib 中的一个定义，位于命名空间 `CommR
ingCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Ring equivalences are isomorphisms in category of commutative rings
-/
def _root_.RingEquiv.toCommRingCatIso
    {R S : Type u} [CommRing R] [CommRing S] (e : R ≃+* S) :
    of R ≅ of S where
  hom := ofHom e
  inv := ofHom e.symm
/-
**CommRingCat.forgetReflectIsos** 是 Mathlib 中的一个实例，位于命名空间 `CommRingCat`。
形式化陈述：forgetReflectIsos : (forget CommRingCat).ReflectsIsomorphisms where reflec
ts {X Y} f _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.left_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Function
.LeftInverse self.invFun self.toFun
· 使用定理 `Equiv.right_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Functio
n.RightInverse self.invFun self.toFun
· 使用定理 `MonoidHom.map_mul'`：∀ {M : Type u_10} {N : Type u_11} [inst : MulOne M] 
[inst_1 : MulOne N] (self : M →* N) (x y : M),   (↑self).toFun (x * y) = (↑self)
.toFun x…
· 使用定理 `RingHom.map_add'`：∀ {α : Type u_5} {β : Type u_6} [inst : NonAssocSemiri
ng α] [inst_1 : NonAssocSemiring β] (self : α →+* β) (x y : α),   (↑↑self).toFun
 (x + …
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
-/
instance forgetReflectIsos : (forget CommRingCat).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    let i := asIso ((forget CommRingCat).map f)
    let ff : X →+* Y := f.hom
    let e : X ≃+* Y := { ff, i.toEquiv with }
    exact e.toCommRingCatIso.isIso_hom

end CommRingCat

namespace CategoryTheory.Iso

/-- Build a `RingEquiv` from an isomorphism in the category `SemiRingCat`. -/
/-
**CategoryTheory.Iso.semiRingCatIsoToRingEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Iso`。
形式化陈述：semiRingCatIsoToRingEquiv {R S : SemiRingCat.{u}} (e : R ≅ S) : R ≃+* S
参数：e : R ≅ S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Build a `RingEquiv` from an isomorphism in the category `SemiRingCat`.
-/
def semiRingCatIsoToRingEquiv {R S : SemiRingCat.{u}} (e : R ≅ S) : R ≃+* S :=
  RingEquiv.ofRingHom e.hom.hom e.inv.hom (by ext; simp) (by ext; simp)

/-- Build a `RingEquiv` from an isomorphism in the category `RingCat`. -/
/-
**CategoryTheory.Iso.ringCatIsoToRingEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Iso`。
形式化陈述：ringCatIsoToRingEquiv {R S : RingCat.{u}} (e : R ≅ S) : R ≃+* S
参数：e : R ≅ S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Build a `RingEquiv` from an isomorphism in the category `RingCat`.
-/
def ringCatIsoToRingEquiv {R S : RingCat.{u}} (e : R ≅ S) : R ≃+* S :=
  RingEquiv.ofRingHom e.hom.hom e.inv.hom (by ext; simp) (by ext; simp)

/-- Build a `RingEquiv` from an isomorphism in the category `CommSemiRingCat`. -/
/-
**CategoryTheory.Iso.commSemiRingCatIsoToRingEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Iso`。
形式化陈述：commSemiRingCatIsoToRingEquiv {R S : CommSemiRingCat.{u}} (e : R ≅ S) : R 
≃+* S
参数：e : R ≅ S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Build a `RingEquiv` from an isomorphism in the category `CommSemiRingCat`.
-/
def commSemiRingCatIsoToRingEquiv {R S : CommSemiRingCat.{u}} (e : R ≅ S) : R ≃+* S :=
  RingEquiv.ofRingHom e.hom.hom e.inv.hom (by ext; simp) (by ext; simp)

/-- Build a `RingEquiv` from an isomorphism in the category `CommRingCat`. -/
/-
**CategoryTheory.Iso.commRingCatIsoToRingEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Iso`。
形式化陈述：commRingCatIsoToRingEquiv {R S : CommRingCat.{u}} (e : R ≅ S) : R ≃+* S
参数：e : R ≅ S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Build a `RingEquiv` from an isomorphism in the category `CommRingCat`.
-/
def commRingCatIsoToRingEquiv {R S : CommRingCat.{u}} (e : R ≅ S) : R ≃+* S :=
  RingEquiv.ofRingHom e.hom.hom e.inv.hom (by ext; simp) (by ext; simp)
/-
**CategoryTheory.Iso.semiRingCatIsoToRingEquiv_toRingHom** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.Iso`。
形式化陈述：∀ {R S : SemiRingCat} (e : R ≅ S), ↑e.semiRingCatIsoToRingEquiv = SemiRing
Cat.Hom.hom e.hom
参数：e : R ≅ S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
-/
@[simp] lemma semiRingCatIsoToRingEquiv_toRingHom {R S : SemiRingCat.{u}} (e : R ≅ S) :
    (e.semiRingCatIsoToRingEquiv : R →+* S) = e.hom.hom := rfl
/-
**CategoryTheory.Iso.ringCatIsoToRingEquiv_toRingHom** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.Iso`。
形式化陈述：∀ {R S : RingCat} (e : R ≅ S), ↑e.ringCatIsoToRingEquiv = RingCat.Hom.hom 
e.hom
参数：e : R ≅ S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
-/
@[simp] lemma ringCatIsoToRingEquiv_toRingHom {R S : RingCat.{u}} (e : R ≅ S) :
    (e.ringCatIsoToRingEquiv : R →+* S) = e.hom.hom := rfl
/-
**CategoryTheory.Iso.commSemiRingCatIsoToRingEquiv_toRingHom** 是 Mathlib 中的一个定理，
位于命名空间 `CategoryTheory.Iso`。
形式化陈述：∀ {R S : CommSemiRingCat} (e : R ≅ S), ↑e.commSemiRingCatIsoToRingEquiv = 
CommSemiRingCat.Hom.hom e.hom
参数：e : R ≅ S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
-/
@[simp] lemma commSemiRingCatIsoToRingEquiv_toRingHom {R S : CommSemiRingCat.{u}} (e : R ≅ S) :
    (e.commSemiRingCatIsoToRingEquiv : R →+* S) = e.hom.hom := rfl
/-
**CategoryTheory.Iso.commRingCatIsoToRingEquiv_toRingHom** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.Iso`。
形式化陈述：∀ {R S : CommRingCat} (e : R ≅ S), ↑e.commRingCatIsoToRingEquiv = CommRing
Cat.Hom.hom e.hom
参数：e : R ≅ S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
-/
@[simp] lemma commRingCatIsoToRingEquiv_toRingHom {R S : CommRingCat.{u}} (e : R ≅ S) :
    (e.commRingCatIsoToRingEquiv : R →+* S) = e.hom.hom := rfl

end CategoryTheory.Iso

/-
**RingCat.forget_map_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：RingCat.forget_map_apply {R S : RingCat} (f : R ⟶ S) (x : (CategoryTheory.
forget RingCat).obj R) : (forget _).map f x = f x
参数：f : R ⟶ S；x : (CategoryTheory.forget RingCat).obj R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma RingCat.forget_map_apply {R S : RingCat} (f : R ⟶ S)
    (x : (CategoryTheory.forget RingCat).obj R) :
    (forget _).map f x = f x :=
  rfl
/-
**CommRingCat.forget_map_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：CommRingCat.forget_map_apply {R S : CommRingCat} (f : R ⟶ S) (x : (Categor
yTheory.forget CommRingCat).obj R) : (forget _).map f x = f x
参数：f : R ⟶ S；x : (CategoryTheory.forget CommRingCat).obj R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma CommRingCat.forget_map_apply {R S : CommRingCat} (f : R ⟶ S)
    (x : (CategoryTheory.forget CommRingCat).obj R) :
    (forget _).map f x = f x :=
  rfl
