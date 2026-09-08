/-
Copyright (c) 2022 Rémi Bottinelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémi Bottinelli
-/
module

public import Mathlib.CategoryTheory.Groupoid
public import Mathlib.CategoryTheory.PathCategory.Basic

/-!
# Free groupoid on a quiver

This file defines the free groupoid on a quiver, the lifting of a prefunctor to its unique
extension as a functor from the free groupoid, and proves uniqueness of this extension.

## Main results

Given the type `V` and a quiver instance on `V`:

- `Quiver.FreeGroupoid V`: a type synonym for `V`.
- `Quiver.FreeGroupoid.instGroupoid`: the `Groupoid` instance on `Quiver.FreeGroupoid V`.
- `lift`: the lifting of a prefunctor from `V` to `V'` where `V'` is a groupoid, to a functor.
  `Quiver.FreeGroupoid V ⥤ V'`.
- `lift_spec` and `lift_unique`: the proofs that, respectively, `lift` indeed is a lifting
  and is the unique one.

## Implementation notes

The free groupoid is first defined by symmetrifying the quiver, taking the induced path category
and finally quotienting by the reducibility relation.

-/

@[expose] public section

open Set Function

namespace Quiver

open CategoryTheory

universe u v u' v' u'' v''

variable {V : Type u} [Quiver.{v} V]

/-- Shorthand for the "forward" arrow corresponding to `f` in `paths <| symmetrify V` -/
/-
**Quiver.Hom.toPosPath** 是 Mathlib 中的一个定义，位于命名空间 `Quiver.Hom`。
形式化陈述：{V : Type u} → [inst : Quiver V] → {X Y : V} → (X ⟶ Y) → (X ⟶ Y)
参数：X ⟶ Y；X ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Shorthand for the "forward" arrow corresponding to `f` in `paths <| symmetrify V
`
-/
abbrev Hom.toPosPath {X Y : V} (f : X ⟶ Y) :
    (CategoryTheory.Paths.categoryPaths <| Quiver.Symmetrify V).Hom X Y :=
  f.toPos.toPath

/-- Shorthand for the "forward" arrow corresponding to `f` in `paths <| symmetrify V` -/
/-
**Quiver.Hom.toNegPath** 是 Mathlib 中的一个定义，位于命名空间 `Quiver.Hom`。
形式化陈述：{V : Type u} → [inst : Quiver V] → {X Y : V} → (X ⟶ Y) → (Y ⟶ X)
参数：X ⟶ Y；Y ⟶ X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Shorthand for the "forward" arrow corresponding to `f` in `paths <| symmetrify V
`
-/
abbrev Hom.toNegPath {X Y : V} (f : X ⟶ Y) :
    (CategoryTheory.Paths.categoryPaths <| Quiver.Symmetrify V).Hom Y X :=
  f.toNeg.toPath

/-- The "reduction" relation -/
/-
**Quiver.FreeGroupoid.redStep** 是 Mathlib 中的一个归纳类型，位于命名空间 `Quiver.FreeGroupoid`。
形式化陈述：{V : Type u} → [inst : Quiver V] → HomRel (CategoryTheory.Paths (Quiver.Sy
mmetrify V))
参数：CategoryTheory.Paths (Quiver.Symmetrify V)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The "reduction" relation
-/
inductive FreeGroupoid.redStep : HomRel (Paths (Quiver.Symmetrify V))
  | step (X Z : Quiver.Symmetrify V) (f : X ⟶ Z) :
    redStep (𝟙 ((Paths.of (Quiver.Symmetrify V)).obj X)) (f.toPath ≫ (Quiver.reverse f).toPath)

/-- The underlying vertices of the free groupoid -/
/-
**Quiver.FreeGroupoid** 是 Mathlib 中的一个定义，位于命名空间 `Quiver`。
形式化陈述：(V : Type u_1) → [Q : Quiver V] → Type u_1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The underlying vertices of the free groupoid
-/
protected def FreeGroupoid (V) [Q : Quiver V] :=
  CategoryTheory.Quotient (@FreeGroupoid.redStep V Q)

namespace FreeGroupoid

open Quiver

/-
**Quiver.FreeGroupoid.** 是 Mathlib 中的一个实例，位于命名空间 `Quiver.FreeGroupoid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {V} [Quiver V] [Nonempty V] : Nonempty (Quiver.FreeGroupoid V) := by
  inhabit V; exact ⟨⟨@default V _⟩⟩

set_option backward.isDefEq.respectTransparency false in
/-
**Quiver.FreeGroupoid.congr_reverse** 是 Mathlib 中的一个定理，位于命名空间 `Quiver.FreeGroupo
id`。
形式化陈述：congr_reverse {X Y : Paths <| Quiver.Symmetrify V} (p q : X ⟶ Y) : HomRel.
CompClosure redStep p q -> HomRel.CompClosure redStep p.reverse q.reverse
参数：p q : X ⟶ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Quiver.Path.nil_comp`：∀ {V : Type u} [inst : Quiver V] {a b : V} (p : Qu
iver.Path a b), Quiver.Path.nil.comp p = p
· 使用定理 `Quiver.Path.reverse_comp`：∀ {V : Type u_2} [inst : Quiver V] [inst_1 : Q
uiver.HasReverse V] {a b c : V} (p : Quiver.Path a b)   (q : Quiver.Path b c), (
p.comp q).reve…
· 使用定理 `Quiver.Path.comp_assoc`：∀ {V : Type u} [inst : Quiver V] {a b c d : V} (
p : Quiver.Path a b) (q : Quiver.Path b c) (r : Quiver.Path c d),   (p.comp q).c
omp r = p.co…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Quiver.reverse_reverse`：reverse_reverse [h : HasInvolutiveReverse V] {a 
b : V} (f : a ⟶ b) : reverse (reverse f) = f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
theorem congr_reverse {X Y : Paths <| Quiver.Symmetrify V} (p q : X ⟶ Y) :
    HomRel.CompClosure redStep p q → HomRel.CompClosure redStep p.reverse q.reverse := by
  rintro ⟨_, _, XW, _, _, WY, _, _, f⟩
  have : HomRel.CompClosure redStep (WY.reverse ≫ 𝟙 _ ≫ XW.reverse)
      (WY.reverse ≫ (f.toPath ≫ (Quiver.reverse f).toPath) ≫ XW.reverse) := by
    constructor
    constructor
  simpa only [CategoryStruct.comp, CategoryStruct.id, Quiver.Path.reverse, Quiver.Path.nil_comp,
    Quiver.Path.reverse_comp, Quiver.reverse_reverse, Quiver.Path.reverse_toPath,
    Quiver.Path.comp_assoc] using this

set_option backward.isDefEq.respectTransparency.types false in
open Relation in
/-
**Quiver.FreeGroupoid.congr_comp_reverse** 是 Mathlib 中的一个定理，位于命名空间 `Quiver.FreeG
roupoid`。
形式化陈述：congr_comp_reverse {X Y : Paths <| Quiver.Symmetrify V} (p : X ⟶ Y) : Quot
.mk (@HomRel.CompClosure _ _ redStep _ _) (p ≫ p.reverse) = Quot.mk (@HomRel.Com
pClosure _ _ redStep _ _) (𝟙 X)
参数：p : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.eqvGen_sound`：Quot.eqvGen_sound (H : EqvGen r a b) : Quot.mk r a = 
Quot.mk r b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
-/
theorem congr_comp_reverse {X Y : Paths <| Quiver.Symmetrify V} (p : X ⟶ Y) :
    Quot.mk (@HomRel.CompClosure _ _ redStep _ _) (p ≫ p.reverse) =
      Quot.mk (@HomRel.CompClosure _ _ redStep _ _) (𝟙 X) := by
  apply Quot.eqvGen_sound
  induction p with
  | nil => apply EqvGen.refl
  | cons q f ih =>
    simp only [Quiver.Path.reverse]
    fapply EqvGen.trans
    -- Porting note: dot notation for `Quiver.Path.*` and `Quiver.Hom.*` not working
    · exact q ≫ Quiver.Path.reverse q
    · apply EqvGen.symm
      apply EqvGen.rel
      have : HomRel.CompClosure redStep (q ≫ 𝟙 _ ≫ Quiver.Path.reverse q)
          (q ≫ (Quiver.Hom.toPath f ≫ Quiver.Hom.toPath (Quiver.reverse f)) ≫
            Quiver.Path.reverse q) := by
        apply HomRel.CompClosure.intro
        apply redStep.step
      simp only [Category.assoc, Category.id_comp] at this ⊢
      -- Porting note: `simp` cannot see how `Quiver.Path.comp_assoc` is relevant, so change to
      -- category notation
      change HomRel.CompClosure redStep (q ≫ Quiver.Path.reverse q)
        (Quiver.Path.cons q f ≫ (Quiver.Hom.toPath (Quiver.reverse f)) ≫ (Quiver.Path.reverse q))
      simp only [← Category.assoc] at this ⊢
      exact this
    · exact ih
/-
**Quiver.FreeGroupoid.congr_reverse_comp** 是 Mathlib 中的一个定理，位于命名空间 `Quiver.FreeG
roupoid`。
形式化陈述：congr_reverse_comp {X Y : Paths <| Quiver.Symmetrify V} (p : X ⟶ Y) : Quot
.mk (@HomRel.CompClosure _ _ redStep _ _) (p.reverse ≫ p) = Quot.mk (@HomRel.Com
pClosure _ _ redStep _ _) (𝟙 Y)
参数：p : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Quiver.Path.reverse_reverse`：∀ {V : Type u_2} [inst : Quiver V] [h : Qui
ver.HasInvolutiveReverse V] {a b : V} (p : Quiver.Path a b),   p.reverse.reverse
 = p
· 使用定理 `Quiver.FreeGroupoid.congr_comp_reverse`：congr_comp_reverse {X Y : Paths 
<| Quiver.Symmetrify V} (p : X ⟶ Y) : Quot.mk (@HomRel.CompClosure _ _ redStep _
 _) (p ≫ p.reverse) = Quot.m…
-/
theorem congr_reverse_comp {X Y : Paths <| Quiver.Symmetrify V} (p : X ⟶ Y) :
    Quot.mk (@HomRel.CompClosure _ _ redStep _ _) (p.reverse ≫ p) =
      Quot.mk (@HomRel.CompClosure _ _ redStep _ _) (𝟙 Y) := by
  nth_rw 2 [← Quiver.Path.reverse_reverse p]
  apply congr_comp_reverse
/-
**Quiver.FreeGroupoid.** 是 Mathlib 中的一个实例，位于命名空间 `Quiver.FreeGroupoid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Category (Quiver.FreeGroupoid V) :=
  Quotient.category redStep

/-- The inverse of an arrow in the free groupoid -/
/-
**Quiver.FreeGroupoid.quotInv** 是 Mathlib 中的一个定义，位于命名空间 `Quiver.FreeGroupoid`。
形式化陈述：quotInv {X Y : Quiver.FreeGroupoid V} (f : X ⟶ Y) : Y ⟶ X
参数：f : X ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inverse of an arrow in the free groupoid
-/
def quotInv {X Y : Quiver.FreeGroupoid V} (f : X ⟶ Y) : Y ⟶ X :=
  Quot.liftOn f (fun pp => Quot.mk _ <| pp.reverse) fun pp qq con =>
    Quot.sound <| congr_reverse pp qq con
/-
**Quiver.FreeGroupoid.instGroupoid** 是 Mathlib 中的一个实例，位于命名空间 `Quiver.FreeGroupoi
d`。
形式化陈述：instGroupoid : Groupoid (Quiver.FreeGroupoid V) where inv
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instGroupoid : Groupoid (Quiver.FreeGroupoid V) where
  inv := quotInv
  inv_comp p := Quot.inductionOn p fun pp => congr_reverse_comp pp
  comp_inv p := Quot.inductionOn p fun pp => congr_comp_reverse pp

/-- The inclusion of the quiver on `V` to the underlying quiver on `FreeGroupoid V` -/
/-
**Quiver.FreeGroupoid.of** 是 Mathlib 中的一个定义，位于命名空间 `Quiver.FreeGroupoid`。
形式化陈述：of (V) [Quiver V] : V ⥤q Quiver.FreeGroupoid V where obj X
参数：V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion of the quiver on `V` to the underlying quiver on `FreeGroupoid V`
-/
def of (V) [Quiver V] : V ⥤q Quiver.FreeGroupoid V where
  obj X := ⟨X⟩
  map f := Quot.mk _ f.toPosPath
/-
**Quiver.FreeGroupoid.of_eq** 是 Mathlib 中的一个定理，位于命名空间 `Quiver.FreeGroupoid`。
形式化陈述：of_eq : of V = (Quiver.Symmetrify.of ⋙q (Paths.of (Quiver.Symmetrify V))).
comp (Quotient.functor <| @redStep V _).toPrefunctor
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem of_eq :
    of V = (Quiver.Symmetrify.of ⋙q (Paths.of (Quiver.Symmetrify V))).comp
      (Quotient.functor <| @redStep V _).toPrefunctor := rfl

section UniversalProperty

variable {V' : Type u'} [Groupoid V']

/-- The lift of a prefunctor to a groupoid, to a functor from `FreeGroupoid V` -/
/-
**Quiver.FreeGroupoid.lift** 是 Mathlib 中的一个定义，位于命名空间 `Quiver.FreeGroupoid`。
形式化陈述：lift (φ : V ⥤q V') : Quiver.FreeGroupoid V ⥤ V'
参数：φ : V ⥤q V'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The lift of a prefunctor to a groupoid, to a functor from `FreeGroupoid V`
-/
def lift (φ : V ⥤q V') : Quiver.FreeGroupoid V ⥤ V' :=
  CategoryTheory.Quotient.lift _ (Paths.lift <| Quiver.Symmetrify.lift φ) <| by
    rintro _ _ _ _ ⟨X, Y, f⟩
    -- Porting note: `simp` does not work, so manually `rewrite`
    erw [Paths.lift_nil, Paths.lift_cons, Quiver.Path.comp_nil, Paths.lift_toPath,
      Quiver.Symmetrify.lift_reverse]
    symm
    apply Groupoid.comp_inv

set_option backward.isDefEq.respectTransparency false in
/-
**Quiver.FreeGroupoid.lift_spec** 是 Mathlib 中的一个定理，位于命名空间 `Quiver.FreeGroupoid`。
形式化陈述：lift_spec (φ : V ⥤q V') : of V ⋙q (lift φ).toPrefunctor = φ
参数：φ : V ⥤q V'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Quiver.FreeGroupoid.of_eq`：of_eq : of V = (Quiver.Symmetrify.of ⋙q (Path
s.of (Quiver.Symmetrify V))).comp (Quotient.functor <| @redStep V _).toPrefuncto
r
· 使用定理 `Prefunctor.comp_assoc`：comp_assoc {U V W Z : Type*} [Quiver U] [Quiver V
] [Quiver W] [Quiver Z] (F : Prefunctor U V) (G : Prefunctor V W) (H : Prefuncto
r W Z) : (F…
· 使用定理 `CategoryTheory.Functor.toPrefunctor_comp`：toPrefunctor_comp (F : C ⥤ D) 
(G : D ⥤ E) : F.toPrefunctor.comp G.toPrefunctor = (F ⋙ G).toPrefunctor
· 使用定理 `CategoryTheory.Quotient.lift_spec`：lift_spec : functor r ⋙ lift r F H = 
F
· 使用定理 `CategoryTheory.Paths.lift_spec`：lift_spec {C} [Category* C] (φ : V ⥤q C)
 : of V ⋙q (lift φ).toPrefunctor = φ
· 使用定理 `Quiver.Symmetrify.lift_spec`：lift_spec [HasReverse V'] (φ : Prefunctor V
 V') : Symmetrify.of.comp (Symmetrify.lift φ) = φ
-/
theorem lift_spec (φ : V ⥤q V') : of V ⋙q (lift φ).toPrefunctor = φ := by
  rw [of_eq, Prefunctor.comp_assoc, Prefunctor.comp_assoc, Functor.toPrefunctor_comp]
  dsimp [lift]
  rw [Quotient.lift_spec, Paths.lift_spec, Quiver.Symmetrify.lift_spec]

set_option backward.isDefEq.respectTransparency.types false in
/-
**Quiver.FreeGroupoid.lift_unique** 是 Mathlib 中的一个定理，位于命名空间 `Quiver.FreeGroupoid
`。
形式化陈述：lift_unique (φ : V ⥤q V') (Φ : Quiver.FreeGroupoid V ⥤ V') (hΦ : of V ⋙q Φ
.toPrefunctor = φ) : Φ = lift φ
参数：φ : V ⥤q V'；Φ : Quiver.FreeGroupoid V ⥤ V'；hΦ : of V ⋙q Φ.toPrefunctor = φ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Quotient.lift_unique`：lift_unique (Φ : Quotient r ⥤ D) (h
Φ : functor r ⋙ Φ = F) : Φ = lift r F H
· 使用定理 `CategoryTheory.Paths.lift_unique`：lift_unique {C} [Category* C] (φ : V ⥤
q C) (Φ : Paths V ⥤ C) (hΦ : of V ⋙q Φ.toPrefunctor = φ) : Φ = lift φ
· 使用定理 `Quiver.Symmetrify.lift_unique`：lift_unique [HasReverse V'] (φ : V ⥤q V')
 (Φ : Symmetrify V ⥤q V') (hΦ : (of ⋙q Φ) = φ) (hΦinv : forall {X Y : Symmetrify
 V} (f : X ⟶ Y), Φ.…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.toPrefunctor_comp`：toPrefunctor_comp (F : C ⥤ D) 
(G : D ⥤ E) : F.toPrefunctor.comp G.toPrefunctor = (F ⋙ G).toPrefunctor
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Prefunctor.comp_map`：∀ {U : Type u_1} [inst : Quiver U] {V : Type u_2} [
inst_1 : Quiver V] {W : Type u_3} [inst_2 : Quiver W] (F : U ⥤q V)   (G : V ⥤q W
) {X Y : …
· 使用定理 `CategoryTheory.Paths.of_map`：∀ (V : Type u₁) [inst : Quiver V] {X Y : V}
 (f : X ⟶ Y), (CategoryTheory.Paths.of V).map f = f.toPath
· 使用定理 `CategoryTheory.IsGroupoid.all_isIso`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.IsGroupoid C] {X Y : C} (f : X ⟶ Y)
,   CategoryTheory.IsIso …
· 使用定理 `CategoryTheory.instIsGroupoid`：∀ {C : Type u} [inst : CategoryTheory.Gro
upoid C], CategoryTheory.IsGroupoid C
· 使用定理 `CategoryTheory.Functor.map_inv`：map_inv (F : C ⥤ D) {X Y : C} (f : X ⟶ Y
) [IsIso f] : F.map (inv f) = inv (F.map f)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.IsIso.of_groupoid`：∀ {C : Type u} [inst : CategoryTheory.
Groupoid C] {X Y : C} (f : X ⟶ Y), CategoryTheory.IsIso f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Groupoid.inv_eq_inv`：∀ {C : Type u} [inst : CategoryTheor
y.Groupoid C] {X Y : C} (f : X ⟶ Y),   CategoryTheory.Groupoid.inv f = CategoryT
heory.inv f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lift_unique (φ : V ⥤q V') (Φ : Quiver.FreeGroupoid V ⥤ V')
    (hΦ : of V ⋙q Φ.toPrefunctor = φ) : Φ = lift φ := by
  apply Quotient.lift_unique
  apply Paths.lift_unique
  fapply @Quiver.Symmetrify.lift_unique _ _ _ _ _ _ _ _ _
  · rw [← Functor.toPrefunctor_comp]
    exact hΦ
  · rintro X Y f
    simp only [← Functor.toPrefunctor_comp, Prefunctor.comp_map, Paths.of_map]
    change Φ.map (Groupoid.inv ((Quotient.functor redStep).toPrefunctor.map f.toPath)) =
      Groupoid.inv (Φ.map ((Quotient.functor redStep).toPrefunctor.map f.toPath))
    have := Functor.map_inv Φ ((Quotient.functor redStep).toPrefunctor.map f.toPath)
    convert! this <;> simp only [Groupoid.inv_eq_inv]

end UniversalProperty

end FreeGroupoid

section Functoriality

open FreeGroupoid

variable {V' : Type u'} [Quiver.{v'} V'] {V'' : Type u''} [Quiver.{v''} V'']

/-- The functor of free groupoid induced by a prefunctor of quivers -/
/-
**Quiver.freeGroupoidFunctor** 是 Mathlib 中的一个定义，位于命名空间 `Quiver`。
形式化陈述：freeGroupoidFunctor (φ : V ⥤q V') : Quiver.FreeGroupoid V ⥤ Quiver.FreeGro
upoid V'
参数：φ : V ⥤q V'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor of free groupoid induced by a prefunctor of quivers
-/
def freeGroupoidFunctor (φ : V ⥤q V') : Quiver.FreeGroupoid V ⥤ Quiver.FreeGroupoid V' :=
  lift (φ ⋙q of V')
/-
**Quiver.freeGroupoidFunctor_id** 是 Mathlib 中的一个定理，位于命名空间 `Quiver`。
形式化陈述：freeGroupoidFunctor_id : freeGroupoidFunctor (Prefunctor.id V) = Functor.i
d (Quiver.FreeGroupoid V)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Quiver.FreeGroupoid.lift_unique`：lift_unique (φ : V ⥤q V') (Φ : Quiver.F
reeGroupoid V ⥤ V') (hΦ : of V ⋙q Φ.toPrefunctor = φ) : Φ = lift φ
-/
theorem freeGroupoidFunctor_id :
    freeGroupoidFunctor (Prefunctor.id V) = Functor.id (Quiver.FreeGroupoid V) := by
  dsimp only [freeGroupoidFunctor]; symm
  apply lift_unique; rfl
/-
**Quiver.freeGroupoidFunctor_comp** 是 Mathlib 中的一个定理，位于命名空间 `Quiver`。
形式化陈述：freeGroupoidFunctor_comp (φ : V ⥤q V') (φ' : V' ⥤q V'') : freeGroupoidFunc
tor (φ ⋙q φ') = freeGroupoidFunctor φ ⋙ freeGroupoidFunctor φ'
参数：φ : V ⥤q V'；φ' : V' ⥤q V''。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Quiver.FreeGroupoid.lift_unique`：lift_unique (φ : V ⥤q V') (Φ : Quiver.F
reeGroupoid V ⥤ V') (hΦ : of V ⋙q Φ.toPrefunctor = φ) : Φ = lift φ
-/
theorem freeGroupoidFunctor_comp (φ : V ⥤q V') (φ' : V' ⥤q V'') :
    freeGroupoidFunctor (φ ⋙q φ') = freeGroupoidFunctor φ ⋙ freeGroupoidFunctor φ' := by
  dsimp only [freeGroupoidFunctor]; symm
  apply lift_unique; rfl

end Functoriality

end Quiver

