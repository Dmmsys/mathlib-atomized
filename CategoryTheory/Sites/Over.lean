/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Limits.Shapes.Connected
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Functor.Flat

/-! # Localization

In this file, given a Grothendieck topology `J` on a category `C` and `X : C`, we construct
a Grothendieck topology `J.over X` on the category `Over X`. In order to do this,
we first construct a bijection `Sieve.overEquiv Y : Sieve Y ≃ Sieve Y.left`
for all `Y : Over X`. Then, as it is stated in SGA 4 III 5.2.1, a sieve of `Y : Over X`
is covering for `J.over X` if and only if the corresponding sieve of `Y.left`
is covering for `J`. As a result, the forgetful functor
`Over.forget X : Over X ⥤ X` is both cover-preserving and cover-lifting.

-/

@[expose] public section

universe w v' v u' u

namespace CategoryTheory

open Category

variable {C : Type u} [Category.{v} C]

namespace Presieve

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CategoryTheory.Presieve.functorPullback_map_overForget** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.Presieve`。
形式化陈述：functorPullback_map_overForget {X : C} {Y : Over X} (S : Presieve Y) : (S.
map (Over.forget X)).functorPullback (Over.forget X) = S
参数：S : Presieve Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `CategoryTheory.Over.mk_surjective`：mk_surjective {S : T} (X : Over S) : 
exists (Y : T) (f : Y ⟶ S), Over.mk f = X
· 使用引理 `CategoryTheory.Over.homMk_surjective`：homMk_surjective {S : T} {X Y : Ov
er S} (f : X ⟶ Y) : exists (g : X.left ⟶ Y.left) (hg : g ≫ Y.hom = X.hom), f = O
ver.homMk g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Presieve.functorPullback_map_functorPullback`：functorPull
back_map_functorPullback {X : C} (R : Presieve (F.obj X)) : Presieve.functorPull
back F (Presieve.map F (R.functorPullback F)) = R…
-/
lemma functorPullback_map_overForget {X : C} {Y : Over X} (S : Presieve Y) :
    (S.map (Over.forget X)).functorPullback (Over.forget X) = S := by
  let R : Presieve Y.left := fun Z g ↦ S (Over.homMk g : Over.mk (g ≫ Y.hom) ⟶ Y)
  suffices hR : (R.functorPullback (Over.forget X)) = S by
    rw [← hR, functorPullback_map_functorPullback]
  funext Z f
  obtain ⟨Z, fZ, rfl⟩ := Z.mk_surjective
  obtain ⟨g : Z ⟶ Y.left, rfl : g ≫ Y.hom = fZ, rfl⟩ := Over.homMk_surjective f
  rfl

@[simp]
/-
**CategoryTheory.Presieve.map_functorPullback_overForget** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.Presieve`。
形式化陈述：map_functorPullback_overForget {X : C} {Y : Over X} (R : Presieve Y.left) 
: (R.functorPullback (Over.forget X)).map (Over.forget X) = R
参数：R : Presieve Y.left。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `CategoryTheory.Presieve.map_functorPullback`：map_functorPullback {X : C}
 (R : Presieve (F.obj X)) : (R.functorPullback F).map F <= R
-/
lemma map_functorPullback_overForget {X : C} {Y : Over X} (R : Presieve Y.left) :
    (R.functorPullback (Over.forget X)).map (Over.forget X) = R :=
  le_antisymm (map_functorPullback _) fun Z g hg ↦
    map.of (u := (Over.homMk g : Over.mk (g ≫ Y.hom) ⟶ Y)) hg

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The equivalence `Presieve Y ≃ Presieve Y.left` for all `Y : Over X`. -/
@[simps]
/-
**CategoryTheory.Presieve.overEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Pr
esieve`。
形式化陈述：overEquiv {X : C} (Y : Over X) : Presieve Y ≃o Presieve Y.left where toFun
 S
参数：Y : Over X。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Presieve.functorPullback_map_overForget`：functorPullback_
map_overForget {X : C} {Y : Over X} (S : Presieve Y) : (S.map (Over.forget X)).f
unctorPullback (Over.forget X) = S
· 使用引理 `CategoryTheory.Presieve.map_functorPullback_overForget`：map_functorPullb
ack_overForget {X : C} {Y : Over X} (R : Presieve Y.left) : (R.functorPullback (
Over.forget X)).map (Over.forget X) = R

--- 原说明 ---
The equivalence `Presieve Y ≃ Presieve Y.left` for all `Y : Over X`.
-/
def overEquiv {X : C} (Y : Over X) : Presieve Y ≃o Presieve Y.left where
  toFun S := map (Over.forget X) S
  invFun S' := functorPullback (Over.forget X) S'
  left_inv := functorPullback_map_overForget
  right_inv := map_functorPullback_overForget
  map_rel_iff' := ⟨fun h ↦ by simpa using functorPullback_monotone h, fun h ↦ map_monotone h⟩

end Presieve

namespace Sieve

@[simp]
/-
**CategoryTheory.Sieve.functorPushforward_overForget_arrows** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.Sieve`。
形式化陈述：functorPushforward_overForget_arrows {X : C} {Y : Over X} (S : Sieve Y) : 
S.arrows.functorPushforward (Over.forget X) = S.arrows.map (Over.forget X)
参数：S : Sieve Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `CategoryTheory.Presieve.map_map`：map_map {X Y : C} {f : Y ⟶ X} {R : Pres
ieve X} (hf : R f) : R.map F (F.map f)
· 使用定理 `CategoryTheory.Sieve.downward_closed`：∀ {C : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} C] {X : C} (self : CategoryTheory.Sieve X) {Y Z : C}   {f
 : Y ⟶ X}, self.arrows f →…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Presieve.map_le_functorPushforward`：∀ {C : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Ca
tegory.{v₂, u₂} D]   (F : CategoryTheor…
-/
lemma functorPushforward_overForget_arrows {X : C} {Y : Over X} (S : Sieve Y) :
    S.arrows.functorPushforward (Over.forget X) = S.arrows.map (Over.forget X) := by
  refine le_antisymm ?_ (S.arrows.map_le_functorPushforward (Over.forget X))
  rintro Z - ⟨W, fW, fZ, h, rfl⟩
  exact Presieve.map_map (S.downward_closed h (Over.homMk fZ : Over.mk (fZ ≫ W.hom) ⟶ W))

@[simp]
/-
**CategoryTheory.Sieve.functorPullback_functorPushforward_overForget** 是 Mathlib
 中的一个引理，位于命名空间 `CategoryTheory.Sieve`。
形式化陈述：functorPullback_functorPushforward_overForget {X : C} {Y : Over X} (S : Si
eve Y) : (S.functorPushforward (Over.forget X)).functorPullback (Over.forget X) 
= S
参数：S : Sieve Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Sieve.arrows_ext`：arrows_ext : forall {R S : Sieve X}, R.
arrows = S.arrows -> R = S
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Sieve.functorPullback_apply`：∀ {C : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.
{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Sieve.functorPushforward_apply`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Catego
ry.{v₂, u₂} D]   (F : CategoryTheor…
· 使用引理 `CategoryTheory.Sieve.functorPushforward_overForget_arrows`：functorPushfo
rward_overForget_arrows {X : C} {Y : Over X} (S : Sieve Y) : S.arrows.functorPus
hforward (Over.forget X) = S.arrows.map (Over.f…
· 使用引理 `CategoryTheory.Presieve.functorPullback_map_overForget`：functorPullback_
map_overForget {X : C} {Y : Over X} (S : Presieve Y) : (S.map (Over.forget X)).f
unctorPullback (Over.forget X) = S
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma functorPullback_functorPushforward_overForget {X : C} {Y : Over X} (S : Sieve Y) :
    (S.functorPushforward (Over.forget X)).functorPullback (Over.forget X) = S := by
  apply arrows_ext
  simp

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CategoryTheory.Sieve.functorPushforward_functorPullback_overForget** 是 Mathlib
 中的一个引理，位于命名空间 `CategoryTheory.Sieve`。
形式化陈述：functorPushforward_functorPullback_overForget {X : C} {Y : Over X} (S : Si
eve Y.left) : (S.functorPullback (Over.forget X)).functorPushforward (Over.forge
t X) = S
参数：S : Sieve Y.left。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Sieve.arrows_ext`：arrows_ext : forall {R S : Sieve X}, R.
arrows = S.arrows -> R = S
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Sieve.functorPushforward_apply`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Catego
ry.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Sieve.functorPullback_apply`：∀ {C : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.
{v₂, u₂} D]   (F : CategoryTheor…
· 使用引理 `CategoryTheory.Presieve.map_functorPullback_overForget`：map_functorPullb
ack_overForget {X : C} {Y : Over X} (R : Presieve Y.left) : (R.functorPullback (
Over.forget X)).map (Over.forget X) = R
· 使用定理 `CategoryTheory.Sieve.generate_sieve`：generate_sieve (S : Sieve X) : gene
rate S = S
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma functorPushforward_functorPullback_overForget {X : C} {Y : Over X} (S : Sieve Y.left) :
    (S.functorPullback (Over.forget X)).functorPushforward (Over.forget X) = S := by
  apply arrows_ext
  simp [← arrows_generate_map_eq_functorPushforward]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The equivalence `Sieve Y ≃ Sieve Y.left` for all `Y : Over X`. -/
@[simps -isSimp] -- working with `overEquiv` is useful enough that we don't want `simp` unfolding it
/-
**CategoryTheory.Sieve.overEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Sieve
`。
形式化陈述：overEquiv {X : C} (Y : Over X) : Sieve Y ≃o Sieve Y.left where toFun
参数：Y : Over X。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Sieve.functorPullback_functorPushforward_overForget`：func
torPullback_functorPushforward_overForget {X : C} {Y : Over X} (S : Sieve Y) : (
S.functorPushforward (Over.forget X)).functorPullback (O…
· 使用引理 `CategoryTheory.Sieve.functorPushforward_functorPullback_overForget`：func
torPushforward_functorPullback_overForget {X : C} {Y : Over X} (S : Sieve Y.left
) : (S.functorPullback (Over.forget X)).functorPushforwa…

--- 原说明 ---
The equivalence `Sieve Y ≃ Sieve Y.left` for all `Y : Over X`.
-/
def overEquiv {X : C} (Y : Over X) : Sieve Y ≃o Sieve Y.left where
  toFun := functorPushforward (Over.forget X)
  invFun := functorPullback (Over.forget X)
  left_inv := functorPullback_functorPushforward_overForget
  right_inv := functorPushforward_functorPullback_overForget
  map_rel_iff' := by
    rw [Equiv.coe_fn_mk]
    exact ⟨fun h ↦ by simpa using functorPullback_monotone _ _ h,
      fun h ↦ functorPushforward_monotone _ _ h⟩

@[deprecated (since := "2026-07-08")] alias overEquiv_top := map_top
@[deprecated (since := "2026-07-08")] alias overEquiv_symm_top := map_top
@[deprecated (since := "2026-07-08")] alias overEquiv_bot := map_bot
@[deprecated (since := "2026-07-08")] alias overEquiv_symm_bot := map_bot
@[deprecated (since := "2026-07-08")] alias overEquiv_le_overEquiv_iff := RelIso.map_rel_iff

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Sieve.overEquiv_pullback** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.Sieve`。
形式化陈述：overEquiv_pullback {X : C} {Y₁ Y₂ : Over X} (f : Y₁ ⟶ Y₂) (S : Sieve Y₂) :
 overEquiv _ (S.pullback f) = (overEquiv _ S).pullback f.left
参数：f : Y₁ ⟶ Y₂；S : Sieve Y₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Sieve.ext`：∀ {C : Type u₁} [inst : CategoryTheory.Categor
y.{v₁, u₁} C] {X : C} {R S : CategoryTheory.Sieve X},   (∀ ⦃Y : C⦄ (f : Y ⟶ X), 
R.arrows f ↔ S…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Over.w`：w : φ.left ≫ g.hom = f.hom
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Mathlib.Tactic.Reassoc.eq_whisker'`：eq_whisker' {C : Type*} [Category* C
] {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) : f ≫ h = g ≫ h
· 使用定理 `CategoryTheory.Over.OverMorphism.ext`：∀ {T : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} T] {X : T} {U V : CategoryTheory.Over X} {f g : U ⟶ V},  
 CategoryTheory.Over.Hom.l…
· 使用定理 `CategoryTheory.Sieve.downward_closed`：∀ {C : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} C] {X : C} (self : CategoryTheory.Sieve X) {Y Z : C}   {f
 : Y ⟶ X}, self.arrows f →…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
-/
lemma overEquiv_pullback {X : C} {Y₁ Y₂ : Over X} (f : Y₁ ⟶ Y₂) (S : Sieve Y₂) :
    overEquiv _ (S.pullback f) = (overEquiv _ S).pullback f.left := by
  ext Z g
  dsimp [overEquiv, Presieve.functorPushforward]
  constructor
  · rintro ⟨W, a, b, h, rfl⟩
    exact ⟨W, a ≫ f, b, h, by simp⟩
  · rintro ⟨W, a, b, h, w⟩
    let T := Over.mk (b ≫ W.hom)
    let c : T ⟶ Y₁ := Over.homMk g (by dsimp [T]; rw [← Over.w a, ← reassoc_of% w, Over.w f])
    let d : T ⟶ W := Over.homMk b
    refine ⟨T, c, 𝟙 Z, ?_, by simp [T, c]⟩
    rw [show c ≫ f = d ≫ a by ext; exact w]
    exact S.downward_closed h _
/-
**CategoryTheory.Sieve.overEquiv_symm_pullback** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.Sieve`。
形式化陈述：overEquiv_symm_pullback {X : C} {Y₁ Y₂ : Over X} (f : Y₁ ⟶ Y₂) (S : Sieve 
Y₂.left) : (overEquiv Y₁).symm (pullback f.left S) = pullback f ((overEquiv Y₂).
symm S)
参数：f : Y₁ ⟶ Y₂；S : Sieve Y₂.left。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Sieve.functorPullback_pullback`：functorPullback_pullback 
{X Y : C} (f : X ⟶ Y) (S : Sieve (F.obj Y)) : functorPullback F (pullback (F.map
 f) S) = pullback f (functorPullbac…
-/
lemma overEquiv_symm_pullback {X : C} {Y₁ Y₂ : Over X} (f : Y₁ ⟶ Y₂) (S : Sieve Y₂.left) :
    (overEquiv Y₁).symm (pullback f.left S) = pullback f ((overEquiv Y₂).symm S) :=
  functorPullback_pullback _ _ _

@[simp]
/-
**CategoryTheory.Sieve.overEquiv_symm_iff** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.Sieve`。
形式化陈述：overEquiv_symm_iff {X : C} {Y : Over X} (S : Sieve Y.left) {Z : Over X} (f
 : Z ⟶ Y) : (overEquiv Y).symm S f ↔ S f.left
参数：S : Sieve Y.left；f : Z ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma overEquiv_symm_iff {X : C} {Y : Over X} (S : Sieve Y.left) {Z : Over X} (f : Z ⟶ Y) :
    (overEquiv Y).symm S f ↔ S f.left := by
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.Sieve.overEquiv_iff** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.S
ieve`。
形式化陈述：overEquiv_iff {X : C} {Y : Over X} (S : Sieve Y) {Z : C} (f : Z ⟶ Y.left) 
: overEquiv Y S f ↔ S (Over.homMk f : Over.mk (f ≫ Y.hom) ⟶ Y)
参数：S : Sieve Y；f : Z ⟶ Y.left。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.surjective`：∀ {α : Type u_2} {β : Type u_3} [inst : LE α] [inst
_1 : LE β] (e : α ≃o β), Function.Surjective ⇑e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `OrderIso.apply_symm_apply`：apply_symm_apply (e : α ≃o β) (x : β) : e (e.
symm x) = x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma overEquiv_iff {X : C} {Y : Over X} (S : Sieve Y) {Z : C} (f : Z ⟶ Y.left) :
    overEquiv Y S f ↔ S (Over.homMk f : Over.mk (f ≫ Y.hom) ⟶ Y) := by
  obtain ⟨S, rfl⟩ := (overEquiv Y).symm.surjective S
  simp

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.Sieve.overEquiv_ofArrows** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.Sieve`。
形式化陈述：overEquiv_ofArrows {X : C} {Y : Over X} {I : Type*} (Z : I -> Over X) (g :
 forall i, Z i ⟶ Y) : overEquiv Y (ofArrows Z g) = ofArrows (fun i => (Z i).left
) (fun i => (g i).left)
参数：Z : I -> Over X；g : forall i, Z i ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Sieve.functorPushforward_ofArrows`：functorPushforward_ofA
rrows {X : C} {ι : Type*} {Y : ι -> C} (f : forall i, Y i ⟶ X) : functorPushforw
ard F (ofArrows Y f) = ofArrows _ fun …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma overEquiv_ofArrows {X : C} {Y : Over X} {I : Type*} (Z : I → Over X) (g : ∀ i, Z i ⟶ Y) :
    overEquiv Y (ofArrows Z g) = ofArrows (fun i => (Z i).left) (fun i => (g i).left) := by
  simp [Sieve.overEquiv, functorPushforward_ofArrows]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.Sieve.overEquiv_preOneHypercover_sieve** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.Sieve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma overEquiv_preOneHypercover_sieve₁ {X : C} {Y : Over X} (E : PreOneHypercover.{w} Y)
    {i₁ i₂ : E.I₀} {W : Over X} (p₁ : W ⟶ E.X i₁) (p₂ : W ⟶ E.X i₂) :
    overEquiv W (E.sieve₁ p₁ p₂) =
      (E.map (Over.forget X)).sieve₁ p₁.left p₂.left := by
  ext
  rw [overEquiv_iff]
  refine ⟨fun ⟨k, b, hb₁, hb₂⟩ ↦ ⟨k, b.left, congr($(hb₁).left), congr($(hb₂).left)⟩, ?_⟩
  intro ⟨k, b, hb₁, hb₂⟩
  exact ⟨k, Over.homMk b (by simpa using (hb₁ =≫ (E.X i₁).hom).symm), by cat_disch, by cat_disch⟩

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.Sieve.overEquiv_generate** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.Sieve`。
形式化陈述：overEquiv_generate {X : C} {Y : Over X} (R : Presieve Y) : overEquiv Y (.g
enerate R) = .generate (Presieve.functorPushforward (Over.forget X) R)
参数：R : Presieve Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Sieve.overEquiv_iff`：overEquiv_iff {X : C} {Y : Over X} (
S : Sieve Y) {Z : C} (f : Z ⟶ Y.left) : overEquiv Y S f ↔ S (Over.homMk f : Over
.mk (f ≫ Y.hom) ⟶ Y)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Sieve.generate_le_iff`：generate_le_iff (R : Presieve X) (
S : Sieve X) : generate R <= S ↔ R <= S
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Over.w`：w : φ.left ≫ g.hom = f.hom
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma overEquiv_generate {X : C} {Y : Over X} (R : Presieve Y) :
    overEquiv Y (.generate R) = .generate (Presieve.functorPushforward (Over.forget X) R) := by
  refine le_antisymm (fun Z g hg ↦ ?_) ?_
  · rw [overEquiv_iff] at hg
    obtain ⟨W, u, v, hv, huv⟩ := hg
    exact ⟨W.left, u.left, v.left, ⟨W, v, 𝟙 _, hv, by simp⟩, congr($(huv).left)⟩
  · rw [generate_le_iff]
    rintro Z g ⟨W, u, v, hu, rfl⟩
    exact (overEquiv_iff _ _).mpr ⟨W, Over.homMk v, u, hu, rfl⟩

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Sieve.overEquiv_symm_generate** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.Sieve`。
形式化陈述：overEquiv_symm_generate {X : C} {Y : Over X} (R : Presieve Y.left) : (over
Equiv Y).symm (.generate R) = .generate (Presieve.functorPullback (Over.forget X
) R)
参数：R : Presieve Y.left。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Sieve.overEquiv_symm_iff`：overEquiv_symm_iff {X : C} {Y :
 Over X} (S : Sieve Y.left) {Z : Over X} (f : Z ⟶ Y) : (overEquiv Y).symm S f ↔ 
S f.left
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Mathlib.Tactic.Reassoc.eq_whisker'`：eq_whisker' {C : Type*} [Category* C
] {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) : f ≫ h = g ≫ h
· 使用定理 `CategoryTheory.Over.w`：w : φ.left ≫ g.hom = f.hom
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Over.OverMorphism.ext`：∀ {T : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} T] {X : T} {U V : CategoryTheory.Over X} {f g : U ⟶ V},  
 CategoryTheory.Over.Hom.l…
· 使用定理 `CategoryTheory.Sieve.generate_le_iff`：generate_le_iff (R : Presieve X) (
S : Sieve X) : generate R <= S ↔ R <= S
· 使用定理 `CategoryTheory.Sieve.le_generate`：le_generate (R : Presieve X) : R <= ge
nerate R
-/
lemma overEquiv_symm_generate {X : C} {Y : Over X} (R : Presieve Y.left) :
    (overEquiv Y).symm (.generate R) =
      .generate (Presieve.functorPullback (Over.forget X) R) := by
  refine le_antisymm (fun Z g hg ↦ ?_) ?_
  · rw [overEquiv_symm_iff] at hg
    obtain ⟨W, p, q, hq, hpq⟩ := hg
    refine ⟨.mk (q ≫ Y.hom), Over.homMk p (by simp [reassoc_of% hpq]), Over.homMk q rfl, hq, ?_⟩
    ext
    exact hpq
  · rw [generate_le_iff]
    exact fun Z g hg ↦ le_generate _ _ _ hg

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**CategoryTheory.Sieve.functorPushforward_over_map** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.Sieve`。
形式化陈述：functorPushforward_over_map {X Y : C} (f : X ⟶ Y) (Z : Over X) (S : Sieve 
Z.left) : Sieve.functorPushforward (Over.map f) ((Sieve.overEquiv Z).symm S) = (
Sieve.overEquiv ((Over.map f).obj Z)).symm S
参数：f : X ⟶ Y；Z : Over X；S : Sieve Z.left。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Sieve.ext`：∀ {C : Type u₁} [inst : CategoryTheory.Categor
y.{v₁, u₁} C] {X : C} {R S : CategoryTheory.Sieve X},   (∀ ⦃Y : C⦄ (f : Y ⟶ X), 
R.arrows f ↔ S…
· 使用定理 `CategoryTheory.Sieve.downward_closed`：∀ {C : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} C] {X : C} (self : CategoryTheory.Sieve X) {Y Z : C}   {f
 : Y ⟶ X}, self.arrows f →…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Over.w`：w : φ.left ≫ g.hom = f.hom
· 使用定理 `CategoryTheory.Over.OverMorphism.ext`：∀ {T : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} T] {X : T} {U V : CategoryTheory.Over X} {f g : U ⟶ V},  
 CategoryTheory.Over.Hom.l…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma functorPushforward_over_map {X Y : C} (f : X ⟶ Y) (Z : Over X) (S : Sieve Z.left) :
    Sieve.functorPushforward (Over.map f) ((Sieve.overEquiv Z).symm S) =
      (Sieve.overEquiv ((Over.map f).obj Z)).symm S := by
  ext W g
  constructor
  · rintro ⟨T, a, b, ha, rfl⟩
    exact S.downward_closed ha _
  · intro hg
    exact ⟨Over.mk (g.left ≫ Z.hom), Over.homMk g.left,
      Over.homMk (𝟙 _) (by simpa using Over.w g), hg, by cat_disch⟩

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Sieve.overEquiv_functorPullback_map** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.Sieve`。
形式化陈述：overEquiv_functorPullback_map {X Y : C} (f : X ⟶ Y) (U : Over X) (S : Siev
e ((Over.map f).obj U)) : overEquiv U (S.functorPullback (Over.map f)) = overEqu
iv ((Over.map f).obj U) S
参数：f : X ⟶ Y；U : Over X；S : Sieve ((Over.map f).obj U)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Sieve.ext`：∀ {C : Type u₁} [inst : CategoryTheory.Categor
y.{v₁, u₁} C] {X : C} {R S : CategoryTheory.Sieve X},   (∀ ⦃Y : C⦄ (f : Y ⟶ X), 
R.arrows f ↔ S…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Over.OverMorphism.ext`：∀ {T : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} T] {X : T} {U V : CategoryTheory.Over X} {f g : U ⟶ V},  
 CategoryTheory.Over.Hom.l…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用引理 `CategoryTheory.Sieve.overEquiv_iff`：overEquiv_iff {X : C} {Y : Over X} (
S : Sieve Y) {Z : C} (f : Z ⟶ Y.left) : overEquiv Y S f ↔ S (Over.homMk f : Over
.mk (f ≫ Y.hom) ⟶ Y)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma overEquiv_functorPullback_map {X Y : C} (f : X ⟶ Y) (U : Over X)
    (S : Sieve ((Over.map f).obj U)) :
    overEquiv U (S.functorPullback (Over.map f)) =
      overEquiv ((Over.map f).obj U) S := by
  ext Z g
  let u : (Over.map f).obj (Over.mk (g ≫ U.hom)) ⟶ Over.mk (g ≫ U.hom ≫ f) :=
    Over.homMk (𝟙 Z) (by simp)
  have heq : (Over.map f).map (Over.homMk (U := Over.mk (g ≫ U.hom)) g rfl) =
      u ≫ Over.homMk (V := (Over.map f).obj U) g rfl := by
    ext
    simp [u]
  have : IsIso u :=
    ⟨Over.homMk (𝟙 Z) (by simp), by ext; simp [u], by ext; simp [u]⟩
  rw [Sieve.overEquiv_iff, Sieve.overEquiv_iff]
  simp [Presieve.functorPullback, heq]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Sieve.overEquiv_functorPullback_post** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Sieve`。
形式化陈述：overEquiv_functorPullback_post {D : Type*} [Category* D] (F : C ⥤ D) {X : 
C} (U : Over X) (S : Sieve ((Over.post F).obj U)) : (Sieve.overEquiv U) (Sieve.f
unctorPullback (Over.post F) S) = Sieve.functorPullback F ((Sieve.overEquiv ((Ov
er.post F).obj U)) S)
参数：F : C ⥤ D；U : Over X；S : Sieve ((Over.post F).obj U)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Sieve.functorPushforward_le_iff_le_functorPullback`：funct
orPushforward_le_iff_le_functorPullback {X : C} (S : Sieve X) (R : Sieve (F.obj 
X)) : S.functorPushforward F <= R ↔ S <= R.functorPullb…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Sieve.functorPullback_comp`：functorPullback_comp (R : Sie
ve ((F ⋙ G).obj X)) : R.functorPullback (F ⋙ G) = (R.functorPullback G).functorP
ullback F
· 使用定理 `CategoryTheory.Sieve.functorPullback_monotone`：functorPullback_monotone 
(X : C) : Monotone (Sieve.functorPullback F : Sieve (F.obj X) -> Sieve X)
· 使用定理 `CategoryTheory.Sieve.le_functorPushforward_pullback`：le_functorPushforwa
rd_pullback (R : Sieve X) : R <= (R.functorPushforward F).functorPullback F
· 使用引理 `CategoryTheory.Sieve.overEquiv_iff`：overEquiv_iff {X : C} {Y : Over X} (
S : Sieve Y) {Z : C} (f : Z ⟶ Y.left) : overEquiv Y S f ↔ S (Over.homMk f : Over
.mk (f ≫ Y.hom) ⟶ Y)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
lemma overEquiv_functorPullback_post {D : Type*} [Category* D] (F : C ⥤ D) {X : C}
    (U : Over X) (S : Sieve ((Over.post F).obj U)) :
    (Sieve.overEquiv U) (Sieve.functorPullback (Over.post F) S) =
      Sieve.functorPullback F ((Sieve.overEquiv ((Over.post F).obj U)) S) := by
  refine le_antisymm ?_ ?_
  · dsimp [Sieve.overEquiv]
    rw [Sieve.functorPushforward_le_iff_le_functorPullback, ← Sieve.functorPullback_comp]
    simp_rw [← CategoryTheory.Over.post_forget_eq_forget_comp, Sieve.functorPullback_comp]
    exact Sieve.functorPullback_monotone _ _ (Sieve.le_functorPushforward_pullback _ _)
  · intro Z g hg
    rw [Sieve.overEquiv_iff]
    dsimp [Presieve.functorPullback]
    convert! (Sieve.overEquiv_iff _ _).mp hg
    simp

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Sieve.overEquiv_functorPushforward_post** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.Sieve`。
形式化陈述：overEquiv_functorPushforward_post {D : Type*} [Category* D] (F : C ⥤ D) {X
 : C} (U : Over X) (S : Sieve U) : (Sieve.overEquiv _) (Sieve.functorPushforward
 (Over.post F) S) = Sieve.functorPushforward F ((Sieve.overEquiv _) S)
参数：F : C ⥤ D；U : Over X；S : Sieve U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma overEquiv_functorPushforward_post {D : Type*} [Category* D] (F : C ⥤ D) {X : C}
    (U : Over X) (S : Sieve U) :
    (Sieve.overEquiv _) (Sieve.functorPushforward (Over.post F) S) =
      Sieve.functorPushforward F ((Sieve.overEquiv _) S) := by
  simp [Sieve.overEquiv, ← Sieve.functorPushforward_comp, ← Over.post_forget_eq_forget_comp]

end Sieve

variable (J : GrothendieckTopology C)

namespace GrothendieckTopology

/-- The Grothendieck topology on the category `Over X` for any `X : C` that is
induced by a Grothendieck topology on `C`. -/
/-
**CategoryTheory.GrothendieckTopology.over** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.GrothendieckTopology`。
形式化陈述：over (X : C) : GrothendieckTopology (Over X) where sieves Y
参数：X : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Grothendieck topology on the category `Over X` for any `X : C` that is
induced by a Grothendieck topology on `C`.
-/
def over (X : C) : GrothendieckTopology (Over X) where
  sieves Y := Sieve.overEquiv Y ⁻¹' J Y.left
  top_mem' Y := by simp
  pullback_stable' Y₁ Y₂ S₁ f h₁ := by
    rw [Set.mem_preimage, Sieve.overEquiv_pullback]
    exact J.pullback_stable _ h₁
  transitive' Y S hS R hR := J.transitive hS _ fun Z f hf => by
    specialize hR ((Sieve.overEquiv_iff _ _).1 hf)
    rwa [Set.mem_preimage, Sieve.overEquiv_pullback] at hR
/-
**CategoryTheory.GrothendieckTopology.mem_over_iff** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.GrothendieckTopology`。
形式化陈述：mem_over_iff {X : C} {Y : Over X} (S : Sieve Y) : S in (J.over X) Y ↔ Siev
e.overEquiv _ S in J Y.left
参数：S : Sieve Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_over_iff {X : C} {Y : Over X} (S : Sieve Y) :
    S ∈ (J.over X) Y ↔ Sieve.overEquiv _ S ∈ J Y.left := by
  rfl
/-
**CategoryTheory.GrothendieckTopology.overEquiv_symm_mem_over** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：overEquiv_symm_mem_over {X : C} (Y : Over X) (S : Sieve Y.left) (hS : S in
 J Y.left) : (Sieve.overEquiv Y).symm S in (J.over X) Y
参数：Y : Over X；S : Sieve Y.left；hS : S in J Y.left。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OrderIso.apply_symm_apply`：apply_symm_apply (e : α ≃o β) (x : β) : e (e.
symm x) = x
-/
lemma overEquiv_symm_mem_over {X : C} (Y : Over X) (S : Sieve Y.left) (hS : S ∈ J Y.left) :
    (Sieve.overEquiv Y).symm S ∈ (J.over X) Y := by
  simpa only [mem_over_iff, OrderIso.apply_symm_apply] using hS
/-
**CategoryTheory.GrothendieckTopology.over_forget_coverPreserving** 是 Mathlib 中的
一个引理，位于命名空间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：over_forget_coverPreserving (X : C) : CoverPreserving (J.over X) J (Over.f
orget X) where cover_preserve hS
参数：X : C。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma over_forget_coverPreserving (X : C) :
    CoverPreserving (J.over X) J (Over.forget X) where
  cover_preserve hS := hS

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.GrothendieckTopology.over_forget_compatiblePreserving** 是 Mathl
ib 中的一个引理，位于命名空间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：over_forget_compatiblePreserving (X : C) : CompatiblePreserving J (Over.fo
rget X) where compatible {_ Z _ _ hx Y₁ Y₂ W f₁ f₂ g₁ g₂ hg₁ hg₂ h}
参数：X : C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Over.w`：w : φ.left ≫ g.hom = f.hom
· 使用定理 `CategoryTheory.eq_whisker`：eq_whisker {f g : X ⟶ Y} (w : f = g) (h : Y ⟶
 Z) : f ≫ h = g ≫ h
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Over.OverMorphism.ext`：∀ {T : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} T] {X : T} {U V : CategoryTheory.Over X} {f g : U ⟶ V},  
 CategoryTheory.Over.Hom.l…
-/
lemma over_forget_compatiblePreserving (X : C) :
    CompatiblePreserving J (Over.forget X) where
  compatible {_ Z _ _ hx Y₁ Y₂ W f₁ f₂ g₁ g₂ hg₁ hg₂ h} := by
    let W' : Over X := Over.mk (f₁ ≫ Y₁.hom)
    let g₁' : W' ⟶ Y₁ := Over.homMk f₁
    let g₂' : W' ⟶ Y₂ := Over.homMk f₂ (by simpa using! h.symm =≫ Z.hom)
    exact hx g₁' g₂' hg₁ hg₂ (by ext; exact h)
/-
**CategoryTheory.GrothendieckTopology.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory
.GrothendieckTopology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : C) : (Over.forget X).IsCocontinuous (J.over X) J where
  cover_lift hS := J.overEquiv_symm_mem_over _ _ hS
/-
**CategoryTheory.GrothendieckTopology.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory
.GrothendieckTopology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : C) : (Over.forget X).IsContinuous (J.over X) J :=
  Functor.isContinuous_of_coverPreserving
    (over_forget_compatiblePreserving J X)
    (over_forget_coverPreserving J X)

/-- The pullback functor `Sheaf J A ⥤ Sheaf (J.over X) A` -/
/-
**CategoryTheory.GrothendieckTopology.overPullback** 是 Mathlib 中的一个缩写定义，位于命名空间 `
CategoryTheory.GrothendieckTopology`。
形式化陈述：overPullback (A : Type u') [Category.{v'} A] (X : C) : Sheaf J A ⥤ Sheaf (
J.over X) A
参数：A : Type u'；X : C。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrothendieckTopology.instIsContinuousOverForgetOver`：∀ {C
 : Type u} [inst : CategoryTheory.Category.{v, u} C] (J : CategoryTheory.Grothen
dieckTopology C) (X : C),   (CategoryTheory.Over.forget …

--- 原说明 ---
The pullback functor `Sheaf J A ⥤ Sheaf (J.over X) A`
-/
abbrev overPullback (A : Type u') [Category.{v'} A] (X : C) :
    Sheaf J A ⥤ Sheaf (J.over X) A :=
  (Over.forget X).sheafPushforwardContinuous _ _ _
/-
**CategoryTheory.GrothendieckTopology.over_map_coverPreserving** 是 Mathlib 中的一个引
理，位于命名空间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：over_map_coverPreserving {X Y : C} (f : X ⟶ Y) : CoverPreserving (J.over X
) (J.over Y) (Over.map f) where cover_preserve {U S} hS
参数：f : X ⟶ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.surjective`：∀ {α : Type u_2} {β : Type u_3} [inst : LE α] [inst
_1 : LE β] (e : α ≃o β), Function.Surjective ⇑e
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Sieve.functorPushforward_over_map`：functorPushforward_ove
r_map {X Y : C} (f : X ⟶ Y) (Z : Over X) (S : Sieve Z.left) : Sieve.functorPushf
orward (Over.map f) ((Sieve.overEquiv …
· 使用引理 `CategoryTheory.GrothendieckTopology.overEquiv_symm_mem_over`：overEquiv_s
ymm_mem_over {X : C} (Y : Over X) (S : Sieve Y.left) (hS : S in J Y.left) : (Sie
ve.overEquiv Y).symm S in (J.over X) Y
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `OrderIso.apply_symm_apply`：apply_symm_apply (e : α ≃o β) (x : β) : e (e.
symm x) = x
-/
lemma over_map_coverPreserving {X Y : C} (f : X ⟶ Y) :
    CoverPreserving (J.over X) (J.over Y) (Over.map f) where
  cover_preserve {U S} hS := by
    obtain ⟨S, rfl⟩ := (Sieve.overEquiv U).symm.surjective S
    rw [Sieve.functorPushforward_over_map]
    apply overEquiv_symm_mem_over
    simpa [mem_over_iff] using! hS

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.GrothendieckTopology.over_map_compatiblePreserving** 是 Mathlib 
中的一个引理，位于命名空间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：over_map_compatiblePreserving {X Y : C} (f : X ⟶ Y) : CompatiblePreserving
 (J.over Y) (Over.map f) where compatible {F Z _ x hx Y₁ Y₂ W f₁ f₂ g₁ g₂ hg₁ hg
₂ h}
参数：f : X ⟶ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Over.w`：w : φ.left ≫ g.hom = f.hom
· 使用定理 `CategoryTheory.eq_whisker`：eq_whisker {f g : X ⟶ Y} (w : f = g) (h : Y ⟶
 Z) : f ≫ h = g ≫ h
· 使用定理 `CategoryTheory.Functor.congr_map`：congr_map (F : C ⥤ D) {X Y : C} {f g :
 X ⟶ Y} (h : f = g) : F.map f = F.map g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `CategoryTheory.Functor.map_comp_apply`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, 
u₂} D]   (self : CategoryTh…
· 使用定理 `CategoryTheory.ConcreteCategory.congr_hom`：congr_hom {X Y : C} {f g : X 
⟶ Y} (h : f = g) (x : ToType X) : f x = g x
· 使用定理 `CategoryTheory.op_comp`：op_comp {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} : (f
 ≫ g).op = g.op ≫ f.op
· 使用定理 `CategoryTheory.Over.OverMorphism.ext`：∀ {T : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} T] {X : T} {U V : CategoryTheory.Over X} {f g : U ⟶ V},  
 CategoryTheory.Over.Hom.l…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
lemma over_map_compatiblePreserving {X Y : C} (f : X ⟶ Y) :
    CompatiblePreserving (J.over Y) (Over.map f) where
  compatible {F Z _ x hx Y₁ Y₂ W f₁ f₂ g₁ g₂ hg₁ hg₂ h} := by
    let W' : Over X := Over.mk (f₁.left ≫ Y₁.hom)
    let g₁' : W' ⟶ Y₁ := Over.homMk f₁.left
    let g₂' : W' ⟶ Y₂ := Over.homMk f₂.left
      (by simpa using! (Over.forget _).congr_map h.symm =≫ Z.hom)
    let e : (Over.map f).obj W' ≅ W := Over.isoMk (Iso.refl _)
      (by simpa [W'] using! (Over.w f₁).symm)
    convert congr_arg (F.obj.map e.inv.op)
      (hx g₁' g₂' hg₁ hg₂ (by ext; exact (Over.forget _).congr_map h)) using 1
    all_goals
      dsimp [e, W', g₁', g₂']
      rw [← Functor.map_comp_apply]
      apply ConcreteCategory.congr_hom
      congr 1
      rw [← op_comp]
      congr 1
      ext
      simp
/-
**CategoryTheory.GrothendieckTopology.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory
.GrothendieckTopology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y : C} (f : X ⟶ Y) : (Over.map f).IsContinuous (J.over X) (J.over Y) :=
  Functor.isContinuous_of_coverPreserving
    (over_map_compatiblePreserving J f)
    (over_map_coverPreserving J f)
/-
**CategoryTheory.GrothendieckTopology.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory
.GrothendieckTopology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y : C} (f : X ⟶ Y) : (Over.map f).IsCocontinuous (J.over _) (J.over _) where
  cover_lift {U} S hS := by
    rw [J.mem_over_iff] at hS ⊢
    rwa [Sieve.overEquiv_functorPullback_map]
/-
**CategoryTheory.GrothendieckTopology.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory
.GrothendieckTopology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {D : Type*} [Category* D] (K : GrothendieckTopology D)
    (F : C ⥤ D) (X : C) [F.IsCocontinuous J K] :
    (Over.post (X := X) F).IsCocontinuous (J.over X) (K.over _) where
  cover_lift {U} S hS := by
    rw [GrothendieckTopology.mem_over_iff] at hS ⊢
    rw [Sieve.overEquiv_functorPullback_post]
    exact F.cover_lift J K hS

variable {J} in
/-
**CategoryTheory.GrothendieckTopology._root_.CategoryTheory.CoverPreserving.over
Post** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.GrothendieckTopology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.CategoryTheory.CoverPreserving.overPost {D : Type*} [Category* D]
    {K : GrothendieckTopology D} {F : C ⥤ D} (X : C) (h : CoverPreserving J K F) :
    CoverPreserving (J.over X) (K.over _) (Over.post (X := X) F) where
  cover_preserve {U} S hS := by
    rw [GrothendieckTopology.mem_over_iff] at hS ⊢
    rw [Sieve.overEquiv_functorPushforward_post]
    exact h.cover_preserve hS

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.GrothendieckTopology.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory
.GrothendieckTopology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {J : GrothendieckTopology C} (X : C) :
    (Over.forget X).PreservesOneHypercovers (J.over _) J := by
  intro Y E
  refine ⟨?_, ?_⟩
  · dsimp
    rw [dsimp% PreZeroHypercover.sieve₀_map (F := Over.forget X)]
    exact E.mem₀
  · intro i₁ i₂ W p₁ p₂ w
    have := w =≫ Over.hom _
    simp only [Over.forget_obj, Over.forget_map, Category.assoc, Over.w] at this
    have := E.mem₁ i₁ i₂ (Over.homMk (U := Over.mk (p₁ ≫ Over.hom _)) p₁)
      (Over.homMk (U := Over.mk (p₁ ≫ Over.hom _)) p₂ this.symm) (by ext; simpa)
    rwa [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_preOneHypercover_sieve₁] at this

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.GrothendieckTopology.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory
.GrothendieckTopology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {D : Type*} [Category* D] {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : C ⥤ D) (X : C) [Functor.PreservesOneHypercovers.{w} F J K] :
    Functor.PreservesOneHypercovers.{w} (Over.post F) (J.over X) (K.over _) := by
  intro Y E
  let E' := (E.map (Over.forget X) J).map F K
  refine ⟨?_, ?_⟩
  · dsimp [-Over.post_obj]
    rw [PreZeroHypercover.sieve₀_map, GrothendieckTopology.mem_over_iff,
      Sieve.functorPushforward_ofArrows, Sieve.overEquiv_ofArrows]
    exact E'.mem₀
  · intro i₁ i₂ W p₁ p₂ w
    simp_rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_preOneHypercover_sieve₁,
      ← PreOneHypercover.map_comp, Over.post_forget_eq_forget_comp, PreOneHypercover.map_comp]
    exact E'.mem₁ _ _ _ _ congr($(w).left)
/-
**CategoryTheory.GrothendieckTopology.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory
.GrothendieckTopology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {D : Type*} [Category* D] {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {F : C ⥤ D} (X : C) (Y : D) (f : F.obj X ⟶ Y)
    [(Over.post F).IsContinuous (J.over X) (K.over _)] :
    (Over.post F ⋙ Over.map f).IsContinuous (J.over X) (K.over Y) :=
  Functor.isContinuous_comp _ _ _ (K.over _) _

open Limits
/-
**CategoryTheory.GrothendieckTopology.coverPreserving_overPullback** 是 Mathlib 中
的一个引理，位于命名空间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：coverPreserving_overPullback [HasPullbacks C] {X Y : C} (f : X ⟶ Y) : Cove
rPreserving (J.over Y) (J.over X) (Over.pullback f)
参数：f : X ⟶ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Adjunction.isCocontinuous_iff_coverPreserving`：∀ {C : Typ
e u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {D : Type u_2}   [inst_1 : 
CategoryTheory.Category.{v_2, u_2} D] (J : Categor…
· 使用定理 `CategoryTheory.GrothendieckTopology.instIsCocontinuousOverMapOver`：∀ {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C] (J : CategoryTheory.Grothend
ieckTopology C) {X Y : C}   (f : X ⟶ Y), (CategoryTheor…
-/
lemma coverPreserving_overPullback [HasPullbacks C] {X Y : C} (f : X ⟶ Y) :
    CoverPreserving (J.over Y) (J.over X) (Over.pullback f) := by
  rw [← (Over.mapPullbackAdj f).isCocontinuous_iff_coverPreserving]
  infer_instance
/-
**CategoryTheory.GrothendieckTopology.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory
.GrothendieckTopology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasPullbacks C] {X Y : C} (f : X ⟶ Y) :
    (Over.pullback f).IsContinuous (J.over Y) (J.over X) :=
  (Over.mapPullbackAdj f).isContinuous_of_isCocontinuous _ _

section

variable {C : Type u'} [Category* C] [HasBinaryProducts C] {J : GrothendieckTopology C}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.GrothendieckTopology.coverPreserving_over_star** 是 Mathlib 中的一个
定理，位于命名空间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：coverPreserving_over_star (X : C) : CoverPreserving J (J.over X) (Over.sta
r X) where cover_preserve {U} S hs
参数：X : C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrothendieckTopology.superset_covering`：superset_covering
 (Hss : S <= R) (sjx : S in J X) : R in J X
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Presieve.functorPushforward_comp`：functorPushforward_comp
 (R : Presieve X) : R.functorPushforward (F ⋙ G) = (R.functorPushforward F).func
torPushforward G
· 使用定理 `CategoryTheory.Limits.prod.hom_ext`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinaryProd
uct X Y] {f g : W ⟶ X ⨯ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Limits.prod.map_map`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {A₁ A₂ A₃ B₁ B₂ B₃ : C}   [inst_1 : CategoryTheory.Limits.H
asBinaryProduct A₁ B₁] […
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Limits.prod.lift_map`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {V W X Y Z : C}   [inst_1 : CategoryTheory.Limits.HasBinar
yProduct W X] [inst_2 : C…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.GrothendieckTopology.pullback_stable`：pullback_stable (f 
: Y ⟶ X) (hS : S in J X) : S.pullback f in J Y
-/
theorem coverPreserving_over_star (X : C) :
    CoverPreserving J (J.over X) (Over.star X) where
  cover_preserve {U} S hs := by
    refine J.superset_covering ?_ (J.pullback_stable prod.snd hs)
    intro y f hf
    dsimp [Sieve.overEquiv]
    rw [← Presieve.functorPushforward_comp]
    refine ⟨_, _, prod.lift (f ≫ prod.fst) (𝟙 _), hf, Limits.prod.hom_ext ?_ ?_⟩ <;> simp
/-
**CategoryTheory.GrothendieckTopology.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory
.GrothendieckTopology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : C) : (Over.star X).IsContinuous J (J.over X) :=
  Functor.isContinuous_of_coverPreserving
    (compatiblePreservingOfFlat (J.over X) (Over.star X)) (coverPreserving_over_star X)

end

section

variable (A : Type u') [Category.{v'} A]

/-- The pullback functor `Sheaf (J.over Y) A ⥤ Sheaf (J.over X) A` induced
by a morphism `f : X ⟶ Y`. -/
/-
**CategoryTheory.GrothendieckTopology.overMapPullback** 是 Mathlib 中的一个缩写定义，位于命名空
间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：overMapPullback {X Y : C} (f : X ⟶ Y) : Sheaf (J.over Y) A ⥤ Sheaf (J.over
 X) A
参数：f : X ⟶ Y。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrothendieckTopology.instIsContinuousOverMapOver`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] (J : CategoryTheory.Grothendie
ckTopology C) {X Y : C}   (f : X ⟶ Y), (CategoryTheor…

--- 原说明 ---
The pullback functor `Sheaf (J.over Y) A ⥤ Sheaf (J.over X) A` induced
by a morphism `f : X ⟶ Y`.
-/
abbrev overMapPullback {X Y : C} (f : X ⟶ Y) :
    Sheaf (J.over Y) A ⥤ Sheaf (J.over X) A :=
  (Over.map f).sheafPushforwardContinuous _ _ _

section

variable {X Y : C} {f g : X ⟶ Y} (h : f = g)

/-- Two identical morphisms give isomorphic `overMapPullback` functors on sheaves. -/
@[simps!]
/-
**CategoryTheory.GrothendieckTopology.overMapPullbackCongr** 是 Mathlib 中的一个定义，位于
命名空间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：overMapPullbackCongr : J.overMapPullback A f ≅ J.overMapPullback A g
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrothendieckTopology.instIsContinuousOverMapOver`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] (J : CategoryTheory.Grothendie
ckTopology C) {X Y : C}   (f : X ⟶ Y), (CategoryTheor…

--- 原说明 ---
Two identical morphisms give isomorphic `overMapPullback` functors on sheaves.
-/
def overMapPullbackCongr :
    J.overMapPullback A f ≅ J.overMapPullback A g :=
  Functor.sheafPushforwardContinuousIso (Over.mapCongr _ _ h) _ _ _
/-
**CategoryTheory.GrothendieckTopology.overMapPullbackCongr_eq_eqToIso** 是 Mathli
b 中的一个引理，位于命名空间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：overMapPullbackCongr_eq_eqToIso : J.overMapPullbackCongr A h = eqToIso (by
 subst h; rfl)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `CategoryTheory.ObjectProperty.hom_ext`：hom_ext {X Y : P.FullSubcategory}
 {f g : X ⟶ Y} (h : f.hom = g.hom) : f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.GrothendieckTopology.instIsContinuousOverMapOver`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] (J : CategoryTheory.Grothendie
ckTopology C) {X Y : C}   (f : X ⟶ Y), (CategoryTheor…
· 使用定理 `CategoryTheory.GrothendieckTopology.overMapPullbackCongr_hom_app_hom_app
`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (J : CategoryTheory.G
rothendieckTopology C) (A : Type u')   [inst_1 : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
-/
lemma overMapPullbackCongr_eq_eqToIso :
    J.overMapPullbackCongr A h = eqToIso (by subst h; rfl) := by
  aesop

end

/-- Applying `overMapPullback` to the identity map gives the identity functor. -/
@[simps!]
/-
**CategoryTheory.GrothendieckTopology.overMapPullbackId** 是 Mathlib 中的一个定义，位于命名空
间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：overMapPullbackId (X : C) : J.overMapPullback A (𝟙 X) ≅ 𝟭 _
参数：X : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Applying `overMapPullback` to the identity map gives the identity functor.
-/
def overMapPullbackId (X : C) :
    J.overMapPullback A (𝟙 X) ≅ 𝟭 _ :=
  Functor.sheafPushforwardContinuousId' (Over.mapId X) _ _

/-- The composition of two `overMapPullback` functors identifies to
`overMapPullback` for the composition. -/
@[simps!]
/-
**CategoryTheory.GrothendieckTopology.overMapPullbackComp** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：overMapPullbackComp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : J.overMapPullbac
k A g ⋙ J.overMapPullback A f ≅ J.overMapPullback A (f ≫ g)
参数：f : X ⟶ Y；g : Y ⟶ Z。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrothendieckTopology.instIsContinuousOverMapOver`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] (J : CategoryTheory.Grothendie
ckTopology C) {X Y : C}   (f : X ⟶ Y), (CategoryTheor…

--- 原说明 ---
The composition of two `overMapPullback` functors identifies to
`overMapPullback` for the composition.
-/
def overMapPullbackComp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    J.overMapPullback A g ⋙ J.overMapPullback A f ≅
      J.overMapPullback A (f ≫ g) :=
  Functor.sheafPushforwardContinuousComp' (Over.mapComp f g).symm _ _ _ _

set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/-
**CategoryTheory.GrothendieckTopology.overMapPullback_comp_id** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：overMapPullback_comp_id {X Y : C} (f : X ⟶ Y) : (J.overMapPullbackComp A f
 (𝟙 Y)).inv ≫ Functor.whiskerRight (J.overMapPullbackId A Y).hom _ ≫ (Functor.le
ftUnitor _).hom = (overMapPullbackCongr _ _ (by simp)).hom
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `CategoryTheory.ObjectProperty.hom_ext`：hom_ext {X Y : P.FullSubcategory}
 {f g : X ⟶ Y} (h : f.hom = g.hom) : f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.GrothendieckTopology.overMapPullbackComp_inv_app_hom_app`
：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (J : CategoryTheory.Gr
othendieckTopology C) (A : Type u')   [inst_1 : CategoryTheor…
· 使用定理 `CategoryTheory.GrothendieckTopology.overMapPullbackId_hom_app_hom_app`：∀
 {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (J : CategoryTheory.Grot
hendieckTopology C) (A : Type u')   [inst_1 : CategoryTheor…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Over.OverMorphism.ext`：∀ {T : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} T] {X : T} {U V : CategoryTheory.Over X} {f g : U ⟶ V},  
 CategoryTheory.Over.Hom.l…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma overMapPullback_comp_id {X Y : C} (f : X ⟶ Y) :
    (J.overMapPullbackComp A f (𝟙 Y)).inv ≫
      Functor.whiskerRight (J.overMapPullbackId A Y).hom _ ≫ (Functor.leftUnitor _).hom =
    (overMapPullbackCongr _ _ (by simp)).hom := by
  ext
  dsimp
  simp only [overMapPullbackComp_inv_app_hom_app, overMapPullbackId_hom_app_hom_app,
    comp_id, ← Functor.map_comp, ← op_comp]
  congr
  cat_disch

set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/-
**CategoryTheory.GrothendieckTopology.overMapPullback_id_comp** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：overMapPullback_id_comp {X Y : C} (f : X ⟶ Y) : (J.overMapPullbackComp A (
𝟙 X) f).inv ≫ Functor.whiskerLeft _ (J.overMapPullbackId A X).hom ≫ (Functor.rig
htUnitor _).hom = (overMapPullbackCongr _ _ (by simp)).hom
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `CategoryTheory.ObjectProperty.hom_ext`：hom_ext {X Y : P.FullSubcategory}
 {f g : X ⟶ Y} (h : f.hom = g.hom) : f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.GrothendieckTopology.overMapPullbackComp_inv_app_hom_app`
：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (J : CategoryTheory.Gr
othendieckTopology C) (A : Type u')   [inst_1 : CategoryTheor…
· 使用定理 `CategoryTheory.GrothendieckTopology.overMapPullbackId_hom_app_hom_app`：∀
 {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (J : CategoryTheory.Grot
hendieckTopology C) (A : Type u')   [inst_1 : CategoryTheor…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Over.OverMorphism.ext`：∀ {T : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} T] {X : T} {U V : CategoryTheory.Over X} {f g : U ⟶ V},  
 CategoryTheory.Over.Hom.l…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma overMapPullback_id_comp {X Y : C} (f : X ⟶ Y) :
    (J.overMapPullbackComp A (𝟙 X) f).inv ≫
      Functor.whiskerLeft _ (J.overMapPullbackId A X).hom ≫ (Functor.rightUnitor _).hom =
    (overMapPullbackCongr _ _ (by simp)).hom := by
  ext
  dsimp
  simp only [overMapPullbackComp_inv_app_hom_app, overMapPullbackId_hom_app_hom_app,
    Functor.sheafPushforwardContinuous_obj_obj_map, Quiver.Hom.unop_op,
    comp_id, ← Functor.map_comp, ← op_comp]
  congr
  cat_disch

set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/-
**CategoryTheory.GrothendieckTopology.overMapPullback_assoc** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：overMapPullback_assoc {X Y Z T : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) : 
(J.overMapPullbackComp A f (g ≫ h)).inv ≫ Functor.whiskerRight (J.overMapPullbac
kComp A g h).inv _ ≫ (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft _ (J.o
verMapPullbackComp A f g).hom ≫ (J.overMapPullbackComp A (f ≫ g) h).hom = (overM
apPullbackCongr _ _ (by simp)).hom
参数：f : X ⟶ Y；g : Y ⟶ Z；h : Z ⟶ T。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `CategoryTheory.ObjectProperty.hom_ext`：hom_ext {X Y : P.FullSubcategory}
 {f g : X ⟶ Y} (h : f.hom = g.hom) : f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.GrothendieckTopology.overMapPullbackComp_inv_app_hom_app`
：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (J : CategoryTheory.Gr
othendieckTopology C) (A : Type u')   [inst_1 : CategoryTheor…
· 使用定理 `CategoryTheory.GrothendieckTopology.overMapPullbackComp_hom_app_hom_app`
：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (J : CategoryTheory.Gr
othendieckTopology C) (A : Type u')   [inst_1 : CategoryTheor…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Over.OverMorphism.ext`：∀ {T : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} T] {X : T} {U V : CategoryTheory.Over X} {f g : U ⟶ V},  
 CategoryTheory.Over.Hom.l…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma overMapPullback_assoc {X Y Z T : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) :
    (J.overMapPullbackComp A f (g ≫ h)).inv ≫
      Functor.whiskerRight (J.overMapPullbackComp A g h).inv _ ≫
        (Functor.associator _ _ _).hom ≫
          Functor.whiskerLeft _ (J.overMapPullbackComp A f g).hom ≫
            (J.overMapPullbackComp A (f ≫ g) h).hom =
    (overMapPullbackCongr _ _ (by simp)).hom := by
  ext
  dsimp
  simp only [overMapPullbackComp_inv_app_hom_app,
    overMapPullbackComp_hom_app_hom_app, Functor.sheafPushforwardContinuous_obj_obj_map,
    Quiver.Hom.unop_op, ← Functor.map_comp, ← op_comp, id_comp, assoc]
  congr
  cat_disch

end

end GrothendieckTopology

variable {J}

/-- Given `F : Sheaf J A` and `X : C`, this is the pullback of `F` on `J.over X`. -/
/-
**CategoryTheory.Sheaf.over** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Sheaf`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {J : Cate
goryTheory.GrothendieckTopology C} →       {A : Type u'} →         [inst_1 : Cat
egoryTheory.Category.{v', u'} A] →           CategoryTheory.Sheaf J A → (X : C) 
→ CategoryTheory.Sheaf (J.over X) A
参数：X : C；J.over X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `F : Sheaf J A` and `X : C`, this is the pullback of `F` on `J.over X`.
-/
abbrev Sheaf.over {A : Type u'} [Category.{v'} A] (F : Sheaf J A) (X : C) :
    Sheaf (J.over X) A := (J.overPullback A X).obj F

variable {A : Type u'} [Category.{v'} A]

set_option backward.defeqAttrib.useBackward true in
/-- For `f : X ⟶ Y`, `F.over Y` viewed as a sheaf on `Over X` is isomorphic to `F.Over X`. -/
@[simps! +dsimpLhs]
/-
**CategoryTheory.Sheaf.pushforwardOverMapIso** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Sheaf`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {J : Cate
goryTheory.GrothendieckTopology C} →       {A : Type u'} →         [inst_1 : Cat
egoryTheory.Category.{v', u'} A] →           (F : CategoryTheory.Sheaf J A) →   
          {X Y : C} →               (f : X ⟶ Y) →                 ((CategoryTheo
ry.Over.map f).sheafPushforwardContinuous A (J.over X) (J.over Y)).obj (F.over Y
) ≅                   F.over X
参数：F : CategoryTheory.Sheaf J A；f : X ⟶ Y；(CategoryTheory.Over.map f).sheafPushf
orwardContinuous A (J.over X) (J.over Y)；F.over Y。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrothendieckTopology.instIsContinuousOverMapOver`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] (J : CategoryTheory.Grothendie
ckTopology C) {X Y : C}   (f : X ⟶ Y), (CategoryTheor…

--- 原说明 ---
For `f : X ⟶ Y`, `F.over Y` viewed as a sheaf on `Over X` is isomorphic to `F.Ov
er X`.
-/
def Sheaf.pushforwardOverMapIso (F : Sheaf J A) {X Y : C} (f : X ⟶ Y) :
    ((Over.map f).sheafPushforwardContinuous A (J.over X) (J.over Y)).obj (F.over Y) ≅
      F.over X :=
  ObjectProperty.isoMk _ (NatIso.ofComponents (fun _ ↦ Iso.refl _) (by simp))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- For `f : X ⟶ Y`, this is the morphism from `F.over Y` to the pushforward of `F.over X`
along `Over.pullback f` induced by `Limits.pullback.fst`. -/
@[simps]
noncomputable
/-
**CategoryTheory.Sheaf.toPushforwardOverPullback** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Sheaf`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {J : Cate
goryTheory.GrothendieckTopology C} →       {A : Type u'} →         [inst_1 : Cat
egoryTheory.Category.{v', u'} A] →           [inst_2 : CategoryTheory.Limits.Has
Pullbacks C] →             (F : CategoryTheory.Sheaf J A) →               {X Y :
 C} →                 (f : X ⟶ Y) →                   F.over Y ⟶                
     ((CategoryTheory.Over.pullback f).sheafPushforwardContinuous A (J.over Y) (
J.over X)).obj (F.over X)
参数：F : CategoryTheory.Sheaf J A；f : X ⟶ Y；(CategoryTheory.Over.pullback f).sheaf
PushforwardContinuous A (J.over Y) (J.over X)；F.over X。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrothendieckTopology.instIsContinuousOverPullbackOver`：∀ 
{C : Type u} [inst : CategoryTheory.Category.{v, u} C] (J : CategoryTheory.Groth
endieckTopology C)   [inst_1 : CategoryTheory.Limits.HasPu…
-/
def Sheaf.toPushforwardOverPullback [Limits.HasPullbacks C] (F : Sheaf J A)
    {X Y : C} (f : X ⟶ Y) :
    F.over Y ⟶ ((Over.pullback f).sheafPushforwardContinuous A _ _).obj (F.over X) where
  hom.app U := F.obj.map (.op <| Limits.pullback.fst _ _)
  hom.naturality := by simp [← Functor.map_comp, ← op_comp]

section

-- TODO: Generalize this section to arbitrary precoverages.

variable (K : Precoverage C) [K.HasPullbacks] [K.IsStableUnderBaseChange]

set_option backward.isDefEq.respectTransparency.types false in
/-- The Grothendieck topology on `Over X`, obtained from localizing the topology generated
by the precoverage `K`, is generated by the preimage of `K`. -/
/-
**CategoryTheory.over_toGrothendieck_eq_toGrothendieck_comap_forget** 是 Mathlib 
中的一个引理，位于命名空间 `CategoryTheory`。
形式化陈述：over_toGrothendieck_eq_toGrothendieck_comap_forget (X : C) : K.toGrothendi
eck.over X = (K.comap (Over.forget X)).toGrothendieck
参数：X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `OrderIso.surjective`：∀ {α : Type u_2} {β : Type u_3} [inst : LE α] [inst
_1 : LE β] (e : α ≃o β), Function.Surjective ⇑e
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Sieve.overEquiv_symm_generate`：overEquiv_symm_generate {X
 : C} {Y : Over X} (R : Presieve Y.left) : (overEquiv Y).symm (.generate R) = .g
enerate (Presieve.functorPullback …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `CategoryTheory.Presieve.map_functorPullback_overForget`：map_functorPullb
ack_overForget {X : C} {Y : Over X} (R : Presieve Y.left) : (R.functorPullback (
Over.forget X)).map (Over.forget X) = R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `TopHomClass.map_top`：∀ {F : Type u_6} {α : outParam (Type u_7)} {β : out
Param (Type u_8)} {inst : Top α} {inst_1 : Top β}   {inst_2 : FunLike F α β} [se
lf : TopH…
· 使用定理 `InfTopHomClass.toTopHomClass`：∀ {F : Type u_1} {α : Type u_2} {β : Type 
u_3} [inst : FunLike F α β] [inst_1 : Min α] [inst_2 : Min β] [inst_3 : Top α]  
 [inst_4 : Top β] …
· 使用定理 `OrderIsoClass.toInfTopHomClass`：∀ {F : Type u_1} {α : Type u_2} {β : Typ
e u_3} [inst : EquivLike F α β] [inst_1 : SemilatticeInf α]   [inst_2 : OrderTop
 α] [inst_3 : Semila…
· 使用定理 `OrderIso.instOrderIsoClass`：∀ {α : Type u_2} {β : Type u_3} [inst : LE α
] [inst_1 : LE β], OrderIsoClass (α ≃o β) α β
· 使用定理 `CategoryTheory.GrothendieckTopology.transitive`：transitive (hS : S in J 
X) (R : Sieve X) (h : forall ⦃Y⦄ ⦃f : Y ⟶ X⦄, S f -> R.pullback f in J Y) : R in
 J X
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.Sieve.overEquiv_symm_pullback`：overEquiv_symm_pullback {X
 : C} {Y₁ Y₂ : Over X} (f : Y₁ ⟶ Y₂) (S : Sieve Y₂.left) : (overEquiv Y₁).symm (
pullback f.left S) = pullback f ((…
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `CategoryTheory.Discrete.instSubsingleton`：∀ {α : Type u₁} [Subsingleton 
α], Subsingleton (CategoryTheory.Discrete α)
· 使用定理 `instSubsingletonPUnit`：Subsingleton PUnit.{u_1}
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `OrderIso.apply_symm_apply`：apply_symm_apply (e : α ≃o β) (x : β) : e (e.
symm x) = x
· 使用引理 `CategoryTheory.Precoverage.toGrothendieck_le_iff_le_toPrecoverage`：toGro
thendieck_le_iff_le_toPrecoverage : K.toGrothendieck <= J ↔ K <= J.toPrecoverage
· 使用引理 `CategoryTheory.GrothendieckTopology.mem_toPrecoverage_iff`：mem_toPrecove
rage_iff (J : GrothendieckTopology C) {S : C} (R : Presieve S) : R in toPrecover
age J S ↔ Sieve.generate R in J S
· 使用引理 `CategoryTheory.GrothendieckTopology.mem_over_iff`：mem_over_iff {X : C} {
Y : Over X} (S : Sieve Y) : S in (J.over X) Y ↔ Sieve.overEquiv _ S in J Y.left
· 使用引理 `CategoryTheory.Sieve.functorPullback_functorPushforward_overForget`：func
torPullback_functorPushforward_overForget {X : C} {Y : Over X} (S : Sieve Y) : (
S.functorPushforward (Over.forget X)).functorPullback (O…
· 使用引理 `CategoryTheory.Sieve.functorPushforward_functorPullback_overForget`：func
torPushforward_functorPullback_overForget {X : C} {Y : Over X} (S : Sieve Y.left
) : (S.functorPullback (Over.forget X)).functorPushforwa…
· 使用定理 `CategoryTheory.Sieve.overEquiv.eq_1`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X : C} (Y : CategoryTheory.Over X),   CategoryTheory.Siev
e.overEquiv Y =     { toF…
· 使用定理 `RelIso.coe_fn_mk`：coe_fn_mk (f : α ≃ β) (o : forall ⦃a b⦄, s (f a) (f b)
 ↔ r a b) : (RelIso.mk f @o : α -> β) = f
· 使用定理 `Equiv.coe_fn_mk`：∀ {α : Sort u} {β : Sort v} (f : α → β) (g : β → α) (l 
: Function.LeftInverse g f) (r : Function.RightInverse g f),   ⇑{ toFun := f, in
vFun …
· 使用定理 `CategoryTheory.Sieve.generate_map_eq_functorPushforward`：generate_map_eq
_functorPushforward {s : Presieve X} : generate (s.map F) = (generate s).functor
Pushforward F
· 使用引理 `CategoryTheory.Precoverage.mem_comap_iff`：mem_comap_iff {X : C} {R : Pre
sieve X} : R in J.comap F X ↔ R.map F in J (F.obj X)

--- 原说明 ---
The Grothendieck topology on `Over X`, obtained from localizing the topology gen
erated
by the precoverage `K`, is generated by the preimage of `K`.
-/
lemma over_toGrothendieck_eq_toGrothendieck_comap_forget (X : C) :
    K.toGrothendieck.over X = (K.comap (Over.forget X)).toGrothendieck := by
  refine le_antisymm ?_ ?_
  · intro ⟨Y, right, (s : Y ⟶ X)⟩ R hR
    obtain ⟨(R : Sieve Y), rfl⟩ := (Sieve.overEquiv _).symm.surjective R
    simp only [GrothendieckTopology.mem_over_iff, OrderIso.apply_symm_apply,
      ← Precoverage.toGrothendieck_toCoverage, Coverage.mem_toGrothendieck,
      Over.left] at hR
    induction hR with
    | of Z S hS =>
      rw [Sieve.overEquiv_symm_generate]
      exact .of _ _ (by simpa)
    | top =>
      simp
    | transitive Y R S hR H ih ih' =>
      refine GrothendieckTopology.transitive _ (ih s) _ fun Z g hg ↦ ?_
      obtain rfl : right = Z.right := Subsingleton.elim _ _
      rw [← Sieve.overEquiv_symm_pullback]
      exact ih' hg Z.hom
  · rw [Precoverage.toGrothendieck_le_iff_le_toPrecoverage]
    intro Y R hR
    rw [Precoverage.mem_comap_iff] at hR
    rw [GrothendieckTopology.mem_toPrecoverage_iff, GrothendieckTopology.mem_over_iff,
      Sieve.overEquiv, RelIso.coe_fn_mk, Equiv.coe_fn_mk,
      ← Sieve.generate_map_eq_functorPushforward]
    exact Precoverage.Saturate.of _ _ hR

end

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X : C} (f : Over X) :
    f.iteratedSliceEquiv.inverse.IsDenseSubsite (J.over _) ((J.over _).over _) where
  functorPushforward_mem_iff := by
    simp [GrothendieckTopology.mem_over_iff, Sieve.overEquiv,
      ← Over.iteratedSliceBackward_forget_forget f, Sieve.functorPushforward_comp]
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X : C} (f : Over X) :
    f.iteratedSliceForward.IsContinuous ((J.over _).over _) (J.over _) :=
  inferInstanceAs (f.iteratedSliceEquiv.functor.IsContinuous _ _)
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X : C} (f : Over X) :
    f.iteratedSliceForward.IsCocontinuous ((J.over _).over _) (J.over _) :=
  inferInstanceAs (f.iteratedSliceEquiv.functor.IsCocontinuous _ _)
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X : C} (f : Over X) :
    f.iteratedSliceBackward.IsContinuous (J.over _) ((J.over _).over _) :=
  inferInstanceAs (f.iteratedSliceEquiv.inverse.IsContinuous _ _)
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X : C} (f : Over X) :
    f.iteratedSliceBackward.IsCocontinuous (J.over _) ((J.over _).over _) :=
  inferInstanceAs (f.iteratedSliceEquiv.inverse.IsCocontinuous _ _)

end CategoryTheory

