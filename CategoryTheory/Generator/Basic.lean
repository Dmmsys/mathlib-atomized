/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Equalizers
public import Mathlib.CategoryTheory.Subobject.Lattice
public import Mathlib.CategoryTheory.ObjectProperty.Small
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import Mathlib.CategoryTheory.ObjectProperty.LimitsOfShape
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small

/-!
# Separating and detecting sets

There are several non-equivalent notions of a generator of a category. Here, we consider two of
them:

* We say that `P : ObjectProperty C` is a separating set if the functors `C(G, -)`
    for `G` such that `P G` are collectively faithful, i.e., if
    `h ≫ f = h ≫ g` for all `h` with domain satisfying `P` implies `f = g`.
* We say that `P : ObjectProperty C` is a detecting set if the functors `C(G, -)`
    collectively reflect isomorphisms, i.e., if any `h` with domain satisfying `P`
    uniquely factors through `f`, then `f` is an isomorphism.

There are, of course, also the dual notions of coseparating and codetecting sets.

## Main results

We
* define predicates `IsSeparating`, `IsCoseparating`, `IsDetecting` and `IsCodetecting` on
  `ObjectProperty C`;
* show that equivalences of categories preserve these notions;
* show that separating and coseparating are dual notions;
* show that detecting and codetecting are dual notions;
* show that if `C` has equalizers, then detecting implies separating;
* show that if `C` has coequalizers, then codetecting implies coseparating;
* show that if `C` is balanced, then separating implies detecting and coseparating implies
  codetecting;
* show that `∅` is separating if and only if `∅` is coseparating if and only if `C` is thin;
* show that `∅` is detecting if and only if `∅` is codetecting if and only if `C` is a groupoid;
* define predicates `IsSeparator`, `IsCoseparator`, `IsDetector` and `IsCodetector` as the
  singleton counterparts to the definitions for sets above and restate the above results in this
  situation;
* show that `G` is a separator if and only if `coyoneda.obj (op G)` is faithful (and the dual);
* show that `G` is a detector if and only if `coyoneda.obj (op G)` reflects isomorphisms (and the
  dual);
* show that `C` is `WellPowered` if it admits small pullbacks and a detector;
* define corresponding typeclasses `HasSeparator`, `HasCoseparator`, `HasDetector`
  and `HasCodetector` on categories and prove analogous results for these.

## Examples

See the files `CategoryTheory.Generator.Presheaf` and `CategoryTheory.Generator.Sheaf`.

-/

@[expose] public section


universe w' w v₁ v₂ u₁ u₂

open CategoryTheory.Limits Opposite

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

namespace ObjectProperty

variable (P : ObjectProperty C)

/-- We say that `P : ObjectProperty C` is separating if the functors `C(G, -)`
for `G : C` such that `P G` are collectively faithful,
i.e., if `h ≫ f = h ≫ g` for all `h` with domain in `𝒢` implies `f = g`. -/
/-
**CategoryTheory.ObjectProperty.IsSeparating** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.ObjectProperty`。
形式化陈述：IsSeparating : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say that `P : ObjectProperty C` is separating if the functors `C(G, -)`
for `G : C` such that `P G` are collectively faithful,
i.e., if `h ≫ f = h ≫ g` for all `h` with domain in `𝒢` implies `f = g`.
-/
def IsSeparating : Prop :=
  ∀ ⦃X Y : C⦄ (f g : X ⟶ Y), (∀ (G : C) (_ : P G) (h : G ⟶ X), h ≫ f = h ≫ g) → f = g

/-- We say that `P : ObjectProperty C` is coseparating if the functors `C(-, G)`
for `G : C` such that `P G` are collectively faithful,
i.e., if `f ≫ h = g ≫ h` for all `h` with codomain in `𝒢` implies `f = g`. -/
/-
**CategoryTheory.ObjectProperty.IsCoseparating** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.ObjectProperty`。
形式化陈述：IsCoseparating : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say that `P : ObjectProperty C` is coseparating if the functors `C(-, G)`
for `G : C` such that `P G` are collectively faithful,
i.e., if `f ≫ h = g ≫ h` for all `h` with codomain in `𝒢` implies `f = g`.
-/
def IsCoseparating : Prop :=
  ∀ ⦃X Y : C⦄ (f g : X ⟶ Y), (∀ (G : C) (_ : P G) (h : Y ⟶ G), f ≫ h = g ≫ h) → f = g

/-- We say that `P : ObjectProperty C` is detecting if the functors `C(G, -)`
for `G : C` such that `P G` collectively reflect isomorphisms,
i.e., if any `h` with domain `G` that `P G` uniquely factors through `f`,
then `f` is an isomorphism. -/
/-
**CategoryTheory.ObjectProperty.IsDetecting** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.ObjectProperty`。
形式化陈述：IsDetecting : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say that `P : ObjectProperty C` is detecting if the functors `C(G, -)`
for `G : C` such that `P G` collectively reflect isomorphisms,
i.e., if any `h` with domain `G` that `P G` uniquely factors through `f`,
then `f` is an isomorphism.
-/
def IsDetecting : Prop :=
  ∀ ⦃X Y : C⦄ (f : X ⟶ Y), (∀ (G : C) (_ : P G),
    ∀ (h : G ⟶ Y), ∃! h' : G ⟶ X, h' ≫ f = h) → IsIso f

/-- We say that `P : ObjectProperty C` is codetecting if the functors `C(-, G)`
for `G : C` such that `P G` collectively reflect isomorphisms,
i.e., if any `h` with codomain `G` such that `P G` uniquely factors through `f`,
then `f` is an isomorphism. -/
/-
**CategoryTheory.ObjectProperty.IsCodetecting** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.ObjectProperty`。
形式化陈述：IsCodetecting : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say that `P : ObjectProperty C` is codetecting if the functors `C(-, G)`
for `G : C` such that `P G` collectively reflect isomorphisms,
i.e., if any `h` with codomain `G` such that `P G` uniquely factors through `f`,
then `f` is an isomorphism.
-/
def IsCodetecting : Prop :=
  ∀ ⦃X Y : C⦄ (f : X ⟶ Y), (∀ (G : C) (_ : P G),
    ∀ (h : X ⟶ G), ∃! h' : Y ⟶ G, f ≫ h' = h) → IsIso f

section Equivalence

variable {P}

/-
**CategoryTheory.ObjectProperty.IsSeparating.of_equivalence** 是 Mathlib 中的一个定理，位
于命名空间 `CategoryTheory.ObjectProperty.IsSeparating`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {P : CategoryT
heory.ObjectProperty C},   P.IsSeparating →     ∀ {D : Type u_1} [inst_1 : Categ
oryTheory.Category.{v_1, u_1} D] (α : C ≌ D), (P.strictMap α.functor).IsSeparati
ng
参数：α : C ≌ D；P.strictMap α.functor。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.map_injective`：map_injective (F : C ⥤ D) [Faithfu
l F] : Function.Injective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Adjunction.homEquiv_unit`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `CategoryTheory.ObjectProperty.strictMap_obj`：strictMap_obj (P : ObjectPr
operty C) (F : C ⥤ D) {X : C} (hX : P X) : P.strictMap F (F.obj X)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma IsSeparating.of_equivalence
    (h : IsSeparating P) {D : Type*} [Category* D] (α : C ≌ D) :
    IsSeparating (P.strictMap α.functor) := fun X Y f g H =>
  α.inverse.map_injective (h _ _ (fun Z hZ h ↦ by
    obtain ⟨h', rfl⟩ := (α.toAdjunction.homEquiv _ _).surjective h
    simp only [Adjunction.homEquiv_unit, Category.assoc, ← Functor.map_comp,
      H _ (P.strictMap_obj _ hZ) h']))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.ObjectProperty.IsCoseparating.of_equivalence** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.ObjectProperty.IsCoseparating`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {P : CategoryT
heory.ObjectProperty C},   P.IsCoseparating →     ∀ {D : Type u_1} [inst_1 : Cat
egoryTheory.Category.{v_1, u_1} D] (α : C ≌ D), (P.strictMap α.functor).IsCosepa
rating
参数：α : C ≌ D；P.strictMap α.functor。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.map_injective`：map_injective (F : C ⥤ D) [Faithfu
l F] : Function.Injective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Adjunction.homEquiv_counit`：∀ {C : Type u₁} [inst : Categ
oryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{
v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `CategoryTheory.ObjectProperty.strictMap_obj`：strictMap_obj (P : ObjectPr
operty C) (F : C ⥤ D) {X : C} (hX : P X) : P.strictMap F (F.obj X)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma IsCoseparating.of_equivalence
    (h : IsCoseparating P) {D : Type*} [Category* D] (α : C ≌ D) :
    IsCoseparating (P.strictMap α.functor) := fun X Y f g H =>
  α.inverse.map_injective (h _ _ (fun Z hZ h ↦ by
    obtain ⟨h', rfl⟩ := (α.symm.toAdjunction.homEquiv _ _).symm.surjective h
    simp only [Equivalence.symm_inverse, Equivalence.symm_functor,
      Adjunction.homEquiv_counit, ← Functor.map_comp_assoc,
      H _ (P.strictMap_obj _ hZ) h']))

end Equivalence

section Dual

/-
**CategoryTheory.ObjectProperty.isSeparating_op_iff** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.ObjectProperty`。
形式化陈述：isSeparating_op_iff : IsSeparating P.op ↔ IsCoseparating P
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quiver.Hom.op_inj`：Quiver.Hom.op_inj {X Y : C} : Function.Injective (Qui
ver.Hom.op : (X ⟶ Y) -> (Opposite.op Y ⟶ Opposite.op X))
· 使用定理 `Quiver.Hom.unop_inj`：Quiver.Hom.unop_inj {X Y : Cᵒᵖ} : Function.Injectiv
e (Quiver.Hom.unop : (X ⟶ Y) -> (Opposite.unop Y ⟶ Opposite.unop X))
-/
theorem isSeparating_op_iff : IsSeparating P.op ↔ IsCoseparating P := by
  refine ⟨fun hP X Y f g hfg => ?_, fun hP X Y f g hfg => ?_⟩
  · refine Quiver.Hom.op_inj (hP _ _ fun G hG h => Quiver.Hom.unop_inj ?_)
    simpa only [unop_comp, Quiver.Hom.unop_op] using hfg _ hG _
  · refine Quiver.Hom.unop_inj (hP _ _ fun G hG h => Quiver.Hom.op_inj ?_)
    simpa only [op_comp, Quiver.Hom.op_unop] using hfg _ hG _
/-
**CategoryTheory.ObjectProperty.isCoseparating_op_iff** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.ObjectProperty`。
形式化陈述：isCoseparating_op_iff : IsCoseparating P.op ↔ IsSeparating P
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quiver.Hom.op_inj`：Quiver.Hom.op_inj {X Y : C} : Function.Injective (Qui
ver.Hom.op : (X ⟶ Y) -> (Opposite.op Y ⟶ Opposite.op X))
· 使用定理 `Quiver.Hom.unop_inj`：Quiver.Hom.unop_inj {X Y : Cᵒᵖ} : Function.Injectiv
e (Quiver.Hom.unop : (X ⟶ Y) -> (Opposite.unop Y ⟶ Opposite.unop X))
-/
theorem isCoseparating_op_iff : IsCoseparating P.op ↔ IsSeparating P := by
  refine ⟨fun hP X Y f g hfg => ?_, fun hP X Y f g hfg => ?_⟩
  · refine Quiver.Hom.op_inj (hP _ _ fun G hG h => Quiver.Hom.unop_inj ?_)
    simpa only [unop_comp, Quiver.Hom.unop_op] using hfg _ hG _
  · refine Quiver.Hom.unop_inj (hP _ _ fun G hG h => Quiver.Hom.op_inj ?_)
    simpa only [op_comp, Quiver.Hom.op_unop] using hfg _ hG _
/-
**CategoryTheory.ObjectProperty.isCoseparating_unop_iff** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.ObjectProperty`。
形式化陈述：isCoseparating_unop_iff (P : ObjectProperty Cᵒᵖ) : IsCoseparating P.unop ↔
 IsSeparating P
参数：P : ObjectProperty Cᵒᵖ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `CategoryTheory.ObjectProperty.isSeparating_op_iff`：isSeparating_op_iff :
 IsSeparating P.op ↔ IsCoseparating P
-/
theorem isCoseparating_unop_iff (P : ObjectProperty Cᵒᵖ) :
    IsCoseparating P.unop ↔ IsSeparating P :=
  P.unop.isSeparating_op_iff.symm
/-
**CategoryTheory.ObjectProperty.isSeparating_unop_iff** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.ObjectProperty`。
形式化陈述：isSeparating_unop_iff (P : ObjectProperty Cᵒᵖ) : IsSeparating P.unop ↔ IsC
oseparating P
参数：P : ObjectProperty Cᵒᵖ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `CategoryTheory.ObjectProperty.isCoseparating_op_iff`：isCoseparating_op_i
ff : IsCoseparating P.op ↔ IsSeparating P
-/
theorem isSeparating_unop_iff (P : ObjectProperty Cᵒᵖ) :
    IsSeparating P.unop ↔ IsCoseparating P :=
  P.unop.isCoseparating_op_iff.symm
/-
**CategoryTheory.ObjectProperty.isDetecting_op_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.ObjectProperty`。
形式化陈述：isDetecting_op_iff : IsDetecting P.op ↔ IsCodetecting P
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.isIso_op_iff`：isIso_op_iff {X Y : C} (f : X ⟶ Y) : IsIso 
f.op ↔ IsIso f
· 使用定理 `Quiver.Hom.unop_inj`：Quiver.Hom.unop_inj {X Y : Cᵒᵖ} : Function.Injectiv
e (Quiver.Hom.unop : (X ⟶ Y) -> (Opposite.unop Y ⟶ Opposite.unop X))
· 使用定理 `Quiver.Hom.op_inj`：Quiver.Hom.op_inj {X Y : C} : Function.Injective (Qui
ver.Hom.op : (X ⟶ Y) -> (Opposite.op Y ⟶ Opposite.op X))
· 使用定理 `CategoryTheory.isIso_unop_iff`：isIso_unop_iff {X Y : Cᵒᵖ} (f : X ⟶ Y) : 
IsIso f.unop ↔ IsIso f
-/
theorem isDetecting_op_iff : IsDetecting P.op ↔ IsCodetecting P := by
  refine ⟨fun hP X Y f hf => ?_, fun hP X Y f hf => ?_⟩
  · refine (isIso_op_iff _).1 (hP _ fun G hG h => ?_)
    obtain ⟨t, ht, ht'⟩ := hf (unop G) hG h.unop
    exact
      ⟨t.op, Quiver.Hom.unop_inj ht, fun y hy => Quiver.Hom.unop_inj (ht' _ (Quiver.Hom.op_inj hy))⟩
  · refine (isIso_unop_iff _).1 (hP _ fun G hG h => ?_)
    obtain ⟨t, ht, ht'⟩ := hf (op G) hG h.op
    refine ⟨t.unop, Quiver.Hom.op_inj ht, fun y hy => Quiver.Hom.op_inj (ht' _ ?_)⟩
    exact Quiver.Hom.unop_inj (by simpa only using! hy)
/-
**CategoryTheory.ObjectProperty.isCodetecting_op_iff** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.ObjectProperty`。
形式化陈述：isCodetecting_op_iff : IsCodetecting P.op ↔ IsDetecting P
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.isIso_op_iff`：isIso_op_iff {X Y : C} (f : X ⟶ Y) : IsIso 
f.op ↔ IsIso f
· 使用定理 `Quiver.Hom.unop_inj`：Quiver.Hom.unop_inj {X Y : Cᵒᵖ} : Function.Injectiv
e (Quiver.Hom.unop : (X ⟶ Y) -> (Opposite.unop Y ⟶ Opposite.unop X))
· 使用定理 `Quiver.Hom.op_inj`：Quiver.Hom.op_inj {X Y : C} : Function.Injective (Qui
ver.Hom.op : (X ⟶ Y) -> (Opposite.op Y ⟶ Opposite.op X))
· 使用定理 `CategoryTheory.isIso_unop_iff`：isIso_unop_iff {X Y : Cᵒᵖ} (f : X ⟶ Y) : 
IsIso f.unop ↔ IsIso f
-/
theorem isCodetecting_op_iff : IsCodetecting P.op ↔ IsDetecting P := by
  refine ⟨fun hP X Y f hf => ?_, fun hP X Y f hf => ?_⟩
  · refine (isIso_op_iff _).1 (hP _ fun G hG h => ?_)
    obtain ⟨t, ht, ht'⟩ := hf (unop G) hG h.unop
    exact
      ⟨t.op, Quiver.Hom.unop_inj ht, fun y hy => Quiver.Hom.unop_inj (ht' _ (Quiver.Hom.op_inj hy))⟩
  · refine (isIso_unop_iff _).1 (hP _ fun G hG h => ?_)
    obtain ⟨t, ht, ht'⟩ := hf (op G) hG h.op
    refine ⟨t.unop, Quiver.Hom.op_inj ht, fun y hy => Quiver.Hom.op_inj (ht' _ ?_)⟩
    exact Quiver.Hom.unop_inj (by simpa only using! hy)
/-
**CategoryTheory.ObjectProperty.isDetecting_unop_iff** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.ObjectProperty`。
形式化陈述：isDetecting_unop_iff (P : ObjectProperty Cᵒᵖ) : IsDetecting P.unop ↔ IsCod
etecting P
参数：P : ObjectProperty Cᵒᵖ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `CategoryTheory.ObjectProperty.isCodetecting_op_iff`：isCodetecting_op_iff
 : IsCodetecting P.op ↔ IsDetecting P
-/
theorem isDetecting_unop_iff (P : ObjectProperty Cᵒᵖ) : IsDetecting P.unop ↔ IsCodetecting P :=
  P.unop.isCodetecting_op_iff.symm
/-
**CategoryTheory.ObjectProperty.isCodetecting_unop_iff** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.ObjectProperty`。
形式化陈述：isCodetecting_unop_iff (P : ObjectProperty Cᵒᵖ) : IsCodetecting P.unop ↔ I
sDetecting P
参数：P : ObjectProperty Cᵒᵖ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `CategoryTheory.ObjectProperty.isDetecting_op_iff`：isDetecting_op_iff : I
sDetecting P.op ↔ IsCodetecting P
-/
theorem isCodetecting_unop_iff (P : ObjectProperty Cᵒᵖ) : IsCodetecting P.unop ↔ IsDetecting P :=
  P.unop.isDetecting_op_iff.symm

end Dual

variable {P}

/-
**CategoryTheory.ObjectProperty.IsDetecting.isSeparating** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.ObjectProperty.IsDetecting`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {P : CategoryT
heory.ObjectProperty C}   [CategoryTheory.Limits.HasEqualizers C], P.IsDetecting
 → P.IsSeparating
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.equalizer.existsUnique`：∀ {C : Type u} {X Y : C} [
inst : CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y}   [inst_1 : CategoryTheor
y.Limits.HasEqualizer f g] {W : C}…
· 使用定理 `CategoryTheory.Limits.eq_of_epi_equalizer`：eq_of_epi_equalizer [HasEqual
izer f g] [Epi (equalizer.ι f g)] : f = g
· 使用定理 `CategoryTheory.StrongEpi.epi`：∀ {C : Type u} {inst : CategoryTheory.Cate
gory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongEpi f],   Cate
goryTheory.Epi f
· 使用定理 `CategoryTheory.strongEpi_of_isIso`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] {P Q : C} (f : P ⟶ Q) [CategoryTheory.IsIso f],   CategoryTh
eory.StrongEpi f
-/
theorem IsDetecting.isSeparating [HasEqualizers C] (hP : IsDetecting P) :
    IsSeparating P := fun _ _ f g hfg =>
  have : IsIso (equalizer.ι f g) := hP _ fun _ hG _ => equalizer.existsUnique _ (hfg _ hG _)
  eq_of_epi_equalizer
/-
**CategoryTheory.ObjectProperty.IsCodetecting.isCoseparating** 是 Mathlib 中的一个定理，
位于命名空间 `CategoryTheory.ObjectProperty.IsCodetecting`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {P : CategoryT
heory.ObjectProperty C}   [CategoryTheory.Limits.HasCoequalizers C], P.IsCodetec
ting → P.IsCoseparating
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `CategoryTheory.ObjectProperty.IsDetecting.isSeparating`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {P : CategoryTheory.ObjectProperty C
}   [CategoryTheory.Limits.HasEqualizers C],…
-/
theorem IsCodetecting.isCoseparating [HasCoequalizers C] :
    IsCodetecting P → IsCoseparating P := by
  simpa only [← isSeparating_op_iff, ← isDetecting_op_iff] using IsDetecting.isSeparating
/-
**CategoryTheory.ObjectProperty.IsSeparating.mono_iff** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.ObjectProperty.IsSeparating`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {P : CategoryT
heory.ObjectProperty C},   P.IsSeparating →     ∀ {X Y : C} (f : X ⟶ Y),       C
ategoryTheory.Mono f ↔         ∀ (G : C),           P G →             ∀ (g₁ g₂ :
 G ⟶ X),               CategoryTheory.CategoryStruct.comp g₁ f = CategoryTheory.
CategoryStruct.comp g₂ f → g₁ = g₂
参数：f : X ⟶ Y；G : C；g₁ g₂ : G ⟶ X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma IsSeparating.mono_iff (hP : IsSeparating P) {X Y : C} (f : X ⟶ Y) :
    Mono f ↔ ∀ (G : C) (_ : P G), ∀ (g₁ g₂ : G ⟶ X), g₁ ≫ f = g₂ ≫ f → g₁ = g₂ :=
  ⟨fun _ _ _ _ _ h ↦ by simpa [cancel_mono] using h,
    fun hf ↦ ⟨fun g₁ g₂ h ↦ hP _ _  (fun G hG h' ↦ hf _ hG _ _ (by simp [h]))⟩⟩
/-
**CategoryTheory.ObjectProperty.IsCoseparating.epi_iff** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.ObjectProperty.IsCoseparating`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {P : CategoryT
heory.ObjectProperty C},   P.IsCoseparating →     ∀ {X Y : C} (f : X ⟶ Y),      
 CategoryTheory.Epi f ↔         ∀ (G : C),           P G →             ∀ (g₁ g₂ 
: Y ⟶ G),               CategoryTheory.CategoryStruct.comp f g₁ = CategoryTheory
.CategoryStruct.comp f g₂ → g₁ = g₂
参数：f : X ⟶ Y；G : C；g₁ g₂ : Y ⟶ G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Mathlib.Tactic.Reassoc.eq_whisker'`：eq_whisker' {C : Type*} [Category* C
] {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) : f ≫ h = g ≫ h
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma IsCoseparating.epi_iff (hP : IsCoseparating P) {X Y : C} (f : X ⟶ Y) :
    Epi f ↔ ∀ (G : C) (_ : P G), ∀ (g₁ g₂ : Y ⟶ G), f ≫ g₁ = f ≫ g₂ → g₁ = g₂ :=
  ⟨fun _ _ _ _ _ h ↦ by simpa [cancel_epi] using h,
    fun hf ↦ ⟨fun g₁ g₂ h ↦ hP _ _  (fun G hG h' ↦ hf _ hG _ _ (by simp [reassoc_of% h]))⟩⟩
/-
**CategoryTheory.ObjectProperty.IsSeparating.isDetecting** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.ObjectProperty.IsSeparating`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {P : CategoryT
heory.ObjectProperty C}   [CategoryTheory.Balanced C], P.IsSeparating → P.IsDete
cting
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.isIso_iff_mono_and_epi`：isIso_iff_mono_and_epi [Balanced 
C] {X Y : C} (f : X ⟶ Y) : IsIso f ↔ Mono f ∧ Epi f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem IsSeparating.isDetecting [Balanced C] (hP : IsSeparating P) :
    IsDetecting P := by
  intro X Y f hf
  refine
    (isIso_iff_mono_and_epi _).2 ⟨⟨fun g h hgh => hP _ _ fun G hG i => ?_⟩, ⟨fun g h hgh => ?_⟩⟩
  · obtain ⟨t, -, ht⟩ := hf G hG (i ≫ g ≫ f)
    rw [ht (i ≫ g) (Category.assoc _ _ _), ht (i ≫ h) (hgh.symm ▸ Category.assoc _ _ _)]
  · refine hP _ _ fun G hG i => ?_
    obtain ⟨t, rfl, -⟩ := hf G hG i
    rw [Category.assoc, hgh, Category.assoc]
/-
**CategoryTheory.ObjectProperty.IsDetecting.isIso_iff_of_mono** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.ObjectProperty.IsDetecting`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {P : CategoryT
heory.ObjectProperty C},   P.IsDetecting →     ∀ {X Y : C} (f : X ⟶ Y) [Category
Theory.Mono f],       CategoryTheory.IsIso f ↔         ∀ (G : C),           P G 
→             Function.Surjective               ⇑(CategoryTheory.ConcreteCategor
y.hom ((CategoryTheory.coyoneda.obj (Opposite.op G)).map f))
参数：f : X ⟶ Y；G : C；CategoryTheory.ConcreteCategory.hom ((CategoryTheory.coyoneda
.obj (Opposite.op G)).map f)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.isIso_iff_yoneda_map_bijective`：isIso_iff_yoneda_map_bije
ctive {X Y : C} (f : X ⟶ Y) : IsIso f ↔ (forall (T : C), Function.Bijective (fun
 (x : T ⟶ X) => x ≫ f))
· 使用定理 `existsUnique_of_exists_of_unique`：existsUnique_of_exists_of_unique {p : 
α -> Prop} (hex : exists x, p x) (hunique : forall y₁ y₂, p y₁ -> p y₂ -> y₁ = y
₂) : exists! x, p x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
-/
lemma IsDetecting.isIso_iff_of_mono (hP : IsDetecting P)
    {X Y : C} (f : X ⟶ Y) [Mono f] :
    IsIso f ↔ ∀ (G : C) (_ : P G), Function.Surjective ((coyoneda.obj (op G)).map f) := by
  constructor
  · intro h
    rw [isIso_iff_yoneda_map_bijective] at h
    intro A _
    exact (h A).2
  · intro hf
    refine hP _ (fun A hA g ↦ existsUnique_of_exists_of_unique ?_ ?_)
    · exact hf A hA g
    · intro l₁ l₂ h₁ h₂
      rw [← cancel_mono f, h₁, h₂]
/-
**CategoryTheory.ObjectProperty.IsCodetecting.isIso_iff_of_epi** 是 Mathlib 中的一个定
理，位于命名空间 `CategoryTheory.ObjectProperty.IsCodetecting`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {P : CategoryT
heory.ObjectProperty C},   P.IsCodetecting →     ∀ {X Y : C} (f : X ⟶ Y) [Catego
ryTheory.Epi f],       CategoryTheory.IsIso f ↔         ∀ (G : C),           P G
 → Function.Surjective ⇑(CategoryTheory.ConcreteCategory.hom ((CategoryTheory.yo
neda.obj G).map f.op))
参数：f : X ⟶ Y；G : C；CategoryTheory.ConcreteCategory.hom ((CategoryTheory.yoneda.o
bj G).map f.op)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.isIso_iff_coyoneda_map_bijective`：isIso_iff_coyoneda_map_
bijective {X Y : C} (f : X ⟶ Y) : IsIso f ↔ (forall (T : C), Function.Bijective 
(fun (x : Y ⟶ T) => f ≫ x))
· 使用定理 `existsUnique_of_exists_of_unique`：existsUnique_of_exists_of_unique {p : 
α -> Prop} (hex : exists x, p x) (hunique : forall y₁ y₂, p y₁ -> p y₂ -> y₁ = y
₂) : exists! x, p x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
-/
lemma IsCodetecting.isIso_iff_of_epi (hP : IsCodetecting P)
    {X Y : C} (f : X ⟶ Y) [Epi f] :
    IsIso f ↔ ∀ (G : C) (_ : P G), Function.Surjective ((yoneda.obj G).map f.op) := by
  constructor
  · intro h
    rw [isIso_iff_coyoneda_map_bijective] at h
    intro A _
    exact (h A).2
  · intro hf
    refine hP _ (fun A hA g ↦ existsUnique_of_exists_of_unique ?_ ?_)
    · exact hf A hA g
    · intro l₁ l₂ h₁ h₂
      rw [← cancel_epi f, h₁, h₂]

section

attribute [local instance] balanced_opposite

/-
**CategoryTheory.ObjectProperty.IsCoseparating.isCodetecting** 是 Mathlib 中的一个定理，
位于命名空间 `CategoryTheory.ObjectProperty.IsCoseparating`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {P : CategoryT
heory.ObjectProperty C}   [CategoryTheory.Balanced C], P.IsCoseparating → P.IsCo
detecting
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `CategoryTheory.ObjectProperty.IsSeparating.isDetecting`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {P : CategoryTheory.ObjectProperty C
}   [CategoryTheory.Balanced C], P.IsSeparat…
-/
theorem IsCoseparating.isCodetecting [Balanced C] :
    IsCoseparating P → IsCodetecting P := by
  simpa only [← isDetecting_op_iff, ← isSeparating_op_iff] using IsSeparating.isDetecting

end

/-
**CategoryTheory.ObjectProperty.isDetecting_iff_isSeparating** 是 Mathlib 中的一个定理，
位于命名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：isDetecting_iff_isSeparating [HasEqualizers C] [Balanced C] : IsDetecting 
P ↔ IsSeparating P
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ObjectProperty.IsDetecting.isSeparating`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {P : CategoryTheory.ObjectProperty C
}   [CategoryTheory.Limits.HasEqualizers C],…
· 使用定理 `CategoryTheory.ObjectProperty.IsSeparating.isDetecting`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {P : CategoryTheory.ObjectProperty C
}   [CategoryTheory.Balanced C], P.IsSeparat…
-/
theorem isDetecting_iff_isSeparating [HasEqualizers C] [Balanced C] :
    IsDetecting P ↔ IsSeparating P :=
  ⟨IsDetecting.isSeparating, IsSeparating.isDetecting⟩
/-
**CategoryTheory.ObjectProperty.isCodetecting_iff_isCoseparating** 是 Mathlib 中的一
个定理，位于命名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：isCodetecting_iff_isCoseparating [HasCoequalizers C] [Balanced C] : IsCode
tecting P ↔ IsCoseparating P
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ObjectProperty.IsCodetecting.isCoseparating`：∀ {C : Type 
u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {P : CategoryTheory.ObjectProper
ty C}   [CategoryTheory.Limits.HasCoequalizers C…
· 使用定理 `CategoryTheory.ObjectProperty.IsCoseparating.isCodetecting`：∀ {C : Type 
u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {P : CategoryTheory.ObjectProper
ty C}   [CategoryTheory.Balanced C], P.IsCosepar…
-/
theorem isCodetecting_iff_isCoseparating [HasCoequalizers C] [Balanced C] :
    IsCodetecting P ↔ IsCoseparating P :=
  ⟨IsCodetecting.isCoseparating, IsCoseparating.isCodetecting⟩

section Mono

/-
**CategoryTheory.ObjectProperty.IsSeparating.of_le** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.ObjectProperty.IsSeparating`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {P : CategoryT
heory.ObjectProperty C},   P.IsSeparating → ∀ {Q : CategoryTheory.ObjectProperty
 C}, P ≤ Q → Q.IsSeparating
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IsSeparating.of_le (hP : IsSeparating P) {Q : ObjectProperty C} (h : P ≤ Q) :
    IsSeparating Q := fun _ _ _ _ hfg => hP _ _ fun _ hG _ => hfg _ (h _ hG) _
/-
**CategoryTheory.ObjectProperty.IsCoseparating.of_le** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.ObjectProperty.IsCoseparating`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {P : CategoryT
heory.ObjectProperty C},   P.IsCoseparating → ∀ {Q : CategoryTheory.ObjectProper
ty C}, P ≤ Q → Q.IsCoseparating
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IsCoseparating.of_le (hP : IsCoseparating P) {Q : ObjectProperty C} (h : P ≤ Q) :
    IsCoseparating Q := fun _ _ _ _ hfg => hP _ _ fun _ hG _ => hfg _ (h _ hG) _
/-
**CategoryTheory.ObjectProperty.IsDetecting.of_le** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.ObjectProperty.IsDetecting`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {P : CategoryT
heory.ObjectProperty C},   P.IsDetecting → ∀ {Q : CategoryTheory.ObjectProperty 
C}, P ≤ Q → Q.IsDetecting
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IsDetecting.of_le (hP : IsDetecting P) {Q : ObjectProperty C} (h : P ≤ Q) :
    IsDetecting Q := fun _ _ _ hf => hP _ fun _ hG _ => hf _ (h _ hG) _
/-
**CategoryTheory.ObjectProperty.IsCodetecting.of_le** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.ObjectProperty.IsCodetecting`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {P : CategoryT
heory.ObjectProperty C},   P.IsCodetecting → ∀ {Q : CategoryTheory.ObjectPropert
y C}, P ≤ Q → Q.IsCodetecting
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IsCodetecting.of_le (h𝒢 : IsCodetecting P) {Q : ObjectProperty C} (h : P ≤ Q) :
    IsCodetecting Q := fun _ _ _ hf => h𝒢 _ fun _ hG _ => hf _ (h _ hG) _

end Mono

section Empty

/-
**CategoryTheory.ObjectProperty.isThin_of_isSeparating_bot** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：isThin_of_isSeparating_bot (h : IsSeparating (⊥ : ObjectProperty C)) : Qui
ver.IsThin C
参数：h : IsSeparating (⊥ : ObjectProperty C)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma isThin_of_isSeparating_bot (h : IsSeparating (⊥ : ObjectProperty C)) :
    Quiver.IsThin C := fun _ _ ↦ ⟨fun _ _ ↦ h _ _ (by simp)⟩
/-
**CategoryTheory.ObjectProperty.isSeparating_bot_of_isThin** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：isSeparating_bot_of_isThin [Quiver.IsThin C] : IsSeparating (⊥ : ObjectPro
perty C)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
lemma isSeparating_bot_of_isThin [Quiver.IsThin C] : IsSeparating (⊥ : ObjectProperty C) :=
  fun _ _ _ _ _ ↦ Subsingleton.elim _ _
/-
**CategoryTheory.ObjectProperty.isThin_of_isCoseparating_bot** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：isThin_of_isCoseparating_bot (h : IsCoseparating (⊥ : ObjectProperty C)) :
 Quiver.IsThin C
参数：h : IsCoseparating (⊥ : ObjectProperty C)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma isThin_of_isCoseparating_bot (h : IsCoseparating (⊥ : ObjectProperty C)) :
    Quiver.IsThin C := fun _ _ ↦ ⟨fun _ _ ↦ h _ _ (by simp)⟩
/-
**CategoryTheory.ObjectProperty.isCoseparating_bot_of_isThin** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：isCoseparating_bot_of_isThin [Quiver.IsThin C] : IsCoseparating (⊥ : Objec
tProperty C)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
lemma isCoseparating_bot_of_isThin [Quiver.IsThin C] : IsCoseparating (⊥ : ObjectProperty C) :=
  fun _ _ _ _ _ ↦ Subsingleton.elim _ _
/-
**CategoryTheory.ObjectProperty.isGroupoid_of_isDetecting_bot** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：isGroupoid_of_isDetecting_bot (h : IsDetecting (⊥ : ObjectProperty C)) : I
sGroupoid C where all_isIso f
参数：h : IsDetecting (⊥ : ObjectProperty C)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma isGroupoid_of_isDetecting_bot (h : IsDetecting (⊥ : ObjectProperty C)) :
    IsGroupoid C where
  all_isIso f := h _ (by simp)
/-
**CategoryTheory.ObjectProperty.isDetecting_bot_of_isGroupoid** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：isDetecting_bot_of_isGroupoid [IsGroupoid C] : IsDetecting (⊥ : ObjectProp
erty C)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsGroupoid.all_isIso`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.IsGroupoid C] {X Y : C} (f : X ⟶ Y)
,   CategoryTheory.IsIso …
-/
lemma isDetecting_bot_of_isGroupoid [IsGroupoid C] :
    IsDetecting (⊥ : ObjectProperty C) :=
  fun _ _ _ _ ↦ inferInstance
/-
**CategoryTheory.ObjectProperty.isGroupoid_of_isCodetecting_bot** 是 Mathlib 中的一个
引理，位于命名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：isGroupoid_of_isCodetecting_bot (h : IsCodetecting (⊥ : ObjectProperty C))
 : IsGroupoid C where all_isIso f
参数：h : IsCodetecting (⊥ : ObjectProperty C)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma isGroupoid_of_isCodetecting_bot (h : IsCodetecting (⊥ : ObjectProperty C)) :
    IsGroupoid C where
  all_isIso f := h _ (by simp)
/-
**CategoryTheory.ObjectProperty.isCodetecting_bot_of_isGroupoid** 是 Mathlib 中的一个
引理，位于命名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：isCodetecting_bot_of_isGroupoid [IsGroupoid C] : IsCodetecting (⊥ : Object
Property C)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsGroupoid.all_isIso`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.IsGroupoid C] {X Y : C} (f : X ⟶ Y)
,   CategoryTheory.IsIso …
-/
lemma isCodetecting_bot_of_isGroupoid [IsGroupoid C] :
    IsCodetecting (⊥ : ObjectProperty C) :=
  fun _ _ _ _ ↦ inferInstance

end Empty

/-
**CategoryTheory.ObjectProperty.IsSeparating.mk_of_exists_epi** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.ObjectProperty.IsSeparating`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {P : CategoryT
heory.ObjectProperty C},   (∀ (X : C), ∃ ι s, ∃ (_ : ∀ (i : ι), P (s i)), ∃ c x 
p, CategoryTheory.Epi p) → P.IsSeparating
参数：∀ (X : C), ∃ ι s, ∃ (_ : ∀ (i : ι), P (s i)), ∃ c x p, CategoryTheory.Epi p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.Limits.Cofan.IsColimit.hom_ext`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] {I : Type u_1} {F : I → C} {c : CategoryTheory.L
imits.Cofan F}   (hc : CategoryTheo…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
-/
lemma IsSeparating.mk_of_exists_epi
    (hP : ∀ (X : C), ∃ (ι : Type w) (s : ι → C) (_ : ∀ i, P (s i)) (c : Cofan s) (_ : IsColimit c)
      (p : c.pt ⟶ X), Epi p) :
    P.IsSeparating := by
  intro X Y f g h
  obtain ⟨ι, s, hs, c, hc, p, _⟩ := hP X
  rw [← cancel_epi p]
  exact Cofan.IsColimit.hom_ext hc _ _
    (fun i ↦ by simpa using h _ (hs i) (c.inj i ≫ p))
/-
**CategoryTheory.ObjectProperty.IsCoseparating.mk_of_exists_mono** 是 Mathlib 中的一
个定理，位于命名空间 `CategoryTheory.ObjectProperty.IsCoseparating`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {P : CategoryT
heory.ObjectProperty C},   (∀ (X : C), ∃ ι s, ∃ (_ : ∀ (i : ι), P (s i)), ∃ c x 
j, CategoryTheory.Mono j) → P.IsCoseparating
参数：∀ (X : C), ∃ ι s, ∃ (_ : ∀ (i : ι), P (s i)), ∃ c x j, CategoryTheory.Mono j。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.Limits.Fan.IsLimit.hom_ext`：∀ {C : Type u} [inst : Catego
ryTheory.Category.{v, u} C] {I : Type u_1} {F : I → C} {c : CategoryTheory.Limit
s.Fan F}   (hc : CategoryTheory…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
-/
lemma IsCoseparating.mk_of_exists_mono
    (hP : ∀ (X : C), ∃ (ι : Type w) (s : ι → C) (_ : ∀ i, P (s i)) (c : Fan s) (_ : IsLimit c)
      (j : X ⟶ c.pt), Mono j) :
    P.IsCoseparating := by
  intro X Y f g h
  obtain ⟨ι, s, hs, c, hc, j, _⟩ := hP Y
  rw [← cancel_mono j]
  exact Fan.IsLimit.hom_ext hc _ _
    (fun i ↦ by simpa using h _ (hs i) (j ≫ c.proj i))
/-
**CategoryTheory.ObjectProperty.IsSeparating.mk_of_exists_colimitsOfShape** 是 Ma
thlib 中的一个定理，位于命名空间 `CategoryTheory.ObjectProperty.IsSeparating`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {P : CategoryT
heory.ObjectProperty C},   (∀ (X : C), ∃ J x, P.colimitsOfShape J X) → P.IsSepar
ating
参数：∀ (X : C), ∃ J x, P.colimitsOfShape J X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsColimit.hom_ext`：∀ {J : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃
, u₃} C]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.ObjectProperty.ColimitOfShape.prop_diag_obj`：∀ {C : Type 
u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {P : CategoryTheory.ObjectPro
perty C} {J : Type u'}   [inst_1 : CategoryTheor…
-/
lemma IsSeparating.mk_of_exists_colimitsOfShape
    (hP : ∀ (X : C), ∃ (J : Type w) (_ : Category.{w'} J), P.colimitsOfShape J X) :
    P.IsSeparating := by
  intro X Y f g h
  obtain ⟨J, _, ⟨p⟩⟩ := hP X
  exact p.isColimit.hom_ext (fun j ↦ h _ (p.prop_diag_obj _) _)
/-
**CategoryTheory.ObjectProperty.IsCoseparating.mk_of_exists_limitsOfShape** 是 Ma
thlib 中的一个定理，位于命名空间 `CategoryTheory.ObjectProperty.IsCoseparating`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {P : CategoryT
heory.ObjectProperty C},   (∀ (X : C), ∃ J x, P.limitsOfShape J X) → P.IsCosepar
ating
参数：∀ (X : C), ∃ J x, P.limitsOfShape J X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsLimit.hom_ext`：hom_ext (h : IsLimit t) {W : C} {
f f' : W ⟶ t.pt} (w : forall j, f ≫ t.π.app j = f' ≫ t.π.app j) : f = f'
· 使用定理 `CategoryTheory.ObjectProperty.LimitOfShape.prop_diag_obj`：∀ {C : Type u_
1} [inst : CategoryTheory.Category.{v_1, u_1} C] {P : CategoryTheory.ObjectPrope
rty C} {J : Type u'}   [inst_1 : CategoryTheor…
-/
lemma IsCoseparating.mk_of_exists_limitsOfShape
    (hP : ∀ (X : C), ∃ (J : Type w) (_ : Category.{w'} J), P.limitsOfShape J X) :
    P.IsCoseparating := by
  intro X Y f g h
  obtain ⟨J, _, ⟨p⟩⟩ := hP Y
  exact p.isLimit.hom_ext (fun j ↦ h _ (p.prop_diag_obj _) _)

variable (P)

section

/-- Given `P : ObjectProperty C` and `X : C`, this is the map which
sends `i : CostructuredArrow P.ι X` to `i.left.obj : C`. The coproduct
of this family is the source of the morphism `P.coproductFrom X`. -/
/-
**CategoryTheory.ObjectProperty.coproductFromFamily** 是 Mathlib 中的一个缩写定义，位于命名空间 
`CategoryTheory.ObjectProperty`。
形式化陈述：coproductFromFamily (X : C) (i : CostructuredArrow P.ι X) : C
参数：X : C；i : CostructuredArrow P.ι X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `P : ObjectProperty C` and `X : C`, this is the map which
sends `i : CostructuredArrow P.ι X` to `i.left.obj : C`. The coproduct
of this family is the source of the morphism `P.coproductFrom X`.
-/
abbrev coproductFromFamily (X : C) (i : CostructuredArrow P.ι X) : C := i.left.obj

variable (X : C)

variable [HasCoproduct (P.coproductFromFamily X)]

/-- Given `P : ObjectProperty C` and `X : C`, this is the coproduct of
all the morphisms `Y ⟶ X` such that `P Y` holds. -/
/-
**CategoryTheory.ObjectProperty.coproductFrom** 是 Mathlib 中的一个缩写定义，位于命名空间 `Categ
oryTheory.ObjectProperty`。
形式化陈述：coproductFrom : ∐ (P.coproductFromFamily X) ⟶ X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `P : ObjectProperty C` and `X : C`, this is the coproduct of
all the morphisms `Y ⟶ X` such that `P Y` holds.
-/
noncomputable abbrev coproductFrom : ∐ (P.coproductFromFamily X) ⟶ X :=
  Sigma.desc (fun i ↦ i.hom)

variable {X} in
/-- The inclusion morphisms to `∐ (P.coproductFromFamily X)`. -/
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.Obj
ectProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion morphisms to `∐ (P.coproductFromFamily X)`.
-/
noncomputable abbrev ιCoproductFrom {Y : C} (f : Y ⟶ X) (hY : P Y) :
    Y ⟶ ∐ (P.coproductFromFamily X) := by
  exact Sigma.ι (P.coproductFromFamily X) (CostructuredArrow.mk (Y := ⟨Y, hY⟩) (by exact f))

end

set_option backward.isDefEq.respectTransparency false in
variable {P} in
/-
**CategoryTheory.ObjectProperty.IsSeparating.epi_coproductFrom** 是 Mathlib 中的一个定
理，位于命名空间 `CategoryTheory.ObjectProperty.IsSeparating`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {P : CategoryT
heory.ObjectProperty C},   P.IsSeparating →     ∀ (X : C) [inst_1 : CategoryTheo
ry.Limits.HasCoproduct (P.coproductFromFamily X)],       CategoryTheory.Epi (P.c
oproductFrom X)
参数：X : C；P.coproductFromFamily X；P.coproductFrom X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc_assoc`：∀ {J : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{
v, u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.whisker_eq`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {X Y Z : C} {f g : Y ⟶ X} (h : Z ⟶ Y),   f = g → CategoryTheory.Cate
goryStruct.comp…
-/
lemma IsSeparating.epi_coproductFrom (hP : P.IsSeparating)
    (X : C) [HasCoproduct (P.coproductFromFamily X)] :
    Epi (P.coproductFrom X) where
  left_cancellation u v huv :=
    hP _ _ (fun G hG h ↦ by simpa using P.ιCoproductFrom h hG ≫= huv)
/-
**CategoryTheory.ObjectProperty.isSeparating_iff_epi** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.ObjectProperty`。
形式化陈述：isSeparating_iff_epi [forall (X : C), HasCoproduct (P.coproductFromFamily 
X)] : IsSeparating P ↔ forall X : C, Epi (P.coproductFrom X)
参数：X : C；P.coproductFromFamily X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ObjectProperty.IsSeparating.epi_coproductFrom`：∀ {C : Typ
e u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {P : CategoryTheory.ObjectProp
erty C},   P.IsSeparating →     ∀ (X : C) [inst_1 …
· 使用定理 `CategoryTheory.ObjectProperty.IsSeparating.mk_of_exists_epi`：∀ {C : Type
 u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {P : CategoryTheory.ObjectPrope
rty C},   (∀ (X : C), ∃ ι s, ∃ (_ : ∀ (i : ι), P …
· 使用定理 `CategoryTheory.ObjectProperty.FullSubcategory.property`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.ObjectProperty C}  
 (self : P.FullSubcategory), P self.obj
-/
theorem isSeparating_iff_epi
    [∀ (X : C), HasCoproduct (P.coproductFromFamily X)] :
    IsSeparating P ↔ ∀ X : C, Epi (P.coproductFrom X) :=
  ⟨fun hP X ↦ hP.epi_coproductFrom X,
    fun hP ↦ IsSeparating.mk_of_exists_epi (fun X ↦ ⟨_, P.coproductFromFamily X,
      fun i ↦ i.left.2, _, colimit.isColimit _, _, hP X⟩)⟩

section

/-- Given `P : ObjectProperty C` and `X : C`, this is the map which
sends `i : StructuredArrow P.ι X` to `i.right.obj : C`. The product
of this family is the target of the morphism `P.productTo X`. -/
/-
**CategoryTheory.ObjectProperty.productToFamily** 是 Mathlib 中的一个缩写定义，位于命名空间 `Cat
egoryTheory.ObjectProperty`。
形式化陈述：productToFamily (X : C) (i : StructuredArrow X P.ι) : C
参数：X : C；i : StructuredArrow X P.ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `P : ObjectProperty C` and `X : C`, this is the map which
sends `i : StructuredArrow P.ι X` to `i.right.obj : C`. The product
of this family is the target of the morphism `P.productTo X`.
-/
abbrev productToFamily (X : C) (i : StructuredArrow X P.ι) : C := i.right.obj

variable (X : C)

variable [HasProduct (P.productToFamily X)]

/-- Given `P : ObjectProperty C` and `X : C`, this is the product of
all the morphisms `X ⟶ Y` such that `P Y` holds. -/
/-
**CategoryTheory.ObjectProperty.productTo** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryT
heory.ObjectProperty`。
形式化陈述：productTo : X ⟶ ∏ᶜ (P.productToFamily X)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `P : ObjectProperty C` and `X : C`, this is the product of
all the morphisms `X ⟶ Y` such that `P Y` holds.
-/
noncomputable abbrev productTo : X ⟶ ∏ᶜ (P.productToFamily X) :=
  Pi.lift (fun i ↦ i.hom)

variable {X} in
/-- The projection morphisms from `∏ᶜ (P.productToFamily X)`. -/
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.Obj
ectProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The projection morphisms from `∏ᶜ (P.productToFamily X)`.
-/
noncomputable abbrev πProductTo {Y : C} (f : X ⟶ Y) (hY : P Y) :
    ∏ᶜ (P.productToFamily X) ⟶ Y := by
  exact Pi.π (P.productToFamily X) (StructuredArrow.mk (Y := ⟨Y, hY⟩) (by exact f))

end

set_option backward.isDefEq.respectTransparency false in
variable {P} in
/-
**CategoryTheory.ObjectProperty.IsCoseparating.mono_productTo** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.ObjectProperty.IsCoseparating`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {P : CategoryT
heory.ObjectProperty C},   P.IsCoseparating →     ∀ (X : C) [inst_1 : CategoryTh
eory.Limits.HasProduct (P.productToFamily X)], CategoryTheory.Mono (P.productTo 
X)
参数：X : C；P.productToFamily X；P.productTo X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.eq_whisker`：eq_whisker {f g : X ⟶ Y} (w : f = g) (h : Y ⟶
 Z) : f ≫ h = g ≫ h
-/
lemma IsCoseparating.mono_productTo (hP : P.IsCoseparating)
    (X : C) [HasProduct (P.productToFamily X)] :
    Mono (P.productTo X) where
  right_cancellation u v huv :=
    hP _ _ (fun G hG h ↦ by simpa using huv =≫ P.πProductTo h hG)
/-
**CategoryTheory.ObjectProperty.isCoseparating_iff_mono** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.ObjectProperty`。
形式化陈述：isCoseparating_iff_mono [forall (X : C), HasProduct (P.productToFamily X)]
 : IsCoseparating P ↔ forall X : C, Mono (P.productTo X)
参数：X : C；P.productToFamily X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ObjectProperty.IsCoseparating.mono_productTo`：∀ {C : Type
 u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {P : CategoryTheory.ObjectPrope
rty C},   P.IsCoseparating →     ∀ (X : C) [inst_…
· 使用定理 `CategoryTheory.ObjectProperty.IsCoseparating.mk_of_exists_mono`：∀ {C : T
ype u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {P : CategoryTheory.ObjectPr
operty C},   (∀ (X : C), ∃ ι s, ∃ (_ : ∀ (i : ι), P …
· 使用定理 `CategoryTheory.ObjectProperty.FullSubcategory.property`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.ObjectProperty C}  
 (self : P.FullSubcategory), P self.obj
-/
theorem isCoseparating_iff_mono
    [∀ (X : C), HasProduct (P.productToFamily X)] :
    IsCoseparating P ↔ ∀ X : C, Mono (P.productTo X) :=
  ⟨fun hP X ↦ hP.mono_productTo X,
    fun hP ↦ IsCoseparating.mk_of_exists_mono (fun X ↦ ⟨_, P.productToFamily X,
      fun i ↦ i.right.2, _, limit.isLimit _, _, hP X⟩)⟩

end ObjectProperty

/-- An ingredient of the proof of the Special Adjoint Functor Theorem: a complete well-powered
    category with a small coseparating set has an initial object.

    In fact, it follows from the Special Adjoint Functor Theorem that `C` is already cocomplete,
    see `hasColimits_of_hasLimits_of_isCoseparating`. -/
/-
**CategoryTheory.hasInitial_of_isCoseparating** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory`。
形式化陈述：hasInitial_of_isCoseparating [LocallySmall.{w} C] [WellPowered.{w} C] [Has
LimitsOfSize.{w, w} C] {P : ObjectProperty C} [ObjectProperty.Small.{w} P] (hP :
 P.IsCoseparating) : HasInitial C
参数：hP : P.IsCoseparating。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.hasFiniteLimits_of_hasLimitsOfSize`：hasFiniteLimit
s_of_hasLimitsOfSize [HasLimitsOfSize.{v', u'} C] : HasFiniteLimits C where out
· 使用定理 `CategoryTheory.Limits.hasProductsOfShape_of_small`：hasProductsOfShape_of
_small (β : Type w₂) [Small.{w₁} β] [HasProducts.{w₁} C] : HasProductsOfShape β 
C
· 使用定理 `CategoryTheory.Limits.hasProductsOfShape_of_hasProducts`：∀ {C : Type u} 
[inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasProducts C] 
(J : Type w),   CategoryTheory.Limits.HasProd…
· 使用定理 `CategoryTheory.Limits.instHasLimitsOfShapeOfHasLimitsOfSize`：∀ {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTh
eory.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.StructuredArrow.instSmallOfLocallySmall`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} D]   {S : D} {T : Categ…
· 使用定理 `CategoryTheory.ObjectProperty.instSmallFullSubcategoryOfSmall`：∀ {C : Ty
pe u} [inst : CategoryTheory.Category.{v, u} C] (P : CategoryTheory.ObjectProper
ty C)   [CategoryTheory.ObjectProperty.Small.{w, v,…
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.ObjectProperty.IsCoseparating.mono_productTo`：∀ {C : Type
 u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {P : CategoryTheory.ObjectPrope
rty C},   P.IsCoseparating →     ∀ (X : C) [inst_…
· 使用定理 `CategoryTheory.ObjectProperty.FullSubcategory.property`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.ObjectProperty C}  
 (self : P.FullSubcategory), P self.obj
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePullbacks_of_hasFiniteLimits`：∀ (C : 
Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFini
teLimits C],   CategoryTheory.Limits.HasFiniteWidePul…
· 使用定理 `CategoryTheory.Limits.pullback.fst_of_mono`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Cat
egoryTheory.Limits.HasPullback f…
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `CategoryTheory.Limits.hasLimitsOfShape_of_hasFiniteLimits`：∀ (C : Type u
) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFiniteLimi
ts C] (J : Type w)   [inst_2 : CategoryTheory.S…
· 使用定理 `CategoryTheory.IsSplitEpi.mk'`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {X Y : C} {f : X ⟶ Y} (se : CategoryTheory.SplitEpi f),   Cat
egoryTheory.IsSplit…
· 使用定理 `CategoryTheory.mono_comp`：∀ {C : Type u} [inst : CategoryTheory.Category
.{v, u} C] {X Y Z : C} (g : Z ⟶ Y) [CategoryTheory.Mono g] (f : Y ⟶ X)   [Catego
ryTheory.Mono …
· 使用定理 `CategoryTheory.Limits.equalizer.ι_mono`：∀ {C : Type u} {X Y : C} [inst :
 CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y}   [inst_1 : CategoryTheory.Limi
ts.HasEqualizer f g], Catego…
· 使用定理 `CategoryTheory.Subobject.eq_of_comp_arrow_eq`：eq_of_comp_arrow_eq {X Y :
 C} {P : Subobject Y} {f g : X ⟶ P} (h : f ≫ P.arrow = g ≫ P.arrow) : f = g
· 使用定理 `CategoryTheory.Limits.Pi.hom_ext`：∀ {β : Type w} {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] {f : β → C}   [inst_1 : CategoryTheory.Limits.Ha
sProduct f] {X : C} (g…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Subobject.ofLEMk_comp`：ofLEMk_comp {B A : C} {X : Subobje
ct B} {f : A ⟶ B} [Mono f] (h : X <= mk f) : ofLEMk X f h ≫ f = X.arrow
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.eq_of_epi_equalizer`：eq_of_epi_equalizer [HasEqual
izer f g] [Epi (equalizer.ι f g)] : f = g
· 使用定理 `CategoryTheory.IsSplitEpi.epi`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [hf : CategoryTheory.IsSplitEpi f],   C
ategoryTheory.Epi f
（共 33 条，此处仅展示前 30 条）

--- 原说明 ---
An ingredient of the proof of the Special Adjoint Functor Theorem: a complete we
ll-powered
    category with a small coseparating set has an initial object.

    In fact, it follows from the Special Adjoint Functor Theorem that `C` is alr
eady cocomplete,
    see `hasColimits_of_hasLimits_of_isCoseparating`.
-/
theorem hasInitial_of_isCoseparating [LocallySmall.{w} C] [WellPowered.{w} C]
    [HasLimitsOfSize.{w, w} C] {P : ObjectProperty C} [ObjectProperty.Small.{w} P]
    (hP : P.IsCoseparating) : HasInitial C := by
  have := hasFiniteLimits_of_hasLimitsOfSize C
  have := hasProductsOfShape_of_small C (Subtype P)
  have := fun A => hasProductsOfShape_of_small.{w} C (StructuredArrow A P.ι)
  let := completeLatticeOfCompleteSemilatticeInf (Subobject (piObj (Subtype.val : Subtype P → C)))
  suffices ∀ A : C, Unique (((⊥ : Subobject (piObj (Subtype.val : Subtype P → C))) : C) ⟶ A) by
    exact hasInitial_of_unique ((⊥ : Subobject (piObj (Subtype.val : Subtype P → C))) : C)
  have := hP.mono_productTo
  refine fun A => ⟨⟨?_⟩, fun f => ?_⟩
  · let s : ∏ᶜ (Subtype.val (p := P)) ⟶ ∏ᶜ P.productToFamily A :=
      Pi.lift (fun f ↦ Pi.π Subtype.val ⟨f.right.obj, f.right.property⟩)
    exact Subobject.ofLEMk _
      (pullback.fst _ _ : pullback s (P.productTo A) ⟶ _) bot_le ≫ pullback.snd _ _
  · suffices ∀ (g : Subobject.underlying.obj ⊥ ⟶ A), f = g by
      apply this
    intro g
    suffices IsSplitEpi (equalizer.ι f g) by exact eq_of_epi_equalizer
    exact IsSplitEpi.mk' ⟨Subobject.ofLEMk _ (equalizer.ι f g ≫ Subobject.arrow _) bot_le, by
      ext
      simp⟩

/-- An ingredient of the proof of the Special Adjoint Functor Theorem: a cocomplete well-copowered
    category with a small separating set has a terminal object.

    In fact, it follows from the Special Adjoint Functor Theorem that `C` is already complete, see
    `hasLimits_of_hasColimits_of_isSeparating`. -/
/-
**CategoryTheory.hasTerminal_of_isSeparating** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory`。
形式化陈述：hasTerminal_of_isSeparating [LocallySmall.{w} Cᵒᵖ] [WellPowered.{w} Cᵒᵖ] [
HasColimitsOfSize.{w, w} C] {P : ObjectProperty C} [ObjectProperty.Small.{w} P] 
(hP : P.IsSeparating) : HasTerminal C
参数：hP : P.IsSeparating。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.hasInitial_of_isCoseparating`：hasInitial_of_isCoseparatin
g [LocallySmall.{w} C] [WellPowered.{w} C] [HasLimitsOfSize.{w, w} C] {P : Objec
tProperty C} [ObjectProperty.Smal…
· 使用定理 `CategoryTheory.ObjectProperty.instSmallOppositeOp_1`：∀ {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C] (P : CategoryTheory.ObjectProperty C)   [C
ategoryTheory.ObjectProperty.Small.{w, v,…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.ObjectProperty.isCoseparating_op_iff`：isCoseparating_op_i
ff : IsCoseparating P.op ↔ IsSeparating P
· 使用定理 `CategoryTheory.Limits.hasTerminal_of_hasInitial_op`：hasTerminal_of_hasIn
itial_op [HasInitial Cᵒᵖ] : HasTerminal C

--- 原说明 ---
An ingredient of the proof of the Special Adjoint Functor Theorem: a cocomplete 
well-copowered
    category with a small separating set has a terminal object.

    In fact, it follows from the Special Adjoint Functor Theorem that `C` is alr
eady complete, see
    `hasLimits_of_hasColimits_of_isSeparating`.
-/
theorem hasTerminal_of_isSeparating [LocallySmall.{w} Cᵒᵖ] [WellPowered.{w} Cᵒᵖ]
    [HasColimitsOfSize.{w, w} C] {P : ObjectProperty C} [ObjectProperty.Small.{w} P]
    (hP : P.IsSeparating) : HasTerminal C := by
  have : HasInitial Cᵒᵖ := hasInitial_of_isCoseparating (P.isCoseparating_op_iff.2 hP)
  exact hasTerminal_of_hasInitial_op

section WellPowered

namespace Subobject

/-
**CategoryTheory.Subobject.eq_of_le_of_isDetecting** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Subobject`。
形式化陈述：eq_of_le_of_isDetecting {𝒢 : ObjectProperty C} (h𝒢 : 𝒢.IsDetecting) {X : C
} (P Q : Subobject X) (h₁ : P <= Q) (h₂ : forall (G : C) (_ : 𝒢 G), forall {f : 
G ⟶ X}, Q.Factors f -> P.Factors f) : P = Q
参数：h𝒢 : 𝒢.IsDetecting；P Q : Subobject X；h₁ : P <= Q；h₂ : forall (G : C) (_ : 𝒢 G
), forall {f : G ⟶ X}, Q.Factors f -> P.Factors f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.Subobject.factors_iff`：factors_iff {X Y : C} (P : Subobje
ct Y) (f : X ⟶ Y) : P.Factors f ↔ (representative.obj P).Factors f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Subobject.ofLE_arrow`：ofLE_arrow {B : C} {X Y : Subobject
 B} (h : X <= Y) : ofLE X Y h ≫ Y.arrow = X.arrow
· 使用定理 `CategoryTheory.Subobject.factorThru_arrow`：factorThru_arrow {X Y : C} (P
 : Subobject Y) (f : X ⟶ Y) (h : Factors P f) : P.factorThru f h ≫ P.arrow = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Subobject.instMonoOfLE`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} C] {B : C} (X Y : CategoryTheory.Subobject B) (h : X ≤ Y
),   CategoryTheory.Mono (X…
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `CategoryTheory.Subobject.le_of_comm`：le_of_comm {B : C} {X Y : Subobject
 B} (f : (X : C) ⟶ (Y : C)) (w : f ≫ Y.arrow = X.arrow) : X <= Y
-/
theorem eq_of_le_of_isDetecting {𝒢 : ObjectProperty C} (h𝒢 : 𝒢.IsDetecting) {X : C}
    (P Q : Subobject X) (h₁ : P ≤ Q)
    (h₂ : ∀ (G : C) (_ : 𝒢 G), ∀ {f : G ⟶ X}, Q.Factors f → P.Factors f) : P = Q := by
  suffices IsIso (ofLE _ _ h₁) by exact le_antisymm h₁ (le_of_comm (inv (ofLE _ _ h₁)) (by simp))
  refine h𝒢 _ fun G hG f => ?_
  have : P.Factors (f ≫ Q.arrow) := h₂ _ hG ((factors_iff _ _).2 ⟨_, rfl⟩)
  refine ⟨factorThru _ _ this, ?_, fun g (hg : g ≫ _ = f) => ?_⟩
  · simp only [← cancel_mono Q.arrow, Category.assoc, ofLE_arrow, factorThru_arrow]
  · simp only [← cancel_mono (Subobject.ofLE _ _ h₁), ← cancel_mono Q.arrow, hg, Category.assoc,
      ofLE_arrow, factorThru_arrow]
/-
**CategoryTheory.Subobject.inf_eq_of_isDetecting** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Subobject`。
形式化陈述：inf_eq_of_isDetecting [HasPullbacks C] {𝒢 : ObjectProperty C} (h𝒢 : 𝒢.IsDe
tecting) {X : C} (P Q : Subobject X) (h : forall (G : C) (_ : 𝒢 G), forall {f : 
G ⟶ X}, P.Factors f -> Q.Factors f) : P ⊓ Q = P
参数：h𝒢 : 𝒢.IsDetecting；P Q : Subobject X；h : forall (G : C) (_ : 𝒢 G), forall {f 
: G ⟶ X}, P.Factors f -> Q.Factors f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subobject.eq_of_le_of_isDetecting`：eq_of_le_of_isDetectin
g {𝒢 : ObjectProperty C} (h𝒢 : 𝒢.IsDetecting) {X : C} (P Q : Subobject X) (h₁ : 
P <= Q) (h₂ : forall (G : C) (_ : 𝒢 G)…
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.Subobject.inf_factors`：inf_factors {A B : C} {X Y : Subob
ject B} (f : A ⟶ B) : (X ⊓ Y).Factors f ↔ X.Factors f ∧ Y.Factors f
-/
theorem inf_eq_of_isDetecting [HasPullbacks C] {𝒢 : ObjectProperty C} (h𝒢 : 𝒢.IsDetecting) {X : C}
    (P Q : Subobject X) (h : ∀ (G : C) (_ : 𝒢 G), ∀ {f : G ⟶ X}, P.Factors f → Q.Factors f) :
    P ⊓ Q = P :=
  eq_of_le_of_isDetecting h𝒢 _ _ _root_.inf_le_left
    fun _ hG _ hf => (inf_factors _).2 ⟨hf, h _ hG hf⟩
/-
**CategoryTheory.Subobject.eq_of_isDetecting** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Subobject`。
形式化陈述：eq_of_isDetecting [HasPullbacks C] {𝒢 : ObjectProperty C} (h𝒢 : 𝒢.IsDetect
ing) {X : C} (P Q : Subobject X) (h : forall (G : C) (_ : 𝒢 G), forall {f : G ⟶ 
X}, P.Factors f ↔ Q.Factors f) : P = Q
参数：h𝒢 : 𝒢.IsDetecting；P Q : Subobject X；h : forall (G : C) (_ : 𝒢 G), forall {f 
: G ⟶ X}, P.Factors f ↔ Q.Factors f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Subobject.inf_eq_of_isDetecting`：inf_eq_of_isDetecting [H
asPullbacks C] {𝒢 : ObjectProperty C} (h𝒢 : 𝒢.IsDetecting) {X : C} (P Q : Subobj
ect X) (h : forall (G : C) (_ : 𝒢 G)…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α), a ⊓ b = b 
⊓ a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem eq_of_isDetecting [HasPullbacks C] {𝒢 : ObjectProperty C} (h𝒢 : 𝒢.IsDetecting) {X : C}
    (P Q : Subobject X) (h : ∀ (G : C) (_ : 𝒢 G),
      ∀ {f : G ⟶ X}, P.Factors f ↔ Q.Factors f) : P = Q :=
  calc
    P = P ⊓ Q := Eq.symm <| inf_eq_of_isDetecting h𝒢 _ _ fun G hG _ hf => (h G hG).1 hf
    _ = Q ⊓ P := inf_comm ..
    _ = Q := inf_eq_of_isDetecting h𝒢 _ _ fun G hG _ hf => (h G hG).2 hf

end Subobject

/-- A category with pullbacks and a small detecting set is well-powered. -/
/-
**CategoryTheory.wellPowered_of_isDetecting** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory`。
形式化陈述：wellPowered_of_isDetecting [HasPullbacks C] {𝒢 : ObjectProperty C} [Object
Property.Small.{w} 𝒢] [LocallySmall.{w} C] (h𝒢 : 𝒢.IsDetecting) : WellPowered.{w
} C where subobject_small X
参数：h𝒢 : 𝒢.IsDetecting。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `small_of_injective`：small_of_injective {α : Type v} {β : Type w} [Small.
{u} β] {f : α -> β} (hf : Function.Injective f) : Small.{u} α
· 使用定理 `CategoryTheory.instSmallHomOfLocallySmall`：∀ (C : Type u) [inst : Catego
ryTheory.Category.{v, u} C] [CategoryTheory.LocallySmall.{w, v, u} C] (X Y : C),
   Small.{w, v} (X ⟶ Y)
· 使用定理 `CategoryTheory.Subobject.eq_of_isDetecting`：eq_of_isDetecting [HasPullba
cks C] {𝒢 : ObjectProperty C} (h𝒢 : 𝒢.IsDetecting) {X : C} (P Q : Subobject X) (
h : forall (G : C) (_ : 𝒢 G), fo…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c

--- 原说明 ---
A category with pullbacks and a small detecting set is well-powered.
-/
theorem wellPowered_of_isDetecting [HasPullbacks C] {𝒢 : ObjectProperty C}
    [ObjectProperty.Small.{w} 𝒢] [LocallySmall.{w} C]
    (h𝒢 : 𝒢.IsDetecting) : WellPowered.{w} C where
  subobject_small X := small_of_injective
    (f := fun P : Subobject X => { f : Σ G : Subtype 𝒢, G.1 ⟶ X | P.Factors f.2 })
      fun P Q h => Subobject.eq_of_isDetecting h𝒢 _ _
        (by simpa [Set.ext_iff, Sigma.forall] using h)

end WellPowered

namespace StructuredArrow

variable (S : D) (T : C ⥤ D)

/-
**CategoryTheory.StructuredArrow.isCoseparating_inverseImage_proj** 是 Mathlib 中的
一个定理，位于命名空间 `CategoryTheory.StructuredArrow`。
形式化陈述：isCoseparating_inverseImage_proj {P : ObjectProperty C} (hP : P.IsCosepara
ting) : (P.inverseImage (proj S T)).IsCoseparating
参数：hP : P.IsCoseparating。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.StructuredArrow.ext`：ext {A B : StructuredArrow S T} (f g
 : A ⟶ B) : f.right = g.right -> f = g
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem isCoseparating_inverseImage_proj {P : ObjectProperty C} (hP : P.IsCoseparating) :
    (P.inverseImage (proj S T)).IsCoseparating := by
  refine fun X Y f g hfg => ext _ _ (hP _ _ fun G hG h => ?_)
  exact congr_arg CommaMorphism.right (hfg (mk (Y.hom ≫ T.map h)) hG (homMk h rfl))

end StructuredArrow

namespace CostructuredArrow

variable (S : C ⥤ D) (T : D)

/-
**CategoryTheory.CostructuredArrow.isSeparating_inverseImage_proj** 是 Mathlib 中的
一个定理，位于命名空间 `CategoryTheory.CostructuredArrow`。
形式化陈述：isSeparating_inverseImage_proj {P : ObjectProperty C} (hP : P.IsSeparating
) : (P.inverseImage (proj S T)).IsSeparating
参数：hP : P.IsSeparating。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CostructuredArrow.ext`：ext {A B : CostructuredArrow S T} 
(f g : A ⟶ B) (h : f.left = g.left) : f = g
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem isSeparating_inverseImage_proj {P : ObjectProperty C} (hP : P.IsSeparating) :
    (P.inverseImage (proj S T)).IsSeparating := by
  refine fun X Y f g hfg => ext _ _ (hP _ _ fun G hG h => ?_)
  exact congr_arg CommaMorphism.left (hfg (mk (S.map h ≫ X.hom)) hG (homMk h rfl))

end CostructuredArrow

/-- We say that `G` is a separator if the functor `C(G, -)` is faithful. -/
/-
**CategoryTheory.IsSeparator** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：IsSeparator (G : C) : Prop
参数：G : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say that `G` is a separator if the functor `C(G, -)` is faithful.
-/
def IsSeparator (G : C) : Prop :=
  ObjectProperty.IsSeparating (.singleton G)

/-- We say that `G` is a coseparator if the functor `C(-, G)` is faithful. -/
/-
**CategoryTheory.IsCoseparator** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：IsCoseparator (G : C) : Prop
参数：G : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say that `G` is a coseparator if the functor `C(-, G)` is faithful.
-/
def IsCoseparator (G : C) : Prop :=
  ObjectProperty.IsCoseparating (.singleton G)

/-- We say that `G` is a detector if the functor `C(G, -)` reflects isomorphisms. -/
/-
**CategoryTheory.IsDetector** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：IsDetector (G : C) : Prop
参数：G : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say that `G` is a detector if the functor `C(G, -)` reflects isomorphisms.
-/
def IsDetector (G : C) : Prop :=
  ObjectProperty.IsDetecting (.singleton G)

/-- We say that `G` is a codetector if the functor `C(-, G)` reflects isomorphisms. -/
/-
**CategoryTheory.IsCodetector** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：IsCodetector (G : C) : Prop
参数：G : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say that `G` is a codetector if the functor `C(-, G)` reflects isomorphisms.
-/
def IsCodetector (G : C) : Prop :=
  ObjectProperty.IsCodetecting (.singleton G)

section Equivalence

/-
**CategoryTheory.IsSeparator.of_equivalence** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.IsSeparator`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {G : C}, CategoryTheory.IsSepara
tor G → ∀ (α : C ≌ D), CategoryTheory.IsSeparator (α.functor.obj G)
参数：α : C ≌ D；α.functor.obj G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ObjectProperty.strictMap_singleton`：strictMap_singleton (
X : C) (F : C ⥤ D) : (singleton X).strictMap F = singleton (F.obj X)
· 使用定理 `CategoryTheory.ObjectProperty.IsSeparating.of_equivalence`：∀ {C : Type u
₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {P : CategoryTheory.ObjectPropert
y C},   P.IsSeparating →     ∀ {D : Type u_1} […
-/
theorem IsSeparator.of_equivalence {G : C} (h : IsSeparator G) (α : C ≌ D) :
    IsSeparator (α.functor.obj G) := by
  simpa using! ObjectProperty.IsSeparating.of_equivalence h α
/-
**CategoryTheory.IsCoseparator.of_equivalence** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.IsCoseparator`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {G : C}, CategoryTheory.IsCosepa
rator G → ∀ (α : C ≌ D), CategoryTheory.IsCoseparator (α.functor.obj G)
参数：α : C ≌ D；α.functor.obj G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ObjectProperty.strictMap_singleton`：strictMap_singleton (
X : C) (F : C ⥤ D) : (singleton X).strictMap F = singleton (F.obj X)
· 使用定理 `CategoryTheory.ObjectProperty.IsCoseparating.of_equivalence`：∀ {C : Type
 u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {P : CategoryTheory.ObjectPrope
rty C},   P.IsCoseparating →     ∀ {D : Type u_1}…
-/
theorem IsCoseparator.of_equivalence {G : C} (h : IsCoseparator G) (α : C ≌ D) :
    IsCoseparator (α.functor.obj G) := by
  simpa using! ObjectProperty.IsCoseparating.of_equivalence h α

end Equivalence

section Dual

open ObjectProperty

/-
**CategoryTheory.isSeparator_op_iff** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：isSeparator_op_iff (G : C) : IsSeparator (op G) ↔ IsCoseparator G
参数：G : C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsSeparator.eq_1`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] (G : C),   CategoryTheory.IsSeparator G = (CategoryTheory.O
bjectProperty.singlet…
· 使用定理 `CategoryTheory.IsCoseparator.eq_1`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] (G : C),   CategoryTheory.IsCoseparator G = (CategoryTheo
ry.ObjectProperty.singl…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.ObjectProperty.isSeparating_op_iff`：isSeparating_op_iff :
 IsSeparating P.op ↔ IsCoseparating P
· 使用引理 `CategoryTheory.ObjectProperty.op_singleton`：op_singleton (X : C) : (sing
leton X).op = singleton (op X)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isSeparator_op_iff (G : C) : IsSeparator (op G) ↔ IsCoseparator G := by
  rw [IsSeparator, IsCoseparator, ← isSeparating_op_iff, op_singleton]
/-
**CategoryTheory.isCoseparator_op_iff** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`
。
形式化陈述：isCoseparator_op_iff (G : C) : IsCoseparator (op G) ↔ IsSeparator G
参数：G : C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsSeparator.eq_1`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] (G : C),   CategoryTheory.IsSeparator G = (CategoryTheory.O
bjectProperty.singlet…
· 使用定理 `CategoryTheory.IsCoseparator.eq_1`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] (G : C),   CategoryTheory.IsCoseparator G = (CategoryTheo
ry.ObjectProperty.singl…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.ObjectProperty.isCoseparating_op_iff`：isCoseparating_op_i
ff : IsCoseparating P.op ↔ IsSeparating P
· 使用引理 `CategoryTheory.ObjectProperty.op_singleton`：op_singleton (X : C) : (sing
leton X).op = singleton (op X)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isCoseparator_op_iff (G : C) : IsCoseparator (op G) ↔ IsSeparator G := by
  rw [IsSeparator, IsCoseparator, ← isCoseparating_op_iff, op_singleton]
/-
**CategoryTheory.isCoseparator_unop_iff** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y`。
形式化陈述：isCoseparator_unop_iff (G : Cᵒᵖ) : IsCoseparator (unop G) ↔ IsSeparator G
参数：G : Cᵒᵖ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsSeparator.eq_1`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] (G : C),   CategoryTheory.IsSeparator G = (CategoryTheory.O
bjectProperty.singlet…
· 使用定理 `CategoryTheory.IsCoseparator.eq_1`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] (G : C),   CategoryTheory.IsCoseparator G = (CategoryTheo
ry.ObjectProperty.singl…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.ObjectProperty.isCoseparating_unop_iff`：isCoseparating_un
op_iff (P : ObjectProperty Cᵒᵖ) : IsCoseparating P.unop ↔ IsSeparating P
· 使用引理 `CategoryTheory.ObjectProperty.unop_singleton`：unop_singleton (X : Cᵒᵖ) :
 (singleton X).unop = singleton X.unop
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isCoseparator_unop_iff (G : Cᵒᵖ) : IsCoseparator (unop G) ↔ IsSeparator G := by
  rw [IsSeparator, IsCoseparator, ← isCoseparating_unop_iff, unop_singleton]
/-
**CategoryTheory.isSeparator_unop_iff** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`
。
形式化陈述：isSeparator_unop_iff (G : Cᵒᵖ) : IsSeparator (unop G) ↔ IsCoseparator G
参数：G : Cᵒᵖ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsSeparator.eq_1`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] (G : C),   CategoryTheory.IsSeparator G = (CategoryTheory.O
bjectProperty.singlet…
· 使用定理 `CategoryTheory.IsCoseparator.eq_1`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] (G : C),   CategoryTheory.IsCoseparator G = (CategoryTheo
ry.ObjectProperty.singl…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.ObjectProperty.isSeparating_unop_iff`：isSeparating_unop_i
ff (P : ObjectProperty Cᵒᵖ) : IsSeparating P.unop ↔ IsCoseparating P
· 使用引理 `CategoryTheory.ObjectProperty.unop_singleton`：unop_singleton (X : Cᵒᵖ) :
 (singleton X).unop = singleton X.unop
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isSeparator_unop_iff (G : Cᵒᵖ) : IsSeparator (unop G) ↔ IsCoseparator G := by
  rw [IsSeparator, IsCoseparator, ← isSeparating_unop_iff, unop_singleton]
/-
**CategoryTheory.isDetector_op_iff** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：isDetector_op_iff (G : C) : IsDetector (op G) ↔ IsCodetector G
参数：G : C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsDetector.eq_1`：∀ {C : Type u₁} [inst : CategoryTheory.C
ategory.{v₁, u₁} C] (G : C),   CategoryTheory.IsDetector G = (CategoryTheory.Obj
ectProperty.singleto…
· 使用定理 `CategoryTheory.IsCodetector.eq_1`：∀ {C : Type u₁} [inst : CategoryTheory
.Category.{v₁, u₁} C] (G : C),   CategoryTheory.IsCodetector G = (CategoryTheory
.ObjectProperty.single…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.ObjectProperty.isDetecting_op_iff`：isDetecting_op_iff : I
sDetecting P.op ↔ IsCodetecting P
· 使用引理 `CategoryTheory.ObjectProperty.op_singleton`：op_singleton (X : C) : (sing
leton X).op = singleton (op X)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isDetector_op_iff (G : C) : IsDetector (op G) ↔ IsCodetector G := by
  rw [IsDetector, IsCodetector, ← isDetecting_op_iff, op_singleton]
/-
**CategoryTheory.isCodetector_op_iff** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：isCodetector_op_iff (G : C) : IsCodetector (op G) ↔ IsDetector G
参数：G : C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsDetector.eq_1`：∀ {C : Type u₁} [inst : CategoryTheory.C
ategory.{v₁, u₁} C] (G : C),   CategoryTheory.IsDetector G = (CategoryTheory.Obj
ectProperty.singleto…
· 使用定理 `CategoryTheory.IsCodetector.eq_1`：∀ {C : Type u₁} [inst : CategoryTheory
.Category.{v₁, u₁} C] (G : C),   CategoryTheory.IsCodetector G = (CategoryTheory
.ObjectProperty.single…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.ObjectProperty.isCodetecting_op_iff`：isCodetecting_op_iff
 : IsCodetecting P.op ↔ IsDetecting P
· 使用引理 `CategoryTheory.ObjectProperty.op_singleton`：op_singleton (X : C) : (sing
leton X).op = singleton (op X)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isCodetector_op_iff (G : C) : IsCodetector (op G) ↔ IsDetector G := by
  rw [IsDetector, IsCodetector, ← isCodetecting_op_iff, op_singleton]
/-
**CategoryTheory.isCodetector_unop_iff** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
`。
形式化陈述：isCodetector_unop_iff (G : Cᵒᵖ) : IsCodetector (unop G) ↔ IsDetector G
参数：G : Cᵒᵖ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsDetector.eq_1`：∀ {C : Type u₁} [inst : CategoryTheory.C
ategory.{v₁, u₁} C] (G : C),   CategoryTheory.IsDetector G = (CategoryTheory.Obj
ectProperty.singleto…
· 使用定理 `CategoryTheory.IsCodetector.eq_1`：∀ {C : Type u₁} [inst : CategoryTheory
.Category.{v₁, u₁} C] (G : C),   CategoryTheory.IsCodetector G = (CategoryTheory
.ObjectProperty.single…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.ObjectProperty.isCodetecting_unop_iff`：isCodetecting_unop
_iff (P : ObjectProperty Cᵒᵖ) : IsCodetecting P.unop ↔ IsDetecting P
· 使用引理 `CategoryTheory.ObjectProperty.unop_singleton`：unop_singleton (X : Cᵒᵖ) :
 (singleton X).unop = singleton X.unop
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isCodetector_unop_iff (G : Cᵒᵖ) : IsCodetector (unop G) ↔ IsDetector G := by
  rw [IsDetector, IsCodetector, ← isCodetecting_unop_iff, unop_singleton]
/-
**CategoryTheory.isDetector_unop_iff** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：isDetector_unop_iff (G : Cᵒᵖ) : IsDetector (unop G) ↔ IsCodetector G
参数：G : Cᵒᵖ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsDetector.eq_1`：∀ {C : Type u₁} [inst : CategoryTheory.C
ategory.{v₁, u₁} C] (G : C),   CategoryTheory.IsDetector G = (CategoryTheory.Obj
ectProperty.singleto…
· 使用定理 `CategoryTheory.IsCodetector.eq_1`：∀ {C : Type u₁} [inst : CategoryTheory
.Category.{v₁, u₁} C] (G : C),   CategoryTheory.IsCodetector G = (CategoryTheory
.ObjectProperty.single…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.ObjectProperty.isDetecting_unop_iff`：isDetecting_unop_iff
 (P : ObjectProperty Cᵒᵖ) : IsDetecting P.unop ↔ IsCodetecting P
· 使用引理 `CategoryTheory.ObjectProperty.unop_singleton`：unop_singleton (X : Cᵒᵖ) :
 (singleton X).unop = singleton X.unop
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isDetector_unop_iff (G : Cᵒᵖ) : IsDetector (unop G) ↔ IsCodetector G := by
  rw [IsDetector, IsCodetector, ← isDetecting_unop_iff, unop_singleton]

end Dual

/-
**CategoryTheory.IsDetector.isSeparator** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.IsDetector`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [CategoryTheor
y.Limits.HasEqualizers C] {G : C},   CategoryTheory.IsDetector G → CategoryTheor
y.IsSeparator G
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ObjectProperty.IsDetecting.isSeparating`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {P : CategoryTheory.ObjectProperty C
}   [CategoryTheory.Limits.HasEqualizers C],…
-/
theorem IsDetector.isSeparator [HasEqualizers C] {G : C} : IsDetector G → IsSeparator G :=
  ObjectProperty.IsDetecting.isSeparating
/-
**CategoryTheory.IsCodetector.isCoseparator** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.IsCodetector`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [CategoryTheor
y.Limits.HasCoequalizers C] {G : C},   CategoryTheory.IsCodetector G → CategoryT
heory.IsCoseparator G
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ObjectProperty.IsCodetecting.isCoseparating`：∀ {C : Type 
u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {P : CategoryTheory.ObjectProper
ty C}   [CategoryTheory.Limits.HasCoequalizers C…
-/
theorem IsCodetector.isCoseparator [HasCoequalizers C] {G : C} : IsCodetector G → IsCoseparator G :=
  ObjectProperty.IsCodetecting.isCoseparating
/-
**CategoryTheory.IsSeparator.isDetector** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.IsSeparator`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [CategoryTheor
y.Balanced C] {G : C},   CategoryTheory.IsSeparator G → CategoryTheory.IsDetecto
r G
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ObjectProperty.IsSeparating.isDetecting`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {P : CategoryTheory.ObjectProperty C
}   [CategoryTheory.Balanced C], P.IsSeparat…
-/
theorem IsSeparator.isDetector [Balanced C] {G : C} : IsSeparator G → IsDetector G :=
  ObjectProperty.IsSeparating.isDetecting
/-
**CategoryTheory.IsCoseparator.isCodetector** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.IsCoseparator`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [CategoryTheor
y.Balanced C] {G : C},   CategoryTheory.IsCoseparator G → CategoryTheory.IsCodet
ector G
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ObjectProperty.IsCoseparating.isCodetecting`：∀ {C : Type 
u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {P : CategoryTheory.ObjectProper
ty C}   [CategoryTheory.Balanced C], P.IsCosepar…
-/
theorem IsCoseparator.isCodetector [Balanced C] {G : C} : IsCoseparator G → IsCodetector G :=
  ObjectProperty.IsCoseparating.isCodetecting
/-
**CategoryTheory.isSeparator_def** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：isSeparator_def (G : C) : IsSeparator G ↔ forall ⦃X Y : C⦄ (f g : X ⟶ Y), 
(forall h : G ⟶ X, h ≫ f = h ≫ g) -> f = g
参数：G : C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `CategoryTheory.ObjectProperty.singleton_iff`：singleton_iff (X Y : C) : s
ingleton X Y ↔ X = Y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem isSeparator_def (G : C) :
    IsSeparator G ↔ ∀ ⦃X Y : C⦄ (f g : X ⟶ Y), (∀ h : G ⟶ X, h ≫ f = h ≫ g) → f = g :=
  ⟨fun hG X Y f g hfg =>
    hG _ _ fun H hH h => by
      obtain rfl := (ObjectProperty.singleton_iff _ _).1 hH
      exact hfg h,
    fun hG _ _ _ _ hfg => hG _ _ fun _ => hfg _ (by simp) _⟩
/-
**CategoryTheory.IsSeparator.def** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.IsSep
arator`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {G : C},   Cat
egoryTheory.IsSeparator G →     ∀ ⦃X Y : C⦄ (f g : X ⟶ Y),       (∀ (h : G ⟶ X),
 CategoryTheory.CategoryStruct.comp h f = CategoryTheory.CategoryStruct.comp h g
) → f = g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.isSeparator_def`：isSeparator_def (G : C) : IsSeparator G 
↔ forall ⦃X Y : C⦄ (f g : X ⟶ Y), (forall h : G ⟶ X, h ≫ f = h ≫ g) -> f = g
-/
theorem IsSeparator.def {G : C} :
    IsSeparator G → ∀ ⦃X Y : C⦄ (f g : X ⟶ Y), (∀ h : G ⟶ X, h ≫ f = h ≫ g) → f = g :=
  (isSeparator_def _).1
/-
**CategoryTheory.isCoseparator_def** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：isCoseparator_def (G : C) : IsCoseparator G ↔ forall ⦃X Y : C⦄ (f g : X ⟶ 
Y), (forall h : Y ⟶ G, f ≫ h = g ≫ h) -> f = g
参数：G : C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `CategoryTheory.ObjectProperty.singleton_iff`：singleton_iff (X Y : C) : s
ingleton X Y ↔ X = Y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem isCoseparator_def (G : C) :
    IsCoseparator G ↔ ∀ ⦃X Y : C⦄ (f g : X ⟶ Y), (∀ h : Y ⟶ G, f ≫ h = g ≫ h) → f = g :=
  ⟨fun hG X Y f g hfg =>
    hG _ _ fun H hH h => by
      obtain rfl := (ObjectProperty.singleton_iff _ _).1 hH
      exact hfg h,
    fun hG _ _ _ _ hfg => hG _ _ fun _ => hfg _ (by simp) _⟩
/-
**CategoryTheory.IsCoseparator.def** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.IsC
oseparator`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {G : C},   Cat
egoryTheory.IsCoseparator G →     ∀ ⦃X Y : C⦄ (f g : X ⟶ Y),       (∀ (h : Y ⟶ G
), CategoryTheory.CategoryStruct.comp f h = CategoryTheory.CategoryStruct.comp g
 h) → f = g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.isCoseparator_def`：isCoseparator_def (G : C) : IsCosepara
tor G ↔ forall ⦃X Y : C⦄ (f g : X ⟶ Y), (forall h : Y ⟶ G, f ≫ h = g ≫ h) -> f =
 g
-/
theorem IsCoseparator.def {G : C} :
    IsCoseparator G → ∀ ⦃X Y : C⦄ (f g : X ⟶ Y), (∀ h : Y ⟶ G, f ≫ h = g ≫ h) → f = g :=
  (isCoseparator_def _).1
/-
**CategoryTheory.isDetector_def** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：isDetector_def (G : C) : IsDetector G ↔ forall ⦃X Y : C⦄ (f : X ⟶ Y), (for
all h : G ⟶ Y, exists! h', h' ≫ f = h) -> IsIso f
参数：G : C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `CategoryTheory.ObjectProperty.singleton_iff`：singleton_iff (X Y : C) : s
ingleton X Y ↔ X = Y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem isDetector_def (G : C) :
    IsDetector G ↔ ∀ ⦃X Y : C⦄ (f : X ⟶ Y), (∀ h : G ⟶ Y, ∃! h', h' ≫ f = h) → IsIso f :=
  ⟨fun hG X Y f hf =>
    hG _ fun H hH h => by
      obtain rfl := (ObjectProperty.singleton_iff _ _).1 hH
      exact hf h,
    fun hG _ _ _ hf => hG _ fun _ => hf _ (by simp) _⟩
/-
**CategoryTheory.IsDetector.def** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.IsDete
ctor`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {G : C},   Cat
egoryTheory.IsDetector G →     ∀ ⦃X Y : C⦄ (f : X ⟶ Y),       (∀ (h : G ⟶ Y), ∃!
 h', CategoryTheory.CategoryStruct.comp h' f = h) → CategoryTheory.IsIso f
该定理/引理表达了一个蕴含关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.isDetector_def`：isDetector_def (G : C) : IsDetector G ↔ f
orall ⦃X Y : C⦄ (f : X ⟶ Y), (forall h : G ⟶ Y, exists! h', h' ≫ f = h) -> IsIso
 f
-/
theorem IsDetector.def {G : C} :
    IsDetector G → ∀ ⦃X Y : C⦄ (f : X ⟶ Y), (∀ h : G ⟶ Y, ∃! h', h' ≫ f = h) → IsIso f :=
  (isDetector_def _).1
/-
**CategoryTheory.isCodetector_def** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：isCodetector_def (G : C) : IsCodetector G ↔ forall ⦃X Y : C⦄ (f : X ⟶ Y), 
(forall h : X ⟶ G, exists! h', f ≫ h' = h) -> IsIso f
参数：G : C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `CategoryTheory.ObjectProperty.singleton_iff`：singleton_iff (X Y : C) : s
ingleton X Y ↔ X = Y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem isCodetector_def (G : C) :
    IsCodetector G ↔ ∀ ⦃X Y : C⦄ (f : X ⟶ Y), (∀ h : X ⟶ G, ∃! h', f ≫ h' = h) → IsIso f :=
  ⟨fun hG X Y f hf =>
    hG _ fun H hH h => by
      obtain rfl := (ObjectProperty.singleton_iff _ _).1 hH
      exact hf h,
    fun hG _ _ _ hf => hG _ fun _ => hf _ (by simp) _⟩
/-
**CategoryTheory.IsCodetector.def** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.IsCo
detector`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {G : C},   Cat
egoryTheory.IsCodetector G →     ∀ ⦃X Y : C⦄ (f : X ⟶ Y),       (∀ (h : X ⟶ G), 
∃! h', CategoryTheory.CategoryStruct.comp f h' = h) → CategoryTheory.IsIso f
该定理/引理表达了一个蕴含关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.isCodetector_def`：isCodetector_def (G : C) : IsCodetector
 G ↔ forall ⦃X Y : C⦄ (f : X ⟶ Y), (forall h : X ⟶ G, exists! h', f ≫ h' = h) ->
 IsIso f
-/
theorem IsCodetector.def {G : C} :
    IsCodetector G → ∀ ⦃X Y : C⦄ (f : X ⟶ Y), (∀ h : X ⟶ G, ∃! h', f ≫ h' = h) → IsIso f :=
  (isCodetector_def _).1

open ConcreteCategory
/-
**CategoryTheory.isSeparator_iff_faithful_coyoneda_obj** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory`。
形式化陈述：isSeparator_iff_faithful_coyoneda_obj (G : C) : IsSeparator G ↔ (coyoneda.
obj (op G)).Faithful
参数：G : C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsSeparator.def`：∀ {C : Type u₁} [inst : CategoryTheory.C
ategory.{v₁, u₁} C] {G : C},   CategoryTheory.IsSeparator G →     ∀ ⦃X Y : C⦄ (f
 g : X ⟶ Y),       (…
· 使用定理 `CategoryTheory.ConcreteCategory.congr_hom`：congr_hom {X Y : C} {f g : X 
⟶ Y} (h : f = g) (x : ToType X) : f x = g x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.isSeparator_def`：isSeparator_def (G : C) : IsSeparator G 
↔ forall ⦃X Y : C⦄ (f g : X ⟶ Y), (forall h : G ⟶ X, h ≫ f = h ≫ g) -> f = g
· 使用定理 `CategoryTheory.Functor.map_injective`：map_injective (F : C ⥤ D) [Faithfu
l F] : Function.Injective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
· 使用定理 `CategoryTheory.ConcreteCategory.ext`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y
 : C) → FunLike (FC X Y) …
· 使用定理 `TypeCat.Fun.ext`：∀ {X : Type u_1} {Y : Type u_2} {x y : TypeCat.Fun X Y}
, x.toFun = y.toFun → x = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem isSeparator_iff_faithful_coyoneda_obj (G : C) :
    IsSeparator G ↔ (coyoneda.obj (op G)).Faithful :=
  ⟨fun hG => ⟨fun hfg => hG.def _ _ (congr_hom hfg)⟩, fun _ =>
    (isSeparator_def _).2 fun _ _ _ _ hfg => (coyoneda.obj (op G)).map_injective
      (by ext; apply hfg)⟩
/-
**CategoryTheory.isCoseparator_iff_faithful_yoneda_obj** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory`。
形式化陈述：isCoseparator_iff_faithful_yoneda_obj (G : C) : IsCoseparator G ↔ (yoneda.
obj G).Faithful
参数：G : C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quiver.Hom.unop_inj`：Quiver.Hom.unop_inj {X Y : Cᵒᵖ} : Function.Injectiv
e (Quiver.Hom.unop : (X ⟶ Y) -> (Opposite.unop Y ⟶ Opposite.unop X))
· 使用定理 `CategoryTheory.IsCoseparator.def`：∀ {C : Type u₁} [inst : CategoryTheory
.Category.{v₁, u₁} C] {G : C},   CategoryTheory.IsCoseparator G →     ∀ ⦃X Y : C
⦄ (f g : X ⟶ Y),      …
· 使用定理 `CategoryTheory.ConcreteCategory.congr_hom`：congr_hom {X Y : C} {f g : X 
⟶ Y} (h : f = g) (x : ToType X) : f x = g x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.isCoseparator_def`：isCoseparator_def (G : C) : IsCosepara
tor G ↔ forall ⦃X Y : C⦄ (f g : X ⟶ Y), (forall h : Y ⟶ G, f ≫ h = g ≫ h) -> f =
 g
· 使用定理 `Quiver.Hom.op_inj`：Quiver.Hom.op_inj {X Y : C} : Function.Injective (Qui
ver.Hom.op : (X ⟶ Y) -> (Opposite.op Y ⟶ Opposite.op X))
· 使用定理 `CategoryTheory.Functor.map_injective`：map_injective (F : C ⥤ D) [Faithfu
l F] : Function.Injective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
· 使用定理 `CategoryTheory.ConcreteCategory.ext`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y
 : C) → FunLike (FC X Y) …
· 使用定理 `TypeCat.Fun.ext`：∀ {X : Type u_1} {Y : Type u_2} {x y : TypeCat.Fun X Y}
, x.toFun = y.toFun → x = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem isCoseparator_iff_faithful_yoneda_obj (G : C) : IsCoseparator G ↔ (yoneda.obj G).Faithful :=
  ⟨fun hG => ⟨fun hfg => Quiver.Hom.unop_inj (hG.def _ _ (congr_hom hfg))⟩, fun _ =>
    (isCoseparator_def _).2 fun _ _ _ _ hfg =>
      Quiver.Hom.op_inj <| (yoneda.obj G).map_injective (by ext; apply hfg)⟩

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.isSeparator_iff_epi** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：isSeparator_iff_epi (G : C) [forall A : C, HasCoproduct fun _ : G ⟶ A => G
] : IsSeparator G ↔ forall A : C, Epi (Sigma.desc fun f : G ⟶ A => f)
参数：G : C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.isSeparator_def`：isSeparator_def (G : C) : IsSeparator G 
↔ forall ⦃X Y : C⦄ (f g : X ⟶ Y), (forall h : G ⟶ X, h ≫ f = h ≫ g) -> f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc_assoc`：∀ {J : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{
v, u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.whisker_eq`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {X Y Z : C} {f g : Y ⟶ X} (h : Z ⟶ Y),   f = g → CategoryTheory.Cate
goryStruct.comp…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.Limits.colimit.hom_ext`：∀ {J : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u}
 C]   {F : CategoryTheory.F…
-/
theorem isSeparator_iff_epi (G : C) [∀ A : C, HasCoproduct fun _ : G ⟶ A => G] :
    IsSeparator G ↔ ∀ A : C, Epi (Sigma.desc fun f : G ⟶ A => f) := by
  rw [isSeparator_def]
  refine ⟨fun h A => ⟨fun u v huv => h _ _ fun i => ?_⟩, fun h X Y f g hh => ?_⟩
  · simpa using Sigma.ι _ i ≫= huv
  · have := h X
    refine (cancel_epi (Sigma.desc fun f : G ⟶ X => f)).1 (colimit.hom_ext fun j => ?_)
    simpa using hh j.as

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.isCoseparator_iff_mono** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y`。
形式化陈述：isCoseparator_iff_mono (G : C) [forall A : C, HasProduct fun _ : A ⟶ G => 
G] : IsCoseparator G ↔ forall A : C, Mono (Pi.lift fun f : A ⟶ G => f)
参数：G : C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.isCoseparator_def`：isCoseparator_def (G : C) : IsCosepara
tor G ↔ forall ⦃X Y : C⦄ (f g : X ⟶ Y), (forall h : Y ⟶ G, f ≫ h = g ≫ h) -> f =
 g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.eq_whisker`：eq_whisker {f g : X ⟶ Y} (w : f = g) (h : Y ⟶
 Z) : f ≫ h = g ≫ h
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.Limits.limit.hom_ext`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C
]   {F : CategoryTheory.F…
-/
theorem isCoseparator_iff_mono (G : C) [∀ A : C, HasProduct fun _ : A ⟶ G => G] :
    IsCoseparator G ↔ ∀ A : C, Mono (Pi.lift fun f : A ⟶ G => f) := by
  rw [isCoseparator_def]
  refine ⟨fun h A => ⟨fun u v huv => h _ _ fun i => ?_⟩, fun h X Y f g hh => ?_⟩
  · simpa using huv =≫ Pi.π _ i
  · have := h Y
    refine (cancel_mono (Pi.lift fun f : Y ⟶ G => f)).1 (limit.hom_ext fun j => ?_)
    simpa using hh j.as

section ZeroMorphisms

variable [HasZeroMorphisms C]

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.isSeparator_of_isColimit_cofan** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory`。
形式化陈述：isSeparator_of_isColimit_cofan {β : Type w} {f : β -> C} (hf : ObjectPrope
rty.IsSeparating (.ofObj f)) {c : Cofan f} (hc : IsColimit c) : IsSeparator c.pt
参数：hf : ObjectProperty.IsSeparating (.ofObj f)；hc : IsColimit c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.isSeparator_def`：isSeparator_def (G : C) : IsSeparator G 
↔ forall ⦃X Y : C⦄ (f g : X ⟶ Y), (forall h : G ⟶ X, h ≫ f = h ≫ g) -> f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.Cofan.IsColimit.inj_desc_assoc`：∀ {β : Type w} {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C] {X : β → C} {c : CategoryThe
ory.Limits.Cofan X}   (d : CategoryTheory.…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Pi.single_eq_same`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) →
 Zero (M i)] [inst_1 : DecidableEq ι] (i : ι) (x : M i),   Pi.single i x i = x
· 使用定理 `CategoryTheory.whisker_eq`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {X Y Z : C} {f g : Y ⟶ X} (h : Z ⟶ Y),   f = g → CategoryTheory.Cate
goryStruct.comp…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma isSeparator_of_isColimit_cofan {β : Type w} {f : β → C}
    (hf : ObjectProperty.IsSeparating (.ofObj f)) {c : Cofan f} (hc : IsColimit c) :
    IsSeparator c.pt := by
  rw [isSeparator_def]
  refine fun _ _ _ _ huv ↦ hf _ _ (fun _ h g ↦ ?_)
  obtain ⟨b⟩ := h
  classical simpa using c.inj b ≫= huv (hc.desc (Cofan.mk _ (Pi.single b g)))
/-
**CategoryTheory.isSeparator_iff_of_isColimit_cofan** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory`。
形式化陈述：isSeparator_iff_of_isColimit_cofan {β : Type w} {f : β -> C} {c : Cofan f}
 (hc : IsColimit c) : IsSeparator c.pt ↔ ObjectProperty.IsSeparating (.ofObj f)
参数：hc : IsColimit c。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsSeparator.def`：∀ {C : Type u₁} [inst : CategoryTheory.C
ategory.{v₁, u₁} C] {G : C},   CategoryTheory.IsSeparator G →     ∀ ⦃X Y : C⦄ (f
 g : X ⟶ Y),       (…
· 使用定理 `CategoryTheory.Limits.IsColimit.hom_ext`：∀ {J : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃
, u₃} C]   {F : CategoryTheor…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `CategoryTheory.isSeparator_of_isColimit_cofan`：isSeparator_of_isColimit_
cofan {β : Type w} {f : β -> C} (hf : ObjectProperty.IsSeparating (.ofObj f)) {c
 : Cofan f} (hc : IsColimit c) : Is…
-/
lemma isSeparator_iff_of_isColimit_cofan {β : Type w} {f : β → C}
    {c : Cofan f} (hc : IsColimit c) :
    IsSeparator c.pt ↔ ObjectProperty.IsSeparating (.ofObj f) := by
  refine ⟨fun h X Y u v huv => ?_, fun h => isSeparator_of_isColimit_cofan h hc⟩
  refine h.def _ _ fun g => hc.hom_ext fun b => ?_
  simpa using! huv (f b.as) (by simp) (c.inj _ ≫ g)
/-
**CategoryTheory.isSeparator_sigma** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：isSeparator_sigma {β : Type w} (f : β -> C) [HasCoproduct f] : IsSeparator
 (∐ f) ↔ ObjectProperty.IsSeparating (.ofObj f)
参数：f : β -> C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.isSeparator_iff_of_isColimit_cofan`：isSeparator_iff_of_is
Colimit_cofan {β : Type w} {f : β -> C} {c : Cofan f} (hc : IsColimit c) : IsSep
arator c.pt ↔ ObjectProperty.IsSeparati…
-/
theorem isSeparator_sigma {β : Type w} (f : β → C) [HasCoproduct f] :
    IsSeparator (∐ f) ↔ ObjectProperty.IsSeparating (.ofObj f) :=
  isSeparator_iff_of_isColimit_cofan (hc := colimit.isColimit _)
/-
**CategoryTheory.isSeparator_coprod** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：isSeparator_coprod (G H : C) [HasBinaryCoproduct G H] : IsSeparator (G ⨿ H
) ↔ ObjectProperty.IsSeparating (.pair G H)
参数：G H : C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用引理 `CategoryTheory.isSeparator_iff_of_isColimit_cofan`：isSeparator_iff_of_is
Colimit_cofan {β : Type w} {f : β -> C} {c : Cofan f} (hc : IsColimit c) : IsSep
arator c.pt ↔ ObjectProperty.IsSeparati…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isSeparator_coprod (G H : C) [HasBinaryCoproduct G H] :
    IsSeparator (G ⨿ H) ↔ ObjectProperty.IsSeparating (.pair G H) := by
  refine (isSeparator_iff_of_isColimit_cofan (coprodIsCoprod G H)).trans ?_
  convert! Iff.rfl
  ext X
  simp only [ObjectProperty.pair_iff, ObjectProperty.ofObj_iff]
  constructor
  · rintro (rfl | rfl); exacts [⟨.left, rfl⟩, ⟨.right, rfl⟩]
  · rintro ⟨⟨_ | _⟩, rfl⟩ <;> tauto
/-
**CategoryTheory.isSeparator_coprod_of_isSeparator_left** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory`。
形式化陈述：isSeparator_coprod_of_isSeparator_left (G H : C) [HasBinaryCoproduct G H] 
(hG : IsSeparator G) : IsSeparator (G ⨿ H)
参数：G H : C；hG : IsSeparator G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.isSeparator_coprod`：isSeparator_coprod (G H : C) [HasBina
ryCoproduct G H] : IsSeparator (G ⨿ H) ↔ ObjectProperty.IsSeparating (.pair G H)
· 使用定理 `CategoryTheory.ObjectProperty.IsSeparating.of_le`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {P : CategoryTheory.ObjectProperty C},   P
.IsSeparating → ∀ {Q : CategoryTheory.…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
-/
theorem isSeparator_coprod_of_isSeparator_left (G H : C) [HasBinaryCoproduct G H]
    (hG : IsSeparator G) : IsSeparator (G ⨿ H) :=
  (isSeparator_coprod _ _).2 <| ObjectProperty.IsSeparating.of_le hG <| by simp
/-
**CategoryTheory.isSeparator_coprod_of_isSeparator_right** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory`。
形式化陈述：isSeparator_coprod_of_isSeparator_right (G H : C) [HasBinaryCoproduct G H]
 (hH : IsSeparator H) : IsSeparator (G ⨿ H)
参数：G H : C；hH : IsSeparator H。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.isSeparator_coprod`：isSeparator_coprod (G H : C) [HasBina
ryCoproduct G H] : IsSeparator (G ⨿ H) ↔ ObjectProperty.IsSeparating (.pair G H)
· 使用定理 `CategoryTheory.ObjectProperty.IsSeparating.of_le`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {P : CategoryTheory.ObjectProperty C},   P
.IsSeparating → ∀ {Q : CategoryTheory.…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
-/
theorem isSeparator_coprod_of_isSeparator_right (G H : C) [HasBinaryCoproduct G H]
    (hH : IsSeparator H) : IsSeparator (G ⨿ H) :=
  (isSeparator_coprod _ _).2 <| ObjectProperty.IsSeparating.of_le hH <| by simp
/-
**CategoryTheory.ObjectProperty.IsSeparating.isSeparator_coproduct** 是 Mathlib 中
的一个定理，位于命名空间 `CategoryTheory.ObjectProperty.IsSeparating`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [CategoryTheor
y.Limits.HasZeroMorphisms C] {β : Type w}   {f : β → C} [inst_2 : CategoryTheory
.Limits.HasCoproduct f],   (CategoryTheory.ObjectProperty.ofObj f).IsSeparating 
→ CategoryTheory.IsSeparator (∐ f)
参数：CategoryTheory.ObjectProperty.ofObj f；∐ f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.isSeparator_sigma`：isSeparator_sigma {β : Type w} (f : β 
-> C) [HasCoproduct f] : IsSeparator (∐ f) ↔ ObjectProperty.IsSeparating (.ofObj
 f)
-/
theorem ObjectProperty.IsSeparating.isSeparator_coproduct
    {β : Type w} {f : β → C} [HasCoproduct f]
    (hS : ObjectProperty.IsSeparating (.ofObj f)) : IsSeparator (∐ f) :=
  (isSeparator_sigma _).2 hS
/-
**CategoryTheory.isSeparator_sigma_of_isSeparator** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory`。
形式化陈述：isSeparator_sigma_of_isSeparator {β : Type w} (f : β -> C) [HasCoproduct f
] (b : β) (hb : IsSeparator (f b)) : IsSeparator (∐ f)
参数：f : β -> C；b : β；hb : IsSeparator (f b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.isSeparator_sigma`：isSeparator_sigma {β : Type w} (f : β 
-> C) [HasCoproduct f] : IsSeparator (∐ f) ↔ ObjectProperty.IsSeparating (.ofObj
 f)
· 使用定理 `CategoryTheory.ObjectProperty.IsSeparating.of_le`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {P : CategoryTheory.ObjectProperty C},   P
.IsSeparating → ∀ {Q : CategoryTheory.…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
theorem isSeparator_sigma_of_isSeparator {β : Type w} (f : β → C) [HasCoproduct f] (b : β)
    (hb : IsSeparator (f b)) : IsSeparator (∐ f) :=
  (isSeparator_sigma _).2 <| ObjectProperty.IsSeparating.of_le hb <| by simp

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.isCoseparator_of_isLimit_fan** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory`。
形式化陈述：isCoseparator_of_isLimit_fan {β : Type w} {f : β -> C} (hf : ObjectPropert
y.IsCoseparating (.ofObj f)) {c : Fan f} (hc : IsLimit c) : IsCoseparator c.pt
参数：hf : ObjectProperty.IsCoseparating (.ofObj f)；hc : IsLimit c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.isCoseparator_def`：isCoseparator_def (G : C) : IsCosepara
tor G ↔ forall ⦃X Y : C⦄ (f g : X ⟶ Y), (forall h : Y ⟶ G, f ≫ h = g ≫ h) -> f =
 g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.Fan.IsLimit.lift_proj`：∀ {β : Type w} {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {X : β → C} {c : CategoryTheory.Limit
s.Fan X}   (d : CategoryTheory.Li…
· 使用定理 `Pi.single_eq_same`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) →
 Zero (M i)] [inst_1 : DecidableEq ι] (i : ι) (x : M i),   Pi.single i x i = x
· 使用定理 `CategoryTheory.eq_whisker`：eq_whisker {f g : X ⟶ Y} (w : f = g) (h : Y ⟶
 Z) : f ≫ h = g ≫ h
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma isCoseparator_of_isLimit_fan {β : Type w} {f : β → C}
    (hf : ObjectProperty.IsCoseparating (.ofObj f)) {c : Fan f} (hc : IsLimit c) :
    IsCoseparator c.pt := by
  rw [isCoseparator_def]
  refine fun _ _ _ _ huv ↦ hf _ _ (fun _ h g ↦ ?_)
  obtain ⟨b⟩ := h
  classical simpa using huv (hc.lift (Fan.mk _ (Pi.single b g))) =≫ c.proj b

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.isCoseparator_iff_of_isLimit_fan** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory`。
形式化陈述：isCoseparator_iff_of_isLimit_fan {β : Type w} {f : β -> C} {c : Fan f} (hc
 : IsLimit c) : IsCoseparator c.pt ↔ ObjectProperty.IsCoseparating (.ofObj f)
参数：hc : IsLimit c。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsCoseparator.def`：∀ {C : Type u₁} [inst : CategoryTheory
.Category.{v₁, u₁} C] {G : C},   CategoryTheory.IsCoseparator G →     ∀ ⦃X Y : C
⦄ (f g : X ⟶ Y),      …
· 使用定理 `CategoryTheory.Limits.IsLimit.hom_ext`：hom_ext (h : IsLimit t) {W : C} {
f f' : W ⟶ t.pt} (w : forall j, f ≫ t.π.app j = f' ≫ t.π.app j) : f = f'
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `CategoryTheory.isCoseparator_of_isLimit_fan`：isCoseparator_of_isLimit_fa
n {β : Type w} {f : β -> C} (hf : ObjectProperty.IsCoseparating (.ofObj f)) {c :
 Fan f} (hc : IsLimit c) : IsCose…
-/
lemma isCoseparator_iff_of_isLimit_fan {β : Type w} {f : β → C}
    {c : Fan f} (hc : IsLimit c) :
    IsCoseparator c.pt ↔ ObjectProperty.IsCoseparating (.ofObj f) := by
  refine ⟨fun h X Y u v huv => ?_, fun h => isCoseparator_of_isLimit_fan h hc⟩
  refine h.def _ _ fun g => hc.hom_ext fun b => ?_
  simpa using! huv (f b.as) (by simp) (g ≫ c.proj _)
/-
**CategoryTheory.isCoseparator_pi** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：isCoseparator_pi {β : Type w} (f : β -> C) [HasProduct f] : IsCoseparator 
(∏ᶜ f) ↔ ObjectProperty.IsCoseparating (.ofObj f)
参数：f : β -> C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.isCoseparator_iff_of_isLimit_fan`：isCoseparator_iff_of_is
Limit_fan {β : Type w} {f : β -> C} {c : Fan f} (hc : IsLimit c) : IsCoseparator
 c.pt ↔ ObjectProperty.IsCoseparating…
-/
theorem isCoseparator_pi {β : Type w} (f : β → C) [HasProduct f] :
    IsCoseparator (∏ᶜ f) ↔ ObjectProperty.IsCoseparating (.ofObj f) :=
  isCoseparator_iff_of_isLimit_fan (hc := limit.isLimit _)
/-
**CategoryTheory.isCoseparator_prod** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：isCoseparator_prod (G H : C) [HasBinaryProduct G H] : IsCoseparator (G ⨯ H
) ↔ ObjectProperty.IsCoseparating (.pair G H)
参数：G H : C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用引理 `CategoryTheory.isCoseparator_iff_of_isLimit_fan`：isCoseparator_iff_of_is
Limit_fan {β : Type w} {f : β -> C} {c : Fan f} (hc : IsLimit c) : IsCoseparator
 c.pt ↔ ObjectProperty.IsCoseparating…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isCoseparator_prod (G H : C) [HasBinaryProduct G H] :
    IsCoseparator (G ⨯ H) ↔ ObjectProperty.IsCoseparating (.pair G H) := by
  refine (isCoseparator_iff_of_isLimit_fan (prodIsProd G H)).trans ?_
  convert! Iff.rfl
  ext X
  simp only [ObjectProperty.pair_iff, ObjectProperty.ofObj_iff]
  constructor
  · rintro (rfl | rfl); exacts [⟨.left, rfl⟩, ⟨.right, rfl⟩]
  · rintro ⟨⟨_ | _⟩, rfl⟩ <;> tauto
/-
**CategoryTheory.isCoseparator_prod_of_isCoseparator_left** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory`。
形式化陈述：isCoseparator_prod_of_isCoseparator_left (G H : C) [HasBinaryProduct G H] 
(hG : IsCoseparator G) : IsCoseparator (G ⨯ H)
参数：G H : C；hG : IsCoseparator G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.isCoseparator_prod`：isCoseparator_prod (G H : C) [HasBina
ryProduct G H] : IsCoseparator (G ⨯ H) ↔ ObjectProperty.IsCoseparating (.pair G 
H)
· 使用定理 `CategoryTheory.ObjectProperty.IsCoseparating.of_le`：∀ {C : Type u₁} [ins
t : CategoryTheory.Category.{v₁, u₁} C] {P : CategoryTheory.ObjectProperty C},  
 P.IsCoseparating → ∀ {Q : CategoryTheor…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
-/
theorem isCoseparator_prod_of_isCoseparator_left (G H : C) [HasBinaryProduct G H]
    (hG : IsCoseparator G) : IsCoseparator (G ⨯ H) :=
  (isCoseparator_prod _ _).2 <| ObjectProperty.IsCoseparating.of_le hG <| by simp
/-
**CategoryTheory.isCoseparator_prod_of_isCoseparator_right** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory`。
形式化陈述：isCoseparator_prod_of_isCoseparator_right (G H : C) [HasBinaryProduct G H]
 (hH : IsCoseparator H) : IsCoseparator (G ⨯ H)
参数：G H : C；hH : IsCoseparator H。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.isCoseparator_prod`：isCoseparator_prod (G H : C) [HasBina
ryProduct G H] : IsCoseparator (G ⨯ H) ↔ ObjectProperty.IsCoseparating (.pair G 
H)
· 使用定理 `CategoryTheory.ObjectProperty.IsCoseparating.of_le`：∀ {C : Type u₁} [ins
t : CategoryTheory.Category.{v₁, u₁} C] {P : CategoryTheory.ObjectProperty C},  
 P.IsCoseparating → ∀ {Q : CategoryTheor…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
-/
theorem isCoseparator_prod_of_isCoseparator_right (G H : C) [HasBinaryProduct G H]
    (hH : IsCoseparator H) : IsCoseparator (G ⨯ H) :=
  (isCoseparator_prod _ _).2 <| ObjectProperty.IsCoseparating.of_le hH <| by simp
/-
**CategoryTheory.isCoseparator_pi_of_isCoseparator** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory`。
形式化陈述：isCoseparator_pi_of_isCoseparator {β : Type w} (f : β -> C) [HasProduct f]
 (b : β) (hb : IsCoseparator (f b)) : IsCoseparator (∏ᶜ f)
参数：f : β -> C；b : β；hb : IsCoseparator (f b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.isCoseparator_pi`：isCoseparator_pi {β : Type w} (f : β ->
 C) [HasProduct f] : IsCoseparator (∏ᶜ f) ↔ ObjectProperty.IsCoseparating (.ofOb
j f)
· 使用定理 `CategoryTheory.ObjectProperty.IsCoseparating.of_le`：∀ {C : Type u₁} [ins
t : CategoryTheory.Category.{v₁, u₁} C] {P : CategoryTheory.ObjectProperty C},  
 P.IsCoseparating → ∀ {Q : CategoryTheor…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
theorem isCoseparator_pi_of_isCoseparator {β : Type w} (f : β → C) [HasProduct f] (b : β)
    (hb : IsCoseparator (f b)) : IsCoseparator (∏ᶜ f) :=
  (isCoseparator_pi _).2 <| ObjectProperty.IsCoseparating.of_le hb <| by simp

end ZeroMorphisms

/-
**CategoryTheory.isDetector_iff_reflectsIsomorphisms_coyoneda_obj** 是 Mathlib 中的
一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：isDetector_iff_reflectsIsomorphisms_coyoneda_obj (G : C) : IsDetector G ↔ 
(coyoneda.obj (op G)).ReflectsIsomorphisms
参数：G : C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsDetector.def`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {G : C},   CategoryTheory.IsDetector G →     ∀ ⦃X Y : C⦄ (f :
 X ⟶ Y),       (∀ (…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.bijective_iff_existsUnique`：bijective_iff_existsUnique (f : α -
> β) : Bijective f ↔ forall b : β, exists! a : α, f a = b
· 使用定理 `CategoryTheory.isIso_iff_bijective`：isIso_iff_bijective {X Y : Type u} (
f : X ⟶ Y) : IsIso f ↔ Function.Bijective f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.isDetector_def`：isDetector_def (G : C) : IsDetector G ↔ f
orall ⦃X Y : C⦄ (f : X ⟶ Y), (forall h : G ⟶ Y, exists! h', h' ≫ f = h) -> IsIso
 f
· 使用定理 `CategoryTheory.isIso_of_reflects_iso`：isIso_of_reflects_iso {A B : C} (f
 : A ⟶ B) (F : C ⥤ D) [IsIso (F.map f)] [F.ReflectsIsomorphisms] : IsIso f
-/
theorem isDetector_iff_reflectsIsomorphisms_coyoneda_obj (G : C) :
    IsDetector G ↔ (coyoneda.obj (op G)).ReflectsIsomorphisms := by
  refine
    ⟨fun hG => ⟨fun f hf => hG.def _ fun h => ?_⟩, fun h =>
      (isDetector_def _).2 fun X Y f hf => ?_⟩
  · rw [isIso_iff_bijective, Function.bijective_iff_existsUnique] at hf
    exact hf h
  · suffices IsIso ((coyoneda.obj (op G)).map f) by
      exact @isIso_of_reflects_iso _ _ _ _ _ _ _ (coyoneda.obj (op G)) _ h
    rwa [isIso_iff_bijective, Function.bijective_iff_existsUnique]
/-
**CategoryTheory.isCodetector_iff_reflectsIsomorphisms_yoneda_obj** 是 Mathlib 中的
一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：isCodetector_iff_reflectsIsomorphisms_yoneda_obj (G : C) : IsCodetector G 
↔ (yoneda.obj G).ReflectsIsomorphisms
参数：G : C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.isIso_unop_iff`：isIso_unop_iff {X Y : Cᵒᵖ} (f : X ⟶ Y) : 
IsIso f.unop ↔ IsIso f
· 使用定理 `CategoryTheory.IsCodetector.def`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {G : C},   CategoryTheory.IsCodetector G →     ∀ ⦃X Y : C⦄ 
(f : X ⟶ Y),       (∀…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.bijective_iff_existsUnique`：bijective_iff_existsUnique (f : α -
> β) : Bijective f ↔ forall b : β, exists! a : α, f a = b
· 使用定理 `CategoryTheory.isIso_iff_bijective`：isIso_iff_bijective {X Y : Type u} (
f : X ⟶ Y) : IsIso f ↔ Function.Bijective f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.isCodetector_def`：isCodetector_def (G : C) : IsCodetector
 G ↔ forall ⦃X Y : C⦄ (f : X ⟶ Y), (forall h : X ⟶ G, exists! h', f ≫ h' = h) ->
 IsIso f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.isIso_op_iff`：isIso_op_iff {X Y : C} (f : X ⟶ Y) : IsIso 
f.op ↔ IsIso f
· 使用定理 `CategoryTheory.isIso_of_reflects_iso`：isIso_of_reflects_iso {A B : C} (f
 : A ⟶ B) (F : C ⥤ D) [IsIso (F.map f)] [F.ReflectsIsomorphisms] : IsIso f
-/
theorem isCodetector_iff_reflectsIsomorphisms_yoneda_obj (G : C) :
    IsCodetector G ↔ (yoneda.obj G).ReflectsIsomorphisms := by
  refine ⟨fun hG => ⟨fun f hf => ?_⟩, fun h => (isCodetector_def _).2 fun X Y f hf => ?_⟩
  · refine (isIso_unop_iff _).1 (hG.def _ ?_)
    rwa [isIso_iff_bijective, Function.bijective_iff_existsUnique] at hf
  · rw [← isIso_op_iff]
    suffices IsIso ((yoneda.obj G).map f.op) by
      exact @isIso_of_reflects_iso _ _ _ _ _ _ _ (yoneda.obj G) _ h
    rwa [isIso_iff_bijective, Function.bijective_iff_existsUnique]
/-
**CategoryTheory.wellPowered_of_isDetector** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory`。
形式化陈述：wellPowered_of_isDetector [HasPullbacks C] (G : C) (hG : IsDetector G) : W
ellPowered.{v₁} C
参数：G : C；hG : IsDetector G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.wellPowered_of_isDetecting`：wellPowered_of_isDetecting [H
asPullbacks C] {𝒢 : ObjectProperty C} [ObjectProperty.Small.{w} 𝒢] [LocallySmall
.{w} C] (h𝒢 : 𝒢.IsDetecting) : …
· 使用定理 `CategoryTheory.ObjectProperty.instSmallOfObjOfSmall`：∀ {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C] {ι : Type u_1} (X : ι → C) [Small.{w, u_1}
 ι],   CategoryTheory.ObjectProperty.Smal…
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `CategoryTheory.locallySmall_of_univLE`：∀ (C : Type u) [inst : CategoryTh
eory.Category.{v, u} C] [UnivLE.{v, w}], CategoryTheory.LocallySmall.{w, v, u} C
-/
theorem wellPowered_of_isDetector [HasPullbacks C] (G : C) (hG : IsDetector G) :
    WellPowered.{v₁} C :=
  wellPowered_of_isDetecting hG
/-
**CategoryTheory.wellPowered_of_isSeparator** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory`。
形式化陈述：wellPowered_of_isSeparator [HasPullbacks C] [Balanced C] (G : C) (hG : IsS
eparator G) : WellPowered.{v₁} C
参数：G : C；hG : IsSeparator G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.wellPowered_of_isDetecting`：wellPowered_of_isDetecting [H
asPullbacks C] {𝒢 : ObjectProperty C} [ObjectProperty.Small.{w} 𝒢] [LocallySmall
.{w} C] (h𝒢 : 𝒢.IsDetecting) : …
· 使用定理 `CategoryTheory.ObjectProperty.instSmallOfObjOfSmall`：∀ {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C] {ι : Type u_1} (X : ι → C) [Small.{w, u_1}
 ι],   CategoryTheory.ObjectProperty.Smal…
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `CategoryTheory.locallySmall_of_univLE`：∀ (C : Type u) [inst : CategoryTh
eory.Category.{v, u} C] [UnivLE.{v, w}], CategoryTheory.LocallySmall.{w, v, u} C
· 使用定理 `CategoryTheory.IsSeparator.isDetector`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} C] [CategoryTheory.Balanced C] {G : C},   CategoryTheory
.IsSeparator G → CategoryTh…
-/
theorem wellPowered_of_isSeparator [HasPullbacks C] [Balanced C] (G : C) (hG : IsSeparator G) :
    WellPowered.{v₁} C := wellPowered_of_isDetecting hG.isDetector

section HasGenerator

section Definitions

variable (C)

/--
For a category `C` and an object `G : C`, `G` is a separator of `C` if
the functor `C(G, -)` is faithful.

While `IsSeparator G : Prop` is the proposition that `G` is a separator of `C`,
an `HasSeparator C : Prop` is the proposition that such a separator exists.
Note that `HasSeparator C` is a proposition. It does not designate a favored separator
and merely asserts the existence of one.
-/
/-
**CategoryTheory.HasSeparator** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`。
形式化陈述：(C : Type u₁) → [CategoryTheory.Category.{v₁, u₁} C] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For a category `C` and an object `G : C`, `G` is a separator of `C` if
the functor `C(G, -)` is faithful.

While `IsSeparator G : Prop` is the proposition that `G` is a separator of `C`,
an `HasSeparator C : Prop` is the proposition that such a separator exists.
Note that `HasSeparator C` is a proposition. It does not designate a favored sep
arator
and merely asserts the existence of one.
-/
class HasSeparator : Prop where
  hasSeparator : ∃ G : C, IsSeparator G

/--
For a category `C` and an object `G : C`, `G` is a coseparator of `C` if
the functor `C(-, G)` is faithful.

While `IsCoseparator G : Prop` is the proposition that `G` is a coseparator of `C`,
an `HasCoseparator C : Prop` is the proposition that such a coseparator exists.
Note that `HasCoseparator C` is a proposition. It does not designate a favored coseparator
and merely asserts the existence of one.
-/
/-
**CategoryTheory.HasCoseparator** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`。
形式化陈述：(C : Type u₁) → [CategoryTheory.Category.{v₁, u₁} C] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For a category `C` and an object `G : C`, `G` is a coseparator of `C` if
the functor `C(-, G)` is faithful.

While `IsCoseparator G : Prop` is the proposition that `G` is a coseparator of `
C`,
an `HasCoseparator C : Prop` is the proposition that such a coseparator exists.
Note that `HasCoseparator C` is a proposition. It does not designate a favored c
oseparator
and merely asserts the existence of one.
-/
class HasCoseparator : Prop where
  hasCoseparator : ∃ G : C, IsCoseparator G

/--
For a category `C` and an object `G : C`, `G` is a detector of `C` if
the functor `C(G, -)` reflects isomorphisms.

While `IsDetector G : Prop` is the proposition that `G` is a detector of `C`,
an `HasDetector C : Prop` is the proposition that such a detector exists.
Note that `HasDetector C` is a proposition. It does not designate a favored detector
and merely asserts the existence of one.
-/
/-
**CategoryTheory.HasDetector** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`。
形式化陈述：(C : Type u₁) → [CategoryTheory.Category.{v₁, u₁} C] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For a category `C` and an object `G : C`, `G` is a detector of `C` if
the functor `C(G, -)` reflects isomorphisms.

While `IsDetector G : Prop` is the proposition that `G` is a detector of `C`,
an `HasDetector C : Prop` is the proposition that such a detector exists.
Note that `HasDetector C` is a proposition. It does not designate a favored dete
ctor
and merely asserts the existence of one.
-/
class HasDetector : Prop where
  hasDetector : ∃ G : C, IsDetector G

/--
For a category `C` and an object `G : C`, `G` is a codetector of `C` if
the functor `C(-, G)` reflects isomorphisms.

While `IsCodetector G : Prop` is the proposition that `G` is a codetector of `C`,
an `HasCodetector C : Prop` is the proposition that such a codetector exists.
Note that `HasCodetector C` is a proposition. It does not designate a favored codetector
and merely asserts the existence of one.
-/
/-
**CategoryTheory.HasCodetector** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`。
形式化陈述：(C : Type u₁) → [CategoryTheory.Category.{v₁, u₁} C] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For a category `C` and an object `G : C`, `G` is a codetector of `C` if
the functor `C(-, G)` reflects isomorphisms.

While `IsCodetector G : Prop` is the proposition that `G` is a codetector of `C`
,
an `HasCodetector C : Prop` is the proposition that such a codetector exists.
Note that `HasCodetector C` is a proposition. It does not designate a favored co
detector
and merely asserts the existence of one.
-/
class HasCodetector : Prop where
  hasCodetector : ∃ G : C, IsCodetector G

end Definitions

section Choice

variable (C)

/--
Given a category `C` that has a separator (`HasSeparator C`), `separator C` is an arbitrarily
chosen separator of `C`.
-/
/-
**CategoryTheory.separator** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：separator [HasSeparator C] : C
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.HasSeparator.hasSeparator`：∀ {C : Type u₁} {inst : Catego
ryTheory.Category.{v₁, u₁} C} [self : CategoryTheory.HasSeparator C],   ∃ G, Cat
egoryTheory.IsSeparator G

--- 原说明 ---
Given a category `C` that has a separator (`HasSeparator C`), `separator C` is a
n arbitrarily
chosen separator of `C`.
-/
noncomputable def separator [HasSeparator C] : C := HasSeparator.hasSeparator.choose

/--
Given a category `C` that has a coseparator (`HasCoseparator C`), `coseparator C` is an arbitrarily
chosen coseparator of `C`.
-/
/-
**CategoryTheory.coseparator** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：coseparator [HasCoseparator C] : C
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.HasCoseparator.hasCoseparator`：∀ {C : Type u₁} {inst : Ca
tegoryTheory.Category.{v₁, u₁} C} [self : CategoryTheory.HasCoseparator C],   ∃ 
G, CategoryTheory.IsCoseparator G

--- 原说明 ---
Given a category `C` that has a coseparator (`HasCoseparator C`), `coseparator C
` is an arbitrarily
chosen coseparator of `C`.
-/
noncomputable def coseparator [HasCoseparator C] : C := HasCoseparator.hasCoseparator.choose

/--
Given a category `C` that has a detector (`HasDetector C`), `detector C` is an arbitrarily
chosen detector of `C`.
-/
/-
**CategoryTheory.detector** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：detector [HasDetector C] : C
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.HasDetector.hasDetector`：∀ {C : Type u₁} {inst : Category
Theory.Category.{v₁, u₁} C} [self : CategoryTheory.HasDetector C],   ∃ G, Catego
ryTheory.IsDetector G

--- 原说明 ---
Given a category `C` that has a detector (`HasDetector C`), `detector C` is an a
rbitrarily
chosen detector of `C`.
-/
noncomputable def detector [HasDetector C] : C := HasDetector.hasDetector.choose

/--
Given a category `C` that has a codetector (`HasCodetector C`), `codetector C` is an arbitrarily
chosen codetector of `C`.
-/
/-
**CategoryTheory.codetector** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：codetector [HasCodetector C] : C
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.HasCodetector.hasCodetector`：∀ {C : Type u₁} {inst : Cate
goryTheory.Category.{v₁, u₁} C} [self : CategoryTheory.HasCodetector C],   ∃ G, 
CategoryTheory.IsCodetector G

--- 原说明 ---
Given a category `C` that has a codetector (`HasCodetector C`), `codetector C` i
s an arbitrarily
chosen codetector of `C`.
-/
noncomputable def codetector [HasCodetector C] : C := HasCodetector.hasCodetector.choose
/-
**CategoryTheory.isSeparator_separator** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
`。
形式化陈述：isSeparator_separator [HasSeparator C] : IsSeparator (separator C)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `CategoryTheory.HasSeparator.hasSeparator`：∀ {C : Type u₁} {inst : Catego
ryTheory.Category.{v₁, u₁} C} [self : CategoryTheory.HasSeparator C],   ∃ G, Cat
egoryTheory.IsSeparator G
-/
theorem isSeparator_separator [HasSeparator C] : IsSeparator (separator C) :=
  HasSeparator.hasSeparator.choose_spec
/-
**CategoryTheory.isDetector_separator** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`
。
形式化陈述：isDetector_separator [Balanced C] [HasSeparator C] : IsDetector (separator
 C)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsSeparator.isDetector`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} C] [CategoryTheory.Balanced C] {G : C},   CategoryTheory
.IsSeparator G → CategoryTh…
· 使用定理 `CategoryTheory.isSeparator_separator`：isSeparator_separator [HasSeparato
r C] : IsSeparator (separator C)
-/
theorem isDetector_separator [Balanced C] [HasSeparator C] : IsDetector (separator C) :=
  isSeparator_separator C |>.isDetector
/-
**CategoryTheory.isCoseparator_coseparator** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory`。
形式化陈述：isCoseparator_coseparator [HasCoseparator C] : IsCoseparator (coseparator 
C)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `CategoryTheory.HasCoseparator.hasCoseparator`：∀ {C : Type u₁} {inst : Ca
tegoryTheory.Category.{v₁, u₁} C} [self : CategoryTheory.HasCoseparator C],   ∃ 
G, CategoryTheory.IsCoseparator G
-/
theorem isCoseparator_coseparator [HasCoseparator C] : IsCoseparator (coseparator C) :=
  HasCoseparator.hasCoseparator.choose_spec
/-
**CategoryTheory.isCodetector_coseparator** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory`。
形式化陈述：isCodetector_coseparator [Balanced C] [HasCoseparator C] : IsCodetector (c
oseparator C)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsCoseparator.isCodetector`：∀ {C : Type u₁} [inst : Categ
oryTheory.Category.{v₁, u₁} C] [CategoryTheory.Balanced C] {G : C},   CategoryTh
eory.IsCoseparator G → Category…
· 使用定理 `CategoryTheory.isCoseparator_coseparator`：isCoseparator_coseparator [Has
Coseparator C] : IsCoseparator (coseparator C)
-/
theorem isCodetector_coseparator [Balanced C] [HasCoseparator C] : IsCodetector (coseparator C) :=
  isCoseparator_coseparator C |>.isCodetector
/-
**CategoryTheory.isDetector_detector** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：isDetector_detector [HasDetector C] : IsDetector (detector C)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `CategoryTheory.HasDetector.hasDetector`：∀ {C : Type u₁} {inst : Category
Theory.Category.{v₁, u₁} C} [self : CategoryTheory.HasDetector C],   ∃ G, Catego
ryTheory.IsDetector G
-/
theorem isDetector_detector [HasDetector C] : IsDetector (detector C) :=
  HasDetector.hasDetector.choose_spec
/-
**CategoryTheory.isSeparator_detector** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`
。
形式化陈述：isSeparator_detector [HasEqualizers C] [HasDetector C] : IsSeparator (dete
ctor C)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsDetector.isSeparator`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} C] [CategoryTheory.Limits.HasEqualizers C] {G : C},   Ca
tegoryTheory.IsDetector G →…
· 使用定理 `CategoryTheory.isDetector_detector`：isDetector_detector [HasDetector C] 
: IsDetector (detector C)
-/
theorem isSeparator_detector [HasEqualizers C] [HasDetector C] : IsSeparator (detector C) :=
  isDetector_detector C |>.isSeparator
/-
**CategoryTheory.isCodetector_codetector** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry`。
形式化陈述：isCodetector_codetector [HasCodetector C] : IsCodetector (codetector C)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `CategoryTheory.HasCodetector.hasCodetector`：∀ {C : Type u₁} {inst : Cate
goryTheory.Category.{v₁, u₁} C} [self : CategoryTheory.HasCodetector C],   ∃ G, 
CategoryTheory.IsCodetector G
-/
theorem isCodetector_codetector [HasCodetector C] : IsCodetector (codetector C) :=
  HasCodetector.hasCodetector.choose_spec
/-
**CategoryTheory.isCoseparator_codetector** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory`。
形式化陈述：isCoseparator_codetector [HasCoequalizers C] [HasCodetector C] : .isCosepa
rator IsCoseparator (codetector C)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsCodetector.isCoseparator`：∀ {C : Type u₁} [inst : Categ
oryTheory.Category.{v₁, u₁} C] [CategoryTheory.Limits.HasCoequalizers C] {G : C}
,   CategoryTheory.IsCodetector…
· 使用定理 `CategoryTheory.isCodetector_codetector`：isCodetector_codetector [HasCode
tector C] : IsCodetector (codetector C)
-/
theorem isCoseparator_codetector [HasCoequalizers C] [HasCodetector C] :
    IsCoseparator (codetector C) := isCodetector_codetector C |>.isCoseparator

end Choice

section Instances

/-
**CategoryTheory.HasSeparator.hasDetector** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.HasSeparator`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [CategoryTheor
y.Balanced C] [CategoryTheory.HasSeparator C],   CategoryTheory.HasDetector C
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.isDetector_separator`：isDetector_separator [Balanced C] [
HasSeparator C] : IsDetector (separator C)
-/
theorem HasSeparator.hasDetector [Balanced C] [HasSeparator C] : HasDetector C :=
  ⟨_, isDetector_separator C⟩
/-
**CategoryTheory.HasDetector.hasSeparator** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.HasDetector`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [CategoryTheor
y.Limits.HasEqualizers C]   [CategoryTheory.HasDetector C], CategoryTheory.HasSe
parator C
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.isSeparator_detector`：isSeparator_detector [HasEqualizers
 C] [HasDetector C] : IsSeparator (detector C)
-/
theorem HasDetector.hasSeparator [HasEqualizers C] [HasDetector C] : HasSeparator C :=
  ⟨_, isSeparator_detector C⟩
/-
**CategoryTheory.HasCoseparator.hasCodetector** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.HasCoseparator`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [CategoryTheor
y.Balanced C]   [CategoryTheory.HasCoseparator C], CategoryTheory.HasCodetector 
C
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.isCodetector_coseparator`：isCodetector_coseparator [Balan
ced C] [HasCoseparator C] : IsCodetector (coseparator C)
-/
theorem HasCoseparator.hasCodetector [Balanced C] [HasCoseparator C] : HasCodetector C :=
  ⟨_, isCodetector_coseparator C⟩
/-
**CategoryTheory.HasCodetector.hasCoseparator** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.HasCodetector`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [CategoryTheor
y.Limits.HasCoequalizers C]   [CategoryTheory.HasCodetector C], CategoryTheory.H
asCoseparator C
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.isCoseparator_codetector`：isCoseparator_codetector [HasCo
equalizers C] [HasCodetector C] : .isCoseparator IsCoseparator (codetector C)
-/
theorem HasCodetector.hasCoseparator [HasCoequalizers C] [HasCodetector C] : HasCoseparator C :=
  ⟨_, isCoseparator_codetector C⟩
/-
**CategoryTheory.HasDetector.wellPowered** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.HasDetector`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [CategoryTheor
y.Limits.HasPullbacks C]   [CategoryTheory.HasDetector C], CategoryTheory.WellPo
wered.{v₁, v₁, u₁} C
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.wellPowered_of_isDetector`：wellPowered_of_isDetector [Has
Pullbacks C] (G : C) (hG : IsDetector G) : WellPowered.{v₁} C
· 使用定理 `CategoryTheory.isDetector_detector`：isDetector_detector [HasDetector C] 
: IsDetector (detector C)
-/
instance HasDetector.wellPowered [HasPullbacks C] [HasDetector C] : WellPowered.{v₁} C :=
  isDetector_detector C |> wellPowered_of_isDetector _
/-
**CategoryTheory.HasSeparator.wellPowered** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.HasSeparator`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [CategoryTheor
y.Limits.HasPullbacks C]   [CategoryTheory.Balanced C] [CategoryTheory.HasSepara
tor C], CategoryTheory.WellPowered.{v₁, v₁, u₁} C
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.HasDetector.wellPowered`：∀ {C : Type u₁} [inst : Category
Theory.Category.{v₁, u₁} C] [CategoryTheory.Limits.HasPullbacks C]   [CategoryTh
eory.HasDetector C], Categor…
· 使用定理 `CategoryTheory.HasSeparator.hasDetector`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] [CategoryTheory.Balanced C] [CategoryTheory.HasSepa
rator C],   CategoryTheory.Ha…
-/
instance HasSeparator.wellPowered [HasPullbacks C] [Balanced C] [HasSeparator C] :
    WellPowered.{v₁} C := HasSeparator.hasDetector.wellPowered

end Instances

section Equivalence

/-
**CategoryTheory.HasSeparator.of_equivalence** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.HasSeparator`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   [CategoryTheory.HasSeparator C] 
(α : C ≌ D), CategoryTheory.HasSeparator D
参数：α : C ≌ D。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsSeparator.of_equivalence`：∀ {C : Type u₁} [inst : Categ
oryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{
v₂, u₂} D]   {G : C}, CategoryT…
· 使用定理 `CategoryTheory.isSeparator_separator`：isSeparator_separator [HasSeparato
r C] : IsSeparator (separator C)
-/
theorem HasSeparator.of_equivalence [HasSeparator C] (α : C ≌ D) : HasSeparator D :=
  ⟨α.functor.obj (separator C), isSeparator_separator C |>.of_equivalence α⟩
/-
**CategoryTheory.HasCoseparator.of_equivalence** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.HasCoseparator`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   [CategoryTheory.HasCoseparator C
] (α : C ≌ D), CategoryTheory.HasCoseparator D
参数：α : C ≌ D。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsCoseparator.of_equivalence`：∀ {C : Type u₁} [inst : Cat
egoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category
.{v₂, u₂} D]   {G : C}, CategoryT…
· 使用定理 `CategoryTheory.isCoseparator_coseparator`：isCoseparator_coseparator [Has
Coseparator C] : IsCoseparator (coseparator C)
-/
theorem HasCoseparator.of_equivalence [HasCoseparator C] (α : C ≌ D) : HasCoseparator D :=
  ⟨α.functor.obj (coseparator C), isCoseparator_coseparator C |>.of_equivalence α⟩

end Equivalence

section Dual

@[simp]
/-
**CategoryTheory.hasSeparator_op_iff** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：hasSeparator_op_iff : HasSeparator Cᵒᵖ ↔ HasCoseparator C
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.isCoseparator_unop_iff`：isCoseparator_unop_iff (G : Cᵒᵖ) 
: IsCoseparator (unop G) ↔ IsSeparator G
· 使用定理 `CategoryTheory.isSeparator_op_iff`：isSeparator_op_iff (G : C) : IsSepara
tor (op G) ↔ IsCoseparator G
-/
theorem hasSeparator_op_iff : HasSeparator Cᵒᵖ ↔ HasCoseparator C :=
  ⟨fun ⟨G, hG⟩ => ⟨unop G, (isCoseparator_unop_iff G).mpr hG⟩,
   fun ⟨G, hG⟩ => ⟨op G, (isSeparator_op_iff G).mpr hG⟩⟩

@[simp]
/-
**CategoryTheory.hasCoseparator_op_iff** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
`。
形式化陈述：hasCoseparator_op_iff : HasCoseparator Cᵒᵖ ↔ HasSeparator C
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.isSeparator_unop_iff`：isSeparator_unop_iff (G : Cᵒᵖ) : Is
Separator (unop G) ↔ IsCoseparator G
· 使用定理 `CategoryTheory.isCoseparator_op_iff`：isCoseparator_op_iff (G : C) : IsCo
separator (op G) ↔ IsSeparator G
-/
theorem hasCoseparator_op_iff : HasCoseparator Cᵒᵖ ↔ HasSeparator C :=
  ⟨fun ⟨G, hG⟩ => ⟨unop G, (isSeparator_unop_iff G).mpr hG⟩,
   fun ⟨G, hG⟩ => ⟨op G, (isCoseparator_op_iff G).mpr hG⟩⟩

@[simp]
/-
**CategoryTheory.hasDetector_op_iff** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：hasDetector_op_iff : HasDetector Cᵒᵖ ↔ HasCodetector C
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.isCodetector_unop_iff`：isCodetector_unop_iff (G : Cᵒᵖ) : 
IsCodetector (unop G) ↔ IsDetector G
· 使用定理 `CategoryTheory.isDetector_op_iff`：isDetector_op_iff (G : C) : IsDetector
 (op G) ↔ IsCodetector G
-/
theorem hasDetector_op_iff : HasDetector Cᵒᵖ ↔ HasCodetector C :=
  ⟨fun ⟨G, hG⟩ => ⟨unop G, (isCodetector_unop_iff G).mpr hG⟩,
   fun ⟨G, hG⟩ => ⟨op G, (isDetector_op_iff G).mpr hG⟩⟩

@[simp]
/-
**CategoryTheory.hasCodetector_op_iff** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`
。
形式化陈述：hasCodetector_op_iff : HasCodetector Cᵒᵖ ↔ HasDetector C
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.isDetector_unop_iff`：isDetector_unop_iff (G : Cᵒᵖ) : IsDe
tector (unop G) ↔ IsCodetector G
· 使用定理 `CategoryTheory.isCodetector_op_iff`：isCodetector_op_iff (G : C) : IsCode
tector (op G) ↔ IsDetector G
-/
theorem hasCodetector_op_iff : HasCodetector Cᵒᵖ ↔ HasDetector C :=
  ⟨fun ⟨G, hG⟩ => ⟨unop G, (isDetector_unop_iff G).mpr hG⟩,
   fun ⟨G, hG⟩ => ⟨op G, (isCodetector_op_iff G).mpr hG⟩⟩
/-
**CategoryTheory.HasSeparator.hasCoseparator_op** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.HasSeparator`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [CategoryTheor
y.HasSeparator C],   CategoryTheory.HasCoseparator Cᵒᵖ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
instance HasSeparator.hasCoseparator_op [HasSeparator C] : HasCoseparator Cᵒᵖ := by simp [*]
/-
**CategoryTheory.HasSeparator.hasCoseparator_of_hasSeparator_op** 是 Mathlib 中的一个
定理，位于命名空间 `CategoryTheory.HasSeparator`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [h : CategoryT
heory.HasSeparator Cᵒᵖ],   CategoryTheory.HasCoseparator C
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem HasSeparator.hasCoseparator_of_hasSeparator_op [h : HasSeparator Cᵒᵖ] :
    HasCoseparator C := by simp_all
/-
**CategoryTheory.HasCoseparator.hasSeparator_op** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.HasCoseparator`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [CategoryTheor
y.HasCoseparator C],   CategoryTheory.HasSeparator Cᵒᵖ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
instance HasCoseparator.hasSeparator_op [HasCoseparator C] : HasSeparator Cᵒᵖ := by simp [*]
/-
**CategoryTheory.HasCoseparator.hasSeparator_of_hasCoseparator_op** 是 Mathlib 中的
一个定理，位于命名空间 `CategoryTheory.HasCoseparator`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [CategoryTheor
y.HasCoseparator Cᵒᵖ],   CategoryTheory.HasSeparator C
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem HasCoseparator.hasSeparator_of_hasCoseparator_op [HasCoseparator Cᵒᵖ] :
    HasSeparator C := by simp_all
/-
**CategoryTheory.HasDetector.hasCodetector_op** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.HasDetector`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [CategoryTheor
y.HasDetector C],   CategoryTheory.HasCodetector Cᵒᵖ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
instance HasDetector.hasCodetector_op [HasDetector C] : HasCodetector Cᵒᵖ := by simp [*]
/-
**CategoryTheory.HasDetector.hasCodetector_of_hasDetector_op** 是 Mathlib 中的一个定理，
位于命名空间 `CategoryTheory.HasDetector`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [CategoryTheor
y.HasDetector Cᵒᵖ],   CategoryTheory.HasCodetector C
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem HasDetector.hasCodetector_of_hasDetector_op [HasDetector Cᵒᵖ] :
    HasCodetector C := by simp_all
/-
**CategoryTheory.HasCodetector.hasDetector_op** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.HasCodetector`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [CategoryTheor
y.HasCodetector C],   CategoryTheory.HasDetector Cᵒᵖ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
instance HasCodetector.hasDetector_op [HasCodetector C] : HasDetector Cᵒᵖ := by simp [*]
/-
**CategoryTheory.HasCodetector.hasDetector_of_hasCodetector_op** 是 Mathlib 中的一个定
理，位于命名空间 `CategoryTheory.HasCodetector`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [CategoryTheor
y.HasCodetector Cᵒᵖ],   CategoryTheory.HasDetector C
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem HasCodetector.hasDetector_of_hasCodetector_op [HasCodetector Cᵒᵖ] :
    HasDetector C := by simp_all

end Dual

end HasGenerator

end CategoryTheory

