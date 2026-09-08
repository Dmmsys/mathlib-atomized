/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Functoriality of the symmetry of equivalences

Using the calculus of mates in `Mathlib.CategoryTheory.Adjunction.Mates`, we prove that passing
to the symmetric equivalence defines an equivalence between `C ≌ D` and `(D ≌ C)ᵒᵖ`,
and provides the definition of the functor that takes an equivalence to its inverse.

## Main definitions
- `Equivalence.symmEquiv C D`: the equivalence `(C ≌ D) ≌ (D ≌ C)ᵒᵖ` obtained by
  taking `Equivalence.symm` on objects, and `conjugateEquiv` on maps.
- `Equivalence.inverseFunctor C D`: The functor `(C ≌ D) ⥤ (D ⥤ C)ᵒᵖ` sending an equivalence
  `e` to the functor `e.inverse`.
- `congrLeftFunctor C D E`: the functor (C ≌ D) ⥤ ((C ⥤ E) ≌ (D ⥤ E))ᵒᵖ that applies
  `Equivalence.congrLeft` on objects, and whiskers left by `conjugateEquiv` on maps.

-/

set_option backward.defeqAttrib.useBackward true

@[expose] public section

namespace CategoryTheory

open CategoryTheory.Functor NatIso Category

namespace Equivalence

variable (C : Type*) [Category* C] (D : Type*) [Category* D]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The forward functor of the equivalence `(C ≌ D) ≌ (D ≌ C)ᵒᵖ`. -/
@[simps]
/-
**CategoryTheory.Equivalence.symmEquivFunctor** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Equivalence`。
形式化陈述：symmEquivFunctor : (C ≌ D) ⥤ (D ≌ C)ᵒᵖ where obj e
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forward functor of the equivalence `(C ≌ D) ≌ (D ≌ C)ᵒᵖ`.
-/
def symmEquivFunctor : (C ≌ D) ⥤ (D ≌ C)ᵒᵖ where
  obj e := Opposite.op e.symm
  map {e f} α := (mkHom <| conjugateEquiv f.toAdjunction e.toAdjunction <| asNatTrans α).op
  map_comp _ _ := Quiver.Hom.unop_inj (by cat_disch)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The inverse functor of the equivalence `(C ≌ D) ≌ (D ≌ C)ᵒᵖ`. -/
@[simps!]
/-
**CategoryTheory.Equivalence.symmEquivInverse** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Equivalence`。
形式化陈述：symmEquivInverse : (D ≌ C)ᵒᵖ ⥤ (C ≌ D)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inverse functor of the equivalence `(C ≌ D) ≌ (D ≌ C)ᵒᵖ`.
-/
def symmEquivInverse : (D ≌ C)ᵒᵖ ⥤ (C ≌ D) :=
  Functor.leftOp
    { obj e := Opposite.op e.symm
      map {e f} α := Quiver.Hom.op <| mkHom <|
        conjugateEquiv e.symm.toAdjunction f.symm.toAdjunction |>.invFun <| asNatTrans α
      map_comp _ _ := Quiver.Hom.unop_inj (by cat_disch) }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Taking the symmetric of an equivalence induces an equivalence of categories
`(C ≌ D) ≌ (D ≌ C)ᵒᵖ`. -/
@[simps]
/-
**CategoryTheory.Equivalence.symmEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Equivalence`。
形式化陈述：symmEquiv : (C ≌ D) ≌ (D ≌ C)ᵒᵖ where functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Taking the symmetric of an equivalence induces an equivalence of categories
`(C ≌ D) ≌ (D ≌ C)ᵒᵖ`.
-/
def symmEquiv : (C ≌ D) ≌ (D ≌ C)ᵒᵖ where
  functor := symmEquivFunctor _ _
  inverse := symmEquivInverse _ _
  counitIso :=
    NatIso.ofComponents (fun e ↦ Iso.op <| Iso.refl _) <| fun _ ↦
      (by simp [symm, symmEquivInverse])
  unitIso :=
    NatIso.ofComponents (fun e ↦ Iso.refl _) <| fun _ ↦ by
      ext c
      simp [symm, symmEquivInverse]
  functor_unitIso_comp X := by
    simp [symm, symmEquivInverse]

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- The `inverse` functor that sends a functor to its inverse. -/
@[simps!]
/-
**CategoryTheory.Equivalence.inverseFunctor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Equivalence`。
形式化陈述：inverseFunctor : (C ≌ D) ⥤ (D ⥤ C)ᵒᵖ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `inverse` functor that sends a functor to its inverse.
-/
def inverseFunctor : (C ≌ D) ⥤ (D ⥤ C)ᵒᵖ :=
  (symmEquiv C D).functor ⋙ (Functor.op <| functorFunctor D C)

variable {C D}

set_option backward.isDefEq.respectTransparency.types false in
/-- The `inverse` functor sends an equivalence to its inverse. -/
@[simps!]
/-
**CategoryTheory.Equivalence.inverseFunctorObjIso** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Equivalence`。
形式化陈述：inverseFunctorObjIso (e : C ≌ D) : (inverseFunctor C D).obj e ≅ Opposite.o
p e.inverse
参数：e : C ≌ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `inverse` functor sends an equivalence to its inverse.
-/
def inverseFunctorObjIso (e : C ≌ D) :
    (inverseFunctor C D).obj e ≅ Opposite.op e.inverse := Iso.refl _

set_option backward.isDefEq.respectTransparency.types false in
/-- We can compare the way we obtain a natural isomorphism `e.inverse ≅ f.inverse` from
an isomorphism `e ≌ f` via `inverseFunctor` with the way we get one through
`Iso.isoInverseOfIsoFunctor`. -/
/-
**CategoryTheory.Equivalence.inverseFunctorMapIso_symm_eq_isoInverseOfIsoFunctor
** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Equivalence`。
形式化陈述：inverseFunctorMapIso_symm_eq_isoInverseOfIsoFunctor {e f : C ≌ D} (α : e ≅
 f) : Iso.unop ((inverseFunctor C D).mapIso α.symm) = Iso.isoInverseOfIsoFunctor
 ((functorFunctor _ _).mapIso α)
参数：α : e ≅ f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.conjugateEquiv_apply_app`：∀ {C : Type u₁} {D : Type u₂} [
inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {L₁ L₂ : CategoryT…
· 使用定理 `CategoryTheory.Iso.isoInverseOfIsoFunctor_hom_app`：∀ {C : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Ca
tegory.{v₂, u₂} D]   {G G' : C ≌ D} (i …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
We can compare the way we obtain a natural isomorphism `e.inverse ≅ f.inverse` f
rom
an isomorphism `e ≌ f` via `inverseFunctor` with the way we get one through
`Iso.isoInverseOfIsoFunctor`.
-/
lemma inverseFunctorMapIso_symm_eq_isoInverseOfIsoFunctor {e f : C ≌ D} (α : e ≅ f) :
    Iso.unop ((inverseFunctor C D).mapIso α.symm) =
    Iso.isoInverseOfIsoFunctor ((functorFunctor _ _).mapIso α) := by
  cat_disch

set_option backward.isDefEq.respectTransparency.types false in
/-- An "unopped" version of the equivalence `inverseFunctorObj'`. -/
@[simps!]
/-
**CategoryTheory.Equivalence.inverseFunctorObj'** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Equivalence`。
形式化陈述：inverseFunctorObj' (e : C ≌ D) : Opposite.unop ((inverseFunctor C D).obj e
) ≅ e.inverse
参数：e : C ≌ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An "unopped" version of the equivalence `inverseFunctorObj'`.
-/
def inverseFunctorObj' (e : C ≌ D) :
    Opposite.unop ((inverseFunctor C D).obj e) ≅ e.inverse :=
  Iso.refl _

set_option backward.isDefEq.respectTransparency.types false in
variable (C D) in
/-- Promoting `Equivalence.congrLeft` to a functor. -/
@[simps!]
/-
**CategoryTheory.Equivalence.congrLeftFunctor** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Equivalence`。
形式化陈述：congrLeftFunctor (E : Type*) [Category* E] : (C ≌ D) ⥤ ((C ⥤ E) ≌ (D ⥤ E))
ᵒᵖ
参数：E : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Promoting `Equivalence.congrLeft` to a functor.
-/
def congrLeftFunctor (E : Type*) [Category* E] : (C ≌ D) ⥤ ((C ⥤ E) ≌ (D ⥤ E))ᵒᵖ :=
  Functor.rightOp
    { obj f := f.unop.congrLeft
      map {e f} α := mkHom <| (whiskeringLeft _ _ _).map <|
        conjugateEquiv e.unop.toAdjunction f.unop.toAdjunction <| asNatTrans <|
          Quiver.Hom.unop α
      map_comp _ _ := by
        ext
        simp [← map_comp] }

end Equivalence

end CategoryTheory

