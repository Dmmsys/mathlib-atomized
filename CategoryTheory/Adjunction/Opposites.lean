/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Thomas Read, Andrew Yang
-/
module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.CategoryTheory.Opposites

/-!
# Opposite adjunctions

This file contains constructions to relate adjunctions of functors to adjunctions of their
opposites.

## Tags
adjunction, opposite, uniqueness
-/

@[expose] public section


open CategoryTheory

universe v₁ v₂ u₁ u₂

-- morphism levels before object levels. See note [category theory universes].
variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

namespace CategoryTheory.Adjunction

attribute [local simp] homEquiv_unit homEquiv_counit

/-- If `G` is adjoint to `F` then `F.unop` is adjoint to `G.unop`. -/
@[simps]
/-
**CategoryTheory.Adjunction.unop** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Adjun
ction`。
形式化陈述：unop {F : Cᵒᵖ ⥤ Dᵒᵖ} {G : Dᵒᵖ ⥤ Cᵒᵖ} (h : G ⊣ F) : F.unop ⊣ G.unop where u
nit
参数：h : G ⊣ F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `G` is adjoint to `F` then `F.unop` is adjoint to `G.unop`.
-/
def unop {F : Cᵒᵖ ⥤ Dᵒᵖ} {G : Dᵒᵖ ⥤ Cᵒᵖ} (h : G ⊣ F) : F.unop ⊣ G.unop where
  unit := NatTrans.unop h.counit
  counit := NatTrans.unop h.unit
  left_triangle_components _ := Quiver.Hom.op_inj (h.right_triangle_components _)
  right_triangle_components _ := Quiver.Hom.op_inj (h.left_triangle_components _)

set_option backward.defeqAttrib.useBackward true in
/-- If `G` is adjoint to `F` then `F.op` is adjoint to `G.op`. -/
@[simps]
/-
**CategoryTheory.Adjunction.op** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Adjunct
ion`。
形式化陈述：op {F : C ⥤ D} {G : D ⥤ C} (h : G ⊣ F) : F.op ⊣ G.op where unit
参数：h : G ⊣ F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `G` is adjoint to `F` then `F.op` is adjoint to `G.op`.
-/
def op {F : C ⥤ D} {G : D ⥤ C} (h : G ⊣ F) : F.op ⊣ G.op where
  unit := NatTrans.op h.counit
  counit := NatTrans.op h.unit
  left_triangle_components _ := Quiver.Hom.unop_inj (by simp)
  right_triangle_components _ := Quiver.Hom.unop_inj (by simp)

/-- If `F` is adjoint to `G.leftOp` then `G` is adjoint to `F.leftOp`. -/
@[simps]
/-
**CategoryTheory.Adjunction.leftOp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Adj
unction`。
形式化陈述：leftOp {F : C ⥤ Dᵒᵖ} {G : D ⥤ Cᵒᵖ} (a : F ⊣ G.leftOp) : G ⊣ F.leftOp where
 unit
参数：a : F ⊣ G.leftOp。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F` is adjoint to `G.leftOp` then `G` is adjoint to `F.leftOp`.
-/
def leftOp {F : C ⥤ Dᵒᵖ} {G : D ⥤ Cᵒᵖ} (a : F ⊣ G.leftOp) : G ⊣ F.leftOp where
  unit := NatTrans.unop a.counit
  counit := NatTrans.op a.unit
  left_triangle_components X := congr($(a.right_triangle_components (.op X)).op)
  right_triangle_components X := congr($(a.left_triangle_components X.unop).unop)

/-- If `F.rightOp` is adjoint to `G` then `G.rightOp` is adjoint to `F`. -/
@[simps]
/-
**CategoryTheory.Adjunction.rightOp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Ad
junction`。
形式化陈述：rightOp {F : Cᵒᵖ ⥤ D} {G : Dᵒᵖ ⥤ C} (a : F.rightOp ⊣ G) : G.rightOp ⊣ F wh
ere unit
参数：a : F.rightOp ⊣ G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F.rightOp` is adjoint to `G` then `G.rightOp` is adjoint to `F`.
-/
def rightOp {F : Cᵒᵖ ⥤ D} {G : Dᵒᵖ ⥤ C} (a : F.rightOp ⊣ G) : G.rightOp ⊣ F where
  unit := NatTrans.unop a.counit
  counit := NatTrans.op a.unit
  left_triangle_components X := congr($(a.right_triangle_components (.op X)).op)
  right_triangle_components X := congr($(a.left_triangle_components X.unop).unop)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Adjunction.leftOp_eq** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.
Adjunction`。
形式化陈述：leftOp_eq {F : C ⥤ Dᵒᵖ} {G : D ⥤ Cᵒᵖ} (a : F ⊣ G.leftOp) : a.leftOp = (opO
pEquivalence D).symm.toAdjunction.comp a.op
参数：a : F ⊣ G.leftOp。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Adjunction.ext`：ext {F : C ⥤ D} {G : D ⥤ C} {adj adj' : F
 ⊣ G} (h : adj.unit = adj'.unit) : adj = adj'
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Adjunction.comp_unit_app`：comp_unit_app (X : C) : dsimp% 
(adj₁.comp adj₂).unit.app X = adj₁.unit.app X ≫ G.map (adj₂.unit.app (F.obj X))
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma leftOp_eq {F : C ⥤ Dᵒᵖ} {G : D ⥤ Cᵒᵖ} (a : F ⊣ G.leftOp) :
    a.leftOp = (opOpEquivalence D).symm.toAdjunction.comp a.op := by
  ext X; simp [Equivalence.unit]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Adjunction.rightOp_eq** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory
.Adjunction`。
形式化陈述：rightOp_eq {F : Cᵒᵖ ⥤ D} {G : Dᵒᵖ ⥤ C} (a : F.rightOp ⊣ G) : a.rightOp = (
opOpEquivalence D).symm.toAdjunction.comp a.op
参数：a : F.rightOp ⊣ G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Adjunction.ext`：ext {F : C ⥤ D} {G : D ⥤ C} {adj adj' : F
 ⊣ G} (h : adj.unit = adj'.unit) : adj = adj'
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Adjunction.comp_unit_app`：comp_unit_app (X : C) : dsimp% 
(adj₁.comp adj₂).unit.app X = adj₁.unit.app X ≫ G.map (adj₂.unit.app (F.obj X))
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma rightOp_eq {F : Cᵒᵖ ⥤ D} {G : Dᵒᵖ ⥤ C} (a : F.rightOp ⊣ G) :
    a.rightOp = (opOpEquivalence D).symm.toAdjunction.comp a.op := by
  ext X; simp [Equivalence.unit]

set_option backward.defeqAttrib.useBackward true in
/-- If `F` and `F'` are both adjoint to `G`, there is a natural isomorphism
`F.op ⋙ coyoneda ≅ F'.op ⋙ coyoneda`.
We use this in combination with `fullyFaithfulCancelRight` to show left adjoints are unique.
-/
@[deprecated "No replacement" (since := "2026-04-11")]
/-
**CategoryTheory.Adjunction.leftAdjointsCoyonedaEquiv** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.Adjunction`。
形式化陈述：leftAdjointsCoyonedaEquiv {F F' : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) (adj2 
: F' ⊣ G) : F.op ⋙ coyoneda ≅ F'.op ⋙ coyoneda
参数：adj1 : F ⊣ G；adj2 : F' ⊣ G。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
If `F` and `F'` are both adjoint to `G`, there is a natural isomorphism
`F.op ⋙ coyoneda ≅ F'.op ⋙ coyoneda`.
We use this in combination with `fullyFaithfulCancelRight` to show left adjoints
 are unique.
-/
def leftAdjointsCoyonedaEquiv {F F' : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F' ⊣ G) :
    F.op ⋙ coyoneda ≅ F'.op ⋙ coyoneda :=
  NatIso.ofComponents fun X =>
    NatIso.ofComponents fun Y =>
      ((adj1.homEquiv X.unop Y).trans (adj2.homEquiv X.unop Y).symm).toIso

/-- Deprecated: prefer `(Adjunction.conjugateIsoEquiv adj1 adj2).symm`. -/
@[deprecated "Use `(Adjunction.conjugateIsoEquiv adj1 adj2).symm` \
  (requires `import Mathlib.CategoryTheory.Adjunction.Mates`)." (since := "2026-01-31")]
/-
**CategoryTheory.Adjunction.natIsoOfRightAdjointNatIso** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.Adjunction`。
形式化陈述：natIsoOfRightAdjointNatIso {F F' : C ⥤ D} {G G' : D ⥤ C} (adj1 : F ⊣ G) (a
dj2 : F' ⊣ G') (r : G ≅ G') : F ≅ F'
参数：adj1 : F ⊣ G；adj2 : F' ⊣ G'；r : G ≅ G'。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
def natIsoOfRightAdjointNatIso {F F' : C ⥤ D} {G G' : D ⥤ C}
    (adj1 : F ⊣ G) (adj2 : F' ⊣ G') (r : G ≅ G') : F ≅ F' :=
  NatIso.removeOp ((Coyoneda.fullyFaithful.whiskeringRight _).isoEquiv.symm
    (leftAdjointsCoyonedaEquiv adj2 (adj1.ofNatIsoRight r)))

/-- Deprecated: prefer `Adjunction.conjugateIsoEquiv adj1 adj2`. -/
@[deprecated "Use `Adjunction.conjugateIsoEquiv adj1 adj2` \
  (requires `import Mathlib.CategoryTheory.Adjunction.Mates`)." (since := "2026-01-31")]
/-
**CategoryTheory.Adjunction.natIsoOfLeftAdjointNatIso** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.Adjunction`。
形式化陈述：natIsoOfLeftAdjointNatIso {F F' : C ⥤ D} {G G' : D ⥤ C} (adj1 : F ⊣ G) (ad
j2 : F' ⊣ G') (l : F ≅ F') : G ≅ G'
参数：adj1 : F ⊣ G；adj2 : F' ⊣ G'；l : F ≅ F'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def natIsoOfLeftAdjointNatIso {F F' : C ⥤ D} {G G' : D ⥤ C}
    (adj1 : F ⊣ G) (adj2 : F' ⊣ G') (l : F ≅ F') : G ≅ G' :=
  NatIso.removeOp (natIsoOfRightAdjointNatIso (op adj2) (op adj1) (NatIso.op l))

end Adjunction

namespace Functor

/-
**CategoryTheory.Functor.IsLeftAdjoint.op** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Functor.IsLeftAdjoint`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {F : CategoryTheory.Functor C D}
 [F.IsLeftAdjoint], F.op.IsRightAdjoint
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance IsLeftAdjoint.op {F : C ⥤ D} [F.IsLeftAdjoint] : F.op.IsRightAdjoint :=
  ⟨F.rightAdjoint.op, ⟨.op <| .ofIsLeftAdjoint _⟩⟩
/-
**CategoryTheory.Functor.IsRightAdjoint.op** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Functor.IsRightAdjoint`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {F : CategoryTheory.Functor C D}
 [F.IsRightAdjoint], F.op.IsLeftAdjoint
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance IsRightAdjoint.op {F : C ⥤ D} [F.IsRightAdjoint] : F.op.IsLeftAdjoint :=
  ⟨F.leftAdjoint.op, ⟨.op <| .ofIsRightAdjoint _⟩⟩
/-
**CategoryTheory.Functor.IsLeftAdjoint.leftOp** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Functor.IsLeftAdjoint`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {F : CategoryTheory.Functor C Dᵒ
ᵖ} [F.IsLeftAdjoint], F.leftOp.IsRightAdjoint
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance IsLeftAdjoint.leftOp {F : C ⥤ Dᵒᵖ} [F.IsLeftAdjoint] : F.leftOp.IsRightAdjoint :=
  ⟨F.rightAdjoint.rightOp, ⟨.leftOp <| .ofIsLeftAdjoint _⟩⟩

-- TODO: Do we need to introduce `Adjunction.leftUnop`?
/-
**CategoryTheory.Functor.IsRightAdjoint.leftOp** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Functor.IsRightAdjoint`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {F : CategoryTheory.Functor C Dᵒ
ᵖ} [F.IsRightAdjoint], F.leftOp.IsLeftAdjoint
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance IsRightAdjoint.leftOp {F : C ⥤ Dᵒᵖ} [F.IsRightAdjoint] : F.leftOp.IsLeftAdjoint :=
  inferInstanceAs (F.op ⋙ (opOpEquivalence D).functor).IsLeftAdjoint

-- TODO: Do we need to introduce `Adjunction.rightUnop`?
/-
**CategoryTheory.Functor.IsLeftAdjoint.rightOp** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Functor.IsLeftAdjoint`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {F : CategoryTheory.Functor Cᵒᵖ 
D} [F.IsLeftAdjoint], F.rightOp.IsRightAdjoint
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance IsLeftAdjoint.rightOp {F : Cᵒᵖ ⥤ D} [F.IsLeftAdjoint] : F.rightOp.IsRightAdjoint :=
  inferInstanceAs ((opOpEquivalence C).inverse ⋙ F.op).IsRightAdjoint
/-
**CategoryTheory.Functor.IsRightAdjoint.rightOp** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Functor.IsRightAdjoint`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {F : CategoryTheory.Functor Cᵒᵖ 
D} [F.IsRightAdjoint], F.rightOp.IsLeftAdjoint
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance IsRightAdjoint.rightOp {F : Cᵒᵖ ⥤ D} [F.IsRightAdjoint] : F.rightOp.IsLeftAdjoint :=
  ⟨F.leftAdjoint.leftOp, ⟨.rightOp <| .ofIsRightAdjoint _⟩⟩

end Functor
end CategoryTheory

