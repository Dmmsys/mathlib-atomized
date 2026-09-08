/-
Copyright (c) 2025 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Floris van Doorn
-/
module

public import Mathlib.CategoryTheory.Limits.Opposites
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Pullbacks and pushouts in `C` and `Cᵒᵖ`

We construct pullbacks and pushouts in the opposite categories.

-/

@[expose] public section

universe v₁ v₂ u₁ u₂

noncomputable section

open CategoryTheory

open CategoryTheory.Functor

open Opposite

namespace CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C]
variable {J : Type u₂} [Category.{v₂} J]

/-
**CategoryTheory.Limits.hasPullbacks_opposite** 是 Mathlib 中的一个实例，位于命名空间 `Categor
yTheory.Limits`。
形式化陈述：hasPullbacks_opposite [HasPushouts C] : HasPullbacks Cᵒᵖ
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasColimitsOfShape_of_equivalence`：hasColimitsOfSh
ape_of_equivalence {J' : Type u₂} [Category.{v₂} J'] (e : J ≌ J') [HasColimitsOf
Shape J C] : HasColimitsOfShape J' C
· 使用定理 `CategoryTheory.Limits.hasLimitsOfShape_op_of_hasColimitsOfShape`：hasLimi
tsOfShape_op_of_hasColimitsOfShape [HasColimitsOfShape Jᵒᵖ C] : HasLimitsOfShape
 J Cᵒᵖ
-/
instance hasPullbacks_opposite [HasPushouts C] : HasPullbacks Cᵒᵖ := by
  have : HasColimitsOfShape WalkingCospanᵒᵖ C :=
    hasColimitsOfShape_of_equivalence walkingCospanOpEquiv.symm
  apply hasLimitsOfShape_op_of_hasColimitsOfShape
/-
**CategoryTheory.Limits.hasPushouts_opposite** 是 Mathlib 中的一个实例，位于命名空间 `Category
Theory.Limits`。
形式化陈述：hasPushouts_opposite [HasPullbacks C] : HasPushouts Cᵒᵖ
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasLimitsOfShape_of_equivalence`：hasLimitsOfShape_
of_equivalence {J' : Type u₂} [Category.{v₂} J'] (e : J ≌ J') [HasLimitsOfShape 
J C] : HasLimitsOfShape J' C
-/
instance hasPushouts_opposite [HasPullbacks C] : HasPushouts Cᵒᵖ := by
  have : HasLimitsOfShape WalkingSpanᵒᵖ C :=
    hasLimitsOfShape_of_equivalence walkingSpanOpEquiv.symm
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The canonical isomorphism relating `Span f.op g.op` and `(Cospan f g).op` -/
@[simps!]
/-
**CategoryTheory.Limits.spanOp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limits`
。
形式化陈述：spanOp {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) : span f.op g.op ≅ walkingCospa
nOpEquiv.inverse ⋙ (cospan f g).op
参数：f : X ⟶ Z；g : Y ⟶ Z。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical isomorphism relating `Span f.op g.op` and `(Cospan f g).op`
-/
def spanOp {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    span f.op g.op ≅ walkingCospanOpEquiv.inverse ⋙ (cospan f g).op :=
  NatIso.ofComponents (fun
    | .none => .refl _
    | .left => .refl _
    | .right => .refl _)
    (by rintro (_ | _ | _) (_ | _ | _) f <;> cases f <;> cat_disch)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The canonical isomorphism relating `span f.unop g.unop` and `(cospan f g).leftOp` -/
@[simps!]
/-
**CategoryTheory.Limits.spanUnop** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limit
s`。
形式化陈述：spanUnop {X Y Z : Cᵒᵖ} (f : X ⟶ Z) (g : Y ⟶ Z) : span f.unop g.unop ≅ walk
ingCospanOpEquiv.inverse ⋙ (cospan f g).leftOp
参数：f : X ⟶ Z；g : Y ⟶ Z。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical isomorphism relating `span f.unop g.unop` and `(cospan f g).leftOp
`
-/
def spanUnop {X Y Z : Cᵒᵖ} (f : X ⟶ Z) (g : Y ⟶ Z) :
    span f.unop g.unop ≅ walkingCospanOpEquiv.inverse ⋙ (cospan f g).leftOp :=
  NatIso.ofComponents (fun
    | .none => .refl _
    | .left => .refl _
    | .right => .refl _)
    (by rintro (_ | _ | _) (_ | _ | _) f <;> cases f <;> cat_disch)

/-- The canonical isomorphism relating `(Cospan f g).op` and `Span f.op g.op` -/
@[simps!]
/-
**CategoryTheory.Limits.opCospan** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limit
s`。
形式化陈述：opCospan {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) : (cospan f g).op ≅ walkingCo
spanOpEquiv.functor ⋙ span f.op g.op
参数：f : X ⟶ Z；g : Y ⟶ Z。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical isomorphism relating `(Cospan f g).op` and `Span f.op g.op`
-/
def opCospan {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    (cospan f g).op ≅ walkingCospanOpEquiv.functor ⋙ span f.op g.op :=
  calc
    (cospan f g).op ≅ 𝟭 _ ⋙ (cospan f g).op := .refl _
    _ ≅ (walkingCospanOpEquiv.functor ⋙ walkingCospanOpEquiv.inverse) ⋙ (cospan f g).op :=
      isoWhiskerRight walkingCospanOpEquiv.unitIso _
    _ ≅ walkingCospanOpEquiv.functor ⋙ walkingCospanOpEquiv.inverse ⋙ (cospan f g).op :=
      Functor.associator _ _ _
    _ ≅ walkingCospanOpEquiv.functor ⋙ span f.op g.op := isoWhiskerLeft _ (spanOp f g).symm

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The canonical isomorphism relating `Cospan f.op g.op` and `(Span f g).op` -/
@[simps!]
/-
**CategoryTheory.Limits.cospanOp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limit
s`。
形式化陈述：cospanOp {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) : cospan f.op g.op ≅ walkingS
panOpEquiv.inverse ⋙ (span f g).op
参数：f : X ⟶ Y；g : X ⟶ Z。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical isomorphism relating `Cospan f.op g.op` and `(Span f g).op`
-/
def cospanOp {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) :
    cospan f.op g.op ≅ walkingSpanOpEquiv.inverse ⋙ (span f g).op :=
  NatIso.ofComponents (fun
    | .none => .refl _
    | .left => .refl _
    | .right => .refl _)
    (by rintro (_ | _ | _) (_ | _ | _) f <;> cases f <;> cat_disch)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The canonical isomorphism relating `cospan f.unop g.unop` and `(span f g).leftOp` -/
@[simps!]
/-
**CategoryTheory.Limits.cospanUnop** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Lim
its`。
形式化陈述：cospanUnop {X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g : X ⟶ Z) : cospan f.unop g.unop ≅ 
walkingSpanOpEquiv.inverse ⋙ (span f g).leftOp
参数：f : X ⟶ Y；g : X ⟶ Z。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical isomorphism relating `cospan f.unop g.unop` and `(span f g).leftOp
`
-/
def cospanUnop {X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g : X ⟶ Z) :
    cospan f.unop g.unop ≅ walkingSpanOpEquiv.inverse ⋙ (span f g).leftOp :=
  NatIso.ofComponents (fun
    | .none => .refl _
    | .left => .refl _
    | .right => .refl _)
    (by rintro (_ | _ | _) (_ | _ | _) f <;> cases f <;> cat_disch)

/-- The canonical isomorphism relating `(Span f g).op` and `Cospan f.op g.op` -/
@[simps!]
/-
**CategoryTheory.Limits.opSpan** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limits`
。
形式化陈述：opSpan {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) : (span f g).op ≅ walkingSpanOp
Equiv.functor ⋙ cospan f.op g.op
参数：f : X ⟶ Y；g : X ⟶ Z。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical isomorphism relating `(Span f g).op` and `Cospan f.op g.op`
-/
def opSpan {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) :
    (span f g).op ≅ walkingSpanOpEquiv.functor ⋙ cospan f.op g.op :=
  calc
    (span f g).op ≅ 𝟭 _ ⋙ (span f g).op := .refl _
    _ ≅ (walkingSpanOpEquiv.functor ⋙ walkingSpanOpEquiv.inverse) ⋙ (span f g).op :=
      isoWhiskerRight walkingSpanOpEquiv.unitIso _
    _ ≅ walkingSpanOpEquiv.functor ⋙ walkingSpanOpEquiv.inverse ⋙ (span f g).op :=
      Functor.associator _ _ _
    _ ≅ walkingSpanOpEquiv.functor ⋙ cospan f.op g.op := isoWhiskerLeft _ (cospanOp f g).symm

namespace PushoutCocone

/-- The obvious map `PushoutCocone f g → PullbackCone f.unop g.unop` -/
@[simps!]
/-
**CategoryTheory.Limits.PushoutCocone.unop** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Limits.PushoutCocone`。
形式化陈述：unop {X Y Z : Cᵒᵖ} {f : X ⟶ Y} {g : X ⟶ Z} (c : PushoutCocone f g) : Pullb
ackCone f.unop g.unop
参数：c : PushoutCocone f g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The obvious map `PushoutCocone f g → PullbackCone f.unop g.unop`
-/
def unop {X Y Z : Cᵒᵖ} {f : X ⟶ Y} {g : X ⟶ Z} (c : PushoutCocone f g) :
    PullbackCone f.unop g.unop :=
  Cocone.unop ((Cocone.precompose (opCospan f.unop g.unop).hom).obj
    (Cocone.whisker walkingCospanOpEquiv.functor c))

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.Limits.PushoutCocone.unop_fst** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Limits.PushoutCocone`。
形式化陈述：unop_fst {X Y Z : Cᵒᵖ} {f : X ⟶ Y} {g : X ⟶ Z} (c : PushoutCocone f g) : c
.unop.fst = c.inl.unop
参数：c : PushoutCocone f g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.PushoutCocone.unop_π_app`：∀ {C : Type u₁} [inst : 
CategoryTheory.Category.{v₁, u₁} C] {X Y Z : Cᵒᵖ} {f : X ⟶ Y} {g : X ⟶ Z}   (c :
 CategoryTheory.Limits.PushoutCocone…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem unop_fst {X Y Z : Cᵒᵖ} {f : X ⟶ Y} {g : X ⟶ Z} (c : PushoutCocone f g) :
    c.unop.fst = c.inl.unop := by simp

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.Limits.PushoutCocone.unop_snd** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Limits.PushoutCocone`。
形式化陈述：unop_snd {X Y Z : Cᵒᵖ} {f : X ⟶ Y} {g : X ⟶ Z} (c : PushoutCocone f g) : c
.unop.snd = c.inr.unop
参数：c : PushoutCocone f g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.PushoutCocone.unop_π_app`：∀ {C : Type u₁} [inst : 
CategoryTheory.Category.{v₁, u₁} C] {X Y Z : Cᵒᵖ} {f : X ⟶ Y} {g : X ⟶ Z}   (c :
 CategoryTheory.Limits.PushoutCocone…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem unop_snd {X Y Z : Cᵒᵖ} {f : X ⟶ Y} {g : X ⟶ Z} (c : PushoutCocone f g) :
    c.unop.snd = c.inr.unop := by simp

/-- The obvious map `PushoutCocone f.op g.op → PullbackCone f g` -/
@[simps!]
/-
**CategoryTheory.Limits.PushoutCocone.op** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Limits.PushoutCocone`。
形式化陈述：op {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} (c : PushoutCocone f g) : PullbackC
one f.op g.op
参数：c : PushoutCocone f g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The obvious map `PushoutCocone f.op g.op → PullbackCone f g`
-/
def op {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} (c : PushoutCocone f g) : PullbackCone f.op g.op :=
  (Cone.postcompose (cospanOp f g).symm.hom).obj
    (Cone.whisker walkingSpanOpEquiv.inverse (Cocone.op c))

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.Limits.PushoutCocone.op_fst** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Limits.PushoutCocone`。
形式化陈述：op_fst {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} (c : PushoutCocone f g) : c.op.
fst = c.inl.op
参数：c : PushoutCocone f g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.PushoutCocone.op_π_app`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}   (c : Cat
egoryTheory.Limits.PushoutCocone f…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem op_fst {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} (c : PushoutCocone f g) :
    c.op.fst = c.inl.op := by simp

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.Limits.PushoutCocone.op_snd** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Limits.PushoutCocone`。
形式化陈述：op_snd {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} (c : PushoutCocone f g) : c.op.
snd = c.inr.op
参数：c : PushoutCocone f g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.PushoutCocone.op_π_app`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}   (c : Cat
egoryTheory.Limits.PushoutCocone f…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem op_snd {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} (c : PushoutCocone f g) :
    c.op.snd = c.inr.op := by simp

end PushoutCocone

namespace PullbackCone

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- The obvious map `PullbackCone f g → PushoutCocone f.unop g.unop` -/
@[simps!]
/-
**CategoryTheory.Limits.PullbackCone.unop** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Limits.PullbackCone`。
形式化陈述：unop {X Y Z : Cᵒᵖ} {f : X ⟶ Z} {g : Y ⟶ Z} (c : PullbackCone f g) : Pushou
tCocone f.unop g.unop
参数：c : PullbackCone f g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The obvious map `PullbackCone f g → PushoutCocone f.unop g.unop`
-/
def unop {X Y Z : Cᵒᵖ} {f : X ⟶ Z} {g : Y ⟶ Z} (c : PullbackCone f g) :
    PushoutCocone f.unop g.unop :=
  Cone.unop
    ((Cone.postcompose (opSpan f.unop g.unop).symm.hom).obj
      (Cone.whisker walkingSpanOpEquiv.functor c))

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.Limits.PullbackCone.unop_inl** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Limits.PullbackCone`。
形式化陈述：unop_inl {X Y Z : Cᵒᵖ} {f : X ⟶ Z} {g : Y ⟶ Z} (c : PullbackCone f g) : c.
unop.inl = c.fst.unop
参数：c : PullbackCone f g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.PullbackCone.unop_ι_app`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {X Y Z : Cᵒᵖ} {f : X ⟶ Z} {g : Y ⟶ Z}   (c : 
CategoryTheory.Limits.PullbackCone …
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem unop_inl {X Y Z : Cᵒᵖ} {f : X ⟶ Z} {g : Y ⟶ Z} (c : PullbackCone f g) :
    c.unop.inl = c.fst.unop := by simp

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.Limits.PullbackCone.unop_inr** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Limits.PullbackCone`。
形式化陈述：unop_inr {X Y Z : Cᵒᵖ} {f : X ⟶ Z} {g : Y ⟶ Z} (c : PullbackCone f g) : c.
unop.inr = c.snd.unop
参数：c : PullbackCone f g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.PullbackCone.unop_ι_app`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {X Y Z : Cᵒᵖ} {f : X ⟶ Z} {g : Y ⟶ Z}   (c : 
CategoryTheory.Limits.PullbackCone …
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem unop_inr {X Y Z : Cᵒᵖ} {f : X ⟶ Z} {g : Y ⟶ Z} (c : PullbackCone f g) :
    c.unop.inr = c.snd.unop := by simp

/-- The obvious map `PullbackCone f g → PushoutCocone f.op g.op` -/
@[simps!]
/-
**CategoryTheory.Limits.PullbackCone.op** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Limits.PullbackCone`。
形式化陈述：op {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} (c : PullbackCone f g) : PushoutCoc
one f.op g.op
参数：c : PullbackCone f g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The obvious map `PullbackCone f g → PushoutCocone f.op g.op`
-/
def op {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} (c : PullbackCone f g) : PushoutCocone f.op g.op :=
  (Cocone.precompose (spanOp f g).hom).obj
    (Cocone.whisker walkingCospanOpEquiv.inverse (Cone.op c))

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.Limits.PullbackCone.op_inl** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Limits.PullbackCone`。
形式化陈述：op_inl {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} (c : PullbackCone f g) : c.op.i
nl = c.fst.op
参数：c : PullbackCone f g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.PullbackCone.op_ι_app`：∀ {C : Type u₁} [inst : Cat
egoryTheory.Category.{v₁, u₁} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   (c : Cate
goryTheory.Limits.PullbackCone f …
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem op_inl {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} (c : PullbackCone f g) :
    c.op.inl = c.fst.op := by simp

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.Limits.PullbackCone.op_inr** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Limits.PullbackCone`。
形式化陈述：op_inr {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} (c : PullbackCone f g) : c.op.i
nr = c.snd.op
参数：c : PullbackCone f g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.PullbackCone.op_ι_app`：∀ {C : Type u₁} [inst : Cat
egoryTheory.Category.{v₁, u₁} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   (c : Cate
goryTheory.Limits.PullbackCone f …
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem op_inr {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} (c : PullbackCone f g) :
    c.op.inr = c.snd.op := by simp

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- If `c` is a pullback cone, then `c.op.unop` is isomorphic to `c`. -/
/-
**CategoryTheory.Limits.PullbackCone.opUnopIso** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Limits.PullbackCone`。
形式化陈述：opUnopIso {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} (c : PullbackCone f g) : c.o
p.unop ≅ c
参数：c : PullbackCone f g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `c` is a pullback cone, then `c.op.unop` is isomorphic to `c`.
-/
def opUnopIso {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} (c : PullbackCone f g) : c.op.unop ≅ c :=
  PullbackCone.ext (Iso.refl _) (by simp) (by simp)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- If `c` is a pullback cone in `Cᵒᵖ`, then `c.unop.op` is isomorphic to `c`. -/
/-
**CategoryTheory.Limits.PullbackCone.unopOpIso** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Limits.PullbackCone`。
形式化陈述：unopOpIso {X Y Z : Cᵒᵖ} {f : X ⟶ Z} {g : Y ⟶ Z} (c : PullbackCone f g) : c
.unop.op ≅ c
参数：c : PullbackCone f g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `c` is a pullback cone in `Cᵒᵖ`, then `c.unop.op` is isomorphic to `c`.
-/
def unopOpIso {X Y Z : Cᵒᵖ} {f : X ⟶ Z} {g : Y ⟶ Z} (c : PullbackCone f g) : c.unop.op ≅ c :=
  PullbackCone.ext (Iso.refl _) (by simp) (by simp)

end PullbackCone

namespace PushoutCocone

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- If `c` is a pushout cocone, then `c.op.unop` is isomorphic to `c`. -/
/-
**CategoryTheory.Limits.PushoutCocone.opUnopIso** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Limits.PushoutCocone`。
形式化陈述：opUnopIso {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} (c : PushoutCocone f g) : c.
op.unop ≅ c
参数：c : PushoutCocone f g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `c` is a pushout cocone, then `c.op.unop` is isomorphic to `c`.
-/
def opUnopIso {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} (c : PushoutCocone f g) : c.op.unop ≅ c :=
  PushoutCocone.ext (Iso.refl _) (by simp) (by simp)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- If `c` is a pushout cocone in `Cᵒᵖ`, then `c.unop.op` is isomorphic to `c`. -/
/-
**CategoryTheory.Limits.PushoutCocone.unopOpIso** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Limits.PushoutCocone`。
形式化陈述：unopOpIso {X Y Z : Cᵒᵖ} {f : X ⟶ Y} {g : X ⟶ Z} (c : PushoutCocone f g) : 
c.unop.op ≅ c
参数：c : PushoutCocone f g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `c` is a pushout cocone in `Cᵒᵖ`, then `c.unop.op` is isomorphic to `c`.
-/
def unopOpIso {X Y Z : Cᵒᵖ} {f : X ⟶ Y} {g : X ⟶ Z} (c : PushoutCocone f g) : c.unop.op ≅ c :=
  PushoutCocone.ext (Iso.refl _) (by simp) (by simp)

/-- A pushout cone is a colimit cocone if and only if the corresponding pullback cone
in the opposite category is a limit cone. -/
noncomputable -- just for performance; compilation takes several seconds
/-
**CategoryTheory.Limits.PushoutCocone.isColimitEquivIsLimitOp** 是 Mathlib 中的一个定义
，位于命名空间 `CategoryTheory.Limits.PushoutCocone`。
形式化陈述：isColimitEquivIsLimitOp {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} (c : PushoutCo
cone f g) : IsColimit c ≃ IsLimit c.op
参数：c : PushoutCocone f g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def isColimitEquivIsLimitOp {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} (c : PushoutCocone f g) :
    IsColimit c ≃ IsLimit c.op := by
  apply equivOfSubsingletonOfSubsingleton
  · intro h
    exact (IsLimit.postcomposeHomEquiv _ _).invFun
      ((IsLimit.whiskerEquivalenceEquiv walkingSpanOpEquiv.symm).toFun h.op)
  · intro h
    exact (IsColimit.equivIsoColimit c.opUnopIso).toFun
      (((IsLimit.postcomposeHomEquiv _ _).invFun
        ((IsLimit.whiskerEquivalenceEquiv _).toFun h)).unop)

/-- A pushout cone is a colimit cocone in `Cᵒᵖ` if and only if the corresponding pullback cone
in `C` is a limit cone. -/
noncomputable -- just for performance; compilation takes several seconds
/-
**CategoryTheory.Limits.PushoutCocone.isColimitEquivIsLimitUnop** 是 Mathlib 中的一个
定义，位于命名空间 `CategoryTheory.Limits.PushoutCocone`。
形式化陈述：isColimitEquivIsLimitUnop {X Y Z : Cᵒᵖ} {f : X ⟶ Y} {g : X ⟶ Z} (c : Pusho
utCocone f g) : IsColimit c ≃ IsLimit c.unop
参数：c : PushoutCocone f g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def isColimitEquivIsLimitUnop {X Y Z : Cᵒᵖ} {f : X ⟶ Y} {g : X ⟶ Z} (c : PushoutCocone f g) :
    IsColimit c ≃ IsLimit c.unop := by
  apply equivOfSubsingletonOfSubsingleton
  · intro h
    exact ((IsColimit.precomposeHomEquiv _ _).invFun
      ((IsColimit.whiskerEquivalenceEquiv _).toFun h)).unop
  · intro h
    exact (IsColimit.equivIsoColimit c.unopOpIso).toFun
      ((IsColimit.precomposeHomEquiv _ _).invFun
      ((IsColimit.whiskerEquivalenceEquiv walkingCospanOpEquiv.symm).toFun h.op))

end PushoutCocone

namespace PullbackCone

/-- A pullback cone is a limit cone if and only if the corresponding pushout cocone
in the opposite category is a colimit cocone. -/
/-
**CategoryTheory.Limits.PullbackCone.isLimitEquivIsColimitOp** 是 Mathlib 中的一个定义，
位于命名空间 `CategoryTheory.Limits.PullbackCone`。
形式化陈述：isLimitEquivIsColimitOp {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} (c : PullbackC
one f g) : IsLimit c ≃ IsColimit c.op
参数：c : PullbackCone f g。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
A pullback cone is a limit cone if and only if the corresponding pushout cocone
in the opposite category is a colimit cocone.
-/
def isLimitEquivIsColimitOp {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} (c : PullbackCone f g) :
    IsLimit c ≃ IsColimit c.op :=
  (IsLimit.equivIsoLimit c.opUnopIso).symm.trans c.op.isColimitEquivIsLimitUnop.symm

/-- A pullback cone is a limit cone in `Cᵒᵖ` if and only if the corresponding pushout cocone
in `C` is a colimit cocone. -/
/-
**CategoryTheory.Limits.PullbackCone.isLimitEquivIsColimitUnop** 是 Mathlib 中的一个定
义，位于命名空间 `CategoryTheory.Limits.PullbackCone`。
形式化陈述：isLimitEquivIsColimitUnop {X Y Z : Cᵒᵖ} {f : X ⟶ Z} {g : Y ⟶ Z} (c : Pullb
ackCone f g) : IsLimit c ≃ IsColimit c.unop
参数：c : PullbackCone f g。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
A pullback cone is a limit cone in `Cᵒᵖ` if and only if the corresponding pushou
t cocone
in `C` is a colimit cocone.
-/
def isLimitEquivIsColimitUnop {X Y Z : Cᵒᵖ} {f : X ⟶ Z} {g : Y ⟶ Z} (c : PullbackCone f g) :
    IsLimit c ≃ IsColimit c.unop :=
  (IsLimit.equivIsoLimit c.unopOpIso).symm.trans c.unop.isColimitEquivIsLimitOp.symm

end PullbackCone

section Pullback

open Opposite

@[simp]
/-
**CategoryTheory.Limits.hasPushout_op_iff_hasPullback** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Limits`。
形式化陈述：hasPushout_op_iff_hasPullback {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) : HasPus
hout f.op g.op ↔ HasPullback f g
参数：f : X ⟶ Z；g : Y ⟶ Z。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.HasPushout.eq_1`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z),   CategoryTheory.Li
mits.HasPushout f g = Categ…
· 使用定理 `CategoryTheory.Limits.hasColimit_iff_of_iso`：∀ {J : Type u₁} [inst : Cat
egoryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.
{v, u} C]   {F G : CategoryTheory…
· 使用引理 `CategoryTheory.Limits.hasColimit_inverse_equivalence_comp_iff`：hasColimi
t_inverse_equivalence_comp_iff (e : J ≌ K) : HasColimit (e.inverse ⋙ F) ↔ HasCol
imit F
· 使用引理 `CategoryTheory.Limits.hasColimit_op_iff_hasLimit`：hasColimit_op_iff_hasL
imit {F : J ⥤ C} : HasColimit F.op ↔ HasLimit F
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma hasPushout_op_iff_hasPullback {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasPushout f.op g.op ↔ HasPullback f g := by
  rw [HasPushout, hasColimit_iff_of_iso (spanOp f g), hasColimit_inverse_equivalence_comp_iff,
    hasColimit_op_iff_hasLimit]

@[simp]
/-
**CategoryTheory.Limits.hasPushout_unop_iff_hasPullback** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.Limits`。
形式化陈述：hasPushout_unop_iff_hasPullback {X Y Z : Cᵒᵖ} (f : X ⟶ Z) (g : Y ⟶ Z) : Ha
sPushout f.unop g.unop ↔ HasPullback f g
参数：f : X ⟶ Z；g : Y ⟶ Z。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.HasPushout.eq_1`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z),   CategoryTheory.Li
mits.HasPushout f g = Categ…
· 使用定理 `CategoryTheory.Limits.hasColimit_iff_of_iso`：∀ {J : Type u₁} [inst : Cat
egoryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.
{v, u} C]   {F G : CategoryTheory…
· 使用引理 `CategoryTheory.Limits.hasColimit_inverse_equivalence_comp_iff`：hasColimi
t_inverse_equivalence_comp_iff (e : J ≌ K) : HasColimit (e.inverse ⋙ F) ↔ HasCol
imit F
· 使用引理 `CategoryTheory.Limits.hasColimit_leftOp_iff_hasLimit`：hasColimit_leftOp_
iff_hasLimit {F : J ⥤ Cᵒᵖ} : HasColimit F.leftOp ↔ HasLimit F
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma hasPushout_unop_iff_hasPullback {X Y Z : Cᵒᵖ} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasPushout f.unop g.unop ↔ HasPullback f g := by
  rw [HasPushout, hasColimit_iff_of_iso (spanUnop f g), hasColimit_inverse_equivalence_comp_iff,
    hasColimit_leftOp_iff_hasLimit]
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] : HasPushout f.op g.op := by
  rwa [hasPushout_op_iff_hasPullback]
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y Z : Cᵒᵖ} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] : HasPushout f.unop g.unop := by
  rwa [hasPushout_unop_iff_hasPullback]

/-- The pullback of `f` and `g` in `C` is isomorphic to the pushout of
`f.op` and `g.op` in `Cᵒᵖ`. -/
/-
**CategoryTheory.Limits.pullbackIsoUnopPushout** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Limits`。
形式化陈述：pullbackIsoUnopPushout {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [h : HasPullbac
k f g] : pullback f g ≅ unop (pushout f.op g.op)
参数：f : X ⟶ Z；g : Y ⟶ Z。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasPushoutOppositeOpOfHasPullback`：∀ {C : Type
 u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X Y Z : C} (f : X ⟶ Z) (g : Y 
⟶ Z)   [CategoryTheory.Limits.HasPullback f g], C…

--- 原说明 ---
The pullback of `f` and `g` in `C` is isomorphic to the pushout of
`f.op` and `g.op` in `Cᵒᵖ`.
-/
noncomputable def pullbackIsoUnopPushout {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [h : HasPullback f g] :
    pullback f g ≅ unop (pushout f.op g.op) :=
  IsLimit.conePointUniqueUpToIso (@limit.isLimit _ _ _ _ _ h)
    ((PushoutCocone.isColimitEquivIsLimitUnop _) (colimit.isColimit (span f.op g.op)))

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.pullbackIsoUnopPushout_inv_fst** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.Limits`。
形式化陈述：pullbackIsoUnopPushout_inv_fst {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPul
lback f g] : (pullbackIsoUnopPushout f g).inv ≫ pullback.fst f g = (pushout.inl 
f.op g.op).unop
参数：f : X ⟶ Z；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.instHasPushoutOppositeOpOfHasPullback`：∀ {C : Type
 u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X Y Z : C} (f : X ⟶ Z) (g : Y 
⟶ Z)   [CategoryTheory.Limits.HasPullback f g], C…
· 使用定理 `CategoryTheory.Limits.IsLimit.conePointUniqueUpToIso_inv_comp`：conePoint
UniqueUpToIso_inv_comp {s t : Cone F} (P : IsLimit s) (Q : IsLimit t) (j : J) : 
(conePointUniqueUpToIso P Q).inv ≫ s.π.app j = t.π.…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.PushoutCocone.unop_π_app`：∀ {C : Type u₁} [inst : 
CategoryTheory.Category.{v₁, u₁} C] {X Y Z : Cᵒᵖ} {f : X ⟶ Y} {g : X ⟶ Z}   (c :
 CategoryTheory.Limits.PushoutCocone…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pullbackIsoUnopPushout_inv_fst {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] :
    (pullbackIsoUnopPushout f g).inv ≫ pullback.fst f g = (pushout.inl f.op g.op).unop :=
  (IsLimit.conePointUniqueUpToIso_inv_comp _ _ _).trans (by simp [unop_id (X := { unop := X })])

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.pullbackIsoUnopPushout_inv_snd** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.Limits`。
形式化陈述：pullbackIsoUnopPushout_inv_snd {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPul
lback f g] : (pullbackIsoUnopPushout f g).inv ≫ pullback.snd f g = (pushout.inr 
f.op g.op).unop
参数：f : X ⟶ Z；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.instHasPushoutOppositeOpOfHasPullback`：∀ {C : Type
 u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X Y Z : C} (f : X ⟶ Z) (g : Y 
⟶ Z)   [CategoryTheory.Limits.HasPullback f g], C…
· 使用定理 `CategoryTheory.Limits.IsLimit.conePointUniqueUpToIso_inv_comp`：conePoint
UniqueUpToIso_inv_comp {s t : Cone F} (P : IsLimit s) (Q : IsLimit t) (j : J) : 
(conePointUniqueUpToIso P Q).inv ≫ s.π.app j = t.π.…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.PushoutCocone.unop_π_app`：∀ {C : Type u₁} [inst : 
CategoryTheory.Category.{v₁, u₁} C] {X Y Z : Cᵒᵖ} {f : X ⟶ Y} {g : X ⟶ Z}   (c :
 CategoryTheory.Limits.PushoutCocone…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pullbackIsoUnopPushout_inv_snd {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] :
    (pullbackIsoUnopPushout f g).inv ≫ pullback.snd f g = (pushout.inr f.op g.op).unop :=
  (IsLimit.conePointUniqueUpToIso_inv_comp _ _ _).trans (by simp [unop_id (X := { unop := Y })])

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.pullbackIsoUnopPushout_hom_inl** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.Limits`。
形式化陈述：pullbackIsoUnopPushout_hom_inl {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPul
lback f g] : pushout.inl f.op g.op ≫ (pullbackIsoUnopPushout f g).hom.op = (pull
back.fst f g).op
参数：f : X ⟶ Z；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quiver.Hom.unop_inj`：Quiver.Hom.unop_inj {X Y : Cᵒᵖ} : Function.Injectiv
e (Quiver.Hom.unop : (X ⟶ Y) -> (Opposite.unop Y ⟶ Opposite.unop X))
· 使用定理 `CategoryTheory.Limits.instHasPushoutOppositeOpOfHasPullback`：∀ {C : Type
 u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X Y Z : C} (f : X ⟶ Z) (g : Y 
⟶ Z)   [CategoryTheory.Limits.HasPullback f g], C…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pullbackIsoUnopPushout_hom_inl {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] :
    pushout.inl f.op g.op ≫ (pullbackIsoUnopPushout f g).hom.op = (pullback.fst f g).op :=
  Quiver.Hom.unop_inj <| by simp [← pullbackIsoUnopPushout_inv_fst]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.pullbackIsoUnopPushout_hom_inr** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.Limits`。
形式化陈述：pullbackIsoUnopPushout_hom_inr {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPul
lback f g] : pushout.inr f.op g.op ≫ (pullbackIsoUnopPushout f g).hom.op = (pull
back.snd f g).op
参数：f : X ⟶ Z；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quiver.Hom.unop_inj`：Quiver.Hom.unop_inj {X Y : Cᵒᵖ} : Function.Injectiv
e (Quiver.Hom.unop : (X ⟶ Y) -> (Opposite.unop Y ⟶ Opposite.unop X))
· 使用定理 `CategoryTheory.Limits.instHasPushoutOppositeOpOfHasPullback`：∀ {C : Type
 u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X Y Z : C} (f : X ⟶ Z) (g : Y 
⟶ Z)   [CategoryTheory.Limits.HasPullback f g], C…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pullbackIsoUnopPushout_hom_inr {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] :
    pushout.inr f.op g.op ≫ (pullbackIsoUnopPushout f g).hom.op = (pullback.snd f g).op :=
  Quiver.Hom.unop_inj <| by simp [← pullbackIsoUnopPushout_inv_snd]

/-- The pullback of `f` and `g` in `Cᵒᵖ` is isomorphic to the pushout of
`f.unop` and `g.unop` in `C`. -/
/-
**CategoryTheory.Limits.pullbackIsoOpPushout** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Limits`。
形式化陈述：pullbackIsoOpPushout {X Y Z : Cᵒᵖ} (f : X ⟶ Z) (g : Y ⟶ Z) [h : HasPullbac
k f g] : pullback f g ≅ op (pushout f.unop g.unop)
参数：f : X ⟶ Z；g : Y ⟶ Z。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasPushoutUnopOfHasPullbackOpposite`：∀ {C : Ty
pe u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X Y Z : Cᵒᵖ} (f : X ⟶ Z) (g 
: Y ⟶ Z)   [CategoryTheory.Limits.HasPullback f g],…

--- 原说明 ---
The pullback of `f` and `g` in `Cᵒᵖ` is isomorphic to the pushout of
`f.unop` and `g.unop` in `C`.
-/
noncomputable def pullbackIsoOpPushout {X Y Z : Cᵒᵖ} (f : X ⟶ Z) (g : Y ⟶ Z) [h : HasPullback f g] :
    pullback f g ≅ op (pushout f.unop g.unop) :=
  IsLimit.conePointUniqueUpToIso (@limit.isLimit _ _ _ _ _ h)
    ((PushoutCocone.isColimitEquivIsLimitOp _) (colimit.isColimit (span f.unop g.unop)))

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.pullbackIsoOpPushout_inv_fst** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.Limits`。
形式化陈述：pullbackIsoOpPushout_inv_fst {X Y Z : Cᵒᵖ} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPul
lback f g] : (pullbackIsoOpPushout f g).inv ≫ pullback.fst f g = (pushout.inl f.
unop g.unop).op
参数：f : X ⟶ Z；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.instHasPushoutUnopOfHasPullbackOpposite`：∀ {C : Ty
pe u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X Y Z : Cᵒᵖ} (f : X ⟶ Z) (g 
: Y ⟶ Z)   [CategoryTheory.Limits.HasPullback f g],…
· 使用定理 `CategoryTheory.Limits.IsLimit.conePointUniqueUpToIso_inv_comp`：conePoint
UniqueUpToIso_inv_comp {s t : Cone F} (P : IsLimit s) (Q : IsLimit t) (j : J) : 
(conePointUniqueUpToIso P Q).inv ≫ s.π.app j = t.π.…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.PushoutCocone.op_π_app`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}   (c : Cat
egoryTheory.Limits.PushoutCocone f…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pullbackIsoOpPushout_inv_fst {X Y Z : Cᵒᵖ} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] :
    (pullbackIsoOpPushout f g).inv ≫ pullback.fst f g = (pushout.inl f.unop g.unop).op :=
  (IsLimit.conePointUniqueUpToIso_inv_comp _ _ _).trans (by simp)

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.pullbackIsoOpPushout_inv_snd** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.Limits`。
形式化陈述：pullbackIsoOpPushout_inv_snd {X Y Z : Cᵒᵖ} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPul
lback f g] : (pullbackIsoOpPushout f g).inv ≫ pullback.snd f g = (pushout.inr f.
unop g.unop).op
参数：f : X ⟶ Z；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.instHasPushoutUnopOfHasPullbackOpposite`：∀ {C : Ty
pe u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X Y Z : Cᵒᵖ} (f : X ⟶ Z) (g 
: Y ⟶ Z)   [CategoryTheory.Limits.HasPullback f g],…
· 使用定理 `CategoryTheory.Limits.IsLimit.conePointUniqueUpToIso_inv_comp`：conePoint
UniqueUpToIso_inv_comp {s t : Cone F} (P : IsLimit s) (Q : IsLimit t) (j : J) : 
(conePointUniqueUpToIso P Q).inv ≫ s.π.app j = t.π.…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.PushoutCocone.op_π_app`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}   (c : Cat
egoryTheory.Limits.PushoutCocone f…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pullbackIsoOpPushout_inv_snd {X Y Z : Cᵒᵖ} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] :
    (pullbackIsoOpPushout f g).inv ≫ pullback.snd f g = (pushout.inr f.unop g.unop).op :=
  (IsLimit.conePointUniqueUpToIso_inv_comp _ _ _).trans (by simp)

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.pullbackIsoOpPushout_hom_inl** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.Limits`。
形式化陈述：pullbackIsoOpPushout_hom_inl {X Y Z : Cᵒᵖ} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPul
lback f g] : pushout.inl _ _ ≫ (pullbackIsoOpPushout f g).hom.unop = (pullback.f
st f g).unop
参数：f : X ⟶ Z；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quiver.Hom.op_inj`：Quiver.Hom.op_inj {X Y : C} : Function.Injective (Qui
ver.Hom.op : (X ⟶ Y) -> (Opposite.op Y ⟶ Opposite.op X))
· 使用定理 `CategoryTheory.Limits.instHasPushoutUnopOfHasPullbackOpposite`：∀ {C : Ty
pe u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X Y Z : Cᵒᵖ} (f : X ⟶ Z) (g 
: Y ⟶ Z)   [CategoryTheory.Limits.HasPullback f g],…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pullbackIsoOpPushout_hom_inl {X Y Z : Cᵒᵖ} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] :
    pushout.inl _ _ ≫ (pullbackIsoOpPushout f g).hom.unop = (pullback.fst f g).unop :=
  Quiver.Hom.op_inj <| by simp [← pullbackIsoOpPushout_inv_fst]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.pullbackIsoOpPushout_hom_inr** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.Limits`。
形式化陈述：pullbackIsoOpPushout_hom_inr {X Y Z : Cᵒᵖ} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPul
lback f g] : pushout.inr _ _ ≫ (pullbackIsoOpPushout f g).hom.unop = (pullback.s
nd f g).unop
参数：f : X ⟶ Z；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quiver.Hom.op_inj`：Quiver.Hom.op_inj {X Y : C} : Function.Injective (Qui
ver.Hom.op : (X ⟶ Y) -> (Opposite.op Y ⟶ Opposite.op X))
· 使用定理 `CategoryTheory.Limits.instHasPushoutUnopOfHasPullbackOpposite`：∀ {C : Ty
pe u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X Y Z : Cᵒᵖ} (f : X ⟶ Z) (g 
: Y ⟶ Z)   [CategoryTheory.Limits.HasPullback f g],…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pullbackIsoOpPushout_hom_inr {X Y Z : Cᵒᵖ} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] :
    pushout.inr _ _ ≫ (pullbackIsoOpPushout f g).hom.unop = (pullback.snd f g).unop :=
  Quiver.Hom.op_inj <| by simp [← pullbackIsoOpPushout_inv_snd]

end Pullback

section Pushout

@[simp]
/-
**CategoryTheory.Limits.hasPullback_op_iff_hasPushout** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Limits`。
形式化陈述：hasPullback_op_iff_hasPushout {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) : HasPul
lback f.op g.op ↔ HasPushout f g
参数：f : X ⟶ Y；g : X ⟶ Z。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.HasPullback.eq_1`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z),   CategoryTheory.L
imits.HasPullback f g = Cate…
· 使用定理 `CategoryTheory.Limits.hasLimit_iff_of_iso`：hasLimit_iff_of_iso {F G : J 
⥤ C} (α : F ≅ G) : HasLimit F ↔ HasLimit G
· 使用引理 `CategoryTheory.Limits.hasLimit_inverse_equivalence_comp_iff`：hasLimit_in
verse_equivalence_comp_iff (e : J ≌ K) : HasLimit (e.inverse ⋙ F) ↔ HasLimit F
· 使用引理 `CategoryTheory.Limits.hasLimit_op_iff_hasColimit`：hasLimit_op_iff_hasCol
imit {F : J ⥤ C} : HasLimit F.op ↔ HasColimit F
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma hasPullback_op_iff_hasPushout {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) :
    HasPullback f.op g.op ↔ HasPushout f g := by
  rw [HasPullback, hasLimit_iff_of_iso (cospanOp f g), hasLimit_inverse_equivalence_comp_iff,
    hasLimit_op_iff_hasColimit]

@[simp]
/-
**CategoryTheory.Limits.hasPullback_unop_iff_hasPushout** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.Limits`。
形式化陈述：hasPullback_unop_iff_hasPushout {X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g : X ⟶ Z) : Ha
sPullback f.unop g.unop ↔ HasPushout f g
参数：f : X ⟶ Y；g : X ⟶ Z。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.HasPullback.eq_1`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z),   CategoryTheory.L
imits.HasPullback f g = Cate…
· 使用定理 `CategoryTheory.Limits.hasLimit_iff_of_iso`：hasLimit_iff_of_iso {F G : J 
⥤ C} (α : F ≅ G) : HasLimit F ↔ HasLimit G
· 使用引理 `CategoryTheory.Limits.hasLimit_inverse_equivalence_comp_iff`：hasLimit_in
verse_equivalence_comp_iff (e : J ≌ K) : HasLimit (e.inverse ⋙ F) ↔ HasLimit F
· 使用引理 `CategoryTheory.Limits.hasLimit_leftOp_iff_hasColimit`：hasLimit_leftOp_if
f_hasColimit {F : J ⥤ Cᵒᵖ} : HasLimit F.leftOp ↔ HasColimit F
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma hasPullback_unop_iff_hasPushout {X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g : X ⟶ Z) :
    HasPullback f.unop g.unop ↔ HasPushout f g := by
  rw [HasPullback, hasLimit_iff_of_iso (cospanUnop f g), hasLimit_inverse_equivalence_comp_iff,
    hasLimit_leftOp_iff_hasColimit]
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g] : HasPullback f.op g.op := by
  rwa [hasPullback_op_iff_hasPushout]
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g] : HasPullback f.unop g.unop := by
  rwa [hasPullback_unop_iff_hasPushout]

/-- The pushout of `f` and `g` in `C` is isomorphic to the pullback of
`f.op` and `g.op` in `Cᵒᵖ`. -/
/-
**CategoryTheory.Limits.pushoutIsoUnopPullback** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Limits`。
形式化陈述：pushoutIsoUnopPullback {X Y Z : C} (f : X ⟶ Z) (g : X ⟶ Y) [h : HasPushout
 f g] : pushout f g ≅ unop (pullback f.op g.op)
参数：f : X ⟶ Z；g : X ⟶ Y。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasPullbackOppositeOpOfHasPushout`：∀ {C : Type
 u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X Y Z : C} (f : X ⟶ Y) (g : X 
⟶ Z)   [CategoryTheory.Limits.HasPushout f g], Ca…

--- 原说明 ---
The pushout of `f` and `g` in `C` is isomorphic to the pullback of
`f.op` and `g.op` in `Cᵒᵖ`.
-/
noncomputable def pushoutIsoUnopPullback {X Y Z : C} (f : X ⟶ Z) (g : X ⟶ Y) [h : HasPushout f g] :
    pushout f g ≅ unop (pullback f.op g.op) :=
  IsColimit.coconePointUniqueUpToIso (@colimit.isColimit _ _ _ _ _ h)
    ((PullbackCone.isLimitEquivIsColimitUnop _) (limit.isLimit (cospan f.op g.op)))

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.pushoutIsoUnopPullback_inl_hom** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.Limits`。
形式化陈述：pushoutIsoUnopPullback_inl_hom {X Y Z : C} (f : X ⟶ Z) (g : X ⟶ Y) [HasPus
hout f g] : pushout.inl _ _ ≫ (pushoutIsoUnopPullback f g).hom = (pullback.fst f
.op g.op).unop
参数：f : X ⟶ Z；g : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.instHasPullbackOppositeOpOfHasPushout`：∀ {C : Type
 u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X Y Z : C} (f : X ⟶ Y) (g : X 
⟶ Z)   [CategoryTheory.Limits.HasPushout f g], Ca…
· 使用定理 `CategoryTheory.Limits.IsColimit.comp_coconePointUniqueUpToIso_hom`：∀ {J 
: Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : C
ategoryTheory.Category.{v₃, u₃} C]   {F : CategoryTheor…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.PullbackCone.unop_ι_app`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {X Y Z : Cᵒᵖ} {f : X ⟶ Z} {g : Y ⟶ Z}   (c : 
CategoryTheory.Limits.PullbackCone …
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pushoutIsoUnopPullback_inl_hom {X Y Z : C} (f : X ⟶ Z) (g : X ⟶ Y) [HasPushout f g] :
    pushout.inl _ _ ≫ (pushoutIsoUnopPullback f g).hom = (pullback.fst f.op g.op).unop :=
  (IsColimit.comp_coconePointUniqueUpToIso_hom _ _ _).trans (by simp)

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.pushoutIsoUnopPullback_inr_hom** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.Limits`。
形式化陈述：pushoutIsoUnopPullback_inr_hom {X Y Z : C} (f : X ⟶ Z) (g : X ⟶ Y) [HasPus
hout f g] : pushout.inr _ _ ≫ (pushoutIsoUnopPullback f g).hom = (pullback.snd f
.op g.op).unop
参数：f : X ⟶ Z；g : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.instHasPullbackOppositeOpOfHasPushout`：∀ {C : Type
 u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X Y Z : C} (f : X ⟶ Y) (g : X 
⟶ Z)   [CategoryTheory.Limits.HasPushout f g], Ca…
· 使用定理 `CategoryTheory.Limits.IsColimit.comp_coconePointUniqueUpToIso_hom`：∀ {J 
: Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : C
ategoryTheory.Category.{v₃, u₃} C]   {F : CategoryTheor…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.PullbackCone.unop_ι_app`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {X Y Z : Cᵒᵖ} {f : X ⟶ Z} {g : Y ⟶ Z}   (c : 
CategoryTheory.Limits.PullbackCone …
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pushoutIsoUnopPullback_inr_hom {X Y Z : C} (f : X ⟶ Z) (g : X ⟶ Y) [HasPushout f g] :
    pushout.inr _ _ ≫ (pushoutIsoUnopPullback f g).hom = (pullback.snd f.op g.op).unop :=
  (IsColimit.comp_coconePointUniqueUpToIso_hom _ _ _).trans (by simp)

@[simp]
/-
**CategoryTheory.Limits.pushoutIsoUnopPullback_inv_fst** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.Limits`。
形式化陈述：pushoutIsoUnopPullback_inv_fst {X Y Z : C} (f : X ⟶ Z) (g : X ⟶ Y) [HasPus
hout f g] : (pushoutIsoUnopPullback f g).inv.op ≫ pullback.fst f.op g.op = (push
out.inl f g).op
参数：f : X ⟶ Z；g : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quiver.Hom.unop_inj`：Quiver.Hom.unop_inj {X Y : Cᵒᵖ} : Function.Injectiv
e (Quiver.Hom.unop : (X ⟶ Y) -> (Opposite.unop Y ⟶ Opposite.unop X))
· 使用定理 `CategoryTheory.Limits.instHasPullbackOppositeOpOfHasPushout`：∀ {C : Type
 u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X Y Z : C} (f : X ⟶ Y) (g : X 
⟶ Z)   [CategoryTheory.Limits.HasPushout f g], Ca…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pushoutIsoUnopPullback_inv_fst {X Y Z : C} (f : X ⟶ Z) (g : X ⟶ Y) [HasPushout f g] :
    (pushoutIsoUnopPullback f g).inv.op ≫ pullback.fst f.op g.op = (pushout.inl f g).op :=
  Quiver.Hom.unop_inj <| by simp [← pushoutIsoUnopPullback_inl_hom]

@[simp]
/-
**CategoryTheory.Limits.pushoutIsoUnopPullback_inv_snd** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.Limits`。
形式化陈述：pushoutIsoUnopPullback_inv_snd {X Y Z : C} (f : X ⟶ Z) (g : X ⟶ Y) [HasPus
hout f g] : (pushoutIsoUnopPullback f g).inv.op ≫ pullback.snd f.op g.op = (push
out.inr f g).op
参数：f : X ⟶ Z；g : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quiver.Hom.unop_inj`：Quiver.Hom.unop_inj {X Y : Cᵒᵖ} : Function.Injectiv
e (Quiver.Hom.unop : (X ⟶ Y) -> (Opposite.unop Y ⟶ Opposite.unop X))
· 使用定理 `CategoryTheory.Limits.instHasPullbackOppositeOpOfHasPushout`：∀ {C : Type
 u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X Y Z : C} (f : X ⟶ Y) (g : X 
⟶ Z)   [CategoryTheory.Limits.HasPushout f g], Ca…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pushoutIsoUnopPullback_inv_snd {X Y Z : C} (f : X ⟶ Z) (g : X ⟶ Y) [HasPushout f g] :
    (pushoutIsoUnopPullback f g).inv.op ≫ pullback.snd f.op g.op = (pushout.inr f g).op :=
  Quiver.Hom.unop_inj <| by simp [← pushoutIsoUnopPullback_inr_hom]

/-- The pushout of `f` and `g` in `Cᵒᵖ` is isomorphic to the pullback of
`f.unop` and `g.unop` in `C`. -/
/-
**CategoryTheory.Limits.pushoutIsoOpPullback** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Limits`。
形式化陈述：pushoutIsoOpPullback {X Y Z : Cᵒᵖ} (f : X ⟶ Z) (g : X ⟶ Y) [h : HasPushout
 f g] : pushout f g ≅ op (pullback f.unop g.unop)
参数：f : X ⟶ Z；g : X ⟶ Y。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasPullbackUnopOfHasPushoutOpposite`：∀ {C : Ty
pe u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g 
: X ⟶ Z)   [CategoryTheory.Limits.HasPushout f g], …

--- 原说明 ---
The pushout of `f` and `g` in `Cᵒᵖ` is isomorphic to the pullback of
`f.unop` and `g.unop` in `C`.
-/
noncomputable def pushoutIsoOpPullback {X Y Z : Cᵒᵖ} (f : X ⟶ Z) (g : X ⟶ Y) [h : HasPushout f g] :
    pushout f g ≅ op (pullback f.unop g.unop) :=
  IsColimit.coconePointUniqueUpToIso (@colimit.isColimit _ _ _ _ _ h)
    ((PullbackCone.isLimitEquivIsColimitOp _) (limit.isLimit (cospan f.unop g.unop)))

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.pushoutIsoOpPullback_inl_hom** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.Limits`。
形式化陈述：pushoutIsoOpPullback_inl_hom {X Y Z : Cᵒᵖ} (f : X ⟶ Z) (g : X ⟶ Y) [HasPus
hout f g] : pushout.inl _ _ ≫ (pushoutIsoOpPullback f g).hom = (pullback.fst f.u
nop g.unop).op
参数：f : X ⟶ Z；g : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.instHasPullbackUnopOfHasPushoutOpposite`：∀ {C : Ty
pe u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g 
: X ⟶ Z)   [CategoryTheory.Limits.HasPushout f g], …
· 使用定理 `CategoryTheory.Limits.IsColimit.comp_coconePointUniqueUpToIso_hom`：∀ {J 
: Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : C
ategoryTheory.Category.{v₃, u₃} C]   {F : CategoryTheor…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.PullbackCone.op_ι_app`：∀ {C : Type u₁} [inst : Cat
egoryTheory.Category.{v₁, u₁} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   (c : Cate
goryTheory.Limits.PullbackCone f …
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pushoutIsoOpPullback_inl_hom {X Y Z : Cᵒᵖ} (f : X ⟶ Z) (g : X ⟶ Y) [HasPushout f g] :
    pushout.inl _ _ ≫ (pushoutIsoOpPullback f g).hom = (pullback.fst f.unop g.unop).op :=
  (IsColimit.comp_coconePointUniqueUpToIso_hom _ _ _).trans (by simp)

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.pushoutIsoOpPullback_inr_hom** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.Limits`。
形式化陈述：pushoutIsoOpPullback_inr_hom {X Y Z : Cᵒᵖ} (f : X ⟶ Z) (g : X ⟶ Y) [HasPus
hout f g] : pushout.inr _ _ ≫ (pushoutIsoOpPullback f g).hom = (pullback.snd f.u
nop g.unop).op
参数：f : X ⟶ Z；g : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.instHasPullbackUnopOfHasPushoutOpposite`：∀ {C : Ty
pe u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g 
: X ⟶ Z)   [CategoryTheory.Limits.HasPushout f g], …
· 使用定理 `CategoryTheory.Limits.IsColimit.comp_coconePointUniqueUpToIso_hom`：∀ {J 
: Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : C
ategoryTheory.Category.{v₃, u₃} C]   {F : CategoryTheor…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.PullbackCone.op_ι_app`：∀ {C : Type u₁} [inst : Cat
egoryTheory.Category.{v₁, u₁} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   (c : Cate
goryTheory.Limits.PullbackCone f …
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pushoutIsoOpPullback_inr_hom {X Y Z : Cᵒᵖ} (f : X ⟶ Z) (g : X ⟶ Y) [HasPushout f g] :
    pushout.inr _ _ ≫ (pushoutIsoOpPullback f g).hom = (pullback.snd f.unop g.unop).op :=
  (IsColimit.comp_coconePointUniqueUpToIso_hom _ _ _).trans (by simp)

@[simp]
/-
**CategoryTheory.Limits.pushoutIsoOpPullback_inv_fst** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.Limits`。
形式化陈述：pushoutIsoOpPullback_inv_fst {X Y Z : Cᵒᵖ} (f : X ⟶ Z) (g : X ⟶ Y) [HasPus
hout f g] : (pushoutIsoOpPullback f g).inv.unop ≫ pullback.fst f.unop g.unop = (
pushout.inl f g).unop
参数：f : X ⟶ Z；g : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quiver.Hom.op_inj`：Quiver.Hom.op_inj {X Y : C} : Function.Injective (Qui
ver.Hom.op : (X ⟶ Y) -> (Opposite.op Y ⟶ Opposite.op X))
· 使用定理 `CategoryTheory.Limits.instHasPullbackUnopOfHasPushoutOpposite`：∀ {C : Ty
pe u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g 
: X ⟶ Z)   [CategoryTheory.Limits.HasPushout f g], …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pushoutIsoOpPullback_inv_fst {X Y Z : Cᵒᵖ} (f : X ⟶ Z) (g : X ⟶ Y) [HasPushout f g] :
    (pushoutIsoOpPullback f g).inv.unop ≫ pullback.fst f.unop g.unop = (pushout.inl f g).unop :=
  Quiver.Hom.op_inj <| by simp [← pushoutIsoOpPullback_inl_hom]

@[simp]
/-
**CategoryTheory.Limits.pushoutIsoOpPullback_inv_snd** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.Limits`。
形式化陈述：pushoutIsoOpPullback_inv_snd {X Y Z : Cᵒᵖ} (f : X ⟶ Z) (g : X ⟶ Y) [HasPus
hout f g] : (pushoutIsoOpPullback f g).inv.unop ≫ pullback.snd f.unop g.unop = (
pushout.inr f g).unop
参数：f : X ⟶ Z；g : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quiver.Hom.op_inj`：Quiver.Hom.op_inj {X Y : C} : Function.Injective (Qui
ver.Hom.op : (X ⟶ Y) -> (Opposite.op Y ⟶ Opposite.op X))
· 使用定理 `CategoryTheory.Limits.instHasPullbackUnopOfHasPushoutOpposite`：∀ {C : Ty
pe u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g 
: X ⟶ Z)   [CategoryTheory.Limits.HasPushout f g], …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pushoutIsoOpPullback_inv_snd {X Y Z : Cᵒᵖ} (f : X ⟶ Z) (g : X ⟶ Y) [HasPushout f g] :
    (pushoutIsoOpPullback f g).inv.unop ≫ pullback.snd f.unop g.unop = (pushout.inr f g).unop :=
  Quiver.Hom.op_inj <| by simp [← pushoutIsoOpPullback_inr_hom]

end Pushout

section Map

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Limits.op_pullbackMap** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory
.Limits`。
形式化陈述：op_pullbackMap {W X Y Z S T : C} (f₁ : W ⟶ S) (f₂ : X ⟶ S) [HasPullback f₁
 f₂] (g₁ : Y ⟶ T) (g₂ : Z ⟶ T) [HasPullback g₁ g₂] (i₁ : W ⟶ Y) (i₂ : X ⟶ Z) (i₃
 : S ⟶ T) (eq₁) (eq₂) : (pullback.map f₁ f₂ g₁ g₂ i₁ i₂ i₃ eq₁ eq₂).op = (pushou
tIsoOpPullback _ _).inv ≫ pushout.map g₁.op g₂.op f₁.op f₂.op i₁.op i₂.op i₃.op 
(by simp [eq₁, ← op_comp]) (by simp [eq₂, ← op_comp]) ≫ (pushoutIsoOpPullback _ 
_).hom
参数：f₁ : W ⟶ S；f₂ : X ⟶ S；g₁ : Y ⟶ T；g₂ : Z ⟶ T；i₁ : W ⟶ Y；i₂ : X ⟶ Z；i₃ : S ⟶ T；
eq₁；eq₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasPullbackUnopOfHasPushoutOpposite`：∀ {C : Ty
pe u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g 
: X ⟶ Z)   [CategoryTheory.Limits.HasPushout f g], …
· 使用定理 `CategoryTheory.Limits.instHasPushoutOppositeOpOfHasPullback`：∀ {C : Type
 u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X Y Z : C} (f : X ⟶ Z) (g : Y 
⟶ Z)   [CategoryTheory.Limits.HasPullback f g], C…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.eq_inv_comp`：eq_inv_comp (α : X ≅ Y) {f : X ⟶ Z} {g :
 Y ⟶ Z} : g = α.inv ≫ f ↔ α.hom ≫ g = f
· 使用定理 `CategoryTheory.Limits.pushout.hom_ext`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}   [inst_1 : Category
Theory.Limits.HasPushout f …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Limits.pushoutIsoOpPullback_inl_hom_assoc`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] {X Y Z : Cᵒᵖ} (f : X ⟶ Z) (g : X ⟶
 Y)   [inst_1 : CategoryTheory.Limits.HasPusho…
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PullbackCone.mk_π_app`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {W : C} (fst :
 W ⟶ X)   (snd : W ⟶ Y)   (eq :  …
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc_assoc`：∀ {J : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{
v, u} C]   {F : CategoryTheory.F…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.PushoutCocone.mk_ι_app`：∀ {C : Type u} [inst : Cat
egoryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} {W : C} (inl 
: Y ⟶ W)   (inr : Z ⟶ W) (eq : Cat…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.pushoutIsoOpPullback_inl_hom`：pushoutIsoOpPullback
_inl_hom {X Y Z : Cᵒᵖ} (f : X ⟶ Z) (g : X ⟶ Y) [HasPushout f g] : pushout.inl _ 
_ ≫ (pushoutIsoOpPullback f g).hom = (pu…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.pushoutIsoOpPullback_inr_hom_assoc`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] {X Y Z : Cᵒᵖ} (f : X ⟶ Z) (g : X ⟶
 Y)   [inst_1 : CategoryTheory.Limits.HasPusho…
· 使用定理 `CategoryTheory.Limits.pushoutIsoOpPullback_inr_hom`：pushoutIsoOpPullback
_inr_hom {X Y Z : Cᵒᵖ} (f : X ⟶ Z) (g : X ⟶ Y) [HasPushout f g] : pushout.inr _ 
_ ≫ (pushoutIsoOpPullback f g).hom = (pu…
-/
lemma op_pullbackMap {W X Y Z S T : C} (f₁ : W ⟶ S) (f₂ : X ⟶ S) [HasPullback f₁ f₂]
    (g₁ : Y ⟶ T) (g₂ : Z ⟶ T) [HasPullback g₁ g₂]
    (i₁ : W ⟶ Y) (i₂ : X ⟶ Z) (i₃ : S ⟶ T) (eq₁) (eq₂) :
    (pullback.map f₁ f₂ g₁ g₂ i₁ i₂ i₃ eq₁ eq₂).op =
      (pushoutIsoOpPullback _ _).inv ≫
        pushout.map g₁.op g₂.op f₁.op f₂.op i₁.op i₂.op i₃.op
        (by simp [eq₁, ← op_comp]) (by simp [eq₂, ← op_comp]) ≫
        (pushoutIsoOpPullback _ _).hom := by
  rw [Iso.eq_inv_comp]
  ext <;> simp [← op_comp]

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Limits.op_pushoutMap** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.
Limits`。
形式化陈述：op_pushoutMap {W X Y Z S T : C} (f₁ : S ⟶ W) (f₂ : S ⟶ X) [HasPushout f₁ f
₂] (g₁ : T ⟶ Y) (g₂ : T ⟶ Z) [HasPushout g₁ g₂] (i₁ : W ⟶ Y) (i₂ : X ⟶ Z) (i₃ : 
S ⟶ T) (eq₁ : f₁ ≫ i₁ = i₃ ≫ g₁) (eq₂ : f₂ ≫ i₂ = i₃ ≫ g₂) : (pushout.map f₁ f₂ 
g₁ g₂ i₁ i₂ i₃ eq₁ eq₂).op = (pullbackIsoOpPushout _ _).inv ≫ pullback.map g₁.op
 g₂.op f₁.op f₂.op i₁.op i₂.op i₃.op (by simp [eq₁, ← op_comp]) (by simp [eq₂, ←
 op_comp]) ≫ (pullbackIsoOpPushout _ _).hom
参数：f₁ : S ⟶ W；f₂ : S ⟶ X；g₁ : T ⟶ Y；g₂ : T ⟶ Z；i₁ : W ⟶ Y；i₂ : X ⟶ Z；i₃ : S ⟶ T；
eq₁ : f₁ ≫ i₁ = i₃ ≫ g₁；eq₂ : f₂ ≫ i₂ = i₃ ≫ g₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasPushoutUnopOfHasPullbackOpposite`：∀ {C : Ty
pe u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X Y Z : Cᵒᵖ} (f : X ⟶ Z) (g 
: Y ⟶ Z)   [CategoryTheory.Limits.HasPullback f g],…
· 使用定理 `CategoryTheory.Limits.instHasPullbackOppositeOpOfHasPushout`：∀ {C : Type
 u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X Y Z : C} (f : X ⟶ Y) (g : X 
⟶ Z)   [CategoryTheory.Limits.HasPushout f g], Ca…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.comp_inv_eq`：comp_inv_eq (α : X ≅ Y) {f : Z ⟶ Y} {g :
 Z ⟶ X} : f ≫ α.inv = g ↔ f = g ≫ α.hom
· 使用定理 `CategoryTheory.Limits.pullback.hom_ext`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categor
yTheory.Limits.HasPullback f…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Limits.pullbackIsoOpPushout_inv_fst`：pullbackIsoOpPushout
_inv_fst {X Y Z : Cᵒᵖ} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] : (pullbackIsoO
pPushout f g).inv ≫ pullback.fst f g = (…
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PushoutCocone.mk_ι_app`：∀ {C : Type u} [inst : Cat
egoryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} {W : C} (inl 
: Y ⟶ W)   (inr : Z ⟶ W) (eq : Cat…
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PullbackCone.mk_π_app`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {W : C} (fst :
 W ⟶ X)   (snd : W ⟶ Y)   (eq :  …
· 使用定理 `CategoryTheory.Limits.pullbackIsoOpPushout_inv_fst_assoc`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] {X Y Z : Cᵒᵖ} (f : X ⟶ Z) (g : Y ⟶
 Z)   [inst_1 : CategoryTheory.Limits.HasPullb…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.pullbackIsoOpPushout_inv_snd`：pullbackIsoOpPushout
_inv_snd {X Y Z : Cᵒᵖ} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] : (pullbackIsoO
pPushout f g).inv ≫ pullback.snd f g = (…
· 使用定理 `CategoryTheory.Limits.pullbackIsoOpPushout_inv_snd_assoc`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] {X Y Z : Cᵒᵖ} (f : X ⟶ Z) (g : Y ⟶
 Z)   [inst_1 : CategoryTheory.Limits.HasPullb…
-/
lemma op_pushoutMap {W X Y Z S T : C} (f₁ : S ⟶ W) (f₂ : S ⟶ X) [HasPushout f₁ f₂]
    (g₁ : T ⟶ Y) (g₂ : T ⟶ Z) [HasPushout g₁ g₂]
    (i₁ : W ⟶ Y) (i₂ : X ⟶ Z) (i₃ : S ⟶ T) (eq₁ : f₁ ≫ i₁ = i₃ ≫ g₁)
    (eq₂ : f₂ ≫ i₂ = i₃ ≫ g₂) :
    (pushout.map f₁ f₂ g₁ g₂ i₁ i₂ i₃ eq₁ eq₂).op =
      (pullbackIsoOpPushout _ _).inv ≫
        pullback.map g₁.op g₂.op f₁.op f₂.op i₁.op i₂.op i₃.op
        (by simp [eq₁, ← op_comp]) (by simp [eq₂, ← op_comp]) ≫
        (pullbackIsoOpPushout _ _).hom := by
  rw [← Category.assoc, ← Iso.comp_inv_eq]
  ext <;> simp [← op_comp]

end Map

end Limits

namespace CommSq
open Limits

variable {C : Type*} [Category* C]
variable {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}

set_option backward.isDefEq.respectTransparency false in
/-- The pushout cocone in the opposite category associated to the cone of
a commutative square identifies to the cocone of the flipped commutative square in
the opposite category -/
/-
**CategoryTheory.CommSq.coneOp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.CommSq`
。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     {W 
X Y Z : C} →       {f : W ⟶ X} → {g : W ⟶ Y} → {h : X ⟶ Z} → {i : Y ⟶ Z} → (p : 
CategoryTheory.CommSq f g h i) → p.cone.op ≅ ⋯.cocone
参数：p : CategoryTheory.CommSq f g h i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pushout cocone in the opposite category associated to the cone of
a commutative square identifies to the cocone of the flipped commutative square 
in
the opposite category
-/
def coneOp (p : CommSq f g h i) : p.cone.op ≅ p.flip.op.cocone :=
  PushoutCocone.ext (Iso.refl _) (by simp) (by simp)

set_option backward.isDefEq.respectTransparency false in
/-- The pullback cone in the opposite category associated to the cocone of
a commutative square identifies to the cone of the flipped commutative square in
the opposite category -/
/-
**CategoryTheory.CommSq.coconeOp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.CommS
q`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     {W 
X Y Z : C} →       {f : W ⟶ X} → {g : W ⟶ Y} → {h : X ⟶ Z} → {i : Y ⟶ Z} → (p : 
CategoryTheory.CommSq f g h i) → p.cocone.op ≅ ⋯.cone
参数：p : CategoryTheory.CommSq f g h i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pullback cone in the opposite category associated to the cocone of
a commutative square identifies to the cone of the flipped commutative square in
the opposite category
-/
def coconeOp (p : CommSq f g h i) : p.cocone.op ≅ p.flip.op.cone :=
  PullbackCone.ext (Iso.refl _) (by simp) (by simp)

set_option backward.isDefEq.respectTransparency false in
/-- The pushout cocone obtained from the pullback cone associated to a
commutative square in the opposite category identifies to the cocone associated
to the flipped square. -/
/-
**CategoryTheory.CommSq.coneUnop** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.CommS
q`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     {W 
X Y Z : Cᵒᵖ} →       {f : W ⟶ X} →         {g : W ⟶ Y} → {h : X ⟶ Z} → {i : Y ⟶ 
Z} → (p : CategoryTheory.CommSq f g h i) → p.cone.unop ≅ ⋯.cocone
参数：p : CategoryTheory.CommSq f g h i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pushout cocone obtained from the pullback cone associated to a
commutative square in the opposite category identifies to the cocone associated
to the flipped square.
-/
def coneUnop {W X Y Z : Cᵒᵖ} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z} (p : CommSq f g h i) :
    p.cone.unop ≅ p.flip.unop.cocone :=
  PushoutCocone.ext (Iso.refl _) (by simp) (by simp)

set_option backward.isDefEq.respectTransparency false in
/-- The pullback cone obtained from the pushout cone associated to a
commutative square in the opposite category identifies to the cone associated
to the flipped square. -/
/-
**CategoryTheory.CommSq.coconeUnop** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Com
mSq`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     {W 
X Y Z : Cᵒᵖ} →       {f : W ⟶ X} →         {g : W ⟶ Y} → {h : X ⟶ Z} → {i : Y ⟶ 
Z} → (p : CategoryTheory.CommSq f g h i) → p.cocone.unop ≅ ⋯.cone
参数：p : CategoryTheory.CommSq f g h i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pullback cone obtained from the pushout cone associated to a
commutative square in the opposite category identifies to the cone associated
to the flipped square.
-/
def coconeUnop {W X Y Z : Cᵒᵖ} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}
    (p : CommSq f g h i) : p.cocone.unop ≅ p.flip.unop.cone :=
  PullbackCone.ext (Iso.refl _) (by simp) (by simp)

end CommSq

end CategoryTheory

