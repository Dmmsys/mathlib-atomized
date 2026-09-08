/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
module

public import Mathlib.CategoryTheory.Sites.Plus
public import Mathlib.CategoryTheory.Limits.Shapes.ConcreteCategory

/-!

# Sheafification

We construct the sheafification of a presheaf over a site `C` with values in `D` whenever
`D` is a concrete category for which the forgetful functor preserves the appropriate (co)limits
and reflects isomorphisms.

We generally follow the approach of https://stacks.math.columbia.edu/tag/00W1

-/

@[expose] public section


namespace CategoryTheory

open CategoryTheory.Limits Opposite

universe t w' w v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {D : Type w} [Category.{w'} D]

section

variable {FD : D → D → Type*} {CD : D → Type t} [∀ X Y, FunLike (FD X Y) (CD X) (CD Y)]
variable [ConcreteCategory.{t} D FD]

/-- A concrete version of the multiequalizer, to be used below. -/
/-
**CategoryTheory.Meq** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：Meq {X : C} (P : Cᵒᵖ ⥤ D) (S : J.Cover X)
参数：P : Cᵒᵖ ⥤ D；S : J.Cover X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A concrete version of the multiequalizer, to be used below.
-/
def Meq {X : C} (P : Cᵒᵖ ⥤ D) (S : J.Cover X) :=
  { x : ∀ I : S.Arrow, ToType (P.obj (op I.Y)) //
    ∀ I : S.Relation, P.map I.r.g₁.op (x I.fst) = P.map I.r.g₂.op (x I.snd) }

end

namespace Meq

variable {FD : D → D → Type*} {CD : D → Type t} [∀ X Y, FunLike (FD X Y) (CD X) (CD Y)]
variable [ConcreteCategory.{t} D FD]

/-
**CategoryTheory.Meq.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Meq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X} (P : Cᵒᵖ ⥤ D) (S : J.Cover X) :
    CoeFun (Meq P S) fun _ => ∀ I : S.Arrow, ToType (P.obj (op I.Y)) :=
  ⟨fun x => x.1⟩
/-
**CategoryTheory.Meq.congr_apply** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Meq`。
形式化陈述：congr_apply {X} {P : Cᵒᵖ ⥤ D} {S : J.Cover X} (x : Meq P S) {Y} {f g : Y ⟶
 X} (h : f = g) (hf : S f) : x ⟨_, _, hf⟩ = x ⟨_, g, by simpa only [← h] using h
f⟩
参数：x : Meq P S；h : f = g；hf : S f。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma congr_apply {X} {P : Cᵒᵖ ⥤ D} {S : J.Cover X} (x : Meq P S) {Y}
    {f g : Y ⟶ X} (h : f = g) (hf : S f) :
    x ⟨_, _, hf⟩ = x ⟨_, g, by simpa only [← h] using hf⟩ := by
  subst h
  rfl

@[ext]
/-
**CategoryTheory.Meq.ext** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Meq`。
形式化陈述：ext {X} {P : Cᵒᵖ ⥤ D} {S : J.Cover X} (x y : Meq P S) (h : forall I : S.Ar
row, x I = y I) : x = y
参数：x y : Meq P S；h : forall I : S.Arrow, x I = y I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem ext {X} {P : Cᵒᵖ ⥤ D} {S : J.Cover X} (x y : Meq P S) (h : ∀ I : S.Arrow, x I = y I) :
    x = y :=
  Subtype.ext <| funext <| h
/-
**CategoryTheory.Meq.condition** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Meq`。
形式化陈述：condition {X} {P : Cᵒᵖ ⥤ D} {S : J.Cover X} (x : Meq P S) (I : S.Relation)
 : P.map I.r.g₁.op (x (S.shape.fst I)) = P.map I.r.g₂.op (x (S.shape.snd I))
参数：x : Meq P S；I : S.Relation。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem condition {X} {P : Cᵒᵖ ⥤ D} {S : J.Cover X} (x : Meq P S) (I : S.Relation) :
    P.map I.r.g₁.op (x (S.shape.fst I)) = P.map I.r.g₂.op (x (S.shape.snd I)) :=
  x.2 _

/-- Refine a term of `Meq P T` with respect to a refinement `S ⟶ T` of covers. -/
/-
**CategoryTheory.Meq.refine** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Meq`。
形式化陈述：refine {X : C} {P : Cᵒᵖ ⥤ D} {S T : J.Cover X} (x : Meq P T) (e : S ⟶ T) :
 Meq P S
参数：x : Meq P T；e : S ⟶ T。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Refine a term of `Meq P T` with respect to a refinement `S ⟶ T` of covers.
-/
def refine {X : C} {P : Cᵒᵖ ⥤ D} {S T : J.Cover X} (x : Meq P T) (e : S ⟶ T) : Meq P S :=
  ⟨fun I => x ⟨I.Y, I.f, (leOfHom e) _ I.hf⟩, fun I =>
    x.condition (GrothendieckTopology.Cover.Relation.mk' (I.r.map e))⟩

@[simp]
/-
**CategoryTheory.Meq.refine_apply** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Meq`
。
形式化陈述：refine_apply {X : C} {P : Cᵒᵖ ⥤ D} {S T : J.Cover X} (x : Meq P T) (e : S 
⟶ T) (I : S.Arrow) : x.refine e I = x ⟨I.Y, I.f, (leOfHom e) _ I.hf⟩
参数：x : Meq P T；e : S ⟶ T；I : S.Arrow。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem refine_apply {X : C} {P : Cᵒᵖ ⥤ D} {S T : J.Cover X} (x : Meq P T) (e : S ⟶ T)
    (I : S.Arrow) : x.refine e I = x ⟨I.Y, I.f, (leOfHom e) _ I.hf⟩ :=
  rfl

/-- Pull back a term of `Meq P S` with respect to a morphism `f : Y ⟶ X` in `C`. -/
/-
**CategoryTheory.Meq.pullback** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Meq`。
形式化陈述：pullback {Y X : C} {P : Cᵒᵖ ⥤ D} {S : J.Cover X} (x : Meq P S) (f : Y ⟶ X)
 : Meq P ((J.pullback f).obj S)
参数：x : Meq P S；f : Y ⟶ X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Pull back a term of `Meq P S` with respect to a morphism `f : Y ⟶ X` in `C`.
-/
def pullback {Y X : C} {P : Cᵒᵖ ⥤ D} {S : J.Cover X} (x : Meq P S) (f : Y ⟶ X) :
    Meq P ((J.pullback f).obj S) :=
  ⟨fun I => x ⟨_, I.f ≫ f, I.hf⟩, fun I =>
    x.condition (GrothendieckTopology.Cover.Relation.mk' I.r.base)⟩

@[simp]
/-
**CategoryTheory.Meq.pullback_apply** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Me
q`。
形式化陈述：pullback_apply {Y X : C} {P : Cᵒᵖ ⥤ D} {S : J.Cover X} (x : Meq P S) (f : 
Y ⟶ X) (I : ((J.pullback f).obj S).Arrow) : x.pullback f I = x ⟨_, I.f ≫ f, I.hf
⟩
参数：x : Meq P S；f : Y ⟶ X；I : ((J.pullback f).obj S).Arrow。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pullback_apply {Y X : C} {P : Cᵒᵖ ⥤ D} {S : J.Cover X} (x : Meq P S) (f : Y ⟶ X)
    (I : ((J.pullback f).obj S).Arrow) : x.pullback f I = x ⟨_, I.f ≫ f, I.hf⟩ :=
  rfl

@[simp]
/-
**CategoryTheory.Meq.pullback_refine** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.M
eq`。
形式化陈述：pullback_refine {Y X : C} {P : Cᵒᵖ ⥤ D} {S T : J.Cover X} (h : S ⟶ T) (f :
 Y ⟶ X) (x : Meq P T) : (x.pullback f).refine ((J.pullback f).map h) = (refine x
 h).pullback _
参数：h : S ⟶ T；f : Y ⟶ X；x : Meq P T。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pullback_refine {Y X : C} {P : Cᵒᵖ ⥤ D} {S T : J.Cover X} (h : S ⟶ T) (f : Y ⟶ X)
    (x : Meq P T) : (x.pullback f).refine ((J.pullback f).map h) = (refine x h).pullback _ :=
  rfl

/-- Make a term of `Meq P S`. -/
/-
**CategoryTheory.Meq.mk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Meq`。
形式化陈述：mk {X : C} {P : Cᵒᵖ ⥤ D} (S : J.Cover X) (x : ToType (P.obj (op X))) : Meq
 P S
参数：S : J.Cover X；x : ToType (P.obj (op X))。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Make a term of `Meq P S`.
-/
def mk {X : C} {P : Cᵒᵖ ⥤ D} (S : J.Cover X) (x : ToType (P.obj (op X))) : Meq P S :=
  ⟨fun I => P.map I.f.op x, fun I => by
    simp only [← ConcreteCategory.comp_apply, ← P.map_comp, ← op_comp, I.r.w]⟩
/-
**CategoryTheory.Meq.mk_apply** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Meq`。
形式化陈述：mk_apply {X : C} {P : Cᵒᵖ ⥤ D} (S : J.Cover X) (x : ToType (P.obj (op X)))
 (I : S.Arrow) : mk S x I = P.map I.f.op x
参数：S : J.Cover X；x : ToType (P.obj (op X))；I : S.Arrow。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_apply {X : C} {P : Cᵒᵖ ⥤ D} (S : J.Cover X) (x : ToType (P.obj (op X))) (I : S.Arrow) :
    mk S x I = P.map I.f.op x :=
  rfl

variable [∀ {X : C} (S : J.Cover X),
  PreservesLimitsOfShape (WalkingMulticospan S.shape) (forget D)]

/-- The equivalence between the type associated to `multiequalizer (S.index P)` and `Meq P S`. -/
/-
**CategoryTheory.Meq.equiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Meq`。
形式化陈述：equiv {X : C} (P : Cᵒᵖ ⥤ D) (S : J.Cover X) [HasMultiequalizer (S.index P)
] : ToType (multiequalizer (S.index P)) ≃ Meq P S
参数：P : Cᵒᵖ ⥤ D；S : J.Cover X；S.index P。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence between the type associated to `multiequalizer (S.index P)` and 
`Meq P S`.
-/
noncomputable def equiv {X : C} (P : Cᵒᵖ ⥤ D) (S : J.Cover X) [HasMultiequalizer (S.index P)] :
    ToType (multiequalizer (S.index P)) ≃ Meq P S :=
  Limits.Concrete.multiequalizerEquiv.{t} (C := D) _

@[simp]
/-
**CategoryTheory.Meq.equiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Meq`。
形式化陈述：equiv_apply {X : C} {P : Cᵒᵖ ⥤ D} {S : J.Cover X} [HasMultiequalizer (S.in
dex P)] (x : ToType (multiequalizer (S.index P))) (I : S.Arrow) : equiv P S x I 
= Multiequalizer.ι (S.index P) I x
参数：S.index P；x : ToType (multiequalizer (S.index P))；I : S.Arrow。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem equiv_apply {X : C} {P : Cᵒᵖ ⥤ D} {S : J.Cover X} [HasMultiequalizer (S.index P)]
    (x : ToType (multiequalizer (S.index P))) (I : S.Arrow) :
    equiv P S x I = Multiequalizer.ι (S.index P) I x :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.Meq.equiv_symm_eq_apply** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Meq`。
形式化陈述：equiv_symm_eq_apply {X : C} {P : Cᵒᵖ ⥤ D} {S : J.Cover X} [HasMultiequaliz
er (S.index P)] (x : Meq P S) (I : S.Arrow) : -- We can hint `ConcreteCategory.h
om (Y
参数：S.index P；x : Meq P S；I : S.Arrow。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem equiv_symm_eq_apply {X : C} {P : Cᵒᵖ ⥤ D} {S : J.Cover X} [HasMultiequalizer (S.index P)]
    (x : Meq P S) (I : S.Arrow) :
    -- We can hint `ConcreteCategory.hom (Y := P.obj (op I.Y))` below to put it into `simp`-normal
    -- form, but that doesn't seem to fix the `erw`s below...
    (Multiequalizer.ι (S.index P) I) ((Meq.equiv P S).symm x) = x I := by
  simp [-GrothendieckTopology.Cover.index_left, ← equiv_apply]

end Meq

namespace GrothendieckTopology

namespace Plus

variable {FD : D → D → Type*} {CD : D → Type t} [∀ X Y, FunLike (FD X Y) (CD X) (CD Y)]
variable [instCC : ConcreteCategory.{t} D FD]

variable [∀ {X : C} (S : J.Cover X),
  PreservesLimitsOfShape (WalkingMulticospan S.shape) (forget D)]
variable [∀ X : C, HasColimitsOfShape (J.Cover X)ᵒᵖ D]
variable [∀ (P : Cᵒᵖ ⥤ D) (X : C) (S : J.Cover X), HasMultiequalizer (S.index P)]

noncomputable section

/-- Make a term of `(J.plusObj P).obj (op X)` from `x : Meq P S`. -/
/-
**CategoryTheory.GrothendieckTopology.Plus.mk** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.GrothendieckTopology.Plus`。
形式化陈述：mk {X : C} {P : Cᵒᵖ ⥤ D} {S : J.Cover X} (x : Meq P S) : ToType ((J.plusOb
j P).obj (op X))
参数：x : Meq P S。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Make a term of `(J.plusObj P).obj (op X)` from `x : Meq P S`.
-/
def mk {X : C} {P : Cᵒᵖ ⥤ D} {S : J.Cover X} (x : Meq P S) : ToType ((J.plusObj P).obj (op X)) :=
  colimit.ι (J.diagram P X) (op S) ((Meq.equiv P S).symm x)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.GrothendieckTopology.Plus.res_mk_eq_mk_pullback** 是 Mathlib 中的一
个定理，位于命名空间 `CategoryTheory.GrothendieckTopology.Plus`。
形式化陈述：res_mk_eq_mk_pullback {Y X : C} {P : Cᵒᵖ ⥤ D} {S : J.Cover X} (x : Meq P S
) (f : Y ⟶ X) : (J.plusObj P).map f.op (mk x) = mk (x.pullback f)
参数：x : Meq P S；f : Y ⟶ X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
· 使用定理 `CategoryTheory.Limits.ι_colimMap_assoc`：∀ {J : Type u₁} [inst : Category
Theory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u
} C]   {F G : CategoryTheory…
· 使用定理 `CategoryTheory.Limits.colimit.ι_pre`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {K : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} K]   {C : Type u} [inst…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `CategoryTheory.Meq.ext`：ext {X} {P : Cᵒᵖ ⥤ D} {S : J.Cover X} (x y : Meq
 P S) (h : forall I : S.Arrow, x I = y I) : x = y
· 使用定理 `CategoryTheory.GrothendieckTopology.Cover.Arrow.hf`：∀ {C : Type u} [inst
 : CategoryTheory.Category.{v, u} C] {X : C} {J : CategoryTheory.GrothendieckTop
ology C}   {S : J.Cover X} (self : S.Arr…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Meq.equiv_symm_eq_apply`：equiv_symm_eq_apply {X : C} {P :
 Cᵒᵖ ⥤ D} {S : J.Cover X} [HasMultiequalizer (S.index P)] (x : Meq P S) (I : S.A
rrow) : -- We can hint `Conc…
-/
theorem res_mk_eq_mk_pullback {Y X : C} {P : Cᵒᵖ ⥤ D} {S : J.Cover X} (x : Meq P S) (f : Y ⟶ X) :
    (J.plusObj P).map f.op (mk x) = mk (x.pullback f) := by
  dsimp [mk, plusObj]
  rw [← CategoryTheory.comp_apply (x := (Meq.equiv P S).symm x), ι_colimMap_assoc, colimit.ι_pre,
    CategoryTheory.comp_apply (x := (Meq.equiv P S).symm x)]
  apply congr_arg
  apply (Meq.equiv P _).injective
  dsimp
  simp only [Equiv.apply_symm_apply]
  ext i
  simp only [Meq.equiv_apply, Cover.index_left, ← ConcreteCategory.comp_apply, limit.lift_π,
    Multifork.ofι_pt, Multifork.ofι_π_app, Meq.pullback_apply, pullback_obj]
  rw [dsimp% Meq.equiv_symm_eq_apply x i.base]
  cases i; rfl

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.GrothendieckTopology.Plus.toPlus_mk** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.GrothendieckTopology.Plus`。
形式化陈述：toPlus_mk {X : C} {P : Cᵒᵖ ⥤ D} (S : J.Cover X) (x : ToType (P.obj (op X))
) : (J.toPlus P).app _ x = mk (Meq.mk S x)
参数：S : J.Cover X；x : ToType (P.obj (op X))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderTop.le_top`：∀ {α : Type u} {inst : LE α} [self : OrderTop α] (a : α
), a ≤ ⊤
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.colimit.w`：∀ {J : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]   
(F : CategoryTheory.F…
· 使用定理 `CategoryTheory.ConcreteCategory.comp_apply`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (
C → Type w)}   {inst_1 : outPara…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.Concrete.multiequalizer_ext`：multiequalizer_ext {J
 : MulticospanShape.{w, w'}} {I : MulticospanIndex J C} [HasMultiequalizer I] [P
reservesLimit I.multicospan (forget C)]…
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.Multiequalizer.lift_ι`：lift_ι (W : C) (k : forall 
a, W ⟶ I.left a) (h : forall b, k (J.fst b) ≫ I.fst b = k (J.snd b) ≫ I.snd b) (
a) : Multiequalizer.lift I _ k h …
· 使用定理 `CategoryTheory.Meq.equiv_symm_eq_apply`：equiv_symm_eq_apply {X : C} {P :
 Cᵒᵖ ⥤ D} {S : J.Cover X} [HasMultiequalizer (S.index P)] (x : Meq P S) (I : S.A
rrow) : -- We can hint `Conc…
-/
theorem toPlus_mk {X : C} {P : Cᵒᵖ ⥤ D} (S : J.Cover X) (x : ToType (P.obj (op X))) :
    (J.toPlus P).app _ x = mk (Meq.mk S x) := by
  dsimp [mk, toPlus]
  let e : S ⟶ ⊤ := homOfLE (OrderTop.le_top _)
  rw [← colimit.w _ e.op]
  delta Cover.toMultiequalizer
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
  apply congr_arg
  dsimp [diagram]
  apply Concrete.multiequalizer_ext (C := D)
  intro i
  simp only [← ConcreteCategory.comp_apply, Category.assoc, Multiequalizer.lift_ι,
    Meq.equiv_symm_eq_apply]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.GrothendieckTopology.Plus.toPlus_apply** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.GrothendieckTopology.Plus`。
形式化陈述：toPlus_apply {X : C} {P : Cᵒᵖ ⥤ D} (S : J.Cover X) (x : Meq P S) (I : S.Ar
row) : (J.toPlus P).app _ (x I) = (J.plusObj P).map I.f.op (mk x)
参数：S : J.Cover X；x : Meq P S；I : S.Arrow。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.ConcreteCategory.comp_apply`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (
C → Type w)}   {inst_1 : outPara…
· 使用定理 `CategoryTheory.Limits.ι_colimMap_assoc`：∀ {J : Type u₁} [inst : Category
Theory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u
} C]   {F G : CategoryTheory…
· 使用定理 `CategoryTheory.Limits.colimit.ι_pre`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {K : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} K]   {C : Type u} [inst…
· 使用定理 `OrderTop.le_top`：∀ {α : Type u} {inst : LE α} [self : OrderTop α] (a : α
), a ≤ ⊤
· 使用定理 `CategoryTheory.Limits.colimit.w`：∀ {J : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]   
(F : CategoryTheory.F…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.Concrete.multiequalizer_ext`：multiequalizer_ext {J
 : MulticospanShape.{w, w'}} {I : MulticospanIndex J C} [HasMultiequalizer I] [P
reservesLimit I.multicospan (forget C)]…
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Limits.Multiequalizer.lift_ι`：lift_ι (W : C) (k : forall 
a, W ⟶ I.left a) (h : forall b, k (J.fst b) ≫ I.fst b = k (J.snd b) ≫ I.snd b) (
a) : Multiequalizer.lift I _ k h …
· 使用定理 `CategoryTheory.Meq.equiv_symm_eq_apply`：equiv_symm_eq_apply {X : C} {P :
 Cᵒᵖ ⥤ D} {S : J.Cover X} [HasMultiequalizer (S.index P)] (x : Meq P S) (I : S.A
rrow) : -- We can hint `Conc…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.id_apply`：∀ {C : Type u} [inst : CategoryTheory.Category.
{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → FunL
ike (FC X Y) …
· 使用定理 `CategoryTheory.Meq.condition`：condition {X} {P : Cᵒᵖ ⥤ D} {S : J.Cover X
} (x : Meq P S) (I : S.Relation) : P.map I.r.g₁.op (x (S.shape.fst I)) = P.map I
.r.g₂.op (x (S.sha…
-/
theorem toPlus_apply {X : C} {P : Cᵒᵖ ⥤ D} (S : J.Cover X) (x : Meq P S) (I : S.Arrow) :
    (J.toPlus P).app _ (x I) = (J.plusObj P).map I.f.op (mk x) := by
  dsimp only [toPlus, plusObj]
  delta Cover.toMultiequalizer
  dsimp [mk]
  rw [← ConcreteCategory.comp_apply, ι_colimMap_assoc, colimit.ι_pre, ConcreteCategory.comp_apply,
    ConcreteCategory.comp_apply]
  dsimp only [Functor.op]
  let e : (J.pullback I.f).obj (unop (op S)) ⟶ ⊤ := homOfLE (OrderTop.le_top _)
  rw [← colimit.w _ e.op, ConcreteCategory.comp_apply]
  apply congr_arg
  apply Concrete.multiequalizer_ext (C := D)
  intro i
  dsimp
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
    Multiequalizer.lift_ι, Multiequalizer.lift_ι, Multiequalizer.lift_ι]
  rw [dsimp% Meq.equiv_symm_eq_apply x i.base]
  simpa using! (x.condition (Cover.Relation.mk' (I.precompRelation i.f))).symm
/-
**CategoryTheory.GrothendieckTopology.Plus.toPlus_eq_mk** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.GrothendieckTopology.Plus`。
形式化陈述：toPlus_eq_mk {X : C} {P : Cᵒᵖ ⥤ D} (x : ToType (P.obj (op X))) : (J.toPlus
 P).app _ x = mk (Meq.mk ⊤ x)
参数：x : ToType (P.obj (op X))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrothendieckTopology.Plus.toPlus_mk`：toPlus_mk {X : C} {P
 : Cᵒᵖ ⥤ D} (S : J.Cover X) (x : ToType (P.obj (op X))) : (J.toPlus P).app _ x =
 mk (Meq.mk S x)
-/
theorem toPlus_eq_mk {X : C} {P : Cᵒᵖ ⥤ D} (x : ToType (P.obj (op X))) :
    (J.toPlus P).app _ x = mk (Meq.mk ⊤ x) := toPlus_mk ⊤ x

variable [∀ X : C, PreservesColimitsOfShape (J.Cover X)ᵒᵖ (forget D)]

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.GrothendieckTopology.Plus.exists_rep** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.GrothendieckTopology.Plus`。
形式化陈述：exists_rep {X : C} {P : Cᵒᵖ ⥤ D} (x : ToType ((J.plusObj P).obj (op X))) :
 exists (S : J.Cover X) (y : Meq P S), x = mk y
参数：x : ToType ((J.plusObj P).obj (op X))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Concrete.colimit_exists_rep`：colimit_exists_rep [H
asColimit F] (x : ToType (colimit F)) : exists (j : J) (y : ToType (F.obj j)), c
olimit.ι F j y = x
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem exists_rep {X : C} {P : Cᵒᵖ ⥤ D} (x : ToType ((J.plusObj P).obj (op X))) :
    ∃ (S : J.Cover X) (y : Meq P S), x = mk y := by
  obtain ⟨S, y, h⟩ := Concrete.colimit_exists_rep (J.diagram P X) x
  use S.unop, Meq.equiv _ _ y
  rw [← h]
  dsimp [mk]
  simp

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.GrothendieckTopology.Plus.eq_mk_iff_exists** 是 Mathlib 中的一个定理，位
于命名空间 `CategoryTheory.GrothendieckTopology.Plus`。
形式化陈述：eq_mk_iff_exists {X : C} {P : Cᵒᵖ ⥤ D} {S T : J.Cover X} (x : Meq P S) (y 
: Meq P T) : mk x = mk y ↔ exists (W : J.Cover X) (h1 : W ⟶ S) (h2 : W ⟶ T), x.r
efine h1 = y.refine h2
参数：x : Meq P S；y : Meq P T。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `CategoryTheory.Limits.Concrete.colimit_exists_of_rep_eq`：colimit_exists_
of_rep_eq [HasColimit F] {i j : J} (x : ToType (F.obj i)) (y : ToType (F.obj j))
 (h : colimit.ι F _ x = colimit.ι F _ y) : ex…
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.isCofiltered_of_directed_ge_nonempty`：∀ (α : Type u) [ins
t : Preorder α] [IsCodirectedOrder α] [Nonempty α], CategoryTheory.IsCofiltered 
α
· 使用定理 `SemilatticeInf.instIsCodirectedOrder`：∀ {α : Type u_1} [inst : Semilatti
ceInf α], IsCodirectedOrder α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `CategoryTheory.Meq.ext`：ext {X} {P : Cᵒᵖ ⥤ D} {S : J.Cover X} (x y : Meq
 P S) (h : forall I : S.Arrow, x I = y I) : x = y
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `CategoryTheory.leOfHom`：leOfHom {x y : X} (h : x ⟶ y) : x <= y
· 使用定理 `CategoryTheory.GrothendieckTopology.Cover.Arrow.hf`：∀ {C : Type u} [inst
 : CategoryTheory.Category.{v, u} C] {X : C} {J : CategoryTheory.GrothendieckTop
ology C}   {S : J.Cover X} (self : S.Arr…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ConcreteCategory.comp_apply`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (
C → Type w)}   {inst_1 : outPara…
· 使用定理 `CategoryTheory.Limits.Multiequalizer.lift_ι`：lift_ι (W : C) (k : forall 
a, W ⟶ I.left a) (h : forall b, k (J.fst b) ≫ I.fst b = k (J.snd b) ≫ I.snd b) (
a) : Multiequalizer.lift I _ k h …
· 使用定理 `CategoryTheory.Meq.equiv_symm_eq_apply`：equiv_symm_eq_apply {X : C} {P :
 Cᵒᵖ ⥤ D} {S : J.Cover X} [HasMultiequalizer (S.index P)] (x : Meq P S) (I : S.A
rrow) : -- We can hint `Conc…
· 使用定理 `CategoryTheory.Limits.Concrete.colimit_rep_eq_of_exists`：colimit_rep_eq_
of_exists [HasColimit F] {i j : J} (x : ToType (F.obj i)) (y : ToType (F.obj j))
 (h : exists (k : _) (f : i ⟶ k) (g : j ⟶ k),…
· 使用定理 `CategoryTheory.Limits.Concrete.multiequalizer_ext`：multiequalizer_ext {J
 : MulticospanShape.{w, w'}} {I : MulticospanIndex J C} [HasMultiequalizer I] [P
reservesLimit I.multicospan (forget C)]…
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
-/
theorem eq_mk_iff_exists {X : C} {P : Cᵒᵖ ⥤ D} {S T : J.Cover X} (x : Meq P S) (y : Meq P T) :
    mk x = mk y ↔ ∃ (W : J.Cover X) (h1 : W ⟶ S) (h2 : W ⟶ T), x.refine h1 = y.refine h2 := by
  constructor
  · intro h
    obtain ⟨W, h1, h2, hh⟩ := Concrete.colimit_exists_of_rep_eq (C := D) _ _ _ h
    use W.unop, h1.unop, h2.unop
    ext I
    apply_fun Multiequalizer.ι (W.unop.index P) I at hh
    convert! hh
    all_goals
      dsimp [diagram]
      rw [← ConcreteCategory.comp_apply, Multiequalizer.lift_ι]
      erw [Meq.equiv_symm_eq_apply]
      cases I; rfl
  · rintro ⟨S, h1, h2, e⟩
    apply Concrete.colimit_rep_eq_of_exists (C := D)
    use op S, h1.op, h2.op
    apply Concrete.multiequalizer_ext
    intro i
    apply_fun fun ee => ee i at e
    convert! e using 1
    all_goals
      dsimp [diagram]
      rw [← ConcreteCategory.comp_apply, Multiequalizer.lift_ι]
      erw [Meq.equiv_symm_eq_apply]
      cases i; rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- `P⁺` is always separated. -/
/-
**CategoryTheory.GrothendieckTopology.Plus.sep** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.GrothendieckTopology.Plus`。
形式化陈述：sep {X : C} (P : Cᵒᵖ ⥤ D) (S : J.Cover X) (x y : ToType ((J.plusObj P).obj
 (op X))) (h : forall I : S.Arrow, (J.plusObj P).map I.f.op x = (J.plusObj P).ma
p I.f.op y) : x = y
参数：P : Cᵒᵖ ⥤ D；S : J.Cover X；x y : ToType ((J.plusObj P).obj (op X))；h : forall 
I : S.Arrow, (J.plusObj P).map I.f.op x = (J.plusObj P).map I.f.op y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrothendieckTopology.Plus.exists_rep`：exists_rep {X : C} 
{P : Cᵒᵖ ⥤ D} (x : ToType ((J.plusObj P).obj (op X))) : exists (S : J.Cover X) (
y : Meq P S), x = mk y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.GrothendieckTopology.Plus.eq_mk_iff_exists`：eq_mk_iff_exi
sts {X : C} {P : Cᵒᵖ ⥤ D} {S T : J.Cover X} (x : Meq P S) (y : Meq P T) : mk x =
 mk y ↔ exists (W : J.Cover X) (h1 : W ⟶ S) (h2…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.leOfHom`：leOfHom {x y : X} (h : x ⟶ y) : x <= y
· 使用定理 `CategoryTheory.Meq.ext`：ext {X} {P : Cᵒᵖ ⥤ D} {S : J.Cover X} (x y : Meq
 P S) (h : forall I : S.Arrow, x I = y I) : x = y
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用引理 `CategoryTheory.Meq.congr_apply`：congr_apply {X} {P : Cᵒᵖ ⥤ D} {S : J.Cov
er X} (x : Meq P S) {Y} {f g : Y ⟶ X} (h : f = g) (hf : S f) : x ⟨_, _, hf⟩ = x 
⟨_, g, by simpa only…
· 使用定理 `CategoryTheory.GrothendieckTopology.Cover.Arrow.middle_spec`：∀ {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C] {J : CategoryTheory.GrothendieckTo
pology C} {X : C}   {S : J.Cover X} {T : (I : S.A…
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.GrothendieckTopology.Plus.res_mk_eq_mk_pullback`：res_mk_e
q_mk_pullback {Y X : C} {P : Cᵒᵖ ⥤ D} {S : J.Cover X} (x : Meq P S) (f : Y ⟶ X) 
: (J.plusObj P).map f.op (mk x) = mk (x.pullback f)

--- 原说明 ---
`P⁺` is always separated.
-/
theorem sep {X : C} (P : Cᵒᵖ ⥤ D) (S : J.Cover X) (x y : ToType ((J.plusObj P).obj (op X)))
    (h : ∀ I : S.Arrow, (J.plusObj P).map I.f.op x = (J.plusObj P).map I.f.op y) : x = y := by
  -- First, we choose representatives for x and y.
  obtain ⟨Sx, x, rfl⟩ := exists_rep x
  obtain ⟨Sy, y, rfl⟩ := exists_rep y
  simp only [res_mk_eq_mk_pullback] at h
  -- Next, using our assumption,
  -- choose covers over which the pullbacks of these representatives become equal.
  choose W h1 h2 hh using fun I : S.Arrow => (eq_mk_iff_exists _ _).mp (h I)
  -- To prove equality, it suffices to prove that there exists a cover over which
  -- the representatives become equal.
  rw [eq_mk_iff_exists]
  -- Construct the cover over which the representatives become equal by combining the various
  -- covers chosen above.
  let B : J.Cover X := S.bind W
  use B
  -- Prove that this cover refines the two covers over which our representatives are defined
  -- and use these proofs.
  let ex : B ⟶ Sx :=
    homOfLE
      (by
        rintro Y f ⟨Z, e1, e2, he2, he1, hee⟩
        rw [← hee]
        apply leOfHom (h1 ⟨_, _, he2⟩)
        exact he1)
  let ey : B ⟶ Sy :=
    homOfLE
      (by
        rintro Y f ⟨Z, e1, e2, he2, he1, hee⟩
        rw [← hee]
        apply leOfHom (h2 ⟨_, _, he2⟩)
        exact he1)
  use ex, ey
  -- Now prove that indeed the representatives become equal over `B`.
  -- This will follow by using the fact that our representatives become
  -- equal over the chosen covers.
  ext1 I
  let IS : S.Arrow := I.fromMiddle
  specialize hh IS
  let IW : (W IS).Arrow := I.toMiddle
  apply_fun fun e => e IW at hh
  convert! hh using 1
  · exact x.congr_apply I.middle_spec.symm _
  · exact y.congr_apply I.middle_spec.symm _

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.GrothendieckTopology.Plus.inj_of_sep** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.GrothendieckTopology.Plus`。
形式化陈述：inj_of_sep (P : Cᵒᵖ ⥤ D) (hsep : forall (X : C) (S : J.Cover X) (x y : ToT
ype (P.obj (op X))), (forall I : S.Arrow, P.map I.f.op x = P.map I.f.op y) -> x 
= y) (X : C) : Function.Injective ((J.toPlus P).app (op X))
参数：P : Cᵒᵖ ⥤ D；hsep : forall (X : C) (S : J.Cover X) (x y : ToType (P.obj (op X)
)), (forall I : S.Arrow, P.map I.f.op x = P.map I.f.op y) -> x = y；X : C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.GrothendieckTopology.Plus.eq_mk_iff_exists`：eq_mk_iff_exi
sts {X : C} {P : Cᵒᵖ ⥤ D} {S T : J.Cover X} (x : Meq P S) (y : Meq P T) : mk x =
 mk y ↔ exists (W : J.Cover X) (h1 : W ⟶ S) (h2…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.GrothendieckTopology.Plus.toPlus_eq_mk`：toPlus_eq_mk {X :
 C} {P : Cᵒᵖ ⥤ D} (x : ToType (P.obj (op X))) : (J.toPlus P).app _ x = mk (Meq.m
k ⊤ x)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem inj_of_sep (P : Cᵒᵖ ⥤ D)
    (hsep :
      ∀ (X : C) (S : J.Cover X) (x y : ToType (P.obj (op X))),
        (∀ I : S.Arrow, P.map I.f.op x = P.map I.f.op y) → x = y)
    (X : C) : Function.Injective ((J.toPlus P).app (op X)) := by
  intro x y h
  simp only [toPlus_eq_mk] at h
  rw [eq_mk_iff_exists] at h
  obtain ⟨W, h1, h2, hh⟩ := h
  apply hsep X W
  intro I
  apply_fun fun e => e I at hh
  exact hh

set_option backward.isDefEq.respectTransparency false in
/-- An auxiliary definition to be used in the proof of `exists_of_sep` below.
  Given a compatible family of local sections for `P⁺`, and representatives of said sections,
  construct a compatible family of local sections of `P` over the combination of the covers
  associated to the representatives.
  The separatedness condition is used to prove compatibility among these local sections of `P`. -/
/-
**CategoryTheory.GrothendieckTopology.Plus.meqOfSep** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.GrothendieckTopology.Plus`。
形式化陈述：meqOfSep (P : Cᵒᵖ ⥤ D) (hsep : forall (X : C) (S : J.Cover X) (x y : ToTyp
e (P.obj (op X))), (forall I : S.Arrow, P.map I.f.op x = P.map I.f.op y) -> x = 
y) (X : C) (S : J.Cover X) (s : Meq (J.plusObj P) S) (T : forall I : S.Arrow, J.
Cover I.Y) (t : forall I : S.Arrow, Meq P (T I)) (ht : forall I : S.Arrow, s I =
 mk (t I)) : Meq P (S.bind T) where val I
参数：P : Cᵒᵖ ⥤ D；hsep : forall (X : C) (S : J.Cover X) (x y : ToType (P.obj (op X)
)), (forall I : S.Arrow, P.map I.f.op x = P.map I.f.op y) -> x = y；X : C；S : J.C
over X；s : Meq (J.plusObj P) S；T : forall I : S.Arrow, J.Cover I.Y；t : forall I 
: S.Arrow, Meq P (T I)；ht : forall I : S.Arrow, s I = mk (t I)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An auxiliary definition to be used in the proof of `exists_of_sep` below.
  Given a compatible family of local sections for `P⁺`, and representatives of s
aid sections,
  construct a compatible family of local sections of `P` over the combination of
 the covers
  associated to the representatives.
  The separatedness condition is used to prove compatibility among these local s
ections of `P`.
-/
def meqOfSep (P : Cᵒᵖ ⥤ D)
    (hsep :
      ∀ (X : C) (S : J.Cover X) (x y : ToType (P.obj (op X))),
        (∀ I : S.Arrow, P.map I.f.op x = P.map I.f.op y) → x = y)
    (X : C) (S : J.Cover X) (s : Meq (J.plusObj P) S) (T : ∀ I : S.Arrow, J.Cover I.Y)
    (t : ∀ I : S.Arrow, Meq P (T I)) (ht : ∀ I : S.Arrow, s I = mk (t I)) : Meq P (S.bind T) where
  val I := t I.fromMiddle I.toMiddle
  property := by
    intro II
    apply inj_of_sep P hsep
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, (J.toPlus P).naturality,
      (J.toPlus P).naturality, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
    erw [toPlus_apply (T II.fst.fromMiddle) (t II.fst.fromMiddle) II.fst.toMiddle,
      toPlus_apply (T II.snd.fromMiddle) (t II.snd.fromMiddle) II.snd.toMiddle]
    rw [← ht, ← ht]
    erw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply];
    rw [← (J.plusObj P).map_comp, ← (J.plusObj P).map_comp, ← op_comp, ← op_comp]
    exact s.condition
      { fst.hf := II.fst.from_middle_condition
        snd.hf := II.snd.from_middle_condition
        r.g₁ := II.r.g₁ ≫ II.fst.toMiddleHom
        r.g₂ := II.r.g₂ ≫ II.snd.toMiddleHom
        r.w := by simpa only [Category.assoc, Cover.Arrow.middle_spec] using II.r.w
        .. }
/-
**CategoryTheory.GrothendieckTopology.Plus.exists_of_sep** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.GrothendieckTopology.Plus`。
形式化陈述：exists_of_sep (P : Cᵒᵖ ⥤ D) (hsep : forall (X : C) (S : J.Cover X) (x y : 
ToType (P.obj (op X))), (forall I : S.Arrow, P.map I.f.op x = P.map I.f.op y) ->
 x = y) (X : C) (S : J.Cover X) (s : Meq (J.plusObj P) S) : exists t : ToType ((
J.plusObj P).obj (op X)), Meq.mk S t = s
参数：P : Cᵒᵖ ⥤ D；hsep : forall (X : C) (S : J.Cover X) (x y : ToType (P.obj (op X)
)), (forall I : S.Arrow, P.map I.f.op x = P.map I.f.op y) -> x = y；X : C；S : J.C
over X；s : Meq (J.plusObj P) S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrothendieckTopology.Plus.inj_of_sep`：inj_of_sep (P : Cᵒᵖ
 ⥤ D) (hsep : forall (X : C) (S : J.Cover X) (x y : ToType (P.obj (op X))), (for
all I : S.Arrow, P.map I.f.op x = P.map I…
· 使用定理 `CategoryTheory.Meq.ext`：ext {X} {P : Cᵒᵖ ⥤ D} {S : J.Cover X} (x y : Meq
 P S) (h : forall I : S.Arrow, x I = y I) : x = y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.GrothendieckTopology.Plus.res_mk_eq_mk_pullback`：res_mk_e
q_mk_pullback {Y X : C} {P : Cᵒᵖ ⥤ D} {S : J.Cover X} (x : Meq P S) (f : Y ⟶ X) 
: (J.plusObj P).map f.op (mk x) = mk (x.pullback f)
· 使用定理 `CategoryTheory.GrothendieckTopology.Plus.sep`：sep {X : C} (P : Cᵒᵖ ⥤ D) 
(S : J.Cover X) (x y : ToType ((J.plusObj P).obj (op X))) (h : forall I : S.Arro
w, (J.plusObj P).map I.f.op x = (J…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Sieve.le_pullback_bind`：le_pullback_bind (S : Presieve X)
 (R : forall ⦃Y : C⦄ ⦃f : Y ⟶ X⦄, S f -> Sieve Y) (f : Y ⟶ X) (h : S f) : R h <=
 (bind S R).pullback f
· 使用定理 `CategoryTheory.GrothendieckTopology.Cover.Arrow.hf`：∀ {C : Type u} [inst
 : CategoryTheory.Category.{v, u} C] {X : C} {J : CategoryTheory.GrothendieckTop
ology C}   {S : J.Cover X} (self : S.Arr…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Sieve.downward_closed`：∀ {C : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} C] {X : C} (self : CategoryTheory.Sieve X) {Y Z : C}   {f
 : Y ⟶ X}, self.arrows f →…
· 使用定理 `CategoryTheory.GrothendieckTopology.Plus.toPlus_apply`：toPlus_apply {X :
 C} {P : Cᵒᵖ ⥤ D} (S : J.Cover X) (x : Meq P S) (I : S.Arrow) : (J.toPlus P).app
 _ (x I) = (J.plusObj P).map I.f.op (mk x)
· 使用定理 `CategoryTheory.GrothendieckTopology.Cover.Arrow.middle_spec`：∀ {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C] {J : CategoryTheory.GrothendieckTo
pology C} {X : C}   {S : J.Cover X} {T : (I : S.A…
· 使用定理 `CategoryTheory.Meq.condition`：condition {X} {P : Cᵒᵖ ⥤ D} {S : J.Cover X
} (x : Meq P S) (I : S.Relation) : P.map I.r.g₁.op (x (S.shape.fst I)) = P.map I
.r.g₂.op (x (S.sha…
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `CategoryTheory.GrothendieckTopology.Plus.exists_rep`：exists_rep {X : C} 
{P : Cᵒᵖ ⥤ D} (x : ToType ((J.plusObj P).obj (op X))) : exists (S : J.Cover X) (
y : Meq P S), x = mk y
-/
theorem exists_of_sep (P : Cᵒᵖ ⥤ D)
    (hsep :
      ∀ (X : C) (S : J.Cover X) (x y : ToType (P.obj (op X))),
        (∀ I : S.Arrow, P.map I.f.op x = P.map I.f.op y) → x = y)
    (X : C) (S : J.Cover X) (s : Meq (J.plusObj P) S) :
    ∃ t : ToType ((J.plusObj P).obj (op X)), Meq.mk S t = s := by
  have inj : ∀ X : C, Function.Injective ((J.toPlus P).app (op X)) := inj_of_sep _ hsep
  -- Choose representatives for the given local sections.
  choose T t ht using fun I => exists_rep (s I)
  -- Construct a large cover over which we will define a representative that will
  -- provide the gluing of the given local sections.
  let B : J.Cover X := S.bind T
  choose Z e1 e2 he2 _ _ using fun I : B.Arrow => I.hf
  -- Construct a compatible system of local sections over this large cover, using the chosen
  -- representatives of our local sections.
  -- The compatibility here follows from the separatedness assumption.
  let w : Meq P B := meqOfSep P hsep X S s T t ht
  -- The associated gluing will be the candidate section.
  use mk w
  ext I
  dsimp [Meq.mk]
  rw [ht, res_mk_eq_mk_pullback]
  -- Use the separatedness of `P⁺` to prove that this is indeed a gluing of our
  -- original local sections.
  apply sep P (T I)
  intro II
  simp only [res_mk_eq_mk_pullback, eq_mk_iff_exists]
  -- It suffices to prove equality for representatives over a
  -- convenient sufficiently large cover...
  use (J.pullback II.f).obj (T I)
  let e0 : (J.pullback II.f).obj (T I) ⟶ (J.pullback II.f).obj ((J.pullback I.f).obj B) :=
    homOfLE
      (by
        intro Y f hf
        apply Sieve.le_pullback_bind _ _ _ I.hf
        · cases I
          exact hf)
  use e0, 𝟙 _
  ext IV
  let IA : B.Arrow := ⟨_, (IV.f ≫ II.f) ≫ I.f,
    ⟨I.Y, _, _, I.hf, Sieve.downward_closed _ II.hf _, rfl⟩⟩
  let IB : S.Arrow := IA.fromMiddle
  let IC : (T IB).Arrow := IA.toMiddle
  let ID : (T I).Arrow := ⟨IV.Y, IV.f ≫ II.f, Sieve.downward_closed (T I).1 II.hf IV.f⟩
  change t IB IC = t I ID
  apply inj IV.Y
  rw [toPlus_apply (T I) (t I) ID]
  erw [toPlus_apply (T IB) (t IB) IC]
  rw [← ht, ← ht]
  -- Conclude by constructing the relation showing equality...
  let IR : S.Relation := { fst.hf := IB.hf, snd.hf := I.hf, r.w := IA.middle_spec, .. }
  exact s.condition IR

variable [(forget D).ReflectsIsomorphisms]

set_option backward.isDefEq.respectTransparency false in
/-- If `P` is separated, then `P⁺` is a sheaf. -/
/-
**CategoryTheory.GrothendieckTopology.Plus.isSheaf_of_sep** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.GrothendieckTopology.Plus`。
形式化陈述：isSheaf_of_sep (P : Cᵒᵖ ⥤ D) (hsep : forall (X : C) (S : J.Cover X) (x y :
 ToType (P.obj (op X))), (forall I : S.Arrow, P.map I.f.op x = P.map I.f.op y) -
> x = y) : Presheaf.IsSheaf J (J.plusObj P)
参数：P : Cᵒᵖ ⥤ D；hsep : forall (X : C) (S : J.Cover X) (x y : ToType (P.obj (op X)
)), (forall I : S.Arrow, P.map I.f.op x = P.map I.f.op y) -> x = y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Presheaf.isSheaf_iff_multiequalizer`：isSheaf_iff_multiequ
alizer [forall (X : C) (S : J.Cover X), HasMultiequalizer (S.index P)] : IsSheaf
 J P ↔ forall (X : C) (S : J.Cover X), I…
· 使用定理 `CategoryTheory.isIso_of_reflects_iso`：isIso_of_reflects_iso {A B : C} (f
 : A ⟶ B) (F : C ⥤ D) [IsIso (F.map f)] [F.ReflectsIsomorphisms] : IsIso f
· 使用定理 `CategoryTheory.isIso_iff_bijective`：isIso_iff_bijective {X Y : Type u} (
f : X ⟶ Y) : IsIso f ↔ Function.Bijective f
· 使用定理 `CategoryTheory.GrothendieckTopology.Plus.sep`：sep {X : C} (P : Cᵒᵖ ⥤ D) 
(S : J.Cover X) (x y : ToType ((J.plusObj P).obj (op X))) (h : forall I : S.Arro
w, (J.plusObj P).map I.f.op x = (J…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.Multifork.ofι_π_app`：∀ {C : Type u} [inst : Catego
ryTheory.Category.{v, u} C] {J : CategoryTheory.Limits.MulticospanShape}   (I : 
CategoryTheory.Limits.Multicosp…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.GrothendieckTopology.Plus.exists_of_sep`：exists_of_sep (P
 : Cᵒᵖ ⥤ D) (hsep : forall (X : C) (S : J.Cover X) (x y : ToType (P.obj (op X)))
, (forall I : S.Arrow, P.map I.f.op x = P.ma…
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `CategoryTheory.Meq.ext`：ext {X} {P : Cᵒᵖ ⥤ D} {S : J.Cover X} (x y : Meq
 P S) (h : forall I : S.Arrow, x I = y I) : x = y
· 使用定理 `CategoryTheory.ConcreteCategory.comp_apply`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (
C → Type w)}   {inst_1 : outPara…
· 使用定理 `CategoryTheory.Limits.Multiequalizer.lift_ι`：lift_ι (W : C) (k : forall 
a, W ⟶ I.left a) (h : forall b, k (J.fst b) ≫ I.fst b = k (J.snd b) ≫ I.snd b) (
a) : Multiequalizer.lift I _ k h …

--- 原说明 ---
If `P` is separated, then `P⁺` is a sheaf.
-/
theorem isSheaf_of_sep (P : Cᵒᵖ ⥤ D)
    (hsep :
      ∀ (X : C) (S : J.Cover X) (x y : ToType (P.obj (op X))),
        (∀ I : S.Arrow, P.map I.f.op x = P.map I.f.op y) → x = y) :
    Presheaf.IsSheaf J (J.plusObj P) := by
  rw [Presheaf.isSheaf_iff_multiequalizer]
  intro X S
  apply @isIso_of_reflects_iso _ _ _ _ _ _ _ (forget D) ?_
  rw [isIso_iff_bijective]
  constructor
  · intro x y h
    apply sep P S _ _
    intro I
    apply_fun Meq.equiv (J.plusObj P) S at h
    apply_fun fun e => e I at h
    dsimp only [ConcreteCategory.forget_map_eq_ofHom] at h
    simpa [Meq.equiv_apply, ← comp_apply] using! h
  · rintro (x : ToType (multiequalizer (S.index _)))
    obtain ⟨t, ht⟩ := exists_of_sep P hsep X S (Meq.equiv _ _ x)
    use t
    apply (Meq.equiv (D := D) _ _).injective
    rw [← ht]
    ext i
    dsimp
    rw [← ConcreteCategory.comp_apply, Multiequalizer.lift_ι]
    rfl

variable (J)

include instCC

/-- `P⁺⁺` is always a sheaf. -/
/-
**CategoryTheory.GrothendieckTopology.Plus.isSheaf_plus_plus** 是 Mathlib 中的一个定理，
位于命名空间 `CategoryTheory.GrothendieckTopology.Plus`。
形式化陈述：isSheaf_plus_plus (P : Cᵒᵖ ⥤ D) : Presheaf.IsSheaf J (J.plusObj (J.plusObj
 P))
参数：P : Cᵒᵖ ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrothendieckTopology.Plus.isSheaf_of_sep`：isSheaf_of_sep 
(P : Cᵒᵖ ⥤ D) (hsep : forall (X : C) (S : J.Cover X) (x y : ToType (P.obj (op X)
)), (forall I : S.Arrow, P.map I.f.op x = P.m…
· 使用定理 `CategoryTheory.GrothendieckTopology.Plus.sep`：sep {X : C} (P : Cᵒᵖ ⥤ D) 
(S : J.Cover X) (x y : ToType ((J.plusObj P).obj (op X))) (h : forall I : S.Arro
w, (J.plusObj P).map I.f.op x = (J…

--- 原说明 ---
`P⁺⁺` is always a sheaf.
-/
theorem isSheaf_plus_plus (P : Cᵒᵖ ⥤ D) : Presheaf.IsSheaf J (J.plusObj (J.plusObj P)) := by
  apply isSheaf_of_sep
  intro X S x y
  apply sep

end

end Plus

variable (J)
variable [∀ (P : Cᵒᵖ ⥤ D) (X : C) (S : J.Cover X), HasMultiequalizer (S.index P)]
  [∀ X : C, HasColimitsOfShape (J.Cover X)ᵒᵖ D]

/-- The sheafification of a presheaf `P`.
*NOTE:* Additional hypotheses are needed to obtain a proof that this is a sheaf! -/
/-
**CategoryTheory.GrothendieckTopology.sheafify** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.GrothendieckTopology`。
形式化陈述：sheafify (P : Cᵒᵖ ⥤ D) : Cᵒᵖ ⥤ D
参数：P : Cᵒᵖ ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The sheafification of a presheaf `P`.
*NOTE:* Additional hypotheses are needed to obtain a proof that this is a sheaf!
-/
noncomputable def sheafify (P : Cᵒᵖ ⥤ D) : Cᵒᵖ ⥤ D :=
  J.plusObj (J.plusObj P)

/-- The canonical map from `P` to its sheafification. -/
/-
**CategoryTheory.GrothendieckTopology.toSheafify** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.GrothendieckTopology`。
形式化陈述：toSheafify (P : Cᵒᵖ ⥤ D) : P ⟶ J.sheafify P
参数：P : Cᵒᵖ ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical map from `P` to its sheafification.
-/
noncomputable def toSheafify (P : Cᵒᵖ ⥤ D) : P ⟶ J.sheafify P :=
  J.toPlus P ≫ J.plusMap (J.toPlus P)

/-- The canonical map on sheafifications induced by a morphism. -/
/-
**CategoryTheory.GrothendieckTopology.sheafifyMap** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.GrothendieckTopology`。
形式化陈述：sheafifyMap {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) : J.sheafify P ⟶ J.sheafify Q
参数：η : P ⟶ Q。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical map on sheafifications induced by a morphism.
-/
noncomputable def sheafifyMap {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) : J.sheafify P ⟶ J.sheafify Q :=
  J.plusMap <| J.plusMap η

@[simp]
/-
**CategoryTheory.GrothendieckTopology.sheafifyMap_id** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.GrothendieckTopology`。
形式化陈述：sheafifyMap_id (P : Cᵒᵖ ⥤ D) : J.sheafifyMap (𝟙 P) = 𝟙 (J.sheafify P)
参数：P : Cᵒᵖ ⥤ D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.GrothendieckTopology.plusMap_id`：plusMap_id (P : Cᵒᵖ ⥤ D)
 : J.plusMap (𝟙 P) = 𝟙 _
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sheafifyMap_id (P : Cᵒᵖ ⥤ D) : J.sheafifyMap (𝟙 P) = 𝟙 (J.sheafify P) := by
  dsimp [sheafifyMap, sheafify]
  simp

@[simp]
/-
**CategoryTheory.GrothendieckTopology.sheafifyMap_comp** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.GrothendieckTopology`。
形式化陈述：sheafifyMap_comp {P Q R : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (γ : Q ⟶ R) : J.sheafifyMap
 (η ≫ γ) = J.sheafifyMap η ≫ J.sheafifyMap γ
参数：η : P ⟶ Q；γ : Q ⟶ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.GrothendieckTopology.plusMap_comp`：plusMap_comp {P Q R : 
Cᵒᵖ ⥤ D} (η : P ⟶ Q) (γ : Q ⟶ R) : J.plusMap (η ≫ γ) = J.plusMap η ≫ J.plusMap γ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sheafifyMap_comp {P Q R : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (γ : Q ⟶ R) :
    J.sheafifyMap (η ≫ γ) = J.sheafifyMap η ≫ J.sheafifyMap γ := by
  dsimp [sheafifyMap, sheafify]
  simp

@[reassoc (attr := simp)]
/-
**CategoryTheory.GrothendieckTopology.toSheafify_naturality** 是 Mathlib 中的一个定理，位
于命名空间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：toSheafify_naturality {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) : η ≫ J.toSheafify _ = J
.toSheafify _ ≫ J.sheafifyMap η
参数：η : P ⟶ Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.GrothendieckTopology.plusMap_toPlus`：plusMap_toPlus : J.p
lusMap (J.toPlus P) = J.toPlus (J.plusObj P)
· 使用定理 `CategoryTheory.GrothendieckTopology.toPlus_naturality`：toPlus_naturality
 {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) : η ≫ J.toPlus Q = J.toPlus _ ≫ J.plusMap η
· 使用定理 `CategoryTheory.GrothendieckTopology.toPlus_naturality_assoc`：∀ {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C] (J : CategoryTheory.GrothendieckTo
pology C) {D : Type w}   [inst_1 : CategoryTheory…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toSheafify_naturality {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) :
    η ≫ J.toSheafify _ = J.toSheafify _ ≫ J.sheafifyMap η := by
  dsimp [sheafifyMap, sheafify, toSheafify]
  simp

variable (D)

/-- The sheafification of a presheaf `P`, as a functor.
*NOTE:* Additional hypotheses are needed to obtain a proof that this is a sheaf! -/
/-
**CategoryTheory.GrothendieckTopology.sheafification** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.GrothendieckTopology`。
形式化陈述：sheafification : (Cᵒᵖ ⥤ D) ⥤ Cᵒᵖ ⥤ D
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The sheafification of a presheaf `P`, as a functor.
*NOTE:* Additional hypotheses are needed to obtain a proof that this is a sheaf!
-/
noncomputable def sheafification : (Cᵒᵖ ⥤ D) ⥤ Cᵒᵖ ⥤ D :=
  J.plusFunctor D ⋙ J.plusFunctor D

@[simp]
/-
**CategoryTheory.GrothendieckTopology.sheafification_obj** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：sheafification_obj (P : Cᵒᵖ ⥤ D) : (J.sheafification D).obj P = J.sheafify
 P
参数：P : Cᵒᵖ ⥤ D。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sheafification_obj (P : Cᵒᵖ ⥤ D) : (J.sheafification D).obj P = J.sheafify P :=
  rfl

@[simp]
/-
**CategoryTheory.GrothendieckTopology.sheafification_map** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：sheafification_map {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) : (J.sheafification D).map 
η = J.sheafifyMap η
参数：η : P ⟶ Q。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sheafification_map {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) :
    (J.sheafification D).map η = J.sheafifyMap η :=
  rfl

/-- The canonical map from `P` to its sheafification, as a natural transformation.
*Note:* We only show this is a sheaf under additional hypotheses on `D`. -/
/-
**CategoryTheory.GrothendieckTopology.toSheafification** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.GrothendieckTopology`。
形式化陈述：toSheafification : 𝟭 _ ⟶ sheafification J D
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical map from `P` to its sheafification, as a natural transformation.
*Note:* We only show this is a sheaf under additional hypotheses on `D`.
-/
noncomputable def toSheafification : 𝟭 _ ⟶ sheafification J D :=
  J.toPlusNatTrans D ≫ Functor.whiskerRight (J.toPlusNatTrans D) (J.plusFunctor D)

@[simp]
/-
**CategoryTheory.GrothendieckTopology.toSheafification_app** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：toSheafification_app (P : Cᵒᵖ ⥤ D) : (J.toSheafification D).app P = J.toSh
eafify P
参数：P : Cᵒᵖ ⥤ D。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toSheafification_app (P : Cᵒᵖ ⥤ D) :
    (J.toSheafification D).app P = J.toSheafify P :=
  rfl

variable {D}

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.GrothendieckTopology.isIso_toSheafify** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.GrothendieckTopology`。
形式化陈述：isIso_toSheafify {P : Cᵒᵖ ⥤ D} (hP : Presheaf.IsSheaf J P) : IsIso (J.toSh
eafify P)
参数：hP : Presheaf.IsSheaf J P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrothendieckTopology.isIso_toPlus_of_isSheaf`：isIso_toPlu
s_of_isSheaf (hP : Presheaf.IsSheaf J P) : IsIso (J.toPlus P)
-/
theorem isIso_toSheafify {P : Cᵒᵖ ⥤ D} (hP : Presheaf.IsSheaf J P) : IsIso (J.toSheafify P) := by
  dsimp [toSheafify]
  have := isIso_toPlus_of_isSheaf J P hP
  change (IsIso (toPlus J P ≫ (J.plusFunctor D).map (toPlus J P)))
  infer_instance

/-- If `P` is a sheaf, then `P` is isomorphic to `J.sheafify P`. -/
/-
**CategoryTheory.GrothendieckTopology.isoSheafify** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.GrothendieckTopology`。
形式化陈述：isoSheafify {P : Cᵒᵖ ⥤ D} (hP : Presheaf.IsSheaf J P) : P ≅ J.sheafify P
参数：hP : Presheaf.IsSheaf J P。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrothendieckTopology.isIso_toSheafify`：isIso_toSheafify {
P : Cᵒᵖ ⥤ D} (hP : Presheaf.IsSheaf J P) : IsIso (J.toSheafify P)

--- 原说明 ---
If `P` is a sheaf, then `P` is isomorphic to `J.sheafify P`.
-/
noncomputable def isoSheafify {P : Cᵒᵖ ⥤ D} (hP : Presheaf.IsSheaf J P) : P ≅ J.sheafify P :=
  letI := isIso_toSheafify J hP
  asIso (J.toSheafify P)

@[simp]
/-
**CategoryTheory.GrothendieckTopology.isoSheafify_hom** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.GrothendieckTopology`。
形式化陈述：isoSheafify_hom {P : Cᵒᵖ ⥤ D} (hP : Presheaf.IsSheaf J P) : (J.isoSheafify
 hP).hom = J.toSheafify P
参数：hP : Presheaf.IsSheaf J P。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isoSheafify_hom {P : Cᵒᵖ ⥤ D} (hP : Presheaf.IsSheaf J P) :
    (J.isoSheafify hP).hom = J.toSheafify P :=
  rfl

/-- Given a sheaf `Q` and a morphism `P ⟶ Q`, construct a morphism from `J.sheafify P` to `Q`. -/
/-
**CategoryTheory.GrothendieckTopology.sheafifyLift** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.GrothendieckTopology`。
形式化陈述：sheafifyLift {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (hQ : Presheaf.IsSheaf J Q) : J.s
heafify P ⟶ Q
参数：η : P ⟶ Q；hQ : Presheaf.IsSheaf J Q。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a sheaf `Q` and a morphism `P ⟶ Q`, construct a morphism from `J.sheafify 
P` to `Q`.
-/
noncomputable def sheafifyLift {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (hQ : Presheaf.IsSheaf J Q) :
    J.sheafify P ⟶ Q :=
  J.plusLift (J.plusLift η hQ) hQ

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.GrothendieckTopology.toSheafify_sheafifyLift** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：toSheafify_sheafifyLift {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (hQ : Presheaf.IsSheaf
 J Q) : J.toSheafify P ≫ sheafifyLift J η hQ = η
参数：η : P ⟶ Q；hQ : Presheaf.IsSheaf J Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.GrothendieckTopology.plusMap_toPlus`：plusMap_toPlus : J.p
lusMap (J.toPlus P) = J.toPlus (J.plusObj P)
· 使用定理 `CategoryTheory.GrothendieckTopology.toPlus_naturality`：toPlus_naturality
 {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) : η ≫ J.toPlus Q = J.toPlus _ ≫ J.plusMap η
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.GrothendieckTopology.toPlus_plusLift`：toPlus_plusLift {P 
Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (hQ : Presheaf.IsSheaf J Q) : J.toPlus P ≫ J.plusLift η
 hQ = η
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toSheafify_sheafifyLift {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (hQ : Presheaf.IsSheaf J Q) :
    J.toSheafify P ≫ sheafifyLift J η hQ = η := by
  dsimp only [sheafifyLift, toSheafify]
  simp

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.GrothendieckTopology.sheafifyLift_unique** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：sheafifyLift_unique {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (hQ : Presheaf.IsSheaf J Q
) (γ : J.sheafify P ⟶ Q) : J.toSheafify P ≫ γ = η -> γ = sheafifyLift J η hQ
参数：η : P ⟶ Q；hQ : Presheaf.IsSheaf J Q；γ : J.sheafify P ⟶ Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrothendieckTopology.plusLift_unique`：plusLift_unique {P 
Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (hQ : Presheaf.IsSheaf J Q) (γ : J.plusObj P ⟶ Q) (hγ :
 J.toPlus P ≫ γ = η) : γ = J.plusLift η h…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.GrothendieckTopology.plusMap_toPlus`：plusMap_toPlus : J.p
lusMap (J.toPlus P) = J.toPlus (J.plusObj P)
-/
theorem sheafifyLift_unique {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (hQ : Presheaf.IsSheaf J Q)
    (γ : J.sheafify P ⟶ Q) : J.toSheafify P ≫ γ = η → γ = sheafifyLift J η hQ := by
  intro h
  apply plusLift_unique
  apply plusLift_unique
  rw [← Category.assoc, ← plusMap_toPlus]
  exact h

@[simp]
/-
**CategoryTheory.GrothendieckTopology.isoSheafify_inv** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.GrothendieckTopology`。
形式化陈述：isoSheafify_inv {P : Cᵒᵖ ⥤ D} (hP : Presheaf.IsSheaf J P) : (J.isoSheafify
 hP).inv = J.sheafifyLift (𝟙 _) hP
参数：hP : Presheaf.IsSheaf J P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrothendieckTopology.sheafifyLift_unique`：sheafifyLift_un
ique {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (hQ : Presheaf.IsSheaf J Q) (γ : J.sheafify P ⟶
 Q) : J.toSheafify P ≫ γ = η -> γ = sheafifyL…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem isoSheafify_inv {P : Cᵒᵖ ⥤ D} (hP : Presheaf.IsSheaf J P) :
    (J.isoSheafify hP).inv = J.sheafifyLift (𝟙 _) hP := by
  apply J.sheafifyLift_unique
  simp [Iso.comp_inv_eq]

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.GrothendieckTopology.sheafify_hom_ext** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.GrothendieckTopology`。
形式化陈述：sheafify_hom_ext {P Q : Cᵒᵖ ⥤ D} (η γ : J.sheafify P ⟶ Q) (hQ : Presheaf.I
sSheaf J Q) (h : J.toSheafify P ≫ η = J.toSheafify P ≫ γ) : η = γ
参数：η γ : J.sheafify P ⟶ Q；hQ : Presheaf.IsSheaf J Q；h : J.toSheafify P ≫ η = J.t
oSheafify P ≫ γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrothendieckTopology.plus_hom_ext`：plus_hom_ext {P Q : Cᵒ
ᵖ ⥤ D} (η γ : J.plusObj P ⟶ Q) (hQ : Presheaf.IsSheaf J Q) (h : J.toPlus P ≫ η =
 J.toPlus P ≫ γ) : η = γ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.GrothendieckTopology.plusMap_toPlus`：plusMap_toPlus : J.p
lusMap (J.toPlus P) = J.toPlus (J.plusObj P)
-/
theorem sheafify_hom_ext {P Q : Cᵒᵖ ⥤ D} (η γ : J.sheafify P ⟶ Q) (hQ : Presheaf.IsSheaf J Q)
    (h : J.toSheafify P ≫ η = J.toSheafify P ≫ γ) : η = γ := by
  apply J.plus_hom_ext _ _ hQ
  apply J.plus_hom_ext _ _ hQ
  rw [← Category.assoc, ← Category.assoc, ← plusMap_toPlus]
  exact h

@[reassoc (attr := simp)]
/-
**CategoryTheory.GrothendieckTopology.sheafifyMap_sheafifyLift** 是 Mathlib 中的一个定
理，位于命名空间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：sheafifyMap_sheafifyLift {P Q R : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (γ : Q ⟶ R) (hR : P
resheaf.IsSheaf J R) : J.sheafifyMap η ≫ J.sheafifyLift γ hR = J.sheafifyLift (η
 ≫ γ) hR
参数：η : P ⟶ Q；γ : Q ⟶ R；hR : Presheaf.IsSheaf J R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrothendieckTopology.sheafifyLift_unique`：sheafifyLift_un
ique {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (hQ : Presheaf.IsSheaf J Q) (γ : J.sheafify P ⟶
 Q) : J.toSheafify P ≫ γ = η -> γ = sheafifyL…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.GrothendieckTopology.toSheafify_naturality`：toSheafify_na
turality {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) : η ≫ J.toSheafify _ = J.toSheafify _ ≫ J.s
heafifyMap η
· 使用定理 `CategoryTheory.GrothendieckTopology.toSheafify_sheafifyLift`：toSheafify_
sheafifyLift {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (hQ : Presheaf.IsSheaf J Q) : J.toSheaf
ify P ≫ sheafifyLift J η hQ = η
-/
theorem sheafifyMap_sheafifyLift {P Q R : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (γ : Q ⟶ R)
    (hR : Presheaf.IsSheaf J R) :
    J.sheafifyMap η ≫ J.sheafifyLift γ hR = J.sheafifyLift (η ≫ γ) hR := by
  apply J.sheafifyLift_unique
  rw [← Category.assoc, ← J.toSheafify_naturality, Category.assoc, toSheafify_sheafifyLift]

end GrothendieckTopology

variable (J)
variable {FD : D → D → Type*} {CD : D → Type t} [∀ X Y, FunLike (FD X Y) (CD X) (CD Y)]
variable [instCC : ConcreteCategory.{t} D FD]
  [∀ {X : C} (S : J.Cover X), PreservesLimitsOfShape (WalkingMulticospan S.shape) (forget D)]
  [∀ (P : Cᵒᵖ ⥤ D) (X : C) (S : J.Cover X), HasMultiequalizer (S.index P)]
  [∀ X : C, HasColimitsOfShape (J.Cover X)ᵒᵖ D]
  [∀ X : C, PreservesColimitsOfShape (J.Cover X)ᵒᵖ (forget D)] [(forget D).ReflectsIsomorphisms]

include instCC in
/-
**CategoryTheory.GrothendieckTopology.sheafify_isSheaf** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.GrothendieckTopology`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (J : CategoryTheo
ry.GrothendieckTopology C) {D : Type w}   [inst_1 : CategoryTheory.Category.{w',
 w} D] {FD : D → D → Type u_1} {CD : D → Type t}   [inst_2 : (X Y : D) → FunLike
 (FD X Y) (CD X) (CD Y)] [instCC : CategoryTheory.ConcreteCategory D FD]   [∀ {X
 : C} (S : J.Cover X),       CategoryTheory.Limits.PreservesLimitsOfShape (Categ
oryTheory.Limits.WalkingMulticospan S.shape)         (CategoryTheory.forget D)] 
  [inst_4 :     ∀ (P : CategoryTheory.Functor Cᵒᵖ D) (X : C) (S : J.Cover X), Ca
tegoryTheory.Limits.HasMultiequalizer (S.index P)]   [inst_5 : ∀ (X : C), Catego
ryTheory.Limits.HasColimitsOfShape (J.Cover X)ᵒᵖ D]   [∀ (X : C), CategoryTheory
.Limits.PreservesColimitsOfShape (J.Cover X)ᵒᵖ (CategoryTheory.forget D)]   [(Ca
tegoryTheory.forget D).ReflectsIsomorphisms] (P : CategoryTheory.Functor Cᵒᵖ D),
   CategoryTheory.Presheaf.IsSheaf J (J.sheafify P)
参数：J : CategoryTheory.GrothendieckTopology C；X Y : D；FD X Y；CD X；CD Y；S : J.Cove
r X；CategoryTheory.Limits.WalkingMulticospan S.shape；CategoryTheory.forget D；P :
 CategoryTheory.Functor Cᵒᵖ D；X : C；S : J.Cover X；S.index P；X : C；J.Cover X；X : 
C；J.Cover X；CategoryTheory.forget D；CategoryTheory.forget D；P : CategoryTheory.F
unctor Cᵒᵖ D；J.sheafify P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrothendieckTopology.Plus.isSheaf_plus_plus`：isSheaf_plus
_plus (P : Cᵒᵖ ⥤ D) : Presheaf.IsSheaf J (J.plusObj (J.plusObj P))
-/
theorem GrothendieckTopology.sheafify_isSheaf (P : Cᵒᵖ ⥤ D) : Presheaf.IsSheaf J (J.sheafify P) :=
  GrothendieckTopology.Plus.isSheaf_plus_plus _ _

variable (D)

/-- The sheafification functor, as a functor taking values in `Sheaf`. -/
@[simps]
/-
**CategoryTheory.plusPlusSheaf** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：plusPlusSheaf : (Cᵒᵖ ⥤ D) ⥤ Sheaf J D where obj P
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrothendieckTopology.sheafify_isSheaf`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] (J : CategoryTheory.GrothendieckTopology 
C) {D : Type w}   [inst_1 : CategoryTheory…

--- 原说明 ---
The sheafification functor, as a functor taking values in `Sheaf`.
-/
noncomputable def plusPlusSheaf : (Cᵒᵖ ⥤ D) ⥤ Sheaf J D where
  obj P := ⟨J.sheafify P, J.sheafify_isSheaf P⟩
  map η := ⟨J.sheafifyMap η⟩

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.plusPlusSheaf_preservesZeroMorphisms** 是 Mathlib 中的一个实例，位于命名空间 
`CategoryTheory`。
形式化陈述：plusPlusSheaf_preservesZeroMorphisms [Preadditive D] : (plusPlusSheaf J D)
.PreservesZeroMorphisms where map_zero F G
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ObjectProperty.hom_ext`：hom_ext {X Y : P.FullSubcategory}
 {f g : X ⟶ Y} (h : f.hom = g.hom) : f = g
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.Limits.colimit.hom_ext`：∀ {J : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u}
 C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.colimit.ι_map`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C
]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.GrothendieckTopology.plusMap_zero`：plusMap_zero [Preaddit
ive D] (P Q : Cᵒᵖ ⥤ D) : J.plusMap (0 : P ⟶ Q) = 0
· 使用定理 `CategoryTheory.GrothendieckTopology.diagramNatTrans_zero`：diagramNatTran
s_zero [Preadditive D] (X : C) (P Q : Cᵒᵖ ⥤ D) : J.diagramNatTrans (0 : P ⟶ Q) X
 = 0
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance plusPlusSheaf_preservesZeroMorphisms [Preadditive D] :
    (plusPlusSheaf J D).PreservesZeroMorphisms where
  map_zero F G := by
    ext : 3
    refine colimit.hom_ext (fun j => ?_)
    erw [colimit.ι_map, comp_zero]
    simp

set_option backward.isDefEq.respectTransparency false in
/-- The sheafification functor is left adjoint to the forgetful functor. -/
--@[simps! unit_app counit_app_val]
/-
**CategoryTheory.plusPlusAdjunction** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：plusPlusAdjunction : plusPlusSheaf J D ⊣ sheafToPresheaf J D
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def plusPlusAdjunction : plusPlusSheaf J D ⊣ sheafToPresheaf J D :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun P Q =>
        { toFun := fun e => J.toSheafify P ≫ e.hom
          invFun := fun e => ⟨J.sheafifyLift e Q.2⟩
          left_inv := fun _ => Sheaf.hom_ext <| (J.sheafifyLift_unique _ _ _ rfl).symm
          right_inv := fun _ => J.toSheafify_sheafifyLift _ _ }
      homEquiv_naturality_left_symm := by
        intro P Q R η γ; ext1; dsimp; symm
        apply J.sheafifyMap_sheafifyLift
      homEquiv_naturality_right := fun η γ => by
        dsimp
        rw [Category.assoc] }
/-
**CategoryTheory.sheafToPresheaf_isRightAdjoint** 是 Mathlib 中的一个实例，位于命名空间 `Categ
oryTheory`。
形式化陈述：sheafToPresheaf_isRightAdjoint : (sheafToPresheaf J D).IsRightAdjoint
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Adjunction.isRightAdjoint`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F : CategoryTheor…
-/
instance sheafToPresheaf_isRightAdjoint : (sheafToPresheaf J D).IsRightAdjoint :=
  (plusPlusAdjunction J D).isRightAdjoint
/-
**CategoryTheory.presheaf_mono_of_mono** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory
`。
形式化陈述：presheaf_mono_of_mono {F G : Sheaf J D} (f : F ⟶ G) [Mono f] : Mono f.1
参数：f : F ⟶ G。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.map_mono`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (F : CategoryTheor…
· 使用定理 `CategoryTheory.preservesMonomorphisms_of_preservesLimitsOfShape`：∀ {C : 
Type u₁} {D : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.instPreservesLimitsOfShapeOfIsRightAdjoint`：∀ {J 
: Type u_1} {C : Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_1, 
u_1} J]   [inst_1 : CategoryTheory.Category.{v_2, u_2} …
-/
instance presheaf_mono_of_mono {F G : Sheaf J D} (f : F ⟶ G) [Mono f] : Mono f.1 :=
  (sheafToPresheaf J D).map_mono _

include instCC in
/-
**CategoryTheory.Sheaf.Hom.mono_iff_presheaf_mono** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Sheaf.Hom`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (J : CategoryTheo
ry.GrothendieckTopology C) (D : Type w)   [inst_1 : CategoryTheory.Category.{w',
 w} D] {FD : D → D → Type u_1} {CD : D → Type t}   [inst_2 : (X Y : D) → FunLike
 (FD X Y) (CD X) (CD Y)] [instCC : CategoryTheory.ConcreteCategory D FD]   [∀ {X
 : C} (S : J.Cover X),       CategoryTheory.Limits.PreservesLimitsOfShape (Categ
oryTheory.Limits.WalkingMulticospan S.shape)         (CategoryTheory.forget D)] 
  [∀ (P : CategoryTheory.Functor Cᵒᵖ D) (X : C) (S : J.Cover X), CategoryTheory.
Limits.HasMultiequalizer (S.index P)]   [∀ (X : C), CategoryTheory.Limits.HasCol
imitsOfShape (J.Cover X)ᵒᵖ D]   [∀ (X : C), CategoryTheory.Limits.PreservesColim
itsOfShape (J.Cover X)ᵒᵖ (CategoryTheory.forget D)]   [(CategoryTheory.forget D)
.ReflectsIsomorphisms] {F G : CategoryTheory.Sheaf J D} (f : F ⟶ G),   CategoryT
heory.Mono f ↔ CategoryTheory.Mono f.hom
参数：J : CategoryTheory.GrothendieckTopology C；D : Type w；X Y : D；FD X Y；CD X；CD Y
；S : J.Cover X；CategoryTheory.Limits.WalkingMulticospan S.shape；CategoryTheory.f
orget D；P : CategoryTheory.Functor Cᵒᵖ D；X : C；S : J.Cover X；S.index P；X : C；J.C
over X；X : C；J.Cover X；CategoryTheory.forget D；CategoryTheory.forget D；f : F ⟶ G
。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Sheaf.Hom.mono_of_presheaf_mono`：∀ {C : Type u₁} [inst : 
CategoryTheory.Category.{v₁, u₁} C] (J : CategoryTheory.GrothendieckTopology C) 
(A : Type u₂)   [inst_1 : CategoryTh…
-/
theorem Sheaf.Hom.mono_iff_presheaf_mono {F G : Sheaf J D} (f : F ⟶ G) : Mono f ↔ Mono f.1 :=
  ⟨fun m => by infer_instance, fun m => by exact Sheaf.Hom.mono_of_presheaf_mono J D f⟩

end CategoryTheory

