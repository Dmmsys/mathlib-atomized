/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Yoneda

/-!
# `IsRepresentedBy` predicate

In this file we define the predicate `IsRepresentedBy`: A presheaf `F` is represented by `X`
with universal element `x : F.obj X` if the natural transformation `yoneda.obj X ⟶ F` induced
by `x` is an isomorphism.

For other declarations expressing a functor is representable, see also:

- `CategoryTheory.Functor.RepresentableBy`:
  Structure bundling an explicit natural isomorphism `yoneda.obj X ⟶ F`.
- `CategoryTheory.Functor.IsRepresentable`:
  Predicate asserting the existence of a representing object.

The relations to these other notions are given as
`CategoryTheory.Functor.IsRepresentable.iff_exists_isRepresentedBy` and
`CategoryTheory.Functor.IsRepresentedBy.iff_exists_representableBy`.

## TODOs

- Dualize to `IsCorepresentedBy`.
-/

@[expose] public section

universe w v u

namespace CategoryTheory.Functor

open Opposite

variable {C : Type u} [Category.{v} C]

/--
A presheaf `F` is represented by `X` with universal element `x : F.obj X`
if the natural transformation `yoneda.obj X ⟶ F` induced by `x` is an isomorphism.
For better universe generality, we state this manually as for every `Y`, the
induced map `(Y ⟶ X) → F.obj Y` is bijective.
-/
@[mk_iff]
/-
**CategoryTheory.Functor.IsRepresentedBy** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTh
eory.Functor`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     (F : Cate
goryTheory.Functor Cᵒᵖ (Type w)) → {X : C} → F.obj (Opposite.op X) → Prop
参数：F : CategoryTheory.Functor Cᵒᵖ (Type w)；Opposite.op X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A presheaf `F` is represented by `X` with universal element `x : F.obj X`
if the natural transformation `yoneda.obj X ⟶ F` induced by `x` is an isomorphis
m.
For better universe generality, we state this manually as for every `Y`, the
induced map `(Y ⟶ X) → F.obj Y` is bijective.
-/
structure IsRepresentedBy (F : Cᵒᵖ ⥤ Type w) {X : C} (x : F.obj (op X)) : Prop where
  map_bijective {Y : C} : Function.Bijective (fun f : Y ⟶ X ↦ F.map f.op x)

variable {F : Cᵒᵖ ⥤ Type w} {X : C} {x : F.obj (op X)}

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Functor.IsRepresentedBy.iff_isIso_uliftYonedaEquiv** 是 Mathlib 
中的一个定理，位于命名空间 `CategoryTheory.Functor.IsRepresentedBy`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {F : CategoryTheo
ry.Functor Cᵒᵖ (Type w)} {X : C}   {x : F.obj (Opposite.op X)},   F.IsRepresente
dBy x ↔ CategoryTheory.IsIso (CategoryTheory.uliftYonedaEquiv.symm { down := x }
)
参数：Type w；Opposite.op X；CategoryTheory.uliftYonedaEquiv.symm { down := x }。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.isRepresentedBy_iff`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] (F : CategoryTheory.Functor Cᵒᵖ (Type w)) {X : C}  
 (x : F.obj (Opposite.op X)),   …
· 使用定理 `CategoryTheory.NatTrans.isIso_iff_isIso_app`：∀ {C : Type u₁} [inst : Cat
egoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category
.{v₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `Opposite.op_surjective`：op_surjective : Function.Surjective (op : α -> α
ᵒᵖ)
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `CategoryTheory.isIso_iff_bijective`：isIso_iff_bijective {X Y : Type u} (
f : X ⟶ Y) : IsIso f ↔ Function.Bijective f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Bijective.of_comp_iff`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sor
t u_3} (f : α → β) {g : γ → α},   Function.Bijective g → (Function.Bijective (f 
∘ g) ↔ Function.Bije…
· 使用定理 `Equiv.bijective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Bijec
tive ⇑e
· 使用定理 `Function.Bijective.of_comp_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {γ : So
rt u_3} {f : α → β},   Function.Bijective f → ∀ (g : γ → α), Function.Bijective 
(f ∘ g) ↔ Function.Bi…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma IsRepresentedBy.iff_isIso_uliftYonedaEquiv :
    F.IsRepresentedBy x ↔
      IsIso ((uliftYonedaEquiv (F := F ⋙ uliftFunctor.{v})).symm ⟨x⟩) := by
  rw [isRepresentedBy_iff, NatTrans.isIso_iff_isIso_app, Opposite.op_surjective.forall]
  refine forall_congr' fun Y ↦ ?_
  rw [isIso_iff_bijective, ← Function.Bijective.of_comp_iff _ Equiv.ulift.{w}.symm.bijective,
    ← Function.Bijective.of_comp_iff' Equiv.ulift.{v}.bijective]
  rfl

/-- If `F` is represented by `X` with universal element `x : F.obj X`, modulo universe
lifting, it is isomorphic to `yoneda.obj X`. -/
@[simps! hom]
/-
**CategoryTheory.Functor.IsRepresentedBy.uliftYonedaIso** 是 Mathlib 中的一个定义，位于命名空
间 `CategoryTheory.Functor.IsRepresentedBy`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {F : Cate
goryTheory.Functor Cᵒᵖ (Type w)} →       {X : C} →         {x : F.obj (Opposite.
op X)} →           F.IsRepresentedBy x → (CategoryTheory.uliftYoneda.{w, v, u}.o
bj X ≅ F.comp CategoryTheory.uliftFunctor.{v, w})
参数：Type w；Opposite.op X；CategoryTheory.uliftYoneda.{w, v, u}.obj X ≅ F.comp Cate
goryTheory.uliftFunctor.{v, w}。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
If `F` is represented by `X` with universal element `x : F.obj X`, modulo univer
se
lifting, it is isomorphic to `yoneda.obj X`.
-/
noncomputable def IsRepresentedBy.uliftYonedaIso (h : F.IsRepresentedBy x) :
    uliftYoneda.obj X ≅ F ⋙ uliftFunctor.{v} :=
  haveI : IsIso ((uliftYonedaEquiv (F := F ⋙ uliftFunctor.{v})).symm ⟨x⟩) := by
    rwa [IsRepresentedBy.iff_isIso_uliftYonedaEquiv] at h
  asIso <| (uliftYonedaEquiv (F := F ⋙ uliftFunctor.{v})).symm ⟨x⟩

/-- The canonical representation induced by the universal element `x : F.obj X`. -/
/-
**CategoryTheory.Functor.IsRepresentedBy.representableBy** 是 Mathlib 中的一个定义，位于命名
空间 `CategoryTheory.Functor.IsRepresentedBy`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {F : Cate
goryTheory.Functor Cᵒᵖ (Type w)} →       {X : C} → {x : F.obj (Opposite.op X)} →
 F.IsRepresentedBy x → F.RepresentableBy X
参数：Type w；Opposite.op X。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The canonical representation induced by the universal element `x : F.obj X`.
-/
noncomputable def IsRepresentedBy.representableBy (h : F.IsRepresentedBy x) :
    F.RepresentableBy X :=
  Functor.representableByUliftFunctorEquiv.{v}
    ((RepresentableBy.equivUliftYonedaIso _ _).symm <| h.uliftYonedaIso)

@[simp]
/-
**CategoryTheory.Functor.IsRepresentedBy.representableBy_homEquiv_apply** 是 Math
lib 中的一个定理，位于命名空间 `CategoryTheory.Functor.IsRepresentedBy`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {F : CategoryTheo
ry.Functor Cᵒᵖ (Type w)} {X : C}   {x : F.obj (Opposite.op X)} (h : F.IsRepresen
tedBy x) {Y : C} (f : Y ⟶ X),   h.representableBy.homEquiv f = (CategoryTheory.C
oncreteCategory.hom (F.map f.op)) x
参数：Type w；Opposite.op X；h : F.IsRepresentedBy x；f : Y ⟶ X；CategoryTheory.Concret
eCategory.hom (F.map f.op)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma IsRepresentedBy.representableBy_homEquiv_apply (h : F.IsRepresentedBy x)
    {Y : C} (f : Y ⟶ X) :
    h.representableBy.homEquiv f = F.map f.op x :=
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Functor.RepresentableBy.isRepresentedBy** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.Functor.RepresentableBy`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {F : CategoryTheo
ry.Functor Cᵒᵖ (Type w)} {X : C}   (R : F.RepresentableBy X), F.IsRepresentedBy 
(R.homEquiv (CategoryTheory.CategoryStruct.id X))
参数：Type w；R : F.RepresentableBy X；R.homEquiv (CategoryTheory.CategoryStruct.id X
)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.IsRepresentedBy.iff_isIso_uliftYonedaEquiv`：∀ {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C] {F : CategoryTheory.Functor 
Cᵒᵖ (Type w)} {X : C}   {x : F.obj (Opposite.op X)},   …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.ConcreteCategory.ext`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y
 : C) → FunLike (FC X Y) …
· 使用定理 `TypeCat.Fun.ext`：∀ {X : Type u_1} {Y : Type u_2} {x y : TypeCat.Fun X Y}
, x.toFun = y.toFun → x = y
· 使用定理 `ULift.up.injEq`：∀ {α : Type s} (down down_1 : α), ({ down := down } = { 
down := down_1 }) = (down = down_1)
· 使用定理 `CategoryTheory.Functor.RepresentableBy.homEquiv_eq`：∀ {C : Type u₁} [ins
t : CategoryTheory.Category.{v₁, u₁} C] {F : CategoryTheory.Functor Cᵒᵖ (Type v)
} {Y : C}   (e : F.RepresentableBy Y) {X…
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
-/
lemma RepresentableBy.isRepresentedBy (R : F.RepresentableBy X) :
    F.IsRepresentedBy (R.homEquiv (𝟙 X)) := by
  rw [IsRepresentedBy.iff_isIso_uliftYonedaEquiv]
  convert!
    (RepresentableBy.equivUliftYonedaIso _ _ <|
        representableByUliftFunctorEquiv.{v}.symm R).isIso_hom
  ext
  simpa [uliftYonedaEquiv] using (homEquiv_eq _ _).symm
/-
**CategoryTheory.Functor.IsRepresentedBy.iff_exists_representableBy** 是 Mathlib 
中的一个定理，位于命名空间 `CategoryTheory.Functor.IsRepresentedBy`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {F : CategoryTheo
ry.Functor Cᵒᵖ (Type w)} {X : C}   {x : F.obj (Opposite.op X)}, F.IsRepresentedB
y x ↔ ∃ R, R.homEquiv (CategoryTheory.CategoryStruct.id X) = x
参数：Type w；Opposite.op X；CategoryTheory.CategoryStruct.id X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.types_congr_hom`：types_congr_hom {X Y : Type u} {f g : X 
⟶ Y} (h : f = g) (x : X) : f x = g x
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.id_apply`：∀ {C : Type u} [inst : CategoryTheory.Category.
{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → FunL
ike (FC X Y) …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Functor.RepresentableBy.isRepresentedBy`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {F : CategoryTheory.Functor Cᵒᵖ (Type w
)} {X : C}   (R : F.RepresentableBy X), F.Is…
-/
lemma IsRepresentedBy.iff_exists_representableBy :
    F.IsRepresentedBy x ↔ ∃ (R : F.RepresentableBy X), R.homEquiv (𝟙 X) = x :=
  ⟨fun h ↦ ⟨h.representableBy, by simp⟩, fun ⟨R, h⟩ ↦ h ▸ R.isRepresentedBy⟩
/-
**CategoryTheory.Functor.IsRepresentedBy.of_natIso** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Functor.IsRepresentedBy`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {F : CategoryTheo
ry.Functor Cᵒᵖ (Type w)} {X : C}   {x : F.obj (Opposite.op X)},   F.IsRepresente
dBy x →     ∀ {F' : CategoryTheory.Functor Cᵒᵖ (Type w)} (e : F ≅ F'),       F'.
IsRepresentedBy ((CategoryTheory.ConcreteCategory.hom (e.hom.app (Opposite.op X)
)) x)
参数：Type w；Opposite.op X；Type w；e : F ≅ F'；(CategoryTheory.ConcreteCategory.hom (
e.hom.app (Opposite.op X))) x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.IsRepresentedBy.iff_exists_representableBy`：∀ {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C] {F : CategoryTheory.Functor 
Cᵒᵖ (Type w)} {X : C}   {x : F.obj (Opposite.op X)}, F.…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `CategoryTheory.types_congr_hom`：types_congr_hom {X Y : Type u} {f g : X 
⟶ Y} (h : f = g) (x : X) : f x = g x
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.id_apply`：∀ {C : Type u} [inst : CategoryTheory.Category.
{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → FunL
ike (FC X Y) …
· 使用定理 `CategoryTheory.Iso.toEquiv_apply`：∀ {X Y : Type u} (i : X ≅ Y) (a : X), 
i.toEquiv a = (CategoryTheory.ConcreteCategory.hom i.hom) a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma IsRepresentedBy.of_natIso (h : F.IsRepresentedBy x) {F' : Cᵒᵖ ⥤ Type w}
    (e : F ≅ F') :
    F'.IsRepresentedBy (e.hom.app (op X) x) := by
  rw [iff_exists_representableBy]
  use h.representableBy.ofIso e
  simp [RepresentableBy.ofIso]
/-
**CategoryTheory.Functor.IsRepresentedBy.iff_natIso** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.Functor.IsRepresentedBy`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {F : CategoryTheo
ry.Functor Cᵒᵖ (Type w)} {X : C}   {x : F.obj (Opposite.op X)} {F' : CategoryThe
ory.Functor Cᵒᵖ (Type w)} (e : F ≅ F'),   F'.IsRepresentedBy ((CategoryTheory.Co
ncreteCategory.hom (e.hom.app (Opposite.op X))) x) ↔ F.IsRepresentedBy x
参数：Type w；Opposite.op X；Type w；e : F ≅ F'；(CategoryTheory.ConcreteCategory.hom (
e.hom.app (Opposite.op X))) x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.hom_inv_id_app_apply`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Functor.IsRepresentedBy.of_natIso`：∀ {C : Type u} [inst :
 CategoryTheory.Category.{v, u} C] {F : CategoryTheory.Functor Cᵒᵖ (Type w)} {X 
: C}   {x : F.obj (Opposite.op X)},   …
-/
lemma IsRepresentedBy.iff_natIso {F' : Cᵒᵖ ⥤ Type w} (e : F ≅ F') :
    F'.IsRepresentedBy (e.hom.app (op X) x) ↔ F.IsRepresentedBy x :=
  ⟨fun h ↦ by simpa using h.of_natIso e.symm, fun h ↦ .of_natIso h _⟩
/-
**CategoryTheory.Functor.IsRepresentedBy.of_isoObj** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Functor.IsRepresentedBy`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {F : CategoryTheo
ry.Functor Cᵒᵖ (Type w)} {X : C}   {x : F.obj (Opposite.op X)},   F.IsRepresente
dBy x →     ∀ {Y : C} (e : Y ≅ X), F.IsRepresentedBy ((CategoryTheory.ConcreteCa
tegory.hom (F.map e.hom.op)) x)
参数：Type w；Opposite.op X；e : Y ≅ X；(CategoryTheory.ConcreteCategory.hom (F.map e.
hom.op)) x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.IsRepresentedBy.iff_exists_representableBy`：∀ {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C] {F : CategoryTheory.Functor 
Cᵒᵖ (Type w)} {X : C}   {x : F.obj (Opposite.op X)}, F.…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `CategoryTheory.Functor.RepresentableBy.ofIsoObj_homEquiv`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] {F : CategoryTheory.Functor Cᵒᵖ (T
ype w)} {X Y : C}   (R : F.RepresentableBy X) …
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma IsRepresentedBy.of_isoObj (h : F.IsRepresentedBy x) {Y : C} (e : Y ≅ X) :
    F.IsRepresentedBy (F.map e.hom.op x) := by
  rw [iff_exists_representableBy]
  use h.representableBy.ofIsoObj e
  simp
/-
**CategoryTheory.Functor.IsRepresentedBy.iff_of_isoObj** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.Functor.IsRepresentedBy`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {F : CategoryTheo
ry.Functor Cᵒᵖ (Type w)} {X : C}   {x : F.obj (Opposite.op X)} {Y : C} (e : Y ≅ 
X),   F.IsRepresentedBy ((CategoryTheory.ConcreteCategory.hom (F.map e.hom.op)) 
x) ↔ F.IsRepresentedBy x
参数：Type w；Opposite.op X；e : Y ≅ X；(CategoryTheory.ConcreteCategory.hom (F.map e.
hom.op)) x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.types_congr_hom`：types_congr_hom {X Y : Type u} {f g : X 
⟶ Y} (h : f = g) (x : X) : f x = g x
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.id_apply`：∀ {C : Type u} [inst : CategoryTheory.Category.
{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → FunL
ike (FC X Y) …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Functor.IsRepresentedBy.of_isoObj`：∀ {C : Type u} [inst :
 CategoryTheory.Category.{v, u} C] {F : CategoryTheory.Functor Cᵒᵖ (Type w)} {X 
: C}   {x : F.obj (Opposite.op X)},   …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma IsRepresentedBy.iff_of_isoObj {Y : C} (e : Y ≅ X) :
    F.IsRepresentedBy (F.map e.hom.op x) ↔ F.IsRepresentedBy x := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.of_isoObj e⟩
  have : x = F.map e.inv.op (F.map e.hom.op x) := by
    simp [← comp_apply, ← map_comp, ← op_comp]
  exact this ▸ .of_isoObj h e.symm
/-
**CategoryTheory.Functor.IsRepresentedBy.of_isRepresentable** 是 Mathlib 中的一个定理，位
于命名空间 `CategoryTheory.Functor.IsRepresentedBy`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {F : CategoryTheo
ry.Functor Cᵒᵖ (Type w)}   [inst_1 : F.IsRepresentable], F.IsRepresentedBy F.rep
rx
参数：Type w。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.RepresentableBy.isRepresentedBy`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {F : CategoryTheory.Functor Cᵒᵖ (Type w
)} {X : C}   (R : F.RepresentableBy X), F.Is…
-/
lemma IsRepresentedBy.of_isRepresentable [F.IsRepresentable] : F.IsRepresentedBy F.reprx :=
  F.representableBy.isRepresentedBy
/-
**CategoryTheory.Functor.IsRepresentable.iff_exists_isRepresentedBy** 是 Mathlib 
中的一个定理，位于命名空间 `CategoryTheory.Functor.IsRepresentable`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {F : CategoryTheo
ry.Functor Cᵒᵖ (Type w)},   F.IsRepresentable ↔ ∃ X x, F.IsRepresentedBy x
参数：Type w。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsRepresentedBy.of_isRepresentable`：∀ {C : Type u
} [inst : CategoryTheory.Category.{v, u} C] {F : CategoryTheory.Functor Cᵒᵖ (Typ
e w)}   [inst_1 : F.IsRepresentable], F.IsRepre…
· 使用定理 `CategoryTheory.Functor.RepresentableBy.isRepresentable`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {F : CategoryTheory.Functor Cᵒᵖ (Typ
e v)} {Y : C}   (e : F.RepresentableBy Y), F…
-/
lemma IsRepresentable.iff_exists_isRepresentedBy :
    F.IsRepresentable ↔ ∃ (X : C) (x : F.obj (op X)), F.IsRepresentedBy x :=
  ⟨fun _ ↦ ⟨F.reprX, F.reprx, .of_isRepresentable⟩,
    fun ⟨_, _, h⟩ ↦ h.representableBy.isRepresentable⟩

end CategoryTheory.Functor

