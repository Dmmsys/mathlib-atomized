/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.CategoryTheory.Sites.Subsheaf
public import Mathlib.CategoryTheory.Sites.Whiskering

/-!
# Locally injective morphisms of (pre)sheaves

Let `C` be a category equipped with a Grothendieck topology `J`,
and let `D` be a concrete category. In this file, we introduce the typeclass
`Presheaf.IsLocallyInjective J φ` for a morphism `φ : F₁ ⟶ F₂` in the category
`Cᵒᵖ ⥤ D`. This means that `φ` is locally injective. More precisely,
if `x` and `y` are two elements of some `F₁.obj U` such
the images of `x` and `y` in `F₂.obj U` coincide, then
the equality `x = y` must hold locally, i.e. after restriction
by the maps of a covering sieve.

-/

@[expose] public section

universe w v' v u' u

namespace CategoryTheory

open Opposite Limits

variable {C : Type u} [Category.{v} C]
  {D : Type u'} [Category.{v'} D] {FD : D → D → Type*} {CD : D → Type w}
  [∀ X Y, FunLike (FD X Y) (CD X) (CD Y)] [ConcreteCategory.{w} D FD]
  (J : GrothendieckTopology C)

namespace Presheaf

/-- If `F : Cᵒᵖ ⥤ D` is a presheaf with values in a concrete category, if `x` and `y` are
elements in `F.obj X`, this is the sieve of `X.unop` consisting of morphisms `f`
such that `F.map f.op x = F.map f.op y`. -/
@[simps]
/-
**CategoryTheory.Presheaf.equalizerSieve** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Presheaf`。
形式化陈述：equalizerSieve {F : Cᵒᵖ ⥤ D} {X : Cᵒᵖ} (x y : ToType (F.obj X)) : Sieve X.
unop where arrows _ f
参数：x y : ToType (F.obj X)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F : Cᵒᵖ ⥤ D` is a presheaf with values in a concrete category, if `x` and `y
` are
elements in `F.obj X`, this is the sieve of `X.unop` consisting of morphisms `f`
such that `F.map f.op x = F.map f.op y`.
-/
def equalizerSieve {F : Cᵒᵖ ⥤ D} {X : Cᵒᵖ} (x y : ToType (F.obj X)) : Sieve X.unop where
  arrows _ f := F.map f.op x = F.map f.op y
  downward_closed {X Y} f hf g := by
    dsimp at hf ⊢
    simp [hf]

@[simp]
/-
**CategoryTheory.Presheaf.equalizerSieve_self_eq_top** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.Presheaf`。
形式化陈述：equalizerSieve_self_eq_top {F : Cᵒᵖ ⥤ D} {X : Cᵒᵖ} (x : ToType (F.obj X)) 
: equalizerSieve x x = ⊤
参数：x : ToType (F.obj X)。
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
· 使用定理 `CategoryTheory.Presheaf.equalizerSieve_apply`：∀ {C : Type u} [inst : Cat
egoryTheory.Category.{v, u} C] {D : Type u'} [inst_1 : CategoryTheory.Category.{
v', u'} D]   {FD : D → D → Type u_…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma equalizerSieve_self_eq_top {F : Cᵒᵖ ⥤ D} {X : Cᵒᵖ} (x : ToType (F.obj X)) :
    equalizerSieve x x = ⊤ := by aesop

@[simp]
/-
**CategoryTheory.Presheaf.equalizerSieve_eq_top_iff** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.Presheaf`。
形式化陈述：equalizerSieve_eq_top_iff {F : Cᵒᵖ ⥤ D} {X : Cᵒᵖ} (x y : ToType (F.obj X))
 : equalizerSieve x y = ⊤ ↔ x = y
参数：x y : ToType (F.obj X)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Presheaf.equalizerSieve_apply`：∀ {C : Type u} [inst : Cat
egoryTheory.Category.{v, u} C] {D : Type u'} [inst_1 : CategoryTheory.Category.{
v', u'} D]   {FD : D → D → Type u_…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.id_apply`：∀ {C : Type u} [inst : CategoryTheory.Category.
{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → FunL
ike (FC X Y) …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `CategoryTheory.Presheaf.equalizerSieve_self_eq_top`：equalizerSieve_self_
eq_top {F : Cᵒᵖ ⥤ D} {X : Cᵒᵖ} (x : ToType (F.obj X)) : equalizerSieve x x = ⊤
-/
lemma equalizerSieve_eq_top_iff {F : Cᵒᵖ ⥤ D} {X : Cᵒᵖ} (x y : ToType (F.obj X)) :
    equalizerSieve x y = ⊤ ↔ x = y := by
  constructor
  · intro h
    simpa using (show equalizerSieve x y (𝟙 _) by simp [h])
  · rintro rfl
    apply equalizerSieve_self_eq_top

variable {F₁ F₂ F₃ : Cᵒᵖ ⥤ D} (φ : F₁ ⟶ F₂) (ψ : F₂ ⟶ F₃)

/-- A morphism `φ : F₁ ⟶ F₂` of presheaves `Cᵒᵖ ⥤ D` (with `D` a concrete category)
is locally injective for a Grothendieck topology `J` on `C` if
whenever two sections of `F₁` are sent to the same section of `F₂`, then these two
sections coincide locally. -/
/-
**CategoryTheory.Presheaf.IsLocallyInjective** 是 Mathlib 中的一个归纳类型，位于命名空间 `Catego
ryTheory.Presheaf`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {D : Type
 u'} →       [inst_1 : CategoryTheory.Category.{v', u'} D] →         {FD : D → D
 → Type u_1} →           {CD : D → Type w} →             [inst_2 : (X Y : D) → F
unLike (FD X Y) (CD X) (CD Y)] →               [CategoryTheory.ConcreteCategory 
D FD] →                 CategoryTheory.GrothendieckTopology C → {F₁ F₂ : Categor
yTheory.Functor Cᵒᵖ D} → (F₁ ⟶ F₂) → Prop
参数：X Y : D；FD X Y；CD X；CD Y；F₁ ⟶ F₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism `φ : F₁ ⟶ F₂` of presheaves `Cᵒᵖ ⥤ D` (with `D` a concrete category)
is locally injective for a Grothendieck topology `J` on `C` if
whenever two sections of `F₁` are sent to the same section of `F₂`, then these t
wo
sections coincide locally.
-/
class IsLocallyInjective : Prop where
  equalizerSieve_mem {X : Cᵒᵖ} (x y : ToType (F₁.obj X)) (h : φ.app X x = φ.app X y) :
    equalizerSieve x y ∈ J X.unop
/-
**CategoryTheory.Presheaf.equalizerSieve_mem** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.Presheaf`。
形式化陈述：equalizerSieve_mem [IsLocallyInjective J φ] {X : Cᵒᵖ} (x y : ToType (F₁.ob
j X)) (h : φ.app X x = φ.app X y) : equalizerSieve x y in J X.unop
参数：x y : ToType (F₁.obj X)；h : φ.app X x = φ.app X y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Presheaf.IsLocallyInjective.equalizerSieve_mem`：∀ {C : Ty
pe u} {inst : CategoryTheory.Category.{v, u} C} {D : Type u'} {inst_1 : Category
Theory.Category.{v', u'} D}   {FD : D → D → Type u_…
-/
lemma equalizerSieve_mem [IsLocallyInjective J φ]
    {X : Cᵒᵖ} (x y : ToType (F₁.obj X)) (h : φ.app X x = φ.app X y) :
    equalizerSieve x y ∈ J X.unop :=
  IsLocallyInjective.equalizerSieve_mem x y h
/-
**CategoryTheory.Presheaf.isLocallyInjective_of_injective** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.Presheaf`。
形式化陈述：isLocallyInjective_of_injective (hφ : forall (X : Cᵒᵖ), Function.Injective
 (φ.app X)) : IsLocallyInjective J φ where equalizerSieve_mem {X} x y h
参数：hφ : forall (X : Cᵒᵖ), Function.Injective (φ.app X)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Sieve.ext`：∀ {C : Type u₁} [inst : CategoryTheory.Categor
y.{v₁, u₁} C] {X : C} {R S : CategoryTheory.Sieve X},   (∀ ⦃Y : C⦄ (f : Y ⟶ X), 
R.arrows f ↔ S…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Presheaf.equalizerSieve_apply`：∀ {C : Type u} [inst : Cat
egoryTheory.Category.{v, u} C] {D : Type u'} [inst_1 : CategoryTheory.Category.{
v', u'} D]   {FD : D → D → Type u_…
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.NatTrans.naturality_apply`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {D : Type u_1} [inst_1 : CategoryTheory.Category.{v_1
, u_1} D]   {FD : outParam (D …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.GrothendieckTopology.top_mem`：top_mem (X : C) : ⊤ in J X
-/
lemma isLocallyInjective_of_injective (hφ : ∀ (X : Cᵒᵖ), Function.Injective (φ.app X)) :
    IsLocallyInjective J φ where
  equalizerSieve_mem {X} x y h := by
    convert! J.top_mem X.unop
    ext Y f
    simp only [equalizerSieve_apply, op_unop, Sieve.top_apply, iff_true]
    apply hφ
    simp [h]
/-
**CategoryTheory.Presheaf.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Presheaf`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsIso φ] : IsLocallyInjective J φ :=
  isLocallyInjective_of_injective J φ (fun X => Function.Bijective.injective (by
    rw [bijective_iff_isIso_ofHom]
    infer_instance))
/-
**CategoryTheory.Presheaf.isLocallyInjective_forget** 是 Mathlib 中的一个实例，位于命名空间 `C
ategoryTheory.Presheaf`。
形式化陈述：isLocallyInjective_forget [IsLocallyInjective J φ] : IsLocallyInjective J 
(Functor.whiskerRight φ (forget D)) where equalizerSieve_mem x y h
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Presheaf.equalizerSieve_mem`：equalizerSieve_mem [IsLocall
yInjective J φ] {X : Cᵒᵖ} (x y : ToType (F₁.obj X)) (h : φ.app X x = φ.app X y) 
: equalizerSieve x y in J X.unop
-/
instance isLocallyInjective_forget [IsLocallyInjective J φ] :
    IsLocallyInjective J (Functor.whiskerRight φ (forget D)) where
  equalizerSieve_mem x y h := equalizerSieve_mem J φ x y h
/-
**CategoryTheory.Presheaf.isLocallyInjective_forget_iff** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.Presheaf`。
形式化陈述：isLocallyInjective_forget_iff : IsLocallyInjective J (Functor.whiskerRight
 φ (forget D)) ↔ IsLocallyInjective J φ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Presheaf.equalizerSieve_mem`：equalizerSieve_mem [IsLocall
yInjective J φ] {X : Cᵒᵖ} (x y : ToType (F₁.obj X)) (h : φ.app X x = φ.app X y) 
: equalizerSieve x y in J X.unop
-/
lemma isLocallyInjective_forget_iff :
    IsLocallyInjective J (Functor.whiskerRight φ (forget D)) ↔ IsLocallyInjective J φ := by
  constructor
  · intro
    exact ⟨fun x y h => equalizerSieve_mem J (Functor.whiskerRight φ (forget D)) x y h⟩
  · intro
    infer_instance
/-
**CategoryTheory.Presheaf.isLocallyInjective_iff_equalizerSieve_mem_imp** 是 Math
lib 中的一个引理，位于命名空间 `CategoryTheory.Presheaf`。
形式化陈述：isLocallyInjective_iff_equalizerSieve_mem_imp : IsLocallyInjective J φ ↔ f
orall ⦃X : Cᵒᵖ⦄ (x y : ToType (F₁.obj X)), equalizerSieve (φ.app _ x) (φ.app _ y
) in J X.unop -> equalizerSieve x y in J X.unop
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrothendieckTopology.superset_covering`：superset_covering
 (Hss : S <= R) (sjx : S in J X) : R in J X
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Presheaf.equalizerSieve_apply`：∀ {C : Type u} [inst : Cat
egoryTheory.Category.{v, u} C] {D : Type u'} [inst_1 : CategoryTheory.Category.{
v', u'} D]   {FD : D → D → Type u_…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
· 使用定理 `CategoryTheory.GrothendieckTopology.transitive`：transitive (hS : S in J 
X) (R : Sieve X) (h : forall ⦃Y⦄ ⦃f : Y ⟶ X⦄, S f -> R.pullback f in J Y) : R in
 J X
· 使用定理 `CategoryTheory.Sieve.le_pullback_bind`：le_pullback_bind (S : Presieve X)
 (R : forall ⦃Y : C⦄ ⦃f : Y ⟶ X⦄, S f -> Sieve Y) (f : Y ⟶ X) (h : S f) : R h <=
 (bind S R).pullback f
· 使用引理 `CategoryTheory.Presheaf.equalizerSieve_mem`：equalizerSieve_mem [IsLocall
yInjective J φ] {X : Cᵒᵖ} (x y : ToType (F₁.obj X)) (h : φ.app X x = φ.app X y) 
: equalizerSieve x y in J X.unop
· 使用定理 `CategoryTheory.NatTrans.naturality_apply`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {D : Type u_1} [inst_1 : CategoryTheory.Category.{v_1
, u_1} D]   {FD : outParam (D …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `CategoryTheory.Presheaf.equalizerSieve_self_eq_top`：equalizerSieve_self_
eq_top {F : Cᵒᵖ ⥤ D} {X : Cᵒᵖ} (x : ToType (F.obj X)) : equalizerSieve x x = ⊤
-/
lemma isLocallyInjective_iff_equalizerSieve_mem_imp :
    IsLocallyInjective J φ ↔ ∀ ⦃X : Cᵒᵖ⦄ (x y : ToType (F₁.obj X)),
      equalizerSieve (φ.app _ x) (φ.app _ y) ∈ J X.unop → equalizerSieve x y ∈ J X.unop := by
  constructor
  · intro _ X x y h
    let S := equalizerSieve (φ.app _ x) (φ.app _ y)
    let T : ∀ ⦃Y : C⦄ ⦃f : Y ⟶ X.unop⦄ (_ : S f), Sieve Y := fun Y f _ =>
      equalizerSieve (F₁.map f.op x) ((F₁.map f.op y))
    refine J.superset_covering ?_ (J.transitive h (Sieve.bind S.1 T) ?_)
    · rintro Y f ⟨Z, a, g, hg, ha, rfl⟩
      simpa using! ha
    · intro Y f hf
      refine J.superset_covering (Sieve.le_pullback_bind S.1 T _ hf)
        (equalizerSieve_mem J φ _ _ ?_)
      rw [NatTrans.naturality_apply, NatTrans.naturality_apply]
      exact hf
  · intro hφ
    exact ⟨fun {X} x y h => hφ x y (by simp [h])⟩
/-
**CategoryTheory.Presheaf.equalizerSieve_mem_of_equalizerSieve_app_mem** 是 Mathl
ib 中的一个引理，位于命名空间 `CategoryTheory.Presheaf`。
形式化陈述：equalizerSieve_mem_of_equalizerSieve_app_mem {X : Cᵒᵖ} (x y : ToType (F₁.o
bj X)) (h : equalizerSieve (φ.app _ x) (φ.app _ y) in J X.unop) [IsLocallyInject
ive J φ] : equalizerSieve x y in J X.unop
参数：x y : ToType (F₁.obj X)；h : equalizerSieve (φ.app _ x) (φ.app _ y) in J X.uno
p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `CategoryTheory.Presheaf.isLocallyInjective_iff_equalizerSieve_mem_imp`：i
sLocallyInjective_iff_equalizerSieve_mem_imp : IsLocallyInjective J φ ↔ forall ⦃
X : Cᵒᵖ⦄ (x y : ToType (F₁.obj X)), equalizerSieve (φ.app _…
-/
lemma equalizerSieve_mem_of_equalizerSieve_app_mem
    {X : Cᵒᵖ} (x y : ToType (F₁.obj X)) (h : equalizerSieve (φ.app _ x) (φ.app _ y) ∈ J X.unop)
    [IsLocallyInjective J φ] :
    equalizerSieve x y ∈ J X.unop :=
  (isLocallyInjective_iff_equalizerSieve_mem_imp J φ).1 inferInstance x y h
/-
**CategoryTheory.Presheaf.isLocallyInjective_comp** 是 Mathlib 中的一个实例，位于命名空间 `Cat
egoryTheory.Presheaf`。
形式化陈述：isLocallyInjective_comp [IsLocallyInjective J φ] [IsLocallyInjective J ψ] 
: IsLocallyInjective J (φ ≫ ψ) where equalizerSieve_mem {X} x y h
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Presheaf.equalizerSieve_mem_of_equalizerSieve_app_mem`：eq
ualizerSieve_mem_of_equalizerSieve_app_mem {X : Cᵒᵖ} (x y : ToType (F₁.obj X)) (
h : equalizerSieve (φ.app _ x) (φ.app _ y) in J X.unop) [I…
· 使用引理 `CategoryTheory.Presheaf.equalizerSieve_mem`：equalizerSieve_mem [IsLocall
yInjective J φ] {X : Cᵒᵖ} (x y : ToType (F₁.obj X)) (h : φ.app X x = φ.app X y) 
: equalizerSieve x y in J X.unop
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
-/
instance isLocallyInjective_comp [IsLocallyInjective J φ] [IsLocallyInjective J ψ] :
    IsLocallyInjective J (φ ≫ ψ) where
  equalizerSieve_mem {X} x y h := by
    apply equalizerSieve_mem_of_equalizerSieve_app_mem J φ
    exact equalizerSieve_mem J ψ _ _ (by simpa using h)
/-
**CategoryTheory.Presheaf.isLocallyInjective_of_isLocallyInjective** 是 Mathlib 中
的一个引理，位于命名空间 `CategoryTheory.Presheaf`。
形式化陈述：isLocallyInjective_of_isLocallyInjective [IsLocallyInjective J (φ ≫ ψ)] : 
IsLocallyInjective J φ where equalizerSieve_mem {X} x y h
参数：φ ≫ ψ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Presheaf.equalizerSieve_mem`：equalizerSieve_mem [IsLocall
yInjective J φ] {X : Cᵒᵖ} (x y : ToType (F₁.obj X)) (h : φ.app X x = φ.app X y) 
: equalizerSieve x y in J X.unop
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma isLocallyInjective_of_isLocallyInjective [IsLocallyInjective J (φ ≫ ψ)] :
    IsLocallyInjective J φ where
  equalizerSieve_mem {X} x y h := equalizerSieve_mem J (φ ≫ ψ) x y (by simp [h])

variable {φ ψ}
/-
**CategoryTheory.Presheaf.isLocallyInjective_of_isLocallyInjective_fac** 是 Mathl
ib 中的一个引理，位于命名空间 `CategoryTheory.Presheaf`。
形式化陈述：isLocallyInjective_of_isLocallyInjective_fac {φψ : F₁ ⟶ F₃} (fac : φ ≫ ψ =
 φψ) [IsLocallyInjective J φψ] : IsLocallyInjective J φ
参数：fac : φ ≫ ψ = φψ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Presheaf.isLocallyInjective_of_isLocallyInjective`：isLoca
llyInjective_of_isLocallyInjective [IsLocallyInjective J (φ ≫ ψ)] : IsLocallyInj
ective J φ where equalizerSieve_mem {X} x y h
-/
lemma isLocallyInjective_of_isLocallyInjective_fac {φψ : F₁ ⟶ F₃} (fac : φ ≫ ψ = φψ)
    [IsLocallyInjective J φψ] : IsLocallyInjective J φ := by
  subst fac
  exact isLocallyInjective_of_isLocallyInjective J φ ψ
/-
**CategoryTheory.Presheaf.isLocallyInjective_iff_of_fac** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.Presheaf`。
形式化陈述：isLocallyInjective_iff_of_fac {φψ : F₁ ⟶ F₃} (fac : φ ≫ ψ = φψ) [IsLocally
Injective J ψ] : IsLocallyInjective J φψ ↔ IsLocallyInjective J φ
参数：fac : φ ≫ ψ = φψ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Presheaf.isLocallyInjective_of_isLocallyInjective_fac`：is
LocallyInjective_of_isLocallyInjective_fac {φψ : F₁ ⟶ F₃} (fac : φ ≫ ψ = φψ) [Is
LocallyInjective J φψ] : IsLocallyInjective J φ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma isLocallyInjective_iff_of_fac {φψ : F₁ ⟶ F₃} (fac : φ ≫ ψ = φψ) [IsLocallyInjective J ψ] :
    IsLocallyInjective J φψ ↔ IsLocallyInjective J φ := by
  constructor
  · intro
    exact isLocallyInjective_of_isLocallyInjective_fac J fac
  · intro
    rw [← fac]
    infer_instance

variable (φ ψ)
/-
**CategoryTheory.Presheaf.isLocallyInjective_comp_iff** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Presheaf`。
形式化陈述：isLocallyInjective_comp_iff [IsLocallyInjective J ψ] : IsLocallyInjective 
J (φ ≫ ψ) ↔ IsLocallyInjective J φ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Presheaf.isLocallyInjective_iff_of_fac`：isLocallyInjectiv
e_iff_of_fac {φψ : F₁ ⟶ F₃} (fac : φ ≫ ψ = φψ) [IsLocallyInjective J ψ] : IsLoca
llyInjective J φψ ↔ IsLocallyInjective J φ
-/
lemma isLocallyInjective_comp_iff [IsLocallyInjective J ψ] :
    IsLocallyInjective J (φ ≫ ψ) ↔ IsLocallyInjective J φ :=
  isLocallyInjective_iff_of_fac J rfl
/-
**CategoryTheory.Presheaf.isLocallyInjective_iff_injective_of_separated** 是 Math
lib 中的一个引理，位于命名空间 `CategoryTheory.Presheaf`。
形式化陈述：isLocallyInjective_iff_injective_of_separated (hsep : Presieve.IsSeparated
 J (F₁ ⋙ forget D)) : IsLocallyInjective J φ ↔ forall (X : Cᵒᵖ), Function.Inject
ive (φ.app X)
参数：hsep : Presieve.IsSeparated J (F₁ ⋙ forget D)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Presieve.IsSeparatedFor.ext`：∀ {C : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} C] {P : CategoryTheory.Functor Cᵒᵖ (Type w)} {X : C
}   {R : CategoryTheory.Presieve…
· 使用引理 `CategoryTheory.Presheaf.equalizerSieve_mem`：equalizerSieve_mem [IsLocall
yInjective J φ] {X : Cᵒᵖ} (x y : ToType (F₁.obj X)) (h : φ.app X x = φ.app X y) 
: equalizerSieve x y in J X.unop
· 使用引理 `CategoryTheory.Presheaf.isLocallyInjective_of_injective`：isLocallyInject
ive_of_injective (hφ : forall (X : Cᵒᵖ), Function.Injective (φ.app X)) : IsLocal
lyInjective J φ where equalizerSieve_mem {X} …
-/
lemma isLocallyInjective_iff_injective_of_separated
    (hsep : Presieve.IsSeparated J (F₁ ⋙ forget D)) :
    IsLocallyInjective J φ ↔ ∀ (X : Cᵒᵖ), Function.Injective (φ.app X) := by
  constructor
  · intro _ X x y h
    exact (hsep _ (equalizerSieve_mem J φ x y h)).ext (fun _ _ hf => hf)
  · apply isLocallyInjective_of_injective
/-
**CategoryTheory.Presheaf.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Presheaf`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (F : Cᵒᵖ ⥤ Type w) (G : Subfunctor F) :
    IsLocallyInjective J G.ι :=
  isLocallyInjective_of_injective _ _ (fun X => by
    intro ⟨x, _⟩ ⟨y, _⟩ h
    exact Subtype.ext h)

section

open GrothendieckTopology.Plus

/-
**CategoryTheory.Presheaf.isLocallyInjective_toPlus** 是 Mathlib 中的一个实例，位于命名空间 `C
ategoryTheory.Presheaf`。
形式化陈述：isLocallyInjective_toPlus (P : Cᵒᵖ ⥤ Type (max u v)) : IsLocallyInjective 
J (J.toPlus P) where equalizerSieve_mem {X} x y h
参数：P : Cᵒᵖ ⥤ Type (max u v)。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `CategoryTheory.Limits.Types.hasColimitsOfShape`：∀ {J : Type v} [inst : C
ategoryTheory.Category.{w, v} J] [Small.{u, v} J],   CategoryTheory.Limits.HasCo
limitsOfShape J (Type u)
· 使用定理 `CategoryTheory.Functor.instPreservesLimitsOfShapeOfIsRightAdjoint`：∀ {J 
: Type u_1} {C : Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_1, 
u_1} J]   [inst_1 : CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `CategoryTheory.Functor.isRightAdjoint_of_isEquivalence`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Types.instIsEquivalenceForgetTypeFun`：(CategoryTheory.for
get (Type u)).IsEquivalence
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.GrothendieckTopology.Plus.eq_mk_iff_exists`：eq_mk_iff_exi
sts {X : C} {P : Cᵒᵖ ⥤ D} {S T : J.Cover X} (x : Meq P S) (y : Meq P T) : mk x =
 mk y ↔ exists (W : J.Cover X) (h1 : W ⟶ S) (h2…
· 使用定理 `CategoryTheory.Functor.instPreservesColimitsOfShapeOfIsLeftAdjoint`：∀ {J
 : Type u_1} {C : Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_1,
 u_1} J]   [inst_1 : CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `CategoryTheory.Functor.isLeftAdjoint_of_isEquivalence`：∀ {C : Type u₁} [
inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheor
y.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.GrothendieckTopology.Plus.toPlus_eq_mk`：toPlus_eq_mk {X :
 C} {P : Cᵒᵖ ⥤ D} (x : ToType (P.obj (op X))) : (J.toPlus P).app _ x = mk (Meq.m
k ⊤ x)
· 使用定理 `CategoryTheory.GrothendieckTopology.superset_covering`：superset_covering
 (Hss : S <= R) (sjx : S in J X) : R in J X
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
instance isLocallyInjective_toPlus (P : Cᵒᵖ ⥤ Type (max u v)) :
    IsLocallyInjective J (J.toPlus P) where
  equalizerSieve_mem {X} x y h := by
    rw [toPlus_eq_mk, toPlus_eq_mk, eq_mk_iff_exists] at h
    obtain ⟨W, h₁, h₂, eq⟩ := h
    exact J.superset_covering (fun Y f hf => congr_fun (congr_arg Subtype.val eq) ⟨Y, f, hf⟩) W.2

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Presheaf.isLocallyInjective_toSheafify** 是 Mathlib 中的一个实例，位于命名空
间 `CategoryTheory.Presheaf`。
形式化陈述：isLocallyInjective_toSheafify (P : Cᵒᵖ ⥤ Type (max u v)) : IsLocallyInject
ive J (J.toSheafify P)
参数：P : Cᵒᵖ ⥤ Type (max u v)。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `CategoryTheory.Limits.Types.hasColimitsOfShape`：∀ {J : Type v} [inst : C
ategoryTheory.Category.{w, v} J] [Small.{u, v} J],   CategoryTheory.Limits.HasCo
limitsOfShape J (Type u)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.GrothendieckTopology.plusMap_toPlus`：plusMap_toPlus : J.p
lusMap (J.toPlus P) = J.toPlus (J.plusObj P)
-/
instance isLocallyInjective_toSheafify (P : Cᵒᵖ ⥤ Type (max u v)) :
    IsLocallyInjective J (J.toSheafify P) := by
  dsimp [GrothendieckTopology.toSheafify]
  rw [GrothendieckTopology.plusMap_toPlus]
  infer_instance
/-
**CategoryTheory.Presheaf.isLocallyInjective_toSheafify'** 是 Mathlib 中的一个实例，位于命名
空间 `CategoryTheory.Presheaf`。
形式化陈述：isLocallyInjective_toSheafify' {CD : D -> Type (max u v)} [forall X Y, Fun
Like (FD X Y) (CD X) (CD Y)] [ConcreteCategory.{max u v} D FD] (P : Cᵒᵖ ⥤ D) [Ha
sWeakSheafify J D] [J.HasSheafCompose (forget D)] [J.PreservesSheafification (fo
rget D)] : IsLocallyInjective J (toSheafify J P)
参数：max u v；FD X Y；CD X；CD Y；P : Cᵒᵖ ⥤ D；forget D；forget D。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.Presheaf.isLocallyInjective_forget_iff`：isLocallyInjectiv
e_forget_iff : IsLocallyInjective J (Functor.whiskerRight φ (forget D)) ↔ IsLoca
llyInjective J φ
· 使用定理 `CategoryTheory.Functor.instPreservesLimitsOfShapeOfIsRightAdjoint`：∀ {J 
: Type u_1} {C : Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_1, 
u_1} J]   [inst_1 : CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `CategoryTheory.Functor.isRightAdjoint_of_isEquivalence`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Types.instIsEquivalenceForgetTypeFun`：(CategoryTheory.for
get (Type u)).IsEquivalence
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `CategoryTheory.Limits.Types.hasColimitsOfShape`：∀ {J : Type v} [inst : C
ategoryTheory.Category.{w, v} J] [Small.{u, v} J],   CategoryTheory.Limits.HasCo
limitsOfShape J (Type u)
· 使用定理 `CategoryTheory.Functor.instPreservesColimitsOfShapeOfIsLeftAdjoint`：∀ {J
 : Type u_1} {C : Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_1,
 u_1} J]   [inst_1 : CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `CategoryTheory.Functor.isLeftAdjoint_of_isEquivalence`：∀ {C : Type u₁} [
inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheor
y.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.reflectsIsomorphisms_of_full_and_faithful`：∀ {C : Type u_
1} [inst : CategoryTheory.Category.{v_1, u_1} C] {D : Type u_2}   [inst_1 : Cate
goryTheory.Category.{v_2, u_2} D] (F : Categor…
· 使用定理 `CategoryTheory.Types.instFullForgetTypeFun`：(CategoryTheory.forget (Type
 u)).Full
· 使用定理 `CategoryTheory.instFaithfulForget`：∀ (C : Type u_1) [inst : CategoryTheo
ry.Category.{v_1, u_1} C] {FC : outParam (C → C → Type u_2)}   {CC : outParam (C
 → Type w)} [inst_1 : o…
· 使用引理 `CategoryTheory.sheafComposeIso_hom_fac`：sheafComposeIso_hom_fac : toShea
fify J (P ⋙ F) ≫ (sheafifyComposeIso J F P).hom = whiskerRight (toSheafify J P) 
F
· 使用引理 `CategoryTheory.toSheafify_plusPlusIsoSheafify_hom`：toSheafify_plusPlusIs
oSheafify_hom (P : Cᵒᵖ ⥤ D) : J.toSheafify P ≫ (plusPlusIsoSheafify J D P).hom =
 toSheafify J P
· 使用定理 `CategoryTheory.Presheaf.instIsLocallyInjectiveOfIsIsoFunctorOpposite`：∀ 
{C : Type u} [inst : CategoryTheory.Category.{v, u} C] {D : Type u'} [inst_1 : C
ategoryTheory.Category.{v', u'} D]   {FD : D → D → Type u_…
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
-/
instance isLocallyInjective_toSheafify' {CD : D → Type (max u v)}
    [∀ X Y, FunLike (FD X Y) (CD X) (CD Y)] [ConcreteCategory.{max u v} D FD]
    (P : Cᵒᵖ ⥤ D) [HasWeakSheafify J D] [J.HasSheafCompose (forget D)]
    [J.PreservesSheafification (forget D)] :
    IsLocallyInjective J (toSheafify J P) := by
  rw [← isLocallyInjective_forget_iff, ← sheafComposeIso_hom_fac,
    ← toSheafify_plusPlusIsoSheafify_hom]
  infer_instance

end

end Presheaf

namespace Sheaf

variable {J}
variable {F₁ F₂ : Sheaf J D} (φ : F₁ ⟶ F₂)

/-- If `φ : F₁ ⟶ F₂` is a morphism of sheaves, this is an abbreviation for
`Presheaf.IsLocallyInjective J φ.val`. Under suitable assumptions, it
is equivalent to the injectivity of all maps `φ.val.app X`,
see `isLocallyInjective_iff_injective`. -/
/-
**CategoryTheory.Sheaf.IsLocallyInjective** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Sheaf`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {D : Type
 u'} →       [inst_1 : CategoryTheory.Category.{v', u'} D] →         {FD : D → D
 → Type u_1} →           {CD : D → Type w} →             [inst_2 : (X Y : D) → F
unLike (FD X Y) (CD X) (CD Y)] →               [CategoryTheory.ConcreteCategory 
D FD] →                 {J : CategoryTheory.GrothendieckTopology C} → {F₁ F₂ : C
ategoryTheory.Sheaf J D} → (F₁ ⟶ F₂) → Prop
参数：X Y : D；FD X Y；CD X；CD Y；F₁ ⟶ F₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `φ : F₁ ⟶ F₂` is a morphism of sheaves, this is an abbreviation for
`Presheaf.IsLocallyInjective J φ.val`. Under suitable assumptions, it
is equivalent to the injectivity of all maps `φ.val.app X`,
see `isLocallyInjective_iff_injective`.
-/
abbrev IsLocallyInjective := Presheaf.IsLocallyInjective J φ.hom
/-
**CategoryTheory.Sheaf.isLocallyInjective_sheafToPresheaf_map_iff** 是 Mathlib 中的
一个定理，位于命名空间 `CategoryTheory.Sheaf`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {D : Type u'} [in
st_1 : CategoryTheory.Category.{v', u'} D]   {FD : D → D → Type u_1} {CD : D → T
ype w} [inst_2 : (X Y : D) → FunLike (FD X Y) (CD X) (CD Y)]   [inst_3 : Categor
yTheory.ConcreteCategory D FD] {J : CategoryTheory.GrothendieckTopology C}   {F₁
 F₂ : CategoryTheory.Sheaf J D} (φ : F₁ ⟶ F₂),   CategoryTheory.Presheaf.IsLocal
lyInjective J ((CategoryTheory.sheafToPresheaf J D).map φ) ↔     CategoryTheory.
Sheaf.IsLocallyInjective φ
参数：X Y : D；FD X Y；CD X；CD Y；φ : F₁ ⟶ F₂；(CategoryTheory.sheafToPresheaf J D).map
 φ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isLocallyInjective_sheafToPresheaf_map_iff :
    Presheaf.IsLocallyInjective J ((sheafToPresheaf J D).map φ) ↔ IsLocallyInjective φ := by rfl
/-
**CategoryTheory.Sheaf.isLocallyInjective_of_iso** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Sheaf`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {D : Type u'} [in
st_1 : CategoryTheory.Category.{v', u'} D]   {FD : D → D → Type u_1} {CD : D → T
ype w} [inst_2 : (X Y : D) → FunLike (FD X Y) (CD X) (CD Y)]   [inst_3 : Categor
yTheory.ConcreteCategory D FD] {J : CategoryTheory.GrothendieckTopology C}   {F₁
 F₂ : CategoryTheory.Sheaf J D} (φ : F₁ ⟶ F₂) [CategoryTheory.IsIso φ], Category
Theory.Sheaf.IsLocallyInjective φ
参数：X Y : D；FD X Y；CD X；CD Y；φ : F₁ ⟶ F₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Presheaf.instIsLocallyInjectiveOfIsIsoFunctorOpposite`：∀ 
{C : Type u} [inst : CategoryTheory.Category.{v, u} C] {D : Type u'} [inst_1 : C
ategoryTheory.Category.{v', u'} D]   {FD : D → D → Type u_…
-/
instance isLocallyInjective_of_iso [IsIso φ] : IsLocallyInjective φ := by
  change Presheaf.IsLocallyInjective J ((sheafToPresheaf _ _).map φ)
  infer_instance
/-
**CategoryTheory.Sheaf.mono_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Sheaf`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {D : Type u'} [in
st_1 : CategoryTheory.Category.{v', u'} D]   {FD : D → D → Type u_1} {CD : D → T
ype w} [inst_2 : (X Y : D) → FunLike (FD X Y) (CD X) (CD Y)]   [inst_3 : Categor
yTheory.ConcreteCategory D FD] {J : CategoryTheory.GrothendieckTopology C}   {F₁
 F₂ : CategoryTheory.Sheaf J D} (φ : F₁ ⟶ F₂),   (∀ (X : Cᵒᵖ), Function.Injectiv
e ⇑(CategoryTheory.ConcreteCategory.hom (φ.hom.app X))) → CategoryTheory.Mono φ
参数：X Y : D；FD X Y；CD X；CD Y；φ : F₁ ⟶ F₂；∀ (X : Cᵒᵖ), Function.Injective ⇑(Catego
ryTheory.ConcreteCategory.hom (φ.hom.app X))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ConcreteCategory.mono_of_injective`：mono_of_injective {X 
Y : C} (f : X ⟶ Y) (i : Function.Injective f) : Mono f
· 使用定理 `CategoryTheory.Functor.mono_of_mono_map`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.reflectsMonomorphisms_of_reflectsLimitsOfShape`：∀ {C : Ty
pe u₁} {D : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Categ
oryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.ReflectsFiniteLimits.reflects`：∀ {C : Type u₁} {in
st : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.
Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.instReflectsFiniteLimitsOfReflectsLimits`：∀ {C : T
ype u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Cate
goryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.NatTrans.mono_of_mono_app`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
-/
lemma mono_of_injective
    (hφ : ∀ (X : Cᵒᵖ), Function.Injective (φ.hom.app X)) : Mono φ :=
  have : ∀ X, Mono (φ.hom.app X) := fun X ↦ ConcreteCategory.mono_of_injective _ (hφ X)
  (sheafToPresheaf _ _).mono_of_mono_map (NatTrans.mono_of_mono_app φ.1)

variable [J.HasSheafCompose (forget D)]
/-
**CategoryTheory.Sheaf.isLocallyInjective_forget** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Sheaf`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {D : Type u'} [in
st_1 : CategoryTheory.Category.{v', u'} D]   {FD : D → D → Type u_1} {CD : D → T
ype w} [inst_2 : (X Y : D) → FunLike (FD X Y) (CD X) (CD Y)]   [inst_3 : Categor
yTheory.ConcreteCategory D FD] {J : CategoryTheory.GrothendieckTopology C}   {F₁
 F₂ : CategoryTheory.Sheaf J D} (φ : F₁ ⟶ F₂) [inst_4 : J.HasSheafCompose (Categ
oryTheory.forget D)]   [CategoryTheory.Sheaf.IsLocallyInjective φ],   CategoryTh
eory.Sheaf.IsLocallyInjective ((CategoryTheory.sheafCompose J (CategoryTheory.fo
rget D)).map φ)
参数：X Y : D；FD X Y；CD X；CD Y；φ : F₁ ⟶ F₂；CategoryTheory.forget D；(CategoryTheory.
sheafCompose J (CategoryTheory.forget D)).map φ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance isLocallyInjective_forget [IsLocallyInjective φ] :
    IsLocallyInjective ((sheafCompose J (forget D)).map φ) :=
  Presheaf.isLocallyInjective_forget J φ.1
/-
**CategoryTheory.Sheaf.isLocallyInjective_iff_injective** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.Sheaf`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {D : Type u'} [in
st_1 : CategoryTheory.Category.{v', u'} D]   {FD : D → D → Type u_1} {CD : D → T
ype w} [inst_2 : (X Y : D) → FunLike (FD X Y) (CD X) (CD Y)]   [inst_3 : Categor
yTheory.ConcreteCategory D FD] {J : CategoryTheory.GrothendieckTopology C}   {F₁
 F₂ : CategoryTheory.Sheaf J D} (φ : F₁ ⟶ F₂) [J.HasSheafCompose (CategoryTheory
.forget D)],   CategoryTheory.Sheaf.IsLocallyInjective φ ↔     ∀ (X : Cᵒᵖ), Func
tion.Injective ⇑(CategoryTheory.ConcreteCategory.hom (φ.hom.app X))
参数：X Y : D；FD X Y；CD X；CD Y；φ : F₁ ⟶ F₂；CategoryTheory.forget D；X : Cᵒᵖ；Category
Theory.ConcreteCategory.hom (φ.hom.app X)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Presheaf.isLocallyInjective_iff_injective_of_separated`：i
sLocallyInjective_iff_injective_of_separated (hsep : Presieve.IsSeparated J (F₁ 
⋙ forget D)) : IsLocallyInjective J φ ↔ forall (X : Cᵒᵖ), F…
· 使用定理 `CategoryTheory.Presieve.IsSheaf.isSeparated`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {J : CategoryTheory.GrothendieckTopology C}   {P :
 CategoryTheory.Functor Cᵒᵖ (Type…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.isSheaf_iff_isSheaf_of_type`：isSheaf_iff_isSheaf_of_type 
(P : Cᵒᵖ ⥤ Type w) : Presheaf.IsSheaf J P ↔ Presieve.IsSheaf J P
· 使用定理 `CategoryTheory.ObjectProperty.FullSubcategory.property`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.ObjectProperty C}  
 (self : P.FullSubcategory), P self.obj
-/
lemma isLocallyInjective_iff_injective :
    IsLocallyInjective φ ↔ ∀ (X : Cᵒᵖ), Function.Injective (φ.hom.app X) :=
  Presheaf.isLocallyInjective_iff_injective_of_separated _ _ (by
    apply Presieve.IsSheaf.isSeparated
    rw [← isSheaf_iff_isSheaf_of_type]
    exact ((sheafCompose J (forget D)).obj F₁).2)
/-
**CategoryTheory.Sheaf.mono_of_isLocallyInjective** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Sheaf`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {D : Type u'} [in
st_1 : CategoryTheory.Category.{v', u'} D]   {FD : D → D → Type u_1} {CD : D → T
ype w} [inst_2 : (X Y : D) → FunLike (FD X Y) (CD X) (CD Y)]   [inst_3 : Categor
yTheory.ConcreteCategory D FD] {J : CategoryTheory.GrothendieckTopology C}   {F₁
 F₂ : CategoryTheory.Sheaf J D} (φ : F₁ ⟶ F₂) [J.HasSheafCompose (CategoryTheory
.forget D)]   [CategoryTheory.Sheaf.IsLocallyInjective φ], CategoryTheory.Mono φ
参数：X Y : D；FD X Y；CD X；CD Y；φ : F₁ ⟶ F₂；CategoryTheory.forget D。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Sheaf.mono_of_injective`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {D : Type u'} [inst_1 : CategoryTheory.Category.{v', u'
} D]   {FD : D → D → Type u_…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Sheaf.isLocallyInjective_iff_injective`：∀ {C : Type u} [i
nst : CategoryTheory.Category.{v, u} C] {D : Type u'} [inst_1 : CategoryTheory.C
ategory.{v', u'} D]   {FD : D → D → Type u_…
-/
lemma mono_of_isLocallyInjective [IsLocallyInjective φ] : Mono φ := by
  apply mono_of_injective
  rw [← isLocallyInjective_iff_injective]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Sheaf.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Sheaf`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {F G : Sheaf J (Type w)} (f : F ⟶ G) :
    IsLocallyInjective (Sheaf.imageι f) := by
  dsimp [Sheaf.imageι]
  infer_instance

end Sheaf

end CategoryTheory

