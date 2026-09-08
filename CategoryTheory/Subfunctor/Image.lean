/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Joël Riou
-/
module

public import Mathlib.CategoryTheory.Subfunctor.Basic
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.CategoryTheory.Limits.Types.Colimits

/-!
# The image of a subfunctor

Given a morphism of type-valued functors `p : F' ⟶ F`, we define its range
`Subfunctor.range p`. More generally, if `G' : Subfunctor F'`, we
define `G'.image p : Subfunctor F` as the image of `G'` by `f`, and
if `G : Subfunctor F`, we define its preimage `G.preimage f : Subfunctor F'`.

-/

@[expose] public section

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {F F' F'' : C ⥤ Type w}

namespace Subfunctor

section range

/-- The range of a morphism of type-valued functors, as a subfunctor of the target. -/
@[simps]
/-
**CategoryTheory.Subfunctor.range** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Subf
unctor`。
形式化陈述：range (p : F' ⟶ F) : Subfunctor F where obj U
参数：p : F' ⟶ F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The range of a morphism of type-valued functors, as a subfunctor of the target.
-/
def range (p : F' ⟶ F) : Subfunctor F where
  obj U := Set.range (p.app U)
  map := by
    rintro U V i _ ⟨x, rfl⟩
    exact ⟨_, NatTrans.naturality_apply p i x⟩

variable (F) in
/-
**CategoryTheory.Subfunctor.range_id** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.S
ubfunctor`。
形式化陈述：range_id : range (𝟙 F) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subfunctor.ext`：∀ {C : Type u} {inst : CategoryTheory.Cat
egory.{v, u} C} {F : CategoryTheory.Functor C (Type w)}   {x y : CategoryTheory.
Subfunctor F}, x.ob…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Subfunctor.range_obj`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {F F' : CategoryTheory.Functor C (Type w)} (p : F' ⟶ F)   
(U : C), (CategoryTheory.…
· 使用定理 `CategoryTheory.id_apply`：∀ {C : Type u} [inst : CategoryTheory.Category.
{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → FunL
ike (FC X Y) …
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma range_id : range (𝟙 F) = ⊤ := by aesop

set_option backward.defeqAttrib.useBackward true in
@[simp]
/-
**CategoryTheory.Subfunctor.range_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Sub
functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma range_ι (G : Subfunctor F) : range G.ι = G := by aesop

end range

section lift

variable (f : F' ⟶ F) {G : Subfunctor F} (hf : range f ≤ G)

set_option backward.defeqAttrib.useBackward true in
/-- If the image of a morphism falls in a subfunctor, then the morphism factors through it. -/
@[simps! app]
/-
**CategoryTheory.Subfunctor.lift** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Subfu
nctor`。
形式化陈述：lift : F' ⟶ G.toFunctor where app U
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If the image of a morphism falls in a subfunctor, then the morphism factors thro
ugh it.
-/
def lift : F' ⟶ G.toFunctor where
  app U := ↾fun x => ⟨f.app U x, hf U (by simp)⟩
  naturality _ _ g := by
    ext x
    simpa [Subtype.ext_iff, -NatTrans.naturality_apply] using NatTrans.naturality_apply f g x

@[reassoc (attr := simp)]
/-
**CategoryTheory.Subfunctor.lift_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Subf
unctor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lift_ι : lift f hf ≫ G.ι = f := rfl

end lift

section range

variable (p : F' ⟶ F)

/-- Given a morphism `p : F' ⟶ F` of type-valued functors, this is the morphism
from `F'` to its range. -/
/-
**CategoryTheory.Subfunctor.toRange** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Su
bfunctor`。
形式化陈述：toRange : F' ⟶ (range p).toFunctor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a morphism `p : F' ⟶ F` of type-valued functors, this is the morphism
from `F'` to its range.
-/
def toRange :
    F' ⟶ (range p).toFunctor :=
  lift p (by rfl)

@[reassoc (attr := simp)]
/-
**CategoryTheory.Subfunctor.toRange_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.S
ubfunctor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toRange_ι : toRange p ≫ (range p).ι = p := rfl

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Subfunctor.toRange_app_val** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.Subfunctor`。
形式化陈述：toRange_app_val {i : C} (x : F'.obj i) : ((toRange p).app i x).val = p.app
 i x
参数：x : F'.obj i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.types_congr_hom`：types_congr_hom {X Y : Type u} {f g : X 
⟶ Y} (h : f = g) (x : X) : f x = g x
· 使用定理 `CategoryTheory.Subfunctor.lift_app`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {F F' : CategoryTheory.Functor C (Type w)} (f : F' ⟶ F)   {
G : CategoryTheory.Subfu…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma toRange_app_val {i : C} (x : F'.obj i) :
    ((toRange p).app i x).val = p.app i x := by
  simp [toRange]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CategoryTheory.Subfunctor.range_toRange** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.Subfunctor`。
形式化陈述：range_toRange : range (toRange p) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subfunctor.ext`：∀ {C : Type u} {inst : CategoryTheory.Cat
egory.{v, u} C} {F : CategoryTheory.Functor C (Type w)}   {x y : CategoryTheory.
Subfunctor F}, x.ob…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
-/
lemma range_toRange : range (toRange p) = ⊤ := by
  ext i ⟨x, hx⟩
  dsimp at hx ⊢
  simp only [Set.mem_range, Set.mem_univ, iff_true]
  simp only [Set.range] at hx
  obtain ⟨y, rfl⟩ := hx
  exact ⟨y, rfl⟩
/-
**CategoryTheory.Subfunctor.epi_iff_range_eq_top** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.Subfunctor`。
形式化陈述：epi_iff_range_eq_top : Epi p ↔ range p = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePushouts_of_has_finite_limits`：∀ (C :
 Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFin
iteColimits C],   CategoryTheory.Limits.HasFiniteWideP…
· 使用定理 `CategoryTheory.Limits.hasFiniteColimits_of_hasColimits`：∀ (C : Type u) [
inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasColimits C], 
  CategoryTheory.Limits.HasFiniteColimits C
· 使用定理 `CategoryTheory.Limits.Types.hasColimitsOfSize`：∀ [UnivLE.{v, u}], Catego
ryTheory.Limits.HasColimitsOfSize.{w, v, u, u + 1} (Type u)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Subfunctor.range_obj`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {F F' : CategoryTheory.Functor C (Type w)} (p : F' ⟶ F)   
(U : C), (CategoryTheory.…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma epi_iff_range_eq_top :
    Epi p ↔ range p = ⊤ := by
  simp [NatTrans.epi_iff_epi_app, epi_iff_surjective, Subfunctor.ext_iff, funext_iff,
    Set.range_eq_univ]
/-
**CategoryTheory.Subfunctor.range_eq_top** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry.Subfunctor`。
形式化陈述：range_eq_top [Epi p] : range p = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.Subfunctor.epi_iff_range_eq_top`：epi_iff_range_eq_top : E
pi p ↔ range p = ⊤
-/
lemma range_eq_top [Epi p] : range p = ⊤ := by rwa [← epi_iff_range_eq_top]
/-
**CategoryTheory.Subfunctor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Subfuncto
r`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Epi (toRange p) := by simp [epi_iff_range_eq_top]
/-
**CategoryTheory.Subfunctor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Subfuncto
r`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Mono p] : IsIso (toRange p) := by
  have := mono_of_mono_fac (toRange_ι p)
  rw [NatTrans.isIso_iff_isIso_app]
  intro i
  rw [isIso_iff_bijective]
  constructor
  · rw [← mono_iff_injective]
    infer_instance
  · rw [← epi_iff_surjective]
    infer_instance
/-
**CategoryTheory.Subfunctor.range_comp_le** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.Subfunctor`。
形式化陈述：range_comp_le (f : F ⟶ F') (g : F' ⟶ F'') : range (f ≫ g) <= range g
参数：f : F ⟶ F'；g : F' ⟶ F''。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Subfunctor.range_obj`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {F F' : CategoryTheory.Functor C (Type w)} (p : F' ⟶ F)   
(U : C), (CategoryTheory.…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
lemma range_comp_le (f : F ⟶ F') (g : F' ⟶ F'') :
    range (f ≫ g) ≤ range g := fun _ _ _ ↦ by aesop

end range

section image

variable (G : Subfunctor F) (f : F ⟶ F')

/-- The image of a subfunctor by a morphism of type-valued functors. -/
@[simps]
/-
**CategoryTheory.Subfunctor.image** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Subf
unctor`。
形式化陈述：image : Subfunctor F' where obj i
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The image of a subfunctor by a morphism of type-valued functors.
-/
def image : Subfunctor F' where
  obj i := (f.app i) '' (G.obj i)
  map := by
    rintro Δ Δ' φ _ ⟨x, hx, rfl⟩
    exact ⟨F.map φ x, G.map φ hx, by apply NatTrans.naturality_apply⟩
/-
**CategoryTheory.Subfunctor.image_top** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.
Subfunctor`。
形式化陈述：image_top : (⊤ : Subfunctor F).image f = range f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subfunctor.ext`：∀ {C : Type u} {inst : CategoryTheory.Cat
egory.{v, u} C} {F : CategoryTheory.Functor C (Type w)}   {x y : CategoryTheory.
Subfunctor F}, x.ob…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Subfunctor.image_obj`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {F F' : CategoryTheory.Functor C (Type w)}   (G : Category
Theory.Subfunctor F) (f :…
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `CategoryTheory.Subfunctor.range_obj`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {F F' : CategoryTheory.Functor C (Type w)} (p : F' ⟶ F)   
(U : C), (CategoryTheory.…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma image_top : (⊤ : Subfunctor F).image f = range f := by aesop

@[simp]
/-
**CategoryTheory.Subfunctor.image_iSup** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory
.Subfunctor`。
形式化陈述：image_iSup {ι : Type*} (G : ι -> Subfunctor F) (f : F ⟶ F') : (⨆ i, G i).i
mage f = ⨆ i, (G i).image f
参数：G : ι -> Subfunctor F；f : F ⟶ F'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subfunctor.ext`：∀ {C : Type u} {inst : CategoryTheory.Cat
egory.{v, u} C} {F : CategoryTheory.Functor C (Type w)}   {x y : CategoryTheory.
Subfunctor F}, x.ob…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Subfunctor.image_obj`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {F F' : CategoryTheory.Functor C (Type w)}   (G : Category
Theory.Subfunctor F) (f :…
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用引理 `CategoryTheory.Subfunctor.iSup_obj`：iSup_obj {ι : Sort*} (S : ι -> Subfu
nctor F) (U : C) : (⨆ i, S i).obj U = ⋃ i, (S i).obj U
-/
lemma image_iSup {ι : Type*} (G : ι → Subfunctor F) (f : F ⟶ F') :
    (⨆ i, G i).image f = ⨆ i, (G i).image f := by aesop
/-
**CategoryTheory.Subfunctor.image_comp** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory
.Subfunctor`。
形式化陈述：image_comp (g : F' ⟶ F'') : G.image (f ≫ g) = (G.image f).image g
参数：g : F' ⟶ F''。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subfunctor.ext`：∀ {C : Type u} {inst : CategoryTheory.Cat
egory.{v, u} C} {F : CategoryTheory.Functor C (Type w)}   {x y : CategoryTheory.
Subfunctor F}, x.ob…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Subfunctor.image_obj`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {F F' : CategoryTheory.Functor C (Type w)}   (G : Category
Theory.Subfunctor F) (f :…
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma image_comp (g : F' ⟶ F'') :
    G.image (f ≫ g) = (G.image f).image g := by aesop
/-
**CategoryTheory.Subfunctor.range_comp** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory
.Subfunctor`。
形式化陈述：range_comp (g : F' ⟶ F'') : range (f ≫ g) = (range f).image g
参数：g : F' ⟶ F''。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subfunctor.ext`：∀ {C : Type u} {inst : CategoryTheory.Cat
egory.{v, u} C} {F : CategoryTheory.Functor C (Type w)}   {x y : CategoryTheory.
Subfunctor F}, x.ob…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Subfunctor.range_obj`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {F F' : CategoryTheory.Functor C (Type w)} (p : F' ⟶ F)   
(U : C), (CategoryTheory.…
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
· 使用定理 `CategoryTheory.Subfunctor.image_obj`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {F F' : CategoryTheory.Functor C (Type w)}   (G : Category
Theory.Subfunctor F) (f :…
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma range_comp (g : F' ⟶ F'') :
    range (f ≫ g) = (range f).image g := by aesop

end image

section preimage

/-- The preimage of a subfunctor by a morphism of type-valued functors. -/
@[simps]
/-
**CategoryTheory.Subfunctor.preimage** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.S
ubfunctor`。
形式化陈述：preimage (G : Subfunctor F) (p : F' ⟶ F) : Subfunctor F' where obj n
参数：G : Subfunctor F；p : F' ⟶ F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The preimage of a subfunctor by a morphism of type-valued functors.
-/
def preimage (G : Subfunctor F) (p : F' ⟶ F) : Subfunctor F' where
  obj n := p.app n ⁻¹' (G.obj n)
  map f := (Set.preimage_mono (G.map f)).trans (by
    simp only [Set.preimage_preimage, NatTrans.naturality_apply]
    rfl)

@[simp]
/-
**CategoryTheory.Subfunctor.preimage_id** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.Subfunctor`。
形式化陈述：preimage_id (G : Subfunctor F) : G.preimage (𝟙 F) = G
参数：G : Subfunctor F。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma preimage_id (G : Subfunctor F) :
    G.preimage (𝟙 F) = G := by aesop
/-
**CategoryTheory.Subfunctor.preimage_comp** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.Subfunctor`。
形式化陈述：preimage_comp (G : Subfunctor F) (f : F'' ⟶ F') (g : F' ⟶ F) : G.preimage 
(f ≫ g) = (G.preimage g).preimage f
参数：G : Subfunctor F；f : F'' ⟶ F'；g : F' ⟶ F。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma preimage_comp (G : Subfunctor F) (f : F'' ⟶ F') (g : F' ⟶ F) :
    G.preimage (f ≫ g) = (G.preimage g).preimage f := by aesop
/-
**CategoryTheory.Subfunctor.image_le_iff** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry.Subfunctor`。
形式化陈述：image_le_iff (G : Subfunctor F) (f : F ⟶ F') (G' : Subfunctor F') : G.imag
e f <= G' ↔ G <= G'.preimage f
参数：G : Subfunctor F；f : F ⟶ F'；G' : Subfunctor F'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Subfunctor.image_obj`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {F F' : CategoryTheory.Functor C (Type w)}   (G : Category
Theory.Subfunctor F) (f :…
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `CategoryTheory.Subfunctor.preimage_obj`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {F F' : CategoryTheory.Functor C (Type w)}   (G : Categ
oryTheory.Subfunctor F) (p :…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma image_le_iff (G : Subfunctor F) (f : F ⟶ F') (G' : Subfunctor F') :
    G.image f ≤ G' ↔ G ≤ G'.preimage f := by
  simp [Subfunctor.le_def]

/-- Given a morphism `p : F' ⟶ F` of type-valued functors and `G : Subfunctor F`,
this is the morphism from the preimage of `G` by `p` to `G`. -/
/-
**CategoryTheory.Subfunctor.fromPreimage** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Subfunctor`。
形式化陈述：fromPreimage (G : Subfunctor F) (p : F' ⟶ F) : (G.preimage p).toFunctor ⟶ 
G.toFunctor
参数：G : Subfunctor F；p : F' ⟶ F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a morphism `p : F' ⟶ F` of type-valued functors and `G : Subfunctor F`,
this is the morphism from the preimage of `G` by `p` to `G`.
-/
def fromPreimage (G : Subfunctor F) (p : F' ⟶ F) :
    (G.preimage p).toFunctor ⟶ G.toFunctor :=
  lift ((G.preimage p).ι ≫ p) (by
    rw [range_comp, range_ι, image_le_iff])

@[reassoc]
/-
**CategoryTheory.Subfunctor.fromPreimage_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.Subfunctor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma fromPreimage_ι (G : Subfunctor F) (p : F' ⟶ F) :
    G.fromPreimage p ≫ G.ι = (G.preimage p).ι ≫ p := rfl
/-
**CategoryTheory.Subfunctor.preimage_eq_top_iff** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.Subfunctor`。
形式化陈述：preimage_eq_top_iff (G : Subfunctor F) (p : F' ⟶ F) : G.preimage p = ⊤ ↔ r
ange p <= G
参数：G : Subfunctor F；p : F' ⟶ F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.Subfunctor.image_top`：image_top : (⊤ : Subfunctor F).imag
e f = range f
· 使用引理 `CategoryTheory.Subfunctor.image_le_iff`：image_le_iff (G : Subfunctor F) 
(f : F ⟶ F') (G' : Subfunctor F') : G.image f <= G' ↔ G <= G'.preimage f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma preimage_eq_top_iff (G : Subfunctor F) (p : F' ⟶ F) :
    G.preimage p = ⊤ ↔ range p ≤ G := by
  rw [← image_top, image_le_iff]
  simp

@[simp]
/-
**CategoryTheory.Subfunctor.preimage_image_of_epi** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.Subfunctor`。
形式化陈述：preimage_image_of_epi (G : Subfunctor F) (p : F' ⟶ F) [hp : Epi p] : (G.pr
eimage p).image p = G
参数：G : Subfunctor F；p : F' ⟶ F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Subfunctor.image_le_iff`：image_le_iff (G : Subfunctor F) 
(f : F ⟶ F') (G' : Subfunctor F') : G.image f <= G' ↔ G <= G'.preimage f
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePushouts_of_has_finite_limits`：∀ (C :
 Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFin
iteColimits C],   CategoryTheory.Limits.HasFiniteWideP…
· 使用定理 `CategoryTheory.Limits.hasFiniteColimits_of_hasColimits`：∀ (C : Type u) [
inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasColimits C], 
  CategoryTheory.Limits.HasFiniteColimits C
· 使用定理 `CategoryTheory.Limits.Types.hasColimitsOfSize`：∀ [UnivLE.{v, u}], Catego
ryTheory.Limits.HasColimitsOfSize.{w, v, u, u + 1} (Type u)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
-/
lemma preimage_image_of_epi (G : Subfunctor F) (p : F' ⟶ F) [hp : Epi p] :
    (G.preimage p).image p = G := by
  apply le_antisymm
  · rw [image_le_iff]
  · intro i x hx
    simp only [NatTrans.epi_iff_epi_app, epi_iff_surjective] at hp
    obtain ⟨y, rfl⟩ := hp _ x
    exact ⟨y, hx, rfl⟩

end preimage

end Subfunctor

end CategoryTheory

