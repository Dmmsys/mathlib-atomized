/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
public import Mathlib.CategoryTheory.Limits.Shapes.Images
public import Mathlib.CategoryTheory.Limits.Shapes.RegularMono
public import Mathlib.Data.Fintype.Order
public import Mathlib.Data.Set.Subsingleton
public import Mathlib.Order.Category.FinPartOrd
public import Mathlib.Order.Category.LinOrd

/-!
# Nonempty finite linear orders

This defines `NonemptyFinLinOrd`, the category of nonempty finite linear
orders with monotone maps. This is the index category for simplicial objects.

Note: `NonemptyFinLinOrd` is *not* a subcategory of `FinBddDistLat` because its morphisms do not
preserve `⊥` and `⊤`.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

/-- The category of nonempty finite linear orders. -/
/-
**NonemptyFinLinOrd** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type (u_1 + 1)
参数：u_1 + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of nonempty finite linear orders.
-/
structure NonemptyFinLinOrd extends LinOrd where
  [nonempty : Nonempty carrier]
  [fintype : Fintype carrier]

attribute [instance] NonemptyFinLinOrd.nonempty NonemptyFinLinOrd.fintype

namespace NonemptyFinLinOrd

/-
**NonemptyFinLinOrd.** 是 Mathlib 中的一个实例，位于命名空间 `NonemptyFinLinOrd`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeSort NonemptyFinLinOrd (Type _) where
  coe X := X.carrier
/-
**NonemptyFinLinOrd.** 是 Mathlib 中的一个实例，位于命名空间 `NonemptyFinLinOrd`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LargeCategory NonemptyFinLinOrd :=
  inferInstanceAs <| Category (InducedCategory _ toLinOrd)
/-
**NonemptyFinLinOrd.** 是 Mathlib 中的一个实例，位于命名空间 `NonemptyFinLinOrd`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ConcreteCategory NonemptyFinLinOrd (· →o ·) :=
  inferInstanceAs <| ConcreteCategory (InducedCategory _ toLinOrd) _
/-
**NonemptyFinLinOrd.** 是 Mathlib 中的一个实例，位于命名空间 `NonemptyFinLinOrd`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : NonemptyFinLinOrd) : BoundedOrder X :=
  Fintype.toBoundedOrder X

/-- Construct a bundled `NonemptyFinLinOrd` from the underlying type and typeclass. -/
/-
**NonemptyFinLinOrd.of** 是 Mathlib 中的一个缩写定义，位于命名空间 `NonemptyFinLinOrd`。
形式化陈述：of (α : Type*) [Nonempty α] [Fintype α] [LinearOrder α] : NonemptyFinLinOr
d where carrier
参数：α : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a bundled `NonemptyFinLinOrd` from the underlying type and typeclass.
-/
abbrev of (α : Type*) [Nonempty α] [Fintype α] [LinearOrder α] : NonemptyFinLinOrd where
  carrier := α
/-
**NonemptyFinLinOrd.coe_of** 是 Mathlib 中的一个定理，位于命名空间 `NonemptyFinLinOrd`。
形式化陈述：coe_of (α : Type*) [Nonempty α] [Fintype α] [LinearOrder α] : ↥(of α) = α
参数：α : Type*。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_of (α : Type*) [Nonempty α] [Fintype α] [LinearOrder α] : ↥(of α) = α :=
  rfl

/-- Typecheck a `OrderHom` as a morphism in `NonemptyFinLinOrd`. -/
/-
**NonemptyFinLinOrd.ofHom** 是 Mathlib 中的一个缩写定义，位于命名空间 `NonemptyFinLinOrd`。
形式化陈述：ofHom {X Y : Type u} [Nonempty X] [LinearOrder X] [Fintype X] [Nonempty Y]
 [LinearOrder Y] [Fintype Y] (f : X ->o Y) : of X ⟶ of Y
参数：f : X ->o Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typecheck a `OrderHom` as a morphism in `NonemptyFinLinOrd`.
-/
abbrev ofHom {X Y : Type u} [Nonempty X] [LinearOrder X] [Fintype X]
    [Nonempty Y] [LinearOrder Y] [Fintype Y] (f : X →o Y) :
    of X ⟶ of Y :=
  ConcreteCategory.ofHom (C := NonemptyFinLinOrd) f

@[simp]
/-
**NonemptyFinLinOrd.hom_hom_id** 是 Mathlib 中的一个引理，位于命名空间 `NonemptyFinLinOrd`。
形式化陈述：hom_hom_id {X : NonemptyFinLinOrd} : (𝟙 X : X ⟶ X).hom.hom = OrderHom.id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_hom_id {X : NonemptyFinLinOrd} : (𝟙 X : X ⟶ X).hom.hom = OrderHom.id := rfl

/- Provided for rewriting. -/
/-
**NonemptyFinLinOrd.id_apply** 是 Mathlib 中的一个引理，位于命名空间 `NonemptyFinLinOrd`。
形式化陈述：id_apply (X : NonemptyFinLinOrd) (x : X) : (𝟙 X : X ⟶ X) x = x
参数：X : NonemptyFinLinOrd；x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.id_apply`：∀ {C : Type u} [inst : CategoryTheory.Category.
{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → FunL
ike (FC X Y) …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Provided for rewriting.
-/
lemma id_apply (X : NonemptyFinLinOrd) (x : X) :
    (𝟙 X : X ⟶ X) x = x := by simp

@[simp]
/-
**NonemptyFinLinOrd.hom_hom_comp** 是 Mathlib 中的一个引理，位于命名空间 `NonemptyFinLinOrd`。
形式化陈述：hom_hom_comp {X Y Z : NonemptyFinLinOrd} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g)
.hom.hom = g.hom.hom.comp f.hom.hom
参数：f : X ⟶ Y；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_hom_comp {X Y Z : NonemptyFinLinOrd} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom.hom = g.hom.hom.comp f.hom.hom := rfl

/- Provided for rewriting. -/
/-
**NonemptyFinLinOrd.comp_apply** 是 Mathlib 中的一个引理，位于命名空间 `NonemptyFinLinOrd`。
形式化陈述：comp_apply {X Y Z : NonemptyFinLinOrd} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) : (
f ≫ g) x = g (f x)
参数：f : X ⟶ Y；g : Y ⟶ Z；x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Provided for rewriting.
-/
lemma comp_apply {X Y Z : NonemptyFinLinOrd} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g) x = g (f x) := by simp

@[ext]
/-
**NonemptyFinLinOrd.hom_ext** 是 Mathlib 中的一个引理，位于命名空间 `NonemptyFinLinOrd`。
形式化陈述：hom_ext {X Y : NonemptyFinLinOrd} {f g : X ⟶ Y} (hf : f.hom.hom = g.hom.ho
m) : f = g
参数：hf : f.hom.hom = g.hom.hom。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.InducedCategory.hom_ext`：hom_ext {X Y : InducedCategory D
 F} {f g : X ⟶ Y} (h : f.hom = g.hom) : f = g
· 使用定理 `CategoryTheory.ConcreteCategory.ext`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y
 : C) → FunLike (FC X Y) …
-/
lemma hom_ext {X Y : NonemptyFinLinOrd} {f g : X ⟶ Y} (hf : f.hom.hom = g.hom.hom) : f = g :=
  InducedCategory.hom_ext (ConcreteCategory.ext hf)

@[simp]
/-
**NonemptyFinLinOrd.hom_hom_ofHom** 是 Mathlib 中的一个引理，位于命名空间 `NonemptyFinLinOrd`。
形式化陈述：hom_hom_ofHom {X Y : Type u} [Nonempty X] [LinearOrder X] [Fintype X] [Non
empty Y] [LinearOrder Y] [Fintype Y] (f : X ->o Y) : (ofHom f).hom.hom = f
参数：f : X ->o Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_hom_ofHom {X Y : Type u} [Nonempty X] [LinearOrder X] [Fintype X] [Nonempty Y]
    [LinearOrder Y] [Fintype Y] (f : X →o Y) :
  (ofHom f).hom.hom = f := rfl

@[simp]
/-
**NonemptyFinLinOrd.ofHom_hom** 是 Mathlib 中的一个引理，位于命名空间 `NonemptyFinLinOrd`。
形式化陈述：ofHom_hom {X Y : NonemptyFinLinOrd} (f : X ⟶ Y) : ofHom f.hom.hom = f
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonemptyFinLinOrd.nonempty`：∀ (self : NonemptyFinLinOrd), Nonempty ↑self
.toLinOrd
-/
lemma ofHom_hom {X Y : NonemptyFinLinOrd} (f : X ⟶ Y) :
    ofHom f.hom.hom = f := rfl
/-
**NonemptyFinLinOrd.** 是 Mathlib 中的一个实例，位于命名空间 `NonemptyFinLinOrd`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited NonemptyFinLinOrd :=
  ⟨of PUnit⟩
/-
**NonemptyFinLinOrd.hasForgetToLinOrd** 是 Mathlib 中的一个实例，位于命名空间 `NonemptyFinLinO
rd`。
形式化陈述：hasForgetToLinOrd : HasForget₂ NonemptyFinLinOrd LinOrd
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasForgetToLinOrd : HasForget₂ NonemptyFinLinOrd LinOrd :=
  inferInstanceAs <| HasForget₂ (InducedCategory _ toLinOrd) _
/-
**NonemptyFinLinOrd.hasForgetToFinPartOrd** 是 Mathlib 中的一个实例，位于命名空间 `NonemptyFin
LinOrd`。
形式化陈述：hasForgetToFinPartOrd : HasForget₂ NonemptyFinLinOrd FinPartOrd where forg
et₂.obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasForgetToFinPartOrd : HasForget₂ NonemptyFinLinOrd FinPartOrd where
  forget₂.obj X := .of X
  forget₂.map f := FinPartOrd.ofHom f.hom.hom

/-- Constructs an equivalence between nonempty finite linear orders from an order isomorphism
between them. -/
@[simps]
/-
**NonemptyFinLinOrd.Iso.mk** 是 Mathlib 中的一个定义，位于命名空间 `NonemptyFinLinOrd.Iso`。
形式化陈述：{α β : NonemptyFinLinOrd} → ↑α.toLinOrd ≃o ↑β.toLinOrd → (α ≅ β)
参数：α ≅ β。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NonemptyFinLinOrd.nonempty`：∀ (self : NonemptyFinLinOrd), Nonempty ↑self
.toLinOrd

--- 原说明 ---
Constructs an equivalence between nonempty finite linear orders from an order is
omorphism
between them.
-/
def Iso.mk {α β : NonemptyFinLinOrd.{u}} (e : α ≃o β) : α ≅ β where
  hom := ofHom e
  inv := ofHom e.symm

/-- `OrderDual` as a functor. -/
@[simps map]
/-
**NonemptyFinLinOrd.dual** 是 Mathlib 中的一个定义，位于命名空间 `NonemptyFinLinOrd`。
形式化陈述：dual : NonemptyFinLinOrd ⥤ NonemptyFinLinOrd where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`OrderDual` as a functor.
-/
def dual : NonemptyFinLinOrd ⥤ NonemptyFinLinOrd where
  obj X := of Xᵒᵈ
  map f := ofHom f.hom.hom.dual

/-- The equivalence between `NonemptyFinLinOrd` and itself induced by `OrderDual` both ways. -/
@[simps functor inverse]
/-
**NonemptyFinLinOrd.dualEquiv** 是 Mathlib 中的一个定义，位于命名空间 `NonemptyFinLinOrd`。
形式化陈述：dualEquiv : NonemptyFinLinOrd ≌ NonemptyFinLinOrd where functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence between `NonemptyFinLinOrd` and itself induced by `OrderDual` bo
th ways.
-/
def dualEquiv : NonemptyFinLinOrd ≌ NonemptyFinLinOrd where
  functor := dual
  inverse := dual
  unitIso := NatIso.ofComponents fun X => Iso.mk <| OrderIso.dualDual X
  counitIso := NatIso.ofComponents fun X => Iso.mk <| OrderIso.dualDual X
/-
**NonemptyFinLinOrd.mono_iff_injective** 是 Mathlib 中的一个定理，位于命名空间 `NonemptyFinLin
Ord`。
形式化陈述：mono_iff_injective {A B : NonemptyFinLinOrd.{u}} (f : A ⟶ B) : Mono f ↔ Fu
nction.Injective f
参数：f : A ⟶ B。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ULift.instNonempty_mathlib`：∀ {α : Type u} [Nonempty α], Nonempty (ULift
.{u_1, u} α)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `NonemptyFinLinOrd.nonempty`：∀ (self : NonemptyFinLinOrd), Nonempty ↑self
.toLinOrd
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用引理 `NonemptyFinLinOrd.hom_ext`：hom_ext {X Y : NonemptyFinLinOrd} {f g : X ⟶ 
Y} (hf : f.hom.hom = g.hom.hom) : f = g
· 使用定理 `OrderHom.ext`：ext (f g : α ->o β) (h : (f : α -> β) = g) : f = g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.ConcreteCategory.mono_of_injective`：mono_of_injective {X 
Y : C} (f : X ⟶ Y) (i : Function.Injective f) : Mono f
-/
theorem mono_iff_injective {A B : NonemptyFinLinOrd.{u}} (f : A ⟶ B) :
    Mono f ↔ Function.Injective f := by
  refine ⟨?_, ConcreteCategory.mono_of_injective f⟩
  intro _ a₁ a₂ h
  let X := of (ULift (Fin 1))
  let g₁ : X ⟶ A := ofHom ⟨fun _ => a₁, fun _ _ _ => by rfl⟩
  let g₂ : X ⟶ A := ofHom ⟨fun _ => a₂, fun _ _ _ => by rfl⟩
  change g₁ (ULift.up (0 : Fin 1)) = g₂ (ULift.up (0 : Fin 1))
  have eq : g₁ ≫ f = g₂ ≫ f := by
    ext
    exact h
  rw [cancel_mono] at eq
  rw [eq]

set_option backward.isDefEq.respectTransparency.types false in
/-
**NonemptyFinLinOrd.epi_iff_surjective** 是 Mathlib 中的一个定理，位于命名空间 `NonemptyFinLin
Ord`。
形式化陈述：epi_iff_surjective {A B : NonemptyFinLinOrd.{u}} (f : A ⟶ B) : Epi f ↔ Fun
ction.Surjective f
参数：f : A ⟶ B。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ULift.instNonempty_mathlib`：∀ {α : Type u} [Nonempty α], Nonempty (ULift
.{u_1, u} α)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `NonemptyFinLinOrd.nonempty`：∀ (self : NonemptyFinLinOrd), Nonempty ↑self
.toLinOrd
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Fin.zero_le`：∀ {n : ℕ} [inst : NeZero n] (a : Fin n), 0 ≤ a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用引理 `NonemptyFinLinOrd.hom_ext`：hom_ext {X Y : NonemptyFinLinOrd} {f g : X ⟶ 
Y} (hf : f.hom.hom = g.hom.hom) : f = g
· 使用定理 `OrderHom.ext`：ext (f g : α ->o β) (h : (f : α -> β) = g) : f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `OrderHom.comp_coe`：∀ {α : Type u_2} {β : Type u_3} {γ : Type u_4} [inst 
: Preorder α] [inst_1 : Preorder β] [inst_2 : Preorder γ]   (g : β →o γ) (f : α 
→o β), …
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `eq_of_le_of_not_lt`：eq_of_le_of_not_lt (h₁ : a <= b) (h₂ : ¬a < b) : a =
 b
· 使用定理 `CategoryTheory.ConcreteCategory.hom_ofHom`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (C
 → Type w)}   {inst_1 : outPara…
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `ULift.up.injEq`：∀ {α : Type s} (down down_1 : α), ({ down := down } = { 
down := down_1 }) = (down = down_1)
· 使用定理 `CategoryTheory.ConcreteCategory.epi_of_surjective`：epi_of_surjective {X 
Y : C} (f : X ⟶ Y) (s : Function.Surjective f) : Epi f
-/
theorem epi_iff_surjective {A B : NonemptyFinLinOrd.{u}} (f : A ⟶ B) :
    Epi f ↔ Function.Surjective f := by
  constructor
  · intro
    dsimp only [Function.Surjective]
    by_contra! ⟨m, hm⟩
    let Y := of (ULift (Fin 2))
    let p₁ : B ⟶ Y := ofHom
      ⟨fun b => if b < m then ULift.up 0 else ULift.up 1, fun x₁ x₂ h => by
        simp only
        split_ifs with h₁ h₂ h₂
        any_goals apply Fin.zero_le
        · exfalso
          exact h₁ (lt_of_le_of_lt h h₂)
        · rfl⟩
    let p₂ : B ⟶ Y := ofHom
      ⟨fun b => if b ≤ m then ULift.up 0 else ULift.up 1, fun x₁ x₂ h => by
        simp only
        split_ifs with h₁ h₂ h₂
        any_goals apply Fin.zero_le
        · exfalso
          exact h₁ (h.trans h₂)
        · rfl⟩
    have h : p₁ m = p₂ m := by
      congr
      rw [← cancel_epi f]
      ext a : 3
      simp only [p₁, p₂, hom_hom_comp, OrderHom.comp_coe, Function.comp_apply]
      change ite _ _ _ = ite _ _ _
      split_ifs with h₁ h₂ h₂
      any_goals rfl
      · exfalso
        exact h₂ (le_of_lt h₁)
      · exfalso
        exact hm a (eq_of_le_of_not_lt h₂ h₁)
    simp [Y, p₁, p₂, ConcreteCategory.hom_ofHom] at h
  · intro h
    exact ConcreteCategory.epi_of_surjective f h
/-
**NonemptyFinLinOrd.** 是 Mathlib 中的一个实例，位于命名空间 `NonemptyFinLinOrd`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SplitEpiCategory NonemptyFinLinOrd.{u} :=
  ⟨fun {X Y} f hf => by
    have H : ∀ y : Y, Nonempty (f ⁻¹' {y}) := by
      rw [epi_iff_surjective] at hf
      intro y
      exact Nonempty.intro ⟨(hf y).choose, (hf y).choose_spec⟩
    let φ : Y → X := fun y => (H y).some.1
    have hφ : ∀ y : Y, f (φ y) = y := fun y => (H y).some.2
    refine IsSplitEpi.mk' ⟨ofHom ⟨φ, ?_⟩, ?_⟩
    swap
    · ext b
      apply hφ
    · intro a b
      contrapose
      intro h
      simp only [not_le] at h ⊢
      suffices b ≤ a by
        apply lt_of_le_of_ne this
        rintro rfl
        exfalso
        simp at h
      have H : f (φ b) ≤ f (φ a) := f.hom.hom.monotone (le_of_lt h)
      simpa only [hφ] using H⟩
/-
**NonemptyFinLinOrd.** 是 Mathlib 中的一个实例，位于命名空间 `NonemptyFinLinOrd`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasStrongEpiMonoFactorisations NonemptyFinLinOrd.{u} :=
  ⟨fun {X Y} f => by
    let I := of (Set.image f ⊤)
    let e : X ⟶ I := ofHom ⟨fun x => ⟨f x, ⟨x, by tauto⟩⟩, fun x₁ x₂ h => f.hom.hom.monotone h⟩
    let m : I ⟶ Y := ofHom ⟨fun y => y.1, by tauto⟩
    have : Epi e := by
      rw [epi_iff_surjective]
      rintro ⟨_, y, h, rfl⟩
      exact ⟨y, rfl⟩
    have : StrongEpi e := strongEpi_of_epi e
    have : Mono m := ConcreteCategory.mono_of_injective _ (fun x y h => Subtype.ext h)
    exact ⟨⟨I, m, e, rfl⟩⟩⟩

end NonemptyFinLinOrd

/-
**nonemptyFinLinOrd_dual_comp_forget_to_linOrd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nonemptyFinLinOrd_dual_comp_forget_to_linOrd : NonemptyFinLinOrd.dual ⋙ fo
rget₂ NonemptyFinLinOrd LinOrd = forget₂ NonemptyFinLinOrd LinOrd ⋙ LinOrd.dual
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem nonemptyFinLinOrd_dual_comp_forget_to_linOrd :
    NonemptyFinLinOrd.dual ⋙ forget₂ NonemptyFinLinOrd LinOrd =
      forget₂ NonemptyFinLinOrd LinOrd ⋙ LinOrd.dual :=
  rfl

/-- The forgetful functor `NonemptyFinLinOrd ⥤ FinPartOrd` and `OrderDual` commute. -/
/-
**nonemptyFinLinOrdDualCompForgetToFinPartOrd** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：nonemptyFinLinOrdDualCompForgetToFinPartOrd : NonemptyFinLinOrd.dual ⋙ for
get₂ NonemptyFinLinOrd FinPartOrd ≅ forget₂ NonemptyFinLinOrd FinPartOrd ⋙ FinPa
rtOrd.dual where hom.app X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful functor `NonemptyFinLinOrd ⥤ FinPartOrd` and `OrderDual` commute.
-/
def nonemptyFinLinOrdDualCompForgetToFinPartOrd :
    NonemptyFinLinOrd.dual ⋙ forget₂ NonemptyFinLinOrd FinPartOrd ≅
      forget₂ NonemptyFinLinOrd FinPartOrd ⋙ FinPartOrd.dual where
  hom.app X := FinPartOrd.ofHom OrderHom.id
  inv.app X := FinPartOrd.ofHom OrderHom.id

/-- The generating arrow `i ⟶ i+1` in the category `Fin n` -/
/-
**Fin.homSucc** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Fin.homSucc {n} (i : Fin n) : i.castSucc ⟶ i.succ
参数：i : Fin n。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.castSucc_le_succ`：castSucc_le_succ {n} (i : Fin n) : i.castSucc <= i
.succ

--- 原说明 ---
The generating arrow `i ⟶ i+1` in the category `Fin n`
-/
def Fin.homSucc {n} (i : Fin n) : i.castSucc ⟶ i.succ := homOfLE (Fin.castSucc_le_succ i)

@[deprecated (since := "2026-07-18")]
alias Fin.hom_succ := Fin.homSucc
