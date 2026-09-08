/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import Mathlib.AlgebraicTopology.SimplexCategory.Augmented.Basic
public import Mathlib.CategoryTheory.Monoidal.Category

/-!
# Monoidal structure on the augmented simplex category

This file defines a monoidal structure on `AugmentedSimplexCategory`.
The tensor product of objects is characterized by the fact that the initial object `star` is
also the unit, and the fact that `⦋m⦌ ⊗ ⦋n⦌ = ⦋m + n + 1⦌` for `n m : ℕ`.

Through the (not in mathlib) equivalence between `AugmentedSimplexCategory` and the category
of finite ordinals, the tensor products corresponds to ordinal sum.

As the unit of this structure is an initial object, for every `x y : AugmentedSimplexCategory`,
there are maps `AugmentedSimplexCategory.inl x y : x ⟶ x ⊗ y` and
`AugmentedSimplexCategory.inr x y : y ⟶ x ⊗ y`. The main API for working with the tensor product
of maps is given by  `AugmentedSimplexCategory.tensorObj_hom_ext`, which characterizes maps
`x ⊗ y ⟶ z` in terms of their composition with these two maps. We also characterize the behaviour
of the associator isomorphism with respect to these maps.

-/

@[expose] public section

namespace AugmentedSimplexCategory

attribute [local aesop safe cases (rule_sets := [CategoryTheory])] CategoryTheory.WithInitial

open CategoryTheory MonoidalCategory
open scoped Simplicial

@[simp]
/-
**AugmentedSimplexCategory.eqToHom_toOrderHom** 是 Mathlib 中的一个引理，位于命名空间 `Augment
edSimplexCategory`。
形式化陈述：eqToHom_toOrderHom {x y : SimplexCategory} (h : WithInitial.of x = WithIni
tial.of y) : SimplexCategory.Hom.toOrderHom (WithInitial.down <| eqToHom h) = (F
in.castOrderIso (congrArg (fun t => t + 1) (by injection h with h; rw [h]))).toO
rderEmbedding.toOrderHom
参数：h : WithInitial.of x = WithInitial.of y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SimplexCategory.eqToHom_toOrderHom`：eqToHom_toOrderHom {x y : SimplexCat
egory} (h : x = y) : SimplexCategory.Hom.toOrderHom (eqToHom h) = (Fin.castOrder
Iso (congrArg (fun t => …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
lemma eqToHom_toOrderHom {x y : SimplexCategory} (h : WithInitial.of x = WithInitial.of y) :
    SimplexCategory.Hom.toOrderHom (WithInitial.down <| eqToHom h) =
      (Fin.castOrderIso
        (congrArg (fun t ↦ t + 1) (by injection h with h; rw [h]))).toOrderEmbedding.toOrderHom :=
  SimplexCategory.eqToHom_toOrderHom (by injection h)

/-- An auxiliary definition for the tensor product of two objects in `AugmentedSimplexCategory`. -/
-- (Impl. note): This definition could easily be inlined in
-- the definition of `tensorObjOf` below, but having it type check directly as an element
-- of `SimplexCategory` avoids having to sprinkle `WithInitial.down` everywhere.
/-
**AugmentedSimplexCategory.tensorObjOf** 是 Mathlib 中的一个缩写定义，位于命名空间 `AugmentedSim
plexCategory`。
形式化陈述：tensorObjOf (m n : SimplexCategory) : SimplexCategory
参数：m n : SimplexCategory。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
abbrev tensorObjOf (m n : SimplexCategory) : SimplexCategory := .mk (m.len + n.len + 1)

/-- The tensor product of two objects of `AugmentedSimplexCategory`. -/
/-
**AugmentedSimplexCategory.tensorObj** 是 Mathlib 中的一个定义，位于命名空间 `AugmentedSimplex
Category`。
形式化陈述：tensorObj (m n : AugmentedSimplexCategory) : AugmentedSimplexCategory
参数：m n : AugmentedSimplexCategory。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The tensor product of two objects of `AugmentedSimplexCategory`.
-/
def tensorObj (m n : AugmentedSimplexCategory) : AugmentedSimplexCategory :=
  match m, n with
  | .of m, .of n => .of <| tensorObjOf m n
  | .star, x => x
  | x, .star => x

/-- The action of the tensor product on maps coming from `SimplexCategory`. -/
/-
**AugmentedSimplexCategory.tensorHomOf** 是 Mathlib 中的一个定义，位于命名空间 `AugmentedSimpl
exCategory`。
形式化陈述：tensorHomOf {x₁ y₁ x₂ y₂ : SimplexCategory} (f₁ : x₁ ⟶ y₁) (f₂ : x₂ ⟶ y₂) 
: tensorObjOf x₁ x₂ ⟶ tensorObjOf y₁ y₂
参数：f₁ : x₁ ⟶ y₁；f₂ : x₂ ⟶ y₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The action of the tensor product on maps coming from `SimplexCategory`.
-/
def tensorHomOf {x₁ y₁ x₂ y₂ : SimplexCategory} (f₁ : x₁ ⟶ y₁) (f₂ : x₂ ⟶ y₂) :
    tensorObjOf x₁ x₂ ⟶ tensorObjOf y₁ y₂ :=
  letI f₁ : Fin ((x₁.len + 1) + (x₂.len + 1)) →o Fin ((y₁.len + 1) + (y₂.len + 1)) :=
    { toFun i :=
        Fin.addCases
          (motive := fun _ ↦ Fin <| (y₁.len + 1) + (y₂.len + 1))
          (fun i ↦ (f₁.toOrderHom i).castAdd _)
          (fun i ↦ (f₂.toOrderHom i).natAdd _)
          i
      monotone' i j h := by
        cases i using Fin.addCases <;>
        cases j using Fin.addCases <;>
        rw [Fin.le_def] at h ⊢ <;>
        simp at h ⊢ <;>
        grind only [OrderHom.apply_mono] }
  (eqToHom (congrArg _ (Nat.succ_add _ _)).symm ≫ (SimplexCategory.mkHom f₁) ≫
    eqToHom (congrArg _ (Nat.succ_add _ _)) : _ ⟶ ⦋y₁.len + y₂.len + 1⦌)

/-- The action of the tensor product on maps of `AugmentedSimplexCategory`. -/
/-
**AugmentedSimplexCategory.tensorHom** 是 Mathlib 中的一个定义，位于命名空间 `AugmentedSimplex
Category`。
形式化陈述：tensorHom {x₁ y₁ x₂ y₂ : AugmentedSimplexCategory} (f₁ : x₁ ⟶ y₁) (f₂ : x₂
 ⟶ y₂) : tensorObj x₁ x₂ ⟶ tensorObj y₁ y₂
参数：f₁ : x₁ ⟶ y₁；f₂ : x₂ ⟶ y₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The action of the tensor product on maps of `AugmentedSimplexCategory`.
-/
def tensorHom {x₁ y₁ x₂ y₂ : AugmentedSimplexCategory} (f₁ : x₁ ⟶ y₁) (f₂ : x₂ ⟶ y₂) :
    tensorObj x₁ x₂ ⟶ tensorObj y₁ y₂ :=
  match x₁, y₁, x₂, y₂, f₁, f₂ with
  | .of _, .of _, .of _, .of _, f₁, f₂ => tensorHomOf f₁ f₂
  | .of _, .of y₁, .star, .of y₂, f₁, _ =>
    f₁ ≫ ((SimplexCategory.mkHom <| (Fin.castAddOrderEmb (y₂.len + 1)).toOrderHom) ≫
      eqToHom (congrArg _ (Nat.succ_add _ _)) : ⦋y₁.len⦌ ⟶ ⦋y₁.len + y₂.len + 1⦌)
  | .star, .of y₁, .of _, .of y₂, _, f₂ =>
    f₂ ≫ ((SimplexCategory.mkHom <| (Fin.natAddOrderEmb (y₁.len + 1)).toOrderHom) ≫
      eqToHom (congrArg _ (Nat.succ_add _ _)) : ⦋y₂.len⦌ ⟶ ⦋y₁.len + y₂.len + 1⦌)
  | .star, .star, .of _, .of _, _, f₂ => f₂
  | .of _, .of _, .star, .star, f₁, _ => f₁
  | .star, _, .star, _, _, _ => WithInitial.starInitial.to _

/-- The unit for the monoidal structure on `AugmentedSimplexCategory` is the initial object. -/
/-
**AugmentedSimplexCategory.tensorUnit** 是 Mathlib 中的一个缩写定义，位于命名空间 `AugmentedSimp
lexCategory`。
形式化陈述：tensorUnit : AugmentedSimplexCategory
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The unit for the monoidal structure on `AugmentedSimplexCategory` is the initial
 object.
-/
abbrev tensorUnit : AugmentedSimplexCategory := WithInitial.star

/-- The associator isomorphism for the monoidal structure on `AugmentedSimplexCategory` -/
/-
**AugmentedSimplexCategory.associator** 是 Mathlib 中的一个定义，位于命名空间 `AugmentedSimple
xCategory`。
形式化陈述：associator (x y z : AugmentedSimplexCategory) : tensorObj (tensorObj x y) 
z ≅ tensorObj x (tensorObj y z)
参数：x y z : AugmentedSimplexCategory。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The associator isomorphism for the monoidal structure on `AugmentedSimplexCatego
ry`
-/
def associator (x y z : AugmentedSimplexCategory) :
    tensorObj (tensorObj x y) z ≅ tensorObj x (tensorObj y z) :=
  match x, y, z with
  | .of x, .of y, .of z =>
    eqToIso (congrArg (fun j ↦ WithInitial.of <| SimplexCategory.mk j)
      (by simp +arith))
  | .star, .star, .star => Iso.refl _
  | .star, .of _, .star => Iso.refl _
  | .star, .star, .of _ => Iso.refl _
  | .star, .of _, .of _ => Iso.refl _
  | .of _, .star, .star => Iso.refl _
  | .of _, .star, .of _ => Iso.refl _
  | .of _, .of _, .star => Iso.refl _

/-- The left unitor isomorphism for the monoidal structure in `AugmentedSimplexCategory` -/
/-
**AugmentedSimplexCategory.leftUnitor** 是 Mathlib 中的一个定义，位于命名空间 `AugmentedSimple
xCategory`。
形式化陈述：leftUnitor (x : AugmentedSimplexCategory) : tensorObj tensorUnit x ≅ x
参数：x : AugmentedSimplexCategory。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The left unitor isomorphism for the monoidal structure in `AugmentedSimplexCateg
ory`
-/
def leftUnitor (x : AugmentedSimplexCategory) :
    tensorObj tensorUnit x ≅ x :=
  match x with
  | .of _ => Iso.refl _
  | .star => Iso.refl _

/-- The right unitor isomorphism for the monoidal structure in `AugmentedSimplexCategory` -/
/-
**AugmentedSimplexCategory.rightUnitor** 是 Mathlib 中的一个定义，位于命名空间 `AugmentedSimpl
exCategory`。
形式化陈述：rightUnitor (x : AugmentedSimplexCategory) : tensorObj x tensorUnit ≅ x
参数：x : AugmentedSimplexCategory。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The right unitor isomorphism for the monoidal structure in `AugmentedSimplexCate
gory`
-/
def rightUnitor (x : AugmentedSimplexCategory) :
    tensorObj x tensorUnit ≅ x :=
  match x with
  | .of _ => Iso.refl _
  | .star => Iso.refl _
/-
**AugmentedSimplexCategory.** 是 Mathlib 中的一个实例，位于命名空间 `AugmentedSimplexCategory`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MonoidalCategoryStruct AugmentedSimplexCategory where
  tensorObj := tensorObj
  tensorHom := tensorHom
  tensorUnit := tensorUnit
  associator := associator
  leftUnitor := leftUnitor
  rightUnitor := rightUnitor
  whiskerLeft x _ _ f := tensorHom (𝟙 x) f
  whiskerRight f x := tensorHom f (𝟙 x)

@[local simp]
/-
**AugmentedSimplexCategory.id_tensorHom** 是 Mathlib 中的一个引理，位于命名空间 `AugmentedSimp
lexCategory`。
形式化陈述：id_tensorHom (x : AugmentedSimplexCategory) {y₁ y₂ : AugmentedSimplexCateg
ory} (f : y₁ ⟶ y₂) : 𝟙 x otimesₘ f = x ◁ f
参数：x : AugmentedSimplexCategory；f : y₁ ⟶ y₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma id_tensorHom (x : AugmentedSimplexCategory) {y₁ y₂ : AugmentedSimplexCategory}
    (f : y₁ ⟶ y₂) : 𝟙 x ⊗ₘ f = x ◁ f :=
  rfl

@[local simp]
/-
**AugmentedSimplexCategory.tensorHom_id** 是 Mathlib 中的一个引理，位于命名空间 `AugmentedSimp
lexCategory`。
形式化陈述：tensorHom_id {x₁ x₂ : AugmentedSimplexCategory} (y : AugmentedSimplexCateg
ory) (f : x₁ ⟶ x₂) : f otimesₘ 𝟙 y = f ▷ y
参数：y : AugmentedSimplexCategory；f : x₁ ⟶ x₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma tensorHom_id {x₁ x₂ : AugmentedSimplexCategory} (y : AugmentedSimplexCategory)
    (f : x₁ ⟶ x₂) : f ⊗ₘ 𝟙 y = f ▷ y :=
  rfl

@[local simp]
/-
**AugmentedSimplexCategory.whiskerLeft_id_star** 是 Mathlib 中的一个引理，位于命名空间 `Augmen
tedSimplexCategory`。
形式化陈述：whiskerLeft_id_star {x : AugmentedSimplexCategory} : x ◁ 𝟙 .star = 𝟙 _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma whiskerLeft_id_star {x : AugmentedSimplexCategory} : x ◁ 𝟙 .star = 𝟙 _ := by
  cases x <;>
  rfl

@[local simp]
/-
**AugmentedSimplexCategory.id_star_whiskerRight** 是 Mathlib 中的一个引理，位于命名空间 `Augme
ntedSimplexCategory`。
形式化陈述：id_star_whiskerRight {x : AugmentedSimplexCategory} : 𝟙 WithInitial.star ▷
 x = 𝟙 _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma id_star_whiskerRight {x : AugmentedSimplexCategory} : 𝟙 WithInitial.star ▷ x = 𝟙 _ := by
  cases x <;>
  rfl

/-- Thanks to `tensorUnit` being initial in `AugmentedSimplexCategory`, we get
a morphism `Δ ⟶ Δ ⊗ Δ'` for every pair of objects `Δ, Δ'`. -/
/-
**AugmentedSimplexCategory.inl** 是 Mathlib 中的一个定义，位于命名空间 `AugmentedSimplexCatego
ry`。
形式化陈述：inl (x y : AugmentedSimplexCategory) : x ⟶ x otimes y
参数：x y : AugmentedSimplexCategory。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Thanks to `tensorUnit` being initial in `AugmentedSimplexCategory`, we get
a morphism `Δ ⟶ Δ ⊗ Δ'` for every pair of objects `Δ, Δ'`.
-/
def inl (x y : AugmentedSimplexCategory) : x ⟶ x ⊗ y :=
  (ρ_ x).inv ≫ _ ◁ (WithInitial.starInitial.to y)

/-- Thanks to `tensorUnit` being initial in `AugmentedSimplexCategory`, we get
a morphism `Δ' ⟶ Δ ⊗ Δ'` for every pair of objects `Δ, Δ'`. -/
/-
**AugmentedSimplexCategory.inr** 是 Mathlib 中的一个定义，位于命名空间 `AugmentedSimplexCatego
ry`。
形式化陈述：inr (x y : AugmentedSimplexCategory) : y ⟶ x otimes y
参数：x y : AugmentedSimplexCategory。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Thanks to `tensorUnit` being initial in `AugmentedSimplexCategory`, we get
a morphism `Δ' ⟶ Δ ⊗ Δ'` for every pair of objects `Δ, Δ'`.
-/
def inr (x y : AugmentedSimplexCategory) : y ⟶ x ⊗ y :=
  (λ_ y).inv ≫ (WithInitial.starInitial.to x) ▷ _

/-- To ease type checking, we also provide a version of inl that lives in
`SimplexCategory`. -/
/-
**AugmentedSimplexCategory.inl'** 是 Mathlib 中的一个缩写定义，位于命名空间 `AugmentedSimplexCat
egory`。
形式化陈述：inl' (x y : SimplexCategory) : x ⟶ tensorObjOf x y
参数：x y : SimplexCategory。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
To ease type checking, we also provide a version of inl that lives in
`SimplexCategory`.
-/
abbrev inl' (x y : SimplexCategory) : x ⟶ tensorObjOf x y := WithInitial.down <| inl (.of x) (.of y)

/-- To ease type checking, we also provide a version of inr that lives in
`SimplexCategory`. -/
/-
**AugmentedSimplexCategory.inr'** 是 Mathlib 中的一个缩写定义，位于命名空间 `AugmentedSimplexCat
egory`。
形式化陈述：inr' (x y : SimplexCategory) : y ⟶ tensorObjOf x y
参数：x y : SimplexCategory。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
To ease type checking, we also provide a version of inr that lives in
`SimplexCategory`.
-/
abbrev inr' (x y : SimplexCategory) : y ⟶ tensorObjOf x y := WithInitial.down <| inr (.of x) (.of y)
/-
**AugmentedSimplexCategory.inl'_eval** 是 Mathlib 中的一个定理，位于命名空间 `AugmentedSimplex
Category`。
形式化陈述：∀ (x y : SimplexCategory) (i : Fin (x.len + 1)),   (SimplexCategory.Hom.to
OrderHom (AugmentedSimplexCategory.inl' x y)) i = Fin.cast ⋯ (Fin.castAdd (y.len
 + 1) i)
参数：x y : SimplexCategory；i : Fin (x.len + 1)；SimplexCategory.Hom.toOrderHom (Aug
mentedSimplexCategory.inl' x y)；Fin.castAdd (y.len + 1) i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.ext`：∀ {n : ℕ} {a b : Fin n}, ↑a = ↑b → a = b
· 使用定理 `Nat.succ_add`：∀ (n m : ℕ), n.succ + m = (n + m).succ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Monotone.comp`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : Preorder
 α] [inst_1 : Preorder β] [inst_2 : Preorder γ] {g : β → γ}   {f : α → β}, Monot
one…
· 使用定理 `OrderEmbedding.monotone`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorde
r α] [inst_1 : Preorder β] (f : α ↪o β), Monotone ⇑f
· 使用引理 `SimplexCategory.eqToHom_toOrderHom`：eqToHom_toOrderHom {x y : SimplexCat
egory} (h : x = y) : SimplexCategory.Hom.toOrderHom (eqToHom h) = (Fin.castOrder
Iso (congrArg (fun t => …
· 使用定理 `OrderHom.comp_id`：comp_id (f : α ->o β) : comp f id = f
· 使用定理 `Fin.castAddOrderEmb_apply`：∀ {n : ℕ} (m : ℕ) (a : Fin n), (Fin.castAddOr
derEmb m) a = Fin.castAdd m a
· 使用定理 `Fin.castOrderIso_apply`：∀ {m n : ℕ} (eq : n = m) (i : Fin n), (Fin.castO
rderIso eq) i = Fin.cast eq i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma inl'_eval (x y : SimplexCategory) (i : Fin (x.len + 1)) :
    (inl' x y).toOrderHom i = (i.castAdd _).cast (Nat.succ_add x.len (y.len + 1)) := by
  ext
  simp [inl', inl, MonoidalCategoryStruct.rightUnitor, MonoidalCategoryStruct.whiskerLeft,
    MonoidalCategoryStruct.tensorUnit, MonoidalCategoryStruct.tensorObj,
    tensorUnit, tensorHom, WithInitial.down, rightUnitor, tensorObj, CategoryStruct.id,
    CategoryStruct.comp, WithInitial.comp, WithInitial.id,
    OrderEmbedding.toOrderHom]

set_option backward.isDefEq.respectTransparency false in
/-
**AugmentedSimplexCategory.inr'_eval** 是 Mathlib 中的一个定理，位于命名空间 `AugmentedSimplex
Category`。
形式化陈述：∀ (x y : SimplexCategory) (i : Fin (y.len + 1)),   (SimplexCategory.Hom.to
OrderHom (AugmentedSimplexCategory.inr' x y)) i = Fin.cast ⋯ (Fin.natAdd x.len.s
ucc i)
参数：x y : SimplexCategory；i : Fin (y.len + 1)；SimplexCategory.Hom.toOrderHom (Aug
mentedSimplexCategory.inr' x y)；Fin.natAdd x.len.succ i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.succ_add`：∀ (n m : ℕ), n.succ + m = (n + m).succ
· 使用定理 `Fin.ext`：∀ {n : ℕ} {a b : Fin n}, ↑a = ↑b → a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Monotone.comp`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : Preorder
 α] [inst_1 : Preorder β] [inst_2 : Preorder γ] {g : β → γ}   {f : α → β}, Monot
one…
· 使用定理 `OrderEmbedding.monotone`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorde
r α] [inst_1 : Preorder β] (f : α ↪o β), Monotone ⇑f
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用引理 `SimplexCategory.eqToHom_toOrderHom`：eqToHom_toOrderHom {x y : SimplexCat
egory} (h : x = y) : SimplexCategory.Hom.toOrderHom (eqToHom h) = (Fin.castOrder
Iso (congrArg (fun t => …
· 使用定理 `Fin.natAddOrderEmb_apply`：∀ {m : ℕ} (n : ℕ) (i : Fin m), (Fin.natAddOrde
rEmb n) i = Fin.natAdd n i
· 使用定理 `Fin.castOrderIso_apply`：∀ {m n : ℕ} (eq : n = m) (i : Fin n), (Fin.castO
rderIso eq) i = Fin.cast eq i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma inr'_eval (x y : SimplexCategory) (i : Fin (y.len + 1)) :
    (inr' x y).toOrderHom i = (i.natAdd _).cast (Nat.succ_add x.len (y.len + 1)) := by
  dsimp [inr', inr, MonoidalCategoryStruct.leftUnitor, MonoidalCategoryStruct.whiskerRight,
    tensorHom, WithInitial.down, leftUnitor, tensorObj]
  ext
  simp [OrderEmbedding.toOrderHom]

/-- We can characterize morphisms out of a tensor product via their precomposition with `inl` and
`inr`. -/
@[ext]
/-
**AugmentedSimplexCategory.tensorObj_hom_ext** 是 Mathlib 中的一个定理，位于命名空间 `Augmente
dSimplexCategory`。
形式化陈述：tensorObj_hom_ext {x y z : AugmentedSimplexCategory} (f g : x otimes y ⟶ z
) (h₁ : inl _ _ ≫ f = inl _ _ ≫ g) (h₂ : inr _ _ ≫ f = inr _ _ ≫ g) : f = g
参数：f g : x otimes y ⟶ z；h₁ : inl _ _ ≫ f = inl _ _ ≫ g；h₂ : inr _ _ ≫ f = inr _ 
_ ≫ g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ConcreteCategory.ext`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y
 : C) → FunLike (FC X Y) …
· 使用定理 `OrderHom.ext`：ext (f g : α ->o β) (h : (f : α -> β) = g) : f = g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Fin.ext`：∀ {n : ℕ} {a b : Fin n}, ↑a = ↑b → a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.succ_add`：∀ (n m : ℕ), n.succ + m = (n + m).succ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `OrderHom.comp_coe`：∀ {α : Type u_2} {β : Type u_3} {γ : Type u_4} [inst 
: Preorder α] [inst_1 : Preorder β] [inst_2 : Preorder γ]   (g : β →o γ) (f : α 
→o β), …
· 使用定理 `OrderHom.ext_iff`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [i
nst_1 : Preorder β] {f g : α →o β}, f = g ↔ ⇑f = ⇑g
· 使用定理 `SimplexCategory.Hom.ext_iff`：∀ {a b : SimplexCategory} {f g : a ⟶ b}, f 
= g ↔ SimplexCategory.Hom.toOrderHom f = SimplexCategory.Hom.toOrderHom g
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.IsInitial.to_self`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {X : C} (t : CategoryTheory.Limits.IsInitial X),   
t.to X = CategoryTheory.Categ…
· 使用引理 `AugmentedSimplexCategory.whiskerLeft_id_star`：whiskerLeft_id_star {x : A
ugmentedSimplexCategory} : x ◁ 𝟙 .star = 𝟙 _
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `AugmentedSimplexCategory.id_star_whiskerRight`：id_star_whiskerRight {x :
 AugmentedSimplexCategory} : 𝟙 WithInitial.star ▷ x = 𝟙 _

--- 原说明 ---
We can characterize morphisms out of a tensor product via their precomposition w
ith `inl` and
`inr`.
-/
theorem tensorObj_hom_ext {x y z : AugmentedSimplexCategory} (f g : x ⊗ y ⟶ z)
    (h₁ : inl _ _ ≫ f = inl _ _ ≫ g)
    (h₂ : inr _ _ ≫ f = inr _ _ ≫ g) : f = g :=
  match x, y, z, f, g with
  | .of x, .of y, .of z, f, g => by
    change (tensorObjOf x y) ⟶ z at f g
    change inl' _ _ ≫ f = inl' _ _ ≫ g at h₁
    change inr' _ _ ≫ f = inr' _ _ ≫ g at h₂
    ext i
    let j : Fin ((x.len + 1) + (y.len + 1)) := i.cast (Nat.succ_add x.len (y.len + 1)).symm
    have : i = j.cast (Nat.succ_add x.len (y.len + 1)) := rfl
    rw [this]
    cases j using Fin.addCases (m := x.len + 1) (n := y.len + 1) with
    | left j =>
      rw [SimplexCategory.Hom.ext_iff, OrderHom.ext_iff] at h₁
      simpa [← inl'_eval, ConcreteCategory.hom, Fin.ext_iff] using congrFun h₁ j
    | right j =>
      rw [SimplexCategory.Hom.ext_iff, OrderHom.ext_iff] at h₂
      simpa [← inr'_eval, ConcreteCategory.hom, Fin.ext_iff] using congrFun h₂ j
  | .of x, .star, .of z, f, g => by
      simp only [inl, Category.assoc, Iso.cancel_iso_inv_left, Limits.IsInitial.to_self,
        whiskerLeft_id_star] at h₁
      simpa [Category.id_comp f, Category.id_comp g] using h₁
  | .star, .of y, .of z, f, g => by
      simp only [inr, Category.assoc, Iso.cancel_iso_inv_left, Limits.IsInitial.to_self,
        id_star_whiskerRight] at h₂
      simpa [Category.id_comp f, Category.id_comp g] using h₂
  | .star, .star, .of z, f, g => rfl
  | .star, .star, .star, f, g => rfl

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/-
**AugmentedSimplexCategory.inl_comp_tensorHom** 是 Mathlib 中的一个引理，位于命名空间 `Augment
edSimplexCategory`。
形式化陈述：inl_comp_tensorHom {x₁ y₁ x₂ y₂ : AugmentedSimplexCategory} (f₁ : x₁ ⟶ y₁)
 (f₂ : x₂ ⟶ y₂) : inl x₁ x₂ ≫ (f₁ otimesₘ f₂) = f₁ ≫ inl y₁ y₂
参数：f₁ : x₁ ⟶ y₁；f₂ : x₂ ⟶ y₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimplexCategory.Hom.ext`：∀ {a b : SimplexCategory} (f g : a ⟶ b), Simple
xCategory.Hom.toOrderHom f = SimplexCategory.Hom.toOrderHom g → f = g
· 使用定理 `OrderHom.ext`：ext (f g : α ->o β) (h : (f : α -> β) = g) : f = g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Nat.succ_add`：∀ (n m : ℕ), n.succ + m = (n + m).succ
· 使用定理 `AugmentedSimplexCategory.inl'_eval`：∀ (x y : SimplexCategory) (i : Fin (
x.len + 1)),   (SimplexCategory.Hom.toOrderHom (AugmentedSimplexCategory.inl' x 
y)) i = Fin.cast ⋯ (Fin.…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `SimplexCategory.eqToHom_toOrderHom`：eqToHom_toOrderHom {x y : SimplexCat
egory} (h : x = y) : SimplexCategory.Hom.toOrderHom (eqToHom h) = (Fin.castOrder
Iso (congrArg (fun t => …
· 使用定理 `Fin.addCases_left`：∀ {m n : ℕ} {motive : Fin (m + n) → Sort u_1} {left :
 (i : Fin m) → motive (Fin.castAdd n i)}   {right : (i : Fin n) → motive (Fin.na
tAdd m …
· 使用引理 `CategoryTheory.WithInitial.false_of_to_star`：false_of_to_star {X : C} (f
 : of X ⟶ star) : False
-/
lemma inl_comp_tensorHom {x₁ y₁ x₂ y₂ : AugmentedSimplexCategory}
    (f₁ : x₁ ⟶ y₁) (f₂ : x₂ ⟶ y₂) : inl x₁ x₂ ≫ (f₁ ⊗ₘ f₂) = f₁ ≫ inl y₁ y₂ :=
  match x₁, y₁, x₂, y₂, f₁, f₂ with
  | .of x₁, .of y₁, .of x₂, .of y₂, f₁, f₂ => by
    change inl' _ _ ≫ tensorHomOf _ _ = WithInitial.down f₁ ≫ inl' _ _
    ext i : 3
    dsimp [tensorHomOf]
    have e₁ := inl'_eval x₁ x₂ i
    have e₂ := inl'_eval y₁ y₂ <| (WithInitial.down f₁).toOrderHom i
    simp only [SimplexCategory.len_mk] at e₁ e₂
    rw [e₁, e₂]
    simp only [SimplexCategory.eqToHom_toOrderHom, SimplexCategory.len_mk,
      OrderEmbedding.toOrderHom_coe, OrderIso.coe_toOrderEmbedding, Fin.castOrderIso_apply,
      Fin.cast_cast, Fin.cast_eq_self, Fin.cast_inj]
    conv_lhs =>
      change Fin.addCases
        (fun i ↦ Fin.castAdd (y₂.len + 1) (f₁.toOrderHom i))
        (fun i ↦ Fin.natAdd (y₁.len + 1) (f₂.toOrderHom i))
        (Fin.castAdd (x₂.len + 1) i)
      rw [Fin.addCases_left]
    rfl
  | _, _, .star, _, f₁, f₂ => by cat_disch
  | .star, _, _, _, _, _ => rfl

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/-
**AugmentedSimplexCategory.inr_comp_tensorHom** 是 Mathlib 中的一个引理，位于命名空间 `Augment
edSimplexCategory`。
形式化陈述：inr_comp_tensorHom {x₁ y₁ x₂ y₂ : AugmentedSimplexCategory} (f₁ : x₁ ⟶ y₁)
 (f₂ : x₂ ⟶ y₂) : inr x₁ x₂ ≫ (f₁ otimesₘ f₂) = f₂ ≫ inr y₁ y₂
参数：f₁ : x₁ ⟶ y₁；f₂ : x₂ ⟶ y₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimplexCategory.Hom.ext`：∀ {a b : SimplexCategory} (f g : a ⟶ b), Simple
xCategory.Hom.toOrderHom f = SimplexCategory.Hom.toOrderHom g → f = g
· 使用定理 `OrderHom.ext`：ext (f g : α ->o β) (h : (f : α -> β) = g) : f = g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Nat.succ_add`：∀ (n m : ℕ), n.succ + m = (n + m).succ
· 使用定理 `AugmentedSimplexCategory.inr'_eval`：∀ (x y : SimplexCategory) (i : Fin (
y.len + 1)),   (SimplexCategory.Hom.toOrderHom (AugmentedSimplexCategory.inr' x 
y)) i = Fin.cast ⋯ (Fin.…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `SimplexCategory.eqToHom_toOrderHom`：eqToHom_toOrderHom {x y : SimplexCat
egory} (h : x = y) : SimplexCategory.Hom.toOrderHom (eqToHom h) = (Fin.castOrder
Iso (congrArg (fun t => …
· 使用定理 `Fin.addCases_right`：∀ {m n : ℕ} {motive : Fin (m + n) → Sort u_1} {left 
: (i : Fin m) → motive (Fin.castAdd n i)}   {right : (i : Fin n) → motive (Fin.n
atAdd m …
· 使用引理 `CategoryTheory.WithInitial.false_of_to_star`：false_of_to_star {X : C} (f
 : of X ⟶ star) : False
-/
lemma inr_comp_tensorHom {x₁ y₁ x₂ y₂ : AugmentedSimplexCategory}
    (f₁ : x₁ ⟶ y₁) (f₂ : x₂ ⟶ y₂) : inr x₁ x₂ ≫ (f₁ ⊗ₘ f₂) = f₂ ≫ inr y₁ y₂ :=
  match x₁, y₁, x₂, y₂, f₁, f₂ with
  | .of x₁, .of y₁, .of x₂, .of y₂, f₁, f₂ => by
    change inr' _ _ ≫ tensorHomOf _ _ = WithInitial.down f₂ ≫ inr' _ _
    ext i : 3
    dsimp [tensorHomOf]
    have e₁ := inr'_eval x₁ x₂ i
    have e₂ := inr'_eval y₁ y₂ <| (WithInitial.down f₂).toOrderHom i
    simp only [SimplexCategory.len_mk] at e₁ e₂
    rw [e₁, e₂]
    simp only [SimplexCategory.eqToHom_toOrderHom, SimplexCategory.len_mk,
      Nat.succ_eq_add_one, OrderEmbedding.toOrderHom_coe,
      OrderIso.coe_toOrderEmbedding, Fin.castOrderIso_apply,
      Fin.cast_cast, Fin.cast_eq_self, Fin.cast_inj]
    conv_lhs =>
      change Fin.addCases
        (fun i ↦ Fin.castAdd (y₂.len + 1) (f₁.toOrderHom i))
        (fun i ↦ Fin.natAdd (y₁.len + 1) (f₂.toOrderHom i))
        (Fin.natAdd (x₁.len + 1) i)
      rw [Fin.addCases_right]
    rfl
  | .star, _, _, _, f₁, f₂ => by cat_disch
  | _, _, .star, _, _, _ => rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**AugmentedSimplexCategory.inr_comp_associator** 是 Mathlib 中的一个引理，位于命名空间 `Augmen
tedSimplexCategory`。
形式化陈述：inr_comp_associator (x y z : AugmentedSimplexCategory) : inr _ _ ≫ (α_ x y
 z).hom = inr _ _ ≫ inr _ _
参数：x y z : AugmentedSimplexCategory。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimplexCategory.Hom.ext`：∀ {a b : SimplexCategory} (f g : a ⟶ b), Simple
xCategory.Hom.toOrderHom f = SimplexCategory.Hom.toOrderHom g → f = g
· 使用定理 `OrderHom.ext`：ext (f g : α ->o β) (h : (f : α -> β) = g) : f = g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `AugmentedSimplexCategory.eqToHom_toOrderHom`：eqToHom_toOrderHom {x y : S
implexCategory} (h : WithInitial.of x = WithInitial.of y) : SimplexCategory.Hom.
toOrderHom (WithInitial.down <| e…
· 使用定理 `Nat.succ_add`：∀ (n m : ℕ), n.succ + m = (n + m).succ
· 使用定理 `AugmentedSimplexCategory.inr'_eval`：∀ (x y : SimplexCategory) (i : Fin (
y.len + 1)),   (SimplexCategory.Hom.toOrderHom (AugmentedSimplexCategory.inr' x 
y)) i = Fin.cast ⋯ (Fin.…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.Internal.Linear.ExprCnstr.eq_true_of_isValid`：∀ (ctx : Nat.Internal.
Linear.Context) (c : Nat.Internal.Linear.ExprCnstr),   c.toNormPoly.isValid = tr
ue → Nat.Internal.Linear.ExprCnstr.den…
· 使用定理 `Fin.ext`：∀ {n : ℕ} {a b : Fin n}, ↑a = ↑b → a = b
-/
lemma inr_comp_associator (x y z : AugmentedSimplexCategory) :
    inr _ _ ≫ (α_ x y z).hom = inr _ _ ≫ inr _ _ :=
  match x, y, z with
  | .of x, .of y, .of z => by
    change inr' _ _ ≫ WithInitial.down _ = inr' _ _ ≫ inr' _ _
    ext i : 3
    dsimp [MonoidalCategoryStruct.associator, associator]
    simp only [eqToHom_toOrderHom, SimplexCategory.len_mk, OrderEmbedding.toOrderHom_coe,
      OrderIso.coe_toOrderEmbedding, Fin.castOrderIso_apply]
    have e₁ := inr'_eval (tensorObjOf x y) z i
    have e₂ := inr'_eval y z i
    have e₃ := inr'_eval x (tensorObjOf y z) <|
      Fin.cast (by simp +arith) <| i.natAdd (y.len + 1)
    simp only [SimplexCategory.len_mk] at e₁ e₂ e₃
    rw [e₁, e₂, e₃]
    ext; simp +arith
  | .star, _, _ => by cat_disch
  | _, .star, _ => by cat_disch
  | _, _, .star => by cat_disch

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**AugmentedSimplexCategory.inl_comp_inl_comp_associator** 是 Mathlib 中的一个引理，位于命名空
间 `AugmentedSimplexCategory`。
形式化陈述：inl_comp_inl_comp_associator (x y z : AugmentedSimplexCategory) : inl _ _ 
≫ inl _ _ ≫ (α_ x y z).hom = inl _ _
参数：x y z : AugmentedSimplexCategory。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimplexCategory.Hom.ext`：∀ {a b : SimplexCategory} (f g : a ⟶ b), Simple
xCategory.Hom.toOrderHom f = SimplexCategory.Hom.toOrderHom g → f = g
· 使用定理 `OrderHom.ext`：ext (f g : α ->o β) (h : (f : α -> β) = g) : f = g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Nat.succ_add`：∀ (n m : ℕ), n.succ + m = (n + m).succ
· 使用定理 `AugmentedSimplexCategory.inl'_eval`：∀ (x y : SimplexCategory) (i : Fin (
x.len + 1)),   (SimplexCategory.Hom.toOrderHom (AugmentedSimplexCategory.inl' x 
y)) i = Fin.cast ⋯ (Fin.…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.Internal.Linear.ExprCnstr.eq_true_of_isValid`：∀ (ctx : Nat.Internal.
Linear.Context) (c : Nat.Internal.Linear.ExprCnstr),   c.toNormPoly.isValid = tr
ue → Nat.Internal.Linear.ExprCnstr.den…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.ext`：∀ {n : ℕ} {a b : Fin n}, ↑a = ↑b → a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `AugmentedSimplexCategory.eqToHom_toOrderHom`：eqToHom_toOrderHom {x y : S
implexCategory} (h : WithInitial.of x = WithInitial.of y) : SimplexCategory.Hom.
toOrderHom (WithInitial.down <| e…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma inl_comp_inl_comp_associator (x y z : AugmentedSimplexCategory) :
    inl _ _ ≫ inl _ _ ≫ (α_ x y z).hom = inl _ _ :=
  match x, y, z with
  | .of x, .of y, .of z => by
    change inl' _ _ ≫ inl' _ _ ≫ WithInitial.down _ = inl' _ _
    ext i : 3
    dsimp [MonoidalCategoryStruct.associator, associator]
    have e₁ := inl'_eval x y i
    have e₂ := inl'_eval x (tensorObjOf y z) i
    have e₃ := inl'_eval (tensorObjOf x y) z <| Fin.cast (by simp +arith) <| i.castAdd (y.len + 1)
    simp only [SimplexCategory.len_mk] at e₁ e₂ e₃
    rw [e₁, e₂, e₃]
    ext; simp +arith
  | .star, _, _ => by cat_disch
  | _, .star, _ => by cat_disch
  | _, _, .star => by cat_disch

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**AugmentedSimplexCategory.inr_comp_inl_comp_associator** 是 Mathlib 中的一个引理，位于命名空
间 `AugmentedSimplexCategory`。
形式化陈述：inr_comp_inl_comp_associator (x y z : AugmentedSimplexCategory) : inr _ _ 
≫ inl _ _ ≫ (α_ x y z).hom = inl _ _ ≫ inr _ _
参数：x y z : AugmentedSimplexCategory。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimplexCategory.Hom.ext`：∀ {a b : SimplexCategory} (f g : a ⟶ b), Simple
xCategory.Hom.toOrderHom f = SimplexCategory.Hom.toOrderHom g → f = g
· 使用定理 `OrderHom.ext`：ext (f g : α ->o β) (h : (f : α -> β) = g) : f = g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Nat.succ_add`：∀ (n m : ℕ), n.succ + m = (n + m).succ
· 使用定理 `AugmentedSimplexCategory.inl'_eval`：∀ (x y : SimplexCategory) (i : Fin (
x.len + 1)),   (SimplexCategory.Hom.toOrderHom (AugmentedSimplexCategory.inl' x 
y)) i = Fin.cast ⋯ (Fin.…
· 使用定理 `AugmentedSimplexCategory.inr'_eval`：∀ (x y : SimplexCategory) (i : Fin (
y.len + 1)),   (SimplexCategory.Hom.toOrderHom (AugmentedSimplexCategory.inr' x 
y)) i = Fin.cast ⋯ (Fin.…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.Internal.Linear.ExprCnstr.eq_true_of_isValid`：∀ (ctx : Nat.Internal.
Linear.Context) (c : Nat.Internal.Linear.ExprCnstr),   c.toNormPoly.isValid = tr
ue → Nat.Internal.Linear.ExprCnstr.den…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.ext`：∀ {n : ℕ} {a b : Fin n}, ↑a = ↑b → a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `AugmentedSimplexCategory.eqToHom_toOrderHom`：eqToHom_toOrderHom {x y : S
implexCategory} (h : WithInitial.of x = WithInitial.of y) : SimplexCategory.Hom.
toOrderHom (WithInitial.down <| e…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma inr_comp_inl_comp_associator (x y z : AugmentedSimplexCategory) :
    inr _ _ ≫ inl _ _ ≫ (α_ x y z).hom = inl _ _ ≫ inr _ _ :=
  match x, y, z with
  | .of x, .of y, .of z => by
    change inr' _ _ ≫ inl' _ _ ≫ WithInitial.down _ = inl' _ _ ≫ inr' _ _
    ext i : 3
    dsimp [MonoidalCategoryStruct.associator, associator]
    have e₁ := inl'_eval y z i
    have e₂ := inr'_eval x y i
    have e₃ := inl'_eval (tensorObjOf x y) z <| Fin.cast (by simp +arith) <| i.natAdd (x.len + 1)
    have e₄ := inr'_eval x (tensorObjOf y z) <| Fin.cast (by simp +arith) <| i.castAdd (z.len + 1)
    simp only [SimplexCategory.len_mk] at e₁ e₂ e₃ e₄
    rw [e₁, e₂, e₃, e₄]
    ext; simp +arith
  | .star, _, _ => by cat_disch
  | _, .star, _ => by cat_disch
  | _, _, .star => by cat_disch
/-
**AugmentedSimplexCategory.tensorHom_comp_tensorHom** 是 Mathlib 中的一个定理，位于命名空间 `A
ugmentedSimplexCategory`。
形式化陈述：tensorHom_comp_tensorHom {x₁ y₁ z₁ x₂ y₂ z₂ : AugmentedSimplexCategory} (f
₁ : x₁ ⟶ y₁) (f₂ : x₂ ⟶ y₂) (g₁ : y₁ ⟶ z₁) (g₂ : y₂ ⟶ z₂) : (f₁ otimesₘ f₂) ≫ (g
₁ otimesₘ g₂) = (f₁ ≫ g₁) otimesₘ (f₂ ≫ g₂)
参数：f₁ : x₁ ⟶ y₁；f₂ : x₂ ⟶ y₂；g₁ : y₁ ⟶ z₁；g₂ : y₂ ⟶ z₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AugmentedSimplexCategory.tensorObj_hom_ext`：tensorObj_hom_ext {x y z : A
ugmentedSimplexCategory} (f g : x otimes y ⟶ z) (h₁ : inl _ _ ≫ f = inl _ _ ≫ g)
 (h₂ : inr _ _ ≫ f = inr _ _ ≫ g…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AugmentedSimplexCategory.inl_comp_tensorHom_assoc`：∀ {x₁ y₁ x₂ y₂ : Augm
entedSimplexCategory} (f₁ : x₁ ⟶ y₁) (f₂ : x₂ ⟶ y₂) {Z : AugmentedSimplexCategor
y}   (h : CategoryTheory.MonoidalCatego…
· 使用引理 `AugmentedSimplexCategory.inl_comp_tensorHom`：inl_comp_tensorHom {x₁ y₁ x
₂ y₂ : AugmentedSimplexCategory} (f₁ : x₁ ⟶ y₁) (f₂ : x₂ ⟶ y₂) : inl x₁ x₂ ≫ (f₁
 otimesₘ f₂) = f₁ ≫ inl y₁ y₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `AugmentedSimplexCategory.inr_comp_tensorHom_assoc`：∀ {x₁ y₁ x₂ y₂ : Augm
entedSimplexCategory} (f₁ : x₁ ⟶ y₁) (f₂ : x₂ ⟶ y₂) {Z : AugmentedSimplexCategor
y}   (h : CategoryTheory.MonoidalCatego…
· 使用引理 `AugmentedSimplexCategory.inr_comp_tensorHom`：inr_comp_tensorHom {x₁ y₁ x
₂ y₂ : AugmentedSimplexCategory} (f₁ : x₁ ⟶ y₁) (f₂ : x₂ ⟶ y₂) : inr x₁ x₂ ≫ (f₁
 otimesₘ f₂) = f₂ ≫ inr y₁ y₂
· 使用引理 `CategoryTheory.WithInitial.false_of_to_star`：false_of_to_star {X : C} (f
 : of X ⟶ star) : False
-/
theorem tensorHom_comp_tensorHom {x₁ y₁ z₁ x₂ y₂ z₂ : AugmentedSimplexCategory}
    (f₁ : x₁ ⟶ y₁) (f₂ : x₂ ⟶ y₂) (g₁ : y₁ ⟶ z₁) (g₂ : y₂ ⟶ z₂) :
    (f₁ ⊗ₘ f₂) ≫ (g₁ ⊗ₘ g₂) = (f₁ ≫ g₁) ⊗ₘ (f₂ ≫ g₂) := by
  cat_disch
/-
**AugmentedSimplexCategory.tensor_id** 是 Mathlib 中的一个定理，位于命名空间 `AugmentedSimplex
Category`。
形式化陈述：tensor_id (x y : AugmentedSimplexCategory) : (𝟙 x) otimesₘ (𝟙 y) = 𝟙 (x ot
imes y)
参数：x y : AugmentedSimplexCategory。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AugmentedSimplexCategory.tensorObj_hom_ext`：tensorObj_hom_ext {x y z : A
ugmentedSimplexCategory} (f g : x otimes y ⟶ z) (h₁ : inl _ _ ≫ f = inl _ _ ≫ g)
 (h₂ : inr _ _ ≫ f = inr _ _ ≫ g…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `AugmentedSimplexCategory.tensorHom_comp_tensorHom`：tensorHom_comp_tensor
Hom {x₁ y₁ z₁ x₂ y₂ z₂ : AugmentedSimplexCategory} (f₁ : x₁ ⟶ y₁) (f₂ : x₂ ⟶ y₂)
 (g₁ : y₁ ⟶ z₁) (g₂ : y₂ ⟶ z₂) : (f₁ ot…
-/
theorem tensor_id (x y : AugmentedSimplexCategory) : (𝟙 x) ⊗ₘ (𝟙 y) = 𝟙 (x ⊗ y) := by
  ext
  · simpa [inl, MonoidalCategoryStruct.whiskerLeft, MonoidalCategoryStruct.whiskerRight] using
      (tensorHom_comp_tensorHom (𝟙 x) (WithInitial.starInitial.to y) (𝟙 x) (𝟙 y))
  · simpa [inr, MonoidalCategoryStruct.whiskerLeft, MonoidalCategoryStruct.whiskerRight] using
      (tensorHom_comp_tensorHom (WithInitial.starInitial.to x) (𝟙 y) (𝟙 x) (𝟙 y))
/-
**AugmentedSimplexCategory.** 是 Mathlib 中的一个实例，位于命名空间 `AugmentedSimplexCategory`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MonoidalCategory AugmentedSimplexCategory :=
  MonoidalCategory.ofTensorHom
    (id_tensorHom_id := tensor_id)
    (tensorHom_comp_tensorHom := tensorHom_comp_tensorHom)
    (pentagon := fun w x y z ↦ by ext <;> simp [-id_tensorHom, -tensorHom_id])

end AugmentedSimplexCategory

