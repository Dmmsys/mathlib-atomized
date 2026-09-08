/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kim Morrison, Adam Topaz
-/
module

public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.CategoryTheory.Adjunction.Reflective
public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.Util.Superscript

/-!
# Simplicial objects in a category.

A simplicial object in a category `C` is a `C`-valued presheaf on `SimplexCategory`.
(Similarly, a cosimplicial object is a functor `SimplexCategory ⥤ C`.)

## Notation

The following notations can be enabled via `open Simplicial`.

- `X _⦋n⦌` denotes the `n`-th term of a simplicial object `X`, where `n : ℕ`.
- `X ^⦋n⦌` denotes the `n`-th term of a cosimplicial object `X`, where `n : ℕ`.

The following notations can be enabled via
`open CategoryTheory.SimplicialObject.Truncated`.

- `X _⦋m⦌ₙ` denotes the `m`-th term of an `n`-truncated simplicial object `X`.
- `X ^⦋m⦌ₙ` denotes the `m`-th term of an `n`-truncated cosimplicial object `X`.
-/

@[expose] public section

open Opposite

open CategoryTheory

open CategoryTheory.Limits CategoryTheory.Functor

universe v u v' u'

namespace CategoryTheory

variable (C : Type u) [Category.{v} C]

/-- The category of simplicial objects valued in a category `C`.
This is the category of contravariant functors from `SimplexCategory` to `C`. -/
/-
**CategoryTheory.SimplicialObject** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory`。
形式化陈述：SimplicialObject
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of simplicial objects valued in a category `C`.
This is the category of contravariant functors from `SimplexCategory` to `C`.
-/
abbrev SimplicialObject :=
  SimplexCategoryᵒᵖ ⥤ C

namespace SimplicialObject

set_option quotPrecheck false in
/-- `X _⦋n⦌` denotes the `n`th-term of the simplicial object X -/
scoped[Simplicial]
  notation3:1000 X " _⦋" n "⦌" =>
      (X : CategoryTheory.SimplicialObject _).obj (Opposite.op (SimplexCategory.mk n))

open Simplicial

/-
**CategoryTheory.SimplicialObject.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Sim
plicialObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {J : Type v} [SmallCategory J] [HasLimitsOfShape J C] :
    HasLimitsOfShape J (SimplicialObject C) := by
  dsimp [SimplicialObject]
  infer_instance
/-
**CategoryTheory.SimplicialObject.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Sim
plicialObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasLimits C] : HasLimits (SimplicialObject C) :=
  ⟨inferInstance⟩
/-
**CategoryTheory.SimplicialObject.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Sim
plicialObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {J : Type v} [SmallCategory J] [HasColimitsOfShape J C] :
    HasColimitsOfShape J (SimplicialObject C) := by
  dsimp [SimplicialObject]
  infer_instance
/-
**CategoryTheory.SimplicialObject.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Sim
plicialObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasColimits C] : HasColimits (SimplicialObject C) :=
  ⟨inferInstance⟩

variable {C}

@[ext]
/-
**CategoryTheory.SimplicialObject.hom_ext** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.SimplicialObject`。
形式化陈述：hom_ext {X Y : SimplicialObject C} (f g : X ⟶ Y) (h : forall (n : SimplexC
ategoryᵒᵖ), f.app n = g.app n) : f = g
参数：f g : X ⟶ Y；h : forall (n : SimplexCategoryᵒᵖ), f.app n = g.app n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext`：∀ {C : Type u₁} {inst : CategoryTheory.Cate
gory.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Category.{v₂, u₂} D}   {
F G : CategoryThe…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
lemma hom_ext {X Y : SimplicialObject C} (f g : X ⟶ Y)
    (h : ∀ (n : SimplexCategoryᵒᵖ), f.app n = g.app n) : f = g :=
  NatTrans.ext (by ext; apply h)

variable (X : SimplicialObject C)

/-- Face maps for a simplicial object. -/
/-
**CategoryTheory.SimplicialObject.** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Sim
plicialObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Face maps for a simplicial object.
-/
def δ {n} (i : Fin (n + 2)) : X _⦋n + 1⦌ ⟶ X _⦋n⦌ :=
  X.map (SimplexCategory.δ i).op
/-
**CategoryTheory.SimplicialObject.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Sim
plicialObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δ_def {n} (i : Fin (n + 2)) : X.δ i = X.map (SimplexCategory.δ i).op := rfl

/-- Degeneracy maps for a simplicial object. -/
/-
**CategoryTheory.SimplicialObject.** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Sim
plicialObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Degeneracy maps for a simplicial object.
-/
def σ {n} (i : Fin (n + 1)) : X _⦋n⦌ ⟶ X _⦋n + 1⦌ :=
  X.map (SimplexCategory.σ i).op
/-
**CategoryTheory.SimplicialObject.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Sim
plicialObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma σ_def {n} (i : Fin (n + 1)) : X.σ i = X.map (SimplexCategory.σ i).op := rfl

/-- The diagonal of a simplex is the long edge of the simplex. -/
/-
**CategoryTheory.SimplicialObject.diagonal** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.SimplicialObject`。
形式化陈述：diagonal {n : Nat} : X _⦋n⦌ ⟶ X _⦋1⦌
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The diagonal of a simplex is the long edge of the simplex.
-/
def diagonal {n : ℕ} : X _⦋n⦌ ⟶ X _⦋1⦌ := X.map ((SimplexCategory.diag n).op)

/-- Isomorphisms from identities in ℕ. -/
/-
**CategoryTheory.SimplicialObject.eqToIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.SimplicialObject`。
形式化陈述：eqToIso {n m : Nat} (h : n = m) : X _⦋n⦌ ≅ X _⦋m⦌
参数：h : n = m。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Isomorphisms from identities in ℕ.
-/
def eqToIso {n m : ℕ} (h : n = m) : X _⦋n⦌ ≅ X _⦋m⦌ :=
  X.mapIso (CategoryTheory.eqToIso (by congr))

@[simp]
/-
**CategoryTheory.SimplicialObject.eqToIso_refl** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.SimplicialObject`。
形式化陈述：eqToIso_refl {n : Nat} (h : n = n) : X.eqToIso h = Iso.refl _
参数：h : n = n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.mapIso_refl`：mapIso_refl (F : C ⥤ D) (X : C) : F.
mapIso (Iso.refl X) = Iso.refl (F.obj X)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem eqToIso_refl {n : ℕ} (h : n = n) : X.eqToIso h = Iso.refl _ := by
  simp [eqToIso]

/-- The generic case of the first simplicial identity -/
@[reassoc]
/-
**CategoryTheory.SimplicialObject.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Sim
plicialObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The generic case of the first simplicial identity
-/
theorem δ_comp_δ {n} {i j : Fin (n + 2)} (H : i ≤ j) :
    X.δ j.succ ≫ X.δ i = X.δ (Fin.castSucc i) ≫ X.δ j := by
  dsimp [δ]
  simp only [← X.map_comp, ← op_comp, SimplexCategory.δ_comp_δ H]

@[reassoc]
/-
**CategoryTheory.SimplicialObject.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Sim
plicialObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem δ_comp_δ' {n} {i : Fin (n + 2)} {j : Fin (n + 3)} (H : Fin.castSucc i < j) :
    X.δ j ≫ X.δ i =
      X.δ (Fin.castSucc i) ≫
        X.δ (j.pred H.ne_zero) := by
  dsimp [δ]
  simp only [← X.map_comp, ← op_comp, SimplexCategory.δ_comp_δ' H]
@[reassoc]
/-
**CategoryTheory.SimplicialObject.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Sim
plicialObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem δ_comp_δ'' {n} {i : Fin (n + 3)} {j : Fin (n + 2)} (H : i ≤ Fin.castSucc j) :
    X.δ j.succ ≫ X.δ (i.castLT (Nat.lt_of_le_of_lt (Fin.le_iff_val_le_val.mp H) j.is_lt)) =
      X.δ i ≫ X.δ j := by
  dsimp [δ]
  simp only [← X.map_comp, ← op_comp, SimplexCategory.δ_comp_δ'' H]

/-- The special case of the first simplicial identity -/
@[reassoc]
/-
**CategoryTheory.SimplicialObject.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Sim
plicialObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The special case of the first simplicial identity
-/
theorem δ_comp_δ_self {n} {i : Fin (n + 2)} :
    X.δ (Fin.castSucc i) ≫ X.δ i = X.δ i.succ ≫ X.δ i := by
  dsimp [δ]
  simp only [← X.map_comp, ← op_comp, SimplexCategory.δ_comp_δ_self]

@[reassoc]
/-
**CategoryTheory.SimplicialObject.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Sim
plicialObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem δ_comp_δ_self' {n} {j : Fin (n + 3)} {i : Fin (n + 2)} (H : j = Fin.castSucc i) :
    X.δ j ≫ X.δ i = X.δ i.succ ≫ X.δ i := by
  subst H
  rw [δ_comp_δ_self]

/-- The second simplicial identity -/
@[reassoc]
/-
**CategoryTheory.SimplicialObject.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Sim
plicialObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The second simplicial identity
-/
theorem δ_comp_σ_of_le {n} {i : Fin (n + 2)} {j : Fin (n + 1)} (H : i ≤ Fin.castSucc j) :
    X.σ j.succ ≫ X.δ (Fin.castSucc i) = X.δ i ≫ X.σ j := by
  dsimp [δ, σ]
  simp only [← X.map_comp, ← op_comp, SimplexCategory.δ_comp_σ_of_le H]

/-- The first part of the third simplicial identity -/
@[reassoc]
/-
**CategoryTheory.SimplicialObject.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Sim
plicialObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The first part of the third simplicial identity
-/
theorem δ_comp_σ_self {n} {i : Fin (n + 1)} : X.σ i ≫ X.δ (Fin.castSucc i) = 𝟙 _ := by
  dsimp [δ, σ]
  simp only [← X.map_comp, ← op_comp, SimplexCategory.δ_comp_σ_self, op_id, X.map_id]

@[reassoc]
/-
**CategoryTheory.SimplicialObject.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Sim
plicialObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem δ_comp_σ_self' {n} {j : Fin (n + 2)} {i : Fin (n + 1)} (H : j = Fin.castSucc i) :
    X.σ i ≫ X.δ j = 𝟙 _ := by
  subst H
  rw [δ_comp_σ_self]

/-- The second part of the third simplicial identity -/
@[reassoc]
/-
**CategoryTheory.SimplicialObject.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Sim
plicialObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The second part of the third simplicial identity
-/
theorem δ_comp_σ_succ {n} {i : Fin (n + 1)} : X.σ i ≫ X.δ i.succ = 𝟙 _ := by
  dsimp [δ, σ]
  simp only [← X.map_comp, ← op_comp, SimplexCategory.δ_comp_σ_succ, op_id, X.map_id]

@[reassoc]
/-
**CategoryTheory.SimplicialObject.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Sim
plicialObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem δ_comp_σ_succ' {n} {j : Fin (n + 2)} {i : Fin (n + 1)} (H : j = i.succ) :
    X.σ i ≫ X.δ j = 𝟙 _ := by
  subst H
  rw [δ_comp_σ_succ]

/-- The fourth simplicial identity -/
@[reassoc]
/-
**CategoryTheory.SimplicialObject.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Sim
plicialObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The fourth simplicial identity
-/
theorem δ_comp_σ_of_gt {n} {i : Fin (n + 2)} {j : Fin (n + 1)} (H : Fin.castSucc j < i) :
    X.σ (Fin.castSucc j) ≫ X.δ i.succ = X.δ i ≫ X.σ j := by
  dsimp [δ, σ]
  simp only [← X.map_comp, ← op_comp, SimplexCategory.δ_comp_σ_of_gt H]

@[reassoc]
/-
**CategoryTheory.SimplicialObject.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Sim
plicialObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem δ_comp_σ_of_gt' {n} {i : Fin (n + 3)} {j : Fin (n + 2)} (H : j.succ < i) :
    X.σ j ≫ X.δ i =
      X.δ (i.pred H.ne_zero) ≫
        X.σ (j.castLT ((add_lt_add_iff_right 1).mp (lt_of_lt_of_le H i.is_le))) := by
  dsimp [δ, σ]
  simp only [← X.map_comp, ← op_comp, SimplexCategory.δ_comp_σ_of_gt' H]

/-- The fifth simplicial identity -/
@[reassoc]
/-
**CategoryTheory.SimplicialObject.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Sim
plicialObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The fifth simplicial identity
-/
theorem σ_comp_σ {n} {i j : Fin (n + 1)} (H : i ≤ j) :
    X.σ j ≫ X.σ (Fin.castSucc i) = X.σ i ≫ X.σ j.succ := by
  dsimp [δ, σ]
  simp only [← X.map_comp, ← op_comp, SimplexCategory.σ_comp_σ H]

open Simplicial

@[reassoc (attr := simp)]
/-
**CategoryTheory.SimplicialObject.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Sim
plicialObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem δ_naturality {X' X : SimplicialObject C} (f : X ⟶ X') {n : ℕ} (i : Fin (n + 2)) :
    X.δ i ≫ f.app (op ⦋n⦌) = f.app (op ⦋n + 1⦌) ≫ X'.δ i :=
  f.naturality _

@[reassoc (attr := simp)]
/-
**CategoryTheory.SimplicialObject.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Sim
plicialObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem σ_naturality {X' X : SimplicialObject C} (f : X ⟶ X') {n : ℕ} (i : Fin (n + 1)) :
    X.σ i ≫ f.app (op ⦋n + 1⦌) = f.app (op ⦋n⦌) ≫ X'.σ i :=
  f.naturality _

variable (C)

section

variable {D : Type*} [Category* D]

variable (D) in
/-- Functor composition induces a functor on simplicial objects. -/
@[simps!]
/-
**CategoryTheory.SimplicialObject.whiskering** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.SimplicialObject`。
形式化陈述：whiskering : (C ⥤ D) ⥤ SimplicialObject C ⥤ SimplicialObject D
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Functor composition induces a functor on simplicial objects.
-/
def whiskering : (C ⥤ D) ⥤ SimplicialObject C ⥤ SimplicialObject D :=
  whiskeringRight _ _ _

set_option backward.defeqAttrib.useBackward true in
@[simp]
/-
**CategoryTheory.SimplicialObject.whiskering_obj_obj_** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.SimplicialObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma whiskering_obj_obj_δ (F : C ⥤ D) (X : SimplicialObject C) {n : ℕ} (i : Fin (n + 2)) :
    dsimp% (((whiskering C D).obj F).obj X).δ i = F.map (X.δ i) := rfl

set_option backward.defeqAttrib.useBackward true in
@[simp]
/-
**CategoryTheory.SimplicialObject.whiskering_obj_obj_** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.SimplicialObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma whiskering_obj_obj_σ (F : C ⥤ D) (X : SimplicialObject C) {n : ℕ} (i : Fin (n + 1)) :
    dsimp% (((whiskering C D).obj F).obj X).σ i = F.map (X.σ i) := rfl

end

/-- Truncated simplicial objects. -/
/-
**CategoryTheory.SimplicialObject.Truncated** 是 Mathlib 中的一个缩写定义，位于命名空间 `Categor
yTheory.SimplicialObject`。
形式化陈述：Truncated (n : Nat)
参数：n : Nat。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Truncated simplicial objects.
-/
abbrev Truncated (n : ℕ) := (SimplexCategory.Truncated n)ᵒᵖ ⥤ C

variable {C}

namespace Truncated

variable (C) in
/-- Functor composition induces a functor on truncated simplicial objects. -/
@[simps!]
/-
**CategoryTheory.SimplicialObject.Truncated.whiskering** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.SimplicialObject.Truncated`。
形式化陈述：whiskering {n} (D : Type*) [Category* D] : (C ⥤ D) ⥤ Truncated C n ⥤ Trunc
ated D n
参数：D : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Functor composition induces a functor on truncated simplicial objects.
-/
def whiskering {n} (D : Type*) [Category* D] : (C ⥤ D) ⥤ Truncated C n ⥤ Truncated D n :=
  whiskeringRight _ _ _

open Mathlib.Tactic (subscriptTerm) in
/-- For `X : Truncated C n` and `m ≤ n`, `X _⦋m⦌ₙ` is the `m`-th term of X. The
proof `p : m ≤ n` can also be provided using the syntax `X _⦋m, p⦌ₙ`. -/
scoped syntax:max (name := mkNotation)
  term " _⦋" term ("," term)? "⦌" noWs subscriptTerm : term

open scoped SimplexCategory.Truncated in
scoped macro_rules
  | `($X:term _⦋$m:term⦌$n:subscript) =>
    -- try `decide` before `get_elem_tactic` because it is faster for goals with literals.
    `(($X : CategoryTheory.SimplicialObject.Truncated _ $n).obj
      (Opposite.op ⟨SimplexCategory.mk $m, by first | decide | get_elem_tactic |
      fail "Failed to prove truncation property. Try writing `X _⦋m, by ...⦌ₙ`."⟩))
  | `($X:term _⦋$m:term, $p:term⦌$n:subscript) =>
    `(($X : CategoryTheory.SimplicialObject.Truncated _ $n).obj
      (Opposite.op ⟨SimplexCategory.mk $m, $p⟩))

variable (C) in
/-- Further truncation of truncated simplicial objects. -/
@[simps!]
/-
**CategoryTheory.SimplicialObject.Truncated.trunc** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.SimplicialObject.Truncated`。
形式化陈述：trunc (n m : Nat) (h : m <= n
参数：n m : Nat。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Further truncation of truncated simplicial objects.
-/
def trunc (n m : ℕ) (h : m ≤ n := by lia) : Truncated C n ⥤ Truncated C m :=
  (whiskeringLeft _ _ _).obj (SimplexCategory.Truncated.incl m n).op

end Truncated

section Truncation

/-- The truncation functor from simplicial objects to truncated simplicial objects. -/
/-
**CategoryTheory.SimplicialObject.truncation** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.SimplicialObject`。
形式化陈述：truncation (n : Nat) : SimplicialObject C ⥤ SimplicialObject.Truncated C n
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The truncation functor from simplicial objects to truncated simplicial objects.
-/
def truncation (n : ℕ) : SimplicialObject C ⥤ SimplicialObject.Truncated C n :=
  (whiskeringLeft _ _ _).obj (SimplexCategory.Truncated.inclusion n).op

/-- For all `m ≤ n`, `truncation m` factors through `Truncated n`. -/
/-
**CategoryTheory.SimplicialObject.truncationCompTrunc** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.SimplicialObject`。
形式化陈述：truncationCompTrunc {n m : Nat} (h : m <= n) : truncation n ⋙ Truncated.tr
unc C n m ≅ truncation m
参数：h : m <= n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For all `m ≤ n`, `truncation m` factors through `Truncated n`.
-/
def truncationCompTrunc {n m : ℕ} (h : m ≤ n) :
    truncation n ⋙ Truncated.trunc C n m ≅ truncation m :=
  Iso.refl _

end Truncation


noncomputable section

/-- The n-skeleton as a functor `SimplicialObject.Truncated C n ⥤ SimplicialObject C`. -/
/-
**CategoryTheory.SimplicialObject.Truncated.sk** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.SimplicialObject.Truncated`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     (n : ℕ) →
       [∀ (F : CategoryTheory.Functor (SimplexCategory.Truncated n)ᵒᵖ C),       
      (SimplexCategory.Truncated.inclusion n).op.HasLeftKanExtension F] →       
  CategoryTheory.Functor (CategoryTheory.SimplicialObject.Truncated C n) (Catego
ryTheory.SimplicialObject C)
参数：n : ℕ；F : CategoryTheory.Functor (SimplexCategory.Truncated n)ᵒᵖ C；SimplexCat
egory.Truncated.inclusion n；CategoryTheory.SimplicialObject.Truncated C n；Catego
ryTheory.SimplicialObject C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The n-skeleton as a functor `SimplicialObject.Truncated C n ⥤ SimplicialObject C
`.
-/
protected abbrev Truncated.sk (n : ℕ) [∀ (F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ C),
    (SimplexCategory.Truncated.inclusion n).op.HasLeftKanExtension F] :
    SimplicialObject.Truncated C n ⥤ SimplicialObject C :=
  lan (SimplexCategory.Truncated.inclusion n).op

/-- The n-coskeleton as a functor `SimplicialObject.Truncated C n ⥤ SimplicialObject C`. -/
/-
**CategoryTheory.SimplicialObject.Truncated.cosk** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.SimplicialObject.Truncated`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     (n : ℕ) →
       [∀ (F : CategoryTheory.Functor (SimplexCategory.Truncated n)ᵒᵖ C),       
      (SimplexCategory.Truncated.inclusion n).op.HasRightKanExtension F] →      
   CategoryTheory.Functor (CategoryTheory.SimplicialObject.Truncated C n) (Categ
oryTheory.SimplicialObject C)
参数：n : ℕ；F : CategoryTheory.Functor (SimplexCategory.Truncated n)ᵒᵖ C；SimplexCat
egory.Truncated.inclusion n；CategoryTheory.SimplicialObject.Truncated C n；Catego
ryTheory.SimplicialObject C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The n-coskeleton as a functor `SimplicialObject.Truncated C n ⥤ SimplicialObject
 C`.
-/
protected abbrev Truncated.cosk (n : ℕ) [∀ (F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ C),
    (SimplexCategory.Truncated.inclusion n).op.HasRightKanExtension F] :
    SimplicialObject.Truncated C n ⥤ SimplicialObject C :=
  ran (SimplexCategory.Truncated.inclusion n).op

/-- The n-skeleton as an endofunctor on `SimplicialObject C`. -/
/-
**CategoryTheory.SimplicialObject.sk** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory
.SimplicialObject`。
形式化陈述：sk (n : Nat) [forall (F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ C), (SimplexCa
tegory.Truncated.inclusion n).op.HasLeftKanExtension F] : SimplicialObject C ⥤ S
implicialObject C
参数：n : Nat；F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ C；SimplexCategory.Truncated.inc
lusion n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The n-skeleton as an endofunctor on `SimplicialObject C`.
-/
abbrev sk (n : ℕ) [∀ (F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ C),
    (SimplexCategory.Truncated.inclusion n).op.HasLeftKanExtension F] :
    SimplicialObject C ⥤ SimplicialObject C := truncation n ⋙ Truncated.sk n

/-- The n-coskeleton as an endofunctor on `SimplicialObject C`. -/
/-
**CategoryTheory.SimplicialObject.cosk** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheo
ry.SimplicialObject`。
形式化陈述：cosk (n : Nat) [forall (F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ C), (Simplex
Category.Truncated.inclusion n).op.HasRightKanExtension F] : SimplicialObject C 
⥤ SimplicialObject C
参数：n : Nat；F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ C；SimplexCategory.Truncated.inc
lusion n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The n-coskeleton as an endofunctor on `SimplicialObject C`.
-/
abbrev cosk (n : ℕ) [∀ (F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ C),
    (SimplexCategory.Truncated.inclusion n).op.HasRightKanExtension F] :
    SimplicialObject C ⥤ SimplicialObject C := truncation n ⋙ Truncated.cosk n

end

section adjunctions
/- When the left and right Kan extensions exist, `Truncated.sk n` and `Truncated.cosk n`
respectively define left and right adjoints to `truncation n`. -/


variable (n : ℕ)
variable [∀ (F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ C),
    (SimplexCategory.Truncated.inclusion n).op.HasRightKanExtension F]
variable [∀ (F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ C),
    (SimplexCategory.Truncated.inclusion n).op.HasLeftKanExtension F]

/-- The adjunction between the n-skeleton and n-truncation. -/
/-
**CategoryTheory.SimplicialObject.skAdj** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.SimplicialObject`。
形式化陈述：skAdj : Truncated.sk (C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The adjunction between the n-skeleton and n-truncation.
-/
noncomputable def skAdj : Truncated.sk (C := C) n ⊣ truncation n :=
  lanAdjunction _ _

/-- The adjunction between n-truncation and the n-coskeleton. -/
/-
**CategoryTheory.SimplicialObject.coskAdj** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.SimplicialObject`。
形式化陈述：coskAdj : truncation (C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The adjunction between n-truncation and the n-coskeleton.
-/
noncomputable def coskAdj : truncation (C := C) n ⊣ Truncated.cosk n :=
  ranAdjunction _ _

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.SimplicialObject.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Sim
plicialObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ((sk n).obj X).IsLeftKanExtension ((skAdj n).unit.app _) := by
  dsimp [sk, skAdj]
  rw [lanAdjunction_unit]
  infer_instance

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.SimplicialObject.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Sim
plicialObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ((cosk n).obj X).IsRightKanExtension ((coskAdj n).counit.app _) := by
  dsimp [cosk, coskAdj]
  rw [ranAdjunction_counit]
  infer_instance

namespace Truncated
/- When the left and right Kan extensions exist and are pointwise Kan extensions,
`skAdj n` and `coskAdj n` are respectively coreflective and reflective. -/

variable [∀ (F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ C),
    (SimplexCategory.Truncated.inclusion n).op.HasPointwiseRightKanExtension F]
variable [∀ (F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ C),
    (SimplexCategory.Truncated.inclusion n).op.HasPointwiseLeftKanExtension F]

/-
**CategoryTheory.SimplicialObject.Truncated.cosk_reflective** 是 Mathlib 中的一个实例，位
于命名空间 `CategoryTheory.SimplicialObject.Truncated`。
形式化陈述：cosk_reflective : IsIso (coskAdj (C
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.instFullOppositeOp`：∀ {C : Type u₁} [inst : Categ
oryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{
v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.instFaithfulOppositeOp`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Catego
ry.{v₂, u₂} D]   {F : CategoryTheor…
-/
instance cosk_reflective : IsIso (coskAdj (C := C) n).counit :=
  reflective' (SimplexCategory.Truncated.inclusion n).op
/-
**CategoryTheory.SimplicialObject.Truncated.sk_coreflective** 是 Mathlib 中的一个实例，位
于命名空间 `CategoryTheory.SimplicialObject.Truncated`。
形式化陈述：sk_coreflective : IsIso (skAdj (C
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.instFullOppositeOp`：∀ {C : Type u₁} [inst : Categ
oryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{
v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.instFaithfulOppositeOp`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Catego
ry.{v₂, u₂} D]   {F : CategoryTheor…
-/
instance sk_coreflective : IsIso (skAdj (C := C) n).unit :=
  coreflective' (SimplexCategory.Truncated.inclusion n).op

/-- Since `Truncated.inclusion` is fully faithful, so is right Kan extension along it. -/
/-
**CategoryTheory.SimplicialObject.Truncated.cosk.fullyFaithful** 是 Mathlib 中的一个定
义，位于命名空间 `CategoryTheory.SimplicialObject.Truncated.cosk`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     (n : ℕ) →
       [inst_1 :           ∀ (F : CategoryTheory.Functor (SimplexCategory.Trunca
ted n)ᵒᵖ C),             (SimplexCategory.Truncated.inclusion n).op.HasRightKanE
xtension F] →         [∀ (F : CategoryTheory.Functor (SimplexCategory.Truncated 
n)ᵒᵖ C),               (SimplexCategory.Truncated.inclusion n).op.HasPointwiseRi
ghtKanExtension F] →           (CategoryTheory.SimplicialObject.Truncated.cosk n
).FullyFaithful
参数：n : ℕ；F : CategoryTheory.Functor (SimplexCategory.Truncated n)ᵒᵖ C；SimplexCat
egory.Truncated.inclusion n；F : CategoryTheory.Functor (SimplexCategory.Truncate
d n)ᵒᵖ C；SimplexCategory.Truncated.inclusion n；CategoryTheory.SimplicialObject.T
runcated.cosk n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Since `Truncated.inclusion` is fully faithful, so is right Kan extension along i
t.
-/
noncomputable def cosk.fullyFaithful :
    (Truncated.cosk (C := C) n).FullyFaithful := by
  apply Adjunction.fullyFaithfulROfIsIsoCounit (coskAdj n)
/-
**CategoryTheory.SimplicialObject.Truncated.cosk.full** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.SimplicialObject.Truncated.cosk`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (n : ℕ)   [inst_1
 :     ∀ (F : CategoryTheory.Functor (SimplexCategory.Truncated n)ᵒᵖ C),       (
SimplexCategory.Truncated.inclusion n).op.HasRightKanExtension F]   [∀ (F : Cate
goryTheory.Functor (SimplexCategory.Truncated n)ᵒᵖ C),       (SimplexCategory.Tr
uncated.inclusion n).op.HasPointwiseRightKanExtension F],   (CategoryTheory.Simp
licialObject.Truncated.cosk n).Full
参数：n : ℕ；F : CategoryTheory.Functor (SimplexCategory.Truncated n)ᵒᵖ C；SimplexCat
egory.Truncated.inclusion n；F : CategoryTheory.Functor (SimplexCategory.Truncate
d n)ᵒᵖ C；SimplexCategory.Truncated.inclusion n；CategoryTheory.SimplicialObject.T
runcated.cosk n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.FullyFaithful.full`：full : F.Full where map_surje
ctive
-/
instance cosk.full : (Truncated.cosk (C := C) n).Full := FullyFaithful.full (cosk.fullyFaithful _)
/-
**CategoryTheory.SimplicialObject.Truncated.cosk.faithful** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.SimplicialObject.Truncated.cosk`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (n : ℕ)   [inst_1
 :     ∀ (F : CategoryTheory.Functor (SimplexCategory.Truncated n)ᵒᵖ C),       (
SimplexCategory.Truncated.inclusion n).op.HasRightKanExtension F]   [∀ (F : Cate
goryTheory.Functor (SimplexCategory.Truncated n)ᵒᵖ C),       (SimplexCategory.Tr
uncated.inclusion n).op.HasPointwiseRightKanExtension F],   (CategoryTheory.Simp
licialObject.Truncated.cosk n).Faithful
参数：n : ℕ；F : CategoryTheory.Functor (SimplexCategory.Truncated n)ᵒᵖ C；SimplexCat
egory.Truncated.inclusion n；F : CategoryTheory.Functor (SimplexCategory.Truncate
d n)ᵒᵖ C；SimplexCategory.Truncated.inclusion n；CategoryTheory.SimplicialObject.T
runcated.cosk n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.FullyFaithful.faithful`：faithful : F.Faithful whe
re map_injective
-/
instance cosk.faithful : (Truncated.cosk (C := C) n).Faithful :=
  FullyFaithful.faithful (cosk.fullyFaithful _)
/-
**CategoryTheory.SimplicialObject.Truncated.coskAdj.reflective** 是 Mathlib 中的一个定
义，位于命名空间 `CategoryTheory.SimplicialObject.Truncated.coskAdj`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     (n : ℕ) →
       [inst_1 :           ∀ (F : CategoryTheory.Functor (SimplexCategory.Trunca
ted n)ᵒᵖ C),             (SimplexCategory.Truncated.inclusion n).op.HasRightKanE
xtension F] →         [∀ (F : CategoryTheory.Functor (SimplexCategory.Truncated 
n)ᵒᵖ C),               (SimplexCategory.Truncated.inclusion n).op.HasPointwiseRi
ghtKanExtension F] →           CategoryTheory.Reflective (CategoryTheory.Simplic
ialObject.Truncated.cosk n)
参数：n : ℕ；F : CategoryTheory.Functor (SimplexCategory.Truncated n)ᵒᵖ C；SimplexCat
egory.Truncated.inclusion n；F : CategoryTheory.Functor (SimplexCategory.Truncate
d n)ᵒᵖ C；SimplexCategory.Truncated.inclusion n；CategoryTheory.SimplicialObject.T
runcated.cosk n。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.SimplicialObject.Truncated.cosk.full`：∀ {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C] (n : ℕ)   [inst_1 :     ∀ (F : CategoryThe
ory.Functor (SimplexCategory.Truncated n)…
· 使用定理 `CategoryTheory.SimplicialObject.Truncated.cosk.faithful`：∀ {C : Type u} 
[inst : CategoryTheory.Category.{v, u} C] (n : ℕ)   [inst_1 :     ∀ (F : Categor
yTheory.Functor (SimplexCategory.Truncated n)…
-/
noncomputable instance coskAdj.reflective : Reflective (Truncated.cosk (C := C) n) :=
  Reflective.mk (truncation _) (coskAdj _)

/-- Since `Truncated.inclusion` is fully faithful, so is left Kan extension along it. -/
/-
**CategoryTheory.SimplicialObject.Truncated.sk.fullyFaithful** 是 Mathlib 中的一个定义，
位于命名空间 `CategoryTheory.SimplicialObject.Truncated.sk`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     (n : ℕ) →
       [inst_1 :           ∀ (F : CategoryTheory.Functor (SimplexCategory.Trunca
ted n)ᵒᵖ C),             (SimplexCategory.Truncated.inclusion n).op.HasLeftKanEx
tension F] →         [∀ (F : CategoryTheory.Functor (SimplexCategory.Truncated n
)ᵒᵖ C),               (SimplexCategory.Truncated.inclusion n).op.HasPointwiseLef
tKanExtension F] →           (CategoryTheory.SimplicialObject.Truncated.sk n).Fu
llyFaithful
参数：n : ℕ；F : CategoryTheory.Functor (SimplexCategory.Truncated n)ᵒᵖ C；SimplexCat
egory.Truncated.inclusion n；F : CategoryTheory.Functor (SimplexCategory.Truncate
d n)ᵒᵖ C；SimplexCategory.Truncated.inclusion n；CategoryTheory.SimplicialObject.T
runcated.sk n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Since `Truncated.inclusion` is fully faithful, so is left Kan extension along it
.
-/
noncomputable def sk.fullyFaithful : (Truncated.sk (C := C) n).FullyFaithful :=
  Adjunction.fullyFaithfulLOfIsIsoUnit (skAdj n)
/-
**CategoryTheory.SimplicialObject.Truncated.sk.full** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.SimplicialObject.Truncated.sk`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (n : ℕ)   [inst_1
 :     ∀ (F : CategoryTheory.Functor (SimplexCategory.Truncated n)ᵒᵖ C),       (
SimplexCategory.Truncated.inclusion n).op.HasLeftKanExtension F]   [∀ (F : Categ
oryTheory.Functor (SimplexCategory.Truncated n)ᵒᵖ C),       (SimplexCategory.Tru
ncated.inclusion n).op.HasPointwiseLeftKanExtension F],   (CategoryTheory.Simpli
cialObject.Truncated.sk n).Full
参数：n : ℕ；F : CategoryTheory.Functor (SimplexCategory.Truncated n)ᵒᵖ C；SimplexCat
egory.Truncated.inclusion n；F : CategoryTheory.Functor (SimplexCategory.Truncate
d n)ᵒᵖ C；SimplexCategory.Truncated.inclusion n；CategoryTheory.SimplicialObject.T
runcated.sk n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.FullyFaithful.full`：full : F.Full where map_surje
ctive
-/
instance sk.full : (Truncated.sk (C := C) n).Full := FullyFaithful.full (sk.fullyFaithful _)
/-
**CategoryTheory.SimplicialObject.Truncated.sk.faithful** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.SimplicialObject.Truncated.sk`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (n : ℕ)   [inst_1
 :     ∀ (F : CategoryTheory.Functor (SimplexCategory.Truncated n)ᵒᵖ C),       (
SimplexCategory.Truncated.inclusion n).op.HasLeftKanExtension F]   [∀ (F : Categ
oryTheory.Functor (SimplexCategory.Truncated n)ᵒᵖ C),       (SimplexCategory.Tru
ncated.inclusion n).op.HasPointwiseLeftKanExtension F],   (CategoryTheory.Simpli
cialObject.Truncated.sk n).Faithful
参数：n : ℕ；F : CategoryTheory.Functor (SimplexCategory.Truncated n)ᵒᵖ C；SimplexCat
egory.Truncated.inclusion n；F : CategoryTheory.Functor (SimplexCategory.Truncate
d n)ᵒᵖ C；SimplexCategory.Truncated.inclusion n；CategoryTheory.SimplicialObject.T
runcated.sk n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.FullyFaithful.faithful`：faithful : F.Faithful whe
re map_injective
-/
instance sk.faithful : (Truncated.sk (C := C) n).Faithful :=
  FullyFaithful.faithful (sk.fullyFaithful _)
/-
**CategoryTheory.SimplicialObject.Truncated.skAdj.coreflective** 是 Mathlib 中的一个定
义，位于命名空间 `CategoryTheory.SimplicialObject.Truncated.skAdj`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     (n : ℕ) →
       [inst_1 :           ∀ (F : CategoryTheory.Functor (SimplexCategory.Trunca
ted n)ᵒᵖ C),             (SimplexCategory.Truncated.inclusion n).op.HasLeftKanEx
tension F] →         [∀ (F : CategoryTheory.Functor (SimplexCategory.Truncated n
)ᵒᵖ C),               (SimplexCategory.Truncated.inclusion n).op.HasPointwiseLef
tKanExtension F] →           CategoryTheory.Coreflective (CategoryTheory.Simplic
ialObject.Truncated.sk n)
参数：n : ℕ；F : CategoryTheory.Functor (SimplexCategory.Truncated n)ᵒᵖ C；SimplexCat
egory.Truncated.inclusion n；F : CategoryTheory.Functor (SimplexCategory.Truncate
d n)ᵒᵖ C；SimplexCategory.Truncated.inclusion n；CategoryTheory.SimplicialObject.T
runcated.sk n。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.SimplicialObject.Truncated.sk.full`：∀ {C : Type u} [inst 
: CategoryTheory.Category.{v, u} C] (n : ℕ)   [inst_1 :     ∀ (F : CategoryTheor
y.Functor (SimplexCategory.Truncated n)…
· 使用定理 `CategoryTheory.SimplicialObject.Truncated.sk.faithful`：∀ {C : Type u} [i
nst : CategoryTheory.Category.{v, u} C] (n : ℕ)   [inst_1 :     ∀ (F : CategoryT
heory.Functor (SimplexCategory.Truncated n)…
-/
noncomputable instance skAdj.coreflective : Coreflective (Truncated.sk (C := C) n) :=
  Coreflective.mk (truncation _) (skAdj _)

end Truncated

end adjunctions

variable (C)

/-- The constant simplicial object is the constant functor. -/
/-
**CategoryTheory.SimplicialObject.const** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryThe
ory.SimplicialObject`。
形式化陈述：const : C ⥤ SimplicialObject C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The constant simplicial object is the constant functor.
-/
abbrev const : C ⥤ SimplicialObject C :=
  CategoryTheory.Functor.const _

/-- The category of augmented simplicial objects, defined as a comma category. -/
@[implicit_reducible]
/-
**CategoryTheory.SimplicialObject.Augmented** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.SimplicialObject`。
形式化陈述：Augmented
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of augmented simplicial objects, defined as a comma category.
-/
def Augmented :=
  Comma (𝟭 (SimplicialObject C)) (const C)

@[simps!]
/-
**CategoryTheory.SimplicialObject.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Sim
plicialObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Category (Augmented C) :=
  inferInstanceAs <| Category (Comma _ _)

variable {C}

namespace Augmented

@[ext]
/-
**CategoryTheory.SimplicialObject.Augmented.hom_ext** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.SimplicialObject.Augmented`。
形式化陈述：hom_ext {X Y : Augmented C} (f g : X ⟶ Y) (h₁ : f.left = g.left) (h₂ : f.r
ight = g.right) : f = g
参数：f g : X ⟶ Y；h₁ : f.left = g.left；h₂ : f.right = g.right。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Comma.hom_ext`：hom_ext (f g : X ⟶ Y) (h₁ : f.left = g.lef
t) (h₂ : f.right = g.right) : f = g
-/
lemma hom_ext {X Y : Augmented C} (f g : X ⟶ Y) (h₁ : f.left = g.left) (h₂ : f.right = g.right) :
    f = g :=
  Comma.hom_ext _ _ h₁ h₂

/-- Drop the augmentation. -/
@[simps!, implicit_reducible]
/-
**CategoryTheory.SimplicialObject.Augmented.drop** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.SimplicialObject.Augmented`。
形式化陈述：drop : Augmented C ⥤ SimplicialObject C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Drop the augmentation.
-/
def drop : Augmented C ⥤ SimplicialObject C :=
  Comma.fst _ _

/-- The point of the augmentation. -/
@[simps!, implicit_reducible]
/-
**CategoryTheory.SimplicialObject.Augmented.point** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.SimplicialObject.Augmented`。
形式化陈述：point : Augmented C ⥤ C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The point of the augmentation.
-/
def point : Augmented C ⥤ C :=
  Comma.snd _ _

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
/-
**CategoryTheory.SimplicialObject.Augmented.w_app** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.SimplicialObject.Augmented`。
形式化陈述：w_app {X Y : Augmented C} (f : X ⟶ Y) (n : SimplexCategoryᵒᵖ) : dsimp% f.l
eft.app n ≫ Y.hom.app n = X.hom.app n ≫ f.right
参数：f : X ⟶ Y；n : SimplexCategoryᵒᵖ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.congr_app`：congr_app {F G : C ⥤ D} {α β : NatTrans F G} (
h : α = β) (X : C) : α.app X = β.app X
· 使用定理 `CategoryTheory.CommaMorphism.w`：∀ {A : Type u₁} [inst : CategoryTheory.C
ategory.{v₁, u₁} A] {B : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} B] 
  {T : Type u₃} [ins…

--- 原说明 ---
`respectTransparency.types true` changes the auto-generated lemmas' signature
-/
lemma w_app {X Y : Augmented C} (f : X ⟶ Y) (n : SimplexCategoryᵒᵖ) :
    dsimp% f.left.app n ≫ Y.hom.app n = X.hom.app n ≫ f.right :=
  congr_app f.w n

set_option backward.isDefEq.respectTransparency false in
/-- The functor from augmented objects to arrows. -/
@[simps]
/-
**CategoryTheory.SimplicialObject.Augmented.toArrow** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.SimplicialObject.Augmented`。
形式化陈述：toArrow : Augmented C ⥤ Arrow C where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor from augmented objects to arrows.
-/
def toArrow : Augmented C ⥤ Arrow C where
  obj X :=
    { left := drop.obj X _⦋0⦌
      right := point.obj X
      hom := X.hom.app _ }
  map η :=
    { left := (drop.map η).app _
      right := point.map η
      w := by simp [w_app] }

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- The compatibility of a morphism with the augmentation, on 0-simplices -/
@[reassoc]
/-
**CategoryTheory.SimplicialObject.Augmented.w** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.SimplicialObject.Augmented`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The compatibility of a morphism with the augmentation, on 0-simplices
-/
theorem w₀ {X Y : Augmented C} (f : X ⟶ Y) :
    dsimp% (Augmented.drop.map f).app (op ⦋0⦌) ≫ Y.hom.app (op ⦋0⦌) =
      X.hom.app (op ⦋0⦌) ≫ Augmented.point.map f :=
  congr_app f.w (op ⦋0⦌)

variable (C)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Functor composition induces a functor on augmented simplicial objects. -/
@[simp]
/-
**CategoryTheory.SimplicialObject.Augmented.whiskeringObj** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.SimplicialObject.Augmented`。
形式化陈述：whiskeringObj (D : Type*) [Category* D] (F : C ⥤ D) : Augmented C ⥤ Augmen
ted D where obj X
参数：D : Type*；F : C ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Functor composition induces a functor on augmented simplicial objects.
-/
def whiskeringObj (D : Type*) [Category* D] (F : C ⥤ D) : Augmented C ⥤ Augmented D where
  obj X :=
    { left := ((whiskering _ _).obj F).obj (drop.obj X)
      right := F.obj (point.obj X)
      hom := whiskerRight X.hom F ≫ (Functor.constComp _ _ _).hom }
  map η :=
    { left := whiskerRight η.left _
      right := F.map η.right
      w := by ext; simp [← Functor.map_comp, w_app] }

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Functor composition induces a functor on augmented simplicial objects. -/
@[simps]
/-
**CategoryTheory.SimplicialObject.Augmented.whiskering** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.SimplicialObject.Augmented`。
形式化陈述：whiskering (D : Type u') [Category.{v'} D] : (C ⥤ D) ⥤ Augmented C ⥤ Augme
nted D where obj
参数：D : Type u'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Functor composition induces a functor on augmented simplicial objects.
-/
def whiskering (D : Type u') [Category.{v'} D] : (C ⥤ D) ⥤ Augmented C ⥤ Augmented D where
  obj := whiskeringObj _ _
  map η :=
    { app := fun A =>
        { left := whiskerLeft _ η
          right := η.app _
          w := by
            ext n
            dsimp
            rw [Category.comp_id, Category.comp_id, η.naturality] } }
  map_comp := fun _ _ => by ext <;> rfl

variable {C}

/-- The constant augmented simplicial object functor. -/
@[simps]
/-
**CategoryTheory.SimplicialObject.Augmented.const** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.SimplicialObject.Augmented`。
形式化陈述：const : C ⥤ Augmented C where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The constant augmented simplicial object functor.
-/
def const : C ⥤ Augmented C where
  obj X :=
    { left := (SimplicialObject.const C).obj X
      right := X
      hom := 𝟙 _ }
  map f :=
    { left := (SimplicialObject.const C).map f
      right := f }

end Augmented

set_option backward.defeqAttrib.useBackward true in
/-- Augment a simplicial object with an object. -/
@[simps]
/-
**CategoryTheory.SimplicialObject.augment** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.SimplicialObject`。
形式化陈述：augment (X : SimplicialObject C) (X₀ : C) (f : X _⦋0⦌ ⟶ X₀) (w : forall (i
 : SimplexCategory) (g₁ g₂ : ⦋0⦌ ⟶ i), X.map g₁.op ≫ f = X.map g₂.op ≫ f) : Simp
licialObject.Augmented C where left
参数：X : SimplicialObject C；X₀ : C；f : X _⦋0⦌ ⟶ X₀；w : forall (i : SimplexCategory
) (g₁ g₂ : ⦋0⦌ ⟶ i), X.map g₁.op ≫ f = X.map g₂.op ≫ f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Augment a simplicial object with an object.
-/
def augment (X : SimplicialObject C) (X₀ : C) (f : X _⦋0⦌ ⟶ X₀)
    (w : ∀ (i : SimplexCategory) (g₁ g₂ : ⦋0⦌ ⟶ i),
      X.map g₁.op ≫ f = X.map g₂.op ≫ f) :
    SimplicialObject.Augmented C where
  left := X
  right := X₀
  hom :=
    { app := fun _ => X.map (SimplexCategory.const _ _ 0).op ≫ f
      naturality := by
        intro i j g
        dsimp
        rw [← g.op_unop]
        simpa only [← X.map_comp, ← Category.assoc, Category.comp_id, ← op_comp] using w _ _ _ }

-- Not `@[simp]` since `simp` can prove this.
set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.SimplicialObject.augment_hom_zero** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.SimplicialObject`。
形式化陈述：augment_hom_zero (X : SimplicialObject C) (X₀ : C) (f : X _⦋0⦌ ⟶ X₀) (w) :
 (X.augment X₀ f w).hom.app (op ⦋0⦌) = f
参数：X : SimplicialObject C；X₀ : C；f : X _⦋0⦌ ⟶ X₀；w。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.SimplicialObject.augment_hom_app`：∀ {C : Type u} [inst : 
CategoryTheory.Category.{v, u} C] (X : CategoryTheory.SimplicialObject C) (X₀ : 
C)   (f : X.obj (Opposite.op { len :=…
· 使用引理 `SimplexCategory.const_eq_id`：const_eq_id : const ⦋0⦌ ⦋0⦌ 0 = 𝟙 _
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem augment_hom_zero (X : SimplicialObject C) (X₀ : C) (f : X _⦋0⦌ ⟶ X₀) (w) :
    (X.augment X₀ f w).hom.app (op ⦋0⦌) = f := by simp

set_option backward.defeqAttrib.useBackward true in
/-- The augmented simplicial object that is deduced from a simplicial object and
a terminal object. -/
@[simps!]
/-
**CategoryTheory.SimplicialObject.augmentOfIsTerminal** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.SimplicialObject`。
形式化陈述：augmentOfIsTerminal (X : SimplicialObject C) {T : C} (hT : IsTerminal T) :
 Augmented C where left
参数：X : SimplicialObject C；hT : IsTerminal T。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The augmented simplicial object that is deduced from a simplicial object and
a terminal object.
-/
def augmentOfIsTerminal (X : SimplicialObject C) {T : C} (hT : IsTerminal T) :
    Augmented C where
  left := X
  right := T
  hom := { app _ := hT.from _ }

end SimplicialObject

/-- Cosimplicial objects. -/
/-
**CategoryTheory.CosimplicialObject** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：CosimplicialObject
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Cosimplicial objects.
-/
def CosimplicialObject :=
  SimplexCategory ⥤ C

namespace CosimplicialObject

@[simps!]
/-
**CategoryTheory.CosimplicialObject.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.C
osimplicialObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Category (CosimplicialObject C) := by
  dsimp only [CosimplicialObject]
  infer_instance

/-- `X ^⦋n⦌` denotes the `n`th-term of the cosimplicial object X -/
scoped[Simplicial]
  notation3:1000 X " ^⦋" n "⦌" =>
    (X : CategoryTheory.CosimplicialObject _).obj (SimplexCategory.mk n)

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.CosimplicialObject.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.C
osimplicialObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {J : Type v} [SmallCategory J] [HasLimitsOfShape J C] :
    HasLimitsOfShape J (CosimplicialObject C) := by
  dsimp [CosimplicialObject]
  infer_instance
/-
**CategoryTheory.CosimplicialObject.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.C
osimplicialObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasLimits C] : HasLimits (CosimplicialObject C) :=
  ⟨inferInstance⟩

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.CosimplicialObject.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.C
osimplicialObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {J : Type v} [SmallCategory J] [HasColimitsOfShape J C] :
    HasColimitsOfShape J (CosimplicialObject C) := by
  dsimp [CosimplicialObject]
  infer_instance
/-
**CategoryTheory.CosimplicialObject.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.C
osimplicialObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasColimits C] : HasColimits (CosimplicialObject C) :=
  ⟨inferInstance⟩

variable {C}

@[ext]
/-
**CategoryTheory.CosimplicialObject.hom_ext** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.CosimplicialObject`。
形式化陈述：hom_ext {X Y : CosimplicialObject C} (f g : X ⟶ Y) (h : forall (n : Simple
xCategory), f.app n = g.app n) : f = g
参数：f g : X ⟶ Y；h : forall (n : SimplexCategory), f.app n = g.app n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext`：∀ {C : Type u₁} {inst : CategoryTheory.Cate
gory.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Category.{v₂, u₂} D}   {
F G : CategoryThe…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
lemma hom_ext {X Y : CosimplicialObject C} (f g : X ⟶ Y)
    (h : ∀ (n : SimplexCategory), f.app n = g.app n) : f = g :=
  NatTrans.ext (by ext; apply h)

variable (X : CosimplicialObject C)

open Simplicial

/-- Coface maps for a cosimplicial object. -/
/-
**CategoryTheory.CosimplicialObject.** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.C
osimplicialObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Coface maps for a cosimplicial object.
-/
def δ {n} (i : Fin (n + 2)) : X ^⦋n⦌ ⟶ X ^⦋n + 1⦌ :=
  X.map (SimplexCategory.δ i)

/-- Codegeneracy maps for a cosimplicial object. -/
/-
**CategoryTheory.CosimplicialObject.** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.C
osimplicialObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Codegeneracy maps for a cosimplicial object.
-/
def σ {n} (i : Fin (n + 1)) : X ^⦋n + 1⦌ ⟶ X ^⦋n⦌ :=
  X.map (SimplexCategory.σ i)

/-- Isomorphisms from identities in ℕ. -/
/-
**CategoryTheory.CosimplicialObject.eqToIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.CosimplicialObject`。
形式化陈述：eqToIso {n m : Nat} (h : n = m) : X ^⦋n⦌ ≅ X ^⦋m⦌
参数：h : n = m。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Isomorphisms from identities in ℕ.
-/
def eqToIso {n m : ℕ} (h : n = m) : X ^⦋n⦌ ≅ X ^⦋m⦌ :=
  X.mapIso (CategoryTheory.eqToIso (by rw [h]))

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**CategoryTheory.CosimplicialObject.eqToIso_refl** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.CosimplicialObject`。
形式化陈述：eqToIso_refl {n : Nat} (h : n = n) : X.eqToIso h = Iso.refl _
参数：h : n = n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.mapIso_refl`：mapIso_refl (F : C ⥤ D) (X : C) : F.
mapIso (Iso.refl X) = Iso.refl (F.obj X)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem eqToIso_refl {n : ℕ} (h : n = n) : X.eqToIso h = Iso.refl _ := by
  simp [eqToIso]

/-- The generic case of the first cosimplicial identity -/
@[reassoc]
/-
**CategoryTheory.CosimplicialObject.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.C
osimplicialObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The generic case of the first cosimplicial identity
-/
theorem δ_comp_δ {n} {i j : Fin (n + 2)} (H : i ≤ j) :
    X.δ i ≫ X.δ j.succ = X.δ j ≫ X.δ (Fin.castSucc i) := by
  dsimp [δ]
  simp only [← X.map_comp, SimplexCategory.δ_comp_δ H]

@[reassoc]
/-
**CategoryTheory.CosimplicialObject.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.C
osimplicialObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem δ_comp_δ' {n} {i : Fin (n + 2)} {j : Fin (n + 3)} (H : Fin.castSucc i < j) :
    X.δ i ≫ X.δ j =
      X.δ (j.pred H.ne_zero) ≫
        X.δ (Fin.castSucc i) := by
  dsimp [δ]
  simp only [← X.map_comp, SimplexCategory.δ_comp_δ' H]

@[reassoc]
/-
**CategoryTheory.CosimplicialObject.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.C
osimplicialObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem δ_comp_δ'' {n} {i : Fin (n + 3)} {j : Fin (n + 2)} (H : i ≤ Fin.castSucc j) :
    X.δ (i.castLT (Nat.lt_of_le_of_lt (Fin.le_iff_val_le_val.mp H) j.is_lt)) ≫ X.δ j.succ =
      X.δ j ≫ X.δ i := by
  dsimp [δ]
  simp only [← X.map_comp, SimplexCategory.δ_comp_δ'' H]

/-- The special case of the first cosimplicial identity -/
@[reassoc]
/-
**CategoryTheory.CosimplicialObject.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.C
osimplicialObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The special case of the first cosimplicial identity
-/
theorem δ_comp_δ_self {n} {i : Fin (n + 2)} :
    X.δ i ≫ X.δ (Fin.castSucc i) = X.δ i ≫ X.δ i.succ := by
  dsimp [δ]
  simp only [← X.map_comp, SimplexCategory.δ_comp_δ_self]

@[reassoc]
/-
**CategoryTheory.CosimplicialObject.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.C
osimplicialObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem δ_comp_δ_self' {n} {i : Fin (n + 2)} {j : Fin (n + 3)} (H : j = Fin.castSucc i) :
    X.δ i ≫ X.δ j = X.δ i ≫ X.δ i.succ := by
  subst H
  rw [δ_comp_δ_self]

/-- The second cosimplicial identity -/
@[reassoc]
/-
**CategoryTheory.CosimplicialObject.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.C
osimplicialObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The second cosimplicial identity
-/
theorem δ_comp_σ_of_le {n} {i : Fin (n + 2)} {j : Fin (n + 1)} (H : i ≤ Fin.castSucc j) :
    X.δ (Fin.castSucc i) ≫ X.σ j.succ = X.σ j ≫ X.δ i := by
  dsimp [δ, σ]
  simp only [← X.map_comp, SimplexCategory.δ_comp_σ_of_le H]

/-- The first part of the third cosimplicial identity -/
@[reassoc]
/-
**CategoryTheory.CosimplicialObject.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.C
osimplicialObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The first part of the third cosimplicial identity
-/
theorem δ_comp_σ_self {n} {i : Fin (n + 1)} : X.δ (Fin.castSucc i) ≫ X.σ i = 𝟙 _ := by
  dsimp [δ, σ]
  simp only [← X.map_comp, SimplexCategory.δ_comp_σ_self, X.map_id]

@[reassoc]
/-
**CategoryTheory.CosimplicialObject.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.C
osimplicialObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem δ_comp_σ_self' {n} {j : Fin (n + 2)} {i : Fin (n + 1)} (H : j = Fin.castSucc i) :
    X.δ j ≫ X.σ i = 𝟙 _ := by
  subst H
  rw [δ_comp_σ_self]

/-- The second part of the third cosimplicial identity -/
@[reassoc]
/-
**CategoryTheory.CosimplicialObject.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.C
osimplicialObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The second part of the third cosimplicial identity
-/
theorem δ_comp_σ_succ {n} {i : Fin (n + 1)} : X.δ i.succ ≫ X.σ i = 𝟙 _ := by
  dsimp [δ, σ]
  simp only [← X.map_comp, SimplexCategory.δ_comp_σ_succ, X.map_id]

@[reassoc]
/-
**CategoryTheory.CosimplicialObject.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.C
osimplicialObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem δ_comp_σ_succ' {n} {j : Fin (n + 2)} {i : Fin (n + 1)} (H : j = i.succ) :
    X.δ j ≫ X.σ i = 𝟙 _ := by
  subst H
  rw [δ_comp_σ_succ]

/-- The fourth cosimplicial identity -/
@[reassoc]
/-
**CategoryTheory.CosimplicialObject.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.C
osimplicialObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The fourth cosimplicial identity
-/
theorem δ_comp_σ_of_gt {n} {i : Fin (n + 2)} {j : Fin (n + 1)} (H : Fin.castSucc j < i) :
    X.δ i.succ ≫ X.σ (Fin.castSucc j) = X.σ j ≫ X.δ i := by
  dsimp [δ, σ]
  simp only [← X.map_comp, SimplexCategory.δ_comp_σ_of_gt H]

@[reassoc]
/-
**CategoryTheory.CosimplicialObject.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.C
osimplicialObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem δ_comp_σ_of_gt' {n} {i : Fin (n + 3)} {j : Fin (n + 2)} (H : j.succ < i) :
    X.δ i ≫ X.σ j =
      X.σ (j.castLT ((add_lt_add_iff_right 1).mp (lt_of_lt_of_le H i.is_le))) ≫
        X.δ (i.pred H.ne_zero) := by
  dsimp [δ, σ]
  simp only [← X.map_comp, SimplexCategory.δ_comp_σ_of_gt' H]

/-- The fifth cosimplicial identity -/
@[reassoc]
/-
**CategoryTheory.CosimplicialObject.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.C
osimplicialObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The fifth cosimplicial identity
-/
theorem σ_comp_σ {n} {i j : Fin (n + 1)} (H : i ≤ j) :
    X.σ (Fin.castSucc i) ≫ X.σ j = X.σ j.succ ≫ X.σ i := by
  dsimp [δ, σ]
  simp only [← X.map_comp, SimplexCategory.σ_comp_σ H]

@[reassoc (attr := simp)]
/-
**CategoryTheory.CosimplicialObject.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.C
osimplicialObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem δ_naturality {X' X : CosimplicialObject C} (f : X ⟶ X') {n : ℕ} (i : Fin (n + 2)) :
    X.δ i ≫ f.app ⦋n + 1⦌ = f.app ⦋n⦌ ≫ X'.δ i :=
  f.naturality _

@[reassoc (attr := simp)]
/-
**CategoryTheory.CosimplicialObject.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.C
osimplicialObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem σ_naturality {X' X : CosimplicialObject C} (f : X ⟶ X') {n : ℕ} (i : Fin (n + 1)) :
    X.σ i ≫ f.app ⦋n⦌ = f.app ⦋n + 1⦌ ≫ X'.σ i :=
  f.naturality _

variable (C)

/-- Functor composition induces a functor on cosimplicial objects. -/
@[simps!]
/-
**CategoryTheory.CosimplicialObject.whiskering** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.CosimplicialObject`。
形式化陈述：whiskering (D : Type*) [Category* D] : (C ⥤ D) ⥤ CosimplicialObject C ⥤ Co
simplicialObject D
参数：D : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Functor composition induces a functor on cosimplicial objects.
-/
def whiskering (D : Type*) [Category* D] : (C ⥤ D) ⥤ CosimplicialObject C ⥤ CosimplicialObject D :=
  whiskeringRight _ _ _

/-- Truncated cosimplicial objects. -/
/-
**CategoryTheory.CosimplicialObject.Truncated** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.CosimplicialObject`。
形式化陈述：Truncated (n : Nat)
参数：n : Nat。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Truncated cosimplicial objects.
-/
def Truncated (n : ℕ) :=
  SimplexCategory.Truncated n ⥤ C
deriving Category

variable {C}

namespace Truncated

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.CosimplicialObject.Truncated.** 是 Mathlib 中的一个实例，位于命名空间 `Catego
ryTheory.CosimplicialObject.Truncated`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {n} {J : Type v} [SmallCategory J] [HasLimitsOfShape J C] :
    HasLimitsOfShape J (CosimplicialObject.Truncated C n) := by
  dsimp [Truncated]
  infer_instance
/-
**CategoryTheory.CosimplicialObject.Truncated.** 是 Mathlib 中的一个实例，位于命名空间 `Catego
ryTheory.CosimplicialObject.Truncated`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {n} [HasLimits C] : HasLimits (CosimplicialObject.Truncated C n) :=
  ⟨inferInstance⟩

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.CosimplicialObject.Truncated.** 是 Mathlib 中的一个实例，位于命名空间 `Catego
ryTheory.CosimplicialObject.Truncated`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {n} {J : Type v} [SmallCategory J] [HasColimitsOfShape J C] :
    HasColimitsOfShape J (CosimplicialObject.Truncated C n) := by
  dsimp [Truncated]
  infer_instance
/-
**CategoryTheory.CosimplicialObject.Truncated.** 是 Mathlib 中的一个实例，位于命名空间 `Catego
ryTheory.CosimplicialObject.Truncated`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {n} [HasColimits C] : HasColimits (CosimplicialObject.Truncated C n) :=
  ⟨inferInstance⟩

variable (C) in
/-- Functor composition induces a functor on truncated cosimplicial objects. -/
@[simps!]
/-
**CategoryTheory.CosimplicialObject.Truncated.whiskering** 是 Mathlib 中的一个定义，位于命名
空间 `CategoryTheory.CosimplicialObject.Truncated`。
形式化陈述：whiskering {n} (D : Type*) [Category* D] : (C ⥤ D) ⥤ Truncated C n ⥤ Trunc
ated D n
参数：D : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Functor composition induces a functor on truncated cosimplicial objects.
-/
def whiskering {n} (D : Type*) [Category* D] : (C ⥤ D) ⥤ Truncated C n ⥤ Truncated D n :=
  whiskeringRight _ _ _

open Mathlib.Tactic (subscriptTerm) in
/-- For `X : Truncated C n` and `m ≤ n`, `X ^⦋m⦌ₙ` is the `m`-th term of X. The
proof `p : m ≤ n` can also be provided using the syntax `X ^⦋m, p⦌ₙ`. -/
scoped syntax:max (name := mkNotation)
  term " ^⦋" term ("," term)? "⦌" noWs subscriptTerm : term

open scoped SimplexCategory.Truncated in
scoped macro_rules
  | `($X:term ^⦋$m:term⦌$n:subscript) =>
    `(($X : CategoryTheory.CosimplicialObject.Truncated _ $n).obj
      ⟨SimplexCategory.mk $m, by first | get_elem_tactic |
      fail "Failed to prove truncation property. Try writing `X ^⦋m, by ...⦌ₙ`."⟩)
  | `($X:term ^⦋$m:term, $p:term⦌$n:subscript) =>
    `(($X : CategoryTheory.CosimplicialObject.Truncated _ $n).obj
      ⟨SimplexCategory.mk $m, $p⟩)

variable (C) in
/-- Further truncation of truncated cosimplicial objects. -/
/-
**CategoryTheory.CosimplicialObject.Truncated.trunc** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.CosimplicialObject.Truncated`。
形式化陈述：trunc (n m : Nat) (h : m <= n
参数：n m : Nat。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Further truncation of truncated cosimplicial objects.
-/
def trunc (n m : ℕ) (h : m ≤ n := by lia) : Truncated C n ⥤ Truncated C m :=
  (whiskeringLeft _ _ _).obj <| SimplexCategory.Truncated.incl m n

end Truncated

section Truncation

/-- The truncation functor from cosimplicial objects to truncated cosimplicial objects. -/
/-
**CategoryTheory.CosimplicialObject.truncation** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.CosimplicialObject`。
形式化陈述：truncation (n : Nat) : CosimplicialObject C ⥤ CosimplicialObject.Truncated
 C n
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The truncation functor from cosimplicial objects to truncated cosimplicial objec
ts.
-/
def truncation (n : ℕ) : CosimplicialObject C ⥤ CosimplicialObject.Truncated C n :=
  (whiskeringLeft _ _ _).obj (SimplexCategory.Truncated.inclusion n)

/-- For all `m ≤ n`, `truncation m` factors through `Truncated n`. -/
/-
**CategoryTheory.CosimplicialObject.truncationCompTrunc** 是 Mathlib 中的一个定义，位于命名空
间 `CategoryTheory.CosimplicialObject`。
形式化陈述：truncationCompTrunc {n m : Nat} (h : m <= n) : truncation n ⋙ Truncated.tr
unc C n m ≅ truncation m
参数：h : m <= n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For all `m ≤ n`, `truncation m` factors through `Truncated n`.
-/
def truncationCompTrunc {n m : ℕ} (h : m ≤ n) :
    truncation n ⋙ Truncated.trunc C n m ≅ truncation m :=
  Iso.refl _

end Truncation

variable (C)

/-- The constant cosimplicial object. -/
/-
**CategoryTheory.CosimplicialObject.const** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryT
heory.CosimplicialObject`。
形式化陈述：const : C ⥤ CosimplicialObject C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The constant cosimplicial object.
-/
abbrev const : C ⥤ CosimplicialObject C :=
  CategoryTheory.Functor.const _

/-- Augmented cosimplicial objects. -/
/-
**CategoryTheory.CosimplicialObject.Augmented** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.CosimplicialObject`。
形式化陈述：Augmented
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Augmented cosimplicial objects.
-/
def Augmented :=
  Comma (const C) (𝟭 (CosimplicialObject C))

@[simps!]
/-
**CategoryTheory.CosimplicialObject.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.C
osimplicialObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Category (Augmented C) :=
  inferInstanceAs <| Category (Comma _ _)

variable {C}

namespace Augmented

@[ext]
/-
**CategoryTheory.CosimplicialObject.Augmented.hom_ext** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.CosimplicialObject.Augmented`。
形式化陈述：hom_ext {X Y : Augmented C} (f g : X ⟶ Y) (h₁ : f.left = g.left) (h₂ : f.r
ight = g.right) : f = g
参数：f g : X ⟶ Y；h₁ : f.left = g.left；h₂ : f.right = g.right。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Comma.hom_ext`：hom_ext (f g : X ⟶ Y) (h₁ : f.left = g.lef
t) (h₂ : f.right = g.right) : f = g
-/
lemma hom_ext {X Y : Augmented C} (f g : X ⟶ Y) (h₁ : f.left = g.left) (h₂ : f.right = g.right) :
    f = g :=
  Comma.hom_ext _ _ h₁ h₂

/-- Drop the augmentation. -/
@[simps!]
/-
**CategoryTheory.CosimplicialObject.Augmented.drop** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.CosimplicialObject.Augmented`。
形式化陈述：drop : Augmented C ⥤ CosimplicialObject C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Drop the augmentation.
-/
def drop : Augmented C ⥤ CosimplicialObject C :=
  Comma.snd _ _

/-- The point of the augmentation. -/
@[simps!]
/-
**CategoryTheory.CosimplicialObject.Augmented.point** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.CosimplicialObject.Augmented`。
形式化陈述：point : Augmented C ⥤ C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The point of the augmentation.
-/
def point : Augmented C ⥤ C :=
  Comma.fst _ _

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
/-
**CategoryTheory.CosimplicialObject.Augmented.w_app** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.CosimplicialObject.Augmented`。
形式化陈述：w_app {X Y : Augmented C} {η : X ⟶ Y} {n : SimplexCategory} : dsimp% η.lef
t ≫ Y.hom.app n = X.hom.app n ≫ η.right.app n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.congr_app`：congr_app {α β : F ⟶ G} (h : α = β) (
X : C) : α.app X = β.app X
· 使用定理 `CategoryTheory.CommaMorphism.w`：∀ {A : Type u₁} [inst : CategoryTheory.C
ategory.{v₁, u₁} A] {B : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} B] 
  {T : Type u₃} [ins…

--- 原说明 ---
`respectTransparency.types true` changes the auto-generated lemmas' signature
-/
lemma w_app {X Y : Augmented C} {η : X ⟶ Y} {n : SimplexCategory} :
    dsimp% η.left ≫ Y.hom.app n = X.hom.app n ≫ η.right.app n :=
  NatTrans.congr_app η.w n

set_option backward.isDefEq.respectTransparency false in
/-- The functor from augmented objects to arrows. -/
@[simps!]
/-
**CategoryTheory.CosimplicialObject.Augmented.toArrow** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.CosimplicialObject.Augmented`。
形式化陈述：toArrow : Augmented C ⥤ Arrow C where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor from augmented objects to arrows.
-/
def toArrow : Augmented C ⥤ Arrow C where
  obj X :=
    { left := point.obj X
      right := (drop.obj X) ^⦋0⦌
      hom := X.hom.app _ }
  map η :=
    { left := point.map η
      right := (drop.map η).app _
      w := by simp [w_app]}

variable (C)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Functor composition induces a functor on augmented cosimplicial objects. -/
@[simp]
/-
**CategoryTheory.CosimplicialObject.Augmented.whiskeringObj** 是 Mathlib 中的一个定义，位
于命名空间 `CategoryTheory.CosimplicialObject.Augmented`。
形式化陈述：whiskeringObj (D : Type*) [Category* D] (F : C ⥤ D) : Augmented C ⥤ Augmen
ted D where obj X
参数：D : Type*；F : C ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Functor composition induces a functor on augmented cosimplicial objects.
-/
def whiskeringObj (D : Type*) [Category* D] (F : C ⥤ D) : Augmented C ⥤ Augmented D where
  obj X :=
    { left := F.obj (point.obj X)
      right := ((whiskering _ _).obj F).obj (drop.obj X)
      hom := (Functor.constComp _ _ _).inv ≫ whiskerRight X.hom F }
  map η :=
    { left := F.map η.left
      right := whiskerRight η.right _
      w := by
        ext
        dsimp
        rw [Category.id_comp, Category.id_comp, ← F.map_comp, ← F.map_comp]
        simp [w_app, map_comp] }

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Functor composition induces a functor on augmented cosimplicial objects. -/
@[simps]
/-
**CategoryTheory.CosimplicialObject.Augmented.whiskering** 是 Mathlib 中的一个定义，位于命名
空间 `CategoryTheory.CosimplicialObject.Augmented`。
形式化陈述：whiskering (D : Type u') [Category.{v'} D] : (C ⥤ D) ⥤ Augmented C ⥤ Augme
nted D where obj
参数：D : Type u'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Functor composition induces a functor on augmented cosimplicial objects.
-/
def whiskering (D : Type u') [Category.{v'} D] : (C ⥤ D) ⥤ Augmented C ⥤ Augmented D where
  obj := whiskeringObj _ _
  map η :=
    { app := fun A =>
        { left := η.app _
          right := whiskerLeft _ η
          w := by
            ext n
            dsimp
            rw [Category.id_comp, Category.id_comp, η.naturality] }
      naturality := fun _ _ f => by ext <;> simp }

variable {C}

/-- The constant augmented cosimplicial object functor. -/
@[simps]
/-
**CategoryTheory.CosimplicialObject.Augmented.const** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.CosimplicialObject.Augmented`。
形式化陈述：const : C ⥤ Augmented C where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The constant augmented cosimplicial object functor.
-/
def const : C ⥤ Augmented C where
  obj X :=
    { left := X
      right := (CosimplicialObject.const C).obj X
      hom := 𝟙 _ }
  map f :=
    { left := f
      right := (CosimplicialObject.const C).map f }

end Augmented

open Simplicial

set_option backward.defeqAttrib.useBackward true in
/-- Augment a cosimplicial object with an object. -/
@[simps]
/-
**CategoryTheory.CosimplicialObject.augment** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.CosimplicialObject`。
形式化陈述：augment (X : CosimplicialObject C) (X₀ : C) (f : X₀ ⟶ X.obj ⦋0⦌) (w : fora
ll (i : SimplexCategory) (g₁ g₂ : ⦋0⦌ ⟶ i), f ≫ X.map g₁ = f ≫ X.map g₂) : Cosim
plicialObject.Augmented C where left
参数：X : CosimplicialObject C；X₀ : C；f : X₀ ⟶ X.obj ⦋0⦌；w : forall (i : SimplexCat
egory) (g₁ g₂ : ⦋0⦌ ⟶ i), f ≫ X.map g₁ = f ≫ X.map g₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Augment a cosimplicial object with an object.
-/
def augment (X : CosimplicialObject C) (X₀ : C) (f : X₀ ⟶ X.obj ⦋0⦌)
    (w : ∀ (i : SimplexCategory) (g₁ g₂ : ⦋0⦌ ⟶ i),
      f ≫ X.map g₁ = f ≫ X.map g₂) : CosimplicialObject.Augmented C where
  left := X₀
  right := X
  hom :=
    { app := fun _ => f ≫ X.map (SimplexCategory.const _ _ 0)
      naturality := by
        intro i j g
        dsimp
        rw [Category.id_comp, Category.assoc, ← X.map_comp, w] }

-- Not `@[simp]` since `simp` can prove this.
set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.CosimplicialObject.augment_hom_zero** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.CosimplicialObject`。
形式化陈述：augment_hom_zero (X : CosimplicialObject C) (X₀ : C) (f : X₀ ⟶ X.obj ⦋0⦌) 
(w) : (X.augment X₀ f w).hom.app ⦋0⦌ = f
参数：X : CosimplicialObject C；X₀ : C；f : X₀ ⟶ X.obj ⦋0⦌；w。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.CosimplicialObject.augment_hom_app`：∀ {C : Type u} [inst 
: CategoryTheory.Category.{v, u} C] (X : CategoryTheory.CosimplicialObject C) (X
₀ : C)   (f : X₀ ⟶ X.obj { len := 0 }) …
· 使用引理 `SimplexCategory.const_eq_id`：const_eq_id : const ⦋0⦌ ⦋0⦌ 0 = 𝟙 _
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem augment_hom_zero (X : CosimplicialObject C) (X₀ : C) (f : X₀ ⟶ X.obj ⦋0⦌) (w) :
    (X.augment X₀ f w).hom.app ⦋0⦌ = f := by simp

set_option backward.defeqAttrib.useBackward true in
/-- The coaugmented cosimplicial object that is deduced from a cosimplicial object and
an initial object. -/
@[simps!]
/-
**CategoryTheory.CosimplicialObject.augmentOfIsInitial** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.CosimplicialObject`。
形式化陈述：augmentOfIsInitial (X : CosimplicialObject C) {T : C} (hT : IsInitial T) :
 Augmented C where right
参数：X : CosimplicialObject C；hT : IsInitial T。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The coaugmented cosimplicial object that is deduced from a cosimplicial object a
nd
an initial object.
-/
def augmentOfIsInitial (X : CosimplicialObject C) {T : C} (hT : IsInitial T) :
    Augmented C where
  right := X
  left := T
  hom := { app _ := hT.to _ }

end CosimplicialObject

/-- The anti-equivalence between simplicial objects and cosimplicial objects. -/
@[simps!]
/-
**CategoryTheory.simplicialCosimplicialEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory`。
形式化陈述：simplicialCosimplicialEquiv : (SimplicialObject C)ᵒᵖ ≌ CosimplicialObject 
Cᵒᵖ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The anti-equivalence between simplicial objects and cosimplicial objects.
-/
def simplicialCosimplicialEquiv : (SimplicialObject C)ᵒᵖ ≌ CosimplicialObject Cᵒᵖ :=
  Functor.leftOpRightOpEquiv _ _

/-- The anti-equivalence between cosimplicial objects and simplicial objects. -/
@[simps!]
/-
**CategoryTheory.cosimplicialSimplicialEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory`。
形式化陈述：cosimplicialSimplicialEquiv : (CosimplicialObject C)ᵒᵖ ≌ SimplicialObject 
Cᵒᵖ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The anti-equivalence between cosimplicial objects and simplicial objects.
-/
def cosimplicialSimplicialEquiv : (CosimplicialObject C)ᵒᵖ ≌ SimplicialObject Cᵒᵖ :=
  Functor.opUnopEquiv _ _

variable {C}

/-- Construct an augmented cosimplicial object in the opposite
category from an augmented simplicial object. -/
@[simps!]
/-
**CategoryTheory.SimplicialObject.Augmented.rightOp** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.SimplicialObject.Augmented`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     CategoryT
heory.SimplicialObject.Augmented C → CategoryTheory.CosimplicialObject.Augmented
 Cᵒᵖ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct an augmented cosimplicial object in the opposite
category from an augmented simplicial object.
-/
def SimplicialObject.Augmented.rightOp (X : SimplicialObject.Augmented C) :
    CosimplicialObject.Augmented Cᵒᵖ where
  left := Opposite.op X.right
  right := X.left.rightOp
  hom := NatTrans.rightOp X.hom

/-- Construct an augmented simplicial object from an augmented cosimplicial
object in the opposite category. -/
@[simps!]
/-
**CategoryTheory.CosimplicialObject.Augmented.leftOp** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.CosimplicialObject.Augmented`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     CategoryT
heory.CosimplicialObject.Augmented Cᵒᵖ → CategoryTheory.SimplicialObject.Augment
ed C
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct an augmented simplicial object from an augmented cosimplicial
object in the opposite category.
-/
def CosimplicialObject.Augmented.leftOp (X : CosimplicialObject.Augmented Cᵒᵖ) :
    SimplicialObject.Augmented C where
  left := X.right.leftOp
  right := X.left.unop
  hom := NatTrans.leftOp X.hom

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Converting an augmented simplicial object to an augmented cosimplicial
object and back is isomorphic to the given object. -/
@[simps!]
/-
**CategoryTheory.SimplicialObject.Augmented.rightOpLeftOpIso** 是 Mathlib 中的一个定义，
位于命名空间 `CategoryTheory.SimplicialObject.Augmented`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] → (X : Category
Theory.SimplicialObject.Augmented C) → X.rightOp.leftOp ≅ X
参数：X : CategoryTheory.SimplicialObject.Augmented C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Converting an augmented simplicial object to an augmented cosimplicial
object and back is isomorphic to the given object.
-/
def SimplicialObject.Augmented.rightOpLeftOpIso (X : SimplicialObject.Augmented C) :
    X.rightOp.leftOp ≅ X :=
  Comma.isoMk X.left.rightOpLeftOpIso (CategoryTheory.eqToIso <| by simp)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Converting an augmented cosimplicial object to an augmented simplicial
object and back is isomorphic to the given object. -/
@[simps!]
/-
**CategoryTheory.CosimplicialObject.Augmented.leftOpRightOpIso** 是 Mathlib 中的一个定
义，位于命名空间 `CategoryTheory.CosimplicialObject.Augmented`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     (X : Cate
goryTheory.CosimplicialObject.Augmented Cᵒᵖ) → X.leftOp.rightOp ≅ X
参数：X : CategoryTheory.CosimplicialObject.Augmented Cᵒᵖ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Converting an augmented cosimplicial object to an augmented simplicial
object and back is isomorphic to the given object.
-/
def CosimplicialObject.Augmented.leftOpRightOpIso (X : CosimplicialObject.Augmented Cᵒᵖ) :
    X.leftOp.rightOp ≅ X :=
  Comma.isoMk (CategoryTheory.eqToIso <| by simp) X.right.leftOpRightOpIso

variable (C)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A functorial version of `SimplicialObject.Augmented.rightOp`. -/
@[simps]
/-
**CategoryTheory.simplicialToCosimplicialAugmented** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory`。
形式化陈述：simplicialToCosimplicialAugmented : (SimplicialObject.Augmented C)ᵒᵖ ⥤ Cos
implicialObject.Augmented Cᵒᵖ where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functorial version of `SimplicialObject.Augmented.rightOp`.
-/
def simplicialToCosimplicialAugmented :
    (SimplicialObject.Augmented C)ᵒᵖ ⥤ CosimplicialObject.Augmented Cᵒᵖ where
  obj X := X.unop.rightOp
  map f :=
    { left := f.unop.right.op
      right := NatTrans.rightOp f.unop.left
      w := by
        ext x
        dsimp
        simp_rw [← op_comp]
        congr 1
        exact (congr_app f.unop.w (op x)).symm }

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A functorial version of `Cosimplicial_object.Augmented.leftOp`. -/
@[simps]
/-
**CategoryTheory.cosimplicialToSimplicialAugmented** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory`。
形式化陈述：cosimplicialToSimplicialAugmented : CosimplicialObject.Augmented Cᵒᵖ ⥤ (Si
mplicialObject.Augmented C)ᵒᵖ where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functorial version of `Cosimplicial_object.Augmented.leftOp`.
-/
def cosimplicialToSimplicialAugmented :
    CosimplicialObject.Augmented Cᵒᵖ ⥤ (SimplicialObject.Augmented C)ᵒᵖ where
  obj X := Opposite.op X.leftOp
  map f :=
    Quiver.Hom.op <|
      { left := NatTrans.leftOp f.right
        right := f.left.unop
        w := by
          ext x
          dsimp
          simp_rw [← unop_comp]
          congr 1
          exact (congr_app f.w (unop x)).symm }

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The contravariant categorical equivalence between augmented simplicial
objects and augmented cosimplicial objects in the opposite category. -/
@[simps! functor inverse]
/-
**CategoryTheory.simplicialCosimplicialAugmentedEquiv** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory`。
形式化陈述：simplicialCosimplicialAugmentedEquiv : (SimplicialObject.Augmented C)ᵒᵖ ≌ 
CosimplicialObject.Augmented Cᵒᵖ where functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The contravariant categorical equivalence between augmented simplicial
objects and augmented cosimplicial objects in the opposite category.
-/
def simplicialCosimplicialAugmentedEquiv :
    (SimplicialObject.Augmented C)ᵒᵖ ≌ CosimplicialObject.Augmented Cᵒᵖ where
  functor := simplicialToCosimplicialAugmented _
  inverse := cosimplicialToSimplicialAugmented _
  unitIso := NatIso.ofComponents (fun X => X.unop.rightOpLeftOpIso.op) fun f => by
      dsimp
      rw [← f.op_unop]
      simp_rw [← op_comp]
      congr 1
      cat_disch
  counitIso := NatIso.ofComponents fun X => X.leftOpRightOpIso

end CategoryTheory

