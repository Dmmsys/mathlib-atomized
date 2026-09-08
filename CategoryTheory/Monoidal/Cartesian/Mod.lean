/-
Copyright (c) 2025 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau, Christian Merten
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mon
public import Mathlib.CategoryTheory.Monoidal.Mod
public import Mathlib.GroupTheory.GroupAction.Hom

/-!
# Module objects in cartesian monoidal categories

In this file we study module objects in a cartesian monoidal category `C` action on
itself by `⊗`.

In particular, for a monoid object `M : C` action on `X : C`, we equip `Z ⟶ X` with a `M ⟶ X` action
for every `Z : C`.
-/

@[expose] public section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory

namespace CategoryTheory
universe v u
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

open scoped MonObj

attribute [local simp] leftUnitor_hom

/-- Every object is a module over a monoid object via the trivial action. -/
/-
**CategoryTheory.ModObj.trivialAction** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
ModObj`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.CartesianMonoidalCategory C] →       (M : C) → [inst_2 : Categor
yTheory.MonObj M] → (X : C) → CategoryTheory.ModObj M X
参数：M : C；X : C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Every object is a module over a monoid object via the trivial action.
-/
@[reducible] def ModObj.trivialAction (M : C) [MonObj M] (X : C) :
    ModObj M X where
  smul := snd M X

attribute [local instance] ModObj.trivialAction in
/-- Every object is a module over a monoid object via the trivial action. -/
@[simps]
/-
**CategoryTheory.Mod.trivialAction** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Mod
`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.CartesianMonoidalCategory C] → (M : CategoryTheory.Mon C) → C → 
CategoryTheory.Mod C M.X
参数：M : CategoryTheory.Mon C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Every object is a module over a monoid object via the trivial action.
-/
def Mod.trivialAction (M : Mon C) (X : C) : Mod C M.X where
  X := X

@[deprecated (since := "2026-04-21")]
alias Mod_.trivialAction := Mod.trivialAction

variable {M : C} [MonObj M] {X : C} [ModObj M X]

namespace Hom

/-- Morphisms `Y ⟶ M` act on morphisms `Y ⟶ X` via the internal scalar multiplication. -/
@[to_additive (attr := simps! -isSimp)
/-- Morphisms `Y ⟶ M` act on morphisms `Y ⟶ X` via the internal additive action. -/]
/-
**CategoryTheory.Hom.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Hom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (Y : C) : SMul (Y ⟶ M) (Y ⟶ X) where
  smul m x := lift m x ≫ γ[M, X]

/-- If `M` is a monoid object acting on `X`, then morphisms into `M` act on
morphisms into `X`. -/
@[to_additive /-- If `M` is an additive monoid object acting on `X`, then morphisms into `M` act on
morphisms into `X`. -/]
/-
**CategoryTheory.Hom.mulAction** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Hom`。
形式化陈述：mulAction (Z : C) : MulAction (Z ⟶ M) (Z ⟶ X) where one_smul x
参数：Z : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance mulAction (Z : C) : MulAction (Z ⟶ M) (Z ⟶ X) where
  one_smul x := by simp [one_def, smul_def, ← lift_whiskerRight]
  mul_smul m n x := by simp [mul_def, smul_def, ← lift_whiskerRight]

end Hom

variable {Y : C} [ModObj M Y]

/-
**CategoryTheory.ModObj.comp_smul** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.ModO
bj`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.CartesianMonoidalCategory C] {M : C}   [inst_2 : CategoryTheory.MonObj M
] {X : C} [inst_3 : CategoryTheory.ModObj M X] {Z Z' : C} (g : Z' ⟶ Z) (m : Z ⟶ 
M)   (x : Z ⟶ X),   CategoryTheory.CategoryStruct.comp g (m • x) =     CategoryT
heory.CategoryStruct.comp g m • CategoryTheory.CategoryStruct.comp g x
参数：g : Z' ⟶ Z；m : Z ⟶ M；x : Z ⟶ X；m • x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Hom.smul_def`：∀ {C : Type u} [inst : CategoryTheory.Categ
ory.{v, u} C] [inst_1 : CategoryTheory.CartesianMonoidalCategory C] {M : C}   [i
nst_2 : CategoryT…
· 使用定理 `CategoryTheory.CartesianMonoidalCategory.comp_lift_assoc`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.CartesianMon
oidalCategory C]   {V W X Y : C} (f : V ⟶ W) (…
-/
lemma ModObj.comp_smul {Z Z' : C} (g : Z' ⟶ Z) (m : Z ⟶ M) (x : Z ⟶ X) :
    g ≫ (m • x) = (g ≫ m) • (g ≫ x) := by
  rw [Hom.smul_def, Hom.smul_def, comp_lift_assoc]

@[to_additive (attr := reassoc (attr := simp))]
/-
**CategoryTheory.IsModHom.map_smul** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.IsM
odHom`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.CartesianMonoidalCategory C] {M : C}   [inst_2 : CategoryTheory.MonObj M
] {X : C} [inst_3 : CategoryTheory.ModObj M X] {Y : C}   [inst_4 : CategoryTheor
y.ModObj M Y] (f : X ⟶ Y) [CategoryTheory.IsModHom M f] {Z : C} (m : Z ⟶ M) (x :
 Z ⟶ X),   CategoryTheory.CategoryStruct.comp (m • x) f = m • CategoryTheory.Cat
egoryStruct.comp x f
参数：f : X ⟶ Y；m : Z ⟶ M；x : Z ⟶ X；m • x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.IsModHom.smul_hom`：∀ {C : Type u₁} {inst : CategoryTheory
.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} {D : Type u₂}
   {inst_2 : CategoryT…
· 使用定理 `CategoryTheory.CartesianMonoidalCategory.lift_whiskerLeft_assoc`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Carte
sianMonoidalCategory C]   {X Y Z W : C} (f : X ⟶ Y) (…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma IsModHom.map_smul (f : X ⟶ Y) [IsModHom M f] {Z : C} (m : Z ⟶ M) (x : Z ⟶ X) :
    (m • x) ≫ f = m • x ≫ f := by
  simp [Hom.smul_def, Category.assoc, IsModHom.smul_hom]

/-- An `M`-equivariant morphism induces an equivariant function on hom types. -/
@[to_additive (attr := simps)
/-- A `φ`-equivariant morphism induces an equivariant morphism on hom types. -/]
/-
**CategoryTheory.IsModHom.mulActionHom** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.IsModHom`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.CartesianMonoidalCategory C] →       {M : C} →         [inst_2 :
 CategoryTheory.MonObj M] →           {X : C} →             [inst_3 : CategoryTh
eory.ModObj M X] →               {Y : C} →                 [inst_4 : CategoryThe
ory.ModObj M Y] →                   (f : X ⟶ Y) → [CategoryTheory.IsModHom M f] 
→ (Z : C) → (Z ⟶ X) →ₑ[id] Z ⟶ Y
参数：f : X ⟶ Y；Z : C；Z ⟶ X。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsModHom.map_smul`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] [inst_1 : CategoryTheory.CartesianMonoidalCategory C] {M : C}
   [inst_2 : CategoryT…
-/
def IsModHom.mulActionHom (f : X ⟶ Y) [IsModHom M f] (Z : C) :
    MulActionHom (id (α := Z ⟶ M)) (Z ⟶ X) (Z ⟶ Y) where
  toFun := (· ≫ f)
  map_smul' := map_smul f

namespace ModObj

variable (M X) in
/-- The morphism `(m, x) ↦ (m • x, x)`. -/
/-
**CategoryTheory.ModObj.leftSMul** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.ModOb
j`。
形式化陈述：leftSMul : M otimes X ⟶ X otimes X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism `(m, x) ↦ (m • x, x)`.
-/
def leftSMul : M ⊗ X ⟶ X ⊗ X :=
  lift γ[M, X] (snd _ _)

@[reassoc (attr := simp)]
/-
**CategoryTheory.ModObj.leftSMul_fst** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.M
odObj`。
形式化陈述：leftSMul_fst : leftSMul M X ≫ fst _ _ = γ[M, X]
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.lift_fst`：lift_fst {T X Y : C} 
(f : T ⟶ X) (g : T ⟶ Y) : lift f g ≫ fst _ _ = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma leftSMul_fst : leftSMul M X ≫ fst _ _ = γ[M, X] := by
  simp [leftSMul]

@[reassoc (attr := simp)]
/-
**CategoryTheory.ModObj.leftSMul_snd** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.M
odObj`。
形式化陈述：leftSMul_snd : leftSMul M X ≫ snd _ _ = snd _ _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.lift_snd`：lift_snd {T X Y : C} 
(f : T ⟶ X) (g : T ⟶ Y) : lift f g ≫ snd _ _ = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma leftSMul_snd : leftSMul M X ≫ snd _ _ = snd _ _ := by
  simp [leftSMul]

@[reassoc]
/-
**CategoryTheory.ModObj.lift_leftSMul** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.
ModObj`。
形式化陈述：lift_leftSMul (Z : C) (x : Z ⟶ X) (m : Z ⟶ M) : lift m x ≫ leftSMul M X = 
lift (m • x) x
参数：Z : C；x : Z ⟶ X；m : Z ⟶ M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.hom_ext`：hom_ext {T X Y : C} (f
 g : T ⟶ X otimes Y) (h_fst : f ≫ fst _ _ = g ≫ fst _ _) (h_snd : f ≫ snd _ _ = 
g ≫ snd _ _) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `CategoryTheory.ModObj.leftSMul_fst`：leftSMul_fst : leftSMul M X ≫ fst _ 
_ = γ[M, X]
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.lift_fst`：lift_fst {T X Y : C} 
(f : T ⟶ X) (g : T ⟶ Y) : lift f g ≫ fst _ _ = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CategoryTheory.ModObj.leftSMul_snd`：leftSMul_snd : leftSMul M X ≫ snd _ 
_ = snd _ _
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.lift_snd`：lift_snd {T X Y : C} 
(f : T ⟶ X) (g : T ⟶ Y) : lift f g ≫ snd _ _ = g
-/
lemma lift_leftSMul (Z : C) (x : Z ⟶ X) (m : Z ⟶ M) : lift m x ≫ leftSMul M X = lift (m • x) x := by
  ext <;> simp [Hom.smul_def]
/-
**CategoryTheory.ModObj.lift_leftSMul_eq_lift_iff** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.ModObj`。
形式化陈述：lift_leftSMul_eq_lift_iff (Z : C) (x y : Z ⟶ X) (m : Z ⟶ M) : lift m x ≫ l
eftSMul M X = lift y x ↔ m • x = y
参数：Z : C；x y : Z ⟶ X；m : Z ⟶ M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.comp_lift`：comp_lift {V W X Y :
 C} (f : V ⟶ W) (g : W ⟶ X) (h : W ⟶ Y) : f ≫ lift g h = lift (f ≫ g) (f ≫ h)
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.lift_snd`：lift_snd {T X Y : C} 
(f : T ⟶ X) (g : T ⟶ Y) : lift f g ≫ snd _ _ = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.lift_fst`：lift_fst {T X Y : C} 
(f : T ⟶ X) (g : T ⟶ Y) : lift f g ≫ fst _ _ = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma lift_leftSMul_eq_lift_iff (Z : C) (x y : Z ⟶ X) (m : Z ⟶ M) :
    lift m x ≫ leftSMul M X = lift y x ↔ m • x = y := by
  simp [Hom.smul_def, leftSMul, CartesianMonoidalCategory.hom_ext_iff]

open CartesianMonoidalCategory in
/-- The morphism `(m, x) ↦ (m • x, x)` is an isomorphism if and only if the induced
action is pointwise simply transitive. -/
/-
**CategoryTheory.ModObj.isIso_leftSMul_iff** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTh
eory.ModObj`。
形式化陈述：isIso_leftSMul_iff : IsIso (leftSMul M X) ↔ forall (Z : C) (x y : Z ⟶ X), 
exists! (m : Z ⟶ M), m • x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.hom_ext`：hom_ext {T X Y : C} (f
 g : T ⟶ X otimes Y) (h_fst : f ≫ fst _ _ = g ≫ fst _ _) (h_snd : f ≫ snd _ _ = 
g ≫ snd _ _) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `CategoryTheory.ModObj.leftSMul_fst`：leftSMul_fst : leftSMul M X ≫ fst _ 
_ = γ[M, X]
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.lift_fst`：lift_fst {T X Y : C} 
(f : T ⟶ X) (g : T ⟶ Y) : lift f g ≫ fst _ _ = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CategoryTheory.ModObj.leftSMul_snd`：leftSMul_snd : leftSMul M X ≫ snd _ 
_ = snd _ _
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.lift_snd`：lift_snd {T X Y : C} 
(f : T ⟶ X) (g : T ⟶ Y) : lift f g ≫ snd _ _ = g
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用引理 `CategoryTheory.isIso_iff_yoneda_map_bijective`：isIso_iff_yoneda_map_bije
ctive {X Y : C} (f : X ⟶ Y) : IsIso f ↔ (forall (T : C), Function.Bijective (fun
 (x : T ⟶ X) => x ≫ f))
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `pi_congr`：∀ {α : Sort u} {β β' : α → Sort v}, (∀ (a : α), β a = β' a) → 
((a : α) → β a) = ((a : α) → β' a)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Bijective.of_comp_iff`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sor
t u_3} (f : α → β) {g : γ → α},   Function.Bijective g → (Function.Bijective (f 
∘ g) ↔ Function.Bije…
· 使用定理 `Equiv.bijective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Bijec
tive ⇑e
· 使用定理 `Function.bijective_iff_existsUnique`：bijective_iff_existsUnique (f : α -
> β) : Bijective f ↔ forall b : β, exists! a : α, f a = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.CartesianMonoidalCategory.liftEquiv_apply`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.CartesianMon
oidalCategory C]   {T X Y : C} (f : (T ⟶ X) × …
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b
· 使用定理 `Equiv.existsUnique_subtype_congr`：∀ {α : Sort u} {β : Sort v} {p : α → P
rop} {q : β → Prop} (e : { a // p a } ≃ { b // q b }), (∃! a, p a) ↔ ∃! b, q b
· 使用定理 `Subtype.coe_eta`：coe_eta (a : { a // p a }) (h : p a) : mk (↑a) h = a

--- 原说明 ---
The morphism `(m, x) ↦ (m • x, x)` is an isomorphism if and only if the induced
action is pointwise simply transitive.
-/
lemma isIso_leftSMul_iff :
    IsIso (leftSMul M X) ↔ ∀ (Z : C) (x y : Z ⟶ X), ∃! (m : Z ⟶ M), m • x = y := by
  have H (Z : C) (x : Z ⟶ X) (m : Z ⟶ M) :
      lift m x ≫ leftSMul M X = lift (m • x) x := by
    ext <;> simp [Hom.smul_def]
  have h (Z : C) (f g : Z ⟶ X) (m : Z ⟶ M) (x : Z ⟶ X) :
      lift m x ≫ leftSMul M X = lift f g ↔ x = g ∧ m • x = f := by
    simp [← lift_leftSMul_eq_lift_iff, CartesianMonoidalCategory.hom_ext_iff]
    grind
  rw [isIso_iff_yoneda_map_bijective]
  congr! with Z
  rw [← Function.Bijective.of_comp_iff _ liftEquiv.bijective, Function.bijective_iff_existsUnique]
  simp only [liftEquiv.surjective.forall, liftEquiv_apply, Prod.forall, Function.comp_apply, h]
  rw [forall_comm]
  congr! 2 with f g
  exact Equiv.existsUnique_subtype_congr ⟨fun a ↦ ⟨a.val.fst, by grind⟩,
    fun a ↦ ⟨⟨a.val, f⟩, by grind⟩, by cat_disch, by cat_disch⟩

end ModObj

end CategoryTheory

