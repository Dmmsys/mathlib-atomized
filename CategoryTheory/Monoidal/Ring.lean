/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.Algebra.Ring.Basic

/-!
# Ring objects in cartesian monoidal categories

If `C` is a cartesian monoidal category and `X : C`, we introduce a typeclass `RingObj X`
which says that `X` is a ring object: it has a commutative additive group structure and
a multiplicative monoid structure that is distributive over the additive structure.
We also introduce a typeclass `CommRingObj X` which further requires that the multiplicative
law is commutative.

The categories of bundled ring objects and bundled commutative ring objects are
denoted `RingObjCat C` and `CommRingObjCat C` respectively.

## TODO
* develop the theory of bimonoidal categories and relate this with `Rig`-objects

-/

@[expose] public section

universe v u

namespace CategoryTheory

open MonoidalCategory CartesianMonoidalCategory

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

open scoped MonObj AddMonObj

/-
**CategoryTheory.mul_add_iff** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory`。
形式化陈述：mul_add_iff (R : C) [MonObj R] [AddMonObj R] : R ◁ σ ≫ μ = lift ((R ◁ fst 
_ _) ≫ μ) ((R ◁ snd _ _) ≫ μ) ≫ σ ↔ forall ⦃X : C⦄ (a b c : X ⟶ R), a * (b + c) 
= a * b + a * c
参数：R : C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.whisker_eq`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {X Y Z : C} {f g : Y ⟶ X} (h : Z ⟶ Y),   f = g → CategoryTheory.Cate
goryStruct.comp…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.CartesianMonoidalCategory.lift_whiskerLeft_assoc`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Carte
sianMonoidalCategory C]   {X Y Z W : C} (f : X ⟶ Y) (…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.comp_lift`：comp_lift {V W X Y :
 C} (f : V ⟶ W) (g : W ⟶ X) (h : W ⟶ Y) : f ≫ lift g h = lift (f ≫ g) (f ≫ h)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.lift_fst`：lift_fst {T X Y : C} 
(f : T ⟶ X) (g : T ⟶ Y) : lift f g ≫ fst _ _ = f
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.lift_snd`：lift_snd {T X Y : C} 
(f : T ⟶ X) (g : T ⟶ Y) : lift f g ≫ snd _ _ = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.lift_comp_fst_snd`：lift_comp_fs
t_snd {X Y Z : C} (f : X ⟶ Y otimes Z) : lift (f ≫ fst _ _) (f ≫ snd _ _) = f
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.hom_ext`：hom_ext {T X Y : C} (f
 g : T ⟶ X otimes Y) (h_fst : f ≫ fst _ _ = g ≫ fst _ _) (h_snd : f ≫ snd _ _ = 
g ≫ snd _ _) : f = g
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.whiskerLeft_fst`：whiskerLeft_fs
t (X : C) {Y Z : C} (f : Y ⟶ Z) : X ◁ f ≫ fst _ _ = fst _ _
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.whiskerLeft_snd`：whiskerLeft_sn
d (X : C) {Y Z : C} (f : Y ⟶ Z) : X ◁ f ≫ snd _ _ = snd _ _ ≫ f
-/
lemma mul_add_iff (R : C) [MonObj R] [AddMonObj R] :
    R ◁ σ ≫ μ = lift ((R ◁ fst _ _) ≫ μ) ((R ◁ snd _ _) ≫ μ) ≫ σ ↔
      ∀ ⦃X : C⦄ (a b c : X ⟶ R), a * (b + c) = a * b + a * c := by
  refine ⟨fun h _ a b c ↦ ?_, fun h ↦ ?_⟩
  · have := lift a (lift b c) ≫= h
    simp only [lift_whiskerLeft_assoc] at this
    simp only [Hom.add_def, Hom.mul_def, this, ← Category.assoc]
    cat_disch
  · replace h := h (fst R (R ⊗ R)) (snd _ _ ≫ fst _ _) (snd _ _ ≫ snd _ _)
    simp only [Hom.mul_def, Hom.add_def] at h
    convert! h using 2
    · cat_disch
    · ext
      · simp only [lift_fst]
        congr 1
        cat_disch
      · simp only [lift_snd]
        congr 1
        cat_disch
/-
**CategoryTheory.add_mul_iff** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory`。
形式化陈述：add_mul_iff (R : C) [MonObj R] [AddMonObj R] : σ ▷ R ≫ μ = lift (fst _ _ ▷
 _ ≫ μ) (snd _ _ ▷ _ ≫ μ) ≫ σ ↔ forall ⦃X : C⦄ (a b c : X ⟶ R), (a + b) * c = a 
* c + b * c
参数：R : C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.whisker_eq`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {X Y Z : C} {f g : Y ⟶ X} (h : Z ⟶ Y),   f = g → CategoryTheory.Cate
goryStruct.comp…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.CartesianMonoidalCategory.lift_whiskerRight_assoc`：∀ {C :
 Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Cart
esianMonoidalCategory C]   {X Y Z W : C} (f : X ⟶ Y) (…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.comp_lift`：comp_lift {V W X Y :
 C} (f : V ⟶ W) (g : W ⟶ X) (h : W ⟶ Y) : f ≫ lift g h = lift (f ≫ g) (f ≫ h)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.lift_fst`：lift_fst {T X Y : C} 
(f : T ⟶ X) (g : T ⟶ Y) : lift f g ≫ fst _ _ = f
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.lift_snd`：lift_snd {T X Y : C} 
(f : T ⟶ X) (g : T ⟶ Y) : lift f g ≫ snd _ _ = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.lift_comp_fst_snd`：lift_comp_fs
t_snd {X Y Z : C} (f : X ⟶ Y otimes Z) : lift (f ≫ fst _ _) (f ≫ snd _ _) = f
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.hom_ext`：hom_ext {T X Y : C} (f
 g : T ⟶ X otimes Y) (h_fst : f ≫ fst _ _ = g ≫ fst _ _) (h_snd : f ≫ snd _ _ = 
g ≫ snd _ _) : f = g
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.whiskerRight_fst`：whiskerRight_
fst {X Y : C} (f : X ⟶ Y) (Z : C) : f ▷ Z ≫ fst _ _ = fst _ _ ≫ f
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.whiskerRight_snd`：whiskerRight_
snd {X Y : C} (f : X ⟶ Y) (Z : C) : f ▷ Z ≫ snd _ _ = snd _ _
-/
lemma add_mul_iff (R : C) [MonObj R] [AddMonObj R] :
    σ ▷ R ≫ μ = lift (fst _ _ ▷ _ ≫ μ) (snd _ _ ▷ _ ≫ μ) ≫ σ ↔
      ∀ ⦃X : C⦄ (a b c : X ⟶ R), (a + b) * c = a * c + b * c := by
  refine ⟨fun h _ a b c ↦ ?_, fun h ↦ ?_⟩
  · have := lift (lift a b) c ≫= h
    simp only [lift_whiskerRight_assoc] at this
    simp only [Hom.add_def, Hom.mul_def, this, ← Category.assoc]
    cat_disch
  · replace h := h (fst (R ⊗ R) R ≫ fst _ _) (fst _ _ ≫ snd _ _) (snd _ _)
    simp only [Hom.mul_def, Hom.add_def] at h
    convert! h using 2
    · cat_disch
    · ext
      · simp only [lift_fst]
        congr 1
        cat_disch
      · simp only [lift_snd]
        congr 1
        cat_disch

variable [BraidedCategory C]

/-- A ring object in a cartesian monoidal category is an object that is equipped
with an additive group structure and a (multiplicative) monoid structure that
is left and right distributive over the additive structure. -/
/-
**CategoryTheory.RingObj** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.CartesianMonoidalCategory C] → [CategoryTheory.BraidedCategory C
] → C → Type v
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A ring object in a cartesian monoidal category is an object that is equipped
with an additive group structure and a (multiplicative) monoid structure that
is left and right distributive over the additive structure.
-/
class RingObj (R : C) extends AddGrpObj R, IsCommAddMonObj R, MonObj R where
  mul_add (R) : R ◁ σ ≫ μ = lift ((R ◁ fst _ _) ≫ μ) ((R ◁ snd _ _) ≫ μ) ≫ σ
  add_mul (R) : σ ▷ R ≫ μ = lift (fst _ _ ▷ _ ≫ μ) (snd _ _ ▷ _ ≫ μ) ≫ σ

section

variable {R : C} [RingObj R] {X : C}

/-
**CategoryTheory.Hom.mul_add** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Hom`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.CartesianMonoidalCategory C]   [inst_2 : CategoryTheory.BraidedCategory 
C] {R : C} [inst_3 : CategoryTheory.RingObj R] {X : C} (a b c : X ⟶ R),   a * (b
 + c) = a * b + a * c
参数：a b c : X ⟶ R；b + c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.RingObj.toIsCommAddMonObj`：∀ {C : Type u} {inst : Categor
yTheory.Category.{v, u} C} {inst_1 : CategoryTheory.CartesianMonoidalCategory C}
   {inst_2 : CategoryTheory.Br…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.mul_add_iff`：mul_add_iff (R : C) [MonObj R] [AddMonObj R]
 : R ◁ σ ≫ μ = lift ((R ◁ fst _ _) ≫ μ) ((R ◁ snd _ _) ≫ μ) ≫ σ ↔ forall ⦃X : C⦄
 (a b c : X ⟶ R)…
· 使用定理 `CategoryTheory.RingObj.mul_add`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {inst_1 : CategoryTheory.CartesianMonoidalCategory C}   {inst_2
 : CategoryTheory.Br…
-/
lemma Hom.mul_add (a b c : X ⟶ R) : a * (b + c) = a * b + a * c := by
  revert X a b c
  rw [← mul_add_iff, RingObj.mul_add R]
/-
**CategoryTheory.Hom.add_mul** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Hom`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.CartesianMonoidalCategory C]   [inst_2 : CategoryTheory.BraidedCategory 
C] {R : C} [inst_3 : CategoryTheory.RingObj R] {X : C} (a b c : X ⟶ R),   (a + b
) * c = a * c + b * c
参数：a b c : X ⟶ R；a + b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.RingObj.toIsCommAddMonObj`：∀ {C : Type u} {inst : Categor
yTheory.Category.{v, u} C} {inst_1 : CategoryTheory.CartesianMonoidalCategory C}
   {inst_2 : CategoryTheory.Br…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.add_mul_iff`：add_mul_iff (R : C) [MonObj R] [AddMonObj R]
 : σ ▷ R ≫ μ = lift (fst _ _ ▷ _ ≫ μ) (snd _ _ ▷ _ ≫ μ) ≫ σ ↔ forall ⦃X : C⦄ (a 
b c : X ⟶ R), (a…
· 使用定理 `CategoryTheory.RingObj.add_mul`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {inst_1 : CategoryTheory.CartesianMonoidalCategory C}   {inst_2
 : CategoryTheory.Br…
-/
lemma Hom.add_mul (a b c : X ⟶ R) : (a + b) * c = a * c + b * c := by
  revert X a b c
  rw [← add_mul_iff, RingObj.add_mul R]

/-- If `G` is a ring object, then `Hom(X, G)` has a ring structure. -/
/-
**CategoryTheory.Hom.ring** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Hom`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.CartesianMonoidalCategory C] →       [inst_2 : CategoryTheory.Br
aidedCategory C] → {R : C} → [CategoryTheory.RingObj R] → {X : C} → Ring (X ⟶ R)
参数：X ⟶ R。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.RingObj.toIsCommAddMonObj`：∀ {C : Type u} {inst : Categor
yTheory.Category.{v, u} C} {inst_1 : CategoryTheory.CartesianMonoidalCategory C}
   {inst_2 : CategoryTheory.Br…
· 使用定理 `CategoryTheory.Hom.mul_add`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] [inst_1 : CategoryTheory.CartesianMonoidalCategory C]   [inst_2 : C
ategoryTheory.Br…
· 使用定理 `CategoryTheory.Hom.add_mul`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] [inst_1 : CategoryTheory.CartesianMonoidalCategory C]   [inst_2 : C
ategoryTheory.Br…

--- 原说明 ---
If `G` is a ring object, then `Hom(X, G)` has a ring structure.
-/
abbrev Hom.ring {X : C} : Ring (X ⟶ R) where
  left_distrib := Hom.mul_add
  right_distrib := Hom.add_mul
  mul_zero a := by simpa using mul_add a 0 0
  zero_mul a := by simpa using add_mul 0 0 a

scoped[CategoryTheory.RingObj] attribute [instance] Hom.ring

end

open scoped RingObj

/-- A commutative ring object in a cartesian monoidal category is a
ring object such that the multiplicative law is commutative. -/
/-
**CategoryTheory.CommRingObj** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.CartesianMonoidalCategory C] → [CategoryTheory.BraidedCategory C
] → C → Type v
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A commutative ring object in a cartesian monoidal category is a
ring object such that the multiplicative law is commutative.
-/
class CommRingObj (R : C) extends RingObj R, IsCommMonObj R where

/-- If `G` is a commutative ring object, then `Hom(X, G)` has a commutative ring structure. -/
/-
**CategoryTheory.Hom.commRing** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Hom`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.CartesianMonoidalCategory C] →       [inst_2 : CategoryTheory.Br
aidedCategory C] → {R X : C} → [CategoryTheory.CommRingObj R] → CommRing (X ⟶ R)
参数：X ⟶ R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `G` is a commutative ring object, then `Hom(X, G)` has a commutative ring str
ucture.
-/
abbrev Hom.commRing {R : C} {X : C} [CommRingObj R] : CommRing (X ⟶ R) where

scoped[CategoryTheory.CommRingObj] attribute [instance] Hom.commRing

/-- The property that a morphism between ring objects is a ring morphism. -/
/-
**CategoryTheory.IsRingHom** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.CartesianMonoidalCategory C] →       {R₁ R₂ : C} →         [Cate
goryTheory.AddMonObj R₁] →           [CategoryTheory.AddMonObj R₂] → [CategoryTh
eory.MonObj R₁] → [CategoryTheory.MonObj R₂] → (R₁ ⟶ R₂) → Prop
参数：R₁ ⟶ R₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The property that a morphism between ring objects is a ring morphism.
-/
class IsRingHom {R₁ R₂ : C} [AddMonObj R₁] [AddMonObj R₂] [MonObj R₁] [MonObj R₂] (f : R₁ ⟶ R₂)
  extends IsAddMonHom f, IsMonHom f
/-
**CategoryTheory.IsRingHom.id** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.IsRingHo
m`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.CartesianMonoidalCategory C] (R : C)   [inst_2 : CategoryTheory.AddMonOb
j R] [inst_3 : CategoryTheory.MonObj R],   CategoryTheory.IsRingHom (CategoryThe
ory.CategoryStruct.id R)
参数：R : C；CategoryTheory.CategoryStruct.id R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.AddMonObj.instIsAddMonHomId`：∀ {C : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.MonoidalCategory C] {X 
: C}   [inst_2 : CategoryTheory.…
· 使用定理 `CategoryTheory.MonObj.instIsMonHomId`：∀ {C : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.MonoidalCategory C] {X : C}  
 [inst_2 : CategoryTheory.…
-/
instance IsRingHom.id (R : C) [AddMonObj R] [MonObj R] : IsRingHom (𝟙 R) where
/-
**CategoryTheory.IsRingHom.comp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.IsRing
Hom`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.CartesianMonoidalCategory C]   {R₁ R₂ R₃ : C} [inst_2 : CategoryTheory.A
ddMonObj R₁] [inst_3 : CategoryTheory.AddMonObj R₂]   [inst_4 : CategoryTheory.A
ddMonObj R₃] [inst_5 : CategoryTheory.MonObj R₁] [inst_6 : CategoryTheory.MonObj
 R₂]   [inst_7 : CategoryTheory.MonObj R₃] (f : R₁ ⟶ R₂) (g : R₂ ⟶ R₃) [Category
Theory.IsRingHom f]   [CategoryTheory.IsRingHom g], CategoryTheory.IsRingHom (Ca
tegoryTheory.CategoryStruct.comp f g)
参数：f : R₁ ⟶ R₂；g : R₂ ⟶ R₃；CategoryTheory.CategoryStruct.comp f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.instIsAddMonHomComp`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.MonoidalCategory C] {M N O : C}
   [inst_2 : CategoryThe…
· 使用定理 `CategoryTheory.IsRingHom.toIsAddMonHom`：∀ {C : Type u} {inst : CategoryT
heory.Category.{v, u} C} {inst_1 : CategoryTheory.CartesianMonoidalCategory C}  
 {R₁ R₂ : C} {inst_2 : Categ…
· 使用定理 `CategoryTheory.instIsMonHomComp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] [inst_1 : CategoryTheory.MonoidalCategory C] {M N O : C}   
[inst_2 : CategoryThe…
· 使用定理 `CategoryTheory.IsRingHom.toIsMonHom`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} {inst_1 : CategoryTheory.CartesianMonoidalCategory C}   {R
₁ R₂ : C} {inst_2 : Categ…
-/
instance IsRingHom.comp {R₁ R₂ R₃ : C}
    [AddMonObj R₁] [AddMonObj R₂] [AddMonObj R₃]
    [MonObj R₁] [MonObj R₂] [MonObj R₃]
    (f : R₁ ⟶ R₂) (g : R₂ ⟶ R₃) [IsRingHom f] [IsRingHom g] :
    IsRingHom (f ≫ g) where

variable (C) in
/-- The category of ring objects in a cartesian monoidal category. -/
/-
**CategoryTheory.RingObjCat** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`。
形式化陈述：(C : Type u) →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.CartesianMonoidalCategory C] → [CategoryTheory.BraidedCategory C
] → Type (max u v)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of ring objects in a cartesian monoidal category.
-/
structure RingObjCat where
  /-- The underlying object in the ambient monoidal category -/
  X : C
  [ringObj : RingObj X]

initialize_simps_projections RingObjCat (-ringObj)

namespace RingObjCat

attribute [instance] ringObj

/-- A morphism of ring objects. -/
@[ext]
/-
**CategoryTheory.RingObjCat.Hom** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory.Ring
ObjCat`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.CartesianMonoidalCategory C] →       [inst_2 : CategoryTheory.Br
aidedCategory C] → CategoryTheory.RingObjCat C → CategoryTheory.RingObjCat C → T
ype v
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism of ring objects.
-/
structure Hom (R₁ R₂ : RingObjCat C) where
  /-- The underlying morphism -/
  hom : R₁.X ⟶ R₂.X
  [isRingHom : IsRingHom hom]

attribute [instance] Hom.isRingHom

@[simps]
/-
**CategoryTheory.RingObjCat.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.RingObjCa
t`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Category (RingObjCat C) where
  Hom R₁ R₂ := Hom R₁ R₂
  id X := { hom := 𝟙 _ }
  comp f g := { hom := f.hom ≫ g.hom }

@[ext]
/-
**CategoryTheory.RingObjCat.hom_ext** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Ri
ngObjCat`。
形式化陈述：hom_ext {R₁ R₂ : RingObjCat C} {f g : R₁ ⟶ R₂} (h : f.hom = g.hom) : f = g
参数：h : f.hom = g.hom。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.RingObjCat.Hom.ext`：∀ {C : Type u} {inst : CategoryTheory
.Category.{v, u} C} {inst_1 : CategoryTheory.CartesianMonoidalCategory C}   {ins
t_2 : CategoryTheory.Br…
-/
lemma hom_ext {R₁ R₂ : RingObjCat C} {f g : R₁ ⟶ R₂} (h : f.hom = g.hom) : f = g :=
  Hom.ext h

variable (C) in
/-- The forgetful functor from the category of ring objects in `C` to `C`. -/
@[simps]
/-
**CategoryTheory.RingObjCat.forget** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Rin
gObjCat`。
形式化陈述：forget : RingObjCat C ⥤ C where obj R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful functor from the category of ring objects in `C` to `C`.
-/
def forget : RingObjCat C ⥤ C where
  obj R := R.X
  map f := f.hom
/-
**CategoryTheory.RingObjCat.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.RingObjCa
t`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (forget C).Faithful where

variable (C) in
/-- The forgetful functor from the category of ring objects in `C`
to the category of monoid objects in `C`. -/
@[simps]
/-
**CategoryTheory.RingObjCat.forget** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Rin
gObjCat`。
形式化陈述：forget : RingObjCat C ⥤ C where obj R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful functor from the category of ring objects in `C`
to the category of monoid objects in `C`.
-/
def forget₂Mon : RingObjCat C ⥤ Mon C where
  obj R := .mk R.X
  map f := .mk f.hom

variable (C) in
/-- The forgetful functor from the category of ring objects in `C`
to the category of additive monoid objects in `C`. -/
@[simps]
/-
**CategoryTheory.RingObjCat.forget** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Rin
gObjCat`。
形式化陈述：forget : RingObjCat C ⥤ C where obj R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful functor from the category of ring objects in `C`
to the category of additive monoid objects in `C`.
-/
def forget₂AddMon : RingObjCat C ⥤ AddMon C where
  obj R := .mk R.X
  map f := .mk f.hom

end RingObjCat

variable (C) in
/-- The category of commutative ring objects in a cartesian monoidal category. -/
/-
**CategoryTheory.CommRingObjCat** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`。
形式化陈述：(C : Type u) →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.CartesianMonoidalCategory C] → [CategoryTheory.BraidedCategory C
] → Type (max u v)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of commutative ring objects in a cartesian monoidal category.
-/
structure CommRingObjCat where
  /-- The underlying object in the ambient monoidal category -/
  X : C
  [commRingObj : CommRingObj X]

initialize_simps_projections CommRingObjCat (-commRingObj)

namespace CommRingObjCat

attribute [instance] commRingObj

/-- A morphism of commutative ring objects. -/
@[ext]
/-
**CategoryTheory.CommRingObjCat.Hom** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory.
CommRingObjCat`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.CartesianMonoidalCategory C] →       [inst_2 : CategoryTheory.Br
aidedCategory C] →         CategoryTheory.CommRingObjCat C → CategoryTheory.Comm
RingObjCat C → Type v
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism of commutative ring objects.
-/
structure Hom (R₁ R₂ : CommRingObjCat C) where
  /-- The underlying morphism -/
  hom : R₁.X ⟶ R₂.X
  [isRingHom : IsRingHom hom]

attribute [instance] Hom.isRingHom

@[simps]
/-
**CategoryTheory.CommRingObjCat.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.CommR
ingObjCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Category (CommRingObjCat C) where
  Hom R₁ R₂ := Hom R₁ R₂
  id X := { hom := 𝟙 _ }
  comp f g := { hom := f.hom ≫ g.hom }

@[ext]
/-
**CategoryTheory.CommRingObjCat.hom_ext** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.CommRingObjCat`。
形式化陈述：hom_ext {R₁ R₂ : CommRingObjCat C} {f g : R₁ ⟶ R₂} (h : f.hom = g.hom) : f
 = g
参数：h : f.hom = g.hom。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CommRingObjCat.Hom.ext`：∀ {C : Type u} {inst : CategoryTh
eory.Category.{v, u} C} {inst_1 : CategoryTheory.CartesianMonoidalCategory C}   
{inst_2 : CategoryTheory.Br…
-/
lemma hom_ext {R₁ R₂ : CommRingObjCat C} {f g : R₁ ⟶ R₂} (h : f.hom = g.hom) : f = g :=
  Hom.ext h

variable (C) in
/-- The forgetful functor from the category of ring objects in `C` to `C`. -/
@[simps]
/-
**CategoryTheory.CommRingObjCat.forget** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.CommRingObjCat`。
形式化陈述：forget : CommRingObjCat C ⥤ C where obj R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful functor from the category of ring objects in `C` to `C`.
-/
def forget : CommRingObjCat C ⥤ C where
  obj R := R.X
  map f := f.hom

variable (C) in
/-- The forgetful functor from the category of commutative ring objects
to the category of ring objects. -/
@[simps]
/-
**CategoryTheory.CommRingObjCat.forget** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.CommRingObjCat`。
形式化陈述：forget : CommRingObjCat C ⥤ C where obj R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful functor from the category of commutative ring objects
to the category of ring objects.
-/
def forget₂RingObjCat : CommRingObjCat C ⥤ RingObjCat C where
  obj R := .mk R.X
  map f := { hom := f.hom }

variable (C) in
/-- The forgetful functor `CommRingObjCat C ⥤ RingObjCat C` is fully faithful. -/
/-
**CategoryTheory.CommRingObjCat.fullyFaithfulForget** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.CommRingObjCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful functor `CommRingObjCat C ⥤ RingObjCat C` is fully faithful.
-/
def fullyFaithfulForget₂RingObjCat : (forget₂RingObjCat C).FullyFaithful where
  preimage f := { hom := f.hom, isRingHom := f.isRingHom }
/-
**CategoryTheory.CommRingObjCat.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.CommR
ingObjCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (forget₂RingObjCat C).Faithful :=
  (fullyFaithfulForget₂RingObjCat C).faithful
/-
**CategoryTheory.CommRingObjCat.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.CommR
ingObjCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (forget₂RingObjCat C).Full :=
  (fullyFaithfulForget₂RingObjCat C).full
/-
**CategoryTheory.CommRingObjCat.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.CommR
ingObjCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (forget C).Faithful where

end CommRingObjCat

end CategoryTheory

