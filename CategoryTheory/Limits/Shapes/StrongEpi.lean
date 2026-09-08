/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Balanced
public import Mathlib.CategoryTheory.LiftingProperties.Basic

/-!
# Strong epimorphisms

In this file, we define strong epimorphisms. A strong epimorphism is an epimorphism `f`
which has the (unique) left lifting property with respect to monomorphisms. Similarly,
a strong monomorphism is a monomorphism which has the (unique) right lifting property
with respect to epimorphisms.

## Main results

Besides the definition, we show that
* the composition of two strong epimorphisms is a strong epimorphism,
* if `f ≫ g` is a strong epimorphism, then so is `g`,
* if `f` is both a strong epimorphism and a monomorphism, then it is an isomorphism

We also define classes `StrongMonoCategory` and `StrongEpiCategory` for categories in which
every monomorphism or epimorphism is strong, and deduce that these categories are balanced.

## TODO

Show that the dual of a strong epimorphism is a strong monomorphism, and vice versa.

## References

* [F. Borceux, *Handbook of Categorical Algebra 1*][borceux-vol1]
-/

public section


universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable {P Q : C}

to_dual_name_hint Epi Mono

/-- A strong epimorphism `f` is an epimorphism which has the left lifting property
with respect to monomorphisms. -/
/-
**CategoryTheory.StrongEpi** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`。
形式化陈述：{C : Type u} → [inst : CategoryTheory.Category.{v, u} C] → {P Q : C} → (P 
⟶ Q) → Prop
参数：P ⟶ Q。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A strong epimorphism `f` is an epimorphism which has the left lifting property
with respect to monomorphisms.
-/
class StrongEpi (f : P ⟶ Q) : Prop where
  /-- The epimorphism condition on `f` -/
  epi : Epi f
  /-- The left lifting property with respect to all monomorphisms -/
  llp : ∀ ⦃X Y : C⦄ (z : X ⟶ Y) [Mono z], HasLiftingProperty f z

/-- A strong monomorphism `f` is a monomorphism which has the right lifting property
with respect to epimorphisms. -/
@[to_dual]
/-
**CategoryTheory.StrongMono** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`。
形式化陈述：{C : Type u} → [inst : CategoryTheory.Category.{v, u} C] → {P Q : C} → (P 
⟶ Q) → Prop
参数：P ⟶ Q。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A strong monomorphism `f` is a monomorphism which has the right lifting property
with respect to epimorphisms.
-/
class StrongMono (f : P ⟶ Q) : Prop where
  /-- The monomorphism condition on `f` -/
  mono : Mono f
  /-- The right lifting property with respect to all epimorphisms -/
  rlp : ∀ ⦃X Y : C⦄ (z : X ⟶ Y) [Epi z], HasLiftingProperty z f

@[to_dual (reorder := hf (X Y, u v))]
/-
**CategoryTheory.StrongEpi.mk'** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.StrongE
pi`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {P Q : C} {f : P 
⟶ Q} [CategoryTheory.Epi f],   (∀ (X Y : C) (z : X ⟶ Y),       CategoryTheory.Mo
no z → ∀ (u : P ⟶ X) (v : Q ⟶ Y) (sq : CategoryTheory.CommSq u f z v), sq.HasLif
t) →     CategoryTheory.StrongEpi f
参数：∀ (X Y : C) (z : X ⟶ Y),       CategoryTheory.Mono z → ∀ (u : P ⟶ X) (v : Q ⟶
 Y) (sq : CategoryTheory.CommSq u f z v), sq.HasLift。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem StrongEpi.mk' {f : P ⟶ Q} [Epi f]
    (hf : ∀ (X Y : C) (z : X ⟶ Y) (_ : Mono z) (u : P ⟶ X)
      (v : Q ⟶ Y) (sq : CommSq u f z v), sq.HasLift) : StrongEpi f where
  epi := inferInstance
  llp {X Y} z hz := ⟨fun {u v} sq => hf X Y z hz u v sq⟩

attribute [instance 100] StrongEpi.epi StrongEpi.llp StrongMono.mono StrongMono.rlp

section

variable {R : C} (f : P ⟶ Q) (g : Q ⟶ R)

/-- The composition of two strong epimorphisms is a strong epimorphism. -/
@[to_dual /-- The composition of two strong monomorphisms is a strong monomorphism. -/]
/-
**CategoryTheory.strongEpi_comp** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
形式化陈述：strongEpi_comp [StrongEpi f] [StrongEpi g] : StrongEpi (f ≫ g)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.StrongEpi.epi`：∀ {C : Type u} {inst : CategoryTheory.Cate
gory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongEpi f],   Cate
goryTheory.Epi f
· 使用定理 `CategoryTheory.StrongEpi.llp`：∀ {C : Type u} {inst : CategoryTheory.Cate
gory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongEpi f]   ⦃X Y 
: C⦄ (z : X ⟶ Y) […

--- 原说明 ---
The composition of two strong epimorphisms is a strong epimorphism.
-/
instance strongEpi_comp [StrongEpi f] [StrongEpi g] : StrongEpi (f ≫ g) :=
  { epi := epi_comp _ _
    llp := by
      intros
      infer_instance }

/-- If `f ≫ g` is a strong epimorphism, then so is `g`. -/
@[to_dual (reorder := f g) (rename := f ↔ g, P ↔ R)
/-- If `f ≫ g` is a strong monomorphism, then so is `f`. -/]
/-
**CategoryTheory.strongEpi_of_strongEpi** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y`。
形式化陈述：strongEpi_of_strongEpi [StrongEpi (f ≫ g)] : StrongEpi g
参数：f ≫ g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.epi_of_epi`：epi_of_epi (f : X ⟶ Y) (g : Y ⟶ Z) [Epi (f ≫ 
g)] : Epi g
· 使用定理 `CategoryTheory.StrongEpi.epi`：∀ {C : Type u} {inst : CategoryTheory.Cate
gory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongEpi f],   Cate
goryTheory.Epi f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.CommSq.w`：∀ {C : Type u_1} [inst : CategoryTheory.Categor
y.{v_1, u_1} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z}   {i : Y ⟶ Z},
   CategoryTh…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.CommSq.HasLift.mk'`：mk' (l : sq.LiftStruct) : HasLift sq
· 使用定理 `CategoryTheory.sq_hasLift_of_hasLiftingProperty`：∀ {C : Type u_1} [inst 
: CategoryTheory.Category.{v_1, u_1} C] {A B X Y : C} (i : A ⟶ B) (p : X ⟶ Y) {f
 : A ⟶ X}   {g : B ⟶ Y} (sq : Categor…
· 使用定理 `CategoryTheory.StrongEpi.llp`：∀ {C : Type u} {inst : CategoryTheory.Cate
gory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongEpi f]   ⦃X Y 
: C⦄ (z : X ⟶ Y) […
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.CommSq.fac_right`：∀ {C : Type u_1} [inst : CategoryTheory
.Category.{v_1, u_1} C] {A B X Y : C} {f : X ⟶ A} {i : B ⟶ A} {p : Y ⟶ X}   {g :
 Y ⟶ B} (sq : Categor…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
theorem strongEpi_of_strongEpi [StrongEpi (f ≫ g)] : StrongEpi g :=
  { epi := epi_of_epi f g
    llp := fun {X Y} z _ => by
      constructor
      intro u v sq
      have h₀ : (f ≫ u) ≫ z = (f ≫ g) ≫ v := by simp only [Category.assoc, sq.w]
      exact
        CommSq.HasLift.mk'
          ⟨(CommSq.mk h₀).lift, by
            simp only [← cancel_mono z, Category.assoc, CommSq.fac_right, sq.w], by simp⟩ }

/-- An isomorphism is in particular a strong epimorphism. -/
@[to_dual /-- An isomorphism is in particular a strong monomorphism. -/]
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An isomorphism is in particular a strong epimorphism.
-/
instance (priority := 100) strongEpi_of_isIso [IsIso f] : StrongEpi f where
  epi := by infer_instance
  llp {_ _} _ := HasLiftingProperty.of_left_iso _ _

set_option backward.isDefEq.respectTransparency false in
@[to_dual]
/-
**CategoryTheory.StrongEpi.of_arrow_iso** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.StrongEpi`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {A B A' B' : C} {
f : A ⟶ B} {g : A' ⟶ B'}   (e : CategoryTheory.Arrow.mk f ≅ CategoryTheory.Arrow
.mk g) [h : CategoryTheory.StrongEpi f],   CategoryTheory.StrongEpi g
参数：e : CategoryTheory.Arrow.mk f ≅ CategoryTheory.Arrow.mk g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Arrow.iso_w'`：iso_w' {W X Y Z : T} {f : W ⟶ X} {g : Y ⟶ Z
} (e : Arrow.mk f ≅ Arrow.mk g) : g = e.inv.left ≫ f ≫ e.hom.right
· 使用定理 `CategoryTheory.StrongEpi.epi`：∀ {C : Type u} {inst : CategoryTheory.Cate
gory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongEpi f],   Cate
goryTheory.Epi f
· 使用定理 `CategoryTheory.strongEpi_of_isIso`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] {P Q : C} (f : P ⟶ Q) [CategoryTheory.IsIso f],   CategoryTh
eory.StrongEpi f
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `CategoryTheory.Arrow.epi_right`：∀ {T : Type u} [inst : CategoryTheory.Ca
tegory.{v, u} T] {f g : CategoryTheory.Arrow T} (sq : g ⟶ f)   [CategoryTheory.E
pi sq], CategoryTheo…
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.HasLiftingProperty.of_arrow_iso_left`：of_arrow_iso_left {
A B A' B' X Y : C} {i : A ⟶ B} {i' : A' ⟶ B'} (e : Arrow.mk i ≅ Arrow.mk i') (p 
: X ⟶ Y) [hip : HasLiftingProperty i p] :…
· 使用定理 `CategoryTheory.StrongEpi.llp`：∀ {C : Type u} {inst : CategoryTheory.Cate
gory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongEpi f]   ⦃X Y 
: C⦄ (z : X ⟶ Y) […
-/
theorem StrongEpi.of_arrow_iso {A B A' B' : C} {f : A ⟶ B} {g : A' ⟶ B'}
    (e : Arrow.mk f ≅ Arrow.mk g) [h : StrongEpi f] : StrongEpi g where
  epi := by
    rw [Arrow.iso_w' e]
    infer_instance
  llp := fun {X Y} z => by
    intro
    apply HasLiftingProperty.of_arrow_iso_left e z

@[to_dual]
/-
**CategoryTheory.StrongEpi.iff_of_arrow_iso** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.StrongEpi`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {A B A' B' : C} {
f : A ⟶ B} {g : A' ⟶ B'}   (e : CategoryTheory.Arrow.mk f ≅ CategoryTheory.Arrow
.mk g), CategoryTheory.StrongEpi f ↔ CategoryTheory.StrongEpi g
参数：e : CategoryTheory.Arrow.mk f ≅ CategoryTheory.Arrow.mk g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.StrongEpi.of_arrow_iso`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {A B A' B' : C} {f : A ⟶ B} {g : A' ⟶ B'}   (e : Categor
yTheory.Arrow.mk f ≅ Catego…
-/
theorem StrongEpi.iff_of_arrow_iso {A B A' B' : C} {f : A ⟶ B} {g : A' ⟶ B'}
    (e : Arrow.mk f ≅ Arrow.mk g) : StrongEpi f ↔ StrongEpi g := by
  constructor <;> intro
  exacts [StrongEpi.of_arrow_iso e, StrongEpi.of_arrow_iso e.symm]

end

/-- A strong epimorphism that is a monomorphism is an isomorphism. -/
@[to_dual /-- A strong monomorphism that is an epimorphism is an isomorphism. -/]
/-
**CategoryTheory.isIso_of_mono_of_strongEpi** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory`。
形式化陈述：isIso_of_mono_of_strongEpi (f : P ⟶ Q) [Mono f] [StrongEpi f] : IsIso f
参数：f : P ⟶ Q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.sq_hasLift_of_hasLiftingProperty`：∀ {C : Type u_1} [inst 
: CategoryTheory.Category.{v_1, u_1} C] {A B X Y : C} (i : A ⟶ B) (p : X ⟶ Y) {f
 : A ⟶ X}   {g : B ⟶ Y} (sq : Categor…
· 使用定理 `CategoryTheory.StrongEpi.llp`：∀ {C : Type u} {inst : CategoryTheory.Cate
gory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongEpi f]   ⦃X Y 
: C⦄ (z : X ⟶ Y) […
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.CommSq.fac_left`：fac_left [hsq : HasLift sq] : i ≫ sq.lif
t = f
· 使用定理 `CategoryTheory.CommSq.fac_right`：∀ {C : Type u_1} [inst : CategoryTheory
.Category.{v_1, u_1} C] {A B X Y : C} {f : X ⟶ A} {i : B ⟶ A} {p : Y ⟶ X}   {g :
 Y ⟶ B} (sq : Categor…
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p

--- 原说明 ---
A strong epimorphism that is a monomorphism is an isomorphism.
-/
theorem isIso_of_mono_of_strongEpi (f : P ⟶ Q) [Mono f] [StrongEpi f] : IsIso f :=
  ⟨⟨(CommSq.mk (show 𝟙 P ≫ f = f ≫ 𝟙 Q by simp)).lift, by simp⟩⟩

section

variable (C)

/-- A strong epi category is a category in which every epimorphism is strong. -/
/-
**CategoryTheory.StrongEpiCategory** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`。
形式化陈述：(C : Type u) → [CategoryTheory.Category.{v, u} C] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A strong epi category is a category in which every epimorphism is strong.
-/
class StrongEpiCategory : Prop where
  /-- A strong epi category is a category in which every epimorphism is strong. -/
  strongEpi_of_epi : ∀ {X Y : C} (f : X ⟶ Y) [Epi f], StrongEpi f

/-- A strong mono category is a category in which every monomorphism is strong. -/
@[to_dual]
/-
**CategoryTheory.StrongMonoCategory** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`
。
形式化陈述：(C : Type u) → [CategoryTheory.Category.{v, u} C] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A strong mono category is a category in which every monomorphism is strong.
-/
class StrongMonoCategory : Prop where
  /-- A strong mono category is a category in which every monomorphism is strong. -/
  strongMono_of_mono : ∀ {X Y : C} (f : X ⟶ Y) [Mono f], StrongMono f

end

@[to_dual]
/-
**CategoryTheory.strongEpi_of_epi** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：strongEpi_of_epi [StrongEpiCategory C] (f : P ⟶ Q) [Epi f] : StrongEpi f
参数：f : P ⟶ Q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.StrongEpiCategory.strongEpi_of_epi`：∀ {C : Type u} {inst 
: CategoryTheory.Category.{v, u} C} [self : CategoryTheory.StrongEpiCategory C] 
{X Y : C}   (f : X ⟶ Y) [CategoryTheory…
-/
theorem strongEpi_of_epi [StrongEpiCategory C] (f : P ⟶ Q) [Epi f] : StrongEpi f :=
  StrongEpiCategory.strongEpi_of_epi _

section

attribute [local instance] strongEpi_of_epi

@[to_dual]
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) balanced_of_strongEpiCategory [StrongEpiCategory C] : Balanced C where
  isIso_of_mono_of_epi _ _ _ := isIso_of_mono_of_strongEpi _

end

end CategoryTheory

