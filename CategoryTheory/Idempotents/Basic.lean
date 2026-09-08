/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Abelian.Basic

/-!
# Idempotent complete categories

In this file, we define the notion of idempotent complete categories
(also known as Karoubian categories, or pseudoabelian in the case of
preadditive categories).

## Main definitions

- `IsIdempotentComplete C` expresses that `C` is idempotent complete, i.e.
  all idempotents in `C` split. Other characterisations of idempotent completeness are given
  by `isIdempotentComplete_iff_hasEqualizer_of_id_and_idempotent` and
  `isIdempotentComplete_iff_idempotents_have_kernels`.
- `isIdempotentComplete_of_abelian` expresses that abelian categories are
  idempotent complete.
- `isIdempotentComplete_iff_ofEquivalence` expresses that if two categories `C` and `D`
  are equivalent, then `C` is idempotent complete iff `D` is.
- `isIdempotentComplete_iff_opposite` expresses that `Cᵒᵖ` is idempotent complete
  iff `C` is.

## References
* [Stacks: Karoubian categories] https://stacks.math.columbia.edu/tag/09SF

-/

public section


open CategoryTheory

open CategoryTheory.Category

open CategoryTheory.Limits

open CategoryTheory.Preadditive

open Opposite

namespace CategoryTheory

variable (C : Type*) [Category* C]

/-- A category is idempotent complete iff all idempotent endomorphisms `p`
split as a composition `p = e ≫ i` with `i ≫ e = 𝟙 _` -/
/-
**CategoryTheory.IsIdempotentComplete** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheor
y`。
形式化陈述：(C : Type u_1) → [CategoryTheory.Category.{v_1, u_1} C] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A category is idempotent complete iff all idempotent endomorphisms `p`
split as a composition `p = e ≫ i` with `i ≫ e = 𝟙 _`
-/
class IsIdempotentComplete : Prop where
  /-- A category is idempotent complete iff all idempotent endomorphisms `p`
  split as a composition `p = e ≫ i` with `i ≫ e = 𝟙 _` -/
  idempotents_split :
    ∀ (X : C) (p : X ⟶ X), p ≫ p = p → ∃ (Y : C) (i : Y ⟶ X) (e : X ⟶ Y), i ≫ e = 𝟙 Y ∧ e ≫ i = p

namespace Idempotents

set_option backward.isDefEq.respectTransparency false in
/-- A category is idempotent complete iff for all idempotent endomorphisms,
the equalizer of the identity and this idempotent exists. -/
/-
**CategoryTheory.Idempotents.isIdempotentComplete_iff_hasEqualizer_of_id_and_ide
mpotent** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Idempotents`。
形式化陈述：isIdempotentComplete_iff_hasEqualizer_of_id_and_idempotent : IsIdempotentC
omplete C ↔ forall (X : C) (p : X ⟶ X), p ≫ p = p -> HasEqualizer (𝟙 X) p
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsIdempotentComplete.idempotents_split`：∀ {C : Type u_1} 
{inst : CategoryTheory.Category.{v_1, u_1} C} [self : CategoryTheory.IsIdempoten
tComplete C] (X : C)   (p : X ⟶ X),   Categ…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.Fork.condition`：∀ {C : Type u} {X Y : C} [inst : C
ategoryTheory.Category.{v, u} C] {f g : X ⟶ Y} (t : CategoryTheory.Limits.Fork f
 g),   CategoryTheory.Cate…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.Fork.ι_ofι`：∀ {C : Type u} {X Y : C} [inst : Categ
oryTheory.Category.{v, u} C] {f g : X ⟶ Y} {P : C} (ι : P ⟶ X)   (w : CategoryTh
eory.CategoryStruct.co…
· 使用定理 `CategoryTheory.Limits.equalizer.hom_ext`：∀ {C : Type u} {X Y : C} [inst 
: CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y}   [inst_1 : CategoryTheory.Lim
its.HasEqualizer f g] {W : C}…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.equalizer.condition`：∀ {C : Type u} {X Y : C} [ins
t : CategoryTheory.Category.{v, u} C] (f g : X ⟶ Y)   [inst_1 : CategoryTheory.L
imits.HasEqualizer f g],   Cate…
· 使用定理 `CategoryTheory.Limits.equalizer.lift_ι`：∀ {C : Type u} {X Y : C} [inst :
 CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y}   [inst_1 : CategoryTheory.Limi
ts.HasEqualizer f g] {W : C}…

--- 原说明 ---
A category is idempotent complete iff for all idempotent endomorphisms,
the equalizer of the identity and this idempotent exists.
-/
theorem isIdempotentComplete_iff_hasEqualizer_of_id_and_idempotent :
    IsIdempotentComplete C ↔ ∀ (X : C) (p : X ⟶ X), p ≫ p = p → HasEqualizer (𝟙 X) p := by
  constructor
  · intro _ X p hp
    rcases IsIdempotentComplete.idempotents_split X p hp with ⟨Y, i, e, ⟨h₁, h₂⟩⟩
    exact
      ⟨Nonempty.intro
          { cone := Fork.ofι i (show i ≫ 𝟙 X = i ≫ p by rw [comp_id, ← h₂, ← assoc, h₁, id_comp])
            isLimit := by
              apply Fork.IsLimit.mk'
              intro s
              refine ⟨s.ι ≫ e, ?_⟩
              constructor
              · simp [h₂, ← Limits.Fork.condition s]
              · intro m hm
                rw [Fork.ι_ofι] at hm
                rw [← hm]
                simp only [assoc, h₁]
                exact (comp_id m).symm }⟩
  · intro h
    refine ⟨?_⟩
    intro X p hp
    have : HasEqualizer (𝟙 X) p := h X p hp
    refine ⟨equalizer (𝟙 X) p, equalizer.ι (𝟙 X) p,
      equalizer.lift p (show p ≫ 𝟙 X = p ≫ p by rw [hp, comp_id]), ?_, equalizer.lift_ι _ _⟩
    ext
    simp only [assoc, limit.lift_π,
      Fork.ofι_π_app, id_comp]
    rw [← equalizer.condition, comp_id]

variable {C} in
/-- In a preadditive category, when `p : X ⟶ X` is idempotent,
then `𝟙 X - p` is also idempotent. -/
/-
**CategoryTheory.Idempotents.idem_of_id_sub_idem** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Idempotents`。
形式化陈述：idem_of_id_sub_idem [Preadditive C] {X : C} (p : X ⟶ X) (hp : p ≫ p = p) :
 (𝟙 _ - p) ≫ (𝟙 _ - p) = 𝟙 _ - p
参数：p : X ⟶ X；hp : p ≫ p = p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Preadditive.comp_sub`：comp_sub : f ≫ (g - g') = f ≫ g - f
 ≫ g'
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Preadditive.sub_comp`：sub_comp : (f - f') ≫ g = f ≫ g - f
' ≫ g
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
In a preadditive category, when `p : X ⟶ X` is idempotent,
then `𝟙 X - p` is also idempotent.
-/
theorem idem_of_id_sub_idem [Preadditive C] {X : C} (p : X ⟶ X) (hp : p ≫ p = p) :
    (𝟙 _ - p) ≫ (𝟙 _ - p) = 𝟙 _ - p := by
  simp only [comp_sub, sub_comp, id_comp, comp_id, hp, sub_self, sub_zero]

/-- A preadditive category is pseudoabelian iff all idempotent endomorphisms have a kernel. -/
/-
**CategoryTheory.Idempotents.isIdempotentComplete_iff_idempotents_have_kernels**
 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Idempotents`。
形式化陈述：isIdempotentComplete_iff_idempotents_have_kernels [Preadditive C] : IsIdem
potentComplete C ↔ forall (X : C) (p : X ⟶ X), p ≫ p = p -> HasKernel p
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Idempotents.isIdempotentComplete_iff_hasEqualizer_of_id_a
nd_idempotent`：isIdempotentComplete_iff_hasEqualizer_of_id_and_idempotent : IsId
empotentComplete C ↔ forall (X : C) (p : X ⟶ X), p ≫ p = p -> HasEqualizer …
· 使用定理 `CategoryTheory.Idempotents.idem_of_id_sub_idem`：idem_of_id_sub_idem [Pre
additive C] {X : C} (p : X ⟶ X) (hp : p ≫ p = p) : (𝟙 _ - p) ≫ (𝟙 _ - p) = 𝟙 _ -
 p
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a - 
(a - b) = b
· 使用定理 `CategoryTheory.Preadditive.hasKernel_of_hasEqualizer`：hasKernel_of_hasEq
ualizer [HasEqualizer f g] : HasKernel (f - g)
· 使用定理 `CategoryTheory.Preadditive.hasEqualizer_of_hasKernel`：hasEqualizer_of_ha
sKernel [HasKernel (f - g)] : HasEqualizer f g

--- 原说明 ---
A preadditive category is pseudoabelian iff all idempotent endomorphisms have a 
kernel.
-/
theorem isIdempotentComplete_iff_idempotents_have_kernels [Preadditive C] :
    IsIdempotentComplete C ↔ ∀ (X : C) (p : X ⟶ X), p ≫ p = p → HasKernel p := by
  rw [isIdempotentComplete_iff_hasEqualizer_of_id_and_idempotent]
  constructor
  · intro h X p hp
    have : HasEqualizer (𝟙 X) (𝟙 X - p) := h X (𝟙 _ - p) (idem_of_id_sub_idem p hp)
    convert! hasKernel_of_hasEqualizer (𝟙 X) (𝟙 X - p)
    rw [sub_sub_cancel]
  · intro h X p hp
    have : HasKernel (𝟙 _ - p) := h X (𝟙 _ - p) (idem_of_id_sub_idem p hp)
    apply Preadditive.hasEqualizer_of_hasKernel

/-- An abelian category is idempotent complete. -/
/-
**CategoryTheory.Idempotents.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Idempote
nts`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An abelian category is idempotent complete.
-/
instance (priority := 100) isIdempotentComplete_of_abelian (D : Type*) [Category* D] [Abelian D] :
    IsIdempotentComplete D := by
  rw [isIdempotentComplete_iff_idempotents_have_kernels]
  intros
  infer_instance

variable {C}
/-
**CategoryTheory.Idempotents.split_imp_of_iso** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Idempotents`。
形式化陈述：split_imp_of_iso {X X' : C} (φ : X ≅ X') (p : X ⟶ X) (p' : X' ⟶ X') (hpp' 
: p ≫ φ.hom = φ.hom ≫ p') (h : exists (Y : C) (i : Y ⟶ X) (e : X ⟶ Y), i ≫ e = 𝟙
 Y ∧ e ≫ i = p) : exists (Y' : C) (i' : Y' ⟶ X') (e' : X' ⟶ Y'), i' ≫ e' = 𝟙 Y' 
∧ e' ≫ i' = p'
参数：φ : X ≅ X'；p : X ⟶ X；p' : X' ⟶ X'；hpp' : p ≫ φ.hom = φ.hom ≫ p'；h : exists (Y
 : C) (i : Y ⟶ X) (e : X ⟶ Y), i ≫ e = 𝟙 Y ∧ e ≫ i = p。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem split_imp_of_iso {X X' : C} (φ : X ≅ X') (p : X ⟶ X) (p' : X' ⟶ X')
    (hpp' : p ≫ φ.hom = φ.hom ≫ p')
    (h : ∃ (Y : C) (i : Y ⟶ X) (e : X ⟶ Y), i ≫ e = 𝟙 Y ∧ e ≫ i = p) :
    ∃ (Y' : C) (i' : Y' ⟶ X') (e' : X' ⟶ Y'), i' ≫ e' = 𝟙 Y' ∧ e' ≫ i' = p' := by
  rcases h with ⟨Y, i, e, ⟨h₁, h₂⟩⟩
  use Y, i ≫ φ.hom, φ.inv ≫ e
  grind
/-
**CategoryTheory.Idempotents.split_iff_of_iso** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Idempotents`。
形式化陈述：split_iff_of_iso {X X' : C} (φ : X ≅ X') (p : X ⟶ X) (p' : X' ⟶ X') (hpp' 
: p ≫ φ.hom = φ.hom ≫ p') : (exists (Y : C) (i : Y ⟶ X) (e : X ⟶ Y), i ≫ e = 𝟙 Y
 ∧ e ≫ i = p) ↔ exists (Y' : C) (i' : Y' ⟶ X') (e' : X' ⟶ Y'), i' ≫ e' = 𝟙 Y' ∧ 
e' ≫ i' = p'
参数：φ : X ≅ X'；p : X ⟶ X；p' : X' ⟶ X'；hpp' : p ≫ φ.hom = φ.hom ≫ p'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Idempotents.split_imp_of_iso`：split_imp_of_iso {X X' : C}
 (φ : X ≅ X') (p : X ⟶ X) (p' : X' ⟶ X') (hpp' : p ≫ φ.hom = φ.hom ≫ p') (h : ex
ists (Y : C) (i : Y ⟶ X) (e : X ⟶…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem split_iff_of_iso {X X' : C} (φ : X ≅ X') (p : X ⟶ X) (p' : X' ⟶ X')
    (hpp' : p ≫ φ.hom = φ.hom ≫ p') :
    (∃ (Y : C) (i : Y ⟶ X) (e : X ⟶ Y), i ≫ e = 𝟙 Y ∧ e ≫ i = p) ↔
      ∃ (Y' : C) (i' : Y' ⟶ X') (e' : X' ⟶ Y'), i' ≫ e' = 𝟙 Y' ∧ e' ≫ i' = p' := by
  constructor
  · exact split_imp_of_iso φ p p' hpp'
  · apply split_imp_of_iso φ.symm p' p
    rw [← comp_id p, ← φ.hom_inv_id]
    slice_rhs 2 3 => rw [hpp']
    simp
/-
**CategoryTheory.Idempotents.Equivalence.isIdempotentComplete** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.Idempotents.Equivalence`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {D : Type u
_2}   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] (ε : C ≌ D),   CategoryThe
ory.IsIdempotentComplete C → CategoryTheory.IsIdempotentComplete D
参数：ε : C ≌ D。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Idempotents.split_iff_of_iso`：split_iff_of_iso {X X' : C}
 (φ : X ≅ X') (p : X ⟶ X) (p' : X' ⟶ X') (hpp' : p ≫ φ.hom = φ.hom ≫ p') : (exis
ts (Y : C) (i : Y ⟶ X) (e : X ⟶ Y…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.IsIdempotentComplete.idempotents_split`：∀ {C : Type u_1} 
{inst : CategoryTheory.Category.{v_1, u_1} C} [self : CategoryTheory.IsIdempoten
tComplete C] (X : C)   (p : X ⟶ X),   Categ…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Equivalence.fun_inv_map`：fun_inv_map (e : C ≌ D) (X Y : D
) (f : X ⟶ Y) : e.functor.map (e.inverse.map f) = e.counit.app X ≫ f ≫ e.counitI
nv.app Y
-/
theorem Equivalence.isIdempotentComplete {D : Type*} [Category* D] (ε : C ≌ D)
    (h : IsIdempotentComplete C) : IsIdempotentComplete D := by
  refine ⟨?_⟩
  intro X' p hp
  let φ := ε.counitIso.symm.app X'
  simp only [Functor.id_obj] at φ
  rw [split_iff_of_iso φ p (φ.inv ≫ p ≫ φ.hom)
      (by
        slice_rhs 1 2 => rw [φ.hom_inv_id]
        rw [id_comp])]
  rcases IsIdempotentComplete.idempotents_split (ε.inverse.obj X') (ε.inverse.map p)
      (by rw [← ε.inverse.map_comp, hp]) with
    ⟨Y, i, e, ⟨h₁, h₂⟩⟩
  use ε.functor.obj Y, ε.functor.map i, ε.functor.map e
  constructor
  · rw [← ε.functor.map_comp, h₁, ε.functor.map_id]
  · simp only [← ε.functor.map_comp, h₂, Equivalence.fun_inv_map]
    rfl

/-- If `C` and `D` are equivalent categories, that `C` is idempotent complete iff `D` is. -/
/-
**CategoryTheory.Idempotents.isIdempotentComplete_iff_of_equivalence** 是 Mathlib
 中的一个定理，位于命名空间 `CategoryTheory.Idempotents`。
形式化陈述：isIdempotentComplete_iff_of_equivalence {D : Type*} [Category* D] (ε : C ≌
 D) : IsIdempotentComplete C ↔ IsIdempotentComplete D
参数：ε : C ≌ D。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Idempotents.Equivalence.isIdempotentComplete`：∀ {C : Type
 u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {D : Type u_2}   [inst_1 : C
ategoryTheory.Category.{v_2, u_2} D] (ε : C ≌ D),…

--- 原说明 ---
If `C` and `D` are equivalent categories, that `C` is idempotent complete iff `D
` is.
-/
theorem isIdempotentComplete_iff_of_equivalence {D : Type*} [Category* D] (ε : C ≌ D) :
    IsIdempotentComplete C ↔ IsIdempotentComplete D := by
  constructor
  · exact Equivalence.isIdempotentComplete ε
  · exact Equivalence.isIdempotentComplete ε.symm
/-
**CategoryTheory.Idempotents.isIdempotentComplete_of_isIdempotentComplete_opposi
te** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Idempotents`。
形式化陈述：isIdempotentComplete_of_isIdempotentComplete_opposite (h : IsIdempotentCom
plete Cᵒᵖ) : IsIdempotentComplete C
参数：h : IsIdempotentComplete Cᵒᵖ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsIdempotentComplete.idempotents_split`：∀ {C : Type u_1} 
{inst : CategoryTheory.Category.{v_1, u_1} C} [self : CategoryTheory.IsIdempoten
tComplete C] (X : C)   (p : X ⟶ X),   Categ…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.op_comp`：op_comp {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} : (f
 ≫ g).op = g.op ≫ f.op
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
theorem isIdempotentComplete_of_isIdempotentComplete_opposite (h : IsIdempotentComplete Cᵒᵖ) :
    IsIdempotentComplete C := by
  refine ⟨?_⟩
  intro X p hp
  rcases IsIdempotentComplete.idempotents_split (op X) p.op (by rw [← op_comp, hp]) with
    ⟨Y, i, e, ⟨h₁, h₂⟩⟩
  use Y.unop, e.unop, i.unop
  constructor
  · simp only [← unop_comp, h₁]
    rfl
  · simp only [← unop_comp, h₂]
    rfl
/-
**CategoryTheory.Idempotents.isIdempotentComplete_iff_opposite** 是 Mathlib 中的一个定
理，位于命名空间 `CategoryTheory.Idempotents`。
形式化陈述：isIdempotentComplete_iff_opposite : IsIdempotentComplete Cᵒᵖ ↔ IsIdempoten
tComplete C
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Idempotents.isIdempotentComplete_of_isIdempotentComplete_
opposite`：isIdempotentComplete_of_isIdempotentComplete_opposite (h : IsIdempoten
tComplete Cᵒᵖ) : IsIdempotentComplete C
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Idempotents.isIdempotentComplete_iff_of_equivalence`：isId
empotentComplete_iff_of_equivalence {D : Type*} [Category* D] (ε : C ≌ D) : IsId
empotentComplete C ↔ IsIdempotentComplete D
-/
theorem isIdempotentComplete_iff_opposite : IsIdempotentComplete Cᵒᵖ ↔ IsIdempotentComplete C := by
  constructor
  · exact isIdempotentComplete_of_isIdempotentComplete_opposite
  · intro h
    apply isIdempotentComplete_of_isIdempotentComplete_opposite
    rw [isIdempotentComplete_iff_of_equivalence (opOpEquivalence C)]
    exact h
/-
**CategoryTheory.Idempotents.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Idempote
nts`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsIdempotentComplete C] : IsIdempotentComplete Cᵒᵖ := by
  rwa [isIdempotentComplete_iff_opposite]

end Idempotents

end CategoryTheory

