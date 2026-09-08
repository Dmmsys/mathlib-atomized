/-
Copyright (c) 2024 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/
module

public import Mathlib.CategoryTheory.Retract
public import Mathlib.CategoryTheory.MorphismProperty.Basic

/-!
# Stability under retracts

Given `P : MorphismProperty C`, we introduce a typeclass `P.IsStableUnderRetracts` which
is the property that `P` is stable under retracts.

-/

@[expose] public section

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace MorphismProperty

/-- A class of morphisms is stable under retracts if a retract of such a morphism still
lies in the class. -/
@[mk_iff]
/-
**CategoryTheory.MorphismProperty.IsStableUnderRetracts** 是 Mathlib 中的一个归纳类型，位于命
名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：{C : Type u} → [inst : CategoryTheory.Category.{v, u} C] → CategoryTheory.
MorphismProperty C → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A class of morphisms is stable under retracts if a retract of such a morphism st
ill
lies in the class.
-/
class IsStableUnderRetracts (P : MorphismProperty C) : Prop where
  of_retract {X Y Z W : C} {f : X ⟶ Y} {g : Z ⟶ W} (h : RetractArrow f g) (hg : P g) : P f
/-
**CategoryTheory.MorphismProperty.of_retract** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.MorphismProperty`。
形式化陈述：of_retract {P : MorphismProperty C} [P.IsStableUnderRetracts] {X Y Z W : C
} {f : X ⟶ Y} {g : Z ⟶ W} (h : RetractArrow f g) (hg : P g) : P f
参数：h : RetractArrow f g；hg : P g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsStableUnderRetracts.of_retract`：∀ {C :
 Type u} {inst : CategoryTheory.Category.{v, u} C} {P : CategoryTheory.MorphismP
roperty C}   [self : P.IsStableUnderRetracts] {X Y Z W…
-/
lemma of_retract {P : MorphismProperty C} [P.IsStableUnderRetracts]
    {X Y Z W : C} {f : X ⟶ Y} {g : Z ⟶ W} (h : RetractArrow f g) (hg : P g) : P f :=
  IsStableUnderRetracts.of_retract h hg
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {D : Type*} [Category* D] (F : C ⥤ D) (P : MorphismProperty D)
    [P.IsStableUnderRetracts] :
    (P.inverseImage F).IsStableUnderRetracts where
  of_retract h₁ h₂ := of_retract (P := P) (h₁.map F) h₂

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.MorphismProperty.IsStableUnderRetracts.monomorphisms** 是 Mathli
b 中的一个定理，位于命名空间 `CategoryTheory.MorphismProperty.IsStableUnderRetracts`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C],   (CategoryTheor
y.MorphismProperty.monomorphisms C).IsStableUnderRetracts
参数：CategoryTheory.MorphismProperty.monomorphisms C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.IsSplitMono.mono`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {X Y : C} (f : Y ⟶ X) [hf : CategoryTheory.IsSplitMono f], 
  CategoryTheory.Mono…
· 使用定理 `CategoryTheory.Retract.instIsSplitMonoI`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {X Y : C} (h : CategoryTheory.Retract X Y),   Category
Theory.IsSplitMono h.i
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.RetractArrow.i_w`：∀ {C : Type u} [inst : CategoryTheory.C
ategory.{v, u} C] {X Y Z W : C} {f : X ⟶ Y} {g : Z ⟶ W}   (h : CategoryTheory.Re
tractArrow f g),   Ca…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Mathlib.Tactic.Reassoc.eq_whisker'`：eq_whisker' {C : Type*} [Category* C
] {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) : f ≫ h = g ≫ h
-/
instance IsStableUnderRetracts.monomorphisms : (monomorphisms C).IsStableUnderRetracts where
  of_retract {_ _ _ _ f g} h (hg : Mono g) := ⟨fun α β w ↦ by
    rw [← cancel_mono h.i.left, ← cancel_mono g, Category.assoc, Category.assoc,
      h.i_w, reassoc_of% w]⟩

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.MorphismProperty.IsStableUnderRetracts.epimorphisms** 是 Mathlib
 中的一个定理，位于命名空间 `CategoryTheory.MorphismProperty.IsStableUnderRetracts`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C],   (CategoryTheor
y.MorphismProperty.epimorphisms C).IsStableUnderRetracts
参数：CategoryTheory.MorphismProperty.epimorphisms C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.Arrow.epi_right`：∀ {T : Type u} [inst : CategoryTheory.Ca
tegory.{v, u} T] {f g : CategoryTheory.Arrow T} (sq : g ⟶ f)   [CategoryTheory.E
pi sq], CategoryTheo…
· 使用定理 `CategoryTheory.IsSplitEpi.epi`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [hf : CategoryTheory.IsSplitEpi f],   C
ategoryTheory.Epi f
· 使用定理 `CategoryTheory.Retract.instIsSplitEpiR`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {X Y : C} (h : CategoryTheory.Retract X Y),   CategoryT
heory.IsSplitEpi h.r
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.RetractArrow.r_w`：∀ {C : Type u} [inst : CategoryTheory.C
ategory.{v, u} C] {X Y Z W : C} {f : X ⟶ Y} {g : Z ⟶ W}   (h : CategoryTheory.Re
tractArrow f g),   Ca…
-/
instance IsStableUnderRetracts.epimorphisms : (epimorphisms C).IsStableUnderRetracts where
  of_retract {_ _ _ _ f g} h (hg : Epi g) := ⟨fun α β w ↦ by
    rw [← cancel_epi h.r.right, ← cancel_epi g, ← Category.assoc, ← Category.assoc, ← h.r_w,
      Category.assoc, Category.assoc, w]⟩

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.MorphismProperty.IsStableUnderRetracts.isomorphisms** 是 Mathlib
 中的一个定理，位于命名空间 `CategoryTheory.MorphismProperty.IsStableUnderRetracts`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C],   (CategoryTheor
y.MorphismProperty.isomorphisms C).IsStableUnderRetracts
参数：CategoryTheory.MorphismProperty.isomorphisms C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.RetractArrow.i_w_assoc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y Z W : C} {f : X ⟶ Y} {g : Z ⟶ W}   (h : CategoryThe
ory.RetractArrow f g) {Z_1 …
· 使用定理 `CategoryTheory.IsIso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y) [I : CategoryTheory.IsIso f] {Z : 
C}   (h : X ⟶ Z), CategoryT…
· 使用定理 `CategoryTheory.RetractArrow.retract_left`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z W : C} {f : X ⟶ Y} {g : Z ⟶ W}   (h : Category
Theory.RetractArrow f g),   Ca…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.RetractArrow.r_w`：∀ {C : Type u} [inst : CategoryTheory.C
ategory.{v, u} C] {X Y Z W : C} {f : X ⟶ Y} {g : Z ⟶ W}   (h : CategoryTheory.Re
tractArrow f g),   Ca…
· 使用定理 `CategoryTheory.IsIso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y) [I : CategoryTheory.IsIso f] {Z : 
C}   (h : Y ⟶ Z), CategoryT…
· 使用定理 `CategoryTheory.RetractArrow.retract_right`：∀ {C : Type u} [inst : Catego
ryTheory.Category.{v, u} C] {X Y Z W : C} {f : Y ⟶ X} {g : W ⟶ Z}   (h : Categor
yTheory.RetractArrow f g),   Ca…
-/
instance IsStableUnderRetracts.isomorphisms : (isomorphisms C).IsStableUnderRetracts where
  of_retract {X Y Z W f g} h (_ : IsIso _) := by
    refine ⟨h.i.right ≫ inv g ≫ h.r.left, ?_, ?_⟩
    · rw [← h.i_w_assoc, IsIso.hom_inv_id_assoc, h.retract_left]
    · rw [Category.assoc, Category.assoc, h.r_w, IsIso.inv_hom_id_assoc, h.retract_right]
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (P : MorphismProperty C) [P.IsStableUnderRetracts] :
    P.op.IsStableUnderRetracts where
  of_retract h₁ h₂ := P.of_retract h₁.unop h₂
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (P : MorphismProperty Cᵒᵖ) [P.IsStableUnderRetracts] :
    P.unop.IsStableUnderRetracts where
  of_retract h₁ h₂ := P.of_retract h₁.op h₂
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (P₁ P₂ : MorphismProperty C)
    [P₁.IsStableUnderRetracts] [P₂.IsStableUnderRetracts] :
    (P₁ ⊓ P₂).IsStableUnderRetracts where
  of_retract := fun h ⟨h₁, h₂⟩ ↦ ⟨of_retract h h₁, of_retract h h₂⟩

/-- The class of morphisms that are retracts of morphisms
belonging to `P : MorphismProperty C`. -/
/-
**CategoryTheory.MorphismProperty.retracts** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.MorphismProperty`。
形式化陈述：retracts (P : MorphismProperty C) : MorphismProperty C
参数：P : MorphismProperty C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The class of morphisms that are retracts of morphisms
belonging to `P : MorphismProperty C`.
-/
def retracts (P : MorphismProperty C) : MorphismProperty C :=
  fun _ _ f ↦ ∃ (Z W : C) (g : Z ⟶ W) (_ : RetractArrow f g), P g
/-
**CategoryTheory.MorphismProperty.le_retracts** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.MorphismProperty`。
形式化陈述：le_retracts (P : MorphismProperty C) : P <= P.retracts
参数：P : MorphismProperty C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma le_retracts (P : MorphismProperty C) : P ≤ P.retracts := by
  intro X Y f hf
  exact ⟨_, _, f, { i := 𝟙 _, r := 𝟙 _}, hf⟩
/-
**CategoryTheory.MorphismProperty.retracts_monotone** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.MorphismProperty`。
形式化陈述：retracts_monotone : Monotone (retracts (C
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma retracts_monotone : Monotone (retracts (C := C)) := by
  intro _ _ h _ _ _ ⟨_, _, _, hg, hg'⟩
  exact ⟨_, _, _, hg, h _ hg'⟩
/-
**CategoryTheory.MorphismProperty.isStableUnderRetracts_iff_retracts_le** 是 Math
lib 中的一个引理，位于命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：isStableUnderRetracts_iff_retracts_le (P : MorphismProperty C) : P.IsStabl
eUnderRetracts ↔ P.retracts <= P
参数：P : MorphismProperty C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MorphismProperty.isStableUnderRetracts_iff`：∀ {C : Type u
} [inst : CategoryTheory.Category.{v, u} C] (P : CategoryTheory.MorphismProperty
 C),   P.IsStableUnderRetracts ↔ ∀ {X Y Z W : C…
-/
lemma isStableUnderRetracts_iff_retracts_le (P : MorphismProperty C) :
    P.IsStableUnderRetracts ↔ P.retracts ≤ P := by
  rw [isStableUnderRetracts_iff]
  constructor
  · intro h₁ X Y f ⟨_, _, _, h₂, h₃⟩
    exact h₁ h₂ h₃
  · intro h₁ _ _ _ _ _ _ h₂ h₃
    exact h₁ _ ⟨_, _, _, h₂, h₃⟩
/-
**CategoryTheory.MorphismProperty.retracts_le** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.MorphismProperty`。
形式化陈述：retracts_le (P : MorphismProperty C) [P.IsStableUnderRetracts] : P.retract
s <= P
参数：P : MorphismProperty C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.MorphismProperty.isStableUnderRetracts_iff_retracts_le`：i
sStableUnderRetracts_iff_retracts_le (P : MorphismProperty C) : P.IsStableUnderR
etracts ↔ P.retracts <= P
-/
lemma retracts_le (P : MorphismProperty C) [P.IsStableUnderRetracts] :
    P.retracts ≤ P := by
  rwa [← isStableUnderRetracts_iff_retracts_le]

@[simp]
/-
**CategoryTheory.MorphismProperty.retracts_le_iff** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.MorphismProperty`。
形式化陈述：retracts_le_iff {P Q : MorphismProperty C} [Q.IsStableUnderRetracts] : P.r
etracts <= Q ↔ P <= Q
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用引理 `CategoryTheory.MorphismProperty.le_retracts`：le_retracts (P : MorphismPr
operty C) : P <= P.retracts
· 使用引理 `CategoryTheory.MorphismProperty.retracts_monotone`：retracts_monotone : M
onotone (retracts (C
· 使用引理 `CategoryTheory.MorphismProperty.retracts_le`：retracts_le (P : MorphismPr
operty C) [P.IsStableUnderRetracts] : P.retracts <= P
-/
lemma retracts_le_iff {P Q : MorphismProperty C} [Q.IsStableUnderRetracts] :
    P.retracts ≤ Q ↔ P ≤ Q := by
  constructor
  · exact le_trans P.le_retracts
  · intro h
    exact le_trans (retracts_monotone h) Q.retracts_le
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {P : MorphismProperty C} [P.IsStableUnderRetracts] :
    P.RespectsIso :=
  RespectsIso.of_respects_arrow_iso _
    (fun _ _ e ↦ of_retract (Retract.ofIso e.symm))

end MorphismProperty

end CategoryTheory

