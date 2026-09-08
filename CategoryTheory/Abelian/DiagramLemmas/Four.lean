/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Joël Riou
-/
module

public import Mathlib.Algebra.Homology.ExactSequence
public import Mathlib.CategoryTheory.Abelian.Refinements

/-!
# The four and five lemmas

Consider the following commutative diagram with exact rows in an abelian category `C`:

```
A ---f--> B ---g--> C ---h--> D ---i--> E
|         |         |         |         |
α         β         γ         δ         ε
|         |         |         |         |
v         v         v         v         v
A' --f'-> B' --g'-> C' --h'-> D' --i'-> E'
```

We show:
- the "mono" version of the four lemma: if `α` is an epimorphism and `β` and `δ` are monomorphisms,
  then `γ` is a monomorphism,
- the "epi" version of the four lemma: if `β` and `δ` are epimorphisms and `ε` is a monomorphism,
  then `γ` is an epimorphism,
- the five lemma: if `α`, `β`, `δ` and `ε` are isomorphisms, then `γ` is an isomorphism.

## Implementation details

The diagram of the five lemma is given by a morphism in the category `ComposableArrows C 4`
between two objects which satisfy `ComposableArrows.Exact`. Similarly, the two versions of the
four lemma are stated in terms of the category `ComposableArrows C 3`.

The five lemma is deduced from the two versions of the four lemma. Both of these versions
are proved separately. It would be easy to deduce the epi version from the mono version
using duality, but this would require lengthy API developments for `ComposableArrows` (TODO).

## Tags

four lemma, five lemma, diagram lemma, diagram chase
-/

public section


namespace CategoryTheory

open Category Limits Preadditive

namespace Abelian

variable {C : Type*} [Category* C] [Abelian C]

open ComposableArrows

section Four

variable {R₁ R₂ : ComposableArrows C 3} (φ : R₁ ⟶ R₂)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Abelian.mono_of_epi_of_mono_of_mono'** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.Abelian`。
形式化陈述：mono_of_epi_of_mono_of_mono' (hR₁ : R₁.map' 0 2 = 0) (hR₁' : (mk₂ (R₁.map'
 1 2) (R₁.map' 2 3)).Exact) (hR₂ : (mk₂ (R₂.map' 0 1) (R₂.map' 1 2)).Exact) (h₀ 
: Epi (app' φ 0)) (h₁ : Mono (app' φ 1)) (h₃ : Mono (app' φ 3)) : Mono (app' φ 2
)
参数：hR₁ : R₁.map' 0 2 = 0；hR₁' : (mk₂ (R₁.map' 1 2) (R₁.map' 2 3)).Exact；hR₂ : (m
k₂ (R₂.map' 0 1) (R₂.map' 1 2)).Exact；h₀ : Epi (app' φ 0)；h₁ : Mono (app' φ 1)；h
₃ : Mono (app' φ 3)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Preadditive.mono_of_cancel_zero`：mono_of_cancel_zero {Q R
 : C} (f : Q ⟶ R) (h : forall {P : C} (g : P ⟶ Q), g ≫ f = 0 -> g = 0) : Mono f 
where right_cancellation
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Mathlib.Tactic.Reassoc.eq_whisker'`：eq_whisker' {C : Type*} [Category* C
] {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) : f ≫ h = g ≫ h
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.ComposableArrows.Exact.toIsComplex`：∀ {C : Type u_1} [ins
t : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZer
oMorphisms C]   {n : ℕ} {S : CategoryTh…
· 使用定理 `CategoryTheory.ShortComplex.Exact.exact_up_to_refinements`：∀ {C : Type u
_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Abeli
an C]   {S : CategoryTheory.ShortComplex C},   …
· 使用定理 `CategoryTheory.ComposableArrows.Exact.exact`：∀ {C : Type u_1} [inst : Ca
tegoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorph
isms C]   {n : ℕ} {S : CategoryTh…
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用引理 `CategoryTheory.surjective_up_to_refinements_of_epi`：surjective_up_to_ref
inements_of_epi (f : X ⟶ Y) [Epi f] {A : C} (y : A ⟶ Y) : exists (A' : C) (π : A
' ⟶ A) (_ : Epi π) (x : A' ⟶ X), π ≫ y =…
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.ComposableArrows.map'_comp`：∀ {C : Type u_1} [inst : Cate
goryTheory.Category.{v_1, u_1} C] {n : ℕ} (F : CategoryTheory.ComposableArrows C
 n)   (i j k : ℕ) (hij : autoPa…
-/
theorem mono_of_epi_of_mono_of_mono' (hR₁ : R₁.map' 0 2 = 0)
    (hR₁' : (mk₂ (R₁.map' 1 2) (R₁.map' 2 3)).Exact)
    (hR₂ : (mk₂ (R₂.map' 0 1) (R₂.map' 1 2)).Exact)
    (h₀ : Epi (app' φ 0)) (h₁ : Mono (app' φ 1)) (h₃ : Mono (app' φ 3)) :
    Mono (app' φ 2) := by
  apply mono_of_cancel_zero
  intro A f₂ h₁
  have h₂ : f₂ ≫ R₁.map' 2 3 = 0 := by
    rw [← cancel_mono (app' φ 3 _), assoc, NatTrans.naturality, reassoc_of% h₁,
      zero_comp, zero_comp]
  obtain ⟨A₁, π₁, _, f₁, hf₁⟩ := (hR₁'.exact 0).exact_up_to_refinements f₂ h₂
  dsimp at hf₁
  have h₃ : (f₁ ≫ app' φ 1) ≫ R₂.map' 1 2 = 0 := by
    rw [assoc, ← NatTrans.naturality, ← reassoc_of% hf₁, h₁, comp_zero]
  obtain ⟨A₂, π₂, _, g₀, hg₀⟩ := (hR₂.exact 0).exact_up_to_refinements _ h₃
  obtain ⟨A₃, π₃, _, f₀, hf₀⟩ := surjective_up_to_refinements_of_epi (app' φ 0 _) g₀
  have h₄ : f₀ ≫ R₁.map' 0 1 = π₃ ≫ π₂ ≫ f₁ := by
    rw [← cancel_mono (app' φ 1 _), assoc, assoc, assoc, NatTrans.naturality,
      ← reassoc_of% hf₀, hg₀]
    rfl
  rw [← cancel_epi π₁, comp_zero, hf₁, ← cancel_epi π₂, ← cancel_epi π₃, comp_zero,
    comp_zero, ← reassoc_of% h₄, ← R₁.map'_comp 0 1 2, hR₁, comp_zero]
/-
**CategoryTheory.Abelian.mono_of_epi_of_mono_of_mono** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.Abelian`。
形式化陈述：mono_of_epi_of_mono_of_mono (hR₁ : R₁.Exact) (hR₂ : R₂.Exact) (h₀ : Epi (a
pp' φ 0)) (h₁ : Mono (app' φ 1)) (h₃ : Mono (app' φ 3)) : Mono (app' φ 2)
参数：hR₁ : R₁.Exact；hR₂ : R₂.Exact；h₀ : Epi (app' φ 0)；h₁ : Mono (app' φ 1)；h₃ : M
ono (app' φ 3)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.mono_of_epi_of_mono_of_mono'`：mono_of_epi_of_mono
_of_mono' (hR₁ : R₁.map' 0 2 = 0) (hR₁' : (mk₂ (R₁.map' 1 2) (R₁.map' 2 3)).Exac
t) (hR₂ : (mk₂ (R₂.map' 0 1) (R₂.map' 1 2…
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ComposableArrows.map'_comp`：∀ {C : Type u_1} [inst : Cate
goryTheory.Category.{v_1, u_1} C] {n : ℕ} (F : CategoryTheory.ComposableArrows C
 n)   (i j k : ℕ) (hij : autoPa…
· 使用定理 `CategoryTheory.ComposableArrows.IsComplex.zero`：∀ {C : Type u_1} [inst :
 CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMo
rphisms C]   {n : ℕ} {S : CategoryTh…
· 使用定理 `CategoryTheory.ComposableArrows.Exact.toIsComplex`：∀ {C : Type u_1} [ins
t : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZer
oMorphisms C]   {n : ℕ} {S : CategoryTh…
· 使用定理 `CategoryTheory.ShortComplex.Exact.exact_toComposableArrows`：∀ {C : Type 
u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limi
ts.HasZeroMorphisms C]   {S : CategoryTheory.Sho…
· 使用定理 `CategoryTheory.ComposableArrows.Exact.exact`：∀ {C : Type u_1} [inst : Ca
tegoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorph
isms C]   {n : ℕ} {S : CategoryTh…
-/
theorem mono_of_epi_of_mono_of_mono (hR₁ : R₁.Exact) (hR₂ : R₂.Exact)
    (h₀ : Epi (app' φ 0)) (h₁ : Mono (app' φ 1)) (h₃ : Mono (app' φ 3)) :
    Mono (app' φ 2) :=
  mono_of_epi_of_mono_of_mono' φ
    (by simpa only [R₁.map'_comp 0 1 2] using hR₁.toIsComplex.zero 0)
    (hR₁.exact 1).exact_toComposableArrows (hR₂.exact 0).exact_toComposableArrows h₀ h₁ h₃

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Abelian.epi_of_epi_of_epi_of_mono'** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.Abelian`。
形式化陈述：epi_of_epi_of_epi_of_mono' (hR₁ : (mk₂ (R₁.map' 1 2) (R₁.map' 2 3)).Exact)
 (hR₂ : (mk₂ (R₂.map' 0 1) (R₂.map' 1 2)).Exact) (hR₂' : R₂.map' 1 3 = 0) (h₀ : 
Epi (app' φ 0)) (h₂ : Epi (app' φ 2)) (h₃ : Mono (app' φ 3)) : Epi (app' φ 1)
参数：hR₁ : (mk₂ (R₁.map' 1 2) (R₁.map' 2 3)).Exact；hR₂ : (mk₂ (R₂.map' 0 1) (R₂.ma
p' 1 2)).Exact；hR₂' : R₂.map' 1 3 = 0；h₀ : Epi (app' φ 0)；h₂ : Epi (app' φ 2)；h₃
 : Mono (app' φ 3)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.epi_iff_surjective_up_to_refinements`：epi_iff_surjective_
up_to_refinements (f : X ⟶ Y) : Epi f ↔ forall ⦃A : C⦄ (y : A ⟶ Y), exists (A' :
 C) (π : A' ⟶ A) (_ : Epi π) (x : A' ⟶ X)…
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用引理 `CategoryTheory.surjective_up_to_refinements_of_epi`：surjective_up_to_ref
inements_of_epi (f : X ⟶ Y) [Epi f] {A : C} (y : A ⟶ Y) : exists (A' : C) (π : A
' ⟶ A) (_ : Epi π) (x : A' ⟶ X), π ≫ y =…
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Reassoc.eq_whisker'`：eq_whisker' {C : Type*} [Category* C
] {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) : f ≫ h = g ≫ h
· 使用定理 `CategoryTheory.ComposableArrows.map'_comp`：∀ {C : Type u_1} [inst : Cate
goryTheory.Category.{v_1, u_1} C] {n : ℕ} (F : CategoryTheory.ComposableArrows C
 n)   (i j k : ℕ) (hij : autoPa…
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.ComposableArrows.Exact.toIsComplex`：∀ {C : Type u_1} [ins
t : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZer
oMorphisms C]   {n : ℕ} {S : CategoryTh…
· 使用定理 `CategoryTheory.ShortComplex.Exact.exact_up_to_refinements`：∀ {C : Type u
_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Abeli
an C]   {S : CategoryTheory.ShortComplex C},   …
· 使用定理 `CategoryTheory.ComposableArrows.Exact.exact`：∀ {C : Type u_1} [inst : Ca
tegoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorph
isms C]   {n : ℕ} {S : CategoryTh…
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `CategoryTheory.Preadditive.sub_comp`：sub_comp : (f - f') ≫ g = f ≫ g - f
' ≫ g
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `CategoryTheory.Preadditive.add_comp`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C)   (f f' 
: P ⟶ Q) (g : Q ⟶ R),   C…
· 使用定理 `CategoryTheory.Preadditive.comp_sub`：comp_sub : f ≫ (g - g') = f ≫ g - f
 ≫ g'
· 使用定理 `add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a + 
(b - a) = b
-/
theorem epi_of_epi_of_epi_of_mono'
    (hR₁ : (mk₂ (R₁.map' 1 2) (R₁.map' 2 3)).Exact)
    (hR₂ : (mk₂ (R₂.map' 0 1) (R₂.map' 1 2)).Exact) (hR₂' : R₂.map' 1 3 = 0)
    (h₀ : Epi (app' φ 0)) (h₂ : Epi (app' φ 2)) (h₃ : Mono (app' φ 3)) :
    Epi (app' φ 1) := by
  rw [epi_iff_surjective_up_to_refinements]
  intro A g₁
  obtain ⟨A₁, π₁, _, f₂, h₁⟩ :=
    surjective_up_to_refinements_of_epi (app' φ 2 _) (g₁ ≫ R₂.map' 1 2)
  have h₂ : f₂ ≫ R₁.map' 2 3 = 0 := by
    rw [← cancel_mono (app' φ 3 _), assoc, zero_comp, NatTrans.naturality, ← reassoc_of% h₁,
      ← R₂.map'_comp 1 2 3, hR₂', comp_zero, comp_zero]
  obtain ⟨A₂, π₂, _, f₁, h₃⟩ := (hR₁.exact 0).exact_up_to_refinements _ h₂
  dsimp at f₁ h₃
  have h₄ : (π₂ ≫ π₁ ≫ g₁ - f₁ ≫ app' φ 1 _) ≫ R₂.map' 1 2 = 0 := by
    rw [sub_comp, assoc, assoc, assoc, ← NatTrans.naturality, ← reassoc_of% h₃, h₁, sub_self]
  obtain ⟨A₃, π₃, _, g₀, h₅⟩ := (hR₂.exact 0).exact_up_to_refinements _ h₄
  dsimp at g₀ h₅
  rw [comp_sub] at h₅
  obtain ⟨A₄, π₄, _, f₀, h₆⟩ := surjective_up_to_refinements_of_epi (app' φ 0 _) g₀
  refine ⟨A₄, π₄ ≫ π₃ ≫ π₂ ≫ π₁, inferInstance,
    π₄ ≫ π₃ ≫ f₁ + f₀ ≫ (by exact R₁.map' 0 1), ?_⟩
  rw [assoc, assoc, assoc, add_comp, assoc, assoc, assoc, NatTrans.naturality,
    ← reassoc_of% h₆, ← h₅, comp_sub]
  dsimp
  rw [add_sub_cancel]
/-
**CategoryTheory.Abelian.epi_of_epi_of_epi_of_mono** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Abelian`。
形式化陈述：epi_of_epi_of_epi_of_mono (hR₁ : R₁.Exact) (hR₂ : R₂.Exact) (h₀ : Epi (app
' φ 0)) (h₂ : Epi (app' φ 2)) (h₃ : Mono (app' φ 3)) : Epi (app' φ 1)
参数：hR₁ : R₁.Exact；hR₂ : R₂.Exact；h₀ : Epi (app' φ 0)；h₂ : Epi (app' φ 2)；h₃ : Mo
no (app' φ 3)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.epi_of_epi_of_epi_of_mono'`：epi_of_epi_of_epi_of_
mono' (hR₁ : (mk₂ (R₁.map' 1 2) (R₁.map' 2 3)).Exact) (hR₂ : (mk₂ (R₂.map' 0 1) 
(R₂.map' 1 2)).Exact) (hR₂' : R₂.map' 1…
· 使用定理 `CategoryTheory.ShortComplex.Exact.exact_toComposableArrows`：∀ {C : Type 
u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limi
ts.HasZeroMorphisms C]   {S : CategoryTheory.Sho…
· 使用定理 `CategoryTheory.ComposableArrows.Exact.toIsComplex`：∀ {C : Type u_1} [ins
t : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZer
oMorphisms C]   {n : ℕ} {S : CategoryTh…
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `CategoryTheory.ComposableArrows.Exact.exact`：∀ {C : Type u_1} [inst : Ca
tegoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorph
isms C]   {n : ℕ} {S : CategoryTh…
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ComposableArrows.map'_comp`：∀ {C : Type u_1} [inst : Cate
goryTheory.Category.{v_1, u_1} C] {n : ℕ} (F : CategoryTheory.ComposableArrows C
 n)   (i j k : ℕ) (hij : autoPa…
· 使用定理 `CategoryTheory.ComposableArrows.IsComplex.zero`：∀ {C : Type u_1} [inst :
 CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMo
rphisms C]   {n : ℕ} {S : CategoryTh…
-/
theorem epi_of_epi_of_epi_of_mono (hR₁ : R₁.Exact) (hR₂ : R₂.Exact)
    (h₀ : Epi (app' φ 0)) (h₂ : Epi (app' φ 2)) (h₃ : Mono (app' φ 3)) :
    Epi (app' φ 1) :=
  epi_of_epi_of_epi_of_mono' φ (hR₁.exact 1).exact_toComposableArrows
    (hR₂.exact 0).exact_toComposableArrows
    (by simpa only [R₂.map'_comp 1 2 3] using hR₂.toIsComplex.zero 1) h₀ h₂ h₃

end Four

section Five

variable {R₁ R₂ : ComposableArrows C 4} (hR₁ : R₁.Exact) (hR₂ : R₂.Exact) (φ : R₁ ⟶ R₂)
include hR₁ hR₂

set_option backward.defeqAttrib.useBackward true in
/-- The five lemma. -/
/-
**CategoryTheory.Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono** 是 Mathlib 中的一个
定理，位于命名空间 `CategoryTheory.Abelian`。
形式化陈述：isIso_of_epi_of_isIso_of_isIso_of_mono (h₀ : Epi (app' φ 0)) (h₁ : IsIso (
app' φ 1)) (h₃ : IsIso (app' φ 3)) (h₄ : Mono (app' φ 4)) : IsIso (app' φ 2)
参数：h₀ : Epi (app' φ 0)；h₁ : IsIso (app' φ 1)；h₃ : IsIso (app' φ 3)；h₄ : Mono (ap
p' φ 4)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `CategoryTheory.Abelian.mono_of_epi_of_mono_of_mono`：mono_of_epi_of_mono_
of_mono (hR₁ : R₁.Exact) (hR₂ : R₂.Exact) (h₀ : Epi (app' φ 0)) (h₁ : Mono (app'
 φ 1)) (h₃ : Mono (app' φ 3)) : Mono (ap…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `CategoryTheory.ComposableArrows.exact_iff_δlast`：exact_iff_δlast {n : Na
t} (S : ComposableArrows C (n + 2)) : S.Exact ↔ S.δlast.Exact ∧ (mk₂ (S.map' n (
n + 1)) (S.map' (n + 1) (n + 2))).Exa…
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.instStrongMonoOfIsRegularMono`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsRegula
rMono f],   CategoryTheory.StrongM…
· 使用定理 `CategoryTheory.instIsRegularMonoOfIsSplitMono`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsSplit
Mono f],   CategoryTheory.IsRegular…
· 使用定理 `CategoryTheory.IsSplitMono.of_iso`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {X Y : C} (f : Y ⟶ X) [CategoryTheory.IsIso f],   Categor
yTheory.IsSplitMono f
· 使用定理 `CategoryTheory.Abelian.epi_of_epi_of_epi_of_mono`：epi_of_epi_of_epi_of_m
ono (hR₁ : R₁.Exact) (hR₂ : R₂.Exact) (h₀ : Epi (app' φ 0)) (h₂ : Epi (app' φ 2)
) (h₃ : Mono (app' φ 3)) : Epi (app' φ…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `CategoryTheory.ComposableArrows.exact_iff_δ₀`：exact_iff_δ₀ (S : Composab
leArrows C (n + 2)) : S.Exact ↔ (mk₂ (S.map' 0 1) (S.map' 1 2)).Exact ∧ S.δ₀.Exa
ct
· 使用定理 `CategoryTheory.instEffectiveEpiOfIsIso`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],  
 CategoryTheory.EffectiveEpi…
· 使用定理 `CategoryTheory.isIso_of_mono_of_epi`：isIso_of_mono_of_epi [Balanced C] {
X Y : C} (f : X ⟶ Y) [Mono f] [Epi f] : IsIso f
· 使用定理 `CategoryTheory.balanced_of_strongMonoCategory`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] [CategoryTheory.StrongMonoCategory C],   Categor
yTheory.Balanced C
· 使用定理 `CategoryTheory.strongMonoCategory_of_regularMonoCategory`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] [CategoryTheory.IsRegularMonoCateg
ory C],   CategoryTheory.StrongMonoCategory C
· 使用定理 `CategoryTheory.regularMonoCategoryOfNormalMonoCategory`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Limits.HasZ
eroMorphisms C]   [CategoryTheory.IsNormalMo…
· 使用定理 `CategoryTheory.Abelian.toIsNormalMonoCategory`：∀ {C : Type u} {inst : Ca
tegoryTheory.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryThe
ory.IsNormalMonoCategory C

--- 原说明 ---
The five lemma.
-/
theorem isIso_of_epi_of_isIso_of_isIso_of_mono (h₀ : Epi (app' φ 0)) (h₁ : IsIso (app' φ 1))
    (h₃ : IsIso (app' φ 3)) (h₄ : Mono (app' φ 4)) : IsIso (app' φ 2) := by
  dsimp at h₀ h₁ h₃ h₄
  have : Mono (app' φ 2) := by
    apply mono_of_epi_of_mono_of_mono (δlastFunctor.map φ) (R₁.exact_iff_δlast.1 hR₁).1
      (R₂.exact_iff_δlast.1 hR₂).1 <;> dsimp <;> infer_instance
  have : Epi (app' φ 2) := by
    apply epi_of_epi_of_epi_of_mono (δ₀Functor.map φ) (R₁.exact_iff_δ₀.1 hR₁).2
      (R₂.exact_iff_δ₀.1 hR₂).2 <;> dsimp <;> infer_instance
  apply isIso_of_mono_of_epi

end Five

section Four

variable {n k : ℕ} (h : k + 3 ≤ n) {R₁ R₂ : ComposableArrows C n}
    (hR₁ : R₁.Exact) (hR₂ : R₂.Exact) (φ : R₁ ⟶ R₂)

include hR₁ hR₂ in
/-- Variant of the first 4-lemma for complexes of any size -/
/-
**CategoryTheory.Abelian.mono_of_epi_of_mono_of_mono''** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.Abelian`。
形式化陈述：mono_of_epi_of_mono_of_mono'' (k₀ k₁ k₂ k₃ : Nat) (hk₀ : k₀ = k) (hk₁ : k₁
 = k + 1) (hk₂ : k₂ = k + 2) (hk₃ : k₃ = k + 3) (h₀ : Epi (app' φ k₀)) (h₁ : Mon
o (app' φ k₁)) (h₃ : Mono (app' φ k₃)) : Mono (app' φ k₂)
参数：k₀ k₁ k₂ k₃ : Nat；hk₀ : k₀ = k；hk₁ : k₁ = k + 1；hk₂ : k₂ = k + 2；hk₃ : k₃ = k
 + 3；h₀ : Epi (app' φ k₀)；h₁ : Mono (app' φ k₁)；h₃ : Mono (app' φ k₃)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ComposableArrows.natAddLEFunctor_app'`：natAddLEFunctor_ap
p' {n k l i : Nat} (h : k + l <= n) {R₁ R₂ : ComposableArrows C n} (φ : R₁ ⟶ R₂)
 (_ : i <= l
· 使用定理 `CategoryTheory.Abelian.mono_of_epi_of_mono_of_mono`：mono_of_epi_of_mono_
of_mono (hR₁ : R₁.Exact) (hR₂ : R₂.Exact) (h₀ : Epi (app' φ 0)) (h₁ : Mono (app'
 φ 1)) (h₃ : Mono (app' φ 3)) : Mono (ap…
· 使用定理 `CategoryTheory.ComposableArrows.natAddLEFunctor_obj_exact`：natAddLEFunct
or_obj_exact {n k l : Nat} (h : k + l <= n) {R : ComposableArrows C n} (hR : R.E
xact) : ((natAddLEFunctor h).obj R).Exact

--- 原说明 ---
Variant of the first 4-lemma for complexes of any size
-/
theorem mono_of_epi_of_mono_of_mono'' (k₀ k₁ k₂ k₃ : ℕ)
    (hk₀ : k₀ = k) (hk₁ : k₁ = k + 1)
    (hk₂ : k₂ = k + 2) (hk₃ : k₃ = k + 3)
    (h₀ : Epi (app' φ k₀)) (h₁ : Mono (app' φ k₁))
    (h₃ : Mono (app' φ k₃)) : Mono (app' φ k₂) := by
  subst_vars
  change Epi (app' φ (k₀ + 0)) at h₀
  rw [← natAddLEFunctor_app' h] at h₀ h₁ h₃ ⊢
  exact mono_of_epi_of_mono_of_mono _ (natAddLEFunctor_obj_exact h hR₁)
    (natAddLEFunctor_obj_exact h hR₂) h₀ h₁ h₃

include hR₁ hR₂ in
/-- Variant of the second 4-lemma for complexes of any size -/
/-
**CategoryTheory.Abelian.epi_of_epi_of_epi_of_mono''** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.Abelian`。
形式化陈述：epi_of_epi_of_epi_of_mono'' (k₀ k₁ k₂ k₃ : Nat) (hk₀ : k₀ = k) (hk₁ : k₁ =
 k + 1) (hk₂ : k₂ = k + 2) (hk₃ : k₃ = k + 3) (h₀ : Epi (app' φ k₀)) (h₂ : Epi (
app' φ k₂)) (h₃ : Mono (app' φ k₃)) : Epi (app' φ k₁)
参数：k₀ k₁ k₂ k₃ : Nat；hk₀ : k₀ = k；hk₁ : k₁ = k + 1；hk₂ : k₂ = k + 2；hk₃ : k₃ = k
 + 3；h₀ : Epi (app' φ k₀)；h₂ : Epi (app' φ k₂)；h₃ : Mono (app' φ k₃)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ComposableArrows.natAddLEFunctor_app'`：natAddLEFunctor_ap
p' {n k l i : Nat} (h : k + l <= n) {R₁ R₂ : ComposableArrows C n} (φ : R₁ ⟶ R₂)
 (_ : i <= l
· 使用定理 `CategoryTheory.Abelian.epi_of_epi_of_epi_of_mono`：epi_of_epi_of_epi_of_m
ono (hR₁ : R₁.Exact) (hR₂ : R₂.Exact) (h₀ : Epi (app' φ 0)) (h₂ : Epi (app' φ 2)
) (h₃ : Mono (app' φ 3)) : Epi (app' φ…
· 使用定理 `CategoryTheory.ComposableArrows.natAddLEFunctor_obj_exact`：natAddLEFunct
or_obj_exact {n k l : Nat} (h : k + l <= n) {R : ComposableArrows C n} (hR : R.E
xact) : ((natAddLEFunctor h).obj R).Exact

--- 原说明 ---
Variant of the second 4-lemma for complexes of any size
-/
theorem epi_of_epi_of_epi_of_mono'' (k₀ k₁ k₂ k₃ : ℕ)
    (hk₀ : k₀ = k) (hk₁ : k₁ = k + 1)
    (hk₂ : k₂ = k + 2) (hk₃ : k₃ = k + 3)
    (h₀ : Epi (app' φ k₀)) (h₂ : Epi (app' φ k₂))
    (h₃ : Mono (app' φ k₃)) : Epi (app' φ k₁) := by
  subst_vars
  change Epi (app' φ (k₀ + 0)) at h₀
  rw [← natAddLEFunctor_app' h] at h₀ h₂ h₃ ⊢
  exact epi_of_epi_of_epi_of_mono _ (natAddLEFunctor_obj_exact h hR₁)
    (natAddLEFunctor_obj_exact h hR₂) h₀ h₂ h₃

end Four

section Five

variable {n k : ℕ} (h : k + 4 ≤ n) {R₁ R₂ : ComposableArrows C n}
    (hR₁ : R₁.Exact) (hR₂ : R₂.Exact) (φ : R₁ ⟶ R₂)

include hR₁ hR₂ in
/-- Variant of the 5-lemma for complexes of any size -/
/-
**CategoryTheory.Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono'** 是 Mathlib 中的一
个定理，位于命名空间 `CategoryTheory.Abelian`。
形式化陈述：isIso_of_epi_of_isIso_of_isIso_of_mono' (k₀ k₁ k₂ k₃ k₄ : Nat) (hk₀ : k₀ =
 k) (hk₁ : k₁ = k + 1) (hk₂ : k₂ = k + 2) (hk₃ : k₃ = k + 3) (hk₄ : k₄ = k + 4) 
(h₀ : Epi (app' φ k₀)) (h₁ : IsIso (app' φ k₁)) (h₃ : IsIso (app' φ k₃)) (h₄ : M
ono (app' φ k₄)) : IsIso (app' φ k₂)
参数：k₀ k₁ k₂ k₃ k₄ : Nat；hk₀ : k₀ = k；hk₁ : k₁ = k + 1；hk₂ : k₂ = k + 2；hk₃ : k₃ 
= k + 3；hk₄ : k₄ = k + 4；h₀ : Epi (app' φ k₀)；h₁ : IsIso (app' φ k₁)；h₃ : IsIso 
(app' φ k₃)；h₄ : Mono (app' φ k₄)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ComposableArrows.natAddLEFunctor_app'`：natAddLEFunctor_ap
p' {n k l i : Nat} (h : k + l <= n) {R₁ R₂ : ComposableArrows C n} (φ : R₁ ⟶ R₂)
 (_ : i <= l
· 使用定理 `CategoryTheory.Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono`：isIso_of_
epi_of_isIso_of_isIso_of_mono (h₀ : Epi (app' φ 0)) (h₁ : IsIso (app' φ 1)) (h₃ 
: IsIso (app' φ 3)) (h₄ : Mono (app' φ 4)) : IsIso …
· 使用定理 `CategoryTheory.ComposableArrows.natAddLEFunctor_obj_exact`：natAddLEFunct
or_obj_exact {n k l : Nat} (h : k + l <= n) {R : ComposableArrows C n} (hR : R.E
xact) : ((natAddLEFunctor h).obj R).Exact

--- 原说明 ---
Variant of the 5-lemma for complexes of any size
-/
theorem isIso_of_epi_of_isIso_of_isIso_of_mono' (k₀ k₁ k₂ k₃ k₄ : ℕ)
    (hk₀ : k₀ = k) (hk₁ : k₁ = k + 1)
    (hk₂ : k₂ = k + 2) (hk₃ : k₃ = k + 3)
    (hk₄ : k₄ = k + 4) (h₀ : Epi (app' φ k₀))
    (h₁ : IsIso (app' φ k₁)) (h₃ : IsIso (app' φ k₃))
    (h₄ : Mono (app' φ k₄)) :
    IsIso (app' φ k₂) := by
  subst_vars
  change Epi (app' φ (k₀ + 0)) at h₀
  rw [← natAddLEFunctor_app' h] at h₀ h₁ h₃ h₄ ⊢
  exact isIso_of_epi_of_isIso_of_isIso_of_mono (natAddLEFunctor_obj_exact h hR₁)
    (natAddLEFunctor_obj_exact h hR₂) _ h₀ h₁ h₃ h₄

end Five

/-! The following "three lemmas" for morphisms in `ComposableArrows C 2` are
special cases of "four lemmas" applied to diagrams where some of the
leftmost or rightmost maps (or objects) are zero. -/

section Three

variable {R₁ R₂ : ComposableArrows C 2} (φ : R₁ ⟶ R₂)

attribute [local simp] Precomp.map

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Abelian.mono_of_epi_of_epi_mono'** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Abelian`。
形式化陈述：mono_of_epi_of_epi_mono' (hR₁ : R₁.map' 0 2 = 0) (hR₁' : Epi (R₁.map' 1 2)
) (hR₂ : R₂.Exact) (h₀ : Epi (app' φ 0)) (h₁ : Mono (app' φ 1)) : Mono (app' φ 2
)
参数：hR₁ : R₁.map' 0 2 = 0；hR₁' : Epi (R₁.map' 1 2)；hR₂ : R₂.Exact；h₀ : Epi (app' 
φ 0)；h₁ : Mono (app' φ 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用引理 `CategoryTheory.ComposableArrows.naturality'`：naturality' (φ : F ⟶ G) (i 
j : Nat) (hij : i <= j
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Abelian.mono_of_epi_of_mono_of_mono'`：mono_of_epi_of_mono
_of_mono' (hR₁ : R₁.map' 0 2 = 0) (hR₁' : (mk₂ (R₁.map' 1 2) (R₁.map' 2 3)).Exac
t) (hR₂ : (mk₂ (R₂.map' 0 1) (R₂.map' 1 2…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用引理 `CategoryTheory.ComposableArrows.exact₂_mk`：exact₂_mk (S : ComposableArro
ws C 2) (w : S.map' 0 1 ≫ S.map' 1 2 = 0) (h : (ShortComplex.mk _ _ w).Exact) : 
S.Exact
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `CategoryTheory.ShortComplex.exact_iff_epi`：exact_iff_epi [HasZeroObject 
C] (hg : S.g = 0) : S.Exact ↔ Epi S.f
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `CategoryTheory.ShortComplex.Exact.exact_toComposableArrows`：∀ {C : Type 
u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limi
ts.HasZeroMorphisms C]   {S : CategoryTheory.Sho…
· 使用定理 `CategoryTheory.ComposableArrows.Exact.toIsComplex`：∀ {C : Type u_1} [ins
t : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZer
oMorphisms C]   {n : ℕ} {S : CategoryTh…
· 使用定理 `CategoryTheory.ComposableArrows.Exact.exact`：∀ {C : Type u_1} [inst : Ca
tegoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorph
isms C]   {n : ℕ} {S : CategoryTh…
· 使用定理 `CategoryTheory.instMonoId`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] (X : C),   CategoryTheory.Mono (CategoryTheory.CategoryStruct.id X)
-/
theorem mono_of_epi_of_epi_mono' (hR₁ : R₁.map' 0 2 = 0) (hR₁' : Epi (R₁.map' 1 2))
    (hR₂ : R₂.Exact) (h₀ : Epi (app' φ 0)) (h₁ : Mono (app' φ 1)) :
    Mono (app' φ 2) := by
  let ψ : mk₃ (R₁.map' 0 1) (R₁.map' 1 2) (0 : _ ⟶ R₁.obj' 0) ⟶
    mk₃ (R₂.map' 0 1) (R₂.map' 1 2) (0 : _ ⟶ R₁.obj' 0) := homMk₃ (app' φ 0) (app' φ 1)
      (app' φ 2) (𝟙 _) (naturality' φ 0 1) (naturality' φ 1 2) (by simp)
  refine mono_of_epi_of_mono_of_mono' ψ ?_ (exact₂_mk _ (by simp) ?_)
    (hR₂.exact 0).exact_toComposableArrows h₀ h₁ (by dsimp [ψ]; infer_instance)
  · dsimp
    rw [← Functor.map_comp]
    exact hR₁
  · rw [ShortComplex.exact_iff_epi _ (by simp)]
    exact hR₁'
/-
**CategoryTheory.Abelian.mono_of_epi_of_epi_of_mono** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.Abelian`。
形式化陈述：mono_of_epi_of_epi_of_mono (hR₁ : R₁.Exact) (hR₂ : R₂.Exact) (hR₁' : Epi (
R₁.map' 1 2)) (h₀ : Epi (app' φ 0)) (h₁ : Mono (app' φ 1)) : Mono (app' φ 2)
参数：hR₁ : R₁.Exact；hR₂ : R₂.Exact；hR₁' : Epi (R₁.map' 1 2)；h₀ : Epi (app' φ 0)；h₁
 : Mono (app' φ 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.mono_of_epi_of_epi_mono'`：mono_of_epi_of_epi_mono
' (hR₁ : R₁.map' 0 2 = 0) (hR₁' : Epi (R₁.map' 1 2)) (hR₂ : R₂.Exact) (h₀ : Epi 
(app' φ 0)) (h₁ : Mono (app' φ 1)) : …
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ComposableArrows.map'_comp`：∀ {C : Type u_1} [inst : Cate
goryTheory.Category.{v_1, u_1} C] {n : ℕ} (F : CategoryTheory.ComposableArrows C
 n)   (i j k : ℕ) (hij : autoPa…
· 使用定理 `CategoryTheory.ComposableArrows.IsComplex.zero`：∀ {C : Type u_1} [inst :
 CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMo
rphisms C]   {n : ℕ} {S : CategoryTh…
· 使用定理 `CategoryTheory.ComposableArrows.Exact.toIsComplex`：∀ {C : Type u_1} [ins
t : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZer
oMorphisms C]   {n : ℕ} {S : CategoryTh…
-/
theorem mono_of_epi_of_epi_of_mono (hR₁ : R₁.Exact) (hR₂ : R₂.Exact)
    (hR₁' : Epi (R₁.map' 1 2)) (h₀ : Epi (app' φ 0)) (h₁ : Mono (app' φ 1)) :
    Mono (app' φ 2) :=
  mono_of_epi_of_epi_mono' φ (by simpa only [map'_comp R₁ 0 1 2] using hR₁.toIsComplex.zero 0)
    hR₁' hR₂ h₀ h₁

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Abelian.epi_of_mono_of_epi_of_mono'** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.Abelian`。
形式化陈述：epi_of_mono_of_epi_of_mono' (hR₁ : R₁.Exact) (hR₂ : R₂.map' 0 2 = 0) (hR₂'
 : Mono (R₂.map' 0 1)) (h₀ : Epi (app' φ 1)) (h₁ : Mono (app' φ 2)) : Epi (app' 
φ 0)
参数：hR₁ : R₁.Exact；hR₂ : R₂.map' 0 2 = 0；hR₂' : Mono (R₂.map' 0 1)；h₀ : Epi (app'
 φ 1)；h₁ : Mono (app' φ 2)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CategoryTheory.ComposableArrows.naturality'`：naturality' (φ : F ⟶ G) (i 
j : Nat) (hij : i <= j
· 使用定理 `CategoryTheory.Abelian.epi_of_epi_of_epi_of_mono'`：epi_of_epi_of_epi_of_
mono' (hR₁ : (mk₂ (R₁.map' 1 2) (R₁.map' 2 3)).Exact) (hR₂ : (mk₂ (R₂.map' 0 1) 
(R₂.map' 1 2)).Exact) (hR₂' : R₂.map' 1…
· 使用定理 `CategoryTheory.ShortComplex.Exact.exact_toComposableArrows`：∀ {C : Type 
u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limi
ts.HasZeroMorphisms C]   {S : CategoryTheory.Sho…
· 使用定理 `CategoryTheory.ComposableArrows.Exact.toIsComplex`：∀ {C : Type u_1} [ins
t : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZer
oMorphisms C]   {n : ℕ} {S : CategoryTh…
· 使用定理 `CategoryTheory.ComposableArrows.Exact.exact`：∀ {C : Type u_1} [inst : Ca
tegoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorph
isms C]   {n : ℕ} {S : CategoryTh…
· 使用引理 `CategoryTheory.ComposableArrows.exact₂_mk`：exact₂_mk (S : ComposableArro
ws C 2) (w : S.map' 0 1 ≫ S.map' 1 2 = 0) (h : (ShortComplex.mk _ _ w).Exact) : 
S.Exact
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `CategoryTheory.ShortComplex.exact_iff_mono`：exact_iff_mono [HasZeroObjec
t C] (hf : S.f = 0) : S.Exact ↔ Mono S.g
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.instEpiId`：∀ {C : Type u} [inst : CategoryTheory.Category
.{v, u} C] (X : C),   CategoryTheory.Epi (CategoryTheory.CategoryStruct.id X)
-/
theorem epi_of_mono_of_epi_of_mono' (hR₁ : R₁.Exact) (hR₂ : R₂.map' 0 2 = 0)
    (hR₂' : Mono (R₂.map' 0 1)) (h₀ : Epi (app' φ 1)) (h₁ : Mono (app' φ 2)) :
    Epi (app' φ 0) := by
  let ψ : mk₃ (0 : R₁.obj' 0 ⟶ _) (R₁.map' 0 1) (R₁.map' 1 2) ⟶
    mk₃ (0 : R₁.obj' 0 ⟶ _) (R₂.map' 0 1) (R₂.map' 1 2) := homMk₃ (𝟙 _) (app' φ 0) (app' φ 1)
      (app' φ 2) (by simp) (naturality' φ 0 1) (naturality' φ 1 2)
  refine epi_of_epi_of_epi_of_mono' ψ (hR₁.exact 0).exact_toComposableArrows
    (exact₂_mk _ (by simp) ?_) ?_ (by dsimp [ψ]; infer_instance) h₀ h₁
  · rw [ShortComplex.exact_iff_mono _ (by simp)]
    exact hR₂'
  · dsimp
    rw [← Functor.map_comp]
    exact hR₂
/-
**CategoryTheory.Abelian.epi_of_mono_of_epi_of_mono** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.Abelian`。
形式化陈述：epi_of_mono_of_epi_of_mono (hR₁ : R₁.Exact) (hR₂ : R₂.Exact) (hR₂' : Mono 
(R₂.map' 0 1)) (h₀ : Epi (app' φ 1)) (h₁ : Mono (app' φ 2)) : Epi (app' φ 0)
参数：hR₁ : R₁.Exact；hR₂ : R₂.Exact；hR₂' : Mono (R₂.map' 0 1)；h₀ : Epi (app' φ 1)；h
₁ : Mono (app' φ 2)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.epi_of_mono_of_epi_of_mono'`：epi_of_mono_of_epi_o
f_mono' (hR₁ : R₁.Exact) (hR₂ : R₂.map' 0 2 = 0) (hR₂' : Mono (R₂.map' 0 1)) (h₀
 : Epi (app' φ 1)) (h₁ : Mono (app' φ 2)…
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ComposableArrows.map'_comp`：∀ {C : Type u_1} [inst : Cate
goryTheory.Category.{v_1, u_1} C] {n : ℕ} (F : CategoryTheory.ComposableArrows C
 n)   (i j k : ℕ) (hij : autoPa…
· 使用定理 `CategoryTheory.ComposableArrows.IsComplex.zero`：∀ {C : Type u_1} [inst :
 CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMo
rphisms C]   {n : ℕ} {S : CategoryTh…
· 使用定理 `CategoryTheory.ComposableArrows.Exact.toIsComplex`：∀ {C : Type u_1} [ins
t : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZer
oMorphisms C]   {n : ℕ} {S : CategoryTh…
-/
theorem epi_of_mono_of_epi_of_mono (hR₁ : R₁.Exact) (hR₂ : R₂.Exact)
    (hR₂' : Mono (R₂.map' 0 1)) (h₀ : Epi (app' φ 1)) (h₁ : Mono (app' φ 2)) :
    Epi (app' φ 0) :=
  epi_of_mono_of_epi_of_mono' φ hR₁
    (by simpa only [map'_comp R₂ 0 1 2] using hR₂.toIsComplex.zero 0) hR₂' h₀ h₁

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Abelian.mono_of_mono_of_mono_of_mono** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.Abelian`。
形式化陈述：mono_of_mono_of_mono_of_mono (hR₁ : R₁.Exact) (hR₂' : Mono (R₂.map' 0 1)) 
(h₀ : Mono (app' φ 0)) (h₁ : Mono (app' φ 2)) : Mono (app' φ 1)
参数：hR₁ : R₁.Exact；hR₂' : Mono (R₂.map' 0 1)；h₀ : Mono (app' φ 0)；h₁ : Mono (app'
 φ 2)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.ComposableArrows.precomp_map`：∀ {C : Type u_1} [inst : Ca
tegoryTheory.Category.{v_1, u_1} C] {n : ℕ} (F : CategoryTheory.ComposableArrows
 C n) {X : C}   (f : X ⟶ F.left) …
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CategoryTheory.ComposableArrows.naturality'`：naturality' (φ : F ⟶ G) (i 
j : Nat) (hij : i <= j
· 使用定理 `CategoryTheory.Abelian.mono_of_epi_of_mono_of_mono'`：mono_of_epi_of_mono
_of_mono' (hR₁ : R₁.map' 0 2 = 0) (hR₁' : (mk₂ (R₁.map' 1 2) (R₁.map' 2 3)).Exac
t) (hR₂ : (mk₂ (R₂.map' 0 1) (R₂.map' 1 2…
· 使用定理 `CategoryTheory.ShortComplex.Exact.exact_toComposableArrows`：∀ {C : Type 
u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limi
ts.HasZeroMorphisms C]   {S : CategoryTheory.Sho…
· 使用定理 `CategoryTheory.ComposableArrows.Exact.toIsComplex`：∀ {C : Type u_1} [ins
t : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZer
oMorphisms C]   {n : ℕ} {S : CategoryTh…
· 使用定理 `CategoryTheory.ComposableArrows.Exact.exact`：∀ {C : Type u_1} [inst : Ca
tegoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorph
isms C]   {n : ℕ} {S : CategoryTh…
· 使用引理 `CategoryTheory.ComposableArrows.exact₂_mk`：exact₂_mk (S : ComposableArro
ws C 2) (w : S.map' 0 1 ≫ S.map' 1 2 = 0) (h : (ShortComplex.mk _ _ w).Exact) : 
S.Exact
· 使用定理 `CategoryTheory.ComposableArrows.mk₁_map`：∀ {C : Type u_1} [inst : Catego
ryTheory.Category.{v_1, u_1} C] {X₀ X₁ : C} (f : X₀ ⟶ X₁) {X Y : Fin (1 + 1)}   
(g : X ⟶ Y), (CategoryTheory.…
· 使用引理 `CategoryTheory.ShortComplex.exact_iff_mono`：exact_iff_mono [HasZeroObjec
t C] (hf : S.f = 0) : S.Exact ↔ Mono S.g
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `CategoryTheory.instEpiId`：∀ {C : Type u} [inst : CategoryTheory.Category
.{v, u} C] (X : C),   CategoryTheory.Epi (CategoryTheory.CategoryStruct.id X)
-/
theorem mono_of_mono_of_mono_of_mono (hR₁ : R₁.Exact)
    (hR₂' : Mono (R₂.map' 0 1))
    (h₀ : Mono (app' φ 0))
    (h₁ : Mono (app' φ 2)) :
    Mono (app' φ 1) := by
  let ψ : mk₃ (0 : R₁.obj' 0 ⟶ _) (R₁.map' 0 1) (R₁.map' 1 2) ⟶
    mk₃ (0 : R₁.obj' 0 ⟶ _) (R₂.map' 0 1) (R₂.map' 1 2) := homMk₃ (𝟙 _) (app' φ 0) (app' φ 1)
      (app' φ 2) (by simp) (naturality' φ 0 1) (naturality' φ 1 2)
  refine mono_of_epi_of_mono_of_mono' ψ (by simp)
    (hR₁.exact 0).exact_toComposableArrows
    (exact₂_mk _ (by simp) ?_) (by dsimp [ψ]; infer_instance) h₀ h₁
  rw [ShortComplex.exact_iff_mono _ (by simp)]
  exact hR₂'

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Abelian.epi_of_epi_of_epi_of_epi** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Abelian`。
形式化陈述：epi_of_epi_of_epi_of_epi (hR₂ : R₂.Exact) (hR₁' : Epi (R₁.map' 1 2)) (h₀ :
 Epi (app' φ 0)) (h₁ : Epi (app' φ 2)) : Epi (app' φ 1)
参数：hR₂ : R₂.Exact；hR₁' : Epi (R₁.map' 1 2)；h₀ : Epi (app' φ 0)；h₁ : Epi (app' φ 
2)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用引理 `CategoryTheory.ComposableArrows.naturality'`：naturality' (φ : F ⟶ G) (i 
j : Nat) (hij : i <= j
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.ComposableArrows.precomp_map`：∀ {C : Type u_1} [inst : Ca
tegoryTheory.Category.{v_1, u_1} C] {n : ℕ} (F : CategoryTheory.ComposableArrows
 C n) {X : C}   (f : X ⟶ F.left) …
· 使用定理 `CategoryTheory.ComposableArrows.mk₁_map`：∀ {C : Type u_1} [inst : Catego
ryTheory.Category.{v_1, u_1} C] {X₀ X₁ : C} (f : X₀ ⟶ X₁) {X Y : Fin (1 + 1)}   
(g : X ⟶ Y), (CategoryTheory.…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Abelian.epi_of_epi_of_epi_of_mono'`：epi_of_epi_of_epi_of_
mono' (hR₁ : (mk₂ (R₁.map' 1 2) (R₁.map' 2 3)).Exact) (hR₂ : (mk₂ (R₂.map' 0 1) 
(R₂.map' 1 2)).Exact) (hR₂' : R₂.map' 1…
· 使用引理 `CategoryTheory.ComposableArrows.exact₂_mk`：exact₂_mk (S : ComposableArro
ws C 2) (w : S.map' 0 1 ≫ S.map' 1 2 = 0) (h : (ShortComplex.mk _ _ w).Exact) : 
S.Exact
· 使用引理 `CategoryTheory.ShortComplex.exact_iff_epi`：exact_iff_epi [HasZeroObject 
C] (hg : S.g = 0) : S.Exact ↔ Epi S.f
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `CategoryTheory.ShortComplex.Exact.exact_toComposableArrows`：∀ {C : Type 
u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limi
ts.HasZeroMorphisms C]   {S : CategoryTheory.Sho…
· 使用定理 `CategoryTheory.ComposableArrows.Exact.toIsComplex`：∀ {C : Type u_1} [ins
t : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZer
oMorphisms C]   {n : ℕ} {S : CategoryTh…
· 使用定理 `CategoryTheory.ComposableArrows.Exact.exact`：∀ {C : Type u_1} [inst : Ca
tegoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorph
isms C]   {n : ℕ} {S : CategoryTh…
· 使用定理 `CategoryTheory.instMonoId`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] (X : C),   CategoryTheory.Mono (CategoryTheory.CategoryStruct.id X)
-/
theorem epi_of_epi_of_epi_of_epi (hR₂ : R₂.Exact) (hR₁' : Epi (R₁.map' 1 2))
    (h₀ : Epi (app' φ 0)) (h₁ : Epi (app' φ 2)) :
    Epi (app' φ 1) := by
  let ψ : mk₃ (R₁.map' 0 1) (R₁.map' 1 2) (0 : _ ⟶ R₁.obj' 0) ⟶
    mk₃ (R₂.map' 0 1) (R₂.map' 1 2) (0 : _ ⟶ R₁.obj' 0) := homMk₃ (app' φ 0) (app' φ 1)
      (app' φ 2) (𝟙 _) (naturality' φ 0 1) (naturality' φ 1 2) (by simp)
  refine epi_of_epi_of_epi_of_mono' ψ (exact₂_mk _ (by simp) ?_)
    (hR₂.exact 0).exact_toComposableArrows (by simp)
    h₀ h₁ (by dsimp [ψ]; infer_instance)
  rw [ShortComplex.exact_iff_epi _ (by simp)]
  exact hR₁'

open ZeroObject

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Abelian.isIso_of_epi_of_isIso** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.Abelian`。
形式化陈述：isIso_of_epi_of_isIso (hR₁ : R₁.Exact) (hR₂ : R₂.Exact) (hR₁' : Epi (R₁.ma
p' 1 2)) (hR₂' : Epi (R₂.map' 1 2)) (h₀ : Epi (app' φ 0)) (h₁ : IsIso (app' φ 1)
) : IsIso (app' φ 2)
参数：hR₁ : R₁.Exact；hR₂ : R₂.Exact；hR₁' : Epi (R₁.map' 1 2)；hR₂' : Epi (R₂.map' 1 
2)；h₀ : Epi (app' φ 0)；h₁ : IsIso (app' φ 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用引理 `CategoryTheory.ComposableArrows.naturality'`：naturality' (φ : F ⟶ G) (i 
j : Nat) (hij : i <= j
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.ComposableArrows.precomp_map`：∀ {C : Type u_1} [inst : Ca
tegoryTheory.Category.{v_1, u_1} C] {n : ℕ} (F : CategoryTheory.ComposableArrows
 C n) {X : C}   (f : X ⟶ F.left) …
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.ComposableArrows.mk₁_map`：∀ {C : Type u_1} [inst : Catego
ryTheory.Category.{v_1, u_1} C] {X₀ X₁ : C} (f : X₀ ⟶ X₁) {X Y : Fin (1 + 1)}   
(g : X ⟶ Y), (CategoryTheory.…
· 使用定理 `CategoryTheory.Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono`：isIso_of_
epi_of_isIso_of_isIso_of_mono (h₀ : Epi (app' φ 0)) (h₁ : IsIso (app' φ 1)) (h₃ 
: IsIso (app' φ 3)) (h₄ : Mono (app' φ 4)) : IsIso …
· 使用引理 `CategoryTheory.ComposableArrows.exact_of_δ₀`：exact_of_δ₀ {S : Composable
Arrows C (n + 2)} (h : (mk₂ (S.map' 0 1) (S.map' 1 2)).Exact) (h₀ : S.δ₀.Exact) 
: S.Exact
· 使用定理 `CategoryTheory.ShortComplex.Exact.exact_toComposableArrows`：∀ {C : Type 
u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limi
ts.HasZeroMorphisms C]   {S : CategoryTheory.Sho…
· 使用定理 `CategoryTheory.ComposableArrows.Exact.toIsComplex`：∀ {C : Type u_1} [ins
t : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZer
oMorphisms C]   {n : ℕ} {S : CategoryTh…
· 使用定理 `CategoryTheory.ComposableArrows.Exact.exact`：∀ {C : Type u_1} [inst : Ca
tegoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorph
isms C]   {n : ℕ} {S : CategoryTh…
· 使用引理 `CategoryTheory.ComposableArrows.exact₂_mk`：exact₂_mk (S : ComposableArro
ws C 2) (w : S.map' 0 1 ≫ S.map' 1 2 = 0) (h : (ShortComplex.mk _ _ w).Exact) : 
S.Exact
· 使用引理 `CategoryTheory.ShortComplex.exact_iff_epi`：exact_iff_epi [HasZeroObject 
C] (hg : S.g = 0) : S.Exact ↔ Epi S.f
· 使用定理 `CategoryTheory.Limits.HasZeroObject.instEpi`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroObject C] {
X : C}   (f : X ⟶ 0), CategoryThe…
· 使用定理 `CategoryTheory.Limits.HasZeroObject.instMono`：∀ {C : Type u} [inst : Cat
egoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroObject C] 
{X : C}   (f : 0 ⟶ X), CategoryThe…
-/
lemma isIso_of_epi_of_isIso (hR₁ : R₁.Exact) (hR₂ : R₂.Exact) (hR₁' : Epi (R₁.map' 1 2))
    (hR₂' : Epi (R₂.map' 1 2)) (h₀ : Epi (app' φ 0)) (h₁ : IsIso (app' φ 1)) :
    IsIso (app' φ 2) := by
  let ψ : mk₄ (R₁.map' 0 1) (R₁.map' 1 2) (0 : _ ⟶ (0 : C)) (0 : _ ⟶ (0 : C)) ⟶
      mk₄ (R₂.map' 0 1) (R₂.map' 1 2) (0 : _ ⟶ (0 : C)) (0 : _ ⟶ (0 : C)) :=
    homMk₄ (app' φ 0) (app' φ 1) (app' φ 2) 0 0 (naturality' φ 0 1)
      (naturality' φ 1 2) (by simp) (by simp)
  refine isIso_of_epi_of_isIso_of_isIso_of_mono ?_ ?_ ψ h₀ h₁ inferInstance inferInstance
  · refine exact_of_δ₀ (hR₁.exact 0).exact_toComposableArrows (exact_of_δ₀ ?_ ?_)
    · refine exact₂_mk _ (by simp) ?_
      rwa [ShortComplex.exact_iff_epi _ (by simp)]
    · refine exact₂_mk _ (by simp) ?_
      rw [ShortComplex.exact_iff_epi _ (by simp)]
      infer_instance
  · refine exact_of_δ₀ (hR₂.exact 0).exact_toComposableArrows (exact_of_δ₀ ?_ ?_)
    · refine exact₂_mk _ (by simp) ?_
      rwa [ShortComplex.exact_iff_epi _ (by simp)]
    · refine exact₂_mk _ (by simp) ?_
      rw [ShortComplex.exact_iff_epi _ (by simp)]
      infer_instance

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Abelian.isIso_of_isIso_of_mono** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.Abelian`。
形式化陈述：isIso_of_isIso_of_mono (hR₁ : R₁.Exact) (hR₂ : R₂.Exact) (hR₁' : Mono (R₁.
map' 0 1)) (hR₂' : Mono (R₂.map' 0 1)) (h₁ : IsIso (app' φ 1)) (h₂ : Mono (app' 
φ 2)) : IsIso (app' φ 0)
参数：hR₁ : R₁.Exact；hR₂ : R₂.Exact；hR₁' : Mono (R₁.map' 0 1)；hR₂' : Mono (R₂.map' 
0 1)；h₁ : IsIso (app' φ 1)；h₂ : Mono (app' φ 2)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.ComposableArrows.precomp_map`：∀ {C : Type u_1} [inst : Ca
tegoryTheory.Category.{v_1, u_1} C] {n : ℕ} (F : CategoryTheory.ComposableArrows
 C n) {X : C}   (f : X ⟶ F.left) …
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用引理 `CategoryTheory.ComposableArrows.naturality'`：naturality' (φ : F ⟶ G) (i 
j : Nat) (hij : i <= j
· 使用定理 `CategoryTheory.Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono`：isIso_of_
epi_of_isIso_of_isIso_of_mono (h₀ : Epi (app' φ 0)) (h₁ : IsIso (app' φ 1)) (h₃ 
: IsIso (app' φ 3)) (h₄ : Mono (app' φ 4)) : IsIso …
· 使用引理 `CategoryTheory.ComposableArrows.exact_of_δ₀`：exact_of_δ₀ {S : Composable
Arrows C (n + 2)} (h : (mk₂ (S.map' 0 1) (S.map' 1 2)).Exact) (h₀ : S.δ₀.Exact) 
: S.Exact
· 使用引理 `CategoryTheory.ComposableArrows.exact₂_mk`：exact₂_mk (S : ComposableArro
ws C 2) (w : S.map' 0 1 ≫ S.map' 1 2 = 0) (h : (ShortComplex.mk _ _ w).Exact) : 
S.Exact
· 使用定理 `CategoryTheory.ComposableArrows.mk₁_map`：∀ {C : Type u_1} [inst : Catego
ryTheory.Category.{v_1, u_1} C] {X₀ X₁ : C} (f : X₀ ⟶ X₁) {X Y : Fin (1 + 1)}   
(g : X ⟶ Y), (CategoryTheory.…
· 使用引理 `CategoryTheory.ShortComplex.exact_iff_mono`：exact_iff_mono [HasZeroObjec
t C] (hf : S.f = 0) : S.Exact ↔ Mono S.g
· 使用定理 `CategoryTheory.Limits.HasZeroObject.instMono`：∀ {C : Type u} [inst : Cat
egoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroObject C] 
{X : C}   (f : 0 ⟶ X), CategoryThe…
· 使用定理 `CategoryTheory.ComposableArrows.IsComplex.zero'`：∀ {C : Type u_1} [inst 
: CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroM
orphisms C]   {n : ℕ} {S : CategoryTh…
· 使用定理 `CategoryTheory.ComposableArrows.Exact.toIsComplex`：∀ {C : Type u_1} [ins
t : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZer
oMorphisms C]   {n : ℕ} {S : CategoryTh…
· 使用定理 `CategoryTheory.ComposableArrows.Exact.exact`：∀ {C : Type u_1} [inst : Ca
tegoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorph
isms C]   {n : ℕ} {S : CategoryTh…
· 使用定理 `CategoryTheory.instEffectiveEpiOfIsIso`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],  
 CategoryTheory.EffectiveEpi…
-/
lemma isIso_of_isIso_of_mono (hR₁ : R₁.Exact) (hR₂ : R₂.Exact) (hR₁' : Mono (R₁.map' 0 1))
    (hR₂' : Mono (R₂.map' 0 1)) (h₁ : IsIso (app' φ 1)) (h₂ : Mono (app' φ 2)) :
    IsIso (app' φ 0) := by
  let ψ : mk₄ (0 : (0 : C) ⟶ (0 : C)) (0 : _ ⟶ _) (R₁.map' 0 1) (R₁.map' 1 2) ⟶
      mk₄ (0 : (0 : C) ⟶ (0 : C)) (0 : _ ⟶ _) (R₂.map' 0 1) (R₂.map' 1 2) :=
    homMk₄ 0 0 (app' φ 0) (app' φ 1) (app' φ 2) (by simp) (by simp) (naturality' φ 0 1)
      (naturality' φ 1 2)
  refine isIso_of_epi_of_isIso_of_isIso_of_mono ?_ ?_ ψ inferInstance inferInstance h₁ h₂
  · refine exact_of_δ₀ (exact₂_mk _ (by simp) ?_) (exact_of_δ₀ ?_ (exact₂_mk _ _ (hR₁.exact 0)))
    · rw [ShortComplex.exact_iff_mono _ (by simp)]
      infer_instance
    · refine exact₂_mk _ (by simp) ?_
      rwa [ShortComplex.exact_iff_mono _ (by simp)]
  · refine exact_of_δ₀ ?_ (exact_of_δ₀ ?_ (exact₂_mk _ _ (hR₂.exact 0)))
    · refine exact₂_mk _ (by simp) ?_
      rw [ShortComplex.exact_iff_mono _ (by simp)]
      infer_instance
    · refine exact₂_mk _ (by simp) ?_
      rwa [ShortComplex.exact_iff_mono _ (by simp)]

end Three

end Abelian

namespace ShortComplex

variable {C : Type*} [Category* C] [Abelian C]
variable {R₁ R₂ : ShortComplex C} (φ : R₁ ⟶ R₂)

attribute [local simp] ComposableArrows.Precomp.map

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.ShortComplex.mono_of_epi_of_epi_of_mono** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.ShortComplex`。
形式化陈述：mono_of_epi_of_epi_of_mono (hR₂ : R₂.Exact) (hR₁' : Epi R₁.g) (h₀ : Epi φ.
τ₁) (h₁ : Mono φ.τ₂) : Mono (φ.τ₃)
参数：hR₂ : R₂.Exact；hR₁' : Epi R₁.g；h₀ : Epi φ.τ₁；h₁ : Mono φ.τ₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.mono_of_epi_of_epi_mono'`：mono_of_epi_of_epi_mono
' (hR₁ : R₁.map' 0 2 = 0) (hR₁' : Epi (R₁.map' 1 2)) (hR₂ : R₂.Exact) (h₀ : Epi 
(app' φ 0)) (h₁ : Mono (app' φ 1)) : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ShortComplex.toComposableArrows_map`：∀ {C : Type u_1} [in
st : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZe
roMorphisms C]   (S : CategoryTheory.Sho…
· 使用定理 `CategoryTheory.ComposableArrows.mk₁_map`：∀ {C : Type u_1} [inst : Catego
ryTheory.Category.{v_1, u_1} C] {X₀ X₁ : C} (f : X₀ ⟶ X₁) {X Y : Fin (1 + 1)}   
(g : X ⟶ Y), (CategoryTheory.…
· 使用定理 `CategoryTheory.ShortComplex.zero`：∀ {C : Type u_1} [inst : CategoryTheor
y.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]   (
self : CategoryTheory.…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.ShortComplex.Exact.exact_toComposableArrows`：∀ {C : Type 
u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limi
ts.HasZeroMorphisms C]   {S : CategoryTheory.Sho…
-/
theorem mono_of_epi_of_epi_of_mono (hR₂ : R₂.Exact) (hR₁' : Epi R₁.g)
    (h₀ : Epi φ.τ₁) (h₁ : Mono φ.τ₂) : Mono (φ.τ₃) :=
  Abelian.mono_of_epi_of_epi_mono' (ShortComplex.mapToComposableArrows φ)
    (by simp) hR₁' hR₂.exact_toComposableArrows h₀ h₁

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.ShortComplex.epi_of_mono_of_epi_of_mono** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.ShortComplex`。
形式化陈述：epi_of_mono_of_epi_of_mono (hR₁ : R₁.Exact) (hR₂' : Mono R₂.f) (h₀ : Epi φ
.τ₂) (h₁ : Mono φ.τ₃) : Epi φ.τ₁
参数：hR₁ : R₁.Exact；hR₂' : Mono R₂.f；h₀ : Epi φ.τ₂；h₁ : Mono φ.τ₃。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.epi_of_mono_of_epi_of_mono'`：epi_of_mono_of_epi_o
f_mono' (hR₁ : R₁.Exact) (hR₂ : R₂.map' 0 2 = 0) (hR₂' : Mono (R₂.map' 0 1)) (h₀
 : Epi (app' φ 1)) (h₁ : Mono (app' φ 2)…
· 使用定理 `CategoryTheory.ShortComplex.Exact.exact_toComposableArrows`：∀ {C : Type 
u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limi
ts.HasZeroMorphisms C]   {S : CategoryTheory.Sho…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ShortComplex.toComposableArrows_map`：∀ {C : Type u_1} [in
st : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZe
roMorphisms C]   (S : CategoryTheory.Sho…
· 使用定理 `CategoryTheory.ComposableArrows.mk₁_map`：∀ {C : Type u_1} [inst : Catego
ryTheory.Category.{v_1, u_1} C] {X₀ X₁ : C} (f : X₀ ⟶ X₁) {X Y : Fin (1 + 1)}   
(g : X ⟶ Y), (CategoryTheory.…
· 使用定理 `CategoryTheory.ShortComplex.zero`：∀ {C : Type u_1} [inst : CategoryTheor
y.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]   (
self : CategoryTheory.…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem epi_of_mono_of_epi_of_mono (hR₁ : R₁.Exact)
    (hR₂' : Mono R₂.f) (h₀ : Epi φ.τ₂) (h₁ : Mono φ.τ₃) : Epi φ.τ₁ :=
  Abelian.epi_of_mono_of_epi_of_mono' (ShortComplex.mapToComposableArrows φ)
    hR₁.exact_toComposableArrows (by simp) hR₂' h₀ h₁
/-
**CategoryTheory.ShortComplex.mono_of_mono_of_mono_of_mono** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.ShortComplex`。
形式化陈述：mono_of_mono_of_mono_of_mono (hR₁ : R₁.Exact) (hR₂' : Mono R₂.f) (h₀ : Mon
o φ.τ₁) (h₁ : Mono φ.τ₃) : Mono φ.τ₂
参数：hR₁ : R₁.Exact；hR₂' : Mono R₂.f；h₀ : Mono φ.τ₁；h₁ : Mono φ.τ₃。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.mono_of_mono_of_mono_of_mono`：mono_of_mono_of_mon
o_of_mono (hR₁ : R₁.Exact) (hR₂' : Mono (R₂.map' 0 1)) (h₀ : Mono (app' φ 0)) (h
₁ : Mono (app' φ 2)) : Mono (app' φ 1)
· 使用定理 `CategoryTheory.ShortComplex.Exact.exact_toComposableArrows`：∀ {C : Type 
u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limi
ts.HasZeroMorphisms C]   {S : CategoryTheory.Sho…
-/
theorem mono_of_mono_of_mono_of_mono (hR₁ : R₁.Exact) (hR₂' : Mono R₂.f) (h₀ : Mono φ.τ₁)
    (h₁ : Mono φ.τ₃) : Mono φ.τ₂ :=
  Abelian.mono_of_mono_of_mono_of_mono (ShortComplex.mapToComposableArrows φ)
    hR₁.exact_toComposableArrows hR₂' h₀ h₁
/-
**CategoryTheory.ShortComplex.epi_of_epi_of_epi_of_epi** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.ShortComplex`。
形式化陈述：epi_of_epi_of_epi_of_epi (hR₂ : R₂.Exact) (hR₁' : Epi R₁.g) (h₀ : Epi φ.τ₁
) (h₁ : Epi φ.τ₃) : Epi φ.τ₂
参数：hR₂ : R₂.Exact；hR₁' : Epi R₁.g；h₀ : Epi φ.τ₁；h₁ : Epi φ.τ₃。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.epi_of_epi_of_epi_of_epi`：epi_of_epi_of_epi_of_ep
i (hR₂ : R₂.Exact) (hR₁' : Epi (R₁.map' 1 2)) (h₀ : Epi (app' φ 0)) (h₁ : Epi (a
pp' φ 2)) : Epi (app' φ 1)
· 使用定理 `CategoryTheory.ShortComplex.Exact.exact_toComposableArrows`：∀ {C : Type 
u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limi
ts.HasZeroMorphisms C]   {S : CategoryTheory.Sho…
-/
theorem epi_of_epi_of_epi_of_epi (hR₂ : R₂.Exact) (hR₁' : Epi R₁.g) (h₀ : Epi φ.τ₁)
    (h₁ : Epi φ.τ₃) : Epi φ.τ₂ :=
  Abelian.epi_of_epi_of_epi_of_epi (ShortComplex.mapToComposableArrows φ)
    hR₂.exact_toComposableArrows hR₁' h₀ h₁

end ShortComplex

end CategoryTheory

