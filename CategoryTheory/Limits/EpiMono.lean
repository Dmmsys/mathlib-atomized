/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Mono

/-!
# Relation between mono/epi and pullback/pushout squares

In this file, monomorphisms and epimorphisms are characterized in terms
of pullback and pushout squares. For example, we obtain `mono_iff_isPullback`
which asserts that a morphism `f : X ⟶ Y` is a monomorphism iff the obvious
square

```
X ⟶ X
|   |
v   v
X ⟶ Y
```

is a pullback square.


-/

public section

namespace CategoryTheory

open Category Limits

variable {C : Type*} [Category* C] {X Y : C} {f : X ⟶ Y}

section Mono

variable {c : PullbackCone f f}

/-
**CategoryTheory.mono_iff_fst_eq_snd** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory`。
形式化陈述：mono_iff_fst_eq_snd (hc : IsLimit c) : Mono f ↔ c.fst = c.snd
参数：hc : IsLimit c。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.Limits.PullbackCone.condition`：condition (t : PullbackCon
e f g) : fst t ≫ f = snd t ≫ g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
lemma mono_iff_fst_eq_snd (hc : IsLimit c) : Mono f ↔ c.fst = c.snd := by
  constructor
  · intro hf
    simpa only [← cancel_mono f] using c.condition
  · intro hf
    constructor
    intro Z g g' h
    obtain ⟨φ, rfl, rfl⟩ := PullbackCone.IsLimit.lift' hc g g' h
    rw [hf]
/-
**CategoryTheory.mono_iff_isIso_fst** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory`。
形式化陈述：mono_iff_isIso_fst (hc : IsLimit c) : Mono f ↔ IsIso c.fst
参数：hc : IsLimit c。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.mono_iff_fst_eq_snd`：mono_iff_fst_eq_snd (hc : IsLimit c)
 : Mono f ↔ c.fst = c.snd
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.PullbackCone.IsLimit.hom_ext`：∀ {C : Type u} [inst
 : CategoryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   {t : 
CategoryTheory.Limits.PullbackCone f g} …
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.strongMono_of_isIso`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {P Q : C} (f : Q ⟶ P) [CategoryTheory.IsIso f],   CategoryT
heory.StrongMono f
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.IsSplitEpi.epi`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [hf : CategoryTheory.IsSplitEpi f],   C
ategoryTheory.Epi f
-/
lemma mono_iff_isIso_fst (hc : IsLimit c) : Mono f ↔ IsIso c.fst := by
  rw [mono_iff_fst_eq_snd hc]
  constructor
  · intro h
    obtain ⟨φ, hφ₁, hφ₂⟩ := PullbackCone.IsLimit.lift' hc (𝟙 X) (𝟙 X) (by simp)
    refine ⟨φ, PullbackCone.IsLimit.hom_ext hc ?_ ?_, hφ₁⟩
    · simp only [assoc, hφ₁, id_comp, comp_id]
    · simp only [assoc, hφ₂, id_comp, comp_id, h]
  · intro
    obtain ⟨φ, hφ₁, hφ₂⟩ := PullbackCone.IsLimit.lift' hc (𝟙 X) (𝟙 X) (by simp)
    have : IsSplitEpi φ := IsSplitEpi.mk ⟨SplitEpi.mk c.fst (by
      rw [← cancel_mono c.fst, assoc, id_comp, hφ₁, comp_id])⟩
    rw [← cancel_epi φ, hφ₁, hφ₂]
/-
**CategoryTheory.mono_iff_isIso_snd** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory`。
形式化陈述：mono_iff_isIso_snd (hc : IsLimit c) : Mono f ↔ IsIso c.snd
参数：hc : IsLimit c。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.mono_iff_isIso_fst`：mono_iff_isIso_fst (hc : IsLimit c) :
 Mono f ↔ IsIso c.fst
-/
lemma mono_iff_isIso_snd (hc : IsLimit c) : Mono f ↔ IsIso c.snd :=
  mono_iff_isIso_fst (PullbackCone.flipIsLimit hc)

variable (f)
/-
**CategoryTheory.mono_iff_isPullback** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory`。
形式化陈述：mono_iff_isPullback : Mono f ↔ IsPullback (𝟙 X) (𝟙 X) f f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPullback.of_isLimit`：of_isLimit {c : PullbackCone f g} 
(h : Limits.IsLimit c) : IsPullback c.fst c.snd f g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `CategoryTheory.mono_iff_fst_eq_snd`：mono_iff_fst_eq_snd (hc : IsLimit c)
 : Mono f ↔ c.fst = c.snd
-/
lemma mono_iff_isPullback : Mono f ↔ IsPullback (𝟙 X) (𝟙 X) f f := by
  constructor
  · intro
    exact IsPullback.of_isLimit (PullbackCone.isLimitMkIdId f)
  · intro hf
    exact (mono_iff_fst_eq_snd hf.isLimit).2 rfl

end Mono

section Epi

variable {c : PushoutCocone f f}

/-
**CategoryTheory.epi_iff_inl_eq_inr** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory`。
形式化陈述：epi_iff_inl_eq_inr (hc : IsColimit c) : Epi f ↔ c.inl = c.inr
参数：hc : IsColimit c。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.Limits.PushoutCocone.condition`：condition (t : PushoutCoc
one f g) : f ≫ inl t = g ≫ inr t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
lemma epi_iff_inl_eq_inr (hc : IsColimit c) : Epi f ↔ c.inl = c.inr := by
  constructor
  · intro hf
    simpa only [← cancel_epi f] using c.condition
  · intro hf
    constructor
    intro Z g g' h
    obtain ⟨φ, rfl, rfl⟩ := PushoutCocone.IsColimit.desc' hc g g' h
    rw [hf]
/-
**CategoryTheory.epi_iff_isIso_inl** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory`。
形式化陈述：epi_iff_isIso_inl (hc : IsColimit c) : Epi f ↔ IsIso c.inl
参数：hc : IsColimit c。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.epi_iff_inl_eq_inr`：epi_iff_inl_eq_inr (hc : IsColimit c)
 : Epi f ↔ c.inl = c.inr
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.PushoutCocone.IsColimit.hom_ext`：∀ {C : Type u} [i
nst : CategoryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}   {t
 : CategoryTheory.Limits.PushoutCocone f g}…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `Mathlib.Tactic.Reassoc.eq_whisker'`：eq_whisker' {C : Type*} [Category* C
] {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) : f ≫ h = g ≫ h
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.StrongEpi.epi`：∀ {C : Type u} {inst : CategoryTheory.Cate
gory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongEpi f],   Cate
goryTheory.Epi f
· 使用定理 `CategoryTheory.strongEpi_of_isIso`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] {P Q : C} (f : P ⟶ Q) [CategoryTheory.IsIso f],   CategoryTh
eory.StrongEpi f
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.IsSplitMono.mono`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {X Y : C} (f : Y ⟶ X) [hf : CategoryTheory.IsSplitMono f], 
  CategoryTheory.Mono…
-/
lemma epi_iff_isIso_inl (hc : IsColimit c) : Epi f ↔ IsIso c.inl := by
  rw [epi_iff_inl_eq_inr hc]
  constructor
  · intro h
    obtain ⟨φ, hφ₁, hφ₂⟩ := PushoutCocone.IsColimit.desc' hc (𝟙 Y) (𝟙 Y) (by simp)
    refine ⟨φ, hφ₁, PushoutCocone.IsColimit.hom_ext hc ?_ ?_⟩
    · simp only [comp_id, reassoc_of% hφ₁]
    · simp only [comp_id, h, reassoc_of% hφ₂]
  · intro
    obtain ⟨φ, hφ₁, hφ₂⟩ := PushoutCocone.IsColimit.desc' hc (𝟙 Y) (𝟙 Y) (by simp)
    have : IsSplitMono φ := IsSplitMono.mk ⟨SplitMono.mk c.inl (by
      rw [← cancel_epi c.inl, reassoc_of% hφ₁, comp_id])⟩
    rw [← cancel_mono φ, hφ₁, hφ₂]
/-
**CategoryTheory.epi_iff_isIso_inr** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory`。
形式化陈述：epi_iff_isIso_inr (hc : IsColimit c) : Epi f ↔ IsIso c.inr
参数：hc : IsColimit c。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.epi_iff_isIso_inl`：epi_iff_isIso_inl (hc : IsColimit c) :
 Epi f ↔ IsIso c.inl
-/
lemma epi_iff_isIso_inr (hc : IsColimit c) : Epi f ↔ IsIso c.inr :=
  epi_iff_isIso_inl (PushoutCocone.flipIsColimit hc)

variable (f)
/-
**CategoryTheory.epi_iff_isPushout** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory`。
形式化陈述：epi_iff_isPushout : Epi f ↔ IsPushout f f (𝟙 Y) (𝟙 Y)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPushout.of_isColimit`：of_isColimit {c : PushoutCocone f
 g} (h : Limits.IsColimit c) : IsPushout f g c.inl c.inr
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `CategoryTheory.epi_iff_inl_eq_inr`：epi_iff_inl_eq_inr (hc : IsColimit c)
 : Epi f ↔ c.inl = c.inr
-/
lemma epi_iff_isPushout : Epi f ↔ IsPushout f f (𝟙 Y) (𝟙 Y) := by
  constructor
  · intro
    exact IsPushout.of_isColimit (PushoutCocone.isColimitMkIdId f)
  · intro hf
    exact (epi_iff_inl_eq_inr hf.isColimit).2 rfl

end Epi

end CategoryTheory

