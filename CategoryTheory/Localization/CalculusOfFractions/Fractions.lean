/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Localization.CalculusOfFractions

/-!
# Lemmas on fractions

Let `W : MorphismProperty C`, and objects `X` and `Y` in `C`. In this file,
we introduce structures like `W.LeftFraction₂ X Y` which consists of two
left fractions with the "same denominator" which shall be important in
the construction of the preadditive structure on the localized category
when `C` is preadditive and `W` has a left calculus of fractions.

When `W` has a left calculus of fractions, we generalize the lemmas
`RightFraction.exists_leftFraction` as `RightFraction₂.exists_leftFraction₂`,
`Localization.exists_leftFraction` as `Localization.exists_leftFraction₂` and
`Localization.exists_leftFraction₃`, and
`LeftFraction.map_eq_iff` as `LeftFraction₂.map_eq_iff`.

## Implementation note

The lemmas in this file are phrased with data that is bundled into structures like
`LeftFraction₂` or `LeftFraction₃`. It could have been possible to phrase them
with "unbundled data". However, this would require introducing 4 or 5 variables instead
of one. It is also very convenient to use dot notation.
Many definitions have been made reducible so as to ease rewrites when this API is used.

-/

@[expose] public section

namespace CategoryTheory

variable {C D : Type*} [Category* C] [Category* D] (L : C ⥤ D) (W : MorphismProperty C)
  [L.IsLocalization W]

namespace MorphismProperty

/-- This structure contains the data of two left fractions for
`W : MorphismProperty C` that have the same "denominator". -/
/-
**CategoryTheory.MorphismProperty.LeftFraction** 是 Mathlib 中的一个归纳类型，位于命名空间 `Cate
goryTheory.MorphismProperty`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] → Categor
yTheory.MorphismProperty C → C → C → Type (max u_1 v_1)
参数：max u_1 v_1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This structure contains the data of two left fractions for
`W : MorphismProperty C` that have the same "denominator".
-/
structure LeftFraction₂ (X Y : C) where
  /-- the auxiliary object of left fractions -/
  {Y' : C}
  /-- the numerator of the first left fraction -/
  f : X ⟶ Y'
  /-- the numerator of the second left fraction -/
  f' : X ⟶ Y'
  /-- the denominator of the left fractions -/
  s : Y ⟶ Y'
  /-- the condition that the denominator belongs to the given morphism property -/
  hs : W s
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y : C} (z : W.LeftFraction₂ X Y) : IsIso (L.map z.s) :=
  Localization.inverts L W _ z.hs

/-- This structure contains the data of three left fractions for
`W : MorphismProperty C` that have the same "denominator". -/
/-
**CategoryTheory.MorphismProperty.LeftFraction** 是 Mathlib 中的一个归纳类型，位于命名空间 `Cate
goryTheory.MorphismProperty`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] → Categor
yTheory.MorphismProperty C → C → C → Type (max u_1 v_1)
参数：max u_1 v_1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This structure contains the data of three left fractions for
`W : MorphismProperty C` that have the same "denominator".
-/
structure LeftFraction₃ (X Y : C) where
  /-- the auxiliary object of left fractions -/
  {Y' : C}
  /-- the numerator of the first left fraction -/
  f : X ⟶ Y'
  /-- the numerator of the second left fraction -/
  f' : X ⟶ Y'
  /-- the numerator of the third left fraction -/
  f'' : X ⟶ Y'
  /-- the denominator of the left fractions -/
  s : Y ⟶ Y'
  /-- the condition that the denominator belongs to the given morphism property -/
  hs : W s
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y : C} (z : W.LeftFraction₃ X Y) : IsIso (L.map z.s) :=
  Localization.inverts L W _ z.hs

/-- This structure contains the data of two right fractions for
`W : MorphismProperty C` that have the same "denominator". -/
/-
**CategoryTheory.MorphismProperty.RightFraction** 是 Mathlib 中的一个归纳类型，位于命名空间 `Cat
egoryTheory.MorphismProperty`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] → Categor
yTheory.MorphismProperty C → C → C → Type (max u_1 v_1)
参数：max u_1 v_1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This structure contains the data of two right fractions for
`W : MorphismProperty C` that have the same "denominator".
-/
structure RightFraction₂ (X Y : C) where
  /-- the auxiliary object of right fractions -/
  {X' : C}
  /-- the denominator of the right fractions -/
  s : X' ⟶ X
  /-- the condition that the denominator belongs to the given morphism property -/
  hs : W s
  /-- the numerator of the first right fraction -/
  f : X' ⟶ Y
  /-- the numerator of the second right fraction -/
  f' : X' ⟶ Y
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y : C} (z : W.RightFraction₂ X Y) : IsIso (L.map z.s) :=
  Localization.inverts L W _ z.hs

variable {W}

/-- The equivalence relation on tuples of left fractions with the same denominator
for a morphism property `W`. The fact it is an equivalence relation is not
formalized, but it would follow easily from `LeftFraction₂.map_eq_iff`. -/
/-
**CategoryTheory.MorphismProperty.LeftFraction** 是 Mathlib 中的一个归纳类型，位于命名空间 `Cate
goryTheory.MorphismProperty`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] → Categor
yTheory.MorphismProperty C → C → C → Type (max u_1 v_1)
参数：max u_1 v_1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence relation on tuples of left fractions with the same denominator
for a morphism property `W`. The fact it is an equivalence relation is not
formalized, but it would follow easily from `LeftFraction₂.map_eq_iff`.
-/
def LeftFraction₂Rel {X Y : C} (z₁ z₂ : W.LeftFraction₂ X Y) : Prop :=
  ∃ (Z : C) (t₁ : z₁.Y' ⟶ Z) (t₂ : z₂.Y' ⟶ Z) (_ : z₁.s ≫ t₁ = z₂.s ≫ t₂)
    (_ : z₁.f ≫ t₁ = z₂.f ≫ t₂) (_ : z₁.f' ≫ t₁ = z₂.f' ≫ t₂), W (z₁.s ≫ t₁)

namespace LeftFraction₂

variable {X Y : C} (φ : W.LeftFraction₂ X Y)

/-- The first left fraction. -/
/-
**CategoryTheory.MorphismProperty.LeftFraction₂.fst** 是 Mathlib 中的一个缩写定义，位于命名空间 
`CategoryTheory.MorphismProperty.LeftFraction₂`。
形式化陈述：fst : W.LeftFraction X Y where Y'
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.LeftFraction₂.hs`：∀ {C : Type u_1} [inst
 : CategoryTheory.Category.{v_1, u_1} C] {W : CategoryTheory.MorphismProperty C}
 {X Y : C}   (self : W.LeftFraction₂ X…

--- 原说明 ---
The first left fraction.
-/
abbrev fst : W.LeftFraction X Y where
  Y' := φ.Y'
  f := φ.f
  s := φ.s
  hs := φ.hs

/-- The second left fraction. -/
/-
**CategoryTheory.MorphismProperty.LeftFraction₂.snd** 是 Mathlib 中的一个缩写定义，位于命名空间 
`CategoryTheory.MorphismProperty.LeftFraction₂`。
形式化陈述：snd : W.LeftFraction X Y where Y'
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.LeftFraction₂.hs`：∀ {C : Type u_1} [inst
 : CategoryTheory.Category.{v_1, u_1} C] {W : CategoryTheory.MorphismProperty C}
 {X Y : C}   (self : W.LeftFraction₂ X…

--- 原说明 ---
The second left fraction.
-/
abbrev snd : W.LeftFraction X Y where
  Y' := φ.Y'
  f := φ.f'
  s := φ.s
  hs := φ.hs

/-- The exchange of the two fractions. -/
/-
**CategoryTheory.MorphismProperty.LeftFraction₂.symm** 是 Mathlib 中的一个缩写定义，位于命名空间
 `CategoryTheory.MorphismProperty.LeftFraction₂`。
形式化陈述：symm : W.LeftFraction₂ X Y where Y'
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.LeftFraction₂.hs`：∀ {C : Type u_1} [inst
 : CategoryTheory.Category.{v_1, u_1} C] {W : CategoryTheory.MorphismProperty C}
 {X Y : C}   (self : W.LeftFraction₂ X…

--- 原说明 ---
The exchange of the two fractions.
-/
abbrev symm : W.LeftFraction₂ X Y where
  Y' := φ.Y'
  f := φ.f'
  f' := φ.f
  s := φ.s
  hs := φ.hs

end LeftFraction₂

namespace LeftFraction₃

variable {X Y : C} (φ : W.LeftFraction₃ X Y)

/-- The first left fraction. -/
/-
**CategoryTheory.MorphismProperty.LeftFraction₃.fst** 是 Mathlib 中的一个缩写定义，位于命名空间 
`CategoryTheory.MorphismProperty.LeftFraction₃`。
形式化陈述：fst : W.LeftFraction X Y where Y'
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.LeftFraction₃.hs`：∀ {C : Type u_1} [inst
 : CategoryTheory.Category.{v_1, u_1} C] {W : CategoryTheory.MorphismProperty C}
 {X Y : C}   (self : W.LeftFraction₃ X…

--- 原说明 ---
The first left fraction.
-/
abbrev fst : W.LeftFraction X Y where
  Y' := φ.Y'
  f := φ.f
  s := φ.s
  hs := φ.hs

/-- The second left fraction. -/
/-
**CategoryTheory.MorphismProperty.LeftFraction₃.snd** 是 Mathlib 中的一个缩写定义，位于命名空间 
`CategoryTheory.MorphismProperty.LeftFraction₃`。
形式化陈述：snd : W.LeftFraction X Y where Y'
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.LeftFraction₃.hs`：∀ {C : Type u_1} [inst
 : CategoryTheory.Category.{v_1, u_1} C] {W : CategoryTheory.MorphismProperty C}
 {X Y : C}   (self : W.LeftFraction₃ X…

--- 原说明 ---
The second left fraction.
-/
abbrev snd : W.LeftFraction X Y where
  Y' := φ.Y'
  f := φ.f'
  s := φ.s
  hs := φ.hs

/-- The third left fraction. -/
/-
**CategoryTheory.MorphismProperty.LeftFraction₃.thd** 是 Mathlib 中的一个缩写定义，位于命名空间 
`CategoryTheory.MorphismProperty.LeftFraction₃`。
形式化陈述：thd : W.LeftFraction X Y where Y'
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.LeftFraction₃.hs`：∀ {C : Type u_1} [inst
 : CategoryTheory.Category.{v_1, u_1} C] {W : CategoryTheory.MorphismProperty C}
 {X Y : C}   (self : W.LeftFraction₃ X…

--- 原说明 ---
The third left fraction.
-/
abbrev thd : W.LeftFraction X Y where
  Y' := φ.Y'
  f := φ.f''
  s := φ.s
  hs := φ.hs

/-- Forgets the first fraction. -/
/-
**CategoryTheory.MorphismProperty.LeftFraction₃.forgetFst** 是 Mathlib 中的一个缩写定义，位
于命名空间 `CategoryTheory.MorphismProperty.LeftFraction₃`。
形式化陈述：forgetFst : W.LeftFraction₂ X Y where Y'
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.LeftFraction₃.hs`：∀ {C : Type u_1} [inst
 : CategoryTheory.Category.{v_1, u_1} C] {W : CategoryTheory.MorphismProperty C}
 {X Y : C}   (self : W.LeftFraction₃ X…

--- 原说明 ---
Forgets the first fraction.
-/
abbrev forgetFst : W.LeftFraction₂ X Y where
  Y' := φ.Y'
  f := φ.f'
  f' := φ.f''
  s := φ.s
  hs := φ.hs

/-- Forgets the second fraction. -/
/-
**CategoryTheory.MorphismProperty.LeftFraction₃.forgetSnd** 是 Mathlib 中的一个缩写定义，位
于命名空间 `CategoryTheory.MorphismProperty.LeftFraction₃`。
形式化陈述：forgetSnd : W.LeftFraction₂ X Y where Y'
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.LeftFraction₃.hs`：∀ {C : Type u_1} [inst
 : CategoryTheory.Category.{v_1, u_1} C] {W : CategoryTheory.MorphismProperty C}
 {X Y : C}   (self : W.LeftFraction₃ X…

--- 原说明 ---
Forgets the second fraction.
-/
abbrev forgetSnd : W.LeftFraction₂ X Y where
  Y' := φ.Y'
  f := φ.f
  f' := φ.f''
  s := φ.s
  hs := φ.hs

/-- Forgets the third fraction. -/
/-
**CategoryTheory.MorphismProperty.LeftFraction₃.forgetThd** 是 Mathlib 中的一个缩写定义，位
于命名空间 `CategoryTheory.MorphismProperty.LeftFraction₃`。
形式化陈述：forgetThd : W.LeftFraction₂ X Y where Y'
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.LeftFraction₃.hs`：∀ {C : Type u_1} [inst
 : CategoryTheory.Category.{v_1, u_1} C] {W : CategoryTheory.MorphismProperty C}
 {X Y : C}   (self : W.LeftFraction₃ X…

--- 原说明 ---
Forgets the third fraction.
-/
abbrev forgetThd : W.LeftFraction₂ X Y where
  Y' := φ.Y'
  f := φ.f
  f' := φ.f'
  s := φ.s
  hs := φ.hs

end LeftFraction₃

namespace LeftFraction₂Rel

variable {X Y : C} {z₁ z₂ : W.LeftFraction₂ X Y}

/-
**CategoryTheory.MorphismProperty.LeftFraction₂Rel.fst** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.MorphismProperty.LeftFraction₂Rel`。
形式化陈述：fst (h : LeftFraction₂Rel z₁ z₂) : LeftFractionRel z₁.fst z₂.fst
参数：h : LeftFraction₂Rel z₁ z₂。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma fst (h : LeftFraction₂Rel z₁ z₂) : LeftFractionRel z₁.fst z₂.fst := by
  obtain ⟨Z, t₁, t₂, hst, hft, _, ht⟩ := h
  exact ⟨Z, t₁, t₂, hst, hft, ht⟩
/-
**CategoryTheory.MorphismProperty.LeftFraction₂Rel.snd** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.MorphismProperty.LeftFraction₂Rel`。
形式化陈述：snd (h : LeftFraction₂Rel z₁ z₂) : LeftFractionRel z₁.snd z₂.snd
参数：h : LeftFraction₂Rel z₁ z₂。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma snd (h : LeftFraction₂Rel z₁ z₂) : LeftFractionRel z₁.snd z₂.snd := by
  obtain ⟨Z, t₁, t₂, hst, _, hft', ht⟩ := h
  exact ⟨Z, t₁, t₂, hst, hft', ht⟩

end LeftFraction₂Rel

namespace LeftFraction₂

variable (W)
variable [W.HasLeftCalculusOfFractions]

/-
**CategoryTheory.MorphismProperty.LeftFraction₂.map_eq_iff** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory.MorphismProperty.LeftFraction₂`。
形式化陈述：map_eq_iff {X Y : C} (φ ψ : W.LeftFraction₂ X Y) : (φ.fst.map L (Localizat
ion.inverts _ _) = ψ.fst.map L (Localization.inverts _ _) ∧ φ.snd.map L (Localiz
ation.inverts _ _) = ψ.snd.map L (Localization.inverts _ _)) ↔ LeftFraction₂Rel 
φ ψ
参数：φ ψ : W.LeftFraction₂ X Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Localization.inverts`：inverts : W.IsInvertedBy L
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.MorphismProperty.LeftFraction.map_eq_iff`：∀ {C : Type u_1
} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Categ
oryTheory.Category.{v_2, u_2} D] (L : Categor…
· 使用定理 `CategoryTheory.MorphismProperty.RightFraction.exists_leftFraction`：∀ {C 
: Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {W : CategoryTheory.Mo
rphismProperty C}   [W.HasLeftCalculusOfFractions] {X Y…
· 使用定理 `CategoryTheory.MorphismProperty.HasLeftCalculusOfFractions.ext`：∀ {C : T
ype u_1} {inst : CategoryTheory.Category.{v_1, u_1} C} {W : CategoryTheory.Morph
ismProperty C}   [self : W.HasLeftCalculusOfFraction…
· 使用定理 `CategoryTheory.MorphismProperty.LeftFraction₂.hs`：∀ {C : Type u_1} [inst
 : CategoryTheory.Category.{v_1, u_1} C] {W : CategoryTheory.MorphismProperty C}
 {X Y : C}   (self : W.LeftFraction₂ X…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Reassoc.eq_whisker'`：eq_whisker' {C : Type*} [Category* C
] {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) : f ≫ h = g ≫ h
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `CategoryTheory.MorphismProperty.comp_mem`：comp_mem (W : MorphismProperty
 C) [W.IsStableUnderComposition] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : W f) 
(hg : W g) : W (f ≫ g)
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.toIsStableUnderComposit
ion`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheor
y.MorphismProperty C}   [self : W.IsMultiplicative], W.IsStableUn…
· 使用定理 `CategoryTheory.MorphismProperty.HasLeftCalculusOfFractions.toIsMultiplic
ative`：∀ {C : Type u_1} {inst : CategoryTheory.Category.{v_1, u_1} C} {W : Categ
oryTheory.MorphismProperty C}   [self : W.HasLeftCalculusOfFraction…
· 使用定理 `CategoryTheory.MorphismProperty.LeftFraction.hs`：∀ {C : Type u_1} [inst 
: CategoryTheory.Category.{v_1, u_1} C] {W : CategoryTheory.MorphismProperty C} 
{X Y : C}   (self : W.LeftFraction X …
· 使用引理 `CategoryTheory.MorphismProperty.LeftFraction₂Rel.fst`：fst (h : LeftFract
ion₂Rel z₁ z₂) : LeftFractionRel z₁.fst z₂.fst
· 使用引理 `CategoryTheory.MorphismProperty.LeftFraction₂Rel.snd`：snd (h : LeftFract
ion₂Rel z₁ z₂) : LeftFractionRel z₁.snd z₂.snd
-/
lemma map_eq_iff {X Y : C} (φ ψ : W.LeftFraction₂ X Y) :
    (φ.fst.map L (Localization.inverts _ _) = ψ.fst.map L (Localization.inverts _ _) ∧
    φ.snd.map L (Localization.inverts _ _) = ψ.snd.map L (Localization.inverts _ _)) ↔
      LeftFraction₂Rel φ ψ := by
  simp only [LeftFraction.map_eq_iff L W]
  constructor
  · intro ⟨h, h'⟩
    obtain ⟨Z, t₁, t₂, hst, hft, ht⟩ := h
    obtain ⟨Z', t₁', t₂', hst', hft', ht'⟩ := h'
    dsimp at t₁ t₂ t₁' t₂' hst hft hst' hft' ht ht'
    have ⟨α, hα⟩ := (RightFraction.mk _ ht (φ.s ≫ t₁')).exists_leftFraction
    simp only [Category.assoc] at hα
    obtain ⟨Z'', u, hu, fac⟩ := HasLeftCalculusOfFractions.ext _ _ _ φ.hs hα
    have hα' : ψ.s ≫ t₂ ≫ α.f ≫ u = ψ.s ≫ t₂' ≫ α.s ≫ u := by
      rw [← reassoc_of% hst, ← reassoc_of% hα, ← reassoc_of% hst']
    obtain ⟨Z''', u', hu', fac'⟩ := HasLeftCalculusOfFractions.ext _ _ _ ψ.hs hα'
    simp only [Category.assoc] at fac fac'
    refine ⟨Z''', t₁' ≫ α.s ≫ u ≫ u', t₂' ≫ α.s ≫ u ≫ u', ?_, ?_, ?_, ?_⟩
    · rw [reassoc_of% hst']
    · rw [reassoc_of% fac, reassoc_of% hft, fac']
    · rw [reassoc_of% hft']
    · rw [← Category.assoc]
      exact W.comp_mem _ _ ht' (W.comp_mem _ _ α.hs (W.comp_mem _ _ hu hu'))
  · intro h
    exact ⟨h.fst, h.snd⟩

end LeftFraction₂

namespace RightFraction₂

variable {X Y : C}
variable (φ : W.RightFraction₂ X Y)

/-- The first right fraction. -/
/-
**CategoryTheory.MorphismProperty.RightFraction₂.fst** 是 Mathlib 中的一个缩写定义，位于命名空间
 `CategoryTheory.MorphismProperty.RightFraction₂`。
形式化陈述：fst : W.RightFraction X Y where X'
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.RightFraction₂.hs`：∀ {C : Type u_1} [ins
t : CategoryTheory.Category.{v_1, u_1} C] {W : CategoryTheory.MorphismProperty C
} {X Y : C}   (self : W.RightFraction₂ …

--- 原说明 ---
The first right fraction.
-/
abbrev fst : W.RightFraction X Y where
  X' := φ.X'
  f := φ.f
  s := φ.s
  hs := φ.hs

/-- The second right fraction. -/
/-
**CategoryTheory.MorphismProperty.RightFraction₂.snd** 是 Mathlib 中的一个缩写定义，位于命名空间
 `CategoryTheory.MorphismProperty.RightFraction₂`。
形式化陈述：snd : W.RightFraction X Y where X'
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.RightFraction₂.hs`：∀ {C : Type u_1} [ins
t : CategoryTheory.Category.{v_1, u_1} C] {W : CategoryTheory.MorphismProperty C
} {X Y : C}   (self : W.RightFraction₂ …

--- 原说明 ---
The second right fraction.
-/
abbrev snd : W.RightFraction X Y where
  X' := φ.X'
  f := φ.f'
  s := φ.s
  hs := φ.hs
/-
**CategoryTheory.MorphismProperty.RightFraction₂.exists_leftFraction** 是 Mathlib
 中的一个引理，位于命名空间 `CategoryTheory.MorphismProperty.RightFraction₂`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma exists_leftFraction₂ [W.HasLeftCalculusOfFractions] :
    ∃ (ψ : W.LeftFraction₂ X Y), φ.f ≫ ψ.s = φ.s ≫ ψ.f ∧
      φ.f' ≫ ψ.s = φ.s ≫ ψ.f' := by
  obtain ⟨ψ₁, hψ₁⟩ := φ.fst.exists_leftFraction
  obtain ⟨ψ₂, hψ₂⟩ := φ.snd.exists_leftFraction
  obtain ⟨α, hα⟩ := (RightFraction.mk _ ψ₁.hs ψ₂.s).exists_leftFraction
  dsimp at hψ₁ hψ₂ hα
  refine ⟨LeftFraction₂.mk (ψ₁.f ≫ α.f) (ψ₂.f ≫ α.s) (ψ₂.s ≫ α.s)
      (W.comp_mem _ _ ψ₂.hs α.hs), ?_, ?_⟩
  · dsimp
    rw [hα, reassoc_of% hψ₁]
  · rw [reassoc_of% hψ₂]

end RightFraction₂

end MorphismProperty

namespace Localization

variable [W.HasLeftCalculusOfFractions]

open MorphismProperty

/-
**CategoryTheory.Localization.exists_leftFraction** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Localization`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1}
 C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] (L : CategoryTheory.Functo
r C D)   (W : CategoryTheory.MorphismProperty C) [inst_2 : L.IsLocalization W] [
W.HasLeftCalculusOfFractions] {X Y : C}   (f : L.obj X ⟶ L.obj Y), ∃ φ, f = φ.ma
p L ⋯
参数：L : CategoryTheory.Functor C D；W : CategoryTheory.MorphismProperty C；f : L.ob
j X ⟶ L.obj Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.LeftFraction.Localization.instIsLocaliza
tionQ`：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] (W : Categ
oryTheory.MorphismProperty C)   [inst_1 : W.HasLeftCalculusOfFracti…
· 使用定理 `CategoryTheory.Localization.inverts`：inverts : W.IsInvertedBy L
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_app`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} 
D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_app_assoc`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F G : CategoryThe…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Functor.map_surjective`：map_surjective (F : C ⥤ D) [Full 
F] : Function.Surjective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
· 使用定理 `CategoryTheory.MorphismProperty.LeftFraction.Localization.Hom.mk_surject
ive`：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {W : Categor
yTheory.MorphismProperty C} {X Y : C}   (f : CategoryTheory.Morph…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.MorphismProperty.LeftFraction.Localization.homMk_eq_hom_m
k`：homMk_eq_hom_mk {X Y : C} (f : W.LeftFraction X Y) : homMk f = Hom.mk f
· 使用引理 `CategoryTheory.MorphismProperty.LeftFraction.Localization.homMk_eq`：homM
k_eq {X Y : C} (f : LeftFraction W X Y) : homMk f = f.map (Q W) (Localization.in
verts _ W)
· 使用引理 `CategoryTheory.MorphismProperty.LeftFraction.map_compatibility`：map_comp
atibility {W} {X Y : C} (φ : W.LeftFraction X Y) {E : Type*} [Category* E] (L₁ :
 C ⥤ D) (L₂ : C ⥤ E) [L₁.IsLocalization W] [L₂.IsLoc…
-/
lemma exists_leftFraction₂ {X Y : C} (f f' : L.obj X ⟶ L.obj Y) :
    ∃ (φ : W.LeftFraction₂ X Y), f = φ.fst.map L (inverts L W) ∧
      f' = φ.snd.map L (inverts L W) := by
  have ⟨φ, hφ⟩ := exists_leftFraction L W f
  have ⟨φ', hφ'⟩ := exists_leftFraction L W f'
  obtain ⟨α, hα⟩ := (RightFraction.mk _ φ.hs φ'.s).exists_leftFraction
  let ψ : W.LeftFraction₂ X Y :=
    { Y' := α.Y'
      f := φ.f ≫ α.f
      f' := φ'.f ≫ α.s
      s := φ'.s ≫ α.s
      hs := W.comp_mem _ _ φ'.hs α.hs }
  have : IsIso (L.map (φ'.s ≫ α.s)) := by
    rw [L.map_comp]
    infer_instance
  refine ⟨ψ, ?_, ?_⟩
  · rw [← cancel_mono (L.map (φ'.s ≫ α.s)), LeftFraction.map_comp_map_s,
      hα, L.map_comp, hφ, LeftFraction.map_comp_map_s_assoc,
      L.map_comp]
  · rw [← cancel_mono (L.map (φ'.s ≫ α.s)), hφ']
    nth_rw 1 [L.map_comp]
    rw [LeftFraction.map_comp_map_s_assoc, LeftFraction.map_comp_map_s,
      L.map_comp]
/-
**CategoryTheory.Localization.exists_leftFraction** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Localization`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1}
 C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] (L : CategoryTheory.Functo
r C D)   (W : CategoryTheory.MorphismProperty C) [inst_2 : L.IsLocalization W] [
W.HasLeftCalculusOfFractions] {X Y : C}   (f : L.obj X ⟶ L.obj Y), ∃ φ, f = φ.ma
p L ⋯
参数：L : CategoryTheory.Functor C D；W : CategoryTheory.MorphismProperty C；f : L.ob
j X ⟶ L.obj Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.LeftFraction.Localization.instIsLocaliza
tionQ`：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] (W : Categ
oryTheory.MorphismProperty C)   [inst_1 : W.HasLeftCalculusOfFracti…
· 使用定理 `CategoryTheory.Localization.inverts`：inverts : W.IsInvertedBy L
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_app`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} 
D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_app_assoc`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F G : CategoryThe…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Functor.map_surjective`：map_surjective (F : C ⥤ D) [Full 
F] : Function.Surjective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
· 使用定理 `CategoryTheory.MorphismProperty.LeftFraction.Localization.Hom.mk_surject
ive`：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {W : Categor
yTheory.MorphismProperty C} {X Y : C}   (f : CategoryTheory.Morph…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.MorphismProperty.LeftFraction.Localization.homMk_eq_hom_m
k`：homMk_eq_hom_mk {X Y : C} (f : W.LeftFraction X Y) : homMk f = Hom.mk f
· 使用引理 `CategoryTheory.MorphismProperty.LeftFraction.Localization.homMk_eq`：homM
k_eq {X Y : C} (f : LeftFraction W X Y) : homMk f = f.map (Q W) (Localization.in
verts _ W)
· 使用引理 `CategoryTheory.MorphismProperty.LeftFraction.map_compatibility`：map_comp
atibility {W} {X Y : C} (φ : W.LeftFraction X Y) {E : Type*} [Category* E] (L₁ :
 C ⥤ D) (L₂ : C ⥤ E) [L₁.IsLocalization W] [L₂.IsLoc…
-/
lemma exists_leftFraction₃ {X Y : C} (f f' f'' : L.obj X ⟶ L.obj Y) :
    ∃ (φ : W.LeftFraction₃ X Y), f = φ.fst.map L (inverts L W) ∧
      f' = φ.snd.map L (inverts L W) ∧
      f'' = φ.thd.map L (inverts L W) := by
  obtain ⟨α, hα, hα'⟩ := exists_leftFraction₂ L W f f'
  have ⟨β, hβ⟩ := exists_leftFraction L W f''
  obtain ⟨γ, hγ⟩ := (RightFraction.mk _ α.hs β.s).exists_leftFraction
  dsimp at hγ
  let ψ : W.LeftFraction₃ X Y :=
    { Y' := γ.Y'
      f := α.f ≫ γ.f
      f' := α.f' ≫ γ.f
      f'' := β.f ≫ γ.s
      s := β.s ≫ γ.s
      hs := W.comp_mem _ _ β.hs γ.hs }
  have : IsIso (L.map (β.s ≫ γ.s)) := by
    rw [L.map_comp]
    infer_instance
  refine ⟨ψ, ?_, ?_, ?_⟩
  · rw [← cancel_mono (L.map (β.s ≫ γ.s)), LeftFraction.map_comp_map_s, hα, hγ,
      L.map_comp, LeftFraction.map_comp_map_s_assoc, L.map_comp]
  · rw [← cancel_mono (L.map (β.s ≫ γ.s)), LeftFraction.map_comp_map_s, hα', hγ,
      L.map_comp, LeftFraction.map_comp_map_s_assoc, L.map_comp]
  · rw [← cancel_mono (L.map (β.s ≫ γ.s)), hβ]
    nth_rw 1 [L.map_comp]
    rw [LeftFraction.map_comp_map_s_assoc, LeftFraction.map_comp_map_s, L.map_comp]

end Localization

/-
**CategoryTheory.Functor.faithful_of_comp_of_hasLeftCalculusOfFractions** 是 Math
lib 中的一个定理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1}
 C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] (L : CategoryTheory.Functo
r C D)   (W : CategoryTheory.MorphismProperty C) [L.IsLocalization W] {E : Type 
u_3}   [inst_3 : CategoryTheory.Category.{v_3, u_3} E] (F : CategoryTheory.Funct
or D E) [W.HasLeftCalculusOfFractions],   (∀ ⦃X₁ X₂ : C⦄ (f g : X₁ ⟶ X₂), F.map 
(L.map f) = F.map (L.map g) → L.map f = L.map g) → F.Faithful
参数：L : CategoryTheory.Functor C D；W : CategoryTheory.MorphismProperty C；F : Cate
goryTheory.Functor D E；∀ ⦃X₁ X₂ : C⦄ (f g : X₁ ⟶ X₂), F.map (L.map f) = F.map (L
.map g) → L.map f = L.map g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Localization.essSurj`：essSurj (W) [L.IsLocalization W] : 
L.EssSurj
· 使用引理 `CategoryTheory.Functor.faithful_of_comp_essSurj`：faithful_of_comp_essSur
j (F : D ⥤ E) (L : C ⥤ D) [EssSurj L] (h : forall ⦃X₁ X₂ : C⦄ (f g : L.obj X₁ ⟶ 
L.obj X₂), F.map f = F.map g -> f = g…
· 使用定理 `CategoryTheory.Localization.inverts`：inverts : W.IsInvertedBy L
· 使用引理 `CategoryTheory.Localization.exists_leftFraction₂`：exists_leftFraction₂ {
X Y : C} (f f' : L.obj X ⟶ L.obj Y) : exists (φ : W.LeftFraction₂ X Y), f = φ.fs
t.map L (inverts L W) ∧ f' = φ.snd.map…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.IsSplitMono.mono`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {X Y : C} (f : Y ⟶ X) [hf : CategoryTheory.IsSplitMono f], 
  CategoryTheory.Mono…
· 使用定理 `CategoryTheory.IsSplitMono.of_iso`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {X Y : C} (f : Y ⟶ X) [CategoryTheory.IsIso f],   Categor
yTheory.IsSplitMono f
· 使用定理 `CategoryTheory.MorphismProperty.instIsIsoMapS`：∀ {C : Type u_1} {D : Typ
e u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.
Category.{v_2, u_2} D] (L : Categor…
· 使用引理 `CategoryTheory.MorphismProperty.LeftFraction.map_comp_map_s`：map_comp_ma
p_s (φ : W.LeftFraction X Y) (L : C ⥤ D) (hL : W.IsInvertedBy L) : φ.map L hL ≫ 
L.map φ.s = L.map φ.f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.eq_whisker`：eq_whisker {f g : X ⟶ Y} (w : f = g) (h : Y ⟶
 Z) : f ≫ h = g ≫ h
-/
lemma Functor.faithful_of_comp_of_hasLeftCalculusOfFractions
    {E : Type*} [Category* E] (F : D ⥤ E)
    [W.HasLeftCalculusOfFractions]
    (h : ∀ ⦃X₁ X₂ : C⦄ (f g : X₁ ⟶ X₂), F.map (L.map f) = F.map (L.map g) → L.map f = L.map g) :
    F.Faithful := by
  have := Localization.essSurj L W
  refine F.faithful_of_comp_essSurj L (fun X₁ X₂ f g hfg ↦ ?_)
  obtain ⟨φ, rfl, rfl⟩ := Localization.exists_leftFraction₂ L W f g
  rw [← cancel_mono (L.map φ.s), φ.fst.map_comp_map_s L, φ.snd.map_comp_map_s L]
  apply h
  simpa only [← F.map_comp, φ.fst.map_comp_map_s, φ.snd.map_comp_map_s] using
    hfg =≫ F.map (L.map φ.s)

end CategoryTheory

