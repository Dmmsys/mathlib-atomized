/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Group.TransferInstance
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions.Fractions
public import Mathlib.CategoryTheory.Localization.HasLocalization
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# The preadditive category structure on the localized category

In this file, it is shown that if `W : MorphismProperty C` has a left calculus
of fractions, and `C` is preadditive, then the localized category is preadditive,
and the localization functor is additive.

Let `L : C ⥤ D` be a localization functor for `W`. We first construct an abelian
group structure on `L.obj X ⟶ L.obj Y` for `X` and `Y` in `C`. The addition
is defined using representatives of two morphisms in `L` as left fractions with
the same denominator thanks to the lemmas in
`CategoryTheory.Localization.CalculusOfFractions.Fractions`.
As `L` is essentially surjective, we finally transport these abelian group structures
to `X' ⟶ Y'` for all `X'` and `Y'` in `D`.

Preadditive category instances are defined on the categories `W.Localization`
(and `W.Localization'`) under the assumption that `W` has a left calculus of fractions.
(It would be easy to deduce from the results in this file that if `W` has a right calculus
of fractions, then the localized category can also be equipped with
a preadditive structure, but only one of these two constructions can be made an instance!)

-/

@[expose] public section

namespace CategoryTheory

open MorphismProperty Preadditive Limits Category

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] (L : C ⥤ D)
  {W : MorphismProperty C} [L.IsLocalization W]

namespace MorphismProperty

/-- The opposite of a left fraction. -/
/-
**CategoryTheory.MorphismProperty.LeftFraction.neg** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.MorphismProperty.LeftFraction`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     [Ca
tegoryTheory.Preadditive C] →       {W : CategoryTheory.MorphismProperty C} → {X
 Y : C} → W.LeftFraction X Y → W.LeftFraction X Y
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.LeftFraction.hs`：∀ {C : Type u_1} [inst 
: CategoryTheory.Category.{v_1, u_1} C] {W : CategoryTheory.MorphismProperty C} 
{X Y : C}   (self : W.LeftFraction X …

--- 原说明 ---
The opposite of a left fraction.
-/
abbrev LeftFraction.neg {X Y : C} (φ : W.LeftFraction X Y) :
    W.LeftFraction X Y where
  Y' := φ.Y'
  f := -φ.f
  s := φ.s
  hs := φ.hs

namespace LeftFraction₂

variable {X Y : C} (φ : W.LeftFraction₂ X Y)

/-- The sum of two left fractions with the same denominator. -/
/-
**CategoryTheory.MorphismProperty.LeftFraction₂.add** 是 Mathlib 中的一个缩写定义，位于命名空间 
`CategoryTheory.MorphismProperty.LeftFraction₂`。
形式化陈述：add : W.LeftFraction X Y where Y'
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.LeftFraction₂.hs`：∀ {C : Type u_1} [inst
 : CategoryTheory.Category.{v_1, u_1} C] {W : CategoryTheory.MorphismProperty C}
 {X Y : C}   (self : W.LeftFraction₂ X…

--- 原说明 ---
The sum of two left fractions with the same denominator.
-/
abbrev add : W.LeftFraction X Y where
  Y' := φ.Y'
  f := φ.f + φ.f'
  s := φ.s
  hs := φ.hs

@[simp]
/-
**CategoryTheory.MorphismProperty.LeftFraction₂.symm_add** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.MorphismProperty.LeftFraction₂`。
形式化陈述：symm_add : φ.symm.add = φ.add
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma symm_add : φ.symm.add = φ.add := by
  grind

@[simp]
/-
**CategoryTheory.MorphismProperty.LeftFraction₂.map_add** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.MorphismProperty.LeftFraction₂`。
形式化陈述：map_add (F : C ⥤ D) (hF : W.IsInvertedBy F) [Preadditive D] [F.Additive] :
 φ.add.map F hF = φ.fst.map F hF + φ.snd.map F hF
参数：F : C ⥤ D；hF : W.IsInvertedBy F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.LeftFraction₂.hs`：∀ {C : Type u_1} [inst
 : CategoryTheory.Category.{v_1, u_1} C] {W : CategoryTheory.MorphismProperty C}
 {X Y : C}   (self : W.LeftFraction₂ X…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
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
· 使用定理 `CategoryTheory.Preadditive.add_comp`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C)   (f f' 
: P ⟶ Q) (g : Q ⟶ R),   C…
· 使用引理 `CategoryTheory.MorphismProperty.LeftFraction.map_comp_map_s`：map_comp_ma
p_s (φ : W.LeftFraction X Y) (L : C ⥤ D) (hL : W.IsInvertedBy L) : φ.map L hL ≫ 
L.map φ.s = L.map φ.f
· 使用定理 `CategoryTheory.Functor.map_add`：map_add {X Y : C} {f g : X ⟶ Y} : F.map 
(f + g) = F.map f + F.map g
-/
lemma map_add (F : C ⥤ D) (hF : W.IsInvertedBy F) [Preadditive D] [F.Additive] :
    φ.add.map F hF = φ.fst.map F hF + φ.snd.map F hF := by
  have := hF φ.s φ.hs
  rw [← cancel_mono (F.map φ.s), add_comp, LeftFraction.map_comp_map_s,
    LeftFraction.map_comp_map_s, LeftFraction.map_comp_map_s, F.map_add]

end LeftFraction₂

end MorphismProperty

variable (W)

namespace Localization

namespace Preadditive

section ImplementationDetails

/-! The definitions in this section (like `neg'` and `add'`) should never be used
directly. These are auxiliary definitions in order to construct the preadditive
structure `Localization.preadditive` (which is made irreducible). The user
should only rely on the fact that the localization functor is additive, as this
completely determines the preadditive structure on the localized category when
there is a calculus of left fractions. -/

variable [W.HasLeftCalculusOfFractions] {X Y Z : C}
variable {L}

/-- The opposite of a map `L.obj X ⟶ L.obj Y` when `L : C ⥤ D` is a localization
functor, `C` is preadditive and there is a left calculus of fractions. -/
/-
**CategoryTheory.Localization.Preadditive.neg'** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Localization.Preadditive`。
形式化陈述：neg' (f : L.obj X ⟶ L.obj Y) : L.obj X ⟶ L.obj Y
参数：f : L.obj X ⟶ L.obj Y。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Localization.inverts`：inverts : W.IsInvertedBy L
· 使用定理 `CategoryTheory.Localization.exists_leftFraction`：∀ {C : Type u_1} {D : T
ype u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheor
y.Category.{v_2, u_2} D] (L : Categor…

--- 原说明 ---
The opposite of a map `L.obj X ⟶ L.obj Y` when `L : C ⥤ D` is a localization
functor, `C` is preadditive and there is a left calculus of fractions.
-/
noncomputable def neg' (f : L.obj X ⟶ L.obj Y) : L.obj X ⟶ L.obj Y :=
  (exists_leftFraction L W f).choose.neg.map L (inverts L W)
/-
**CategoryTheory.Localization.Preadditive.neg'_eq** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Localization.Preadditive`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1}
 C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : CategoryTheory.P
readditive C]   {L : CategoryTheory.Functor C D} (W : CategoryTheory.MorphismPro
perty C) [inst_3 : L.IsLocalization W]   [inst_4 : W.HasLeftCalculusOfFractions]
 {X Y : C} (f : L.obj X ⟶ L.obj Y) (φ : W.LeftFraction X Y),   f = φ.map L ⋯ → C
ategoryTheory.Localization.Preadditive.neg' W f = φ.neg.map L ⋯
参数：W : CategoryTheory.MorphismProperty C；f : L.obj X ⟶ L.obj Y；φ : W.LeftFractio
n X Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Localization.inverts`：inverts : W.IsInvertedBy L
· 使用定理 `CategoryTheory.Localization.exists_leftFraction`：∀ {C : Type u_1} {D : T
ype u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheor
y.Category.{v_2, u_2} D] (L : Categor…
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MorphismProperty.LeftFraction.map_eq_iff`：∀ {C : Type u_1
} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Categ
oryTheory.Category.{v_2, u_2} D] (L : Categor…
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
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.MorphismProperty.LeftFraction.map_comp_map_s_assoc`：∀ {C 
: Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst
_1 : CategoryTheory.Category.{v_2, u_2} D] {W : Categor…
· 使用定理 `CategoryTheory.Preadditive.neg_comp`：neg_comp : (-f) ≫ g = -f ≫ g
-/
lemma neg'_eq (f : L.obj X ⟶ L.obj Y) (φ : W.LeftFraction X Y)
    (hφ : f = φ.map L (inverts L W)) :
    neg' W f = φ.neg.map L (inverts L W) := by
  obtain ⟨φ₀, rfl, hφ₀⟩ : ∃ (φ₀ : W.LeftFraction X Y)
    (_ : f = φ₀.map L (inverts L W)),
      neg' W f = φ₀.neg.map L (inverts L W) :=
    ⟨_, (exists_leftFraction L W f).choose_spec, rfl⟩
  rw [MorphismProperty.LeftFraction.map_eq_iff] at hφ
  obtain ⟨Y', t₁, t₂, hst, hft, ht⟩ := hφ
  have := inverts L W _ ht
  rw [← cancel_mono (L.map (φ₀.s ≫ t₁))]
  nth_rw 1 [L.map_comp]
  rw [hφ₀, hst, LeftFraction.map_comp_map_s_assoc, L.map_comp,
    LeftFraction.map_comp_map_s_assoc, ← L.map_comp, ← L.map_comp,
    neg_comp, neg_comp, hft]

/-- The addition of two maps `L.obj X ⟶ L.obj Y` when `L : C ⥤ D` is a localization
functor, `C` is preadditive and there is a left calculus of fractions. -/
/-
**CategoryTheory.Localization.Preadditive.add'** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Localization.Preadditive`。
形式化陈述：add' (f₁ f₂ : L.obj X ⟶ L.obj Y) : L.obj X ⟶ L.obj Y
参数：f₁ f₂ : L.obj X ⟶ L.obj Y。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Localization.inverts`：inverts : W.IsInvertedBy L
· 使用引理 `CategoryTheory.Localization.exists_leftFraction₂`：exists_leftFraction₂ {
X Y : C} (f f' : L.obj X ⟶ L.obj Y) : exists (φ : W.LeftFraction₂ X Y), f = φ.fs
t.map L (inverts L W) ∧ f' = φ.snd.map…

--- 原说明 ---
The addition of two maps `L.obj X ⟶ L.obj Y` when `L : C ⥤ D` is a localization
functor, `C` is preadditive and there is a left calculus of fractions.
-/
noncomputable def add' (f₁ f₂ : L.obj X ⟶ L.obj Y) : L.obj X ⟶ L.obj Y :=
  (exists_leftFraction₂ L W f₁ f₂).choose.add.map L (inverts L W)
/-
**CategoryTheory.Localization.Preadditive.add'_eq** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Localization.Preadditive`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1}
 C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : CategoryTheory.P
readditive C]   {L : CategoryTheory.Functor C D} (W : CategoryTheory.MorphismPro
perty C) [inst_3 : L.IsLocalization W]   [inst_4 : W.HasLeftCalculusOfFractions]
 {X Y : C} (f₁ f₂ : L.obj X ⟶ L.obj Y) (φ : W.LeftFraction₂ X Y),   f₁ = φ.fst.m
ap L ⋯ → f₂ = φ.snd.map L ⋯ → CategoryTheory.Localization.Preadditive.add' W f₁ 
f₂ = φ.add.map L ⋯
参数：W : CategoryTheory.MorphismProperty C；f₁ f₂ : L.obj X ⟶ L.obj Y；φ : W.LeftFra
ction₂ X Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Localization.inverts`：inverts : W.IsInvertedBy L
· 使用引理 `CategoryTheory.Localization.exists_leftFraction₂`：exists_leftFraction₂ {
X Y : C} (f f' : L.obj X ⟶ L.obj Y) : exists (φ : W.LeftFraction₂ X Y), f = φ.fs
t.map L (inverts L W) ∧ f' = φ.snd.map…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `CategoryTheory.MorphismProperty.LeftFraction₂.map_eq_iff`：map_eq_iff {X 
Y : C} (φ ψ : W.LeftFraction₂ X Y) : (φ.fst.map L (Localization.inverts _ _) = ψ
.fst.map L (Localization.inverts _ _) ∧ φ.snd.…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
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
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.MorphismProperty.LeftFraction.map_comp_map_s_assoc`：∀ {C 
: Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst
_1 : CategoryTheory.Category.{v_2, u_2} D] {W : Categor…
· 使用定理 `CategoryTheory.Preadditive.add_comp`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C)   (f f' 
: P ⟶ Q) (g : Q ⟶ R),   C…
-/
lemma add'_eq (f₁ f₂ : L.obj X ⟶ L.obj Y) (φ : W.LeftFraction₂ X Y)
    (hφ₁ : f₁ = φ.fst.map L (inverts L W))
    (hφ₂ : f₂ = φ.snd.map L (inverts L W)) :
    add' W f₁ f₂ = φ.add.map L (inverts L W) := by
  obtain ⟨φ₀, rfl, rfl, hφ₀⟩ : ∃ (φ₀ : W.LeftFraction₂ X Y)
    (_ : f₁ = φ₀.fst.map L (inverts L W))
    (_ : f₂ = φ₀.snd.map L (inverts L W)),
    add' W f₁ f₂ = φ₀.add.map L (inverts L W) :=
    ⟨(exists_leftFraction₂ L W f₁ f₂).choose,
      (exists_leftFraction₂ L W f₁ f₂).choose_spec.1,
      (exists_leftFraction₂ L W f₁ f₂).choose_spec.2, rfl⟩
  obtain ⟨Z, t₁, t₂, hst, hft, hft', ht⟩ := (LeftFraction₂.map_eq_iff L W φ₀ φ).1 ⟨hφ₁, hφ₂⟩
  have := inverts L W _ ht
  rw [hφ₀, ← cancel_mono (L.map (φ₀.s ≫ t₁))]
  nth_rw 2 [hst]
  rw [L.map_comp, L.map_comp, LeftFraction.map_comp_map_s_assoc,
    LeftFraction.map_comp_map_s_assoc, ← L.map_comp, ← L.map_comp,
    add_comp, add_comp, hft, hft']
/-
**CategoryTheory.Localization.Preadditive.add'_comm** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.Localization.Preadditive`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1}
 C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : CategoryTheory.P
readditive C]   {L : CategoryTheory.Functor C D} (W : CategoryTheory.MorphismPro
perty C) [inst_3 : L.IsLocalization W]   [inst_4 : W.HasLeftCalculusOfFractions]
 {X Y : C} (f₁ f₂ : L.obj X ⟶ L.obj Y),   CategoryTheory.Localization.Preadditiv
e.add' W f₁ f₂ = CategoryTheory.Localization.Preadditive.add' W f₂ f₁
参数：W : CategoryTheory.MorphismProperty C；f₁ f₂ : L.obj X ⟶ L.obj Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Localization.inverts`：inverts : W.IsInvertedBy L
· 使用引理 `CategoryTheory.Localization.exists_leftFraction₂`：exists_leftFraction₂ {
X Y : C} (f f' : L.obj X ⟶ L.obj Y) : exists (φ : W.LeftFraction₂ X Y), f = φ.fs
t.map L (inverts L W) ∧ f' = φ.snd.map…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Localization.Preadditive.add'_eq`：∀ {C : Type u_1} {D : T
ype u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheor
y.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用引理 `CategoryTheory.MorphismProperty.LeftFraction₂.symm_add`：symm_add : φ.sym
m.add = φ.add
-/
lemma add'_comm (f₁ f₂ : L.obj X ⟶ L.obj Y) :
    add' W f₁ f₂ = add' W f₂ f₁ := by
  obtain ⟨α, h₁, h₂⟩ := exists_leftFraction₂ L W f₁ f₂
  rw [add'_eq W f₁ f₂ α h₁ h₂, add'_eq W f₂ f₁ α.symm h₂ h₁, α.symm_add]
/-
**CategoryTheory.Localization.Preadditive.add'_zero** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.Localization.Preadditive`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1}
 C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : CategoryTheory.P
readditive C]   {L : CategoryTheory.Functor C D} (W : CategoryTheory.MorphismPro
perty C) [inst_3 : L.IsLocalization W]   [inst_4 : W.HasLeftCalculusOfFractions]
 {X Y : C} (f : L.obj X ⟶ L.obj Y),   CategoryTheory.Localization.Preadditive.ad
d' W f (L.map 0) = f
参数：W : CategoryTheory.MorphismProperty C；f : L.obj X ⟶ L.obj Y；L.map 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Localization.inverts`：inverts : W.IsInvertedBy L
· 使用定理 `CategoryTheory.Localization.exists_leftFraction`：∀ {C : Type u_1} {D : T
ype u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheor
y.Category.{v_2, u_2} D] (L : Categor…
· 使用定理 `CategoryTheory.MorphismProperty.LeftFraction.hs`：∀ {C : Type u_1} [inst 
: CategoryTheory.Category.{v_1, u_1} C] {W : CategoryTheory.MorphismProperty C} 
{X Y : C}   (self : W.LeftFraction X …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Localization.Preadditive.add'_eq`：∀ {C : Type u_1} {D : T
ype u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheor
y.Category.{v_2, u_2} D] [inst_2 : Ca…
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
· 使用定理 `CategoryTheory.MorphismProperty.LeftFraction.instIsIsoMapSOfIsLocalizati
on`：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C
]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] {W : Categor…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用引理 `CategoryTheory.MorphismProperty.LeftFraction.map_comp_map_s`：map_comp_ma
p_s (φ : W.LeftFraction X Y) (L : C ⥤ D) (hL : W.IsInvertedBy L) : φ.map L hL ≫ 
L.map φ.s = L.map φ.f
· 使用定理 `CategoryTheory.MorphismProperty.LeftFraction₂.hs`：∀ {C : Type u_1} [inst
 : CategoryTheory.Category.{v_1, u_1} C] {W : CategoryTheory.MorphismProperty C}
 {X Y : C}   (self : W.LeftFraction₂ X…
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
lemma add'_zero (f : L.obj X ⟶ L.obj Y) :
    add' W f (L.map 0) = f := by
  obtain ⟨α, hα⟩ := exists_leftFraction L W f
  rw [add'_eq W f (L.map 0) (LeftFraction₂.mk α.f 0 α.s α.hs) hα, hα]; swap
  · rw [← cancel_mono (L.map α.s), ← L.map_comp, Limits.zero_comp,
      LeftFraction.map_comp_map_s]
  dsimp [LeftFraction₂.add]
  rw [add_zero]
/-
**CategoryTheory.Localization.Preadditive.zero_add'** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.Localization.Preadditive`。
形式化陈述：zero_add' (f : L.obj X ⟶ L.obj Y) : add' W (L.map 0) f = f
参数：f : L.obj X ⟶ L.obj Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Localization.Preadditive.add'_comm`：∀ {C : Type u_1} {D :
 Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryThe
ory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Localization.Preadditive.add'_zero`：∀ {C : Type u_1} {D :
 Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryThe
ory.Category.{v_2, u_2} D] [inst_2 : Ca…
-/
lemma zero_add' (f : L.obj X ⟶ L.obj Y) :
    add' W (L.map 0) f = f := by
  rw [add'_comm, add'_zero]
/-
**CategoryTheory.Localization.Preadditive.neg'_add'_self** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.Localization.Preadditive`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1}
 C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : CategoryTheory.P
readditive C]   {L : CategoryTheory.Functor C D} (W : CategoryTheory.MorphismPro
perty C) [inst_3 : L.IsLocalization W]   [inst_4 : W.HasLeftCalculusOfFractions]
 {X Y : C} (f : L.obj X ⟶ L.obj Y),   CategoryTheory.Localization.Preadditive.ad
d' W (CategoryTheory.Localization.Preadditive.neg' W f) f = L.map 0
参数：W : CategoryTheory.MorphismProperty C；f : L.obj X ⟶ L.obj Y；CategoryTheory.Lo
calization.Preadditive.neg' W f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Localization.inverts`：inverts : W.IsInvertedBy L
· 使用定理 `CategoryTheory.Localization.exists_leftFraction`：∀ {C : Type u_1} {D : T
ype u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheor
y.Category.{v_2, u_2} D] (L : Categor…
· 使用定理 `CategoryTheory.MorphismProperty.LeftFraction.hs`：∀ {C : Type u_1} [inst 
: CategoryTheory.Category.{v_1, u_1} C] {W : CategoryTheory.MorphismProperty C} 
{X Y : C}   (self : W.LeftFraction X …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Localization.Preadditive.add'_eq`：∀ {C : Type u_1} {D : T
ype u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheor
y.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Localization.Preadditive.neg'_eq`：∀ {C : Type u_1} {D : T
ype u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheor
y.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
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
· 使用定理 `CategoryTheory.MorphismProperty.LeftFraction.instIsIsoMapSOfIsLocalizati
on`：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C
]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] {W : Categor…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `CategoryTheory.MorphismProperty.LeftFraction.map_comp_map_s`：map_comp_ma
p_s (φ : W.LeftFraction X Y) (L : C ⥤ D) (hL : W.IsInvertedBy L) : φ.map L hL ≫ 
L.map φ.s = L.map φ.f
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma neg'_add'_self (f : L.obj X ⟶ L.obj Y) :
    add' W (neg' W f) f = L.map 0 := by
  obtain ⟨α, rfl⟩ := exists_leftFraction L W f
  rw [add'_eq W _ _ (LeftFraction₂.mk (-α.f) α.f α.s α.hs) (neg'_eq W _ _ rfl) rfl]
  simp only [← cancel_mono (L.map α.s), LeftFraction.map_comp_map_s, ← L.map_comp,
    Limits.zero_comp, neg_add_cancel]
/-
**CategoryTheory.Localization.Preadditive.add'_assoc** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.Localization.Preadditive`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1}
 C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : CategoryTheory.P
readditive C]   {L : CategoryTheory.Functor C D} (W : CategoryTheory.MorphismPro
perty C) [inst_3 : L.IsLocalization W]   [inst_4 : W.HasLeftCalculusOfFractions]
 {X Y : C} (f₁ f₂ f₃ : L.obj X ⟶ L.obj Y),   CategoryTheory.Localization.Preaddi
tive.add' W (CategoryTheory.Localization.Preadditive.add' W f₁ f₂) f₃ =     Cate
goryTheory.Localization.Preadditive.add' W f₁ (CategoryTheory.Localization.Pread
ditive.add' W f₂ f₃)
参数：W : CategoryTheory.MorphismProperty C；f₁ f₂ f₃ : L.obj X ⟶ L.obj Y；CategoryTh
eory.Localization.Preadditive.add' W f₁ f₂；CategoryTheory.Localization.Preadditi
ve.add' W f₂ f₃。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Localization.inverts`：inverts : W.IsInvertedBy L
· 使用引理 `CategoryTheory.Localization.exists_leftFraction₃`：exists_leftFraction₃ {
X Y : C} (f f' f'' : L.obj X ⟶ L.obj Y) : exists (φ : W.LeftFraction₃ X Y), f = 
φ.fst.map L (inverts L W) ∧ f' = φ.snd…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Localization.Preadditive.add'_eq`：∀ {C : Type u_1} {D : T
ype u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheor
y.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.MorphismProperty.LeftFraction₃.hs`：∀ {C : Type u_1} [inst
 : CategoryTheory.Category.{v_1, u_1} C] {W : CategoryTheory.MorphismProperty C}
 {X Y : C}   (self : W.LeftFraction₃ X…
· 使用定理 `CategoryTheory.MorphismProperty.LeftFraction₂.hs`：∀ {C : Type u_1} [inst
 : CategoryTheory.Category.{v_1, u_1} C] {W : CategoryTheory.MorphismProperty C}
 {X Y : C}   (self : W.LeftFraction₂ X…
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
-/
lemma add'_assoc (f₁ f₂ f₃ : L.obj X ⟶ L.obj Y) :
    add' W (add' W f₁ f₂) f₃ = add' W f₁ (add' W f₂ f₃) := by
  obtain ⟨α, h₁, h₂, h₃⟩ := exists_leftFraction₃ L W f₁ f₂ f₃
  rw [add'_eq W f₁ f₂ α.forgetThd h₁ h₂, add'_eq W f₂ f₃ α.forgetFst h₂ h₃,
    add'_eq W _ _ (LeftFraction₂.mk (α.f + α.f') α.f'' α.s α.hs) rfl h₃,
    add'_eq W _ _ (LeftFraction₂.mk α.f (α.f' + α.f'') α.s α.hs) h₁ rfl]
  dsimp [LeftFraction₂.add]
  rw [add_assoc]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Localization.Preadditive.add'_comp** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.Localization.Preadditive`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1}
 C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : CategoryTheory.P
readditive C]   {L : CategoryTheory.Functor C D} (W : CategoryTheory.MorphismPro
perty C) [inst_3 : L.IsLocalization W]   [inst_4 : W.HasLeftCalculusOfFractions]
 {X Y Z : C} (f₁ f₂ : L.obj X ⟶ L.obj Y) (g : L.obj Y ⟶ L.obj Z),   CategoryTheo
ry.CategoryStruct.comp (CategoryTheory.Localization.Preadditive.add' W f₁ f₂) g 
=     CategoryTheory.Localization.Preadditive.add' W (CategoryTheory.CategoryStr
uct.comp f₁ g)       (CategoryTheory.CategoryStruct.comp f₂ g)
参数：W : CategoryTheory.MorphismProperty C；f₁ f₂ : L.obj X ⟶ L.obj Y；g : L.obj Y ⟶
 L.obj Z；CategoryTheory.Localization.Preadditive.add' W f₁ f₂；CategoryTheory.Cat
egoryStruct.comp f₁ g；CategoryTheory.CategoryStruct.comp f₂ g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Localization.inverts`：inverts : W.IsInvertedBy L
· 使用引理 `CategoryTheory.Localization.exists_leftFraction₂`：exists_leftFraction₂ {
X Y : C} (f f' : L.obj X ⟶ L.obj Y) : exists (φ : W.LeftFraction₂ X Y), f = φ.fs
t.map L (inverts L W) ∧ f' = φ.snd.map…
· 使用定理 `CategoryTheory.Localization.exists_leftFraction`：∀ {C : Type u_1} {D : T
ype u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheor
y.Category.{v_2, u_2} D] (L : Categor…
· 使用定理 `CategoryTheory.MorphismProperty.LeftFraction₂.hs`：∀ {C : Type u_1} [inst
 : CategoryTheory.Category.{v_1, u_1} C] {W : CategoryTheory.MorphismProperty C}
 {X Y : C}   (self : W.LeftFraction₂ X…
· 使用定理 `CategoryTheory.MorphismProperty.RightFraction.exists_leftFraction`：∀ {C 
: Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {W : CategoryTheory.Mo
rphismProperty C}   [W.HasLeftCalculusOfFractions] {X Y…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Localization.Preadditive.add'_eq`：∀ {C : Type u_1} {D : T
ype u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheor
y.Category.{v_2, u_2} D] [inst_2 : Ca…
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
· 使用引理 `CategoryTheory.MorphismProperty.LeftFraction.map_comp_map_eq_map`：map_co
mp_map_eq_map {X Y Z : C} (z₁ : W.LeftFraction X Y) (z₂ : W.LeftFraction Y Z) (z
₃ : W.LeftFraction z₁.Y' z₂.Y') (h₃ : z₂.f ≫ z₃.s = z₁…
· 使用定理 `CategoryTheory.Preadditive.add_comp`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C)   (f f' 
: P ⟶ Q) (g : Q ⟶ R),   C…
-/
lemma add'_comp (f₁ f₂ : L.obj X ⟶ L.obj Y) (g : L.obj Y ⟶ L.obj Z) :
    add' W f₁ f₂ ≫ g = add' W (f₁ ≫ g) (f₂ ≫ g) := by
  obtain ⟨α, h₁, h₂⟩ := exists_leftFraction₂ L W f₁ f₂
  obtain ⟨β, hβ⟩ := exists_leftFraction L W g
  obtain ⟨γ, hγ⟩ := (RightFraction.mk _ α.hs β.f).exists_leftFraction
  dsimp at hγ
  rw [add'_eq W f₁ f₂ α h₁ h₂, add'_eq W (f₁ ≫ g) (f₂ ≫ g)
    (LeftFraction₂.mk (α.f ≫ γ.f) (α.f' ≫ γ.f) (β.s ≫ γ.s)
    (W.comp_mem _ _ β.hs γ.hs))]; rotate_left
  · rw [h₁, hβ]
    exact LeftFraction.map_comp_map_eq_map _ _ _ hγ _
  · rw [h₂, hβ]
    exact LeftFraction.map_comp_map_eq_map _ _ _ hγ _
  rw [hβ, LeftFraction.map_comp_map_eq_map _ _ γ hγ]
  dsimp [LeftFraction₂.add]
  rw [add_comp]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Localization.Preadditive.comp_add'** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.Localization.Preadditive`。
形式化陈述：comp_add' (f : L.obj X ⟶ L.obj Y) (g₁ g₂ : L.obj Y ⟶ L.obj Z) : f ≫ add' W
 g₁ g₂ = add' W (f ≫ g₁) (f ≫ g₂)
参数：f : L.obj X ⟶ L.obj Y；g₁ g₂ : L.obj Y ⟶ L.obj Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Localization.inverts`：inverts : W.IsInvertedBy L
· 使用定理 `CategoryTheory.Localization.exists_leftFraction`：∀ {C : Type u_1} {D : T
ype u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheor
y.Category.{v_2, u_2} D] (L : Categor…
· 使用引理 `CategoryTheory.Localization.exists_leftFraction₂`：exists_leftFraction₂ {
X Y : C} (f f' : L.obj X ⟶ L.obj Y) : exists (φ : W.LeftFraction₂ X Y), f = φ.fs
t.map L (inverts L W) ∧ f' = φ.snd.map…
· 使用定理 `CategoryTheory.MorphismProperty.LeftFraction.hs`：∀ {C : Type u_1} [inst 
: CategoryTheory.Category.{v_1, u_1} C] {W : CategoryTheory.MorphismProperty C} 
{X Y : C}   (self : W.LeftFraction X …
· 使用引理 `CategoryTheory.MorphismProperty.RightFraction₂.exists_leftFraction₂`：exi
sts_leftFraction₂ [W.HasLeftCalculusOfFractions] : exists (ψ : W.LeftFraction₂ X
 Y), φ.f ≫ ψ.s = φ.s ≫ ψ.f ∧ φ.f' ≫ ψ.s = φ.s ≫ ψ.f'
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Localization.Preadditive.add'_eq`：∀ {C : Type u_1} {D : T
ype u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheor
y.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用引理 `CategoryTheory.MorphismProperty.comp_mem`：comp_mem (W : MorphismProperty
 C) [W.IsStableUnderComposition] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : W f) 
(hg : W g) : W (f ≫ g)
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.toIsStableUnderComposit
ion`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheor
y.MorphismProperty C}   [self : W.IsMultiplicative], W.IsStableUn…
· 使用定理 `CategoryTheory.MorphismProperty.HasLeftCalculusOfFractions.toIsMultiplic
ative`：∀ {C : Type u_1} {inst : CategoryTheory.Category.{v_1, u_1} C} {W : Categ
oryTheory.MorphismProperty C}   [self : W.HasLeftCalculusOfFraction…
· 使用定理 `CategoryTheory.MorphismProperty.LeftFraction₂.hs`：∀ {C : Type u_1} [inst
 : CategoryTheory.Category.{v_1, u_1} C] {W : CategoryTheory.MorphismProperty C}
 {X Y : C}   (self : W.LeftFraction₂ X…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `CategoryTheory.MorphismProperty.LeftFraction.map_comp_map_eq_map`：map_co
mp_map_eq_map {X Y Z : C} (z₁ : W.LeftFraction X Y) (z₂ : W.LeftFraction Y Z) (z
₃ : W.LeftFraction z₁.Y' z₂.Y') (h₃ : z₂.f ≫ z₃.s = z₁…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Preadditive.add_comp`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C)   (f f' 
: P ⟶ Q) (g : Q ⟶ R),   C…
· 使用定理 `CategoryTheory.Preadditive.comp_add`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C) (f : P ⟶
 Q)   (g g' : Q ⟶ R),   C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma comp_add' (f : L.obj X ⟶ L.obj Y) (g₁ g₂ : L.obj Y ⟶ L.obj Z) :
    f ≫ add' W g₁ g₂ = add' W (f ≫ g₁) (f ≫ g₂) := by
  obtain ⟨α, hα⟩ := exists_leftFraction L W f
  obtain ⟨β, hβ₁, hβ₂⟩ := exists_leftFraction₂ L W g₁ g₂
  obtain ⟨γ, hγ₁, hγ₂⟩ := (RightFraction₂.mk _ α.hs β.f β.f').exists_leftFraction₂
  dsimp at hγ₁ hγ₂
  rw [add'_eq W g₁ g₂ β hβ₁ hβ₂, add'_eq W (f ≫ g₁) (f ≫ g₂)
    (LeftFraction₂.mk (α.f ≫ γ.f) (α.f ≫ γ.f') (β.s ≫ γ.s) (W.comp_mem _ _ β.hs γ.hs))
    (by simpa only [hα, hβ₁] using! LeftFraction.map_comp_map_eq_map α β.fst γ.fst hγ₁ L)
    (by simpa only [hα, hβ₂] using! LeftFraction.map_comp_map_eq_map α β.snd γ.snd hγ₂ L),
    hα, LeftFraction.map_comp_map_eq_map α β.add γ.add
      (by simp only [add_comp, hγ₁, hγ₂, comp_add])]
  dsimp [LeftFraction₂.add]
  rw [comp_add]

@[simp]
/-
**CategoryTheory.Localization.Preadditive.add'_map** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Localization.Preadditive`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1}
 C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : CategoryTheory.P
readditive C]   {L : CategoryTheory.Functor C D} (W : CategoryTheory.MorphismPro
perty C) [inst_3 : L.IsLocalization W]   [inst_4 : W.HasLeftCalculusOfFractions]
 {X Y : C} (f₁ f₂ : X ⟶ Y),   CategoryTheory.Localization.Preadditive.add' W (L.
map f₁) (L.map f₂) = L.map (f₁ + f₂)
参数：W : CategoryTheory.MorphismProperty C；f₁ f₂ : X ⟶ Y；L.map f₁；L.map f₂；f₁ + f₂
。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `CategoryTheory.MorphismProperty.id_mem`：id_mem (W : MorphismProperty C) 
[W.ContainsIdentities] (X : C) : W (𝟙 X)
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.toContainsIdentities`：∀
 {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheory.Morp
hismProperty C}   [self : W.IsMultiplicative], W.ContainsId…
· 使用定理 `CategoryTheory.MorphismProperty.HasLeftCalculusOfFractions.toIsMultiplic
ative`：∀ {C : Type u_1} {inst : CategoryTheory.Category.{v_1, u_1} C} {W : Categ
oryTheory.MorphismProperty C}   [self : W.HasLeftCalculusOfFraction…
· 使用定理 `CategoryTheory.Localization.inverts`：inverts : W.IsInvertedBy L
· 使用定理 `CategoryTheory.Localization.Preadditive.add'_eq`：∀ {C : Type u_1} {D : T
ype u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheor
y.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.MorphismProperty.LeftFraction.map_ofHom`：map_ofHom (f : X
 ⟶ Y) (L : C ⥤ D) (hL : W.IsInvertedBy L) [W.ContainsIdentities] : (ofHom W f).m
ap L hL = L.map f
-/
lemma add'_map (f₁ f₂ : X ⟶ Y) :
    add' W (L.map f₁) (L.map f₂) = L.map (f₁ + f₂) :=
  (add'_eq W (L.map f₁) (L.map f₂) (LeftFraction₂.mk f₁ f₂ (𝟙 _) (W.id_mem _))
    (LeftFraction.map_ofHom _ _ _ _).symm (LeftFraction.map_ofHom _ _ _ _).symm).trans
    (LeftFraction.map_ofHom _ _ _ _)

variable (L X Y)

/-- The abelian group structure on `L.obj X ⟶ L.obj Y` when `L : C ⥤ D` is a localization
functor, `C` is preadditive and there is a left calculus of fractions. -/
@[instance_reducible]
/-
**CategoryTheory.Localization.Preadditive.addCommGroup'** 是 Mathlib 中的一个定义，位于命名空
间 `CategoryTheory.Localization.Preadditive`。
形式化陈述：addCommGroup' : AddCommGroup (L.obj X ⟶ L.obj Y)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Localization.Preadditive.add'_assoc`：∀ {C : Type u_1} {D 
: Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTh
eory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用引理 `CategoryTheory.Localization.Preadditive.zero_add'`：zero_add' (f : L.obj 
X ⟶ L.obj Y) : add' W (L.map 0) f = f
· 使用定理 `CategoryTheory.Localization.Preadditive.add'_zero`：∀ {C : Type u_1} {D :
 Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryThe
ory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Localization.Preadditive.neg'_add'_self`：∀ {C : Type u_1}
 {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Catego
ryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Localization.Preadditive.add'_comm`：∀ {C : Type u_1} {D :
 Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryThe
ory.Category.{v_2, u_2} D] [inst_2 : Ca…

--- 原说明 ---
The abelian group structure on `L.obj X ⟶ L.obj Y` when `L : C ⥤ D` is a localiz
ation
functor, `C` is preadditive and there is a left calculus of fractions.
-/
noncomputable def addCommGroup' : AddCommGroup (L.obj X ⟶ L.obj Y) := by
  letI : Zero (L.obj X ⟶ L.obj Y) := ⟨L.map 0⟩
  letI : Add (L.obj X ⟶ L.obj Y) := ⟨add' W⟩
  letI : Neg (L.obj X ⟶ L.obj Y) := ⟨neg' W⟩
  exact
    { add_assoc := add'_assoc _
      add_zero := add'_zero _
      add_comm := add'_comm _
      zero_add := zero_add' _
      neg_add_cancel := neg'_add'_self _
      nsmul := nsmulRec
      zsmul := zsmulRec }

variable {X Y}

variable {L}
variable {X' Y' Z' : D} (eX : L.obj X ≅ X') (eY : L.obj Y ≅ Y') (eZ : L.obj Z ≅ Z')

/-- The bijection `(X' ⟶ Y') ≃ (L.obj X ⟶ L.obj Y)` induced by isomorphisms
`eX : L.obj X ≅ X'` and `eY : L.obj Y ≅ Y'`. -/
@[simps]
/-
**CategoryTheory.Localization.Preadditive.homEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Localization.Preadditive`。
形式化陈述：homEquiv : (X' ⟶ Y') ≃ (L.obj X ⟶ L.obj Y) where toFun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The bijection `(X' ⟶ Y') ≃ (L.obj X ⟶ L.obj Y)` induced by isomorphisms
`eX : L.obj X ≅ X'` and `eY : L.obj Y ≅ Y'`.
-/
def homEquiv : (X' ⟶ Y') ≃ (L.obj X ⟶ L.obj Y) where
  toFun f := eX.hom ≫ f ≫ eY.inv
  invFun g := eX.inv ≫ g ≫ eY.hom
  left_inv _ := by simp
  right_inv _ := by simp

/-- The addition of morphisms in `D`, when `L : C ⥤ D` is a localization
functor, `C` is preadditive and there is a left calculus of fractions. -/
/-
**CategoryTheory.Localization.Preadditive.add** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Localization.Preadditive`。
形式化陈述：add (f₁ f₂ : X' ⟶ Y') : X' ⟶ Y'
参数：f₁ f₂ : X' ⟶ Y'。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The addition of morphisms in `D`, when `L : C ⥤ D` is a localization
functor, `C` is preadditive and there is a left calculus of fractions.
-/
noncomputable def add (f₁ f₂ : X' ⟶ Y') : X' ⟶ Y' :=
  (homEquiv eX eY).symm (add' W (homEquiv eX eY f₁) (homEquiv eX eY f₂))

@[reassoc]
/-
**CategoryTheory.Localization.Preadditive.add_comp** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.Localization.Preadditive`。
形式化陈述：add_comp (f₁ f₂ : X' ⟶ Y') (g : Y' ⟶ Z') : add W eX eY f₁ f₂ ≫ g = add W e
X eZ (f₁ ≫ g) (f₂ ≫ g)
参数：f₁ f₂ : X' ⟶ Y'；g : Y' ⟶ Z'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Localization.Preadditive.add'.congr_simp`：∀ {C : Type u_1
} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Categ
oryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Localization.Preadditive.homEquiv_apply`：∀ {C : Type u_1}
 {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Catego
ryTheory.Category.{v_2, u_2} D] {L : Categor…
· 使用定理 `CategoryTheory.Localization.Preadditive.homEquiv_symm_apply`：∀ {C : Type
 u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : C
ategoryTheory.Category.{v_2, u_2} D] {L : Categor…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `CategoryTheory.Localization.Preadditive.add'_comp_assoc`：∀ {C : Type u_1
} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Categ
oryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma add_comp (f₁ f₂ : X' ⟶ Y') (g : Y' ⟶ Z') :
    add W eX eY f₁ f₂ ≫ g = add W eX eZ (f₁ ≫ g) (f₂ ≫ g) := by
  obtain ⟨g, rfl⟩ := (homEquiv eY eZ).symm.surjective g
  simp [add]

@[reassoc]
/-
**CategoryTheory.Localization.Preadditive.comp_add** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.Localization.Preadditive`。
形式化陈述：comp_add (f : X' ⟶ Y') (g₁ g₂ : Y' ⟶ Z') : f ≫ add W eY eZ g₁ g₂ = add W e
X eZ (f ≫ g₁) (f ≫ g₂)
参数：f : X' ⟶ Y'；g₁ g₂ : Y' ⟶ Z'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Localization.Preadditive.homEquiv_symm_apply`：∀ {C : Type
 u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : C
ategoryTheory.Category.{v_2, u_2} D] {L : Categor…
· 使用定理 `CategoryTheory.Localization.Preadditive.add'.congr_simp`：∀ {C : Type u_1
} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Categ
oryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Localization.Preadditive.homEquiv_apply`：∀ {C : Type u_1}
 {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Catego
ryTheory.Category.{v_2, u_2} D] {L : Categor…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `CategoryTheory.Localization.Preadditive.comp_add'_assoc`：∀ {C : Type u_1
} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Categ
oryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma comp_add (f : X' ⟶ Y') (g₁ g₂ : Y' ⟶ Z') :
    f ≫ add W eY eZ g₁ g₂ = add W eX eZ (f ≫ g₁) (f ≫ g₂) := by
  obtain ⟨f, rfl⟩ := (homEquiv eX eY).symm.surjective f
  simp [add]
/-
**CategoryTheory.Localization.Preadditive.add_eq_add** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.Localization.Preadditive`。
形式化陈述：add_eq_add {X'' Y'' : C} (eX' : L.obj X'' ≅ X') (eY' : L.obj Y'' ≅ Y') (f₁
 f₂ : X' ⟶ Y') : add W eX eY f₁ f₂ = add W eX' eY' f₁ f₂
参数：eX' : L.obj X'' ≅ X'；eY' : L.obj Y'' ≅ Y'；f₁ f₂ : X' ⟶ Y'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Localization.Preadditive.comp_add`：comp_add (f : X' ⟶ Y')
 (g₁ g₂ : Y' ⟶ Z') : f ≫ add W eY eZ g₁ g₂ = add W eX eZ (f ≫ g₁) (f ≫ g₂)
· 使用引理 `CategoryTheory.Localization.Preadditive.add_comp`：add_comp (f₁ f₂ : X' ⟶
 Y') (g : Y' ⟶ Z') : add W eX eY f₁ f₂ ≫ g = add W eX eZ (f₁ ≫ g) (f₂ ≫ g)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Localization.Preadditive.add.congr_simp`：∀ {C : Type u_1}
 {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Catego
ryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
lemma add_eq_add {X'' Y'' : C} (eX' : L.obj X'' ≅ X') (eY' : L.obj Y'' ≅ Y')
    (f₁ f₂ : X' ⟶ Y') :
    add W eX eY f₁ f₂ = add W eX' eY' f₁ f₂ := by
  have h₁ := comp_add W eX' eX eY (𝟙 _) f₁ f₂
  have h₂ := add_comp W eX' eY eY' f₁ f₂ (𝟙 _)
  simp only [id_comp] at h₁
  simp only [comp_id] at h₂
  rw [h₁, h₂]

variable (L X' Y') in
/-- The abelian group structure on morphisms in `D`, when `L : C ⥤ D` is a localization
functor, `C` is preadditive and there is a left calculus of fractions. -/
@[instance_reducible]
/-
**CategoryTheory.Localization.Preadditive.addCommGroup** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.Localization.Preadditive`。
形式化陈述：addCommGroup : AddCommGroup (X' ⟶ Y')
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Localization.essSurj`：essSurj (W) [L.IsLocalization W] : 
L.EssSurj

--- 原说明 ---
The abelian group structure on morphisms in `D`, when `L : C ⥤ D` is a localizat
ion
functor, `C` is preadditive and there is a left calculus of fractions.
-/
noncomputable def addCommGroup : AddCommGroup (X' ⟶ Y') := by
  have := Localization.essSurj L W
  letI := addCommGroup' L W (L.objPreimage X') (L.objPreimage Y')
  exact Equiv.addCommGroup (homEquiv (L.objObjPreimageIso X') (L.objObjPreimageIso Y'))
/-
**CategoryTheory.Localization.Preadditive.add_eq** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.Localization.Preadditive`。
形式化陈述：add_eq (f₁ f₂ : X' ⟶ Y') : letI
参数：f₁ f₂ : X' ⟶ Y'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Localization.Preadditive.add_eq_add`：add_eq_add {X'' Y'' 
: C} (eX' : L.obj X'' ≅ X') (eY' : L.obj Y'' ≅ Y') (f₁ f₂ : X' ⟶ Y') : add W eX 
eY f₁ f₂ = add W eX' eY' f₁ f₂
· 使用定理 `CategoryTheory.Localization.essSurj`：essSurj (W) [L.IsLocalization W] : 
L.EssSurj
-/
lemma add_eq (f₁ f₂ : X' ⟶ Y') :
    letI := addCommGroup L W X' Y'
    f₁ + f₂ = add W eX eY f₁ f₂ := by
  apply add_eq_add

variable (L)
/-
**CategoryTheory.Localization.Preadditive.map_add** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.Localization.Preadditive`。
形式化陈述：map_add (f₁ f₂ : X ⟶ Y) : letI
参数：f₁ f₂ : X ⟶ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Localization.Preadditive.add_eq`：add_eq (f₁ f₂ : X' ⟶ Y')
 : letI
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `CategoryTheory.Localization.Preadditive.add'.congr_simp`：∀ {C : Type u_1
} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Categ
oryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Localization.Preadditive.homEquiv_apply`：∀ {C : Type u_1}
 {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Catego
ryTheory.Category.{v_2, u_2} D] {L : Categor…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Localization.Preadditive.add'_map`：∀ {C : Type u_1} {D : 
Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheo
ry.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Localization.Preadditive.homEquiv_symm_apply`：∀ {C : Type
 u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : C
ategoryTheory.Category.{v_2, u_2} D] {L : Categor…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_add (f₁ f₂ : X ⟶ Y) :
    letI := addCommGroup L W (L.obj X) (L.obj Y)
    L.map (f₁ + f₂) = L.map f₁ + L.map f₂ := by
  rw [add_eq W (Iso.refl _) (Iso.refl _) (L.map f₁) (L.map f₂)]
  simp [add]

end ImplementationDetails

end Preadditive

variable [W.HasLeftCalculusOfFractions]

/-- The preadditive structure on `D`, when `L : C ⥤ D` is a localization
functor, `C` is preadditive and there is a left calculus of fractions. -/
@[instance_reducible]
/-
**CategoryTheory.Localization.preadditive** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Localization`。
形式化陈述：preadditive : Preadditive D where homGroup
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The preadditive structure on `D`, when `L : C ⥤ D` is a localization
functor, `C` is preadditive and there is a left calculus of fractions.
-/
noncomputable def preadditive : Preadditive D where
  homGroup := Preadditive.addCommGroup L W
  add_comp _ _ _ _ _ _ := by apply Preadditive.add_comp
  comp_add _ _ _ _ _ _ := by apply Preadditive.comp_add
/-
**CategoryTheory.Localization.functor_additive** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.Localization`。
形式化陈述：functor_additive : letI
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Localization.Preadditive.map_add`：map_add (f₁ f₂ : X ⟶ Y)
 : letI
-/
lemma functor_additive :
    letI := preadditive L W
    L.Additive :=
  letI := preadditive L W
  ⟨by apply Preadditive.map_add⟩

attribute [irreducible] preadditive

set_option backward.isDefEq.respectTransparency false in
include W in
/-
**CategoryTheory.Localization.functor_additive_iff** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.Localization`。
形式化陈述：functor_additive_iff {E : Type*} [Category* E] [Preadditive E] [Preadditiv
e D] [L.Additive] (G : D ⥤ E) : G.Additive ↔ (L ⋙ G).Additive
参数：G : D ⥤ E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.instAdditiveComp`：∀ {C : Type u_1} {D : Type u_2}
 [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.Catego
ry.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Localization.inverts`：inverts : W.IsInvertedBy L
· 使用引理 `CategoryTheory.Localization.exists_leftFraction₂`：exists_leftFraction₂ {
X Y : C} (f f' : L.obj X ⟶ L.obj Y) : exists (φ : W.LeftFraction₂ X Y), f = φ.fs
t.map L (inverts L W) ∧ f' = φ.snd.map…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.MorphismProperty.LeftFraction₂.map_add`：map_add (F : C ⥤ 
D) (hF : W.IsInvertedBy F) [Preadditive D] [F.Additive] : φ.add.map F hF = φ.fst
.map F hF + φ.snd.map F hF
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.strongMono_of_isIso`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {P Q : C} (f : Q ⟶ P) [CategoryTheory.IsIso f],   CategoryT
heory.StrongMono f
· 使用定理 `CategoryTheory.MorphismProperty.instIsIsoMapS`：∀ {C : Type u_1} {D : Typ
e u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.
Category.{v_2, u_2} D] (L : Categor…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Preadditive.add_comp`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C)   (f f' 
: P ⟶ Q) (g : Q ⟶ R),   C…
· 使用引理 `CategoryTheory.MorphismProperty.LeftFraction.map_comp_map_s`：map_comp_ma
p_s (φ : W.LeftFraction X Y) (L : C ⥤ D) (hL : W.IsInvertedBy L) : φ.map L hL ≫ 
L.map φ.s = L.map φ.f
· 使用定理 `CategoryTheory.Functor.comp_map`：comp_map (F : C ⥤ D) (G : D ⥤ E) {X Y :
 C} (f : X ⟶ Y) : (F ⋙ G).map f = G.map (F.map f)
· 使用定理 `CategoryTheory.Functor.map_add`：map_add {X Y : C} {f g : X ⟶ Y} : F.map 
(f + g) = F.map f + F.map g
· 使用定理 `CategoryTheory.Localization.essSurj`：essSurj (W) [L.IsLocalization W] : 
L.EssSurj
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.StrongEpi.epi`：∀ {C : Type u} {inst : CategoryTheory.Cate
gory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongEpi f],   Cate
goryTheory.Epi f
· 使用定理 `CategoryTheory.strongEpi_of_isIso`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] {P Q : C} (f : P ⟶ Q) [CategoryTheory.IsIso f],   CategoryTh
eory.StrongEpi f
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.Preadditive.comp_add`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C) (f : P ⟶
 Q)   (g g' : Q ⟶ R),   C…
-/
lemma functor_additive_iff {E : Type*} [Category* E] [Preadditive E] [Preadditive D] [L.Additive]
    (G : D ⥤ E) :
    G.Additive ↔ (L ⋙ G).Additive := by
  constructor
  · intro
    infer_instance
  · intro h
    suffices ∀ ⦃X Y : C⦄ (f g : L.obj X ⟶ L.obj Y), G.map (f + g) = G.map f + G.map g by
      refine ⟨fun {X Y f g} => ?_⟩
      have hL := essSurj L W
      have eq := this ((L.objObjPreimageIso X).hom ≫ f ≫ (L.objObjPreimageIso Y).inv)
        ((L.objObjPreimageIso X).hom ≫ g ≫ (L.objObjPreimageIso Y).inv)
      rw [Functor.map_comp, Functor.map_comp, Functor.map_comp, Functor.map_comp,
        ← comp_add, ← comp_add, ← add_comp, ← add_comp, Functor.map_comp, Functor.map_comp] at eq
      rw [← cancel_mono (G.map (L.objObjPreimageIso Y).inv),
        ← cancel_epi (G.map (L.objObjPreimageIso X).hom), eq]
    intro X Y f g
    obtain ⟨φ, rfl, rfl⟩ := exists_leftFraction₂ L W f g
    rw [← φ.map_add L (inverts L W), ← cancel_mono (G.map (L.map φ.s)), ← G.map_comp,
      add_comp, ← G.map_comp, ← G.map_comp, LeftFraction.map_comp_map_s,
      LeftFraction.map_comp_map_s, LeftFraction.map_comp_map_s, ← Functor.comp_map,
      Functor.map_add, Functor.comp_map, Functor.comp_map]
/-
**CategoryTheory.Localization.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Localiz
ation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : Preadditive W.Localization := preadditive W.Q W
/-
**CategoryTheory.Localization.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Localiz
ation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : W.Q.Additive := functor_additive W.Q W
/-
**CategoryTheory.Localization.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Localiz
ation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasZeroObject C] : HasZeroObject W.Localization := W.Q.hasZeroObject_of_additive

variable [W.HasLocalization]
/-
**CategoryTheory.Localization.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Localiz
ation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : Preadditive W.Localization' := preadditive W.Q' W
/-
**CategoryTheory.Localization.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Localiz
ation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : W.Q'.Additive := functor_additive W.Q' W
/-
**CategoryTheory.Localization.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Localiz
ation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasZeroObject C] : HasZeroObject W.Localization' := W.Q'.hasZeroObject_of_additive

end Localization

/-
**CategoryTheory.Functor.faithful_of_comp_cancel_zero_of_hasLeftCalculusOfFracti
ons** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1}
 C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : CategoryTheory.P
readditive C]   (L : CategoryTheory.Functor C D) (W : CategoryTheory.MorphismPro
perty C) [L.IsLocalization W] {E : Type u_3}   [inst_4 : CategoryTheory.Category
.{v_3, u_3} E] (F : CategoryTheory.Functor D E) [W.HasLeftCalculusOfFractions]  
 [inst_6 : CategoryTheory.Preadditive D] [inst_7 : CategoryTheory.Preadditive E]
 [L.Additive] [F.Additive],   (∀ ⦃X₁ X₂ : C⦄ (f : X₁ ⟶ X₂), F.map (L.map f) = 0 
→ L.map f = 0) → F.Faithful
参数：L : CategoryTheory.Functor C D；W : CategoryTheory.MorphismProperty C；F : Cate
goryTheory.Functor D E；∀ ⦃X₁ X₂ : C⦄ (f : X₁ ⟶ X₂), F.map (L.map f) = 0 → L.map 
f = 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.faithful_of_comp_of_hasLeftCalculusOfFractions`：∀
 {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [
inst_1 : CategoryTheory.Category.{v_2, u_2} D] (L : Categor…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `CategoryTheory.Functor.map_sub`：map_sub {X Y : C} {f g : X ⟶ Y} : F.map 
(f - g) = F.map f - F.map g
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
-/
lemma Functor.faithful_of_comp_cancel_zero_of_hasLeftCalculusOfFractions
    {E : Type*} [Category* E] (F : D ⥤ E)
    [W.HasLeftCalculusOfFractions]
    [Preadditive D] [Preadditive E] [L.Additive] [F.Additive]
    (h : ∀ ⦃X₁ X₂ : C⦄ (f : X₁ ⟶ X₂), F.map (L.map f) = 0 → L.map f = 0) :
    Faithful F :=
  faithful_of_comp_of_hasLeftCalculusOfFractions L W F
    (fun X₁ X₂ f g hfg => by
      rw [← sub_eq_zero, ← L.map_sub]
      exact h _ (by rw [L.map_sub, F.map_sub, hfg, sub_self]))

end CategoryTheory

