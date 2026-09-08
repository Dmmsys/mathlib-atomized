/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Subobject.Lattice

/-!
# Specific subobjects

We define `equalizerSubobject`, `kernelSubobject` and `imageSubobject`, which are the subobjects
represented by the equalizer, kernel and image of (a pair of) morphism(s) and provide conditions
for `P.factors f`, where `P` is one of these special subobjects.

TODO: an iff characterisation of `(imageSubobject f).Factors h`

-/

@[expose] public section

universe v u

noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits CategoryTheory.Subobject Opposite

variable {C : Type u} [Category.{v} C] {X Y Z : C}

namespace CategoryTheory

namespace Limits

section Pullback

variable {W : C} (f : X ⟶ Y) [HasPullbacks C]

/-
**CategoryTheory.Limits.pullback_factors** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Limits`。
形式化陈述：pullback_factors (y : Subobject Y) (h : W ⟶ X) (hF : y.Factors (h ≫ f)) : 
Subobject.Factors ((Subobject.pullback f).obj y) h
参数：y : Subobject Y；h : W ⟶ X；hF : y.Factors (h ≫ f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subobject.factorThru_arrow`：factorThru_arrow {X Y : C} (P
 : Subobject Y) (f : X ⟶ Y) (h : Factors P f) : P.factorThru f h ≫ P.arrow = f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.Subobject.factors_iff`：factors_iff {X Y : C} (P : Subobje
ct Y) (f : X ⟶ Y) : P.Factors f ↔ (representative.obj P).Factors f
· 使用定理 `CategoryTheory.Subobject.isPullback`：isPullback (f : X ⟶ Y) (y : Subobje
ct Y) : IsPullback (pullbackπ f y) ((pullback f).obj y).arrow y.arrow f
· 使用引理 `CategoryTheory.IsPullback.lift_snd`：lift_snd (hP : IsPullback fst snd f 
g) {W : C} (h : W ⟶ X) (k : W ⟶ Y) (w : h ≫ f = k ≫ g) : hP.lift h k w ≫ snd = k
-/
theorem pullback_factors (y : Subobject Y) (h : W ⟶ X) (hF : y.Factors (h ≫ f)) :
    Subobject.Factors ((Subobject.pullback f).obj y) h :=
  let h' := Subobject.factorThru _ _ hF
  let w := Subobject.factorThru_arrow _ _ hF
  (factors_iff _ _).mpr
    ⟨(Subobject.isPullback f y).lift h' h w,
      (Subobject.isPullback f y).lift_snd h' h w⟩
/-
**CategoryTheory.Limits.pullback_factors_iff** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Limits`。
形式化陈述：pullback_factors_iff (y : Subobject Y) (h : W ⟶ X) : Subobject.Factors ((S
ubobject.pullback f).obj y) h ↔ y.Factors (h ≫ f)
参数：y : Subobject Y；h : W ⟶ X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Subobject.factors_iff`：factors_iff {X Y : C} (P : Subobje
ct Y) (f : X ⟶ Y) : P.Factors f ↔ (representative.obj P).Factors f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.CommSq.w`：∀ {C : Type u_1} [inst : CategoryTheory.Categor
y.{v_1, u_1} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z}   {i : Y ⟶ Z},
   CategoryTh…
· 使用定理 `CategoryTheory.IsPullback.toCommSq`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {P X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z}   
{g : Y ⟶ Z}, CategoryThe…
· 使用定理 `CategoryTheory.Subobject.isPullback`：isPullback (f : X ⟶ Y) (y : Subobje
ct Y) : IsPullback (pullbackπ f y) ((pullback f).obj y).arrow y.arrow f
· 使用定理 `CategoryTheory.Subobject.factorThru_arrow_assoc`：∀ {C : Type u₁} [inst :
 CategoryTheory.Category.{v₁, u₁} C] {X Y : C} (P : CategoryTheory.Subobject Y) 
(f : X ⟶ Y)   (h : P.Factors f) {Z : …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.pullback_factors`：pullback_factors (y : Subobject 
Y) (h : W ⟶ X) (hF : y.Factors (h ≫ f)) : Subobject.Factors ((Subobject.pullback
 f).obj y) h
-/
theorem pullback_factors_iff (y : Subobject Y) (h : W ⟶ X) :
    Subobject.Factors ((Subobject.pullback f).obj y) h ↔ y.Factors (h ≫ f) := by
  refine ⟨fun hf ↦ ?_, fun hF ↦ pullback_factors f y h hF⟩
  rw [factors_iff]
  use Subobject.factorThru _ _ hf ≫ Subobject.pullbackπ f y
  simp [(Subobject.isPullback f y).w]

end Pullback

section Equalizer

variable (f g : X ⟶ Y) [HasEqualizer f g]

/-- The equalizer of morphisms `f g : X ⟶ Y` as a `Subobject X`. -/
/-
**CategoryTheory.Limits.equalizerSubobject** 是 Mathlib 中的一个缩写定义，位于命名空间 `Category
Theory.Limits`。
形式化陈述：equalizerSubobject : Subobject X
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.equalizer.ι_mono`：∀ {C : Type u} {X Y : C} [inst :
 CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y}   [inst_1 : CategoryTheory.Limi
ts.HasEqualizer f g], Catego…

--- 原说明 ---
The equalizer of morphisms `f g : X ⟶ Y` as a `Subobject X`.
-/
abbrev equalizerSubobject : Subobject X :=
  Subobject.mk (equalizer.ι f g)

/-- The underlying object of `equalizerSubobject f g` is (up to isomorphism!)
the same as the chosen object `equalizer f g`. -/
/-
**CategoryTheory.Limits.equalizerSubobjectIso** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Limits`。
形式化陈述：equalizerSubobjectIso : (equalizerSubobject f g : C) ≅ equalizer f g
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.equalizer.ι_mono`：∀ {C : Type u} {X Y : C} [inst :
 CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y}   [inst_1 : CategoryTheory.Limi
ts.HasEqualizer f g], Catego…

--- 原说明 ---
The underlying object of `equalizerSubobject f g` is (up to isomorphism!)
the same as the chosen object `equalizer f g`.
-/
def equalizerSubobjectIso : (equalizerSubobject f g : C) ≅ equalizer f g :=
  Subobject.underlyingIso (equalizer.ι f g)

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.equalizerSubobject_arrow** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Limits`。
形式化陈述：equalizerSubobject_arrow : (equalizerSubobjectIso f g).hom ≫ equalizer.ι f
 g = (equalizerSubobject f g).arrow
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.equalizer.ι_mono`：∀ {C : Type u} {X Y : C} [inst :
 CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y}   [inst_1 : CategoryTheory.Limi
ts.HasEqualizer f g], Catego…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Subobject.underlyingIso_hom_comp_eq_mk`：underlyingIso_hom
_comp_eq_mk {X Y : C} (f : X ⟶ Y) [Mono f] : (underlyingIso f).hom ≫ f = (mk f).
arrow
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem equalizerSubobject_arrow :
    (equalizerSubobjectIso f g).hom ≫ equalizer.ι f g = (equalizerSubobject f g).arrow := by
  simp [equalizerSubobjectIso]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.equalizerSubobject_arrow'** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Limits`。
形式化陈述：equalizerSubobject_arrow' : (equalizerSubobjectIso f g).inv ≫ (equalizerSu
bobject f g).arrow = equalizer.ι f g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Subobject.underlyingIso_arrow`：underlyingIso_arrow {X Y :
 C} (f : X ⟶ Y) [Mono f] : (underlyingIso f).inv ≫ (Subobject.mk f).arrow = f
· 使用定理 `CategoryTheory.Limits.equalizer.ι_mono`：∀ {C : Type u} {X Y : C} [inst :
 CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y}   [inst_1 : CategoryTheory.Limi
ts.HasEqualizer f g], Catego…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem equalizerSubobject_arrow' :
    (equalizerSubobjectIso f g).inv ≫ (equalizerSubobject f g).arrow = equalizer.ι f g := by
  simp [equalizerSubobjectIso]

@[reassoc]
/-
**CategoryTheory.Limits.equalizerSubobject_arrow_comp** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.Limits`。
形式化陈述：equalizerSubobject_arrow_comp : (equalizerSubobject f g).arrow ≫ f = (equa
lizerSubobject f g).arrow ≫ g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.equalizerSubobject_arrow`：equalizerSubobject_arrow
 : (equalizerSubobjectIso f g).hom ≫ equalizer.ι f g = (equalizerSubobject f g).
arrow
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.equalizer.condition`：∀ {C : Type u} {X Y : C} [ins
t : CategoryTheory.Category.{v, u} C] (f g : X ⟶ Y)   [inst_1 : CategoryTheory.L
imits.HasEqualizer f g],   Cate…
-/
theorem equalizerSubobject_arrow_comp :
    (equalizerSubobject f g).arrow ≫ f = (equalizerSubobject f g).arrow ≫ g := by
  rw [← equalizerSubobject_arrow, Category.assoc, Category.assoc, equalizer.condition]

@[simp]
/-
**CategoryTheory.Limits.equalizerSubobject_of_self** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Limits`。
形式化陈述：equalizerSubobject_of_self : equalizerSubobject f f = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subobject.mk_eq_top_of_isIso`：mk_eq_top_of_isIso {X Y : C
} (f : X ⟶ Y) [IsIso f] : mk f = ⊤
· 使用定理 `CategoryTheory.Limits.equalizer.ι_of_self`：∀ {C : Type u} {X Y : C} [ins
t : CategoryTheory.Category.{v, u} C] (f : X ⟶ Y),   CategoryTheory.IsIso (Categ
oryTheory.Limits.equalizer.ι f …
-/
theorem equalizerSubobject_of_self : equalizerSubobject f f = ⊤ := by
  apply mk_eq_top_of_isIso

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Limits.equalizerSubobject_factors** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Limits`。
形式化陈述：equalizerSubobject_factors {W : C} (h : W ⟶ X) (w : h ≫ f = h ≫ g) : (equa
lizerSubobject f g).Factors h
参数：h : W ⟶ X；w : h ≫ f = h ≫ g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.equalizer.ι_mono`：∀ {C : Type u} {X Y : C} [inst :
 CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y}   [inst_1 : CategoryTheory.Limi
ts.HasEqualizer f g], Catego…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem equalizerSubobject_factors {W : C} (h : W ⟶ X) (w : h ≫ f = h ≫ g) :
    (equalizerSubobject f g).Factors h :=
  ⟨equalizer.lift h w, by simp⟩
/-
**CategoryTheory.Limits.equalizerSubobject_factors_iff** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.Limits`。
形式化陈述：equalizerSubobject_factors_iff {W : C} (h : W ⟶ X) : (equalizerSubobject f
 g).Factors h ↔ h ≫ f = h ≫ g
参数：h : W ⟶ X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Subobject.factorThru_arrow`：factorThru_arrow {X Y : C} (P
 : Subobject Y) (f : X ⟶ Y) (h : Factors P f) : P.factorThru f h ≫ P.arrow = f
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.equalizerSubobject_arrow_comp`：equalizerSubobject_
arrow_comp : (equalizerSubobject f g).arrow ≫ f = (equalizerSubobject f g).arrow
 ≫ g
· 使用定理 `CategoryTheory.Limits.equalizerSubobject_factors`：equalizerSubobject_fac
tors {W : C} (h : W ⟶ X) (w : h ≫ f = h ≫ g) : (equalizerSubobject f g).Factors 
h
-/
theorem equalizerSubobject_factors_iff {W : C} (h : W ⟶ X) :
    (equalizerSubobject f g).Factors h ↔ h ≫ f = h ≫ g :=
  ⟨fun w => by
    rw [← Subobject.factorThru_arrow _ _ w, Category.assoc, equalizerSubobject_arrow_comp,
      Category.assoc],
    equalizerSubobject_factors f g h⟩

@[simp]
/-
**CategoryTheory.Limits.pullback_equalizer** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTh
eory.Limits`。
形式化陈述：pullback_equalizer {W : C} (h : W ⟶ X) [HasPullbacks C] : (Subobject.pullb
ack h).obj (equalizerSubobject f g) = equalizerSubobject (h ≫ f) (h ≫ g)
参数：h : W ⟶ X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Subobject.skeletal`：skeletal (X : C) : Skeletal (Subobjec
t X)
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.equalizerSubobject_factors`：equalizerSubobject_fac
tors {W : C} (h : W ⟶ X) (w : h ≫ f = h ≫ g) : (equalizerSubobject f g).Factors 
h
· 使用定理 `CategoryTheory.CommSq.w`：∀ {C : Type u_1} [inst : CategoryTheory.Categor
y.{v_1, u_1} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z}   {i : Y ⟶ Z},
   CategoryTh…
· 使用定理 `CategoryTheory.IsPullback.toCommSq`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {P X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z}   
{g : Y ⟶ Z}, CategoryThe…
· 使用定理 `CategoryTheory.Subobject.isPullback`：isPullback (f : X ⟶ Y) (y : Subobje
ct Y) : IsPullback (pullbackπ f y) ((pullback f).obj y).arrow y.arrow f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Mathlib.Tactic.Reassoc.eq_whisker'`：eq_whisker' {C : Type*} [Category* C
] {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) : f ≫ h = g ≫ h
· 使用定理 `CategoryTheory.Limits.equalizerSubobject_arrow_comp`：equalizerSubobject_
arrow_comp : (equalizerSubobject f g).arrow ≫ f = (equalizerSubobject f g).arrow
 ≫ g
· 使用定理 `CategoryTheory.Limits.pullback_factors`：pullback_factors (y : Subobject 
Y) (h : W ⟶ X) (hF : y.Factors (h ≫ f)) : Subobject.Factors ((Subobject.pullback
 f).obj y) h
-/
lemma pullback_equalizer {W : C} (h : W ⟶ X) [HasPullbacks C] :
  (Subobject.pullback h).obj (equalizerSubobject f g) =
    equalizerSubobject (h ≫ f) (h ≫ g) := by
  refine skeletal _ ⟨iso_of_both_ways (homOfFactors ?_) (homOfFactors ?_)⟩
  · apply equalizerSubobject_factors
    have := (Subobject.isPullback h (equalizerSubobject f g)).w
    rw [← reassoc_of% (Subobject.isPullback h (equalizerSubobject f g)).w,
      ← reassoc_of% (Subobject.isPullback h (equalizerSubobject f g)).w,
      equalizerSubobject_arrow_comp]
  · apply pullback_factors
    apply equalizerSubobject_factors
    rw [assoc, assoc, equalizerSubobject_arrow_comp]

end Equalizer

section Kernel

variable [HasZeroMorphisms C] (f : X ⟶ Y) [HasKernel f]

/-- The kernel of a morphism `f : X ⟶ Y` as a `Subobject X`. -/
/-
**CategoryTheory.Limits.kernelSubobject** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryThe
ory.Limits`。
形式化陈述：kernelSubobject : Subobject X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The kernel of a morphism `f : X ⟶ Y` as a `Subobject X`.
-/
abbrev kernelSubobject : Subobject X :=
  Subobject.mk (kernel.ι f)

/-- The underlying object of `kernelSubobject f` is (up to isomorphism!)
the same as the chosen object `kernel f`. -/
/-
**CategoryTheory.Limits.kernelSubobjectIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Limits`。
形式化陈述：kernelSubobjectIso : (kernelSubobject f : C) ≅ kernel f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The underlying object of `kernelSubobject f` is (up to isomorphism!)
the same as the chosen object `kernel f`.
-/
def kernelSubobjectIso : (kernelSubobject f : C) ≅ kernel f :=
  Subobject.underlyingIso (kernel.ι f)

@[reassoc (attr := simp), elementwise (attr := simp)]
/-
**CategoryTheory.Limits.kernelSubobject_arrow** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Limits`。
形式化陈述：kernelSubobject_arrow : (kernelSubobjectIso f).hom ≫ kernel.ι f = (kernelS
ubobject f).arrow
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Subobject.underlyingIso_hom_comp_eq_mk`：underlyingIso_hom
_comp_eq_mk {X Y : C} (f : X ⟶ Y) [Mono f] : (underlyingIso f).hom ≫ f = (mk f).
arrow
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem kernelSubobject_arrow :
    (kernelSubobjectIso f).hom ≫ kernel.ι f = (kernelSubobject f).arrow := by
  simp [kernelSubobjectIso]

@[reassoc (attr := simp), elementwise (attr := simp)]
/-
**CategoryTheory.Limits.kernelSubobject_arrow'** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Limits`。
形式化陈述：kernelSubobject_arrow' : (kernelSubobjectIso f).inv ≫ (kernelSubobject f).
arrow = kernel.ι f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Subobject.underlyingIso_arrow`：underlyingIso_arrow {X Y :
 C} (f : X ⟶ Y) [Mono f] : (underlyingIso f).inv ≫ (Subobject.mk f).arrow = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem kernelSubobject_arrow' :
    (kernelSubobjectIso f).inv ≫ (kernelSubobject f).arrow = kernel.ι f := by
  simp [kernelSubobjectIso]

@[reassoc (attr := simp), elementwise (attr := simp)]
/-
**CategoryTheory.Limits.kernelSubobject_arrow_comp** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Limits`。
形式化陈述：kernelSubobject_arrow_comp : (kernelSubobject f).arrow ≫ f = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.kernelSubobject_arrow`：kernelSubobject_arrow : (ke
rnelSubobjectIso f).hom ≫ kernel.ι f = (kernelSubobject f).arrow
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.kernel.condition`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X 
Y : C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem kernelSubobject_arrow_comp : (kernelSubobject f).arrow ≫ f = 0 := by
  rw [← kernelSubobject_arrow]
  simp only [Category.assoc, kernel.condition, comp_zero]
/-
**CategoryTheory.Limits.kernelSubobject_factors** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Limits`。
形式化陈述：kernelSubobject_factors {W : C} (h : W ⟶ X) (w : h ≫ f = 0) : (kernelSubob
ject f).Factors h
参数：h : W ⟶ X；w : h ≫ f = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.kernel.lift_ι`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X Y :
 C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem kernelSubobject_factors {W : C} (h : W ⟶ X) (w : h ≫ f = 0) :
    (kernelSubobject f).Factors h :=
  ⟨kernel.lift _ h w, by simp⟩
/-
**CategoryTheory.Limits.kernelSubobject_factors_iff** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.Limits`。
形式化陈述：kernelSubobject_factors_iff {W : C} (h : W ⟶ X) : (kernelSubobject f).Fact
ors h ↔ h ≫ f = 0
参数：h : W ⟶ X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Subobject.factorThru_arrow`：factorThru_arrow {X Y : C} (P
 : Subobject Y) (f : X ⟶ Y) (h : Factors P f) : P.factorThru f h ≫ P.arrow = f
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.kernelSubobject_arrow_comp`：kernelSubobject_arrow_
comp : (kernelSubobject f).arrow ≫ f = 0
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.Limits.kernelSubobject_factors`：kernelSubobject_factors {
W : C} (h : W ⟶ X) (w : h ≫ f = 0) : (kernelSubobject f).Factors h
-/
theorem kernelSubobject_factors_iff {W : C} (h : W ⟶ X) :
    (kernelSubobject f).Factors h ↔ h ≫ f = 0 :=
  ⟨fun w => by
    rw [← Subobject.factorThru_arrow _ _ w, Category.assoc, kernelSubobject_arrow_comp,
      comp_zero],
    kernelSubobject_factors f h⟩

/-- A factorisation of `h : W ⟶ X` through `kernelSubobject f`, assuming `h ≫ f = 0`. -/
/-
**CategoryTheory.Limits.factorThruKernelSubobject** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Limits`。
形式化陈述：factorThruKernelSubobject {W : C} (h : W ⟶ X) (w : h ≫ f = 0) : W ⟶ kernel
Subobject f
参数：h : W ⟶ X；w : h ≫ f = 0。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.kernelSubobject_factors`：kernelSubobject_factors {
W : C} (h : W ⟶ X) (w : h ≫ f = 0) : (kernelSubobject f).Factors h

--- 原说明 ---
A factorisation of `h : W ⟶ X` through `kernelSubobject f`, assuming `h ≫ f = 0`
.
-/
def factorThruKernelSubobject {W : C} (h : W ⟶ X) (w : h ≫ f = 0) : W ⟶ kernelSubobject f :=
  (kernelSubobject f).factorThru h (kernelSubobject_factors f h w)

@[simp]
/-
**CategoryTheory.Limits.factorThruKernelSubobject_comp_arrow** 是 Mathlib 中的一个定理，
位于命名空间 `CategoryTheory.Limits`。
形式化陈述：factorThruKernelSubobject_comp_arrow {W : C} (h : W ⟶ X) (w : h ≫ f = 0) :
 factorThruKernelSubobject f h w ≫ (kernelSubobject f).arrow = h
参数：h : W ⟶ X；w : h ≫ f = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Limits.kernelSubobject_factors`：kernelSubobject_factors {
W : C} (h : W ⟶ X) (w : h ≫ f = 0) : (kernelSubobject f).Factors h
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Subobject.factorThru_arrow`：factorThru_arrow {X Y : C} (P
 : Subobject Y) (f : X ⟶ Y) (h : Factors P f) : P.factorThru f h ≫ P.arrow = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem factorThruKernelSubobject_comp_arrow {W : C} (h : W ⟶ X) (w : h ≫ f = 0) :
    factorThruKernelSubobject f h w ≫ (kernelSubobject f).arrow = h := by
  dsimp [factorThruKernelSubobject]
  simp

@[simp]
/-
**CategoryTheory.Limits.factorThruKernelSubobject_comp_kernelSubobjectIso** 是 Ma
thlib 中的一个定理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：factorThruKernelSubobject_comp_kernelSubobjectIso {W : C} (h : W ⟶ X) (w :
 h ≫ f = 0) : factorThruKernelSubobject f h w ≫ (kernelSubobjectIso f).hom = ker
nel.lift f h w
参数：h : W ⟶ X；w : h ≫ f = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.Limits.equalizer.ι_mono`：∀ {C : Type u} {X Y : C} [inst :
 CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y}   [inst_1 : CategoryTheory.Limi
ts.HasEqualizer f g], Catego…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.kernelSubobject_arrow`：kernelSubobject_arrow : (ke
rnelSubobjectIso f).hom ≫ kernel.ι f = (kernelSubobject f).arrow
· 使用定理 `CategoryTheory.Limits.factorThruKernelSubobject_comp_arrow`：factorThruKe
rnelSubobject_comp_arrow {W : C} (h : W ⟶ X) (w : h ≫ f = 0) : factorThruKernelS
ubobject f h w ≫ (kernelSubobject f).arrow = h
· 使用定理 `CategoryTheory.Limits.kernel.lift_ι`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X Y :
 C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem factorThruKernelSubobject_comp_kernelSubobjectIso {W : C} (h : W ⟶ X) (w : h ≫ f = 0) :
    factorThruKernelSubobject f h w ≫ (kernelSubobjectIso f).hom = kernel.lift f h w :=
  (cancel_mono (kernel.ι f)).1 <| by simp

section

variable {f} {X' Y' : C} {f' : X' ⟶ Y'} [HasKernel f']

set_option backward.isDefEq.respectTransparency false in
/-- A commuting square induces a morphism between the kernel subobjects. -/
/-
**CategoryTheory.Limits.kernelSubobjectMap** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Limits`。
形式化陈述：kernelSubobjectMap (sq : Arrow.mk f ⟶ Arrow.mk f') : (kernelSubobject f : 
C) ⟶ (kernelSubobject f' : C)
参数：sq : Arrow.mk f ⟶ Arrow.mk f'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A commuting square induces a morphism between the kernel subobjects.
-/
def kernelSubobjectMap (sq : Arrow.mk f ⟶ Arrow.mk f') :
    (kernelSubobject f : C) ⟶ (kernelSubobject f' : C) :=
  Subobject.factorThru _ ((kernelSubobject f).arrow ≫ sq.left)
    (kernelSubobject_factors _ _ (by simp))

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp), elementwise (attr := simp)]
/-
**CategoryTheory.Limits.kernelSubobjectMap_arrow** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Limits`。
形式化陈述：kernelSubobjectMap_arrow (sq : Arrow.mk f ⟶ Arrow.mk f') : kernelSubobject
Map sq ≫ (kernelSubobject f').arrow = (kernelSubobject f).arrow ≫ sq.left
参数：sq : Arrow.mk f ⟶ Arrow.mk f'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Subobject.factorThru_arrow`：factorThru_arrow {X Y : C} (P
 : Subobject Y) (f : X ⟶ Y) (h : Factors P f) : P.factorThru f h ≫ P.arrow = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
`respectTransparency.types true` changes the auto-generated lemmas' signature
-/
theorem kernelSubobjectMap_arrow (sq : Arrow.mk f ⟶ Arrow.mk f') :
    kernelSubobjectMap sq ≫ (kernelSubobject f').arrow = (kernelSubobject f).arrow ≫ sq.left := by
  simp [kernelSubobjectMap]

set_option backward.defeqAttrib.useBackward true in
@[simp]
/-
**CategoryTheory.Limits.kernelSubobjectMap_id** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Limits`。
形式化陈述：kernelSubobjectMap_id : kernelSubobjectMap (𝟙 (Arrow.mk f)) = 𝟙 _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subobject.eq_of_comp_arrow_eq`：eq_of_comp_arrow_eq {X Y :
 C} {P : Subobject Y} {f g : X ⟶ P} (h : f ≫ P.arrow = g ≫ P.arrow) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.kernelSubobjectMap_arrow`：kernelSubobjectMap_arrow
 (sq : Arrow.mk f ⟶ Arrow.mk f') : kernelSubobjectMap sq ≫ (kernelSubobject f').
arrow = (kernelSubobject f).arrow ≫ …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem kernelSubobjectMap_id : kernelSubobjectMap (𝟙 (Arrow.mk f)) = 𝟙 _ := by cat_disch

set_option backward.defeqAttrib.useBackward true in
@[simp]
/-
**CategoryTheory.Limits.kernelSubobjectMap_comp** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Limits`。
形式化陈述：kernelSubobjectMap_comp {X'' Y'' : C} {f'' : X'' ⟶ Y''} [HasKernel f''] (s
q : Arrow.mk f ⟶ Arrow.mk f') (sq' : Arrow.mk f' ⟶ Arrow.mk f'') : kernelSubobje
ctMap (sq ≫ sq') = kernelSubobjectMap sq ≫ kernelSubobjectMap sq'
参数：sq : Arrow.mk f ⟶ Arrow.mk f'；sq' : Arrow.mk f' ⟶ Arrow.mk f''。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subobject.eq_of_comp_arrow_eq`：eq_of_comp_arrow_eq {X Y :
 C} {P : Subobject Y} {f g : X ⟶ P} (h : f ≫ P.arrow = g ≫ P.arrow) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.kernelSubobjectMap_arrow`：kernelSubobjectMap_arrow
 (sq : Arrow.mk f ⟶ Arrow.mk f') : kernelSubobjectMap sq ≫ (kernelSubobject f').
arrow = (kernelSubobject f).arrow ≫ …
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.kernelSubobjectMap_arrow_assoc`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {X Y : C} [inst_1 : CategoryTheory.Limits
.HasZeroMorphisms C]   {f : X ⟶ Y} [inst_2…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem kernelSubobjectMap_comp {X'' Y'' : C} {f'' : X'' ⟶ Y''} [HasKernel f'']
    (sq : Arrow.mk f ⟶ Arrow.mk f') (sq' : Arrow.mk f' ⟶ Arrow.mk f'') :
    kernelSubobjectMap (sq ≫ sq') = kernelSubobjectMap sq ≫ kernelSubobjectMap sq' := by
  cat_disch

set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/-
**CategoryTheory.Limits.kernel_map_comp_kernelSubobjectIso_inv** 是 Mathlib 中的一个定
理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：kernel_map_comp_kernelSubobjectIso_inv (sq : Arrow.mk f ⟶ Arrow.mk f') : k
ernel.map f f' sq.1 sq.2 sq.3.symm ≫ (kernelSubobjectIso _).inv = (kernelSubobje
ctIso _).inv ≫ kernelSubobjectMap sq
参数：sq : Arrow.mk f ⟶ Arrow.mk f'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subobject.eq_of_comp_arrow_eq`：eq_of_comp_arrow_eq {X Y :
 C} {P : Subobject Y} {f g : X ⟶ P} (h : f ≫ P.arrow = g ≫ P.arrow) : f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.CommaMorphism.w`：∀ {A : Type u₁} [inst : CategoryTheory.C
ategory.{v₁, u₁} A] {B : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} B] 
  {T : Type u₃} [ins…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.kernelSubobject_arrow'`：kernelSubobject_arrow' : (
kernelSubobjectIso f).inv ≫ (kernelSubobject f).arrow = kernel.ι f
· 使用定理 `CategoryTheory.Limits.kernel.lift_ι`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X Y :
 C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `CategoryTheory.Limits.kernelSubobjectMap_arrow`：kernelSubobjectMap_arrow
 (sq : Arrow.mk f ⟶ Arrow.mk f') : kernelSubobjectMap sq ≫ (kernelSubobject f').
arrow = (kernelSubobject f).arrow ≫ …
· 使用定理 `CategoryTheory.Limits.kernelSubobject_arrow'_assoc`：∀ {C : Type u} [inst
 : CategoryTheory.Category.{v, u} C] {X Y : C} [inst_1 : CategoryTheory.Limits.H
asZeroMorphisms C]   (f : X ⟶ Y) [inst_2…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem kernel_map_comp_kernelSubobjectIso_inv (sq : Arrow.mk f ⟶ Arrow.mk f') :
    kernel.map f f' sq.1 sq.2 sq.3.symm ≫ (kernelSubobjectIso _).inv =
      (kernelSubobjectIso _).inv ≫ kernelSubobjectMap sq := by cat_disch

@[reassoc]
/-
**CategoryTheory.Limits.kernelSubobjectIso_comp_kernel_map** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.Limits`。
形式化陈述：kernelSubobjectIso_comp_kernel_map (sq : Arrow.mk f ⟶ Arrow.mk f') : (kern
elSubobjectIso _).hom ≫ kernel.map f f' sq.1 sq.2 sq.3.symm = kernelSubobjectMap
 sq ≫ (kernelSubobjectIso _).hom
参数：sq : Arrow.mk f ⟶ Arrow.mk f'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.CommaMorphism.w`：∀ {A : Type u₁} [inst : CategoryTheory.C
ategory.{v₁, u₁} A] {B : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} B] 
  {T : Type u₃} [ins…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.kernel_map_comp_kernelSubobjectIso_inv`：kernel_map
_comp_kernelSubobjectIso_inv (sq : Arrow.mk f ⟶ Arrow.mk f') : kernel.map f f' s
q.1 sq.2 sq.3.symm ≫ (kernelSubobjectIso _).inv = …
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem kernelSubobjectIso_comp_kernel_map (sq : Arrow.mk f ⟶ Arrow.mk f') :
    (kernelSubobjectIso _).hom ≫ kernel.map f f' sq.1 sq.2 sq.3.symm =
      kernelSubobjectMap sq ≫ (kernelSubobjectIso _).hom := by
  simp [← Iso.comp_inv_eq, kernel_map_comp_kernelSubobjectIso_inv]

end

/-
**CategoryTheory.Limits.kernelSubobject_zero** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Limits`。
形式化陈述：kernelSubobject_zero {A B : C} : kernelSubobject (0 : A ⟶ B) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.equalizerSubobject_of_self`：equalizerSubobject_of_
self : equalizerSubobject f f = ⊤
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem kernelSubobject_zero {A B : C} : kernelSubobject (0 : A ⟶ B) = ⊤ := by
  simp
/-
**CategoryTheory.Limits.isIso_kernelSubobject_zero_arrow** 是 Mathlib 中的一个实例，位于命名
空间 `CategoryTheory.Limits`。
形式化陈述：isIso_kernelSubobject_zero_arrow : IsIso (kernelSubobject (0 : X ⟶ Y)).arr
ow
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.Subobject.isIso_arrow_iff_eq_top`：isIso_arrow_iff_eq_top 
{Y : C} (P : Subobject Y) : IsIso P.arrow ↔ P = ⊤
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.equalizerSubobject_of_self`：equalizerSubobject_of_
self : equalizerSubobject f f = ⊤
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance isIso_kernelSubobject_zero_arrow : IsIso (kernelSubobject (0 : X ⟶ Y)).arrow :=
  (isIso_arrow_iff_eq_top _).mpr (by simp)
/-
**CategoryTheory.Limits.le_kernelSubobject** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Limits`。
形式化陈述：le_kernelSubobject (A : Subobject X) (h : A.arrow ≫ f = 0) : A <= kernelSu
bobject f
参数：A : Subobject X；h : A.arrow ≫ f = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subobject.le_mk_of_comm`：le_mk_of_comm {B A : C} {X : Sub
object B} {f : A ⟶ B} [Mono f] (g : (X : C) ⟶ A) (w : g ≫ f = X.arrow) : X <= mk
 f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.kernel.lift_ι`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X Y :
 C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem le_kernelSubobject (A : Subobject X) (h : A.arrow ≫ f = 0) : A ≤ kernelSubobject f :=
  Subobject.le_mk_of_comm (kernel.lift f A.arrow h) (by simp)

/-- The isomorphism between the kernel of `f ≫ g` and the kernel of `g`,
when `f` is an isomorphism.
-/
/-
**CategoryTheory.Limits.kernelSubobjectIsoComp** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Limits`。
形式化陈述：kernelSubobjectIsoComp {X' : C} (f : X' ⟶ X) [IsIso f] (g : X ⟶ Y) [HasKer
nel g] : (kernelSubobject (f ≫ g) : C) ≅ (kernelSubobject g : C)
参数：f : X' ⟶ X；g : X ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism between the kernel of `f ≫ g` and the kernel of `g`,
when `f` is an isomorphism.
-/
def kernelSubobjectIsoComp {X' : C} (f : X' ⟶ X) [IsIso f] (g : X ⟶ Y) [HasKernel g] :
    (kernelSubobject (f ≫ g) : C) ≅ (kernelSubobject g : C) :=
  kernelSubobjectIso _ ≪≫ kernelIsIsoComp f g ≪≫ (kernelSubobjectIso _).symm

@[simp]
/-
**CategoryTheory.Limits.kernelSubobjectIsoComp_hom_arrow** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.Limits`。
形式化陈述：kernelSubobjectIsoComp_hom_arrow {X' : C} (f : X' ⟶ X) [IsIso f] (g : X ⟶ 
Y) [HasKernel g] : (kernelSubobjectIsoComp f g).hom ≫ (kernelSubobject g).arrow 
= (kernelSubobject (f ≫ g)).arrow ≫ f
参数：f : X' ⟶ X；g : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.kernelIsIsoComp_hom`：∀ {C : Type u} [inst : Catego
ryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
{X Y Z : C}   (f : X ⟶ Y) (g : …
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.kernelSubobject_arrow'`：kernelSubobject_arrow' : (
kernelSubobjectIso f).inv ≫ (kernelSubobject f).arrow = kernel.ι f
· 使用定理 `CategoryTheory.Limits.kernel.lift_ι`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X Y :
 C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `CategoryTheory.Limits.kernelSubobject_arrow_assoc`：∀ {C : Type u} [inst 
: CategoryTheory.Category.{v, u} C] {X Y : C} [inst_1 : CategoryTheory.Limits.Ha
sZeroMorphisms C]   (f : X ⟶ Y) [inst_2…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem kernelSubobjectIsoComp_hom_arrow {X' : C} (f : X' ⟶ X) [IsIso f] (g : X ⟶ Y) [HasKernel g] :
    (kernelSubobjectIsoComp f g).hom ≫ (kernelSubobject g).arrow =
      (kernelSubobject (f ≫ g)).arrow ≫ f := by
  simp [kernelSubobjectIsoComp]

@[simp]
/-
**CategoryTheory.Limits.kernelSubobjectIsoComp_inv_arrow** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.Limits`。
形式化陈述：kernelSubobjectIsoComp_inv_arrow {X' : C} (f : X' ⟶ X) [IsIso f] (g : X ⟶ 
Y) [HasKernel g] : (kernelSubobjectIsoComp f g).inv ≫ (kernelSubobject (f ≫ g)).
arrow = (kernelSubobject g).arrow ≫ inv f
参数：f : X' ⟶ X；g : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.kernelIsIsoComp_inv`：∀ {C : Type u} [inst : Catego
ryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
{X Y Z : C}   (f : X ⟶ Y) (g : …
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.kernelSubobject_arrow'`：kernelSubobject_arrow' : (
kernelSubobjectIso f).inv ≫ (kernelSubobject f).arrow = kernel.ι f
· 使用定理 `CategoryTheory.Limits.kernel.lift_ι`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X Y :
 C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `CategoryTheory.Limits.kernelSubobject_arrow_assoc`：∀ {C : Type u} [inst 
: CategoryTheory.Category.{v, u} C] {X Y : C} [inst_1 : CategoryTheory.Limits.Ha
sZeroMorphisms C]   (f : X ⟶ Y) [inst_2…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem kernelSubobjectIsoComp_inv_arrow {X' : C} (f : X' ⟶ X) [IsIso f] (g : X ⟶ Y) [HasKernel g] :
    (kernelSubobjectIsoComp f g).inv ≫ (kernelSubobject (f ≫ g)).arrow =
      (kernelSubobject g).arrow ≫ inv f := by
  simp [kernelSubobjectIsoComp]

/-- The kernel of `f` is always a smaller subobject than the kernel of `f ≫ h`. -/
/-
**CategoryTheory.Limits.kernelSubobject_comp_le** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Limits`。
形式化陈述：kernelSubobject_comp_le (f : X ⟶ Y) [HasKernel f] {Z : C} (h : Y ⟶ Z) [Has
Kernel (f ≫ h)] : kernelSubobject f <= kernelSubobject (f ≫ h)
参数：f : X ⟶ Y；h : Y ⟶ Z；f ≫ h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.le_kernelSubobject`：le_kernelSubobject (A : Subobj
ect X) (h : A.arrow ≫ f = 0) : A <= kernelSubobject f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.kernelSubobject_arrow_comp_assoc`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {X Y : C} [inst_1 : CategoryTheory.Limi
ts.HasZeroMorphisms C]   (f : X ⟶ Y) [inst_2…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The kernel of `f` is always a smaller subobject than the kernel of `f ≫ h`.
-/
theorem kernelSubobject_comp_le (f : X ⟶ Y) [HasKernel f] {Z : C} (h : Y ⟶ Z) [HasKernel (f ≫ h)] :
    kernelSubobject f ≤ kernelSubobject (f ≫ h) :=
  le_kernelSubobject _ _ (by simp)

/-- Postcomposing by a monomorphism does not change the kernel subobject. -/
@[simp]
/-
**CategoryTheory.Limits.kernelSubobject_comp_mono** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Limits`。
形式化陈述：kernelSubobject_comp_mono (f : X ⟶ Y) [HasKernel f] {Z : C} (h : Y ⟶ Z) [M
ono h] : kernelSubobject (f ≫ h) = kernelSubobject f
参数：f : X ⟶ Y；h : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `CategoryTheory.Limits.le_kernelSubobject`：le_kernelSubobject (A : Subobj
ect X) (h : A.arrow ≫ f = 0) : A <= kernelSubobject f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.kernelSubobject_arrow_comp`：kernelSubobject_arrow_
comp : (kernelSubobject f).arrow ≫ f = 0
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.kernelSubobject_comp_le`：kernelSubobject_comp_le (
f : X ⟶ Y) [HasKernel f] {Z : C} (h : Y ⟶ Z) [HasKernel (f ≫ h)] : kernelSubobje
ct f <= kernelSubobject (f ≫ h)

--- 原说明 ---
Postcomposing by a monomorphism does not change the kernel subobject.
-/
theorem kernelSubobject_comp_mono (f : X ⟶ Y) [HasKernel f] {Z : C} (h : Y ⟶ Z) [Mono h] :
    kernelSubobject (f ≫ h) = kernelSubobject f :=
  le_antisymm (le_kernelSubobject _ _ ((cancel_mono h).mp (by simp))) (kernelSubobject_comp_le f h)
/-
**CategoryTheory.Limits.kernelSubobject_comp_mono_isIso** 是 Mathlib 中的一个实例，位于命名空
间 `CategoryTheory.Limits`。
形式化陈述：kernelSubobject_comp_mono_isIso (f : X ⟶ Y) [HasKernel f] {Z : C} (h : Y ⟶
 Z) [Mono h] : IsIso (Subobject.ofLE _ _ (kernelSubobject_comp_le f h))
参数：f : X ⟶ Y；h : Y ⟶ Z。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.kernelSubobject_comp_le`：kernelSubobject_comp_le (
f : X ⟶ Y) [HasKernel f] {Z : C} (h : Y ⟶ Z) [HasKernel (f ≫ h)] : kernelSubobje
ct f <= kernelSubobject (f ≫ h)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Subobject.mk_le_mk_of_comm`：mk_le_mk_of_comm {B A₁ A₂ : C
} {f₁ : A₁ ⟶ B} {f₂ : A₂ ⟶ B} [Mono f₁] [Mono f₂] (g : A₁ ⟶ A₂) (w : g ≫ f₂ = f₁
) : mk f₁ <= mk f₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.kernelCompMono_inv`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {
X Y Z : C}   (f : X ⟶ Y) (g : …
· 使用定理 `CategoryTheory.Limits.kernel.lift_ι`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X Y :
 C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Subobject.ofLE_mk_le_mk_of_comm`：ofLE_mk_le_mk_of_comm {B
 A₁ A₂ : C} {f₁ : A₁ ⟶ B} {f₂ : A₂ ⟶ B} [Mono f₁] [Mono f₂] (g : A₁ ⟶ A₂) (w : g
 ≫ f₂ = f₁) : ofLE _ _ (mk_le_mk_of_…
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
-/
instance kernelSubobject_comp_mono_isIso (f : X ⟶ Y) [HasKernel f] {Z : C} (h : Y ⟶ Z) [Mono h] :
    IsIso (Subobject.ofLE _ _ (kernelSubobject_comp_le f h)) := by
  rw [ofLE_mk_le_mk_of_comm (kernelCompMono f h).inv]
  · infer_instance
  · simp

set_option backward.isDefEq.respectTransparency false in
/-- Taking cokernels is an order-reversing map from the subobjects of `X` to the quotient objects
of `X`. -/
@[simps]
/-
**CategoryTheory.Limits.cokernelOrderHom** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Limits`。
形式化陈述：cokernelOrderHom [HasCokernels C] (X : C) : Subobject X ->o (Subobject (op
 X))ᵒᵈ where toFun
参数：X : C。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasCokernels.has_colimit`：∀ {C : Type u} {inst : C
ategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C}   [self : CategoryTheory.Limits…

--- 原说明 ---
Taking cokernels is an order-reversing map from the subobjects of `X` to the quo
tient objects
of `X`.
-/
def cokernelOrderHom [HasCokernels C] (X : C) : Subobject X →o (Subobject (op X))ᵒᵈ where
  toFun :=
    Subobject.lift (fun _ f _ => Subobject.mk (cokernel.π f).op)
      (by
        rintro A B f g hf hg i rfl
        refine Subobject.mk_eq_mk_of_comm _ _ (Iso.op ?_) (Quiver.Hom.unop_inj ?_)
        · exact (IsColimit.coconePointUniqueUpToIso (colimit.isColimit _)
            (isCokernelEpiComp (colimit.isColimit _) i.hom rfl)).symm
        · simp only [Iso.comp_inv_eq, Iso.op_hom, Iso.symm_hom, unop_comp, Quiver.Hom.unop_op,
            colimit.comp_coconePointUniqueUpToIso_hom, Cofork.ofπ_ι_app,
            coequalizer.cofork_π])
  monotone' :=
    Subobject.ind₂ _ <| by
      intro A B f g hf hg h
      dsimp only [Subobject.lift_mk]
      refine Subobject.mk_le_mk_of_comm (cokernel.desc f (cokernel.π g) ?_).op ?_
      · rw [← Subobject.ofMkLEMk_comp h, Category.assoc, cokernel.condition, comp_zero]
      · exact Quiver.Hom.unop_inj (cokernel.π_desc _ _ _)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Taking kernels is an order-reversing map from the quotient objects of `X` to the subobjects of
`X`. -/
@[simps]
/-
**CategoryTheory.Limits.kernelOrderHom** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Limits`。
形式化陈述：kernelOrderHom [HasKernels C] (X : C) : (Subobject (op X))ᵒᵈ ->o Subobject
 X where toFun
参数：X : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Taking kernels is an order-reversing map from the quotient objects of `X` to the
 subobjects of
`X`.
-/
def kernelOrderHom [HasKernels C] (X : C) : (Subobject (op X))ᵒᵈ →o Subobject X where
  toFun :=
    Subobject.lift (fun _ f _ => Subobject.mk (kernel.ι f.unop))
      (by
        rintro A B f g hf hg i rfl
        refine Subobject.mk_eq_mk_of_comm _ _ ?_ ?_
        · exact
            IsLimit.conePointUniqueUpToIso (limit.isLimit _)
              (isKernelCompMono (limit.isLimit (parallelPair g.unop 0)) i.unop.hom rfl)
        · dsimp
          simp only [← Iso.eq_inv_comp, limit.conePointUniqueUpToIso_inv_comp,
            Fork.ofι_π_app])
  monotone' :=
    Subobject.ind₂ _ <| by
      intro A B f g hf hg h
      dsimp only [Subobject.lift_mk]
      refine Subobject.mk_le_mk_of_comm (kernel.lift g.unop (kernel.ι f.unop) ?_) ?_
      · rw [← Subobject.ofMkLEMk_comp h, unop_comp, kernel.condition_assoc, zero_comp]
      · exact Quiver.Hom.op_inj (by simp)

end Kernel

section Image

variable (f : X ⟶ Y) [HasImage f]

/-- The image of a morphism `f g : X ⟶ Y` as a `Subobject Y`. -/
/-
**CategoryTheory.Limits.imageSubobject** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheo
ry.Limits`。
形式化陈述：imageSubobject : Subobject Y
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instMonoι`：∀ {C : Type u} [inst : CategoryTheory.C
ategory.{v, u} C] {X Y : C} (f : X ⟶ Y)   [inst_1 : CategoryTheory.Limits.HasIma
ge f], CategoryTheory…

--- 原说明 ---
The image of a morphism `f g : X ⟶ Y` as a `Subobject Y`.
-/
abbrev imageSubobject : Subobject Y :=
  Subobject.mk (image.ι f)

/-- The underlying object of `imageSubobject f` is (up to isomorphism!)
the same as the chosen object `image f`. -/
/-
**CategoryTheory.Limits.imageSubobjectIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Limits`。
形式化陈述：imageSubobjectIso : (imageSubobject f : C) ≅ image f
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instMonoι`：∀ {C : Type u} [inst : CategoryTheory.C
ategory.{v, u} C] {X Y : C} (f : X ⟶ Y)   [inst_1 : CategoryTheory.Limits.HasIma
ge f], CategoryTheory…

--- 原说明 ---
The underlying object of `imageSubobject f` is (up to isomorphism!)
the same as the chosen object `image f`.
-/
def imageSubobjectIso : (imageSubobject f : C) ≅ image f :=
  Subobject.underlyingIso (image.ι f)

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.imageSubobject_arrow** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Limits`。
形式化陈述：imageSubobject_arrow : (imageSubobjectIso f).hom ≫ image.ι f = (imageSubob
ject f).arrow
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.instMonoι`：∀ {C : Type u} [inst : CategoryTheory.C
ategory.{v, u} C] {X Y : C} (f : X ⟶ Y)   [inst_1 : CategoryTheory.Limits.HasIma
ge f], CategoryTheory…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Subobject.underlyingIso_hom_comp_eq_mk`：underlyingIso_hom
_comp_eq_mk {X Y : C} (f : X ⟶ Y) [Mono f] : (underlyingIso f).hom ≫ f = (mk f).
arrow
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem imageSubobject_arrow :
    (imageSubobjectIso f).hom ≫ image.ι f = (imageSubobject f).arrow := by simp [imageSubobjectIso]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.imageSubobject_arrow'** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Limits`。
形式化陈述：imageSubobject_arrow' : (imageSubobjectIso f).inv ≫ (imageSubobject f).arr
ow = image.ι f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Subobject.underlyingIso_arrow`：underlyingIso_arrow {X Y :
 C} (f : X ⟶ Y) [Mono f] : (underlyingIso f).inv ≫ (Subobject.mk f).arrow = f
· 使用定理 `CategoryTheory.Limits.instMonoι`：∀ {C : Type u} [inst : CategoryTheory.C
ategory.{v, u} C] {X Y : C} (f : X ⟶ Y)   [inst_1 : CategoryTheory.Limits.HasIma
ge f], CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem imageSubobject_arrow' :
    (imageSubobjectIso f).inv ≫ (imageSubobject f).arrow = image.ι f := by simp [imageSubobjectIso]

/-- A factorisation of `f : X ⟶ Y` through `imageSubobject f`. -/
/-
**CategoryTheory.Limits.factorThruImageSubobject** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Limits`。
形式化陈述：factorThruImageSubobject : X ⟶ imageSubobject f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A factorisation of `f : X ⟶ Y` through `imageSubobject f`.
-/
def factorThruImageSubobject : X ⟶ imageSubobject f :=
  factorThruImage f ≫ (imageSubobjectIso f).inv
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasEqualizers C] : Epi (factorThruImageSubobject f) := by
  dsimp [factorThruImageSubobject]
  apply epi_comp

@[reassoc (attr := simp), elementwise (attr := simp)]
/-
**CategoryTheory.Limits.imageSubobject_arrow_comp** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Limits`。
形式化陈述：imageSubobject_arrow_comp : factorThruImageSubobject f ≫ (imageSubobject f
).arrow = f
该定理/引理给出了一组等式。
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
· 使用定理 `CategoryTheory.Limits.imageSubobject_arrow'`：imageSubobject_arrow' : (im
ageSubobjectIso f).inv ≫ (imageSubobject f).arrow = image.ι f
· 使用定理 `CategoryTheory.Limits.image.fac`：∀ {C : Type u} [inst : CategoryTheory.C
ategory.{v, u} C] {X Y : C} (f : X ⟶ Y)   [inst_1 : CategoryTheory.Limits.HasIma
ge f],   CategoryTheo…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem imageSubobject_arrow_comp : factorThruImageSubobject f ≫ (imageSubobject f).arrow = f := by
  simp [factorThruImageSubobject]
/-
**CategoryTheory.Limits.imageSubobject_arrow_comp_eq_zero** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.Limits`。
形式化陈述：imageSubobject_arrow_comp_eq_zero [HasZeroMorphisms C] {X Y Z : C} {f : X 
⟶ Y} {g : Y ⟶ Z} [HasImage f] [Epi (factorThruImageSubobject f)] (h : f ≫ g = 0)
 : (imageSubobject f).arrow ≫ g = 0
参数：factorThruImageSubobject f；h : f ≫ g = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.zero_of_epi_comp`：zero_of_epi_comp {X Y Z : C} (f 
: X ⟶ Y) {g : Y ⟶ Z} [Epi f] (h : f ≫ g = 0) : g = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.imageSubobject_arrow_comp_assoc`：∀ {C : Type u} [i
nst : CategoryTheory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y)   [inst_1 : Catego
ryTheory.Limits.HasImage f] {Z : C} (h : Y …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem imageSubobject_arrow_comp_eq_zero [HasZeroMorphisms C] {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z}
    [HasImage f] [Epi (factorThruImageSubobject f)] (h : f ≫ g = 0) :
    (imageSubobject f).arrow ≫ g = 0 :=
  zero_of_epi_comp (factorThruImageSubobject f) <| by simp [h]
/-
**CategoryTheory.Limits.imageSubobject_factors_comp_self** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.Limits`。
形式化陈述：imageSubobject_factors_comp_self {W : C} (k : W ⟶ X) : (imageSubobject f).
Factors (k ≫ f)
参数：k : W ⟶ X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instMonoι`：∀ {C : Type u} [inst : CategoryTheory.C
ategory.{v, u} C] {X Y : C} (f : X ⟶ Y)   [inst_1 : CategoryTheory.Limits.HasIma
ge f], CategoryTheory…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.image.fac`：∀ {C : Type u} [inst : CategoryTheory.C
ategory.{v, u} C] {X Y : C} (f : X ⟶ Y)   [inst_1 : CategoryTheory.Limits.HasIma
ge f],   CategoryTheo…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem imageSubobject_factors_comp_self {W : C} (k : W ⟶ X) : (imageSubobject f).Factors (k ≫ f) :=
  ⟨k ≫ factorThruImage f, by simp⟩

@[simp]
/-
**CategoryTheory.Limits.factorThruImageSubobject_comp_self** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.Limits`。
形式化陈述：factorThruImageSubobject_comp_self {W : C} (k : W ⟶ X) (h) : (imageSubobje
ct f).factorThru (k ≫ f) h = k ≫ factorThruImageSubobject f
参数：k : W ⟶ X；h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subobject.eq_of_comp_arrow_eq`：eq_of_comp_arrow_eq {X Y :
 C} {P : Subobject Y} {f g : X ⟶ P} (h : f ≫ P.arrow = g ≫ P.arrow) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Subobject.factorThru_arrow`：factorThru_arrow {X Y : C} (P
 : Subobject Y) (f : X ⟶ Y) (h : Factors P f) : P.factorThru f h ≫ P.arrow = f
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.imageSubobject_arrow_comp`：imageSubobject_arrow_co
mp : factorThruImageSubobject f ≫ (imageSubobject f).arrow = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem factorThruImageSubobject_comp_self {W : C} (k : W ⟶ X) (h) :
    (imageSubobject f).factorThru (k ≫ f) h = k ≫ factorThruImageSubobject f := by
  ext
  simp

@[simp]
/-
**CategoryTheory.Limits.factorThruImageSubobject_comp_self_assoc** 是 Mathlib 中的一
个定理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：factorThruImageSubobject_comp_self_assoc {W W' : C} (k : W ⟶ W') (k' : W' 
⟶ X) (h) : (imageSubobject f).factorThru (k ≫ k' ≫ f) h = k ≫ k' ≫ factorThruIma
geSubobject f
参数：k : W ⟶ W'；k' : W' ⟶ X；h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subobject.eq_of_comp_arrow_eq`：eq_of_comp_arrow_eq {X Y :
 C} {P : Subobject Y} {f g : X ⟶ P} (h : f ≫ P.arrow = g ≫ P.arrow) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Subobject.factorThru_arrow`：factorThru_arrow {X Y : C} (P
 : Subobject Y) (f : X ⟶ Y) (h : Factors P f) : P.factorThru f h ≫ P.arrow = f
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.imageSubobject_arrow_comp`：imageSubobject_arrow_co
mp : factorThruImageSubobject f ≫ (imageSubobject f).arrow = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem factorThruImageSubobject_comp_self_assoc {W W' : C} (k : W ⟶ W') (k' : W' ⟶ X) (h) :
    (imageSubobject f).factorThru (k ≫ k' ≫ f) h = k ≫ k' ≫ factorThruImageSubobject f := by
  ext
  simp

/-- The image of `h ≫ f` is always a smaller subobject than the image of `f`. -/
/-
**CategoryTheory.Limits.imageSubobject_comp_le** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Limits`。
形式化陈述：imageSubobject_comp_le {X' : C} (h : X' ⟶ X) (f : X ⟶ Y) [HasImage f] [Has
Image (h ≫ f)] : imageSubobject (h ≫ f) <= imageSubobject f
参数：h : X' ⟶ X；f : X ⟶ Y；h ≫ f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subobject.mk_le_mk_of_comm`：mk_le_mk_of_comm {B A₁ A₂ : C
} {f₁ : A₁ ⟶ B} {f₂ : A₂ ⟶ B} [Mono f₁] [Mono f₂] (g : A₁ ⟶ A₂) (w : g ≫ f₂ = f₁
) : mk f₁ <= mk f₂
· 使用定理 `CategoryTheory.Limits.instMonoι`：∀ {C : Type u} [inst : CategoryTheory.C
ategory.{v, u} C] {X Y : C} (f : X ⟶ Y)   [inst_1 : CategoryTheory.Limits.HasIma
ge f], CategoryTheory…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.image.preComp_ι`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y) {Z : C} (g : Y ⟶ Z)   [inst_1 : Ca
tegoryTheory.Limits.HasImag…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The image of `h ≫ f` is always a smaller subobject than the image of `f`.
-/
theorem imageSubobject_comp_le {X' : C} (h : X' ⟶ X) (f : X ⟶ Y) [HasImage f] [HasImage (h ≫ f)] :
    imageSubobject (h ≫ f) ≤ imageSubobject f :=
  Subobject.mk_le_mk_of_comm (image.preComp h f) (by simp)

section

open ZeroObject

variable [HasZeroMorphisms C] [HasZeroObject C]

@[simp]
/-
**CategoryTheory.Limits.imageSubobject_zero_arrow** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Limits`。
形式化陈述：imageSubobject_zero_arrow : (imageSubobject (0 : X ⟶ Y)).arrow = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.imageSubobject_arrow`：imageSubobject_arrow : (imag
eSubobjectIso f).hom ≫ image.ι f = (imageSubobject f).arrow
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.image.ι_zero`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]   [Cate
goryTheory.Limits.HasZer…
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem imageSubobject_zero_arrow : (imageSubobject (0 : X ⟶ Y)).arrow = 0 := by
  rw [← imageSubobject_arrow]
  simp

@[simp]
/-
**CategoryTheory.Limits.imageSubobject_zero** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Limits`。
形式化陈述：imageSubobject_zero {A B : C} : imageSubobject (0 : A ⟶ B) = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subobject.eq_of_comm`：eq_of_comm {B : C} {X Y : Subobject
 B} (f : (X : C) ≅ (Y : C)) (w : f.hom ≫ Y.arrow = X.arrow) : X = Y
· 使用定理 `CategoryTheory.Limits.HasZeroObject.hasInitial`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasZeroObject C],   Cate
goryTheory.Limits.HasInitial C
· 使用定理 `CategoryTheory.Limits.HasZeroObject.initialMonoClass`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasZeroObject C], 
  CategoryTheory.Limits.InitialMonoClass C
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Subobject.bot_arrow`：bot_arrow {B : C} : (⊥ : Subobject B
).arrow = 0
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.Limits.imageSubobject_zero_arrow`：imageSubobject_zero_arr
ow : (imageSubobject (0 : X ⟶ Y)).arrow = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem imageSubobject_zero {A B : C} : imageSubobject (0 : A ⟶ B) = ⊥ :=
  Subobject.eq_of_comm (imageSubobjectIso _ ≪≫ imageZero ≪≫ Subobject.botCoeIsoZero.symm) (by simp)

end

section

variable [HasEqualizers C]

/-- The morphism `imageSubobject (h ≫ f) ⟶ imageSubobject f`
is an epimorphism when `h` is an epimorphism.
In general this does not imply that `imageSubobject (h ≫ f) = imageSubobject f`,
although it will when the ambient category is abelian.
-/
/-
**CategoryTheory.Limits.imageSubobject_comp_le_epi_of_epi** 是 Mathlib 中的一个实例，位于命
名空间 `CategoryTheory.Limits`。
形式化陈述：imageSubobject_comp_le_epi_of_epi {X' : C} (h : X' ⟶ X) [Epi h] (f : X ⟶ Y
) [HasImage f] [HasImage (h ≫ f)] : Epi (Subobject.ofLE _ _ (imageSubobject_comp
_le h f))
参数：h : X' ⟶ X；f : X ⟶ Y；h ≫ f。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.imageSubobject_comp_le`：imageSubobject_comp_le {X'
 : C} (h : X' ⟶ X) (f : X ⟶ Y) [HasImage f] [HasImage (h ≫ f)] : imageSubobject 
(h ≫ f) <= imageSubobject f
· 使用定理 `CategoryTheory.Limits.instMonoι`：∀ {C : Type u} [inst : CategoryTheory.C
ategory.{v, u} C] {X Y : C} (f : X ⟶ Y)   [inst_1 : CategoryTheory.Limits.HasIma
ge f], CategoryTheory…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Subobject.mk_le_mk_of_comm`：mk_le_mk_of_comm {B A₁ A₂ : C
} {f₁ : A₁ ⟶ B} {f₂ : A₂ ⟶ B} [Mono f₁] [Mono f₂] (g : A₁ ⟶ A₂) (w : g ≫ f₂ = f₁
) : mk f₁ <= mk f₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.image.preComp_ι`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y) {Z : C} (g : Y ⟶ Z)   [inst_1 : Ca
tegoryTheory.Limits.HasImag…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Subobject.ofLE_mk_le_mk_of_comm`：ofLE_mk_le_mk_of_comm {B
 A₁ A₂ : C} {f₁ : A₁ ⟶ B} {f₂ : A₂ ⟶ B} [Mono f₁] [Mono f₂] (g : A₁ ⟶ A₂) (w : g
 ≫ f₂ = f₁) : ofLE _ _ (mk_le_mk_of_…
· 使用定理 `CategoryTheory.StrongEpi.epi`：∀ {C : Type u} {inst : CategoryTheory.Cate
gory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongEpi f],   Cate
goryTheory.Epi f
· 使用定理 `CategoryTheory.strongEpi_of_isIso`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] {P Q : C} (f : P ⟶ Q) [CategoryTheory.IsIso f],   CategoryTh
eory.StrongEpi f
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.Limits.image.preComp_epi_of_epi`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y) {Z : C} (g : Y ⟶ Z)   [Ca
tegoryTheory.Limits.HasEqualizers C]…
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv

--- 原说明 ---
The morphism `imageSubobject (h ≫ f) ⟶ imageSubobject f`
is an epimorphism when `h` is an epimorphism.
In general this does not imply that `imageSubobject (h ≫ f) = imageSubobject f`,
although it will when the ambient category is abelian.
-/
instance imageSubobject_comp_le_epi_of_epi {X' : C} (h : X' ⟶ X) [Epi h] (f : X ⟶ Y) [HasImage f]
    [HasImage (h ≫ f)] : Epi (Subobject.ofLE _ _ (imageSubobject_comp_le h f)) := by
  rw [ofLE_mk_le_mk_of_comm (image.preComp h f)]
  · infer_instance
  · simp

end

section

variable [HasEqualizers C]

/-- Postcomposing by an isomorphism gives an isomorphism between image subobjects. -/
/-
**CategoryTheory.Limits.imageSubobjectCompIso** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Limits`。
形式化陈述：imageSubobjectCompIso (f : X ⟶ Y) [HasImage f] {Y' : C} (h : Y ⟶ Y') [IsIs
o h] : (imageSubobject (f ≫ h) : C) ≅ (imageSubobject f : C)
参数：f : X ⟶ Y；h : Y ⟶ Y'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Postcomposing by an isomorphism gives an isomorphism between image subobjects.
-/
def imageSubobjectCompIso (f : X ⟶ Y) [HasImage f] {Y' : C} (h : Y ⟶ Y') [IsIso h] :
    (imageSubobject (f ≫ h) : C) ≅ (imageSubobject f : C) :=
  imageSubobjectIso _ ≪≫ (image.compIso _ _).symm ≪≫ (imageSubobjectIso _).symm

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.imageSubobjectCompIso_hom_arrow** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.Limits`。
形式化陈述：imageSubobjectCompIso_hom_arrow (f : X ⟶ Y) [HasImage f] {Y' : C} (h : Y ⟶
 Y') [IsIso h] : (imageSubobjectCompIso f h).hom ≫ (imageSubobject f).arrow = (i
mageSubobject (f ≫ h)).arrow ≫ inv h
参数：f : X ⟶ Y；h : Y ⟶ Y'。
该定理/引理给出了一组等式。
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
· 使用定理 `CategoryTheory.Limits.imageSubobject_arrow'`：imageSubobject_arrow' : (im
ageSubobjectIso f).inv ≫ (imageSubobject f).arrow = image.ι f
· 使用定理 `CategoryTheory.Limits.image.compIso_inv_comp_image_ι`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y) {Z : C} (g : Y ⟶ Z)
   [inst_1 : CategoryTheory.Limits.HasEqua…
· 使用定理 `CategoryTheory.Limits.imageSubobject_arrow_assoc`：∀ {C : Type u} [inst :
 CategoryTheory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y)   [inst_1 : CategoryThe
ory.Limits.HasImage f] {Z : C} (h : Y …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem imageSubobjectCompIso_hom_arrow (f : X ⟶ Y) [HasImage f] {Y' : C} (h : Y ⟶ Y') [IsIso h] :
    (imageSubobjectCompIso f h).hom ≫ (imageSubobject f).arrow =
      (imageSubobject (f ≫ h)).arrow ≫ inv h := by
  simp [imageSubobjectCompIso]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.imageSubobjectCompIso_inv_arrow** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.Limits`。
形式化陈述：imageSubobjectCompIso_inv_arrow (f : X ⟶ Y) [HasImage f] {Y' : C} (h : Y ⟶
 Y') [IsIso h] : (imageSubobjectCompIso f h).inv ≫ (imageSubobject (f ≫ h)).arro
w = (imageSubobject f).arrow ≫ h
参数：f : X ⟶ Y；h : Y ⟶ Y'。
该定理/引理给出了一组等式。
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
· 使用定理 `CategoryTheory.Limits.imageSubobject_arrow'`：imageSubobject_arrow' : (im
ageSubobjectIso f).inv ≫ (imageSubobject f).arrow = image.ι f
· 使用定理 `CategoryTheory.Limits.image.compIso_hom_comp_image_ι`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y) {Z : C} (g : Y ⟶ Z)
   [inst_1 : CategoryTheory.Limits.HasEqua…
· 使用定理 `CategoryTheory.Limits.imageSubobject_arrow_assoc`：∀ {C : Type u} [inst :
 CategoryTheory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y)   [inst_1 : CategoryThe
ory.Limits.HasImage f] {Z : C} (h : Y …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem imageSubobjectCompIso_inv_arrow (f : X ⟶ Y) [HasImage f] {Y' : C} (h : Y ⟶ Y') [IsIso h] :
    (imageSubobjectCompIso f h).inv ≫ (imageSubobject (f ≫ h)).arrow =
      (imageSubobject f).arrow ≫ h := by
  simp [imageSubobjectCompIso]

end

/-
**CategoryTheory.Limits.imageSubobject_mono** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Limits`。
形式化陈述：imageSubobject_mono (f : X ⟶ Y) [Mono f] : imageSubobject f = Subobject.mk
 f
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subobject.eq_of_comm`：eq_of_comm {B : C} {X Y : Subobject
 B} (f : (X : C) ≅ (Y : C)) (w : f.hom ≫ Y.arrow = X.arrow) : X = Y
· 使用定理 `CategoryTheory.Limits.mono_hasImage`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.Mono f],   CategoryT
heory.Limits.HasImage f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Subobject.underlyingIso_arrow`：underlyingIso_arrow {X Y :
 C} (f : X ⟶ Y) [Mono f] : (underlyingIso f).inv ≫ (Subobject.mk f).arrow = f
· 使用定理 `CategoryTheory.Limits.imageMonoIsoSource_hom_self`：imageMonoIsoSource_ho
m_self [Mono f] : (imageMonoIsoSource f).hom ≫ f = image.ι f
· 使用定理 `CategoryTheory.Limits.imageSubobject_arrow`：imageSubobject_arrow : (imag
eSubobjectIso f).hom ≫ image.ι f = (imageSubobject f).arrow
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem imageSubobject_mono (f : X ⟶ Y) [Mono f] : imageSubobject f = Subobject.mk f :=
  eq_of_comm (imageSubobjectIso f ≪≫ imageMonoIsoSource f ≪≫ (underlyingIso f).symm) (by simp)

/-- Precomposing by an isomorphism does not change the image subobject. -/
/-
**CategoryTheory.Limits.imageSubobject_iso_comp** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Limits`。
形式化陈述：imageSubobject_iso_comp [HasEqualizers C] {X' : C} (h : X' ⟶ X) [IsIso h] 
(f : X ⟶ Y) [HasImage f] : imageSubobject (h ≫ f) = imageSubobject f
参数：h : X' ⟶ X；f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `CategoryTheory.Limits.imageSubobject_comp_le`：imageSubobject_comp_le {X'
 : C} (h : X' ⟶ X) (f : X ⟶ Y) [HasImage f] [HasImage (h ≫ f)] : imageSubobject 
(h ≫ f) <= imageSubobject f
· 使用定理 `CategoryTheory.Subobject.mk_le_mk_of_comm`：mk_le_mk_of_comm {B A₁ A₂ : C
} {f₁ : A₁ ⟶ B} {f₂ : A₂ ⟶ B} [Mono f₁] [Mono f₂] (g : A₁ ⟶ A₂) (w : g ≫ f₂ = f₁
) : mk f₁ <= mk f₂
· 使用定理 `CategoryTheory.Limits.instMonoι`：∀ {C : Type u} [inst : CategoryTheory.C
ategory.{v, u} C] {X Y : C} (f : X ⟶ Y)   [inst_1 : CategoryTheory.Limits.HasIma
ge f], CategoryTheory…
· 使用定理 `CategoryTheory.Limits.image.isIso_precomp_iso`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] {X Y Z : C} (g : Y ⟶ Z) [CategoryTheory.Limits.H
asEqualizers C]   (f : X ⟶ Y) [inst…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.image.preComp_ι`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y) {Z : C} (g : Y ⟶ Z)   [inst_1 : Ca
tegoryTheory.Limits.HasImag…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Precomposing by an isomorphism does not change the image subobject.
-/
theorem imageSubobject_iso_comp [HasEqualizers C] {X' : C} (h : X' ⟶ X) [IsIso h] (f : X ⟶ Y)
    [HasImage f] : imageSubobject (h ≫ f) = imageSubobject f :=
  le_antisymm (imageSubobject_comp_le h f)
    (Subobject.mk_le_mk_of_comm (inv (image.preComp h f)) (by simp))
/-
**CategoryTheory.Limits.imageSubobject_le** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Limits`。
形式化陈述：imageSubobject_le {A B : C} {X : Subobject B} (f : A ⟶ B) [HasImage f] (h 
: A ⟶ X) (w : h ≫ X.arrow = f) : imageSubobject f <= X
参数：f : A ⟶ B；h : A ⟶ X；w : h ≫ X.arrow = f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subobject.le_of_comm`：le_of_comm {B : C} {X Y : Subobject
 B} (f : (X : C) ⟶ (Y : C)) (w : f ≫ Y.arrow = X.arrow) : X <= Y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.image.lift_fac`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {X Y : C} {f : X ⟶ Y}   [inst_1 : CategoryTheory.Limits.H
asImage f] (F' : CategoryT…
· 使用定理 `CategoryTheory.Limits.imageSubobject_arrow`：imageSubobject_arrow : (imag
eSubobjectIso f).hom ≫ image.ι f = (imageSubobject f).arrow
-/
theorem imageSubobject_le {A B : C} {X : Subobject B} (f : A ⟶ B) [HasImage f] (h : A ⟶ X)
    (w : h ≫ X.arrow = f) : imageSubobject f ≤ X :=
  Subobject.le_of_comm
    ((imageSubobjectIso f).hom ≫
      image.lift
        { I := (X : C)
          e := h
          m := X.arrow })
    (by rw [assoc, image.lift_fac, imageSubobject_arrow])
/-
**CategoryTheory.Limits.imageSubobject_le_mk** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Limits`。
形式化陈述：imageSubobject_le_mk {A B : C} {X : C} (g : X ⟶ B) [Mono g] (f : A ⟶ B) [H
asImage f] (h : A ⟶ X) (w : h ≫ g = f) : imageSubobject f <= Subobject.mk g
参数：g : X ⟶ B；f : A ⟶ B；h : A ⟶ X；w : h ≫ g = f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.imageSubobject_le`：imageSubobject_le {A B : C} {X 
: Subobject B} (f : A ⟶ B) [HasImage f] (h : A ⟶ X) (w : h ≫ X.arrow = f) : imag
eSubobject f <= X
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Subobject.underlyingIso_arrow`：underlyingIso_arrow {X Y :
 C} (f : X ⟶ Y) [Mono f] : (underlyingIso f).inv ≫ (Subobject.mk f).arrow = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem imageSubobject_le_mk {A B : C} {X : C} (g : X ⟶ B) [Mono g] (f : A ⟶ B) [HasImage f]
    (h : A ⟶ X) (w : h ≫ g = f) : imageSubobject f ≤ Subobject.mk g :=
  imageSubobject_le f (h ≫ (Subobject.underlyingIso g).inv) (by simp [w])

/-- Given a commutative square between morphisms `f` and `g`,
we have a morphism in the category from `imageSubobject f` to `imageSubobject g`. -/
/-
**CategoryTheory.Limits.imageSubobjectMap** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Limits`。
形式化陈述：imageSubobjectMap {W X Y Z : C} {f : W ⟶ X} [HasImage f] {g : Y ⟶ Z} [HasI
mage g] (sq : Arrow.mk f ⟶ Arrow.mk g) [HasImageMap sq] : (imageSubobject f : C)
 ⟶ (imageSubobject g : C)
参数：sq : Arrow.mk f ⟶ Arrow.mk g。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasImageHomMk`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.Limits.HasImage 
f],   CategoryTheory.Limits.H…

--- 原说明 ---
Given a commutative square between morphisms `f` and `g`,
we have a morphism in the category from `imageSubobject f` to `imageSubobject g`
.
-/
def imageSubobjectMap {W X Y Z : C} {f : W ⟶ X} [HasImage f] {g : Y ⟶ Z} [HasImage g]
    (sq : Arrow.mk f ⟶ Arrow.mk g) [HasImageMap sq] :
    (imageSubobject f : C) ⟶ (imageSubobject g : C) :=
  (imageSubobjectIso f).hom ≫ image.map sq ≫ (imageSubobjectIso g).inv

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.imageSubobjectMap_arrow** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Limits`。
形式化陈述：imageSubobjectMap_arrow {W X Y Z : C} {f : W ⟶ X} [HasImage f] {g : Y ⟶ Z}
 [HasImage g] (sq : Arrow.mk f ⟶ Arrow.mk g) [HasImageMap sq] : imageSubobjectMa
p sq ≫ (imageSubobject g).arrow = (imageSubobject f).arrow ≫ sq.right
参数：sq : Arrow.mk f ⟶ Arrow.mk g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasImageHomMk`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.Limits.HasImage 
f],   CategoryTheory.Limits.H…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.imageSubobject_arrow'`：imageSubobject_arrow' : (im
ageSubobjectIso f).inv ≫ (imageSubobject f).arrow = image.ι f
· 使用定理 `CategoryTheory.Limits.image.map_ι`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] {f g : CategoryTheory.Arrow C}   [inst_1 : CategoryTheory.Li
mits.HasImage f.hom] [i…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Limits.imageSubobject_arrow_assoc`：∀ {C : Type u} [inst :
 CategoryTheory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y)   [inst_1 : CategoryThe
ory.Limits.HasImage f] {Z : C} (h : Y …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
`respectTransparency.types true` changes the auto-generated lemmas' signature
-/
theorem imageSubobjectMap_arrow {W X Y Z : C} {f : W ⟶ X} [HasImage f] {g : Y ⟶ Z} [HasImage g]
    (sq : Arrow.mk f ⟶ Arrow.mk g) [HasImageMap sq] :
    imageSubobjectMap sq ≫ (imageSubobject g).arrow = (imageSubobject f).arrow ≫ sq.right := by
  simp only [imageSubobjectMap, Category.assoc, Arrow.mk_left, Arrow.mk_right,
    Arrow.mk_hom, imageSubobject_arrow']
  rw [dsimp% image.map_ι sq]
  simp

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Limits.image_map_comp_imageSubobjectIso_inv** 是 Mathlib 中的一个定理，
位于命名空间 `CategoryTheory.Limits`。
形式化陈述：image_map_comp_imageSubobjectIso_inv {W X Y Z : C} {f : W ⟶ X} [HasImage f
] {g : Y ⟶ Z} [HasImage g] (sq : Arrow.mk f ⟶ Arrow.mk g) [HasImageMap sq] : ima
ge.map sq ≫ (imageSubobjectIso _).inv = (imageSubobjectIso _).inv ≫ imageSubobje
ctMap sq
参数：sq : Arrow.mk f ⟶ Arrow.mk g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasImageHomMk`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.Limits.HasImage 
f],   CategoryTheory.Limits.H…
· 使用定理 `CategoryTheory.Subobject.eq_of_comp_arrow_eq`：eq_of_comp_arrow_eq {X Y :
 C} {P : Subobject Y} {f g : X ⟶ P} (h : f ≫ P.arrow = g ≫ P.arrow) : f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.imageSubobject_arrow'`：imageSubobject_arrow' : (im
ageSubobjectIso f).inv ≫ (imageSubobject f).arrow = image.ι f
· 使用定理 `CategoryTheory.Limits.imageSubobjectMap_arrow`：imageSubobjectMap_arrow {
W X Y Z : C} {f : W ⟶ X} [HasImage f] {g : Y ⟶ Z} [HasImage g] (sq : Arrow.mk f 
⟶ Arrow.mk g) [HasImageMap sq] : im…
· 使用定理 `CategoryTheory.Limits.imageSubobject_arrow'_assoc`：∀ {C : Type u} [inst 
: CategoryTheory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y)   [inst_1 : CategoryTh
eory.Limits.HasImage f] {Z : C} (h : Y …
· 使用定理 `CategoryTheory.Limits.image.map_ι`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] {f g : CategoryTheory.Arrow C}   [inst_1 : CategoryTheory.Li
mits.HasImage f.hom] [i…
-/
theorem image_map_comp_imageSubobjectIso_inv {W X Y Z : C} {f : W ⟶ X} [HasImage f] {g : Y ⟶ Z}
    [HasImage g] (sq : Arrow.mk f ⟶ Arrow.mk g) [HasImageMap sq] :
    image.map sq ≫ (imageSubobjectIso _).inv =
      (imageSubobjectIso _).inv ≫ imageSubobjectMap sq := by
  ext
  simpa using image.map_ι sq

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Limits.imageSubobjectIso_comp_image_map** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.Limits`。
形式化陈述：imageSubobjectIso_comp_image_map {W X Y Z : C} {f : W ⟶ X} [HasImage f] {g
 : Y ⟶ Z} [HasImage g] (sq : Arrow.mk f ⟶ Arrow.mk g) [HasImageMap sq] : (imageS
ubobjectIso _).hom ≫ image.map sq = imageSubobjectMap sq ≫ (imageSubobjectIso _)
.hom
参数：sq : Arrow.mk f ⟶ Arrow.mk g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasImageHomMk`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.Limits.HasImage 
f],   CategoryTheory.Limits.H…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem imageSubobjectIso_comp_image_map {W X Y Z : C} {f : W ⟶ X} [HasImage f] {g : Y ⟶ Z}
    [HasImage g] (sq : Arrow.mk f ⟶ Arrow.mk g) [HasImageMap sq] :
    (imageSubobjectIso _).hom ≫ image.map sq =
      imageSubobjectMap sq ≫ (imageSubobjectIso _).hom := by
  simp [imageSubobjectMap]

end Image

end Limits

end CategoryTheory

