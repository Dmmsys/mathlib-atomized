/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.ModelCategory.CategoryWithCofibrations
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.MorphismProperty.Factorization

/-!
# A trick by Joyal

In order to construct a model category, we may sometimes have basically
proven all the axioms with the exception of the left lifting property
of cofibrations with respect to trivial fibrations. A trick by Joyal
allows to obtain this lifting property under suitable assumptions,
namely that cofibrations are stable under composition and cobase change.
(The dual result is also formalized.)

## References
* [John F. Jardine, Simplicial presheaves][jardine-1987]

-/

public section

open CategoryTheory Category Limits MorphismProperty

namespace HomotopicalAlgebra

namespace ModelCategory

variable {C : Type*} [Category* C]
  [CategoryWithCofibrations C] [CategoryWithFibrations C] [CategoryWithWeakEquivalences C]
  [(weakEquivalences C).HasTwoOutOfThreeProperty]

set_option backward.isDefEq.respectTransparency false in
/-- Joyal's trick: that cofibrations have the left lifting property
with respect to trivial fibrations follows from the left lifting property
of trivial cofibrations with respect to fibrations and a few other
consequences of the model categories axioms. -/
/-
**HomotopicalAlgebra.ModelCategory.hasLiftingProperty_of_joyalTrick** 是 Mathlib 
中的一个引理，位于命名空间 `HomotopicalAlgebra.ModelCategory`。
形式化陈述：hasLiftingProperty_of_joyalTrick [HasFactorization (cofibrations C) (trivi
alFibrations C)] [HasPushouts C] [(cofibrations C).IsStableUnderComposition] [(c
ofibrations C).IsStableUnderCobaseChange] (h : forall {A B X Y : C} (i : A ⟶ B) 
(p : X ⟶ Y) [Cofibration i] [WeakEquivalence i] [Fibration p], HasLiftingPropert
y i p) {A B X Y : C} (i : A ⟶ B) (p : X ⟶ Y) [Cofibration i] [Fibration p] [Weak
Equivalence p] : HasLiftingProperty i p where sq_hasLift {f g} sq
参数：cofibrations C；trivialFibrations C；cofibrations C；cofibrations C；h : forall {
A B X Y : C} (i : A ⟶ B) (p : X ⟶ Y) [Cofibration i] [WeakEquivalence i] [Fibrat
ion p], HasLiftingProperty i p；i : A ⟶ B；p : X ⟶ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.CommSq.w`：∀ {C : Type u_1} [inst : CategoryTheory.Categor
y.{v_1, u_1} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z}   {i : Y ⟶ Z},
   CategoryTh…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.MorphismProperty.MapFactorizationData.fac`：∀ {C : Type u_
1} [inst : CategoryTheory.Category.{v_1, u_1} C] {W₁ W₂ : CategoryTheory.Morphis
mProperty C} {X Y : C}   {f : X ⟶ Y} (self : W…
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PushoutCocone.mk_ι_app`：∀ {C : Type u} [inst : Cat
egoryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} {W : C} (inl 
: Y ⟶ W)   (inr : Z ⟶ W) (eq : Cat…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `CategoryTheory.MorphismProperty.comp_mem`：comp_mem (W : MorphismProperty
 C) [W.IsStableUnderComposition] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : W f) 
(hg : W g) : W (f ≫ g)
· 使用定理 `CategoryTheory.MorphismProperty.of_isPushout`：∀ {C : Type u} {inst : Cat
egoryTheory.Category.{v, u} C} {P : CategoryTheory.MorphismProperty C}   [self :
 P.IsStableUnderCobaseChange] {A A…
· 使用定理 `CategoryTheory.IsPushout.of_hasPushout`：of_hasPushout (f : Z ⟶ X) (g : Z
 ⟶ Y) [HasPushout f g] : IsPushout f g (pushout.inl f g) (pushout.inr f g)
· 使用引理 `HomotopicalAlgebra.mem_cofibrations`：mem_cofibrations [Cofibration f] : 
cofibrations C f
· 使用定理 `CategoryTheory.MorphismProperty.MapFactorizationData.hi`：∀ {C : Type u_1
} [inst : CategoryTheory.Category.{v_1, u_1} C] {W₁ W₂ : CategoryTheory.Morphism
Property C} {X Y : C}   {f : X ⟶ Y} (self : W…
· 使用定理 `HomotopicalAlgebra.weakEquivalence_iff`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y)   [inst_1 : HomotopicalAlgebra.Ca
tegoryWithWeakEquivalences C…
· 使用引理 `CategoryTheory.MorphismProperty.of_postcomp`：of_postcomp [W.HasOfPostcom
pProperty W'] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hg : W' g) (hfg : W (f ≫ g)) 
: W f
· 使用定理 `CategoryTheory.MorphismProperty.HasTwoOutOfThreeProperty.toHasOfPostcomp
Property`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : Category
Theory.MorphismProperty C}   [self : W.HasTwoOutOfThreeProperty], W.Ha…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `CategoryTheory.MorphismProperty.MapFactorizationData.hp`：∀ {C : Type u_1
} [inst : CategoryTheory.Category.{v_1, u_1} C] {W₁ W₂ : CategoryTheory.Morphism
Property C} {X Y : C}   {f : X ⟶ Y} (self : W…
· 使用定理 `CategoryTheory.sq_hasLift_of_hasLiftingProperty`：∀ {C : Type u_1} [inst 
: CategoryTheory.Category.{v_1, u_1} C] {A B X Y : C} (i : A ⟶ B) (p : X ⟶ Y) {f
 : A ⟶ X}   {g : B ⟶ Y} (sq : Categor…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HomotopicalAlgebra.cofibration_iff`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {X Y : C} (f : X ⟶ Y)   [inst_1 : HomotopicalAlgebra.Catego
ryWithCofibrations C],  …
· 使用定理 `CategoryTheory.Limits.pushout.condition_assoc`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}   [inst_1 : 
CategoryTheory.Limits.HasPushout f …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.whisker_eq`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {X Y Z : C} {f g : Y ⟶ X} (h : Z ⟶ Y),   f = g → CategoryTheory.Cate
goryStruct.comp…
· 使用定理 `CategoryTheory.CommSq.fac_left`：fac_left [hsq : HasLift sq] : i ≫ sq.lif
t = f
（共 32 条，此处仅展示前 30 条）

--- 原说明 ---
Joyal's trick: that cofibrations have the left lifting property
with respect to trivial fibrations follows from the left lifting property
of trivial cofibrations with respect to fibrations and a few other
consequences of the model categories axioms.
-/
lemma hasLiftingProperty_of_joyalTrick
    [HasFactorization (cofibrations C) (trivialFibrations C)] [HasPushouts C]
    [(cofibrations C).IsStableUnderComposition] [(cofibrations C).IsStableUnderCobaseChange]
    (h : ∀ {A B X Y : C} (i : A ⟶ B) (p : X ⟶ Y)
      [Cofibration i] [WeakEquivalence i] [Fibration p], HasLiftingProperty i p)
    {A B X Y : C} (i : A ⟶ B) (p : X ⟶ Y)
    [Cofibration i] [Fibration p] [WeakEquivalence p] :
    HasLiftingProperty i p where
  sq_hasLift {f g} sq := by
    let h := factorizationData (cofibrations C) (trivialFibrations C)
      (pushout.desc p g sq.w)
    have sq' : CommSq (𝟙 X) (pushout.inl _ _ ≫ h.i) p h.p := .mk
    have h₁ : WeakEquivalence ((pushout.inl f i ≫ h.i) ≫ h.p) := by simpa
    have h₂ := comp_mem _ _ _ ((cofibrations C).of_isPushout
      (IsPushout.of_hasPushout f i) (mem_cofibrations i)) h.hi
    rw [← cofibration_iff] at h₂
    have : WeakEquivalence (pushout.inl f i ≫ h.i) := by
      rw [weakEquivalence_iff] at h₁ ⊢
      exact of_postcomp _ _ _ h.hp.2 h₁
    exact ⟨⟨{ l := pushout.inr f i ≫ h.i ≫ sq'.lift
              fac_left := by
                simpa only [assoc, comp_id, pushout.condition_assoc] using
                  f ≫= sq'.fac_left }⟩⟩

set_option backward.isDefEq.respectTransparency false in
/-- Joyal's trick (dual): that trivial cofibrations have the left lifting
property with respect to fibrations follows from the left lifting property
of cofibrations with respect to trivial fibrations and a few other
consequences of the model categories axioms. -/
/-
**HomotopicalAlgebra.ModelCategory.hasLiftingProperty_of_joyalTrickDual** 是 Math
lib 中的一个引理，位于命名空间 `HomotopicalAlgebra.ModelCategory`。
形式化陈述：hasLiftingProperty_of_joyalTrickDual [HasFactorization (trivialCofibration
s C) (fibrations C)] [HasPullbacks C] [(fibrations C).IsStableUnderComposition] 
[(fibrations C).IsStableUnderBaseChange] (h : forall {A B X Y : C} (i : A ⟶ B) (
p : X ⟶ Y) [Cofibration i] [WeakEquivalence p] [Fibration p], HasLiftingProperty
 i p) {A B X Y : C} (i : A ⟶ B) (p : X ⟶ Y) [Cofibration i] [Fibration p] [WeakE
quivalence i] : HasLiftingProperty i p where sq_hasLift {f g} sq
参数：trivialCofibrations C；fibrations C；fibrations C；fibrations C；h : forall {A B 
X Y : C} (i : A ⟶ B) (p : X ⟶ Y) [Cofibration i] [WeakEquivalence p] [Fibration 
p], HasLiftingProperty i p；i : A ⟶ B；p : X ⟶ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.CommSq.w`：∀ {C : Type u_1} [inst : CategoryTheory.Categor
y.{v_1, u_1} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z}   {i : Y ⟶ Z},
   CategoryTh…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MorphismProperty.MapFactorizationData.fac_assoc`：∀ {C : T
ype u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {W₁ W₂ : CategoryTheory.M
orphismProperty C} {X Y : C}   {f : X ⟶ Y} (self : W…
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PullbackCone.mk_π_app`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {W : C} (fst :
 W ⟶ X)   (snd : W ⟶ Y)   (eq :  …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `CategoryTheory.MorphismProperty.comp_mem`：comp_mem (W : MorphismProperty
 C) [W.IsStableUnderComposition] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : W f) 
(hg : W g) : W (f ≫ g)
· 使用定理 `CategoryTheory.MorphismProperty.MapFactorizationData.hp`：∀ {C : Type u_1
} [inst : CategoryTheory.Category.{v_1, u_1} C] {W₁ W₂ : CategoryTheory.Morphism
Property C} {X Y : C}   {f : X ⟶ Y} (self : W…
· 使用定理 `CategoryTheory.MorphismProperty.of_isPullback`：∀ {C : Type u} {inst : Ca
tegoryTheory.Category.{v, u} C} {P : CategoryTheory.MorphismProperty C}   [self 
: P.IsStableUnderBaseChange] {X Y Y…
· 使用定理 `CategoryTheory.IsPullback.of_hasPullback`：of_hasPullback (f : X ⟶ Z) (g 
: Y ⟶ Z) [HasPullback f g] : IsPullback (pullback.fst f g) (pullback.snd f g) f 
g
· 使用引理 `HomotopicalAlgebra.mem_fibrations`：mem_fibrations [Fibration f] : fibrat
ions C f
· 使用定理 `HomotopicalAlgebra.weakEquivalence_iff`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y)   [inst_1 : HomotopicalAlgebra.Ca
tegoryWithWeakEquivalences C…
· 使用引理 `CategoryTheory.MorphismProperty.of_precomp`：of_precomp [W.HasOfPrecompPr
operty W'] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : W' f) (hfg : W (f ≫ g)) : W
 g
· 使用定理 `CategoryTheory.MorphismProperty.HasTwoOutOfThreeProperty.toHasOfPrecompP
roperty`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryT
heory.MorphismProperty C}   [self : W.HasTwoOutOfThreeProperty], W.Ha…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `CategoryTheory.MorphismProperty.MapFactorizationData.hi`：∀ {C : Type u_1
} [inst : CategoryTheory.Category.{v_1, u_1} C] {W₁ W₂ : CategoryTheory.Morphism
Property C} {X Y : C}   {f : X ⟶ Y} (self : W…
· 使用定理 `CategoryTheory.sq_hasLift_of_hasLiftingProperty`：∀ {C : Type u_1} [inst 
: CategoryTheory.Category.{v_1, u_1} C] {A B X Y : C} (i : A ⟶ B) (p : X ⟶ Y) {f
 : A ⟶ X}   {g : B ⟶ Y} (sq : Categor…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HomotopicalAlgebra.fibration_iff`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {X Y : C} (f : X ⟶ Y)   [inst_1 : HomotopicalAlgebra.Category
WithFibrations C],   H…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.CommSq.fac_left_assoc`：∀ {C : Type u_1} [inst : CategoryT
heory.Category.{v_1, u_1} C] {A B X Y : C} {f : A ⟶ X} {i : A ⟶ B} {p : X ⟶ Y}  
 {g : B ⟶ Y} (sq : Categor…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.pullback.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPullback f…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
（共 33 条，此处仅展示前 30 条）

--- 原说明 ---
Joyal's trick (dual): that trivial cofibrations have the left lifting
property with respect to fibrations follows from the left lifting property
of cofibrations with respect to trivial fibrations and a few other
consequences of the model categories axioms.
-/
lemma hasLiftingProperty_of_joyalTrickDual
    [HasFactorization (trivialCofibrations C) (fibrations C)] [HasPullbacks C]
    [(fibrations C).IsStableUnderComposition] [(fibrations C).IsStableUnderBaseChange]
    (h : ∀ {A B X Y : C} (i : A ⟶ B) (p : X ⟶ Y)
      [Cofibration i] [WeakEquivalence p] [Fibration p], HasLiftingProperty i p)
    {A B X Y : C} (i : A ⟶ B) (p : X ⟶ Y)
    [Cofibration i] [Fibration p] [WeakEquivalence i] :
    HasLiftingProperty i p where
  sq_hasLift {f g} sq := by
    let h := factorizationData (trivialCofibrations C) (fibrations C)
      (pullback.lift f i sq.w)
    have sq' : CommSq h.i i (h.p ≫ pullback.snd _ _) (𝟙 B) := .mk
    have h₁ : WeakEquivalence (h.i ≫ h.p ≫ pullback.snd p g) := by simpa
    have h₂ := comp_mem _ _ _ h.hp ((fibrations C).of_isPullback
      (IsPullback.of_hasPullback p g) (mem_fibrations p))
    rw [← fibration_iff] at h₂
    have : WeakEquivalence (h.p ≫ pullback.snd p g) := by
      rw [weakEquivalence_iff] at h₁ ⊢
      exact of_precomp _ _ _ h.hi.2 h₁
    exact ⟨⟨{ l := sq'.lift ≫ h.p ≫ pullback.fst p g
              fac_right := by
                rw [assoc, assoc, pullback.condition, reassoc_of% sq'.fac_right] }⟩⟩

end ModelCategory

end HomotopicalAlgebra

