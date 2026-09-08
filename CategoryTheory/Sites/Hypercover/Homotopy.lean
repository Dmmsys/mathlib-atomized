/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Quotient
public import Mathlib.CategoryTheory.Sites.Hypercover.One
public import Mathlib.CategoryTheory.Filtered.Basic

/-!
# The category of `1`-hypercovers up to homotopy

In this file we define the category of `1`-hypercovers up to homotopy. This is the category of
`1`-hypercovers, but where morphisms are considered up to existence of a homotopy.

## Main definitions

- `CategoryTheory.PreOneHypercover.Homotopy`: A homotopy of refinements `E ⟶ F` is a family of
  morphisms `Xᵢ ⟶ Yₐ` where `Yₐ` is a component of the cover of `X_{f(i)} ×[S] X_{g(i)}`.
- `CategoryTheory.GrothendieckTopology.HOneHypercover`: The category of `1`-hypercovers
  with respect to a Grothendieck topology and morphisms up to homotopy.

## Main results

- `CategoryTheory.GrothendieckTopology.HOneHypercover.isCofiltered_of_hasPullbacks`: The
  category of `1`-hypercovers up to homotopy is cofiltered if `C` has pullbacks.
-/

@[expose] public section

universe w'' w' w v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C]

namespace PreOneHypercover

variable {S : C} {E : PreOneHypercover.{w} S} {F : PreOneHypercover.{w'} S}

/-- A homotopy of refinements `E ⟶ F` is a family of morphisms `Xᵢ ⟶ Yₐ` where
`Yₐ` is a component of the cover of `X_{f(i)} ×[S] X_{g(i)}`. -/
/-
**CategoryTheory.PreOneHypercover.Homotopy** 是 Mathlib 中的一个结构，位于命名空间 `CategoryTh
eory.PreOneHypercover`。
形式化陈述：Homotopy (f g : E.Hom F) where /-- The index map sending `i : E.I₀` to `a`
 above `(f(i), g(i))`. -/ H (i : E.I₀) : F.I₁ (f.s₀ i) (g.s₀ i) /-- The morphism
 `Xᵢ ⟶ Yₐ`. -/ a (i : E.I₀) : E.X i ⟶ F.Y (H i) wl (i : E.I₀) : a i ≫ F.p₁ (H i)
 = f.h₀ i wr (i : E.I₀) : a i ≫ F.p₂ (H i) = g.h₀ i  attribute [reassoc (attr
参数：f g : E.Hom F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A homotopy of refinements `E ⟶ F` is a family of morphisms `Xᵢ ⟶ Yₐ` where
`Yₐ` is a component of the cover of `X_{f(i)} ×[S] X_{g(i)}`.
-/
structure Homotopy (f g : E.Hom F) where
  /-- The index map sending `i : E.I₀` to `a` above `(f(i), g(i))`. -/
  H (i : E.I₀) : F.I₁ (f.s₀ i) (g.s₀ i)
  /-- The morphism `Xᵢ ⟶ Yₐ`. -/
  a (i : E.I₀) : E.X i ⟶ F.Y (H i)
  wl (i : E.I₀) : a i ≫ F.p₁ (H i) = f.h₀ i
  wr (i : E.I₀) : a i ≫ F.p₂ (H i) = g.h₀ i

attribute [reassoc (attr := simp)] Homotopy.wl Homotopy.wr

section

variable {A : Type*} [Category* A]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Homotopic refinements induce the same map on multiequalizers. -/
/-
**CategoryTheory.PreOneHypercover.Homotopy.mapMultiforkOfIsLimit_eq** 是 Mathlib 
中的一个定理，位于命名空间 `CategoryTheory.PreOneHypercover.Homotopy`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {S : C} {A : Type
 u_1}   [inst_1 : CategoryTheory.Category.{v_1, u_1} A] {E F : CategoryTheory.Pr
eOneHypercover S} {f g : E.Hom F}   (H : CategoryTheory.PreOneHypercover.Homotop
y f g) (P : CategoryTheory.Functor Cᵒᵖ A)   {c : CategoryTheory.Limits.Multifork
 (E.multicospanIndex P)} (hc : CategoryTheory.Limits.IsLimit c)   (d : CategoryT
heory.Limits.Multifork (F.multicospanIndex P)),   f.mapMultiforkOfIsLimit P hc d
 = g.mapMultiforkOfIsLimit P hc d
参数：H : CategoryTheory.PreOneHypercover.Homotopy f g；P : CategoryTheory.Functor C
ᵒᵖ A；E.multicospanIndex P；hc : CategoryTheory.Limits.IsLimit c；d : CategoryTheor
y.Limits.Multifork (F.multicospanIndex P)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Multifork.IsLimit.hom_ext`：∀ {C : Type u} [inst : 
CategoryTheory.Category.{v, u} C] {J : CategoryTheory.Limits.MulticospanShape}  
 {I : CategoryTheory.Limits.Multicosp…
· 使用定理 `CategoryTheory.Limits.Multifork.condition`：condition (b) : K.ι (J.fst b)
 ≫ I.fst b = K.ι (J.snd b) ≫ I.snd b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.PreOneHypercover.Hom.mapMultiforkOfIsLimit_ι`：∀ {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C] {A : Type u_1} [inst_1 : CategoryT
heory.Category.{v_1, u_1} A]   {S : C} {E : Categ…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.PreOneHypercover.Homotopy.wl`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {S : C} {E : CategoryTheory.PreOneHypercover S}   
{F : CategoryTheory.PreOneHyperco…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Mathlib.Tactic.Reassoc.eq_whisker'`：eq_whisker' {C : Type*} [Category* C
] {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) : f ≫ h = g ≫ h
· 使用定理 `CategoryTheory.PreOneHypercover.Homotopy.wr`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {S : C} {E : CategoryTheory.PreOneHypercover S}   
{F : CategoryTheory.PreOneHyperco…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Homotopic refinements induce the same map on multiequalizers.
-/
lemma Homotopy.mapMultiforkOfIsLimit_eq
    {E F : PreOneHypercover.{w} S} {f g : E.Hom F} (H : Homotopy f g)
    (P : Cᵒᵖ ⥤ A) {c : Multifork (E.multicospanIndex P)} (hc : IsLimit c)
    (d : Multifork (F.multicospanIndex P)) :
    f.mapMultiforkOfIsLimit P hc d = g.mapMultiforkOfIsLimit P hc d := by
  refine Multifork.IsLimit.hom_ext hc fun a ↦ ?_
  have heq := d.condition ⟨⟨(f.s₀ a), (g.s₀ a)⟩, H.H a⟩
  simp only [multicospanIndex_right, multicospanShape_fst, multicospanIndex_left,
    multicospanIndex_fst, multicospanShape_snd, multicospanIndex_snd] at heq
  simp [-Homotopy.wl, -Homotopy.wr, ← H.wl, ← H.wr, reassoc_of% heq]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- If `f : E ⟶ F` and `g : F ⟶ E` are refinement morphisms of pre-`1`-hypercovers such that
the composition `g ≫ f` is homotopic to the identity, then if the multifork associated
to `E` is exact also the multifork associated to `F` is exact. -/
/-
**CategoryTheory.PreOneHypercover.Homotopy.isLimitMultifork** 是 Mathlib 中的一个定义，位
于命名空间 `CategoryTheory.PreOneHypercover.Homotopy`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {S : C} →
       {E : CategoryTheory.PreOneHypercover S} →         {F : CategoryTheory.Pre
OneHypercover S} →           {A : Type u_1} →             [inst_1 : CategoryTheo
ry.Category.{v_1, u_1} A] →               (f : E.Hom F) →                 (g : F
.Hom E) →                   CategoryTheory.PreOneHypercover.Homotopy (g.comp f) 
(CategoryTheory.PreOneHypercover.Hom.id F) →                     {G : CategoryTh
eory.Functor Cᵒᵖ A} →                       CategoryTheory.Limits.IsLimit (E.mul
tifork G) → CategoryTheory.Limits.IsLimit (F.multifork G)
参数：f : E.Hom F；g : F.Hom E；g.comp f；CategoryTheory.PreOneHypercover.Hom.id F；E.m
ultifork G；F.multifork G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f : E ⟶ F` and `g : F ⟶ E` are refinement morphisms of pre-`1`-hypercovers s
uch that
the composition `g ≫ f` is homotopic to the identity, then if the multifork asso
ciated
to `E` is exact also the multifork associated to `F` is exact.
-/
def Homotopy.isLimitMultifork (f : E.Hom F) (g : F.Hom E) (hgf : Homotopy (g.comp f) (.id F))
    {G : Cᵒᵖ ⥤ A} (hE : IsLimit (E.multifork G)) :
    IsLimit (F.multifork G) := by
  refine Multifork.IsLimit.mk _ ?_ ?_ ?_
  · intro t
    refine Multifork.IsLimit.lift hE (fun a ↦ t.ι (f.s₀ a) ≫ G.map (f.h₀ a).op) ?_
    intro b
    dsimp
    simp only [Category.assoc, ← Functor.map_comp, ← op_comp]
    rw [← f.w₁₁, ← f.w₁₂]
    simp only [op_comp, Functor.map_comp]
    exact t.condition_assoc ⟨(f.s₀ b.1.1, f.s₀ b.1.2), f.s₁ b.2⟩ _
  · intro t i
    simp only [multicospanIndex_left, multicospanShape_L, multifork_ι]
    have h1 := hgf.wl i
    have h2 := t.condition ⟨⟨_, _⟩, hgf.H i⟩
    dsimp at h1 h2
    rw [← g.w₀, op_comp, Functor.map_comp, ← E.multifork_ι, Multifork.IsLimit.fac_assoc,
      Category.assoc, ← Functor.map_comp, ← op_comp, ← h1, op_comp, Functor.map_comp,
      reassoc_of% h2, ← Functor.map_comp, ← op_comp, hgf.wr i]
    simp
  · intro t m hm
    refine Multifork.IsLimit.hom_ext hE fun i ↦ ?_
    rw [Multifork.IsLimit.fac, multifork_ι, ← f.w₀, op_comp, Functor.map_comp, ← F.multifork_ι,
      reassoc_of% hm]

/-- `E` and `F` are homotopy equivalent, then the multifork associated
to `E` is exact if and only if the multifork associated to `F` is exact. -/
/-
**CategoryTheory.PreOneHypercover.Homotopy.isLimitMultiforkEquiv** 是 Mathlib 中的一
个定义，位于命名空间 `CategoryTheory.PreOneHypercover.Homotopy`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {S : C} →
       {E : CategoryTheory.PreOneHypercover S} →         {F : CategoryTheory.Pre
OneHypercover S} →           {A : Type u_1} →             [inst_1 : CategoryTheo
ry.Category.{v_1, u_1} A] →               (f : E.Hom F) →                 (g : F
.Hom E) →                   CategoryTheory.PreOneHypercover.Homotopy (f.comp g) 
(CategoryTheory.PreOneHypercover.Hom.id E) →                     CategoryTheory.
PreOneHypercover.Homotopy (g.comp f) (CategoryTheory.PreOneHypercover.Hom.id F) 
→                       {G : CategoryTheory.Functor Cᵒᵖ A} →                    
     CategoryTheory.Limits.IsLimit (E.multifork G) ≃ CategoryTheory.Limits.IsLim
it (F.multifork G)
参数：f : E.Hom F；g : F.Hom E；f.comp g；CategoryTheory.PreOneHypercover.Hom.id E；g.c
omp f；CategoryTheory.PreOneHypercover.Hom.id F；E.multifork G；F.multifork G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`E` and `F` are homotopy equivalent, then the multifork associated
to `E` is exact if and only if the multifork associated to `F` is exact.
-/
def Homotopy.isLimitMultiforkEquiv (f : E.Hom F) (g : F.Hom E)
    (hfg : Homotopy (f.comp g) (.id E)) (hgf : Homotopy (g.comp f) (.id F)) {G : Cᵒᵖ ⥤ A} :
    IsLimit (E.multifork G) ≃ IsLimit (F.multifork G) where
  toFun h := hgf.isLimitMultifork _ _ h
  invFun h := hfg.isLimitMultifork _ _ h
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

end

variable [Limits.HasPullbacks C] (f g : E.Hom F)

/-- (Implementation): The covering object of `cylinder f g`. -/
noncomputable
/-
**CategoryTheory.PreOneHypercover.cylinderX** 是 Mathlib 中的一个缩写定义，位于命名空间 `Categor
yTheory.PreOneHypercover`。
形式化陈述：cylinderX {i : E.I₀} (k : F.I₁ (f.s₀ i) (g.s₀ i)) : C
参数：k : F.I₁ (f.s₀ i) (g.s₀ i)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
abbrev cylinderX {i : E.I₀} (k : F.I₁ (f.s₀ i) (g.s₀ i)) : C :=
  pullback (pullback.lift (f.h₀ i) (g.h₀ i) (by simp)) (F.toPullback k)

/-- (Implementation): The structure morphisms of the covering objects of `cylinder f g`. -/
noncomputable
/-
**CategoryTheory.PreOneHypercover.cylinderf** 是 Mathlib 中的一个缩写定义，位于命名空间 `Categor
yTheory.PreOneHypercover`。
形式化陈述：cylinderf {i : E.I₀} (k : F.I₁ (f.s₀ i) (g.s₀ i)) : cylinderX f g k ⟶ S
参数：k : F.I₁ (f.s₀ i) (g.s₀ i)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
abbrev cylinderf {i : E.I₀} (k : F.I₁ (f.s₀ i) (g.s₀ i)) : cylinderX f g k ⟶ S :=
  pullback.fst _ _ ≫ E.f _

/-- Given two refinement morphisms `f, g : E ⟶ F`, this is a (pre-)`1`-hypercover `W` that
admits a morphism `h : W ⟶ E` such that `h ≫ f` and `h ≫ g` are homotopic. Hence
they become equal after quotienting out by homotopy.
This is a `1`-hypercover, if `E` and `F` are (see `OneHypercover.cylinder`). -/
@[simps]
/-
**CategoryTheory.PreOneHypercover.cylinder** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.PreOneHypercover`。
形式化陈述：cylinder (f g : E.Hom F) : PreOneHypercover.{max w w'} S where I₀
参数：f g : E.Hom F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given two refinement morphisms `f, g : E ⟶ F`, this is a (pre-)`1`-hypercover `W
` that
admits a morphism `h : W ⟶ E` such that `h ≫ f` and `h ≫ g` are homotopic. Hence
they become equal after quotienting out by homotopy.
This is a `1`-hypercover, if `E` and `F` are (see `OneHypercover.cylinder`).
-/
noncomputable def cylinder (f g : E.Hom F) : PreOneHypercover.{max w w'} S where
  I₀ := Σ (i : E.I₀), F.I₁ (f.s₀ i) (g.s₀ i)
  X p := cylinderX f g p.2
  f p := cylinderf f g p.2
  I₁ p q := ULift.{max w w'} (E.I₁ p.1 q.1)
  Y {p q} k :=
    pullback
      (pullback.map (cylinderf f g p.2)
        (cylinderf f g q.2) _ _ (pullback.fst _ _) (pullback.fst _ _) (𝟙 S) (by simp)
        (by simp))
      (pullback.lift _ _ (E.w k.down))
  p₁ {p q} k := pullback.fst _ _ ≫ pullback.fst _ _
  p₂ {p q} k := pullback.fst _ _ ≫ pullback.snd _ _
  w {_ _} k := by simp [pullback.condition]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.PreOneHypercover.toPullback_cylinder** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.PreOneHypercover`。
形式化陈述：toPullback_cylinder {i j : (cylinder f g).I₀} (k : (cylinder f g).I₁ i j) 
: (cylinder f g).toPullback k = pullback.fst _ _
参数：cylinder f g；k : (cylinder f g).I₁ i j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.pullback.hom_ext`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categor
yTheory.Limits.HasPullback f…
· 使用定理 `CategoryTheory.Precoverage.ZeroHypercover.instHasPullbackFOfHasPullbacks
Presieve₀`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} (E
 : CategoryTheory.PreZeroHypercover X) (f : Y ⟶ X)   [E.presieve₀.HasPu…
· 使用定理 `CategoryTheory.Presieve.instHasPullbacksOfArrowsOfHasPullback`：∀ {C : Ty
pe u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : Y ⟶ X) {ι : Ty
pe u_1} (Z : ι → C)   (g : (i : ι) → Z i ⟶ X) [∀ (i…
· 使用定理 `CategoryTheory.Precoverage.ZeroHypercover.instHasPullbackFOfHasPullbacks
Presieve₀_1`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} 
(E : CategoryTheory.PreZeroHypercover X) (f : Y ⟶ X)   [E.presieve₀.HasPu…
· 使用定理 `CategoryTheory.Presieve.instHasPullbackOfHasPairwisePullbacksOfArrows`：∀
 {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {α : Type v₂} {X : α 
→ C} {B : C} (π : (a : α) → X a ⟶ B)   [(CategoryTheory.Pre…
· 使用定理 `CategoryTheory.Presieve.instHasPairwisePullbacksOfHasPullbacks`：∀ {C : T
ype u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X : C} (R : CategoryTheory.
Presieve X)   [CategoryTheory.Limits.HasPullbacks C]…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.PreOneHypercover.w`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] {S : C} (self : CategoryTheory.PreOneHypercover S)   ⦃i₁ i₂ 
: self.I₀⦄ (j : self.I₁…
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
lemma toPullback_cylinder {i j : (cylinder f g).I₀} (k : (cylinder f g).I₁ i j) :
    (cylinder f g).toPullback k = pullback.fst _ _ := by
  apply pullback.hom_ext <;> simp [toPullback]

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.PreOneHypercover.sieve** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.PreOneHypercover`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma sieve₀_cylinder :
    (cylinder f g).sieve₀ =
      Sieve.generate
        (Presieve.bindOfArrows _ E.f <| fun i ↦
          (Sieve.pullback (pullback.lift (f.h₀ _) (g.h₀ _) (by simp))
            (F.sieve₁' _ _)).arrows) := by
  refine le_antisymm ?_ ?_
  · rw [PreZeroHypercover.sieve₀, Sieve.generate_le_iff]
    rintro - - ⟨i⟩
    refine ⟨_, 𝟙 _, (cylinder f g).f _, ⟨_, _, ?_⟩, by simp⟩
    simp only [Sieve.pullback_apply, pullback.condition]
    exact Sieve.downward_closed _ (Sieve.ofArrows_mk _ _ _) _
  · rw [Sieve.generate_le_iff, PreZeroHypercover.sieve₀]
    rintro Z u ⟨i, v, ⟨W, o, o', ⟨j⟩, hoo'⟩⟩
    exact ⟨_, pullback.lift v o hoo'.symm, (cylinder f g).f ⟨i, j⟩, Presieve.ofArrows.mk _,
      by simp⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.PreOneHypercover.sieve** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.PreOneHypercover`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma sieve₁'_cylinder (i j : Σ (i : E.I₀), F.I₁ (f.s₀ i) (g.s₀ i)) :
    (cylinder f g).sieve₁' i j =
      Sieve.pullback
        (pullback.map _ _ _ _ (pullback.fst _ _) (pullback.fst _ _) (𝟙 S) (by simp) (by simp))
        (E.sieve₁' i.1 j.1) := by
  refine le_antisymm ?_ ?_
  · rw [sieve₁', Sieve.ofArrows, Sieve.generate_le_iff]
    rintro - - ⟨k⟩
    refine ⟨E.Y k.down, pullback.snd _ _, E.toPullback k.down, Presieve.ofArrows.mk k.down, ?_⟩
    simp only [cylinder_Y, cylinder_f, toPullback_cylinder, pullback.condition]
  · rw [sieve₁', Sieve.ofArrows, ← Sieve.pullbackArrows_comm, Sieve.generate_le_iff]
    rintro Z u ⟨W, v, ⟨k⟩⟩
    simp_rw [← pullbackSymmetry_inv_comp_fst]
    apply (((cylinder f g).sieve₁' i j)).downward_closed
    rw [sieve₁']
    convert! Sieve.ofArrows_mk _ _ (ULift.up k)
    simp [toPullback_cylinder f g ⟨k⟩]

set_option backward.isDefEq.respectTransparency false in
/-- (Implementation): The refinement morphism `cylinder f g ⟶ E`. -/
@[simps]
/-
**CategoryTheory.PreOneHypercover.cylinderHom** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.PreOneHypercover`。
形式化陈述：cylinderHom : (cylinder f g).Hom E where s₀ p
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(Implementation): The refinement morphism `cylinder f g ⟶ E`.
-/
noncomputable def cylinderHom : (cylinder f g).Hom E where
  s₀ p := p.1
  s₁ k := k.down
  h₀ p := pullback.fst _ _
  h₁ {p q} k := pullback.snd _ _
  w₁₁ k := by
    have : E.p₁ k.down = pullback.lift _ _ (E.w k.down) ≫ pullback.fst _ _ := by simp
    nth_rw 2 [this]
    rw [← pullback.condition_assoc]
    simp
  w₁₂ {p q} k := by
    have : E.p₂ k.down = pullback.lift _ _ (E.w k.down) ≫ pullback.snd _ _ := by simp
    nth_rw 2 [this]
    rw [← pullback.condition_assoc]
    simp
  w₀ := by simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- (Implementation): The homotopy of the morphisms `cylinder f g ⟶ E ⟶ F`. -/
/-
**CategoryTheory.PreOneHypercover.cylinderHomotopy** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.PreOneHypercover`。
形式化陈述：cylinderHomotopy : Homotopy ((cylinderHom f g).comp f) ((cylinderHom f g).
comp g) where H p
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(Implementation): The homotopy of the morphisms `cylinder f g ⟶ E ⟶ F`.
-/
noncomputable def cylinderHomotopy :
    Homotopy ((cylinderHom f g).comp f) ((cylinderHom f g).comp g) where
  H p := p.2
  a p := pullback.snd _ _
  wl p := by
    have : F.p₁ p.snd = pullback.lift _ _ (F.w p.2) ≫ pullback.fst _ _ := by simp
    nth_rw 1 [this]
    rw [← pullback.condition_assoc]
    simp
  wr p := by
    have : g.h₀ p.fst = pullback.lift (f.h₀ p.fst) (g.h₀ p.fst) (by simp) ≫
        pullback.snd (F.f _) (F.f _) := by simp
    dsimp only [cylinder_X, Hom.comp_s₀, cylinder_I₀, Function.comp_apply, cylinderHom_s₀,
      Hom.comp_h₀, cylinderHom_h₀]
    nth_rw 3 [this]
    rw [pullback.condition_assoc]
    simp

/-- Up to homotopy, the category of (pre-)`1`-hypercovers is cofiltered. -/
/-
**CategoryTheory.PreOneHypercover.exists_nonempty_homotopy** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory.PreOneHypercover`。
形式化陈述：exists_nonempty_homotopy (f g : E.Hom F) : exists (W : PreOneHypercover.{m
ax w w'} S) (h : W.Hom E), Nonempty (Homotopy (h.comp f) (h.comp g))
参数：f g : E.Hom F。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Up to homotopy, the category of (pre-)`1`-hypercovers is cofiltered.
-/
lemma exists_nonempty_homotopy (f g : E.Hom F) :
    ∃ (W : PreOneHypercover.{max w w'} S) (h : W.Hom E),
      Nonempty (Homotopy (h.comp f) (h.comp g)) :=
  ⟨cylinder f g, PreOneHypercover.cylinderHom f g, ⟨cylinderHomotopy f g⟩⟩

end PreOneHypercover

namespace GrothendieckTopology

open PreOneHypercover OneHypercover

variable {J : GrothendieckTopology C}

namespace OneHypercover

variable {S : C} {E : OneHypercover.{w} J S} {F : OneHypercover.{w'} J S}
variable [HasPullbacks C]

set_option backward.isDefEq.respectTransparency.types false in
/-- Given two refinement morphism `f, g : E ⟶ F`, this is a `1`-hypercover `W` that
admits a morphism `h : W ⟶ E` such that `h ≫ f` and `h ≫ g` are homotopic. Hence
they become equal after quotienting out by homotopy. -/
@[simps! toPreOneHypercover]
/-
**CategoryTheory.GrothendieckTopology.OneHypercover.cylinder** 是 Mathlib 中的一个定义，
位于命名空间 `CategoryTheory.GrothendieckTopology.OneHypercover`。
形式化陈述：cylinder (f g : E.Hom F) : J.OneHypercover S
参数：f g : E.Hom F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given two refinement morphism `f, g : E ⟶ F`, this is a `1`-hypercover `W` that
admits a morphism `h : W ⟶ E` such that `h ≫ f` and `h ≫ g` are homotopic. Hence
they become equal after quotienting out by homotopy.
-/
noncomputable def cylinder (f g : E.Hom F) : J.OneHypercover S :=
  mk' (PreOneHypercover.cylinder f g)
    (by
      rw [PreOneHypercover.sieve₀_cylinder]
      refine J.bindOfArrows E.mem₀ fun i ↦ ?_
      rw [Sieve.generate_sieve]
      exact J.pullback_stable _ (mem_sieve₁' F _ _))
    (fun i j ↦ by
      rw [PreOneHypercover.sieve₁'_cylinder]
      exact J.pullback_stable _ (mem_sieve₁' E _ _))

/-- Up to homotopy, the category of `1`-hypercovers is cofiltered. -/
/-
**CategoryTheory.GrothendieckTopology.OneHypercover.exists_nonempty_homotopy** 是
 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.GrothendieckTopology.OneHypercover`。
形式化陈述：exists_nonempty_homotopy (f g : E.Hom F) : exists (W : OneHypercover.{max 
w w'} J S) (h : W.Hom E), Nonempty (PreOneHypercover.Homotopy (h.comp f) (h.comp
 g))
参数：f g : E.Hom F。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Up to homotopy, the category of `1`-hypercovers is cofiltered.
-/
lemma exists_nonempty_homotopy (f g : E.Hom F) :
    ∃ (W : OneHypercover.{max w w'} J S) (h : W.Hom E),
      Nonempty (PreOneHypercover.Homotopy (h.comp f) (h.comp g)) :=
  ⟨cylinder f g, PreOneHypercover.cylinderHom f g, ⟨PreOneHypercover.cylinderHomotopy f g⟩⟩

end OneHypercover

variable (J S)

/--
Two refinement morphisms of `1`-hypercovers are homotopic if there exists a homotopy between
them.
Note: This is not an equivalence relation, it is not even reflexive!
-/
/-
**CategoryTheory.GrothendieckTopology.OneHypercover.homotopicRel** 是 Mathlib 中的一
个定义，位于命名空间 `CategoryTheory.GrothendieckTopology.OneHypercover`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     (J : Cate
goryTheory.GrothendieckTopology C) → (S : C) → HomRel (J.OneHypercover S)
参数：J : CategoryTheory.GrothendieckTopology C；S : C；J.OneHypercover S。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Two refinement morphisms of `1`-hypercovers are homotopic if there exists a homo
topy between
them.
Note: This is not an equivalence relation, it is not even reflexive!
-/
def OneHypercover.homotopicRel : HomRel (J.OneHypercover S) :=
  fun _ _ f g ↦ Nonempty (PreOneHypercover.Homotopy f g)

/-- The category of `1`-hypercovers with refinement morphisms up to homotopy. -/
/-
**CategoryTheory.GrothendieckTopology.HOneHypercover** 是 Mathlib 中的一个缩写定义，位于命名空间
 `CategoryTheory.GrothendieckTopology`。
形式化陈述：HOneHypercover (S : C)
参数：S : C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of `1`-hypercovers with refinement morphisms up to homotopy.
-/
abbrev HOneHypercover (S : C) := Quotient (OneHypercover.homotopicRel J S)

/-- The canonical projection from `1`-hypercovers to `1`-hypercovers up to homotopy. -/
/-
**CategoryTheory.GrothendieckTopology.OneHypercover.toHOneHypercover** 是 Mathlib
 中的一个定义，位于命名空间 `CategoryTheory.GrothendieckTopology.OneHypercover`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     (J : Cate
goryTheory.GrothendieckTopology C) →       (S : C) → CategoryTheory.Functor (J.O
neHypercover S) (J.HOneHypercover S)
参数：J : CategoryTheory.GrothendieckTopology C；S : C；J.OneHypercover S；J.HOneHyper
cover S。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical projection from `1`-hypercovers to `1`-hypercovers up to homotopy.
-/
abbrev OneHypercover.toHOneHypercover (S : C) : J.OneHypercover S ⥤ J.HOneHypercover S :=
  Quotient.functor _
/-
**CategoryTheory.GrothendieckTopology._root_.CategoryTheory.PreOneHypercover.Hom
otopy.map_eq_map** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.GrothendieckTopology`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.CategoryTheory.PreOneHypercover.Homotopy.map_eq_map {S : C} {E F : J.OneHypercover S}
    {f g : E ⟶ F} (H : Homotopy f g) :
    (toHOneHypercover J S).map f = (toHOneHypercover J S).map g :=
  Quotient.sound _ ⟨H⟩

namespace HOneHypercover

variable {S : C}

/-
**CategoryTheory.GrothendieckTopology.HOneHypercover.** 是 Mathlib 中的一个实例，位于命名空间 
`CategoryTheory.GrothendieckTopology.HOneHypercover`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Nonempty (J.HOneHypercover S) := ⟨⟨Nonempty.some inferInstance⟩⟩

set_option backward.isDefEq.respectTransparency false in
/-- If `C` has pullbacks, the category of `1`-hypercovers up to homotopy is cofiltered. -/
/-
**CategoryTheory.GrothendieckTopology.HOneHypercover.isCofiltered_of_hasPullback
s** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.GrothendieckTopology.HOneHypercover`
。
形式化陈述：isCofiltered_of_hasPullbacks [HasPullbacks C] : IsCofiltered (J.HOneHyperc
over S) where cone_objs {E F}
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Precoverage.ZeroHypercover.instHasPullbackFOfHasPullbacks
Presieve₀`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} (E
 : CategoryTheory.PreZeroHypercover X) (f : Y ⟶ X)   [E.presieve₀.HasPu…
· 使用定理 `CategoryTheory.Presieve.instHasPullbacksOfArrowsOfHasPullback`：∀ {C : Ty
pe u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : Y ⟶ X) {ι : Ty
pe u_1} (Z : ι → C)   (g : (i : ι) → Z i ⟶ X) [∀ (i…
· 使用定理 `CategoryTheory.Precoverage.ZeroHypercover.instHasPullbackFOfHasPullbacks
Presieve₀_1`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} 
(E : CategoryTheory.PreZeroHypercover X) (f : Y ⟶ X)   [E.presieve₀.HasPu…
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Presieve.instHasPullbacksOfHasPullbacks`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {X : C} [CategoryTheory.Limits.HasPu
llbacks C]   (R : CategoryTheory.Presieve X)…
· 使用定理 `CategoryTheory.IsPullback.instHasPullbackFst`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {P X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_
1 : CategoryTheory.Limits.HasPullb…
· 使用定理 `CategoryTheory.Functor.map_surjective`：map_surjective (F : C ⥤ D) [Full 
F] : Function.Surjective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
· 使用引理 `CategoryTheory.GrothendieckTopology.OneHypercover.exists_nonempty_homoto
py`：exists_nonempty_homotopy (f g : E.Hom F) : exists (W : OneHypercover.{max w 
w'} J S) (h : W.Hom E), Nonempty (PreOneHypercover.Homotopy (h.c…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.PreOneHypercover.Homotopy.map_eq_map`：∀ {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C] (J : CategoryTheory.GrothendieckTopology C
) {S : C}   {E F : J.OneHypercover S} {f …
· 使用定理 `CategoryTheory.GrothendieckTopology.HOneHypercover.instNonempty`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] (J : CategoryTheory.Grothendie
ckTopology C) {S : C},   Nonempty (J.HOneHypercover S…

--- 原说明 ---
If `C` has pullbacks, the category of `1`-hypercovers up to homotopy is cofilter
ed.
-/
instance isCofiltered_of_hasPullbacks [HasPullbacks C] : IsCofiltered (J.HOneHypercover S) where
  cone_objs {E F} :=
    ⟨⟨E.1.inter F.1⟩, Quot.mk _ (PreOneHypercover.interFst _ _),
      Quot.mk _ (PreOneHypercover.interSnd _ _), ⟨⟩⟩
  cone_maps {X Y} f g := by
    obtain ⟨(f : X.1 ⟶ Y.1), rfl⟩ := (toHOneHypercover J S).map_surjective f
    obtain ⟨(g : X.1 ⟶ Y.1), rfl⟩ := (toHOneHypercover J S).map_surjective g
    obtain ⟨W, h, ⟨H⟩⟩ := OneHypercover.exists_nonempty_homotopy f g
    use (toHOneHypercover J S).obj W, (toHOneHypercover J S).map h
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact H.map_eq_map

end HOneHypercover

end GrothendieckTopology

end CategoryTheory

