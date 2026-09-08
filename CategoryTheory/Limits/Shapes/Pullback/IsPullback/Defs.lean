/-
Copyright (c) 2022 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Joël Riou, Calle Sönne
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Pullbacks


/-!
# Pullback and pushout squares

We provide another API for pullbacks and pushouts.

`IsPullback fst snd f g` is the proposition that
```
  P --fst--> X
  |          |
 snd         f
  |          |
  v          v
  Y ---g---> Z

```
is a pullback square.

(And similarly for `IsPushout`.)

We provide the glue to go back and forth to the usual `IsLimit` API for pullbacks, and prove
`IsPullback (pullback.fst f g) (pullback.snd f g) f g`
for the usual `pullback f g` provided by the `HasLimit` API.
-/

@[expose] public section

noncomputable section

open CategoryTheory

open CategoryTheory.Limits

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]

/-- The proposition that a square
```
  P --fst--> X
  |          |
 snd         f
  |          |
  v          v
  Y ---g---> Z

```
is a pullback square. (Also known as a fibered product or Cartesian square.)
-/
/-
**CategoryTheory.IsPullback** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] → {P X Y Z :
 C} → (P ⟶ X) → (P ⟶ Y) → (X ⟶ Z) → (Y ⟶ Z) → Prop
参数：P ⟶ X；P ⟶ Y；X ⟶ Z；Y ⟶ Z。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The proposition that a square
```
  P --fst--> X
  |          |
 snd         f
  |          |
  v          v
  Y ---g---> Z

```
is a pullback square. (Also known as a fibered product or Cartesian square.)
-/
structure IsPullback {P X Y Z : C} (fst : P ⟶ X) (snd : P ⟶ Y) (f : X ⟶ Z) (g : Y ⟶ Z) : Prop
    extends CommSq fst snd f g where
  /-- the pullback cone is a limit -/
  isLimit' : Nonempty (IsLimit (PullbackCone.mk _ _ w))

/-- The proposition that a square
```
  Z ---f---> X
  |          |
  g         inl
  |          |
  v          v
  Y --inr--> P

```
is a pushout square. (Also known as a fiber coproduct or co-Cartesian square.)
-/
/-
**CategoryTheory.IsPushout** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] → {Z X Y P :
 C} → (Z ⟶ X) → (Z ⟶ Y) → (X ⟶ P) → (Y ⟶ P) → Prop
参数：Z ⟶ X；Z ⟶ Y；X ⟶ P；Y ⟶ P。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The proposition that a square
```
  Z ---f---> X
  |          |
  g         inl
  |          |
  v          v
  Y --inr--> P

```
is a pushout square. (Also known as a fiber coproduct or co-Cartesian square.)
-/
structure IsPushout {Z X Y P : C} (f : Z ⟶ X) (g : Z ⟶ Y) (inl : X ⟶ P) (inr : Y ⟶ P) : Prop
    extends CommSq f g inl inr where
  /-- the pushout cocone is a colimit -/
  isColimit' : Nonempty (IsColimit (PushoutCocone.mk _ _ w))

namespace IsPullback
variable {P X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}

/-- The (limiting) `PullbackCone f g` implicit in the statement
that we have an `IsPullback fst snd f g`.
-/
/-
**CategoryTheory.IsPullback.cone** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.IsPul
lback`。
形式化陈述：cone (h : IsPullback fst snd f g) : PullbackCone f g
参数：h : IsPullback fst snd f g。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPullback.toCommSq`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {P X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z}   
{g : Y ⟶ Z}, CategoryThe…

--- 原说明 ---
The (limiting) `PullbackCone f g` implicit in the statement
that we have an `IsPullback fst snd f g`.
-/
def cone (h : IsPullback fst snd f g) : PullbackCone f g :=
  h.toCommSq.cone

@[simp]
/-
**CategoryTheory.IsPullback.cone_fst** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.I
sPullback`。
形式化陈述：cone_fst (h : IsPullback fst snd f g) : h.cone.fst = fst
参数：h : IsPullback fst snd f g。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cone_fst (h : IsPullback fst snd f g) : h.cone.fst = fst :=
  rfl

@[simp]
/-
**CategoryTheory.IsPullback.cone_snd** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.I
sPullback`。
形式化陈述：cone_snd (h : IsPullback fst snd f g) : h.cone.snd = snd
参数：h : IsPullback fst snd f g。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cone_snd (h : IsPullback fst snd f g) : h.cone.snd = snd :=
  rfl

/-- The cone obtained from `IsPullback fst snd f g` is a limit cone.
-/
/-
**CategoryTheory.IsPullback.isLimit** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Is
Pullback`。
形式化陈述：isLimit (h : IsPullback fst snd f g) : IsLimit h.cone
参数：h : IsPullback fst snd f g。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPullback.isLimit'`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {P X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z}   
{g : Y ⟶ Z} (self : Cate…

--- 原说明 ---
The cone obtained from `IsPullback fst snd f g` is a limit cone.
-/
noncomputable def isLimit (h : IsPullback fst snd f g) : IsLimit h.cone :=
  h.isLimit'.some

/-- API for PullbackCone.IsLimit.lift for `IsPullback` -/
/-
**CategoryTheory.IsPullback.lift** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.IsPul
lback`。
形式化陈述：lift (hP : IsPullback fst snd f g) {W : C} (h : W ⟶ X) (k : W ⟶ Y) (w : h 
≫ f = k ≫ g) : W ⟶ P
参数：hP : IsPullback fst snd f g；h : W ⟶ X；k : W ⟶ Y；w : h ≫ f = k ≫ g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
API for PullbackCone.IsLimit.lift for `IsPullback`
-/
noncomputable def lift (hP : IsPullback fst snd f g) {W : C} (h : W ⟶ X) (k : W ⟶ Y)
    (w : h ≫ f = k ≫ g) : W ⟶ P :=
  PullbackCone.IsLimit.lift hP.isLimit h k w

@[reassoc (attr := simp)]
/-
**CategoryTheory.IsPullback.lift_fst** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.I
sPullback`。
形式化陈述：lift_fst (hP : IsPullback fst snd f g) {W : C} (h : W ⟶ X) (k : W ⟶ Y) (w 
: h ≫ f = k ≫ g) : hP.lift h k w ≫ fst = h
参数：hP : IsPullback fst snd f g；h : W ⟶ X；k : W ⟶ Y；w : h ≫ f = k ≫ g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.PullbackCone.IsLimit.lift_fst`：∀ {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   {t :
 CategoryTheory.Limits.PullbackCone f g} …
-/
lemma lift_fst (hP : IsPullback fst snd f g) {W : C} (h : W ⟶ X) (k : W ⟶ Y)
    (w : h ≫ f = k ≫ g) : hP.lift h k w ≫ fst = h :=
  PullbackCone.IsLimit.lift_fst hP.isLimit h k w

@[reassoc (attr := simp)]
/-
**CategoryTheory.IsPullback.lift_snd** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.I
sPullback`。
形式化陈述：lift_snd (hP : IsPullback fst snd f g) {W : C} (h : W ⟶ X) (k : W ⟶ Y) (w 
: h ≫ f = k ≫ g) : hP.lift h k w ≫ snd = k
参数：hP : IsPullback fst snd f g；h : W ⟶ X；k : W ⟶ Y；w : h ≫ f = k ≫ g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.PullbackCone.IsLimit.lift_snd`：∀ {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   {t :
 CategoryTheory.Limits.PullbackCone f g} …
-/
lemma lift_snd (hP : IsPullback fst snd f g) {W : C} (h : W ⟶ X) (k : W ⟶ Y)
    (w : h ≫ f = k ≫ g) : hP.lift h k w ≫ snd = k :=
  PullbackCone.IsLimit.lift_snd hP.isLimit h k w
/-
**CategoryTheory.IsPullback.exists_lift** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.IsPullback`。
形式化陈述：exists_lift (hP : IsPullback fst snd f g) {W : C} (h : W ⟶ X) (k : W ⟶ Y) 
(w : h ≫ f = k ≫ g) : exists (l : W ⟶ P), l ≫ fst = h ∧ l ≫ snd = k
参数：hP : IsPullback fst snd f g；h : W ⟶ X；k : W ⟶ Y；w : h ≫ f = k ≫ g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.IsPullback.lift_fst`：lift_fst (hP : IsPullback fst snd f 
g) {W : C} (h : W ⟶ X) (k : W ⟶ Y) (w : h ≫ f = k ≫ g) : hP.lift h k w ≫ fst = h
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CategoryTheory.IsPullback.lift_snd`：lift_snd (hP : IsPullback fst snd f 
g) {W : C} (h : W ⟶ X) (k : W ⟶ Y) (w : h ≫ f = k ≫ g) : hP.lift h k w ≫ snd = k
-/
lemma exists_lift (hP : IsPullback fst snd f g)
    {W : C} (h : W ⟶ X) (k : W ⟶ Y) (w : h ≫ f = k ≫ g) :
    ∃ (l : W ⟶ P), l ≫ fst = h ∧ l ≫ snd = k :=
  ⟨hP.lift h k w, by simp, by simp⟩
/-
**CategoryTheory.IsPullback.hom_ext** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Is
Pullback`。
形式化陈述：hom_ext (hP : IsPullback fst snd f g) {W : C} {k l : W ⟶ P} (h₀ : k ≫ fst 
= l ≫ fst) (h₁ : k ≫ snd = l ≫ snd) : k = l
参数：hP : IsPullback fst snd f g；h₀ : k ≫ fst = l ≫ fst；h₁ : k ≫ snd = l ≫ snd。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.PullbackCone.IsLimit.hom_ext`：∀ {C : Type u} [inst
 : CategoryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   {t : 
CategoryTheory.Limits.PullbackCone f g} …
-/
lemma hom_ext (hP : IsPullback fst snd f g) {W : C} {k l : W ⟶ P}
    (h₀ : k ≫ fst = l ≫ fst) (h₁ : k ≫ snd = l ≫ snd) : k = l :=
  PullbackCone.IsLimit.hom_ext hP.isLimit h₀ h₁

set_option backward.defeqAttrib.useBackward true in
/-- If `c` is a limiting pullback cone, then we have an `IsPullback c.fst c.snd f g`. -/
/-
**CategoryTheory.IsPullback.of_isLimit** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.IsPullback`。
形式化陈述：of_isLimit {c : PullbackCone f g} (h : Limits.IsLimit c) : IsPullback c.fs
t c.snd f g
参数：h : Limits.IsLimit c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.PullbackCone.condition`：condition (t : PullbackCon
e f g) : fst t ≫ f = snd t ≫ g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `c` is a limiting pullback cone, then we have an `IsPullback c.fst c.snd f g`
.
-/
theorem of_isLimit {c : PullbackCone f g} (h : Limits.IsLimit c) : IsPullback c.fst c.snd f g :=
  { w := c.condition
    isLimit' := ⟨IsLimit.ofIsoLimit h (Limits.PullbackCone.ext (Iso.refl _)
      (by simp) (by simp))⟩ }

/-- A variant of `of_isLimit` that is more useful with `apply`. -/
/-
**CategoryTheory.IsPullback.of_isLimit'** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.IsPullback`。
形式化陈述：of_isLimit' (w : CommSq fst snd f g) (h : Limits.IsLimit w.cone) : IsPullb
ack fst snd f g
参数：w : CommSq fst snd f g；h : Limits.IsLimit w.cone。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPullback.of_isLimit`：of_isLimit {c : PullbackCone f g} 
(h : Limits.IsLimit c) : IsPullback c.fst c.snd f g

--- 原说明 ---
A variant of `of_isLimit` that is more useful with `apply`.
-/
theorem of_isLimit' (w : CommSq fst snd f g) (h : Limits.IsLimit w.cone) :
    IsPullback fst snd f g :=
  of_isLimit h

set_option backward.isDefEq.respectTransparency false in
/-- Variant of `of_isLimit` for an arbitrary cone on a diagram `WalkingCospan ⥤ C`. -/
/-
**CategoryTheory.IsPullback.of_isLimit_cone** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.IsPullback`。
形式化陈述：of_isLimit_cone {D : WalkingCospan ⥤ C} {c : Cone D} (hc : IsLimit c) : Is
Pullback (c.π.app .left) (c.π.app .right) (D.map WalkingCospan.Hom.inl) (D.map W
alkingCospan.Hom.inr) where w
参数：hc : IsLimit c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.Cone.w`：∀ {J : Type u₁} [inst : CategoryTheory.Cat
egory.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃} C]   
{F : CategoryTheor…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…

--- 原说明 ---
Variant of `of_isLimit` for an arbitrary cone on a diagram `WalkingCospan ⥤ C`.
-/
lemma of_isLimit_cone {D : WalkingCospan ⥤ C} {c : Cone D} (hc : IsLimit c) :
    IsPullback (c.π.app .left) (c.π.app .right) (D.map WalkingCospan.Hom.inl)
      (D.map WalkingCospan.Hom.inr) where
  w := by simp_rw [Cone.w]
  isLimit' := ⟨IsLimit.equivOfNatIsoOfIso _ _ _ (PullbackCone.isoMk c) hc⟩
/-
**CategoryTheory.IsPullback.hasPullback** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.IsPullback`。
形式化陈述：hasPullback (h : IsPullback fst snd f g) : HasPullback f g where exists_li
mit
参数：h : IsPullback fst snd f g。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hasPullback (h : IsPullback fst snd f g) : HasPullback f g where
  exists_limit := ⟨⟨h.cone, h.isLimit⟩⟩

/-- The pullback provided by `HasPullback f g` fits into an `IsPullback`. -/
/-
**CategoryTheory.IsPullback.of_hasPullback** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.IsPullback`。
形式化陈述：of_hasPullback (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] : IsPullback (pul
lback.fst f g) (pullback.snd f g) f g
参数：f : X ⟶ Z；g : Y ⟶ Z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPullback.of_isLimit`：of_isLimit {c : PullbackCone f g} 
(h : Limits.IsLimit c) : IsPullback c.fst c.snd f g

--- 原说明 ---
The pullback provided by `HasPullback f g` fits into an `IsPullback`.
-/
theorem of_hasPullback (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] :
    IsPullback (pullback.fst f g) (pullback.snd f g) f g :=
  of_isLimit (limit.isLimit (cospan f g))


section

variable (X Y)

variable {P' : C} {fst' : P' ⟶ X} {snd' : P' ⟶ Y}

/-- Any object at the top left of a pullback square is isomorphic to the object at the top left
of any other pullback square with the same cospan. -/
/-
**CategoryTheory.IsPullback.isoIsPullback** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.IsPullback`。
形式化陈述：isoIsPullback (h : IsPullback fst snd f g) (h' : IsPullback fst' snd' f g)
 : P ≅ P'
参数：h : IsPullback fst snd f g；h' : IsPullback fst' snd' f g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any object at the top left of a pullback square is isomorphic to the object at t
he top left
of any other pullback square with the same cospan.
-/
noncomputable def isoIsPullback (h : IsPullback fst snd f g) (h' : IsPullback fst' snd' f g) :
    P ≅ P' :=
  IsLimit.conePointUniqueUpToIso h.isLimit h'.isLimit

@[reassoc (attr := simp)]
/-
**CategoryTheory.IsPullback.isoIsPullback_hom_fst** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.IsPullback`。
形式化陈述：isoIsPullback_hom_fst (h : IsPullback fst snd f g) (h' : IsPullback fst' s
nd' f g) : (h.isoIsPullback _ _ h').hom ≫ fst' = fst
参数：h : IsPullback fst snd f g；h' : IsPullback fst' snd' f g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsLimit.conePointUniqueUpToIso_hom_comp`：conePoint
UniqueUpToIso_hom_comp {s t : Cone F} (P : IsLimit s) (Q : IsLimit t) (j : J) : 
(conePointUniqueUpToIso P Q).hom ≫ t.π.app j = s.π.…
-/
theorem isoIsPullback_hom_fst (h : IsPullback fst snd f g) (h' : IsPullback fst' snd' f g) :
    (h.isoIsPullback _ _ h').hom ≫ fst' = fst :=
  IsLimit.conePointUniqueUpToIso_hom_comp h.isLimit h'.isLimit WalkingCospan.left

@[reassoc (attr := simp)]
/-
**CategoryTheory.IsPullback.isoIsPullback_hom_snd** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.IsPullback`。
形式化陈述：isoIsPullback_hom_snd (h : IsPullback fst snd f g) (h' : IsPullback fst' s
nd' f g) : (h.isoIsPullback _ _ h').hom ≫ snd' = snd
参数：h : IsPullback fst snd f g；h' : IsPullback fst' snd' f g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsLimit.conePointUniqueUpToIso_hom_comp`：conePoint
UniqueUpToIso_hom_comp {s t : Cone F} (P : IsLimit s) (Q : IsLimit t) (j : J) : 
(conePointUniqueUpToIso P Q).hom ≫ t.π.app j = s.π.…
-/
theorem isoIsPullback_hom_snd (h : IsPullback fst snd f g) (h' : IsPullback fst' snd' f g) :
    (h.isoIsPullback _ _ h').hom ≫ snd' = snd :=
  IsLimit.conePointUniqueUpToIso_hom_comp h.isLimit h'.isLimit WalkingCospan.right

@[reassoc (attr := simp)]
/-
**CategoryTheory.IsPullback.isoIsPullback_inv_fst** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.IsPullback`。
形式化陈述：isoIsPullback_inv_fst (h : IsPullback fst snd f g) (h' : IsPullback fst' s
nd' f g) : (h.isoIsPullback _ _ h').inv ≫ fst = fst'
参数：h : IsPullback fst snd f g；h' : IsPullback fst' snd' f g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsPullback.isoIsPullback_hom_fst`：isoIsPullback_hom_fst (
h : IsPullback fst snd f g) (h' : IsPullback fst' snd' f g) : (h.isoIsPullback _
 _ h').hom ≫ fst' = fst
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem isoIsPullback_inv_fst (h : IsPullback fst snd f g) (h' : IsPullback fst' snd' f g) :
    (h.isoIsPullback _ _ h').inv ≫ fst = fst' := by
  simp only [Iso.inv_comp_eq, isoIsPullback_hom_fst]

@[reassoc (attr := simp)]
/-
**CategoryTheory.IsPullback.isoIsPullback_inv_snd** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.IsPullback`。
形式化陈述：isoIsPullback_inv_snd (h : IsPullback fst snd f g) (h' : IsPullback fst' s
nd' f g) : (h.isoIsPullback _ _ h').inv ≫ snd = snd'
参数：h : IsPullback fst snd f g；h' : IsPullback fst' snd' f g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsPullback.isoIsPullback_hom_snd`：isoIsPullback_hom_snd (
h : IsPullback fst snd f g) (h' : IsPullback fst' snd' f g) : (h.isoIsPullback _
 _ h').hom ≫ snd' = snd
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem isoIsPullback_inv_snd (h : IsPullback fst snd f g) (h' : IsPullback fst' snd' f g) :
    (h.isoIsPullback _ _ h').inv ≫ snd = snd' := by
  simp only [Iso.inv_comp_eq, isoIsPullback_hom_snd]

end

/-- Any object at the top left of a pullback square is
isomorphic to the pullback provided by the `HasLimit` API. -/
/-
**CategoryTheory.IsPullback.isoPullback** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.IsPullback`。
形式化陈述：isoPullback (h : IsPullback fst snd f g) [HasPullback f g] : P ≅ pullback 
f g
参数：h : IsPullback fst snd f g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any object at the top left of a pullback square is
isomorphic to the pullback provided by the `HasLimit` API.
-/
noncomputable def isoPullback (h : IsPullback fst snd f g) [HasPullback f g] : P ≅ pullback f g :=
  (limit.isoLimitCone ⟨_, h.isLimit⟩).symm


set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.IsPullback.isoPullback_hom_fst** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.IsPullback`。
形式化陈述：isoPullback_hom_fst (h : IsPullback fst snd f g) [HasPullback f g] : h.iso
Pullback.hom ≫ pullback.fst _ _ = fst
参数：h : IsPullback fst snd f g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.CommSq.w`：∀ {C : Type u_1} [inst : CategoryTheory.Categor
y.{v_1, u_1} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z}   {i : Y ⟶ Z},
   CategoryTh…
· 使用定理 `CategoryTheory.IsPullback.toCommSq`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {P X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z}   
{g : Y ⟶ Z}, CategoryThe…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.limit.isoLimitCone_inv_π`：∀ {J : Type u₁} [inst : 
CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Catego
ry.{v, u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PullbackCone.mk_π_app`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {W : C} (fst :
 W ⟶ X)   (snd : W ⟶ Y)   (eq :  …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem isoPullback_hom_fst (h : IsPullback fst snd f g) [HasPullback f g] :
    h.isoPullback.hom ≫ pullback.fst _ _ = fst := by
  dsimp [isoPullback, cone, CommSq.cone]
  simp

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.IsPullback.isoPullback_hom_snd** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.IsPullback`。
形式化陈述：isoPullback_hom_snd (h : IsPullback fst snd f g) [HasPullback f g] : h.iso
Pullback.hom ≫ pullback.snd _ _ = snd
参数：h : IsPullback fst snd f g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.CommSq.w`：∀ {C : Type u_1} [inst : CategoryTheory.Categor
y.{v_1, u_1} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z}   {i : Y ⟶ Z},
   CategoryTh…
· 使用定理 `CategoryTheory.IsPullback.toCommSq`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {P X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z}   
{g : Y ⟶ Z}, CategoryThe…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.limit.isoLimitCone_inv_π`：∀ {J : Type u₁} [inst : 
CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Catego
ry.{v, u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PullbackCone.mk_π_app`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {W : C} (fst :
 W ⟶ X)   (snd : W ⟶ Y)   (eq :  …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem isoPullback_hom_snd (h : IsPullback fst snd f g) [HasPullback f g] :
    h.isoPullback.hom ≫ pullback.snd _ _ = snd := by
  dsimp [isoPullback, cone, CommSq.cone]
  simp

@[reassoc (attr := simp)]
/-
**CategoryTheory.IsPullback.isoPullback_inv_fst** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.IsPullback`。
形式化陈述：isoPullback_inv_fst (h : IsPullback fst snd f g) [HasPullback f g] : h.iso
Pullback.inv ≫ fst = pullback.fst _ _
参数：h : IsPullback fst snd f g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsPullback.isoPullback_hom_fst`：isoPullback_hom_fst (h : 
IsPullback fst snd f g) [HasPullback f g] : h.isoPullback.hom ≫ pullback.fst _ _
 = fst
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem isoPullback_inv_fst (h : IsPullback fst snd f g) [HasPullback f g] :
    h.isoPullback.inv ≫ fst = pullback.fst _ _ := by simp [Iso.inv_comp_eq]

@[reassoc (attr := simp)]
/-
**CategoryTheory.IsPullback.isoPullback_inv_snd** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.IsPullback`。
形式化陈述：isoPullback_inv_snd (h : IsPullback fst snd f g) [HasPullback f g] : h.iso
Pullback.inv ≫ snd = pullback.snd _ _
参数：h : IsPullback fst snd f g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsPullback.isoPullback_hom_snd`：isoPullback_hom_snd (h : 
IsPullback fst snd f g) [HasPullback f g] : h.isoPullback.hom ≫ pullback.snd _ _
 = snd
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem isoPullback_inv_snd (h : IsPullback fst snd f g) [HasPullback f g] :
    h.isoPullback.inv ≫ snd = pullback.snd _ _ := by simp [Iso.inv_comp_eq]

end IsPullback

namespace IsPushout

variable {Z X Y P : C} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P} {inr : Y ⟶ P}

/-- The (colimiting) `PushoutCocone f g` implicit in the statement
that we have an `IsPushout f g inl inr`.
-/
/-
**CategoryTheory.IsPushout.cocone** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.IsPu
shout`。
形式化陈述：cocone (h : IsPushout f g inl inr) : PushoutCocone f g
参数：h : IsPushout f g inl inr。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPushout.toCommSq`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {Z X Y P : C} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P}   {in
r : Y ⟶ P}, CategoryThe…

--- 原说明 ---
The (colimiting) `PushoutCocone f g` implicit in the statement
that we have an `IsPushout f g inl inr`.
-/
def cocone (h : IsPushout f g inl inr) : PushoutCocone f g :=
  h.toCommSq.cocone

@[simp]
/-
**CategoryTheory.IsPushout.cocone_inl** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
IsPushout`。
形式化陈述：cocone_inl (h : IsPushout f g inl inr) : h.cocone.inl = inl
参数：h : IsPushout f g inl inr。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cocone_inl (h : IsPushout f g inl inr) : h.cocone.inl = inl :=
  rfl

@[simp]
/-
**CategoryTheory.IsPushout.cocone_inr** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
IsPushout`。
形式化陈述：cocone_inr (h : IsPushout f g inl inr) : h.cocone.inr = inr
参数：h : IsPushout f g inl inr。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cocone_inr (h : IsPushout f g inl inr) : h.cocone.inr = inr :=
  rfl

/-- The cocone obtained from `IsPushout f g inl inr` is a colimit cocone.
-/
/-
**CategoryTheory.IsPushout.isColimit** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.I
sPushout`。
形式化陈述：isColimit (h : IsPushout f g inl inr) : IsColimit h.cocone
参数：h : IsPushout f g inl inr。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPushout.isColimit'`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {Z X Y P : C} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P}   {
inr : Y ⟶ P} (self : Cate…

--- 原说明 ---
The cocone obtained from `IsPushout f g inl inr` is a colimit cocone.
-/
noncomputable def isColimit (h : IsPushout f g inl inr) : IsColimit h.cocone :=
  h.isColimit'.some

/-- API for PushoutCocone.IsColimit.lift for `IsPushout` -/
/-
**CategoryTheory.IsPushout.desc** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.IsPush
out`。
形式化陈述：desc (hP : IsPushout f g inl inr) {W : C} (h : X ⟶ W) (k : Y ⟶ W) (w : f ≫
 h = g ≫ k) : P ⟶ W
参数：hP : IsPushout f g inl inr；h : X ⟶ W；k : Y ⟶ W；w : f ≫ h = g ≫ k。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
API for PushoutCocone.IsColimit.lift for `IsPushout`
-/
noncomputable def desc (hP : IsPushout f g inl inr) {W : C} (h : X ⟶ W) (k : Y ⟶ W)
    (w : f ≫ h = g ≫ k) : P ⟶ W :=
  PushoutCocone.IsColimit.desc hP.isColimit h k w

@[reassoc (attr := simp)]
/-
**CategoryTheory.IsPushout.inl_desc** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Is
Pushout`。
形式化陈述：inl_desc (hP : IsPushout f g inl inr) {W : C} (h : X ⟶ W) (k : Y ⟶ W) (w :
 f ≫ h = g ≫ k) : inl ≫ hP.desc h k w = h
参数：hP : IsPushout f g inl inr；h : X ⟶ W；k : Y ⟶ W；w : f ≫ h = g ≫ k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.PushoutCocone.IsColimit.inl_desc`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}   {
t : CategoryTheory.Limits.PushoutCocone f g}…
-/
lemma inl_desc (hP : IsPushout f g inl inr) {W : C} (h : X ⟶ W) (k : Y ⟶ W)
    (w : f ≫ h = g ≫ k) : inl ≫ hP.desc h k w = h :=
  PushoutCocone.IsColimit.inl_desc hP.isColimit h k w

@[reassoc (attr := simp)]
/-
**CategoryTheory.IsPushout.inr_desc** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Is
Pushout`。
形式化陈述：inr_desc (hP : IsPushout f g inl inr) {W : C} (h : X ⟶ W) (k : Y ⟶ W) (w :
 f ≫ h = g ≫ k) : inr ≫ hP.desc h k w = k
参数：hP : IsPushout f g inl inr；h : X ⟶ W；k : Y ⟶ W；w : f ≫ h = g ≫ k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.PushoutCocone.IsColimit.inr_desc`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}   {
t : CategoryTheory.Limits.PushoutCocone f g}…
-/
lemma inr_desc (hP : IsPushout f g inl inr) {W : C} (h : X ⟶ W) (k : Y ⟶ W)
    (w : f ≫ h = g ≫ k) : inr ≫ hP.desc h k w = k :=
  PushoutCocone.IsColimit.inr_desc hP.isColimit h k w
/-
**CategoryTheory.IsPushout.exists_desc** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory
.IsPushout`。
形式化陈述：exists_desc (hP : IsPushout f g inl inr) {W : C} (h : X ⟶ W) (k : Y ⟶ W) (
w : f ≫ h = g ≫ k) : exists (d : P ⟶ W), inl ≫ d = h ∧ inr ≫ d = k
参数：hP : IsPushout f g inl inr；h : X ⟶ W；k : Y ⟶ W；w : f ≫ h = g ≫ k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.IsPushout.inl_desc`：inl_desc (hP : IsPushout f g inl inr)
 {W : C} (h : X ⟶ W) (k : Y ⟶ W) (w : f ≫ h = g ≫ k) : inl ≫ hP.desc h k w = h
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CategoryTheory.IsPushout.inr_desc`：inr_desc (hP : IsPushout f g inl inr)
 {W : C} (h : X ⟶ W) (k : Y ⟶ W) (w : f ≫ h = g ≫ k) : inr ≫ hP.desc h k w = k
-/
lemma exists_desc (hP : IsPushout f g inl inr)
    {W : C} (h : X ⟶ W) (k : Y ⟶ W) (w : f ≫ h = g ≫ k) :
    ∃ (d : P ⟶ W), inl ≫ d = h ∧ inr ≫ d = k :=
  ⟨hP.desc h k w, by simp, by simp⟩
/-
**CategoryTheory.IsPushout.hom_ext** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.IsP
ushout`。
形式化陈述：hom_ext (hP : IsPushout f g inl inr) {W : C} {k l : P ⟶ W} (h₀ : inl ≫ k =
 inl ≫ l) (h₁ : inr ≫ k = inr ≫ l) : k = l
参数：hP : IsPushout f g inl inr；h₀ : inl ≫ k = inl ≫ l；h₁ : inr ≫ k = inr ≫ l。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.PushoutCocone.IsColimit.hom_ext`：∀ {C : Type u} [i
nst : CategoryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}   {t
 : CategoryTheory.Limits.PushoutCocone f g}…
-/
lemma hom_ext (hP : IsPushout f g inl inr) {W : C} {k l : P ⟶ W}
    (h₀ : inl ≫ k = inl ≫ l) (h₁ : inr ≫ k = inr ≫ l) : k = l :=
  PushoutCocone.IsColimit.hom_ext hP.isColimit h₀ h₁

set_option backward.defeqAttrib.useBackward true in
/-- If `c` is a colimiting pushout cocone, then we have an `IsPushout f g c.inl c.inr`. -/
/-
**CategoryTheory.IsPushout.of_isColimit** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.IsPushout`。
形式化陈述：of_isColimit {c : PushoutCocone f g} (h : Limits.IsColimit c) : IsPushout 
f g c.inl c.inr
参数：h : Limits.IsColimit c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.PushoutCocone.condition`：condition (t : PushoutCoc
one f g) : f ≫ inl t = g ≫ inr t
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

--- 原说明 ---
If `c` is a colimiting pushout cocone, then we have an `IsPushout f g c.inl c.in
r`.
-/
theorem of_isColimit {c : PushoutCocone f g} (h : Limits.IsColimit c) : IsPushout f g c.inl c.inr :=
  { w := c.condition
    isColimit' :=
      ⟨IsColimit.ofIsoColimit h (Limits.PushoutCocone.ext (Iso.refl _)
        (by simp) (by simp))⟩ }

/-- A variant of `of_isColimit` that is more useful with `apply`. -/
/-
**CategoryTheory.IsPushout.of_isColimit'** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.IsPushout`。
形式化陈述：of_isColimit' (w : CommSq f g inl inr) (h : Limits.IsColimit w.cocone) : I
sPushout f g inl inr
参数：w : CommSq f g inl inr；h : Limits.IsColimit w.cocone。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPushout.of_isColimit`：of_isColimit {c : PushoutCocone f
 g} (h : Limits.IsColimit c) : IsPushout f g c.inl c.inr

--- 原说明 ---
A variant of `of_isColimit` that is more useful with `apply`.
-/
theorem of_isColimit' (w : CommSq f g inl inr) (h : Limits.IsColimit w.cocone) :
    IsPushout f g inl inr :=
  of_isColimit h

set_option backward.isDefEq.respectTransparency false in
/-- Variant of `of_isColimit` for an arbitrary cocone on a diagram `WalkingSpan ⥤ C`. -/
/-
**CategoryTheory.IsPushout.of_isColimit_cocone** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.IsPushout`。
形式化陈述：of_isColimit_cocone {D : WalkingSpan ⥤ C} {c : Cocone D} (hc : IsColimit c
) : IsPushout (D.map WalkingSpan.Hom.fst) (D.map WalkingSpan.Hom.snd) (c.ι.app .
left) (c.ι.app .right) where w
参数：hc : IsColimit c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.Cocone.w`：∀ {J : Type u₁} [inst : CategoryTheory.C
ategory.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃} C] 
  {F : CategoryTheor…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
Variant of `of_isColimit` for an arbitrary cocone on a diagram `WalkingSpan ⥤ C`
.
-/
lemma of_isColimit_cocone {D : WalkingSpan ⥤ C} {c : Cocone D} (hc : IsColimit c) :
    IsPushout (D.map WalkingSpan.Hom.fst) (D.map WalkingSpan.Hom.snd)
      (c.ι.app .left) (c.ι.app .right) where
  w := by simp_rw [Cocone.w]
  isColimit' := ⟨IsColimit.equivOfNatIsoOfIso _ _ _ (PushoutCocone.isoMk c) hc⟩
/-
**CategoryTheory.IsPushout.hasPushout** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.
IsPushout`。
形式化陈述：hasPushout (h : IsPushout f g inl inr) : HasPushout f g where exists_colim
it
参数：h : IsPushout f g inl inr。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hasPushout (h : IsPushout f g inl inr) : HasPushout f g where
  exists_colimit := ⟨⟨h.cocone, h.isColimit⟩⟩

/-- The pushout provided by `HasPushout f g` fits into an `IsPushout`. -/
/-
**CategoryTheory.IsPushout.of_hasPushout** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.IsPushout`。
形式化陈述：of_hasPushout (f : Z ⟶ X) (g : Z ⟶ Y) [HasPushout f g] : IsPushout f g (pu
shout.inl f g) (pushout.inr f g)
参数：f : Z ⟶ X；g : Z ⟶ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPushout.of_isColimit`：of_isColimit {c : PushoutCocone f
 g} (h : Limits.IsColimit c) : IsPushout f g c.inl c.inr

--- 原说明 ---
The pushout provided by `HasPushout f g` fits into an `IsPushout`.
-/
theorem of_hasPushout (f : Z ⟶ X) (g : Z ⟶ Y) [HasPushout f g] :
    IsPushout f g (pushout.inl f g) (pushout.inr f g) :=
  of_isColimit (colimit.isColimit (span f g))

section

variable (X Y)
variable {P' : C} {inl' : X ⟶ P'} {inr' : Y ⟶ P'}

/-- Any object at the bottom right of a pushout square is isomorphic to the object at the bottom
right of any other pushout square with the same span. -/
/-
**CategoryTheory.IsPushout.isoIsPushout** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.IsPushout`。
形式化陈述：isoIsPushout (h : IsPushout f g inl inr) (h' : IsPushout f g inl' inr') : 
P ≅ P'
参数：h : IsPushout f g inl inr；h' : IsPushout f g inl' inr'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any object at the bottom right of a pushout square is isomorphic to the object a
t the bottom
right of any other pushout square with the same span.
-/
noncomputable def isoIsPushout (h : IsPushout f g inl inr) (h' : IsPushout f g inl' inr') :
    P ≅ P' :=
  IsColimit.coconePointUniqueUpToIso h.isColimit h'.isColimit

@[reassoc (attr := simp)]
/-
**CategoryTheory.IsPushout.inl_isoIsPushout_hom** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.IsPushout`。
形式化陈述：inl_isoIsPushout_hom (h : IsPushout f g inl inr) (h' : IsPushout f g inl' 
inr') : inl ≫ (h.isoIsPushout _ _ h').hom = inl'
参数：h : IsPushout f g inl inr；h' : IsPushout f g inl' inr'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsColimit.comp_coconePointUniqueUpToIso_hom`：∀ {J 
: Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : C
ategoryTheory.Category.{v₃, u₃} C]   {F : CategoryTheor…
-/
theorem inl_isoIsPushout_hom (h : IsPushout f g inl inr) (h' : IsPushout f g inl' inr') :
    inl ≫ (h.isoIsPushout _ _ h').hom = inl' :=
  IsColimit.comp_coconePointUniqueUpToIso_hom h.isColimit h'.isColimit WalkingSpan.left

@[reassoc (attr := simp)]
/-
**CategoryTheory.IsPushout.inr_isoIsPushout_hom** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.IsPushout`。
形式化陈述：inr_isoIsPushout_hom (h : IsPushout f g inl inr) (h' : IsPushout f g inl' 
inr') : inr ≫ (h.isoIsPushout _ _ h').hom = inr'
参数：h : IsPushout f g inl inr；h' : IsPushout f g inl' inr'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsColimit.comp_coconePointUniqueUpToIso_hom`：∀ {J 
: Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : C
ategoryTheory.Category.{v₃, u₃} C]   {F : CategoryTheor…
-/
theorem inr_isoIsPushout_hom (h : IsPushout f g inl inr) (h' : IsPushout f g inl' inr') :
    inr ≫ (h.isoIsPushout _ _ h').hom = inr' :=
  IsColimit.comp_coconePointUniqueUpToIso_hom h.isColimit h'.isColimit WalkingSpan.right

@[reassoc (attr := simp)]
/-
**CategoryTheory.IsPushout.inl_isoIsPushout_inv** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.IsPushout`。
形式化陈述：inl_isoIsPushout_inv (h : IsPushout f g inl inr) (h' : IsPushout f g inl' 
inr') : inl' ≫ (h.isoIsPushout _ _ h').inv = inl
参数：h : IsPushout f g inl inr；h' : IsPushout f g inl' inr'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsPushout.inl_isoIsPushout_hom`：inl_isoIsPushout_hom (h :
 IsPushout f g inl inr) (h' : IsPushout f g inl' inr') : inl ≫ (h.isoIsPushout _
 _ h').hom = inl'
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inl_isoIsPushout_inv (h : IsPushout f g inl inr) (h' : IsPushout f g inl' inr') :
    inl' ≫ (h.isoIsPushout _ _ h').inv = inl := by
  simp only [Iso.comp_inv_eq, inl_isoIsPushout_hom]

@[reassoc (attr := simp)]
/-
**CategoryTheory.IsPushout.inr_isoIsPushout_inv** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.IsPushout`。
形式化陈述：inr_isoIsPushout_inv (h : IsPushout f g inl inr) (h' : IsPushout f g inl' 
inr') : inr' ≫ (h.isoIsPushout _ _ h').inv = inr
参数：h : IsPushout f g inl inr；h' : IsPushout f g inl' inr'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsPushout.inr_isoIsPushout_hom`：inr_isoIsPushout_hom (h :
 IsPushout f g inl inr) (h' : IsPushout f g inl' inr') : inr ≫ (h.isoIsPushout _
 _ h').hom = inr'
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inr_isoIsPushout_inv (h : IsPushout f g inl inr) (h' : IsPushout f g inl' inr') :
    inr' ≫ (h.isoIsPushout _ _ h').inv = inr := by
  simp only [Iso.comp_inv_eq, inr_isoIsPushout_hom]

end

/-- Any object at the top left of a pullback square is
isomorphic to the pullback provided by the `HasLimit` API. -/
/-
**CategoryTheory.IsPushout.isoPushout** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
IsPushout`。
形式化陈述：isoPushout (h : IsPushout f g inl inr) [HasPushout f g] : P ≅ pushout f g
参数：h : IsPushout f g inl inr。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any object at the top left of a pullback square is
isomorphic to the pullback provided by the `HasLimit` API.
-/
noncomputable def isoPushout (h : IsPushout f g inl inr) [HasPushout f g] : P ≅ pushout f g :=
  (colimit.isoColimitCocone ⟨_, h.isColimit⟩).symm

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.IsPushout.inl_isoPushout_inv** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.IsPushout`。
形式化陈述：inl_isoPushout_inv (h : IsPushout f g inl inr) [HasPushout f g] : pushout.
inl _ _ ≫ h.isoPushout.inv = inl
参数：h : IsPushout f g inl inr。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.CommSq.w`：∀ {C : Type u_1} [inst : CategoryTheory.Categor
y.{v_1, u_1} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z}   {i : Y ⟶ Z},
   CategoryTh…
· 使用定理 `CategoryTheory.IsPushout.toCommSq`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {Z X Y P : C} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P}   {in
r : Y ⟶ P}, CategoryThe…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.colimit.isoColimitCocone_ι_hom`：∀ {J : Type u₁} [i
nst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.
Category.{v, u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PushoutCocone.mk_ι_app`：∀ {C : Type u} [inst : Cat
egoryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} {W : C} (inl 
: Y ⟶ W)   (inr : Z ⟶ W) (eq : Cat…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inl_isoPushout_inv (h : IsPushout f g inl inr) [HasPushout f g] :
    pushout.inl _ _ ≫ h.isoPushout.inv = inl := by
  dsimp [isoPushout, cocone, CommSq.cocone]
  simp

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.IsPushout.inr_isoPushout_inv** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.IsPushout`。
形式化陈述：inr_isoPushout_inv (h : IsPushout f g inl inr) [HasPushout f g] : pushout.
inr _ _ ≫ h.isoPushout.inv = inr
参数：h : IsPushout f g inl inr。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.CommSq.w`：∀ {C : Type u_1} [inst : CategoryTheory.Categor
y.{v_1, u_1} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z}   {i : Y ⟶ Z},
   CategoryTh…
· 使用定理 `CategoryTheory.IsPushout.toCommSq`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {Z X Y P : C} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P}   {in
r : Y ⟶ P}, CategoryThe…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.colimit.isoColimitCocone_ι_hom`：∀ {J : Type u₁} [i
nst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.
Category.{v, u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PushoutCocone.mk_ι_app`：∀ {C : Type u} [inst : Cat
egoryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} {W : C} (inl 
: Y ⟶ W)   (inr : Z ⟶ W) (eq : Cat…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inr_isoPushout_inv (h : IsPushout f g inl inr) [HasPushout f g] :
    pushout.inr _ _ ≫ h.isoPushout.inv = inr := by
  dsimp [isoPushout, cocone, CommSq.cocone]
  simp

@[reassoc (attr := simp)]
/-
**CategoryTheory.IsPushout.inl_isoPushout_hom** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.IsPushout`。
形式化陈述：inl_isoPushout_hom (h : IsPushout f g inl inr) [HasPushout f g] : inl ≫ h.
isoPushout.hom = pushout.inl _ _
参数：h : IsPushout f g inl inr。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsPushout.inl_isoPushout_inv`：inl_isoPushout_inv (h : IsP
ushout f g inl inr) [HasPushout f g] : pushout.inl _ _ ≫ h.isoPushout.inv = inl
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inl_isoPushout_hom (h : IsPushout f g inl inr) [HasPushout f g] :
    inl ≫ h.isoPushout.hom = pushout.inl _ _ := by simp [← Iso.eq_comp_inv]

@[reassoc (attr := simp)]
/-
**CategoryTheory.IsPushout.inr_isoPushout_hom** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.IsPushout`。
形式化陈述：inr_isoPushout_hom (h : IsPushout f g inl inr) [HasPushout f g] : inr ≫ h.
isoPushout.hom = pushout.inr _ _
参数：h : IsPushout f g inl inr。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsPushout.inr_isoPushout_inv`：inr_isoPushout_inv (h : IsP
ushout f g inl inr) [HasPushout f g] : pushout.inr _ _ ≫ h.isoPushout.inv = inr
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inr_isoPushout_hom (h : IsPushout f g inl inr) [HasPushout f g] :
    inr ≫ h.isoPushout.hom = pushout.inr _ _ := by simp [← Iso.eq_comp_inv]

end IsPushout

namespace IsPullback
variable {P X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}

/-
**CategoryTheory.IsPullback.flip** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.IsPul
lback`。
形式化陈述：flip (h : IsPullback fst snd f g) : IsPullback snd fst g f
参数：h : IsPullback fst snd f g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPullback.of_isLimit`：of_isLimit {c : PullbackCone f g} 
(h : Limits.IsLimit c) : IsPullback c.fst c.snd f g
-/
theorem flip (h : IsPullback fst snd f g) : IsPullback snd fst g f :=
  of_isLimit (PullbackCone.flipIsLimit h.isLimit)
/-
**CategoryTheory.IsPullback.flip_iff** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.I
sPullback`。
形式化陈述：flip_iff : IsPullback fst snd f g ↔ IsPullback snd fst g f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPullback.flip`：flip (h : IsPullback fst snd f g) : IsPu
llback snd fst g f
-/
theorem flip_iff : IsPullback fst snd f g ↔ IsPullback snd fst g f :=
  ⟨flip, flip⟩
/-
**CategoryTheory.IsPullback.op** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.IsPullb
ack`。
形式化陈述：op (h : IsPullback fst snd f g) : IsPushout g.op f.op snd.op fst.op
参数：h : IsPullback fst snd f g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPushout.of_isColimit`：of_isColimit {c : PushoutCocone f
 g} (h : Limits.IsColimit c) : IsPushout f g c.inl c.inr
· 使用定理 `CategoryTheory.CommSq.op`：op (p : CommSq f g h i) : CommSq i.op h.op g.o
p f.op
· 使用定理 `CategoryTheory.CommSq.flip`：flip (p : CommSq f g h i) : CommSq g f i h
· 使用定理 `CategoryTheory.IsPullback.toCommSq`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {P X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z}   
{g : Y ⟶ Z}, CategoryThe…
· 使用定理 `CategoryTheory.IsPullback.flip`：flip (h : IsPullback fst snd f g) : IsPu
llback snd fst g f
-/
theorem op (h : IsPullback fst snd f g) : IsPushout g.op f.op snd.op fst.op :=
  IsPushout.of_isColimit
    (IsColimit.ofIsoColimit (Limits.PullbackCone.isLimitEquivIsColimitOp h.flip.cone h.flip.isLimit)
      h.toCommSq.flip.coneOp)
/-
**CategoryTheory.IsPullback.unop** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.IsPul
lback`。
形式化陈述：unop {P X Y Z : Cᵒᵖ} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (
h : IsPullback fst snd f g) : IsPushout g.unop f.unop snd.unop fst.unop
参数：h : IsPullback fst snd f g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPushout.of_isColimit`：of_isColimit {c : PushoutCocone f
 g} (h : Limits.IsColimit c) : IsPushout f g c.inl c.inr
· 使用定理 `CategoryTheory.CommSq.unop`：unop {W X Y Z : Cᵒᵖ} {f : W ⟶ X} {g : W ⟶ Y}
 {h : X ⟶ Z} {i : Y ⟶ Z} (p : CommSq f g h i) : CommSq i.unop h.unop g.unop f.un
op
· 使用定理 `CategoryTheory.CommSq.flip`：flip (p : CommSq f g h i) : CommSq g f i h
· 使用定理 `CategoryTheory.IsPullback.toCommSq`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {P X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z}   
{g : Y ⟶ Z}, CategoryThe…
· 使用定理 `CategoryTheory.IsPullback.flip`：flip (h : IsPullback fst snd f g) : IsPu
llback snd fst g f
-/
theorem unop {P X Y Z : Cᵒᵖ} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback fst snd f g) : IsPushout g.unop f.unop snd.unop fst.unop :=
  IsPushout.of_isColimit
    (IsColimit.ofIsoColimit
      (Limits.PullbackCone.isLimitEquivIsColimitUnop h.flip.cone h.flip.isLimit)
      h.toCommSq.flip.coneUnop)

end IsPullback

namespace IsPushout
variable {Z X Y P : C} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P} {inr : Y ⟶ P}

/-
**CategoryTheory.IsPushout.flip** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.IsPush
out`。
形式化陈述：flip (h : IsPushout f g inl inr) : IsPushout g f inr inl
参数：h : IsPushout f g inl inr。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPushout.of_isColimit`：of_isColimit {c : PushoutCocone f
 g} (h : Limits.IsColimit c) : IsPushout f g c.inl c.inr
-/
theorem flip (h : IsPushout f g inl inr) : IsPushout g f inr inl :=
  of_isColimit (PushoutCocone.flipIsColimit h.isColimit)
/-
**CategoryTheory.IsPushout.flip_iff** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Is
Pushout`。
形式化陈述：flip_iff : IsPushout f g inl inr ↔ IsPushout g f inr inl
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPushout.flip`：flip (h : IsPushout f g inl inr) : IsPush
out g f inr inl
-/
theorem flip_iff : IsPushout f g inl inr ↔ IsPushout g f inr inl :=
  ⟨flip, flip⟩
/-
**CategoryTheory.IsPushout.op** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.IsPushou
t`。
形式化陈述：op (h : IsPushout f g inl inr) : IsPullback inr.op inl.op g.op f.op
参数：h : IsPushout f g inl inr。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPullback.of_isLimit`：of_isLimit {c : PullbackCone f g} 
(h : Limits.IsLimit c) : IsPullback c.fst c.snd f g
· 使用定理 `CategoryTheory.CommSq.op`：op (p : CommSq f g h i) : CommSq i.op h.op g.o
p f.op
· 使用定理 `CategoryTheory.CommSq.flip`：flip (p : CommSq f g h i) : CommSq g f i h
· 使用定理 `CategoryTheory.IsPushout.toCommSq`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {Z X Y P : C} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P}   {in
r : Y ⟶ P}, CategoryThe…
· 使用定理 `CategoryTheory.IsPushout.flip`：flip (h : IsPushout f g inl inr) : IsPush
out g f inr inl
-/
theorem op (h : IsPushout f g inl inr) : IsPullback inr.op inl.op g.op f.op :=
  IsPullback.of_isLimit
    (IsLimit.ofIsoLimit
      (Limits.PushoutCocone.isColimitEquivIsLimitOp h.flip.cocone h.flip.isColimit)
      h.toCommSq.flip.coconeOp)
/-
**CategoryTheory.IsPushout.unop** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.IsPush
out`。
形式化陈述：unop {Z X Y P : Cᵒᵖ} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P} {inr : Y ⟶ P} (
h : IsPushout f g inl inr) : IsPullback inr.unop inl.unop g.unop f.unop
参数：h : IsPushout f g inl inr。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPullback.of_isLimit`：of_isLimit {c : PullbackCone f g} 
(h : Limits.IsLimit c) : IsPullback c.fst c.snd f g
· 使用定理 `CategoryTheory.CommSq.unop`：unop {W X Y Z : Cᵒᵖ} {f : W ⟶ X} {g : W ⟶ Y}
 {h : X ⟶ Z} {i : Y ⟶ Z} (p : CommSq f g h i) : CommSq i.unop h.unop g.unop f.un
op
· 使用定理 `CategoryTheory.CommSq.flip`：flip (p : CommSq f g h i) : CommSq g f i h
· 使用定理 `CategoryTheory.IsPushout.toCommSq`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {Z X Y P : C} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P}   {in
r : Y ⟶ P}, CategoryThe…
· 使用定理 `CategoryTheory.IsPushout.flip`：flip (h : IsPushout f g inl inr) : IsPush
out g f inr inl
-/
theorem unop {Z X Y P : Cᵒᵖ} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P} {inr : Y ⟶ P}
    (h : IsPushout f g inl inr) : IsPullback inr.unop inl.unop g.unop f.unop :=
  IsPullback.of_isLimit
    (IsLimit.ofIsoLimit
      (Limits.PushoutCocone.isColimitEquivIsLimitUnop h.flip.cocone h.flip.isColimit)
      h.toCommSq.flip.coconeUnop)

end IsPushout

/-
**CategoryTheory.IsPullback.op_iff** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.IsP
ullback`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X Y Z P : C} 
{f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P}   {inr : Y ⟶ P}, CategoryTheory.IsPullback
 inr.op inl.op g.op f.op ↔ CategoryTheory.IsPushout f g inl inr
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPullback.unop`：unop {P X Y Z : Cᵒᵖ} {fst : P ⟶ X} {snd 
: P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback fst snd f g) : IsPushout g.unop
 f.unop snd.unop fst…
· 使用定理 `CategoryTheory.IsPushout.op`：op (h : IsPushout f g inl inr) : IsPullback
 inr.op inl.op g.op f.op
-/
lemma IsPullback.op_iff {X Y Z P : C} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P} {inr : Y ⟶ P} :
    IsPullback inr.op inl.op g.op f.op ↔ IsPushout f g inl inr :=
  ⟨fun h ↦ h.unop, fun h ↦ h.op⟩
/-
**CategoryTheory.IsPullback.unop_iff** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.I
sPullback`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X Y Z P : Cᵒᵖ
} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P}   {inr : Y ⟶ P}, CategoryTheory.IsPullba
ck inr.unop inl.unop g.unop f.unop ↔ CategoryTheory.IsPushout f g inl inr
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPullback.op`：op (h : IsPullback fst snd f g) : IsPushou
t g.op f.op snd.op fst.op
· 使用定理 `CategoryTheory.IsPushout.unop`：unop {Z X Y P : Cᵒᵖ} {f : Z ⟶ X} {g : Z ⟶
 Y} {inl : X ⟶ P} {inr : Y ⟶ P} (h : IsPushout f g inl inr) : IsPullback inr.uno
p inl.unop g.unop f…
-/
lemma IsPullback.unop_iff {X Y Z P : Cᵒᵖ} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P} {inr : Y ⟶ P} :
    IsPullback inr.unop inl.unop g.unop f.unop ↔ IsPushout f g inl inr :=
  ⟨fun h ↦ h.op, fun h ↦ h.unop⟩
/-
**CategoryTheory.IsPushout.op_iff** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.IsPu
shout`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {P X Y Z : C} 
{fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z}   {g : Y ⟶ Z}, CategoryTheory.IsPushout 
g.op f.op snd.op fst.op ↔ CategoryTheory.IsPullback fst snd f g
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPushout.unop`：unop {Z X Y P : Cᵒᵖ} {f : Z ⟶ X} {g : Z ⟶
 Y} {inl : X ⟶ P} {inr : Y ⟶ P} (h : IsPushout f g inl inr) : IsPullback inr.uno
p inl.unop g.unop f…
· 使用定理 `CategoryTheory.IsPullback.op`：op (h : IsPullback fst snd f g) : IsPushou
t g.op f.op snd.op fst.op
-/
lemma IsPushout.op_iff {P X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} :
    IsPushout g.op f.op snd.op fst.op ↔ IsPullback fst snd f g :=
  ⟨fun h ↦ h.unop, fun h ↦ h.op⟩
/-
**CategoryTheory.IsPushout.unop_iff** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Is
Pushout`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {P X Y Z : Cᵒᵖ
} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z}   {g : Y ⟶ Z}, CategoryTheory.IsPushou
t g.unop f.unop snd.unop fst.unop ↔ CategoryTheory.IsPullback fst snd f g
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPushout.op`：op (h : IsPushout f g inl inr) : IsPullback
 inr.op inl.op g.op f.op
· 使用定理 `CategoryTheory.IsPullback.unop`：unop {P X Y Z : Cᵒᵖ} {fst : P ⟶ X} {snd 
: P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback fst snd f g) : IsPushout g.unop
 f.unop snd.unop fst…
-/
lemma IsPushout.unop_iff {P X Y Z : Cᵒᵖ} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} :
    IsPushout g.unop f.unop snd.unop fst.unop ↔ IsPullback fst snd f g :=
  ⟨fun h ↦ h.op, fun h ↦ h.unop⟩

end CategoryTheory

