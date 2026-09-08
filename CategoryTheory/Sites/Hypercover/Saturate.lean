/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Sites.Hypercover.Homotopy
public import Mathlib.CategoryTheory.Sites.Hypercover.SheafOfTypes
public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal

/-!
# Saturation of a `0`-hypercover

Given a `0`-hypercover `E`, we define a `1`-hypercover `E.saturate`
-/

@[expose] public section

namespace CategoryTheory.PreZeroHypercover

variable {C : Type*} [Category* C] {A : Type*} [Category* A]

open Limits

/-- A relation on a pre-`0`-hypercover is a commutative diagram
```
obj ----> E.X i
 |         |
 |         |
 v         v
E.X j ---> S
```
-/
/-
**CategoryTheory.PreZeroHypercover.Relation** 是 Mathlib 中的一个归纳类型，位于命名空间 `Categor
yTheory.PreZeroHypercover`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     {S 
: C} → (E : CategoryTheory.PreZeroHypercover S) → E.I₀ → E.I₀ → Type (max u_1 v_
1)
参数：E : CategoryTheory.PreZeroHypercover S；max u_1 v_1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A relation on a pre-`0`-hypercover is a commutative diagram
```
obj ----> E.X i
 |         |
 |         |
 v         v
E.X j ---> S
```
-/
structure Relation {S : C} (E : PreZeroHypercover S) (i j : E.I₀) where
  /-- The object. -/
  obj : C
  /-- The first projection. -/
  fst : obj ⟶ E.X i
  /-- The second projection. -/
  snd : obj ⟶ E.X j
  w : fst ≫ E.f i = snd ≫ E.f j

/-- The maximal pre-`1`-hypercover containing `E`, where the `1`-components are all relations
on `E`. -/
@[simps toPreZeroHypercover I₁ Y p₁ p₂]
/-
**CategoryTheory.PreZeroHypercover.saturate** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.PreZeroHypercover`。
形式化陈述：saturate {S : C} (E : PreZeroHypercover S) : PreOneHypercover S where __
参数：E : PreZeroHypercover S。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.PreZeroHypercover.Relation.w`：∀ {C : Type u_1} [inst : Ca
tegoryTheory.Category.{v_1, u_1} C] {S : C} {E : CategoryTheory.PreZeroHypercove
r S}   {i j : E.I₀} (self : E.Rel…

--- 原说明 ---
The maximal pre-`1`-hypercover containing `E`, where the `1`-components are all 
relations
on `E`.
-/
def saturate {S : C} (E : PreZeroHypercover S) : PreOneHypercover S where
  __ := E
  I₁ := E.Relation
  Y _ _ r := r.obj
  p₁ _ _ r := r.fst
  p₂ _ _ r := r.snd
  w _ _ r := r.w

/-- For a presheaf of types, sections over the multifork associated to `E.saturate` are equivalent
to compatible families. -/
@[simps]
/-
**CategoryTheory.PreZeroHypercover.sectionsSaturateEquiv** 是 Mathlib 中的一个定义，位于命名
空间 `CategoryTheory.PreZeroHypercover`。
形式化陈述：sectionsSaturateEquiv {S : C} (E : PreZeroHypercover S) (F : Cᵒᵖ ⥤ Type*) 
: (E.saturate.multicospanIndex F).sections ≃ Subtype (Presieve.Arrows.Compatible
 F E.f) where toFun s
参数：E : PreZeroHypercover S；F : Cᵒᵖ ⥤ Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For a presheaf of types, sections over the multifork associated to `E.saturate` 
are equivalent
to compatible families.
-/
def sectionsSaturateEquiv {S : C} (E : PreZeroHypercover S) (F : Cᵒᵖ ⥤ Type*) :
    (E.saturate.multicospanIndex F).sections ≃ Subtype (Presieve.Arrows.Compatible F E.f) where
  toFun s := ⟨s.val, fun i j _ _ _ hgij ↦ s.property ⟨(i, j), ⟨_, _, _, hgij⟩⟩⟩
  invFun s := ⟨s.val, fun r ↦ s.property _ _ _ _ _ r.snd.w⟩
  left_inv _ := rfl
  right_inv _ := rfl
/-
**CategoryTheory.PreZeroHypercover.isLimit_saturate_type_iff** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.PreZeroHypercover`。
形式化陈述：isLimit_saturate_type_iff {S : C} (E : PreZeroHypercover S) (F : Cᵒᵖ ⥤ Typ
e*) : Nonempty (IsLimit <| E.saturate.multifork F) ↔ E.presieve₀.IsSheafFor F
参数：E : PreZeroHypercover S；F : Cᵒᵖ ⥤ Type*。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Limits.Multifork.isLimit_types_iff`：isLimit_types_iff : N
onempty (IsLimit c) ↔ Function.Bijective c.toSections
· 使用定理 `CategoryTheory.Presieve.isSheafFor_ofArrows_iff_bijective_toCompabible`：
isSheafFor_ofArrows_iff_bijective_toCompabible : IsSheafFor P (ofArrows X π) ↔ F
unction.Bijective (Arrows.toCompatible P π)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Bijective.of_comp_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {γ : So
rt u_3} {f : α → β},   Function.Bijective f → ∀ (g : γ → α), Function.Bijective 
(f ∘ g) ↔ Function.Bi…
· 使用定理 `Equiv.bijective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Bijec
tive ⇑e
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isLimit_saturate_type_iff {S : C} (E : PreZeroHypercover S) (F : Cᵒᵖ ⥤ Type*) :
    Nonempty (IsLimit <| E.saturate.multifork F) ↔ E.presieve₀.IsSheafFor F := by
  rw [Multifork.isLimit_types_iff, Presieve.isSheafFor_ofArrows_iff_bijective_toCompabible,
    ← Function.Bijective.of_comp_iff' (E.sectionsSaturateEquiv F).symm.bijective]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- If `E` has pairwise pullbacks, this is the canonical map from the minimal `1`-hypercover
to the saturation. -/
@[simps]
noncomputable
/-
**CategoryTheory.PreZeroHypercover.toSaturateOfHasPullbacks** 是 Mathlib 中的一个定义，位
于命名空间 `CategoryTheory.PreZeroHypercover`。
形式化陈述：toSaturateOfHasPullbacks {S : C} (E : PreZeroHypercover S) [E.HasPullbacks
] : E.toPreOneHypercover ⟶ E.saturate where s₀ i
参数：E : PreZeroHypercover S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def toSaturateOfHasPullbacks {S : C} (E : PreZeroHypercover S) [E.HasPullbacks] :
    E.toPreOneHypercover ⟶ E.saturate where
  s₀ i := i
  h₀ i := 𝟙 _
  s₁ {i j} k := ⟨pullback (E.f i) (E.f j), _, _, pullback.condition⟩
  h₁ {i j} k := 𝟙 _

set_option backward.isDefEq.respectTransparency false in
/-- If `E` has pairwise pullbacks, this is the canonical map to the minimal `1`-hypercover
from the saturation. -/
@[simps]
noncomputable
/-
**CategoryTheory.PreZeroHypercover.fromSaturateOfHasPullbacks** 是 Mathlib 中的一个定义
，位于命名空间 `CategoryTheory.PreZeroHypercover`。
形式化陈述：fromSaturateOfHasPullbacks {S : C} (E : PreZeroHypercover S) [E.HasPullbac
ks] : E.saturate ⟶ E.toPreOneHypercover where s₀ i
参数：E : PreZeroHypercover S。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.PreZeroHypercover.Relation.w`：∀ {C : Type u_1} [inst : Ca
tegoryTheory.Category.{v_1, u_1} C] {S : C} {E : CategoryTheory.PreZeroHypercove
r S}   {i j : E.I₀} (self : E.Rel…
-/
def fromSaturateOfHasPullbacks {S : C} (E : PreZeroHypercover S)
    [E.HasPullbacks] : E.saturate ⟶ E.toPreOneHypercover where
  s₀ i := i
  h₀ i := 𝟙 _
  s₁ {i j} k := ⟨⟩
  h₁ {i j} k := pullback.lift k.fst k.snd k.w

variable {S : C} (E : PreZeroHypercover S) [E.HasPullbacks]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The identity of the minimal pre-`1`-hypercover when `E` has pairwise pullbacks
is homotopic to itself. -/
noncomputable
/-
**CategoryTheory.PreZeroHypercover.toPreOneHypercoverHomotopy** 是 Mathlib 中的一个定义
，位于命名空间 `CategoryTheory.PreZeroHypercover`。
形式化陈述：toPreOneHypercoverHomotopy {S : C} (E : PreZeroHypercover S) [E.HasPullbac
ks] : PreOneHypercover.Homotopy (.id E.toPreOneHypercover) (.id E.toPreOneHyperc
over) where H _
参数：E : PreZeroHypercover S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def toPreOneHypercoverHomotopy {S : C} (E : PreZeroHypercover S)
    [E.HasPullbacks] :
    PreOneHypercover.Homotopy (.id E.toPreOneHypercover) (.id E.toPreOneHypercover) where
  H _ := ⟨⟩
  a i := pullback.diagonal (E.f i)
  wl := by simp
  wr := by simp

variable {S : C} (E : PreZeroHypercover S) [E.HasPullbacks]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simp]
/-
**CategoryTheory.PreZeroHypercover.toSaturateOfHasPullbacks_fromSaturateOfHasPul
lbacks** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.PreZeroHypercover`。
形式化陈述：toSaturateOfHasPullbacks_fromSaturateOfHasPullbacks : E.toSaturateOfHasPul
lbacks.comp E.fromSaturateOfHasPullbacks = .id _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.PreOneHypercover.Hom.ext'`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {S : C} {E : CategoryTheory.PreOneHypercover S}   {F 
: CategoryTheory.PreOneHyperco…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `CategoryTheory.PreOneHypercover.congrIndexOneOfEq_refl`：congrIndexOneOfE
q_refl (i j : E.I₀) : E.congrIndexOneOfEq rfl rfl = Equiv.refl (E.I₁ i j)
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.pullback.lift_fst_snd`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)   [inst_1 : Ca
tegoryTheory.Limits.HasPullback f…
· 使用引理 `CategoryTheory.PreOneHypercover.congrIndexOneOfEqIso_refl`：congrIndexOne
OfEqIso_refl {i j : E.I₀} (k : E.I₁ i j) : E.congrIndexOneOfEqIso rfl rfl k = Is
o.refl _
-/
lemma toSaturateOfHasPullbacks_fromSaturateOfHasPullbacks :
    E.toSaturateOfHasPullbacks.comp E.fromSaturateOfHasPullbacks = .id _ := by
  refine PreOneHypercover.Hom.ext' rfl (by simp) (by simp) (by simp)

set_option backward.isDefEq.respectTransparency false in
/-- The composition `E.saturate ⟶ E.toPreOneHypercover ⟶ E.saturate` is homotopic to the
identity. -/
noncomputable
/-
**CategoryTheory.PreZeroHypercover.fromSaturateToSaturateHomotopy** 是 Mathlib 中的
一个定义，位于命名空间 `CategoryTheory.PreZeroHypercover`。
形式化陈述：fromSaturateToSaturateHomotopy : PreOneHypercover.Homotopy (E.fromSaturate
OfHasPullbacks.comp E.toSaturateOfHasPullbacks) (.id _) where H i
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def fromSaturateToSaturateHomotopy : PreOneHypercover.Homotopy
    (E.fromSaturateOfHasPullbacks.comp E.toSaturateOfHasPullbacks) (.id _) where
  H i := ⟨pullback (E.f i) (E.f i), pullback.fst _ _, pullback.snd _ _, pullback.condition⟩
  a i := pullback.diagonal (E.f i)
  wl i := by simp
  wr i := by simp

/-- If the pre-`0`-hypercover `E` has pairwise pullbacks, then the multifork associated to the
full saturated pre-`1`-hypercover is exact if and only if the minimal one given by taking
the pairwise pullbacks is exact. -/
noncomputable
/-
**CategoryTheory.PreZeroHypercover.isLimitSaturateEquivOfHasPullbacks** 是 Mathli
b 中的一个定义，位于命名空间 `CategoryTheory.PreZeroHypercover`。
形式化陈述：isLimitSaturateEquivOfHasPullbacks {S : C} (E : PreZeroHypercover S) [E.Ha
sPullbacks] (F : Cᵒᵖ ⥤ A) : IsLimit (E.saturate.multifork F) ≃ IsLimit (E.toPreO
neHypercover.multifork F)
参数：E : PreZeroHypercover S；F : Cᵒᵖ ⥤ A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def isLimitSaturateEquivOfHasPullbacks {S : C} (E : PreZeroHypercover S)
    [E.HasPullbacks] (F : Cᵒᵖ ⥤ A) :
    IsLimit (E.saturate.multifork F) ≃ IsLimit (E.toPreOneHypercover.multifork F) :=
  PreOneHypercover.Homotopy.isLimitMultiforkEquiv E.fromSaturateOfHasPullbacks
    E.toSaturateOfHasPullbacks E.fromSaturateToSaturateHomotopy
    (by
      rw [toSaturateOfHasPullbacks_fromSaturateOfHasPullbacks]
      exact E.toPreOneHypercoverHomotopy)

end CategoryTheory.PreZeroHypercover

