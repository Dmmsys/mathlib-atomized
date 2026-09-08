/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Sites.Hypercover.Zero

/-!
# Defining precoverages via pre-`0`-hypercovers

A precoverage is a condition on all presieves. In some applications, it is practical
to instead define a condition on all pre-`0`-hypercovers. Such a condition
for every object is a pre-`0`-hypercover family if these conditions are
invariant under deduplication.
-/

@[expose] public section

universe w' w v u

namespace CategoryTheory
open Limits

variable {C : Type u} [Category.{v} C]

variable (C) in
/--
A pre-`0`-hypercover family on `C` is a property on the category of pre-`0`-hypercovers
for every `X : C` that is invariant under deduplication.
The data of a pre-`0`-hypercover family is the same as the data of a precoverage
(see: `Precoverage.equivPreZeroHypercoverFamily`).
-/
@[ext]
/-
**CategoryTheory.PreZeroHypercoverFamily** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTh
eory`。
形式化陈述：(C : Type u) → [CategoryTheory.Category.{v, u} C] → Type (max (u + 1) (v +
 1))
参数：u + 1；v + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A pre-`0`-hypercover family on `C` is a property on the category of pre-`0`-hype
rcovers
for every `X : C` that is invariant under deduplication.
The data of a pre-`0`-hypercover family is the same as the data of a precoverage
(see: `Precoverage.equivPreZeroHypercoverFamily`).
-/
structure PreZeroHypercoverFamily where
  /-- The condition on pre-`0`-hypercovers for every object. -/
  property ⦃X : C⦄ : ObjectProperty (PreZeroHypercover.{max u v} X)
  iff_shrink {X : C} {E : PreZeroHypercover.{max u v} X} : property E ↔ property E.shrink
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeFun (PreZeroHypercoverFamily C)
    fun _ ↦ ⦃X : C⦄ → (E : PreZeroHypercover.{max u v} X) → Prop where
  coe P := P.property

/-- The induced condition on presieves in `C`, given by a pre-`0`-hypercover family. -/
/-
**CategoryTheory.PreZeroHypercoverFamily.presieve** 是 Mathlib 中的一个归纳类型，位于命名空间 `C
ategoryTheory.PreZeroHypercoverFamily`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     CategoryT
heory.PreZeroHypercoverFamily C → {X : C} → CategoryTheory.Presieve X → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The induced condition on presieves in `C`, given by a pre-`0`-hypercover family.
-/
inductive PreZeroHypercoverFamily.presieve (P : PreZeroHypercoverFamily C) {X : C} :
    Presieve X → Prop where
  | mk (E : PreZeroHypercover.{max u v} X) : P E → presieve P E.presieve₀

/-- The associated precoverage to a pre-`0`-hypercover family. -/
/-
**CategoryTheory.PreZeroHypercoverFamily.precoverage** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.PreZeroHypercoverFamily`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] → CategoryTheor
y.PreZeroHypercoverFamily C → CategoryTheory.Precoverage C
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The associated precoverage to a pre-`0`-hypercover family.
-/
def PreZeroHypercoverFamily.precoverage (P : PreZeroHypercoverFamily C) :
    Precoverage C where
  coverings _ := {R | P.presieve R}
/-
**CategoryTheory.PreZeroHypercoverFamily.mem_precoverage_iff** 是 Mathlib 中的一个定理，
位于命名空间 `CategoryTheory.PreZeroHypercoverFamily`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheo
ry.PreZeroHypercoverFamily C} {X : C}   {R : CategoryTheory.Presieve X}, R ∈ P.p
recoverage.coverings X ↔ ∃ E, P.property E ∧ R = E.presieve₀
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma PreZeroHypercoverFamily.mem_precoverage_iff {P : PreZeroHypercoverFamily C} {X : C}
    {R : Presieve X} :
    R ∈ P.precoverage X ↔ ∃ (E : PreZeroHypercover.{max u v} X), P E ∧ R = E.presieve₀ :=
  ⟨fun ⟨E, hE⟩ ↦ ⟨E, hE, rfl⟩, fun ⟨_, hE, h⟩ ↦ h ▸ ⟨_, hE⟩⟩

@[simp]
/-
**CategoryTheory.PreZeroHypercover.presieve** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma PreZeroHypercover.presieve₀_mem_precoverage_iff {P : PreZeroHypercoverFamily C} {X : C}
    {E : PreZeroHypercover.{max u v} X} :
    E.presieve₀ ∈ P.precoverage X ↔ P E := by
  refine ⟨fun h ↦ ?_, fun h ↦ .mk _ h⟩
  rw [PreZeroHypercoverFamily.mem_precoverage_iff] at h
  obtain ⟨F, h, heq⟩ := h
  rw [P.iff_shrink] at h ⊢
  rwa [PreZeroHypercover.shrink_eq_shrink_of_presieve₀_eq_presieve₀ heq]

/-- The associated pre-`0`-hypercover family to a precoverage. -/
@[simps]
/-
**CategoryTheory.Precoverage.preZeroHypercoverFamily** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Precoverage`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] → CategoryTheor
y.Precoverage C → CategoryTheory.PreZeroHypercoverFamily C
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The associated pre-`0`-hypercover family to a precoverage.
-/
def Precoverage.preZeroHypercoverFamily (K : Precoverage C) :
    PreZeroHypercoverFamily C where
  property X E := E.presieve₀ ∈ K X
  iff_shrink {X} E := by simp

variable (C) in
/-- Giving a precoverage on a category is the same as giving a predicate
on every pre-`0`-hypercover that is stable under deduplication. -/
/-
**CategoryTheory.Precoverage.equivPreZeroHypercoverFamily** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.Precoverage`。
形式化陈述：(C : Type u) →   [inst : CategoryTheory.Category.{v, u} C] → CategoryTheor
y.Precoverage C ≃ CategoryTheory.PreZeroHypercoverFamily C
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Giving a precoverage on a category is the same as giving a predicate
on every pre-`0`-hypercover that is stable under deduplication.
-/
def Precoverage.equivPreZeroHypercoverFamily :
    Precoverage C ≃ PreZeroHypercoverFamily C where
  toFun K := K.preZeroHypercoverFamily
  invFun P := P.precoverage
  left_inv K := by
    ext X R
    obtain ⟨E, rfl⟩ := R.exists_eq_preZeroHypercover
    simp
  right_inv P := by cat_disch
/-
**CategoryTheory.Precoverage.HasIsos.of_preZeroHypercoverFamily** 是 Mathlib 中的一个
定理，位于命名空间 `CategoryTheory.Precoverage.HasIsos`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheo
ry.PreZeroHypercoverFamily C},   (∀ ⦃X Y : C⦄ (f : X ⟶ Y) [CategoryTheory.IsIso 
f], P.property (CategoryTheory.PreZeroHypercover.singleton f)) →     P.precovera
ge.HasIsos
参数：∀ ⦃X Y : C⦄ (f : X ⟶ Y) [CategoryTheory.IsIso f], P.property (CategoryTheory.
PreZeroHypercover.singleton f)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.PreZeroHypercover.presieve₀_singleton`：presieve₀_singleto
n (f : S ⟶ T) : (singleton f).presieve₀ = .singleton f
-/
lemma Precoverage.HasIsos.of_preZeroHypercoverFamily {P : PreZeroHypercoverFamily C}
    (h : ∀ ⦃X Y : C⦄ (f : X ⟶ Y) [IsIso f], P (.singleton f)) :
    P.precoverage.HasIsos where
  mem_coverings_of_isIso {S T} f hf := by
    rw [← PreZeroHypercover.presieve₀_singleton.{_, _, max u v}]
    refine .mk _ (h _)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Precoverage.IsStableUnderBaseChange.of_preZeroHypercoverFamily_
of_isClosedUnderIsomorphisms** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Precovera
ge.IsStableUnderBaseChange`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheo
ry.PreZeroHypercoverFamily C},   (∀ {X : C}, P.property.IsClosedUnderIsomorphism
s) →     (∀ {X Y : C} (f : X ⟶ Y) (E : CategoryTheory.PreZeroHypercover Y)      
   [inst_1 : ∀ (i : E.I₀), CategoryTheory.Limits.HasPullback f (E.f i)],        
 P.property E → P.property (CategoryTheory.PreZeroHypercover.pullback₁ f E)) →  
     P.precoverage.IsStableUnderBaseChange
参数：∀ {X : C}, P.property.IsClosedUnderIsomorphisms；∀ {X Y : C} (f : X ⟶ Y) (E : 
CategoryTheory.PreZeroHypercover Y)         [inst_1 : ∀ (i : E.I₀), CategoryTheo
ry.Limits.HasPullback f (E.f i)],         P.property E → P.property (CategoryThe
ory.PreZeroHypercover.pullback₁ f E)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.IsPullback.hasPullback`：hasPullback (h : IsPullback fst s
nd f g) : HasPullback f g where exists_limit
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsPullback.isoPullback_hom_fst`：isoPullback_hom_fst (h : 
IsPullback fst snd f g) [HasPullback f g] : h.isoPullback.hom ≫ pullback.fst _ _
 = fst
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.PreZeroHypercover.presieve₀_mem_precoverage_iff`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.PreZeroHype
rcoverFamily C} {X : C}   {E : CategoryTheory.PreZer…
· 使用引理 `CategoryTheory.ObjectProperty.prop_iff_of_iso`：prop_iff_of_iso [IsClosed
UnderIsomorphisms P] {X Y : C} (e : X ≅ Y) : P X ↔ P Y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma Precoverage.IsStableUnderBaseChange.of_preZeroHypercoverFamily_of_isClosedUnderIsomorphisms
    {P : PreZeroHypercoverFamily C}
    (h₁ : ∀ {X : C}, (P (X := X)).IsClosedUnderIsomorphisms)
    (h₂ : ∀ {X Y : C} (f : X ⟶ Y) (E : PreZeroHypercover.{max u v} Y)
      [∀ (i : E.I₀), HasPullback f (E.f i)], P E → P (E.pullback₁ f)) :
    Precoverage.IsStableUnderBaseChange P.precoverage where
  mem_coverings_of_isPullback {ι} S X f hf Y g Z p₁ p₂ h := by
    let E : PreZeroHypercover S := ⟨ι, X, f⟩
    have (i : E.I₀) : HasPullback g (E.f i) := (h i).hasPullback
    let F : PreZeroHypercover Y := ⟨_, _, p₁⟩
    let e : F ≅ E.pullback₁ g :=
      PreZeroHypercover.isoMk (Equiv.refl _) (fun i ↦ (h i).isoPullback)
    change F.presieve₀ ∈ _
    rw [F.presieve₀_mem_precoverage_iff, (P (X := Y)).prop_iff_of_iso e]
    refine h₂ _ _ ?_
    rwa [← E.presieve₀_mem_precoverage_iff]
/-
**CategoryTheory.Precoverage.IsStableUnderComposition.of_preZeroHypercoverFamily
** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Precoverage.IsStableUnderComposition`
。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheo
ry.PreZeroHypercoverFamily C},   (∀ {X : C} (E : CategoryTheory.PreZeroHypercove
r X) (F : (i : E.I₀) → CategoryTheory.PreZeroHypercover (E.X i)),       P.proper
ty E → (∀ (i : E.I₀), P.property (F i)) → P.property (E.bind F)) →     P.precove
rage.IsStableUnderComposition
参数：∀ {X : C} (E : CategoryTheory.PreZeroHypercover X) (F : (i : E.I₀) → Category
Theory.PreZeroHypercover (E.X i)),       P.property E → (∀ (i : E.I₀), P.propert
y (F i)) → P.property (E.bind F)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.PreZeroHypercover.presieve₀_mem_precoverage_iff`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.PreZeroHype
rcoverFamily C} {X : C}   {E : CategoryTheory.PreZer…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma Precoverage.IsStableUnderComposition.of_preZeroHypercoverFamily
    {P : PreZeroHypercoverFamily C}
    (h : ∀ {X : C} (E : PreZeroHypercover.{max u v} X)
      (F : ∀ i, PreZeroHypercover.{max u v} (E.X i)),
      P E → (∀ i, P (F i)) → P (E.bind F)) :
    Precoverage.IsStableUnderComposition P.precoverage where
  comp_mem_coverings {ι} S X f hf σ Y g hg := by
    let E : PreZeroHypercover S := ⟨_, _, f⟩
    let F (i : ι) : PreZeroHypercover (E.X i) := ⟨_, _, g i⟩
    refine (E.bind F).presieve₀_mem_precoverage_iff.mpr (h _ _ ?_ fun i ↦ ?_)
    · rwa [← E.presieve₀_mem_precoverage_iff]
    · rw [← (F i).presieve₀_mem_precoverage_iff]
      exact hg i
/-
**CategoryTheory.Precoverage.IsStableUnderSup.of_preZeroHypercoverFamily** 是 Mat
hlib 中的一个定理，位于命名空间 `CategoryTheory.Precoverage.IsStableUnderSup`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheo
ry.PreZeroHypercoverFamily C},   (∀ ⦃X : C⦄ ⦃E F : CategoryTheory.PreZeroHyperco
ver X⦄, P.property E → P.property F → P.property (E.sum F)) →     P.precoverage.
IsStableUnderSup
参数：∀ ⦃X : C⦄ ⦃E F : CategoryTheory.PreZeroHypercover X⦄, P.property E → P.proper
ty F → P.property (E.sum F)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Presieve.exists_eq_preZeroHypercover`：∀ {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C] {S : C} (R : CategoryTheory.Presieve S), ∃
 E, R = E.presieve₀
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.PreZeroHypercover.presieve₀_sum`：presieve₀_sum : (E.sum F
).presieve₀ = E.presieve₀ ⊔ F.presieve₀
· 使用定理 `CategoryTheory.PreZeroHypercover.presieve₀_mem_precoverage_iff`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.PreZeroHype
rcoverFamily C} {X : C}   {E : CategoryTheory.PreZer…
-/
lemma Precoverage.IsStableUnderSup.of_preZeroHypercoverFamily
    {P : PreZeroHypercoverFamily C}
    (h : ∀ ⦃X : C⦄ ⦃E F : PreZeroHypercover.{max u v} X⦄,
      P E → P F → P (E.sum F)) :
    P.precoverage.IsStableUnderSup where
  sup_mem_coverings {X} R S hR hS := by
    obtain ⟨E, rfl⟩ := R.exists_eq_preZeroHypercover
    obtain ⟨F, rfl⟩ := S.exists_eq_preZeroHypercover
    rw [← PreZeroHypercover.presieve₀_sum]
    rw [PreZeroHypercover.presieve₀_mem_precoverage_iff] at hR hS ⊢
    exact h hR hS

end CategoryTheory

