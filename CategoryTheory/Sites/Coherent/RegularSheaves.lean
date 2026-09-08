/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, Filippo A. E. Nuccio, Riccardo Brasca
-/
module

public import Mathlib.CategoryTheory.EffectiveEpi.Preserves
public import Mathlib.CategoryTheory.Limits.Final.ParallelPair
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import Mathlib.CategoryTheory.Sites.Canonical
public import Mathlib.CategoryTheory.Sites.Coherent.Basic
public import Mathlib.CategoryTheory.Sites.EffectiveEpimorphic
/-!

# Sheaves for the regular topology

This file characterises sheaves for the regular topology.

## Main results

* `equalizerCondition_iff_isSheaf`: In a preregular category with pullbacks, the sheaves for the
  regular topology are precisely the presheaves satisfying an equaliser condition with respect to
  effective epimorphisms.

* `isSheaf_of_projective`: In a preregular category in which every object is projective, every
  presheaf is a sheaf for the regular topology.
-/

@[expose] public section

namespace CategoryTheory

open Limits

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]

open Opposite Presieve CategoryTheory.Functor

/-- A presieve is *regular* if it consists of a single effective epimorphism. -/
/-
**CategoryTheory.Presieve.regular** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory.Pr
esieve`。
形式化陈述：{C : Type u_1} → [inst : CategoryTheory.Category.{v_1, u_1} C] → {X : C} →
 CategoryTheory.Presieve X → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A presieve is *regular* if it consists of a single effective epimorphism.
-/
class Presieve.regular {X : C} (R : Presieve X) : Prop where
  /-- `R` consists of a single epimorphism. -/
  single_epi : ∃ (Y : C) (f : Y ⟶ X), R = Presieve.ofArrows (fun (_ : Unit) ↦ Y)
    (fun (_ : Unit) ↦ f) ∧ EffectiveEpi f

namespace regularTopology

/-
**CategoryTheory.regularTopology.equalizerCondition_w** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.regularTopology`。
形式化陈述：equalizerCondition_w (P : Cᵒᵖ ⥤ D) {X B : C} {π : X ⟶ B} (c : PullbackCone
 π π) : P.map π.op ≫ P.map c.fst.op = P.map π.op ≫ P.map c.snd.op
参数：P : Cᵒᵖ ⥤ D；c : PullbackCone π π。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.PullbackCone.condition`：condition (t : PullbackCon
e f g) : fst t ≫ f = snd t ≫ g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma equalizerCondition_w (P : Cᵒᵖ ⥤ D) {X B : C} {π : X ⟶ B} (c : PullbackCone π π) :
    P.map π.op ≫ P.map c.fst.op = P.map π.op ≫ P.map c.snd.op := by
  simp only [← Functor.map_comp, ← op_comp, c.condition]

/--
A contravariant functor on `C` satisfies `SingleEqualizerCondition` with respect to a morphism `π`
if it takes its kernel pair to an equalizer diagram.
-/
/-
**CategoryTheory.regularTopology.SingleEqualizerCondition** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.regularTopology`。
形式化陈述：SingleEqualizerCondition (P : Cᵒᵖ ⥤ D) ⦃X B : C⦄ (π : X ⟶ B) : Prop
参数：P : Cᵒᵖ ⥤ D。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.regularTopology.equalizerCondition_w`：equalizerCondition_
w (P : Cᵒᵖ ⥤ D) {X B : C} {π : X ⟶ B} (c : PullbackCone π π) : P.map π.op ≫ P.ma
p c.fst.op = P.map π.op ≫ P.map c.snd.op

--- 原说明 ---
A contravariant functor on `C` satisfies `SingleEqualizerCondition` with respect
 to a morphism `π`
if it takes its kernel pair to an equalizer diagram.
-/
def SingleEqualizerCondition (P : Cᵒᵖ ⥤ D) ⦃X B : C⦄ (π : X ⟶ B) : Prop :=
  ∀ (c : PullbackCone π π) (_ : IsLimit c),
    Nonempty (IsLimit (Fork.ofι (P.map π.op) (equalizerCondition_w P c)))

/--
A contravariant functor on `C` satisfies `EqualizerCondition` if it takes kernel pairs of effective
epimorphisms to equalizer diagrams.
-/
/-
**CategoryTheory.regularTopology.EqualizerCondition** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.regularTopology`。
形式化陈述：EqualizerCondition (P : Cᵒᵖ ⥤ D) : Prop
参数：P : Cᵒᵖ ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A contravariant functor on `C` satisfies `EqualizerCondition` if it takes kernel
 pairs of effective
epimorphisms to equalizer diagrams.
-/
def EqualizerCondition (P : Cᵒᵖ ⥤ D) : Prop :=
  ∀ ⦃X B : C⦄ (π : X ⟶ B) [EffectiveEpi π], SingleEqualizerCondition P π

set_option backward.defeqAttrib.useBackward true in
/-- The equalizer condition is preserved by natural isomorphism. -/
/-
**CategoryTheory.regularTopology.equalizerCondition_of_natIso** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.regularTopology`。
形式化陈述：equalizerCondition_of_natIso {P P' : Cᵒᵖ ⥤ D} (i : P ≅ P') (hP : Equalizer
Condition P) : EqualizerCondition P'
参数：i : P ≅ P'；hP : EqualizerCondition P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.regularTopology.equalizerCondition_w`：equalizerCondition_
w (P : Cᵒᵖ ⥤ D) {X B : C} {π : X ⟶ B} (c : PullbackCone π π) : P.map π.op ≫ P.ma
p c.fst.op = P.map π.op ≫ P.map c.snd.op
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The equalizer condition is preserved by natural isomorphism.
-/
theorem equalizerCondition_of_natIso {P P' : Cᵒᵖ ⥤ D} (i : P ≅ P')
    (hP : EqualizerCondition P) : EqualizerCondition P' := fun X B π _ c hc ↦
  ⟨Fork.isLimitOfIsos _ (hP π c hc).some _ (i.app _) (i.app _) (i.app _)⟩

set_option backward.isDefEq.respectTransparency false in
/-- Precomposing with a pullback-preserving functor preserves the equalizer condition. -/
/-
**CategoryTheory.regularTopology.equalizerCondition_precomp_of_preservesPullback
** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.regularTopology`。
形式化陈述：equalizerCondition_precomp_of_preservesPullback (P : Cᵒᵖ ⥤ D) (F : E ⥤ C) 
[forall {X B} (π : X ⟶ B) [EffectiveEpi π], PreservesLimit (cospan π π) F] [F.Pr
eservesEffectiveEpis] (hP : EqualizerCondition P) : EqualizerCondition (F.op ⋙ P
)
参数：P : Cᵒᵖ ⥤ D；F : E ⥤ C；π : X ⟶ B；cospan π π；hP : EqualizerCondition P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CategoryTheory.regularTopology.equalizerCondition_w`：equalizerCondition_
w (P : Cᵒᵖ ⥤ D) {X B : C} {π : X ⟶ B} (c : PullbackCone π π) : P.map π.op ≫ P.ma
p c.fst.op = P.map π.op ≫ P.map c.snd.op
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.PullbackCone.condition`：condition (t : PullbackCon
e f g) : fst t ≫ f = snd t ≫ g
· 使用定理 `CategoryTheory.Limits.PullbackCone.mk_π_app`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {W : C} (fst :
 W ⟶ X)   (snd : W ⟶ Y)   (eq :  …
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…

--- 原说明 ---
Precomposing with a pullback-preserving functor preserves the equalizer conditio
n.
-/
theorem equalizerCondition_precomp_of_preservesPullback (P : Cᵒᵖ ⥤ D) (F : E ⥤ C)
    [∀ {X B} (π : X ⟶ B) [EffectiveEpi π], PreservesLimit (cospan π π) F]
    [F.PreservesEffectiveEpis] (hP : EqualizerCondition P) : EqualizerCondition (F.op ⋙ P) := by
  intro X B π _ c hc
  have h : P.map (F.map π).op = (F.op ⋙ P).map π.op := by simp
  refine ⟨(IsLimit.equivIsoLimit (ForkOfι.ext ?_ _ h)) ?_⟩
  · simp only [Functor.comp_map, op_map, Quiver.Hom.unop_op, ← map_comp, ← op_comp, c.condition]
  · refine (hP (F.map π) (PullbackCone.mk (F.map c.fst) (F.map c.snd) ?_) ?_).some
    · simp only [← map_comp, c.condition]
    · exact (isLimitMapConePullbackConeEquiv F c.condition)
        (isLimitOfPreserves F (hc.ofIsoLimit (PullbackCone.ext (Iso.refl _) (by simp) (by simp))))

/-- The canonical map to the explicit equalizer. -/
/-
**CategoryTheory.regularTopology.mapToEqualizer** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.regularTopology`。
形式化陈述：mapToEqualizer (P : Cᵒᵖ ⥤ Type*) {W X B : C} (f : X ⟶ B) (g₁ g₂ : W ⟶ X) (
w : g₁ ≫ f = g₂ ≫ f) : P.obj (op B) ⟶ { x : P.obj (op X) | P.map g₁.op x = P.map
 g₂.op x }
参数：P : Cᵒᵖ ⥤ Type*；f : X ⟶ B；g₁ g₂ : W ⟶ X；w : g₁ ≫ f = g₂ ≫ f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical map to the explicit equalizer.
-/
def mapToEqualizer (P : Cᵒᵖ ⥤ Type*) {W X B : C} (f : X ⟶ B)
    (g₁ g₂ : W ⟶ X) (w : g₁ ≫ f = g₂ ≫ f) :
    P.obj (op B) ⟶ { x : P.obj (op X) | P.map g₁.op x = P.map g₂.op x } :=
  ↾fun t ↦
    ⟨P.map f.op t, by simp only [Set.mem_ofPred_eq, ← comp_apply, ← Functor.map_comp, ← op_comp, w]⟩
/-
**CategoryTheory.regularTopology.EqualizerCondition.bijective_mapToEqualizer_pul
lback'** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.regularTopology.EqualizerCondit
ion`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {P : Catego
ryTheory.Functor Cᵒᵖ (Type u_4)},   CategoryTheory.regularTopology.EqualizerCond
ition P →     ∀ {X B : C} {π : X ⟶ B} [CategoryTheory.EffectiveEpi π] (c : Categ
oryTheory.Limits.PullbackCone π π)       (hc : CategoryTheory.Limits.IsLimit c),
       Function.Bijective         ⇑(CategoryTheory.ConcreteCategory.hom (Categor
yTheory.regularTopology.mapToEqualizer P π c.fst c.snd ⋯))
参数：Type u_4；c : CategoryTheory.Limits.PullbackCone π π；hc : CategoryTheory.Limit
s.IsLimit c；CategoryTheory.ConcreteCategory.hom (CategoryTheory.regularTopology.
mapToEqualizer P π c.fst c.snd ⋯)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.PullbackCone.condition`：condition (t : PullbackCon
e f g) : fst t ≫ f = snd t ≫ g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.bijective_iff_existsUnique`：bijective_iff_existsUnique (f : α -
> β) : Bijective f ↔ forall b : β, exists! a : α, f a = b
· 使用引理 `CategoryTheory.regularTopology.equalizerCondition_w`：equalizerCondition_
w (P : Cᵒᵖ ⥤ D) {X B : C} {π : X ⟶ B} (c : PullbackCone π π) : P.map π.op ≫ P.ma
p c.fst.op = P.map π.op ≫ P.map c.snd.op
· 使用定理 `CategoryTheory.Limits.Types.type_equalizer_iff_unique`：type_equalizer_if
f_unique : Nonempty (IsLimit (Fork.ofι _ w)) ↔ forall y : Y, g y = h y -> exists
! x : X, f x = y
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
-/
theorem EqualizerCondition.bijective_mapToEqualizer_pullback' {P : Cᵒᵖ ⥤ Type*}
    (hP : EqualizerCondition P) {X B : C} {π : X ⟶ B} [EffectiveEpi π]
    (c : PullbackCone π π) (hc : IsLimit c) :
    Function.Bijective (mapToEqualizer P π c.fst c.snd c.condition) := by
  specialize hP π _ hc
  rw [Types.type_equalizer_iff_unique] at hP
  rw [Function.bijective_iff_existsUnique]
  intro ⟨b, hb⟩
  obtain ⟨a, ha₁, ha₂⟩ := hP b hb
  refine ⟨a, ?_, ?_⟩
  · ext
    simpa [mapToEqualizer] using! ha₁
  · intro y h
    apply ha₂ y
    simpa [mapToEqualizer] using Subtype.ext_iff.1 h
/-
**CategoryTheory.regularTopology.EqualizerCondition.bijective_mapToEqualizer_pul
lback** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.regularTopology.EqualizerConditi
on`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {P : Catego
ryTheory.Functor Cᵒᵖ (Type u_4)},   CategoryTheory.regularTopology.EqualizerCond
ition P →     ∀ {X B : C} (π : X ⟶ B) [CategoryTheory.EffectiveEpi π] [inst_2 : 
CategoryTheory.Limits.HasPullback π π],       Function.Bijective         ⇑(Categ
oryTheory.ConcreteCategory.hom             (CategoryTheory.regularTopology.mapTo
Equalizer P π (CategoryTheory.Limits.pullback.fst π π)               (CategoryTh
eory.Limits.pullback.snd π π) ⋯))
参数：Type u_4；π : X ⟶ B；CategoryTheory.ConcreteCategory.hom             (CategoryT
heory.regularTopology.mapToEqualizer P π (CategoryTheory.Limits.pullback.fst π π
)               (CategoryTheory.Limits.pullback.snd π π) ⋯)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.regularTopology.EqualizerCondition.bijective_mapToEqualiz
er_pullback'`：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {P 
: CategoryTheory.Functor Cᵒᵖ (Type u_4)},   CategoryTheory.regularTopology…
-/
theorem EqualizerCondition.bijective_mapToEqualizer_pullback {P : Cᵒᵖ ⥤ Type*}
    (hP : EqualizerCondition P) {X B : C} (π : X ⟶ B) [EffectiveEpi π] [HasPullback π π] :
    Function.Bijective
      (mapToEqualizer P π (pullback.fst π π) (pullback.snd π π) pullback.condition) :=
  bijective_mapToEqualizer_pullback' hP _ (pullback.isLimit _ _)
/-
**CategoryTheory.regularTopology.EqualizerCondition.mk'** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.regularTopology.EqualizerCondition`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] (P : Catego
ryTheory.Functor Cᵒᵖ (Type u_4)),   (∀ (X B : C) (π : X ⟶ B) [CategoryTheory.Eff
ectiveEpi π] (c : CategoryTheory.Limits.PullbackCone π π)       (x : CategoryThe
ory.Limits.IsLimit c),       Function.Bijective         ⇑(CategoryTheory.Concret
eCategory.hom (CategoryTheory.regularTopology.mapToEqualizer P π c.fst c.snd ⋯))
) →     CategoryTheory.regularTopology.EqualizerCondition P
参数：P : CategoryTheory.Functor Cᵒᵖ (Type u_4)；∀ (X B : C) (π : X ⟶ B) [CategoryTh
eory.EffectiveEpi π] (c : CategoryTheory.Limits.PullbackCone π π)       (x : Cat
egoryTheory.Limits.IsLimit c),       Function.Bijective         ⇑(CategoryTheory
.ConcreteCategory.hom (CategoryTheory.regularTopology.mapToEqualizer P π c.fst c
.snd ⋯))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.PullbackCone.condition`：condition (t : PullbackCon
e f g) : fst t ≫ f = snd t ≫ g
· 使用引理 `CategoryTheory.regularTopology.equalizerCondition_w`：equalizerCondition_
w (P : Cᵒᵖ ⥤ D) {X B : C} {π : X ⟶ B} (c : PullbackCone π π) : P.map π.op ≫ P.ma
p c.fst.op = P.map π.op ≫ P.map c.snd.op
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.Types.type_equalizer_iff_unique`：type_equalizer_if
f_unique : Nonempty (IsLimit (Fork.ofι _ w)) ↔ forall y : Y, g y = h y -> exists
! x : X, f x = y
· 使用定理 `Function.bijective_iff_existsUnique`：bijective_iff_existsUnique (f : α -
> β) : Bijective f ↔ forall b : β, exists! a : α, f a = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
-/
theorem EqualizerCondition.mk' (P : Cᵒᵖ ⥤ Type*)
    (hP : ∀ (X B : C) (π : X ⟶ B) [EffectiveEpi π] (c : PullbackCone π π) (_ : IsLimit c),
      Function.Bijective (mapToEqualizer P π c.fst c.snd c.condition)) :
    EqualizerCondition P := by
  intro X B π _ c hc
  specialize hP X B π c hc
  rw [Types.type_equalizer_iff_unique]
  rw [Function.bijective_iff_existsUnique] at hP
  intro b hb
  obtain ⟨a, ha₁, ha₂⟩ := hP ⟨b, hb⟩
  refine ⟨a, ?_, ?_⟩
  · simpa [mapToEqualizer] using Subtype.ext_iff.1 ha₁
  · intro y h
    apply ha₂ y
    ext
    simpa [mapToEqualizer] using h

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.regularTopology.EqualizerCondition.mk** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.regularTopology.EqualizerCondition`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] (P : Catego
ryTheory.Functor Cᵒᵖ (Type u_4)),   (∀ (X B : C) (π : X ⟶ B) [CategoryTheory.Eff
ectiveEpi π] [inst_2 : CategoryTheory.Limits.HasPullback π π],       Function.Bi
jective         ⇑(CategoryTheory.ConcreteCategory.hom             (CategoryTheor
y.regularTopology.mapToEqualizer P π (CategoryTheory.Limits.pullback.fst π π)   
            (CategoryTheory.Limits.pullback.snd π π) ⋯))) →     CategoryTheory.r
egularTopology.EqualizerCondition P
参数：P : CategoryTheory.Functor Cᵒᵖ (Type u_4)；∀ (X B : C) (π : X ⟶ B) [CategoryTh
eory.EffectiveEpi π] [inst_2 : CategoryTheory.Limits.HasPullback π π],       Fun
ction.Bijective         ⇑(CategoryTheory.ConcreteCategory.hom             (Categ
oryTheory.regularTopology.mapToEqualizer P π (CategoryTheory.Limits.pullback.fst
 π π)               (CategoryTheory.Limits.pullback.snd π π) ⋯))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.pullback.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPullback f…
· 使用引理 `CategoryTheory.regularTopology.equalizerCondition_w`：equalizerCondition_
w (P : Cᵒᵖ ⥤ D) {X B : C} {π : X ⟶ B} (c : PullbackCone π π) : P.map π.op ≫ P.ma
p c.fst.op = P.map π.op ≫ P.map c.snd.op
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.Types.type_equalizer_iff_unique`：type_equalizer_if
f_unique : Nonempty (IsLimit (Fork.ofι _ w)) ↔ forall y : Y, g y = h y -> exists
! x : X, f x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.IsLimit.conePointUniqueUpToIso_hom_comp`：conePoint
UniqueUpToIso_hom_comp {s t : Cone F} (P : IsLimit s) (Q : IsLimit t) (j : J) : 
(conePointUniqueUpToIso P Q).hom ≫ t.π.app j = s.π.…
· 使用定理 `CategoryTheory.Limits.PullbackCone.mk_π_app`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {W : C} (fst :
 W ⟶ X)   (snd : W ⟶ Y)   (eq :  …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.op_comp`：op_comp {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} : (f
 ≫ g).op = g.op ≫ f.op
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
· 使用引理 `CategoryTheory.types_congr_hom`：types_congr_hom {X Y : Type u} {f g : X 
⟶ Y} (h : f = g) (x : X) : f x = g x
· 使用定理 `Function.bijective_iff_existsUnique`：bijective_iff_existsUnique (f : α -
> β) : Bijective f ↔ forall b : β, exists! a : α, f a = b
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem EqualizerCondition.mk (P : Cᵒᵖ ⥤ Type*)
    (hP : ∀ (X B : C) (π : X ⟶ B) [EffectiveEpi π] [HasPullback π π], Function.Bijective
    (mapToEqualizer P π (pullback.fst π π) (pullback.snd π π)
    pullback.condition)) : EqualizerCondition P := by
  intro X B π _ c hc
  have : HasPullback π π := ⟨c, hc⟩
  specialize hP X B π
  rw [Types.type_equalizer_iff_unique]
  rw [Function.bijective_iff_existsUnique] at hP
  intro b hb
  have h₁ : ((pullbackIsPullback π π).conePointUniqueUpToIso hc).hom ≫ c.fst =
    pullback.fst π π := by simp
  have hb' : P.map (pullback.fst π π).op b = P.map (pullback.snd _ _).op b := by
    rw [← h₁, op_comp, Functor.map_comp, comp_apply, hb]
    simp [← comp_apply, ← Functor.map_comp, ← op_comp]
  obtain ⟨a, ha₁, ha₂⟩ := hP ⟨b, hb'⟩
  refine ⟨a, ?_, ?_⟩
  · simpa [mapToEqualizer] using ha₁
  · simpa [mapToEqualizer] using ha₂
/-
**CategoryTheory.regularTopology.equalizerCondition_w'** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.regularTopology`。
形式化陈述：equalizerCondition_w' (P : Cᵒᵖ ⥤ Type*) {X B : C} (π : X ⟶ B) [HasPullback
 π π] : P.map π.op ≫ P.map (pullback.fst π π).op = P.map π.op ≫ P.map (pullback.
snd π π).op
参数：P : Cᵒᵖ ⥤ Type*；π : X ⟶ B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.pullback.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPullback f…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma equalizerCondition_w' (P : Cᵒᵖ ⥤ Type*) {X B : C} (π : X ⟶ B)
    [HasPullback π π] : P.map π.op ≫ P.map (pullback.fst π π).op =
    P.map π.op ≫ P.map (pullback.snd π π).op := by
  simp only [← Functor.map_comp, ← op_comp, pullback.condition]

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.regularTopology.mapToEqualizer_eq_comp** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.regularTopology`。
形式化陈述：mapToEqualizer_eq_comp (P : Cᵒᵖ ⥤ Type*) {X B : C} (π : X ⟶ B) [HasPullbac
k π π] : mapToEqualizer P π (pullback.fst π π) (pullback.snd π π) pullback.condi
tion = equalizer.lift (P.map π.op) (equalizerCondition_w' P π) ≫ (Types.equalize
rIso _ _).hom
参数：P : Cᵒᵖ ⥤ Type*；π : X ⟶ B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.pullback.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPullback f…
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用引理 `CategoryTheory.regularTopology.equalizerCondition_w'`：equalizerCondition
_w' (P : Cᵒᵖ ⥤ Type*) {X B : C} (π : X ⟶ B) [HasPullback π π] : P.map π.op ≫ P.m
ap (pullback.fst π π).op = P.map π.op ≫ P.…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Iso.comp_inv_eq`：comp_inv_eq (α : X ≅ Y) {f : Z ⟶ Y} {g :
 Z ⟶ X} : f ≫ α.inv = g ↔ f = g ≫ α.hom
· 使用定理 `CategoryTheory.Limits.equalizer.hom_ext`：∀ {C : Type u} {X Y : C} [inst 
: CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y}   [inst_1 : CategoryTheory.Lim
its.HasEqualizer f g] {W : C}…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.Types.equalizerIso_inv_comp_ι`：equalizerIso_inv_co
mp_ι : (equalizerIso g h).inv ≫ equalizer.ι g h = ↾Subtype.val
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
-/
lemma mapToEqualizer_eq_comp (P : Cᵒᵖ ⥤ Type*) {X B : C} (π : X ⟶ B) [HasPullback π π] :
    mapToEqualizer P π (pullback.fst π π) (pullback.snd π π) pullback.condition =
    equalizer.lift (P.map π.op) (equalizerCondition_w' P π) ≫
    (Types.equalizerIso _ _).hom := by
  rw [← Iso.comp_inv_eq (α := Types.equalizerIso _ _)]
  apply equalizer.hom_ext
  aesop

set_option backward.isDefEq.respectTransparency false in
/-- An alternative phrasing of the explicit equalizer condition, using more categorical language. -/
/-
**CategoryTheory.regularTopology.equalizerCondition_iff_isIso_lift** 是 Mathlib 中
的一个定理，位于命名空间 `CategoryTheory.regularTopology`。
形式化陈述：equalizerCondition_iff_isIso_lift (P : Cᵒᵖ ⥤ Type*) : EqualizerCondition P
 ↔ forall (X B : C) (π : X ⟶ B) [EffectiveEpi π] [HasPullback π π], IsIso (equal
izer.lift (P.map π.op) (equalizerCondition_w' P π))
参数：P : Cᵒᵖ ⥤ Type*。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用引理 `CategoryTheory.regularTopology.equalizerCondition_w'`：equalizerCondition
_w' (P : Cᵒᵖ ⥤ Type*) {X B : C} (π : X ⟶ B) [HasPullback π π] : P.map π.op ≫ P.m
ap (pullback.fst π π).op = P.map π.op ≫ P.…
· 使用定理 `CategoryTheory.Limits.pullback.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPullback f…
· 使用定理 `CategoryTheory.regularTopology.EqualizerCondition.bijective_mapToEqualiz
er_pullback`：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {P :
 CategoryTheory.Functor Cᵒᵖ (Type u_4)},   CategoryTheory.regularTopology…
· 使用定理 `CategoryTheory.IsIso.of_isIso_comp_right`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} (g : Z ⟶ Y) (f : Y ⟶ X) [CategoryTheory.I
sIso f]   [CategoryTheory.IsIs…
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.regularTopology.mapToEqualizer_eq_comp`：mapToEqualizer_eq
_comp (P : Cᵒᵖ ⥤ Type*) {X B : C} (π : X ⟶ B) [HasPullback π π] : mapToEqualizer
 P π (pullback.fst π π) (pullback.snd π π) …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.isIso_iff_bijective`：isIso_iff_bijective {X Y : Type u} (
f : X ⟶ Y) : IsIso f ↔ Function.Bijective f
· 使用定理 `CategoryTheory.regularTopology.EqualizerCondition.mk`：∀ {C : Type u_1} [
inst : CategoryTheory.Category.{v_1, u_1} C] (P : CategoryTheory.Functor Cᵒᵖ (Ty
pe u_4)),   (∀ (X B : C) (π : X ⟶ B) [Cate…

--- 原说明 ---
An alternative phrasing of the explicit equalizer condition, using more categori
cal language.
-/
theorem equalizerCondition_iff_isIso_lift (P : Cᵒᵖ ⥤ Type*) : EqualizerCondition P ↔
    ∀ (X B : C) (π : X ⟶ B) [EffectiveEpi π] [HasPullback π π],
      IsIso (equalizer.lift (P.map π.op) (equalizerCondition_w' P π)) := by
  constructor
  · intro hP X B π _ _
    have h := hP.bijective_mapToEqualizer_pullback π
    rw [← isIso_iff_bijective, mapToEqualizer_eq_comp] at h
    exact IsIso.of_isIso_comp_right (equalizer.lift (P.map π.op)
      (equalizerCondition_w' P π))
      (Types.equalizerIso _ _).hom
  · intro hP
    apply EqualizerCondition.mk
    intro X B π _ _
    rw [mapToEqualizer_eq_comp, ← isIso_iff_bijective]
    infer_instance

/-- `P` satisfies the equalizer condition iff its precomposition by an equivalence does. -/
/-
**CategoryTheory.regularTopology.equalizerCondition_iff_of_equivalence** 是 Mathl
ib 中的一个定理，位于命名空间 `CategoryTheory.regularTopology`。
形式化陈述：equalizerCondition_iff_of_equivalence (P : Cᵒᵖ ⥤ D) (e : C ≌ E) : Equalize
rCondition P ↔ EqualizerCondition (e.op.inverse ⋙ P)
参数：P : Cᵒᵖ ⥤ D；e : C ≌ E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.regularTopology.equalizerCondition_precomp_of_preservesPu
llback`：equalizerCondition_precomp_of_preservesPullback (P : Cᵒᵖ ⥤ D) (F : E ⥤ C
) [forall {X B} (π : X ⟶ B) [EffectiveEpi π], PreservesLimit (cospan…
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Limits.PreservesFiniteLimits.preservesFiniteLimits`：∀ {C 
: Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : C
ategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.PreservesLimits.preservesFiniteLimits`：∀ {C : Type
 u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Categor
yTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.instPreservesLimitsOfSizeOfIsRightAdjoint`：∀ {C :
 Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_2, u_2} C]   [inst_
1 : CategoryTheory.Category.{v_3, u_3} D] (F : Categor…
· 使用定理 `CategoryTheory.Functor.isRightAdjoint_of_isEquivalence`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_inverse`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.inv…
· 使用定理 `CategoryTheory.Functor.instPreservesEffectiveEpisOfPreservesFiniteEffect
iveEpiFamilies`：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {
D : Type u_2}   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] (F : Categor…
· 使用定理 `CategoryTheory.Functor.instPreservesFiniteEffectiveEpiFamiliesOfPreserve
sEffectiveEpiFamilies`：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_
1} C] {D : Type u_2}   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] (F : Cate
gor…
· 使用定理 `CategoryTheory.Functor.instPreservesEffectiveEpiFamiliesOfIsEquivalence`
：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {D : Type u_2}  
 [inst_1 : CategoryTheory.Category.{v_2, u_2} D] (F : Categor…
· 使用定理 `CategoryTheory.regularTopology.equalizerCondition_of_natIso`：equalizerCo
ndition_of_natIso {P P' : Cᵒᵖ ⥤ D} (i : P ≅ P') (hP : EqualizerCondition P) : Eq
ualizerCondition P'
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_functor`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.fun…

--- 原说明 ---
`P` satisfies the equalizer condition iff its precomposition by an equivalence d
oes.
-/
theorem equalizerCondition_iff_of_equivalence (P : Cᵒᵖ ⥤ D)
    (e : C ≌ E) : EqualizerCondition P ↔ EqualizerCondition (e.op.inverse ⋙ P) :=
  ⟨fun h ↦ equalizerCondition_precomp_of_preservesPullback P e.inverse h, fun h ↦
    equalizerCondition_of_natIso (e.op.funInvIdAssoc P)
      (equalizerCondition_precomp_of_preservesPullback (e.op.inverse ⋙ P) e.functor h)⟩

set_option backward.isDefEq.respectTransparency false in
open WalkingParallelPair WalkingParallelPairHom in
/-
**CategoryTheory.regularTopology.parallelPair_pullback_initial** 是 Mathlib 中的一个定
理，位于命名空间 `CategoryTheory.regularTopology`。
形式化陈述：parallelPair_pullback_initial {X B : C} (π : X ⟶ B) (c : PullbackCone π π)
 (hc : IsLimit c) : (parallelPair (C
参数：π : X ⟶ B；c : PullbackCone π π；hc : IsLimit c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.parallelPair_initial_mk`：parallelPair_initial_mk {
X Y : C} (f g : X ⟶ Y) (h₁ : forall Z, Nonempty (X ⟶ Z)) (h₂ : forall ⦃Z : C⦄ (i
 j : X ⟶ Z), exists (a : Y ⟶ Z), i …
· 使用引理 `CategoryTheory.Sieve.ofArrows_mk`：ofArrows_mk (i : I) : ofArrows Y f (f 
i)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.PullbackCone.condition`：condition (t : PullbackCon
e f g) : fst t ≫ f = snd t ≫ g
· 使用定理 `CategoryTheory.ObjectProperty.FullSubcategory.property`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.ObjectProperty C}  
 (self : P.FullSubcategory), P self.obj
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `CategoryTheory.Over.w`：w : φ.left ≫ g.hom = f.hom
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Limits.PullbackCone.IsLimit.lift_fst_assoc`：∀ {C : Type u
} [inst : CategoryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} 
  {t : CategoryTheory.Limits.PullbackCone f g} …
· 使用引理 `CategoryTheory.ObjectProperty.hom_ext`：hom_ext {X Y : P.FullSubcategory}
 {f g : X ⟶ Y} (h : f.hom = g.hom) : f = g
· 使用定理 `CategoryTheory.Over.OverMorphism.ext`：∀ {T : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} T] {X : T} {U V : CategoryTheory.Over X} {f g : U ⟶ V},  
 CategoryTheory.Over.Hom.l…
· 使用定理 `CategoryTheory.Over.homMk_left`：∀ {T : Type u₁} [inst : CategoryTheory.C
ategory.{v₁, u₁} T] {X : T} {U V : CategoryTheory.Over X} (f : U.left ⟶ V.left) 
  (w : autoParam (Ca…
· 使用定理 `CategoryTheory.Limits.PullbackCone.IsLimit.lift_fst`：∀ {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   {t :
 CategoryTheory.Limits.PullbackCone f g} …
· 使用定理 `CategoryTheory.Limits.PullbackCone.IsLimit.lift_snd`：∀ {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   {t :
 CategoryTheory.Limits.PullbackCone f g} …
-/
theorem parallelPair_pullback_initial {X B : C} (π : X ⟶ B)
    (c : PullbackCone π π) (hc : IsLimit c) :
    (parallelPair (C := (Sieve.ofArrows (fun (_ : Unit) => X) (fun _ => π)).arrows.categoryᵒᵖ)
    (Y := op ((Presieve.categoryMk _ (c.fst ≫ π) ⟨_, c.fst, π, ofArrows.mk (), rfl⟩)))
    (X := op ((Presieve.categoryMk _ π (Sieve.ofArrows_mk _ _ Unit.unit))))
    ((ObjectProperty.homMk (Over.homMk c.fst)).op)
    ((ObjectProperty.homMk (Over.homMk c.snd c.condition.symm)).op)).Initial := by
  apply Limits.parallelPair_initial_mk
  · intro ⟨Z⟩
    obtain ⟨_, f, g, ⟨⟩, hh⟩ := Z.property
    let X' : (Presieve.ofArrows (fun () ↦ X) (fun () ↦ π)).category :=
      Presieve.categoryMk _ π (ofArrows.mk ())
    let f' : Z.obj.left ⟶ X'.obj.left := f
    exact ⟨(ObjectProperty.homMk (Over.homMk f')).op⟩
  · intro ⟨Z⟩ ⟨i⟩ ⟨j⟩
    have hi := Over.w i.hom
    have hj := Over.w j.hom
    dsimp at hi hj
    let ij := PullbackCone.IsLimit.lift hc i.hom.left j.hom.left (by simp [hi, hj])
    refine ⟨Quiver.Hom.op (ObjectProperty.homMk (Over.homMk ij)), ?_, ?_⟩
    all_goals congr; aesop

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Given a limiting pullback cone, the fork in `SingleEqualizerCondition` is limiting iff the diagram
in `Presheaf.isSheaf_iff_isLimit_coverage` is limiting.
-/
/-
**CategoryTheory.regularTopology.isLimit_forkOf** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.regularTopology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a limiting pullback cone, the fork in `SingleEqualizerCondition` is limiti
ng iff the diagram
in `Presheaf.isSheaf_iff_isLimit_coverage` is limiting.
-/
noncomputable def isLimit_forkOfι_equiv (P : Cᵒᵖ ⥤ D) {X B : C} (π : X ⟶ B)
    (c : PullbackCone π π) (hc : IsLimit c) :
    IsLimit (Fork.ofι (P.map π.op) (equalizerCondition_w P c)) ≃
    IsLimit (P.mapCone (Sieve.ofArrows (fun (_ : Unit) ↦ X) fun _ ↦ π).arrows.cocone.op) := by
  let S := (Sieve.ofArrows (fun (_ : Unit) => X) (fun _ => π)).arrows
  let X' := S.categoryMk π ⟨_, 𝟙 _, π, ofArrows.mk (), Category.id_comp _⟩
  let P' := S.categoryMk (c.fst ≫ π) ⟨_, c.fst, π, ofArrows.mk (), rfl⟩
  let fst : P' ⟶ X' := ObjectProperty.homMk (Over.homMk c.fst)
  let snd : P' ⟶ X' := ObjectProperty.homMk (Over.homMk c.snd c.condition.symm)
  let F : S.categoryᵒᵖ ⥤ D := S.diagram.op ⋙ P
  let G := parallelPair (P.map c.fst.op) (P.map c.snd.op)
  let H := parallelPair fst.op snd.op
  have : H.Initial := parallelPair_pullback_initial π c hc
  let i : H ⋙ F ≅ G := parallelPair.ext (Iso.refl _) (Iso.refl _) (by aesop) (by aesop)
  refine (IsLimit.equivOfNatIsoOfIso i.symm _ _ ?_).trans (Functor.Initial.isLimitWhiskerEquiv H _)
  refine Cone.ext (Iso.refl _) ?_
  rintro ⟨_ | _⟩
  all_goals aesop
/-
**CategoryTheory.regularTopology.equalizerConditionMap_iff_nonempty_isLimit** 是 
Mathlib 中的一个引理，位于命名空间 `CategoryTheory.regularTopology`。
形式化陈述：equalizerConditionMap_iff_nonempty_isLimit (P : Cᵒᵖ ⥤ D) ⦃X B : C⦄ (π : X 
⟶ B) [HasPullback π π] : SingleEqualizerCondition P π ↔ Nonempty (IsLimit (P.map
Cone (Sieve.ofArrows (fun (_ : Unit) => X) (fun _ => π)).arrows.cocone.op))
参数：P : Cᵒᵖ ⥤ D。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.pullback.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPullback f…
· 使用引理 `CategoryTheory.regularTopology.equalizerCondition_w`：equalizerCondition_
w (P : Cᵒᵖ ⥤ D) {X B : C} {π : X ⟶ B} (c : PullbackCone π π) : P.map π.op ≫ P.ma
p c.fst.op = P.map π.op ≫ P.map c.snd.op
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma equalizerConditionMap_iff_nonempty_isLimit (P : Cᵒᵖ ⥤ D) ⦃X B : C⦄ (π : X ⟶ B)
    [HasPullback π π] : SingleEqualizerCondition P π ↔
      Nonempty (IsLimit (P.mapCone
        (Sieve.ofArrows (fun (_ : Unit) => X) (fun _ => π)).arrows.cocone.op)) := by
  constructor
  · intro h
    exact ⟨isLimit_forkOfι_equiv _ _ _ (pullbackIsPullback π π) (h _ (pullbackIsPullback π π)).some⟩
  · intro ⟨h⟩
    exact fun c hc ↦ ⟨(isLimit_forkOfι_equiv _ _ _ hc).symm h⟩
/-
**CategoryTheory.regularTopology.equalizerCondition_iff_isSheaf** 是 Mathlib 中的一个
引理，位于命名空间 `CategoryTheory.regularTopology`。
形式化陈述：equalizerCondition_iff_isSheaf (F : Cᵒᵖ ⥤ D) [Preregular C] [forall {Y X :
 C} (f : Y ⟶ X) [EffectiveEpi f], HasPullback f f] : EqualizerCondition F ↔ Pres
heaf.IsSheaf (regularTopology C) F
参数：F : Cᵒᵖ ⥤ D；f : Y ⟶ X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Presheaf.isSheaf_iff_isLimit_coverage`：isSheaf_iff_isLimi
t_coverage (K : Coverage C) (P : Cᵒᵖ ⥤ D) : Presheaf.IsSheaf K.toGrothendieck P 
↔ forall ⦃X : C⦄ (R : Presieve X), R in K …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `CategoryTheory.regularTopology.equalizerConditionMap_iff_nonempty_isLimi
t`：equalizerConditionMap_iff_nonempty_isLimit (P : Cᵒᵖ ⥤ D) ⦃X B : C⦄ (π : X ⟶ B
) [HasPullback π π] : SingleEqualizerCondition P π ↔ Nonempty (…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
lemma equalizerCondition_iff_isSheaf (F : Cᵒᵖ ⥤ D) [Preregular C]
    [∀ {Y X : C} (f : Y ⟶ X) [EffectiveEpi f], HasPullback f f] :
    EqualizerCondition F ↔ Presheaf.IsSheaf (regularTopology C) F := by
  dsimp [regularTopology]
  rw [Presheaf.isSheaf_iff_isLimit_coverage]
  constructor
  · rintro hF X _ ⟨Y, f, rfl, _⟩
    exact (equalizerConditionMap_iff_nonempty_isLimit F f).1 (hF f)
  · intro hF Y X f _
    exact (equalizerConditionMap_iff_nonempty_isLimit F f).2 (hF _ ⟨_, f, rfl, inferInstance⟩)
/-
**CategoryTheory.regularTopology.isSheafFor_regular_of_projective** 是 Mathlib 中的
一个引理，位于命名空间 `CategoryTheory.regularTopology`。
形式化陈述：isSheafFor_regular_of_projective {X : C} (S : Presieve X) [S.regular] [Pro
jective X] (F : Cᵒᵖ ⥤ Type*) : S.IsSheafFor F
参数：S : Presieve X；F : Cᵒᵖ ⥤ Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Presieve.regular.single_epi`：∀ {C : Type u_1} {inst : Cat
egoryTheory.Category.{v_1, u_1} C} {X : C} {R : CategoryTheory.Presieve X}   [se
lf : R.regular],   ∃ Y f, (R = C…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Presieve.isSheafFor_arrows_iff`：isSheafFor_arrows_iff : (
ofArrows X π).IsSheafFor P ↔ (forall (x : (i : I) -> P.obj (op (X i))), Arrows.C
ompatible P π x -> exists! t, foral…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `CategoryTheory.types_congr_hom`：types_congr_hom {X Y : Type u} {f g : X 
⟶ Y} (h : f = g) (x : X) : f x = g x
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.id_apply`：∀ {C : Type u} [inst : CategoryTheory.Category.
{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → FunL
ike (FC X Y) …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Projective.factorThru_comp`：factorThru_comp {P X E : C} [
Projective P] (f : P ⟶ X) (e : E ⟶ X) [Epi e] : factorThru f e ≫ e = f
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma isSheafFor_regular_of_projective {X : C} (S : Presieve X) [S.regular] [Projective X]
    (F : Cᵒᵖ ⥤ Type*) : S.IsSheafFor F := by
  obtain ⟨Y, f, rfl, hf⟩ := Presieve.regular.single_epi (R := S)
  rw [isSheafFor_arrows_iff]
  refine fun x hx ↦ ⟨F.map (Projective.factorThru (𝟙 _) f).op <| x (), fun _ ↦ ?_, fun y h ↦ ?_⟩
  · simpa using (hx () () Y (𝟙 Y) (f ≫ (Projective.factorThru (𝟙 _) f)) (by simp)).symm
  · simp [← h (), ← comp_apply, ← Functor.map_comp, ← op_comp]

/-- Every presheaf is a sheaf for the regular topology if every object of `C` is projective. -/
/-
**CategoryTheory.regularTopology.isSheaf_of_projective** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.regularTopology`。
形式化陈述：isSheaf_of_projective (F : Cᵒᵖ ⥤ D) [Preregular C] [forall (X : C), Projec
tive X] : Presheaf.IsSheaf (regularTopology C) F
参数：F : Cᵒᵖ ⥤ D；X : C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.Presieve.isSheaf_coverage`：isSheaf_coverage (K : Coverage
 C) (P : Cᵒᵖ ⥤ Type*) : Presieve.IsSheaf K.toGrothendieck P ↔ (forall {X : C} (R
 : Presieve X), R in K X -> Pr…
· 使用引理 `CategoryTheory.regularTopology.isSheafFor_regular_of_projective`：isSheaf
For_regular_of_projective {X : C} (S : Presieve X) [S.regular] [Projective X] (F
 : Cᵒᵖ ⥤ Type*) : S.IsSheafFor F

--- 原说明 ---
Every presheaf is a sheaf for the regular topology if every object of `C` is pro
jective.
-/
theorem isSheaf_of_projective (F : Cᵒᵖ ⥤ D) [Preregular C] [∀ (X : C), Projective X] :
    Presheaf.IsSheaf (regularTopology C) F :=
  fun _ ↦ (isSheaf_coverage _ _).mpr fun S ⟨_, h⟩ ↦ have : S.regular := ⟨_, h⟩
    isSheafFor_regular_of_projective _ _

/-- Every Yoneda-presheaf is a sheaf for the regular topology. -/
/-
**CategoryTheory.regularTopology.isSheaf_yoneda_obj** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.regularTopology`。
形式化陈述：isSheaf_yoneda_obj [Preregular C] (W : C) : Presieve.IsSheaf (regularTopol
ogy C) (yoneda.obj W)
参数：W : C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.regularTopology.eq_1`：∀ (C : Type u_1) [inst : CategoryTh
eory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preregular C],   CategoryTh
eory.regularTopology C = …
· 使用定理 `CategoryTheory.Presieve.isSheaf_coverage`：isSheaf_coverage (K : Coverage
 C) (P : Cᵒᵖ ⥤ Type*) : Presieve.IsSheaf K.toGrothendieck P ↔ (forall {X : C} (R
 : Presieve X), R in K X -> Pr…
· 使用定理 `CategoryTheory.Presieve.regular.single_epi`：∀ {C : Type u_1} {inst : Cat
egoryTheory.Category.{v_1, u_1} C} {X : C} {R : CategoryTheory.Presieve X}   [se
lf : R.regular],   ∃ Y f, (R = C…
· 使用定理 `CategoryTheory.EffectiveEpi.effectiveEpi`：∀ {C : Type u_1} {inst : Categ
oryTheory.Category.{v_1, u_1} C} {X Y : C} {f : Y ⟶ X}   [self : CategoryTheory.
EffectiveEpi f], Nonempty (Cat…
· 使用定理 `CategoryTheory.Presieve.FamilyOfElements.Compatible.sieveExtend`：∀ {C : 
Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {P : CategoryTheory.Functor
 Cᵒᵖ (Type w)} {X : C}   {R : CategoryTheory.Presieve…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.Sieve.forallYonedaIsSheaf_iff_colimit`：forallYonedaIsShea
f_iff_colimit (S : Sieve X) : (forall W : C, Presieve.IsSheafFor (yoneda.obj W) 
(S : Presieve X)) ↔ Nonempty (IsColimit S.…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Presieve.ofArrows_pUnit`：ofArrows_pUnit : (ofArrows _ fun
 _ : PUnit.{w + 1} => f) = singleton f
· 使用定理 `CategoryTheory.Sieve.generateSingleton_eq`：∀ {C : Type u} [inst : Catego
ryTheory.Category.{v, u} C] {X Y : C} (f : Y ⟶ X),   CategoryTheory.Sieve.genera
te (CategoryTheory.Presieve.sin…
· 使用定理 `CategoryTheory.Sieve.le_generate`：le_generate (R : Presieve X) : R <= ge
nerate R
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `CategoryTheory.Presieve.restrict_extend`：restrict_extend {x : FamilyOfEl
ements P R} (t : x.Compatible) : x.sieveExtend.restrict (le_generate R) = x
· 使用定理 `CategoryTheory.Presieve.isAmalgamation_restrict`：isAmalgamation_restrict
 {R₁ R₂ : Presieve X} (h : R₁ <= R₂) (x : FamilyOfElements P R₂) (t : P.obj (op 
X)) (ht : x.IsAmalgamation t) : (x.re…
· 使用定理 `CategoryTheory.Presieve.isAmalgamation_sieveExtend`：isAmalgamation_sieve
Extend {R : Presieve X} (x : FamilyOfElements P R) (t : P.obj (op X)) (ht : x.Is
Amalgamation t) : x.sieveExtend.IsAmalga…

--- 原说明 ---
Every Yoneda-presheaf is a sheaf for the regular topology.
-/
lemma isSheaf_yoneda_obj [Preregular C] (W : C) :
    Presieve.IsSheaf (regularTopology C) (yoneda.obj W) := by
  rw [regularTopology, isSheaf_coverage]
  intro X S ⟨_, hS⟩
  have : S.regular := ⟨_, hS⟩
  obtain ⟨Y, f, rfl, hf⟩ := Presieve.regular.single_epi (R := S)
  have h_colim := isColimitOfEffectiveEpiStruct f hf.effectiveEpi.some
  rw [← Sieve.generateSingleton_eq, ← Presieve.ofArrows_pUnit] at h_colim
  intro x hx
  let x_ext := Presieve.FamilyOfElements.sieveExtend x
  have hx_ext := Presieve.FamilyOfElements.Compatible.sieveExtend hx
  let S := Sieve.generate (Presieve.ofArrows (fun () ↦ Y) (fun () ↦ f))
  obtain ⟨t, t_amalg, t_uniq⟩ :=
    (Sieve.forallYonedaIsSheaf_iff_colimit S).mpr ⟨h_colim⟩ W x_ext hx_ext
  refine ⟨t, ?_, ?_⟩
  · convert!
    Presieve.isAmalgamation_restrict
      (Sieve.le_generate (Presieve.ofArrows (fun () ↦ Y) (fun () ↦ f))) _ _ t_amalg
    exact (Presieve.restrict_extend hx).symm
  · exact fun y hy ↦ t_uniq y <| Presieve.isAmalgamation_sieveExtend x y hy

/-- The regular topology on any preregular category is subcanonical. -/
/-
**CategoryTheory.regularTopology.subcanonical** 是 Mathlib 中的一个实例，位于命名空间 `Categor
yTheory.regularTopology`。
形式化陈述：subcanonical [Preregular C] : (regularTopology C).Subcanonical
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrothendieckTopology.Subcanonical.of_isSheaf_yoneda_obj`：
of_isSheaf_yoneda_obj (J : GrothendieckTopology C) (h : forall X, Presieve.IsShe
af J (yoneda.obj X)) : Subcanonical J where le_canonical
· 使用引理 `CategoryTheory.regularTopology.isSheaf_yoneda_obj`：isSheaf_yoneda_obj [P
reregular C] (W : C) : Presieve.IsSheaf (regularTopology C) (yoneda.obj W)

--- 原说明 ---
The regular topology on any preregular category is subcanonical.
-/
instance subcanonical [Preregular C] : (regularTopology C).Subcanonical :=
  GrothendieckTopology.Subcanonical.of_isSheaf_yoneda_obj _ isSheaf_yoneda_obj

end regularTopology

end CategoryTheory

