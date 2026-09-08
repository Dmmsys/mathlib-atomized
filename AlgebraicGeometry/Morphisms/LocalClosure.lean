/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Basic

/-!
# Local closure of morphism properties

We define the source local closure of a property `P` w.r.t. a morphism property `W` and show it
inherits stability properties from `P`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MorphismProperty

namespace AlgebraicGeometry

variable (W : MorphismProperty Scheme.{u})

/-- The source (Zariski-)local closure of `P` is satisfied if there exists
an open cover of the source on which `P` is satisfied. -/
/-
**AlgebraicGeometry.sourceLocalClosure** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeome
try`。
形式化陈述：sourceLocalClosure (P : MorphismProperty Scheme.{u}) : MorphismProperty Sc
heme.{u}
参数：P : MorphismProperty Scheme.{u}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The source (Zariski-)local closure of `P` is satisfied if there exists
an open cover of the source on which `P` is satisfied.
-/
def sourceLocalClosure (P : MorphismProperty Scheme.{u}) : MorphismProperty Scheme.{u} :=
  fun X _ f ↦ ∃ (𝒰 : Scheme.Cover.{u} (Scheme.precoverage W) X), ∀ (i : 𝒰.I₀), P (𝒰.f i ≫ f)

namespace sourceLocalClosure

variable {W} {P Q : MorphismProperty Scheme.{u}} {X Y : Scheme.{u}}

/-- A choice of open cover on which `P` is satisfied if `f` satisfies the source local closure
of `P`. -/
/-
**AlgebraicGeometry.sourceLocalClosure.cover** 是 Mathlib 中的一个定义，位于命名空间 `Algebrai
cGeometry.sourceLocalClosure`。
形式化陈述：cover {f : X ⟶ Y} (hf : sourceLocalClosure W P f) : Scheme.Cover.{u} (Sche
me.precoverage W) X
参数：hf : sourceLocalClosure W P f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A choice of open cover on which `P` is satisfied if `f` satisfies the source loc
al closure
of `P`.
-/
noncomputable def cover {f : X ⟶ Y} (hf : sourceLocalClosure W P f) :
    Scheme.Cover.{u} (Scheme.precoverage W) X :=
  hf.choose
/-
**AlgebraicGeometry.sourceLocalClosure.property_coverMap_comp** 是 Mathlib 中的一个引理
，位于命名空间 `AlgebraicGeometry.sourceLocalClosure`。
形式化陈述：property_coverMap_comp {f : X ⟶ Y} (hf : sourceLocalClosure W P f) (i : hf
.cover.I₀) : P (hf.cover.f i ≫ f)
参数：hf : sourceLocalClosure W P f；i : hf.cover.I₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
lemma property_coverMap_comp {f : X ⟶ Y} (hf : sourceLocalClosure W P f) (i : hf.cover.I₀) :
    P (hf.cover.f i ≫ f) :=
  hf.choose_spec i

set_option backward.defeqAttrib.useBackward true in
/-
**AlgebraicGeometry.sourceLocalClosure.le** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGe
ometry.sourceLocalClosure`。
形式化陈述：le [W.ContainsIdentities] [W.RespectsIso] : P <= sourceLocalClosure W P
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
lemma le [W.ContainsIdentities] [W.RespectsIso] : P ≤ sourceLocalClosure W P :=
  fun X Y f hf ↦ ⟨X.coverOfIsIso (𝟙 X), by simpa⟩
/-
**AlgebraicGeometry.sourceLocalClosure.iff_forall_exists** 是 Mathlib 中的一个引理，位于命名
空间 `AlgebraicGeometry.sourceLocalClosure`。
形式化陈述：iff_forall_exists [P.RespectsIso] {f : X ⟶ Y} : sourceLocalClosure IsOpenI
mmersion P f ↔ forall (x : X), exists (U : X.Opens), x in U ∧ P (U.ι ≫ f)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.instJointlySurjectivePrecoverage`：∀ {P : Catego
ryTheory.MorphismProperty AlgebraicGeometry.Scheme},   AlgebraicGeometry.Scheme.
JointlySurjective (AlgebraicGeometry.Scheme.pre…
· 使用定理 `AlgebraicGeometry.Scheme.instIsOpenImmersionF`：∀ {X : AlgebraicGeometry.
Scheme} (𝒰 : X.OpenCover) (i : 𝒰.I₀), AlgebraicGeometry.IsOpenImmersion (𝒰.f i)
· 使用定理 `AlgebraicGeometry.Scheme.Cover.covers`：∀ {K : CategoryTheory.Precoverage
 AlgebraicGeometry.Scheme} {X : AlgebraicGeometry.Scheme}   [inst : AlgebraicGeo
metry.Scheme.JointlySurject…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.Scheme.Hom.isoOpensRange_inv_comp`：∀ {X Y : AlgebraicG
eometry.Scheme} (f : X ⟶ Y) [inst : AlgebraicGeometry.IsOpenImmersion f],   Cate
goryTheory.CategoryStruct.comp (Algebraic…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.MorphismProperty.cancel_left_of_respectsIso`：cancel_left_
of_respectsIso (P : MorphismProperty C) [hP : RespectsIso P] {X Y Z : C} (f : X 
⟶ Y) (g : Y ⟶ Z) [IsIso f] : P (f ≫ g) ↔ P g
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `AlgebraicGeometry.Scheme.Opens.instIsOpenImmersionι`：∀ {X : AlgebraicGeo
metry.Scheme} (U : X.Opens), AlgebraicGeometry.IsOpenImmersion U.ι
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
lemma iff_forall_exists [P.RespectsIso] {f : X ⟶ Y} :
    sourceLocalClosure IsOpenImmersion P f ↔ ∀ (x : X), ∃ (U : X.Opens), x ∈ U ∧ P (U.ι ≫ f) := by
  refine ⟨fun ⟨𝒰, hf⟩ x ↦ ?_, fun H ↦ ?_⟩
  · refine ⟨(𝒰.f (𝒰.idx x)).opensRange, 𝒰.covers x, ?_⟩
    rw [← Scheme.Hom.isoOpensRange_inv_comp, Category.assoc, P.cancel_left_of_respectsIso]
    apply hf
  · choose U hx hf using H
    exact ⟨.mkOfCovers X (fun x ↦ U x) (fun _ ↦ (U _).ι) (fun x ↦ ⟨x, ⟨x, hx x⟩, rfl⟩)
      fun _ ↦ inferInstance, hf⟩

variable [W.IsStableUnderBaseChange] [Scheme.IsJointlySurjectivePreserving W]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**AlgebraicGeometry.sourceLocalClosure.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeom
etry.sourceLocalClosure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [P.RespectsLeft Q] [Q.IsStableUnderBaseChange] :
    (sourceLocalClosure W P).RespectsLeft Q := by
  refine ⟨fun {X Y} Z f hf g ⟨𝒰, hg⟩ ↦ ⟨𝒰.pullback₁ f, fun i ↦ ?_⟩⟩
  simpa [pullback.condition_assoc] using
    RespectsLeft.precomp (Q := Q) _ (Q.pullback_snd _ _ hf) _ (hg i)
/-
**AlgebraicGeometry.sourceLocalClosure.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeom
etry.sourceLocalClosure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [P.RespectsRight Q] : (sourceLocalClosure W P).RespectsRight Q := by
  refine ⟨fun {X Y} Z f hf g ⟨𝒰, hg⟩ ↦ ⟨𝒰, fun i ↦ ?_⟩⟩
  rw [← Category.assoc]
  exact RespectsRight.postcomp _ hf _ (hg i)
/-
**AlgebraicGeometry.sourceLocalClosure.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeom
etry.sourceLocalClosure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [P.RespectsIso] : (sourceLocalClosure W P).RespectsIso where

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**AlgebraicGeometry.sourceLocalClosure.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeom
etry.sourceLocalClosure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [P.RespectsIso] [P.RespectsLeft @IsOpenImmersion] :
    IsZariskiLocalAtSource (sourceLocalClosure IsOpenImmersion P) := by
  refine .mk_of_iff_of_zeroHypercover fun f 𝒰 ↦ ?_
  refine ⟨fun ⟨𝒱, h⟩ ↦ fun i ↦ ⟨𝒱.pullback₁ (𝒰.f i), fun j ↦ ?_⟩, fun h ↦ ?_⟩
  · simpa [pullback.condition_assoc] using
      RespectsLeft.precomp (Q := @IsOpenImmersion) _ inferInstance _ (h j)
  · choose 𝒱 h𝒱 using h
    exact ⟨(Scheme.Cover.ulift 𝒰).bind (fun i ↦ Scheme.Cover.ulift (𝒱 _)), fun i ↦ h𝒱 _ _⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**AlgebraicGeometry.sourceLocalClosure.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeom
etry.sourceLocalClosure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [P.IsStableUnderBaseChange] : (sourceLocalClosure W P).IsStableUnderBaseChange := by
  refine .mk' fun X Y S f g _ ⟨𝒰, hg⟩ ↦ ⟨𝒰.pullback₁ (pullback.snd f g), fun i ↦ ?_⟩
  simpa [← pullbackLeftPullbackSndIso_hom_fst, P.cancel_left_of_respectsIso] using
    P.pullback_fst _ _ (hg i)
/-
**AlgebraicGeometry.sourceLocalClosure.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeom
etry.sourceLocalClosure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [W.ContainsIdentities] [P.ContainsIdentities] :
    (sourceLocalClosure W P).ContainsIdentities :=
  ⟨fun X ↦ ⟨X.coverOfIsIso (𝟙 X), fun _ ↦ P.id_mem _⟩⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**AlgebraicGeometry.sourceLocalClosure.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeom
etry.sourceLocalClosure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [W.IsStableUnderComposition] [P.IsStableUnderBaseChange] [P.IsStableUnderComposition] :
    (sourceLocalClosure W P).IsStableUnderComposition := by
  refine ⟨fun {X Y Z} f g ⟨𝒰, hf⟩ ⟨𝒱, hg⟩ ↦ ?_⟩
  refine ⟨𝒰.bind fun i ↦ (𝒱.pullback₁ (𝒰.f i ≫ f)), fun ⟨l, r⟩ ↦ ?_⟩
  simpa [← pullbackRightPullbackFstIso_inv_snd_fst_assoc, pullback.condition_assoc] using
    P.comp_mem _ _ (P.pullback_snd _ _ (hf _)) (hg r)
/-
**AlgebraicGeometry.sourceLocalClosure.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeom
etry.sourceLocalClosure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [W.IsMultiplicative] [P.IsStableUnderBaseChange] [P.IsMultiplicative] :
    (sourceLocalClosure W P).IsMultiplicative where

end sourceLocalClosure

end AlgebraicGeometry

