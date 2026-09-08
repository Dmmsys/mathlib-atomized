/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timo Kraenzle, Judith Ludwig, Bryan Wang, Christian Merten,
  Yannis Monbru, Alireza Shavali, Chenyi Yang
-/
module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Fiber

/-!
# Geometrically-`P` schemes over a field

In this file we define the basic interface for properties like geometrically reduced,
geometrically irreducible, geometrically connected etc. In this file
we treat an abstract property of schemes `P` and derive the general properties that are
shared by all of these variants.

A morphism of schemes `f : X ⟶ Y` is geometrically `P` if for any field `K` and
morphism `Spec K ⟶ Y`, the base change `X ×[Y] Spec K` satisfies `P`.

## Main definitions and results

- `AlgebraicGeometry.geometrically`: The morphism property of geometrically-`P` morphisms
- `AlgebraicGeometry.geometrically_iff_forall_fiberToSpecResidueField`: `f : X ⟶ Y` is
  geometrically-`P` if and only if for every `y : Y`, the fiber `f ⁻¹ {y}` is geometrically-`P`
  over `Spec κ(y)`.

## Notes

This contribution was created as part of the Formalising Algebraic Geometry workshop 2025 in
Heidelberg.
-/

@[expose] public section

universe u

open CategoryTheory Limits CommRingCat

namespace AlgebraicGeometry

/-- A morphism of schemes `f : X ⟶ Y` is geometrically `P` if for any field `K` and
morphism `Spec K ⟶ Y`, the base change `X ×[Y] Spec K` satisfies `P`. -/
/-
**AlgebraicGeometry.geometrically** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeometry`。
形式化陈述：geometrically (P : ObjectProperty Scheme.{u}) : MorphismProperty Scheme.{u
}
参数：P : ObjectProperty Scheme.{u}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism of schemes `f : X ⟶ Y` is geometrically `P` if for any field `K` and
morphism `Spec K ⟶ Y`, the base change `X ×[Y] Spec K` satisfies `P`.
-/
def geometrically (P : ObjectProperty Scheme.{u}) : MorphismProperty Scheme.{u} :=
  fun X Y f ↦ ∀ ⦃K : Type u⦄ [Field K] (y : Spec (.of K) ⟶ Y)
    ⦃Z : Scheme.{u}⦄ (fst : Z ⟶ X) (snd : Z ⟶ Spec (.of K)),
    IsPullback fst snd f y → P Z
/-
**AlgebraicGeometry.geometrically_eq_universally** 是 Mathlib 中的一个引理，位于命名空间 `Alge
braicGeometry`。
形式化陈述：geometrically_eq_universally (P : ObjectProperty Scheme.{u}) : geometrical
ly P = .universally fun X Y _ => IsIntegral Y -> Subsingleton Y -> P X
参数：P : ObjectProperty Scheme.{u}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.ext`：ext (W W' : MorphismProperty C) (h 
: forall ⦃X Y : C⦄ (f : X ⟶ Y), W f ↔ W' f) : W = W'
· 使用引理 `AlgebraicGeometry.isField_of_isIntegral_of_subsingleton`：isField_of_isIn
tegral_of_subsingleton (X : Scheme.{u}) [IsIntegral X] [Subsingleton X] : IsFiel
d Γ(X, ⊤)
· 使用定理 `AlgebraicGeometry.instIsAffineOfFiniteOfDiscreteTopologyCarrierCarrierCo
mmRingCat`：∀ {X : AlgebraicGeometry.Scheme} [Finite ↥X] [DiscreteTopology ↥X], A
lgebraicGeometry.IsAffine X
· 使用定理 `Finite.of_subsingleton`：Finite.of_subsingleton [Subsingleton α] (s : Set
 α) : s.Finite
· 使用定理 `Subsingleton.discreteTopology`：∀ {α : Type u} [t : TopologicalSpace α] [
Subsingleton α], DiscreteTopology α
· 使用引理 `CategoryTheory.IsPullback.of_iso`：of_iso (h : IsPullback fst snd f g) {P
' X' Y' Z' : C} {fst' : P' ⟶ X'} {snd' : P' ⟶ Y'} {f' : X' ⟶ Z'} {g' : Y' ⟶ Z'} 
(e₁ : P ≅ P') (e₂ : X …
· 使用定理 `CategoryTheory.IsPullback.flip`：flip (h : IsPullback fst snd f g) : IsPu
llback snd fst g f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `AlgebraicGeometry.instIsIntegralSpecOfIsDomainCarrier`：∀ {R : CommRingCa
t} [IsDomain ↑R], AlgebraicGeometry.IsIntegral (AlgebraicGeometry.Spec R)
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
-/
lemma geometrically_eq_universally (P : ObjectProperty Scheme.{u}) :
    geometrically P = .universally fun X Y _ ↦ IsIntegral Y → Subsingleton Y → P X := by
  ext X Y f
  refine ⟨fun hf Z W snd q fst h _ _ ↦ ?_, fun hf aK y Z W fst snd h ↦ ?_⟩
  · let := (isField_of_isIntegral_of_subsingleton W).toField
    apply hf (W.isoSpec.inv ≫ q) snd (fst ≫ W.isoSpec.hom)
    apply h.flip.of_iso (.refl _) (.refl _) W.isoSpec (.refl _) <;> simp
  · exact hf _ _ _ h.flip inferInstance inferInstance

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.geometrically_inf** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeomet
ry`。
形式化陈述：geometrically_inf (P Q : ObjectProperty Scheme.{u}) : geometrically (P ⊓ Q
) = geometrically P ⊓ geometrically Q
参数：P Q : ObjectProperty Scheme.{u}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.geometrically_eq_universally`：geometrically_eq_univers
ally (P : ObjectProperty Scheme.{u}) : geometrically P = .universally fun X Y _ 
=> IsIntegral Y -> Subsingleton Y ->…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `CategoryTheory.MorphismProperty.ext`：ext (W W' : MorphismProperty C) (h 
: forall ⦃X Y : C⦄ (f : X ⟶ Y), W f ↔ W' f) : W = W'
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma geometrically_inf (P Q : ObjectProperty Scheme.{u}) :
    geometrically (P ⊓ Q) = geometrically P ⊓ geometrically Q := by
  simp only [geometrically_eq_universally, ← MorphismProperty.universally_inf]
  congr with X Y f
  exact ⟨fun H ↦ ⟨(H · · |>.1), (H · · |>.2)⟩, fun H a b ↦ ⟨H.1 a b, H.2 a b⟩⟩

variable (P : ObjectProperty Scheme.{u})

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (geometrically P).IsStableUnderBaseChange := by
  rw [geometrically_eq_universally]
  infer_instance
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [P.IsClosedUnderIsomorphisms] : IsZariskiLocalAtTarget (geometrically P) := by
  rw [geometrically_eq_universally]
  refine universally_isZariskiLocalAtTarget _ fun {X} Y f ι U hU H _ _ ↦ ?_
  obtain ⟨y⟩ := (inferInstance : Nonempty Y)
  obtain ⟨i, hy⟩ := hU.exists_mem y
  have heq : U i = ⊤ := eq_top_iff.mpr fun z _ ↦ by rwa [Subsingleton.elim z y]
  let e : ↑(U i) ≅ Y := Y.isoOfEq heq ≪≫ Y.topIso
  let e' : ↑(f ⁻¹ᵁ U i) ≅ X := X.isoOfEq (by simp [heq]) ≪≫ X.topIso
  exact P.prop_of_iso e' <| H i (.of_isIso e.inv) (e.hom.homeomorph.subsingleton_congr.mpr ‹_›)

section geometrically

variable {P : ObjectProperty Scheme.{u}} {X Y : Scheme.{u}} {f : X ⟶ Y}

/-
**AlgebraicGeometry.pullback_of_geometrically** 是 Mathlib 中的一个引理，位于命名空间 `Algebra
icGeometry`。
形式化陈述：pullback_of_geometrically (hf : geometrically P f) (K : Type u) [Field K] 
(y : Spec (.of K) ⟶ Y) : P (Limits.pullback f y)
参数：hf : geometrically P f；K : Type u；y : Spec (.of K) ⟶ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `CategoryTheory.IsPullback.of_hasPullback`：of_hasPullback (f : X ⟶ Z) (g 
: Y ⟶ Z) [HasPullback f g] : IsPullback (pullback.fst f g) (pullback.snd f g) f 
g
-/
lemma pullback_of_geometrically (hf : geometrically P f) (K : Type u) [Field K]
    (y : Spec (.of K) ⟶ Y) : P (Limits.pullback f y) :=
  hf _ _ _ (.of_hasPullback _ _)
/-
**AlgebraicGeometry.pullback_of_geometrically'** 是 Mathlib 中的一个引理，位于命名空间 `Algebr
aicGeometry`。
形式化陈述：pullback_of_geometrically' (hf : geometrically P f) (K : Type u) [Field K]
 (y : Spec (.of K) ⟶ Y) : P (Limits.pullback y f)
参数：hf : geometrically P f；K : Type u；y : Spec (.of K) ⟶ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `CategoryTheory.IsPullback.flip`：flip (h : IsPullback fst snd f g) : IsPu
llback snd fst g f
· 使用定理 `CategoryTheory.IsPullback.of_hasPullback`：of_hasPullback (f : X ⟶ Z) (g 
: Y ⟶ Z) [HasPullback f g] : IsPullback (pullback.fst f g) (pullback.snd f g) f 
g
-/
lemma pullback_of_geometrically' (hf : geometrically P f) (K : Type u) [Field K]
    (y : Spec (.of K) ⟶ Y) : P (Limits.pullback y f) :=
  hf _ _ _ (.flip <| .of_hasPullback _ _)
/-
**AlgebraicGeometry.geometrically_iff_of_isClosedUnderIsomorphisms** 是 Mathlib 中
的一个引理，位于命名空间 `AlgebraicGeometry`。
形式化陈述：geometrically_iff_of_isClosedUnderIsomorphisms [P.IsClosedUnderIsomorphism
s] : geometrically P f ↔ forall (K : Type u) [Field K] (y : Spec (.of K) ⟶ Y), P
 (Limits.pullback f y)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用引理 `AlgebraicGeometry.pullback_of_geometrically`：pullback_of_geometrically (
hf : geometrically P f) (K : Type u) [Field K] (y : Spec (.of K) ⟶ Y) : P (Limit
s.pullback f y)
· 使用引理 `CategoryTheory.ObjectProperty.prop_of_iso`：prop_of_iso [IsClosedUnderIso
morphisms P] {X Y : C} (e : X ≅ Y) (hX : P X) : P Y
-/
lemma geometrically_iff_of_isClosedUnderIsomorphisms [P.IsClosedUnderIsomorphisms] :
    geometrically P f ↔
      ∀ (K : Type u) [Field K] (y : Spec (.of K) ⟶ Y), P (Limits.pullback f y) := by
  refine ⟨fun h K _ _ ↦ pullback_of_geometrically h _ _, fun H K _ _ Y fst snd h ↦ ?_⟩
  exact P.prop_of_iso h.isoPullback.symm (H _ _)
/-
**AlgebraicGeometry.fiber_of_geometrically** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicG
eometry`。
形式化陈述：fiber_of_geometrically (hf : geometrically P f) (y : Y) : P (f.fiber y)
参数：hf : geometrically P f；y : Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.pullback_of_geometrically`：pullback_of_geometrically (
hf : geometrically P f) (K : Type u) [Field K] (y : Spec (.of K) ⟶ Y) : P (Limit
s.pullback f y)
-/
lemma fiber_of_geometrically (hf : geometrically P f) (y : Y) : P (f.fiber y) :=
  pullback_of_geometrically hf _ _

set_option backward.isDefEq.respectTransparency false in
/-- `P` holds geometrically for `f` if and only if all fibers are geometrically `P`. -/
/-
**AlgebraicGeometry.geometrically_iff_forall_fiberToSpecResidueField** 是 Mathlib
 中的一个引理，位于命名空间 `AlgebraicGeometry`。
形式化陈述：geometrically_iff_forall_fiberToSpecResidueField : geometrically P f ↔ for
all (y : Y), geometrically P (f.fiberToSpecResidueField y)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.pullback_snd`：pullback_snd {X Y S : C} (
f : X ⟶ S) (g : Y ⟶ S) [HasPullback f g] [P.IsStableUnderBaseChangeAlong g] (H :
 P f) : P (pullback.snd f g)
· 使用定理 `CategoryTheory.MorphismProperty.instIsStableUnderBaseChangeAlongOfIsStab
leUnderBaseChange`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (P :
 CategoryTheory.MorphismProperty C)   [P.IsStableUnderBaseChange] {X Y : C} (f …
· 使用定理 `AlgebraicGeometry.instIsStableUnderBaseChangeSchemeGeometrically`：∀ (P :
 CategoryTheory.ObjectProperty AlgebraicGeometry.Scheme),   (AlgebraicGeometry.g
eometrically P).IsStableUnderBaseChange
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.CommSq.w`：∀ {C : Type u_1} [inst : CategoryTheory.Categor
y.{v_1, u_1} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z}   {i : Y ⟶ Z},
   CategoryTh…
· 使用定理 `CategoryTheory.IsPullback.toCommSq`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {P X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z}   
{g : Y ⟶ Z}, CategoryThe…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.IsPullback.flip`：flip (h : IsPullback fst snd f g) : IsPu
llback snd fst g f
· 使用定理 `CategoryTheory.IsPullback.of_bot`：of_bot {X₁₁ X₁₂ X₂₁ X₂₂ X₃₁ X₃₂ : C} {
h₁₁ : X₁₁ ⟶ X₁₂} {h₂₁ : X₂₁ ⟶ X₂₂} {h₃₁ : X₃₁ ⟶ X₃₂} {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁
₂ ⟶ X₂₂} {v₂₁ : X₂₁ ⟶ …
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PullbackCone.mk_π_app`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {W : C} (fst :
 W ⟶ X)   (snd : W ⟶ Y)   (eq :  …
· 使用定理 `CategoryTheory.IsPullback.of_hasPullback`：of_hasPullback (f : X ⟶ Z) (g 
: Y ⟶ Z) [HasPullback f g] : IsPullback (pullback.fst f g) (pullback.snd f g) f 
g

--- 原说明 ---
`P` holds geometrically for `f` if and only if all fibers are geometrically `P`.
-/
lemma geometrically_iff_forall_fiberToSpecResidueField :
    geometrically P f ↔ ∀ (y : Y), geometrically P (f.fiberToSpecResidueField y) := by
  refine ⟨fun hf y ↦ (geometrically P).pullback_snd _ _ hf, fun H ↦ ?_⟩
  intro K _ y Z fst snd h
  obtain ⟨⟨y, φ⟩, rfl⟩ := (Scheme.SpecToEquivOfField _ _).symm.surjective y
  let p : Z ⟶ f.fiber y :=
    pullback.lift fst (snd ≫ Spec.map φ) (by simp [h.w, Scheme.SpecToEquivOfField])
  apply H y (Spec.map φ) p snd
  simp only [Scheme.SpecToEquivOfField, Equiv.coe_fn_symm_mk] at h
  refine .flip (.of_bot (.flip ?_) ?_ (IsPullback.of_hasPullback f (Y.fromSpecResidueField y)).flip)
  · convert! h
    simp [p]
  · simp [p, Scheme.Hom.fiberToSpecResidueField]

/-- This holds in particular if `Y = Spec K`. -/
/-
**AlgebraicGeometry.self_of_isIntegral_of_geometrically** 是 Mathlib 中的一个引理，位于命名空
间 `AlgebraicGeometry`。
形式化陈述：self_of_isIntegral_of_geometrically [IsIntegral Y] [Subsingleton Y] (hf : 
geometrically P f) : P X
参数：hf : geometrically P f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.universally_le`：universally_le (P : Morp
hismProperty C) : P.universally <= P
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.geometrically_eq_universally`：geometrically_eq_univers
ally (P : ObjectProperty Scheme.{u}) : geometrically P = .universally fun X Y _ 
=> IsIntegral Y -> Subsingleton Y ->…

--- 原说明 ---
This holds in particular if `Y = Spec K`.
-/
lemma self_of_isIntegral_of_geometrically [IsIntegral Y] [Subsingleton Y] (hf : geometrically P f) :
    P X := by
  rw [geometrically_eq_universally] at hf
  exact MorphismProperty.universally_le _ _ hf ‹_› ‹_›

variable {P : ObjectProperty Scheme.{u}} {R : Type u} [CommRing R] {f : X ⟶ Spec (.of R)}
/-
**AlgebraicGeometry.geometrically_iff_of_commRing** 是 Mathlib 中的一个引理，位于命名空间 `Alg
ebraicGeometry`。
形式化陈述：geometrically_iff_of_commRing : geometrically P f ↔ forall ⦃K : Type u⦄ [F
ield K] [Algebra R K] ⦃Y : Scheme.{u}⦄ (fst : Y ⟶ X) (snd : Y ⟶ Spec (.of K)), I
sPullback fst snd f (Spec.map <| ofHom (algebraMap R K)) -> P Y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Spec.map_surjective`：∀ {R S : CommRingCat}, Function.S
urjective AlgebraicGeometry.Spec.map
-/
lemma geometrically_iff_of_commRing :
    geometrically P f ↔ ∀ ⦃K : Type u⦄ [Field K] [Algebra R K] ⦃Y : Scheme.{u}⦄ (fst : Y ⟶ X)
      (snd : Y ⟶ Spec (.of K)), IsPullback fst snd f (Spec.map <| ofHom (algebraMap R K)) →
      P Y := by
  refine ⟨fun hs K _ _ Z fst snd h ↦ hs _ _ _ h, fun H K _ y Z fst snd h ↦ ?_⟩
  obtain ⟨φ, rfl⟩ := Spec.map_surjective y
  algebraize [φ.hom]
  exact H fst snd h
/-
**AlgebraicGeometry.geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms**
 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry`。
形式化陈述：geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms [P.IsClosedUnde
rIsomorphisms] : geometrically P f ↔ forall (K : Type u) [Field K] [Algebra R K]
, P (Limits.pullback f (Spec.map <| ofHom <| algebraMap R K))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用引理 `AlgebraicGeometry.pullback_of_geometrically`：pullback_of_geometrically (
hf : geometrically P f) (K : Type u) [Field K] (y : Spec (.of K) ⟶ Y) : P (Limit
s.pullback f y)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.geometrically_iff_of_isClosedUnderIsomorphisms`：geomet
rically_iff_of_isClosedUnderIsomorphisms [P.IsClosedUnderIsomorphisms] : geometr
ically P f ↔ forall (K : Type u) [Field K] (y : Spec (…
· 使用定理 `AlgebraicGeometry.Spec.map_surjective`：∀ {R S : CommRingCat}, Function.S
urjective AlgebraicGeometry.Spec.map
-/
lemma geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms [P.IsClosedUnderIsomorphisms] :
    geometrically P f ↔ ∀ (K : Type u) [Field K] [Algebra R K],
      P (Limits.pullback f (Spec.map <| ofHom <| algebraMap R K)) := by
  refine ⟨fun hf K _ _ ↦ pullback_of_geometrically hf _ _, fun H ↦ ?_⟩
  rw [geometrically_iff_of_isClosedUnderIsomorphisms]
  intro K _ y
  obtain ⟨φ, rfl⟩ := Spec.map_surjective y
  algebraize [φ.hom]
  exact H K

end geometrically

end AlgebraicGeometry

