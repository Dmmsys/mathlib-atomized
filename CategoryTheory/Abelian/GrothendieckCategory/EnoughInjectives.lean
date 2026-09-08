/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Abelian.CommSq
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.ColimCoyoneda
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Monomorphisms
public import Mathlib.CategoryTheory.Preadditive.Injective.LiftingProperties
public import Mathlib.CategoryTheory.SmallObject.Basic
public import Mathlib.CategoryTheory.Subobject.HasCardinalLT
public import Mathlib.Order.TransfiniteIteration

/-!
# Grothendieck abelian categories have enough injectives

Let `C` be a Grothendieck abelian category. In this file, we formalize
the theorem by Grothendieck that `C` has enough injectives.

We recall that injective objects can be characterized in terms of
lifting properties (see the file `Preadditive.Injective.LiftingProperties`):
an object `I : C` is injective iff the morphism `I ⟶ 0` has the right lifting
property with respect to all monomorphisms.

The main technical lemma in this file is the lemma
`generatingMonomorphisms_rlp` which states that
if `G` is a generator of `C`, then a morphism `X ⟶ Y` has the right
lifting property with respect to the inclusions of subobjects of `G`
iff it has the right lifting property with respect to all
monomorphisms. Then, we can apply the small object argument
to the family of morphisms `generatingMonomorphisms G`
which consists of the inclusions of subobjects of `G`. When it is
applied to the morphism `X ⟶ 0`, the factorization given by the
small object is a factorization `X ⟶ I ⟶ 0` where `I` is
injective (because `I ⟶ 0` has the expected right lifting properties),
and `X ⟶ I` is a monomorphism because it is a transfinite composition
of monomorphisms (this uses the axiom AB5).

The proof of the technical lemma `generatingMonomorphisms_rlp` that
was formalized is not exactly the same as in the mathematical literature.
Assume that `p : X ⟶ Y` has the lifting property with respect to
monomorphisms in the family `generatingMonomorphisms G`.
We would like to show that `p` has the right lifting property with
respect to any monomorphism `i : A ⟶ B`. In various sources,
given a commutative square with `i` on the left and `p` on the right,
the ordered set of subobjects `A'` of `B` containing `A` equipped
with a lifting `A' ⟶ X` is introduced. The existence of a lifting `B ⟶ X`
is usually obtained by applying Zorn's lemma in this situation.
Here, we split the argument into two separate facts:
* any monomorphism `A ⟶ B` is a transfinite composition of pushouts of monomorphisms in
  `generatingMonomorphisms G` (see `generatingMonomorphisms.exists_transfiniteCompositionOfShape`);
* the class of morphisms that have the left lifting property with respect to `p` is stable under
  transfinite composition (see the file `SmallObject.TransfiniteCompositionLifting`).

## References

- [Alexander Grothendieck, *Sur quelques points d'algèbre homologique*][grothendieck-1957]

-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Category Limits ZeroObject

variable {C : Type u} [Category.{v} C]

namespace IsGrothendieckAbelian

/-- Given an object `G : C`, this is the family of morphisms in `C`
given by the inclusions of all subobjects of `G`. If `G` is a separator,
and `C` is a Grothendieck abelian category, then any monomorphism in `C`
is a transfinite composition of pushouts of monomorphisms in this family
(see `generatingMonomorphisms.exists_transfiniteCompositionOfShape`). -/
/-
**CategoryTheory.IsGrothendieckAbelian.generatingMonomorphisms** 是 Mathlib 中的一个定
义，位于命名空间 `CategoryTheory.IsGrothendieckAbelian`。
形式化陈述：generatingMonomorphisms (G : C) : MorphismProperty C
参数：G : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an object `G : C`, this is the family of morphisms in `C`
given by the inclusions of all subobjects of `G`. If `G` is a separator,
and `C` is a Grothendieck abelian category, then any monomorphism in `C`
is a transfinite composition of pushouts of monomorphisms in this family
(see `generatingMonomorphisms.exists_transfiniteCompositionOfShape`).
-/
def generatingMonomorphisms (G : C) : MorphismProperty C :=
  MorphismProperty.ofHoms (fun (X : Subobject G) ↦ X.arrow)
/-
**CategoryTheory.IsGrothendieckAbelian.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheor
y.IsGrothendieckAbelian`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (G : C) [Small.{w} (Subobject G)] :
    MorphismProperty.IsSmall.{w} (generatingMonomorphisms G) := by
  dsimp [generatingMonomorphisms]
  infer_instance
/-
**CategoryTheory.IsGrothendieckAbelian.generatingMonomorphisms_le_monomorphisms*
* 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.IsGrothendieckAbelian`。
形式化陈述：generatingMonomorphisms_le_monomorphisms (G : C) : generatingMonomorphisms
 G <= MorphismProperty.monomorphisms C
参数：G : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
lemma generatingMonomorphisms_le_monomorphisms (G : C) :
    generatingMonomorphisms G ≤ MorphismProperty.monomorphisms C := by
  rintro _ _ _ ⟨X⟩
  exact inferInstanceAs (Mono _)

variable (G : C)
/-
**CategoryTheory.IsGrothendieckAbelian.isomorphisms_le_pushouts_generatingMonomo
rphisms** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.IsGrothendieckAbelian`。
形式化陈述：isomorphisms_le_pushouts_generatingMonomorphisms [HasZeroMorphisms C] : Mo
rphismProperty.isomorphisms C <= (generatingMonomorphisms G).pushouts
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.isomorphisms_le_pushouts`：isomorphisms_l
e_pushouts (h : forall (X : C), exists (A B : C) (p : A ⟶ B) (_ : P p) (_ : B ⟶ 
X), IsIso p) : isomorphisms C <= P.pushouts
-/
lemma isomorphisms_le_pushouts_generatingMonomorphisms [HasZeroMorphisms C] :
    MorphismProperty.isomorphisms C ≤ (generatingMonomorphisms G).pushouts :=
  MorphismProperty.isomorphisms_le_pushouts _
    (fun _ ↦ ⟨_, _, _, ⟨⊤⟩, 0, inferInstance⟩)

variable [Abelian C]

namespace generatingMonomorphisms

variable {G} (hG : IsSeparator G)

include hG

set_option backward.isDefEq.respectTransparency false in
/-- If `p : X ⟶ Y` is a monomorphism that is not an isomorphism, there exists
a subobject `X'` of `Y` containing `X` (but different from `X`) such that
the inclusion `X ⟶ X'` is a pushout of a monomorphism in the family
`generatingMonomorphisms G`. -/
/-
**CategoryTheory.IsGrothendieckAbelian.generatingMonomorphisms.exists_pushouts**
 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.IsGrothendieckAbelian.generatingMonomor
phisms`。
形式化陈述：exists_pushouts {X Y : C} (p : X ⟶ Y) [Mono p] (hp : ¬ IsIso p) : exists (
X' : C) (i : X ⟶ X') (p' : X' ⟶ Y) (_ : (generatingMonomorphisms G).pushouts i) 
(_ : ¬ IsIso i) (_ : Mono p'), i ≫ p' = p
参数：p : X ⟶ Y；hp : ¬ IsIso p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.ObjectProperty.IsDetecting.isIso_iff_of_mono`：∀ {C : Type
 u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {P : CategoryTheory.ObjectPrope
rty C},   P.IsDetecting →     ∀ {X Y : C} (f : X …
· 使用定理 `CategoryTheory.IsSeparator.isDetector`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} C] [CategoryTheory.Balanced C] {G : C},   CategoryTheory
.IsSeparator G → CategoryTh…
· 使用定理 `CategoryTheory.balanced_of_strongMonoCategory`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] [CategoryTheory.StrongMonoCategory C],   Categor
yTheory.Balanced C
· 使用定理 `CategoryTheory.strongMonoCategory_of_regularMonoCategory`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] [CategoryTheory.IsRegularMonoCateg
ory C],   CategoryTheory.StrongMonoCategory C
· 使用定理 `CategoryTheory.regularMonoCategoryOfNormalMonoCategory`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Limits.HasZ
eroMorphisms C]   [CategoryTheory.IsNormalMo…
· 使用定理 `CategoryTheory.Abelian.toIsNormalMonoCategory`：∀ {C : Type u} {inst : Ca
tegoryTheory.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryThe
ory.IsNormalMonoCategory C
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePullbacks_of_hasFiniteLimits`：∀ (C : 
Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFini
teLimits C],   CategoryTheory.Limits.HasFiniteWidePul…
· 使用定理 `CategoryTheory.Abelian.hasFiniteLimits`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.Has
FiniteLimits C
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePushouts_of_has_finite_limits`：∀ (C :
 Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFin
iteColimits C],   CategoryTheory.Limits.HasFiniteWideP…
· 使用定理 `CategoryTheory.Abelian.hasFiniteColimits`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.H
asFiniteColimits C
· 使用定理 `CategoryTheory.Limits.pullback.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPullback f…
· 使用定理 `CategoryTheory.Limits.pullback.snd_of_mono`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Cat
egoryTheory.Limits.HasPullback f…
· 使用引理 `CategoryTheory.IsPushout.of_iso`：of_iso (h : IsPushout f g inl inr) {Z' 
X' Y' P' : C} {f' : Z' ⟶ X'} {g' : Z' ⟶ Y'} {inl' : X' ⟶ P'} {inr' : Y' ⟶ P'} (e
₁ : Z ≅ Z') (e₂ : X ≅…
· 使用定理 `CategoryTheory.IsPushout.of_hasPushout`：of_hasPushout (f : Z ⟶ X) (g : Z
 ⟶ Y) [HasPushout f g] : IsPushout f g (pushout.inl f g) (pushout.inr f g)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Subobject.underlyingIso_arrow`：underlyingIso_arrow {X Y :
 C} (f : X ⟶ Y) [Mono f] : (underlyingIso f).inv ≫ (Subobject.mk f).arrow = f
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
（共 38 条，此处仅展示前 30 条）

--- 原说明 ---
If `p : X ⟶ Y` is a monomorphism that is not an isomorphism, there exists
a subobject `X'` of `Y` containing `X` (but different from `X`) such that
the inclusion `X ⟶ X'` is a pushout of a monomorphism in the family
`generatingMonomorphisms G`.
-/
lemma exists_pushouts
    {X Y : C} (p : X ⟶ Y) [Mono p] (hp : ¬ IsIso p) :
    ∃ (X' : C) (i : X ⟶ X') (p' : X' ⟶ Y) (_ : (generatingMonomorphisms G).pushouts i)
      (_ : ¬ IsIso i) (_ : Mono p'), i ≫ p' = p := by
  rw [hG.isDetector.isIso_iff_of_mono] at hp
  simp only [ObjectProperty.singleton_iff, Function.Surjective, Functor.flip_obj_map, forall_eq',
    not_forall, not_exists] at hp
  -- `f : G ⟶ Y` is a monomorphism the image of which is not contained in `X`
  obtain ⟨f, hf⟩ := hp
  -- we use the subobject `X'` of `Y` that is generated by the images of `p : X ⟶ Y`
  -- and `f : G ⟶ Y`: this is the pushout of `p` and `f` along their pullback
  refine ⟨pushout (pullback.fst p f) (pullback.snd p f), pushout.inl _ _,
    pushout.desc p f pullback.condition,
    ⟨_, _, _, (Subobject.underlyingIso _).hom ≫ pullback.fst _ _,
    pushout.inr _ _, ⟨Subobject.mk (pullback.snd p f)⟩,
    (IsPushout.of_hasPushout (pullback.fst p f) (pullback.snd p f)).of_iso
      ((Subobject.underlyingIso _).symm) (Iso.refl _) (Iso.refl _)
      (Iso.refl _) (by simp) (by simp) (by simp) (by simp)⟩, ?_, ?_, by simp⟩
  · intro h
    rw [isIso_iff_yoneda_map_bijective] at h
    obtain ⟨a, ha⟩ := (h G).2 (pushout.inr _ _)
    exact hf a (by simpa using ha =≫ pushout.desc p f pullback.condition)
  · exact (IsPushout.of_hasPushout _ _).mono_of_isPullback_of_mono
      (IsPullback.of_hasPullback p f) _ (by simp) (by simp)

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.IsGrothendieckAbelian.generatingMonomorphisms.exists_larger_sub
object** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.IsGrothendieckAbelian.generatin
gMonomorphisms`。
形式化陈述：exists_larger_subobject {X : C} (A : Subobject X) (hA : A != ⊤) : exists (
A' : Subobject X) (h : A < A'), (generatingMonomorphisms G).pushouts (Subobject.
ofLE A A' h.le)
参数：A : Subobject X；hA : A != ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subobject.ind`：∀ {C : Type u₁} [inst : CategoryTheory.Cat
egory.{v₁, u₁} C] {X : C} (p : CategoryTheory.Subobject X → Prop),   (∀ ⦃A : C⦄ 
(f : A ⟶ X) [inst_…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `CategoryTheory.IsGrothendieckAbelian.generatingMonomorphisms.exists_push
outs`：exists_pushouts {X Y : C} (p : X ⟶ Y) [Mono p] (hp : ¬ IsIso p) : exists (
X' : C) (i : X ⟶ X') (p' : X' ⟶ Y) (_ : (generatingMonomorphisms G…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Subobject.mk_lt_mk_of_comm`：mk_lt_mk_of_comm {X A₁ A₂ : C
} {i₁ : A₁ ⟶ X} {i₂ : A₂ ⟶ X} [Mono i₁] [Mono i₂] (f : A₁ ⟶ A₂) (fac : f ≫ i₂ = 
i₁) (hf : ¬ IsIso f) : Subobjec…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.MorphismProperty.arrow_mk_iso_iff`：arrow_mk_iso_iff (P : 
MorphismProperty C) [RespectsIso P] {W X Y Z : C} {f : W ⟶ X} {g : Y ⟶ Z} (e : A
rrow.mk f ≅ Arrow.mk g) : P f ↔ P g
· 使用定理 `CategoryTheory.MorphismProperty.instRespectsIsoPushouts`：∀ {C : Type u} 
[inst : CategoryTheory.Category.{v, u} C] (P : CategoryTheory.MorphismProperty C
), P.pushouts.RespectsIso
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Subobject.underlyingIso_hom_comp_eq_mk`：underlyingIso_hom
_comp_eq_mk {X Y : C} (f : X ⟶ Y) [Mono f] : (underlyingIso f).hom ≫ f = (mk f).
arrow
· 使用定理 `CategoryTheory.Subobject.ofLE_arrow`：ofLE_arrow {B : C} {X Y : Subobject
 B} (h : X <= Y) : ofLE X Y h ≫ Y.arrow = X.arrow
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma exists_larger_subobject {X : C} (A : Subobject X) (hA : A ≠ ⊤) :
    ∃ (A' : Subobject X) (h : A < A'),
      (generatingMonomorphisms G).pushouts (Subobject.ofLE A A' h.le) := by
  induction A using Subobject.ind with | _ f
  obtain ⟨X', i, p', hi, hi', hp', fac⟩ := exists_pushouts hG f
    (by simpa only [Subobject.isIso_iff_mk_eq_top] using hA)
  refine ⟨Subobject.mk p', Subobject.mk_lt_mk_of_comm i fac hi',
    (MorphismProperty.arrow_mk_iso_iff _ ?_).2 hi⟩
  refine Arrow.isoMk (Subobject.underlyingIso f) (Subobject.underlyingIso p') ?_
  dsimp
  simp only [← cancel_mono p', assoc, fac,
    Subobject.underlyingIso_hom_comp_eq_mk, Subobject.ofLE_arrow]

variable {X : C}

open scoped Classical in
/-- Assuming `G : C` is a generator, `X : C`, and `A : Subobject X`,
this is a subobject of `X` which is `⊤` if `A = ⊤`, and otherwise
it is a larger subobject given by the lemma `exists_larger_subobject`.
The inclusion of `A` in `largerSubobject hG A` is a pushout of
a monomorphism in the family `generatingMonomorphisms G`
(see `pushouts_ofLE_le_largerSubobject`). -/
/-
**CategoryTheory.IsGrothendieckAbelian.generatingMonomorphisms.largerSubobject**
 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.IsGrothendieckAbelian.generatingMonomor
phisms`。
形式化陈述：largerSubobject (A : Subobject X) : Subobject X
参数：A : Subobject X。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.IsGrothendieckAbelian.generatingMonomorphisms.exists_larg
er_subobject`：exists_larger_subobject {X : C} (A : Subobject X) (hA : A != ⊤) : 
exists (A' : Subobject X) (h : A < A'), (generatingMonomorphisms G).pushou…

--- 原说明 ---
Assuming `G : C` is a generator, `X : C`, and `A : Subobject X`,
this is a subobject of `X` which is `⊤` if `A = ⊤`, and otherwise
it is a larger subobject given by the lemma `exists_larger_subobject`.
The inclusion of `A` in `largerSubobject hG A` is a pushout of
a monomorphism in the family `generatingMonomorphisms G`
(see `pushouts_ofLE_le_largerSubobject`).
-/
noncomputable def largerSubobject (A : Subobject X) : Subobject X :=
  if hA : A = ⊤ then ⊤ else (exists_larger_subobject hG A hA).choose

variable (X) in
@[simp]
/-
**CategoryTheory.IsGrothendieckAbelian.generatingMonomorphisms.largerSubobject_t
op** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.IsGrothendieckAbelian.generatingMon
omorphisms`。
形式化陈述：largerSubobject_top : largerSubobject hG (⊤ : Subobject X) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用引理 `CategoryTheory.IsGrothendieckAbelian.generatingMonomorphisms.exists_larg
er_subobject`：exists_larger_subobject {X : C} (A : Subobject X) (hA : A != ⊤) : 
exists (A' : Subobject X) (h : A < A'), (generatingMonomorphisms G).pushou…
-/
lemma largerSubobject_top : largerSubobject hG (⊤ : Subobject X) = ⊤ := dif_pos rfl
/-
**CategoryTheory.IsGrothendieckAbelian.generatingMonomorphisms.lt_largerSubobjec
t** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.IsGrothendieckAbelian.generatingMono
morphisms`。
形式化陈述：lt_largerSubobject (A : Subobject X) (hA : A != ⊤) : A < largerSubobject h
G A
参数：A : Subobject X；hA : A != ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.IsGrothendieckAbelian.generatingMonomorphisms.exists_larg
er_subobject`：exists_larger_subobject {X : C} (A : Subobject X) (hA : A != ⊤) : 
exists (A' : Subobject X) (h : A < A'), (generatingMonomorphisms G).pushou…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
lemma lt_largerSubobject (A : Subobject X) (hA : A ≠ ⊤) :
    A < largerSubobject hG A := by
  dsimp only [largerSubobject]
  rw [dif_neg hA]
  exact (exists_larger_subobject hG A hA).choose_spec.choose
/-
**CategoryTheory.IsGrothendieckAbelian.generatingMonomorphisms.le_largerSubobjec
t** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.IsGrothendieckAbelian.generatingMono
morphisms`。
形式化陈述：le_largerSubobject (A : Subobject X) : A <= largerSubobject hG A
参数：A : Subobject X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.IsGrothendieckAbelian.generatingMonomorphisms.largerSubob
ject_top`：largerSubobject_top : largerSubobject hG (⊤ : Subobject X) = ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `CategoryTheory.IsGrothendieckAbelian.generatingMonomorphisms.lt_largerSu
bobject`：lt_largerSubobject (A : Subobject X) (hA : A != ⊤) : A < largerSubobjec
t hG A
-/
lemma le_largerSubobject (A : Subobject X) :
    A ≤ largerSubobject hG A := by
  by_cases hA : A = ⊤
  · subst hA
    simp only [largerSubobject_top, le_refl]
  · exact (lt_largerSubobject hG A hA).le

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.IsGrothendieckAbelian.generatingMonomorphisms.pushouts_ofLE_le_
largerSubobject** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.IsGrothendieckAbelian.
generatingMonomorphisms`。
形式化陈述：pushouts_ofLE_le_largerSubobject (A : Subobject X) : (generatingMonomorphi
sms G).pushouts (Subobject.ofLE _ _ (le_largerSubobject hG A))
参数：A : Subobject X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.IsGrothendieckAbelian.generatingMonomorphisms.le_largerSu
bobject`：le_largerSubobject (A : Subobject X) : A <= largerSubobject hG A
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.Subobject.isIso_arrow_iff_eq_top`：isIso_arrow_iff_eq_top 
{Y : C} (P : Subobject Y) : IsIso P.arrow ↔ P = ⊤
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.IsGrothendieckAbelian.generatingMonomorphisms.largerSubob
ject_top`：largerSubobject_top : largerSubobject hG (⊤ : Subobject X) = ⊤
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.MorphismProperty.arrow_mk_iso_iff`：arrow_mk_iso_iff (P : 
MorphismProperty C) [RespectsIso P] {W X Y Z : C} {f : W ⟶ X} {g : Y ⟶ Z} (e : A
rrow.mk f ≅ Arrow.mk g) : P f ↔ P g
· 使用定理 `CategoryTheory.MorphismProperty.instRespectsIsoPushouts`：∀ {C : Type u} 
[inst : CategoryTheory.Category.{v, u} C] (P : CategoryTheory.MorphismProperty C
), P.pushouts.RespectsIso
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Subobject.ofLE_arrow`：ofLE_arrow {B : C} {X Y : Subobject
 B} (h : X <= Y) : ofLE X Y h ≫ Y.arrow = X.arrow
· 使用引理 `CategoryTheory.IsGrothendieckAbelian.isomorphisms_le_pushouts_generating
Monomorphisms`：isomorphisms_le_pushouts_generatingMonomorphisms [HasZeroMorphism
s C] : MorphismProperty.isomorphisms C <= (generatingMonomorphisms G).pusho…
· 使用定理 `CategoryTheory.MorphismProperty.isomorphisms.infer_property`：∀ {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y) [hf : Catego
ryTheory.IsIso f],   CategoryTheory.MorphismPrope…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `CategoryTheory.IsGrothendieckAbelian.generatingMonomorphisms.exists_larg
er_subobject`：exists_larger_subobject {X : C} (A : Subobject X) (hA : A != ⊤) : 
exists (A' : Subobject X) (h : A < A'), (generatingMonomorphisms G).pushou…
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Subobject.ofLE_comp_ofLE`：ofLE_comp_ofLE {B : C} (X Y Z :
 Subobject B) (h₁ : X <= Y) (h₂ : Y <= Z) : ofLE X Y h₁ ≫ ofLE Y Z h₂ = ofLE X Z
 (h₁.trans h₂)
-/
lemma pushouts_ofLE_le_largerSubobject (A : Subobject X) :
      (generatingMonomorphisms G).pushouts
        (Subobject.ofLE _ _ (le_largerSubobject hG A)) := by
  by_cases hA : A = ⊤
  · subst hA
    have := (Subobject.isIso_arrow_iff_eq_top (largerSubobject hG (⊤ : Subobject X))).2 (by simp)
    exact (MorphismProperty.arrow_mk_iso_iff _
      (Arrow.isoMk (asIso (Subobject.arrow _)) (asIso (Subobject.arrow _)) (by simp))).2
        (isomorphisms_le_pushouts_generatingMonomorphisms G (𝟙 X)
          (MorphismProperty.isomorphisms.infer_property _))
  · refine (MorphismProperty.arrow_mk_iso_iff _ ?_).1
      (exists_larger_subobject hG A hA).choose_spec.choose_spec
    exact Arrow.isoMk (Iso.refl _)
      (Subobject.isoOfEq _ _ ((by simp [largerSubobject, dif_neg hA])))

variable [IsGrothendieckAbelian.{w} C]
/-
**CategoryTheory.IsGrothendieckAbelian.generatingMonomorphisms.top_mem_range** 是
 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.IsGrothendieckAbelian.generatingMonomorph
isms`。
形式化陈述：top_mem_range (A₀ : Subobject X) {J : Type w} [LinearOrder J] [OrderBot J]
 [SuccOrder J] [WellFoundedLT J] (hJ : HasCardinalLT (Subobject X) (Cardinal.mk 
J)) : exists (j : J), transfiniteIterate (largerSubobject hG) j A₀ = ⊤
参数：A₀ : Subobject X；hJ : HasCardinalLT (Subobject X) (Cardinal.mk J)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `top_mem_range_transfiniteIterate`：top_mem_range_transfiniteIterate (hφ' 
: forall i != (⊤ : I), i < φ i) (φtop : φ ⊤ = ⊤) (H : ¬ Function.Injective (fun 
(j : J) => transfinite…
· 使用定理 `CategoryTheory.IsGrothendieckAbelian.locallySmall`：∀ {C : Type u} {inst 
: CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Abelian C}   [self 
: CategoryTheory.IsGrothendieckAbelian.…
· 使用定理 `CategoryTheory.IsGrothendieckAbelian.wellPowered`：∀ (C : Type u) [inst :
 CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2
 : CategoryTheory.IsGrothendieckAbelia…
· 使用定理 `CategoryTheory.Limits.instHasLimitsOfShapeOfHasLimitsOfSize`：∀ {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTh
eory.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.IsGrothendieckAbelian.hasLimits`：∀ (C : Type u) [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [Category
Theory.IsGrothendieckAbelian.{w, v, …
· 使用定理 `CategoryTheory.Limits.hasImages_of_hasStrongEpiMonoFactorisations`：∀ {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasSt
rongEpiMonoFactorisations C],   CategoryTheory.Limits.H…
· 使用定理 `CategoryTheory.Abelian.instHasStrongEpiMonoFactorisations`：∀ {C : Type u
} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Abelian C],   Catego
ryTheory.Limits.HasStrongEpiMonoFactorisations …
· 使用定理 `CategoryTheory.Limits.instHasColimitsOfShapeOfHasColimitsOfSize`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : Catego
ryTheory.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.IsGrothendieckAbelian.hasColimits`：∀ (C : Type u) [inst :
 CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [Catego
ryTheory.IsGrothendieckAbelian.{w, v, …
· 使用定理 `CategoryTheory.Limits.HasZeroObject.initialMonoClass`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasZeroObject C], 
  CategoryTheory.Limits.InitialMonoClass C
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用引理 `CategoryTheory.IsGrothendieckAbelian.generatingMonomorphisms.lt_largerSu
bobject`：lt_largerSubobject (A : Subobject X) (hA : A != ⊤) : A < largerSubobjec
t hG A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.IsGrothendieckAbelian.generatingMonomorphisms.largerSubob
ject_top`：largerSubobject_top : largerSubobject hG (⊤ : Subobject X) = ⊤
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `HasCardinalLT.of_injective`：of_injective (f : Y -> X) (hf : Function.Inj
ective f) : HasCardinalLT Y κ
-/
lemma top_mem_range (A₀ : Subobject X) {J : Type w} [LinearOrder J] [OrderBot J] [SuccOrder J]
    [WellFoundedLT J] (hJ : HasCardinalLT (Subobject X) (Cardinal.mk J)) :
    ∃ (j : J), transfiniteIterate (largerSubobject hG) j A₀ = ⊤ :=
  top_mem_range_transfiniteIterate (largerSubobject hG) A₀ (lt_largerSubobject hG) (by simp)
    (fun h ↦ by simpa [hasCardinalLT_iff_cardinal_mk_lt] using hJ.of_injective _ h)
/-
**CategoryTheory.IsGrothendieckAbelian.generatingMonomorphisms.exists_ordinal** 
是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.IsGrothendieckAbelian.generatingMonomorp
hisms`。
形式化陈述：exists_ordinal (A₀ : Subobject X) : exists (o : Ordinal.{w}) (j : o.ToType
), transfiniteIterate (largerSubobject hG) j A₀ = ⊤
参数：A₀ : Subobject X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsGrothendieckAbelian.locallySmall`：∀ {C : Type u} {inst 
: CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Abelian C}   [self 
: CategoryTheory.IsGrothendieckAbelian.…
· 使用定理 `CategoryTheory.IsGrothendieckAbelian.wellPowered`：∀ (C : Type u) [inst :
 CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2
 : CategoryTheory.IsGrothendieckAbelia…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `CategoryTheory.Limits.instHasLimitsOfShapeOfHasLimitsOfSize`：∀ {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTh
eory.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.IsGrothendieckAbelian.hasLimits`：∀ (C : Type u) [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [Category
Theory.IsGrothendieckAbelian.{w, v, …
· 使用定理 `CategoryTheory.Limits.hasImages_of_hasStrongEpiMonoFactorisations`：∀ {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasSt
rongEpiMonoFactorisations C],   CategoryTheory.Limits.H…
· 使用定理 `CategoryTheory.Abelian.instHasStrongEpiMonoFactorisations`：∀ {C : Type u
} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Abelian C],   Catego
ryTheory.Limits.HasStrongEpiMonoFactorisations …
· 使用定理 `CategoryTheory.Limits.instHasColimitsOfShapeOfHasColimitsOfSize`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : Catego
ryTheory.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.IsGrothendieckAbelian.hasColimits`：∀ (C : Type u) [inst :
 CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [Catego
ryTheory.IsGrothendieckAbelian.{w, v, …
· 使用定理 `CategoryTheory.Limits.HasZeroObject.initialMonoClass`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasZeroObject C], 
  CategoryTheory.Limits.InitialMonoClass C
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用引理 `CategoryTheory.IsGrothendieckAbelian.generatingMonomorphisms.top_mem_ran
ge`：top_mem_range (A₀ : Subobject X) {J : Type w} [LinearOrder J] [OrderBot J] [
SuccOrder J] [WellFoundedLT J] (hJ : HasCardinalLT (Subobject X)…
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `Order.lt_succ`：lt_succ (a : α) : a < succ a
· 使用定理 `Cardinal.instNoMaxOrder`：NoMaxOrder Cardinal.{u}
· 使用定理 `Cardinal.mk_toType`：∀ (o : Ordinal.{u_1}), Cardinal.mk o.ToType = o.card
· 使用定理 `Cardinal.card_ord`：card_ord (c) : (ord c).card = c
· 使用定理 `Cardinal.lift_succ`：lift_succ (a) : lift.{v, u} (succ a) = succ (lift.{v
, u} a)
· 使用定理 `Cardinal.lift_mk_shrink'`：lift_mk_shrink' (α : Type u) [Small.{v} α] : C
ardinal.lift.{u} #(Shrink.{v} α) = Cardinal.lift.{v} #α
-/
lemma exists_ordinal (A₀ : Subobject X) :
    ∃ (o : Ordinal.{w}) (j : o.ToType), transfiniteIterate (largerSubobject hG) j A₀ = ⊤ := by
  let κ := Order.succ (Cardinal.mk (Shrink.{w} (Subobject X)))
  have : Nonempty κ.ord.ToType := by simp [κ]
  have := WellFoundedLT.toOrderBot κ.ord.ToType
  exact ⟨κ.ord, top_mem_range hG A₀ (lt_of_lt_of_le (Order.lt_succ _) (by simp [κ]))⟩

section

variable (A₀ : Subobject X) (J : Type w) [LinearOrder J] [OrderBot J] [SuccOrder J]
  [WellFoundedLT J]

/-- Let `C` be a Grothendieck abelian category with a generator (`hG`),
`X : C`, `A₀ : Subobject X`. Let `J` be a well-ordered type. This is
the functor `J ⥤ MonoOver X` which corresponds to the evaluation
at `A₀` of the transfinite iteration of the map
`largerSubobject hG : Subobject X → Subobject X`. -/
@[simps]
/-
**CategoryTheory.IsGrothendieckAbelian.generatingMonomorphisms.functorToMonoOver
** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.IsGrothendieckAbelian.generatingMonom
orphisms`。
形式化陈述：functorToMonoOver : J ⥤ MonoOver X where obj j
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsGrothendieckAbelian.locallySmall`：∀ {C : Type u} {inst 
: CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Abelian C}   [self 
: CategoryTheory.IsGrothendieckAbelian.…
· 使用定理 `CategoryTheory.IsGrothendieckAbelian.wellPowered`：∀ (C : Type u) [inst :
 CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2
 : CategoryTheory.IsGrothendieckAbelia…

--- 原说明 ---
Let `C` be a Grothendieck abelian category with a generator (`hG`),
`X : C`, `A₀ : Subobject X`. Let `J` be a well-ordered type. This is
the functor `J ⥤ MonoOver X` which corresponds to the evaluation
at `A₀` of the transfinite iteration of the map
`largerSubobject hG : Subobject X → Subobject X`.
-/
noncomputable def functorToMonoOver : J ⥤ MonoOver X where
  obj j := MonoOver.mk (transfiniteIterate (largerSubobject hG) j A₀).arrow
  map {j j'} f := MonoOver.homMk (Subobject.ofLE _ _
      (monotone_transfiniteIterate _ _ (le_largerSubobject hG) (leOfHom f)))

/-- The functor `J ⥤ C` induced by `functorToMonoOver hG A₀ J : J ⥤ MonoOver X`. -/
/-
**CategoryTheory.IsGrothendieckAbelian.generatingMonomorphisms.functor** 是 Mathl
ib 中的一个缩写定义，位于命名空间 `CategoryTheory.IsGrothendieckAbelian.generatingMonomorphisms
`。
形式化陈述：functor : J ⥤ C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `J ⥤ C` induced by `functorToMonoOver hG A₀ J : J ⥤ MonoOver X`.
-/
noncomputable abbrev functor : J ⥤ C :=
  functorToMonoOver hG A₀ J ⋙ MonoOver.forget _ ⋙ Over.forget _

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.IsGrothendieckAbelian.generatingMonomorphisms.** 是 Mathlib 中的一个
实例，位于命名空间 `CategoryTheory.IsGrothendieckAbelian.generatingMonomorphisms`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (functor hG A₀ J).IsWellOrderContinuous where
  nonempty_isColimit m hm := ⟨by
    have := hm.nonempty_Iio.to_subtype
    let c := (Set.principalSegIio m).cocone (functorToMonoOver hG A₀ J ⋙ MonoOver.forget _)
    have : Mono c.pt.hom := by dsimp [c]; infer_instance
    apply IsGrothendieckAbelian.isColimitMapCoconeOfSubobjectMkEqISup
      ((Set.principalSegIio m).monotone.functor ⋙ functorToMonoOver hG A₀ J) c
    dsimp [c]
    simp only [Subobject.mk_arrow]
    exact transfiniteIterate_limit (largerSubobject hG) A₀ m hm⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
variable {J} in
/-- For any `j`, the map `(functor hG A₀ J).map (homOfLE bot_le : ⊥ ⟶ j)`
is a transfinite composition of pushouts of monomorphisms in the
family `generatingMonomorphisms G`. -/
/-
**CategoryTheory.IsGrothendieckAbelian.generatingMonomorphisms.transfiniteCompos
itionOfShapeMapFromBot** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.IsGrothendieckA
belian.generatingMonomorphisms`。
形式化陈述：transfiniteCompositionOfShapeMapFromBot (j : J) : (generatingMonomorphisms
 G).pushouts.TransfiniteCompositionOfShape (Set.Iic j) ((functor hG A₀ J).map (h
omOfLE bot_le : ⊥ ⟶ j)) where F
参数：j : J。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For any `j`, the map `(functor hG A₀ J).map (homOfLE bot_le : ⊥ ⟶ j)`
is a transfinite composition of pushouts of monomorphisms in the
family `generatingMonomorphisms G`.
-/
noncomputable def transfiniteCompositionOfShapeMapFromBot (j : J) :
    (generatingMonomorphisms G).pushouts.TransfiniteCompositionOfShape (Set.Iic j)
    ((functor hG A₀ J).map (homOfLE bot_le : ⊥ ⟶ j)) where
  F := (Set.initialSegIic j).monotone.functor ⋙ functor hG A₀ J
  isoBot := Iso.refl _
  incl :=
    { app k := (functor hG A₀ J).map (homOfLE k.2)
      naturality k k' h := by simp [MonoOver.forget] }
  isColimit := colimitOfDiagramTerminal isTerminalTop _
  map_mem k hk := by
    dsimp [MonoOver.forget]
    convert!
      pushouts_ofLE_le_largerSubobject hG (transfiniteIterate (largerSubobject hG) k.1 A₀) using 2
    all_goals
      rw [Set.Iic.succ_eq_of_not_isMax hk,
        transfiniteIterate_succ _ _ _ (Set.not_isMax_coe _ hk)]

end

variable {A : C} {f : A ⟶ X} [Mono f]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- If `transfiniteIterate (largerSubobject hG) j (Subobject.mk f) = ⊤`,
then the monomorphism `f` is a transfinite composition of pushouts of
monomorphisms in the family `generatingMonomorphisms G`. -/
/-
**CategoryTheory.IsGrothendieckAbelian.generatingMonomorphisms.transfiniteCompos
itionOfShapeOfEqTop** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.IsGrothendieckAbel
ian.generatingMonomorphisms`。
形式化陈述：transfiniteCompositionOfShapeOfEqTop {J : Type w} [LinearOrder J] [OrderBo
t J] [SuccOrder J] [WellFoundedLT J] {j : J} (hj : transfiniteIterate (largerSub
object hG) j (Subobject.mk f) = ⊤) : (generatingMonomorphisms G).pushouts.Transf
initeCompositionOfShape (Set.Iic j) f
参数：hj : transfiniteIterate (largerSubobject hG) j (Subobject.mk f) = ⊤。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsGrothendieckAbelian.locallySmall`：∀ {C : Type u} {inst 
: CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Abelian C}   [self 
: CategoryTheory.IsGrothendieckAbelian.…
· 使用定理 `CategoryTheory.IsGrothendieckAbelian.wellPowered`：∀ (C : Type u) [inst :
 CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2
 : CategoryTheory.IsGrothendieckAbelia…

--- 原说明 ---
If `transfiniteIterate (largerSubobject hG) j (Subobject.mk f) = ⊤`,
then the monomorphism `f` is a transfinite composition of pushouts of
monomorphisms in the family `generatingMonomorphisms G`.
-/
noncomputable def transfiniteCompositionOfShapeOfEqTop
    {J : Type w} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J] {j : J}
    (hj : transfiniteIterate (largerSubobject hG) j (Subobject.mk f) = ⊤) :
    (generatingMonomorphisms G).pushouts.TransfiniteCompositionOfShape (Set.Iic j) f := by
  let t := transfiniteIterate (largerSubobject hG) j (Subobject.mk f)
  have := (Subobject.isIso_arrow_iff_eq_top t).2 hj
  apply (transfiniteCompositionOfShapeMapFromBot hG (Subobject.mk f) j).ofArrowIso
  refine Arrow.isoMk ((Subobject.isoOfEq _ _ (transfiniteIterate_bot _ _) ≪≫
    Subobject.underlyingIso f)) (asIso t.arrow) ?_
  dsimp [MonoOver.forget]
  rw [assoc, Subobject.underlyingIso_hom_comp_eq_mk, Subobject.ofLE_arrow,
    Subobject.ofLE_arrow]

variable (f)

/-- Let `C` be a Grothendieck abelian category. Assume that `G : C` is a generator
of `C`. Then, any morphism in `C` is a transfinite composition of pushouts
of monomorphisms in the family `generatingMonomorphisms G` which consists
of the inclusions of the subobjects of `G`. -/
/-
**CategoryTheory.IsGrothendieckAbelian.generatingMonomorphisms.exists_transfinit
eCompositionOfShape** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.IsGrothendieckAbel
ian.generatingMonomorphisms`。
形式化陈述：exists_transfiniteCompositionOfShape : exists (J : Type w) (_ : LinearOrde
r J) (_ : OrderBot J) (_ : SuccOrder J) (_ : WellFoundedLT J), Nonempty ((genera
tingMonomorphisms G).pushouts.TransfiniteCompositionOfShape J f)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsGrothendieckAbelian.locallySmall`：∀ {C : Type u} {inst 
: CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Abelian C}   [self 
: CategoryTheory.IsGrothendieckAbelian.…
· 使用定理 `CategoryTheory.IsGrothendieckAbelian.wellPowered`：∀ (C : Type u) [inst :
 CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2
 : CategoryTheory.IsGrothendieckAbelia…
· 使用定理 `CategoryTheory.Limits.instHasLimitsOfShapeOfHasLimitsOfSize`：∀ {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTh
eory.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.IsGrothendieckAbelian.hasLimits`：∀ (C : Type u) [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [Category
Theory.IsGrothendieckAbelian.{w, v, …
· 使用定理 `CategoryTheory.Limits.hasImages_of_hasStrongEpiMonoFactorisations`：∀ {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasSt
rongEpiMonoFactorisations C],   CategoryTheory.Limits.H…
· 使用定理 `CategoryTheory.Abelian.instHasStrongEpiMonoFactorisations`：∀ {C : Type u
} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Abelian C],   Catego
ryTheory.Limits.HasStrongEpiMonoFactorisations …
· 使用定理 `CategoryTheory.Limits.instHasColimitsOfShapeOfHasColimitsOfSize`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : Catego
ryTheory.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.IsGrothendieckAbelian.hasColimits`：∀ (C : Type u) [inst :
 CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [Catego
ryTheory.IsGrothendieckAbelian.{w, v, …
· 使用定理 `CategoryTheory.Limits.HasZeroObject.initialMonoClass`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasZeroObject C], 
  CategoryTheory.Limits.InitialMonoClass C
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用引理 `CategoryTheory.IsGrothendieckAbelian.generatingMonomorphisms.exists_ordi
nal`：exists_ordinal (A₀ : Subobject X) : exists (o : Ordinal.{w}) (j : o.ToType)
, transfiniteIterate (largerSubobject hG) j A₀ = ⊤
· 使用定理 `Set.ordConnected_Iic`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, (Set
.Iic a).OrdConnected

--- 原说明 ---
Let `C` be a Grothendieck abelian category. Assume that `G : C` is a generator
of `C`. Then, any morphism in `C` is a transfinite composition of pushouts
of monomorphisms in the family `generatingMonomorphisms G` which consists
of the inclusions of the subobjects of `G`.
-/
lemma exists_transfiniteCompositionOfShape :
    ∃ (J : Type w) (_ : LinearOrder J) (_ : OrderBot J) (_ : SuccOrder J)
        (_ : WellFoundedLT J),
    Nonempty ((generatingMonomorphisms G).pushouts.TransfiniteCompositionOfShape J f) := by
  obtain ⟨o, j, hj⟩ := exists_ordinal hG (Subobject.mk f)
  have : Nonempty o.ToType := ⟨j⟩
  have : OrderBot o.ToType := WellFoundedLT.toOrderBot _
  exact ⟨_, _, _, _, _, ⟨transfiniteCompositionOfShapeOfEqTop hG hj⟩⟩

end generatingMonomorphisms

open MorphismProperty

variable {G}

/-
**CategoryTheory.IsGrothendieckAbelian.generatingMonomorphisms_rlp** 是 Mathlib 中
的一个引理，位于命名空间 `CategoryTheory.IsGrothendieckAbelian`。
形式化陈述：generatingMonomorphisms_rlp [IsGrothendieckAbelian.{w} C] (hG : IsSeparato
r G) : (generatingMonomorphisms G).rlp = (monomorphisms C).rlp
参数：hG : IsSeparator G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `CategoryTheory.IsGrothendieckAbelian.generatingMonomorphisms.exists_tran
sfiniteCompositionOfShape`：exists_transfiniteCompositionOfShape : exists (J : Ty
pe w) (_ : LinearOrder J) (_ : OrderBot J) (_ : SuccOrder J) (_ : WellFoundedLT 
J), Non…
· 使用引理 `CategoryTheory.MorphismProperty.transfiniteCompositionsOfShape_le_llp_rl
p`：transfiniteCompositionsOfShape_le_llp_rlp : W.transfiniteCompositionsOfShape 
J <= W.rlp.llp
· 使用定理 `CategoryTheory.MorphismProperty.TransfiniteCompositionOfShape.mem`：∀ {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C] {W : CategoryTheory.Morphism
Property C} {J : Type w}   [inst_1 : LinearOrder J] [in…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.MorphismProperty.rlp_pushouts`：rlp_pushouts : T.pushouts.
rlp = T.rlp
· 使用引理 `CategoryTheory.MorphismProperty.antitone_rlp`：antitone_rlp : Antitone (r
lp : MorphismProperty C -> _)
· 使用引理 `CategoryTheory.IsGrothendieckAbelian.generatingMonomorphisms_le_monomorp
hisms`：generatingMonomorphisms_le_monomorphisms (G : C) : generatingMonomorphism
s G <= MorphismProperty.monomorphisms C
-/
lemma generatingMonomorphisms_rlp [IsGrothendieckAbelian.{w} C] (hG : IsSeparator G) :
    (generatingMonomorphisms G).rlp = (monomorphisms C).rlp := by
  apply le_antisymm
  · intro X Y p hp A B i (_ : Mono i)
    obtain ⟨J, _, _, _, _, ⟨h⟩⟩ :=
      generatingMonomorphisms.exists_transfiniteCompositionOfShape hG i
    exact transfiniteCompositionsOfShape_le_llp_rlp _ _ _ h.mem _ (by simpa)
  · exact antitone_rlp (generatingMonomorphisms_le_monomorphisms _)

open MorphismProperty

variable [IsGrothendieckAbelian.{w} C]
/-
**CategoryTheory.IsGrothendieckAbelian.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheor
y.IsGrothendieckAbelian`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasSmallObjectArgument.{w} (generatingMonomorphisms G) := by
  obtain ⟨κ, hκ', hκ⟩ := HasCardinalLT.exists_regular_cardinal.{w} (Subobject G)
  have : Fact κ.IsRegular := ⟨hκ'⟩
  have : Nonempty κ.ord.ToType := by simpa using hκ'.ne_zero
  have := WellFoundedLT.toOrderBot κ.ord.ToType
  exact ⟨κ, inferInstance, inferInstance,
    { preservesColimit {A B X Y} i hi f hf := by
        let hf' : (monomorphisms C).TransfiniteCompositionOfShape κ.ord.ToType f :=
          { toTransfiniteCompositionOfShape := hf.toTransfiniteCompositionOfShape
            map_mem j hj := by
              have := (hf.attachCells j hj).pushouts_coproducts
              simp only [ofHoms_homFamily] at this
              refine (?_ : _ ≤ monomorphisms C) _ this
              simp only [pushouts_le_iff, coproducts_le_iff]
              exact generatingMonomorphisms_le_monomorphisms G }
        have (j j' : κ.ord.ToType) (φ : j ⟶ j') : Mono (hf'.F.map φ) := hf'.mem_map φ
        apply preservesColimit_coyoneda_obj_of_mono (Y := hf'.F) (κ := κ)
        obtain ⟨S⟩ := hi
        exact Subobject.hasCardinalLT_of_mono hκ S.arrow }⟩
/-
**CategoryTheory.IsGrothendieckAbelian.llp_rlp_monomorphisms** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.IsGrothendieckAbelian`。
形式化陈述：llp_rlp_monomorphisms (hG : IsSeparator G) : (monomorphisms C).rlp.llp = m
onomorphisms C
参数：hG : IsSeparator G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.IsGrothendieckAbelian.generatingMonomorphisms_rlp`：genera
tingMonomorphisms_rlp [IsGrothendieckAbelian.{w} C] (hG : IsSeparator G) : (gene
ratingMonomorphisms G).rlp = (monomorphisms C).rlp
· 使用引理 `CategoryTheory.MorphismProperty.llp_rlp_of_hasSmallObjectArgument`：llp_r
lp_of_hasSmallObjectArgument : I.rlp.llp = (transfiniteCompositions.{w} (coprodu
cts.{w} I).pushouts).retracts
· 使用定理 `CategoryTheory.IsGrothendieckAbelian.instHasSmallObjectArgumentGeneratin
gMonomorphisms`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {G : C}
 [inst_1 : CategoryTheory.Abelian C]   [CategoryTheory.IsGrothendieckAbelian…
· 使用引理 `CategoryTheory.MorphismProperty.retracts_monotone`：retracts_monotone : M
onotone (retracts (C
· 使用引理 `CategoryTheory.MorphismProperty.transfiniteCompositions_monotone`：transf
initeCompositions_monotone : Monotone (transfiniteCompositions.{w} (C
· 使用引理 `CategoryTheory.MorphismProperty.pushouts_monotone`：pushouts_monotone : M
onotone (pushouts (C
· 使用引理 `CategoryTheory.MorphismProperty.coproducts_monotone`：coproducts_monotone
 : Monotone (coproducts.{w} (C
· 使用引理 `CategoryTheory.IsGrothendieckAbelian.generatingMonomorphisms_le_monomorp
hisms`：generatingMonomorphisms_le_monomorphisms (G : C) : generatingMonomorphism
s G <= MorphismProperty.monomorphisms C
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `CategoryTheory.MorphismProperty.coproducts_eq_self`：coproducts_eq_self [
IsStableUnderCoproducts.{w} W] : coproducts.{w} W = W
· 使用定理 `CategoryTheory.MorphismProperty.instIsStableUnderCoproductsMonomorphisms
OfAB4OfSize`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : 
CategoryTheory.Limits.HasCoproducts C]   [CategoryTheory.AB4OfSize.{u', v…
· 使用定理 `CategoryTheory.Limits.instHasColimitsOfShapeOfHasColimitsOfSize`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : Catego
ryTheory.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.IsGrothendieckAbelian.hasColimits`：∀ (C : Type u) [inst :
 CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [Catego
ryTheory.IsGrothendieckAbelian.{w, v, …
· 使用定理 `CategoryTheory.IsGrothendieckAbelian.ab4OfSize`：∀ (C : Type u) [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2 :
 CategoryTheory.IsGrothendieckAbelia…
· 使用定理 `CategoryTheory.MorphismProperty.IsStableUnderRetracts.monomorphisms`：∀ {
C : Type u} [inst : CategoryTheory.Category.{v, u} C],   (CategoryTheory.Morphis
mProperty.monomorphisms C).IsStableUnderRetracts
· 使用定理 `CategoryTheory.IsGrothendieckAbelian.instIsStableUnderTransfiniteComposi
tionMonomorphisms`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [ins
t_1 : CategoryTheory.Abelian C]   [CategoryTheory.IsGrothendieckAbelian.{w, v, …
· 使用定理 `CategoryTheory.Abelian.instIsStableUnderCobaseChangeMonomorphisms`：∀ {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Abelian C], 
  (CategoryTheory.MorphismProperty.monomorphisms C).IsS…
· 使用引理 `CategoryTheory.MorphismProperty.le_llp_rlp`：le_llp_rlp : T <= T.rlp.llp
-/
lemma llp_rlp_monomorphisms (hG : IsSeparator G) :
    (monomorphisms C).rlp.llp = monomorphisms C := by
  refine le_antisymm ?_ (le_llp_rlp _)
  rw [← generatingMonomorphisms_rlp hG, llp_rlp_of_hasSmallObjectArgument]
  trans (transfiniteCompositions.{w} (coproducts.{w} (monomorphisms C)).pushouts).retracts
  · apply retracts_monotone
    apply transfiniteCompositions_monotone
    apply pushouts_monotone
    apply coproducts_monotone
    apply generatingMonomorphisms_le_monomorphisms
  · simp
/-
**CategoryTheory.IsGrothendieckAbelian.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheor
y.IsGrothendieckAbelian`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasFunctorialFactorization (monomorphisms C) (monomorphisms C).rlp := by
  have hG := isSeparator_separator C
  rw [← generatingMonomorphisms_rlp hG, ← llp_rlp_monomorphisms hG,
    ← generatingMonomorphisms_rlp hG]
  infer_instance

/-- A (functorial) factorization of any morphisms in a Grothendieck abelian category
as a monomorphism followed by a morphism which has the right lifting property
with respect to all monomorphisms. -/
/-
**CategoryTheory.IsGrothendieckAbelian.monoMapFactorizationDataRlp** 是 Mathlib 中
的一个缩写定义，位于命名空间 `CategoryTheory.IsGrothendieckAbelian`。
形式化陈述：monoMapFactorizationDataRlp {X Y : C} (f : X ⟶ Y) : MapFactorizationData (
monomorphisms C) (monomorphisms C).rlp f
参数：f : X ⟶ Y。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsGrothendieckAbelian.instHasFunctorialFactorizationMonom
orphismsRlp`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : 
CategoryTheory.Abelian C]   [CategoryTheory.IsGrothendieckAbelian.{w, v, …

--- 原说明 ---
A (functorial) factorization of any morphisms in a Grothendieck abelian category
as a monomorphism followed by a morphism which has the right lifting property
with respect to all monomorphisms.
-/
noncomputable abbrev monoMapFactorizationDataRlp {X Y : C} (f : X ⟶ Y) :
    MapFactorizationData (monomorphisms C) (monomorphisms C).rlp f :=
  (functorialFactorizationData _ _).factorizationData f
/-
**CategoryTheory.IsGrothendieckAbelian.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheor
y.IsGrothendieckAbelian`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y : C} (f : X ⟶ Y) :
    Mono (monoMapFactorizationDataRlp f).i :=
  (monoMapFactorizationDataRlp f).hi
/-
**CategoryTheory.IsGrothendieckAbelian.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheor
y.IsGrothendieckAbelian`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X : C} : Injective (monoMapFactorizationDataRlp (0 : X ⟶ 0)).Z := by
  let fac := (monoMapFactorizationDataRlp (0 : X ⟶ 0))
  simpa only [injective_iff_rlp_monomorphisms_zero,
    (isZero_zero C).eq_of_tgt fac.p 0] using fac.hp

/-- A Grothendieck abelian category has enough injectives. -/
@[stacks 079H]
/-
**CategoryTheory.IsGrothendieckAbelian.enoughInjectives** 是 Mathlib 中的一个实例，位于命名空
间 `CategoryTheory.IsGrothendieckAbelian`。
形式化陈述：enoughInjectives : EnoughInjectives C where presentation X
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `CategoryTheory.IsGrothendieckAbelian.instInjectiveZMonomorphismsRlpMonoM
apFactorizationDataRlpOfNatHom`：∀ {C : Type u} [inst : CategoryTheory.Category.{
v, u} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2 : CategoryTheory.IsGrothe
ndieckAbelia…
· 使用定理 `CategoryTheory.IsGrothendieckAbelian.instMonoIMonomorphismsRlpMonoMapFac
torizationDataRlp`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [ins
t_1 : CategoryTheory.Abelian C]   [inst_2 : CategoryTheory.IsGrothendieckAbelia…

--- 原说明 ---
A Grothendieck abelian category has enough injectives.
-/
instance enoughInjectives : EnoughInjectives C where
  presentation X := ⟨{ J := _, f := (monoMapFactorizationDataRlp (0 : X ⟶ 0)).i }⟩

end IsGrothendieckAbelian

end CategoryTheory

