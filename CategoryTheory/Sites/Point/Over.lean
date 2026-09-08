/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Filtered.FinallySmall
public import Mathlib.CategoryTheory.Functor.TypeValuedFlat
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Comma.LocallySmall
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Point.Conservative

/-!
# Points of `Over` sites

Given a point `Φ` of a site `(C, J)`, an object `X : C`, and `x : Φ.fiber.obj X`,
we define a point `Φ.over x` of the site `(Over X, J.over X)`.

We show that if `(C, J)` has enough points, then so does `(Over X, J.over X)`.

-/

@[expose] public section

universe w v u

namespace CategoryTheory

open GrothendieckTopology

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [LocallySmall.{w} C] (Φ : Point.{w} J) {X : C} (x : Φ.fiber.obj X)

namespace GrothendieckTopology.Point

set_option backward.isDefEq.respectTransparency false in
/-- Given a point `Φ` of a site `(C, J)`, an object `X : C`, and `x : Φ.fiber.obj X`,
this is the point of the site `(Over X, J.over X)` such that the fiber of
an object of `Over X` corresponding to a morphism `f : Y ⟶ X` identifies
to subtype of `Φ.fiber.obj Y` consisting of elements `y` such
that `Φ.fiber.map f y = x`. -/
@[simps]
/-
**CategoryTheory.GrothendieckTopology.Point.over** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.GrothendieckTopology.Point`。
形式化陈述：over : Point.{w} (J.over X) where fiber
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a point `Φ` of a site `(C, J)`, an object `X : C`, and `x : Φ.fiber.obj X`
,
this is the point of the site `(Over X, J.over X)` such that the fiber of
an object of `Over X` corresponding to a morphism `f : Y ⟶ X` identifies
to subtype of `Φ.fiber.obj Y` consisting of elements `y` such
that `Φ.fiber.map f y = x`.
-/
def over : Point.{w} (J.over X) where
  fiber := FunctorToTypes.fromOverFunctor Φ.fiber x
  initiallySmall :=
    initiallySmall_of_initial_of_initiallySmall
      (FunctorToTypes.fromOverFunctorElementsEquivalence Φ.fiber x).inverse
  jointly_surjective := by
    rintro U R hR ⟨u, hu⟩
    obtain ⟨R, rfl⟩ := (Sieve.overEquiv _).symm.surjective R
    simp only [mem_over_iff, OrderIso.apply_symm_apply] at hR
    obtain ⟨Y, f, hf, v, rfl⟩ := Φ.jointly_surjective R hR u
    refine ⟨Over.mk (f ≫ U.hom), Over.homMk f, hf, ⟨v, ?_⟩, rfl⟩
    rw [FunctorToTypes.mem_fromOverSubfunctor_iff] at hu ⊢
    simpa

end GrothendieckTopology.Point

namespace ObjectProperty

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints.over** 是 Mathlib 中的
一个定理，位于命名空间 `CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {J : CategoryTheo
ry.GrothendieckTopology C}   [inst_1 : CategoryTheory.LocallySmall.{w, v, u} C] 
{P : CategoryTheory.ObjectProperty J.Point}   [CategoryTheory.ObjectProperty.Sma
ll.{w, max u w, max (max u v) (w + 1)} P] [J.WEqualsLocallyBijective (Type w)]  
 [CategoryTheory.HasSheafify J (Type w)],   P.IsConservativeFamilyOfPoints →    
 ∀ (X : C) [CategoryTheory.HasSheafify (J.over X) (Type w)],       (CategoryTheo
ry.ObjectProperty.ofObj fun ψ => ψ.fst.obj.over ψ.snd).IsConservativeFamilyOfPoi
nts
参数：max u v；w + 1；Type w；Type w；X : C；J.over X；Type w；CategoryTheory.ObjectProper
ty.ofObj fun ψ => ψ.fst.obj.over ψ.snd。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints.mk'`：mk' [Has
Sheafify J (Type w)] (hP : forall ⦃X : C⦄ (S : Sieve X) (_ : forall (Φ : P.FullS
ubcategory) (x : Φ.obj.fiber.obj X), exists (Y : C) …
· 使用定理 `CategoryTheory.Over.locallySmall`：∀ {T : Type u₃} [inst : CategoryTheory
.Category.{v₃, u₃} T] (X : T) [CategoryTheory.LocallySmall.{w, v₃, u₃} T],   Cat
egoryTheory.LocallySma…
· 使用引理 `CategoryTheory.Over.mk_surjective`：mk_surjective {S : T} (X : Over S) : 
exists (Y : T) (f : Y ⟶ S), Over.mk f = X
· 使用定理 `OrderIso.surjective`：∀ {α : Type u_2} {β : Type u_3} [inst : LE α] [inst
_1 : LE β] (e : α ≃o β), Function.Surjective ⇑e
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.GrothendieckTopology.mem_over_iff`：mem_over_iff {X : C} {
Y : Over X} (S : Sieve Y) : S in (J.over X) Y ↔ Sieve.overEquiv _ S in J Y.left
· 使用定理 `OrderIso.apply_symm_apply`：apply_symm_apply (e : α ≃o β) (x : β) : e (e.
symm x) = x
· 使用引理 `CategoryTheory.Sieve.exists_eq_ofArrows`：exists_eq_ofArrows (R : Sieve X
) : exists (I : Type max u₁ v₁) (Y : I -> C) (f : forall i, Y i ⟶ X), R = Sieve.
ofArrows _ f
· 使用引理 `CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints.jointly_refle
ct_ofArrows_mem_of_small`：jointly_reflect_ofArrows_mem_of_small [HasSheafify J (
Type w)] [J.WEqualsLocallyBijective (Type w)] (hP : P.IsConservativeFamilyOfPoin
ts) [O…
· 使用引理 `CategoryTheory.FunctorToTypes.mem_fromOverSubfunctor_iff`：mem_fromOverSu
bfunctor_iff {U : Over X} (u : F.obj U.left) : u in (fromOverSubfunctor F x).obj
 U ↔ F.map U.hom u = x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.ConcreteCategory.congr_hom`：congr_hom {X Y : C} {f g : X 
⟶ Y} (h : f = g) (x : ToType X) : f x = g x
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
lemma IsConservativeFamilyOfPoints.over
    {P : ObjectProperty (Point.{w} J)} [ObjectProperty.Small.{w} P]
    [J.WEqualsLocallyBijective (Type w)] [HasSheafify J (Type w)]
    (hP : P.IsConservativeFamilyOfPoints) (X : C) [HasSheafify (J.over X) (Type w)] :
    IsConservativeFamilyOfPoints
      (ObjectProperty.ofObj (fun (ψ : Σ (Φ : P.FullSubcategory),
        Φ.obj.fiber.obj X) ↦ ψ.1.obj.over ψ.2)) :=
  mk' (fun Y S hS ↦ by
    obtain ⟨Y, f, rfl⟩ := Over.mk_surjective Y
    obtain ⟨S, rfl⟩ := (Sieve.overEquiv _).symm.surjective S
    rw [mem_over_iff, OrderIso.apply_symm_apply]
    obtain ⟨ι, Z, g, rfl⟩ := S.exists_eq_ofArrows
    rw [hP.jointly_reflect_ofArrows_mem_of_small]
    intro Φ y
    obtain ⟨T, a, ⟨_, b, _, ⟨i⟩, hb⟩, ⟨z, hz₁⟩, hz₂⟩ := hS (⟨_, ⟨⟨Φ, Φ.obj.fiber.map f y⟩⟩⟩)
      (⟨by exact y, by rw [FunctorToTypes.mem_fromOverSubfunctor_iff]; rfl⟩)
    rw [Subtype.ext_iff] at hz₂
    exact ⟨i, Φ.obj.fiber.map b z,
      (ConcreteCategory.congr_hom (Φ.obj.fiber.map_comp b (g i)) _).symm.trans (by rwa [hb])⟩)

end ObjectProperty

namespace GrothendieckTopology

/-
**CategoryTheory.GrothendieckTopology.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory
.GrothendieckTopology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasEnoughPoints.{w} J] [J.WEqualsLocallyBijective (Type w)]
    [HasSheafify J (Type w)] (X : C)
    [HasSheafify (J.over X) (Type w)] :
    HasEnoughPoints.{w} (J.over X) := by
  obtain ⟨P, _, hP⟩ := HasEnoughPoints.exists_objectProperty J
  exact ⟨_, inferInstance, hP.over X⟩

end GrothendieckTopology

end CategoryTheory

