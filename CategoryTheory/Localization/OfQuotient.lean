/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.ModelCategory.LeftHomotopy
public import Mathlib.AlgebraicTopology.ModelCategory.RightHomotopy
public import Mathlib.CategoryTheory.Localization.Opposite
public import Mathlib.CategoryTheory.Quotient

/-!
# Certain quotient categories are localizations

Let `r : HomRel C` be a relation on morphisms in a category `C` and
`W : MorphismProperty C`. We assume that `W` is inverted by the quotient functor
`functor r : C ⥤ quotient r`. If any relation `r f₀ f₁` between morphisms
`f₀ : X ⟶ Y` and `f₁ : X ⟶ Y` can be "explained" by the use of a homotopy
involving a cylinder object (i.e. there exists an object `cylinder : C`,
a morphism `π : cylinder ⟶ X` in `W`, a morphism `φ : cylinder ⟶ Y` and two
sections `i₀` and `i₁` to `π` such that `i₀ ≫ φ = f₀` and `i₁ ≫ φ = f₁`),
then `functor r : C ⥤ quotient r` is a localization functor for `W`.
We also deduce a slightly more general result involving
a full and essentially surjective functor `L : C ⥤ D` instead of the quotient
functor `functor r : C ⥤ quotient r`.
Dual results involving path objects are also obtained.

-/

public section

namespace CategoryTheory

open HomotopicalAlgebra

variable {C D : Type*} [Category* C] [Category* D]

namespace Quotient

variable (r : HomRel C) (W : MorphismProperty C)
  (hW : W.IsInvertedBy (functor r))
  (hr : ∀ ⦃X Y : C⦄ (f₀ f₁ : X ⟶ Y) (_ : r f₀ f₁),
    ∃ (P : Precylinder X) (_ : P.LeftHomotopy f₀ f₁), W P.π)

namespace isLocalization_functor

variable {r W} in
/-- Auxiliary definition for `Quotient.isLocalization_functor`. -/
/-
**CategoryTheory.Quotient.isLocalization_functor.strictUniversalPropertyFixedTar
get** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Quotient.isLocalization_functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `Quotient.isLocalization_functor`.
-/
private def strictUniversalPropertyFixedTarget (E : Type*) [Category* E] :
    Localization.StrictUniversalPropertyFixedTarget (functor r) W E where
  inverts := hW
  lift F hF := Quotient.lift r F (fun X Y f₀ f₁ hf ↦ by
    obtain ⟨P, h, hπ⟩ := hr f₀ f₁ hf
    simp only [← h.h₀, ← h.h₁, Functor.map_comp]
    congr 1
    have := hF _ hπ
    simp [← cancel_mono (F.map P.π), ← Functor.map_comp])
  fac F hF := rfl
  uniq F₁ F₂ h := by
    fapply Functor.ext
    · rintro ⟨X⟩
      exact Functor.congr_obj h X
    · rintro ⟨X⟩ ⟨Y⟩ ⟨f⟩
      exact Functor.congr_hom h f

end isLocalization_functor

include hW hr in
/-
**CategoryTheory.Quotient.isLocalization_functor** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.Quotient`。
形式化陈述：isLocalization_functor : (functor r).IsLocalization W
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsLocalization.mk'`：∀ {C : Type u_1} {D : Type u_
2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.Cate
gory.{v_2, u_2} D] (L : Categor…
-/
lemma isLocalization_functor : (functor r).IsLocalization W := by
  apply Functor.IsLocalization.mk'
  all_goals apply isLocalization_functor.strictUniversalPropertyFixedTarget hW hr

end Quotient

namespace Functor

/-
**CategoryTheory.Functor.isLocalization_of_essSurj_of_full_of_exists_cylinders**
 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：isLocalization_of_essSurj_of_full_of_exists_cylinders (L : C ⥤ D) [L.EssSu
rj] [L.Full] (W : MorphismProperty C) (hW : W.IsInvertedBy L) (hr : forall ⦃X Y 
: C⦄ (f₀ f₁ : X ⟶ Y) (_ : L.map f₀ = L.map f₁), exists (P : Precylinder X) (_ : 
P.LeftHomotopy f₀ f₁), W P.π) : L.IsLocalization W
参数：L : C ⥤ D；W : MorphismProperty C；hW : W.IsInvertedBy L；hr : forall ⦃X Y : C⦄ 
(f₀ f₁ : X ⟶ Y) (_ : L.map f₀ = L.map f₁), exists (P : Precylinder X) (_ : P.Lef
tHomotopy f₀ f₁), W P.π。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `CategoryTheory.isIso_of_reflects_iso`：isIso_of_reflects_iso {A B : C} (f
 : A ⟶ B) (F : C ⥤ D) [IsIso (F.map f)] [F.ReflectsIsomorphisms] : IsIso f
· 使用定理 `CategoryTheory.reflectsIsomorphisms_of_full_and_faithful`：∀ {C : Type u_
1} [inst : CategoryTheory.Category.{v_1, u_1} C] {D : Type u_2}   [inst_1 : Cate
goryTheory.Category.{v_2, u_2} D] (F : Categor…
· 使用定理 `CategoryTheory.Functor.instFullQuotientHomRelLift`：∀ {C : Type u_1} [ins
t : CategoryTheory.Category.{v_1, u_1} C] {D : Type u_2}   [inst_1 : CategoryThe
ory.Category.{v_2, u_2} D] (L : Categor…
· 使用定理 `CategoryTheory.Functor.instFaithfulQuotientHomRelLift`：∀ {C : Type u_1} 
[inst : CategoryTheory.Category.{v_1, u_1} C] {D : Type u_2}   [inst_1 : Categor
yTheory.Category.{v_2, u_2} D] (L : Categor…
· 使用引理 `CategoryTheory.Quotient.isLocalization_functor`：isLocalization_functor :
 (functor r).IsLocalization W
· 使用定理 `CategoryTheory.Functor.IsLocalization.of_equivalence_target`：of_equivale
nce_target {E : Type*} [Category* E] (L' : C ⥤ E) (eq : D ≌ E) [L.IsLocalization
 W] (e : L ⋙ eq.functor ≅ L') : L'.IsLocalization…
· 使用定理 `CategoryTheory.Functor.instIsEquivalenceQuotientHomRelLift`：∀ {C : Type 
u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {D : Type u_2}   [inst_1 : Ca
tegoryTheory.Category.{v_2, u_2} D] (L : Categor…
-/
lemma isLocalization_of_essSurj_of_full_of_exists_cylinders
    (L : C ⥤ D) [L.EssSurj] [L.Full] (W : MorphismProperty C) (hW : W.IsInvertedBy L)
    (hr : ∀ ⦃X Y : C⦄ (f₀ f₁ : X ⟶ Y) (_ : L.map f₀ = L.map f₁),
      ∃ (P : Precylinder X) (_ : P.LeftHomotopy f₀ f₁), W P.π) :
    L.IsLocalization W := by
  let F := Quotient.lift L.homRel L (by simp)
  have hW' : W.IsInvertedBy (Quotient.functor L.homRel) := fun _ _ f hf ↦ by
    have : IsIso (F.map ((Quotient.functor L.homRel).map f)) := hW _ hf
    apply isIso_of_reflects_iso _ F
  have := Quotient.isLocalization_functor L.homRel W hW' hr
  exact IsLocalization.of_equivalence_target (Quotient.functor L.homRel) W L
    F.asEquivalence (Iso.refl _)
/-
**CategoryTheory.Functor.isLocalization_of_essSurj_of_full_of_exists_pathObjects
** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：isLocalization_of_essSurj_of_full_of_exists_pathObjects (L : C ⥤ D) [L.Ess
Surj] [L.Full] (W : MorphismProperty C) (hW : W.IsInvertedBy L) (hr : forall ⦃X 
Y : C⦄ (f₀ f₁ : X ⟶ Y) (_ : L.map f₀ = L.map f₁), exists (P : PrepathObject Y) (
_ : P.RightHomotopy f₀ f₁), W P.ι) : L.IsLocalization W
参数：L : C ⥤ D；W : MorphismProperty C；hW : W.IsInvertedBy L；hr : forall ⦃X Y : C⦄ 
(f₀ f₁ : X ⟶ Y) (_ : L.map f₀ = L.map f₁), exists (P : PrepathObject Y) (_ : P.R
ightHomotopy f₀ f₁), W P.ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.IsLocalization.op_iff`：∀ {C : Type u_1} {D : Type
 u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.C
ategory.{v_2, u_2} D] (L : Categor…
· 使用引理 `CategoryTheory.Functor.isLocalization_of_essSurj_of_full_of_exists_cylin
ders`：isLocalization_of_essSurj_of_full_of_exists_cylinders (L : C ⥤ D) [L.EssSu
rj] [L.Full] (W : MorphismProperty C) (hW : W.IsInvertedBy L) (hr …
· 使用定理 `CategoryTheory.Functor.instEssSurjOppositeOp`：∀ (C : Type u₁) [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] (D : Type u₂) [inst_1 : CategoryTheory.Categor
y.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.instFullOppositeOp`：∀ {C : Type u₁} [inst : Categ
oryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{
v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.MorphismProperty.IsInvertedBy.op`：op {W : MorphismPropert
y C} {L : C ⥤ D} (h : W.IsInvertedBy L) : W.op.IsInvertedBy L.op
· 使用定理 `Quiver.Hom.op_inj`：Quiver.Hom.op_inj {X Y : C} : Function.Injective (Qui
ver.Hom.op : (X ⟶ Y) -> (Opposite.op Y ⟶ Opposite.op X))
-/
lemma isLocalization_of_essSurj_of_full_of_exists_pathObjects
    (L : C ⥤ D) [L.EssSurj] [L.Full] (W : MorphismProperty C) (hW : W.IsInvertedBy L)
    (hr : ∀ ⦃X Y : C⦄ (f₀ f₁ : X ⟶ Y) (_ : L.map f₀ = L.map f₁),
      ∃ (P : PrepathObject Y) (_ : P.RightHomotopy f₀ f₁), W P.ι) :
    L.IsLocalization W := by
  rw [← Functor.IsLocalization.op_iff]
  refine isLocalization_of_essSurj_of_full_of_exists_cylinders L.op W.op hW.op
    (fun X Y f₀ f₁ hf ↦ ?_)
  obtain ⟨P, h, hι⟩ := hr f₀.unop f₁.unop (Quiver.Hom.op_inj hf)
  exact ⟨P.op, h.op, hι⟩

end Functor

/-
**CategoryTheory.Quotient.isLocalization_functor'** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Quotient`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] (r : HomRel
 C) [CategoryTheory.Congruence r]   (W : CategoryTheory.MorphismProperty C),   W
.IsInvertedBy (CategoryTheory.Quotient.functor r) →     (∀ ⦃X Y : C⦄ (f₀ f₁ : X 
⟶ Y), r f₀ f₁ → ∃ P x, W P.ι) → (CategoryTheory.Quotient.functor r).IsLocalizati
on W
参数：r : HomRel C；W : CategoryTheory.MorphismProperty C；CategoryTheory.Quotient.fu
nctor r；∀ ⦃X Y : C⦄ (f₀ f₁ : X ⟶ Y), r f₀ f₁ → ∃ P x, W P.ι；CategoryTheory.Quoti
ent.functor r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.isLocalization_of_essSurj_of_full_of_exists_pathO
bjects`：isLocalization_of_essSurj_of_full_of_exists_pathObjects (L : C ⥤ D) [L.E
ssSurj] [L.Full] (W : MorphismProperty C) (hW : W.IsInvertedBy L) (h…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Quotient.functor_map_eq_iff`：functor_map_eq_iff [h : Cong
ruence r] {X Y : C} (f f' : X ⟶ Y) : (functor r).map f = (functor r).map f' ↔ r 
f f'
-/
lemma Quotient.isLocalization_functor' (r : HomRel C) [Congruence r] (W : MorphismProperty C)
    (hW : W.IsInvertedBy (functor r))
    (hr : ∀ ⦃X Y : C⦄ (f₀ f₁ : X ⟶ Y) (_ : r f₀ f₁),
      ∃ (P : PrepathObject Y) (_ : P.RightHomotopy f₀ f₁), W P.ι) :
    (functor r).IsLocalization W :=
  (functor r).isLocalization_of_essSurj_of_full_of_exists_pathObjects W hW
    (fun X Y f₀ f₁ hf ↦ by
      rw [functor_map_eq_iff] at hf
      exact hr _ _ hf)

end CategoryTheory

