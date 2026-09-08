/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Sites.DenseSubsite.Basic
public import Mathlib.CategoryTheory.Sites.LocallySurjective
/-!

# Preserving and reflecting local injectivity and surjectivity

This file proves that precomposition with a cocontinuous functor preserves local injectivity and
surjectivity of morphisms of presheaves, and that precomposition with a cover-preserving and
cover-dense functor reflects the same properties.
-/

public section

open CategoryTheory Functor

variable {C D A : Type*} [Category* C] [Category* D] [Category* A]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (H : C ⥤ D) {F G : Dᵒᵖ ⥤ A} (f : F ⟶ G)

namespace CategoryTheory

namespace Presheaf

variable {FA : A → A → Type*} {CA : A → Type*}
variable [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA]


/-
**CategoryTheory.Presheaf.isLocallyInjective_whisker** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.Presheaf`。
形式化陈述：isLocallyInjective_whisker [H.IsCocontinuous J K] [IsLocallyInjective K f]
 : IsLocallyInjective J (whiskerLeft H.op f) where equalizerSieve_mem x y h
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.cover_lift`：∀ {C : Type u_1} [inst : CategoryTheo
ry.Category.{v_1, u_1} C] {D : Type u_2}   [inst_1 : CategoryTheory.Category.{v_
2, u_2} D] (G : Categor…
· 使用引理 `CategoryTheory.Presheaf.equalizerSieve_mem`：equalizerSieve_mem [IsLocall
yInjective J φ] {X : Cᵒᵖ} (x y : ToType (F₁.obj X)) (h : φ.app X x = φ.app X y) 
: equalizerSieve x y in J X.unop
-/
lemma isLocallyInjective_whisker [H.IsCocontinuous J K] [IsLocallyInjective K f] :
    IsLocallyInjective J (whiskerLeft H.op f) where
  equalizerSieve_mem x y h := H.cover_lift J K (equalizerSieve_mem K f x y h)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Presheaf.isLocallyInjective_of_whisker** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.Presheaf`。
形式化陈述：isLocallyInjective_of_whisker (hH : CoverPreserving J K H) [H.IsCoverDense
 K] [IsLocallyInjective J (whiskerLeft H.op f)] : IsLocallyInjective K f where e
qualizerSieve_mem {X} a b h
参数：hH : CoverPreserving J K H；whiskerLeft H.op f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrothendieckTopology.transitive`：transitive (hS : S in J 
X) (R : Sieve X) (h : forall ⦃Y⦄ ⦃f : Y ⟶ X⦄, S f -> R.pullback f in J Y) : R in
 J X
· 使用定理 `CategoryTheory.Functor.is_cover_of_isCoverDense`：∀ {C : Type u_1} [inst 
: CategoryTheory.Category.{v_1, u_1} C] {D : Type u_2}   [inst_1 : CategoryTheor
y.Category.{v_2, u_2} D] (G : Categor…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Sieve.pullback_comp`：pullback_comp {f : Y ⟶ X} {g : Z ⟶ Y
} (S : Sieve X) : S.pullback (g ≫ f) = (S.pullback f).pullback g
· 使用定理 `CategoryTheory.GrothendieckTopology.pullback_stable`：pullback_stable (f 
: Y ⟶ X) (hS : S in J X) : S.pullback f in J Y
· 使用定理 `CategoryTheory.GrothendieckTopology.superset_covering`：superset_covering
 (Hss : S <= R) (sjx : S in J X) : R in J X
· 使用定理 `CategoryTheory.Sieve.functorPullback_pushforward_le`：functorPullback_pus
hforward_le (R : Sieve (F.obj X)) : (R.functorPullback F).functorPushforward F <
= R
· 使用定理 `CategoryTheory.Sieve.functorPushforward_monotone`：functorPushforward_mon
otone (X : C) : Monotone (Sieve.functorPushforward F : Sieve X -> Sieve (F.obj X
))
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
· 使用定理 `CategoryTheory.CoverPreserving.cover_preserve`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Catego
ry.{v₂, u₂} D]   {J : CategoryTheor…
· 使用引理 `CategoryTheory.Presheaf.equalizerSieve_mem`：equalizerSieve_mem [IsLocall
yInjective J φ] {X : Cᵒᵖ} (x y : ToType (F₁.obj X)) (h : φ.app X x = φ.app X y) 
: equalizerSieve x y in J X.unop
· 使用定理 `CategoryTheory.NatTrans.naturality_apply`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {D : Type u_1} [inst_1 : CategoryTheory.Category.{v_1
, u_1} D]   {FD : outParam (D …
-/
lemma isLocallyInjective_of_whisker (hH : CoverPreserving J K H)
    [H.IsCoverDense K] [IsLocallyInjective J (whiskerLeft H.op f)] : IsLocallyInjective K f where
  equalizerSieve_mem {X} a b h := by
    apply K.transitive (H.is_cover_of_isCoverDense K X.unop)
    intro Y g ⟨⟨Z, lift, m, fac⟩⟩
    rw [← fac, Sieve.pullback_comp]
    apply K.pullback_stable
    refine K.superset_covering (Sieve.functorPullback_pushforward_le H _) ?_
    refine K.superset_covering (Sieve.functorPushforward_monotone H _ ?_)
      (hH.cover_preserve <| equalizerSieve_mem J (whiskerLeft H.op f)
        (F.map m.op a) (F.map m.op b) ?_)
    · intro W q hq
      simpa using hq
    · simp only [comp_obj, op_obj, whiskerLeft_app, Opposite.op_unop]
      rw [NatTrans.naturality_apply, NatTrans.naturality_apply, h]
/-
**CategoryTheory.Presheaf.isLocallyInjective_whisker_iff** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.Presheaf`。
形式化陈述：isLocallyInjective_whisker_iff (hH : CoverPreserving J K H) [H.IsCocontinu
ous J K] [H.IsCoverDense K] : IsLocallyInjective J (whiskerLeft H.op f) ↔ IsLoca
llyInjective K f
参数：hH : CoverPreserving J K H。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Presheaf.isLocallyInjective_of_whisker`：isLocallyInjectiv
e_of_whisker (hH : CoverPreserving J K H) [H.IsCoverDense K] [IsLocallyInjective
 J (whiskerLeft H.op f)] : IsLocallyInjecti…
· 使用引理 `CategoryTheory.Presheaf.isLocallyInjective_whisker`：isLocallyInjective_w
hisker [H.IsCocontinuous J K] [IsLocallyInjective K f] : IsLocallyInjective J (w
hiskerLeft H.op f) where equalizerSieve_…
-/
lemma isLocallyInjective_whisker_iff (hH : CoverPreserving J K H) [H.IsCocontinuous J K]
    [H.IsCoverDense K] : IsLocallyInjective J (whiskerLeft H.op f) ↔ IsLocallyInjective K f :=
  ⟨fun _ ↦ isLocallyInjective_of_whisker J K H f hH,
    fun _ ↦ isLocallyInjective_whisker J K H f⟩
/-
**CategoryTheory.Presheaf.isLocallySurjective_whisker** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Presheaf`。
形式化陈述：isLocallySurjective_whisker [H.IsCocontinuous J K] [IsLocallySurjective K 
f] : IsLocallySurjective J (whiskerLeft H.op f) where imageSieve_mem a
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.cover_lift`：∀ {C : Type u_1} [inst : CategoryTheo
ry.Category.{v_1, u_1} C] {D : Type u_2}   [inst_1 : CategoryTheory.Category.{v_
2, u_2} D] (G : Categor…
· 使用引理 `CategoryTheory.Presheaf.imageSieve_mem`：imageSieve_mem {F G : Cᵒᵖ ⥤ A} (
f : F ⟶ G) [IsLocallySurjective J f] {U : Cᵒᵖ} (s : ToType (G.obj U)) : imageSie
ve f s in J U.unop
-/
lemma isLocallySurjective_whisker [H.IsCocontinuous J K] [IsLocallySurjective K f] :
    IsLocallySurjective J (whiskerLeft H.op f) where
  imageSieve_mem a := H.cover_lift J K (imageSieve_mem K f a)
/-
**CategoryTheory.Presheaf.isLocallySurjective_of_whisker** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.Presheaf`。
形式化陈述：isLocallySurjective_of_whisker (hH : CoverPreserving J K H) [H.IsCoverDens
e K] [IsLocallySurjective J (whiskerLeft H.op f)] : IsLocallySurjective K f wher
e imageSieve_mem {X} a
参数：hH : CoverPreserving J K H；whiskerLeft H.op f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrothendieckTopology.transitive`：transitive (hS : S in J 
X) (R : Sieve X) (h : forall ⦃Y⦄ ⦃f : Y ⟶ X⦄, S f -> R.pullback f in J Y) : R in
 J X
· 使用定理 `CategoryTheory.Functor.is_cover_of_isCoverDense`：∀ {C : Type u_1} [inst 
: CategoryTheory.Category.{v_1, u_1} C] {D : Type u_2}   [inst_1 : CategoryTheor
y.Category.{v_2, u_2} D] (G : Categor…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Sieve.pullback_comp`：pullback_comp {f : Y ⟶ X} {g : Z ⟶ Y
} (S : Sieve X) : S.pullback (g ≫ f) = (S.pullback f).pullback g
· 使用定理 `CategoryTheory.GrothendieckTopology.pullback_stable`：pullback_stable (f 
: Y ⟶ X) (hS : S in J X) : S.pullback f in J Y
· 使用定理 `CategoryTheory.CoverPreserving.cover_preserve`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Catego
ry.{v₂, u₂} D]   {J : CategoryTheor…
· 使用引理 `CategoryTheory.Presheaf.imageSieve_mem`：imageSieve_mem {F G : Cᵒᵖ ⥤ A} (
f : F ⟶ G) [IsLocallySurjective J f] {U : Cᵒᵖ} (s : ToType (G.obj U)) : imageSie
ve f s in J U.unop
· 使用定理 `CategoryTheory.GrothendieckTopology.superset_covering`：superset_covering
 (Hss : S <= R) (sjx : S in J X) : R in J X
· 使用定理 `CategoryTheory.Sieve.functorPullback_pushforward_le`：functorPullback_pus
hforward_le (R : Sieve (F.obj X)) : (R.functorPullback F).functorPushforward F <
= R
· 使用定理 `CategoryTheory.Sieve.functorPushforward_monotone`：functorPushforward_mon
otone (X : C) : Monotone (Sieve.functorPushforward F : Sieve X -> Sieve (F.obj X
))
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Sieve.functorPullback_apply`：∀ {C : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.
{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Sieve.pullback_apply`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {X Y : C} (h : Y ⟶ X) (S : CategoryTheory.Sieve X) (x :
 C)   (sl : x ⟶ Y), (Cate…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
-/
lemma isLocallySurjective_of_whisker (hH : CoverPreserving J K H)
    [H.IsCoverDense K] [IsLocallySurjective J (whiskerLeft H.op f)] : IsLocallySurjective K f where
  imageSieve_mem {X} a := by
    apply K.transitive (H.is_cover_of_isCoverDense K X)
    intro Y g ⟨⟨Z, lift, m, fac⟩⟩
    rw [← fac, Sieve.pullback_comp]
    apply K.pullback_stable
    have hh := hH.cover_preserve <| imageSieve_mem J (whiskerLeft H.op f) (G.map m.op a)
    refine K.superset_covering (Sieve.functorPullback_pushforward_le H _) ?_
    refine K.superset_covering (Sieve.functorPushforward_monotone H _ ?_) hh
    intro W q ⟨x, h⟩
    simp only [Sieve.functorPullback_apply, Presieve.functorPullback_mem, Sieve.pullback_apply]
    exact ⟨x, by simpa using! h⟩
/-
**CategoryTheory.Presheaf.isLocallySurjective_whisker_iff** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.Presheaf`。
形式化陈述：isLocallySurjective_whisker_iff (hH : CoverPreserving J K H) [H.IsCocontin
uous J K] [H.IsCoverDense K] : IsLocallySurjective J (whiskerLeft H.op f) ↔ IsLo
callySurjective K f
参数：hH : CoverPreserving J K H。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Presheaf.isLocallySurjective_of_whisker`：isLocallySurject
ive_of_whisker (hH : CoverPreserving J K H) [H.IsCoverDense K] [IsLocallySurject
ive J (whiskerLeft H.op f)] : IsLocallySurje…
· 使用引理 `CategoryTheory.Presheaf.isLocallySurjective_whisker`：isLocallySurjective
_whisker [H.IsCocontinuous J K] [IsLocallySurjective K f] : IsLocallySurjective 
J (whiskerLeft H.op f) where imageSieve_m…
-/
lemma isLocallySurjective_whisker_iff (hH : CoverPreserving J K H) [H.IsCocontinuous J K]
    [H.IsCoverDense K] : IsLocallySurjective J (whiskerLeft H.op f) ↔ IsLocallySurjective K f :=
  ⟨fun _ ↦ isLocallySurjective_of_whisker J K H f hH,
    fun _ ↦ isLocallySurjective_whisker J K H f⟩

end Presheaf

end CategoryTheory

