/-
Copyright (c) 2025 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Preadditive.Projective.Internal
public import Mathlib.Condensed.Light.Epi
public import Mathlib.Condensed.Light.Functors
public import Mathlib.Condensed.Light.Monoidal
/-!

# Characterization of internal projectivity in light condensed modules

This file gives an explicit condition on light condensed modules over a ring `R` to be internally
projective, namely the following:

`internallyProjective_iff_tensor_condition`: `P : LightCondMod R` is internally projective if and
only if, for all `A B : LightCondMod R`, for all epimorphisms `e : A ⟶ B`, for all
`S : LightProfinite` and all morphisms `g : P ⊗ R[S] ⟶ B`, there exists a `S' : LightProfinite`
with a surjection `π : S' ⟶ S` and a morphism `g' : P ⊗ R[S'] ⟶ A`, making the diagram
```
P ⊗ R[S'] --> A
  |           |
  v           v
P ⊗ R[S]  --> B
```
commute.

We also provide the analogous characterization with the tensor product commuted the other way around
(see `internallyProjective_iff_tensor_condition'`), and the special cases when `P` is the free
condensed module on a condensed set (`free_internallyProjective_iff_tensor_condition`,
`free_internallyProjective_iff_tensor_condition'`) and when `P` is the free condensed module on a
light profinite set (`free_lightProfinite_internallyProjective_iff_tensor_condition`/
`free_lightProfinite_internallyProjective_iff_tensor_condition'`).
-/

@[expose] public section

universe u

open CategoryTheory Category MonoidalCategory Functor Monoidal LaxMonoidal OplaxMonoidal

variable (R : Type u) [CommRing R]

namespace LightCondensed

/--
The `S`-valued points of the internal hom `A ⟶[LightCondMod R] B` are in bijection with
morphisms `A ⊗ R[S] ⟶ B`.
-/
/-
**LightCondensed.ihomPoints** 是 Mathlib 中的一个定义，位于命名空间 `LightCondensed`。
形式化陈述：ihomPoints (A B : LightCondMod.{u} R) (S : LightProfinite) : (A ⟶[LightCon
dMod R] B).obj.obj ⟨S⟩ ≃ ((A otimes ((free R).obj S.toCondensed)) ⟶ B)
参数：A B : LightCondMod.{u} R；S : LightProfinite。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The `S`-valued points of the internal hom `A ⟶[LightCondMod R] B` are in bijecti
on with
morphisms `A ⊗ R[S] ⟶ B`.
-/
noncomputable def ihomPoints (A B : LightCondMod.{u} R) (S : LightProfinite) :
    (A ⟶[LightCondMod R] B).obj.obj ⟨S⟩ ≃ ((A ⊗ ((free R).obj S.toCondensed)) ⟶ B) :=
  (((freeForgetAdjunction R).homEquiv _ _).trans
    (coherentTopology _).yonedaEquiv).symm.trans
      ((ihom.adjunction A).homEquiv _ _).symm
/-
**LightCondensed.ihomPoints_apply** 是 Mathlib 中的一个引理，位于命名空间 `LightCondensed`。
形式化陈述：ihomPoints_apply (A B : LightCondMod.{u} R) (S : LightProfinite) (x : (A ⟶
[LightCondMod R] B).obj.obj ⟨S⟩) : ihomPoints R A B S x = (MonoidalClosed.uncurr
y (((freeForgetAdjunction R).homEquiv _ _).symm ((coherentTopology LightProfinit
e.{u}).yonedaEquiv.symm x)))
参数：A B : LightCondMod.{u} R；S : LightProfinite；x : (A ⟶[LightCondMod R] B).obj.o
bj ⟨S⟩。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ihomPoints_apply (A B : LightCondMod.{u} R) (S : LightProfinite)
    (x : (A ⟶[LightCondMod R] B).obj.obj ⟨S⟩) :
    ihomPoints R A B S x = (MonoidalClosed.uncurry (((freeForgetAdjunction R).homEquiv _ _).symm
      ((coherentTopology LightProfinite.{u}).yonedaEquiv.symm x))) :=
  rfl
/-
**LightCondensed.ihomPoints_symm_apply** 是 Mathlib 中的一个引理，位于命名空间 `LightCondensed
`。
形式化陈述：ihomPoints_symm_apply (A B : LightCondMod.{u} R) (S : LightProfinite) (x :
 (A otimes ((free R).obj S.toCondensed)) ⟶ B) : (ihomPoints R A B S).symm x = (c
oherentTopology LightProfinite.{u}).yonedaEquiv ((freeForgetAdjunction R).homEqu
iv _ _ (MonoidalClosed.curry x))
参数：A B : LightCondMod.{u} R；S : LightProfinite；x : (A otimes ((free R).obj S.toC
ondensed)) ⟶ B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma ihomPoints_symm_apply (A B : LightCondMod.{u} R) (S : LightProfinite)
    (x : (A ⊗ ((free R).obj S.toCondensed)) ⟶ B) :
    (ihomPoints R A B S).symm x = (coherentTopology LightProfinite.{u}).yonedaEquiv
      ((freeForgetAdjunction R).homEquiv _ _ (MonoidalClosed.curry x)) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-
**LightCondensed.ihom_map_val_app** 是 Mathlib 中的一个引理，位于命名空间 `LightCondensed`。
形式化陈述：ihom_map_val_app (A B P : LightCondMod.{u} R) (S : LightProfinite) (e : A 
⟶ B) (x : (P ⟶[LightCondMod R] A).obj.obj ⟨S⟩) : (((ihom P).map e).hom.app ⟨S⟩) 
x = (ihomPoints R P B S).symm (ihomPoints R P A S x ≫ e)
参数：A B P : LightCondMod.{u} R；S : LightProfinite；e : A ⟶ B；x : (P ⟶[LightCondMod
 R] A).obj.obj ⟨S⟩。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `CategoryTheory.instPrecoherentOfFinitaryPreExtensiveOfPreregular`：∀ (C :
 Type u_1) [inst : CategoryTheory.Category.{v_1, u_1} C] [CategoryTheory.Finitar
yPreExtensive C]   [CategoryTheory.Preregular C], Cate…
· 使用定理 `CategoryTheory.FinitaryExtensive.toFinitaryPreExtensive`：∀ {C : Type u} 
[inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.FinitaryExtensive C], 
  CategoryTheory.FinitaryPreExtensive C
· 使用定理 `CompHausLike.instFinitaryExtensiveOfHasExplicitPullbacksOfInclusions`：∀ 
{P : TopCat → Prop} [inst : CompHausLike.HasExplicitFiniteCoproducts P]   [CompH
ausLike.HasExplicitPullbacksOfInclusions P], CategoryTheor…
· 使用定理 `LightProfinite.instHasExplicitFiniteCoproductsAndTotallyDisconnectedSpac
eCarrierSecondCountableTopology`：CompHausLike.HasExplicitFiniteCoproducts fun Y 
=> TotallyDisconnectedSpace ↑Y ∧ SecondCountableTopology ↑Y
· 使用定理 `CompHausLike.instHasExplicitPullbacksOfInclusionsOfHasExplicitPullbacks`
：∀ {P : TopCat → Prop} [CompHausLike.HasExplicitPullbacks P] [inst : CompHausLik
e.HasExplicitFiniteCoproducts P],   CompHausLike.HasExplicitP…
· 使用定理 `LightProfinite.instHasExplicitPullbacksAndTotallyDisconnectedSpaceCarrie
rSecondCountableTopology`：CompHausLike.HasExplicitPullbacks fun Y => TotallyDisc
onnectedSpace ↑Y ∧ SecondCountableTopology ↑Y
· 使用定理 `LightProfinite.instPreregular`：CategoryTheory.Preregular LightProfinite
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `CategoryTheory.GrothendieckTopology.yonedaEquiv_comp`：yonedaEquiv_comp {
X : C} {F G : Sheaf J (Type v)} (α : J.yoneda.obj X ⟶ F) (β : F ⟶ G) : J.yonedaE
quiv (α ≫ β) = β.hom.app _ (J.yonedaEquiv …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma ihom_map_val_app (A B P : LightCondMod.{u} R) (S : LightProfinite) (e : A ⟶ B)
    (x : (P ⟶[LightCondMod R] A).obj.obj ⟨S⟩) :
    (((ihom P).map e).hom.app ⟨S⟩) x = (ihomPoints R P B S).symm (ihomPoints R P A S x ≫ e) := by
  apply (ihomPoints R P B S).injective
  simp only [ihomPoints_apply, ← MonoidalClosed.uncurry_natural_right,
    ← Adjunction.homEquiv_naturality_right_symm, Equiv.apply_symm_apply]
  congr
  apply (coherentTopology LightProfinite.{u}).yonedaEquiv.injective
  simp [dsimp% GrothendieckTopology.yonedaEquiv_comp]

set_option backward.isDefEq.respectTransparency false in
/-
**LightCondensed.ihomPoints_symm_comp** 是 Mathlib 中的一个引理，位于命名空间 `LightCondensed`
。
形式化陈述：ihomPoints_symm_comp (B P : LightCondMod.{u} R) (S S' : LightProfinite) (π
 : S ⟶ S') (f : P otimes (free R).obj S'.toCondensed ⟶ B) : (ihomPoints R P B S)
.symm (P ◁ (free R).map (lightProfiniteToLightCondSet.map π) ≫ f) = ((P ⟶[LightC
ondMod R] B).obj.map π.op) ((ihomPoints R P B S').symm f)
参数：B P : LightCondMod.{u} R；S S' : LightProfinite；π : S ⟶ S'；f : P otimes (free 
R).obj S'.toCondensed ⟶ B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `CategoryTheory.instPrecoherentOfFinitaryPreExtensiveOfPreregular`：∀ (C :
 Type u_1) [inst : CategoryTheory.Category.{v_1, u_1} C] [CategoryTheory.Finitar
yPreExtensive C]   [CategoryTheory.Preregular C], Cate…
· 使用定理 `CategoryTheory.FinitaryExtensive.toFinitaryPreExtensive`：∀ {C : Type u} 
[inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.FinitaryExtensive C], 
  CategoryTheory.FinitaryPreExtensive C
· 使用定理 `CompHausLike.instFinitaryExtensiveOfHasExplicitPullbacksOfInclusions`：∀ 
{P : TopCat → Prop} [inst : CompHausLike.HasExplicitFiniteCoproducts P]   [CompH
ausLike.HasExplicitPullbacksOfInclusions P], CategoryTheor…
· 使用定理 `LightProfinite.instHasExplicitFiniteCoproductsAndTotallyDisconnectedSpac
eCarrierSecondCountableTopology`：CompHausLike.HasExplicitFiniteCoproducts fun Y 
=> TotallyDisconnectedSpace ↑Y ∧ SecondCountableTopology ↑Y
· 使用定理 `CompHausLike.instHasExplicitPullbacksOfInclusionsOfHasExplicitPullbacks`
：∀ {P : TopCat → Prop} [CompHausLike.HasExplicitPullbacks P] [inst : CompHausLik
e.HasExplicitFiniteCoproducts P],   CompHausLike.HasExplicitP…
· 使用定理 `LightProfinite.instHasExplicitPullbacksAndTotallyDisconnectedSpaceCarrie
rSecondCountableTopology`：CompHausLike.HasExplicitPullbacks fun Y => TotallyDisc
onnectedSpace ↑Y ∧ SecondCountableTopology ↑Y
· 使用定理 `LightProfinite.instPreregular`：CategoryTheory.Preregular LightProfinite
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.MonoidalClosed.curry_natural_left`：curry_natural_left (f 
: X ⟶ X') (g : A otimes X' ⟶ Y) : curry (_ ◁ f ≫ g) = f ≫ curry g
· 使用定理 `CategoryTheory.Adjunction.homEquiv_apply`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Adjunction.unit_naturality_assoc`：∀ {C : Type u₁} [inst :
 CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cate
gory.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.GrothendieckTopology.yonedaEquiv_naturality`：yonedaEquiv_
naturality {X Y : C} {F : Sheaf J (Type v)} (f : J.yoneda.obj X ⟶ F) (g : Y ⟶ X)
 : F.obj.map g.op (J.yonedaEquiv f) = J.yonedaEq…
-/
lemma ihomPoints_symm_comp (B P : LightCondMod.{u} R) (S S' : LightProfinite) (π : S ⟶ S')
    (f : P ⊗ (free R).obj S'.toCondensed ⟶ B) :
    (ihomPoints R P B S).symm (P ◁ (free R).map (lightProfiniteToLightCondSet.map π) ≫ f) =
      ((P ⟶[LightCondMod R] B).obj.map π.op) ((ihomPoints R P B S').symm f) := by
  simpa [ihomPoints_symm_apply, MonoidalClosed.curry_natural_left, Adjunction.homEquiv_apply] using!
    (GrothendieckTopology.yonedaEquiv_naturality _ _ _).symm

set_option backward.defeqAttrib.useBackward true in
/--
`P : LightCondMod R` is internally projective if and
only if, for all `A B : LightCondMod R`, for all epimorphisms `e : A ⟶ B`, for all
`S : LightProfinite` and all morphisms `g : P ⊗ R[S] ⟶ B`, there exists a `S' : LightProfinite`
with a surjection `π : S' ⟶ S` and a morphism `g' : P ⊗ R[S'] ⟶ A`, making the diagram
```
P ⊗ R[S'] --> A
  |           |
  v           v
P ⊗ R[S]  --> B
```
commute.
-/
/-
**LightCondensed.internallyProjective_iff_tensor_condition** 是 Mathlib 中的一个引理，位于
命名空间 `LightCondensed`。
形式化陈述：internallyProjective_iff_tensor_condition (P : LightCondMod R) : Internall
yProjective P ↔ forall {A B : LightCondMod R} (e : A ⟶ B) [Epi e], (forall (S : 
LightProfinite) (g : P otimes (free R).obj S.toCondensed ⟶ B), exists (S' : Ligh
tProfinite) (π : S' ⟶ S) (_ : Function.Surjective π) (g' : P otimes (free R).obj
 S'.toCondensed ⟶ A), (P ◁ ((lightProfiniteToLightCondSet ⋙ free R).map π)) ≫ g 
= g' ≫ e)
参数：P : LightCondMod R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.PreservesEpimorphisms.preserves`：∀ {C : Type u₁} 
{inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheo
ry.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LightCondMod.epi_iff_locallySurjective_on_lightProfinite`：epi_iff_locall
ySurjective_on_lightProfinite : Epi f ↔ forall (S : LightProfinite) (y : Y.obj.o
bj ⟨S⟩), (exists (S' : LightProfinite) (φ : S'…
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用引理 `LightCondensed.ihom_map_val_app`：ihom_map_val_app (A B P : LightCondMod.
{u} R) (S : LightProfinite) (e : A ⟶ B) (x : (P ⟶[LightCondMod R] A).obj.obj ⟨S⟩
) : (((ihom P).map e)…
· 使用引理 `LightCondensed.ihomPoints_symm_comp`：ihomPoints_symm_comp (B P : LightCo
ndMod.{u} R) (S S' : LightProfinite) (π : S ⟶ S') (f : P otimes (free R).obj S'.
toCondensed ⟶ B) : (ihomP…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
`P : LightCondMod R` is internally projective if and
only if, for all `A B : LightCondMod R`, for all epimorphisms `e : A ⟶ B`, for a
ll
`S : LightProfinite` and all morphisms `g : P ⊗ R[S] ⟶ B`, there exists a `S' : 
LightProfinite`
with a surjection `π : S' ⟶ S` and a morphism `g' : P ⊗ R[S'] ⟶ A`, making the d
iagram
```
P ⊗ R[S'] --> A
  |           |
  v           v
P ⊗ R[S]  --> B
```
commute.
-/
lemma internallyProjective_iff_tensor_condition (P : LightCondMod R) : InternallyProjective P ↔
    ∀ {A B : LightCondMod R} (e : A ⟶ B) [Epi e],
      (∀ (S : LightProfinite) (g : P ⊗ (free R).obj S.toCondensed ⟶ B), ∃ (S' : LightProfinite)
        (π : S' ⟶ S) (_ : Function.Surjective π) (g' : P ⊗ (free R).obj S'.toCondensed ⟶ A),
          (P ◁ ((lightProfiniteToLightCondSet ⋙ free R).map π)) ≫ g = g' ≫ e) := by
  refine ⟨fun ⟨h⟩ A B e he S g ↦ ?_, fun h ↦ ⟨⟨fun {A B} e he ↦ ?_⟩⟩⟩
  · have hh := h.1 e
    rw [LightCondMod.epi_iff_locallySurjective_on_lightProfinite] at hh
    specialize hh S ((ihomPoints R P B S).symm g)
    obtain ⟨S', π, hπ, g', hh⟩ := hh
    refine ⟨S', π, hπ, (ihomPoints _ _ _ _) g', ?_⟩
    rw [ihom_map_val_app] at hh
    apply (ihomPoints R P B S').symm.injective
    rw [hh]
    exact ihomPoints_symm_comp R B P S' S π g
  · rw [LightCondMod.epi_iff_locallySurjective_on_lightProfinite]
    intro S g
    specialize h e S ((ihomPoints _ _ _ _) g)
    obtain ⟨S', π, hπ, g', hh⟩ := h
    refine ⟨S', π, hπ, (ihomPoints _ _ _ _).symm g', ?_⟩
    rw [ihom_map_val_app]
    have := ihomPoints_symm_comp R B P S' S π ((ihomPoints R P B S) g)
    dsimp at hh
    rw [hh] at this
    simp [this, Quiver.Hom.op]

set_option backward.defeqAttrib.useBackward true in
/--
`P : LightCondMod R` is internally projective if and
only if, for all `A B : LightCondMod R`, for all epimorphisms `e : A ⟶ B`, for all
`S : LightProfinite` and all morphisms `g : R[S] ⊗ P ⟶ B`, there exists a `S' : LightProfinite`
with a surjection `π : S' ⟶ S` and a morphism `g' : R[S'] ⊗ P ⟶ A`, making the diagram
```
R[S'] ⊗ P --> A
  |           |
  v           v
R[S] ⊗ P  --> B
```
commute.
-/
/-
**LightCondensed.internallyProjective_iff_tensor_condition'** 是 Mathlib 中的一个引理，位
于命名空间 `LightCondensed`。
形式化陈述：internallyProjective_iff_tensor_condition' (P : LightCondMod R) : Internal
lyProjective P ↔ forall {A B : LightCondMod R} (e : A ⟶ B) [Epi e], (forall (S :
 LightProfinite) (g : (free R).obj S.toCondensed otimes P ⟶ B), exists (S' : Lig
htProfinite) (π : S' ⟶ S) (_ : Function.Surjective π) (g' : (free R).obj S'.toCo
ndensed otimes P ⟶ A), (((lightProfiniteToLightCondSet ⋙ free R).map π) ▷ P) ≫ g
 = g' ≫ e)
参数：P : LightCondMod R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LightCondensed.internallyProjective_iff_tensor_condition`：internallyProj
ective_iff_tensor_condition (P : LightCondMod R) : InternallyProjective P ↔ fora
ll {A B : LightCondMod R} (e : A ⟶ B) [Epi e],…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.BraidedCategory.braiding_naturality_right_assoc`：∀ {C : T
ype u} {inst : CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Monoid
alCategory C}   [self : CategoryTheory.BraidedCatego…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.BraidedCategory.braiding_inv_naturality_left_assoc`：∀ {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Mon
oidalCategory C]   [inst_2 : CategoryTheory.BraidedCate…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …

--- 原说明 ---
`P : LightCondMod R` is internally projective if and
only if, for all `A B : LightCondMod R`, for all epimorphisms `e : A ⟶ B`, for a
ll
`S : LightProfinite` and all morphisms `g : R[S] ⊗ P ⟶ B`, there exists a `S' : 
LightProfinite`
with a surjection `π : S' ⟶ S` and a morphism `g' : R[S'] ⊗ P ⟶ A`, making the d
iagram
```
R[S'] ⊗ P --> A
  |           |
  v           v
R[S] ⊗ P  --> B
```
commute.
-/
lemma internallyProjective_iff_tensor_condition' (P : LightCondMod R) : InternallyProjective P ↔
    ∀ {A B : LightCondMod R} (e : A ⟶ B) [Epi e],
      (∀ (S : LightProfinite) (g : (free R).obj S.toCondensed ⊗ P ⟶ B), ∃ (S' : LightProfinite)
        (π : S' ⟶ S) (_ : Function.Surjective π) (g' : (free R).obj S'.toCondensed ⊗ P ⟶ A),
          (((lightProfiniteToLightCondSet ⋙ free R).map π) ▷ P) ≫ g = g' ≫ e) := by
  rw [internallyProjective_iff_tensor_condition]
  refine ⟨fun h A B e he S g ↦ ?_, fun h A B e he S g ↦ ?_⟩
  · specialize h e S ((β_ _ _).hom ≫ g)
    obtain ⟨S', π, hπ, g', hh⟩ := h
    refine ⟨S', π, hπ, (β_ _ _).inv ≫ g', ?_⟩
    simp [← hh]
  · specialize h e S ((β_ _ _).inv ≫ g)
    obtain ⟨S', π, hπ, g', hh⟩ := h
    refine ⟨S', π, hπ, (β_ _ _).hom ≫ g', ?_⟩
    simp [← hh]

/--
Given a `P : LightCondSet`, the light free light condensed module `R[P]` is internally projective if
and only if, for all `A B : LightCondMod R`, for all epimorphisms `e : A ⟶ B`, for all
`S : LightProfinite` and all morphisms `g : R[P × S] ⟶ B`, there exists a `S' : LightProfinite`
with a surjection `π : S' ⟶ S` and a morphism `g' : R[P × S'] ⟶ A`, making the diagram
```
R[P × S'] --> A
  |           |
  v           v
R[P × S]  --> B
```
commute.
-/
/-
**LightCondensed.free_internallyProjective_iff_tensor_condition** 是 Mathlib 中的一个
引理，位于命名空间 `LightCondensed`。
形式化陈述：free_internallyProjective_iff_tensor_condition (P : LightCondSet.{u}) : In
ternallyProjective ((free R).obj P) ↔ forall {A B : LightCondMod R} (e : A ⟶ B) 
[Epi e], (forall (S : LightProfinite) (g : (free R).obj (P otimes S.toCondensed)
 ⟶ B), exists (S' : LightProfinite) (π : S' ⟶ S) (_ : Function.Surjective π) (g'
 : (free R).obj (P otimes S'.toCondensed) ⟶ A), ((free R).map (P ◁ ((lightProfin
iteToLightCondSet).map π))) ≫ g = g' ≫ e)
参数：P : LightCondSet.{u}。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Sheaf.instIsMonoidalFunctorOppositeIsSheaf`：∀ {C : Type u
₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {A : Type u₂} [inst_1 : CategoryT
heory.Category.{v₂, u₂} A]   (J : CategoryTheor…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LightCondensed.internallyProjective_iff_tensor_condition`：internallyProj
ective_iff_tensor_condition (P : LightCondMod R) : InternallyProjective P ↔ fora
ll {A B : LightCondMod R} (e : A ⟶ B) [Epi e],…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Functor.Monoidal.μIso_inv`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.MonoidalCategory C] {D : 
Type u₂}   [inst_2 : CategoryT…
· 使用定理 `CategoryTheory.Functor.OplaxMonoidal.δ_natural_right`：∀ {C : Type u₁} {i
nst : CategoryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCateg
ory C} {D : Type u₂}   {inst_2 : CategoryT…
· 使用定理 `CategoryTheory.Functor.Monoidal.μIso_hom`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.MonoidalCategory C] {D : 
Type u₂}   [inst_2 : CategoryT…
· 使用定理 `CategoryTheory.Functor.Monoidal.δ_μ`：∀ {C : Type u₁} {inst : CategoryThe
ory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} {D : Type 
u₂}   {inst_2 : CategoryT…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Functor.Monoidal.μ_δ`：∀ {C : Type u₁} {inst : CategoryThe
ory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} {D : Type 
u₂}   {inst_2 : CategoryT…

--- 原说明 ---
Given a `P : LightCondSet`, the light free light condensed module `R[P]` is inte
rnally projective if
and only if, for all `A B : LightCondMod R`, for all epimorphisms `e : A ⟶ B`, f
or all
`S : LightProfinite` and all morphisms `g : R[P × S] ⟶ B`, there exists a `S' : 
LightProfinite`
with a surjection `π : S' ⟶ S` and a morphism `g' : R[P × S'] ⟶ A`, making the d
iagram
```
R[P × S'] --> A
  |           |
  v           v
R[P × S]  --> B
```
commute.
-/
lemma free_internallyProjective_iff_tensor_condition (P : LightCondSet.{u}) :
    InternallyProjective ((free R).obj P) ↔
      ∀ {A B : LightCondMod R} (e : A ⟶ B) [Epi e], (∀ (S : LightProfinite)
        (g : (free R).obj (P ⊗ S.toCondensed) ⟶ B), ∃ (S' : LightProfinite)
          (π : S' ⟶ S) (_ : Function.Surjective π) (g' : (free R).obj (P ⊗ S'.toCondensed) ⟶ A),
            ((free R).map (P ◁ ((lightProfiniteToLightCondSet).map π))) ≫ g = g' ≫ e) := by
  rw [internallyProjective_iff_tensor_condition]
  refine ⟨fun h A B e he S g ↦ ?_, fun h A B e he S g ↦ ?_⟩
  · specialize h e S ((μIso (free R) _ _).hom ≫ g)
    obtain ⟨S', π, hπ, g', hh⟩ := h
    refine ⟨S', π, hπ, (μIso (free R) _ _).inv ≫ g', ?_⟩
    rw [assoc, ← hh]
    simp only [← assoc]
    -- Generated by `simp?`. Leaving it unsqueezed is too slow
    simp only [μIso_hom, μIso_inv, Functor.comp_map, δ_natural_right, assoc, δ_μ, comp_id]
  · specialize h e S ((μIso (free R) _ _).inv ≫ g)
    obtain ⟨S', π, hπ, g', hh⟩ := h
    refine ⟨S', π, hπ, (μIso (free R) _ _).hom ≫ g', ?_⟩
    rw [assoc, ← hh, ← assoc, ← assoc]
    -- Generated by `simp? [← μ_natural_right]`.
    -- Leaving it unsqueezed is too slow
    simp only [Functor.comp_map, μIso_hom, ← μ_natural_right, μIso_inv, assoc, μ_δ,
      comp_id]

set_option backward.defeqAttrib.useBackward true in
/--
Given a `P : LightCondSet`, the light free light condensed module `R[P]` is internally projective if
and only if, for all `A B : LightCondMod R`, for all epimorphisms `e : A ⟶ B`, for all
`S : LightProfinite` and all morphisms `g : R[S × P] ⟶ B`, there exists a `S' : LightProfinite`
with a surjection `π : S' ⟶ S` and a morphism `g' : R[S' × P] ⟶ A`, making the diagram
```
R[S' × P] --> A
  |           |
  v           v
R[S × P]  --> B
```
commute.
-/
/-
**LightCondensed.free_internallyProjective_iff_tensor_condition'** 是 Mathlib 中的一
个引理，位于命名空间 `LightCondensed`。
形式化陈述：free_internallyProjective_iff_tensor_condition' (P : LightCondSet.{u}) : I
nternallyProjective ((free R).obj P) ↔ forall {A B : LightCondMod R} (e : A ⟶ B)
 [Epi e], (forall (S : LightProfinite) (g : (free R).obj (S.toCondensed otimes P
) ⟶ B), exists (S' : LightProfinite) (π : S' ⟶ S) (_ : Function.Surjective π) (g
' : (free R).obj (S'.toCondensed otimes P) ⟶ A), ((free R).map (((lightProfinite
ToLightCondSet).map π) ▷ P)) ≫ g = g' ≫ e)
参数：P : LightCondSet.{u}。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Sheaf.instIsMonoidalFunctorOppositeIsSheaf`：∀ {C : Type u
₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {A : Type u₂} [inst_1 : CategoryT
heory.Category.{v₂, u₂} A]   (J : CategoryTheor…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LightCondensed.internallyProjective_iff_tensor_condition'`：internallyPro
jective_iff_tensor_condition' (P : LightCondMod R) : InternallyProjective P ↔ fo
rall {A B : LightCondMod R} (e : A ⟶ B) [Epi e]…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Functor.LaxMonoidal.μ_natural_left_assoc`：∀ {C : Type u₁}
 {inst : CategoryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCa
tegory C} {D : Type u₂}   {inst_2 : CategoryT…
· 使用定理 `CategoryTheory.Functor.Monoidal.δ_μ_assoc`：∀ {C : Type u₁} {inst : Categ
oryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} {D :
 Type u₂}   {inst_2 : CategoryT…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.Monoidal.μ_δ`：∀ {C : Type u₁} {inst : CategoryThe
ory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} {D : Type 
u₂}   {inst_2 : CategoryT…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…

--- 原说明 ---
Given a `P : LightCondSet`, the light free light condensed module `R[P]` is inte
rnally projective if
and only if, for all `A B : LightCondMod R`, for all epimorphisms `e : A ⟶ B`, f
or all
`S : LightProfinite` and all morphisms `g : R[S × P] ⟶ B`, there exists a `S' : 
LightProfinite`
with a surjection `π : S' ⟶ S` and a morphism `g' : R[S' × P] ⟶ A`, making the d
iagram
```
R[S' × P] --> A
  |           |
  v           v
R[S × P]  --> B
```
commute.
-/
lemma free_internallyProjective_iff_tensor_condition' (P : LightCondSet.{u}) :
    InternallyProjective ((free R).obj P) ↔
      ∀ {A B : LightCondMod R} (e : A ⟶ B) [Epi e], (∀ (S : LightProfinite)
        (g : (free R).obj (S.toCondensed ⊗ P) ⟶ B), ∃ (S' : LightProfinite)
          (π : S' ⟶ S) (_ : Function.Surjective π) (g' : (free R).obj (S'.toCondensed ⊗ P) ⟶ A),
            ((free R).map (((lightProfiniteToLightCondSet).map π) ▷ P)) ≫ g = g' ≫ e) := by
  rw [internallyProjective_iff_tensor_condition']
  refine ⟨fun h A B e he S g ↦ ?_, fun h A B e he S g ↦ ?_⟩
  · specialize h e S ((μIso (free R) _ _).hom ≫ g)
    obtain ⟨S', π, hπ, g', hh⟩ := h
    refine ⟨S', π, hπ, (μIso (free R) _ _).inv ≫ g', ?_⟩
    rw [assoc, ← hh]
    -- Generated by `simp?`. Leaving it unsqueezed is too slow
    simp only [μIso_inv, comp_obj, Functor.comp_map, μIso_hom, μ_natural_left_assoc, δ_μ_assoc]
  · specialize h e S ((μIso (free R) _ _).inv ≫ g)
    obtain ⟨S', π, hπ, g', hh⟩ := h
    refine ⟨S', π, hπ, (μIso (free R) _ _).hom ≫ g', ?_⟩
    rw [assoc, ← hh, ← assoc, ← assoc]
    -- Generated by `simp? [← μ_natural_left]`
    -- Leaving it unsqueezed is too slow.
    simp only [comp_obj, Functor.comp_map, μIso_hom, ← μ_natural_left, μIso_inv, assoc, μ_δ,
      comp_id]

attribute [-simp] ObjectProperty.whiskerLeft_def ObjectProperty.whiskerRight_def

/--
Given a `P : LightProfinite`, the light free light condensed module `R[P]` is internally projective
if and only if, for all `A B : LightCondMod R`, for all epimorphisms `e : A ⟶ B`, for all
`S : LightProfinite` and all morphisms `g : R[P × S] ⟶ B`, there exists a `S' : LightProfinite`
with a surjection `π : S' ⟶ S` and a morphism `g' : R[P × S'] ⟶ A`, making the diagram
```
R[P × S'] --> A
  |           |
  v           v
R[P × S]  --> B
```
commute.
-/
/-
**LightCondensed.free_lightProfinite_internallyProjective_iff_tensor_condition**
 是 Mathlib 中的一个引理，位于命名空间 `LightCondensed`。
形式化陈述：free_lightProfinite_internallyProjective_iff_tensor_condition (P : LightPr
ofinite.{u}) : InternallyProjective ((free R).obj P.toCondensed) ↔ forall {A B :
 LightCondMod R} (e : A ⟶ B) [Epi e], (forall (S : LightProfinite) (g : (free R)
.obj ((P otimes S).toCondensed) ⟶ B), exists (S' : LightProfinite) (π : S' ⟶ S) 
(_ : Function.Surjective π) (g' : (free R).obj (P otimes S').toCondensed ⟶ A), (
(free R).map (lightProfiniteToLightCondSet.map (P ◁ π))) ≫ g = g' ≫ e)
参数：P : LightProfinite.{u}。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Sheaf.instIsMonoidalFunctorOppositeIsSheaf`：∀ {C : Type u
₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {A : Type u₂} [inst_1 : CategoryT
heory.Category.{v₂, u₂} A]   (J : CategoryTheor…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LightCondensed.free_internallyProjective_iff_tensor_condition`：free_inte
rnallyProjective_iff_tensor_condition (P : LightCondSet.{u}) : InternallyProject
ive ((free R).obj P) ↔ forall {A B : LightCondMod R…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Functor.Monoidal.μIso_inv`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.MonoidalCategory C] {D : 
Type u₂}   [inst_2 : CategoryT…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.Monoidal.μIso_hom`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.MonoidalCategory C] {D : 
Type u₂}   [inst_2 : CategoryT…
· 使用定理 `CategoryTheory.Functor.LaxMonoidal.μ_natural_right`：∀ {C : Type u₁} {ins
t : CategoryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategor
y C} {D : Type u₂}   {inst_2 : CategoryT…
· 使用定理 `CategoryTheory.Functor.Monoidal.δ_μ_assoc`：∀ {C : Type u₁} {inst : Categ
oryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} {D :
 Type u₂}   {inst_2 : CategoryT…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Functor.Monoidal.μ_δ`：∀ {C : Type u₁} {inst : CategoryThe
ory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} {D : Type 
u₂}   {inst_2 : CategoryT…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…

--- 原说明 ---
Given a `P : LightProfinite`, the light free light condensed module `R[P]` is in
ternally projective
if and only if, for all `A B : LightCondMod R`, for all epimorphisms `e : A ⟶ B`
, for all
`S : LightProfinite` and all morphisms `g : R[P × S] ⟶ B`, there exists a `S' : 
LightProfinite`
with a surjection `π : S' ⟶ S` and a morphism `g' : R[P × S'] ⟶ A`, making the d
iagram
```
R[P × S'] --> A
  |           |
  v           v
R[P × S]  --> B
```
commute.
-/
lemma free_lightProfinite_internallyProjective_iff_tensor_condition (P : LightProfinite.{u}) :
    InternallyProjective ((free R).obj P.toCondensed) ↔
      ∀ {A B : LightCondMod R} (e : A ⟶ B) [Epi e], (∀ (S : LightProfinite)
        (g : (free R).obj ((P ⊗ S).toCondensed) ⟶ B), ∃ (S' : LightProfinite)
          (π : S' ⟶ S) (_ : Function.Surjective π) (g' : (free R).obj (P ⊗ S').toCondensed ⟶ A),
            ((free R).map (lightProfiniteToLightCondSet.map (P ◁ π))) ≫ g = g' ≫ e) := by
  rw [free_internallyProjective_iff_tensor_condition]
  refine ⟨fun h A B e he S g ↦ ?_, fun h A B e he S g ↦ ?_⟩
  · specialize h e S ((free R).map (μIso lightProfiniteToLightCondSet _ _).hom ≫ g)
    obtain ⟨S', π, hπ, g', hh⟩ := h
    refine ⟨S', π, hπ, (free R).map (μIso
        lightProfiniteToLightCondSet _ _).inv ≫ g', ?_⟩
    rw [assoc, ← hh]
    simp [-map_comp, ← map_comp_assoc]
  · specialize h e S ((free R).map (μIso lightProfiniteToLightCondSet _ _).inv ≫ g)
    obtain ⟨S', π, hπ, g', hh⟩ := h
    refine ⟨S', π, hπ, (free R).map
      (μIso lightProfiniteToLightCondSet _ _).hom ≫ g', ?_⟩
    rw [assoc, ← hh]
    simp [-map_comp, ← map_comp_assoc, ← μ_natural_right_assoc]

/--
Given a `P : LightProfinite`, the light free light condensed module `R[P]` is internally projective
if and only if, for all `A B : LightCondMod R`, for all epimorphisms `e : A ⟶ B`, for all
`S : LightProfinite` and all morphisms `g : R[S × P] ⟶ B`, there exists a `S' : LightProfinite`
with a surjection `π : S' ⟶ S` and a morphism `g' : R[S' × P] ⟶ A`, making the diagram
```
R[S' × P] --> A
  |           |
  v           v
R[S × P]  --> B
```
commute.
-/
/-
**LightCondensed.free_lightProfinite_internallyProjective_iff_tensor_condition'*
* 是 Mathlib 中的一个引理，位于命名空间 `LightCondensed`。
形式化陈述：free_lightProfinite_internallyProjective_iff_tensor_condition' (P : LightP
rofinite.{u}) : InternallyProjective ((free R).obj P.toCondensed) ↔ forall {A B 
: LightCondMod R} (e : A ⟶ B) [Epi e], (forall (S : LightProfinite) (g : (free R
).obj ((S otimes P).toCondensed) ⟶ B), exists (S' : LightProfinite) (π : S' ⟶ S)
 (_ : Function.Surjective π) (g' : (free R).obj (S' otimes P).toCondensed ⟶ A), 
((free R).map (lightProfiniteToLightCondSet.map (π ▷ P))) ≫ g = g' ≫ e)
参数：P : LightProfinite.{u}。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Sheaf.instIsMonoidalFunctorOppositeIsSheaf`：∀ {C : Type u
₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {A : Type u₂} [inst_1 : CategoryT
heory.Category.{v₂, u₂} A]   (J : CategoryTheor…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LightCondensed.free_internallyProjective_iff_tensor_condition'`：free_int
ernallyProjective_iff_tensor_condition' (P : LightCondSet.{u}) : InternallyProje
ctive ((free R).obj P) ↔ forall {A B : LightCondMod …
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Functor.Monoidal.μIso_inv`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.MonoidalCategory C] {D : 
Type u₂}   [inst_2 : CategoryT…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.Monoidal.μIso_hom`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.MonoidalCategory C] {D : 
Type u₂}   [inst_2 : CategoryT…
· 使用定理 `CategoryTheory.Functor.LaxMonoidal.μ_natural_left`：∀ {C : Type u₁} {inst
 : CategoryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory
 C} {D : Type u₂}   {inst_2 : CategoryT…
· 使用定理 `CategoryTheory.Functor.Monoidal.δ_μ_assoc`：∀ {C : Type u₁} {inst : Categ
oryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} {D :
 Type u₂}   {inst_2 : CategoryT…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Functor.Monoidal.μ_δ`：∀ {C : Type u₁} {inst : CategoryThe
ory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} {D : Type 
u₂}   {inst_2 : CategoryT…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…

--- 原说明 ---
Given a `P : LightProfinite`, the light free light condensed module `R[P]` is in
ternally projective
if and only if, for all `A B : LightCondMod R`, for all epimorphisms `e : A ⟶ B`
, for all
`S : LightProfinite` and all morphisms `g : R[S × P] ⟶ B`, there exists a `S' : 
LightProfinite`
with a surjection `π : S' ⟶ S` and a morphism `g' : R[S' × P] ⟶ A`, making the d
iagram
```
R[S' × P] --> A
  |           |
  v           v
R[S × P]  --> B
```
commute.
-/
lemma free_lightProfinite_internallyProjective_iff_tensor_condition' (P : LightProfinite.{u}) :
    InternallyProjective ((free R).obj P.toCondensed) ↔
      ∀ {A B : LightCondMod R} (e : A ⟶ B) [Epi e], (∀ (S : LightProfinite)
        (g : (free R).obj ((S ⊗ P).toCondensed) ⟶ B), ∃ (S' : LightProfinite)
          (π : S' ⟶ S) (_ : Function.Surjective π) (g' : (free R).obj (S' ⊗ P).toCondensed ⟶ A),
            ((free R).map (lightProfiniteToLightCondSet.map (π ▷ P))) ≫ g = g' ≫ e) := by
  rw [free_internallyProjective_iff_tensor_condition']
  refine ⟨fun h A B e he S g ↦ ?_, fun h A B e he S g ↦ ?_⟩
  · specialize h e S ((free R).map (μIso lightProfiniteToLightCondSet _ _).hom ≫ g)
    obtain ⟨S', π, hπ, g', hh⟩ := h
    refine ⟨S', π, hπ, (free R).map (μIso
        lightProfiniteToLightCondSet _ _).inv ≫ g', ?_⟩
    rw [assoc, ← hh]
    simp [-map_comp, ← map_comp_assoc]
  · specialize h e S ((free R).map (μIso lightProfiniteToLightCondSet _ _).inv ≫ g)
    obtain ⟨S', π, hπ, g', hh⟩ := h
    refine ⟨S', π, hπ, (free R).map
      (μIso lightProfiniteToLightCondSet _ _).hom ≫ g', ?_⟩
    rw [assoc, ← hh]
    simp [-map_comp, ← map_comp_assoc, ← μ_natural_left_assoc]

end LightCondensed

