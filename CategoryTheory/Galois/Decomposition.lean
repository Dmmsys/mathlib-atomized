/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Galois.GaloisObjects
public import Mathlib.CategoryTheory.Limits.Shapes.CombinedProducts
public import Mathlib.Data.Finite.Sum

/-!
# Decomposition of objects into connected components and applications

We show that in a Galois category every object is the (finite) coproduct of connected subobjects.
This has many useful corollaries, in particular that the fiber of every object
is represented by a Galois object.

## Main results

* `has_decomp_connected_components`: Every object is the sum of its (finitely many) connected
  components.
* `fiber_in_connected_component`: An element of the fiber of `X` lies in the fiber of some
  connected component.
* `connected_component_unique`: Up to isomorphism, for each element `x` in the fiber of `X` there
  is only one connected component whose fiber contains `x`.
* `exists_galois_representative`: The fiber of `X` is represented by some Galois object `A`:
  Evaluation at some `a` in the fiber of `A` induces a bijection `A ⟶ X` to `F.obj X`.

## References

* [lenstraGSchemes]: H. W. Lenstra. Galois theory for schemes.

-/

public section

universe u₁ u₂ w

namespace CategoryTheory

open Limits CategoryTheory.Functor

variable {C : Type u₁} [Category.{u₂} C]

namespace PreGaloisCategory


section Decomposition

/-! ### Decomposition in connected components

To show that an object `X` of a Galois category admits a decomposition into connected objects,
we proceed by induction on the cardinality of the fiber under an arbitrary fiber functor.

If `X` is connected, there is nothing to show. If not, we can write `X` as the sum of two
non-trivial subobjects which have strictly smaller fiber and conclude by the induction hypothesis.

-/

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The trivial case if `X` is connected. -/
/-
**CategoryTheory.PreGaloisCategory.has_decomp_connected_components_aux_conn** 是 
Mathlib 中的一个引理，位于命名空间 `CategoryTheory.PreGaloisCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The trivial case if `X` is connected.
-/
private lemma has_decomp_connected_components_aux_conn (X : C) [IsConnected X] :
    ∃ (ι : Type) (f : ι → C) (g : (i : ι) → (f i) ⟶ X) (_ : IsColimit (Cofan.mk X g)),
    (∀ i, IsConnected (f i)) ∧ Finite ι := by
  refine ⟨Unit, fun _ ↦ X, fun _ ↦ 𝟙 X, Cofan.IsColimit.mk _ (fun s ↦ s.inj ()), ?_⟩
  exact ⟨fun _ ↦ inferInstance, inferInstance⟩

/-- The trivial case if `X` is initial. -/
/-
**CategoryTheory.PreGaloisCategory.has_decomp_connected_components_aux_initial**
 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.PreGaloisCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The trivial case if `X` is initial.
-/
private lemma has_decomp_connected_components_aux_initial (X : C) (h : IsInitial X) :
    ∃ (ι : Type) (f : ι → C) (g : (i : ι) → (f i) ⟶ X) (_ : IsColimit (Cofan.mk X g)),
    (∀ i, IsConnected (f i)) ∧ Finite ι := by
  refine ⟨Empty, fun _ ↦ X, fun _ ↦ 𝟙 X, ?_⟩
  use Cofan.IsColimit.mk _ (fun s ↦ IsInitial.to h s.pt) (fun s ↦ by simp)
    (fun s m _ ↦ IsInitial.hom_ext h m _)
  exact ⟨by simp only [IsEmpty.forall_iff], inferInstance⟩

variable [GaloisCategory C]

/- Show decomposition by inducting on `Nat.card (F.obj X)`. -/
/-
**CategoryTheory.PreGaloisCategory.has_decomp_connected_components_aux** 是 Mathl
ib 中的一个引理，位于命名空间 `CategoryTheory.PreGaloisCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Show decomposition by inducting on `Nat.card (F.obj X)`.
-/
private lemma has_decomp_connected_components_aux (F : C ⥤ FintypeCat.{w}) [FiberFunctor F]
    (n : ℕ) : ∀ (X : C), n = Nat.card (F.obj X) → ∃ (ι : Type) (f : ι → C)
    (g : (i : ι) → (f i) ⟶ X) (_ : IsColimit (Cofan.mk X g)),
    (∀ i, IsConnected (f i)) ∧ Finite ι := by
  induction n using Nat.strongRecOn with | _ n hi
  intro X hn
  by_cases h : IsConnected X
  · exact has_decomp_connected_components_aux_conn X
  by_cases nhi : IsInitial X → False
  · obtain ⟨Y, v, hni, hvmono, hvnoiso⟩ :=
      has_non_trivial_subobject_of_not_isConnected_of_not_initial X h nhi
    obtain ⟨Z, u, ⟨c⟩⟩ := PreGaloisCategory.monoInducesIsoOnDirectSummand v
    let t : ColimitCocone (pair Y Z) := { cocone := BinaryCofan.mk v u, isColimit := c }
    have hn1 : Nat.card (F.obj Y) < n := by
      rw [hn]
      exact lt_card_fiber_of_mono_of_notIso F v hvnoiso
    have i : X ≅ Y ⨿ Z := (colimit.isoColimitCocone t).symm
    have hnn : Nat.card (F.obj X) = Nat.card (F.obj Y) + Nat.card (F.obj Z) := by
      rw [card_fiber_eq_of_iso F i]
      exact card_fiber_coprod_eq_sum F Y Z
    have hn2 : Nat.card (F.obj Z) < n := by
      rw [hn, hnn, lt_add_iff_pos_left]
      exact Nat.pos_of_ne_zero (non_zero_card_fiber_of_not_initial F Y hni)
    let ⟨ι₁, f₁, g₁, hc₁, hf₁, he₁⟩ := hi (Nat.card (F.obj Y)) hn1 Y rfl
    let ⟨ι₂, f₂, g₂, hc₂, hf₂, he₂⟩ := hi (Nat.card (F.obj Z)) hn2 Z rfl
    refine ⟨ι₁ ⊕ ι₂, Sum.elim f₁ f₂,
      Cofan.combPairHoms (Cofan.mk Y g₁) (Cofan.mk Z g₂) (BinaryCofan.mk v u), ?_⟩
    use Cofan.combPairIsColimit hc₁ hc₂ c
    refine ⟨fun i ↦ ?_, inferInstance⟩
    cases i
    · exact hf₁ _
    · exact hf₂ _
  · simp only [not_forall, not_false_eq_true] at nhi
    obtain ⟨hi⟩ := nhi
    exact has_decomp_connected_components_aux_initial X hi

/-- In a Galois category, every object is the sum of connected objects. -/
/-
**CategoryTheory.PreGaloisCategory.has_decomp_connected_components** 是 Mathlib 中
的一个定理，位于命名空间 `CategoryTheory.PreGaloisCategory`。
形式化陈述：has_decomp_connected_components (X : C) : exists (ι : Type) (f : ι -> C) (
g : (i : ι) -> f i ⟶ X) (_ : IsColimit (Cofan.mk X g)), (forall i, IsConnected (
f i)) ∧ Finite ι
参数：X : C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.CategoryTheory.Galois.Decomposition.0.CategoryTheory.Pr
eGaloisCategory.has_decomp_connected_components_aux`：∀ {C : Type u₁} [inst : Cat
egoryTheory.Category.{u₂, u₁} C] [inst_1 : CategoryTheory.GaloisCategory C]   (F
 : CategoryTheory.Functor C Finty…
· 使用定理 `CategoryTheory.PreGaloisCategory.instFiberFunctorGetFiberFunctor`：∀ (C :
 Type u₁) [inst : CategoryTheory.Category.{u₂, u₁} C] [inst_1 : CategoryTheory.G
aloisCategory C],   CategoryTheory.PreGaloisCategory.F…

--- 原说明 ---
In a Galois category, every object is the sum of connected objects.
-/
theorem has_decomp_connected_components (X : C) :
    ∃ (ι : Type) (f : ι → C) (g : (i : ι) → f i ⟶ X) (_ : IsColimit (Cofan.mk X g)),
      (∀ i, IsConnected (f i)) ∧ Finite ι := by
  let F := GaloisCategory.getFiberFunctor C
  exact has_decomp_connected_components_aux F (Nat.card <| F.obj X) X rfl

/-- In a Galois category, every object is the sum of connected objects. -/
/-
**CategoryTheory.PreGaloisCategory.has_decomp_connected_components'** 是 Mathlib 
中的一个定理，位于命名空间 `CategoryTheory.PreGaloisCategory`。
形式化陈述：has_decomp_connected_components' (X : C) : exists (ι : Type) (_ : Finite ι
) (f : ι -> C) (_ : ∐ f ≅ X), forall i, IsConnected (f i)
参数：X : C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.PreGaloisCategory.hasFiniteCoproducts`：∀ {C : Type u₁} {i
nst : CategoryTheory.Category.{u₂, u₁} C} [self : CategoryTheory.PreGaloisCatego
ry C],   CategoryTheory.Limits.HasFiniteCo…
· 使用定理 `CategoryTheory.GaloisCategory.toPreGaloisCategory`：∀ {C : Type u₁} {inst
 : CategoryTheory.Category.{u₂, u₁} C} [self : CategoryTheory.GaloisCategory C],
   CategoryTheory.PreGaloisCategory C
· 使用定理 `CategoryTheory.PreGaloisCategory.has_decomp_connected_components`：has_de
comp_connected_components (X : C) : exists (ι : Type) (f : ι -> C) (g : (i : ι) 
-> f i ⟶ X) (_ : IsColimit (Cofan.mk X g)), (forall i,…

--- 原说明 ---
In a Galois category, every object is the sum of connected objects.
-/
theorem has_decomp_connected_components' (X : C) :
    ∃ (ι : Type) (_ : Finite ι) (f : ι → C) (_ : ∐ f ≅ X), ∀ i, IsConnected (f i) := by
  obtain ⟨ι, f, g, hl, hc, hf⟩ := has_decomp_connected_components X
  exact ⟨ι, hf, f, colimit.isoColimitCocone ⟨Cofan.mk X g, hl⟩, hc⟩

variable (F : C ⥤ FintypeCat.{w}) [FiberFunctor F]

/-- Every element in the fiber of `X` lies in some connected component of `X`. -/
/-
**CategoryTheory.PreGaloisCategory.fiber_in_connected_component** 是 Mathlib 中的一个
引理，位于命名空间 `CategoryTheory.PreGaloisCategory`。
形式化陈述：fiber_in_connected_component (X : C) (x : F.obj X) : exists (Y : C) (i : Y
 ⟶ X) (y : F.obj Y), F.map i y = x ∧ IsConnected Y ∧ Mono i
参数：X : C；x : F.obj X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GaloisCategory.toPreGaloisCategory`：∀ {C : Type u₁} {inst
 : CategoryTheory.Category.{u₂, u₁} C} [self : CategoryTheory.GaloisCategory C],
   CategoryTheory.PreGaloisCategory C
· 使用定理 `CategoryTheory.PreGaloisCategory.has_decomp_connected_components`：has_de
comp_connected_components (X : C) : exists (ι : Type) (f : ι -> C) (g : (i : ι) 
-> f i ⟶ X) (_ : IsColimit (Cofan.mk X g)), (forall i,…
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Limits.instPreservesColimitsOfShapeDiscreteOfFiniteOfPres
ervesFiniteCoproducts`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} 
C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTh
eor…
· 使用定理 `CategoryTheory.PreGaloisCategory.FiberFunctor.preservesFiniteCoproducts`
：∀ {C : Type u₁} {inst : CategoryTheory.Category.{u₂, u₁} C} {inst_1 : CategoryT
heory.PreGaloisCategory C}   {F : CategoryTheory.Functor C Fi…
· 使用定理 `CategoryTheory.Limits.Concrete.isColimit_exists_rep`：isColimit_exists_re
p {D : Cocone F} (hD : IsColimit D) (x : ToType D.pt) : exists (j : J) (y : ToTy
pe (F.obj j)), D.ι.app j y = x
· 使用定理 `CategoryTheory.Limits.instPreservesFiniteCoproductsOfPreservesFiniteColi
mits`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.FintypeCat.instPreservesFiniteColimitsFintypeCatFo
rgetFunObjFinite`：CategoryTheory.Limits.PreservesFiniteColimits (CategoryTheory.
forget FintypeCat)
· 使用引理 `CategoryTheory.Limits.MonoCoprod.mono_inj`：mono_inj (c : Cofan X) (h : I
sColimit c) (i : I) [HasCoproduct (fun (k : ((Set.range (fun _ : Unit => i))ᶜ : 
Set I)) => X k.1)] : Mono (Cofa…
· 使用定理 `CategoryTheory.PreGaloisCategory.instMonoCoprod`：∀ {C : Type u₁} [inst :
 CategoryTheory.Category.{u₂, u₁} C] [CategoryTheory.GaloisCategory C],   Catego
ryTheory.Limits.MonoCoprod C
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.PreGaloisCategory.hasFiniteCoproducts`：∀ {C : Type u₁} {i
nst : CategoryTheory.Category.{u₂, u₁} C} [self : CategoryTheory.PreGaloisCatego
ry C],   CategoryTheory.Limits.HasFiniteCo…

--- 原说明 ---
Every element in the fiber of `X` lies in some connected component of `X`.
-/
lemma fiber_in_connected_component (X : C) (x : F.obj X) : ∃ (Y : C) (i : Y ⟶ X) (y : F.obj Y),
    F.map i y = x ∧ IsConnected Y ∧ Mono i := by
  obtain ⟨ι, f, g, hl, hc, he⟩ := has_decomp_connected_components X
  let s : Cocone (Discrete.functor f ⋙ F) := F.mapCocone (Cofan.mk X g)
  let s' : IsColimit s := isColimitOfPreserves F hl
  obtain ⟨⟨j⟩, z, h⟩ := Concrete.isColimit_exists_rep _ s' x
  refine ⟨f j, g j, z, ⟨?_, hc j, MonoCoprod.mono_inj _ (Cofan.mk X g) hl j⟩⟩
  subst h
  rfl

/-- Up to isomorphism an element of the fiber of `X` only lies in one connected component. -/
/-
**CategoryTheory.PreGaloisCategory.connected_component_unique** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory.PreGaloisCategory`。
形式化陈述：connected_component_unique {X A B : C} [IsConnected A] [IsConnected B] (a 
: F.obj A) (b : F.obj B) (i : A ⟶ X) (j : B ⟶ X) (h : F.map i a = F.map j b) [Mo
no i] [Mono j] : exists (f : A ≅ B), F.map f.hom a = b
参数：a : F.obj A；b : F.obj B；i : A ⟶ X；j : B ⟶ X；h : F.map i a = F.map j b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GaloisCategory.toPreGaloisCategory`：∀ {C : Type u₁} {inst
 : CategoryTheory.Category.{u₂, u₁} C} [self : CategoryTheory.GaloisCategory C],
   CategoryTheory.PreGaloisCategory C
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.PreGaloisCategory.hasPullbacks`：∀ {C : Type u₁} {inst : C
ategoryTheory.Category.{u₂, u₁} C} [self : CategoryTheory.PreGaloisCategory C], 
  CategoryTheory.Limits.HasPullback…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用引理 `CategoryTheory.PreGaloisCategory.not_initial_of_inhabited`：not_initial_o
f_inhabited {X : C} (x : F.obj X) (h : IsInitial X) : False
· 使用定理 `CategoryTheory.PreGaloisCategory.IsConnected.noTrivialComponent`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{u₂, u₁} C} {X : C}   [self : CategoryT
heory.PreGaloisCategory.IsConnected X] (Y : C) (i : Y…
· 使用定理 `CategoryTheory.Limits.pullback.fst_of_mono`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Cat
egoryTheory.Limits.HasPullback f…
· 使用定理 `CategoryTheory.Limits.pullback.snd_of_mono`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Cat
egoryTheory.Limits.HasPullback f…
· 使用引理 `CategoryTheory.PreGaloisCategory.fiberPullbackEquiv_symm_fst_apply`：fibe
rPullbackEquiv_symm_fst_apply {X A B : C} {f : A ⟶ X} {g : B ⟶ X} (a : F.obj A) 
(b : F.obj B) (h : F.map f a = F.map g b) : F.map (pullb…
· 使用引理 `CategoryTheory.PreGaloisCategory.fiberPullbackEquiv_symm_snd_apply`：fibe
rPullbackEquiv_symm_snd_apply {X A B : C} {f : A ⟶ X} {g : B ⟶ X} (a : F.obj A) 
(b : F.obj B) (h : F.map f a = F.map g b) : F.map (pullb…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.IsIso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y) [I : CategoryTheory.IsIso f] {Z : 
C}   (h : X ⟶ Z), CategoryT…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Up to isomorphism an element of the fiber of `X` only lies in one connected comp
onent.
-/
lemma connected_component_unique {X A B : C} [IsConnected A] [IsConnected B] (a : F.obj A)
    (b : F.obj B) (i : A ⟶ X) (j : B ⟶ X) (h : F.map i a = F.map j b) [Mono i] [Mono j] :
    ∃ (f : A ≅ B), F.map f.hom a = b := by
  /- We consider the fiber product of A and B over X. This is a non-empty (because of `h`)
  subobject of `A` and `B` and hence isomorphic to `A` and `B` by connectedness. -/
  let Y : C := pullback i j
  let u : Y ⟶ A := pullback.fst i j
  let v : Y ⟶ B := pullback.snd i j
  let G := F ⋙ FintypeCat.incl
  let e : F.obj Y ≃ { p : F.obj A × F.obj B // F.map i p.1 = F.map j p.2 } :=
    fiberPullbackEquiv F i j
  let y : F.obj Y := e.symm ⟨(a, b), h⟩
  have hn : IsInitial Y → False := not_initial_of_inhabited F y
  have : IsIso u := IsConnected.noTrivialComponent Y u hn
  have : IsIso v := IsConnected.noTrivialComponent Y v hn
  use (asIso u).symm ≪≫ asIso v
  have hu : G.map u y = a := fiberPullbackEquiv_symm_fst_apply _ _ _ h
  have hv : G.map v y = b := fiberPullbackEquiv_symm_snd_apply _ _ _ h
  rw [← hu, ← hv]
  change (F.map u ≫ F.map _) y = F.map v y
  simp only [← F.map_comp, Iso.trans_hom, Iso.symm_hom, asIso_inv, asIso_hom,
    IsIso.hom_inv_id_assoc]

end Decomposition

section GaloisRep

/-! ### Galois representative of fiber

If `X` is any object, then its fiber is represented by some Galois object: There exists
a Galois object `A` and an element `a` in the fiber of `A` such that the
evaluation at `a` from `A ⟶ X` to `F.obj X` is bijective.

To show this we consider the product `∏ᶜ (fun _ : F.obj X ↦ X)` and let `A`
be the connected component whose fiber contains the element `a` in the fiber of the self product
that has at each index `x : F.obj X` the element `x`.

This `A` is Galois and evaluation at `a` is bijective.

Reference: [lenstraGSchemes, 3.14]

-/

variable [GaloisCategory C] (F : C ⥤ FintypeCat.{w}) [FiberFunctor F]

section GaloisRepAux

variable (X : C)

set_option backward.privateInPublic true in
/-- The self product of `X` indexed by its fiber. -/
@[simp]
/-
**CategoryTheory.PreGaloisCategory.selfProd** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.PreGaloisCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The self product of `X` indexed by its fiber.
-/
private noncomputable def selfProd : C := ∏ᶜ (fun _ : F.obj X ↦ X)

set_option backward.privateInPublic true in
/-- For `g : F.obj X → F.obj X`, this is the element in the fiber of the self product,
which has at index `x : F.obj X` the element `g x`. -/
/-
**CategoryTheory.PreGaloisCategory.mkSelfProdFib** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.PreGaloisCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For `g : F.obj X → F.obj X`, this is the element in the fiber of the self produc
t,
which has at index `x : F.obj X` the element `g x`.
-/
private noncomputable def mkSelfProdFib : F.obj (selfProd F X) :=
  (PreservesProduct.iso F _).inv ((Concrete.productEquiv (fun _ : F.obj X ↦ F.obj X)).symm id)

@[simp]
/-
**CategoryTheory.PreGaloisCategory.mkSelfProdFib_map_** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.PreGaloisCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma mkSelfProdFib_map_π (t : F.obj X) : F.map (Pi.π _ t) (mkSelfProdFib F X) = t := by
  rw [← piComparison_comp_π]
  simp [← PreservesProduct.iso_hom, mkSelfProdFib]

variable {X} {A : C} (u : A ⟶ selfProd F X)
  (a : F.obj A) (h : F.map u a = mkSelfProdFib F X) {F}
include h

set_option backward.privateInPublic true in
/-- For each `x : F.obj X`, this is the composition of `u` with the projection at `x`. -/
@[simp]
/-
**CategoryTheory.PreGaloisCategory.selfProdProj** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.PreGaloisCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For each `x : F.obj X`, this is the composition of `u` with the projection at `x
`.
-/
private noncomputable def selfProdProj (x : F.obj X) : A ⟶ X := u ≫ Pi.π _ x

variable {u a}

set_option backward.isDefEq.respectTransparency false in
set_option backward.privateInPublic true in
/-
**CategoryTheory.PreGaloisCategory.selfProdProj_fiber** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.PreGaloisCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma selfProdProj_fiber (x : F.obj X) :
    F.map (selfProdProj u x) a = x := by
  simp_all

variable [IsConnected A]

set_option backward.privateInPublic true in
/-- An element `b : F.obj A` defines a permutation of the fiber of `X` by projecting onto the
`F.map u b` factor. -/
/-
**CategoryTheory.PreGaloisCategory.fiberPerm** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.PreGaloisCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An element `b : F.obj A` defines a permutation of the fiber of `X` by projecting
 onto the
`F.map u b` factor.
-/
private noncomputable def fiberPerm (b : F.obj A) : F.obj X ≃ F.obj X := by
  let σ (t : F.obj X) : F.obj X := F.map (selfProdProj u t) b
  apply Equiv.ofBijective σ
  apply Finite.injective_iff_bijective.mp
  intro t s (hs : F.map (selfProdProj u t) b = F.map (selfProdProj u s) b)
  change id t = id s
  have h' : selfProdProj u t = selfProdProj u s := evaluation_injective_of_isConnected F A X b hs
  rw [← selfProdProj_fiber h s, ← selfProdProj_fiber h t, h']

set_option backward.privateInPublic true in
/-- Twisting `u` by `fiberPerm h b` yields an inclusion of `A` into `selfProd F X`. -/
/-
**CategoryTheory.PreGaloisCategory.selfProdPermIncl** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.PreGaloisCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Twisting `u` by `fiberPerm h b` yields an inclusion of `A` into `selfProd F X`.
-/
private noncomputable def selfProdPermIncl (b : F.obj A) : A ⟶ selfProd F X :=
  u ≫ (Pi.whiskerEquiv (fiberPerm h b) (fun _ => Iso.refl X)).inv

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.privateInPublic true in
/-
**CategoryTheory.PreGaloisCategory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Pr
eGaloisCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private instance [Mono u] (b : F.obj A) : Mono (selfProdPermIncl h b) := mono_comp _ _

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.privateInPublic true in
/-- Key technical lemma: the twisted inclusion `selfProdPermIncl h b` maps `a` to `F.map u b`. -/
/-
**CategoryTheory.PreGaloisCategory.selfProdTermIncl_fib_eq** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory.PreGaloisCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Key technical lemma: the twisted inclusion `selfProdPermIncl h b` maps `a` to `F
.map u b`.
-/
private lemma selfProdTermIncl_fib_eq (b : F.obj A) :
    F.map u b = F.map (selfProdPermIncl h b) a := by
  apply Concrete.Pi.map_ext _ F
  intro (t : F.obj X)
  convert_to F.map (selfProdProj u t) b = _
  · simp only [selfProdProj, map_comp, FintypeCat.comp_apply]; rfl
  · dsimp only [selfProdPermIncl, Pi.whiskerEquiv]
    rw [map_comp, FintypeCat.comp_apply, h]
    convert_to! F.map (selfProdProj u t) b =
      (F.map (Pi.map' (fiberPerm h b) fun _ ↦ 𝟙 X) ≫
      F.map (Pi.π (fun _ ↦ X) t)) (mkSelfProdFib F X)
    rw [← map_comp, Pi.map'_comp_π, Category.comp_id, mkSelfProdFib_map_π F X (fiberPerm h b t)]
    rfl

set_option backward.privateInPublic true in
/-- There exists an automorphism `f` of `A` that maps `b` to `a`.
`f` is obtained by considering `u` and `selfProdPermIncl h b`.
Both are inclusions of `A` into `selfProd F X` mapping `b` respectively `a` to the same element
in the fiber of `selfProd F X`. Applying `connected_component_unique` yields the result. -/
/-
**CategoryTheory.PreGaloisCategory.subobj_selfProd_trans** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.PreGaloisCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
There exists an automorphism `f` of `A` that maps `b` to `a`.
`f` is obtained by considering `u` and `selfProdPermIncl h b`.
Both are inclusions of `A` into `selfProd F X` mapping `b` respectively `a` to t
he same element
in the fiber of `selfProd F X`. Applying `connected_component_unique` yields the
 result.
-/
private lemma subobj_selfProd_trans [Mono u] (b : F.obj A) : ∃ (f : A ≅ A), F.map f.hom b = a := by
  apply connected_component_unique F b a u (selfProdPermIncl h b)
  exact selfProdTermIncl_fib_eq h b

end GaloisRepAux

/-- The fiber of any object in a Galois category is represented by a Galois object. -/
/-
**CategoryTheory.PreGaloisCategory.exists_galois_representative** 是 Mathlib 中的一个
引理，位于命名空间 `CategoryTheory.PreGaloisCategory`。
形式化陈述：exists_galois_representative (X : C) : exists (A : C) (a : F.obj A), IsGal
ois A ∧ Function.Bijective (fun (f : A ⟶ X) => F.map f a)
参数：X : C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GaloisCategory.toPreGaloisCategory`：∀ {C : Type u₁} {inst
 : CategoryTheory.Category.{u₂, u₁} C} [self : CategoryTheory.GaloisCategory C],
   CategoryTheory.PreGaloisCategory C
· 使用引理 `CategoryTheory.PreGaloisCategory.fiber_in_connected_component`：fiber_in_
connected_component (X : C) (x : F.obj X) : exists (Y : C) (i : Y ⟶ X) (y : F.ob
j Y), F.map i y = x ∧ IsConnected Y ∧ Mono i
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.PreGaloisCategory.isGalois_iff_pretransitive`：isGalois_if
f_pretransitive (X : C) [IsConnected X] : IsGalois X ↔ MulAction.IsPretransitive
 (Aut X) (F.obj X)
· 使用定理 `_private.Mathlib.CategoryTheory.Galois.Decomposition.0.CategoryTheory.Pr
eGaloisCategory.subobj_selfProd_trans`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{u₂, u₁} C] [inst_1 : CategoryTheory.GaloisCategory C]   {F : CategoryThe
ory.Functor C Finty…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.ConcreteCategory.congr_hom`：congr_hom {X Y : C} {f g : X 
⟶ Y} (h : f = g) (x : ToType X) : f x = g x
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用引理 `CategoryTheory.PreGaloisCategory.evaluation_injective_of_isConnected`：ev
aluation_injective_of_isConnected (A X : C) [IsConnected A] (a : F.obj A) : Func
tion.Injective (fun (f : A ⟶ X) => F.map f a)
· 使用定理 `_private.Mathlib.CategoryTheory.Galois.Decomposition.0.CategoryTheory.Pr
eGaloisCategory.selfProdProj_fiber`：∀ {C : Type u₁} [inst : CategoryTheory.Categ
ory.{u₂, u₁} C] [inst_1 : CategoryTheory.GaloisCategory C]   {F : CategoryTheory
.Functor C Finty…

--- 原说明 ---
The fiber of any object in a Galois category is represented by a Galois object.
-/
lemma exists_galois_representative (X : C) : ∃ (A : C) (a : F.obj A),
    IsGalois A ∧ Function.Bijective (fun (f : A ⟶ X) ↦ F.map f a) := by
  obtain ⟨A, u, a, h1, h2, h3⟩ := fiber_in_connected_component F (selfProd F X)
    (mkSelfProdFib F X)
  use A
  use a
  constructor
  · refine (isGalois_iff_pretransitive F A).mpr ⟨fun x y ↦ ?_⟩
    obtain ⟨fi1, hfi1⟩ := subobj_selfProd_trans h1 x
    obtain ⟨fi2, hfi2⟩ := subobj_selfProd_trans h1 y
    use fi1 ≪≫ fi2.symm
    change F.map (fi1.hom ≫ fi2.inv) x = y
    simp only [map_comp, FintypeCat.comp_apply]
    rw [hfi1, ← hfi2]
    exact ConcreteCategory.congr_hom (F.mapIso fi2).hom_inv_id y
  · refine ⟨evaluation_injective_of_isConnected F A X a, ?_⟩
    intro x
    use u ≫ Pi.π _ x
    exact (selfProdProj_fiber h1) x

/-- Any element in the fiber of an object `X` is the evaluation of a morphism from a
Galois object. -/
/-
**CategoryTheory.PreGaloisCategory.exists_hom_from_galois_of_fiber** 是 Mathlib 中
的一个引理，位于命名空间 `CategoryTheory.PreGaloisCategory`。
形式化陈述：exists_hom_from_galois_of_fiber (X : C) (x : F.obj X) : exists (A : C) (f 
: A ⟶ X) (a : F.obj A), IsGalois A ∧ F.map f a = x
参数：X : C；x : F.obj X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GaloisCategory.toPreGaloisCategory`：∀ {C : Type u₁} {inst
 : CategoryTheory.Category.{u₂, u₁} C} [self : CategoryTheory.GaloisCategory C],
   CategoryTheory.PreGaloisCategory C
· 使用引理 `CategoryTheory.PreGaloisCategory.exists_galois_representative`：exists_ga
lois_representative (X : C) : exists (A : C) (a : F.obj A), IsGalois A ∧ Functio
n.Bijective (fun (f : A ⟶ X) => F.map f a)
· 使用定理 `Function.Bijective.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → 
β}, Function.Bijective f → Function.Surjective f

--- 原说明 ---
Any element in the fiber of an object `X` is the evaluation of a morphism from a
Galois object.
-/
lemma exists_hom_from_galois_of_fiber (X : C) (x : F.obj X) :
    ∃ (A : C) (f : A ⟶ X) (a : F.obj A), IsGalois A ∧ F.map f a = x := by
  obtain ⟨A, a, h1, h2⟩ := exists_galois_representative F X
  obtain ⟨f, hf⟩ := h2.surjective x
  exact ⟨A, f, a, h1, hf⟩

/-- Any object with non-empty fiber admits a hom from a Galois object. -/
/-
**CategoryTheory.PreGaloisCategory.exists_hom_from_galois_of_fiber_nonempty** 是 
Mathlib 中的一个引理，位于命名空间 `CategoryTheory.PreGaloisCategory`。
形式化陈述：exists_hom_from_galois_of_fiber_nonempty (X : C) (h : Nonempty (F.obj X)) 
: exists (A : C) (_ : A ⟶ X), IsGalois A
参数：X : C；h : Nonempty (F.obj X)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GaloisCategory.toPreGaloisCategory`：∀ {C : Type u₁} {inst
 : CategoryTheory.Category.{u₂, u₁} C} [self : CategoryTheory.GaloisCategory C],
   CategoryTheory.PreGaloisCategory C
· 使用引理 `CategoryTheory.PreGaloisCategory.exists_hom_from_galois_of_fiber`：exists
_hom_from_galois_of_fiber (X : C) (x : F.obj X) : exists (A : C) (f : A ⟶ X) (a 
: F.obj A), IsGalois A ∧ F.map f a = x

--- 原说明 ---
Any object with non-empty fiber admits a hom from a Galois object.
-/
lemma exists_hom_from_galois_of_fiber_nonempty (X : C) (h : Nonempty (F.obj X)) :
    ∃ (A : C) (_ : A ⟶ X), IsGalois A := by
  obtain ⟨x⟩ := h
  obtain ⟨A, f, a, h1, _⟩ := exists_hom_from_galois_of_fiber F X x
  exact ⟨A, f, h1⟩

include F in
/-- Any connected object admits a hom from a Galois object. -/
/-
**CategoryTheory.PreGaloisCategory.exists_hom_from_galois_of_connected** 是 Mathl
ib 中的一个引理，位于命名空间 `CategoryTheory.PreGaloisCategory`。
形式化陈述：exists_hom_from_galois_of_connected (X : C) [IsConnected X] : exists (A : 
C) (_ : A ⟶ X), IsGalois A
参数：X : C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GaloisCategory.toPreGaloisCategory`：∀ {C : Type u₁} {inst
 : CategoryTheory.Category.{u₂, u₁} C} [self : CategoryTheory.GaloisCategory C],
   CategoryTheory.PreGaloisCategory C
· 使用引理 `CategoryTheory.PreGaloisCategory.exists_hom_from_galois_of_fiber_nonempt
y`：exists_hom_from_galois_of_fiber_nonempty (X : C) (h : Nonempty (F.obj X)) : e
xists (A : C) (_ : A ⟶ X), IsGalois A

--- 原说明 ---
Any connected object admits a hom from a Galois object.
-/
lemma exists_hom_from_galois_of_connected (X : C) [IsConnected X] :
    ∃ (A : C) (_ : A ⟶ X), IsGalois A :=
  exists_hom_from_galois_of_fiber_nonempty F X inferInstance

/-- To check equality of natural transformations `F ⟶ G`, it suffices to check it on
Galois objects. -/
/-
**CategoryTheory.PreGaloisCategory.natTrans_ext_of_isGalois** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.PreGaloisCategory`。
形式化陈述：natTrans_ext_of_isGalois {G : C ⥤ FintypeCat.{w}} {t s : F ⟶ G} (h : foral
l (X : C) [IsGalois X], t.app X = s.app X) : t = s
参数：h : forall (X : C) [IsGalois X], t.app X = s.app X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GaloisCategory.toPreGaloisCategory`：∀ {C : Type u₁} {inst
 : CategoryTheory.Category.{u₂, u₁} C} [self : CategoryTheory.GaloisCategory C],
   CategoryTheory.PreGaloisCategory C
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `FintypeCat.hom_ext`：hom_ext {X Y : FintypeCat} (f g : X ⟶ Y) (h : forall
 x, f x = g x) : f = g
· 使用引理 `CategoryTheory.PreGaloisCategory.exists_hom_from_galois_of_fiber`：exists
_hom_from_galois_of_fiber (X : C) (x : F.obj X) : exists (A : C) (f : A ⟶ X) (a 
: F.obj A), IsGalois A ∧ F.map f a = x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.NatTrans.naturality_apply`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {D : Type u_1} [inst_1 : CategoryTheory.Category.{v_1
, u_1} D]   {FD : outParam (D …

--- 原说明 ---
To check equality of natural transformations `F ⟶ G`, it suffices to check it on
Galois objects.
-/
lemma natTrans_ext_of_isGalois {G : C ⥤ FintypeCat.{w}} {t s : F ⟶ G}
    (h : ∀ (X : C) [IsGalois X], t.app X = s.app X) :
    t = s := by
  ext X x
  obtain ⟨A, f, a, _, rfl⟩ := exists_hom_from_galois_of_fiber F X x
  rw [NatTrans.naturality_apply, NatTrans.naturality_apply, h A]

end GaloisRep

end PreGaloisCategory

end CategoryTheory

