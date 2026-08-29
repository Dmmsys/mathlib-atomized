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
/--
lemma `has_decomp_connected_components_aux_conn` / 引理 `has_decomp_connected_components_aux_conn`

English:
lemma has_decomp_connected_components_aux_conn
  given: (X : C) [IsConnected X]
  proof: by
  refine ⟨Unit, fun _ => X, fun _ => 𝟙 X, Cofan.IsColimit.mk _ (fun s => s.inj ()), ?_⟩
  exact ⟨fun _ => inferInstance, inferInstance⟩

中文:
引理 has_decomp_connected_components_aux_conn
  条件: (X : C) [IsConnected X]
  证明: by
  refine ⟨Unit, fun _ => X, fun _ => 𝟙 X, Cofan.IsColimit.mk _ (fun s => s.inj ()), ?_⟩
  exact ⟨fun _ => inferInstance, inferInstance⟩
-/
private lemma has_decomp_connected_components_aux_conn (X : C) [IsConnected X] :
    exists (ι : Type) (f : ι -> C) (g : (i : ι) -> (f i) ⟶ X) (_ : IsColimit (Cofan.mk X g)),
    (forall i, IsConnected (f i)) ∧ Finite ι := by
  refine ⟨Unit, fun _ => X, fun _ => 𝟙 X, Cofan.IsColimit.mk _ (fun s => s.inj ()), ?_⟩
  exact ⟨fun _ => inferInstance, inferInstance⟩

/--
lemma `has_decomp_connected_components_aux_initial` / 引理 `has_decomp_connected_components_aux_initial`

English:
lemma has_decomp_connected_components_aux_initial
  given: (X : C) (h : IsInitial X)
  proof: by
  refine ⟨Empty, fun _ => X, fun _ => 𝟙 X, ?_⟩
  use Cofan.IsColimit.mk _ (fun s => IsInitial.to h s.pt) (fun s => by simp)
    (fun s m _ => IsInitial.hom_ext h m _)
  exact ⟨by simp only [IsEmpty.forall_iff], inferInstance⟩

中文:
引理 has_decomp_connected_components_aux_initial
  条件: (X : C) (h : IsInitial X)
  证明: by
  refine ⟨Empty, fun _ => X, fun _ => 𝟙 X, ?_⟩
  use Cofan.IsColimit.mk _ (fun s => IsInitial.to h s.pt) (fun s => by simp)
    (fun s m _ => IsInitial.hom_ext h m _)
  exact ⟨by simp only [IsEmpty.forall_iff], inferInstance⟩
-/
private lemma has_decomp_connected_components_aux_initial (X : C) (h : IsInitial X) :
    exists (ι : Type) (f : ι -> C) (g : (i : ι) -> (f i) ⟶ X) (_ : IsColimit (Cofan.mk X g)),
    (forall i, IsConnected (f i)) ∧ Finite ι := by
  refine ⟨Empty, fun _ => X, fun _ => 𝟙 X, ?_⟩
  use Cofan.IsColimit.mk _ (fun s => IsInitial.to h s.pt) (fun s => by simp)
    (fun s m _ => IsInitial.hom_ext h m _)
  exact ⟨by simp only [IsEmpty.forall_iff], inferInstance⟩

variable [GaloisCategory C]

/--
lemma `has_decomp_connected_components_aux` / 引理 `has_decomp_connected_components_aux`

English:
lemma has_decomp_connected_components_aux
  statement: (F : C ⥤ FintypeCat.{w}) [FiberFunctor F]
  proof: by
  induction n using Nat.strongRecOn with | _ n hi
  intro X hn
  by_cases h : IsConnected X
  · exact has_decomp_connected_components_aux_conn X
  by_cases nhi : IsInitial X -> False
  · obtain ⟨Y, v, hni, hvmono, hvnoiso⟩ :=
      has_non_trivial_subobject_of_not_isConnected_of_not_initial X h n

中文:
引理 has_decomp_connected_components_aux
  结论: (F : C ⥤ FintypeCat.{w}) [FiberFunctor F]
  证明: by
  induction n using Nat.strongRecOn with | _ n hi
  intro X hn
  by_cases h : IsConnected X
  · exact has_decomp_connected_components_aux_conn X
  by_cases nhi : IsInitial X -> False
  · obtain ⟨Y, v, hni, hvmono, hvnoiso⟩ :=
      has_non_trivial_subobject_of_not_isConnected_of_not_initial X h n
-/
private lemma has_decomp_connected_components_aux (F : C ⥤ FintypeCat.{w}) [FiberFunctor F]
    (n : Nat) : forall (X : C), n = Nat.card (F.obj X) -> exists (ι : Type) (f : ι -> C)
    (g : (i : ι) -> (f i) ⟶ X) (_ : IsColimit (Cofan.mk X g)),
    (forall i, IsConnected (f i)) ∧ Finite ι := by
  induction n using Nat.strongRecOn with | _ n hi
  intro X hn
  by_cases h : IsConnected X
  · exact has_decomp_connected_components_aux_conn X
  by_cases nhi : IsInitial X -> False
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
      rw [hn]; rw [hnn]; rw [lt_add_iff_pos_left]
      exact Nat.pos_of_ne_zero (non_zero_card_fiber_of_not_initial F Y hni)
    let ⟨ι₁, f₁, g₁, hc₁, hf₁, he₁⟩ := hi (Nat.card (F.obj Y)) hn1 Y rfl
    let ⟨ι₂, f₂, g₂, hc₂, hf₂, he₂⟩ := hi (Nat.card (F.obj Z)) hn2 Z rfl
    refine ⟨ι₁ oplus ι₂, Sum.elim f₁ f₂,
      Cofan.combPairHoms (Cofan.mk Y g₁) (Cofan.mk Z g₂) (BinaryCofan.mk v u), ?_⟩
    use Cofan.combPairIsColimit hc₁ hc₂ c
    refine ⟨fun i => ?_, inferInstance⟩
    cases i
    · exact hf₁ _
    · exact hf₂ _
  · simp only [not_forall, not_false_eq_true] at nhi
    obtain ⟨hi⟩ := nhi
    exact has_decomp_connected_components_aux_initial X hi

/--
theorem `has_decomp_connected_components` / 定理 `has_decomp_connected_components`

English:
theorem has_decomp_connected_components
  given: (X : C)
  proof: by
  let F := GaloisCategory.getFiberFunctor C
  exact has_decomp_connected_components_aux F (Nat.card <| F.obj X) X rfl

中文:
定理 has_decomp_connected_components
  条件: (X : C)
  证明: by
  let F := GaloisCategory.getFiberFunctor C
  exact has_decomp_connected_components_aux F (Nat.card <| F.obj X) X rfl

Depends on / 依赖: F.obj, GaloisCategory, GaloisCategory.getFiberFunctor, Nat.card, getFiberFunctor, has_decomp_connected_components_aux
-/
theorem has_decomp_connected_components (X : C) :
    exists (ι : Type) (f : ι -> C) (g : (i : ι) -> f i ⟶ X) (_ : IsColimit (Cofan.mk X g)),
      (forall i, IsConnected (f i)) ∧ Finite ι := by
  let F := GaloisCategory.getFiberFunctor C
  exact has_decomp_connected_components_aux F (Nat.card <| F.obj X) X rfl

/--
theorem `has_decomp_connected_components'` / 定理 `has_decomp_connected_components'`

English:
theorem has_decomp_connected_components'
  given: (X : C)
  proof: by
  obtain ⟨ι, f, g, hl, hc, hf⟩ := has_decomp_connected_components X
  exact ⟨ι, hf, f, colimit.isoColimitCocone ⟨Cofan.mk X g, hl⟩, hc⟩

中文:
定理 has_decomp_connected_components'
  条件: (X : C)
  证明: by
  obtain ⟨ι, f, g, hl, hc, hf⟩ := has_decomp_connected_components X
  exact ⟨ι, hf, f, colimit.isoColimitCocone ⟨Cofan.mk X g, hl⟩, hc⟩

Depends on / 依赖: Cofan.mk, colimit, colimit.isoColimitCocone, has_decomp_connected_components, isoColimitCocone
-/
theorem has_decomp_connected_components' (X : C) :
    exists (ι : Type) (_ : Finite ι) (f : ι -> C) (_ : ∐ f ≅ X), forall i, IsConnected (f i) := by
  obtain ⟨ι, f, g, hl, hc, hf⟩ := has_decomp_connected_components X
  exact ⟨ι, hf, f, colimit.isoColimitCocone ⟨Cofan.mk X g, hl⟩, hc⟩

variable (F : C ⥤ FintypeCat.{w}) [FiberFunctor F]

/--
lemma `fiber_in_connected_component` / 引理 `fiber_in_connected_component`

English:
lemma fiber_in_connected_component
  given: (X : C) (x : F.obj X)
  statement: exists (Y : C) (i : Y ⟶ X) (y : F.obj Y),
  proof: by
  obtain ⟨ι, f, g, hl, hc, he⟩ := has_decomp_connected_components X
  let s : Cocone (Discrete.functor f ⋙ F) := F.mapCocone (Cofan.mk X g)
  let s' : IsColimit s := isColimitOfPreserves F hl
  obtain ⟨⟨j⟩, z, h⟩ := Concrete.isColimit_exists_rep _ s' x
  refine ⟨f j, g j, z, ⟨?_, hc j, MonoCoprod

中文:
引理 fiber_in_connected_component
  条件: (X : C) (x : F.obj X)
  结论: 存在 (Y : C) (i : Y ⟶ X) (y : F.obj Y),
  证明: by
  obtain ⟨ι, f, g, hl, hc, he⟩ := has_decomp_connected_components X
  let s : Cocone (Discrete.functor f ⋙ F) := F.mapCocone (Cofan.mk X g)
  let s' : IsColimit s := isColimitOfPreserves F hl
  obtain ⟨⟨j⟩, z, h⟩ := Concrete.isColimit_exists_rep _ s' x
  refine ⟨f j, g j, z, ⟨?_, hc j, MonoCoprod

Depends on / 依赖: Cocone, Cofan.mk, Concrete, Concrete.isColimit_exists_rep, Discrete, Discrete.functor, F.mapCocone, IsColimit, MonoCoprod, MonoCoprod.mono_inj, functor, has_decomp_connected_components, isColimitOfPreserves, isColimit_exists_rep, mapCocone, mono_inj
-/
lemma fiber_in_connected_component (X : C) (x : F.obj X) : exists (Y : C) (i : Y ⟶ X) (y : F.obj Y),
    F.map i y = x ∧ IsConnected Y ∧ Mono i := by
  obtain ⟨ι, f, g, hl, hc, he⟩ := has_decomp_connected_components X
  let s : Cocone (Discrete.functor f ⋙ F) := F.mapCocone (Cofan.mk X g)
  let s' : IsColimit s := isColimitOfPreserves F hl
  obtain ⟨⟨j⟩, z, h⟩ := Concrete.isColimit_exists_rep _ s' x
  refine ⟨f j, g j, z, ⟨?_, hc j, MonoCoprod.mono_inj _ (Cofan.mk X g) hl j⟩⟩
  subst h
  rfl

/--
lemma `connected_component_unique` / 引理 `connected_component_unique`

English:
lemma connected_component_unique
  statement: {X A B : C} [IsConnected A] [IsConnected B] (a : F.obj A)
  proof: by
  /- We consider the fiber product of A and B over X. This is a non-empty (because of `h`)
  subobject of `A` and `B` and hence isomorphic to `A` and `B` by connectedness. -/
  let Y : C := pullback i j
  let u : Y ⟶ A := pullback.fst i j
  let v : Y ⟶ B := pullback.snd i j
  let G := F ⋙ Fintype

中文:
引理 connected_component_unique
  结论: {X A B : C} [IsConnected A] [IsConnected B] (a : F.obj A)
  证明: by
  /- We consider the fiber product of A and B over X. This is a non-empty (because of `h`)
  subobject of `A` and `B` and hence isomorphic to `A` and `B` by connectedness. -/
  let Y : C := pullback i j
  let u : Y ⟶ A := pullback.fst i j
  let v : Y ⟶ B := pullback.snd i j
  let G := F ⋙ Fintype

Depends on / 依赖: IsIso.id, convert
-/
lemma connected_component_unique {X A B : C} [IsConnected A] [IsConnected B] (a : F.obj A)
    (b : F.obj B) (i : A ⟶ X) (j : B ⟶ X) (h : F.map i a = F.map j b) [Mono i] [Mono j] :
    exists (f : A ≅ B), F.map f.hom a = b := by
  /- We consider the fiber product of A and B over X. This is a non-empty (because of `h`)
  subobject of `A` and `B` and hence isomorphic to `A` and `B` by connectedness. -/
  let Y : C := pullback i j
  let u : Y ⟶ A := pullback.fst i j
  let v : Y ⟶ B := pullback.snd i j
  let G := F ⋙ FintypeCat.incl
  let e : F.obj Y ≃ { p : F.obj A × F.obj B // F.map i p.1 = F.map j p.2 } :=
    fiberPullbackEquiv F i j
  let y : F.obj Y := e.symm ⟨(a, b), h⟩
  have hn : IsInitial Y -> False := not_initial_of_inhabited F y
  have : IsIso u := IsConnected.noTrivialComponent Y u hn
  have : IsIso v := IsConnected.noTrivialComponent Y v hn
  use (asIso u).symm ≪≫ asIso v
  have hu : G.map u y = a := fiberPullbackEquiv_symm_fst_apply _ _ _ h
  have hv : G.map v y = b := fiberPullbackEquiv_symm_snd_apply _ _ _ h
  rw [← hu]; rw [← hv]
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
/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def selfProd
  body: ∏ᶜ (fun _ : F.obj X => X)

中文:
定义 noncomputable
  签名: def selfProd
  定义体: ∏ᶜ (fun _ : F.obj X => X)
-/
private noncomputable def selfProd : C := ∏ᶜ (fun _ : F.obj X => X)

set_option backward.privateInPublic true in
/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def mkSelfProdFib
  body: (PreservesProduct.iso F _).inv ((Concrete.productEquiv (fun _ : F.obj X => F.obj X)).symm id)

@[simp]

中文:
定义 noncomputable
  签名: def mkSelfProdFib
  定义体: (PreservesProduct.iso F _).inv ((Concrete.productEquiv (fun _ : F.obj X => F.obj X)).symm id)

@[simp]
-/
private noncomputable def mkSelfProdFib : F.obj (selfProd F X) :=
  (PreservesProduct.iso F _).inv ((Concrete.productEquiv (fun _ : F.obj X => F.obj X)).symm id)

@[simp]
/--
lemma `mkSelfProdFib_map_π` / 引理 `mkSelfProdFib_map_π`

English:
lemma mkSelfProdFib_map_π
  given: (t : F.obj X)
  statement: F.map (Pi.π _ t) (mkSelfProdFib F X) = t
  proof: by
  rw [← piComparison_comp_π]
  simp [← PreservesProduct.iso_hom, mkSelfProdFib]

中文:
引理 mkSelfProdFib_map_π
  条件: (t : F.obj X)
  结论: F.map (Pi.π _ t) (mkSelfProdFib F X) = t
  证明: by
  rw [← piComparison_comp_π]
  simp [← PreservesProduct.iso_hom, mkSelfProdFib]
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
/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def selfProdProj (x : F.obj X)
  body: u ≫ Pi.π _ x

中文:
定义 noncomputable
  签名: def selfProdProj (x : F.obj X)
  定义体: u ≫ Pi.π _ x
-/
private noncomputable def selfProdProj (x : F.obj X) : A ⟶ X := u ≫ Pi.π _ x

variable {u a}

set_option backward.isDefEq.respectTransparency false in
set_option backward.privateInPublic true in
/--
lemma `selfProdProj_fiber` / 引理 `selfProdProj_fiber`

English:
lemma selfProdProj_fiber
  given: (x : F.obj X)
  proof: by
  simp_all

中文:
引理 selfProdProj_fiber
  条件: (x : F.obj X)
  证明: by
  simp_all
-/
private lemma selfProdProj_fiber (x : F.obj X) :
    F.map (selfProdProj u x) a = x := by
  simp_all

variable [IsConnected A]

set_option backward.privateInPublic true in
/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def fiberPerm (b : F.obj A)
  body: by
  let σ (t : F.obj X) : F.obj X := F.map (selfProdProj u t) b
  apply Equiv.ofBijective σ
  apply Finite.injective_iff_bijective.mp
  intro t s (hs : F.map (selfProdProj u t) b = F.map (selfProdProj u s) b)
  change id t = id s
  have h' : selfProdProj u t = selfProdProj u s := evaluation_injecti

中文:
定义 noncomputable
  签名: def fiberPerm (b : F.obj A)
  定义体: by
  let σ (t : F.obj X) : F.obj X := F.map (selfProdProj u t) b
  apply Equiv.ofBijective σ
  apply Finite.injective_iff_bijective.mp
  intro t s (hs : F.map (selfProdProj u t) b = F.map (selfProdProj u s) b)
  change id t = id s
  have h' : selfProdProj u t = selfProdProj u s := evaluation_injecti
-/
private noncomputable def fiberPerm (b : F.obj A) : F.obj X ≃ F.obj X := by
  let σ (t : F.obj X) : F.obj X := F.map (selfProdProj u t) b
  apply Equiv.ofBijective σ
  apply Finite.injective_iff_bijective.mp
  intro t s (hs : F.map (selfProdProj u t) b = F.map (selfProdProj u s) b)
  change id t = id s
  have h' : selfProdProj u t = selfProdProj u s := evaluation_injective_of_isConnected F A X b hs
  rw [← selfProdProj_fiber h s]; rw [← selfProdProj_fiber h t]; rw [h']

set_option backward.privateInPublic true in
/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def selfProdPermIncl (b : F.obj A)
  body: u ≫ (Pi.whiskerEquiv (fiberPerm h b) (fun _ => Iso.refl X)).inv

中文:
定义 noncomputable
  签名: def selfProdPermIncl (b : F.obj A)
  定义体: u ≫ (Pi.whiskerEquiv (fiberPerm h b) (fun _ => Iso.refl X)).inv
-/
private noncomputable def selfProdPermIncl (b : F.obj A) : A ⟶ selfProd F X :=
  u ≫ (Pi.whiskerEquiv (fiberPerm h b) (fun _ => Iso.refl X)).inv

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.privateInPublic true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Mono
  signature: u] (b
  body: mono_comp _ _

中文:
实例 [Mono
  签名: u] (b
  定义体: mono_comp _ _
-/
private instance [Mono u] (b : F.obj A) : Mono (selfProdPermIncl h b) := mono_comp _ _

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.privateInPublic true in
/--
lemma `selfProdTermIncl_fib_eq` / 引理 `selfProdTermIncl_fib_eq`

English:
lemma selfProdTermIncl_fib_eq
  given: (b : F.obj A)
  proof: by
  apply Concrete.Pi.map_ext _ F
  intro (t : F.obj X)
  convert_to F.map (selfProdProj u t) b = _
  · simp only [selfProdProj, map_comp, FintypeCat.comp_apply]; rfl
  · dsimp only [selfProdPermIncl, Pi.whiskerEquiv]
    rw [map_comp]; rw [FintypeCat.comp_apply]; rw [h]
    convert_to! F.map (self

中文:
引理 selfProdTermIncl_fib_eq
  条件: (b : F.obj A)
  证明: by
  apply Concrete.Pi.map_ext _ F
  intro (t : F.obj X)
  convert_to F.map (selfProdProj u t) b = _
  · simp only [selfProdProj, map_comp, FintypeCat.comp_apply]; rfl
  · dsimp only [selfProdPermIncl, Pi.whiskerEquiv]
    rw [map_comp]; rw [FintypeCat.comp_apply]; rw [h]
    convert_to! F.map (self
-/
private lemma selfProdTermIncl_fib_eq (b : F.obj A) :
    F.map u b = F.map (selfProdPermIncl h b) a := by
  apply Concrete.Pi.map_ext _ F
  intro (t : F.obj X)
  convert_to F.map (selfProdProj u t) b = _
  · simp only [selfProdProj, map_comp, FintypeCat.comp_apply]; rfl
  · dsimp only [selfProdPermIncl, Pi.whiskerEquiv]
    rw [map_comp]; rw [FintypeCat.comp_apply]; rw [h]
    convert_to! F.map (selfProdProj u t) b =
      (F.map (Pi.map' (fiberPerm h b) fun _ => 𝟙 X) ≫
      F.map (Pi.π (fun _ => X) t)) (mkSelfProdFib F X)
    rw [← map_comp]; rw [Pi.map'_comp_π]; rw [Category.comp_id]; rw [mkSelfProdFib_map_π F X (fiberPerm h b t)]
    rfl

set_option backward.privateInPublic true in
/--
lemma `subobj_selfProd_trans` / 引理 `subobj_selfProd_trans`

English:
lemma subobj_selfProd_trans
  given: [Mono u] (b : F.obj A)
  statement: exists (f : A ≅ A), F.map f.hom b = a
  proof: by
  apply connected_component_unique F b a u (selfProdPermIncl h b)
  exact selfProdTermIncl_fib_eq h b

中文:
引理 subobj_selfProd_trans
  条件: [Mono u] (b : F.obj A)
  结论: 存在 (f : A ≅ A), F.map f.hom b = a
  证明: by
  apply connected_component_unique F b a u (selfProdPermIncl h b)
  exact selfProdTermIncl_fib_eq h b
-/
private lemma subobj_selfProd_trans [Mono u] (b : F.obj A) : exists (f : A ≅ A), F.map f.hom b = a := by
  apply connected_component_unique F b a u (selfProdPermIncl h b)
  exact selfProdTermIncl_fib_eq h b

end GaloisRepAux

/--
lemma `exists_galois_representative` / 引理 `exists_galois_representative`

English:
lemma exists_galois_representative
  given: (X : C)
  statement: exists (A : C) (a : F.obj A),
  proof: by
  obtain ⟨A, u, a, h1, h2, h3⟩ := fiber_in_connected_component F (selfProd F X)
    (mkSelfProdFib F X)
  use A
  use a
  constructor
  · refine (isGalois_iff_pretransitive F A).mpr ⟨fun x y => ?_⟩
    obtain ⟨fi1, hfi1⟩ := subobj_selfProd_trans h1 x
    obtain ⟨fi2, hfi2⟩ := subobj_selfProd_tran

中文:
引理 exists_galois_representative
  条件: (X : C)
  结论: 存在 (A : C) (a : F.obj A),
  证明: by
  obtain ⟨A, u, a, h1, h2, h3⟩ := fiber_in_connected_component F (selfProd F X)
    (mkSelfProdFib F X)
  use A
  use a
  constructor
  · refine (isGalois_iff_pretransitive F A).mpr ⟨fun x y => ?_⟩
    obtain ⟨fi1, hfi1⟩ := subobj_selfProd_trans h1 x
    obtain ⟨fi2, hfi2⟩ := subobj_selfProd_tran

Depends on / 依赖: ConcreteCategory, ConcreteCategory.congr_hom, F.map, F.mapIso, FintypeCat, FintypeCat.comp_apply, comp_apply, congr_hom, evaluation_injecti, fi1.hom, fi2.inv, fi2.symm, fiber_in_connected_component, hom_inv_id, isGalois_iff_pretransitive, limit.lift_, mapIso, map_comp, mkSelfProdFib, selfProd
-/
lemma exists_galois_representative (X : C) : exists (A : C) (a : F.obj A),
    IsGalois A ∧ Function.Bijective (fun (f : A ⟶ X) => F.map f a) := by
  obtain ⟨A, u, a, h1, h2, h3⟩ := fiber_in_connected_component F (selfProd F X)
    (mkSelfProdFib F X)
  use A
  use a
  constructor
  · refine (isGalois_iff_pretransitive F A).mpr ⟨fun x y => ?_⟩
    obtain ⟨fi1, hfi1⟩ := subobj_selfProd_trans h1 x
    obtain ⟨fi2, hfi2⟩ := subobj_selfProd_trans h1 y
    use fi1 ≪≫ fi2.symm
    change F.map (fi1.hom ≫ fi2.inv) x = y
    simp only [map_comp, FintypeCat.comp_apply]
    rw [hfi1]; rw [← hfi2]
    exact ConcreteCategory.congr_hom (F.mapIso fi2).hom_inv_id y
  · refine ⟨evaluation_injective_of_isConnected F A X a, ?_⟩
    intro x
    use u ≫ Pi.π _ x
    exact (selfProdProj_fiber h1) x

/--
lemma `exists_hom_from_galois_of_fiber` / 引理 `exists_hom_from_galois_of_fiber`

English:
lemma exists_hom_from_galois_of_fiber
  given: (X : C) (x : F.obj X)
  proof: by
  obtain ⟨A, a, h1, h2⟩ := exists_galois_representative F X
  obtain ⟨f, hf⟩ := h2.surjective x
  exact ⟨A, f, a, h1, hf⟩

中文:
引理 exists_hom_from_galois_of_fiber
  条件: (X : C) (x : F.obj X)
  证明: by
  obtain ⟨A, a, h1, h2⟩ := exists_galois_representative F X
  obtain ⟨f, hf⟩ := h2.surjective x
  exact ⟨A, f, a, h1, hf⟩

Depends on / 依赖: exists_galois_representative, h2.surjective, surjective
-/
lemma exists_hom_from_galois_of_fiber (X : C) (x : F.obj X) :
    exists (A : C) (f : A ⟶ X) (a : F.obj A), IsGalois A ∧ F.map f a = x := by
  obtain ⟨A, a, h1, h2⟩ := exists_galois_representative F X
  obtain ⟨f, hf⟩ := h2.surjective x
  exact ⟨A, f, a, h1, hf⟩

/--
lemma `exists_hom_from_galois_of_fiber_nonempty` / 引理 `exists_hom_from_galois_of_fiber_nonempty`

English:
lemma exists_hom_from_galois_of_fiber_nonempty
  given: (X : C) (h : Nonempty (F.obj X))
  proof: by
  obtain ⟨x⟩ := h
  obtain ⟨A, f, a, h1, _⟩ := exists_hom_from_galois_of_fiber F X x
  exact ⟨A, f, h1⟩

include F in

中文:
引理 exists_hom_from_galois_of_fiber_nonempty
  条件: (X : C) (h : Nonempty (F.obj X))
  证明: by
  obtain ⟨x⟩ := h
  obtain ⟨A, f, a, h1, _⟩ := exists_hom_from_galois_of_fiber F X x
  exact ⟨A, f, h1⟩

include F in

Depends on / 依赖: exists_hom_from_galois_of_fiber
-/
lemma exists_hom_from_galois_of_fiber_nonempty (X : C) (h : Nonempty (F.obj X)) :
    exists (A : C) (_ : A ⟶ X), IsGalois A := by
  obtain ⟨x⟩ := h
  obtain ⟨A, f, a, h1, _⟩ := exists_hom_from_galois_of_fiber F X x
  exact ⟨A, f, h1⟩

include F in
/--
lemma `exists_hom_from_galois_of_connected` / 引理 `exists_hom_from_galois_of_connected`

English:
lemma exists_hom_from_galois_of_connected
  given: (X : C) [IsConnected X]
  proof: exists_hom_from_galois_of_fiber_nonempty F X inferInstance

中文:
引理 exists_hom_from_galois_of_connected
  条件: (X : C) [IsConnected X]
  证明: exists_hom_from_galois_of_fiber_nonempty F X inferInstance

Depends on / 依赖: exists_hom_from_galois_of_fiber_nonempty
-/
lemma exists_hom_from_galois_of_connected (X : C) [IsConnected X] :
    exists (A : C) (_ : A ⟶ X), IsGalois A :=
  exists_hom_from_galois_of_fiber_nonempty F X inferInstance

/--
lemma `natTrans_ext_of_isGalois` / 引理 `natTrans_ext_of_isGalois`

English:
lemma natTrans_ext_of_isGalois
  statement: {G : C ⥤ FintypeCat.{w}} {t s : F ⟶ G}
  proof: by
  ext X x
  obtain ⟨A, f, a, _, rfl⟩ := exists_hom_from_galois_of_fiber F X x
  rw [NatTrans.naturality_apply]; rw [NatTrans.naturality_apply]; rw [h A]

中文:
引理 natTrans_ext_of_isGalois
  结论: {G : C ⥤ FintypeCat.{w}} {t s : F ⟶ G}
  证明: by
  ext X x
  obtain ⟨A, f, a, _, rfl⟩ := exists_hom_from_galois_of_fiber F X x
  rw [NatTrans.naturality_apply]; rw [NatTrans.naturality_apply]; rw [h A]

Depends on / 依赖: NatTrans, NatTrans.naturality_apply, exists_hom_from_galois_of_fiber, naturality_apply
-/
lemma natTrans_ext_of_isGalois {G : C ⥤ FintypeCat.{w}} {t s : F ⟶ G}
    (h : forall (X : C) [IsGalois X], t.app X = s.app X) :
    t = s := by
  ext X x
  obtain ⟨A, f, a, _, rfl⟩ := exists_hom_from_galois_of_fiber F X x
  rw [NatTrans.naturality_apply]; rw [NatTrans.naturality_apply]; rw [h A]

end GaloisRep

end PreGaloisCategory

end CategoryTheory
