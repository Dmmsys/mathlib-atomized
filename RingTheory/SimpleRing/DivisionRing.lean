/-
Copyright (c) 2026 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edison Xie
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Simple
public import Mathlib.RingTheory.SimpleModule.Basic

/-!

## Simple modules over division rings
This file contains some results about simple modules over division rings.

# Main results

* `DivisionRing.nonempty_linearEquiv_of_isSimpleModule` : There is an unique simple module over
  a division ring, up to isomorphism.
* `isSimpleModule_iff_eq_zero_or_injective` : A module is simple if and only if it is nontrivial
  and every linear map from it is either zero or injective, this is the module analogue of
  `RingHom.injective`
* `IsSimpleModule.obj_of_isEquivalence` : If `M` is a simple module over a ring `R`, and
  `e : ModuleCat R ⥤ ModuleCat S` is an equivalence of categories,
  then `e(M)` is a simple module over `S`.

## Tags
Noncommutative algebra, simple module, division ring

-/

@[expose] public section

universe u v

open CategoryTheory

variable (R S : Type*) [DivisionRing R] [DivisionRing S] (e : ModuleCat R ≌ ModuleCat S)

/--
lemma `DivisionRing.nonempty_linearEquiv_of_isSimpleModule` / 引理 `DivisionRing.nonempty_linearEquiv_of_isSimpleModule`

English:
lemma DivisionRing.nonempty_linearEquiv_of_isSimpleModule
  statement: (N : Type*) [AddCommGroup N]
  proof: by
  obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp ‹_›
  exact ⟨e ≪≫ₗ I.quotEquivOfEqBot ((eq_bot_or_eq_top I).resolve_right hI.ne_top)⟩

中文:
引理 除环.nonempty_linearEquiv_of_isSimpleModule
  结论: (N : 类型) [加法交换群 N]
  证明: by
  obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp ‹_›
  exact ⟨e ≪≫ₗ I.quotEquivOfEqBot ((eq_bot_or_eq_top I).resolve_right hI.ne_top)⟩

Depends on / 依赖: I.quotEquivOfEqBot, eq_bot_or_eq_top, hI.ne_top, isSimpleModule_iff_quot_maximal, isSimpleModule_iff_quot_maximal.mp, ne_top, quotEquivOfEqBot, resolve_right
-/
lemma DivisionRing.nonempty_linearEquiv_of_isSimpleModule (N : Type*) [AddCommGroup N]
    [Module S N] [IsSimpleModule S N] : Nonempty (N ≃ₗ[S] S) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp ‹_›
  exact ⟨e ≪≫ₗ I.quotEquivOfEqBot ((eq_bot_or_eq_top I).resolve_right hI.ne_top)⟩

/--
lemma `isSimpleModule_iff_eq_zero_or_injective` / 引理 `isSimpleModule_iff_eq_zero_or_injective`

English:
lemma isSimpleModule_iff_eq_zero_or_injective
  statement: (R : Type u) (M : Type v) [Ring R] [AddCommGroup M]
  proof: .elim .1 hM.1.1, fun N _ _ f => hM.1.2 (LinearMap.ker f) ⟨fun hM => ⟨Submodule.nontrivial_iff _
    (fun h => Or.inr <| by rwa [LinearMap.ker_eq_bot] at h) (fun h => Or.inl <|by simp_all)⟩,
.2 ⟨fun p => (hM2 (M ⧸ p) p.mkQ).elim fun ⟨hM1, hM2⟩ => isSimpleModule_iff R M
  (fun h => Or.inr <| by simpa 

中文:
引理 isSimpleModule_iff_eq_zero_or_injective
  结论: (R : 类型u) (M : 类型v) [环 R] [加法交换群 M]
  证明: .elim .1 hM.1.1, fun N _ _ f => hM.1.2 (LinearMap.ker f) ⟨fun hM => ⟨Submodule.nontrivial_iff _
    (fun h => Or.inr <| by rwa [LinearMap.ker_eq_bot] at h) (fun h => Or.inl <|by simp_all)⟩,
.2 ⟨fun p => (hM2 (M ⧸ p) p.mkQ).elim fun ⟨hM1, hM2⟩ => isSimpleModule_iff R M
  (fun h => Or.inr <| by simpa 

Depends on / 依赖: LinearMap, LinearMap.ext_iff, LinearMap.ker, LinearMap.ker_eq_bot, Or.inl, Or.inr, Submodule, Submodule.ext_iff, Submodule.nontrivial_iff, eq_bot_iff, ext_iff, isSimpleModule_iff, ker_eq_bot, nontrivial_iff, p.mkQ
-/
lemma isSimpleModule_iff_eq_zero_or_injective (R : Type u) (M : Type v) [Ring R] [AddCommGroup M]
    [Module R M] : IsSimpleModule R M ↔ (Nontrivial M ∧ forall (N : Type v) [AddCommGroup N]
    [Module R N] (f : M ->ₗ[R] N), f = 0 ∨ Function.Injective f) :=
.elim .1 hM.1.1, fun N _ _ f => hM.1.2 (LinearMap.ker f) ⟨fun hM => ⟨Submodule.nontrivial_iff _
    (fun h => Or.inr <| by rwa [LinearMap.ker_eq_bot] at h) (fun h => Or.inl <|by simp_all)⟩,
.2 ⟨fun p => (hM2 (M ⧸ p) p.mkQ).elim fun ⟨hM1, hM2⟩ => isSimpleModule_iff R M
  (fun h => Or.inr <| by simpa [Submodule.ext_iff, LinearMap.ext_iff] using h)
  (fun h => Or.inl <| eq_bot_iff.2 fun x hx => h (by simp [hx]))⟩⟩

/--
lemma `IsSimpleModule.obj_of_isEquivalence` / 引理 `IsSimpleModule.obj_of_isEquivalence`

English:
lemma IsSimpleModule.obj_of_isEquivalence
  proof: by
  rw [← simple_iff_isSimpleModule'] at *
  exact simple_obj e M

中文:
引理 是单模.obj_of_isEquivalence
  证明: by
  rw [← simple_iff_isSimpleModule'] at *
  exact simple_obj e M

Depends on / 依赖: simple_iff_isSimpleModule, simple_obj
-/
lemma IsSimpleModule.obj_of_isEquivalence
    {R S : Type*} [Ring R] [Ring S] (e : ModuleCat R ⥤ ModuleCat S)
    [e.IsEquivalence] (M : ModuleCat R) [IsSimpleModule R M] :
    IsSimpleModule S (e.obj M) := by
  rw [← simple_iff_isSimpleModule'] at *
  exact simple_obj e M
