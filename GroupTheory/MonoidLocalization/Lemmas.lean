/-
Copyright (c) 2025 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
module

public import Mathlib.Algebra.Group.Pi.Units
public import Mathlib.Data.Fintype.Basic
public import Mathlib.GroupTheory.MonoidLocalization.Basic

/-!
# Lemmas about localizations of commutative monoids

that requires additional imports.
-/

public section

namespace Submonoid.IsLocalizationMap

open Finset in
/--
theorem `surj_pi_of_finite` / 定理 `surj_pi_of_finite`

English:
theorem surj_pi_of_finite
  statement: {M N F ι : Type*} [Finite ι]
  proof: by
  choose x hx using hf.surj
  have ⟨_⟩ := nonempty_fintype ι
  classical
  refine ⟨∏ i : ι, (x (n i)).2, fun i => (x (n i)).1 * ∏ j in univ.erase i, (x (n j)).2, fun i => ?_⟩
  rw [← univ.mul_prod_erase _ (mem_univ i)]; rw [S.coe_mul]; rw [map_mul]; rw [← mul_assoc]; rw [hx]; rw [map_mul]

中文:
定理 surj_pi_of_finite
  结论: {M N F ι : 类型} [有限 ι]
  证明: by
  choose x hx using hf.surj
  have ⟨_⟩ := nonempty_fintype ι
  classical
  refine ⟨∏ i : ι, (x (n i)).2, fun i => (x (n i)).1 * ∏ j in univ.erase i, (x (n j)).2, fun i => ?_⟩
  rw [← univ.mul_prod_erase _ (mem_univ i)]; rw [S.coe_mul]; rw [map_mul]; rw [← mul_assoc]; rw [hx]; rw [map_mul]
-/
@[to_additive] theorem surj_pi_of_finite {M N F ι : Type*} [Finite ι]
    [CommMonoid M] [CommMonoid N] [FunLike F M N] [MulHomClass F M N] {f : F}
    {S : Submonoid M} (hf : IsLocalizationMap S f) (n : ι -> N) :
    exists (s : S) (x : ι -> M), forall i, n i * f s = f (x i) := by
  choose x hx using hf.surj
  have ⟨_⟩ := nonempty_fintype ι
  classical
  refine ⟨∏ i : ι, (x (n i)).2, fun i => (x (n i)).1 * ∏ j in univ.erase i, (x (n j)).2, fun i => ?_⟩
  rw [← univ.mul_prod_erase _ (mem_univ i)]; rw [S.coe_mul]; rw [map_mul]; rw [← mul_assoc]; rw [hx]; rw [map_mul]

/--
theorem `pi` / 定理 `pi`

English:
theorem pi
  statement: {ι : Type*} {M N : ι -> Type*}
  proof: Pi.isUnit_iff.mpr fun i => (hf i).map_units ⟨_, m.2 i ⟨⟩⟩
  surj z := by
    choose x hx using fun i => (hf i).surj
    exact ⟨⟨fun i => (x i (z i)).1, ⟨_, fun i _ => (x i (z i)).2.2⟩⟩, funext fun i => hx i (z i)⟩
  exists_of_eq {x y} eq := by
    choose c hc using fun i => (hf i).exists_of_eq congr

中文:
定理 pi
  结论: {ι : 类型} {M N : ι -> 类型}
  证明: Pi.isUnit_iff.mpr fun i => (hf i).map_units ⟨_, m.2 i ⟨⟩⟩
  surj z := by
    choose x hx using fun i => (hf i).surj
    exact ⟨⟨fun i => (x i (z i)).1, ⟨_, fun i _ => (x i (z i)).2.2⟩⟩, funext fun i => hx i (z i)⟩
  exists_of_eq {x y} eq := by
    choose c hc using fun i => (hf i).exists_of_eq congr
-/
@[to_additive] protected theorem pi {ι : Type*} {M N : ι -> Type*}
    [forall i, CommMonoid (M i)] [forall i, CommMonoid (N i)] (S : Π i, Submonoid (M i))
    {f : Π i, M i -> N i} (hf : forall i, IsLocalizationMap (S i) (f i)) :
    IsLocalizationMap (Submonoid.pi .univ S) (Pi.map f) where
  map_units m := Pi.isUnit_iff.mpr fun i => (hf i).map_units ⟨_, m.2 i ⟨⟩⟩
  surj z := by
    choose x hx using fun i => (hf i).surj
    exact ⟨⟨fun i => (x i (z i)).1, ⟨_, fun i _ => (x i (z i)).2.2⟩⟩, funext fun i => hx i (z i)⟩
  exists_of_eq {x y} eq := by
    choose c hc using fun i => (hf i).exists_of_eq congr($eq i)
    exact ⟨⟨_, fun i _ => (c i).2⟩, funext hc⟩

end Submonoid.IsLocalizationMap
