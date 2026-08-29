/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Module.LocalizedModule.Basic

/-!
# API for localized modules away from an element

We provide some specialized API for the localization of a module away from an element.
-/

public section

namespace IsLocalizedModule.Away

variable {R : Type*} [CommSemiring R] {M N : Type*} [AddCommMonoid M] [AddCommMonoid N]
  [Module R M] [Module R N] {f : M ->ₗ[R] N} {r : R}

/--
lemma `mk` / 引理 `mk`

English:
lemma mk
  statement: (h₁ : IsUnit (algebraMap R (Module.End R N) r))
  proof: fun ⟨_, ⟨n, rfl⟩⟩ => by simp [h₁.pow]
  surj x := by
    obtain ⟨n, y, hy⟩ := h₂ x
    use ⟨y, ⟨_, n, rfl⟩⟩, hy
  exists_of_eq {x y} hxy := by
    obtain ⟨n, hn⟩ := h₃ _ _ hxy
    use ⟨_, n, rfl⟩, hn

中文:
引理 mk
  结论: (h₁ : IsUnit (algebraMap R (Module.End R N) r))
  证明: fun ⟨_, ⟨n, rfl⟩⟩ => by simp [h₁.pow]
  surj x := by
    obtain ⟨n, y, hy⟩ := h₂ x
    use ⟨y, ⟨_, n, rfl⟩⟩, hy
  exists_of_eq {x y} hxy := by
    obtain ⟨n, hn⟩ := h₃ _ _ hxy
    use ⟨_, n, rfl⟩, hn
-/
lemma mk (h₁ : IsUnit (algebraMap R (Module.End R N) r))
    (h₂ : forall (x : N), exists (n : Nat) (y : M), r ^ n • x = f y)
    (h₃ : forall (x y : M), f x = f y -> exists (n : Nat), r ^ n • x = r ^ n • y) :
    IsLocalizedModule.Away r f where
  map_units := fun ⟨_, ⟨n, rfl⟩⟩ => by simp [h₁.pow]
  surj x := by
    obtain ⟨n, y, hy⟩ := h₂ x
    use ⟨y, ⟨_, n, rfl⟩⟩, hy
  exists_of_eq {x y} hxy := by
    obtain ⟨n, hn⟩ := h₃ _ _ hxy
    use ⟨_, n, rfl⟩, hn

/--
lemma `mk_of_addCommGroup` / 引理 `mk_of_addCommGroup`

English:
lemma mk_of_addCommGroup
  statement: {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
  proof: by
  refine IsLocalizedModule.Away.mk h₁ h₂ fun x y hxy => ?_
  have : f (x - y) = 0 := by simp [hxy]
  obtain ⟨n, hn⟩ := h₃ _ this
  use n
  simpa [smul_sub, sub_eq_zero] using hn

中文:
引理 mk_of_addCommGroup
  结论: {M N : 类型} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
  证明: by
  refine IsLocalizedModule.Away.mk h₁ h₂ fun x y hxy => ?_
  have : f (x - y) = 0 := by simp [hxy]
  obtain ⟨n, hn⟩ := h₃ _ this
  use n
  simpa [smul_sub, sub_eq_zero] using hn

Depends on / 依赖: IsLocalizedModule, IsLocalizedModule.Away.mk, smul_sub, sub_eq_zero
-/
lemma mk_of_addCommGroup {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    {f : M ->ₗ[R] N} {r : R} (h₁ : IsUnit (algebraMap R (Module.End R N) r))
    (h₂ : forall (x : N), exists (n : Nat) (y : M), r ^ n • x = f y)
    (h₃ : forall (x : M), f x = 0 -> exists (n : Nat), r ^ n • x = 0) :
    IsLocalizedModule.Away r f := by
  refine IsLocalizedModule.Away.mk h₁ h₂ fun x y hxy => ?_
  have : f (x - y) = 0 := by simp [hxy]
  obtain ⟨n, hn⟩ := h₃ _ this
  use n
  simpa [smul_sub, sub_eq_zero] using hn

variable (r) [IsLocalizedModule.Away r f]

variable (f) in
include f in
/--
lemma `isUnit_algebraMap` / 引理 `isUnit_algebraMap`

English:
lemma isUnit_algebraMap
  statement: IsUnit (algebraMap R (Module.End R N) r)
  proof: IsLocalizedModule.map_units (S := .powers r) f ⟨_, 1, by simp⟩

中文:
引理 isUnit_algebraMap
  结论: IsUnit (algebraMap R (Module.End R N) r)
  证明: IsLocalizedModule.map_units (S := .powers r) f ⟨_, 1, by simp⟩

Depends on / 依赖: IsLocalizedModule, IsLocalizedModule.map_units, map_units, powers
-/
lemma isUnit_algebraMap : IsUnit (algebraMap R (Module.End R N) r) :=
  IsLocalizedModule.map_units (S := .powers r) f ⟨_, 1, by simp⟩

/--
lemma `exists_of_eq` / 引理 `exists_of_eq`

English:
lemma exists_of_eq
  given: {x y : M} (h : f x = f y)
  statement: exists (n : Nat), r ^ n • x = r ^ n • y
  proof: by
  obtain ⟨⟨_, n, rfl⟩, hn⟩ := IsLocalizedModule.exists_of_eq (S := .powers r) h
  use n, hn

中文:
引理 exists_of_eq
  条件: {x y : M} (h : f x = f y)
  结论: 存在 (n : 自然数), r ^ n • x = r ^ n • y
  证明: by
  obtain ⟨⟨_, n, rfl⟩, hn⟩ := IsLocalizedModule.exists_of_eq (S := .powers r) h
  use n, hn

Depends on / 依赖: IsLocalizedModule, IsLocalizedModule.exists_of_eq, exists_of_eq, powers
-/
lemma exists_of_eq {x y : M} (h : f x = f y) : exists (n : Nat), r ^ n • x = r ^ n • y := by
  obtain ⟨⟨_, n, rfl⟩, hn⟩ := IsLocalizedModule.exists_of_eq (S := .powers r) h
  use n, hn

variable (f) in
/--
lemma `surj` / 引理 `surj`

English:
lemma surj
  given: (y : N)
  statement: exists (n : Nat) (x : M), r ^ n • y = f x
  proof: by
  obtain ⟨⟨x, ⟨_, n, rfl⟩⟩, h⟩ := IsLocalizedModule.surj (S := .powers r) f y
  use n, x, h

中文:
引理 surj
  条件: (y : N)
  结论: 存在 (n : 自然数) (x : M), r ^ n • y = f x
  证明: by
  obtain ⟨⟨x, ⟨_, n, rfl⟩⟩, h⟩ := IsLocalizedModule.surj (S := .powers r) f y
  use n, x, h

Depends on / 依赖: IsLocalizedModule, IsLocalizedModule.surj, powers
-/
lemma surj (y : N) : exists (n : Nat) (x : M), r ^ n • y = f x := by
  obtain ⟨⟨x, ⟨_, n, rfl⟩⟩, h⟩ := IsLocalizedModule.surj (S := .powers r) f y
  use n, x, h

/--
lemma `of_associated` / 引理 `of_associated`

English:
lemma of_associated
  given: {r r' : R} (h : Associated r r') [IsLocalizedModule.Away r f]
  proof: by
  obtain ⟨u, rfl⟩ := h
  rw [mul_comm]
  refine .mk ?_ ?_ ?_
  · simp [IsUnit.mul, isUnit_algebraMap f r, u.isUnit.map _]
  · intro y
    obtain ⟨n, x, hx⟩ := surj f r y
    use n, (u ^ n) • x
    simp [mul_pow, ← hx, mul_smul, Units.smul_def]
  · intro x y hxy
    obtain ⟨n, hn⟩ := exists_of_eq 

中文:
引理 of_associated
  条件: {r r' : R} (h : Associated r r') [IsLocalizedModule.Away r f]
  证明: by
  obtain ⟨u, rfl⟩ := h
  rw [mul_comm]
  refine .mk ?_ ?_ ?_
  · simp [IsUnit.mul, isUnit_algebraMap f r, u.isUnit.map _]
  · intro y
    obtain ⟨n, x, hx⟩ := surj f r y
    use n, (u ^ n) • x
    simp [mul_pow, ← hx, mul_smul, Units.smul_def]
  · intro x y hxy
    obtain ⟨n, hn⟩ := exists_of_eq 

Depends on / 依赖: IsUnit, IsUnit.mul, Units.smul_def, exists_of_eq, isUnit, isUnit_algebraMap, mul_comm, mul_pow, mul_smul, smul_def, u.isUnit.map
-/
lemma of_associated {r r' : R} (h : Associated r r') [IsLocalizedModule.Away r f] :
    IsLocalizedModule.Away r' f := by
  obtain ⟨u, rfl⟩ := h
  rw [mul_comm]
  refine .mk ?_ ?_ ?_
  · simp [IsUnit.mul, isUnit_algebraMap f r, u.isUnit.map _]
  · intro y
    obtain ⟨n, x, hx⟩ := surj f r y
    use n, (u ^ n) • x
    simp [mul_pow, ← hx, mul_smul, Units.smul_def]
  · intro x y hxy
    obtain ⟨n, hn⟩ := exists_of_eq r hxy
    use n
    simp [mul_pow, mul_smul, hn]

/--
lemma `iff_of_associated` / 引理 `iff_of_associated`

English:
lemma iff_of_associated
  given: {r r' : R} (h : Associated r r')
  proof: ⟨fun _ => .of_associated h, fun _ => .of_associated h.symm⟩

中文:
引理 iff_of_associated
  条件: {r r' : R} (h : Associated r r')
  证明: ⟨fun _ => .of_associated h, fun _ => .of_associated h.symm⟩

Depends on / 依赖: h.symm, of_associated
-/
lemma iff_of_associated {r r' : R} (h : Associated r r') :
    IsLocalizedModule.Away r f ↔ IsLocalizedModule.Away r' f :=
  ⟨fun _ => .of_associated h, fun _ => .of_associated h.symm⟩

end IsLocalizedModule.Away
