/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.Localization.Module
public import Mathlib.Algebra.Algebra.Operations

/-!
# Localization of Submodules

Results about localizations of submodules and quotient modules are provided in this file.

## Main results
- `Submodule.localized`:
  The localization of an `R`-submodule of `M` at `p` viewed as an `Rₚ`-submodule of `Mₚ`.
  A direct consequence of this is that `Rₚ` is flat over `R`; see `IsLocalization.flat`.
- `Submodule.toLocalized`:
  The localization map of a submodule `M' →ₗ[R] M'.localized p`.
- `Submodule.toLocalizedQuotient`:
  The localization map of a quotient module `M ⧸ M' →ₗ[R] LocalizedModule p M ⧸ M'.localized p`.

## TODO
- Statements regarding the exactness of localization.

-/

@[expose] public section

open nonZeroDivisors

variable {R S M N : Type*}
variable (S) [CommSemiring R] [CommSemiring S] [AddCommMonoid M] [AddCommMonoid N]
variable [Module R M] [Module R N] [Algebra R S] [Module S N] [IsScalarTower R S N]
variable (p : Submonoid R) [IsLocalization p S] (f : M ->ₗ[R] N) [IsLocalizedModule p f]
variable (M' M'' : Submodule R M)

namespace Submodule

/--
Definition of `localized₀` / `localized₀` 的定义

English:
definition localized₀
  signature: : Submodule R N where
  body: { x | exists m in M', exists s : p, IsLocalizedModule.mk' f m s = x }
  add_mem' := fun {x y} ⟨m, hm, s, hx⟩ ⟨n, hn, t, hy⟩ => ⟨t • m + s • n, add_mem (M'.smul_mem t hm)
    (M'.smul_mem s hn), s * t, by rw [← hx, ← hy, IsLocalizedModule.mk'_add_mk']⟩
  zero_mem' := ⟨0, zero_mem _, 1, by simp⟩
  smu

中文:
定义 localized₀
  签名: : Submodule R N where
  定义体: { x | exists m in M', exists s : p, IsLocalizedModule.mk' f m s = x }
  add_mem' := fun {x y} ⟨m, hm, s, hx⟩ ⟨n, hn, t, hy⟩ => ⟨t • m + s • n, add_mem (M'.smul_mem t hm)
    (M'.smul_mem s hn), s * t, by rw [← hx, ← hy, IsLocalizedModule.mk'_add_mk']⟩
  zero_mem' := ⟨0, zero_mem _, 1, by simp⟩
  smu

Depends on / 依赖: IsLocalizedModule, IsLocalizedModule.mk
-/
def localized₀ : Submodule R N where
  carrier := { x | exists m in M', exists s : p, IsLocalizedModule.mk' f m s = x }
  add_mem' := fun {x y} ⟨m, hm, s, hx⟩ ⟨n, hn, t, hy⟩ => ⟨t • m + s • n, add_mem (M'.smul_mem t hm)
    (M'.smul_mem s hn), s * t, by rw [← hx, ← hy, IsLocalizedModule.mk'_add_mk']⟩
  zero_mem' := ⟨0, zero_mem _, 1, by simp⟩
  smul_mem' r x := by
    rintro ⟨m, hm, s, hx⟩
    exact ⟨r • m, smul_mem M' _ hm, s, by rw [IsLocalizedModule.mk'_smul, hx]⟩

/--
Definition of `localized'` / `localized'` 的定义

English:
definition localized'
  signature: : Submodule S N where
  body: localized₀ p f M'
  smul_mem' := fun r x ⟨m, hm, s, hx⟩ => by
    have ⟨y, t, hyt⟩ := IsLocalization.exists_mk'_eq p r
    exact ⟨y • m, M'.smul_mem y hm, t * s, by simp [← hyt, ← hx, IsLocalizedModule.mk'_smul_mk']⟩

中文:
定义 localized'
  签名: : Submodule S N where
  定义体: localized₀ p f M'
  smul_mem' := fun r x ⟨m, hm, s, hx⟩ => by
    have ⟨y, t, hyt⟩ := IsLocalization.exists_mk'_eq p r
    exact ⟨y • m, M'.smul_mem y hm, t * s, by simp [← hyt, ← hx, IsLocalizedModule.mk'_smul_mk']⟩
-/
def localized' : Submodule S N where
  __ := localized₀ p f M'
  smul_mem' := fun r x ⟨m, hm, s, hx⟩ => by
    have ⟨y, t, hyt⟩ := IsLocalization.exists_mk'_eq p r
    exact ⟨y • m, M'.smul_mem y hm, t * s, by simp [← hyt, ← hx, IsLocalizedModule.mk'_smul_mk']⟩

/--
lemma `mem_localized₀` / 引理 `mem_localized₀`

English:
lemma mem_localized₀
  given: (x : N)
  proof: Iff.rfl

中文:
引理 mem_localized₀
  条件: (x : N)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma mem_localized₀ (x : N) :
    x in localized₀ p f M' ↔ exists m in M', exists s : p, IsLocalizedModule.mk' f m s = x :=
  Iff.rfl

/--
lemma `mem_localized'` / 引理 `mem_localized'`

English:
lemma mem_localized'
  given: (x : N)
  proof: Iff.rfl

中文:
引理 mem_localized'
  条件: (x : N)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma mem_localized' (x : N) :
    x in localized' S p f M' ↔ exists m in M', exists s : p, IsLocalizedModule.mk' f m s = x :=
  Iff.rfl

/--
lemma `restrictScalars_localized'` / 引理 `restrictScalars_localized'`

English:
lemma restrictScalars_localized'
  proof: rfl

中文:
引理 restrictScalars_localized'
  证明: rfl
-/
lemma restrictScalars_localized' :
    (localized' S p f M').restrictScalars R = localized₀ p f M' :=
  rfl

/--
theorem `localized'_eq_span` / 定理 `localized'_eq_span`

English:
theorem localized'_eq_span
  statement: localized' S p f M' = span S (f '' M')
  proof: by
  refine le_antisymm ?_ (span_le.mpr <| by rintro _ ⟨m, hm, rfl⟩; exact ⟨m, hm, 1, by simp⟩)
  rintro _ ⟨m, hm, s, rfl⟩
  rw [← one_smul R m]; rw [← mul_one s]; rw [← IsLocalizedModule.mk'_smul_mk' S]
  exact smul_mem _ _ (subset_span ⟨m, hm, by simp⟩)

中文:
定理 localized'_eq_span
  结论: localized' S p f M' = span S (f '' M')
  证明: by
  refine le_antisymm ?_ (span_le.mpr <| by rintro _ ⟨m, hm, rfl⟩; exact ⟨m, hm, 1, by simp⟩)
  rintro _ ⟨m, hm, s, rfl⟩
  rw [← one_smul R m]; rw [← mul_one s]; rw [← IsLocalizedModule.mk'_smul_mk' S]
  exact smul_mem _ _ (subset_span ⟨m, hm, by simp⟩)
-/
theorem localized'_eq_span : localized' S p f M' = span S (f '' M') := by
  refine le_antisymm ?_ (span_le.mpr <| by rintro _ ⟨m, hm, rfl⟩; exact ⟨m, hm, 1, by simp⟩)
  rintro _ ⟨m, hm, s, rfl⟩
  rw [← one_smul R m]; rw [← mul_one s]; rw [← IsLocalizedModule.mk'_smul_mk' S]
  exact smul_mem _ _ (subset_span ⟨m, hm, by simp⟩)

/--
theorem `map_le_localized₀` / 定理 `map_le_localized₀`

English:
theorem map_le_localized₀
  statement: M'.map f <= localized₀ p f M'
  proof: by
  rintro - ⟨x, hx, rfl⟩
  rw [mem_localized₀]
  exact ⟨x, hx, 1, IsLocalizedModule.mk'_one p f x⟩

中文:
定理 map_le_localized₀
  结论: M'.map f <= localized₀ p f M'
  证明: by
  rintro - ⟨x, hx, rfl⟩
  rw [mem_localized₀]
  exact ⟨x, hx, 1, IsLocalizedModule.mk'_one p f x⟩

Depends on / 依赖: IsLocalizedModule, IsLocalizedModule.mk, _one
-/
theorem map_le_localized₀ : M'.map f <= localized₀ p f M' := by
  rintro - ⟨x, hx, rfl⟩
  rw [mem_localized₀]
  exact ⟨x, hx, 1, IsLocalizedModule.mk'_one p f x⟩

/--
Definition of `localized'gi` / `localized'gi` 的定义

English:
definition localized'gi
  signature: : GaloisInsertion (localized' S p f) (comap f <| ·.restrictScalars R) where
  body: ⟨fun h m hm => h ⟨m, hm, 1, by simp⟩, fun h => by
    rw [localized'_eq_span]; rw [span_le]; apply map_le_iff_le_comap.mpr h⟩
  le_l_u N' n hn := by
    obtain ⟨⟨m, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective p f n
    refine ⟨m, ?_, s, rfl⟩
    rw [mem_comap]; rw [restrictScalars_mem]; rw [← IsLoc

中文:
定义 localized'gi
  签名: : GaloisInsertion (localized' S p f) (comap f <| ·.restrictScalars R) where
  定义体: ⟨fun h m hm => h ⟨m, hm, 1, by simp⟩, fun h => by
    rw [localized'_eq_span]; rw [span_le]; apply map_le_iff_le_comap.mpr h⟩
  le_l_u N' n hn := by
    obtain ⟨⟨m, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective p f n
    refine ⟨m, ?_, s, rfl⟩
    rw [mem_comap]; rw [restrictScalars_mem]; rw [← IsLoc
-/
def localized'gi : GaloisInsertion (localized' S p f) (comap f <| ·.restrictScalars R) where
  gc M' N' := ⟨fun h m hm => h ⟨m, hm, 1, by simp⟩, fun h => by
    rw [localized'_eq_span]; rw [span_le]; apply map_le_iff_le_comap.mpr h⟩
  le_l_u N' n hn := by
    obtain ⟨⟨m, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective p f n
    refine ⟨m, ?_, s, rfl⟩
    rw [mem_comap]; rw [restrictScalars_mem]; rw [← IsLocalizedModule.mk'_cancel' _ _ s]; rw [Submonoid.smul_def]; rw [← algebraMap_smul S]
    exact smul_mem _ _ hn
  choice x _ := localized' S p f x
  choice_eq _ _ := rfl

/--
Definition of `localized` / `localized` 的定义

English:
abbreviation localized
  signature: : Submodule (Localization p) (LocalizedModule p M)
  body: M'.localized' (Localization p) p (LocalizedModule.mkLinearMap p M)

@[simp]

中文:
缩写 localized
  签名: : Submodule (Localization p) (LocalizedModule p M)
  定义体: M'.localized' (Localization p) p (LocalizedModule.mkLinearMap p M)

@[simp]

Depends on / 依赖: Localization, LocalizedModule, LocalizedModule.mkLinearMap, localized, mkLinearMap
-/
noncomputable abbrev localized : Submodule (Localization p) (LocalizedModule p M) :=
  M'.localized' (Localization p) p (LocalizedModule.mkLinearMap p M)

@[simp]
/--
lemma `localized₀_bot` / 引理 `localized₀_bot`

English:
lemma localized₀_bot
  statement: (⊥ : Submodule R M).localized₀ p f = ⊥
  proof: by
  rw [← le_bot_iff]
  rintro _ ⟨_, rfl, s, rfl⟩
  simp only [IsLocalizedModule.mk'_zero, mem_bot]

@[simp]

中文:
引理 localized₀_bot
  结论: (⊥ : Submodule R M).localized₀ p f = ⊥
  证明: by
  rw [← le_bot_iff]
  rintro _ ⟨_, rfl, s, rfl⟩
  simp only [IsLocalizedModule.mk'_zero, mem_bot]

@[simp]

Depends on / 依赖: IsLocalizedModule, IsLocalizedModule.mk, _zero, le_bot_iff, mem_bot
-/
lemma localized₀_bot : (⊥ : Submodule R M).localized₀ p f = ⊥ := by
  rw [← le_bot_iff]
  rintro _ ⟨_, rfl, s, rfl⟩
  simp only [IsLocalizedModule.mk'_zero, mem_bot]

@[simp]
/--
lemma `localized'_bot` / 引理 `localized'_bot`

English:
lemma localized'_bot
  statement: (⊥ : Submodule R M).localized' S p f = ⊥
  proof: SetLike.ext' (by apply SetLike.ext'_iff.mp <| Submodule.localized₀_bot p f)

@[simp]

中文:
引理 localized'_bot
  结论: (⊥ : Submodule R M).localized' S p f = ⊥
  证明: SetLike.ext' (by apply SetLike.ext'_iff.mp <| Submodule.localized₀_bot p f)

@[simp]
-/
lemma localized'_bot : (⊥ : Submodule R M).localized' S p f = ⊥ :=
  SetLike.ext' (by apply SetLike.ext'_iff.mp <| Submodule.localized₀_bot p f)

@[simp]
/--
lemma `localized₀_top` / 引理 `localized₀_top`

English:
lemma localized₀_top
  statement: (⊤ : Submodule R M).localized₀ p f = ⊤
  proof: by
  rw [← top_le_iff]
  rintro x _
  obtain ⟨⟨x, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective p f x
  exact ⟨x, trivial, s, rfl⟩

@[simp]

中文:
引理 localized₀_top
  结论: (⊤ : Submodule R M).localized₀ p f = ⊤
  证明: by
  rw [← top_le_iff]
  rintro x _
  obtain ⟨⟨x, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective p f x
  exact ⟨x, trivial, s, rfl⟩

@[simp]

Depends on / 依赖: IsLocalizedModule, IsLocalizedModule.mk, _surjective, top_le_iff
-/
lemma localized₀_top : (⊤ : Submodule R M).localized₀ p f = ⊤ := by
  rw [← top_le_iff]
  rintro x _
  obtain ⟨⟨x, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective p f x
  exact ⟨x, trivial, s, rfl⟩

@[simp]
/--
lemma `localized'_top` / 引理 `localized'_top`

English:
lemma localized'_top
  statement: (⊤ : Submodule R M).localized' S p f = ⊤
  proof: SetLike.ext' (by apply SetLike.ext'_iff.mp <| Submodule.localized₀_top p f)

中文:
引理 localized'_top
  结论: (⊤ : Submodule R M).localized' S p f = ⊤
  证明: SetLike.ext' (by apply SetLike.ext'_iff.mp <| Submodule.localized₀_top p f)
-/
lemma localized'_top : (⊤ : Submodule R M).localized' S p f = ⊤ :=
  SetLike.ext' (by apply SetLike.ext'_iff.mp <| Submodule.localized₀_top p f)

/--
theorem `localized₀_inf` / 定理 `localized₀_inf`

English:
theorem localized₀_inf
  proof: by
  simp only [Submodule.ext_iff, Submodule.mem_inf, mem_localized₀]
  refine fun x => ⟨by grind, ?_⟩
  rintro ⟨⟨i, hi, s, hs⟩, j, hj, t, ht⟩
  have h := ht.trans hs.symm
  rw [IsLocalizedModule.mk'_eq_mk'_iff] at h
  obtain ⟨k, hk⟩ := h
  refine ⟨(k * t) • i, ⟨M'.smul_of_tower_mem (k * t) hi, ?_⟩,

中文:
定理 localized₀_inf
  证明: by
  simp only [Submodule.ext_iff, Submodule.mem_inf, mem_localized₀]
  refine fun x => ⟨by grind, ?_⟩
  rintro ⟨⟨i, hi, s, hs⟩, j, hj, t, ht⟩
  have h := ht.trans hs.symm
  rw [IsLocalizedModule.mk'_eq_mk'_iff] at h
  obtain ⟨k, hk⟩ := h
  refine ⟨(k * t) • i, ⟨M'.smul_of_tower_mem (k * t) hi, ?_⟩,

Depends on / 依赖: IsLocalizedModule, IsLocalizedModule.mk, Submodule, Submodule.ext_iff, Submodule.mem_inf, _cancel_left, _eq_mk, _iff, ext_iff, hs.symm, ht.trans, mem_inf, mul_smul, smul_of_tower_mem, smul_smul
-/
theorem localized₀_inf :
    (M' ⊓ M'').localized₀ p f = M'.localized₀ p f ⊓ M''.localized₀ p f := by
  simp only [Submodule.ext_iff, Submodule.mem_inf, mem_localized₀]
  refine fun x => ⟨by grind, ?_⟩
  rintro ⟨⟨i, hi, s, hs⟩, j, hj, t, ht⟩
  have h := ht.trans hs.symm
  rw [IsLocalizedModule.mk'_eq_mk'_iff] at h
  obtain ⟨k, hk⟩ := h
  refine ⟨(k * t) • i, ⟨M'.smul_of_tower_mem (k * t) hi, ?_⟩, k * s * t, ?_⟩
  · rw [mul_smul, hk, smul_smul]
    exact M''.smul_of_tower_mem (k * s) hj
  · rwa [mul_smul, hk, smul_smul, IsLocalizedModule.mk'_cancel_left]

/--
theorem `localized'_inf` / 定理 `localized'_inf`

English:
theorem localized'_inf
  proof: SetLike.ext' (by apply SetLike.ext'_iff.mp <| Submodule.localized₀_inf p f M' M'')

中文:
定理 localized'_inf
  证明: SetLike.ext' (by apply SetLike.ext'_iff.mp <| Submodule.localized₀_inf p f M' M'')
-/
theorem localized'_inf :
    (M' ⊓ M'').localized' S p f = M'.localized' S p f ⊓ M''.localized' S p f :=
  SetLike.ext' (by apply SetLike.ext'_iff.mp <| Submodule.localized₀_inf p f M' M'')

/--
theorem `localized'_iSup` / 定理 `localized'_iSup`

English:
theorem localized'_iSup
  given: {ι : Type*} (g : ι -> Submodule R M)
  proof: by
  exact GaloisConnection.l_iSup (localized'gi S p f).gc

中文:
定理 localized'_iSup
  条件: {ι : 类型} (g : ι -> Submodule R M)
  证明: by
  exact GaloisConnection.l_iSup (localized'gi S p f).gc
-/
theorem localized'_iSup {ι : Type*} (g : ι -> Submodule R M) :
    (⨆ i, g i).localized' S p f = ⨆ i, (g i).localized' S p f := by
  exact GaloisConnection.l_iSup (localized'gi S p f).gc

/--
theorem `localized₀_iSup` / 定理 `localized₀_iSup`

English:
theorem localized₀_iSup
  given: {ι : Type*} (g : ι -> Submodule R M)
  proof: by
  let : Module (Localization p) N := IsLocalizedModule.module p f
  have : IsScalarTower R (Localization p) N := IsLocalizedModule.isScalarTower_module p f
  simpa using! congr_arg (restrictScalars R) (localized'_iSup (Localization p) p f g)

中文:
定理 localized₀_iSup
  条件: {ι : 类型} (g : ι -> Submodule R M)
  证明: by
  let : Module (Localization p) N := IsLocalizedModule.module p f
  have : IsScalarTower R (Localization p) N := IsLocalizedModule.isScalarTower_module p f
  simpa using! congr_arg (restrictScalars R) (localized'_iSup (Localization p) p f g)

Depends on / 依赖: IsLocalizedModule, IsLocalizedModule.isScalarTower_module, IsLocalizedModule.module, IsScalarTower, Localization, Module, _iSup, congr_arg, isScalarTower_module, localized, module, restrictScalars
-/
theorem localized₀_iSup {ι : Type*} (g : ι -> Submodule R M) :
    (⨆ i, g i).localized₀ p f = ⨆ i, (g i).localized₀ p f := by
  let : Module (Localization p) N := IsLocalizedModule.module p f
  have : IsScalarTower R (Localization p) N := IsLocalizedModule.isScalarTower_module p f
  simpa using! congr_arg (restrictScalars R) (localized'_iSup (Localization p) p f g)

/--
Definition of `localized₀FrameHom` / `localized₀FrameHom` 的定义

English:
definition localized₀FrameHom
  signature: : FrameHom (Submodule R M) (Submodule R N) where
  body: localized₀ p f
  map_inf' := localized₀_inf p f
  map_top' := localized₀_top p f
  map_sSup' s := by rw [sSup_eq_iSup', localized₀_iSup, sSup_image']

@[simp]

中文:
定义 localized₀FrameHom
  签名: : FrameHom (Submodule R M) (Submodule R N) where
  定义体: localized₀ p f
  map_inf' := localized₀_inf p f
  map_top' := localized₀_top p f
  map_sSup' s := by rw [sSup_eq_iSup', localized₀_iSup, sSup_image']

@[simp]
-/
noncomputable def localized₀FrameHom : FrameHom (Submodule R M) (Submodule R N) where
  toFun := localized₀ p f
  map_inf' := localized₀_inf p f
  map_top' := localized₀_top p f
  map_sSup' s := by rw [sSup_eq_iSup', localized₀_iSup, sSup_image']

@[simp]
/--
lemma `IsLocalizedModule.localized₀FrameHom_apply` / 引理 `IsLocalizedModule.localized₀FrameHom_apply`

English:
lemma IsLocalizedModule.localized₀FrameHom_apply
  proof: rfl

中文:
引理 IsLocalizedModule.localized₀FrameHom_apply
  证明: rfl
-/
lemma IsLocalizedModule.localized₀FrameHom_apply :
    localized₀FrameHom p f M' = M'.localized₀ p f :=
  rfl

/--
Definition of `localized'FrameHom` / `localized'FrameHom` 的定义

English:
definition localized'FrameHom
  signature: :
  body: localized' S p f
  map_inf' := localized'_inf S p f
  map_top' := localized'_top S p f
  map_sSup' s := by rw [sSup_eq_iSup', localized'_iSup, sSup_image']

@[simp]

中文:
定义 localized'FrameHom
  签名: :
  定义体: localized' S p f
  map_inf' := localized'_inf S p f
  map_top' := localized'_top S p f
  map_sSup' s := by rw [sSup_eq_iSup', localized'_iSup, sSup_image']

@[simp]
-/
noncomputable def localized'FrameHom :
    FrameHom (Submodule R M) (Submodule S N) where
  toFun := localized' S p f
  map_inf' := localized'_inf S p f
  map_top' := localized'_top S p f
  map_sSup' s := by rw [sSup_eq_iSup', localized'_iSup, sSup_image']

@[simp]
/--
lemma `IsLocalizedModule.localized'FrameHom_apply` / 引理 `IsLocalizedModule.localized'FrameHom_apply`

English:
lemma IsLocalizedModule.localized'FrameHom_apply
  proof: rfl

@[simp]

中文:
引理 IsLocalizedModule.localized'FrameHom_apply
  证明: rfl

@[simp]
-/
lemma IsLocalizedModule.localized'FrameHom_apply :
    localized'FrameHom S p f M' = M'.localized' S p f :=
  rfl

@[simp]
/--
lemma `localized'_span` / 引理 `localized'_span`

English:
lemma localized'_span
  given: (s : Set M)
  statement: (span R s).localized' S p f = span S (f '' s)
  proof: by
  rw [localized'_eq_span]; rw [← map_coe]; rw [map_span]; rw [span_span_of_tower]

中文:
引理 localized'_span
  条件: (s : Set M)
  结论: (span R s).localized' S p f = span S (f '' s)
  证明: by
  rw [localized'_eq_span]; rw [← map_coe]; rw [map_span]; rw [span_span_of_tower]
-/
lemma localized'_span (s : Set M) : (span R s).localized' S p f = span S (f '' s) := by
  rw [localized'_eq_span]; rw [← map_coe]; rw [map_span]; rw [span_span_of_tower]

/--
lemma `localized₀_smul` / 引理 `localized₀_smul`

English:
lemma localized₀_smul
  given: (I : Submodule R R)
  statement: (I • M').localized₀ p f = I • M'.localized₀ p f
  proof: by
  apply le_antisymm
  · rintro _ ⟨a, ha, s, rfl⟩
    refine Submodule.smul_induction_on ha ?_ ?_
    · intro r hr n hn
      rw [IsLocalizedModule.mk'_smul]
      exact Submodule.smul_mem_smul hr ⟨n, hn, s, rfl⟩
    · simp +contextual only [IsLocalizedModule.mk'_add, add_mem, implies_true]
  · re

中文:
引理 localized₀_smul
  条件: (I : Submodule R R)
  结论: (I • M').localized₀ p f = I • M'.localized₀ p f
  证明: by
  apply le_antisymm
  · rintro _ ⟨a, ha, s, rfl⟩
    refine Submodule.smul_induction_on ha ?_ ?_
    · intro r hr n hn
      rw [IsLocalizedModule.mk'_smul]
      exact Submodule.smul_mem_smul hr ⟨n, hn, s, rfl⟩
    · simp +contextual only [IsLocalizedModule.mk'_add, add_mem, implies_true]
  · re

Depends on / 依赖: IsLocalizedModule, IsLocalizedModule.mk, Submodule, Submodule.smul_induction_on, Submodule.smul_le.mpr, Submodule.smul_mem_smul, _add, _smul, add_mem, contextual, implies_true, le_antisymm, single_mem_span_single, smul_induction_on, smul_le, smul_mem_smul
-/
lemma localized₀_smul (I : Submodule R R) : (I • M').localized₀ p f = I • M'.localized₀ p f := by
  apply le_antisymm
  · rintro _ ⟨a, ha, s, rfl⟩
    refine Submodule.smul_induction_on ha ?_ ?_
    · intro r hr n hn
      rw [IsLocalizedModule.mk'_smul]
      exact Submodule.smul_mem_smul hr ⟨n, hn, s, rfl⟩
    · simp +contextual only [IsLocalizedModule.mk'_add, add_mem, implies_true]
  · refine Submodule.smul_le.mpr ?_
    rintro r hr _ ⟨a, ha, s, rfl⟩
    rw [← IsLocalizedModule.mk'_smul]
    exact ⟨_, Submodule.smul_mem_smul hr ha, s, rfl⟩

/--
lemma `restrictScalars_localized'_smul` / 引理 `restrictScalars_localized'_smul`

English:
lemma restrictScalars_localized'_smul
  given: (I : Submodule R R) (N' : Submodule S N)
  proof: by
  refine le_antisymm (fun x hx => ?_) (Submodule.smul_le.mpr fun r hr n hn => ?_)
  · refine smul_induction_on ((Submodule.restrictScalars_mem _ _ _).mp hx) ?_ fun _ _ => add_mem
    rintro _ ⟨r, hr, s, rfl⟩ n hn
    rw [← IsLocalization.mk'_eq_mk']; rw [IsLocalization.mk'_eq_mul_mk'_one]; rw [mu

中文:
引理 restrictScalars_localized'_smul
  条件: (I : Submodule R R) (N' : Submodule S N)
  证明: by
  refine le_antisymm (fun x hx => ?_) (Submodule.smul_le.mpr fun r hr n hn => ?_)
  · refine smul_induction_on ((Submodule.restrictScalars_mem _ _ _).mp hx) ?_ fun _ _ => add_mem
    rintro _ ⟨r, hr, s, rfl⟩ n hn
    rw [← IsLocalization.mk'_eq_mk']; rw [IsLocalization.mk'_eq_mul_mk'_one]; rw [mu
-/
lemma restrictScalars_localized'_smul (I : Submodule R R) (N' : Submodule S N) :
    (I.localized' S p (Algebra.linearMap R S) • N').restrictScalars R =
      I • N'.restrictScalars R := by
  refine le_antisymm (fun x hx => ?_) (Submodule.smul_le.mpr fun r hr n hn => ?_)
  · refine smul_induction_on ((Submodule.restrictScalars_mem _ _ _).mp hx) ?_ fun _ _ => add_mem
    rintro _ ⟨r, hr, s, rfl⟩ n hn
    rw [← IsLocalization.mk'_eq_mk']; rw [IsLocalization.mk'_eq_mul_mk'_one]; rw [mul_smul]; rw [algebraMap_smul]
    exact smul_mem_smul hr ((Submodule.restrictScalars_mem _ _ _).mpr <| smul_mem _ _ hn)
  · rw [← algebraMap_smul S, Submodule.restrictScalars_mem]
    exact Submodule.smul_mem_smul ⟨_, hr, 1, by simp⟩ hn

/--
lemma `localized'_smul` / 引理 `localized'_smul`

English:
lemma localized'_smul
  given: (I : Submodule R R)
  proof: Submodule.restrictScalars_injective R _ _ by
    simp_rw [restrictScalars_localized'_smul, restrictScalars_localized', localized₀_smul]

中文:
引理 localized'_smul
  条件: (I : Submodule R R)
  证明: Submodule.restrictScalars_injective R _ _ by
    simp_rw [restrictScalars_localized'_smul, restrictScalars_localized', localized₀_smul]
-/
lemma localized'_smul (I : Submodule R R) :
    (I • M').localized' S p f = I.localized' S p (Algebra.linearMap R S) • M'.localized' S p f :=
Submodule.restrictScalars_injective R _ _ by
    simp_rw [restrictScalars_localized'_smul, restrictScalars_localized', localized₀_smul]

/-- The localization map of a submodule. -/
@[simps!]
/--
Definition of `toLocalized₀` / `toLocalized₀` 的定义

English:
definition toLocalized₀
  signature: : M' ->ₗ[R] M'.localized₀ p f
  body: f.restrict fun x hx => ⟨x, hx, 1, by simp⟩

中文:
定义 toLocalized₀
  签名: : M' ->ₗ[R] M'.localized₀ p f
  定义体: f.restrict fun x hx => ⟨x, hx, 1, by simp⟩

Depends on / 依赖: f.restrict, restrict
-/
def toLocalized₀ : M' ->ₗ[R] M'.localized₀ p f := f.restrict fun x hx => ⟨x, hx, 1, by simp⟩

/-- The localization map of a submodule. -/
@[simps!]
/--
Definition of `toLocalized'` / `toLocalized'` 的定义

English:
definition toLocalized'
  signature: : M' ->ₗ[R] M'.localized' S p f
  body: toLocalized₀ p f M'

中文:
定义 toLocalized'
  签名: : M' ->ₗ[R] M'.localized' S p f
  定义体: toLocalized₀ p f M'
-/
def toLocalized' : M' ->ₗ[R] M'.localized' S p f := toLocalized₀ p f M'

/--
Definition of `toLocalized` / `toLocalized` 的定义

English:
abbreviation toLocalized
  signature: : M' ->ₗ[R] M'.localized p
  body: M'.toLocalized' (Localization p) p (LocalizedModule.mkLinearMap p M)

中文:
缩写 toLocalized
  签名: : M' ->ₗ[R] M'.localized p
  定义体: M'.toLocalized' (Localization p) p (LocalizedModule.mkLinearMap p M)

Depends on / 依赖: Localization, LocalizedModule, LocalizedModule.mkLinearMap, mkLinearMap, toLocalized
-/
noncomputable abbrev toLocalized : M' ->ₗ[R] M'.localized p :=
  M'.toLocalized' (Localization p) p (LocalizedModule.mkLinearMap p M)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsLocalizedModule p (M'.toLocalized₀ p f)
  body: by
    simp_rw [Module.End.isUnit_iff]
    constructor
    · exact fun _ _ e => Subtype.ext
        (IsLocalizedModule.smul_injective f x (congr_arg Subtype.val e))
    · rintro ⟨_, m, hm, s, rfl⟩
      refine ⟨⟨IsLocalizedModule.mk' f m (s * x), ⟨_, hm, _, rfl⟩⟩, Subtype.ext ?_⟩
      rw [Module.al

中文:
实例 :
  签名: IsLocalizedModule p (M'.toLocalized₀ p f)
  定义体: by
    simp_rw [Module.End.isUnit_iff]
    constructor
    · exact fun _ _ e => Subtype.ext
        (IsLocalizedModule.smul_injective f x (congr_arg Subtype.val e))
    · rintro ⟨_, m, hm, s, rfl⟩
      refine ⟨⟨IsLocalizedModule.mk' f m (s * x), ⟨_, hm, _, rfl⟩⟩, Subtype.ext ?_⟩
      rw [Module.al

Depends on / 依赖: IsLocalizedModule, IsLocalizedModule.mk, IsLocalizedModule.smul_injective, Module, Module.End.isUnit_iff, Module.algebraMap_end_apply, SetLike, SetLike.val_smul_of_tower, Submonoid, Submonoid.smul_def, Subtype, Subtype.ext, Subtype.val, _cancel_right, _smul, algebraMap_end_apply, congr_arg, exists_of, isUnit_iff, simp_rw
-/
instance : IsLocalizedModule p (M'.toLocalized₀ p f) where
  map_units x := by
    simp_rw [Module.End.isUnit_iff]
    constructor
    · exact fun _ _ e => Subtype.ext
        (IsLocalizedModule.smul_injective f x (congr_arg Subtype.val e))
    · rintro ⟨_, m, hm, s, rfl⟩
      refine ⟨⟨IsLocalizedModule.mk' f m (s * x), ⟨_, hm, _, rfl⟩⟩, Subtype.ext ?_⟩
      rw [Module.algebraMap_end_apply]; rw [SetLike.val_smul_of_tower]; rw [← IsLocalizedModule.mk'_smul]; rw [← Submonoid.smul_def]; rw [IsLocalizedModule.mk'_cancel_right]
  surj := by
    rintro ⟨y, x, hx, s, rfl⟩
    exact ⟨⟨⟨x, hx⟩, s⟩, by ext; simp⟩
  exists_of_eq e := by simpa [Subtype.ext_iff] using
      IsLocalizedModule.exists_of_eq (S := p) (f := f) (congr_arg Subtype.val e)

/--
Instance `isLocalizedModule` / 实例 `isLocalizedModule`

English:
instance isLocalizedModule
  signature: : IsLocalizedModule p (M'.toLocalized' S p f)
  body: inferInstanceAs (IsLocalizedModule p (M'.toLocalized₀ p f))

中文:
实例 isLocalizedModule
  签名: : IsLocalizedModule p (M'.toLocalized' S p f)
  定义体: inferInstanceAs (IsLocalizedModule p (M'.toLocalized₀ p f))

Depends on / 依赖: IsLocalizedModule
-/
instance isLocalizedModule : IsLocalizedModule p (M'.toLocalized' S p f) :=
  inferInstanceAs (IsLocalizedModule p (M'.toLocalized₀ p f))

/--
Definition of `localizedEquiv` / `localizedEquiv` 的定义

English:
definition localizedEquiv
  signature: : M'.localized p ≃ₗ[Localization p] LocalizedModule p M'
  body: have := IsLocalization.linearMap_compatibleSMul p
  IsLocalizedModule.linearEquiv p (M'.toLocalized p) (LocalizedModule.mkLinearMap _ _)
.restrictScalars _

中文:
定义 localizedEquiv
  签名: : M'.localized p ≃ₗ[Localization p] LocalizedModule p M'
  定义体: have := IsLocalization.linearMap_compatibleSMul p
  IsLocalizedModule.linearEquiv p (M'.toLocalized p) (LocalizedModule.mkLinearMap _ _)
.restrictScalars _

Depends on / 依赖: IsLocalization, IsLocalization.linearMap_compatibleSMul, IsLocalizedModule, IsLocalizedModule.linearEquiv, LocalizedModule, LocalizedModule.mkLinearMap, linearEquiv, linearMap_compatibleSMul, mkLinearMap, restrictScalars, toLocalized
-/
noncomputable def localizedEquiv : M'.localized p ≃ₗ[Localization p] LocalizedModule p M' :=
  have := IsLocalization.linearMap_compatibleSMul p
  IsLocalizedModule.linearEquiv p (M'.toLocalized p) (LocalizedModule.mkLinearMap _ _)
.restrictScalars _

open scoped Pointwise

/--
lemma `localized₀_le_localized₀_of_smul_le` / 引理 `localized₀_le_localized₀_of_smul_le`

English:
lemma localized₀_le_localized₀_of_smul_le
  given: {P Q : Submodule R M} (x : p) (h : x • P <= Q)
  proof: by
  rintro - ⟨a, ha, r, rfl⟩
  refine ⟨x • a, h ⟨a, ha, rfl⟩, x * r, ?_⟩
  simp

中文:
引理 localized₀_le_localized₀_of_smul_le
  条件: {P Q : Submodule R M} (x : p) (h : x • P <= Q)
  证明: by
  rintro - ⟨a, ha, r, rfl⟩
  refine ⟨x • a, h ⟨a, ha, rfl⟩, x * r, ?_⟩
  simp
-/
lemma localized₀_le_localized₀_of_smul_le {P Q : Submodule R M} (x : p) (h : x • P <= Q) :
    P.localized₀ p f <= Q.localized₀ p f := by
  rintro - ⟨a, ha, r, rfl⟩
  refine ⟨x • a, h ⟨a, ha, rfl⟩, x * r, ?_⟩
  simp

/--
lemma `localized'_le_localized'_of_smul_le` / 引理 `localized'_le_localized'_of_smul_le`

English:
lemma localized'_le_localized'_of_smul_le
  given: {P Q : Submodule R M} (x : p) (h : x • P <= Q)
  proof: localized₀_le_localized₀_of_smul_le p f x h

中文:
引理 localized'_le_localized'_of_smul_le
  条件: {P Q : Submodule R M} (x : p) (h : x • P <= Q)
  证明: localized₀_le_localized₀_of_smul_le p f x h
-/
lemma localized'_le_localized'_of_smul_le {P Q : Submodule R M} (x : p) (h : x • P <= Q) :
    P.localized' S p f <= Q.localized' S p f :=
  localized₀_le_localized₀_of_smul_le p f x h

end Submodule

section Quotient

variable {R S M N : Type*}
variable (S) [CommRing R] [CommRing S] [AddCommGroup M] [AddCommGroup N]
variable [Module R M] [Module R N] [Algebra R S] [Module S N] [IsScalarTower R S N]
variable (p : Submonoid R) [IsLocalization p S] (f : M ->ₗ[R] N) [IsLocalizedModule p f]
variable (M' : Submodule R M)

/--
Definition of `Submodule.toLocalizedQuotient'` / `Submodule.toLocalizedQuotient'` 的定义

English:
definition Submodule.toLocalizedQuotient'
  signature: : M ⧸ M' ->ₗ[R] N ⧸ M'.localized' S p f
  body: Submodule.mapQ M' ((M'.localized' S p f).restrictScalars R) f (fun x hx => ⟨x, hx, 1, by simp⟩)

中文:
定义 Submodule.toLocalizedQuotient'
  签名: : M ⧸ M' ->ₗ[R] N ⧸ M'.localized' S p f
  定义体: Submodule.mapQ M' ((M'.localized' S p f).restrictScalars R) f (fun x hx => ⟨x, hx, 1, by simp⟩)

Depends on / 依赖: Submodule, Submodule.mapQ, localized, restrictScalars
-/
def Submodule.toLocalizedQuotient' : M ⧸ M' ->ₗ[R] N ⧸ M'.localized' S p f :=
  Submodule.mapQ M' ((M'.localized' S p f).restrictScalars R) f (fun x hx => ⟨x, hx, 1, by simp⟩)

/--
Definition of `Submodule.toLocalizedQuotient` / `Submodule.toLocalizedQuotient` 的定义

English:
abbreviation Submodule.toLocalizedQuotient
  signature: :
  body: M'.toLocalizedQuotient' (Localization p) p (LocalizedModule.mkLinearMap p M)

@[simp]

中文:
缩写 Submodule.toLocalizedQuotient
  签名: :
  定义体: M'.toLocalizedQuotient' (Localization p) p (LocalizedModule.mkLinearMap p M)

@[simp]

Depends on / 依赖: Localization, LocalizedModule, LocalizedModule.mkLinearMap, mkLinearMap, toLocalizedQuotient
-/
noncomputable abbrev Submodule.toLocalizedQuotient :
    M ⧸ M' ->ₗ[R] LocalizedModule p M ⧸ M'.localized p :=
  M'.toLocalizedQuotient' (Localization p) p (LocalizedModule.mkLinearMap p M)

@[simp]
/--
lemma `Submodule.toLocalizedQuotient'_mk` / 引理 `Submodule.toLocalizedQuotient'_mk`

English:
lemma Submodule.toLocalizedQuotient'_mk
  given: (x : M)
  proof: rfl

中文:
引理 Submodule.toLocalizedQuotient'_mk
  条件: (x : M)
  证明: rfl
-/
lemma Submodule.toLocalizedQuotient'_mk (x : M) :
    M'.toLocalizedQuotient' S p f (Submodule.Quotient.mk x) = Submodule.Quotient.mk (f x) := rfl

open Submodule Submodule.Quotient IsLocalization in
/--
Instance `IsLocalizedModule.toLocalizedQuotient'` / 实例 `IsLocalizedModule.toLocalizedQuotient'`

English:
instance IsLocalizedModule.toLocalizedQuotient'
  signature: (M' : Submodule R M)
  body: by
    refine (Module.End.isUnit_iff _).mpr ⟨fun m n e => ?_, fun m => ⟨(IsLocalization.mk' S 1 x) • m,
      by rw [Module.algebraMap_end_apply, ← smul_assoc, smul_mk'_one, mk'_self', one_smul]⟩⟩
    obtain ⟨⟨m, rfl⟩, n, rfl⟩ := PProd.mk (mk_surjective _ m) (mk_surjective _ n)
    simp only [Module

中文:
实例 IsLocalizedModule.toLocalizedQuotient'
  签名: (M' : Submodule R M)
  定义体: by
    refine (Module.End.isUnit_iff _).mpr ⟨fun m n e => ?_, fun m => ⟨(IsLocalization.mk' S 1 x) • m,
      by rw [Module.algebraMap_end_apply, ← smul_assoc, smul_mk'_one, mk'_self', one_smul]⟩⟩
    obtain ⟨⟨m, rfl⟩, n, rfl⟩ := PProd.mk (mk_surjective _ m) (mk_surjective _ n)
    simp only [Module

Depends on / 依赖: IsLocalization, IsLocalization.mk, Module, Module.End.isUnit_iff, Module.algebraMap_end_apply, PProd.mk, Quotient, Submodule, Submodule.Quot, Submodule.Quotient.eq, Submodule.smul_mem, _one, _self, algebraMap_end_apply, isUnit_iff, mk_smul, mk_surjective, one_smul, replace, smul_assoc
-/
instance IsLocalizedModule.toLocalizedQuotient' (M' : Submodule R M) :
    IsLocalizedModule p (M'.toLocalizedQuotient' S p f) where
  map_units x := by
    refine (Module.End.isUnit_iff _).mpr ⟨fun m n e => ?_, fun m => ⟨(IsLocalization.mk' S 1 x) • m,
      by rw [Module.algebraMap_end_apply, ← smul_assoc, smul_mk'_one, mk'_self', one_smul]⟩⟩
    obtain ⟨⟨m, rfl⟩, n, rfl⟩ := PProd.mk (mk_surjective _ m) (mk_surjective _ n)
    simp only [Module.algebraMap_end_apply, ← mk_smul, Submodule.Quotient.eq, ← smul_sub] at e
    replace e := Submodule.smul_mem _ (IsLocalization.mk' S 1 x) e
    rwa [smul_comm, ← smul_assoc, smul_mk'_one, mk'_self', one_smul, ← Submodule.Quotient.eq] at e
  surj y := by
    obtain ⟨y, rfl⟩ := mk_surjective _ y
    obtain ⟨⟨y, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective p f y
    exact ⟨⟨Submodule.Quotient.mk y, s⟩,
      by simp only [Function.uncurry_apply_pair, toLocalizedQuotient'_mk, ← mk_smul, mk'_cancel']⟩
  exists_of_eq {m n} e := by
    obtain ⟨⟨m, rfl⟩, n, rfl⟩ := PProd.mk (mk_surjective _ m) (mk_surjective _ n)
    obtain ⟨x, hx, s, hs⟩ : f (m - n) in _ := by simpa [Submodule.Quotient.eq] using! e
    obtain ⟨c, hc⟩ := exists_of_eq (S := p) (show f (s • (m - n)) = f x by simp [-map_sub, ← hs])
    exact ⟨c * s, by simpa only [← Quotient.mk_smul, Submodule.Quotient.eq,
      ← smul_sub, mul_smul, hc] using! M'.smul_mem c hx⟩

instance (M' : Submodule R M) : IsLocalizedModule p (M'.toLocalizedQuotient p) :=
  IsLocalizedModule.toLocalizedQuotient' _ _ _ _

/--
Definition of `localizedQuotientEquiv` / `localizedQuotientEquiv` 的定义

English:
definition localizedQuotientEquiv
  signature: :
  body: have := IsLocalization.linearMap_compatibleSMul p
  IsLocalizedModule.linearEquiv p (M'.toLocalizedQuotient p) (LocalizedModule.mkLinearMap _ _)
.restrictScalars _

中文:
定义 localizedQuotientEquiv
  签名: :
  定义体: have := IsLocalization.linearMap_compatibleSMul p
  IsLocalizedModule.linearEquiv p (M'.toLocalizedQuotient p) (LocalizedModule.mkLinearMap _ _)
.restrictScalars _

Depends on / 依赖: IsLocalization, IsLocalization.linearMap_compatibleSMul, IsLocalizedModule, IsLocalizedModule.linearEquiv, LocalizedModule, LocalizedModule.mkLinearMap, linearEquiv, linearMap_compatibleSMul, mkLinearMap, restrictScalars, toLocalizedQuotient
-/
noncomputable def localizedQuotientEquiv :
    (LocalizedModule p M ⧸ M'.localized p) ≃ₗ[Localization p] LocalizedModule p (M ⧸ M') :=
  have := IsLocalization.linearMap_compatibleSMul p
  IsLocalizedModule.linearEquiv p (M'.toLocalizedQuotient p) (LocalizedModule.mkLinearMap _ _)
.restrictScalars _

end Quotient

namespace LinearMap

variable {P : Type*} [AddCommMonoid P] [Module R P]
variable {Q : Type*} [AddCommMonoid Q] [Module R Q] [Module S Q] [IsScalarTower R S Q]
variable (f' : P ->ₗ[R] Q) [IsLocalizedModule p f']

open Submodule IsLocalizedModule

/--
lemma `ker_localizedMap_eq_localized₀_ker` / 引理 `ker_localizedMap_eq_localized₀_ker`

English:
lemma ker_localizedMap_eq_localized₀_ker
  given: (g : M ->ₗ[R] P)
  proof: by
  ext x
  simp only [Submodule.mem_localized₀, mem_ker]
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨⟨a, b⟩, rfl⟩ := IsLocalizedModule.mk'_surjective p f x
    simp only [Function.uncurry_apply_pair, map_mk', mk'_eq_zero, eq_zero_iff p f'] at h
    obtain ⟨c, hc⟩ := h
    refine ⟨c • a, by simpa, c * b

中文:
引理 ker_localizedMap_eq_localized₀_ker
  条件: (g : M ->ₗ[R] P)
  证明: by
  ext x
  simp only [Submodule.mem_localized₀, mem_ker]
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨⟨a, b⟩, rfl⟩ := IsLocalizedModule.mk'_surjective p f x
    simp only [Function.uncurry_apply_pair, map_mk', mk'_eq_zero, eq_zero_iff p f'] at h
    obtain ⟨c, hc⟩ := h
    refine ⟨c • a, by simpa, c * b

Depends on / 依赖: Function, Function.uncurry_apply_pair, IsLocalizedModule, IsLocalizedModule.map_mk, IsLocalizedModule.mk, Submodule, Submodule.mem_localized, _eq_zero, _surjective, eq_zero_iff, map_mk, mem_ker, uncurry_apply_pair
-/
lemma ker_localizedMap_eq_localized₀_ker (g : M ->ₗ[R] P) :
    ker (map p f f' g) = (ker g).localized₀ p f := by
  ext x
  simp only [Submodule.mem_localized₀, mem_ker]
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨⟨a, b⟩, rfl⟩ := IsLocalizedModule.mk'_surjective p f x
    simp only [Function.uncurry_apply_pair, map_mk', mk'_eq_zero, eq_zero_iff p f'] at h
    obtain ⟨c, hc⟩ := h
    refine ⟨c • a, by simpa, c * b, by simp⟩
  · rintro ⟨m, hm, a, ha, rfl⟩
    simp [IsLocalizedModule.map_mk', hm]

/--
lemma `localized'_ker_eq_ker_localizedMap` / 引理 `localized'_ker_eq_ker_localizedMap`

English:
lemma localized'_ker_eq_ker_localizedMap
  given: (g : M ->ₗ[R] P)
  proof: SetLike.ext (by apply SetLike.ext_iff.mp (f.ker_localizedMap_eq_localized₀_ker p f' g).symm)

中文:
引理 localized'_ker_eq_ker_localizedMap
  条件: (g : M ->ₗ[R] P)
  证明: SetLike.ext (by apply SetLike.ext_iff.mp (f.ker_localizedMap_eq_localized₀_ker p f' g).symm)

Depends on / 依赖: SetLike, SetLike.ext, SetLike.ext_iff.mp, ext_iff, f.ker_localizedMap_eq_localized
-/
lemma localized'_ker_eq_ker_localizedMap (g : M ->ₗ[R] P) :
    (ker g).localized' S p f = ker ((map p f f' g).extendScalarsOfIsLocalization p S) :=
  SetLike.ext (by apply SetLike.ext_iff.mp (f.ker_localizedMap_eq_localized₀_ker p f' g).symm)

/--
lemma `ker_localizedMap_eq_localized'_ker` / 引理 `ker_localizedMap_eq_localized'_ker`

English:
lemma ker_localizedMap_eq_localized'_ker
  given: (g : M ->ₗ[R] P)
  proof: by
  ext
  simp [localized'_ker_eq_ker_localizedMap S p f f']

中文:
引理 ker_localizedMap_eq_localized'_ker
  条件: (g : M ->ₗ[R] P)
  证明: by
  ext
  simp [localized'_ker_eq_ker_localizedMap S p f f']

Depends on / 依赖: _ker_eq_ker_localizedMap, localized
-/
lemma ker_localizedMap_eq_localized'_ker (g : M ->ₗ[R] P) :
    ker (map p f f' g) = ((ker g).localized' S p f).restrictScalars _ := by
  ext
  simp [localized'_ker_eq_ker_localizedMap S p f f']

/--
The canonical map from the kernel of `g` to the kernel of `g` localized at a submonoid.

This is a localization map by `LinearMap.toKerLocalized_isLocalizedModule`.
-/
@[simps!]
/--
Definition of `toKerIsLocalized` / `toKerIsLocalized` 的定义

English:
definition toKerIsLocalized
  signature: (g : M ->ₗ[R] P)
  body: f.restrict (fun x hx => by simp [mem_ker, mem_ker.mp hx])

include S in

中文:
定义 toKerIsLocalized
  签名: (g : M ->ₗ[R] P)
  定义体: f.restrict (fun x hx => by simp [mem_ker, mem_ker.mp hx])

include S in

Depends on / 依赖: f.restrict, mem_ker, mem_ker.mp, restrict
-/
noncomputable def toKerIsLocalized (g : M ->ₗ[R] P) :
    ker g ->ₗ[R] ker (map p f f' g) :=
  f.restrict (fun x hx => by simp [mem_ker, mem_ker.mp hx])

include S in
/--
lemma `toKerLocalized_isLocalizedModule` / 引理 `toKerLocalized_isLocalizedModule`

English:
lemma toKerLocalized_isLocalizedModule
  given: (g : M ->ₗ[R] P)
  proof: let e : Submodule.localized' S p f (ker g) ≃ₗ[S]
      ker ((map p f f' g).extendScalarsOfIsLocalization p S) :=
    LinearEquiv.ofEq _ _ (localized'_ker_eq_ker_localizedMap S p f f' g)
  IsLocalizedModule.of_linearEquiv p (Submodule.toLocalized' S p f (ker g)) (e.restrictScalars R)

中文:
引理 toKerLocalized_isLocalizedModule
  条件: (g : M ->ₗ[R] P)
  证明: let e : Submodule.localized' S p f (ker g) ≃ₗ[S]
      ker ((map p f f' g).extendScalarsOfIsLocalization p S) :=
    LinearEquiv.ofEq _ _ (localized'_ker_eq_ker_localizedMap S p f f' g)
  IsLocalizedModule.of_linearEquiv p (Submodule.toLocalized' S p f (ker g)) (e.restrictScalars R)

Depends on / 依赖: IsLocalizedModule, IsLocalizedModule.of_linearEquiv, LinearEquiv, LinearEquiv.ofEq, Submodule, Submodule.localized, Submodule.toLocalized, _ker_eq_ker_localizedMap, e.restrictScalars, extendScalarsOfIsLocalization, localized, of_linearEquiv, restrictScalars, toLocalized
-/
lemma toKerLocalized_isLocalizedModule (g : M ->ₗ[R] P) :
    IsLocalizedModule p (toKerIsLocalized p f f' g) :=
  let e : Submodule.localized' S p f (ker g) ≃ₗ[S]
      ker ((map p f f' g).extendScalarsOfIsLocalization p S) :=
    LinearEquiv.ofEq _ _ (localized'_ker_eq_ker_localizedMap S p f f' g)
  IsLocalizedModule.of_linearEquiv p (Submodule.toLocalized' S p f (ker g)) (e.restrictScalars R)

/--
lemma `range_localizedMap_eq_localized₀_range` / 引理 `range_localizedMap_eq_localized₀_range`

English:
lemma range_localizedMap_eq_localized₀_range
  given: (g : M ->ₗ[R] P)
  proof: by
  ext; simp [mem_localized₀, mem_range, (mk'_surjective p f).exists]

中文:
引理 range_localizedMap_eq_localized₀_range
  条件: (g : M ->ₗ[R] P)
  证明: by
  ext; simp [mem_localized₀, mem_range, (mk'_surjective p f).exists]

Depends on / 依赖: _surjective, mem_range
-/
lemma range_localizedMap_eq_localized₀_range (g : M ->ₗ[R] P) :
    range (map p f f' g) = (range g).localized₀ p f' := by
  ext; simp [mem_localized₀, mem_range, (mk'_surjective p f).exists]

/--
lemma `localized'_range_eq_range_localizedMap` / 引理 `localized'_range_eq_range_localizedMap`

English:
lemma localized'_range_eq_range_localizedMap
  given: (g : M ->ₗ[R] P)
  proof: SetLike.ext (by apply SetLike.ext_iff.mp (f.range_localizedMap_eq_localized₀_range p f' g).symm)

中文:
引理 localized'_range_eq_range_localizedMap
  条件: (g : M ->ₗ[R] P)
  证明: SetLike.ext (by apply SetLike.ext_iff.mp (f.range_localizedMap_eq_localized₀_range p f' g).symm)
-/
lemma localized'_range_eq_range_localizedMap (g : M ->ₗ[R] P) :
    (range g).localized' S p f' = range ((map p f f' g).extendScalarsOfIsLocalization p S) :=
  SetLike.ext (by apply SetLike.ext_iff.mp (f.range_localizedMap_eq_localized₀_range p f' g).symm)

/--
lemma `localizedMap_surjective_iff_subsingleton_localized_coker` / 引理 `localizedMap_surjective_iff_subsingleton_localized_coker`

English:
lemma localizedMap_surjective_iff_subsingleton_localized_coker
  statement: {R M N : Type*} [CommRing R]
  proof: by
  simp [(localizedQuotientEquiv S φ.range).symm.subsingleton_congr,
    LinearMap.localized'_range_eq_range_localizedMap (Localization S) S
      (LocalizedModule.mkLinearMap S M) (LocalizedModule.mkLinearMap S N),
    LinearMap.range_eq_top, LocalizedModule.map, mapExtendScalars]

中文:
引理 localizedMap_surjective_iff_subsingleton_localized_coker
  结论: {R M N : 类型} [CommRing R]
  证明: by
  simp [(localizedQuotientEquiv S φ.range).symm.subsingleton_congr,
    LinearMap.localized'_range_eq_range_localizedMap (Localization S) S
      (LocalizedModule.mkLinearMap S M) (LocalizedModule.mkLinearMap S N),
    LinearMap.range_eq_top, LocalizedModule.map, mapExtendScalars]

Depends on / 依赖: LinearMap, LinearMap.localized, LinearMap.range_eq_top, Localization, LocalizedModule, LocalizedModule.map, LocalizedModule.mkLinearMap, _range_eq_range_localizedMap, localized, localizedQuotientEquiv, mapExtendScalars, mkLinearMap, range_eq_top, subsingleton_congr, symm.subsingleton_congr
-/
lemma localizedMap_surjective_iff_subsingleton_localized_coker {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (S : Submonoid R) (φ : M ->ₗ[R] N) :
    Function.Surjective (LocalizedModule.map S φ) ↔
      Subsingleton (LocalizedModule S (N ⧸ φ.range)) := by
  simp [(localizedQuotientEquiv S φ.range).symm.subsingleton_congr,
    LinearMap.localized'_range_eq_range_localizedMap (Localization S) S
      (LocalizedModule.mkLinearMap S M) (LocalizedModule.mkLinearMap S N),
    LinearMap.range_eq_top, LocalizedModule.map, mapExtendScalars]

end LinearMap
