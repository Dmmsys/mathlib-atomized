/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Algebra.Exact.Basic

/-!

# The snake lemma in terms of modules

The snake lemma is proven in `Mathlib/Algebra/Homology/ShortComplex/SnakeLemma.lean` for all abelian
categories, but for definitional equality and universe issues we reprove them here for modules.

## Main results
- `SnakeLemma.δ`: The connecting homomorphism guaranteed by the snake lemma.
- `SnakeLemma.exact_δ_left`: The connecting homomorphism is exact on the right.
- `SnakeLemma.exact_δ_right`: The connecting homomorphism is exact on the left.

-/

@[expose] public section

open LinearMap hiding id
open Function

/-!
Suppose we have an exact commutative diagram
```
        K₂ -F-→ K₃
        | |
        ι₂ ι₃
        ↓ ↓
M₁ -f₁→ M₂ -f₂→ M₃
| | |
i₁ i₂ i₃
↓ ↓ ↓
N₁ -g₁→ N₂ -g₂→ N₃
| |
π₁ π₂
↓ ↓
C₁ -G-→ C₂

```
such that `f₂` is surjective with a (set-theoretic) section `σ`, `g₁` is injective with a
(set-theoretic) retraction `ρ`, and that `ι₃` is injective and `π₁` is surjective.
-/

variable {R : Type*} [CommRing R] {M₁ M₂ M₃ N₁ N₂ N₃ : Type*}
  [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂] [AddCommGroup M₃] [Module R M₃]
  [AddCommGroup N₁] [Module R N₁] [AddCommGroup N₂] [Module R N₂] [AddCommGroup N₃] [Module R N₃]
  (i₁ : M₁ ->ₗ[R] N₁) (i₂ : M₂ ->ₗ[R] N₂) (i₃ : M₃ ->ₗ[R] N₃)
  (f₁ : M₁ ->ₗ[R] M₂) (f₂ : M₂ ->ₗ[R] M₃) (hf : Exact f₁ f₂)
  (g₁ : N₁ ->ₗ[R] N₂) (g₂ : N₂ ->ₗ[R] N₃) (hg : Exact g₁ g₂)
  (h₁ : g₁.comp i₁ = i₂.comp f₁) (h₂ : g₂.comp i₂ = i₃.comp f₂)
  (σ : M₃ -> M₂) (hσ : f₂ ∘ σ = id) (ρ : N₂ -> N₁) (hρ : ρ ∘ g₁ = id)
  {K₂ K₃ C₁ C₂ : Type*} [AddCommGroup K₂] [Module R K₂] [AddCommGroup K₃] [Module R K₃]
  [AddCommGroup C₁] [Module R C₁] [AddCommGroup C₂] [Module R C₂]
  (ι₂ : K₂ ->ₗ[R] M₂) (hι₂ : Exact ι₂ i₂) (ι₃ : K₃ ->ₗ[R] M₃) (hι₃ : Exact ι₃ i₃)
  (π₁ : N₁ ->ₗ[R] C₁) (hπ₁ : Exact i₁ π₁) (π₂ : N₂ ->ₗ[R] C₂) (hπ₂ : Exact i₂ π₂)

include hg hρ h₂ hσ hι₃ in
/--
lemma `SnakeLemma.δ_aux` / 引理 `SnakeLemma.δ_aux`

English:
lemma SnakeLemma.δ_aux
  given: (x : K₃)
  statement: g₁ (ρ (i₂ (σ (ι₃ x)))) = i₂ (σ (ι₃ x))
  proof: by
  obtain ⟨d, hd⟩ : i₂ (σ (ι₃ x)) in range g₁ := by
    rw [← hg.linearMap_ker_eq]; rw [mem_ker]; rw [show g₂ (i₂ _) = i₃ (f₂ _) from DFunLike.congr_fun h₂ _]; rw [← @comp_apply _ _ _ f₂ σ]; rw [hσ]; rw [id_eq]; rw [← i₃.comp_apply]; rw [hι₃.linearMap_comp_eq_zero]; rw [zero_apply]
  rw [← hd]; rw

中文:
引理 SnakeLemma.δ_aux
  条件: (x : K₃)
  结论: g₁ (ρ (i₂ (σ (ι₃ x)))) = i₂ (σ (ι₃ x))
  证明: by
  obtain ⟨d, hd⟩ : i₂ (σ (ι₃ x)) in range g₁ := by
    rw [← hg.linearMap_ker_eq]; rw [mem_ker]; rw [show g₂ (i₂ _) = i₃ (f₂ _) from DFunLike.congr_fun h₂ _]; rw [← @comp_apply _ _ _ f₂ σ]; rw [hσ]; rw [id_eq]; rw [← i₃.comp_apply]; rw [hι₃.linearMap_comp_eq_zero]; rw [zero_apply]
  rw [← hd]; rw

Depends on / 依赖: DFunLike, DFunLike.congr_fun, comp_apply, congr_fun, hg.linearMap_ker_eq, id_eq, linearMap_comp_eq_zero, linearMap_ker_eq, mem_ker, zero_apply
-/
lemma SnakeLemma.δ_aux (x : K₃) : g₁ (ρ (i₂ (σ (ι₃ x)))) = i₂ (σ (ι₃ x)) := by
  obtain ⟨d, hd⟩ : i₂ (σ (ι₃ x)) in range g₁ := by
    rw [← hg.linearMap_ker_eq]; rw [mem_ker]; rw [show g₂ (i₂ _) = i₃ (f₂ _) from DFunLike.congr_fun h₂ _]; rw [← @comp_apply _ _ _ f₂ σ]; rw [hσ]; rw [id_eq]; rw [← i₃.comp_apply]; rw [hι₃.linearMap_comp_eq_zero]; rw [zero_apply]
  rw [← hd]; rw [← ρ.comp_apply]; rw [hρ]; rw [id_eq]

include hf h₁ hρ hπ₁ in
/--
lemma `SnakeLemma.eq_of_eq` / 引理 `SnakeLemma.eq_of_eq`

English:
lemma SnakeLemma.eq_of_eq
  statement: (x : K₃)
  proof: by
  have := sub_eq_zero.mpr (hy₁.trans hy₂.symm)
  rw [← map_sub]; rw [hf] at this
  obtain ⟨d, hd⟩ := this
  rw [← eq_sub_iff_add_eq.mp hd]; rw [map_add]; rw [← hz₂]; rw [← sub_eq_iff_eq_add]; rw [← map_sub]; rw [← i₂.comp_apply]; rw [← h₁]; rw [LinearMap.comp_apply]; rw [(HasLeftInverse.injective

中文:
引理 SnakeLemma.eq_of_eq
  结论: (x : K₃)
  证明: by
  have := sub_eq_zero.mpr (hy₁.trans hy₂.symm)
  rw [← map_sub]; rw [hf] at this
  obtain ⟨d, hd⟩ := this
  rw [← eq_sub_iff_add_eq.mp hd]; rw [map_add]; rw [← hz₂]; rw [← sub_eq_iff_eq_add]; rw [← map_sub]; rw [← i₂.comp_apply]; rw [← h₁]; rw [LinearMap.comp_apply]; rw [(HasLeftInverse.injective

Depends on / 依赖: HasLeftInverse, HasLeftInverse.injective, LinearMap, LinearMap.comp_apply, comp_apply, congr_fun, eq_iff, eq_sub_iff_add_eq, eq_sub_iff_add_eq.mp, injective, map_add, map_sub, sub_eq_iff_eq_add, sub_eq_zero, sub_eq_zero.mpr
-/
lemma SnakeLemma.eq_of_eq (x : K₃)
    (y₁) (hy₁ : f₂ y₁ = ι₃ x) (z₁) (hz₁ : g₁ z₁ = i₂ y₁)
    (y₂) (hy₂ : f₂ y₂ = ι₃ x) (z₂) (hz₂ : g₁ z₂ = i₂ y₂) : π₁ z₁ = π₁ z₂ := by
  have := sub_eq_zero.mpr (hy₁.trans hy₂.symm)
  rw [← map_sub]; rw [hf] at this
  obtain ⟨d, hd⟩ := this
  rw [← eq_sub_iff_add_eq.mp hd]; rw [map_add]; rw [← hz₂]; rw [← sub_eq_iff_eq_add]; rw [← map_sub]; rw [← i₂.comp_apply]; rw [← h₁]; rw [LinearMap.comp_apply]; rw [(HasLeftInverse.injective ⟨ρ]; rw [congr_fun hρ⟩).eq_iff] at hz₁
  rw [← sub_eq_zero]; rw [← map_sub]; rw [hz₁]; rw [hπ₁]
  exact ⟨_, rfl⟩

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `SnakeLemma.δ` / `SnakeLemma.δ` 的定义

English:
definition SnakeLemma.δ
  signature: : K₃ ->ₗ[R] C₁
  body: haveI H₁ : forall x, f₂ (σ x) = x := congr_fun hσ
  haveI H₂ := δ_aux i₂ i₃ f₂ g₁ g₂ hg h₂ σ hσ ρ hρ ι₃ hι₃
  { toFun := fun x => π₁ (ρ (i₂ (σ (ι₃ x))))
    map_add' := fun x y => by
      rw [← map_add]
      exact eq_of_eq i₁ i₂ f₁ f₂ hf g₁ h₁ ρ hρ ι₃ π₁ hπ₁ (x + y) _ (H₁ _) _ (H₂ _)
        (σ (ι

中文:
定义 SnakeLemma.δ
  签名: : K₃ ->ₗ[R] C₁
  定义体: haveI H₁ : forall x, f₂ (σ x) = x := congr_fun hσ
  haveI H₂ := δ_aux i₂ i₃ f₂ g₁ g₂ hg h₂ σ hσ ρ hρ ι₃ hι₃
  { toFun := fun x => π₁ (ρ (i₂ (σ (ι₃ x))))
    map_add' := fun x y => by
      rw [← map_add]
      exact eq_of_eq i₁ i₂ f₁ f₂ hf g₁ h₁ ρ hρ ι₃ π₁ hπ₁ (x + y) _ (H₁ _) _ (H₂ _)
        (σ (ι

Depends on / 依赖: RingHom, RingHom.id_apply, congr_fun, eq_of_eq, id_apply, map_add, map_smul
-/
def SnakeLemma.δ : K₃ ->ₗ[R] C₁ :=
  haveI H₁ : forall x, f₂ (σ x) = x := congr_fun hσ
  haveI H₂ := δ_aux i₂ i₃ f₂ g₁ g₂ hg h₂ σ hσ ρ hρ ι₃ hι₃
  { toFun := fun x => π₁ (ρ (i₂ (σ (ι₃ x))))
    map_add' := fun x y => by
      rw [← map_add]
      exact eq_of_eq i₁ i₂ f₁ f₂ hf g₁ h₁ ρ hρ ι₃ π₁ hπ₁ (x + y) _ (H₁ _) _ (H₂ _)
        (σ (ι₃ x) + σ (ι₃ y)) (by simp only [map_add, H₁]) _ (by simp only [map_add, H₂])
    map_smul' := fun r x => by
      simp only [← map_smul, RingHom.id_apply]
      apply eq_of_eq i₁ i₂ f₁ f₂ hf g₁ h₁ ρ hρ ι₃ π₁ hπ₁ (r • x) _ (H₁ _) _ (H₂ _)
        (r • σ (ι₃ x)) (by simp only [map_smul, H₁]) _ (by simp only [map_smul, H₂]) }

/--
lemma `SnakeLemma.δ_eq` / 引理 `SnakeLemma.δ_eq`

English:
lemma SnakeLemma.δ_eq
  given: (x : K₃) (y) (hy : f₂ y = ι₃ x) (z) (hz : g₁ z = i₂ y)
  proof: eq_of_eq i₁ i₂ f₁ f₂ hf g₁ h₁ ρ hρ ι₃ π₁ hπ₁ x _ (congr_fun hσ _) _
    (δ_aux i₂ i₃ f₂ g₁ g₂ hg h₂ σ hσ ρ hρ ι₃ hι₃ _) y hy z hz

include hι₂ in

中文:
引理 SnakeLemma.δ_eq
  条件: (x : K₃) (y) (hy : f₂ y = ι₃ x) (z) (hz : g₁ z = i₂ y)
  证明: eq_of_eq i₁ i₂ f₁ f₂ hf g₁ h₁ ρ hρ ι₃ π₁ hπ₁ x _ (congr_fun hσ _) _
    (δ_aux i₂ i₃ f₂ g₁ g₂ hg h₂ σ hσ ρ hρ ι₃ hι₃ _) y hy z hz

include hι₂ in

Depends on / 依赖: congr_fun, eq_of_eq
-/
lemma SnakeLemma.δ_eq (x : K₃) (y) (hy : f₂ y = ι₃ x) (z) (hz : g₁ z = i₂ y) :
    δ i₁ i₂ i₃ f₁ f₂ hf g₁ g₂ hg h₁ h₂ σ hσ ρ hρ ι₃ hι₃ π₁ hπ₁ x = π₁ z :=
  eq_of_eq i₁ i₂ f₁ f₂ hf g₁ h₁ ρ hρ ι₃ π₁ hπ₁ x _ (congr_fun hσ _) _
    (δ_aux i₂ i₃ f₂ g₁ g₂ hg h₂ σ hσ ρ hρ ι₃ hι₃ _) y hy z hz

include hι₂ in
/--
lemma `SnakeLemma.exact_δ_right` / 引理 `SnakeLemma.exact_δ_right`

English:
lemma SnakeLemma.exact_δ_right
  statement: (F : K₂ ->ₗ[R] K₃) (hF : f₂.comp ι₂ = ι₃.comp F)
  proof: by
  have H₁ : forall x, f₂ (σ x) = x := congr_fun hσ
  have H₂ := δ_aux i₂ i₃ f₂ g₁ g₂ hg h₂ σ hσ ρ hρ ι₃ hι₃
  intro x
  constructor
  · intro H
    obtain ⟨y, hy⟩ := (hπ₁ _).mp H
    obtain ⟨k, hk⟩ : σ (ι₃ x) - f₁ y in Set.range ι₂ := by
      rw [← hι₂]; rw [map_sub]; rw [← H₂]; rw [← hy]; rw [s

中文:
引理 SnakeLemma.exact_δ_right
  结论: (F : K₂ ->ₗ[R] K₃) (hF : f₂.comp ι₂ = ι₃.comp F)
  证明: by
  have H₁ : forall x, f₂ (σ x) = x := congr_fun hσ
  have H₂ := δ_aux i₂ i₃ f₂ g₁ g₂ hg h₂ σ hσ ρ hρ ι₃ hι₃
  intro x
  constructor
  · intro H
    obtain ⟨y, hy⟩ := (hπ₁ _).mp H
    obtain ⟨k, hk⟩ : σ (ι₃ x) - f₁ y in Set.range ι₂ := by
      rw [← hι₂]; rw [map_sub]; rw [← H₂]; rw [← hy]; rw [s

Depends on / 依赖: Set.range, apply_apply_eq_zero, comp_apply, congr_fun, hf.apply_apply_eq_zero, map_sub, sub_eq_zero, sub_zero
-/
lemma SnakeLemma.exact_δ_right (F : K₂ ->ₗ[R] K₃) (hF : f₂.comp ι₂ = ι₃.comp F)
    (h : Injective ι₃) :
    Exact F (δ i₁ i₂ i₃ f₁ f₂ hf g₁ g₂ hg h₁ h₂ σ hσ ρ hρ ι₃ hι₃ π₁ hπ₁) := by
  have H₁ : forall x, f₂ (σ x) = x := congr_fun hσ
  have H₂ := δ_aux i₂ i₃ f₂ g₁ g₂ hg h₂ σ hσ ρ hρ ι₃ hι₃
  intro x
  constructor
  · intro H
    obtain ⟨y, hy⟩ := (hπ₁ _).mp H
    obtain ⟨k, hk⟩ : σ (ι₃ x) - f₁ y in Set.range ι₂ := by
      rw [← hι₂]; rw [map_sub]; rw [← H₂]; rw [← hy]; rw [sub_eq_zero]; exact congr($h₁ y)
    refine ⟨k, h ?_⟩
    rw [← ι₃.comp_apply]; rw [← hF]; rw [f₂.comp_apply]; rw [hk]; rw [map_sub]; rw [H₁]; rw [hf.apply_apply_eq_zero]; rw [sub_zero]
  · rintro ⟨y, rfl⟩
    exact (δ_eq i₁ i₂ i₃ f₁ f₂ hf g₁ g₂ hg h₁ h₂ σ hσ ρ hρ ι₃ hι₃ π₁ hπ₁ _ (ι₂ y) congr($hF y)
      _ (by rw [map_zero, hι₂.apply_apply_eq_zero])).trans π₁.map_zero

include hπ₂ in
/--
lemma `SnakeLemma.exact_δ_left` / 引理 `SnakeLemma.exact_δ_left`

English:
lemma SnakeLemma.exact_δ_left
  given: (G : C₁ ->ₗ[R] C₂) (hF : G.comp π₁ = π₂.comp g₁) (h : Surjective π₁)
  proof: by
  have H₂ := δ_aux i₂ i₃ f₂ g₁ g₂ hg h₂ σ hσ ρ hρ ι₃ hι₃
  intro x
  constructor
  · intro H
    obtain ⟨x, rfl⟩ := h x
    obtain ⟨y, hy⟩ := (hπ₂ (g₁ x)).mp (by simpa only [← LinearMap.comp_apply, hF] using H)
    obtain ⟨z, hz⟩ : f₂ y in range ι₃ := (hι₃ (f₂ y)).mp (by rw [← i₃.comp_apply, ← h₂

中文:
引理 SnakeLemma.exact_δ_left
  条件: (G : C₁ ->ₗ[R] C₂) (hF : G.comp π₁ = π₂.comp g₁) (h : Surjective π₁)
  证明: by
  have H₂ := δ_aux i₂ i₃ f₂ g₁ g₂ hg h₂ σ hσ ρ hρ ι₃ hι₃
  intro x
  constructor
  · intro H
    obtain ⟨x, rfl⟩ := h x
    obtain ⟨y, hy⟩ := (hπ₂ (g₁ x)).mp (by simpa only [← LinearMap.comp_apply, hF] using H)
    obtain ⟨z, hz⟩ : f₂ y in range ι₃ := (hι₃ (f₂ y)).mp (by rw [← i₃.comp_apply, ← h₂

Depends on / 依赖: AddHom, AddHom.coe_mk, G.comp_apply, LinearMap, LinearMap.comp_apply, apply_apply_eq_zero, coe_mk, comp_apply, hg.apply_apply_eq_zero, hy.symm, hz.symm
-/
lemma SnakeLemma.exact_δ_left (G : C₁ ->ₗ[R] C₂) (hF : G.comp π₁ = π₂.comp g₁) (h : Surjective π₁) :
    Exact (δ i₁ i₂ i₃ f₁ f₂ hf g₁ g₂ hg h₁ h₂ σ hσ ρ hρ ι₃ hι₃ π₁ hπ₁) G := by
  have H₂ := δ_aux i₂ i₃ f₂ g₁ g₂ hg h₂ σ hσ ρ hρ ι₃ hι₃
  intro x
  constructor
  · intro H
    obtain ⟨x, rfl⟩ := h x
    obtain ⟨y, hy⟩ := (hπ₂ (g₁ x)).mp (by simpa only [← LinearMap.comp_apply, hF] using H)
    obtain ⟨z, hz⟩ : f₂ y in range ι₃ := (hι₃ (f₂ y)).mp (by rw [← i₃.comp_apply, ← h₂,
      g₂.comp_apply, hy, hg.apply_apply_eq_zero])
    exact ⟨z, δ_eq i₁ i₂ i₃ f₁ f₂ hf g₁ g₂ hg h₁ h₂ σ hσ ρ hρ ι₃ hι₃ π₁ hπ₁ _ _ hz.symm _ hy.symm⟩
  · rintro ⟨x, rfl⟩
    simp only [δ, coe_mk, AddHom.coe_mk]
    rw [← G.comp_apply]; rw [hF]; rw [π₂.comp_apply]; rw [H₂]; rw [hπ₂.apply_apply_eq_zero]

/--
Definition of `SnakeLemma.δ'` / `SnakeLemma.δ'` 的定义

English:
definition SnakeLemma.δ'
  signature: (hf₂ : Surjective f₂) (hg₁ : Injective g₁)
  body: δ i₁ i₂ i₃ f₁ f₂ hf g₁ g₂ hg h₁ h₂ _ (funext (surjInv_eq hf₂)) _ (invFun_comp hg₁) ι₃ hι₃ π₁ hπ₁

中文:
定义 SnakeLemma.δ'
  签名: (hf₂ : Surjective f₂) (hg₁ : Injective g₁)
  定义体: δ i₁ i₂ i₃ f₁ f₂ hf g₁ g₂ hg h₁ h₂ _ (funext (surjInv_eq hf₂)) _ (invFun_comp hg₁) ι₃ hι₃ π₁ hπ₁

Depends on / 依赖: invFun_comp, surjInv_eq
-/
noncomputable def SnakeLemma.δ' (hf₂ : Surjective f₂) (hg₁ : Injective g₁) : K₃ ->ₗ[R] C₁ :=
  δ i₁ i₂ i₃ f₁ f₂ hf g₁ g₂ hg h₁ h₂ _ (funext (surjInv_eq hf₂)) _ (invFun_comp hg₁) ι₃ hι₃ π₁ hπ₁

/--
lemma `SnakeLemma.δ'_eq` / 引理 `SnakeLemma.δ'_eq`

English:
lemma SnakeLemma.δ'_eq
  statement: (hf₂ : Surjective f₂) (hg₁ : Injective g₁)
  proof: SnakeLemma.δ_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ‹_› ‹_› _ ‹_›

include hι₂ in

中文:
引理 SnakeLemma.δ'_eq
  结论: (hf₂ : Surjective f₂) (hg₁ : Injective g₁)
  证明: SnakeLemma.δ_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ‹_› ‹_› _ ‹_›

include hι₂ in
-/
lemma SnakeLemma.δ'_eq (hf₂ : Surjective f₂) (hg₁ : Injective g₁)
    (x : K₃) (y) (hy : f₂ y = ι₃ x) (z) (hz : g₁ z = i₂ y) :
    δ' i₁ i₂ i₃ f₁ f₂ hf g₁ g₂ hg h₁ h₂ ι₃ hι₃ π₁ hπ₁ hf₂ hg₁ x = π₁ z :=
  SnakeLemma.δ_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ‹_› ‹_› _ ‹_›

include hι₂ in
/--
lemma `SnakeLemma.exact_δ'_right` / 引理 `SnakeLemma.exact_δ'_right`

English:
lemma SnakeLemma.exact_δ'_right
  statement: (hf₂ : Surjective f₂) (hg₁ : Injective g₁)
  proof: SnakeLemma.exact_δ_right _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ‹_› _ _ _ _ _ ‹_› ‹_›

include hπ₂ in

中文:
引理 SnakeLemma.exact_δ'_right
  结论: (hf₂ : Surjective f₂) (hg₁ : Injective g₁)
  证明: SnakeLemma.exact_δ_right _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ‹_› _ _ _ _ _ ‹_› ‹_›

include hπ₂ in

Depends on / 依赖: SnakeLemma, SnakeLemma.exact_
-/
lemma SnakeLemma.exact_δ'_right (hf₂ : Surjective f₂) (hg₁ : Injective g₁)
    (F : K₂ ->ₗ[R] K₃) (hF : f₂.comp ι₂ = ι₃.comp F) (h : Injective ι₃) :
    Exact F (δ' i₁ i₂ i₃ f₁ f₂ hf g₁ g₂ hg h₁ h₂ ι₃ hι₃ π₁ hπ₁ hf₂ hg₁) :=
  SnakeLemma.exact_δ_right _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ‹_› _ _ _ _ _ ‹_› ‹_›

include hπ₂ in
/--
lemma `SnakeLemma.exact_δ'_left` / 引理 `SnakeLemma.exact_δ'_left`

English:
lemma SnakeLemma.exact_δ'_left
  statement: (hf₂ : Surjective f₂) (hg₁ : Injective g₁)
  proof: SnakeLemma.exact_δ_left _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ‹_› _ ‹_› ‹_›

中文:
引理 SnakeLemma.exact_δ'_left
  结论: (hf₂ : Surjective f₂) (hg₁ : Injective g₁)
  证明: SnakeLemma.exact_δ_left _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ‹_› _ ‹_› ‹_›
-/
lemma SnakeLemma.exact_δ'_left (hf₂ : Surjective f₂) (hg₁ : Injective g₁)
    (G : C₁ ->ₗ[R] C₂) (hF : G.comp π₁ = π₂.comp g₁) (h : Surjective π₁) :
    Exact (δ' i₁ i₂ i₃ f₁ f₂ hf g₁ g₂ hg h₁ h₂ ι₃ hι₃ π₁ hπ₁ hf₂ hg₁) G :=
  SnakeLemma.exact_δ_left _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ‹_› _ ‹_› ‹_›
