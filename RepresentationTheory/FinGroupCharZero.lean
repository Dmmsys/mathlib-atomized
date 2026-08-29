/-
Copyright (c) 2025 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel
-/
module

public import Mathlib.Algebra.Category.FGModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Injective
public import Mathlib.RepresentationTheory.Character
public import Mathlib.RepresentationTheory.Maschke
public import Mathlib.RingTheory.SimpleModule.InjectiveProjective
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.RepresentationTheory.Rep.Iso

/-!
# Applications of Maschke's theorem

This proves some properties of representations that follow from Maschke's
theorem.

We prove that, if `G` is a finite group whose order is invertible in a field `k`,
then every object of `Rep k G` (resp. `FDRep k G`) is injective and projective.

We also give two simpleness criteria for an object `V` of `FDRep k G`, when `k` is
an algebraically closed field in which the order of `G` is invertible:
* `FDRep.simple_iff_end_is_rank_one`: `V` is simple if and only `V ⟶ V` is a `k`-vector
  space of dimension `1`.
* `FDRep.simple_iff_char_is_norm_one`: when `k` is characteristic zero, `V` is simple
  if and only if `∑ g : G, V.character g * V.character g⁻¹ = Fintype.card G`.

-/

public section

universe u v w

variable {k : Type u} [Field k] {G : Type u} [Finite G] [Group G]

open CategoryTheory Limits

namespace Rep

variable [NeZero (Nat.card G : k)]

/--
If `G` is finite and its order is nonzero in the field `k`, then every object of
`Rep k G` is injective.
-/
instance (V : Rep.{w} k G) : Injective V := by
  rw [← Rep.equivalenceModuleMonoidAlgebra.map_injective_iff]; rw [← Module.injective_iff_injective_object]
  exact Module.injective_of_isSemisimpleRing _ _

/--
If `G` is finite and its order is nonzero in the field `k`, then every object of
`Rep k G` is projective.
-/
-- Will this clash with the previously defined `Projective` instances?
instance (V : Rep.{u} k G) : Projective V := by
  rw [← Rep.equivalenceModuleMonoidAlgebra.map_projective_iff]; rw [← IsProjective.iff_projective]
  exact Module.projective_of_isSemisimpleRing _ _

end Rep

namespace FDRep

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NeZero
  signature: (Nat.card G : k)] (V
  body: (forget₂ (FDRep k G) (Rep k G)).injective_of_map_injective inferInstance

中文:
实例 [NeZero
  签名: (自然数.card G : k)] (V
  定义体: (forget₂ (FDRep k G) (Rep k G)).injective_of_map_injective inferInstance

Depends on / 依赖: injective_of_map_injective
-/
instance [NeZero (Nat.card G : k)] (V : FDRep k G) : Injective V :=
  (forget₂ (FDRep k G) (Rep k G)).injective_of_map_injective inferInstance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NeZero
  signature: (Nat.card G : k)] (V
  body: (forget₂ (FDRep k G) (Rep k G)).projective_of_map_projective inferInstance

中文:
实例 [NeZero
  签名: (自然数.card G : k)] (V
  定义体: (forget₂ (FDRep k G) (Rep k G)).projective_of_map_projective inferInstance

Depends on / 依赖: projective_of_map_projective
-/
instance [NeZero (Nat.card G : k)] (V : FDRep k G) : Projective V :=
  (forget₂ (FDRep k G) (Rep k G)).projective_of_map_projective inferInstance

variable [IsAlgClosed k]

/--
lemma `simple_iff_end_is_rank_one` / 引理 `simple_iff_end_is_rank_one`

English:
lemma simple_iff_end_is_rank_one
  given: [NeZero (Nat.card G : k)] (V : FDRep k G)
  proof: finrank_endomorphism_simple_eq_one k V
  mpr h := by
    refine { mono_isIso_iff_nonzero {W} f _ := ⟨fun hf habs => ?_, fun hf => ?_⟩ }
    · rw [habs, isIsoZero_iff_source_target_isZero] at hf
      obtain ⟨g, hg⟩ : exists g : V ⟶ V, g != 0 :=
        (Module.finrank_pos_iff_exists_ne_zero (R := k)).mp (by grind)
      exact hg (hf.2.eq_zero_of_src g)
    · suffices Epi f by exact isIso_of_mono_of_epi f
      suffices Epi (Abelian.image.ι f) by
        rw [← Abelian.image.fac f]
        exact epi_comp _ _
      rw [← Abelian.image.fac f] at hf
      set ι := Abelian.image.ι f
      set φ := Injective.factorThru (𝟙 _) ι
      have hφι : φ ≫ ι != 0 := by
        intro habs
        have hιφ : 𝟙 _ = ι ≫ φ := (Injective.comp_factorThru (𝟙 _) ι).symm
        apply_fun (· ≫ ι) at hιφ
        simp_all
      obtain ⟨c, hc⟩ : exists c : k, c • _ = 𝟙 V := (finrank_eq_one_iff_of_nonzero' _ hφι).mp h (𝟙 V)
      refine Preadditive.epi_of_cancel_zero _ (fun g hg => ?_)
      apply_fun (· ≫ g) at hc
      simpa [hg] using hc.symm

omit [Finite G] in

中文:
引理 simple_iff_end_is_rank_one
  条件: [NeZero (自然数.card G : k)] (V : FDRep k G)
  证明: finrank_endomorphism_simple_eq_one k V
  mpr h := by
    refine { mono_isIso_iff_nonzero {W} f _ := ⟨fun hf habs => ?_, fun hf => ?_⟩ }
    · rw [habs, isIsoZero_iff_source_target_isZero] at hf
      obtain ⟨g, hg⟩ : exists g : V ⟶ V, g != 0 :=
        (Module.finrank_pos_iff_exists_ne_zero (R := k)).mp (by grind)
      exact hg (hf.2.eq_zero_of_src g)
    · suffices Epi f by exact isIso_of_mono_of_epi f
      suffices Epi (Abelian.image.ι f) by
        rw [← Abelian.image.fac f]
        exact epi_comp _ _
      rw [← Abelian.image.fac f] at hf
      set ι := Abelian.image.ι f
      set φ := Injective.factorThru (𝟙 _) ι
      have hφι : φ ≫ ι != 0 := by
        intro habs
        have hιφ : 𝟙 _ = ι ≫ φ := (Injective.comp_factorThru (𝟙 _) ι).symm
        apply_fun (· ≫ ι) at hιφ
        simp_all
      obtain ⟨c, hc⟩ : exists c : k, c • _ = 𝟙 V := (finrank_eq_one_iff_of_nonzero' _ hφι).mp h (𝟙 V)
      refine Preadditive.epi_of_cancel_zero _ (fun g hg => ?_)
      apply_fun (· ≫ g) at hc
      simpa [hg] using hc.symm

omit [Finite G] in

Depends on / 依赖: finrank_endomorphism_simple_eq_one
-/
lemma simple_iff_end_is_rank_one [NeZero (Nat.card G : k)] (V : FDRep k G) :
    Simple V ↔ Module.finrank k (V ⟶ V) = 1 where
  mp h := finrank_endomorphism_simple_eq_one k V
  mpr h := by
    refine { mono_isIso_iff_nonzero {W} f _ := ⟨fun hf habs => ?_, fun hf => ?_⟩ }
    · rw [habs, isIsoZero_iff_source_target_isZero] at hf
      obtain ⟨g, hg⟩ : exists g : V ⟶ V, g != 0 :=
        (Module.finrank_pos_iff_exists_ne_zero (R := k)).mp (by grind)
      exact hg (hf.2.eq_zero_of_src g)
    · suffices Epi f by exact isIso_of_mono_of_epi f
      suffices Epi (Abelian.image.ι f) by
        rw [← Abelian.image.fac f]
        exact epi_comp _ _
      rw [← Abelian.image.fac f] at hf
      set ι := Abelian.image.ι f
      set φ := Injective.factorThru (𝟙 _) ι
      have hφι : φ ≫ ι != 0 := by
        intro habs
        have hιφ : 𝟙 _ = ι ≫ φ := (Injective.comp_factorThru (𝟙 _) ι).symm
        apply_fun (· ≫ ι) at hιφ
        simp_all
      obtain ⟨c, hc⟩ : exists c : k, c • _ = 𝟙 V := (finrank_eq_one_iff_of_nonzero' _ hφι).mp h (𝟙 V)
      refine Preadditive.epi_of_cancel_zero _ (fun g hg => ?_)
      apply_fun (· ≫ g) at hc
      simpa [hg] using hc.symm

omit [Finite G] in
/--
lemma `simple_iff_char_is_norm_one` / 引理 `simple_iff_char_is_norm_one`

English:
lemma simple_iff_char_is_norm_one
  given: [CharZero k] [Fintype G] (V : FDRep k G)
  proof: by
  have := invertibleOfNonzero (NeZero.ne (Nat.card G : k))
  constructor <;> intro h
  · symm; simpa [Nonempty.intro (Iso.refl V), inv_mul_eq_one₀] using char_orthonormal V V
  · have eq := V.scalar_product_char_eq_finrank_equivariant V
    rw [h]; rw [inv_mul_cancel_of_invertible] at eq
    rw [simple_iff_end_is_rank_one]; rw [← Nat.cast_inj (R := k)]; rw [← eq]; rw [Nat.cast_one]

中文:
引理 simple_iff_char_is_norm_one
  条件: [特征零 k] [有限类型 G] (V : FDRep k G)
  证明: by
  have := invertibleOfNonzero (NeZero.ne (Nat.card G : k))
  constructor <;> intro h
  · symm; simpa [Nonempty.intro (Iso.refl V), inv_mul_eq_one₀] using char_orthonormal V V
  · have eq := V.scalar_product_char_eq_finrank_equivariant V
    rw [h]; rw [inv_mul_cancel_of_invertible] at eq
    rw [simple_iff_end_is_rank_one]; rw [← Nat.cast_inj (R := k)]; rw [← eq]; rw [Nat.cast_one]

Depends on / 依赖: Iso.refl, Nat.card, Nat.cast_inj, Nat.cast_one, NeZero, NeZero.ne, Nonempty, Nonempty.intro, V.scalar_product_char_eq_finrank_equivariant, cast_inj, cast_one, char_orthonormal, inv_mul_cancel_of_invertible, invertibleOfNonzero, scalar_product_char_eq_finrank_equivariant, simple_iff_end_is_rank_one
-/
lemma simple_iff_char_is_norm_one [CharZero k] [Fintype G] (V : FDRep k G) :
    Simple V ↔ ∑ g : G, V.character g * V.character g⁻¹ = Nat.card G := by
  have := invertibleOfNonzero (NeZero.ne (Nat.card G : k))
  constructor <;> intro h
  · symm; simpa [Nonempty.intro (Iso.refl V), inv_mul_eq_one₀] using char_orthonormal V V
  · have eq := V.scalar_product_char_eq_finrank_equivariant V
    rw [h]; rw [inv_mul_cancel_of_invertible] at eq
    rw [simple_iff_end_is_rank_one]; rw [← Nat.cast_inj (R := k)]; rw [← eq]; rw [Nat.cast_one]

end FDRep
