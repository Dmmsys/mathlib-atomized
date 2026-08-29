/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Johan Commelin
-/
module

public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Finiteness.Bilinear
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Finiteness of the tensor product of (sub)modules

In this file we show that the supremum of two subalgebras that are finitely generated as modules,
is again finitely generated.

-/

public section

open Function (Surjective)
open Finsupp

namespace Submodule

variable {R M N : Type*} [CommSemiring R] [AddCommMonoid M]
  [AddCommMonoid N] [Module R M] [Module R N] {I : Submodule R N}

open TensorProduct LinearMap
/--
theorem `exists_fg_le_eq_rTensor_subtype` / 定理 `exists_fg_le_eq_rTensor_subtype`

English:
theorem exists_fg_le_eq_rTensor_subtype
  given: (x : N otimes M)
  proof: by
  induction x with
  | zero => exact ⟨⊥, fg_bot, 0, rfl⟩
  | tmul i m => exact ⟨R ∙ i, fg_span_singleton i, ⟨i, mem_span_singleton_self _⟩ otimesₜ[R] m, rfl⟩
  | add x₁ x₂ ihx₁ ihx₂ =>
    obtain ⟨J₁, fg₁, y₁, rfl⟩ := ihx₁
    obtain ⟨J₂, fg₂, y₂, rfl⟩ := ihx₂
    refine ⟨J₁ ⊔ J₂, fg₁.sup fg₂,
      rTensor M (J₁.inclusion le_sup_left) y₁ + rTensor M (J₂.inclusion le_sup_right) y₂, ?_⟩
    rw [map_add]; rw [← rTensor_comp_apply]; rw [← rTensor_comp_apply]
    rfl

中文:
定理 存在_fg_le_eq_rTensor_subtype
  条件: (x : N otimes M)
  证明: by
  induction x with
  | zero => exact ⟨⊥, fg_bot, 0, rfl⟩
  | tmul i m => exact ⟨R ∙ i, fg_span_singleton i, ⟨i, mem_span_singleton_self _⟩ otimesₜ[R] m, rfl⟩
  | add x₁ x₂ ihx₁ ihx₂ =>
    obtain ⟨J₁, fg₁, y₁, rfl⟩ := ihx₁
    obtain ⟨J₂, fg₂, y₂, rfl⟩ := ihx₂
    refine ⟨J₁ ⊔ J₂, fg₁.sup fg₂,
      rTensor M (J₁.inclusion le_sup_left) y₁ + rTensor M (J₂.inclusion le_sup_right) y₂, ?_⟩
    rw [map_add]; rw [← rTensor_comp_apply]; rw [← rTensor_comp_apply]
    rfl

Depends on / 依赖: fg_bot, fg_span_singleton, inclusion, le_sup_left, le_sup_right, map_add, mem_span_singleton_self, rTensor, rTensor_comp_apply
-/
theorem exists_fg_le_eq_rTensor_subtype (x : N otimes M) :
    exists (J : Submodule R N) (_ : J.FG) (y : J otimes M), x = rTensor M J.subtype y := by
  induction x with
  | zero => exact ⟨⊥, fg_bot, 0, rfl⟩
  | tmul i m => exact ⟨R ∙ i, fg_span_singleton i, ⟨i, mem_span_singleton_self _⟩ otimesₜ[R] m, rfl⟩
  | add x₁ x₂ ihx₁ ihx₂ =>
    obtain ⟨J₁, fg₁, y₁, rfl⟩ := ihx₁
    obtain ⟨J₂, fg₂, y₂, rfl⟩ := ihx₂
    refine ⟨J₁ ⊔ J₂, fg₁.sup fg₂,
      rTensor M (J₁.inclusion le_sup_left) y₁ + rTensor M (J₂.inclusion le_sup_right) y₂, ?_⟩
    rw [map_add]; rw [← rTensor_comp_apply]; rw [← rTensor_comp_apply]
    rfl

/--
theorem `exists_fg_le_subset_range_rTensor_subtype` / 定理 `exists_fg_le_subset_range_rTensor_subtype`

English:
theorem exists_fg_le_subset_range_rTensor_subtype
  given: (s : Set (N otimes[R] M)) (hs : s.Finite)
  proof: by
  choose J fg y eq using exists_fg_le_eq_rTensor_subtype (R := R) (M := M) (N := N)
  rw [← Set.finite_coe_iff] at hs
  refine ⟨⨆ x : s, J x, fg_iSup _ fun _ => fg _, fun x hx =>
    ⟨rTensor M (inclusion <| le_iSup _ ⟨x, hx⟩) (y x), .trans ?_ (eq x).symm⟩⟩
  rw [← comp_apply]; rw [← rTensor_comp]; rfl

中文:
定理 存在_fg_le_subset_range_rTensor_subtype
  条件: (s : 集合 (N otimes[R] M)) (hs : s.有限)
  证明: by
  choose J fg y eq using exists_fg_le_eq_rTensor_subtype (R := R) (M := M) (N := N)
  rw [← Set.finite_coe_iff] at hs
  refine ⟨⨆ x : s, J x, fg_iSup _ fun _ => fg _, fun x hx =>
    ⟨rTensor M (inclusion <| le_iSup _ ⟨x, hx⟩) (y x), .trans ?_ (eq x).symm⟩⟩
  rw [← comp_apply]; rw [← rTensor_comp]; rfl

Depends on / 依赖: Set.finite_coe_iff, comp_apply, exists_fg_le_eq_rTensor_subtype, fg_iSup, finite_coe_iff, inclusion, le_iSup, rTensor, rTensor_comp
-/
theorem exists_fg_le_subset_range_rTensor_subtype (s : Set (N otimes[R] M)) (hs : s.Finite) :
    exists (J : Submodule R N) (_ : J.FG), s subseteq LinearMap.range (rTensor M J.subtype) := by
  choose J fg y eq using exists_fg_le_eq_rTensor_subtype (R := R) (M := M) (N := N)
  rw [← Set.finite_coe_iff] at hs
  refine ⟨⨆ x : s, J x, fg_iSup _ fun _ => fg _, fun x hx =>
    ⟨rTensor M (inclusion <| le_iSup _ ⟨x, hx⟩) (y x), .trans ?_ (eq x).symm⟩⟩
  rw [← comp_apply]; rw [← rTensor_comp]; rfl

open TensorProduct LinearMap
/--
theorem `exists_fg_le_eq_rTensor_inclusion` / 定理 `exists_fg_le_eq_rTensor_inclusion`

English:
theorem exists_fg_le_eq_rTensor_inclusion
  given: (x : I otimes M)
  proof: by
  obtain ⟨J, fg, y, rfl⟩ := exists_fg_le_eq_rTensor_subtype x
  refine ⟨J.map I.subtype, fg.map _, I.map_subtype_le J, rTensor M (I.subtype.submoduleMap J) y, ?_⟩
  rw [← LinearMap.rTensor_comp_apply]; rfl

中文:
定理 存在_fg_le_eq_rTensor_inclusion
  条件: (x : I otimes M)
  证明: by
  obtain ⟨J, fg, y, rfl⟩ := exists_fg_le_eq_rTensor_subtype x
  refine ⟨J.map I.subtype, fg.map _, I.map_subtype_le J, rTensor M (I.subtype.submoduleMap J) y, ?_⟩
  rw [← LinearMap.rTensor_comp_apply]; rfl

Depends on / 依赖: I.map_subtype_le, I.subtype, I.subtype.submoduleMap, J.map, LinearMap, LinearMap.rTensor_comp_apply, exists_fg_le_eq_rTensor_subtype, fg.map, map_subtype_le, rTensor, rTensor_comp_apply, submoduleMap, subtype
-/
theorem exists_fg_le_eq_rTensor_inclusion (x : I otimes M) :
    exists (J : Submodule R N) (_ : J.FG) (hle : J <= I) (y : J otimes M),
      x = rTensor M (J.inclusion hle) y := by
  obtain ⟨J, fg, y, rfl⟩ := exists_fg_le_eq_rTensor_subtype x
  refine ⟨J.map I.subtype, fg.map _, I.map_subtype_le J, rTensor M (I.subtype.submoduleMap J) y, ?_⟩
  rw [← LinearMap.rTensor_comp_apply]; rfl

/--
theorem `exists_fg_le_subset_range_rTensor_inclusion` / 定理 `exists_fg_le_subset_range_rTensor_inclusion`

English:
theorem exists_fg_le_subset_range_rTensor_inclusion
  given: (s : Set (I otimes[R] M)) (hs : s.Finite)
  proof: by
  choose J fg hle y eq using exists_fg_le_eq_rTensor_inclusion (M := M) (I := I)
  rw [← Set.finite_coe_iff] at hs
  refine ⟨⨆ x : s, J x, fg_iSup _ fun _ => fg _, iSup_le fun _ => hle _, fun x hx =>
    ⟨rTensor M (inclusion <| le_iSup _ ⟨x, hx⟩) (y x), .trans ?_ (eq x).symm⟩⟩
  rw [← comp_apply]; rw [← rTensor_comp]; rfl

中文:
定理 存在_fg_le_subset_range_rTensor_inclusion
  条件: (s : 集合 (I otimes[R] M)) (hs : s.有限)
  证明: by
  choose J fg hle y eq using exists_fg_le_eq_rTensor_inclusion (M := M) (I := I)
  rw [← Set.finite_coe_iff] at hs
  refine ⟨⨆ x : s, J x, fg_iSup _ fun _ => fg _, iSup_le fun _ => hle _, fun x hx =>
    ⟨rTensor M (inclusion <| le_iSup _ ⟨x, hx⟩) (y x), .trans ?_ (eq x).symm⟩⟩
  rw [← comp_apply]; rw [← rTensor_comp]; rfl

Depends on / 依赖: Set.finite_coe_iff, comp_apply, exists_fg_le_eq_rTensor_inclusion, fg_iSup, finite_coe_iff, iSup_le, inclusion, le_iSup, rTensor, rTensor_comp
-/
theorem exists_fg_le_subset_range_rTensor_inclusion (s : Set (I otimes[R] M)) (hs : s.Finite) :
    exists (J : Submodule R N) (_ : J.FG) (hle : J <= I),
      s subseteq LinearMap.range (rTensor M (J.inclusion hle)) := by
  choose J fg hle y eq using exists_fg_le_eq_rTensor_inclusion (M := M) (I := I)
  rw [← Set.finite_coe_iff] at hs
  refine ⟨⨆ x : s, J x, fg_iSup _ fun _ => fg _, iSup_le fun _ => hle _, fun x hx =>
    ⟨rTensor M (inclusion <| le_iSup _ ⟨x, hx⟩) (y x), .trans ?_ (eq x).symm⟩⟩
  rw [← comp_apply]; rw [← rTensor_comp]; rfl

end Submodule

section ModuleAndAlgebra

variable (R A B M N : Type*)

/--
Instance `Module.Finite.base_change` / 实例 `Module.Finite.base_change`

English:
instance Module.Finite.base_change
  signature: [CommSemiring R] [Semiring A] [Algebra R A] [AddCommMonoid M]
  body: by
  classical
    obtain ⟨s, hs⟩ := h.fg_top
    refine ⟨⟨s.image (TensorProduct.mk R A M 1), eq_top_iff.mpr ?_⟩⟩
    rintro x -
    induction x with
    | zero => exact zero_mem _
    | tmul x y =>
      rw [Finset.coe_image]; rw [← Submodule.span_span_of_tower R]; rw [Submodule.span_image]; rw [hs]; rw [Submodule.map_top]; rw [LinearMap.coe_range]; rw [← mul_one x]; rw [← smul_eq_mul]; rw [← TensorProduct.smul_tmul']
      exact Submodule.smul_mem _ x (Submodule.subset_span <| Set.mem_range_self y)
    | add x y hx hy => exact Submodule.add_mem _ hx hy

中文:
实例 模.有限.base_change
  签名: [交换半环 R] [半环 A] [代数 R A] [加法交换幺半群 M]
  定义体: by
  classical
    obtain ⟨s, hs⟩ := h.fg_top
    refine ⟨⟨s.image (TensorProduct.mk R A M 1), eq_top_iff.mpr ?_⟩⟩
    rintro x -
    induction x with
    | zero => exact zero_mem _
    | tmul x y =>
      rw [Finset.coe_image]; rw [← Submodule.span_span_of_tower R]; rw [Submodule.span_image]; rw [hs]; rw [Submodule.map_top]; rw [LinearMap.coe_range]; rw [← mul_one x]; rw [← smul_eq_mul]; rw [← TensorProduct.smul_tmul']
      exact Submodule.smul_mem _ x (Submodule.subset_span <| Set.mem_range_self y)
    | add x y hx hy => exact Submodule.add_mem _ hx hy

Depends on / 依赖: Finset, Finset.coe_image, LinearMap, LinearMap.coe_range, Set.mem_range_self, Submod, Submodule, Submodule.map_top, Submodule.smul_mem, Submodule.span_image, Submodule.span_span_of_tower, Submodule.subset_span, TensorProduct, TensorProduct.mk, TensorProduct.smul_tmul, classical, coe_image, coe_range, eq_top_iff, eq_top_iff.mpr
-/
instance Module.Finite.base_change [CommSemiring R] [Semiring A] [Algebra R A] [AddCommMonoid M]
    [Module R M] [h : Module.Finite R M] : Module.Finite A (TensorProduct R A M) := by
  classical
    obtain ⟨s, hs⟩ := h.fg_top
    refine ⟨⟨s.image (TensorProduct.mk R A M 1), eq_top_iff.mpr ?_⟩⟩
    rintro x -
    induction x with
    | zero => exact zero_mem _
    | tmul x y =>
      rw [Finset.coe_image]; rw [← Submodule.span_span_of_tower R]; rw [Submodule.span_image]; rw [hs]; rw [Submodule.map_top]; rw [LinearMap.coe_range]; rw [← mul_one x]; rw [← smul_eq_mul]; rw [← TensorProduct.smul_tmul']
      exact Submodule.smul_mem _ x (Submodule.subset_span <| Set.mem_range_self y)
    | add x y hx hy => exact Submodule.add_mem _ hx hy

/--
Instance `Module.Finite.tensorProduct` / 实例 `Module.Finite.tensorProduct`

English:
instance Module.Finite.tensorProduct
  signature: [CommSemiring R] [AddCommMonoid M] [Module R M]
  body: (TensorProduct.map₂_mk_top_top_eq_top R M N).subst (hM.fg_top.map₂ _ hN.fg_top)

中文:
实例 模.有限.tensorProduct
  签名: [交换半环 R] [加法交换幺半群 M] [模 R M]
  定义体: (TensorProduct.map₂_mk_top_top_eq_top R M N).subst (hM.fg_top.map₂ _ hN.fg_top)

Depends on / 依赖: TensorProduct, TensorProduct.map, fg_top, hM.fg_top.map, hN.fg_top
-/
instance Module.Finite.tensorProduct [CommSemiring R] [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N] [hM : Module.Finite R M] [hN : Module.Finite R N] :
    Module.Finite R (TensorProduct R M N) where
  fg_top := (TensorProduct.map₂_mk_top_top_eq_top R M N).subst (hM.fg_top.map₂ _ hN.fg_top)

end ModuleAndAlgebra

section NontrivialTensorProduct

variable (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]

/--
lemma `Module.exists_isPrincipal_quotient_of_finite` / 引理 `Module.exists_isPrincipal_quotient_of_finite`

English:
lemma Module.exists_isPrincipal_quotient_of_finite
  proof: by
  obtain ⟨n, f, hf⟩ := @Module.Finite.exists_fin R M _ _ _ _
  let s := { m : Nat | Submodule.span R (f '' Fin.val ⁻¹' Set.Iio m) != ⊤ }
  have hns : forall x in s, x < n := by
    refine fun x hx => lt_iff_not_ge.mpr fun e => ?_
    have : (Fin.val ⁻¹' Set.Iio x : Set (Fin n)) = Set.univ := by ext y; simpa using y.2.trans_le e
    simp [s, this, hf] at hx
  have hs₁ : s.Nonempty := ⟨0, by simp [s]⟩
  have hs₂ : BddAbove s := ⟨n, fun x hx => (hns x hx).le⟩
  have hs := Nat.sSup_mem hs₁ hs₂
  refine ⟨_, hs, ⟨⟨Submodule.mkQ _ (f ⟨_, hns _ hs⟩), ?_⟩⟩⟩
  have := not_not.mp (notMem_of_csSup_lt (Order.lt_succ _) hs₂)
  rw [← Set.image_singleton]; rw [← Submodule.map_span]; rw [← (Submodule.comap_injective_of_surjective (Submodule.mkQ_surjective _)).eq_iff]; rw [Submodule.comap_map_eq]; rw [Submodule.ker_mkQ]; rw [Submodule.comap_top]; rw [← this]; rw [← Submodule.span_union]; rw [Order.Iio_succ_eq_insert (sSup s)]; rw [← Set.union_singleton]; rw [Set.preimage_union]; rw [Set.image_union]; rw [← @Set.image_singleton _ _ f]; rw [Set.union_comm]
  congr!
  ext
  simp [Fin.ext_iff]

中文:
引理 模.存在_isPrincipal_quotient_of_finite
  证明: by
  obtain ⟨n, f, hf⟩ := @Module.Finite.exists_fin R M _ _ _ _
  let s := { m : Nat | Submodule.span R (f '' Fin.val ⁻¹' Set.Iio m) != ⊤ }
  have hns : forall x in s, x < n := by
    refine fun x hx => lt_iff_not_ge.mpr fun e => ?_
    have : (Fin.val ⁻¹' Set.Iio x : Set (Fin n)) = Set.univ := by ext y; simpa using y.2.trans_le e
    simp [s, this, hf] at hx
  have hs₁ : s.Nonempty := ⟨0, by simp [s]⟩
  have hs₂ : BddAbove s := ⟨n, fun x hx => (hns x hx).le⟩
  have hs := Nat.sSup_mem hs₁ hs₂
  refine ⟨_, hs, ⟨⟨Submodule.mkQ _ (f ⟨_, hns _ hs⟩), ?_⟩⟩⟩
  have := not_not.mp (notMem_of_csSup_lt (Order.lt_succ _) hs₂)
  rw [← Set.image_singleton]; rw [← Submodule.map_span]; rw [← (Submodule.comap_injective_of_surjective (Submodule.mkQ_surjective _)).eq_iff]; rw [Submodule.comap_map_eq]; rw [Submodule.ker_mkQ]; rw [Submodule.comap_top]; rw [← this]; rw [← Submodule.span_union]; rw [Order.Iio_succ_eq_insert (sSup s)]; rw [← Set.union_singleton]; rw [Set.preimage_union]; rw [Set.image_union]; rw [← @Set.image_singleton _ _ f]; rw [Set.union_comm]
  congr!
  ext
  simp [Fin.ext_iff]

Depends on / 依赖: BddAbove, Fin.val, Finite, Module, Module.Finite.exists_fin, Nat.sSup_mem, Nonempty, Set.Iio, Set.univ, Submodule, Submodule.span, exists_fin, lt_iff_not_ge, lt_iff_not_ge.mpr, s.Nonempty, sSup_mem, trans_le
-/
lemma Module.exists_isPrincipal_quotient_of_finite :
    exists N : Submodule R M, N != ⊤ ∧ Submodule.IsPrincipal (⊤ : Submodule R (M ⧸ N)) := by
  obtain ⟨n, f, hf⟩ := @Module.Finite.exists_fin R M _ _ _ _
  let s := { m : Nat | Submodule.span R (f '' Fin.val ⁻¹' Set.Iio m) != ⊤ }
  have hns : forall x in s, x < n := by
    refine fun x hx => lt_iff_not_ge.mpr fun e => ?_
    have : (Fin.val ⁻¹' Set.Iio x : Set (Fin n)) = Set.univ := by ext y; simpa using y.2.trans_le e
    simp [s, this, hf] at hx
  have hs₁ : s.Nonempty := ⟨0, by simp [s]⟩
  have hs₂ : BddAbove s := ⟨n, fun x hx => (hns x hx).le⟩
  have hs := Nat.sSup_mem hs₁ hs₂
  refine ⟨_, hs, ⟨⟨Submodule.mkQ _ (f ⟨_, hns _ hs⟩), ?_⟩⟩⟩
  have := not_not.mp (notMem_of_csSup_lt (Order.lt_succ _) hs₂)
  rw [← Set.image_singleton]; rw [← Submodule.map_span]; rw [← (Submodule.comap_injective_of_surjective (Submodule.mkQ_surjective _)).eq_iff]; rw [Submodule.comap_map_eq]; rw [Submodule.ker_mkQ]; rw [Submodule.comap_top]; rw [← this]; rw [← Submodule.span_union]; rw [Order.Iio_succ_eq_insert (sSup s)]; rw [← Set.union_singleton]; rw [Set.preimage_union]; rw [Set.image_union]; rw [← @Set.image_singleton _ _ f]; rw [Set.union_comm]
  congr!
  ext
  simp [Fin.ext_iff]

/--
lemma `Module.exists_surjective_quotient_of_finite` / 引理 `Module.exists_surjective_quotient_of_finite`

English:
lemma Module.exists_surjective_quotient_of_finite
  proof: by
  obtain ⟨N, hN, ⟨x, hx⟩⟩ := Module.exists_isPrincipal_quotient_of_finite R M
  let f := (LinearMap.toSpanSingleton R _ x).quotKerEquivOfSurjective
    (by rw [← LinearMap.range_eq_top, ← LinearMap.span_singleton_eq_range, hx])
  refine ⟨_, f.symm.toLinearMap.comp N.mkQ, fun e => ?_, f.symm.surjective.comp N.mkQ_surjective⟩
  obtain rfl : x = 0 := by simpa using LinearMap.congr_fun (LinearMap.ker_eq_top.mp e) 1
  have : Nontrivial (M ⧸ N) := by rwa [Submodule.Quotient.nontrivial_iff]
  simp at hx

中文:
引理 模.存在_surjective_quotient_of_finite
  证明: by
  obtain ⟨N, hN, ⟨x, hx⟩⟩ := Module.exists_isPrincipal_quotient_of_finite R M
  let f := (LinearMap.toSpanSingleton R _ x).quotKerEquivOfSurjective
    (by rw [← LinearMap.range_eq_top, ← LinearMap.span_singleton_eq_range, hx])
  refine ⟨_, f.symm.toLinearMap.comp N.mkQ, fun e => ?_, f.symm.surjective.comp N.mkQ_surjective⟩
  obtain rfl : x = 0 := by simpa using LinearMap.congr_fun (LinearMap.ker_eq_top.mp e) 1
  have : Nontrivial (M ⧸ N) := by rwa [Submodule.Quotient.nontrivial_iff]
  simp at hx

Depends on / 依赖: LinearMap, LinearMap.congr_fun, LinearMap.ker_eq_top.mp, LinearMap.range_eq_top, LinearMap.span_singleton_eq_range, LinearMap.toSpanSingleton, Module, Module.exists_isPrincipal_quotient_of_finite, N.mkQ, N.mkQ_surjective, Nontrivial, Quotient, Submodule, Submodule.Quotient.nontrivial_iff, congr_fun, exists_isPrincipal_quotient_of_finite, f.symm.surjective.comp, f.symm.toLinearMap.comp, ker_eq_top, mkQ_surjective
-/
lemma Module.exists_surjective_quotient_of_finite :
    exists (I : Ideal R) (f : M ->ₗ[R] R ⧸ I), I != ⊤ ∧ Function.Surjective f := by
  obtain ⟨N, hN, ⟨x, hx⟩⟩ := Module.exists_isPrincipal_quotient_of_finite R M
  let f := (LinearMap.toSpanSingleton R _ x).quotKerEquivOfSurjective
    (by rw [← LinearMap.range_eq_top, ← LinearMap.span_singleton_eq_range, hx])
  refine ⟨_, f.symm.toLinearMap.comp N.mkQ, fun e => ?_, f.symm.surjective.comp N.mkQ_surjective⟩
  obtain rfl : x = 0 := by simpa using LinearMap.congr_fun (LinearMap.ker_eq_top.mp e) 1
  have : Nontrivial (M ⧸ N) := by rwa [Submodule.Quotient.nontrivial_iff]
  simp at hx

open TensorProduct

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Nontrivial (M otimes[R] M)
  body: by
  obtain ⟨I, ϕ, hI, hϕ⟩ := Module.exists_surjective_quotient_of_finite R M
  let ψ : M otimes[R] M ->ₗ[R] R ⧸ I :=
    (LinearMap.mul' R (R ⧸ I)).comp (TensorProduct.map ϕ ϕ)
  have : Nontrivial (R ⧸ I) := by rwa [Submodule.Quotient.nontrivial_iff]
  have : Function.Surjective ψ := by
    intro x; obtain ⟨x, rfl⟩ := hϕ x; obtain ⟨y, hy⟩ := hϕ 1; exact ⟨x otimesₜ y, by simp [ψ, hy]⟩
  exact this.nontrivial

中文:
实例 :
  签名: 非平凡 (M otimes[R] M)
  定义体: by
  obtain ⟨I, ϕ, hI, hϕ⟩ := Module.exists_surjective_quotient_of_finite R M
  let ψ : M otimes[R] M ->ₗ[R] R ⧸ I :=
    (LinearMap.mul' R (R ⧸ I)).comp (TensorProduct.map ϕ ϕ)
  have : Nontrivial (R ⧸ I) := by rwa [Submodule.Quotient.nontrivial_iff]
  have : Function.Surjective ψ := by
    intro x; obtain ⟨x, rfl⟩ := hϕ x; obtain ⟨y, hy⟩ := hϕ 1; exact ⟨x otimesₜ y, by simp [ψ, hy]⟩
  exact this.nontrivial

Depends on / 依赖: Function, Function.Surjective, LinearMap, LinearMap.mul, Module, Module.exists_surjective_quotient_of_finite, Nontrivial, Quotient, Submodule, Submodule.Quotient.nontrivial_iff, Surjective, TensorProduct, TensorProduct.map, exists_surjective_quotient_of_finite, nontrivial, nontrivial_iff, otimes, this.nontrivial
-/
instance : Nontrivial (M otimes[R] M) := by
  obtain ⟨I, ϕ, hI, hϕ⟩ := Module.exists_surjective_quotient_of_finite R M
  let ψ : M otimes[R] M ->ₗ[R] R ⧸ I :=
    (LinearMap.mul' R (R ⧸ I)).comp (TensorProduct.map ϕ ϕ)
  have : Nontrivial (R ⧸ I) := by rwa [Submodule.Quotient.nontrivial_iff]
  have : Function.Surjective ψ := by
    intro x; obtain ⟨x, rfl⟩ := hϕ x; obtain ⟨y, hy⟩ := hϕ 1; exact ⟨x otimesₜ y, by simp [ψ, hy]⟩
  exact this.nontrivial

end NontrivialTensorProduct

/--
theorem `Subalgebra.finite_sup` / 定理 `Subalgebra.finite_sup`

English:
theorem Subalgebra.finite_sup
  statement: {K L : Type*} [CommSemiring K] [CommSemiring L] [Algebra K L]
  proof: by
  rw [← E1.range_val]; rw [← E2.range_val]; rw [← Algebra.TensorProduct.productMap_range]
  exact Module.Finite.range (Algebra.TensorProduct.productMap E1.val E2.val).toLinearMap

中文:
定理 子代数.finite_sup
  结论: {K L : 类型} [交换半环 K] [交换半环 L] [代数 K L]
  证明: by
  rw [← E1.range_val]; rw [← E2.range_val]; rw [← Algebra.TensorProduct.productMap_range]
  exact Module.Finite.range (Algebra.TensorProduct.productMap E1.val E2.val).toLinearMap

Depends on / 依赖: Algebra, Algebra.TensorProduct.productMap, Algebra.TensorProduct.productMap_range, E1.range_val, E1.val, E2.range_val, E2.val, Finite, Module, Module.Finite.range, TensorProduct, productMap, productMap_range, range_val, toLinearMap
-/
theorem Subalgebra.finite_sup {K L : Type*} [CommSemiring K] [CommSemiring L] [Algebra K L]
    (E1 E2 : Subalgebra K L) [Module.Finite K E1] [Module.Finite K E2] :
    Module.Finite K ↥(E1 ⊔ E2) := by
  rw [← E1.range_val]; rw [← E2.range_val]; rw [← Algebra.TensorProduct.productMap_range]
  exact Module.Finite.range (Algebra.TensorProduct.productMap E1.val E2.val).toLinearMap

-- Subsumed by `RingHom.Finite.tensorProductMap`.
/--
lemma `RingHom.Finite.tensorProductMap_id` / 引理 `RingHom.Finite.tensorProductMap_id`

English:
lemma RingHom.Finite.tensorProductMap_id
  proof: by
  let := f.toRingHom.toAlgebra
  have := IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  have : Module.Finite S S' := finite_algebraMap.mp Hf
  change (Algebra.TensorProduct.map (Algebra.ofId S S') (AlgHom.id R T)).Finite
  convert_to (((Algebra.TensorProduct.comm _ _ _).trans
      (Algebra.TensorProduct.cancelBaseChange R S S S' T)).toAlgHom.comp
    Algebra.TensorProduct.includeLeft).Finite
  · ext; simp
  exact (RingEquiv.finite _).comp (finite_algebraMap.mpr inferInstance)

中文:
引理 环态射.有限.tensorProductMap_id
  证明: by
  let := f.toRingHom.toAlgebra
  have := IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  have : Module.Finite S S' := finite_algebraMap.mp Hf
  change (Algebra.TensorProduct.map (Algebra.ofId S S') (AlgHom.id R T)).Finite
  convert_to (((Algebra.TensorProduct.comm _ _ _).trans
      (Algebra.TensorProduct.cancelBaseChange R S S S' T)).toAlgHom.comp
    Algebra.TensorProduct.includeLeft).Finite
  · ext; simp
  exact (RingEquiv.finite _).comp (finite_algebraMap.mpr inferInstance)
-/
private lemma RingHom.Finite.tensorProductMap_id
    {R S S' T : Type*} [CommRing R] [CommRing S] [CommRing T] [CommRing S']
    [Algebra R S] [Algebra R T] [Algebra R S']
    {f : S ->ₐ[R] S'} (Hf : f.Finite) :
    (Algebra.TensorProduct.map f (AlgHom.id R T)).toRingHom.Finite := by
  let := f.toRingHom.toAlgebra
  have := IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  have : Module.Finite S S' := finite_algebraMap.mp Hf
  change (Algebra.TensorProduct.map (Algebra.ofId S S') (AlgHom.id R T)).Finite
  convert_to (((Algebra.TensorProduct.comm _ _ _).trans
      (Algebra.TensorProduct.cancelBaseChange R S S S' T)).toAlgHom.comp
    Algebra.TensorProduct.includeLeft).Finite
  · ext; simp
  exact (RingEquiv.finite _).comp (finite_algebraMap.mpr inferInstance)

/--
lemma `RingHom.Finite.tensorProductMap` / 引理 `RingHom.Finite.tensorProductMap`

English:
lemma RingHom.Finite.tensorProductMap
  proof: by
  convert!
.comp RingHom.Finite.tensorProductMap_id (T := T') Hf
.comp (Algebra.TensorProduct.comm _ _ _).toRingEquiv.finite
.comp RingHom.Finite.tensorProductMap_id (T := S) Hg
          (Algebra.TensorProduct.comm _ _ _).toRingEquiv.finite
  simp only [AlgHom.toRingHom_eq_coe, RingEquiv.toRingHom_eq_coe,
    AlgEquiv.toRingEquiv_toRingHom, ← AlgEquiv.toAlgHom_toRingHom, ← AlgHom.comp_toRingHom]
  congr
  ext <;> simp

中文:
引理 环态射.有限.tensorProductMap
  证明: by
  convert!
.comp RingHom.Finite.tensorProductMap_id (T := T') Hf
.comp (Algebra.TensorProduct.comm _ _ _).toRingEquiv.finite
.comp RingHom.Finite.tensorProductMap_id (T := S) Hg
          (Algebra.TensorProduct.comm _ _ _).toRingEquiv.finite
  simp only [AlgHom.toRingHom_eq_coe, RingEquiv.toRingHom_eq_coe,
    AlgEquiv.toRingEquiv_toRingHom, ← AlgEquiv.toAlgHom_toRingHom, ← AlgHom.comp_toRingHom]
  congr
  ext <;> simp

Depends on / 依赖: AlgEquiv, AlgEquiv.toAlgHom_toRingHom, AlgEquiv.toRingEquiv_toRingHom, AlgHom, AlgHom.comp_toRingHom, AlgHom.toRingHom_eq_coe, Algebra, Algebra.TensorProduct.comm, Finite, RingEquiv, RingEquiv.toRingHom_eq_coe, RingHom, RingHom.Finite.tensorProductMap_id, TensorProduct, comp_toRingHom, convert, finite, tensorProductMap_id, toAlgHom_toRingHom, toRingEquiv
-/
lemma RingHom.Finite.tensorProductMap
    {R S S' T T' : Type*} [CommRing R] [CommRing S] [CommRing T] [CommRing S'] [CommRing T']
    [Algebra R S] [Algebra R T] [Algebra R S'] [Algebra R T']
    {f : S ->ₐ[R] S'} (Hf : f.Finite) {g : T ->ₐ[R] T'} (Hg : g.Finite) :
    (Algebra.TensorProduct.map f g).toRingHom.Finite := by
  convert!
.comp RingHom.Finite.tensorProductMap_id (T := T') Hf
.comp (Algebra.TensorProduct.comm _ _ _).toRingEquiv.finite
.comp RingHom.Finite.tensorProductMap_id (T := S) Hg
          (Algebra.TensorProduct.comm _ _ _).toRingEquiv.finite
  simp only [AlgHom.toRingHom_eq_coe, RingEquiv.toRingHom_eq_coe,
    AlgEquiv.toRingEquiv_toRingHom, ← AlgEquiv.toAlgHom_toRingHom, ← AlgHom.comp_toRingHom]
  congr
  ext <;> simp
