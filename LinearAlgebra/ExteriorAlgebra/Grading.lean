/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
public import Mathlib.RingTheory.GradedAlgebra.Basic

/-!
# Results about the grading structure of the exterior algebra

Many of these results are copied with minimal modification from the tensor algebra.

The main result is `ExteriorAlgebra.gradedAlgebra`, which says that the exterior algebra is a
ℕ-graded algebra.
-/

@[expose] public section

namespace ExteriorAlgebra

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable (R M)

open scoped DirectSum

/--
Definition of `GradedAlgebra.ι` / `GradedAlgebra.ι` 的定义

English:
definition GradedAlgebra.ι
  signature: :
  body: DirectSum.lof R Nat (fun i => ⋀[R]^i M) 1 ∘ₗ
    (ι R).codRestrict _ fun m => by simpa only [pow_one] using LinearMap.mem_range_self _ m

中文:
定义 分次代数.ι
  签名: :
  定义体: DirectSum.lof R Nat (fun i => ⋀[R]^i M) 1 ∘ₗ
    (ι R).codRestrict _ fun m => by simpa only [pow_one] using LinearMap.mem_range_self _ m
-/
protected def GradedAlgebra.ι :
    M ->ₗ[R] ⨁ i : Nat, ⋀[R]^i M :=
  DirectSum.lof R Nat (fun i => ⋀[R]^i M) 1 ∘ₗ
    (ι R).codRestrict _ fun m => by simpa only [pow_one] using LinearMap.mem_range_self _ m

/--
theorem `GradedAlgebra.ι_apply` / 定理 `GradedAlgebra.ι_apply`

English:
theorem GradedAlgebra.ι_apply
  given: (m : M)
  proof: rfl

中文:
定理 分次代数.ι_apply
  条件: (m : M)
  证明: rfl
-/
theorem GradedAlgebra.ι_apply (m : M) :
    GradedAlgebra.ι R M m =
      DirectSum.of (fun i : Nat => ⋀[R]^i M) 1
        ⟨ι R m, by simpa only [pow_one] using LinearMap.mem_range_self _ m⟩ :=
  rfl

-- Defining this instance manually, because Lean doesn't seem to be able to synthesize it.
-- Strangely, this problem only appears when we use the abbreviation or notation for the
-- exterior powers.
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SetLike.GradedMonoid fun i
  body: Submodule.nat_power_gradedMonoid (LinearMap.range (ι R : M ->ₗ[R] ExteriorAlgebra R M))

中文:
实例 :
  签名: 集合状.分次幺半群 fun i
  定义体: Submodule.nat_power_gradedMonoid (LinearMap.range (ι R : M ->ₗ[R] ExteriorAlgebra R M))

Depends on / 依赖: ExteriorAlgebra, LinearMap, LinearMap.range, Submodule, Submodule.nat_power_gradedMonoid, nat_power_gradedMonoid
-/
instance : SetLike.GradedMonoid fun i : Nat => ⋀[R]^i M :=
  Submodule.nat_power_gradedMonoid (LinearMap.range (ι R : M ->ₗ[R] ExteriorAlgebra R M))

/--
theorem `GradedAlgebra.ι_sq_zero` / 定理 `GradedAlgebra.ι_sq_zero`

English:
theorem GradedAlgebra.ι_sq_zero
  given: (m : M)
  statement: GradedAlgebra.ι R M m * GradedAlgebra.ι R M m = 0
  proof: by
  rw [GradedAlgebra.ι_apply]; rw [DirectSum.of_mul_of]
  exact DFinsupp.single_eq_zero.mpr (Subtype.ext <| ExteriorAlgebra.ι_sq_zero _)

中文:
定理 分次代数.ι_sq_zero
  条件: (m : M)
  结论: 分次代数.ι R M m * 分次代数.ι R M m = 0
  证明: by
  rw [GradedAlgebra.ι_apply]; rw [DirectSum.of_mul_of]
  exact DFinsupp.single_eq_zero.mpr (Subtype.ext <| ExteriorAlgebra.ι_sq_zero _)

Depends on / 依赖: DFinsupp, DFinsupp.single_eq_zero.mpr, DirectSum, DirectSum.of_mul_of, ExteriorAlgebra, GradedAlgebra, Subtype, Subtype.ext, of_mul_of, single_eq_zero
-/
theorem GradedAlgebra.ι_sq_zero (m : M) : GradedAlgebra.ι R M m * GradedAlgebra.ι R M m = 0 := by
  rw [GradedAlgebra.ι_apply]; rw [DirectSum.of_mul_of]
  exact DFinsupp.single_eq_zero.mpr (Subtype.ext <| ExteriorAlgebra.ι_sq_zero _)

/--
Definition of `GradedAlgebra.liftι` / `GradedAlgebra.liftι` 的定义

English:
definition GradedAlgebra.liftι
  signature: :
  body: lift R ⟨by apply GradedAlgebra.ι R M, GradedAlgebra.ι_sq_zero R M⟩

中文:
定义 分次代数.liftι
  签名: :
  定义体: lift R ⟨by apply GradedAlgebra.ι R M, GradedAlgebra.ι_sq_zero R M⟩

Depends on / 依赖: GradedAlgebra
-/
def GradedAlgebra.liftι :
    ExteriorAlgebra R M ->ₐ[R] ⨁ i : Nat, ⋀[R]^i M :=
  lift R ⟨by apply GradedAlgebra.ι R M, GradedAlgebra.ι_sq_zero R M⟩

/--
theorem `GradedAlgebra.liftι_eq` / 定理 `GradedAlgebra.liftι_eq`

English:
theorem GradedAlgebra.liftι_eq
  given: (i : Nat) (x : ⋀[R]^i M)
  proof: by
  obtain ⟨x, hx⟩ := x
  dsimp only [Subtype.coe_mk, DirectSum.lof_eq_of]
  induction hx using Submodule.pow_induction_on_left' with
  | algebraMap => simp_rw [AlgHom.commutes, DirectSum.algebraMap_apply]; rfl
  | add _ _ _ _ _ ihx ihy => simp_rw [map_add, ihx, ihy, ← map_add]; rfl
  | mem_mul _ hm _ _ _ ih =>
      obtain ⟨_, rfl⟩ := hm
      simp_rw [map_mul, ih, GradedAlgebra.liftι, lift_ι_apply, GradedAlgebra.ι_apply R M,
        DirectSum.of_mul_of]
      exact DirectSum.of_eq_of_gradedMonoid_eq (Sigma.subtype_ext (add_comm _ _) rfl)

中文:
定理 分次代数.liftι_eq
  条件: (i : 自然数) (x : ⋀[R]^i M)
  证明: by
  obtain ⟨x, hx⟩ := x
  dsimp only [Subtype.coe_mk, DirectSum.lof_eq_of]
  induction hx using Submodule.pow_induction_on_left' with
  | algebraMap => simp_rw [AlgHom.commutes, DirectSum.algebraMap_apply]; rfl
  | add _ _ _ _ _ ihx ihy => simp_rw [map_add, ihx, ihy, ← map_add]; rfl
  | mem_mul _ hm _ _ _ ih =>
      obtain ⟨_, rfl⟩ := hm
      simp_rw [map_mul, ih, GradedAlgebra.liftι, lift_ι_apply, GradedAlgebra.ι_apply R M,
        DirectSum.of_mul_of]
      exact DirectSum.of_eq_of_gradedMonoid_eq (Sigma.subtype_ext (add_comm _ _) rfl)

Depends on / 依赖: AlgHom, AlgHom.commutes, DirectSum, DirectSum.algebraMap_apply, DirectSum.lof_eq_of, DirectSum.of_eq_of_gradedMonoid_eq, DirectSum.of_mul_of, GradedAlgebra, GradedAlgebra.lift, Sigma.subtype_ext, Submodule, Submodule.pow_induction_on_left, Subtype, Subtype.coe_mk, add_comm, algebraMap, algebraMap_apply, coe_mk, commutes, lof_eq_of
-/
theorem GradedAlgebra.liftι_eq (i : Nat) (x : ⋀[R]^i M) :
    GradedAlgebra.liftι R M x = DirectSum.of (fun i => ⋀[R]^i M) i x := by
  obtain ⟨x, hx⟩ := x
  dsimp only [Subtype.coe_mk, DirectSum.lof_eq_of]
  induction hx using Submodule.pow_induction_on_left' with
  | algebraMap => simp_rw [AlgHom.commutes, DirectSum.algebraMap_apply]; rfl
  | add _ _ _ _ _ ihx ihy => simp_rw [map_add, ihx, ihy, ← map_add]; rfl
  | mem_mul _ hm _ _ _ ih =>
      obtain ⟨_, rfl⟩ := hm
      simp_rw [map_mul, ih, GradedAlgebra.liftι, lift_ι_apply, GradedAlgebra.ι_apply R M,
        DirectSum.of_mul_of]
      exact DirectSum.of_eq_of_gradedMonoid_eq (Sigma.subtype_ext (add_comm _ _) rfl)

/--
Instance `gradedAlgebra` / 实例 `gradedAlgebra`

English:
instance gradedAlgebra
  signature: : GradedAlgebra (fun i : Nat => ⋀[R]^i M)
  body: GradedAlgebra.ofAlgHom _
    (-- while not necessary, the `by apply` makes this elaborate faster
    by apply GradedAlgebra.liftι R M)
    -- the proof from here onward is identical to the `TensorAlgebra` case
    (by
      ext m
      dsimp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, AlgHom.comp_apply,
        AlgHom.id_apply, GradedAlgebra.liftι]
      rw [lift_ι_apply]; rw [GradedAlgebra.ι_apply R M]; rw [DirectSum.coeAlgHom_of]; rw [Subtype.coe_mk])
    (by apply GradedAlgebra.liftι_eq R M)

中文:
实例 gradedAlgebra
  签名: : 分次代数 (fun i : 自然数 => ⋀[R]^i M)
  定义体: GradedAlgebra.ofAlgHom _
    (-- while not necessary, the `by apply` makes this elaborate faster
    by apply GradedAlgebra.liftι R M)
    -- the proof from here onward is identical to the `TensorAlgebra` case
    (by
      ext m
      dsimp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, AlgHom.comp_apply,
        AlgHom.id_apply, GradedAlgebra.liftι]
      rw [lift_ι_apply]; rw [GradedAlgebra.ι_apply R M]; rw [DirectSum.coeAlgHom_of]; rw [Subtype.coe_mk])
    (by apply GradedAlgebra.liftι_eq R M)

Depends on / 依赖: GradedAlgebra, GradedAlgebra.lift, GradedAlgebra.ofAlgHom, elaborate, faster, necessary, ofAlgHom
-/
instance gradedAlgebra : GradedAlgebra (fun i : Nat => ⋀[R]^i M) :=
  GradedAlgebra.ofAlgHom _
    (-- while not necessary, the `by apply` makes this elaborate faster
    by apply GradedAlgebra.liftι R M)
    -- the proof from here onward is identical to the `TensorAlgebra` case
    (by
      ext m
      dsimp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, AlgHom.comp_apply,
        AlgHom.id_apply, GradedAlgebra.liftι]
      rw [lift_ι_apply]; rw [GradedAlgebra.ι_apply R M]; rw [DirectSum.coeAlgHom_of]; rw [Subtype.coe_mk])
    (by apply GradedAlgebra.liftι_eq R M)

/--
lemma `ιMulti_span` / 引理 `ιMulti_span`

English:
lemma ιMulti_span
  proof: by
  rw [Submodule.eq_top_iff']
  intro x
  induction x using DirectSum.Decomposition.inductionOn fun i => ⋀[R]^i M with
  | zero => exact Submodule.zero_mem _
  | add _ _ hm hm' => exact Submodule.add_mem _ hm hm'
  | homogeneous hm =>
    let ⟨m, hm⟩ := hm
    apply Set.mem_of_mem_of_subset hm
    rw [← ιMulti_span_fixedDegree]
    refine Submodule.span_mono fun _ hx => ?_
    obtain ⟨y, rfl⟩ := hx
    exact ⟨⟨_, y⟩, rfl⟩

中文:
引理 ιMulti_span
  证明: by
  rw [Submodule.eq_top_iff']
  intro x
  induction x using DirectSum.Decomposition.inductionOn fun i => ⋀[R]^i M with
  | zero => exact Submodule.zero_mem _
  | add _ _ hm hm' => exact Submodule.add_mem _ hm hm'
  | homogeneous hm =>
    let ⟨m, hm⟩ := hm
    apply Set.mem_of_mem_of_subset hm
    rw [← ιMulti_span_fixedDegree]
    refine Submodule.span_mono fun _ hx => ?_
    obtain ⟨y, rfl⟩ := hx
    exact ⟨⟨_, y⟩, rfl⟩

Depends on / 依赖: Decomposition, DirectSum, DirectSum.Decomposition.inductionOn, Set.mem_of_mem_of_subset, Submodule, Submodule.add_mem, Submodule.eq_top_iff, Submodule.span_mono, Submodule.zero_mem, add_mem, eq_top_iff, homogeneous, inductionOn, mem_of_mem_of_subset, span_mono, zero_mem
-/
lemma ιMulti_span :
    Submodule.span R (Set.range fun x : Σ n, (Fin n -> M) => ιMulti R x.1 x.2) = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro x
  induction x using DirectSum.Decomposition.inductionOn fun i => ⋀[R]^i M with
  | zero => exact Submodule.zero_mem _
  | add _ _ hm hm' => exact Submodule.add_mem _ hm hm'
  | homogeneous hm =>
    let ⟨m, hm⟩ := hm
    apply Set.mem_of_mem_of_subset hm
    rw [← ιMulti_span_fixedDegree]
    refine Submodule.span_mono fun _ hx => ?_
    obtain ⟨y, rfl⟩ := hx
    exact ⟨⟨_, y⟩, rfl⟩

end ExteriorAlgebra
