/-
Copyright (c) 2022 Antoine Labelle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Labelle
-/
module

public import Mathlib.RepresentationTheory.Intertwining
public import Mathlib.RepresentationTheory.FDRep
public import Mathlib.RepresentationTheory.Rep.Res

/-!
# Subspace of invariants a group representation

This file introduces the subspace of invariants of a group representation
and proves basic results about it.
The main tool used is the average of all elements of the group, seen as an element of `k[G]`.
The action of this special element gives a projection onto the subspace of invariants.
In order for the definition of the average element to make sense, we need to assume for most of the
results that the order of `G` is invertible in `k` (e. g. `k` has characteristic `0`).
-/

@[expose] public section

suppress_compilation

universe w u v

open MonoidAlgebra

open Representation

namespace GroupAlgebra

variable (k G : Type*) [CommSemiring k] [Group G]
variable [Fintype G] [Invertible (Fintype.card G : k)]

/--
Definition of `average` / `average` 的定义

English:
definition average
  signature: : k[G]
  body: ⅟(Fintype.card G : k) • ∑ g : G, of k G g

中文:
定义 average
  签名: : k[G]
  定义体: ⅟(Fintype.card G : k) • ∑ g : G, of k G g

Depends on / 依赖: Fintype, Fintype.card
-/
noncomputable def average : k[G] := ⅟(Fintype.card G : k) • ∑ g : G, of k G g

set_option backward.isDefEq.respectTransparency.types false in
/-- `average k G` is invariant under left multiplication by elements of `G`. -/
@[simp]
/--
theorem `mul_average_left` / 定理 `mul_average_left`

English:
theorem mul_average_left
  given: (g : G)
  statement: .single g 1 * average k G = average k G
  proof: by
  simp only [mul_one, Finset.mul_sum, Algebra.mul_smul_comm, average, MonoidAlgebra.of_apply,
    MonoidAlgebra.single_mul_single]
  set f : G -> k[G] := fun x => .single x 1
  change ⅟(Fintype.card G : k) • ∑ x : G, f (g * x) = ⅟(Fintype.card G : k) • ∑ x : G, f x
  rw [Function.Bijective.sum_comp (Group.mulLeft_bijective g) _]

中文:
定理 mul_average_left
  条件: (g : G)
  结论: .single g 1 * average k G = average k G
  证明: by
  simp only [mul_one, Finset.mul_sum, Algebra.mul_smul_comm, average, MonoidAlgebra.of_apply,
    MonoidAlgebra.single_mul_single]
  set f : G -> k[G] := fun x => .single x 1
  change ⅟(Fintype.card G : k) • ∑ x : G, f (g * x) = ⅟(Fintype.card G : k) • ∑ x : G, f x
  rw [Function.Bijective.sum_comp (Group.mulLeft_bijective g) _]

Depends on / 依赖: Algebra, Algebra.mul_smul_comm, Bijective, Finset, Finset.mul_sum, Fintype, Fintype.card, Function, Function.Bijective.sum_comp, Group.mulLeft_bijective, MonoidAlgebra, MonoidAlgebra.of_apply, MonoidAlgebra.single_mul_single, average, mulLeft_bijective, mul_one, mul_smul_comm, mul_sum, of_apply, single
-/
theorem mul_average_left (g : G) : .single g 1 * average k G = average k G := by
  simp only [mul_one, Finset.mul_sum, Algebra.mul_smul_comm, average, MonoidAlgebra.of_apply,
    MonoidAlgebra.single_mul_single]
  set f : G -> k[G] := fun x => .single x 1
  change ⅟(Fintype.card G : k) • ∑ x : G, f (g * x) = ⅟(Fintype.card G : k) • ∑ x : G, f x
  rw [Function.Bijective.sum_comp (Group.mulLeft_bijective g) _]

set_option backward.isDefEq.respectTransparency.types false in
/-- `average k G` is invariant under right multiplication by elements of `G`.
-/
@[simp]
/--
theorem `mul_average_right` / 定理 `mul_average_right`

English:
theorem mul_average_right
  given: (g : G)
  statement: average k G * .single g 1 = average k G
  proof: by
  simp only [mul_one, Finset.sum_mul, Algebra.smul_mul_assoc, average, MonoidAlgebra.of_apply,
    MonoidAlgebra.single_mul_single]
  set f : G -> k[G] := fun x => .single x 1
  change ⅟(Fintype.card G : k) • ∑ x : G, f (x * g) = ⅟(Fintype.card G : k) • ∑ x : G, f x
  rw [Function.Bijective.sum_comp (Group.mulRight_bijective g) _]

中文:
定理 mul_average_right
  条件: (g : G)
  结论: average k G * .single g 1 = average k G
  证明: by
  simp only [mul_one, Finset.sum_mul, Algebra.smul_mul_assoc, average, MonoidAlgebra.of_apply,
    MonoidAlgebra.single_mul_single]
  set f : G -> k[G] := fun x => .single x 1
  change ⅟(Fintype.card G : k) • ∑ x : G, f (x * g) = ⅟(Fintype.card G : k) • ∑ x : G, f x
  rw [Function.Bijective.sum_comp (Group.mulRight_bijective g) _]

Depends on / 依赖: Algebra, Algebra.smul_mul_assoc, Bijective, Finset, Finset.sum_mul, Fintype, Fintype.card, Function, Function.Bijective.sum_comp, Group.mulRight_bijective, MonoidAlgebra, MonoidAlgebra.of_apply, MonoidAlgebra.single_mul_single, average, mulRight_bijective, mul_one, of_apply, single, single_mul_single, smul_mul_assoc
-/
theorem mul_average_right (g : G) : average k G * .single g 1 = average k G := by
  simp only [mul_one, Finset.sum_mul, Algebra.smul_mul_assoc, average, MonoidAlgebra.of_apply,
    MonoidAlgebra.single_mul_single]
  set f : G -> k[G] := fun x => .single x 1
  change ⅟(Fintype.card G : k) • ∑ x : G, f (x * g) = ⅟(Fintype.card G : k) • ∑ x : G, f x
  rw [Function.Bijective.sum_comp (Group.mulRight_bijective g) _]

end GroupAlgebra

namespace Representation

section Invariants

open GroupAlgebra

variable {k G V W : Type*} [CommRing k] [Group G] [AddCommGroup V] [Module k V] [AddCommGroup W]
  [Module k W]
variable (ρ : Representation k G V) (σ : Representation k G W)

/--
Definition of `invariants` / `invariants` 的定义

English:
definition invariants
  signature: : Submodule k V where
  body: Set.ofPred fun v => forall g : G, ρ g v = v
  zero_mem' g := by simp only [map_zero]
  add_mem' hv hw g := by simp only [hv g, hw g, map_add]
  smul_mem' r v hv g := by simp only [hv g, map_smulₛₗ, RingHom.id_apply]

@[simp]

中文:
定义 invariants
  签名: : 子模 k V where
  定义体: Set.ofPred fun v => forall g : G, ρ g v = v
  zero_mem' g := by simp only [map_zero]
  add_mem' hv hw g := by simp only [hv g, hw g, map_add]
  smul_mem' r v hv g := by simp only [hv g, map_smulₛₗ, RingHom.id_apply]

@[simp]

Depends on / 依赖: Set.ofPred, ofPred
-/
def invariants : Submodule k V where
  carrier := Set.ofPred fun v => forall g : G, ρ g v = v
  zero_mem' g := by simp only [map_zero]
  add_mem' hv hw g := by simp only [hv g, hw g, map_add]
  smul_mem' r v hv g := by simp only [hv g, map_smulₛₗ, RingHom.id_apply]

@[simp]
/--
theorem `mem_invariants` / 定理 `mem_invariants`

English:
theorem mem_invariants
  given: (v : V)
  statement: v in invariants ρ ↔ forall g : G, ρ g v = v
  proof: by rfl

中文:
定理 mem_invariants
  条件: (v : V)
  结论: v in invariants ρ ↔ 对任意 g : G, ρ g v = v
  证明: by rfl
-/
theorem mem_invariants (v : V) : v in invariants ρ ↔ forall g : G, ρ g v = v := by rfl

/--
theorem `invariants_eq_inter` / 定理 `invariants_eq_inter`

English:
theorem invariants_eq_inter
  statement: (invariants ρ).carrier = ⋂ g : G, Function.fixedPoints (ρ g)
  proof: by
  ext; simp [Function.IsFixedPt]

中文:
定理 invariants_eq_inter
  结论: (invariants ρ).carrier = ⋂ g : G, 函数.fixedPoints (ρ g)
  证明: by
  ext; simp [Function.IsFixedPt]

Depends on / 依赖: Function, Function.IsFixedPt, IsFixedPt
-/
theorem invariants_eq_inter : (invariants ρ).carrier = ⋂ g : G, Function.fixedPoints (ρ g) := by
  ext; simp [Function.IsFixedPt]

/--
theorem `invariants_eq_top` / 定理 `invariants_eq_top`

English:
theorem invariants_eq_top
  given: [ρ.IsTrivial]
  proof: eq_top_iff.2 (fun x _ g => ρ.isTrivial_apply g x)

中文:
定理 invariants_eq_top
  条件: [ρ.是平凡]
  证明: eq_top_iff.2 (fun x _ g => ρ.isTrivial_apply g x)

Depends on / 依赖: eq_top_iff, isTrivial_apply
-/
theorem invariants_eq_top [ρ.IsTrivial] :
    invariants ρ = ⊤ :=
eq_top_iff.2 (fun x _ g => ρ.isTrivial_apply g x)

/--
lemma `mem_invariants_iff_of_forall_mem_zpowers` / 引理 `mem_invariants_iff_of_forall_mem_zpowers`

English:
lemma mem_invariants_iff_of_forall_mem_zpowers
  proof: ⟨fun h => h g, fun hx γ => by
    rcases hg γ with ⟨i, rfl⟩
    induction i with | zero => simp | succ i _ => simp_all [zpow_add_one] | pred i h => _
    simpa [neg_sub_comm _ (1 : Int), zpow_sub] using congr(ρ g⁻¹ $(h.trans hx.symm))⟩

中文:
引理 mem_invariants_iff_of_对任意_mem_zpowers
  证明: ⟨fun h => h g, fun hx γ => by
    rcases hg γ with ⟨i, rfl⟩
    induction i with | zero => simp | succ i _ => simp_all [zpow_add_one] | pred i h => _
    simpa [neg_sub_comm _ (1 : Int), zpow_sub] using congr(ρ g⁻¹ $(h.trans hx.symm))⟩

Depends on / 依赖: h.trans, hx.symm, neg_sub_comm, zpow_add_one, zpow_sub
-/
lemma mem_invariants_iff_of_forall_mem_zpowers
    (g : G) (hg : forall x, x in Subgroup.zpowers g) (x : V) :
    x in ρ.invariants ↔ ρ g x = x :=
  ⟨fun h => h g, fun hx γ => by
    rcases hg γ with ⟨i, rfl⟩
    induction i with | zero => simp | succ i _ => simp_all [zpow_add_one] | pred i h => _
    simpa [neg_sub_comm _ (1 : Int), zpow_sub] using congr(ρ g⁻¹ $(h.trans hx.symm))⟩

variable {ρ σ} in
/--
lemma `mem_linHom_invariants_iff_isIntertwining` / 引理 `mem_linHom_invariants_iff_isIntertwining`

English:
lemma mem_linHom_invariants_iff_isIntertwining
  given: (f : V ->ₗ[k] W)
  proof: by
  refine ⟨fun hf => ⟨fun γ v => ?_⟩, fun hf γ => ?_⟩
  · specialize hf γ
    nth_rewrite 1 [← hf]
    simp
  · ext v
    simp [hf.isIntertwining]

中文:
引理 mem_linHom_invariants_iff_is整数ertwining
  条件: (f : V ->ₗ[k] W)
  证明: by
  refine ⟨fun hf => ⟨fun γ v => ?_⟩, fun hf γ => ?_⟩
  · specialize hf γ
    nth_rewrite 1 [← hf]
    simp
  · ext v
    simp [hf.isIntertwining]
-/
@[simp] lemma mem_linHom_invariants_iff_isIntertwining (f : V ->ₗ[k] W) :
    (forall (g : G), σ g ∘ₗ f ∘ₗ ρ g⁻¹ = f) ↔ ρ.IsIntertwiningMap σ f := by
  refine ⟨fun hf => ⟨fun γ v => ?_⟩, fun hf γ => ?_⟩
  · specialize hf γ
    nth_rewrite 1 [← hf]
    simp
  · ext v
    simp [hf.isIntertwining]

/--
Definition of `invariantsEquivIntertwiningMap` / `invariantsEquivIntertwiningMap` 的定义

English:
definition invariantsEquivIntertwiningMap
  signature: : (linHom ρ σ).invariants ≃ₗ[k] IntertwiningMap ρ σ where
  body: f.val.intertwiningMap_of_isIntertwiningMap ρ σ
    ((mem_linHom_invariants_iff_isIntertwining f.val).mp f.property).isIntertwining
  map_add' _ _ := IntertwiningMap.ext_iff.mpr rfl
  map_smul' _ _ := IntertwiningMap.ext_iff.mpr rfl
  invFun g :=
    { val := g.toLinearMap
      property := (mem_linHom_invariants_iff_isIntertwining g.toLinearMap).mpr
        { isIntertwining := g.isIntertwining } }

中文:
定义 invariantsEquiv整数ertwiningMap
  签名: : (linHom ρ σ).invariants ≃ₗ[k] 整数ertwining映射 ρ σ where
  定义体: f.val.intertwiningMap_of_isIntertwiningMap ρ σ
    ((mem_linHom_invariants_iff_isIntertwining f.val).mp f.property).isIntertwining
  map_add' _ _ := IntertwiningMap.ext_iff.mpr rfl
  map_smul' _ _ := IntertwiningMap.ext_iff.mpr rfl
  invFun g :=
    { val := g.toLinearMap
      property := (mem_linHom_invariants_iff_isIntertwining g.toLinearMap).mpr
        { isIntertwining := g.isIntertwining } }

Depends on / 依赖: f.val.intertwiningMap_of_isIntertwiningMap, intertwiningMap_of_isIntertwiningMap
-/
def invariantsEquivIntertwiningMap : (linHom ρ σ).invariants ≃ₗ[k] IntertwiningMap ρ σ where
  toFun f := f.val.intertwiningMap_of_isIntertwiningMap ρ σ
    ((mem_linHom_invariants_iff_isIntertwining f.val).mp f.property).isIntertwining
  map_add' _ _ := IntertwiningMap.ext_iff.mpr rfl
  map_smul' _ _ := IntertwiningMap.ext_iff.mpr rfl
  invFun g :=
    { val := g.toLinearMap
      property := (mem_linHom_invariants_iff_isIntertwining g.toLinearMap).mpr
        { isIntertwining := g.isIntertwining } }

section

variable [Fintype G] [Invertible (Fintype.card G : k)]

/-- The action of `average k G` gives a projection map onto the subspace of invariants.
-/
@[simp]
/--
Definition of `averageMap` / `averageMap` 的定义

English:
definition averageMap
  signature: : V ->ₗ[k] V
  body: asAlgebraHom ρ (average k G)

中文:
定义 averageMap
  签名: : V ->ₗ[k] V
  定义体: asAlgebraHom ρ (average k G)

Depends on / 依赖: asAlgebraHom, average
-/
noncomputable def averageMap : V ->ₗ[k] V :=
  asAlgebraHom ρ (average k G)

/--
theorem `averageMap_invariant` / 定理 `averageMap_invariant`

English:
theorem averageMap_invariant
  given: (v : V)
  statement: averageMap ρ v in invariants ρ
  proof: fun g => by
  rw [averageMap]; rw [← asAlgebraHom_single_one]; rw [← Module.End.mul_apply]; rw [← map_mul (asAlgebraHom ρ)]; rw [mul_average_left]

中文:
定理 averageMap_invariant
  条件: (v : V)
  结论: averageMap ρ v in invariants ρ
  证明: fun g => by
  rw [averageMap]; rw [← asAlgebraHom_single_one]; rw [← Module.End.mul_apply]; rw [← map_mul (asAlgebraHom ρ)]; rw [mul_average_left]

Depends on / 依赖: Module, Module.End.mul_apply, asAlgebraHom, asAlgebraHom_single_one, averageMap, map_mul, mul_apply, mul_average_left
-/
theorem averageMap_invariant (v : V) : averageMap ρ v in invariants ρ := fun g => by
  rw [averageMap]; rw [← asAlgebraHom_single_one]; rw [← Module.End.mul_apply]; rw [← map_mul (asAlgebraHom ρ)]; rw [mul_average_left]

/--
theorem `averageMap_id` / 定理 `averageMap_id`

English:
theorem averageMap_id
  given: (v : V) (hv : v in invariants ρ)
  statement: averageMap ρ v = v
  proof: by
  rw [mem_invariants] at hv
  simp [average, map_sum, hv, Finset.card_univ, ← Nat.cast_smul_eq_nsmul k _ v, smul_smul]

中文:
定理 averageMap_id
  条件: (v : V) (hv : v in invariants ρ)
  结论: averageMap ρ v = v
  证明: by
  rw [mem_invariants] at hv
  simp [average, map_sum, hv, Finset.card_univ, ← Nat.cast_smul_eq_nsmul k _ v, smul_smul]

Depends on / 依赖: Finset, Finset.card_univ, Nat.cast_smul_eq_nsmul, average, card_univ, cast_smul_eq_nsmul, map_sum, mem_invariants, smul_smul
-/
theorem averageMap_id (v : V) (hv : v in invariants ρ) : averageMap ρ v = v := by
  rw [mem_invariants] at hv
  simp [average, map_sum, hv, Finset.card_univ, ← Nat.cast_smul_eq_nsmul k _ v, smul_smul]

/--
theorem `isProj_averageMap` / 定理 `isProj_averageMap`

English:
theorem isProj_averageMap
  statement: LinearMap.IsProj ρ.invariants ρ.averageMap
  proof: ⟨ρ.averageMap_invariant, ρ.averageMap_id⟩

中文:
定理 isProj_averageMap
  结论: 线性映射.是Proj ρ.invariants ρ.averageMap
  证明: ⟨ρ.averageMap_invariant, ρ.averageMap_id⟩

Depends on / 依赖: averageMap_id, averageMap_invariant
-/
theorem isProj_averageMap : LinearMap.IsProj ρ.invariants ρ.averageMap :=
  ⟨ρ.averageMap_invariant, ρ.averageMap_id⟩

end
section Subgroup

variable {V : Type*} [AddCommGroup V] [Module k V]
variable (ρ : Representation k G V) (S : Subgroup G) [S.Normal]

/--
lemma `le_comap_invariants` / 引理 `le_comap_invariants`

English:
lemma le_comap_invariants
  given: (g : G)
  proof: fun x hx ⟨s, hs⟩ => by
    simpa using congr(ρ g $(hx ⟨(g⁻¹ * s * g), Subgroup.Normal.conj_mem' ‹_› s hs g⟩))

中文:
引理 le_comap_invariants
  条件: (g : G)
  证明: fun x hx ⟨s, hs⟩ => by
    simpa using congr(ρ g $(hx ⟨(g⁻¹ * s * g), Subgroup.Normal.conj_mem' ‹_› s hs g⟩))

Depends on / 依赖: Normal, Subgroup, Subgroup.Normal.conj_mem, conj_mem
-/
lemma le_comap_invariants (g : G) :
    (invariants <| ρ.comp S.subtype) <=
      (invariants <| ρ.comp S.subtype).comap (ρ g) :=
  fun x hx ⟨s, hs⟩ => by
    simpa using congr(ρ g $(hx ⟨(g⁻¹ * s * g), Subgroup.Normal.conj_mem' ‹_› s hs g⟩))

/--
Definition of `toInvariants` / `toInvariants` 的定义

English:
abbreviation toInvariants
  signature: :
  body: subrepresentation ρ _ le_comap_invariants ρ S

中文:
缩写 toInvariants
  签名: :
  定义体: subrepresentation ρ _ le_comap_invariants ρ S

Depends on / 依赖: le_comap_invariants, subrepresentation
-/
abbrev toInvariants :
    Representation k G (invariants (ρ.comp S.subtype)) :=
subrepresentation ρ _ le_comap_invariants ρ S

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsTrivial ((toInvariants ρ S).comp S.subtype)
  body: LinearMap.ext fun ⟨x, hx⟩ => Subtype.ext by simpa using (hx g)

中文:
实例 :
  签名: 是平凡 ((toInvariants ρ S).comp S.subtype)
  定义体: LinearMap.ext fun ⟨x, hx⟩ => Subtype.ext by simpa using (hx g)

Depends on / 依赖: LinearMap, LinearMap.ext, Subtype, Subtype.ext
-/
instance : IsTrivial ((toInvariants ρ S).comp S.subtype) where
out g := LinearMap.ext fun ⟨x, hx⟩ => Subtype.ext by simpa using (hx g)

/--
Definition of `quotientToInvariants` / `quotientToInvariants` 的定义

English:
abbreviation quotientToInvariants
  signature: :
  body: ofQuotient (toInvariants ρ S) S

中文:
缩写 quotientToInvariants
  签名: :
  定义体: ofQuotient (toInvariants ρ S) S

Depends on / 依赖: ofQuotient, toInvariants
-/
abbrev quotientToInvariants :
    Representation k (G ⧸ S) (invariants (ρ.comp S.subtype)) :=
  ofQuotient (toInvariants ρ S) S

/--
Definition of `quotientToInvariants_lift` / `quotientToInvariants_lift` 的定义

English:
abbreviation quotientToInvariants_lift
  signature: :
  body: ⟨Submodule.subtype _, fun _ => rfl⟩

中文:
缩写 quotientToInvariants_lift
  签名: :
  定义体: ⟨Submodule.subtype _, fun _ => rfl⟩

Depends on / 依赖: Submodule, Submodule.subtype, subtype
-/
abbrev quotientToInvariants_lift :
    Representation.IntertwiningMap (MonoidHom.comp (quotientToInvariants ρ S)
      (QuotientGroup.mk' _)) ρ := ⟨Submodule.subtype _, fun _ => rfl⟩

end Subgroup
end Invariants

namespace linHom

open CategoryTheory Action

section Rep

variable {k : Type u} [CommRing k] {G : Type v} [Group G] {X Y : Rep.{w} k G}

/--
theorem `mem_invariants_iff_comm` / 定理 `mem_invariants_iff_comm`

English:
theorem mem_invariants_iff_comm
  given: (f : X.V ->ₗ[k] Y.V) (g : G)
  proof: by
  dsimp
  constructor
  · intro h
    nth_rw 1 [← h]
    rw [LinearMap.comp_assoc]; rw [LinearMap.comp_assoc]; rw [← Rep.ρ_mul]; rw [inv_mul_cancel]; rw [map_one]; rw [Module.End.one_eq_id]; rw [LinearMap.comp_id]
  · intro h
    rw [← LinearMap.comp_assoc]; rw [← h]; rw [LinearMap.comp_assoc]; rw [← Rep.ρ_mul]; rw [mul_inv_cancel]; rw [map_one]; rw [Module.End.one_eq_id]; rw [LinearMap.comp_id]

中文:
定理 mem_invariants_iff_comm
  条件: (f : X.V ->ₗ[k] Y.V) (g : G)
  证明: by
  dsimp
  constructor
  · intro h
    nth_rw 1 [← h]
    rw [LinearMap.comp_assoc]; rw [LinearMap.comp_assoc]; rw [← Rep.ρ_mul]; rw [inv_mul_cancel]; rw [map_one]; rw [Module.End.one_eq_id]; rw [LinearMap.comp_id]
  · intro h
    rw [← LinearMap.comp_assoc]; rw [← h]; rw [LinearMap.comp_assoc]; rw [← Rep.ρ_mul]; rw [mul_inv_cancel]; rw [map_one]; rw [Module.End.one_eq_id]; rw [LinearMap.comp_id]

Depends on / 依赖: LinearMap, LinearMap.comp_assoc, LinearMap.comp_id, Module, Module.End.one_eq_id, comp_assoc, comp_id, inv_mul_cancel, map_one, mul_inv_cancel, nth_rw, one_eq_id
-/
theorem mem_invariants_iff_comm (f : X.V ->ₗ[k] Y.V) (g : G) :
    (linHom X.ρ Y.ρ) g f = f ↔ f.comp (X.ρ g) = (Y.ρ g).comp f := by
  dsimp
  constructor
  · intro h
    nth_rw 1 [← h]
    rw [LinearMap.comp_assoc]; rw [LinearMap.comp_assoc]; rw [← Rep.ρ_mul]; rw [inv_mul_cancel]; rw [map_one]; rw [Module.End.one_eq_id]; rw [LinearMap.comp_id]
  · intro h
    rw [← LinearMap.comp_assoc]; rw [← h]; rw [LinearMap.comp_assoc]; rw [← Rep.ρ_mul]; rw [mul_inv_cancel]; rw [map_one]; rw [Module.End.one_eq_id]; rw [LinearMap.comp_id]

variable (X Y) in
/-- The invariants of the representation `linHom X.ρ Y.ρ` correspond to the representation
homomorphisms from `X` to `Y`. -/
@[simps]
/--
Definition of `invariantsEquivRepHom` / `invariantsEquivRepHom` 的定义

English:
definition invariantsEquivRepHom
  signature: : (linHom X.ρ Y.ρ).invariants ≃ₗ[k] X ⟶ Y where
  body: Rep.ofHom ⟨f.val, fun g => (mem_invariants_iff_comm _ g).1 f.2 g⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
invFun f := ⟨f.hom, fun g => (mem_invariants_iff_comm _ g).2 f.hom.2 g⟩

中文:
定义 invariantsEquivRepHom
  签名: : (linHom X.ρ Y.ρ).invariants ≃ₗ[k] X ⟶ Y where
  定义体: Rep.ofHom ⟨f.val, fun g => (mem_invariants_iff_comm _ g).1 f.2 g⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
invFun f := ⟨f.hom, fun g => (mem_invariants_iff_comm _ g).2 f.hom.2 g⟩

Depends on / 依赖: Rep.ofHom, f.val, mem_invariants_iff_comm
-/
def invariantsEquivRepHom : (linHom X.ρ Y.ρ).invariants ≃ₗ[k] X ⟶ Y where
toFun f := Rep.ofHom ⟨f.val, fun g => (mem_invariants_iff_comm _ g).1 f.2 g⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
invFun f := ⟨f.hom, fun g => (mem_invariants_iff_comm _ g).2 f.hom.2 g⟩

end Rep

section FDRep

variable {k : Type u} [Field k] {G : Type v} [Group G]

/--
Definition of `invariantsEquivFDRepHom` / `invariantsEquivFDRepHom` 的定义

English:
definition invariantsEquivFDRepHom
  signature: (X Y : FDRep k G)
  body: by
  rw [← FDRep.forget₂_ρ]; rw [← FDRep.forget₂_ρ]
  -- Porting note: The original version used `linHom.invariantsEquivRepHom _ _ ≪≫ₗ`
  exact linHom.invariantsEquivRepHom
    ((forget₂ (FDRep k G) (Rep k G)).obj X) ((forget₂ (FDRep k G) (Rep k G)).obj Y) ≪≫ₗ
    FDRep.forget₂HomLinearEquiv X Y

中文:
定义 invariantsEquivFDRepHom
  签名: (X Y : FDRep k G)
  定义体: by
  rw [← FDRep.forget₂_ρ]; rw [← FDRep.forget₂_ρ]
  -- Porting note: The original version used `linHom.invariantsEquivRepHom _ _ ≪≫ₗ`
  exact linHom.invariantsEquivRepHom
    ((forget₂ (FDRep k G) (Rep k G)).obj X) ((forget₂ (FDRep k G) (Rep k G)).obj Y) ≪≫ₗ
    FDRep.forget₂HomLinearEquiv X Y

Depends on / 依赖: FDRep.forget
-/
def invariantsEquivFDRepHom (X Y : FDRep k G) : (linHom X.ρ Y.ρ).invariants ≃ₗ[k] X ⟶ Y := by
  rw [← FDRep.forget₂_ρ]; rw [← FDRep.forget₂_ρ]
  -- Porting note: The original version used `linHom.invariantsEquivRepHom _ _ ≪≫ₗ`
  exact linHom.invariantsEquivRepHom
    ((forget₂ (FDRep k G) (Rep k G)).obj X) ((forget₂ (FDRep k G) (Rep k G)).obj Y) ≪≫ₗ
    FDRep.forget₂HomLinearEquiv X Y

end FDRep

end linHom

end Representation

namespace Rep

open CategoryTheory

variable {k : Type u} {G : Type v} [CommRing k] [Group G] (A : Rep.{w} k G)
  (S : Subgroup G) [S.Normal]

/--
Definition of `toInvariants` / `toInvariants` 的定义

English:
abbreviation toInvariants
  signature: : Rep k G
  body: Rep.of A.ρ.toInvariants S

中文:
缩写 toInvariants
  签名: : Rep k G
  定义体: Rep.of A.ρ.toInvariants S

Depends on / 依赖: Rep.of, toInvariants
-/
abbrev toInvariants : Rep k G := Rep.of A.ρ.toInvariants S

/--
Definition of `quotientToInvariants` / `quotientToInvariants` 的定义

English:
abbreviation quotientToInvariants
  signature: : Rep k (G ⧸ S)
  body: Rep.of (A.ρ.quotientToInvariants S)

中文:
缩写 quotientToInvariants
  签名: : Rep k (G ⧸ S)
  定义体: Rep.of (A.ρ.quotientToInvariants S)

Depends on / 依赖: Rep.of, quotientToInvariants
-/
abbrev quotientToInvariants : Rep k (G ⧸ S) := Rep.of (A.ρ.quotientToInvariants S)

variable (k G)

/-- The functor sending a representation to its submodule of invariants. -/
@[implicit_reducible, simps! obj_carrier map_hom]
/--
Definition of `invariantsFunctor` / `invariantsFunctor` 的定义

English:
definition invariantsFunctor
  signature: : Rep.{w} k G ⥤ ModuleCat k where
  body: ModuleCat.of k A.ρ.invariants
map {A B} f := ModuleCat.ofHom (f.hom ∘ₗ A.ρ.invariants.subtype).codRestrict
    B.ρ.invariants fun ⟨c, hc⟩ g => by
      have := (hom_comm_apply f g c).symm
      simp_all [hc g]

中文:
定义 invariantsFunctor
  签名: : Rep.{w} k G ⥤ 模范畴 k where
  定义体: ModuleCat.of k A.ρ.invariants
map {A B} f := ModuleCat.ofHom (f.hom ∘ₗ A.ρ.invariants.subtype).codRestrict
    B.ρ.invariants fun ⟨c, hc⟩ g => by
      have := (hom_comm_apply f g c).symm
      simp_all [hc g]

Depends on / 依赖: ModuleCat, ModuleCat.of, invariants
-/
noncomputable def invariantsFunctor : Rep.{w} k G ⥤ ModuleCat k where
  obj A := ModuleCat.of k A.ρ.invariants
map {A B} f := ModuleCat.ofHom (f.hom ∘ₗ A.ρ.invariants.subtype).codRestrict
    B.ρ.invariants fun ⟨c, hc⟩ g => by
      have := (hom_comm_apply f g c).symm
      simp_all [hc g]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (invariantsFunctor k G).PreservesZeroMorphisms

中文:
实例 :
  签名: (invariantsFunctor k G).保持ZeroMorphisms
-/
instance : (invariantsFunctor k G).PreservesZeroMorphisms where
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (invariantsFunctor k G).Additive

中文:
实例 :
  签名: (invariantsFunctor k G).加性
-/
instance : (invariantsFunctor k G).Additive where
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (invariantsFunctor k G).Linear k

中文:
实例 :
  签名: (invariantsFunctor k G).线性 k
-/
instance : (invariantsFunctor k G).Linear k where

variable {G} in
/--
Definition of `quotientToInvariantsFunctor` / `quotientToInvariantsFunctor` 的定义

English:
definition quotientToInvariantsFunctor
  signature: (S : Subgroup G) [S.Normal]
  body: X.quotientToInvariants S
  map {X Y} f := Rep.ofHom ⟨((invariantsFunctor k S).map ((Rep.resFunctor S.subtype).map f)).hom,
    fun g => QuotientGroup.induction_on g fun g => by ext; simp [hom_comm_apply]⟩

中文:
定义 quotientToInvariantsFunctor
  签名: (S : 子群 G) [S.正规]
  定义体: X.quotientToInvariants S
  map {X Y} f := Rep.ofHom ⟨((invariantsFunctor k S).map ((Rep.resFunctor S.subtype).map f)).hom,
    fun g => QuotientGroup.induction_on g fun g => by ext; simp [hom_comm_apply]⟩

Depends on / 依赖: X.quotientToInvariants, quotientToInvariants
-/
noncomputable def quotientToInvariantsFunctor (S : Subgroup G) [S.Normal] :
    Rep.{w} k G ⥤ Rep k (G ⧸ S) where
  obj X := X.quotientToInvariants S
  map {X Y} f := Rep.ofHom ⟨((invariantsFunctor k S).map ((Rep.resFunctor S.subtype).map f)).hom,
    fun g => QuotientGroup.induction_on g fun g => by ext; simp [hom_comm_apply]⟩

set_option backward.isDefEq.respectTransparency false in
/-- The adjunction between the functor equipping a module with the trivial representation, and
the functor sending a representation to its submodule of invariants. -/
@[simps]
/--
Definition of `invariantsAdjunction` / `invariantsAdjunction` 的定义

English:
definition invariantsAdjunction
  signature: : trivialFunctor k G ⊣ invariantsFunctor k G where
  body: { app _ := ModuleCat.ofHom <| LinearMap.id.codRestrict _ <| by simp [trivialFunctor] }
  counit := { app X := Rep.ofHom ⟨Submodule.subtype _, fun g => by ext x; exact (x.2 g).symm⟩ }

@[simp]

中文:
定义 invariantsAdjunction
  签名: : trivialFunctor k G ⊣ invariantsFunctor k G where
  定义体: { app _ := ModuleCat.ofHom <| LinearMap.id.codRestrict _ <| by simp [trivialFunctor] }
  counit := { app X := Rep.ofHom ⟨Submodule.subtype _, fun g => by ext x; exact (x.2 g).symm⟩ }

@[simp]

Depends on / 依赖: LinearMap, LinearMap.id.codRestrict, ModuleCat, ModuleCat.ofHom, codRestrict, trivialFunctor
-/
noncomputable def invariantsAdjunction : trivialFunctor k G ⊣ invariantsFunctor k G where
  unit := { app _ := ModuleCat.ofHom <| LinearMap.id.codRestrict _ <| by simp [trivialFunctor] }
  counit := { app X := Rep.ofHom ⟨Submodule.subtype _, fun g => by ext x; exact (x.2 g).symm⟩ }

@[simp]
/--
lemma `invariantsAdjunction_homEquiv_apply_hom` / 引理 `invariantsAdjunction_homEquiv_apply_hom`

English:
lemma invariantsAdjunction_homEquiv_apply_hom
  proof: rfl

@[simp]

中文:
引理 invariantsAdjunction_homEquiv_apply_hom
  证明: rfl

@[simp]
-/
lemma invariantsAdjunction_homEquiv_apply_hom
    {X : ModuleCat k} {Y : Rep k G} (f : (trivialFunctor k G).obj X ⟶ Y) :
    ((invariantsAdjunction k G).homEquiv _ _ f).hom =
      f.hom.codRestrict _ (by intro _ _; exact (hom_comm_apply f _ _).symm) := rfl

@[simp]
/--
lemma `invariantsAdjunction_homEquiv_symm_apply_hom` / 引理 `invariantsAdjunction_homEquiv_symm_apply_hom`

English:
lemma invariantsAdjunction_homEquiv_symm_apply_hom
  proof: rfl

中文:
引理 invariantsAdjunction_homEquiv_symm_apply_hom
  证明: rfl
-/
lemma invariantsAdjunction_homEquiv_symm_apply_hom
    {X : ModuleCat k} {Y : Rep k G} (f : X ⟶ (invariantsFunctor k G).obj Y) :
    (((invariantsAdjunction k G).homEquiv _ _).symm f).hom.toLinearMap =
      Submodule.subtype _ ∘ₗ f.hom := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (invariantsFunctor k G).IsRightAdjoint
  body: (invariantsAdjunction k G).isRightAdjoint

中文:
实例 :
  签名: (invariantsFunctor k G).是右伴随
  定义体: (invariantsAdjunction k G).isRightAdjoint

Depends on / 依赖: invariantsAdjunction, isRightAdjoint
-/
noncomputable instance : (invariantsFunctor k G).IsRightAdjoint :=
  (invariantsAdjunction k G).isRightAdjoint

end Rep
