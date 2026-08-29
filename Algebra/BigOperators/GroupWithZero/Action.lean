/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Order.Group.Multiset
public import Mathlib.Data.Finset.Basic
public import Mathlib.Algebra.Group.Action.Basic
public import Mathlib.Algebra.Group.Units.Equiv

/-!
# Lemmas about group actions on big operators

This file contains results about two kinds of actions:

* sums over `DistribSMul`: `r • ∑ x ∈ s, f x = ∑ x ∈ s, r • f x`
* products over `MulDistribMulAction` (with primed name): `r • ∏ x ∈ s, f x = ∏ x ∈ s, r • f x`
* products over `SMulCommClass` (with unprimed name):
  `b ^ s.card • ∏ x ∈ s, f x = ∏ x ∈ s, b • f x`

Note that analogous lemmas for `Module`s like `Finset.sum_smul` appear in other files.
-/

public section


variable {M N γ : Type*}

section

variable [AddMonoid N] [DistribSMul M N]

/--
theorem `List.smul_sum` / 定理 `List.smul_sum`

English:
theorem List.smul_sum
  given: {r : M} {l : List N}
  statement: r • l.sum = (l.map (r • ·)).sum
  proof: map_list_sum (DistribSMul.toAddMonoidHom N r) l

中文:
定理 List.smul_sum
  条件: {r : M} {l : List N}
  结论: r • l.sum = (l.map (r • ·)).sum
  证明: map_list_sum (DistribSMul.toAddMonoidHom N r) l

Depends on / 依赖: DistribSMul, DistribSMul.toAddMonoidHom, map_list_sum, toAddMonoidHom
-/
theorem List.smul_sum {r : M} {l : List N} : r • l.sum = (l.map (r • ·)).sum :=
  map_list_sum (DistribSMul.toAddMonoidHom N r) l

end

section

variable [Monoid M] [Monoid N] [MulDistribMulAction M N]

/--
theorem `List.smul_prod'` / 定理 `List.smul_prod'`

English:
theorem List.smul_prod'
  given: {r : M} {l : List N}
  statement: r • l.prod = (l.map (r • ·)).prod
  proof: map_list_prod (MulDistribMulAction.toMonoidHom N r) l

中文:
定理 List.smul_prod'
  条件: {r : M} {l : List N}
  结论: r • l.prod = (l.map (r • ·)).prod
  证明: map_list_prod (MulDistribMulAction.toMonoidHom N r) l

Depends on / 依赖: MulDistribMulAction, MulDistribMulAction.toMonoidHom, map_list_prod, toMonoidHom
-/
theorem List.smul_prod' {r : M} {l : List N} : r • l.prod = (l.map (r • ·)).prod :=
  map_list_prod (MulDistribMulAction.toMonoidHom N r) l

end

section

variable [AddCommMonoid N] [DistribSMul M N] {r : M}

/--
theorem `Multiset.smul_sum` / 定理 `Multiset.smul_sum`

English:
theorem Multiset.smul_sum
  given: {s : Multiset N}
  statement: r • s.sum = (s.map (r • ·)).sum
  proof: (DistribSMul.toAddMonoidHom N r).map_multiset_sum s

中文:
定理 Multiset.smul_sum
  条件: {s : Multiset N}
  结论: r • s.sum = (s.map (r • ·)).sum
  证明: (DistribSMul.toAddMonoidHom N r).map_multiset_sum s

Depends on / 依赖: DistribSMul, DistribSMul.toAddMonoidHom, map_multiset_sum, toAddMonoidHom
-/
theorem Multiset.smul_sum {s : Multiset N} : r • s.sum = (s.map (r • ·)).sum :=
  (DistribSMul.toAddMonoidHom N r).map_multiset_sum s

/--
theorem `Finset.smul_sum` / 定理 `Finset.smul_sum`

English:
theorem Finset.smul_sum
  given: {f : γ -> N} {s : Finset γ}
  proof: map_sum (DistribSMul.toAddMonoidHom N r) f s

中文:
定理 Finset.smul_sum
  条件: {f : γ -> N} {s : Finset γ}
  证明: map_sum (DistribSMul.toAddMonoidHom N r) f s

Depends on / 依赖: DistribSMul, DistribSMul.toAddMonoidHom, map_sum, toAddMonoidHom
-/
theorem Finset.smul_sum {f : γ -> N} {s : Finset γ} :
    (r • ∑ x in s, f x) = ∑ x in s, r • f x :=
  map_sum (DistribSMul.toAddMonoidHom N r) f s

/--
theorem `smul_finsum_mem` / 定理 `smul_finsum_mem`

English:
theorem smul_finsum_mem
  given: {f : γ -> N} {s : Set γ} (hs : s.Finite)
  proof: (DistribSMul.toAddMonoidHom N r).map_finsum_mem f hs

中文:
定理 smul_finsum_mem
  条件: {f : γ -> N} {s : Set γ} (hs : s.Finite)
  证明: (DistribSMul.toAddMonoidHom N r).map_finsum_mem f hs

Depends on / 依赖: DistribSMul, DistribSMul.toAddMonoidHom, map_finsum_mem, toAddMonoidHom
-/
theorem smul_finsum_mem {f : γ -> N} {s : Set γ} (hs : s.Finite) :
    r • ∑ᶠ x in s, f x = ∑ᶠ x in s, r • f x :=
  (DistribSMul.toAddMonoidHom N r).map_finsum_mem f hs

end

section

variable [Monoid M] [CommMonoid N] [MulDistribMulAction M N]

/--
theorem `Multiset.smul_prod'` / 定理 `Multiset.smul_prod'`

English:
theorem Multiset.smul_prod'
  given: {r : M} {s : Multiset N}
  statement: r • s.prod = (s.map (r • ·)).prod
  proof: (MulDistribMulAction.toMonoidHom N r).map_multiset_prod s

中文:
定理 Multiset.smul_prod'
  条件: {r : M} {s : Multiset N}
  结论: r • s.prod = (s.map (r • ·)).prod
  证明: (MulDistribMulAction.toMonoidHom N r).map_multiset_prod s

Depends on / 依赖: MulDistribMulAction, MulDistribMulAction.toMonoidHom, map_multiset_prod, toMonoidHom
-/
theorem Multiset.smul_prod' {r : M} {s : Multiset N} : r • s.prod = (s.map (r • ·)).prod :=
  (MulDistribMulAction.toMonoidHom N r).map_multiset_prod s

/--
theorem `Finset.smul_prod'` / 定理 `Finset.smul_prod'`

English:
theorem Finset.smul_prod'
  given: {r : M} {f : γ -> N} {s : Finset γ}
  proof: map_prod (MulDistribMulAction.toMonoidHom N r) f s

中文:
定理 Finset.smul_prod'
  条件: {r : M} {f : γ -> N} {s : Finset γ}
  证明: map_prod (MulDistribMulAction.toMonoidHom N r) f s

Depends on / 依赖: MulDistribMulAction, MulDistribMulAction.toMonoidHom, map_prod, toMonoidHom
-/
theorem Finset.smul_prod' {r : M} {f : γ -> N} {s : Finset γ} :
    (r • ∏ x in s, f x) = ∏ x in s, r • f x :=
  map_prod (MulDistribMulAction.toMonoidHom N r) f s

/--
theorem `smul_finprod'` / 定理 `smul_finprod'`

English:
theorem smul_finprod'
  given: {ι : Sort*} [Finite ι] {f : ι -> N} (r : M)
  proof: by
  cases nonempty_fintype (PLift ι)
  simp only [finprod_eq_prod_plift_of_mulSupport_subset (s := Finset.univ) (by simp),
    Finset.smul_prod']

中文:
定理 smul_finprod'
  条件: {ι : Sort*} [Finite ι] {f : ι -> N} (r : M)
  证明: by
  cases nonempty_fintype (PLift ι)
  simp only [finprod_eq_prod_plift_of_mulSupport_subset (s := Finset.univ) (by simp),
    Finset.smul_prod']

Depends on / 依赖: Finset, Finset.smul_prod, Finset.univ, finprod_eq_prod_plift_of_mulSupport_subset, nonempty_fintype, smul_prod
-/
theorem smul_finprod' {ι : Sort*} [Finite ι] {f : ι -> N} (r : M) :
    r • ∏ᶠ x : ι, f x = ∏ᶠ x : ι, r • (f x) := by
  cases nonempty_fintype (PLift ι)
  simp only [finprod_eq_prod_plift_of_mulSupport_subset (s := Finset.univ) (by simp),
    Finset.smul_prod']

variable {G : Type*} [Group G] [MulDistribMulAction G N]

/--
theorem `Finset.smul_prod_perm` / 定理 `Finset.smul_prod_perm`

English:
theorem Finset.smul_prod_perm
  given: [Fintype G] (b : N) (g : G)
  proof: by
  simp only [smul_prod', smul_smul]
  exact Finset.prod_bijective (g * ·) (Group.mulLeft_bijective g) (by simp) (fun _ _ => rfl)

中文:
定理 Finset.smul_prod_perm
  条件: [Fintype G] (b : N) (g : G)
  证明: by
  simp only [smul_prod', smul_smul]
  exact Finset.prod_bijective (g * ·) (Group.mulLeft_bijective g) (by simp) (fun _ _ => rfl)

Depends on / 依赖: Finset, Finset.prod_bijective, Group.mulLeft_bijective, mulLeft_bijective, prod_bijective, smul_prod, smul_smul
-/
theorem Finset.smul_prod_perm [Fintype G] (b : N) (g : G) :
    (g • ∏ h : G, h • b) = ∏ h : G, h • b := by
  simp only [smul_prod', smul_smul]
  exact Finset.prod_bijective (g * ·) (Group.mulLeft_bijective g) (by simp) (fun _ _ => rfl)

/--
theorem `smul_finprod_perm` / 定理 `smul_finprod_perm`

English:
theorem smul_finprod_perm
  given: [Finite G] (b : N) (g : G)
  proof: by
  cases nonempty_fintype G
  simp only [finprod_eq_prod_of_fintype, Finset.smul_prod_perm]

中文:
定理 smul_finprod_perm
  条件: [Finite G] (b : N) (g : G)
  证明: by
  cases nonempty_fintype G
  simp only [finprod_eq_prod_of_fintype, Finset.smul_prod_perm]

Depends on / 依赖: Finset, Finset.smul_prod_perm, finprod_eq_prod_of_fintype, nonempty_fintype, smul_prod_perm
-/
theorem smul_finprod_perm [Finite G] (b : N) (g : G) :
    (g • ∏ᶠ h : G, h • b) = ∏ᶠ h : G, h • b := by
  cases nonempty_fintype G
  simp only [finprod_eq_prod_of_fintype, Finset.smul_prod_perm]

end

namespace List

@[to_additive]
/--
theorem `smul_prod` / 定理 `smul_prod`

English:
theorem smul_prod
  statement: [Monoid M] [MulOneClass N] [MulAction M N] [IsScalarTower M N N]
  proof: by
  induction l with
  | nil => simp
  | cons head tail ih => simp [← ih, smul_mul_smul_comm, pow_succ']

中文:
定理 smul_prod
  结论: [Monoid M] [MulOneClass N] [MulAction M N] [IsScalarTower M N N]
  证明: by
  induction l with
  | nil => simp
  | cons head tail ih => simp [← ih, smul_mul_smul_comm, pow_succ']

Depends on / 依赖: pow_succ, smul_mul_smul_comm
-/
theorem smul_prod [Monoid M] [MulOneClass N] [MulAction M N] [IsScalarTower M N N]
    [SMulCommClass M N N] (l : List N) (m : M) :
    m ^ l.length • l.prod = (l.map (m • ·)).prod := by
  induction l with
  | nil => simp
  | cons head tail ih => simp [← ih, smul_mul_smul_comm, pow_succ']

end List

namespace Multiset

@[to_additive]
/--
theorem `smul_prod` / 定理 `smul_prod`

English:
theorem smul_prod
  statement: [Monoid M] [CommMonoid N] [MulAction M N] [IsScalarTower M N N]
  proof: Quot.induction_on s by simp [List.smul_prod]

中文:
定理 smul_prod
  结论: [Monoid M] [CommMonoid N] [MulAction M N] [IsScalarTower M N N]
  证明: Quot.induction_on s by simp [List.smul_prod]

Depends on / 依赖: List.smul_prod, Quot.induction_on, induction_on, smul_prod
-/
theorem smul_prod [Monoid M] [CommMonoid N] [MulAction M N] [IsScalarTower M N N]
    [SMulCommClass M N N] (s : Multiset N) (b : M) :
    b ^ card s • s.prod = (s.map (b • ·)).prod :=
Quot.induction_on s by simp [List.smul_prod]

end Multiset

namespace Finset

variable {ι : Type*}

/--
theorem `smul_prod` / 定理 `smul_prod`

English:
theorem smul_prod
  proof: by
  have : Multiset.map (fun (x : ι) => b • f x) s.val =
      Multiset.map (fun x => b • x) (Multiset.map f s.val) := by
    simp only [Multiset.map_map, Function.comp_apply]
  simp_rw [prod_eq_multiset_prod, card_def, this, ← Multiset.smul_prod _ b, Multiset.card_map]

中文:
定理 smul_prod
  证明: by
  have : Multiset.map (fun (x : ι) => b • f x) s.val =
      Multiset.map (fun x => b • x) (Multiset.map f s.val) := by
    simp only [Multiset.map_map, Function.comp_apply]
  simp_rw [prod_eq_multiset_prod, card_def, this, ← Multiset.smul_prod _ b, Multiset.card_map]

Depends on / 依赖: Function, Function.comp_apply, Multiset, Multiset.card_map, Multiset.map, Multiset.map_map, Multiset.smul_prod, card_def, card_map, comp_apply, map_map, prod_eq_multiset_prod, s.val, simp_rw, smul_prod
-/
theorem smul_prod
    [CommMonoid N] [Monoid M] [MulAction M N] [IsScalarTower M N N] [SMulCommClass M N N]
    (s : Finset ι) (b : M) (f : ι -> N) :
    b ^ s.card • ∏ x in s, f x = ∏ x in s, b • f x := by
  have : Multiset.map (fun (x : ι) => b • f x) s.val =
      Multiset.map (fun x => b • x) (Multiset.map f s.val) := by
    simp only [Multiset.map_map, Function.comp_apply]
  simp_rw [prod_eq_multiset_prod, card_def, this, ← Multiset.smul_prod _ b, Multiset.card_map]

/--
theorem `prod_smul` / 定理 `prod_smul`

English:
theorem prod_smul
  proof: by
  induction s using Finset.cons_induction_on with
  | empty => simp
  | cons _ _ hj ih => rw [prod_cons, ih, smul_mul_smul_comm, ← prod_cons hj, ← prod_cons hj]

中文:
定理 prod_smul
  证明: by
  induction s using Finset.cons_induction_on with
  | empty => simp
  | cons _ _ hj ih => rw [prod_cons, ih, smul_mul_smul_comm, ← prod_cons hj, ← prod_cons hj]

Depends on / 依赖: Finset, Finset.cons_induction_on, cons_induction_on, prod_cons, smul_mul_smul_comm
-/
theorem prod_smul
    [CommMonoid N] [CommMonoid M] [MulAction M N] [IsScalarTower M N N] [SMulCommClass M N N]
    (s : Finset ι) (b : ι -> M) (f : ι -> N) :
    ∏ i in s, b i • f i = (∏ i in s, b i) • ∏ i in s, f i := by
  induction s using Finset.cons_induction_on with
  | empty => simp
  | cons _ _ hj ih => rw [prod_cons, ih, smul_mul_smul_comm, ← prod_cons hj, ← prod_cons hj]

end Finset
