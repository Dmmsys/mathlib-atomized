/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Geometry.Convex.Cone.Pointed

/-!
# The algebraic dual of a cone

Given a bilinear pairing `p` between two `R`-modules `M` and `N` and a set `s` in `M`, we define
`PointedCone.dual p s` to be the pointed cone in `N` consisting of all points `y` such that
`0 ≤ p x y` for all `x ∈ s`.

When the pairing is perfect, this gives us the algebraic dual of a cone. This is developed here.
When the pairing is continuous and perfect (as a continuous pairing), this gives us the topological
dual instead. See `Mathlib/Analysis/Convex/Cone/Dual.lean` for that case.

## Implementation notes

We do not provide a `ConvexCone`-valued version of `PointedCone.dual` since the dual cone of any set
always contains `0`, i.e. is a pointed cone.
Furthermore, the strict version `{y | ∀ x ∈ s, 0 < p x y}` is a candidate to the name
`ConvexCone.dual`.

-/

@[expose] public section

assert_not_exists TopologicalSpace Real Cardinal

open Function LinearMap Pointwise Set

namespace PointedCone

section CommSemiring

variable {R : Type*} [CommSemiring R] [PartialOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommMonoid M] [Module R M]
variable {N : Type*} [AddCommMonoid N] [Module R N]
variable {p : M ->ₗ[R] N ->ₗ[R] R} {s t : Set M} {y : N}

local notation3 "R>=0" => {c : R // 0 <= c}

variable (p) in
/--
Definition of `dual` / `dual` 的定义

English:
definition dual
  signature: (s : Set M)
  body: {y | forall ⦃x⦄, x in s -> 0 <= p x y}
  zero_mem' := by simp
  add_mem' {u v} hu hv x hx := by rw [map_add]; exact add_nonneg (hu hx) (hv hx)
  smul_mem' c y hy x hx := by rw [← Nonneg.coe_smul, map_smul]; exact mul_nonneg c.2 (hy hx)

中文:
定义 dual
  签名: (s : 集合 M)
  定义体: {y | forall ⦃x⦄, x in s -> 0 <= p x y}
  zero_mem' := by simp
  add_mem' {u v} hu hv x hx := by rw [map_add]; exact add_nonneg (hu hx) (hv hx)
  smul_mem' c y hy x hx := by rw [← Nonneg.coe_smul, map_smul]; exact mul_nonneg c.2 (hy hx)
-/
def dual (s : Set M) : PointedCone R N where
  carrier := {y | forall ⦃x⦄, x in s -> 0 <= p x y}
  zero_mem' := by simp
  add_mem' {u v} hu hv x hx := by rw [map_add]; exact add_nonneg (hu hx) (hv hx)
  smul_mem' c y hy x hx := by rw [← Nonneg.coe_smul, map_smul]; exact mul_nonneg c.2 (hy hx)

/--
lemma `mem_dual` / 引理 `mem_dual`

English:
lemma mem_dual
  statement: y in dual p s ↔ forall ⦃x⦄, x in s -> 0 <= p x y
  proof: .rfl

中文:
引理 mem_dual
  结论: y in dual p s ↔ 对任意 ⦃x⦄, x in s -> 0 <= p x y
  证明: .rfl
-/
@[simp] lemma mem_dual : y in dual p s ↔ forall ⦃x⦄, x in s -> 0 <= p x y := .rfl

/--
lemma `dual_empty` / 引理 `dual_empty`

English:
lemma dual_empty
  statement: dual p ∅ = ⊤
  proof: by ext; simp

中文:
引理 dual_empty
  结论: dual p ∅ = ⊤
  证明: by ext; simp
-/
@[simp] lemma dual_empty : dual p ∅ = ⊤ := by ext; simp
/--
lemma `dual_zero` / 引理 `dual_zero`

English:
lemma dual_zero
  statement: dual p 0 = ⊤
  proof: by ext; simp

中文:
引理 dual_zero
  结论: dual p 0 = ⊤
  证明: by ext; simp
-/
@[simp] lemma dual_zero : dual p 0 = ⊤ := by ext; simp
/--
lemma `dual_singleton_zero` / 引理 `dual_singleton_zero`

English:
lemma dual_singleton_zero
  statement: dual p {0} = ⊤
  proof: dual_zero

中文:
引理 dual_singleton_zero
  结论: dual p {0} = ⊤
  证明: dual_zero
-/
@[simp] lemma dual_singleton_zero : dual p {0} = ⊤ := dual_zero
/--
lemma `dual_ker` / 引理 `dual_ker`

English:
lemma dual_ker
  statement: dual p (ker p) = ⊤
  proof: by ext; simp +contextual

中文:
引理 dual_ker
  结论: dual p (ker p) = ⊤
  证明: by ext; simp +contextual
-/
@[simp] lemma dual_ker : dual p (ker p) = ⊤ := by ext; simp +contextual

/--
lemma `dual_anti` / 引理 `dual_anti`

English:
lemma dual_anti
  given: (h : t subseteq s)
  statement: dual p s <= dual p t
  proof: fun _y hy _x hx => hy (h hx)

alias dual_le_dual := dual_anti

中文:
引理 dual_anti
  条件: (h : t subseteq s)
  结论: dual p s <= dual p t
  证明: fun _y hy _x hx => hy (h hx)

alias dual_le_dual := dual_anti
-/
@[gcongr] lemma dual_anti (h : t subseteq s) : dual p s <= dual p t := fun _y hy _x hx => hy (h hx)

alias dual_le_dual := dual_anti

/--
lemma `dual_antitone` / 引理 `dual_antitone`

English:
lemma dual_antitone
  statement: Antitone (dual p)
  proof: fun _ _ h => dual_anti h

中文:
引理 dual_antitone
  结论: 递减 (dual p)
  证明: fun _ _ h => dual_anti h

Depends on / 依赖: dual_anti
-/
lemma dual_antitone : Antitone (dual p) := fun _ _ h => dual_anti h

/--
lemma `dual_singleton` / 引理 `dual_singleton`

English:
lemma dual_singleton
  given: (x : M)
  statement: dual p {x} = (positive R R).comap (p x)
  proof: by ext; simp

中文:
引理 dual_singleton
  条件: (x : M)
  结论: dual p {x} = (positive R R).comap (p x)
  证明: by ext; simp
-/
lemma dual_singleton (x : M) : dual p {x} = (positive R R).comap (p x) := by ext; simp

/--
lemma `dual_union` / 引理 `dual_union`

English:
lemma dual_union
  given: (s t : Set M)
  statement: dual p (s union t) = dual p s ⊓ dual p t
  proof: by aesop

中文:
引理 dual_union
  条件: (s t : 集合 M)
  结论: dual p (s union t) = dual p s ⊓ dual p t
  证明: by aesop
-/
lemma dual_union (s t : Set M) : dual p (s union t) = dual p s ⊓ dual p t := by aesop

/--
lemma `dual_insert` / 引理 `dual_insert`

English:
lemma dual_insert
  given: (x : M) (s : Set M)
  statement: dual p (insert x s) = dual p {x} ⊓ dual p s
  proof: by
  rw [insert_eq]; rw [dual_union]

中文:
引理 dual_insert
  条件: (x : M) (s : 集合 M)
  结论: dual p (insert x s) = dual p {x} ⊓ dual p s
  证明: by
  rw [insert_eq]; rw [dual_union]

Depends on / 依赖: dual_union, insert_eq
-/
lemma dual_insert (x : M) (s : Set M) : dual p (insert x s) = dual p {x} ⊓ dual p s := by
  rw [insert_eq]; rw [dual_union]

/--
lemma `dual_iUnion` / 引理 `dual_iUnion`

English:
lemma dual_iUnion
  given: {ι : Sort*} (f : ι -> Set M)
  statement: dual p (⋃ i, f i) = ⨅ i, dual p (f i)
  proof: by
  ext; simp [forall_comm (α := M)]

中文:
引理 dual_iUnion
  条件: {ι : 类型层*} (f : ι -> 集合 M)
  结论: dual p (⋃ i, f i) = ⨅ i, dual p (f i)
  证明: by
  ext; simp [forall_comm (α := M)]

Depends on / 依赖: forall_comm
-/
lemma dual_iUnion {ι : Sort*} (f : ι -> Set M) : dual p (⋃ i, f i) = ⨅ i, dual p (f i) := by
  ext; simp [forall_comm (α := M)]

/--
lemma `dual_sUnion` / 引理 `dual_sUnion`

English:
lemma dual_sUnion
  given: (S : Set (Set M))
  statement: dual p (⋃₀ S) = sInf (dual p '' S)
  proof: by
  ext; simp [forall_comm (α := M)]

中文:
引理 dual_sUnion
  条件: (S : 集合 (集合 M))
  结论: dual p (⋃₀ S) = sInf (dual p '' S)
  证明: by
  ext; simp [forall_comm (α := M)]

Depends on / 依赖: forall_comm
-/
lemma dual_sUnion (S : Set (Set M)) : dual p (⋃₀ S) = sInf (dual p '' S) := by
  ext; simp [forall_comm (α := M)]

/--
lemma `dual_eq_iInter_dual_singleton` / 引理 `dual_eq_iInter_dual_singleton`

English:
lemma dual_eq_iInter_dual_singleton
  given: (s : Set M)
  proof: by ext; simp

中文:
引理 dual_eq_i整数er_dual_singleton
  条件: (s : 集合 M)
  证明: by ext; simp
-/
lemma dual_eq_iInter_dual_singleton (s : Set M) :
    dual p s = ⋂ i : s, (dual p {i.val} : Set N) := by ext; simp

/--
lemma `subset_dual_dual` / 引理 `subset_dual_dual`

English:
lemma subset_dual_dual
  statement: s subseteq dual p.flip (dual p s)
  proof: fun _x hx _y hy => hy hx

中文:
引理 subset_dual_dual
  结论: s subseteq dual p.flip (dual p s)
  证明: fun _x hx _y hy => hy hx
-/
lemma subset_dual_dual : s subseteq dual p.flip (dual p s) := fun _x hx _y hy => hy hx

/--
lemma `subset_dual_flip_iff_subset_dual` / 引理 `subset_dual_flip_iff_subset_dual`

English:
lemma subset_dual_flip_iff_subset_dual
  given: {s : Set M} {t : Set N}
  proof: by
  constructor <;> exact (le_trans subset_dual_dual <| dual_antitone ·)

中文:
引理 subset_dual_flip_iff_subset_dual
  条件: {s : 集合 M} {t : 集合 N}
  证明: by
  constructor <;> exact (le_trans subset_dual_dual <| dual_antitone ·)
-/
@[simp] lemma subset_dual_flip_iff_subset_dual {s : Set M} {t : Set N} :
    s subseteq dual p.flip t ↔ t subseteq dual p s := by
  constructor <;> exact (le_trans subset_dual_dual <| dual_antitone ·)

variable (s) in
/--
lemma `dual_dual_flip_dual` / 引理 `dual_dual_flip_dual`

English:
lemma dual_dual_flip_dual
  statement: dual p (dual p.flip (dual p s)) = dual p s
  proof: le_antisymm (dual_anti subset_dual_dual) subset_dual_dual

中文:
引理 dual_dual_flip_dual
  结论: dual p (dual p.flip (dual p s)) = dual p s
  证明: le_antisymm (dual_anti subset_dual_dual) subset_dual_dual
-/
@[simp] lemma dual_dual_flip_dual : dual p (dual p.flip (dual p s)) = dual p s :=
  le_antisymm (dual_anti subset_dual_dual) subset_dual_dual

/--
lemma `dual_flip_dual_dual_flip` / 引理 `dual_flip_dual_dual_flip`

English:
lemma dual_flip_dual_dual_flip
  given: (s : Set N)
  proof: dual_dual_flip_dual _

@[simp]

中文:
引理 dual_flip_dual_dual_flip
  条件: (s : 集合 N)
  证明: dual_dual_flip_dual _

@[simp]
-/
@[simp] lemma dual_flip_dual_dual_flip (s : Set N) :
    dual p.flip (dual p (dual p.flip s)) = dual p.flip s := dual_dual_flip_dual _

@[simp]
/--
lemma `dual_hull` / 引理 `dual_hull`

English:
lemma dual_hull
  given: (s : Set M)
  statement: dual p (hull R s) = dual p s
  proof: by
  refine le_antisymm (dual_anti Submodule.subset_span) (fun x hx y hy => ?_)
  induction hy using Submodule.span_induction with
  | mem _y h => exact hx h
  | zero => simp
  | add y z _hy _hz hy hz => rw [map_add, add_apply]; exact add_nonneg hy hz
  | smul t y _hy hy => rw [map_smul_of_tower, Nonneg.mk_smul, smul_apply]; exact mul_nonneg t.2 hy

@[deprecated "`PointedCone.span` was renamed to `PointedCone.hull`" (since := "2026-03-22")]
alias dual_span := dual_hull

中文:
引理 dual_hull
  条件: (s : 集合 M)
  结论: dual p (hull R s) = dual p s
  证明: by
  refine le_antisymm (dual_anti Submodule.subset_span) (fun x hx y hy => ?_)
  induction hy using Submodule.span_induction with
  | mem _y h => exact hx h
  | zero => simp
  | add y z _hy _hz hy hz => rw [map_add, add_apply]; exact add_nonneg hy hz
  | smul t y _hy hy => rw [map_smul_of_tower, Nonneg.mk_smul, smul_apply]; exact mul_nonneg t.2 hy

@[deprecated "`PointedCone.span` was renamed to `PointedCone.hull`" (since := "2026-03-22")]
alias dual_span := dual_hull

Depends on / 依赖: Nonneg, Nonneg.mk_smul, Submodule, Submodule.span_induction, Submodule.subset_span, add_apply, add_nonneg, dual_anti, le_antisymm, map_add, map_smul_of_tower, mk_smul, mul_nonneg, smul_apply, span_induction, subset_span
-/
lemma dual_hull (s : Set M) : dual p (hull R s) = dual p s := by
  refine le_antisymm (dual_anti Submodule.subset_span) (fun x hx y hy => ?_)
  induction hy using Submodule.span_induction with
  | mem _y h => exact hx h
  | zero => simp
  | add y z _hy _hz hy hz => rw [map_add, add_apply]; exact add_nonneg hy hz
  | smul t y _hy hy => rw [map_smul_of_tower, Nonneg.mk_smul, smul_apply]; exact mul_nonneg t.2 hy

@[deprecated "`PointedCone.span` was renamed to `PointedCone.hull`" (since := "2026-03-22")]
alias dual_span := dual_hull

/--
lemma `dual_sup` / 引理 `dual_sup`

English:
lemma dual_sup
  given: (C D : PointedCone R M)
  statement: dual p (C ⊔ D : PointedCone R M) = dual p (C union D)
  proof: by simp [← dual_hull]

中文:
引理 dual_sup
  条件: (C D : PointedCone R M)
  结论: dual p (C ⊔ D : PointedCone R M) = dual p (C union D)
  证明: by simp [← dual_hull]
-/
@[simp] lemma dual_sup (C D : PointedCone R M) : dual p (C ⊔ D : PointedCone R M) = dual p (C union D)
  := by simp [← dual_hull]

variable {M' : Type*} [AddCommMonoid M'] [Module R M']

/--
lemma `dual_image` / 引理 `dual_image`

English:
lemma dual_image
  given: (s : Set M') (q : M' ->ₗ[R] M)
  statement: dual p (q '' s) = dual (p.comp q) s
  proof: by
  ext; simp

中文:
引理 dual_image
  条件: (s : 集合 M') (q : M' ->ₗ[R] M)
  结论: dual p (q '' s) = dual (p.comp q) s
  证明: by
  ext; simp
-/
@[simp] lemma dual_image (s : Set M') (q : M' ->ₗ[R] M) : dual p (q '' s) = dual (p.comp q) s := by
  ext; simp

/--
lemma `dual_eq_dual_id_image` / 引理 `dual_eq_dual_id_image`

English:
lemma dual_eq_dual_id_image
  given: (s : Set M)
  statement: dual p s = dual .id (p '' s)
  proof: by simp

中文:
引理 dual_eq_dual_id_image
  条件: (s : 集合 M)
  结论: dual p s = dual .id (p '' s)
  证明: by simp
-/
lemma dual_eq_dual_id_image (s : Set M) : dual p s = dual .id (p '' s) := by simp

/--
lemma `dual_eq_dual_id_map` / 引理 `dual_eq_dual_id_map`

English:
lemma dual_eq_dual_id_map
  given: (C : PointedCone R M)
  statement: dual p C = dual .id (map p C)
  proof: by simp

中文:
引理 dual_eq_dual_id_map
  条件: (C : PointedCone R M)
  结论: dual p C = dual .id (map p C)
  证明: by simp
-/
lemma dual_eq_dual_id_map (C : PointedCone R M) : dual p C = dual .id (map p C) := by simp

/--
lemma `dual_eq_comap_dual_eval` / 引理 `dual_eq_comap_dual_eval`

English:
lemma dual_eq_comap_dual_eval
  given: (s : Set M)
  proof: by
  ext; simp

中文:
引理 dual_eq_comap_dual_eval
  条件: (s : 集合 M)
  证明: by
  ext; simp
-/
lemma dual_eq_comap_dual_eval (s : Set M) :
    dual p s = comap p.flip (dual (Module.Dual.eval R M) s) := by
  ext; simp

end CommSemiring

section CommRing

variable {R : Type*} [CommRing R] [PartialOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommMonoid N] [Module R N]
variable {p : M ->ₗ[R] N ->ₗ[R] R}

/--
lemma `dual_univ` / 引理 `dual_univ`

English:
lemma dual_univ
  given: (hp : Injective p.flip)
  statement: dual p univ = 0
  proof: by
  refine le_antisymm (fun y hy => (map_eq_zero_iff p.flip hp).1 ?_) (by simp)
  ext x
exact (hy <| mem_univ x).antisymm' by simpa using hy mem_univ (-x)

中文:
引理 dual_univ
  条件: (hp : 单射 p.flip)
  结论: dual p univ = 0
  证明: by
  refine le_antisymm (fun y hy => (map_eq_zero_iff p.flip hp).1 ?_) (by simp)
  ext x
exact (hy <| mem_univ x).antisymm' by simpa using hy mem_univ (-x)

Depends on / 依赖: antisymm, le_antisymm, map_eq_zero_iff, mem_univ, p.flip
-/
lemma dual_univ (hp : Injective p.flip) : dual p univ = 0 := by
  refine le_antisymm (fun y hy => (map_eq_zero_iff p.flip hp).1 ?_) (by simp)
  ext x
exact (hy <| mem_univ x).antisymm' by simpa using hy mem_univ (-x)

variable {N : Type*} [AddCommGroup N] [Module R N]
variable {p : M ->ₗ[R] N ->ₗ[R] R}

/--
lemma `dual_neg` / 引理 `dual_neg`

English:
lemma dual_neg
  given: {s : Set M}
  statement: dual p (-s) = -dual p s
  proof: by ext; simp

中文:
引理 dual_neg
  条件: {s : 集合 M}
  结论: dual p (-s) = -dual p s
  证明: by ext; simp
-/
@[simp] lemma dual_neg {s : Set M} : dual p (-s) = -dual p s := by ext; simp

end CommRing

end PointedCone
